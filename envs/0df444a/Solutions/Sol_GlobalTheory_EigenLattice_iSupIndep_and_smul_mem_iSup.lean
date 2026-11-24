-- Prove2me | solution 1 for GlobalTheory.EigenLattice.iSupIndep_and_smul_mem_iSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:06:18.014808+00:00
-- url     : https://prove2.me/submissions/25be94c5-578e-4d7e-b9f4-5b92511f635c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralThird
import Theorems.Thm_GlobalTheory_EigenLattice_tensAct_eig
import Theorems.Thm_GlobalTheory_EigenLattice_inK_apply_map
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.EigenLattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)}
variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
variable {H : Type} [AddCommGroup H] [Module O H]
namespace GlobalTheory.EigenLattice
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → DirectSum.IsInternal (fun σ : E →+* K => eigK ρ σ) → iSupIndep (fun σ : E →+* K => eigLat ρ σ) ∧ ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat ρ σ := by
  intro E _ _ _ c _ l _ O _ _ _ _ K _ _ _ _ hcard D _ hclr I _ φ _ H _ _ ρ Fil B hlat hint
  have hfree : Module.Free O H := hlat.1
  have hinj : Function.Injective (inK (O := O) K H) := by
    have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := H) (Algebra.linearMap O K)
      (IsFractionRing.injective O K)
    have : inK (O := O) K H = (LinearMap.rTensor H (Algebra.linearMap O K)) ∘ₗ
        (TensorProduct.lid O H).symm.toLinearMap := by
      ext h; simp [inK]
    rw [this]; exact h1.comp (TensorProduct.lid O H).symm.injective
  have hindK := hint.submodule_iSupIndep
  have htop : ∀ v : K ⊗[O] H, v ∈ ⨆ σ, eigK ρ σ := fun v => by
    rw [hint.submodule_iSup_eq_top]; trivial
  constructor
  · intro σ
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    have hle : (⨆ j, ⨆ (_ : j ≠ σ), eigLat ρ j) ≤
        ((⨆ j, ⨆ (_ : j ≠ σ), eigK ρ j).restrictScalars O).comap (inK K H) := by
      refine iSup₂_le fun j hj y hy => ?_
      exact (le_iSup₂ (f := fun j (_ : j ≠ σ) => eigK ρ j) j hj) hy
    have h0 := (Submodule.disjoint_def.1 (hindK σ)) _ hx1 (hle hx2)
    exact hinj (by rw [h0, map_zero])
  · have hfin : Finite (E →+* K) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact Module.finrank_pos.ne')
    letI := Fintype.ofFinite (E →+* K)
    choose t ht using hclr
    have hA : ∀ (σ σ' : E →+* K) v, v ∈ eigK ρ σ' →
        ((tensAct ρ (t σ)).baseChange K) v = if σ' = σ then algebraMap O K D • v else 0 := by
      intro σ σ' v hv
      rw [tensAct_eig ρ σ' v hv, ht σ σ']
      split_ifs <;> simp
    have hsum : ∀ v : K ⊗[O] H, ∑ σ, ((tensAct ρ (t σ)).baseChange K) v = algebraMap O K D • v := by
      intro v
      refine Submodule.iSup_induction (fun σ => eigK ρ σ)
        (motive := fun v => ∑ σ, ((tensAct ρ (t σ)).baseChange K) v = algebraMap O K D • v) (htop v) ?_ ?_ ?_
      · intro σ' w hw
        rw [Finset.sum_congr rfl (fun σ _ => hA σ σ' w hw)]
        simp
      · simp
      · intro x y hx hy
        simp only [map_add, Finset.sum_add_distrib, smul_add] at hx hy ⊢
        rw [hx, hy]
    have hmem : ∀ σ v, ((tensAct ρ (t σ)).baseChange K) v ∈ eigK ρ σ := by
      intro σ v
      refine Submodule.iSup_induction (fun σ => eigK ρ σ)
        (motive := fun v => ((tensAct ρ (t σ)).baseChange K) v ∈ eigK ρ σ) (htop v) ?_ ?_ ?_
      · intro σ' w hw
        rw [hA σ σ' w hw]
        split_ifs with h
        · subst h; exact Submodule.smul_mem _ _ hw
        · exact zero_mem _
      · simp
      · intro x y hx hy
        simp only [map_add] at hx hy ⊢
        exact add_mem hx hy
    intro h
    have key : ∑ σ, tensAct ρ (t σ) h = D • h := by
      apply hinj
      rw [map_sum, map_smul]
      simp_rw [inK_apply_map, hsum, algebraMap_smul]
    rw [← key]
    refine Submodule.sum_mem _ fun σ _ => (le_iSup (fun σ => eigLat ρ σ) σ) ?_
    show inK K H _ ∈ eigK ρ σ
    rw [inK_apply_map]
    exact hmem σ _
end GlobalTheory.EigenLattice
