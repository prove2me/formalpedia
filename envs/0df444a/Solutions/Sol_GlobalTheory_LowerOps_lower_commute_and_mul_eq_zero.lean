-- Prove2me | solution 1 for GlobalTheory.LowerOps.lower_commute_and_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:30:20.740399+00:00
-- url     : https://prove2.me/submissions/5a422f0a-12eb-468f-8c61-62a75dca3250

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodConjugateIntegral
import Theorems.Thm_GlobalTheory_LowerOps_act_of_mem_eigK
import Theorems.Thm_GlobalTheory_LowerOps_conj_ofF
import Theorems.Thm_GlobalTheory_LowerOps_bar_ne_self
import Theorems.Thm_GlobalTheory_LowerOps_inK_mem_eigK
import Theorems.Thm_GlobalTheory_LowerOps_ext_of_eigLat
import Theorems.Thm_GlobalTheory_LowerOps_lower_mem_eigK_bar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.LowerOps
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}
namespace GlobalTheory.LowerOps
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ N : I → Module.End K (K ⊗[O] H), (∀ i, IsLower ρ (φ i) (e i) (f i) (N i)) → (∀ i (a : OF E), Commute (N i) ((ρ (ofF c a)).baseChange K)) ∧ ∀ i j, N i * N j = 0 := by
  intro E _ _ _ c _ l _ O _ _ _ _ K _ _ _ _ _ D hD _ I _ φ hφ H _ _ ρ Fil B _ hEig e f hG N hN
  have hsum := hEig.2.2.1.2
  refine ⟨fun i a => ?_, fun i j => ?_⟩
  · show N i * (ρ (ofF c a)).baseChange K = (ρ (ofF c a)).baseChange K * N i
    apply ext_of_eigLat ρ D hD hsum
    intro σ y hy
    have hx := inK_mem_eigK (K := K) hy
    rw [Module.End.mul_apply, Module.End.mul_apply, act_of_mem_eigK hx, map_smul]
    by_cases hσ : σ = φ i
    · subst hσ
      have hm := lower_mem_eigK_bar hG (hN i) hy
      rw [act_of_mem_eigK hm]
      congr 1
      show _ = φ i (IsCMField.complexConj E ((ofF c a : orderC c) : E))
      rw [conj_ofF]
    · rw [(hN i).2 σ hσ _ hx, smul_zero, map_zero]
  · apply ext_of_eigLat ρ D hD hsum
    intro σ y hy
    have hx := inK_mem_eigK (K := K) hy
    rw [Module.End.mul_apply, LinearMap.zero_apply]
    by_cases hσ : σ = φ j
    · subst hσ
      have hm := lower_mem_eigK_bar hG (hN j) hy
      have hne : bar (φ j) ≠ φ i := by
        intro h
        obtain ⟨k, _, hk⟩ := hφ (bar (φ j))
        have hi := hk i (Or.inl h)
        have hj := hk j (Or.inr rfl)
        subst hi; subst hj
        exact bar_ne_self _ h
      exact (hN i).2 _ hne _ hm
    · rw [(hN j).2 σ hσ _ hx, map_zero]
end GlobalTheory.LowerOps
