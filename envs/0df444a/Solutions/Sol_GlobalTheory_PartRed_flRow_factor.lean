-- Prove2me | solution 1 for GlobalTheory.PartRed.flRow_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:53:05.34471+00:00
-- url     : https://prove2.me/submissions/133ba5fa-6197-455e-b538-77ed31ba58b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMulAddCharLinearFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatCompAffineMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEvaluateEntryOfMulLawStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionIntegrateEntryOfTranslationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionLowerEntryMultiplicationLawStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionUpperFreeEntryTranslationLawStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEqFlatMapFourierJacobiRowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapFourierJacobiRowAddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapLawsFactorFourierJacobiSource
import Theorems.Thm_GlobalTheory_PartRed_evalLaw_direct
import Theorems.Thm_GlobalTheory_PartRed_intLaw_direct
import Theorems.Thm_GlobalTheory_PartRed_kills_empty
import Theorems.Thm_GlobalTheory_PartRed_kills_evals
import Theorems.Thm_GlobalTheory_PartRed_kills_ints
import Theorems.Thm_GlobalTheory_PartRed_mem_fixSet
import Theorems.Thm_GlobalTheory_PartRed_mem_transSet
import Theorems.Thm_GlobalTheory_PartRed_mem_lowSet
import Theorems.Thm_GlobalTheory_PartRed_disj_trans_fix
import Theorems.Thm_GlobalTheory_PartRed_kills_low
import Theorems.Thm_GlobalTheory_PartRed_kills_up
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_PartRed_chL_apply
import Theorems.Thm_GlobalTheory_T_flatMapFourierJacobiRow_add
import Theorems.Thm_GlobalTheory_T_partialReduction_eq_flatMapFourierJacobiRow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open GlobalTheory GlobalTheory.PartRed
open GlobalTheory.LocFlat
namespace GlobalTheory.PartRed
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ + 1 → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val ≤ ρ ∧ ¬ Free (ρ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ l s, r = Sum.inr l ∧ ρ < l.val ∧ q = Sum.inl s) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), Free (ρ + 1) (r, q) → (∀ i, q = Sum.inr i → ρ < i.val) → ∀ (a : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (t + Matrix.single r q a)) → L Φ' = (ψ (ch (Matrix.single r q a)) : ℂ) • L Φ) → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∃ L₀ : SB (Matrix (n ⊕ Unit) n' k) →ₗ[ℂ] M, ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flRow ψ ν (ρ + 1) Φ.1 → L Φ = L₀ Ψ := by
  intro k _ _ _ _ _ _ ψ ν hψ hψ1 hν n n' _ _ _ _ c ρ M _ _ L hc H1 H2 H3 H4
  have K0 := kills_empty ψ ν L chL (basePt c (0 : Matrix n n' k))
  have K1 := kills_evals ψ ν hψ hψ1 hν L chL (basePt c (0 : Matrix n n' k)) ∅ (fixSet ρ) ∅
    (Finset.disjoint_empty_right _) K0 (by
      intro e he E' _ _ heE'
      refine evalLaw_direct ψ ν hψ L chL _ E' ∅ e (Finset.notMem_empty _) heE' ?_
      obtain ⟨r, q⟩ := e
      rcases mem_fixSet.mp he with h | h
      · exact H1 r q h
      · exact H2 r q h)
  rw [Finset.empty_union] at K1
  have K2 := kills_ints ψ ν hψ hν L chL (basePt c (0 : Matrix n n' k)) (fixSet ρ) (transSet ρ) ∅
    (disj_trans_fix ρ) K1 (by
      intro e he I' _ _ heI'
      refine intLaw_direct ψ ν L chL _ (fixSet ρ) I' e heI'
        (Finset.disjoint_left.mp (disj_trans_fix ρ) he) ?_
      obtain ⟨r, q⟩ := e
      have h := mem_transSet.mp he
      intro a Φ Φ' hΦ'
      rw [chL_apply]
      exact H3 r q h.1 h.2 a Φ Φ' hΦ')
  rw [Finset.empty_union] at K2
  have K3 := kills_low ψ ν hψ hψ1 hν ρ L hc H4 K2 (c + 1)
  have hlow : (lowSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))).filter (fun e => colIx e < c + 1) = lowSet ρ := by
    apply Finset.filter_true_of_mem
    intro e he
    obtain ⟨l, i, rfl, -, -⟩ := mem_lowSet.mp he
    simp only [colIx, Sum.elim_inr]
    exact i.isLt
  rw [hlow] at K3
  have K4 := kills_up ψ ν hψ hν ρ L hc H4 K3 (c + 1) 0 (by omega)
  have hup : (upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))).filter (fun e => 0 ≤ colIx e) = upSet ρ := by
    apply Finset.filter_true_of_mem
    intro e _
    exact Nat.zero_le _
  rw [hup] at K4
  have hρc : ρ < c := by omega
  let lρ : Fin c := ⟨ρ, hρc⟩
  let F : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (Matrix (n ⊕ Unit) n' k → ℂ) :=
    { toFun := fun Φ => flRow ψ ν (ρ + 1) Φ.1
      map_add' := fun Φ₁ Φ₂ => GlobalTheory.T.flatMapFourierJacobiRow_add k ψ ν hψ hν n n' c (ρ + 1) Φ₁.1 Φ₂.1 Φ₁.2 Φ₂.2
      map_smul' := fun a Φ => by
        funext x
        simp only [flRow, opE, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul _ _ }
  have hker : LinearMap.ker F ≤ LinearMap.ker L := by
    intro Φ hΦ
    rw [LinearMap.mem_ker] at hΦ ⊢
    apply K4
    funext x
    rw [GlobalTheory.T.partialReduction_eq_flatMapFourierJacobiRow k ψ ν hν n n' c ρ hc lρ rfl Φ.1 x]
    exact congrFun hΦ _
  let f₀ : LinearMap.range F →ₗ[ℂ] M := (LinearMap.ker F).liftQ L hker ∘ₗ F.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f₀
  refine ⟨g ∘ₗ (SB (Matrix (n ⊕ Unit) n' k)).subtype, fun Φ Ψ hΨ => ?_⟩
  have h1 : g (F Φ) = L Φ := by
    have := LinearMap.congr_fun hg ⟨F Φ, LinearMap.mem_range_self F Φ⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at this
    rw [this]
    simp [f₀, LinearMap.quotKerEquivRange_symm_apply_image]
  rw [LinearMap.comp_apply, Submodule.coe_subtype, hΨ]
  exact h1.symm
end GlobalTheory.PartRed
