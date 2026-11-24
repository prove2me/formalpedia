-- Prove2me | solution 1 for GlobalTheory.FunObj.OneCosetProof.psi_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:11:02.638235+00:00
-- url     : https://prove2.me/submissions/34aefa70-2fcf-4218-8b9b-47e8b4df7a1c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsKOOfDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCosetOfIsTensor
import Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_phase_shift
import Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_moved_shift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.OneCosetProof
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
variable {k : Type} [Field k]
variable {G : Grid k}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ}
variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {ν : Measure k}
namespace GlobalTheory.FunObj.OneCosetProof
theorem _root_.solution [ν.IsAddHaarMeasure] (hs : 1 ≤ G.s) (hT : G.IsTensor ϖ e (oppositePath G.m) T) (g : G.VertexGroup)
    (x : ColArgs G) (y : RowArgs G) (h : flatTensor hs ψ ν (moved G false g T) x y ≠ 0) (Y : Shift G)
    (hY : ∀ j r s, ¬ Free ((G.m - 2 - j.val) / 2 + 1) (r, s) → Y j r s = 0) (hX : ∀ j r s, Y j r (.inl s) = 0)
    (hL : ∀ (j : Fin (G.m - 1)) r s, valuation k ((((frameGL (tgt_eq hs j) (g (G.m, j + 1)))⁻¹).val * Y j *
      (frameGL (src_eq hs j) (g (G.m, j))).val) r s) ≤ valuation k ((ϖ ^ e : kˣ) : k)) :
    ψ (∑ j, ch (Y j)) = 1 := by
  set s := ∑ j, ch (Y j) with hs_def
  have key : ∀ v : Vars G, flatIntegrand hs ψ (moved G false g T) x y (v + Y.vars) =
      (ψ (-s) : ℂ) * flatIntegrand hs ψ (moved G false g T) x y v := by
    intro v
    unfold flatIntegrand
    rw [moved_shift hs hT g x y v Y hY hL, phase_shift x v Y hY hX, neg_add, AddChar.map_add_eq_mul]
    push_cast
    ring
  have i0 : SigmaCompactSpace k := by
    have hZ : Countable ℤ := Countable.of_equiv _ Equiv.intEquivNat.symm
    have hz : Countable (WithZero (Multiplicative ℤ)) := @Option.instCountable ℤ hZ
    have hc : Countable (ValueGroupWithZero k) :=
      Countable.of_equiv _ (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k).toMulEquiv.toEquiv.symm
    have hu : (⋃ γ : ValueGroupWithZero k, {x : k | valuation k x ≤ γ}) = Set.univ :=
      Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ⟨valuation k x, show valuation k x ≤ valuation k x from le_rfl⟩
    have hsig : IsSigmaCompact (Set.univ : Set k) := by
      rw [← hu]
      exact isSigmaCompact_iUnion_of_isCompact _ fun γ => IsNonarchimedeanLocalField.isCompact_closedBall k γ
    exact isSigmaCompact_univ_iff.mp hsig
  have i1 : SigmaFinite ν := inferInstance
  have i2 : ν.IsAddRightInvariant := inferInstance
  have : (varsVol G ν).IsAddRightInvariant := by
    unfold varsVol
    infer_instance
  have hint := MeasureTheory.integral_add_right_eq_self (μ := varsVol G ν)
    (flatIntegrand hs ψ (moved G false g T) x y) Y.vars
  simp_rw [key] at hint
  rw [MeasureTheory.integral_const_mul] at hint
  unfold flatTensor at h
  have h1 : ((ψ (-s) : Circle) : ℂ) = 1 := by
    refine mul_right_cancel₀ h ?_
    rw [one_mul]
    exact hint
  have h2 : ψ (-s) = 1 := by
    exact Circle.coe_eq_one.mp h1
  rw [AddChar.map_neg_eq_inv, inv_eq_one] at h2
  exact h2
end GlobalTheory.FunObj.OneCosetProof
