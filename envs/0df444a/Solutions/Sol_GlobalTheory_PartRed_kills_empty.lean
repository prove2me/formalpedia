-- Prove2me | solution 1 for GlobalTheory.PartRed.kills_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:14:53.330885+00:00
-- url     : https://prove2.me/submissions/e129fa9d-28ac-4019-b4d8-f17edb8aae07

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
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] {M : Type} [AddCommGroup M]
  [Module ℂ M]
namespace GlobalTheory.PartRed
theorem _root_.solution (ψ : AddChar k Circle) (ν : Measure k) (L : SB (Matrix R Q k) →ₗ[ℂ] M)
    (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) : Kills L ψ ν w β ∅ ∅ := by
  intro Φ hΦ
  have h0 : Φ = 0 := by
    apply Subtype.ext
    funext x
    have hx := congrFun hΦ x
    unfold red at hx
    have hf : ∀ y : (∅ : Finset (R × Q)) → k, fillAt β ∅ ∅ x y = x := fun y => by ext r q; simp [fillAt]
    simp only [hf] at hx
    rw [integral_const] at hx
    have hv : (Measure.pi fun _ : (∅ : Finset (R × Q)) => ν) Set.univ = 1 := by
      rw [Measure.pi_of_empty]; simp
    have hv' : (Measure.pi fun _ : (∅ : Finset (R × Q)) => ν).real Set.univ = 1 := by
      simp [Measure.real, hv]
    rw [hv', one_smul, Pi.zero_apply] at hx
    rw [Submodule.coe_zero, Pi.zero_apply]
    exact (mul_eq_zero.mp hx).resolve_right (Circle.coe_ne_zero _)
  rw [h0, map_zero]
end GlobalTheory.PartRed
