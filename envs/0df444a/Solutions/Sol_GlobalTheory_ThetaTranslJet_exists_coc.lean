-- Prove2me | solution 1 for GlobalTheory.ThetaTranslJet.exists_coc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:33:11.327777+00:00
-- url     : https://prove2.me/submissions/cf3bd47e-47bf-4ff1-b14e-17d67d34b014

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImFormApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaFunctionIsogenyRestriction
import Theorems.Thm_GlobalTheory_UpperHalfImaginaryForm_exists_coc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ReciprocityTheory.ChartRestriction.G.I2
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaTranslJet
namespace GlobalTheory.ThetaTranslJet
theorem _root_.solution {ι : Type} [Fintype ι]
    (b : Module.Basis (Fin (2 * Fintype.card ι)) ℝ (EuclideanSpace ℂ ι))
    (hint : ∀ x y : EuclideanSpace ℂ ι, x ∈ lat b → y ∈ lat b → ∃ k : ℤ, (Hf x y).im = k)
    (hperf : ∀ φ : lat b →+ ℤ, ∃ x ∈ lat b, ∀ y : lat b,
      (φ y : ℝ) = (Hf x (y : EuclideanSpace ℂ ι)).im) :
    ∃ Y : GT ι, Y.b = b ∧ FPw.Coc Y 1 := by
  first
  | exact @_root_.GlobalTheory.UpperHalfImaginaryForm.exists_coc
  | exact _root_.GlobalTheory.UpperHalfImaginaryForm.exists_coc
  | (apply _root_.GlobalTheory.UpperHalfImaginaryForm.exists_coc <;> assumption)
  | (intros; apply _root_.GlobalTheory.UpperHalfImaginaryForm.exists_coc <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UpperHalfImaginaryForm.exists_coc <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UpperHalfImaginaryForm.exists_coc ..)
end GlobalTheory.ThetaTranslJet
