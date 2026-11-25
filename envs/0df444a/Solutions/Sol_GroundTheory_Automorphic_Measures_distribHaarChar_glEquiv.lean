-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.distribHaarChar_glEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:18:18.119801+00:00
-- url     : https://prove2.me/submissions/d807fedf-c2d1-4994-8b84-72ec46ec835e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Theorems.Thm_GroundTheory_Automorphic_Measures_distribHaarChar_glEquiv_diagonal
import Theorems.Thm_GroundTheory_Automorphic_Measures_distribHaarChar_glEquiv_transvection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {F} {ι : Type*} [Fintype ι]
variable [DecidableEq ι]
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution (g : GL ι F) :
    distribHaarChar (ι → F) (glEquiv g) = distribHaarChar F (Matrix.GeneralLinearGroup.det g) := by
  let φ : GL ι F →* ℝ≥0 := (distribHaarChar (ι → F)).comp glEquiv.toMonoidHom
  let ψ : GL ι F →* ℝ≥0 := (distribHaarChar F).comp Matrix.GeneralLinearGroup.det
  have key : ∀ (M : Matrix ι ι F) (h : M.det ≠ 0),
      φ (Matrix.GeneralLinearGroup.mkOfDetNeZero M h) =
        ψ (Matrix.GeneralLinearGroup.mkOfDetNeZero M h) := by
    intro M hM
    refine Matrix.diagonal_transvection_induction_of_det_ne_zero
      (fun M => ∀ h : M.det ≠ 0, φ (Matrix.GeneralLinearGroup.mkOfDetNeZero M h) =
        ψ (Matrix.GeneralLinearGroup.mkOfDetNeZero M h)) M hM ?_ ?_ ?_ hM
    · intro D _ h
      exact distribHaarChar_glEquiv_diagonal h
    · intro t h
      have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) = 1 := by
        ext
        simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]
      change distribHaarChar (ι → F) (glEquiv _) = distribHaarChar F _
      rw [distribHaarChar_glEquiv_transvection t h, hdet, map_one]
    · intro A B hA hB IHA IHB h
      have : Matrix.GeneralLinearGroup.mkOfDetNeZero (A * B) h =
          Matrix.GeneralLinearGroup.mkOfDetNeZero A hA *
            Matrix.GeneralLinearGroup.mkOfDetNeZero B hB := by
        ext : 1
        rfl
      rw [this, map_mul, map_mul, IHA hA, IHB hB]
  have hg : Matrix.GeneralLinearGroup.mkOfDetNeZero (g : Matrix ι ι F)
      (Matrix.det_ne_zero_of_left_inverse (g.inv_mul)) = g := by
    ext : 1
    rfl
  have := key _ (Matrix.det_ne_zero_of_left_inverse (g.inv_mul))
  rw [hg] at this
  exact this
end GroundTheory.Automorphic.Measures
