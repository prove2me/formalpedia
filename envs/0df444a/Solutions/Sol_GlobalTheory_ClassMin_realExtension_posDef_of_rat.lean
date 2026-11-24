-- Prove2me | solution 1 for GlobalTheory.ClassMin.realExtension_posDef_of_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:30:00.392805+00:00
-- url     : https://prove2.me/submissions/a23a0e44-787f-478c-bf28-5c650aa24d56

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Theorems.Thm_GlobalTheory_ClassMin_dotProduct_gram_pos_of_rat
import Theorems.Thm_GlobalTheory_ClassMin_gram_posSemidef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassMin
open QuadraticMap Matrix Filter
open scoped TensorProduct
variable {X : Type*} [AddCommGroup X] {ι : Type*} {Q : QuadraticMap ℤ X ℝ}
namespace GlobalTheory.ClassMin
theorem _root_.solution [Module.Free ℤ X] [Module.Finite ℤ X] (hQ : Q.PosDef)
    (hr : ∀ x y, ∃ q : ℚ, polar Q x y = q) : (realExtension Q).PosDef := by
  classical
  let e := Module.Free.chooseBasis ℤ X
  choose M hM using fun i j => hr (e i) (e j)
  have hG : gram Q e = (Matrix.of M).map (Rat.castHom ℝ) := by
    ext i j
    simp [hM]
  rw [realExtension_posDef_iff Q e, (gram_posSemidef hQ e).posDef_iff_det_ne_zero]
  intro h0
  rw [hG, ← RingHom.mapMatrix_apply, ← RingHom.map_det, map_eq_zero] at h0
  obtain ⟨v, hv, hMv⟩ := exists_mulVec_eq_zero_iff.mpr h0
  have h1 := dotProduct_gram_pos_of_rat hQ e hv
  have h2 : (gram Q e *ᵥ fun i => (v i : ℝ)) = 0 := by
    funext i
    have := congrArg (Rat.castHom ℝ) (congrFun hMv i)
    rw [RingHom.map_mulVec] at this
    rw [hG]
    simpa [Function.comp_def] using this
  rw [h2, dotProduct_zero] at h1
  exact lt_irrefl _ h1
end GlobalTheory.ClassMin
