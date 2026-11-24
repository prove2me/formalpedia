-- Prove2me | solution 1 for GlobalTheory.ClassMin.gram_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:12:00.983688+00:00
-- url     : https://prove2.me/submissions/0d68be07-e349-4f1b-a311-a68a7156f340

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Theorems.Thm_GlobalTheory_ClassMin_dotProduct_gram_pos_of_rat

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
theorem _root_.solution [Finite ι] (hQ : Q.PosDef) (e : Module.Basis ι ℤ X) :
    (gram Q e).PosSemidef := by
  have := Fintype.ofFinite ι
  refine posSemidef_iff_dotProduct_mulVec.mpr ⟨gram_isHermitian Q e, fun x => ?_⟩
  rw [star_trivial]
  have hd : DenseRange (Pi.map fun (_ : ι) (q : ℚ) => (q : ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  refine hd.induction_on x (isClosed_le continuous_const ?_) fun y => ?_
  · simp only [dotProduct, mulVec]
    fun_prop
  · rcases eq_or_ne y 0 with rfl | hy
    · have : (Pi.map (fun (_ : ι) (q : ℚ) => (q : ℝ)) 0) = 0 := by funext i; simp
      rw [this, zero_dotProduct]
    · exact (dotProduct_gram_pos_of_rat hQ e hy).le
end GlobalTheory.ClassMin
