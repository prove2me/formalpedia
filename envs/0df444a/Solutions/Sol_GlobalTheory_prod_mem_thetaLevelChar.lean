-- Prove2me | solution 1 for GlobalTheory.prod_mem_thetaLevelChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:23:17.940814+00:00
-- url     : https://prove2.me/submissions/8fdcf232-acad-406a-8a9e-b68260acf26c

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Theorems.Thm_GlobalTheory_one_mem_thetaLevelChar
import Theorems.Thm_GlobalTheory_mul_mem_thetaLevelChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
open GlobalTheory
variable {ι : Type} [Fintype ι]
variable {N M : ℕ} {τ : Matrix ι ι ℂ} {a b : ι → ℝ} {f g : (ι → ℂ) → ℂ}
namespace GlobalTheory
theorem _root_.solution {κ : Type*} (s : Finset κ) {d : κ → ℕ} {F : κ → (ι → ℂ) → ℂ}
    (hF : ∀ i ∈ s, F i ∈ thetaLevelChar a b (d i) τ) :
    ∏ i ∈ s, F i ∈ thetaLevelChar a b (∑ i ∈ s, d i) τ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact one_mem_thetaLevelChar
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact mul_mem_thetaLevelChar (hF i (Finset.mem_insert_self _ _))
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))
end GlobalTheory
