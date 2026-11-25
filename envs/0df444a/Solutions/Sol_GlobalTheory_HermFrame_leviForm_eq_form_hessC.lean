-- Prove2me | solution 1 for GlobalTheory.HermFrame.leviForm_eq_form_hessC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:51:39.910396+00:00
-- url     : https://prove2.me/submissions/1995c25b-cb5a-4c68-aaa1-3d3b4a2bc53c

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
import Theorems.Thm_GlobalTheory_leviForm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory.HermFrame
theorem _root_.solution {D : ℕ} {u : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (hu : ContDiffAt ℝ 2 u z) (ξ η : Fin D → ℂ) :
    leviForm u z ξ η = form (ReciprocityTheory.AnForm.hessC u z) ξ η := by
  have h : ∀ i j, ReciprocityTheory.AnForm.hessC u z i j =
      leviForm u z (Pi.single i 1) (Pi.single j 1) := fun i j => by
    rw [leviForm_apply hu, ReciprocityTheory.AnForm.hessC]; push_cast; ring
  have e : ∀ v : Fin D → ℂ, v = ∑ i, v i • (Pi.single i 1 : Fin D → ℂ) := fun v => by
    ext j; simp [Pi.single_apply]
  conv_lhs => rw [e ξ, e η]
  simp only [form_eq_sum, h, map_sum, map_smul, map_smulₛₗ, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end GlobalTheory.HermFrame
