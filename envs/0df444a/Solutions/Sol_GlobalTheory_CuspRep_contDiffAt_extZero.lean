-- Prove2me | solution 1 for GlobalTheory.CuspRep.contDiffAt_extZero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:48.751112+00:00
-- url     : https://prove2.me/submissions/40900c99-a289-4767-9734-b7fbabbdd6ab

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsOpenKerFinIdele
import Theorems.Thm_GlobalTheory_CuspRep_unit_ne_zero
import Theorems.Thm_GlobalTheory_CuspRep_exists_lin
import Theorems.Thm_GlobalTheory_CuspRep_extZero_eventually

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Topology
open scoped ContDiff
open GlobalTheory GlobalTheory.CuspRep
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.CuspRep
theorem _root_.solution (ψ : (ι → ℂ)ˣ →* ℂˣ) (hψ : Continuous ψ) (u : (ι → ℂ)ˣ) :
    ContDiffAt ℝ ∞ (extZero ψ) u := by
  obtain ⟨L, hL⟩ := exists_lin ψ hψ
  refine ContDiffAt.congr_of_eventuallyEq ?_ (extZero_eventually hL u)
  refine contDiffAt_const.mul (ContDiffAt.cexp (L.contDiff.contDiffAt.comp _ (contDiffAt_pi.2 fun i => ?_)))
  have h1 : ContDiffAt ℝ ∞ Complex.log ((u : ι → ℂ) i / (u : ι → ℂ) i) := by
    rw [div_self (unit_ne_zero u i)]
    exact (Complex.contDiffAt_log Complex.one_mem_slitPlane).restrict_scalars ℝ
  exact h1.comp (f := fun x : ι → ℂ => x i / (u : ι → ℂ) i) _ ((contDiffAt_apply ℝ ℂ i _).div_const _)
end GlobalTheory.CuspRep
