-- Prove2me | solution 1 for GlobalTheory.CuspRep.extZero_eventually
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:13.543908+00:00
-- url     : https://prove2.me/submissions/aa0e2a50-b503-46a9-96de-cdd1b2132b4b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsOpenKerFinIdele
import Theorems.Thm_GlobalTheory_CuspRep_unit_ne_zero
import Theorems.Thm_GlobalTheory_CuspRep_extZero_unit

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
theorem _root_.solution {ψ : (ι → ℂ)ˣ →* ℂˣ} {L : (ι → ℂ) →L[ℝ] ℂ}
    (hL : ∀ z, ((ψ (expU z) : ℂˣ) : ℂ) = Complex.exp (L z)) (u : (ι → ℂ)ˣ) :
    extZero ψ =ᶠ[𝓝 (u : ι → ℂ)] fun x => (ψ u : ℂˣ) * Complex.exp (L fun i => Complex.log (x i / (u : ι → ℂ) i)) := by
  have h : ∀ᶠ x in 𝓝 (u : ι → ℂ), ∀ i, x i ≠ 0 :=
    Filter.eventually_all.2 fun i => (continuous_apply i).continuousAt.eventually_ne (unit_ne_zero u i)
  filter_upwards [h] with x hx
  have e : x = ((u * expU fun i => Complex.log (x i / (u : ι → ℂ) i) : (ι → ℂ)ˣ) : ι → ℂ) := by
    funext i
    change x i = (u : ι → ℂ) i * Complex.exp (Complex.log (x i / (u : ι → ℂ) i))
    rw [Complex.exp_log (div_ne_zero (hx i) (unit_ne_zero u i)), mul_div_cancel₀ _ (unit_ne_zero u i)]
  conv_lhs => rw [e, extZero_unit, map_mul, Units.val_mul, hL]
end GlobalTheory.CuspRep
