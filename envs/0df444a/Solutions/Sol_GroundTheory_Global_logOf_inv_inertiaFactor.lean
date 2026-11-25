-- Prove2me | solution 1 for GroundTheory.Global.logOf_inv_inertiaFactor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:50:05.663396+00:00
-- url     : https://prove2.me/submissions/08ef5d9d-235c-4250-960a-3f73185e6805

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
import Theorems.Thm_GroundTheory_Global_trace_invariantsEnd_pow
import Theorems.Thm_GroundTheory_Global_logOf_inv_reverse_charpoly


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField Polynomial
open scoped Pointwise
open GroundTheory GroundTheory.Global
variable {K L V : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (v : HeightOneSpectrum (𝓞 K)) [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (ρ : Representation ℂ Gal(L/K) V)
omit [IsGalois K L]
namespace GroundTheory.Global
theorem _root_.solution (w : HeightOneSpectrum (𝓞 L)) {φ : Gal(L/K)}
    (hφ : φ ∈ MulAction.stabilizer Gal(L/K) w.asIdeal) :
    PowerSeries.logOf ((inertiaFactor ρ w φ hφ : PowerSeries ℂ)⁻¹) =
      PowerSeries.mk fun m => if m = 0 then 0 else
        cosetAverage (w.asIdeal.inertia Gal(L/K)) ρ.character (φ ^ m) / m := by
  rw [inertiaFactor, logOf_inv_reverse_charpoly]
  congr 1
  funext m
  rw [trace_invariantsEnd_pow]
end GroundTheory.Global
