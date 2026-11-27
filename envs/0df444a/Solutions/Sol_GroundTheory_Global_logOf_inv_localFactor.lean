-- Prove2me | solution 1 for GroundTheory.Global.logOf_inv_localFactor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:46:27.590799+00:00
-- url     : https://prove2.me/submissions/f797869c-e2e9-4234-bad4-2aa2b153401c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
import Theorems.Thm_GroundTheory_Global_logOf_inv_inertiaFactor

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
namespace GroundTheory.Global
theorem _root_.solution :
    PowerSeries.logOf ((localFactor v ρ : PowerSeries ℂ)⁻¹) =
      PowerSeries.mk fun m => if m = 0 then 0 else localAverage L v ρ.character m / m :=
  logOf_inv_inertiaFactor ρ _ _
end GroundTheory.Global
