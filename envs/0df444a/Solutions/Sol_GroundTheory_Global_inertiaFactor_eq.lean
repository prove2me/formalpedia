-- Prove2me | solution 1 for GroundTheory.Global.inertiaFactor_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:50:04.771258+00:00
-- url     : https://prove2.me/submissions/c811976e-28dd-4dbf-9100-05acb3c8ef2e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
import Theorems.Thm_GroundTheory_Global_cosetAverage_inertia_eq
import Theorems.Thm_GroundTheory_Global_trace_invariantsEnd_pow
import Theorems.Thm_GroundTheory_Global_reverse_charpoly_eq_of_trace_pow_eq


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
theorem _root_.solution (w w' : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    [w'.asIdeal.LiesOver v.asIdeal] {φ φ' : Gal(L/K)} (hφ : IsArithFrobAt (𝓞 K) φ w.asIdeal)
    (hφ' : IsArithFrobAt (𝓞 K) φ' w'.asIdeal) :
    inertiaFactor ρ w φ hφ.mem_stabilizer = inertiaFactor ρ w' φ' hφ'.mem_stabilizer :=
  reverse_charpoly_eq_of_trace_pow_eq _ _ fun m _ => by
    rw [trace_invariantsEnd_pow, trace_invariantsEnd_pow,
      cosetAverage_inertia_eq v ρ.character (fun g h => ρ.char_conj g h) w w' hφ hφ' m]
end GroundTheory.Global
