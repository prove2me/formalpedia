-- Prove2me | solution 1 for GroundTheory.Global.exact_ofUnits_valuationVector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:57:43.325365+00:00
-- url     : https://prove2.me/submissions/0111d566-833c-44d0-9c8b-2edb33a480aa

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SUnits
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Lattice
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsExact
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsRep
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrandValue
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain MulAction Module
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
variable (S : Set (HeightOneSpectrum (𝓞 L))) [Finite S]
omit [IsGalois K L] [Finite S]
namespace GroundTheory.Global
theorem _root_.solution :
    Function.Exact (SUnit.ofUnits (K := L) S).toAdditive
      (SUnit.valuationVector (K := L) S).toAddMonoidHom := by
  intro y
  have h := SetLike.ext_iff.1 (SUnit.ker_valuationVector (K := L) S) y
  rw [LinearMap.mem_ker, LinearMap.mem_range] at h
  exact h
end GroundTheory.Global
