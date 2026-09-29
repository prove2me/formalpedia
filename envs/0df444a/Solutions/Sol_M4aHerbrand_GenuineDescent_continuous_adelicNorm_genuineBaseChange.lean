-- Prove2me | solution 1 for M4aHerbrand.GenuineDescent.continuous_adelicNorm_genuineBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/f97c3d03-0bc3-555f-8bdb-389026eec770

import Mathlib
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_GenuineDescent_continuous_adelicNorm_genuineBaseChange

set_option autoImplicit false

open NumberField M4aHerbrand M4aHerbrand.GenuineDescent

namespace HCont

theorem continuous_adelicNorm_of_continuous_β (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (B : AdeleBaseChange (𝓞 E) E (𝓞 F) F) (hβ : Continuous B.β) : Continuous B.adelicNorm := by
  classical
  letI : Algebra (AdeleRing (𝓞 E) E) (AdeleRing (𝓞 F) F) := B.β.toAlgebra
  haveI : Module.Finite E F := Module.Finite.of_restrictScalars_finite ℚ E F
  haveI : IsModuleTopology (AdeleRing (𝓞 E) E) (AdeleRing (𝓞 F) F) :=
    M4aHerbrand.Bridge.isModuleTopology_adeleRing_of_free (𝓞 E) E (𝓞 F) F hβ B.tensorEquiv
  haveI : Module.Finite (AdeleRing (𝓞 E) E) (AdeleRing (𝓞 F) F) :=
    Module.Finite.equiv B.tensorEquiv.toLinearEquiv
  haveI : Module.Free (AdeleRing (𝓞 E) E) (AdeleRing (𝓞 F) F) :=
    Module.Free.of_equiv B.tensorEquiv.toLinearEquiv
  let b := Module.Free.chooseBasis (AdeleRing (𝓞 E) E) (AdeleRing (𝓞 F) F)
  have h : (B.adelicNorm : AdeleRing (𝓞 F) F → AdeleRing (𝓞 E) E) = fun x => (Algebra.leftMulMatrix b x).det := by
    funext x
    exact Algebra.norm_eq_matrix_det b x
  rw [h]
  exact (IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap).matrix_det

end HCont

theorem solution
    (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] :
    Continuous (genuineBaseChange K M).adelicNorm :=
  HCont.continuous_adelicNorm_of_continuous_β K M (genuineBaseChange K M) (M4aHerbrand.Bridge.continuous_genuineβ K M)

end S_M4aHerbrand_GenuineDescent_continuous_adelicNorm_genuineBaseChange
end P2MW
export P2MW.S_M4aHerbrand_GenuineDescent_continuous_adelicNorm_genuineBaseChange (solution)
