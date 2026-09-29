-- Prove2me | solution 1 for LanglandsTunnell.Converse.isAdmissibleTwist_comp_idelicNorm_genuineBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/3f5a55ed-dee7-5358-899b-8a550c3ac3ca

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_adelicNorm_genuineBaseChange_algebraMap
import Theorems.Thm_M4aHerbrand_GenuineDescent_continuous_adelicNorm_genuineBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_isAdmissibleTwist_comp_idelicNorm_genuineBaseChange

set_option autoImplicit false

open NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain LanglandsTunnell.Converse M4aHerbrand.GenuineDescent

namespace LTIdelicNormBaseChange

variable (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]

theorem idelicNorm_principal (u : Mˣ) :
    (genuineBaseChange E M).idelicNorm (Units.map (algebraMap M (AdeleRing (𝓞 M) M) : M →* _) u) =
      Units.map (algebraMap E (AdeleRing (𝓞 E) E) : E →* _) (Units.map (Algebra.norm E : M →* E) u) := by
  refine Units.ext ?_
  show (genuineBaseChange E M).adelicNorm (algebraMap M (AdeleRing (𝓞 M) M) (u : M)) =
    algebraMap E (AdeleRing (𝓞 E) E) (Algebra.norm E (u : M))
  exact adelicNorm_genuineBaseChange_algebraMap E M (u : M)

theorem continuous_idelicNorm : Continuous (genuineBaseChange E M).idelicNorm :=
  Continuous.units_map _ (continuous_adelicNorm_genuineBaseChange E M)

end LTIdelicNormBaseChange

theorem solution
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (η : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (hη : IsAdmissibleTwist E η) :
    IsAdmissibleTwist M (η.comp (genuineBaseChange E M).idelicNorm) := by
  obtain ⟨hcl, hcont, hun⟩ := hη
  refine ⟨?_, ?_, ?_⟩
  · intro u
    rw [MonoidHom.comp_apply, LTIdelicNormBaseChange.idelicNorm_principal E M u]
    exact hcl _
  · exact hcont.comp (LTIdelicNormBaseChange.continuous_idelicNorm E M)
  · intro x
    exact hun _

end S_LanglandsTunnell_Converse_isAdmissibleTwist_comp_idelicNorm_genuineBaseChange
end P2MW
export P2MW.S_LanglandsTunnell_Converse_isAdmissibleTwist_comp_idelicNorm_genuineBaseChange (solution)
