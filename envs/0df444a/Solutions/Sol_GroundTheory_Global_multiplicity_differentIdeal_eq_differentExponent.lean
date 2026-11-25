-- Prove2me | solution 1 for GroundTheory.Global.multiplicity_differentIdeal_eq_differentExponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:01:35.638053+00:00
-- url     : https://prove2.me/submissions/6214ab1a-687c-4d7b-9d7c-ea2649c49793

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_LocalFields_Different
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminantLocal
import Theorems.Thm_GroundTheory_Global_multiplicity_differentIdeal
import Theorems.Thm_GroundTheory_Global_algebraMap_adicCompletion_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.LocalField
open scoped WithZero
open GroundTheory GroundTheory.Global
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
namespace GroundTheory.Global
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal]
    [iA : Algebra (v.adicCompletion K) (w.adicCompletion M)]
    [ContinuousSMul (v.adicCompletion K) (w.adicCompletion M)]
    [IsScalarTower K (v.adicCompletion K) (w.adicCompletion M)] :
    multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 M)) =
      differentExponent (v.adicCompletion K) (w.adicCompletion M) := by
  have h : iA = SemiLocal.algebraCompletion v w := Algebra.algebra_ext _ _ fun r ↦ by
    rw [algebraMap_adicCompletion_eq v w]
    rfl
  subst h
  exact multiplicity_differentIdeal v w
end GroundTheory.Global
