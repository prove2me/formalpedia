-- Prove2me | solution 1 for GroundTheory.Global.HeckeCharacter.infiniteComponent_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:26:41.095099+00:00
-- url     : https://prove2.me/submissions/9b7f6dd6-26b0-40c5-a7da-da9929a46714

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Gaussian
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplex
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_EulerFactorsArch

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField InfinitePlace InfinitePlace.Completion MeasureTheory Complex ComplexConjugate
open scoped Real
open GroundTheory GroundTheory.Global
noncomputable section
open GroundTheory.Global.HeckeCharacter
variable {K : Type*} [Field K] [NumberField K] (χ : HeckeCharacter K)
namespace GroundTheory.Global.HeckeCharacter
theorem _root_.solution (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    (χ.infiniteComponent w a : ℂ) =
      (extensionEmbedding w (a : w.Completion) / (‖(a : w.Completion)‖ : ℂ)) ^ χ.infiniteWeight w *
        ((‖(a : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ ((χ.infiniteTau w : ℂ) * I) :=
  (χ.exists_infiniteParams w).choose_spec.2 a
end GroundTheory.Global.HeckeCharacter
