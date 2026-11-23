-- Prove2me | solution 1 for GlobalTheory.Mem.Chr.Model.localIdele_snd_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:00.534359+00:00
-- url     : https://prove2.me/submissions/7fad3419-32f8-421f-b088-7c4bc05420df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ValuedAlgebraMapEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_DiagUnitsEqLocalIdele

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Chr.Model
variable (L : Type) [Field L] [NumberField L]
namespace GlobalTheory.Mem.Chr.Model
theorem _root_.solution (v w : HeightOneSpectrum (𝓞 L)) (h : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 w = 1 := by
  classical
  change Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
    (x : v.adicCompletion L) w = 1
  exact Pi.mulSingle_eq_of_ne h _
end GlobalTheory.Mem.Chr.Model
