-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.mem_maxOrder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:57:43.203472+00:00
-- url     : https://prove2.me/submissions/2ad071aa-cef2-42ab-93ca-ba0b6ed8893c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualUnramifiedPlaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F))
    (z : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E) :
    z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.maxOrder F E v ↔
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.intToEv F E v).IsIntegralElem z :=
  Iff.rfl
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces
end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces
