-- Prove2me | solution 1 for GlobalTheory.HermLineZeros.hform_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:40.537294+00:00
-- url     : https://prove2.me/submissions/4fa561af-5f7b-4dd5-9707-6fc573e359f0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HermitianFormFiniteZerosOnLineCmExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.HermLineZeros
variable {A : Type} [CommRing A] {M : ℕ}
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
variable {A : Type} [CommRing A] {M : ℕ}
namespace GlobalTheory.HermLineZeros
namespace _root_.GlobalTheory.HermLineZeros
theorem _root_.solution (s : A →+* A) (J : Matrix (Fin M) (Fin M) A)
    (i j : Fin M) :
    _root_.Formalism.UG.hform s J (Pi.single i 1) (Pi.single j 1) = J i j := by
  simp [_root_.Formalism.UG.hform, Pi.single_apply, apply_ite s]
end _root_.GlobalTheory.HermLineZeros
end GlobalTheory.HermLineZeros
