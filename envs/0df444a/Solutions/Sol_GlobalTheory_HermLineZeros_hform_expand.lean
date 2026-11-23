-- Prove2me | solution 1 for GlobalTheory.HermLineZeros.hform_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:43.199099+00:00
-- url     : https://prove2.me/submissions/3d75232d-c727-458e-b133-cc5361cb851b

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
    (x y : Fin M → A) (c : A) :
    _root_.Formalism.UG.hform s J (x + c • y) (x + c • y) =
      _root_.Formalism.UG.hform s J x x + c * _root_.Formalism.UG.hform s J x y + s c * _root_.Formalism.UG.hform s J y x
        + s c * c * _root_.Formalism.UG.hform s J y y := by
  unfold _root_.Formalism.UG.hform
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
  ring
end _root_.GlobalTheory.HermLineZeros
end GlobalTheory.HermLineZeros
