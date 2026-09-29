-- Prove2me | solution 1 for M4aHerbrand.GenuineDescent.adelicNorm_genuineBaseChange_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/74c25801-73a4-5904-a434-da163c3e15ca

import Mathlib
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_GenuineDescent_adelicNorm_genuineBaseChange_algebraMap

set_option autoImplicit false

open NumberField M4aHerbrand M4aHerbrand.GenuineDescent
open scoped TensorProduct

namespace HIC

theorem norm_one_tmul {R S A : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [Algebra R A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R S) (s : S) :
    Algebra.norm A ((1 : A) ⊗ₜ[R] s) = algebraMap R A (Algebra.norm R s) := by
  rw [Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis A b), Algebra.norm_eq_matrix_det b, RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.basis_repr_tmul,
    one_smul, Finsupp.mapRange_apply]

theorem adelicNorm_algebraMap (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (B : AdeleBaseChange (𝓞 E) E (𝓞 F) F) (f : F) :
    B.adelicNorm (algebraMap F (AdeleRing (𝓞 F) F) f) = algebraMap E (AdeleRing (𝓞 E) E) (Algebra.norm E f) := by
  classical
  letI : Algebra (AdeleRing (𝓞 E) E) (AdeleRing (𝓞 F) F) := B.β.toAlgebra
  haveI : Module.Finite E F := Module.Finite.of_restrictScalars_finite ℚ E F
  rw [← B.tensorEquiv_one_tmul f]
  show Algebra.norm (AdeleRing (𝓞 E) E) (B.tensorEquiv ((1 : AdeleRing (𝓞 E) E) ⊗ₜ[E] f)) = _
  rw [Algebra.norm_eq_of_algEquiv]
  exact norm_one_tmul (Module.Free.chooseBasis E F) f

end HIC

theorem solution
    (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (m : M) :
    (genuineBaseChange K M).adelicNorm (algebraMap M (AdeleRing (𝓞 M) M) m) =
      algebraMap K (AdeleRing (𝓞 K) K) (Algebra.norm K m) :=
  HIC.adelicNorm_algebraMap K M (genuineBaseChange K M) m

end S_M4aHerbrand_GenuineDescent_adelicNorm_genuineBaseChange_algebraMap
end P2MW
export P2MW.S_M4aHerbrand_GenuineDescent_adelicNorm_genuineBaseChange_algebraMap (solution)
