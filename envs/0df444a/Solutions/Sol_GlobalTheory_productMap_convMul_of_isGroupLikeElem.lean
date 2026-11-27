-- Prove2me | solution 1 for GlobalTheory.productMap_convMul_of_isGroupLikeElem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:40:59.335946+00:00
-- url     : https://prove2.me/submissions/c788eb18-0224-4dee-8ba8-0356e111ec02

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Theorems.Thm_GlobalTheory_isGroupLikeElem_tensor_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open TensorProduct Coalgebra Bialgebra HopfAlgebra WithConv
namespace GlobalTheory
namespace CartierDual
section Modules
variable {R M N P : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] [AddCommMonoid P] [Module R P]
end Modules
section Coalgebra
variable {R H : Type*} [CommSemiring R] [Semiring H] [Algebra R H] [Module.Finite R H]
  [Module.Projective R H]
end Coalgebra
section Algebra
variable {R C C' : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [AddCommMonoid C'] [Module R C'] [Coalgebra R C']
end Algebra
section Bialgebra
variable {R H : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H] [Module.Finite R H]
  [Module.Projective R H]
end Bialgebra
section Hopf
variable {R H : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H] [Module.Finite R H]
  [Module.Projective R H]
end Hopf
section Transpose
variable {R M N P Q : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]
end Transpose
section MapAlg
variable {R C C' : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [AddCommMonoid C'] [Module R C'] [Coalgebra R C']
end MapAlg
section MapCoalg
variable {R H K : Type*} [CommSemiring R] [Semiring H] [Algebra R H] [Module.Finite R H]
  [Module.Projective R H] [Semiring K] [Algebra R K] [Module.Finite R K] [Module.Projective R K]
end MapCoalg
section Map
variable {R H K L : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H] [Module.Finite R H]
  [Module.Projective R H] [Semiring K] [Bialgebra R K] [Module.Finite R K] [Module.Projective R K]
  [Semiring L] [Bialgebra R L] [Module.Finite R L] [Module.Projective R L]
end Map
section BaseChange
variable {R : Type*} (A : Type*) {M N : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
section Coalgebra
variable {C : Type*} [AddCommMonoid C] [Module R C] [Coalgebra R C]
end Coalgebra
variable (R) (H : Type*) [Semiring H] [Bialgebra R H] [Module.Finite R H] [Module.Projective R H]
variable {R H}
end BaseChange
section Product
variable (R H K : Type*) [CommSemiring R] [Semiring H] [Bialgebra R H] [Module.Finite R H]
  [Module.Projective R H] [Semiring K] [Bialgebra R K] [Module.Finite R K] [Module.Projective R K]
end Product
section Tensor
variable {R N M N' M' : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
end Tensor
section Points
variable {R C : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [Module.Finite R C] [Module.Projective R C]
variable {A : Type*} [CommSemiring A] [Algebra R A]
end Points
section PointsBialgebra
variable {R H A : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H] [Module.Finite R H]
  [Module.Projective R H] [CommSemiring A] [Algebra R A]
end PointsBialgebra
end CartierDual
section Primitive
variable (R : Type*) {H K : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H] [Semiring K]
  [Bialgebra R K]
end Primitive
namespace CartierDual
section Lie
variable {R H : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H] [Module.Finite R H]
  [Module.Projective R H]
end Lie
section LieRing
open TrivSqZeroExt
variable (R H A M : Type*) [CommRing R] [Semiring H] [Bialgebra R H] [Module.Finite R H]
  [Module.Projective R H] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M] [Module A M]
  [Module Aᵐᵒᵖ M] [IsCentralScalar A M] [IsScalarTower R A M] [IsScalarTower R Aᵐᵒᵖ M]
variable {R H A M}
end LieRing
section MonoidAlgebra
variable (R Γ : Type*) [CommSemiring R]
variable {R Γ}
end MonoidAlgebra
section AddMonoidAlgebra
variable (R Γ : Type*) [CommSemiring R]
variable {R Γ}
end AddMonoidAlgebra
end CartierDual
section GroupLikeBase
open Algebra.TensorProduct (includeLeft includeRight productMap)
variable {R A K : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [CommSemiring K] [Bialgebra R K] {x : A ⊗[R] K} {B : Type*} [CommSemiring B] [Algebra R B]
private theorem productMap_convMul (x : A ⊗[R] K) (g : A →ₐ[R] B) (y y' : WithConv (K →ₐ[R] B)) :
    productMap g (y * y').ofConv x =
      productMap g (productMap y.ofConv y'.ofConv) (LinearMap.lTensor A comul x) := by
  induction x with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a h => simp [AlgHom.convMul_apply, productMap]
end GroupLikeBase
section Bicharacter
open CartierDual
open Algebra.TensorProduct (productMap)
variable (R : Type*) {H K : Type*} [CommSemiring R] [CommSemiring H] [Bialgebra R H]
  [CommSemiring K] [Bialgebra R K]
variable {R} {u v : H ⊗[R] K}
namespace IsBicharacter
variable {A : Type*} [CommSemiring A] [Algebra R A]
end IsBicharacter
variable [Module.Finite R H] [Module.Projective R H] [Module.Finite R K] [Module.Projective R K]
end Bicharacter
namespace CartierDual
section Canonical
variable (R H : Type*) [CommSemiring R] [AddCommMonoid H] [Module R H] [Module.Finite R H]
  [Module.Projective R H]
variable {R H}
end Canonical
section CanonicalPairing
variable {R H : Type*} [CommSemiring R] [CommSemiring H] [Bialgebra R H] [IsCocomm R H]
  [Module.Finite R H] [Module.Projective R H]
end CanonicalPairing
end CartierDual
section PairingMap
open CartierDual
variable {R : Type*} [CommSemiring R]
variable {H K : Type*} [CommSemiring H] [Bialgebra R H] [CommSemiring K] [Bialgebra R K]
  {u : H ⊗[R] K}
variable (A : Type*) [CommSemiring A] [Algebra R A]
variable [Module.Finite R H] [Module.Projective R H] [Module.Finite R K] [Module.Projective R K]
end PairingMap
section Examples
open CartierDual
example (R H : Type) [CommRing R] [CommRing H] [HopfAlgebra R H] [IsCocomm R H]
    [Module.Finite R H] [Module.Projective R H] : CommHopfAlgCat R :=
  have : IsCocomm R (CartierDual R H) := inferInstance
  have : Module.Finite R (CartierDual R H) := inferInstance
  have : Module.Projective R (CartierDual R H) := inferInstance
  CommHopfAlgCat.of R (CartierDual R H)
example : addMonoidAlgebraEquiv ℤ (ZMod 3)
    (antipode ℤ ((addMonoidAlgebraEquiv ℤ (ZMod 3)).symm (Pi.single 1 1))) = Pi.single 2 1 := by
  funext γ
  rw [antipode_addMonoidAlgebra, AlgEquiv.apply_symm_apply]
  revert γ
  decide
example (R : Type) [CommRing R] [Nontrivial R] :
    IsPerfectBicharacter R (canonical R (AddMonoidAlgebra R (ZMod 2))) ∧
      ¬ IsGroupLikeElem R (canonical R (AddMonoidAlgebra R (ZMod 2))) :=
  ⟨isPerfectBicharacter_canonical _ _, fun h => canonical_zmod_two_ne_one R
    ((isPerfectBicharacter_canonical _ _).toIsBicharacter.eq_one_of_isGroupLikeElem h)⟩
example : IsPrimitiveElem (ZMod 2) ((addMonoidAlgebraEquiv (ZMod 2) (ZMod 2)).symm id) := by
  refine tensor_ext fun a b => ?_
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
  | single g r =>
    induction b using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
    | single g' r' =>
      simp [AddMonoidAlgebra.single_mul_single]
      ring
end Examples
end GlobalTheory
end
end

set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra HopfAlgebra WithConv
open GlobalTheory
open Algebra.TensorProduct (includeLeft includeRight productMap)
variable {R A K : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [CommSemiring K] [Bialgebra R K] {x : A ⊗[R] K} {B : Type*} [CommSemiring B] [Algebra R B]
namespace GlobalTheory
theorem _root_.solution (hx : IsGroupLikeElem A x) (g : A →ₐ[R] B)
    (y y' : WithConv (K →ₐ[R] B)) :
    productMap g (y * y').ofConv x = productMap g y.ofConv x * productMap g y'.ofConv x := by
  rw [productMap_convMul, ((isGroupLikeElem_tensor_iff x).1 hx).2, map_mul]
  congr 1
  · rw [← AlgHom.comp_apply]; congr 1; ext <;> simp
  · rw [← AlgHom.comp_apply]; congr 1; ext <;> simp
end GlobalTheory
