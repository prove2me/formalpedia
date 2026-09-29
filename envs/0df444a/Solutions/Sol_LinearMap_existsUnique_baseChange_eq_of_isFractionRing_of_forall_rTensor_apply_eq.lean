-- Prove2me | solution 1 for LinearMap.existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/5ffc84bb-f9bc-553f-bedf-6662e3fdb226

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace ModuleDescent

variable {O : Type u} [CommRing O] {S T : Type u} [CommRing S] [CommRing T] [Algebra O S] [Algebra O T]
  {N : Type u} [AddCommGroup N] [Module O N] {ι : Type*}

theorem repr_rTensor (φ : S →ₐ[O] T) (b : Module.Basis ι O N) (x : S ⊗[O] N) (j : ι) :
    (Algebra.TensorProduct.basis T b).repr (φ.toLinearMap.rTensor N x) j =
      φ ((Algebra.TensorProduct.basis S b).repr x j) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, Finsupp.zero_apply, Finsupp.zero_apply, map_zero]
  | tmul s n =>
    rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, Algebra.TensorProduct.basis_repr_tmul,
      Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.mapRange_apply,
      Finsupp.mapRange_apply, smul_eq_mul, smul_eq_mul, map_mul, AlgHom.commutes]
  | add x y hx hy =>
    rw [map_add, map_add, map_add, Finsupp.add_apply, Finsupp.add_apply, map_add, hx, hy]

end ModuleDescent

theorem solution
    (O : Type u) [CommRing O] [IsDomain O] (K : Type u) [Field K] [Algebra O K] [IsFractionRing O K]
    (Oh : Type u) [CommRing Oh] [Algebra O Oh]
    (Kh : Type u) [CommRing Kh] [Algebra O Kh] [Algebra K Kh] [Algebra Oh Kh] [IsScalarTower O K Kh] [IsScalarTower O Oh Kh]
    (hinj : Function.Injective (algebraMap Oh Kh))
    (hcap : ∀ (x : K) (y : Oh), algebraMap K Kh x = algebraMap Oh Kh y → ∃ z : O, algebraMap O K z = x)
    (M : Type u) [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M]
    (N : Type u) [AddCommGroup N] [Module O N] [Module.Free O N] [Module.Finite O N]
    (fK : K ⊗[O] M →ₗ[K] K ⊗[O] N) (fOh : Oh ⊗[O] M →ₗ[Oh] Oh ⊗[O] N)
    (hagree : ∀ m : M,
      ((IsScalarTower.toAlgHom O K Kh).toLinearMap.rTensor N) (fK ((1 : K) ⊗ₜ m)) =
        ((IsScalarTower.toAlgHom O Oh Kh).toLinearMap.rTensor N) (fOh ((1 : Oh) ⊗ₜ m))) :
    ∃! f : M →ₗ[O] N, f.baseChange K = fK ∧ f.baseChange Oh = fOh := by
  classical
  haveI : FaithfulSMul O K := (faithfulSMul_iff_algebraMap_injective O K).mpr (IsFractionRing.injective O K)
  let bM := Module.Free.chooseBasis O M
  let bN := Module.Free.chooseBasis O N

  let aK : Module.Free.ChooseBasisIndex O N → Module.Free.ChooseBasisIndex O M → K :=
    fun j i => (Algebra.TensorProduct.basis K bN).repr (fK ((1 : K) ⊗ₜ bM i)) j
  let aOh : Module.Free.ChooseBasisIndex O N → Module.Free.ChooseBasisIndex O M → Oh :=
    fun j i => (Algebra.TensorProduct.basis Oh bN).repr (fOh ((1 : Oh) ⊗ₜ bM i)) j
  have hcoord : ∀ j i, algebraMap K Kh (aK j i) = algebraMap Oh Kh (aOh j i) := by
    intro j i
    have h := congrArg (fun x => (Algebra.TensorProduct.basis Kh bN).repr x j) (hagree (bM i))
    simp only [ModuleDescent.repr_rTensor] at h
    exact h

  choose z hz using fun j i => hcap (aK j i) (aOh j i) (hcoord j i)
  have hzOh : ∀ j i, algebraMap O Oh (z j i) = aOh j i := by
    intro j i
    apply hinj
    rw [← hcoord, ← hz, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

  let f : M →ₗ[O] N := bM.constr O fun i => ∑ j, z j i • bN j
  have hf : ∀ i, f (bM i) = ∑ j, z j i • bN j := fun i => by
    show bM.constr O (fun i => ∑ j, z j i • bN j) (bM i) = _
    rw [Module.Basis.constr_basis]

  have hbc : ∀ (S : Type u) [CommRing S] [Algebra O S] (g : S ⊗[O] M →ₗ[S] S ⊗[O] N)
      (hg : ∀ j i, (Algebra.TensorProduct.basis S bN).repr (g ((1 : S) ⊗ₜ bM i)) j = algebraMap O S (z j i)),
      f.baseChange S = g := by
    intro S _ _ g hg
    apply (Algebra.TensorProduct.basis S bM).ext
    intro i
    rw [Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul, hf, TensorProduct.tmul_sum]
    rw [← (Algebra.TensorProduct.basis S bN).sum_repr (g ((1 : S) ⊗ₜ bM i))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hg, Algebra.TensorProduct.basis_apply, TensorProduct.tmul_smul, algebraMap_smul]
  refine ⟨f, ⟨hbc K fK (fun j i => (hz j i).symm), hbc Oh fOh (fun j i => (hzOh j i).symm)⟩, ?_⟩

  rintro f' ⟨hf'K, -⟩
  apply LinearMap.baseChangeHom_injective (R := O) (S := K) (M := M) (N := N)
  rw [LinearMap.baseChangeHom_apply, LinearMap.baseChangeHom_apply, hf'K]
  exact (hbc K fK (fun j i => (hz j i).symm)).symm

end S_LinearMap_existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq
end P2MW
export P2MW.S_LinearMap_existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq (solution)
