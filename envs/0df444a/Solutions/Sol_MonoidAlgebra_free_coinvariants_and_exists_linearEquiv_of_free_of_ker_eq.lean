-- Prove2me | solution 1 for MonoidAlgebra.free_coinvariants_and_exists_linearEquiv_of_free_of_ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/e6e034b0-d6cd-51d4-acb7-6936fe70f604

import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MonoidAlgebra_free_coinvariants_and_exists_linearEquiv_of_free_of_ker_eq

set_option autoImplicit false

open Module

noncomputable section

namespace TWCoinvariants

section Coinvariants

variable {𝒪 : Type*} [CommRing 𝒪] {Δ : Type*} [CommMonoid Δ]
variable {M : Type*} [AddCommGroup M] [Module (MonoidAlgebra 𝒪 Δ) M] [Module 𝒪 M]
  [IsScalarTower 𝒪 (MonoidAlgebra 𝒪 Δ) M]

abbrev aug (𝒪 : Type*) [CommRing 𝒪] (Δ : Type*) [CommMonoid Δ] : Ideal (MonoidAlgebra 𝒪 Δ) :=
  RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ))

abbrev augSmul (𝒪 : Type*) [CommRing 𝒪] (Δ : Type*) [CommMonoid Δ] (M : Type*) [AddCommGroup M]
    [Module (MonoidAlgebra 𝒪 Δ) M] : Submodule (MonoidAlgebra 𝒪 Δ) M :=
  aug 𝒪 Δ • (⊤ : Submodule (MonoidAlgebra 𝒪 Δ) M)

theorem mem_aug_iff (a : MonoidAlgebra 𝒪 Δ) : a ∈ aug 𝒪 Δ ↔ Coalgebra.counit (R := 𝒪) a = 0 := by
  simp [aug, RingHom.mem_ker]

variable {κ : Type*}

noncomputable def reduce (b : Basis κ (MonoidAlgebra 𝒪 Δ) M) : M →ₗ[𝒪] (κ →₀ 𝒪) :=
  (Finsupp.mapRange.linearMap (Coalgebra.counit : MonoidAlgebra 𝒪 Δ →ₗ[𝒪] 𝒪)) ∘ₗ
    (b.repr.toLinearMap.restrictScalars 𝒪)

theorem reduce_apply (b : Basis κ (MonoidAlgebra 𝒪 Δ) M) (m : M) (k : κ) :
    reduce b m k = Coalgebra.counit (R := 𝒪) (b.repr m k) := by
  simp [reduce]

theorem reduce_smul (b : Basis κ (MonoidAlgebra 𝒪 Δ) M) (a : MonoidAlgebra 𝒪 Δ) (m : M) :
    reduce b (a • m) = Coalgebra.counit (R := 𝒪) a • reduce b m := by
  ext k
  simp [reduce_apply, Finsupp.smul_apply, smul_eq_mul, Bialgebra.counit_mul]

theorem reduce_basis (b : Basis κ (MonoidAlgebra 𝒪 Δ) M) (k : κ) :
    reduce b (b k) = Finsupp.single k 1 := by
  classical
  ext k'
  rw [reduce_apply, Basis.repr_self, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> simp

noncomputable def unreduce (b : Basis κ (MonoidAlgebra 𝒪 Δ) M) : (κ →₀ 𝒪) →ₗ[𝒪] M :=
  Finsupp.linearCombination 𝒪 (fun k => b k)

theorem reduce_comp_unreduce (b : Basis κ (MonoidAlgebra 𝒪 Δ) M) :
    reduce b ∘ₗ unreduce b = LinearMap.id := by
  ext k
  simp [unreduce, reduce_basis]

theorem reduce_surjective (b : Basis κ (MonoidAlgebra 𝒪 Δ) M) :
    Function.Surjective (reduce b) := fun f =>
  ⟨unreduce b f, by
    have := congrArg (fun g => g f) (reduce_comp_unreduce b)
    simpa using this⟩

theorem reduce_eq_zero_of_mem (b : Basis κ (MonoidAlgebra 𝒪 Δ) M) {m : M}
    (hm : m ∈ augSmul 𝒪 Δ M) : reduce b m = 0 := by
  refine Submodule.smul_induction_on hm (fun a ha n _ => ?_) (fun x y hx hy => ?_)
  · rw [reduce_smul, (mem_aug_iff a).1 ha, zero_smul]
  · rw [map_add, hx, hy, add_zero]

theorem mem_of_reduce_eq_zero (b : Basis κ (MonoidAlgebra 𝒪 Δ) M) {m : M}
    (hm : reduce b m = 0) : m ∈ augSmul 𝒪 Δ M := by
  have hcoord : ∀ k, b.repr m k ∈ aug 𝒪 Δ := fun k => by
    rw [mem_aug_iff, ← reduce_apply, hm, Finsupp.zero_apply]
  rw [← b.linearCombination_repr m, Finsupp.linearCombination_apply, Finsupp.sum]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem_smul (hcoord k) Submodule.mem_top

theorem reduce_eq_zero_iff (b : Basis κ (MonoidAlgebra 𝒪 Δ) M) (m : M) :
    reduce b m = 0 ↔ m ∈ augSmul 𝒪 Δ M :=
  ⟨mem_of_reduce_eq_zero b, reduce_eq_zero_of_mem b⟩

theorem ker_reduce_eq (b : Basis κ (MonoidAlgebra 𝒪 Δ) M) :
    LinearMap.ker (reduce b) = (augSmul 𝒪 Δ M).restrictScalars 𝒪 := by
  ext m
  rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, reduce_eq_zero_iff]

noncomputable def coinvariantsRepr (b : Basis κ (MonoidAlgebra 𝒪 Δ) M) :
    (M ⧸ augSmul 𝒪 Δ M) ≃ₗ[𝒪] (κ →₀ 𝒪) :=
  (Submodule.Quotient.restrictScalarsEquiv 𝒪 (augSmul 𝒪 Δ M)).symm ≪≫ₗ
    (Submodule.quotEquivOfEq _ _ (ker_reduce_eq b).symm ≪≫ₗ
      (reduce b).quotKerEquivOfSurjective (reduce_surjective b))

theorem coinvariantsRepr_mk (b : Basis κ (MonoidAlgebra 𝒪 Δ) M) (m : M) :
    coinvariantsRepr b (Submodule.Quotient.mk m) = reduce b m := by
  simp only [coinvariantsRepr, LinearEquiv.trans_apply,
    Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

noncomputable def coinvariantsBasis (b : Basis κ (MonoidAlgebra 𝒪 Δ) M) :
    Basis κ 𝒪 (M ⧸ augSmul 𝒪 Δ M) :=
  Basis.ofRepr (coinvariantsRepr b)

theorem coinvariantsBasis_apply (b : Basis κ (MonoidAlgebra 𝒪 Δ) M) (k : κ) :
    coinvariantsBasis b k = Submodule.Quotient.mk (b k) := by
  rw [coinvariantsBasis, Basis.apply_eq_iff]
  change coinvariantsRepr b (Submodule.Quotient.mk (b k)) = Finsupp.single k 1
  rw [coinvariantsRepr_mk, reduce_basis]

theorem free_coinvariants [Module.Free (MonoidAlgebra 𝒪 Δ) M] :
    Module.Free 𝒪 (M ⧸ augSmul 𝒪 Δ M) :=
  Module.Free.of_basis (coinvariantsBasis (Module.Free.chooseBasis (MonoidAlgebra 𝒪 Δ) M))

theorem rank_coinvariants [Nontrivial 𝒪] [Module.Free (MonoidAlgebra 𝒪 Δ) M] :
    Module.rank 𝒪 (M ⧸ augSmul 𝒪 Δ M) = Module.rank (MonoidAlgebra 𝒪 Δ) M := by
  rw [← (coinvariantsBasis (Module.Free.chooseBasis (MonoidAlgebra 𝒪 Δ) M)).mk_eq_rank'',
    ← (Module.Free.chooseBasis (MonoidAlgebra 𝒪 Δ) M).mk_eq_rank'']

end Coinvariants

section Descent

variable {𝒪 : Type*} [CommRing 𝒪] {Δ : Type*} [CommMonoid Δ]
variable {R : Type*} [Ring R] [Algebra 𝒪 R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module (MonoidAlgebra 𝒪 Δ) M] [Module 𝒪 M]
  [IsScalarTower 𝒪 (MonoidAlgebra 𝒪 Δ) M]
variable {T₀ : Type*} [Ring T₀] [Algebra 𝒪 T₀]
variable {M₀ : Type*} [AddCommGroup M₀] [Module T₀ M₀] [Module 𝒪 M₀]

variable (π : M →ₗ[𝒪] M₀)

noncomputable def descend (h : (augSmul 𝒪 Δ M).restrictScalars 𝒪 ≤ LinearMap.ker π) :
    (M ⧸ augSmul 𝒪 Δ M) →ₗ[𝒪] M₀ :=
  ((augSmul 𝒪 Δ M).restrictScalars 𝒪).liftQ π h ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv 𝒪 (augSmul 𝒪 Δ M)).symm.toLinearMap

theorem descend_mk (h : (augSmul 𝒪 Δ M).restrictScalars 𝒪 ≤ LinearMap.ker π) (m : M) :
    descend π h (Submodule.Quotient.mk m) = π m := by
  simp only [descend, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.liftQ_apply]

theorem descend_surjective (h : (augSmul 𝒪 Δ M).restrictScalars 𝒪 ≤ LinearMap.ker π)
    (hπ : Function.Surjective π) : Function.Surjective (descend π h) := fun y => by
  obtain ⟨m, rfl⟩ := hπ y
  exact ⟨Submodule.Quotient.mk m, descend_mk π h m⟩

theorem descend_injective (h : (augSmul 𝒪 Δ M).restrictScalars 𝒪 ≤ LinearMap.ker π)
    (hker : ∀ m : M, π m = 0 → m ∈ augSmul 𝒪 Δ M) : Function.Injective (descend π h) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  induction q using Submodule.Quotient.induction_on with
  | H m =>
    rw [descend_mk] at hq
    exact (Submodule.Quotient.mk_eq_zero _).2 (hker m hq)

variable (ψ : R →ₐ[𝒪] T₀) (hπψ : ∀ (x : R) (m : M), π (x • m) = ψ x • π m)

include hπψ in

theorem exists_linearEquiv (hπ : Function.Surjective π)
    (hker : ∀ m : M, π m = 0 ↔ m ∈ augSmul 𝒪 Δ M) :
    ∃ e : (M ⧸ augSmul 𝒪 Δ M) ≃ₗ[𝒪] M₀,
      (∀ m : M, e (Submodule.Quotient.mk m) = π m) ∧
      ∀ (x : R) (m : M),
        e (Submodule.Quotient.mk (x • m)) = ψ x • e (Submodule.Quotient.mk m) := by
  have h : (augSmul 𝒪 Δ M).restrictScalars 𝒪 ≤ LinearMap.ker π := fun m hm =>
    (hker m).2 hm
  refine ⟨LinearEquiv.ofBijective (descend π h)
      ⟨descend_injective π h fun m => (hker m).1, descend_surjective π h hπ⟩,
    fun m => ?_, fun x m => ?_⟩
  · rw [LinearEquiv.ofBijective_apply, descend_mk]
  · rw [LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply, descend_mk, descend_mk,
      hπψ]

theorem eq_algebraMap_counit_of_forall_of (χ : MonoidAlgebra 𝒪 Δ →ₐ[𝒪] T₀)
    (hχ : ∀ g : Δ, χ (MonoidAlgebra.of 𝒪 Δ g) = 1) (a : MonoidAlgebra 𝒪 Δ) :
    χ a = algebraMap 𝒪 T₀ (Coalgebra.counit (R := 𝒪) a) := by
  have h : χ = (Algebra.ofId 𝒪 T₀).comp (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ)) := by
    refine MonoidAlgebra.algHom_ext (fun g => ?_) (Subsingleton.elim _ _)
    have := hχ g
    rw [MonoidAlgebra.of_apply] at this
    rw [this, AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, MonoidAlgebra.counit_single,
      CommSemiring.counit_apply, Algebra.ofId_apply, map_one]
  rw [h]
  rfl

variable (ι : MonoidAlgebra 𝒪 Δ →ₐ[𝒪] R)
  (hι : ∀ (c : MonoidAlgebra 𝒪 Δ) (m : M), c • m = ι c • m)
  (hψ : ∀ g : Δ, ψ (ι (MonoidAlgebra.of 𝒪 Δ g)) = 1)

include hι hψ hπψ in
omit [IsScalarTower 𝒪 (MonoidAlgebra 𝒪 Δ) M] in

theorem eq_zero_of_mem_augSmul {m : M} (hm : m ∈ augSmul 𝒪 Δ M) : π m = 0 := by
  refine Submodule.smul_induction_on hm (fun a ha n _ => ?_) (fun x y hx hy => ?_)
  · rw [hι, hπψ, ← AlgHom.comp_apply,
      eq_algebraMap_counit_of_forall_of (ψ.comp ι) (fun g => hψ g) a, (mem_aug_iff a).1 ha,
      map_zero, zero_smul]
  · rw [map_add, hx, hy, add_zero]

include hι hψ hπψ in
theorem augSmul_le_ker_of_forall_of : (augSmul 𝒪 Δ M).restrictScalars 𝒪 ≤ LinearMap.ker π :=
  fun _ hm => eq_zero_of_mem_augSmul π ψ hπψ ι hι hψ hm

theorem ker_le_augSmul_of_finrank_eq [Nontrivial 𝒪] [Module.Free (MonoidAlgebra 𝒪 Δ) M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M₀] [Module.Finite 𝒪 M₀]
    (h : (augSmul 𝒪 Δ M).restrictScalars 𝒪 ≤ LinearMap.ker π) (hπ : Function.Surjective π)
    (hrank : Module.finrank 𝒪 M₀ = Module.finrank (MonoidAlgebra 𝒪 Δ) M) :
    ∀ m : M, π m = 0 → m ∈ augSmul 𝒪 Δ M := by
  haveI : Module.Free 𝒪 (M ⧸ augSmul 𝒪 Δ M) := free_coinvariants
  haveI : Module.Finite 𝒪 (M ⧸ augSmul 𝒪 Δ M) := Module.Finite.quotient 𝒪 (augSmul 𝒪 Δ M)
  have hfr : Module.finrank 𝒪 (M ⧸ augSmul 𝒪 Δ M) = Module.finrank 𝒪 M₀ := by
    rw [hrank]
    exact congrArg Cardinal.toNat (rank_coinvariants (𝒪 := 𝒪) (Δ := Δ) (M := M))

  let f : M₀ ≃ₗ[𝒪] (M ⧸ augSmul 𝒪 Δ M) := LinearEquiv.ofFinrankEq M₀ _ hfr.symm
  have hinj : Function.Injective (descend π h) :=
    OrzechProperty.injective_of_surjective_of_injective f.symm.toLinearMap _ f.symm.injective
      (descend_surjective π h hπ)
  intro m hm
  have h0 : descend π h (Submodule.Quotient.mk m) = 0 := by rw [descend_mk, hm]
  exact (Submodule.Quotient.mk_eq_zero _).1 (hinj (by rw [h0, map_zero]))

include hι hψ hπψ in

theorem exists_linearEquiv_of_forall_of_of_finrank_eq [Nontrivial 𝒪]
    [Module.Free (MonoidAlgebra 𝒪 Δ) M] [Module.Finite 𝒪 M] [Module.Free 𝒪 M₀]
    [Module.Finite 𝒪 M₀] (hπ : Function.Surjective π)
    (hrank : Module.finrank 𝒪 M₀ = Module.finrank (MonoidAlgebra 𝒪 Δ) M) :
    (∀ m : M, π m = 0 ↔ m ∈ augSmul 𝒪 Δ M) ∧
    ∃ e : (M ⧸ augSmul 𝒪 Δ M) ≃ₗ[𝒪] M₀,
      (∀ m : M, e (Submodule.Quotient.mk m) = π m) ∧
      ∀ (x : R) (m : M),
        e (Submodule.Quotient.mk (x • m)) = ψ x • e (Submodule.Quotient.mk m) := by
  have hker : ∀ m : M, π m = 0 ↔ m ∈ augSmul 𝒪 Δ M := fun m =>
    ⟨ker_le_augSmul_of_finrank_eq π (augSmul_le_ker_of_forall_of π ψ hπψ ι hι hψ) hπ hrank m,
      eq_zero_of_mem_augSmul π ψ hπψ ι hι hψ⟩
  exact ⟨hker, exists_linearEquiv π ψ hπψ hπ hker⟩

end Descent

end TWCoinvariants

end

open TWCoinvariants in
theorem solution
    {𝒪 : Type*} [CommRing 𝒪] [Nontrivial 𝒪]
    {Δ : Type*} [CommMonoid Δ]
    {R : Type*} [Ring R] [Algebra 𝒪 R] (ι : MonoidAlgebra 𝒪 Δ →ₐ[𝒪] R)
    {M : Type*} [AddCommGroup M] [Module R M] [Module (MonoidAlgebra 𝒪 Δ) M] [Module 𝒪 M]
    [IsScalarTower 𝒪 (MonoidAlgebra 𝒪 Δ) M] [Module.Free (MonoidAlgebra 𝒪 Δ) M]
    (hι : ∀ (c : MonoidAlgebra 𝒪 Δ) (m : M), c • m = ι c • m)
    {T₀ : Type*} [Ring T₀] [Algebra 𝒪 T₀] (ψ : R →ₐ[𝒪] T₀)
    {M₀ : Type*} [AddCommGroup M₀] [Module T₀ M₀] [Module 𝒪 M₀]
    (π : M →ₗ[𝒪] M₀) (hπ : Function.Surjective π)
    (hπψ : ∀ (x : R) (m : M), π (x • m) = ψ x • π m)
    (hker : ∀ m : M, π m = 0 ↔
      m ∈ (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ)) •
        (⊤ : Submodule (MonoidAlgebra 𝒪 Δ) M))) :
    Module.Free 𝒪 (M ⧸ (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ)) •
        (⊤ : Submodule (MonoidAlgebra 𝒪 Δ) M))) ∧
    Module.rank 𝒪 (M ⧸ (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ)) •
        (⊤ : Submodule (MonoidAlgebra 𝒪 Δ) M))) = Module.rank (MonoidAlgebra 𝒪 Δ) M ∧
    ∃ e : (M ⧸ (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ)) •
        (⊤ : Submodule (MonoidAlgebra 𝒪 Δ) M))) ≃ₗ[𝒪] M₀,
      (∀ m : M, e (Submodule.Quotient.mk m) = π m) ∧
      ∀ (x : R) (m : M),
        e (Submodule.Quotient.mk (x • m)) = ψ x • e (Submodule.Quotient.mk m) :=

  have _ := hι
  ⟨free_coinvariants, rank_coinvariants, exists_linearEquiv π ψ hπψ hπ hker⟩

end S_MonoidAlgebra_free_coinvariants_and_exists_linearEquiv_of_free_of_ker_eq
end P2MW
export P2MW.S_MonoidAlgebra_free_coinvariants_and_exists_linearEquiv_of_free_of_ker_eq (solution)
