-- Prove2me | solution 1 for Matrix.SpecialLinearGroup.exists_generators_free_mod_neg_one_of_forall_trace_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/9ce5f5c0-0c4d-5814-b662-464da7d3f2e5

import Mathlib
import Theorems.Thm_Matrix_SpecialLinearGroup_nonempty_freeGroupBasis_map_quotient_center_of_forall_trace_ne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_SpecialLinearGroup_exists_generators_free_mod_neg_one_of_forall_trace_ne

set_option autoImplicit false

open Matrix MatrixGroups Subgroup

namespace ModularCurve
namespace FreeModNegOne

section Basis

variable {ι K L : Type*} [Group K] [Group L]

theorem lift_apply_basis (b : FreeGroupBasis ι K) (f : ι → L) (i : ι) :
    b.lift f (b i) = f i := by
  show FreeGroup.lift f (b.repr (b i)) = f i
  rw [FreeGroupBasis.repr_apply_coe, FreeGroup.lift_apply_of]

theorem closure_range_basis (b : FreeGroupBasis ι K) :
    Subgroup.closure (Set.range (b : ι → K)) = ⊤ := by
  have hrange : Set.range (b : ι → K) =
      ⇑b.repr.symm.toMonoidHom '' Set.range (FreeGroup.of : ι → FreeGroup ι) := by
    rw [MulEquiv.coe_toMonoidHom, ← Set.range_comp]
    rfl
  rw [hrange, ← MonoidHom.map_closure, FreeGroup.closure_range_of, ← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.mpr b.repr.symm.surjective

end Basis

variable (Γ : Subgroup SL(2, ℤ))

theorem mem_center_iff_eq (A : SL(2, ℤ)) : A ∈ Subgroup.center SL(2, ℤ) ↔ A = 1 ∨ A = -1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hA⟩
    have hr' : r * r = 1 := by rw [← pow_two]; simpa using hr
    rcases mul_self_eq_one_iff.mp hr' with rfl | rfl
    · left
      apply Subtype.ext
      rw [← hA, map_one]
      rfl
    · right
      apply Subtype.ext
      rw [← hA, map_neg, map_one]
      rfl
  · rintro (rfl | rfl)
    · exact ⟨1, by simp, by simp⟩
    · exact ⟨-1, by simp, by simp⟩

abbrev toBar : Γ →* Γ.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) :=
  (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))).subgroupMap Γ

theorem eq_one_or_eq_neg_of_toBar_eq_one (hneg : (-1 : SL(2, ℤ)) ∈ Γ) {x : Γ}
    (h : toBar Γ x = 1) : x = 1 ∨ x = ⟨-1, hneg⟩ := by
  have h' : (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) (x : SL(2, ℤ)) = 1 := by
    have := congrArg Subtype.val h
    simpa using this
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', mem_center_iff_eq] at h'
  rcases h' with h1 | h1
  · left; exact Subtype.ext h1
  · right; exact Subtype.ext h1

theorem exists_gens [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (hΓ : ∀ γ ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 1 ∧ (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ -1) :
    ∃ gens : Fin (1 + Γ.index / 6) → Γ,
      Subgroup.closure (Set.range gens ∪ {⟨-1, hneg⟩}) = ⊤ ∧
      ∀ (L : Type) [Group L] (v : Fin (1 + Γ.index / 6) → L),
        ∃ f : Γ →* L, ∀ i, f (gens i) = v i := by
  classical
  obtain ⟨b⟩ :=
    Matrix.SpecialLinearGroup.nonempty_freeGroupBasis_map_quotient_center_of_forall_trace_ne Γ hneg hΓ
  have hsurj := (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))).subgroupMap_surjective Γ
  choose gens hgens using fun i => hsurj (b i)
  refine ⟨gens, ?_, ?_⟩
  · set C : Subgroup Γ := Subgroup.closure (Set.range gens ∪ {⟨-1, hneg⟩}) with hC
    have hnegC : (⟨-1, hneg⟩ : Γ) ∈ C := Subgroup.subset_closure (Set.mem_union_right _ rfl)
    have hgensC : ∀ i, gens i ∈ C := fun i =>
      Subgroup.subset_closure (Set.mem_union_left _ (Set.mem_range_self i))
    have hker : (toBar Γ).ker ≤ C := by
      intro x hx
      rcases eq_one_or_eq_neg_of_toBar_eq_one Γ hneg (MonoidHom.mem_ker.mp hx) with rfl | rfl
      · exact one_mem C
      · exact hnegC
    have himage : Subgroup.map (toBar Γ) C = ⊤ := by
      rw [eq_top_iff, ← closure_range_basis b, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨gens i, hgensC i, hgens i⟩
    have hsup : C ⊔ (toBar Γ).ker = ⊤ := by
      rw [← Subgroup.comap_map_eq, himage, Subgroup.comap_top]
    exact (sup_of_le_left hker).symm.trans hsup
  · intro L _ v
    refine ⟨(b.lift v).comp (toBar Γ), fun i => ?_⟩
    rw [MonoidHom.comp_apply, hgens i]
    exact lift_apply_basis b v i

theorem finrank_addMonoidHom [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (hΓ : ∀ γ ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 1 ∧ (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ -1)
    (K : Type) [Field K] [CharZero K] :
    Module.finrank K (Additive Γ →+ K) = 1 + Γ.index / 6 := by
  obtain ⟨gens, hcl, hext⟩ := exists_gens Γ hneg hΓ

  let ev : (Additive Γ →+ K) →ₗ[K] (Fin (1 + Γ.index / 6) → K) :=
    { toFun := fun φ i => φ (Additive.ofMul (gens i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hneg0 : ∀ φ : Additive Γ →+ K, φ (Additive.ofMul (⟨-1, hneg⟩ : Γ)) = 0 := by
    intro φ
    have h2 : (⟨-1, hneg⟩ : Γ) * ⟨-1, hneg⟩ = 1 := by
      apply Subtype.ext
      show (-1 : SL(2, ℤ)) * -1 = 1
      rw [neg_mul_neg, one_mul]
    have : φ (Additive.ofMul (⟨-1, hneg⟩ : Γ)) + φ (Additive.ofMul (⟨-1, hneg⟩ : Γ)) = 0 := by
      rw [← map_add, ← ofMul_mul, h2, ofMul_one, map_zero]
    have h3 : (2 : K) * φ (Additive.ofMul (⟨-1, hneg⟩ : Γ)) = 0 := by rw [two_mul]; exact this
    exact (mul_eq_zero.mp h3).resolve_left two_ne_zero
  have hinj : Function.Injective ev := by
    intro φ ψ h
    have key : ∀ γ : Γ, φ (Additive.ofMul γ) = ψ (Additive.ofMul γ) := by
      intro γ
      have hγ : γ ∈ Subgroup.closure (Set.range gens ∪ {⟨-1, hneg⟩}) := by
        rw [hcl]; exact Subgroup.mem_top γ
      induction hγ using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with ⟨i, rfl⟩ | hx
        · exact congrFun h i
        · rw [Set.mem_singleton_iff] at hx
          subst hx
          rw [hneg0, hneg0]
      | one => rw [ofMul_one, map_zero, map_zero]
      | mul x y _ _ hx hy => rw [ofMul_mul, map_add, map_add, hx, hy]
      | inv x _ hx => rw [ofMul_inv, map_neg, map_neg, hx]
    exact AddMonoidHom.ext fun a => key (Additive.toMul a)
  have hsurj : Function.Surjective ev := by
    intro v
    obtain ⟨f, hf⟩ := hext (Multiplicative K) (fun i => Multiplicative.ofAdd (v i))
    refine ⟨(MonoidHom.toAdditive f), funext fun i => ?_⟩
    show Multiplicative.toAdd (f (gens i)) = v i
    rw [hf i]
    rfl
  rw [(LinearEquiv.ofBijective ev ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_fin_fun]

end ModularCurve.FreeModNegOne

theorem solution (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ)
    (hΓ : ∀ γ ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 1 ∧ (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ -1) :
    ∃ gens : Fin (1 + Γ.index / 6) → Γ,
      Subgroup.closure (Set.range gens ∪ {⟨-1, hneg⟩}) = ⊤ ∧
      ∀ (L : Type) [Group L] (v : Fin (1 + Γ.index / 6) → L),
        ∃ f : Γ →* L, ∀ i, f (gens i) = v i :=
  ModularCurve.FreeModNegOne.exists_gens Γ hneg hΓ

end S_Matrix_SpecialLinearGroup_exists_generators_free_mod_neg_one_of_forall_trace_ne
end P2MW
export P2MW.S_Matrix_SpecialLinearGroup_exists_generators_free_mod_neg_one_of_forall_trace_ne (solution)
