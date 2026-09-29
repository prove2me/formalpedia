-- Prove2me | solution 1 for NumberField.exists_algHom_cyclotomicField_of_sup
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:49:27.885583+00:00
-- url     : https://prove2.me/submissions/6abba18a-11c0-473a-a49c-92a0c9fe049c

import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.Algebra.Algebra.Hom.Rat
import Theorems.Thm_NumberField_nonempty_algHom_cyclotomicField_of_dvd

open Polynomial

theorem solution {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (E₁ E₂ : IntermediateField ℚ Ω)
    (h₁ : ∃ n : ℕ, 0 < n ∧ Nonempty (E₁ →ₐ[ℚ] CyclotomicField n ℚ))
    (h₂ : ∃ n : ℕ, 0 < n ∧ Nonempty (E₂ →ₐ[ℚ] CyclotomicField n ℚ)) :
    ∃ n : ℕ, 0 < n ∧ Nonempty (↥(E₁ ⊔ E₂) →ₐ[ℚ] CyclotomicField n ℚ) := by
  obtain ⟨a, ha, ⟨f₁⟩⟩ := h₁
  obtain ⟨b, hb, ⟨f₂⟩⟩ := h₂
  have hab : 0 < a * b := Nat.mul_pos ha hb
  obtain ⟨g₁⟩ := NumberField.nonempty_algHom_cyclotomicField_of_dvd ha hab (dvd_mul_right a b)
  obtain ⟨g₂⟩ := NumberField.nonempty_algHom_cyclotomicField_of_dvd hb hab (dvd_mul_left b a)
  have : NeZero (((a * b : ℕ)) : ℚ) := ⟨by exact_mod_cast hab.ne'⟩
  have : NeZero (a * b) := ⟨hab.ne'⟩
  have : IsCyclotomicExtension {a * b} ℚ (CyclotomicField (a * b) ℚ) := by
    convert CyclotomicField.isCyclotomicExtension (a * b) ℚ <;> rfl
  have : IsGalois ℚ (CyclotomicField (a * b) ℚ) :=
    IsCyclotomicExtension.isGalois {a * b} ℚ _
  have : FiniteDimensional ℚ (CyclotomicField (a * b) ℚ) :=
    IsCyclotomicExtension.finiteDimensional {a * b} ℚ _
  let N := CyclotomicField (a * b) ℚ
  let A := AlgebraicClosure Ω
  let τ : N →ₐ[ℚ] A := IsAlgClosed.lift
  let ι : Ω →ₐ[ℚ] A := IsScalarTower.toAlgHom ℚ Ω A
  -- every root in `A` of the minimal polynomial of an element of `N` lies in `τ(N)`
  have hroot : ∀ (w : N) (y : A), Polynomial.aeval y (minpoly ℚ w) = 0 → ∃ v : N, τ v = y := by
    intro w y hy
    have hint : IsIntegral ℚ w := Algebra.IsIntegral.isIntegral w
    have hs := Normal.splits (inferInstance : Normal ℚ N) w
    have hmem := hs.mem_range_of_isRoot
      (Polynomial.map_ne_zero (minpoly.ne_zero hint)) (i := (τ : N →+* A)) (x := y) (by
        rw [Polynomial.map_map, AlgHom.comp_algebraMap, Polynomial.IsRoot,
          Polynomial.eval_map_algebraMap]
        exact hy)
    obtain ⟨v, hv⟩ := hmem
    exact ⟨v, hv⟩
  have key : ∀ (E : IntermediateField ℚ Ω) (f : E →ₐ[ℚ] N), ∀ x ∈ E, ∃ v : N, τ v = ι x := by
    intro E f x hx
    let u : E := ⟨x, hx⟩
    let φ₁ : E →ₐ[ℚ] N := (f : E →+* N).toRatAlgHom
    let φ₂ : E →ₐ[ℚ] A := ((ι : Ω →+* A).comp (E.val : E →+* Ω)).toRatAlgHom
    have h0 : Polynomial.aeval (f u) (minpoly ℚ (f u)) = 0 := minpoly.aeval ℚ (f u)
    have h1 : Polynomial.aeval u (minpoly ℚ (f u)) = 0 := by
      have := Polynomial.aeval_algHom_apply φ₁ u (minpoly ℚ (f u))
      rw [show φ₁ u = f u from rfl, h0] at this
      exact (map_eq_zero φ₁).mp this.symm
    have h2 : Polynomial.aeval (φ₂ u) (minpoly ℚ (f u)) = 0 := by
      rw [Polynomial.aeval_algHom_apply, h1, map_zero]
    exact hroot (f u) (ι x) h2
  have hsup : ∀ x ∈ E₁ ⊔ E₂, ∃ v : N, τ v = ι x := by
    let S : IntermediateField ℚ Ω :=
      { carrier := {x | ∃ v : N, τ v = ι x}
        mul_mem' := by
          rintro x y ⟨v, hv⟩ ⟨w, hw⟩; exact ⟨v * w, by rw [map_mul, map_mul, hv, hw]⟩
        add_mem' := by
          rintro x y ⟨v, hv⟩ ⟨w, hw⟩; exact ⟨v + w, by rw [map_add, map_add, hv, hw]⟩
        algebraMap_mem' := fun r => ⟨algebraMap ℚ N r, by rw [AlgHom.commutes, AlgHom.commutes]⟩
        inv_mem' := by
          rintro x ⟨v, hv⟩; exact ⟨v⁻¹, by rw [map_inv₀, map_inv₀, hv]⟩ }
    have h : E₁ ⊔ E₂ ≤ S := sup_le (fun x hx => key E₁ (g₁.comp f₁) x hx)
      (fun x hx => key E₂ (g₂.comp f₂) x hx)
    exact fun x hx => h hx
  choose g hg using fun x : ↥(E₁ ⊔ E₂) => hsup x.1 x.2
  let G : ↥(E₁ ⊔ E₂) →+* N :=
    { toFun := g
      map_one' := τ.injective (by show τ (g 1) = τ 1; rw [hg, map_one]; exact map_one ι)
      map_mul' := fun x y => τ.injective (by show τ (g (x * y)) = τ (g x * g y); rw [map_mul, hg, hg, hg]; exact map_mul ι x.1 y.1)
      map_zero' := τ.injective (by show τ (g 0) = τ 0; rw [hg, map_zero]; exact map_zero ι)
      map_add' := fun x y => τ.injective (by show τ (g (x + y)) = τ (g x + g y); rw [map_add, hg, hg, hg]; exact map_add ι x.1 y.1) }
  exact ⟨a * b, hab, ⟨G.toRatAlgHom⟩⟩

