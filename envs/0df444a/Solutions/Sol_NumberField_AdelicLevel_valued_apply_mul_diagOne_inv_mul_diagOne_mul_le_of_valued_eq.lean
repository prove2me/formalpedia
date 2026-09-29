-- Prove2me | solution 1 for NumberField.AdelicLevel.valued_apply_mul_diagOne_inv_mul_diagOne_mul_le_of_valued_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/cf21174c-f859-5637-b6e6-cd7c33920f00

import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicLevel_valued_apply_mul_diagOne_inv_mul_diagOne_mul_le_of_valued_eq

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

theorem solution
    (K : Type) [Field K] [NumberField K] (h κ : AdelicGL2 (𝓞 K) K) (hh : glFin (𝓞 K) K h = 1)
    (hκ : glFin (𝓞 K) K κ ∈ finiteIntegralGL2 (𝓞 K) K)
    (t₀ t₁ : (AdeleRing (𝓞 K) K)ˣ) (a₀ a₁ : HeightOneSpectrum (𝓞 K) → ℤ)
    (ht₀ : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) =
      ((Multiplicative.ofAdd (a₀ v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (ht₁ : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((t₁ : AdeleRing (𝓞 K) K)).2 v) =
      ((Multiplicative.ofAdd (a₁ v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (v : HeightOneSpectrum (𝓞 K)) (i j : Fin 2) :
    Valued.v (((((h * ((diagOne t₀)⁻¹ * (diagOne t₁ * κ)) : AdelicGL2 (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
      ((Multiplicative.ofAdd (((a₀ v).natAbs + (a₁ v).natAbs : ℕ) : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ∧
    Valued.v ((((((h * ((diagOne t₀)⁻¹ * (diagOne t₁ * κ)))⁻¹ : AdelicGL2 (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
      ((Multiplicative.ofAdd (((a₀ v).natAbs + (a₁ v).natAbs : ℕ) : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by

  set F : AdelicGL2 (𝓞 K) K →* GL (Fin 2) (v.adicCompletion K) :=
    (finComponent (𝓞 K) K v).comp (glFin (𝓞 K) K) with hFdef
  have hF : ∀ (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2),
      ((F g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
        (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v := fun _ _ _ => rfl
  set B : WithZero (Multiplicative ℤ) :=
    ((Multiplicative.ofAdd (((a₀ v).natAbs + (a₁ v).natAbs : ℕ) : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) with hB
  have hFh : F h = 1 := by
    show finComponent (𝓞 K) K v (glFin (𝓞 K) K h) = 1
    rw [hh, map_one]
  obtain ⟨hκi, hκi'⟩ := (mem_finiteIntegralGL2_iff).mp hκ
  have hκ1 : ∀ i j, Valued.v (((F κ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ 1 :=
    fun i j => by rw [hF]; exact valued_apply_le_one (hκi i j) v
  have hκ1' : ∀ i j, Valued.v ((((F κ)⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ 1 :=
    fun i j => by rw [← map_inv, hF]; exact valued_apply_le_one (hκi' i j) v

  set dv : (v.adicCompletion K) := (((t₀⁻¹ * t₁ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v with hdv
  set dv' : (v.adicCompletion K) := (((t₁⁻¹ * t₀ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v with hdv'
  have hval_inv : ∀ (t : (AdeleRing (𝓞 K) K)ˣ) (z : ℤ), Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) =
      ((Multiplicative.ofAdd z : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
      Valued.v ((((t⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
        ((Multiplicative.ofAdd (-z) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro t z ht
    have hmul : Valued.v ((((t⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) * Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) = 1 := by
      rw [← map_mul]
      have : ((((t⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) * (((t : AdeleRing (𝓞 K) K)).2 v) = 1 :=
        congrArg (fun x : AdeleRing (𝓞 K) K => x.2 v) (Units.inv_mul t)
      rw [this, map_one]
    rw [ht] at hmul
    have hne : ((Multiplicative.ofAdd z : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≠ 0 := WithZero.coe_ne_zero
    calc Valued.v ((((t⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v)
        = Valued.v ((((t⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) *
            ((Multiplicative.ofAdd z : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) *
            (((Multiplicative.ofAdd z : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))⁻¹ := by
              rw [mul_inv_cancel_right₀ hne]
      _ = ((Multiplicative.ofAdd (-z) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
              rw [hmul, one_mul, ← WithZero.coe_inv, ofAdd_neg]
  have hle_abs : ∀ z : ℤ, ((Multiplicative.ofAdd z : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤
      ((Multiplicative.ofAdd (z.natAbs : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := fun z =>
    WithZero.coe_le_coe.mpr (Multiplicative.ofAdd_le.mpr (Int.le_natAbs))
  have hdvB : Valued.v dv ≤ B := by
    rw [hdv, Units.val_mul, show ∀ a b : AdeleRing (𝓞 K) K, (a * b).2 v = a.2 v * b.2 v from fun _ _ => rfl, map_mul,
      hval_inv t₀ (a₀ v) (ht₀ v), ht₁ v, ← WithZero.coe_mul, ← ofAdd_add, hB]
    refine WithZero.coe_le_coe.mpr (Multiplicative.ofAdd_le.mpr ?_)
    omega
  have hdv'B : Valued.v dv' ≤ B := by
    rw [hdv', Units.val_mul, show ∀ a b : AdeleRing (𝓞 K) K, (a * b).2 v = a.2 v * b.2 v from fun _ _ => rfl, map_mul,
      hval_inv t₁ (a₁ v) (ht₁ v), ht₀ v, ← WithZero.coe_mul, ← ofAdd_add, hB]
    refine WithZero.coe_le_coe.mpr (Multiplicative.ofAdd_le.mpr ?_)
    omega
  have hB1 : 1 ≤ B := by
    rw [hB, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]; positivity

  have hdiag : ∀ (t : (AdeleRing (𝓞 K) K)ˣ) (i j : Fin 2),
      ((F (diagOne t) : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
        if i = j then (if i = 0 then ((t : AdeleRing (𝓞 K) K)).2 v else 1) else 0 := by
    intro t i j
    rw [hF, diagOne_coe_apply]
    fin_cases i <;> fin_cases j <;> simp <;> rfl
  have hd_eq : F ((diagOne t₀)⁻¹ * diagOne t₁) = F (diagOne (t₀⁻¹ * t₁)) := by
    symm; congr 1; rw [map_mul, map_inv]
  have hd'_eq : F ((diagOne t₁)⁻¹ * diagOne t₀) = F (diagOne (t₁⁻¹ * t₀)) := by
    symm; congr 1; rw [map_mul, map_inv]
  have hdB : ∀ i j, Valued.v (((F ((diagOne t₀)⁻¹ * diagOne t₁) : GL (Fin 2) (v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ B := by
    intro i j
    rw [hd_eq, hdiag]
    split_ifs
    · exact hdvB
    · rw [map_one]; exact hB1
    · rw [map_zero]; exact zero_le'
  have hd'B : ∀ i j, Valued.v (((F ((diagOne t₁)⁻¹ * diagOne t₀) : GL (Fin 2) (v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ B := by
    intro i j
    rw [hd'_eq, hdiag]
    split_ifs
    · exact hdv'B
    · rw [map_one]; exact hB1
    · rw [map_zero]; exact zero_le'

  have hprod : ∀ (P Q : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) (x y : WithZero (Multiplicative ℤ)),
      (∀ i j, Valued.v (P i j) ≤ x) → (∀ i j, Valued.v (Q i j) ≤ y) → ∀ i j, Valued.v ((P * Q) i j) ≤ x * y := by
    intro P Q x y hP hQ i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_) <;> rw [map_mul]
    · exact mul_le_mul' (hP i 0) (hQ 0 j)
    · exact mul_le_mul' (hP i 1) (hQ 1 j)
  constructor
  · have he : F (h * ((diagOne t₀)⁻¹ * (diagOne t₁ * κ))) = F ((diagOne t₀)⁻¹ * diagOne t₁) * F κ := by
      rw [map_mul, hFh, one_mul, ← mul_assoc, map_mul]
    rw [← hF, he, Units.val_mul]
    have := hprod _ _ B 1 hdB hκ1 i j
    rwa [mul_one] at this
  · have he : F ((h * ((diagOne t₀)⁻¹ * (diagOne t₁ * κ)))⁻¹) = (F κ)⁻¹ * F ((diagOne t₁)⁻¹ * diagOne t₀) := by
      rw [map_inv, map_mul, hFh, one_mul, ← mul_assoc, map_mul, mul_inv_rev, map_mul, map_inv, map_mul, map_inv,
        mul_inv_rev, inv_inv]
    rw [← hF, he, Units.val_mul]
    have := hprod _ _ 1 B hκ1' hd'B i j
    rwa [one_mul] at this

end S_NumberField_AdelicLevel_valued_apply_mul_diagOne_inv_mul_diagOne_mul_le_of_valued_eq
end P2MW
export P2MW.S_NumberField_AdelicLevel_valued_apply_mul_diagOne_inv_mul_diagOne_mul_le_of_valued_eq (solution)
