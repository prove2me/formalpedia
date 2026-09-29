-- Prove2me | solution 1 for ModularCurve.mem_of_coeffEmb_mem_laurentBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/4994f242-a0ee-5a6f-8e6c-929c3f901c7c

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Adjoin.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_of_coeffEmb_mem_laurentBaseChange

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange"
p2m_open "ModularCurve"
namespace CoeffDescent

open HahnSeries

variable {L : Type*} [Field L] [Algebra ℚ L]

noncomputable def lam (φ : L →ₗ[ℚ] ℚ) : LaurentSeries L →+ LaurentSeries ℚ where
  toFun y :=
    { coeff := fun k => φ (y.coeff k)
      isPWO_support' := y.isPWO_support.mono (by
        intro k hk
        simp only [Function.mem_support, ne_eq] at hk ⊢
        intro h
        exact hk (by rw [h, map_zero])) }
  map_zero' := by ext k; simp
  map_add' x y := by ext k; simp

@[scoped simp] theorem lam_coeff (φ : L →ₗ[ℚ] ℚ) (y : LaurentSeries L) (k : ℤ) :
    (lam φ y).coeff k = φ (y.coeff k) := rfl

theorem support_lam_subset (φ : L →ₗ[ℚ] ℚ) (y : LaurentSeries L) :
    (lam φ y).support ⊆ y.support := by
  intro k hk
  simp only [HahnSeries.mem_support, lam_coeff, ne_eq] at hk ⊢
  intro h; exact hk (by rw [h, map_zero])

theorem lam_smul (φ : L →ₗ[ℚ] ℚ) (c : L) (y : LaurentSeries L) :
    lam φ (c • y) = lam (φ ∘ₗ LinearMap.mulLeft ℚ c) y := by
  ext k; simp

theorem lam_single_zero_mul (φ : L →ₗ[ℚ] ℚ) (c : L) (y : LaurentSeries L) :
    lam φ (HahnSeries.single 0 c * y) = lam (φ ∘ₗ LinearMap.mulLeft ℚ c) y := by
  rw [HahnSeries.single_zero_mul_eq_smul, lam_smul]

theorem lam_algebraMap (φ : L →ₗ[ℚ] ℚ) (c : L) :
    lam φ (algebraMap L (LaurentSeries L) c) = algebraMap ℚ (LaurentSeries ℚ) (φ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single]
  ext k
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · simp [HahnSeries.coeff_single_of_ne hk]

theorem support_coeffEmb (x : LaurentSeries ℚ) : (coeffEmb L x).support = x.support := by
  ext k
  rw [HahnSeries.mem_support, HahnSeries.mem_support, coeffEmb_coeff, ne_eq, ne_eq,
    map_eq_zero_iff _ (algebraMap ℚ L).injective]

theorem lam_coeffEmb_mul (φ : L →ₗ[ℚ] ℚ) (x : LaurentSeries ℚ) (y : LaurentSeries L) :
    lam φ (coeffEmb L x * y) = x * lam φ y := by
  ext a
  rw [lam_coeff]
  rw [HahnSeries.coeff_mul_left' (x.isPWO_support) (by rw [support_coeffEmb])]
  rw [HahnSeries.coeff_mul_right' (y.isPWO_support) (support_lam_subset φ y)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [coeffEmb_coeff, lam_coeff, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

theorem lam_coeffEmb (φ : L →ₗ[ℚ] ℚ) (x : LaurentSeries ℚ) :
    lam φ (coeffEmb L x) = algebraMap ℚ (LaurentSeries ℚ) (φ 1) * x := by
  have h := lam_coeffEmb_mul φ x 1
  rw [mul_one] at h
  rw [h, ← map_one (algebraMap L (LaurentSeries L)), lam_algebraMap, mul_comm]

theorem exists_lam_ne_zero {y : LaurentSeries L} (hy : y ≠ 0) :
    ∃ φ : L →ₗ[ℚ] ℚ, lam φ y ≠ 0 := by
  obtain ⟨k, hk⟩ : ∃ k, y.coeff k ≠ 0 := by
    by_contra h; push Not at h; exact hy (HahnSeries.ext (funext h))
  obtain ⟨φ, hφ⟩ : ∃ φ : L →ₗ[ℚ] ℚ, φ (y.coeff k) ≠ 0 := by
    by_contra h; push Not at h
    exact hk ((Module.forall_dual_apply_eq_zero_iff ℚ (y.coeff k)).mp h)
  exact ⟨φ, fun h => hφ (by simpa using congrArg (fun z => HahnSeries.coeff z k) h)⟩

theorem exists_dual_map_one_eq_one : ∃ φ : L →ₗ[ℚ] ℚ, φ 1 = 1 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : L →ₗ[ℚ] ℚ, φ (1 : L) ≠ 0 := by
    by_contra h; push Not at h
    exact one_ne_zero ((Module.forall_dual_apply_eq_zero_iff ℚ (1 : L)).mp h)
  exact ⟨(φ 1)⁻¹ • φ, by simp [inv_mul_cancel₀ hφ]⟩

theorem lam_mem_of_mem_adjoin {S : Set (LaurentSeries ℚ)} (A : Subalgebra ℚ (LaurentSeries ℚ))
    (hS : ∀ y ∈ Submonoid.closure (⇑(coeffEmb L) '' S), ∃ f ∈ A, coeffEmb L f = y)
    {r : LaurentSeries L} (hr : r ∈ Algebra.adjoin L (⇑(coeffEmb L) '' S)) (φ : L →ₗ[ℚ] ℚ) :
    lam φ r ∈ A := by
  have hr' : r ∈ Subalgebra.toSubmodule (Algebra.adjoin L (⇑(coeffEmb L) '' S)) := hr
  rw [Algebra.adjoin_eq_span] at hr'
  clear hr
  induction hr' using Submodule.span_induction generalizing φ with
  | mem y hy =>
      obtain ⟨f, hf, rfl⟩ := hS y hy
      rw [lam_coeffEmb]
      exact A.mul_mem (A.algebraMap_mem _) hf
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact A.add_mem (hy φ) (hz φ)
  | smul c y _ hy =>
      rw [Algebra.smul_def, algebraMap_laurentSeries_eq_single, lam_single_zero_mul]
      exact hy _

end CoeffDescent
p2m_reactivate "P2MW.S_ModularCurve_mem_of_coeffEmb_mem_laurentBaseChange.ModularCurve.CoeffDescent"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_mem_of_coeffEmb_mem_laurentBaseChange.ModularCurve.CoeffDescent P2MW.S_ModularCurve_mem_of_coeffEmb_mem_laurentBaseChange.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange"
p2m_open "ModularCurve"
open CoeffDescent

theorem mem_of_coeffEmb_mem_laurentBaseChange' (L : Type*) [Field L] [Algebra ℚ L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (x : LaurentSeries ℚ)
    (hx : ModularCurve.coeffEmb L x ∈ ModularCurve.laurentBaseChange L F₀) : x ∈ F₀ := by

  have hS : ∀ y ∈ Submonoid.closure (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ))),
      ∃ f ∈ F₀.toSubalgebra, coeffEmb L f = y := by
    intro y hy
    induction hy using Submonoid.closure_induction with
    | mem y hy => obtain ⟨f, hf, rfl⟩ := hy; exact ⟨f, hf, rfl⟩
    | one => exact ⟨1, F₀.one_mem, map_one _⟩
    | mul y z _ _ hy hz =>
        obtain ⟨f, hf, rfl⟩ := hy
        obtain ⟨g, hg, rfl⟩ := hz
        exact ⟨f * g, F₀.mul_mem hf hg, map_mul _ _ _⟩

  rw [laurentBaseChange, IntermediateField.mem_adjoin_iff_div] at hx
  obtain ⟨r, hr, s, hs, hrs⟩ := hx
  have hrM : ∀ φ : L →ₗ[ℚ] ℚ, lam φ r ∈ F₀.toSubalgebra := fun φ =>
    lam_mem_of_mem_adjoin F₀.toSubalgebra hS hr φ
  have hsM : ∀ φ : L →ₗ[ℚ] ℚ, lam φ s ∈ F₀.toSubalgebra := fun φ =>
    lam_mem_of_mem_adjoin F₀.toSubalgebra hS hs φ
  by_cases hs0 : s = 0
  ·
    rw [hs0, div_zero, map_eq_zero_iff _ (coeffEmb L).injective] at hrs
    rw [hrs]; exact F₀.zero_mem
  · obtain ⟨φ, hφ⟩ := exists_lam_ne_zero hs0
    have hmul : coeffEmb L x * s = r := by
      rw [hrs, div_mul_cancel₀ _ hs0]
    have key : x * lam φ s = lam φ r := by
      rw [← lam_coeffEmb_mul, hmul]
    have hx' : x = lam φ r / lam φ s := by
      rw [← key, mul_div_cancel_right₀ _ hφ]
    rw [hx']
    exact F₀.div_mem (hrM φ) (hsM φ)

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_mem_of_coeffEmb_mem_laurentBaseChange.ModularCurve.CoeffDescent P2MW.S_ModularCurve_mem_of_coeffEmb_mem_laurentBaseChange.ModularCurve"

theorem solution (L : Type*) [Field L] [Algebra ℚ L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (x : LaurentSeries ℚ)
    (hx : ModularCurve.coeffEmb L x ∈ ModularCurve.laurentBaseChange L F₀) : x ∈ F₀ :=
  ModularCurve.mem_of_coeffEmb_mem_laurentBaseChange' L F₀ x hx

end
p2m_reactivate "P2MW.S_ModularCurve_mem_of_coeffEmb_mem_laurentBaseChange.ModularCurve.CoeffDescent P2MW.S_ModularCurve_mem_of_coeffEmb_mem_laurentBaseChange.ModularCurve"

end S_ModularCurve_mem_of_coeffEmb_mem_laurentBaseChange
end P2MW
export P2MW.S_ModularCurve_mem_of_coeffEmb_mem_laurentBaseChange (solution)
