-- Prove2me | solution 1 for KServerConj.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T02:23:04.762396+00:00
-- url     : https://prove2.me/submissions/aa56a689-0907-4098-8eff-e68e216735eb

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.Localization.FractionRing
import Definitions.Def_KServerConj_K
set_option autoImplicit false

section PaperFile001
namespace KServerConj

variable {k : ℕ} {M : Type*}

@[simp] theorem nu_zero : nu (0 : K k M) = ⊤ := by
  exact AddValuation.map_zero _

@[simp] theorem nu_one : nu (1 : K k M) = 0 := by
  exact AddValuation.map_one _

@[simp] theorem nu_eq_top_iff (f : K k M) : nu f = ⊤ ↔ f = 0 := by
  exact HahnSeries.orderTop_eq_top

theorem nu_mul (f g : K k M) : nu (f * g) = nu f + nu g := by
  exact AddValuation.map_mul _ f g

theorem nu_add (f g : K k M) : min (nu f) (nu g) ≤ nu (f + g) := by
  exact AddValuation.map_add _ f g

@[simp] theorem nu_zp (a : ℝ) : nu (zp a : K k M) = (a : WithTop ℝ) := by
  exact HahnSeries.orderTop_single one_ne_zero

theorem varF_ne_zero (v : Var k M) : varF v ≠ 0 := by
  exact (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Var k M) ℚ) (F k M))).mpr
    (MvPolynomial.X_ne_zero v)

@[simp] theorem nu_coef (v : Var k M) : nu (coef v) = 0 := by
  simpa only [nu, HahnSeries.addVal_apply, coef, HahnSeries.C_apply, WithTop.coe_zero] using
    (HahnSeries.orderTop_single (a := (0 : ℝ)) (varF_ne_zero v))

theorem nu_C {c : F k M} (hc : c ≠ 0) : nu (HahnSeries.C c : K k M) = 0 := by
  simpa only [nu, HahnSeries.addVal_apply, HahnSeries.C_apply, WithTop.coe_zero] using
    (HahnSeries.orderTop_single (a := (0 : ℝ)) hc)

theorem coef_ne_zero (v : Var k M) : coef v ≠ 0 := by
  exact HahnSeries.single_ne_zero (varF_ne_zero v)

theorem zp_ne_zero (a : ℝ) : (zp a : K k M) ≠ 0 := by
  exact HahnSeries.single_ne_zero one_ne_zero

@[simp] theorem zp_zero : (zp 0 : K k M) = 1 := by
  exact HahnSeries.single_zero_one

theorem zp_add (a b : ℝ) : (zp (a + b) : K k M) = zp a * zp b := by
  simpa only [one_mul] using
    (HahnSeries.single_mul_single (a := a) (b := b) (r := (1 : F k M)) (s := 1)).symm

@[simp] theorem nu_neg (f : K k M) : nu (-f) = nu f := by
  exact AddValuation.map_neg _ _

@[simp] theorem nu_inv (f : K k M) : nu f⁻¹ = -(nu f) := by
  exact AddValuation.map_inv _

theorem nu_sum_ge {ι : Type*} [Fintype ι] (f : ι → K k M) (b : WithTop ℝ)
    (hf : ∀ i, b ≤ nu (f i)) : b ≤ nu (∑ i, f i) := by
  exact AddValuation.map_le_sum _ (fun i _ => hf i)

theorem nu_fresh_term (v : Var k M) (a : ℝ) (f : K k M) :
    nu (coef v * zp a * f) = (a : WithTop ℝ) + nu f := by
  simp only [nu_mul, nu_coef, nu_zp, zero_add]

theorem zp_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (zp (∑ i ∈ s, a i) : K k M) = ∏ i ∈ s, zp (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty, zp_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, zp_add, ih]

end KServerConj
end PaperFile001

section PaperFile002
open scoped BigOperators

namespace KServerConj

variable {k : ℕ} {M : Type*}

theorem varF_algebraicIndependent : AlgebraicIndependent ℚ (@varF k M) := by
  exact (MvPolynomial.algebraicIndependent_X (Var k M) ℚ).map'
    (f := IsScalarTower.toAlgHom ℚ (MvPolynomial (Var k M) ℚ) (F k M))
    (IsFractionRing.injective (MvPolynomial (Var k M) ℚ) (F k M))

theorem varF_algebraicIndependent_over_complement (S : Set (Var k M)) :
    AlgebraicIndependent (IntermediateField.adjoin ℚ ((@varF k M) '' Sᶜ))
      (fun i : S => varF (i : Var k M)) := by
  exact IntermediateField.algebraicIndependent_adjoin_iff.mpr
    ((AlgebraicIndependent.iff_adjoin_image_compl S).mp varF_algebraicIndependent).2

theorem fresh_vars_linearIndependent {N : ℕ} (v : Fin N → Var k M)
    (hv : Function.Injective v) :
    LinearIndependent
      (IntermediateField.adjoin ℚ ((@varF k M) '' (Set.range v)ᶜ))
      (fun i => varF (v i)) := by
  exact (varF_algebraicIndependent_over_complement (Set.range v)).linearIndependent.comp
    (fun i => ⟨v i, Set.mem_range_self i⟩)
    (fun _ _ h => hv (congrArg Subtype.val h))

theorem complement_closure_le_adjoin (S : Set (Var k M)) :
    Subfield.closure ((@varF k M) '' Sᶜ) ≤
      (IntermediateField.adjoin ℚ ((@varF k M) '' Sᶜ)).toSubfield := by
  exact Subfield.closure_le.mpr (IntermediateField.subset_adjoin ℚ _)

theorem fresh_vars_sum_ne_zero {N : ℕ} (v : Fin N → Var k M)
    (hv : Function.Injective v) (b : Fin N → F k M)
    (hb : ∀ i, b i ∈ Subfield.closure ((@varF k M) '' (Set.range v)ᶜ))
    (hne : ∃ i, b i ≠ 0) :
    ∑ i, varF (v i) * b i ≠ 0 := by
  intro hz
  let c : Fin N → IntermediateField.adjoin ℚ ((@varF k M) '' (Set.range v)ᶜ) :=
    fun i => ⟨b i, complement_closure_le_adjoin (Set.range v) (hb i)⟩
  have hsum : ∑ i, c i • varF (v i) = 0 := by
    simpa only [c, IntermediateField.smul_def, Subtype.coe_mk, smul_eq_mul, mul_comm] using hz
  have hczero := Fintype.linearIndependent_iff.mp (fresh_vars_linearIndependent v hv) c hsum
  exact hne.elim (fun i hi => hi (congrArg Subtype.val (hczero i)))

end KServerConj
end PaperFile002

section PaperFile003
open scoped BigOperators

namespace KServerConj

variable {k : ℕ} {M : Type*}

theorem coeff_fresh_term (v : Var k M) (a b : ℝ) (f : K k M) :
    (coef v * zp a * f).coeff b = varF v * f.coeff (b - a) := by
  simp only [mul_assoc, coef, HahnSeries.C_apply, zp, HahnSeries.coeff_single_mul,
    one_mul, sub_zero]

theorem fresh_sum_coeff_ne_zero {N : ℕ} (v : Fin N → Var k M)
    (hv : Function.Injective v) (f : Fin N → K k M)
    (hf : ∀ i, FreeOf (Set.range v) (f i)) (a : Fin N → ℝ) (b : ℝ)
    (hne : ∃ i, (f i).coeff (b - a i) ≠ 0) :
    (∑ i, coef (v i) * zp (a i) * f i).coeff b ≠ 0 := by
  simpa only [HahnSeries.coeff_sum, coeff_fresh_term] using
    fresh_vars_sum_ne_zero v hv (fun i => (f i).coeff (b - a i))
      (fun i => hf i (b - a i)) hne

theorem nu_fresh_sum_le_of_ne {N : ℕ} (v : Fin N → Var k M)
    (hv : Function.Injective v) (f : Fin N → K k M)
    (hf : ∀ i, FreeOf (Set.range v) (f i)) (a : Fin N → ℝ)
    (j : Fin N) (hj : f j ≠ 0) :
    nu (∑ i, coef (v i) * zp (a i) * f i) ≤ (a j : WithTop ℝ) + nu (f j) := by
  have hcoeff := fresh_sum_coeff_ne_zero v hv f hf a (a j + (f j).order)
    ⟨j, by simpa only [add_sub_cancel_left] using (HahnSeries.coeff_order_eq_zero.not.mpr hj)⟩
  simpa only [nu, HahnSeries.addVal_apply_of_ne hj, ← WithTop.coe_add] using
    (HahnSeries.addVal_le_of_coeff_ne_zero hcoeff)

theorem fresh_coefficients_no_cancellation {N : ℕ} (v : Fin N → Var k M)
    (hv : Function.Injective v) (f : Fin N → K k M)
    (hf : ∀ i, FreeOf (Set.range v) (f i)) (a : Fin N → ℝ) :
    nu (∑ i, coef (v i) * zp (a i) * f i) =
      Finset.univ.inf (fun i => (a i : WithTop ℝ) + nu (f i)) := by
  apply le_antisymm
  · refine Finset.le_inf ?_
    intro j _
    exact (eq_or_ne (f j) 0).elim
      (fun hj => by simp only [hj, nu_zero, WithTop.add_top, le_top])
      (nu_fresh_sum_le_of_ne v hv f hf a j)
  · exact nu_sum_ge _ _ (fun i => by
      simpa only [nu_fresh_term] using
        (Finset.inf_le (f := fun i => (a i : WithTop ℝ) + nu (f i)) (Finset.mem_univ i)))

end KServerConj
end PaperFile003

open KServerConj

theorem solution {k : ℕ} {M : Type*} {N : ℕ} (v : Fin N → Var k M) (hv : Function.Injective v)
    (f : Fin N → K k M) (hf : ∀ i, FreeOf (Set.range v) (f i)) (a : Fin N → ℝ)
    (hne : ∃ i, f i ≠ 0) :
    nu (∑ i, coef (v i) * zp (a i) * f i) =
      Finset.univ.inf fun i => ((a i : ℝ) : WithTop ℝ) + nu (f i) := by
  exact fresh_coefficients_no_cancellation v hv f hf a

#print axioms solution
