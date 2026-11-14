-- Prove2me | solution 1 for KServerConj.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T03:10:49.383284+00:00
-- url     : https://prove2.me/submissions/fd3ecf7d-c251-458c-aef6-0021863f8fb2

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Definitions.Def_KServerConj_workFn
import Definitions.Def_KServerConj_colDet
import Definitions.Def_KServerConj_rowReplace
import Theorems.Thm_KServerConj_eq_2
set_option autoImplicit false

section PaperFile003
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
end PaperFile003

section PaperFile004
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
end PaperFile004

section PaperFile005
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
end PaperFile005

section PaperFile006
namespace KServerConj

noncomputable def hahnCoeffMap {F E : Type*} [Field F] [Field E] (g : F →+* E) :
    HahnSeries ℝ F →+* HahnSeries ℝ E where
  toFun f := f.map g
  map_zero' := HahnSeries.map_zero g.toZeroHom
  map_one' := by
    simpa only [map_one] using (HahnSeries.map_C (Γ := ℝ) (1 : F) g)
  map_add' _ _ := HahnSeries.map_add g.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul g.toNonUnitalRingHom

@[simp] theorem hahnCoeffMap_coeff {F E : Type*} [Field F] [Field E]
    (g : F →+* E) (f : HahnSeries ℝ F) (a : ℝ) :
    (hahnCoeffMap g f).coeff a = g (f.coeff a) := rfl

noncomputable def restrictCoeffs {F : Type*} [Field F] (S : Subfield F) (f : HahnSeries ℝ F)
    (hf : ∀ a, f.coeff a ∈ S) : HahnSeries ℝ S where
  coeff a := ⟨f.coeff a, hf a⟩
  isPWO_support' := f.isPWO_support.mono fun _ ha hz => ha (Subtype.ext hz)

@[simp] theorem restrictCoeffs_map {F : Type*} [Field F] (S : Subfield F)
    (f : HahnSeries ℝ F) (hf : ∀ a, f.coeff a ∈ S) :
    hahnCoeffMap S.subtype (restrictCoeffs S f hf) = f := by
  exact HahnSeries.coeff_injective rfl

theorem coeff_inv_mem_subfield {F : Type*} [Field F] (S : Subfield F)
    (f : HahnSeries ℝ F) (hf : ∀ a, f.coeff a ∈ S) :
    ∀ a, (f⁻¹).coeff a ∈ S := by
  have hmap : hahnCoeffMap S.subtype (restrictCoeffs S f hf)⁻¹ = f⁻¹ := by
    rw [map_inv₀, restrictCoeffs_map]
  exact fun a => (congrArg (fun g : HahnSeries ℝ F => g.coeff a) hmap) ▸
    (((restrictCoeffs S f hf)⁻¹).coeff a).property

end KServerConj
end PaperFile006

section PaperFile007
namespace KServerConj

variable {k : ℕ} {M : Type*}

theorem freeOf_zero (S : Set (Var k M)) : FreeOf S (0 : K k M) := by
  exact fun _ => Subfield.zero_mem _

theorem freeOf_single (S : Set (Var k M)) (a : ℝ) (c : F k M)
    (hc : c ∈ Subfield.closure ((fun v => varF v) '' Sᶜ)) :
    FreeOf S (HahnSeries.single a c) := by
  intro b
  rw [HahnSeries.coeff_single]
  exact ite_mem.mpr ⟨fun _ => hc, fun _ => Subfield.zero_mem _⟩

theorem freeOf_zp (S : Set (Var k M)) (a : ℝ) : FreeOf S (zp a : K k M) := by
  exact freeOf_single S a 1 (Subfield.one_mem _)

theorem freeOf_one (S : Set (Var k M)) : FreeOf S (1 : K k M) := by
  exact freeOf_single S 0 1 (Subfield.one_mem _)

theorem freeOf_coef (S : Set (Var k M)) (v : Var k M) (hv : v ∉ S) :
    FreeOf S (coef v) := by
  exact freeOf_single S 0 (varF v) (Subfield.subset_closure ⟨v, hv, rfl⟩)

theorem freeOf_add {S : Set (Var k M)} {f g : K k M} (hf : FreeOf S f) (hg : FreeOf S g) :
    FreeOf S (f + g) := by
  simpa only [FreeOf, HahnSeries.coeff_add] using
    fun a => Subfield.add_mem _ (hf a) (hg a)

theorem freeOf_neg {S : Set (Var k M)} {f : K k M} (hf : FreeOf S f) :
    FreeOf S (-f) := by
  simpa only [FreeOf, HahnSeries.coeff_neg] using
    fun a => Subfield.neg_mem _ (hf a)

theorem freeOf_mul {S : Set (Var k M)} {f g : K k M} (hf : FreeOf S f) (hg : FreeOf S g) :
    FreeOf S (f * g) := by
  intro a
  rw [HahnSeries.coeff_mul]
  exact Subfield.sum_mem _ fun ij _ => Subfield.mul_mem _ (hf ij.1) (hg ij.2)

theorem freeOf_inv {S : Set (Var k M)} {f : K k M} (hf : FreeOf S f) :
    FreeOf S f⁻¹ := by
  exact coeff_inv_mem_subfield _ f hf

noncomputable def freeOfSubfield (S : Set (Var k M)) : Subfield (K k M) where
  carrier := FreeOf S
  zero_mem' := freeOf_zero S
  one_mem' := freeOf_one S
  add_mem' := freeOf_add
  mul_mem' := freeOf_mul
  neg_mem' := freeOf_neg
  inv_mem' := fun _ hf => freeOf_inv hf

theorem freeOf_div {S : Set (Var k M)} {f g : K k M} (hf : FreeOf S f) (hg : FreeOf S g) :
    FreeOf S (f / g) := by
  exact (freeOfSubfield S).div_mem hf hg

theorem freeOf_sum {S : Set (Var k M)} {ι : Type*} (s : Finset ι) (f : ι → K k M)
    (hf : ∀ i ∈ s, FreeOf S (f i)) : FreeOf S (∑ i ∈ s, f i) := by
  exact (freeOfSubfield S).sum_mem hf

theorem freeOf_prod {S : Set (Var k M)} {ι : Type*} (s : Finset ι) (f : ι → K k M)
    (hf : ∀ i ∈ s, FreeOf S (f i)) : FreeOf S (∏ i ∈ s, f i) := by
  exact (freeOfSubfield S).prod_mem hf

theorem freeOf_mono {S T : Set (Var k M)} {f : K k M} (hST : S ⊆ T)
    (hf : FreeOf T f) : FreeOf S f := by
  exact fun a => Subfield.closure_mono (Set.image_mono (Set.compl_subset_compl.mpr hST)) (hf a)

end KServerConj
end PaperFile007

section PaperFile008
namespace KServerConj

theorem colDet_eq_zero_of_not_injective {k : ℕ} {M : Type*}
    (q : M → Fin k → K k M) (x : Fin k → M) (hx : ¬ Function.Injective x) :
    colDet q x = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hx
  exact Matrix.det_zero_of_column_eq hne (fun a => congrArg (fun y => q y a) hij)

theorem update_injective_of_not_mem_range {ι M : Type*} [DecidableEq ι]
    (x : ι → M) (hx : Function.Injective x) (r : M) (hr : r ∉ Set.range x) (i : ι) :
    Function.Injective (Function.update x i r) := by
  intro a b hab
  by_cases ha : a = i
  · have hb : b = i := Classical.byContradiction fun hb => hr
      ⟨b, by simpa only [Function.update_apply, ha, hb, if_true, if_false] using hab.symm⟩
    exact ha.trans hb.symm
  · have hb : b ≠ i := fun hb => hr
      ⟨a, by simpa only [Function.update_apply, ha, hb, if_true, if_false] using hab⟩
    exact hx (by simpa only [Function.update_apply, ha, hb, if_false] using hab)

end KServerConj
end PaperFile008

section PaperFile009
open scoped BigOperators

namespace KServerAlgebra

theorem det_updateRow_eq_sum_updateCol
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : Matrix ι ι R) (j : ι) (δ : ι → R) :
    (M.updateRow j δ).det =
      ∑ i, δ i * (M.updateCol i (Pi.single j 1)).det := by
  rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec]
  simp only [Matrix.mulVec, dotProduct, Matrix.adjugate_apply,
    Matrix.updateRow_transpose, Matrix.det_transpose]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem updateCol_column_family
    {ι M R : Type*} [DecidableEq ι]
    (q : M → ι → R) (X : ι → M) (i : ι) (r : M) :
    (Matrix.of fun a b => q (X b) a).updateCol i (q r) =
      Matrix.of (fun a b => q (Function.update X i r b) a) := by
  ext a b
  by_cases h : b = i <;> simp [Matrix.updateCol, Function.update, h]

theorem det_updateRow_column_family
    {ι M R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (q : M → ι → R) (X : ι → M) (r : M) (j : ι) (δ : ι → R)
    (hr : q r = Pi.single j 1) :
    ((Matrix.of fun a b => q (X b) a).updateRow j δ).det =
      ∑ i, δ i * (Matrix.of fun a b => q (Function.update X i r b) a).det := by
  simpa only [← hr, updateCol_column_family] using
    det_updateRow_eq_sum_updateCol (Matrix.of fun a b => q (X b) a) j δ

theorem rowReplace_column_matrix
    {n : ℕ} {M R : Type*}
    (q : M → Fin (n + 1) → R) (δ : M → R) (X : Fin (n + 1) → M) :
    (Matrix.of fun a b => Fin.cons (δ (X b)) (Fin.tail (q (X b))) a) =
      (Matrix.of fun a b => q (X b) a).updateRow 0 (fun b => δ (X b)) := by
  ext a b
  cases a using Fin.cases <;> simp [Matrix.updateRow, Function.update, Fin.tail]

theorem det_rowReplace_column_family
    {n : ℕ} {M R : Type*} [CommRing R]
    (q : M → Fin (n + 1) → R) (δ : M → R) (X : Fin (n + 1) → M)
    (r : M) (hr : q r = Pi.single 0 1) :
    (Matrix.of fun a b => Fin.cons (δ (X b)) (Fin.tail (q (X b))) a).det =
      ∑ i, δ (X i) * (Matrix.of fun a b => q (Function.update X i r b) a).det := by
  rw [rowReplace_column_matrix]
  exact det_updateRow_column_family q X r 0 (fun i => δ (X i)) hr

theorem mulVec_column_matrix
    {ι M R : Type*} [Fintype ι] [CommRing R]
    (B : Matrix ι ι R) (q : M → ι → R) (X : ι → M) :
    (Matrix.of fun a b => B.mulVec (q (X b)) a) =
      B * (Matrix.of fun a b => q (X b) a) := by
  rfl

theorem det_normalized_column_family
    {ι M R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (B : Matrix ι ι R) (hB : B.det = 1) (q : M → ι → R) (X : ι → M) :
    (Matrix.of fun a b => B.mulVec (q (X b)) a).det =
      (Matrix.of fun a b => q (X b) a).det := by
  rw [mulVec_column_matrix, Matrix.det_mul, hB, one_mul]

end KServerAlgebra
end PaperFile009

section PaperFile010
open scoped BigOperators

namespace KServerConj

theorem colDet_rowReplace_eq_sum {n : ℕ} {M : Type*}
    (q : M → Fin (n + 1) → K (n + 1) M) (δ : M → K (n + 1) M)
    (x : Fin (n + 1) → M) (r : M) (hr : q r = Pi.single 0 1) :
    colDet (rowReplace q δ) x =
      ∑ i, δ (x i) * colDet q (Function.update x i r) := by
  exact KServerAlgebra.det_rowReplace_column_family q δ x r hr

theorem fresh_rowReplace_valuation_eq_inf {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (t : ℕ)
    (hr : q r = Pi.single 0 1)
    (hfree : ∀ x : Fin (n + 1) → M,
      FreeOf (Set.range fun y : M => (Sum.inr (t, y) : Var (n + 1) M)) (colDet q x))
    (x : Fin (n + 1) → M) (hx : Function.Injective x) :
    nu (colDet (rowReplace q (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) x) =
      Finset.univ.inf (fun i => (dist r (x i) : WithTop ℝ) +
        nu (colDet q (Function.update x i r))) := by
  have hv : Function.Injective (fun i : Fin (n + 1) => (Sum.inr (t, x i) : Var (n + 1) M)) :=
    fun _ _ h => hx (congrArg (fun p : ℕ × M => p.2) (Sum.inr.inj h))
  have hsubset :
      Set.range (fun i : Fin (n + 1) => (Sum.inr (t, x i) : Var (n + 1) M)) ⊆
        Set.range (fun y : M => (Sum.inr (t, y) : Var (n + 1) M)) :=
    fun _ ⟨i, hi⟩ => ⟨x i, hi⟩
  exact (congrArg nu (colDet_rowReplace_eq_sum q
    (fun y => coef (Sum.inr (t, y)) * zp (dist r y)) x r hr)).trans
    (fresh_coefficients_no_cancellation
      (fun i => (Sum.inr (t, x i) : Var (n + 1) M)) hv
      (fun i => colDet q (Function.update x i r))
      (fun i => freeOf_mono hsubset (hfree (Function.update x i r)))
      (fun i => dist r (x i)))

theorem exists_injective_update_le {ι M : Type*} [DecidableEq ι] [PseudoMetricSpace M]
    (x : ι → M) (hx : Function.Injective x) (r : M)
    (w : (ι → M) → ℝ) (b : ℝ)
    (hge : ∃ i, w (Function.update x i r) + dist r (x i) ≤ b) (hmono : w x ≤ b) :
    ∃ i, Function.Injective (Function.update x i r) ∧
      w (Function.update x i r) + dist r (x i) ≤ b := by
  by_cases hrange : r ∈ Set.range x
  · exact hrange.elim (fun j hj =>
      let hu : Function.update x j r = x := Function.update_eq_self_iff.mpr hj.symm
      ⟨j, hu.symm ▸ hx, by simpa only [hu, hj, dist_self, add_zero] using hmono⟩)
  · exact hge.elim (fun i hi =>
      ⟨i, update_injective_of_not_mem_range x hx r hrange i, hi⟩)

theorem determinant_cost_inf_eq {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M)
    (w : (Fin (n + 1) → M) → ℝ) (b : ℝ)
    (hrep : ∀ y : Fin (n + 1) → M, Function.Injective y →
      nu (colDet q y) = (w y : WithTop ℝ))
    (x : Fin (n + 1) → M) (hx : Function.Injective x)
    (hle : ∀ i, b ≤ w (Function.update x i r) + dist r (x i))
    (hge : ∃ i, w (Function.update x i r) + dist r (x i) ≤ b)
    (hmono : w x ≤ b) :
    Finset.univ.inf (fun i => (dist r (x i) : WithTop ℝ) +
      nu (colDet q (Function.update x i r))) = (b : WithTop ℝ) := by
  apply le_antisymm
  · obtain ⟨i, hi, hcost⟩ := exists_injective_update_le x hx r w b hge hmono
    exact (Finset.inf_le
      (f := fun i => (dist r (x i) : WithTop ℝ) + nu (colDet q (Function.update x i r)))
      (Finset.mem_univ i)).trans (by
        simpa only [hrep _ hi, ← WithTop.coe_add, add_comm] using
          (WithTop.coe_le_coe.mpr hcost))
  · refine Finset.le_inf ?_
    intro i _
    exact (em (Function.Injective (Function.update x i r))).elim
      (fun hi => by
        simpa only [hrep _ hi, ← WithTop.coe_add, add_comm] using
          (WithTop.coe_le_coe.mpr (hle i)))
      (fun hi => by
        simp only [colDet_eq_zero_of_not_injective q _ hi, nu_zero, WithTop.add_top, le_top])

theorem request_representation_step {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (t : ℕ)
    (w w' : (Fin (n + 1) → M) → ℝ) (hr : q r = Pi.single 0 1)
    (hrep : ∀ y : Fin (n + 1) → M, Function.Injective y →
      nu (colDet q y) = (w y : WithTop ℝ))
    (hfree : ∀ y : Fin (n + 1) → M,
      FreeOf (Set.range fun z : M => (Sum.inr (t, z) : Var (n + 1) M)) (colDet q y))
    (hrec_le : ∀ y : Fin (n + 1) → M, Function.Injective y → ∀ i,
      w' y ≤ w (Function.update y i r) + dist r (y i))
    (hrec_ge : ∀ y : Fin (n + 1) → M, Function.Injective y →
      ∃ i, w (Function.update y i r) + dist r (y i) ≤ w' y)
    (hmono : ∀ y : Fin (n + 1) → M, Function.Injective y → w y ≤ w' y)
    (x : Fin (n + 1) → M) (hx : Function.Injective x) :
    nu (colDet (rowReplace q (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) x) =
      (w' x : WithTop ℝ) := by
  exact (fresh_rowReplace_valuation_eq_inf q r t hr hfree x hx).trans
    (determinant_cost_inf_eq q r w (w' x) hrep x hx
      (hrec_le x hx) (hrec_ge x hx) (hmono x hx))

theorem rowReplace_det_freeOf {n : ℕ} {M : Type*} (S : Set (Var (n + 1) M))
    (q : M → Fin (n + 1) → K (n + 1) M) (δ : M → K (n + 1) M)
    (r : M) (hr : q r = Pi.single 0 1)
    (hfree : ∀ y : Fin (n + 1) → M, FreeOf S (colDet q y))
    (hδ : ∀ y : M, FreeOf S (δ y)) (x : Fin (n + 1) → M) :
    FreeOf S (colDet (rowReplace q δ) x) := by
  exact (colDet_rowReplace_eq_sum q δ x r hr).symm ▸
    freeOf_sum Finset.univ (fun i => δ (x i) * colDet q (Function.update x i r))
      (fun i _ => freeOf_mul (hδ (x i)) (hfree (Function.update x i r)))

theorem fresh_rowReplace_det_freeOf {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (S : Set (Var (n + 1) M)) (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (t : ℕ)
    (hr : q r = Pi.single 0 1)
    (hfree : ∀ y : Fin (n + 1) → M, FreeOf S (colDet q y))
    (hS : ∀ y : M, Sum.inr (t, y) ∉ S) (x : Fin (n + 1) → M) :
    FreeOf S (colDet (rowReplace q (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) x) := by
  exact rowReplace_det_freeOf S q _ r hr hfree
    (fun y => freeOf_mul (freeOf_coef S (Sum.inr (t, y)) (hS y)) (freeOf_zp S (dist r y))) x

theorem colDet_normalize_eq {k : ℕ} {M : Type*}
    (B : Matrix (Fin k) (Fin k) (K k M)) (hB : B.det = 1)
    (q : M → Fin k → K k M) (x : Fin k → M) :
    colDet (fun y => B.mulVec (q y)) x = colDet q x := by
  exact KServerAlgebra.det_normalized_column_family B hB q x

theorem normalized_request_representation_step {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (K (n + 1) M)) (hB : B.det = 1)
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (t : ℕ)
    (w w' : (Fin (n + 1) → M) → ℝ) (hr : B.mulVec (q r) = Pi.single 0 1)
    (hrep : ∀ y : Fin (n + 1) → M, Function.Injective y →
      nu (colDet q y) = (w y : WithTop ℝ))
    (hfree : ∀ y : Fin (n + 1) → M,
      FreeOf (Set.range fun z : M => (Sum.inr (t, z) : Var (n + 1) M)) (colDet q y))
    (hrec_le : ∀ y : Fin (n + 1) → M, Function.Injective y → ∀ i,
      w' y ≤ w (Function.update y i r) + dist r (y i))
    (hrec_ge : ∀ y : Fin (n + 1) → M, Function.Injective y →
      ∃ i, w (Function.update y i r) + dist r (y i) ≤ w' y)
    (hmono : ∀ y : Fin (n + 1) → M, Function.Injective y → w y ≤ w' y)
    (x : Fin (n + 1) → M) (hx : Function.Injective x) :
    nu (colDet (rowReplace (fun y => B.mulVec (q y))
      (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) x) = (w' x : WithTop ℝ) := by
  exact request_representation_step (fun y => B.mulVec (q y)) r t w w' hr
    (fun y hy => (congrArg nu (colDet_normalize_eq B hB q y)).trans (hrep y hy))
    (fun y => (colDet_normalize_eq B hB q y).symm ▸ hfree y)
    hrec_le hrec_ge hmono x hx

theorem normalized_fresh_rowReplace_det_freeOf {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (S : Set (Var (n + 1) M))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (K (n + 1) M)) (hB : B.det = 1)
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M) (t : ℕ)
    (hr : B.mulVec (q r) = Pi.single 0 1)
    (hfree : ∀ y : Fin (n + 1) → M, FreeOf S (colDet q y))
    (hS : ∀ y : M, Sum.inr (t, y) ∉ S) (x : Fin (n + 1) → M) :
    FreeOf S (colDet (rowReplace (fun y => B.mulVec (q y))
      (fun y => coef (Sum.inr (t, y)) * zp (dist r y))) x) := by
  exact fresh_rowReplace_det_freeOf S (fun y => B.mulVec (q y)) r t hr
    (fun y => (colDet_normalize_eq B hB q y).symm ▸ hfree y) hS x

end KServerConj
end PaperFile010

section PaperFile011
namespace KServerConj

theorem image_update_injective {k : ℕ} {M : Type*} [DecidableEq M]
    (x : Fin k → M) (hx : Function.Injective x) (i : Fin k) (r : M) :
    Finset.univ.image (Function.update x i r) =
      insert r ((Finset.univ.image x).erase (x i)) := by
  classical
  ext a
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_erase]
  constructor
  · rintro ⟨j, rfl⟩
    by_cases hji : j = i
    · subst j
      exact Or.inl (Function.update_self _ _ _)
    · rw [Function.update_of_ne hji]
      exact Or.inr ⟨fun h => hji (hx h), j, rfl⟩
  · rintro (rfl | ⟨ha, j, hj⟩)
    · exact ⟨i, Function.update_self _ _ _⟩
    · have hji : j ≠ i := fun h => ha (by simpa only [h] using hj.symm)
      exact ⟨j, by rw [Function.update_of_ne hji]; exact hj⟩

theorem update_injective_iff_admissible {k : ℕ} {M : Type*} [DecidableEq M]
    (x : Fin k → M) (hx : Function.Injective x) (i : Fin k) (r : M) :
    Function.Injective (Function.update x i r) ↔
      r ∉ Finset.univ.image x ∨ x i = r := by
  classical
  constructor
  · intro hu
    by_cases hr : r ∈ Finset.univ.image x
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hr
      by_cases hji : j = i
      · exact Or.inr (hji ▸ hj)
      · have heq : Function.update x i r j = Function.update x i r i := by
          rw [Function.update_of_ne hji, Function.update_self, hj]
        exact False.elim (hji (hu heq))
    · exact Or.inl hr
  · rintro (hr | hr)
    · exact update_injective_of_not_mem_range x hx r
        (fun ⟨j, hj⟩ => hr (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)) i
    · exact (Function.update_eq_self_iff.mpr hr.symm : Function.update x i r = x).symm ▸ hx

end KServerConj
end PaperFile011

section PaperFile023
open scoped BigOperators

namespace KServerConj

theorem determinant_cost_inf_eq_admissible {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin (n + 1) → K (n + 1) M) (r : M)
    (w : (Fin (n + 1) → M) → ℝ) (b : ℝ)
    (hrep : ∀ y : Fin (n + 1) → M, Function.Injective y →
      nu (colDet q y) = (w y : WithTop ℝ))
    (x : Fin (n + 1) → M) (hx : Function.Injective x)
    (hle : ∀ i, Function.Injective (Function.update x i r) →
      b ≤ w (Function.update x i r) + dist r (x i))
    (hge : ∃ i, Function.Injective (Function.update x i r) ∧
      w (Function.update x i r) + dist r (x i) ≤ b) :
    Finset.univ.inf (fun i => (dist r (x i) : WithTop ℝ) +
      nu (colDet q (Function.update x i r))) = (b : WithTop ℝ) := by
  classical
  apply le_antisymm
  · obtain ⟨i, hi, hcost⟩ := hge
    exact (Finset.inf_le
      (f := fun i => (dist r (x i) : WithTop ℝ) + nu (colDet q (Function.update x i r)))
      (Finset.mem_univ i)).trans (by
        simpa only [hrep _ hi, ← WithTop.coe_add, add_comm] using
          (WithTop.coe_le_coe.mpr hcost))
  · refine Finset.le_inf ?_
    intro i _
    by_cases hi : Function.Injective (Function.update x i r)
    · simpa only [hrep _ hi, ← WithTop.coe_add, add_comm] using
        (WithTop.coe_le_coe.mpr (hle i hi))
    · simp only [colDet_eq_zero_of_not_injective q _ hi, nu_zero, WithTop.add_top, le_top]

theorem fresh_request_representation_admissible {M : Type*} [PseudoMetricSpace M]
    [Fintype M] [DecidableEq M] {m : ℕ}
    (hm : 1 ≤ m) (s : Fin (m + 1) → M) (hs : Function.Injective s) (r : ℕ → M) (t : ℕ)
    (ht : 1 ≤ t) (q : M → Fin (m + 1) → K (m + 1) M)
    (hrep : ∀ x : Fin (m + 1) → M, Function.Injective x →
      nu (colDet q x) = (workFn (m + 1) (Finset.univ.image s) r (t - 1)
        (Finset.univ.image x) : WithTop ℝ))
    (hfree : ∀ x : Fin (m + 1) → M,
      FreeOf (Set.range fun y : M => (Sum.inr (t, y) : Var (m + 1) M)) (colDet q x))
    (hr : q (r t) = Pi.single 0 1) :
    ∀ x : Fin (m + 1) → M, Function.Injective x →
      nu (colDet (rowReplace q (freshRow r t)) x) =
        (workFn (m + 1) (Finset.univ.image s) r t (Finset.univ.image x) : WithTop ℝ) := by
  classical
  intro x hx
  have hS : (Finset.univ.image s).card = m + 1 := by
    rw [Finset.card_image_of_injective _ hs]
    simp
  have hX : (Finset.univ.image x).card = m + 1 := by
    rw [Finset.card_image_of_injective _ hx]
    simp
  have hrec := (eq_2 (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
    (Finset.univ.image s) hS r).2 t ht (Finset.univ.image x) hX
  have hle (i : Fin (m + 1)) (hi : Function.Injective (Function.update x i (r t))) :
      workFn (m + 1) (Finset.univ.image s) r t (Finset.univ.image x) ≤
        workFn (m + 1) (Finset.univ.image s) r (t - 1)
          (Finset.univ.image (Function.update x i (r t))) + dist (r t) (x i) := by
    rw [image_update_injective x hx i (r t)]
    exact hrec.1 (x i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      ((update_injective_iff_admissible x hx i (r t)).mp hi)
  have hge : ∃ i : Fin (m + 1), Function.Injective (Function.update x i (r t)) ∧
      workFn (m + 1) (Finset.univ.image s) r (t - 1)
        (Finset.univ.image (Function.update x i (r t))) + dist (r t) (x i) ≤
          workFn (m + 1) (Finset.univ.image s) r t (Finset.univ.image x) := by
    obtain ⟨a, ha, hvalid, heq⟩ := hrec.2
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    refine ⟨i, (update_injective_iff_admissible x hx i (r t)).mpr hvalid, ?_⟩
    rw [image_update_injective x hx i (r t)]
    exact heq.ge
  have hcost := determinant_cost_inf_eq_admissible q (r t)
    (fun y => workFn (m + 1) (Finset.univ.image s) r (t - 1) (Finset.univ.image y))
    (workFn (m + 1) (Finset.univ.image s) r t (Finset.univ.image x)) hrep x hx hle hge
  change nu (colDet (rowReplace q (fun y => coef (Sum.inr (t, y)) * zp (dist (r t) y))) x) = _
  exact (fresh_rowReplace_valuation_eq_inf q (r t) t hr hfree x hx).trans hcost

end KServerConj
end PaperFile023

open KServerConj

theorem solution {M : Type*} [PseudoMetricSpace M] [Fintype M] [DecidableEq M] {m : ℕ}
    (hm : 1 ≤ m) (s : Fin (m + 1) → M) (hs : Function.Injective s) (r : ℕ → M) (t : ℕ)
    (ht : 1 ≤ t) (q : M → Fin (m + 1) → K (m + 1) M)
    (hrep : ∀ x : Fin (m + 1) → M, Function.Injective x →
      nu (colDet q x) = ((workFn (m + 1) (Finset.univ.image s) r (t - 1) (Finset.univ.image x) : ℝ) :
        WithTop ℝ))
    (hfree : ∀ x : Fin (m + 1) → M,
      FreeOf (Set.range fun y : M => (Sum.inr (t, y) : Var (m + 1) M)) (colDet q x))
    (hr : q (r t) = Pi.single 0 1) :
    ∀ x : Fin (m + 1) → M, Function.Injective x →
      nu (colDet (rowReplace q (freshRow r t)) x) =
        ((workFn (m + 1) (Finset.univ.image s) r t (Finset.univ.image x) : ℝ) : WithTop ℝ) := by
  exact fresh_request_representation_admissible hm s hs r t ht q hrep hfree hr

#print axioms solution
