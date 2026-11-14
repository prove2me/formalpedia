-- Prove2me | solution 1 for KServerConj.theorem_2_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T03:29:31.728839+00:00
-- url     : https://prove2.me/submissions/c1a28779-0556-4175-903a-b23c29f14787

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.WithTop
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Transvection
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
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Definitions.Def_KServerConj_K
import Definitions.Def_KServerConj_initCols
import Definitions.Def_KServerConj_colDet
import Definitions.Def_KServerConj_rowReplace
import Definitions.Def_KServerConj_IsRun
import Definitions.Def_KServerConj_confDist
import Definitions.Def_KServerConj_workFn
import Definitions.Def_KServerConj_symProd
import Definitions.Def_KServerConj_minorVal
import Definitions.Def_KServerConj_Psi
set_option autoImplicit false

section PaperFile008
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
end PaperFile008

section PaperFile009
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
end PaperFile009

section PaperFile010
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
end PaperFile010

section PaperFile011
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
end PaperFile011

section PaperFile012
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
end PaperFile012

section PaperFile013
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
end PaperFile013

section PaperFile014
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
end PaperFile014

section PaperFile015
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
end PaperFile015

section PaperFile016
open scoped BigOperators

namespace KServerAlgebra

theorem exists_nonsingular_matrix_with_first_column
    {K : Type*} [Field K] {n : ℕ}
    (v : Fin (n + 1) → K) (hv : v ≠ 0) :
    ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) K,
      A.det ≠ 0 ∧ (fun r => A r 0) = v := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  refine ⟨((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K).updateCol j v).submatrix
    id (Equiv.swap 0 j), ?_, ?_⟩
  · rw [Matrix.det_permute']
    apply mul_ne_zero
    · exact ((Equiv.Perm.sign (Equiv.swap (0 : Fin (n + 1)) j)).isUnit.map
        (Int.castRingHom K)).ne_zero
    · simpa [← Matrix.cramer_apply] using hj
  · exact funext (fun r => by simp [Matrix.submatrix])

theorem exists_nonsingular_normalizer
    {K : Type*} [Field K] {n : ℕ}
    (v : Fin (n + 1) → K) (hv : v ≠ 0) :
    ∃ T : Matrix (Fin (n + 1)) (Fin (n + 1)) K,
      T.det ≠ 0 ∧ T.mulVec v = Pi.single 0 1 := by
  obtain ⟨A, hA, hcol⟩ := exists_nonsingular_matrix_with_first_column v hv
  refine ⟨A⁻¹, (A.isUnit_nonsing_inv_det (isUnit_iff_ne_zero.mpr hA)).ne_zero, ?_⟩
  have hvec : A.mulVec (Pi.single 0 1) = v := by
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply'] using hcol
  rw [← hvec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA), Matrix.one_mulVec]

theorem exists_det_one_normalizer
    {K : Type*} [Field K] {n : ℕ}
    (v : Fin (n + 2) → K) (hv : v ≠ 0) :
    ∃ B : Matrix (Fin (n + 2)) (Fin (n + 2)) K,
      B.det = 1 ∧ B.mulVec v = Pi.single 0 1 := by
  obtain ⟨T, hT, hTv⟩ := exists_nonsingular_normalizer v hv
  refine ⟨T.updateRow 1 (T.det⁻¹ • T 1), ?_, ?_⟩
  · rw [Matrix.det_updateRow_smul, Matrix.updateRow_eq_self, inv_mul_cancel₀ hT]
  · have hrow : dotProduct (T 1) v = 0 := by
      simpa [Matrix.mulVec] using congrFun hTv 1
    simp [Matrix.updateRow_mulVec, smul_dotProduct, hrow, hTv]

end KServerAlgebra
end PaperFile016

section PaperFile017
set_option autoImplicit false

namespace KServerConj

noncomputable def hahnCoeffRingMap {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : HahnSeries ℝ R →+* HahnSeries ℝ S where
  toFun a := a.map f
  map_zero' := HahnSeries.map_zero f.toZeroHom
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_add' _ _ := HahnSeries.map_add f.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom

@[simp] theorem hahnCoeffRingMap_coeff {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : HahnSeries ℝ R) (t : ℝ) :
    (hahnCoeffRingMap f a).coeff t = f (a.coeff t) := rfl

@[simp] theorem hahnCoeffRingMap_single {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : ℝ) (r : R) :
    hahnCoeffRingMap f (HahnSeries.single a r) = HahnSeries.single a (f r) := by
  exact HahnSeries.map_single f.toZeroHom

end KServerConj
end PaperFile017

section PaperFile021
open scoped BigOperators

theorem det_mul_det_updateCol
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (A B : Matrix ι ι R) (j : ι) (v : ι → R) :
    A.det * (B.updateCol j v).det =
      ∑ i, (A.updateCol i v).det *
        (B.updateCol j (fun r => A r i)).det := by
  have h : A.det • v =
      ∑ i, (A.updateCol i v).det • (fun r => A r i) := by
    rw [← Matrix.mulVec_cramer A v]
    ext r
    simp only [Matrix.mulVec, dotProduct, Matrix.cramer_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  have h' := congrArg (fun w : ι → R => B.cramer w j) h
  simp only [map_smul, map_sum] at h'
  simpa only [map_smul, map_sum, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.cramer_apply] using h'
end PaperFile021

section PaperFile022
open scoped BigOperators

namespace DetValuationMilestone

def prependColumn {n : ℕ} {R : Type*} (v : Fin (n + 1) → R)
    (W : Matrix (Fin (n + 1)) (Fin n) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun r j => Fin.cases (v r) (fun j => W r j) j

theorem updateCol_prepend {n : ℕ} {R : Type*}
    (v w : Fin (n + 1) → R) (W : Matrix (Fin (n + 1)) (Fin n) R) :
    (prependColumn v W).updateCol 0 w = prependColumn w W := by
  ext r j
  cases j using Fin.cases <;> simp [prependColumn, Matrix.updateCol]

theorem det_prepend_single {n : ℕ} {R : Type*} [CommRing R]
    (W : Matrix (Fin (n + 1)) (Fin n) R) :
    (prependColumn (Pi.single 0 1) W).det = (W.submatrix Fin.succ id).det := by
  rw [Matrix.det_succ_column_zero]
  simp [prependColumn, Matrix.submatrix, Pi.single_apply, mul_ite, ite_mul]

theorem det_mul_det_prepend {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (v : Fin (n + 1) → R) (W : Matrix (Fin (n + 1)) (Fin n) R) :
    A.det * (prependColumn v W).det =
      ∑ i, (A.updateCol i v).det * (prependColumn (fun r => A r i) W).det := by
  simpa only [updateCol_prepend] using det_mul_det_updateCol A (prependColumn v W) 0 v

theorem det_prepend_smul {n : ℕ} {R : Type*} [CommRing R]
    (c : R) (v : Fin (n + 1) → R) (W : Matrix (Fin (n + 1)) (Fin n) R) :
    (prependColumn (c • v) W).det = c * (prependColumn v W).det := by
  simpa only [updateCol_prepend] using Matrix.det_updateCol_smul (prependColumn v W) 0 c v

theorem prepend_submatrix {n : ℕ} {R ι : Type*}
    (H : Matrix (Fin (n + 1)) ι R) (x : ι) (y : Fin n → ι) :
    prependColumn (fun r => H r x) (H.submatrix id y) =
      H.submatrix id (Fin.cases x y) := by
  ext r j
  cases j using Fin.cases <;> rfl

theorem projected_minor_identity {n : ℕ} {R ι : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (y : Fin n → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i))) :
    A.det * (H.submatrix Fin.succ y).det =
      ∑ i, (A.updateCol i (Pi.single 0 1)).det * c i *
        (prependColumn (fun r => H r (x i)) (H.submatrix id y)).det := by
  simpa only [det_prepend_single, Matrix.submatrix_submatrix, Function.comp_id,
    Function.id_comp, hcol, det_prepend_smul, mul_assoc] using
      det_mul_det_prepend A (Pi.single 0 1) (H.submatrix id y)

theorem exists_nonzero_projected_minor {n : ℕ} {R ι : Type*} [CommRing R]
    (H : Matrix (Fin (n + 1)) ι R) (x : Fin (n + 1) → ι)
    (hdet : (H.submatrix id x).det ≠ 0) :
    ∃ y : Fin n → ι, (H.submatrix Fin.succ y).det ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hdet
  rw [Matrix.det_succ_row_zero]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  simp only [Matrix.submatrix_submatrix, Function.id_comp, h, mul_zero]

theorem nonzero_unscaled_minor {n : ℕ} {R ι : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i)))
    (hdet : A.det ≠ 0) : (H.submatrix id x).det ≠ 0 := by
  have hA : A = Matrix.of (fun r i => c i * (H.submatrix id x) r i) :=
    funext fun r => funext fun i => congrFun (hcol i) r
  rw [hA, Matrix.det_mul_row c (H.submatrix id x)] at hdet
  exact right_ne_zero_of_mul hdet

theorem det_eq_sum_scaled_cramer {n : ℕ} {R ι : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i))) :
    A.det = ∑ i, (A.updateCol i (Pi.single 0 1)).det * c i * H 0 (x i) := by
  have hentry : ∀ r i, A r i = c i * H r (x i) :=
    fun r i => congrFun (hcol i) r
  simpa [Matrix.mulVec, dotProduct, Matrix.cramer_apply, hentry,
    mul_comm, mul_left_comm, mul_assoc] using
      (congrFun (Matrix.mulVec_cramer A (Pi.single 0 1)) 0).symm

theorem exists_nonzero_scaled_cramer {n : ℕ} {R ι : Type*} [CommRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i)))
    (hdet : A.det ≠ 0) :
    ∃ i, (A.updateCol i (Pi.single 0 1)).det * c i ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hdet (by
    simpa only [h, zero_mul, Finset.sum_const_zero] using det_eq_sum_scaled_cramer A H x c hcol)

end DetValuationMilestone
end PaperFile022

section PaperFile023
open scoped BigOperators

namespace DetValuationMilestone

theorem valuation_sum_lower_bound
    {R ι : Type*} [AddCommMonoid R]
    (ν : R → WithTop ℝ)
    (hzero : ν 0 = ⊤)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (s : Finset ι) (f : ι → R) (c : WithTop ℝ)
    (hf : ∀ i ∈ s, c ≤ ν (f i)) :
    c ≤ ν (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hzero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (le_min (hf i (Finset.mem_insert_self _ _))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))).trans (hadd _ _)

theorem valuation_lower_bound_of_minor_identity
    {R ι : Type*} [Semiring R] [Fintype ι]
    (ν : R → WithTop ℝ)
    (hzero : ν 0 = ⊤)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (D P : R) (a M : ι → R) (δ α μ : ℝ)
    (hD : ν D = (δ : WithTop ℝ))
    (hid : D * P = ∑ i, a i * M i)
    (ha : ∀ i, (α : WithTop ℝ) ≤ ν (a i))
    (hM : ∀ i, (μ : WithTop ℝ) ≤ ν (M i)) :
    ((α + μ - δ : ℝ) : WithTop ℝ) ≤ ν P := by
  have hsum : ((α + μ : ℝ) : WithTop ℝ) ≤ ν (∑ i, a i * M i) := by
    apply valuation_sum_lower_bound ν hzero hadd
    intro i _
    simpa only [WithTop.coe_add, hmul] using add_le_add (ha i) (hM i)
  rw [← hid, hmul, hD] at hsum
  apply WithTop.le_of_add_le_add_left (x := (δ : WithTop ℝ)) (by simp)
  simpa only [← WithTop.coe_add,
    show δ + (α + μ - δ) = α + μ by linarith] using hsum

theorem minValue_growth_of_minor_identities
    {R ι κ : Type*} [Semiring R] [Fintype ι]
    (ν : R → WithTop ℝ)
    (hzero : ν 0 = ⊤)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (D : R) (a : ι → R) (P : κ → R) (M : ι → κ → R)
    (δ α μ μhat : ℝ)
    (hD : ν D = (δ : WithTop ℝ))
    (hid : ∀ y, D * P y = ∑ i, a i * M i y)
    (ha : ∀ i, (α : WithTop ℝ) ≤ ν (a i))
    (hM : ∀ i y, (μ : WithTop ℝ) ≤ ν (M i y))
    (hmin : ∃ y, ν (P y) = (μhat : WithTop ℝ)) :
    α - δ ≤ μhat - μ := by
  obtain ⟨y, hy⟩ := hmin
  have h := valuation_lower_bound_of_minor_identity ν hzero hmul hadd
    D (P y) a (fun i => M i y) δ α μ hD (hid y) ha (fun i => hM i y)
  rw [hy, WithTop.coe_le_coe] at h
  linarith

theorem exists_real_minimum_of_nonzero
    {R ι : Type*} [Zero R] [Fintype ι]
    (ν : R → WithTop ℝ)
    (htop : ∀ x, ν x = ⊤ ↔ x = 0)
    (f : ι → R) (hnonzero : ∃ i, f i ≠ 0) :
    ∃ μ : ℝ,
      (Finset.univ.inf fun i => ν (f i)) = (μ : WithTop ℝ) ∧
      (∀ i, (μ : WithTop ℝ) ≤ ν (f i)) ∧
      (∃ i, ν (f i) = (μ : WithTop ℝ) ∧ f i ≠ 0) := by
  classical
  obtain ⟨i, hi⟩ := hnonzero
  have hfinite : (Finset.univ.inf fun i => ν (f i)) ≠ ⊤ := by
    exact ne_of_lt ((Finset.inf_le (Finset.mem_univ i)).trans_lt
      (lt_top_iff_ne_top.mpr fun h => hi ((htop _).mp h)))
  obtain ⟨μ, hμ⟩ := WithTop.ne_top_iff_exists.mp hfinite
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf (Finset.univ : Finset ι)
    ⟨i, Finset.mem_univ i⟩ (fun j => ν (f j))
  exact ⟨μ, hμ.symm, fun j => hμ.trans_le (Finset.inf_le (Finset.mem_univ j)),
    j, hj.symm.trans hμ.symm, fun hz => hfinite (hj.trans ((htop _).mpr hz))⟩

theorem canonical_minValue_growth
    {R ι κ η : Type*} [Semiring R] [Fintype ι] [Fintype κ] [Fintype η]
    (ν : R → WithTop ℝ)
    (htop : ∀ x, ν x = ⊤ ↔ x = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (D : R) (a : ι → R) (P : κ → R) (F : η → R) (M : ι → κ → R)
    (hD : D ≠ 0)
    (ha_nonzero : ∃ i, a i ≠ 0)
    (hP_nonzero : ∃ y, P y ≠ 0)
    (hF_nonzero : ∃ z, F z ≠ 0)
    (hid : ∀ y, D * P y = ∑ i, a i * M i y)
    (hM : ∀ i y, M i y = 0 ∨ ∃ z, M i y = F z) :
    ∃ δ α μ μhat : ℝ,
      ν D = (δ : WithTop ℝ) ∧
      (Finset.univ.inf fun i => ν (a i)) = (α : WithTop ℝ) ∧
      (Finset.univ.inf fun z => ν (F z)) = (μ : WithTop ℝ) ∧
      (Finset.univ.inf fun y => ν (P y)) = (μhat : WithTop ℝ) ∧
      α - δ ≤ μhat - μ := by
  obtain ⟨δ, hδ⟩ := WithTop.ne_top_iff_exists.mp (fun h => hD ((htop _).mp h))
  obtain ⟨α, hα, ha, _⟩ := exists_real_minimum_of_nonzero ν htop a ha_nonzero
  obtain ⟨μ, hμ, hF, _⟩ := exists_real_minimum_of_nonzero ν htop F hF_nonzero
  obtain ⟨μhat, hμhat, _, y, hy, _⟩ :=
    exists_real_minimum_of_nonzero ν htop P hP_nonzero
  exact ⟨δ, α, μ, μhat, hδ.symm, hα, hμ, hμhat,
    minValue_growth_of_minor_identities ν ((htop 0).mpr rfl) hmul hadd
      D a P M δ α μ μhat hδ.symm hid ha
      (fun i y => (hM i y).elim
        (fun hz => by simp [hz, (htop 0).mpr rfl])
        (fun ⟨z, hz⟩ => by simpa only [hz] using hF z))
      ⟨y, hy⟩⟩

end DetValuationMilestone
end PaperFile023

section PaperFile024
open scoped BigOperators

namespace DetValuationMilestone

theorem canonical_projected_minValue_growth
    {n : ℕ} {R ι : Type*} [CommRing R] [Fintype ι]
    (ν : R → WithTop ℝ)
    (htop : ∀ x, ν x = ⊤ ↔ x = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i)))
    (hdet : A.det ≠ 0) :
    ∃ δ α μ μhat : ℝ,
      ν A.det = (δ : WithTop ℝ) ∧
      (Finset.univ.inf fun i => ν ((A.updateCol i (Pi.single 0 1)).det * c i)) =
        (α : WithTop ℝ) ∧
      (Finset.univ.inf fun z : Fin (n + 1) → ι => ν (H.submatrix id z).det) =
        (μ : WithTop ℝ) ∧
      (Finset.univ.inf fun y : Fin n → ι => ν (H.submatrix Fin.succ y).det) =
        (μhat : WithTop ℝ) ∧
      α - δ ≤ μhat - μ := by
  exact canonical_minValue_growth ν htop hmul hadd A.det
    (fun i => (A.updateCol i (Pi.single 0 1)).det * c i)
    (fun y : Fin n → ι => (H.submatrix Fin.succ y).det)
    (fun z : Fin (n + 1) → ι => (H.submatrix id z).det)
    (fun i y => (prependColumn (fun r => H r (x i)) (H.submatrix id y)).det)
    hdet (exists_nonzero_scaled_cramer A H x c hcol hdet)
    (exists_nonzero_projected_minor H x (nonzero_unscaled_minor A H x c hcol hdet))
    ⟨x, nonzero_unscaled_minor A H x c hcol hdet⟩
    (fun y => projected_minor_identity A H x y c hcol)
    (fun i y => Or.inr ⟨Fin.cases (x i) y,
      congrArg Matrix.det (prepend_submatrix H (x i) y)⟩)

end DetValuationMilestone
end PaperFile024

section PaperFile025
open scoped BigOperators

namespace DetValuationMilestone

noncomputable def tupleMinorVal
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (G : Matrix I J R) : WithTop ℝ := by
  classical
  exact Finset.univ.inf fun e : I → J => ν (G.submatrix id e).det

noncomputable def embeddingMinorVal
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (G : Matrix I J R) : WithTop ℝ := by
  classical
  exact Finset.univ.inf fun e : I ↪ J => ν (G.submatrix id e).det

theorem det_submatrix_eq_zero_of_not_injective
    {I J R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (G : Matrix I J R) (x : I → J) (hx : ¬ Function.Injective x) :
    (G.submatrix id x).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hx
  exact Matrix.det_zero_of_column_eq hne (fun r => congrArg (fun j => G r j) hij)

theorem embeddingMinorVal_le_tuple
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤)
    (G : Matrix I J R) (x : I → J) :
    embeddingMinorVal ν G ≤ ν (G.submatrix id x).det := by
  classical
  exact (Classical.em (Function.Injective x)).elim
    (fun hx => Finset.inf_le (f := fun e : I ↪ J => ν (G.submatrix id e).det)
      (Finset.mem_univ (⟨x, hx⟩ : I ↪ J)))
    (fun hx => by
      simpa only [det_submatrix_eq_zero_of_not_injective G x hx, hzero] using
        (le_top : embeddingMinorVal ν G ≤ ⊤))

theorem tupleMinorVal_eq_embeddingMinorVal
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (G : Matrix I J R) :
    tupleMinorVal ν G = embeddingMinorVal ν G := by
  classical
  exact le_antisymm
    (Finset.le_inf fun e _ => Finset.inf_le
      (f := fun x : I → J => ν (G.submatrix id x).det) (Finset.mem_univ (e : I → J)))
    (Finset.le_inf fun x _ => embeddingMinorVal_le_tuple ν hzero G x)

theorem add_finset_inf {ι : Type*} (a : WithTop ℝ) (s : Finset ι)
    (f : ι → WithTop ℝ) :
    a + s.inf f = s.inf (fun i => a + f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.inf_insert, ← ih, min_add_add_left]

theorem tupleMinorVal_mul
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (A : Matrix I I R) (G : Matrix I J R) :
    tupleMinorVal ν (A * G) = ν A.det + tupleMinorVal ν G := by
  have hval : ∀ x : I → J, ν ((A * G).submatrix id x).det =
      ν A.det + ν (G.submatrix id x).det := fun x =>
    (congrArg ν (Matrix.det_mul A (G.submatrix id x))).trans (hmul _ _)
  simpa only [tupleMinorVal, hval] using
    (add_finset_inf (ν A.det) (Finset.univ : Finset (I → J))
      (fun x => ν (G.submatrix id x).det)).symm

theorem embeddingMinorVal_mul
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (A : Matrix I I R) (G : Matrix I J R) :
    embeddingMinorVal ν (A * G) = ν A.det + embeddingMinorVal ν G := by
  simpa only [tupleMinorVal_eq_embeddingMinorVal ν hzero] using tupleMinorVal_mul ν hmul A G

end DetValuationMilestone
end PaperFile025

section PaperFile026
namespace KServerConj

theorem minorVal_eq_embeddingMinorVal
    {F I J : Type*} [Field F] [Fintype I] [hI : DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) :
    minorVal G = DetValuationMilestone.embeddingMinorVal (HahnSeries.addVal ℝ F) G := by
  classical
  cases Subsingleton.elim hI (Classical.decEq I)
  unfold minorVal DetValuationMilestone.embeddingMinorVal
  rfl

theorem minorVal_mul
    {F I J : Type*} [Field F] [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix I I (HahnSeries ℝ F)) (G : Matrix I J (HahnSeries ℝ F)) :
    minorVal (A * G) = HahnSeries.addVal ℝ F A.det + minorVal G := by
  simpa only [minorVal_eq_embeddingMinorVal] using
    DetValuationMilestone.embeddingMinorVal_mul (HahnSeries.addVal ℝ F)
      (AddValuation.map_zero _) (fun x y => AddValuation.map_mul _ x y) A G

end KServerConj
end PaperFile026

section PaperFile027
open scoped BigOperators

namespace KServerConj

noncomputable def quadraticMatrix {F : Type*} [Field F] {k : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin k → HahnSeries ℝ F) :
    Matrix (Sym2 (Fin k)) (Sym2 M) (HahnSeries ℝ F) :=
  fun p c => Sym2.lift ⟨fun x y =>
    HahnSeries.single (-dist x y) (1 : F) * symProd (q x) (q y) p,
    fun x y => by
      dsimp only
      rw [dist_comm, symProd_comm]⟩ c

theorem Qmat_eq_quadraticMatrix {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin k → K k M) : Qmat q = quadraticMatrix q := rfl

noncomputable def weightedColumns {F : Type*} [Field F] {k : ℕ} {M : Type*}
    [PseudoMetricSpace M] (q : M → Fin k → HahnSeries ℝ F) (r : M) :
    Matrix (Fin k) M (HahnSeries ℝ F) :=
  fun i x => HahnSeries.single (-dist r x) (1 : F) * q x i

noncomputable def negPairDist {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (x : Fin k → M) : Sym2 (Fin k) → ℝ :=
  Sym2.lift ⟨fun i j => -dist (x i) (x j),
    fun i j => congrArg Neg.neg (dist_comm (x i) (x j))⟩

theorem quadraticMatrix_submatrix {F : Type*} [Field F]
    {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin k → HahnSeries ℝ F) (x : Fin k → M) :
    (quadraticMatrix q).submatrix id (Sym2.map x) =
      Matrix.of (fun r c => HahnSeries.single (negPairDist x c) (1 : F) *
        sym2Mat (Matrix.of (fun i j => q (x j) i)) r c) := by
  funext r c
  induction c using Sym2.ind with
  | _ i j => rfl

end KServerConj
end PaperFile027

section PaperFile028
namespace KServerConj

theorem nu_det_C {k : ℕ} {M ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (F k M)) (hA : A.det ≠ 0) :
    nu (((HahnSeries.C : F k M →+* K k M).mapMatrix A).det) = 0 := by
  exact (congrArg nu ((HahnSeries.C : F k M →+* K k M).map_det A).symm).trans (nu_C hA)

end KServerConj
end PaperFile028

section PaperFile029
namespace KServerConj

theorem freeOf_det {k : ℕ} {M ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Set (Var k M)} (A : Matrix ι ι (K k M)) (hA : ∀ i j, FreeOf S (A i j)) :
    FreeOf S A.det := by
  let B : Matrix ι ι (freeOfSubfield S) := fun i j => ⟨A i j, hA i j⟩
  exact ((freeOfSubfield S).subtype.map_det B) ▸ B.det.property

end KServerConj
end PaperFile029

section PaperFile030
open scoped BigOperators

namespace KServerConj

variable {k : ℕ} {M : Type*}

theorem gamma_det_ne_zero (x : Fin k → M) (hx : Function.Injective x) :
    (Matrix.of fun i j : Fin k => varF (Sum.inl (i, x j))).det ≠ 0 := by
  let ρ : Fin k × Fin k → Var k M := fun ij => Sum.inl (ij.1, x ij.2)
  have hρ : Function.Injective ρ := fun a b h =>
    let h' : (a.1, x a.2) = (b.1, x b.2) := Sum.inl.inj h
    Prod.ext (congrArg (fun z : Fin k × M => z.1) h')
      (hx (congrArg (fun z : Fin k × M => z.2) h'))
  have hAI := (@varF_algebraicIndependent k M).comp ρ hρ
  have hne := (map_ne_zero_iff (MvPolynomial.aeval ((@varF k M) ∘ ρ))
    (algebraicIndependent_iff_injective_aeval.mp hAI)).mpr
      (Matrix.det_mvPolynomialX_ne_zero (m := Fin k) (R := ℚ))
  simpa [AlgHom.map_det, Matrix.mvPolynomialX, Matrix.map, ρ] using hne

theorem nu_gamma_det (x : Fin k → M) (hx : Function.Injective x) :
    nu ((Matrix.of fun i j : Fin k => coef (Sum.inl (i, x j))).det) = 0 := by
  exact nu_det_C (Matrix.of fun i j : Fin k => varF (Sum.inl (i, x j)))
    (gamma_det_ne_zero x hx)

theorem weighted_gamma_det_valuation (w : M → ℝ) (x : Fin k → M)
    (hx : Function.Injective x) :
    nu ((Matrix.of fun i j : Fin k => coef (Sum.inl (i, x j)) * zp (w (x j))).det) =
      ((∑ j, w (x j) : ℝ) : WithTop ℝ) := by
  have hfactor :
      (Matrix.of fun i j : Fin k => coef (Sum.inl (i, x j)) * zp (w (x j))).det =
        (∏ j, (zp (w (x j)) : K k M)) *
          (Matrix.of fun i j : Fin k => coef (Sum.inl (i, x j))).det := by
    simpa only [Matrix.of_apply, mul_comm] using
      Matrix.det_mul_row (fun j => (zp (w (x j)) : K k M))
        (Matrix.of fun i j : Fin k => coef (Sum.inl (i, x j)))
  rw [hfactor, ← zp_sum Finset.univ (fun j => w (x j)), nu_mul, nu_zp,
    nu_gamma_det x hx, add_zero]

theorem initCols_colDet_valuation_of_uniform_dist [PseudoMetricSpace M]
    (s : Fin k → M) (w : M → ℝ) (hd : ∀ i y, dist (s i) y = w y)
    (x : Fin k → M) (hx : Function.Injective x) :
    nu (colDet (initCols s) x) = ((∑ j, w (x j) : ℝ) : WithTop ℝ) := by
  simpa only [colDet, initCols, hd] using weighted_gamma_det_valuation w x hx

theorem initCols_coalesced_valuation [PseudoMetricSpace M]
    (p : M) (x : Fin k → M) (hx : Function.Injective x) :
    nu (colDet (initCols (fun _ : Fin k => p)) x) =
      ((∑ j, dist p (x j) : ℝ) : WithTop ℝ) := by
  exact initCols_colDet_valuation_of_uniform_dist (fun _ => p) (dist p) (fun _ _ => rfl) x hx

theorem initCols_freeOf [PseudoMetricSpace M] (S : Set (Var k M))
    (hS : ∀ (i : Fin k) (y : M), Sum.inl (i, y) ∉ S)
    (s : Fin k → M) (y : M) (i : Fin k) : FreeOf S (initCols s y i) := by
  exact freeOf_mul (freeOf_coef S (Sum.inl (i, y)) (hS i y))
    (freeOf_zp S (dist (s i) y))

theorem colDet_freeOf (S : Set (Var k M)) (q : M → Fin k → K k M)
    (x : Fin k → M) (hq : ∀ i j, FreeOf S (q (x j) i)) : FreeOf S (colDet q x) := by
  exact freeOf_det (Matrix.of fun i j => q (x j) i) hq

theorem initCols_colDet_freeOf [PseudoMetricSpace M] (S : Set (Var k M))
    (hS : ∀ (i : Fin k) (y : M), Sum.inl (i, y) ∉ S)
    (s : Fin k → M) (x : Fin k → M) : FreeOf S (colDet (initCols s) x) := by
  exact colDet_freeOf S (initCols s) x (fun i j => initCols_freeOf S hS s (x j) i)

end KServerConj
end PaperFile030

section PaperFile031
open scoped BigOperators

namespace KServerConj

@[simp] theorem symProd_apply {R : Type*} [CommRing R] {k : ℕ}
    (a b : Fin k → R) (i j : Fin k) :
    symProd a b s(i, j) =
      if i = j then a i * b i else a i * b j + a j * b i := by
  rfl

theorem symProd_add_left {R : Type*} [CommRing R] {k : ℕ}
    (a b c : Fin k → R) : symProd (a + b) c = symProd a c + symProd b c := by
  funext p
  induction p using Sym2.ind with
  | _ i j =>
    simp only [Pi.add_apply, symProd_apply]
    split_ifs <;> ring

theorem symProd_smul_left {R : Type*} [CommRing R] {k : ℕ}
    (c : R) (a b : Fin k → R) : symProd (c • a) b = c • symProd a b := by
  funext p
  induction p using Sym2.ind with
  | _ i j =>
    simp only [Pi.smul_apply, symProd_apply, smul_eq_mul]
    split_ifs <;> ring

theorem symProd_add_right {R : Type*} [CommRing R] {k : ℕ}
    (a b c : Fin k → R) : symProd a (b + c) = symProd a b + symProd a c := by
  simpa only [symProd_comm] using symProd_add_left b c a

theorem symProd_smul_right {R : Type*} [CommRing R] {k : ℕ}
    (c : R) (a b : Fin k → R) : symProd a (c • b) = c • symProd a b := by
  simpa only [symProd_comm] using symProd_smul_left c b a

def symProdBilin {R : Type*} [CommRing R] {k : ℕ} :
    (Fin k → R) →ₗ[R] (Fin k → R) →ₗ[R] (Sym2 (Fin k) → R) where
  toFun a :=
    { toFun := symProd a
      map_add' := symProd_add_right a
      map_smul' c b := symProd_smul_right c a b }
  map_add' a b := LinearMap.ext fun c => symProd_add_left a b c
  map_smul' c a := LinearMap.ext fun b => symProd_smul_left c a b

@[simp] theorem symProd_single_single {R : Type*} [CommRing R] {k : ℕ}
    (i j : Fin k) :
    symProd (Pi.single i (1 : R)) (Pi.single j (1 : R)) = Pi.single s(i, j) 1 := by
  funext p
  induction p using Sym2.ind with
  | _ l m =>
    by_cases hlm : l = m <;> by_cases hli : l = i <;> by_cases hlj : l = j <;>
      by_cases hmi : m = i <;> by_cases hmj : m = j <;>
      simp_all [symProd_apply, Pi.single_apply]

@[simp] theorem sym2Mat_col {R : Type*} [CommRing R] {k : ℕ}
    (A : Matrix (Fin k) (Fin k) R) (i j : Fin k) :
    (sym2Mat A).col s(i, j) = symProd (A.col i) (A.col j) := rfl

theorem sym2Mat_mulVec_symProd {R : Type*} [CommRing R] {k : ℕ}
    (A : Matrix (Fin k) (Fin k) R) (a b : Fin k → R) :
    (sym2Mat A).mulVec (symProd a b) = symProd (A.mulVec a) (A.mulVec b) := by
  have h : (symProdBilin (R := R) (k := k)).compr₂ (sym2Mat A).mulVecLin =
      (symProdBilin (R := R) (k := k)).compl₁₂ A.mulVecLin A.mulVecLin := by
    apply (Pi.basisFun R (Fin k)).ext
    intro i
    apply (Pi.basisFun R (Fin k)).ext
    intro j
    simp only [Pi.basisFun_apply, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply]
    simp [symProdBilin, symProd_single_single]
  exact congrArg (fun f => f a b) h

@[simp] theorem sym2Mat_one {R : Type*} [CommRing R] (k : ℕ) :
    sym2Mat (1 : Matrix (Fin k) (Fin k) R) = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro c
  induction c using Sym2.ind with
  | _ i j =>
    simpa only [symProd_single_single, Matrix.one_mulVec] using
      sym2Mat_mulVec_symProd (1 : Matrix (Fin k) (Fin k) R)
        (Pi.single i 1) (Pi.single j 1)

theorem sym2Mat_mul {R : Type*} [CommRing R] {k : ℕ}
    (A B : Matrix (Fin k) (Fin k) R) :
    sym2Mat (A * B) = sym2Mat A * sym2Mat B := by
  apply Matrix.ext_of_mulVec_single
  intro c
  induction c using Sym2.ind with
  | _ i j =>
    simp only [← symProd_single_single, ← Matrix.mulVec_mulVec, sym2Mat_mulVec_symProd]

end KServerConj
end PaperFile031

section PaperFile032
open scoped BigOperators

namespace KServerConj

theorem det_eq_one_of_weight {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (A : Matrix ι ι R) (weight : ι → ℕ)
    (h : ∀ i j, weight j ≤ weight i → A i j = (1 : Matrix ι ι R) i j) :
    A.det = 1 := by
  have ht : A.BlockTriangular weight := by
    intro i j hij
    rw [h i j hij.le]
    exact Matrix.one_apply_ne (fun he => (ne_of_lt hij) (congrArg weight he).symm)
  have hb (n : ℕ) : A.toSquareBlock weight n = 1 := by
    ext i j
    change A i.val j.val = (1 : Matrix { a // weight a = n } { a // weight a = n } R) i j
    simpa [Matrix.one_apply, Subtype.ext_iff] using
      h i.val j.val (le_of_eq (j.property.trans i.property.symm))
  simpa [hb] using ht.det

def symCount {ι : Type*} [DecidableEq ι] (a : ι) : Sym2 ι → ℕ :=
  Sym2.lift ⟨fun i j => (if i = a then 1 else 0) + (if j = a then 1 else 0), by
    intro i j
    exact Nat.add_comm _ _⟩

@[simp] theorem symCount_mk {ι : Type*} [DecidableEq ι] (a i j : ι) :
    symCount a s(i, j) = (if i = a then 1 else 0) + (if j = a then 1 else 0) := rfl

theorem transvection_col {R : Type*} [CommRing R] {k : ℕ}
    (i j l : Fin k) (c : R) :
    (Matrix.transvection i j c).col l =
      Pi.single l 1 + if l = j then c • Pi.single i 1 else 0 := by
  ext r
  by_cases hl : l = j <;> by_cases hr : r = i <;>
    simp_all [Matrix.transvection, Matrix.col, Matrix.single, Matrix.one_apply,
      Pi.single_apply, eq_comm]

theorem sym2Mat_transvection_weight {R : Type*} [CommRing R] {k : ℕ}
    (i j : Fin k) (c : R) (hij : i ≠ j) (p q : Sym2 (Fin k))
    (hw : symCount j q ≤ symCount j p) :
    sym2Mat (Matrix.transvection i j c) p q = (1 : Matrix _ _ R) p q := by
  have hz (z : Sym2 (Fin k)) (hzp : symCount j z < symCount j p) :
      (Pi.single z (1 : R) : Sym2 (Fin k) → R) p = 0 :=
    Pi.single_eq_of_ne (M := fun _ : Sym2 (Fin k) => R)
      (fun he => hzp.ne (congrArg (symCount j) he).symm) (1 : R)
  induction q using Sym2.ind with
  | _ x y =>
    change symProd ((Matrix.transvection i j c).col x)
      ((Matrix.transvection i j c).col y) p = _
    by_cases hx : x = j <;> by_cases hy : y = j
    · have h0 := hz s(i, i) (lt_of_lt_of_le (by simp [hx, hy, hij]) hw)
      have h1 := hz s(i, j) (lt_of_lt_of_le (by simp [hx, hy, hij]) hw)
      simp only [transvection_col, hx, hy, ite_true, symProd_add_left,
        symProd_add_right, symProd_smul_left, symProd_smul_right, symProd_single_single,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        show s(j, i) = s(i, j) from Sym2.eq_swap, h0, h1, mul_zero, add_zero]
      simp [hx, hy, Matrix.one_apply, Pi.single_apply]
    · have h0 := hz s(i, y) (lt_of_lt_of_le (by simp [hx, hy, hij]) hw)
      simp only [transvection_col, hx, hy, ite_true, ite_false, add_zero,
        symProd_add_left, symProd_smul_left, symProd_single_single,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0, mul_zero]
      simp [hx, Matrix.one_apply, Pi.single_apply]
    · have h0 := hz s(x, i) (lt_of_lt_of_le (by simp [hx, hy, hij]) hw)
      simp only [transvection_col, hx, hy, ite_true, ite_false, add_zero,
        symProd_add_right, symProd_smul_right, symProd_single_single,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0, mul_zero]
      simp [hy, Matrix.one_apply, Pi.single_apply]
    · simp [transvection_col, hx, hy, symProd_single_single, Matrix.one_apply, Pi.single_apply]

theorem det_sym2Mat_transvection {R : Type*} [CommRing R] {k : ℕ}
    (i j : Fin k) (c : R) (hij : i ≠ j) :
    (sym2Mat (Matrix.transvection i j c)).det = 1 := by
  exact det_eq_one_of_weight _ (symCount j) (sym2Mat_transvection_weight i j c hij)

theorem sym2_mk_left_injective {ι : Type*} (i : ι) :
    Function.Injective (fun j : ι => s(i, j)) :=
  fun _ _ h => (Sym2.eq_iff.mp h).elim And.right (fun h => h.2.trans h.1)

theorem symCount_eq_zero_of_not_mem_image {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (p : Sym2 ι)
    (hp : p ∉ Finset.univ.image (fun j : ι => s(i, j))) : symCount i p = 0 := by
  induction p using Sym2.ind with
  | _ x y =>
    have hx : x ≠ i := fun h => hp (Finset.mem_image.mpr
      ⟨y, Finset.mem_univ _, congrArg (fun a => s(a, y)) h.symm⟩)
    have hy : y ≠ i := fun h => hp (Finset.mem_image.mpr
      ⟨x, Finset.mem_univ _, (Sym2.eq_swap : s(i, x) = s(x, i)).trans
        (congrArg (fun a => s(x, a)) h.symm)⟩)
    simp [symCount_mk, hx, hy]

theorem sum_symCount {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    ∑ p : Sym2 ι, symCount i p = Fintype.card ι + 1 := by
  have hs : (∑ p ∈ Finset.univ.image (fun j : ι => s(i, j)), symCount i p) =
      ∑ p : Sym2 ι, symCount i p :=
    Finset.sum_subset (Finset.subset_univ _) (fun p _ hp => symCount_eq_zero_of_not_mem_image i p hp)
  rw [← hs, Finset.sum_image (sym2_mk_left_injective i).injOn]
  simp [symCount_mk, Finset.sum_add_distrib]

def symPairMul {ι R : Type*} [CommMonoid R] (d : ι → R) : Sym2 ι → R :=
  Sym2.lift ⟨fun i j => d i * d j, fun i j => mul_comm (d i) (d j)⟩

@[simp] theorem symPairMul_mk {ι R : Type*} [CommMonoid R]
    (d : ι → R) (i j : ι) : symPairMul d s(i, j) = d i * d j := rfl

theorem symPairMul_eq_prod {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid R]
    (d : ι → R) (p : Sym2 ι) :
    symPairMul d p = ∏ i : ι, d i ^ symCount i p := by
  induction p using Sym2.ind with
  | _ x y =>
    simp only [symPairMul_mk, symCount_mk, pow_add, Finset.prod_mul_distrib]
    simp only [Finset.prod_pow_boole, Finset.mem_univ, ite_true]

theorem prod_symPairMul {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid R]
    (d : ι → R) :
    (∏ p : Sym2 ι, symPairMul d p) = (∏ i : ι, d i) ^ (Fintype.card ι + 1) := by
  simp_rw [symPairMul_eq_prod]
  rw [Finset.prod_comm]
  simp_rw [Finset.prod_pow_eq_pow_sum, sum_symCount]
  exact Finset.prod_pow _ _ _

theorem sym2Mat_diagonal {R : Type*} [CommRing R] {k : ℕ} (d : Fin k → R) :
    sym2Mat (Matrix.diagonal d) = Matrix.diagonal (symPairMul d) := by
  have hs (i : Fin k) (a : R) :
      (Pi.single i a : Fin k → R) = a • Pi.single i 1 := by
    simpa only [smul_eq_mul, mul_one] using Pi.single_smul' i a (1 : R)
  apply Matrix.ext_of_mulVec_single
  intro c
  induction c using Sym2.ind with
  | _ i j =>
    simp only [Matrix.mulVec_single_one, sym2Mat_col, Matrix.col_diagonal, symPairMul_mk]
    rw [hs i (d i), hs j (d j), symProd_smul_left, symProd_smul_right,
      symProd_single_single, smul_smul]
    simp only [← Pi.single_smul', smul_eq_mul, mul_one]

theorem det_sym2Mat_diagonal {R : Type*} [CommRing R] {k : ℕ} (d : Fin k → R) :
    (sym2Mat (Matrix.diagonal d)).det = (Matrix.diagonal d).det ^ (k + 1) := by
  simp only [sym2Mat_diagonal, Matrix.det_diagonal, prod_symPairMul, Fintype.card_fin]

theorem det_sym2Mat {K : Type*} [Field K] {k : ℕ} (A : Matrix (Fin k) (Fin k) K) :
    (sym2Mat A).det = A.det ^ (k + 1) := by
  apply Matrix.diagonal_transvection_induction
    (fun M : Matrix (Fin k) (Fin k) K => (sym2Mat M).det = M.det ^ (k + 1)) A
  · exact fun d _ => det_sym2Mat_diagonal d
  · intro t
    simpa [Matrix.TransvectionStruct.toMatrix, t.hij] using
      det_sym2Mat_transvection t.i t.j t.c t.hij
  · intro M N hM hN
    rw [sym2Mat_mul, Matrix.det_mul, hM, hN, Matrix.det_mul, mul_pow]

end KServerConj
end PaperFile032

section PaperFile033
open scoped BigOperators

namespace DetValuationMilestone

theorem det_mul_rectangular_expansion
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (G : Matrix I J R) (C : Matrix J I R) :
    (G * C).det =
      ∑ f : I → J, (∏ i, C (f i) i) * (G.submatrix id f).det := by
  simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
    Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]
  simp only [Finset.prod_mul_distrib, Matrix.submatrix_apply, id_eq,
    mul_comm, mul_assoc]

theorem valuation_prod_nonneg
    {R I : Type*} [CommMonoid R]
    (ν : R → WithTop ℝ) (hone : ν 1 = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (s : Finset I) (f : I → R)
    (hf : ∀ i ∈ s, (0 : WithTop ℝ) ≤ ν (f i)) :
    (0 : WithTop ℝ) ≤ ν (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hone]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, hmul]
    exact add_nonneg (hf i (Finset.mem_insert_self _ _))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem valuation_det_mul_lower_bound
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (C : Matrix J I R) (μ : WithTop ℝ)
    (hG : ∀ f : I → J, μ ≤ ν (G.submatrix id f).det)
    (hC : ∀ j i, (0 : WithTop ℝ) ≤ ν (C j i)) :
    μ ≤ ν (G * C).det := by
  rw [det_mul_rectangular_expansion]
  apply valuation_sum_lower_bound ν hzero hadd
  intro f _
  have hcoeff : (0 : WithTop ℝ) ≤ ν (∏ i, C (f i) i) :=
    valuation_prod_nonneg ν hone hmul Finset.univ (fun i => C (f i) i)
      (fun i _ => hC (f i) i)
  simpa only [hmul, zero_add] using add_le_add hcoeff (hG f)

theorem tupleMinorVal_mono_of_nonneg_coeff
    {I J K R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype K] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (C : Matrix J K R)
    (hC : ∀ j k, (0 : WithTop ℝ) ≤ ν (C j k)) :
    tupleMinorVal ν G ≤ tupleMinorVal ν (G * C) := by
  classical
  refine Finset.le_inf (fun e _ => ?_)
  change tupleMinorVal ν G ≤ ν (G * (C.submatrix id e)).det
  exact valuation_det_mul_lower_bound ν hzero hone hmul hadd G (C.submatrix id e)
    (tupleMinorVal ν G)
    (fun f => Finset.inf_le (f := fun x : I → J => ν (G.submatrix id x).det)
      (Finset.mem_univ f))
    (fun j i => hC j (e i))

theorem embeddingMinorVal_mono_of_nonneg_coeff
    {I J K R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype K] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (C : Matrix J K R)
    (hC : ∀ j k, (0 : WithTop ℝ) ≤ ν (C j k)) :
    embeddingMinorVal ν G ≤ embeddingMinorVal ν (G * C) := by
  simpa only [tupleMinorVal_eq_embeddingMinorVal ν hzero] using
    tupleMinorVal_mono_of_nonneg_coeff ν hzero hone hmul hadd G C hC

theorem embeddingMinorVal_mono_of_column_combinations
    {I J K R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype K] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (F : Matrix I K R)
    (hF : ∀ k, ∃ c : J → R,
      (∀ j, (0 : WithTop ℝ) ≤ ν (c j)) ∧ ∀ i, F i k = ∑ j, G i j * c j) :
    embeddingMinorVal ν G ≤ embeddingMinorVal ν F := by
  classical
  let C : Matrix J K R := Matrix.of fun j k => (hF k).choose j
  have hGC : G * C = F :=
    Matrix.ext (fun i k => by
      simpa only [Matrix.mul_apply, C, Matrix.of_apply] using ((hF k).choose_spec.2 i).symm)
  simpa only [hGC] using
    embeddingMinorVal_mono_of_nonneg_coeff ν hzero hone hmul hadd G C
      (fun j k => (hF k).choose_spec.1 j)

end DetValuationMilestone
end PaperFile033

section PaperFile034
open scoped BigOperators

namespace DetValuationMilestone

theorem valuation_det_nonneg
    {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hneg : ∀ x, ν (-x) = ν x)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (A : Matrix I I R) (hA : ∀ i j, (0 : WithTop ℝ) ≤ ν (A i j)) :
    (0 : WithTop ℝ) ≤ ν A.det := by
  let S : Subring R :=
    { carrier := {x | (0 : WithTop ℝ) ≤ ν x}
      zero_mem' := (show (0 : WithTop ℝ) ≤ ν 0 from
        hzero.symm ▸ (le_top : (0 : WithTop ℝ) ≤ ⊤))
      one_mem' := (show (0 : WithTop ℝ) ≤ ν 1 from
        hone.symm ▸ (le_rfl : (0 : WithTop ℝ) ≤ 0))
      add_mem' := fun hx hy => (le_min hx hy).trans (hadd _ _)
      neg_mem' := fun {x} hx => (show (0 : WithTop ℝ) ≤ ν (-x) from (hneg x).symm ▸ hx)
      mul_mem' := fun {x y} hx hy => (show (0 : WithTop ℝ) ≤ ν (x * y) from
        (hmul x y).symm ▸ add_nonneg hx hy) }
  let B : Matrix I I S := Matrix.of fun i j => ⟨A i j, hA i j⟩
  have hmatrix : S.subtype.mapMatrix B = A := Matrix.ext (fun _ _ => rfl)
  have hmap : (↑(B.det) : R) = A.det :=
    (RingHom.map_det S.subtype B).trans (congrArg Matrix.det hmatrix)
  exact hmap ▸ (show (0 : WithTop ℝ) ≤ ν (↑(B.det) : R) from (B.det).property)

theorem zero_le_tupleMinorVal_of_entries
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hneg : ∀ x, ν (-x) = ν x)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (hG : ∀ i j, (0 : WithTop ℝ) ≤ ν (G i j)) :
    (0 : WithTop ℝ) ≤ tupleMinorVal ν G := by
  classical
  exact Finset.le_inf (fun e _ => valuation_det_nonneg ν hzero hone hneg hmul hadd
    (G.submatrix id e) (fun i j => hG i (e j)))

theorem zero_le_embeddingMinorVal_of_entries
    {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [CommRing R]
    (ν : R → WithTop ℝ) (hzero : ν 0 = ⊤) (hone : ν 1 = 0)
    (hneg : ∀ x, ν (-x) = ν x)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (G : Matrix I J R) (hG : ∀ i j, (0 : WithTop ℝ) ≤ ν (G i j)) :
    (0 : WithTop ℝ) ≤ embeddingMinorVal ν G := by
  simpa only [tupleMinorVal_eq_embeddingMinorVal ν hzero] using
    zero_le_tupleMinorVal_of_entries ν hzero hone hneg hmul hadd G hG

end DetValuationMilestone
end PaperFile034

section PaperFile035
namespace KServerConj

theorem minorVal_le_tuple {F I J : Type*} [Field F] [Fintype I] [DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) (x : I → J) :
    minorVal G ≤ HahnSeries.addVal ℝ F (G.submatrix id x).det := by
  simpa only [minorVal_eq_embeddingMinorVal] using
    DetValuationMilestone.embeddingMinorVal_le_tuple (HahnSeries.addVal ℝ F)
      (AddValuation.map_zero _) G x

theorem exists_minorVal_minimizer {F I J : Type*}
    [Field F] [Fintype I] [DecidableEq I] [Fintype J]
    (G : Matrix I J (HahnSeries ℝ F)) (a : ℝ)
    (ha : minorVal G = (a : WithTop ℝ)) :
    ∃ x : I ↪ J, HahnSeries.addVal ℝ F (G.submatrix id x).det = (a : WithTop ℝ) := by
  classical
  have hh : DetValuationMilestone.embeddingMinorVal (HahnSeries.addVal ℝ F) G =
      (a : WithTop ℝ) := (minorVal_eq_embeddingMinorVal G).symm.trans ha
  unfold DetValuationMilestone.embeddingMinorVal at hh
  obtain ⟨x, _, hx⟩ := (Finset.inf_le_iff (show (a : WithTop ℝ) < ⊤ by simp)).mp hh.le
  exact ⟨x, le_antisymm hx (hh.symm.trans_le (Finset.inf_le (Finset.mem_univ x)))⟩

end KServerConj
end PaperFile035

section PaperFile036
open scoped BigOperators

namespace KServerConj

theorem single_add_one {F : Type*} [Field F] (a b : ℝ) :
    (HahnSeries.single (a + b) (1 : F) : HahnSeries ℝ F) =
      HahnSeries.single a (1 : F) * HahnSeries.single b (1 : F) := by
  simpa only [one_mul] using
    (HahnSeries.single_mul_single (a := a) (b := b) (r := (1 : F)) (s := 1)).symm

theorem single_sum_one {F ι : Type*} [Field F] (s : Finset ι) (a : ι → ℝ) :
    (HahnSeries.single (∑ i ∈ s, a i) (1 : F) : HahnSeries ℝ F) =
      ∏ i ∈ s, HahnSeries.single (a i) (1 : F) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty, HahnSeries.single_zero_one]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, single_add_one, ih]

theorem quadraticMatrix_selected_det {F : Type*} [Field F]
    {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin k → HahnSeries ℝ F) (x : Fin k → M) :
    ((quadraticMatrix q).submatrix id (Sym2.map x)).det =
      HahnSeries.single (∑ c, negPairDist x c) (1 : F) *
        (Matrix.of (fun i j => q (x j) i)).det ^ (k + 1) := by
  rw [quadraticMatrix_submatrix]
  rw [Matrix.det_mul_row (fun c => HahnSeries.single (negPairDist x c) (1 : F))
    (sym2Mat (Matrix.of (fun i j => q (x j) i)))]
  rw [det_sym2Mat, ← single_sum_one]

theorem quadraticMatrix_selected_valuation {F : Type*} [Field F]
    {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (q : M → Fin k → HahnSeries ℝ F) (x : Fin k → M) (δ : ℝ)
    (hD : HahnSeries.addVal ℝ F (Matrix.of (fun i j => q (x j) i)).det =
      (δ : WithTop ℝ)) :
    HahnSeries.addVal ℝ F ((quadraticMatrix q).submatrix id (Sym2.map x)).det =
      ((∑ c, negPairDist x c) + ((k : ℝ) + 1) * δ : ℝ) := by
  rw [quadraticMatrix_selected_det, AddValuation.map_mul, AddValuation.map_pow, hD]
  rw [show HahnSeries.addVal ℝ F
      (HahnSeries.single (∑ c, negPairDist x c) (1 : F)) =
      (((∑ c, negPairDist x c) : ℝ) : WithTop ℝ) from HahnSeries.orderTop_single one_ne_zero]
  simp only [← WithTop.coe_nsmul, ← WithTop.coe_add, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]

theorem negPairDist_nonpos {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (x : Fin k → M) (c : Sym2 (Fin k)) : negPairDist x c ≤ 0 := by
  induction c using Sym2.ind with
  | _ i j => exact neg_nonpos.mpr dist_nonneg

theorem minorVal_quadratic_le {F : Type*} [Field F]
    {k : ℕ} {M : Type*} [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (q : M → Fin k → HahnSeries ℝ F) (x : Fin k → M) (δ : ℝ)
    (hD : HahnSeries.addVal ℝ F (Matrix.of (fun i j => q (x j) i)).det =
      (δ : WithTop ℝ)) :
    minorVal (quadraticMatrix q) ≤ ((((k : ℝ) + 1) * δ : ℝ) : WithTop ℝ) := by
  exact (minorVal_le_tuple (quadraticMatrix q) (Sym2.map x)).trans
    ((quadraticMatrix_selected_valuation q x δ hD).le.trans
      (WithTop.coe_le_coe.mpr (add_le_of_nonpos_left
        (Finset.sum_nonpos fun c _ => negPairDist_nonpos x c))))

end KServerConj
end PaperFile036

section PaperFile037
set_option autoImplicit false
open scoped BigOperators

namespace KServerConj

theorem hahn_valuation_prod {F I : Type*} [Field F]
    (s : Finset I) (f : I → HahnSeries ℝ F) :
    HahnSeries.addVal ℝ F (∏ i ∈ s, f i) =
      ∑ i ∈ s, HahnSeries.addVal ℝ F (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, AddValuation.map_one]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, AddValuation.map_mul, ih]

theorem hahn_valuation_sign_smul {F : Type*} [Field F]
    (ε : ℤˣ) (a : HahnSeries ℝ F) :
    HahnSeries.addVal ℝ F (ε • a) = HahnSeries.addVal ℝ F a := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [Units.smul_def]

theorem weighted_det_valuation_lower {F I : Type*} [Field F]
    [Fintype I] [DecidableEq I] (A : Matrix I I (HahnSeries ℝ F))
    (a : I → I → ℝ)
    (hA : ∀ i j, HahnSeries.addVal ℝ F (A i j) = (a i j : WithTop ℝ))
    (b : ℝ) (hb : ∀ σ : Equiv.Perm I, b ≤ ∑ i, a (σ i) i) :
    (b : WithTop ℝ) ≤ HahnSeries.addVal ℝ F A.det := by
  rw [Matrix.det_apply]
  apply AddValuation.map_le_sum (HahnSeries.addVal ℝ F)
  intro σ _
  rw [hahn_valuation_sign_smul, hahn_valuation_prod]
  simpa only [hA, ← WithTop.coe_sum] using (WithTop.coe_le_coe.mpr (hb σ))

end KServerConj
end PaperFile037

section PaperFile038
open scoped BigOperators

namespace KServerConj

theorem confDist_equiv_nonempty {M : Type*} (X Y : Finset M) (hXY : X.card = Y.card) :
    Nonempty (X ≃ Y) := by
  exact ⟨Fintype.equivOfCardEq (by simpa using hXY)⟩

theorem confDist_costs_bdd {M : Type*} [PseudoMetricSpace M] (X Y : Finset M) :
    BddBelow (Set.range fun e : X ≃ Y => ∑ x : X, dist (x : M) (e x : M)) := by
  exact ⟨0, fun _ ⟨e, he⟩ => he ▸ Finset.sum_nonneg (fun _ _ => dist_nonneg)⟩

theorem confDist_le_matching {M : Type*} [PseudoMetricSpace M]
    (X Y : Finset M) (e : X ≃ Y) :
    confDist X Y ≤ ∑ x : X, dist (x : M) (e x : M) := by
  exact ciInf_le (confDist_costs_bdd X Y) e

theorem confDist_minimizer {M : Type*} [PseudoMetricSpace M]
    (X Y : Finset M) (hXY : X.card = Y.card) :
    ∃ e : X ≃ Y, (∑ x : X, dist (x : M) (e x : M)) = confDist X Y := by
  let : Nonempty (X ≃ Y) := confDist_equiv_nonempty X Y hXY
  exact exists_eq_ciInf_of_finite

theorem confDist_nonneg {M : Type*} [PseudoMetricSpace M]
    (X Y : Finset M) (hXY : X.card = Y.card) : 0 ≤ confDist X Y := by
  obtain ⟨e, he⟩ := confDist_minimizer X Y hXY
  exact he ▸ Finset.sum_nonneg (fun _ _ => dist_nonneg)

theorem confDist_self {M : Type*} [PseudoMetricSpace M] (X : Finset M) :
    confDist X X = 0 := by
  exact le_antisymm (by simpa using confDist_le_matching X X (Equiv.refl X))
    (confDist_nonneg X X rfl)

theorem matching_cost_inverse {M : Type*} [PseudoMetricSpace M]
    (X Y : Finset M) (e : X ≃ Y) :
    (∑ x : X, dist (x : M) (e x : M)) = ∑ y : Y, dist (y : M) (e.symm y : M) := by
  simpa only [Equiv.symm_apply_apply, dist_comm] using
    e.sum_comp (fun y : Y => dist (y : M) (e.symm y : M))

theorem confDist_symm {M : Type*} [PseudoMetricSpace M]
    (X Y : Finset M) (hXY : X.card = Y.card) : confDist X Y = confDist Y X := by
  obtain ⟨e, he⟩ := confDist_minimizer X Y hXY
  obtain ⟨f, hf⟩ := confDist_minimizer Y X hXY.symm
  exact le_antisymm
    ((confDist_le_matching X Y f.symm).trans_eq ((matching_cost_inverse Y X f).symm.trans hf))
    ((confDist_le_matching Y X e.symm).trans_eq ((matching_cost_inverse X Y e).symm.trans he))

theorem confDist_nonneg_all {M : Type*} [PseudoMetricSpace M] (X Y : Finset M) :
    0 ≤ confDist X Y := by
  classical
  by_cases hXY : X.card = Y.card
  · exact confDist_nonneg X Y hXY
  · let : IsEmpty (X ≃ Y) := ⟨fun e => hXY (by simpa using Fintype.card_congr e)⟩
    simp [confDist]

theorem confDist_triangle {M : Type*} [PseudoMetricSpace M]
    (X Y Z : Finset M) (hXY : X.card = Y.card) (hYZ : Y.card = Z.card) :
    confDist X Z ≤ confDist X Y + confDist Y Z := by
  obtain ⟨e, he⟩ := confDist_minimizer X Y hXY
  obtain ⟨f, hf⟩ := confDist_minimizer Y Z hYZ
  calc
    confDist X Z ≤ ∑ x : X, dist (x : M) (f (e x) : M) :=
      confDist_le_matching X Z (e.trans f)
    _ ≤ ∑ x : X, (dist (x : M) (e x : M) + dist (e x : M) (f (e x) : M)) :=
      Finset.sum_le_sum (fun _ _ => dist_triangle _ _ _)
    _ = (∑ x : X, dist (x : M) (e x : M)) + ∑ y : Y, dist (y : M) (f y : M) := by
      rw [Finset.sum_add_distrib, e.sum_comp (fun y : Y => dist (y : M) (f y : M))]
    _ = confDist X Y + confDist Y Z := by rw [he, hf]

end KServerConj
end PaperFile038

section PaperFile039
open scoped BigOperators

namespace KServerConj

noncomputable def imageEquiv {M : Type*} [DecidableEq M] {k : ℕ}
    (x : Fin k → M) (hx : Function.Injective x) :
    Fin k ≃ {y : M // y ∈ Finset.univ.image x} := by
  refine Equiv.ofBijective (fun i => ⟨x i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩) ?_
  constructor
  · exact fun _ _ h => hx (congrArg Subtype.val h)
  · rintro ⟨y, hy⟩
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨i, rfl⟩

@[simp] theorem imageEquiv_apply_val {M : Type*} [DecidableEq M] {k : ℕ}
    (x : Fin k → M) (hx : Function.Injective x) (i : Fin k) :
    (imageEquiv x hx i : M) = x i := rfl

theorem imageEquiv_symm_val {M : Type*} [DecidableEq M] {k : ℕ}
    (x : Fin k → M) (hx : Function.Injective x) (y : {y : M // y ∈ Finset.univ.image x}) :
    x ((imageEquiv x hx).symm y) = (y : M) := by
  exact congrArg Subtype.val ((imageEquiv x hx).apply_symm_apply y)

noncomputable def rowPermOfMatching {M : Type*} [DecidableEq M] {k : ℕ}
    (s x : Fin k → M) (hs : Function.Injective s) (hx : Function.Injective x)
    (e : (Finset.univ.image x : Finset M) ≃ (Finset.univ.image s : Finset M)) :
    Equiv.Perm (Fin k) :=
  ((imageEquiv x hx).trans e).trans (imageEquiv s hs).symm

theorem matching_cost_rowPerm {M : Type*} [PseudoMetricSpace M] [DecidableEq M] {k : ℕ}
    (s x : Fin k → M) (hs : Function.Injective s) (hx : Function.Injective x)
    (e : (Finset.univ.image x : Finset M) ≃ (Finset.univ.image s : Finset M)) :
    (∑ y : (Finset.univ.image x : Finset M), dist (y : M) (e y : M)) =
      ∑ j : Fin k, dist (s (rowPermOfMatching s x hs hx e j)) (x j) := by
  simpa only [rowPermOfMatching, Equiv.trans_apply, imageEquiv_apply_val,
    imageEquiv_symm_val, dist_comm] using
      ((imageEquiv x hx).sum_comp
        (fun y : (Finset.univ.image x : Finset M) => dist (y : M) (e y : M))).symm

noncomputable def matchingOfRowPerm {M : Type*} [DecidableEq M] {k : ℕ}
    (s x : Fin k → M) (hs : Function.Injective s) (hx : Function.Injective x)
    (σ : Equiv.Perm (Fin k)) :
    (Finset.univ.image x : Finset M) ≃ (Finset.univ.image s : Finset M) :=
  (((imageEquiv x hx).symm.trans σ).trans (imageEquiv s hs))

theorem matching_cost_perm {M : Type*} [PseudoMetricSpace M] [DecidableEq M] {k : ℕ}
    (s x : Fin k → M) (hs : Function.Injective s) (hx : Function.Injective x)
    (σ : Equiv.Perm (Fin k)) :
    (∑ y : (Finset.univ.image x : Finset M),
      dist (y : M) (matchingOfRowPerm s x hs hx σ y : M)) =
      ∑ j : Fin k, dist (s (σ j)) (x j) := by
  simpa only [rowPermOfMatching, matchingOfRowPerm, Equiv.trans_apply,
    Equiv.symm_apply_apply] using
      matching_cost_rowPerm s x hs hx (matchingOfRowPerm s x hs hx σ)

theorem confDist_images_min_rowPerm {M : Type*} [PseudoMetricSpace M] [DecidableEq M] {k : ℕ}
    (s x : Fin k → M) (hs : Function.Injective s) (hx : Function.Injective x) :
    ∃ σ : Equiv.Perm (Fin k),
      confDist (Finset.univ.image s) (Finset.univ.image x) =
        (∑ j : Fin k, dist (s (σ j)) (x j)) ∧
      ∀ τ : Equiv.Perm (Fin k),
        (∑ j : Fin k, dist (s (σ j)) (x j)) ≤ ∑ j : Fin k, dist (s (τ j)) (x j) := by
  have hcard : (Finset.univ.image x).card = (Finset.univ.image s).card := by
    simpa using Fintype.card_congr ((imageEquiv x hx).symm.trans (imageEquiv s hs))
  obtain ⟨e, he⟩ := confDist_minimizer (Finset.univ.image x) (Finset.univ.image s) hcard
  let σ := rowPermOfMatching s x hs hx e
  have hcost : (∑ j : Fin k, dist (s (σ j)) (x j)) =
      confDist (Finset.univ.image x) (Finset.univ.image s) :=
    (matching_cost_rowPerm s x hs hx e).symm.trans he
  refine ⟨σ, ?_, ?_⟩
  · exact (confDist_symm _ _ hcard.symm).trans hcost.symm
  · intro τ
    rw [hcost]
    exact (confDist_le_matching _ _ (matchingOfRowPerm s x hs hx τ)).trans_eq
      (matching_cost_perm s x hs hx τ)

end KServerConj
end PaperFile039

section PaperFile040
open scoped BigOperators

namespace KServerConj

theorem isSchedule_zero {M : Type*} (k : ℕ) (C₀ : Finset M) (r : ℕ → M)
    (S : ℕ → Finset M) : IsSchedule k C₀ r 0 S ↔ S 0 = C₀ := by
  exact ⟨And.left, fun h => ⟨h, fun _ hs hst =>
    False.elim (Nat.not_succ_le_zero 0 (hs.trans hst))⟩⟩

theorem IsSchedule.card {M : Type*} {k t : ℕ} {C₀ : Finset M} {r : ℕ → M}
    {S : ℕ → Finset M} (hS : IsSchedule k C₀ r t S) (hC₀ : C₀.card = k)
    (s : ℕ) (hst : s ≤ t) : (S s).card = k := by
  by_cases hs : s = 0
  · simpa only [hs, hS.1] using hC₀
  · exact (hS.2 s (Nat.one_le_iff_ne_zero.mpr hs) hst).1

theorem IsSchedule.mono {M : Type*} {k t u : ℕ} {C₀ : Finset M} {r : ℕ → M}
    {S : ℕ → Finset M} (hS : IsSchedule k C₀ r t S) (hut : u ≤ t) :
    IsSchedule k C₀ r u S := by
  exact ⟨hS.1, fun s hs hsu => hS.2 s hs (hsu.trans hut)⟩

theorem workFn_zero {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (C₀ : Finset M) (r : ℕ → M) (X : Finset M) :
    workFn k C₀ r 0 X = confDist C₀ X := by
  unfold workFn
  simp only [isSchedule_zero, Finset.Icc_eq_empty_of_lt (by decide : (0 : ℕ) < 1),
    Finset.sum_empty, zero_add]
  have hset : {c : ℝ | ∃ S : ℕ → Finset M, S 0 = C₀ ∧ c = confDist (S 0) X} =
      {confDist C₀ X} := by
    ext c
    constructor
    · rintro ⟨S, hS, hc⟩
      simpa only [Set.mem_singleton_iff, hS] using hc
    · intro hc
      exact ⟨fun _ => C₀, rfl, hc⟩
  rw [hset, csInf_singleton]

theorem schedule_cost_nonneg {M : Type*} [PseudoMetricSpace M]
    (S : ℕ → Finset M) (t : ℕ) (X : Finset M) :
    0 ≤ (∑ s ∈ Finset.Icc 1 t, confDist (S (s - 1)) (S s)) + confDist (S t) X := by
  exact add_nonneg (Finset.sum_nonneg (fun _ _ => confDist_nonneg_all _ _))
    (confDist_nonneg_all _ _)

theorem workFn_costs_bdd {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (C₀ : Finset M) (r : ℕ → M) (t : ℕ) (X : Finset M) :
    BddBelow {c : ℝ | ∃ S : ℕ → Finset M, IsSchedule k C₀ r t S ∧
      c = (∑ s ∈ Finset.Icc 1 t, confDist (S (s - 1)) (S s)) + confDist (S t) X} := by
  exact ⟨0, fun _ ⟨S, _, hc⟩ => hc.symm ▸ schedule_cost_nonneg S t X⟩

theorem workFn_le_schedule {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (C₀ : Finset M) (r : ℕ → M) (t : ℕ) (X : Finset M)
    (S : ℕ → Finset M) (hS : IsSchedule k C₀ r t S) :
    workFn k C₀ r t X ≤
      (∑ s ∈ Finset.Icc 1 t, confDist (S (s - 1)) (S s)) + confDist (S t) X := by
  exact csInf_le (workFn_costs_bdd k C₀ r t X) ⟨S, hS, rfl⟩

theorem workFn_costs_nonempty {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (C₀ : Finset M) (r : ℕ → M) (t : ℕ) (X : Finset M)
    (hex : ∃ S : ℕ → Finset M, IsSchedule k C₀ r t S) :
    {c : ℝ | ∃ S : ℕ → Finset M, IsSchedule k C₀ r t S ∧
      c = (∑ s ∈ Finset.Icc 1 t, confDist (S (s - 1)) (S s)) + confDist (S t) X}.Nonempty := by
  exact hex.elim (fun S hS => ⟨_, S, hS, rfl⟩)

theorem workFn_nonneg_of_exists_schedule {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (C₀ : Finset M) (r : ℕ → M) (t : ℕ) (X : Finset M)
    (hex : ∃ S : ℕ → Finset M, IsSchedule k C₀ r t S) : 0 ≤ workFn k C₀ r t X := by
  exact le_csInf (workFn_costs_nonempty k C₀ r t X hex)
    (fun _ ⟨S, _, hc⟩ => hc.symm ▸ schedule_cost_nonneg S t X)

theorem workFn_lipschitz_of_exists_schedule {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) (t : ℕ)
    (hex : ∃ S : ℕ → Finset M, IsSchedule k C₀ r t S)
    (X Y : Finset M) (hX : X.card = k) (hY : Y.card = k) :
    workFn k C₀ r t Y ≤ workFn k C₀ r t X + confDist X Y := by
  apply (sub_le_iff_le_add).mp
  apply le_csInf (workFn_costs_nonempty k C₀ r t X hex)
  rintro c ⟨S, hS, rfl⟩
  have htri := confDist_triangle (S t) X Y
    ((hS.card hC₀ t le_rfl).trans hX.symm) (hX.trans hY.symm)
  have hb := workFn_le_schedule k C₀ r t Y S hS
  linarith

end KServerConj
end PaperFile040

section PaperFile041
set_option autoImplicit false
open scoped BigOperators

namespace KServerConj

noncomputable def permutationSelector {k : ℕ} {V : Type*}
    (v : Fin k → Fin k → V) (σ : Equiv.Perm (Fin k)) (w : V) : ℚ := by
  classical
  exact if w ∈ Finset.univ.image (fun j => v (σ j) j) then 1 else 0

theorem permutationSelector_apply {k : ℕ} {V : Type*}
    (v : Fin k → Fin k → V)
    (hv : Function.Injective (fun p : Fin k × Fin k => v p.1 p.2))
    (σ : Equiv.Perm (Fin k)) (i j : Fin k) :
    permutationSelector v σ (v i j) = if i = σ j then 1 else 0 := by
  classical
  have hmem : v i j ∈ Finset.univ.image (fun a => v (σ a) a) ↔ i = σ j := by
    constructor
    · intro h
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
      have hp := @hv (σ a, a) (i, j) ha
      have hj : a = j := congrArg Prod.snd hp
      simpa only [hj] using (congrArg Prod.fst hp).symm
    · intro h
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, h.symm ▸ rfl⟩
  simp only [permutationSelector, hmem]

noncomputable def weightedPolyMatrix {k : ℕ} {V : Type*}
    (v : Fin k → Fin k → V) (a : Fin k → Fin k → ℝ) :
    Matrix (Fin k) (Fin k) (HahnSeries ℝ (MvPolynomial V ℚ)) :=
  fun i j => HahnSeries.single (a i j) (MvPolynomial.X (v i j))

theorem weightedPolyMatrix_specialize {k : ℕ} {V : Type*}
    (v : Fin k → Fin k → V)
    (hv : Function.Injective (fun p : Fin k × Fin k => v p.1 p.2))
    (a : Fin k → Fin k → ℝ) (σ : Equiv.Perm (Fin k)) :
    (hahnCoeffRingMap (MvPolynomial.eval (permutationSelector v σ))).mapMatrix
        (weightedPolyMatrix v a) =
      (Matrix.diagonal (fun j => HahnSeries.single (a (σ j) j) (1 : ℚ))).submatrix σ.symm id := by
  classical
  funext i j
  change hahnCoeffRingMap (MvPolynomial.eval (permutationSelector v σ))
      (HahnSeries.single (a i j) (MvPolynomial.X (v i j))) = _
  rw [hahnCoeffRingMap_single, MvPolynomial.eval_X, permutationSelector_apply v hv σ]
  by_cases h : i = σ j
  · subst i
    simp [Matrix.submatrix_apply]
  · have h' : σ.symm i ≠ j := fun hh =>
      h ((σ.apply_symm_apply i).symm.trans (congrArg σ hh))
    simp [Matrix.submatrix_apply, h, h']

theorem weightedPolyMatrix_specialize_det {k : ℕ} {V : Type*}
    (v : Fin k → Fin k → V)
    (hv : Function.Injective (fun p : Fin k × Fin k => v p.1 p.2))
    (a : Fin k → Fin k → ℝ) (σ : Equiv.Perm (Fin k)) :
    hahnCoeffRingMap (MvPolynomial.eval (permutationSelector v σ))
        (weightedPolyMatrix v a).det =
      (σ.sign : HahnSeries ℝ ℚ) * HahnSeries.single (∑ j, a (σ j) j) (1 : ℚ) := by
  rw [RingHom.map_det, weightedPolyMatrix_specialize v hv a σ,
    Matrix.det_permute, Matrix.det_diagonal]
  rw [show Equiv.Perm.sign σ.symm = σ.sign from Equiv.Perm.sign_inv σ, ← single_sum_one]

theorem weightedPolyMatrix_coeff_ne_zero {k : ℕ} {V : Type*}
    (v : Fin k → Fin k → V)
    (hv : Function.Injective (fun p : Fin k × Fin k => v p.1 p.2))
    (a : Fin k → Fin k → ℝ) (σ : Equiv.Perm (Fin k)) :
    (weightedPolyMatrix v a).det.coeff (∑ j, a (σ j) j) ≠ 0 := by
  intro hz
  have h := congrArg (fun f : HahnSeries ℝ ℚ => f.coeff (∑ j, a (σ j) j))
    (weightedPolyMatrix_specialize_det v hv a σ)
  rw [hahnCoeffRingMap_coeff, hz, map_zero] at h
  rcases Int.units_eq_one_or σ.sign with hs | hs <;> simp [hs] at h

theorem weighted_generic_det_valuation {k : ℕ} {V : Type*}
    (v : Fin k → Fin k → V)
    (hv : Function.Injective (fun p : Fin k × Fin k => v p.1 p.2))
    (a : Fin k → Fin k → ℝ) (σ : Equiv.Perm (Fin k))
    (hmin : ∀ τ : Equiv.Perm (Fin k), (∑ j, a (σ j) j) ≤ ∑ j, a (τ j) j) :
    HahnSeries.addVal ℝ (FractionRing (MvPolynomial V ℚ))
      ((hahnCoeffRingMap (algebraMap (MvPolynomial V ℚ) (FractionRing (MvPolynomial V ℚ)))).mapMatrix
        (weightedPolyMatrix v a)).det = ((∑ j, a (σ j) j : ℝ) : WithTop ℝ) := by
  let φ : MvPolynomial V ℚ →+* FractionRing (MvPolynomial V ℚ) := algebraMap _ _
  let A := (hahnCoeffRingMap φ).mapMatrix (weightedPolyMatrix v a)
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  have hA : ∀ i j, HahnSeries.addVal ℝ (FractionRing (MvPolynomial V ℚ)) (A i j) =
      (a i j : WithTop ℝ) := by
    intro i j
    change HahnSeries.addVal ℝ (FractionRing (MvPolynomial V ℚ))
      (hahnCoeffRingMap φ (HahnSeries.single (a i j) (MvPolynomial.X (v i j)))) = _
    simpa only [hahnCoeffRingMap_single, HahnSeries.addVal_apply] using
      (HahnSeries.orderTop_single
        ((map_ne_zero_iff φ hφ).mpr (MvPolynomial.X_ne_zero (v i j))))
  change HahnSeries.addVal ℝ (FractionRing (MvPolynomial V ℚ)) A.det = _
  apply le_antisymm
  · change A.det.orderTop ≤ _
    apply HahnSeries.orderTop_le_of_coeff_ne_zero
    dsimp only [A]
    rw [← RingHom.map_det, hahnCoeffRingMap_coeff]
    exact (map_ne_zero_iff φ hφ).mpr (weightedPolyMatrix_coeff_ne_zero v hv a σ)
  · exact weighted_det_valuation_lower A a hA _ hmin

theorem initCols_colDet_valuation_of_minimizing_perm {k : ℕ} {M : Type*}
    [PseudoMetricSpace M] (s x : Fin k → M) (hx : Function.Injective x)
    (σ : Equiv.Perm (Fin k))
    (hmin : ∀ τ : Equiv.Perm (Fin k),
      (∑ j, dist (s (σ j)) (x j)) ≤ ∑ j, dist (s (τ j)) (x j)) :
    nu (colDet (initCols s) x) = ((∑ j, dist (s (σ j)) (x j) : ℝ) : WithTop ℝ) := by
  classical
  let v : Fin k → Fin k → Var k M := fun i j => Sum.inl (i, x j)
  let a : Fin k → Fin k → ℝ := fun i j => dist (s i) (x j)
  have hv : Function.Injective (fun p : Fin k × Fin k => v p.1 p.2) := by
    intro i j hij
    have hp : (i.1, x i.2) = (j.1, x j.2) := Sum.inl.inj hij
    exact Prod.ext (congrArg (fun p : Fin k × M => p.1) hp)
      (hx (congrArg (fun p : Fin k × M => p.2) hp))
  have hmat : (hahnCoeffRingMap (algebraMap (MvPolynomial (Var k M) ℚ) (F k M))).mapMatrix
      (weightedPolyMatrix v a) = Matrix.of (fun i j => initCols s (x j) i) := by
    funext i j
    change hahnCoeffRingMap (algebraMap (MvPolynomial (Var k M) ℚ) (F k M))
      (HahnSeries.single (a i j) (MvPolynomial.X (v i j))) = initCols s (x j) i
    rw [hahnCoeffRingMap_single]
    simp only [initCols, coef, zp, varF, HahnSeries.C_apply,
      HahnSeries.single_mul_single, zero_add, mul_one, a, v]
  have h := weighted_generic_det_valuation v hv a σ hmin
  rw [hmat] at h
  exact h

theorem initCols_self_colDet_valuation {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    (s : Fin k → M) (hs : Function.Injective s) :
    nu (colDet (initCols s) s) = 0 := by
  have h := initCols_colDet_valuation_of_minimizing_perm s s hs (Equiv.refl (Fin k))
    (by
      intro τ
      simp only [Equiv.refl_apply, dist_self, Finset.sum_const_zero]
      exact Finset.sum_nonneg (fun _ _ => dist_nonneg))
  simpa only [Equiv.refl_apply, dist_self, Finset.sum_const_zero, WithTop.coe_zero] using h

theorem initCols_workFn_zero {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    [DecidableEq M] (s x : Fin k → M) (hs : Function.Injective s)
    (hx : Function.Injective x) (r : ℕ → M) :
    nu (colDet (initCols s) x) =
      (workFn k (Finset.univ.image s) r 0 (Finset.univ.image x) : WithTop ℝ) := by
  obtain ⟨σ, hdist, hmin⟩ := confDist_images_min_rowPerm s x hs hx
  rw [workFn_zero, hdist]
  exact initCols_colDet_valuation_of_minimizing_perm s x hx σ hmin

end KServerConj
end PaperFile041

section PaperFile042
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
end PaperFile042

section PaperFile043
open scoped BigOperators

namespace KServerConj

noncomputable def updateConfigEquiv {M : Type*} [DecidableEq M]
    (X : Finset M) (x : M) (hx : x ∈ X) (r : M) (hr : r ∉ X) :
    X ≃ {z : M // z ∈ insert r (X.erase x)} := by
  refine (Equiv.swap x r).subtypeEquiv ?_
  intro z
  have hxr : x ≠ r := fun h => hr (h ▸ hx)
  by_cases hzx : z = x <;> by_cases hzr : z = r <;>
    simp_all [Equiv.swap_apply_def]

theorem card_insert_erase_admissible {M : Type*} [DecidableEq M]
    (X : Finset M) (x : M) (hx : x ∈ X) (r : M) (hvalid : r ∉ X ∨ x = r) :
    (insert r (X.erase x)).card = X.card := by
  rcases hvalid with hr | rfl
  · simpa using (Fintype.card_congr (updateConfigEquiv X x hx r hr)).symm
  · rw [Finset.insert_erase hx]

theorem updateConfigEquiv_apply {M : Type*} [DecidableEq M]
    (X : Finset M) (x : M) (hx : x ∈ X) (r : M) (hr : r ∉ X) (y : X) :
    (updateConfigEquiv X x hx r hr y : M) = Equiv.swap x r (y : M) := rfl

theorem updateConfigEquiv_cost {M : Type*} [PseudoMetricSpace M] [DecidableEq M]
    (X : Finset M) (x : M) (hx : x ∈ X) (r : M) (hr : r ∉ X) :
    (∑ y : X, dist (y : M) (updateConfigEquiv X x hx r hr y : M)) = dist x r := by
  classical
  simp only [updateConfigEquiv_apply]
  rw [Finset.sum_eq_single (⟨x, hx⟩ : X)]
  · simp
  · intro y _hy hy
    have hyx : (y : M) ≠ x := fun h => hy (Subtype.ext h)
    have hyr : (y : M) ≠ r := fun h => hr (h ▸ y.property)
    simp [Equiv.swap_apply_def, hyx, hyr]
  · simp

theorem confDist_insert_erase_le {M : Type*} [PseudoMetricSpace M] [DecidableEq M]
    (X : Finset M) (x : M) (hx : x ∈ X) (r : M) (hvalid : r ∉ X ∨ x = r) :
    confDist (insert r (X.erase x)) X ≤ dist r x := by
  rcases hvalid with hr | rfl
  · rw [confDist_symm _ X (card_insert_erase_admissible X x hx r (Or.inl hr))]
    exact (confDist_le_matching X _ (updateConfigEquiv X x hx r hr)).trans_eq
      ((updateConfigEquiv_cost X x hx r hr).trans (dist_comm x r))
  · simpa only [Finset.insert_erase hx, confDist_self, dist_self] using (le_refl (0 : ℝ))

end KServerConj
end PaperFile043

section PaperFile044
namespace KServerConj

theorem exists_serving_config {M : Type*} [DecidableEq M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : M) :
    ∃ Y : Finset M, Y.card = k ∧ r ∈ Y := by
  by_cases hr : r ∈ C₀
  · exact ⟨C₀, hC₀, hr⟩
  · obtain ⟨x, hx⟩ := Finset.card_pos.mp (hC₀.symm ▸ hk)
    exact ⟨insert r (C₀.erase x),
      (card_insert_erase_admissible C₀ x hx r (Or.inl hr)).trans hC₀,
      Finset.mem_insert_self _ _⟩

theorem exists_schedule {M : Type*}
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) (t : ℕ) :
    ∃ S : ℕ → Finset M, IsSchedule k C₀ r t S := by
  classical
  refine ⟨fun s => if s = 0 then C₀ else (exists_serving_config k hk C₀ hC₀ (r s)).choose,
    by simp, ?_⟩
  intro s hs _hst
  simpa only [if_neg (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hs))] using
    (exists_serving_config k hk C₀ hC₀ (r s)).choose_spec

theorem workFn_nonneg {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k)
    (r : ℕ → M) (t : ℕ) (X : Finset M) : 0 ≤ workFn k C₀ r t X := by
  exact workFn_nonneg_of_exists_schedule k C₀ r t X (exists_schedule k hk C₀ hC₀ r t)

theorem workFn_lipschitz {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) (t : ℕ)
    (X Y : Finset M) (hX : X.card = k) (hY : Y.card = k) :
    workFn k C₀ r t Y ≤ workFn k C₀ r t X + confDist X Y := by
  exact workFn_lipschitz_of_exists_schedule k C₀ hC₀ r t
    (exists_schedule k hk C₀ hC₀ r t) X Y hX hY

end KServerConj
end PaperFile044

section PaperFile045
open scoped BigOperators

namespace KServerConj

theorem IsSchedule.append_terminal {M : Type*} {k t : ℕ} {C₀ : Finset M} {r : ℕ → M}
    {S : ℕ → Finset M} (hS : IsSchedule k C₀ r t S)
    (X : Finset M) (hX : X.card = k) (hr : r (t + 1) ∈ X) :
    IsSchedule k C₀ r (t + 1) (Function.update S (t + 1) X) := by
  refine ⟨?_, ?_⟩
  · simpa only [Function.update_of_ne (by omega : 0 ≠ t + 1)] using hS.1
  · intro s hs hst
    by_cases he : s = t + 1
    · simpa only [he, Function.update_self] using And.intro hX hr
    · simpa only [Function.update_of_ne he] using hS.2 s hs (by omega)

theorem schedule_prefix_update_last {M : Type*} [PseudoMetricSpace M]
    (S : ℕ → Finset M) (t : ℕ) (X : Finset M) :
    (∑ s ∈ Finset.Icc 1 t,
      confDist (Function.update S (t + 1) X (s - 1)) (Function.update S (t + 1) X s)) =
      ∑ s ∈ Finset.Icc 1 t, confDist (S (s - 1)) (S s) := by
  apply Finset.sum_congr rfl
  intro s hs
  have hst : s ≤ t := (Finset.mem_Icc.mp hs).2
  simp only [Function.update_of_ne (by omega : s - 1 ≠ t + 1),
    Function.update_of_ne (by omega : s ≠ t + 1)]

theorem schedule_cost_update_last {M : Type*} [PseudoMetricSpace M]
    (S : ℕ → Finset M) (t : ℕ) (X : Finset M) :
    (∑ s ∈ Finset.Icc 1 (t + 1),
      confDist (Function.update S (t + 1) X (s - 1)) (Function.update S (t + 1) X s)) +
        confDist (Function.update S (t + 1) X (t + 1)) X =
      (∑ s ∈ Finset.Icc 1 t, confDist (S (s - 1)) (S s)) + confDist (S t) X := by
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ t + 1), schedule_prefix_update_last]
  simp only [Nat.add_sub_cancel, Function.update_self,
    Function.update_of_ne (by omega : t ≠ t + 1), confDist_self, add_zero]

end KServerConj
end PaperFile045

section PaperFile046
open scoped BigOperators

namespace KServerConj

theorem workFn_mono_succ {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M)
    (t : ℕ) (X : Finset M) (hX : X.card = k) :
    workFn k C₀ r t X ≤ workFn k C₀ r (t + 1) X := by
  apply le_csInf (workFn_costs_nonempty k C₀ r (t + 1) X
    (exists_schedule k hk C₀ hC₀ r (t + 1)))
  rintro c ⟨S, hS, rfl⟩
  have h₀ := hS.card hC₀ t (Nat.le_succ t)
  have h₁ := hS.card hC₀ (t + 1) le_rfl
  have hb := workFn_le_schedule k C₀ r t X S (hS.mono (Nat.le_succ t))
  have htri := confDist_triangle (S t) (S (t + 1)) X
    (h₀.trans h₁.symm) (h₁.trans hX.symm)
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ t + 1)]
  simp only [Nat.add_sub_cancel]
  linarith

theorem workFn_covered_succ {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M)
    (t : ℕ) (X : Finset M) (hX : X.card = k) (hr : r (t + 1) ∈ X) :
    workFn k C₀ r (t + 1) X = workFn k C₀ r t X := by
  apply le_antisymm ?_ (workFn_mono_succ k hk C₀ hC₀ r t X hX)
  apply le_csInf (workFn_costs_nonempty k C₀ r t X (exists_schedule k hk C₀ hC₀ r t))
  rintro c ⟨S, hS, rfl⟩
  have hb := workFn_le_schedule k C₀ r (t + 1) X (Function.update S (t + 1) X)
    (hS.append_terminal X hX hr)
  simpa only [schedule_cost_update_last] using hb

theorem workFn_mono {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M)
    (t : ℕ) (ht : 1 ≤ t) (X : Finset M) (hX : X.card = k) :
    workFn k C₀ r (t - 1) X ≤ workFn k C₀ r t X := by
  simpa only [Nat.sub_add_cancel ht] using workFn_mono_succ k hk C₀ hC₀ r (t - 1) X hX

theorem workFn_covered {M : Type*} [PseudoMetricSpace M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M)
    (t : ℕ) (ht : 1 ≤ t) (X : Finset M) (hX : X.card = k) (hr : r t ∈ X) :
    workFn k C₀ r t X = workFn k C₀ r (t - 1) X := by
  simpa only [Nat.sub_add_cancel ht] using workFn_covered_succ k hk C₀ hC₀ r (t - 1) X hX
    (by simpa only [Nat.sub_add_cancel ht] using hr)

theorem workFn_rec_le {M : Type*} [PseudoMetricSpace M] [DecidableEq M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M)
    (t : ℕ) (ht : 1 ≤ t) (X : Finset M) (hX : X.card = k)
    (x : M) (hx : x ∈ X) (hvalid : r t ∉ X ∨ x = r t) :
    workFn k C₀ r t X ≤
      workFn k C₀ r (t - 1) (insert (r t) (X.erase x)) + dist (r t) x := by
  have hY := (card_insert_erase_admissible X x hx (r t) hvalid).trans hX
  have hcover := workFn_covered k hk C₀ hC₀ r t ht (insert (r t) (X.erase x)) hY
    (Finset.mem_insert_self _ _)
  have hle := workFn_lipschitz k hk C₀ hC₀ r t (insert (r t) (X.erase x)) X hY hX
  rw [hcover] at hle
  exact hle.trans (add_le_add le_rfl (confDist_insert_erase_le X x hx (r t) hvalid))

end KServerConj
end PaperFile046

section PaperFile047
open scoped BigOperators

namespace KServerConj

theorem matching_replacement_cost {M : Type*} [PseudoMetricSpace M] [DecidableEq M]
    (X Y : Finset M) (r : M) (hrY : r ∈ Y) (hrX : r ∉ X) (e : Y ≃ X) :
    let ry : Y := ⟨r, hrY⟩
    let x : M := (e ry : M)
    let f := updateConfigEquiv X x (e ry).property r hrX
    (∑ y : Y, dist (y : M) (f (e y) : M)) + dist r x =
      ∑ y : Y, dist (y : M) (e y : M) := by
  let ry : Y := ⟨r, hrY⟩
  let x : M := (e ry : M)
  let f := updateConfigEquiv X x (e ry).property r hrX
  have hcost (y : Y) :
      dist (y : M) (f (e y) : M) + (if y = ry then dist r x else 0) =
        dist (y : M) (e y : M) := by
    by_cases hy : y = ry
    · simp [hy, ry, x, f, updateConfigEquiv_apply]
    · have hyx : (e y : M) ≠ x := fun h => hy (e.injective (Subtype.ext h))
      have hyr : (e y : M) ≠ r := fun h => hrX (h ▸ (e y).property)
      simp [hy, f, updateConfigEquiv_apply, Equiv.swap_apply_def, hyx, hyr]
  simpa only [Finset.sum_add_distrib, Fintype.sum_ite_eq'] using
    (show (∑ y : Y, (dist (y : M) (f (e y) : M) + if y = ry then dist r x else 0)) =
      ∑ y : Y, dist (y : M) (e y : M) from
        Finset.sum_congr rfl (fun y _ => hcost y))

theorem confDist_exchange_missing {M : Type*} [PseudoMetricSpace M] [DecidableEq M]
    (X Y : Finset M) (hYX : Y.card = X.card) (r : M) (hrY : r ∈ Y) (hrX : r ∉ X) :
    ∃ x ∈ X, confDist Y (insert r (X.erase x)) + dist r x ≤ confDist Y X := by
  obtain ⟨e, he⟩ := confDist_minimizer Y X hYX
  let ry : Y := ⟨r, hrY⟩
  let x : M := (e ry : M)
  let f := updateConfigEquiv X x (e ry).property r hrX
  exact ⟨x, (e ry).property,
    (add_le_add (confDist_le_matching Y _ (e.trans f)) (le_refl (dist r x))).trans_eq
      ((matching_replacement_cost X Y r hrY hrX e).trans he)⟩

theorem confDist_served_exchange {M : Type*} [PseudoMetricSpace M] [DecidableEq M]
    (X Y : Finset M) (hYX : Y.card = X.card) (r : M) (hrY : r ∈ Y) :
    ∃ x ∈ X, (r ∉ X ∨ x = r) ∧
      confDist Y (insert r (X.erase x)) + dist r x ≤ confDist Y X := by
  by_cases hrX : r ∈ X
  · exact ⟨r, hrX, Or.inr rfl, by
      simpa only [Finset.insert_erase hrX, dist_self, add_zero] using
        (le_refl (confDist Y X))⟩
  · exact (confDist_exchange_missing X Y hYX r hrY hrX).elim
      (fun x ⟨hx, hcost⟩ => ⟨x, hx, Or.inl hrX, hcost⟩)

end KServerConj
end PaperFile047

section PaperFile048
open scoped BigOperators

namespace KServerConj

theorem schedule_to_replacement_cost {M : Type*} [PseudoMetricSpace M] [DecidableEq M]
    (k : ℕ) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M)
    (t : ℕ) (ht : 1 ≤ t) (X : Finset M) (hX : X.card = k)
    (S : ℕ → Finset M) (hS : IsSchedule k C₀ r t S) :
    ∃ x ∈ X, (r t ∉ X ∨ x = r t) ∧
      workFn k C₀ r (t - 1) (insert (r t) (X.erase x)) + dist (r t) x ≤
        (∑ s ∈ Finset.Icc 1 t, confDist (S (s - 1)) (S s)) + confDist (S t) X := by
  have hlast := hS.2 t ht le_rfl
  obtain ⟨x, hx, hvalid, hexch⟩ := confDist_served_exchange X (S t)
    (hlast.1.trans hX.symm) (r t) hlast.2
  have hY := (card_insert_erase_admissible X x hx (r t) hvalid).trans hX
  have hprev := hS.card hC₀ (t - 1) (Nat.sub_le t 1)
  have hb := workFn_le_schedule k C₀ r (t - 1) (insert (r t) (X.erase x)) S
    (hS.mono (Nat.sub_le t 1))
  have htri := confDist_triangle (S (t - 1)) (S t) (insert (r t) (X.erase x))
    (hprev.trans hlast.1.symm) (hlast.1.trans hY.symm)
  have hsum : (∑ s ∈ Finset.Icc 1 t, confDist (S (s - 1)) (S s)) =
      (∑ s ∈ Finset.Icc 1 (t - 1), confDist (S (s - 1)) (S s)) +
        confDist (S (t - 1)) (S t) := by
    simpa only [Nat.sub_add_cancel ht] using
      Finset.sum_Icc_succ_top (by omega : 1 ≤ (t - 1) + 1)
        (fun s => confDist (S (s - 1)) (S s))
  exact ⟨x, hx, hvalid, by rw [hsum]; linarith⟩

theorem admissible_point_nonempty {M : Type*} [DecidableEq M]
    (k : ℕ) (hk : 1 ≤ k) (X : Finset M) (hX : X.card = k) (r : M) :
    Nonempty {x : X // r ∉ X ∨ (x : M) = r} := by
  by_cases hr : r ∈ X
  · exact ⟨⟨⟨r, hr⟩, Or.inr rfl⟩⟩
  · exact (Finset.card_pos.mp (hX.symm ▸ hk)).elim
      (fun x hx => ⟨⟨⟨x, hx⟩, Or.inl hr⟩⟩)

theorem workFn_rec_ge {M : Type*} [PseudoMetricSpace M] [DecidableEq M]
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M)
    (t : ℕ) (ht : 1 ≤ t) (X : Finset M) (hX : X.card = k) :
    ∃ x ∈ X, (r t ∉ X ∨ x = r t) ∧
      workFn k C₀ r (t - 1) (insert (r t) (X.erase x)) + dist (r t) x ≤
        workFn k C₀ r t X := by
  let A := {x : X // r t ∉ X ∨ (x : M) = r t}
  let f (a : A) : ℝ :=
    workFn k C₀ r (t - 1) (insert (r t) (X.erase (a.1 : M))) + dist (r t) (a.1 : M)
  let : Nonempty A := admissible_point_nonempty k hk X hX (r t)
  have hfb : BddBelow (Set.range f) :=
    ⟨0, fun _ ⟨a, ha⟩ => ha ▸ add_nonneg
      (workFn_nonneg k hk C₀ hC₀ r (t - 1) (insert (r t) (X.erase (a.1 : M)))) dist_nonneg⟩
  have hmin : (⨅ a : A, f a) ≤ workFn k C₀ r t X := by
    apply le_csInf (workFn_costs_nonempty k C₀ r t X (exists_schedule k hk C₀ hC₀ r t))
    rintro c ⟨S, hS, rfl⟩
    obtain ⟨x, hx, hvalid, hcost⟩ := schedule_to_replacement_cost k C₀ hC₀ r t ht X hX S hS
    exact (ciInf_le hfb (⟨⟨x, hx⟩, hvalid⟩ : A)).trans hcost
  obtain ⟨a, ha⟩ : ∃ a : A, f a = ⨅ a : A, f a := exists_eq_ciInf_of_finite
  exact ⟨(a.1 : M), a.1.property, a.property, ha.trans_le hmin⟩

end KServerConj
end PaperFile048

section PaperFile049
set_option autoImplicit false

namespace KServerConj

theorem eq_2 {M : Type*} [PseudoMetricSpace M] [DecidableEq M] (k : ℕ) (hk : 1 ≤ k)
    (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) :
    (∀ X : Finset M, X.card = k → workFn k C₀ r 0 X = confDist C₀ X) ∧
    ∀ t : ℕ, 1 ≤ t → ∀ X : Finset M, X.card = k →
      (∀ x ∈ X, (r t ∉ X ∨ x = r t) →
        workFn k C₀ r t X ≤ workFn k C₀ r (t - 1) (insert (r t) (X.erase x)) + dist (r t) x) ∧
      ∃ x ∈ X, (r t ∉ X ∨ x = r t) ∧
        workFn k C₀ r t X = workFn k C₀ r (t - 1) (insert (r t) (X.erase x)) + dist (r t) x := by
  exact ⟨fun X _ => workFn_zero k C₀ r X, fun t ht X hX =>
    ⟨fun x hx hvalid => workFn_rec_le k hk C₀ hC₀ r t ht X hX x hx hvalid,
      (workFn_rec_ge k hk C₀ hC₀ r t ht X hX).elim
        (fun x ⟨hx, hvalid, hge⟩ => ⟨x, hx, hvalid,
          le_antisymm (workFn_rec_le k hk C₀ hC₀ r t ht X hX x hx hvalid) hge⟩)⟩⟩

end KServerConj
end PaperFile049

section PaperFile050
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
end PaperFile050

section PaperFile051
set_option autoImplicit false
open scoped BigOperators

namespace KServerConj

structure AlgebraicState {k : ℕ} {M : Type*} [PseudoMetricSpace M] [DecidableEq M]
    (s : Fin k → M) (r : ℕ → M) (t : ℕ) where
  q : M → Fin k → K k M
  represents : ∀ x : Fin k → M, Function.Injective x →
    nu (colDet q x) =
      (workFn k (Finset.univ.image s) r t (Finset.univ.image x) : WithTop ℝ)
  fresh : ∀ u : ℕ, t < u → ∀ x : Fin k → M,
    FreeOf (Set.range fun y : M => (Sum.inr (u, y) : Var k M)) (colDet q x)

noncomputable def initialAlgebraicState {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    [DecidableEq M] (s : Fin k → M) (hs : Function.Injective s) (r : ℕ → M) :
    AlgebraicState s r 0 where
  q := initCols s
  represents := fun x hx => initCols_workFn_zero s x hs hx r
  fresh := by
    intro u _ x
    apply initCols_colDet_freeOf
    intro i y hy
    obtain ⟨z, hz⟩ := hy
    cases hz

noncomputable def AlgebraicState.normalized {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    [DecidableEq M] {s : Fin k → M} {r : ℕ → M} {t : ℕ}
    (st : AlgebraicState s r t) (B : Matrix (Fin k) (Fin k) (K k M)) (hB : B.det = 1) :
    AlgebraicState s r t where
  q := fun y => B.mulVec (st.q y)
  represents := fun x hx =>
    (congrArg nu (colDet_normalize_eq B hB st.q x)).trans (st.represents x hx)
  fresh := fun u hu x => (colDet_normalize_eq B hB st.q x).symm ▸ st.fresh u hu x

noncomputable def AlgebraicState.advance {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    [Fintype M] [DecidableEq M] {s : Fin (n + 2) → M} {r : ℕ → M} {t : ℕ}
    (st : AlgebraicState s r t) (hs : Function.Injective s)
    (B : Matrix (Fin (n + 2)) (Fin (n + 2)) (K (n + 2) M))
    (hB : B.det = 1) (hr : B.mulVec (st.q (r (t + 1))) = Pi.single 0 1) :
    AlgebraicState s r (t + 1) where
  q := rowReplace (st.normalized B hB).q (freshRow r (t + 1))
  represents := by
    intro x hx
    exact fresh_request_representation_admissible (Nat.succ_le_succ (Nat.zero_le n))
      s hs r (t + 1) (Nat.succ_le_succ (Nat.zero_le t)) (st.normalized B hB).q
      (fun y hy => by simpa only [Nat.add_sub_cancel] using
        (st.normalized B hB).represents y hy)
      ((st.normalized B hB).fresh (t + 1) (Nat.lt_succ_self t)) hr x hx
  fresh := by
    intro u hu x
    exact fresh_rowReplace_det_freeOf
      (Set.range fun y : M => (Sum.inr (u, y) : Var (n + 2) M))
      (st.normalized B hB).q (r (t + 1)) (t + 1) hr
      ((st.normalized B hB).fresh u ((Nat.lt_succ_self t).trans hu))
      (fun y hy => by
        obtain ⟨z, hz⟩ := hy
        exact (Nat.ne_of_lt hu) (congrArg (fun p : ℕ × M => p.1) (Sum.inr.inj hz)).symm) x

theorem exists_injective_tuple_covering {k : ℕ} {M : Type*}
    (s : Fin k → M) (hs : Function.Injective s) (i₀ : Fin k) (y : M) :
    ∃ x : Fin k → M, Function.Injective x ∧ ∃ i, x i = y := by
  classical
  by_cases hy : y ∈ Set.range s
  · exact ⟨s, hs, hy⟩
  · exact ⟨Function.update s i₀ y, update_injective_of_not_mem_range s hs y hy i₀,
      i₀, Function.update_self _ _ _⟩

theorem AlgebraicState.det_ne_zero {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    [DecidableEq M] {s : Fin k → M} {r : ℕ → M} {t : ℕ}
    (st : AlgebraicState s r t) (x : Fin k → M) (hx : Function.Injective x) :
    colDet st.q x ≠ 0 := by
  exact (nu_eq_top_iff _).not.mp
    (ne_of_eq_of_ne (st.represents x hx) WithTop.coe_ne_top)

theorem AlgebraicState.column_ne_zero {k : ℕ} {M : Type*} [PseudoMetricSpace M]
    [DecidableEq M] {s : Fin k → M} {r : ℕ → M} {t : ℕ}
    (st : AlgebraicState s r t) (hs : Function.Injective s) (i₀ : Fin k) (y : M) :
    st.q y ≠ 0 := by
  obtain ⟨x, hx, i, hi⟩ := exists_injective_tuple_covering s hs i₀ y
  intro hy
  apply st.det_ne_zero x hx
  unfold colDet
  exact Matrix.det_eq_zero_of_column_eq_zero i (fun j => by
    change st.q (x i) j = 0
    rw [hi]
    exact congrFun hy j)

theorem AlgebraicState.exists_normalizer {n : ℕ} {M : Type*} [PseudoMetricSpace M]
    [DecidableEq M] {s : Fin (n + 2) → M} {r : ℕ → M} {t : ℕ}
    (st : AlgebraicState s r t) (hs : Function.Injective s) :
    ∃ B : Matrix (Fin (n + 2)) (Fin (n + 2)) (K (n + 2) M),
      B.det = 1 ∧ B.mulVec (st.q (r (t + 1))) = Pi.single 0 1 := by
  exact KServerAlgebra.exists_det_one_normalizer _ (st.column_ne_zero hs 0 _)

end KServerConj
end PaperFile051

section PaperFile052
set_option autoImplicit false
open scoped BigOperators

namespace KServerConj

noncomputable def AlgebraicState.chosenNormalizer {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] [DecidableEq M] {s : Fin (n + 2) → M} {r : ℕ → M} {t : ℕ}
    (st : AlgebraicState s r t) (hs : Function.Injective s) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) (K (n + 2) M) :=
  Classical.choose (st.exists_normalizer hs)

theorem AlgebraicState.chosenNormalizer_spec {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] [DecidableEq M] {s : Fin (n + 2) → M} {r : ℕ → M} {t : ℕ}
    (st : AlgebraicState s r t) (hs : Function.Injective s) :
    (st.chosenNormalizer hs).det = 1 ∧
      (st.chosenNormalizer hs).mulVec (st.q (r (t + 1))) = Pi.single 0 1 :=
  Classical.choose_spec (st.exists_normalizer hs)

noncomputable def nextAlgebraicState {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    {s : Fin (n + 2) → M} {r : ℕ → M} {t : ℕ}
    (st : AlgebraicState s r t) (hs : Function.Injective s) : AlgebraicState s r (t + 1) :=
  st.advance hs (st.chosenNormalizer hs) (st.chosenNormalizer_spec hs).1
    (st.chosenNormalizer_spec hs).2

noncomputable def algebraicStateSeq {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (s : Fin (n + 2) → M) (hs : Function.Injective s) (r : ℕ → M) :
    (t : ℕ) → AlgebraicState s r t
  | 0 => initialAlgebraicState s hs r
  | t + 1 => nextAlgebraicState (algebraicStateSeq s hs r t) hs

noncomputable def algebraicColumns {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (s : Fin (n + 2) → M) (hs : Function.Injective s) (r : ℕ → M) (t : ℕ) :
    M → Fin (n + 2) → K (n + 2) M :=
  (algebraicStateSeq s hs r t).q

noncomputable def algebraicNormalizedColumns {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (s : Fin (n + 2) → M) (hs : Function.Injective s) (r : ℕ → M) (t : ℕ) :
    M → Fin (n + 2) → K (n + 2) M :=
  fun x => ((algebraicStateSeq s hs r (t - 1)).chosenNormalizer hs).mulVec
    ((algebraicStateSeq s hs r (t - 1)).q x)

theorem algebraicSequences_isRun {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (s : Fin (n + 2) → M) (hs : Function.Injective s) (r : ℕ → M) (T : ℕ) :
    IsRun s r T (algebraicColumns s hs r) (algebraicNormalizedColumns s hs r) := by
  constructor
  · rfl
  · intro t ht _
    cases t with
    | zero => exact (Nat.not_succ_le_zero 0 ht).elim
    | succ u =>
      refine ⟨?_, ?_⟩
      · refine ⟨(algebraicStateSeq s hs r u).chosenNormalizer hs,
          ((algebraicStateSeq s hs r u).chosenNormalizer_spec hs).1, ?_, ?_⟩
        · simpa only [algebraicColumns, Nat.succ_sub_one, Nat.add_sub_cancel] using
            ((algebraicStateSeq s hs r u).chosenNormalizer_spec hs).2
        · intro x
          simp only [algebraicNormalizedColumns, algebraicColumns, Nat.succ_sub_one]
      · rfl

end KServerConj
end PaperFile052

section PaperFile053
set_option autoImplicit false
open scoped BigOperators

namespace KServerConj

theorem algebraicState_of_run {n : ℕ} {M : Type*}
    [PseudoMetricSpace M] [Fintype M] [DecidableEq M]
    (s : Fin (n + 2) → M) (hs : Function.Injective s) (r : ℕ → M) (T : ℕ)
    (q qn : ℕ → M → Fin (n + 2) → K (n + 2) M) (hrun : IsRun s r T q qn) :
    ∀ t, t ≤ T → ∃ st : AlgebraicState s r t, st.q = q t := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨initialAlgebraicState s hs r, hrun.1.symm⟩
  | succ t ih =>
    intro ht
    obtain ⟨st, hst⟩ := ih ((Nat.le_succ t).trans ht)
    obtain ⟨⟨B, hB, hr, hqn⟩, hupdate⟩ :=
      hrun.2 (t + 1) (Nat.succ_le_succ (Nat.zero_le t)) ht
    have hr' : B.mulVec (st.q (r (t + 1))) = Pi.single 0 1 := by
      simpa only [hst, Nat.add_sub_cancel] using hr
    have hqn' : qn (t + 1) = (st.normalized B hB).q := by
      funext y
      change qn (t + 1) y = B.mulVec (st.q y)
      simpa only [hst, Nat.add_sub_cancel] using hqn y
    refine ⟨st.advance hs B hB hr', ?_⟩
    change rowReplace (st.normalized B hB).q (freshRow r (t + 1)) = q (t + 1)
    rw [hupdate, hqn']

end KServerConj
end PaperFile053

section PaperFile054

end PaperFile054

open KServerConj

theorem solution {M : Type*} [PseudoMetricSpace M] [Fintype M] [DecidableEq M] {m : ℕ}
    (hm : 1 ≤ m) (s : Fin (m + 1) → M) (hs : Function.Injective s) (r : ℕ → M) (T : ℕ) :
    (∃ q qn : ℕ → M → Fin (m + 1) → K (m + 1) M, IsRun s r T q qn) ∧
    ∀ q qn : ℕ → M → Fin (m + 1) → K (m + 1) M, IsRun s r T q qn →
      ∀ t, t ≤ T → ∀ x : Fin (m + 1) → M, Function.Injective x →
        nu (colDet (q t) x) =
          ((workFn (m + 1) (Finset.univ.image s) r t (Finset.univ.image x) : ℝ) : WithTop ℝ) := by
  cases m with
  | zero => exact (Nat.not_succ_le_zero 0 hm).elim
  | succ n =>
    refine ⟨⟨algebraicColumns s hs r, algebraicNormalizedColumns s hs r,
      algebraicSequences_isRun s hs r T⟩, ?_⟩
    intro q qn hrun t ht x hx
    obtain ⟨st, hst⟩ := algebraicState_of_run s hs r T q qn hrun t ht
    simpa only [hst] using st.represents x hx

#print axioms solution
