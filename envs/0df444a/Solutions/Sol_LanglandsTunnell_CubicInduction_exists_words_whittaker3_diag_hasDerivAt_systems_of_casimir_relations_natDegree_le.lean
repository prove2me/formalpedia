-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/7de3c1d2-b745-5c20-b92a-d290e48c138a

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmoothSpace3
import Definitions.Def_LanglandsTunnell_CubicInduction_Growth
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Mathlib.Analysis.Matrix.Normed
import Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace
import Definitions.Def_NumberField_HeightOneSpectrum
import Theorems.Thm_LanglandsTunnell_CubicInduction_whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul
import Theorems.Thm_LanglandsTunnell_CubicInduction_whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.SimpleRing.Principal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le

set_option autoImplicit false

noncomputable section

namespace RealGL3

open Matrix

private abbrev M3 : Type := Matrix (Fin 3) (Fin 3) ℝ

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private def GLs : Set M3 := {x | x.det ≠ 0}

private theorem isOpen_GLs : IsOpen GLs := by
  have h : GLs = (fun x : M3 => x.det) ⁻¹' {0}ᶜ := by
    ext x
    simp [GLs]
  rw [h]
  exact isOpen_compl_singleton.preimage (continuous_id.matrix_det)

private theorem mul_mem_GLs {x y : M3} (hx : x ∈ GLs) (hy : y ∈ GLs) : x * y ∈ GLs := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at hx hy ⊢
  exact mul_ne_zero hx hy

private abbrev E (a b : Fin 3) : M3 := Matrix.single a b 1

section Deriv

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private def rD (X : M3) (F : M3 → V) : M3 → V :=
  fun x => deriv (fun s : ℝ => F (x * (1 + s • X))) 0

private theorem curve_eq (x X : M3) : (fun s : ℝ => x * (1 + s • X)) = fun s => x + s • (x * X) := by
  funext s
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]

private theorem hasDerivAt_curve (x X : M3) (s : ℝ) : HasDerivAt (fun s : ℝ => x * (1 + s • X)) (x * X) s := by
  rw [curve_eq]
  exact (((hasDerivAt_id' s).smul_const (x * X)).const_add x).congr_deriv (one_smul _ _)

private theorem curve_zero (x X : M3) : x * (1 + (0 : ℝ) • X) = x := by simp

private theorem continuous_curve (x X : M3) : Continuous fun s : ℝ => x * (1 + s • X) := by
  rw [curve_eq]
  fun_prop

private def mulRightL (X : M3) : M3 →L[ℝ] M3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => y * X
      map_add' := fun a b => Matrix.add_mul a b X
      map_smul' := fun c a => Matrix.smul_mul c a X }

@[scoped simp] private theorem mulRightL_apply (X y : M3) : mulRightL X y = y * X := rfl

private def mulLeftL (X : M3) : M3 →L[ℝ] M3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => X * y
      map_add' := fun a b => Matrix.mul_add X a b
      map_smul' := fun c a => Matrix.mul_smul X c a }

@[scoped simp] private theorem mulLeftL_apply (X y : M3) : mulLeftL X y = X * y := rfl

private theorem differentiableAt_of_contDiffOn {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {x : M3}
    (hx : x ∈ GLs) : DifferentiableAt ℝ F x :=
  (hF.differentiableOn (by simp) x hx).differentiableAt (isOpen_GLs.mem_nhds hx)

private theorem rD_eq_fderiv (X : M3) {F : M3 → V} {x : M3} (hF : DifferentiableAt ℝ F x) :
    rD X F x = fderiv ℝ F x (x * X) := by
  have hF' : HasFDerivAt F (fderiv ℝ F x) (x * (1 + (0 : ℝ) • X)) := by
    rw [curve_zero]
    exact hF.hasFDerivAt
  exact (hF'.comp_hasDerivAt (0 : ℝ) (hasDerivAt_curve x X 0)).deriv

private theorem rD_congr_of_eventuallyEq (X : M3) {F G : M3 → V} {x : M3} (h : F =ᶠ[nhds x] G) : rD X F x = rD X G x :=
    by
  simp only [rD]
  refine Filter.EventuallyEq.deriv_eq ?_
  have hc : Filter.Tendsto (fun s : ℝ => x * (1 + s • X)) (nhds 0) (nhds x) := by
    have h' := (continuous_curve x X).continuousAt (x := 0)
    rwa [ContinuousAt, curve_zero] at h'
  exact hc.eventually h

private theorem rD_congr_of_eqOn (X : M3) {F G : M3 → V} (h : Set.EqOn F G GLs) {x : M3} (hx : x ∈ GLs) :
    rD X F x = rD X G x :=
  rD_congr_of_eventuallyEq X (h.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hx))

private theorem contDiffOn_rD (X : M3) {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) :
    ContDiffOn ℝ (⊤ : ℕ∞) (rD X F) GLs := by
  obtain ⟨hdiff, hsmooth⟩ := (contDiffOn_infty_iff_fderiv_of_isOpen isOpen_GLs).1 hF
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ F y (mulRightL X y)) GLs :=
    hsmooth.clm_apply (mulRightL X).contDiff.contDiffOn
  refine h2.congr fun y hy => ?_
  rw [mulRightL_apply]
  exact rD_eq_fderiv X ((hdiff y hy).differentiableAt (isOpen_GLs.mem_nhds hy))

private theorem rD_add_dir (X Y : M3) {F : M3 → V} {x : M3} (hF : DifferentiableAt ℝ F x) :
    rD (X + Y) F x = rD X F x + rD Y F x := by
  rw [rD_eq_fderiv _ hF, rD_eq_fderiv _ hF, rD_eq_fderiv _ hF, Matrix.mul_add, map_add]

private theorem rD_smul_dir (c : ℝ) (X : M3) {F : M3 → V} {x : M3} (hF : DifferentiableAt ℝ F x) :
    rD (c • X) F x = c • rD X F x := by
  rw [rD_eq_fderiv _ hF, rD_eq_fderiv _ hF, Matrix.mul_smul, map_smul]

private theorem rD_zero_dir (F : M3 → V) (x : M3) : rD 0 F x = 0 := by
  simp [rD]

private theorem rD_sum_dir {α : Type*} (s : Finset α) (X : α → M3) {F : M3 → V} {x : M3} (hF : DifferentiableAt ℝ F x)
    :
    rD (∑ a ∈ s, X a) F x = ∑ a ∈ s, rD (X a) F x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rD_zero_dir]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, rD_add_dir _ _ hF, ih]

private theorem rD_sub_dir (X Y : M3) {F : M3 → V} {x : M3} (hF : DifferentiableAt ℝ F x) :
    rD (X - Y) F x = rD X F x - rD Y F x := by
  rw [rD_eq_fderiv _ hF, rD_eq_fderiv _ hF, rD_eq_fderiv _ hF, Matrix.mul_sub, map_sub]

private theorem differentiableAt_comp_curve {F : M3 → V} {x : M3} (X : M3) (hF : DifferentiableAt ℝ F x) :
    DifferentiableAt ℝ (fun s : ℝ => F (x * (1 + s • X))) 0 := by
  have hF' : DifferentiableAt ℝ F (x * (1 + (0 : ℝ) • X)) := by rwa [curve_zero]
  exact hF'.comp 0 (hasDerivAt_curve x X 0).differentiableAt

private theorem rD_add (X : M3) {F G : M3 → V} {x : M3} (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    rD X (F + G) x = rD X F x + rD X G x := by
  simp only [rD, Pi.add_apply]
  exact deriv_fun_add (differentiableAt_comp_curve X hF) (differentiableAt_comp_curve X hG)

private theorem rD_sub (X : M3) {F G : M3 → V} {x : M3} (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    rD X (F - G) x = rD X F x - rD X G x := by
  simp only [rD, Pi.sub_apply]
  exact deriv_fun_sub (differentiableAt_comp_curve X hF) (differentiableAt_comp_curve X hG)

private theorem rD_const_smul {R : Type*} [Semiring R] [Module R V] [SMulCommClass ℝ R V] [ContinuousConstSMul R V]
    (X : M3) (c : R) {F : M3 → V} {x : M3} (hF : DifferentiableAt ℝ F x) : rD X (c • F) x = c • rD X F x := by
  simp only [rD, Pi.smul_apply]
  exact deriv_fun_const_smul c (differentiableAt_comp_curve X hF)

private theorem rD_sum {α : Type*} (s : Finset α) (X : M3) {F : α → M3 → V} {x : M3}
    (hF : ∀ a ∈ s, DifferentiableAt ℝ (F a) x) :
    rD X (fun y => ∑ a ∈ s, F a y) x = ∑ a ∈ s, rD X (F a) x := by
  simp only [rD]
  exact deriv_fun_sum fun a ha => differentiableAt_comp_curve X (hF a ha)

private theorem rD_clm_comp {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W) (X : M3)
    {F : M3 → V} {x : M3} (hF : DifferentiableAt ℝ F x) : rD X (fun y => L (F y)) x = L (rD X F x) := by
  have h2 : HasFDerivAt (fun y => L (F y)) ((L : V →L[ℝ] W).comp (fderiv ℝ F x)) x :=
    L.hasFDerivAt.comp x hF.hasFDerivAt
  rw [rD_eq_fderiv X hF, rD_eq_fderiv X h2.differentiableAt, h2.fderiv, ContinuousLinearMap.comp_apply]

private theorem rD_rD_apply (X Y : M3) {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {x : M3} (hx : x ∈ GLs) :
    rD X (rD Y F) x = fderiv ℝ (fderiv ℝ F) x (x * X) (x * Y) + fderiv ℝ F x (x * X * Y) := by
  obtain ⟨hdiff, hsmooth⟩ := (contDiffOn_infty_iff_fderiv_of_isOpen isOpen_GLs).1 hF
  have hev : rD Y F =ᶠ[nhds x] fun y => fderiv ℝ F y (mulRightL Y y) := by
    filter_upwards [isOpen_GLs.mem_nhds hx] with y hy
    rw [mulRightL_apply]
    exact rD_eq_fderiv Y ((hdiff y hy).differentiableAt (isOpen_GLs.mem_nhds hy))
  have hfd : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) x) x :=
    ((hsmooth.contDiffAt (isOpen_GLs.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have hlin : HasFDerivAt (fun y : M3 => mulRightL Y y) (mulRightL Y) x := (mulRightL Y).hasFDerivAt
  have hprod := (hfd.clm_apply hlin).congr_of_eventuallyEq hev
  rw [rD_eq_fderiv X hprod.differentiableAt]
  refine (DFunLike.congr_fun hprod.fderiv (x * X)).trans ?_
  first
    | rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
      exact (add_comm _ _).trans rfl
    | show fderiv ℝ F x (mulRightL Y (x * X)) + fderiv ℝ (fderiv ℝ F) x (x * X) (mulRightL Y x) = _
      exact (add_comm _ _).trans rfl
    | exact (add_comm _ _).trans rfl

private theorem rD_comm (X Y : M3) {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {x : M3} (hx : x ∈ GLs) :
    rD X (rD Y F) x - rD Y (rD X F) x = rD (X * Y - Y * X) F x := by
  have hsymm : IsSymmSndFDerivAt ℝ F x :=
    (hF.contDiffAt (isOpen_GLs.mem_nhds hx)).isSymmSndFDerivAt
      (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)
  have hs : fderiv ℝ (fderiv ℝ F) x (x * X) (x * Y) = fderiv ℝ (fderiv ℝ F) x (x * Y) (x * X) :=
    hsymm (x * X) (x * Y)
  rw [rD_rD_apply X Y hF hx, rD_rD_apply Y X hF hx, hs, rD_eq_fderiv _ (differentiableAt_of_contDiffOn hF hx),
    Matrix.mul_sub, map_sub, Matrix.mul_assoc, Matrix.mul_assoc]
  abel

private theorem rD_rD_eq (X Y : M3) {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {x : M3} (hx : x ∈ GLs) :
    rD X (rD Y F) x = rD Y (rD X F) x + rD (X * Y - Y * X) F x := by
  rw [← rD_comm X Y hF hx]
  abel

private theorem rD_comp_mul_left (X g : M3) (F : M3 → V) : rD X (fun y => F (g * y)) = fun y => rD X F (g * y) := by
  funext y
  simp only [rD, Matrix.mul_assoc]

private theorem rD_comp_mul_right (X : M3) {g : M3} (hg : g ∈ GLs) (F : M3 → V) (x : M3) :
    rD X (fun y => F (y * g)) x = rD (g⁻¹ * X * g) F (x * g) := by
  have hg' : IsUnit g.det := isUnit_iff_ne_zero.mpr hg
  have key : x * g * (g⁻¹ * X * g) = x * X * g := by
    rw [Matrix.mul_assoc g⁻¹ X g, ← Matrix.mul_assoc (x * g) g⁻¹ (X * g), Matrix.mul_assoc x g g⁻¹,
      Matrix.mul_nonsing_inv g hg', Matrix.mul_one, ← Matrix.mul_assoc]
  simp only [rD]
  congr 1
  funext s
  congr 1
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, key]

private def c2 (F : M3 → V) : M3 → V := fun x => ∑ i : Fin 3, ∑ j : Fin 3, rD (E i j) (rD (E j i) F) x

private def c3 (F : M3 → V) : M3 → V :=
  fun x => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, rD (E i j) (rD (E j k) (rD (E k i) F)) x

private theorem contDiffOn_c2 {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) : ContDiffOn ℝ (⊤ : ℕ∞) (c2 F) GLs := by
  unfold c2
  exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => contDiffOn_rD _ (contDiffOn_rD _ hF)

private theorem contDiffOn_c3 {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) : ContDiffOn ℝ (⊤ : ℕ∞) (c3 F) GLs := by
  unfold c3
  exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ =>
    contDiffOn_rD _ (contDiffOn_rD _ (contDiffOn_rD _ hF))

private theorem E_mul_E (a b c d : Fin 3) : E a b * E c d = if b = c then E a d else 0 := by
  by_cases h : b = c
  · subst h
    simp [Matrix.single_mul_single_same]
  · rw [Matrix.single_mul_single_of_ne (c := (1 : ℝ)) a b c h (1 : ℝ), if_neg h]

private theorem rD_E_rD_E (a b c d : Fin 3) {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {x : M3} (hx : x ∈ GLs) :
    rD (E a b) (rD (E c d) F) x = rD (E c d) (rD (E a b) F) x +
      ((if b = c then rD (E a d) F x else 0) - if d = a then rD (E c b) F x else 0) := by
  rw [rD_rD_eq (E a b) (E c d) hF hx, rD_sub_dir _ _ (differentiableAt_of_contDiffOn hF hx), E_mul_E, E_mul_E]
  congr 2
  · split_ifs <;> simp [rD_zero_dir]
  · split_ifs <;> simp [rD_zero_dir]

private theorem matrix_eq_sum_E (X : M3) : X = ∑ a : Fin 3, ∑ b : Fin 3, X a b • E a b := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [E, Matrix.smul_single, smul_eq_mul, mul_one]

private theorem rD_dir_expand (X : M3) {F : M3 → V} {x : M3} (hF : DifferentiableAt ℝ F x) :
    rD X F x = ∑ a : Fin 3, ∑ b : Fin 3, X a b • rD (E a b) F x := by
  conv_lhs => rw [matrix_eq_sum_E X]
  rw [rD_sum_dir _ _ hF]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rD_sum_dir _ _ hF]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [rD_smul_dir _ _ hF]

private theorem differentiableAt_ite (p : Prop) [Decidable p] {G : M3 → V} {x : M3} (hG : DifferentiableAt ℝ G x) :
    DifferentiableAt ℝ (fun y => if p then G y else 0) x := by
  by_cases hp : p
  · simp only [hp, if_true]; exact hG
  · simp only [hp, if_false]; exact differentiableAt_const 0

private theorem rD_ite (X : M3) (p : Prop) [Decidable p] (G : M3 → V) (x : M3) :
    rD X (fun y => if p then G y else 0) x = if p then rD X G x else 0 := by
  by_cases hp : p
  · simp only [hp, if_true]
  · simp only [hp, if_false, rD, deriv_const]

private theorem c2_rD_E (a b : Fin 3) {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {x : M3} (hx : x ∈ GLs) :
    c2 (rD (E a b) F) x = rD (E a b) (c2 F) x := by
  have hd : ∀ c d : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞) (rD (E c d) F) GLs := fun c d => contDiffOn_rD _ hF
  have hdd : ∀ c d e f : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞) (rD (E c d) (rD (E e f) F)) GLs :=
    fun c d e f => contDiffOn_rD _ (hd e f)

  have hsum : ∀ i j : Fin 3, rD (E i j) (rD (E j i) (rD (E a b) F)) x =
      rD (E a b) (rD (E i j) (rD (E j i) F)) x +
        ((if j = a then rD (E i b) (rD (E j i) F) x else 0) - if b = i then rD (E a j) (rD (E j i) F) x else 0) +
        ((if i = a then rD (E i j) (rD (E j b) F) x else 0) - if b = j then rD (E i j) (rD (E a i) F) x else 0) := by
    intro i j
    have hin : Set.EqOn (rD (E j i) (rD (E a b) F))
        (rD (E a b) (rD (E j i) F) +
          ((fun y => if i = a then rD (E j b) F y else 0) - fun y => if b = j then rD (E a i) F y else 0)) GLs := by
      intro y hy
      simp only [Pi.add_apply, Pi.sub_apply]
      exact rD_E_rD_E j i a b hF hy
    rw [rD_congr_of_eqOn (E i j) hin hx]
    have hA : DifferentiableAt ℝ (rD (E a b) (rD (E j i) F)) x := differentiableAt_of_contDiffOn (hdd a b j i) hx
    have hB : DifferentiableAt ℝ (fun y => if i = a then rD (E j b) F y else 0) x :=
      differentiableAt_ite _ (differentiableAt_of_contDiffOn (hd j b) hx)
    have hC : DifferentiableAt ℝ (fun y => if b = j then rD (E a i) F y else 0) x :=
      differentiableAt_ite _ (differentiableAt_of_contDiffOn (hd a i) hx)
    rw [rD_add _ hA (hB.sub hC), rD_sub _ hB hC, rD_ite, rD_ite, rD_E_rD_E i j a b (hd j i) hx]

  have hmain : ∑ i : Fin 3, ∑ j : Fin 3, rD (E a b) (rD (E i j) (rD (E j i) F)) x = rD (E a b) (c2 F) x := by
    unfold c2
    rw [rD_sum _ _ fun i _ => DifferentiableAt.fun_sum fun j _ => differentiableAt_of_contDiffOn (hdd i j j i) hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [rD_sum _ _ fun j _ => differentiableAt_of_contDiffOn (hdd i j j i) hx]
  have hT1 : ∑ i : Fin 3, ∑ j : Fin 3,
      ((if j = a then rD (E i b) (rD (E j i) F) x else 0) - if b = i then rD (E a j) (rD (E j i) F) x else 0) =
      (∑ i : Fin 3, rD (E i b) (rD (E a i) F) x) - ∑ j : Fin 3, rD (E a j) (rD (E j b) F) x := by
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hT2 : ∑ i : Fin 3, ∑ j : Fin 3,
      ((if i = a then rD (E i j) (rD (E j b) F) x else 0) - if b = j then rD (E i j) (rD (E a i) F) x else 0) =
      (∑ j : Fin 3, rD (E a j) (rD (E j b) F) x) - ∑ i : Fin 3, rD (E i b) (rD (E a i) F) x := by
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  calc c2 (rD (E a b) F) x = ∑ i : Fin 3, ∑ j : Fin 3, rD (E i j) (rD (E j i) (rD (E a b) F)) x := rfl
    _ = ∑ i : Fin 3, ∑ j : Fin 3, (rD (E a b) (rD (E i j) (rD (E j i) F)) x +
        ((if j = a then rD (E i b) (rD (E j i) F) x else 0) - if b = i then rD (E a j) (rD (E j i) F) x else 0) +
        ((if i = a then rD (E i j) (rD (E j b) F) x else 0) - if b = j then rD (E i j) (rD (E a i) F) x else 0)) := by
          simp only [hsum]
    _ = rD (E a b) (c2 F) x := by
          simp only [Finset.sum_add_distrib]
          rw [hmain, hT1, hT2]
          abel

private theorem c2_sum {α : Type*} (s : Finset α) {F : α → M3 → V} (hF : ∀ a ∈ s, ContDiffOn ℝ (⊤ : ℕ∞) (F a) GLs)
    {x : M3} (hx : x ∈ GLs) : c2 (fun y => ∑ a ∈ s, F a y) x = ∑ a ∈ s, c2 (F a) x := by
  unfold c2
  have hin : ∀ i j : Fin 3, Set.EqOn (rD (E j i) fun y => ∑ a ∈ s, F a y) (fun y => ∑ a ∈ s, rD (E j i) (F a) y) GLs :=
    fun i j y hy => rD_sum s _ fun a ha => differentiableAt_of_contDiffOn (hF a ha) hy
  have h1 : ∀ i j : Fin 3,
      rD (E i j) (rD (E j i) fun y => ∑ a ∈ s, F a y) x = ∑ a ∈ s, rD (E i j) (rD (E j i) (F a)) x := by
    intro i j
    rw [rD_congr_of_eqOn (E i j) (hin i j) hx,
      rD_sum s _ fun a ha => differentiableAt_of_contDiffOn (contDiffOn_rD _ (hF a ha)) hx]
  simp only [h1]
  exact (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans Finset.sum_comm

private theorem c2_const_smul (c : ℝ) {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {x : M3} (hx : x ∈ GLs) :
    c2 (c • F) x = c • c2 F x := by
  unfold c2
  have hin : ∀ i j : Fin 3, Set.EqOn (rD (E j i) (c • F)) (c • rD (E j i) F) GLs :=
    fun i j y hy => rD_const_smul _ c (differentiableAt_of_contDiffOn hF hy)
  have h1 : ∀ i j : Fin 3, rD (E i j) (rD (E j i) (c • F)) x = c • rD (E i j) (rD (E j i) F) x := by
    intro i j
    rw [rD_congr_of_eqOn (E i j) (hin i j) hx,
      rD_const_smul _ c (differentiableAt_of_contDiffOn (contDiffOn_rD _ hF) hx)]
  simp only [h1, Finset.smul_sum]

private theorem c2_congr_of_eqOn {F G : M3 → V} (h : Set.EqOn F G GLs) {x : M3} (hx : x ∈ GLs) : c2 F x = c2 G x := by
  unfold c2
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact rD_congr_of_eqOn _ (fun y hy => rD_congr_of_eqOn _ h hy) hx

private theorem c2_rD (X : M3) {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {x : M3} (hx : x ∈ GLs) :
    c2 (rD X F) x = rD X (c2 F) x := by
  have hexp : Set.EqOn (rD X F) (fun y => ∑ a : Fin 3, ∑ b : Fin 3, X a b • rD (E a b) F y) GLs :=
    fun y hy => rD_dir_expand X (differentiableAt_of_contDiffOn hF hy)
  have hflat : Set.EqOn (fun y => ∑ a : Fin 3, ∑ b : Fin 3, X a b • rD (E a b) F y)
      (fun y => ∑ p : Fin 3 × Fin 3, (X p.1 p.2 • rD (E p.1 p.2) F) y) GLs := by
    intro y _
    simp only [Pi.smul_apply, Fintype.sum_prod_type]
  rw [c2_congr_of_eqOn (hexp.trans hflat) hx,
    c2_sum _ (fun p _ => (contDiffOn_rD _ hF).const_smul (X p.1 p.2)) hx,
    rD_dir_expand X (differentiableAt_of_contDiffOn (contDiffOn_c2 hF) hx), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [c2_const_smul _ (contDiffOn_rD _ hF) hx, c2_rD_E a b hF hx]

private theorem c2_c3 {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {x : M3} (hx : x ∈ GLs) :
    c2 (c3 F) x = c3 (c2 F) x := by
  have hd : ∀ c d : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞) (rD (E c d) F) GLs := fun c d => contDiffOn_rD _ hF
  have hdd : ∀ c d e f : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞) (rD (E c d) (rD (E e f) F)) GLs :=
    fun c d e f => contDiffOn_rD _ (hd e f)
  have hddd : ∀ c d e f g h : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞) (rD (E c d) (rD (E e f) (rD (E g h) F))) GLs :=
    fun c d e f g h => contDiffOn_rD _ (hdd e f g h)
  have hflat : Set.EqOn (c3 F) (fun y => ∑ p : Fin 3 × Fin 3 × Fin 3,
      rD (E p.1 p.2.1) (rD (E p.2.1 p.2.2) (rD (E p.2.2 p.1) F)) y) GLs := by
    intro y _
    simp only [c3, Fintype.sum_prod_type]
  rw [c2_congr_of_eqOn hflat hx, c2_sum _ (fun p _ => hddd _ _ _ _ _ _) hx]
  unfold c3
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_

  rw [c2_rD (E i j) (hdd j k k i) hx]
  refine rD_congr_of_eqOn (E i j) (fun y hy => ?_) hx
  rw [c2_rD (E j k) (hd k i) hy]
  refine rD_congr_of_eqOn (E j k) (fun z hz => ?_) hy
  exact c2_rD (E k i) hF hz

private theorem c2_comp_mul_left (g : M3) (F : M3 → V) : c2 (fun y => F (g * y)) = fun y => c2 F (g * y) := by
  funext y
  unfold c2
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [rD_comp_mul_left (E j i) g F, rD_comp_mul_left (E i j) g (rD (E j i) F)]

private theorem c3_comp_mul_left (g : M3) (F : M3 → V) : c3 (fun y => F (g * y)) = fun y => c3 F (g * y) := by
  funext y
  unfold c3
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [rD_comp_mul_left (E k i) g F, rD_comp_mul_left (E j k) g (rD (E k i) F),
    rD_comp_mul_left (E i j) g (rD (E j k) (rD (E k i) F))]

private theorem conj_E_apply (P Q : M3) (i j c d : Fin 3) : (P * E i j * Q) c d = P c i * Q j d := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j, Matrix.mul_single_apply_same (1 : ℝ) i j c P, mul_one]
  · intro q _ hq
    rw [Matrix.mul_single_apply_of_ne (1 : ℝ) i j c q hq P, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

private theorem rD_fun_const_smul (X : M3) (c : ℝ) {F : M3 → V} {x : M3} (hF : DifferentiableAt ℝ F x) :
    rD X (fun y => c • F y) x = c • rD X F x :=
  rD_const_smul X c hF

private theorem differentiableAt_smul_lam (c : ℝ) {G : M3 → V} {x : M3} (hG : DifferentiableAt ℝ G x) :
    DifferentiableAt ℝ (fun y => c • G y) x :=
  hG.const_smul c

private theorem differentiableAt_sum_smul_lam (Y : M3) (G : Fin 3 → Fin 3 → M3 → V) {x : M3}
    (hG : ∀ e f : Fin 3, DifferentiableAt ℝ (G e f) x) (e : Fin 3) :
    DifferentiableAt ℝ (fun y => ∑ f : Fin 3, Y e f • G e f y) x :=
  DifferentiableAt.fun_sum fun f _ => differentiableAt_smul_lam (Y e f) (hG e f)

private theorem sum_ite_const {α β : Type*} [AddCommMonoid β] (s : Finset α) (P : Prop) [Decidable P]
    (f : α → β) : (∑ a ∈ s, if P then f a else 0) = if P then ∑ a ∈ s, f a else 0 := by
  split_ifs <;> simp

private theorem sum_sum_sum_smul {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (a : α → β → γ → ℝ)
    (B : γ → V) : (∑ i, ∑ j, ∑ p, a i j p • B p) = ∑ p, (∑ i, ∑ j, a i j p) • B p := by
  calc (∑ i, ∑ j, ∑ p, a i j p • B p) = ∑ i, ∑ p, ∑ j, a i j p • B p :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ p, ∑ i, ∑ j, a i j p • B p := Finset.sum_comm
    _ = ∑ p, (∑ i, ∑ j, a i j p) • B p := by simp only [Finset.sum_smul]

private theorem sum_sum_sum_sum_smul {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (a : α → β → γ → δ → ℝ) (B : δ → V) :
    (∑ i, ∑ j, ∑ k, ∑ p, a i j k p • B p) = ∑ p, (∑ i, ∑ j, ∑ k, a i j k p) • B p := by
  calc (∑ i, ∑ j, ∑ k, ∑ p, a i j k p • B p) = ∑ i, ∑ p, (∑ j, ∑ k, a i j k p) • B p :=
        Finset.sum_congr rfl fun i _ => sum_sum_sum_smul (a i) B
    _ = ∑ p, ∑ i, (∑ j, ∑ k, a i j k p) • B p := Finset.sum_comm
    _ = ∑ p, (∑ i, ∑ j, ∑ k, a i j k p) • B p := by simp only [Finset.sum_smul]

private theorem rD_rD_expand (X Y : M3) {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {x : M3} (hx : x ∈ GLs) :
    rD X (rD Y F) x = ∑ p : (Fin 3 × Fin 3) × (Fin 3 × Fin 3),
      (X p.1.1 p.1.2 * Y p.2.1 p.2.2) • rD (E p.1.1 p.1.2) (rD (E p.2.1 p.2.2) F) x := by
  have hin : Set.EqOn (rD Y F) (fun y => ∑ e : Fin 3, ∑ f : Fin 3, Y e f • rD (E e f) F y) GLs :=
    fun y hy => rD_dir_expand Y (differentiableAt_of_contDiffOn hF hy)
  have hd : ∀ e f : Fin 3, DifferentiableAt ℝ (rD (E e f) F) x :=
    fun e f => differentiableAt_of_contDiffOn (contDiffOn_rD _ hF) hx
  rw [rD_dir_expand X (differentiableAt_of_contDiffOn (contDiffOn_rD _ hF) hx)]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [rD_congr_of_eqOn _ hin hx,
    rD_sum _ _ fun e _ => differentiableAt_sum_smul_lam Y (fun e f => rD (E e f) F) hd e, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [rD_sum _ _ fun f _ => differentiableAt_smul_lam (Y e f) (hd e f), Finset.smul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [rD_fun_const_smul _ _ (hd e f), smul_smul]

private theorem rD_rD_rD_expand (X Y Z : M3) {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {x : M3} (hx : x ∈ GLs) :
    rD X (rD Y (rD Z F)) x = ∑ p : (Fin 3 × Fin 3) × (Fin 3 × Fin 3) × (Fin 3 × Fin 3),
      (X p.1.1 p.1.2 * Y p.2.1.1 p.2.1.2 * Z p.2.2.1 p.2.2.2) •
        rD (E p.1.1 p.1.2) (rD (E p.2.1.1 p.2.1.2) (rD (E p.2.2.1 p.2.2.2) F)) x := by
  have hZ : ContDiffOn ℝ (⊤ : ℕ∞) (rD Z F) GLs := contDiffOn_rD _ hF
  have hd : ∀ e f : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞) (rD (E e f) F) GLs := fun e f => contDiffOn_rD _ hF
  have hdd : ∀ c d e f : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞) (rD (E c d) (rD (E e f) F)) GLs :=
    fun c d e f => contDiffOn_rD _ (hd e f)

  have hin : Set.EqOn (rD Z F) (fun y => ∑ e : Fin 3, ∑ f : Fin 3, Z e f • rD (E e f) F y) GLs :=
    fun y hy => rD_dir_expand Z (differentiableAt_of_contDiffOn hF hy)
  have hmid : ∀ c d : Fin 3, Set.EqOn (rD (E c d) (rD Z F))
      (fun y => ∑ e : Fin 3, ∑ f : Fin 3, Z e f • rD (E c d) (rD (E e f) F) y) GLs := by
    intro c d y hy
    rw [rD_congr_of_eqOn _ hin hy, rD_sum _ _ fun e _ => differentiableAt_sum_smul_lam Z (fun e f => rD (E e f) F)
      (fun e f => differentiableAt_of_contDiffOn (hd e f) hy) e]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [rD_sum _ _ fun f _ => differentiableAt_smul_lam (Z e f) (differentiableAt_of_contDiffOn (hd e f) hy)]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [rD_fun_const_smul _ _ (differentiableAt_of_contDiffOn (hd e f) hy)]
  have hout : ∀ a b c d : Fin 3, rD (E a b) (rD (E c d) (rD Z F)) x =
      ∑ e : Fin 3, ∑ f : Fin 3, Z e f • rD (E a b) (rD (E c d) (rD (E e f) F)) x := by
    intro a b c d
    rw [rD_congr_of_eqOn _ (hmid c d) hx, rD_sum _ _ fun e _ =>
      differentiableAt_sum_smul_lam Z (fun e f => rD (E c d) (rD (E e f) F))
        (fun e f => differentiableAt_of_contDiffOn (hdd c d e f) hx) e]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [rD_sum _ _ fun f _ => differentiableAt_smul_lam (Z e f) (differentiableAt_of_contDiffOn (hdd c d e f) hx)]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [rD_fun_const_smul _ _ (differentiableAt_of_contDiffOn (hdd c d e f) hx)]
  rw [rD_rD_expand X Y hZ hx]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  rw [hout, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [smul_smul]

private theorem c2_comp_mul_right {g : M3} (hg : g ∈ GLs) {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {x : M3}
    (hx : x ∈ GLs) : c2 (fun y => F (y * g)) x = c2 F (x * g) := by
  have hxg : x * g ∈ GLs := mul_mem_GLs hx hg
  have hg' : IsUnit g.det := isUnit_iff_ne_zero.mpr hg
  have hB : c2 (fun y => F (y * g)) x =
      ∑ i : Fin 3, ∑ j : Fin 3, rD (g⁻¹ * E i j * g) (rD (g⁻¹ * E j i * g) F) (x * g) := by
    unfold c2
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h1 : rD (E j i) (fun y => F (y * g)) = fun y => rD (g⁻¹ * E j i * g) F (y * g) :=
      funext fun y => rD_comp_mul_right _ hg F y
    rw [h1, rD_comp_mul_right _ hg]
  have hkey : ∀ c d e f : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, (g⁻¹ * E i j * g) c d * (g⁻¹ * E j i * g) e f =
      (if c = f then 1 else 0) * if e = d then 1 else 0 := by
    intro c d e f
    simp only [conj_E_apply]
    have h1 : ∀ i j : Fin 3, g⁻¹ c i * g j d * (g⁻¹ e j * g i f) = (g⁻¹ c i * g i f) * (g⁻¹ e j * g j d) := by
      intros; ring
    simp only [h1]
    rw [← Finset.sum_mul_sum, ← Matrix.mul_apply, ← Matrix.mul_apply, Matrix.nonsing_inv_mul g hg',
      Matrix.one_apply, Matrix.one_apply]
  have hB2 : (∑ i : Fin 3, ∑ j : Fin 3, rD (g⁻¹ * E i j * g) (rD (g⁻¹ * E j i * g) F) (x * g)) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ p : (Fin 3 × Fin 3) × (Fin 3 × Fin 3),
        ((g⁻¹ * E i j * g) p.1.1 p.1.2 * (g⁻¹ * E j i * g) p.2.1 p.2.2) •
          rD (E p.1.1 p.1.2) (rD (E p.2.1 p.2.2) F) (x * g) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [rD_rD_expand _ _ hF hxg]
  rw [hB, hB2, sum_sum_sum_smul]
  simp only [hkey, ite_mul, one_mul, zero_mul, ite_smul, one_smul, zero_smul]
  unfold c2
  simp only [Fintype.sum_prod_type, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem c3_comp_mul_right {g : M3} (hg : g ∈ GLs) {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {x : M3}
    (hx : x ∈ GLs) : c3 (fun y => F (y * g)) x = c3 F (x * g) := by
  have hxg : x * g ∈ GLs := mul_mem_GLs hx hg
  have hg' : IsUnit g.det := isUnit_iff_ne_zero.mpr hg
  have hB : c3 (fun y => F (y * g)) x = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      rD (g⁻¹ * E i j * g) (rD (g⁻¹ * E j k * g) (rD (g⁻¹ * E k i * g) F)) (x * g) := by
    unfold c3
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    have h1 : rD (E k i) (fun y => F (y * g)) = fun y => rD (g⁻¹ * E k i * g) F (y * g) :=
      funext fun y => rD_comp_mul_right _ hg F y
    have h2 : rD (E j k) (fun y => rD (g⁻¹ * E k i * g) F (y * g)) =
        fun y => rD (g⁻¹ * E j k * g) (rD (g⁻¹ * E k i * g) F) (y * g) :=
      funext fun y => rD_comp_mul_right _ hg _ y
    rw [h1, h2, rD_comp_mul_right _ hg]
  have hkey : ∀ c₁ d₁ c₂ d₂ c₃ d₃ : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      (g⁻¹ * E i j * g) c₁ d₁ * (g⁻¹ * E j k * g) c₂ d₂ * (g⁻¹ * E k i * g) c₃ d₃ =
      (if c₁ = d₃ then 1 else 0) * (if c₂ = d₁ then 1 else 0) * if c₃ = d₂ then 1 else 0 := by
    intro c₁ d₁ c₂ d₂ c₃ d₃
    simp only [conj_E_apply]
    have h1 : ∀ i j k : Fin 3, g⁻¹ c₁ i * g j d₁ * (g⁻¹ c₂ j * g k d₂) * (g⁻¹ c₃ k * g i d₃) =
        (g⁻¹ c₁ i * g i d₃) * ((g⁻¹ c₂ j * g j d₁) * (g⁻¹ c₃ k * g k d₂)) := by
      intros; ring
    simp only [h1, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [← Matrix.mul_apply, ← Matrix.mul_apply, ← Matrix.mul_apply, Matrix.nonsing_inv_mul g hg',
      Matrix.one_apply, Matrix.one_apply, Matrix.one_apply, mul_assoc]
  have hB2 : (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      rD (g⁻¹ * E i j * g) (rD (g⁻¹ * E j k * g) (rD (g⁻¹ * E k i * g) F)) (x * g)) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ p : (Fin 3 × Fin 3) × (Fin 3 × Fin 3) × (Fin 3 × Fin 3),
        ((g⁻¹ * E i j * g) p.1.1 p.1.2 * (g⁻¹ * E j k * g) p.2.1.1 p.2.1.2 *
          (g⁻¹ * E k i * g) p.2.2.1 p.2.2.2) •
          rD (E p.1.1 p.1.2) (rD (E p.2.1.1 p.2.1.2) (rD (E p.2.2.1 p.2.2.2) F)) (x * g) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [rD_rD_rD_expand _ _ _ hF hxg]
  rw [hB, hB2, sum_sum_sum_sum_smul]
  simp only [hkey, ite_mul, one_mul, zero_mul, ite_smul, one_smul, zero_smul]
  unfold c3
  simp only [Fintype.sum_prod_type, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    sum_ite_const]

end Deriv

private def IsUpperUni (n : M3) : Prop := (∀ i j : Fin 3, j < i → n i j = 0) ∧ ∀ i : Fin 3, n i i = 1

private def gram (x : M3) : M3 := x * xᵀ

private def gram12 (x : M3) : ℝ := gram x 1 1 * gram x 2 2 - gram x 1 2 ^ 2

private def iwD (x : M3) : Fin 3 → ℝ := ![x.det ^ 2 / gram12 x, gram12 x / gram x 2 2, gram x 2 2]

private def iwA (x : M3) : Fin 3 → ℝ := fun i => Real.sqrt (iwD x i)

private def iwP (x : M3) : ℝ := (gram x 0 1 * gram x 2 2 - gram x 0 2 * gram x 1 2) / gram12 x
private def iwQ (x : M3) : ℝ := gram x 0 2 / gram x 2 2
private def iwR (x : M3) : ℝ := gram x 1 2 / gram x 2 2

private def iwN (x : M3) : M3 := !![1, iwP x, iwQ x; 0, 1, iwR x; 0, 0, 1]

private def iwK (x : M3) : M3 := (Matrix.diagonal (iwA x))⁻¹ * (iwN x)⁻¹ * x

private def torus (y z : ℝ) : M3 := Matrix.diagonal ![y * z, z, 1]

section R2Furniture

private theorem gram_apply (x : M3) (i j : Fin 3) :
    gram x i j = x i 0 * x j 0 + x i 1 * x j 1 + x i 2 * x j 2 := by
  simp [gram, Matrix.mul_apply, Fin.sum_univ_three]

private theorem gram_symm (x : M3) (i j : Fin 3) : gram x i j = gram x j i := by
  rw [gram_apply, gram_apply]; ring

private theorem gram12_eq_sum_sq (x : M3) :
    gram12 x = (x 1 1 * x 2 2 - x 1 2 * x 2 1) ^ 2 + (x 1 0 * x 2 2 - x 1 2 * x 2 0) ^ 2 +
      (x 1 0 * x 2 1 - x 1 1 * x 2 0) ^ 2 := by
  simp only [gram12, gram_apply]; ring

private theorem det_eq_minors (x : M3) :
    x.det = x 0 0 * (x 1 1 * x 2 2 - x 1 2 * x 2 1) - x 0 1 * (x 1 0 * x 2 2 - x 1 2 * x 2 0) +
      x 0 2 * (x 1 0 * x 2 1 - x 1 1 * x 2 0) := by
  rw [Matrix.det_fin_three]; ring

private theorem eq_zero_of_sq_add_sq_add_sq {a b c : ℝ} (h : a ^ 2 + b ^ 2 + c ^ 2 = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have ha := sq_nonneg a; have hb := sq_nonneg b; have hc := sq_nonneg c
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

private theorem gram12_pos {x : M3} (hx : x ∈ GLs) : 0 < gram12 x := by
  rcases (show (0 : ℝ) ≤ gram12 x by rw [gram12_eq_sum_sq]; positivity).lt_or_eq with h | h
  · exact h
  exfalso; apply hx
  rw [gram12_eq_sum_sq] at h
  obtain ⟨h1, h2, h3⟩ := eq_zero_of_sq_add_sq_add_sq h.symm
  rw [det_eq_minors, h1, h2, h3]; ring

private theorem gram22_eq (x : M3) : gram x 2 2 = x 2 0 ^ 2 + x 2 1 ^ 2 + x 2 2 ^ 2 := by
  rw [gram_apply]; ring

private theorem gram22_pos {x : M3} (hx : x ∈ GLs) : 0 < gram x 2 2 := by
  rcases (show (0 : ℝ) ≤ gram x 2 2 by rw [gram22_eq]; positivity).lt_or_eq with h | h
  · exact h
  exfalso; apply hx
  rw [gram22_eq] at h
  obtain ⟨h0, h1, h2⟩ := eq_zero_of_sq_add_sq_add_sq h.symm
  rw [det_eq_minors, h0, h1, h2]; ring

private theorem det_ne_zero_of_mem {x : M3} (hx : x ∈ GLs) : x.det ≠ 0 := hx

private theorem iwD_pos {x : M3} (hx : x ∈ GLs) (i : Fin 3) : 0 < iwD x i := by
  have h12 := gram12_pos hx; have h22 := gram22_pos hx; have hd := det_ne_zero_of_mem hx
  fin_cases i <;> simp [iwD] <;> positivity

private theorem iwA_sq {x : M3} (hx : x ∈ GLs) (i : Fin 3) : iwA x i ^ 2 = iwD x i :=
  Real.sq_sqrt (iwD_pos hx i).le

private theorem iwN_inv (x : M3) :
    (iwN x)⁻¹ = !![1, -iwP x, iwP x * iwR x - iwQ x; 0, 1, -iwR x; 0, 0, 1] := by
  apply Matrix.inv_eq_left_inv
  rw [iwN, Matrix.mul_fin_three, Matrix.one_fin_three]; congr 1; ring

private theorem det_iwN (x : M3) : (iwN x).det = 1 := by
  rw [iwN, Matrix.det_fin_three]; simp

private theorem iwN_inv_mul (x : M3) : (iwN x)⁻¹ * iwN x = 1 :=
  Matrix.nonsing_inv_mul _ (by rw [det_iwN]; exact isUnit_one)

private theorem iwN_mul_inv (x : M3) : iwN x * (iwN x)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (by rw [det_iwN]; exact isUnit_one)

private theorem diag_inv_of_ne {d : Fin 3 → ℝ} (hd : ∀ i, d i ≠ 0) :
    (Matrix.diagonal d)⁻¹ = Matrix.diagonal fun i => (d i)⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i
  exact inv_mul_cancel₀ (hd i)

private theorem diagA_inv {x : M3} (hx : x ∈ GLs) :
    (Matrix.diagonal (iwA x))⁻¹ = Matrix.diagonal fun i => (iwA x i)⁻¹ :=
  diag_inv_of_ne fun i => (Real.sqrt_pos.2 (iwD_pos hx i)).ne'

private theorem diagA_mul_inv {x : M3} (hx : x ∈ GLs) :
    Matrix.diagonal (iwA x) * (Matrix.diagonal (iwA x))⁻¹ = 1 := by
  rw [diagA_inv hx, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i
  exact mul_inv_cancel₀ (Real.sqrt_pos.2 (iwD_pos hx i)).ne'

private theorem det_sq_eq (x : M3) :
    x.det ^ 2 = gram x 0 0 * gram12 x - gram x 2 2 * gram x 0 1 ^ 2 +
      2 * gram x 0 1 * gram x 0 2 * gram x 1 2 - gram x 1 1 * gram x 0 2 ^ 2 := by
  have hdet : x.det ^ 2 = (gram x).det := by rw [gram, Matrix.det_mul, Matrix.det_transpose, sq]
  rw [hdet, Matrix.det_fin_three, gram12, gram_symm x 1 0, gram_symm x 2 0, gram_symm x 2 1]; ring

private theorem iwD_zero (x : M3) : iwD x 0 = x.det ^ 2 / gram12 x := rfl
private theorem iwD_one (x : M3) : iwD x 1 = gram12 x / gram x 2 2 := rfl
private theorem iwD_two (x : M3) : iwD x 2 = gram x 2 2 := rfl

private theorem recon22 (x : M3) : gram x 2 2 = iwD x 2 := rfl

private theorem recon12 {x : M3} (hx : x ∈ GLs) : gram x 1 2 = iwR x * iwD x 2 := by
  rw [iwR, iwD_two]; field_simp [(gram22_pos hx).ne']

private theorem recon02 {x : M3} (hx : x ∈ GLs) : gram x 0 2 = iwQ x * iwD x 2 := by
  rw [iwQ, iwD_two]; field_simp [(gram22_pos hx).ne']

private theorem recon11 {x : M3} (hx : x ∈ GLs) : gram x 1 1 = iwD x 1 + iwR x ^ 2 * iwD x 2 := by
  rw [iwR, iwD_one, iwD_two, gram12]; field_simp [(gram22_pos hx).ne']; ring

private theorem recon01 {x : M3} (hx : x ∈ GLs) : gram x 0 1 = iwP x * iwD x 1 + iwQ x * iwR x * iwD x 2 := by
  have h22 := (gram22_pos hx).ne'; have h12 := (gram12_pos hx).ne'
  rw [iwP, iwQ, iwR, iwD_one, iwD_two]; field_simp; ring

private theorem recon00 {x : M3} (hx : x ∈ GLs) :
    gram x 0 0 = iwD x 0 + iwP x ^ 2 * iwD x 1 + iwQ x ^ 2 * iwD x 2 := by
  have h22 := (gram22_pos hx).ne'; have h12 := (gram12_pos hx).ne'
  rw [iwP, iwQ, iwD_zero, iwD_one, iwD_two, det_sq_eq]
  field_simp
  simp only [gram12]; ring

private theorem diagonal_iwD (x : M3) :
    Matrix.diagonal (iwD x) = !![iwD x 0, 0, 0; 0, iwD x 1, 0; 0, 0, iwD x 2] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

private theorem iwN_transpose (x : M3) : (iwN x)ᵀ = !![1, 0, 0; iwP x, 1, 0; iwQ x, iwR x, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [iwN]

private theorem gram_eq_iwN_iwD {x : M3} (hx : x ∈ GLs) :
    gram x = iwN x * Matrix.diagonal (iwD x) * (iwN x)ᵀ := by
  have e00 := recon00 hx; have e01 := recon01 hx; have e02 := recon02 hx; have e11 := recon11 hx
  have e12 := recon12 hx; have e22 := recon22 x
  have s10 := gram_symm x 1 0; have s20 := gram_symm x 2 0; have s21 := gram_symm x 2 1
  rw [diagonal_iwD, iwN_transpose, iwN, Matrix.mul_fin_three, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    first
      | linear_combination e00 | linear_combination e01 | linear_combination e02 | linear_combination e11
      | linear_combination e12 | linear_combination e22 | linear_combination s10 + e01 | linear_combination s20 + e02
      | linear_combination s21 + e12

end R2Furniture

private theorem isUpperUni_iwN (x : M3) : IsUpperUni (iwN x) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [iwN] at hij ⊢
  · fin_cases i <;> simp [iwN]

private theorem iwA_pos {x : M3} (hx : x ∈ GLs) (i : Fin 3) : 0 < iwA x i := by
  exact Real.sqrt_pos.2 (iwD_pos hx i)

private theorem iwK_orth {x : M3} (hx : x ∈ GLs) : (iwK x)ᵀ * iwK x = 1 := by
  rw [mul_eq_one_comm]
  have hkk : iwK x * (iwK x)ᵀ =
      (Matrix.diagonal (iwA x))⁻¹ * ((iwN x)⁻¹ * gram x * ((iwN x)⁻¹)ᵀ) * ((Matrix.diagonal (iwA x))⁻¹)ᵀ := by
    rw [iwK, gram]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [hkk, gram_eq_iwN_iwD hx, diagA_inv hx, Matrix.diagonal_transpose]
  have h1 : (iwN x)⁻¹ * (iwN x * Matrix.diagonal (iwD x) * (iwN x)ᵀ) * ((iwN x)⁻¹)ᵀ = Matrix.diagonal (iwD x) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, iwN_inv_mul, one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul,
      iwN_inv_mul, Matrix.transpose_one, mul_one]
  rw [h1, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i
  have hi := (iwA_pos hx i).ne'
  rw [← iwA_sq hx i]; field_simp

private theorem iwasawa {x : M3} (hx : x ∈ GLs) : iwN x * Matrix.diagonal (iwA x) * iwK x = x := by
  rw [iwK, ← mul_assoc, ← mul_assoc, mul_assoc (iwN x), diagA_mul_inv hx, mul_one, iwN_mul_inv, one_mul]

section R2Unique

private theorem IsUpperUni.entries {n : M3} (hn : IsUpperUni n) :
    n 0 0 = 1 ∧ n 1 1 = 1 ∧ n 2 2 = 1 ∧ n 1 0 = 0 ∧ n 2 0 = 0 ∧ n 2 1 = 0 :=
  ⟨hn.2 0, hn.2 1, hn.2 2, hn.1 1 0 (by decide), hn.1 2 0 (by decide), hn.1 2 1 (by decide)⟩

private theorem IsUpperUni.eq_literal {n : M3} (hn : IsUpperUni n) :
    n = !![1, n 0 1, n 0 2; 0, 1, n 1 2; 0, 0, 1] := by
  obtain ⟨h00, h11, h22, h10, h20, h21⟩ := hn.entries
  ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h11, h22, h10, h20, h21]

private theorem isUpperUni_of_literal (p q r : ℝ) : IsUpperUni !![1, p, q; 0, 1, r; 0, 0, 1] := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · fin_cases i <;> simp

private theorem IsUpperUni.det_eq_one {n : M3} (hn : IsUpperUni n) : n.det = 1 := by
  rw [hn.eq_literal, Matrix.det_fin_three]; simp

private theorem IsUpperUni.mul {n m : M3} (hn : IsUpperUni n) (hm : IsUpperUni m) : IsUpperUni (n * m) := by
  rw [hn.eq_literal, hm.eq_literal, Matrix.mul_fin_three]
  simp only [mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add]
  exact isUpperUni_of_literal _ _ _

private theorem isUpperUni_one : IsUpperUni (1 : M3) := by
  rw [Matrix.one_fin_three]; exact isUpperUni_of_literal 0 0 0

private theorem isUpperUni_diag_conj {d : Fin 3 → ℝ} (hd : ∀ i, 0 < d i) {n : M3} (hn : IsUpperUni n) :
    IsUpperUni (Matrix.diagonal d * n * (Matrix.diagonal d)⁻¹) := by
  rw [diag_inv_of_ne fun i => (hd i).ne', hn.eq_literal]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    fin_cases i <;> simp [(hd _).ne']

private theorem gram_of_decomp {n k : M3} {a : Fin 3 → ℝ} (hk : kᵀ * k = 1) :
    gram (n * Matrix.diagonal a * k) = n * Matrix.diagonal (fun i => a i ^ 2) * nᵀ := by
  have hkk : k * kᵀ = 1 := mul_eq_one_comm.1 hk
  rw [gram, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose]
  calc n * Matrix.diagonal a * k * (kᵀ * (Matrix.diagonal a * nᵀ))
      = n * Matrix.diagonal a * (k * kᵀ) * (Matrix.diagonal a * nᵀ) := by simp only [Matrix.mul_assoc]
    _ = n * (Matrix.diagonal a * Matrix.diagonal a) * nᵀ := by rw [hkk, mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.diagonal_mul_diagonal]; congr 3; funext i; ring

private theorem gram_entries_of_decomp {k : M3} {a : Fin 3 → ℝ} (p q r : ℝ) (hk : kᵀ * k = 1) :
    let x := !![1, p, q; 0, 1, r; 0, 0, 1] * Matrix.diagonal a * k
    gram x 2 2 = a 2 ^ 2 ∧ gram x 1 2 = a 2 ^ 2 * r ∧ gram x 0 2 = a 2 ^ 2 * q ∧
      gram x 1 1 = a 1 ^ 2 + a 2 ^ 2 * r ^ 2 ∧ gram x 0 1 = a 1 ^ 2 * p + a 2 ^ 2 * q * r := by
  intro x
  have hg : gram x = !![1, p, q; 0, 1, r; 0, 0, 1] * Matrix.diagonal (fun i => a i ^ 2) *
      (!![1, p, q; 0, 1, r; 0, 0, 1] : M3)ᵀ := gram_of_decomp hk
  have hd : Matrix.diagonal (fun i => a i ^ 2) = !![a 0 ^ 2, 0, 0; 0, a 1 ^ 2, 0; 0, 0, a 2 ^ 2] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  have ht : (!![1, p, q; 0, 1, r; 0, 0, 1] : M3)ᵀ = !![1, 0, 0; p, 1, 0; q, r, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [hd, ht, Matrix.mul_fin_three, Matrix.mul_fin_three] at hg
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [hg] <;> ring

private theorem det_sq_of_decomp {n k : M3} {a : Fin 3 → ℝ} (hn : IsUpperUni n) (hk : kᵀ * k = 1) :
    (n * Matrix.diagonal a * k).det ^ 2 = (a 0 * a 1 * a 2) ^ 2 := by
  have hkdet : k.det ^ 2 = 1 := by
    have := congrArg Matrix.det hk
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    rw [sq, this]
  rw [Matrix.det_mul, Matrix.det_mul, hn.det_eq_one, Matrix.det_diagonal, Fin.prod_univ_three, one_mul, mul_pow, hkdet,
    mul_one]

private theorem coords_of_decomp {n k : M3} {a : Fin 3 → ℝ} (hn : IsUpperUni n) (ha : ∀ i, 0 < a i) (hk : kᵀ * k = 1) :
    iwN (n * Matrix.diagonal a * k) = n ∧ iwA (n * Matrix.diagonal a * k) = a := by
  have hdet := det_sq_of_decomp hn hk (a := a)
  obtain ⟨p, q, r, rfl⟩ : ∃ p q r : ℝ, n = !![1, p, q; 0, 1, r; 0, 0, 1] := ⟨_, _, _, hn.eq_literal⟩
  obtain ⟨g22, g12, g02, g11, g01⟩ := gram_entries_of_decomp p q r hk (a := a)
  have h1 := (ha 1).ne'; have h2 := (ha 2).ne'
  have hg12 : gram12 (!![1, p, q; 0, 1, r; 0, 0, 1] * Matrix.diagonal a * k) = a 1 ^ 2 * a 2 ^ 2 := by
    rw [gram12, g11, g12, g22]; ring
  have hR : iwR (!![1, p, q; 0, 1, r; 0, 0, 1] * Matrix.diagonal a * k) = r := by rw [iwR, g12, g22]; field_simp
  have hQ : iwQ (!![1, p, q; 0, 1, r; 0, 0, 1] * Matrix.diagonal a * k) = q := by rw [iwQ, g02, g22]; field_simp
  have hP : iwP (!![1, p, q; 0, 1, r; 0, 0, 1] * Matrix.diagonal a * k) = p := by
    rw [iwP, g01, g22, g02, g12, hg12]; field_simp; ring
  refine ⟨?_, ?_⟩
  · rw [iwN, hP, hQ, hR]
  · funext i
    fin_cases i
    · show Real.sqrt (iwD _ 0) = a 0
      rw [iwD_zero, hdet, hg12, show (a 0 * a 1 * a 2) ^ 2 / (a 1 ^ 2 * a 2 ^ 2) = a 0 ^ 2 by field_simp]
      exact Real.sqrt_sq (ha 0).le
    · show Real.sqrt (iwD _ 1) = a 1
      rw [iwD_one, hg12, g22, show a 1 ^ 2 * a 2 ^ 2 / a 2 ^ 2 = a 1 ^ 2 by field_simp]
      exact Real.sqrt_sq (ha 1).le
    · show Real.sqrt (iwD _ 2) = a 2
      rw [iwD_two, g22]; exact Real.sqrt_sq (ha 2).le

private theorem diag_pos_det_isUnit {a : Fin 3 → ℝ} (ha : ∀ i, 0 < a i) : IsUnit (Matrix.diagonal a).det := by
  rw [Matrix.det_diagonal, Fin.prod_univ_three]
  exact (mul_pos (mul_pos (ha 0) (ha 1)) (ha 2)).ne'.isUnit

private theorem iwK_of_decomp {n k : M3} {a : Fin 3 → ℝ} (hn : IsUpperUni n) (ha : ∀ i, 0 < a i) (hk : kᵀ * k = 1) :
    iwK (n * Matrix.diagonal a * k) = k := by
  obtain ⟨hN, hA⟩ := coords_of_decomp hn ha hk
  rw [iwK, hN, hA]
  have hn' : IsUnit n.det := by rw [hn.det_eq_one]; exact isUnit_one
  calc (Matrix.diagonal a)⁻¹ * n⁻¹ * (n * Matrix.diagonal a * k)
      = (Matrix.diagonal a)⁻¹ * (n⁻¹ * n) * Matrix.diagonal a * k := by simp only [Matrix.mul_assoc]
    _ = k := by rw [Matrix.nonsing_inv_mul _ hn', mul_one, Matrix.nonsing_inv_mul _ (diag_pos_det_isUnit ha), one_mul]

private theorem coords_eq_of_decomp {x n k : M3} {a : Fin 3 → ℝ} (hn : IsUpperUni n) (ha : ∀ i, 0 < a i)
    (hk : kᵀ * k = 1) (h : n * Matrix.diagonal a * k = x) : iwN x = n ∧ iwA x = a ∧ iwK x = k := by
  subst h
  obtain ⟨hN, hA⟩ := coords_of_decomp hn ha hk
  exact ⟨hN, hA, iwK_of_decomp hn ha hk⟩

end R2Unique

private theorem iwasawa_unique {x n k : M3} {a : Fin 3 → ℝ} (hn : IsUpperUni n) (ha : ∀ i, 0 < a i) (hk : kᵀ * k = 1)
    (h : n * Matrix.diagonal a * k = x) : n = iwN x ∧ a = iwA x ∧ k = iwK x := by
  obtain ⟨hN, hA, hK⟩ := coords_eq_of_decomp hn ha hk h
  exact ⟨hN.symm, hA.symm, hK.symm⟩

section R2Smooth

private theorem contDiffOn_entry (i j : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : M3 => x i j) GLs :=
  ((contDiff_apply ℝ ℝ j).comp (contDiff_apply ℝ (Fin 3 → ℝ) i)).contDiffOn

private theorem contDiffOn_gram_entry (i j : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : M3 => gram x i j) GLs := by
  have h : (fun x : M3 => gram x i j) = fun x => x i 0 * x j 0 + x i 1 * x j 1 + x i 2 * x j 2 :=
    funext fun x => gram_apply x i j
  rw [h]
  have e := contDiffOn_entry
  exact (((e i 0).mul (e j 0)).add ((e i 1).mul (e j 1))).add ((e i 2).mul (e j 2))

private theorem contDiffOn_gram12 : ContDiffOn ℝ (⊤ : ℕ∞) gram12 GLs := by
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun x => gram x 1 1 * gram x 2 2 - gram x 1 2 ^ 2) GLs
  exact ((contDiffOn_gram_entry 1 1).mul (contDiffOn_gram_entry 2 2)).sub ((contDiffOn_gram_entry 1 2).pow 2)

private theorem contDiffOn_det : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : M3 => x.det) GLs := by
  have h : (fun x : M3 => x.det) = fun x => x 0 0 * (x 1 1 * x 2 2 - x 1 2 * x 2 1) -
      x 0 1 * (x 1 0 * x 2 2 - x 1 2 * x 2 0) + x 0 2 * (x 1 0 * x 2 1 - x 1 1 * x 2 0) := funext det_eq_minors
  rw [h]
  have e := contDiffOn_entry
  exact (((e 0 0).mul (((e 1 1).mul (e 2 2)).sub ((e 1 2).mul (e 2 1)))).sub
    ((e 0 1).mul (((e 1 0).mul (e 2 2)).sub ((e 1 2).mul (e 2 0))))).add
    ((e 0 2).mul (((e 1 0).mul (e 2 1)).sub ((e 1 1).mul (e 2 0))))

private theorem gram12_ne_on : ∀ x ∈ GLs, gram12 x ≠ 0 := fun _ hx => (gram12_pos hx).ne'
private theorem gram22_ne_on : ∀ x ∈ GLs, gram x 2 2 ≠ 0 := fun _ hx => (gram22_pos hx).ne'

private theorem contDiffOn_iwD (i : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => iwD x i) GLs := by
  fin_cases i
  · exact (contDiffOn_det.pow 2).div contDiffOn_gram12 gram12_ne_on
  · exact contDiffOn_gram12.div (contDiffOn_gram_entry 2 2) gram22_ne_on
  · exact contDiffOn_gram_entry 2 2

private theorem contDiffOn_iwP : ContDiffOn ℝ (⊤ : ℕ∞) iwP GLs :=
  (((contDiffOn_gram_entry 0 1).mul (contDiffOn_gram_entry 2 2)).sub
    ((contDiffOn_gram_entry 0 2).mul (contDiffOn_gram_entry 1 2))).div contDiffOn_gram12 gram12_ne_on

private theorem contDiffOn_iwQ : ContDiffOn ℝ (⊤ : ℕ∞) iwQ GLs :=
  (contDiffOn_gram_entry 0 2).div (contDiffOn_gram_entry 2 2) gram22_ne_on

private theorem contDiffOn_iwR : ContDiffOn ℝ (⊤ : ℕ∞) iwR GLs :=
  (contDiffOn_gram_entry 1 2).div (contDiffOn_gram_entry 2 2) gram22_ne_on

private theorem contDiffOn_iwN_entry (i j : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => iwN x i j) GLs := by
  have hP := contDiffOn_iwP; have hQ := contDiffOn_iwQ; have hR := contDiffOn_iwR
  simp only [iwN]
  fin_cases i <;> fin_cases j <;> simp <;> first | exact contDiffOn_const | exact hP | exact hQ | exact hR

private theorem contDiffOn_iwN_inv_entry (i j : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (iwN x)⁻¹ i j) GLs := by
  have hP := contDiffOn_iwP; have hQ := contDiffOn_iwQ; have hR := contDiffOn_iwR
  simp only [iwN_inv]
  fin_cases i <;> fin_cases j <;> simp <;>
    first | exact contDiffOn_const | exact hP.neg | exact hR.neg | exact (hP.mul hR).sub hQ

end R2Smooth

private theorem contDiffOn_iwN : ContDiffOn ℝ (⊤ : ℕ∞) iwN GLs := by
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  exact contDiffOn_iwN_entry i j

private theorem contDiffOn_iwA : ContDiffOn ℝ (⊤ : ℕ∞) iwA GLs := by
  refine contDiffOn_pi.2 fun i => ?_
  exact (contDiffOn_iwD i).sqrt fun x hx => (iwD_pos hx i).ne'

private theorem contDiffOn_iwK : ContDiffOn ℝ (⊤ : ℕ∞) iwK GLs := by
  have hA : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => iwA x i) GLs := fun i => contDiffOn_pi.1 contDiffOn_iwA i
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  refine ContDiffOn.congr (f := fun x => (iwA x i)⁻¹ *
    ((iwN x)⁻¹ i 0 * x 0 j + (iwN x)⁻¹ i 1 * x 1 j + (iwN x)⁻¹ i 2 * x 2 j)) ?_ ?_
  · refine ((hA i).inv fun x hx => (iwA_pos hx i).ne').mul ?_
    exact (((contDiffOn_iwN_inv_entry i 0).mul (contDiffOn_entry 0 j)).add
      ((contDiffOn_iwN_inv_entry i 1).mul (contDiffOn_entry 1 j))).add
      ((contDiffOn_iwN_inv_entry i 2).mul (contDiffOn_entry 2 j))
  · intro x hx
    show iwK x i j = _
    rw [iwK, diagA_inv hx, Matrix.mul_apply, Fin.sum_univ_three]
    simp only [Matrix.diagonal_mul]
    ring

private theorem iw_uni_mul {n x : M3} (hn : IsUpperUni n) (hx : x ∈ GLs) :
    iwN (n * x) = n * iwN x ∧ iwA (n * x) = iwA x ∧ iwK (n * x) = iwK x := by
  have hNx := isUpperUni_iwN x
  refine coords_eq_of_decomp (hn.mul hNx) (iwA_pos hx) (iwK_orth hx) ?_
  rw [Matrix.mul_assoc n, Matrix.mul_assoc n, iwasawa hx]

private theorem iw_mul_orth {x k : M3} (hx : x ∈ GLs) (hk : kᵀ * k = 1) :
    iwN (x * k) = iwN x ∧ iwA (x * k) = iwA x ∧ iwK (x * k) = iwK x * k := by
  have hkk : (iwK x * k)ᵀ * (iwK x * k) = 1 := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (iwK x)ᵀ, iwK_orth hx, one_mul, hk]
  refine coords_eq_of_decomp (isUpperUni_iwN x) (iwA_pos hx) hkk ?_
  rw [← Matrix.mul_assoc, iwasawa hx]

private theorem iw_smul {c : ℝ} (hc : 0 < c) {x : M3} (hx : x ∈ GLs) :
    iwN (c • x) = iwN x ∧ iwA (c • x) = c • iwA x ∧ iwK (c • x) = iwK x := by
  refine coords_eq_of_decomp (isUpperUni_iwN x) (fun i => by simpa using mul_pos hc (iwA_pos hx i)) (iwK_orth hx) ?_
  rw [Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul, iwasawa hx]

private theorem iw_diag_mul {d : Fin 3 → ℝ} (hd : ∀ i, 0 < d i) {x : M3} (hx : x ∈ GLs) :
    iwN (Matrix.diagonal d * x) = Matrix.diagonal d * iwN x * (Matrix.diagonal d)⁻¹ ∧
      iwA (Matrix.diagonal d * x) = d * iwA x ∧ iwK (Matrix.diagonal d * x) = iwK x := by
  have hdA : ∀ i, 0 < (d * iwA x) i := fun i => mul_pos (hd i) (iwA_pos hx i)
  refine coords_eq_of_decomp (isUpperUni_diag_conj hd (isUpperUni_iwN x)) hdA (iwK_orth hx) ?_
  have hdd : (Matrix.diagonal d)⁻¹ * Matrix.diagonal (d * iwA x) = Matrix.diagonal (iwA x) := by
    rw [diag_inv_of_ne fun i => (hd i).ne', Matrix.diagonal_mul_diagonal]; congr 1; funext i
    simp only [Pi.mul_apply]; field_simp [(hd i).ne']
  calc Matrix.diagonal d * iwN x * (Matrix.diagonal d)⁻¹ * Matrix.diagonal (d * iwA x) * iwK x
      = Matrix.diagonal d * (iwN x * ((Matrix.diagonal d)⁻¹ * Matrix.diagonal (d * iwA x)) * iwK x) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.diagonal d * x := by rw [hdd, iwasawa hx]

private theorem torus_mem_GLs {y z : ℝ} (hy : 0 < y) (hz : 0 < z) : torus y z ∈ GLs := by
  show (torus y z).det ≠ 0
  rw [torus, Matrix.det_diagonal, Fin.prod_univ_three]
  show y * z * z * 1 ≠ 0
  positivity

private theorem iw_torus {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    iwN (torus y z) = 1 ∧ iwA (torus y z) = ![y * z, z, 1] ∧ iwK (torus y z) = 1 := by
  have hpos : ∀ i, 0 < (![y * z, z, 1] : Fin 3 → ℝ) i := by
    intro i; fin_cases i <;> simp <;> positivity
  exact coords_eq_of_decomp isUpperUni_one hpos (by rw [Matrix.transpose_one, one_mul]) (by rw [one_mul, mul_one]; rfl)

end RealGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

namespace CoinvariantS3

open MvPolynomial

private noncomputable def s₂ : MvPolynomial (Fin 2) ℚ := 2 * (X 0 ^ 2 - X 0 * X 1 + X 1 ^ 2)

private noncomputable def s₃ : MvPolynomial (Fin 2) ℚ := 3 * (X 0 * X 1 * (X 0 - X 1))

private def basisExp : Fin 6 → ℕ × ℕ := ![(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (2, 1)]

private def basisDeg (j : Fin 6) : ℕ := (basisExp j).1 + (basisExp j).2

private noncomputable def bmon (j : Fin 6) : MvPolynomial (Fin 2) ℚ := X 0 ^ (basisExp j).1 * X 1 ^ (basisExp j).2

private noncomputable def term (j : Fin 6) (e f : ℕ) : MvPolynomial (Fin 2) ℚ := bmon j * s₂ ^ e * s₃ ^ f

private def HasDecomp (n : ℕ) (p : MvPolynomial (Fin 2) ℚ) : Prop :=
  ∃ c : Fin 6 → ℕ → ℕ → ℚ, (∀ j e f, c j e f ≠ 0 → basisDeg j + 2 * e + 3 * f = n) ∧
    p = ∑ j, ∑ e ∈ Finset.range (n + 1), ∑ f ∈ Finset.range (n + 1), c j e f • term j e f

private theorem HasDecomp.zero (n : ℕ) : HasDecomp n 0 :=
  ⟨fun _ _ _ => 0, fun _ _ _ h => (h rfl).elim, by simp⟩

private theorem HasDecomp.add {n : ℕ} {p q : MvPolynomial (Fin 2) ℚ} (hp : HasDecomp n p) (hq : HasDecomp n q) :
    HasDecomp n (p + q) := by
  obtain ⟨c, hc, rfl⟩ := hp
  obtain ⟨c', hc', rfl⟩ := hq
  refine ⟨fun j e f => c j e f + c' j e f, fun j e f h => ?_, ?_⟩
  · have h' : c j e f + c' j e f ≠ 0 := h
    by_cases h1 : c j e f = 0
    · rw [h1, zero_add] at h'
      exact hc' j e f h'
    · exact hc j e f h1
  · simp only [add_smul, Finset.sum_add_distrib]

private theorem HasDecomp.smul {n : ℕ} {p : MvPolynomial (Fin 2) ℚ} (a : ℚ) (hp : HasDecomp n p) :
    HasDecomp n (a • p) := by
  obtain ⟨c, hc, rfl⟩ := hp
  refine ⟨fun j e f => a * c j e f, fun j e f h => ?_, ?_⟩
  · exact hc j e f (by rintro h0; exact h (show a * c j e f = 0 by rw [h0, mul_zero]))
  simp only [Finset.smul_sum, smul_smul]

private theorem HasDecomp.sub {n : ℕ} {p q : MvPolynomial (Fin 2) ℚ} (hp : HasDecomp n p) (hq : HasDecomp n q) :
    HasDecomp n (p - q) := by
  have h := hp.add (hq.smul (-1))
  rwa [neg_one_smul, ← sub_eq_add_neg] at h

private theorem hasDecomp_bmon (j : Fin 6) : HasDecomp (basisDeg j) (bmon j) := by
  classical
  refine ⟨fun j' e f => if j' = j ∧ e = 0 ∧ f = 0 then 1 else 0, fun j' e f h => ?_, ?_⟩
  · by_cases hc : j' = j ∧ e = 0 ∧ f = 0
    · obtain ⟨rfl, rfl, rfl⟩ := hc
      simp
    · exact absurd (if_neg hc) h
  · rw [Finset.sum_eq_single j, Finset.sum_eq_single 0, Finset.sum_eq_single 0]
    · simp [term]
    · intro f _ hf
      simp [hf]
    · simp
    · intro e _ he
      refine Finset.sum_eq_zero fun f _ => ?_
      simp [he]
    · simp
    · intro j' _ hj'
      refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun f _ => ?_
      simp [hj']
    · simp

private theorem sum_box_eq (c : Fin 6 → ℕ → ℕ → ℚ) {N₀ N₀' : ℕ} (hc : ∀ j e f, c j e f ≠ 0 → e < N₀ ∧ f < N₀')
    (N N' : ℕ) (hN : N₀ ≤ N) (hN' : N₀' ≤ N') :
    ∑ j, ∑ e ∈ Finset.range N, ∑ f ∈ Finset.range N', c j e f • term j e f
      = ∑ j, ∑ e ∈ Finset.range N₀, ∑ f ∈ Finset.range N₀', c j e f • term j e f := by
  refine Finset.sum_congr rfl fun j _ => ?_
  symm
  refine (Finset.sum_subset (Finset.range_subset_range.mpr hN) ?_).trans ?_
  · intro e _ he
    refine Finset.sum_eq_zero fun f _ => ?_
    have hce : c j e f = 0 := by
      by_contra h
      have h1 := (hc j e f h).1
      have h2 : N₀ ≤ e := by simpa using he
      omega
    rw [hce, zero_smul]
  · refine Finset.sum_congr rfl fun e _ => ?_
    refine Finset.sum_subset (Finset.range_subset_range.mpr hN') ?_
    intro f _ hf
    have hce : c j e f = 0 := by
      by_contra h
      have h1 := (hc j e f h).2
      have h2 : N₀' ≤ f := by simpa using hf
      omega
    rw [hce, zero_smul]

private theorem HasDecomp.mul_s₂ {n : ℕ} {p : MvPolynomial (Fin 2) ℚ} (hp : HasDecomp n p) :
    HasDecomp (n + 2) (s₂ * p) := by
  classical
  obtain ⟨c, hc, rfl⟩ := hp
  set c' : Fin 6 → ℕ → ℕ → ℚ := fun j e f => if e = 0 then 0 else c j (e - 1) f with hc'
  have hc'deg : ∀ j e f, c' j e f ≠ 0 → basisDeg j + 2 * e + 3 * f = n + 2 := by
    intro j e f h
    by_cases he : e = 0
    · simp [hc', he] at h
    · simp only [hc', if_neg he] at h
      have := hc j (e - 1) f h
      omega
  refine ⟨c', hc'deg, ?_⟩

  have hbox : ∀ j e f, c' j e f ≠ 0 → e < n + 1 + 1 ∧ f < n + 1 := by
    intro j e f h
    have := hc'deg j e f h
    by_cases he : e = 0
    · simp [hc', he] at h
    · simp only [hc', if_neg he] at h
      have := hc j (e - 1) f h
      omega
  rw [sum_box_eq c' hbox (n + 2 + 1) (n + 2 + 1) (by omega) (by omega)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.sum_range_succ' (fun e => ∑ f ∈ Finset.range (n + 1), c' j e f • term j e f)]
  have h0 : ∑ f ∈ Finset.range (n + 1), c' j 0 f • term j 0 f = 0 :=
    Finset.sum_eq_zero fun f _ => by simp [hc']
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hce : c' j (e + 1) f = c j e f := by simp [hc']
  rw [hce, mul_smul_comm]
  congr 1
  simp only [term, pow_succ]
  ring

private theorem HasDecomp.mul_s₃ {n : ℕ} {p : MvPolynomial (Fin 2) ℚ} (hp : HasDecomp n p) :
    HasDecomp (n + 3) (s₃ * p) := by
  classical
  obtain ⟨c, hc, rfl⟩ := hp
  set c' : Fin 6 → ℕ → ℕ → ℚ := fun j e f => if f = 0 then 0 else c j e (f - 1) with hc'
  have hc'deg : ∀ j e f, c' j e f ≠ 0 → basisDeg j + 2 * e + 3 * f = n + 3 := by
    intro j e f h
    by_cases hf : f = 0
    · simp [hc', hf] at h
    · simp only [hc', if_neg hf] at h
      have := hc j e (f - 1) h
      omega
  refine ⟨c', hc'deg, ?_⟩
  have hbox : ∀ j e f, c' j e f ≠ 0 → e < n + 1 ∧ f < n + 1 + 1 := by
    intro j e f h
    have := hc'deg j e f h
    by_cases hf : f = 0
    · simp [hc', hf] at h
    · simp only [hc', if_neg hf] at h
      have := hc j e (f - 1) h
      omega
  rw [sum_box_eq c' hbox (n + 3 + 1) (n + 3 + 1) (by omega) (by omega)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.mul_sum, Finset.sum_range_succ' (fun f => c' j e f • term j e f)]
  have h0 : c' j e 0 • term j e 0 = 0 := by simp [hc']
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hce : c' j e (f + 1) = c j e f := by simp [hc']
  rw [hce, mul_smul_comm]
  congr 1
  simp only [term, pow_succ]
  ring

private theorem X1_sq : (X 1 : MvPolynomial (Fin 2) ℚ) ^ 2 = (1 / 2 : ℚ) • s₂ - X 0 ^ 2 + X 0 * X 1 := by
  have h2 : (C (1 / 2 : ℚ) : MvPolynomial (Fin 2) ℚ) * 2 = 1 := by
    rw [show (2 : MvPolynomial (Fin 2) ℚ) = C 2 from (map_ofNat C 2).symm, ← C_mul]
    norm_num
  simp only [s₂, smul_eq_C_mul]
  linear_combination (-(X 0 ^ 2 - X 0 * X 1 + X 1 ^ 2 : MvPolynomial (Fin 2) ℚ)) * h2

private theorem X0_cube : (X 0 : MvPolynomial (Fin 2) ℚ) ^ 3 = (1 / 2 : ℚ) • (s₂ * X 0) + (1 / 3 : ℚ) • s₃ := by
  have h2 : (C (1 / 2 : ℚ) : MvPolynomial (Fin 2) ℚ) * 2 = 1 := by
    rw [show (2 : MvPolynomial (Fin 2) ℚ) = C 2 from (map_ofNat C 2).symm, ← C_mul]
    norm_num
  have h3 : (C (1 / 3 : ℚ) : MvPolynomial (Fin 2) ℚ) * 3 = 1 := by
    rw [show (3 : MvPolynomial (Fin 2) ℚ) = C 3 from (map_ofNat C 3).symm, ← C_mul]
    norm_num
  simp only [s₂, s₃, smul_eq_C_mul]
  linear_combination (-((X 0 ^ 2 - X 0 * X 1 + X 1 ^ 2) * X 0) : MvPolynomial (Fin 2) ℚ) * h2
    + (-(X 0 * X 1 * (X 0 - X 1)) : MvPolynomial (Fin 2) ℚ) * h3

private theorem hasDecomp_monomial (a b : ℕ) : HasDecomp (a + b) (X 0 ^ a * X 1 ^ b) := by

  suffices h : ∀ n, ∀ b a, a + b = n → HasDecomp n (X 0 ^ a * X 1 ^ b) from h _ b a rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro b
    induction b using Nat.strong_induction_on with
    | _ b ihb =>
      intro a hab
      rcases le_or_gt 2 b with hb | hb
      ·
        obtain ⟨b', rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
        have hsplit : (X 0 : MvPolynomial (Fin 2) ℚ) ^ a * X 1 ^ (b' + 2)
            = (1 / 2 : ℚ) • (s₂ * (X 0 ^ a * X 1 ^ b')) - X 0 ^ (a + 2) * X 1 ^ b'
              + X 0 ^ (a + 1) * X 1 ^ (b' + 1) := by
          rw [pow_add, ← mul_assoc, mul_comm (X 0 ^ a * X 1 ^ b'), X1_sq]
          simp only [smul_eq_C_mul]
          ring
        rw [hsplit]
        refine ((HasDecomp.smul _ ?_).sub ?_).add ?_
        · have h := (ihn (n - 2) (by omega) b' a (by omega)).mul_s₂
          rwa [show n - 2 + 2 = n by omega] at h
        · exact ihb b' (by omega) (a + 2) (by omega)
        · exact ihb (b' + 1) (by omega) (a + 1) (by omega)
      · rcases le_or_gt 3 a with ha | ha
        ·
          obtain ⟨a', rfl⟩ : ∃ a', a = a' + 3 := ⟨a - 3, by omega⟩
          have hsplit : (X 0 : MvPolynomial (Fin 2) ℚ) ^ (a' + 3) * X 1 ^ b
              = (1 / 2 : ℚ) • (s₂ * (X 0 ^ (a' + 1) * X 1 ^ b)) + (1 / 3 : ℚ) • (s₃ * (X 0 ^ a' * X 1 ^ b)) := by
            rw [pow_add, X0_cube]
            simp only [smul_eq_C_mul]
            ring
          rw [hsplit]
          refine (HasDecomp.smul _ ?_).add (HasDecomp.smul _ ?_)
          · have h := (ihn (n - 2) (by omega) b (a' + 1) (by omega)).mul_s₂
            rwa [show n - 2 + 2 = n by omega] at h
          · have h := (ihn (n - 3) (by omega) b a' (by omega)).mul_s₃
            rwa [show n - 3 + 3 = n by omega] at h
        ·
          have hj : ∃ j : Fin 6, basisExp j = (a, b) := by
            interval_cases a <;> interval_cases b
            exacts [⟨0, rfl⟩, ⟨2, rfl⟩, ⟨1, rfl⟩, ⟨4, rfl⟩, ⟨3, rfl⟩, ⟨5, rfl⟩]
          obtain ⟨j, hj⟩ := hj
          have hdeg : basisDeg j = n := by rw [basisDeg, hj]; exact hab
          have hmon : bmon j = X 0 ^ a * X 1 ^ b := by rw [bmon, hj]
          rw [← hmon, ← hdeg]
          exact hasDecomp_bmon j

private theorem HasDecomp.sum {n : ℕ} {s : Finset ℕ} {g : ℕ → MvPolynomial (Fin 2) ℚ}
    (h : ∀ a ∈ s, HasDecomp n (g a)) : HasDecomp n (∑ a ∈ s, g a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasDecomp.zero n
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun a' ha' => h a' (Finset.mem_insert_of_mem ha'))

private theorem hasDecomp_homogeneous (n : ℕ) (r : ℕ → ℚ) :
    HasDecomp n (∑ a ∈ Finset.range (n + 1), r a • (X 0 ^ a * X 1 ^ (n - a))) := by
  refine HasDecomp.sum fun a ha => HasDecomp.smul _ ?_
  have han : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  have h := hasDecomp_monomial a (n - a)
  rwa [Nat.add_sub_cancel' han] at h

end CoinvariantS3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

namespace HolonomicD2

open MvPolynomial Matrix

private abbrev Coef : Type := MvPolynomial (Fin 2) ℂ

private noncomputable def Coef.ev (p : Coef) (t₁ t₂ : ℝ) : ℂ :=
  MvPolynomial.eval ![Complex.exp t₁, Complex.exp t₂] p

private noncomputable def eul (i : Fin 2) (p : Coef) : Coef := X i * MvPolynomial.pderiv i p

private noncomputable def killX0 : Coef →ₐ[ℂ] Coef := MvPolynomial.aeval ![0, X 1]

private theorem eul_add (i : Fin 2) (p q : Coef) : eul i (p + q) = eul i p + eul i q := by
  simp only [eul, map_add, mul_add]
private theorem eul_smul (i : Fin 2) (c : ℂ) (p : Coef) : eul i (c • p) = c • eul i p := by
  simp only [eul, Derivation.map_smul, mul_smul_comm]
private theorem eul_mul (i : Fin 2) (p q : Coef) : eul i (p * q) = eul i p * q + p * eul i q := by
  simp only [eul, Derivation.leibniz, smul_eq_mul]
  ring
private theorem eul_C (i : Fin 2) (c : ℂ) : eul i (C c) = 0 := by
  simp [eul]
private theorem eul_X_pow (i : Fin 2) (n : ℕ) : eul i (X i ^ n) = (n : ℂ) • X i ^ n := by
  rcases n with _ | n
  · simp [eul]
  · simp only [eul, Derivation.leibniz_pow, pderiv_X_self, smul_eq_mul, mul_one, nsmul_eq_mul, Nat.add_sub_cancel,
      smul_eq_C_mul, map_natCast]
    push_cast
    ring
private theorem eul_comm (p : Coef) : eul 0 (eul 1 p) = eul 1 (eul 0 p) := by
  have hc : ⁅(pderiv 0 : Derivation ℂ Coef Coef), (pderiv 1 : Derivation ℂ Coef Coef)⁆ = 0 := by
    apply derivation_ext
    intro j
    fin_cases j <;> simp [Derivation.commutator_apply, pderiv_X]
  have hp : pderiv 0 (pderiv 1 p) = pderiv 1 (pderiv 0 p) := by
    have h : ⁅(pderiv 0 : Derivation ℂ Coef Coef), (pderiv 1 : Derivation ℂ Coef Coef)⁆ p
        = pderiv 0 (pderiv 1 p) - pderiv 1 (pderiv 0 p) := Derivation.commutator_apply p
    rw [hc, Derivation.zero_apply] at h
    exact sub_eq_zero.mp h.symm
  simp only [eul, Derivation.leibniz, smul_eq_mul]
  simp only [pderiv_X, Pi.single_apply, Fin.isValue, one_ne_zero, zero_ne_one, if_false, mul_zero, add_zero]
  rw [hp]
  ring
private theorem constantCoeff_eul (i : Fin 2) (p : Coef) : constantCoeff (eul i p) = 0 := by
  simp [eul]
private theorem killX0_eul0 (p : Coef) : killX0 (eul 0 p) = 0 := by
  simp [killX0, eul]
private theorem killX0_eul1 (p : Coef) : killX0 (eul 1 p) = eul 1 (killX0 p) := by
  have key : ∀ q : Coef, killX0 (pderiv 1 q) = pderiv 1 (killX0 q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => simp [killX0]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p j hp =>
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hp]
      fin_cases j <;> simp [killX0, pderiv_X]
  simp only [eul, map_mul, key]
  simp [killX0]

private theorem ev_add (p q : Coef) (t₁ t₂ : ℝ) : (p + q).ev t₁ t₂ = p.ev t₁ t₂ + q.ev t₁ t₂ := by
  simp [Coef.ev]
private theorem ev_mul (p q : Coef) (t₁ t₂ : ℝ) : (p * q).ev t₁ t₂ = p.ev t₁ t₂ * q.ev t₁ t₂ := by
  simp [Coef.ev]
private theorem ev_C (c : ℂ) (t₁ t₂ : ℝ) : Coef.ev (C c) t₁ t₂ = c := by
  simp [Coef.ev]
private theorem ev_X0 (t₁ t₂ : ℝ) : Coef.ev (X 0) t₁ t₂ = Complex.exp t₁ := by
  simp [Coef.ev]
private theorem ev_X1 (t₁ t₂ : ℝ) : Coef.ev (X 1) t₁ t₂ = Complex.exp t₂ := by
  simp [Coef.ev]
private theorem contDiff_ev (p : Coef) : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ × ℝ => p.ev t.1 t.2) := by
  simp only [Coef.ev]
  induction p using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p j hp =>
    simp only [map_mul, eval_X]
    refine hp.mul ?_
    fin_cases j
    · simpa [Function.comp_def] using Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.comp contDiff_fst)
    · simpa [Function.comp_def] using Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.comp contDiff_snd)
private theorem hasDerivAt_ev_eul0 (p : Coef) (t₁ t₂ : ℝ) :
    HasDerivAt (fun s => p.ev s t₂) ((eul 0 p).ev t₁ t₂) t₁ := by
  simp only [Coef.ev]
  induction p using MvPolynomial.induction_on with
  | C a => simpa [eul] using hasDerivAt_const t₁ a
  | add p q hp hq => simpa only [eul_add, map_add] using hp.fun_add hq
  | mul_X p j hp =>
    rw [eul_mul]
    simp only [map_add, map_mul]
    refine hp.mul ?_
    fin_cases j
    · simpa [eul, pderiv_X] using (Complex.hasDerivAt_exp (t₁ : ℂ)).comp_ofReal
    · simpa [eul, pderiv_X] using hasDerivAt_const t₁ (Complex.exp t₂)
private theorem hasDerivAt_ev_eul1 (p : Coef) (t₁ t₂ : ℝ) :
    HasDerivAt (fun s => p.ev t₁ s) ((eul 1 p).ev t₁ t₂) t₂ := by
  simp only [Coef.ev]
  induction p using MvPolynomial.induction_on with
  | C a => simpa [eul] using hasDerivAt_const t₂ a
  | add p q hp hq => simpa only [eul_add, map_add] using hp.fun_add hq
  | mul_X p j hp =>
    rw [eul_mul]
    simp only [map_add, map_mul]
    refine hp.mul ?_
    fin_cases j
    · simpa [eul, pderiv_X] using hasDerivAt_const t₂ (Complex.exp t₁)
    · simpa [eul, pderiv_X] using (Complex.hasDerivAt_exp (t₂ : ℂ)).comp_ofReal

private theorem Coef.eq_zero_of_ev (p : Coef) (h : ∀ t₁ t₂, p.ev t₁ t₂ = 0) : p = 0 := by
  have one : ∀ f : Polynomial ℂ, (∀ t : ℝ, f.eval (Complex.exp t) = 0) → f = 0 := by
    intro f hf
    refine Polynomial.eq_zero_of_infinite_isRoot f ?_
    have hinj : Function.Injective fun t : ℝ => Complex.exp t := by
      have : (fun t : ℝ => Complex.exp t) = fun t : ℝ => ((Real.exp t : ℝ) : ℂ) :=
        funext fun t => (Complex.ofReal_exp t).symm
      rw [this]
      exact Complex.ofReal_injective.comp Real.exp_injective
    exact Set.infinite_of_injective_forall_mem hinj fun t => hf t
  have hsub : ∀ (q : Coef) (a b : Polynomial ℂ) (w : ℂ),
      Polynomial.eval w (aeval ![a, b] q) = eval ![a.eval w, b.eval w] q := by
    intro q a b w
    induction q using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p j hp => fin_cases j <;> simp [hp]
  have step1 : ∀ (t₂ : ℝ) (z : ℂ), eval ![z, Complex.exp t₂] p = 0 := by
    intro t₂ z
    have h0 : aeval ![Polynomial.X, Polynomial.C (Complex.exp t₂)] p = 0 := by
      refine one _ fun t₁ => ?_
      rw [hsub]
      simpa [Coef.ev] using h t₁ t₂
    have := hsub p Polynomial.X (Polynomial.C (Complex.exp t₂)) z
    rw [h0] at this
    simpa using this.symm
  have step2 : ∀ z w : ℂ, eval ![z, w] p = 0 := by
    intro z w
    have h0 : aeval ![Polynomial.C z, Polynomial.X] p = 0 := by
      refine one _ fun t₂ => ?_
      rw [hsub]
      simpa using step1 t₂ z
    have := hsub p (Polynomial.C z) Polynomial.X w
    rw [h0] at this
    simpa using this.symm
  refine MvPolynomial.funext fun x => ?_
  have hx : x = ![x 0, x 1] := by
    ext j
    fin_cases j <;> rfl
  rw [hx, map_zero]
  exact step2 (x 0) (x 1)

private noncomputable def mev {ι : Type} [Fintype ι] [DecidableEq ι] (C : Matrix ι ι Coef) (t₁ t₂ : ℝ) : Matrix ι ι ℂ
    :=
  C.map fun p => p.ev t₁ t₂

section Functions

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private def Smooth2 (G : ℝ → ℝ → (ι → ℂ)) : Prop := ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ × ℝ => G t.1 t.2)

private noncomputable def _root_.HolonomicD2.d1 (G : ℝ → ℝ → (ι → ℂ)) : ℝ → ℝ → (ι → ℂ) := fun t₁ t₂ => deriv (fun s => G s t₂) t₁
p2m_export "HolonomicD2" "d1"
private noncomputable def _root_.HolonomicD2.d2 (G : ℝ → ℝ → (ι → ℂ)) : ℝ → ℝ → (ι → ℂ) := fun t₁ t₂ => deriv (fun s => G t₁ s) t₂

p2m_export "HolonomicD2" "d2"
private noncomputable def _root_.HolonomicD2.dIter (a b : ℕ) (G : ℝ → ℝ → (ι → ℂ)) : ℝ → ℝ → (ι → ℂ) := (d1^[a]) ((d2^[b]) G)

p2m_export "HolonomicD2" "dIter"
private theorem hasDerivAt_slice1 {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) (t₁ t₂ : ℝ) :
    HasDerivAt (fun s => G s t₂) (fderiv ℝ (fun t : ℝ × ℝ => G t.1 t.2) (t₁, t₂) (1, 0)) t₁ := by
  have hd : DifferentiableAt ℝ (fun t : ℝ × ℝ => G t.1 t.2) (t₁, t₂) :=
    (hG.differentiable (by simp)).differentiableAt
  have hl : HasDerivAt (fun s : ℝ => (s, t₂)) ((1 : ℝ), (0 : ℝ)) t₁ :=
    (hasDerivAt_id t₁).prodMk (hasDerivAt_const t₁ t₂)
  exact hd.hasFDerivAt.comp_hasDerivAt t₁ hl

private theorem hasDerivAt_slice2 {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) (t₁ t₂ : ℝ) :
    HasDerivAt (fun s => G t₁ s) (fderiv ℝ (fun t : ℝ × ℝ => G t.1 t.2) (t₁, t₂) (0, 1)) t₂ := by
  have hd : DifferentiableAt ℝ (fun t : ℝ × ℝ => G t.1 t.2) (t₁, t₂) :=
    (hG.differentiable (by simp)).differentiableAt
  have hl : HasDerivAt (fun s : ℝ => (t₁, s)) ((0 : ℝ), (1 : ℝ)) t₂ :=
    (hasDerivAt_const t₂ t₁).prodMk (hasDerivAt_id t₂)
  exact hd.hasFDerivAt.comp_hasDerivAt t₂ hl

private theorem d1_eq_fderiv {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) :
    d1 G = fun t₁ t₂ => fderiv ℝ (fun t : ℝ × ℝ => G t.1 t.2) (t₁, t₂) (1, 0) :=
  funext fun t₁ => funext fun t₂ => (hasDerivAt_slice1 hG t₁ t₂).deriv

private theorem d2_eq_fderiv {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) :
    d2 G = fun t₁ t₂ => fderiv ℝ (fun t : ℝ × ℝ => G t.1 t.2) (t₁, t₂) (0, 1) :=
  funext fun t₁ => funext fun t₂ => (hasDerivAt_slice2 hG t₁ t₂).deriv

private theorem smooth2_fderiv_apply {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) (v : ℝ × ℝ) :
    Smooth2 fun t₁ t₂ => fderiv ℝ (fun t : ℝ × ℝ => G t.1 t.2) (t₁, t₂) v := by
  have h := (contDiff_infty_iff_fderiv.mp hG).2
  exact h.clm_apply contDiff_const

private theorem Smooth2.d1 {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) : Smooth2 (d1 G) := by
  rw [d1_eq_fderiv hG]
  exact smooth2_fderiv_apply hG _
private theorem Smooth2.d2 {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) : Smooth2 (d2 G) := by
  rw [d2_eq_fderiv hG]
  exact smooth2_fderiv_apply hG _
private theorem smooth2_iterate_d1 {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) : ∀ n : ℕ, Smooth2 ((d1^[n]) G)
  | 0 => hG
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    exact (smooth2_iterate_d1 hG n).d1

private theorem smooth2_iterate_d2 {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) : ∀ n : ℕ, Smooth2 ((d2^[n]) G)
  | 0 => hG
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    exact (smooth2_iterate_d2 hG n).d2

private theorem Smooth2.dIter {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) (a b : ℕ) : Smooth2 (dIter a b G) := by
  exact smooth2_iterate_d1 (smooth2_iterate_d2 hG b) a
private theorem Smooth2.hasDerivAt_d1 {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) (t₁ t₂ : ℝ) :
    HasDerivAt (fun s => G s t₂) (HolonomicD2.d1 G t₁ t₂) t₁ := by
  exact (hasDerivAt_slice1 hG t₁ t₂).differentiableAt.hasDerivAt
private theorem Smooth2.hasDerivAt_d2 {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) (t₁ t₂ : ℝ) :
    HasDerivAt (fun s => G t₁ s) (HolonomicD2.d2 G t₁ t₂) t₂ := by
  exact (hasDerivAt_slice2 hG t₁ t₂).differentiableAt.hasDerivAt

private theorem Smooth2.d1_d2 {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) :
    HolonomicD2.d1 (HolonomicD2.d2 G) = HolonomicD2.d2 (HolonomicD2.d1 G) := by
  have hF := hG
  have hdiff : Differentiable ℝ (fderiv ℝ fun t : ℝ × ℝ => G t.1 t.2) :=
    (contDiff_infty_iff_fderiv.mp hF).2.differentiable (by simp)
  have key : ∀ (v w : ℝ × ℝ),
      (fun t₁ t₂ => fderiv ℝ (fun t : ℝ × ℝ => fderiv ℝ (fun t : ℝ × ℝ => G t.1 t.2) (t.1, t.2) w) (t₁, t₂) v)
        = fun t₁ t₂ => fderiv ℝ (fderiv ℝ fun t : ℝ × ℝ => G t.1 t.2) (t₁, t₂) v w := by
    intro v w
    funext t₁ t₂
    have h := fderiv_clm_apply (hdiff (t₁, t₂)) (differentiableAt_const w)
    simp only [Prod.mk.eta] at h ⊢
    rw [h]
    simp
  rw [d1_eq_fderiv hG.d2, d2_eq_fderiv hG.d1, d1_eq_fderiv hG, d2_eq_fderiv hG]
  simp only [Prod.mk.eta]
  rw [key, key]
  funext t₁ t₂
  have h2 : minSmoothness ℝ 2 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top
  exact (hG.contDiffAt.isSymmSndFDerivAt h2) (1, 0) (0, 1)
private theorem dIter_succ_left (a b : ℕ) (G : ℝ → ℝ → (ι → ℂ)) : dIter (a + 1) b G = d1 (dIter a b G) := by
  show (d1^[a + 1]) ((d2^[b]) G) = d1 ((d1^[a]) ((d2^[b]) G))
  exact Function.iterate_succ_apply' d1 a _
private theorem iterate_d1_d2 {H : ℝ → ℝ → (ι → ℂ)} (hH : Smooth2 H) :
    ∀ a : ℕ, (d1^[a]) (d2 H) = d2 ((d1^[a]) H)
  | 0 => rfl
  | a + 1 => by
    rw [Function.iterate_succ_apply', iterate_d1_d2 hH a, Function.iterate_succ_apply']
    exact (smooth2_iterate_d1 hH a).d1_d2

private theorem Smooth2.dIter_succ_right {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) (a b : ℕ) :
    HolonomicD2.dIter a (b + 1) G = HolonomicD2.d2 (HolonomicD2.dIter a b G) := by
  show (HolonomicD2.d1^[a]) ((HolonomicD2.d2^[b + 1]) G)
    = HolonomicD2.d2 ((HolonomicD2.d1^[a]) ((HolonomicD2.d2^[b]) G))
  rw [Function.iterate_succ_apply']
  exact iterate_d1_d2 (smooth2_iterate_d2 hG b) a
private theorem Smooth2.add {G H : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) (hH : Smooth2 H) :
    Smooth2 (fun t₁ t₂ => G t₁ t₂ + H t₁ t₂) := by
  exact ContDiff.add hG hH
private theorem mev_apply (C : Matrix ι ι Coef) (t₁ t₂ : ℝ) (i j : ι) : mev C t₁ t₂ i j = (C i j).ev t₁ t₂ := rfl

private theorem smooth2_component {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) (j : ι) :
    ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ × ℝ => G t.1 t.2 j :=
  (contDiff_pi.mp hG) j

private theorem Smooth2.mev_mulVec {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) (C : Matrix ι ι Coef) :
    Smooth2 (fun t₁ t₂ => mev C t₁ t₂ *ᵥ G t₁ t₂) := by
  unfold Smooth2
  refine contDiff_pi.mpr fun i => ?_
  simp only [Matrix.mulVec, dotProduct, mev_apply]
  exact ContDiff.sum fun j _ => (contDiff_ev (C i j)).mul (smooth2_component hG j)

private theorem d1_mev_mulVec {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) (C : Matrix ι ι Coef) :
    d1 (fun t₁ t₂ => mev C t₁ t₂ *ᵥ G t₁ t₂)
      = fun t₁ t₂ => mev (C.map (eul 0)) t₁ t₂ *ᵥ G t₁ t₂ + mev C t₁ t₂ *ᵥ d1 G t₁ t₂ := by
  funext t₁ t₂
  have hGd := hasDerivAt_pi.mp (hG.hasDerivAt_d1 t₁ t₂)
  have h : HasDerivAt (fun s => mev C s t₂ *ᵥ G s t₂)
      (mev (C.map (eul 0)) t₁ t₂ *ᵥ G t₁ t₂ + mev C t₁ t₂ *ᵥ d1 G t₁ t₂) t₁ := by
    refine hasDerivAt_pi.mpr fun i => ?_
    simp only [Matrix.mulVec, dotProduct, mev_apply, Matrix.map_apply, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact HasDerivAt.fun_sum fun j _ => (hasDerivAt_ev_eul0 (C i j) t₁ t₂).mul (hGd j)
  exact h.deriv
private theorem d2_mev_mulVec {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) (C : Matrix ι ι Coef) :
    d2 (fun t₁ t₂ => mev C t₁ t₂ *ᵥ G t₁ t₂)
      = fun t₁ t₂ => mev (C.map (eul 1)) t₁ t₂ *ᵥ G t₁ t₂ + mev C t₁ t₂ *ᵥ d2 G t₁ t₂ := by
  funext t₁ t₂
  have hGd := hasDerivAt_pi.mp (hG.hasDerivAt_d2 t₁ t₂)
  have h : HasDerivAt (fun s => mev C t₁ s *ᵥ G t₁ s)
      (mev (C.map (eul 1)) t₁ t₂ *ᵥ G t₁ t₂ + mev C t₁ t₂ *ᵥ d2 G t₁ t₂) t₂ := by
    refine hasDerivAt_pi.mpr fun i => ?_
    simp only [Matrix.mulVec, dotProduct, mev_apply, Matrix.map_apply, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact HasDerivAt.fun_sum fun j _ => (hasDerivAt_ev_eul1 (C i j) t₁ t₂).mul (hGd j)
  exact h.deriv

end Functions
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

private abbrev DOp (ι : Type) [Fintype ι] [DecidableEq ι] : Type := (ℕ × ℕ) →₀ Matrix ι ι Coef

section Operators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace DOp

private noncomputable def apply (D : DOp ι) (G : ℝ → ℝ → (ι → ℂ)) : ℝ → ℝ → (ι → ℂ) :=
  fun t₁ t₂ => D.sum fun ab C => mev C t₁ t₂ *ᵥ dIter ab.1 ab.2 G t₁ t₂

private noncomputable def cmul (C : Matrix ι ι Coef) (D : DOp ι) : DOp ι :=
  D.sum fun ab C' => Finsupp.single ab (C * C')

private noncomputable def cmap (f : Coef → Coef) (D : DOp ι) : DOp ι :=
  D.sum fun ab C => Finsupp.single ab (C.map f)

private noncomputable def one : DOp ι := Finsupp.single (0, 0) 1
private noncomputable def d₁ : DOp ι := Finsupp.single (1, 0) 1
private noncomputable def d₂ : DOp ι := Finsupp.single (0, 1) 1

private noncomputable def mono (a b : ℕ) : DOp ι := Finsupp.single (a, b) 1

private noncomputable def comp (D D' : DOp ι) : DOp ι :=
  D.sum fun ab C => D'.sum fun cd C' =>
    ∑ i ∈ Finset.range (ab.1 + 1), ∑ j ∈ Finset.range (ab.2 + 1),
      Finsupp.single (ab.1 - i + cd.1, ab.2 - j + cd.2)
        (((ab.1.choose i : ℕ) * (ab.2.choose j : ℕ) : ℂ) • (C * C'.map ((eul 0)^[i] ∘ (eul 1)^[j])))

private noncomputable def npow (D : DOp ι) (n : ℕ) : DOp ι := (comp D)^[n] one

private noncomputable def polyOp {N : ℕ} (a : Fin (N + 1) → ℂ) (D : DOp ι) : DOp ι := ∑ m : Fin (N + 1), a m • npow D m

private def HasOrder (D : DOp ι) (k : ℕ) : Prop := ∀ ab ∈ D.support, ab.1 + ab.2 ≤ k

private theorem mev_eq (C : Matrix ι ι Coef) (t₁ t₂ : ℝ) :
    mev C t₁ t₂ = (MvPolynomial.eval ![Complex.exp t₁, Complex.exp t₂]).mapMatrix C := rfl

private theorem mev_zero (t₁ t₂ : ℝ) : mev (0 : Matrix ι ι Coef) t₁ t₂ = 0 := by
  rw [mev_eq]; exact map_zero _

private theorem mev_add (C C' : Matrix ι ι Coef) (t₁ t₂ : ℝ) : mev (C + C') t₁ t₂ = mev C t₁ t₂ + mev C' t₁ t₂ := by
  simp only [mev_eq, map_add]

private theorem mev_mul (C C' : Matrix ι ι Coef) (t₁ t₂ : ℝ) : mev (C * C') t₁ t₂ = mev C t₁ t₂ * mev C' t₁ t₂ := by
  simp only [mev_eq, map_mul]

private theorem mev_one (t₁ t₂ : ℝ) : mev (1 : Matrix ι ι Coef) t₁ t₂ = 1 := by
  rw [mev_eq]; exact map_one _

private theorem mev_smul (c : ℂ) (C : Matrix ι ι Coef) (t₁ t₂ : ℝ) : mev (c • C) t₁ t₂ = c • mev C t₁ t₂ := by
  ext i j
  simp [mev, Coef.ev, MvPolynomial.smul_eval]

private theorem d1_add_fun {G H : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) (hH : Smooth2 H) :
    d1 (fun t₁ t₂ => G t₁ t₂ + H t₁ t₂) = fun t₁ t₂ => d1 G t₁ t₂ + d1 H t₁ t₂ :=
  funext fun t₁ => funext fun t₂ => ((hG.hasDerivAt_d1 t₁ t₂).add (hH.hasDerivAt_d1 t₁ t₂)).deriv

private theorem d2_add_fun {G H : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) (hH : Smooth2 H) :
    d2 (fun t₁ t₂ => G t₁ t₂ + H t₁ t₂) = fun t₁ t₂ => d2 G t₁ t₂ + d2 H t₁ t₂ :=
  funext fun t₁ => funext fun t₂ => ((hG.hasDerivAt_d2 t₁ t₂).add (hH.hasDerivAt_d2 t₁ t₂)).deriv

private theorem d1_smul_fun (c : ℂ) {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) :
    d1 (fun t₁ t₂ => c • G t₁ t₂) = fun t₁ t₂ => c • d1 G t₁ t₂ :=
  funext fun t₁ => funext fun t₂ => ((hG.hasDerivAt_d1 t₁ t₂).const_smul c).deriv

private theorem d2_smul_fun (c : ℂ) {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) :
    d2 (fun t₁ t₂ => c • G t₁ t₂) = fun t₁ t₂ => c • d2 G t₁ t₂ :=
  funext fun t₁ => funext fun t₂ => ((hG.hasDerivAt_d2 t₁ t₂).const_smul c).deriv

private theorem smooth2_add_fun {G H : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) (hH : Smooth2 H) :
    Smooth2 (fun t₁ t₂ => G t₁ t₂ + H t₁ t₂) := ContDiff.add hG hH

private theorem smooth2_smul_fun (c : ℂ) {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) :
    Smooth2 (fun t₁ t₂ => c • G t₁ t₂) := ContDiff.const_smul c hG

private theorem iterate_d2_add_fun {G H : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) (hH : Smooth2 H) :
    ∀ n : ℕ, (d2^[n]) (fun t₁ t₂ => G t₁ t₂ + H t₁ t₂) = fun t₁ t₂ => (d2^[n]) G t₁ t₂ + (d2^[n]) H t₁ t₂
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply', iterate_d2_add_fun hG hH n, Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    exact d2_add_fun (smooth2_iterate_d2 hG n) (smooth2_iterate_d2 hH n)

private theorem iterate_d1_add_fun {G H : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) (hH : Smooth2 H) :
    ∀ n : ℕ, (d1^[n]) (fun t₁ t₂ => G t₁ t₂ + H t₁ t₂) = fun t₁ t₂ => (d1^[n]) G t₁ t₂ + (d1^[n]) H t₁ t₂
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply', iterate_d1_add_fun hG hH n, Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    exact d1_add_fun (smooth2_iterate_d1 hG n) (smooth2_iterate_d1 hH n)

private theorem iterate_d2_smul_fun (c : ℂ) {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) :
    ∀ n : ℕ, (d2^[n]) (fun t₁ t₂ => c • G t₁ t₂) = fun t₁ t₂ => c • (d2^[n]) G t₁ t₂
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply', iterate_d2_smul_fun c hG n, Function.iterate_succ_apply']
    exact d2_smul_fun c (smooth2_iterate_d2 hG n)

private theorem iterate_d1_smul_fun (c : ℂ) {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) :
    ∀ n : ℕ, (d1^[n]) (fun t₁ t₂ => c • G t₁ t₂) = fun t₁ t₂ => c • (d1^[n]) G t₁ t₂
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply', iterate_d1_smul_fun c hG n, Function.iterate_succ_apply']
    exact d1_smul_fun c (smooth2_iterate_d1 hG n)

private theorem dIter_add_fun (a b : ℕ) {G H : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) (hH : Smooth2 H) :
    dIter a b (fun t₁ t₂ => G t₁ t₂ + H t₁ t₂) = fun t₁ t₂ => dIter a b G t₁ t₂ + dIter a b H t₁ t₂ := by
  simp only [dIter]
  rw [iterate_d2_add_fun hG hH b]
  exact iterate_d1_add_fun (smooth2_iterate_d2 hG b) (smooth2_iterate_d2 hH b) a

private theorem dIter_smul_fun (a b : ℕ) (c : ℂ) {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) :
    dIter a b (fun t₁ t₂ => c • G t₁ t₂) = fun t₁ t₂ => c • dIter a b G t₁ t₂ := by
  simp only [dIter]
  rw [iterate_d2_smul_fun c hG b]
  exact iterate_d1_smul_fun c (smooth2_iterate_d2 hG b) a

private theorem smooth2_finset_sum {κ : Type} (s : Finset κ) {F : κ → ℝ → ℝ → (ι → ℂ)}
    (h : ∀ x ∈ s, Smooth2 (F x)) : Smooth2 (fun t₁ t₂ => ∑ x ∈ s, F x t₁ t₂) :=
  ContDiff.sum fun x hx => h x hx

private theorem apply_add (D D' : DOp ι) (G : ℝ → ℝ → (ι → ℂ)) :
    apply (D + D') G = fun t₁ t₂ => apply D G t₁ t₂ + apply D' G t₁ t₂ := by
  funext t₁ t₂
  simp only [DOp.apply]
  exact Finsupp.sum_add_index' (fun ab => by simp [mev_zero]) (fun ab C₁ C₂ => by simp [mev_add, Matrix.add_mulVec])
private theorem apply_smul (c : ℂ) (D : DOp ι) (G : ℝ → ℝ → (ι → ℂ)) :
    apply (c • D) G = fun t₁ t₂ => c • apply D G t₁ t₂ := by
  funext t₁ t₂
  simp only [DOp.apply]
  rw [Finsupp.sum_smul_index' (fun ab => by simp [mev_zero]), Finsupp.smul_sum]
  simp only [mev_smul, Matrix.smul_mulVec]
private theorem apply_cmul (C : Matrix ι ι Coef) (D : DOp ι) (G : ℝ → ℝ → (ι → ℂ)) :
    apply (cmul C D) G = fun t₁ t₂ => mev C t₁ t₂ *ᵥ apply D G t₁ t₂ := by
  funext t₁ t₂
  simp only [DOp.apply, cmul]
  rw [Finsupp.sum_sum_index (fun ab => by simp [mev_zero]) (fun ab C₁ C₂ => by simp [mev_add, Matrix.add_mulVec])]
  simp only [Finsupp.sum_single_index, mev_zero, Matrix.zero_mulVec]
  simp only [Finsupp.sum, Matrix.mulVec_sum, mev_mul, Matrix.mulVec_mulVec]
private theorem apply_one (G : ℝ → ℝ → (ι → ℂ)) : apply one G = G := by
  funext t₁ t₂
  simp only [DOp.apply, one]
  rw [Finsupp.sum_single_index (by simp [mev_zero])]
  simp [mev_one, dIter]
private theorem apply_mono (a b : ℕ) (G : ℝ → ℝ → (ι → ℂ)) : apply (mono a b) G = dIter a b G := by
  funext t₁ t₂
  simp only [DOp.apply, mono]
  rw [Finsupp.sum_single_index (by simp [mev_zero])]
  simp [mev_one]
private theorem apply_add_fun (D : DOp ι) {G H : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) (hH : Smooth2 H) :
    apply D (fun t₁ t₂ => G t₁ t₂ + H t₁ t₂) = fun t₁ t₂ => apply D G t₁ t₂ + apply D H t₁ t₂ := by
  funext t₁ t₂
  simp only [DOp.apply]
  simp only [dIter_add_fun _ _ hG hH, Matrix.mulVec_add, Finsupp.sum_add]
private theorem apply_smul_fun (D : DOp ι) (c : ℂ) {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) :
    apply D (fun t₁ t₂ => c • G t₁ t₂) = fun t₁ t₂ => c • apply D G t₁ t₂ := by
  funext t₁ t₂
  simp only [DOp.apply]
  simp only [dIter_smul_fun _ _ c hG, Matrix.mulVec_smul, Finsupp.smul_sum]
namespace Smooth2
private theorem _root_.HolonomicD2.DOp.Smooth2.apply (D : DOp ι) {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) : Smooth2 (apply D G) := by
  show Smooth2 (fun t₁ t₂ => ∑ ab ∈ D.support, mev (D ab) t₁ t₂ *ᵥ dIter ab.1 ab.2 G t₁ t₂)
  exact smooth2_finset_sum D.support fun ab _ => (hG.dIter ab.1 ab.2).mev_mulVec (D ab)

end Smooth2
p2m_export "HolonomicD2.DOp" "Smooth2.apply"
private theorem apply_zero' (G : ℝ → ℝ → (ι → ℂ)) : DOp.apply (0 : DOp ι) G = fun _ _ => 0 := by
  funext t₁ t₂
  simp only [DOp.apply]
  exact Finsupp.sum_zero_index

private theorem apply_finset_sum {κ : Type} (s : Finset κ) (Ds : κ → DOp ι) (G : ℝ → ℝ → (ι → ℂ)) :
    DOp.apply (∑ x ∈ s, Ds x) G = fun t₁ t₂ => ∑ x ∈ s, DOp.apply (Ds x) G t₁ t₂ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using apply_zero' (ι := ι) G
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, apply_add, ih]
    funext t₁ t₂
    rw [Finset.sum_insert hx]

private theorem apply_single (p : ℕ × ℕ) (M : Matrix ι ι Coef) (G : ℝ → ℝ → (ι → ℂ)) :
    DOp.apply (Finsupp.single p M) G = fun t₁ t₂ => mev M t₁ t₂ *ᵥ dIter p.1 p.2 G t₁ t₂ := by
  funext t₁ t₂
  simp only [DOp.apply]
  exact Finsupp.sum_single_index (by simp [mev_zero])

private theorem smooth2_nsmul (m : ℕ) {H : ℝ → ℝ → (ι → ℂ)} (hH : Smooth2 H) :
    Smooth2 (fun t₁ t₂ => m • H t₁ t₂) := by
  have : (fun t₁ t₂ => m • H t₁ t₂) = fun t₁ t₂ => (m : ℂ) • H t₁ t₂ := by
    funext t₁ t₂; rw [Nat.cast_smul_eq_nsmul]
  rw [this]
  exact smooth2_smul_fun (m : ℂ) hH

private theorem d1_finset_sum {κ : Type} (s : Finset κ) {Φ : κ → ℝ → ℝ → (ι → ℂ)} (h : ∀ k ∈ s, Smooth2 (Φ k)) :
    d1 (fun t₁ t₂ => ∑ k ∈ s, Φ k t₁ t₂) = fun t₁ t₂ => ∑ k ∈ s, d1 (Φ k) t₁ t₂ :=
  funext fun t₁ => funext fun t₂ => (HasDerivAt.fun_sum fun k hk => (h k hk).hasDerivAt_d1 t₁ t₂).deriv

private theorem d2_finset_sum {κ : Type} (s : Finset κ) {Φ : κ → ℝ → ℝ → (ι → ℂ)} (h : ∀ k ∈ s, Smooth2 (Φ k)) :
    d2 (fun t₁ t₂ => ∑ k ∈ s, Φ k t₁ t₂) = fun t₁ t₂ => ∑ k ∈ s, d2 (Φ k) t₁ t₂ :=
  funext fun t₁ => funext fun t₂ => (HasDerivAt.fun_sum fun k hk => (h k hk).hasDerivAt_d2 t₁ t₂).deriv

private theorem d1_nsmul_fun (m : ℕ) {H : ℝ → ℝ → (ι → ℂ)} (hH : Smooth2 H) :
    d1 (fun t₁ t₂ => m • H t₁ t₂) = fun t₁ t₂ => m • d1 H t₁ t₂ := by
  have e : ∀ (K : ℝ → ℝ → (ι → ℂ)), (fun t₁ t₂ => m • K t₁ t₂) = fun t₁ t₂ => (m : ℂ) • K t₁ t₂ := fun K => by
    funext t₁ t₂; rw [Nat.cast_smul_eq_nsmul]
  rw [e, d1_smul_fun (m : ℂ) hH, ← e]

private theorem d2_nsmul_fun (m : ℕ) {H : ℝ → ℝ → (ι → ℂ)} (hH : Smooth2 H) :
    d2 (fun t₁ t₂ => m • H t₁ t₂) = fun t₁ t₂ => m • d2 H t₁ t₂ := by
  have e : ∀ (K : ℝ → ℝ → (ι → ℂ)), (fun t₁ t₂ => m • K t₁ t₂) = fun t₁ t₂ => (m : ℂ) • K t₁ t₂ := fun K => by
    funext t₁ t₂; rw [Nat.cast_smul_eq_nsmul]
  rw [e, d2_smul_fun (m : ℂ) hH, ← e]

private structure PartialData (δ : (ℝ → ℝ → (ι → ℂ)) → (ℝ → ℝ → (ι → ℂ))) (e : Coef → Coef) : Prop where
  smooth : ∀ (F : ℝ → ℝ → (ι → ℂ)), Smooth2 F → Smooth2 (δ F)
  prod : ∀ (C : Matrix ι ι Coef) (F : ℝ → ℝ → (ι → ℂ)), Smooth2 F →
    δ (fun t₁ t₂ => mev C t₁ t₂ *ᵥ F t₁ t₂)
      = fun t₁ t₂ => mev (C.map e) t₁ t₂ *ᵥ F t₁ t₂ + mev C t₁ t₂ *ᵥ δ F t₁ t₂
  sum : ∀ (κ : Type) (s : Finset κ) (Φ : κ → ℝ → ℝ → (ι → ℂ)), (∀ k ∈ s, Smooth2 (Φ k)) →
    δ (fun t₁ t₂ => ∑ k ∈ s, Φ k t₁ t₂) = fun t₁ t₂ => ∑ k ∈ s, δ (Φ k) t₁ t₂
  nsmul : ∀ (m : ℕ) (F : ℝ → ℝ → (ι → ℂ)), Smooth2 F →
    δ (fun t₁ t₂ => m • F t₁ t₂) = fun t₁ t₂ => m • δ F t₁ t₂

private theorem partialData_d1 : PartialData (ι := ι) d1 (eul 0) where
  smooth _ hF := hF.d1
  prod C _ hF := d1_mev_mulVec hF C
  sum _ s _ h := d1_finset_sum s h
  nsmul m _ hF := d1_nsmul_fun m hF

private theorem partialData_d2 : PartialData (ι := ι) d2 (eul 1) where
  smooth _ hF := hF.d2
  prod C _ hF := d2_mev_mulVec hF C
  sum _ s _ h := d2_finset_sum s h
  nsmul m _ hF := d2_nsmul_fun m hF

private theorem PartialData.iterate_smooth {δ : (ℝ → ℝ → (ι → ℂ)) → (ℝ → ℝ → (ι → ℂ))} {e : Coef → Coef}
    (hδ : PartialData δ e) {F : ℝ → ℝ → (ι → ℂ)} (hF : Smooth2 F) : ∀ n : ℕ, Smooth2 ((δ^[n]) F)
  | 0 => hF
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    exact hδ.smooth _ (hδ.iterate_smooth hF n)

private theorem PartialData.iterate_sum {δ : (ℝ → ℝ → (ι → ℂ)) → (ℝ → ℝ → (ι → ℂ))} {e : Coef → Coef}
    (hδ : PartialData δ e) {κ : Type} (s : Finset κ) {Φ : κ → ℝ → ℝ → (ι → ℂ)} (h : ∀ k ∈ s, Smooth2 (Φ k)) :
    ∀ n : ℕ, (δ^[n]) (fun t₁ t₂ => ∑ k ∈ s, Φ k t₁ t₂) = fun t₁ t₂ => ∑ k ∈ s, (δ^[n]) (Φ k) t₁ t₂
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply', hδ.iterate_sum s h n, hδ.sum _ s _ (fun k hk => hδ.iterate_smooth (h k hk) n)]
    funext t₁ t₂
    simp only [Function.iterate_succ_apply']

private theorem PartialData.iterate_nsmul {δ : (ℝ → ℝ → (ι → ℂ)) → (ℝ → ℝ → (ι → ℂ))} {e : Coef → Coef}
    (hδ : PartialData δ e) (m : ℕ) {F : ℝ → ℝ → (ι → ℂ)} (hF : Smooth2 F) :
    ∀ n : ℕ, (δ^[n]) (fun t₁ t₂ => m • F t₁ t₂) = fun t₁ t₂ => m • (δ^[n]) F t₁ t₂
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply', hδ.iterate_nsmul m hF n, hδ.nsmul m _ (hδ.iterate_smooth hF n)]
    funext t₁ t₂
    simp only [Function.iterate_succ_apply']

private theorem PartialData.leibniz {δ : (ℝ → ℝ → (ι → ℂ)) → (ℝ → ℝ → (ι → ℂ))} {e : Coef → Coef}
    (hδ : PartialData δ e) (C : Matrix ι ι Coef) {F : ℝ → ℝ → (ι → ℂ)} (hF : Smooth2 F) :
    ∀ n : ℕ, (δ^[n]) (fun t₁ t₂ => mev C t₁ t₂ *ᵥ F t₁ t₂)
      = fun t₁ t₂ => ∑ i ∈ Finset.range (n + 1), n.choose i • (mev (C.map (e^[i])) t₁ t₂ *ᵥ (δ^[n - i]) F t₁ t₂)
  | 0 => by
    funext t₁ t₂
    simp
  | n + 1 => by
    rw [Function.iterate_succ_apply', hδ.leibniz C hF n]
    have hterm : ∀ i ∈ Finset.range (n + 1),
        Smooth2 (fun t₁ t₂ => n.choose i • (mev (C.map (e^[i])) t₁ t₂ *ᵥ (δ^[n - i]) F t₁ t₂)) :=
      fun i _ => smooth2_nsmul _ ((hδ.iterate_smooth hF (n - i)).mev_mulVec _)
    rw [hδ.sum _ (Finset.range (n + 1)) _ hterm]
    funext t₁ t₂
    have hstep : ∀ i ∈ Finset.range (n + 1),
        δ (fun t₁ t₂ => n.choose i • (mev (C.map (e^[i])) t₁ t₂ *ᵥ (δ^[n - i]) F t₁ t₂)) t₁ t₂
          = n.choose i • (mev (C.map (e^[i + 1])) t₁ t₂ *ᵥ (δ^[n - i]) F t₁ t₂)
            + n.choose i • (mev (C.map (e^[i])) t₁ t₂ *ᵥ (δ^[n + 1 - i]) F t₁ t₂) := by
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [hδ.nsmul _ _ ((hδ.iterate_smooth hF (n - i)).mev_mulVec _), hδ.prod _ _ (hδ.iterate_smooth hF (n - i))]
      simp only [Matrix.map_map, Nat.sub_add_comm hi', Function.iterate_succ_apply', Function.iterate_succ', smul_add]
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_choose_succ_nsmul
      (fun i j => mev (C.map (e^[i])) t₁ t₂ *ᵥ (δ^[j]) F t₁ t₂) n, add_comm]

private theorem iterate_d2_iterate_d1 {H : ℝ → ℝ → (ι → ℂ)} (hH : Smooth2 H) (c : ℕ) :
    ∀ b : ℕ, (d2^[b]) ((d1^[c]) H) = (d1^[c]) ((d2^[b]) H)
  | 0 => rfl
  | b + 1 => by
    rw [Function.iterate_succ_apply', iterate_d2_iterate_d1 hH c b, Function.iterate_succ_apply',
      iterate_d1_d2 (smooth2_iterate_d2 hH b) c]

private theorem dIter_dIter (a b c d : ℕ) {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) :
    dIter a b (dIter c d G) = dIter (a + c) (b + d) G := by
  simp only [dIter]
  rw [iterate_d2_iterate_d1 (smooth2_iterate_d2 hG d) c b, ← Function.iterate_add_apply,
    ← Function.iterate_add_apply]

private theorem dIter_finset_sum (a b : ℕ) {κ : Type} (s : Finset κ) {Φ : κ → ℝ → ℝ → (ι → ℂ)}
    (h : ∀ k ∈ s, Smooth2 (Φ k)) :
    dIter a b (fun t₁ t₂ => ∑ k ∈ s, Φ k t₁ t₂) = fun t₁ t₂ => ∑ k ∈ s, dIter a b (Φ k) t₁ t₂ := by
  simp only [dIter]
  rw [partialData_d2.iterate_sum s h b]
  exact partialData_d1.iterate_sum s (fun k hk => partialData_d2.iterate_smooth (h k hk) b) a

private theorem dIter_mev_mulVec (a b : ℕ) (C : Matrix ι ι Coef) {F : ℝ → ℝ → (ι → ℂ)} (hF : Smooth2 F) :
    dIter a b (fun t₁ t₂ => mev C t₁ t₂ *ᵥ F t₁ t₂)
      = fun t₁ t₂ => ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          a.choose i • b.choose j •
            (mev (C.map ((eul 0)^[i] ∘ (eul 1)^[j])) t₁ t₂ *ᵥ dIter (a - i) (b - j) F t₁ t₂) := by
  simp only [dIter]
  rw [partialData_d2.leibniz C hF b]
  have hterm : ∀ j ∈ Finset.range (b + 1),
      Smooth2 (fun t₁ t₂ => b.choose j • (mev (C.map ((eul 1)^[j])) t₁ t₂ *ᵥ (d2^[b - j]) F t₁ t₂)) :=
    fun j _ => smooth2_nsmul _ ((smooth2_iterate_d2 hF (b - j)).mev_mulVec _)
  rw [partialData_d1.iterate_sum (Finset.range (b + 1)) hterm a]
  funext t₁ t₂
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [partialData_d1.iterate_nsmul _ ((smooth2_iterate_d2 hF (b - j)).mev_mulVec _) a,
    partialData_d1.leibniz _ (smooth2_iterate_d2 hF (b - j)) a]
  simp only [Finset.smul_sum, Matrix.map_map]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm]

private theorem comp_leaf (a b i j : ℕ) (C C' : Matrix ι ι Coef) (W : ℝ → ℝ → (ι → ℂ)) (t₁ t₂ : ℝ) :
    mev (((a.choose i : ℕ) * (b.choose j : ℕ) : ℂ) • (C * C'.map ((eul 0)^[i] ∘ (eul 1)^[j]))) t₁ t₂ *ᵥ W t₁ t₂
      = mev C t₁ t₂ *ᵥ (a.choose i • b.choose j • (mev (C'.map ((eul 0)^[i] ∘ (eul 1)^[j])) t₁ t₂ *ᵥ W t₁ t₂)) := by
  simp only [← Nat.cast_smul_eq_nsmul ℂ, Matrix.mulVec_smul, mev_smul, mev_mul, Matrix.smul_mulVec,
    Matrix.mulVec_mulVec, smul_smul]

private theorem apply_comp (D D' : DOp ι) {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) :
    apply (comp D D') G = apply D (apply D' G) := by
  have hL : DOp.apply (comp D D') G = fun t₁ t₂ => ∑ ab ∈ D.support, ∑ cd ∈ D'.support,
      ∑ i ∈ Finset.range (ab.1 + 1), ∑ j ∈ Finset.range (ab.2 + 1),
        mev (((ab.1.choose i : ℕ) * (ab.2.choose j : ℕ) : ℂ) • (D ab * (D' cd).map ((eul 0)^[i] ∘ (eul 1)^[j])))
            t₁ t₂ *ᵥ dIter (ab.1 - i + cd.1) (ab.2 - j + cd.2) G t₁ t₂ := by
    simp only [comp, Finsupp.sum, apply_finset_sum, apply_single]
  have hR : DOp.apply D (DOp.apply D' G) = fun t₁ t₂ => ∑ ab ∈ D.support, ∑ cd ∈ D'.support,
      ∑ i ∈ Finset.range (ab.1 + 1), ∑ j ∈ Finset.range (ab.2 + 1),
        mev (D ab) t₁ t₂ *ᵥ (ab.1.choose i • ab.2.choose j •
          (mev ((D' cd).map ((eul 0)^[i] ∘ (eul 1)^[j])) t₁ t₂ *ᵥ
            dIter (ab.1 - i + cd.1) (ab.2 - j + cd.2) G t₁ t₂)) := by
    have hinner : DOp.apply D' G = fun t₁ t₂ => ∑ cd ∈ D'.support, mev (D' cd) t₁ t₂ *ᵥ dIter cd.1 cd.2 G t₁ t₂ := rfl
    funext t₁ t₂
    simp only [DOp.apply, Finsupp.sum] at hinner ⊢
    rw [hinner]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [dIter_finset_sum _ _ _ (fun cd _ => (hG.dIter cd.1 cd.2).mev_mulVec _), Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun cd _ => ?_
    rw [dIter_mev_mulVec _ _ _ (hG.dIter cd.1 cd.2)]
    simp only [Matrix.mulVec_sum, dIter_dIter _ _ _ _ hG]
  rw [hL, hR]
  funext t₁ t₂
  refine Finset.sum_congr rfl fun ab _ => Finset.sum_congr rfl fun cd _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  exact comp_leaf ab.1 ab.2 i j (D ab) (D' cd) _ t₁ t₂

private noncomputable def expTest (l m : ℂ) (v : ι → ℂ) : ℝ → ℝ → (ι → ℂ) :=
  fun t₁ t₂ i => Complex.exp (l * t₁ + m * t₂) * v i

private theorem expTest_eq (l m : ℂ) (v : ι → ℂ) (t₁ t₂ : ℝ) :
    expTest l m v t₁ t₂ = Complex.exp (l * t₁ + m * t₂) • v := rfl

private theorem smooth2_expTest (l m : ℂ) (v : ι → ℂ) : Smooth2 (expTest l m v) := by
  unfold Smooth2 expTest
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ × ℝ => l * (t.1 : ℂ) + m * (t.2 : ℂ) :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_fst)).add
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_snd))
  exact contDiff_pi.mpr fun i => (Complex.contDiff_exp.comp h1).mul contDiff_const

private theorem d1_expTest (l m : ℂ) (v : ι → ℂ) : d1 (expTest l m v) = fun t₁ t₂ => l • expTest l m v t₁ t₂ := by
  funext t₁ t₂
  have h : HasDerivAt (fun s : ℝ => expTest l m v s t₂) (l • expTest l m v t₁ t₂) t₁ := by
    refine hasDerivAt_pi.mpr fun i => ?_
    have hi := ((((Complex.ofRealCLM.hasDerivAt (x := t₁)).const_mul l).add_const (m * (t₂ : ℂ))).cexp).mul_const (v i)
    refine hi.congr_deriv ?_
    simp only [expTest, Pi.smul_apply, smul_eq_mul, Complex.ofRealCLM_apply, Complex.ofReal_one]
    ring
  exact h.deriv

private theorem d2_expTest (l m : ℂ) (v : ι → ℂ) : d2 (expTest l m v) = fun t₁ t₂ => m • expTest l m v t₁ t₂ := by
  funext t₁ t₂
  have h : HasDerivAt (fun s : ℝ => expTest l m v t₁ s) (m • expTest l m v t₁ t₂) t₂ := by
    refine hasDerivAt_pi.mpr fun i => ?_
    have hi := ((((Complex.ofRealCLM.hasDerivAt (x := t₂)).const_mul m).const_add (l * (t₁ : ℂ))).cexp).mul_const (v i)
    refine hi.congr_deriv ?_
    simp only [expTest, Pi.smul_apply, smul_eq_mul, Complex.ofRealCLM_apply, Complex.ofReal_one]
    ring
  exact h.deriv

private theorem iterate_d1_expTest (l m : ℂ) (v : ι → ℂ) :
    ∀ a : ℕ, (d1^[a]) (expTest l m v) = fun t₁ t₂ => l ^ a • expTest l m v t₁ t₂
  | 0 => by funext t₁ t₂; simp
  | a + 1 => by
    rw [Function.iterate_succ_apply', iterate_d1_expTest l m v a, d1_smul_fun _ (smooth2_expTest l m v), d1_expTest]
    funext t₁ t₂
    simp only [smul_smul, pow_succ]

private theorem iterate_d2_expTest (l m : ℂ) (v : ι → ℂ) :
    ∀ b : ℕ, (d2^[b]) (expTest l m v) = fun t₁ t₂ => m ^ b • expTest l m v t₁ t₂
  | 0 => by funext t₁ t₂; simp
  | b + 1 => by
    rw [Function.iterate_succ_apply', iterate_d2_expTest l m v b, d2_smul_fun _ (smooth2_expTest l m v), d2_expTest]
    funext t₁ t₂
    simp only [smul_smul, pow_succ]

private theorem dIter_expTest (a b : ℕ) (l m : ℂ) (v : ι → ℂ) :
    dIter a b (expTest l m v) = fun t₁ t₂ => (l ^ a * m ^ b) • expTest l m v t₁ t₂ := by
  simp only [dIter]
  rw [iterate_d2_expTest, iterate_d1_smul_fun _ (smooth2_expTest l m v), iterate_d1_expTest]
  funext t₁ t₂
  simp only [smul_smul, mul_comm]

private theorem apply_expTest (D : DOp ι) (l m : ℂ) (v : ι → ℂ) (t₁ t₂ : ℝ) :
    DOp.apply D (expTest l m v) t₁ t₂
      = Complex.exp (l * t₁ + m * t₂) • ∑ ab ∈ D.support, (l ^ ab.1 * m ^ ab.2) • (mev (D ab) t₁ t₂ *ᵥ v) := by
  simp only [DOp.apply, Finsupp.sum, dIter_expTest, expTest_eq, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, smul_comm]

private noncomputable def expIdx (ab : ℕ × ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 ab.1 + Finsupp.single 1 ab.2

private theorem expIdx_injective : Function.Injective expIdx := by
  intro x y h
  have h0 := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
  have h1 := congrArg (fun f : Fin 2 →₀ ℕ => f 1) h
  simp [expIdx] at h0 h1
  exact Prod.ext h0 h1

private theorem eval_monomial_expIdx (l m : ℂ) (ab : ℕ × ℕ) (c : ℂ) :
    MvPolynomial.eval ![l, m] (MvPolynomial.monomial (expIdx ab) c) = c * (l ^ ab.1 * m ^ ab.2) := by
  rw [MvPolynomial.eval_monomial, expIdx, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  simp

private theorem coeffs_eq_zero_of_forall (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ)
    (h : ∀ l m : ℂ, ∑ ab ∈ s, (l ^ ab.1 * m ^ ab.2) * c ab = 0) : ∀ ab ∈ s, c ab = 0 := by
  classical
  set p : MvPolynomial (Fin 2) ℂ := ∑ ab ∈ s, MvPolynomial.monomial (expIdx ab) (c ab) with hp
  have hp0 : p = 0 := by
    apply MvPolynomial.funext
    intro x
    have hx : x = ![x 0, x 1] := by
      funext i; fin_cases i <;> rfl
    rw [hx, hp, map_sum, map_zero]
    simp only [eval_monomial_expIdx]
    rw [← h (x 0) (x 1)]
    exact Finset.sum_congr rfl fun ab _ => mul_comm _ _
  intro ab hab
  have hc := congrArg (MvPolynomial.coeff (expIdx ab)) hp0
  rw [hp, MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at hc
  simp only [MvPolynomial.coeff_monomial, expIdx_injective.eq_iff] at hc
  rwa [Finset.sum_ite_eq' s ab, if_pos hab] at hc

private theorem mev_eq_zero_of_forall_mulVec (M : Matrix ι ι Coef) (t₁ t₂ : ℝ)
    (h : ∀ v : ι → ℂ, mev M t₁ t₂ *ᵥ v = 0) : mev M t₁ t₂ = 0 := by
  refine Matrix.ext fun i j => ?_
  have hj := congrFun (h (Pi.single j 1)) i
  rwa [Matrix.mulVec_single_one] at hj

private theorem eq_zero_of_forall_mev (M : Matrix ι ι Coef) (h : ∀ t₁ t₂, mev M t₁ t₂ = 0) : M = 0 := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.zero_apply]
  apply Coef.eq_zero_of_ev
  intro t₁ t₂
  have := congrFun (congrFun (h t₁ t₂) i) j
  simpa [mev] using this

private theorem faithful' (D : DOp ι)
    (h : ∀ G : ℝ → ℝ → (ι → ℂ), Smooth2 G → DOp.apply D G = fun _ _ => 0) : D = 0 := by

  have key : ∀ ab ∈ D.support, ∀ (t₁ t₂ : ℝ) (v : ι → ℂ) (i : ι), (mev (D ab) t₁ t₂ *ᵥ v) i = 0 := by
    intro ab hab t₁ t₂ v i
    refine coeffs_eq_zero_of_forall D.support (fun ab => (mev (D ab) t₁ t₂ *ᵥ v) i) (fun l m => ?_) ab hab
    have h1 := congrFun (congrFun (h (expTest l m v) (smooth2_expTest l m v)) t₁) t₂
    rw [apply_expTest] at h1
    have h2 := (smul_eq_zero.mp h1).resolve_left (Complex.exp_ne_zero _)
    have h3 := congrFun h2 i
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h3
  refine Finsupp.ext fun ab => ?_
  rw [Finsupp.coe_zero, Pi.zero_apply]
  by_cases hab : ab ∈ D.support
  · apply eq_zero_of_forall_mev
    intro t₁ t₂
    apply mev_eq_zero_of_forall_mulVec
    intro v
    funext i
    exact key ab hab t₁ t₂ v i
  · exact Finsupp.notMem_support_iff.mp hab

private theorem ext_of_apply {D D' : DOp ι}
    (h : ∀ G : ℝ → ℝ → (ι → ℂ), Smooth2 G → DOp.apply D G = DOp.apply D' G) : D = D' := by
  refine sub_eq_zero.mp (faithful' (D - D') fun G hG => ?_)
  rw [sub_eq_add_neg, apply_add, ← neg_one_smul ℂ D', apply_smul, h G hG]
  funext t₁ t₂
  simp

private theorem apply_d₁ (G : ℝ → ℝ → (ι → ℂ)) : DOp.apply d₁ G = d1 G := by
  rw [show (d₁ : DOp ι) = mono 1 0 from rfl, apply_mono]
  rfl

private theorem apply_d₂ (G : ℝ → ℝ → (ι → ℂ)) : DOp.apply d₂ G = d2 G := by
  rw [show (d₂ : DOp ι) = mono 0 1 from rfl, apply_mono]
  rfl

private theorem comp_assoc (D D' D'' : DOp ι) : comp (comp D D') D'' = comp D (comp D' D'') := by
  refine ext_of_apply fun G hG => ?_
  rw [apply_comp _ _ hG, apply_comp _ _ (Smooth2.apply D'' hG), apply_comp _ _ hG, apply_comp _ _ hG]
private theorem one_comp (D : DOp ι) : comp one D = D := by
  refine ext_of_apply fun G hG => ?_
  rw [apply_comp _ _ hG, apply_one]
private theorem comp_one (D : DOp ι) : comp D one = D := by
  refine ext_of_apply fun G hG => ?_
  rw [apply_comp _ _ hG, apply_one]
private theorem comp_add (D D' D'' : DOp ι) : comp D (D' + D'') = comp D D' + comp D D'' := by
  refine ext_of_apply fun G hG => ?_
  rw [apply_comp _ _ hG, apply_add, apply_add, apply_comp _ _ hG, apply_comp _ _ hG,
    apply_add_fun _ (Smooth2.apply D' hG) (Smooth2.apply D'' hG)]
private theorem add_comp (D D' D'' : DOp ι) : comp (D + D') D'' = comp D D'' + comp D' D'' := by
  refine ext_of_apply fun G hG => ?_
  rw [apply_comp _ _ hG, apply_add, apply_add, apply_comp _ _ hG, apply_comp _ _ hG]
private theorem comp_smul (c : ℂ) (D D' : DOp ι) : comp D (c • D') = c • comp D D' := by
  refine ext_of_apply fun G hG => ?_
  rw [apply_comp _ _ hG, apply_smul, apply_smul, apply_comp _ _ hG, apply_smul_fun _ _ (Smooth2.apply D' hG)]
private theorem smul_comp (c : ℂ) (D D' : DOp ι) : comp (c • D) D' = c • comp D D' := by
  refine ext_of_apply fun G hG => ?_
  rw [apply_comp _ _ hG, apply_smul, apply_smul, apply_comp _ _ hG]
private theorem cmul_comp (C : Matrix ι ι Coef) (D D' : DOp ι) : comp (cmul C D) D' = cmul C (comp D D') := by
  refine ext_of_apply fun G hG => ?_
  rw [apply_comp _ _ hG, apply_cmul, apply_cmul, apply_comp _ _ hG]
private theorem cmul_cmul (C C' : Matrix ι ι Coef) (D : DOp ι) : cmul C (cmul C' D) = cmul (C * C') D := by
  refine ext_of_apply fun G hG => ?_
  rw [apply_cmul, apply_cmul, apply_cmul]
  funext t₁ t₂
  rw [Matrix.mulVec_mulVec, mev_mul]
private theorem cmul_add (C : Matrix ι ι Coef) (D D' : DOp ι) : cmul C (D + D') = cmul C D + cmul C D' := by
  refine ext_of_apply fun G hG => ?_
  rw [apply_cmul, apply_add, apply_add, apply_cmul, apply_cmul]
  funext t₁ t₂
  rw [Matrix.mulVec_add]
private theorem add_cmul (C C' : Matrix ι ι Coef) (D : DOp ι) : cmul (C + C') D = cmul C D + cmul C' D := by
  refine ext_of_apply fun G hG => ?_
  rw [apply_cmul, apply_add, apply_cmul, apply_cmul]
  funext t₁ t₂
  rw [mev_add, Matrix.add_mulVec]
private theorem cmul_one_eq (D : DOp ι) : cmul 1 D = D := by
  simp only [cmul, one_mul]
  exact Finsupp.sum_single D

private theorem d₁_comp_cmul (C : Matrix ι ι Coef) (D : DOp ι) :
    comp d₁ (cmul C D) = cmul (C.map (eul 0)) D + cmul C (comp d₁ D) := by
  refine ext_of_apply fun G hG => ?_
  rw [apply_comp _ _ hG, apply_d₁, apply_cmul, apply_add, apply_cmul, apply_cmul, apply_comp _ _ hG, apply_d₁,
    d1_mev_mulVec (Smooth2.apply D hG)]
private theorem d₂_comp_cmul (C : Matrix ι ι Coef) (D : DOp ι) :
    comp d₂ (cmul C D) = cmul (C.map (eul 1)) D + cmul C (comp d₂ D) := by
  refine ext_of_apply fun G hG => ?_
  rw [apply_comp _ _ hG, apply_d₂, apply_cmul, apply_add, apply_cmul, apply_cmul, apply_comp _ _ hG, apply_d₂,
    d2_mev_mulVec (Smooth2.apply D hG)]
private theorem d₁_comp_d₂ : comp (d₁ : DOp ι) d₂ = comp d₂ d₁ := by
  refine ext_of_apply fun G hG => ?_
  rw [apply_comp _ _ hG, apply_comp _ _ hG, apply_d₁, apply_d₂, apply_d₁, apply_d₂, hG.d1_d2]
private theorem mono_comp_mono (a b c d : ℕ) : comp (mono a b : DOp ι) (mono c d) = mono (a + c) (b + d) := by
  refine ext_of_apply fun G hG => ?_
  rw [apply_comp _ _ hG, apply_mono, apply_mono, apply_mono, dIter_dIter _ _ _ _ hG]
private theorem d₁_eq_mono : (d₁ : DOp ι) = mono 1 0 := by
  rfl
private theorem d₂_eq_mono : (d₂ : DOp ι) = mono 0 1 := by
  rfl
private theorem one_eq_mono : (one : DOp ι) = mono 0 0 := by
  rfl

private theorem support_sum_single_subset (D : DOp ι) (f : ℕ × ℕ → Matrix ι ι Coef → Matrix ι ι Coef) :
    (D.sum fun ab M => Finsupp.single ab (f ab M)).support ⊆ D.support := by
  intro x hx
  obtain ⟨ab, hab, hx⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hx)
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hx)]
  exact hab

private theorem exists_of_mem_support_comp {D D' : DOp ι} {x : ℕ × ℕ} (hx : x ∈ (comp D D').support) :
    ∃ ab ∈ D.support, ∃ cd ∈ D'.support, ∃ i ≤ ab.1, ∃ j ≤ ab.2, x = (ab.1 - i + cd.1, ab.2 - j + cd.2) := by
  obtain ⟨ab, hab, hx⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hx)
  obtain ⟨cd, hcd, hx⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hx)
  obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp (Finsupp.support_finset_sum hx)
  obtain ⟨j, hj, hx⟩ := Finset.mem_biUnion.mp (Finsupp.support_finset_sum hx)
  refine ⟨ab, hab, cd, hcd, i, Nat.lt_succ_iff.mp (Finset.mem_range.mp hi), j,
    Nat.lt_succ_iff.mp (Finset.mem_range.mp hj), ?_⟩
  exact Finset.mem_singleton.mp (Finsupp.support_single_subset hx)

private theorem HasOrder.mono_le {D : DOp ι} {k k' : ℕ} (h : HasOrder D k) (hk : k ≤ k') : HasOrder D k' := by
  intro ab hab
  exact (h ab hab).trans hk
private theorem HasOrder.add {D D' : DOp ι} {k : ℕ} (h : HasOrder D k) (h' : HasOrder D' k) : HasOrder (D + D') k := by
  intro ab hab
  rcases Finset.mem_union.mp (Finsupp.support_add hab) with hab | hab
  · exact h ab hab
  · exact h' ab hab
private theorem HasOrder.smul {D : DOp ι} {k : ℕ} (c : ℂ) (h : HasOrder D k) : HasOrder (c • D) k := by
  intro ab hab
  exact h ab (Finsupp.support_smul hab)
private theorem HasOrder.cmul {D : DOp ι} {k : ℕ} (C : Matrix ι ι Coef) (h : HasOrder D k) : HasOrder (cmul C D) k :=
    by
  intro ab hab
  exact h ab (support_sum_single_subset D _ hab)
private theorem hasOrder_mono (a b : ℕ) : HasOrder (mono a b : DOp ι) (a + b) := by
  intro ab hab
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hab)]
private theorem HasOrder.comp {D D' : DOp ι} {k k' : ℕ} (h : HasOrder D k) (h' : HasOrder D' k') :
    HasOrder (comp D D') (k + k') := by
  intro x hx
  obtain ⟨ab, hab, cd, hcd, i, hi, j, hj, rfl⟩ := exists_of_mem_support_comp hx
  have h1 := h ab hab
  have h2 := h' cd hcd
  beta_reduce
  omega

private theorem comp_apply_top {D D' : DOp ι} {k k' : ℕ} (h : HasOrder D k) (h' : HasOrder D' k') (a b : ℕ)
    (hab : a + b = k + k') :
    comp D D' (a, b) = ∑ a' ∈ Finset.range (a + 1), ∑ b' ∈ Finset.range (b + 1),
      if a' + b' = k then D (a', b') * D' (a - a', b - b') else 0 := by
  classical

  have hunf : comp D D' (a, b) = ∑ ab ∈ D.support, ∑ cd ∈ D'.support,
      ∑ i ∈ Finset.range (ab.1 + 1), ∑ j ∈ Finset.range (ab.2 + 1),
        if (ab.1 - i + cd.1, ab.2 - j + cd.2) = (a, b) then
          ((ab.1.choose i : ℕ) * (ab.2.choose j : ℕ) : ℂ) •
            (D ab * (D' cd).map ((eul 0)^[i] ∘ (eul 1)^[j])) else 0 := by
    simp only [comp, Finsupp.sum, Finsupp.finset_sum_apply, Finsupp.single_apply]

  have hinner : ∀ ab ∈ D.support, ∀ cd ∈ D'.support,
      (∑ i ∈ Finset.range (ab.1 + 1), ∑ j ∈ Finset.range (ab.2 + 1),
        if (ab.1 - i + cd.1, ab.2 - j + cd.2) = (a, b) then
          ((ab.1.choose i : ℕ) * (ab.2.choose j : ℕ) : ℂ) • (D ab * (D' cd).map ((eul 0)^[i] ∘ (eul 1)^[j])) else 0)
        = if (ab.1 + cd.1, ab.2 + cd.2) = (a, b) then D ab * D' cd else 0 := by
    intro ab habs cd hcds
    have h1 := h ab habs
    have h2 := h' cd hcds
    have hzero : ∀ i ∈ Finset.range (ab.1 + 1), ∀ j ∈ Finset.range (ab.2 + 1), 0 < i + j →
        (ab.1 - i + cd.1, ab.2 - j + cd.2) ≠ (a, b) := by
      intro i hi j hj hij heq
      have hi' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hj' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have := congrArg (fun p : ℕ × ℕ => p.1 + p.2) heq
      beta_reduce at this
      omega
    rw [Finset.sum_eq_single 0]
    · rw [Finset.sum_eq_single 0]
      · simp
      · intro j hj hj0
        exact if_neg (hzero 0 (Finset.mem_range.mpr (Nat.succ_pos _)) j hj (by omega))
      · intro h0; exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h0
    · intro i hi hi0
      refine Finset.sum_eq_zero fun j hj => ?_
      exact if_neg (hzero i hi j hj (by omega))
    · intro h0; exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h0
  rw [hunf, Finset.sum_congr rfl fun ab hab => Finset.sum_congr rfl fun cd hcd => hinner ab hab cd hcd]

  have hcol : ∀ ab ∈ D.support,
      (∑ cd ∈ D'.support, if (ab.1 + cd.1, ab.2 + cd.2) = (a, b) then D ab * D' cd else 0)
        = if ab.1 ≤ a ∧ ab.2 ≤ b then D ab * D' (a - ab.1, b - ab.2) else 0 := by
    intro ab _
    by_cases hle : ab.1 ≤ a ∧ ab.2 ≤ b
    · rw [if_pos hle]
      have hcond : ∀ cd : ℕ × ℕ, ((ab.1 + cd.1, ab.2 + cd.2) = (a, b)) ↔ cd = (a - ab.1, b - ab.2) := by
        intro cd
        constructor
        · intro hcd
          have h1 := congrArg Prod.fst hcd
          have h2 := congrArg Prod.snd hcd
          beta_reduce at h1 h2
          exact Prod.ext (by omega) (by omega)
        · intro hcd
          subst hcd
          exact Prod.ext (by simp only; omega) (by simp only; omega)
      simp only [hcond]
      rw [Finset.sum_ite_eq']
      split_ifs with hmem
      · rfl
      · rw [Finsupp.notMem_support_iff.mp hmem, mul_zero]
    · rw [if_neg hle]
      refine Finset.sum_eq_zero fun cd _ => if_neg fun hcd => hle ?_
      have h1 := congrArg Prod.fst hcd
      have h2 := congrArg Prod.snd hcd
      beta_reduce at h1 h2
      omega
  rw [Finset.sum_congr rfl hcol]

  set box : Finset (ℕ × ℕ) := Finset.range (a + 1) ×ˢ Finset.range (b + 1) with hbox
  have hmem_box : ∀ ab : ℕ × ℕ, ab ∈ box ↔ ab.1 ≤ a ∧ ab.2 ≤ b := by
    intro ab
    simp [hbox, Finset.mem_product]
  have hL : (∑ ab ∈ D.support, if ab.1 ≤ a ∧ ab.2 ≤ b then D ab * D' (a - ab.1, b - ab.2) else 0)
      = ∑ ab ∈ D.support ∩ box, D ab * D' (a - ab.1, b - ab.2) := by
    rw [← Finset.sum_filter]
    congr 1
    ext ab
    simp [Finset.mem_filter, Finset.mem_inter, hmem_box]
  have hR : (∑ a' ∈ Finset.range (a + 1), ∑ b' ∈ Finset.range (b + 1),
        if a' + b' = k then D (a', b') * D' (a - a', b - b') else 0)
      = ∑ ab ∈ D.support ∩ box, D ab * D' (a - ab.1, b - ab.2) := by
    rw [← Finset.sum_product' (s := Finset.range (a + 1)) (t := Finset.range (b + 1))
      (f := fun a' b' => if a' + b' = k then D (a', b') * D' (a - a', b - b') else 0)]
    change (∑ ab ∈ box, if ab.1 + ab.2 = k then D ab * D' (a - ab.1, b - ab.2) else 0) = _
    rw [← Finset.sum_subset (Finset.inter_subset_right (s₁ := D.support) (s₂ := box))]
    · refine Finset.sum_congr rfl fun ab habm => ?_
      have hab' := Finset.mem_inter.mp habm
      by_cases hk : ab.1 + ab.2 = k
      · rw [if_pos hk]
      · rw [if_neg hk]
        have h1 := h ab hab'.1
        have hnot : (a - ab.1, b - ab.2) ∉ D'.support := by
          intro hmem
          have h2 := h' _ hmem
          beta_reduce at h2
          have hb := (hmem_box ab).mp hab'.2
          omega
        rw [Finsupp.notMem_support_iff.mp hnot, mul_zero]
    · intro ab habm hnot
      have : ab ∉ D.support := fun hs => hnot (Finset.mem_inter.mpr ⟨hs, habm⟩)
      rw [Finsupp.notMem_support_iff.mp this, zero_mul, ite_self]
  rw [hL, hR]

private theorem HasOrder.of_top_eq_zero {D : DOp ι} {k : ℕ} (h : HasOrder D (k + 1))
    (h0 : ∀ a b, a + b = k + 1 → D (a, b) = 0) : HasOrder D k := by
  intro ab hab
  rcases Nat.lt_or_ge (ab.1 + ab.2) (k + 1) with hlt | hge
  · exact Nat.lt_succ_iff.mp hlt
  · exact absurd (h0 ab.1 ab.2 (le_antisymm (h ab hab) hge)) (Finsupp.mem_support_iff.mp hab)

private theorem faithful (D : DOp ι) (h : ∀ G : ℝ → ℝ → (ι → ℂ), Smooth2 G → apply D G = fun _ _ => 0) : D = 0 := by
  exact faithful' D h

private theorem eul_zero (i : Fin 2) : eul i (0 : Coef) = 0 := by
  simp [eul]

private theorem iterate_eul_zero (i : Fin 2) : ∀ n : ℕ, (eul i)^[n] (0 : Coef) = 0
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply, eul_zero, iterate_eul_zero i n]

private noncomputable abbrev eulIt (i j : ℕ) : Coef → Coef := (eul 0)^[i] ∘ (eul 1)^[j]

private theorem eulIt_zero (i j : ℕ) : eulIt i j 0 = 0 := by
  simp only [eulIt, Function.comp_apply, iterate_eul_zero]

private theorem cmap_apply (φ : Coef →ₐ[ℂ] Coef) (D : DOp ι) (x : ℕ × ℕ) : cmap φ D x = (D x).map φ := by
  classical
  simp only [cmap, Finsupp.sum, Finsupp.finset_sum_apply, Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  split_ifs with hx
  · rfl
  · rw [Finsupp.notMem_support_iff.mp hx, Matrix.map_zero _ (map_zero φ)]

private theorem cmap_eq_zero_iff_aux (φ : Coef →ₐ[ℂ] Coef) (D : DOp ι) :
    (cmap φ D).support ⊆ D.support := support_sum_single_subset D _

private theorem cmap_finsupp_sum (φ : Coef →ₐ[ℂ] Coef) (D : DOp ι) (g : ℕ × ℕ → Matrix ι ι Coef → DOp ι) :
    cmap φ (D.sum g) = D.sum fun ab M => cmap φ (g ab M) := by
  ext x i j
  simp [cmap_apply, Finsupp.sum, Finsupp.finset_sum_apply, Matrix.sum_apply]

private theorem cmap_finset_sum (φ : Coef →ₐ[ℂ] Coef) {κ : Type} (s : Finset κ) (g : κ → DOp ι) :
    cmap φ (∑ k ∈ s, g k) = ∑ k ∈ s, cmap φ (g k) := by
  ext x i j
  simp [cmap_apply, Finsupp.finset_sum_apply, Matrix.sum_apply]

private theorem cmap_single (φ : Coef →ₐ[ℂ] Coef) (ab : ℕ × ℕ) (M : Matrix ι ι Coef) :
    cmap φ (Finsupp.single ab M) = Finsupp.single ab (M.map φ) := by
  ext x i j
  simp only [cmap_apply, Finsupp.single_apply]
  split_ifs
  · rfl
  · simp

private theorem map_mul' (φ : Coef →ₐ[ℂ] Coef) (M N : Matrix ι ι Coef) : (M * N).map φ = M.map φ * N.map φ := by
  ext i j
  simp [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul]

private theorem map_smul_mul (φ : Coef →ₐ[ℂ] Coef) (z : ℂ) (M N : Matrix ι ι Coef) :
    (z • (M * N)).map φ = z • (M.map φ * N.map φ) := by
  rw [← map_mul']
  exact Matrix.ext fun i j => by simp only [Matrix.map_apply, Matrix.smul_apply, map_smul]

private theorem cmap_comp_of_comm (φ : Coef →ₐ[ℂ] Coef) (hφ : ∀ i j : ℕ, ⇑φ ∘ eulIt i j = eulIt i j ∘ ⇑φ)
    (D D' : DOp ι) : cmap φ (comp D D') = comp (cmap φ D) (cmap φ D') := by
  simp only [comp]
  rw [cmap_finsupp_sum, Finsupp.sum_of_support_subset (cmap φ D) (cmap_eq_zero_iff_aux φ D), Finsupp.sum]
  · refine Finset.sum_congr rfl fun ab _ => ?_
    beta_reduce
    rw [cmap_apply, cmap_finsupp_sum, Finsupp.sum_of_support_subset (cmap φ D') (cmap_eq_zero_iff_aux φ D'),
      Finsupp.sum]
    · refine Finset.sum_congr rfl fun cd _ => ?_
      beta_reduce
      rw [cmap_apply, cmap_finset_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [cmap_finset_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [cmap_single, map_smul_mul, Matrix.map_map, Matrix.map_map]
      exact congrArg _ (congrArg _ (congrArg _ (congrArg _ (hφ i j))))
    · intro cd _
      simp [Matrix.map_zero _ (eulIt_zero _ _)]
  · intro ab _
    simp [Finsupp.sum]

private theorem cmap_cmul_hom (φ : Coef →ₐ[ℂ] Coef) (C : Matrix ι ι Coef) (D : DOp ι) :
    cmap φ (cmul C D) = cmul (C.map φ) (cmap φ D) := by
  simp only [cmul]
  rw [cmap_finsupp_sum, Finsupp.sum_of_support_subset (cmap φ D) (cmap_eq_zero_iff_aux φ D)]
  · rw [Finsupp.sum]
    refine Finset.sum_congr rfl fun ab _ => ?_
    beta_reduce
    rw [cmap_apply, cmap_single, map_mul']
  · intro ab _
    simp

private theorem pderiv0_killX0 (p : Coef) : MvPolynomial.pderiv 0 (killX0 p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [killX0]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
    rw [killX0, map_mul, MvPolynomial.aeval_X]
    fin_cases i
    · simp
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Derivation.leibniz, smul_eq_mul]
      rw [MvPolynomial.pderiv_X_of_ne (by decide)]
      simpa [killX0] using hp

private theorem eul0_killX0 (p : Coef) : eul 0 (killX0 p) = 0 := by
  simp [eul, pderiv0_killX0]

private theorem killX0_iterate_eul1 (p : Coef) : ∀ j : ℕ, killX0 ((eul 1)^[j] p) = (eul 1)^[j] (killX0 p)
  | 0 => rfl
  | j + 1 => by rw [Function.iterate_succ_apply', killX0_eul1, killX0_iterate_eul1 p j, Function.iterate_succ_apply']

private theorem killX0_comp_eulIt (i j : ℕ) : ⇑killX0 ∘ eulIt i j = eulIt i j ∘ ⇑killX0 := by
  funext p
  simp only [Function.comp_apply, eulIt]
  cases i with
  | zero => simpa using killX0_iterate_eul1 p j
  | succ i =>
    rw [Function.iterate_succ_apply', killX0_eul0, Function.iterate_succ_apply, ← killX0_iterate_eul1, eul0_killX0,
      iterate_eul_zero]

private noncomputable def constHom : Coef →ₐ[ℂ] Coef := MvPolynomial.aeval fun _ => 0

private theorem constHom_apply (p : Coef) : constHom p = C (constantCoeff p) := by
  show (MvPolynomial.aeval fun _ => (0 : Coef)) p = _
  rw [MvPolynomial.aeval_zero', MvPolynomial.algebraMap_eq]

private theorem const_fun_eq : (fun p : Coef => C (constantCoeff p)) = ⇑constHom := by
  funext p
  rw [constHom_apply]

private theorem iterate_eul_C (i : Fin 2) (c : ℂ) : ∀ n : ℕ, (eul i)^[n] (C c) = if n = 0 then C c else 0
  | 0 => by simp
  | n + 1 => by rw [Function.iterate_succ_apply, eul_C, iterate_eul_zero]; simp

private theorem constantCoeff_iterate_eul (i : Fin 2) (p : Coef) (n : ℕ) (hn : n ≠ 0) :
    constantCoeff ((eul i)^[n] p) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [Function.iterate_succ_apply', constantCoeff_eul]

private theorem constHom_comp_eulIt (i j : ℕ) : ⇑constHom ∘ eulIt i j = eulIt i j ∘ ⇑constHom := by
  funext p
  simp only [Function.comp_apply, eulIt, constHom_apply]
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      simp
    · simp only [Function.iterate_zero, id]
      rw [constantCoeff_iterate_eul 1 p j hj.ne', iterate_eul_C, if_neg hj.ne', map_zero]
  · rw [constantCoeff_iterate_eul 0 _ i hi.ne', map_zero]
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      simp only [Function.iterate_zero, id]
      rw [iterate_eul_C, if_neg hi.ne']
    · rw [iterate_eul_C, if_neg hj.ne', iterate_eul_zero]

private theorem comp_of_const_right (D D' : DOp ι) (hD' : cmap (fun p => C (constantCoeff p)) D' = D') :
    comp D D' = D.sum fun ab M => D'.sum fun cd M' => Finsupp.single (ab.1 + cd.1, ab.2 + cd.2) (M * M') := by
  have hconst : ∀ (cd : ℕ × ℕ) (i j : ℕ), 0 < i + j → (D' cd).map ((eul 0)^[i] ∘ (eul 1)^[j]) = 0 := by
    intro cd i j hij
    rw [const_fun_eq] at hD'
    have hcd : D' cd = (D' cd).map constHom := by rw [← cmap_apply, hD']
    rw [hcd, Matrix.map_map]
    ext a b
    have h1 := congrFun (constHom_comp_eulIt i j) (D' cd a b)
    simp only [Function.comp_apply, eulIt] at h1
    simp only [Matrix.map_apply, Function.comp_apply, Matrix.zero_apply]
    rw [constHom_apply, show (eul 0)^[i] ((eul 1)^[j] (C (constantCoeff (D' cd a b)))) = _ from rfl]
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      simp only [Function.iterate_zero, id]
      rw [iterate_eul_C, if_neg (by omega)]
    · rw [iterate_eul_C, if_neg hj.ne', iterate_eul_zero]
  simp only [comp]
  refine Finsupp.sum_congr fun ab _ => Finsupp.sum_congr fun cd hcd => ?_
  rw [Finset.sum_eq_single 0]
  · rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj0
      rw [hconst cd 0 j (by omega), mul_zero, smul_zero, Finsupp.single_zero]
    · intro h0; exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h0
  · intro i _ hi0
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hconst cd i j (by omega), mul_zero, smul_zero, Finsupp.single_zero]
  · intro h0; exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h0

private theorem cmap_comp_killX0 (D D' : DOp ι) :
    cmap killX0 (comp D D') = comp (cmap killX0 D) (cmap killX0 D') := by
  exact cmap_comp_of_comm killX0 killX0_comp_eulIt D D'
private theorem cmap_killX0_cmul (C : Matrix ι ι Coef) (D : DOp ι) :
    cmap killX0 (cmul C D) = cmul (C.map killX0) (cmap killX0 D) := by
  exact cmap_cmul_hom killX0 C D

private theorem cmap_comp_const (D D' : DOp ι) :
    cmap (fun p => C (constantCoeff p)) (comp D D')
      = comp (cmap (fun p => C (constantCoeff p)) D) (cmap (fun p => C (constantCoeff p)) D') := by
  rw [const_fun_eq]
  exact cmap_comp_of_comm constHom constHom_comp_eulIt D D'
private theorem comp_comm_of_const (D D' : DOp ι) (hD : cmap (fun p => C (constantCoeff p)) D = D)
    (hD' : cmap (fun p => C (constantCoeff p)) D' = D')
    (hcomm : ∀ ab cd, D ab * D' cd = D' cd * D ab) : comp D D' = comp D' D := by
  rw [comp_of_const_right D D' hD', comp_of_const_right D' D hD, Finsupp.sum_comm]
  refine Finsupp.sum_congr fun ab _ => Finsupp.sum_congr fun cd _ => ?_
  rw [hcomm, add_comm ab.1, add_comm ab.2]

end DOp
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

end Operators
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

private def _root_.HolonomicD2.basisExp : Fin 6 → ℕ × ℕ := ![(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (2, 1)]
p2m_export "HolonomicD2" "basisExp"
private def basisDeg (j : Fin 6) : ℕ := (basisExp j).1 + (basisExp j).2

section NormalOrder

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace DOp

private noncomputable def scal (c : ℂ) : Matrix ι ι Coef := (C c : Coef) • (1 : Matrix ι ι Coef)

private structure IsCasimirPair (Ω₂ Ω₃ : DOp ι) : Prop where
  ord₂ : HasOrder Ω₂ 2
  ord₃ : HasOrder Ω₃ 3
  top₂₀ : Ω₂ (2, 0) = scal 2
  top₁₁ : Ω₂ (1, 1) = scal (-2)
  top₀₂ : Ω₂ (0, 2) = scal 2
  top₃₀ : Ω₃ (3, 0) = 0
  top₂₁ : Ω₃ (2, 1) = scal 3
  top₁₂ : Ω₃ (1, 2) = scal (-3)
  top₀₃ : Ω₃ (0, 3) = 0
  comm : comp Ω₂ Ω₃ = comp Ω₃ Ω₂

private noncomputable def B (j : Fin 6) : DOp ι := mono (basisExp j).1 (basisExp j).2

private noncomputable def nb (Ω₂ Ω₃ : DOp ι) (j : Fin 6) (e f : ℕ) : DOp ι := comp (B j) (comp (npow Ω₂ e) (npow Ω₃ f))

private abbrev SP : Type := MvPolynomial (Fin 2) Coef

private noncomputable def xm (ab : ℕ × ℕ) : SP := (X 0 : SP) ^ ab.1 * (X 1 : SP) ^ ab.2

private theorem xm_add (ab cd : ℕ × ℕ) : xm (ab.1 + cd.1, ab.2 + cd.2) = xm ab * xm cd := by
  simp only [xm, pow_add]
  ring

private theorem xm_mul_C (ab : ℕ × ℕ) (c : Coef) :
    xm ab * MvPolynomial.C c = MvPolynomial.monomial (expIdx ab) c := by
  rw [MvPolynomial.monomial_eq, expIdx, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  simp only [Finsupp.prod_single_index, pow_zero, xm]
  ring

private noncomputable def ψ : MvPolynomial (Fin 2) ℚ →+* SP := MvPolynomial.map (algebraMap ℚ Coef)

private noncomputable def symb (k : ℕ) (D : DOp ι) : Matrix ι ι SP :=
  Matrix.of fun i j => ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal k, xm ab * MvPolynomial.C (D ab i j)

private theorem symb_apply (k : ℕ) (D : DOp ι) (i j : ι) :
    symb k D i j = ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal k, xm ab * MvPolynomial.C (D ab i j) := rfl

private theorem coeff_symb (k : ℕ) (D : DOp ι) {x : ℕ × ℕ} (hx : x ∈ Finset.HasAntidiagonal.antidiagonal k) (i j : ι) :
    MvPolynomial.coeff (expIdx x) (symb k D i j) = D x i j := by
  classical
  simp only [symb_apply, xm_mul_C, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, expIdx_injective.eq_iff]
  rw [Finset.sum_ite_eq' (Finset.HasAntidiagonal.antidiagonal k) x, if_pos hx]

private theorem apply_eq_of_symb_eq {k : ℕ} {D D' : DOp ι} (h : symb k D = symb k D') {x : ℕ × ℕ}
    (hx : x ∈ Finset.HasAntidiagonal.antidiagonal k) : D x = D' x := by
  refine Matrix.ext fun i j => ?_
  rw [← coeff_symb k D hx, ← coeff_symb k D' hx, h]

private theorem symb_zero (k : ℕ) : symb k (0 : DOp ι) = 0 := by
  refine Matrix.ext fun i j => ?_
  simp [symb_apply]

private theorem symb_add (k : ℕ) (D D' : DOp ι) : symb k (D + D') = symb k D + symb k D' := by
  refine Matrix.ext fun i j => ?_
  simp only [symb_apply, Matrix.add_apply, Finsupp.add_apply, map_add, mul_add, Finset.sum_add_distrib]

private theorem symb_finset_sum (k : ℕ) {κ : Type} (s : Finset κ) (g : κ → DOp ι) :
    symb k (∑ c ∈ s, g c) = ∑ c ∈ s, symb k (g c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [symb_zero]
  | insert c s hc ih => rw [Finset.sum_insert hc, symb_add, ih, Finset.sum_insert hc]

private theorem cmul_apply (M : Matrix ι ι Coef) (D : DOp ι) (x : ℕ × ℕ) : cmul M D x = M * D x := by
  classical
  simp only [cmul, Finsupp.sum, Finsupp.finset_sum_apply, Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  split_ifs with hx
  · rfl
  · rw [Finsupp.notMem_support_iff.mp hx, mul_zero]

private theorem symb_cmul (k : ℕ) (M : Matrix ι ι Coef) (D : DOp ι) :
    symb k (cmul M D) = M.map (MvPolynomial.C : Coef → SP) * symb k D := by
  refine Matrix.ext fun i j => ?_
  simp only [symb_apply, cmul_apply, Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ab _ => Finset.sum_congr rfl fun l _ => ?_
  ring

private theorem symb_mono {a b k : ℕ} (hk : a + b = k) :
    symb k (mono a b : DOp ι) = Matrix.scalar ι (xm (a, b)) := by
  classical
  have hmem : (a, b) ∈ Finset.HasAntidiagonal.antidiagonal k := Finset.HasAntidiagonal.mem_antidiagonal.mpr hk
  refine Matrix.ext fun i j => ?_
  simp only [symb_apply, mono, Finsupp.single_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single (a, b)]
  · simp only [if_true, Matrix.one_apply]
    split_ifs <;> simp
  · intro x _ hx
    simp [Ne.symm hx]
  · intro h; exact absurd hmem h

private theorem symb_comp {D D' : DOp ι} {k k' : ℕ} (h : HasOrder D k) (h' : HasOrder D' k') :
    symb (k + k') (comp D D') = symb k D * symb k' D' := by
  classical
  refine Matrix.ext fun i j => ?_

  have hR : (symb k D * symb k' D') i j = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k ×ˢ Finset.HasAntidiagonal.antidiagonal k',
      xm (p.1.1 + p.2.1, p.1.2 + p.2.2) * MvPolynomial.C ((D p.1 * D' p.2) i j) := by
    simp only [Matrix.mul_apply, symb_apply, Finset.sum_product]
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun cd _ => ?_
    rw [map_sum, Finset.mul_sum, xm_add]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul]
    ring

  have hL : symb (k + k') (comp D D') i j = ∑ y ∈ (Finset.HasAntidiagonal.antidiagonal (k + k')).sigma
      (fun x : ℕ × ℕ => (Finset.range (x.1 + 1) ×ˢ Finset.range (x.2 + 1)).filter fun q => q.1 + q.2 = k),
        xm y.1 * MvPolynomial.C ((D y.2 * D' (y.1.1 - y.2.1, y.1.2 - y.2.2)) i j) := by
    rw [Finset.sum_sigma, symb_apply]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [comp_apply_top h h' x.1 x.2 (Finset.HasAntidiagonal.mem_antidiagonal.mp hx), ← Finset.sum_product', ← Finset.sum_filter,
      Matrix.sum_apply, map_sum, Finset.mul_sum]
  rw [hL, hR]
  refine Finset.sum_nbij' (fun y => (y.2, (y.1.1 - y.2.1, y.1.2 - y.2.2)))
    (fun p => ⟨(p.1.1 + p.2.1, p.1.2 + p.2.2), p.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨x, q⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.HasAntidiagonal.mem_antidiagonal] at hy
    simp only [Finset.mem_product, Finset.HasAntidiagonal.mem_antidiagonal]
    omega
  · rintro ⟨ab, cd⟩ hp
    simp only [Finset.mem_product, Finset.HasAntidiagonal.mem_antidiagonal] at hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.HasAntidiagonal.mem_antidiagonal]
    omega
  · rintro ⟨x, q⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.HasAntidiagonal.mem_antidiagonal] at hy
    have hx : (q.1 + (x.1 - q.1), q.2 + (x.2 - q.2)) = x := Prod.ext (by simp only; omega) (by simp only; omega)
    exact Sigma.ext hx (heq_of_eq rfl)
  · rintro ⟨ab, cd⟩ _
    simp
  · rintro ⟨x, q⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.HasAntidiagonal.mem_antidiagonal] at hy
    have hx : (q.1 + (x.1 - q.1), q.2 + (x.2 - q.2)) = x := Prod.ext (by simp only; omega) (by simp only; omega)
    beta_reduce
    rw [hx]

private theorem map_scal (c : ℂ) :
    (scal c : Matrix ι ι Coef).map (MvPolynomial.C : Coef → SP) = Matrix.scalar ι (MvPolynomial.C (C c) : SP) := by
  refine Matrix.ext fun i j => ?_
  simp only [scal, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
    smul_eq_mul]
  split_ifs <;> simp

private theorem symb_eq_scalar_of (k : ℕ) (D : DOp ι) (p : SP)
    (hp : ∀ i j : ι, (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal k, xm ab * MvPolynomial.C (D ab i j)) = if i = j then p else 0) :
    symb k D = Matrix.scalar ι p := by
  refine Matrix.ext fun i j => ?_
  rw [symb_apply, hp, Matrix.scalar_apply, Matrix.diagonal_apply]

omit [Fintype ι] in
private theorem scal_apply' (c : ℂ) (i j : ι) : (scal c : Matrix ι ι Coef) i j = if i = j then C c else 0 := by
  simp [scal, Matrix.one_apply]

private theorem symb_Ω₂ {Ω₂ Ω₃ : DOp ι} (hΩ : IsCasimirPair Ω₂ Ω₃) :
    symb 2 Ω₂ = Matrix.scalar ι (ψ CoinvariantS3.s₂) := by
  have hanti : Finset.HasAntidiagonal.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by decide
  refine symb_eq_scalar_of 2 Ω₂ _ fun i j => ?_
  rw [hanti, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, hΩ.top₀₂, hΩ.top₁₁,
    hΩ.top₂₀]
  simp only [scal_apply']
  split_ifs
  · simp only [CoinvariantS3.s₂, ψ, xm, map_mul, map_sub, map_add, map_pow, MvPolynomial.map_X, map_ofNat, map_neg]
    ring
  · simp

private theorem symb_Ω₃ {Ω₂ Ω₃ : DOp ι} (hΩ : IsCasimirPair Ω₂ Ω₃) :
    symb 3 Ω₃ = Matrix.scalar ι (ψ CoinvariantS3.s₃) := by
  have hanti : Finset.HasAntidiagonal.antidiagonal 3 = {(0, 3), (1, 2), (2, 1), (3, 0)} := by decide
  refine symb_eq_scalar_of 3 Ω₃ _ fun i j => ?_
  rw [hanti, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, hΩ.top₀₃, hΩ.top₁₂, hΩ.top₂₁, hΩ.top₃₀]
  simp only [scal_apply', Matrix.zero_apply, map_zero, mul_zero, zero_add, add_zero]
  split_ifs
  · simp only [CoinvariantS3.s₃, ψ, xm, map_mul, map_sub, map_pow, MvPolynomial.map_X, map_ofNat, map_neg]
    ring
  · simp

private theorem hasOrder_one : HasOrder (one : DOp ι) 0 := hasOrder_mono 0 0

private theorem symb_one : symb 0 (one : DOp ι) = 1 := by
  rw [one_eq_mono, symb_mono (k := 0) (a := 0) (b := 0) rfl]
  simp [xm]

private theorem npow_succ' (Ω : DOp ι) (n : ℕ) : npow Ω (n + 1) = comp Ω (npow Ω n) := by
  simp only [npow, Function.iterate_succ_apply']

private theorem hasOrder_symb_npow {Ω : DOp ι} {k : ℕ} (hk : HasOrder Ω k) {p : SP}
    (hs : symb k Ω = Matrix.scalar ι p) :
    ∀ n : ℕ, HasOrder (npow Ω n) (k * n) ∧ symb (k * n) (npow Ω n) = Matrix.scalar ι (p ^ n)
  | 0 => by
    refine ⟨?_, ?_⟩
    · simpa [npow] using hasOrder_one (ι := ι)
    · simp [npow, symb_one]
  | n + 1 => by
    obtain ⟨ho, hsym⟩ := hasOrder_symb_npow hk hs n
    have hidx : k * (n + 1) = k + k * n := by ring
    refine ⟨?_, ?_⟩
    · rw [npow_succ', hidx]
      exact hk.comp ho
    · rw [npow_succ', hidx, symb_comp hk ho, hs, hsym, ← map_mul, pow_succ']

private theorem basisExp_eq : (basisExp : Fin 6 → ℕ × ℕ) = CoinvariantS3.basisExp := rfl

private theorem hasOrder_B (j : Fin 6) : HasOrder (B j : DOp ι) (basisDeg j) := hasOrder_mono _ _

private theorem ψ_bmon (j : Fin 6) : ψ (CoinvariantS3.bmon j) = xm (basisExp j) := by
  simp [ψ, CoinvariantS3.bmon, xm, basisExp_eq]

private theorem ψ_bmon_aux (a b : ℕ) : ψ ((X 0 : MvPolynomial (Fin 2) ℚ) ^ a * X 1 ^ b) = xm (a, b) := by
  simp [ψ, xm]

private theorem symb_B (j : Fin 6) : symb (basisDeg j) (B j : DOp ι) = Matrix.scalar ι (ψ (CoinvariantS3.bmon j)) := by
  rw [B, symb_mono (k := basisDeg j) rfl, ψ_bmon]

private theorem hasOrder_symb_nb {Ω₂ Ω₃ : DOp ι} (hΩ : IsCasimirPair Ω₂ Ω₃) (j : Fin 6) (e f : ℕ) :
    HasOrder (nb Ω₂ Ω₃ j e f) (basisDeg j + 2 * e + 3 * f) ∧
      symb (basisDeg j + 2 * e + 3 * f) (nb Ω₂ Ω₃ j e f) = Matrix.scalar ι (ψ (CoinvariantS3.term j e f)) := by
  obtain ⟨h2, s2⟩ := hasOrder_symb_npow hΩ.ord₂ (symb_Ω₂ hΩ) e
  obtain ⟨h3, s3⟩ := hasOrder_symb_npow hΩ.ord₃ (symb_Ω₃ hΩ) f
  have hidx : basisDeg j + 2 * e + 3 * f = basisDeg j + (2 * e + 3 * f) := Nat.add_assoc _ _ _
  refine ⟨?_, ?_⟩
  · rw [hidx, nb]
    exact (hasOrder_B j).comp (h2.comp h3)
  · rw [hidx, nb, symb_comp (hasOrder_B j) (h2.comp h3), symb_comp h2 h3, symb_B, s2, s3]
    simp only [CoinvariantS3.term, map_mul, map_pow, mul_assoc]

private theorem cmul_zero_right_aux (M : Matrix ι ι Coef) : cmul M (0 : DOp ι) = 0 := by
  ext x : 1
  rw [cmul_apply, Finsupp.zero_apply, mul_zero]

private noncomputable def nfSum (Ω₂ Ω₃ : DOp ι) (k : ℕ) (ν : Fin 6 → ℕ → ℕ → Matrix ι ι Coef) : DOp ι :=
  ∑ j, ∑ e ∈ Finset.range (k + 1), ∑ f ∈ Finset.range (k + 1), cmul (ν j e f) (nb Ω₂ Ω₃ j e f)

private def NF (Ω₂ Ω₃ : DOp ι) (k : ℕ) (D : DOp ι) : Prop :=
  ∃ ν : Fin 6 → ℕ → ℕ → Matrix ι ι Coef,
    (∀ j e f, ν j e f ≠ 0 → basisDeg j + 2 * e + 3 * f ≤ k) ∧ D = nfSum Ω₂ Ω₃ k ν

private theorem cmul_zero_left (D : DOp ι) : cmul (0 : Matrix ι ι Coef) D = 0 := by
  ext x : 1
  rw [cmul_apply, zero_mul, Finsupp.zero_apply]

private theorem cmul_finset_sum (M : Matrix ι ι Coef) {κ : Type} (s : Finset κ) (g : κ → DOp ι) :
    cmul M (∑ c ∈ s, g c) = ∑ c ∈ s, cmul M (g c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cmul_zero_right_aux]
  | insert c s hc ih => rw [Finset.sum_insert hc, cmul_add, ih, Finset.sum_insert hc]

private theorem NF.zero (Ω₂ Ω₃ : DOp ι) (k : ℕ) : NF Ω₂ Ω₃ k 0 :=
  ⟨fun _ _ _ => 0, fun _ _ _ h => (h rfl).elim, by simp [nfSum, cmul_zero_left]⟩

private theorem NF.add {Ω₂ Ω₃ : DOp ι} {k : ℕ} {D D' : DOp ι} (h : NF Ω₂ Ω₃ k D) (h' : NF Ω₂ Ω₃ k D') :
    NF Ω₂ Ω₃ k (D + D') := by
  obtain ⟨ν, hν, rfl⟩ := h
  obtain ⟨ν', hν', rfl⟩ := h'
  refine ⟨fun j e f => ν j e f + ν' j e f, fun j e f hne => ?_, ?_⟩
  · dsimp only at hne
    by_cases h0 : ν j e f = 0
    · rw [h0, zero_add] at hne
      exact hν' j e f hne
    · exact hν j e f h0
  · simp only [nfSum, add_cmul, Finset.sum_add_distrib]

private theorem NF.sum {Ω₂ Ω₃ : DOp ι} {k : ℕ} {κ : Type} (s : Finset κ) {g : κ → DOp ι}
    (hg : ∀ c ∈ s, NF Ω₂ Ω₃ k (g c)) : NF Ω₂ Ω₃ k (∑ c ∈ s, g c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using NF.zero Ω₂ Ω₃ k
  | insert c s hc ih =>
    rw [Finset.sum_insert hc]
    exact (hg c (Finset.mem_insert_self c s)).add (ih fun c' hc' => hg c' (Finset.mem_insert_of_mem hc'))

private theorem NF.cmul {Ω₂ Ω₃ : DOp ι} {k : ℕ} {D : DOp ι} (M : Matrix ι ι Coef) (h : NF Ω₂ Ω₃ k D) :
    NF Ω₂ Ω₃ k (cmul M D) := by
  obtain ⟨ν, hν, rfl⟩ := h
  refine ⟨fun j e f => M * ν j e f, fun j e f hne => hν j e f fun h0 => hne (by dsimp only; rw [h0, mul_zero]), ?_⟩
  simp only [nfSum, cmul_finset_sum, cmul_cmul]

private theorem NF.mono_le {Ω₂ Ω₃ : DOp ι} {k k' : ℕ} {D : DOp ι} (h : NF Ω₂ Ω₃ k D) (hk : k ≤ k') :
    NF Ω₂ Ω₃ k' D := by
  obtain ⟨ν, hν, rfl⟩ := h
  refine ⟨ν, fun j e f hne => (hν j e f hne).trans hk, ?_⟩
  have hzero : ∀ j e f, k < e ∨ k < f → ν j e f = 0 := by
    intro j e f hef
    by_contra hne
    have := hν j e f hne
    omega
  have hrange : Finset.range (k + 1) ⊆ Finset.range (k' + 1) := fun x hx =>
    Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega)
  simp only [nfSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_subset hrange]
  · refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_subset hrange]
    intro f _ hf
    rw [hzero j e f (Or.inr (by simpa [Nat.lt_succ_iff] using hf)), cmul_zero_left]
  · intro e _ he
    refine Finset.sum_eq_zero fun f _ => ?_
    rw [hzero j e f (Or.inl (by simpa [Nat.lt_succ_iff] using he)), cmul_zero_left]

private theorem hasOrder_of_forall {D : DOp ι} {k : ℕ} (h : ∀ x : ℕ × ℕ, k < x.1 + x.2 → D x = 0) :
    HasOrder D k := by
  intro x hx
  by_contra hlt
  exact Finsupp.mem_support_iff.mp hx (h x (by omega))

private theorem apply_eq_zero_of_hasOrder {D : DOp ι} {k : ℕ} (h : HasOrder D k) {x : ℕ × ℕ} (hx : k < x.1 + x.2) :
    D x = 0 := by
  by_contra hne
  have := h x (Finsupp.mem_support_iff.mpr hne)
  omega

private theorem HasOrder.finset_sum {k : ℕ} {κ : Type} (s : Finset κ) {g : κ → DOp ι}
    (hg : ∀ c ∈ s, HasOrder (g c) k) : HasOrder (∑ c ∈ s, g c) k := by
  classical
  induction s using Finset.induction_on with
  | empty => intro x hx; simp at hx
  | insert c s hc ih =>
    rw [Finset.sum_insert hc]
    exact (hg c (Finset.mem_insert_self c s)).add (ih fun c' hc' => hg c' (Finset.mem_insert_of_mem hc'))

private theorem symb_term {Ω₂ Ω₃ : DOp ι} (hΩ : IsCasimirPair Ω₂ Ω₃) {k : ℕ} (c : ℚ) (j : Fin 6) (e f : ℕ)
    (hc : c ≠ 0 → basisDeg j + 2 * e + 3 * f = k) :
    HasOrder (cmul (scal (algebraMap ℚ ℂ c)) (nb Ω₂ Ω₃ j e f)) k ∧
      symb k (cmul (scal (algebraMap ℚ ℂ c)) (nb Ω₂ Ω₃ j e f))
        = Matrix.scalar ι (ψ (c • CoinvariantS3.term j e f)) := by
  by_cases h0 : c = 0
  · subst h0
    have hz : cmul (scal (algebraMap ℚ ℂ 0)) (nb Ω₂ Ω₃ j e f) = 0 := by
      rw [map_zero, show (scal 0 : Matrix ι ι Coef) = 0 by simp [scal], cmul_zero_left]
    rw [hz, symb_zero, zero_smul, map_zero, map_zero]
    exact ⟨fun x hx => by simp at hx, rfl⟩
  · obtain ⟨ho, hs⟩ := hasOrder_symb_nb hΩ j e f
    rw [hc h0] at ho hs
    refine ⟨ho.cmul _, ?_⟩
    rw [symb_cmul, hs, map_scal, ← map_mul, MvPolynomial.smul_eq_C_mul, map_mul ψ (MvPolynomial.C c), ψ,
      MvPolynomial.map_C, MvPolynomial.algebraMap_apply]

private theorem exists_nf_mono {Ω₂ Ω₃ : DOp ι} (hΩ : IsCasimirPair Ω₂ Ω₃) (a b : ℕ) :
    ∃ N R : DOp ι, NF Ω₂ Ω₃ (a + b) N ∧ (∀ x : ℕ × ℕ, a + b ≤ x.1 + x.2 → R x = 0) ∧ mono a b = N + R := by
  obtain ⟨c, hc, hdec⟩ := CoinvariantS3.hasDecomp_monomial a b
  set k := a + b with hk
  set N : DOp ι := nfSum Ω₂ Ω₃ k fun j e f => scal (algebraMap ℚ ℂ (c j e f)) with hN
  have hterm : ∀ j e f, HasOrder (cmul (scal (algebraMap ℚ ℂ (c j e f))) (nb Ω₂ Ω₃ j e f)) k ∧
      symb k (cmul (scal (algebraMap ℚ ℂ (c j e f))) (nb Ω₂ Ω₃ j e f))
        = Matrix.scalar ι (ψ (c j e f • CoinvariantS3.term j e f)) :=
    fun j e f => symb_term hΩ (c j e f) j e f (hc j e f)
  have hNord : HasOrder N k :=
    HasOrder.finset_sum _ fun j _ => HasOrder.finset_sum _ fun e _ => HasOrder.finset_sum _ fun f _ => (hterm j e f).1
  have hNsymb : symb k N = symb k (mono a b) := by
    rw [hN, nfSum, symb_finset_sum, symb_mono hk.symm]
    simp only [symb_finset_sum, fun j e f => (hterm j e f).2, ← map_sum]
    congr 1
    rw [← ψ_bmon_aux a b, hdec]
  refine ⟨N, mono a b - N, ?_, ?_, (add_sub_cancel N (mono a b)).symm⟩
  · refine ⟨_, fun j e f hne => ?_, rfl⟩
    exact (hc j e f fun h0 => hne (by simp [h0, scal])).le
  · intro x hx
    rw [Finsupp.sub_apply, sub_eq_zero]
    rcases hx.lt_or_eq with hlt | heq
    · rw [apply_eq_zero_of_hasOrder hNord hlt, apply_eq_zero_of_hasOrder (hasOrder_mono a b) hlt]
    · exact (apply_eq_of_symb_eq hNsymb (Finset.HasAntidiagonal.mem_antidiagonal.mpr heq.symm)).symm

private theorem nf_of_hasOrder {Ω₂ Ω₃ : DOp ι} (hΩ : IsCasimirPair Ω₂ Ω₃) :
    ∀ (k : ℕ) (D : DOp ι), HasOrder D k → NF Ω₂ Ω₃ k D := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro D hD

  have hlow : ∀ R : DOp ι, (∀ x : ℕ × ℕ, k ≤ x.1 + x.2 → R x = 0) → NF Ω₂ Ω₃ k R := by
    intro R hR
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · have : R = 0 := Finsupp.ext fun x => by rw [hR x (by omega), Finsupp.zero_apply]
      rw [this]
      exact NF.zero Ω₂ Ω₃ k
    · refine (ih (k - 1) (by omega) R (hasOrder_of_forall fun x hx => hR x (by omega))).mono_le (by omega)

  set T : DOp ι := ∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, cmul (D x) (mono x.1 x.2) with hT
  have hTapply : ∀ y : ℕ × ℕ, T y = if y ∈ Finset.HasAntidiagonal.antidiagonal k then D y else 0 := by
    classical
    intro y
    simp only [hT, Finsupp.finset_sum_apply, cmul_apply, mono, Finsupp.single_apply]
    by_cases hy : y ∈ Finset.HasAntidiagonal.antidiagonal k
    · rw [if_pos hy, Finset.sum_eq_single y]
      · simp
      · intro x _ hxy
        have : (x.1, x.2) ≠ y := by simpa using hxy
        simp [this]
      · intro h; exact absurd hy h
    · rw [if_neg hy]
      refine Finset.sum_eq_zero fun x hx => ?_
      have : (x.1, x.2) ≠ y := by
        intro h
        apply hy
        rw [← h]
        exact hx
      simp [this]
  have hTnf : NF Ω₂ Ω₃ k T := by
    refine NF.sum _ fun x hx => ?_
    obtain ⟨N, R, hN, hR, hmono⟩ := exists_nf_mono hΩ x.1 x.2
    have hxk : x.1 + x.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    rw [hmono, cmul_add]
    refine (hN.mono_le hxk.le |>.cmul (D x)).add (hlow _ fun y hy => ?_)
    rw [cmul_apply, hR y (by omega), mul_zero]
  have hrest : NF Ω₂ Ω₃ k (D - T) := by
    refine hlow _ fun y hy => ?_
    rw [Finsupp.sub_apply, hTapply, sub_eq_zero]
    split_ifs with hmem
    · rfl
    · exact apply_eq_zero_of_hasOrder hD (lt_of_le_of_ne hy fun h => hmem (Finset.HasAntidiagonal.mem_antidiagonal.mpr h.symm))
  simpa using hTnf.add hrest

private theorem normalOrder_exists {Ω₂ Ω₃ : DOp ι} (hΩ : IsCasimirPair Ω₂ Ω₃) (D : DOp ι) (k : ℕ) (hD : HasOrder D k) :
    ∃ ν : Fin 6 → ℕ → ℕ → Matrix ι ι Coef,
      (∀ j e f, ν j e f ≠ 0 → basisDeg j + 2 * e + 3 * f ≤ k) ∧
      D = ∑ j, ∑ e ∈ Finset.range (k + 1), ∑ f ∈ Finset.range (k + 1), cmul (ν j e f) (nb Ω₂ Ω₃ j e f) := by
  exact nf_of_hasOrder hΩ k D hD

private def tri (n : ℕ) : Finset (Fin 6 × ℕ × ℕ) :=
  (Finset.univ ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter fun J =>
    basisDeg J.1 + 2 * J.2.1 + 3 * J.2.2 = n

private theorem basisDeg_le_three : ∀ j : Fin 6, basisDeg j ≤ 3 := by decide

private theorem mem_tri {n : ℕ} {J : Fin 6 × ℕ × ℕ} : J ∈ tri n ↔ basisDeg J.1 + 2 * J.2.1 + 3 * J.2.2 = n := by
  simp only [tri, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨⟨by omega, by omega⟩, h⟩

private theorem card_tri_add_six (n : ℕ) : (tri (n + 6)).card = (tri n).card + 6 := by
  classical
  rw [← Finset.card_filter_add_card_filter_not (fun J : Fin 6 × ℕ × ℕ => J.2.1 < 3)]
  have hhigh : ((tri (n + 6)).filter fun J => ¬ J.2.1 < 3)
      = (tri n).map ⟨fun J => (J.1, J.2.1 + 3, J.2.2), fun J J' h => by
          simp only [Prod.mk.injEq] at h
          exact Prod.ext h.1 (Prod.ext (by omega) h.2.2)⟩ := by
    ext ⟨j, e, f⟩
    simp only [Finset.mem_filter, mem_tri, Finset.mem_map, Function.Embedding.coeFn_mk, Prod.mk.injEq, Prod.exists]
    constructor
    · rintro ⟨h, he⟩
      exact ⟨j, e - 3, f, by omega, rfl, by omega, rfl⟩
    · rintro ⟨j', e', f', h, rfl, rfl, rfl⟩
      exact ⟨by omega, by omega⟩
  have hlow : ((tri (n + 6)).filter fun J => J.2.1 < 3).card = 6 := by
    refine (Finset.card_bij (fun J _ => J.1) (fun _ _ => Finset.mem_univ (α := Fin 6) _) ?_ ?_).trans (by simp)
    · rintro ⟨j, e, f⟩ h ⟨j', e', f'⟩ h' hjj
      simp only [Finset.mem_filter, mem_tri] at h h' hjj
      subst hjj
      have : e = e' ∧ f = f' := by omega
      rw [this.1, this.2]
    · intro j _
      have hd := basisDeg_le_three j
      refine ⟨(j, (2 * (n + 6 - basisDeg j)) % 3, (n + 6 - basisDeg j - 2 * ((2 * (n + 6 - basisDeg j)) % 3)) / 3),
        ?_, rfl⟩
      simp only [Finset.mem_filter, mem_tri]
      omega
  rw [hhigh, Finset.card_map, hlow, add_comm]

private theorem card_tri (n : ℕ) : (tri n).card = n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 6 with h | h
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      rw [card_tri_add_six, ih m (by omega)]

private noncomputable def termJ (J : Fin 6 × ℕ × ℕ) : MvPolynomial (Fin 2) ℚ := CoinvariantS3.term J.1 J.2.1 J.2.2

private theorem monomial_expIdx_rat (a b : ℕ) :
    (X 0 : MvPolynomial (Fin 2) ℚ) ^ a * X 1 ^ b = MvPolynomial.monomial (expIdx (a, b)) (1 : ℚ) := by
  rw [MvPolynomial.monomial_eq, map_one, one_mul, expIdx,
    Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  simp only [Finsupp.prod_single_index, pow_zero]

private theorem exists_span_coeffs (n : ℕ) {ab : ℕ × ℕ} (hab : ab ∈ Finset.HasAntidiagonal.antidiagonal n) :
    ∃ d : Fin 6 × ℕ × ℕ → ℚ, ∀ x ∈ Finset.HasAntidiagonal.antidiagonal n,
      (∑ J ∈ tri n, d J * MvPolynomial.coeff (expIdx x) (termJ J)) = if ab = x then 1 else 0 := by
  classical
  obtain ⟨c, hc, hdec⟩ := CoinvariantS3.hasDecomp_monomial ab.1 ab.2
  have hn : ab.1 + ab.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  rw [hn] at hc hdec
  refine ⟨fun J => c J.1 J.2.1 J.2.2, fun x hx => ?_⟩

  have hbox : (∑ j, ∑ e ∈ Finset.range (n + 1), ∑ f ∈ Finset.range (n + 1), c j e f • CoinvariantS3.term j e f)
      = ∑ J ∈ tri n, c J.1 J.2.1 J.2.2 • termJ J := by
    rw [tri, Finset.sum_filter_of_ne, Finset.sum_product, Finset.sum_congr rfl fun j _ => Finset.sum_product _ _ _]
    · rfl
    · intro J _ hJ
      refine hc J.1 J.2.1 J.2.2 fun h0 => hJ ?_
      simp [termJ, h0]
  have hcoeff := congrArg (MvPolynomial.coeff (expIdx x)) hdec
  rw [hbox, monomial_expIdx_rat, MvPolynomial.coeff_monomial, MvPolynomial.coeff_sum] at hcoeff
  simp only [MvPolynomial.coeff_smul, smul_eq_mul] at hcoeff
  rw [← hcoeff]
  simp only [expIdx_injective.eq_iff, Prod.mk.eta]

private theorem terms_indep (n : ℕ) (c : Fin 6 × ℕ × ℕ → Coef)
    (h : (∑ J ∈ tri n, MvPolynomial.C (c J) * ψ (termJ J)) = 0) : ∀ J ∈ tri n, c J = 0 := by
  classical

  have hrel : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal n,
      (∑ J ∈ tri n, c J * algebraMap ℚ Coef (MvPolynomial.coeff (expIdx x) (termJ J))) = 0 := by
    intro x _
    have := congrArg (MvPolynomial.coeff (expIdx x)) h
    simpa only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, ψ, MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
      using this

  choose d hd using fun ab : Finset.HasAntidiagonal.antidiagonal n => exists_span_coeffs n ab.2
  let Dm : Matrix (Finset.HasAntidiagonal.antidiagonal n) (tri n) ℚ := fun ab J => d ab J.1
  let Tm : Matrix (tri n) (Finset.HasAntidiagonal.antidiagonal n) ℚ := fun J ab => MvPolynomial.coeff (expIdx ab.1) (termJ J.1)
  have hDT : Dm * Tm = 1 := by
    ext ab x
    simp only [Matrix.mul_apply, Matrix.one_apply, Dm, Tm]
    rw [Finset.sum_coe_sort (tri n) (fun J => d ab J * MvPolynomial.coeff (expIdx x.1) (termJ J)), hd ab x.1 x.2]
    simp only [Subtype.ext_iff]
  have hcard : Fintype.card (Finset.HasAntidiagonal.antidiagonal n) = Fintype.card (tri n) := by
    simp only [Fintype.card_coe, Finset.Nat.card_antidiagonal, card_tri]
  have hTD : Tm * Dm = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcard)).mp hDT

  have hδ : ∀ J J' : tri n,
      (∑ a : Finset.HasAntidiagonal.antidiagonal n, MvPolynomial.coeff (expIdx a.1) (termJ J'.1) * d a J.1)
        = if J' = J then 1 else 0 := by
    intro J J'
    have := congrFun (congrFun hTD J') J
    simpa only [Matrix.mul_apply, Matrix.one_apply, Tm, Dm] using this

  have hrel' : ∀ a : Finset.HasAntidiagonal.antidiagonal n,
      (∑ J' : tri n, c J'.1 * algebraMap ℚ Coef (MvPolynomial.coeff (expIdx a.1) (termJ J'.1))) = 0 := by
    intro a
    rw [Finset.sum_coe_sort (tri n) (fun J' => c J' * algebraMap ℚ Coef (MvPolynomial.coeff (expIdx a.1) (termJ J')))]
    exact hrel a.1 a.2
  intro J hJ
  have key : (∑ J' : tri n, c J'.1 * algebraMap ℚ Coef
      (∑ a : Finset.HasAntidiagonal.antidiagonal n, MvPolynomial.coeff (expIdx a.1) (termJ J'.1) * d a J)) = c J := by
    simp only [fun J' => hδ ⟨J, hJ⟩ J']
    simp [apply_ite (algebraMap ℚ Coef)]
  rw [← key]
  simp only [map_sum, map_mul, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [← Finset.sum_mul, hrel' a, zero_mul]

private theorem symb_eq_zero_of_hasOrder_lt {D : DOp ι} {m n : ℕ} (h : HasOrder D m) (hmn : m < n) : symb n D = 0 := by
  refine Matrix.ext fun i j => ?_
  rw [symb_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun ab hab => ?_
  rw [apply_eq_zero_of_hasOrder h (by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hab; omega), Matrix.zero_apply, map_zero,
    mul_zero]

private theorem symb_cmul_nb {Ω₂ Ω₃ : DOp ι} (hΩ : IsCasimirPair Ω₂ Ω₃) {n : ℕ} (M : Matrix ι ι Coef)
    (J : Fin 6 × ℕ × ℕ) (hle : M ≠ 0 → basisDeg J.1 + 2 * J.2.1 + 3 * J.2.2 ≤ n) :
    symb n (cmul M (nb Ω₂ Ω₃ J.1 J.2.1 J.2.2))
      = (if J ∈ tri n then M else 0).map (MvPolynomial.C : Coef → SP) * Matrix.scalar ι (ψ (termJ J)) := by
  by_cases hM : M = 0
  · subst hM
    simp only [cmul_zero_left, symb_zero, ite_self, Matrix.map_zero _ (map_zero _), zero_mul]
  obtain ⟨ho, hs⟩ := hasOrder_symb_nb hΩ J.1 J.2.1 J.2.2
  rcases (hle hM).lt_or_eq with hlt | heq
  · rw [symb_eq_zero_of_hasOrder_lt (ho.cmul M) hlt, if_neg (fun hJ => by have := mem_tri.mp hJ; omega),
      Matrix.map_zero _ (map_zero _), zero_mul]
  · rw [if_pos (mem_tri.mpr heq), symb_cmul, ← heq, hs]
    rfl

private theorem normalOrder_unique {Ω₂ Ω₃ : DOp ι} (hΩ : IsCasimirPair Ω₂ Ω₃) (K : ℕ)
    (ν : Fin 6 → ℕ → ℕ → Matrix ι ι Coef)
    (h : ∑ j, ∑ e ∈ Finset.range K, ∑ f ∈ Finset.range K, cmul (ν j e f) (nb Ω₂ Ω₃ j e f) = 0) :
    ∀ j, ∀ e < K, ∀ f < K, ν j e f = 0 := by
  classical
  intro j e he f hf
  by_contra hne

  set box : Finset (Fin 6 × ℕ × ℕ) := Finset.univ ×ˢ Finset.range K ×ˢ Finset.range K with hbox
  set S : Finset (Fin 6 × ℕ × ℕ) := box.filter fun J => ν J.1 J.2.1 J.2.2 ≠ 0 with hS
  have hmemS : (j, e, f) ∈ S := by
    simp only [hS, hbox, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_range]
    exact ⟨⟨he, hf⟩, hne⟩
  obtain ⟨J₀, hJ₀S, hJ₀max⟩ :=
    S.exists_max_image (fun J => basisDeg J.1 + 2 * J.2.1 + 3 * J.2.2) ⟨_, hmemS⟩
  set n := basisDeg J₀.1 + 2 * J₀.2.1 + 3 * J₀.2.2 with hn
  have hJ₀box : J₀ ∈ box := (Finset.mem_filter.mp hJ₀S).1
  have hJ₀ne : ν J₀.1 J₀.2.1 J₀.2.2 ≠ 0 := (Finset.mem_filter.mp hJ₀S).2
  have hJ₀tri : J₀ ∈ tri n := mem_tri.mpr rfl

  have hle : ∀ J ∈ box, ν J.1 J.2.1 J.2.2 ≠ 0 → basisDeg J.1 + 2 * J.2.1 + 3 * J.2.2 ≤ n :=
    fun J hJ hJne => hJ₀max J (Finset.mem_filter.mpr ⟨hJ, hJne⟩)

  have hsymb : (∑ J ∈ box, (if J ∈ tri n then ν J.1 J.2.1 J.2.2 else 0).map (MvPolynomial.C : Coef → SP)
      * Matrix.scalar ι (ψ (termJ J))) = 0 := by
    have h' : (∑ J ∈ box, cmul (ν J.1 J.2.1 J.2.2) (nb Ω₂ Ω₃ J.1 J.2.1 J.2.2)) = 0 := by
      rw [hbox, Finset.sum_product, ← h]
      exact Finset.sum_congr rfl fun j' _ => Finset.sum_product _ _ _
    have := congrArg (symb n) h'
    rw [symb_finset_sum, symb_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun J hJ => (symb_cmul_nb hΩ _ J (hle J hJ)).symm

  have hentry : ∀ i l : ι, ν J₀.1 J₀.2.1 J₀.2.2 i l = 0 := by
    intro i l
    have hrel := terms_indep n (fun J => if J ∈ box then ν J.1 J.2.1 J.2.2 i l else 0) ?_ J₀ hJ₀tri
    · simpa [hJ₀box] using hrel

    have hentries := congrFun (congrFun hsymb i) l
    rw [Matrix.sum_apply, Matrix.zero_apply] at hentries
    rw [← hentries, ← Finset.sum_filter_of_ne (p := fun J => J ∈ box) (s := tri n)
      (fun J _ hJ => by by_contra hJb; exact hJ (by simp [hJb])),
      ← Finset.sum_filter_of_ne (p := fun J => J ∈ tri n) (s := box) (fun J _ hJ => by
        by_contra hJt; exact hJ (by simp [hJt]))]
    have hsets : (tri n).filter (fun J => J ∈ box) = box.filter fun J => J ∈ tri n := by
      ext J; simp only [Finset.mem_filter]; exact and_comm
    rw [hsets]
    refine Finset.sum_congr rfl fun J hJ => ?_
    obtain ⟨hJb, hJt⟩ := Finset.mem_filter.mp hJ
    beta_reduce
    rw [if_pos hJb, if_pos hJt, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.map_apply]
  exact hJ₀ne (Matrix.ext hentry)

private theorem range_mono {a b : ℕ} (h : a ≤ b) : Finset.range a ⊆ Finset.range b := fun x hx =>
  Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega)

private theorem comp_zero' (D : DOp ι) : comp D (0 : DOp ι) = 0 := by
  have h := comp_add D 0 0
  rw [add_zero] at h
  have h2 : comp D 0 + comp D 0 = comp D 0 + 0 := by rw [add_zero]; exact h.symm
  exact (add_left_cancel h2).symm ▸ rfl

private theorem zero_comp' (D : DOp ι) : comp (0 : DOp ι) D = 0 := by
  have h := add_comp 0 0 D
  rw [add_zero] at h
  have h2 : comp 0 D + comp 0 D = comp 0 D + 0 := by rw [add_zero]; exact h.symm
  exact (add_left_cancel h2).symm ▸ rfl

private theorem comp_finset_sum (D : DOp ι) {κ : Type} (s : Finset κ) (g : κ → DOp ι) :
    comp D (∑ c ∈ s, g c) = ∑ c ∈ s, comp D (g c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [comp_zero']
  | insert c s hc ih => rw [Finset.sum_insert hc, comp_add, ih, Finset.sum_insert hc]

private theorem finset_sum_comp {κ : Type} (s : Finset κ) (g : κ → DOp ι) (D : DOp ι) :
    comp (∑ c ∈ s, g c) D = ∑ c ∈ s, comp (g c) D := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_comp']
  | insert c s hc ih => rw [Finset.sum_insert hc, add_comp, ih, Finset.sum_insert hc]

private theorem cmul_smul' (M : Matrix ι ι Coef) (c : ℂ) (D : DOp ι) : cmul M (c • D) = cmul (c • M) D := by
  ext x : 1
  rw [cmul_apply, cmul_apply, Finsupp.smul_apply, Matrix.mul_smul, Matrix.smul_mul]

private theorem comp_npow_npow (Ω : DOp ι) (m n : ℕ) : comp (npow Ω m) (npow Ω n) = npow Ω (m + n) := by
  induction m with
  | zero => simp only [npow, Function.iterate_zero, id_eq, Nat.zero_add]; exact one_comp _
  | succ m ih => rw [npow_succ', comp_assoc, ih, Nat.succ_add, ← npow_succ']

private theorem comp_npow₃_Ω₂ {Ω₂ Ω₃ : DOp ι} (hΩ : IsCasimirPair Ω₂ Ω₃) (f : ℕ) :
    comp (npow Ω₃ f) Ω₂ = comp Ω₂ (npow Ω₃ f) := by
  induction f with
  | zero => simp only [npow, Function.iterate_zero, id_eq]; rw [one_comp, comp_one]
  | succ f ih => rw [npow_succ', comp_assoc, ih, ← comp_assoc, ← hΩ.comm, comp_assoc]

private theorem comp_npow₃_npow₂ {Ω₂ Ω₃ : DOp ι} (hΩ : IsCasimirPair Ω₂ Ω₃) (f k : ℕ) :
    comp (npow Ω₃ f) (npow Ω₂ k) = comp (npow Ω₂ k) (npow Ω₃ f) := by
  induction k with
  | zero => simp only [npow, Function.iterate_zero, id_eq]; rw [one_comp, comp_one]
  | succ k ih =>
    rw [npow_succ' Ω₂, ← comp_assoc, comp_npow₃_Ω₂ hΩ, comp_assoc, ih, ← comp_assoc]

private theorem nb_comp_npow₂ {Ω₂ Ω₃ : DOp ι} (hΩ : IsCasimirPair Ω₂ Ω₃) (j : Fin 6) (e f k : ℕ) :
    comp (nb Ω₂ Ω₃ j e f) (npow Ω₂ k) = nb Ω₂ Ω₃ j (e + k) f := by
  simp only [nb]
  rw [comp_assoc, comp_assoc, comp_npow₃_npow₂ hΩ, ← comp_assoc (npow Ω₂ e), comp_npow_npow]

private theorem nb_comp_npow₃ {Ω₂ Ω₃ : DOp ι} (j : Fin 6) (e f k : ℕ) :
    comp (nb Ω₂ Ω₃ j e f) (npow Ω₃ k) = nb Ω₂ Ω₃ j e (f + k) := by
  simp only [nb]
  rw [comp_assoc, comp_assoc, comp_npow_npow]

private noncomputable def tsum (Ω₂ Ω₃ : DOp ι) (K : ℕ) (T : Fin 6 → ℕ → ℕ → Matrix ι ι Coef) : DOp ι :=
  ∑ j, ∑ e ∈ Finset.range K, ∑ f ∈ Finset.range K, cmul (T j e f) (nb Ω₂ Ω₃ j e f)

private theorem tsum_add (Ω₂ Ω₃ : DOp ι) (K : ℕ) (T T' : Fin 6 → ℕ → ℕ → Matrix ι ι Coef) :
    tsum Ω₂ Ω₃ K (fun j e f => T j e f + T' j e f) = tsum Ω₂ Ω₃ K T + tsum Ω₂ Ω₃ K T' := by
  simp only [tsum, add_cmul, Finset.sum_add_distrib]

private theorem tsum_sub (Ω₂ Ω₃ : DOp ι) (K : ℕ) (T T' : Fin 6 → ℕ → ℕ → Matrix ι ι Coef) :
    tsum Ω₂ Ω₃ K (fun j e f => T j e f - T' j e f) = tsum Ω₂ Ω₃ K T - tsum Ω₂ Ω₃ K T' := by
  have h := tsum_add Ω₂ Ω₃ K (fun j e f => T j e f - T' j e f) T'
  simp only [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

private theorem tsum_smul (Ω₂ Ω₃ : DOp ι) (K : ℕ) (c : ℂ) (T : Fin 6 → ℕ → ℕ → Matrix ι ι Coef) :
    tsum Ω₂ Ω₃ K (fun j e f => c • T j e f) = c • tsum Ω₂ Ω₃ K T := by
  simp only [tsum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  ext x : 1
  rw [cmul_apply, Finsupp.smul_apply, cmul_apply, Matrix.smul_mul]

private theorem tsum_finset_sum (Ω₂ Ω₃ : DOp ι) (K : ℕ) {κ : Type} (s : Finset κ)
    (T : κ → Fin 6 → ℕ → ℕ → Matrix ι ι Coef) :
    tsum Ω₂ Ω₃ K (fun j e f => ∑ c ∈ s, T c j e f) = ∑ c ∈ s, tsum Ω₂ Ω₃ K (T c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tsum, cmul_zero_left]
  | insert c s hc ih =>
    simp only [Finset.sum_insert hc]
    rw [← ih, ← tsum_add]

private theorem tsum_mono_box (Ω₂ Ω₃ : DOp ι) {K K' : ℕ} (hK : K ≤ K') (T : Fin 6 → ℕ → ℕ → Matrix ι ι Coef)
    (hT : ∀ j e f, K ≤ e ∨ K ≤ f → T j e f = 0) : tsum Ω₂ Ω₃ K T = tsum Ω₂ Ω₃ K' T := by
  have hrange := range_mono hK
  simp only [tsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_subset hrange]
  · refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_subset hrange]
    intro f _ hf
    rw [hT j e f (Or.inr (by simpa using hf)), cmul_zero_left]
  · intro e _ he
    refine Finset.sum_eq_zero fun f _ => ?_
    rw [hT j e f (Or.inl (by simpa using he)), cmul_zero_left]

private noncomputable def shiftE (m : ℕ) (T : Fin 6 → ℕ → ℕ → Matrix ι ι Coef) : Fin 6 → ℕ → ℕ → Matrix ι ι Coef :=
  fun j e f => if m ≤ e then T j (e - m) f else 0

private noncomputable def shiftF (m : ℕ) (T : Fin 6 → ℕ → ℕ → Matrix ι ι Coef) : Fin 6 → ℕ → ℕ → Matrix ι ι Coef :=
  fun j e f => if m ≤ f then T j e (f - m) else 0

private theorem shiftE_add (m : ℕ) (T : Fin 6 → ℕ → ℕ → Matrix ι ι Coef) (j : Fin 6) (e f : ℕ) :
    shiftE m T j (m + e) f = T j e f := by
  simp only [shiftE, Nat.le_add_right, if_true, Nat.add_sub_cancel_left]

private theorem shiftF_add (m : ℕ) (T : Fin 6 → ℕ → ℕ → Matrix ι ι Coef) (j : Fin 6) (e f : ℕ) :
    shiftF m T j e (m + f) = T j e f := by
  simp only [shiftF, Nat.le_add_right, if_true, Nat.add_sub_cancel_left]

private theorem tsum_comp_npow₂ {Ω₂ Ω₃ : DOp ι} (hΩ : IsCasimirPair Ω₂ Ω₃) {K : ℕ}
    (T : Fin 6 → ℕ → ℕ → Matrix ι ι Coef) (hT : ∀ j e f, K ≤ e ∨ K ≤ f → T j e f = 0) (m K' : ℕ) (hK' : K + m ≤ K') :
    comp (tsum Ω₂ Ω₃ K T) (npow Ω₂ m) = tsum Ω₂ Ω₃ K' (shiftE m T) := by
  simp only [tsum, finset_sum_comp, cmul_comp, nb_comp_npow₂ hΩ]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hlow : (∑ e ∈ Finset.range m, ∑ f ∈ Finset.range K', cmul (shiftE m T j e f) (nb Ω₂ Ω₃ j e f)) = 0 := by
    refine Finset.sum_eq_zero fun e he => Finset.sum_eq_zero fun f _ => ?_
    have : ¬ m ≤ e := by have := Finset.mem_range.mp he; omega
    simp only [shiftE, this, if_false, cmul_zero_left]
  have hhigh : (∑ e ∈ Finset.Ico m K', ∑ f ∈ Finset.range K', cmul (shiftE m T j e f) (nb Ω₂ Ω₃ j e f))
      = ∑ e ∈ Finset.range K, ∑ f ∈ Finset.range K, cmul (T j e f) (nb Ω₂ Ω₃ j (e + m) f) := by
    rw [Finset.sum_Ico_eq_sum_range, ← Finset.sum_subset (range_mono (show K ≤ K' - m by omega))]
    · refine Finset.sum_congr rfl fun e _ => ?_
      rw [← Finset.sum_subset (range_mono (show K ≤ K' by omega))]
      · refine Finset.sum_congr rfl fun f _ => ?_
        rw [shiftE_add, Nat.add_comm m e]
      · intro f _ hf
        rw [shiftE_add, hT j e f (Or.inr (by simpa using hf)), cmul_zero_left]
    · intro e _ he
      refine Finset.sum_eq_zero fun f _ => ?_
      rw [shiftE_add, hT j e f (Or.inl (by simpa using he)), cmul_zero_left]
  rw [← Finset.sum_range_add_sum_Ico _ (show m ≤ K' by omega), hlow, zero_add, hhigh]

private theorem tsum_comp_npow₃ (Ω₂ Ω₃ : DOp ι) {K : ℕ} (T : Fin 6 → ℕ → ℕ → Matrix ι ι Coef)
    (hT : ∀ j e f, K ≤ e ∨ K ≤ f → T j e f = 0) (m K' : ℕ) (hK' : K + m ≤ K') :
    comp (tsum Ω₂ Ω₃ K T) (npow Ω₃ m) = tsum Ω₂ Ω₃ K' (shiftF m T) := by
  simp only [tsum, finset_sum_comp, cmul_comp, nb_comp_npow₃]
  refine Finset.sum_congr rfl fun j _ => ?_
  symm
  rw [← Finset.sum_subset (range_mono (show K ≤ K' by omega))]
  · refine Finset.sum_congr rfl fun e _ => ?_
    have hlow : (∑ f ∈ Finset.range m, cmul (shiftF m T j e f) (nb Ω₂ Ω₃ j e f)) = 0 := by
      refine Finset.sum_eq_zero fun f hf => ?_
      have : ¬ m ≤ f := by have := Finset.mem_range.mp hf; omega
      simp only [shiftF, this, if_false, cmul_zero_left]
    rw [← Finset.sum_range_add_sum_Ico _ (show m ≤ K' by omega), hlow, zero_add, Finset.sum_Ico_eq_sum_range,
      ← Finset.sum_subset (range_mono (show K ≤ K' - m by omega))]
    · refine Finset.sum_congr rfl fun f _ => ?_
      rw [shiftF_add, Nat.add_comm m f]
    · intro f _ hf
      rw [shiftF_add, hT j e f (Or.inr (by simpa using hf)), cmul_zero_left]
  · intro e _ he
    refine Finset.sum_eq_zero fun f _ => ?_
    simp only [shiftF]
    split_ifs
    · rw [hT j e _ (Or.inl (by simpa using he)), cmul_zero_left]
    · exact cmul_zero_left _

private noncomputable def convE {N : ℕ} (a : Fin (N + 1) → ℂ) (T : Fin 6 → ℕ → ℕ → Matrix ι ι Coef) :
    Fin 6 → ℕ → ℕ → Matrix ι ι Coef :=
  fun j e f => ∑ m : Fin (N + 1), a m • shiftE (m : ℕ) T j e f

private noncomputable def convF {N : ℕ} (a : Fin (N + 1) → ℂ) (T : Fin 6 → ℕ → ℕ → Matrix ι ι Coef) :
    Fin 6 → ℕ → ℕ → Matrix ι ι Coef :=
  fun j e f => ∑ m : Fin (N + 1), a m • shiftF (m : ℕ) T j e f

private theorem tsum_comp_polyOp₂ {Ω₂ Ω₃ : DOp ι} (hΩ : IsCasimirPair Ω₂ Ω₃) {K : ℕ}
    (T : Fin 6 → ℕ → ℕ → Matrix ι ι Coef) (hT : ∀ j e f, K ≤ e ∨ K ≤ f → T j e f = 0) {N : ℕ} (a : Fin (N + 1) → ℂ)
    (K' : ℕ) (hK' : K + N ≤ K') : comp (tsum Ω₂ Ω₃ K T) (polyOp a Ω₂) = tsum Ω₂ Ω₃ K' (convE a T) := by
  simp only [polyOp, comp_finset_sum, comp_smul]
  show _ = tsum Ω₂ Ω₃ K' (fun j e f => ∑ m : Fin (N + 1), a m • shiftE (m : ℕ) T j e f)
  rw [tsum_finset_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [tsum_comp_npow₂ hΩ T hT m K' (by have := m.isLt; omega), tsum_smul]

private theorem tsum_comp_polyOp₃ {Ω₂ Ω₃ : DOp ι} {K : ℕ}
    (T : Fin 6 → ℕ → ℕ → Matrix ι ι Coef) (hT : ∀ j e f, K ≤ e ∨ K ≤ f → T j e f = 0) {N : ℕ} (a : Fin (N + 1) → ℂ)
    (K' : ℕ) (hK' : K + N ≤ K') : comp (tsum Ω₂ Ω₃ K T) (polyOp a Ω₃) = tsum Ω₂ Ω₃ K' (convF a T) := by
  simp only [polyOp, comp_finset_sum, comp_smul]
  show _ = tsum Ω₂ Ω₃ K' (fun j e f => ∑ m : Fin (N + 1), a m • shiftF (m : ℕ) T j e f)
  rw [tsum_finset_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [tsum_comp_npow₃ Ω₂ Ω₃ T hT m K' (by have := m.isLt; omega), tsum_smul]

private theorem exists_tsum {Ω₂ Ω₃ : DOp ι} (hΩ : IsCasimirPair Ω₂ Ω₃) (Y : DOp ι) :
    ∃ (K : ℕ) (T : Fin 6 → ℕ → ℕ → Matrix ι ι Coef), (∀ j e f, K ≤ e ∨ K ≤ f → T j e f = 0) ∧ Y = tsum Ω₂ Ω₃ K T := by
  obtain ⟨ν, hν, hY⟩ := normalOrder_exists hΩ Y (Y.support.sup fun ab => ab.1 + ab.2) fun ab hab =>
    Finset.le_sup (f := fun ab : ℕ × ℕ => ab.1 + ab.2) hab
  refine ⟨_ + 1, ν, fun j e f hef => ?_, hY⟩
  by_contra hne
  have := hν j e f hne
  omega

private noncomputable def extT {N₂ N₃ : ℕ} (ν : Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef) :
    Fin 6 → ℕ → ℕ → Matrix ι ι Coef :=
  fun j e f => if he : e < N₂ then (if hf : f < N₃ then ν j ⟨e, he⟩ ⟨f, hf⟩ else 0) else 0

private theorem extT_of_ge {N₂ N₃ : ℕ} (ν : Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef) (j : Fin 6) {e f : ℕ}
    (h : N₂ ≤ e ∨ N₃ ≤ f) : extT ν j e f = 0 := by
  unfold extT
  rcases h with h | h
  · rw [dif_neg (by omega)]
  · by_cases he : e < N₂
    · rw [dif_pos he, dif_neg (by omega)]
    · rw [dif_neg he]

private theorem extT_fin {N₂ N₃ : ℕ} (ν : Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef) (j : Fin 6) (e : Fin N₂)
    (f : Fin N₃) :
    extT ν j e f = ν j e f := by
  simp only [extT, e.isLt, f.isLt, dif_pos, Fin.eta]

private theorem reduced_eq_tsum (Ω₂ Ω₃ : DOp ι) {N₂ N₃ : ℕ} (ν : Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef) {K : ℕ}
    (h₂ : N₂ ≤ K) (h₃ : N₃ ≤ K) :
    (∑ j : Fin 6, ∑ e : Fin N₂, ∑ f : Fin N₃, cmul (ν j e f) (nb Ω₂ Ω₃ j e f)) = tsum Ω₂ Ω₃ K (extT ν) := by
  simp only [tsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_subset (range_mono h₂) (fun e _ he => Finset.sum_eq_zero fun f _ => by
        rw [extT_of_ge ν j (Or.inl (by simpa using he)), cmul_zero_left]) |>.symm,
    Finset.sum_range]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_subset (range_mono h₃) (fun f _ hf => by
        rw [extT_of_ge ν j (Or.inr (by simpa using hf)), cmul_zero_left]) |>.symm,
    Finset.sum_range]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [extT_fin]

private theorem exists_table_identity {Ω₂ Ω₃ : DOp ι} (hΩ : IsCasimirPair Ω₂ Ω₃) {N₂ N₃ : ℕ}
    (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ) (ν : Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef) (Y Y' : DOp ι)
    (h : (∑ j : Fin 6, ∑ e : Fin N₂, ∑ f : Fin N₃, cmul (ν j e f) (nb Ω₂ Ω₃ j e f))
      = comp Y (polyOp a₂ Ω₂) + comp Y' (polyOp a₃ Ω₃)) :
    ∃ (K₀ K : ℕ) (μ μ' : Fin 6 → ℕ → ℕ → Matrix ι ι Coef),
      N₂ ≤ K ∧ N₃ ≤ K ∧ K₀ + N₂ < K ∧ K₀ + N₃ < K ∧
      (∀ j e f, K₀ ≤ e ∨ K₀ ≤ f → μ j e f = 0) ∧ (∀ j e f, K₀ ≤ e ∨ K₀ ≤ f → μ' j e f = 0) ∧
      ∀ j, ∀ e < K, ∀ f < K, extT ν j e f = convE a₂ μ j e f + convF a₃ μ' j e f := by
  obtain ⟨K₁, μ, hμ, rfl⟩ := exists_tsum hΩ Y
  obtain ⟨K₂, μ', hμ', rfl⟩ := exists_tsum hΩ Y'
  set K₀ := K₁ + K₂ with hK₀
  set K := K₀ + N₂ + N₃ + 1 with hK
  have hμ₀ : ∀ j e f, K₀ ≤ e ∨ K₀ ≤ f → μ j e f = 0 := fun j e f hef => hμ j e f (by omega)
  have hμ'₀ : ∀ j e f, K₀ ≤ e ∨ K₀ ≤ f → μ' j e f = 0 := fun j e f hef => hμ' j e f (by omega)
  refine ⟨K₀, K, μ, μ', by omega, by omega, by omega, by omega, hμ₀, hμ'₀, ?_⟩
  rw [reduced_eq_tsum Ω₂ Ω₃ ν (K := K) (by omega) (by omega), tsum_comp_polyOp₂ hΩ μ hμ a₂ K (by omega),
    tsum_comp_polyOp₃ μ' hμ' a₃ K (by omega), ← tsum_add, ← sub_eq_zero, ← tsum_sub] at h
  intro j e he f hf
  have := normalOrder_unique hΩ K _ h j e he f hf
  exact sub_eq_zero.mp this

private noncomputable def cv {N : ℕ} (a : Fin (N + 1) → ℂ) (t : ℕ → ℕ → Matrix ι ι Coef) (e f : ℕ) : Matrix ι ι Coef :=
  ∑ m : Fin (N + 1), a m • (if (m : ℕ) ≤ e then t (e - m) f else 0)

private def swapT (t : ℕ → ℕ → Matrix ι ι Coef) : ℕ → ℕ → Matrix ι ι Coef := fun e f => t f e

private theorem convE_eq {N : ℕ} (a : Fin (N + 1) → ℂ) (μ : Fin 6 → ℕ → ℕ → Matrix ι ι Coef) (j : Fin 6) (e f : ℕ) :
    convE a μ j e f = cv a (μ j) e f := rfl

private theorem convF_eq {N : ℕ} (a : Fin (N + 1) → ℂ) (μ : Fin 6 → ℕ → ℕ → Matrix ι ι Coef) (j : Fin 6) (e f : ℕ) :
    convF a μ j e f = swapT (cv a (swapT (μ j))) e f := rfl

private theorem cv_add {N : ℕ} (a : Fin (N + 1) → ℂ) (t t' : ℕ → ℕ → Matrix ι ι Coef) (e f : ℕ) :
    cv a (fun e f => t e f + t' e f) e f = cv a t e f + cv a t' e f := by
  simp only [cv, ← Finset.sum_add_distrib, ← smul_add]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> simp

private theorem cv_sub {N : ℕ} (a : Fin (N + 1) → ℂ) (t t' : ℕ → ℕ → Matrix ι ι Coef) (e f : ℕ) :
    cv a (fun e f => t e f - t' e f) e f = cv a t e f - cv a t' e f := by
  simp only [cv, ← Finset.sum_sub_distrib, ← smul_sub]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> simp

private theorem cv_zero {N : ℕ} (a : Fin (N + 1) → ℂ) (e f : ℕ) : cv a (fun _ _ => (0 : Matrix ι ι Coef)) e f = 0 := by
  simp [cv]

private theorem cv_eq_zero_of_col {N : ℕ} (a : Fin (N + 1) → ℂ) (t : ℕ → ℕ → Matrix ι ι Coef) {f : ℕ}
    (ht : ∀ e, t e f = 0) (e : ℕ) : cv a t e f = 0 := by
  simp [cv, ht]

private theorem cv_eq_zero_of_above {N : ℕ} (a : Fin (N + 1) → ℂ) (t : ℕ → ℕ → Matrix ι ι Coef) {E₀ : ℕ}
    (ht : ∀ e f, E₀ < e → t e f = 0) {e : ℕ} (he : E₀ + N < e) (f : ℕ) : cv a t e f = 0 := by
  refine Finset.sum_eq_zero fun m _ => ?_
  have hm := m.isLt
  rw [if_pos (by omega), ht _ _ (by omega), smul_zero]

private theorem cv_top {N : ℕ} (a : Fin (N + 1) → ℂ) (ha : a (Fin.last N) = 1) (t : ℕ → ℕ → Matrix ι ι Coef) {E₀ : ℕ}
    (ht : ∀ e f, E₀ < e → t e f = 0) (f : ℕ) : cv a t (E₀ + N) f = t E₀ f := by
  unfold cv
  rw [Finset.sum_eq_single (Fin.last N)]
  · rw [ha, Fin.val_last, if_pos (Nat.le_add_left N E₀), Nat.add_sub_cancel, one_smul]
  · intro m _ hm
    have hlt : (m : ℕ) < N := Fin.val_lt_last hm
    rw [if_pos (by omega), ht _ _ (by omega), smul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem eq_zero_of_cv_eq_zero {N : ℕ} (a : Fin (N + 1) → ℂ) (ha : a (Fin.last N) = 1)
    (t : ℕ → ℕ → Matrix ι ι Coef) {Bd : ℕ} (hB : ∀ e f, Bd ≤ e → t e f = 0) (h : ∀ e f, N ≤ e → cv a t e f = 0) :
    ∀ e f, t e f = 0 := by
  have key : ∀ d e f, Bd ≤ e + d → t e f = 0 := by
    intro d
    induction d with
    | zero => intro e f he; exact hB e f (by omega)
    | succ d ih =>
      intro e f he
      by_cases hBe : Bd ≤ e
      · exact hB e f hBe
      · have htop : ∀ e' f', e < e' → t e' f' = 0 := fun e' f' he' => ih e' f' (by omega)
        rw [← cv_top a ha t htop f]
        exact h _ _ (by omega)
  exact fun e f => key Bd e f (by omega)

private theorem ite_sum {p : Prop} [Decidable p] {κ : Type} (s : Finset κ) (g : κ → Matrix ι ι Coef) :
    (if p then ∑ x ∈ s, g x else 0) = ∑ x ∈ s, if p then g x else 0 := by
  split_ifs <;> simp

private theorem cv_swap_cv {N₂ N₃ : ℕ} (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ) (t : ℕ → ℕ → Matrix ι ι Coef)
    (e f : ℕ) : cv a₂ (swapT (cv a₃ (swapT t))) e f = swapT (cv a₃ (swapT (cv a₂ t))) e f := by
  simp only [cv, swapT, Finset.smul_sum, smul_ite, smul_zero, ite_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : (m : ℕ) ≤ e <;> by_cases hn : (n : ℕ) ≤ f <;> simp only [hm, hn, if_true, if_false]
  rw [smul_smul, smul_smul, mul_comm]

private theorem core_base {N₂ N₃ : ℕ} (a₂ : Fin (N₂ + 1) → ℂ) (ha₂ : a₂ (Fin.last N₂) = 1) (a₃ : Fin (N₃ + 1) → ℂ)
    (ha₃ : a₃ (Fin.last N₃) = 1) (R μ μ' : ℕ → ℕ → Matrix ι ι Coef) (hR : ∀ e f, N₂ ≤ e ∨ N₃ ≤ f → R e f = 0) {Bd : ℕ}
    (hμ : ∀ e f, Bd ≤ e → μ e f = 0) (hμ'e : ∀ e f, N₂ ≤ e → μ' e f = 0) (hμ'f : ∀ e f, Bd ≤ f → μ' e f = 0)
    (hid : ∀ e f, R e f = cv a₂ μ e f + swapT (cv a₃ (swapT μ')) e f) : ∀ e f, R e f = 0 := by

  have hμ0 : ∀ e f, μ e f = 0 := by
    refine eq_zero_of_cv_eq_zero a₂ ha₂ μ hμ fun e f he => ?_
    have h1 := hid e f
    rw [hR e f (Or.inl he)] at h1
    have h2 : swapT (cv a₃ (swapT μ')) e f = 0 := by
      show cv a₃ (swapT μ') f e = 0
      exact cv_eq_zero_of_col a₃ (swapT μ') (fun f' => hμ'e e f' he) f
    rw [h2, add_zero] at h1
    exact h1.symm
  have hμ'0 : ∀ f e, swapT μ' f e = 0 := by
    refine eq_zero_of_cv_eq_zero a₃ ha₃ (swapT μ') (Bd := Bd) (fun f e hf => hμ'f e f hf) fun f e hf => ?_
    have h1 := hid e f
    rw [hR e f (Or.inr hf), cv_eq_zero_of_col a₂ μ (fun e' => hμ0 e' f) e, zero_add] at h1
    exact h1.symm
  intro e f
  rw [hid e f, cv_eq_zero_of_col a₂ μ (fun e' => hμ0 e' f) e, zero_add]
  show cv a₃ (swapT μ') f e = 0
  exact cv_eq_zero_of_col a₃ (swapT μ') (fun f' => hμ'0 f' e) f

private theorem core {N₂ N₃ : ℕ} (a₂ : Fin (N₂ + 1) → ℂ) (ha₂ : a₂ (Fin.last N₂) = 1) (a₃ : Fin (N₃ + 1) → ℂ)
    (ha₃ : a₃ (Fin.last N₃) = 1) (R : ℕ → ℕ → Matrix ι ι Coef) (hR : ∀ e f, N₂ ≤ e ∨ N₃ ≤ f → R e f = 0) :
    ∀ (E : ℕ) (μ μ' : ℕ → ℕ → Matrix ι ι Coef) (Bd : ℕ), (∀ e f, Bd ≤ e → μ e f = 0) → (∀ e f, Bd ≤ f → μ' e f = 0) →
      (∀ e f, E ≤ e → μ' e f = 0) → (∀ e f, R e f = cv a₂ μ e f + swapT (cv a₃ (swapT μ')) e f) →
      ∀ e f, R e f = 0 := by
  intro E
  induction E with
  | zero =>
    intro μ μ' Bd hμ hμ'f hμ'E hid
    exact core_base a₂ ha₂ a₃ ha₃ R μ μ' hR hμ (fun e f _ => hμ'E e f (Nat.zero_le e)) hμ'f hid
  | succ E ih =>
    intro μ μ' Bd hμ hμ'f hμ'E hid
    by_cases hE : E + 1 ≤ N₂
    · exact core_base a₂ ha₂ a₃ ha₃ R μ μ' hR hμ (fun e f he => hμ'E e f (by omega)) hμ'f hid

    set Z : ℕ → ℕ → Matrix ι ι Coef := fun e f => if e = E - N₂ then μ' E f else 0 with hZ
    have hZabove : ∀ e f, E - N₂ < e → Z e f = 0 := fun e f he => by
      simp only [hZ]; rw [if_neg (by omega)]
    have hZcol : ∀ e f, Bd ≤ f → Z e f = 0 := fun e f hf => by
      simp only [hZ]; split_ifs <;> simp [hμ'f E f hf]
    set μ₂ : ℕ → ℕ → Matrix ι ι Coef := fun e f => μ e f + swapT (cv a₃ (swapT Z)) e f with hμ₂
    set μ'₂ : ℕ → ℕ → Matrix ι ι Coef := fun e f => μ' e f - cv a₂ Z e f with hμ'₂
    refine ih μ₂ μ'₂ (max Bd (E + 1)) ?_ ?_ ?_ ?_
    ·
      intro e f he
      simp only [hμ₂]
      rw [hμ e f (by omega)]
      show 0 + cv a₃ (swapT Z) f e = 0
      rw [cv_eq_zero_of_col a₃ (swapT Z) (fun f' => hZabove e f' (by omega)) f, add_zero]
    ·
      intro e f hf
      simp only [hμ'₂]
      rw [hμ'f e f (by omega), cv_eq_zero_of_col a₂ Z (fun e' => hZcol e' f (by omega)) e, sub_zero]
    ·
      intro e f he
      simp only [hμ'₂]
      rcases he.lt_or_eq with hlt | rfl
      · rw [hμ'E e f (by omega), cv_eq_zero_of_above a₂ Z hZabove (by omega) f, sub_zero]
      · have htop := cv_top a₂ ha₂ Z hZabove f
        rw [show E - N₂ + N₂ = E by omega] at htop
        rw [htop]
        simp only [hZ, if_true, sub_self]
    ·
      intro e f
      rw [hid e f]
      simp only [hμ₂, hμ'₂]
      rw [cv_add]
      show _ = cv a₂ μ e f + cv a₂ (swapT (cv a₃ (swapT Z))) e f + cv a₃ (swapT (fun e f => μ' e f - cv a₂ Z e f)) f e
      have hsw : swapT (fun e f => μ' e f - cv a₂ Z e f) = fun f e => swapT μ' f e - swapT (cv a₂ Z) f e := rfl
      rw [hsw, cv_sub, cv_swap_cv]
      show cv a₂ μ e f + cv a₃ (swapT μ') f e = cv a₂ μ e f + cv a₃ (swapT (cv a₂ Z)) f e
        + (cv a₃ (swapT μ') f e - cv a₃ (swapT (cv a₂ Z)) f e)
      abel

private theorem normalForm_unique_mod {Ω₂ Ω₃ : DOp ι} (hΩ : IsCasimirPair Ω₂ Ω₃) {N₂ N₃ : ℕ}
    (a₂ : Fin (N₂ + 1) → ℂ) (ha₂ : a₂ (Fin.last N₂) = 1) (a₃ : Fin (N₃ + 1) → ℂ) (ha₃ : a₃ (Fin.last N₃) = 1)
    (ν : Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef) (Y Y' : DOp ι)
    (h : ∑ j : Fin 6, ∑ e : Fin N₂, ∑ f : Fin N₃, cmul (ν j e f) (nb Ω₂ Ω₃ j e f)
      = comp Y (polyOp a₂ Ω₂) + comp Y' (polyOp a₃ Ω₃)) :
    ∀ j e f, ν j e f = 0 := by
  classical
  obtain ⟨K₀, K, μ, μ', hN₂, hN₃, hK₀₂, hK₀₃, hμ, hμ', hid⟩ := exists_table_identity hΩ a₂ a₃ ν Y Y' h
  intro j e f

  have hid' : ∀ e' f', extT ν j e' f' = cv a₂ (μ j) e' f' + swapT (cv a₃ (swapT (μ' j))) e' f' := by
    intro e' f'
    by_cases hbox : e' < K ∧ f' < K
    · rw [hid j e' hbox.1 f' hbox.2, convE_eq, convF_eq]
    · rw [extT_of_ge ν j (by omega)]
      have h1 : cv a₂ (μ j) e' f' = 0 := by
        rcases not_and_or.mp hbox with he' | hf'
        · exact cv_eq_zero_of_above a₂ (μ j) (E₀ := K₀) (fun e'' f'' he'' => hμ j e'' f'' (Or.inl (by omega)))
            (by omega) f'
        · exact cv_eq_zero_of_col a₂ (μ j) (fun e'' => hμ j e'' f' (Or.inr (by omega))) e'
      have h2 : cv a₃ (swapT (μ' j)) f' e' = 0 := by
        rcases not_and_or.mp hbox with he' | hf'
        · exact cv_eq_zero_of_col a₃ (swapT (μ' j)) (fun f'' => hμ' j e' f'' (Or.inl (by omega))) f'
        · exact cv_eq_zero_of_above a₃ (swapT (μ' j)) (E₀ := K₀)
            (fun f'' e'' hf'' => hμ' j e'' f'' (Or.inr (by omega))) (by omega) e'
      rw [h1]
      show (0 : Matrix ι ι Coef) = 0 + cv a₃ (swapT (μ' j)) f' e'
      rw [h2, add_zero]
  have hzero := core a₂ ha₂ a₃ ha₃ (extT ν j) (fun e' f' h' => extT_of_ge ν j h') K₀ (μ j) (μ' j) K₀
    (fun e' f' he' => hμ j e' f' (Or.inl he')) (fun e' f' hf' => hμ' j e' f' (Or.inr hf'))
    (fun e' f' he' => hμ' j e' f' (Or.inl he')) hid' e f
  rwa [extT_fin] at hzero

private abbrev RIdx (N₂ N₃ : ℕ) (ι : Type) := Fin 6 × Fin N₂ × Fin N₃ × ι

private noncomputable def frame (Ω₂ Ω₃ : DOp ι) (N₂ N₃ : ℕ) (Φ₀ : ℝ → ℝ → (ι → ℂ)) :
    ℝ → ℝ → (RIdx N₂ N₃ ι → ℂ) :=
  fun t₁ t₂ J => apply (nb Ω₂ Ω₃ J.1 J.2.1 J.2.2.1) Φ₀ t₁ t₂ J.2.2.2

section Reduction

variable (Ω₂ Ω₃ : DOp ι) {N₂ N₃ : ℕ}

private noncomputable def rsum (T : Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef) : DOp ι :=
  ∑ j : Fin 6, ∑ e : Fin N₂, ∑ f : Fin N₃, cmul (T j e f) (nb Ω₂ Ω₃ j e f)

private def RedT (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ) (D : DOp ι)
    (T : Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef) : Prop :=
  ∃ Y Y' : DOp ι, D = rsum Ω₂ Ω₃ T + comp Y (polyOp a₂ Ω₂) + comp Y' (polyOp a₃ Ω₃)

variable {Ω₂ Ω₃}

private theorem rsum_add (T T' : Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef) :
    rsum Ω₂ Ω₃ (fun j e f => T j e f + T' j e f) = rsum Ω₂ Ω₃ T + rsum Ω₂ Ω₃ T' := by
  simp only [rsum, add_cmul, Finset.sum_add_distrib]

private theorem rsum_zero : rsum Ω₂ Ω₃ (fun (_ : Fin 6) (_ : Fin N₂) (_ : Fin N₃) => (0 : Matrix ι ι Coef)) = 0 := by
  simp [rsum, cmul_zero_left]

private theorem rsum_sub (T T' : Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef) :
    rsum Ω₂ Ω₃ (fun j e f => T j e f - T' j e f) = rsum Ω₂ Ω₃ T - rsum Ω₂ Ω₃ T' := by
  have h := rsum_add (Ω₂ := Ω₂) (Ω₃ := Ω₃) (fun j e f => T j e f - T' j e f) T'
  simp only [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

private theorem cmul_rsum (M : Matrix ι ι Coef) (T : Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef) :
    cmul M (rsum Ω₂ Ω₃ T) = rsum Ω₂ Ω₃ (fun j e f => M * T j e f) := by
  simp only [rsum, cmul_finset_sum, cmul_cmul]

private theorem smul_rsum (c : ℂ) (T : Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef) :
    c • rsum Ω₂ Ω₃ T = rsum Ω₂ Ω₃ (fun j e f => c • T j e f) := by
  simp only [rsum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  ext x : 1
  rw [Finsupp.smul_apply, cmul_apply, cmul_apply, Matrix.smul_mul]

private theorem rsum_finset_sum {κ : Type} (s : Finset κ) (T : κ → Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef) :
    rsum Ω₂ Ω₃ (fun j e f => ∑ c ∈ s, T c j e f) = ∑ c ∈ s, rsum Ω₂ Ω₃ (T c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rsum_zero (Ω₂ := Ω₂) (Ω₃ := Ω₃) (N₂ := N₂) (N₃ := N₃)
  | insert c s hc ih =>
    simp only [Finset.sum_insert hc]
    rw [← ih, ← rsum_add]

private theorem neg_comp' (D D' : DOp ι) : comp (-D) D' = -comp D D' := by
  have h := add_comp D (-D) D'
  rw [add_neg_cancel, zero_comp'] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

private theorem sub_comp' (D₁ D₂ D' : DOp ι) : comp (D₁ - D₂) D' = comp D₁ D' - comp D₂ D' := by
  rw [sub_eq_add_neg, add_comp, neg_comp', sub_eq_add_neg]

variable (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ)

private theorem redT_rsum (T : Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef) : RedT Ω₂ Ω₃ a₂ a₃ (rsum Ω₂ Ω₃ T) T :=
  ⟨0, 0, by rw [zero_comp', zero_comp', add_zero, add_zero]⟩

private theorem redT_zero : RedT Ω₂ Ω₃ a₂ a₃ 0 (fun _ _ _ => 0) :=
  ⟨0, 0, by rw [rsum_zero, zero_comp', zero_comp', add_zero, add_zero]⟩

private theorem redT_ideal₂ (Y : DOp ι) : RedT Ω₂ Ω₃ a₂ a₃ (comp Y (polyOp a₂ Ω₂)) (fun _ _ _ => 0) :=
  ⟨Y, 0, by rw [rsum_zero, zero_comp', zero_add, add_zero]⟩

private theorem redT_ideal₃ (Y' : DOp ι) : RedT Ω₂ Ω₃ a₂ a₃ (comp Y' (polyOp a₃ Ω₃)) (fun _ _ _ => 0) :=
  ⟨0, Y', by rw [rsum_zero, zero_comp', zero_add, zero_add]⟩

variable {a₂ a₃}

private theorem redT_add {D D' : DOp ι} {T T' : Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef}
    (h : RedT Ω₂ Ω₃ a₂ a₃ D T) (h' : RedT Ω₂ Ω₃ a₂ a₃ D' T') :
    RedT Ω₂ Ω₃ a₂ a₃ (D + D') (fun j e f => T j e f + T' j e f) := by
  obtain ⟨Y₁, Y₁', rfl⟩ := h
  obtain ⟨Y₂, Y₂', rfl⟩ := h'
  refine ⟨Y₁ + Y₂, Y₁' + Y₂', ?_⟩
  rw [rsum_add, add_comp, add_comp]
  abel

private theorem redT_cmul {D : DOp ι} {T : Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef} (h : RedT Ω₂ Ω₃ a₂ a₃ D T)
    (M : Matrix ι ι Coef) : RedT Ω₂ Ω₃ a₂ a₃ (cmul M D) (fun j e f => M * T j e f) := by
  obtain ⟨Y, Y', rfl⟩ := h
  exact ⟨cmul M Y, cmul M Y', by rw [cmul_add, cmul_add, cmul_rsum, cmul_comp, cmul_comp]⟩

private theorem redT_smul {D : DOp ι} {T : Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef} (h : RedT Ω₂ Ω₃ a₂ a₃ D T)
    (c : ℂ) : RedT Ω₂ Ω₃ a₂ a₃ (c • D) (fun j e f => c • T j e f) := by
  obtain ⟨Y, Y', rfl⟩ := h
  exact ⟨c • Y, c • Y', by rw [smul_add, smul_add, smul_rsum, smul_comp, smul_comp]⟩

private theorem redT_sum {κ : Type} (s : Finset κ) {g : κ → DOp ι} {Tg : κ → Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef}
    (h : ∀ c ∈ s, RedT Ω₂ Ω₃ a₂ a₃ (g c) (Tg c)) :
    RedT Ω₂ Ω₃ a₂ a₃ (∑ c ∈ s, g c) (fun j e f => ∑ c ∈ s, Tg c j e f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using redT_zero (Ω₂ := Ω₂) (Ω₃ := Ω₃) a₂ a₃
  | insert c s hc ih =>
    simp only [Finset.sum_insert hc]
    exact redT_add (h c (Finset.mem_insert_self c s)) (ih fun c' hc' => h c' (Finset.mem_insert_of_mem hc'))

private theorem redT_congr {D : DOp ι} {T T' : Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef} (h : RedT Ω₂ Ω₃ a₂ a₃ D T)
    (hT : ∀ j e f, T j e f = T' j e f) : RedT Ω₂ Ω₃ a₂ a₃ D T' := by
  have : T = T' := funext fun j => funext fun e => funext fun f => hT j e f
  exact this ▸ h

private noncomputable def unitT (j₀ : Fin 6) (e₀ : Fin N₂) (f₀ : Fin N₃) : Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef :=
  fun j e f => if j = j₀ then (if e = e₀ then (if f = f₀ then 1 else 0) else 0) else 0

private theorem rsum_unitT (j₀ : Fin 6) (e₀ : Fin N₂) (f₀ : Fin N₃) :
    rsum Ω₂ Ω₃ (unitT (ι := ι) j₀ e₀ f₀) = nb Ω₂ Ω₃ j₀ e₀ f₀ := by
  simp only [rsum, unitT]
  rw [Finset.sum_eq_single j₀]
  · rw [Finset.sum_eq_single e₀]
    · rw [Finset.sum_eq_single f₀]
      · simp only [if_true]; exact cmul_one_eq _
      · intro f _ hf; simp only [if_true, hf, if_false, cmul_zero_left]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro e _ he
      refine Finset.sum_eq_zero fun f _ => ?_
      simp only [if_true, he, if_false, cmul_zero_left]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro j _ hj
    refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun f _ => ?_
    simp only [hj, if_false, cmul_zero_left]
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem redT_nb_reduced (j : Fin 6) (e : Fin N₂) (f : Fin N₃) :
    RedT Ω₂ Ω₃ a₂ a₃ (nb Ω₂ Ω₃ j e f) (unitT j e f) := by
  rw [← rsum_unitT (Ω₂ := Ω₂) (Ω₃ := Ω₃) j e f]
  exact redT_rsum a₂ a₃ _

private theorem npow_eq_polyOp_sub {N : ℕ} (a : Fin (N + 1) → ℂ) (ha : a (Fin.last N) = 1) (Ω : DOp ι) :
    npow Ω N = polyOp a Ω - ∑ m : Fin N, a m.castSucc • npow Ω m := by
  rw [polyOp, Fin.sum_univ_castSucc, ha, Fin.val_last, one_smul]
  simp only [Fin.coe_castSucc]
  abel

end Reduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

section ReductionTheorems

variable {Ω₂ Ω₃ : DOp ι} {N₂ N₃ : ℕ} {a₂ : Fin (N₂ + 1) → ℂ} {a₃ : Fin (N₃ + 1) → ℂ}

private theorem comp_neg' (D A : DOp ι) : comp D (-A) = -comp D A := by
  have h := comp_add D A (-A)
  rw [add_neg_cancel, comp_zero'] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

private theorem comp_sub' (D A B : DOp ι) : comp D (A - B) = comp D A - comp D B := by
  rw [sub_eq_add_neg, comp_add, comp_neg', sub_eq_add_neg]

private theorem nb_split₂ (hΩ : IsCasimirPair Ω₂ Ω₃) (ha₂ : a₂ (Fin.last N₂) = 1) (j : Fin 6) (e₀ f : ℕ) :
    nb Ω₂ Ω₃ j (e₀ + N₂) f
      = comp (nb Ω₂ Ω₃ j e₀ f) (polyOp a₂ Ω₂) + ∑ m : Fin N₂, (-(a₂ m.castSucc)) • nb Ω₂ Ω₃ j (e₀ + m) f := by
  rw [← nb_comp_npow₂ hΩ j e₀ f N₂, npow_eq_polyOp_sub a₂ ha₂, comp_sub', comp_finset_sum]
  simp only [comp_smul, nb_comp_npow₂ hΩ, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

private theorem nb_split₃ (ha₃ : a₃ (Fin.last N₃) = 1) (j : Fin 6) (e f₀ : ℕ) :
    nb Ω₂ Ω₃ j e (f₀ + N₃)
      = comp (nb Ω₂ Ω₃ j e f₀) (polyOp a₃ Ω₃) + ∑ m : Fin N₃, (-(a₃ m.castSucc)) • nb Ω₂ Ω₃ j e (f₀ + m) := by
  rw [← nb_comp_npow₃ j e f₀ N₃, npow_eq_polyOp_sub a₃ ha₃, comp_sub', comp_finset_sum]
  simp only [comp_smul, nb_comp_npow₃, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

private theorem redT_nb (hΩ : IsCasimirPair Ω₂ Ω₃) (ha₂ : a₂ (Fin.last N₂) = 1) (ha₃ : a₃ (Fin.last N₃) = 1)
    (j : Fin 6) :
    ∀ (n : ℕ) (e f : ℕ), e + f = n → ∃ T, RedT Ω₂ Ω₃ a₂ a₃ (nb Ω₂ Ω₃ j e f) T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro e f hef
    by_cases he : e < N₂
    · by_cases hf : f < N₃
      · exact ⟨_, redT_nb_reduced j ⟨e, he⟩ ⟨f, hf⟩⟩
      · obtain ⟨f₀, rfl⟩ : ∃ f₀, f = f₀ + N₃ := ⟨f - N₃, by omega⟩
        have hrec : ∀ m : Fin N₃, ∃ T, RedT Ω₂ Ω₃ a₂ a₃ (nb Ω₂ Ω₃ j e (f₀ + m)) T :=
          fun m => ih (e + (f₀ + m)) (by have := m.isLt; omega) e (f₀ + m) rfl
        choose Tm hTm using hrec
        rw [nb_split₃ ha₃]
        exact ⟨_, redT_add (redT_ideal₃ a₂ a₃ _) (redT_sum Finset.univ fun m _ => redT_smul (hTm m) _)⟩
    · obtain ⟨e₀, rfl⟩ : ∃ e₀, e = e₀ + N₂ := ⟨e - N₂, by omega⟩
      have hrec : ∀ m : Fin N₂, ∃ T, RedT Ω₂ Ω₃ a₂ a₃ (nb Ω₂ Ω₃ j (e₀ + m) f) T :=
        fun m => ih (e₀ + m + f) (by have := m.isLt; omega) (e₀ + m) f rfl
      choose Tm hTm using hrec
      rw [nb_split₂ hΩ ha₂]
      exact ⟨_, redT_add (redT_ideal₂ a₂ a₃ _) (redT_sum Finset.univ fun m _ => redT_smul (hTm m) _)⟩

private theorem exists_redT (hΩ : IsCasimirPair Ω₂ Ω₃) (ha₂ : a₂ (Fin.last N₂) = 1) (ha₃ : a₃ (Fin.last N₃) = 1)
    (D : DOp ι) : ∃ T, RedT Ω₂ Ω₃ a₂ a₃ D T := by
  obtain ⟨K, S, -, rfl⟩ := exists_tsum hΩ D
  have hb : ∀ (j : Fin 6) (e f : ℕ), ∃ T, RedT Ω₂ Ω₃ a₂ a₃ (nb Ω₂ Ω₃ j e f) T :=
    fun j e f => redT_nb hΩ ha₂ ha₃ j (e + f) e f rfl
  choose Tb hTb using hb
  unfold tsum
  exact ⟨_, redT_sum Finset.univ fun j _ =>
    redT_sum _ fun e _ => redT_sum _ fun f _ => redT_cmul (hTb j e f) (S j e f)⟩

private theorem redT_unique (hΩ : IsCasimirPair Ω₂ Ω₃) (ha₂ : a₂ (Fin.last N₂) = 1) (ha₃ : a₃ (Fin.last N₃) = 1)
    {D : DOp ι} {T T' : Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef} (h : RedT Ω₂ Ω₃ a₂ a₃ D T)
    (h' : RedT Ω₂ Ω₃ a₂ a₃ D T') : T = T' := by
  obtain ⟨Y₁, Y₁', h₁⟩ := h
  obtain ⟨Y₂, Y₂', h₂⟩ := h'
  have h₃ := h₁.symm.trans h₂
  have h₄ : rsum Ω₂ Ω₃ T = rsum Ω₂ Ω₃ T' + comp Y₂ (polyOp a₂ Ω₂) + comp Y₂' (polyOp a₃ Ω₃) - comp Y₁' (polyOp a₃ Ω₃)
      - comp Y₁ (polyOp a₂ Ω₂) := eq_sub_of_add_eq (eq_sub_of_add_eq h₃)
  have h₅ : rsum Ω₂ Ω₃ (fun j e f => T j e f - T' j e f)
      = comp (Y₂ - Y₁) (polyOp a₂ Ω₂) + comp (Y₂' - Y₁') (polyOp a₃ Ω₃) := by
    rw [rsum_sub, sub_comp', sub_comp', h₄]
    abel
  have h₆ := normalForm_unique_mod hΩ a₂ ha₂ a₃ ha₃ (fun j e f => T j e f - T' j e f) (Y₂ - Y₁) (Y₂' - Y₁') h₅
  funext j e f
  exact sub_eq_zero.mp (h₆ j e f)

private theorem redT_deriv_comp (Dd : DOp ι) (φ : Coef → Coef)
    (hL : ∀ (C : Matrix ι ι Coef) (D : DOp ι), comp Dd (cmul C D) = cmul (C.map φ) D + cmul C (comp Dd D))
    {D : DOp ι} {T : Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef} (hD : RedT Ω₂ Ω₃ a₂ a₃ D T)
    {T' : Fin 6 → Fin N₂ → Fin N₃ → Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef}
    (hT' : ∀ (j : Fin 6) (e : Fin N₂) (f : Fin N₃), RedT Ω₂ Ω₃ a₂ a₃ (comp Dd (nb Ω₂ Ω₃ j e f)) (T' j e f)) :
    RedT Ω₂ Ω₃ a₂ a₃ (comp Dd D) (fun j e f =>
      (T j e f).map φ + ∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃, T j' e' f' * T' j' e' f' j e f) := by
  obtain ⟨Y, Y', rfl⟩ := hD
  have hmain : RedT Ω₂ Ω₃ a₂ a₃ (comp Dd (rsum Ω₂ Ω₃ T)) (fun j e f =>
      (T j e f).map φ + ∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃, T j' e' f' * T' j' e' f' j e f) := by
    have hsplit : comp Dd (rsum Ω₂ Ω₃ T)
        = rsum Ω₂ Ω₃ (fun j e f => (T j e f).map φ)
          + ∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃, cmul (T j' e' f') (comp Dd (nb Ω₂ Ω₃ j' e' f')) := by
      simp only [rsum, comp_finset_sum, hL, Finset.sum_add_distrib]
    rw [hsplit]
    exact redT_add (redT_rsum a₂ a₃ _)
      (redT_sum Finset.univ fun j' _ => redT_sum _ fun e' _ => redT_sum _ fun f' _ => redT_cmul (hT' j' e' f') _)
  rw [comp_add, comp_add, ← comp_assoc, ← comp_assoc]
  refine redT_congr (redT_add (redT_add hmain (redT_ideal₂ a₂ a₃ (comp Dd Y))) (redT_ideal₃ a₂ a₃ (comp Dd Y')))
    fun j e f => ?_
  simp only [add_zero]

end ReductionTheorems
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

section ConnectionAnalytic

variable {Ω₂ Ω₃ : DOp ι} {N₂ N₃ : ℕ} {a₂ : Fin (N₂ + 1) → ℂ} {a₃ : Fin (N₃ + 1) → ℂ}

private noncomputable def ofT (Tt : Fin 6 → Fin N₂ → Fin N₃ → Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef) :
    Matrix (RIdx N₂ N₃ ι) (RIdx N₂ N₃ ι) Coef :=
  Matrix.of fun p q => Tt p.1 p.2.1 p.2.2.1 q.1 q.2.1 q.2.2.1 p.2.2.2 q.2.2.2

private theorem smooth2_zero : Smooth2 (fun (_ : ℝ) (_ : ℝ) => (0 : ι → ℂ)) := contDiff_const

private theorem apply_zero_fun (D : DOp ι) : DOp.apply D (fun _ _ => (0 : ι → ℂ)) = fun _ _ => 0 := by
  have h := apply_smul_fun D 0 (smooth2_zero (ι := ι))
  simpa only [zero_smul] using h

private theorem apply_of_redT {E : DOp ι} {T : Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef} (hE : RedT Ω₂ Ω₃ a₂ a₃ E T)
    {Φ₀ : ℝ → ℝ → (ι → ℂ)} (hΦ : Smooth2 Φ₀) (h₂ : DOp.apply (polyOp a₂ Ω₂) Φ₀ = fun _ _ => 0)
    (h₃ : DOp.apply (polyOp a₃ Ω₃) Φ₀ = fun _ _ => 0) :
    DOp.apply E Φ₀ = fun t₁ t₂ => ∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃,
      mev (T j' e' f') t₁ t₂ *ᵥ DOp.apply (nb Ω₂ Ω₃ j' e' f') Φ₀ t₁ t₂ := by
  obtain ⟨Y, Y', rfl⟩ := hE
  rw [apply_add, apply_add, apply_comp _ _ hΦ, apply_comp _ _ hΦ, h₂, h₃, apply_zero_fun, apply_zero_fun]
  funext t₁ t₂
  simp only [add_zero]
  simp only [rsum, apply_finset_sum, apply_cmul]

private theorem mulVec_frame_entry (Tt : Fin 6 → Fin N₂ → Fin N₃ → Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef)
    (Φ₀ : ℝ → ℝ → (ι → ℂ)) (t₁ t₂ : ℝ) (J : RIdx N₂ N₃ ι) :
    (mev (ofT Tt) t₁ t₂
        *ᵥ frame Ω₂ Ω₃ N₂ N₃ Φ₀ t₁ t₂) J
      = (∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃,
          mev (Tt J.1 J.2.1 J.2.2.1 j' e' f') t₁ t₂ *ᵥ DOp.apply (nb Ω₂ Ω₃ j' e' f') Φ₀ t₁ t₂) J.2.2.2 := by
  simp only [ofT, Matrix.mulVec, dotProduct, Finset.sum_apply, mev_apply, Matrix.of_apply, frame,
    Fintype.sum_prod_type]

private theorem frame_system₁ (Tt : Fin 6 → Fin N₂ → Fin N₃ → Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef)
    (hT : ∀ (j : Fin 6) (e : Fin N₂) (f : Fin N₃), RedT Ω₂ Ω₃ a₂ a₃ (comp d₁ (nb Ω₂ Ω₃ j e f)) (Tt j e f))
    {Φ₀ : ℝ → ℝ → (ι → ℂ)} (hΦ : Smooth2 Φ₀) (h₂ : DOp.apply (polyOp a₂ Ω₂) Φ₀ = fun _ _ => 0)
    (h₃ : DOp.apply (polyOp a₃ Ω₃) Φ₀ = fun _ _ => 0) :
    d1 (frame Ω₂ Ω₃ N₂ N₃ Φ₀) = fun t₁ t₂ =>
      mev (ofT Tt) t₁ t₂
        *ᵥ frame Ω₂ Ω₃ N₂ N₃ Φ₀ t₁ t₂ := by
  funext t₁ t₂
  show deriv (fun s => frame Ω₂ Ω₃ N₂ N₃ Φ₀ s t₂) t₁ = _
  refine HasDerivAt.deriv (hasDerivAt_pi.mpr fun J => ?_)
  have hsm := Smooth2.apply (nb Ω₂ Ω₃ J.1 J.2.1 J.2.2.1) hΦ
  have hd := hasDerivAt_pi.mp (hsm.hasDerivAt_d1 t₁ t₂) J.2.2.2
  refine hd.congr_deriv ?_
  rw [mulVec_frame_entry, ← apply_d₁, ← apply_comp _ _ hΦ, apply_of_redT (hT J.1 J.2.1 J.2.2.1) hΦ h₂ h₃]

private theorem frame_system₂ (Tt : Fin 6 → Fin N₂ → Fin N₃ → Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef)
    (hT : ∀ (j : Fin 6) (e : Fin N₂) (f : Fin N₃), RedT Ω₂ Ω₃ a₂ a₃ (comp d₂ (nb Ω₂ Ω₃ j e f)) (Tt j e f))
    {Φ₀ : ℝ → ℝ → (ι → ℂ)} (hΦ : Smooth2 Φ₀) (h₂ : DOp.apply (polyOp a₂ Ω₂) Φ₀ = fun _ _ => 0)
    (h₃ : DOp.apply (polyOp a₃ Ω₃) Φ₀ = fun _ _ => 0) :
    d2 (frame Ω₂ Ω₃ N₂ N₃ Φ₀) = fun t₁ t₂ =>
      mev (ofT Tt) t₁ t₂
        *ᵥ frame Ω₂ Ω₃ N₂ N₃ Φ₀ t₁ t₂ := by
  funext t₁ t₂
  show deriv (fun s => frame Ω₂ Ω₃ N₂ N₃ Φ₀ t₁ s) t₂ = _
  refine HasDerivAt.deriv (hasDerivAt_pi.mpr fun J => ?_)
  have hsm := Smooth2.apply (nb Ω₂ Ω₃ J.1 J.2.1 J.2.2.1) hΦ
  have hd := hasDerivAt_pi.mp (hsm.hasDerivAt_d2 t₁ t₂) J.2.2.2
  refine hd.congr_deriv ?_
  rw [mulVec_frame_entry, ← apply_d₂, ← apply_comp _ _ hΦ, apply_of_redT (hT J.1 J.2.1 J.2.2.1) hΦ h₂ h₃]

private theorem entry_map_add_mul (Ta Tb : Fin 6 → Fin N₂ → Fin N₃ → Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef)
    (φ : Coef → Coef) (p q : RIdx N₂ N₃ ι) :
    ((ofT Ta).map φ + ofT Ta * ofT Tb) p q
      = ((Ta p.1 p.2.1 p.2.2.1 q.1 q.2.1 q.2.2.1).map φ
          + ∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃,
              Ta p.1 p.2.1 p.2.2.1 j' e' f' * Tb j' e' f' q.1 q.2.1 q.2.2.1) p.2.2.2 q.2.2.2 := by
  simp only [ofT, Matrix.add_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.sum_apply,
    Fintype.sum_prod_type]

end ConnectionAnalytic
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

private theorem exists_connection {Ω₂ Ω₃ : DOp ι} (hΩ : IsCasimirPair Ω₂ Ω₃) {N₂ N₃ : ℕ}
    (a₂ : Fin (N₂ + 1) → ℂ) (ha₂ : a₂ (Fin.last N₂) = 1) (a₃ : Fin (N₃ + 1) → ℂ) (ha₃ : a₃ (Fin.last N₃) = 1) :
    ∃ 𝔐 𝔐' : Matrix (RIdx N₂ N₃ ι) (RIdx N₂ N₃ ι) Coef,
      (∀ (j : Fin 6) (e : Fin N₂) (f : Fin N₃), ∃ Y Y' : DOp ι,
        comp d₁ (nb Ω₂ Ω₃ j e f)
          = (∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃,
              cmul (Matrix.of fun i i' => 𝔐 (j, e, f, i) (j', e', f', i')) (nb Ω₂ Ω₃ j' e' f'))
            + comp Y (polyOp a₂ Ω₂) + comp Y' (polyOp a₃ Ω₃)) ∧
      (∀ (j : Fin 6) (e : Fin N₂) (f : Fin N₃), ∃ Y Y' : DOp ι,
        comp d₂ (nb Ω₂ Ω₃ j e f)
          = (∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃,
              cmul (Matrix.of fun i i' => 𝔐' (j, e, f, i) (j', e', f', i')) (nb Ω₂ Ω₃ j' e' f'))
            + comp Y (polyOp a₂ Ω₂) + comp Y' (polyOp a₃ Ω₃)) ∧
      (∀ Φ₀ : ℝ → ℝ → (ι → ℂ), Smooth2 Φ₀ →
        apply (polyOp a₂ Ω₂) Φ₀ = (fun _ _ => 0) → apply (polyOp a₃ Ω₃) Φ₀ = (fun _ _ => 0) →
          d1 (frame Ω₂ Ω₃ N₂ N₃ Φ₀) = (fun t₁ t₂ => mev 𝔐 t₁ t₂ *ᵥ frame Ω₂ Ω₃ N₂ N₃ Φ₀ t₁ t₂) ∧
          d2 (frame Ω₂ Ω₃ N₂ N₃ Φ₀) = (fun t₁ t₂ => mev 𝔐' t₁ t₂ *ᵥ frame Ω₂ Ω₃ N₂ N₃ Φ₀ t₁ t₂)) ∧
      𝔐'.map (eul 0) + 𝔐' * 𝔐 = 𝔐.map (eul 1) + 𝔐 * 𝔐' ∧
      (𝔐.map killX0).map (eul 1) = 𝔐'.map killX0 * 𝔐.map killX0 - 𝔐.map killX0 * 𝔐'.map killX0 := by
  classical

  have h₁ : ∀ (j : Fin 6) (e : Fin N₂) (f : Fin N₃), ∃ T, RedT Ω₂ Ω₃ a₂ a₃ (comp d₁ (nb Ω₂ Ω₃ j e f)) T :=
    fun j e f => exists_redT hΩ ha₂ ha₃ _
  have h₂ : ∀ (j : Fin 6) (e : Fin N₂) (f : Fin N₃), ∃ T, RedT Ω₂ Ω₃ a₂ a₃ (comp d₂ (nb Ω₂ Ω₃ j e f)) T :=
    fun j e f => exists_redT hΩ ha₂ ha₃ _
  choose Ta hTa using h₁
  choose Tb hTb using h₂

  have hflat : ∀ (j : Fin 6) (e : Fin N₂) (f : Fin N₃),
      (fun j' e' f' => (Tb j e f j' e' f').map (eul 0)
          + ∑ j'' : Fin 6, ∑ e'' : Fin N₂, ∑ f'' : Fin N₃, Tb j e f j'' e'' f'' * Ta j'' e'' f'' j' e' f')
        = (fun j' e' f' => (Ta j e f j' e' f').map (eul 1)
          + ∑ j'' : Fin 6, ∑ e'' : Fin N₂, ∑ f'' : Fin N₃, Ta j e f j'' e'' f'' * Tb j'' e'' f'' j' e' f') := by
    intro j e f
    have hA := redT_deriv_comp d₁ (eul 0) d₁_comp_cmul (hTb j e f) hTa
    have hB := redT_deriv_comp d₂ (eul 1) d₂_comp_cmul (hTa j e f) hTb
    rw [← comp_assoc, ← d₁_comp_d₂, comp_assoc] at hB
    exact redT_unique hΩ ha₂ ha₃ hA hB
  have h4 : (ofT Tb).map (eul 0) + ofT Tb * ofT Ta = (ofT Ta).map (eul 1) + ofT Ta * ofT Tb := by
    refine Matrix.ext fun p q => ?_
    rw [entry_map_add_mul Tb Ta (eul 0) p q, entry_map_add_mul Ta Tb (eul 1) p q]
    exact congrFun (congrFun (congrFun (congrFun (congrFun (hflat p.1 p.2.1 p.2.2.1) q.1) q.2.1) q.2.2.1) p.2.2.2)
      q.2.2.2
  refine ⟨ofT Ta, ofT Tb, ?_, ?_, ?_, h4, ?_⟩
  · intro j e f
    obtain ⟨Y, Y', hY⟩ := hTa j e f
    exact ⟨Y, Y', hY⟩
  · intro j e f
    obtain ⟨Y, Y', hY⟩ := hTb j e f
    exact ⟨Y, Y', hY⟩
  · intro Φ₀ hΦ hp₂ hp₃
    exact ⟨frame_system₁ Ta hTa hΦ hp₂ hp₃, frame_system₂ Tb hTb hΦ hp₂ hp₃⟩
  ·
    refine Matrix.ext fun p q => ?_
    have h := congrFun (congrFun h4 p) q
    simp only [Matrix.add_apply, Matrix.map_apply, Matrix.mul_apply] at h
    have hk := congrArg killX0 h
    simp only [map_add, map_sum, map_mul, killX0_eul0, killX0_eul1, zero_add] at hk
    simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.mul_apply]
    rw [hk]
    ring

section Lax

private theorem eul_sum' (i : Fin 2) {κ : Type} (s : Finset κ) (g : κ → Coef) :
    eul i (∑ x ∈ s, g x) = ∑ x ∈ s, eul i (g x) := by
  simp only [eul, map_sum, Finset.mul_sum]

private theorem eul_sub' (i : Fin 2) (p q : Coef) : eul i (p - q) = eul i p - eul i q := by
  simp only [eul, map_sub, mul_sub]

private theorem eul_one' (i : Fin 2) : eul i (1 : Coef) = 0 := by
  rw [← MvPolynomial.C_1, eul_C]

private theorem eul_intCast' (i : Fin 2) (z : ℤ) : eul i (z : Coef) = 0 := by
  rw [← map_intCast (MvPolynomial.C : ℂ →+* Coef) z, eul_C]

private noncomputable def lxD (i : Fin 2) (f : Polynomial Coef) : Polynomial Coef :=
  f.sum fun k a => Polynomial.monomial k (eul i a)

private theorem lxD_coeff (i : Fin 2) (f : Polynomial Coef) (k : ℕ) : (lxD i f).coeff k = eul i (f.coeff k) := by
  unfold lxD
  rw [Polynomial.sum_def, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Polynomial.notMem_support_iff.mp h, eul_zero]

private theorem lxD_add (i : Fin 2) (f g : Polynomial Coef) : lxD i (f + g) = lxD i f + lxD i g := by
  refine Polynomial.ext fun k => ?_; simp only [lxD_coeff, Polynomial.coeff_add, eul_add]

private theorem lxD_sub (i : Fin 2) (f g : Polynomial Coef) : lxD i (f - g) = lxD i f - lxD i g := by
  refine Polynomial.ext fun k => ?_; simp only [lxD_coeff, Polynomial.coeff_sub, eul_sub']

private theorem lxD_zero (i : Fin 2) : lxD i (0 : Polynomial Coef) = 0 := by
  refine Polynomial.ext fun k => ?_; simp only [lxD_coeff, Polynomial.coeff_zero, eul_zero]

private theorem lxD_sum (i : Fin 2) {κ : Type} (s : Finset κ) (g : κ → Polynomial Coef) :
    lxD i (∑ x ∈ s, g x) = ∑ x ∈ s, lxD i (g x) := by
  refine Polynomial.ext fun k => ?_; simp only [lxD_coeff, Polynomial.finset_sum_coeff, eul_sum']

private theorem lxD_C (i : Fin 2) (a : Coef) : lxD i (Polynomial.C a) = Polynomial.C (eul i a) := by
  refine Polynomial.ext fun k => ?_
  simp only [lxD_coeff, Polynomial.coeff_C]
  split_ifs
  · rfl
  · exact eul_zero i

private theorem lxD_X (i : Fin 2) : lxD i (Polynomial.X : Polynomial Coef) = 0 := by
  refine Polynomial.ext fun k => ?_
  simp only [lxD_coeff, Polynomial.coeff_X, Polynomial.coeff_zero]
  split_ifs
  · exact eul_one' i
  · exact eul_zero i

private theorem lxD_mul (i : Fin 2) (f g : Polynomial Coef) : lxD i (f * g) = lxD i f * g + f * lxD i g := by
  refine Polynomial.ext fun k => ?_
  simp only [lxD_coeff, Polynomial.coeff_add, Polynomial.coeff_mul, eul_sum', eul_mul, Finset.sum_add_distrib]

private theorem lxD_intCast_mul (i : Fin 2) (z : ℤ) (f : Polynomial Coef) :
    lxD i ((z : Polynomial Coef) * f) = (z : Polynomial Coef) * lxD i f := by
  rw [lxD_mul, ← Polynomial.C_eq_intCast, lxD_C, eul_intCast', Polynomial.C_0, zero_mul, zero_add]

private theorem lxD_prod (i : Fin 2) {κ : Type} [DecidableEq κ] (s : Finset κ) (g : κ → Polynomial Coef) :
    lxD i (∏ x ∈ s, g x) = ∑ x ∈ s, lxD i (g x) * ∏ y ∈ s.erase x, g y := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty]; rw [← Polynomial.C_1, lxD_C, eul_one', Polynomial.C_0]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, lxD_mul, ih, Finset.sum_insert ha, Finset.erase_insert ha, Finset.mul_sum]
    rw [add_right_inj]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hax : a ≠ x := fun h => ha (h ▸ hx)
    rw [Finset.erase_insert_of_ne hax, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
    ring

variable {n : Type} [Fintype n] [DecidableEq n]

private theorem lxD_det (i : Fin 2) (M : Matrix n n (Polynomial Coef)) :
    lxD i M.det = Matrix.trace (M.adjugate * M.map (lxD i)) := by
  have htr : Matrix.trace (M.adjugate * M.map (lxD i)) = ∑ j, (M.updateCol j fun r => lxD i (M r j)).det := by
    simp only [Matrix.trace, Matrix.diag_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.map_apply]
  rw [htr, Matrix.det_apply', lxD_sum]
  simp only [Matrix.det_apply', lxD_intCast_mul, lxD_prod]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  symm
  rw [← Finset.mul_prod_erase Finset.univ (fun k => (M.updateCol j fun r => lxD i (M r j)) (σ k) k)
    (Finset.mem_univ j)]
  simp only [Matrix.updateCol_self]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [Matrix.updateCol_ne (Finset.ne_of_mem_erase hk)]

private theorem lxD_charmatrix (i : Fin 2) (A P : Matrix n n Coef) (hlax : A.map (eul i) = A * P - P * A) :
    (Matrix.charmatrix A).map (lxD i)
      = Matrix.charmatrix A * P.map Polynomial.C - P.map Polynomial.C * Matrix.charmatrix A := by
  have hentry : ∀ a b, eul i (A a b) = (A * P - P * A) a b := fun a b => by
    rw [← hlax, Matrix.map_apply]
  ext a b : 2
  simp only [Matrix.map_apply, Matrix.charmatrix_apply, Matrix.sub_apply, Matrix.mul_apply, lxD_sub, lxD_C, hentry,
    Matrix.diagonal, Matrix.of_apply]
  split_ifs with hab
  · subst hab
    simp only [lxD_X, Matrix.map_apply, Finset.sum_sub_distrib, sub_mul, mul_sub, map_sub, map_sum, map_mul]
    simp only [Matrix.diagonal, Matrix.of_apply, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_sub_distrib]
    ring
  · simp only [lxD_zero, Matrix.map_apply, Finset.sum_sub_distrib, sub_mul, mul_sub, map_sub, map_sum, map_mul]
    simp only [Matrix.diagonal, Matrix.of_apply, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_sub_distrib, hab, if_false]
    ring

private theorem eul_charpoly_coeff (i : Fin 2) (A P : Matrix n n Coef) (hlax : A.map (eul i) = A * P - P * A) (m : ℕ) :
    eul i (A.charpoly.coeff m) = 0 := by
  rw [← lxD_coeff, Matrix.charpoly, lxD_det, lxD_charmatrix i A P hlax, mul_sub, ← mul_assoc, Matrix.adjugate_mul,
    Matrix.trace_sub, ← mul_assoc,
    Matrix.trace_mul_comm (A.charmatrix.adjugate * P.map Polynomial.C) A.charmatrix, ← mul_assoc,
    Matrix.mul_adjugate, sub_self, Polynomial.coeff_zero]

private theorem coeff_eul (i : Fin 2) (p : Coef) (s : Fin 2 →₀ ℕ) :
    MvPolynomial.coeff s (eul i p) = s i • MvPolynomial.coeff s p := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    simp only [eul, MvPolynomial.X_mul_pderiv_monomial, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]
    split_ifs with h
    · subst h; rfl
    · simp only [smul_zero]
  | add p q hp hq =>
    rw [eul_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, smul_add]

private theorem eq_C_constantCoeff_of_eul (c : Coef) (h0 : eul 0 c = 0) (h1 : eul 1 c = 0) :
    c = C (constantCoeff c) := by
  refine MvPolynomial.ext _ _ fun s => ?_
  rw [MvPolynomial.coeff_C]
  split_ifs with hs
  · subst hs; rfl
  · have hs' : s ≠ 0 := fun h => hs (by simp [h])
    obtain ⟨idx, hidx⟩ := Finsupp.ne_iff.mp hs'
    rw [Finsupp.coe_zero, Pi.zero_apply] at hidx
    have key : ∀ i : Fin 2, eul i c = 0 → s i ≠ 0 → MvPolynomial.coeff s c = 0 := by
      intro i hi hsi
      have := coeff_eul i c s
      rw [hi, MvPolynomial.coeff_zero, nsmul_eq_mul] at this
      rcases mul_eq_zero.mp this.symm with h | h
      · exact absurd (Nat.cast_eq_zero.mp h) hsi
      · exact h
    fin_cases idx
    · exact (key 0 h0 hidx).symm ▸ rfl
    · exact (key 1 h1 hidx).symm ▸ rfl

end Lax
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

private theorem charpoly_const_of_lax {n : Type} [Fintype n] [DecidableEq n] (A P : Matrix n n Coef)
    (hA : A.map killX0 = A) (hlax : A.map (eul 1) = A * P - P * A) (m : ℕ) :
    (A.charpoly.coeff m) = C (constantCoeff (A.charpoly.coeff m)) := by
  have h1 : eul 1 (A.charpoly.coeff m) = 0 := eul_charpoly_coeff 1 A P hlax m
  have hmap0 : A.map (eul 0) = A * 0 - 0 * A := by
    rw [mul_zero, zero_mul, sub_zero]
    ext a b : 2
    rw [Matrix.map_apply, Matrix.zero_apply]
    have : A a b = killX0 (A a b) := by
      conv_lhs => rw [← hA]
      rfl
    rw [this, eul0_killX0]
  have h0 : eul 0 (A.charpoly.coeff m) = 0 := eul_charpoly_coeff 0 A 0 hmap0 m
  exact eq_C_constantCoeff_of_eul _ h0 h1

section DegreeBounds

private def MDeg (d : ℕ) (M : Matrix ι ι Coef) : Prop := ∀ i i', (M i i').totalDegree ≤ d

private def DDeg (c : ℕ) (D : DOp ι) : Prop := ∀ ab, MDeg c (D ab)

omit [Fintype ι] [DecidableEq ι] in
private theorem mdeg_zero (d : ℕ) : MDeg d (0 : Matrix ι ι Coef) := fun _ _ => by
  simp only [Matrix.zero_apply, MvPolynomial.totalDegree_zero, zero_le]

omit [Fintype ι] in
private theorem mdeg_one (d : ℕ) : MDeg d (1 : Matrix ι ι Coef) := by
  intro i i'
  rw [Matrix.one_apply]
  split_ifs <;> simp only [MvPolynomial.totalDegree_one, MvPolynomial.totalDegree_zero, zero_le]

omit [Fintype ι] in
private theorem mdeg_scal (d : ℕ) (z : ℂ) : MDeg d (scal (ι := ι) z) := by
  intro i i'
  simp only [scal, Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> simp only [smul_eq_mul, mul_one, mul_zero, MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_zero,
    zero_le]

omit [Fintype ι] [DecidableEq ι] in
private theorem MDeg.mono {d d' : ℕ} {M : Matrix ι ι Coef} (h : MDeg d M) (hd : d ≤ d') : MDeg d' M :=
  fun i i' => (h i i').trans hd

omit [Fintype ι] [DecidableEq ι] in
private theorem MDeg.add {d : ℕ} {M M' : Matrix ι ι Coef} (h : MDeg d M) (h' : MDeg d M') : MDeg d (M + M') :=
  fun i i' => by
    rw [Matrix.add_apply]
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le (h i i') (h' i i'))

omit [Fintype ι] [DecidableEq ι] in
private theorem MDeg.sub {d : ℕ} {M M' : Matrix ι ι Coef} (h : MDeg d M) (h' : MDeg d M') : MDeg d (M - M') :=
  fun i i' => by
    rw [Matrix.sub_apply]
    exact (MvPolynomial.totalDegree_sub _ _).trans (max_le (h i i') (h' i i'))

private theorem totalDegree_sum_le {d : ℕ} {κ : Type} (s : Finset κ) {g : κ → Coef}
    (hg : ∀ c ∈ s, (g c).totalDegree ≤ d) : (∑ c ∈ s, g c).totalDegree ≤ d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, MvPolynomial.totalDegree_zero, zero_le]
  | insert c s hc ih =>
    rw [Finset.sum_insert hc]
    exact (MvPolynomial.totalDegree_add _ _).trans
      (max_le (hg c (Finset.mem_insert_self c s)) (ih fun c' hc' => hg c' (Finset.mem_insert_of_mem hc')))

omit [Fintype ι] [DecidableEq ι] in
private theorem MDeg.sum {d : ℕ} {κ : Type} (s : Finset κ) {g : κ → Matrix ι ι Coef} (hg : ∀ c ∈ s, MDeg d (g c)) :
    MDeg d (∑ c ∈ s, g c) := fun i i' => by
  rw [Matrix.sum_apply]
  exact totalDegree_sum_le s fun c hc => hg c hc i i'

omit [DecidableEq ι] in
private theorem MDeg.mul {d d' : ℕ} {M M' : Matrix ι ι Coef} (h : MDeg d M) (h' : MDeg d' M') :
    MDeg (d + d') (M * M') := fun i i' => by
  rw [Matrix.mul_apply]
  exact totalDegree_sum_le _ fun l _ => (MvPolynomial.totalDegree_mul _ _).trans (add_le_add (h i l) (h' l i'))

omit [Fintype ι] [DecidableEq ι] in
private theorem MDeg.smul {d : ℕ} (z : ℂ) {M : Matrix ι ι Coef} (h : MDeg d M) : MDeg d (z • M) := fun i i' => by
  rw [Matrix.smul_apply]
  exact (MvPolynomial.totalDegree_smul_le _ _).trans (h i i')

private theorem totalDegree_eul_le (i : Fin 2) (p : Coef) : (eul i p).totalDegree ≤ p.totalDegree := by
  refine MvPolynomial.totalDegree_le_of_support_subset fun s hs => ?_
  rw [MvPolynomial.mem_support_iff] at hs ⊢
  intro h0
  exact hs (by rw [coeff_eul, h0, smul_zero])

private theorem totalDegree_eul_iterate_le (i : Fin 2) (n : ℕ) (p : Coef) :
    ((eul i)^[n] p).totalDegree ≤ p.totalDegree := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact (ih _).trans (totalDegree_eul_le i p)

omit [Fintype ι] [DecidableEq ι] in
private theorem MDeg.map_eul {d : ℕ} {M : Matrix ι ι Coef} (h : MDeg d M) (a b : ℕ) :
    MDeg d (M.map ((eul 0)^[a] ∘ (eul 1)^[b])) := fun i i' => by
  rw [Matrix.map_apply, Function.comp_apply]
  exact (totalDegree_eul_iterate_le 0 a _).trans ((totalDegree_eul_iterate_le 1 b _).trans (h i i'))

private theorem DDeg.mono {c c' : ℕ} {D : DOp ι} (h : DDeg c D) (hc : c ≤ c') : DDeg c' D :=
  fun ab => (h ab).mono hc

private theorem ddeg_zero (c : ℕ) : DDeg c (0 : DOp ι) := fun _ => by
  rw [Finsupp.zero_apply]; exact mdeg_zero c

private theorem DDeg.add {c : ℕ} {D D' : DOp ι} (h : DDeg c D) (h' : DDeg c D') : DDeg c (D + D') := fun ab => by
  rw [Finsupp.add_apply]; exact (h ab).add (h' ab)

private theorem DDeg.sub {c : ℕ} {D D' : DOp ι} (h : DDeg c D) (h' : DDeg c D') : DDeg c (D - D') := fun ab => by
  rw [Finsupp.sub_apply]; exact (h ab).sub (h' ab)

private theorem DDeg.sum {c : ℕ} {κ : Type} (s : Finset κ) {g : κ → DOp ι} (hg : ∀ x ∈ s, DDeg c (g x)) :
    DDeg c (∑ x ∈ s, g x) := fun ab => by
  rw [Finsupp.finset_sum_apply]; exact MDeg.sum s fun x hx => hg x hx ab

private theorem ddeg_single (c : ℕ) (ab : ℕ × ℕ) {M : Matrix ι ι Coef} (h : MDeg c M) :
    DDeg c (Finsupp.single ab M) := by
  intro cd
  rw [Finsupp.single_apply]
  split_ifs
  · exact h
  · exact mdeg_zero c

private theorem ddeg_mono (c a b : ℕ) : DDeg c (mono a b : DOp ι) := ddeg_single c _ (mdeg_one c)

private theorem ddeg_one (c : ℕ) : DDeg c (one : DOp ι) := ddeg_single c _ (mdeg_one c)

private theorem ddeg_B (c : ℕ) (j : Fin 6) : DDeg c (B j : DOp ι) := ddeg_mono c _ _

private theorem ddeg_cmul {d c : ℕ} {M : Matrix ι ι Coef} (hM : MDeg d M) {D : DOp ι} (hD : DDeg c D) :
    DDeg (d + c) (cmul M D) := fun ab => by
  rw [cmul_apply]; exact hM.mul (hD ab)

private theorem DDeg.finsupp_sum {c : ℕ} (D : DOp ι) (g : ℕ × ℕ → Matrix ι ι Coef → DOp ι)
    (hg : ∀ ab, DDeg c (g ab (D ab))) : DDeg c (D.sum g) :=
  DDeg.sum _ fun ab _ => hg ab

private theorem ddeg_comp {c c' : ℕ} {D D' : DOp ι} (hD : DDeg c D) (hD' : DDeg c' D') :
    DDeg (c + c') (comp D D') := by
  unfold comp
  refine DDeg.finsupp_sum D _ fun ab => DDeg.finsupp_sum D' _ fun cd => DDeg.sum _ fun i _ => DDeg.sum _ fun j _ => ?_
  exact ddeg_single _ _ (MDeg.smul _ ((hD ab).mul ((hD' cd).map_eul i j)))

private theorem ddeg_npow {cΩ : ℕ} {Ω : DOp ι} (hΩ : DDeg cΩ Ω) (e : ℕ) : DDeg (e * cΩ) (npow Ω e) := by
  induction e with
  | zero => exact (ddeg_one 0).mono (by simp)
  | succ e ih =>
    rw [npow_succ']
    exact (ddeg_comp hΩ ih).mono (by rw [Nat.succ_mul, add_comm])

private theorem ddeg_nb {cΩ : ℕ} {Ω₂ Ω₃ : DOp ι} (h₂ : DDeg cΩ Ω₂) (h₃ : DDeg cΩ Ω₃) (j : Fin 6) (e f : ℕ) :
    DDeg ((e + f) * cΩ) (nb Ω₂ Ω₃ j e f) := by
  unfold nb
  exact (ddeg_comp (ddeg_B 0 j) (ddeg_comp (ddeg_npow h₂ e) (ddeg_npow h₃ f))).mono (by rw [add_mul]; omega)

private theorem ddeg_nfSum {cΩ : ℕ} {Ω₂ Ω₃ : DOp ι} (h₂ : DDeg cΩ Ω₂) (h₃ : DDeg cΩ Ω₃) (k β : ℕ)
    {ν : Fin 6 → ℕ → ℕ → Matrix ι ι Coef} (hν : ∀ j e f, MDeg β (ν j e f)) :
    DDeg (β + 2 * k * cΩ) (nfSum Ω₂ Ω₃ k ν) := by
  unfold nfSum
  refine DDeg.sum _ fun j _ => DDeg.sum _ fun e he => DDeg.sum _ fun f hf => ?_
  have he' := Finset.mem_range_succ_iff.mp he
  have hf' := Finset.mem_range_succ_iff.mp hf
  refine (ddeg_cmul (hν j e f) (ddeg_nb h₂ h₃ j e f)).mono (Nat.add_le_add_left ?_ β)
  calc (e + f) * cΩ ≤ (k + k) * cΩ := Nat.mul_le_mul_right cΩ (by omega)
    _ = 2 * k * cΩ := by ring

private def NFd (Ω₂ Ω₃ : DOp ι) (k β : ℕ) (D : DOp ι) : Prop :=
  ∃ ν : Fin 6 → ℕ → ℕ → Matrix ι ι Coef,
    (∀ j e f, ν j e f ≠ 0 → basisDeg j + 2 * e + 3 * f ≤ k) ∧ (∀ j e f, MDeg β (ν j e f)) ∧ D = nfSum Ω₂ Ω₃ k ν

private theorem NFd.zero (Ω₂ Ω₃ : DOp ι) (k β : ℕ) : NFd Ω₂ Ω₃ k β 0 :=
  ⟨fun _ _ _ => 0, fun _ _ _ h => (h rfl).elim, fun _ _ _ => mdeg_zero β, by simp [nfSum, cmul_zero_left]⟩

private theorem NFd.add {Ω₂ Ω₃ : DOp ι} {k β : ℕ} {D D' : DOp ι} (h : NFd Ω₂ Ω₃ k β D) (h' : NFd Ω₂ Ω₃ k β D') :
    NFd Ω₂ Ω₃ k β (D + D') := by
  obtain ⟨ν, hν, hνd, rfl⟩ := h
  obtain ⟨ν', hν', hνd', rfl⟩ := h'
  refine ⟨fun j e f => ν j e f + ν' j e f, fun j e f hne => ?_, fun j e f => (hνd j e f).add (hνd' j e f), ?_⟩
  · dsimp only at hne
    by_cases h0 : ν j e f = 0
    · rw [h0, zero_add] at hne
      exact hν' j e f hne
    · exact hν j e f h0
  · simp only [nfSum, add_cmul, Finset.sum_add_distrib]

private theorem NFd.sum {Ω₂ Ω₃ : DOp ι} {k β : ℕ} {κ : Type} (s : Finset κ) {g : κ → DOp ι}
    (hg : ∀ c ∈ s, NFd Ω₂ Ω₃ k β (g c)) : NFd Ω₂ Ω₃ k β (∑ c ∈ s, g c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using NFd.zero Ω₂ Ω₃ k β
  | insert c s hc ih =>
    rw [Finset.sum_insert hc]
    exact (hg c (Finset.mem_insert_self c s)).add (ih fun c' hc' => hg c' (Finset.mem_insert_of_mem hc'))

private theorem NFd.cmul {Ω₂ Ω₃ : DOp ι} {k β d : ℕ} {D : DOp ι} {M : Matrix ι ι Coef} (hM : MDeg d M)
    (h : NFd Ω₂ Ω₃ k β D) : NFd Ω₂ Ω₃ k (d + β) (cmul M D) := by
  obtain ⟨ν, hν, hνd, rfl⟩ := h
  refine ⟨fun j e f => M * ν j e f, fun j e f hne => hν j e f fun h0 => hne (by dsimp only; rw [h0, mul_zero]),
    fun j e f => hM.mul (hνd j e f), ?_⟩
  simp only [nfSum, cmul_finset_sum, cmul_cmul]

private theorem NFd.mono_le {Ω₂ Ω₃ : DOp ι} {k k' β β' : ℕ} {D : DOp ι} (h : NFd Ω₂ Ω₃ k β D) (hk : k ≤ k')
    (hβ : β ≤ β') : NFd Ω₂ Ω₃ k' β' D := by
  obtain ⟨ν, hν, hνd, rfl⟩ := h
  refine ⟨ν, fun j e f hne => (hν j e f hne).trans hk, fun j e f => (hνd j e f).mono hβ, ?_⟩
  have hzero : ∀ j e f, k < e ∨ k < f → ν j e f = 0 := by
    intro j e f hef
    by_contra hne
    have := hν j e f hne
    omega
  have hrange : Finset.range (k + 1) ⊆ Finset.range (k' + 1) := fun x hx =>
    Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega)
  simp only [nfSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_subset hrange]
  · refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_subset hrange]
    intro f _ hf
    rw [hzero j e f (Or.inr (by simpa [Nat.lt_succ_iff] using hf)), cmul_zero_left]
  · intro e _ he
    refine Finset.sum_eq_zero fun f _ => ?_
    rw [hzero j e f (Or.inl (by simpa [Nat.lt_succ_iff] using he)), cmul_zero_left]

private theorem exists_nfd_mono {cΩ : ℕ} {Ω₂ Ω₃ : DOp ι} (hΩ : IsCasimirPair Ω₂ Ω₃) (h₂ : DDeg cΩ Ω₂)
    (h₃ : DDeg cΩ Ω₃) (a b : ℕ) :
    ∃ N R : DOp ι, NFd Ω₂ Ω₃ (a + b) 0 N ∧ (∀ x : ℕ × ℕ, a + b ≤ x.1 + x.2 → R x = 0) ∧
      DDeg (2 * (a + b) * cΩ) R ∧ mono a b = N + R := by
  obtain ⟨c, hc, hdec⟩ := CoinvariantS3.hasDecomp_monomial a b
  set k := a + b with hk
  set N : DOp ι := nfSum Ω₂ Ω₃ k fun j e f => scal (algebraMap ℚ ℂ (c j e f)) with hN
  have hterm : ∀ j e f, HasOrder (cmul (scal (algebraMap ℚ ℂ (c j e f))) (nb Ω₂ Ω₃ j e f)) k ∧
      symb k (cmul (scal (algebraMap ℚ ℂ (c j e f))) (nb Ω₂ Ω₃ j e f))
        = Matrix.scalar ι (ψ (c j e f • CoinvariantS3.term j e f)) :=
    fun j e f => symb_term hΩ (c j e f) j e f (hc j e f)
  have hNord : HasOrder N k :=
    HasOrder.finset_sum _ fun j _ => HasOrder.finset_sum _ fun e _ => HasOrder.finset_sum _ fun f _ => (hterm j e f).1
  have hNsymb : symb k N = symb k (mono a b) := by
    rw [hN, nfSum, symb_finset_sum, symb_mono hk.symm]
    simp only [symb_finset_sum, fun j e f => (hterm j e f).2, ← map_sum]
    congr 1
    rw [← ψ_bmon_aux a b, hdec]
  have hNdeg : DDeg (2 * k * cΩ) N := by
    have := ddeg_nfSum h₂ h₃ k 0 (ν := fun j e f => scal (algebraMap ℚ ℂ (c j e f))) fun j e f => mdeg_scal 0 _
    simpa [hN] using this
  refine ⟨N, mono a b - N, ?_, ?_, (ddeg_mono _ a b).sub hNdeg, (add_sub_cancel N (mono a b)).symm⟩
  · refine ⟨_, fun j e f hne => ?_, fun j e f => mdeg_scal 0 _, rfl⟩
    exact (hc j e f fun h0 => hne (by simp [h0, scal])).le
  · intro x hx
    rw [Finsupp.sub_apply, sub_eq_zero]
    rcases hx.lt_or_eq with hlt | heq
    · rw [apply_eq_zero_of_hasOrder hNord hlt, apply_eq_zero_of_hasOrder (hasOrder_mono a b) hlt]
    · exact (apply_eq_of_symb_eq hNsymb (Finset.HasAntidiagonal.mem_antidiagonal.mpr heq.symm)).symm

private theorem nfd_of_hasOrder {cΩ : ℕ} {Ω₂ Ω₃ : DOp ι} (hΩ : IsCasimirPair Ω₂ Ω₃) (h₂ : DDeg cΩ Ω₂)
    (h₃ : DDeg cΩ Ω₃) :
    ∀ (k c : ℕ) (D : DOp ι), HasOrder D k → DDeg c D → NFd Ω₂ Ω₃ k (c + 2 * k * k * cΩ) D := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro c D hD hDc

  have hlow : ∀ (c' : ℕ) (R : DOp ι), (∀ x : ℕ × ℕ, k ≤ x.1 + x.2 → R x = 0) → DDeg c' R →
      NFd Ω₂ Ω₃ k (c' + 2 * (k - 1) * (k - 1) * cΩ) R := by
    intro c' R hR hRc
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · have : R = 0 := Finsupp.ext fun x => by rw [hR x (by omega), Finsupp.zero_apply]
      rw [this]
      exact NFd.zero Ω₂ Ω₃ _ _
    · exact (ih (k - 1) (by omega) c' R (hasOrder_of_forall fun x hx => hR x (by omega)) hRc).mono_le (by omega) le_rfl
  have hbudget : ∀ c' : ℕ, c' ≤ c + 2 * k * cΩ → c' + 2 * (k - 1) * (k - 1) * cΩ ≤ c + 2 * k * k * cΩ := by
    intro c' hc'
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0; simpa using hc'
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      nlinarith [hc', Nat.zero_le (m * cΩ), Nat.zero_le cΩ]

  set T : DOp ι := ∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, cmul (D x) (mono x.1 x.2) with hT
  have hTapply : ∀ y : ℕ × ℕ, T y = if y ∈ Finset.HasAntidiagonal.antidiagonal k then D y else 0 := by
    classical
    intro y
    simp only [hT, Finsupp.finset_sum_apply, cmul_apply, mono, Finsupp.single_apply]
    by_cases hy : y ∈ Finset.HasAntidiagonal.antidiagonal k
    · rw [if_pos hy, Finset.sum_eq_single y]
      · simp
      · intro x _ hxy
        have : (x.1, x.2) ≠ y := by simpa using hxy
        simp [this]
      · intro h; exact absurd hy h
    · rw [if_neg hy]
      refine Finset.sum_eq_zero fun x hx => ?_
      have : (x.1, x.2) ≠ y := by
        intro h
        apply hy
        rw [← h]
        exact hx
      simp [this]
  have hTnf : NFd Ω₂ Ω₃ k (c + 2 * k * k * cΩ) T := by
    refine NFd.sum _ fun x hx => ?_
    obtain ⟨N, R, hN, hR, hRdeg, hmono⟩ := exists_nfd_mono hΩ h₂ h₃ x.1 x.2
    have hxk : x.1 + x.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    rw [hmono, cmul_add]
    refine ((hN.mono_le hxk.le le_rfl).cmul (hDc x)).mono_le le_rfl (by simp) |>.add ?_
    have hRk : DDeg (c + 2 * k * cΩ) (cmul (D x) R) := by
      rw [← hxk]; exact ddeg_cmul (hDc x) hRdeg
    refine (hlow _ _ (fun y hy => ?_) hRk).mono_le le_rfl (hbudget _ le_rfl)
    rw [cmul_apply, hR y (by omega), mul_zero]
  have hrest : NFd Ω₂ Ω₃ k (c + 2 * k * k * cΩ) (D - T) := by
    have hDT : DDeg c (D - T) := by
      refine hDc.sub fun y => ?_
      rw [hTapply]
      split_ifs
      · exact hDc y
      · exact mdeg_zero c
    refine (hlow c _ (fun y hy => ?_) hDT).mono_le le_rfl (hbudget c (by omega))
    rw [Finsupp.sub_apply, hTapply, sub_eq_zero]
    split_ifs with hmem
    · rfl
    · exact apply_eq_zero_of_hasOrder hD (lt_of_le_of_ne hy fun h => hmem (Finset.HasAntidiagonal.mem_antidiagonal.mpr h.symm))
  simpa using hTnf.add hrest

end DegreeBounds
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

section ReductionDegrees

variable {Ω₂ Ω₃ : DOp ι} {N₂ N₃ : ℕ} {a₂ : Fin (N₂ + 1) → ℂ} {a₃ : Fin (N₃ + 1) → ℂ}

private theorem redT_nb_deg (hΩ : IsCasimirPair Ω₂ Ω₃) (ha₂ : a₂ (Fin.last N₂) = 1) (ha₃ : a₃ (Fin.last N₃) = 1)
    (j : Fin 6) :
    ∀ (n : ℕ) (e f : ℕ), e + f = n →
      ∃ T, (∀ j' e' f', MDeg 0 (T j' e' f')) ∧ RedT Ω₂ Ω₃ a₂ a₃ (nb Ω₂ Ω₃ j e f) T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro e f hef
    by_cases he : e < N₂
    · by_cases hf : f < N₃
      · refine ⟨_, fun j' e' f' => ?_, redT_nb_reduced j ⟨e, he⟩ ⟨f, hf⟩⟩
        unfold unitT
        split_ifs <;> first | exact mdeg_one 0 | exact mdeg_zero 0
      · obtain ⟨f₀, rfl⟩ : ∃ f₀, f = f₀ + N₃ := ⟨f - N₃, by omega⟩
        have hrec : ∀ m : Fin N₃, ∃ T, (∀ j' e' f', MDeg 0 (T j' e' f')) ∧
            RedT Ω₂ Ω₃ a₂ a₃ (nb Ω₂ Ω₃ j e (f₀ + m)) T :=
          fun m => ih (e + (f₀ + m)) (by have := m.isLt; omega) e (f₀ + m) rfl
        choose Tm hTmd hTm using hrec
        rw [nb_split₃ ha₃]
        refine ⟨_, fun j' e' f' => ?_,
          redT_add (redT_ideal₃ a₂ a₃ _) (redT_sum Finset.univ fun m _ => redT_smul (hTm m) _)⟩
        exact (mdeg_zero 0).add (MDeg.sum _ fun m _ => MDeg.smul _ (hTmd m j' e' f'))
    · obtain ⟨e₀, rfl⟩ : ∃ e₀, e = e₀ + N₂ := ⟨e - N₂, by omega⟩
      have hrec : ∀ m : Fin N₂, ∃ T, (∀ j' e' f', MDeg 0 (T j' e' f')) ∧
          RedT Ω₂ Ω₃ a₂ a₃ (nb Ω₂ Ω₃ j (e₀ + m) f) T :=
        fun m => ih (e₀ + m + f) (by have := m.isLt; omega) (e₀ + m) f rfl
      choose Tm hTmd hTm using hrec
      rw [nb_split₂ hΩ ha₂]
      refine ⟨_, fun j' e' f' => ?_,
        redT_add (redT_ideal₂ a₂ a₃ _) (redT_sum Finset.univ fun m _ => redT_smul (hTm m) _)⟩
      exact (mdeg_zero 0).add (MDeg.sum _ fun m _ => MDeg.smul _ (hTmd m j' e' f'))

private theorem exists_redT_deg {cΩ : ℕ} (hΩ : IsCasimirPair Ω₂ Ω₃) (h₂ : DDeg cΩ Ω₂) (h₃ : DDeg cΩ Ω₃)
    (ha₂ : a₂ (Fin.last N₂) = 1) (ha₃ : a₃ (Fin.last N₃) = 1) {k c : ℕ} {D : DOp ι} (hD : HasOrder D k)
    (hDc : DDeg c D) :
    ∃ T, (∀ j e f, MDeg (c + 2 * k * k * cΩ) (T j e f)) ∧ RedT Ω₂ Ω₃ a₂ a₃ D T := by
  obtain ⟨ν, -, hνd, rfl⟩ := nfd_of_hasOrder hΩ h₂ h₃ k c D hD hDc
  have hb : ∀ (j : Fin 6) (e f : ℕ), ∃ T, (∀ j' e' f', MDeg 0 (T j' e' f')) ∧ RedT Ω₂ Ω₃ a₂ a₃ (nb Ω₂ Ω₃ j e f) T :=
    fun j e f => redT_nb_deg hΩ ha₂ ha₃ j (e + f) e f rfl
  choose Tb hTbd hTb using hb
  unfold nfSum
  refine ⟨_, fun j' e' f' => ?_, redT_sum Finset.univ fun j _ =>
    redT_sum _ fun e _ => redT_sum _ fun f _ => redT_cmul (hTb j e f) (ν j e f)⟩
  refine MDeg.sum _ fun j _ => MDeg.sum _ fun e _ => MDeg.sum _ fun f _ => ?_
  simpa using (hνd j e f).mul (hTbd j e f j' e' f')

end ReductionDegrees
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

private theorem exists_reduce_totalDegree_le (k c cΩ N₂ N₃ : ℕ) :
    ∃ δ : ℕ, ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {Ω₂ Ω₃ : DOp ι}, IsCasimirPair Ω₂ Ω₃ →
      (∀ ab (i i' : ι), (Ω₂ ab i i').totalDegree ≤ cΩ) → (∀ ab (i i' : ι), (Ω₃ ab i i').totalDegree ≤ cΩ) →
      ∀ (a₂ : Fin (N₂ + 1) → ℂ), a₂ (Fin.last N₂) = 1 → ∀ (a₃ : Fin (N₃ + 1) → ℂ), a₃ (Fin.last N₃) = 1 →
      ∀ D : DOp ι, HasOrder D k → (∀ ab (i i' : ι), (D ab i i').totalDegree ≤ c) →
      ∃ (ν : Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef) (Y Y' : DOp ι),
        D = (∑ j, ∑ e, ∑ f, cmul (ν j e f) (nb Ω₂ Ω₃ j e f)) + comp Y (polyOp a₂ Ω₂) + comp Y' (polyOp a₃ Ω₃) ∧
        ∀ j e f (i i' : ι), (ν j e f i i').totalDegree ≤ δ := by
  refine ⟨c + 2 * k * k * cΩ, ?_⟩
  intro ι _ _ Ω₂ Ω₃ hΩ h₂ h₃ a₂ ha₂ a₃ ha₃ D hD hDc
  obtain ⟨T, hTd, Y, Y', hY⟩ := exists_redT_deg hΩ h₂ h₃ ha₂ ha₃ hD hDc
  exact ⟨T, Y, Y', hY, fun j e f i i' => hTd j e f i i'⟩

private theorem aeval_wall_charpoly_eq_zero {n : Type} [Fintype n] [DecidableEq n] (A P : Matrix n n Coef)
    (hA : A.map killX0 = A) (hlax : A.map (eul 1) = A * P - P * A) (x : Fin 2 → ℂ) :
    Polynomial.aeval (A.map (MvPolynomial.eval x)) ((A.map constantCoeff).charpoly) = 0 := by
  have hconst := charpoly_const_of_lax A P hA hlax
  have hcp : (A.map (MvPolynomial.eval x)).charpoly = ((A.map constantCoeff).charpoly).map (RingHom.id ℂ) := by
    rw [Polynomial.map_id, Matrix.charpoly_map, Matrix.charpoly_map]
    ext k
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    conv_lhs => rw [hconst k]
    simp only [MvPolynomial.eval_C]
  rw [Polynomial.map_id] at hcp
  rw [← hcp]
  exact Matrix.aeval_self_charpoly _

private def entM (i i' : ι) (M : Matrix ι ι Coef) : Matrix Unit Unit Coef := fun _ _ => M i i'

omit [Fintype ι] [DecidableEq ι] in
private theorem entM_zero (i i' : ι) : entM i i' (0 : Matrix ι ι Coef) = 0 := by
  funext _ _; simp [entM]

omit [Fintype ι] [DecidableEq ι] in
private theorem entM_add (i i' : ι) (M M' : Matrix ι ι Coef) : entM i i' (M + M') = entM i i' M + entM i i' M' := by
  funext _ _; simp [entM]

private noncomputable def ent (i i' : ι) (D : DOp ι) : DOp Unit := Finsupp.mapRange (entM i i') (entM_zero i i') D

private theorem ent_apply (i i' : ι) (D : DOp ι) (ab : ℕ × ℕ) : ent i i' D ab = entM i i' (D ab) :=
  Finsupp.mapRange_apply

private theorem ent_single (i i' : ι) (ab : ℕ × ℕ) (M : Matrix ι ι Coef) :
    ent i i' (Finsupp.single ab M) = Finsupp.single ab (entM i i' M) :=
  Finsupp.mapRange_single

private theorem ent_zero (i i' : ι) : ent i i' (0 : DOp ι) = 0 := Finsupp.mapRange_zero

private theorem ent_add (i i' : ι) (D D' : DOp ι) : ent i i' (D + D') = ent i i' D + ent i i' D' :=
  Finsupp.mapRange_add (entM_add i i') D D'

private noncomputable def entHom (i i' : ι) : DOp ι →+ DOp Unit where
  toFun := ent i i'
  map_zero' := ent_zero i i'
  map_add' := ent_add i i'

private theorem entHom_apply (i i' : ι) (D : DOp ι) : entHom i i' D = ent i i' D := rfl

private theorem ent_sub (i i' : ι) (D D' : DOp ι) : ent i i' (D - D') = ent i i' D - ent i i' D' :=
  map_sub (entHom i i') D D'

private theorem ent_smul (i i' : ι) (c : ℂ) (D : DOp ι) : ent i i' (c • D) = c • ent i i' D := by
  refine Finsupp.ext fun ab => Matrix.ext fun _ _ => ?_
  simp only [ent_apply, Finsupp.smul_apply, entM, Matrix.smul_apply]

private theorem ent_finset_sum {α : Type} (s : Finset α) (g : α → DOp ι) (i i' : ι) :
    ent i i' (∑ a ∈ s, g a) = ∑ a ∈ s, ent i i' (g a) :=
  map_sum (entHom i i') g s

private theorem ent_finsupp_sum (i i' : ι) (D : DOp ι) (g : ℕ × ℕ → Matrix ι ι Coef → DOp ι) :
    ent i i' (D.sum g) = D.sum fun ab M => ent i i' (g ab M) := by
  simp only [Finsupp.sum]
  exact map_sum (entHom i i') _ _

private def IsDiag (D : DOp ι) : Prop := ∀ (ab : ℕ × ℕ) (k k' : ι), k ≠ k' → D ab k k' = 0

omit [DecidableEq ι] in

private theorem mul_apply_of_diag (M N : Matrix ι ι Coef) (i' : ι) (hN : ∀ k, k ≠ i' → N k i' = 0) (i : ι) :
    (M * N) i i' = M i i' * N i' i' := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i']
  · intro k _ hk
    rw [hN k hk, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i') h

omit [DecidableEq ι] in
private theorem entM_mul_of_diag (M N : Matrix ι ι Coef) (i i' : ι) (hN : ∀ k, k ≠ i' → N k i' = 0) :
    entM i i' (M * N) = entM i i' M * entM i' i' N := by
  unfold entM
  refine Matrix.ext fun u v => ?_
  show (M * N) i i' = _
  rw [mul_apply_of_diag M N i' hN i]
  simp [Matrix.mul_apply]

omit [Fintype ι] [DecidableEq ι] in
private theorem entM_smul (c : ℂ) (M : Matrix ι ι Coef) (i i' : ι) : entM i i' (c • M) = c • entM i i' M := by
  funext _ _; simp [entM]

omit [Fintype ι] [DecidableEq ι] in
private theorem entM_map (g : Coef → Coef) (M : Matrix ι ι Coef) (i i' : ι) :
    entM i i' (M.map g) = (entM i i' M).map g := by
  funext _ _; simp [entM]

private theorem ent_cmul_of_isDiag (M : Matrix ι ι Coef) {D : DOp ι} (hD : IsDiag D) (i i' : ι) :
    ent i i' (cmul M D) = cmul (entM i i' M) (ent i' i' D) := by
  unfold cmul
  rw [ent_finsupp_sum]
  conv_rhs => unfold ent
  rw [Finsupp.sum_mapRange_index (fun _ => by simp)]
  refine Finsupp.sum_congr fun ab _ => ?_
  rw [ent_single, entM_mul_of_diag _ _ _ _ (fun k hk => hD ab k i' hk)]

private theorem ent_comp_of_isDiag (D : DOp ι) {D' : DOp ι} (hD' : IsDiag D') (i i' : ι) :
    ent i i' (comp D D') = comp (ent i i' D) (ent i' i' D') := by
  have hmap0 : ∀ n m : ℕ, ((eul 0)^[n] ∘ (eul 1)^[m]) (0 : Coef) = 0 := by
    intro n m
    have h0 : ∀ (j : Fin 2) (k : ℕ), (eul j)^[k] (0 : Coef) = 0 := by
      intro j k
      induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply', ih]; simp [eul]
    simp only [Function.comp_apply, h0]
  have hmz : ∀ (κ : Type) (n m : ℕ), (0 : Matrix κ κ Coef).map ((eul 0)^[n] ∘ (eul 1)^[m]) = 0 :=
    fun _ n m => Matrix.map_zero _ (hmap0 n m)
  unfold comp
  rw [ent_finsupp_sum]
  conv_rhs => unfold ent
  rw [Finsupp.sum_mapRange_index (fun _ => by simp)]
  refine Finsupp.sum_congr fun ab _ => ?_
  rw [ent_finsupp_sum, Finsupp.sum_mapRange_index (fun _ => by
    simp only [hmz, mul_zero, smul_zero, Finsupp.single_zero, Finset.sum_const_zero])]
  refine Finsupp.sum_congr fun cd _ => ?_
  rw [ent_finset_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ent_finset_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ent_single, entM_smul, entM_mul_of_diag, entM_map]
  intro k hk
  simp only [Matrix.map_apply, hD' cd k i' hk, hmap0]

private theorem apply_eq_ent (D : DOp ι) (ab : ℕ × ℕ) (k k' : ι) : D ab k k' = ent k k' D ab () () := by
  rw [ent_apply]; rfl

private theorem ent_eq_zero_of_isDiag {D : DOp ι} (hD : IsDiag D) {k k' : ι} (h : k ≠ k') : ent k k' D = 0 := by
  refine Finsupp.ext fun ab => ?_
  rw [ent_apply, Finsupp.zero_apply]
  exact Matrix.ext fun _ _ => hD ab k k' h

private theorem isDiag_of_ent {D : DOp ι} (h : ∀ k k' : ι, k ≠ k' → ent k k' D = 0) : IsDiag D := by
  intro ab k k' hkk'
  rw [apply_eq_ent, h k k' hkk']
  rfl

private theorem zero_comp (D' : DOp ι) : comp (0 : DOp ι) D' = 0 := by
  unfold comp
  exact Finsupp.sum_zero_index

private theorem IsDiag.comp {D D' : DOp ι} (hD : IsDiag D) (hD' : IsDiag D') : IsDiag (comp D D') :=
  isDiag_of_ent fun k k' h => by rw [ent_comp_of_isDiag _ hD', ent_eq_zero_of_isDiag hD h, zero_comp]

private theorem isDiag_single_one (ab : ℕ × ℕ) : IsDiag (Finsupp.single ab (1 : Matrix ι ι Coef)) := by
  intro cd k k' h
  rw [Finsupp.single_apply]
  split_ifs
  · exact Matrix.one_apply_ne h
  · rfl

private theorem isDiag_one : IsDiag (one : DOp ι) := isDiag_single_one _
private theorem isDiag_d₁ : IsDiag (d₁ : DOp ι) := isDiag_single_one _
private theorem isDiag_B (j : Fin 6) : IsDiag (B j : DOp ι) := isDiag_single_one _

private theorem IsDiag.npow {Ω : DOp ι} (hΩ : IsDiag Ω) (n : ℕ) : IsDiag (npow Ω n) := by
  induction n with
  | zero => exact isDiag_one
  | succ n ih => rw [npow_succ']; exact hΩ.comp ih

private theorem IsDiag.smul {D : DOp ι} (hD : IsDiag D) (c : ℂ) : IsDiag (c • D) := by
  intro ab k k' h
  simp only [Finsupp.smul_apply, Matrix.smul_apply, hD ab k k' h, smul_zero]

private theorem isDiag_sum {α : Type} (s : Finset α) (g : α → DOp ι) (hg : ∀ a ∈ s, IsDiag (g a)) :
    IsDiag (∑ a ∈ s, g a) := by
  intro ab k k' h
  rw [Finsupp.finset_sum_apply, Matrix.sum_apply]
  exact Finset.sum_eq_zero fun a ha => hg a ha ab k k' h

private theorem IsDiag.polyOp {Ω : DOp ι} (hΩ : IsDiag Ω) {N : ℕ} (a : Fin (N + 1) → ℂ) : IsDiag (polyOp a Ω) :=
  isDiag_sum _ _ fun m _ => (hΩ.npow m).smul (a m)

private theorem isDiag_nb {Ω₂ Ω₃ : DOp ι} (h₂ : IsDiag Ω₂) (h₃ : IsDiag Ω₃) (j : Fin 6) (e f : ℕ) :
    IsDiag (nb Ω₂ Ω₃ j e f) :=
  (isDiag_B j).comp ((h₂.npow e).comp (h₃.npow f))

omit [Fintype ι] in
private theorem entM_one_same (i : ι) : entM i i (1 : Matrix ι ι Coef) = 1 := by
  funext _ _; simp [entM]

omit [Fintype ι] in
private theorem entM_one_ne {i i' : ι} (h : i ≠ i') : entM i i' (1 : Matrix ι ι Coef) = 0 := by
  funext _ _; simp [entM, Matrix.one_apply_ne h]

private theorem ent_single_one_same (i : ι) (ab : ℕ × ℕ) :
    ent i i (Finsupp.single ab (1 : Matrix ι ι Coef)) = Finsupp.single ab 1 := by
  rw [ent_single, entM_one_same]

private theorem ent_single_one_ne {i i' : ι} (h : i ≠ i') (ab : ℕ × ℕ) :
    ent i i' (Finsupp.single ab (1 : Matrix ι ι Coef)) = 0 := by
  rw [ent_single, entM_one_ne h, Finsupp.single_zero]

private theorem ent_one_same (i : ι) : ent i i (one : DOp ι) = one := ent_single_one_same i _
private theorem ent_d₁_same (i : ι) : ent i i (d₁ : DOp ι) = d₁ := ent_single_one_same i _
private theorem ent_d₁_ne {i i' : ι} (h : i ≠ i') : ent i i' (d₁ : DOp ι) = 0 := ent_single_one_ne h _
private theorem ent_B_same (i : ι) (j : Fin 6) : ent i i (B j : DOp ι) = B j := ent_single_one_same i _

private theorem ent_npow_same {Ω : DOp ι} (hΩ : IsDiag Ω) (i : ι) (n : ℕ) :
    ent i i (npow Ω n) = npow (ent i i Ω) n := by
  induction n with
  | zero => exact ent_one_same i
  | succ n ih => rw [npow_succ', npow_succ', ent_comp_of_isDiag _ (hΩ.npow n), ih]

private theorem ent_polyOp_same {Ω : DOp ι} (hΩ : IsDiag Ω) (i : ι) {N : ℕ} (a : Fin (N + 1) → ℂ) :
    ent i i (polyOp a Ω) = polyOp a (ent i i Ω) := by
  unfold polyOp
  rw [ent_finset_sum]
  exact Finset.sum_congr rfl fun m _ => by rw [ent_smul, ent_npow_same hΩ]

private theorem ent_nb_same {Ω₂ Ω₃ : DOp ι} (h₂ : IsDiag Ω₂) (h₃ : IsDiag Ω₃) (i : ι) (j : Fin 6) (e f : ℕ) :
    ent i i (nb Ω₂ Ω₃ j e f) = nb (ent i i Ω₂) (ent i i Ω₃) j e f := by
  unfold nb
  rw [ent_comp_of_isDiag _ ((h₂.npow e).comp (h₃.npow f)), ent_B_same, ent_comp_of_isDiag _ (h₃.npow f),
    ent_npow_same h₂, ent_npow_same h₃]

private theorem ent_relation {Ω₂ Ω₃ : DOp ι} (h₂ : IsDiag Ω₂) (h₃ : IsDiag Ω₃) {N₂ N₃ : ℕ}
    (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ) (j : Fin 6) (e : Fin N₂) (f : Fin N₃)
    (blk : Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef) (Y Y' : DOp ι)
    (h : comp d₁ (nb Ω₂ Ω₃ j e f)
      = (∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃, cmul (blk j' e' f') (nb Ω₂ Ω₃ j' e' f'))
          + comp Y (polyOp a₂ Ω₂) + comp Y' (polyOp a₃ Ω₃))
    (i i' : ι) :
    (if i = i' then comp d₁ (nb (ent i' i' Ω₂) (ent i' i' Ω₃) j e f) else 0)
      = (∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃,
            cmul (entM i i' (blk j' e' f')) (nb (ent i' i' Ω₂) (ent i' i' Ω₃) j' e' f'))
          + comp (ent i i' Y) (polyOp a₂ (ent i' i' Ω₂)) + comp (ent i i' Y') (polyOp a₃ (ent i' i' Ω₃)) := by
  have hs := congrArg (ent i i') h
  rw [ent_comp_of_isDiag _ (isDiag_nb h₂ h₃ j e f), ent_nb_same h₂ h₃, ent_add, ent_add, ent_finset_sum,
    ent_comp_of_isDiag _ (h₂.polyOp a₂), ent_comp_of_isDiag _ (h₃.polyOp a₃), ent_polyOp_same h₂,
    ent_polyOp_same h₃] at hs
  simp only [ent_finset_sum] at hs
  simp only [ent_cmul_of_isDiag _ (isDiag_nb h₂ h₃ _ _ _), ent_nb_same h₂ h₃] at hs
  rw [← hs]
  by_cases hii : i = i'
  · subst hii; rw [if_pos rfl, ent_d₁_same]
  · rw [if_neg hii, ent_d₁_ne hii, zero_comp]

private theorem cmap_smul' (φ : Coef →ₐ[ℂ] Coef) (c : ℂ) (D : DOp ι) : cmap φ (c • D) = c • cmap φ D := by
  ext x k k'
  simp only [cmap_apply, Finsupp.smul_apply, Matrix.map_apply, Matrix.smul_apply, map_smul]

private theorem cmap_add' (φ : Coef →ₐ[ℂ] Coef) (D D' : DOp ι) : cmap φ (D + D') = cmap φ D + cmap φ D' := by
  ext x k k'
  simp only [cmap_apply, Finsupp.add_apply, Matrix.map_apply, Matrix.add_apply, map_add]

private theorem cmap_single_one (φ : Coef →ₐ[ℂ] Coef) (ab : ℕ × ℕ) :
    cmap φ (Finsupp.single ab (1 : Matrix ι ι Coef)) = Finsupp.single ab 1 := by
  rw [cmap_single, Matrix.map_one _ (map_zero φ) (map_one φ)]

private theorem cmap_one' (φ : Coef →ₐ[ℂ] Coef) : cmap φ (one : DOp ι) = one := cmap_single_one φ _
private theorem cmap_d₁' (φ : Coef →ₐ[ℂ] Coef) : cmap φ (d₁ : DOp ι) = d₁ := cmap_single_one φ _
private theorem cmap_B' (φ : Coef →ₐ[ℂ] Coef) (j : Fin 6) : cmap φ (B j : DOp ι) = B j := cmap_single_one φ _

private theorem cmap_npow' (φ : Coef →ₐ[ℂ] Coef)
    (hcomp : ∀ D D' : DOp ι, cmap φ (comp D D') = comp (cmap φ D) (cmap φ D')) (Ω : DOp ι) (n : ℕ) :
    cmap φ (npow Ω n) = npow (cmap φ Ω) n := by
  induction n with
  | zero => exact cmap_one' φ
  | succ n ih => rw [npow_succ', npow_succ', hcomp, ih]

private theorem cmap_polyOp' (φ : Coef →ₐ[ℂ] Coef)
    (hcomp : ∀ D D' : DOp ι, cmap φ (comp D D') = comp (cmap φ D) (cmap φ D')) (Ω : DOp ι) {N : ℕ}
    (a : Fin (N + 1) → ℂ) : cmap φ (polyOp a Ω) = polyOp a (cmap φ Ω) := by
  unfold polyOp
  rw [cmap_finset_sum]
  exact Finset.sum_congr rfl fun m _ => by rw [cmap_smul', cmap_npow' φ hcomp]

private theorem cmap_nb' (φ : Coef →ₐ[ℂ] Coef)
    (hcomp : ∀ D D' : DOp ι, cmap φ (comp D D') = comp (cmap φ D) (cmap φ D')) (Ω₂ Ω₃ : DOp ι) (j : Fin 6)
    (e f : ℕ) : cmap φ (nb Ω₂ Ω₃ j e f) = nb (cmap φ Ω₂) (cmap φ Ω₃) j e f := by
  unfold nb
  rw [hcomp, hcomp, cmap_B', cmap_npow' φ hcomp, cmap_npow' φ hcomp]

private theorem cmap_relation (φ : Coef →ₐ[ℂ] Coef)
    (hcomp : ∀ D D' : DOp ι, cmap φ (comp D D') = comp (cmap φ D) (cmap φ D')) {Ω₂ Ω₃ : DOp ι} {N₂ N₃ : ℕ}
    (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ) (j : Fin 6) (e : Fin N₂) (f : Fin N₃)
    (blk : Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef) (Y Y' : DOp ι)
    (h : comp d₁ (nb Ω₂ Ω₃ j e f)
      = (∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃, cmul (blk j' e' f') (nb Ω₂ Ω₃ j' e' f'))
          + comp Y (polyOp a₂ Ω₂) + comp Y' (polyOp a₃ Ω₃)) :
    comp d₁ (nb (cmap φ Ω₂) (cmap φ Ω₃) j e f)
      = (∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃,
            cmul ((blk j' e' f').map φ) (nb (cmap φ Ω₂) (cmap φ Ω₃) j' e' f'))
          + comp (cmap φ Y) (polyOp a₂ (cmap φ Ω₂)) + comp (cmap φ Y') (polyOp a₃ (cmap φ Ω₃)) := by
  have hs := congrArg (cmap φ) h
  rw [hcomp, cmap_d₁', cmap_nb' φ hcomp, cmap_add', cmap_add', cmap_finset_sum, hcomp, hcomp,
    cmap_polyOp' φ hcomp, cmap_polyOp' φ hcomp] at hs
  simp only [cmap_finset_sum, cmap_cmul_hom, cmap_nb' φ hcomp] at hs
  exact hs

private theorem sub_cmul (M M' : Matrix ι ι Coef) (D : DOp ι) : cmul (M - M') D = cmul M D - cmul M' D := by
  rw [eq_sub_iff_add_eq, ← add_cmul, sub_add_cancel]

private theorem sub_comp (Y Y' D : DOp ι) : comp (Y - Y') D = comp Y D - comp Y' D := by
  rw [eq_sub_iff_add_eq, ← add_comp, sub_add_cancel]

private theorem coeffs_eq_of_relations {Ω₂ Ω₃ : DOp ι} (hΩ : IsCasimirPair Ω₂ Ω₃) {N₂ N₃ : ℕ}
    (a₂ : Fin (N₂ + 1) → ℂ) (ha₂ : a₂ (Fin.last N₂) = 1) (a₃ : Fin (N₃ + 1) → ℂ) (ha₃ : a₃ (Fin.last N₃) = 1)
    (L : DOp ι) (A A' : Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef) (Y Y' Z Z' : DOp ι)
    (hA : L = (∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃, cmul (A j' e' f') (nb Ω₂ Ω₃ j' e' f'))
        + comp Y (polyOp a₂ Ω₂) + comp Y' (polyOp a₃ Ω₃))
    (hA' : L = (∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃, cmul (A' j' e' f') (nb Ω₂ Ω₃ j' e' f'))
        + comp Z (polyOp a₂ Ω₂) + comp Z' (polyOp a₃ Ω₃)) :
    ∀ j e f, A j e f = A' j e f := by
  intro j e f
  have h := normalForm_unique_mod hΩ a₂ ha₂ a₃ ha₃ (fun j e f => A j e f - A' j e f) (Z - Y) (Z' - Y') ?_
  · exact sub_eq_zero.mp (h j e f)
  simp only [sub_cmul, Finset.sum_sub_distrib, sub_comp]
  have key := hA.symm.trans hA'
  rw [sub_eq_iff_eq_add]
  calc (∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃, cmul (A j' e' f') (nb Ω₂ Ω₃ j' e' f'))
      = ((∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃, cmul (A j' e' f') (nb Ω₂ Ω₃ j' e' f'))
          + comp Y (polyOp a₂ Ω₂) + comp Y' (polyOp a₃ Ω₃)) - comp Y (polyOp a₂ Ω₂) - comp Y' (polyOp a₃ Ω₃) := by
        abel
    _ = ((∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃, cmul (A' j' e' f') (nb Ω₂ Ω₃ j' e' f'))
          + comp Z (polyOp a₂ Ω₂) + comp Z' (polyOp a₃ Ω₃)) - comp Y (polyOp a₂ Ω₂) - comp Y' (polyOp a₃ Ω₃) := by
        rw [key]
    _ = _ := by abel

private theorem connection_wall0_scalar {Ω₂ Ω₃ : DOp ι} (hΩ : IsCasimirPair Ω₂ Ω₃) {N₂ N₃ : ℕ}
    (a₂ : Fin (N₂ + 1) → ℂ) (ha₂ : a₂ (Fin.last N₂) = 1) (a₃ : Fin (N₃ + 1) → ℂ) (ha₃ : a₃ (Fin.last N₃) = 1)
    (ω₂ ω₃ : ℕ × ℕ → ℂ)
    (hω₂ : ∀ ab, (Ω₂ ab).map constantCoeff = ω₂ ab • (1 : Matrix ι ι ℂ))
    (hω₃ : ∀ ab, (Ω₃ ab).map constantCoeff = ω₃ ab • (1 : Matrix ι ι ℂ))
    (𝔐 : Matrix (RIdx N₂ N₃ ι) (RIdx N₂ N₃ ι) Coef)
    (h𝔐 : ∀ (j : Fin 6) (e : Fin N₂) (f : Fin N₃), ∃ Y Y' : DOp ι,
        comp d₁ (nb Ω₂ Ω₃ j e f)
          = (∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃,
              cmul (Matrix.of fun i i' => 𝔐 (j, e, f, i) (j', e', f', i')) (nb Ω₂ Ω₃ j' e' f'))
            + comp Y (polyOp a₂ Ω₂) + comp Y' (polyOp a₃ Ω₃))

    (Ωs₂ Ωs₃ : DOp Unit) (hΩs : IsCasimirPair Ωs₂ Ωs₃)
    (hΩs₂ : ∀ ab, Ωs₂ ab = fun _ _ => C (ω₂ ab)) (hΩs₃ : ∀ ab, Ωs₃ ab = fun _ _ => C (ω₃ ab))
    (Msc : Matrix (RIdx N₂ N₃ Unit) (RIdx N₂ N₃ Unit) Coef)
    (hMsc : ∀ (j : Fin 6) (e : Fin N₂) (f : Fin N₃), ∃ Y Y' : DOp Unit,
        comp d₁ (nb Ωs₂ Ωs₃ j e f)
          = (∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃,
              cmul (Matrix.of fun i i' => Msc (j, e, f, i) (j', e', f', i')) (nb Ωs₂ Ωs₃ j' e' f'))
            + comp Y (polyOp a₂ Ωs₂) + comp Y' (polyOp a₃ Ωs₃)) :
    ∀ (J J' : Fin 6 × Fin N₂ × Fin N₃) (i i' : ι),
      constantCoeff (𝔐 (J.1, J.2.1, J.2.2, i) (J'.1, J'.2.1, J'.2.2, i'))
        = if i = i' then constantCoeff (Msc (J.1, J.2.1, J.2.2, ()) (J'.1, J'.2.1, J'.2.2, ())) else 0 := by
  have _ := hΩ

  have hcomp : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (D D' : DOp κ),
      cmap constHom (comp D D') = comp (cmap constHom D) (cmap constHom D') := by
    intro κ _ _ D D'
    have h := cmap_comp_const D D'
    rwa [const_fun_eq] at h
  intro J J' i i'
  obtain ⟨j, e, f⟩ := J
  obtain ⟨j', e', f'⟩ := J'

  have hdiag₂ : IsDiag (cmap constHom Ω₂) := by
    intro ab k k' hk
    have h := congrFun (congrFun (hω₂ ab) k) k'
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply_ne hk, smul_zero] at h
    rw [cmap_apply, Matrix.map_apply, constHom_apply, h, map_zero]
  have hdiag₃ : IsDiag (cmap constHom Ω₃) := by
    intro ab k k' hk
    have h := congrFun (congrFun (hω₃ ab) k) k'
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply_ne hk, smul_zero] at h
    rw [cmap_apply, Matrix.map_apply, constHom_apply, h, map_zero]
  have hent₂ : ∀ k : ι, ent k k (cmap constHom Ω₂) = Ωs₂ := by
    intro k
    refine Finsupp.ext fun ab => Matrix.ext fun u v => ?_
    have h := congrFun (congrFun (hω₂ ab) k) k
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
    rw [ent_apply, cmap_apply, hΩs₂]
    change constHom (Ω₂ ab k k) = C (ω₂ ab)
    rw [constHom_apply, h]
  have hent₃ : ∀ k : ι, ent k k (cmap constHom Ω₃) = Ωs₃ := by
    intro k
    refine Finsupp.ext fun ab => Matrix.ext fun u v => ?_
    have h := congrFun (congrFun (hω₃ ab) k) k
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
    rw [ent_apply, cmap_apply, hΩs₃]
    change constHom (Ω₃ ab k k) = C (ω₃ ab)
    rw [constHom_apply, h]

  have hfix₂ : cmap constHom Ωs₂ = Ωs₂ := by
    refine Finsupp.ext fun ab => Matrix.ext fun u v => ?_
    rw [cmap_apply, hΩs₂]
    change constHom (C (ω₂ ab)) = C (ω₂ ab)
    rw [constHom_apply, MvPolynomial.constantCoeff_C]
  have hfix₃ : cmap constHom Ωs₃ = Ωs₃ := by
    refine Finsupp.ext fun ab => Matrix.ext fun u v => ?_
    rw [cmap_apply, hΩs₃]
    change constHom (C (ω₃ ab)) = C (ω₃ ab)
    rw [constHom_apply, MvPolynomial.constantCoeff_C]

  obtain ⟨Y, Y', hrel⟩ := h𝔐 j e f
  obtain ⟨Z, Z', hs⟩ := hMsc j e f
  have hrelκ := cmap_relation constHom hcomp a₂ a₃ j e f
    (fun j' e' f' => Matrix.of fun k k' => 𝔐 (j, e, f, k) (j', e', f', k')) Y Y' hrel
  have hsl := ent_relation hdiag₂ hdiag₃ a₂ a₃ j e f
    (fun j' e' f' => (Matrix.of fun k k' => 𝔐 (j, e, f, k) (j', e', f', k')).map constHom) _ _ hrelκ i i'
  rw [hent₂, hent₃] at hsl
  have hsκ := cmap_relation constHom hcomp a₂ a₃ j e f
    (fun j' e' f' => Matrix.of fun u v => Msc (j, e, f, u) (j', e', f', v)) Z Z' hs
  rw [hfix₂, hfix₃] at hsκ
  by_cases hii : i = i'
  · subst hii
    rw [if_pos rfl] at hsl ⊢
    have hc := coeffs_eq_of_relations hΩs a₂ ha₂ a₃ ha₃ _ _ _ _ _ _ _ hsl hsκ j' e' f'
    have hc' := congrFun (congrFun hc ()) ()
    change constHom (𝔐 (j, e, f, i) (j', e', f', i)) = constHom (Msc (j, e, f, ()) (j', e', f', ())) at hc'
    rw [constHom_apply, constHom_apply] at hc'
    exact MvPolynomial.C_injective _ _ hc'
  · rw [if_neg hii] at hsl ⊢
    have h0 : (0 : DOp Unit)
        = (∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃,
              cmul ((fun _ _ _ => (0 : Matrix Unit Unit Coef)) j' e' f') (nb Ωs₂ Ωs₃ j' e' f'))
            + comp 0 (polyOp a₂ Ωs₂) + comp 0 (polyOp a₃ Ωs₃) := by
      simp only [cmul_zero_left, Finset.sum_const_zero, zero_comp, add_zero]
    have hc := coeffs_eq_of_relations hΩs a₂ ha₂ a₃ ha₃ _ _ _ _ _ _ _ hsl h0 j' e' f'
    have hc' := congrFun (congrFun hc ()) ()
    change constHom (𝔐 (j, e, f, i) (j', e', f', i')) = 0 at hc'
    rw [constHom_apply, MvPolynomial.C_eq_zero] at hc'
    exact hc'

private theorem connection_killX0_blockDiagonal {Ω₂ Ω₃ : DOp ι} (hΩ : IsCasimirPair Ω₂ Ω₃) {N₂ N₃ : ℕ}
    (a₂ : Fin (N₂ + 1) → ℂ) (ha₂ : a₂ (Fin.last N₂) = 1) (a₃ : Fin (N₃ + 1) → ℂ) (ha₃ : a₃ (Fin.last N₃) = 1)
    (zw : ι → ℂ) (φ₂ φ₃ : ℕ × ℕ → ℂ → Coef)
    (hφ₂ : ∀ ab c, killX0 (φ₂ ab c) = φ₂ ab c) (hφ₃ : ∀ ab c, killX0 (φ₃ ab c) = φ₃ ab c)
    (hΩ₂ : ∀ ab i i', killX0 (Ω₂ ab i i') = if i = i' then φ₂ ab (zw i) else 0)
    (hΩ₃ : ∀ ab i i', killX0 (Ω₃ ab i i') = if i = i' then φ₃ ab (zw i) else 0)
    (𝔐 : Matrix (RIdx N₂ N₃ ι) (RIdx N₂ N₃ ι) Coef)
    (h𝔐 : ∀ (j : Fin 6) (e : Fin N₂) (f : Fin N₃), ∃ Y Y' : DOp ι,
        comp d₁ (nb Ω₂ Ω₃ j e f)
          = (∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃,
              cmul (Matrix.of fun i i' => 𝔐 (j, e, f, i) (j', e', f', i')) (nb Ω₂ Ω₃ j' e' f'))
            + comp Y (polyOp a₂ Ω₂) + comp Y' (polyOp a₃ Ω₃))

    (Ωw₂ Ωw₃ : ι → DOp Unit) (hΩw : ∀ i, IsCasimirPair (Ωw₂ i) (Ωw₃ i))
    (hΩw₂ : ∀ i ab, Ωw₂ i ab = fun _ _ => φ₂ ab (zw i)) (hΩw₃ : ∀ i ab, Ωw₃ i ab = fun _ _ => φ₃ ab (zw i))
    (Mw : ι → Matrix (RIdx N₂ N₃ Unit) (RIdx N₂ N₃ Unit) Coef)
    (hMw : ∀ (i : ι) (j : Fin 6) (e : Fin N₂) (f : Fin N₃), ∃ Y Y' : DOp Unit,
        comp d₁ (nb (Ωw₂ i) (Ωw₃ i) j e f)
          = (∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃,
              cmul (Matrix.of fun k k' => Mw i (j, e, f, k) (j', e', f', k')) (nb (Ωw₂ i) (Ωw₃ i) j' e' f'))
            + comp Y (polyOp a₂ (Ωw₂ i)) + comp Y' (polyOp a₃ (Ωw₃ i))) :
    ∀ (J J' : Fin 6 × Fin N₂ × Fin N₃) (i i' : ι),
      killX0 (𝔐 (J.1, J.2.1, J.2.2, i) (J'.1, J'.2.1, J'.2.2, i'))
        = if i = i' then killX0 (Mw i (J.1, J.2.1, J.2.2, ()) (J'.1, J'.2.1, J'.2.2, ())) else 0 := by
  have _ := hΩ
  have hcomp : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (D D' : DOp κ),
      cmap killX0 (comp D D') = comp (cmap killX0 D) (cmap killX0 D') := fun D D' => cmap_comp_killX0 D D'
  intro J J' i i'
  obtain ⟨j, e, f⟩ := J
  obtain ⟨j', e', f'⟩ := J'

  have hdiag₂ : IsDiag (cmap killX0 Ω₂) := by
    intro ab k k' hk
    rw [cmap_apply, Matrix.map_apply, hΩ₂, if_neg hk]
  have hdiag₃ : IsDiag (cmap killX0 Ω₃) := by
    intro ab k k' hk
    rw [cmap_apply, Matrix.map_apply, hΩ₃, if_neg hk]
  have hent₂ : ∀ k : ι, ent k k (cmap killX0 Ω₂) = Ωw₂ k := by
    intro k
    refine Finsupp.ext fun ab => Matrix.ext fun u v => ?_
    rw [ent_apply, cmap_apply, hΩw₂]
    change killX0 (Ω₂ ab k k) = φ₂ ab (zw k)
    rw [hΩ₂, if_pos rfl]
  have hent₃ : ∀ k : ι, ent k k (cmap killX0 Ω₃) = Ωw₃ k := by
    intro k
    refine Finsupp.ext fun ab => Matrix.ext fun u v => ?_
    rw [ent_apply, cmap_apply, hΩw₃]
    change killX0 (Ω₃ ab k k) = φ₃ ab (zw k)
    rw [hΩ₃, if_pos rfl]

  have hfix₂ : ∀ k : ι, cmap killX0 (Ωw₂ k) = Ωw₂ k := by
    intro k
    refine Finsupp.ext fun ab => Matrix.ext fun u v => ?_
    rw [cmap_apply, hΩw₂]
    exact hφ₂ ab (zw k)
  have hfix₃ : ∀ k : ι, cmap killX0 (Ωw₃ k) = Ωw₃ k := by
    intro k
    refine Finsupp.ext fun ab => Matrix.ext fun u v => ?_
    rw [cmap_apply, hΩw₃]
    exact hφ₃ ab (zw k)
  obtain ⟨Y, Y', hrel⟩ := h𝔐 j e f
  have hrelκ := cmap_relation killX0 hcomp a₂ a₃ j e f
    (fun j' e' f' => Matrix.of fun k k' => 𝔐 (j, e, f, k) (j', e', f', k')) Y Y' hrel
  have hsl := ent_relation hdiag₂ hdiag₃ a₂ a₃ j e f
    (fun j' e' f' => (Matrix.of fun k k' => 𝔐 (j, e, f, k) (j', e', f', k')).map killX0) _ _ hrelκ i i'
  rw [hent₂, hent₃] at hsl
  by_cases hii : i = i'
  · subst hii
    rw [if_pos rfl] at hsl ⊢
    obtain ⟨Z, Z', hs⟩ := hMw i j e f
    have hsκ := cmap_relation killX0 hcomp a₂ a₃ j e f
      (fun j' e' f' => Matrix.of fun u v => Mw i (j, e, f, u) (j', e', f', v)) Z Z' hs
    rw [hfix₂, hfix₃] at hsκ
    have hc := coeffs_eq_of_relations (hΩw i) a₂ ha₂ a₃ ha₃ _ _ _ _ _ _ _ hsl hsκ j' e' f'
    exact congrFun (congrFun hc ()) ()
  · rw [if_neg hii] at hsl ⊢
    have h0 : (0 : DOp Unit)
        = (∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃,
              cmul ((fun _ _ _ => (0 : Matrix Unit Unit Coef)) j' e' f') (nb (Ωw₂ i') (Ωw₃ i') j' e' f'))
            + comp 0 (polyOp a₂ (Ωw₂ i')) + comp 0 (polyOp a₃ (Ωw₃ i')) := by
      simp only [cmul_zero_left, Finset.sum_const_zero, zero_comp, add_zero]
    have hc := coeffs_eq_of_relations (hΩw i') a₂ ha₂ a₃ ha₃ _ _ _ _ _ _ _ hsl h0 j' e' f'
    exact congrFun (congrFun hc ()) ()

private theorem aeval_blockDiagonal {o m : Type} [Fintype o] [DecidableEq o] [Fintype m] [DecidableEq m]
    (M : o → Matrix m m ℂ) (p : Polynomial ℂ) :
    Polynomial.aeval (Matrix.blockDiagonal M) p = Matrix.blockDiagonal fun k => Polynomial.aeval (M k) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, hp, hq]
    ext ⟨i, k⟩ ⟨j, k'⟩
    by_cases h : k = k'
    · subst h; simp [Matrix.blockDiagonal_apply_eq]
    · simp [Matrix.blockDiagonal_apply_ne _ _ _ h]
  | monomial n c =>
    simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    rw [← Matrix.blockDiagonal_pow, ← Matrix.blockDiagonal_smul]
    rfl

private def ridxEquiv (N₂ N₃ : ℕ) : RIdx N₂ N₃ ι ≃ RIdx N₂ N₃ Unit × ι where
  toFun x := ((x.1, x.2.1, x.2.2.1, ()), x.2.2.2)
  invFun y := (y.1.1, y.1.2.1, y.1.2.2.1, y.2)
  left_inv := by rintro ⟨j, e, f, i⟩; rfl
  right_inv := by rintro ⟨⟨j, e, f, u⟩, i⟩; cases u; rfl

private theorem aeval_charpoly_eq_zero_of_blockDiagonal {N₂ N₃ : ℕ}
    (Aw : Matrix (RIdx N₂ N₃ ι) (RIdx N₂ N₃ ι) Coef)
    (Bk Pk : ι → Matrix (RIdx N₂ N₃ Unit) (RIdx N₂ N₃ Unit) Coef)
    (B₀ : Matrix (RIdx N₂ N₃ Unit) (RIdx N₂ N₃ Unit) ℂ)
    (hblock : ∀ (J J' : Fin 6 × Fin N₂ × Fin N₃) (i i' : ι),
      Aw (J.1, J.2.1, J.2.2, i) (J'.1, J'.2.1, J'.2.2, i')
        = if i = i' then Bk i (J.1, J.2.1, J.2.2, ()) (J'.1, J'.2.1, J'.2.2, ()) else 0)
    (hB : ∀ i, (Bk i).map killX0 = Bk i) (hlax : ∀ i, (Bk i).map (eul 1) = Bk i * Pk i - Pk i * Bk i)
    (h0 : ∀ i, (Bk i).map constantCoeff = B₀) (x : Fin 2 → ℂ) :
    Polynomial.aeval (Aw.map (MvPolynomial.eval x)) B₀.charpoly = 0 := by

  have hAx : Aw.map (MvPolynomial.eval x)
      = Matrix.reindex (ridxEquiv N₂ N₃).symm (ridxEquiv N₂ N₃).symm
          (Matrix.blockDiagonal fun i => (Bk i).map (MvPolynomial.eval x)) := by
    ext ⟨j, e, f, i⟩ ⟨j', e', f', i'⟩
    rw [Matrix.map_apply, hblock (j, e, f) (j', e', f') i i', Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm]
    by_cases h : i = i'
    · subst h
      simp [ridxEquiv, Matrix.blockDiagonal_apply_eq]
    · simp [ridxEquiv, Matrix.blockDiagonal_apply_ne _ _ _ h, h]

  have hblk : ∀ i, Polynomial.aeval ((Bk i).map (MvPolynomial.eval x)) B₀.charpoly = 0 := by
    intro i
    have h := aeval_wall_charpoly_eq_zero (Bk i) (Pk i) (hB i) (hlax i) x
    rwa [h0 i] at h
  have hfun : (fun i => Polynomial.aeval ((Bk i).map (MvPolynomial.eval x)) B₀.charpoly) = (0 : ι → _) :=
    funext hblk
  rw [hAx, ← Matrix.reindexAlgEquiv_apply ℂ ℂ, Polynomial.aeval_algEquiv, AlgHom.comp_apply, aeval_blockDiagonal, hfun,
    Matrix.blockDiagonal_zero, map_zero]

private theorem iterate_d2_constMul (Q : Matrix ι ι Coef) (hQ1 : Q.map (eul 1) = 0) {G : ℝ → ℝ → (ι → ℂ)}
    (hG : Smooth2 G) :
    ∀ b : ℕ, (d2^[b]) (fun s₁ s₂ => mev Q s₁ s₂ *ᵥ G s₁ s₂) = fun t₁ t₂ => mev Q t₁ t₂ *ᵥ (d2^[b]) G t₁ t₂
  | 0 => rfl
  | b + 1 => by
    rw [Function.iterate_succ_apply', iterate_d2_constMul Q hQ1 hG b, Function.iterate_succ_apply',
      d2_mev_mulVec (smooth2_iterate_d2 hG b) Q, hQ1]
    funext t₁ t₂
    rw [mev_zero, Matrix.zero_mulVec, zero_add]

private theorem iterate_d1_constMul (Q : Matrix ι ι Coef) (hQ0 : Q.map (eul 0) = 0) {G : ℝ → ℝ → (ι → ℂ)}
    (hG : Smooth2 G) :
    ∀ a : ℕ, (d1^[a]) (fun s₁ s₂ => mev Q s₁ s₂ *ᵥ G s₁ s₂) = fun t₁ t₂ => mev Q t₁ t₂ *ᵥ (d1^[a]) G t₁ t₂
  | 0 => rfl
  | a + 1 => by
    rw [Function.iterate_succ_apply', iterate_d1_constMul Q hQ0 hG a, Function.iterate_succ_apply',
      d1_mev_mulVec (smooth2_iterate_d1 hG a) Q, hQ0]
    funext t₁ t₂
    rw [mev_zero, Matrix.zero_mulVec, zero_add]

private theorem dIter_constMul (Q : Matrix ι ι Coef) (hQ0 : Q.map (eul 0) = 0) (hQ1 : Q.map (eul 1) = 0)
    (a b : ℕ) {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) (t₁ t₂ : ℝ) :
    dIter a b (fun s₁ s₂ => mev Q s₁ s₂ *ᵥ G s₁ s₂) t₁ t₂ = mev Q t₁ t₂ *ᵥ dIter a b G t₁ t₂ := by
  simp only [dIter]
  rw [iterate_d2_constMul Q hQ1 hG b, iterate_d1_constMul Q hQ0 (smooth2_iterate_d2 hG b) a]

private noncomputable def conjLin (P Q : Matrix ι ι Coef) : Matrix ι ι Coef →ₗ[ℂ] Matrix ι ι Coef where
  toFun M := P * M * Q
  map_add' M N := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c M := by simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

private noncomputable def umap (P Q : Matrix ι ι Coef) : DOp ι →ₗ[ℂ] DOp ι :=
  Finsupp.mapRange.linearMap (conjLin P Q)

private theorem umap_eq (P Q : Matrix ι ι Coef) (D : DOp ι) :
    umap P Q D = Finsupp.mapRange (fun M => P * M * Q) (by simp) D := rfl

private theorem umap_apply (P Q : Matrix ι ι Coef) (D : DOp ι) (ab : ℕ × ℕ) : umap P Q D ab = P * D ab * Q := rfl

private theorem support_umap (P Q : Matrix ι ι Coef) (D : DOp ι) : (umap P Q D).support ⊆ D.support := by
  rw [umap_eq]
  exact Finsupp.support_mapRange

private theorem umap_single (P Q : Matrix ι ι Coef) (ab : ℕ × ℕ) (M : Matrix ι ι Coef) :
    umap P Q (Finsupp.single ab M) = Finsupp.single ab (P * M * Q) := by
  rw [umap_eq, Finsupp.mapRange_single]

private theorem apply_umap (P Q : Matrix ι ι Coef) (hQ0 : Q.map (eul 0) = 0) (hQ1 : Q.map (eul 1) = 0)
    (D : DOp ι) {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) :
    apply (umap P Q D) G = fun t₁ t₂ => mev P t₁ t₂ *ᵥ apply D (fun s₁ s₂ => mev Q s₁ s₂ *ᵥ G s₁ s₂) t₁ t₂ := by
  funext t₁ t₂
  simp only [DOp.apply, umap_eq]
  rw [Finsupp.sum_mapRange_index fun ab => by rw [mev_zero, Matrix.zero_mulVec]]
  simp only [Finsupp.sum, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [dIter_constMul Q hQ0 hQ1 ab.1 ab.2 hG]
  simp only [mev_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]

private theorem umap_comp (P Q : Matrix ι ι Coef) (hQP : Q * P = 1) (hQ0 : Q.map (eul 0) = 0)
    (hQ1 : Q.map (eul 1) = 0) (D D' : DOp ι) : umap P Q (comp D D') = comp (umap P Q D) (umap P Q D') := by
  refine ext_of_apply fun G hG => ?_
  have hQG : Smooth2 fun s₁ s₂ => mev Q s₁ s₂ *ᵥ G s₁ s₂ := hG.mev_mulVec Q
  rw [apply_umap P Q hQ0 hQ1 _ hG, apply_comp _ _ hQG, apply_comp _ _ hG, apply_umap P Q hQ0 hQ1 D' hG,
    apply_umap P Q hQ0 hQ1 D ((Smooth2.apply D' hQG).mev_mulVec P)]
  funext t₁ t₂
  simp only [Matrix.mulVec_mulVec, ← mev_mul, hQP, mev_one, Matrix.one_mulVec]

private theorem umap_cmul (P Q : Matrix ι ι Coef) (hQP : Q * P = 1) (hQ0 : Q.map (eul 0) = 0)
    (hQ1 : Q.map (eul 1) = 0) (M : Matrix ι ι Coef) (D : DOp ι) :
    umap P Q (cmul M D) = cmul (P * M * Q) (umap P Q D) := by
  refine ext_of_apply fun G hG => ?_
  rw [apply_umap P Q hQ0 hQ1 _ hG, apply_cmul, apply_cmul, apply_umap P Q hQ0 hQ1 D hG]
  funext t₁ t₂
  simp only [Matrix.mulVec_mulVec, ← mev_mul, Matrix.mul_assoc, hQP, Matrix.mul_one]

private theorem umap_one (P Q : Matrix ι ι Coef) (hPQ : P * Q = 1) : umap P Q one = one := by
  rw [DOp.one, umap_single, Matrix.mul_one, hPQ]

private theorem umap_d₁ (P Q : Matrix ι ι Coef) (hPQ : P * Q = 1) : umap P Q d₁ = d₁ := by
  rw [d₁, umap_single, Matrix.mul_one, hPQ]

private theorem umap_B (P Q : Matrix ι ι Coef) (hPQ : P * Q = 1) (j : Fin 6) : umap P Q (B j) = B j := by
  rw [B, mono, umap_single, Matrix.mul_one, hPQ]

private theorem umap_npow (P Q : Matrix ι ι Coef) (hPQ : P * Q = 1) (hQP : Q * P = 1) (hQ0 : Q.map (eul 0) = 0)
    (hQ1 : Q.map (eul 1) = 0) (Ω : DOp ι) : ∀ n : ℕ, umap P Q (npow Ω n) = npow (umap P Q Ω) n
  | 0 => umap_one P Q hPQ
  | n + 1 => by
    have ih := umap_npow P Q hPQ hQP hQ0 hQ1 Ω n
    simp only [npow] at ih ⊢
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', umap_comp P Q hQP hQ0 hQ1, ih]

private theorem umap_polyOp (P Q : Matrix ι ι Coef) (hPQ : P * Q = 1) (hQP : Q * P = 1) (hQ0 : Q.map (eul 0) = 0)
    (hQ1 : Q.map (eul 1) = 0) {N : ℕ} (a : Fin (N + 1) → ℂ) (Ω : DOp ι) :
    umap P Q (polyOp a Ω) = polyOp a (umap P Q Ω) := by
  simp only [polyOp, map_sum, map_smul, umap_npow P Q hPQ hQP hQ0 hQ1 Ω]

private theorem umap_nb (P Q : Matrix ι ι Coef) (hPQ : P * Q = 1) (hQP : Q * P = 1) (hQ0 : Q.map (eul 0) = 0)
    (hQ1 : Q.map (eul 1) = 0) (Ω₂ Ω₃ : DOp ι) (j : Fin 6) (e f : ℕ) :
    umap P Q (nb Ω₂ Ω₃ j e f) = nb (umap P Q Ω₂) (umap P Q Ω₃) j e f := by
  rw [nb, nb, umap_comp P Q hQP hQ0 hQ1, umap_comp P Q hQP hQ0 hQ1, umap_B P Q hPQ, umap_npow P Q hPQ hQP hQ0 hQ1,
    umap_npow P Q hPQ hQP hQ0 hQ1]

private theorem conj_scal (P Q : Matrix ι ι Coef) (hPQ : P * Q = 1) (c : ℂ) : P * scal c * Q = scal c := by
  rw [scal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPQ]

private theorem isCasimirPair_umap (P Q : Matrix ι ι Coef) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hQ0 : Q.map (eul 0) = 0) (hQ1 : Q.map (eul 1) = 0) {Ω₂ Ω₃ : DOp ι} (hΩ : IsCasimirPair Ω₂ Ω₃) :
    IsCasimirPair (umap P Q Ω₂) (umap P Q Ω₃) where
  ord₂ := fun ab hab => hΩ.ord₂ ab (support_umap P Q Ω₂ hab)
  ord₃ := fun ab hab => hΩ.ord₃ ab (support_umap P Q Ω₃ hab)
  top₂₀ := by rw [umap_apply, hΩ.top₂₀, conj_scal P Q hPQ]
  top₁₁ := by rw [umap_apply, hΩ.top₁₁, conj_scal P Q hPQ]
  top₀₂ := by rw [umap_apply, hΩ.top₀₂, conj_scal P Q hPQ]
  top₃₀ := by rw [umap_apply, hΩ.top₃₀, Matrix.mul_zero, Matrix.zero_mul]
  top₂₁ := by rw [umap_apply, hΩ.top₂₁, conj_scal P Q hPQ]
  top₁₂ := by rw [umap_apply, hΩ.top₁₂, conj_scal P Q hPQ]
  top₀₃ := by rw [umap_apply, hΩ.top₀₃, Matrix.mul_zero, Matrix.zero_mul]
  comm := by rw [← umap_comp P Q hQP hQ0 hQ1, ← umap_comp P Q hQP hQ0 hQ1, hΩ.comm]

private theorem connection_conj_aux {Ω₂ Ω₃ : DOp ι} (hΩ : IsCasimirPair Ω₂ Ω₃) {N₂ N₃ : ℕ}
    (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ) (P Q : Matrix ι ι Coef) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hQ0 : Q.map (eul 0) = 0) (hQ1 : Q.map (eul 1) = 0)
    (blk : Fin 6 → Fin N₂ → Fin N₃ → Fin 6 → Fin N₂ → Fin N₃ → Matrix ι ι Coef)
    (h𝔐 : ∀ (j : Fin 6) (e : Fin N₂) (f : Fin N₃), ∃ Y Y' : DOp ι,
        comp d₁ (nb Ω₂ Ω₃ j e f)
          = (∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃, cmul (blk j e f j' e' f') (nb Ω₂ Ω₃ j' e' f'))
            + comp Y (polyOp a₂ Ω₂) + comp Y' (polyOp a₃ Ω₃)) :
    IsCasimirPair (umap P Q Ω₂) (umap P Q Ω₃) ∧
      ∀ (j : Fin 6) (e : Fin N₂) (f : Fin N₃), ∃ Y Y' : DOp ι,
        comp d₁ (nb (umap P Q Ω₂) (umap P Q Ω₃) j e f)
          = (∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃,
              cmul (P * blk j e f j' e' f' * Q) (nb (umap P Q Ω₂) (umap P Q Ω₃) j' e' f'))
            + comp Y (polyOp a₂ (umap P Q Ω₂)) + comp Y' (polyOp a₃ (umap P Q Ω₃)) := by
  refine ⟨isCasimirPair_umap P Q hPQ hQP hQ0 hQ1 hΩ, fun j e f => ?_⟩
  obtain ⟨Y, Y', hY⟩ := h𝔐 j e f
  refine ⟨umap P Q Y, umap P Q Y', ?_⟩
  have h := congrArg (umap P Q) hY
  rw [umap_comp P Q hQP hQ0 hQ1, umap_d₁ P Q hPQ, umap_nb P Q hPQ hQP hQ0 hQ1] at h
  rw [h, map_add, map_add, umap_comp P Q hQP hQ0 hQ1, umap_comp P Q hQP hQ0 hQ1, umap_polyOp P Q hPQ hQP hQ0 hQ1,
    umap_polyOp P Q hPQ hQP hQ0 hQ1]
  simp only [map_sum, umap_cmul P Q hQP hQ0 hQ1, umap_nb P Q hPQ hQP hQ0 hQ1]

private theorem connection_conj {Ω₂ Ω₃ : DOp ι} (hΩ : IsCasimirPair Ω₂ Ω₃) {N₂ N₃ : ℕ}
    (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnit U.det)
    (𝔐 : Matrix (RIdx N₂ N₃ ι) (RIdx N₂ N₃ ι) Coef)
    (h𝔐 : ∀ (j : Fin 6) (e : Fin N₂) (f : Fin N₃), ∃ Y Y' : DOp ι,
        comp d₁ (nb Ω₂ Ω₃ j e f)
          = (∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃,
              cmul (Matrix.of fun i i' => 𝔐 (j, e, f, i) (j', e', f', i')) (nb Ω₂ Ω₃ j' e' f'))
            + comp Y (polyOp a₂ Ω₂) + comp Y' (polyOp a₃ Ω₃)) :
    let Uc : Matrix ι ι Coef := U.map C
    let Uci : Matrix ι ι Coef := U⁻¹.map C
    let cΩ₂ : DOp ι := Finsupp.mapRange (fun M => Uc * M * Uci) (by simp) Ω₂
    let cΩ₃ : DOp ι := Finsupp.mapRange (fun M => Uc * M * Uci) (by simp) Ω₃
    IsCasimirPair cΩ₂ cΩ₃ ∧
      ∀ (j : Fin 6) (e : Fin N₂) (f : Fin N₃), ∃ Y Y' : DOp ι,
        comp d₁ (nb cΩ₂ cΩ₃ j e f)
          = (∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃,
              cmul (Matrix.of fun i i' =>
                  (Uc * (Matrix.of fun k k' => 𝔐 (j, e, f, k) (j', e', f', k')) * Uci) i i')
                (nb cΩ₂ cΩ₃ j' e' f'))
            + comp Y (polyOp a₂ cΩ₂) + comp Y' (polyOp a₃ cΩ₃) := by
  intro Uc Uci cΩ₂ cΩ₃
  have hPQ : U.map C * U⁻¹.map C = (1 : Matrix ι ι Coef) := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv U hU, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQP : U⁻¹.map C * U.map C = (1 : Matrix ι ι Coef) := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul U hU, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQ0 : (U⁻¹.map C : Matrix ι ι Coef).map (eul 0) = 0 :=
    Matrix.ext fun i j => by simp only [Matrix.map_apply, Matrix.zero_apply, eul_C]
  have hQ1 : (U⁻¹.map C : Matrix ι ι Coef).map (eul 1) = 0 :=
    Matrix.ext fun i j => by simp only [Matrix.map_apply, Matrix.zero_apply, eul_C]
  exact connection_conj_aux hΩ a₂ a₃ (U.map C) (U⁻¹.map C) hPQ hQP hQ0 hQ1
    (fun j e f j' e' f' => Matrix.of fun i i' => 𝔐 (j, e, f, i) (j', e', f', i')) h𝔐

end DOp
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

end NormalOrder
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

end HolonomicD2
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

namespace HolonomicD2

open MvPolynomial Matrix

private noncomputable def killX1 : Coef →ₐ[ℂ] Coef := MvPolynomial.aeval ![X 0, 0]

private noncomputable def swapC : Coef →ₐ[ℂ] Coef := MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)

private theorem swapC_swapC (p : Coef) : swapC (swapC p) = p := by
  have h : swapC.comp swapC = AlgHom.id ℂ Coef := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [swapC]
  exact AlgHom.congr_fun h p

private theorem swapC_X0 : swapC (X 0) = X 1 := by
  simp [swapC]

private theorem swapC_X1 : swapC (X 1) = X 0 := by
  simp [swapC]

private theorem swapC_C (c : ℂ) : swapC (C c) = C c := by
  simp [swapC]

private theorem constantCoeff_swapC (p : Coef) : MvPolynomial.constantCoeff (swapC p) = MvPolynomial.constantCoeff p :=
    by
  simp [swapC, MvPolynomial.constantCoeff_rename]

private theorem killX0_swapC (p : Coef) : killX0 (swapC p) = swapC (killX1 p) := by
  have h : killX0.comp swapC = swapC.comp killX1 := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [killX0, killX1, swapC]
  exact AlgHom.congr_fun h p

private theorem killX1_swapC (p : Coef) : killX1 (swapC p) = swapC (killX0 p) := by
  have h : killX1.comp swapC = swapC.comp killX0 := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [killX0, killX1, swapC]
  exact AlgHom.congr_fun h p

private theorem ev_swapC (p : Coef) (t₁ t₂ : ℝ) : (swapC p).ev t₁ t₂ = p.ev t₂ t₁ := by
  simp only [Coef.ev, swapC]
  rw [MvPolynomial.eval_rename]
  congr 2
  funext i
  fin_cases i <;> simp

private theorem totalDegree_swapC (p : Coef) : (swapC p).totalDegree = p.totalDegree := by
  apply le_antisymm
  · exact MvPolynomial.totalDegree_rename_le _ p
  · calc p.totalDegree = (swapC (swapC p)).totalDegree := by rw [swapC_swapC]
      _ ≤ (swapC p).totalDegree := MvPolynomial.totalDegree_rename_le _ _

section Swap

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace DOp

private noncomputable def swapOp (D : DOp ι) : DOp ι := Finsupp.mapDomain Prod.swap (cmap swapC D)

private def mswap (M : Matrix ι ι Coef) : Matrix ι ι Coef := M.map swapC

omit [Fintype ι] [DecidableEq ι] in
private theorem mswap_zero : mswap (0 : Matrix ι ι Coef) = 0 := by
  ext i j
  simp [mswap]

omit [Fintype ι] [DecidableEq ι] in
private theorem mswap_mswap (M : Matrix ι ι Coef) : mswap (mswap M) = M := by
  ext i j
  simp [mswap, swapC_swapC]

omit [Fintype ι] [DecidableEq ι] in
private theorem mswap_add (M N : Matrix ι ι Coef) : mswap (M + N) = mswap M + mswap N := by
  ext i j
  simp [mswap]

omit [Fintype ι] [DecidableEq ι] in
private theorem mswap_smul (c : ℂ) (M : Matrix ι ι Coef) : mswap (c • M) = c • mswap M := by
  ext i j
  simp [mswap]

omit [DecidableEq ι] in
private theorem mswap_mul (M N : Matrix ι ι Coef) : mswap (M * N) = mswap M * mswap N := by
  ext i j
  simp [mswap, Matrix.mul_apply, map_sum]

omit [Fintype ι] in
private theorem mswap_one : mswap (1 : Matrix ι ι Coef) = 1 := by
  unfold mswap
  exact Matrix.map_one _ (map_zero swapC) (map_one swapC)

private theorem cmap_eq_mapRange {f : Coef → Coef} (hf : f 0 = 0) (D : DOp ι) :
    cmap f D = Finsupp.mapRange (fun M : Matrix ι ι Coef => M.map f) (by ext i j; simp [hf]) D := by
  ext ab i j
  unfold cmap
  rw [Finsupp.sum_apply, Finsupp.mapRange_apply, Finsupp.sum]
  rw [Finset.sum_eq_single ab]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hab
    have h0 : D ab = 0 := by simpa using hab
    simp [h0, hf]

private theorem swapOp_eq (D : DOp ι) :
    swapOp D = Finsupp.mapDomain Prod.swap (Finsupp.mapRange mswap mswap_zero D) := by
  unfold swapOp
  rw [cmap_eq_mapRange (map_zero swapC)]
  rfl

private theorem swapOp_single (ab : ℕ × ℕ) (M : Matrix ι ι Coef) :
    swapOp (Finsupp.single ab M) = Finsupp.single ab.swap (mswap M) := by
  rw [swapOp_eq, Finsupp.mapRange_single, Finsupp.mapDomain_single]

private theorem swapOp_zero : swapOp (0 : DOp ι) = 0 := by
  rw [swapOp_eq, Finsupp.mapRange_zero, Finsupp.mapDomain_zero]

private theorem swapOp_add' (D D' : DOp ι) : swapOp (D + D') = swapOp D + swapOp D' := by
  simp only [swapOp_eq]
  rw [Finsupp.mapRange_add mswap_add, Finsupp.mapDomain_add]

private def swapOpHom : DOp ι →+ DOp ι where
  toFun := swapOp
  map_zero' := swapOp_zero
  map_add' := swapOp_add'

private theorem swapOpHom_apply (D : DOp ι) : swapOpHom D = swapOp D := rfl

private theorem swapOp_induction {P : DOp ι → Prop} (h0 : P 0) (hadd : ∀ D D', P D → P D' → P (D + D'))
    (hsingle : ∀ ab M, P (Finsupp.single ab M)) (D : DOp ι) : P D :=
  Finsupp.induction_linear D h0 hadd hsingle

private theorem swapOp_apply (D : DOp ι) (a b : ℕ) : swapOp D (a, b) = (D (b, a)).map swapC := by
  rw [swapOp_eq]
  exact (Finsupp.mapDomain_apply Prod.swap_injective _ (b, a)).trans (by rw [Finsupp.mapRange_apply]; rfl)

private theorem swapOp_swapOp (D : DOp ι) : swapOp (swapOp D) = D := by
  refine Finsupp.ext fun ab => ?_
  obtain ⟨a, b⟩ := ab
  rw [swapOp_apply, swapOp_apply]
  exact mswap_mswap (D (a, b))

private theorem swapOp_add (D D' : DOp ι) : swapOp (D + D') = swapOp D + swapOp D' := by
  exact swapOp_add' D D'

private theorem swapOp_smul (c : ℂ) (D : DOp ι) : swapOp (c • D) = c • swapOp D := by
  simp only [swapOp_eq]
  rw [Finsupp.mapRange_smul' c c D (mswap_smul c), Finsupp.mapDomain_smul]

private theorem swapOp_neg (D : DOp ι) : swapOp (-D) = -swapOp D := by
  exact map_neg swapOpHom D

private theorem swapOp_sum {α : Type*} (s : Finset α) (D : α → DOp ι) : swapOp (∑ a ∈ s, D a) = ∑ a ∈ s, swapOp (D a)
    := by
  exact map_sum swapOpHom D s

private theorem swapOp_one : swapOp (one : DOp ι) = one := by
  unfold one
  rw [swapOp_single, mswap_one]
  rfl

private theorem swapOp_d₁ : swapOp (d₁ : DOp ι) = d₂ := by
  unfold d₁ d₂
  rw [swapOp_single, mswap_one]
  rfl

private theorem swapOp_d₂ : swapOp (d₂ : DOp ι) = d₁ := by
  unfold d₁ d₂
  rw [swapOp_single, mswap_one]
  rfl

private theorem swapOp_cmul (C : Matrix ι ι Coef) (D : DOp ι) : swapOp (cmul C D) = cmul (C.map swapC) (swapOp D) := by
  refine Finsupp.ext fun ab => ?_
  obtain ⟨a, b⟩ := ab
  rw [swapOp_apply, cmul_apply, cmul_apply, swapOp_apply]
  exact mswap_mul C (D (b, a))

private theorem swapC_eul0 (p : Coef) : swapC (eul 0 p) = eul 1 (swapC p) := by
  simp only [eul, swapC, map_mul]
  rw [MvPolynomial.rename_X, ← MvPolynomial.pderiv_rename (Equiv.swap (0 : Fin 2) 1).injective]
  simp

private theorem swapC_eul1 (p : Coef) : swapC (eul 1 p) = eul 0 (swapC p) := by
  simp only [eul, swapC, map_mul]
  rw [MvPolynomial.rename_X, ← MvPolynomial.pderiv_rename (Equiv.swap (0 : Fin 2) 1).injective]
  simp

private theorem swapC_iterate_eul0 (n : ℕ) (p : Coef) : swapC ((eul 0)^[n] p) = (eul 1)^[n] (swapC p) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, swapC_eul0]

private theorem swapC_iterate_eul1 (n : ℕ) (p : Coef) : swapC ((eul 1)^[n] p) = (eul 0)^[n] (swapC p) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, swapC_eul1]

omit [Fintype ι] [DecidableEq ι] in
private theorem mswap_map_eul (i j : ℕ) (N : Matrix ι ι Coef) :
    mswap (N.map ((eul 0)^[i] ∘ (eul 1)^[j])) = (mswap N).map ((eul 1)^[i] ∘ (eul 0)^[j]) := by
  ext a b
  simp only [mswap, Matrix.map_apply, Function.comp_apply]
  rw [swapC_iterate_eul0, swapC_iterate_eul1]

private theorem iterate_eul_comm (i j : ℕ) : (eul 1)^[i] ∘ (eul 0)^[j] = (eul 0)^[j] ∘ (eul 1)^[i] :=
  ((Function.Commute.iterate_iterate (fun p => (eul_comm p).symm) i j)).comp_eq

omit [Fintype ι] [DecidableEq ι] in
private theorem map_zero_eul_iter (i j : ℕ) : (0 : Matrix ι ι Coef).map ((eul 0)^[i] ∘ (eul 1)^[j]) = 0 := by
  ext a b
  simp [iterate_eul_zero]

private theorem comp_single_single (ab cd : ℕ × ℕ) (M N : Matrix ι ι Coef) :
    comp (Finsupp.single ab M) (Finsupp.single cd N) =
      ∑ i ∈ Finset.range (ab.1 + 1), ∑ j ∈ Finset.range (ab.2 + 1),
        Finsupp.single (ab.1 - i + cd.1, ab.2 - j + cd.2)
          (((ab.1.choose i : ℕ) * (ab.2.choose j : ℕ) : ℂ) • (M * N.map ((eul 0)^[i] ∘ (eul 1)^[j]))) := by
  unfold comp
  rw [Finsupp.sum_single_index, Finsupp.sum_single_index]
  all_goals simp [Finsupp.sum, map_zero_eul_iter]

private theorem swapOp_comp_single_single (ab cd : ℕ × ℕ) (M N : Matrix ι ι Coef) :
    swapOp (comp (Finsupp.single ab M) (Finsupp.single cd N)) =
      comp (swapOp (Finsupp.single ab M)) (swapOp (Finsupp.single cd N)) := by
  rw [swapOp_single, swapOp_single, comp_single_single, comp_single_single, ← swapOpHom_apply]
  simp only [map_sum, swapOpHom_apply, swapOp_single, mswap_smul, mswap_mul, mswap_map_eul, Prod.swap_prod_mk,
    Prod.fst_swap, Prod.snd_swap]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [iterate_eul_comm, mul_comm]

private theorem swapOp_comp (D D' : DOp ι) : swapOp (comp D D') = comp (swapOp D) (swapOp D') := by
  induction D using swapOp_induction with
  | h0 => rw [zero_comp', swapOp_zero, zero_comp']
  | hadd D₁ D₂ h₁ h₂ => rw [add_comp, swapOp_add', h₁, h₂, swapOp_add', add_comp]
  | hsingle ab M =>
    induction D' using swapOp_induction with
    | h0 => rw [comp_zero', swapOp_zero, comp_zero']
    | hadd E₁ E₂ h₁ h₂ => rw [comp_add, swapOp_add', h₁, h₂, swapOp_add', comp_add]
    | hsingle cd N => exact swapOp_comp_single_single ab cd M N

private theorem swapOp_npow (D : DOp ι) (m : ℕ) : swapOp (npow D m) = npow (swapOp D) m := by
  induction m with
  | zero => exact swapOp_one
  | succ m ih =>
    rw [npow_succ', npow_succ', swapOp_comp, ih]

private theorem swapOp_polyOp {N : ℕ} (a : Fin (N + 1) → ℂ) (D : DOp ι) : swapOp (polyOp a D) = polyOp a (swapOp D) :=
    by
  unfold polyOp
  rw [swapOp_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [swapOp_smul, swapOp_npow]

private theorem HasOrder.swapOp {D : DOp ι} {k : ℕ} (h : HasOrder D k) : HasOrder (swapOp D) k := by
  intro ab hab
  rw [swapOp_eq, Finsupp.mapDomain_support_of_injective Prod.swap_injective] at hab
  obtain ⟨cd, hcd, rfl⟩ := Finset.mem_image.1 hab
  have hk := h cd (Finsupp.support_mapRange hcd)
  rw [Prod.fst_swap, Prod.snd_swap, add_comm]
  exact hk

omit [Fintype ι] in
private theorem scal_map_swapC (c : ℂ) : (scal c : Matrix ι ι Coef).map swapC = scal c := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [scal]
  · simp [scal, hij]

private theorem cmap_apply_of_zero {f : Coef → Coef} (hf : f 0 = 0) (D : DOp ι) (ab : ℕ × ℕ) :
    cmap f D ab = (D ab).map f := by
  rw [cmap_eq_mapRange hf, Finsupp.mapRange_apply]

private theorem cmap_swapOp_of_comm {f g : Coef → Coef} (hf : f 0 = 0) (hg : g 0 = 0)
    (hfg : ∀ p, f (swapC p) = swapC (g p)) (D : DOp ι) : cmap f (swapOp D) = swapOp (cmap g D) := by
  refine Finsupp.ext fun ab => ?_
  obtain ⟨a, b⟩ := ab
  rw [cmap_apply_of_zero hf, swapOp_apply, swapOp_apply, cmap_apply_of_zero hg]
  exact Matrix.ext fun i j => hfg _

private theorem cmap_killX0_swapOp (D : DOp ι) : cmap killX0 (swapOp D) = swapOp (cmap killX1 D) := by
  exact cmap_swapOp_of_comm (map_zero killX0) (map_zero killX1) killX0_swapC D

private theorem cmap_const_swapOp (D : DOp ι) :
    cmap (fun p => C (MvPolynomial.constantCoeff p)) (swapOp D) =
      swapOp (cmap (fun p => C (MvPolynomial.constantCoeff p)) D) := by
  exact cmap_swapOp_of_comm (by simp) (by simp) (fun p => by rw [constantCoeff_swapC, swapC_C]) D

omit [Fintype ι] [DecidableEq ι] in
private theorem d1_transpose (G : ℝ → ℝ → (ι → ℂ)) : d1 (fun s₁ s₂ => G s₂ s₁) = fun s₁ s₂ => d2 G s₂ s₁ := rfl

omit [Fintype ι] [DecidableEq ι] in
private theorem d2_transpose (G : ℝ → ℝ → (ι → ℂ)) : d2 (fun s₁ s₂ => G s₂ s₁) = fun s₁ s₂ => d1 G s₂ s₁ := rfl

omit [Fintype ι] [DecidableEq ι] in
private theorem iterate_d1_transpose (n : ℕ) (G : ℝ → ℝ → (ι → ℂ)) :
    (d1^[n]) (fun s₁ s₂ => G s₂ s₁) = fun s₁ s₂ => (d2^[n]) G s₂ s₁ := by
  induction n generalizing G with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, d1_transpose, ih]

omit [Fintype ι] [DecidableEq ι] in
private theorem iterate_d2_transpose (n : ℕ) (G : ℝ → ℝ → (ι → ℂ)) :
    (d2^[n]) (fun s₁ s₂ => G s₂ s₁) = fun s₁ s₂ => (d1^[n]) G s₂ s₁ := by
  induction n generalizing G with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, d2_transpose, ih]

private theorem dIter_transpose {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) (a b : ℕ) (t₁ t₂ : ℝ) :
    dIter b a (fun s₁ s₂ => G s₂ s₁) t₁ t₂ = dIter a b G t₂ t₁ := by
  unfold dIter
  rw [iterate_d2_transpose, iterate_d1_transpose]
  show (d2^[b]) ((d1^[a]) G) t₂ t₁ = (d1^[a]) ((d2^[b]) G) t₂ t₁
  rw [iterate_d2_iterate_d1 hG a b]

private theorem mev_mswap (M : Matrix ι ι Coef) (t₁ t₂ : ℝ) : mev (mswap M) t₁ t₂ = mev M t₂ t₁ := by
  ext i j
  simp only [mev, mswap, Matrix.map_apply]
  exact ev_swapC (M i j) t₁ t₂

private theorem apply_swapOp (D : DOp ι) {G : ℝ → ℝ → (ι → ℂ)} (hG : Smooth2 G) (t₁ t₂ : ℝ) :
    apply (swapOp D) (fun s₁ s₂ => G s₂ s₁) t₁ t₂ = apply D G t₂ t₁ := by
  induction D using swapOp_induction with
  | h0 => rw [swapOp_zero]; simp [DOp.apply]
  | hadd D D' hD hD' => simp only [swapOp_add', apply_add, hD, hD']
  | hsingle ab M =>
    rw [swapOp_single, apply_single, apply_single]
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [mev_mswap, dIter_transpose hG]

omit [Fintype ι] [DecidableEq ι] in
private theorem map_swapC_zero : (0 : Matrix ι ι Coef).map swapC = 0 := mswap_zero

omit [Fintype ι] in
private theorem neg_scal (c : ℂ) : -(scal c : Matrix ι ι Coef) = scal (-c) := by
  ext i j
  by_cases hij : i = j <;> simp [scal, hij]

private theorem HasOrder.neg' {D : DOp ι} {k : ℕ} (h : HasOrder D k) : HasOrder (-D) k := by
  intro ab hab
  exact h ab (by simpa using hab)

private theorem IsCasimirPair.swapOp {Ω₂ Ω₃ : DOp ι} (h : IsCasimirPair Ω₂ Ω₃) : IsCasimirPair (swapOp Ω₂) (-swapOp Ω₃)
    := by
  refine ⟨h.ord₂.swapOp, h.ord₃.swapOp.neg', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [swapOp_apply, h.top₀₂, scal_map_swapC]
  · rw [swapOp_apply, h.top₁₁, scal_map_swapC]
  · rw [swapOp_apply, h.top₂₀, scal_map_swapC]
  · rw [Finsupp.neg_apply, swapOp_apply, h.top₀₃, map_swapC_zero, neg_zero]
  · rw [Finsupp.neg_apply, swapOp_apply, h.top₁₂, scal_map_swapC, neg_scal, neg_neg]
  · rw [Finsupp.neg_apply, swapOp_apply, h.top₂₁, scal_map_swapC, neg_scal]
  · rw [Finsupp.neg_apply, swapOp_apply, h.top₃₀, map_swapC_zero, neg_zero]
  · rw [comp_neg', neg_comp', ← swapOp_comp, ← swapOp_comp, h.comm]

end DOp
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

end Swap
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

end HolonomicD2
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

namespace RealGL3

open Matrix HolonomicD2 HolonomicD2.DOp

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Words

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private def rDm : (ℓ : ℕ) → (Fin ℓ → M3) → (M3 → V) → M3 → V
  | 0, _, F => F
  | ℓ + 1, w, F => rD (w 0) (rDm ℓ (Fin.tail w) F)

private def rDw (ℓ : ℕ) (w : Fin ℓ → Fin 3 × Fin 3) (F : M3 → V) : M3 → V := rDm ℓ (fun p => E (w p).1 (w p).2) F

private def rDl (w : List (Fin 3 × Fin 3)) (F : M3 → V) : M3 → V := List.foldr (fun ab G => rD (E ab.1 ab.2) G) F w

private theorem rDl_ofFn (ℓ : ℕ) (w : Fin ℓ → Fin 3 × Fin 3) (F : M3 → V) : rDl (List.ofFn w) F = rDw ℓ w F := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    rw [List.ofFn_succ]
    exact congrArg (rD (E (w 0).1 (w 0).2)) (ih (Fin.tail w))

private theorem contDiffOn_rDm (ℓ : ℕ) (w : Fin ℓ → M3) {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) :
    ContDiffOn ℝ (⊤ : ℕ∞) (rDm ℓ w F) GLs := by
  induction ℓ with
  | zero => exact hF
  | succ ℓ ih => exact contDiffOn_rD (w 0) (ih (Fin.tail w))

section WordFurniture

private theorem differentiableAt_of_contDiffOn_GLs {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {x : M3}
    (hx : x ∈ GLs) : DifferentiableAt ℝ F x :=
  (hF.differentiableOn (by simp)).differentiableAt (isOpen_GLs.mem_nhds hx)

private theorem rDm_zero (w : Fin 0 → M3) (F : M3 → V) : rDm 0 w F = F := rfl

private theorem rDm_succ (ℓ : ℕ) (w : Fin (ℓ + 1) → M3) (F : M3 → V) :
    rDm (ℓ + 1) w F = rD (w 0) (rDm ℓ (Fin.tail w) F) := rfl

private theorem rDm_update_add_eqOn (ℓ : ℕ) (w : Fin ℓ → M3) (p : Fin ℓ) (Y Y' : M3) {F : M3 → V}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) :
    Set.EqOn (rDm ℓ (Function.update w p (Y + Y')) F)
      (rDm ℓ (Function.update w p Y) F + rDm ℓ (Function.update w p Y') F) GLs := by
  induction ℓ with
  | zero => exact p.elim0
  | succ ℓ ih =>
    intro x hx
    induction p using Fin.cases with
    | zero =>
      simp only [rDm_succ, Function.update_self, Fin.tail_update_zero, Pi.add_apply]
      exact rD_add_dir Y Y' (differentiableAt_of_contDiffOn_GLs (contDiffOn_rDm ℓ _ hF) hx)
    | succ q =>
      simp only [rDm_succ, Function.update_of_ne (Fin.succ_ne_zero q).symm, Fin.tail_update_succ, Pi.add_apply]
      rw [rD_congr_of_eqOn (w 0) (ih (Fin.tail w) q) hx]
      exact rD_add (w 0) (differentiableAt_of_contDiffOn_GLs (contDiffOn_rDm ℓ _ hF) hx)
        (differentiableAt_of_contDiffOn_GLs (contDiffOn_rDm ℓ _ hF) hx)

private theorem rDm_update_smul_eqOn (ℓ : ℕ) (w : Fin ℓ → M3) (p : Fin ℓ) (c : ℝ) (Y : M3) {F : M3 → V}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) :
    Set.EqOn (rDm ℓ (Function.update w p (c • Y)) F) (c • rDm ℓ (Function.update w p Y) F) GLs := by
  induction ℓ with
  | zero => exact p.elim0
  | succ ℓ ih =>
    intro x hx
    induction p using Fin.cases with
    | zero =>
      simp only [rDm_succ, Function.update_self, Fin.tail_update_zero, Pi.smul_apply]
      exact rD_smul_dir c Y (differentiableAt_of_contDiffOn_GLs (contDiffOn_rDm ℓ _ hF) hx)
    | succ q =>
      simp only [rDm_succ, Function.update_of_ne (Fin.succ_ne_zero q).symm, Fin.tail_update_succ, Pi.smul_apply]
      rw [rD_congr_of_eqOn (w 0) (ih (Fin.tail w) q) hx]
      exact rD_const_smul (w 0) c (differentiableAt_of_contDiffOn_GLs (contDiffOn_rDm ℓ _ hF) hx)

private theorem rDm_clm_comp_eqOn {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V'] (L : V →L[ℝ] V') (ℓ : ℕ)
    (w : Fin ℓ → M3) {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) :
    Set.EqOn (rDm ℓ w (fun y => L (F y))) (fun y => L (rDm ℓ w F y)) GLs := by
  induction ℓ with
  | zero => intro x _; rfl
  | succ ℓ ih =>
    intro x hx
    simp only [rDm_succ]
    rw [rD_congr_of_eqOn (w 0) (ih (Fin.tail w)) hx]
    exact rD_clm_comp L (w 0) (differentiableAt_of_contDiffOn_GLs (contDiffOn_rDm ℓ _ hF) hx)

end WordFurniture
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

private theorem rDm_update_add (ℓ : ℕ) (w : Fin ℓ → M3) (p : Fin ℓ) (Y Y' : M3) {F : M3 → V}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {x : M3} (hx : x ∈ GLs) :
    rDm ℓ (Function.update w p (Y + Y')) F x =
      rDm ℓ (Function.update w p Y) F x + rDm ℓ (Function.update w p Y') F x := by
  exact rDm_update_add_eqOn ℓ w p Y Y' hF hx

private theorem rDm_update_smul (ℓ : ℕ) (w : Fin ℓ → M3) (p : Fin ℓ) (c : ℝ) (Y : M3) {F : M3 → V}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {x : M3} (hx : x ∈ GLs) :
    rDm ℓ (Function.update w p (c • Y)) F x = c • rDm ℓ (Function.update w p Y) F x := by
  exact rDm_update_smul_eqOn ℓ w p c Y hF hx

section WordLaws

private theorem rD_rDm_eqOn (Z : M3) (ℓ : ℕ) (w : Fin ℓ → M3) {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) :
    Set.EqOn (rD Z (rDm ℓ w F))
      (rDm ℓ w (rD Z F) + fun x => ∑ p : Fin ℓ, rDm ℓ (Function.update w p (Z * w p - w p * Z)) F x) GLs := by
  induction ℓ with
  | zero => intro x _; simp [rDm_zero]
  | succ ℓ ih =>
    intro x hx
    have hG := contDiffOn_rDm ℓ (Fin.tail w) hF
    have hcomm := rD_comm Z (w 0) hG hx
    rw [sub_eq_iff_eq_add] at hcomm
    simp only [rDm_succ, Pi.add_apply]
    rw [hcomm, rD_congr_of_eqOn (w 0) (ih (Fin.tail w)) hx, rD_add (w 0)
        (differentiableAt_of_contDiffOn_GLs (contDiffOn_rDm ℓ _ (contDiffOn_rD Z hF)) hx)
        (differentiableAt_of_contDiffOn_GLs (ContDiffOn.sum fun p _ => contDiffOn_rDm ℓ _ hF) hx),
      rD_sum Finset.univ (w 0) fun p _ => differentiableAt_of_contDiffOn_GLs (contDiffOn_rDm ℓ _ hF) hx,
      Fin.sum_univ_succ]
    simp only [Function.update_self, Fin.tail_update_zero, Function.update_of_ne (Fin.succ_ne_zero _).symm,
      Fin.tail_update_succ]
    abel

private theorem eq_sum_entries_smul_E (X : M3) : X = ∑ ab : Fin 3 × Fin 3, X ab.1 ab.2 • E ab.1 ab.2 := by
  ext i j
  simp [Matrix.sum_apply, E, Matrix.single_apply, Fintype.sum_prod_type, ite_and]

private theorem rDw_succ (ℓ : ℕ) (ab : Fin 3 × Fin 3) (e : Fin ℓ → Fin 3 × Fin 3) (F : M3 → V) :
    rDw (ℓ + 1) (Fin.cons ab e) F = rD (E ab.1 ab.2) (rDw ℓ e F) := by
  simp only [rDw, rDm_succ, Fin.cons_zero]
  congr 1

private theorem contDiffOn_rDw (ℓ : ℕ) (e : Fin ℓ → Fin 3 × Fin 3) {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) :
    ContDiffOn ℝ (⊤ : ℕ∞) (rDw ℓ e F) GLs := contDiffOn_rDm ℓ _ hF

private theorem rDm_eq_sum_rDw_eqOn (ℓ : ℕ) (w : Fin ℓ → M3) {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) :
    Set.EqOn (rDm ℓ w F) (fun x => ∑ e : Fin ℓ → Fin 3 × Fin 3, (∏ p, w p (e p).1 (e p).2) • rDw ℓ e F x) GLs := by
  induction ℓ with
  | zero =>
    intro x _
    simp [rDm_zero, rDw]
  | succ ℓ ih =>
    intro x hx
    have hG := contDiffOn_rDm ℓ (Fin.tail w) hF
    have hGx := differentiableAt_of_contDiffOn_GLs hG hx

    rw [rDm_succ, eq_sum_entries_smul_E (w 0), rD_sum_dir Finset.univ _ hGx]
    simp_rw [rD_smul_dir _ _ hGx]
    conv_rhs => rw [← (Fin.consEquiv fun _ => Fin 3 × Fin 3).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [rD_congr_of_eqOn _ (ih (Fin.tail w)) hx, rD_sum Finset.univ _ fun e _ =>
      differentiableAt_of_contDiffOn_GLs ((contDiffOn_rDw ℓ e hF).const_smul _) hx, Finset.smul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    erw [rD_const_smul _ _ (differentiableAt_of_contDiffOn_GLs (contDiffOn_rDw ℓ e hF) hx)]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, rDw_succ, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Fin.tail_def, smul_smul]

end WordLaws
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

private theorem rDm_eq_sum_rDw (ℓ : ℕ) (w : Fin ℓ → M3) {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {x : M3}
    (hx : x ∈ GLs) :
    rDm ℓ w F x = ∑ e : Fin ℓ → Fin 3 × Fin 3, (∏ p, w p (e p).1 (e p).2) • rDw ℓ e F x := by
  exact rDm_eq_sum_rDw_eqOn ℓ w hF hx

private theorem rD_rDm (Z : M3) (ℓ : ℕ) (w : Fin ℓ → M3) {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {x : M3}
    (hx : x ∈ GLs) :
    rD Z (rDm ℓ w F) x = rDm ℓ w (rD Z F) x + ∑ p : Fin ℓ, rDm ℓ (Function.update w p (Z * w p - w p * Z)) F x := by
  exact rD_rDm_eqOn Z ℓ w hF hx

private theorem rDm_clm_comp {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V'] (L : V →L[ℝ] V') (ℓ : ℕ)
    (w : Fin ℓ → M3) {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {x : M3} (hx : x ∈ GLs) :
    rDm ℓ w (fun y => L (F y)) x = L (rDm ℓ w F x) := by
  exact rDm_clm_comp_eqOn L ℓ w hF hx

private theorem rDm_comp_mul_left (ℓ : ℕ) (w : Fin ℓ → M3) (g : M3) (F : M3 → V) :
    rDm ℓ w (fun y => F (g * y)) = fun y => rDm ℓ w F (g * y) := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    show rD (w 0) (rDm ℓ (Fin.tail w) fun y => F (g * y)) = fun y => rD (w 0) (rDm ℓ (Fin.tail w) F) (g * y)
    rw [ih (Fin.tail w), rD_comp_mul_left]

end Words
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

section Ad

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem inv_mul_cancel_of_mem_GLs {g : M3} (hg : g ∈ GLs) : g⁻¹ * g = 1 :=
  Matrix.nonsing_inv_mul g (isUnit_iff_ne_zero.2 hg)

private theorem mul_inv_cancel_of_mem_GLs {g : M3} (hg : g ∈ GLs) : g * g⁻¹ = 1 :=
  Matrix.mul_nonsing_inv g (isUnit_iff_ne_zero.2 hg)

private theorem inv_mul_conj_mul_of_mem_GLs {g : M3} (hg : g ∈ GLs) (Y : M3) : g⁻¹ * (g * Y * g⁻¹) * g = Y := by
  calc g⁻¹ * (g * Y * g⁻¹) * g = (g⁻¹ * g) * Y * (g⁻¹ * g) := by simp only [Matrix.mul_assoc]
    _ = Y := by rw [inv_mul_cancel_of_mem_GLs hg, Matrix.one_mul, Matrix.mul_one]

private theorem rD_apply_mul_right (Y : M3) {g : M3} (hg : g ∈ GLs) (F : M3 → V) (x : M3) :
    rD Y F (x * g) = rD (g * Y * g⁻¹) (fun y => F (y * g)) x := by
  rw [rD_comp_mul_right _ hg, inv_mul_conj_mul_of_mem_GLs hg]

private theorem rDm_apply_mul_right (ℓ : ℕ) (w : Fin ℓ → M3) {g : M3} (hg : g ∈ GLs) (F : M3 → V) (x : M3) :
    rDm ℓ w F (x * g) = rDm ℓ (fun p => g * w p * g⁻¹) (fun y => F (y * g)) x := by
  induction ℓ generalizing F x with
  | zero => rfl
  | succ ℓ ih =>
    show rD (w 0) (rDm ℓ (Fin.tail w) F) (x * g) = rD (g * w 0 * g⁻¹) (rDm ℓ (fun p => g * Fin.tail w p * g⁻¹)
      (fun y => F (y * g))) x
    rw [rD_apply_mul_right _ hg]
    congr 1
    funext y
    exact ih (Fin.tail w) F y

private theorem contDiffOn_comp_mul_right {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {g : M3} (hg : g ∈ GLs) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => F (y * g)) GLs := by
  have hmul : ContDiff ℝ (⊤ : ℕ∞) (fun y : M3 => y * g) :=
    (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ g)).contDiff
  exact hF.comp hmul.contDiffOn fun _ hy => mul_mem_GLs hy hg

private def ad (g : M3) : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℝ := fun ab cd => (g * E ab.1 ab.2 * g⁻¹) cd.1 cd.2

private def adPow (ℓ : ℕ) (g : M3) : Matrix (Fin ℓ → Fin 3 × Fin 3) (Fin ℓ → Fin 3 × Fin 3) ℝ :=
  fun v e => ∏ p, ad g (v p) (e p)

private theorem adPow_apply (ℓ : ℕ) (g : M3) (v e : Fin ℓ → Fin 3 × Fin 3) : adPow ℓ g v e = ∏ p, ad g (v p) (e p) :=
    rfl

private theorem rDw_apply_mul_right_eq_sum (ℓ : ℕ) (v : Fin ℓ → Fin 3 × Fin 3) {F : M3 → V}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {g : M3} (hg : g ∈ GLs) {x : M3} (hx : x ∈ GLs) :
    rDw ℓ v F (x * g) = ∑ e : Fin ℓ → Fin 3 × Fin 3, adPow ℓ g v e • rDw ℓ e (fun y => F (y * g)) x := by
  show rDm ℓ (fun p => E (v p).1 (v p).2) F (x * g) = _
  rw [rDm_apply_mul_right _ _ hg, rDm_eq_sum_rDw _ _ (contDiffOn_comp_mul_right hF hg) hx]
  rfl

private theorem eq_sum_entry_smul_E (Y : M3) : Y = ∑ cd : Fin 3 × Fin 3, Y cd.1 cd.2 • E cd.1 cd.2 := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [E, Matrix.smul_single, smul_eq_mul, mul_one]

private theorem ad_one : ad 1 = 1 := by
  ext ab cd
  by_cases h : ab = cd
  · subst h
    simp [ad, E]
  · have h' : ¬(ab.1 = cd.1 ∧ ab.2 = cd.2) := fun h2 => h (Prod.ext h2.1 h2.2)
    simp [ad, E, h, h']

private theorem ad_mul (g h : M3) : ad (g * h) = ad h * ad g := by
  ext ab cd
  have hexp : g * (h * E ab.1 ab.2 * h⁻¹) * g⁻¹ =
      ∑ ef : Fin 3 × Fin 3, ad h ab ef • (g * E ef.1 ef.2 * g⁻¹) := by
    conv_lhs => rw [eq_sum_entry_smul_E (h * E ab.1 ab.2 * h⁻¹)]
    simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul]
    rfl
  have : ad (g * h) ab cd = (g * (h * E ab.1 ab.2 * h⁻¹) * g⁻¹) cd.1 cd.2 := by
    simp only [ad, Matrix.mul_inv_rev, Matrix.mul_assoc]
  rw [this, hexp, Matrix.sum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun ef _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  rfl

private theorem adPow_one (ℓ : ℕ) : adPow ℓ (1 : M3) = 1 := by
  ext v e
  simp only [adPow_apply, ad_one, Matrix.one_apply]
  by_cases hve : v = e
  · subst hve
    simp
  · obtain ⟨p, hp⟩ : ∃ p, v p ≠ e p := by
      by_contra hcon
      push Not at hcon
      exact hve (funext hcon)
    rw [if_neg hve]
    exact Finset.prod_eq_zero (Finset.mem_univ p) (by simp [hp])

private theorem adPow_mul (ℓ : ℕ) (g h : M3) : adPow ℓ (g * h) = adPow ℓ h * adPow ℓ g := by
  ext v e
  rw [Matrix.mul_apply]
  simp only [adPow_apply, ad_mul, Matrix.mul_apply]
  rw [Fintype.prod_sum fun p f => ad h (v p) f * ad g f (e p)]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.prod_mul_distrib]

private theorem continuousOn_inv_GLs : ContinuousOn (fun g : M3 => g⁻¹) GLs := by
  refine continuousOn_of_forall_continuousAt fun g hg => ?_
  refine continuousAt_matrix_inv g ?_
  simpa using NormedRing.inverse_continuousAt (Units.mk0 g.det hg)

private theorem continuousOn_ad_entry (ab cd : Fin 3 × Fin 3) : ContinuousOn (fun g : M3 => ad g ab cd) GLs := by
  have h1 : ContinuousOn (fun g : M3 => g * E ab.1 ab.2 * g⁻¹) GLs :=
    (continuousOn_id.mul continuousOn_const).mul continuousOn_inv_GLs
  exact (continuous_id.matrix_elem cd.1 cd.2).comp_continuousOn h1

private theorem continuousOn_adPow_entry (ℓ : ℕ) (v e : Fin ℓ → Fin 3 × Fin 3) :
    ContinuousOn (fun g : M3 => adPow ℓ g v e) GLs := by
  simp only [adPow_apply]
  exact continuousOn_finset_prod _ fun p _ => continuousOn_ad_entry (v p) (e p)

end Ad
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

private def uniChar (n : M3) : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((n 0 1 + n 1 2 : ℝ) : ℂ))

private def twoPiI : ℂ := 2 * Real.pi * Complex.I

private theorem uniChar_mul {n n' : M3} (hn : IsUpperUni n) (hn' : IsUpperUni n') :
    uniChar (n * n') = uniChar n * uniChar n' := by
  have h01 : (n * n') 0 1 = n 0 1 + n' 0 1 := by
    rw [Matrix.mul_apply, Fin.sum_univ_three, hn.2 0, hn'.2 1, hn'.1 2 1 (by decide)]
    ring
  have h12 : (n * n') 1 2 = n 1 2 + n' 1 2 := by
    rw [Matrix.mul_apply, Fin.sum_univ_three, hn.1 1 0 (by decide), hn.2 1, hn'.2 2]
    ring
  rw [uniChar, uniChar, uniChar, ← Complex.exp_add, h01, h12]
  congr 1
  push_cast
  ring

private theorem uniChar_one : uniChar 1 = 1 := by
  simp [uniChar]

section Transport

variable {n : ℕ}

section TransportFurniture

private theorem rDm_congr_GLs {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (ℓ : ℕ) (w : Fin ℓ → M3)
    {F G : M3 → V} (h : Set.EqOn F G GLs) : Set.EqOn (rDm ℓ w F) (rDm ℓ w G) GLs := by
  induction ℓ with
  | zero => exact h
  | succ ℓ ih => intro x hx; simp only [rDm_succ]; exact rD_congr_of_eqOn (w 0) (ih (Fin.tail w)) hx

private theorem rD_smul_complex (X : M3) (c : ℂ) (F : M3 → (Fin n → ℂ)) (x : M3) :
    rD X (fun y => c • F y) x = c • rD X F x := by
  unfold rD
  exact deriv_fun_const_smul_field c fun s : ℝ => F (x * (1 + s • X))

private theorem rDm_smul_complex (ℓ : ℕ) (w : Fin ℓ → M3) (c : ℂ) (F : M3 → (Fin n → ℂ)) :
    Set.EqOn (rDm ℓ w (fun y => c • F y)) (fun y => c • rDm ℓ w F y) GLs := by
  induction ℓ with
  | zero => intro x _; rfl
  | succ ℓ ih =>
    intro x hx
    simp only [rDm_succ]
    rw [rD_congr_of_eqOn (w 0) (ih (Fin.tail w)) hx]
    exact rD_smul_complex (w 0) c _ x

private theorem rDm_sum_fun {α : Type*} (s : Finset α) (ℓ : ℕ) (w : Fin ℓ → M3) {F : α → M3 → (Fin n → ℂ)}
    (hF : ∀ a ∈ s, ContDiffOn ℝ (⊤ : ℕ∞) (F a) GLs) :
    Set.EqOn (rDm ℓ w (fun y => ∑ a ∈ s, F a y)) (fun y => ∑ a ∈ s, rDm ℓ w (F a) y) GLs := by
  induction ℓ with
  | zero => intro x _; rfl
  | succ ℓ ih =>
    intro x hx
    simp only [rDm_succ]
    rw [rD_congr_of_eqOn (w 0) (ih (Fin.tail w)) hx]
    exact rD_sum s (w 0) fun a ha => differentiableAt_of_contDiffOn_GLs (contDiffOn_rDm ℓ _ (hF a ha)) hx

private theorem contDiffOn_mulVec_component (S : Matrix (Fin n) (Fin n) ℂ) {W : M3 → (Fin n → ℂ)}
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) W GLs) (i j : Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => S i j • W y) GLs := by
  refine contDiffOn_pi.2 fun k => ?_
  exact contDiffOn_const.mul (contDiffOn_pi.1 hW k)

private theorem mulVec_eq_sum (S : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    S *ᵥ v = ∑ j, v j • fun i => S i j := by
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

private theorem contDiffOn_proj_smul_const {W : M3 → (Fin n → ℂ)} (hW : ContDiffOn ℝ (⊤ : ℕ∞) W GLs) (j : Fin n)
    (v : Fin n → ℂ) : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => W y j • v) GLs := by
  refine contDiffOn_pi.2 fun k => ?_
  exact (contDiffOn_pi.1 hW j).mul contDiffOn_const

private theorem rDm_proj (ℓ : ℕ) (w : Fin ℓ → M3) {W : M3 → (Fin n → ℂ)} (hW : ContDiffOn ℝ (⊤ : ℕ∞) W GLs)
    (k : Fin n) {x : M3} (hx : x ∈ GLs) : rDm ℓ w (fun y => W y k) x = rDm ℓ w W x k :=
  rDm_clm_comp_eqOn (ContinuousLinearMap.proj k) ℓ w hW hx

private theorem rDm_mul_const (ℓ : ℕ) (w : Fin ℓ → M3) {f : M3 → ℂ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f GLs) (c : ℂ)
    {x : M3} (hx : x ∈ GLs) : rDm ℓ w (fun y => f y * c) x = rDm ℓ w f x * c := by
  have h := rDm_clm_comp_eqOn (ContinuousLinearMap.mul ℝ ℂ c) ℓ w hf hx
  simp only [ContinuousLinearMap.mul_apply'] at h
  rw [mul_comm, ← h]
  congr 1
  funext y
  ring

private theorem rDm_proj_smul_const (ℓ : ℕ) (w : Fin ℓ → M3) {W : M3 → (Fin n → ℂ)}
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) W GLs) (j : Fin n) (v : Fin n → ℂ) :
    Set.EqOn (rDm ℓ w (fun y => W y j • v)) (fun y => rDm ℓ w W y j • v) GLs := by
  intro x hx
  funext k
  rw [← rDm_proj ℓ w (contDiffOn_proj_smul_const hW j v) k hx]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [rDm_mul_const ℓ w (contDiffOn_pi.1 hW j) (v k) hx, rDm_proj ℓ w hW j hx]

private theorem rDm_mulVec (ℓ : ℕ) (w : Fin ℓ → M3) (S : Matrix (Fin n) (Fin n) ℂ) {W : M3 → (Fin n → ℂ)}
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) W GLs) :
    Set.EqOn (rDm ℓ w (fun y => S *ᵥ W y)) (fun y => S *ᵥ rDm ℓ w W y) GLs := by
  intro x hx
  simp only [mulVec_eq_sum]
  rw [rDm_sum_fun Finset.univ ℓ w (fun j _ => contDiffOn_proj_smul_const hW j _) hx]
  exact Finset.sum_congr rfl fun j _ => rDm_proj_smul_const ℓ w hW j _ hx

private theorem rDm_update_zero (ℓ : ℕ) (w : Fin ℓ → M3) (p : Fin ℓ) {F : M3 → (Fin n → ℂ)}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {x : M3} (hx : x ∈ GLs) : rDm ℓ (Function.update w p 0) F x = 0 := by
  have h := rDm_update_smul_eqOn ℓ w p 0 (w p) hF hx
  rw [zero_smul] at h
  rw [h, Pi.smul_apply, zero_smul]

end TransportFurniture
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

private theorem rDm_uni {W : M3 → (Fin n → ℂ)}
    (hN : ∀ n' x : M3, IsUpperUni n' → x ∈ GLs → W (n' * x) = uniChar n' • W x)
    (ℓ : ℕ) (w : Fin ℓ → M3) {n' x : M3} (hn' : IsUpperUni n') (hx : x ∈ GLs) :
    rDm ℓ w W (n' * x) = uniChar n' • rDm ℓ w W x := by
  have h1 : Set.EqOn (fun y => W (n' * y)) (fun y => uniChar n' • W y) GLs := fun y hy => hN n' y hn' hy
  rw [← congrFun (rDm_comp_mul_left ℓ w n' W) x, rDm_congr_GLs ℓ w h1 hx]
  exact rDm_smul_complex ℓ w (uniChar n') W hx

private theorem rDm_centre {W : M3 → (Fin n → ℂ)} (hW : ContDiffOn ℝ (⊤ : ℕ∞) W GLs) {cω : ℂ}
    (hZ : ∀ x ∈ GLs, rD 1 W x = cω • W x) (ℓ : ℕ) (w : Fin ℓ → M3) {x : M3} (hx : x ∈ GLs) :
    rD 1 (rDm ℓ w W) x = cω • rDm ℓ w W x := by
  rw [rD_rDm_eqOn 1 ℓ w hW hx, Pi.add_apply]
  have hz : ∀ p : Fin ℓ, rDm ℓ (Function.update w p (1 * w p - w p * 1)) W x = 0 := fun p => by
    rw [one_mul, mul_one, sub_self]; exact rDm_update_zero ℓ w p hW hx
  simp only [hz, Finset.sum_const_zero, add_zero]
  rw [rDm_congr_GLs ℓ w (fun y hy => hZ y hy) hx]
  exact rDm_smul_complex ℓ w cω W hx

section TorusFurniture

private theorem torus_mul_E00 (y z : ℝ) : torus y z * E 0 0 = (y * z) • E 0 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [torus, E, Matrix.mul_apply, Matrix.single_apply]

private theorem torus_mul_E11 (y z : ℝ) : torus y z * E 1 1 = z • E 1 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [torus, E, Matrix.mul_apply, Matrix.single_apply]

private theorem torus_mul_E22 (y z : ℝ) : torus y z * E 2 2 = E 2 2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [torus, E, Matrix.mul_apply, Matrix.single_apply]

private theorem torus_eq_sum (y z : ℝ) : torus y z = (y * z) • E 0 0 + z • E 1 1 + E 2 2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [torus, E]

private theorem torus_exp_mem (t₁ t₂ : ℝ) : torus (Real.exp t₁) (Real.exp t₂) ∈ GLs :=
  torus_mem_GLs (Real.exp_pos t₁) (Real.exp_pos t₂)

private theorem hasDerivAt_torus_left (t₁ z : ℝ) :
    HasDerivAt (fun s => torus (Real.exp s) z) (Real.exp t₁ • (z • E 0 0)) t₁ := by
  have hf : (fun s => torus (Real.exp s) z) = fun s => Real.exp s • (z • E 0 0) + (z • E 1 1 + E 2 2) := by
    funext s; rw [torus_eq_sum, smul_smul, add_assoc]
  rw [hf]
  exact ((Real.hasDerivAt_exp t₁).smul_const (z • E 0 0)).add_const _

private theorem hasDerivAt_torus_right (y t₂ : ℝ) :
    HasDerivAt (fun s => torus y (Real.exp s)) (Real.exp t₂ • (y • E 0 0 + E 1 1)) t₂ := by
  have hf : (fun s => torus y (Real.exp s)) = fun s => Real.exp s • (y • E 0 0 + E 1 1) + E 2 2 := by
    funext s; rw [torus_eq_sum, smul_add, smul_smul, mul_comm]
  rw [hf]
  exact ((Real.hasDerivAt_exp t₂).smul_const (y • E 0 0 + E 1 1)).add_const _

private theorem deriv_torus_left {G : M3 → (Fin n → ℂ)} (hG : ContDiffOn ℝ (⊤ : ℕ∞) G GLs) (t₁ t₂ : ℝ) :
    deriv (fun s => G (torus (Real.exp s) (Real.exp t₂))) t₁ =
      fderiv ℝ G (torus (Real.exp t₁) (Real.exp t₂)) ((Real.exp t₁ * Real.exp t₂) • E 0 0) := by
  have hd := differentiableAt_of_contDiffOn_GLs hG (torus_exp_mem t₁ t₂)
  have h : HasDerivAt (fun s => G (torus (Real.exp s) (Real.exp t₂))) _ t₁ :=
    hd.hasFDerivAt.comp_hasDerivAt t₁ (hasDerivAt_torus_left t₁ (Real.exp t₂))
  rw [h.deriv]
  exact congrArg _ (smul_smul _ _ _)

private theorem deriv_torus_right {G : M3 → (Fin n → ℂ)} (hG : ContDiffOn ℝ (⊤ : ℕ∞) G GLs) (t₁ t₂ : ℝ) :
    deriv (fun s => G (torus (Real.exp t₁) (Real.exp s))) t₂ =
      fderiv ℝ G (torus (Real.exp t₁) (Real.exp t₂)) ((Real.exp t₁ * Real.exp t₂) • E 0 0) +
        fderiv ℝ G (torus (Real.exp t₁) (Real.exp t₂)) (Real.exp t₂ • E 1 1) := by
  have hd := differentiableAt_of_contDiffOn_GLs hG (torus_exp_mem t₁ t₂)
  have h : HasDerivAt (fun s => G (torus (Real.exp t₁) (Real.exp s))) _ t₂ :=
    hd.hasFDerivAt.comp_hasDerivAt t₂ (hasDerivAt_torus_right (Real.exp t₁) t₂)
  rw [h.deriv, smul_add, map_add]
  exact congrArg (· + _) (congrArg _ ((smul_smul _ _ _).trans (congrArg (· • E 0 0) (mul_comm _ _))))

private theorem rD_eq_fderiv_torus (X : M3) {G : M3 → (Fin n → ℂ)} (hG : ContDiffOn ℝ (⊤ : ℕ∞) G GLs) (t₁ t₂ : ℝ) :
    rD X G (torus (Real.exp t₁) (Real.exp t₂)) =
      fderiv ℝ G (torus (Real.exp t₁) (Real.exp t₂)) (torus (Real.exp t₁) (Real.exp t₂) * X) :=
  rD_eq_fderiv X (differentiableAt_of_contDiffOn_GLs hG (torus_exp_mem t₁ t₂))

private theorem torus_mul_one_add_E01 (y z s : ℝ) :
    torus y z * (1 + s • E 0 1) = (1 + (s * y) • E 0 1) * torus y z := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [torus, E, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply, mul_assoc, mul_comm,
      mul_left_comm]

private theorem torus_mul_one_add_E12 (y z s : ℝ) :
    torus y z * (1 + s • E 1 2) = (1 + (s * z) • E 1 2) * torus y z := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [torus, E, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply, mul_assoc, mul_comm,
      mul_left_comm]

private theorem torus_mul_one_add_E02 (y z s : ℝ) :
    torus y z * (1 + s • E 0 2) = (1 + (s * (y * z)) • E 0 2) * torus y z := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [torus, E, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply, mul_assoc, mul_comm,
      mul_left_comm]

private theorem isUpperUni_one_add_smul_E {a b : Fin 3} (hab : a < b) (r : ℝ) : IsUpperUni (1 + r • E a b) := by
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · have : ¬ (a = i ∧ b = j) := fun h => by rw [← h.1, ← h.2] at hji; exact absurd hab (not_lt.2 hji.le)
    simp [E, hji.ne', this]
  · have : ¬ (a = i ∧ b = i) := fun h => by rw [h.1, h.2] at hab; exact lt_irrefl _ hab
    simp [E, this]

private theorem uniChar_one_add_E01 (r : ℝ) : uniChar (1 + r • E 0 1) = Complex.exp (twoPiI * r) := by
  simp [uniChar, twoPiI, E]

private theorem uniChar_one_add_E12 (r : ℝ) : uniChar (1 + r • E 1 2) = Complex.exp (twoPiI * r) := by
  simp [uniChar, twoPiI, E]

private theorem uniChar_one_add_E02 (r : ℝ) : uniChar (1 + r • E 0 2) = 1 := by
  simp [uniChar, E]

private theorem deriv_cexp_mul_smul (c : ℂ) (v : Fin n → ℂ) :
    deriv (fun s : ℝ => Complex.exp (c * s) • v) 0 = c • v := by
  have h : HasDerivAt (fun s : ℝ => Complex.exp (c * s) • v) (c • v) 0 := by
    rw [hasDerivAt_pi]
    intro k
    have h1 : HasDerivAt (fun s : ℝ => c * (s : ℂ)) c 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul c
    simpa using h1.cexp.mul_const (v k)
  exact h.deriv

private theorem rD_upper_torus {G : M3 → (Fin n → ℂ)}
    (hN : ∀ n' x : M3, IsUpperUni n' → x ∈ GLs → G (n' * x) = uniChar n' • G x) {X : M3} {x : M3} (hx : x ∈ GLs)
    {m : ℝ → M3} (hm : ∀ s : ℝ, x * (1 + s • X) = m s * x) (hu : ∀ s, IsUpperUni (m s)) {c : ℂ}
    (hc : ∀ s : ℝ, uniChar (m s) = Complex.exp (c * s)) : rD X G x = c • G x := by
  unfold rD
  have hf : (fun s : ℝ => G (x * (1 + s • X))) = fun s : ℝ => Complex.exp (c * s) • G x := by
    funext s; rw [hm s, hN _ _ (hu s) hx, hc s]
  rw [hf, deriv_cexp_mul_smul]

private theorem ofReal_map_sub (X Y : M3) :
    (X - Y).map ((↑) : ℝ → ℂ) = X.map ((↑) : ℝ → ℂ) - Y.map ((↑) : ℝ → ℂ) := by
  ext i j; simp

private theorem ofReal_map_ite (P : Prop) [Decidable P] (p q : Fin 3) :
    (if P then E p q else (0 : M3)).map ((↑) : ℝ → ℂ) = if P then (E p q : M3).map ((↑) : ℝ → ℂ) else 0 := by
  split_ifs <;> simp

end TorusFurniture
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

private theorem rD_E00_torus {G : M3 → (Fin n → ℂ)} (hG : ContDiffOn ℝ (⊤ : ℕ∞) G GLs) (t₁ t₂ : ℝ) :
    rD (E 0 0) G (torus (Real.exp t₁) (Real.exp t₂)) =
      deriv (fun s => G (torus (Real.exp s) (Real.exp t₂))) t₁ := by
  rw [rD_eq_fderiv_torus _ hG, torus_mul_E00, deriv_torus_left hG]

private theorem rD_E11_torus {G : M3 → (Fin n → ℂ)} (hG : ContDiffOn ℝ (⊤ : ℕ∞) G GLs) (t₁ t₂ : ℝ) :
    rD (E 1 1) G (torus (Real.exp t₁) (Real.exp t₂)) =
      deriv (fun s => G (torus (Real.exp t₁) (Real.exp s))) t₂ -
        deriv (fun s => G (torus (Real.exp s) (Real.exp t₂))) t₁ := by
  rw [rD_eq_fderiv_torus _ hG, torus_mul_E11, deriv_torus_right hG, deriv_torus_left hG]
  abel

private theorem rD_E22_torus {G : M3 → (Fin n → ℂ)} (hG : ContDiffOn ℝ (⊤ : ℕ∞) G GLs) {cω : ℂ}
    (hZ : ∀ x ∈ GLs, rD 1 G x = cω • G x) (t₁ t₂ : ℝ) :
    rD (E 2 2) G (torus (Real.exp t₁) (Real.exp t₂)) =
      cω • G (torus (Real.exp t₁) (Real.exp t₂)) - deriv (fun s => G (torus (Real.exp t₁) (Real.exp s))) t₂ := by
  rw [rD_eq_fderiv_torus _ hG, torus_mul_E22, deriv_torus_right hG, ← hZ _ (torus_exp_mem t₁ t₂),
    rD_eq_fderiv_torus _ hG, mul_one]
  conv_lhs => rw [← add_sub_cancel_left (fderiv ℝ G (torus (Real.exp t₁) (Real.exp t₂))
    ((Real.exp t₁ * Real.exp t₂) • E 0 0) + fderiv ℝ G (torus (Real.exp t₁) (Real.exp t₂)) (Real.exp t₂ • E 1 1))
    (fderiv ℝ G (torus (Real.exp t₁) (Real.exp t₂)) (E 2 2))]
  congr 1
  rw [← map_add, ← map_add]
  congr 1
  exact (torus_eq_sum _ _).symm

private theorem rD_E01_torus {G : M3 → (Fin n → ℂ)}
    (hN : ∀ n' x : M3, IsUpperUni n' → x ∈ GLs → G (n' * x) = uniChar n' • G x) (t₁ t₂ : ℝ) :
    rD (E 0 1) G (torus (Real.exp t₁) (Real.exp t₂)) =
      (twoPiI * Real.exp t₁) • G (torus (Real.exp t₁) (Real.exp t₂)) := by
  refine rD_upper_torus hN (torus_exp_mem t₁ t₂) (m := fun s => 1 + (s * Real.exp t₁) • E 0 1)
    (fun s => torus_mul_one_add_E01 _ _ s) (fun s => isUpperUni_one_add_smul_E (by decide) _) fun s => ?_
  rw [uniChar_one_add_E01]
  push_cast
  ring_nf

private theorem rD_E12_torus {G : M3 → (Fin n → ℂ)}
    (hN : ∀ n' x : M3, IsUpperUni n' → x ∈ GLs → G (n' * x) = uniChar n' • G x) (t₁ t₂ : ℝ) :
    rD (E 1 2) G (torus (Real.exp t₁) (Real.exp t₂)) =
      (twoPiI * Real.exp t₂) • G (torus (Real.exp t₁) (Real.exp t₂)) := by
  refine rD_upper_torus hN (torus_exp_mem t₁ t₂) (m := fun s => 1 + (s * Real.exp t₂) • E 1 2)
    (fun s => torus_mul_one_add_E12 _ _ s) (fun s => isUpperUni_one_add_smul_E (by decide) _) fun s => ?_
  rw [uniChar_one_add_E12]
  push_cast
  ring_nf

private theorem rD_E02_torus {G : M3 → (Fin n → ℂ)}
    (hN : ∀ n' x : M3, IsUpperUni n' → x ∈ GLs → G (n' * x) = uniChar n' • G x) (t₁ t₂ : ℝ) :
    rD (E 0 2) G (torus (Real.exp t₁) (Real.exp t₂)) = 0 := by
  rw [show (0 : Fin n → ℂ) = (0 : ℂ) • G (torus (Real.exp t₁) (Real.exp t₂)) from (zero_smul ℂ _).symm]
  refine rD_upper_torus hN (torus_exp_mem t₁ t₂) (m := fun s => 1 + (s * (Real.exp t₁ * Real.exp t₂)) • E 0 2)
    (fun s => torus_mul_one_add_E02 _ _ s) (fun s => isUpperUni_one_add_smul_E (by decide) _) fun s => ?_
  rw [uniChar_one_add_E02, zero_mul, Complex.exp_zero]

private theorem smooth2_torus {W : M3 → (Fin n → ℂ)} (hW : ContDiffOn ℝ (⊤ : ℕ∞) W GLs) :
    Smooth2 (fun t₁ t₂ => W (torus (Real.exp t₁) (Real.exp t₂))) := by
  unfold Smooth2
  have hτ : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ × ℝ => torus (Real.exp t.1) (Real.exp t.2) := by
    have hf : (fun t : ℝ × ℝ => torus (Real.exp t.1) (Real.exp t.2)) =
        fun t : ℝ × ℝ => (Real.exp t.1 * Real.exp t.2) • E 0 0 + Real.exp t.2 • E 1 1 + E 2 2 := by
      funext t; exact torus_eq_sum _ _
    rw [hf]
    exact (((contDiff_fst.exp).mul (contDiff_snd.exp)).smul contDiff_const).add
      ((contDiff_snd.exp).smul contDiff_const) |>.add contDiff_const
  exact hW.comp_contDiff hτ fun t => torus_exp_mem t.1 t.2

private def brCoeff (a b : Fin 3) (cd ef : Fin 3 × Fin 3) : ℂ :=
  (if b = cd.1 ∧ ef = (a, cd.2) then 1 else 0) - (if cd.2 = a ∧ ef = (cd.1, b) then 1 else 0)
    - (if a = cd.1 ∧ ef = (b, cd.2) then 1 else 0) + (if cd.2 = b ∧ ef = (cd.1, a) then 1 else 0)

private theorem bracket_eq_sum_brCoeff (a b : Fin 3) (cd : Fin 3 × Fin 3) :
    ((E a b - E b a) * E cd.1 cd.2 - E cd.1 cd.2 * (E a b - E b a) : M3).map ((↑) : ℝ → ℂ) =
      ∑ ef : Fin 3 × Fin 3, brCoeff a b cd ef • (E ef.1 ef.2 : M3).map ((↑) : ℝ → ℂ) := by
  obtain ⟨c, d⟩ := cd
  simp only [brCoeff, sub_mul, mul_sub, E_mul_E, sub_smul, add_smul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ite_smul, one_smul, zero_smul, ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const_zero, ofReal_map_sub, ofReal_map_ite]
  abel

variable (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ)

private noncomputable def upperOp (ab : Fin 3 × Fin 3) (D : DOp (Fin n)) : DOp (Fin n) :=
  if ab = (0, 1) then cmul ((MvPolynomial.C twoPiI * MvPolynomial.X 0 : Coef) • (1 : Matrix (Fin n) (Fin n) Coef)) D
  else if ab = (1, 2) then
    cmul ((MvPolynomial.C twoPiI * MvPolynomial.X 1 : Coef) • (1 : Matrix (Fin n) (Fin n) Coef)) D
  else 0

private noncomputable def diagOp (a : Fin 3) (D : DOp (Fin n)) : DOp (Fin n) :=
  if a = 0 then comp d₁ D else if a = 1 then comp d₂ D - comp d₁ D else cω • D - comp d₂ D

private noncomputable def letterOp {ℓ : ℕ} (ab : Fin 3 × Fin 3) (w : Fin ℓ → Fin 3 × Fin 3)
    (ev : (Fin ℓ → Fin 3 × Fin 3) → DOp (Fin n)) : DOp (Fin n) :=
  if ab.1 = ab.2 then diagOp cω ab.1 (ev w)
  else if ab.1 < ab.2 then upperOp ab (ev w)
  else upperOp (ab.2, ab.1) (ev w) + cmul ((S ab.1 ab.2).map MvPolynomial.C) (ev w)
    + ∑ p : Fin ℓ, ∑ ef : Fin 3 × Fin 3, brCoeff ab.1 ab.2 (w p) ef • ev (Function.update w p ef)

private noncomputable def wordOp : (ℓ : ℕ) → (Fin ℓ → Fin 3 × Fin 3) → DOp (Fin n)
  | 0, _ => one
  | ℓ + 1, w => letterOp S cω (w 0) (Fin.tail w) (wordOp ℓ)

private noncomputable def casOp₂ : DOp (Fin n) := ∑ i : Fin 3, ∑ j : Fin 3, wordOp S cω 2 ![(i, j), (j, i)]

private noncomputable def casOp₃ : DOp (Fin n) :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, wordOp S cω 3 ![(i, j), (j, k), (k, i)]

section TransportProof

private def tor (G : M3 → (Fin n → ℂ)) : ℝ → ℝ → (Fin n → ℂ) := fun s₁ s₂ => G (torus (Real.exp s₁) (Real.exp s₂))

private theorem smooth2_tor {G : M3 → (Fin n → ℂ)} (hG : ContDiffOn ℝ (⊤ : ℕ∞) G GLs) : Smooth2 (tor G) :=
  smooth2_torus hG

private theorem rDw_succ_eq (ℓ : ℕ) (w : Fin (ℓ + 1) → Fin 3 × Fin 3) (F : M3 → (Fin n → ℂ)) :
    rDw (ℓ + 1) w F = rD (E (w 0).1 (w 0).2) (rDw ℓ (Fin.tail w) F) := rfl

private theorem wordOp_succ (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ) (ℓ : ℕ)
    (w : Fin (ℓ + 1) → Fin 3 × Fin 3) : wordOp S cω (ℓ + 1) w = letterOp S cω (w 0) (Fin.tail w) (wordOp S cω ℓ) := rfl

private theorem letters_update (ℓ : ℕ) (w : Fin ℓ → Fin 3 × Fin 3) (p : Fin ℓ) (ef : Fin 3 × Fin 3) :
    (fun q => E (Function.update w p ef q).1 (Function.update w p ef q).2) =
      Function.update (fun q => E (w q).1 (w q).2) p (E ef.1 ef.2) := by
  funext q
  by_cases hq : q = p
  · subst hq; simp
  · simp [hq]

private def brCoeffR (a b : Fin 3) (cd ef : Fin 3 × Fin 3) : ℝ :=
  (if b = cd.1 ∧ ef = (a, cd.2) then 1 else 0) - (if cd.2 = a ∧ ef = (cd.1, b) then 1 else 0)
    - (if a = cd.1 ∧ ef = (b, cd.2) then 1 else 0) + (if cd.2 = b ∧ ef = (cd.1, a) then 1 else 0)

private theorem brCoeff_eq_coe (a b : Fin 3) (cd ef : Fin 3 × Fin 3) :
    brCoeff a b cd ef = (brCoeffR a b cd ef : ℂ) := by
  unfold brCoeff brCoeffR
  split_ifs <;> simp

private theorem bracket_eq_sum_brCoeffR (a b : Fin 3) (cd : Fin 3 × Fin 3) :
    ((E a b - E b a) * E cd.1 cd.2 - E cd.1 cd.2 * (E a b - E b a) : M3) =
      ∑ ef : Fin 3 × Fin 3, brCoeffR a b cd ef • E ef.1 ef.2 := by
  obtain ⟨c, d⟩ := cd
  simp only [brCoeffR, sub_mul, mul_sub, E_mul_E, sub_smul, add_smul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ite_smul, one_smul, zero_smul, ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const_zero]
  abel

private theorem rDm_update_sum (ℓ : ℕ) (w : Fin ℓ → M3) (p : Fin ℓ) {κ : Type} (s : Finset κ) (Y : κ → M3)
    {F : M3 → (Fin n → ℂ)} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {x : M3} (hx : x ∈ GLs) :
    rDm ℓ (Function.update w p (∑ k ∈ s, Y k)) F x = ∑ k ∈ s, rDm ℓ (Function.update w p (Y k)) F x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact rDm_update_zero ℓ w p hF hx
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, rDm_update_add_eqOn ℓ w p _ _ hF hx, Pi.add_apply, ih]

private theorem real_smul_eq_coe_smul (r : ℝ) (v : Fin n → ℂ) : r • v = (r : ℂ) • v := by
  funext i
  simp [Complex.real_smul]

private theorem apply_sub_fun (D D' : DOp (Fin n)) (G : ℝ → ℝ → (Fin n → ℂ)) :
    apply (D - D') G = fun t₁ t₂ => apply D G t₁ t₂ - apply D' G t₁ t₂ := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ D', apply_add, apply_smul]
  funext t₁ t₂
  simp [sub_eq_add_neg]

private theorem mev_map_C (M : Matrix (Fin n) (Fin n) ℂ) (t₁ t₂ : ℝ) : mev (M.map MvPolynomial.C) t₁ t₂ = M := by
  ext i j
  simp [mev, Coef.ev]

private theorem mev_poly_smul_one (p : Coef) (t₁ t₂ : ℝ) :
    mev (p • (1 : Matrix (Fin n) (Fin n) Coef)) t₁ t₂ = p.ev t₁ t₂ • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  by_cases h : i = j <;> simp [mev, Coef.ev, Matrix.one_apply, h]

private theorem apply_upperOp_01 (D : DOp (Fin n)) (G : ℝ → ℝ → (Fin n → ℂ)) (t₁ t₂ : ℝ) :
    apply (upperOp ((0 : Fin 3), (1 : Fin 3)) D) G t₁ t₂ = (twoPiI * Real.exp t₁) • apply D G t₁ t₂ := by
  simp only [upperOp, if_true]
  rw [apply_cmul]
  simp only [mev_poly_smul_one, ev_mul, ev_C, ev_X0, Matrix.smul_mulVec, Matrix.one_mulVec, Complex.ofReal_exp]

private theorem apply_upperOp_12 (D : DOp (Fin n)) (G : ℝ → ℝ → (Fin n → ℂ)) (t₁ t₂ : ℝ) :
    apply (upperOp ((1 : Fin 3), (2 : Fin 3)) D) G t₁ t₂ = (twoPiI * Real.exp t₂) • apply D G t₁ t₂ := by
  have h1 : ((1 : Fin 3), (2 : Fin 3)) ≠ ((0 : Fin 3), (1 : Fin 3)) := by decide
  simp only [upperOp, h1, if_false, if_true]
  rw [apply_cmul]
  simp only [mev_poly_smul_one, ev_mul, ev_C, ev_X1, Matrix.smul_mulVec, Matrix.one_mulVec, Complex.ofReal_exp]

private theorem apply_upperOp_02 (D : DOp (Fin n)) (G : ℝ → ℝ → (Fin n → ℂ)) (t₁ t₂ : ℝ) :
    apply (upperOp ((0 : Fin 3), (2 : Fin 3)) D) G t₁ t₂ = 0 := by
  have h1 : ((0 : Fin 3), (2 : Fin 3)) ≠ ((0 : Fin 3), (1 : Fin 3)) := by decide
  have h2 : ((0 : Fin 3), (2 : Fin 3)) ≠ ((1 : Fin 3), (2 : Fin 3)) := by decide
  simp only [upperOp, h1, h2, if_false]
  rw [apply_zero']

private theorem tor_rD_upper {G : M3 → (Fin n → ℂ)}
    (hN : ∀ n' x : M3, IsUpperUni n' → x ∈ GLs → G (n' * x) = uniChar n' • G x)
    {a b : Fin 3} (hab : a < b) {D : DOp (Fin n)} {H : ℝ → ℝ → (Fin n → ℂ)} (hD : apply D H = tor G) (t₁ t₂ : ℝ) :
    rD (E a b) G (torus (Real.exp t₁) (Real.exp t₂)) = apply (upperOp (a, b) D) H t₁ t₂ := by
  have hDt : apply D H t₁ t₂ = G (torus (Real.exp t₁) (Real.exp t₂)) := by rw [hD]; rfl
  fin_cases a <;> fin_cases b <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hab ⊢ <;>
    first
    | exact absurd hab (by decide)
    | (rw [apply_upperOp_01 D H, hDt]; exact rD_E01_torus hN t₁ t₂)
    | (rw [apply_upperOp_12 D H, hDt]; exact rD_E12_torus hN t₁ t₂)
    | (rw [apply_upperOp_02 D H]; exact rD_E02_torus hN t₁ t₂)

private theorem tor_rD_diag {G : M3 → (Fin n → ℂ)} (hG : ContDiffOn ℝ (⊤ : ℕ∞) G GLs) {cω : ℂ}
    (hZ : ∀ x ∈ GLs, rD 1 G x = cω • G x) (a : Fin 3) {D : DOp (Fin n)} {H : ℝ → ℝ → (Fin n → ℂ)} (hH : Smooth2 H)
    (hD : apply D H = tor G) (t₁ t₂ : ℝ) :
    rD (E a a) G (torus (Real.exp t₁) (Real.exp t₂)) = apply (diagOp cω a D) H t₁ t₂ := by
  have h1 : apply (comp d₁ D) H t₁ t₂ = deriv (fun s => G (torus (Real.exp s) (Real.exp t₂))) t₁ := by
    rw [apply_comp _ _ hH, hD, apply_d₁]; rfl
  have h2 : apply (comp d₂ D) H t₁ t₂ = deriv (fun s => G (torus (Real.exp t₁) (Real.exp s))) t₂ := by
    rw [apply_comp _ _ hH, hD, apply_d₂]; rfl
  have hDt : apply D H t₁ t₂ = G (torus (Real.exp t₁) (Real.exp t₂)) := by rw [hD]; rfl
  fin_cases a
  · simp only [diagOp, Fin.zero_eta, if_true]
    rw [h1]; exact rD_E00_torus hG t₁ t₂
  · have h10 : (1 : Fin 3) ≠ 0 := by decide
    simp only [diagOp, Fin.mk_one, h10, if_false, if_true]
    rw [apply_sub_fun]; simp only []; rw [h2, h1]; exact rD_E11_torus hG t₁ t₂
  · have h20 : (2 : Fin 3) ≠ 0 := by decide
    have h21 : (2 : Fin 3) ≠ 1 := by decide
    simp only [diagOp, Fin.reduceFinMk, h20, h21, if_false]
    rw [apply_sub_fun]; simp only []; rw [apply_smul]; simp only []; rw [hDt, h2]; exact rD_E22_torus hG hZ t₁ t₂

private theorem tor_rD_lower {W : M3 → (Fin n → ℂ)} (hW : ContDiffOn ℝ (⊤ : ℕ∞) W GLs)
    (hN : ∀ n' x : M3, IsUpperUni n' → x ∈ GLs → W (n' * x) = uniChar n' • W x)
    (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ)
    (hK : ∀ x ∈ GLs, ∀ a b : Fin 3, b < a → rD (E a b - E b a) W x = S a b *ᵥ W x) (ℓ : ℕ)
    (ev : (Fin ℓ → Fin 3 × Fin 3) → DOp (Fin n)) (ih : ∀ v, tor (rDw ℓ v W) = apply (ev v) (tor W))
    (w' : Fin ℓ → Fin 3 × Fin 3) {a b : Fin 3} (hba : b < a) (t₁ t₂ : ℝ) :
    rD (E a b) (rDw ℓ w' W) (torus (Real.exp t₁) (Real.exp t₂)) =
      apply (upperOp (b, a) (ev w') + cmul ((S a b).map MvPolynomial.C) (ev w')
        + ∑ p : Fin ℓ, ∑ ef : Fin 3 × Fin 3, brCoeff a b (w' p) ef • ev (Function.update w' p ef)) (tor W) t₁ t₂ := by
  have hx := torus_exp_mem t₁ t₂
  set x := torus (Real.exp t₁) (Real.exp t₂) with hxdef
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) (rDw ℓ w' W) GLs := contDiffOn_rDw ℓ w' hW
  have hGN : ∀ n' y : M3, IsUpperUni n' → y ∈ GLs → rDw ℓ w' W (n' * y) = uniChar n' • rDw ℓ w' W y :=
    fun n' y hn' hy => rDm_uni hN ℓ _ hn' hy
  have ih_pt : ∀ v, rDw ℓ v W x = apply (ev v) (tor W) t₁ t₂ := fun v => by
    have h := congrFun (congrFun (ih v) t₁) t₂
    exact h

  have hsplit : E a b = E b a + (E a b - E b a) := by abel
  rw [apply_add, apply_add]
  simp only []
  conv_lhs => rw [hsplit, rD_add_dir _ _ (differentiableAt_of_contDiffOn_GLs hG hx)]

  have h1 : rD (E b a) (rDw ℓ w' W) x = apply (upperOp (b, a) (ev w')) (tor W) t₁ t₂ :=
    tor_rD_upper hGN hba (ih w').symm t₁ t₂

  have h2 := rD_rDm_eqOn (E a b - E b a) ℓ (fun q => E (w' q).1 (w' q).2) hW hx
  simp only [Pi.add_apply] at h2

  have h2a : rDm ℓ (fun q => E (w' q).1 (w' q).2) (rD (E a b - E b a) W) x =
      apply (cmul ((S a b).map MvPolynomial.C) (ev w')) (tor W) t₁ t₂ := by
    rw [rDm_congr_GLs ℓ _ (fun y hy => hK y hy a b hba) hx, rDm_mulVec ℓ _ (S a b) hW hx, apply_cmul]
    simp only [mev_map_C]
    rw [← ih_pt w']
    rfl

  have h2b : ∀ p : Fin ℓ,
      rDm ℓ (Function.update (fun q => E (w' q).1 (w' q).2) p
          ((E a b - E b a) * E (w' p).1 (w' p).2 - E (w' p).1 (w' p).2 * (E a b - E b a))) W x =
        ∑ ef : Fin 3 × Fin 3, brCoeff a b (w' p) ef • apply (ev (Function.update w' p ef)) (tor W) t₁ t₂ := by
    intro p
    rw [bracket_eq_sum_brCoeffR a b (w' p), rDm_update_sum ℓ _ p Finset.univ _ hW hx]
    refine Finset.sum_congr rfl fun ef _ => ?_
    rw [rDm_update_smul_eqOn ℓ _ p _ _ hW hx, Pi.smul_apply, ← letters_update, brCoeff_eq_coe, ← real_smul_eq_coe_smul,
      ← ih_pt (Function.update w' p ef)]
    rfl
  have h2op : apply (∑ p : Fin ℓ, ∑ ef : Fin 3 × Fin 3, brCoeff a b (w' p) ef • ev (Function.update w' p ef))
      (tor W) t₁ t₂ =
        ∑ p : Fin ℓ, ∑ ef : Fin 3 × Fin 3,
          brCoeff a b (w' p) ef • apply (ev (Function.update w' p ef)) (tor W) t₁ t₂ := by
    rw [apply_finset_sum]
    simp only []
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [apply_finset_sum]
    simp only []
    exact Finset.sum_congr rfl fun ef _ => by rw [apply_smul]
  rw [h1, h2op]
  show _ + rD (E a b - E b a) (rDm ℓ (fun q => E (w' q).1 (w' q).2) W) x = _
  rw [h2, h2a, add_assoc]
  congr 2
  exact Finset.sum_congr rfl fun p _ => h2b p

private theorem tor_rDw_eq (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ) {W : M3 → (Fin n → ℂ)}
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) W GLs)
    (hN : ∀ n' x : M3, IsUpperUni n' → x ∈ GLs → W (n' * x) = uniChar n' • W x)
    (hZ : ∀ x ∈ GLs, rD 1 W x = cω • W x)
    (hK : ∀ x ∈ GLs, ∀ a b : Fin 3, b < a → rD (E a b - E b a) W x = S a b *ᵥ W x) (ℓ : ℕ) :
    ∀ w : Fin ℓ → Fin 3 × Fin 3, tor (rDw ℓ w W) = apply (wordOp S cω ℓ w) (tor W) := by
  induction ℓ with
  | zero =>
    intro w
    show tor W = apply one (tor W)
    rw [apply_one]
  | succ ℓ ih =>
    intro w
    funext t₁ t₂
    rw [rDw_succ_eq, wordOp_succ]
    rcases hw0 : w 0 with ⟨a, b⟩
    have hG : ContDiffOn ℝ (⊤ : ℕ∞) (rDw ℓ (Fin.tail w) W) GLs := contDiffOn_rDw ℓ _ hW
    have hGN : ∀ n' y : M3, IsUpperUni n' → y ∈ GLs →
        rDw ℓ (Fin.tail w) W (n' * y) = uniChar n' • rDw ℓ (Fin.tail w) W y :=
      fun n' y hn' hy => rDm_uni hN ℓ _ hn' hy
    have hGZ : ∀ y ∈ GLs, rD 1 (rDw ℓ (Fin.tail w) W) y = cω • rDw ℓ (Fin.tail w) W y :=
      fun y hy => rDm_centre hW hZ ℓ _ hy
    show rD (E a b) (rDw ℓ (Fin.tail w) W) (torus (Real.exp t₁) (Real.exp t₂)) = _
    rcases lt_trichotomy a b with hab | hab | hba
    · simp only [letterOp, hab.ne, if_false, hab, if_true]
      exact tor_rD_upper hGN hab (ih (Fin.tail w)).symm t₁ t₂
    · subst hab
      simp only [letterOp, if_true]
      exact tor_rD_diag hG hGZ a (smooth2_tor hW) (ih (Fin.tail w)).symm t₁ t₂
    · simp only [letterOp, hba.ne', if_false, not_lt.2 hba.le]
      exact tor_rD_lower hW hN S hK ℓ (wordOp S cω ℓ) ih (Fin.tail w) hba t₁ t₂

end TransportProof
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

private theorem rDw_torus_eq_apply_wordOp {W : M3 → (Fin n → ℂ)} (hW : ContDiffOn ℝ (⊤ : ℕ∞) W GLs)
    (hN : ∀ n' x : M3, IsUpperUni n' → x ∈ GLs → W (n' * x) = uniChar n' • W x)
    (hZ : ∀ x ∈ GLs, rD 1 W x = cω • W x)
    (hK : ∀ x ∈ GLs, ∀ a b : Fin 3, b < a → rD (E a b - E b a) W x = S a b *ᵥ W x)
    (ℓ : ℕ) (w : Fin ℓ → Fin 3 × Fin 3) (t₁ t₂ : ℝ) :
    rDw ℓ w W (torus (Real.exp t₁) (Real.exp t₂)) =
      apply (wordOp S cω ℓ w) (fun s₁ s₂ => W (torus (Real.exp s₁) (Real.exp s₂))) t₁ t₂ := by
  have h := congrFun (congrFun (tor_rDw_eq S cω hW hN hZ hK ℓ w) t₁) t₂
  exact h

private theorem c2_eq_sum_rDw {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (F : M3 → V) (x : M3) :
    c2 F x = ∑ i : Fin 3, ∑ j : Fin 3, rDw 2 ![(i, j), (j, i)] F x := by
  rfl

private theorem c3_eq_sum_rDw {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (F : M3 → V) (x : M3) :
    c3 F x = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, rDw 3 ![(i, j), (j, k), (k, i)] F x := by
  rfl

private theorem c2_torus_eq_apply_casOp₂ {W : M3 → (Fin n → ℂ)} (hW : ContDiffOn ℝ (⊤ : ℕ∞) W GLs)
    (hN : ∀ n' x : M3, IsUpperUni n' → x ∈ GLs → W (n' * x) = uniChar n' • W x)
    (hZ : ∀ x ∈ GLs, rD 1 W x = cω • W x)
    (hK : ∀ x ∈ GLs, ∀ a b : Fin 3, b < a → rD (E a b - E b a) W x = S a b *ᵥ W x) (t₁ t₂ : ℝ) :
    c2 W (torus (Real.exp t₁) (Real.exp t₂)) =
      apply (casOp₂ S cω) (fun s₁ s₂ => W (torus (Real.exp s₁) (Real.exp s₂))) t₁ t₂ := by
  rw [c2_eq_sum_rDw, casOp₂, apply_finset_sum]
  simp only []
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [apply_finset_sum]
  simp only []
  exact Finset.sum_congr rfl fun j _ => rDw_torus_eq_apply_wordOp S cω hW hN hZ hK 2 _ t₁ t₂

private theorem c3_torus_eq_apply_casOp₃ {W : M3 → (Fin n → ℂ)} (hW : ContDiffOn ℝ (⊤ : ℕ∞) W GLs)
    (hN : ∀ n' x : M3, IsUpperUni n' → x ∈ GLs → W (n' * x) = uniChar n' • W x)
    (hZ : ∀ x ∈ GLs, rD 1 W x = cω • W x)
    (hK : ∀ x ∈ GLs, ∀ a b : Fin 3, b < a → rD (E a b - E b a) W x = S a b *ᵥ W x) (t₁ t₂ : ℝ) :
    c3 W (torus (Real.exp t₁) (Real.exp t₂)) =
      apply (casOp₃ S cω) (fun s₁ s₂ => W (torus (Real.exp s₁) (Real.exp s₂))) t₁ t₂ := by
  rw [c3_eq_sum_rDw, casOp₃, apply_finset_sum]
  simp only []
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [apply_finset_sum]
  simp only []
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [apply_finset_sum]
  simp only []
  exact Finset.sum_congr rfl fun k _ => rDw_torus_eq_apply_wordOp S cω hW hN hZ hK 3 _ t₁ t₂

section WordAlgebra

private theorem hasOrder_zero_op (k : ℕ) : HasOrder (0 : DOp (Fin n)) k := fun ab hab => by simp at hab

private theorem hasOrder_sub_op {D D' : DOp (Fin n)} {k : ℕ} (h : HasOrder D k) (h' : HasOrder D' k) :
    HasOrder (D - D') k := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ D']
  exact h.add (h'.smul _)

private theorem hasOrder_d₁_op : HasOrder (d₁ : DOp (Fin n)) 1 := by
  rw [d₁_eq_mono]; exact hasOrder_mono 1 0

private theorem hasOrder_d₂_op : HasOrder (d₂ : DOp (Fin n)) 1 := by
  rw [d₂_eq_mono]; exact hasOrder_mono 0 1

private theorem hasOrder_upperOp (ab : Fin 3 × Fin 3) {D : DOp (Fin n)} {k : ℕ} (hD : HasOrder D k) :
    HasOrder (upperOp ab D) k := by
  unfold upperOp
  split_ifs
  · exact hD.cmul _
  · exact hD.cmul _
  · exact hasOrder_zero_op k

private theorem hasOrder_diagOp (cω : ℂ) (a : Fin 3) {D : DOp (Fin n)} {k : ℕ} (hD : HasOrder D k) :
    HasOrder (diagOp cω a D) (k + 1) := by
  have h1 := hasOrder_d₁_op.comp hD
  have h2 := hasOrder_d₂_op.comp hD
  rw [add_comm] at h1 h2
  unfold diagOp
  split_ifs
  · exact h1
  · exact hasOrder_sub_op h2 h1
  · exact hasOrder_sub_op ((hD.smul cω).mono_le (Nat.le_succ k)) h2

private theorem hasOrder_lowerOp (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) {ℓ : ℕ} (a b : Fin 3)
    (w : Fin ℓ → Fin 3 × Fin 3) {ev : (Fin ℓ → Fin 3 × Fin 3) → DOp (Fin n)} (hev : ∀ v, HasOrder (ev v) ℓ) :
    HasOrder (upperOp (b, a) (ev w) + cmul ((S a b).map MvPolynomial.C) (ev w)
      + ∑ p : Fin ℓ, ∑ ef : Fin 3 × Fin 3, brCoeff a b (w p) ef • ev (Function.update w p ef)) ℓ :=
  ((hasOrder_upperOp _ (hev w)).add ((hev w).cmul _)).add
    (HasOrder.finset_sum _ fun p _ => HasOrder.finset_sum _ fun ef _ => (hev _).smul _)

private theorem hasOrder_letterOp (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ) {ℓ : ℕ}
    (ab : Fin 3 × Fin 3) (w : Fin ℓ → Fin 3 × Fin 3) {ev : (Fin ℓ → Fin 3 × Fin 3) → DOp (Fin n)}
    (hev : ∀ v, HasOrder (ev v) ℓ) : HasOrder (letterOp S cω ab w ev) (ℓ + 1) := by
  unfold letterOp
  split_ifs
  · exact hasOrder_diagOp cω _ (hev w)
  · exact (hasOrder_upperOp _ (hev w)).mono_le (Nat.le_succ ℓ)
  · exact (hasOrder_lowerOp S _ _ w hev).mono_le (Nat.le_succ ℓ)

private theorem hasOrder_letterOp_of_ne (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ) {ℓ : ℕ}
    {ab : Fin 3 × Fin 3} (hab : ab.1 ≠ ab.2) (w : Fin ℓ → Fin 3 × Fin 3)
    {ev : (Fin ℓ → Fin 3 × Fin 3) → DOp (Fin n)} (hev : ∀ v, HasOrder (ev v) ℓ) :
    HasOrder (letterOp S cω ab w ev) ℓ := by
  unfold letterOp
  rw [if_neg hab]
  split_ifs
  · exact hasOrder_upperOp _ (hev w)
  · exact hasOrder_lowerOp S _ _ w hev

private theorem ddeg_smul_op {c : ℕ} (z : ℂ) {D : DOp (Fin n)} (h : DDeg c D) : DDeg c (z • D) := fun ab => by
  rw [Finsupp.smul_apply]; exact (h ab).smul z

private theorem mdeg_poly_smul_one {d : ℕ} {p : Coef} (hp : p.totalDegree ≤ d) :
    MDeg d (p • (1 : Matrix (Fin n) (Fin n) Coef)) := fun i i' => by
  rw [Matrix.smul_apply, smul_eq_mul]
  by_cases h : i = i'
  · subst h; simpa using hp
  · simp [Matrix.one_apply, h]

private theorem mdeg_map_C (M : Matrix (Fin n) (Fin n) ℂ) (d : ℕ) : MDeg d (M.map MvPolynomial.C) := fun i i' => by
  simp [MvPolynomial.totalDegree_C]

private theorem totalDegree_C_mul_X_le (z : ℂ) (i : Fin 2) :
    ((MvPolynomial.C z * MvPolynomial.X i : Coef)).totalDegree ≤ 1 :=
  (MvPolynomial.totalDegree_mul _ _).trans (by simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X])

private theorem ddeg_upperOp (ab : Fin 3 × Fin 3) {D : DOp (Fin n)} {k : ℕ} (hD : DDeg k D) :
    DDeg (k + 1) (upperOp ab D) := by
  unfold upperOp
  split_ifs
  · exact (ddeg_cmul (mdeg_poly_smul_one (totalDegree_C_mul_X_le _ _)) hD).mono (by omega)
  · exact (ddeg_cmul (mdeg_poly_smul_one (totalDegree_C_mul_X_le _ _)) hD).mono (by omega)
  · exact ddeg_zero _

private theorem ddeg_diagOp (cω : ℂ) (a : Fin 3) {D : DOp (Fin n)} {k : ℕ} (hD : DDeg k D) :
    DDeg (k + 1) (diagOp cω a D) := by
  have h1 : DDeg (k + 1) (comp d₁ D) := by
    rw [d₁_eq_mono]; exact (ddeg_comp (ddeg_mono 0 1 0) hD).mono (by omega)
  have h2 : DDeg (k + 1) (comp d₂ D) := by
    rw [d₂_eq_mono]; exact (ddeg_comp (ddeg_mono 0 0 1) hD).mono (by omega)
  unfold diagOp
  split_ifs
  · exact h1
  · exact h2.sub h1
  · exact (ddeg_smul_op cω (hD.mono (Nat.le_succ k))).sub h2

private theorem ddeg_letterOp (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ) {ℓ : ℕ}
    (ab : Fin 3 × Fin 3) (w : Fin ℓ → Fin 3 × Fin 3) {ev : (Fin ℓ → Fin 3 × Fin 3) → DOp (Fin n)}
    (hev : ∀ v, DDeg ℓ (ev v)) : DDeg (ℓ + 1) (letterOp S cω ab w ev) := by
  unfold letterOp
  split_ifs
  · exact ddeg_diagOp cω _ (hev w)
  · exact ddeg_upperOp _ (hev w)
  · refine ((ddeg_upperOp _ (hev w)).add ((ddeg_cmul (mdeg_map_C _ 0) (hev w)).mono (by omega))).add ?_
    exact (DDeg.sum _ fun p _ => DDeg.sum _ fun ef _ => ddeg_smul_op _ (hev _)).mono (Nat.le_succ ℓ)

private theorem ddeg_wordOp (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ) (ℓ : ℕ) :
    ∀ w : Fin ℓ → Fin 3 × Fin 3, DDeg ℓ (wordOp S cω ℓ w) := by
  induction ℓ with
  | zero => intro w; exact ddeg_one 0
  | succ ℓ ih => intro w; rw [wordOp_succ]; exact ddeg_letterOp S cω _ _ ih

end WordAlgebra
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

private theorem hasOrder_wordOp (ℓ : ℕ) (w : Fin ℓ → Fin 3 × Fin 3) : HasOrder (wordOp S cω ℓ w) ℓ := by
  induction ℓ with
  | zero => exact hasOrder_one
  | succ ℓ ih => rw [wordOp_succ]; exact hasOrder_letterOp S cω _ _ ih

private theorem totalDegree_wordOp_le (ℓ : ℕ) (w : Fin ℓ → Fin 3 × Fin 3) (ab : ℕ × ℕ) (i i' : Fin n) :
    (wordOp S cω ℓ w ab i i').totalDegree ≤ ℓ := by
  exact ddeg_wordOp S cω ℓ w ab i i'

private theorem hasOrder_casOp₂ : HasOrder (casOp₂ S cω) 2 := by
  exact HasOrder.finset_sum _ fun i _ => HasOrder.finset_sum _ fun j _ => hasOrder_wordOp S cω 2 _

private theorem hasOrder_casOp₃ : HasOrder (casOp₃ S cω) 3 := by
  exact HasOrder.finset_sum _ fun i _ => HasOrder.finset_sum _ fun j _ => HasOrder.finset_sum _ fun k _ =>
    hasOrder_wordOp S cω 3 _

private theorem hasOrder_wordOp_of_exists_ne (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ) (ℓ : ℕ) :
    ∀ w : Fin (ℓ + 1) → Fin 3 × Fin 3, (∃ p, (w p).1 ≠ (w p).2) → HasOrder (wordOp S cω (ℓ + 1) w) ℓ := by
  induction ℓ with
  | zero =>
    intro w h
    obtain ⟨p, hp⟩ := h
    rw [Fin.fin_one_eq_zero p] at hp
    rw [wordOp_succ]
    exact hasOrder_letterOp_of_ne S cω hp _ fun v => hasOrder_wordOp S cω 0 v
  | succ ℓ ih =>
    intro w h
    rw [wordOp_succ]
    by_cases h0 : (w 0).1 ≠ (w 0).2
    · exact hasOrder_letterOp_of_ne S cω h0 _ fun v => hasOrder_wordOp S cω (ℓ + 1) v
    · have h0' : (w 0).1 = (w 0).2 := not_not.1 h0
      obtain ⟨p, hp⟩ := h
      have hp0 : p ≠ 0 := by rintro rfl; exact hp h0'
      obtain ⟨q, rfl⟩ : ∃ q : Fin (ℓ + 1), p = q.succ := ⟨p.pred hp0, (Fin.succ_pred p hp0).symm⟩
      have hinner := ih (Fin.tail w) ⟨q, hp⟩
      unfold letterOp
      rw [if_pos h0']
      exact hasOrder_diagOp cω _ hinner

private theorem wordOp_apply_top_eq_zero (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ) (ℓ : ℕ)
    (w : Fin (ℓ + 1) → Fin 3 × Fin 3) (h : ∃ p, (w p).1 ≠ (w p).2) {ab : ℕ × ℕ} (hab : ab.1 + ab.2 = ℓ + 1) :
    wordOp S cω (ℓ + 1) w ab = 0 :=
  apply_eq_zero_of_hasOrder (hasOrder_wordOp_of_exists_ne S cω ℓ w h) (by omega)

private theorem wordOp_zero_eq (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ) (w : Fin 0 → Fin 3 × Fin 3) :
    wordOp S cω 0 w = (one : DOp (Fin n)) := rfl

private theorem wordOp_diag_two (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ) (i : Fin 3) :
    wordOp S cω 2 ![(i, i), (i, i)] = diagOp cω i (diagOp cω i one) := by
  simp [wordOp_succ, wordOp_zero_eq, letterOp, Fin.tail_def]

private theorem wordOp_diag_three (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ) (i : Fin 3) :
    wordOp S cω 3 ![(i, i), (i, i), (i, i)] = diagOp cω i (diagOp cω i (diagOp cω i one)) := by
  simp [wordOp_succ, wordOp_zero_eq, letterOp, Fin.tail_def]

private theorem diagOp_zero_eq (cω : ℂ) (D : DOp (Fin n)) : diagOp cω 0 D = comp (mono 1 0) D := by
  simp [diagOp, d₁_eq_mono]

private theorem diagOp_one_eq (cω : ℂ) (D : DOp (Fin n)) : diagOp cω 1 D = comp (mono 0 1) D - comp (mono 1 0) D := by
  simp [diagOp, d₁_eq_mono, d₂_eq_mono]

private theorem diagOp_two_eq (cω : ℂ) (D : DOp (Fin n)) : diagOp cω 2 D = cω • D - comp (mono 0 1) D := by
  simp [diagOp, d₂_eq_mono]

private theorem one_eq_mono' : (one : DOp (Fin n)) = mono 0 0 := one_eq_mono

private theorem mono_apply_eq (a b : ℕ) (ab : ℕ × ℕ) :
    (mono a b : DOp (Fin n)) ab = if (a, b) = ab then (1 : Matrix (Fin n) (Fin n) Coef) else 0 := by
  simp [mono, Finsupp.single_apply]

private theorem casOp₂_apply_top (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ) (ab : ℕ × ℕ)
    (hab : ab.1 + ab.2 = 2) : casOp₂ S cω ab = ∑ i : Fin 3, wordOp S cω 2 ![(i, i), (i, i)] ab := by
  simp only [casOp₂, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hji => wordOp_apply_top_eq_zero S cω 1 _ ⟨0, by simpa using hji.symm⟩ hab)
    (fun h => absurd (Finset.mem_univ i) h)]

private theorem casOp₃_apply_top (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ) (ab : ℕ × ℕ)
    (hab : ab.1 + ab.2 = 3) : casOp₃ S cω ab = ∑ i : Fin 3, wordOp S cω 3 ![(i, i), (i, i), (i, i)] ab := by
  simp only [casOp₃, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hji => Finset.sum_eq_zero fun k _ =>
      wordOp_apply_top_eq_zero S cω 2 _ ⟨0, by simpa using hji.symm⟩ hab) (fun h => absurd (Finset.mem_univ i) h),
    Finset.sum_eq_single i (fun k _ hki => wordOp_apply_top_eq_zero S cω 2 _ ⟨1, by simpa using hki.symm⟩ hab)
      (fun h => absurd (Finset.mem_univ i) h)]

private theorem casOp₂_top : casOp₂ S cω (2, 0) = scal 2 ∧ casOp₂ S cω (1, 1) = scal (-2) ∧ casOp₂ S cω (0, 2) = scal 2
    := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [casOp₂_apply_top S cω _ rfl]
    simp only [Fin.sum_univ_three, wordOp_diag_two, diagOp_zero_eq, diagOp_one_eq, diagOp_two_eq]
    simp only [comp_sub', DOp.comp_smul, one_eq_mono', mono_comp_mono, sub_comp', DOp.smul_comp, Finsupp.sub_apply,
      Finsupp.smul_apply, Finsupp.add_apply, mono_apply_eq, Prod.mk.injEq]
    simp only [Nat.reduceEqDiff, and_self, and_false, false_and, if_true, if_false, smul_zero, sub_zero, zero_sub,
      sub_neg_eq_add, sub_self, zero_add, add_zero, neg_zero]
    ext r s
    by_cases hrs : r = s
    · subst hrs
      simp only [scal_apply', if_true, map_ofNat, map_neg, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
        Matrix.one_apply_eq, Matrix.zero_apply]
      ring
    · simp only [scal_apply', hrs, if_false, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
        Matrix.one_apply_ne hrs, Matrix.zero_apply]
      ring

private theorem casOp₃_top : casOp₃ S cω (3, 0) = 0 ∧ casOp₃ S cω (2, 1) = scal 3 ∧ casOp₃ S cω (1, 2) = scal (-3) ∧
    casOp₃ S cω (0, 3) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [casOp₃_apply_top S cω _ rfl]
    simp only [Fin.sum_univ_three, wordOp_diag_three, diagOp_zero_eq, diagOp_one_eq, diagOp_two_eq]
    simp only [comp_sub', DOp.comp_smul, one_eq_mono', mono_comp_mono, sub_comp', DOp.smul_comp, Finsupp.sub_apply,
      Finsupp.smul_apply, Finsupp.add_apply, mono_apply_eq, Prod.mk.injEq]
    simp only [Nat.reduceEqDiff, and_self, and_false, false_and, if_true, if_false, smul_zero, sub_zero, zero_sub,
      sub_neg_eq_add, sub_self, zero_add, add_zero, neg_zero]
    ext r s
    by_cases hrs : r = s
    · subst hrs
      simp only [scal_apply', if_true, map_ofNat, map_neg, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
        Matrix.one_apply_eq, Matrix.zero_apply]
      ring
    · simp only [scal_apply', hrs, if_false, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
        Matrix.one_apply_ne hrs, Matrix.zero_apply]
      ring

private theorem totalDegree_casOp_le (ab : ℕ × ℕ) (i i' : Fin n) :
    (casOp₂ S cω ab i i').totalDegree ≤ 3 ∧ (casOp₃ S cω ab i i').totalDegree ≤ 3 := by
  constructor
  · exact (DDeg.sum _ fun i _ => DDeg.sum _ fun j _ => (ddeg_wordOp S cω 2 _).mono (by norm_num)) ab i i'
  · exact (DDeg.sum _ fun i _ => DDeg.sum _ fun j _ => DDeg.sum _ fun k _ => ddeg_wordOp S cω 3 _) ab i i'

end Transport
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

section Walls

section WallScheme

private noncomputable def entryScal (n : ℕ) : Matrix (Fin 1) (Fin 1) Coef →+ Matrix (Fin n) (Fin n) Coef where
  toFun M := M 0 0 • (1 : Matrix (Fin n) (Fin n) Coef)
  map_zero' := by simp
  map_add' M N := by simp [add_smul]

private noncomputable def liftOp (n : ℕ) : DOp (Fin 1) →+ DOp (Fin n) := Finsupp.mapRange.addMonoidHom (entryScal n)

private theorem liftOp_apply (n : ℕ) (T : DOp (Fin 1)) (ab : ℕ × ℕ) :
    liftOp n T ab = T ab 0 0 • (1 : Matrix (Fin n) (Fin n) Coef) := by
  simp [liftOp, entryScal]

private theorem liftOp_single (n : ℕ) (ab : ℕ × ℕ) (M : Matrix (Fin 1) (Fin 1) Coef) :
    liftOp n (Finsupp.single ab M) = Finsupp.single ab (M 0 0 • (1 : Matrix (Fin n) (Fin n) Coef)) := by
  simp [liftOp, entryScal, Finsupp.mapRange_single]

private theorem liftOp_one (n : ℕ) : liftOp n (DOp.one : DOp (Fin 1)) = DOp.one := by
  simp [DOp.one, liftOp_single]

private theorem liftOp_smul (n : ℕ) (c : ℂ) (T : DOp (Fin 1)) : liftOp n (c • T) = c • liftOp n T := by
  ext ab i j
  simp [liftOp_apply, smul_smul, Matrix.one_apply]

private theorem smul_one_map_of_map_zero {f : Coef → Coef} (hf : f 0 = 0) (t : Coef) (m : ℕ) :
    ((t • (1 : Matrix (Fin m) (Fin m) Coef)).map f) = f t • (1 : Matrix (Fin m) (Fin m) Coef) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h, hf]

private theorem entry_smul_one_mul (a t : Coef) (m : ℕ) :
    (a • (1 : Matrix (Fin m) (Fin m) Coef)) * (t • (1 : Matrix (Fin m) (Fin m) Coef)) =
      (a * t) • (1 : Matrix (Fin m) (Fin m) Coef) := by
  rw [smul_mul_smul_comm, one_mul]

private theorem liftOp_map_sum (n : ℕ) (A : DOp (Fin 1)) (G : ℕ × ℕ → Matrix (Fin 1) (Fin 1) Coef → DOp (Fin 1)) :
    liftOp n (A.sum G) = A.sum fun ab a => liftOp n (G ab a) := by
  simp only [Finsupp.sum, map_sum]

private theorem liftOp_sum (n : ℕ) (A : DOp (Fin 1)) {β : Type} [AddCommMonoid β]
    (F : ℕ × ℕ → Matrix (Fin n) (Fin n) Coef → β) (hF : ∀ ab, F ab 0 = 0) :
    (liftOp n A).sum F = A.sum fun ab a => F ab (entryScal n a) := by
  rw [show liftOp n A = Finsupp.mapRange (entryScal n) (map_zero _) A from rfl]
  exact Finsupp.sum_mapRange_index hF

private theorem liftOp_comp (n : ℕ) (A T : DOp (Fin 1)) : liftOp n (comp A T) = comp (liftOp n A) (liftOp n T) := by
  simp only [DOp.comp]
  rw [liftOp_map_sum, liftOp_sum _ _ _ (fun ab => by simp)]
  refine Finsupp.sum_congr fun ab _ => ?_
  rw [liftOp_map_sum, liftOp_sum _ _ _ (fun cd => by simp [Matrix.map_zero _ (eulIt_zero _ _)])]
  refine Finsupp.sum_congr fun cd _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show liftOp n = Finsupp.mapRange.addMonoidHom (entryScal n) from rfl, Finsupp.mapRange.addMonoidHom_apply,
    Finsupp.mapRange_single]
  congr 1
  simp only [entryScal, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [smul_one_map_of_map_zero (eulIt_zero _ _), entry_smul_one_mul, Matrix.smul_apply, Matrix.mul_apply,
    Fin.sum_univ_one, Matrix.map_apply, smul_assoc]

private theorem liftOp_d₁ (n : ℕ) : liftOp n (d₁ : DOp (Fin 1)) = d₁ := by
  simp [d₁, liftOp_single]

private theorem liftOp_d₂ (n : ℕ) : liftOp n (d₂ : DOp (Fin 1)) = d₂ := by
  simp [d₂, liftOp_single]

private theorem cmul_zero_op {m : ℕ} (M : Matrix (Fin m) (Fin m) Coef) : cmul M (0 : DOp (Fin m)) = 0 := by
  ext ab i j
  simp [cmul_apply]

private theorem zero_cmul_op {m : ℕ} (D : DOp (Fin m)) : cmul (0 : Matrix (Fin m) (Fin m) Coef) D = 0 := by
  ext ab i j
  simp [cmul_apply]

private theorem cmul_smul_right {m : ℕ} (M : Matrix (Fin m) (Fin m) Coef) (c : ℂ) (D : DOp (Fin m)) :
    cmul M (c • D) = c • cmul M D := by
  ext ab i j
  simp [cmul_apply, Matrix.mul_smul]

private theorem liftOp_cmul_scalar (n : ℕ) (u : Coef) (T : DOp (Fin 1)) :
    cmul (u • (1 : Matrix (Fin n) (Fin n) Coef)) (liftOp n T) = liftOp n (cmul (u • (1 : Matrix (Fin 1)
    (Fin 1) Coef)) T) := by
  refine Finsupp.ext fun ab => ?_
  rw [cmul_apply, liftOp_apply, liftOp_apply, cmul_apply, entry_smul_one_mul, smul_one_mul, Matrix.smul_apply,
    smul_eq_mul]

private def Vp {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) (μ : ℕ) : Matrix (Fin n) (Fin n) Coef :=
    (V ^ μ).map MvPolynomial.C

private theorem Vp_zero {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) : Vp V 0 = 1 := by
  simp [Vp, Matrix.map_one]

private theorem Vp_succ {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) (μ : ℕ) : Vp V
    (μ + 1) = V.map MvPolynomial.C * Vp V μ := by
  simp only [Vp, pow_succ']
  exact Matrix.map_mul

private theorem Vp_map_eul {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) (μ : ℕ) (i : Fin 2) : (Vp V μ).map (eul i) = 0 := by
  ext a b
  simp [Vp, eul_C]

private def TForm {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (tab : ℕ → DOp (Fin 1)) (E : DOp (Fin n)) : Prop :=
  E = ∑ μ ∈ Finset.range m, cmul (Vp V μ) (liftOp n (tab μ))

private theorem tform_zero {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) : TForm V m 0 (0 : DOp (Fin n)) := by
  simp [TForm, cmul_zero_op]

private theorem tform_add {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ} {m : ℕ} {tab tab' : ℕ → DOp (Fin 1)}
    {E E' : DOp (Fin n)}
    (h : TForm V m tab E) (h' : TForm V m tab' E') : TForm V m (tab + tab') (E + E') := by
  unfold TForm at *
  rw [h, h', ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Pi.add_apply, map_add, cmul_add]

private theorem tform_smul {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ} {m : ℕ} {tab : ℕ → DOp (Fin 1)} {E : DOp (Fin n)}
    (c : ℂ) (h : TForm V m tab E) : TForm V m (c • tab) (c • E) := by
  unfold TForm at *
  rw [h, Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Pi.smul_apply, liftOp_smul, cmul_smul_right]

private theorem tform_sum {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ} {m : ℕ} {κ : Type} (s : Finset κ)
    {tab : κ → ℕ → DOp (Fin 1)}
    {E : κ → DOp (Fin n)} (h : ∀ k ∈ s, TForm V m (tab k) (E k)) : TForm V m (∑ k ∈ s, tab k) (∑ k ∈ s, E k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tform_zero V m
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk]
    exact tform_add (h k (Finset.mem_insert_self k s)) (ih fun k' hk' => h k' (Finset.mem_insert_of_mem hk'))

private theorem tform_comp_d₁ {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ} {m : ℕ} {tab : ℕ → DOp (Fin 1)} {E : DOp (Fin n)}
    (h : TForm V m tab E) : TForm V m (fun μ => comp d₁ (tab μ)) (comp d₁ E) := by
  unfold TForm at *
  rw [h, comp_finset_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [d₁_comp_cmul, Vp_map_eul, zero_cmul_op, zero_add, liftOp_comp, liftOp_d₁]

private theorem tform_comp_d₂ {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ} {m : ℕ} {tab : ℕ → DOp (Fin 1)} {E : DOp (Fin n)}
    (h : TForm V m tab E) : TForm V m (fun μ => comp d₂ (tab μ)) (comp d₂ E) := by
  unfold TForm at *
  rw [h, comp_finset_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [d₂_comp_cmul, Vp_map_eul, zero_cmul_op, zero_add, liftOp_comp, liftOp_d₂]

private theorem tform_cmul_scalar {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ} {m : ℕ} {tab : ℕ → DOp (Fin 1)}
    {E : DOp (Fin n)}
    (u : Coef) (h : TForm V m tab E) :
    TForm V m (fun μ => cmul (u • (1 : Matrix (Fin 1) (Fin 1) Coef)) (tab μ)) (cmul (u • (1 : Matrix (Fin n)
    (Fin n) Coef)) E) := by
  unfold TForm at *
  rw [h, cmul_finset_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [cmul_cmul, smul_one_mul, ← mul_smul_one, ← cmul_cmul, liftOp_cmul_scalar]

private def shiftTab (tab : ℕ → DOp (Fin 1)) : ℕ → DOp (Fin 1) := fun μ => if μ = 0 then 0 else tab (μ - 1)

private theorem tform_shift {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ} {m : ℕ} {tab : ℕ → DOp (Fin 1)} {E : DOp (Fin n)}
    (h : TForm V m tab E) : TForm V (m + 1) (shiftTab tab) (cmul (V.map MvPolynomial.C) E) := by
  unfold TForm at *
  rw [h, cmul_finset_sum, Finset.sum_range_succ']
  simp only [shiftTab, if_true, map_zero, cmul_zero_op, add_zero, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [cmul_cmul, Vp_succ]

private theorem tform_pad {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ} {m : ℕ} {tab : ℕ → DOp (Fin 1)} {E : DOp (Fin n)}
    (h : TForm V m tab E) (hm : tab m = 0) : TForm V (m + 1) tab E := by
  unfold TForm at *
  rw [Finset.sum_range_succ, hm, map_zero, cmul_zero_op, add_zero]
  exact h

private def oneTab : ℕ → DOp (Fin 1) := fun μ => if μ = 0 then DOp.one else 0

private theorem tform_one {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) : TForm V 1 oneTab (DOp.one : DOp (Fin n)) := by
  simp [TForm, oneTab, Vp_zero, liftOp_one, cmul_one_eq]

private def Fixed (φ : Coef →ₐ[ℂ] Coef) (tab : ℕ → DOp (Fin 1)) : Prop := ∀ μ, cmap φ (tab μ) = tab μ
private def Van (k : ℕ) (tab : ℕ → DOp (Fin 1)) : Prop := ∀ μ, k ≤ μ → tab μ = 0

private theorem cmap_zero' {m : ℕ} (φ : Coef →ₐ[ℂ] Coef) : cmap φ (0 : DOp (Fin m)) = 0 := by
  simp [cmap]

private theorem cmap_sub' {m : ℕ} (φ : Coef →ₐ[ℂ] Coef) (D D' : DOp (Fin m)) : cmap φ
    (D - D') = cmap φ D - cmap φ D' := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ D', cmap_add', cmap_smul', neg_one_smul, ← sub_eq_add_neg]

private theorem cmap_d₂' {m : ℕ} (φ : Coef →ₐ[ℂ] Coef) : cmap φ (d₂ : DOp (Fin m)) = d₂ := cmap_single_one φ _

private theorem phi_C (φ : Coef →ₐ[ℂ] Coef) (c : ℂ) : φ (MvPolynomial.C c) = MvPolynomial.C c := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]

private theorem map_C_map_phi {m : ℕ} (φ : Coef →ₐ[ℂ] Coef) (M : Matrix (Fin m) (Fin m) ℂ) :
    (M.map MvPolynomial.C).map φ = M.map MvPolynomial.C := by
  ext i j
  simp [phi_C]

private theorem cmap_diagOp {m : ℕ} (φ : Coef →ₐ[ℂ] Coef) (hφ : ∀ i j : ℕ, ⇑φ ∘ eulIt i j = eulIt i j ∘ ⇑φ) (cω : ℂ)
    (a : Fin 3) (D : DOp (Fin m)) : cmap φ (diagOp cω a D) = diagOp cω a (cmap φ D) := by
  unfold diagOp
  split_ifs <;> simp only [cmap_sub', cmap_smul', cmap_comp_of_comm φ hφ, cmap_d₁', cmap_d₂']

private theorem diagOp_zero {m : ℕ} (cω : ℂ) (a : Fin 3) : diagOp cω a (0 : DOp (Fin m)) = 0 := by
  unfold diagOp
  split_ifs <;> simp [comp_zero']

private def diagTab (cω : ℂ) (a : Fin 3) (tab : ℕ → DOp (Fin 1)) : ℕ → DOp (Fin 1) := fun μ => diagOp cω a (tab μ)
private def scalTab (u : Coef) (tab : ℕ → DOp (Fin 1)) : ℕ → DOp (Fin 1) :=
  fun μ => cmul (u • (1 : Matrix (Fin 1) (Fin 1) Coef)) (tab μ)

private theorem cmul_sub_right {m : ℕ} (M : Matrix (Fin m) (Fin m) Coef) (D D' : DOp (Fin m)) :
    cmul M (D - D') = cmul M D - cmul M D' := by
  refine Finsupp.ext fun ab => ?_
  rw [cmul_apply, Finsupp.sub_apply, Finsupp.sub_apply, cmul_apply, cmul_apply, Matrix.mul_sub]

private theorem tform_sub {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ} {m : ℕ} {tab tab' : ℕ → DOp (Fin 1)}
    {E E' : DOp (Fin n)} (h : TForm V m tab E) (h' : TForm V m tab' E') : TForm V m (tab - tab') (E - E') := by
  unfold TForm at *
  rw [h, h', ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Pi.sub_apply, map_sub, cmul_sub_right]

private theorem tform_diagTab {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ} {m : ℕ} {tab : ℕ → DOp (Fin 1)} {E : DOp (Fin n)}
    (cω : ℂ) (a : Fin 3) (h : TForm V m tab E) : TForm V m (diagTab cω a tab) (diagOp cω a E) := by
  unfold diagTab diagOp
  split_ifs
  · exact tform_comp_d₁ h
  · exact tform_sub (tform_comp_d₂ h) (tform_comp_d₁ h)
  · exact tform_sub (tform_smul cω h) (tform_comp_d₂ h)

private theorem tform_scalTab {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ} {m : ℕ} {tab : ℕ → DOp (Fin 1)} {E : DOp (Fin n)}
    (u : Coef) (h : TForm V m tab E) : TForm V m (scalTab u tab) (cmul (u • (1 : Matrix (Fin n) (Fin n) Coef)) E) :=
  tform_cmul_scalar u h

private theorem fixed_zero (φ : Coef →ₐ[ℂ] Coef) : Fixed φ 0 := fun _ => cmap_zero' φ
private theorem fixed_oneTab (φ : Coef →ₐ[ℂ] Coef) : Fixed φ oneTab := fun μ => by
  unfold oneTab; split_ifs
  · exact cmap_one' φ
  · exact cmap_zero' φ
private theorem fixed_add {φ : Coef →ₐ[ℂ] Coef} {t t' : ℕ → DOp (Fin 1)} (h : Fixed φ t) (h' : Fixed φ t') :
    Fixed φ (t + t') := fun μ => by
  rw [Pi.add_apply, cmap_add', h, h']
private theorem fixed_smul {φ : Coef →ₐ[ℂ] Coef} {t : ℕ → DOp (Fin 1)} (c : ℂ) (h : Fixed φ t) : Fixed φ
    (c • t) := fun μ => by
  rw [Pi.smul_apply, cmap_smul', h]
private theorem fixed_sum {φ : Coef →ₐ[ℂ] Coef} {κ : Type} (s : Finset κ) {t : κ → ℕ → DOp (Fin 1)}
    (h : ∀ k ∈ s, Fixed φ (t k)) : Fixed φ (∑ k ∈ s, t k) := fun μ => by
  rw [Finset.sum_apply, cmap_finset_sum]
  exact Finset.sum_congr rfl fun k hk => h k hk μ
private theorem fixed_diagTab {φ : Coef →ₐ[ℂ] Coef} (hφ : ∀ i j : ℕ, ⇑φ ∘ eulIt i j = eulIt i j ∘ ⇑φ) (cω : ℂ)
    (a : Fin 3)
    {t : ℕ → DOp (Fin 1)} (h : Fixed φ t) : Fixed φ (diagTab cω a t) := fun μ => by
  unfold diagTab
  rw [cmap_diagOp φ hφ, h]
private theorem fixed_scalTab {φ : Coef →ₐ[ℂ] Coef} {u : Coef} (hu : φ u = u) {t : ℕ → DOp (Fin 1)} (h : Fixed φ t) :
    Fixed φ (scalTab u t) := fun μ => by
  unfold scalTab
  rw [cmap_cmul_hom, h, smul_one_map_of_map_zero (map_zero φ), hu]
private theorem fixed_shiftTab {φ : Coef →ₐ[ℂ] Coef} {t : ℕ → DOp (Fin 1)} (h : Fixed φ t) : Fixed φ
    (shiftTab t) := fun μ => by
  unfold shiftTab
  split_ifs
  · exact cmap_zero' φ
  · exact h _
private theorem fixed_ite {φ : Coef →ₐ[ℂ] Coef} {P : Prop} [Decidable P] {t : ℕ → DOp (Fin 1)} (h : P → Fixed φ t) :
    Fixed φ (if P then t else 0) := by
  split_ifs with hP
  · exact h hP
  · exact fixed_zero φ

private theorem van_zero (k : ℕ) : Van k 0 := fun _ _ => rfl
private theorem van_oneTab : Van 1 oneTab := fun μ hμ => by
  unfold oneTab; rw [if_neg (by omega)]
private theorem van_add {k : ℕ} {t t' : ℕ → DOp (Fin 1)} (h : Van k t) (h' : Van k t') : Van k (t + t')
    := fun μ hμ => by
  rw [Pi.add_apply, h μ hμ, h' μ hμ, add_zero]
private theorem van_smul {k : ℕ} {t : ℕ → DOp (Fin 1)} (c : ℂ) (h : Van k t) : Van k (c • t) := fun μ hμ => by
  rw [Pi.smul_apply, h μ hμ, smul_zero]
private theorem van_sum {k : ℕ} {κ : Type} (s : Finset κ) {t : κ → ℕ → DOp (Fin 1)} (h : ∀ j ∈ s, Van k (t j)) :
    Van k (∑ j ∈ s, t j) := fun μ hμ => by
  rw [Finset.sum_apply]
  exact Finset.sum_eq_zero fun j hj => h j hj μ hμ
private theorem van_diagTab {k : ℕ} (cω : ℂ) (a : Fin 3) {t : ℕ → DOp (Fin 1)} (h : Van k t) : Van k
    (diagTab cω a t) :=
  fun μ hμ => by unfold diagTab; rw [h μ hμ, diagOp_zero]
private theorem van_scalTab {k : ℕ} (u : Coef) {t : ℕ → DOp (Fin 1)} (h : Van k t) : Van k (scalTab u t)
    := fun μ hμ => by
  unfold scalTab; rw [h μ hμ, cmul_zero_op]
private theorem van_shiftTab {k : ℕ} {t : ℕ → DOp (Fin 1)} (h : Van k t) : Van (k + 1) (shiftTab t) := fun μ hμ => by
  unfold shiftTab
  split_ifs
  · rfl
  · exact h _ (by omega)
private theorem van_succ {k : ℕ} {t : ℕ → DOp (Fin 1)} (h : Van k t) : Van (k + 1) t := fun μ hμ => h μ (by omega)
private theorem van_ite {k : ℕ} {P : Prop} [Decidable P] {t : ℕ → DOp (Fin 1)} (h : P → Van k t) :
    Van k (if P then t else 0) := by
  split_ifs with hP
  · exact h hP
  · exact van_zero k

private theorem tform_pad_of_van {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ} {k : ℕ} {tab : ℕ → DOp (Fin 1)} {E
    : DOp (Fin n)}
    (h : TForm V k tab E) (hv : Van k tab) : TForm V (k + 1) tab E :=
  tform_pad h (hv k le_rfl)

private def IsPos (ν : ℤ × ℤ) : Prop := 0 < ν.1 ∨ 0 < ν.2

private theorem isPos_add_of_nonneg {ν δ : ℤ × ℤ} (h : IsPos ν) (hδ : 0 ≤ δ.1 ∧ 0 ≤ δ.2) : IsPos (ν + δ) := by
  rcases h with h | h
  · exact Or.inl (by simp only [Prod.fst_add]; omega)
  · exact Or.inr (by simp only [Prod.snd_add]; omega)

private theorem isPos_neg_of_nonpos_ne {ν : ℤ × ℤ} (h : ν.1 ≤ 0 ∧ ν.2 ≤ 0) (hν : ν ≠ 0) : IsPos (-ν) := by
  by_contra hc
  apply hν
  simp only [IsPos, Prod.fst_neg, Prod.snd_neg, not_or, not_lt] at hc
  exact Prod.ext (by simp only [Prod.fst_zero]; omega) (by simp only [Prod.snd_zero]; omega)

private theorem eq_zero_of_not_isPos_of_nonneg {ν : ℤ × ℤ} (h : ¬ IsPos ν) (hν : 0 ≤ ν.1 ∧ 0 ≤ ν.2) : ν = 0 := by
  simp only [IsPos, not_or, not_lt] at h
  exact Prod.ext (by simp only [Prod.fst_zero]; omega) (by simp only [Prod.snd_zero]; omega)

private theorem ne_zero_of_isPos {ν : ℤ × ℤ} (h : IsPos ν) : ν ≠ 0 := by
  rintro rfl
  simp [IsPos] at h

private structure WallData where
  φ : Coef →ₐ[ℂ] Coef
  hφ : ∀ i j : ℕ, ⇑φ ∘ eulIt i j = eulIt i j ∘ ⇑φ
  f : Fin 3 → ℤ × ℤ
  f_anti : ∀ x y : Fin 3, y < x → (f x - f y).1 ≤ 0 ∧ (f x - f y).2 ≤ 0
  V : (n : ℕ) → (Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) → Matrix (Fin n) (Fin n) ℂ
  upper_pos : ∀ a b : Fin 3, a < b → IsPos (f a - f b) → ∀ (n : ℕ) (D : DOp (Fin n)), cmap φ (upperOp (a, b) D) = 0
  upper_zero : ∀ a b : Fin 3, a < b → f a - f b = 0 → ∃ u : Coef, φ u = u ∧
    ∀ (n : ℕ) (D : DOp (Fin n)), cmap φ (upperOp (a, b) D) = cmul (u • (1 : Matrix (Fin n) (Fin n) Coef)) (cmap φ D)
  lower_zero : ∀ a b : Fin 3, b < a → f a - f b = 0 →
    ∀ (n : ℕ) (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ), S a b = V n S

private def WallData.wt (W : WallData) (ab : Fin 3 × Fin 3) : ℤ × ℤ := W.f ab.1 - W.f ab.2

private def WallData.wsum (W : WallData) {ℓ : ℕ} (w : Fin ℓ → Fin 3 × Fin 3) : ℤ × ℤ := ∑ p, W.wt (w p)

private theorem WallData.wsum_zero (W : WallData) (w : Fin 0 → Fin 3 × Fin 3) : W.wsum w = 0 := by
  simp [WallData.wsum]

private theorem WallData.wsum_succ (W : WallData) {ℓ : ℕ} (w : Fin (ℓ + 1) → Fin 3 × Fin 3) :
    W.wsum w = W.wt (w 0) + W.wsum (Fin.tail w) := by
  simp only [WallData.wsum, Fin.sum_univ_succ, Fin.tail]

private theorem WallData.wsum_update (W : WallData) {ℓ : ℕ} (w : Fin ℓ → Fin 3 × Fin 3) (p : Fin ℓ) (e
    : Fin 3 × Fin 3) :
    W.wsum (Function.update w p e) = W.wsum w - W.wt (w p) + W.wt e := by
  unfold WallData.wsum
  rw [Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_univ p) (fun q => W.wt (w q))]
  rw [show (∑ q, W.wt (Function.update w p e q)) = ∑ q, Function.update (W.wt ∘ w) p (W.wt e) q from
    Finset.sum_congr rfl fun q _ => by rw [← Function.comp_update]; rfl]
  rw [Finset.sum_update_of_mem (Finset.mem_univ p)]
  simp only [Function.comp]
  abel

private theorem WallData.wt_swap (W : WallData) (a b : Fin 3) : W.wt (b, a) = -W.wt (a, b) := by
  simp [WallData.wt]

private theorem WallData.wt_diag (W : WallData) (a : Fin 3) : W.wt (a, a) = 0 := by
  simp [WallData.wt]

private theorem WallData.wt_lower_nonpos (W : WallData) {a b : Fin 3} (h : b < a) : (W.wt (a, b)).1 ≤ 0 ∧
    (W.wt (a, b)).2 ≤ 0 :=
  W.f_anti a b h

private theorem WallData.wt_upper_nonneg (W : WallData) {a b : Fin 3} (h : a < b) : 0 ≤ (W.wt (a, b)).1 ∧ 0 ≤
    (W.wt (a, b)).2 := by
  have := W.wt_lower_nonpos h
  rw [W.wt_swap] at this
  simp only [Prod.fst_neg, Prod.snd_neg] at this
  omega

private theorem WallData.br (W : WallData) (a b : Fin 3) (cd ef : Fin 3 × Fin 3) (h : brCoeff a b cd ef ≠ 0) :
    W.wt ef = W.wt (a, b) + W.wt cd ∨ W.wt ef = W.wt (b, a) + W.wt cd := by
  by_cases h1 : b = cd.1 ∧ ef = (a, cd.2)
  · obtain ⟨hb, rfl⟩ := h1
    left; simp only [WallData.wt, hb]; abel
  by_cases h2 : cd.2 = a ∧ ef = (cd.1, b)
  · obtain ⟨ha, rfl⟩ := h2
    left; simp only [WallData.wt, ← ha]; abel
  by_cases h3 : a = cd.1 ∧ ef = (b, cd.2)
  · obtain ⟨ha, rfl⟩ := h3
    right; simp only [WallData.wt, ha]; abel
  by_cases h4 : cd.2 = b ∧ ef = (cd.1, a)
  · obtain ⟨hb, rfl⟩ := h4
    right; simp only [WallData.wt, ← hb]; abel
  exact absurd (by simp [brCoeff, h1, h2, h3, h4]) h

private theorem wall_invariant (W : WallData) (cω : ℂ) : ∀ (ℓ : ℕ) (w : Fin ℓ → Fin 3 × Fin 3),
    (IsPos (W.wsum w) → ∀ (n : ℕ) (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ), cmap W.φ (wordOp S cω ℓ w) = 0) ∧
    ∃ tab : ℕ → DOp (Fin 1), Fixed W.φ tab ∧ Van (ℓ + 1) tab ∧
      (W.wsum w = 0 → ∀ (n : ℕ) (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ),
        TForm (W.V n S) (ℓ + 1) tab (cmap W.φ (wordOp S cω ℓ w))) ∧
      (W.wsum w ≠ 0 → tab = 0) := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro w
    refine ⟨fun h => absurd h (by rw [W.wsum_zero]; simp [IsPos]), oneTab, fixed_oneTab _, van_oneTab, fun _ n S => ?_,
      fun h => absurd (W.wsum_zero w) h⟩
    rw [wordOp_zero_eq, cmap_one']
    exact tform_one _
  | succ ℓ ih =>
    intro w
    choose tabOf hfix hvan hform hjunk using fun v => (ih v).2
    have ihz : ∀ v, IsPos (W.wsum v) → ∀ (n : ℕ) (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ),
        cmap W.φ (wordOp S cω ℓ v) = 0 := fun v => (ih v).1
    set w' := Fin.tail w with hw'
    set ab := w 0 with hab0
    obtain ⟨a, b⟩ := ab
    have hwsw : W.wsum w = W.wt (a, b) + W.wsum w' := by rw [W.wsum_succ, ← hab0]
    rcases lt_trichotomy a b with hlt | rfl | hgt
    ·
      have hval : ∀ (n : ℕ) (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ),
          wordOp S cω (ℓ + 1) w = upperOp (a, b) (wordOp S cω ℓ w') := fun n S => by
        rw [wordOp_succ, ← hab0]
        simp only [letterOp, hlt.ne, hlt, if_false, if_true]
        rfl
      by_cases hp : IsPos (W.f a - W.f b)
      · have hz := W.upper_pos a b hlt hp
        refine ⟨fun _ n S => ?_, 0, fixed_zero _, van_zero _, fun _ n S => ?_, fun _ => rfl⟩
        · rw [hval, hz]
        · rw [hval, hz]
          exact tform_zero _ _
      · have h0 : W.f a - W.f b = 0 := eq_zero_of_not_isPos_of_nonneg hp (W.wt_upper_nonneg hlt)
        have hws : W.wsum w = W.wsum w' := by
          rw [hwsw, show W.wt (a, b) = 0 from h0, zero_add]
        obtain ⟨u, hu, hU⟩ := W.upper_zero a b hlt h0
        refine ⟨fun hpos n S => ?_, if W.wsum w = 0 then scalTab u (tabOf w') else 0,
          fixed_ite fun _ => fixed_scalTab hu (hfix w'), van_ite fun _ => van_succ (van_scalTab u (hvan w')),
          fun hz n S => ?_, fun hnz => if_neg hnz⟩
        · have hpos' : IsPos (W.wsum w') := hws ▸ hpos
          rw [hval, hU, ihz w' hpos', cmul_zero_op]
        · have hz' : W.wsum w' = 0 := hws ▸ hz
          rw [if_pos hz, hval, hU]
          exact tform_pad_of_van (tform_scalTab u (hform w' hz' n S)) (van_scalTab u (hvan w'))
    ·
      have hval : ∀ (n : ℕ) (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ),
          cmap W.φ (wordOp S cω (ℓ + 1) w) = diagOp cω a (cmap W.φ (wordOp S cω ℓ w')) := fun n S => by
        rw [wordOp_succ, ← hab0]
        simp only [letterOp, if_true]
        exact cmap_diagOp W.φ W.hφ cω a _
      have hws : W.wsum w = W.wsum w' := by rw [hwsw, W.wt_diag, zero_add]
      refine ⟨fun hpos n S => ?_, if W.wsum w = 0 then diagTab cω a (tabOf w') else 0,
        fixed_ite fun _ => fixed_diagTab W.hφ cω a (hfix w'), van_ite fun _ => van_succ (van_diagTab cω a (hvan w')),
        fun hz n S => ?_, fun hnz => if_neg hnz⟩
      · have hpos' : IsPos (W.wsum w') := hws ▸ hpos
        rw [hval, ihz w' hpos', diagOp_zero]
      · have hz' : W.wsum w' = 0 := hws ▸ hz
        rw [if_pos hz, hval]
        exact tform_pad_of_van (tform_diagTab cω a (hform w' hz' n S)) (van_diagTab cω a (hvan w'))
    ·
      have hval : ∀ (n : ℕ) (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ),
          cmap W.φ (wordOp S cω (ℓ + 1) w) = cmap W.φ (upperOp (b, a) (wordOp S cω ℓ w'))
            + cmul ((S a b).map MvPolynomial.C) (cmap W.φ (wordOp S cω ℓ w'))
            + ∑ p : Fin ℓ, ∑ ef : Fin 3 × Fin 3,
                brCoeff a b (w' p) ef • cmap W.φ (wordOp S cω ℓ (Function.update w' p ef)) := fun n S => by
        rw [wordOp_succ, ← hab0]
        simp only [letterOp, hgt.ne', not_lt.2 hgt.le, if_false]
        rw [cmap_add', cmap_add', cmap_cmul_hom, map_C_map_phi, cmap_finset_sum]
        simp only [cmap_finset_sum, cmap_smul']
        rfl
      have hlow := W.wt_lower_nonpos hgt
      have hba_nonneg := W.wt_upper_nonneg hgt
      by_cases h0 : W.wt (a, b) = 0
      ·
        have hws : W.wsum w = W.wsum w' := by rw [hwsw, h0, zero_add]
        have hba : W.wt (b, a) = 0 := by rw [W.wt_swap, h0, neg_zero]
        obtain ⟨u, hu, hU⟩ := W.upper_zero b a hgt hba
        have hS := W.lower_zero a b hgt h0
        have hbr : ∀ (p : Fin ℓ) (ef : Fin 3 × Fin 3), brCoeff a b (w' p) ef ≠ 0 →
            W.wsum (Function.update w' p ef) = W.wsum w' := by
          intro p ef hne
          rw [W.wsum_update]
          rcases W.br a b (w' p) ef hne with h | h <;> rw [h]
          · rw [h0, zero_add, sub_add_cancel]
          · rw [hba, zero_add, sub_add_cancel]
        refine ⟨fun hpos n S => ?_, if W.wsum w = 0 then scalTab u (tabOf w') + shiftTab (tabOf w')
            + ∑ p : Fin ℓ, ∑ ef : Fin 3 × Fin 3, brCoeff a b (w' p) ef • tabOf (Function.update w' p ef) else 0,
          fixed_ite fun _ => fixed_add (fixed_add (fixed_scalTab hu (hfix w')) (fixed_shiftTab (hfix w')))
            (fixed_sum _ fun p _ => fixed_sum _ fun ef _ => fixed_smul _ (hfix _)),
          van_ite fun _ => van_add (van_add (van_succ (van_scalTab u (hvan w'))) (van_shiftTab (hvan w')))
            (van_sum _ fun p _ => van_sum _ fun ef _ => van_succ (van_smul _ (hvan _))),
          fun hz n S => ?_, fun hnz => if_neg hnz⟩
        · have hpos' : IsPos (W.wsum w') := hws ▸ hpos
          rw [hval, hU, ihz w' hpos', cmul_zero_op, cmul_zero_op, zero_add, zero_add]
          refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun ef _ => ?_
          by_cases hne : brCoeff a b (w' p) ef = 0
          · rw [hne, zero_smul]
          · rw [ihz _ (by rw [hbr p ef hne]; exact hpos'), smul_zero]
        · have hz' : W.wsum w' = 0 := hws ▸ hz
          rw [if_pos hz, hval, hU, hS n S]
          refine tform_add (tform_add (tform_pad_of_van (tform_scalTab u (hform w' hz' n S)) (van_scalTab u (hvan w')))
            (tform_shift (hform w' hz' n S))) (tform_sum _ fun p _ => tform_sum _ fun ef _ => ?_)
          by_cases hne : brCoeff a b (w' p) ef = 0
          · rw [hne, zero_smul, zero_smul]
            exact tform_zero _ _
          · exact tform_pad_of_van (tform_smul _ (hform _ (by rw [hbr p ef hne, hz']) n S)) (van_smul _ (hvan _))
      ·
        have hba_pos : IsPos (W.wt (b, a)) := by rw [W.wt_swap]; exact isPos_neg_of_nonpos_ne hlow h0
        have hupper := W.upper_pos b a hgt hba_pos
        have hws' : W.wsum w' = W.wsum w + W.wt (b, a) := by rw [hwsw, W.wt_swap a b]; abel
        have hbr : ∀ (p : Fin ℓ) (ef : Fin 3 × Fin 3), brCoeff a b (w' p) ef ≠ 0 →
            W.wsum (Function.update w' p ef) = W.wsum w ∨
              W.wsum (Function.update w' p ef) = W.wsum w + W.wt (b, a) + W.wt (b, a) := by
          intro p ef hne
          rw [W.wsum_update, hws']
          rcases W.br a b (w' p) ef hne with h | h <;> rw [h]
          · left; rw [W.wt_swap a b]; abel
          · right; abel
        refine ⟨fun hpos n S => ?_,
          if W.wsum w = 0 then ∑ p : Fin ℓ, ∑ ef : Fin 3 × Fin 3, brCoeff a b (w' p) ef • tabOf
    (Function.update w' p ef)
            else 0,
          fixed_ite fun _ => fixed_sum _ fun p _ => fixed_sum _ fun ef _ => fixed_smul _ (hfix _),
          van_ite fun _ => van_sum _ fun p _ => van_sum _ fun ef _ => van_succ (van_smul _ (hvan _)),
          fun hz n S => ?_, fun hnz => if_neg hnz⟩
        · have hpos' : IsPos (W.wsum w') := by rw [hws']; exact isPos_add_of_nonneg hpos hba_nonneg
          rw [hval, hupper, ihz w' hpos', cmul_zero_op, add_zero, zero_add]
          refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun ef _ => ?_
          by_cases hne : brCoeff a b (w' p) ef = 0
          · rw [hne, zero_smul]
          · rcases hbr p ef hne with h | h
            · rw [ihz _ (by rw [h]; exact hpos), smul_zero]
            · rw [ihz _ (by rw [h]; exact isPos_add_of_nonneg (isPos_add_of_nonneg hpos hba_nonneg) hba_nonneg),
                smul_zero]
        · have hpos' : IsPos (W.wsum w') := by rw [hws', hz, zero_add]; exact hba_pos
          rw [if_pos hz, hval, hupper, ihz w' hpos', cmul_zero_op, add_zero, zero_add]
          refine tform_sum _ fun p _ => tform_sum _ fun ef _ => ?_
          by_cases hne : brCoeff a b (w' p) ef = 0
          · rw [hne, zero_smul, zero_smul]
            exact tform_zero _ _
          · rcases hbr p ef hne with h | h
            · exact tform_pad_of_van (tform_smul _ (hform _ (by rw [h, hz]) n S)) (van_smul _ (hvan _))
            · have hp2 : IsPos (W.wsum (Function.update w' p ef)) := by
                rw [h, hz, zero_add]; exact isPos_add_of_nonneg hba_pos hba_nonneg
              rw [hjunk _ (ne_zero_of_isPos hp2), ihz _ hp2 n S, smul_zero, smul_zero]
              exact tform_zero _ _

private theorem WallData.wsum_word2 (W : WallData) (i j : Fin 3) : W.wsum ![(i, j), (j, i)] = 0 := by
  simp only [WallData.wsum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, WallData.wt]
  abel

private theorem WallData.wsum_word3 (W : WallData) (i j k : Fin 3) : W.wsum ![(i, j), (j, k), (k, i)] = 0 := by
  simp only [WallData.wsum, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, WallData.wt]
  abel

private theorem wall_casOp (W : WallData) (cω : ℂ) : ∃ tab₂ tab₃ : ℕ → DOp (Fin 1), Fixed W.φ tab₂ ∧ Fixed W.φ tab₃ ∧
    ∀ (n : ℕ) (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ),
      TForm (W.V n S) 4 tab₂ (cmap W.φ (casOp₂ S cω)) ∧ TForm (W.V n S) 4 tab₃ (cmap W.φ (casOp₃ S cω)) := by
  choose tab₂ hfix₂ hvan₂ hform₂ _ using fun v : Fin 2 → Fin 3 × Fin 3 => (wall_invariant W cω 2 v).2
  choose tab₃ hfix₃ _ hform₃ _ using fun v : Fin 3 → Fin 3 × Fin 3 => (wall_invariant W cω 3 v).2
  refine ⟨∑ i : Fin 3, ∑ j : Fin 3, tab₂ ![(i, j), (j, i)],
    ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, tab₃ ![(i, j), (j, k), (k, i)],
    fixed_sum _ fun i _ => fixed_sum _ fun j _ => hfix₂ _,
    fixed_sum _ fun i _ => fixed_sum _ fun j _ => fixed_sum _ fun k _ => hfix₃ _, fun n S => ⟨?_, ?_⟩⟩
  · unfold casOp₂
    simp only [cmap_finset_sum]
    exact tform_sum _ fun i _ => tform_sum _ fun j _ =>
      tform_pad_of_van (hform₂ _ (W.wsum_word2 i j) n S) (hvan₂ _)
  · unfold casOp₃
    simp only [cmap_finset_sum]
    exact tform_sum _ fun i _ => tform_sum _ fun j _ => tform_sum _ fun k _ => hform₃ _ (W.wsum_word3 i j k) n S

private theorem tform_entry {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ} {m : ℕ} {tab : ℕ → DOp (Fin 1)} {E : DOp (Fin n)}
    (h : TForm V m tab E) (ab : ℕ × ℕ) :
    E ab = ∑ μ : Fin m, (tab μ ab 0 0) • ((V ^ (μ : ℕ)).map MvPolynomial.C) := by
  unfold TForm at h
  rw [h, Finsupp.finset_sum_apply, ← Finset.sum_range fun k => (tab k ab 0 0) • ((V ^ k).map MvPolynomial.C)]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [cmul_apply, liftOp_apply, Matrix.mul_smul, mul_one]
  rfl

private theorem fixed_entry {φ : Coef →ₐ[ℂ] Coef} {tab : ℕ → DOp (Fin 1)} (h : Fixed φ tab) (ab : ℕ × ℕ) (μ : ℕ) :
    φ (tab μ ab 0 0) = tab μ ab 0 0 := by
  have := congrArg (fun D : DOp (Fin 1) => D ab 0 0) (h μ)
  simpa [cmap_apply] using this

private theorem wall_entries (W : WallData) (cω : ℂ) : ∃ p₂ p₃ : ℕ × ℕ → Fin 4 → Coef,
    (∀ ab μ, W.φ (p₂ ab μ) = p₂ ab μ) ∧ (∀ ab μ, W.φ (p₃ ab μ) = p₃ ab μ) ∧
      ∀ (n : ℕ) (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (ab : ℕ × ℕ),
        (casOp₂ S cω ab).map W.φ = ∑ μ : Fin 4, p₂ ab μ • ((W.V n S) ^ (μ : ℕ)).map MvPolynomial.C ∧
          (casOp₃ S cω ab).map W.φ = ∑ μ : Fin 4, p₃ ab μ • ((W.V n S) ^ (μ : ℕ)).map MvPolynomial.C := by
  obtain ⟨tab₂, tab₃, hf₂, hf₃, hT⟩ := wall_casOp W cω
  refine ⟨fun ab μ => tab₂ μ ab 0 0, fun ab μ => tab₃ μ ab 0 0, fun ab μ => fixed_entry hf₂ ab μ,
    fun ab μ => fixed_entry hf₃ ab μ, fun n S ab => ⟨?_, ?_⟩⟩
  · rw [← cmap_apply, tform_entry (hT n S).1 ab]
  · rw [← cmap_apply, tform_entry (hT n S).2 ab]

private theorem killX1_X0 : killX1 (MvPolynomial.X 0) = MvPolynomial.X 0 := by simp [killX1]
private theorem killX1_X1 : killX1 (MvPolynomial.X 1) = 0 := by simp [killX1]

private theorem killX1_eul1 (p : Coef) : killX1 (eul 1 p) = 0 := by
  simp [killX1, eul]

private theorem killX1_eul0 (p : Coef) : killX1 (eul 0 p) = eul 0 (killX1 p) := by
  have key : ∀ q : Coef, killX1 (MvPolynomial.pderiv 0 q) = MvPolynomial.pderiv 0 (killX1 q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => simp [killX1]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p j hp =>
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hp]
      fin_cases j <;> simp [killX1, MvPolynomial.pderiv_X]
  simp only [eul, map_mul, key]
  simp [killX1]

private theorem pderiv1_killX1 (p : Coef) : MvPolynomial.pderiv 1 (killX1 p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [killX1]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
    rw [killX1, map_mul, MvPolynomial.aeval_X]
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, Derivation.leibniz, smul_eq_mul]
      rw [MvPolynomial.pderiv_X_of_ne (by decide)]
      simpa [killX1] using hp
    · simp

private theorem eul1_killX1 (p : Coef) : eul 1 (killX1 p) = 0 := by
  simp [eul, pderiv1_killX1]

private theorem killX1_iterate_eul0 (p : Coef) : ∀ i : ℕ, killX1 ((eul 0)^[i] p) = (eul 0)^[i] (killX1 p)
  | 0 => rfl
  | i + 1 => by rw [Function.iterate_succ_apply', killX1_eul0, killX1_iterate_eul0 p i, Function.iterate_succ_apply']

private theorem killX1_comp_eulIt (i j : ℕ) : ⇑killX1 ∘ eulIt i j = eulIt i j ∘ ⇑killX1 := by
  funext p
  simp only [Function.comp_apply, eulIt]
  cases j with
  | zero => simpa using killX1_iterate_eul0 p i
  | succ j =>
    rw [Function.iterate_succ_apply', killX1_iterate_eul0, killX1_eul1, iterate_eul_zero, Function.iterate_succ_apply,
      eul1_killX1, iterate_eul_zero, iterate_eul_zero]

private theorem upperOp_01 {n : ℕ} (D : DOp (Fin n)) :
    upperOp (0, 1) D = cmul ((MvPolynomial.C twoPiI * MvPolynomial.X 0 : Coef) • (1 : Matrix (Fin n)
    (Fin n) Coef)) D := by
  simp [upperOp]
private theorem upperOp_12 {n : ℕ} (D : DOp (Fin n)) :
    upperOp (1, 2) D = cmul ((MvPolynomial.C twoPiI * MvPolynomial.X 1 : Coef) • (1 : Matrix (Fin n)
    (Fin n) Coef)) D := by
  simp [upperOp]
private theorem upperOp_02 {n : ℕ} (D : DOp (Fin n)) : upperOp (0, 2) D = 0 := by
  simp [upperOp]

private theorem cmap_upper_of_kills {n : ℕ} (φ : Coef →ₐ[ℂ] Coef) {u : Coef} (hu : φ u = 0) (D : DOp (Fin n)) :
    cmap φ (cmul (u • (1 : Matrix (Fin n) (Fin n) Coef)) D) = 0 := by
  rw [cmap_cmul_hom, smul_one_map_of_map_zero (map_zero φ), hu, zero_smul, zero_cmul_op]

private theorem cmap_upper_of_fixes {n : ℕ} (φ : Coef →ₐ[ℂ] Coef) {u : Coef} (hu : φ u = u) (D : DOp (Fin n)) :
    cmap φ (cmul (u • (1 : Matrix (Fin n) (Fin n) Coef)) D) = cmul (u • (1 : Matrix (Fin n) (Fin n) Coef))
    (cmap φ D) := by
  rw [cmap_cmul_hom, smul_one_map_of_map_zero (map_zero φ), hu]

private theorem killX0_upper01 {n : ℕ} (D : DOp (Fin n)) : cmap killX0 (upperOp (0, 1) D) = 0 := by
  rw [upperOp_01]; exact cmap_upper_of_kills _ (by simp [killX0]) D
private theorem killX0_upper12 {n : ℕ} (D : DOp (Fin n)) : cmap killX0 (upperOp (1, 2) D) =
    cmul ((MvPolynomial.C twoPiI * MvPolynomial.X 1 : Coef) • (1 : Matrix (Fin n) (Fin n) Coef)) (cmap killX0 D) := by
  rw [upperOp_12]; exact cmap_upper_of_fixes _ (by simp [killX0]) D
private theorem killX1_upper12 {n : ℕ} (D : DOp (Fin n)) : cmap killX1 (upperOp (1, 2) D) = 0 := by
  rw [upperOp_12]; exact cmap_upper_of_kills _ (by simp [killX1]) D
private theorem killX1_upper01 {n : ℕ} (D : DOp (Fin n)) : cmap killX1 (upperOp (0, 1) D) =
    cmul ((MvPolynomial.C twoPiI * MvPolynomial.X 0 : Coef) • (1 : Matrix (Fin n) (Fin n) Coef)) (cmap killX1 D) := by
  rw [upperOp_01]; exact cmap_upper_of_fixes _ (by simp [killX1]) D
private theorem constHom_upper01 {n : ℕ} (D : DOp (Fin n)) : cmap constHom (upperOp (0, 1) D) = 0 := by
  rw [upperOp_01]; exact cmap_upper_of_kills _ (by simp [constHom_apply]) D
private theorem constHom_upper12 {n : ℕ} (D : DOp (Fin n)) : cmap constHom (upperOp (1, 2) D) = 0 := by
  rw [upperOp_12]; exact cmap_upper_of_kills _ (by simp [constHom_apply]) D
private theorem cmap_upper02 {n : ℕ} (φ : Coef →ₐ[ℂ] Coef) (D : DOp (Fin n)) : cmap φ (upperOp (0, 2) D) = 0 := by
  rw [upperOp_02]; exact cmap_zero' _

private noncomputable def wallX0Data : WallData where
  φ := killX0
  hφ := killX0_comp_eulIt
  f := ![(1, 0), 0, 0]
  f_anti := by decide
  V := fun _ S => S 2 1
  upper_pos := by
    intro a b hab hpos n D
    fin_cases a <;> fin_cases b <;> simp at hab <;> simp [IsPos] at hpos
    exacts [killX0_upper01 D, cmap_upper02 _ D]
  upper_zero := by
    intro a b hab h0
    fin_cases a <;> fin_cases b <;> simp at hab <;> simp [Prod.ext_iff] at h0
    exact ⟨MvPolynomial.C twoPiI * MvPolynomial.X 1, by simp [killX0], fun n D => killX0_upper12 D⟩
  lower_zero := by
    intro a b hba h0 n S
    fin_cases a <;> fin_cases b <;> simp at hba <;> simp [Prod.ext_iff] at h0
    rfl

private noncomputable def wallX1Data : WallData where
  φ := killX1
  hφ := killX1_comp_eulIt
  f := ![0, 0, (0, -1)]
  f_anti := by decide
  V := fun _ S => S 1 0
  upper_pos := by
    intro a b hab hpos n D
    fin_cases a <;> fin_cases b <;> simp at hab <;> simp [IsPos] at hpos
    exacts [cmap_upper02 _ D, killX1_upper12 D]
  upper_zero := by
    intro a b hab h0
    fin_cases a <;> fin_cases b <;> simp at hab <;> simp [Prod.ext_iff] at h0
    exact ⟨MvPolynomial.C twoPiI * MvPolynomial.X 0, by simp [killX1], fun n D => killX1_upper01 D⟩
  lower_zero := by
    intro a b hba h0 n S
    fin_cases a <;> fin_cases b <;> simp at hba <;> simp [Prod.ext_iff] at h0
    rfl

private noncomputable def wall00Data : WallData where
  φ := constHom
  hφ := constHom_comp_eulIt
  f := ![(1, 0), 0, (0, -1)]
  f_anti := by decide
  V := fun _ _ => 0
  upper_pos := by
    intro a b hab hpos n D
    fin_cases a <;> fin_cases b <;> simp at hab <;> simp [IsPos] at hpos
    exacts [constHom_upper01 D, cmap_upper02 _ D, constHom_upper12 D]
  upper_zero := by
    intro a b hab h0
    fin_cases a <;> fin_cases b <;> simp at hab <;> simp [Prod.ext_iff] at h0
  lower_zero := by
    intro a b hba h0 n S
    fin_cases a <;> fin_cases b <;> simp at hba <;> simp [Prod.ext_iff] at h0

private theorem sum_zero_pow_smul {n : ℕ} (t : Fin 4 → Coef) :
    (∑ μ : Fin 4, t μ • (((0 : Matrix (Fin n) (Fin n) ℂ) ^ (μ : ℕ)).map MvPolynomial.C)) =
      t 0 • (1 : Matrix (Fin n) (Fin n) Coef) := by
  simp [Fin.sum_univ_four, Matrix.map_one MvPolynomial.C (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _)]

private theorem map_constantCoeff_of_map_constHom {n : ℕ} {M : Matrix (Fin n) (Fin n) Coef} {t : Coef}
    (h : M.map constHom = t • (1 : Matrix (Fin n) (Fin n) Coef)) :
    M.map MvPolynomial.constantCoeff = MvPolynomial.constantCoeff t • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  have hij := congrFun (congrFun h i) j
  rw [Matrix.map_apply, constHom_apply] at hij
  have := congrArg MvPolynomial.constantCoeff hij
  rw [MvPolynomial.constantCoeff_C] at this
  rw [Matrix.map_apply, this]
  by_cases hh : i = j <;> simp [Matrix.one_apply, hh]

end WallScheme
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

private theorem exists_casOp_wall00 (cω : ℂ) : ∃ ω₂ ω₃ : ℕ × ℕ → ℂ,
    ∀ (n : ℕ) (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (ab : ℕ × ℕ),
      (casOp₂ S cω ab).map MvPolynomial.constantCoeff = ω₂ ab • (1 : Matrix (Fin n) (Fin n) ℂ) ∧
        (casOp₃ S cω ab).map MvPolynomial.constantCoeff = ω₃ ab • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  obtain ⟨p₂, p₃, -, -, h⟩ := wall_entries wall00Data cω
  refine ⟨fun ab => MvPolynomial.constantCoeff (p₂ ab 0), fun ab => MvPolynomial.constantCoeff (p₃ ab 0),
    fun n S ab => ?_⟩
  obtain ⟨h2, h3⟩ := h n S ab
  have e2 : (casOp₂ S cω ab).map constHom = p₂ ab 0 • (1 : Matrix (Fin n) (Fin n) Coef) := by
    rw [show (casOp₂ S cω ab).map constHom = (casOp₂ S cω ab).map wall00Data.φ from rfl, h2]
    exact sum_zero_pow_smul _
  have e3 : (casOp₃ S cω ab).map constHom = p₃ ab 0 • (1 : Matrix (Fin n) (Fin n) Coef) := by
    rw [show (casOp₃ S cω ab).map constHom = (casOp₃ S cω ab).map wall00Data.φ from rfl, h3]
    exact sum_zero_pow_smul _
  exact ⟨map_constantCoeff_of_map_constHom e2, map_constantCoeff_of_map_constHom e3⟩

private theorem exists_casOp_wallX0 (cω : ℂ) : ∃ (m : ℕ) (p₂ p₃ : ℕ × ℕ → Fin m → Coef),
    (∀ ab μ, killX0 (p₂ ab μ) = p₂ ab μ) ∧ (∀ ab μ, killX0 (p₃ ab μ) = p₃ ab μ) ∧
      ∀ (n : ℕ) (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (ab : ℕ × ℕ),
        (casOp₂ S cω ab).map killX0 = ∑ μ : Fin m, p₂ ab μ • ((S 2 1) ^ (μ : ℕ)).map MvPolynomial.C ∧
          (casOp₃ S cω ab).map killX0 = ∑ μ : Fin m, p₃ ab μ • ((S 2 1) ^ (μ : ℕ)).map MvPolynomial.C := by
  obtain ⟨p₂, p₃, h₂, h₃, h⟩ := wall_entries wallX0Data cω
  exact ⟨4, p₂, p₃, h₂, h₃, h⟩

private theorem exists_casOp_wallX1 (cω : ℂ) : ∃ (m : ℕ) (p₂ p₃ : ℕ × ℕ → Fin m → Coef),
    (∀ ab μ, killX1 (p₂ ab μ) = p₂ ab μ) ∧ (∀ ab μ, killX1 (p₃ ab μ) = p₃ ab μ) ∧
      ∀ (n : ℕ) (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (ab : ℕ × ℕ),
        (casOp₂ S cω ab).map killX1 = ∑ μ : Fin m, p₂ ab μ • ((S 1 0) ^ (μ : ℕ)).map MvPolynomial.C ∧
          (casOp₃ S cω ab).map killX1 = ∑ μ : Fin m, p₃ ab μ • ((S 1 0) ^ (μ : ℕ)).map MvPolynomial.C := by
  obtain ⟨p₂, p₃, h₂, h₃, h⟩ := wall_entries wallX1Data cω
  exact ⟨4, p₂, p₃, h₂, h₃, h⟩

end Walls
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

section Extension

variable {n : ℕ}

private theorem iwK_mem_GLs {x : M3} (hx : x ∈ GLs) : iwK x ∈ GLs := by
  have h := congrArg Matrix.det (iwK_orth hx)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  intro h0
  rw [h0, mul_zero] at h
  exact zero_ne_one h

private theorem contDiffOn_uniChar_iwN : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : M3 => uniChar (iwN x)) GLs := by
  have hN : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => iwN x i j) GLs :=
    fun i j => contDiffOn_pi.1 (contDiffOn_pi.1 contDiffOn_iwN i) j
  have hsum : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (iwN x 0 1 + iwN x 1 2 : ℝ)) GLs := (hN 0 1).add (hN 1 2)
  have hof : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => ((iwN x 0 1 + iwN x 1 2 : ℝ) : ℂ)) GLs :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hsum
  exact Complex.contDiff_exp.comp_contDiffOn (contDiffOn_const.mul hof)

private theorem contDiffOn_iwA_apply (i : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => iwA x i) GLs :=
  contDiffOn_pi.1 contDiffOn_iwA i

private theorem contDiffOn_log_iwA (i : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => Real.log (iwA x i)) GLs :=
  (contDiffOn_iwA_apply i).log fun _ hx => (iwA_pos hx i).ne'

private theorem contDiffOn_centralFactor (cω : ℂ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : M3 => Complex.exp (cω * ((Real.log (iwA x 2) : ℝ) : ℂ))) GLs := by
  have hof : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : M3 => ((Real.log (iwA x 2) : ℝ) : ℂ)) GLs :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_log_iwA 2)
  exact Complex.contDiff_exp.comp_contDiffOn (contDiffOn_const.mul hof)

private def lg₁ (x : M3) : ℝ := Real.log (iwA x 0) - Real.log (iwA x 1)

private def lg₂ (x : M3) : ℝ := Real.log (iwA x 1) - Real.log (iwA x 2)

private theorem contDiffOn_lg₁ : ContDiffOn ℝ (⊤ : ℕ∞) lg₁ GLs := (contDiffOn_log_iwA 0).sub (contDiffOn_log_iwA 1)

private theorem contDiffOn_lg₂ : ContDiffOn ℝ (⊤ : ℕ∞) lg₂ GLs := (contDiffOn_log_iwA 1).sub (contDiffOn_log_iwA 2)

private def extW (σ : M3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ) (G : ℝ → ℝ → (Fin n → ℂ)) (x : M3) : Fin n → ℂ :=
  (uniChar (iwN x) * Complex.exp (cω * ((Real.log (iwA x 2) : ℝ) : ℂ))) • (G (lg₁ x) (lg₂ x) ᵥ* σ (iwK x))

private theorem contDiffOn_vecMul {v : M3 → (Fin n → ℂ)} {M : M3 → Matrix (Fin n) (Fin n) ℂ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v GLs) (hM : ContDiffOn ℝ (⊤ : ℕ∞) M GLs) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => v x ᵥ* M x) GLs := by
  refine contDiffOn_pi.2 fun j => ?_
  have h : (fun x => (v x ᵥ* M x) j) = fun x => ∑ i, v x i * M x i j := by
    funext x
    rfl
  rw [h]
  exact ContDiffOn.sum fun i _ => (contDiffOn_pi.1 hv i).mul (contDiffOn_pi.1 (contDiffOn_pi.1 hM i) j)

private theorem contDiffOn_extW (σ : M3 → Matrix (Fin n) (Fin n) ℂ) (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ GLs) (cω : ℂ)
    (G : ℝ → ℝ → (Fin n → ℂ)) (hG : Smooth2 G) : ContDiffOn ℝ (⊤ : ℕ∞) (extW σ cω G) GLs := by
  have hGl : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => G (lg₁ x) (lg₂ x)) GLs :=
    hG.comp_contDiffOn (contDiffOn_lg₁.prodMk contDiffOn_lg₂)
  have hσK : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => σ (iwK x)) GLs :=
    hσ.comp contDiffOn_iwK fun _ hx => iwK_mem_GLs hx
  refine contDiffOn_pi.2 fun j => ?_
  have h : (fun x => extW σ cω G x j) = fun x =>
      (uniChar (iwN x) * Complex.exp (cω * ((Real.log (iwA x 2) : ℝ) : ℂ))) * (G (lg₁ x) (lg₂ x) ᵥ* σ (iwK x)) j := by
    funext x
    rfl
  rw [h]
  exact (contDiffOn_uniChar_iwN.mul (contDiffOn_centralFactor cω)).mul (contDiffOn_pi.1 (contDiffOn_vecMul hGl hσK) j)

private theorem extW_uni (σ : M3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ) (G : ℝ → ℝ → (Fin n → ℂ)) {n' x : M3}
    (hn' : IsUpperUni n') (hx : x ∈ GLs) : extW σ cω G (n' * x) = uniChar n' • extW σ cω G x := by
  obtain ⟨hN, hA, hK⟩ := iw_uni_mul hn' hx
  simp only [extW, lg₁, lg₂, hN, hA, hK, uniChar_mul hn' (isUpperUni_iwN x), smul_smul, mul_assoc]

private theorem extW_orth (σ : M3 → Matrix (Fin n) (Fin n) ℂ)
    (hσm : ∀ k k' : M3, kᵀ * k = 1 → k'ᵀ * k' = 1 → σ (k * k') = σ k * σ k') (cω : ℂ) (G : ℝ → ℝ → (Fin n → ℂ))
    {x k : M3} (hx : x ∈ GLs) (hk : kᵀ * k = 1) : extW σ cω G (x * k) = extW σ cω G x ᵥ* σ k := by
  obtain ⟨hN, hA, hK⟩ := iw_mul_orth hx hk
  simp only [extW, lg₁, lg₂, hN, hA, hK, hσm _ _ (iwK_orth hx) hk, ← Matrix.vecMul_vecMul, Matrix.smul_vecMul]

private theorem extW_smul (σ : M3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ) (G : ℝ → ℝ → (Fin n → ℂ)) {c : ℝ}
    (hc : 0 < c) {x : M3} (hx : x ∈ GLs) :
    extW σ cω G (c • x) = Complex.exp (cω * ((Real.log c : ℝ) : ℂ)) • extW σ cω G x := by
  obtain ⟨hN, hA, hK⟩ := iw_smul hc hx
  have ha : ∀ i, 0 < iwA x i := iwA_pos hx
  have hl : ∀ i, Real.log ((c • iwA x) i) = Real.log c + Real.log (iwA x i) := fun i => by
    rw [Pi.smul_apply, smul_eq_mul, Real.log_mul hc.ne' (ha i).ne']
  simp only [extW, lg₁, lg₂, hN, hA, hK, hl, smul_smul]
  congr 1
  · push_cast
    rw [mul_add, Complex.exp_add]
    ring
  · congr 2 <;> ring

private theorem extW_torus (σ : M3 → Matrix (Fin n) (Fin n) ℂ) (hσ1 : σ 1 = 1) (cω : ℂ) (G : ℝ → ℝ → (Fin n → ℂ))
    (t₁ t₂ : ℝ) : extW σ cω G (torus (Real.exp t₁) (Real.exp t₂)) = G t₁ t₂ := by
  obtain ⟨hN, hA, hK⟩ := iw_torus (Real.exp_pos t₁) (Real.exp_pos t₂)
  simp only [extW, lg₁, lg₂, hN, hA, hK, hσ1, uniChar_one, Matrix.vecMul_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Real.log_mul (Real.exp_pos t₁).ne' (Real.exp_pos t₂).ne', Real.log_exp, Real.log_one, add_sub_cancel_right,
    sub_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, one_smul]

private theorem extW_centre (σ : M3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ) (G : ℝ → ℝ → (Fin n → ℂ)) {x : M3}
    (hx : x ∈ GLs) : rD 1 (extW σ cω G) x = cω • extW σ cω G x := by
  have hcurve : ∀ s : ℝ, x * (1 + s • (1 : M3)) = (1 + s) • x := fun s => by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_one, add_smul, one_smul]
  have hev : (fun s : ℝ => extW σ cω G (x * (1 + s • (1 : M3)))) =ᶠ[nhds 0]
      fun s => Complex.exp (cω * ((Real.log (1 + s) : ℝ) : ℂ)) • extW σ cω G x := by
    have hopen : IsOpen {s : ℝ | 0 < 1 + s} := isOpen_lt continuous_const (continuous_const.add continuous_id)
    filter_upwards [hopen.mem_nhds (show (0 : ℝ) ∈ {s : ℝ | 0 < 1 + s} by simp)] with s hs
    rw [hcurve s, extW_smul σ cω G hs hx]
  have hder : HasDerivAt (fun s : ℝ => Complex.exp (cω * ((Real.log (1 + s) : ℝ) : ℂ)) • extW σ cω G x)
      (cω • extW σ cω G x) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => Real.log (1 + s)) 1 0 := by
      have h := (Real.hasDerivAt_log (show (1 : ℝ) + 0 ≠ 0 by norm_num)).comp 0
        ((hasDerivAt_id (0 : ℝ)).const_add 1)
      simpa [Function.comp_def] using h
    have h2 : HasDerivAt (fun s : ℝ => cω * ((Real.log (1 + s) : ℝ) : ℂ)) (cω * 1) 0 := h1.ofReal_comp.const_mul cω
    have h3 : HasDerivAt (fun s : ℝ => Complex.exp (cω * ((Real.log (1 + s) : ℝ) : ℂ))) cω 0 := by
      have h := h2.cexp
      simpa using h
    refine hasDerivAt_pi.2 fun j => ?_
    simpa only [Pi.smul_apply, smul_eq_mul] using h3.mul_const (extW σ cω G x j)
  rw [rD, hev.deriv_eq, hder.deriv]

private theorem exists_transforming_extension (σ : M3 → Matrix (Fin n) (Fin n) ℂ) (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ GLs)
    (hσ1 : σ 1 = 1) (hσm : ∀ k k' : M3, kᵀ * k = 1 → k'ᵀ * k' = 1 → σ (k * k') = σ k * σ k') (cω : ℂ)
    (G : ℝ → ℝ → (Fin n → ℂ)) (hG : Smooth2 G) :
    ∃ W : M3 → (Fin n → ℂ), ContDiffOn ℝ (⊤ : ℕ∞) W GLs ∧
      (∀ n' x : M3, IsUpperUni n' → x ∈ GLs → W (n' * x) = uniChar n' • W x) ∧
      (∀ x k : M3, x ∈ GLs → kᵀ * k = 1 → W (x * k) = W x ᵥ* σ k) ∧
      (∀ x ∈ GLs, rD 1 W x = cω • W x) ∧
      ∀ t₁ t₂ : ℝ, W (torus (Real.exp t₁) (Real.exp t₂)) = G t₁ t₂ :=
  ⟨extW σ cω G, contDiffOn_extW σ hσ cω G hG, fun _ _ hn' hx => extW_uni σ cω G hn' hx,
    fun _ _ hx hk => extW_orth σ hσm cω G hx hk, fun _ hx => extW_centre σ cω G hx,
    fun t₁ t₂ => extW_torus σ hσ1 cω G t₁ t₂⟩

end Extension
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

section Weights

variable {n : ℕ}

private def rotC (a b : Fin 3) (s : ℝ) : M3 := 1 + Real.sin s • (E a b - E b a) + (Real.cos s - 1) • (E a a + E b b)

section SkewCurve

private theorem E_transpose (a b : Fin 3) : (E a b)ᵀ = E b a := by
  simp [E, Matrix.transpose_single]

private theorem rotC_zero (a b : Fin 3) : rotC a b 0 = 1 := by
  simp [rotC]

private theorem hasDerivAt_rotC_zero (a b : Fin 3) : HasDerivAt (rotC a b) (E a b - E b a) 0 := by
  have h1 := (Real.hasDerivAt_sin 0).smul_const (E a b - E b a)
  have h2 := ((Real.hasDerivAt_cos 0).sub_const 1).smul_const (E a a + E b b)
  have h := (h1.add h2).const_add (1 : M3)
  simp only [Real.cos_zero, one_smul, Real.sin_zero, neg_zero, zero_smul, add_zero] at h
  have hr : rotC a b = fun s => 1 + (Real.sin s • (E a b - E b a) + (Real.cos s - 1) • (E a a + E b b)) := by
    funext s
    rw [rotC, add_assoc]
  rw [hr]
  exact h

private theorem lin_mul {a b : Fin 3} (hab : a ≠ b) (α β α' β' : ℝ) :
    (1 + α • (E a b - E b a) + β • (E a a + E b b)) * (1 + α' • (E a b - E b a) + β' • (E a a + E b b)) =
      1 + (α + α' + α * β' + β * α') • (E a b - E b a) + (β + β' - α * α' + β * β') • (E a a + E b b) := by
  have hba : b ≠ a := fun h => hab h.symm
  have hZZ : (E a b - E b a) * (E a b - E b a) = -(E a a + E b b) := by
    simp only [sub_mul, mul_sub, E_mul_E, hab, hba, if_false, if_true]
    abel
  have hZP : (E a b - E b a) * (E a a + E b b) = E a b - E b a := by
    simp only [sub_mul, mul_add, E_mul_E, hab, hba, if_false, if_true]
    abel
  have hPZ : (E a a + E b b) * (E a b - E b a) = E a b - E b a := by
    simp only [add_mul, mul_sub, E_mul_E, hab, hba, if_false, if_true]
    abel
  have hPP : (E a a + E b b) * (E a a + E b b) = E a a + E b b := by
    simp only [add_mul, mul_add, E_mul_E, hab, hba, if_false, if_true]
    abel
  set Z : M3 := E a b - E b a with hZdef
  set P : M3 := E a a + E b b with hPdef
  simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hZZ, hZP, hPZ, hPP,
    smul_neg]
  module

private theorem rotC_orth {a b : Fin 3} (hab : a ≠ b) (s : ℝ) : (rotC a b s)ᵀ * rotC a b s = 1 := by
  have ht : (rotC a b s)ᵀ = 1 + (-Real.sin s) • (E a b - E b a) + (Real.cos s - 1) • (E a a + E b b) := by
    simp only [rotC, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_sub,
      E_transpose]
    module
  rw [ht, rotC, lin_mul hab]
  have h1 : -Real.sin s + Real.sin s + -Real.sin s * (Real.cos s - 1) + (Real.cos s - 1) * Real.sin s = 0 := by ring
  have h2 :
      Real.cos s - 1 + (Real.cos s - 1) - -Real.sin s * Real.sin s + (Real.cos s - 1) * (Real.cos s - 1) = 0 := by
    linear_combination Real.sin_sq_add_cos_sq s
  rw [h1, h2, zero_smul, zero_smul, add_zero, add_zero]

private theorem rotC_mem_GLs {a b : Fin 3} (hab : a ≠ b) (s : ℝ) : rotC a b s ∈ GLs := by
  have h := congrArg Matrix.det (rotC_orth hab s)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  intro h0
  rw [h0, mul_zero] at h
  exact zero_ne_one h

private theorem rotC_add {a b : Fin 3} (hab : a ≠ b) (s t : ℝ) : rotC a b (s + t) = rotC a b s * rotC a b t := by
  simp only [rotC]
  rw [lin_mul hab, Real.sin_add, Real.cos_add]
  have h1 : Real.sin s + Real.sin t + Real.sin s * (Real.cos t - 1) + (Real.cos s - 1) * Real.sin t =
      Real.sin s * Real.cos t + Real.cos s * Real.sin t := by ring
  have h2 : Real.cos s - 1 + (Real.cos t - 1) - Real.sin s * Real.sin t + (Real.cos s - 1) * (Real.cos t - 1) =
      Real.cos s * Real.cos t - Real.sin s * Real.sin t - 1 := by ring
  rw [h1, h2]

private theorem rotC_two_pi (a b : Fin 3) : rotC a b (2 * Real.pi) = 1 := by
  simp [rotC]

private def soData (σ : M3 → Matrix (Fin n) (Fin n) ℂ) (a b : Fin 3) : Matrix (Fin n) (Fin n) ℂ :=
    (rD (E a b - E b a) σ 1)ᵀ

private noncomputable def conjOp (U : Matrix (Fin n) (Fin n) ℂ) (D : DOp (Fin n)) : DOp (Fin n) :=
  Finsupp.mapRange (fun M => U.map MvPolynomial.C * M * U⁻¹.map MvPolynomial.C) (by simp) D

private noncomputable def diagEntry {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (D : DOp ι) : DOp Unit :=
  Finsupp.mapRange (fun M => fun _ _ => M i i) rfl D

private theorem rotC_comm {a b : Fin 3} (hab : a ≠ b) (s t : ℝ) : rotC a b s * rotC a b t = rotC a b t * rotC a b s :=
    by
  rw [← rotC_add hab, ← rotC_add hab, add_comm]

end SkewCurve
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

private theorem rD_skew_eq_soData_mulVec (σ : M3 → Matrix (Fin n) (Fin n) ℂ) (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ GLs)
    {W : M3 → (Fin n → ℂ)} (hW : ContDiffOn ℝ (⊤ : ℕ∞) W GLs)
    (hK : ∀ x k : M3, x ∈ GLs → kᵀ * k = 1 → W (x * k) = W x ᵥ* σ k) {x : M3} (hx : x ∈ GLs) (a b : Fin 3)
    (hab : b < a) : rD (E a b - E b a) W x = soData σ a b *ᵥ W x := by
  have hne : a ≠ b := fun h => (lt_irrefl b) (h ▸ hab)
  have hR0 : rotC a b 0 = 1 := rotC_zero a b
  have hRd : HasDerivAt (rotC a b) (E a b - E b a) 0 := hasDerivAt_rotC_zero a b
  have h1 : (1 : M3) ∈ GLs := by simp [GLs]
  have hWd : DifferentiableAt ℝ W x := differentiableAt_of_contDiffOn hW hx
  have hσd : DifferentiableAt ℝ σ 1 := differentiableAt_of_contDiffOn hσ h1

  have hL : HasDerivAt (fun s => W (x * rotC a b s)) (fderiv ℝ W x (x * (E a b - E b a))) 0 := by
    have hc : HasDerivAt (fun s => x * rotC a b s) (x * (E a b - E b a)) 0 := by
      have h := (mulLeftL x).hasFDerivAt.comp_hasDerivAt 0 hRd
      simp only [Function.comp_def, mulLeftL_apply] at h
      exact h
    exact hWd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hc (by rw [hR0, Matrix.mul_one])

  have hσR : HasDerivAt (fun s => σ (rotC a b s)) (fderiv ℝ σ 1 (E a b - E b a)) 0 :=
    hσd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hRd (by rw [hR0])
  have hRt : HasDerivAt (fun s => W x ᵥ* σ (rotC a b s)) (W x ᵥ* fderiv ℝ σ 1 (E a b - E b a)) 0 := by
    refine hasDerivAt_pi.2 fun j => ?_
    have hij : ∀ i, HasDerivAt (fun s => σ (rotC a b s) i j) (fderiv ℝ σ 1 (E a b - E b a) i j) 0 :=
      fun i => hasDerivAt_pi.1 (hasDerivAt_pi.1 hσR i) j
    have hs := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hij i).const_mul (W x i)
    simpa only [Matrix.vecMul, dotProduct] using hs
  have hg : (fun s => W (x * rotC a b s)) = fun s => W x ᵥ* σ (rotC a b s) :=
    funext fun s => hK x _ hx (rotC_orth hne s)
  rw [hg] at hL
  have hr : rD (E a b - E b a) σ 1 = fderiv ℝ σ 1 (E a b - E b a) :=
    (rD_eq_fderiv _ hσd).trans (congrArg _ (Matrix.one_mul _))
  calc rD (E a b - E b a) W x = fderiv ℝ W x (x * (E a b - E b a)) := rD_eq_fderiv _ hWd
    _ = W x ᵥ* fderiv ℝ σ 1 (E a b - E b a) := hL.unique hRt
    _ = soData σ a b *ᵥ W x := by rw [← hr]; exact (Matrix.mulVec_transpose _ _).symm

private theorem hasDerivAt_vecMul_of_hasDerivAt {f : ℝ → Matrix (Fin n) (Fin n) ℂ} {D : Matrix (Fin n) (Fin n) ℂ}
    {s : ℝ} (hf : HasDerivAt f D s) (v : Fin n → ℂ) : HasDerivAt (fun t => v ᵥ* f t) (v ᵥ* D) s := by
  refine hasDerivAt_pi.2 fun j => ?_
  have hij : ∀ i, HasDerivAt (fun t => f t i j) (D i j) s := fun i => hasDerivAt_pi.1 (hasDerivAt_pi.1 hf i) j
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hij i).const_mul (v i)
  simpa only [Matrix.vecMul, dotProduct] using hs

private theorem hasDerivAt_const_mul_mat {f : ℝ → Matrix (Fin n) (Fin n) ℂ} {D : Matrix (Fin n) (Fin n) ℂ} {s : ℝ}
    (hf : HasDerivAt f D s) (M : Matrix (Fin n) (Fin n) ℂ) : HasDerivAt (fun t => M * f t) (M * D) s := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  have hkj : ∀ k, HasDerivAt (fun t => f t k j) (D k j) s := fun k => hasDerivAt_pi.1 (hasDerivAt_pi.1 hf k) j
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun k _ => (hkj k).const_mul (M i k)
  simpa only [Matrix.mul_apply] using hs

private theorem hasDerivAt_mul_const_mat {f : ℝ → Matrix (Fin n) (Fin n) ℂ} {D : Matrix (Fin n) (Fin n) ℂ} {s : ℝ}
    (hf : HasDerivAt f D s) (M : Matrix (Fin n) (Fin n) ℂ) : HasDerivAt (fun t => f t * M) (D * M) s := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  have hik : ∀ k, HasDerivAt (fun t => f t i k) (D i k) s := fun k => hasDerivAt_pi.1 (hasDerivAt_pi.1 hf i) k
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun k _ => (hik k).mul_const (M k j)
  simpa only [Matrix.mul_apply] using hs

private theorem hasDerivAt_expneg (μ : ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (-(μ * (t : ℂ)))) (-μ * Complex.exp (-(μ * (s : ℂ)))) s := by
  have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 s := (hasDerivAt_id' s).ofReal_comp
  have h1 : HasDerivAt (fun t : ℝ => -(μ * (t : ℂ))) (-μ) s := by
    have h := (h0.const_mul μ).neg
    simpa only [mul_one, Pi.neg_def] using h
  have h2 := h1.cexp
  convert h2 using 1
  all_goals try rfl
  ring

private theorem no_chain_of_periodic {g : ℝ → Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin n) (Fin n) ℂ} (hg0 : g 0 = 1)
    (hg2π : g (2 * Real.pi) = 1) (hrow : ∀ (v : Fin n → ℂ) (s : ℝ), HasDerivAt (fun t => v ᵥ* g t) ((v ᵥ* B) ᵥ* g s) s)
    (μ : ℂ) (v₁ v₂ : Fin n → ℂ) (hv₁ : v₁ ᵥ* B = μ • v₁) (hv₂ : v₂ ᵥ* B = μ • v₂ + v₁) : v₁ = 0 := by
  have hψ₁ : ∀ (j : Fin n) (s : ℝ), Complex.exp (-(μ * (s : ℂ))) * (v₁ ᵥ* g s) j = v₁ j := by
    intro j
    have hd : ∀ s : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(μ * (t : ℂ))) * (v₁ ᵥ* g t) j) 0 s := by
      intro s
      have hv := hasDerivAt_pi.1 (hrow v₁ s) j
      rw [hv₁, Matrix.smul_vecMul] at hv
      have h := (hasDerivAt_expneg μ s).mul hv
      convert h using 1
      all_goals try rfl
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    intro s
    have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) s 0
    rw [hc, hg0, Matrix.vecMul_one]
    simp
  have hψ₁' : ∀ (j : Fin n) (s : ℝ), (v₁ ᵥ* g s) j = Complex.exp (μ * (s : ℂ)) * v₁ j := by
    intro j s
    have hE : Complex.exp (μ * (s : ℂ)) * Complex.exp (-(μ * (s : ℂ))) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    calc (v₁ ᵥ* g s) j = Complex.exp (μ * (s : ℂ)) * (Complex.exp (-(μ * (s : ℂ))) * (v₁ ᵥ* g s) j) := by
          rw [← mul_assoc, hE, one_mul]
      _ = Complex.exp (μ * (s : ℂ)) * v₁ j := by rw [hψ₁ j s]
  have hψ₂ : ∀ (j : Fin n) (s : ℝ), Complex.exp (-(μ * (s : ℂ))) * (v₂ ᵥ* g s) j - (s : ℂ) * v₁ j = v₂ j := by
    intro j
    have hd : ∀ s : ℝ,
        HasDerivAt (fun t : ℝ => Complex.exp (-(μ * (t : ℂ))) * (v₂ ᵥ* g t) j - (t : ℂ) * v₁ j) 0 s := by
      intro s
      have hv := hasDerivAt_pi.1 (hrow v₂ s) j
      rw [hv₂, Matrix.add_vecMul, Matrix.smul_vecMul] at hv
      have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 s := (hasDerivAt_id' s).ofReal_comp
      have h := ((hasDerivAt_expneg μ s).mul hv).sub (h0.mul_const (v₁ j))
      have hE : Complex.exp (-(μ * (s : ℂ))) * Complex.exp (μ * (s : ℂ)) = 1 := by
        rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
      convert h using 1
      all_goals try rfl
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hψ₁' j s]
      linear_combination (-(v₁ j)) * hE
    intro s
    have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) s 0
    rw [hc, hg0, Matrix.vecMul_one]
    simp
  by_contra hne0
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hne0
  rw [Pi.zero_apply] at hj
  have hper : Complex.exp (μ * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
    have h := hψ₁' j (2 * Real.pi)
    rw [hg2π, Matrix.vecMul_one] at h
    exact (mul_right_cancel₀ hj ((one_mul (v₁ j)).trans h)).symm
  have h2 := hψ₂ j (2 * Real.pi)
  rw [hg2π, Matrix.vecMul_one, Complex.exp_neg, hper, inv_one, one_mul, sub_eq_self, mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · have h2π : (2 * Real.pi : ℝ) ≠ 0 := (mul_pos two_pos Real.pi_pos).ne'
    exact h2π (Complex.ofReal_eq_zero.1 h2)
  · exact hj h2

private theorem exists_conj_eq_diagonal_of_no_chain (A : Matrix (Fin n) (Fin n) ℂ)
    (hcol : ∀ (μ : ℂ) (v₁ v₂ : Fin n → ℂ), A *ᵥ v₁ = μ • v₁ → A *ᵥ v₂ = μ • v₂ + v₁ → v₁ = 0) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (zw : Fin n → ℂ), IsUnit U.det ∧ U * A * U⁻¹ = Matrix.diagonal zw := by
  let T : Module.End ℂ (Fin n → ℂ) := Matrix.toLin' A
  have hT : ∀ v, T v = A *ᵥ v := fun v => Matrix.toLin'_apply A v
  have hgen : ∀ (μ : ℂ) (k : ℕ) (m : Fin n → ℂ), ((T - μ • 1) ^ k) m = 0 → (T - μ • 1) m = 0 := by
    intro μ k
    induction k with
    | zero =>
      intro m hm
      rw [pow_zero, Module.End.one_apply] at hm
      rw [hm, map_zero]
    | succ k ih =>
      intro m hm
      rw [pow_succ, Module.End.mul_apply] at hm
      have h1 := ih _ hm
      have e₁ : A *ᵥ ((T - μ • 1) m) = μ • (T - μ • 1) m := by
        rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero, hT] at h1
        exact h1
      have e₂ : A *ᵥ m = μ • m + (T - μ • 1) m := by
        rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hT]
        abel
      exact hcol μ _ m e₁ e₂
  have hmax : ∀ μ, T.maxGenEigenspace μ ≤ T.eigenspace μ := by
    intro μ m hm
    rw [Module.End.mem_maxGenEigenspace] at hm
    obtain ⟨k, hk⟩ := hm
    rw [Module.End.mem_eigenspace_iff]
    have h := hgen μ k m hk
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h
    exact h
  have htop : ⨆ μ, T.eigenspace μ = ⊤ :=
    top_le_iff.1 ((Module.End.iSup_maxGenEigenspace_eq_top T).symm.le.trans (iSup_mono hmax))
  let S : Set (Fin n → ℂ) := ⋃ μ, (T.eigenspace μ : Set (Fin n → ℂ))
  have hspan : Submodule.span ℂ S = ⊤ := by
    rw [Submodule.span_iUnion]
    simp only [Submodule.span_eq]
    exact htop
  obtain ⟨bs, hbsS, hbspan, hli⟩ := exists_linearIndependent ℂ S
  haveI : Fintype bs := hli.setFinite.fintype
  have hsp' : ⊤ ≤ Submodule.span ℂ (Set.range fun x : bs => (x : Fin n → ℂ)) := by
    rw [Subtype.range_coe, hbspan, hspan]
  let bb : Module.Basis bs ℂ (Fin n → ℂ) := Module.Basis.mk hli hsp'
  have hcard : Fintype.card bs = n := by
    have h := Module.finrank_eq_card_basis bb
    rw [Module.finrank_fin_fun] at h
    exact h.symm
  let e : bs ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let eb : Module.Basis (Fin n) ℂ (Fin n → ℂ) := bb.reindex e
  have heig : ∀ i, ∃ μ : ℂ, T (eb i) = μ • eb i := by
    intro i
    have hmem : eb i ∈ S := by
      rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
      exact hbsS (e.symm i).2
    obtain ⟨μ, hμ⟩ := Set.mem_iUnion.1 hmem
    exact ⟨μ, Module.End.mem_eigenspace_iff.1 hμ⟩
  choose zw hzw using heig
  let std : Module.Basis (Fin n) ℂ (Fin n → ℂ) := Pi.basisFun ℂ (Fin n)
  refine ⟨eb.toMatrix std, zw, Matrix.isUnit_det_of_right_inverse (Module.Basis.toMatrix_mul_toMatrix_flip eb std), ?_⟩
  have hdiag : LinearMap.toMatrix eb eb T = Matrix.diagonal zw := by
    ext i j
    rw [LinearMap.toMatrix_apply, hzw j, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
      Matrix.diagonal_apply, smul_eq_mul]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  have hstd : LinearMap.toMatrix std std T = A := by
    rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  have hinv : (eb.toMatrix std)⁻¹ = std.toMatrix eb :=
    Matrix.inv_eq_right_inv (Module.Basis.toMatrix_mul_toMatrix_flip eb std)
  rw [hinv, ← hstd, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix, hdiag]

private theorem exists_conj_soData_eq_diagonal (σ : M3 → Matrix (Fin n) (Fin n) ℂ) (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ GLs)
    (hσ1 : σ 1 = 1) (hσm : ∀ k k' : M3, kᵀ * k = 1 → k'ᵀ * k' = 1 → σ (k * k') = σ k * σ k') (a b : Fin 3)
    (hab : b < a) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (zw : Fin n → ℂ), IsUnit U.det ∧ U * soData σ a b * U⁻¹ = Matrix.diagonal zw := by
  have hne : a ≠ b := fun h => (lt_irrefl b) (h ▸ hab)
  set g : ℝ → Matrix (Fin n) (Fin n) ℂ := fun s => σ (rotC a b s) with hgdef
  set B : Matrix (Fin n) (Fin n) ℂ := rD (E a b - E b a) σ 1 with hBdef
  have hg0 : g 0 = 1 := by simp only [hgdef, rotC_zero, hσ1]
  have hg2π : g (2 * Real.pi) = 1 := by simp only [hgdef, rotC_two_pi, hσ1]
  have hgadd : ∀ s t, g (s + t) = g s * g t := fun s t => by
    simp only [hgdef]
    rw [rotC_add hne, hσm _ _ (rotC_orth hne s) (rotC_orth hne t)]
  have hgcomm : ∀ s t, g s * g t = g t * g s := fun s t => by rw [← hgadd, ← hgadd, add_comm]
  have h1 : (1 : M3) ∈ GLs := by simp [GLs]
  have hσd : DifferentiableAt ℝ σ 1 := differentiableAt_of_contDiffOn hσ h1
  have hgd0 : HasDerivAt g B 0 := by
    have h := hσd.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hasDerivAt_rotC_zero a b) (by rw [rotC_zero])
    rw [hBdef, rD_eq_fderiv _ hσd, Matrix.one_mul]
    exact h
  have hgd : ∀ s, HasDerivAt g (g s * B) s := fun s => by
    have h := hasDerivAt_const_mul_mat hgd0 (g s)
    have hfun : (fun t => g s * g t) = fun t => g (s + t) := funext fun t => (hgadd s t).symm
    rw [hfun, ← sub_self s] at h
    have h' := h.comp_sub_const s s
    have hfun' : (fun x => g (s + (x - s))) = g := funext fun x => by rw [add_sub_cancel]
    rw [hfun'] at h'
    exact h'
  have hcommB : ∀ s, g s * B = B * g s := fun s => by
    have hl := hasDerivAt_const_mul_mat hgd0 (g s)
    have hr := hasDerivAt_mul_const_mat hgd0 (g s)
    have hfun : (fun t => g s * g t) = fun t => g t * g s := funext fun t => hgcomm s t
    rw [hfun] at hl
    exact hl.unique hr
  have hrow : ∀ (v : Fin n → ℂ) (s : ℝ), HasDerivAt (fun t => v ᵥ* g t) ((v ᵥ* B) ᵥ* g s) s := fun v s => by
    have h := hasDerivAt_vecMul_of_hasDerivAt (hgd s) v
    rw [hcommB s, ← Matrix.vecMul_vecMul] at h
    exact h
  refine exists_conj_eq_diagonal_of_no_chain (soData σ a b) fun μ v₁ v₂ h₁ h₂ => ?_
  have hAB : soData σ a b = Bᵀ := rfl
  rw [hAB, Matrix.mulVec_transpose] at h₁ h₂
  exact no_chain_of_periodic hg0 hg2π hrow μ v₁ v₂ h₁ h₂

section WallDiagonal

private theorem conjOp_apply' (U : Matrix (Fin n) (Fin n) ℂ) (D : DOp (Fin n)) (ab : ℕ × ℕ) :
    conjOp U D ab = U.map MvPolynomial.C * D ab * U⁻¹.map MvPolynomial.C := by
  simp [conjOp, Finsupp.mapRange_apply]

private theorem diagEntry_apply' {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (D : DOp ι) (ab : ℕ × ℕ) :
    diagEntry i D ab = fun _ _ => D ab i i := by
  simp [diagEntry, Finsupp.mapRange_apply]

private theorem map_phi_mul {m : ℕ} (φ : Coef →ₐ[ℂ] Coef) (M N : Matrix (Fin m) (Fin m) Coef) :
    (M * N).map φ = M.map φ * N.map φ := by
  ext i j
  simp [Matrix.mul_apply, map_sum, map_mul]

private theorem conj_pow_of_isUnit {m : ℕ} (U V : Matrix (Fin m) (Fin m) ℂ) (hU : IsUnit U.det) (μ : ℕ) :
    U * V ^ μ * U⁻¹ = (U * V * U⁻¹) ^ μ := by
  induction μ with
  | zero => simp [Matrix.mul_nonsing_inv _ hU]
  | succ μ ih =>
    rw [pow_succ, pow_succ, ← ih]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U⁻¹ U, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]

private theorem wall_diagonal (W : WallData) (cω : ℂ) : ∃ φ₂ φ₃ : ℕ × ℕ → ℂ → Coef,
    (∀ ab c, W.φ (φ₂ ab c) = φ₂ ab c) ∧ (∀ ab c, W.φ (φ₃ ab c) = φ₃ ab c) ∧
      ∀ (n : ℕ) (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (zw : Fin n → ℂ),
        IsUnit U.det → U * W.V n S * U⁻¹ = Matrix.diagonal zw →
          ∀ (ab : ℕ × ℕ) (i i' : Fin n),
            W.φ (conjOp U (casOp₂ S cω) ab i i') = (if i = i' then φ₂ ab (zw i) else 0) ∧
              W.φ (conjOp U (casOp₃ S cω) ab i i') = (if i = i' then φ₃ ab (zw i) else 0) := by
  obtain ⟨p₂, p₃, h₂, h₃, h⟩ := wall_entries W cω
  have key : ∀ (p : ℕ × ℕ → Fin 4 → Coef) (n : ℕ) (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ)
      (U : Matrix (Fin n) (Fin n) ℂ) (zw : Fin n → ℂ), IsUnit U.det → U * W.V n S * U⁻¹ = Matrix.diagonal zw →
      ∀ (D : DOp (Fin n)) (ab : ℕ × ℕ),
        (D ab).map W.φ = ∑ μ : Fin 4, p ab μ • ((W.V n S) ^ (μ : ℕ)).map MvPolynomial.C →
        ∀ i i' : Fin n, W.φ (conjOp U D ab i i') =
          if i = i' then ∑ μ : Fin 4, p ab μ * MvPolynomial.C (zw i ^ (μ : ℕ)) else 0 := by
    intro p n S U zw hU hd D ab hD i i'
    rw [← Matrix.map_apply (f := W.φ), conjOp_apply', map_phi_mul, map_phi_mul, map_C_map_phi, map_C_map_phi, hD,
      Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
    have hterm : ∀ μ : Fin 4, U.map MvPolynomial.C
        * (p ab μ • (((W.V n S) ^ (μ : ℕ)).map MvPolynomial.C : Matrix (Fin n) (Fin n) Coef)) * U⁻¹.map MvPolynomial.C
        = p ab μ • (Matrix.diagonal fun k => (MvPolynomial.C (zw k ^ (μ : ℕ)) : Coef)) := by
      intro μ
      rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.map_mul, ← Matrix.map_mul, conj_pow_of_isUnit _ _ hU, hd,
        Matrix.diagonal_pow, Matrix.diagonal_map (map_zero _)]
      rfl
    simp only [hterm, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
    split_ifs <;> simp
  refine ⟨fun ab c => ∑ μ : Fin 4, p₂ ab μ * MvPolynomial.C (c ^ (μ : ℕ)),
    fun ab c => ∑ μ : Fin 4, p₃ ab μ * MvPolynomial.C (c ^ (μ : ℕ)), fun ab c => ?_, fun ab c => ?_,
    fun n S U zw hU hd ab i i' =>
      ⟨key p₂ n S U zw hU hd _ ab (h n S ab).1 i i', key p₃ n S U zw hU hd _ ab (h n S ab).2 i i'⟩⟩
  · simp only [map_sum, map_mul, h₂, phi_C]
  · simp only [map_sum, map_mul, h₃, phi_C]

private theorem scal_unit_eq (c : ℂ) : (scal c : Matrix Unit Unit Coef) = fun _ _ => MvPolynomial.C c := by
  ext u v
  simp [scal_apply', Subsingleton.elim u v]

private theorem hasOrder_of_entries {ι : Type} [Fintype ι] [DecidableEq ι] {D : DOp ι} {k : ℕ} (hD : HasOrder D k)
    (D' : DOp Unit) (h : ∀ ab, D ab = 0 → D' ab = 0) : HasOrder D' k :=
  hasOrder_of_forall fun x hx => h x (apply_eq_zero_of_hasOrder hD hx)

private theorem diagEntry_cmap_const_apply (D : DOp (Fin 1)) (ab : ℕ × ℕ) :
    diagEntry (0 : Fin 1) (cmap (fun p => MvPolynomial.C (MvPolynomial.constantCoeff p)) D) ab =
      fun _ _ => MvPolynomial.C (MvPolynomial.constantCoeff (D ab 0 0)) := by
  rw [diagEntry_apply', const_fun_eq, cmap_apply]
  funext _ _
  rw [Matrix.map_apply, constHom_apply]

private theorem diagEntry_cmap_const_scal (D : DOp (Fin 1)) (ab : ℕ × ℕ) (c : ℂ) (h : D ab = scal c) :
    diagEntry (0 : Fin 1) (cmap (fun p => MvPolynomial.C (MvPolynomial.constantCoeff p)) D) ab = scal c := by
  rw [diagEntry_cmap_const_apply, h, scal_apply', if_pos rfl, MvPolynomial.constantCoeff_C, scal_unit_eq]

private theorem diagEntry_cmap_const_zero (D : DOp (Fin 1)) (ab : ℕ × ℕ) (h : D ab = 0) :
    diagEntry (0 : Fin 1) (cmap (fun p => MvPolynomial.C (MvPolynomial.constantCoeff p)) D) ab = 0 := by
  rw [diagEntry_cmap_const_apply, h]
  funext _ _
  simp

private theorem cmap_const_diagEntry_cmap_const (D : DOp (Fin 1)) :
    cmap (fun p => MvPolynomial.C (MvPolynomial.constantCoeff p))
        (diagEntry (0 : Fin 1) (cmap (fun p => MvPolynomial.C (MvPolynomial.constantCoeff p)) D)) =
      diagEntry (0 : Fin 1) (cmap (fun p => MvPolynomial.C (MvPolynomial.constantCoeff p)) D) := by
  refine Finsupp.ext fun ab => ?_
  rw [const_fun_eq, cmap_apply, ← const_fun_eq, diagEntry_cmap_const_apply]
  funext u v
  rw [Matrix.map_apply, MvPolynomial.constantCoeff_C]

private theorem unit_matrix_comm (M N : Matrix Unit Unit Coef) : M * N = N * M := by
  ext u v
  simp [Matrix.mul_apply, mul_comm]

end WallDiagonal
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

private theorem exists_wallX0_diagonal (cω : ℂ) : ∃ φ₂ φ₃ : ℕ × ℕ → ℂ → Coef,
    (∀ ab c, killX0 (φ₂ ab c) = φ₂ ab c) ∧ (∀ ab c, killX0 (φ₃ ab c) = φ₃ ab c) ∧
      ∀ (n : ℕ) (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (zw : Fin n → ℂ),
        IsUnit U.det → U * S 2 1 * U⁻¹ = Matrix.diagonal zw →
          ∀ (ab : ℕ × ℕ) (i i' : Fin n),
            killX0 (conjOp U (casOp₂ S cω) ab i i') = (if i = i' then φ₂ ab (zw i) else 0) ∧
              killX0 (conjOp U (casOp₃ S cω) ab i i') = (if i = i' then φ₃ ab (zw i) else 0) := by
  obtain ⟨φ₂, φ₃, h₂, h₃, h⟩ := wall_diagonal wallX0Data cω
  exact ⟨φ₂, φ₃, h₂, h₃, h⟩

private theorem iterate_eul_sum (k : Fin 2) (e : ℕ) {κ : Type} (s : Finset κ) (g : κ → Coef) :
    (eul k)^[e] (∑ x ∈ s, g x) = ∑ x ∈ s, (eul k)^[e] (g x) := by
  induction e generalizing g with
  | zero => simp
  | succ e ih =>
    simp only [Function.iterate_succ_apply]
    rw [eul_sum', ih]

private theorem iterate_eul_C_mul (k : Fin 2) (e : ℕ) (c : ℂ) (p : Coef) :
    (eul k)^[e] (MvPolynomial.C c * p) = MvPolynomial.C c * (eul k)^[e] p := by
  induction e generalizing p with
  | zero => rfl
  | succ e ih => rw [Function.iterate_succ_apply, eul_mul, eul_C, zero_mul, zero_add, ih, Function.iterate_succ_apply]

private theorem iterate_eul_mul_C (k : Fin 2) (e : ℕ) (c : ℂ) (p : Coef) :
    (eul k)^[e] (p * MvPolynomial.C c) = (eul k)^[e] p * MvPolynomial.C c := by
  induction e generalizing p with
  | zero => rfl
  | succ e ih => rw [Function.iterate_succ_apply, eul_mul, eul_C, mul_zero, add_zero, ih, Function.iterate_succ_apply]

private theorem eulIt_sum' (e f : ℕ) {κ : Type} (s : Finset κ) (g : κ → Coef) :
    ((eul 0)^[e] ∘ (eul 1)^[f]) (∑ x ∈ s, g x) = ∑ x ∈ s, ((eul 0)^[e] ∘ (eul 1)^[f]) (g x) := by
  simp only [Function.comp_apply, iterate_eul_sum]

private theorem eulIt_C_mul (e f : ℕ) (c : ℂ) (p : Coef) :
    ((eul 0)^[e] ∘ (eul 1)^[f]) (MvPolynomial.C c * p) = MvPolynomial.C c * ((eul 0)^[e] ∘ (eul 1)^[f]) p := by
  simp only [Function.comp_apply, iterate_eul_C_mul]

private theorem eulIt_mul_C (e f : ℕ) (c : ℂ) (p : Coef) :
    ((eul 0)^[e] ∘ (eul 1)^[f]) (p * MvPolynomial.C c) = ((eul 0)^[e] ∘ (eul 1)^[f]) p * MvPolynomial.C c := by
  simp only [Function.comp_apply, iterate_eul_mul_C]

private theorem mapRange_comp {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (f : Matrix ι ι Coef → Matrix ι' ι' Coef) (hf0 : f 0 = 0) (hadd : ∀ M N, f (M + N) = f M + f N)
    (hsmul : ∀ (c : ℂ) M, f (c • M) = c • f M) (D D' : DOp ι)
    (hmul : ∀ ab cd (e g : ℕ), f (D ab * (D' cd).map ((eul 0)^[e] ∘ (eul 1)^[g])) =
      f (D ab) * (f (D' cd)).map ((eul 0)^[e] ∘ (eul 1)^[g])) :
    Finsupp.mapRange f hf0 (comp D D') = comp (Finsupp.mapRange f hf0 D) (Finsupp.mapRange f hf0 D') := by
  classical
  let F : Matrix ι ι Coef →+ Matrix ι' ι' Coef := { toFun := f, map_zero' := hf0, map_add' := hadd }
  have hsumF : ∀ (A : DOp ι) (G : ℕ × ℕ → Matrix ι ι Coef → DOp ι),
      Finsupp.mapRange.addMonoidHom F (A.sum G) = A.sum fun ab a => Finsupp.mapRange.addMonoidHom F (G ab a) :=
    fun A G => by simp only [Finsupp.sum, _root_.map_sum]
  rw [show Finsupp.mapRange f hf0 (comp D D') = Finsupp.mapRange.addMonoidHom F (comp D D') from rfl]
  simp only [DOp.comp]
  rw [hsumF, Finsupp.sum_mapRange_index]
  · refine Finsupp.sum_congr fun ab _ => ?_
    rw [hsumF, Finsupp.sum_mapRange_index]
    · refine Finsupp.sum_congr fun cd _ => ?_
      rw [_root_.map_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [_root_.map_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      change Finsupp.mapRange f hf0 (Finsupp.single _ _) = _
      rw [Finsupp.mapRange_single, hsmul, hmul]
    · intro cd
      simp [Matrix.map_zero _ (eulIt_zero _ _)]
  · intro ab
    simp

private theorem mapC_mul_inv (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnit U.det) :
    U.map (MvPolynomial.C : ℂ → Coef) * U⁻¹.map MvPolynomial.C = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hU, Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)]

private theorem mapC_inv_mul (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnit U.det) :
    U⁻¹.map (MvPolynomial.C : ℂ → Coef) * U.map MvPolynomial.C = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hU, Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)]

private theorem map_eulIt_mapC_mul_mul (U V : Matrix (Fin n) (Fin n) ℂ) (M : Matrix (Fin n) (Fin n) Coef) (e g : ℕ) :
    (U.map MvPolynomial.C * M * V.map MvPolynomial.C).map ((eul 0)^[e] ∘ (eul 1)^[g]) =
      U.map MvPolynomial.C * M.map ((eul 0)^[e] ∘ (eul 1)^[g]) * V.map MvPolynomial.C := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, eulIt_sum', eulIt_mul_C, eulIt_C_mul]

private theorem conjOp_comp (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnit U.det) (D D' : DOp (Fin n)) :
    conjOp U (comp D D') = comp (conjOp U D) (conjOp U D') := by
  refine mapRange_comp _ _ (fun M N => by simp only [Matrix.mul_add, Matrix.add_mul])
    (fun c M => by simp only [Matrix.mul_smul, Matrix.smul_mul]) D D' fun ab cd e g => ?_
  rw [map_eulIt_mapC_mul_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (U⁻¹.map MvPolynomial.C) (U.map MvPolynomial.C), mapC_inv_mul U hU, Matrix.one_mul]

private theorem mul_apply_diag {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (M N : Matrix ι ι Coef)
    (hM : ∀ k, k ≠ i → M i k = 0) : (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_single i (fun k _ hk => by rw [hM k hk, zero_mul]) (fun h => absurd (Finset.mem_univ i) h)

private theorem diagEntry_comp {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (D D' : DOp ι)
    (hD : ∀ ab k, k ≠ i → D ab i k = 0) : diagEntry i (comp D D') = comp (diagEntry i D) (diagEntry i D') := by
  refine mapRange_comp (fun M => fun _ _ => M i i) rfl (fun M N => by ext; simp) (fun c M => by ext; simp) D D'
    fun ab cd e g => ?_
  refine Matrix.ext fun u v => ?_
  show (D ab * (D' cd).map ((eul 0)^[e] ∘ (eul 1)^[g]) : Matrix ι ι Coef) i i = _
  rw [mul_apply_diag i _ _ (hD ab)]
  simp [Matrix.mul_apply, Matrix.map_apply]

private theorem weight_offDiag (U : Matrix (Fin n) (Fin n) ℂ) (Ω : DOp (Fin n)) (φ : ℕ × ℕ → ℂ → Coef)
    (zw : Fin n → ℂ)
    (h : ∀ (ab : ℕ × ℕ) (i i' : Fin n), killX0 (conjOp U Ω ab i i') = if i = i' then φ ab (zw i) else 0)
    (i : Fin n) (ab : ℕ × ℕ) (k : Fin n) (hk : k ≠ i) : cmap killX0 (conjOp U Ω) ab i k = 0 := by
  rw [cmap_apply, Matrix.map_apply, h, if_neg (Ne.symm hk)]

private theorem weight_apply (U : Matrix (Fin n) (Fin n) ℂ) (Ω : DOp (Fin n)) (i : Fin n) (ab : ℕ × ℕ) :
    diagEntry i (cmap killX0 (conjOp U Ω)) ab =
      fun _ _ =>
        killX0 ((U.map MvPolynomial.C * Ω ab * U⁻¹.map MvPolynomial.C : Matrix (Fin n) (Fin n) Coef) i i) := by
  rw [diagEntry_apply', cmap_apply, Matrix.map_apply, conjOp_apply']

private theorem weight_top_scal (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnit U.det) (Ω : DOp (Fin n)) (i : Fin n)
    (ab : ℕ × ℕ) (c : ℂ) (h : Ω ab = scal c) : diagEntry i (cmap killX0 (conjOp U Ω)) ab = scal c := by
  rw [weight_apply, h, scal_unit_eq]
  have : U.map MvPolynomial.C * (scal c : Matrix (Fin n) (Fin n) Coef) * U⁻¹.map MvPolynomial.C = scal c := by
    simp only [scal, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, mapC_mul_inv U hU]
  rw [this, scal_apply', if_pos rfl, phi_C]

private theorem weight_top_zero (U : Matrix (Fin n) (Fin n) ℂ) (Ω : DOp (Fin n)) (i : Fin n) (ab : ℕ × ℕ)
    (h : Ω ab = 0) : diagEntry i (cmap killX0 (conjOp U Ω)) ab = 0 := by
  rw [weight_apply, h, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply, _root_.map_zero]
  rfl

private theorem isCasimirPair_weightPair {Ω₂ Ω₃ : DOp (Fin n)} (hΩ : IsCasimirPair Ω₂ Ω₃) (φ₂ φ₃ : ℕ × ℕ → ℂ → Coef)
    (U : Matrix (Fin n) (Fin n) ℂ) (zw : Fin n → ℂ) (hU : IsUnit U.det)
    (h₂ : ∀ (ab : ℕ × ℕ) (i i' : Fin n), killX0 (conjOp U Ω₂ ab i i') = if i = i' then φ₂ ab (zw i) else 0)
    (h₃ : ∀ (ab : ℕ × ℕ) (i i' : Fin n), killX0 (conjOp U Ω₃ ab i i') = if i = i' then φ₃ ab (zw i) else 0)
    (i : Fin n) :
    IsCasimirPair (diagEntry i (cmap killX0 (conjOp U Ω₂))) (diagEntry i (cmap killX0 (conjOp U Ω₃))) := by
  have hd₂ := weight_offDiag U Ω₂ φ₂ zw h₂ i
  have hd₃ := weight_offDiag U Ω₃ φ₃ zw h₃ i
  refine ⟨hasOrder_of_entries hΩ.ord₂ _ fun ab hab => weight_top_zero U Ω₂ i ab hab,
    hasOrder_of_entries hΩ.ord₃ _ fun ab hab => weight_top_zero U Ω₃ i ab hab,
    weight_top_scal U hU Ω₂ i _ _ hΩ.top₂₀, weight_top_scal U hU Ω₂ i _ _ hΩ.top₁₁,
    weight_top_scal U hU Ω₂ i _ _ hΩ.top₀₂,
    weight_top_zero U Ω₃ i _ hΩ.top₃₀, weight_top_scal U hU Ω₃ i _ _ hΩ.top₂₁, weight_top_scal U hU Ω₃ i _ _ hΩ.top₁₂,
    weight_top_zero U Ω₃ i _ hΩ.top₀₃, ?_⟩
  rw [← diagEntry_comp i _ _ hd₂, ← diagEntry_comp i _ _ hd₃, ← cmap_comp_killX0, ← cmap_comp_killX0,
    ← conjOp_comp U hU, ← conjOp_comp U hU, hΩ.comm]

private theorem diagEntry_cmap_killX0_conjOp_apply (φ : ℕ × ℕ → ℂ → Coef) (U : Matrix (Fin n) (Fin n) ℂ)
    (zw : Fin n → ℂ)
    (D : DOp (Fin n))
    (h : ∀ (ab : ℕ × ℕ) (i i' : Fin n), killX0 (conjOp U D ab i i') = if i = i' then φ ab (zw i) else 0)
    (i : Fin n) (ab : ℕ × ℕ) : diagEntry i (cmap killX0 (conjOp U D)) ab = fun _ _ => φ ab (zw i) := by
  rw [diagEntry_apply', cmap_apply]
  funext _ _
  rw [Matrix.map_apply, h, if_pos rfl]

private theorem exists_wallX1_diagonal (cω : ℂ) : ∃ φ₂ φ₃ : ℕ × ℕ → ℂ → Coef,
    (∀ ab c, killX1 (φ₂ ab c) = φ₂ ab c) ∧ (∀ ab c, killX1 (φ₃ ab c) = φ₃ ab c) ∧
      ∀ (n : ℕ) (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (zw : Fin n → ℂ),
        IsUnit U.det → U * S 1 0 * U⁻¹ = Matrix.diagonal zw →
          ∀ (ab : ℕ × ℕ) (i i' : Fin n),
            killX1 (conjOp U (casOp₂ S cω) ab i i') = (if i = i' then φ₂ ab (zw i) else 0) ∧
              killX1 (conjOp U (casOp₃ S cω) ab i i') = (if i = i' then φ₃ ab (zw i) else 0) := by
  obtain ⟨φ₂, φ₃, h₂, h₃, h⟩ := wall_diagonal wallX1Data cω
  exact ⟨φ₂, φ₃, h₂, h₃, h⟩

private theorem swapOp_conjOp (U : Matrix (Fin n) (Fin n) ℂ) (D : DOp (Fin n)) :
    swapOp (conjOp U D) = conjOp U (swapOp D) := by
  refine Finsupp.ext fun ab => ?_
  obtain ⟨a, b⟩ := ab
  rw [swapOp_apply]
  simp only [conjOp, Finsupp.mapRange_apply]
  rw [swapOp_apply]
  refine Matrix.ext fun i j => ?_
  simp [Matrix.mul_apply, map_sum]

private theorem diagEntry_swapOp {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (D : DOp ι) :
    diagEntry i (swapOp D) = swapOp (diagEntry i D) := by
  refine Finsupp.ext fun ab => ?_
  obtain ⟨a, b⟩ := ab
  rw [swapOp_apply]
  simp only [diagEntry, Finsupp.mapRange_apply]
  rw [swapOp_apply]
  refine Matrix.ext fun _ _ => ?_
  simp

private theorem isCasimirPair_wall00 (cω : ℂ) :
    IsCasimirPair (diagEntry (0 : Fin 1) (cmap (fun p => MvPolynomial.C (MvPolynomial.constantCoeff p))
        (casOp₂ (fun _ _ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) cω)))
      (diagEntry (0 : Fin 1) (cmap (fun p => MvPolynomial.C (MvPolynomial.constantCoeff p))
        (casOp₃ (fun _ _ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) cω))) := by
  set S0 : Fin 3 → Fin 3 → Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => 0 with hS0
  obtain ⟨t20, t11, t02⟩ := casOp₂_top S0 cω
  obtain ⟨t30, t21, t12, t03⟩ := casOp₃_top S0 cω
  refine ⟨hasOrder_of_entries (hasOrder_casOp₂ S0 cω) _ (diagEntry_cmap_const_zero _),
    hasOrder_of_entries (hasOrder_casOp₃ S0 cω) _ (diagEntry_cmap_const_zero _),
    diagEntry_cmap_const_scal _ _ _ t20, diagEntry_cmap_const_scal _ _ _ t11, diagEntry_cmap_const_scal _ _ _ t02,
    diagEntry_cmap_const_zero _ _ t30, diagEntry_cmap_const_scal _ _ _ t21, diagEntry_cmap_const_scal _ _ _ t12,
    diagEntry_cmap_const_zero _ _ t03, ?_⟩
  exact comp_comm_of_const _ _ (cmap_const_diagEntry_cmap_const _) (cmap_const_diagEntry_cmap_const _)
    fun ab cd => unit_matrix_comm _ _

private theorem diagEntry_wall00_apply (cω : ℂ) (ω₂ : ℕ × ℕ → ℂ)
    (h : ∀ ab : ℕ × ℕ, (casOp₂ (fun _ _ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) cω ab).map MvPolynomial.constantCoeff =
      ω₂ ab • (1 : Matrix (Fin 1) (Fin 1) ℂ)) (ab : ℕ × ℕ) :
    diagEntry (0 : Fin 1) (cmap (fun p => MvPolynomial.C (MvPolynomial.constantCoeff p))
      (casOp₂ (fun _ _ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) cω)) ab = fun _ _ => MvPolynomial.C (ω₂ ab) := by
  rw [diagEntry_cmap_const_apply]
  funext _ _
  have := congrFun (congrFun (h ab) 0) 0
  rw [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at this
  rw [this]

end Weights
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

section CasimirPair

variable {n : ℕ}

section CasimirInherit

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem c3_congr_of_eqOn {F G : M3 → V} (h : Set.EqOn F G GLs) {x : M3} (hx : x ∈ GLs) : c3 F x = c3 G x := by
  unfold c3
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  refine rD_congr_of_eqOn (E i j) (fun y hy => ?_) hx
  refine rD_congr_of_eqOn (E j k) (fun z hz => ?_) hy
  exact rD_congr_of_eqOn (E k i) h hz

private theorem c2_clm_comp {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V'] (L : V →L[ℝ] V') {F : M3 → V}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {x : M3} (hx : x ∈ GLs) : c2 (fun y => L (F y)) x = L (c2 F x) := by
  have h1 : ∀ (Y : M3) {G : M3 → V}, ContDiffOn ℝ (⊤ : ℕ∞) G GLs →
      Set.EqOn (rD Y fun y => L (G y)) (fun y => L (rD Y G y)) GLs :=
    fun Y G hG y hy => rD_clm_comp L Y (differentiableAt_of_contDiffOn hG hy)
  unfold c2
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hd := contDiffOn_rD (E j i) hF
  rw [rD_congr_of_eqOn (E i j) (h1 (E j i) hF) hx, h1 (E i j) hd hx]

private theorem c3_clm_comp {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V'] (L : V →L[ℝ] V') {F : M3 → V}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {x : M3} (hx : x ∈ GLs) : c3 (fun y => L (F y)) x = L (c3 F x) := by
  have h1 : ∀ (Y : M3) {G : M3 → V}, ContDiffOn ℝ (⊤ : ℕ∞) G GLs →
      Set.EqOn (rD Y fun y => L (G y)) (fun y => L (rD Y G y)) GLs :=
    fun Y G hG y hy => rD_clm_comp L Y (differentiableAt_of_contDiffOn hG hy)
  unfold c3
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hd := contDiffOn_rD (E k i) hF
  have hdd := contDiffOn_rD (E j k) hd
  rw [rD_congr_of_eqOn (E i j) (fun y hy => rD_congr_of_eqOn (E j k) (h1 (E k i) hF) hy) hx,
    rD_congr_of_eqOn (E i j) (h1 (E j k) hd) hx, h1 (E i j) hdd hx]

private theorem rD_one_rD (Y : M3) {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {x : M3} (hx : x ∈ GLs) :
    rD 1 (rD Y F) x = rD Y (rD 1 F) x := by
  have h := rD_comm 1 Y hF hx
  rw [Matrix.one_mul, Matrix.mul_one, sub_self, rD_zero_dir] at h
  exact sub_eq_zero.1 h

private theorem rD_one_c2 {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {x : M3} (hx : x ∈ GLs) :
    rD 1 (c2 F) x = c2 (rD 1 F) x := by
  have hd : ∀ Y : M3, ContDiffOn ℝ (⊤ : ℕ∞) (rD Y F) GLs := fun Y => contDiffOn_rD Y hF
  have hflat : Set.EqOn (c2 F) (fun y => ∑ p : Fin 3 × Fin 3, rD (E p.1 p.2) (rD (E p.2 p.1) F) y) GLs := by
    intro y _
    simp only [c2, Fintype.sum_prod_type]
  rw [rD_congr_of_eqOn 1 hflat hx,
    rD_sum _ _ fun p _ => differentiableAt_of_contDiffOn (contDiffOn_rD _ (hd _)) hx]
  unfold c2
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [rD_one_rD (E i j) (hd _) hx]
  exact rD_congr_of_eqOn (E i j) (fun y hy => rD_one_rD (E j i) hF hy) hx

private theorem rD_one_c3 {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {x : M3} (hx : x ∈ GLs) :
    rD 1 (c3 F) x = c3 (rD 1 F) x := by
  have hd : ∀ Y : M3, ContDiffOn ℝ (⊤ : ℕ∞) (rD Y F) GLs := fun Y => contDiffOn_rD Y hF
  have hdd : ∀ Y Y' : M3, ContDiffOn ℝ (⊤ : ℕ∞) (rD Y (rD Y' F)) GLs := fun Y Y' => contDiffOn_rD Y (hd Y')
  have hflat : Set.EqOn (c3 F)
      (fun y => ∑ p : Fin 3 × Fin 3 × Fin 3, rD (E p.1 p.2.1) (rD (E p.2.1 p.2.2) (rD (E p.2.2 p.1) F)) y) GLs := by
    intro y _
    simp only [c3, Fintype.sum_prod_type]
  rw [rD_congr_of_eqOn 1 hflat hx,
    rD_sum _ _ fun p _ => differentiableAt_of_contDiffOn (contDiffOn_rD _ (hdd _ _)) hx]
  unfold c3
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [rD_one_rD (E i j) (hdd _ _) hx]
  refine rD_congr_of_eqOn (E i j) (fun y hy => ?_) hx
  rw [rD_one_rD (E j k) (hd _) hy]
  exact rD_congr_of_eqOn (E j k) (fun z hz => rD_one_rD (E k i) hF hz) hy

end CasimirInherit
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

private theorem mem_GLs_of_orth {k : M3} (hk : kᵀ * k = 1) : k ∈ GLs := by
  have h := congrArg Matrix.det hk
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  intro h0
  rw [h0, mul_zero] at h
  exact zero_ne_one h

private def vecMulCLM (M : Matrix (Fin n) (Fin n) ℂ) : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => v ᵥ* M
      map_add' := fun v w => Matrix.add_vecMul M v w
      map_smul' := fun c v => by
        rw [RingHom.id_apply]
        funext j
        simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, Finset.smul_sum, smul_mul_assoc] }

private theorem vecMulCLM_apply (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : vecMulCLM M v = v ᵥ* M := rfl

private def smulCLM (c : ℂ) : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => c • v
      map_add' := fun v w => smul_add c v w
      map_smul' := fun r v => by
        rw [RingHom.id_apply]
        funext j
        simp only [Pi.smul_apply]
        exact smul_comm c r (v j) }

private theorem smulCLM_apply (c : ℂ) (v : Fin n → ℂ) : smulCLM c v = c • v := rfl

private theorem transforms_c2_c3 (σ : M3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ) {W : M3 → (Fin n → ℂ)}
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) W GLs)
    (hN : ∀ n' x : M3, IsUpperUni n' → x ∈ GLs → W (n' * x) = uniChar n' • W x)
    (hK : ∀ x k : M3, x ∈ GLs → kᵀ * k = 1 → W (x * k) = W x ᵥ* σ k)
    (hZ : ∀ x ∈ GLs, rD 1 W x = cω • W x) :
    ((∀ n' x : M3, IsUpperUni n' → x ∈ GLs → c2 W (n' * x) = uniChar n' • c2 W x) ∧
      (∀ x k : M3, x ∈ GLs → kᵀ * k = 1 → c2 W (x * k) = c2 W x ᵥ* σ k) ∧
      (∀ x ∈ GLs, rD 1 (c2 W) x = cω • c2 W x)) ∧
    ((∀ n' x : M3, IsUpperUni n' → x ∈ GLs → c3 W (n' * x) = uniChar n' • c3 W x) ∧
      (∀ x k : M3, x ∈ GLs → kᵀ * k = 1 → c3 W (x * k) = c3 W x ᵥ* σ k) ∧
      (∀ x ∈ GLs, rD 1 (c3 W) x = cω • c3 W x)) := by
  refine ⟨⟨fun n' x hn' hx => ?_, fun x k hx hk => ?_, fun x hx => ?_⟩,
    ⟨fun n' x hn' hx => ?_, fun x k hx hk => ?_, fun x hx => ?_⟩⟩
  · have h := congrFun (c2_comp_mul_left n' W) x
    beta_reduce at h
    rw [← h, c2_congr_of_eqOn (fun y hy => (hN n' y hn' hy).trans (smulCLM_apply (uniChar n') (W y)).symm) hx,
      c2_clm_comp (smulCLM (uniChar n')) hW hx, smulCLM_apply]
  · rw [← c2_comp_mul_right (mem_GLs_of_orth hk) hW hx,
      c2_congr_of_eqOn (fun y hy => (hK y k hy hk).trans (vecMulCLM_apply (σ k) (W y)).symm) hx,
      c2_clm_comp (vecMulCLM (σ k)) hW hx, vecMulCLM_apply]
  · rw [rD_one_c2 hW hx, c2_congr_of_eqOn (fun y hy => (hZ y hy).trans (smulCLM_apply cω (W y)).symm) hx,
      c2_clm_comp (smulCLM cω) hW hx, smulCLM_apply]
  · have h := congrFun (c3_comp_mul_left n' W) x
    beta_reduce at h
    rw [← h, c3_congr_of_eqOn (fun y hy => (hN n' y hn' hy).trans (smulCLM_apply (uniChar n') (W y)).symm) hx,
      c3_clm_comp (smulCLM (uniChar n')) hW hx, smulCLM_apply]
  · rw [← c3_comp_mul_right (mem_GLs_of_orth hk) hW hx,
      c3_congr_of_eqOn (fun y hy => (hK y k hy hk).trans (vecMulCLM_apply (σ k) (W y)).symm) hx,
      c3_clm_comp (vecMulCLM (σ k)) hW hx, vecMulCLM_apply]
  · rw [rD_one_c3 hW hx, c3_congr_of_eqOn (fun y hy => (hZ y hy).trans (smulCLM_apply cω (W y)).symm) hx,
      c3_clm_comp (smulCLM cω) hW hx, smulCLM_apply]

private theorem apply_sub (D D' : DOp (Fin n)) (G : ℝ → ℝ → (Fin n → ℂ)) :
    apply (D - D') G = fun t₁ t₂ => apply D G t₁ t₂ - apply D' G t₁ t₂ := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ D', apply_add, apply_smul]
  funext t₁ t₂
  simp only [neg_one_smul, sub_eq_add_neg]

private theorem isCasimirPair_casOp (σ : M3 → Matrix (Fin n) (Fin n) ℂ) (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ GLs)
    (hσ1 : σ 1 = 1) (hσm : ∀ k k' : M3, kᵀ * k = 1 → k'ᵀ * k' = 1 → σ (k * k') = σ k * σ k') (cω : ℂ) :
    IsCasimirPair (casOp₂ (soData σ) cω) (casOp₃ (soData σ) cω) := by
  refine ⟨hasOrder_casOp₂ _ _, hasOrder_casOp₃ _ _, (casOp₂_top _ _).1, (casOp₂_top _ _).2.1, (casOp₂_top _ _).2.2,
    (casOp₃_top _ _).1, (casOp₃_top _ _).2.1, (casOp₃_top _ _).2.2.1, (casOp₃_top _ _).2.2.2, ?_⟩
  refine sub_eq_zero.1 (faithful _ fun G hG => ?_)
  obtain ⟨W, hW, hN, hK, hZ, hT⟩ := exists_transforming_extension σ hσ hσ1 hσm cω G hG
  have hKinf : ∀ {W' : M3 → (Fin n → ℂ)}, ContDiffOn ℝ (⊤ : ℕ∞) W' GLs →
      (∀ x k : M3, x ∈ GLs → kᵀ * k = 1 → W' (x * k) = W' x ᵥ* σ k) →
        ∀ x ∈ GLs, ∀ a b : Fin 3, b < a → rD (E a b - E b a) W' x = soData σ a b *ᵥ W' x :=
    fun hW' hK' x hx a b hab => rD_skew_eq_soData_mulVec σ hσ hW' hK' hx a b hab
  obtain ⟨⟨hN₂, hK₂, hZ₂⟩, ⟨hN₃, hK₃, hZ₃⟩⟩ := transforms_c2_c3 σ cω hW hN hK hZ
  have hG' : G = fun s₁ s₂ => W (torus (Real.exp s₁) (Real.exp s₂)) := by
    funext s₁ s₂
    exact (hT s₁ s₂).symm
  have h3 : apply (casOp₃ (soData σ) cω) G = fun t₁ t₂ => c3 W (torus (Real.exp t₁) (Real.exp t₂)) := by
    funext t₁ t₂
    rw [hG', c3_torus_eq_apply_casOp₃ (soData σ) cω hW hN hZ (hKinf hW hK)]
  have h2 : apply (casOp₂ (soData σ) cω) G = fun t₁ t₂ => c2 W (torus (Real.exp t₁) (Real.exp t₂)) := by
    funext t₁ t₂
    rw [hG', c2_torus_eq_apply_casOp₂ (soData σ) cω hW hN hZ (hKinf hW hK)]
  have h23 : apply (casOp₂ (soData σ) cω) (fun t₁ t₂ => c3 W (torus (Real.exp t₁) (Real.exp t₂))) =
      fun t₁ t₂ => c2 (c3 W) (torus (Real.exp t₁) (Real.exp t₂)) := by
    funext t₁ t₂
    rw [c2_torus_eq_apply_casOp₂ (soData σ) cω (contDiffOn_c3 hW) hN₃ hZ₃ (hKinf (contDiffOn_c3 hW) hK₃)]
  have h32 : apply (casOp₃ (soData σ) cω) (fun t₁ t₂ => c2 W (torus (Real.exp t₁) (Real.exp t₂))) =
      fun t₁ t₂ => c3 (c2 W) (torus (Real.exp t₁) (Real.exp t₂)) := by
    funext t₁ t₂
    rw [c3_torus_eq_apply_casOp₃ (soData σ) cω (contDiffOn_c2 hW) hN₂ hZ₂ (hKinf (contDiffOn_c2 hW) hK₂)]
  rw [apply_sub, apply_comp _ _ hG, apply_comp _ _ hG, h3, h2, h23, h32]
  funext t₁ t₂
  show c2 (c3 W) (torus (Real.exp t₁) (Real.exp t₂)) - c3 (c2 W) (torus (Real.exp t₁) (Real.exp t₂)) = 0
  rw [c2_c3 hW (torus_mem_GLs (Real.exp_pos t₁) (Real.exp_pos t₂)), sub_self]

end CasimirPair
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

section MasterSystem

variable {n : ℕ}

private abbrev PWord (L : ℕ) : Type :=
  {v : Fin (L + 1) × (Fin L → Fin 3 × Fin 3) // ∀ p : Fin L, (v.1 : ℕ) ≤ p → v.2 p = (0, 0)}

private abbrev PWord.len {L : ℕ} (v : PWord L) : ℕ := v.1.1

private def PWord.toFn {L : ℕ} (v : PWord L) : Fin v.len → Fin 3 × Fin 3 :=
  fun i => v.1.2 (Fin.castLE (Nat.le_of_lt_succ v.1.1.2) i)

private def master (L : ℕ) (𝒟 : (k : ℕ) → (Fin k → Fin 3 × Fin 3) → DOp (Fin n)) (Φ₀ : ℝ → ℝ → (Fin n → ℂ))
    (t₁ t₂ : ℝ) : PWord L × Fin n → ℂ :=
  fun μ => apply (𝒟 μ.1.len μ.1.toFn) Φ₀ t₁ t₂ μ.2

private structure IsWordFamily (Ω₂ Ω₃ : DOp (Fin n)) (𝒟 : (k : ℕ) → (Fin k → Fin 3 × Fin 3) → DOp (Fin n)) : Prop where
  zero : ∀ w, 𝒟 0 w = DOp.one
  hasOrder : ∀ k w, HasOrder (𝒟 k w) k
  totalDegree_le : ∀ k w ab i i', ((𝒟 k w) ab i i').totalDegree ≤ k
  comp_casimir₂ : ∀ k w, comp (𝒟 k w) Ω₂ ∈ Submodule.span ℂ (Set.range (𝒟 (k + 2)))
  comp_casimir₃ : ∀ k w, comp (𝒟 k w) Ω₃ ∈ Submodule.span ℂ (Set.range (𝒟 (k + 3)))
  d₁_comp : ∀ k w, comp d₁ (𝒟 k w) ∈ Submodule.span ℂ (Set.range (𝒟 (k + 1)))
  d₂_comp : ∀ k w, comp d₂ (𝒟 k w) ∈ Submodule.span ℂ (Set.range (𝒟 (k + 1)))

private def PWord.pad {L : ℕ} (k : ℕ) (hk : k ≤ L) (w : Fin k → Fin 3 × Fin 3) : PWord L :=
  ⟨(⟨k, Nat.lt_succ_of_le hk⟩, fun i => if h : (i : ℕ) < k then w ⟨i, h⟩ else (0, 0)),
    fun p hp => by dsimp only; rw [dif_neg (Nat.not_lt.2 hp)]⟩

private theorem PWord.toFn_pad {L : ℕ} (k : ℕ) (hk : k ≤ L) (w : Fin k → Fin 3 × Fin 3) : (PWord.pad k hk w).toFn = w
    := by
  funext i
  have hi : (i : ℕ) < k := i.2
  simp only [PWord.toFn, PWord.pad, Fin.castLE]
  rw [dif_pos hi]
  exact congrArg w (Fin.ext rfl)

private theorem PWord.app_pad {α : Sort*} (𝒟 : (k : ℕ) → (Fin k → Fin 3 × Fin 3) → α) {L : ℕ} (k : ℕ) (hk : k ≤ L)
    (w : Fin k → Fin 3 × Fin 3) : 𝒟 (PWord.pad (L := L) k hk w).len (PWord.pad (L := L) k hk w).toFn = 𝒟 k w := by
  show 𝒟 k (PWord.pad (L := L) k hk w).toFn = 𝒟 k w
  rw [PWord.toFn_pad]

private abbrev wspan (𝒟 : (k : ℕ) → (Fin k → Fin 3 × Fin 3) → DOp (Fin n)) (k : ℕ) : Submodule ℂ (DOp (Fin n)) :=
  Submodule.span ℂ (Set.range (𝒟 k))

private theorem mem_span_pwords {L : ℕ} (𝒟 : (k : ℕ) → (Fin k → Fin 3 × Fin 3) → DOp (Fin n)) {k : ℕ} (hk : k ≤ L)
    {D : DOp (Fin n)} (hD : D ∈ wspan 𝒟 k) :
    D ∈ Submodule.span ℂ (Set.range (fun v : PWord L => 𝒟 v.len v.toFn)) := by
  refine Submodule.span_mono ?_ hD
  rintro _ ⟨w, rfl⟩
  exact ⟨PWord.pad k hk w, PWord.app_pad 𝒟 k hk w⟩

private theorem map_mem_of_mem_span {S : Set (DOp (Fin n))} {S' : Submodule ℂ (DOp (Fin n))}
    (F : DOp (Fin n) → DOp (Fin n))
    (hadd : ∀ x y, F (x + y) = F x + F y) (hsmul : ∀ (a : ℂ) x, F (a • x) = a • F x) (hS : ∀ x ∈ S, F x ∈ S')
    {D : DOp (Fin n)} (hD : D ∈ Submodule.span ℂ S) : F D ∈ S' := by
  induction hD using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero =>
    have h := hsmul 0 0
    rw [zero_smul, zero_smul] at h
    rw [h]
    exact S'.zero_mem
  | add x y _ _ hx hy =>
    rw [hadd]
    exact S'.add_mem hx hy
  | smul a x _ hx =>
    rw [hsmul]
    exact S'.smul_mem a hx

section WordSpans

variable {Ω₂ Ω₃ : DOp (Fin n)} {𝒟 : (k : ℕ) → (Fin k → Fin 3 × Fin 3) → DOp (Fin n)}

private theorem IsWordFamily.comp_mem₂ (h : IsWordFamily Ω₂ Ω₃ 𝒟) {k : ℕ} {D : DOp (Fin n)} (hD : D ∈ wspan 𝒟 k) :
    comp D Ω₂ ∈ wspan 𝒟 (k + 2) :=
  map_mem_of_mem_span (fun D => comp D Ω₂) (fun x y => add_comp x y Ω₂) (fun a x => smul_comp a x Ω₂)
    (by rintro _ ⟨w, rfl⟩; exact h.comp_casimir₂ k w) hD

private theorem IsWordFamily.comp_mem₃ (h : IsWordFamily Ω₂ Ω₃ 𝒟) {k : ℕ} {D : DOp (Fin n)} (hD : D ∈ wspan 𝒟 k) :
    comp D Ω₃ ∈ wspan 𝒟 (k + 3) :=
  map_mem_of_mem_span (fun D => comp D Ω₃) (fun x y => add_comp x y Ω₃) (fun a x => smul_comp a x Ω₃)
    (by rintro _ ⟨w, rfl⟩; exact h.comp_casimir₃ k w) hD

private theorem IsWordFamily.d₁_mem (h : IsWordFamily Ω₂ Ω₃ 𝒟) {k : ℕ} {D : DOp (Fin n)} (hD : D ∈ wspan 𝒟 k) :
    comp d₁ D ∈ wspan 𝒟 (k + 1) :=
  map_mem_of_mem_span (fun D => comp d₁ D) (fun x y => comp_add d₁ x y) (fun a x => comp_smul a d₁ x)
    (by rintro _ ⟨w, rfl⟩; exact h.d₁_comp k w) hD

private theorem IsWordFamily.d₂_mem (h : IsWordFamily Ω₂ Ω₃ 𝒟) {k : ℕ} {D : DOp (Fin n)} (hD : D ∈ wspan 𝒟 k) :
    comp d₂ D ∈ wspan 𝒟 (k + 1) :=
  map_mem_of_mem_span (fun D => comp d₂ D) (fun x y => comp_add d₂ x y) (fun a x => comp_smul a d₂ x)
    (by rintro _ ⟨w, rfl⟩; exact h.d₂_comp k w) hD

private theorem IsWordFamily.one_mem (h : IsWordFamily Ω₂ Ω₃ 𝒟) : DOp.one ∈ wspan 𝒟 0 :=
  Submodule.subset_span ⟨Fin.elim0, h.zero _⟩

private theorem npow_succ_eq (D : DOp (Fin n)) (e : ℕ) : npow D (e + 1) = comp D (npow D e) :=
  Function.iterate_succ_apply' (comp D) e DOp.one

private theorem IsWordFamily.comp_npow_mem₂ (h : IsWordFamily Ω₂ Ω₃ 𝒟) (e : ℕ) :
    ∀ {k : ℕ} {D : DOp (Fin n)}, D ∈ wspan 𝒟 k → comp D (npow Ω₂ e) ∈ wspan 𝒟 (k + 2 * e) := by
  induction e with
  | zero =>
    intro k D hD
    rw [Nat.mul_zero, Nat.add_zero]
    show comp D DOp.one ∈ _
    rw [DOp.comp_one]
    exact hD
  | succ e ih =>
    intro k D hD
    rw [npow_succ_eq, ← comp_assoc, show k + 2 * (e + 1) = k + 2 + 2 * e by ring]
    exact ih (h.comp_mem₂ hD)

private theorem IsWordFamily.comp_npow_mem₃ (h : IsWordFamily Ω₂ Ω₃ 𝒟) (f : ℕ) :
    ∀ {k : ℕ} {D : DOp (Fin n)}, D ∈ wspan 𝒟 k → comp D (npow Ω₃ f) ∈ wspan 𝒟 (k + 3 * f) := by
  induction f with
  | zero =>
    intro k D hD
    rw [Nat.mul_zero, Nat.add_zero]
    show comp D DOp.one ∈ _
    rw [DOp.comp_one]
    exact hD
  | succ f ih =>
    intro k D hD
    rw [npow_succ_eq, ← comp_assoc, show k + 3 * (f + 1) = k + 3 + 3 * f by ring]
    exact ih (h.comp_mem₃ hD)

private theorem IsWordFamily.comp_mono_mem (h : IsWordFamily Ω₂ Ω₃ 𝒟) (a b : ℕ) :
    ∀ {k : ℕ} {D : DOp (Fin n)}, D ∈ wspan 𝒟 k → comp (mono a b) D ∈ wspan 𝒟 (a + b + k) := by
  induction a with
  | zero =>
    induction b with
    | zero =>
      intro k D hD
      rw [show (0 : ℕ) + 0 + k = k by omega, ← one_eq_mono, one_comp]
      exact hD
    | succ b ihb =>
      intro k D hD
      have hm : (mono 0 (b + 1) : DOp (Fin n)) = DOp.comp DOp.d₂ (mono 0 b) := by
        rw [d₂_eq_mono, mono_comp_mono, Nat.zero_add, Nat.add_comm 1 b]
      rw [hm, comp_assoc, show 0 + (b + 1) + k = 0 + b + k + 1 by ring]
      exact h.d₂_mem (ihb hD)
  | succ a iha =>
    intro k D hD
    have hm : (mono (a + 1) b : DOp (Fin n)) = DOp.comp DOp.d₁ (mono a b) := by
      rw [d₁_eq_mono, mono_comp_mono, Nat.add_comm 1 a, Nat.zero_add]
    rw [hm, comp_assoc, show a + 1 + b + k = a + b + k + 1 by ring]
    exact h.d₁_mem (iha hD)

private theorem basisDeg_le (j : Fin 6) : basisDeg j ≤ 3 := by
  fin_cases j <;> simp [basisDeg, basisExp]

private theorem IsWordFamily.nb_mem (h : IsWordFamily Ω₂ Ω₃ 𝒟) (j : Fin 6) (e f : ℕ) :
    nb Ω₂ Ω₃ j e f ∈ wspan 𝒟 (basisDeg j + (2 * e + 3 * f)) := by
  have h1 : comp DOp.one (npow Ω₂ e) ∈ wspan 𝒟 (0 + 2 * e) := h.comp_npow_mem₂ e h.one_mem
  have h2 : comp (comp DOp.one (npow Ω₂ e)) (npow Ω₃ f) ∈ wspan 𝒟 (0 + 2 * e + 3 * f) := h.comp_npow_mem₃ f h1
  rw [one_comp, show 0 + 2 * e + 3 * f = 2 * e + 3 * f by ring] at h2
  have h3 := h.comp_mono_mem (basisExp j).1 (basisExp j).2 h2
  exact h3

private theorem IsWordFamily.exists_frame_coeffs (h : IsWordFamily Ω₂ Ω₃ 𝒟) {N₂ N₃ L : ℕ}
    (hL : 3 + 2 * N₂ + 3 * N₃ ≤ L)
    (j : Fin 6) (e : Fin N₂) (f : Fin N₃) :
    ∃ c : PWord L → ℂ, (∑ v, c v • 𝒟 v.len v.toFn) = nb Ω₂ Ω₃ j e f := by
  refine (Submodule.mem_span_range_iff_exists_fun ℂ).1 (mem_span_pwords 𝒟 ?_ (h.nb_mem j e f))
  have hj := basisDeg_le j
  have he := e.2
  have hf := f.2
  omega

end WordSpans
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

section OperatorLinearAlgebra

private theorem ms_cmul_zero_left (D : DOp (Fin n)) : cmul (0 : Matrix (Fin n) (Fin n) Coef) D = 0 := by
  have h := add_cmul (0 : Matrix (Fin n) (Fin n) Coef) 0 D
  rw [add_zero] at h
  have h2 : cmul (0 : Matrix (Fin n) (Fin n) Coef) D + cmul 0 D = cmul 0 D + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

private theorem ms_cmul_zero_right (C : Matrix (Fin n) (Fin n) Coef) : cmul C (0 : DOp (Fin n)) = 0 := by
  have h := cmul_add C (0 : DOp (Fin n)) 0
  rw [add_zero] at h
  have h2 : cmul C (0 : DOp (Fin n)) + cmul C 0 = cmul C 0 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

private theorem ms_neg_cmul (C : Matrix (Fin n) (Fin n) Coef) (D : DOp (Fin n)) : cmul (-C) D = -cmul C D := by
  have h := add_cmul (-C) C D
  rw [neg_add_cancel, ms_cmul_zero_left] at h
  exact eq_neg_of_add_eq_zero_left h.symm

private theorem ms_sum_cmul {α : Type*} (s : Finset α) (C : α → Matrix (Fin n) (Fin n) Coef) (D : DOp (Fin n)) :
    cmul (∑ a ∈ s, C a) D = ∑ a ∈ s, cmul (C a) D := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ms_cmul_zero_left]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, add_cmul, ih]

private theorem ms_cmul_sum {α : Type*} (s : Finset α) (C : Matrix (Fin n) (Fin n) Coef) (D : α → DOp (Fin n)) :
    cmul C (∑ a ∈ s, D a) = ∑ a ∈ s, cmul C (D a) := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ms_cmul_zero_right]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, cmul_add, ih]

private theorem ms_smul_cmul (c : ℂ) (C : Matrix (Fin n) (Fin n) Coef) (D : DOp (Fin n)) : c • cmul C D = cmul (c • C)
    D := by
  unfold cmul
  rw [Finsupp.smul_sum]
  refine Finset.sum_congr rfl fun ab _ => ?_
  beta_reduce
  rw [Finsupp.smul_single, smul_mul_assoc]

private theorem ms_zero_comp (D : DOp (Fin n)) : comp (0 : DOp (Fin n)) D = 0 := by
  have h := smul_comp (0 : ℂ) (0 : DOp (Fin n)) D
  rwa [zero_smul, zero_smul] at h

private theorem ms_comp_zero (D : DOp (Fin n)) : comp D (0 : DOp (Fin n)) = 0 := by
  have h := comp_smul (0 : ℂ) D (0 : DOp (Fin n))
  rwa [zero_smul, zero_smul] at h

private theorem ms_sum_comp {α : Type*} (s : Finset α) (Y : α → DOp (Fin n)) (D : DOp (Fin n)) :
    comp (∑ a ∈ s, Y a) D = ∑ a ∈ s, comp (Y a) D := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ms_zero_comp]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, add_comp, ih]

private theorem ms_comp_sum {α : Type*} (s : Finset α) (D : DOp (Fin n)) (Y : α → DOp (Fin n)) :
    comp D (∑ a ∈ s, Y a) = ∑ a ∈ s, comp D (Y a) := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ms_comp_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, comp_add, ih]

private theorem ms_sub_comp (Y Z D : DOp (Fin n)) : comp (Y - Z) D = comp Y D - comp Z D := by
  rw [sub_eq_add_neg, add_comp, ← neg_one_smul ℂ Z, smul_comp, neg_one_smul, ← sub_eq_add_neg]

private theorem ms_apply_zero (G : ℝ → ℝ → (Fin n → ℂ)) : apply (0 : DOp (Fin n)) G = fun _ _ => 0 := by
  have h := apply_smul (0 : ℂ) (0 : DOp (Fin n)) G
  rw [zero_smul] at h
  rw [h]
  funext t₁ t₂
  rw [zero_smul]

private theorem ms_apply_zero_fun (D : DOp (Fin n)) : apply D (fun (_ : ℝ) (_ : ℝ) => (0 : Fin n → ℂ)) = fun _ _ => 0
    := by
  have h0 : Smooth2 (fun (_ : ℝ) (_ : ℝ) => (0 : Fin n → ℂ)) := contDiff_const
  rw [← ms_apply_zero (fun (_ : ℝ) (_ : ℝ) => (0 : Fin n → ℂ)), ← apply_comp _ _ h0, ms_comp_zero, ms_apply_zero]

private theorem ms_apply_sum {α : Type*} (s : Finset α) (D : α → DOp (Fin n)) (G : ℝ → ℝ → (Fin n → ℂ)) :
    apply (∑ a ∈ s, D a) G = fun t₁ t₂ => ∑ a ∈ s, apply (D a) G t₁ t₂ := by
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, ms_apply_zero]
    funext t₁ t₂
    rw [Finset.sum_empty]
  | cons a s ha ih =>
    rw [Finset.sum_cons, apply_add, ih]
    funext t₁ t₂
    rw [Finset.sum_cons]

private theorem ms_apply_d₁ (G : ℝ → ℝ → (Fin n → ℂ)) : apply (d₁ : DOp (Fin n)) G = d1 G := by
  rw [d₁_eq_mono, apply_mono]
  rfl

end OperatorLinearAlgebra
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

section NormalForms

variable {N₂ N₃ : ℕ}

private abbrev FIdx (N₂ N₃ : ℕ) : Type := Fin 6 × Fin N₂ × Fin N₃

private abbrev blk (𝔐 : Matrix (RIdx N₂ N₃ (Fin n)) (RIdx N₂ N₃ (Fin n)) Coef) (J J' : FIdx N₂ N₃) :
    Matrix (Fin n) (Fin n) Coef :=
  Matrix.of fun i i' => 𝔐 (J.1, J.2.1, J.2.2, i) (J'.1, J'.2.1, J'.2.2, i')

private noncomputable def lc (Ω₂ Ω₃ : DOp (Fin n)) (ν : FIdx N₂ N₃ → Matrix (Fin n) (Fin n) Coef) : DOp (Fin n) :=
  ∑ J, cmul (ν J) (nb Ω₂ Ω₃ J.1 J.2.1 J.2.2)

private theorem lc_eq_sum3 (Ω₂ Ω₃ : DOp (Fin n)) (ν : FIdx N₂ N₃ → Matrix (Fin n) (Fin n) Coef) :
    lc Ω₂ Ω₃ ν = ∑ j, ∑ e, ∑ f, cmul (ν (j, e, f)) (nb Ω₂ Ω₃ j e f) := by
  simp only [lc, Fintype.sum_prod_type]

private theorem lc_add (Ω₂ Ω₃ : DOp (Fin n)) (ν ν' : FIdx N₂ N₃ → Matrix (Fin n) (Fin n) Coef) :
    lc Ω₂ Ω₃ (ν + ν') = lc Ω₂ Ω₃ ν + lc Ω₂ Ω₃ ν' := by
  simp only [lc, Pi.add_apply, add_cmul, Finset.sum_add_distrib]

private theorem lc_zero (Ω₂ Ω₃ : DOp (Fin n)) : lc Ω₂ Ω₃ (0 : FIdx N₂ N₃ → Matrix (Fin n) (Fin n) Coef) = 0 := by
  simp only [lc, Pi.zero_apply, ms_cmul_zero_left, Finset.sum_const_zero]

private theorem lc_neg (Ω₂ Ω₃ : DOp (Fin n)) (ν : FIdx N₂ N₃ → Matrix (Fin n) (Fin n) Coef) :
    lc Ω₂ Ω₃ (-ν) = -lc Ω₂ Ω₃ ν := by
  simp only [lc, Pi.neg_apply, ms_neg_cmul, Finset.sum_neg_distrib]

private theorem lc_sub (Ω₂ Ω₃ : DOp (Fin n)) (ν ν' : FIdx N₂ N₃ → Matrix (Fin n) (Fin n) Coef) :
    lc Ω₂ Ω₃ (ν - ν') = lc Ω₂ Ω₃ ν - lc Ω₂ Ω₃ ν' := by
  rw [sub_eq_add_neg, lc_add, lc_neg, ← sub_eq_add_neg]

private theorem lc_smul (Ω₂ Ω₃ : DOp (Fin n)) (c : ℂ) (ν : FIdx N₂ N₃ → Matrix (Fin n) (Fin n) Coef) :
    lc Ω₂ Ω₃ (c • ν) = c • lc Ω₂ Ω₃ ν := by
  simp only [lc, Pi.smul_apply, Finset.smul_sum, ms_smul_cmul]

private theorem lc_cmul (Ω₂ Ω₃ : DOp (Fin n)) (M : Matrix (Fin n) (Fin n) Coef)
    (ν : FIdx N₂ N₃ → Matrix (Fin n) (Fin n) Coef) :
    cmul M (lc Ω₂ Ω₃ ν) = lc Ω₂ Ω₃ (fun J => M * ν J) := by
  simp only [lc, ms_cmul_sum, cmul_cmul]

private theorem lc_sum {α : Type*} (Ω₂ Ω₃ : DOp (Fin n)) (s : Finset α)
    (ν : α → FIdx N₂ N₃ → Matrix (Fin n) (Fin n) Coef) :
    lc Ω₂ Ω₃ (∑ a ∈ s, ν a) = ∑ a ∈ s, lc Ω₂ Ω₃ (ν a) := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, lc_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, lc_add, ih]

private theorem lc_single (Ω₂ Ω₃ : DOp (Fin n)) (J : FIdx N₂ N₃) (M : Matrix (Fin n) (Fin n) Coef) :
    lc Ω₂ Ω₃ (fun J' => if J' = J then M else 0) = cmul M (nb Ω₂ Ω₃ J.1 J.2.1 J.2.2) := by
  rw [lc, Finset.sum_eq_single J]
  · rw [if_pos rfl]
  · intro J' _ hJ'
    rw [if_neg hJ', ms_cmul_zero_left]
  · intro h
    exact absurd (Finset.mem_univ J) h

variable (Ω₂ Ω₃ : DOp (Fin n)) (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ)

private def HasNF (D : DOp (Fin n)) (ν : FIdx N₂ N₃ → Matrix (Fin n) (Fin n) Coef) : Prop :=
  ∃ Y Y' : DOp (Fin n), D = lc Ω₂ Ω₃ ν + comp Y (polyOp a₂ Ω₂) + comp Y' (polyOp a₃ Ω₃)

variable {Ω₂ Ω₃ a₂ a₃}

private theorem HasNF.congr {D D' : DOp (Fin n)} {ν ν' : FIdx N₂ N₃ → Matrix (Fin n) (Fin n) Coef}
    (h : HasNF Ω₂ Ω₃ a₂ a₃ D ν) (hD : D = D') (hν : ν = ν') : HasNF Ω₂ Ω₃ a₂ a₃ D' ν' := by
  subst hD hν
  exact h

private theorem HasNF.add {D D' : DOp (Fin n)} {ν ν' : FIdx N₂ N₃ → Matrix (Fin n) (Fin n) Coef}
    (h : HasNF Ω₂ Ω₃ a₂ a₃ D ν) (h' : HasNF Ω₂ Ω₃ a₂ a₃ D' ν') : HasNF Ω₂ Ω₃ a₂ a₃ (D + D') (ν + ν') := by
  obtain ⟨Y, Y', rfl⟩ := h
  obtain ⟨Z, Z', rfl⟩ := h'
  refine ⟨Y + Z, Y' + Z', ?_⟩
  rw [lc_add, add_comp, add_comp]
  abel

private theorem HasNF.zero : HasNF Ω₂ Ω₃ a₂ a₃ (0 : DOp (Fin n)) (0 : FIdx N₂ N₃ → Matrix (Fin n) (Fin n) Coef) :=
  ⟨0, 0, by rw [lc_zero, ms_zero_comp, ms_zero_comp, add_zero, add_zero]⟩

private theorem HasNF.smul (c : ℂ) {D : DOp (Fin n)} {ν : FIdx N₂ N₃ → Matrix (Fin n) (Fin n) Coef}
    (h : HasNF Ω₂ Ω₃ a₂ a₃ D ν) : HasNF Ω₂ Ω₃ a₂ a₃ (c • D) (c • ν) := by
  obtain ⟨Y, Y', rfl⟩ := h
  refine ⟨c • Y, c • Y', ?_⟩
  rw [smul_add, smul_add, smul_comp, smul_comp, lc_smul]

private theorem HasNF.sum {α : Type*} (s : Finset α) {D : α → DOp (Fin n)}
    {ν : α → FIdx N₂ N₃ → Matrix (Fin n) (Fin n) Coef} (h : ∀ a ∈ s, HasNF Ω₂ Ω₃ a₂ a₃ (D a) (ν a)) :
    HasNF Ω₂ Ω₃ a₂ a₃ (∑ a ∈ s, D a) (∑ a ∈ s, ν a) := by
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact HasNF.zero
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact (h a (Finset.mem_cons_self a s)).add (ih fun b hb => h b (Finset.mem_cons_of_mem hb))

private theorem HasNF.mul_left (M : Matrix (Fin n) (Fin n) Coef) {D : DOp (Fin n)}
    {ν : FIdx N₂ N₃ → Matrix (Fin n) (Fin n) Coef} (h : HasNF Ω₂ Ω₃ a₂ a₃ D ν) :
    HasNF Ω₂ Ω₃ a₂ a₃ (cmul M D) (fun J => M * ν J) := by
  obtain ⟨Y, Y', rfl⟩ := h
  refine ⟨cmul M Y, cmul M Y', ?_⟩
  rw [cmul_add, cmul_add, cmul_comp, cmul_comp, lc_cmul]

private theorem hasNF_nb (J : FIdx N₂ N₃) :
    HasNF Ω₂ Ω₃ a₂ a₃ (nb Ω₂ Ω₃ J.1 J.2.1 J.2.2) (fun J' => if J' = J then 1 else 0) := by
  refine ⟨0, 0, ?_⟩
  rw [lc_single, cmul_one_eq, ms_zero_comp, ms_zero_comp, add_zero, add_zero]

private theorem HasNF.ideal (Y Y' : DOp (Fin n)) :
    HasNF Ω₂ Ω₃ a₂ a₃ (comp Y (polyOp a₂ Ω₂) + comp Y' (polyOp a₃ Ω₃))
      (0 : FIdx N₂ N₃ → Matrix (Fin n) (Fin n) Coef) :=
  ⟨Y, Y', by rw [lc_zero, zero_add]⟩

private theorem HasNF.unique (hΩ : IsCasimirPair Ω₂ Ω₃) (ha₂ : a₂ (Fin.last N₂) = 1) (ha₃ : a₃ (Fin.last N₃) = 1)
    {D : DOp (Fin n)} {ν ν' : FIdx N₂ N₃ → Matrix (Fin n) (Fin n) Coef} (h : HasNF Ω₂ Ω₃ a₂ a₃ D ν)
    (h' : HasNF Ω₂ Ω₃ a₂ a₃ D ν') : ν = ν' := by
  obtain ⟨Y, Y', hY⟩ := h
  obtain ⟨Z, Z', hZ⟩ := h'
  have hsub : lc Ω₂ Ω₃ (ν - ν') = comp (Z - Y) (polyOp a₂ Ω₂) + comp (Z' - Y') (polyOp a₃ Ω₃) := by
    rw [lc_sub, ms_sub_comp, ms_sub_comp]
    have h1 : lc Ω₂ Ω₃ ν = lc Ω₂ Ω₃ ν' + comp Z (polyOp a₂ Ω₂) + comp Z' (polyOp a₃ Ω₃) - comp Y (polyOp a₂ Ω₂) -
        comp Y' (polyOp a₃ Ω₃) := by
      rw [← hZ, hY]
      abel
    rw [h1]
    abel
  rw [lc_eq_sum3] at hsub
  have h0 := normalForm_unique_mod hΩ a₂ ha₂ a₃ ha₃ (fun j e f => (ν - ν') (j, e, f)) (Z - Y) (Z' - Y') hsub
  funext J
  exact sub_eq_zero.1 (h0 J.1 J.2.1 J.2.2)

private theorem HasNF.comp_d₁ (hΩ : IsCasimirPair Ω₂ Ω₃) {𝔐 : Matrix (RIdx N₂ N₃ (Fin n)) (RIdx N₂ N₃ (Fin n)) Coef}
    (h𝔐 : ∀ (j : Fin 6) (e : Fin N₂) (f : Fin N₃), ∃ Y Y' : DOp (Fin n),
      comp d₁ (nb Ω₂ Ω₃ j e f)
        = (∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃,
            cmul (Matrix.of fun i i' => 𝔐 (j, e, f, i) (j', e', f', i')) (nb Ω₂ Ω₃ j' e' f'))
          + comp Y (polyOp a₂ Ω₂) + comp Y' (polyOp a₃ Ω₃))
    {D : DOp (Fin n)} {ν : FIdx N₂ N₃ → Matrix (Fin n) (Fin n) Coef} (h : HasNF Ω₂ Ω₃ a₂ a₃ D ν) :
    HasNF Ω₂ Ω₃ a₂ a₃ (comp d₁ D) (fun J' => (ν J').map (eul 0) + ∑ J, ν J * blk 𝔐 J J') := by
  have _ := hΩ
  obtain ⟨Y, Y', rfl⟩ := h
  have hnb : ∀ J : FIdx N₂ N₃, HasNF Ω₂ Ω₃ a₂ a₃ (comp d₁ (nb Ω₂ Ω₃ J.1 J.2.1 J.2.2)) (fun J' => blk 𝔐 J J') := by
    intro J
    obtain ⟨Z, Z', hZ⟩ := h𝔐 J.1 J.2.1 J.2.2
    refine ⟨Z, Z', ?_⟩
    rw [hZ, lc_eq_sum3]
  have hterm : ∀ J : FIdx N₂ N₃, HasNF Ω₂ Ω₃ a₂ a₃ (comp d₁ (cmul (ν J) (nb Ω₂ Ω₃ J.1 J.2.1 J.2.2)))
      ((fun J' => if J' = J then (ν J).map (eul 0) else 0) + fun J' => ν J * blk 𝔐 J J') := by
    intro J
    rw [d₁_comp_cmul]
    refine HasNF.add ?_ ((hnb J).mul_left (ν J))
    have h1 := (hasNF_nb (Ω₂ := Ω₂) (Ω₃ := Ω₃) (a₂ := a₂) (a₃ := a₃) J).mul_left ((ν J).map (eul 0))
    refine h1.congr rfl ?_
    funext J'
    beta_reduce
    split_ifs
    · rw [mul_one]
    · rw [mul_zero]
  have hlc : HasNF Ω₂ Ω₃ a₂ a₃ (comp d₁ (lc Ω₂ Ω₃ ν)) (fun J' => (ν J').map (eul 0) + ∑ J, ν J * blk 𝔐 J J') := by
    rw [lc, ms_comp_sum]
    refine (HasNF.sum Finset.univ fun J _ => hterm J).congr rfl ?_
    funext J'
    simp only [Finset.sum_apply, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hid : HasNF Ω₂ Ω₃ a₂ a₃ (comp d₁ (comp Y (polyOp a₂ Ω₂) + comp Y' (polyOp a₃ Ω₃)))
      (0 : FIdx N₂ N₃ → Matrix (Fin n) (Fin n) Coef) := by
    rw [comp_add, ← comp_assoc, ← comp_assoc]
    exact HasNF.ideal _ _
  have h := hlc.add hid
  rw [add_zero] at h
  refine h.congr ?_ rfl
  rw [add_assoc, comp_add, comp_add, comp_add]

end NormalForms
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

section Evaluations

private theorem ms_ev_sum {α : Type*} (s : Finset α) (f : α → Coef) (t₁ t₂ : ℝ) :
    (∑ a ∈ s, f a).ev t₁ t₂ = ∑ a ∈ s, (f a).ev t₁ t₂ := by
  unfold Coef.ev
  exact map_sum (MvPolynomial.eval _) f s

private theorem ms_ev_zero (t₁ t₂ : ℝ) : (0 : Coef).ev t₁ t₂ = 0 := by
  unfold Coef.ev
  exact map_zero _

private theorem ms_ev_ite (p : Prop) [Decidable p] (a b : Coef) (t₁ t₂ : ℝ) :
    (if p then a else b).ev t₁ t₂ = if p then a.ev t₁ t₂ else b.ev t₁ t₂ := by
  split_ifs <;> rfl

private theorem ms_mev_apply {ι : Type} [Fintype ι] [DecidableEq ι] (C : Matrix ι ι Coef) (t₁ t₂ : ℝ) (i i' : ι) :
    mev C t₁ t₂ i i' = (C i i').ev t₁ t₂ := rfl

end Evaluations
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

section WallAlgebra

private theorem ms_killX0_C (a : ℂ) : killX0 (MvPolynomial.C a) = MvPolynomial.C a := by
  unfold killX0
  rw [MvPolynomial.aeval_C]
  rfl

private theorem ms_killX0_X0 : killX0 (MvPolynomial.X 0 : Coef) = 0 := by
  unfold killX0
  rw [MvPolynomial.aeval_X]
  rfl

private theorem ms_killX0_X1 : killX0 (MvPolynomial.X 1 : Coef) = MvPolynomial.X 1 := by
  unfold killX0
  rw [MvPolynomial.aeval_X]
  rfl

private theorem ms_killX0_killX0 (p : Coef) : killX0 (killX0 p) = killX0 p := by
  have h : killX0.comp killX0 = killX0 := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply]
    fin_cases i
    · show killX0 (killX0 (MvPolynomial.X 0)) = killX0 (MvPolynomial.X 0)
      rw [ms_killX0_X0, map_zero]
    · show killX0 (killX0 (MvPolynomial.X 1)) = killX0 (MvPolynomial.X 1)
      rw [ms_killX0_X1, ms_killX0_X1]
  exact AlgHom.congr_fun h p

private theorem ms_constantCoeff_killX0 (p : Coef) :
    MvPolynomial.constantCoeff (killX0 p) = MvPolynomial.constantCoeff p := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [ms_killX0_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p i hp =>
    have _ := hp
    rw [map_mul, map_mul, map_mul, MvPolynomial.constantCoeff_X, mul_zero]
    suffices h : MvPolynomial.constantCoeff (killX0 (MvPolynomial.X i)) = 0 by rw [h, mul_zero]
    unfold killX0
    rw [MvPolynomial.aeval_X]
    fin_cases i <;> simp

private theorem ms_sum_ite_const {α β : Type*} [AddCommMonoid β] (s : Finset α) (p : Prop) [Decidable p] (f : α → β) :
    (∑ a ∈ s, if p then f a else 0) = if p then ∑ a ∈ s, f a else 0 := by
  split_ifs <;> simp

variable {N₂ N₃ : ℕ}

private def bl (T : Matrix (Fin n) (Fin n) ℂ) : Matrix (RIdx N₂ N₃ (Fin n)) (RIdx N₂ N₃ (Fin n)) ℂ := fun K K' =>
  if K.1 = K'.1 then if K.2.1 = K'.2.1 then if K.2.2.1 = K'.2.2.1 then T K.2.2.2 K'.2.2.2 else 0 else 0 else 0

private theorem bl_mul_apply (T : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (RIdx N₂ N₃ (Fin n)) (RIdx N₂ N₃ (Fin n)) ℂ)
    (K K' : RIdx N₂ N₃ (Fin n)) :
    (bl T * X : Matrix (RIdx N₂ N₃ (Fin n)) (RIdx N₂ N₃ (Fin n)) ℂ) K K' =
      ∑ k, T K.2.2.2 k * X (K.1, K.2.1, K.2.2.1, k) K' := by
  rw [Matrix.mul_apply]
  simp only [bl, Fintype.sum_prod_type, ite_mul, zero_mul, ms_sum_ite_const, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

private theorem mul_bl_apply (T : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (RIdx N₂ N₃ (Fin n)) (RIdx N₂ N₃ (Fin n)) ℂ)
    (K K' : RIdx N₂ N₃ (Fin n)) :
    (X * bl T : Matrix (RIdx N₂ N₃ (Fin n)) (RIdx N₂ N₃ (Fin n)) ℂ) K K' =
      ∑ k, X K (K'.1, K'.2.1, K'.2.2.1, k) * T k K'.2.2.2 := by
  rw [Matrix.mul_apply]
  simp only [bl, Fintype.sum_prod_type, mul_ite, mul_zero, ms_sum_ite_const]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem bl_mul_bl (T T' : Matrix (Fin n) (Fin n) ℂ) :
    (bl T * bl T' : Matrix (RIdx N₂ N₃ (Fin n)) _ ℂ) = bl (T * T') := by
  ext K K'
  rw [bl_mul_apply]
  simp only [bl, mul_ite, mul_zero, ms_sum_ite_const, Matrix.mul_apply]

private theorem bl_one : (bl 1 : Matrix (RIdx N₂ N₃ (Fin n)) (RIdx N₂ N₃ (Fin n)) ℂ) = 1 := by
  ext K K'
  simp only [bl, Matrix.one_apply, Prod.ext_iff]
  by_cases h1 : K.1 = K'.1 <;> by_cases h2 : K.2.1 = K'.2.1 <;> by_cases h3 : K.2.2.1 = K'.2.2.1 <;>
    by_cases h4 : K.2.2.2 = K'.2.2.2 <;> simp [h1, h2, h3, h4]

private theorem ms_aeval_conj {m : Type*} [Fintype m] [DecidableEq m] (P M Q : Matrix m m ℂ) (hQP : Q * P = 1)
    (hPQ : P * Q = 1) (p : Polynomial ℂ) : Polynomial.aeval (P * M * Q) p = P * Polynomial.aeval M p * Q := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, Matrix.mul_add, Matrix.add_mul]
  | monomial k a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial]
    have hpow : (P * M * Q) ^ k = P * M ^ k * Q := by
      induction k with
      | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hPQ]
      | succ k ih =>
        rw [pow_succ, ih, pow_succ]
        simp only [mul_assoc]
        rw [← mul_assoc Q P, hQP, Matrix.one_mul]
    rw [hpow]
    simp only [mul_assoc]
    rw [← mul_assoc, Algebra.commutes a P, mul_assoc]

private theorem ms_mul_aeval_factor {m m' : Type*} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
    (A : Matrix m m' ℂ) (M : Matrix m' m' ℂ) (C : Matrix m' m ℂ) (hCA : C * A = 1) (p : Polynomial ℂ) :
    A * M * C * Polynomial.aeval (A * M * C) p = A * (M * Polynomial.aeval M p) * C := by
  have hpow : ∀ k : ℕ, (A * M * C) ^ (k + 1) = A * M ^ (k + 1) * C := by
    intro k
    induction k with
    | zero => rw [zero_add, pow_one, pow_one]
    | succ k ih =>
      rw [pow_succ, ih, pow_succ M (k + 1), Matrix.mul_assoc (A * M ^ (k + 1)) C (A * M * C),
        ← Matrix.mul_assoc C (A * M) C, ← Matrix.mul_assoc C A M, hCA, Matrix.one_mul,
        Matrix.mul_assoc A (M ^ (k + 1)) (M * C),
        ← Matrix.mul_assoc (M ^ (k + 1)) M C, Matrix.mul_assoc A (M ^ (k + 1) * M) C]
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Matrix.mul_sum, Matrix.mul_sum, Matrix.mul_sum,
    Matrix.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, ← pow_succ', ← pow_succ', hpow]

private theorem ms_aeval_X_mul {m : Type*} [Fintype m] [DecidableEq m] (Y : Matrix m m ℂ) (p : Polynomial ℂ) :
    Polynomial.aeval Y (Polynomial.X * p) = Y * Polynomial.aeval Y p := by
  rw [map_mul, Polynomial.aeval_X]

end WallAlgebra
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

private theorem exists_master_system (N₂ N₃ L : ℕ) (hL : 3 + 2 * N₂ + 3 * N₃ ≤ L) : ∃ d : ℕ,
    ∀ (ω₂ ω₃ : ℕ × ℕ → ℂ) (a₂ : Fin (N₂ + 1) → ℂ), a₂ (Fin.last N₂) = 1 →
    ∀ (a₃ : Fin (N₃ + 1) → ℂ), a₃ (Fin.last N₃) = 1 →
    ∀ (Ωs₂ Ωs₃ : DOp Unit), IsCasimirPair Ωs₂ Ωs₃ →
    (∀ ab, Ωs₂ ab = fun _ _ => MvPolynomial.C (ω₂ ab)) → (∀ ab, Ωs₃ ab = fun _ _ => MvPolynomial.C (ω₃ ab)) →
    ∃ q : Polynomial ℂ, q ≠ 0 ∧ q.natDegree ≤ 6 * N₂ * N₃ + 1 ∧
    ∀ (n : ℕ) (Ω₂ Ω₃ : DOp (Fin n)) (𝒟 : (k : ℕ) → (Fin k → Fin 3 × Fin 3) → DOp (Fin n)),
    IsCasimirPair Ω₂ Ω₃ → IsWordFamily Ω₂ Ω₃ 𝒟 →
    (∀ ab, (Ω₂ ab).map MvPolynomial.constantCoeff = ω₂ ab • (1 : Matrix (Fin n) (Fin n) ℂ)) →
    (∀ ab, (Ω₃ ab).map MvPolynomial.constantCoeff = ω₃ ab • (1 : Matrix (Fin n) (Fin n) ℂ)) →
    (∀ (ab : ℕ × ℕ) (i i' : Fin n), (Ω₂ ab i i').totalDegree ≤ 3) →
    (∀ (ab : ℕ × ℕ) (i i' : Fin n), (Ω₃ ab i i').totalDegree ≤ 3) →
    ∀ (U : Matrix (Fin n) (Fin n) ℂ) (zw : Fin n → ℂ) (φ₂ φ₃ : ℕ × ℕ → ℂ → Coef), IsUnit U.det →
    (∀ ab c, killX0 (φ₂ ab c) = φ₂ ab c) → (∀ ab c, killX0 (φ₃ ab c) = φ₃ ab c) →
    (∀ (ab : ℕ × ℕ) (i i' : Fin n), killX0 (conjOp U Ω₂ ab i i') = if i = i' then φ₂ ab (zw i) else 0) →
    (∀ (ab : ℕ × ℕ) (i i' : Fin n), killX0 (conjOp U Ω₃ ab i i') = if i = i' then φ₃ ab (zw i) else 0) →
    (∀ i, IsCasimirPair (diagEntry i (cmap killX0 (conjOp U Ω₂))) (diagEntry i (cmap killX0 (conjOp U Ω₃)))) →
    ∃ R : Matrix (PWord L × Fin n) (PWord L × Fin n) Coef,
      (∀ μ ν, (R μ ν).totalDegree ≤ d) ∧
      (∀ x : Fin 2 → ℂ, Polynomial.aeval ((R.map killX0).map (MvPolynomial.eval x)) q = 0) ∧
      ∀ Φ₀ : ℝ → ℝ → (Fin n → ℂ), Smooth2 Φ₀ →
        apply (polyOp a₂ Ω₂) Φ₀ = (fun _ _ => 0) → apply (polyOp a₃ Ω₃) Φ₀ = (fun _ _ => 0) →
        ∀ t₁ t₂ : ℝ, HasDerivAt (fun s => master L 𝒟 Φ₀ s t₂) (mev R t₁ t₂ *ᵥ master L 𝒟 Φ₀ t₁ t₂) t₁ := by
  classical
  obtain ⟨δ, hδ⟩ := exists_reduce_totalDegree_le (L + 1) (L + 1) 3 N₂ N₃
  refine ⟨δ, ?_⟩
  intro ω₂ ω₃ a₂ ha₂ a₃ ha₃ Ωs₂ Ωs₃ hΩs hΩs₂ hΩs₃
  obtain ⟨Ms, Ms', hMs1, -, -, -, -⟩ := exists_connection hΩs a₂ ha₂ a₃ ha₃
  have _ := hΩs₂
  have _ := hΩs₃
  have _ := hMs1
  refine ⟨Polynomial.X * (Ms.map MvPolynomial.constantCoeff).charpoly, ?_, ?_, ?_⟩
  · exact mul_ne_zero Polynomial.X_ne_zero (Matrix.charpoly_monic _).ne_zero
  · rw [Polynomial.natDegree_mul Polynomial.X_ne_zero (Matrix.charpoly_monic _).ne_zero, Polynomial.natDegree_X,
      Matrix.charpoly_natDegree_eq_dim]
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_unit, mul_one]
    rw [Nat.mul_assoc]
    omega
  intro n Ω₂ Ω₃ 𝒟 hΩ h𝒟 hω₂ hω₃ hdΩ₂ hdΩ₃ U zw φ₂ φ₃ hU hφ₂ hφ₃ hUΩ₂ hUΩ₃ hΩw

  have hred : ∀ (k : ℕ) (hk : k ≤ L + 1) (w : Fin k → Fin 3 × Fin 3),
      ∃ (ν : Fin 6 → Fin N₂ → Fin N₃ → Matrix (Fin n) (Fin n) Coef) (Y Y' : DOp (Fin n)),
        𝒟 k w = (∑ j, ∑ e, ∑ f, cmul (ν j e f) (nb Ω₂ Ω₃ j e f)) + comp Y (polyOp a₂ Ω₂) + comp Y' (polyOp a₃ Ω₃) ∧
          ∀ j e f (i i' : Fin n), (ν j e f i i').totalDegree ≤ δ :=
    fun k hk w => hδ hΩ hdΩ₂ hdΩ₃ a₂ ha₂ a₃ ha₃ (𝒟 k w)
      ((h𝒟.hasOrder k w).mono_le hk) (fun ab i i' => (h𝒟.totalDegree_le k w ab i i').trans hk)
  choose ν Y Y' hνeq hνdeg using hred
  have hNF : ∀ (k : ℕ) (hk : k ≤ L + 1) (w : Fin k → Fin 3 × Fin 3),
      HasNF Ω₂ Ω₃ a₂ a₃ (𝒟 k w) (fun J => ν k hk w J.1 J.2.1 J.2.2) :=
    fun k hk w => ⟨Y k hk w, Y' k hk w, by rw [lc_eq_sum3]; exact hνeq k hk w⟩
  have _ := hNF

  choose Cf hCf using fun J : FIdx N₂ N₃ => h𝒟.exists_frame_coeffs hL J.1 J.2.1 J.2.2
  have hpre : ∀ v : PWord L, ∃ c : (Fin (v.len + 1) → Fin 3 × Fin 3) → ℂ,
      (∑ w, c w • 𝒟 (v.len + 1) w) = comp d₁ (𝒟 v.len v.toFn) :=
    fun v => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (h𝒟.d₁_comp v.len v.toFn)
  choose P hP using hpre
  have hvL : ∀ v : PWord L, v.len ≤ L + 1 := fun v => Nat.le_succ_of_le (Nat.le_of_lt_succ v.1.1.2)
  have hvL1 : ∀ v : PWord L, v.len + 1 ≤ L + 1 := fun v => Nat.succ_le_succ (Nat.le_of_lt_succ v.1.1.2)
  have _ := hvL

  set Rd : Matrix (PWord L × Fin n) (RIdx N₂ N₃ (Fin n)) Coef := fun μ K =>
    ∑ w, MvPolynomial.C (P μ.1 w) * ν (μ.1.len + 1) (hvL1 μ.1) w K.1 K.2.1 K.2.2.1 μ.2 K.2.2.2 with hRd
  set Cm : Matrix (RIdx N₂ N₃ (Fin n)) (PWord L × Fin n) Coef := fun K μ =>
    if K.2.2.2 = μ.2 then MvPolynomial.C (Cf (K.1, K.2.1, K.2.2.1) μ.1) else 0 with hCm
  refine ⟨Rd * Cm, ?_, ?_, ?_⟩
  ·
    intro μ μ'
    rw [Matrix.mul_apply]
    refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun K _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have hC : (Cm K μ').totalDegree = 0 := by
      rw [hCm]
      beta_reduce
      split_ifs
      · exact MvPolynomial.totalDegree_C _
      · exact MvPolynomial.totalDegree_zero
    rw [hC, add_zero, hRd]
    refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun w _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact hνdeg _ _ _ _ _ _ _ _
  ·
    intro x
    obtain ⟨𝔐, 𝔐', h𝔐1, -, -, -, -⟩ := exists_connection hΩ a₂ ha₂ a₃ ha₃
    have _ := 𝔐'
    set Rb : Matrix (PWord L × Fin n) (RIdx N₂ N₃ (Fin n)) Coef := fun μ K =>
      ν μ.1.len (hvL μ.1) μ.1.toFn K.1 K.2.1 K.2.2.1 μ.2 K.2.2.2 with hRb

    have hRd_eq : Rd = Rb.map (eul 0) + Rb * 𝔐 := by
      refine Matrix.ext fun μ K => ?_
      obtain ⟨v, l⟩ := μ
      obtain ⟨j', e', f', l'⟩ := K
      have hA : HasNF Ω₂ Ω₃ a₂ a₃ (comp d₁ (𝒟 v.len v.toFn))
          (∑ w, P v w • fun J => ν (v.len + 1) (hvL1 v) w J.1 J.2.1 J.2.2) := by
        rw [← hP v]
        exact HasNF.sum _ fun w _ => (hNF _ (hvL1 v) w).smul (P v w)
      have hB := (hNF v.len (hvL v) v.toFn).comp_d₁ hΩ h𝔐1
      have hAB := HasNF.unique hΩ ha₂ ha₃ hA hB
      have h2 := congrArg (fun m : FIdx N₂ N₃ → Matrix (Fin n) (Fin n) Coef => m (j', e', f') l l') hAB
      simp only [Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply, MvPolynomial.smul_eq_C_mul,
        Matrix.add_apply, Matrix.map_apply, Matrix.mul_apply, blk, Matrix.of_apply] at h2
      rw [Matrix.add_apply, Matrix.map_apply, Matrix.mul_apply, hRd, hRb]
      beta_reduce
      rw [h2]
      simp only [Fintype.sum_prod_type]

    have hCmRb : Cm * Rb = 1 := by
      refine Matrix.ext fun K μ => ?_
      obtain ⟨j, e, f, l⟩ := K
      obtain ⟨j', e', f', l'⟩ := μ
      have hA : HasNF Ω₂ Ω₃ a₂ a₃ (nb Ω₂ Ω₃ j e f)
          (∑ v, Cf (j, e, f) v • fun J => ν v.len (hvL v) v.toFn J.1 J.2.1 J.2.2) := by
        have hC := hCf (j, e, f)
        dsimp only at hC
        rw [← hC]
        exact HasNF.sum _ fun v _ => (hNF _ (hvL v) _).smul _
      have hB := hasNF_nb (Ω₂ := Ω₂) (Ω₃ := Ω₃) (a₂ := a₂) (a₃ := a₃) ((j, e, f) : FIdx N₂ N₃)
      dsimp only at hB
      have hAB := HasNF.unique hΩ ha₂ ha₃ hA hB
      have h2 := congrArg (fun m : FIdx N₂ N₃ → Matrix (Fin n) (Fin n) Coef => m (j', e', f') l l') hAB
      simp only [Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply, MvPolynomial.smul_eq_C_mul]
        at h2
      rw [Matrix.mul_apply, Fintype.sum_prod_type, hCm, hRb]
      beta_reduce
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Matrix.one_apply]
      split_ifs at h2 with hJ
      · rw [h2, Matrix.one_apply]
        simp only [Prod.mk.injEq] at hJ
        obtain ⟨rfl, rfl, rfl⟩ := hJ
        by_cases hl : l = l'
        · subst hl
          rw [if_pos rfl, if_pos rfl]
        · rw [if_neg hl, if_neg]
          intro h
          simp only [Prod.mk.injEq] at h
          exact hl h.2.2.2
      · rw [h2, Matrix.zero_apply, if_neg]
        intro h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, -⟩ := h
        exact hJ rfl

    obtain ⟨hΩU, h𝔐U⟩ := connection_conj hΩ a₂ a₃ U hU 𝔐 h𝔐1
    have hΩU' : IsCasimirPair (conjOp U Ω₂) (conjOp U Ω₃) := hΩU
    obtain ⟨𝔐U, h𝔐U_def⟩ : ∃ M : Matrix (RIdx N₂ N₃ (Fin n)) (RIdx N₂ N₃ (Fin n)) Coef, M = fun K K' =>
        ((U.map MvPolynomial.C * (Matrix.of fun k k' => 𝔐 (K.1, K.2.1, K.2.2.1, k) (K'.1, K'.2.1, K'.2.2.1, k')) *
          U⁻¹.map MvPolynomial.C : Matrix (Fin n) (Fin n) Coef) K.2.2.2 K'.2.2.2) := ⟨_, rfl⟩
    have h𝔐U' : ∀ (j : Fin 6) (e : Fin N₂) (f : Fin N₃), ∃ Y Y' : DOp (Fin n),
        comp d₁ (nb (conjOp U Ω₂) (conjOp U Ω₃) j e f)
          = (∑ j' : Fin 6, ∑ e' : Fin N₂, ∑ f' : Fin N₃,
              cmul (Matrix.of fun i i' => 𝔐U (j, e, f, i) (j', e', f', i'))
                (nb (conjOp U Ω₂) (conjOp U Ω₃) j' e' f'))
            + comp Y (polyOp a₂ (conjOp U Ω₂)) + comp Y' (polyOp a₃ (conjOp U Ω₃)) := by
      intro j e f
      rw [h𝔐U_def]
      exact h𝔐U j e f
    have hΩw₂ : ∀ i ab, diagEntry i (cmap killX0 (conjOp U Ω₂)) ab = fun _ _ => φ₂ ab (zw i) :=
      fun i ab => diagEntry_cmap_killX0_conjOp_apply φ₂ U zw Ω₂ hUΩ₂ i ab
    have hΩw₃ : ∀ i ab, diagEntry i (cmap killX0 (conjOp U Ω₃)) ab = fun _ _ => φ₃ ab (zw i) :=
      fun i ab => diagEntry_cmap_killX0_conjOp_apply φ₃ U zw Ω₃ hUΩ₃ i ab
    choose Mw Mw' hMw1 hMw2 hMw3 hMw4 hMw5 using fun i => exists_connection (hΩw i) a₂ ha₂ a₃ ha₃
    have _ := hMw2
    have _ := hMw3
    have _ := hMw4
    have hblk := connection_killX0_blockDiagonal hΩU' a₂ ha₂ a₃ ha₃ zw φ₂ φ₃ hφ₂ hφ₃ hUΩ₂ hUΩ₃ 𝔐U h𝔐U'
      (fun i => diagEntry i (cmap killX0 (conjOp U Ω₂))) (fun i => diagEntry i (cmap killX0 (conjOp U Ω₃))) hΩw
      hΩw₂ hΩw₃ Mw hMw1

    have hcc : ∀ (Ω : DOp (Fin n)) (ω : ℕ × ℕ → ℂ) (φ : ℕ × ℕ → ℂ → Coef),
        (∀ ab, (Ω ab).map MvPolynomial.constantCoeff = ω ab • (1 : Matrix (Fin n) (Fin n) ℂ)) →
        (∀ (ab : ℕ × ℕ) (i i' : Fin n), killX0 (conjOp U Ω ab i i') = if i = i' then φ ab (zw i) else 0) →
        ∀ i ab, MvPolynomial.constantCoeff (φ ab (zw i)) = ω ab := by
      intro Ω ω φ hω hφ i ab
      have h1 := hφ ab i i
      rw [if_pos rfl] at h1
      rw [← h1, ms_constantCoeff_killX0]
      have hmap : ∀ (X : Matrix (Fin n) (Fin n) Coef) (k k' : Fin n),
          MvPolynomial.constantCoeff (X k k') = X.map MvPolynomial.constantCoeff k k' := fun X k k' => rfl
      simp only [conjOp, Finsupp.mapRange_apply]
      rw [hmap (U.map MvPolynomial.C * Ω ab * U⁻¹.map MvPolynomial.C) i i, Matrix.map_mul, Matrix.map_mul,
        Matrix.map_map, Matrix.map_map, hω]
      have hcC : (⇑(MvPolynomial.constantCoeff : Coef →+* ℂ) ∘ ⇑(MvPolynomial.C : ℂ →+* Coef)) = id :=
        funext fun a => by simp
      rw [hcC, Matrix.map_id, Matrix.map_id, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        Matrix.mul_nonsing_inv _ hU, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    have hωw₂ : ∀ i ab, (diagEntry i (cmap killX0 (conjOp U Ω₂)) ab).map MvPolynomial.constantCoeff =
        ω₂ ab • (1 : Matrix Unit Unit ℂ) := by
      intro i ab
      rw [hΩw₂ i ab]
      ext u u'
      rw [Matrix.map_apply, hcc Ω₂ ω₂ φ₂ hω₂ hUΩ₂ i ab, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    have hωw₃ : ∀ i ab, (diagEntry i (cmap killX0 (conjOp U Ω₃)) ab).map MvPolynomial.constantCoeff =
        ω₃ ab • (1 : Matrix Unit Unit ℂ) := by
      intro i ab
      rw [hΩw₃ i ab]
      ext u u'
      rw [Matrix.map_apply, hcc Ω₃ ω₃ φ₃ hω₃ hUΩ₃ i ab, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    have h5d : ∀ i, ∀ (J J' : FIdx N₂ N₃) (u u' : Unit),
        MvPolynomial.constantCoeff (Mw i (J.1, J.2.1, J.2.2, u) (J'.1, J'.2.1, J'.2.2, u')) =
          if u = u' then MvPolynomial.constantCoeff (Ms (J.1, J.2.1, J.2.2, ()) (J'.1, J'.2.1, J'.2.2, ())) else 0 :=
      fun i => connection_wall0_scalar (hΩw i) a₂ ha₂ a₃ ha₃ ω₂ ω₃ (hωw₂ i) (hωw₃ i) (Mw i) (hMw1 i) Ωs₂ Ωs₃ hΩs hΩs₂
        hΩs₃ Ms hMs1
    have h5f := aeval_charpoly_eq_zero_of_blockDiagonal (𝔐U.map killX0) (fun i => (Mw i).map killX0)
      (fun i => -((Mw' i).map killX0)) (Ms.map MvPolynomial.constantCoeff)
      (fun J J' i i' => by simp only [Matrix.map_apply]; exact hblk J J' i i')
      (fun i => by ext K K'; simp only [Matrix.map_apply, ms_killX0_killX0])
      (fun i => by rw [hMw5 i, Matrix.mul_neg, Matrix.neg_mul]; abel)
      (fun i => by
        refine Matrix.ext fun K K' => ?_
        obtain ⟨j, e, f, u⟩ := K
        obtain ⟨j', e', f', u'⟩ := K'
        simp only [Matrix.map_apply, ms_constantCoeff_killX0]
        have h := h5d i (j, e, f) (j', e', f') u u'
        dsimp only at h
        rw [h, if_pos (Subsingleton.elim u u')]) x

    set g : Coef →+* ℂ := (MvPolynomial.eval x).comp (killX0 : Coef →ₐ[ℂ] Coef).toRingHom with hg
    have hgC : ∀ a : ℂ, g (MvPolynomial.C a) = a := fun a => by
      rw [hg, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, ms_killX0_C, MvPolynomial.eval_C]
    have hmapg : ∀ {m m' : Type} [Fintype m] [Fintype m'] (X : Matrix m m' Coef),
        (X.map killX0).map (MvPolynomial.eval x) = X.map g := fun X => by
      rw [Matrix.map_map]
      rfl
    have h𝔐U_g : 𝔐U.map g = bl U * 𝔐.map g * bl U⁻¹ := by
      ext K K'
      rw [mul_bl_apply, Matrix.map_apply, h𝔐U_def]
      beta_reduce
      rw [Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun k' _ => ?_
      rw [Matrix.mul_apply, Finset.sum_mul, map_sum, bl_mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, map_mul, Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, Matrix.of_apply, hgC, hgC]
    have hUU : bl U * bl U⁻¹ = (1 : Matrix (RIdx N₂ N₃ (Fin n)) (RIdx N₂ N₃ (Fin n)) ℂ) := by
      rw [bl_mul_bl, Matrix.mul_nonsing_inv _ hU, bl_one]
    have hUU' : bl U⁻¹ * bl U = (1 : Matrix (RIdx N₂ N₃ (Fin n)) (RIdx N₂ N₃ (Fin n)) ℂ) := by
      rw [bl_mul_bl, Matrix.nonsing_inv_mul _ hU, bl_one]
    have hwall𝔐 : Polynomial.aeval (𝔐.map g) (Ms.map MvPolynomial.constantCoeff).charpoly = 0 := by
      rw [hmapg, h𝔐U_g, ms_aeval_conj _ _ _ hUU' hUU] at h5f
      have h := congrArg (fun Y => bl U⁻¹ * Y * bl U) h5f
      beta_reduce at h
      simp only [Matrix.mul_zero, Matrix.zero_mul, mul_assoc] at h
      rw [hUU', Matrix.mul_one, ← mul_assoc, hUU', Matrix.one_mul] at h
      exact h

    have hReul : (Rb.map (eul 0)).map g = 0 := by
      ext μ K
      rw [Matrix.map_apply, Matrix.map_apply, hg, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        killX0_eul0, map_zero, Matrix.zero_apply]
    have hCA : Cm.map g * Rb.map g = 1 := by
      rw [← Matrix.map_mul, hCmRb, Matrix.map_one _ (map_zero g) (map_one g)]
    rw [hmapg, Matrix.map_mul, hRd_eq, Matrix.map_add _ (map_add g), Matrix.map_mul, hReul, zero_add, ms_aeval_X_mul,
      ms_mul_aeval_factor _ _ _ hCA, hwall𝔐, Matrix.mul_zero, Matrix.mul_zero, Matrix.zero_mul]
  ·
    intro Φ₀ hΦ h₂ h₃ t₁ t₂
    have happ : ∀ (k : ℕ) (hk : k ≤ L + 1) (w : Fin k → Fin 3 × Fin 3) (s₁ s₂ : ℝ) (l : Fin n),
        apply (𝒟 k w) Φ₀ s₁ s₂ l = ∑ K : RIdx N₂ N₃ (Fin n), (ν k hk w K.1 K.2.1 K.2.2.1 l K.2.2.2).ev s₁ s₂ *
          frame Ω₂ Ω₃ N₂ N₃ Φ₀ s₁ s₂ K := by
      intro k hk w s₁ s₂ l
      rw [hνeq k hk w, apply_add, apply_add]
      beta_reduce
      rw [apply_comp _ _ hΦ, apply_comp _ _ hΦ, h₂, h₃, ms_apply_zero_fun, ms_apply_zero_fun]
      simp only [Pi.add_apply, Pi.zero_apply, add_zero, ms_apply_sum, Finset.sum_apply, apply_cmul, Matrix.mulVec,
        dotProduct, ms_mev_apply, Fintype.sum_prod_type]
      rfl
    have hframe : ∀ (s₁ s₂ : ℝ) (K : RIdx N₂ N₃ (Fin n)), frame Ω₂ Ω₃ N₂ N₃ Φ₀ s₁ s₂ K =
        ∑ μ : PWord L × Fin n, (Cm K μ).ev s₁ s₂ * master L 𝒟 Φ₀ s₁ s₂ μ := by
      intro s₁ s₂ K
      have hC := hCf (K.1, K.2.1, K.2.2.1)
      dsimp only at hC
      show apply (nb Ω₂ Ω₃ K.1 K.2.1 K.2.2.1) Φ₀ s₁ s₂ K.2.2.2 = _
      rw [Fintype.sum_prod_type, ← hC, ms_apply_sum]
      simp only [Finset.sum_apply, apply_smul, Pi.smul_apply, smul_eq_mul, hCm, master, ms_ev_ite, ev_C, ms_ev_zero,
        ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hder : ∀ (v : PWord L) (l : Fin n), d1 (apply (𝒟 v.len v.toFn) Φ₀) t₁ t₂ l =
        ∑ K : RIdx N₂ N₃ (Fin n), (Rd (v, l) K).ev t₁ t₂ * frame Ω₂ Ω₃ N₂ N₃ Φ₀ t₁ t₂ K := by
      intro v l
      rw [← ms_apply_d₁, ← apply_comp _ _ hΦ, ← hP v, ms_apply_sum]
      simp only [Finset.sum_apply, apply_smul, Pi.smul_apply, smul_eq_mul, happ (v.len + 1) (hvL1 v), hRd,
        ms_ev_sum, ev_mul, ev_C, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [mul_assoc]
    refine hasDerivAt_pi.2 fun μ => ?_
    have hsm : Smooth2 (apply (𝒟 μ.1.len μ.1.toFn) Φ₀) := Smooth2.apply _ hΦ
    have hd : HasDerivAt (fun s => master L 𝒟 Φ₀ s t₂ μ) (d1 (apply (𝒟 μ.1.len μ.1.toFn) Φ₀) t₁ t₂ μ.2) t₁ :=
      hasDerivAt_pi.1 (Smooth2.hasDerivAt_d1 hsm t₁ t₂) μ.2
    have hval : d1 (apply (𝒟 μ.1.len μ.1.toFn) Φ₀) t₁ t₂ μ.2 = (mev (Rd * Cm) t₁ t₂ *ᵥ master L 𝒟 Φ₀ t₁ t₂) μ := by
      rw [hder]
      simp only [Matrix.mulVec, dotProduct, ms_mev_apply, Matrix.mul_apply, ms_ev_sum, ev_mul, hframe, Finset.mul_sum,
        Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [mul_assoc]
    rw [hval] at hd
    exact hd

section WordFamily

private abbrev Ltr : Type := Fin 3 × Fin 3

private theorem wordOp_cons (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ) (k : ℕ) (x : Ltr)
    (u : Fin k → Ltr) :
    wordOp S cω (k + 1) (Fin.cons x u) = letterOp S cω x u (wordOp S cω k) := by
  rw [wordOp_succ]
  simp only [Fin.cons_zero, Fin.tail_cons]

private theorem cons_append₂ {k : ℕ} (x : Ltr) (u : Fin k → Ltr) (v : Fin 2 → Ltr) :
    Fin.append (Fin.cons x u) v = Fin.cons x (Fin.append u v) := by
  rw [Fin.append_cons]
  rfl

private theorem nil_append₂ (u : Fin 0 → Ltr) (v : Fin 2 → Ltr) : Fin.append u v = v := by
  rw [Fin.append_left_nil u v rfl]
  rfl

private theorem update_append_left₂ {k : ℕ} (u : Fin k → Ltr) (v : Fin 2 → Ltr) (q : Fin k) (ef : Ltr) :
    Function.update (Fin.append u v) (Fin.castAdd 2 q) ef = Fin.append (Function.update u q ef) v := by
  refine funext (Fin.addCases (fun q' => ?_) fun r => ?_)
  · rw [Fin.append_left, Function.update_apply, Function.update_apply]
    by_cases h : q' = q
    · subst h; simp
    · rw [if_neg h, if_neg (fun h' => h (Fin.ext (by simpa [Fin.ext_iff] using h'))), Fin.append_left]
  · rw [Fin.append_right, Function.update_of_ne, Fin.append_right]
    intro h
    have := congrArg Fin.val h
    simp only [Fin.coe_natAdd, Fin.coe_castAdd] at this
    omega

private theorem update_append_right₂ {k : ℕ} (u : Fin k → Ltr) (v : Fin 2 → Ltr) (r : Fin 2) (ef : Ltr) :
    Function.update (Fin.append u v) (Fin.natAdd k r) ef = Fin.append u (Function.update v r ef) := by
  refine funext (Fin.addCases (fun q' => ?_) fun r' => ?_)
  · rw [Fin.append_left, Function.update_of_ne, Fin.append_left]
    intro h
    have := congrArg Fin.val h
    simp only [Fin.coe_natAdd, Fin.coe_castAdd] at this
    omega
  · rw [Fin.append_right, Function.update_apply, Function.update_apply, Fin.append_right]
    by_cases h : r' = r
    · subst h; simp
    · rw [if_neg h, if_neg (fun h' => h ((Fin.natAdd_inj k).1 h'))]

private theorem cons_append₃ {k : ℕ} (x : Ltr) (u : Fin k → Ltr) (v : Fin 3 → Ltr) :
    Fin.append (Fin.cons x u) v = Fin.cons x (Fin.append u v) := by
  rw [Fin.append_cons]
  rfl

private theorem nil_append₃ (u : Fin 0 → Ltr) (v : Fin 3 → Ltr) : Fin.append u v = v := by
  rw [Fin.append_left_nil u v rfl]
  rfl

private theorem update_append_left₃ {k : ℕ} (u : Fin k → Ltr) (v : Fin 3 → Ltr) (q : Fin k) (ef : Ltr) :
    Function.update (Fin.append u v) (Fin.castAdd 3 q) ef = Fin.append (Function.update u q ef) v := by
  refine funext (Fin.addCases (fun q' => ?_) fun r => ?_)
  · rw [Fin.append_left, Function.update_apply, Function.update_apply]
    by_cases h : q' = q
    · subst h; simp
    · rw [if_neg h, if_neg (fun h' => h (Fin.ext (by simpa [Fin.ext_iff] using h'))), Fin.append_left]
  · rw [Fin.append_right, Function.update_of_ne, Fin.append_right]
    intro h
    have := congrArg Fin.val h
    simp only [Fin.coe_natAdd, Fin.coe_castAdd] at this
    omega

private theorem update_append_right₃ {k : ℕ} (u : Fin k → Ltr) (v : Fin 3 → Ltr) (r : Fin 3) (ef : Ltr) :
    Function.update (Fin.append u v) (Fin.natAdd k r) ef = Fin.append u (Function.update v r ef) := by
  refine funext (Fin.addCases (fun q' => ?_) fun r' => ?_)
  · rw [Fin.append_left, Function.update_of_ne, Fin.append_left]
    intro h
    have := congrArg Fin.val h
    simp only [Fin.coe_natAdd, Fin.coe_castAdd] at this
    omega
  · rw [Fin.append_right, Function.update_apply, Function.update_apply, Fin.append_right]
    by_cases h : r' = r
    · subst h; simp
    · rw [if_neg h, if_neg (fun h' => h ((Fin.natAdd_inj k).1 h'))]

private theorem upd2_0 (x y z : Ltr) : Function.update ![x, y] 0 z = ![z, y] := by
  ext i <;> fin_cases i <;> simp
private theorem upd2_1 (x y z : Ltr) : Function.update ![x, y] 1 z = ![x, z] := by
  ext i <;> fin_cases i <;> simp
private theorem upd3_0 (x y w z : Ltr) : Function.update ![x, y, w] 0 z = ![z, y, w] := by
  ext i <;> fin_cases i <;> simp
private theorem upd3_1 (x y w z : Ltr) : Function.update ![x, y, w] 1 z = ![x, z, w] := by
  ext i <;> fin_cases i <;> simp
private theorem upd3_2 (x y w z : Ltr) : Function.update ![x, y, w] 2 z = ![x, y, z] := by
  ext i <;> fin_cases i <;> simp

private theorem cancel₂ (a b : Fin 3) (F : (Fin 2 → Ltr) → DOp (Fin n)) :
    ∑ i : Fin 3, ∑ j : Fin 3, ∑ r : Fin 2, ∑ ef : Ltr,
      brCoeff a b (![(i, j), (j, i)] r) ef • F (Function.update ![(i, j), (j, i)] r ef) = 0 := by
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, upd2_0, upd2_1, brCoeff,
    sub_smul, add_smul, ite_smul, one_smul, zero_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_and,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  abel

private theorem cancel₃ (a b : Fin 3) (F : (Fin 3 → Ltr) → DOp (Fin n)) :
    ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, ∑ r : Fin 3, ∑ ef : Ltr,
      brCoeff a b (![(i, j), (j, l), (l, i)] r) ef • F (Function.update ![(i, j), (j, l), (l, i)] r ef) = 0 := by
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, upd3_0, upd3_1, upd3_2, brCoeff, sub_smul, add_smul, ite_smul, one_smul, zero_smul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  abel

private theorem diagOp_finset_sum (cω : ℂ) (a : Fin 3) {κ : Type} (s : Finset κ) (g : κ → DOp (Fin n)) :
    diagOp cω a (∑ t ∈ s, g t) = ∑ t ∈ s, diagOp cω a (g t) := by
  unfold diagOp
  split_ifs <;> simp only [comp_finset_sum, Finset.smul_sum, Finset.sum_sub_distrib]

private theorem upperOp_finset_sum (ab : Ltr) {κ : Type} (s : Finset κ) (g : κ → DOp (Fin n)) :
    upperOp ab (∑ t ∈ s, g t) = ∑ t ∈ s, upperOp ab (g t) := by
  unfold upperOp
  split_ifs <;> simp only [cmul_finset_sum, Finset.sum_const_zero]

private theorem comp_diagOp_left (cω : ℂ) (a : Fin 3) (D D' : DOp (Fin n)) :
    comp (diagOp cω a D) D' = diagOp cω a (comp D D') := by
  unfold diagOp
  split_ifs <;> simp only [comp_assoc, sub_comp', smul_comp]

private theorem comp_upperOp_left (ab : Ltr) (D D' : DOp (Fin n)) :
    comp (upperOp ab D) D' = upperOp ab (comp D D') := by
  unfold upperOp
  split_ifs <;> simp only [cmul_comp, zero_comp']

private theorem push_in₂ {α : Type} [Fintype α] (g : α → Fin 3 → Fin 3 → DOp (Fin n)) :
    ∑ a, ∑ i, ∑ j, g a i j = ∑ i, ∑ j, ∑ a, g a i j := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

private theorem push_in₃ {α : Type} [Fintype α] (g : α → Fin 3 → Fin 3 → Fin 3 → DOp (Fin n)) :
    ∑ a, ∑ i, ∑ j, ∑ l, g a i j l = ∑ i, ∑ j, ∑ l, ∑ a, g a i j l := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => push_in₂ fun a j l => g a i j l

private theorem reorder₂ {α β : Type} [Fintype α] [Fintype β] (f : α → β → Fin 3 → Fin 3 → DOp (Fin n)) :
    ∑ a, ∑ b, ∑ i, ∑ j, f a b i j = ∑ i, ∑ j, ∑ a, ∑ b, f a b i j := by
  rw [show (∑ a, ∑ b, ∑ i, ∑ j, f a b i j) = ∑ a, ∑ i, ∑ j, ∑ b, f a b i j from
    Finset.sum_congr rfl fun a _ => push_in₂ fun b i j => f a b i j]
  exact push_in₂ fun a i j => ∑ b, f a b i j

private theorem reorder₃ {α β : Type} [Fintype α] [Fintype β] (f : α → β → Fin 3 → Fin 3 → Fin 3 → DOp (Fin n)) :
    ∑ a, ∑ b, ∑ i, ∑ j, ∑ l, f a b i j l = ∑ i, ∑ j, ∑ l, ∑ a, ∑ b, f a b i j l := by
  rw [show (∑ a, ∑ b, ∑ i, ∑ j, ∑ l, f a b i j l) = ∑ a, ∑ i, ∑ j, ∑ l, ∑ b, f a b i j l from
    Finset.sum_congr rfl fun a _ => push_in₃ fun b i j l => f a b i j l]
  exact push_in₃ fun a i j l => ∑ b, f a b i j l

private theorem wordOp_cons_append₂ (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ) {k : ℕ} (x : Ltr)
    (u : Fin k → Ltr) (v : Fin 2 → Ltr) :
    wordOp S cω (k + 1 + 2) (Fin.append (Fin.cons x u) v) =
      letterOp S cω x (Fin.append u v) (wordOp S cω (k + 2)) := by
  rw [cons_append₂]
  exact wordOp_cons S cω (k + 2) x (Fin.append u v)

private theorem wordOp_cons_append₃ (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ) {k : ℕ} (x : Ltr)
    (u : Fin k → Ltr) (v : Fin 3 → Ltr) :
    wordOp S cω (k + 1 + 3) (Fin.append (Fin.cons x u) v) =
      letterOp S cω x (Fin.append u v) (wordOp S cω (k + 3)) := by
  rw [cons_append₃]
  exact wordOp_cons S cω (k + 3) x (Fin.append u v)

private theorem comp_casOp₂ (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ) : ∀ (k : ℕ) (w : Fin k → Ltr),
    comp (wordOp S cω k w) (casOp₂ S cω) =
      ∑ i : Fin 3, ∑ j : Fin 3, wordOp S cω (k + 2) (Fin.append w ![(i, j), (j, i)])
  | 0, w => by
    rw [wordOp_zero_eq, one_comp]
    unfold casOp₂
    simp only [nil_append₂]
  | k + 1, w => by
    have ih := comp_casOp₂ S cω k
    rw [← Fin.cons_self_tail w]
    simp only [wordOp_cons, wordOp_cons_append₂]
    unfold letterOp
    split_ifs
    · rw [comp_diagOp_left, ih, diagOp_finset_sum]
      simp only [diagOp_finset_sum]
    · rw [comp_upperOp_left, ih, upperOp_finset_sum]
      simp only [upperOp_finset_sum]
    · rw [add_comp, add_comp, comp_upperOp_left, cmul_comp, finset_sum_comp]
      simp only [finset_sum_comp, smul_comp, ih, upperOp_finset_sum, cmul_finset_sum, Finset.smul_sum,
        Fin.sum_univ_add, Fin.append_left, Fin.append_right, update_append_left₂, update_append_right₂,
        Finset.sum_add_distrib]
      rw [cancel₂ (w 0).1 (w 0).2 fun v => wordOp S cω (k + 2) (Fin.append (Fin.tail w) v), add_zero,
        reorder₂ fun p ef i j => brCoeff (w 0).1 (w 0).2 (Fin.tail w p) ef •
          wordOp S cω (k + 2) (Fin.append (Function.update (Fin.tail w) p ef) ![(i, j), (j, i)])]

private theorem comp_casOp₃ (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ) : ∀ (k : ℕ) (w : Fin k → Ltr),
    comp (wordOp S cω k w) (casOp₃ S cω) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, wordOp S cω (k + 3) (Fin.append w ![(i, j), (j, l), (l, i)])
  | 0, w => by
    rw [wordOp_zero_eq, one_comp]
    unfold casOp₃
    simp only [nil_append₃]
  | k + 1, w => by
    have ih := comp_casOp₃ S cω k
    rw [← Fin.cons_self_tail w]
    simp only [wordOp_cons, wordOp_cons_append₃]
    unfold letterOp
    split_ifs
    · rw [comp_diagOp_left, ih, diagOp_finset_sum]
      simp only [diagOp_finset_sum]
    · rw [comp_upperOp_left, ih, upperOp_finset_sum]
      simp only [upperOp_finset_sum]
    · rw [add_comp, add_comp, comp_upperOp_left, cmul_comp, finset_sum_comp]
      simp only [finset_sum_comp, smul_comp, ih, upperOp_finset_sum, cmul_finset_sum, Finset.smul_sum,
        Fin.sum_univ_add, Fin.append_left, Fin.append_right, update_append_left₃, update_append_right₃,
        Finset.sum_add_distrib]
      rw [cancel₃ (w 0).1 (w 0).2 fun v => wordOp S cω (k + 3) (Fin.append (Fin.tail w) v), add_zero,
        reorder₃ fun p ef i j l => brCoeff (w 0).1 (w 0).2 (Fin.tail w p) ef •
          wordOp S cω (k + 3) (Fin.append (Function.update (Fin.tail w) p ef) ![(i, j), (j, l), (l, i)])]

private theorem comp_d₁_wordOp (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ) (k : ℕ) (w : Fin k → Ltr) :
    comp d₁ (wordOp S cω k w) = wordOp S cω (k + 1) (Fin.cons (0, 0) w) := by
  rw [wordOp_cons]
  simp [letterOp, diagOp]

private theorem comp_d₂_wordOp (S : Fin 3 → Fin 3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ) (k : ℕ) (w : Fin k → Ltr) :
    comp d₂ (wordOp S cω k w) =
      wordOp S cω (k + 1) (Fin.cons (1, 1) w) + wordOp S cω (k + 1) (Fin.cons (0, 0) w) := by
  rw [wordOp_cons, wordOp_cons]
  simp [letterOp, diagOp]

end WordFamily
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

private theorem isWordFamily_wordOp (σ : M3 → Matrix (Fin n) (Fin n) ℂ) (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ GLs)
    (hσ1 : σ 1 = 1) (hσm : ∀ k k' : M3, kᵀ * k = 1 → k'ᵀ * k' = 1 → σ (k * k') = σ k * σ k') (cω : ℂ) :
    IsWordFamily (casOp₂ (soData σ) cω) (casOp₃ (soData σ) cω) (wordOp (soData σ) cω) := by
  refine ⟨fun w => rfl, fun k w => hasOrder_wordOp (soData σ) cω k w,
    fun k w ab i i' => totalDegree_wordOp_le (soData σ) cω k w ab i i', fun k w => ?_, fun k w => ?_, fun k w => ?_,
    fun k w => ?_⟩
  · rw [comp_casOp₂]
    exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.subset_span (Set.mem_range_self _)
  · rw [comp_casOp₃]
    exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun l _ =>
      Submodule.subset_span (Set.mem_range_self _)
  · rw [comp_d₁_wordOp]
    exact Submodule.subset_span (Set.mem_range_self _)
  · rw [comp_d₂_wordOp]
    exact Submodule.add_mem _ (Submodule.subset_span (Set.mem_range_self _))
      (Submodule.subset_span (Set.mem_range_self _))

private def swapOpₗ {ι : Type} [Fintype ι] [DecidableEq ι] : DOp ι →ₗ[ℂ] DOp ι where
  toFun := swapOp
  map_add' := swapOp_add
  map_smul' := swapOp_smul

private theorem mem_span_swapOp {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set (DOp ι)} {x : DOp ι}
    (hx : x ∈ Submodule.span ℂ s) : swapOp x ∈ Submodule.span ℂ (swapOp '' s) :=
  Submodule.apply_mem_span_image_of_mem_span (swapOpₗ (ι := ι)) hx

private theorem mem_span_range_swapOp {ι κ : Type} [Fintype ι] [DecidableEq ι] {f : κ → DOp ι} {x : DOp ι}
    (hx : x ∈ Submodule.span ℂ (Set.range f)) : swapOp x ∈ Submodule.span ℂ (Set.range fun w => swapOp (f w)) := by
  have h := mem_span_swapOp hx
  rwa [← Set.range_comp] at h

private theorem IsWordFamily.swapOp {Ω₂ Ω₃ : DOp (Fin n)} {𝒟 : (k : ℕ) → (Fin k → Fin 3 × Fin 3) → DOp (Fin n)}
    (h : IsWordFamily Ω₂ Ω₃ 𝒟) : IsWordFamily (swapOp Ω₂) (-swapOp Ω₃) (fun k w => swapOp (𝒟 k w)) := by
  refine ⟨fun w => ?_, fun k w => (h.hasOrder k w).swapOp, fun k w ab i i' => ?_, fun k w => ?_, fun k w => ?_,
    fun k w => ?_, fun k w => ?_⟩
  · rw [h.zero w, swapOp_one]
  · obtain ⟨a, b⟩ := ab
    rw [swapOp_apply, Matrix.map_apply, totalDegree_swapC]
    exact h.totalDegree_le k w (b, a) i i'
  · rw [← swapOp_comp]
    exact mem_span_range_swapOp (h.comp_casimir₂ k w)
  · rw [comp_neg', ← swapOp_comp]
    exact Submodule.neg_mem _ (mem_span_range_swapOp (h.comp_casimir₃ k w))
  · rw [← swapOp_d₂, ← swapOp_comp]
    exact mem_span_range_swapOp (h.d₂_comp k w)
  · rw [← swapOp_d₁, ← swapOp_comp]
    exact mem_span_range_swapOp (h.d₁_comp k w)

end MasterSystem
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

section Main

section AssemblyDatum

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem rDm_congr_of_eqOn (ℓ : ℕ) (w : Fin ℓ → M3) {F G : M3 → V} (h : Set.EqOn F G GLs) :
    Set.EqOn (rDm ℓ w F) (rDm ℓ w G) GLs := by
  induction ℓ with
  | zero => intro x hx; exact h hx
  | succ ℓ ih => intro x hx; exact rD_congr_of_eqOn _ (ih (Fin.tail w)) hx

private theorem rDw_congr_of_eqOn (ℓ : ℕ) (v : Fin ℓ → Fin 3 × Fin 3) {F G : M3 → V} (h : Set.EqOn F G GLs) :
    Set.EqOn (rDw ℓ v F) (rDw ℓ v G) GLs :=
  rDm_congr_of_eqOn ℓ _ h

private theorem asm_contDiff_mul_right (g : M3) : ContDiff ℝ (⊤ : ℕ∞) fun x : M3 => x * g := by
  have h : (fun x : M3 => x * g) = fun x => LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ g) x := by
    funext x
    rw [LinearMap.coe_toContinuousLinearMap', LinearMap.mulRight_apply]
  rw [h]
  exact ContinuousLinearMap.contDiff _

private theorem asm_contDiffOn_comp_mul_right {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {g : M3} (hg : g ∈ GLs) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => F (y * g)) GLs :=
  hF.comp (asm_contDiff_mul_right g).contDiffOn fun _ hx => mul_mem_GLs hx hg

private theorem contDiffOn_c2_iterate {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) (j : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (c2^[j] F) GLs := by
  induction j with
  | zero => exact hF
  | succ j ih => rw [Function.iterate_succ_apply']; exact contDiffOn_c2 ih

private theorem contDiffOn_c3_iterate {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) (j : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (c3^[j] F) GLs := by
  induction j with
  | zero => exact hF
  | succ j ih => rw [Function.iterate_succ_apply']; exact contDiffOn_c3 ih

private theorem c2_iterate_clm_comp {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V'] (L : V →L[ℝ] V')
    {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) (j : ℕ) :
    Set.EqOn (c2^[j] (fun y => L (F y))) (fun y => L ((c2^[j] F) y)) GLs := by
  induction j with
  | zero => intro x hx; rfl
  | succ j ih =>
    intro x hx
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', c2_congr_of_eqOn ih hx]
    exact c2_clm_comp L (contDiffOn_c2_iterate hF j) hx

private theorem c3_iterate_clm_comp {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V'] (L : V →L[ℝ] V')
    {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) (j : ℕ) :
    Set.EqOn (c3^[j] (fun y => L (F y))) (fun y => L ((c3^[j] F) y)) GLs := by
  induction j with
  | zero => intro x hx; rfl
  | succ j ih =>
    intro x hx
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', c3_congr_of_eqOn ih hx]
    exact c3_clm_comp L (contDiffOn_c3_iterate hF j) hx

private theorem c2_iterate_comp_mul_right {g : M3} (hg : g ∈ GLs) {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs)
    (j : ℕ) :
    Set.EqOn (c2^[j] (fun y => F (y * g))) (fun y => (c2^[j] F) (y * g)) GLs := by
  induction j with
  | zero => intro x hx; rfl
  | succ j ih =>
    intro x hx
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', c2_congr_of_eqOn ih hx]
    exact c2_comp_mul_right hg (contDiffOn_c2_iterate hF j) hx

private theorem c3_iterate_comp_mul_right {g : M3} (hg : g ∈ GLs) {F : M3 → V} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs)
    (j : ℕ) :
    Set.EqOn (c3^[j] (fun y => F (y * g))) (fun y => (c3^[j] F) (y * g)) GLs := by
  induction j with
  | zero => intro x hx; rfl
  | succ j ih =>
    intro x hx
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', c3_congr_of_eqOn ih hx]
    exact c3_comp_mul_right hg (contDiffOn_c3_iterate hF j) hx

variable {n : ℕ}

private def vecW (kb : Fin (n + 1) → M3) (W₁ : M3 → ℂ) : M3 → (Fin (n + 1) → ℂ) := fun x l => W₁ (x * kb l)

private def projL (l : Fin (n + 1)) : (Fin (n + 1) → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj (R := ℝ) l

private theorem projL_apply (l : Fin (n + 1)) (v : Fin (n + 1) → ℂ) : projL l v = v l := rfl

private theorem contDiffOn_vecW {kb : Fin (n + 1) → M3} (hkb : ∀ l, (kb l)ᵀ * kb l = 1) {W₁ : M3 → ℂ}
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) W₁ GLs) : ContDiffOn ℝ (⊤ : ℕ∞) (vecW kb W₁) GLs :=
  contDiffOn_pi.2 fun l => asm_contDiffOn_comp_mul_right hW (mem_GLs_of_orth (hkb l))

private theorem vecW_uni {kb : Fin (n + 1) → M3} (hkb : ∀ l, (kb l)ᵀ * kb l = 1) {W₁ : M3 → ℂ}
    (hN : ∀ n' x : M3, IsUpperUni n' → x ∈ GLs → W₁ (n' * x) = uniChar n' * W₁ x) :
    ∀ n' x : M3, IsUpperUni n' → x ∈ GLs → vecW kb W₁ (n' * x) = uniChar n' • vecW kb W₁ x := by
  intro n' x hn hx
  funext l
  show W₁ (n' * x * kb l) = uniChar n' * W₁ (x * kb l)
  rw [mul_assoc]
  exact hN n' _ hn (mul_mem_GLs hx (mem_GLs_of_orth (hkb l)))

private theorem vecW_orth {kb : Fin (n + 1) → M3} {σ : M3 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {W₁ : M3 → ℂ}
    (hK : ∀ x k : M3, x ∈ GLs → kᵀ * k = 1 → ∀ l, W₁ (x * k * kb l) = ∑ l', σ k l' l * W₁ (x * kb l')) :
    ∀ x k : M3, x ∈ GLs → kᵀ * k = 1 → vecW kb W₁ (x * k) = vecW kb W₁ x ᵥ* σ k := by
  intro x k hx hk
  funext l
  show W₁ (x * k * kb l) = _
  rw [hK x k hx hk l]
  simp only [Matrix.vecMul, dotProduct, vecW, mul_comm]

private theorem asm_rD_pi {m : ℕ} (X : M3) {F : M3 → (Fin m → ℂ)} {x : M3} (hF : DifferentiableAt ℝ F x) (l : Fin m) :
    rD X F x l = rD X (fun y => F y l) x := by
  rw [rD_eq_fderiv X hF, rD_eq_fderiv X (differentiableAt_pi.1 hF l)]
  first
    | exact (DFunLike.congr_fun (hasFDerivAt_pi'.1 hF.hasFDerivAt l).fderiv (x * X)).symm
    | erw [(hasFDerivAt_pi'.1 hF.hasFDerivAt l).fderiv] <;> rfl
    | erw [fderiv_pi fun l' => differentiableAt_pi.1 hF l'] <;> rfl

private theorem vecW_centre {kb : Fin (n + 1) → M3} (hkb : ∀ l, (kb l)ᵀ * kb l = 1) {W₁ : M3 → ℂ}
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) W₁ GLs) {cω : ℂ} (hZ : ∀ x ∈ GLs, rD 1 W₁ x = cω * W₁ x) :
    ∀ x ∈ GLs, rD 1 (vecW kb W₁) x = cω • vecW kb W₁ x := by
  intro x hx
  have hd : DifferentiableAt ℝ (vecW kb W₁) x := differentiableAt_of_contDiffOn (contDiffOn_vecW hkb hW) hx
  funext l
  rw [asm_rD_pi 1 hd l, Pi.smul_apply, smul_eq_mul]
  have hg : kb l ∈ GLs := mem_GLs_of_orth (hkb l)
  have h1 := rD_apply_mul_right 1 hg W₁ x
  rw [mul_one, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 ?_)] at h1
  · show rD 1 (fun y => W₁ (y * kb l)) x = cω * W₁ (x * kb l)
    rw [← h1]
    exact hZ _ (mul_mem_GLs hx hg)
  · exact (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit hg)

private theorem vecW_rel₂ {kb : Fin (n + 1) → M3} (hkb : ∀ l, (kb l)ᵀ * kb l = 1) {W₁ : M3 → ℂ}
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) W₁ GLs) {N₂ : ℕ} {a₂ : Fin (N₂ + 1) → ℂ}
    (hC : ∀ x ∈ GLs, ∑ j, a₂ j * (c2^[j] W₁) x = 0) :
    ∀ x ∈ GLs, ∑ j, a₂ j • (c2^[(j : ℕ)] (vecW kb W₁)) x = 0 := by
  intro x hx
  funext l
  rw [Finset.sum_apply, Pi.zero_apply]
  have hg : kb l ∈ GLs := mem_GLs_of_orth (hkb l)
  have hl : ∀ j : ℕ, (c2^[j] (vecW kb W₁)) x l = (c2^[j] W₁) (x * kb l) := by
    intro j
    have h1 := c2_iterate_clm_comp (projL l) (contDiffOn_vecW hkb hW) j hx
    simp only [projL_apply] at h1
    rw [← h1]
    exact c2_iterate_comp_mul_right hg hW j hx
  simp only [Pi.smul_apply, smul_eq_mul, hl]
  exact hC _ (mul_mem_GLs hx hg)

private theorem vecW_rel₃ {kb : Fin (n + 1) → M3} (hkb : ∀ l, (kb l)ᵀ * kb l = 1) {W₁ : M3 → ℂ}
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) W₁ GLs) {N₃ : ℕ} {a₃ : Fin (N₃ + 1) → ℂ}
    (hC : ∀ x ∈ GLs, ∑ j, a₃ j * (c3^[j] W₁) x = 0) :
    ∀ x ∈ GLs, ∑ j, a₃ j • (c3^[(j : ℕ)] (vecW kb W₁)) x = 0 := by
  intro x hx
  funext l
  rw [Finset.sum_apply, Pi.zero_apply]
  have hg : kb l ∈ GLs := mem_GLs_of_orth (hkb l)
  have hl : ∀ j : ℕ, (c3^[j] (vecW kb W₁)) x l = (c3^[j] W₁) (x * kb l) := by
    intro j
    have h1 := c3_iterate_clm_comp (projL l) (contDiffOn_vecW hkb hW) j hx
    simp only [projL_apply] at h1
    rw [← h1]
    exact c3_iterate_comp_mul_right hg hW j hx
  simp only [Pi.smul_apply, smul_eq_mul, hl]
  exact hC _ (mul_mem_GLs hx hg)

end AssemblyDatum
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

section AssemblyTransport

variable {n : ℕ}

private structure Transf (σ : M3 → Matrix (Fin n) (Fin n) ℂ) (cω : ℂ) (W : M3 → (Fin n → ℂ)) : Prop where
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) W GLs
  uni : ∀ n' x : M3, IsUpperUni n' → x ∈ GLs → W (n' * x) = uniChar n' • W x
  orth : ∀ x k : M3, x ∈ GLs → kᵀ * k = 1 → W (x * k) = W x ᵥ* σ k
  centre : ∀ x ∈ GLs, rD 1 W x = cω • W x

variable {σ : M3 → Matrix (Fin n) (Fin n) ℂ} {cω : ℂ} {W : M3 → (Fin n → ℂ)}

private theorem Transf.casimir₂ (h : Transf σ cω W) : Transf σ cω (c2 W) :=
  ⟨contDiffOn_c2 h.smooth, (transforms_c2_c3 σ cω h.smooth h.uni h.orth h.centre).1.1,
    (transforms_c2_c3 σ cω h.smooth h.uni h.orth h.centre).1.2.1,
    (transforms_c2_c3 σ cω h.smooth h.uni h.orth h.centre).1.2.2⟩

private theorem Transf.casimir₃ (h : Transf σ cω W) : Transf σ cω (c3 W) :=
  ⟨contDiffOn_c3 h.smooth, (transforms_c2_c3 σ cω h.smooth h.uni h.orth h.centre).2.1,
    (transforms_c2_c3 σ cω h.smooth h.uni h.orth h.centre).2.2.1,
    (transforms_c2_c3 σ cω h.smooth h.uni h.orth h.centre).2.2.2⟩

private theorem Transf.iter₂ (h : Transf σ cω W) : ∀ j : ℕ, Transf σ cω (c2^[j] W)
  | 0 => h
  | j + 1 => by rw [Function.iterate_succ_apply']; exact (h.iter₂ j).casimir₂

private theorem Transf.iter₃ (h : Transf σ cω W) : ∀ j : ℕ, Transf σ cω (c3^[j] W)
  | 0 => h
  | j + 1 => by rw [Function.iterate_succ_apply']; exact (h.iter₃ j).casimir₃

private def onTorus (W : M3 → (Fin n → ℂ)) : ℝ → ℝ → (Fin n → ℂ) := fun s₁ s₂ => W (torus (Real.exp s₁) (Real.exp s₂))

private theorem contDiff_torus_exp : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ × ℝ => torus (Real.exp t.1) (Real.exp t.2) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ × ℝ => Real.exp t.1 := Real.contDiff_exp.comp contDiff_fst
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ × ℝ => Real.exp t.2 := Real.contDiff_exp.comp contDiff_snd
  simp only [torus, Matrix.diagonal_apply]
  split_ifs
  · subst_vars
    fin_cases j
    · exact h1.mul h2
    · exact h2
    · exact contDiff_const
  · exact contDiff_const

private theorem torus_exp_mem_GLs (s₁ s₂ : ℝ) : torus (Real.exp s₁) (Real.exp s₂) ∈ GLs :=
  torus_mem_GLs (Real.exp_pos s₁) (Real.exp_pos s₂)

private theorem smooth2_onTorus (hW : ContDiffOn ℝ (⊤ : ℕ∞) W GLs) : Smooth2 (onTorus W) :=
  hW.comp_contDiff contDiff_torus_exp fun t => torus_exp_mem_GLs t.1 t.2

private theorem Transf.c2_onTorus (h : Transf σ cω W) (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ GLs) (t₁ t₂ : ℝ) :
    c2 W (torus (Real.exp t₁) (Real.exp t₂)) = apply (casOp₂ (soData σ) cω) (onTorus W) t₁ t₂ :=
  c2_torus_eq_apply_casOp₂ (soData σ) cω h.smooth h.uni h.centre
    (fun _ hx a b hab => rD_skew_eq_soData_mulVec σ hσ h.smooth h.orth hx a b hab) t₁ t₂

private theorem Transf.c3_onTorus (h : Transf σ cω W) (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ GLs) (t₁ t₂ : ℝ) :
    c3 W (torus (Real.exp t₁) (Real.exp t₂)) = apply (casOp₃ (soData σ) cω) (onTorus W) t₁ t₂ :=
  c3_torus_eq_apply_casOp₃ (soData σ) cω h.smooth h.uni h.centre
    (fun _ hx a b hab => rD_skew_eq_soData_mulVec σ hσ h.smooth h.orth hx a b hab) t₁ t₂

private theorem Transf.rDw_onTorus (h : Transf σ cω W) (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ GLs) (ℓ : ℕ)
    (v : Fin ℓ → Fin 3 × Fin 3) (t₁ t₂ : ℝ) :
    rDw ℓ v W (torus (Real.exp t₁) (Real.exp t₂)) = apply (wordOp (soData σ) cω ℓ v) (onTorus W) t₁ t₂ :=
  rDw_torus_eq_apply_wordOp (soData σ) cω h.smooth h.uni h.centre
    (fun _ hx a b hab => rD_skew_eq_soData_mulVec σ hσ h.smooth h.orth hx a b hab) ℓ v t₁ t₂

private theorem Transf.apply_npow_casOp₂ (h : Transf σ cω W) (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ GLs) :
    ∀ j : ℕ, apply (npow (casOp₂ (soData σ) cω) j) (onTorus W) = onTorus (c2^[j] W)
  | 0 => by rw [npow, Function.iterate_zero_apply, apply_one]; rfl
  | j + 1 => by
    rw [npow, Function.iterate_succ_apply', ← npow, apply_comp _ _ (smooth2_onTorus h.smooth),
      h.apply_npow_casOp₂ hσ j, Function.iterate_succ_apply']
    funext t₁ t₂
    exact ((h.iter₂ j).c2_onTorus hσ t₁ t₂).symm

private theorem Transf.apply_npow_casOp₃ (h : Transf σ cω W) (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ GLs) :
    ∀ j : ℕ, apply (npow (casOp₃ (soData σ) cω) j) (onTorus W) = onTorus (c3^[j] W)
  | 0 => by rw [npow, Function.iterate_zero_apply, apply_one]; rfl
  | j + 1 => by
    rw [npow, Function.iterate_succ_apply', ← npow, apply_comp _ _ (smooth2_onTorus h.smooth),
      h.apply_npow_casOp₃ hσ j, Function.iterate_succ_apply']
    funext t₁ t₂
    exact ((h.iter₃ j).c3_onTorus hσ t₁ t₂).symm

private theorem Transf.apply_polyOp_casOp₂ (h : Transf σ cω W) (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ GLs) {N₂ : ℕ}
    (a₂ : Fin (N₂ + 1) → ℂ) (hrel : ∀ x ∈ GLs, ∑ j, a₂ j • (c2^[(j : ℕ)] W) x = 0) :
    apply (polyOp a₂ (casOp₂ (soData σ) cω)) (onTorus W) = fun _ _ => 0 := by
  rw [polyOp, ms_apply_sum]
  funext t₁ t₂
  simp only [apply_smul, h.apply_npow_casOp₂ hσ]
  simp only [onTorus]
  exact hrel _ (torus_exp_mem_GLs t₁ t₂)

private theorem Transf.apply_polyOp_casOp₃ (h : Transf σ cω W) (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ GLs) {N₃ : ℕ}
    (a₃ : Fin (N₃ + 1) → ℂ) (hrel : ∀ x ∈ GLs, ∑ j, a₃ j • (c3^[(j : ℕ)] W) x = 0) :
    apply (polyOp a₃ (casOp₃ (soData σ) cω)) (onTorus W) = fun _ _ => 0 := by
  rw [polyOp, ms_apply_sum]
  funext t₁ t₂
  simp only [apply_smul, h.apply_npow_casOp₃ hσ]
  simp only [onTorus]
  exact hrel _ (torus_exp_mem_GLs t₁ t₂)

end AssemblyTransport
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

section AssemblyTransfer

variable {L : ℕ}

private def padEquiv (ℓ : ℕ) (hℓ : ℓ ≤ L) : (Fin ℓ → Fin 3 × Fin 3) ≃ {v : PWord L // v.len = ℓ} where
  toFun w := ⟨PWord.pad ℓ hℓ w, rfl⟩
  invFun v := fun p => v.1.toFn (Fin.cast v.2.symm p)
  left_inv w := by
    funext p
    show (PWord.pad (L := L) ℓ hℓ w).toFn (Fin.cast rfl p) = w p
    rw [PWord.toFn_pad]
    rfl
  right_inv v := by
    obtain ⟨⟨⟨k, f⟩, hf⟩, hk⟩ := v
    change (k : ℕ) = ℓ at hk
    subst hk
    apply Subtype.ext
    apply Subtype.ext
    show ((⟨(k : ℕ), _⟩ : Fin (L + 1)), _) = (k, f)
    refine Prod.ext (Fin.ext rfl) (funext fun i => ?_)
    dsimp only
    split_ifs with h
    · simp only [PWord.toFn, Fin.castLE, Fin.cast]
    · exact (hf i (Nat.not_lt.1 h)).symm

private theorem sum_words_eq_sum_pwords {M : Type*} [AddCommMonoid M] (ℓ : ℕ) (hℓ : ℓ ≤ L)
    (f : (Fin ℓ → Fin 3 × Fin 3) → M) :
    ∑ w, f w = ∑ v : PWord L, if h : v.len = ℓ then f (fun p => v.toFn (Fin.cast h.symm p)) else 0 := by
  classical
  set F' : PWord L → M := fun v => if h : v.len = ℓ then f (fun p => v.toFn (Fin.cast h.symm p)) else 0 with hF'
  have h1 : ∑ w, f w = ∑ v : {v : PWord L // v.len = ℓ}, f (fun p => v.1.toFn (Fin.cast v.2.symm p)) :=
    Fintype.sum_equiv (padEquiv ℓ hℓ) _ _ fun w => by
      show f w = f ((padEquiv ℓ hℓ).symm (padEquiv ℓ hℓ w))
      rw [Equiv.symm_apply_apply]
  have h2 : ∑ v : {v : PWord L // v.len = ℓ}, f (fun p => v.1.toFn (Fin.cast v.2.symm p)) =
      ∑ v : {v : PWord L // v.len = ℓ}, F' v.1 :=
    Finset.sum_congr rfl fun v _ => by rw [hF']; dsimp only; rw [dif_pos v.2]
  have hmem : ∀ v : PWord L, v ∈ Finset.univ.filter (fun v : PWord L => v.len = ℓ) ↔ v.len = ℓ := fun v => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [h1, h2, ← Finset.sum_subtype _ hmem F', Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : v.len = ℓ
  · rw [if_pos h]
  · rw [if_neg h, hF']
    beta_reduce
    rw [dif_neg h]

private theorem rDw_cast {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {a b : ℕ} (h : a = b)
    (w : Fin a → Fin 3 × Fin 3) (F : M3 → V) : rDw b (fun p => w (Fin.cast h.symm p)) F = rDw a w F := by
  subst h
  rfl

private theorem adPow_cast {a b : ℕ} (h : a = b) (g : M3) (w w' : Fin a → Fin 3 × Fin 3) :
    adPow b g (fun p => w (Fin.cast h.symm p)) (fun p => w' (Fin.cast h.symm p)) = adPow a g w w' := by
  subst h
  rfl

private theorem app_cast {α : Sort*} (𝒟 : (k : ℕ) → (Fin k → Fin 3 × Fin 3) → α) {a b : ℕ} (h : a = b)
    (w : Fin a → Fin 3 × Fin 3) : 𝒟 b (fun p => w (Fin.cast h.symm p)) = 𝒟 a w := by
  subst h
  rfl

private theorem PWord.pad_toFn_cast (v : PWord L) {ℓ : ℕ} (h : v.len = ℓ) (hℓ : ℓ ≤ L) :
    PWord.pad ℓ hℓ (fun p => v.toFn (Fin.cast h.symm p)) = v :=
  congrArg Subtype.val ((padEquiv ℓ hℓ).apply_symm_apply ⟨v, h⟩)

private theorem PWord.len_le (v : PWord L) : v.len ≤ L := Nat.le_of_lt_succ v.1.1.2

variable {n : ℕ}

private def adBlkW (g : M3) (v v' : PWord L) : ℝ :=
  if h : v'.len = v.len then adPow v.len g v.toFn (fun p => v'.toFn (Fin.cast h.symm p)) else 0

private theorem adBlkW_pad (g : M3) (v : PWord L) (w : Fin v.len → Fin 3 × Fin 3) :
    adBlkW g v (PWord.pad v.len v.len_le w) = adPow v.len g v.toFn w := by
  unfold adBlkW
  split_ifs with h
  · congr 1
    funext p
    rw [PWord.toFn_pad]
    rfl
  · exact absurd rfl h

private theorem adBlkW_of_ne (g : M3) {v v' : PWord L} (h : v'.len ≠ v.len) : adBlkW g v v' = 0 := by
  rw [adBlkW, dif_neg h]

private theorem sum_pwords_eq_sum_words {M : Type*} [AddCommMonoid M] (v : PWord L) (S : PWord L → M)
    (hS : ∀ v' : PWord L, v'.len ≠ v.len → S v' = 0) :
    ∑ v', S v' = ∑ w : Fin v.len → Fin 3 × Fin 3, S (PWord.pad v.len v.len_le w) := by
  rw [sum_words_eq_sum_pwords v.len v.len_le]
  refine Finset.sum_congr rfl fun v' _ => ?_
  by_cases h : v'.len = v.len
  · rw [dif_pos h, PWord.pad_toFn_cast v' h]
  · rw [dif_neg h, hS v' h]

private theorem adBlkW_mul_sum (g g' : M3) (v v' : PWord L) :
    ∑ v'', adBlkW g v v'' * adBlkW g' v'' v' = adBlkW (g' * g) v v' := by
  rw [sum_pwords_eq_sum_words v _ fun v'' h => by rw [adBlkW_of_ne g h, zero_mul]]
  by_cases h : v'.len = v.len
  · have hterm : ∀ w : Fin v.len → Fin 3 × Fin 3, adBlkW g v (PWord.pad v.len v.len_le w) *
        adBlkW g' (PWord.pad v.len v.len_le w) v' =
        adPow v.len g v.toFn w * adPow v.len g' w (fun p => v'.toFn (Fin.cast h.symm p)) := by
      intro w
      rw [adBlkW_pad]
      congr 1
      unfold adBlkW
      split_ifs with h'
      · show adPow v.len g' (PWord.pad (L := L) v.len v.len_le w).toFn _ = _
        rw [PWord.toFn_pad]
        rfl
      · exact absurd h h'
    simp only [hterm]
    rw [adBlkW, dif_pos h, adPow_mul, Matrix.mul_apply]
  · rw [adBlkW_of_ne _ h]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [adBlkW_of_ne g' (fun h' => h ?_), mul_zero]
    rw [h']
    rfl

private theorem adBlkW_one (v v' : PWord L) : adBlkW 1 v v' = if v = v' then 1 else 0 := by
  by_cases h : v'.len = v.len
  · rw [adBlkW, dif_pos h, adPow_one, Matrix.one_apply]
    by_cases hv : v = v'
    · subst hv
      rw [if_pos rfl, if_pos]
      funext p
      rfl
    · rw [if_neg hv, if_neg]
      intro hw
      apply hv
      rw [← PWord.pad_toFn_cast v' h v.len_le, ← hw]
      exact (PWord.pad_toFn_cast v rfl v.len_le).symm
  · rw [adBlkW_of_ne _ h, if_neg]
    rintro rfl
    exact h rfl

private def adBlkC (g : M3) (v v' : PWord L) : ℂ := (adBlkW g v v' : ℂ)

private theorem adBlkC_mul_sum (g g' : M3) (v v' : PWord L) :
    ∑ v'', adBlkC g v v'' * adBlkC g' v'' v' = adBlkC (g' * g) v v' := by
  simp only [adBlkC, ← Complex.ofReal_mul, ← Complex.ofReal_sum, adBlkW_mul_sum]

private theorem adBlkC_one (v v' : PWord L) : adBlkC 1 v v' = if v = v' then 1 else 0 := by
  rw [adBlkC, adBlkW_one]
  split_ifs
  · exact Complex.ofReal_one
  · exact Complex.ofReal_zero

private theorem adBlkC_of_ne (g : M3) {v v' : PWord L} (h : v'.len ≠ v.len) : adBlkC g v v' = 0 := by
  rw [adBlkC, adBlkW_of_ne g h, Complex.ofReal_zero]

variable (L)

private abbrev MIdx (n : ℕ) : Type := PWord L × Fin (n + 1)

variable {L}

private def DA (kb : Fin (n + 1) → M3) (k : M3) : Matrix (MIdx L n) (MIdx L n) ℂ :=
  fun μ μ' => if μ'.2 = μ.2 then adBlkC (k * kb μ.2) μ.1 μ'.1 else 0

private def DAi (kb : Fin (n + 1) → M3) (k : M3) : Matrix (MIdx L n) (MIdx L n) ℂ :=
  fun μ μ' => if μ'.2 = μ.2 then adBlkC (k * kb μ.2)ᵀ μ.1 μ'.1 else 0

private def KB (σ : M3 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (k : M3) : Matrix (MIdx L n) (MIdx L n) ℂ :=
  fun μ μ' => if μ.1 = μ'.1 then σ k μ'.2 μ.2 else 0

private def KBi (σ : M3 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (k : M3) : Matrix (MIdx L n) (MIdx L n) ℂ :=
  fun μ μ' => if μ.1 = μ'.1 then σ kᵀ μ'.2 μ.2 else 0

private theorem DA_mul_apply (kb : Fin (n + 1) → M3) (k : M3) (X : Matrix (MIdx L n) (MIdx L n) ℂ) (μ μ' : MIdx L n) :
    (DA kb k * X : Matrix (MIdx L n) (MIdx L n) ℂ) μ μ' = ∑ v, adBlkC (k * kb μ.2) μ.1 v * X (v, μ.2) μ' := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [DA, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem DAi_mul_apply (kb : Fin (n + 1) → M3) (k : M3) (X : Matrix (MIdx L n) (MIdx L n) ℂ) (μ μ' : MIdx L n) :
    (DAi kb k * X : Matrix (MIdx L n) (MIdx L n) ℂ) μ μ' = ∑ v, adBlkC (k * kb μ.2)ᵀ μ.1 v * X (v, μ.2) μ' := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [DAi, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem KB_mul_apply (σ : M3 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (k : M3)
    (X : Matrix (MIdx L n) (MIdx L n) ℂ)
    (μ μ' : MIdx L n) : (KB σ k * X : Matrix (MIdx L n) (MIdx L n) ℂ) μ μ' = ∑ l, σ k l μ.2 * X (μ.1, l) μ' := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [KB, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem KBi_mul_apply (σ : M3 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (k : M3)
    (X : Matrix (MIdx L n) (MIdx L n) ℂ) (μ μ' : MIdx L n) :
    (KBi σ k * X : Matrix (MIdx L n) (MIdx L n) ℂ) μ μ' = ∑ l, σ kᵀ l μ.2 * X (μ.1, l) μ' := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [KBi, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem orth_comm {k : M3} (hk : kᵀ * k = 1) : k * kᵀ = 1 := mul_eq_one_comm.1 hk

private theorem orth_mul_kb {kb : Fin (n + 1) → M3} (hkb : ∀ l, (kb l)ᵀ * kb l = 1) {k : M3} (hk : kᵀ * k = 1)
    (l : Fin (n + 1)) : (k * kb l)ᵀ * (k * kb l) = 1 := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc kᵀ, hk, Matrix.one_mul, hkb]

private theorem DAi_mul_DA {kb : Fin (n + 1) → M3} (hkb : ∀ l, (kb l)ᵀ * kb l = 1) {k : M3} (hk : kᵀ * k = 1) :
    DAi kb k * DA kb k = (1 : Matrix (MIdx L n) (MIdx L n) ℂ) := by
  ext μ μ'
  rw [DAi_mul_apply]
  simp only [DA, mul_ite, mul_zero, ms_sum_ite_const, adBlkC_mul_sum, orth_comm (orth_mul_kb hkb hk μ.2),
    adBlkC_one, Matrix.one_apply, Prod.ext_iff]
  by_cases h1 : μ.1 = μ'.1
  · by_cases h2 : μ'.2 = μ.2
    · simp [h1, h2]
    · simp [h1, h2, Ne.symm h2]
  · by_cases h2 : μ'.2 = μ.2
    · simp [h1, h2]
    · simp [h1, h2, Ne.symm h2]

private theorem DA_mul_DAi {kb : Fin (n + 1) → M3} (hkb : ∀ l, (kb l)ᵀ * kb l = 1) {k : M3} (hk : kᵀ * k = 1) :
    DA kb k * DAi kb k = (1 : Matrix (MIdx L n) (MIdx L n) ℂ) := by
  ext μ μ'
  rw [DA_mul_apply]
  simp only [DAi, mul_ite, mul_zero, ms_sum_ite_const, adBlkC_mul_sum, orth_mul_kb hkb hk μ.2, adBlkC_one,
    Matrix.one_apply, Prod.ext_iff]
  by_cases h1 : μ.1 = μ'.1
  · by_cases h2 : μ'.2 = μ.2
    · simp [h1, h2]
    · simp [h1, h2, Ne.symm h2]
  · by_cases h2 : μ'.2 = μ.2
    · simp [h1, h2]
    · simp [h1, h2, Ne.symm h2]

private theorem KB_mul_KBi {σ : M3 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hσ1 : σ 1 = 1)
    (hσm : ∀ k k' : M3, kᵀ * k = 1 → k'ᵀ * k' = 1 → σ (k * k') = σ k * σ k') {k : M3} (hk : kᵀ * k = 1) :
    KB σ k * KBi σ k = (1 : Matrix (MIdx L n) (MIdx L n) ℂ) := by
  have hkt : (kᵀ)ᵀ * kᵀ = 1 := by rw [Matrix.transpose_transpose]; exact orth_comm hk
  have hσ : σ kᵀ * σ k = 1 := by rw [← hσm _ _ hkt hk, hk, hσ1]
  ext μ μ'
  rw [KB_mul_apply]
  simp only [KBi, mul_ite, mul_zero, ms_sum_ite_const]
  have hsum : ∑ l, σ k l μ.2 * σ kᵀ μ'.2 l = (σ kᵀ * σ k) μ'.2 μ.2 := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  rw [hsum, hσ, Matrix.one_apply, Matrix.one_apply]
  simp only [Prod.ext_iff]
  by_cases h1 : μ.1 = μ'.1
  · by_cases h2 : μ'.2 = μ.2
    · simp [h1, h2]
    · simp [h1, h2, Ne.symm h2]
  · by_cases h2 : μ'.2 = μ.2
    · simp [h1, h2]
    · simp [h1, Ne.symm h2]

private theorem KBi_mul_KB {σ : M3 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hσ1 : σ 1 = 1)
    (hσm : ∀ k k' : M3, kᵀ * k = 1 → k'ᵀ * k' = 1 → σ (k * k') = σ k * σ k') {k : M3} (hk : kᵀ * k = 1) :
    KBi σ k * KB σ k = (1 : Matrix (MIdx L n) (MIdx L n) ℂ) := by
  have hkt : (kᵀ)ᵀ * kᵀ = 1 := by rw [Matrix.transpose_transpose]; exact orth_comm hk
  have hσ : σ k * σ kᵀ = 1 := by rw [← hσm _ _ hk hkt, orth_comm hk, hσ1]
  ext μ μ'
  rw [KBi_mul_apply]
  simp only [KB, mul_ite, mul_zero, ms_sum_ite_const]
  have hsum : ∑ l, σ kᵀ l μ.2 * σ k μ'.2 l = (σ k * σ kᵀ) μ'.2 μ.2 := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  rw [hsum, hσ, Matrix.one_apply, Matrix.one_apply]
  simp only [Prod.ext_iff]
  by_cases h1 : μ.1 = μ'.1
  · by_cases h2 : μ'.2 = μ.2
    · simp [h1, h2]
    · simp [h1, h2, Ne.symm h2]
  · by_cases h2 : μ'.2 = μ.2
    · simp [h1, h2]
    · simp [h1, Ne.symm h2]

private def transfer (kb : Fin (n + 1) → M3) (σ : M3 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (k : M3) :
    Matrix (MIdx L n) (MIdx L n) ℂ :=
  DA kb k * KB σ k

private def transferInv (kb : Fin (n + 1) → M3) (σ : M3 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (k : M3) :
    Matrix (MIdx L n) (MIdx L n) ℂ :=
  KBi σ k * DAi kb k

private theorem transferInv_mul_transfer {kb : Fin (n + 1) → M3} (hkb : ∀ l, (kb l)ᵀ * kb l = 1)
    {σ : M3 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hσ1 : σ 1 = 1)
    (hσm : ∀ k k' : M3, kᵀ * k = 1 → k'ᵀ * k' = 1 → σ (k * k') = σ k * σ k') {k : M3} (hk : kᵀ * k = 1) :
    transferInv kb σ k * transfer kb σ k = (1 : Matrix (MIdx L n) (MIdx L n) ℂ) := by
  rw [transferInv, transfer, Matrix.mul_assoc, ← Matrix.mul_assoc (DAi kb k), DAi_mul_DA hkb hk, Matrix.one_mul,
    KBi_mul_KB hσ1 hσm hk]

private theorem transfer_mul_transferInv {kb : Fin (n + 1) → M3} (hkb : ∀ l, (kb l)ᵀ * kb l = 1)
    {σ : M3 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hσ1 : σ 1 = 1)
    (hσm : ∀ k k' : M3, kᵀ * k = 1 → k'ᵀ * k' = 1 → σ (k * k') = σ k * σ k') {k : M3} (hk : kᵀ * k = 1) :
    transfer kb σ k * transferInv kb σ k = (1 : Matrix (MIdx L n) (MIdx L n) ℂ) := by
  rw [transferInv, transfer, Matrix.mul_assoc, ← Matrix.mul_assoc (KB σ k), KB_mul_KBi hσ1 hσm hk, Matrix.one_mul,
    DA_mul_DAi hkb hk]

private theorem transfer_apply (kb : Fin (n + 1) → M3) (σ : M3 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (k : M3)
    (μ μ' : MIdx L n) : transfer kb σ k μ μ' = adBlkC (k * kb μ.2) μ.1 μ'.1 * σ k μ'.2 μ.2 := by
  rw [transfer, DA_mul_apply]
  simp only [KB, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end AssemblyTransfer
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

section AssemblyKeyVec

variable {L n : ℕ}

private theorem rDw_apply_mul_right_eq_sum_mul (ℓ : ℕ) (v : Fin ℓ → Fin 3 × Fin 3) {F : M3 → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F GLs) {g x : M3} (hg : g ∈ GLs) (hx : x ∈ GLs) :
    rDw ℓ v F (x * g) = ∑ e, (adPow ℓ g v e : ℂ) * rDw ℓ e (fun y => F (y * g)) x :=
  rDw_apply_mul_right_eq_sum ℓ v hF hg hx

private def keyVec (kb : Fin (n + 1) → M3) (W₁ : M3 → ℂ) (k : M3) (y z : ℝ) : MIdx L n → ℂ :=
  fun μ => rDw μ.1.len μ.1.toFn W₁ (torus y z * k * kb μ.2)

private theorem master_pad (𝒟 : (k : ℕ) → (Fin k → Fin 3 × Fin 3) → DOp (Fin (n + 1))) (Φ₀ : ℝ → ℝ → (Fin (n + 1) → ℂ))
    (t₁ t₂ : ℝ) {ℓ : ℕ} (hℓ : ℓ ≤ L) (e : Fin ℓ → Fin 3 × Fin 3) (l : Fin (n + 1)) :
    master L 𝒟 Φ₀ t₁ t₂ (PWord.pad ℓ hℓ e, l) = apply (𝒟 ℓ e) Φ₀ t₁ t₂ l := by
  show apply (𝒟 (PWord.pad (L := L) ℓ hℓ e).len (PWord.pad (L := L) ℓ hℓ e).toFn) Φ₀ t₁ t₂ l = _
  rw [PWord.app_pad 𝒟]

private theorem keyVec_eq_transfer_mulVec {kb : Fin (n + 1) → M3} (hkb : ∀ l, (kb l)ᵀ * kb l = 1)
    {σ : M3 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ GLs) {cω : ℂ} {W₁ : M3 → ℂ}
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) W₁ GLs) (hT : Transf σ cω (vecW kb W₁)) {k : M3} (hk : kᵀ * k = 1) {y z : ℝ}
    (hy : 0 < y) (hz : 0 < z) :
    keyVec kb W₁ k y z = transfer kb σ k *ᵥ
      master L (wordOp (soData σ) cω) (onTorus (vecW kb W₁)) (Real.log y) (Real.log z) := by
  have hkG : k ∈ GLs := mem_GLs_of_orth hk
  have hT0 : torus y z ∈ GLs := torus_mem_GLs hy hz
  have hlog : torus y z = torus (Real.exp (Real.log y)) (Real.exp (Real.log z)) := by
    rw [Real.exp_log hy, Real.exp_log hz]
  funext μ
  obtain ⟨v, l⟩ := μ
  have hg : k * kb l ∈ GLs := mul_mem_GLs hkG (mem_GLs_of_orth (hkb l))

  simp only [Matrix.mulVec, dotProduct, transfer_apply]
  rw [Fintype.sum_prod_type, sum_pwords_eq_sum_words v
    (fun v' => ∑ l', adBlkC (k * kb l) v v' * σ k l' l *
      master L (wordOp (soData σ) cω) (onTorus (vecW kb W₁)) (Real.log y) (Real.log z) (v', l'))
    (fun v' h => by simp only [adBlkC_of_ne _ h, zero_mul, Finset.sum_const_zero])]

  show rDw v.len v.toFn W₁ (torus y z * k * kb l) = _
  rw [mul_assoc, rDw_apply_mul_right_eq_sum_mul v.len v.toFn hW hg hT0]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hEq : Set.EqOn (fun y' => W₁ (y' * (k * kb l)))
      (fun y' => ((projL l).comp (vecMulCLM (σ k))) (vecW kb W₁ y')) GLs := by
    intro y' hy'
    show W₁ (y' * (k * kb l)) = ((projL l).comp (vecMulCLM (σ k))) (vecW kb W₁ y')
    rw [ContinuousLinearMap.comp_apply, vecMulCLM_apply, projL_apply, ← hT.orth y' k hy' hk, ← mul_assoc]
    rfl
  rw [rDw_congr_of_eqOn v.len e hEq hT0]
  have hclm : rDw v.len e (fun y' => ((projL l).comp (vecMulCLM (σ k))) (vecW kb W₁ y')) (torus y z) =
      ((projL l).comp (vecMulCLM (σ k))) (rDw v.len e (vecW kb W₁) (torus y z)) :=
    rDm_clm_comp _ v.len _ hT.smooth hT0
  rw [hclm, ContinuousLinearMap.comp_apply, vecMulCLM_apply, projL_apply, hlog, hT.rDw_onTorus hσ v.len e]
  simp only [Matrix.vecMul, dotProduct, Finset.mul_sum, adBlkC, adBlkW_pad, master_pad]
  exact Finset.sum_congr rfl fun l' _ => by ring

end AssemblyKeyVec
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

section AssemblyContinuity

variable {L n : ℕ}

private theorem transpose_mem_GLs {g : M3} (hg : g ∈ GLs) : gᵀ ∈ GLs := by
  show gᵀ.det ≠ 0
  rw [Matrix.det_transpose]
  exact hg

private theorem continuousOn_adBlkC (v v' : PWord L) : ContinuousOn (fun g => adBlkC g v v') GLs := by
  unfold adBlkC adBlkW
  by_cases h : v'.len = v.len
  · simp only [dif_pos h]
    exact Complex.continuous_ofReal.comp_continuousOn (continuousOn_adPow_entry _ _ _)
  · simp only [dif_neg h, Complex.ofReal_zero]
    exact continuousOn_const

private theorem continuousOn_entry {m : Type*} {σ : M3 → Matrix m m ℂ} {s : Set M3} (hσ : ContinuousOn σ s) (i j : m) :
    ContinuousOn (fun k => σ k i j) s :=
  continuousOn_pi.1 (continuousOn_pi.1 hσ i) j

private theorem continuousOn_DA {kb : Fin (n + 1) → M3} (hkb : ∀ l, (kb l)ᵀ * kb l = 1) :
    ContinuousOn (fun k => (DA kb k : Matrix (MIdx L n) (MIdx L n) ℂ)) GLs := by
  refine continuousOn_pi.2 fun μ => continuousOn_pi.2 fun μ' => ?_
  simp only [DA]
  split_ifs
  · exact (continuousOn_adBlkC μ.1 μ'.1).comp (continuous_id.mul continuous_const).continuousOn
      fun k hk => mul_mem_GLs hk (mem_GLs_of_orth (hkb μ.2))
  · exact continuousOn_const

private theorem continuousOn_DAi {kb : Fin (n + 1) → M3} (hkb : ∀ l, (kb l)ᵀ * kb l = 1) :
    ContinuousOn (fun k => (DAi kb k : Matrix (MIdx L n) (MIdx L n) ℂ)) GLs := by
  refine continuousOn_pi.2 fun μ => continuousOn_pi.2 fun μ' => ?_
  simp only [DAi]
  split_ifs
  · exact (continuousOn_adBlkC μ.1 μ'.1).comp (continuous_id.mul continuous_const).matrix_transpose.continuousOn
      fun k hk => transpose_mem_GLs (mul_mem_GLs hk (mem_GLs_of_orth (hkb μ.2)))
  · exact continuousOn_const

private theorem continuousOn_KB {σ : M3 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ GLs) :
    ContinuousOn (fun k => (KB σ k : Matrix (MIdx L n) (MIdx L n) ℂ)) GLs := by
  refine continuousOn_pi.2 fun μ => continuousOn_pi.2 fun μ' => ?_
  simp only [KB]
  split_ifs
  · exact continuousOn_entry hσ.continuousOn _ _
  · exact continuousOn_const

private theorem continuousOn_KBi {σ : M3 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ GLs) :
    ContinuousOn (fun k => (KBi σ k : Matrix (MIdx L n) (MIdx L n) ℂ)) GLs := by
  refine continuousOn_pi.2 fun μ => continuousOn_pi.2 fun μ' => ?_
  simp only [KBi]
  split_ifs
  · exact continuousOn_entry (hσ.continuousOn.comp continuous_id.matrix_transpose.continuousOn
      fun k hk => transpose_mem_GLs hk) _ _
  · exact continuousOn_const

private theorem continuousOn_transfer {kb : Fin (n + 1) → M3} (hkb : ∀ l, (kb l)ᵀ * kb l = 1)
    {σ : M3 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ GLs) :
    ContinuousOn (fun k => (transfer kb σ k : Matrix (MIdx L n) (MIdx L n) ℂ)) GLs :=
  (continuousOn_DA hkb).mul (continuousOn_KB hσ)

private theorem continuousOn_transferInv {kb : Fin (n + 1) → M3} (hkb : ∀ l, (kb l)ᵀ * kb l = 1)
    {σ : M3 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ GLs) :
    ContinuousOn (fun k => (transferInv kb σ k : Matrix (MIdx L n) (MIdx L n) ℂ)) GLs :=
  (continuousOn_KBi hσ).mul (continuousOn_DAi hkb)

end AssemblyContinuity
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

section AssemblyCoeff

private def expo (ab : ℕ × ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 ab.1 + Finsupp.single 1 ab.2

private theorem expo_apply_zero (ab : ℕ × ℕ) : expo ab 0 = ab.1 := by
  simp [expo]

private theorem expo_apply_one (ab : ℕ × ℕ) : expo ab 1 = ab.2 := by
  simp [expo]

private theorem expo_of (d : Fin 2 →₀ ℕ) : expo (d 0, d 1) = d := by
  ext i
  fin_cases i
  · exact expo_apply_zero _
  · exact expo_apply_one _

private theorem expo_injective : Function.Injective expo := fun ab ab' h => by
  have h0 := congrArg (fun d => d 0) h
  have h1 := congrArg (fun d => d 1) h
  simp only [expo_apply_zero, expo_apply_one] at h0 h1
  exact Prod.ext h0 h1

private def box (δ : ℕ) : Finset (ℕ × ℕ) := Finset.range (δ + 1) ×ˢ Finset.range (δ + 1)

private theorem eval_eq_sum_coeff_expo (x : Fin 2 → ℂ) {p : Coef} {δ : ℕ} (hp : p.totalDegree ≤ δ) :
    MvPolynomial.eval x p = ∑ ab ∈ box δ, MvPolynomial.coeff (expo ab) p * (x 0 ^ ab.1 * x 1 ^ ab.2) := by
  classical
  rw [MvPolynomial.eval_eq']
  have hsub : p.support ⊆ (box δ).image expo := fun d hd => by
    rw [Finset.mem_image]
    refine ⟨(d 0, d 1), ?_, expo_of d⟩
    have hle : d 0 + d 1 ≤ δ := by
      have h := MvPolynomial.le_totalDegree hd
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at h
      exact h.trans hp
    simp only [box, Finset.mem_product, Finset.mem_range]
    omega
  rw [Finset.sum_subset hsub fun d _ hd => by
      rw [show MvPolynomial.coeff d p = 0 by simpa only [MvPolynomial.mem_support_iff, ne_eq, not_not] using hd,
        zero_mul],
    Finset.sum_image fun ab _ ab' _ h => expo_injective h]
  exact Finset.sum_congr rfl fun ab _ => by simp only [Fin.prod_univ_two, expo_apply_zero, expo_apply_one]

variable {ι' : Type} [Fintype ι'] [DecidableEq ι']

private def coefM (R : Matrix ι' ι' Coef) (ab : ℕ × ℕ) : Matrix ι' ι' ℂ := fun μ μ' => MvPolynomial.coeff (expo ab)
    (R μ μ')

private theorem mev_eq_sum_coefM {R : Matrix ι' ι' Coef} {δ : ℕ} (hR : ∀ μ μ', (R μ μ').totalDegree ≤ δ) (t₁ t₂ : ℝ) :
    mev R t₁ t₂ = ∑ ab ∈ box δ, (Complex.exp t₁ ^ ab.1 * Complex.exp t₂ ^ ab.2) • coefM R ab := by
  ext μ μ'
  rw [ms_mev_apply, Matrix.sum_apply]
  unfold Coef.ev
  rw [eval_eq_sum_coeff_expo _ (hR μ μ')]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, mul_comm]
  simp only [coefM, Matrix.cons_val_zero, Matrix.cons_val_one]

private def matL (M : Matrix ι' ι' ℂ) : (ι' → ℂ) →L[ℂ] (ι' → ℂ) :=
  LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := ι' → ℂ) (Matrix.toLin' M)

private theorem matL_apply (M : Matrix ι' ι' ℂ) (w : ι' → ℂ) : matL M w = M *ᵥ w := by
  rw [matL, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply]

private theorem continuous_matL : Continuous (matL : Matrix ι' ι' ℂ → (ι' → ℂ) →L[ℂ] (ι' → ℂ)) := by
  let Φ : Matrix ι' ι' ℂ →ₗ[ℂ] (ι' → ℂ) →L[ℂ] (ι' → ℂ) :=
    (LinearMap.toContinuousLinearMap : ((ι' → ℂ) →ₗ[ℂ] (ι' → ℂ)) ≃ₗ[ℂ] _).toLinearMap ∘ₗ
      (Matrix.toLin' : Matrix ι' ι' ℂ ≃ₗ[ℂ] _).toLinearMap
  have h : (matL : Matrix ι' ι' ℂ → _) = Φ := rfl
  rw [h]
  exact Φ.continuous_of_finiteDimensional

end AssemblyCoeff
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

section AssemblyReindex

variable {ι' : Type}

private def reix {r : ℕ} (e : Fin (r + 1) ≃ ι') (M : Matrix ι' ι' ℂ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Matrix.reindex e.symm e.symm M

private theorem reix_apply {r : ℕ} (e : Fin (r + 1) ≃ ι') (M : Matrix ι' ι' ℂ) (i j : Fin (r + 1)) :
    reix e M i j = M (e i) (e j) := rfl

private theorem reix_mulVec [Fintype ι'] {r : ℕ} (e : Fin (r + 1) ≃ ι') (M : Matrix ι' ι' ℂ) (w : ι' → ℂ)
    (i : Fin (r + 1)) :
    (reix e M *ᵥ fun j => w (e j)) i = (M *ᵥ w) (e i) := by
  simp only [Matrix.mulVec, dotProduct, reix_apply]
  exact Fintype.sum_equiv e _ _ fun j => rfl

private theorem continuous_reix {r : ℕ} (e : Fin (r + 1) ≃ ι') : Continuous (reix e : Matrix ι' ι' ℂ → _) :=
  continuous_pi fun i => continuous_pi fun j => (continuous_apply (e j)).comp (continuous_apply (e i))

end AssemblyReindex
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

section AssemblyGlue

private theorem asm_cmap_apply {ι : Type} [Fintype ι] [DecidableEq ι] (f : Coef → Coef)
    (hf : (0 : Matrix ι ι Coef).map f = 0) (D : DOp ι) (ab : ℕ × ℕ) : cmap f D ab = (D ab).map f := by
  classical
  unfold cmap
  rw [Finsupp.sum_apply, Finsupp.sum]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  by_cases h : ab ∈ D.support
  · rw [if_pos h]
  · rw [if_neg h, Finsupp.notMem_support_iff.1 h, hf]

private theorem diagEntry_cmap_const_eq {D : DOp (Fin 1)} {ω : ℕ × ℕ → ℂ}
    (h : ∀ ab, (D ab).map MvPolynomial.constantCoeff = ω ab • (1 : Matrix (Fin 1) (Fin 1) ℂ)) (ab : ℕ × ℕ) :
    diagEntry (0 : Fin 1) (cmap (fun p => MvPolynomial.C (MvPolynomial.constantCoeff p)) D) ab =
      fun _ _ => MvPolynomial.C (ω ab) := by
  unfold diagEntry
  rw [Finsupp.mapRange_apply, asm_cmap_apply _ (by ext i j; simp) D ab]
  funext u u'
  have h0 := congrFun (congrFun (h ab) 0) 0
  rw [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h0
  rw [Matrix.map_apply, h0]

variable {m : ℕ}

private theorem swapOp_apply' {ι : Type} [Fintype ι] [DecidableEq ι] (D : DOp ι) (ab : ℕ × ℕ) :
    swapOp D ab = (D ab.swap).map swapC := by
  obtain ⟨a, b⟩ := ab
  exact swapOp_apply D a b

private theorem map_constantCoeff_swapOp {Ω : DOp (Fin m)} {ω : ℕ × ℕ → ℂ}
    (h : ∀ ab, (Ω ab).map MvPolynomial.constantCoeff = ω ab • (1 : Matrix (Fin m) (Fin m) ℂ)) (ab : ℕ × ℕ) :
    (swapOp Ω ab).map MvPolynomial.constantCoeff = ω ab.swap • (1 : Matrix (Fin m) (Fin m) ℂ) := by
  rw [swapOp_apply', Matrix.map_map]
  have hc : (⇑(MvPolynomial.constantCoeff : Coef →+* ℂ) ∘ ⇑swapC) = MvPolynomial.constantCoeff :=
    funext constantCoeff_swapC
  rw [hc, h]

private theorem map_constantCoeff_neg_swapOp {Ω : DOp (Fin m)} {ω : ℕ × ℕ → ℂ}
    (h : ∀ ab, (Ω ab).map MvPolynomial.constantCoeff = ω ab • (1 : Matrix (Fin m) (Fin m) ℂ)) (ab : ℕ × ℕ) :
    ((-swapOp Ω) ab).map MvPolynomial.constantCoeff = (-ω ab.swap) • (1 : Matrix (Fin m) (Fin m) ℂ) := by
  ext i j
  rw [Finsupp.neg_apply, Matrix.map_apply, Matrix.neg_apply, map_neg,
    ← Matrix.map_apply (f := MvPolynomial.constantCoeff), map_constantCoeff_swapOp h ab, Matrix.smul_apply,
    Matrix.smul_apply, smul_eq_mul, smul_eq_mul, neg_mul]

private theorem totalDegree_swapOp_le {Ω : DOp (Fin m)} {c : ℕ}
    (h : ∀ (ab : ℕ × ℕ) (i i' : Fin m), (Ω ab i i').totalDegree ≤ c) (ab : ℕ × ℕ) (i i' : Fin m) :
    (swapOp Ω ab i i').totalDegree ≤ c := by
  rw [swapOp_apply', Matrix.map_apply, totalDegree_swapC]
  exact h _ _ _

private theorem totalDegree_neg_swapOp_le {Ω : DOp (Fin m)} {c : ℕ}
    (h : ∀ (ab : ℕ × ℕ) (i i' : Fin m), (Ω ab i i').totalDegree ≤ c) (ab : ℕ × ℕ) (i i' : Fin m) :
    ((-swapOp Ω) ab i i').totalDegree ≤ c := by
  rw [Finsupp.neg_apply, Matrix.neg_apply, MvPolynomial.totalDegree_neg]
  exact totalDegree_swapOp_le h _ _ _

private theorem conjOp_neg (U : Matrix (Fin m) (Fin m) ℂ) (D : DOp (Fin m)) : conjOp U (-D) = -conjOp U D := by
  apply Finsupp.ext
  intro ab
  unfold conjOp
  rw [Finsupp.neg_apply, Finsupp.mapRange_apply, Finsupp.mapRange_apply, Finsupp.neg_apply, Matrix.mul_neg,
    Matrix.neg_mul]

private theorem killX0_conjOp_swapOp {Ω : DOp (Fin m)} {U : Matrix (Fin m) (Fin m) ℂ} {zw : Fin m → ℂ}
    {ψ : ℕ × ℕ → ℂ → Coef}
    (h : ∀ (ab : ℕ × ℕ) (i i' : Fin m), killX1 (conjOp U Ω ab i i') = if i = i' then ψ ab (zw i) else 0)
    (ab : ℕ × ℕ) (i i' : Fin m) :
    killX0 (conjOp U (swapOp Ω) ab i i') = if i = i' then swapC (ψ ab.swap (zw i)) else 0 := by
  rw [← swapOp_conjOp, swapOp_apply', Matrix.map_apply, killX0_swapC, h]
  split_ifs
  · rfl
  · exact map_zero _

private theorem killX0_conjOp_neg_swapOp {Ω : DOp (Fin m)} {U : Matrix (Fin m) (Fin m) ℂ} {zw : Fin m → ℂ}
    {ψ : ℕ × ℕ → ℂ → Coef}
    (h : ∀ (ab : ℕ × ℕ) (i i' : Fin m), killX1 (conjOp U Ω ab i i') = if i = i' then ψ ab (zw i) else 0)
    (ab : ℕ × ℕ) (i i' : Fin m) :
    killX0 (conjOp U (-swapOp Ω) ab i i') = if i = i' then -swapC (ψ ab.swap (zw i)) else 0 := by
  rw [conjOp_neg, Finsupp.neg_apply, Matrix.neg_apply, map_neg, killX0_conjOp_swapOp h]
  split_ifs
  · rfl
  · exact neg_zero

private theorem npow_neg {ι : Type} [Fintype ι] [DecidableEq ι] (D : DOp ι) (j : ℕ) :
    npow (-D) j = (-1 : ℂ) ^ j • npow D j := by
  induction j with
  | zero =>
    show ((comp (-D))^[0] one : DOp ι) = (-1 : ℂ) ^ 0 • ((comp D)^[0] one)
    rw [Function.iterate_zero_apply, Function.iterate_zero_apply, pow_zero, one_smul]
  | succ j ih =>
    show ((comp (-D))^[j + 1] one : DOp ι) = (-1 : ℂ) ^ (j + 1) • ((comp D)^[j + 1] one)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change comp (-D) (npow (-D) j) = (-1 : ℂ) ^ (j + 1) • comp D (npow D j)
    rw [ih, comp_smul, ← neg_one_smul ℂ D, smul_comp, smul_smul, ← pow_succ]

private theorem polyOp_signed_neg {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (a : Fin (N + 1) → ℂ) (D : DOp ι) :
    polyOp (fun j => (-1 : ℂ) ^ (N - (j : ℕ)) * a j) (-D) = (-1 : ℂ) ^ N • polyOp a D := by
  unfold polyOp
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [npow_neg, smul_smul, smul_smul]
  congr 1
  rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel (Fin.is_le j)]

private theorem sum_box_eq {M : Type*} [AddCommMonoid M] (δ : ℕ) (f : ℕ × ℕ → M) :
    ∑ ab ∈ box δ, f ab = ∑ b : Fin (δ + 1), f (0, b) + ∑ k : Fin δ, ∑ b : Fin (δ + 1), f ((k : ℕ) + 1, b) := by
  rw [box, Finset.sum_product, Finset.sum_range, Fin.sum_univ_succ]
  simp only [Finset.sum_range, Fin.val_zero, Fin.val_succ]

private theorem eval_killX0 (x : Fin 2 → ℂ) (p : Coef) :
    MvPolynomial.eval x (killX0 p) = MvPolynomial.eval ![0, x 1] p := by
  have h : (MvPolynomial.eval x).comp (killX0 : Coef →ₐ[ℂ] Coef).toRingHom = MvPolynomial.eval ![0, x 1] := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, ms_killX0_C, MvPolynomial.eval_C,
        MvPolynomial.eval_C]
    · fin_cases i
      · show MvPolynomial.eval x (killX0 (MvPolynomial.X 0)) = MvPolynomial.eval ![0, x 1] (MvPolynomial.X 0)
        rw [ms_killX0_X0, map_zero, MvPolynomial.eval_X]
        rfl
      · show MvPolynomial.eval x (killX0 (MvPolynomial.X 1)) = MvPolynomial.eval ![0, x 1] (MvPolynomial.X 1)
        rw [ms_killX0_X1, MvPolynomial.eval_X, MvPolynomial.eval_X]
        rfl
  exact RingHom.congr_fun h p

variable {ι' : Type} [Fintype ι'] [DecidableEq ι']

omit [Fintype ι'] [DecidableEq ι'] in
private theorem map_killX0_eval_eq_sum {R : Matrix ι' ι' Coef} {δ : ℕ} (hR : ∀ μ μ', (R μ μ').totalDegree ≤ δ)
    (x : Fin 2 → ℂ) :
    (R.map killX0).map (MvPolynomial.eval x) = ∑ b : Fin (δ + 1), x 1 ^ (b : ℕ) • coefM R (0, b) := by
  ext μ μ'
  rw [Matrix.map_apply, Matrix.map_apply, eval_killX0, eval_eq_sum_coeff_expo _ (hR μ μ'), Matrix.sum_apply,
    sum_box_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pow_zero, one_mul,
    zero_pow (Nat.succ_ne_zero _), zero_mul, mul_zero, Finset.sum_const_zero, add_zero, Matrix.smul_apply,
    smul_eq_mul, coefM]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

private theorem aeval_reix {r : ℕ} (e : Fin (r + 1) ≃ ι') (M : Matrix ι' ι' ℂ) (p : Polynomial ℂ) :
    Polynomial.aeval (reix e M) p = reix e (Polynomial.aeval M p) := by
  have h : ∀ X : Matrix ι' ι' ℂ, reix e X = Matrix.reindexAlgEquiv ℂ ℂ e.symm X := fun X => rfl
  rw [h, h, Polynomial.aeval_algHom_apply]

omit [DecidableEq ι'] in
private theorem sum_mulVec' {α : Type*} (s : Finset α) (M : α → Matrix ι' ι' ℂ) (v : ι' → ℂ) :
    (∑ a ∈ s, M a) *ᵥ v = ∑ a ∈ s, M a *ᵥ v := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, Matrix.zero_mulVec]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_mulVec, ih]

private theorem asm_system {δ : ℕ} {R : Matrix ι' ι' Coef} (hR : ∀ μ μ', (R μ μ').totalDegree ≤ δ)
    (T Ti : Matrix ι' ι' ℂ) (hTi : Ti * T = 1) {mst : ℝ → ℝ → ι' → ℂ}
    (hsys : ∀ s u : ℝ, HasDerivAt (fun s => mst s u) (mev R s u *ᵥ mst s u) s) {G : ℝ → ℝ → ι' → ℂ}
    (hG : ∀ a c : ℝ, 0 < a → 0 < c → G a c = T *ᵥ mst (Real.log a) (Real.log c)) {a c : ℝ} (ha : 0 < a)
    (hc : 0 < c) :
    HasDerivAt (fun a => G a c)
      ((a⁻¹ : ℝ) • (T *ᵥ (mev R (Real.log a) (Real.log c) *ᵥ mst (Real.log a) (Real.log c)))) a ∧
    (a : ℂ) • ((a⁻¹ : ℝ) • (T *ᵥ (mev R (Real.log a) (Real.log c) *ᵥ mst (Real.log a) (Real.log c)))) =
      ∑ ab ∈ box δ, ((a : ℂ) ^ ab.1 * (c : ℂ) ^ ab.2) • ((T * coefM R ab * Ti) *ᵥ G a c) := by
  constructor
  · have h1 := (hsys (Real.log a) (Real.log c)).scomp a (Real.hasDerivAt_log ha.ne')
    have h3' : HasDerivAt (fun a => T *ᵥ mst (Real.log a) (Real.log c))
        (T *ᵥ ((a⁻¹ : ℝ) • (mev R (Real.log a) (Real.log c) *ᵥ mst (Real.log a) (Real.log c)))) a := by
      refine hasDerivAt_pi.2 fun i => ?_
      simp only [Matrix.mulVec, dotProduct]
      exact HasDerivAt.fun_sum fun j _ => (hasDerivAt_pi.1 h1 j).const_mul (T i j)
    have heq : ∀ X : ι' → ℂ, T *ᵥ ((a⁻¹ : ℝ) • X) = (a⁻¹ : ℝ) • (T *ᵥ X) := fun X => by
      funext i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Complex.real_smul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have h3 := h3'.congr_deriv (heq _)
    exact h3.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (Ioi_mem_nhds ha) fun a' ha' => hG a' c ha' hc)
  · have hsm : ∀ X : ι' → ℂ, (a : ℂ) • ((a⁻¹ : ℝ) • X) = X := fun X => by
      funext i
      simp only [Pi.smul_apply, Complex.real_smul, Complex.ofReal_inv, smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 ha.ne'), one_mul]
    have hmst : mst (Real.log a) (Real.log c) = Ti *ᵥ G a c := by
      rw [hG a c ha hc, Matrix.mulVec_mulVec, hTi, Matrix.one_mulVec]
    have hexp : ∀ {b : ℝ}, 0 < b → Complex.exp (Real.log b) = (b : ℂ) := fun hb => by
      rw [← Complex.ofReal_exp, Real.exp_log hb]
    rw [hsm, hmst, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mev_eq_sum_coefM hR, hexp ha, hexp hc, Finset.mul_sum,
      Finset.sum_mul, sum_mulVec']
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mulVec]

end AssemblyGlue
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

section AssemblyMain

variable {ι' : Type} [Fintype ι'] [DecidableEq ι']

omit [DecidableEq ι'] in
private theorem reix_smul_sum {r δ : ℕ} (e : Fin (r + 1) ≃ ι') (c : Fin (δ + 1) → ℂ) (T Ti : Matrix ι' ι' ℂ)
    (C : Fin (δ + 1) → Matrix ι' ι' ℂ) :
    ∑ b, c b • reix e (T * C b * Ti) = reix e (T * (∑ b, c b • C b) * Ti) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, reix_apply, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul]

private theorem asm_wall {δ : ℕ} {R : Matrix ι' ι' Coef} (hR : ∀ μ μ', (R μ μ').totalDegree ≤ δ)
    {T Ti : Matrix ι' ι' ℂ}
    (hTiT : Ti * T = 1) (hTTi : T * Ti = 1) {r : ℕ} (e : Fin (r + 1) ≃ ι') {q : Polynomial ℂ}
    (hwall : ∀ x : Fin 2 → ℂ, Polynomial.aeval ((R.map killX0).map (MvPolynomial.eval x)) q = 0) (zc : ℂ) :
    Polynomial.aeval (∑ b : Fin (δ + 1), (zc ^ (b : ℕ)) • reix e (T * coefM R (0, (b : ℕ)) * Ti)) q = 0 := by
  have h : ∑ b : Fin (δ + 1), (zc ^ (b : ℕ)) • reix e (T * coefM R (0, (b : ℕ)) * Ti) =
      reix e (T * (R.map killX0).map (MvPolynomial.eval ![0, zc]) * Ti) := by
    rw [map_killX0_eval_eq_sum hR, reix_smul_sum]
    rfl
  rw [h, aeval_reix, ms_aeval_conj _ _ _ hTiT hTTi, hwall, Matrix.mul_zero, Matrix.zero_mul]
  rfl

omit [DecidableEq ι'] in
private theorem asm_block {r δ : ℕ} (e : Fin (r + 1) ≃ ι') (c : Fin (δ + 1) → ℂ) (M : Fin (δ + 1) → Matrix ι' ι' ℂ)
    (kv : ι' → ℂ) (i : Fin (r + 1)) :
    ∑ b, c b * (M b *ᵥ kv) (e i) = ∑ j, (∑ b, c b * reix e (M b) i j) * kv (e j) := by
  simp only [Matrix.mulVec, dotProduct, reix_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  symm
  refine Fintype.sum_equiv e _ _ fun j => ?_
  exact Finset.sum_congr rfl fun b _ => by ring

omit [DecidableEq ι'] in
private theorem exists_equiv_fin (μ₀ : ι') : ∃ (r : ℕ) (e : Fin (r + 1) ≃ ι'), e 0 = μ₀ := by
  have hN : 0 < Fintype.card ι' := Fintype.card_pos_iff.2 ⟨μ₀⟩
  obtain ⟨r, hr⟩ : ∃ r, Fintype.card ι' = r + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hN).symm⟩
  let e₁ : Fin (r + 1) ≃ ι' := (finCongr hr.symm).trans (Fintype.equivFin ι').symm
  refine ⟨r, (Equiv.swap (0 : Fin (r + 1)) (e₁.symm μ₀)).trans e₁, ?_⟩
  rw [Equiv.trans_apply, Equiv.swap_apply_left, Equiv.apply_symm_apply]

omit [DecidableEq ι'] in

private theorem asm_coeff_form {r δ : ℕ} (e : Fin (r + 1) ≃ ι') (T Ti : Matrix ι' ι' ℂ) (R : Matrix ι' ι' Coef)
    (ac cc : ℂ) (Y kv : ι' → ℂ) (Fv : Fin (r + 1) → ℂ) (hFv : ∀ j, Fv j = kv (e j))
    (hX : ac • Y = ∑ ab ∈ box δ, (ac ^ ab.1 * cc ^ ab.2) • ((T * coefM R ab * Ti) *ᵥ kv)) :
    ac • (fun i : Fin (r + 1) => Y (e i)) =
      (fun i => ∑ j, (∑ b : Fin (δ + 1), cc ^ (b : ℕ) * reix e (T * coefM R (0, (b : ℕ)) * Ti) i j) • Fv j) +
        ∑ k : Fin δ, ∑ b : Fin (δ + 1), (ac ^ ((k : ℕ) + 1) * cc ^ (b : ℕ)) •
          matL (reix e (T * coefM R ((k : ℕ) + 1, (b : ℕ)) * Ti)) Fv := by
  have hF : Fv = fun j => kv (e j) := funext hFv
  subst hF
  funext i
  rw [Pi.smul_apply, show ac • Y (e i) = (ac • Y) (e i) from rfl, hX, Finset.sum_apply, sum_box_eq]
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pow_zero, one_mul, matL_apply, reix_mulVec]
  rw [asm_block e]

end AssemblyMain
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

private theorem exists_words_rDl_torus_hasDerivAt_systems (N₂ N₃ : ℕ) :
    ∃ (d d₂ d' d₂' : ℕ),
      ∀ (cω : ℂ) (a₂ : Fin (N₂ + 1) → ℂ), a₂ (Fin.last N₂) = 1 → ∀ (a₃ : Fin (N₃ + 1) → ℂ), a₃ (Fin.last N₃) = 1 →
      ∃ (q q' : Polynomial ℂ),
      q ≠ 0 ∧ q' ≠ 0 ∧ q.natDegree ≤ 6 * N₂ * N₃ + 1 ∧ q'.natDegree ≤ 6 * N₂ * N₃ + 1 ∧
      ∀ (n : ℕ) (σ : M3 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (kb : Fin (n + 1) → M3),
      ContDiffOn ℝ (⊤ : ℕ∞) σ GLs → σ 1 = 1 →
      (∀ k k' : M3, kᵀ * k = 1 → k'ᵀ * k' = 1 → σ (k * k') = σ k * σ k') →
      (∀ l, (kb l)ᵀ * kb l = 1) → kb 0 = 1 →
      ∃ (r : ℕ) (w : Fin (r + 1) → List (Fin 3 × Fin 3)) (m : Fin (r + 1) → Fin (n + 1))
        (Mc : M3 → Fin (d₂ + 1) → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
        (Mc' : M3 → Fin (d₂' + 1) → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
        (A : M3 → Fin d → Fin (d₂ + 1) → ((Fin (r + 1) → ℂ) →L[ℂ] (Fin (r + 1) → ℂ)))
        (A' : M3 → Fin d' → Fin (d₂' + 1) → ((Fin (r + 1) → ℂ) →L[ℂ] (Fin (r + 1) → ℂ))),
        w 0 = [] ∧ m 0 = 0 ∧
        (∀ b, ContinuousOn (fun k => Mc k b) GLs) ∧ (∀ a, ContinuousOn (fun k => Mc' k a) GLs) ∧
        (∀ i b, ContinuousOn (fun k => A k i b) GLs) ∧ (∀ i a, ContinuousOn (fun k => A' k i a) GLs) ∧
        ∀ k₀ : M3, k₀ᵀ * k₀ = 1 →
          (∀ z : ℝ, 0 < z → Polynomial.aeval (∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • Mc k₀ b) q = 0) ∧
          (∀ y : ℝ, 0 < y → Polynomial.aeval (∑ a : Fin (d₂' + 1), ((y : ℂ) ^ (a : ℕ)) • Mc' k₀ a) q' = 0) ∧
          ∀ W₁ : M3 → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) W₁ GLs →
          (∀ n' x : M3, IsUpperUni n' → x ∈ GLs → W₁ (n' * x) = uniChar n' * W₁ x) →
          (∀ x ∈ GLs, rD 1 W₁ x = cω * W₁ x) →
          (∀ x k : M3, x ∈ GLs → kᵀ * k = 1 → ∀ l, W₁ (x * k * kb l) = ∑ l', σ k l' l * W₁ (x * kb l')) →
          (∀ x ∈ GLs, ∑ j, a₂ j * (c2^[j] W₁) x = 0) → (∀ x ∈ GLs, ∑ j, a₃ j * (c3^[j] W₁) x = 0) →
          ∀ F : ℝ → ℝ → (Fin (r + 1) → ℂ),
          (∀ (y z : ℝ) (i : Fin (r + 1)), F y z i = rDl (w i) W₁ (torus y z * k₀ * kb (m i))) →
          ∃ Fy Fz : ℝ → ℝ → (Fin (r + 1) → ℂ),
          (∀ z : ℝ, 0 < z → ∀ y : ℝ, 0 < y → HasDerivAt (fun y => F y z) (Fy y z) y ∧
            (y : ℂ) • Fy y z = (fun i => ∑ j, (∑ b : Fin (d₂ + 1), (z : ℂ) ^ (b : ℕ) * Mc k₀ b i j) • F y z j) +
              ∑ k : Fin d, ∑ b : Fin (d₂ + 1),
                ((y : ℂ) ^ ((k : ℕ) + 1) * (z : ℂ) ^ (b : ℕ)) • A k₀ k b (F y z)) ∧
          (∀ y : ℝ, 0 < y → ∀ z : ℝ, 0 < z → HasDerivAt (fun z => F y z) (Fz y z) z ∧
            (z : ℂ) • Fz y z = (fun i => ∑ j, (∑ a : Fin (d₂' + 1), (y : ℂ) ^ (a : ℕ) * Mc' k₀ a i j) • F y z j) +
              ∑ k : Fin d', ∑ a : Fin (d₂' + 1),
                ((z : ℂ) ^ ((k : ℕ) + 1) * (y : ℂ) ^ (a : ℕ)) • A' k₀ k a (F y z)) := by
  classical
  have hms0 := exists_master_system N₂ N₃ (3 + 2 * N₂ + 3 * N₃) le_rfl
  obtain ⟨d, hd⟩ := hms0
  refine ⟨d, d, d, d, fun cω a₂ ha₂ a₃ ha₃ => ?_⟩

  have hw00 := exists_casOp_wall00 cω
  obtain ⟨ω₂, ω₃, hω⟩ := hw00
  have hΩs := isCasimirPair_wall00 cω
  have hΩs₂ := diagEntry_cmap_const_eq (fun ab => (hω 1 (fun _ _ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) ab).1)
  have hΩs₃ := diagEntry_cmap_const_eq (fun ab => (hω 1 (fun _ _ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) ab).2)
  have hdq := hd ω₂ ω₃ a₂ ha₂ a₃ ha₃ _ _ hΩs hΩs₂ hΩs₃
  obtain ⟨q, hq0, hqdeg, hq⟩ := hdq
  have ha₃' : (fun j : Fin (N₃ + 1) => (-1 : ℂ) ^ (N₃ - (j : ℕ)) * a₃ j) (Fin.last N₃) = 1 := by
    beta_reduce
    rw [Fin.val_last, Nat.sub_self, pow_zero, one_mul, ha₃]
  have hΩs₂' : ∀ ab : ℕ × ℕ, swapOp (diagEntry (0 : Fin 1)
      (cmap (fun p => MvPolynomial.C (MvPolynomial.constantCoeff p))
        (casOp₂ (fun _ _ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) cω))) ab =
      fun _ _ => MvPolynomial.C ((fun ab : ℕ × ℕ => ω₂ ab.swap) ab) := fun ab => by
    rw [swapOp_apply', hΩs₂]
    funext u u'
    exact swapC_C _
  have hΩs₃' : ∀ ab : ℕ × ℕ, (-swapOp (diagEntry (0 : Fin 1)
      (cmap (fun p => MvPolynomial.C (MvPolynomial.constantCoeff p))
        (casOp₃ (fun _ _ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) cω)))) ab =
      fun _ _ => MvPolynomial.C ((fun ab : ℕ × ℕ => -ω₃ ab.swap) ab) := fun ab => by
    rw [Finsupp.neg_apply, swapOp_apply', hΩs₃]
    funext u u'
    rw [Matrix.neg_apply, Matrix.map_apply, swapC_C, map_neg]
  have hdq' :=
    hd _ _ a₂ ha₂ (fun j : Fin (N₃ + 1) => (-1 : ℂ) ^ (N₃ - (j : ℕ)) * a₃ j) ha₃' _ _ hΩs.swapOp hΩs₂' hΩs₃'
  obtain ⟨q', hq0', hqdeg', hq'⟩ := hdq'
  refine ⟨q, q', hq0, hq0', hqdeg, hqdeg', fun n σ kb hσ hσ1 hσm hkb hkb0 => ?_⟩

  have hΩ := isCasimirPair_casOp σ hσ hσ1 hσm cω
  have h𝒟 := isWordFamily_wordOp σ hσ hσ1 hσm cω
  have hcd := exists_conj_soData_eq_diagonal σ hσ hσ1 hσm 2 1 (by decide)
  obtain ⟨U, zw, hU, hUd⟩ := hcd
  have hwx0 := exists_wallX0_diagonal cω
  obtain ⟨φ₂, φ₃, hφ₂, hφ₃, hφ⟩ := hwx0
  have h5 := hφ (n + 1) (soData σ) U zw hU hUd
  have hcc₂ : ∀ ab, (casOp₂ (soData σ) cω ab).map MvPolynomial.constantCoeff =
      ω₂ ab • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := fun ab => (hω _ _ ab).1
  have hcc₃ : ∀ ab, (casOp₃ (soData σ) cω ab).map MvPolynomial.constantCoeff =
      ω₃ ab • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := fun ab => (hω _ _ ab).2
  have hdg₂ : ∀ (ab : ℕ × ℕ) (i i' : Fin (n + 1)), (casOp₂ (soData σ) cω ab i i').totalDegree ≤ 3 :=
    fun ab i i' => (totalDegree_casOp_le (soData σ) cω ab i i').1
  have hdg₃ : ∀ (ab : ℕ × ℕ) (i i' : Fin (n + 1)), (casOp₃ (soData σ) cω ab i i').totalDegree ≤ 3 :=
    fun ab i i' => (totalDegree_casOp_le (soData σ) cω ab i i').2
  have h5₂ : ∀ (ab : ℕ × ℕ) (i i' : Fin (n + 1)),
      killX0 (conjOp U (casOp₂ (soData σ) cω) ab i i') = if i = i' then φ₂ ab (zw i) else 0 :=
    fun ab i i' => (h5 ab i i').1
  have h5₃ : ∀ (ab : ℕ × ℕ) (i i' : Fin (n + 1)),
      killX0 (conjOp U (casOp₃ (soData σ) cω) ab i i') = if i = i' then φ₃ ab (zw i) else 0 :=
    fun ab i i' => (h5 ab i i').2
  have hqR := hq (n + 1) _ _ _ hΩ h𝒟 hcc₂ hcc₃ hdg₂ hdg₃ U zw φ₂ φ₃ hU hφ₂ hφ₃ h5₂ h5₃
    fun i => isCasimirPair_weightPair hΩ φ₂ φ₃ U zw hU h5₂ h5₃ i
  obtain ⟨R, hRdeg, hRwall, hRsys⟩ := hqR

  have hcd' := exists_conj_soData_eq_diagonal σ hσ hσ1 hσm 1 0 (by decide)
  obtain ⟨U', zw', hU', hUd'⟩ := hcd'
  have hwx1 := exists_wallX1_diagonal cω
  obtain ⟨ψ₂, ψ₃, hψ₂, hψ₃, hψ⟩ := hwx1
  have h5' := hψ (n + 1) (soData σ) U' zw' hU' hUd'
  have h5'₂ := killX0_conjOp_swapOp fun ab i i' => (h5' ab i i').1
  have h5'₃ := killX0_conjOp_neg_swapOp fun ab i i' => (h5' ab i i').2
  have hst₂ : ∀ (ab : ℕ × ℕ) (c : ℂ), killX0 ((fun (ab : ℕ × ℕ) (c : ℂ) => swapC (ψ₂ ab.swap c)) ab c) =
      (fun (ab : ℕ × ℕ) (c : ℂ) => swapC (ψ₂ ab.swap c)) ab c := fun ab c => by
    beta_reduce
    rw [killX0_swapC, hψ₂]
  have hst₃ : ∀ (ab : ℕ × ℕ) (c : ℂ), killX0 ((fun (ab : ℕ × ℕ) (c : ℂ) => -swapC (ψ₃ ab.swap c)) ab c) =
      (fun (ab : ℕ × ℕ) (c : ℂ) => -swapC (ψ₃ ab.swap c)) ab c := fun ab c => by
    beta_reduce
    rw [map_neg, killX0_swapC, hψ₃]
  have hqR' := hq' (n + 1) _ _ _ hΩ.swapOp h𝒟.swapOp (map_constantCoeff_swapOp hcc₂)
    (map_constantCoeff_neg_swapOp hcc₃) (totalDegree_swapOp_le hdg₂) (totalDegree_neg_swapOp_le hdg₃) U' zw'
    (fun (ab : ℕ × ℕ) (c : ℂ) => swapC (ψ₂ ab.swap c)) (fun (ab : ℕ × ℕ) (c : ℂ) => -swapC (ψ₃ ab.swap c)) hU'
    hst₂ hst₃ h5'₂ h5'₃ fun i => isCasimirPair_weightPair hΩ.swapOp (fun (ab : ℕ × ℕ) (c : ℂ) => swapC (ψ₂ ab.swap c))
      (fun (ab : ℕ × ℕ) (c : ℂ) => -swapC (ψ₃ ab.swap c)) U' zw' hU' h5'₂ h5'₃ i
  obtain ⟨R', hRdeg', hRwall', hRsys'⟩ := hqR'

  have hidx := exists_equiv_fin
    ((PWord.pad 0 (Nat.zero_le (3 + 2 * N₂ + 3 * N₃)) Fin.elim0, 0) : MIdx (3 + 2 * N₂ + 3 * N₃) n)
  obtain ⟨r, e, he0⟩ := hidx
  let Tk : M3 → Matrix (MIdx (3 + 2 * N₂ + 3 * N₃) n) (MIdx (3 + 2 * N₂ + 3 * N₃) n) ℂ := fun k => transfer kb σ k
  let Tik : M3 → Matrix (MIdx (3 + 2 * N₂ + 3 * N₃) n) (MIdx (3 + 2 * N₂ + 3 * N₃) n) ℂ :=
    fun k => transferInv kb σ k
  let Mc : M3 → Fin (d + 1) → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
    fun k b => reix e (Tk k * coefM R (0, (b : ℕ)) * Tik k)
  let Mc' : M3 → Fin (d + 1) → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
    fun k a => reix e (Tk k * coefM R' (0, (a : ℕ)) * Tik k)
  let A : M3 → Fin d → Fin (d + 1) → ((Fin (r + 1) → ℂ) →L[ℂ] (Fin (r + 1) → ℂ)) :=
    fun k i b => matL (reix e (Tk k * coefM R ((i : ℕ) + 1, (b : ℕ)) * Tik k))
  let A' : M3 → Fin d → Fin (d + 1) → ((Fin (r + 1) → ℂ) →L[ℂ] (Fin (r + 1) → ℂ)) :=
    fun k i a => matL (reix e (Tk k * coefM R' ((i : ℕ) + 1, (a : ℕ)) * Tik k))
  have hTc : ContinuousOn Tk GLs := continuousOn_transfer hkb hσ
  have hTic : ContinuousOn Tik GLs := continuousOn_transferInv hkb hσ
  refine ⟨r, fun i => List.ofFn (e i).1.toFn, fun i => (e i).2, ?_⟩
  refine ⟨Mc, ?_⟩
  refine ⟨Mc', ?_⟩
  refine ⟨A, ?_⟩
  refine ⟨A', ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun k₀ hk₀ => ⟨?_, ?_, ?_⟩⟩
  · show List.ofFn (e 0).1.toFn = []
    rw [he0]
    exact List.ofFn_zero
  · show (e 0).2 = 0
    rw [he0]
  · intro b
    exact (continuous_reix e).comp_continuousOn ((hTc.mul continuousOn_const).mul hTic)
  · intro a
    exact (continuous_reix e).comp_continuousOn ((hTc.mul continuousOn_const).mul hTic)
  · intro i b
    exact continuous_matL.comp_continuousOn
      ((continuous_reix e).comp_continuousOn ((hTc.mul continuousOn_const).mul hTic))
  · intro i a
    exact continuous_matL.comp_continuousOn
      ((continuous_reix e).comp_continuousOn ((hTc.mul continuousOn_const).mul hTic))
  · intro z _
    have hTiT : Tik k₀ * Tk k₀ = 1 := transferInv_mul_transfer hkb hσ1 hσm hk₀
    have hTTi : Tk k₀ * Tik k₀ = 1 := transfer_mul_transferInv hkb hσ1 hσm hk₀
    exact asm_wall hRdeg hTiT hTTi e hRwall _
  · intro y _
    have hTiT : Tik k₀ * Tk k₀ = 1 := transferInv_mul_transfer hkb hσ1 hσm hk₀
    have hTTi : Tk k₀ * Tik k₀ = 1 := transfer_mul_transferInv hkb hσ1 hσm hk₀
    exact asm_wall hRdeg' hTiT hTTi e hRwall' _

  intro W₁ hW hN hZ hK hrel₂ hrel₃ F hF
  have hT : Transf σ cω (vecW kb W₁) :=
    ⟨contDiffOn_vecW hkb hW, vecW_uni hkb hN, vecW_orth hK, vecW_centre hkb hW hZ⟩
  have hΦ₀ : Smooth2 (onTorus (vecW kb W₁)) := smooth2_onTorus hT.smooth
  have hsys := hRsys _ hΦ₀ (hT.apply_polyOp_casOp₂ hσ a₂ (vecW_rel₂ hkb hW hrel₂))
    (hT.apply_polyOp_casOp₃ hσ a₃ (vecW_rel₃ hkb hW hrel₃))

  have hsw : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ × ℝ => (t.2, t.1)) := contDiff_snd.prodMk contDiff_fst
  have hΦ₀' : Smooth2 (fun s₁ s₂ => onTorus (vecW kb W₁) s₂ s₁) :=
    ContDiff.comp (g := fun t : ℝ × ℝ => onTorus (vecW kb W₁) t.1 t.2) (f := fun t : ℝ × ℝ => (t.2, t.1)) hΦ₀ hsw
  have hrelT₂' : apply (polyOp a₂ (swapOp (casOp₂ (soData σ) cω))) (fun s₁ s₂ => onTorus (vecW kb W₁) s₂ s₁) =
      fun _ _ => 0 := by
    rw [← swapOp_polyOp]
    funext t₁ t₂
    rw [apply_swapOp _ hΦ₀]
    exact congrFun (congrFun (hT.apply_polyOp_casOp₂ hσ a₂ (vecW_rel₂ hkb hW hrel₂)) t₂) t₁
  have hrelT₃' : apply (polyOp (fun j : Fin (N₃ + 1) => (-1 : ℂ) ^ (N₃ - (j : ℕ)) * a₃ j)
      (-swapOp (casOp₃ (soData σ) cω))) (fun s₁ s₂ => onTorus (vecW kb W₁) s₂ s₁) = fun _ _ => 0 := by
    rw [polyOp_signed_neg, apply_smul, ← swapOp_polyOp]
    funext t₁ t₂
    rw [apply_swapOp _ hΦ₀, congrFun (congrFun (hT.apply_polyOp_casOp₃ hσ a₃ (vecW_rel₃ hkb hW hrel₃)) t₂) t₁,
      smul_zero]
  have hsys' := hRsys' _ hΦ₀' hrelT₂' hrelT₃'
  have hms : ∀ s u : ℝ, master (3 + 2 * N₂ + 3 * N₃) (fun k w => swapOp (wordOp (soData σ) cω k w))
      (fun s₁ s₂ => onTorus (vecW kb W₁) s₂ s₁) s u =
      master (3 + 2 * N₂ + 3 * N₃) (wordOp (soData σ) cω) (onTorus (vecW kb W₁)) u s := fun s u => by
    funext μ
    show apply (swapOp _) (fun s₁ s₂ => onTorus (vecW kb W₁) s₂ s₁) s u μ.2 = _
    rw [apply_swapOp _ hΦ₀]
    rfl

  have hTiT : Tik k₀ * Tk k₀ = 1 := transferInv_mul_transfer hkb hσ1 hσm hk₀
  have hG : ∀ y z : ℝ, 0 < y → 0 < z → keyVec kb W₁ k₀ y z = Tk k₀ *ᵥ
      master (3 + 2 * N₂ + 3 * N₃) (wordOp (soData σ) cω) (onTorus (vecW kb W₁)) (Real.log y) (Real.log z) :=
    fun y z hy hz => keyVec_eq_transfer_mulVec hkb hσ hW hT hk₀ hy hz
  have hG' : ∀ z y : ℝ, 0 < z → 0 < y → (fun z y => keyVec kb W₁ k₀ y z) z y = Tk k₀ *ᵥ
      master (3 + 2 * N₂ + 3 * N₃) (fun k w => swapOp (wordOp (soData σ) cω k w))
        (fun s₁ s₂ => onTorus (vecW kb W₁) s₂ s₁) (Real.log z) (Real.log y) := by
    intro z y hz hy
    rw [hms]
    exact hG y z hy hz
  have hF' : ∀ y z, F y z = fun i => keyVec kb W₁ k₀ y z (e i) := fun y z => funext fun i => by
    rw [hF]
    show rDl (List.ofFn (e i).1.toFn) W₁ _ = _
    rw [rDl_ofFn]
    rfl
  refine ⟨fun y z => fun i => ((y⁻¹ : ℝ) • (Tk k₀ *ᵥ (mev R (Real.log y) (Real.log z) *ᵥ
      master (3 + 2 * N₂ + 3 * N₃) (wordOp (soData σ) cω) (onTorus (vecW kb W₁)) (Real.log y) (Real.log z)))) (e i),
    fun y z => fun i => ((z⁻¹ : ℝ) • (Tk k₀ *ᵥ (mev R' (Real.log z) (Real.log y) *ᵥ
      master (3 + 2 * N₂ + 3 * N₃) (fun k w => swapOp (wordOp (soData σ) cω k w))
        (fun s₁ s₂ => onTorus (vecW kb W₁) s₂ s₁) (Real.log z) (Real.log y)))) (e i), ?_, ?_⟩
  · intro z hz y hy
    have hsy := asm_system hRdeg (Tk k₀) (Tik k₀) hTiT hsys hG hy hz
    obtain ⟨hder, hid⟩ := hsy
    refine ⟨?_, ?_⟩
    · rw [show (fun y => F y z) = fun y => fun i => keyVec kb W₁ k₀ y z (e i) from funext fun y => hF' y z]
      exact hasDerivAt_pi.2 fun i => hasDerivAt_pi.1 hder (e i)
    · exact asm_coeff_form e (Tk k₀) (Tik k₀) R (y : ℂ) (z : ℂ) _ (keyVec kb W₁ k₀ y z) (F y z)
        (fun j => congrFun (hF' y z) j) hid
  · intro y hy z hz
    have hsz := asm_system hRdeg' (Tk k₀) (Tik k₀) hTiT hsys' hG' hz hy
    obtain ⟨hder, hid⟩ := hsz
    refine ⟨?_, ?_⟩
    · rw [show (fun z => F y z) = fun z => fun i => keyVec kb W₁ k₀ y z (e i) from funext fun z => hF' y z]
      exact hasDerivAt_pi.2 fun i => hasDerivAt_pi.1 hder (e i)
    · exact asm_coeff_form e (Tk k₀) (Tik k₀) R' (z : ℂ) (y : ℂ) _ (keyVec kb W₁ k₀ y z) (F y z)
        (fun j => congrFun (hF' y z) j) hid

end Main
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

end RealGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3"

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm AutomorphicForm.StandardKernel WhittakerBlock LanglandsTunnell.CubicInduction.WhittakerBlock

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv WhittakerBlock.casimir2 WhittakerBlock.casimir3 AdelicGL globalPointsGL centralScalarGL upperUnipotent3 componentAt3 archComponent3 whittaker3 orth3 whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3"
namespace ArchCalculus
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem realCoord_ofReal (r : ℝ) : realCoord (ofReal r) = r := by
  show (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)
      ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal Rat.infinitePlace)).symm r) = r
  exact RingEquiv.apply_symm_apply _ r

private def realEquiv : InfiniteAdeleRing ℚ ≃+* ℝ where
  toFun := realCoord
  invFun := ofReal
  left_inv := ofReal_realCoord
  right_inv := realCoord_ofReal
  map_mul' := map_mul realCoord
  map_add' := map_add realCoord

private def ofRealHom : ℝ →+* InfiniteAdeleRing ℚ := realEquiv.symm.toRingHom

@[scoped simp] private theorem ofRealHom_apply (r : ℝ) : ofRealHom r = ofReal r := rfl

@[scoped simp] private theorem ofRealHom_realCoord (x : InfiniteAdeleRing ℚ) : ofRealHom
    (realCoord x) = x := ofReal_realCoord x

private theorem map_realCoord_map_ofRealHom (M : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (M.map realCoord).map ofRealHom = M := by
  ext i j
  simp only [Matrix.map_apply, ofRealHom_apply, ofReal_realCoord]

private def invertibleSet : Set (Fin 3 → Fin 3 → ℝ) := {e | (Matrix.of e).det ≠ 0}

private theorem isOpen_invertibleSet : IsOpen invertibleSet :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

private theorem isArchSmooth3_iff (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    IsArchSmooth3 φ ↔ ∀ g, ContDiffOn ℝ (⊤ : ℕ∞) (fun e => φ (g * archRealLift3 e)) invertibleSet :=
  Iff.rfl

private def archMat (e : Fin 3 → Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ) :=
  (Matrix.of e).map ofRealHom

private theorem archRealMat3_eq (e : Fin 3 → Fin 3 → ℝ) :
    archRealMat3 e = archMatrixInclN (Fin 3) ℚ (archMat e) := rfl

private def archUnit (e : Fin 3 → Fin 3 → ℝ) (he : e ∈ invertibleSet) : GL (Fin 3) (InfiniteAdeleRing ℚ) :=
  Matrix.GeneralLinearGroup.map ofRealHom (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) he)

private theorem coe_archUnit (e : Fin 3 → Fin 3 → ℝ) (he : e ∈ invertibleSet) :
    (archUnit e he : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) = archMat e := rfl

private theorem archRealLift3_eq (e : Fin 3 → Fin 3 → ℝ) (he : e ∈ invertibleSet) :
    archRealLift3 e = archInclN (Fin 3) ℚ (archUnit e he) := by
  have hu : IsUnit (archRealMat3 e) := ⟨archInclN (Fin 3) ℚ (archUnit e he), rfl⟩
  rw [archRealLift3, dif_pos hu]
  exact Units.ext hu.unit_spec

private theorem one_mem_invertibleSet : (fun a b : Fin 3 => if a = b then (1 : ℝ) else 0) ∈ invertibleSet := by
  have h : Matrix.of (fun a b : Fin 3 => if a = b then (1 : ℝ) else 0) = 1 := by
    ext a b
    simp [Matrix.one_apply]
  show (Matrix.of fun a b : Fin 3 => if a = b then (1 : ℝ) else 0).det ≠ 0
  rw [h, Matrix.det_one]
  exact one_ne_zero

private theorem archRealLift3_one : archRealLift3 (fun a b : Fin 3 => if a = b then (1 : ℝ) else 0) = 1 := by
  rw [archRealLift3_eq _ one_mem_invertibleSet, ← map_one (archInclN (Fin 3) ℚ)]
  congr 1
  apply Units.ext
  rw [coe_archUnit, Units.val_one, archMat]
  ext a b
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.one_apply, apply_ite ofRealHom, map_one, map_zero]

private theorem matrix_ext_of_arch_fin {M N : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)}
    (harch : M.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) = N.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ))
    (hfin : M.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) = N.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)) : M = N := by
  ext i j
  refine Prod.ext ?_ ?_
  · have h := congrFun (congrFun harch i) j
    simp [Matrix.map_apply] at h
    exact h
  · have h := congrFun (congrFun hfin i) j
    simp [Matrix.map_apply] at h
    exact h

private theorem map_adeleArch_archMatrixInclN (X : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (archMatrixInclN (Fin 3) ℚ X).map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) = X := by
  ext i j
  simp [Matrix.map_apply, adeleArch_archMatrixInclN]

private theorem map_adeleFin_archMatrixInclN (X : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (archMatrixInclN (Fin 3) ℚ X).map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) = 1 := by
  ext i j
  simp [Matrix.map_apply, adeleFin_archMatrixInclN, Matrix.one_apply]

private def adArray (k : AdelicGL 3 (𝓞 ℚ) ℚ) (e : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun a b => (realMat (archComponent3 (𝓞 ℚ) ℚ k)⁻¹ * Matrix.of e * realMat (archComponent3 (𝓞 ℚ) ℚ k)) a b

private theorem of_adArray (k : AdelicGL 3 (𝓞 ℚ) ℚ) (e : Fin 3 → Fin 3 → ℝ) :
    Matrix.of (adArray k e) =
      realMat (archComponent3 (𝓞 ℚ) ℚ k)⁻¹ * Matrix.of e * realMat (archComponent3 (𝓞 ℚ) ℚ k) := rfl

private theorem det_realMat_ne_zero (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) : (realMat h).det ≠ 0 := by
  have hu : IsUnit (realMat h) := ⟨realGL h, rfl⟩
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero

private theorem adArray_mem_invertibleSet (k : AdelicGL 3 (𝓞 ℚ) ℚ) {e : Fin 3 → Fin 3 → ℝ}
    (he : e ∈ invertibleSet) :
    adArray k e ∈ invertibleSet := by
  show (Matrix.of (adArray k e)).det ≠ 0
  rw [of_adArray, Matrix.det_mul, Matrix.det_mul]
  exact mul_ne_zero (mul_ne_zero (det_realMat_ne_zero _) he) (det_realMat_ne_zero _)

private theorem archMat_adArray (k : AdelicGL 3 (𝓞 ℚ) ℚ) (e : Fin 3 → Fin 3 → ℝ) :
    archMat (adArray k e) =
      ((archComponent3 (𝓞 ℚ) ℚ k)⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)).val * archMat e *
        (archComponent3 (𝓞 ℚ) ℚ k).val := by
  rw [archMat, of_adArray, Matrix.map_mul, Matrix.map_mul, realMat_eq, realMat_eq, map_realCoord_map_ofRealHom,
    map_realCoord_map_ofRealHom]
  rfl

private theorem map_adeleArch_val (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) =
      (archComponent3 (𝓞 ℚ) ℚ k).val := rfl

private theorem map_adeleArch_val_inv (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (k⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ).val.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) =
      ((archComponent3 (𝓞 ℚ) ℚ k)⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)).val := by
  rw [← map_inv (archComponent3 (𝓞 ℚ) ℚ)]
  rfl

private theorem map_adeleFin_inv_mul (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (k⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ).val.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) *
        (k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) = 1 := by
  rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) (map_zero _) (map_one _)]

private theorem inv_mul_archRealLift3_mul (k : AdelicGL 3 (𝓞 ℚ) ℚ) {e : Fin 3 → Fin 3 → ℝ}
    (he : e ∈ invertibleSet) :
    k⁻¹ * archRealLift3 e * k = archRealLift3 (adArray k e) := by
  rw [archRealLift3_eq _ he, archRealLift3_eq _ (adArray_mem_invertibleSet k he)]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  apply matrix_ext_of_arch_fin
  · rw [Matrix.map_mul, Matrix.map_mul]
    change _ * (archMatrixInclN (Fin 3) ℚ (archMat e)).map _ * _ =
      (archMatrixInclN (Fin 3) ℚ (archMat (adArray k e))).map _
    rw [map_adeleArch_archMatrixInclN, map_adeleArch_archMatrixInclN, archMat_adArray, map_adeleArch_val_inv,
      map_adeleArch_val]
  · rw [Matrix.map_mul, Matrix.map_mul]
    change _ * (archMatrixInclN (Fin 3) ℚ (archMat e)).map _ * _ =
      (archMatrixInclN (Fin 3) ℚ (archMat (adArray k e))).map _
    rw [map_adeleFin_archMatrixInclN, map_adeleFin_archMatrixInclN, Matrix.mul_one, map_adeleFin_inv_mul]

private theorem archRealLift3_mul_eq_mul_archRealLift3 (k : AdelicGL 3 (𝓞 ℚ) ℚ) {e : Fin 3 → Fin 3 → ℝ}
    (he : e ∈ invertibleSet) : archRealLift3 e * k = k * archRealLift3 (adArray k e) := by
  rw [← inv_mul_archRealLift3_mul k he, mul_assoc, ← mul_assoc k k⁻¹, mul_inv_cancel, one_mul]

private def adArrayL (k : AdelicGL 3 (𝓞 ℚ) ℚ) : (Fin 3 → Fin 3 → ℝ) →L[ℝ] (Fin 3 → Fin 3 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := adArray k
      map_add' := fun e e' => by
        funext a b
        simp only [adArray, Pi.add_apply]
        rw [show Matrix.of (e + e') = Matrix.of e + Matrix.of e' from rfl, Matrix.mul_add, Matrix.add_mul,
          Matrix.add_apply]
      map_smul' := fun c e => by
        funext a b
        simp only [adArray, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [show Matrix.of (c • e) = c • Matrix.of e from rfl, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
          smul_eq_mul] }

@[scoped simp] private theorem adArrayL_apply (k : AdelicGL 3 (𝓞 ℚ) ℚ)
    (e : Fin 3 → Fin 3 → ℝ) : adArrayL k e = adArray k e := rfl

private theorem isArchSmooth3_mul_right {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u)
    (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    IsArchSmooth3 (fun g => u (g * k)) := by
  intro g
  have hmaps : Set.MapsTo (adArrayL k) invertibleSet invertibleSet := fun e he => adArray_mem_invertibleSet k he
  refine ((hu (g * k)).comp ((adArrayL k).contDiff.contDiffOn) hmaps).congr ?_
  intro e he
  simp only [Function.comp, adArrayL_apply]
  rw [mul_assoc, archRealLift3_mul_eq_mul_archRealLift3 k he, ← mul_assoc]

private def oneArray : Fin 3 → Fin 3 → ℝ := fun a b => if a = b then (1 : ℝ) else 0

private def elemArray (i j : Fin 3) : Fin 3 → Fin 3 → ℝ := fun a b => if a = i ∧ b = j then (1 : ℝ) else 0

private theorem oneArray_mem_invertibleSet : oneArray ∈ invertibleSet := one_mem_invertibleSet

private theorem archRealLift3_oneArray : archRealLift3 oneArray = 1 := archRealLift3_one

private theorem archDeriv_apply_eq_fderiv_oneArray {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u)
    (i j : Fin 3)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archDeriv i j u g = fderiv ℝ (fun e => u (g * archRealLift3 e)) oneArray (elemArray i j) := by
  have h := archDeriv_eq_fderiv hu i j g (e := oneArray) oneArray_mem_invertibleSet
  rw [archRealLift3_oneArray, mul_one] at h
  rw [h]
  congr 1
  funext a b
  simp only [oneArray, elemArray]
  by_cases hb : b = j <;> by_cases ha : a = i <;> simp [ha, hb]

end LanglandsTunnell.CubicInduction.ArchCalculus
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv WhittakerBlock.casimir2 WhittakerBlock.casimir3 AdelicGL globalPointsGL centralScalarGL upperUnipotent3 componentAt3 archComponent3 whittaker3 orth3 whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3"
namespace ArchCalculus
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private def chart (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : (Fin 3 → Fin 3 → ℝ) → ℂ :=
  fun e => u (g * archRealLift3 e)

private theorem contDiffOn_chart {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (chart u g) invertibleSet :=
  hu g

private theorem contDiffAt_chart {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    {e : Fin 3 → Fin 3 → ℝ} (he : e ∈ invertibleSet) : ContDiffAt ℝ (⊤ : ℕ∞) (chart u g) e :=
  (contDiffOn_chart hu g).contDiffAt (isOpen_invertibleSet.mem_nhds he)

private def dirArray (e : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) : Fin 3 → Fin 3 → ℝ := fun a b => if b = j then e a i else 0

private theorem dirArray_oneArray (i j : Fin 3) : dirArray oneArray i j = elemArray i j := by
  funext a b
  simp only [dirArray, oneArray, elemArray]
  by_cases hb : b = j <;> by_cases ha : a = i <;> simp [ha, hb]

private theorem dirArray_elemArray (a b i j : Fin 3) :
    dirArray (elemArray a b) i j = if b = i then elemArray a j else 0 := by
  by_cases hb : b = i
  · subst hb
    funext x y
    by_cases hy : y = j <;> by_cases hx : x = a <;> simp [dirArray, elemArray, hx, hy]
  · have hib : i ≠ b := fun h => hb h.symm
    funext x y
    simp [dirArray, elemArray, hib, hb]

private def dirArrayL (i j : Fin 3) : (Fin 3 → Fin 3 → ℝ) →L[ℝ] (Fin 3 → Fin 3 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun e => dirArray e i j
      map_add' := fun e e' => by
        funext a b
        simp only [dirArray, Pi.add_apply]
        split_ifs <;> simp
      map_smul' := fun c e => by
        funext a b
        simp only [dirArray, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        split_ifs <;> simp }

@[scoped simp] private theorem dirArrayL_apply (i j : Fin 3) (e : Fin 3 → Fin 3 → ℝ) : dirArrayL i j e = dirArray e i j := rfl

private theorem archDeriv_mul_archRealLift3 {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u) (i j : Fin 3)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) {e : Fin 3 → Fin 3 → ℝ} (he : e ∈ invertibleSet) :
    archDeriv i j u (g * archRealLift3 e) = fderiv ℝ (chart u g) e (dirArray e i j) :=
  archDeriv_eq_fderiv hu i j g he

private theorem derivArray_eq (i j : Fin 3) (s : ℝ) :
    (fun a b : Fin 3 => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) =
      oneArray + s • elemArray i j := by
  funext a b
  simp only [oneArray, elemArray, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

private theorem archDeriv_apply (i j : Fin 3) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archDeriv i j u g = deriv (fun s : ℝ => chart u g (oneArray + s • elemArray i j)) 0 := by
  simp only [archDeriv, chart, derivArray_eq]

private theorem hasDerivAt_line (e v : Fin 3 → Fin 3 → ℝ) (s : ℝ) : HasDerivAt (fun t : ℝ => e + t • v) v s := by
  simpa using ((hasDerivAt_id s).smul_const v).const_add e

private theorem eventually_line_mem_invertibleSet (v : Fin 3 → Fin 3 → ℝ) :
    ∀ᶠ s : ℝ in nhds 0, oneArray + s • v ∈ invertibleSet := by
  have hc : Continuous fun s : ℝ => oneArray + s • v := by fun_prop
  have h0 : (fun s : ℝ => oneArray + s • v) 0 ∈ invertibleSet := by simpa using oneArray_mem_invertibleSet
  exact hc.continuousAt.preimage_mem_nhds (isOpen_invertibleSet.mem_nhds h0)

private theorem deriv_comp_line {F : (Fin 3 → Fin 3 → ℝ) → ℂ} (hF : DifferentiableAt ℝ F oneArray)
    (v : Fin 3 → Fin 3 → ℝ) :
    deriv (fun s : ℝ => F (oneArray + s • v)) 0 = fderiv ℝ F oneArray v := by
  have hF' : HasFDerivAt F (fderiv ℝ F oneArray) ((fun s : ℝ => oneArray + s • v) 0) := by
    simpa using hF.hasFDerivAt
  exact (hF'.comp_hasDerivAt (0 : ℝ) (hasDerivAt_line oneArray v 0)).deriv

private theorem archDeriv_archDeriv_apply {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u) (a b c d : Fin 3)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archDeriv a b (archDeriv c d u) g =
      fderiv ℝ (fderiv ℝ (chart u g)) oneArray (elemArray a b) (elemArray c d) +
        fderiv ℝ (chart u g) oneArray (if b = c then elemArray a d else 0) := by
  have hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (chart u g)) invertibleSet :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_invertibleSet).1 (contDiffOn_chart hu g)).2
  have hfd : HasFDerivAt (fderiv ℝ (chart u g))
      (fderiv ℝ (fderiv ℝ (chart u g)) oneArray) oneArray :=
    ((hsmooth.contDiffAt (isOpen_invertibleSet.mem_nhds oneArray_mem_invertibleSet)).differentiableAt
      (by simp)).hasFDerivAt
  have hdir : HasFDerivAt (fun e => dirArray e c d) (dirArrayL c d) oneArray := by
    simpa using (dirArrayL c d).hasFDerivAt

  have hFd := hfd.clm_apply hdir

  have hev : (fun s : ℝ => chart (archDeriv c d u) g (oneArray + s • elemArray a b)) =ᶠ[nhds 0]
      fun s : ℝ =>
        fderiv ℝ (chart u g) (oneArray + s • elemArray a b) (dirArray (oneArray + s • elemArray a b) c d) := by
    filter_upwards [eventually_line_mem_invertibleSet (elemArray a b)] with s hs
    simp only [chart]
    exact archDeriv_mul_archRealLift3 hu c d g hs
  rw [archDeriv_apply, hev.deriv_eq, deriv_comp_line hFd.differentiableAt (elemArray a b), hFd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
    dirArrayL_apply, dirArray_oneArray, dirArray_elemArray]
  exact add_comm _ _

private theorem archDeriv_comm_apply {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u) (a b c d : Fin 3)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archDeriv a b (archDeriv c d u) g =
      archDeriv c d (archDeriv a b u) g + (if b = c then archDeriv a d u g else 0) -
        (if d = a then archDeriv c b u g else 0) := by
  have hsymm : IsSymmSndFDerivAt ℝ (chart u g) oneArray :=
    (contDiffAt_chart hu g oneArray_mem_invertibleSet).isSymmSndFDerivAt
      (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)
  rw [archDeriv_archDeriv_apply hu a b c d g, archDeriv_archDeriv_apply hu c d a b g,
    hsymm (elemArray a b) (elemArray c d)]
  have h1 : fderiv ℝ (chart u g) oneArray (if b = c then elemArray a d else 0) =
      if b = c then archDeriv a d u g else 0 := by
    by_cases hbc : b = c
    · simp only [hbc, if_true]
      exact (archDeriv_apply_eq_fderiv_oneArray hu a d g).symm
    · simp [hbc]
  have h2 : fderiv ℝ (chart u g) oneArray (if d = a then elemArray c b else 0) =
      if d = a then archDeriv c b u g else 0 := by
    by_cases hda : d = a
    · simp only [hda, if_true]
      exact (archDeriv_apply_eq_fderiv_oneArray hu c b g).symm
    · simp [hda]
  rw [h1, h2]
  ring

private theorem archDeriv_comm {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u) (a b c d : Fin 3) :
    archDeriv a b (archDeriv c d u) =
      archDeriv c d (archDeriv a b u) + (if b = c then archDeriv a d u else 0) -
        (if d = a then archDeriv c b u else 0) := by
  funext g
  have h := archDeriv_comm_apply hu a b c d g
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [h]
  congr 1
  · congr 1
    split_ifs <;> simp
  · split_ifs <;> simp

private theorem isArchSmooth3_add {u v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u) (hv : IsArchSmooth3 v) :
    IsArchSmooth3 (u + v) :=
  smoothFunctions3.add_mem hu hv

private theorem isArchSmooth3_smul {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (c : ℂ) (hu : IsArchSmooth3 u) : IsArchSmooth3 (c • u)
    :=
  smoothFunctions3.smul_mem c hu

private theorem isArchSmooth3_zero : IsArchSmooth3 (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :=
  smoothFunctions3.zero_mem

private theorem isArchSmooth3_sum {ι : Type*} (s : Finset ι) {f : ι → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hf : ∀ i ∈ s, IsArchSmooth3 (f i)) : IsArchSmooth3 (∑ i ∈ s, f i) :=
  smoothFunctions3.sum_mem hf

private theorem archDeriv_add (i j : Fin 3) {u v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u)
    (hv : IsArchSmooth3 v) :
    archDeriv i j (u + v) = archDeriv i j u + archDeriv i j v := by
  have h := congrArg (fun φ : smoothFunctions3 => (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))
    (map_add (archDerivₗ i j) (⟨u, hu⟩ : smoothFunctions3) ⟨v, hv⟩)
  exact h

private theorem archDeriv_smul (i j : Fin 3) (c : ℂ) {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u) :
    archDeriv i j (c • u) = c • archDeriv i j u := by
  have h := congrArg (fun φ : smoothFunctions3 => (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))
    (map_smul (archDerivₗ i j) c (⟨u, hu⟩ : smoothFunctions3))
  exact h

private theorem archDeriv_zero (i j : Fin 3) : archDeriv i j (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = 0 := by
  have h := congrArg (fun φ : smoothFunctions3 => (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (map_zero (archDerivₗ i j))
  exact h

private theorem archDeriv_sum (i j : Fin 3) {ι : Type*} (s : Finset ι) {f : ι → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hf : ∀ l ∈ s, IsArchSmooth3 (f l)) :
    archDeriv i j (∑ l ∈ s, f l) = ∑ l ∈ s, archDeriv i j (f l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [archDeriv_zero]
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, archDeriv_add i j (hf x (Finset.mem_insert_self x s))
      (isArchSmooth3_sum s fun l hl => hf l (Finset.mem_insert_of_mem hl)),
        ih fun l hl => hf l (Finset.mem_insert_of_mem hl)]

private theorem archDeriv_sub (i j : Fin 3) {u v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u)
    (hv : IsArchSmooth3 v) :
    archDeriv i j (u - v) = archDeriv i j u - archDeriv i j v := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ← neg_one_smul ℂ v, archDeriv_add i j hu (isArchSmooth3_smul _ hv),
    archDeriv_smul i j _ hv, neg_one_smul]

private theorem archDeriv_ite (i j : Fin 3) (p : Prop) [Decidable p] {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (_hu : IsArchSmooth3 u) :
    archDeriv i j (if p then u else 0) = if p then archDeriv i j u else 0 := by
  split_ifs <;> simp [archDeriv_zero]

private theorem isArchSmooth3_ite (p : Prop) [Decidable p] {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u) :
    IsArchSmooth3 (if p then u else 0) := by
  split_ifs
  · exact hu
  · exact isArchSmooth3_zero

private theorem casimir2_eq (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    casimir2 u = ∑ i : Fin 3, ∑ j : Fin 3, archDeriv i j (archDeriv j i u) := by
  funext g
  simp [casimir2, Finset.sum_apply]

private theorem casimir3_eq (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    casimir3 u = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, archDeriv i j (archDeriv j k (archDeriv k i u)) := by
  funext g
  simp [casimir3, Finset.sum_apply]

private theorem isArchSmooth3_casimir2 {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u)
    : IsArchSmooth3 (casimir2 u) := by
  rw [casimir2_eq]
  exact isArchSmooth3_sum _ fun i _ => isArchSmooth3_sum _ fun j _ =>
    isArchSmooth3_archDeriv (isArchSmooth3_archDeriv hu j i) i j

private theorem isArchSmooth3_casimir3 {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u)
    : IsArchSmooth3 (casimir3 u) := by
  rw [casimir3_eq]
  exact isArchSmooth3_sum _ fun i _ => isArchSmooth3_sum _ fun j _ => isArchSmooth3_sum _ fun k _ =>
    isArchSmooth3_archDeriv (isArchSmooth3_archDeriv (isArchSmooth3_archDeriv hu k i) j k) i j

private theorem isArchSmooth3_casimir2_iterate {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u) (m : ℕ) :
    IsArchSmooth3 (casimir2^[m] u) := by
  induction m generalizing u with
  | zero => exact hu
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    exact ih (isArchSmooth3_casimir2 hu)

private theorem isArchSmooth3_casimir3_iterate {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u) (m : ℕ) :
    IsArchSmooth3 (casimir3^[m] u) := by
  induction m generalizing u with
  | zero => exact hu
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    exact ih (isArchSmooth3_casimir3 hu)

private theorem archDeriv_archDeriv_archDeriv_comm {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u)
    (a b i j k : Fin 3) :
    archDeriv a b (archDeriv i j (archDeriv j k u)) =
      archDeriv i j (archDeriv j k (archDeriv a b u)) +
        ((if b = i then archDeriv a j (archDeriv j k u) else 0)
          - (if j = a then archDeriv i b (archDeriv j k u) else 0)) +
        ((if b = j then archDeriv i j (archDeriv a k u) else 0)
          - (if k = a then archDeriv i j (archDeriv j b u) else 0)) := by
  have hjk : IsArchSmooth3 (archDeriv j k u) := isArchSmooth3_archDeriv hu j k
  have hab : IsArchSmooth3 (archDeriv a b u) := isArchSmooth3_archDeriv hu a b
  have s1 : IsArchSmooth3 (archDeriv j k (archDeriv a b u)) := isArchSmooth3_archDeriv hab j k
  have s2 : IsArchSmooth3 (if b = j then archDeriv a k u else 0) :=
    isArchSmooth3_ite _ (isArchSmooth3_archDeriv hu a k)
  have s3 : IsArchSmooth3 (if k = a then archDeriv j b u else 0) :=
    isArchSmooth3_ite _ (isArchSmooth3_archDeriv hu j b)
  rw [archDeriv_comm hjk a b i j, archDeriv_comm hu a b j k, archDeriv_sub i j (isArchSmooth3_add s1 s2) s3,
    archDeriv_add i j s1 s2, archDeriv_ite i j _ (isArchSmooth3_archDeriv hu a k),
    archDeriv_ite i j _ (isArchSmooth3_archDeriv hu j b)]
  abel

private theorem casimir2_archDeriv {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u) (a b : Fin 3) :
    casimir2 (archDeriv a b u) = archDeriv a b (casimir2 u) := by
  have hsm : ∀ i j : Fin 3, IsArchSmooth3 (archDeriv i j (archDeriv j i u)) := fun i j =>
    isArchSmooth3_archDeriv (isArchSmooth3_archDeriv hu j i) i j
  rw [casimir2_eq, casimir2_eq, archDeriv_sum a b _ fun i _ => isArchSmooth3_sum _ fun j _ => hsm i j]
  simp_rw [archDeriv_sum a b _ fun j _ => hsm _ j]

  have key : ∀ i j : Fin 3, archDeriv a b (archDeriv i j (archDeriv j i u)) =
      archDeriv i j (archDeriv j i (archDeriv a b u)) +
        ((if b = i then archDeriv a j (archDeriv j i u) else 0)
          - (if j = a then archDeriv i b (archDeriv j i u) else 0)) +
        ((if b = j then archDeriv i j (archDeriv a i u) else 0)
          - (if i = a then archDeriv i j (archDeriv j b u) else 0)) :=
    fun i j => archDeriv_archDeriv_archDeriv_comm hu a b i j i
  simp_rw [key, Finset.sum_add_distrib, Finset.sum_sub_distrib]

  have c1 : (∑ i : Fin 3, ∑ j : Fin 3, if b = i then archDeriv a j (archDeriv j i u) else 0) =
      ∑ j : Fin 3, archDeriv a j (archDeriv j b u) := by
    simp [Finset.sum_ite_eq]
  have c2 : (∑ i : Fin 3, ∑ j : Fin 3, if j = a then archDeriv i b (archDeriv j i u) else 0) =
      ∑ i : Fin 3, archDeriv i b (archDeriv a i u) := by
    simp [Finset.sum_ite_eq']
  have c3 : (∑ i : Fin 3, ∑ j : Fin 3, if b = j then archDeriv i j (archDeriv a i u) else 0) =
      ∑ i : Fin 3, archDeriv i b (archDeriv a i u) := by
    simp [Finset.sum_ite_eq]
  have c4 : (∑ i : Fin 3, ∑ j : Fin 3, if i = a then archDeriv i j (archDeriv j b u) else 0) =
      ∑ j : Fin 3, archDeriv a j (archDeriv j b u) := by
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq']
  rw [c1, c2, c3, c4]
  abel

private theorem casimir3_archDeriv {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u) (a b : Fin 3) :
    casimir3 (archDeriv a b u) = archDeriv a b (casimir3 u) := by
  have hsm : ∀ i j k : Fin 3, IsArchSmooth3 (archDeriv i j (archDeriv j k (archDeriv k i u))) := fun i j k =>
    isArchSmooth3_archDeriv (isArchSmooth3_archDeriv (isArchSmooth3_archDeriv hu k i) j k) i j
  rw [casimir3_eq, casimir3_eq,
    archDeriv_sum a b _ fun i _ => isArchSmooth3_sum _ fun j _ => isArchSmooth3_sum _ fun k _ => hsm i j k]
  simp_rw [archDeriv_sum a b _ fun j _ => isArchSmooth3_sum _ fun k _ => hsm _ j k,
    archDeriv_sum a b _ fun k _ => hsm _ _ k]

  have key : ∀ i j k : Fin 3, archDeriv a b (archDeriv i j (archDeriv j k (archDeriv k i u))) =
      archDeriv i j (archDeriv j k (archDeriv k i (archDeriv a b u))) +
        ((if b = i then archDeriv a j (archDeriv j k (archDeriv k i u)) else 0) -
          (if j = a then archDeriv i b (archDeriv j k (archDeriv k i u)) else 0)) +
        ((if b = j then archDeriv i j (archDeriv a k (archDeriv k i u)) else 0) -
          (if k = a then archDeriv i j (archDeriv j b (archDeriv k i u)) else 0)) +
        ((if b = k then archDeriv i j (archDeriv j k (archDeriv a i u)) else 0) -
          (if i = a then archDeriv i j (archDeriv j k (archDeriv k b u)) else 0)) := by
    intro i j k
    have hki : IsArchSmooth3 (archDeriv k i u) := isArchSmooth3_archDeriv hu k i
    have hab : IsArchSmooth3 (archDeriv a b u) := isArchSmooth3_archDeriv hu a b
    have s1 : IsArchSmooth3 (archDeriv k i (archDeriv a b u)) := isArchSmooth3_archDeriv hab k i
    have s2 : IsArchSmooth3 (if b = k then archDeriv a i u else 0) :=
      isArchSmooth3_ite _ (isArchSmooth3_archDeriv hu a i)
    have s3 : IsArchSmooth3 (if i = a then archDeriv k b u else 0) :=
      isArchSmooth3_ite _ (isArchSmooth3_archDeriv hu k b)
    have t1 : IsArchSmooth3 (archDeriv j k (archDeriv k i (archDeriv a b u))) := isArchSmooth3_archDeriv s1 j k
    have t2 : IsArchSmooth3 (if b = k then archDeriv j k (archDeriv a i u) else 0) :=
      isArchSmooth3_ite _ (isArchSmooth3_archDeriv (isArchSmooth3_archDeriv hu a i) j k)
    have t3 : IsArchSmooth3 (if i = a then archDeriv j k (archDeriv k b u) else 0) :=
      isArchSmooth3_ite _ (isArchSmooth3_archDeriv (isArchSmooth3_archDeriv hu k b) j k)
    rw [archDeriv_archDeriv_archDeriv_comm hki a b i j k, archDeriv_comm hu a b k i,
      archDeriv_sub j k (isArchSmooth3_add s1 s2) s3, archDeriv_add j k s1 s2,
      archDeriv_ite j k _ (isArchSmooth3_archDeriv hu a i), archDeriv_ite j k _ (isArchSmooth3_archDeriv hu k b),
      archDeriv_sub i j (isArchSmooth3_add t1 t2) t3, archDeriv_add i j t1 t2,
      archDeriv_ite i j _ (isArchSmooth3_archDeriv (isArchSmooth3_archDeriv hu a i) j k),
      archDeriv_ite i j _ (isArchSmooth3_archDeriv (isArchSmooth3_archDeriv hu k b) j k)]
    abel
  simp_rw [key, Finset.sum_add_distrib, Finset.sum_sub_distrib]

  have c1 : (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      if b = i then archDeriv a j (archDeriv j k (archDeriv k i u)) else 0) =
      ∑ j : Fin 3, ∑ k : Fin 3, archDeriv a j (archDeriv j k (archDeriv k b u)) := by
    simp [Finset.sum_ite_eq]
  have c2 : (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      if j = a then archDeriv i b (archDeriv j k (archDeriv k i u)) else 0) =
      ∑ i : Fin 3, ∑ k : Fin 3, archDeriv i b (archDeriv a k (archDeriv k i u)) := by
    simp [Finset.sum_ite_eq']
  have c3 : (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      if b = j then archDeriv i j (archDeriv a k (archDeriv k i u)) else 0) =
      ∑ i : Fin 3, ∑ k : Fin 3, archDeriv i b (archDeriv a k (archDeriv k i u)) := by
    simp [Finset.sum_ite_eq]
  have c4 : (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      if k = a then archDeriv i j (archDeriv j b (archDeriv k i u)) else 0) =
      ∑ i : Fin 3, ∑ j : Fin 3, archDeriv i j (archDeriv j b (archDeriv a i u)) := by
    simp [Finset.sum_ite_eq']
  have c5 : (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      if b = k then archDeriv i j (archDeriv j k (archDeriv a i u)) else 0) =
      ∑ i : Fin 3, ∑ j : Fin 3, archDeriv i j (archDeriv j b (archDeriv a i u)) := by
    simp [Finset.sum_ite_eq]
  have c6 : (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      if i = a then archDeriv i j (archDeriv j k (archDeriv k b u)) else 0) =
      ∑ j : Fin 3, ∑ k : Fin 3, archDeriv a j (archDeriv j k (archDeriv k b u)) := by
    simp [Finset.sum_ite_eq']
  rw [c1, c2, c3, c4, c5, c6]
  abel

private theorem casimir2_iterate_archDeriv {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u) (a b : Fin 3) (m : ℕ) :
    casimir2^[m] (archDeriv a b u) = archDeriv a b (casimir2^[m] u) := by
  induction m generalizing u with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, casimir2_archDeriv hu,
      ih (isArchSmooth3_casimir2 hu)]

private theorem casimir3_iterate_archDeriv {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u) (a b : Fin 3) (m : ℕ) :
    casimir3^[m] (archDeriv a b u) = archDeriv a b (casimir3^[m] u) := by
  induction m generalizing u with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, casimir3_archDeriv hu,
      ih (isArchSmooth3_casimir3 hu)]

private theorem sum_smul_casimir2_iterate_archDeriv {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u) (a b : Fin 3)
    {N : ℕ} (c : Fin (N + 1) → ℂ) (h : ∑ m, c m • (casimir2^[m] u) = 0) :
    ∑ m, c m • (casimir2^[m] (archDeriv a b u)) = 0 := by
  simp_rw [casimir2_iterate_archDeriv hu a b]
  have hsm : ∀ m : Fin (N + 1), IsArchSmooth3 (casimir2^[m] u) := fun m => isArchSmooth3_casimir2_iterate hu m
  have h1 : (∑ m : Fin (N + 1), c m • archDeriv a b (casimir2^[m] u)) =
      archDeriv a b (∑ m, c m • (casimir2^[m] u)) := by
    rw [archDeriv_sum a b _ fun m _ => isArchSmooth3_smul _ (hsm m)]
    exact Finset.sum_congr rfl fun m _ => (archDeriv_smul a b (c m) (hsm m)).symm
  rw [h1, h, archDeriv_zero]

private theorem sum_smul_casimir3_iterate_archDeriv {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u) (a b : Fin 3)
    {N : ℕ} (c : Fin (N + 1) → ℂ) (h : ∑ m, c m • (casimir3^[m] u) = 0) :
    ∑ m, c m • (casimir3^[m] (archDeriv a b u)) = 0 := by
  simp_rw [casimir3_iterate_archDeriv hu a b]
  have hsm : ∀ m : Fin (N + 1), IsArchSmooth3 (casimir3^[m] u) := fun m => isArchSmooth3_casimir3_iterate hu m
  have h1 : (∑ m : Fin (N + 1), c m • archDeriv a b (casimir3^[m] u)) =
      archDeriv a b (∑ m, c m • (casimir3^[m] u)) := by
    rw [archDeriv_sum a b _ fun m _ => isArchSmooth3_smul _ (hsm m)]
    exact Finset.sum_congr rfl fun m _ => (archDeriv_smul a b (c m) (hsm m)).symm
  rw [h1, h, archDeriv_zero]

private theorem adArray_oneArray (k : AdelicGL 3 (𝓞 ℚ) ℚ) : adArray k oneArray = oneArray := by
  have h1 : Matrix.of oneArray = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext a b
    simp [oneArray, Matrix.one_apply]
  funext a b
  show (realMat (archComponent3 (𝓞 ℚ) ℚ k)⁻¹ * Matrix.of oneArray * realMat (archComponent3 (𝓞 ℚ) ℚ k)) a b =
    oneArray a b
  rw [h1, Matrix.mul_one, ← realMat_mul, inv_mul_cancel, realMat_one]
  simp [oneArray, Matrix.one_apply]

private def adCoeff (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i j a b : Fin 3) : ℝ := adArray k⁻¹ (elemArray i j) a b

private theorem array_eq_sum_elemArray (v : Fin 3 → Fin 3 → ℝ)
    : v = ∑ a : Fin 3, ∑ b : Fin 3, v a b • elemArray a b := by
  funext x y
  simp [elemArray, Finset.sum_apply, ite_and]

private theorem mul_archRealLift3_eq (k : AdelicGL 3 (𝓞 ℚ) ℚ) {e : Fin 3 → Fin 3 → ℝ} (he : e ∈ invertibleSet) :
    k * archRealLift3 e = archRealLift3 (adArray k⁻¹ e) * k := by
  rw [← inv_mul_archRealLift3_mul k⁻¹ he, inv_inv, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]

private theorem archDeriv_mul_right {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u) (i j : Fin 3)
    (k g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archDeriv i j u (g * k) =
      ∑ a : Fin 3, ∑ b : Fin 3, (adCoeff k i j a b : ℂ) * archDeriv a b (fun h => u (h * k)) g := by
  have hvs : IsArchSmooth3 fun h => u (h * k) := isArchSmooth3_mul_right hu k

  have hev : (fun s : ℝ => chart u (g * k) (oneArray + s • elemArray i j)) =ᶠ[nhds 0]
      fun s : ℝ => chart (fun h => u (h * k)) g (oneArray + s • adArray k⁻¹ (elemArray i j)) := by
    filter_upwards [eventually_line_mem_invertibleSet (elemArray i j)] with s hs
    simp only [chart]
    rw [mul_assoc, mul_archRealLift3_eq k hs, ← mul_assoc]
    congr 3
    have hlin := (adArrayL k⁻¹).map_add oneArray (s • elemArray i j)
    simp only [adArrayL_apply, map_smul, adArray_oneArray] at hlin
    rw [hlin]
  have hdiff : DifferentiableAt ℝ (chart (fun h => u (h * k)) g) oneArray :=
    (contDiffAt_chart hvs g oneArray_mem_invertibleSet).differentiableAt (by simp)
  rw [archDeriv_apply, hev.deriv_eq, deriv_comp_line hdiff, array_eq_sum_elemArray (adArray k⁻¹ (elemArray i j)),
    map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, archDeriv_apply_eq_fderiv_oneArray hvs a b g, adCoeff, Complex.real_smul]
  rfl

end LanglandsTunnell.CubicInduction.ArchCalculus
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"

open LanglandsTunnell.CubicInduction.ArchCalculus

open IsDedekindDomain NumberField AutomorphicForm WhittakerBlock LanglandsTunnell.CubicInduction.WhittakerBlock

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv WhittakerBlock.casimir2 WhittakerBlock.casimir3 AdelicGL globalPointsGL centralScalarGL upperUnipotent3 componentAt3 archComponent3 whittaker3 orth3 whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open ArchCalculus

section Words

private def W (w : List (Fin 3 × Fin 3)) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ :=
  List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) u w

private theorem W_eq (w : List (Fin 3 × Fin 3)) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    W w u = List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) u w := rfl

@[scoped simp] private theorem W_nil (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : W [] u = u := rfl

@[scoped simp] private theorem W_cons (ij : Fin 3 × Fin 3) (w : List (Fin 3 × Fin 3)) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    W (ij :: w) u = archDeriv ij.1 ij.2 (W w u) := rfl

private theorem W_append (w₁ w₂ : List (Fin 3 × Fin 3)) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : W (w₁ ++ w₂) u = W w₁ (W w₂ u)
    := by
  simp only [W, List.foldr_append]

private theorem isArchSmooth3_W (w : List (Fin 3 × Fin 3)) {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u) :
    IsArchSmooth3 (W w u) := by
  induction w with
  | nil => exact hu
  | cons ij w ih => exact isArchSmooth3_archDeriv ih ij.1 ij.2

private theorem W_smul (w : List (Fin 3 × Fin 3)) (c : ℂ) {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u) :
    W w (c • u) = c • W w u := by
  induction w with
  | nil => rfl
  | cons ij w ih => rw [W_cons, W_cons, ih, archDeriv_smul ij.1 ij.2 c (isArchSmooth3_W w hu)]

private theorem W_sum (w : List (Fin 3 × Fin 3)) {ι : Type*} (s : Finset ι) {f : ι → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hf : ∀ l ∈ s, IsArchSmooth3 (f l)) : W w (∑ l ∈ s, f l) = ∑ l ∈ s, W w (f l) := by
  induction w with
  | nil => rfl
  | cons ij w ih =>
    rw [W_cons, ih, archDeriv_sum ij.1 ij.2 s fun l hl => isArchSmooth3_W w (hf l hl)]
    rfl

private theorem W_sum_smul (w : List (Fin 3 × Fin 3)) {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    {f : ι → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hf : ∀ l ∈ s, IsArchSmooth3 (f l)) :
    W w (∑ l ∈ s, c l • f l) = ∑ l ∈ s, c l • W w (f l) := by
  rw [W_sum w s fun l hl => isArchSmooth3_smul (c l) (hf l hl)]
  exact Finset.sum_congr rfl fun l hl => W_smul w (c l) (hf l hl)

private theorem casimir2_iterate_W (w : List (Fin 3 × Fin 3)) {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u)
    (m : ℕ) :
    casimir2^[m] (W w u) = W w (casimir2^[m] u) := by
  induction w with
  | nil => rfl
  | cons ij w ih => rw [W_cons, casimir2_iterate_archDeriv (isArchSmooth3_W w hu) ij.1 ij.2 m, ih, W_cons]

private theorem casimir3_iterate_W (w : List (Fin 3 × Fin 3)) {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : IsArchSmooth3 u)
    (m : ℕ) :
    casimir3^[m] (W w u) = W w (casimir3^[m] u) := by
  induction w with
  | nil => rfl
  | cons ij w ih => rw [W_cons, casimir3_iterate_archDeriv (isArchSmooth3_W w hu) ij.1 ij.2 m, ih, W_cons]

private theorem sum_smul_casimir2_iterate_W (w : List (Fin 3 × Fin 3)) {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hu : IsArchSmooth3 u)
    {N : ℕ} (a : Fin (N + 1) → ℂ) (h : ∑ m, a m • (casimir2^[m] u) = 0) : ∑ m, a m • (casimir2^[m] (W w u)) = 0 := by
  simp_rw [casimir2_iterate_W w hu]
  rw [← W_sum_smul w Finset.univ a fun m _ => isArchSmooth3_casimir2_iterate hu m, h]
  clear h
  induction w with
  | nil => rfl
  | cons ij w ih => rw [W_cons, ih, archDeriv_zero]

private theorem sum_smul_casimir3_iterate_W (w : List (Fin 3 × Fin 3)) {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hu : IsArchSmooth3 u)
    {N : ℕ} (a : Fin (N + 1) → ℂ) (h : ∑ m, a m • (casimir3^[m] u) = 0) : ∑ m, a m • (casimir3^[m] (W w u)) = 0 := by
  simp_rw [casimir3_iterate_W w hu]
  rw [← W_sum_smul w Finset.univ a fun m _ => isArchSmooth3_casimir3_iterate hu m, h]
  clear h
  induction w with
  | nil => rfl
  | cons ij w ih => rw [W_cons, ih, archDeriv_zero]

end Words
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"

section Frame

private theorem exists_finset_translates_span {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => u (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) :
    ∃ t : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      (∀ φ ∈ t, ∃ k : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) ∧
        archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧ φ = fun g => u (g * k)) ∧
      ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => u (g * k)) ∈ Submodule.span ℂ (t : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) := by
  obtain ⟨s, hs⟩ := hKf

  let T : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :=
    {φ | ∃ k : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) ∧
      archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧ φ = fun g => u (g * k)}
  have hTle : Submodule.span ℂ T ≤ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) := by
    rw [Submodule.span_le]
    rintro φ ⟨k, hkf, hka, rfl⟩
    exact hs k hkf hka
  haveI : Module.Finite ℂ (Submodule.span ℂ T) := Submodule.finiteDimensional_of_le hTle
  obtain ⟨t, htT, -, htspan, -⟩ := Submodule.exists_finset_span_eq_linearIndepOn ℂ T
  refine ⟨t, fun φ hφ => htT hφ, fun k hkf hka => ?_⟩
  rw [htspan]
  exact Submodule.subset_span ⟨k, hkf, hka, rfl⟩

private theorem exists_eq_sum_of_mem_span_finset {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} {t : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)}
    (h : φ ∈ Submodule.span ℂ (t : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) :
    ∃ c : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ℂ, φ = ∑ ψ ∈ t, c ψ • ψ := by
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp h
  exact ⟨c, hc.symm⟩

end Frame
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"

open Matrix IsDedekindDomain NumberField AutomorphicForm AutomorphicForm.StandardKernel WhittakerBlock
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.WhittakerBlock"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv WhittakerBlock.casimir2 WhittakerBlock.casimir3 AdelicGL globalPointsGL centralScalarGL upperUnipotent3 componentAt3 archComponent3 whittaker3 orth3 whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3"
namespace Bridge
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private abbrev P3 : CarrierPins ℚ := productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)

private abbrev ψQ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ := NumberField.StandardAddChar.psiQ

private def realRestr (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : RealGL3.M3 → ℂ := fun x => f (archRealLift3 x)

private theorem contDiffOn_realRestr {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hs : IsArchSmooth3 f) :
    ContDiffOn ℝ (⊤ : ℕ∞) (realRestr f) RealGL3.GLs := by
  have h := hs 1
  simp only [one_mul] at h
  exact h

private theorem mem_invertibleSet_of_mem_GLs {x : RealGL3.M3} (hx : x ∈ RealGL3.GLs) : x ∈ invertibleSet := hx

private theorem archMat_eq_map (x : RealGL3.M3) : archMat x = x.map ofRealHom := rfl

private theorem archRealLift3_eq_archInclN {x : RealGL3.M3} (hx : x ∈ RealGL3.GLs) :
    archRealLift3 x = archInclN (Fin 3) ℚ (archUnit x (mem_invertibleSet_of_mem_GLs hx)) :=
  archRealLift3_eq x (mem_invertibleSet_of_mem_GLs hx)

private theorem archRealLift3_eq_one_or_exists (x : RealGL3.M3) :
    archRealLift3 x = 1 ∨ ∃ u : GL (Fin 3) (InfiniteAdeleRing ℚ),
      (u : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) = archMat x ∧ archRealLift3 x = archInclN (Fin 3) ℚ u := by
  by_cases h : IsUnit (archRealMat3 x)
  · right
    have hu : IsUnit (archMat x) := by
      have := h.map (RingHom.mapMatrix (AdelicLevel.adeleArch (𝓞 ℚ) ℚ))
      rwa [RingHom.mapMatrix_apply, archRealMat3_eq, map_adeleArch_archMatrixInclN] at this
    refine ⟨hu.unit, hu.unit_spec, ?_⟩
    rw [archRealLift3, dif_pos h]
    apply Units.ext
    show archRealMat3 x = archMatrixInclN (Fin 3) ℚ (hu.unit : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))
    rw [hu.unit_spec, archRealMat3_eq]
  · left
    rw [archRealLift3, dif_neg h]

private theorem archComponent3_archInclN (u : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    archComponent3 (𝓞 ℚ) ℚ (archInclN (Fin 3) ℚ u) = u :=
  archComponentN_archInclN (Fin 3) ℚ u

private theorem componentAt3_archInclN (p : HeightOneSpectrum (𝓞 ℚ)) (u : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ p (archInclN (Fin 3) ℚ u) = 1 :=
  componentAtN_archInclN (Fin 3) ℚ p u

private theorem realMat_archUnit {x : RealGL3.M3} (hx : x ∈ RealGL3.GLs) :
    realMat (archUnit x (mem_invertibleSet_of_mem_GLs hx)) = x := by
  rw [realMat_eq, coe_archUnit, archMat_eq_map, Matrix.map_map]
  ext i j
  simp only [Matrix.map_apply, Function.comp_apply, ofRealHom_apply, realCoord_ofReal]

private theorem archComponent3_archRealLift3_of_mem {x : RealGL3.M3} (hx : x ∈ RealGL3.GLs) :
    archComponent3 (𝓞 ℚ) ℚ (archRealLift3 x) = archUnit x (mem_invertibleSet_of_mem_GLs hx) := by
  rw [archRealLift3_eq_archInclN hx, archComponent3_archInclN]

private theorem archUnit_mul {x k : RealGL3.M3} (hx : x ∈ RealGL3.GLs) (hk : k ∈ RealGL3.GLs)
    (hxk : x * k ∈ RealGL3.GLs) :
    archUnit (x * k) (mem_invertibleSet_of_mem_GLs hxk) =
      archUnit x (mem_invertibleSet_of_mem_GLs hx) * archUnit k (mem_invertibleSet_of_mem_GLs hk) := by
  apply Units.ext
  rw [Units.val_mul, coe_archUnit, coe_archUnit, coe_archUnit, archMat_eq_map, archMat_eq_map, archMat_eq_map,
    Matrix.map_mul]

private theorem _root_.LanglandsTunnell.CubicInduction.Bridge.mul_mem_GLs {x k : RealGL3.M3} (hx : x ∈ RealGL3.GLs) (hk : k ∈ RealGL3.GLs) : x * k ∈ RealGL3.GLs :=
    by
  show (x * k).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero hx hk

p2m_export "LanglandsTunnell.CubicInduction.Bridge" "mul_mem_GLs"
private theorem archInclN_mul_comm_of_archComponent3_eq_one {h : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hh : archComponent3 (𝓞 ℚ) ℚ h = 1)
    (u : GL (Fin 3) (InfiniteAdeleRing ℚ)) : archInclN (Fin 3) ℚ u * h = h * archInclN (Fin 3) ℚ u := by
  have harch : (h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) = 1 := by
    rw [map_adeleArch_val, hh, Units.val_one]
  have hu : (archInclN (Fin 3) ℚ u : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      archMatrixInclN (Fin 3) ℚ (u : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) := rfl
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hu]
  refine matrix_ext_of_arch_fin ?_ ?_
  · rw [Matrix.map_mul, Matrix.map_mul, harch, map_adeleArch_archMatrixInclN, Matrix.mul_one, Matrix.one_mul]
  · rw [Matrix.map_mul, Matrix.map_mul, map_adeleFin_archMatrixInclN, Matrix.mul_one, Matrix.one_mul]

private theorem archRealLift3_mul_comm_of_archComponent3_eq_one {h : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hh : archComponent3 (𝓞 ℚ) ℚ h = 1) (x : RealGL3.M3) : archRealLift3 x * h = h * archRealLift3 x := by
  rcases archRealLift3_eq_one_or_exists x with h1 | ⟨u, -, hu⟩
  · rw [h1, one_mul, mul_one]
  · rw [hu]
    exact archInclN_mul_comm_of_archComponent3_eq_one hh u

private theorem archRealLift3_mul_of_mem {x k : RealGL3.M3} (hx : x ∈ RealGL3.GLs) (hk : k ∈ RealGL3.GLs) :
    archRealLift3 (x * k) = archRealLift3 x * archRealLift3 k := by
  rw [archRealLift3_eq_archInclN (mul_mem_GLs hx hk), archRealLift3_eq_archInclN hx, archRealLift3_eq_archInclN hk,
    archUnit_mul hx hk (mul_mem_GLs hx hk), map_mul]

private theorem one_add_smul_E_eq (a b : Fin 3) (s : ℝ) :
    (1 + s • RealGL3.E a b : RealGL3.M3) =
      fun i j => (if i = j then (1 : ℝ) else 0) + if i = a ∧ j = b then s else 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.single_apply, smul_eq_mul]
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · have h' : ¬(a = i ∧ b = j) := fun h'' => h ⟨h''.1.symm, h''.2.symm⟩
    simp [h, h']

private theorem eventually_one_add_smul_E_mem_GLs (a b : Fin 3) :
    ∀ᶠ s : ℝ in nhds 0, (1 + s • RealGL3.E a b : RealGL3.M3) ∈ RealGL3.GLs := by
  have hc : Continuous fun s : ℝ => (1 + s • RealGL3.E a b : RealGL3.M3).det :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have h0 : (1 + (0 : ℝ) • RealGL3.E a b : RealGL3.M3).det = 1 := by simp
  exact hc.continuousAt.eventually_ne (by rw [h0]; exact one_ne_zero)

private theorem rD_realRestr (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (a b : Fin 3) {x : RealGL3.M3}
    (hx : x ∈ RealGL3.GLs) : RealGL3.rD (RealGL3.E a b) (realRestr f) x = archDeriv a b f (archRealLift3 x) := by
  have hev : (fun s : ℝ => realRestr f (x * (1 + s • RealGL3.E a b))) =ᶠ[nhds 0] fun s : ℝ =>
      f (archRealLift3 x *
        archRealLift3 fun i j => (if i = j then (1 : ℝ) else 0) + if i = a ∧ j = b then s else 0) := by
    filter_upwards [eventually_one_add_smul_E_mem_GLs a b] with s hs
    simp only [realRestr]
    rw [archRealLift3_mul_of_mem hx hs, one_add_smul_E_eq]
  unfold RealGL3.rD archDeriv
  exact hev.deriv_eq

private theorem eq_unipArr_of_isUpperUni {n : RealGL3.M3} (hn : RealGL3.IsUpperUni n) :
    n = !![1, n 0 1, n 0 2; 0, 1, n 1 2; 0, 0, 1] := by
  have h10 : n 1 0 = 0 := hn.1 1 0 (by decide)
  have h20 : n 2 0 = 0 := hn.1 2 0 (by decide)
  have h21 : n 2 1 = 0 := hn.1 2 1 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hn.2, h10, h20, h21]

private theorem det_of_isUpperUni {n : RealGL3.M3} (hn : RealGL3.IsUpperUni n) : n.det = 1 := by
  rw [eq_unipArr_of_isUpperUni hn, Matrix.det_fin_three]
  simp

private theorem mem_GLs_of_isUpperUni {n : RealGL3.M3} (hn : RealGL3.IsUpperUni n) : n ∈ RealGL3.GLs := by
  show n.det ≠ 0
  rw [det_of_isUpperUni hn]
  exact one_ne_zero

private def adeleOfReal (r : ℝ) : AdeleRing (𝓞 ℚ) ℚ :=
  ((ofRealHom r, 0) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)

private theorem adeleOfReal_add (r r' : ℝ) : adeleOfReal (r + r') = adeleOfReal r + adeleOfReal r' := by
  show ((ofRealHom (r + r'), (0 : FiniteAdeleRing (𝓞 ℚ) ℚ)) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) =
    (ofRealHom r + ofRealHom r', 0 + 0)
  rw [map_add, add_zero]

private theorem archRealLift3_val_apply {a : RealGL3.M3} (ha : a ∈ RealGL3.GLs) (i j : Fin 3) :
    ((archRealLift3 a : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j =
      ((ofRealHom (a i j), (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) :
        InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) := by
  rw [archRealLift3_eq_archInclN ha]
  rfl

private theorem archRealLift3_eq_upperUnipotent3_of_isUpperUni {n : RealGL3.M3} (hn : RealGL3.IsUpperUni n) :
    archRealLift3 n = upperUnipotent3 (adeleOfReal (n 0 1)) (adeleOfReal (n 1 2)) (adeleOfReal (n 0 2)) := by
  have hn' := eq_unipArr_of_isUpperUni hn
  apply Units.ext
  ext i j
  rw [archRealLift3_val_apply (mem_GLs_of_isUpperUni hn)]
  conv_lhs => rw [hn']
  fin_cases i <;> fin_cases j <;>
    simp [upperUnipotent3, adeleOfReal] <;>
    first
      | exact Prod.ext (map_one ofRealHom) rfl
      | exact Prod.ext (map_zero ofRealHom) rfl

private theorem psiArch_eq_exp_realCoord (x : InfiniteAdeleRing ℚ) :
    NumberField.StandardAddChar.psiArch x = Complex.exp (2 * Real.pi * Complex.I * (realCoord x : ℂ)) := by
  rw [NumberField.StandardAddChar.psiArch_apply,
    finprod_eq_single _ Rat.infinitePlace fun v hv => (hv (Subsingleton.elim v _)).elim,
    NumberField.StandardAddChar.psiArchPlace_apply, realCoord_apply]

private theorem psiQ_adeleOfReal (r : ℝ) : ψQ (adeleOfReal r) = Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) := by
  rw [NumberField.StandardAddChar.psiQ_apply]
  show NumberField.StandardAddChar.psiArch (ofRealHom r) * NumberField.StandardAddChar.psiFin 0 = _
  rw [AddChar.map_zero_eq_one, mul_one, psiArch_eq_exp_realCoord, ofRealHom_apply, realCoord_ofReal]

private theorem whittaker3_archRealLift3_uni_mul (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hinv : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g)
    {n : RealGL3.M3} (hn : RealGL3.IsUpperUni n) {x : RealGL3.M3} (hx : x ∈ RealGL3.GLs) :
    whittaker3 P3 ψQ φ (archRealLift3 (n * x)) =
      Complex.exp (2 * Real.pi * Complex.I * ((n 0 1 + n 1 2 : ℝ) : ℂ)) * whittaker3 P3 ψQ φ (archRealLift3 x) := by
  rw [archRealLift3_mul_of_mem (mem_GLs_of_isUpperUni hn) hx, archRealLift3_eq_upperUnipotent3_of_isUpperUni hn,
    (whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul φ hinv).1, ← adeleOfReal_add,
    psiQ_adeleOfReal]

private theorem whittaker3_mul_right (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 P3 ψQ φ (g * h) = whittaker3 P3 ψQ (fun x => φ (x * h)) g := by
  unfold whittaker3
  simp only [mul_assoc]

private theorem archRealLift3_mul {x k : RealGL3.M3} (hx : x ∈ RealGL3.GLs) (hk : k ∈ RealGL3.GLs) :
    archRealLift3 (x * k) = archRealLift3 x * archRealLift3 k := by
  exact archRealLift3_mul_of_mem hx hk

private theorem componentAt3_archRealLift3 (x : RealGL3.M3) (p : HeightOneSpectrum (𝓞 ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ p (archRealLift3 x) = 1 := by
  rcases archRealLift3_eq_one_or_exists x with h1 | ⟨u, -, hu⟩
  · rw [h1, map_one]
  · rw [hu, componentAt3_archInclN]

private theorem realMat_archComponent3_archRealLift3 {x : RealGL3.M3} (hx : x ∈ RealGL3.GLs) :
    realMat (archComponent3 (𝓞 ℚ) ℚ (archRealLift3 x)) = x := by
  rw [archComponent3_archRealLift3_of_mem hx, realMat_archUnit hx]

private theorem archComponent3_archRealLift3_mem_orth3_iff {x : RealGL3.M3} (hx : x ∈ RealGL3.GLs) :
    archComponent3 (𝓞 ℚ) ℚ (archRealLift3 x) ∈ orth3 ↔ xᵀ * x = 1 := by
  rw [archComponent3_archRealLift3_of_mem hx]
  constructor
  · intro hk
    have h := realMat_orth (k := archUnit x (mem_invertibleSet_of_mem_GLs hx)) hk
    rwa [realMat_archUnit hx] at h
  · intro hxx
    show (archUnit x (mem_invertibleSet_of_mem_GLs hx) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))ᵀ *
      archUnit x (mem_invertibleSet_of_mem_GLs hx) = 1
    rw [coe_archUnit, archMat_eq_map, ← Matrix.transpose_map, ← Matrix.map_mul, hxx,
      Matrix.map_one ofRealHom (map_zero _) (map_one _)]

private theorem archRealLift3_one_matrix : archRealLift3 (1 : RealGL3.M3) = 1 := by
  have h : (1 : RealGL3.M3) = fun a b : Fin 3 => if a = b then (1 : ℝ) else 0 := by
    ext a b
    simp [Matrix.one_apply]
  rw [h]
  exact archRealLift3_one

private theorem mem_GLs_of_orth {k : RealGL3.M3} (hk : kᵀ * k = 1) : k ∈ RealGL3.GLs := by
  show k.det ≠ 0
  intro h0
  have h := congrArg Matrix.det hk
  rw [Matrix.det_mul, Matrix.det_transpose, h0, mul_zero, Matrix.det_one] at h
  exact zero_ne_one h

section FrameCore

variable {G : Type*} {n : ℕ}

private def frameRow (φ : Fin n → G → ℂ) (g : G) : Fin n → ℂ := fun m => φ m g

private theorem span_range_frameRow_eq_top (φ : Fin n → G → ℂ) (hli : LinearIndependent ℂ φ) :
    Submodule.span ℂ (Set.range (frameRow φ)) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)

  set c : Fin n → ℂ := fun m => f fun j => if m = j then (1 : ℂ) else 0 with hc
  have hfx : ∀ x : Fin n → ℂ, f x = ∑ m, x m * c m := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    simp only [hc, smul_eq_mul]
  have hzero : ∑ m, c m • φ m = 0 := by
    funext g
    have h := hf (Submodule.subset_span ⟨g, rfl⟩)
    rw [LinearMap.mem_ker, hfx] at h
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  have hc0 : c = 0 := by
    funext m
    exact Fintype.linearIndependent_iff.1 hli c hzero m
  apply hf0
  refine LinearMap.ext fun x => ?_
  rw [hfx, LinearMap.zero_apply]
  simp [hc0]

private theorem exists_points_det_ne_zero (φ : Fin n → G → ℂ) (hli : LinearIndependent ℂ φ) :
    ∃ pts : Fin n → G, (Matrix.of fun i m => φ m (pts i)).det ≠ 0 := by
  obtain ⟨b, hbr, hbspan, hbli⟩ := exists_linearIndependent ℂ (Set.range (frameRow φ))
  rw [span_range_frameRow_eq_top φ hli] at hbspan

  haveI : Fintype b := Set.Finite.fintype (hbli.setFinite)
  let B : Module.Basis b ℂ (Fin n → ℂ) := Module.Basis.mk hbli (by rw [Subtype.range_val, hbspan])
  have hcard : Fintype.card b = n := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]
  let e : Fin n ≃ b := (Fintype.equivFinOfCardEq hcard).symm

  have hpt : ∀ j : b, ∃ g : G, frameRow φ g = (j : Fin n → ℂ) := fun j => hbr j.2
  choose pt hpt using hpt
  refine ⟨fun i => pt (e i), ?_⟩
  have hrows : LinearIndependent ℂ fun i : Fin n => (Matrix.of fun i m => φ m (pt (e i))) i := by
    have h : (fun i : Fin n => (Matrix.of fun i m => φ m (pt (e i))) i) = fun i => ((e i : b) : Fin n → ℂ) := by
      funext i
      rw [← hpt (e i)]
      rfl
    rw [h]
    exact hbli.comp e e.injective
  exact (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hrows) |>.ne_zero

variable {K : Type*}

private def frameEval (φ : Fin n → G → ℂ) (T : K → G → G) (pts : Fin n → G) (k : K) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i l => φ l (T k (pts i))

private def frameCoeff (φ : Fin n → G → ℂ) (T : K → G → G) (pts : Fin n → G) (k : K) : Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.of fun i m => φ m (pts i))⁻¹ * frameEval φ T pts k

private theorem frameCoeff_expansion (φ : Fin n → G → ℂ) (T : K → G → G) (pts : Fin n → G)
    (hA : (Matrix.of fun i m => φ m (pts i)).det ≠ 0) (k : K)
    (hk : ∀ l, (fun g => φ l (T k g)) ∈ Submodule.span ℂ (Set.range φ)) (l : Fin n) (g : G) :
    φ l (T k g) = ∑ l', frameCoeff φ T pts k l' l * φ l' g := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hk l)

  have hcol : (fun i => frameEval φ T pts k i l) = (Matrix.of fun i m => φ m (pts i)) *ᵥ c := by
    funext i
    have h := congrFun hc (pts i)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    simp only [frameEval, Matrix.of_apply, Matrix.mulVec, dotProduct, ← h]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  have hcoeff : ∀ l', frameCoeff φ T pts k l' l = c l' := by
    intro l'
    have h : frameCoeff φ T pts k l' l =
        ((Matrix.of fun i m => φ m (pts i))⁻¹ *ᵥ fun i => frameEval φ T pts k i l) l' := by
      simp only [frameCoeff, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [h, hcol, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit hA), Matrix.one_mulVec]
  have hg := congrFun hc g
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hg
  rw [← hg]
  exact Finset.sum_congr rfl fun l' _ => by rw [hcoeff]

private theorem frameCoeff_one [Monoid K] (φ : Fin n → G → ℂ) (T : K → G → G) (pts : Fin n → G)
    (hA : (Matrix.of fun i m => φ m (pts i)).det ≠ 0) (hT1 : ∀ g, T 1 g = g) : frameCoeff φ T pts 1 = 1 := by
  have hB : frameEval φ T pts 1 = Matrix.of fun i m => φ m (pts i) := by
    ext i l
    simp [frameEval, hT1]
  rw [frameCoeff, hB, Matrix.nonsing_inv_mul _ (Ne.isUnit hA)]

private theorem frameCoeff_mul [Monoid K] (φ : Fin n → G → ℂ) (T : K → G → G) (pts : Fin n → G)
    (hA : (Matrix.of fun i m => φ m (pts i)).det ≠ 0) (k k' : K) (hTkk' : ∀ g, T (k * k') g = T k' (T k g))
    (hk' : ∀ l, (fun g => φ l (T k' g)) ∈ Submodule.span ℂ (Set.range φ)) :
    frameCoeff φ T pts (k * k') = frameCoeff φ T pts k * frameCoeff φ T pts k' := by
  have hB : frameEval φ T pts (k * k') = frameEval φ T pts k * frameCoeff φ T pts k' := by
    ext i l
    rw [frameEval, Matrix.of_apply, hTkk', frameCoeff_expansion φ T pts hA k' hk' l, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun m _ => by rw [frameEval, Matrix.of_apply, mul_comm]
  rw [frameCoeff, hB, ← Matrix.mul_assoc]
  rfl

end FrameCore
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"

private theorem exists_frame_coeff {n : ℕ} (φ : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hs : ∀ l, IsArchSmooth3 (φ l))
    (hli : LinearIndependent ℂ φ)
    (hstab : ∀ k : RealGL3.M3, kᵀ * k = 1 → ∀ l,
      (fun g => φ l (g * archRealLift3 k)) ∈ Submodule.span ℂ (Set.range φ)) :
    ∃ σt : RealGL3.M3 → Matrix (Fin n) (Fin n) ℂ,
      ContDiffOn ℝ (⊤ : ℕ∞) σt RealGL3.GLs ∧ σt 1 = 1 ∧
      (∀ k k' : RealGL3.M3, kᵀ * k = 1 → k'ᵀ * k' = 1 → σt (k * k') = σt k * σt k') ∧
      ∀ k : RealGL3.M3, kᵀ * k = 1 → ∀ (l : Fin n) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        φ l (g * archRealLift3 k) = ∑ l' : Fin n, σt k l' l * φ l' g := by
  obtain ⟨pts, hA⟩ := exists_points_det_ne_zero φ hli
  refine ⟨frameCoeff (K := RealGL3.M3) φ (fun k g => g * archRealLift3 k) pts, ?_, ?_, ?_, ?_⟩
  ·
    refine contDiffOn_pi.2 fun l' => contDiffOn_pi.2 fun l => ?_
    have hsum : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun k : RealGL3.M3 =>
          ∑ i, (Matrix.of fun i m => φ m (pts i))⁻¹ l' i * φ l (pts i * archRealLift3 k)) RealGL3.GLs :=
      ContDiffOn.sum fun i _ => contDiffOn_const.mul (hs l (pts i))
    refine hsum.congr fun k _ => ?_
    simp only [frameCoeff, frameEval, Matrix.mul_apply, Matrix.of_apply]
  · exact frameCoeff_one (K := RealGL3.M3) φ (fun k g => g * archRealLift3 k) pts hA fun g => by
      show g * archRealLift3 (1 : RealGL3.M3) = g
      rw [archRealLift3_one_matrix, mul_one]
  · intro k k' hk hk'
    refine frameCoeff_mul (K := RealGL3.M3) φ (fun k g => g * archRealLift3 k) pts hA k k' (fun g => ?_)
      (hstab k' hk')
    show g * archRealLift3 (k * k') = g * archRealLift3 k * archRealLift3 k'
    rw [archRealLift3_mul_of_mem (mem_GLs_of_orth hk) (mem_GLs_of_orth hk'), mul_assoc]
  · intro k hk l g
    exact frameCoeff_expansion (K := RealGL3.M3) φ (fun k g => g * archRealLift3 k) pts hA k (hstab k hk) l g

private def ideleOfReal (r : ℝ) (hr : r ≠ 0) : (AdeleRing (𝓞 ℚ) ℚ)ˣ where
  val := ((ofRealHom r, 1) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)
  inv := ((ofRealHom r⁻¹, 1) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)
  val_inv := by
    show ((ofRealHom r * ofRealHom r⁻¹, (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) * 1) :
      InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) = ((1, 1) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)
    rw [← map_mul, mul_inv_cancel₀ hr, map_one, mul_one]
  inv_val := by
    show ((ofRealHom r⁻¹ * ofRealHom r, (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) * 1) :
      InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) = ((1, 1) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)
    rw [← map_mul, inv_mul_cancel₀ hr, map_one, mul_one]

private theorem of_smul_oneArray (r : ℝ) : Matrix.of (r • oneArray) = r • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext a b
  by_cases hab : a = b
  · subst hab; simp [oneArray]
  · simp [oneArray, hab, Matrix.one_apply_ne hab]

private theorem smul_oneArray_mem_invertibleSet {r : ℝ} (hr : r ≠ 0) : r • oneArray ∈ invertibleSet := by
  show (Matrix.of (r • oneArray)).det ≠ 0
  rw [of_smul_oneArray, Matrix.det_smul, Matrix.det_one, mul_one]
  exact pow_ne_zero _ hr

private theorem archRealLift3_entry {e : Fin 3 → Fin 3 → ℝ} (he : e ∈ invertibleSet) (a b : Fin 3) :
    ((archRealLift3 e : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) a b =
      ((ofRealHom (e a b), (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) a b) :
        InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) := by
  rw [archRealLift3_eq e he]
  rfl

private theorem archRealLift3_smul_oneArray {r : ℝ} (hr : r ≠ 0) :
    archRealLift3 (r • oneArray) = centralScalarGL 3 (𝓞 ℚ) ℚ (ideleOfReal r hr) := by
  apply Units.ext
  ext a b
  rw [archRealLift3_entry (smul_oneArray_mem_invertibleSet hr)]
  show ((ofRealHom ((r • oneArray) a b), (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) a b) :
      InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) =
    Matrix.scalar (Fin 3) ((ideleOfReal r hr : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) a b
  rw [Matrix.scalar_apply]
  by_cases hab : a = b
  · subst hab
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    simp only [Pi.smul_apply, oneArray, if_true, smul_eq_mul, mul_one]
    rfl
  · rw [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab]
    simp only [Pi.smul_apply, oneArray, hab, if_false, smul_eq_mul, mul_zero, map_zero]
    rfl

private theorem mul_centralScalarGL_comm (g : AdelicGL 3 (𝓞 ℚ) ℚ) (c : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    g * centralScalarGL 3 (𝓞 ℚ) ℚ c = centralScalarGL 3 (𝓞 ℚ) ℚ c * g := by
  apply Units.ext
  simp only [Units.val_mul]
  exact ((Matrix.scalar_commute (c : AdeleRing (𝓞 ℚ) ℚ) (fun _ => Commute.all _ _) _).symm :
    (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) * Matrix.scalar (Fin 3) (c : AdeleRing (𝓞 ℚ) ℚ) =
      Matrix.scalar (Fin 3) (c : AdeleRing (𝓞 ℚ) ℚ) * g)

private theorem sum_elemArray_diag : ∑ i : Fin 3, elemArray i i = oneArray := by
  funext a b
  simp only [Finset.sum_apply, elemArray, oneArray, Fin.sum_univ_three]
  fin_cases a <;> fin_cases b <;> simp

private theorem exists_forall_sum_archDeriv_diag_eq_mul (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) :
    ∃ cω : ℂ, ∀ Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsArchSmooth3 Φ →
      (∀ (c : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), Φ (centralScalarGL 3 (𝓞 ℚ) ℚ c * g) = (ω c : ℂ) * Φ g) →
      ∀ g, ∑ i : Fin 3, archDeriv i i Φ g = cω * Φ g := by

  let χ : ℝ → ℂ := fun s => if h : (1 + s : ℝ) = 0 then 0 else ((ω (ideleOfReal (1 + s) h) : ℂˣ) : ℂ)
  refine ⟨deriv χ 0, fun Φ hs hω g => ?_⟩
  have hd : DifferentiableAt ℝ (chart Φ g) oneArray :=
    (contDiffAt_chart hs g oneArray_mem_invertibleSet).differentiableAt (by simp)

  have hsum : ∑ i : Fin 3, archDeriv i i Φ g = deriv (fun s : ℝ => chart Φ g (oneArray + s • oneArray)) 0 := by
    have hlin : fderiv ℝ (chart Φ g) oneArray oneArray
        = ∑ i : Fin 3, fderiv ℝ (chart Φ g) oneArray (elemArray i i) := by
      rw [← map_sum, sum_elemArray_diag]
    rw [deriv_comp_line hd, hlin]
    exact Finset.sum_congr rfl fun i _ => by rw [archDeriv_apply, deriv_comp_line hd]

  have hev : (fun s : ℝ => chart Φ g (oneArray + s • oneArray)) =ᶠ[nhds (0 : ℝ)] fun s => χ s * Φ g := by
    filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with s hs1
    have h1 : (1 + s : ℝ) ≠ 0 := by
      have : (0 : ℝ) < 1 + s := by linarith [Set.mem_Ioi.mp hs1]
      exact this.ne'
    have harr : oneArray + s • oneArray = (1 + s) • oneArray := by rw [add_smul, one_smul]
    simp only [chart, harr, χ, dif_neg h1]
    rw [archRealLift3_smul_oneArray h1, mul_centralScalarGL_comm, hω]
  rw [hsum, hev.deriv_eq, deriv_mul_const_field]

open MeasureTheory

private theorem continuous_upperUnipotent3_adele {T : Type*} [TopologicalSpace T] {X Y Z : T → AdeleRing (𝓞 ℚ) ℚ}
    (hX : Continuous X) (hY : Continuous Y) (hZ : Continuous Z) :
    Continuous fun t => (upperUnipotent3 (X t) (Y t) (Z t) : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop
  · have h : ∀ t : T,
        (((upperUnipotent3 (X t) (Y t) (Z t) : AdelicGL 3 (𝓞 ℚ) ℚ)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) :
            Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
          !![1, -X t, X t * Y t - Z t; 0, 1, -Y t; 0, 0, 1] := fun _ => rfl
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem continuous_whittaker3_integrand {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : Continuous φ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    {T : Type*} [TopologicalSpace T] {X Y Z : T → AdeleRing (𝓞 ℚ) ℚ} (hX : Continuous X) (hY : Continuous Y)
    (hZ : Continuous Z) :
    Continuous fun t => φ (upperUnipotent3 (X t) (Y t) (Z t) * g) * ψQ (-(X t + Y t)) := by
  refine (hφ.comp ((continuous_upperUnipotent3_adele hX hY hZ).mul continuous_const)).mul ?_
  exact NumberField.StandardAddChar.continuous_psiQ.comp (by fun_prop)

private theorem secondCountableTopology_finiteAdeleRing : SecondCountableTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  RestrictedProduct.secondCountableTopology fun _ => Valued.isOpen_valuationSubring _

private theorem firstCountableTopology_adeleRing : FirstCountableTopology (AdeleRing (𝓞 ℚ) ℚ) := by
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) := secondCountableTopology_finiteAdeleRing
  haveI : FirstCountableTopology (InfiniteAdeleRing ℚ) :=
    inferInstanceAs (FirstCountableTopology ((v : InfinitePlace ℚ) → v.Completion))
  exact inferInstanceAs (FirstCountableTopology (InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ))

private theorem integrable_of_continuous_pins {f : AdeleRing (𝓞 ℚ) ℚ → ℂ} (hf : Continuous f) :
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := P3.nS
    Integrable f P3.ν := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  show Integrable f (@ProbabilityTheory.cond _ (NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ)
    (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
  obtain ⟨C, hC, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  have hint : IntegrableOn f (AdelicBox.adelicBox ℚ) (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) :=
    (hf.continuousOn.integrableOn_compact hC).mono_set hsub
  rw [ProbabilityTheory.cond]
  exact hint.smul_measure (ENNReal.inv_ne_top.mpr (AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne')

private theorem continuous_integral_pins {Y : Type*} [TopologicalSpace Y] [LocallyCompactSpace Y]
    [FirstCountableTopology Y]
    {F : Y → AdeleRing (𝓞 ℚ) ℚ → ℂ} (hF : Continuous (Function.uncurry F)) :
    letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := P3.nS
    Continuous fun y => ∫ z, F y z ∂P3.ν := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI : IsProbabilityMeasure (@ProbabilityTheory.cond _ (NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ)
      (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)) :=
    AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ
  show Continuous fun y => ∫ z, F y z ∂(@ProbabilityTheory.cond _ (NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ)
    (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
  obtain ⟨C, hC, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  have hae : ∀ᵐ z ∂(@ProbabilityTheory.cond _ (NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ)
      (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)), z ∈ C := by
    rw [ProbabilityTheory.cond]
    exact Measure.ae_smul_measure ((ae_restrict_mem (AdelicBox.measurableSet_adelicBox ℚ)).mono fun z hz => hsub hz) _
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  obtain ⟨K, hK, hKmem⟩ := exists_compact_mem_nhds y₀
  obtain ⟨M, hM⟩ := (hK.prod hC).exists_bound_of_continuousOn hF.continuousOn
  refine continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ (integrable_const M) ?_
  · exact Filter.Eventually.of_forall fun y => (hF.comp (Continuous.prodMk_right y)).aestronglyMeasurable
  · filter_upwards [hKmem] with y hy
    filter_upwards [hae] with z hz
    exact hM (y, z) ⟨hy, hz⟩
  · exact Filter.Eventually.of_forall fun z => (hF.comp (Continuous.prodMk_left z)).continuousAt

private theorem whittaker3_zero_fun (g : AdelicGL 3 (𝓞 ℚ) ℚ) : whittaker3 P3 ψQ (fun _ => (0 : ℂ)) g = 0 := by
  unfold whittaker3
  simp

private theorem whittaker3_add {φ φ' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : Continuous φ) (hφ' : Continuous φ')
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 P3 ψQ (fun x => φ x + φ' x) g = whittaker3 P3 ψQ φ g + whittaker3 P3 ψQ φ' g := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := P3.nS
  haveI : FirstCountableTopology (AdeleRing (𝓞 ℚ) ℚ) := firstCountableTopology_adeleRing

  have hin : ∀ {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}, Continuous u → ∀ x y : AdeleRing (𝓞 ℚ) ℚ,
      Continuous fun z => u (upperUnipotent3 x y z * g) * ψQ (-(x + y)) :=
    fun {u} hu x y => continuous_whittaker3_integrand hu g
      (continuous_const : Continuous fun _ : AdeleRing (𝓞 ℚ) ℚ => x)
      (continuous_const : Continuous fun _ : AdeleRing (𝓞 ℚ) ℚ => y)
      (continuous_id : Continuous fun z : AdeleRing (𝓞 ℚ) ℚ => z)
  have hmid : ∀ {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}, Continuous u → ∀ x : AdeleRing (𝓞 ℚ) ℚ,
      Continuous fun y : AdeleRing (𝓞 ℚ) ℚ => ∫ z, u (upperUnipotent3 x y z * g) * ψQ (-(x + y)) ∂P3.ν :=
    fun {u} hu x => continuous_integral_pins (F := fun y z => u (upperUnipotent3 x y z * g) * ψQ (-(x + y)))
      (continuous_whittaker3_integrand hu g
        (continuous_const : Continuous fun _ : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => x)
        (continuous_fst : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => p.1)
        (continuous_snd : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => p.2))
  have hout : ∀ {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}, Continuous u →
      Continuous fun x : AdeleRing (𝓞 ℚ) ℚ =>
        ∫ y, ∫ z, u (upperUnipotent3 x y z * g) * ψQ (-(x + y)) ∂P3.ν ∂P3.ν :=
    fun {u} hu => continuous_integral_pins
      (F := fun x y => ∫ z, u (upperUnipotent3 x y z * g) * ψQ (-(x + y)) ∂P3.ν)
      (continuous_integral_pins (F := fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => fun z =>
          u (upperUnipotent3 q.1 q.2 z * g) * ψQ (-(q.1 + q.2)))
        (continuous_whittaker3_integrand hu g
          (by fun_prop : Continuous fun p : (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ => p.1.1)
          (by fun_prop : Continuous fun p : (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ => p.1.2)
          (by fun_prop : Continuous fun p : (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) × AdeleRing (𝓞 ℚ) ℚ => p.2)))
  show (∫ x, ∫ y, ∫ z, (φ (upperUnipotent3 x y z * g) + φ' (upperUnipotent3 x y z * g)) * ψQ (-(x + y))
        ∂P3.ν ∂P3.ν ∂P3.ν) =
      (∫ x, ∫ y, ∫ z, φ (upperUnipotent3 x y z * g) * ψQ (-(x + y)) ∂P3.ν ∂P3.ν ∂P3.ν) +
        ∫ x, ∫ y, ∫ z, φ' (upperUnipotent3 x y z * g) * ψQ (-(x + y)) ∂P3.ν ∂P3.ν ∂P3.ν
  have h1 : ∀ x y : AdeleRing (𝓞 ℚ) ℚ,
      (∫ z, (φ (upperUnipotent3 x y z * g) + φ' (upperUnipotent3 x y z * g)) * ψQ (-(x + y)) ∂P3.ν) =
        (∫ z, φ (upperUnipotent3 x y z * g) * ψQ (-(x + y)) ∂P3.ν) +
          ∫ z, φ' (upperUnipotent3 x y z * g) * ψQ (-(x + y)) ∂P3.ν := by
    intro x y
    simp only [add_mul]
    exact integral_add (integrable_of_continuous_pins (hin hφ x y)) (integrable_of_continuous_pins (hin hφ' x y))
  have h2 : ∀ x : AdeleRing (𝓞 ℚ) ℚ,
      (∫ y, ((∫ z, φ (upperUnipotent3 x y z * g) * ψQ (-(x + y)) ∂P3.ν) +
          ∫ z, φ' (upperUnipotent3 x y z * g) * ψQ (-(x + y)) ∂P3.ν) ∂P3.ν) =
        (∫ y, ∫ z, φ (upperUnipotent3 x y z * g) * ψQ (-(x + y)) ∂P3.ν ∂P3.ν) +
          ∫ y, ∫ z, φ' (upperUnipotent3 x y z * g) * ψQ (-(x + y)) ∂P3.ν ∂P3.ν := by
    intro x
    exact integral_add (integrable_of_continuous_pins (hmid hφ x)) (integrable_of_continuous_pins (hmid hφ' x))
  simp_rw [h1, h2]
  exact integral_add (integrable_of_continuous_pins (hout hφ)) (integrable_of_continuous_pins (hout hφ'))

private theorem whittaker3_finset_sum {α : Type*} (s : Finset α) (φ : α → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hc : ∀ a ∈ s, Continuous (φ a)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 P3 ψQ (fun x => ∑ a ∈ s, φ a x) g = ∑ a ∈ s, whittaker3 P3 ψQ (φ a) g := by
  classical
  revert hc
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    exact whittaker3_zero_fun g
  · intro a s ha ih hc
    have hca : Continuous (φ a) := hc a (Finset.mem_insert_self a s)
    have hcs : ∀ b ∈ s, Continuous (φ b) := fun b hb => hc b (Finset.mem_insert_of_mem hb)
    simp only [Finset.sum_insert ha]
    have hadd := whittaker3_add hca (continuous_finsetSum s hcs) g
    rw [hadd, ih hcs]

private theorem whittaker3_const_mul (c : ℂ) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 P3 ψQ (fun x => c * φ x) g = c * whittaker3 P3 ψQ φ g := by
  unfold whittaker3
  simp only [mul_assoc, MeasureTheory.integral_const_mul]

private theorem exists_eq_archRealLift3_mul (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∃ gf : AdelicGL 3 (𝓞 ℚ) ℚ, archComponent3 (𝓞 ℚ) ℚ gf = 1 ∧
      g = archRealLift3 (realMat (archComponent3 (𝓞 ℚ) ℚ g)) * gf := by
  set a := archComponent3 (𝓞 ℚ) ℚ g with ha
  have hx : realMat a ∈ RealGL3.GLs := det_realMat_ne_zero a
  have hlift : archComponent3 (𝓞 ℚ) ℚ (archRealLift3 (realMat a)) = a := by
    rw [archComponent3_archRealLift3_of_mem hx]
    apply Units.ext
    rw [coe_archUnit, archMat_eq_map, realMat_eq, map_realCoord_map_ofRealHom]
  refine ⟨(archRealLift3 (realMat a))⁻¹ * g, ?_, ?_⟩
  · rw [map_mul, map_inv, hlift, ← ha, inv_mul_cancel]
  · rw [mul_inv_cancel_left]

private theorem archDeriv_comp_mul_right_of_archComponent3 {h : AdelicGL 3 (𝓞 ℚ) ℚ} (hh : archComponent3 (𝓞 ℚ) ℚ h = 1)
    (a b : Fin 3) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    archDeriv a b (fun g => φ (g * h)) = fun g => archDeriv a b φ (g * h) := by
  funext g
  simp only [archDeriv, mul_assoc, archRealLift3_mul_comm_of_archComponent3_eq_one hh]

private theorem archDeriv_comp_mul_left (γ : AdelicGL 3 (𝓞 ℚ) ℚ) (a b : Fin 3) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    archDeriv a b (fun g => φ (γ * g)) = fun g => archDeriv a b φ (γ * g) := by
  funext g
  simp only [archDeriv, mul_assoc]

private theorem archRealLift3_mul_comm_of_archComponent3 {h : AdelicGL 3 (𝓞 ℚ) ℚ} (hh : archComponent3 (𝓞 ℚ) ℚ h = 1)
    (x : RealGL3.M3) : archRealLift3 x * h = h * archRealLift3 x := by
  exact archRealLift3_mul_comm_of_archComponent3_eq_one hh x

end LanglandsTunnell.CubicInduction.Bridge
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"

open LanglandsTunnell.CubicInduction.Bridge

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv WhittakerBlock.casimir2 WhittakerBlock.casimir3 AdelicGL globalPointsGL centralScalarGL upperUnipotent3 componentAt3 archComponent3 whittaker3 orth3 whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3"
namespace Datum
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private theorem exists_frame_of_mem {G : Type*} (t : Set (G → ℂ)) (u : G → ℂ) (hu : u ≠ 0) (hut : u ∈ t)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ t)) :
    ∃ (n : ℕ) (b : Fin (n + 1) → (G → ℂ)), b 0 = u ∧ (∀ i, b i ∈ t) ∧ LinearIndependent ℂ b ∧
      ∀ v ∈ t, v ∈ Submodule.span ℂ (Set.range b) := by

  have hu' : LinearIndepOn ℂ id ({u} : Set (G → ℂ)) :=
    LinearIndepOn.singleton (R := ℂ) (v := id) (i := u) (by simpa using hu)
  obtain ⟨e, he_sub, hue', he_span, he_li⟩ :=
    exists_linearIndepOn_id_extension hu' (Set.singleton_subset_iff.2 hut)
  have hue : u ∈ e := hue' (Set.mem_singleton u)

  have he_li' : LinearIndependent ℂ fun x : e => (⟨(x : G → ℂ), Submodule.subset_span (he_sub x.2)⟩ :
      Submodule.span ℂ t) :=
    LinearIndependent.of_comp (Submodule.span ℂ t).subtype he_li
  haveI : Finite e := he_li'.finite_of_isNoetherian
  haveI : Fintype e := Fintype.ofFinite e
  haveI : Nonempty e := ⟨⟨u, hue⟩⟩

  obtain ⟨n, hn⟩ : ∃ n, Fintype.card e = n + 1 := Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  let f : Fin (n + 1) ≃ e := (Fintype.equivFinOfCardEq hn).symm
  let f' : Fin (n + 1) ≃ e := (Equiv.swap (0 : Fin (n + 1)) (f.symm ⟨u, hue⟩)).trans f
  refine ⟨n, fun i => (f' i : G → ℂ), ?_, fun i => he_sub (f' i).2,
    LinearIndependent.comp he_li f' f'.injective, fun v hv => ?_⟩
  · simp [f']
  · have hrange : Set.range (fun i => (f' i : G → ℂ)) = e := by
      rw [Set.range_comp' (fun x : e => (x : G → ℂ)) f', f'.range_eq_univ, Set.image_univ, Subtype.range_coe]
    rw [hrange]
    exact he_span hv

private theorem orth_mul {k k' : RealGL3.M3} (hk : kᵀ * k = 1) (hk' : k'ᵀ * k' = 1) : (k * k')ᵀ * (k * k') = 1 := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc kᵀ, hk, Matrix.one_mul, hk']

private theorem orth_one : (1 : RealGL3.M3)ᵀ * 1 = 1 := by simp

private def tr (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (k : RealGL3.M3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ := fun g => u
    (g * archRealLift3 k)

private theorem tr_one (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : tr u 1 = u := by
  funext g
  simp only [tr, archRealLift3_one_matrix, mul_one]

private theorem exists_real_frame {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu0 : u ≠ 0)
    (hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => u (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) :
    ∃ (n : ℕ) (kb : Fin (n + 1) → RealGL3.M3), (∀ l, (kb l)ᵀ * kb l = 1) ∧ kb 0 = 1 ∧
      LinearIndependent ℂ (fun l => tr u (kb l)) ∧
      ∀ k : RealGL3.M3, kᵀ * k = 1 → ∀ l,
        (fun g => tr u (kb l) (g * archRealLift3 k)) ∈ Submodule.span ℂ (Set.range fun l => tr u (kb l)) := by
  obtain ⟨t, -, ht⟩ := exists_finset_translates_span hKf

  set T : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) := {φ | ∃ k : RealGL3.M3, kᵀ * k = 1 ∧ φ = tr u k} with hT
  have hmemT : ∀ {k : RealGL3.M3}, kᵀ * k = 1 → tr u k ∈ T := fun hk => ⟨_, hk, rfl⟩
  have hTle : Submodule.span ℂ T ≤ Submodule.span ℂ (t : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) := by
    rw [Submodule.span_le]
    rintro φ ⟨k, hk, rfl⟩
    exact ht (archRealLift3 k) (componentAt3_archRealLift3 k)
      ((archComponent3_archRealLift3_mem_orth3_iff (mem_GLs_of_orth hk)).2 hk)
  haveI : FiniteDimensional ℂ (Submodule.span ℂ T) := Submodule.finiteDimensional_of_le hTle
  obtain ⟨n, b, hb0, hbT, hbli, hbspan⟩ :=
    exists_frame_of_mem T u hu0 (by simpa only [tr_one] using hmemT orth_one) inferInstance

  have hbT' : ∀ i, ∃ k : RealGL3.M3, kᵀ * k = 1 ∧ b i = tr u k := fun i => hbT i
  choose kb' hkb' using hbT'
  let kb : Fin (n + 1) → RealGL3.M3 := fun l => if l = 0 then 1 else kb' l
  have hkb_orth : ∀ l, (kb l)ᵀ * kb l = 1 := by
    intro l
    by_cases hl : l = 0
    · simp [kb, hl]
    · simp [kb, hl, (hkb' l).1]
  have hb_eq : (fun l => tr u (kb l)) = b := by
    funext l
    by_cases hl : l = 0
    · subst hl
      simp [kb, tr_one, hb0]
    · simp [kb, hl, (hkb' l).2]
  refine ⟨n, kb, hkb_orth, by simp [kb], ?_, fun k hk l => ?_⟩
  · rw [hb_eq]
    exact hbli
  · rw [hb_eq]
    have htr : (fun g => tr u (kb l) (g * archRealLift3 k)) = tr u (k * kb l) := by
      funext g
      simp only [tr, mul_assoc, Bridge.archRealLift3_mul (mem_GLs_of_orth hk) (mem_GLs_of_orth (hkb_orth l))]
    rw [htr]
    exact hbspan _ (hmemT (orth_mul hk (hkb_orth l)))

end LanglandsTunnell.CubicInduction.Datum
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv WhittakerBlock.casimir2 WhittakerBlock.casimir3 AdelicGL globalPointsGL centralScalarGL upperUnipotent3 componentAt3 archComponent3 whittaker3 orth3 whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3"
namespace Datum
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private def Φt (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ := fun g => u (g * h)

private def W₁ (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) : RealGL3.M3 → ℂ :=
  realRestr (whittaker3 P3 ψQ (Φt u h))

private theorem W₁_apply (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) (x : RealGL3.M3) :
    W₁ u h x = whittaker3 P3 ψQ (Φt u h) (archRealLift3 x) := rfl

private theorem isArchSmooth3_Φt {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hs : IsArchSmooth3 u) (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    IsArchSmooth3 (Φt u h) :=
  isArchSmooth3_mul_right hs h

private theorem W_Φt (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) {h : AdelicGL 3 (𝓞 ℚ) ℚ} (hh : archComponent3 (𝓞 ℚ) ℚ h = 1)
    (w : List (Fin 3 × Fin 3)) : W w (Φt u h) = Φt (W w u) h := by
  induction w with
  | nil => rfl
  | cons ij w ih =>
    rw [W_cons, ih]
    exact archDeriv_comp_mul_right_of_archComponent3 hh ij.1 ij.2 (W w u)

private theorem continuous_W_Φt {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hD : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) u w))
    {h : AdelicGL 3 (𝓞 ℚ) ℚ} (hh : archComponent3 (𝓞 ℚ) ℚ h = 1) (w : List (Fin 3 × Fin 3)) :
    Continuous (List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) (Φt u h) w) := by
  rw [← W_eq, W_Φt u hh w]
  exact (hD w).comp (continuous_mul_const h)

private theorem alpha_Φt {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hD : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) u w))
    (hs : IsArchSmooth3 u) {h : AdelicGL 3 (𝓞 ℚ) ℚ} (hh : archComponent3 (𝓞 ℚ) ℚ h = 1) :
    (∀ w : List (Fin 3 × Fin 3), whittaker3 P3 ψQ (W w (Φt u h)) = W w (whittaker3 P3 ψQ (Φt u h))) ∧
      IsArchSmooth3 (whittaker3 P3 ψQ (Φt u h)) :=
  whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3 (Φt u h) (isArchSmooth3_Φt hs h)
    (continuous_W_Φt hD hh)

private theorem contDiffOn_W₁ {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hD : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) u w))
    (hs : IsArchSmooth3 u) {h : AdelicGL 3 (𝓞 ℚ) ℚ} (hh : archComponent3 (𝓞 ℚ) ℚ h = 1) :
    ContDiffOn ℝ (⊤ : ℕ∞) (W₁ u h) RealGL3.GLs :=
  contDiffOn_realRestr (alpha_Φt hD hs hh).2

private theorem W₁_uni_mul {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hinv : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g)
    (h : AdelicGL 3 (𝓞 ℚ) ℚ) (n' x : RealGL3.M3) (hn : RealGL3.IsUpperUni n') (hx : x ∈ RealGL3.GLs) :
    W₁ u h (n' * x) = RealGL3.uniChar n' * W₁ u h x := by
  have hinv' : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), Φt u h (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = Φt u h g := by
    intro γ g
    simp only [Φt, mul_assoc, hinv]
  exact whittaker3_archRealLift3_uni_mul (Φt u h) hinv' hn hx

private theorem upperUnipotent3_mul_centralScalarGL (x y z : AdeleRing (𝓞 ℚ) ℚ) (c : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    upperUnipotent3 x y z * (centralScalarGL 3 (𝓞 ℚ) ℚ c * g) =
      centralScalarGL 3 (𝓞 ℚ) ℚ c * (upperUnipotent3 x y z * g) := by
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  apply Units.ext
  simp only [Units.val_mul]
  exact ((Matrix.scalar_commute (c : AdeleRing (𝓞 ℚ) ℚ) (fun _ => Commute.all _ _) _).symm :
    (upperUnipotent3 x y z : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) *
        Matrix.scalar (Fin 3) (c : AdeleRing (𝓞 ℚ) ℚ) =
      Matrix.scalar (Fin 3) (c : AdeleRing (𝓞 ℚ) ℚ) * upperUnipotent3 x y z)

private theorem whittaker3_centralScalarGL_mul (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      v (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * v g)
    (c : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 P3 ψQ v (centralScalarGL 3 (𝓞 ℚ) ℚ c * g) = (ω c : ℂ) * whittaker3 P3 ψQ v g := by
  unfold whittaker3
  simp only [upperUnipotent3_mul_centralScalarGL, hcen, mul_assoc, MeasureTheory.integral_const_mul]

private theorem Φt_central {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} {ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ}
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g)
    (h : AdelicGL 3 (𝓞 ℚ) ℚ) (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Φt u h (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * Φt u h g := by
  simp only [Φt, mul_assoc, hcen]

private theorem one_eq_sum_E : (1 : RealGL3.M3) = ∑ i : Fin 3, RealGL3.E i i := by
  ext a b
  rw [Matrix.sum_apply]
  simp only [RealGL3.E, Matrix.single_apply, Matrix.one_apply]
  by_cases hab : a = b
  · subst hab
    simp
  · rw [if_neg hab]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    apply hab
    exact h1.symm.trans h2

private theorem rD_one_W₁ {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hD : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) u w))
    (hs : IsArchSmooth3 u) {ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ}
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g)
    {cω : ℂ} (hcω : ∀ Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsArchSmooth3 Φ →
      (∀ (c : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        Φ (centralScalarGL 3 (𝓞 ℚ) ℚ c * g) = (ω c : ℂ) * Φ g) →
      ∀ g, ∑ i : Fin 3, archDeriv i i Φ g = cω * Φ g)
    {h : AdelicGL 3 (𝓞 ℚ) ℚ} (hh : archComponent3 (𝓞 ℚ) ℚ h = 1) {x : RealGL3.M3} (hx : x ∈ RealGL3.GLs) :
    RealGL3.rD 1 (W₁ u h) x = cω * W₁ u h x := by
  have hdiff : DifferentiableAt ℝ (W₁ u h) x :=
    ((contDiffOn_W₁ hD hs hh).differentiableOn (by simp)).differentiableAt
      (RealGL3.isOpen_GLs.mem_nhds hx)
  rw [one_eq_sum_E, RealGL3.rD_sum_dir _ _ hdiff]
  simp only [W₁, rD_realRestr _ _ _ hx]
  exact hcω _ (alpha_Φt hD hs hh).2 (whittaker3_centralScalarGL_mul (Φt u h) ω (Φt_central hcen h)) _

end LanglandsTunnell.CubicInduction.Datum
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv WhittakerBlock.casimir2 WhittakerBlock.casimir3 AdelicGL globalPointsGL centralScalarGL upperUnipotent3 componentAt3 archComponent3 whittaker3 orth3 whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3"
namespace Datum
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private theorem Φt_mul_lift_eq_sum {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} {n : ℕ} {kb : Fin (n + 1) → RealGL3.M3}
    {σ : RealGL3.M3 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {k : RealGL3.M3}
    (hexp : ∀ (l : Fin (n + 1)) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      tr u (kb l) (g * archRealLift3 k) = ∑ l', σ k l' l * tr u (kb l') g)
    {h : AdelicGL 3 (𝓞 ℚ) ℚ} (hh : archComponent3 (𝓞 ℚ) ℚ h = 1) (l : Fin (n + 1)) :
    (fun g => Φt u h (g * (archRealLift3 k * archRealLift3 (kb l)))) =
      fun g => ∑ l', σ k l' l * Φt u h (g * archRealLift3 (kb l')) := by
  funext g
  have h1 := hexp l (g * h)
  simp only [tr, mul_assoc] at h1
  simp only [Φt, mul_assoc, archRealLift3_mul_comm_of_archComponent3 hh]
  rw [← mul_assoc (archRealLift3 k) h, archRealLift3_mul_comm_of_archComponent3 hh k, mul_assoc h]
  exact h1

private theorem W₁_mul_orth_mul_kb {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hD : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) u w))
    {n : ℕ} {kb : Fin (n + 1) → RealGL3.M3} (hkb : ∀ l, (kb l)ᵀ * kb l = 1)
    {σ : RealGL3.M3 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hσ : ∀ k : RealGL3.M3, kᵀ * k = 1 → ∀ (l : Fin (n + 1)) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      tr u (kb l) (g * archRealLift3 k) = ∑ l', σ k l' l * tr u (kb l') g)
    {h : AdelicGL 3 (𝓞 ℚ) ℚ} (hh : archComponent3 (𝓞 ℚ) ℚ h = 1)
    (x k : RealGL3.M3) (hx : x ∈ RealGL3.GLs) (hk : kᵀ * k = 1) (l : Fin (n + 1)) :
    W₁ u h (x * k * kb l) = ∑ l', σ k l' l * W₁ u h (x * kb l') := by
  have hkG : k ∈ RealGL3.GLs := mem_GLs_of_orth hk
  have hucont : Continuous u := hD []
  have hlift : archRealLift3 (x * k * kb l) = archRealLift3 x * (archRealLift3 k * archRealLift3 (kb l)) := by
    rw [Bridge.archRealLift3_mul (RealGL3.mul_mem_GLs hx hkG) (mem_GLs_of_orth (hkb l)),
      Bridge.archRealLift3_mul hx hkG,
      mul_assoc]
  rw [W₁_apply, hlift, whittaker3_mul_right, Φt_mul_lift_eq_sum (hσ k hk) hh l]
  rw [whittaker3_finset_sum Finset.univ (fun l' g => σ k l' l * Φt u h (g * archRealLift3 (kb l'))) ?_]
  · refine Finset.sum_congr rfl fun l' _ => ?_
    rw [whittaker3_const_mul, W₁_apply, Bridge.archRealLift3_mul hx (mem_GLs_of_orth (hkb l')),
      whittaker3_mul_right]
  · intro l' _
    exact continuous_const.mul (hucont.comp ((continuous_mul_const _).mul continuous_const))

end LanglandsTunnell.CubicInduction.Datum
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv WhittakerBlock.casimir2 WhittakerBlock.casimir3 AdelicGL globalPointsGL centralScalarGL upperUnipotent3 componentAt3 archComponent3 whittaker3 orth3 whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3"
namespace Datum
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private def Good (θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop := IsArchSmooth3 θ ∧ ∀ w : List (Fin 3 × Fin 3), Continuous
    (W w θ)

private theorem good_Φt {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hD : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) u w))
    (hs : IsArchSmooth3 u) {h : AdelicGL 3 (𝓞 ℚ) ℚ} (hh : archComponent3 (𝓞 ℚ) ℚ h = 1) : Good (Φt u h) :=
  ⟨isArchSmooth3_Φt hs h, fun w => continuous_W_Φt hD hh w⟩

private theorem whittaker3_W_of_good {θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hθ : Good θ) (w : List (Fin 3 × Fin 3)) :
    whittaker3 P3 ψQ (W w θ) = W w (whittaker3 P3 ψQ θ) :=
  (whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3 θ hθ.1 hθ.2).1 w

private theorem whittaker3_zero_fun' (g : AdelicGL 3 (𝓞 ℚ) ℚ) : whittaker3 P3 ψQ (fun _ => (0 : ℂ)) g = 0 := by
  unfold whittaker3
  simp

private theorem casimir2_eq_sum_W (θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    casimir2 θ = fun g => ∑ p : Fin 3 × Fin 3, W [(p.1, p.2), (p.2, p.1)] θ g := by
  funext g
  simp only [casimir2, W_cons, W_nil, Fintype.sum_prod_type]

private theorem casimir3_eq_sum_W (θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    casimir3 θ = fun g => ∑ p : Fin 3 × Fin 3 × Fin 3, W [(p.1, p.2.1), (p.2.1, p.2.2), (p.2.2, p.1)] θ g := by
  funext g
  simp only [casimir3, W_cons, W_nil, Fintype.sum_prod_type]

private theorem good_casimir2 {θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hθ : Good θ) : Good (casimir2 θ) := by
  refine ⟨isArchSmooth3_casimir2 hθ.1, fun w => ?_⟩
  have h1 : W w (casimir2 θ) = casimir2 (W w θ) := by
    have h := casimir2_iterate_W w hθ.1 1
    simpa only [Function.iterate_one] using h.symm
  rw [h1, casimir2_eq_sum_W]
  exact continuous_finsetSum _ fun p _ => hθ.2 ((p.1, p.2) :: (p.2, p.1) :: w)

private theorem good_casimir3 {θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hθ : Good θ) : Good (casimir3 θ) := by
  refine ⟨isArchSmooth3_casimir3 hθ.1, fun w => ?_⟩
  have h1 : W w (casimir3 θ) = casimir3 (W w θ) := by
    have h := casimir3_iterate_W w hθ.1 1
    simpa only [Function.iterate_one] using h.symm
  rw [h1, casimir3_eq_sum_W]
  exact continuous_finsetSum _ fun p _ => hθ.2 ((p.1, p.2.1) :: (p.2.1, p.2.2) :: (p.2.2, p.1) :: w)

private theorem whittaker3_casimir2 {θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hθ : Good θ) :
    whittaker3 P3 ψQ (casimir2 θ) = casimir2 (whittaker3 P3 ψQ θ) := by
  funext g
  rw [casimir2_eq_sum_W θ, casimir2_eq_sum_W,
    whittaker3_finset_sum Finset.univ (fun p : Fin 3 × Fin 3 => W [(p.1, p.2), (p.2, p.1)] θ) (fun p _ => hθ.2 _) g]
  simp only [whittaker3_W_of_good hθ]

private theorem whittaker3_casimir3 {θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hθ : Good θ) :
    whittaker3 P3 ψQ (casimir3 θ) = casimir3 (whittaker3 P3 ψQ θ) := by
  funext g
  rw [casimir3_eq_sum_W θ, casimir3_eq_sum_W,
    whittaker3_finset_sum Finset.univ
      (fun p : Fin 3 × Fin 3 × Fin 3 => W [(p.1, p.2.1), (p.2.1, p.2.2), (p.2.2, p.1)] θ) (fun p _ => hθ.2 _) g]
  simp only [whittaker3_W_of_good hθ]

section Iterates

variable {S : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)}

private theorem good_iterate (hS : ∀ θ, Good θ → Good (S θ)) {θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hθ : Good θ) (m : ℕ) :
    Good (S^[m] θ) := by
  induction m with
  | zero => exact hθ
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact hS _ ih

private theorem whittaker3_iterate (hS : ∀ θ, Good θ → Good (S θ))
    (hwh : ∀ θ, Good θ → whittaker3 P3 ψQ (S θ) = S (whittaker3 P3 ψQ θ))
    {θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hθ : Good θ) (m : ℕ) :
    whittaker3 P3 ψQ (S^[m] θ) = S^[m] (whittaker3 P3 ψQ θ) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', hwh _ (good_iterate hS hθ m), ih, Function.iterate_succ_apply']

private theorem sum_smul_iterate_whittaker3 (hS : ∀ θ, Good θ → Good (S θ))
    (hwh : ∀ θ, Good θ → whittaker3 P3 ψQ (S θ) = S (whittaker3 P3 ψQ θ))
    {θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hθ : Good θ) {N : ℕ} (a : Fin (N + 1) → ℂ) (hrel : ∑ m, a m • (S^[m] θ) = 0) :
    ∑ m, a m • (S^[m] (whittaker3 P3 ψQ θ)) = 0 := by
  have h1 : ∀ m, S^[m] (whittaker3 P3 ψQ θ) = whittaker3 P3 ψQ (S^[m] θ) := fun m =>
    (whittaker3_iterate hS hwh hθ m).symm
  have h3 : (fun x => ∑ m, a m * S^[m] θ x) = fun _ => (0 : ℂ) := by
    funext x
    have hx := congrFun hrel x
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hx
  simp only [h1]
  funext g
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  simp_rw [← whittaker3_const_mul]
  rw [← whittaker3_finset_sum Finset.univ (fun m x => a m * S^[m] θ x)
    (fun m _ => continuous_const.mul ((good_iterate hS hθ m).2 [])) g]
  rw [h3]
  exact whittaker3_zero_fun' g

end Iterates
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"

private theorem casimir2_Φt (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) {h : AdelicGL 3 (𝓞 ℚ) ℚ} (hh : archComponent3 (𝓞 ℚ) ℚ h = 1) :
    casimir2 (Φt v h) = Φt (casimir2 v) h := by
  rw [casimir2_eq_sum_W, casimir2_eq_sum_W]
  simp only [W_Φt v hh]
  rfl

private theorem casimir3_Φt (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) {h : AdelicGL 3 (𝓞 ℚ) ℚ} (hh : archComponent3 (𝓞 ℚ) ℚ h = 1) :
    casimir3 (Φt v h) = Φt (casimir3 v) h := by
  rw [casimir3_eq_sum_W, casimir3_eq_sum_W]
  simp only [W_Φt v hh]
  rfl

private theorem iterate_Φt {S : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)} {h : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hSΦ : ∀ v, S (Φt v h) = Φt (S v) h) (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (m : ℕ) :
    S^[m] (Φt v h) = Φt (S^[m] v) h := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, hSΦ, Function.iterate_succ_apply']

private theorem sum_smul_iterate_Φt {S : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)} {h : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hSΦ : ∀ v, S (Φt v h) = Φt (S v) h) {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} {N : ℕ} (a : Fin (N + 1) → ℂ)
    (hrel : ∑ m, a m • (S^[m] u) = 0) : ∑ m, a m • (S^[m] (Φt u h)) = 0 := by
  simp only [iterate_Φt hSΦ]
  funext g
  have hx := congrFun hrel (g * h)
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Φt] using hx

private theorem relation2_whittaker3_Φt {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hD : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) u w))
    (hs : IsArchSmooth3 u) {h : AdelicGL 3 (𝓞 ℚ) ℚ} (hh : archComponent3 (𝓞 ℚ) ℚ h = 1) {N : ℕ}
    (a : Fin (N + 1) → ℂ) (hrel : ∑ m, a m • (casimir2^[m] u) = 0) :
    ∑ m, a m • (casimir2^[m] (whittaker3 P3 ψQ (Φt u h))) = 0 :=
  sum_smul_iterate_whittaker3 (fun _ => good_casimir2) (fun _ => whittaker3_casimir2) (good_Φt hD hs hh) a
    (sum_smul_iterate_Φt (fun v => casimir2_Φt v hh) a hrel)

private theorem relation3_whittaker3_Φt {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hD : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) u w))
    (hs : IsArchSmooth3 u) {h : AdelicGL 3 (𝓞 ℚ) ℚ} (hh : archComponent3 (𝓞 ℚ) ℚ h = 1) {N : ℕ}
    (a : Fin (N + 1) → ℂ) (hrel : ∑ m, a m • (casimir3^[m] u) = 0) :
    ∑ m, a m • (casimir3^[m] (whittaker3 P3 ψQ (Φt u h))) = 0 :=
  sum_smul_iterate_whittaker3 (fun _ => good_casimir3) (fun _ => whittaker3_casimir3) (good_Φt hD hs hh) a
    (sum_smul_iterate_Φt (fun v => casimir3_Φt v hh) a hrel)

end LanglandsTunnell.CubicInduction.Datum
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv WhittakerBlock.casimir2 WhittakerBlock.casimir3 AdelicGL globalPointsGL centralScalarGL upperUnipotent3 componentAt3 archComponent3 whittaker3 orth3 whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3"
namespace Datum
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private theorem rD_E_congr {F G : RealGL3.M3 → ℂ} (hFG : ∀ y ∈ RealGL3.GLs, F y = G y) (a b : Fin 3) {x : RealGL3.M3}
    (hx : x ∈ RealGL3.GLs) : RealGL3.rD (RealGL3.E a b) F x = RealGL3.rD (RealGL3.E a b) G x := by
  show deriv (fun s : ℝ => F (x * (1 + s • RealGL3.E a b))) 0 = deriv (fun s : ℝ => G (x * (1 + s • RealGL3.E a b))) 0
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [eventually_one_add_smul_E_mem_GLs a b] with s hs
  exact hFG _ (RealGL3.mul_mem_GLs hx hs)

private theorem rDl_congr (w : List (Fin 3 × Fin 3)) {F G : RealGL3.M3 → ℂ} (hFG : ∀ y ∈ RealGL3.GLs, F y = G y) :
    ∀ x ∈ RealGL3.GLs, RealGL3.rDl w F x = RealGL3.rDl w G x := by
  induction w with
  | nil => exact hFG
  | cons ab w ih =>
    intro x hx
    exact rD_E_congr ih ab.1 ab.2 hx

private theorem rDl_realRestr (Ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (w : List (Fin 3 × Fin 3)) :
    ∀ x ∈ RealGL3.GLs, RealGL3.rDl w (realRestr Ψ) x = realRestr (W w Ψ) x := by
  induction w with
  | nil =>
    intro x _
    rfl
  | cons ab w ih =>
    intro x hx
    show RealGL3.rD (RealGL3.E ab.1 ab.2) (RealGL3.rDl w (realRestr Ψ)) x = _
    rw [rD_E_congr ih ab.1 ab.2 hx, rD_realRestr _ _ _ hx]
    rfl

private theorem c2_eq_sum_rDl (F : RealGL3.M3 → ℂ) (x : RealGL3.M3) :
    RealGL3.c2 F x = ∑ p : Fin 3 × Fin 3, RealGL3.rDl [(p.1, p.2), (p.2, p.1)] F x := by
  simp only [RealGL3.c2, RealGL3.rDl, List.foldr, Fintype.sum_prod_type]

private theorem c3_eq_sum_rDl (F : RealGL3.M3 → ℂ) (x : RealGL3.M3) :
    RealGL3.c3 F x =
      ∑ p : Fin 3 × Fin 3 × Fin 3, RealGL3.rDl [(p.1, p.2.1), (p.2.1, p.2.2), (p.2.2, p.1)] F x := by
  simp only [RealGL3.c3, RealGL3.rDl, List.foldr, Fintype.sum_prod_type]

private theorem c2_congr (F G : RealGL3.M3 → ℂ) (hFG : ∀ y ∈ RealGL3.GLs, F y = G y) :
    ∀ x ∈ RealGL3.GLs, RealGL3.c2 F x = RealGL3.c2 G x := by
  intro x hx
  rw [c2_eq_sum_rDl, c2_eq_sum_rDl]
  exact Finset.sum_congr rfl fun p _ => rDl_congr _ hFG x hx

private theorem c3_congr (F G : RealGL3.M3 → ℂ) (hFG : ∀ y ∈ RealGL3.GLs, F y = G y) :
    ∀ x ∈ RealGL3.GLs, RealGL3.c3 F x = RealGL3.c3 G x := by
  intro x hx
  rw [c3_eq_sum_rDl, c3_eq_sum_rDl]
  exact Finset.sum_congr rfl fun p _ => rDl_congr _ hFG x hx

private theorem c2_realRestr (Ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : ∀ x ∈ RealGL3.GLs,
    RealGL3.c2 (realRestr Ψ) x = realRestr (casimir2 Ψ) x := by
  intro x hx
  rw [c2_eq_sum_rDl]
  simp only [rDl_realRestr Ψ _ x hx, realRestr, casimir2_eq_sum_W]

private theorem c3_realRestr (Ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : ∀ x ∈ RealGL3.GLs,
    RealGL3.c3 (realRestr Ψ) x = realRestr (casimir3 Ψ) x := by
  intro x hx
  rw [c3_eq_sum_rDl]
  simp only [rDl_realRestr Ψ _ x hx, realRestr, casimir3_eq_sum_W]

section RealIterates

variable {T : (RealGL3.M3 → ℂ) → (RealGL3.M3 → ℂ)} {S : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)}

private theorem iterate_realRestr
    (hT : ∀ F G : RealGL3.M3 → ℂ, (∀ y ∈ RealGL3.GLs, F y = G y) → ∀ x ∈ RealGL3.GLs, T F x = T G x)
    (hTS : ∀ Ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ∀ x ∈ RealGL3.GLs, T (realRestr Ψ) x = realRestr (S Ψ) x)
    (Ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (m : ℕ) :
    ∀ x ∈ RealGL3.GLs, (T^[m] (realRestr Ψ)) x = realRestr (S^[m] Ψ) x := by
  induction m with
  | zero =>
    intro x _
    rfl
  | succ m ih =>
    intro x hx
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hT _ _ ih x hx]
    exact hTS _ x hx

end RealIterates
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"

private theorem sum_mul_iterate_realRestr_eq_zero {T : (RealGL3.M3 → ℂ) → (RealGL3.M3 → ℂ)}
    {S : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)}
    (hT : ∀ F G : RealGL3.M3 → ℂ, (∀ y ∈ RealGL3.GLs, F y = G y) → ∀ x ∈ RealGL3.GLs, T F x = T G x)
    (hTS : ∀ Ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ∀ x ∈ RealGL3.GLs, T (realRestr Ψ) x = realRestr (S Ψ) x)
    {Ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} {N : ℕ} {a : Fin (N + 1) → ℂ} (hrel : ∑ m, a m • (S^[m] Ψ) = 0) :
    ∀ x ∈ RealGL3.GLs, ∑ j, a j * (T^[j] (realRestr Ψ)) x = 0 := by
  intro x hx
  have hx' := congrFun hrel (archRealLift3 x)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hx'
  refine (Finset.sum_congr rfl fun j _ => ?_).trans hx'
  rw [iterate_realRestr hT hTS Ψ j x hx]
  rfl

private theorem relation2_W₁ {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hD : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) u w))
    (hs : IsArchSmooth3 u) {h : AdelicGL 3 (𝓞 ℚ) ℚ} (hh : archComponent3 (𝓞 ℚ) ℚ h = 1) {N : ℕ}
    (a : Fin (N + 1) → ℂ) (hrel : ∑ m, a m • (casimir2^[m] u) = 0) :
    ∀ x ∈ RealGL3.GLs, ∑ j, a j * (RealGL3.c2^[j] (W₁ u h)) x = 0 :=
  sum_mul_iterate_realRestr_eq_zero c2_congr c2_realRestr (relation2_whittaker3_Φt hD hs hh a hrel)

private theorem relation3_W₁ {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hD : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) u w))
    (hs : IsArchSmooth3 u) {h : AdelicGL 3 (𝓞 ℚ) ℚ} (hh : archComponent3 (𝓞 ℚ) ℚ h = 1) {N : ℕ}
    (a : Fin (N + 1) → ℂ) (hrel : ∑ m, a m • (casimir3^[m] u) = 0) :
    ∀ x ∈ RealGL3.GLs, ∑ j, a j * (RealGL3.c3^[j] (W₁ u h)) x = 0 :=
  sum_mul_iterate_realRestr_eq_zero c3_congr c3_realRestr (relation3_whittaker3_Φt hD hs hh a hrel)

end LanglandsTunnell.CubicInduction.Datum
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv WhittakerBlock.casimir2 WhittakerBlock.casimir3 AdelicGL globalPointsGL centralScalarGL upperUnipotent3 componentAt3 archComponent3 whittaker3 orth3 whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3"
namespace Datum
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private def Legs (cω : ℂ) {N₂ N₃ : ℕ} (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ) {n : ℕ}
    (σ : RealGL3.M3 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (kb : Fin (n + 1) → RealGL3.M3) (Wr : RealGL3.M3 → ℂ) :
    Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) Wr RealGL3.GLs ∧
    (∀ n' x : RealGL3.M3, RealGL3.IsUpperUni n' → x ∈ RealGL3.GLs → Wr (n' * x) = RealGL3.uniChar n' * Wr x) ∧
    (∀ x ∈ RealGL3.GLs, RealGL3.rD 1 Wr x = cω * Wr x) ∧
    (∀ x k : RealGL3.M3, x ∈ RealGL3.GLs → kᵀ * k = 1 → ∀ l,
      Wr (x * k * kb l) = ∑ l', σ k l' l * Wr (x * kb l')) ∧
    (∀ x ∈ RealGL3.GLs, ∑ j, a₂ j * (RealGL3.c2^[j] Wr) x = 0) ∧
    (∀ x ∈ RealGL3.GLs, ∑ j, a₃ j * (RealGL3.c3^[j] Wr) x = 0)

private def HasDatum (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (cω : ℂ) {N₂ N₃ : ℕ} (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ)
    :
    Prop :=
  ∃ (n : ℕ) (σ : RealGL3.M3 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (kb : Fin (n + 1) → RealGL3.M3),
    ContDiffOn ℝ (⊤ : ℕ∞) σ RealGL3.GLs ∧ σ 1 = 1 ∧
    (∀ k k' : RealGL3.M3, kᵀ * k = 1 → k'ᵀ * k' = 1 → σ (k * k') = σ k * σ k') ∧
    (∀ l, (kb l)ᵀ * kb l = 1) ∧ kb 0 = 1 ∧
    ∀ h : AdelicGL 3 (𝓞 ℚ) ℚ, archComponent3 (𝓞 ℚ) ℚ h = 1 → Legs cω a₂ a₃ σ kb (W₁ u h)

private theorem hasDatum_of_ne_zero {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hD : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) u w))
    (hinv : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g)
    {ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ}
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g)
    (hs : IsArchSmooth3 u)
    (hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => u (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    {cω : ℂ} (hcω : ∀ Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsArchSmooth3 Φ →
      (∀ (c : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        Φ (centralScalarGL 3 (𝓞 ℚ) ℚ c * g) = (ω c : ℂ) * Φ g) →
      ∀ g, ∑ i : Fin 3, archDeriv i i Φ g = cω * Φ g)
    {N₂ N₃ : ℕ} {a₂ : Fin (N₂ + 1) → ℂ} {a₃ : Fin (N₃ + 1) → ℂ}
    (hrel2 : ∑ m, a₂ m • (casimir2^[m] u) = 0) (hrel3 : ∑ m, a₃ m • (casimir3^[m] u) = 0) (hu0 : u ≠ 0) :
    HasDatum u cω a₂ a₃ := by
  obtain ⟨n, kb, hkb, hkb0, hli, hstab⟩ := exists_real_frame hu0 hKf
  obtain ⟨σ, hσs, hσ1, hσmul, hexp⟩ :=
    exists_frame_coeff (fun l => tr u (kb l)) (fun l => isArchSmooth3_mul_right hs (archRealLift3 (kb l))) hli hstab
  refine ⟨n, σ, kb, hσs, hσ1, hσmul, hkb, hkb0, fun h hh => ?_⟩
  exact ⟨contDiffOn_W₁ hD hs hh, W₁_uni_mul hinv h, fun x hx => rD_one_W₁ hD hs hcen hcω hh hx,
    W₁_mul_orth_mul_kb hD hkb hexp hh, relation2_W₁ hD hs hh a₂ hrel2, relation3_W₁ hD hs hh a₃ hrel3⟩

private theorem W₁_zero (h : AdelicGL 3 (𝓞 ℚ) ℚ) : W₁ (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) h = fun _ => (0 : ℂ) := by
  funext x
  exact whittaker3_zero_fun' (archRealLift3 x)

private theorem rD_zero_fun (X : RealGL3.M3) (x : RealGL3.M3) : RealGL3.rD X (fun _ => (0 : ℂ)) x = 0 := by
  show deriv (fun _ : ℝ => (0 : ℂ)) 0 = 0
  simp

private theorem c2_zero_fun : RealGL3.c2 (fun _ => (0 : ℂ)) = fun _ => (0 : ℂ) := by
  funext x
  simp only [RealGL3.c2]
  have h2 : ∀ a b : Fin 3, RealGL3.rD (RealGL3.E a b) (fun _ => (0 : ℂ)) = fun _ => (0 : ℂ) := by
    intro a b
    funext y
    exact rD_zero_fun _ y
  simp only [h2, Finset.sum_const_zero]

private theorem c3_zero_fun : RealGL3.c3 (fun _ => (0 : ℂ)) = fun _ => (0 : ℂ) := by
  funext x
  simp only [RealGL3.c3]
  have h2 : ∀ a b : Fin 3, RealGL3.rD (RealGL3.E a b) (fun _ => (0 : ℂ)) = fun _ => (0 : ℂ) := by
    intro a b
    funext y
    exact rD_zero_fun _ y
  simp only [h2, Finset.sum_const_zero]

private theorem iterate_zero_fun {T : (RealGL3.M3 → ℂ) → (RealGL3.M3 → ℂ)}
    (hT : T (fun _ => (0 : ℂ)) = fun _ => (0 : ℂ))
    (j : ℕ) : T^[j] (fun _ => (0 : ℂ)) = fun _ => (0 : ℂ) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih, hT]

private theorem legs_zero_fun (cω : ℂ) {N₂ N₃ : ℕ} (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ) {n : ℕ}
    (σ : RealGL3.M3 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (kb : Fin (n + 1) → RealGL3.M3) :
    Legs cω a₂ a₃ σ kb (fun _ => (0 : ℂ)) := by
  refine ⟨contDiffOn_const, fun _ _ _ _ => by simp, fun x _ => ?_, fun _ _ _ _ _ => by simp, fun x _ => ?_,
    fun x _ => ?_⟩
  · rw [rD_zero_fun]
    simp
  · simp only [iterate_zero_fun c2_zero_fun, mul_zero, Finset.sum_const_zero]
  · simp only [iterate_zero_fun c3_zero_fun, mul_zero, Finset.sum_const_zero]

private theorem hasDatum_zero (cω : ℂ) {N₂ N₃ : ℕ} (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ) :
    HasDatum (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) cω a₂ a₃ := by
  refine ⟨0, fun _ => 1, fun _ => 1, contDiffOn_const, rfl, fun _ _ _ _ => by simp,
    fun _ => orth_one, rfl, fun h _ => ?_⟩
  rw [W₁_zero h]
  exact legs_zero_fun cω a₂ a₃ _ _

private theorem hasDatum {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hD : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) u w))
    (hinv : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g)
    {ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ}
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g)
    (hs : IsArchSmooth3 u)
    (hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => u (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    {cω : ℂ} (hcω : ∀ Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsArchSmooth3 Φ →
      (∀ (c : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        Φ (centralScalarGL 3 (𝓞 ℚ) ℚ c * g) = (ω c : ℂ) * Φ g) →
      ∀ g, ∑ i : Fin 3, archDeriv i i Φ g = cω * Φ g)
    {N₂ N₃ : ℕ} {a₂ : Fin (N₂ + 1) → ℂ} {a₃ : Fin (N₃ + 1) → ℂ}
    (hrel2 : ∑ m, a₂ m • (casimir2^[m] u) = 0) (hrel3 : ∑ m, a₃ m • (casimir3^[m] u) = 0) :
    HasDatum u cω a₂ a₃ := by
  by_cases hu0 : u = 0
  · subst hu0
    exact hasDatum_zero cω a₂ a₃
  · exact hasDatum_of_ne_zero hD hinv hcen hs hKf hcω hrel2 hrel3 hu0

end LanglandsTunnell.CubicInduction.Datum
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv WhittakerBlock.casimir2 WhittakerBlock.casimir3 AdelicGL globalPointsGL centralScalarGL upperUnipotent3 componentAt3 archComponent3 whittaker3 orth3 whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3"
namespace Datum
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private theorem continuous_realCoord : Continuous realCoord := by
  have h : (realCoord : InfiniteAdeleRing ℚ → ℝ) = fun x =>
      InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (x Rat.infinitePlace) :=
    funext realCoord_apply
  rw [h]
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).continuous.comp (continuous_apply _)

private theorem continuous_realMat : Continuous realMat := by
  have h : (realMat : GL (Fin 3) (InfiniteAdeleRing ℚ) → Matrix (Fin 3) (Fin 3) ℝ) =
      fun g : GL (Fin 3) (InfiniteAdeleRing ℚ) => (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).map realCoord :=
    funext realMat_eq
  rw [h]
  exact Units.continuous_val.matrix_map continuous_realCoord

private theorem continuous_glMap3 {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A]
    [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 3) f) :=
  Continuous.units_map _ ((continuous_id.matrix_map hf) : Continuous fun m : Matrix (Fin 3) (Fin 3) A => m.map f)

private theorem continuous_archComponent3 : Continuous (archComponent3 (𝓞 ℚ) ℚ) :=
  continuous_glMap3 _ (AdelicLevel.continuous_adeleArch (𝓞 ℚ) ℚ)

private theorem continuous_realMat_archComponent3 :
    Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => realMat (archComponent3 (𝓞 ℚ) ℚ g) :=
  continuous_realMat.comp continuous_archComponent3

private theorem realMat_archComponent3_mem_GLs (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    realMat (archComponent3 (𝓞 ℚ) ℚ g) ∈ RealGL3.GLs := by
  show (realMat (archComponent3 (𝓞 ℚ) ℚ g)).det ≠ 0
  exact det_realMat_ne_zero _

private theorem torus_eq_array (y z : ℝ) :
    RealGL3.torus y z = fun i j : Fin 3 => if i = j then ![y * z, z, 1] i else (0 : ℝ) := rfl

private theorem whittaker3_W_eq_rDl_W₁ {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hD : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => archDeriv ij.1 ij.2 φ) u w))
    (hs : IsArchSmooth3 u) {h : AdelicGL 3 (𝓞 ℚ) ℚ} (hh : archComponent3 (𝓞 ℚ) ℚ h = 1) (w : List (Fin 3 × Fin 3))
    {t k₀ kb' : RealGL3.M3} (ht : t ∈ RealGL3.GLs) (hk₀ : k₀ ∈ RealGL3.GLs) (hkb : kb' ∈ RealGL3.GLs) :
    whittaker3 P3 ψQ (W w u) (archRealLift3 t * (archRealLift3 k₀ * h) * archRealLift3 kb') =
      RealGL3.rDl w (W₁ u h) (t * k₀ * kb') := by
  have h1 : RealGL3.rDl w (W₁ u h) (t * k₀ * kb') =
      W w (whittaker3 P3 ψQ (Φt u h)) (archRealLift3 (t * k₀ * kb')) :=
    rDl_realRestr _ w _ (RealGL3.mul_mem_GLs (RealGL3.mul_mem_GLs ht hk₀) hkb)
  rw [h1, ← whittaker3_W_of_good (good_Φt hD hs hh) w, W_Φt u hh w,
    Bridge.archRealLift3_mul (RealGL3.mul_mem_GLs ht hk₀) hkb, Bridge.archRealLift3_mul ht hk₀]
  have h2 : whittaker3 P3 ψQ (Φt (W w u) h) (archRealLift3 t * archRealLift3 k₀ * archRealLift3 kb') =
      whittaker3 P3 ψQ (W w u) (archRealLift3 t * archRealLift3 k₀ * archRealLift3 kb' * h) :=
    (whittaker3_mul_right (W w u) _ h).symm
  rw [h2]
  congr 1
  simp only [mul_assoc]
  rw [archRealLift3_mul_comm_of_archComponent3 hh kb']

end LanglandsTunnell.CubicInduction.Datum
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"

open LanglandsTunnell.CubicInduction.Bridge

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv WhittakerBlock.casimir2 WhittakerBlock.casimir3 AdelicGL globalPointsGL centralScalarGL upperUnipotent3 componentAt3 archComponent3 whittaker3 orth3 whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3"
namespace Datum
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem key_of_R7
    (N₂ N₃ : ℕ) :
    ∃ (d d₂ d' d₂' : ℕ),
      ∀ (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a₂ : Fin (N₂ + 1) → ℂ), a₂ (Fin.last N₂) = 1 →
      ∀ (a₃ : Fin (N₃ + 1) → ℂ), a₃ (Fin.last N₃) = 1 →
      ∃ (ι ι' : Finset ℂ) (q q' : Polynomial ℂ),
      q ≠ 0 ∧ q' ≠ 0 ∧ q.natDegree ≤ 6 * N₂ * N₃ + 1 ∧ q'.natDegree ≤ 6 * N₂ * N₃ + 1 ∧
      (∀ e : ℂ, q.IsRoot e → ∃ e₀ ∈ ι, ∃ j : ℕ, e = e₀ + j) ∧
      (∀ e : ℂ, q'.IsRoot e → ∃ e₀ ∈ ι', ∃ j : ℕ, e = e₀ + j) ∧
      ∀ (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      (∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w)) →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g) →
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g) →
      WhittakerBlock.IsArchSmooth3 u →
      (∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => u (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) →
      (∑ m, a₂ m • (WhittakerBlock.casimir2^[m] u) = 0) →
      (∑ m, a₃ m • (WhittakerBlock.casimir3^[m] u) = 0) →
      ∃ (r : ℕ) (w : Fin (r + 1) → List (Fin 3 × Fin 3)) (κ : Fin (r + 1) → AdelicGL 3 (𝓞 ℚ) ℚ)
        (Mc : AdelicGL 3 (𝓞 ℚ) ℚ → Fin (d₂ + 1) → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
        (Mc' : AdelicGL 3 (𝓞 ℚ) ℚ → Fin (d₂' + 1) → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
        (A : AdelicGL 3 (𝓞 ℚ) ℚ → Fin d → Fin (d₂ + 1) → ((Fin (r + 1) → ℂ) →L[ℂ] (Fin (r + 1) → ℂ)))
        (A' : AdelicGL 3 (𝓞 ℚ) ℚ → Fin d' → Fin (d₂' + 1) → ((Fin (r + 1) → ℂ) →L[ℂ] (Fin (r + 1) → ℂ))),
        w 0 = [] ∧ κ 0 = 1 ∧
        (∀ i, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p (κ i) = 1) ∧
          archComponent3 (𝓞 ℚ) ℚ (κ i) ∈ orth3) ∧
        (∀ b, Continuous fun g => Mc g b) ∧ (∀ a, Continuous fun g => Mc' g a) ∧
        (∀ k b, Continuous fun g => A g k b) ∧ (∀ k a, Continuous fun g => A' g k a) ∧
        ∀ g₀ : AdelicGL 3 (𝓞 ℚ) ℚ, archComponent3 (𝓞 ℚ) ℚ g₀ ∈ orth3 →
          (∀ z : ℝ, 0 < z → Polynomial.aeval (∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • Mc g₀ b) q = 0) ∧
          (∀ y : ℝ, 0 < y → Polynomial.aeval (∑ a : Fin (d₂' + 1), ((y : ℂ) ^ (a : ℕ)) • Mc' g₀ a) q' = 0) ∧
          ∀ F : ℝ → ℝ → (Fin (r + 1) → ℂ),
          (∀ (y z : ℝ) (i : Fin (r + 1)), F y z i =
            whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ
              (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u (w i))
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y * z, z, 1] i else 0) * g₀ * κ i)) →
          (∀ y z : ℝ, F y z 0 =
            whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y * z, z, 1] i else 0) * g₀)) ∧
          ∃ Fy Fz : ℝ → ℝ → (Fin (r + 1) → ℂ),
          (∀ z : ℝ, 0 < z → ∀ y : ℝ, 0 < y → HasDerivAt (fun y => F y z) (Fy y z) y ∧
            (y : ℂ) • Fy y z = (fun i => ∑ j, (∑ b : Fin (d₂ + 1), (z : ℂ) ^ (b : ℕ) * Mc g₀ b i j) • F y z j) +
              ∑ k : Fin d, ∑ b : Fin (d₂ + 1),
                ((y : ℂ) ^ ((k : ℕ) + 1) * (z : ℂ) ^ (b : ℕ)) • A g₀ k b (F y z)) ∧
          (∀ y : ℝ, 0 < y → ∀ z : ℝ, 0 < z → HasDerivAt (fun z => F y z) (Fz y z) z ∧
            (z : ℂ) • Fz y z = (fun i => ∑ j, (∑ a : Fin (d₂' + 1), (y : ℂ) ^ (a : ℕ) * Mc' g₀ a i j) • F y z j) +
              ∑ k : Fin d', ∑ a : Fin (d₂' + 1),
                ((z : ℂ) ^ ((k : ℕ) + 1) * (y : ℂ) ^ (a : ℕ)) • A' g₀ k a (F y z)) := by
  obtain ⟨d, d₂, d', d₂', hR⟩ := RealGL3.exists_words_rDl_torus_hasDerivAt_systems N₂ N₃
  refine ⟨d, d₂, d', d₂', fun ω a₂ ha₂ a₃ ha₃ => ?_⟩
  obtain ⟨cω, hcω⟩ := exists_forall_sum_archDeriv_diag_eq_mul ω
  obtain ⟨q, q', hq0, hq'0, hqdeg, hq'deg, hmain⟩ := hR cω a₂ ha₂ a₃ ha₃
  refine ⟨q.roots.toFinset, q'.roots.toFinset, q, q', hq0, hq'0, hqdeg, hq'deg,
    fun e he => ⟨e, Multiset.mem_toFinset.2 ((Polynomial.mem_roots hq0).2 he), 0, by simp⟩,
    fun e he => ⟨e, Multiset.mem_toFinset.2 ((Polynomial.mem_roots hq'0).2 he), 0, by simp⟩,
    fun u hD hinv hcen hs hKf hrel2 hrel3 => ?_⟩

  obtain ⟨n, σ, kb, hσs, hσ1, hσmul, hkb, hkb0, hlegs⟩ := hasDatum hD hinv hcen hs hKf hcω hrel2 hrel3
  obtain ⟨r, w, m, Mc, Mc', A, A', hw0, hm0, hMc, hMc', hA, hA', hk⟩ := hmain n σ kb hσs hσ1 hσmul hkb hkb0
  refine ⟨r, w, fun i => archRealLift3 (kb (m i)),
    fun g b => Mc (realMat (archComponent3 (𝓞 ℚ) ℚ g)) b, fun g a => Mc' (realMat (archComponent3 (𝓞 ℚ) ℚ g)) a,
    fun g k b => A (realMat (archComponent3 (𝓞 ℚ) ℚ g)) k b, fun g k a => A' (realMat (archComponent3 (𝓞 ℚ) ℚ g)) k a,
    hw0, ?_, fun i => ⟨componentAt3_archRealLift3 (kb (m i)), ?_⟩,
    fun b => (hMc b).comp_continuous continuous_realMat_archComponent3 realMat_archComponent3_mem_GLs,
    fun a => (hMc' a).comp_continuous continuous_realMat_archComponent3 realMat_archComponent3_mem_GLs,
    fun k b => (hA k b).comp_continuous continuous_realMat_archComponent3 realMat_archComponent3_mem_GLs,
    fun k a => (hA' k a).comp_continuous continuous_realMat_archComponent3 realMat_archComponent3_mem_GLs,
    fun g₀ hg₀ => ?_⟩
  ·
    show archRealLift3 (kb (m 0)) = 1
    rw [hm0, hkb0, archRealLift3_one_matrix]
  ·
    exact (archComponent3_archRealLift3_mem_orth3_iff (mem_GLs_of_orth (hkb (m i)))).2 (hkb (m i))

  obtain ⟨h, hh, hg₀eq⟩ := exists_eq_archRealLift3_mul g₀
  have hk₀ : (realMat (archComponent3 (𝓞 ℚ) ℚ g₀))ᵀ * realMat (archComponent3 (𝓞 ℚ) ℚ g₀) = 1 := realMat_orth hg₀
  obtain ⟨haev, haev', hW⟩ := hk _ hk₀
  obtain ⟨hsm, hN, hZ, hK, hC2, hC3⟩ := hlegs h hh
  refine ⟨haev, haev', fun F hF => ⟨fun y z => ?_, ?_⟩⟩
  ·
    rw [hF y z 0]
    beta_reduce
    rw [hw0, List.foldr_nil, hm0, hkb0, archRealLift3_one_matrix, mul_one]

  obtain ⟨Fy, Fz, hFy, hFz⟩ := hW (W₁ u h) hsm hN hZ hK hC2 hC3
    (fun y z i => RealGL3.rDl (w i) (W₁ u h) (RealGL3.torus y z * realMat (archComponent3 (𝓞 ℚ) ℚ g₀) * kb (m i)))
    (fun _ _ _ => rfl)
  have hagree : ∀ y z : ℝ, 0 < y → 0 < z → F y z =
      fun i => RealGL3.rDl (w i) (W₁ u h) (RealGL3.torus y z * realMat (archComponent3 (𝓞 ℚ) ℚ g₀) * kb (m i)) := by
    intro y z hy hz
    funext i
    rw [hF y z i]
    have key := whittaker3_W_eq_rDl_W₁ hD hs hh (w i) (RealGL3.torus_mem_GLs hy hz) (mem_GLs_of_orth hk₀)
      (mem_GLs_of_orth (hkb (m i)))
    rw [← hg₀eq] at key
    exact key
  refine ⟨Fy, Fz, fun z hz y hy => ?_, fun y hy z hz => ?_⟩
  · obtain ⟨hd, hid⟩ := hFy z hz y hy
    refine ⟨hd.congr_of_eventuallyEq ?_, ?_⟩
    · filter_upwards [lt_mem_nhds hy] with y' hy'
      exact hagree y' z hy' hz
    · rw [hagree y z hy hz]
      exact hid
  · obtain ⟨hd, hid⟩ := hFz y hy z hz
    refine ⟨hd.congr_of_eventuallyEq ?_, ?_⟩
    · filter_upwards [lt_mem_nhds hz] with z' hz'
      exact hagree y z' hy hz'
    · rw [hagree y z hy hz]
      exact hid

end LanglandsTunnell.CubicInduction.Datum
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.RealGL3 P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction.ArchCalculus"

set_option autoImplicit false in
open IsDedekindDomain NumberField AutomorphicForm AutomorphicForm.StandardKernel _root_.WhittakerBlock _root_.LanglandsTunnell.CubicInduction.WhittakerBlock in
open LanglandsTunnell.CubicInduction.ArchCalculus in
open IsDedekindDomain NumberField AutomorphicForm _root_.WhittakerBlock _root_.LanglandsTunnell.CubicInduction.WhittakerBlock LanglandsTunnell.CubicInduction.WhittakerBlock in
open Matrix IsDedekindDomain NumberField AutomorphicForm AutomorphicForm.StandardKernel _root_.WhittakerBlock _root_.LanglandsTunnell.CubicInduction.WhittakerBlock in
open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.WhittakerBlock in
open LanglandsTunnell.CubicInduction.Bridge in
open LanglandsTunnell.CubicInduction.Bridge in
open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le.LanglandsTunnell.CubicInduction in
theorem solution
    (N₂ N₃ : ℕ) :
    ∃ (d d₂ d' d₂' : ℕ),
      ∀ (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a₂ : Fin (N₂ + 1) → ℂ), a₂ (Fin.last N₂) = 1 →
      ∀ (a₃ : Fin (N₃ + 1) → ℂ), a₃ (Fin.last N₃) = 1 →
      ∃ (ι ι' : Finset ℂ) (q q' : Polynomial ℂ),
      q ≠ 0 ∧ q' ≠ 0 ∧ q.natDegree ≤ 6 * N₂ * N₃ + 1 ∧ q'.natDegree ≤ 6 * N₂ * N₃ + 1 ∧
      (∀ e : ℂ, q.IsRoot e → ∃ e₀ ∈ ι, ∃ j : ℕ, e = e₀ + j) ∧
      (∀ e : ℂ, q'.IsRoot e → ∃ e₀ ∈ ι', ∃ j : ℕ, e = e₀ + j) ∧
      ∀ (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      (∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w)) →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g) →
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g) →
      WhittakerBlock.IsArchSmooth3 u →
      (∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => u (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) →
      (∑ m, a₂ m • (WhittakerBlock.casimir2^[m] u) = 0) →
      (∑ m, a₃ m • (WhittakerBlock.casimir3^[m] u) = 0) →
      ∃ (r : ℕ) (w : Fin (r + 1) → List (Fin 3 × Fin 3)) (κ : Fin (r + 1) → AdelicGL 3 (𝓞 ℚ) ℚ)
        (Mc : AdelicGL 3 (𝓞 ℚ) ℚ → Fin (d₂ + 1) → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
        (Mc' : AdelicGL 3 (𝓞 ℚ) ℚ → Fin (d₂' + 1) → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
        (A : AdelicGL 3 (𝓞 ℚ) ℚ → Fin d → Fin (d₂ + 1) → ((Fin (r + 1) → ℂ) →L[ℂ] (Fin (r + 1) → ℂ)))
        (A' : AdelicGL 3 (𝓞 ℚ) ℚ → Fin d' → Fin (d₂' + 1) → ((Fin (r + 1) → ℂ) →L[ℂ] (Fin (r + 1) → ℂ))),
        w 0 = [] ∧ κ 0 = 1 ∧
        (∀ i, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p (κ i) = 1) ∧
          archComponent3 (𝓞 ℚ) ℚ (κ i) ∈ orth3) ∧
        (∀ b, Continuous fun g => Mc g b) ∧ (∀ a, Continuous fun g => Mc' g a) ∧
        (∀ k b, Continuous fun g => A g k b) ∧ (∀ k a, Continuous fun g => A' g k a) ∧
        ∀ g₀ : AdelicGL 3 (𝓞 ℚ) ℚ, archComponent3 (𝓞 ℚ) ℚ g₀ ∈ orth3 →
          (∀ z : ℝ, 0 < z → Polynomial.aeval (∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • Mc g₀ b) q = 0) ∧
          (∀ y : ℝ, 0 < y → Polynomial.aeval (∑ a : Fin (d₂' + 1), ((y : ℂ) ^ (a : ℕ)) • Mc' g₀ a) q' = 0) ∧
          ∀ F : ℝ → ℝ → (Fin (r + 1) → ℂ),
          (∀ (y z : ℝ) (i : Fin (r + 1)), F y z i =
            whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ
              (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u (w i))
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y * z, z, 1] i else 0) * g₀ * κ i)) →
          (∀ y z : ℝ, F y z 0 =
            whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y * z, z, 1] i else 0) * g₀)) ∧
          ∃ Fy Fz : ℝ → ℝ → (Fin (r + 1) → ℂ),
          (∀ z : ℝ, 0 < z → ∀ y : ℝ, 0 < y → HasDerivAt (fun y => F y z) (Fy y z) y ∧
            (y : ℂ) • Fy y z = (fun i => ∑ j, (∑ b : Fin (d₂ + 1), (z : ℂ) ^ (b : ℕ) * Mc g₀ b i j) • F y z j) +
              ∑ k : Fin d, ∑ b : Fin (d₂ + 1),
                ((y : ℂ) ^ ((k : ℕ) + 1) * (z : ℂ) ^ (b : ℕ)) • A g₀ k b (F y z)) ∧
          (∀ y : ℝ, 0 < y → ∀ z : ℝ, 0 < z → HasDerivAt (fun z => F y z) (Fz y z) z ∧
            (z : ℂ) • Fz y z = (fun i => ∑ j, (∑ a : Fin (d₂' + 1), (y : ℂ) ^ (a : ℕ) * Mc' g₀ a i j) • F y z j) +
              ∑ k : Fin d', ∑ a : Fin (d₂' + 1),
                ((z : ℂ) ^ ((k : ℕ) + 1) * (y : ℂ) ^ (a : ℕ)) • A' g₀ k a (F y z)) := by
  exact LanglandsTunnell.CubicInduction.Datum.key_of_R7 N₂ N₃

end
end
end S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_words_whittaker3_diag_hasDerivAt_systems_of_casimir_relations_natDegree_le (solution)
