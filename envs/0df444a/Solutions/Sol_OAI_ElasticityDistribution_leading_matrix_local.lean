-- Prove2me | solution 1 for OAI.ElasticityDistribution.leading_matrix_local
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:33:24.51949+00:00
-- url     : https://prove2.me/submissions/29a73c9a-41a9-4cc6-9e7c-97a030d5cc8a

import Mathlib
import Definitions.Def_OAIQ6El006

section
-- module Solutions.OAIQ6_Elast.Elasticity_Augmented
attribute [-instance] _root_.OAI.ElasticityDistribution.instIsCentralScalarSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instIsScalarTowerComplexMulOppositeSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instIsScalarTowerComplexSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instModuleMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instModuleSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulCommClassComplexSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact differential-algebra identities of the physical and normalized
augmented elasticity systems. Smooth derivatives are constructed below;
commutation and Leibniz are proved, not postulated for the physical operator. -/
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented

lemma coord_coord (f : Smooth) (i j : Fin 3) (x : X) :
    (coord i (coord j f) : X → ℂ) x = fderiv ℝ (fderiv ℝ (f : X → ℂ)) x (e i) (e j) := by
  have hd : Differentiable ℝ (fderiv ℝ (f : X → ℂ)) :=
    ((smooth_coe f).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  change fderiv ℝ (fun y => fderiv ℝ (f : X → ℂ) y (e j)) x (e i) = _
  rw [fderiv_clm_apply (hd x) (differentiableAt_const (e j))]
  simp

lemma coord_commute (i j : Fin 3) (f : Smooth) : coord i (coord j f) = coord j (coord i f) := by
  apply Subtype.ext
  funext x
  rw [coord_coord, coord_coord]
  exact (smooth_coe f).contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) _ _

section CovariantAlgebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι : Type*} [Fintype ι]
variable (D : ι → Derivation ℂ A A) (T : ι → A →ₗ[ℂ] A)

variable (hD : ∀ i j f, D i (D j f) = D j (D i f))
variable (hT : ∀ i j f, T i (T j f) = T j (T i f))
variable (hTD : ∀ i a b, T i (a*b) = D i a*b+a*T i b)

omit [Fintype ι] in
lemma shifted_apply (z : ι → ℂ) (i : ι) (f : A) :
    shifted D z i f = D i f + z i • f := rfl

end CovariantAlgebra

variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι : Type*} [Fintype ι]
variable (D : ι → Derivation ℂ A A) (T : ι → A →ₗ[ℂ] A)

lemma grad_cm (m : A) (u : ι → A) :
    (∑ i, D i m*cmT D T m u i) =
      2*(∑ i, ∑ j, D i m*D j m*T i (u j)) := by
  have hs : (∑ i, ∑ j, D i m*D j m*T j (u i)) =
      ∑ i, ∑ j, D i m*D j m*T i (u j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [cmT, Finset.mul_sum, mul_add, ← mul_assoc, Finset.sum_add_distrib]
  rw [hs]
  ring_nf
  simp only [← Finset.sum_mul]

lemma grad_RT (lam m : A) (u : ι → A) (d : A) :
    (∑ i, D i m*RT D T lam m u d i) =
      m*(∑ i, D i m*lapT T (u i)) +
      (lam+m)*(∑ i, D i m*T i d) +
      2*(∑ i, ∑ j, D i m*D j m*T i (u j)) +
      (∑ i, D i m*D i lam)*d := by
  have hc := grad_cm D T m u
  simp only [RT, mul_add, Finset.sum_add_distrib]
  rw [hc]
  simp only [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

lemma normalized_vector (lam m n : A) (hn : n*m=1) (u : ι → A) (d : A) (i : ι) :
    n*RT D T lam m u d i = lapT T (u i) + ((lam+m)*n)*T i d +
      (∑ j, ((n*D j m)*T j (u i) + (n*D j m)*T i (u j))) +
      (n*D i lam)*d := by
  simp only [RT, cmT, mul_add, add_mul, Finset.mul_sum, Finset.sum_add_distrib]
  simp only [← mul_assoc]
  linear_combination lapT T (u i)*hn

lemma normalized_scalar_numerator (lam m n : A) (hn : n*m=1)
    (u : ι → A) (d : A) :
    ST D T lam m u d - 2*n*(∑ i, D i m*RT D T lam m u d i) =
      (lam+m+m)*lapT T d +
      2*(∑ i, (D i (lam+m)-(lam+m)*n*D i m)*T i d) +
      2*(∑ i, ∑ j, (D i (D j m)-2*n*D i m*D j m)*T i (u j)) +
      (lap D lam-2*n*(∑ i, D i m*D i lam))*d := by
  rw [grad_RT]
  simp only [ST, sub_mul, Finset.sum_sub_distrib]
  simp only [mul_assoc, ← Finset.mul_sum]
  linear_combination -2*(∑ i, D i m*lapT T (u i))*hn

lemma normalized_scalar (lam m n o : A) (hn : n*m=1) (ho : o*(lam+m+m)=1)
    (u : ι → A) (d : A) :
    o*(ST D T lam m u d - 2*n*(∑ i, D i m*RT D T lam m u d i)) =
      lapT T d +
      (∑ i, (2*o*(D i (lam+m)-(lam+m)*n*D i m))*T i d) +
      (∑ i, ∑ j, (2*o*(D i (D j m)-2*n*D i m*D j m))*T i (u j)) +
      (o*(lap D lam-2*n*(∑ i, D i m*D i lam)))*d := by
  rw [normalized_scalar_numerator D T lam m n hn]
  simp only [mul_add, Finset.mul_sum, ← mul_assoc, ho, one_mul]
  ring_nf

end ElasticityAugmented

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Bessel
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Concrete Fourier Bessel potentials for the required negative-order
supported Carleman estimate. All functions and operators are actual Schwartz
maps; no Sobolev-shift estimate is being assumed. -/
open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

/-! Positive commutator algebra on actual Schwartz functions, allowing
nonlocal Bessel shifts without silently retaining compact support. -/
open MeasureTheory Complex SchwartzMap LineDeriv
open scoped BigOperators LineDeriv SchwartzMap
namespace ElasticitySchwartzCarleman

lemma smooth (f : Test) : ContDiff ℝ (⊤ : ℕ∞) (f : X → ℂ) := f.smooth _

lemma d_d (v w : X) (f : Test) (z : X) :
    (d v (d w f) : X → ℂ) z = fderiv ℝ (fderiv ℝ (f : X → ℂ)) z v w := by
  have hd : Differentiable ℝ (fderiv ℝ (f : X → ℂ)) :=
    ((smooth f).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  change fderiv ℝ (fun y => fderiv ℝ (f : X → ℂ) y w) z v = _
  rw [fderiv_clm_apply (hd z) (differentiableAt_const w)]
  simp

lemma d_comm (v w : X) (f : Test) : d v (d w f) = d w (d v f) := by
  ext z
  rw [d_d, d_d]
  exact (smooth f).contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) _ _

end ElasticitySchwartzCarleman

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Carleman
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

open scoped BigOperators
namespace ElasticityAugmented
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (D : Fin 3 → Derivation ℂ A A) (T : Fin 3 → A →ₗ[ℂ] A)

lemma normalizedPair_matrix (lam m n o : A) (hn : n*m=1) (ho : o*(lam+m+m)=1)
    (U : Fin 4 → A) (i : Fin 4) :
    normalizedPair D T lam m n o (fun j => U j.succ) (U 0) i =
      lapT T (U i) + (∑ k, ∑ j, coeffA D lam m n o k i j * T k (U j)) +
        (∑ j, coeffV D lam m n o i j*U j) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · change o*(ST D T lam m _ _-2*n*(∑ i, D i m*RT D T lam m _ _ i)) = _
    rw [normalized_scalar D T lam m n o hn ho]
    simp only [coeffA, coeffV, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      zero_mul, Finset.sum_const_zero, add_zero, Finset.sum_add_distrib]
    ring
  · change n*RT D T lam m _ _ i = _
    rw [normalized_vector D T lam m n hn]
    simp only [coeffA, coeffV, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      zero_mul, Finset.sum_const_zero, add_zero, add_mul, ite_mul,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring

end ElasticityAugmented

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
open Set MeasureTheory SchwartzMap
open scoped BigOperators SchwartzMap Topology

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Regularity
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Actual distributional elliptic regularity dependencies of the physical and
planar weak-limit constructions. No regularity assumption on an L2 unknown is
used in the gain of Sobolev order below. -/
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal

open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators
namespace ElasticityDistribution

open ElasticityAugmented ElasticityRegularity TemperedDistribution
lemma dd_apply (i : Fin 3) (u : Dist) : dd i u = ∂_{e i} u := rfl
lemma dc_commute (i j : Fin 3) (a : Coeff) : dc i (dc j a) = dc j (dc i a) := by
  apply Subtype.ext
  exact coord_commute i j a.val
lemma dd_commute (i j : Fin 3) (u : Dist) : dd i (dd j u) = dd j (dd i u) := by
  ext φ
  change u (- ∂_{e j} (- ∂_{e i} φ)) = u (- ∂_{e i} (- ∂_{e j} φ))
  simp only [LineDeriv.lineDerivOp_neg,neg_neg]
  congr 1
  exact ElasticitySchwartzCarleman.d_comm (e j) (e i) φ

open ElasticityAugmented TrivSqZeroExt

lemma de_fst (i : Fin 3) (v : Ext) : (de i v).fst = dc i v.fst := rfl
lemma de_snd (i : Fin 3) (v : Ext) : (de i v).snd = dd i v.snd := rfl
lemma de_inl (i : Fin 3) (a : Coeff) : de i (inl a) = inl (dc i a) := by
  apply TrivSqZeroExt.ext <;> simp [de_fst,de_snd]
lemma de_inr (i : Fin 3) (u : Dist) : de i (inr u) = inr (dd i u) := by
  apply TrivSqZeroExt.ext <;> simp [de_fst,de_snd]
lemma de_commute (i j : Fin 3) (v : Ext) : de i (de j v) = de j (de i v) := by
  apply TrivSqZeroExt.ext
  · exact dc_commute i j v.fst
  · exact dd_commute i j v.snd

lemma sd_apply (z : Fin 3 → ℂ) (i : Fin 3) (u : Dist) : sd z i u = dd i u+z i • u := rfl
lemma shifted_inr (z : Fin 3 → ℂ) (i : Fin 3) (u : Dist) :
    shifted (A := Ext) de z i (inr u) = inr (sd z i u) := by
  simp only [shifted_apply,sd_apply,de_inr,inr_add,inr_smul]

lemma lapT_inr (z : Fin 3 → ℂ) (u : Dist) :
    lapT (shifted (A := Ext) de z) (inr u) = inr (lapd z u) := by
  simp only [lapT,lapd,shifted_inr,inr_sum]
lemma RT_inr (z : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (d : Dist) (i : Fin 3) :
    RT de (shifted (A := Ext) de z) (inl lam) (inl m) (fun j => inr (u j)) (inr d) i =
      inr (rd z lam m u d i) := by
  simp only [RT,cmT,rd,lapT_inr,shifted_inr,de_inl,← inl_add,inl_mul_inr,← inr_add,← inr_sum]
lemma ST_inr (z : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (d : Dist) :
    ST de (shifted (A := Ext) de z) (inl lam) (inl m) (fun j => inr (u j)) (inr d) =
      inr (scd z lam m u d) := by
  simp only [ElasticityAugmented.ST,scd,lap,lapT_inr,shifted_inr,de_inl,← inl_add,inl_mul_inr,
    ← inl_sum,← inr_sum]
  simp only [two_mul,← inr_add]
  congr 1
  ext φ
  simp only [add_apply]
  change _ = _ + (2 : ℂ) * ((∑ i, dc i (lam+m) • sd z i d) φ) +
    (2 : ℂ) * ((∑ i, dc i m • lapd z (u i)) φ) +
    (2 : ℂ) * ((∑ i, ∑ j, dc i (dc j m) • sd z i (u j)) φ) + _
  ring

lemma inl_two : inl (2 : Coeff) = (2 : Ext) := by
  exact inl_natCast 2
lemma coff_inl_mul (a b : Coeff) : (inl a : Ext)*inl b = inl (a*b) :=
  (inl_mul Dist a b).symm
lemma coff_inl_add (a b : Coeff) : (inl a : Ext)+inl b = inl (a+b) :=
  (inl_add Dist a b).symm
lemma coff_inl_sub (a b : Coeff) : (inl a : Ext)-inl b = inl (a-b) :=
  (inl_sub Dist a b).symm
lemma dist_inr_sub (u v : Dist) : (inr u : Ext)-inr v = inr (u-v) :=
  (inr_sub Coeff u v).symm
lemma coeff_two_smul (u : Dist) : (2 : Coeff) • u = (2 : ℂ) • u := by
  change TemperedDistribution.smulLeftCLM ℂ (fun _ : X => (2 : ℂ)) u = _
  rw [TemperedDistribution.smulLeftCLM_const]

lemma coeffA_inl (lam m n o : Coeff) (k : Fin 3) (i j : Fin 4) :
    coeffA (A := Ext) de (inl lam) (inl m) (inl n) (inl o) k i j = inl (coeffA dc lam m n o k i j) := by
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [coeffA,Fin.cons_zero,Fin.cons_succ,coff_inl_add,de_inl,coff_inl_mul,
      coff_inl_sub,← inl_two]
  · split_ifs <;> rfl
  · split_ifs <;> simp only [coff_inl_add,add_zero,zero_add,inl_zero]
lemma coeffV_inl (lam m n o : Coeff) (i j : Fin 4) :
    coeffV (A := Ext) de (inl lam) (inl m) (inl n) (inl o) i j = inl (coeffV dc lam m n o i j) := by
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [coeffV,lap,Fin.cons_zero,Fin.cons_succ,de_inl,coff_inl_mul,← inl_sum,
      coff_inl_sub,← inl_two,inl_zero]
lemma normalizedPair_inr (z : Fin 3 → ℂ) (lam m n o : Coeff) (u : Fin 3 → Dist) (d : Dist) (i : Fin 4) :
    normalizedPair de (shifted (A := Ext) de z) (inl lam) (inl m) (inl n) (inl o) (fun j => inr (u j)) (inr d) i =
      inr (normPair z lam m n o u d i) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [normalizedPair,normPair,Fin.cons_zero,ST_inr,RT_inr,de_inl,inl_mul_inr,
      ← inr_sum]
    rw [← inl_two,coff_inl_mul,inl_mul_inr,dist_inr_sub,inl_mul_inr]
    congr 1
    congr 1
    congr 1
    exact (mul_smul (2 : Coeff) n (∑ i, dc i m • rd z lam m u d i)).trans (coeff_two_smul _)
  · simp only [normalizedPair,normPair,Fin.cons_succ,RT_inr,inl_mul_inr]

/-- Genuine scalar-principal matrix form for the actual distribution system. -/
theorem normalized_matrix (z : Fin 3 → ℂ) (lam m n o : Coeff)
    (hn : n*m=1) (ho : o*(lam+m+m)=1) (U : Fin 4 → Dist) (i : Fin 4) :
    normPair z lam m n o (fun j => U j.succ) (U 0) i =
      lapd z (U i)+(∑ k, ∑ j, coeffA dc lam m n o k i j • sd z k (U j))+
        (∑ j, coeffV dc lam m n o i j • U j) := by
  have hn' : (inl n : Ext)*inl m=1 := by rw [coff_inl_mul,hn]; rfl
  have ho' : (inl o : Ext)*(inl lam+inl m+inl m)=1 := by
    rw [coff_inl_add,coff_inl_add,coff_inl_mul,ho]; rfl
  have h := normalizedPair_matrix de (shifted (A := Ext) de z) (inl lam) (inl m) (inl n) (inl o)
    hn' ho' (fun j => inr (U j)) i
  simp only [normalizedPair_inr,lapT_inr,coeffA_inl,coeffV_inl,shifted_inr,inl_mul_inr,
    ← inr_sum,← inr_add] at h
  exact congrArg TrivSqZeroExt.snd h
end ElasticityDistribution

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators

open scoped SchwartzMap LineDeriv BigOperators
open scoped SchwartzMap LineDeriv Laplacian BigOperators
namespace ElasticityDistribution
open ElasticityAugmented TemperedDistribution
namespace LocalEq
variable {Ω : Set X} {u v w u' v' : Dist}
lemma sub (h : LocalEq Ω u v) (h' : LocalEq Ω u' v') : LocalEq Ω (u-u') (v-v') := by
  intro φ hc hs
  simp only [sub_apply,h φ hc hs,h' φ hc hs]
lemma smul (h : LocalEq Ω u v) (c : ℂ) : LocalEq Ω (c • u) (c • v) := by
  intro φ hc hs
  simp only [smul_apply,h φ hc hs]
lemma sum {ι : Type*} (s : Finset ι) {a b : ι → Dist} (h : ∀ i ∈ s, LocalEq Ω (a i) (b i)) :
    LocalEq Ω (∑ i ∈ s, a i) (∑ i ∈ s, b i) := by
  intro φ hc hs
  simp only [sum_apply]
  exact Finset.sum_congr rfl (fun i hi => h i hi φ hc hs)
lemma coeff (h : LocalEq Ω u v) (a : Coeff) : LocalEq Ω (a • u) (a • v) := by
  intro φ hc hs
  change u (SchwartzMap.smulLeftCLM ℂ (eval a) φ) = v (SchwartzMap.smulLeftCLM ℂ (eval a) φ)
  apply h
  · simpa only [SchwartzMap.smulLeftCLM_apply (growth a),Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (hc.mul_left : HasCompactSupport (eval a * (φ : X → ℂ)))
  · simpa only [SchwartzMap.smulLeftCLM_apply (growth a),Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (tsupport_mul_subset_right (f := eval a) (g := (φ : X → ℂ))).trans hs
end LocalEq

lemma lapd_expand (z : Fin 3 → ℂ) (u : Dist) :
    lapd z u = Δ u + (∑ i, (2*z i) • dd i u)+(∑ i, z i*z i) • u := by
  have he (i : Fin 3) : sd z i (sd z i u)=dd i (dd i u)+(2*z i) • dd i u+(z i*z i) • u := by
    simp only [sd_apply,map_add,map_smul,smul_add,smul_smul]
    module
  rw [lapd]
  simp only [he,Finset.sum_add_distrib,← Finset.sum_smul]
  congr 2
  simpa only [dd_apply,e,EuclideanSpace.basisFun_apply] using
    (laplacian_eq_sum (EuclideanSpace.basisFun (Fin 3) ℝ) u).symm

end ElasticityDistribution

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_TransportAlgebra
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented
section CGO
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (D : Fin 3 → Derivation ℂ A A)

lemma RT_phase_polynomial (θ : Fin 3 → ℂ) (τ : ℂ) (lam m : A) (u : Fin 3 → A) (b : A) :
    RT D (shifted D (τ • θ)) lam m u b =
      (fun i => R D lam m u b i+τ • leadingR D θ lam m u b i+
        (τ*τ*(∑ j, θ j*θ j)) • (m*u i)) := by
  funext i
  simp only [RT,R,cmT,cm,lapT,lap,shifted_apply,direction,leadingR,
    Pi.smul_apply,smul_eq_mul,Fin.sum_univ_three,map_add,Derivation.map_smul,smul_add]
  simp only [Algebra.smul_def,map_add,map_mul]
  ring

lemma ST_phase_polynomial (θ : Fin 3 → ℂ) (τ : ℂ) (lam m : A) (u : Fin 3 → A) (b : A)
    (hD : ∀ i j f, D i (D j f)=D j (D i f)) :
    ST D (shifted D (τ • θ)) lam m u b = S D lam m u b+τ • leadingS D θ lam m u b+
      (τ*τ*(∑ j, θ j*θ j)) • ((lam+m+m)*b+2*∑ i, D i m*u i) := by
  simp only [ST,S,lapT,lap,shifted_apply,direction,leadingS,
    Pi.smul_apply,smul_eq_mul,Fin.sum_univ_three,map_add,Derivation.map_smul,smul_add]
  simp only [Algebra.smul_def,map_add,map_mul]
  rw [hD 1 0 m,hD 2 0 m,hD 2 1 m]
  ring

lemma RT_null_expansion (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0)
    (τ : ℂ) (lam m : A) (u : Fin 3 → A) (b : A) (i : Fin 3) :
    RT D (shifted D (τ • θ)) lam m u b i=R D lam m u b i+τ • leadingR D θ lam m u b i := by
  have hh := congrFun (RT_phase_polynomial D θ τ lam m u b) i
  simpa only [hθ,mul_zero,zero_smul,add_zero] using hh

lemma ST_null_expansion (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0)
    (τ : ℂ) (lam m : A) (u : Fin 3 → A) (b : A)
    (hD : ∀ i j f, D i (D j f)=D j (D i f)) :
    ST D (shifted D (τ • θ)) lam m u b=S D lam m u b+τ • leadingS D θ lam m u b := by
  simpa only [hθ,mul_zero,zero_smul,add_zero] using ST_phase_polynomial D θ τ lam m u b hD
end CGO
end ElasticityAugmented

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_WeakLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityDistribution

section
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open ElasticityAugmented TemperedDistribution TrivSqZeroExt

lemma complex_inr_smul (c : ℂ) (u : Dist) : (c • (inr u : Ext))=inr (c • u) := by
  exact (TrivSqZeroExt.inr_smul Coeff c u).symm

lemma direction_inr (θ : Fin 3 → ℂ) (u : Dist) :
    direction (A := Ext) de θ (inr u)=inr (directiond θ u) := by
  simp only [direction,directiond,de_inr,inr_smul,inr_sum]
lemma direction_inl (θ : Fin 3 → ℂ) (a : Coeff) :
    direction (A := Ext) de θ (inl a)=inl (direction dc θ a) := by
  simp only [direction,de_inl,inl_smul,inl_sum]
lemma leadingR_inr (θ : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (b : Dist) (i : Fin 3) :
    leadingR de θ (inl lam) (inl m) (fun j => inr (u j)) (inr b) i =
      inr (leadingRd θ lam m u b i) := by
  simp only [leadingR,leadingRd,direction_inr,direction_inl,← inl_two,
    coff_inl_mul,coff_inl_add,inl_mul_inr,de_inl,← inr_sum,← inr_add,complex_inr_smul]
lemma leadingS_inr (θ : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (b : Dist) :
    leadingS de θ (inl lam) (inl m) (fun j => inr (u j)) (inr b) =
      inr (leadingSd θ lam m u b) := by
  have hf : (4 : Ext)=inl (4 : Coeff) := (inl_natCast 4).symm
  simp only [leadingS,leadingSd,direction_inr,direction_inl,← inl_two,hf,
    coff_inl_mul,coff_inl_add,inl_mul_inr,de_inl,← inr_sum,← inr_add]

/-- Exact null-phase polynomial decomposition for the physical distributions. -/
theorem rd_null_expansion (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0)
    (τ : ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (b : Dist) (i : Fin 3) :
    rd (τ • θ) lam m u b i=rd 0 lam m u b i+τ • leadingRd θ lam m u b i := by
  have he := RT_null_expansion de θ hθ τ (inl lam) (inl m) (fun j => inr (u j)) (inr b) i
  have h0 := RT_inr 0 lam m u b i
  have ht : shifted (A := Ext) de 0=fun i => (de i).toLinearMap := by
    funext i
    apply LinearMap.ext
    intro a
    change de i a+(0 : ℂ) • a=de i a
    rw [zero_smul ℂ a,add_zero]
  rw [ht] at h0
  change R de (inl lam) (inl m) (fun j => inr (u j)) (inr b) i=_ at h0
  rw [RT_inr,h0,leadingR_inr,← inr_smul,← inr_add] at he
  exact congrArg TrivSqZeroExt.snd he

theorem scd_null_expansion (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0)
    (τ : ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (b : Dist) :
    scd (τ • θ) lam m u b=scd 0 lam m u b+τ • leadingSd θ lam m u b := by
  have he := ST_null_expansion de θ hθ τ (inl lam) (inl m) (fun j => inr (u j)) (inr b) de_commute
  have h0 := ST_inr 0 lam m u b
  have ht : shifted (A := Ext) de 0=fun i => (de i).toLinearMap := by
    funext i
    apply LinearMap.ext
    intro a
    change de i a+(0 : ℂ) • a=de i a
    rw [zero_smul ℂ a,add_zero]
  rw [ht] at h0
  change ElasticityAugmented.S de (inl lam) (inl m) (fun j => inr (u j)) (inr b)=_ at h0
  rw [ST_inr,h0,leadingS_inr,← inr_smul,← inr_add] at he
  exact congrArg TrivSqZeroExt.snd he

end
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators
open ElasticityAugmented
end ElasticityDistribution

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Smoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityDistribution
open Set TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators
open ElasticityAugmented

lemma lapd_null_direction (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (u : Dist) :
    lapd θ u=lapd 0 u+(2 : ℂ) • directiond θ u := by
  rw [lapd_expand,lapd_expand]
  ext φ
  simp only [hθ,Pi.zero_apply,mul_zero,Finset.sum_const_zero]
  unfold directiond
  simp [mul_smul,Finset.smul_sum]

lemma normPair_null_leading (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0)
    (lam m n o : Coeff) (U : Fin 4 → Dist) (i : Fin 4) :
    normPair θ lam m n o (fun j => U j.succ) (U 0) i=
      normPair 0 lam m n o (fun j => U j.succ) (U 0) i+leadingPair θ lam m n o U i := by
  have hr (j) : rd θ lam m (fun j => U j.succ) (U 0) j=
      rd 0 lam m (fun j => U j.succ) (U 0) j+leadingRd θ lam m (fun j => U j.succ) (U 0) j := by
    simpa only [one_smul] using rd_null_expansion θ hθ 1 lam m (fun j => U j.succ) (U 0) j
  have hs : scd θ lam m (fun j => U j.succ) (U 0)=
      scd 0 lam m (fun j => U j.succ) (U 0)+leadingSd θ lam m (fun j => U j.succ) (U 0) := by
    simpa only [one_smul] using scd_null_expansion θ hθ 1 lam m (fun j => U j.succ) (U 0)
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [normPair,leadingPair,Fin.cons_zero,hr,hs,smul_def,map_add,map_sub,map_sum,smul_add,Finset.sum_add_distrib]
    abel
  · simp only [normPair,leadingPair,Fin.cons_succ,hr,smul_def,map_add]

/-- The physical leading equations have a scalar planar principal part on all
four actual augmented entries. The constraint is retained separately. -/
theorem leadingPair_matrix (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0)
    (lam m n o : Coeff) (hn : n*m=1) (ho : o*(lam+m+m)=1)
    (U : Fin 4 → Dist) (i : Fin 4) :
    leadingPair θ lam m n o U i=(2 : ℂ) • directiond θ (U i)+
      ∑ k,∑ j,θ k • (coeffA dc lam m n o k i j • U j) := by
  have hz0 (k : Fin 3) (u : Dist) : sd (0 : Fin 3 → ℂ) k u=dd k u := by
    change dd k u+(0 : ℂ) • u=dd k u
    rw [zero_smul ℂ u,add_zero]
  have hz := normalized_matrix 0 lam m n o hn ho U i
  simp only [hz0] at hz
  have ht := normalized_matrix θ lam m n o hn ho U i
  rw [normPair_null_leading θ hθ,lapd_null_direction θ hθ] at ht
  simp only [sd_apply,smul_def,map_add,map_smul,Finset.sum_add_distrib] at ht
  apply add_left_cancel (a := normPair 0 lam m n o (fun j => U j.succ) (U 0) i)
  calc
    _ = _ := ht
    _ = _ := by
      rw [hz]
      simp only [smul_def]
      abel

lemma leading_matrix_local_oai {B : Set X} (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0)
    (lam m n o : Coeff) (hn : n*m=1) (ho : o*(lam+m+m)=1) (U : Fin 4 → Dist)
    (hr : ∀ i,LocalEq B (leadingRd θ lam m (fun j => U j.succ) (U 0) i) 0)
    (hs : LocalEq B (leadingSd θ lam m (fun j => U j.succ) (U 0)) 0) (i : Fin 4) :
    LocalEq B ((2 : ℂ) • directiond θ (U i)+
      ∑ k,∑ j,θ k • (coeffA dc lam m n o k i j • U j)) 0 := by
  rw [← leadingPair_matrix θ hθ lam m n o hn ho]
  refine Fin.cases ?_ (fun j => ?_) i
  · have hh := (hs.sub ((LocalEq.sum Finset.univ (fun j _ => (hr j).coeff (dc j m))).coeff n |>.smul 2)).coeff o
    simpa only [leadingPair,Fin.cons_zero,smul_def,map_zero,smul_zero,Finset.sum_const_zero,sub_zero] using hh
  · have hh := (hr j).coeff n
    simpa only [leadingPair,Fin.cons_succ,smul_def,map_zero] using hh
end ElasticityDistribution
open Set Filter TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators Topology

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityDistribution.leading_matrix_local_oai := @OAI.ElasticityDistribution.leading_matrix_local_oai
