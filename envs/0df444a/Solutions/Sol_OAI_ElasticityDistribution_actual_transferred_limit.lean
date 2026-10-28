-- Prove2me | solution 1 for OAI.ElasticityDistribution.actual_transferred_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:31:30.498086+00:00
-- url     : https://prove2.me/submissions/3c7fc2c1-7dc1-4974-b3d3-cce41070640a

import Mathlib
import Definitions.Def_ElasticityUniqueness
import Definitions.Def_OAIQ6El006
import Theorems.Thm_OAI_ElasticityDistribution_weak_physical_leading

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

section DifferentialAlgebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι : Type*} [Fintype ι]
variable (D : ι → Derivation ℂ A A)

omit [Fintype ι] in
lemma partial_mul (i : ι) (a b : A) : D i (a*b) = D i a*b + a*D i b := by
  simpa only [smul_eq_mul, add_comm, mul_comm] using (D i).leibniz a b

end DifferentialAlgebra

section CovariantAlgebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι : Type*} [Fintype ι]
variable (D : ι → Derivation ℂ A A) (T : ι → A →ₗ[ℂ] A)

variable (hD : ∀ i j f, D i (D j f) = D j (D i f))
variable (hT : ∀ i j f, T i (T j f) = T j (T i f))
variable (hTD : ∀ i a b, T i (a*b) = D i a*b+a*T i b)

include hT in
lemma covariant_div_lap (u : ι → A) : divT T (fun i => lapT T (u i)) = lapT T (divT T u) := by
  simp only [divT, lapT, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [hT i j, hT i j]

include hD hT hTD in
lemma covariant_div_cm (m : A) (u : ι → A) :
    divT T (cmT D T m u) =
    2*(∑ i, ∑ j, D i (D j m)*T i (u j)) +
      (∑ i, D i m*T i (divT T u)) + (∑ i, D i m*lapT T (u i)) := by
  have hH : (∑ i, ∑ j, D i (D j m)*T j (u i)) =
      ∑ i, ∑ j, D i (D j m)*T i (u j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hD j i]
  have hv : (∑ i, ∑ j, D j m * T i (T j (u i))) =
      ∑ j, D j m*T j (divT T u) := by
    rw [Finset.sum_comm]
    simp only [divT, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [hT i j]
  have hl : (∑ i, ∑ j, D j m * T i (T i (u j))) =
      ∑ j, D j m*lapT T (u j) := by
    rw [Finset.sum_comm]
    simp only [lapT, Finset.mul_sum]
  simp only [divT, cmT, map_sum, hTD, map_add, mul_add, Finset.sum_add_distrib]
  rw [hH, hv, hl]
  simp only [divT, map_sum]
  ring

include hD hT hTD in
/-- Compatibility after conjugation, proved for the genuine connection
Leibniz rule rather than falsely treating a shifted derivative as a derivation. -/
theorem covariant_augmented_identity (lam m : A) (u : ι → A) (d : A) :
    divT T (RT D T lam m u d) - ST D T lam m u d = PT D T m (divT T u-d) := by
  have hL := covariant_div_lap T hT u
  have hC := covariant_div_cm D T hD hT hTD m u
  simp only [divT] at hL hC
  simp only [divT, RT, map_add, hTD, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, hL, hC]
  simp only [ST, PT, lap, lapT, map_sub, map_add, map_sum, mul_sub, add_mul, mul_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  ring_nf
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  ring

include hT hTD in
lemma physical_conjugated_expansion (lam m : A) (u : ι → A) (i : ι) :
    LT T lam m u i = RT D T lam m u (divT T u) i := by
  have ht : (∑ j, T j (T i (u j))) = T i (divT T u) := by
    simp only [divT, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hT j i]
  simp only [LT, RT, hTD, map_add, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [ht]
  simp only [cmT, lapT, mul_add, Finset.sum_add_distrib]
  ring

omit [Fintype ι] in
lemma shifted_apply (z : ι → ℂ) (i : ι) (f : A) :
    shifted D z i f = D i f + z i • f := rfl

omit [Fintype ι] in
lemma shifted_mul (z : ι → ℂ) (i : ι) (a b : A) :
    shifted D z i (a*b) = D i a*b+a*shifted D z i b := by
  simp only [shifted_apply, partial_mul, Algebra.smul_def]
  ring

include hD in
omit [Fintype ι] in
lemma shifted_commute (z : ι → ℂ) (i j : ι) (f : A) :
    shifted D z i (shifted D z j f) = shifted D z j (shifted D z i f) := by
  simp only [shifted_apply, map_add, map_smul, smul_add, smul_smul, hD i j]
  simp only [Algebra.smul_def]
  ring_nf

theorem shifted_physical_expansion (z : ι → ℂ) (lam m : A) (u : ι → A)
    (hc : ∀ i j f, D i (D j f) = D j (D i f)) (i : ι) :
    LT (shifted D z) lam m u i = RT D (shifted D z) lam m u (divT (shifted D z) u) i :=
  physical_conjugated_expansion D (shifted D z) (shifted_commute D hc z) (shifted_mul D z) lam m u i

theorem shifted_physical_divergence (z : ι → ℂ) (lam m : A) (u : ι → A)
    (hc : ∀ i j f, D i (D j f) = D j (D i f)) :
    divT (shifted D z) (LT (shifted D z) lam m u) =
      ST D (shifted D z) lam m u (divT (shifted D z) u) := by
  have he := covariant_augmented_identity D (shifted D z) hc (shifted_commute D hc z)
    (shifted_mul D z) lam m u (divT (shifted D z) u)
  rw [sub_self] at he
  simp only [PT, lapT, map_zero, mul_zero, Finset.sum_const_zero, add_zero] at he
  rw [← sub_eq_zero]
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  funext i
  exact shifted_physical_expansion D z lam m u hc i

end CovariantAlgebra

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

namespace ElasticityPhysicalAlgebra
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder

lemma shiftD_apply (z : Fin 3 → ℂ) (i : Fin 3) (f : S) :
    shiftD z i f = d (e i) f + z i • f := rfl

end ElasticityPhysicalAlgebra

open scoped BigOperators

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
lemma divT_inr (z : Fin 3 → ℂ) (u : Fin 3 → Dist) :
    divT (shifted (A := Ext) de z) (fun i => inr (u i)) = inr (divd z u) := by
  simp only [divT,divd,shifted_inr,inr_sum]
lemma LT_inr (z : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (i : Fin 3) :
    LT (shifted (A := Ext) de z) (inl lam) (inl m) (fun j => inr (u j)) i = inr (phys z lam m u i) := by
  simp only [ElasticityAugmented.LT,phys,divT_inr,shifted_inr,inl_mul_inr,← inr_add,← inr_sum]
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

/-- The genuine distributional physical equation has the same compatible
augmented scalar-principal system as the smooth equation. No regularity of the
unknown is used in this differential identity. -/
theorem physical_expansion (z : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (i : Fin 3) :
    phys z lam m u i = rd z lam m u (divd z u) i := by
  have h := shifted_physical_expansion de z (inl lam) (inl m) (fun j => inr (u j)) de_commute i
  rw [LT_inr,divT_inr,RT_inr] at h
  exact congrArg TrivSqZeroExt.snd h

theorem physical_divergence (z : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) :
    divd z (phys z lam m u) = scd z lam m u (divd z u) := by
  have h := shifted_physical_divergence de z (inl lam) (inl m) (fun j => inr (u j)) de_commute
  have hL : ElasticityAugmented.LT (shifted (A := Ext) de z) (inl lam) (inl m) (fun j => inr (u j)) =
      (fun i => inr (phys z lam m u i)) := funext (LT_inr z lam m u)
  rw [hL,divT_inr,divT_inr,ST_inr] at h
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
namespace ElasticityRegularity


variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma derivative_support_subset (g : E → ℂ) (m : E) :
    tsupport (fun x => fderiv ℝ g x m) ⊆ tsupport g :=
  (tsupport_comp_subset (g := fun T : E →L[ℝ] ℂ => T m) (by simp) (fderiv ℝ g)).trans
    (tsupport_fderiv_subset ℝ)

end ElasticityRegularity

open scoped SchwartzMap LineDeriv BigOperators
open scoped SchwartzMap LineDeriv Laplacian BigOperators
namespace ElasticityDistribution
open ElasticityAugmented TemperedDistribution
namespace LocalEq
variable {Ω : Set X} {u v w u' v' : Dist}
lemma refl (u : Dist) : LocalEq Ω u u := fun _ _ _ => rfl
lemma add (h : LocalEq Ω u v) (h' : LocalEq Ω u' v') : LocalEq Ω (u+u') (v+v') := by
  intro φ hc hs
  simp only [add_apply,h φ hc hs,h' φ hc hs]
lemma smul (h : LocalEq Ω u v) (c : ℂ) : LocalEq Ω (c • u) (c • v) := by
  intro φ hc hs
  simp only [smul_apply,h φ hc hs]
lemma sum {ι : Type*} (s : Finset ι) {a b : ι → Dist} (h : ∀ i ∈ s, LocalEq Ω (a i) (b i)) :
    LocalEq Ω (∑ i ∈ s, a i) (∑ i ∈ s, b i) := by
  intro φ hc hs
  simp only [sum_apply]
  exact Finset.sum_congr rfl (fun i hi => h i hi φ hc hs)
lemma derivative (h : LocalEq Ω u v) (i : Fin 3) : LocalEq Ω (dd i u) (dd i v) := by
  intro φ hc hs
  change u (- ∂_{e i} φ) = v (- ∂_{e i} φ)
  apply h
  · change HasCompactSupport (fun x => -((∂_{e i} φ : Test) x))
    exact (hc.fderiv_apply (𝕜 := ℝ) (e i)).neg
  · change tsupport (-((∂_{e i} φ : Test) : X → ℂ)) ⊆ Ω
    rw [tsupport_neg]
    exact (ElasticityRegularity.derivative_support_subset (φ : X → ℂ) (e i)).trans hs
end LocalEq

lemma LocalEq.shifted {Ω : Set X} {u v : Dist} (h : LocalEq Ω u v) (z : Fin 3 → ℂ) (i : Fin 3) :
    LocalEq Ω (sd z i u) (sd z i v) :=
  (h.derivative i).add (h.smul (z i))
lemma LocalEq.divergence {Ω : Set X} {u v : Fin 3 → Dist} (h : ∀ i, LocalEq Ω (u i) (v i))
    (z : Fin 3 → ℂ) : LocalEq Ω (divd z u) (divd z v) :=
  LocalEq.sum Finset.univ (fun i _ => (h i).shifted z i)

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
-- module Solutions.OAIQ6_Elast.Elasticity_LocalRegularity
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal
namespace ElasticityRegularity


section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma distribution_schwartz_product {g : E → ℂ} (hg : g.HasTemperateGrowth) (u : 𝓢(E,ℂ)) :
    smulLeftCLM ℂ g (u : 𝓢'(E,ℂ)) = (SchwartzMap.smulLeftCLM ℂ g u : 𝓢'(E,ℂ)) := by
  ext φ
  simp only [smulLeftCLM_apply_apply,SchwartzMap.coe_apply,SchwartzMap.smulLeftCLM_apply_apply hg,
    smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

end

end ElasticityRegularity

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators ENNReal
namespace ElasticityDistribution
open ElasticityAugmented ElasticityPhysicalAlgebra ElasticityNegativeOrder

lemma coe_schwartz_add (u v : S) : ((u+v : S) : Dist)=(u : Dist)+(v : Dist) := map_add _ _ _
lemma coe_schwartz_smul (c : ℂ) (u : S) : ((c • u : S) : Dist)=c • (u : Dist) := map_smul _ _ _
lemma coe_schwartz_sum {ι : Type*} (s : Finset ι) (u : ι → S) :
    ((∑ i ∈ s, u i : S) : Dist)=∑ i ∈ s, (u i : Dist) := map_sum _ _ _
lemma sd_schwartz (z : Fin 3 → ℂ) (i : Fin 3) (u : S) :
    sd z i (u : Dist)=(shiftD z i u : Dist) := by
  rw [sd_apply,dd_apply,shiftD_apply,coe_schwartz_add,coe_schwartz_smul]
  congr 1
  exact TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq u (e i)
lemma coeff_schwartz (a : Coeff) (u : S) : a • (u : Dist)=(mult (eval a) u : Dist) :=
  ElasticityRegularity.distribution_schwartz_product (growth a) u
lemma divd_schwartz (z : Fin 3 → ℂ) (u : Fin 3 → S) :
    divd z (fun i => (u i : Dist))=(∑ i, shiftD z i (u i) : S) := by
  rw [divd,coe_schwartz_sum]
  simp only [sd_schwartz]
lemma phys_schwartz (z : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → S) (i : Fin 3) :
    phys z lam m (fun j => (u j : Dist)) i=(physical z (eval lam) (eval m) u i : Dist) := by
  simp only [phys,physical,divd_schwartz,sd_schwartz,← coe_schwartz_add,
    coeff_schwartz,← coe_schwartz_sum]

end ElasticityDistribution

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_WeakSolutions
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Set SchwartzMap TemperedDistribution
open scoped BigOperators SchwartzMap LineDeriv
namespace Elasticity
open ElasticityDistribution
variable {Ω : Set X}
lemma localEq_of_schwartz_eqOn {F G : SchwartzMap X ℂ} (h : Set.EqOn (F : X → ℂ) G Ω) :
    LocalEq Ω (F : Dist) (G : Dist) := by
  intro φ _ hs
  change (∫ x, φ x*F x)=(∫ x, φ x*G x)
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    change φ x*F x=φ x*G x
    by_cases hx : x∈Ω
    · rw [h hx]
    · rw [image_eq_zero_of_notMem_tsupport (f := (φ : X → ℂ)) (fun hg => hx (hs hg)),zero_mul,zero_mul])
end Elasticity

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Transfer
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators SchwartzMap
namespace ElasticityCGO
open ElasticityAugmented
open ElasticityPhysicalAlgebra (toSmooth toSmooth_apply physical phase)
open ElasticityDistribution (finiteResidual)

lemma phase_eq (h : ℝ) (α β : X) :
    phase h α β=(h : ℂ)⁻¹ • (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) := by
  funext i
  simp only [phase,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
end ElasticityCGO

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

namespace ElasticityCGO

section
open Set Filter MeasureTheory
open scoped SchwartzMap Topology BigOperators ENNReal
open ElasticityAugmented
open ElasticityBessel (L2 norm2 J)
open ElasticityNegativeOrder (mult sobNorm)
open ElasticityPhysicalAlgebra (divShift)
open ElasticityPhysicalEstimate (physicalAug)
open ElasticityDistribution (AugHilbert)

lemma augEmbed_apply (u : Fin 4 → S) (i : Fin 4) : augEmbed u i=L2 (u i) := rfl

end
open Set MeasureTheory Filter
open scoped SchwartzMap Topology BigOperators
open ElasticityAugmented
open ElasticityCoeffBounds (ExteriorConstant)
open ElasticityBessel (L2 norm2)
open ElasticityNegativeOrder (mult sobNorm)
open ElasticityPhysicalAlgebra (phase physical)
open ElasticityPhysicalEstimate (physicalAug)

end ElasticityCGO
namespace ElasticityWeakLimit
open Filter Topology
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Bounded physical amplitudes admit a common weak subsequence in the genuine
Hilbert space. For several columns, take their finite Hilbert product. -/
theorem bounded_weak_subsequence [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (u : ℕ → H) (C : ℝ) (hC : ∀ n, ‖u n‖ ≤ C) :
    ∃ w : H, ‖w‖ ≤ C ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ v : H, Tendsto (fun n => inner ℂ (u (σ n)) v) atTop (𝓝 (inner ℂ w v)) := by
  let f : ℕ → WeakDual ℂ H := fun n => StrongDual.toWeakDual (InnerProductSpace.toDual ℂ H (u n))
  have hf : ∀ n, f n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ H) C := by
    intro n
    simpa only [Set.mem_preimage,Metric.mem_closedBall,dist_zero_right,
      f,StrongDual.toStrongDual_toWeakDual,LinearIsometryEquiv.norm_map] using hC n
  obtain ⟨w,hw,σ,hσ,hlim⟩ := (WeakDual.isSeqCompact_closedBall (𝕜 := ℂ) (E := H) 0 C) hf
  refine ⟨(InnerProductSpace.toDual ℂ H).symm w.toStrongDual,?_,σ,hσ,fun v => ?_⟩
  · simpa only [Set.mem_preimage,Metric.mem_closedBall,dist_zero_right,
      LinearIsometryEquiv.norm_map] using hw
  · have he := (WeakDual.eval_continuous v).tendsto w |>.comp hlim
    rw [InnerProductSpace.toDual_symm_apply]
    exact he

end ElasticityWeakLimit
namespace ElasticityWeakLimit
open MeasureTheory TemperedDistribution Filter Topology
open scoped SchwartzMap InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
lemma weak_scalar {u : ℕ → H} {w : H}
    (hu : ∀ v, Tendsto (fun n => inner ℂ (u n) v) atTop (𝓝 (inner ℂ w v)))
    (L : H →L[ℂ] ℂ) : Tendsto (fun n => L (u n)) atTop (𝓝 (L w)) := by
  let v := (InnerProductSpace.toDual ℂ H).symm L
  have he (x : H) : L x=inner ℂ v x := (InnerProductSpace.toDual_symm_apply (y := L) (x := x)).symm
  simp only [he]
  have hh := (continuous_star.tendsto (inner ℂ w v)).comp (hu v)
  change Tendsto (fun n => star (inner ℂ (u n) v)) atTop (𝓝 (star (inner ℂ w v))) at hh
  have hs (a b : H) : star (inner ℂ a b)=inner ℂ b a := inner_conj_symm (𝕜 := ℂ) b a
  simpa only [hs] using hh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma weak_distribution {u : ℕ → H} {w : H}
    (hu : ∀ v, Tendsto (fun n => inner ℂ (u n) v) atTop (𝓝 (inner ℂ w v)))
    (A : H →L[ℂ] 𝓢'(E,ℂ)) (φ : 𝓢(E,ℂ)) :
    Tendsto (fun n => A (u n) φ) atTop (𝓝 (A w φ)) := by
  let L : H →L[ℂ] ℂ := (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).comp A
  exact weak_scalar hu L

end ElasticityWeakLimit
section
open MeasureTheory TemperedDistribution Filter Topology
open scoped SchwartzMap InnerProductSpace ENNReal
namespace ElasticityWeakLimit
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exterior data need only converge in distributions. In particular, this
retains the finite-amplitude and correction terms of the physical CGO sequence
until after the weak limit, rather than replacing them by their leading value. -/
theorem weak_moving_local_agreement {u : ℕ → H} {w : H}
    (hu : ∀ v, Tendsto (fun n => inner ℂ (u n) v) atTop (𝓝 (inner ℂ w v)))
    (A : H →L[ℂ] 𝓢'(E,ℂ)) (Ω : Set E) (f : ℕ → 𝓢'(E,ℂ)) (g : 𝓢'(E,ℂ))
    (hf : ∀ φ, Tendsto (fun n => f n φ) atTop (𝓝 (g φ)))
    (heq : ∀ n, ElasticityRegularity.LocalEqual Ω (A (u n)) (f n)) :
    ElasticityRegularity.LocalEqual Ω (A w) g := by
  intro φ hc hs
  have htest (n : ℕ) : A (u n) φ=f n φ := heq n φ hc hs
  have ht : Tendsto (fun n => A (u n) φ) atTop (𝓝 (g φ)) := by
    simpa only [htest] using hf φ
  exact tendsto_nhds_unique (weak_distribution hu A φ) ht
end ElasticityWeakLimit

namespace ElasticityDistribution
open ElasticityAugmented ElasticityWeakLimit

/-- Actual coefficientwise physical equations survive bounded weak extraction,
including the divergence constraint and the varying physical exterior data.
The bound is a premise here: deriving it from the DN transfer and its compact
Carleman estimate remains separate and is not identified with the main theorem. -/
theorem bounded_physical_limit
    (U : ℕ → AugHilbert) (C : ℝ) (hbound : ∀ n, ‖U n‖≤C)
    (Ω E : Set X) (eps : ℕ → ℂ) (heps : Tendsto eps atTop (𝓝 0))
    (hne : ∀ n,eps n≠0) (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0)
    (lam m : Coeff)
    (hR : ∀ n i,LocalEq Ω (rd ((eps n)⁻¹ • θ) lam m
      (fun j => (U n j.succ : Dist)) (U n 0 : Dist) i) 0)
    (hS : ∀ n,LocalEq Ω (scd ((eps n)⁻¹ • θ) lam m
      (fun j => (U n j.succ : Dist)) (U n 0 : Dist)) 0)
    (hdiv : ∀ n,LocalEq Ω (divd ((eps n)⁻¹ • θ) (fun j => (U n j.succ : Dist)))
      (U n 0 : Dist))
    (F : ℕ → Fin 4 → Dist) (a : Fin 4 → Dist)
    (hF : ∀ i φ,Tendsto (fun n => F n i φ) atTop (𝓝 (a i φ)))
    (hext : ∀ n i,LocalEq E (U n i : Dist) (F n i)) :
    ∃ W : AugHilbert,‖W‖≤C ∧
      (∀ i,LocalEq Ω (leadingRd θ lam m (fun j => (W j.succ : Dist)) (W 0 : Dist) i) 0) ∧
      LocalEq Ω (leadingSd θ lam m (fun j => (W j.succ : Dist)) (W 0 : Dist)) 0 ∧
      LocalEq Ω (normald θ (fun j => (W j.succ : Dist))) 0 ∧
      (∀ i,LocalEq E (W i : Dist) (a i)) ∧
      ∃ σ : ℕ → ℕ,StrictMono σ ∧
        ∀ v,Tendsto (fun n => inner ℂ (U (σ n)) v) atTop (𝓝 (inner ℂ W v)) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have : TopologicalSpace.SeparableSpace (Lp ℂ 2 (volume : Measure X)) := inferInstance
  have : TopologicalSpace.SeparableSpace AugHilbert := inferInstance
  obtain ⟨W,hW,σ,hσ,hw⟩ := bounded_weak_subsequence U C hbound
  have ht := hσ.tendsto_atTop
  obtain ⟨hr,hs,hd⟩ := weak_physical_leading hw Ω (fun n => eps (σ n))
    (heps.comp ht) (fun n => hne (σ n)) θ hθ lam m
    (fun n => hR (σ n)) (fun n => hS (σ n)) (fun n => hdiv (σ n))
  refine ⟨W,hW,hr,hs,hd,fun i => ?_,σ,hσ,hw⟩
  have he := weak_moving_local_agreement hw (augEntry i) E (fun n => F (σ n) i) (a i)
    (fun φ => (hF i φ).comp ht) (fun n => hext (σ n) i)
  exact he
end ElasticityDistribution

end
namespace ElasticityDistribution

section
open Set MeasureTheory TemperedDistribution
open scoped SchwartzMap BigOperators
open ElasticityAugmented
open ElasticityCGO (augEmbed)
open ElasticityPhysicalEstimate (physicalAug)

lemma augEmbed_distribution (u : Fin 4 → SchwartzMap X ℂ) (i : Fin 4) :
    (augEmbed u i : Dist)=(u i : Dist) :=
  Lp.toTemperedDistribution_toLp_eq (u i)

/-- The scalar entry of the actual augmented amplitude is its actual physical
shifted divergence. Both physical equations, including the scalar consequence,
are thereby inherited by the same L2 object used in weak extraction. -/
theorem actual_augmented_equations {B : Set X} (z : Fin 3 → ℂ) (lam m : Coeff)
    (u : Fin 3 → SchwartzMap X ℂ)
    (hu : ∀ i,EqOn (ElasticityPhysicalAlgebra.physical z (eval lam) (eval m) u i : X → ℂ) 0 B) :
    let U := augEmbed (physicalAug z u)
    (∀ i,LocalEq B (rd z lam m (fun j => (U j.succ : Dist)) (U 0 : Dist) i) 0) ∧
    LocalEq B (scd z lam m (fun j => (U j.succ : Dist)) (U 0 : Dist)) 0 ∧
    LocalEq B (divd z (fun j => (U j.succ : Dist))) (U 0 : Dist) := by
  intro U
  have he (i : Fin 3) : (U i.succ : Dist)=(u i : Dist) := augEmbed_distribution _ _
  have hd : (U 0 : Dist)=divd z (fun i => (u i : Dist)) := by
    rw [augEmbed_distribution,divd_schwartz]
    rfl
  simp only [he,hd]
  have hp (i) : LocalEq B (phys z lam m (fun j => (u j : Dist)) i) 0 := by
    rw [phys_schwartz]
    have hh := Elasticity.localEq_of_schwartz_eqOn (F := ElasticityPhysicalAlgebra.physical z
      (eval lam) (eval m) u i) (G := 0) (hu i)
    simpa only [map_zero] using hh
  refine ⟨fun i => ?_,?_,LocalEq.refl _⟩
  · rw [← physical_expansion]
    exact hp i
  · rw [← physical_divergence]
    have hh := LocalEq.divergence hp z
    simpa only [divd,map_zero,Finset.sum_const_zero] using hh

lemma actual_augmented_exterior {K : Set X} (z : Fin 3 → ℂ)
    (u v : Fin 3 → SchwartzMap X ℂ)
    (hs : ∀ i,tsupport (v i-u i : SchwartzMap X ℂ)⊆K) :
    ∀ i,LocalEq Kᶜ (augEmbed (physicalAug z v) i : Dist) (augEmbed (physicalAug z u) i : Dist) := by
  have hh (j : Fin 3) : LocalEq Kᶜ (v j : Dist) (u j : Dist) := by
    apply Elasticity.localEq_of_schwartz_eqOn
    intro x hx
    have hz : (v j-u j) x=0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (hs j hh))
    exact sub_eq_zero.mp hz
  intro i
  simp only [augEmbed_distribution]
  refine Fin.cases ?_ (fun j => hh j) i
  change LocalEq Kᶜ (ElasticityPhysicalAlgebra.divShift z v : Dist)
    (ElasticityPhysicalAlgebra.divShift z u : Dist)
  have hd := LocalEq.divergence hh z
  simpa only [divd_schwartz,ElasticityPhysicalAlgebra.divShift] using hd

end
open Set Filter MeasureTheory TemperedDistribution
open scoped SchwartzMap Topology BigOperators
open ElasticityAugmented
open ElasticityCGO (augEmbed)
open ElasticityBessel (L2)
open ElasticityPhysicalEstimate (physicalAug)
open ElasticityPhysicalAlgebra (phase physical)

/-- Weak transport extraction for the literal transferred physical sequence.
The exterior leading value follows from strong convergence of the actual
source augmented amplitudes, not from dropping CGO remainders by definition. -/
theorem actual_transferred_limit_oai (B K : Set X) (α β : X)
    (hθ : ∑ i,((α i : ℂ)+Complex.I*(β i : ℂ))*((α i : ℂ)+Complex.I*(β i : ℂ))=0)
    (lam m : Coeff) (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ n,h n≠0)
    (u v : ℕ → Fin 3 → SchwartzMap X ℂ) (a : Fin 4 → SchwartzMap X ℂ)
    (hv : ∀ n i,EqOn (physical (phase (h n) α β) (eval lam) (eval m) (v n) i : X → ℂ) 0 B)
    (hs : ∀ n i,tsupport (v n i-u n i : SchwartzMap X ℂ)⊆K)
    (C : ℝ) (hC : ∀ n,‖augEmbed (physicalAug (phase (h n) α β) (v n))‖≤C)
    (ha : ∀ i,Tendsto (fun n => L2 (physicalAug (phase (h n) α β) (u n) i)) atTop (𝓝 (L2 (a i)))) :
    ∃ W : AugHilbert,
      (∀ i,LocalEq B (leadingRd (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) lam m
        (fun j => (W j.succ : Dist)) (W 0 : Dist) i) 0) ∧
      LocalEq B (leadingSd (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) lam m
        (fun j => (W j.succ : Dist)) (W 0 : Dist)) 0 ∧
      LocalEq B (normald (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) (fun j => (W j.succ : Dist))) 0 ∧
      ∀ i,LocalEq Kᶜ (W i : Dist) (a i : Dist) := by
  let U := fun n => augEmbed (physicalAug (phase (h n) α β) (v n))
  have hh' : Tendsto (fun n => (h n : ℂ)) atTop (𝓝 0) := by
    simpa only [Complex.ofReal_zero,Function.comp_def] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hh
  have heq (n) := actual_augmented_equations (phase (h n) α β) lam m (v n) (hv n)
  have hF (i : Fin 4) (φ : 𝓢(X,ℂ)) :
      Tendsto (fun n => (augEmbed (physicalAug (phase (h n) α β) (u n)) i : Dist) φ)
        atTop (𝓝 ((a i : Dist) φ)) := by
    let A : Lp ℂ 2 (volume : Measure X) →L[ℂ] ℂ :=
      (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).comp
        (Lp.toTemperedDistributionCLM ℂ (volume : Measure X) 2)
    have ht := A.continuous.continuousAt.tendsto.comp (ha i)
    simp only [A,Function.comp_def,ContinuousLinearMap.comp_apply,
      PointwiseConvergenceCLM.evalCLM_apply,Lp.toTemperedDistributionCLM_apply,
      ElasticityCGO.augEmbed_apply,ElasticityBessel.L2,SchwartzMap.toLpCLM_apply,
      Lp.toTemperedDistribution_toLp_eq] at ht ⊢
    exact ht
  obtain ⟨W,_hW,hr,hs',hn,hext,_hseq⟩ := bounded_physical_limit U C hC B Kᶜ
    (fun n => (h n : ℂ)) hh' (fun n => Complex.ofReal_ne_zero.mpr (hne n)) _ hθ lam m
    (fun n i => by simpa only [← ElasticityCGO.phase_eq] using (heq n).1 i)
    (fun n => by simpa only [← ElasticityCGO.phase_eq] using (heq n).2.1)
    (fun n => by simpa only [← ElasticityCGO.phase_eq] using (heq n).2.2)
    (fun n i => (augEmbed (physicalAug (phase (h n) α β) (u n)) i : Dist))
    (fun i => (a i : Dist)) hF (fun n => actual_augmented_exterior _ (u n) (v n) (hs n))
  exact ⟨W,hr,hs',hn,hext⟩

end ElasticityDistribution

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityDistribution.actual_transferred_limit_oai := @OAI.ElasticityDistribution.actual_transferred_limit_oai
