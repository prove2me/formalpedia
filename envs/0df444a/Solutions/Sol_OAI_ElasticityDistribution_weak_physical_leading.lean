-- Prove2me | solution 1 for OAI.ElasticityDistribution.weak_physical_leading
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:38:33.815891+00:00
-- url     : https://prove2.me/submissions/f2bf5178-ca9c-4999-b996-c06038e00110

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
lemma refl (u : Dist) : LocalEq Ω u u := fun _ _ _ => rfl
lemma sub (h : LocalEq Ω u v) (h' : LocalEq Ω u' v') : LocalEq Ω (u-u') (v-v') := by
  intro φ hc hs
  simp only [sub_apply,h φ hc hs,h' φ hc hs]
lemma smul (h : LocalEq Ω u v) (c : ℂ) : LocalEq Ω (c • u) (c • v) := by
  intro φ hc hs
  simp only [smul_apply,h φ hc hs]
end LocalEq

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

lemma divergence_phase (θ : Fin 3 → ℂ) (τ : ℂ) (u : Fin 3 → Dist) :
    divd (τ • θ) u=divd 0 u+τ • normald θ u := by
  have hz (i : Fin 3) : sd 0 i (u i)=dd i (u i) := by
    change dd i (u i)+(0 : ℂ) • u i=dd i (u i)
    rw [zero_smul ℂ (u i),add_zero]
  simp only [divd,hz,sd_apply,Pi.smul_apply,smul_eq_mul,normald,
    Finset.sum_add_distrib,Finset.smul_sum,smul_smul]
end
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators
open ElasticityAugmented
lemma augEntry_apply (i : Fin 4) (U : AugHilbert) : augEntry i U=(U i : Dist) := rfl

lemma coeffCLM_apply (a : Coeff) (u : Dist) : coeffCLM a u=a • u := rfl
lemma ddCLM_apply (i : Fin 3) (u : Dist) : ddCLM i u=dd i u := rfl
lemma sdCLM_apply (z : Fin 3 → ℂ) (i : Fin 3) (u : Dist) : sdCLM z i u=sd z i u := rfl
lemma lapdCLM_apply (z : Fin 3 → ℂ) (u : Dist) : lapdCLM z u=lapd z u := by
  simp only [lapdCLM,lapd,sum_apply,ContinuousLinearMap.comp_apply,sdCLM_apply]
lemma directionCLM_apply (θ : Fin 3 → ℂ) (u : Dist) : directionCLM θ u=directiond θ u := by
  simp only [directionCLM,directiond,sum_apply,smul_apply,ddCLM_apply]

lemma rdCLM_apply (z : Fin 3 → ℂ) (lam m : Coeff) (i : Fin 3) (U : AugHilbert) :
    rdCLM z lam m i U=rd z lam m (fun j => (U j.succ : Dist)) (U 0 : Dist) i := by
  simp only [rdCLM,rd,add_apply,sum_apply,ContinuousLinearMap.comp_apply,
    coeffCLM_apply,lapdCLM_apply,sdCLM_apply,augEntry_apply]
lemma scdCLM_apply (z : Fin 3 → ℂ) (lam m : Coeff) (U : AugHilbert) :
    scdCLM z lam m U=scd z lam m (fun j => (U j.succ : Dist)) (U 0 : Dist) := by
  simp only [scdCLM,scd,add_apply,sum_apply,smul_apply,ContinuousLinearMap.comp_apply,
    coeffCLM_apply,lapdCLM_apply,sdCLM_apply,augEntry_apply]
lemma leadingRCLM_apply (θ : Fin 3 → ℂ) (lam m : Coeff) (i : Fin 3) (U : AugHilbert) :
    leadingRCLM θ lam m i U=leadingRd θ lam m (fun j => (U j.succ : Dist)) (U 0 : Dist) i := by
  simp only [leadingRCLM,leadingRd,add_apply,sum_apply,smul_apply,ContinuousLinearMap.comp_apply,
    coeffCLM_apply,directionCLM_apply,augEntry_apply]
lemma leadingSCLM_apply (θ : Fin 3 → ℂ) (lam m : Coeff) (U : AugHilbert) :
    leadingSCLM θ lam m U=leadingSd θ lam m (fun j => (U j.succ : Dist)) (U 0 : Dist) := by
  simp only [leadingSCLM,leadingSd,add_apply,sum_apply,ContinuousLinearMap.comp_apply,
    coeffCLM_apply,directionCLM_apply,augEntry_apply]
lemma normalCLM_apply (θ : Fin 3 → ℂ) (U : AugHilbert) :
    normalCLM θ U=normald θ (fun j => (U j.succ : Dist)) := by
  simp only [normalCLM,normald,sum_apply,smul_apply,augEntry_apply]
lemma divergenceCLM_apply (z : Fin 3 → ℂ) (U : AugHilbert) :
    divergenceCLM z U=divd z (fun j => (U j.succ : Dist)) := by
  simp only [divergenceCLM,divd,sum_apply,ContinuousLinearMap.comp_apply,sdCLM_apply,augEntry_apply]
end ElasticityDistribution
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

/-- The actual distributional lower-order terms disappear after transposing to
fixed tests. This is the passage used for physical transferred amplitudes. -/
theorem weak_local_equation {u : ℕ → H} {w : H}
    (hu : ∀ v, Tendsto (fun n => inner ℂ (u n) v) atTop (𝓝 (inner ℂ w v)))
    (A B : H →L[ℂ] 𝓢'(E,ℂ)) (Ω : Set E) (eps : ℕ → ℂ)
    (heps : Tendsto eps atTop (𝓝 0))
    (heq : ∀ n, ElasticityRegularity.LocalEqual Ω (A (u n)+eps n • B (u n)) 0) :
    ElasticityRegularity.LocalEqual Ω (A w) 0 := by
  intro φ hc hs
  have hh := (weak_distribution hu A φ).add (heps.mul (weak_distribution hu B φ))
  simp only [zero_mul,add_zero] at hh
  have hz : Tendsto (fun n => A (u n) φ+eps n*B (u n) φ) atTop (𝓝 (0 : ℂ)) := by
    have he (n : ℕ) : A (u n) φ+eps n*B (u n) φ=0 := heq n φ hc hs
    simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hh hz

end ElasticityWeakLimit
namespace ElasticityDistribution
open MeasureTheory TemperedDistribution Filter Topology
open scoped SchwartzMap InnerProductSpace
open ElasticityAugmented ElasticityWeakLimit

lemma scaled_null_sum (ε : ℂ) (hε : ε ≠ 0) (a b : Dist) :
    ε • (a+ε⁻¹ • b)=b+ε • a := by
  rw [smul_add,smul_smul,mul_inv_cancel₀ hε,one_smul]
  exact add_comm _ _
lemma complex_smul_zero (ε : ℂ) : ε • (0 : Dist)=0 := by
  exact @smul_zero ℂ Dist _ _ ε

/-- Weak physical transferred amplitudes satisfy the actual constrained leading
system, not an unconstrained augmented transport. -/
theorem weak_physical_leading_oai {U : ℕ → AugHilbert} {W : AugHilbert}
    (hU : ∀ v, Tendsto (fun n => inner ℂ (U n) v) atTop (𝓝 (inner ℂ W v)))
    (Ω : Set X) (eps : ℕ → ℂ) (heps : Tendsto eps atTop (𝓝 0))
    (hne : ∀ n, eps n ≠ 0) (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0)
    (lam m : Coeff)
    (hR : ∀ n i, LocalEq Ω (rd ((eps n)⁻¹ • θ) lam m
      (fun j => (U n j.succ : Dist)) (U n 0 : Dist) i) 0)
    (hS : ∀ n, LocalEq Ω (scd ((eps n)⁻¹ • θ) lam m
      (fun j => (U n j.succ : Dist)) (U n 0 : Dist)) 0)
    (hdiv : ∀ n, LocalEq Ω (divd ((eps n)⁻¹ • θ) (fun j => (U n j.succ : Dist)))
      (U n 0 : Dist)) :
    (∀ i, LocalEq Ω (leadingRd θ lam m (fun j => (W j.succ : Dist)) (W 0 : Dist) i) 0) ∧
    LocalEq Ω (leadingSd θ lam m (fun j => (W j.succ : Dist)) (W 0 : Dist)) 0 ∧
    LocalEq Ω (normald θ (fun j => (W j.succ : Dist))) 0 := by
  refine ⟨fun i => ?_,?_,?_⟩
  · have hh := weak_local_equation hU (leadingRCLM θ lam m i) (rdCLM 0 lam m i) Ω eps heps
    simp only [leadingRCLM_apply,rdCLM_apply] at hh
    apply hh
    intro n
    have h := (hR n i).smul (eps n)
    rw [rd_null_expansion θ hθ] at h
    rw [scaled_null_sum _ (hne n),complex_smul_zero] at h
    exact h
  · have hh := weak_local_equation hU (leadingSCLM θ lam m) (scdCLM 0 lam m) Ω eps heps
    simp only [leadingSCLM_apply,scdCLM_apply] at hh
    apply hh
    intro n
    have h := (hS n).smul (eps n)
    rw [scd_null_expansion θ hθ] at h
    rw [scaled_null_sum _ (hne n),complex_smul_zero] at h
    exact h
  · have hh := weak_local_equation hU (normalCLM θ) (divergenceCLM 0-augEntry 0) Ω eps heps
    simp only [normalCLM_apply,sub_apply,divergenceCLM_apply,augEntry_apply] at hh
    apply hh
    intro n
    have h := ((hdiv n).sub (LocalEq.refl (U n 0 : Dist))).smul (eps n)
    rw [divergence_phase] at h
    have he (a b c : Dist) : eps n • (a+(eps n)⁻¹ • b-c)=b+eps n • (a-c) := by
      rw [smul_sub,smul_add,smul_smul,mul_inv_cancel₀ (hne n),one_smul,smul_sub]
      abel
    rw [he,sub_self,complex_smul_zero] at h
    exact h
end ElasticityDistribution

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityDistribution.weak_physical_leading_oai := @OAI.ElasticityDistribution.weak_physical_leading_oai
