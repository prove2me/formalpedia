-- Prove2me | solution 1 for OAI.ElasticityDistribution.normalized_quantitative_gain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:34:53.727467+00:00
-- url     : https://prove2.me/submissions/97a20c74-d0e0-4e23-9b16-a6a6100db566

import Mathlib
import Definitions.Def_OAIQ6El006
import Theorems.Thm_OAI_ElasticityDistribution_scalar_principal_quantitative_gain

section
-- module Solutions.OAIQ6_Elast.Elasticity_Augmented
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
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

open ElasticityAugmented TrivSqZeroExt

lemma de_fst (i : Fin 3) (v : Ext) : (de i v).fst = dc i v.fst := rfl
lemma de_snd (i : Fin 3) (v : Ext) : (de i v).snd = dd i v.snd := rfl
lemma de_inl (i : Fin 3) (a : Coeff) : de i (inl a) = inl (dc i a) := by
  apply TrivSqZeroExt.ext <;> simp [de_fst,de_snd]
lemma de_inr (i : Fin 3) (u : Dist) : de i (inr u) = inr (dd i u) := by
  apply TrivSqZeroExt.ext <;> simp [de_fst,de_snd]
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
-- module Solutions.OAIQ6_Elast.Elasticity_CGO
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityDistribution
open MeasureTheory TemperedDistribution

section
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open ElasticityAugmented ElasticityRegularity

lemma normalized_laplacian (z : Fin 3 → ℂ) (lam m n o : Coeff)
    (hn : n*m=1) (ho : o*(lam+m+m)=1) (U : Fin 4 → Dist) (i : Fin 4) :
    normPair z lam m n o (fun j => U j.succ) (U 0) i =
      Δ (U i)+lowerPart z (coeffA dc lam m n o) (coeffV dc lam m n o) U i := by
  rw [normalized_matrix z lam m n o hn ho,lapd_expand,lowerPart]
  abel

/-- The preceding estimate applies to the actual normalized physical system. -/
theorem normalized_quantitative_gain_oai (k : ℤ) {Ω : Set X} {χ η ξ : X → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcχ : HasCompactSupport χ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η)
    (hξ : ContDiff ℝ (⊤ : ℕ∞) ξ) (hcξ : HasCompactSupport ξ)
    (h1 : Set.EqOn η 1 (tsupport χ)) (h2 : Set.EqOn ξ 1 (tsupport η))
    (hsη : tsupport η ⊆ Ω) (lam m n o : Coeff) (hn : n*m=1) (ho : o*(lam+m+m)=1) :
    ∃ C : ℝ, 0<C ∧ ∀ (z : Fin 3 → ℂ) (U F : Fin 4 → Dist) (f g : HV),
      (∀ i, LocalEq Ω (normPair z lam m n o (fun j => U j.succ) (U 0) i) (F i)) →
      (∀ i, sobolevInjection (k : ℝ) (f i)=smulLeftCLM ℂ ξ (U i)) →
      (∀ i, sobolevInjection ((k : ℝ)-1) (g i)=smulLeftCLM ℂ η (F i)) →
      ∃ q : HV, (∀ i, sobolevInjection ((k : ℝ)+1) (q i)=smulLeftCLM ℂ χ (U i)) ∧
        ‖q‖ ≤ C*(1+∑ d, ‖z d‖)^2*(‖f‖+‖g‖) := by
  obtain ⟨C,hC,hgain⟩ := scalar_principal_quantitative_gain k hχ hcχ hη hcη hξ hcξ h1 h2 hsη
    (coeffA dc lam m n o) (coeffV dc lam m n o)
  refine ⟨C,hC,fun z U F f g heq hf hg => hgain z U F f g (fun i => ?_) hf hg⟩
  simpa only [normalized_laplacian z lam m n o hn ho] using heq i
end
open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal
open ElasticityAugmented ElasticityRegularity
end ElasticityDistribution

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityDistribution.normalized_quantitative_gain_oai := @OAI.ElasticityDistribution.normalized_quantitative_gain_oai
