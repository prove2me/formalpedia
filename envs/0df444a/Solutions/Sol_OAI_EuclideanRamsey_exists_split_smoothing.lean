-- Prove2me | solution 1 for OAI.EuclideanRamsey.exists_split_smoothing
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:06:00.855434+00:00
-- url     : https://prove2.me/submissions/e729aa7b-67c4-48db-a6d9-9b1b88e6c224

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/DifferentialSplitting.lean:L230-L323
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.exists_split_smoothing. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Theorems.Thm_OAI_EuclideanRamsey_bilinear_matrix_pushforward
import Theorems.Thm_OAI_EuclideanRamsey_bilinear_orthonormal_trace
import Theorems.Thm_OAI_EuclideanRamsey_exists_radial_smoothing
import Theorems.Thm_OAI_EuclideanRamsey_hessianB_linear_comp
import Theorems.Thm_OAI_EuclideanRamsey_hessianB_prod_horizontal
import Theorems.Thm_OAI_EuclideanRamsey_hessianB_prod_vertical

-- ---- from OAI.Combinatorics.EuclideanRamsey.Hessian ----
namespace OAI

universe uDomain uCodomain uIndex uColor uAction

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial

open scoped BigOperators
open Matrix MeasureTheory
namespace EuclideanRamsey

section Hessian
variable {E : Type uDomain} {F : Type uCodomain} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma hessianB_eq (f : E → ℝ) (x v w : E) :
    hessianB f x v w = iteratedFDeriv ℝ 2 f x ![v,w] := by
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_one_apply]
  rfl

lemma hessianB_continuous {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (hessianB f) :=
  (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous_fderiv (by simp)

lemma hessianB_compact {f : E → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (hessianB f) := (hf.fderiv ℝ).fderiv ℝ

lemma hessianB_apply_continuous {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (v w : E) : Continuous (fun x => hessianB f x v w) :=
  ((hessianB_continuous hf).clm_apply continuous_const).clm_apply continuous_const

end Hessian

section Trace
variable {E : Type uDomain} {ι : Type uIndex} {κ : Type uColor} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [Fintype κ]

end Trace

section MatrixContraction

end MatrixContraction

section Split
variable {E : Type uDomain} {H : Type uAction} [AddCommGroup E] [Module ℝ E] [AddCommGroup H] [Module ℝ H]

end Split

end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.DifferentialSplitting ----
namespace OAI

universe uDomain uAction uVertical uCodomain

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory

open scoped BigOperators
open Matrix MeasureTheory
namespace EuclideanRamsey

section Operator
variable {E : Type uDomain} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}

lemma secondOperator_continuous (C : Matrix (Fin k) (Fin k) ℝ) (v : Fin k → E)
    {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (secondOperator C v f) := by
  unfold secondOperator
  apply continuous_const.mul
  apply continuous_finsetSum
  intro j hj
  apply continuous_finsetSum
  intro l hl
  exact continuous_const.mul (hessianB_apply_continuous hf _ _)

lemma secondOperator_compact (C : Matrix (Fin k) (Fin k) ℝ) (v : Fin k → E)
    {f : E → ℝ} (hf : HasCompactSupport f) : HasCompactSupport (secondOperator C v f) := by
  apply (hessianB_compact hf).comp_left (g := fun B => (1/2:ℝ)*∑ j, ∑ l, C j l*B (v j) (v l))
  simp

end Operator

section Scale
variable (H : Type uAction) (V : Type uVertical) [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ H] [FiniteDimensional ℝ V]

end Scale

section SplitDifferential
variable {k d : ℕ} {H : Type uAction} {V : Type uVertical}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

lemma split_differential
    (C : Matrix (Fin k) (Fin k) ℝ) (R : Matrix (Fin k) (Fin d) ℝ)
    (Z : Matrix (Fin k) (Fin k) ℝ)
    (hsplit : C = R*R.transpose+Z*C*Z.transpose)
    (e : (Fin k → ℝ) ≃L[ℝ] H×V) (eh : OrthonormalBasis (Fin d) ℝ H)
    (z : Fin k → V)
    (hR : ∀ j, e (fun l => R l j) = (eh j,0))
    (hZ : ∀ j, e (fun l => Z l j) = (0,z j))
    (f : H → ℝ) (g : V → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (t : ℝ) (ht : t ≠ 0) (x : Fin k → ℝ) :
    let et := e.trans (scaleVertical H V t ht)
    let b := (fun y : H×V => f y.1*g y.2) ∘ et
    secondOperator C (fun j => Pi.single j 1) b x =
      g (et x).2 * halfLaplacian f (et x).1 +
      t^2*f (et x).1*secondOperator C z g (et x).2 := by
  dsimp only
  let et := e.trans (scaleVertical H V t ht)
  let b := (fun y : H×V => f y.1*g y.2) ∘ et
  change secondOperator C (fun j => Pi.single j 1) b x = _
  have hfg : ContDiff ℝ (⊤ : ℕ∞) (fun y : H×V => f y.1*g y.2) :=
    (hf.comp contDiff_fst).mul (hg.comp contDiff_snd)
  have hb (v w : Fin k → ℝ) : hessianB b x v w =
      hessianB (fun y : H×V => f y.1*g y.2) (et x) (et v) (et w) :=
    hessianB_linear_comp hfg et.toContinuousLinearMap x v w
  have hhr (j : Fin d) : et (fun l => R l j) = (eh j,0) := by simp [et,hR]
  have hhz (j : Fin k) : et (fun l => Z l j) = (0,t • z j) := by simp [et,hZ]
  have hhor : ∑ j, hessianB b x (fun l => R l j) (fun l => R l j) =
      g (et x).2 * ∑ j, hessianB f (et x).1 (eh j) (eh j) := by
    simp only [hb, hhr, hessianB_prod_horizontal hf hg, Finset.mul_sum]
  have hver : ∑ j, ∑ l, C j l*hessianB b x (fun a => Z a j) (fun a => Z a l) =
      t^2*f (et x).1 * ∑ j, ∑ l, C j l*hessianB g (et x).2 (z j) (z l) := by
    simp only [hb, hhz, hessianB_prod_vertical hf hg, map_smul,
      _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro l hl
    ring
  unfold secondOperator
  have hcon : ∑ j, ∑ l, C j l*hessianB b x (Pi.single j 1) (Pi.single l 1) =
      (∑ j, hessianB b x (fun l => R l j) (fun l => R l j)) +
      ∑ j, ∑ l, C j l*hessianB b x (fun a => Z a j) (fun a => Z a l) := by
    conv_lhs => rw [hsplit]
    simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
    congr 1
    · have he := bilinear_matrix_pushforward (hessianB b x) R 1
      simpa [Matrix.one_apply] using he
    · exact bilinear_matrix_pushforward (hessianB b x) Z C
  rw [hcon, hhor, hver]
  have htrace := bilinear_orthonormal_trace (hessianB f (et x).1) eh (stdOrthonormalBasis ℝ H)
  rw [htrace]
  simp only [halfLaplacian, ← hessianB_eq]
  ring

end SplitDifferential
end EuclideanRamsey

open MeasureTheory
namespace EuclideanRamsey

lemma haar_linear_change {E : Type uDomain} {F : Type uCodomain}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (e : E ≃L[ℝ] F) (μ : Measure E) [μ.IsAddHaarMeasure]
    (ν : Measure F) [ν.IsAddHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ ∀ f : F → ℝ, Continuous f →
      (∫ x, f (e x) ∂μ) = c * ∫ y, f y ∂ν := by
  let : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  let c := (μ.map e).addHaarScalarFactor ν
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  refine ⟨c, by exact_mod_cast hc, ?_⟩
  intro f hf
  rw [← integral_map e.continuous.measurable.aemeasurable hf.aestronglyMeasurable,
    Measure.isAddLeftInvariant_eq_smul (μ.map e) ν]
  simp [c, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]

lemma compact_prod_mul {E : Type uDomain} {F : Type uCodomain} [TopologicalSpace E] [TopologicalSpace F]
    [R1Space E] [R1Space F] {f : E → ℝ} {g : F → ℝ}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    HasCompactSupport (fun x : E×F => f x.1*g x.2) := by
  apply HasCompactSupport.of_support_subset_isCompact (hf.prod hg)
  rintro ⟨x,y⟩ h
  have hx : f x ≠ 0 := by intro h0; exact h (by simp [h0])
  have hy : g y ≠ 0 := by intro h0; exact h (by simp [h0])
  exact ⟨subset_closure hx, subset_closure hy⟩

end EuclideanRamsey

open MeasureTheory
namespace EuclideanRamsey

lemma product_negative_integral_bound {E : Type uDomain} {F : Type uCodomain}
    [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (ν : Measure F) [SFinite μ] [SFinite ν]
    (f a w : E → ℝ) (g b : F → ℝ) (t : ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ y, 0 ≤ g y) (hw : ∀ x, 0 ≤ w x)
    (haI : Integrable (fun x => max (-a x) 0*w x) μ)
    (hfI : Integrable (fun x => f x*w x) μ)
    (hgI : Integrable g ν) (hbI : Integrable (fun y => |b y|) ν) :
    (∫ z : E×F, max (-(g z.2*a z.1+t^2*f z.1*b z.2)) 0*w z.1 ∂μ.prod ν) ≤
      (∫ x, max (-a x) 0*w x ∂μ)*(∫ y, g y ∂ν) +
      t^2*(∫ x, f x*w x ∂μ)*(∫ y, |b y| ∂ν) := by
  have hI := (haI.mul_prod hgI).add ((hfI.mul_prod hbI).const_mul (t^2))
  have hbound (z : E×F) :
      max (-(g z.2*a z.1+t^2*f z.1*b z.2)) 0*w z.1 ≤
      (max (-a z.1) 0*w z.1)*g z.2+t^2*((f z.1*w z.1)*|b z.2|) := by
    have h : max (-(g z.2*a z.1+t^2*f z.1*b z.2)) 0 ≤
        g z.2*max (-a z.1) 0+t^2*f z.1*|b z.2| := by
      apply max_le
      · have ha := le_max_left (-a z.1) 0
        have hb := neg_le_abs (b z.2)
        nlinarith [mul_le_mul_of_nonneg_left ha (hg z.2),
          mul_le_mul_of_nonneg_left hb (mul_nonneg (sq_nonneg t) (hf z.1))]
      · exact add_nonneg (mul_nonneg (hg z.2) (le_max_right _ _))
          (mul_nonneg (mul_nonneg (sq_nonneg t) (hf z.1)) (abs_nonneg _))
    calc
      _ ≤ (g z.2*max (-a z.1) 0+t^2*f z.1*|b z.2|)*w z.1 :=
        mul_le_mul_of_nonneg_right h (hw z.1)
      _ = _ := by ring
  refine (integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun z => mul_nonneg (le_max_right _ _) (hw z.1))) hI
    (Filter.Eventually.of_forall hbound)).trans_eq ?_
  change (∫ z : E×F, (max (-a z.1) 0*w z.1)*g z.2+
    t^2*((f z.1*w z.1)*|b z.2|) ∂μ.prod ν) = _
  rw [integral_add (haI.mul_prod hgI) ((hfI.mul_prod hbI).const_mul (t^2)),
    integral_const_mul, integral_prod_mul (fun x => max (-a x) 0*w x) g,
    integral_prod_mul (fun x => f x*w x) (fun y => |b y|)]
  ring

end EuclideanRamsey

namespace EuclideanRamsey
open MeasureTheory Matrix
open scoped BigOperators

lemma halfLaplacian_continuous {H : Type uAction} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] {f : H → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (halfLaplacian f) := by
  change Continuous (fun x => halfLaplacian f x)
  simp only [halfLaplacian, ← hessianB_eq]
  apply continuous_const.mul
  exact continuous_finsetSum _ (fun j hj => hessianB_apply_continuous hf _ _)

lemma halfLaplacian_compact {H : Type uAction} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] {f : H → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (halfLaplacian f) := by
  change HasCompactSupport (fun x => halfLaplacian f x)
  simp only [halfLaplacian, ← hessianB_eq]
  apply (hessianB_compact hf).comp_left
    (g := fun B => (1/2:ℝ)*∑ j, B (stdOrthonormalBasis ℝ H j) (stdOrthonormalBasis ℝ H j))
  simp

 theorem exists_split_smoothing {k d : ℕ} {H : Type uAction} {V : Type uVertical}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace H] [BorelSpace H] [MeasurableSpace V] [BorelSpace V]
    (hn : 1 ≤ Module.finrank ℝ H)
    (C : Matrix (Fin k) (Fin k) ℝ) (R : Matrix (Fin k) (Fin d) ℝ)
    (Z : Matrix (Fin k) (Fin k) ℝ)
    (hsplit : C = R*R.transpose+Z*C*Z.transpose)
    (e : (Fin k → ℝ) ≃L[ℝ] H×V) (eh : OrthonormalBasis (Fin d) ℝ H)
    (z : Fin k → V)
    (hR : ∀ j, e (fun l => R l j) = (eh j,0))
    (hZ : ∀ j, e (fun l => Z l j) = (0,z j))
    {η : ℝ} (hη : 0 < η) :
    ∃ b : (Fin k → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) b ∧ HasCompactSupport b ∧
      (∀ x, 0 ≤ b x) ∧ 0 < ∫ x, b x ∧
      (∫ x, max (-secondOperator C (fun j => Pi.single j 1) b x) 0 * ‖(e x).1‖^2) <
        η * ∫ x, b x := by
  let μH : Measure H := Measure.addHaar
  let μV : Measure V := Measure.addHaar
  obtain ⟨f,hfs,hfc,hfp,hfm,hfsmall⟩ := exists_radial_smoothing μH hn (η := η/2) (by positivity)
  let g₀ : ContDiffBump (0:V) := ⟨1,2,by norm_num,by norm_num⟩
  let g : V → ℝ := g₀
  have hgs : ContDiff ℝ (⊤ : ℕ∞) g := g₀.contDiff
  have hgc : HasCompactSupport g := g₀.hasCompactSupport
  have hgp : ∀ y, 0 ≤ g y := g₀.nonneg'
  have hgm : 0 < ∫ y, g y ∂μV := g₀.integral_pos
  let a := halfLaplacian f
  let bV := secondOperator C z g
  have hac : Continuous a := halfLaplacian_continuous hfs
  have hak : HasCompactSupport a := halfLaplacian_compact hfc
  have hbc : Continuous bV := secondOperator_continuous C z hgs
  have hbk : HasCompactSupport bV := secondOperator_compact C z hgc
  have haI : Integrable (fun x => max (-a x) 0*‖x‖^2) μH := by
    have hk : HasCompactSupport (fun x => max (-a x) 0) :=
      hak.comp_left (g := fun r : ℝ => max (-r) 0) (by simp)
    exact ((hac.neg.max continuous_const).mul (continuous_norm.pow 2)).integrable_of_hasCompactSupport hk.mul_right
  have hfI : Integrable (fun x => f x*‖x‖^2) μH :=
    (hfs.continuous.mul (continuous_norm.pow 2)).integrable_of_hasCompactSupport hfc.mul_right
  have hgI : Integrable g μV := hgs.continuous.integrable_of_hasCompactSupport hgc
  have hbI : Integrable (fun y => |bV y|) μV :=
    hbc.abs.integrable_of_hasCompactSupport hbk.abs
  let K := (∫ x, f x*‖x‖^2 ∂μH)*(∫ y, |bV y| ∂μV)
  have hK : 0 ≤ K := mul_nonneg
    (integral_nonneg (fun x => mul_nonneg (hfp x) (sq_nonneg _)))
    (integral_nonneg (fun y => abs_nonneg _))
  obtain ⟨t₀,ht₀,htsmall⟩ := exists_pos_mul_lt
    (mul_pos (mul_pos (show 0 < η/2 by positivity) hfm) hgm) (K+1)
  let t := min t₀ 1
  have ht : 0 < t := lt_min ht₀ zero_lt_one
  have ht1 : t ≤ 1 := min_le_right _ _
  have htt₀ : t ≤ t₀ := min_le_left _ _
  have hsmall : t^2*K < (η/2)*(∫ x,f x ∂μH)*(∫ y,g y ∂μV) := by
    have h : (K+1)*t ≤ (K+1)*t₀ := mul_le_mul_of_nonneg_left htt₀ (by linarith)
    have hsq : t^2 ≤ t := by nlinarith
    have hsqK := mul_le_mul_of_nonneg_right hsq hK
    nlinarith
  let et := e.trans (scaleVertical H V t ht.ne')
  let b := (fun y : H×V => f y.1*g y.2) ∘ et
  have hfgs : ContDiff ℝ (⊤ : ℕ∞) (fun y : H×V => f y.1*g y.2) :=
    (hfs.comp contDiff_fst).mul (hgs.comp contDiff_snd)
  have hbs : ContDiff ℝ (⊤ : ℕ∞) b := hfgs.comp et.contDiff
  have hbk' : HasCompactSupport b := (compact_prod_mul hfc hgc).comp_homeomorph et.toHomeomorph
  obtain ⟨c,hc,hchange⟩ := haar_linear_change et volume (μH.prod μV)
  have hmass : (∫ x,b x) = c*((∫ x,f x ∂μH)*(∫ y,g y ∂μV)) := by
    change (∫ x, f (et x).1*g (et x).2) = _
    rw [hchange _ hfgs.continuous, integral_prod_mul]
  have hetfst (x : Fin k → ℝ) : (et x).1 = (e x).1 := rfl
  have hdiff (x : Fin k → ℝ) : secondOperator C (fun j => Pi.single j 1) b x =
      g (et x).2*a (et x).1+t^2*f (et x).1*bV (et x).2 :=
    split_differential C R Z hsplit e eh z hR hZ f g hfs hgs t ht.ne' x
  let φ : H×V → ℝ := fun y => max (-(g y.2*a y.1+t^2*f y.1*bV y.2)) 0*‖y.1‖^2
  have hφ : Continuous φ := by
    dsimp [φ]
    exact ((((hgs.continuous.comp continuous_snd).mul (hac.comp continuous_fst)).add
      ((continuous_const.mul (hfs.continuous.comp continuous_fst)).mul
        (hbc.comp continuous_snd))).neg.max continuous_const).mul ((continuous_fst.norm).pow 2)
  have hneg : (∫ x, max (-secondOperator C (fun j => Pi.single j 1) b x) 0*‖(e x).1‖^2) =
      c*∫ y, φ y ∂μH.prod μV := by
    conv_lhs => arg 2; intro x; rw [hdiff, ← hetfst]
    exact hchange φ hφ
  have hbound := product_negative_integral_bound μH μV f a (fun x => ‖x‖^2) g bV t
    hfp hgp (fun x => sq_nonneg _) haI hfI hgI hbI
  have hfinal : (∫ y,φ y ∂μH.prod μV) < η*((∫ x,f x ∂μH)*(∫ y,g y ∂μV)) := by
    have hh := mul_lt_mul_of_pos_right hfsmall hgm
    change _ < η/2 * _ * _ at hh
    rw [mul_assoc (t^2)] at hbound
    change _ ≤ _ + t^2*K at hbound
    change _ < _ at hsmall
    dsimp only [φ] at *
    nlinarith
  refine ⟨b,hbs,hbk',fun x => mul_nonneg (hfp _) (hgp _),?_,?_⟩
  · rw [hmass]; positivity
  · rw [hneg,hmass]
    nlinarith [mul_lt_mul_of_pos_left hfinal hc]

end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open scoped BigOperators
open Matrix MeasureTheory
open MeasureTheory
open MeasureTheory
open MeasureTheory Matrix
open scoped BigOperators


theorem solution.{uAction,uVertical} : type_of% @_root_.OAI.EuclideanRamsey.exists_split_smoothing.{uAction,uVertical} := @_root_.OAI.EuclideanRamsey.exists_split_smoothing.{uAction,uVertical}
