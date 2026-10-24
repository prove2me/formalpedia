-- Prove2me | solution 1 for OAI.SharpLiebThirring.ActionProof.matrix_compact_penalty
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T13:59:50.070548+00:00
-- url     : https://prove2.me/submissions/cbcd868b-3640-417e-b003-d516a92d21af

import Mathlib
import Definitions.Def_OAIQWSLT000
import Theorems.Thm_OAI_SharpLiebThirring_MatrixProof_hilbertSchmidt_cfc_sub_le

section
-- module Solutions.OAIQW_LiebThirring.MatrixOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
namespace SharpLiebThirring


/-! ## The matrix field and action -/


open Matrix Unitary
namespace MatrixProof
variable {n : Type u1} [Fintype n] [DecidableEq n]

lemma monotone_sub_mul_nonneg {f : ℝ → ℝ} (hf : Monotone f) (x y : ℝ) :
    0 ≤ (f x - f y) * (x - y) := by
  rcases le_total x y with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hf h)) (sub_nonpos.mpr h)
  · exact mul_nonneg (sub_nonneg.mpr (hf h)) (sub_nonneg.mpr h)

omit [DecidableEq n] in
lemma trace_star_mul_sum (A B : Matrix n n ℂ) :
    (trace (star A * B)).re = ∑ i, ∑ j, (star (A i j) * B i j).re := by
  simp only [trace, diag, mul_apply, star_eq_conjTranspose, conjTranspose_apply,
    Complex.re_sum, Complex.star_def]
  exact Finset.sum_comm

lemma trace_star_mul_change (U V : unitary (Matrix n n ℂ)) (A B : Matrix n n ℂ) :
    trace (star (star (U : Matrix n n ℂ) * A * (V : Matrix n n ℂ)) *
      (star (U : Matrix n n ℂ) * B * (V : Matrix n n ℂ))) = trace (star A * B) := by
  have hu : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 :=
    Unitary.mul_star_self_of_mem U.property
  have hv : (V : Matrix n n ℂ) * star (V : Matrix n n ℂ) = 1 :=
    Unitary.mul_star_self_of_mem V.property
  simp only [star_mul, star_star]
  calc
    _ = trace (star (V : Matrix n n ℂ) * (star A *
          ((U : Matrix n n ℂ) * star (U : Matrix n n ℂ))) * B * (V : Matrix n n ℂ)) := by
      congr 1
      noncomm_ring
    _ = trace (star (V : Matrix n n ℂ) * (star A * B) * (V : Matrix n n ℂ)) := by simp [hu, mul_assoc]
    _ = trace ((V : Matrix n n ℂ) * star (V : Matrix n n ℂ) * (star A * B)) :=
      trace_mul_cycle _ _ _
    _ = trace (star A * B) := by rw [hv, one_mul]

lemma mixed_diagonal_sub (U V : unitary (Matrix n n ℂ)) (a b : n → ℝ) :
    star (U : Matrix n n ℂ) *
      (conjStarAlgAut ℂ (Matrix n n ℂ) U (diagonal (fun i ↦ (a i : ℂ))) -
        conjStarAlgAut ℂ (Matrix n n ℂ) V (diagonal (fun i ↦ (b i : ℂ)))) * (V : Matrix n n ℂ) =
      diagonal (fun i ↦ (a i : ℂ)) * (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) -
        (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) * diagonal (fun i ↦ (b i : ℂ)) := by
  simp only [conjStarAlgAut_apply]
  calc
    _ = (star (U : Matrix n n ℂ) * (U : Matrix n n ℂ)) * diagonal (fun i ↦ (a i : ℂ)) *
          (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) -
          (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) * diagonal (fun i ↦ (b i : ℂ)) *
          (star (V : Matrix n n ℂ) * (V : Matrix n n ℂ)) := by noncomm_ring
    _ = _ := by simp only [Unitary.coe_star_mul_self, one_mul, mul_one]

lemma mixed_diagonal_sub_apply (U V : unitary (Matrix n n ℂ)) (a b : n → ℝ)
    (i j : n) :
    (star (U : Matrix n n ℂ) *
      (conjStarAlgAut ℂ (Matrix n n ℂ) U (diagonal (fun i ↦ (a i : ℂ))) -
        conjStarAlgAut ℂ (Matrix n n ℂ) V (diagonal (fun i ↦ (b i : ℂ)))) * (V : Matrix n n ℂ)) i j =
      ((a i - b j : ℝ) : ℂ) * (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) i j := by
  rw [mixed_diagonal_sub]
  simp only [Matrix.sub_apply, diagonal_mul, mul_diagonal, Complex.ofReal_sub]
  ring

lemma trace_functional_monotonicity {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {f : ℝ → ℝ} (hf : Monotone f) :
    0 ≤ (trace ((hA.cfc f - hB.cfc f) * (A - B))).re := by
  let U := hA.eigenvectorUnitary
  let V := hB.eigenvectorUnitary
  let a := hA.eigenvalues
  let b := hB.eigenvalues
  have hfab : (hA.cfc f - hB.cfc f).IsHermitian := by
    apply IsHermitian.sub
    · rw [← hA.cfc_eq]
      exact (cfc_predicate f A).isHermitian
    · rw [← hB.cfc_eq]
      exact (cfc_predicate f B).isHermitian
  have ha : A = conjStarAlgAut ℂ (Matrix n n ℂ) U (diagonal (fun i ↦ (a i : ℂ))) :=
    hA.spectral_theorem
  have hb : B = conjStarAlgAut ℂ (Matrix n n ℂ) V (diagonal (fun i ↦ (b i : ℂ))) :=
    hB.spectral_theorem
  have hfm (i j : n) :
      (star (U : Matrix n n ℂ) * (hA.cfc f - hB.cfc f) * (V : Matrix n n ℂ)) i j =
        ((f (a i) - f (b j) : ℝ) : ℂ) *
          (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) i j := by
    exact mixed_diagonal_sub_apply U V (f ∘ a) (f ∘ b) i j
  have hm (i j : n) :
      (star (U : Matrix n n ℂ) * (A - B) * (V : Matrix n n ℂ)) i j =
        ((a i - b j : ℝ) : ℂ) * (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) i j := by
    rw [ha, hb]
    exact mixed_diagonal_sub_apply U V a b i j
  rw [← hfab.star_eq, ← trace_star_mul_change U V, trace_star_mul_sum]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  rw [hfm, hm]
  have heq (s t : ℝ) (z : ℂ) :
      (star ((s : ℂ) * z) * ((t : ℂ) * z)).re = (s * t) * Complex.normSq z := by
    simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
    ring
  rw [heq]
  exact mul_nonneg (monotone_sub_mul_nonneg hf _ _) (Complex.normSq_nonneg _)


lemma trace_unitary_conjugate (U : unitary (Matrix n n ℂ)) (A : Matrix n n ℂ) :
    trace (conjStarAlgAut ℂ (Matrix n n ℂ) U A) = trace A := by
  simp only [conjStarAlgAut_apply]
  rw [trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

lemma trace_conjugate_pair (U : unitary (Matrix n n ℂ)) (F A : Matrix n n ℂ) :
    trace (conjStarAlgAut ℂ (Matrix n n ℂ) U F * A) =
      trace (F * conjStarAlgAut ℂ (Matrix n n ℂ) (star U) A) := by
  simp only [conjStarAlgAut_apply, Unitary.coe_star, star_star]
  calc
    _ = trace ((U : Matrix n n ℂ) * (F * (star (U : Matrix n n ℂ) * A))) := by
      congr 1
      noncomm_ring
    _ = trace ((F * (star (U : Matrix n n ℂ) * A)) * (U : Matrix n n ℂ)) :=
      trace_mul_comm _ _
    _ = _ := by congr 1; noncomm_ring

lemma trace_conjugate_difference (U : unitary (Matrix n n ℂ)) (F A : Matrix n n ℂ) :
    trace ((conjStarAlgAut ℂ (Matrix n n ℂ) U F - F) * (conjStarAlgAut ℂ (Matrix n n ℂ) U A - A)) =
      trace (F * (2 • A - conjStarAlgAut ℂ (Matrix n n ℂ) U A -
        conjStarAlgAut ℂ (Matrix n n ℂ) (star U) A)) := by
  have h1 : trace (conjStarAlgAut ℂ (Matrix n n ℂ) U F * conjStarAlgAut ℂ (Matrix n n ℂ) U A) =
      trace (F * A) := by
    rw [← map_mul, trace_unitary_conjugate]
  simp only [mul_sub, sub_mul, trace_sub, h1, trace_conjugate_pair, two_smul,
    mul_add, trace_add]
  ring

lemma functional_unitary_conjugate {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (U : unitary (Matrix n n ℂ)) (f : ℝ → ℝ) :
    (hermitian_unitary_conjugate hA U).cfc f = conjStarAlgAut ℂ (Matrix n n ℂ) U (hA.cfc f) := by
  rw [← IsHermitian.cfc_eq, ← hA.cfc_eq]
  symm
  exact StarAlgHomClass.map_cfc (conjStarAlgAut ℂ (Matrix n n ℂ) U) f A
    (A.finite_real_spectrum.continuousOn f) (by
      change Continuous (fun X : Matrix n n ℂ ↦ conjStarAlgAut ℂ (Matrix n n ℂ) U X)
      simp only [conjStarAlgAut_apply]
      fun_prop) hA
    (hermitian_unitary_conjugate hA U)

/-- The fixed-unitary trace comparison used before averaging. -/
lemma trace_unitary_comparison {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {f : ℝ → ℝ} (hf : Monotone f) (U : unitary (Matrix n n ℂ)) :
    0 ≤ (trace (hA.cfc f * (2 • A - conjStarAlgAut ℂ (Matrix n n ℂ) U A -
      conjStarAlgAut ℂ (Matrix n n ℂ) (star U) A))).re := by
  have h := trace_functional_monotonicity (hermitian_unitary_conjugate hA U) hA hf
  rw [functional_unitary_conjugate, trace_conjugate_difference] at h
  exact h

/-- Removing any invariant part, such as (s I - B)^2, is an exact identity. -/
lemma conjugate_difference_sub_invariant (U : unitary (Matrix n n ℂ))
    (D Y : Matrix n n ℂ) (hY : conjStarAlgAut ℂ (Matrix n n ℂ) U Y = Y) :
    2 • (D + Y) - conjStarAlgAut ℂ (Matrix n n ℂ) U (D + Y) -
        conjStarAlgAut ℂ (Matrix n n ℂ) (star U) (D + Y) =
      2 • D - conjStarAlgAut ℂ (Matrix n n ℂ) U D - conjStarAlgAut ℂ (Matrix n n ℂ) (star U) D := by
  have hYs : conjStarAlgAut ℂ (Matrix n n ℂ) (star U) Y = Y := by
    calc
      _ = conjStarAlgAut ℂ (Matrix n n ℂ) (star U) (conjStarAlgAut ℂ (Matrix n n ℂ) U Y) := by rw [hY]
      _ = Y := by rw [← conjStarAlgAut_mul_apply]; simp
  rw [map_add, map_add, hY, hYs]
  simp only [two_smul]
  abel

lemma trace_unitary_comparison_sub_invariant {D Y : Matrix n n ℂ}
    (hA : (D + Y).IsHermitian) {f : ℝ → ℝ} (hf : Monotone f)
    (U : unitary (Matrix n n ℂ)) (hY : conjStarAlgAut ℂ (Matrix n n ℂ) U Y = Y) :
    0 ≤ (trace (hA.cfc f * (2 • D - conjStarAlgAut ℂ (Matrix n n ℂ) U D -
      conjStarAlgAut ℂ (Matrix n n ℂ) (star U) D))).re := by
  have h := trace_unitary_comparison hA hf U
  rwa [conjugate_difference_sub_invariant U D Y hY] at h


lemma hsSquared_cfc_sub {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ i j, |f (hA.eigenvalues i) - f (hB.eigenvalues j)| ≤
      L * |hA.eigenvalues i - hB.eigenvalues j|) :
    hsSquared (hA.cfc f - hB.cfc f) ≤ L ^ 2 * hsSquared (A - B) :=
  hilbertSchmidt_cfc_sub_le hA hB f L hL hf

open MeasureTheory
open scoped Matrix.Norms.L2Operator NNReal

/-- Trace comparison commutes with limits in matrix norm. -/
lemma trace_unitary_comparison_limit {ι : Type u2} {l : Filter ι} [l.NeBot]
    {F : ι → Matrix n n ℂ} {M D : Matrix n n ℂ}
    (hlim : Filter.Tendsto F l (nhds M)) (U : unitary (Matrix n n ℂ))
    (hF : ∀ᶠ i in l, 0 ≤ (trace (F i * (2 • D - conjStarAlgAut ℂ (Matrix n n ℂ) U D -
      conjStarAlgAut ℂ (Matrix n n ℂ) (star U) D))).re) :
    0 ≤ (trace (M * (2 • D - conjStarAlgAut ℂ (Matrix n n ℂ) U D -
      conjStarAlgAut ℂ (Matrix n n ℂ) (star U) D))).re := by
  apply ge_of_tendsto ?_ hF
  have hc : Continuous (fun X : Matrix n n ℂ ↦
      (trace (X * (2 • D - conjStarAlgAut ℂ (Matrix n n ℂ) U D -
        conjStarAlgAut ℂ (Matrix n n ℂ) (star U) D))).re) := by
    unfold trace diag
    fun_prop
  exact hc.continuousAt.tendsto.comp hlim

/-- The integration step in `trace-average`, for any symmetric probability
average. The symmetry needed is expressed by equality of the two integrals. -/
lemma trace_comparison_average {α : Type u3} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (U : α → unitary (Matrix n n ℂ))
    (M D : Matrix n n ℂ)
    (hU : Integrable (fun t ↦ conjStarAlgAut ℂ (Matrix n n ℂ) (U t) D) ν)
    (hUs : Integrable (fun t ↦ conjStarAlgAut ℂ (Matrix n n ℂ) (star (U t)) D) ν)
    (hsym : (∫ t, conjStarAlgAut ℂ (Matrix n n ℂ) (star (U t)) D ∂ν) =
      ∫ t, conjStarAlgAut ℂ (Matrix n n ℂ) (U t) D ∂ν)
    (hpoint : ∀ᵐ t ∂ν, 0 ≤ (trace (M * (2 • D - conjStarAlgAut ℂ (Matrix n n ℂ) (U t) D -
      conjStarAlgAut ℂ (Matrix n n ℂ) (star (U t)) D))).re) :
    (trace (M * (∫ t, conjStarAlgAut ℂ (Matrix n n ℂ) (U t) D ∂ν))).re ≤
      (trace (M * D)).re := by
  have hi : Integrable (fun t ↦ 2 • D - conjStarAlgAut ℂ (Matrix n n ℂ) (U t) D -
      conjStarAlgAut ℂ (Matrix n n ℂ) (star (U t)) D) ν :=
    ((integrable_const (2 • D)).sub hU).sub hUs
  have hn := integral_nonneg_of_ae hpoint
  change 0 ≤ ∫ t, tracePairCLM M
    (2 • D - conjStarAlgAut ℂ (Matrix n n ℂ) (U t) D - conjStarAlgAut ℂ (Matrix n n ℂ) (star (U t)) D) ∂ν at hn
  rw [(tracePairCLM M).integral_comp_comm hi,
    integral_sub (f := fun t ↦ 2 • D - conjStarAlgAut ℂ (Matrix n n ℂ) (U t) D)
      ((integrable_const (2 • D)).sub hU) hUs,
    integral_sub (f := fun _ : α ↦ 2 • D) (integrable_const (2 • D)) hU, integral_const, probReal_univ,
    one_smul, hsym, map_sub, map_sub, map_nsmul] at hn
  norm_num only [tracePairCLM_apply, nsmul_eq_mul, Nat.cast_ofNat] at hn
  linarith


lemma phaseUnitary_conj_apply (z : n → ℝ) (t : ℝ) (D : Matrix n n ℂ) (i j : n) :
    conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) D i j =
      Complex.exp (((z i - z j) * t : ℝ) * Complex.I) * D i j := by
  simp only [conjStarAlgAut_apply, phaseUnitary, star_eq_conjTranspose,
    diagonal_conjTranspose, diagonal_mul, mul_diagonal]
  simp only [Pi.star_apply]
  rw [Complex.star_def, ← Complex.exp_conj]
  calc _ = (Complex.exp (((t * z i : ℝ) : ℂ) * Complex.I) *
      Complex.exp (starRingEnd ℂ (((t * z j : ℝ) : ℂ) * Complex.I))) * D i j := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring

lemma phaseUnitary_star (z : n → ℝ) (t : ℝ) :
    star (phaseUnitary z t) = phaseUnitary z (-t) := by
  apply Subtype.ext
  simp only [Unitary.coe_star, phaseUnitary, star_eq_conjTranspose, diagonal_conjTranspose]
  congr 1
  funext i
  simp only [Pi.star_apply]
  rw [Complex.star_def, ← Complex.exp_conj]
  simp

lemma continuous_phase_conj (z : n → ℝ) (D : Matrix n n ℂ) :
    Continuous (fun t : ℝ ↦ conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) D) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp_rw [phaseUnitary_conj_apply]
  fun_prop

lemma integrable_phase_conj (z : n → ℝ) (D : Matrix n n ℂ) (ν : Measure ℝ)
    [IsFiniteMeasure ν] :
    Integrable (fun t ↦ conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) D) ν := by
  apply Integrable.of_bound (continuous_phase_conj z D).aestronglyMeasurable ‖D‖
  filter_upwards [] with t
  change ‖(phaseUnitary z t : Matrix n n ℂ) * D *
    ((star (phaseUnitary z t) : unitary (Matrix n n ℂ)) : Matrix n n ℂ)‖ ≤ ‖D‖
  rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]

lemma gaussian_phase_average (z : n → ℝ) (D : Matrix n n ℂ) (v : ℝ≥0) (i j : n) :
    (∫ t, conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) D ∂ProbabilityTheory.gaussianReal 0 v) i j =
      Complex.exp (-((v : ℝ) * (z i - z j) ^ 2 / 2 : ℝ)) * D i j := by
  have h := (entryCLM i j).integral_comp_comm
    (integrable_phase_conj z D (ProbabilityTheory.gaussianReal 0 v))
  simp only [entryCLM_apply] at h
  rw [← h]
  simp_rw [phaseUnitary_conj_apply]
  rw [integral_mul_const]
  simp only [Complex.ofReal_mul]
  rw [← charFun_apply_real, ProbabilityTheory.charFun_gaussianReal]
  congr 2
  push_cast
  ring

lemma gaussian_phase_star_average (z : n → ℝ) (D : Matrix n n ℂ) (v : ℝ≥0) :
    (∫ t, conjStarAlgAut ℂ (Matrix n n ℂ) (star (phaseUnitary z t)) D
      ∂ProbabilityTheory.gaussianReal 0 v) =
      ∫ t, conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) D
        ∂ProbabilityTheory.gaussianReal 0 v := by
  simp_rw [phaseUnitary_star]
  have hm : (ProbabilityTheory.gaussianReal 0 v).map (fun x : ℝ ↦ -x) =
      ProbabilityTheory.gaussianReal 0 v := by
    simpa using (ProbabilityTheory.gaussianReal_map_neg (μ := 0) (v := v))
  have he := integral_map (μ := ProbabilityTheory.gaussianReal 0 v)
    (φ := fun x : ℝ ↦ -x) (by fun_prop)
    ((continuous_phase_conj z D).aestronglyMeasurable
      (μ := (ProbabilityTheory.gaussianReal 0 v).map (fun x : ℝ ↦ -x)))
  rw [hm] at he
  exact he.symm

lemma integrable_gaussian_phase_star (z : n → ℝ) (D : Matrix n n ℂ) (v : ℝ≥0) :
    Integrable (fun t ↦ conjStarAlgAut ℂ (Matrix n n ℂ) (star (phaseUnitary z t)) D)
      (ProbabilityTheory.gaussianReal 0 v) := by
  simp_rw [phaseUnitary_star]
  have hm : (ProbabilityTheory.gaussianReal 0 v).map (fun x : ℝ ↦ -x) =
      ProbabilityTheory.gaussianReal 0 v := by
    simpa using (ProbabilityTheory.gaussianReal_map_neg (μ := 0) (v := v))
  have hi := integrable_phase_conj z D (ProbabilityTheory.gaussianReal 0 v)
  rw [← hm] at hi
  exact hi.comp_measurable (by fun_prop)

/-- The Gaussian stage of the even-unitary trace contraction. -/
lemma gaussian_trace_comparison (z : n → ℝ) (M D : Matrix n n ℂ) (v : ℝ≥0)
    (hpoint : ∀ t : ℝ, 0 ≤ (trace (M * (2 • D -
      conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) D -
      conjStarAlgAut ℂ (Matrix n n ℂ) (star (phaseUnitary z t)) D))).re) :
    (trace (M * (∫ t, conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) D
      ∂ProbabilityTheory.gaussianReal 0 v))).re ≤ (trace (M * D)).re := by
  exact trace_comparison_average (ProbabilityTheory.gaussianReal 0 v)
    (phaseUnitary z) M D (integrable_phase_conj z D _)
    (integrable_gaussian_phase_star z D v) (gaussian_phase_star_average z D v)
    (Filter.Eventually.of_forall hpoint)

end MatrixProof

open MeasureTheory Set Filter
open scoped Topology
namespace ScalarProof

lemma primitive_deriv (σ : ℝ) {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    deriv (regularizedPrimitive σ δ) y = (max y 0 + δ) ^ (σ - 3 / 2) :=
  (primitive_hasDerivAt σ hδ y).deriv

lemma primitive_strictMono (σ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    StrictMono (regularizedPrimitive σ δ) := by
  apply strictMono_of_deriv_pos
  intro y
  rw [primitive_deriv σ hδ]
  exact Real.rpow_pos_of_pos (by positivity) _

lemma primitive_concave {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) :
    ConcaveOn ℝ univ (regularizedPrimitive σ δ) := by
  apply Antitone.concaveOn_univ_of_deriv (primitive_differentiable σ hδ)
  intro x y hxy
  rw [primitive_deriv σ hδ, primitive_deriv σ hδ]
  exact Real.rpow_le_rpow_of_nonpos (by positivity)
    (add_le_add (max_le_max hxy le_rfl) le_rfl) (by linarith)

lemma normalization_integral_pos {σ : ℝ} (hσ : σ < 1) :
    0 < ∫ s : ℝ, (1 + s ^ 2) ^ (σ - 3 / 2) := by
  apply integral_pos_iff_support_of_nonneg
    (fun s ↦ Real.rpow_nonneg (by positivity) _)
    (normalization_integrable hσ) |>.2
  have hs : Function.support (fun s : ℝ ↦ (1 + s ^ 2) ^ (σ - 3 / 2)) = univ := by
    ext s
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (Real.rpow_pos_of_pos (by positivity) _).ne'
  rw [hs]
  simp

lemma normalization_pos {σ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) :
    0 < fieldNormalization σ :=
  div_pos hσ₀ (normalization_integral_pos hσ₁)


/-- A global comparison with the Japanese-bracket integrable majorant, including
negative shifts. It supplies all scalar dominated-convergence bounds. -/
lemma shifted_base_lower {δ : ℝ} (hδ : 0 < δ) (z s : ℝ) :
    (δ / (δ + |z| + 1)) * (1 + s ^ 2) ≤ max (s ^ 2 + z) 0 + δ := by
  have hd : 0 < δ + |z| + 1 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hd]
  have hm : 0 ≤ max (s ^ 2 + z) 0 := le_max_right _ _
  have hh : s ^ 2 ≤ max (s ^ 2 + z) 0 + |z| := by
    have := le_max_left (s ^ 2 + z) 0
    have := neg_le_abs z
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hh hδ.le,
    mul_nonneg (abs_nonneg z) hm, mul_nonneg (abs_nonneg z) hδ.le]

lemma shifted_derivative_integrable {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z : ℝ) :
    Integrable (fun s : ℝ ↦ (max (s ^ 2 + z) 0 + δ) ^ (σ - 3 / 2)) := by
  have ha : 0 < δ / (δ + |z| + 1) := by positivity
  refine ((normalization_integrable hσ).const_mul
    ((δ / (δ + |z| + 1)) ^ (σ - 3 / 2))).mono' ?_ ?_
  · exact ((derivative_continuous σ hδ).comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards [] with s
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    rw [← Real.mul_rpow ha.le (by positivity : 0 ≤ 1 + s ^ 2)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (shifted_base_lower hδ z s) (by linarith)

lemma primitive_difference_bound {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z s : ℝ) :
    ‖regularizedPrimitive σ δ (s ^ 2 + z) - regularizedPrimitive σ δ (s ^ 2)‖ ≤
      (max (s ^ 2 - |z|) 0 + δ) ^ (σ - 3 / 2) * |z| := by
  have hd : ∀ y ∈ Ici (s ^ 2 - |z|),
      ‖(max y 0 + δ) ^ (σ - 3 / 2)‖ ≤
        (max (s ^ 2 - |z|) 0 + δ) ^ (σ - 3 / 2) := by
    intro y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (add_le_add (max_le_max hy le_rfl) le_rfl) (by linarith)
  have hs : s ^ 2 ∈ Ici (s ^ 2 - |z|) := by
    simp only [mem_Ici]
    have := abs_nonneg z
    linarith
  have hsz : s ^ 2 + z ∈ Ici (s ^ 2 - |z|) := by
    simp only [mem_Ici]
    have := neg_le_abs z
    linarith
  simpa only [add_sub_cancel_left, Real.norm_eq_abs] using
    (convex_Ici (s ^ 2 - |z|)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y _ ↦ (primitive_hasDerivAt σ hδ y).hasDerivWithinAt) hd hs hsz

lemma mu_integrand_integrable {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z : ℝ) :
    Integrable (fun s : ℝ ↦ regularizedPrimitive σ δ (s ^ 2 + z) -
      regularizedPrimitive σ δ (s ^ 2)) := by
  have hi := (shifted_derivative_integrable hσ hδ (-|z|)).mul_const |z|
  refine hi.mono' ?_ (Filter.Eventually.of_forall ?_)
  · exact (((primitive_differentiable σ hδ).continuous.comp (by fun_prop)).sub
      ((primitive_differentiable σ hδ).continuous.comp (by fun_prop))).aestronglyMeasurable
  · intro s
    simpa only [sub_eq_add_neg] using primitive_difference_bound hσ hδ z s

lemma mu_hasDerivAt_integral {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z : ℝ) :
    HasDerivAt (scalarMu σ δ)
      (fieldNormalization σ * ∫ s : ℝ, (max (s ^ 2 + z) 0 + δ) ^ (σ - 3 / 2)) z := by
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (s := Ioi (z - 1)) (x₀ := z)
    (F := fun y s : ℝ ↦ regularizedPrimitive σ δ (s ^ 2 + y) -
      regularizedPrimitive σ δ (s ^ 2))
    (F' := fun y s : ℝ ↦ (max (s ^ 2 + y) 0 + δ) ^ (σ - 3 / 2))
    (bound := fun s : ℝ ↦ (max (s ^ 2 + (z - 1)) 0 + δ) ^ (σ - 3 / 2))
    (Ioi_mem_nhds (by linarith))
    (Filter.Eventually.of_forall (fun y ↦ (mu_integrand_integrable hσ hδ y).aestronglyMeasurable))
    (mu_integrand_integrable hσ hδ z)
    (shifted_derivative_integrable hσ hδ z).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun s y hy ↦ ?_))
    (shifted_derivative_integrable hσ hδ (z - 1))
    (Filter.Eventually.of_forall (fun s y _ ↦ ?_))
  · exact hh.2.const_mul (fieldNormalization σ)
  · change z - 1 < y at hy
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (add_le_add (max_le_max (by linarith) le_rfl) le_rfl) (by linarith)
  · simpa using ((primitive_hasDerivAt σ hδ (s ^ 2 + y)).comp y
      ((hasDerivAt_id y).const_add (s ^ 2))).sub_const (regularizedPrimitive σ δ (s ^ 2))

lemma mu_strictMono {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ) :
    StrictMono (scalarMu σ δ) := by
  apply strictMono_of_deriv_pos
  intro z
  rw [(mu_hasDerivAt_integral hσ₁ hδ z).deriv]
  apply mul_pos (normalization_pos hσ₀ hσ₁)
  apply (integral_pos_iff_support_of_nonneg
    (fun s ↦ Real.rpow_nonneg (by positivity) _)
    (shifted_derivative_integrable hσ₁ hδ z)).2
  have hs : Function.support (fun s : ℝ ↦ (max (s ^ 2 + z) 0 + δ) ^ (σ - 3 / 2)) = univ := by
    ext s
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (Real.rpow_pos_of_pos (by positivity) _).ne'
  rw [hs]
  simp

/-- The scaling integral used in the evaluation of the scalar field. -/
lemma quadratic_integral_scale (t : ℝ) {a : ℝ} (ha : 0 < a) :
    (∫ s : ℝ, (s ^ 2 + a) ^ t) =
      a ^ (t + 1 / 2) * ∫ s : ℝ, (1 + s ^ 2) ^ t := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have he (s : ℝ) : (s ^ 2 + a) ^ t =
      a ^ t * (1 + (s / Real.sqrt a) ^ 2) ^ t := by
    rw [← Real.mul_rpow ha.le (by positivity)]
    congr 1
    rw [div_pow, Real.sq_sqrt ha.le]
    field_simp
    ring
  simp_rw [he]
  rw [integral_const_mul, Measure.integral_comp_div (fun s : ℝ ↦ (1 + s ^ 2) ^ t),
    abs_of_pos hs, smul_eq_mul, ← mul_assoc, Real.sqrt_eq_rpow,
    ← Real.rpow_add ha]

lemma mu_hasDerivAt_nonneg {σ δ z : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (hz : 0 ≤ z) :
    HasDerivAt (scalarMu σ δ) (σ * (z + δ) ^ (σ - 1)) z := by
  have hh := mu_hasDerivAt_integral hσ hδ z
  have he (s : ℝ) : (max (s ^ 2 + z) 0 + δ) ^ (σ - 3 / 2) =
      (s ^ 2 + (z + δ)) ^ (σ - 3 / 2) := by
    rw [max_eq_left (by positivity)]
    congr 1
    ring
  simp_rw [he] at hh
  rw [quadratic_integral_scale _ (by positivity : 0 < z + δ)] at hh
  have hp := (normalization_integral_pos hσ).ne'
  convert hh using 1
  unfold fieldNormalization
  rw [show σ - 3 / 2 + 1 / 2 = σ - 1 by ring]
  rw [mul_comm ((z + δ) ^ (σ - 1)), ← mul_assoc, div_mul_cancel₀ _ hp]

lemma mu_eq_nonneg {σ δ z : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (hz : 0 ≤ z) :
    scalarMu σ δ z = (z + δ) ^ σ - δ ^ σ := by
  have hd (y : ℝ) (hy : 0 ≤ y) :
      HasDerivAt (fun x : ℝ ↦ (x + δ) ^ σ - δ ^ σ)
        (σ * (y + δ) ^ (σ - 1)) y := by
    convert! (((hasDerivAt_id y).add_const δ).rpow_const (p := σ)
      (Or.inl (by positivity : y + δ ≠ 0))).sub_const (δ ^ σ) using 1
    simp
  exact eq_of_has_deriv_right_eq
    (fun y hy ↦ (mu_hasDerivAt_nonneg hσ hδ hy.1).hasDerivWithinAt)
    (fun y hy ↦ (hd y hy.1).hasDerivWithinAt)
    (continuous_iff_continuousAt.mpr (fun y ↦
      (mu_hasDerivAt_integral hσ hδ y).continuousAt)).continuousOn
    (fun y hy ↦ (hd y hy.1).continuousAt.continuousWithinAt)
    (by simp) z ⟨hz, le_rfl⟩


lemma gammaWeight_nonneg {σ v : ℝ} (hσ : σ < 1) (hv : 0 ≤ v) :
    0 ≤ gammaWeight σ v := by
  unfold gammaWeight
  exact mul_nonneg (inv_nonneg.2 (Real.Gamma_pos_of_pos (by linarith)).le)
    (mul_nonneg (Real.rpow_nonneg hv _) (Real.exp_pos _).le)

lemma gammaWeight_integrable {σ : ℝ} (hσ : σ < 1) :
    IntegrableOn (gammaWeight σ) (Ioi 0) := by
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow (s := -σ) (p := 1) (b := 1)
    (by linarith) zero_lt_one zero_lt_one
  simp only [Real.rpow_one, neg_one_mul] at hi
  exact hi.const_mul _

lemma gamma_mixture {σ h x : ℝ} (hσ : σ < 1) (hh : 0 ≤ h) :
    (∫ v in Ioi (0 : ℝ), gammaWeight σ v * Real.exp (-v * h * x ^ 2)) =
      (1 + h * x ^ 2) ^ (σ - 1) := by
  have hb : 0 < 1 + h * x ^ 2 := by positivity
  have hg : Real.Gamma (1 - σ) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have he (v : ℝ) : gammaWeight σ v * Real.exp (-v * h * x ^ 2) =
      (Real.Gamma (1 - σ))⁻¹ * (v ^ (-σ) * Real.exp (-(1 + h * x ^ 2) * v ^ (1 : ℝ))) := by
    unfold gammaWeight
    rw [mul_assoc, mul_assoc, ← Real.exp_add, Real.rpow_one]
    congr 3
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_rpow_mul_exp_neg_mul_rpow zero_lt_one (by linarith) hb]
  simp only [div_one, mul_one]
  rw [show -σ + 1 = 1 - σ by ring, show -(1 - σ) = σ - 1 by ring]
  rw [← mul_assoc, mul_comm _ ((1 + h * x ^ 2) ^ (σ - 1)), mul_assoc,
    inv_mul_cancel₀ hg, mul_one]

lemma gammaWeight_integral {σ : ℝ} (hσ : σ < 1) :
    (∫ v in Ioi (0 : ℝ), gammaWeight σ v) = 1 := by
  simpa using gamma_mixture (h := 0) (x := 0) hσ le_rfl

/-- Integrability of the scalar kernel used in the matrix resolvent tangent formula. -/
lemma resolvent_kernel_integrable {β a : ℝ} (hβ₀ : -1 < β) (hβ₁ : β < 1)
    (ha : 0 < a) : IntegrableOn (fun v : ℝ ↦ v ^ β / (a + v) ^ 2) (Ioi 0) := by
  have hc : ContinuousOn (fun v : ℝ ↦ v ^ β / (a + v) ^ 2) (Ioi 0) := by
    apply ContinuousOn.div
    · exact continuousOn_id.rpow_const (fun v hv ↦ Or.inl (ne_of_gt hv))
    · fun_prop
    · intro v hv
      exact pow_ne_zero _ (ne_of_gt (add_pos ha hv) : a + v ≠ 0)
  have hn : IntegrableOn (fun v : ℝ ↦ v ^ β / (a + v) ^ 2) (Ioo 0 1) := by
    have hi : IntegrableOn (fun v : ℝ ↦ v ^ β * (a ^ 2)⁻¹) (Ioo 0 1) :=
      ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 hβ₀).mul_const _
    apply hi.mono' ((hc.mono Ioo_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioo)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.rpow_nonneg hv.1.le _) (sq_nonneg _)),
      ← div_eq_mul_inv]
    apply div_le_div_of_nonneg_left (Real.rpow_nonneg hv.1.le _) (sq_pos_of_pos ha)
    nlinarith [hv.1, hv.2]
  have hf : IntegrableOn (fun v : ℝ ↦ v ^ β / (a + v) ^ 2) (Ioi 1) := by
    apply (integrableOn_Ioi_rpow_of_lt (show β - 2 < -1 by linarith) zero_lt_one).mono'
      ((hc.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv₀ : 0 < v := lt_trans zero_lt_one hv
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.rpow_nonneg hv₀.le _) (sq_nonneg _)),
      Real.rpow_sub hv₀, Real.rpow_two]
    apply div_le_div_of_nonneg_left (Real.rpow_nonneg hv₀.le _) (sq_pos_of_pos hv₀)
    nlinarith
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact (hn.congr_set_ae Ioo_ae_eq_Ioc.symm).union hf

lemma resolvent_kernel_integral_scale (β : ℝ) {a : ℝ} (ha : 0 < a) :
    (∫ v in Ioi (0 : ℝ), v ^ β / (a + v) ^ 2) =
      a ^ (β - 1) * ∫ v in Ioi (0 : ℝ), v ^ β / (1 + v) ^ 2 := by
  have hs := integral_comp_mul_left_Ioi (fun v : ℝ ↦ v ^ β / (a + v) ^ 2) 0 ha
  simp only [mul_zero, smul_eq_mul] at hs
  have he : (fun v : ℝ ↦ (a * v) ^ β / (a + a * v) ^ 2) =ᵐ[volume.restrict (Ioi 0)]
      fun v ↦ (a ^ β / a ^ 2) * (v ^ β / (1 + v) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [Real.mul_rpow ha.le hv.le, show a + a * v = a * (1 + v) by ring, mul_pow, mul_div_mul_comm]
  rw [integral_congr_ae he, integral_const_mul] at hs
  have he' : a ^ (β - 1) = a * (a ^ β / a ^ 2) := by
    rw [Real.rpow_sub ha, Real.rpow_one]
    field_simp
  rw [he', mul_assoc, hs, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]

lemma resolvent_kernel_integral_pos {β a : ℝ} (hβ₀ : -1 < β) (hβ₁ : β < 1)
    (ha : 0 < a) : 0 < ∫ v in Ioi (0 : ℝ), v ^ β / (a + v) ^ 2 := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun v ↦ v ^ β / (a + v) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact div_nonneg (Real.rpow_nonneg hv.le _) (sq_nonneg _)
  rw [setIntegral_pos_iff_support_of_nonneg_ae hn
    (resolvent_kernel_integrable hβ₀ hβ₁ ha)]
  have he : Function.support (fun v : ℝ ↦ v ^ β / (a + v) ^ 2) ∩ Ioi 0 = Ioi 0 := by
    apply inter_eq_right.mpr
    intro v hv
    exact (div_pos (Real.rpow_pos_of_pos hv _) (sq_pos_of_pos (add_pos ha hv))).ne'
  rw [he]
  simp

lemma resolvent_difference_eq (β : ℝ) {δ y v : ℝ}
    (hδv : δ + v ≠ 0) (hyδv : y + δ + v ≠ 0) :
    resolventDifference β δ y v = y * (v ^ β / ((δ + v) * (y + δ + v))) := by
  unfold resolventDifference
  field_simp
  ring

lemma resolvent_difference_integrable {β δ y : ℝ} (hβ₀ : -1 < β) (hβ₁ : β < 1)
    (hδ : 0 < δ) (hy : -δ / 2 < y) :
    IntegrableOn (resolventDifference β δ y) (Ioi 0) := by
  have hc : ContinuousOn (resolventDifference β δ y) (Ioi 0) := by
    unfold resolventDifference
    apply ContinuousOn.mul
    · exact continuousOn_id.rpow_const (fun _ hv ↦ Or.inl (ne_of_gt hv))
    · apply ContinuousOn.sub
      · apply ContinuousOn.inv₀ (by fun_prop)
        intro v hv
        exact ne_of_gt (add_pos hδ hv)
      · apply ContinuousOn.inv₀ (by fun_prop)
        intro v hv
        have hv' : 0 < v := hv
        linarith
  apply ((resolvent_kernel_integrable hβ₀ hβ₁ (half_pos hδ)).const_mul |y|).mono'
    (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv' : 0 < v := hv
  have ha : 0 < δ + v := by linarith
  have hb : 0 < y + δ + v := by linarith
  have hm : 0 < δ / 2 + v := by linarith
  rw [resolvent_difference_eq β ha.ne' hb.ne', norm_mul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.rpow_nonneg hv'.le _) (mul_pos ha hb).le)]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg y)
  apply div_le_div_of_nonneg_left (Real.rpow_nonneg hv'.le _) (sq_pos_of_pos hm)
  nlinarith [mul_nonneg (show 0 ≤ δ / 2 by linarith) (show 0 ≤ δ / 2 + v by linarith),
    mul_nonneg (show 0 ≤ y + δ / 2 by linarith) (show 0 ≤ δ + v by linarith)]

lemma resolvent_integral_hasDerivAt {β δ y : ℝ} (hβ₀ : -1 < β) (hβ₁ : β < 1)
    (hδ : 0 < δ) (hy : 0 ≤ y) :
    HasDerivAt (fun x ↦ ∫ v in Ioi (0 : ℝ), resolventDifference β δ x v)
      (∫ v in Ioi (0 : ℝ), v ^ β / (y + δ + v) ^ 2) y := by
  have hi x (hx : -δ / 2 < x) := resolvent_difference_integrable hβ₀ hβ₁ hδ hx
  have hmeas : ∀ᶠ x in 𝓝 y, AEStronglyMeasurable (resolventDifference β δ x)
      (volume.restrict (Ioi 0)) := by
    filter_upwards [Ioi_mem_nhds (show -δ / 2 < y by linarith)] with x hx
    exact (hi x hx).aestronglyMeasurable
  have hdint : IntegrableOn (fun v : ℝ ↦ v ^ β / (y + δ + v) ^ 2) (Ioi 0) :=
    resolvent_kernel_integrable hβ₀ hβ₁ (by linarith)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) (s := Ioi (-δ / 2))
    (F' := fun x v : ℝ ↦ v ^ β / (x + δ + v) ^ 2)
    (bound := fun v : ℝ ↦ v ^ β / (δ / 2 + v) ^ 2)
    (Ioi_mem_nhds (show -δ / 2 < y by linarith)) hmeas
    (hi y (by linarith)) hdint.aestronglyMeasurable ?_
    (resolvent_kernel_integrable hβ₀ hβ₁ (half_pos hδ)) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    intro x hx
    have hv' : 0 < v := hv
    have hx' : -δ / 2 < x := hx
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.rpow_nonneg hv'.le _) (sq_nonneg _))]
    apply div_le_div_of_nonneg_left (Real.rpow_nonneg hv'.le _)
      (sq_pos_of_pos (by linarith : 0 < δ / 2 + v))
    nlinarith
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    intro x hx
    have hv' : 0 < v := hv
    have hx' : -δ / 2 < x := hx
    have he := (((hasDerivAt_id x).add_const δ).add_const v).inv
      (by linarith : x + δ + v ≠ 0)
    convert! (he.const_sub ((δ + v)⁻¹)).const_mul (v ^ β) using 1
    simp [div_eq_mul_inv]


lemma resolvent_normalization_pos {β : ℝ} (hβ₀ : -1 < β) (hβ₁ : β < 1) :
    0 < resolventNormalization β :=
  inv_pos.2 (resolvent_kernel_integral_pos hβ₀ hβ₁ zero_lt_one)

/-- Resolvent representation of f, for every nonnegative scalar argument.
The exponent sigma-1/2 may be zero or negative. -/
lemma primitive_resolvent_representation {σ δ y : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hδ : 0 < δ) (hy : 0 ≤ y) :
    regularizedPrimitive σ δ y = resolventNormalization (σ - 1 / 2) *
      ∫ v in Ioi (0 : ℝ), resolventDifference (σ - 1 / 2) δ y v := by
  have hβ₀ : -1 < σ - 1 / 2 := by linarith
  have hβ₁ : σ - 1 / 2 < 1 := by linarith
  have hJ := (resolvent_kernel_integral_pos hβ₀ hβ₁ zero_lt_one).ne'
  have hd (x : ℝ) (hx : 0 ≤ x) :
      HasDerivAt (fun t ↦ resolventNormalization (σ - 1 / 2) *
        ∫ v in Ioi (0 : ℝ), resolventDifference (σ - 1 / 2) δ t v)
        ((x + δ) ^ (σ - 3 / 2)) x := by
    have hh := (resolvent_integral_hasDerivAt hβ₀ hβ₁ hδ hx).const_mul
      (resolventNormalization (σ - 1 / 2))
    rw [resolvent_kernel_integral_scale _ (by positivity : 0 < x + δ)] at hh
    convert! hh using 1
    unfold resolventNormalization
    rw [show σ - 1 / 2 - 1 = σ - 3 / 2 by ring,
      mul_comm ((x + δ) ^ (σ - 3 / 2)), ← mul_assoc, inv_mul_cancel₀ hJ, one_mul]
  have hf (x : ℝ) (hx : 0 ≤ x) :
      HasDerivAt (regularizedPrimitive σ δ) ((x + δ) ^ (σ - 3 / 2)) x := by
    simpa only [max_eq_left hx] using primitive_hasDerivAt σ hδ x
  exact eq_of_has_deriv_right_eq
    (fun x hx ↦ (hf x hx.1).hasDerivWithinAt)
    (fun x hx ↦ (hd x hx.1).hasDerivWithinAt)
    (primitive_differentiable σ hδ).continuous.continuousOn
    (fun x hx ↦ (hd x hx.1).continuousAt.continuousWithinAt)
    (by simp [resolventDifference]) y ⟨hy, le_rfl⟩

lemma inverse_mu_positive {σ δ m : ℝ} (hσ₀ : 0 < σ) (hδ : 0 < δ) (hm : 0 < m) :
    0 < (m + δ ^ σ) ^ (1 / σ) - δ := by
  have hbase : 0 < δ ^ σ := Real.rpow_pos_of_pos hδ _
  have hi : 0 < (1 : ℝ) / σ := one_div_pos.2 hσ₀
  have hc := Real.rpow_lt_rpow hbase.le (show δ ^ σ < m + δ ^ σ by linarith) hi
  rw [← Real.rpow_mul hδ.le, mul_one_div_cancel hσ₀.ne', Real.rpow_one] at hc
  linarith

lemma mu_inverse {σ δ m : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ)
    (hm : 0 < m) :
    scalarMu σ δ ((m + δ ^ σ) ^ (1 / σ) - δ) = m := by
  rw [mu_eq_nonneg hσ₁ hδ (inverse_mu_positive hσ₀ hδ hm).le, sub_add_cancel,
    ← Real.rpow_mul (by positivity : 0 ≤ m + δ ^ σ),
    one_div_mul_cancel hσ₀.ne', Real.rpow_one]
  ring

lemma mu_le_rpow {σ δ d : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ)
    (hd : 0 ≤ d) : scalarMu σ δ d ≤ d ^ σ := by
  rw [mu_eq_nonneg hσ₁ hδ hd]
  have := Real.rpow_add_le_add_rpow hd hδ.le hσ₀.le hσ₁.le
  linarith

lemma rankone_scalar_power {σ δ m d : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hδ : 0 < δ) (hm : 0 < m) (hd : 0 ≤ d) (he : scalarMu σ δ d = m) :
    m ^ (1 + 1 / σ) ≤ d * m := by
  have hmd : m ≤ d ^ σ := by rw [← he]; exact mu_le_rpow hσ₀ hσ₁ hδ hd
  have hp := Real.rpow_le_rpow hm.le hmd (le_of_lt (one_div_pos.2 hσ₀))
  rw [← Real.rpow_mul hd, mul_one_div_cancel hσ₀.ne', Real.rpow_one] at hp
  rw [Real.rpow_add hm, Real.rpow_one, mul_comm d]
  exact mul_le_mul_of_nonneg_left hp hm.le

end ScalarProof

open scoped MatrixOrder ComplexOrder
namespace MatrixProof
variable {n : Type u4} [Fintype n] [DecidableEq n]

/-- Exact resolvent remainder. All inverses are the ordinary finite-matrix
inverse; invertibility is provided by the positive-definiteness hypotheses. -/
lemma resolvent_remainder (A B : Matrix n n ℂ) (hA : IsUnit A) (hB : IsUnit B) :
    -A⁻¹ + A⁻¹ * (B - A) * A⁻¹ - (-B⁻¹) =
      (A⁻¹ * (B - A)) * B⁻¹ * ((B - A) * A⁻¹) := by
  have hAA := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have hAA' := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have hBB := Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp hB)
  have hBB' := Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).mp hB)
  have hb (C : Matrix n n ℂ) : B⁻¹ * (B * C) = C := by
    rw [← mul_assoc, hBB', one_mul]
  simp only [mul_sub, sub_mul, hAA, hAA', mul_one, one_mul]
  simp only [mul_assoc, hb, hBB, mul_one]
  noncomm_ring

/-- The resolvent tangent inequality before integration. -/
lemma resolvent_tangent {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    -B⁻¹ ≤ -A⁻¹ + A⁻¹ * (B - A) * A⁻¹ := by
  rw [← sub_nonneg, resolvent_remainder A B hA.isUnit hB.isUnit]
  have hp := hB.inv.posSemidef.conjTranspose_mul_mul_same ((B - A) * A⁻¹)
  have he : (((B - A) * A⁻¹)ᴴ) = A⁻¹ * (B - A) := by
    rw [conjTranspose_mul, hA.inv.isHermitian.eq, (hB.isHermitian.sub hA.isHermitian).eq]
  rw [he] at hp
  exact hp.nonneg


end MatrixProof


end SharpLiebThirring

end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.ResolventCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u6 u7 u8 u9 u10 u11

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix


open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace SharpLiebThirring.MatrixProof
variable {n : Type u6} [Fintype n] [DecidableEq n]

lemma integrable_hermitian_cfc {X : Type u7} [MeasurableSpace X] {μ : Measure X}
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : X → ℝ → ℝ)
    (hf : ∀ i, Integrable (fun x ↦ f x (hA.eigenvalues i)) μ) :
    Integrable (fun x ↦ hA.cfc (f x)) μ :=
  (spectralCLM hA).integrable_comp (integrable_pi_iff.2 hf)

lemma integral_hermitian_cfc {X : Type u8} [MeasurableSpace X] {μ : Measure X}
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : X → ℝ → ℝ)
    (hf : ∀ i, Integrable (fun x ↦ f x (hA.eigenvalues i)) μ) :
    ∫ x, hA.cfc (f x) ∂μ = hA.cfc (fun t ↦ ∫ x, f x t ∂μ) := by
  have hi := integrable_pi_iff.2 hf
  calc
    _ = ∫ x, spectralCLM hA (fun i ↦ f x (hA.eigenvalues i)) ∂μ := rfl
    _ = spectralCLM hA (∫ x, fun i ↦ f x (hA.eigenvalues i) ∂μ) :=
      (spectralCLM hA).integral_comp_comm hi
    _ = _ := by
      apply congrArg (spectralCLM hA)
      ext i
      exact ((ContinuousLinearMap.proj i : (n → ℝ) →L[ℝ] ℝ).integral_comp_comm hi).symm

lemma cfc_shifted_inverse {A : Matrix n n ℂ} (hA : A.PosSemidef) {a : ℝ} (ha : 0 < a) :
    hA.isHermitian.cfc (fun y ↦ (y + a)⁻¹) = (A + a • 1)⁻¹ := by
  have hn : ∀ x ∈ spectrum ℝ A, x + a ≠ 0 := by
    intro x hx
    have hx₀ : 0 ≤ x := spectrum_nonneg_of_nonneg hA.nonneg hx
    linarith
  erw [← hA.isHermitian.cfc_eq,
    cfc_inv (fun y : ℝ ↦ y + a) A hn (by fun_prop) hA.isHermitian,
    cfc_add A id (fun _ ↦ a) (by fun_prop) (by fun_prop),
    cfc_const a A hA.isHermitian, cfc_id ℝ A hA.isHermitian,
    Matrix.nonsing_inv_eq_ringInverse, Algebra.algebraMap_eq_smul_one]

open ScalarProof

lemma shifted_inverse_norm_le {A : Matrix n n ℂ} (hA : A.PosSemidef) {a : ℝ} (ha : 0 < a) :
    ‖(A + a • 1)⁻¹‖ ≤ a⁻¹ := by
  rw [← cfc_shifted_inverse hA ha, ← hA.isHermitian.cfc_eq]
  apply norm_cfc_le (inv_nonneg.2 ha.le)
  intro x hx
  have hx₀ : 0 ≤ x := spectrum_nonneg_of_nonneg hA.nonneg hx
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (by linarith : 0 < x + a))]
  exact inv_anti₀ ha (by linarith)

lemma cfc_resolventDifference {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (β : ℝ) {δ v : ℝ} (hδ : 0 < δ) (hv : 0 ≤ v) :
    hA.isHermitian.cfc (fun y ↦ resolventDifference β δ y v) =
      resolventMatrix β δ A v := by
  have ha : 0 < δ + v := by linarith
  have hn : ∀ x ∈ spectrum ℝ A, x + (δ + v) ≠ 0 := by
    intro x hx
    have hx₀ : 0 ≤ x := spectrum_nonneg_of_nonneg hA.nonneg hx
    linarith
  have hc : ContinuousOn (fun x : ℝ ↦ (x + (δ + v))⁻¹) (spectrum ℝ A) :=
    (continuousOn_id.add continuousOn_const).inv₀ hn
  unfold resolventDifference resolventMatrix
  simp only [add_assoc]
  erw [← hA.isHermitian.cfc_eq,
    cfc_const_mul (v ^ β) (fun y ↦ (δ + v)⁻¹ - (y + (δ + v))⁻¹) A
      (continuousOn_const.sub hc),
    cfc_sub (fun _ ↦ (δ + v)⁻¹) (fun y ↦ (y + (δ + v))⁻¹) A
      continuousOn_const hc,
    cfc_const (δ + v)⁻¹ A hA.isHermitian,
    hA.isHermitian.cfc_eq, cfc_shifted_inverse hA ha,
    Algebra.algebraMap_eq_smul_one]

lemma integrable_resolventMatrix {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {β δ : ℝ} (hβ₀ : -1 < β) (hβ₁ : β < 1) (hδ : 0 < δ) :
    IntegrableOn (resolventMatrix β δ A) (Ioi 0) := by
  have hi := integrable_hermitian_cfc hA.isHermitian
    (fun v y ↦ resolventDifference β δ y v) (μ := volume.restrict (Ioi (0 : ℝ)))
    (fun i ↦ resolvent_difference_integrable hβ₀ hβ₁ hδ (by
      have := hA.eigenvalues_nonneg i
      linarith))
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact cfc_resolventDifference hA β hδ (le_of_lt hv)

/-- Matrix-valued resolvent representation, not only a scalar or commuting case. -/
lemma primitive_cfc_resolvent_representation {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ) :
    hA.isHermitian.cfc (regularizedPrimitive σ δ) =
      resolventNormalization (σ - 1 / 2) •
        ∫ v in Ioi (0 : ℝ), resolventMatrix (σ - 1 / 2) δ A v := by
  have hβ₀ : -1 < σ - 1 / 2 := by linarith
  have hβ₁ : σ - 1 / 2 < 1 := by linarith
  have hi (i : n) : IntegrableOn
      (fun v ↦ resolventDifference (σ - 1 / 2) δ (hA.isHermitian.eigenvalues i) v) (Ioi 0) :=
    resolvent_difference_integrable hβ₀ hβ₁ hδ (by
      have := hA.eigenvalues_nonneg i
      linarith)
  have he : (∫ v in Ioi (0 : ℝ), resolventMatrix (σ - 1 / 2) δ A v) =
      hA.isHermitian.cfc (fun y ↦ ∫ v in Ioi (0 : ℝ), resolventDifference (σ - 1 / 2) δ y v) := by
    rw [← integral_hermitian_cfc hA.isHermitian
      (fun v y ↦ resolventDifference (σ - 1 / 2) δ y v) hi]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact (cfc_resolventDifference hA _ hδ (le_of_lt hv)).symm
  rw [he]
  change spectralCLM hA.isHermitian (fun i ↦ regularizedPrimitive σ δ (hA.isHermitian.eigenvalues i)) =
    _ • spectralCLM hA.isHermitian _
  rw [← map_smul]
  apply congrArg (spectralCLM hA.isHermitian)
  ext i
  exact primitive_resolvent_representation hσ₀ hσ₁ hδ (hA.eigenvalues_nonneg i)

end SharpLiebThirring.MatrixProof


namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
variable {n : Type u9} [Fintype n] [DecidableEq n]

lemma continuousOn_shifted_inverse {Y : Matrix n n ℂ} (hY : Y.PosSemidef)
    {δ : ℝ} (hδ : 0 < δ) :
    ContinuousOn (fun v : ℝ ↦ (Y + (δ + v) • 1)⁻¹) (Ioi 0) := by
  have hc : ContinuousOn (fun v : ℝ ↦ fun i ↦ (hY.isHermitian.eigenvalues i + (δ + v))⁻¹)
      (Ioi 0) := by
    apply continuousOn_pi.2
    intro i
    apply (continuousOn_const.add (continuousOn_const.add continuousOn_id)).inv₀
    intro v hv
    change hY.isHermitian.eigenvalues i + (δ + v) ≠ 0
    have hv' : 0 < v := hv
    have := hY.eigenvalues_nonneg i
    linarith
  apply ((spectralCLM hY.isHermitian).continuous.comp_continuousOn hc).congr
  intro v hv
  change (Y + (δ + v) • 1)⁻¹ = hY.isHermitian.cfc (fun y ↦ (y + (δ + v))⁻¹)
  exact (cfc_shifted_inverse hY (by have hv' : 0 < v := hv; linarith)).symm

lemma integrable_resolventTangentKernel {Y : Matrix n n ℂ} (hY : Y.PosSemidef)
    (Z : Matrix n n ℂ) {β δ : ℝ} (hβ₀ : -1 < β) (hβ₁ : β < 1) (hδ : 0 < δ) :
    IntegrableOn (resolventTangentKernel β δ Y Z) (Ioi 0) := by
  have hc := continuousOn_shifted_inverse hY hδ
  have ht : ContinuousOn (resolventTangentKernel β δ Y Z) (Ioi 0) :=
    (continuousOn_id.rpow_const (fun _ hv ↦ Or.inl (ne_of_gt hv))).smul
      ((hc.mul continuousOn_const).mul hc)
  apply ((resolvent_kernel_integrable hβ₀ hβ₁ hδ).const_mul ‖Z‖).mono'
    (ht.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv' : 0 < v := hv
  have hb := shifted_inverse_norm_le hY (show 0 < δ + v by linarith)
  have hn : 0 ≤ v ^ β := Real.rpow_nonneg hv'.le _
  unfold resolventTangentKernel
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hn]
  calc
    _ ≤ v ^ β * ((‖(Y + (δ + v) • 1)⁻¹‖ * ‖Z‖) * ‖(Y + (δ + v) • 1)⁻¹‖) := by
      gcongr
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ v ^ β * (((δ + v)⁻¹ * ‖Z‖) * (δ + v)⁻¹) := by gcongr
    _ = ‖Z‖ * (v ^ β / (δ + v) ^ 2) := by rw [div_eq_mul_inv, ← inv_pow]; ring

omit [Fintype n] in
lemma shifted_posDef {Y : Matrix n n ℂ} (hY : Y.PosSemidef) {a : ℝ} (ha : 0 < a) :
    (Y + a • 1).PosDef :=
  PosDef.posSemidef_add hY ((PosDef.one : (1 : Matrix n n ℂ).PosDef).smul ha)

lemma resolventMatrix_le {X Y : Matrix n n ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    {β δ v : ℝ} (hδ : 0 < δ) (hv : 0 < v) :
    resolventMatrix β δ X v ≤ resolventMatrix β δ Y v + resolventTangentKernel β δ Y (X - Y) v := by
  have ha : 0 < δ + v := by linarith
  have ht := resolvent_tangent (shifted_posDef hY ha) (shifted_posDef hX ha)
  have he : (X + (δ + v) • 1) - (Y + (δ + v) • 1) = X - Y := by abel
  rw [he] at ht
  have hh := add_le_add_left ht ((δ + v)⁻¹ • (1 : Matrix n n ℂ))
  have hsm := smul_le_smul_of_nonneg_left hh (Real.rpow_nonneg hv.le β)
  convert! hsm using 1 <;> simp only [resolventMatrix, resolventTangentKernel, sub_eq_add_neg,
    smul_add, add_assoc] <;> abel

/-- Operator tangent inequality for every pair of positive Hermitian matrices,
with a fully convergent resolvent integral. -/
lemma primitive_cfc_tangent {X Y : Matrix n n ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ) :
    hX.isHermitian.cfc (regularizedPrimitive σ δ) ≤
      hY.isHermitian.cfc (regularizedPrimitive σ δ) +
        resolventNormalization (σ - 1 / 2) •
          ∫ v in Ioi (0 : ℝ), resolventTangentKernel (σ - 1 / 2) δ Y (X - Y) v := by
  have hβ₀ : -1 < σ - 1 / 2 := by linarith
  have hβ₁ : σ - 1 / 2 < 1 := by linarith
  have hiX := integrable_resolventMatrix hX hβ₀ hβ₁ hδ
  have hiY := integrable_resolventMatrix hY hβ₀ hβ₁ hδ
  have hiT := integrable_resolventTangentKernel hY (X - Y) hβ₀ hβ₁ hδ
  have hle := integral_mono_ae hiX (hiY.add hiT) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact resolventMatrix_le hX hY hδ hv)
  simp only [Pi.add_apply] at hle
  rw [integral_add hiY hiT] at hle
  rw [primitive_cfc_resolvent_representation hX hσ₀ hσ₁ hδ,
    primitive_cfc_resolvent_representation hY hσ₀ hσ₁ hδ, ← smul_add]
  exact smul_le_smul_of_nonneg_left hle (resolvent_normalization_pos hβ₀ hβ₁).le

end SharpLiebThirring.MatrixProof


namespace SharpLiebThirring.ScalarProof
open MeasureTheory Set

lemma convex_combo_nonneg {x y τ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hτ : τ ∈ Icc (0 : ℝ) 1) : 0 ≤ τ * x + (1 - τ) * y :=
  add_nonneg (mul_nonneg hτ.1 hx) (mul_nonneg (sub_nonneg.2 hτ.2) hy)

lemma continuousOn_divided_integrand (σ : ℝ) {δ x y : ℝ} (hδ : 0 < δ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ContinuousOn (fun τ : ℝ ↦ (τ * x + (1 - τ) * y + δ) ^ (σ - 3 / 2)) (Icc 0 1) := by
  apply ContinuousOn.rpow_const (by fun_prop)
  intro τ hτ
  left
  exact ne_of_gt (add_pos_of_nonneg_of_pos (convex_combo_nonneg hx hy hτ) hδ)

lemma dividedPrimitive_self (σ δ x : ℝ) :
    dividedPrimitive σ δ x x = (x + δ) ^ (σ - 3 / 2) := by
  simp only [dividedPrimitive, show ∀ τ : ℝ, τ * x + (1 - τ) * x = x by intro τ; ring]
  simp

lemma dividedPrimitive_mul_sub (σ : ℝ) {δ x y : ℝ} (hδ : 0 < δ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x - y) * dividedPrimitive σ δ x y =
      regularizedPrimitive σ δ x - regularizedPrimitive σ δ y := by
  have hd (τ : ℝ) (hτ : τ ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ ↦ regularizedPrimitive σ δ (t * x + (1 - t) * y))
        ((x - y) * (τ * x + (1 - τ) * y + δ) ^ (σ - 3 / 2)) τ := by
    have hc : HasDerivAt (fun t : ℝ ↦ t * x + (1 - t) * y) (x - y) τ := by
      convert! ((hasDerivAt_id τ).mul_const x).add
        (((hasDerivAt_const τ (1 : ℝ)).sub (hasDerivAt_id τ)).mul_const y) using 1; ring
    have hp := (primitive_hasDerivAt σ hδ (τ * x + (1 - τ) * y)).comp τ hc
    rw [max_eq_left (convex_combo_nonneg hx hy (by simpa using hτ))] at hp
    convert! hp using 1; ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuousOn_divided_integrand σ hδ hx hy).const_mul (x - y)).intervalIntegrable_of_Icc zero_le_one)
  simp only [one_mul, sub_self, zero_mul, add_zero, sub_zero, zero_add] at he
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc] at he
  exact he

/-- The divided-difference coefficient, including coincident eigenvalues. -/
lemma mixed_resolvent_eq_divided {σ δ x y : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hδ : 0 < δ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    resolventNormalization (σ - 1 / 2) *
      (∫ v in Ioi (0 : ℝ), v ^ (σ - 1 / 2) / ((x + δ + v) * (y + δ + v))) =
        dividedPrimitive σ δ x y := by
  have hβ₀ : -1 < σ - 1 / 2 := by linarith
  have hβ₁ : σ - 1 / 2 < 1 := by linarith
  by_cases hxy : x = y
  · subst y
    simp only [dividedPrimitive_self, ← pow_two]
    rw [resolvent_kernel_integral_scale _ (show 0 < x + δ by linarith)]
    unfold resolventNormalization
    have hn := (resolvent_kernel_integral_pos hβ₀ hβ₁ zero_lt_one).ne'
    rw [mul_left_comm, inv_mul_cancel₀ hn, mul_one]
    congr 1
    ring
  · apply mul_left_cancel₀ (sub_ne_zero.mpr hxy)
    rw [dividedPrimitive_mul_sub _ hδ hx hy,
      primitive_resolvent_representation hσ₀ hσ₁ hδ hx,
      primitive_resolvent_representation hσ₀ hσ₁ hδ hy, ← mul_sub,
      ← integral_sub (resolvent_difference_integrable hβ₀ hβ₁ hδ (by linarith))
        (resolvent_difference_integrable hβ₀ hβ₁ hδ (by linarith))]
    rw [mul_left_comm, ← integral_const_mul]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    have hv' : 0 < v := hv
    unfold resolventDifference
    have ha : x + δ + v ≠ 0 := by linarith
    have hb : y + δ + v ≠ 0 := by linarith
    field_simp
    ring

end SharpLiebThirring.ScalarProof

noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
namespace SharpLiebThirring.MatrixProof
variable {n : Type u10} [Fintype n] [DecidableEq n]

lemma cfc_diagonal_real (f : ℝ → ℝ) (x : n → ℝ) (hf : Continuous f) :
    cfc f (diagonal (fun i ↦ (x i : ℂ))) = diagonal (fun i ↦ (f (x i) : ℂ)) := by
  have : ContinuousFunctionalCalculus ℝ (n → ℂ) IsSelfAdjoint :=
    (IsSelfAdjoint.instIsometricContinuousFunctionalCalculus (A := n → ℂ)).toContinuousFunctionalCalculus
  have hself : IsSelfAdjoint (fun i ↦ (x i : ℂ)) := by ext i; simp
  change cfc f (diagonalStarAlgHom (fun i ↦ (x i : ℂ))) = _
  erw [← (diagonalStarAlgHom (n := n)).map_cfc f (fun i ↦ (x i : ℂ)) hf.continuousOn
    (by change Continuous (diagonal : (n → ℂ) → Matrix n n ℂ); fun_prop) hself
    (isHermitian_diagonal_iff.2 fun i ↦ by simp [IsSelfAdjoint])]
  rw [cfc_map_pi (S := ℝ) f _ hf.continuousOn hself (fun i ↦ by simp [IsSelfAdjoint])]
  change diagonal (fun i ↦ cfc f (x i : ℂ)) = diagonal (fun i ↦ (f (x i) : ℂ))
  apply congrArg diagonal
  funext i
  exact cfc_algebraMap (R := ℝ) (A := ℂ) (x i) f

lemma inverse_diagonal_real (x : n → ℝ) (hx : ∀ i, x i ≠ 0) :
    (diagonal (fun i ↦ (x i : ℂ)))⁻¹ = diagonal (fun i ↦ ((x i)⁻¹ : ℂ)) := by
  apply Matrix.inv_eq_right_inv
  ext i j
  simp only [diagonal_mul_diagonal]
  by_cases hij : i = j
  · subst j; simp [hx]
  · simp [hij]

omit [Fintype n] in
lemma shifted_diagonal_real (x : n → ℝ) (a : ℝ) :
    diagonal (fun i ↦ (x i : ℂ)) + a • (1 : Matrix n n ℂ) =
      diagonal (fun i ↦ ((x i + a : ℝ) : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst j; simp
  · simp [hij]

end SharpLiebThirring.MatrixProof


namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type u11} [Fintype n] [DecidableEq n]

omit [Fintype n] in
lemma diagonal_real_posSemidef (x : n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (diagonal (fun i ↦ (x i : ℂ))).PosSemidef :=
  posSemidef_diagonal_iff.2 (fun i ↦ by exact_mod_cast hx i)

lemma resolventTangentKernel_diagonal {δ : ℝ} (hδ : 0 < δ) (β : ℝ)
    (x : n → ℝ) (hx : ∀ i, 0 ≤ x i) (Z : Matrix n n ℂ) {v : ℝ} (hv : 0 < v) (i j : n) :
    resolventTangentKernel β δ (diagonal (fun i ↦ (x i : ℂ))) Z v i j =
      ((v ^ β / ((x i + δ + v) * (x j + δ + v)) : ℝ) : ℂ) * Z i j := by
  unfold resolventTangentKernel
  rw [shifted_diagonal_real, inverse_diagonal_real _ (fun i ↦ by have := hx i; linarith)]
  simp only [Matrix.smul_apply, Complex.real_smul, mul_diagonal, diagonal_mul]
  simp only [div_eq_mul_inv, _root_.mul_inv_rev]
  push_cast
  ring

lemma integral_resolventTangent_diagonal {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hδ : 0 < δ) (x : n → ℝ) (hx : ∀ i, 0 ≤ x i) (Z : Matrix n n ℂ) :
    resolventNormalization (σ - 1 / 2) •
      ∫ v in Ioi (0 : ℝ), resolventTangentKernel (σ - 1 / 2) δ
        (diagonal (fun i ↦ (x i : ℂ))) Z v =
      fun i j ↦ (dividedPrimitive σ δ (x i) (x j) : ℂ) * Z i j := by
  have hi := integrable_resolventTangentKernel (diagonal_real_posSemidef x hx) Z
    (show -1 < σ - 1 / 2 by linarith) (show σ - 1 / 2 < 1 by linarith) hδ
  ext i j
  have he := (entryCLM i j).integral_comp_comm hi
  simp only [entryCLM_apply] at he
  simp only [Matrix.smul_apply]
  rw [← he]
  have he' : (∫ v in Ioi (0 : ℝ), resolventTangentKernel (σ - 1 / 2) δ
      (diagonal (fun i ↦ (x i : ℂ))) Z v i j) =
      (∫ v in Ioi (0 : ℝ), ((v ^ (σ - 1 / 2) / ((x i + δ + v) *
        (x j + δ + v)) : ℝ) : ℂ)) * Z i j := by
    rw [← integral_mul_const]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    exact resolventTangentKernel_diagonal hδ _ x hx Z hv i j
  rw [he']
  erw [integral_ofReal]
  rw [Complex.real_smul, ← mul_assoc]
  change (resolventNormalization (σ - 1 / 2) : ℂ) *
    ((∫ v in Ioi (0 : ℝ), v ^ (σ - 1 / 2) / ((x i + δ + v) * (x j + δ + v)) : ℝ) : ℂ) *
      Z i j = _
  rw [← Complex.ofReal_mul, mixed_resolvent_eq_divided hσ₀ hσ₁ hδ (hx i) (hx j)]

end SharpLiebThirring.MatrixProof


namespace SharpLiebThirring.ScalarProof
open MeasureTheory Set

lemma quadratic_combo (d x y s τ : ℝ) :
    τ * ((s - x) ^ 2 + d) + (1 - τ) * ((s - y) ^ 2 + d) =
      (s - (τ * x + (1 - τ) * y)) ^ 2 + (d + τ * (1 - τ) * (x - y) ^ 2) := by ring

lemma quadraticDivided_integrable_left {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (d x y τ : ℝ) : Integrable (fun s ↦ quadraticDividedIntegrand σ δ d x y s τ) := by
  have hi := shifted_derivative_integrable hσ hδ (d + τ * (1 - τ) * (x - y) ^ 2)
  have hp := (measurePreserving_sub_right (volume : Measure ℝ) (τ * x + (1 - τ) * y)).integrable_comp
    hi.aestronglyMeasurable |>.2 hi
  simpa only [Function.comp_def, quadraticDividedIntegrand, quadratic_combo] using hp

lemma integral_quadraticDivided_left {σ δ d τ : ℝ} (hδ : 0 < δ) (hd : 0 ≤ d)
    (hτ : τ ∈ Icc (0 : ℝ) 1) (x y : ℝ) :
    (∫ s : ℝ, quadraticDividedIntegrand σ δ d x y s τ) =
      (d + δ + τ * (1 - τ) * (x - y) ^ 2) ^ (σ - 1) *
        ∫ s : ℝ, (1 + s ^ 2) ^ (σ - 3 / 2) := by
  have hz : 0 ≤ d + τ * (1 - τ) * (x - y) ^ 2 := by
    exact add_nonneg hd (mul_nonneg (mul_nonneg hτ.1 (sub_nonneg.2 hτ.2)) (sq_nonneg _))
  have ha : 0 < d + δ + τ * (1 - τ) * (x - y) ^ 2 := by linarith
  have he (s : ℝ) : quadraticDividedIntegrand σ δ d x y s τ =
      ((s - (τ * x + (1 - τ) * y)) ^ 2 + (d + δ + τ * (1 - τ) * (x - y) ^ 2)) ^
        (σ - 3 / 2) := by
    unfold quadraticDividedIntegrand
    rw [quadratic_combo, max_eq_left (add_nonneg (sq_nonneg _) hz)]
    congr 1
    ring
  simp_rw [he]
  rw [integral_sub_right_eq_self (fun s : ℝ ↦ (s ^ 2 + (d + δ + τ * (1 - τ) * (x - y) ^ 2)) ^
    (σ - 3 / 2)), quadratic_integral_scale _ ha]
  congr 2
  ring

lemma quadraticDivided_integrable_prod {σ δ d : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (hd : 0 ≤ d) (x y : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦ quadraticDividedIntegrand σ δ d x y p.1 p.2)
      (volume.prod (volume.restrict (Icc (0 : ℝ) 1))) := by
  have hc : Continuous (fun p : ℝ × ℝ ↦ quadraticDividedIntegrand σ δ d x y p.1 p.2) :=
    (derivative_continuous σ hδ).comp (by fun_prop)
  apply (integrable_prod_iff' hc.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall (quadraticDivided_integrable_left hσ hδ d x y)
  · have hv : ContinuousOn (fun τ : ℝ ↦
        (d + δ + τ * (1 - τ) * (x - y) ^ 2) ^ (σ - 1) *
          ∫ s : ℝ, (1 + s ^ 2) ^ (σ - 3 / 2)) (Icc 0 1) := by
      apply ContinuousOn.mul _ continuousOn_const
      apply ContinuousOn.rpow_const (by fun_prop)
      intro τ hτ
      left
      have hz : 0 ≤ τ * (1 - τ) * (x - y) ^ 2 :=
        mul_nonneg (mul_nonneg hτ.1 (sub_nonneg.2 hτ.2)) (sq_nonneg _)
      linarith
    apply hv.integrableOn_Icc.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
    rw [← integral_quadraticDivided_left hδ hd hτ x y]
    apply integral_congr_ae
    filter_upwards [] with s
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ quadraticDividedIntegrand σ δ d x y s τ by
      unfold quadraticDividedIntegrand; positivity)]

/-- Absolute convergence of the integrated tangent coefficients. -/
lemma integrable_divided_quadratic {σ δ d : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (hd : 0 ≤ d) (x y : ℝ) :
    Integrable (fun s ↦ dividedPrimitive σ δ ((s - x) ^ 2 + d) ((s - y) ^ 2 + d)) := by
  have hi := (quadraticDivided_integrable_prod hσ hδ hd x y).integral_prod_left
  apply hi.congr
  filter_upwards [] with s
  unfold dividedPrimitive
  apply setIntegral_congr_fun measurableSet_Icc
  intro τ hτ
  unfold quadraticDividedIntegrand
  rw [max_eq_left (convex_combo_nonneg (add_nonneg (sq_nonneg _) hd)
    (add_nonneg (sq_nonneg _) hd) hτ)]

/-- The integrated tangent kernel. -/
lemma integral_divided_quadratic {σ δ d : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (hd : 0 ≤ d) (x y : ℝ) :
    fieldNormalization σ *
      (∫ s : ℝ, dividedPrimitive σ δ ((s - x) ^ 2 + d) ((s - y) ^ 2 + d)) =
      σ * (d + δ) ^ (σ - 1) *
        ∫ τ in Icc (0 : ℝ) 1,
          (1 + τ * (1 - τ) / (d + δ) * (x - y) ^ 2) ^ (σ - 1) := by
  have ha : 0 < d + δ := by linarith
  have hn := (normalization_integral_pos hσ).ne'
  have he (s : ℝ) : dividedPrimitive σ δ ((s - x) ^ 2 + d) ((s - y) ^ 2 + d) =
      ∫ τ in Icc (0 : ℝ) 1, quadraticDividedIntegrand σ δ d x y s τ := by
    unfold dividedPrimitive
    apply setIntegral_congr_fun measurableSet_Icc
    intro τ hτ
    unfold quadraticDividedIntegrand
    rw [max_eq_left (convex_combo_nonneg (add_nonneg (sq_nonneg _) hd)
      (add_nonneg (sq_nonneg _) hd) hτ)]
  simp_rw [he]
  rw [integral_integral_swap (quadraticDivided_integrable_prod hσ hδ hd x y)]
  have he' : (∫ τ in Icc (0 : ℝ) 1, ∫ s : ℝ, quadraticDividedIntegrand σ δ d x y s τ) =
      ((d + δ) ^ (σ - 1) * ∫ s : ℝ, (1 + s ^ 2) ^ (σ - 3 / 2)) *
        ∫ τ in Icc (0 : ℝ) 1,
          (1 + τ * (1 - τ) / (d + δ) * (x - y) ^ 2) ^ (σ - 1) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Icc
    intro τ hτ
    dsimp only
    rw [integral_quadraticDivided_left (σ := σ) hδ hd hτ x y]
    have hp : 0 ≤ 1 + τ * (1 - τ) / (d + δ) * (x - y) ^ 2 := by
      have := mul_nonneg (div_nonneg (mul_nonneg hτ.1 (sub_nonneg.2 hτ.2)) ha.le) (sq_nonneg (x - y))
      linarith
    rw [show d + δ + τ * (1 - τ) * (x - y) ^ 2 =
      (d + δ) * (1 + τ * (1 - τ) / (d + δ) * (x - y) ^ 2) by field_simp,
      Real.mul_rpow ha.le hp]
    ring
  rw [he']
  unfold fieldNormalization
  calc
    _ = (σ / (∫ s : ℝ, (1 + s ^ 2) ^ (σ - 3 / 2)) *
        (∫ s : ℝ, (1 + s ^ 2) ^ (σ - 3 / 2))) * ((d + δ) ^ (σ - 1) *
        ∫ τ in Icc (0 : ℝ) 1, (1 + τ * (1 - τ) / (d + δ) * (x - y) ^ 2) ^ (σ - 1)) := by ring
    _ = _ := by rw [div_mul_cancel₀ _ hn]; ring

end SharpLiebThirring.ScalarProof

end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.MatrixTangent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u12 u13 u14 u15

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra


namespace SharpLiebThirring.MatrixProof
open ScalarProof MeasureTheory Set Filter Unitary
open scoped Matrix.Norms.L2Operator NNReal Topology
variable {n : Type u12} [Fintype n] [DecidableEq n]

lemma gaussianSchur_eq_average (z : n → ℝ) (D : Matrix n n ℂ) {v h : ℝ}
    (hv : 0 ≤ v) (hh : 0 ≤ h) :
    gaussianSchur z v h D = ∫ t,
      conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) D
        ∂ProbabilityTheory.gaussianReal 0 ⟨2 * v * h, by positivity⟩ := by
  ext i j
  have he := (gaussian_phase_average z D (⟨2 * v * h, by positivity⟩ : ℝ≥0) i j).symm
  convert! he using 1
  change (Real.exp (-v * h * (z i - z j) ^ 2) : ℂ) * D i j =
    Complex.exp (-((2 * v * h) * (z i - z j) ^ 2 / 2 : ℝ)) * D i j
  rw [Complex.ofReal_exp]
  congr 2
  push_cast
  ring

lemma gaussianSchur_norm_le (z : n → ℝ) (D : Matrix n n ℂ) {v h : ℝ}
    (hv : 0 ≤ v) (hh : 0 ≤ h) : ‖gaussianSchur z v h D‖ ≤ ‖D‖ := by
  rw [gaussianSchur_eq_average z D hv hh]
  apply (norm_integral_le_integral_norm _).trans
  have he (t : ℝ) :
      ‖conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) D‖ = ‖D‖ := by
    change ‖(phaseUnitary z t : Matrix n n ℂ) * D *
      ((star (phaseUnitary z t) : unitary (Matrix n n ℂ)) : Matrix n n ℂ)‖ = ‖D‖
    rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  simp_rw [he]
  rw [integral_const]
  have hp : (ProbabilityTheory.gaussianReal 0 (⟨2 * v * h, by positivity⟩ : ℝ≥0)).real univ = 1 :=
    @probReal_univ ℝ _ _ (ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 _)
  erw [hp]
  simp only [one_smul, le_refl]

omit [Fintype n] [DecidableEq n] in
lemma continuous_gaussianSchur (z : n → ℝ) (h : ℝ) (D : Matrix n n ℂ) :
    Continuous (fun v ↦ gaussianSchur z v h D) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold gaussianSchur
  fun_prop

lemma gamma_integrable_gaussianSchur {σ h : ℝ} (hσ : σ < 1) (hh : 0 ≤ h)
    (z : n → ℝ) (D : Matrix n n ℂ) :
    IntegrableOn (fun v ↦ gammaWeight σ v • gaussianSchur z v h D) (Ioi 0) := by
  apply ((gammaWeight_integrable hσ).norm.mul_const ‖D‖).mono'
  · exact (gammaWeight_integrable hσ).aestronglyMeasurable.smul
      (continuous_gaussianSchur z h D).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (gaussianSchur_norm_le z D (le_of_lt hv) hh) (norm_nonneg _)

lemma gamma_gaussianSchur_integral {σ h : ℝ} (hσ : σ < 1) (hh : 0 ≤ h)
    (z : n → ℝ) (D : Matrix n n ℂ) :
    (∫ v in Ioi (0 : ℝ), gammaWeight σ v • gaussianSchur z v h D) =
      powerSchur σ z h D := by
  ext i j
  have he := (entryCLM i j).integral_comp_comm (gamma_integrable_gaussianSchur hσ hh z D)
  simp only [entryCLM_apply] at he
  rw [← he]
  simp only [Matrix.smul_apply, gaussianSchur, powerSchur, Complex.real_smul,
    ← mul_assoc, ← Complex.ofReal_mul]
  erw [integral_mul_const, integral_ofReal, gamma_mixture hσ hh]
  rfl

lemma powerSchur_trace_comparison {σ h : ℝ} (hσ : σ < 1) (hh : 0 ≤ h)
    (z : n → ℝ) (M D : Matrix n n ℂ)
    (hpoint : ∀ t : ℝ, 0 ≤ (trace (M * (2 • D -
      conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) D -
      conjStarAlgAut ℂ (Matrix n n ℂ) (star (phaseUnitary z t)) D))).re) :
    (trace (M * powerSchur σ z h D)).re ≤ (trace (M * D)).re := by
  have hi := gamma_integrable_gaussianSchur hσ hh z D
  have hp (v : ℝ) (hv : 0 < v) :
      gammaWeight σ v * (trace (M * gaussianSchur z v h D)).re ≤
        gammaWeight σ v * (trace (M * D)).re := by
    apply mul_le_mul_of_nonneg_left _ (gammaWeight_nonneg hσ hv.le)
    rw [gaussianSchur_eq_average z D hv.le hh]
    exact gaussian_trace_comparison z M D _ hpoint
  have hle := integral_mono_ae ((tracePairCLM M).integrable_comp hi)
    ((gammaWeight_integrable hσ).mul_const ((trace (M * D)).re))
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
        simpa only [map_smul, tracePairCLM_apply, smul_eq_mul] using hp v hv)
  rw [(tracePairCLM M).integral_comp_comm hi, gamma_gaussianSchur_integral hσ hh z D,
    integral_mul_const, gammaWeight_integral hσ, one_mul] at hle
  exact hle

end SharpLiebThirring.MatrixProof


namespace SharpLiebThirring.MatrixProof
open ScalarProof MeasureTheory Set
open scoped Matrix.Norms.L2Operator
variable {n : Type u13} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
lemma continuousOn_powerSchur_tau (σ : ℝ) {a : ℝ} (ha : 0 < a)
    (z : n → ℝ) (D : Matrix n n ℂ) :
    ContinuousOn (fun τ ↦ powerSchur σ z (τ * (1 - τ) / a) D) (Icc (0 : ℝ) 1) := by
  apply continuousOn_pi.2
  intro i
  apply continuousOn_pi.2
  intro j
  apply ContinuousOn.mul _ continuousOn_const
  apply Complex.continuous_ofReal.comp_continuousOn
  apply ContinuousOn.rpow_const (by fun_prop)
  intro τ hτ
  left
  have hp : 0 ≤ τ * (1 - τ) / a * (z i - z j) ^ 2 :=
    mul_nonneg (div_nonneg (mul_nonneg hτ.1 (sub_nonneg.2 hτ.2)) ha.le) (sq_nonneg _)
  linarith

lemma integrable_powerSchur_tau (σ : ℝ) {a : ℝ} (ha : 0 < a)
    (z : n → ℝ) (D : Matrix n n ℂ) :
    IntegrableOn (fun τ ↦ powerSchur σ z (τ * (1 - τ) / a) D) (Icc (0 : ℝ) 1) :=
  (continuousOn_powerSchur_tau σ ha z D).integrableOn_Icc

lemma tangentSchur_trace_comparison {σ a : ℝ} (hσ : σ < 1) (ha : 0 < a)
    (z : n → ℝ) (M D : Matrix n n ℂ)
    (hpoint : ∀ t : ℝ, 0 ≤ (trace (M * (2 • D -
      Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) D -
      Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) (star (phaseUnitary z t)) D))).re) :
    (trace (M * tangentSchur σ a z D)).re ≤ (trace (M * D)).re := by
  have hi := integrable_powerSchur_tau σ ha z D
  have hle := integral_mono_ae ((tracePairCLM M).integrable_comp hi)
    (integrableOn_const (C := (trace (M * D)).re) (s := Icc (0 : ℝ) 1) (by simp)) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
      exact powerSchur_trace_comparison hσ
        (div_nonneg (mul_nonneg hτ.1 (sub_nonneg.2 hτ.2)) ha.le) z M D hpoint)
  rw [(tracePairCLM M).integral_comp_comm hi] at hle
  simpa [tangentSchur, tracePairCLM_apply] using hle

lemma tangentSchur_one (σ a : ℝ) (z : n → ℝ) :
    tangentSchur σ a z 1 = 1 := by
  have he : ∀ τ : ℝ, powerSchur σ z (τ * (1 - τ) / a) (1 : Matrix n n ℂ) = 1 := by
    intro τ
    ext i j
    by_cases hij : i = j
    · subst j; simp [powerSchur]
    · simp [powerSchur, hij]
  simp only [tangentSchur, he]
  simp

end SharpLiebThirring.MatrixProof


namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type u14} [Fintype n] [DecidableEq n]

lemma integrable_quadraticTangent {σ δ d : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (hd : 0 ≤ d) (z : n → ℝ) (Z : Matrix n n ℂ) :
    Integrable (quadraticTangent σ δ d z Z) := by
  let e : (n → n → ℂ) →L[ℝ] Matrix n n ℂ :=
    ({ toFun := Matrix.of
       map_add' := by intros; rfl
       map_smul' := by intros; rfl } : (n → n → ℂ) →ₗ[ℝ] Matrix n n ℂ).toContinuousLinearMap
  apply e.integrable_comp
  apply integrable_pi_iff.2
  intro i
  apply integrable_pi_iff.2
  intro j
  exact (Complex.ofRealCLM.integrable_comp (integrable_divided_quadratic hσ hδ hd (z i) (z j))).mul_const _

lemma tangentSchur_apply (σ : ℝ) {a : ℝ} (ha : 0 < a) (z : n → ℝ) (Z : Matrix n n ℂ) (i j : n) :
    tangentSchur σ a z Z i j =
      ((∫ τ in Icc (0 : ℝ) 1, (1 + τ * (1 - τ) / a * (z i - z j) ^ 2) ^
        (σ - 1) : ℝ) : ℂ) * Z i j := by
  have he := (entryCLM i j).integral_comp_comm (integrable_powerSchur_tau σ ha z Z)
  simp only [entryCLM_apply] at he
  rw [tangentSchur, ← he]
  simp only [powerSchur]
  rw [integral_mul_const]
  exact congrArg (fun t : ℂ ↦ t * Z i j) (integral_ofReal (f := fun τ : ℝ ↦
    (1 + τ * (1 - τ) / a * (z i - z j) ^ 2) ^ (σ - 1)))

/-- Exact integrated tangent map in any diagonalizing basis, not only simple spectrum. -/
lemma integral_quadraticTangent {σ δ d : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (hd : 0 ≤ d) (z : n → ℝ) (Z : Matrix n n ℂ) :
    fieldNormalization σ • ∫ s : ℝ, quadraticTangent σ δ d z Z s =
      (σ * (d + δ) ^ (σ - 1)) • tangentSchur σ (d + δ) z Z := by
  ext i j
  have he := (entryCLM i j).integral_comp_comm (integrable_quadraticTangent hσ hδ hd z Z)
  simp only [entryCLM_apply] at he
  simp only [Matrix.smul_apply]
  rw [← he, tangentSchur_apply σ (by linarith) z Z i j]
  simp only [quadraticTangent]
  rw [integral_mul_const]
  erw [integral_ofReal (f := fun s : ℝ ↦ dividedPrimitive σ δ
    ((s - z i) ^ 2 + d) ((s - z j) ^ 2 + d))]
  simp only [Complex.real_smul, ← mul_assoc]
  have h := congrArg (fun t : ℝ ↦ (t : ℂ) * Z i j)
    (integral_divided_quadratic hσ hδ hd (z i) (z j))
  push_cast at h
  push_cast
  convert! h using 1


lemma primitive_diagonal_tangent {σ δ d : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hδ : 0 < δ) (hd : 0 ≤ d) (z : n → ℝ) (s : ℝ) {X : Matrix n n ℂ}
    (hX : X.PosSemidef) :
    hX.isHermitian.cfc (regularizedPrimitive σ δ) ≤
      cfc (regularizedPrimitive σ δ) (diagonal (fun i ↦ (((s - z i) ^ 2 + d : ℝ) : ℂ))) +
      quadraticTangent σ δ d z (X - diagonal (fun i ↦ (((s - z i) ^ 2 + d : ℝ) : ℂ))) s := by
  have hY := diagonal_real_posSemidef (fun i ↦ (s - z i) ^ 2 + d)
    (fun i ↦ add_nonneg (sq_nonneg _) hd)
  have ht := primitive_cfc_tangent hX hY hσ₀ hσ₁ hδ
  rw [← hY.isHermitian.cfc_eq, integral_resolventTangent_diagonal hσ₀ hσ₁ hδ _
    (fun i ↦ add_nonneg (sq_nonneg _) hd)] at ht
  exact ht

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.ScalarProof

lemma primitive_le_tangent {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (x y : ℝ) :
    regularizedPrimitive σ δ y ≤ regularizedPrimitive σ δ x +
      (max x 0 + δ) ^ (σ - 3 / 2) * (y - x) := by
  have hc := (primitive_concave hσ hδ).neg
  have hd := (primitive_hasDerivAt σ hδ x).neg
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hs := hc.le_slope_of_hasDerivAt (mem_univ x) (mem_univ y) hxy hd
    rw [slope_def_field] at hs
    have := (le_div_iff₀ (sub_pos.2 hxy)).1 hs
    dsimp at this
    nlinarith
  · simp
  · have hs := hc.slope_le_of_hasDerivAt (mem_univ y) (mem_univ x) hyx hd
    rw [slope_def_field] at hs
    have := (div_le_iff₀ (sub_pos.2 hyx)).1 hs
    dsimp at this
    nlinarith

end SharpLiebThirring.ScalarProof

namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type u15} [Fintype n] [DecidableEq n]

/-- Scalar Jensen inequality for every positive unital real-linear matrix state.
No assertion of operator concavity on the whole line is used. -/
lemma primitive_state_jensen {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (φ : Matrix n n ℂ →ₗ[ℝ] ℝ) (hφ : ∀ A, A.PosSemidef → 0 ≤ φ A)
    (hφ₁ : φ 1 = 1) {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    φ (cfc (regularizedPrimitive σ δ) A) ≤ regularizedPrimitive σ δ (φ A) := by
  let f := regularizedPrimitive σ δ
  let x := φ A
  let d := (max x 0 + δ) ^ (σ - 3 / 2)
  have ht : cfc f A ≤ cfc (fun y : ℝ ↦ f x + d * (y - x)) A :=
    cfc_mono (fun y _ ↦ primitive_le_tangent hσ hδ x y)
      (primitive_differentiable σ hδ).continuous.continuousOn (by fun_prop)
  have he : cfc (fun y : ℝ ↦ f x + d * (y - x)) A =
      f x • 1 + d • (A - x • 1) := by
    erw [cfc_const_add (f x) (fun y : ℝ ↦ d * (y - x)) A (by fun_prop) hA,
      cfc_const_mul d (fun y : ℝ ↦ y - x) A (by fun_prop),
      cfc_sub id (fun _ : ℝ ↦ x) A (by fun_prop) (by fun_prop),
      cfc_id ℝ A hA, cfc_const x A hA,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  rw [he] at ht
  have hp := hφ _ (Matrix.nonneg_iff_posSemidef.1 (sub_nonneg.2 ht))
  simp only [map_sub, map_add, map_smul, hφ₁, smul_eq_mul, mul_one] at hp
  dsimp [x] at hp
  linarith

end SharpLiebThirring.MatrixProof

end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.FieldLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u16 u17 u18

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra


noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SharpLiebThirring.ScalarProof

lemma symmetric_shift_boundary {g : ℝ → ℝ} (hg : Continuous g) (he : Function.Even g)
    (R b : ℝ) :
    (∫ s in -R..R, g (s - b) - g s) =
      ∫ t in 0..b, g (R + t) - g (R - b + t) := by
  have hc1 : Continuous (fun s : ℝ ↦ g (s - b)) := by fun_prop
  have hc2 : Continuous (fun t : ℝ ↦ g (R + t)) := by fun_prop
  have hc3 : Continuous (fun t : ℝ ↦ g (R - b + t)) := by fun_prop
  rw [intervalIntegral.integral_sub (hc1.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _), intervalIntegral.integral_comp_sub_right]
  rw [intervalIntegral.integral_interval_sub_interval_comm
    (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  have hn : (∫ s in -R - b..-R, g s) = ∫ t in R..R + b, g t := by
    have h := intervalIntegral.integral_comp_neg (f := g) (a := R) (b := R + b)
    calc
      _ = ∫ x in R..R + b, g (-x) := by
        simpa only [show -(R + b) = -R - b by ring] using h.symm
      _ = _ := intervalIntegral.integral_congr (fun x _ ↦ he x)
  rw [hn, intervalIntegral.integral_sub (hc2.intervalIntegrable _ _)
    (hc3.intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_comp_add_left, add_zero, sub_add_cancel]

lemma symmetric_shift_norm_le {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (he : Function.Even g) (R b C T : ℝ) (hR : T + 2 * |b| ≤ R)
    (hbound : ∀ x, T ≤ x → ‖g' x‖ ≤ C) :
    ‖∫ s in -R..R, g (s - b) - g s‖ ≤ C * |b| ^ 2 := by
  rw [symmetric_shift_boundary (continuous_iff_continuousAt.2 (fun x ↦ (hg x).continuousAt)) he]
  apply le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := C * |b|) (fun t ht ↦ ?_)) (by simp [pow_two, mul_assoc])
  have ht' : -|b| ≤ t := by
    have := ht.1
    have hmin : -|b| ≤ min 0 b := le_min (by linarith [abs_nonneg b]) (neg_abs_le b)
    linarith
  have hx : R - b + t ∈ Ici T := by
    have := le_abs_self b
    change T ≤ _
    linarith
  have hy : R + t ∈ Ici T := by change T ≤ _; linarith [abs_nonneg b]
  have hm := (convex_Ici T).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ ↦ (hg x).hasDerivWithinAt) (fun x hx ↦ hbound x hx) hx hy
  simpa only [show R + t - (R - b + t) = b by ring, Real.norm_eq_abs] using hm

lemma symmetric_shift_tendsto_zero {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (he : Function.Even g) (hlim : Tendsto g' atTop (𝓝 0)) (b : ℝ) :
    Tendsto (fun R : ℝ ↦ ∫ s in -R..R, g (s - b) - g s) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hc : 0 < ε / (|b| ^ 2 + 1) := div_pos hε (by positivity)
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.1 hlim) _ hc
  refine ⟨T + 2 * |b|, fun R hR ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
  refine lt_of_le_of_lt (symmetric_shift_norm_le hg he R b (ε / (|b| ^ 2 + 1)) T hR (fun x hx ↦ ?_)) ?_
  · simpa only [dist_zero_right] using (hT x hx).le
  · have hden : 0 < |b| ^ 2 + 1 := by positivity
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith

end SharpLiebThirring.ScalarProof

namespace SharpLiebThirring.ScalarProof

lemma primitive_quadratic_hasDerivAt (σ : ℝ) {δ : ℝ} (hδ : 0 < δ) (z s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ regularizedPrimitive σ δ (t ^ 2 + z))
      (2 * s * (max (s ^ 2 + z) 0 + δ) ^ (σ - 3 / 2)) s := by
  convert! (primitive_hasDerivAt σ hδ (s ^ 2 + z)).comp s
    (((hasDerivAt_id s).pow 2).add_const z) using 1
  simp only [id_eq, Nat.cast_ofNat, mul_one]
  ring

lemma primitive_quadratic_deriv_tendsto {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z : ℝ) :
    Tendsto (fun s : ℝ ↦ 2 * s * (max (s ^ 2 + z) 0 + δ) ^ (σ - 3 / 2)) atTop (𝓝 0) := by
  let a := δ / (δ + |z| + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have ht : Tendsto (fun s : ℝ ↦ (2 * a ^ (σ - 3 / 2)) * s ^ (2 * σ - 2)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0 < 2 - 2 * σ by linarith)).const_mul
      (2 * a ^ (σ - 3 / 2))
    simpa only [show -(2 - 2 * σ) = 2 * σ - 2 by ring, mul_zero] using h
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have hs₀ : 0 < s := by linarith
    have hb := Real.rpow_le_rpow_of_nonpos (show 0 < a * (1 + s ^ 2) by positivity)
      (shifted_base_lower hδ z s) (show σ - 3 / 2 ≤ 0 by linarith)
    have hsq := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hs₀)
      (show s ^ 2 ≤ 1 + s ^ 2 by linarith) (show σ - 3 / 2 ≤ 0 by linarith)
    rw [Real.mul_rpow ha.le (by positivity)] at hb
    calc
      _ ≤ 2 * s * (a ^ (σ - 3 / 2) * (1 + s ^ 2) ^ (σ - 3 / 2)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ 2 * s * (a ^ (σ - 3 / 2) * (s ^ 2) ^ (σ - 3 / 2)) := by
        gcongr
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hs₀.le]
        norm_num only [Nat.cast_ofNat]
        conv_lhs => arg 1; arg 2; rw [← Real.rpow_one s]
        rw [show 2 * s ^ (1 : ℝ) * (a ^ (σ - 3 / 2) * s ^ ((2 : ℝ) * (σ - 3 / 2))) =
          (2 * a ^ (σ - 3 / 2)) * (s ^ (1 : ℝ) * s ^ (2 * (σ - 3 / 2))) by ring,
          ← Real.rpow_add hs₀]
        congr 2
        ring

lemma primitive_symmetric_shift_zero {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z b : ℝ) :
    Tendsto (fun R : ℝ ↦ ∫ s in -R..R,
      regularizedPrimitive σ δ ((s - b) ^ 2 + z) - regularizedPrimitive σ δ (s ^ 2 + z))
      atTop (𝓝 0) :=
  symmetric_shift_tendsto_zero (primitive_quadratic_hasDerivAt σ hδ z)
    (fun s ↦ by simp) (primitive_quadratic_deriv_tendsto hσ hδ z) b

/-- The symmetric shift identity, with exactly the cutoff used in the field. -/
lemma primitive_shift_limit {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (z b : ℝ) :
    Tendsto (fun R : ℝ ↦ fieldNormalization σ * ∫ s in -R..R,
      regularizedPrimitive σ δ ((s - b) ^ 2 + z) - regularizedPrimitive σ δ (s ^ 2))
      atTop (𝓝 (scalarMu σ δ z)) := by
  have hc := (primitive_differentiable σ hδ).continuous
  have h₁ := primitive_symmetric_shift_zero hσ hδ z b
  have h₂ := intervalIntegral_tendsto_integral (mu_integrand_integrable hσ hδ z)
    tendsto_neg_atTop_atBot tendsto_id
  have hh := (h₁.add h₂).const_mul (fieldNormalization σ)
  simp only [zero_add] at hh
  apply hh.congr
  intro R
  congr 1
  simp only [id_eq]
  rw [← intervalIntegral.integral_add
    (show IntervalIntegrable (fun s : ℝ ↦ regularizedPrimitive σ δ ((s - b) ^ 2 + z) -
      regularizedPrimitive σ δ (s ^ 2 + z)) volume (-R) R from
      (by fun_prop : Continuous _).intervalIntegrable _ _)
    (show IntervalIntegrable (fun s : ℝ ↦ regularizedPrimitive σ δ (s ^ 2 + z) -
      regularizedPrimitive σ δ (s ^ 2)) volume (-R) R from
      (by fun_prop : Continuous _).intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro s hs
  ring

end SharpLiebThirring.ScalarProof

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.RankOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u19 u20 u21 u22 u23 u24

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology


namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type u19} [Fintype n] [DecidableEq n]

lemma hermitianField_state_jensen {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ)
    (φ : Matrix n n ℂ →L[ℝ] ℝ) (hφ : ∀ A, A.PosSemidef → 0 ≤ φ A) (hφ₁ : φ 1 = 1)
    {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) :
    φ (hermitianField σ δ C B) ≤ scalarMu σ δ (φ C - (φ B) ^ 2) := by
  have hlim := φ.continuous.continuousAt.tendsto.comp (hermitianField_cutoff_limit hσ₁ hδ hC hB)
  have hs := primitive_shift_limit hσ₁ hδ (φ C - (φ B) ^ 2) (φ B)
  apply le_of_tendsto_of_tendsto hlim hs
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  have hc := continuous_fieldIntegrand hδ σ hC hB
  dsimp only [Function.comp_apply]
  rw [map_smul, ← φ.intervalIntegral_comp_comm (hc.intervalIntegrable _ _), smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (normalization_pos hσ₀ hσ₁).le
  apply intervalIntegral.integral_mono (by linarith : -R ≤ R)
    ((φ.continuous.comp hc).intervalIntegrable _ _)
    ((by have hf := (primitive_differentiable σ hδ).continuous; fun_prop : Continuous
      (fun s : ℝ ↦ regularizedPrimitive σ δ ((s - φ B) ^ 2 + (φ C - (φ B) ^ 2)) -
        regularizedPrimitive σ δ (s ^ 2))).intervalIntegrable _ _)
  intro s
  have hp := primitive_state_jensen hσ₁ hδ φ.toLinearMap hφ hφ₁ (quadraticMatrix_hermitian hC hB s)
  have he : φ (quadraticMatrix C B s) = (s - φ B) ^ 2 + (φ C - (φ B) ^ 2) := by
    simp only [quadraticMatrix, map_add, map_sub, map_smul, hφ₁, smul_eq_mul, mul_one]
    ring
  change φ (cfc (regularizedPrimitive σ δ) (quadraticMatrix C B s)) ≤
    regularizedPrimitive σ δ (φ (quadraticMatrix C B s)) at hp
  rw [he] at hp
  simpa only [Function.comp_apply, fieldIntegrand, map_sub, map_smul, hφ₁, smul_eq_mul, mul_one] using
    sub_le_sub_right hp (regularizedPrimitive σ δ (s ^ 2))

lemma unitaryState_positive (U : unitary (Matrix n n ℂ)) (i : n)
    {A : Matrix n n ℂ} (hA : A.PosSemidef) : 0 ≤ unitaryState U i A := by
  have hp := hA.mul_mul_conjTranspose_same (U : Matrix n n ℂ)
  have hd := hp.diag_nonneg (i := i)
  exact (Complex.nonneg_iff.1 hd).1

lemma state_quadratic_nonneg {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ)
    (φ : Matrix n n ℂ →L[ℝ] ℝ) (hφ : ∀ A, A.PosSemidef → 0 ≤ φ A) (hφ₁ : φ 1 = 1)
    {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian)
    (hM : (hermitianField σ δ C B).PosSemidef) (s : ℝ) :
    0 ≤ φ (quadraticMatrix C B s) := by
  have hj := hermitianField_state_jensen hσ₀ hσ₁ hδ φ hφ hφ₁ hC hB
  have hn := (hφ _ hM).trans hj
  have hz : 0 ≤ φ C - (φ B) ^ 2 := by
    apply (mu_strictMono hσ₀ hσ₁ hδ).le_iff_le.1
    simpa only [mu_zero] using hn
  simp only [quadraticMatrix, map_add, map_sub, map_smul, hφ₁, smul_eq_mul, mul_one]
  nlinarith [sq_nonneg (s - φ B)]

lemma hermitianField_nonneg_implies_quadratic {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hδ : 0 < δ) {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian)
    (hM : (hermitianField σ δ C B).PosSemidef) (s : ℝ) :
    (quadraticMatrix C B s).PosSemidef := by
  let X := quadraticMatrix C B s
  have hX : X.IsHermitian := quadraticMatrix_hermitian hC hB s
  apply hX.posSemidef_iff_eigenvalues_nonneg.2
  intro i
  have hp := state_quadratic_nonneg hσ₀ hσ₁ hδ
    (unitaryState (star hX.eigenvectorUnitary) i)
    (fun A hA ↦ unitaryState_positive _ _ hA) (unitaryState_one _ _) hC hB hM s
  change 0 ≤ unitaryState (star hX.eigenvectorUnitary) i X at hp
  rw [unitaryState_apply, hX.conjStarAlgAut_star_eigenvectorUnitary] at hp
  simpa using hp

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
variable {n : Type u20} [Fintype n] [DecidableEq n]

omit [Fintype n] in
lemma continuous_diagonalFieldIntegrand {δ : ℝ} (hδ : 0 < δ) (σ d : ℝ) (z : n → ℝ) :
    Continuous (diagonalFieldIntegrand σ δ d z) := by
  have hf := (primitive_differentiable σ hδ).continuous
  unfold diagonalFieldIntegrand
  fun_prop

lemma diagonalField_cutoff_limit {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (d : ℝ) (z : n → ℝ) :
    Tendsto (fun R : ℝ ↦ fieldNormalization σ • ∫ s in -R..R, diagonalFieldIntegrand σ δ d z s)
      atTop (𝓝 (scalarMu σ δ d • (1 : Matrix n n ℂ))) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  have he (R : ℝ) := (entryCLM i j).intervalIntegral_comp_comm (μ := volume)
    ((continuous_diagonalFieldIntegrand hδ σ d z).intervalIntegrable (-R) R)
  simp only [entryCLM_apply] at he
  have he' (R : ℝ) : (fieldNormalization σ • ∫ s in -R..R, diagonalFieldIntegrand σ δ d z s) i j =
      fieldNormalization σ • ∫ s in -R..R, diagonalFieldIntegrand σ δ d z s i j := by
    simp only [Matrix.smul_apply]
    rw [← he R]
  simp only [he']
  by_cases hij : i = j
  · subst j
    simp only [diagonalFieldIntegrand, diagonal_apply_eq, Matrix.smul_apply, one_apply_eq]
    have hs := Complex.continuous_ofReal.continuousAt.tendsto.comp (primitive_shift_limit hσ hδ d (z i))
    convert! hs using 1
    · funext R
      rw [intervalIntegral.integral_ofReal]
      simp [Complex.real_smul]
    · simp
  · simp only [diagonalFieldIntegrand, diagonal_apply_ne _ hij, intervalIntegral.integral_zero,
      smul_zero, Matrix.smul_apply, one_apply_ne hij]
    exact tendsto_const_nhds

omit [Fintype n] in
lemma quadraticMatrix_sub_diagonal (C : Matrix n n ℂ) (z : n → ℝ) (s d : ℝ) :
    quadraticMatrix C (diagonal (fun i ↦ (z i : ℂ))) s -
      diagonal (fun i ↦ (((s - z i) ^ 2 + d : ℝ) : ℂ)) =
      C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ)) - d • 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [quadraticMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      diagonal_apply_eq, one_apply_eq, Complex.real_smul]
    push_cast
    ring
  · simp [quadraticMatrix, hij]

lemma fieldIntegrand_tangent {σ δ d : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hδ : 0 < δ) (hd : 0 ≤ d) (C : Matrix n n ℂ) (z : n → ℝ) (s : ℝ)
    (hX : (quadraticMatrix C (diagonal (fun i ↦ (z i : ℂ))) s).PosSemidef) :
    fieldIntegrand σ δ C (diagonal (fun i ↦ (z i : ℂ))) s ≤
      diagonalFieldIntegrand σ δ d z s +
        quadraticTangent σ δ d z (C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ)) - d • 1) s := by
  have ht := primitive_diagonal_tangent hσ₀ hσ₁ hδ hd z s hX
  rw [quadraticMatrix_sub_diagonal, ← hX.isHermitian.cfc_eq,
    cfc_diagonal_real _ _ (primitive_differentiable σ hδ).continuous] at ht
  have hh := sub_le_sub_right ht (regularizedPrimitive σ δ (s ^ 2) • (1 : Matrix n n ℂ))
  convert! hh using 1
  unfold diagonalFieldIntegrand
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      diagonal_apply_eq, one_apply_eq, Complex.real_smul]
    push_cast
    ring
  · simp [hij]

lemma hermitianField_diagonal_tangent {σ δ d : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hδ : 0 < δ) (hd : 0 ≤ d) {C : Matrix n n ℂ} (hC : C.IsHermitian) (z : n → ℝ)
    (hX : ∀ s, (quadraticMatrix C (diagonal (fun i ↦ (z i : ℂ))) s).PosSemidef) :
    hermitianField σ δ C (diagonal (fun i ↦ (z i : ℂ))) ≤
      scalarMu σ δ d • 1 + (σ * (d + δ) ^ (σ - 1)) •
        tangentSchur σ (d + δ) z (C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ)) - d • 1) := by
  have hB : (diagonal (fun i ↦ (z i : ℂ))).IsHermitian :=
    isHermitian_diagonal_iff.2 (fun i ↦ by simp [IsSelfAdjoint])
  let Z := C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ)) - d • 1
  have hiT := integrable_quadraticTangent hσ₁ hδ hd z Z
  have hlimT := (intervalIntegral_tendsto_integral hiT tendsto_neg_atTop_atBot tendsto_id).const_smul
    (fieldNormalization σ)
  rw [integral_quadraticTangent hσ₁ hδ hd] at hlimT
  have hlimY := diagonalField_cutoff_limit hσ₁ hδ d z
  apply le_of_tendsto_of_tendsto (hermitianField_cutoff_limit hσ₁ hδ hC hB) (hlimY.add hlimT)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  have hc := continuous_fieldIntegrand hδ σ hC hB
  have hy := continuous_diagonalFieldIntegrand hδ σ d z
  have hab : -R ≤ R := by linarith
  have hi := MeasureTheory.integral_mono (μ := volume.restrict (Ioc (-R) R))
    (hc.intervalIntegrable (-R) R).1
    (((hy.intervalIntegrable (-R) R).add (hiT.intervalIntegrable (a := -R) (b := R))).1)
    (fun s ↦ fieldIntegrand_tangent hσ₀ hσ₁ hδ hd C z s (hX s))
  rw [← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hab] at hi
  rw [intervalIntegral.integral_add (hy.intervalIntegrable _ _) hiT.intervalIntegrable] at hi
  simpa only [smul_add, id_eq] using smul_le_smul_of_nonneg_left hi (normalization_pos hσ₀ hσ₁).le

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
variable {n : Type u21} [Fintype n] [DecidableEq n]

lemma phaseUnitary_conj_diagonal (z x : n → ℝ) (t : ℝ) :
    conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) (diagonal (fun i ↦ (x i : ℂ))) =
      diagonal (fun i ↦ (x i : ℂ)) := by
  ext i j
  rw [phaseUnitary_conj_apply]
  by_cases hij : i = j
  · subst j; simp
  · simp [hij]

lemma trace_conjugate_difference_zero (U : unitary (Matrix n n ℂ)) (D : Matrix n n ℂ) :
    trace (2 • D - conjStarAlgAut ℂ (Matrix n n ℂ) U D -
      conjStarAlgAut ℂ (Matrix n n ℂ) (star U) D) = 0 := by
  rw [trace_sub, trace_sub, trace_smul, trace_unitary_conjugate, trace_unitary_conjugate]
  simp only [two_smul]
  abel

lemma fieldIntegrand_trace_phase_nonneg {σ δ : ℝ} (hδ : 0 < δ)
    {C : Matrix n n ℂ} (hC : C.IsHermitian) (z : n → ℝ) (s t : ℝ) :
    0 ≤ (trace (fieldIntegrand σ δ C (diagonal (fun i ↦ (z i : ℂ))) s *
      (2 • (C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ))) -
        conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) (C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ))) -
        conjStarAlgAut ℂ (Matrix n n ℂ) (star (phaseUnitary z t))
          (C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ)))))).re := by
  let B := diagonal (fun i ↦ (z i : ℂ))
  let D := C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ))
  let Y := diagonal (fun i ↦ (((s - z i) ^ 2 : ℝ) : ℂ))
  let H := 2 • D - conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) D -
    conjStarAlgAut ℂ (Matrix n n ℂ) (star (phaseUnitary z t)) D
  have hB : B.IsHermitian := isHermitian_diagonal_iff.2 (fun i ↦ by simp [IsSelfAdjoint])
  have he : quadraticMatrix C B s = D + Y := by
    have hh := quadraticMatrix_sub_diagonal C z s 0
    simp only [add_zero, zero_smul, sub_zero] at hh
    exact (sub_eq_iff_eq_add.1 hh)
  have hA : (D + Y).IsHermitian := he ▸ quadraticMatrix_hermitian hC hB s
  have hp := trace_unitary_comparison_sub_invariant hA (primitive_strictMono σ hδ).monotone
    (phaseUnitary z t) (phaseUnitary_conj_diagonal z (fun i ↦ (s - z i) ^ 2) t)
  rw [← hA.cfc_eq, ← he] at hp
  have hH : trace H = 0 := trace_conjugate_difference_zero _ _
  change 0 ≤ (trace ((cfc (regularizedPrimitive σ δ) (quadraticMatrix C B s) -
    regularizedPrimitive σ δ (s ^ 2) • 1) * H)).re
  rw [sub_mul, trace_sub, smul_mul_assoc, one_mul, trace_smul, hH, smul_zero, sub_zero]
  exact hp

lemma hermitianField_trace_phase_nonneg {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hδ : 0 < δ) {C : Matrix n n ℂ} (hC : C.IsHermitian) (z : n → ℝ) (t : ℝ) :
    0 ≤ (trace (hermitianField σ δ C (diagonal (fun i ↦ (z i : ℂ))) *
      (2 • (C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ))) -
        conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) (C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ))) -
        conjStarAlgAut ℂ (Matrix n n ℂ) (star (phaseUnitary z t))
          (C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ)))))).re := by
  have hB : (diagonal (fun i ↦ (z i : ℂ))).IsHermitian :=
    isHermitian_diagonal_iff.2 (fun i ↦ by simp [IsSelfAdjoint])
  apply trace_unitary_comparison_limit (hermitianField_cutoff_limit hσ₁ hδ hC hB) (phaseUnitary z t)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  let D := C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ))
  let H := 2 • D - conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) D -
    conjStarAlgAut ℂ (Matrix n n ℂ) (star (phaseUnitary z t)) D
  have hc := continuous_fieldIntegrand hδ σ hC hB
  have hn : 0 ≤ ∫ s in -R..R, tracePairCLM H (fieldIntegrand σ δ C (diagonal (fun i ↦ (z i : ℂ))) s) := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro s hs
    rw [tracePairCLM_apply, trace_mul_comm]
    exact fieldIntegrand_trace_phase_nonneg hδ hC z s t
  rw [(tracePairCLM H).intervalIntegral_comp_comm (hc.intervalIntegrable _ _)] at hn
  change 0 ≤ (trace ((fieldNormalization σ • ∫ s in -R..R,
    fieldIntegrand σ δ C (diagonal (fun i ↦ (z i : ℂ))) s) * H)).re
  rw [smul_mul_assoc, trace_smul, Complex.real_smul, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [tracePairCLM_apply, trace_mul_comm] at hn
  exact mul_nonneg (normalization_pos hσ₀ hσ₁).le hn

lemma hermitianField_tangentSchur_contraction {σ δ a : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hδ : 0 < δ) (ha : 0 < a) {C : Matrix n n ℂ} (hC : C.IsHermitian) (z : n → ℝ) :
    (trace (hermitianField σ δ C (diagonal (fun i ↦ (z i : ℂ))) *
      tangentSchur σ a z (C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ))))).re ≤
      (trace (hermitianField σ δ C (diagonal (fun i ↦ (z i : ℂ))) *
        (C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ))))).re :=
  tangentSchur_trace_comparison hσ₁ ha z _ _ (hermitianField_trace_phase_nonneg hσ₀ hσ₁ hδ hC z)

end SharpLiebThirring.MatrixProof
namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
variable {n : Type u22} [Fintype n] [DecidableEq n]

lemma tangentSchur_sub_smul_one (σ : ℝ) {a : ℝ} (ha : 0 < a)
    (z : n → ℝ) (D : Matrix n n ℂ) (d : ℝ) :
    tangentSchur σ a z (D - d • 1) = tangentSchur σ a z D - d • 1 := by
  calc
    _ = tangentSchur σ a z D - d • tangentSchur σ a z 1 := by
      ext i j
      simp only [tangentSchur_apply σ ha, Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul]
      ring
    _ = _ := by rw [tangentSchur_one]

omit [DecidableEq n] in
lemma vectorMass_nonneg (a : n → ℂ) : 0 ≤ vectorMass a :=
  Finset.sum_nonneg (fun i _ ↦ Complex.normSq_nonneg (a i))

omit [DecidableEq n] in
lemma vectorMass_eq_zero {a : n → ℂ} : vectorMass a = 0 ↔ a = 0 := by
  rw [vectorMass, Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ Complex.normSq_nonneg (a i))]
  simp [funext_iff]

omit [DecidableEq n] in
lemma dot_star_self_vectorMass (a : n → ℂ) : star a ⬝ᵥ a = (vectorMass a : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    vectorMass, Complex.ofReal_sum]

omit [DecidableEq n] in
lemma rankone_trace (a : n → ℂ) : trace (vecMulVec a (star a)) = (vectorMass a : ℂ) := by
  rw [trace_vecMulVec, dotProduct_comm, dot_star_self_vectorMass]

omit [DecidableEq n] in
lemma rankone_square (a : n → ℂ) :
    vecMulVec a (star a) * vecMulVec a (star a) = vectorMass a • vecMulVec a (star a) := by
  rw [vecMulVec_mul_vecMulVec, dot_star_self_vectorMass, vecMulVec_smul]
  ext i j
  simp [Complex.real_smul]

lemma rankone_tracePair_positive (a : n → ℂ) {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    0 ≤ tracePairCLM (vecMulVec a (star a)) A := by
  rw [tracePairCLM_apply, trace_mul_comm, mul_vecMulVec, trace_vecMulVec, dotProduct_comm]
  exact (Complex.nonneg_iff.1 (hA.dotProduct_mulVec_nonneg a)).1

lemma rankone_tracePair_monotone (a : n → ℂ) : Monotone (tracePairCLM (vecMulVec a (star a))) := by
  intro A B hAB
  have h := rankone_tracePair_positive a (le_iff.1 hAB)
  rw [map_sub] at h
  linarith

lemma rankone_tracePair_one (a : n → ℂ) : tracePairCLM (vecMulVec a (star a)) 1 = vectorMass a := by
  rw [tracePairCLM_apply, mul_one, rankone_trace, Complex.ofReal_re]

lemma rankone_tracePair_self (a : n → ℂ) :
    tracePairCLM (vecMulVec a (star a)) (vecMulVec a (star a)) = (vectorMass a) ^ 2 := by
  rw [tracePairCLM_apply, rankone_square, trace_smul, rankone_trace, Complex.real_smul]
  simp [pow_two]

/-- The rank-one comparison in an arbitrary eigenbasis of B. No positivity of
C - B² is assumed; its needed trace bound is obtained by contraction. -/
lemma rankone_diagonal_comparison {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ)
    {C : Matrix n n ℂ} (hC : C.IsHermitian) (z : n → ℝ) (a : n → ℂ)
    (hM : hermitianField σ δ C (diagonal (fun i ↦ (z i : ℂ))) = vecMulVec a (star a)) :
    (vectorMass a) ^ (1 + 1 / σ) ≤
      (trace (vecMulVec a (star a) * (C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ))))).re := by
  by_cases ha : a = 0
  · subst a
    have hexp : (1 + 1 / σ : ℝ) ≠ 0 := by positivity
    have hz : vecMulVec (0 : n → ℂ) (star (0 : n → ℂ)) = 0 := by
      ext i j
      simp [vecMulVec]
    rw [hz, zero_mul, trace_zero, Complex.zero_re]
    simpa only [vectorMass, Pi.zero_apply, Complex.normSq_zero, Finset.sum_const_zero]
      using (le_of_eq (Real.zero_rpow hexp))
  have hm : 0 < vectorMass a := lt_of_le_of_ne (vectorMass_nonneg a)
    (Ne.symm (mt vectorMass_eq_zero.1 ha))
  let d := (vectorMass a + δ ^ σ) ^ (1 / σ) - δ
  have hd : 0 < d := inverse_mu_positive hσ₀ hδ hm
  have he : scalarMu σ δ d = vectorMass a := mu_inverse hσ₀ hσ₁ hδ hm
  have hB : (diagonal (fun i ↦ (z i : ℂ))).IsHermitian :=
    isHermitian_diagonal_iff.2 (fun i ↦ by simp [IsSelfAdjoint])
  have hMP : (hermitianField σ δ C (diagonal (fun i ↦ (z i : ℂ)))).PosSemidef := by
    rw [hM]
    exact posSemidef_vecMulVec_self_star a
  have ht := hermitianField_diagonal_tangent hσ₀ hσ₁ hδ hd.le hC z
    (hermitianField_nonneg_implies_quadratic hσ₀ hσ₁ hδ hC hB hMP)
  rw [hM, he, tangentSchur_sub_smul_one σ (by linarith) z _ d] at ht
  have hp := rankone_tracePair_monotone a ht
  rw [map_add, map_smul, map_smul, map_sub, map_smul, rankone_tracePair_one,
    rankone_tracePair_self] at hp
  simp only [smul_eq_mul] at hp
  have hc := hermitianField_tangentSchur_contraction hσ₀ hσ₁ hδ (show 0 < d + δ by linarith) hC z
  rw [hM] at hc
  have hk : 0 < σ * (d + δ) ^ (σ - 1) := mul_pos hσ₀ (Real.rpow_pos_of_pos (by linarith) _)
  have hpd : d * vectorMass a ≤ tracePairCLM (vecMulVec a (star a))
      (tangentSchur σ (d + δ) z (C - diagonal (fun i ↦ ((z i ^ 2 : ℝ) : ℂ)))) := by
    nlinarith
  exact (rankone_scalar_power hσ₀ hσ₁ hδ hm hd.le he).trans (hpd.trans hc)

end SharpLiebThirring.MatrixProof
namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
variable {n : Type u23} [Fintype n] [DecidableEq n]

lemma quadraticMatrix_conj (U : unitary (Matrix n n ℂ)) (C B : Matrix n n ℂ) (s : ℝ) :
    quadraticMatrix (conjStarAlgAut ℂ (Matrix n n ℂ) U C)
      (conjStarAlgAut ℂ (Matrix n n ℂ) U B) s =
        conjStarAlgAut ℂ (Matrix n n ℂ) U (quadraticMatrix C B s) := by
  have hs (r : ℝ) (A : Matrix n n ℂ) :
      conjStarAlgAut ℂ (Matrix n n ℂ) U (r • A) =
        r • conjStarAlgAut ℂ (Matrix n n ℂ) U A := (unitaryConjCLM U).map_smul r A
  simp only [quadraticMatrix, map_add, map_sub, hs, map_one]

lemma cfc_unitary_conj {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (U : unitary (Matrix n n ℂ)) (f : ℝ → ℝ) :
    cfc f (conjStarAlgAut ℂ (Matrix n n ℂ) U A) = conjStarAlgAut ℂ (Matrix n n ℂ) U (cfc f A) := by
  have h := functional_unitary_conjugate hA U f
  rwa [← IsHermitian.cfc_eq, ← hA.cfc_eq] at h

lemma pairedFieldIntegrand_conj (σ δ : ℝ) {C B : Matrix n n ℂ}
    (hC : C.IsHermitian) (hB : B.IsHermitian) (U : unitary (Matrix n n ℂ)) (s : ℝ) :
    pairedFieldIntegrand σ δ (conjStarAlgAut ℂ (Matrix n n ℂ) U C)
      (conjStarAlgAut ℂ (Matrix n n ℂ) U B) s =
        unitaryConjCLM U (pairedFieldIntegrand σ δ C B s) := by
  simp only [pairedFieldIntegrand, quadraticMatrix_conj, unitaryConjCLM_apply,
    cfc_unitary_conj (quadraticMatrix_hermitian hC hB _), map_sub, map_add, map_smul, map_one]

lemma hermitianField_conj {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian)
    (U : unitary (Matrix n n ℂ)) :
    hermitianField σ δ (conjStarAlgAut ℂ (Matrix n n ℂ) U C)
      (conjStarAlgAut ℂ (Matrix n n ℂ) U B) =
        conjStarAlgAut ℂ (Matrix n n ℂ) U (hermitianField σ δ C B) := by
  change _ = unitaryConjCLM U (hermitianField σ δ C B)
  simp only [hermitianField, pairedFieldIntegrand_conj σ δ hC hB, map_smul]
  rw [(unitaryConjCLM U).integral_comp_comm (integrable_pairedFieldIntegrand hσ hδ hC hB)]

lemma unitary_conj_rankone (U : unitary (Matrix n n ℂ)) (a : n → ℂ) :
    conjStarAlgAut ℂ (Matrix n n ℂ) U (vecMulVec a (star a)) =
      vecMulVec ((U : Matrix n n ℂ) *ᵥ a) (star ((U : Matrix n n ℂ) *ᵥ a)) := by
  rw [conjStarAlgAut_apply, mul_vecMulVec, vecMulVec_mul, star_mulVec]
  rfl

lemma vectorMass_unitary (U : unitary (Matrix n n ℂ)) (a : n → ℂ) :
    vectorMass ((U : Matrix n n ℂ) *ᵥ a) = vectorMass a := by
  apply Complex.ofReal_injective
  rw [← rankone_trace, ← unitary_conj_rankone, trace_unitary_conjugate, rankone_trace]

/-- The complete complex Hermitian rank-one comparison, before identifying the
real symmetric field with its complexification. -/
lemma rankone_hermitian_comparison {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ)
    {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) (a : n → ℂ)
    (hM : hermitianField σ δ C B = vecMulVec a (star a)) :
    (vectorMass a) ^ (1 + 1 / σ) ≤ (trace (vecMulVec a (star a) * (C - B ^ 2))).re := by
  let U := star hB.eigenvectorUnitary
  let C' := conjStarAlgAut ℂ (Matrix n n ℂ) U C
  let a' := (U : Matrix n n ℂ) *ᵥ a
  have hb : conjStarAlgAut ℂ (Matrix n n ℂ) U B =
      diagonal (fun i ↦ (hB.eigenvalues i : ℂ)) := hB.conjStarAlgAut_star_eigenvectorUnitary
  have hm : hermitianField σ δ C' (diagonal (fun i ↦ (hB.eigenvalues i : ℂ))) =
      vecMulVec a' (star a') := by
    rw [← hb, hermitianField_conj hσ₁ hδ hC hB, hM, unitary_conj_rankone]
  have hp := rankone_diagonal_comparison hσ₀ hσ₁ hδ (hermitian_unitary_conjugate hC U)
    hB.eigenvalues a' hm
  have hsq : conjStarAlgAut ℂ (Matrix n n ℂ) U (B ^ 2) =
      diagonal (fun i ↦ ((hB.eigenvalues i ^ 2 : ℝ) : ℂ)) := by
    rw [map_pow, hb, pow_two, diagonal_mul_diagonal]
    congr 1
    funext i
    simp [pow_two]
  rw [vectorMass_unitary U a] at hp
  have ht : trace (vecMulVec a' (star a') *
      (C' - diagonal (fun i ↦ ((hB.eigenvalues i ^ 2 : ℝ) : ℂ)))) =
      trace (vecMulVec a (star a) * (C - B ^ 2)) := by
    rw [← unitary_conj_rankone U a, ← hsq]
    change trace (conjStarAlgAut ℂ (Matrix n n ℂ) U (vecMulVec a (star a)) *
      (conjStarAlgAut ℂ (Matrix n n ℂ) U C - conjStarAlgAut ℂ (Matrix n n ℂ) U (B ^ 2))) = _
    rw [← map_sub, ← map_mul, trace_unitary_conjugate]
  rwa [ht] at hp

end SharpLiebThirring.MatrixProof
namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
variable {n : Type u24} [Fintype n] [DecidableEq n]

lemma complexify_vecMulVec (a : n → ℝ) :
    complexify (vecMulVec a a) = vecMulVec (fun i ↦ (a i : ℂ)) (star (fun i ↦ (a i : ℂ))) := by
  ext i j
  simp [vecMulVec]

omit [DecidableEq n] in
lemma vectorMass_ofReal (a : n → ℝ) : vectorMass (fun i ↦ (a i : ℂ)) = ∑ i, a i ^ 2 := by
  simp [vectorMass, Complex.normSq_ofReal, pow_two]

lemma complexify_trace_real (A : Matrix n n ℝ) : (trace (complexify A)).re = trace A := by
  simp only [trace, diag, complexify_apply, Complex.re_sum, Complex.ofReal_re]

/-- The rank-one comparison for the real field
with its symmetric-cutoff definition. -/
theorem source_rankone_comparison {N : ℕ} {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hδ : 0 < δ) (k : Fin N → ℝ) {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.IsHermitian)
    (a : Fin N → ℝ) (hM : matrixField σ δ k B = vecMulVec a a) :
    (∑ i, a i ^ 2) ^ (1 + 1 / σ) ≤
      ∑ i, a i * ((diagonal (fun i ↦ k i ^ 2) - B ^ 2) *ᵥ a) i := by
  have hm : hermitianField σ δ (complexify (diagonal (fun i ↦ k i ^ 2))) (complexify B) =
      vecMulVec (fun i ↦ (a i : ℂ)) (star (fun i ↦ (a i : ℂ))) := by
    rw [← complexify_matrixField hσ₁ hδ k hB, hM, complexify_vecMulVec]
  have hp := rankone_hermitian_comparison hσ₀ hσ₁ hδ
    (complexify_hermitian (isHermitian_diagonal (fun i ↦ k i ^ 2))) (complexify_hermitian hB)
    (fun i ↦ (a i : ℂ)) hm
  rw [vectorMass_ofReal, ← complexify_vecMulVec, ← map_pow, ← map_sub, ← map_mul,
    complexify_trace_real, trace_mul_comm, mul_vecMulVec, trace_vecMulVec, dotProduct_comm] at hp
  exact hp

end SharpLiebThirring.MatrixProof

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.FieldRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u25 u26 u27 u28 u29 u30 u31

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace SharpLiebThirring.MatrixProof
open Matrix
open scoped Matrix.Norms.L2Operator
variable {n : Type u25} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma flatten_norm_sq (A : Matrix n n ℂ) : ‖flattenCLM A‖ ^ 2 = hsSquared A := by
  rw [EuclideanSpace.norm_sq_eq, hsSquared, Fintype.sum_prod_type]
  change (∑ i, ∑ j, ‖A i j‖ ^ 2) = _
  simp only [Complex.sq_norm]


lemma cfc_lipschitz_norm {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x ∈ spectrum ℝ A, ∀ y ∈ spectrum ℝ B, |f x - f y| ≤ L * |x - y|) :
    ‖cfc f A - cfc f B‖ ≤
      (‖(unflattenCLM : EuclideanSpace ℂ (n × n) →L[ℝ] Matrix n n ℂ)‖ *
        ‖(flattenCLM : Matrix n n ℂ →L[ℝ] EuclideanSpace ℂ (n × n))‖) * L * ‖A - B‖ := by
  have hs := hsSquared_cfc_sub hA hB f L hL
    (fun i j ↦ hf _ (hA.eigenvalues_mem_spectrum_real i) _ (hB.eigenvalues_mem_spectrum_real j))
  rw [← hA.cfc_eq, ← hB.cfc_eq, ← flatten_norm_sq, ← flatten_norm_sq] at hs
  have h1 : ‖flattenCLM (cfc f A - cfc f B)‖ ≤ L * ‖flattenCLM (A - B)‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).1
    simpa only [mul_pow] using hs
  calc
    _ = ‖unflattenCLM (flattenCLM (cfc f A - cfc f B))‖ := rfl
    _ ≤ ‖unflattenCLM (n := n)‖ * ‖flattenCLM (cfc f A - cfc f B)‖ := (unflattenCLM (n := n)).le_opNorm _
    _ ≤ ‖unflattenCLM (n := n)‖ * (L * (‖flattenCLM (n := n)‖ * ‖A - B‖)) := by
      exact mul_le_mul_of_nonneg_left (h1.trans
        (mul_le_mul_of_nonneg_left ((flattenCLM (n := n)).le_opNorm _) hL)) (norm_nonneg _)
    _ = _ := by ring

end SharpLiebThirring.MatrixProof

open scoped NNReal
namespace SharpLiebThirring.ScalarProof
open Set
lemma primitive_lipschitz {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) :
    LipschitzWith ⟨δ ^ (σ - 3 / 2), Real.rpow_nonneg hδ.le _⟩
      (regularizedPrimitive σ δ) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x ↦ (primitive_hasDerivAt σ hδ x).differentiableAt)
  intro x
  rw [(primitive_hasDerivAt σ hδ x).deriv]
  change ‖(max x 0 + δ) ^ (σ - 3 / 2)‖ ≤ δ ^ (σ - 3 / 2)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact Real.rpow_le_rpow_of_nonpos hδ (by have := le_max_right x 0; linarith) (by linarith)

end SharpLiebThirring.ScalarProof

namespace SharpLiebThirring.ScalarProof
open Set
lemma primitive_remainder_lipschitz {σ δ a x r y z : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (ha : 0 < a) (hr : 0 ≤ r) (hxr : a ≤ x - r) (hy : |y| ≤ r) (hz : |z| ≤ r) :
    ‖(regularizedPrimitive σ δ (x + y) - regularizedPrimitive σ δ x -
        (x + δ) ^ (σ - 3 / 2) * y) -
      (regularizedPrimitive σ δ (x + z) - regularizedPrimitive σ δ x -
        (x + δ) ^ (σ - 3 / 2) * z)‖ ≤
      ((3 / 2 - σ) * (a + δ) ^ (σ - 5 / 2) * r) * ‖y - z‖ := by
  have hd (t : ℝ) (ht : t ∈ Icc (-r) r) :
      HasDerivWithinAt (fun t : ℝ ↦ regularizedPrimitive σ δ (x + t) -
        regularizedPrimitive σ δ x - (x + δ) ^ (σ - 3 / 2) * t)
        ((x + t + δ) ^ (σ - 3 / 2) - (x + δ) ^ (σ - 3 / 2)) (Icc (-r) r) t := by
    have hxt : 0 ≤ x + t := by have := ht.1; linarith
    convert! (((primitive_hasDerivAt σ hδ (x + t)).comp t ((hasDerivAt_id t).const_add x)).sub_const
        (regularizedPrimitive σ δ x) |>.sub
        ((hasDerivAt_id t).const_mul ((x + δ) ^ (σ - 3 / 2)))).hasDerivWithinAt using 1
    simp [max_eq_left hxt]
  have hb (t : ℝ) (ht : t ∈ Icc (-r) r) :
      ‖(x + t + δ) ^ (σ - 3 / 2) - (x + δ) ^ (σ - 3 / 2)‖ ≤
        (3 / 2 - σ) * (a + δ) ^ (σ - 5 / 2) * r := by
    have hh := derivative_lipschitz_on_positive hσ hδ ha
      (show a ≤ x + t by have := ht.1; linarith) (show a ≤ x by linarith)
    simp only [add_sub_cancel_left] at hh
    refine hh.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by linarith)
      (Real.rpow_nonneg (by linarith) _)))
    exact abs_le.2 ht
  exact (convex_Icc (-r) r).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (abs_le.1 hz) (abs_le.1 hy)
end SharpLiebThirring.ScalarProof

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof
open scoped Matrix.Norms.L2Operator
variable {n : Type u28} [Fintype n] [DecidableEq n]

lemma matrixNormBridge_nonneg : 0 ≤ matrixNormBridge n := mul_nonneg (norm_nonneg _) (norm_nonneg _)

lemma cfc_remainder_eq (σ : ℝ) {δ : ℝ} (hδ : 0 < δ) (x : ℝ)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    cfc (fun y : ℝ ↦ regularizedPrimitive σ δ (x + y) -
      regularizedPrimitive σ δ x - (x + δ) ^ (σ - 3 / 2) * y) A =
      cfc (regularizedPrimitive σ δ) (x • 1 + A) -
        regularizedPrimitive σ δ x • 1 - (x + δ) ^ (σ - 3 / 2) • A := by
  have hc := (primitive_differentiable σ hδ).continuous
  erw [cfc_sub (fun y : ℝ ↦ regularizedPrimitive σ δ (x + y) -
      regularizedPrimitive σ δ x) (fun y : ℝ ↦ (x + δ) ^ (σ - 3 / 2) * y) A
      (by fun_prop) (by fun_prop),
    cfc_sub (fun y : ℝ ↦ regularizedPrimitive σ δ (x + y))
      (fun _ : ℝ ↦ regularizedPrimitive σ δ x) A (by fun_prop) (by fun_prop),
    cfc_const (regularizedPrimitive σ δ x) A hA,
    cfc_const_mul_id ((x + δ) ^ (σ - 3 / 2)) A hA,
    Algebra.algebraMap_eq_smul_one, ← cfc_scalar_add _ hc x hA]

lemma cfc_remainder_lipschitz {σ δ a x r : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (ha : 0 < a) (hr : 0 ≤ r) (hxr : a ≤ x - r)
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hnA : ‖A‖ ≤ r) (hnB : ‖B‖ ≤ r) :
    ‖(cfc (regularizedPrimitive σ δ) (x • 1 + A) -
      regularizedPrimitive σ δ x • 1 - (x + δ) ^ (σ - 3 / 2) • A) -
      (cfc (regularizedPrimitive σ δ) (x • 1 + B) -
      regularizedPrimitive σ δ x • 1 - (x + δ) ^ (σ - 3 / 2) • B)‖ ≤
      matrixNormBridge n * ((3 / 2 - σ) * (a + δ) ^ (σ - 5 / 2) * r) * ‖A - B‖ := by
  rw [← cfc_remainder_eq σ hδ x hA, ← cfc_remainder_eq σ hδ x hB]
  apply cfc_lipschitz_norm hA hB (mul_nonneg (mul_nonneg (by linarith)
    (Real.rpow_nonneg (by linarith) _)) hr)
  intro y hy z hz
  exact primitive_remainder_lipschitz hσ hδ ha hr hxr
    ((spectrum_abs_le_matrix_norm hy).trans hnA) ((spectrum_abs_le_matrix_norm hz).trans hnB)

omit [Fintype n] in
lemma quadraticMatrix_sub (C B D : Matrix n n ℂ) (s : ℝ) :
    quadraticMatrix C B s - quadraticMatrix C D s = (-2 * s) • (B - D) := by
  unfold quadraticMatrix
  module

lemma cfc_quadratic_lipschitz {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B D : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian)
    (hD : D.IsHermitian) (s : ℝ) :
    ‖cfc (regularizedPrimitive σ δ) (quadraticMatrix C B s) -
      cfc (regularizedPrimitive σ δ) (quadraticMatrix C D s)‖ ≤
      matrixNormBridge n * δ ^ (σ - 3 / 2) * (2 * |s|) * ‖B - D‖ := by
  have hh := cfc_lipschitz_norm (quadraticMatrix_hermitian hC hB s)
    (quadraticMatrix_hermitian hC hD s) (Real.rpow_nonneg hδ.le (σ - 3 / 2))
    (fun x _ y _ ↦ (primitive_lipschitz hσ hδ).norm_sub_le x y)
  rw [quadraticMatrix_sub, norm_smul] at hh
  simpa [Real.norm_eq_abs, abs_mul, mul_assoc, matrixNormBridge] using hh

lemma pairedFieldIntegrand_lipschitz_global {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B D : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian)
    (hD : D.IsHermitian) (s : ℝ) :
    ‖pairedFieldIntegrand σ δ C B s - pairedFieldIntegrand σ δ C D s‖ ≤
      (4 * matrixNormBridge n * δ ^ (σ - 3 / 2) * |s|) * ‖B - D‖ := by
  have he : pairedFieldIntegrand σ δ C B s - pairedFieldIntegrand σ δ C D s =
      (cfc (regularizedPrimitive σ δ) (quadraticMatrix C B s) -
        cfc (regularizedPrimitive σ δ) (quadraticMatrix C D s)) +
      (cfc (regularizedPrimitive σ δ) (quadraticMatrix C B (-s)) -
        cfc (regularizedPrimitive σ δ) (quadraticMatrix C D (-s))) := by
    unfold pairedFieldIntegrand
    abel
  rw [he]
  have h1 := cfc_quadratic_lipschitz hσ hδ hC hB hD s
  have h2 := cfc_quadratic_lipschitz hσ hδ hC hB hD (-s)
  rw [abs_neg] at h2
  linarith [norm_add_le
    (cfc (regularizedPrimitive σ δ) (quadraticMatrix C B s) -
      cfc (regularizedPrimitive σ δ) (quadraticMatrix C D s))
    (cfc (regularizedPrimitive σ δ) (quadraticMatrix C B (-s)) -
      cfc (regularizedPrimitive σ δ) (quadraticMatrix C D (-s)))]

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof
open scoped Matrix.Norms.L2Operator
variable {n : Type u30} [Fintype n] [DecidableEq n]

lemma quadraticRemainder_lipschitz_tail {σ δ M : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B D : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) (hD : D.IsHermitian)
    (hBM : ‖B‖ ≤ M) (hDM : ‖D‖ ≤ M) {s : ℝ}
    (hs : max 1 (2 * (‖C‖ + 2 * M)) ≤ |s|) :
    ‖quadraticRemainder σ δ C B s - quadraticRemainder σ δ C D s‖ ≤
      (2 * matrixNormBridge n * (3 / 2 - σ) * (‖C‖ + 2 * M) *
        (1 / 4 : ℝ) ^ (σ - 5 / 2) * (1 + s ^ 2) ^ (σ - 3 / 2)) * ‖B - D‖ := by
  have hs1 : 1 ≤ |s| := (le_max_left _ _).trans hs
  have hsA : 2 * (‖C‖ + 2 * M) ≤ |s| := (le_max_right _ _).trans hs
  have hM : 0 ≤ M := (norm_nonneg _).trans hBM
  let A := ‖C‖ + 2 * M
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hs2 : 0 < s ^ 2 := by nlinarith [sq_abs s]
  have hxr : s ^ 2 / 2 ≤ s ^ 2 - A * |s| := by
    dsimp [A]; nlinarith [sq_abs s]
  have hnB : ‖C - (2 * s) • B‖ ≤ A * |s| :=
    (perturbed_norm_le hs1).trans (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) (abs_nonneg _))
  have hnD : ‖C - (2 * s) • D‖ ≤ A * |s| :=
    (perturbed_norm_le hs1).trans (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) (abs_nonneg _))
  have hh := cfc_remainder_lipschitz hσ hδ (by linarith : 0 < s ^ 2 / 2)
    (mul_nonneg hA (abs_nonneg s)) hxr
    (hC.sub (hB.smul (isSelfAdjoint_iff.2 rfl : IsSelfAdjoint (2 * s))))
    (hC.sub (hD.smul (isSelfAdjoint_iff.2 rfl : IsSelfAdjoint (2 * s)))) hnB hnD
  have he : (C - (2 * s) • B) - (C - (2 * s) • D) = (-2 * s) • (B - D) := by module
  rw [he, norm_smul] at hh
  simp only [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
  have hw := quadratic_taylor_weight (A := 1) hσ hδ hs1
  simp only [one_mul, one_pow, mul_one, sq_abs] at hw
  have hp : 0 ≤ 2 * matrixNormBridge n * (3 / 2 - σ) * A * ‖B - D‖ := by
    have := matrixNormBridge_nonneg (n := n)
    have : 0 ≤ 3 / 2 - σ := by linarith
    positivity
  calc
    _ ≤ matrixNormBridge n * ((3 / 2 - σ) * (s ^ 2 / 2 + δ) ^ (σ - 5 / 2) * (A * |s|)) *
        (2 * |s| * ‖B - D‖) := hh
    _ = (2 * matrixNormBridge n * (3 / 2 - σ) * A * ‖B - D‖) *
        ((s ^ 2 / 2 + δ) ^ (σ - 5 / 2) * s ^ 2) := by rw [← sq_abs s]; ring
    _ ≤ (2 * matrixNormBridge n * (3 / 2 - σ) * A * ‖B - D‖) *
        ((1 / 4 : ℝ) ^ (σ - 5 / 2) * (1 + s ^ 2) ^ (σ - 3 / 2)) :=
      mul_le_mul_of_nonneg_left hw hp
    _ = _ := by dsimp [A]; ring

lemma pairedFieldIntegrand_remainder_difference (σ δ : ℝ) (C B D : Matrix n n ℂ) (s : ℝ) :
    pairedFieldIntegrand σ δ C B s - pairedFieldIntegrand σ δ C D s =
      (quadraticRemainder σ δ C B s - quadraticRemainder σ δ C D s) +
      (quadraticRemainder σ δ C B (-s) - quadraticRemainder σ δ C D (-s)) := by
  unfold pairedFieldIntegrand quadraticRemainder
  simp only [neg_sq]
  module

lemma pairedFieldIntegrand_lipschitz_tail {σ δ M : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B D : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) (hD : D.IsHermitian)
    (hBM : ‖B‖ ≤ M) (hDM : ‖D‖ ≤ M) {s : ℝ}
    (hs : max 1 (2 * (‖C‖ + 2 * M)) ≤ |s|) :
    ‖pairedFieldIntegrand σ δ C B s - pairedFieldIntegrand σ δ C D s‖ ≤
      (4 * matrixNormBridge n * (3 / 2 - σ) * (‖C‖ + 2 * M) *
        (1 / 4 : ℝ) ^ (σ - 5 / 2) * (1 + s ^ 2) ^ (σ - 3 / 2)) * ‖B - D‖ := by
  have h1 := quadraticRemainder_lipschitz_tail hσ hδ hC hB hD hBM hDM hs
  have h2 := quadraticRemainder_lipschitz_tail hσ hδ hC hB hD hBM hDM
    (s := -s) (by rwa [abs_neg])
  rw [neg_sq] at h2
  rw [pairedFieldIntegrand_remainder_difference]
  linarith [norm_add_le (quadraticRemainder σ δ C B s - quadraticRemainder σ δ C D s)
    (quadraticRemainder σ δ C B (-s) - quadraticRemainder σ δ C D (-s))]

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory
open scoped Matrix.Norms.L2Operator NNReal
variable {n : Type u31} [Fintype n] [DecidableEq n]

lemma fieldLipEnvelope_nonneg {σ δ M : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (hM : 0 ≤ M) (C : Matrix n n ℂ) (s : ℝ) : 0 ≤ fieldLipEnvelope σ δ M C s := by
  have h1 : 0 ≤ matrixNormBridge n := matrixNormBridge_nonneg
  have h2 : 0 ≤ 3 / 2 - σ := by linarith
  unfold fieldLipEnvelope
  apply add_nonneg
  · exact Set.indicator_nonneg (fun _ _ ↦ by positivity) _
  · positivity

lemma integrable_fieldLipEnvelope {σ δ : ℝ} (hσ : σ < 1) (M : ℝ)
    (C : Matrix n n ℂ) : Integrable (fieldLipEnvelope σ δ M C) := by
  apply Integrable.add
  · apply IntegrableOn.integrable_indicator _ measurableSet_Icc
    exact (by fun_prop : Continuous (fun s : ℝ ↦
      4 * matrixNormBridge n * δ ^ (σ - 3 / 2) * |s|)).integrableOn_Icc
  · exact (normalization_integrable hσ).const_mul _

lemma pairedFieldIntegrand_lipschitz_envelope {σ δ M : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B D : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) (hD : D.IsHermitian)
    (hBM : ‖B‖ ≤ M) (hDM : ‖D‖ ≤ M) (s : ℝ) :
    ‖pairedFieldIntegrand σ δ C B s - pairedFieldIntegrand σ δ C D s‖ ≤
      fieldLipEnvelope σ δ M C s * ‖B - D‖ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hBM
  have h1 : 0 ≤ matrixNormBridge n := matrixNormBridge_nonneg
  have h2 : 0 ≤ 3 / 2 - σ := by linarith
  let R := max 1 (2 * (‖C‖ + 2 * M))
  by_cases hs : |s| ≤ R
  · have hs' : s ∈ Set.Icc (-R) R := abs_le.mp hs
    have hh := pairedFieldIntegrand_lipschitz_global hσ hδ hC hB hD s
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    unfold fieldLipEnvelope
    rw [Set.indicator_of_mem hs']
    exact le_add_of_nonneg_right (by positivity)
  · have hh := pairedFieldIntegrand_lipschitz_tail hσ hδ hC hB hD hBM hDM
      (le_of_not_ge hs)
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact le_add_of_nonneg_left (Set.indicator_nonneg (fun _ _ ↦ by positivity) _)

lemma hermitianField_lipschitz_bound {σ δ M : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B D : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) (hD : D.IsHermitian)
    (hBM : ‖B‖ ≤ M) (hDM : ‖D‖ ≤ M) :
    ‖hermitianField σ δ C B - hermitianField σ δ C D‖ ≤
      (|fieldNormalization σ / 2| * ∫ s : ℝ, fieldLipEnvelope σ δ M C s) * ‖B - D‖ := by
  have hiB := integrable_pairedFieldIntegrand hσ hδ hC hB
  have hiD := integrable_pairedFieldIntegrand hσ hδ hC hD
  unfold hermitianField
  rw [← smul_sub, ← integral_sub hiB hiD, norm_smul, Real.norm_eq_abs]
  have hh := norm_integral_le_of_norm_le (integrable_fieldLipEnvelope hσ M C |>.mul_const ‖B - D‖)
    (Filter.Eventually.of_forall (pairedFieldIntegrand_lipschitz_envelope hσ hδ hC hB hD hBM hDM))
  rw [integral_mul_const] at hh
  exact (mul_le_mul_of_nonneg_left hh (abs_nonneg _)).trans_eq (mul_assoc _ _ _).symm

lemma hermitianField_locallyLipschitz {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C : Matrix n n ℂ} (hC : C.IsHermitian) :
    LocallyLipschitz (fun B : selfAdjoint (Matrix n n ℂ) ↦ hermitianField σ δ C B) := by
  intro B
  let M : ℝ := ‖B‖ + 1
  let L : ℝ := |fieldNormalization σ / 2| * ∫ s : ℝ, fieldLipEnvelope σ δ M C s
  have hL : 0 ≤ L := mul_nonneg (abs_nonneg _) (integral_nonneg (fun s ↦
    fieldLipEnvelope_nonneg hσ hδ (by dsimp [M]; positivity) C s))
  refine ⟨⟨L, hL⟩, Metric.ball B 1, Metric.ball_mem_nhds B (by norm_num), ?_⟩
  change @LipschitzOnWith _ _ (PseudoMetricSpace.toPseudoEMetricSpace)
    (PseudoMetricSpace.toPseudoEMetricSpace) _ _ _
  apply lipschitzOnWith_iff_norm_sub_le.mpr
  intro A hA D hD
  have hAM : ‖(A : Matrix n n ℂ)‖ ≤ M := by
    change ‖A‖ ≤ ‖B‖ + 1
    exact norm_le_norm_add_const_of_dist_le (Metric.mem_ball.mp hA).le
  have hDM : ‖(D : Matrix n n ℂ)‖ ≤ M := by
    change ‖D‖ ≤ ‖B‖ + 1
    exact norm_le_norm_add_const_of_dist_le (Metric.mem_ball.mp hD).le
  exact hermitianField_lipschitz_bound hσ hδ hC A.prop D.prop hAM hDM

end SharpLiebThirring.MatrixProof

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.FieldPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u32 u33 u34

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open scoped NNReal


namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
variable {N : ℕ}

lemma matrixField_eq_realPart {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (k : Fin N → ℝ) {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.IsHermitian) :
    matrixField σ δ k B = realPartCLM (hermitianField σ δ
      (complexify (diagonal (fun i ↦ k i ^ 2))) (complexify B)) := by
  rw [← complexify_matrixField hσ hδ k hB, realPartCLM_complexify]

lemma matrixField_continuous {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (k : Fin N → ℝ) :
    Continuous (fun B : selfAdjoint (Matrix (Fin N) (Fin N) ℝ) ↦ matrixField σ δ k B) := by
  have hc := (hermitianField_locallyLipschitz hσ hδ
    (complexify_hermitian (isHermitian_diagonal (fun i ↦ k i ^ 2)))).continuous
  have hh := realPartCLM.continuous.comp (hc.comp realHermitianComplexify_continuous)
  convert! hh using 1
  funext B
  exact matrixField_eq_realPart hσ hδ k B.prop

end SharpLiebThirring.MatrixProof

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.ActionPenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u35

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open scoped NNReal


namespace SharpLiebThirring.ActionProof
open Set Filter

/-- The compact penalty argument, with no convergence of
minimizers or chosen coefficients required. -/
lemma compact_penalty_bound {E : Type u35} [TopologicalSpace E] {K : Set E}
    (hK : IsCompact K) {f g : E → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hg0 : ∀ x ∈ K, 0 ≤ g x) (hzero : ∀ x ∈ K, g x = 0 → f x ≤ 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ x ∈ K, f x - g x / ε ≤ η := by
  let S := K ∩ {x | η ≤ f x}
  have hS : IsCompact S := hK.inter_right (isClosed_le continuous_const hf)
  obtain ⟨F, hF⟩ := (hK.image hf).bddAbove
  by_cases hne : S.Nonempty
  · obtain ⟨y, hy, hmin⟩ := hS.exists_isMinOn hne hg.continuousOn
    have hgy : 0 < g y := lt_of_le_of_ne (hg0 y hy.1) (by
      intro he
      have := hzero y hy.1 he.symm
      dsimp [S] at hy
      have hηy : η ≤ f y := hy.2
      linarith)
    have hF1 : 0 < max F 1 := lt_of_lt_of_le (by norm_num) (le_max_right F 1)
    refine ⟨g y / max F 1, div_pos hgy hF1, ?_⟩
    intro ε hε hε₀ x hx
    by_cases hfx : η ≤ f x
    · have hxy : g y ≤ g x := hmin ⟨hx, hfx⟩
      have hprod : ε * max F 1 ≤ g y := (le_div_iff₀ hF1).mp hε₀
      have hr : max F 1 ≤ g x / ε := (le_div_iff₀ hε).mpr (by nlinarith)
      have := (hF (Set.mem_image_of_mem f hx)).trans (le_max_left F 1)
      linarith
    · exact (sub_le_self _ (div_nonneg (hg0 x hx) hε.le)).trans (le_of_not_ge hfx)
  · refine ⟨1, by norm_num, ?_⟩
    intro ε hε _ x hx
    have hfx : f x < η := lt_of_not_ge (fun hh ↦ hne ⟨x, hx, hh⟩)
    exact (sub_le_self _ (div_nonneg (hg0 x hx) hε.le)).trans hfx.le

end SharpLiebThirring.ActionProof

namespace SharpLiebThirring.ActionProof
open Matrix MatrixProof Set
open scoped Matrix.Norms.L2Operator
variable {N : ℕ}

lemma actionDefect_continuous {σ : ℝ} (hσ : 0 < σ) (k : Fin N → ℝ) :
    Continuous (actionDefect σ k) := by
  apply Continuous.sub
  · exact (by fun_prop : Continuous (fun z : selfAdjoint (Matrix (Fin N) (Fin N) ℝ) × (Fin N → ℝ) ↦
      ∑ i, z.2 i ^ 2)).rpow_const (fun _ ↦ Or.inr (by positivity))
  · unfold mulVec dotProduct
    fun_prop

lemma constraintDefect_continuous {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (k : Fin N → ℝ) :
    Continuous (constraintDefect σ δ k) := by
  have hc : Continuous (fun z : selfAdjoint (Matrix (Fin N) (Fin N) ℝ) × (Fin N → ℝ) ↦
      matrixField σ δ k z.1) := (matrixField_continuous hσ hδ k).comp continuous_fst
  unfold constraintDefect
  fun_prop

lemma constraintDefect_nonneg (σ δ : ℝ) (k : Fin N → ℝ)
    (z : selfAdjoint (Matrix (Fin N) (Fin N) ℝ) × (Fin N → ℝ)) :
    0 ≤ constraintDefect σ δ k z := by
  unfold constraintDefect
  exact Finset.sum_nonneg (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ sq_nonneg _))

lemma constraintDefect_eq_zero_iff (σ δ : ℝ) (k : Fin N → ℝ)
    (z : selfAdjoint (Matrix (Fin N) (Fin N) ℝ) × (Fin N → ℝ)) :
    constraintDefect σ δ k z = 0 ↔ matrixField σ δ k z.1 = vecMulVec z.2 z.2 := by
  constructor
  · intro h
    ext i j
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ sq_nonneg
        (matrixField σ δ k z.1 i j - z.2 i * z.2 j)))).mp h i (Finset.mem_univ i)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg
      (matrixField σ δ k z.1 i j - z.2 i * z.2 j))).mp hi j (Finset.mem_univ j)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hij)
  · intro h
    simp [constraintDefect, h, vecMulVec]

/-- Uniform compact penalty estimate for the matrix field and rank-one
constraint. -/
lemma matrix_compact_penalty_oai {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ)
    (k : Fin N → ℝ)
    {K : Set (selfAdjoint (Matrix (Fin N) (Fin N) ℝ) × (Fin N → ℝ))} (hK : IsCompact K)
    {η : ℝ} (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ z ∈ K,
      actionDefect σ k z - constraintDefect σ δ k z / ε ≤ η := by
  apply compact_penalty_bound hK (actionDefect_continuous hσ₀ k)
    (constraintDefect_continuous hσ₁ hδ k) (fun z _ ↦ constraintDefect_nonneg σ δ k z) _ hη
  intro z _ hz
  exact sub_nonpos.mpr (source_rankone_comparison hσ₀ hσ₁ hδ k z.1.prop z.2
    ((constraintDefect_eq_zero_iff σ δ k z).mp hz))

end SharpLiebThirring.ActionProof

end
end
end

end OAI
end

theorem solution : type_of% @OAI.SharpLiebThirring.ActionProof.matrix_compact_penalty_oai := @OAI.SharpLiebThirring.ActionProof.matrix_compact_penalty_oai
