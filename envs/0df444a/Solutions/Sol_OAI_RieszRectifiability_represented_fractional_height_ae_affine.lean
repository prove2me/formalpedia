-- Prove2me | solution 1 for OAI.RieszRectifiability.represented_fractional_height_ae_affine
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:41.521598+00:00
-- url     : https://prove2.me/submissions/ea73818d-8d5a-413b-930d-72d8cd17224e

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_DegreeOnePolynomialAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Affine representations of degree-one polynomials

Evaluation of a homogeneous degree-one complex polynomial on real Euclidean
space is a continuous real-linear map. Splitting off the constant homogeneous
component gives an affine representation for polynomials of degree at most one.
-/

namespace RieszRectifiability

noncomputable section

theorem homogeneous_degree_one_eval_linear {d : ℕ}
    (P : MvPolynomial (Fin d) ℂ) (hP : P.IsHomogeneous 1) :
    ∃ L : Ambient d →L[ℝ] ℂ, ∀ x : Ambient d,
      MvPolynomial.eval (fun j => (x j : ℂ)) P = L x := by
  have hmem : P ∈ Submodule.span ℂ (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) ℂ)) := by
    rw [← MvPolynomial.homogeneousSubmodule_one_eq_span_X]
    exact hP
  clear hP
  induction hmem using Submodule.span_induction with
  | mem Q hQ =>
    obtain ⟨i, rfl⟩ := hQ
    refine ⟨Complex.ofRealCLM.comp (EuclideanSpace.proj i), fun x => ?_⟩
    rw [MvPolynomial.eval_X]
    rfl
  | zero =>
    exact ⟨0, fun x => by simp only [map_zero, zero_apply]⟩
  | add Q R _ _ hQ hR =>
    obtain ⟨L, hL⟩ := hQ
    obtain ⟨M, hM⟩ := hR
    refine ⟨L + M, fun x => ?_⟩
    rw [map_add, hL x, hM x]
    rfl
  | smul c Q _ hQ =>
    obtain ⟨L, hL⟩ := hQ
    refine ⟨c • L, fun x => ?_⟩
    rw [MvPolynomial.smul_eval, hL x]
    rfl

theorem degree_one_polynomial_eval_affine {d : ℕ}
    (P : MvPolynomial (Fin d) ℂ) (hP : P.totalDegree ≤ 1) :
    ∃ c : ℂ, ∃ L : Ambient d →L[ℝ] ℂ, ∀ x : Ambient d,
      MvPolynomial.eval (fun j => (x j : ℂ)) P = c + L x := by
  rcases (show P.totalDegree = 0 ∨ P.totalDegree = 1 by omega) with h0 | h1
  · have heq := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0
    refine ⟨P.coeff 0, 0, fun x => ?_⟩
    calc
      _ = MvPolynomial.eval (fun j => (x j : ℂ)) (MvPolynomial.C (P.coeff 0)) :=
        congrArg (MvPolynomial.eval (fun j => (x j : ℂ))) heq
      _ = _ := by simp only [MvPolynomial.eval_C, zero_apply, add_zero]
  · obtain ⟨L, hL⟩ := homogeneous_degree_one_eval_linear (MvPolynomial.homogeneousComponent 1 P)
      (MvPolynomial.homogeneousComponent_isHomogeneous 1 P)
    have hsplit : P = MvPolynomial.C (P.coeff 0) + MvPolynomial.homogeneousComponent 1 P := by
      have h := MvPolynomial.sum_homogeneousComponent P
      rw [h1] at h
      simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        MvPolynomial.homogeneousComponent_zero] using! h.symm
    refine ⟨P.coeff 0, L, fun x => ?_⟩
    calc
      _ = MvPolynomial.eval (fun j => (x j : ℂ))
          (MvPolynomial.C (P.coeff 0) + MvPolynomial.homogeneousComponent 1 P) :=
        congrArg (MvPolynomial.eval (fun j => (x j : ℂ))) hsplit
      _ = _ := by rw [map_add, MvPolynomial.eval_C, hL x]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ClosedTailBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem closedExterior_measurable {d : ℕ} (a : Ambient d) (R : ℝ) :
    MeasurableSet (closedExterior a R) :=
  measurableSet_le measurable_const (continuous_const.dist continuous_id).measurable

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_SchwartzPairingSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap
open scoped ContDiff

theorem complex_schwartz_pairing_ae_eq {d : ℕ} (f h : Ambient d → ℂ)
    (hf : LocallyIntegrable f) (hh : LocallyIntegrable h)
    (heq : ∀ g : 𝓢(Ambient d, ℂ), (∫ x, f x * g x) = ∫ x, h x * g x) :
    f =ᵐ[volume] h := by
  apply ae_eq_of_integral_contDiff_smul_eq hf hh
  intro g hg hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let G : 𝓢(Ambient d, ℂ) := hc'.toSchwartzMap hg'
  have hmul : ∀ (a : Ambient d → ℂ) x, g x • a x = a x * G x := by
    intro a x
    change g x • a x = a x * (g x : ℂ)
    erw [Complex.real_smul]
    exact mul_comm _ _
  calc
    _ = ∫ x, f x * G x := integral_congr_ae (Filter.Eventually.of_forall (hmul f))
    _ = ∫ x, h x * G x := heq G
    _ = _ := (integral_congr_ae (Filter.Eventually.of_forall (hmul h))).symm

theorem mvPolynomial_complex_eval_continuous {d : ℕ} (P : MvPolynomial (Fin d) ℂ) :
    Continuous (fun x : Ambient d => MvPolynomial.eval (fun j => (x j : ℂ)) P) := by
  exact P.continuous_eval.comp (by fun_prop)

theorem locallyIntegrable_complex_of_real {d : ℕ} (w : Ambient d → ℝ)
    (hw : LocallyIntegrable w) : LocallyIntegrable (fun x => (w x : ℂ)) := by
  intro x
  obtain ⟨U, hU, hi⟩ := hw x
  exact ⟨U, hU, hi.ofReal⟩

theorem real_height_ae_eq_polynomial_of_pairings {d : ℕ}
    (w : Ambient d → ℝ) (hw : LocallyIntegrable w) (P : MvPolynomial (Fin d) ℂ)
    (heq : ∀ g : 𝓢(Ambient d, ℂ), (∫ x, w x • g x) =
      ∫ x, MvPolynomial.eval (fun j => (x j : ℂ)) P * g x) :
    ∀ᵐ x, (w x : ℂ) = MvPolynomial.eval (fun j => (x j : ℂ)) P := by
  apply complex_schwartz_pairing_ae_eq _ _ (locallyIntegrable_complex_of_real w hw)
    (mvPolynomial_complex_eval_continuous P).locallyIntegrable
  intro g
  calc
    _ = ∫ x, w x • g x := by
      apply integral_congr_ae
      filter_upwards with x
      erw [Complex.real_smul]
    _ = _ := heq g

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FourierMeanZeroTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap
open scoped FourierTransform

theorem schwartz_fourier_at_zero {d : ℕ} (g : 𝓢(Ambient d, ℂ)) :
    (𝓕 g) (0 : Ambient d) = ∫ x, g x := by
  change 𝓕 (g : Ambient d → ℂ) (0 : Ambient d) = _
  simp [Real.fourier_eq]

theorem schwartz_inverse_fourier_integral {d : ℕ} (g : 𝓢(Ambient d, ℂ)) :
    (∫ x, (𝓕⁻ g) x) = g 0 := by
  rw [← schwartz_fourier_at_zero, FourierTransform.fourier_fourierInv_eq]

theorem inverse_fourier_mean_zero_of_zero_at_origin {d : ℕ} (g : 𝓢(Ambient d, ℂ))
    (hg : g 0 = 0) : (∫ x, (𝓕⁻ g) x) = 0 :=
  (schwartz_inverse_fourier_integral g).trans hg

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FourierJetMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fourier jets and Schwartz moments

Iterated directional Fourier derivatives correspond to polynomially weighted
Schwartz functions. Evaluating these derivatives at zero expresses Fourier jets
as integrable moments with the appropriate Fourier normalization factor.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap LineDeriv
open scoped FourierTransform

theorem fourierMomentSchwartz_apply {d n : ℕ} (m : Fin n → Ambient d)
    (g : 𝓢(Ambient d, ℂ)) (x : Ambient d) :
    fourierMomentSchwartz m g x = fourierDerivativeFactor ^ n *
      (∏ i, (inner ℝ x (m i) : ℂ)) * g x := by
  induction n with
  | zero => simp [fourierMomentSchwartz]
  | succ n ih =>
    have hm : (inner ℝ · (m 0)).HasTemperateGrowth :=
      ((innerSL ℝ).flip (m 0)).hasTemperateGrowth
    simp only [fourierMomentSchwartz, smul_apply]
    erw [smulLeftCLM_apply_apply hm, ih]
    erw [Complex.real_smul]
    rw [smul_eq_mul, Fin.prod_univ_succ, pow_succ]
    simp only [Fin.tail_def]
    ring

theorem iteratedLineDeriv_fourier_moment {d n : ℕ} (m : Fin n → Ambient d)
    (g : 𝓢(Ambient d, ℂ)) :
    ∂^{m} (𝓕 g) = 𝓕 (fourierMomentSchwartz m g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedLineDerivOp_succ_left, ih, lineDerivOp_fourier_eq]
    rfl

theorem fourier_jet_at_zero_eq_moment {d n : ℕ} (m : Fin n → Ambient d)
    (g : 𝓢(Ambient d, ℂ)) :
    iteratedFDeriv ℝ n (𝓕 g : 𝓢(Ambient d, ℂ)) 0 m =
      ∫ x, fourierDerivativeFactor ^ n * (∏ i, (inner ℝ x (m i) : ℂ)) * g x := by
  rw [← SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv,
    iteratedLineDeriv_fourier_moment, schwartz_fourier_at_zero]
  simp_rw [fourierMomentSchwartz_apply]

theorem fourier_jet_moment_integrable {d n : ℕ} (m : Fin n → Ambient d)
    (g : 𝓢(Ambient d, ℂ)) :
    Integrable (fun x => fourierDerivativeFactor ^ n *
      (∏ i, (inner ℝ x (m i) : ℂ)) * g x) := by
  exact (fourierMomentSchwartz m g).integrable.congr
    (Filter.Eventually.of_forall (fourierMomentSchwartz_apply m g))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_SchwartzJetCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap LineDeriv
open scoped LineDeriv

theorem schwartzJetCoordinates_apply (d N : ℕ) (g : 𝓢(Ambient d, ℂ))
    (i : JetCoordinateIndex d N) :
    schwartzJetCoordinates d N g i =
      iteratedFDeriv ℝ i.1.val g 0 (fun j => EuclideanSpace.basisFun (Fin d) ℝ (i.2 j)) := by
  change (∂^{fun j => EuclideanSpace.basisFun (Fin d) ℝ (i.2 j)} g) 0 = _
  exact SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv

theorem schwartzJetCoordinates_eq_iff (d N : ℕ) (g h : 𝓢(Ambient d, ℂ)) :
    schwartzJetCoordinates d N g = schwartzJetCoordinates d N h ↔
      ∀ i, i ≤ N → iteratedFDeriv ℝ i g 0 = iteratedFDeriv ℝ i h 0 := by
  constructor
  · intro heq i hi
    have hm : (iteratedFDeriv ℝ i g 0).toMultilinearMap =
        (iteratedFDeriv ℝ i h 0).toMultilinearMap := by
      apply Module.Basis.ext_multilinear (fun _ : Fin i => (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)
      intro v
      have hv := congrFun heq (⟨⟨i, by omega⟩, v⟩ : JetCoordinateIndex d N)
      simpa only [schwartzJetCoordinates_apply] using! hv
    ext v
    exact congrArg (fun f => f v) hm
  · intro heq
    funext i
    rw [schwartzJetCoordinates_apply, schwartzJetCoordinates_apply,
      heq i.1.val (by omega)]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_JetMomentPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Polynomial pairings for Fourier jets

A finite family of jet coefficients defines a multivariable moment polynomial.
Its pairing with a Schwartz function is integrable and equals the corresponding
linear combination of Fourier derivatives at zero.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap
open scoped FourierTransform

theorem jetMomentPolynomial_eval {d N : ℕ} (c : JetCoordinateIndex d N → ℂ)
    (x : Ambient d) :
    MvPolynomial.eval (fun j => (x j : ℂ)) (jetMomentPolynomial c) =
      ∑ i, c i * fourierDerivativeFactor ^ i.1.val *
        ∏ j, (inner ℝ x (EuclideanSpace.basisFun (Fin d) ℝ (i.2 j)) : ℂ) := by
  simp only [jetMomentPolynomial, map_sum, map_mul, map_prod,
    MvPolynomial.eval_C, MvPolynomial.eval_X, EuclideanSpace.inner_basisFun_real]

theorem fourier_jet_sum_eq_polynomial_pairing {d N : ℕ}
    (c : JetCoordinateIndex d N → ℂ) (g : 𝓢(Ambient d, ℂ)) :
    (∑ i, c i * iteratedFDeriv ℝ i.1.val (𝓕 g : 𝓢(Ambient d, ℂ)) 0
      (fun j => EuclideanSpace.basisFun (Fin d) ℝ (i.2 j))) =
      ∫ x, MvPolynomial.eval (fun j => (x j : ℂ)) (jetMomentPolynomial c) * g x := by
  have hi : ∀ i : JetCoordinateIndex d N, Integrable
      (fun x => c i * (fourierDerivativeFactor ^ i.1.val *
        (∏ j, (inner ℝ x (EuclideanSpace.basisFun (Fin d) ℝ (i.2 j)) : ℂ)) * g x)) :=
    fun i => (fourier_jet_moment_integrable
      (fun j => EuclideanSpace.basisFun (Fin d) ℝ (i.2 j)) g).const_mul (c i)
  calc
    _ = ∑ i, ∫ x, c i * (fourierDerivativeFactor ^ i.1.val *
        (∏ j, (inner ℝ x (EuclideanSpace.basisFun (Fin d) ℝ (i.2 j)) : ℂ)) * g x) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [fourier_jet_at_zero_eq_moment]
      erw [integral_const_mul]
    _ = ∫ x, ∑ i, c i * (fourierDerivativeFactor ^ i.1.val *
        (∏ j, (inner ℝ x (EuclideanSpace.basisFun (Fin d) ℝ (i.2 j)) : ℂ)) * g x) :=
      (integral_finsetSum _ (fun i _ => hi i)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [jetMomentPolynomial_eval, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_LinearCoordinateFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

theorem linear_functional_finite_coordinate_representation
    {E ι : Type*} [AddCommGroup E] [Module ℂ E] [Fintype ι]
    (J : E →ₗ[ℂ] (ι → ℂ)) (T : E →ₗ[ℂ] ℂ)
    (hker : ∀ x, J x = 0 → T x = 0) :
    ∃ c : ι → ℂ, ∀ x, T x = ∑ i, c i * J x i := by
  classical
  have hk : LinearMap.ker J ≤ LinearMap.ker T := fun x hx => hker x hx
  let qT : (E ⧸ LinearMap.ker J) →ₗ[ℂ] ℂ := (LinearMap.ker J).liftQ T hk
  let a : LinearMap.range J →ₗ[ℂ] ℂ := qT.comp J.quotKerEquivRange.symm.toLinearMap
  obtain ⟨A, hA⟩ := a.exists_extend
  have hfactor : ∀ x, A (J x) = T x := by
    intro x
    calc
      A (J x) = a ⟨J x, ⟨x, rfl⟩⟩ := LinearMap.congr_fun hA ⟨J x, ⟨x, rfl⟩⟩
      _ = T x := by
        exact congrArg qT (J.quotKerEquivRange_symm_apply_image x ⟨x, rfl⟩)
  refine ⟨fun i => A (Pi.single i 1), fun x => ?_⟩
  rw [← hfactor x]
  have hx : J x = ∑ i, (J x i) • (Pi.single i (1 : ℂ) : ι → ℂ) := by
    ext i
    simp [Pi.single_apply]
  conv_lhs => rw [hx, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul, mul_comm]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ExpandingSmoothCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Expanding smooth cutoffs

Dilating a fixed bump gives compactly supported smooth cutoffs equal to one on
balls of increasing radius. Composition with linear contractions bounds all
derivatives by Schwartz seminorms and supplies uniform derivative bounds for
the cutoff errors.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology
open scoped ContDiff

theorem expandingSmoothCutoff_smooth (d j : ℕ) :
    ContDiff ℝ ∞ (expandingSmoothCutoff d j) := by
  apply (unitSmoothCutoff d).contDiff.comp
  exact (contDiff_id : ContDiff ℝ ∞ (fun x : Ambient d => x)).const_smul _

theorem expandingSmoothCutoff_compact (d j : ℕ) :
    HasCompactSupport (expandingSmoothCutoff d j) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Ambient d) (2 * ((j : ℝ) + 1)))
  intro x hx
  apply (unitSmoothCutoff d).zero_of_le_dist
  have hR : 0 < (j : ℝ) + 1 := by positivity
  have hx' : 2 * ((j : ℝ) + 1) < ‖x‖ := by
    simpa only [mem_closedBall, dist_zero_right, not_le] using! hx
  change 2 ≤ dist (((j : ℝ) + 1)⁻¹ • x) 0
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
  exact (le_div_iff₀ hR).2 hx'.le |>.trans_eq (div_eq_inv_mul _ _)

theorem expandingSmoothCutoff_one (d j : ℕ) (x : Ambient d)
    (hx : x ∈ ball (0 : Ambient d) ((j : ℝ) + 1)) :
    expandingSmoothCutoff d j x = 1 := by
  apply (unitSmoothCutoff d).one_of_mem_closedBall
  have hR : 0 < (j : ℝ) + 1 := by positivity
  have hx' : ‖x‖ < (j : ℝ) + 1 := by
    simpa only [mem_ball, dist_zero_right] using! hx
  change dist (((j : ℝ) + 1)⁻¹ • x) 0 ≤ 1
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
  have hh : ‖x‖ / ((j : ℝ) + 1) ≤ 1 := (div_le_one hR).2 hx'.le
  simpa only [div_eq_inv_mul] using! hh

theorem schwartz_contraction_derivative_bound {d : ℕ} (g : 𝓢(Ambient d, ℝ))
    (S : Ambient d →L[ℝ] Ambient d) (hS : ‖S‖ ≤ 1) (n : ℕ) (x : Ambient d) :
    ‖iteratedFDeriv ℝ n (g ∘ S) x‖ ≤ SchwartzMap.seminorm ℝ 0 n g := by
  rw [S.iteratedFDeriv_comp_right (g.smooth n) x le_rfl]
  have hp : (∏ _ : Fin n, ‖S‖) ≤ 1 := by
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hS)
  calc
    _ ≤ ‖iteratedFDeriv ℝ n g (S x)‖ * ∏ _ : Fin n, ‖S‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ n g (S x)‖ := by nlinarith [norm_nonneg (iteratedFDeriv ℝ n g (S x))]
    _ ≤ _ := g.norm_iteratedFDeriv_le_seminorm ℝ n (S x)

theorem expandingSmoothCutoff_error_uniform_derivatives (d : ℕ) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧ ∀ j n x,
      ‖iteratedFDeriv ℝ n (fun y => expandingSmoothCutoff d j y - 1) x‖ ≤ C n := by
  let β : 𝓢(Ambient d, ℝ) := (unitSmoothCutoff d).hasCompactSupport.toSchwartzMap
    (unitSmoothCutoff d).contDiff
  refine ⟨fun n => SchwartzMap.seminorm ℝ 0 n β + 1, fun n => by positivity, ?_⟩
  intro j n x
  let S : Ambient d →L[ℝ] Ambient d := ((j : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ (Ambient d)
  have hR : 1 ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
  have hS : ‖S‖ ≤ 1 := by
    calc
      ‖S‖ ≤ ‖((j : ℝ) + 1)⁻¹‖ * ‖ContinuousLinearMap.id ℝ (Ambient d)‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ 1 * 1 := mul_le_mul
        (by rw [Real.norm_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ hR)
        ContinuousLinearMap.norm_id_le (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1
  have heq : (expandingSmoothCutoff d j : Ambient d → ℝ) = β ∘ S := rfl
  have hb := schwartz_contraction_derivative_bound β S hS n x
  have hs : ContDiff ℝ n (expandingSmoothCutoff d j) := by
    rw [heq]
    exact (β.smooth n).comp S.contDiff
  have hc : ‖iteratedFDeriv ℝ n (fun _ : Ambient d => (1 : ℝ)) x‖ ≤ 1 := by
    cases n with
    | zero => simp
    | succ n => simp [iteratedFDeriv_succ_const]
  have hh := iteratedFDeriv_sub_apply hs.contDiffAt
    (contDiffAt_const (c := (1 : ℝ)) : ContDiffAt ℝ n (fun _ : Ambient d => (1 : ℝ)) x)
  change ‖iteratedFDeriv ℝ n ((expandingSmoothCutoff d j) - (fun _ => 1)) x‖ ≤ _
  rw [hh]
  exact (norm_sub_le _ _).trans (add_le_add (by simpa only [heq] using! hb) hc)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_SchwartzCutoffConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology
open scoped ContDiff

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem schwartz_cutoff_error_seminorm_le
    (g : 𝓢(Ambient d, F)) (q : Ambient d → ℝ) (hq : q.HasTemperateGrowth)
    (C : ℕ → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i x, ‖iteratedFDeriv ℝ i q x‖ ≤ C i)
    (R : ℝ) (hR : 0 < R) (hzero : ∀ x ∈ ball (0 : Ambient d) R, q x = 0)
    (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n (smulLeftCLM F q g) ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C i *
        SchwartzMap.seminorm ℝ (k + 1) (n - i) g) / R := by
  have hM : 0 ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C i *
      SchwartzMap.seminorm ℝ (k + 1) (n - i) g := by
    exact Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity) (hC i))
      (apply_nonneg _ _)
  apply seminorm_le_bound ℝ k n _ (div_nonneg hM hR.le)
  intro x
  rw [smulLeftCLM_apply hq]
  by_cases hx : x ∈ ball (0 : Ambient d) R
  · have heq : (fun y => q y • g y) =ᶠ[𝓝 x] (fun _ => (0 : F)) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      simp [hzero y hy]
    have he := (heq.iteratedFDeriv ℝ n).eq_of_nhds
    rw [he]
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero] using! div_nonneg hM hR.le
  · have hxR : R ≤ ‖x‖ := by simpa only [mem_ball, dist_zero_right, not_lt] using! hx
    have hp := norm_iteratedFDeriv_smul_le hq.1 (g.smooth ⊤) x (n := n) (mod_cast le_top)
    apply (le_div_iff₀ hR).2
    calc
      (‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => q y • g y) x‖) * R ≤
          R * ‖x‖ ^ k * (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i q x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖) := by
        nlinarith [mul_le_mul_of_nonneg_left hp (pow_nonneg (norm_nonneg x) k)]
      _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i q x‖ *
            (R * (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) g x‖)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C i *
          SchwartzMap.seminorm ℝ (k + 1) (n - i) g := by
        apply Finset.sum_le_sum
        intro i _
        have hw : R * (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) g x‖) ≤
            SchwartzMap.seminorm ℝ (k + 1) (n - i) g := by
          calc
            _ ≤ ‖x‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) g x‖) := by gcongr
            _ = ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ (n - i) g x‖ := by ring
            _ ≤ _ := le_seminorm ℝ (k + 1) (n - i) g x
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hbound i x) (by positivity)) hw
          (by positivity) (mul_nonneg (by positivity) (hC i))

theorem schwartz_cutoff_errors_tendsto_zero
    (g : 𝓢(Ambient d, F)) (q : ℕ → Ambient d → ℝ)
    (hq : ∀ j, (q j).HasTemperateGrowth)
    (C : ℕ → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ j i x, ‖iteratedFDeriv ℝ i (q j) x‖ ≤ C i)
    (R : ℕ → ℝ) (hR : ∀ j, 0 < R j) (hRt : Tendsto R atTop atTop)
    (hzero : ∀ j x, x ∈ ball (0 : Ambient d) (R j) → q j x = 0) :
    Tendsto (fun j => smulLeftCLM F (q j) g) atTop (𝓝 0) := by
  apply (schwartz_withSeminorms ℝ (Ambient d) F).tendsto_nhds _ _ |>.2
  rintro ⟨k, n⟩ ε hε
  let M := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C i *
    SchwartzMap.seminorm ℝ (k + 1) (n - i) g
  have ht : Tendsto (fun j => M / R j) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using! tendsto_const_nhds.mul hRt.inv_tendsto_atTop
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with j hj
  simpa only [sub_zero, schwartzSeminormFamily_apply] using!
    (schwartz_cutoff_error_seminorm_le g (q j) (hq j) C hC (hbound j)
      (R j) (hR j) (hzero j) k n).trans_lt hj

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_SchwartzSupportLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Support-preserving Schwartz approximation

Multiplication by expanding cutoffs gives compact approximants whose topological
supports remain inside that of the original test. This extends vanishing of tempered
distributions on compact tests away from the origin to all Schwartz tests away from
the origin, and shows that such distributions depend only on the test's germ there.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set
open scoped ContDiff

theorem exists_compact_schwartz_approximation_with_support {d : ℕ}
    (g : 𝓢(Ambient d, ℂ)) :
    ∃ G : ℕ → 𝓢(Ambient d, ℂ), (∀ j, HasCompactSupport (G j)) ∧
      (∀ j, tsupport (G j) ⊆ tsupport g) ∧ Tendsto G atTop (𝓝 g) := by
  let G : ℕ → 𝓢(Ambient d, ℂ) := fun j => smulLeftCLM ℂ (expandingSmoothCutoff d j) g
  let q : ℕ → Ambient d → ℝ := fun j x => expandingSmoothCutoff d j x - 1
  have hβ : ∀ j, (expandingSmoothCutoff d j).HasTemperateGrowth :=
    fun j => (expandingSmoothCutoff_compact d j).hasTemperateGrowth (expandingSmoothCutoff_smooth d j)
  have hq : ∀ j, (q j).HasTemperateGrowth :=
    fun j => (hβ j).sub (Function.HasTemperateGrowth.const 1)
  obtain ⟨C, hC, hbound⟩ := expandingSmoothCutoff_error_uniform_derivatives d
  have hRt : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hzero : ∀ (j : ℕ) x, x ∈ ball (0 : Ambient d) ((j : ℝ) + 1) → q j x = 0 := by
    intro j x hx
    simp only [q, expandingSmoothCutoff_one d j x hx, sub_self]
  have ht := schwartz_cutoff_errors_tendsto_zero g q hq C hC hbound
    (fun j : ℕ => (j : ℝ) + 1) (fun j => by positivity) hRt hzero
  refine ⟨G, ?_, ?_, ?_⟩
  · intro j
    have hc : HasCompactSupport (fun x => expandingSmoothCutoff d j x • g x) :=
      (expandingSmoothCutoff_compact d j).smul_right
    simpa only [G, smulLeftCLM_apply (hβ j)] using! hc
  · intro j
    simpa only [G, smulLeftCLM_apply (hβ j)] using!
      tsupport_smul_subset_right (expandingSmoothCutoff d j) (g : Ambient d → ℂ)
  · have heq : G = fun j => g + smulLeftCLM ℂ (q j) g := by
      funext j
      ext x
      simp only [G, add_apply, smulLeftCLM_apply_apply (hβ j),
        smulLeftCLM_apply_apply (hq j), q, sub_smul, one_smul]
      abel
    rw [heq]
    simpa only [add_zero] using! tendsto_const_nhds.add ht

theorem tempered_distribution_zero_away_zero_of_compact_tests {d : ℕ}
    (T : 𝓢'(Ambient d, ℂ))
    (hT : ∀ g : 𝓢(Ambient d, ℂ), HasCompactSupport g →
      (0 : Ambient d) ∉ tsupport g → T g = 0)
    (g : 𝓢(Ambient d, ℂ)) (hg : (0 : Ambient d) ∉ tsupport g) : T g = 0 := by
  obtain ⟨G, hc, hs, ht⟩ := exists_compact_schwartz_approximation_with_support g
  have hlim := T.continuous.tendsto g |>.comp ht
  have hz : ∀ j, T (G j) = 0 := fun j => hT (G j) (hc j) (fun h => hg (hs j h))
  apply tendsto_nhds_unique hlim
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)).congr'
    (Eventually.of_forall fun j => (hz j).symm)

theorem tempered_distribution_eq_of_germ_at_zero {d : ℕ}
    (T : 𝓢'(Ambient d, ℂ))
    (hT : ∀ g : 𝓢(Ambient d, ℂ), HasCompactSupport g →
      (0 : Ambient d) ∉ tsupport g → T g = 0)
    (g h : 𝓢(Ambient d, ℂ))
    (hgh : (g : Ambient d → ℂ) =ᶠ[𝓝 (0 : Ambient d)] h) : T g = T h := by
  have hz : (0 : Ambient d) ∉ tsupport (g - h) := by
    apply notMem_tsupport_iff_eventuallyEq.mpr
    filter_upwards [hgh] with x hx
    simp only [sub_apply, Pi.zero_apply, hx, sub_self]
  have heq := tempered_distribution_zero_away_zero_of_compact_tests T hT (g - h) hz
  rw [map_sub, sub_eq_zero] at heq
  exact heq

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ShrinkingSmoothCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap Metric Set
open scoped ContDiff

theorem scaledSmoothCutoff_smooth (d : ℕ) (r : ℝ) :
    ContDiff ℝ ∞ (scaledSmoothCutoff d r) :=
  (unitSmoothCutoff d).contDiff.comp
    ((contDiff_id : ContDiff ℝ ∞ (fun x : Ambient d => x)).const_smul r⁻¹)

theorem scaledSmoothCutoff_zero (d : ℕ) (r : ℝ) (hr : 0 < r)
    (x : Ambient d) (hx : 2 * r ≤ ‖x‖) : scaledSmoothCutoff d r x = 0 := by
  apply (unitSmoothCutoff d).zero_of_le_dist
  change 2 ≤ dist (r⁻¹ • x) 0
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  exact (le_div_iff₀ hr).2 hx |>.trans_eq (div_eq_inv_mul _ _)

theorem scaledSmoothCutoff_support (d : ℕ) (r : ℝ) (hr : 0 < r) :
    tsupport (scaledSmoothCutoff d r) ⊆ closedBall (0 : Ambient d) (2 * r) := by
  apply closure_minimal ?_ isClosed_closedBall
  intro x hx
  by_contra h
  have hn : 2 * r < ‖x‖ := by
    simpa only [mem_closedBall, dist_zero_right, not_le] using! h
  exact hx (scaledSmoothCutoff_zero d r hr x hn.le)

theorem scaledSmoothCutoff_compact (d : ℕ) (r : ℝ) (hr : 0 < r) :
    HasCompactSupport (scaledSmoothCutoff d r) :=
  (isCompact_closedBall (0 : Ambient d) (2 * r)).of_isClosed_subset
    (isClosed_tsupport _) (scaledSmoothCutoff_support d r hr)

theorem scaledSmoothCutoff_one (d : ℕ) (r : ℝ) (hr : 0 < r)
    (x : Ambient d) (hx : x ∈ ball (0 : Ambient d) r) : scaledSmoothCutoff d r x = 1 := by
  apply (unitSmoothCutoff d).one_of_mem_closedBall
  have hx' : ‖x‖ < r := by simpa only [mem_ball, dist_zero_right] using! hx
  change dist (r⁻¹ • x) 0 ≤ 1
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  have hh : ‖x‖ / r ≤ 1 := (div_le_one hr).2 hx'.le
  simpa only [div_eq_inv_mul] using! hh

theorem scaledSmoothCutoff_derivatives (d : ℕ) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧ ∀ r : ℝ, 0 < r → ∀ n x,
      ‖iteratedFDeriv ℝ n (scaledSmoothCutoff d r) x‖ ≤ C n * (r⁻¹) ^ n := by
  let β : 𝓢(Ambient d, ℝ) := (unitSmoothCutoff d).hasCompactSupport.toSchwartzMap
    (unitSmoothCutoff d).contDiff
  refine ⟨fun n => SchwartzMap.seminorm ℝ 0 n β, fun n => apply_nonneg _ _, ?_⟩
  intro r hr n x
  let S : Ambient d →L[ℝ] Ambient d := r⁻¹ • ContinuousLinearMap.id ℝ (Ambient d)
  have hS : ‖S‖ ≤ r⁻¹ := by
    calc
      ‖S‖ ≤ ‖r⁻¹‖ * ‖ContinuousLinearMap.id ℝ (Ambient d)‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ r⁻¹ * 1 := mul_le_mul
        (by rw [Real.norm_of_nonneg (inv_nonneg.mpr hr.le)])
        ContinuousLinearMap.norm_id_le (norm_nonneg _) (inv_nonneg.mpr hr.le)
      _ = _ := mul_one _
  have heq : scaledSmoothCutoff d r = β ∘ S := rfl
  rw [heq, S.iteratedFDeriv_comp_right (β.smooth n) x le_rfl]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n β (S x)‖ * ∏ _ : Fin n, ‖S‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ n β (S x)‖ * ‖S‖ ^ n := by simp
    _ ≤ SchwartzMap.seminorm ℝ 0 n β * (r⁻¹) ^ n :=
      mul_le_mul (β.norm_iteratedFDeriv_le_seminorm ℝ n (S x))
        (pow_le_pow_left₀ (norm_nonneg _) hS n) (by positivity) (apply_nonneg _ _)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_VanishingJetGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap Metric Set
open scoped ContDiff

theorem iteratedFDeriv_growth_of_zero_jets {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Ambient d → F) (hf : ContDiff ℝ ∞ f)
    (M : ℝ) (hM : 0 ≤ M) (n k : ℕ)
    (hz : ∀ j, n ≤ j → j < n + k → iteratedFDeriv ℝ j f 0 = 0)
    (hb : ∀ x, ‖iteratedFDeriv ℝ (n + k) f x‖ ≤ M) (x : Ambient d) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ M * ‖x‖ ^ k := by
  induction k generalizing n x with
  | zero => simpa only [Nat.add_zero, pow_zero, mul_one] using! hb x
  | succ k ih =>
    have hn : ∀ y, ‖iteratedFDeriv ℝ (n + 1) f y‖ ≤ M * ‖y‖ ^ k := by
      intro y
      apply ih (n + 1)
      · intro j hj hjk
        exact hz j (by omega) (by omega)
      · intro z
        rw [show n + 1 + k = n + (k + 1) by omega]
        exact hb z
    have hfinite : ContDiff ℝ (n + 1 : ℕ) f := hf.of_le (by exact_mod_cast le_top)
    have hd : Differentiable ℝ (iteratedFDeriv ℝ n f) :=
      hfinite.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n)
    have hbound : ∀ y ∈ segment ℝ (0 : Ambient d) x,
        ‖fderiv ℝ (iteratedFDeriv ℝ n f) y‖ ≤ M * ‖x‖ ^ k := by
      intro y hy
      rw [norm_fderiv_iteratedFDeriv]
      apply (hn y).trans
      have hxy : ‖y‖ ≤ ‖x‖ := by
        simpa only [sub_zero] using! norm_sub_le_of_mem_segment hy
      gcongr
    have hv := (convex_segment (0 : Ambient d) x).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => hd y) hbound (left_mem_segment ℝ 0 x) (right_mem_segment ℝ 0 x)
    rw [hz n le_rfl (by omega), sub_zero, sub_zero] at hv
    simpa only [pow_succ, mul_assoc] using! hv

theorem schwartz_zero_jet_derivative_bound {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : 𝓢(Ambient d, F)) (N j : ℕ) (hj : j ≤ N + 1)
    (hz : ∀ i, i ≤ N → iteratedFDeriv ℝ i g 0 = 0) (x : Ambient d) :
    ‖iteratedFDeriv ℝ j g x‖ ≤
      SchwartzMap.seminorm ℝ 0 (N + 1) g * ‖x‖ ^ (N + 1 - j) := by
  apply iteratedFDeriv_growth_of_zero_jets g (g.smooth ⊤)
    (SchwartzMap.seminorm ℝ 0 (N + 1) g) (apply_nonneg _ _) j (N + 1 - j)
  · intro i _ hi
    exact hz i (by omega)
  · intro y
    rw [show j + (N + 1 - j) = N + 1 by omega]
    exact norm_iteratedFDeriv_le_seminorm ℝ g (N + 1) y

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_ShrinkingJetSeminorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap Metric Set Filter Topology
open scoped ContDiff

theorem jetCutoffCoefficient_nonneg (C : ℕ → ℝ) (hC : ∀ i, 0 ≤ C i) (n : ℕ) :
    0 ≤ jetCutoffCoefficient C n :=
  Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity) (hC i)) (by positivity)

theorem inverse_scale_cancel (r : ℝ) (hr : 0 < r) (i : ℕ) :
    (r⁻¹) ^ i * (2 * r) ^ (i + 1) = 2 ^ (i + 1) * r := by
  rw [mul_pow, pow_succ r]
  calc
    _ = 2 ^ (i + 1) * ((r⁻¹) ^ i * r ^ i) * r := by ring
    _ = _ := by rw [← mul_pow, inv_mul_cancel₀ hr.ne', one_pow, mul_one]

theorem zero_jet_localized_derivative_bound {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : 𝓢(Ambient d, F)) (n : ℕ)
    (hz : ∀ i, i ≤ n → iteratedFDeriv ℝ i g 0 = 0)
    (q : Ambient d → ℝ) (hq : ContDiff ℝ ∞ q)
    (C : ℕ → ℝ) (hC : ∀ i, 0 ≤ C i) (r : ℝ) (hr : 0 < r)
    (hb : ∀ i x, ‖iteratedFDeriv ℝ i q x‖ ≤ C i * (r⁻¹) ^ i)
    (x : Ambient d) (hx : ‖x‖ ≤ 2 * r) :
    ‖iteratedFDeriv ℝ n (fun y => q y • g y) x‖ ≤
      SchwartzMap.seminorm ℝ 0 (n + 1) g * jetCutoffCoefficient C n * r := by
  let M := SchwartzMap.seminorm ℝ 0 (n + 1) g
  have hM : 0 ≤ M := apply_nonneg _ _
  have hd := norm_iteratedFDeriv_smul_le hq (g.smooth ⊤) x (n := n) (mod_cast le_top)
  apply hd.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), M * ((n.choose i : ℝ) * C i * 2 ^ (i + 1)) * r := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using! hi
      have hg : ‖iteratedFDeriv ℝ (n - i) g x‖ ≤ M * (2 * r) ^ (i + 1) := by
        have ht := schwartz_zero_jet_derivative_bound g n (n - i) (by omega) hz x
        rw [show n + 1 - (n - i) = i + 1 by omega] at ht
        exact ht.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx _) hM)
      calc
        _ ≤ (n.choose i : ℝ) * (C i * (r⁻¹) ^ i) * (M * (2 * r) ^ (i + 1)) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hb i x) (by positivity)) hg
            (norm_nonneg _) (mul_nonneg (by positivity) (mul_nonneg (hC i) (by positivity)))
        _ = M * ((n.choose i : ℝ) * C i) * ((r⁻¹) ^ i * (2 * r) ^ (i + 1)) := by ring
        _ = _ := by rw [inverse_scale_cancel r hr i]; ring
    _ = _ := by
      unfold jetCutoffCoefficient
      rw [Finset.mul_sum, Finset.sum_mul]

theorem zero_jet_localized_seminorm_bound {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : 𝓢(Ambient d, F)) (k n : ℕ)
    (hz : ∀ i, i ≤ n → iteratedFDeriv ℝ i g 0 = 0)
    (q : Ambient d → ℝ) (hq : q.HasTemperateGrowth)
    (C : ℕ → ℝ) (hC : ∀ i, 0 ≤ C i) (r : ℝ) (hr : 0 < r) (hrsmall : 2 * r ≤ 1)
    (hb : ∀ i x, ‖iteratedFDeriv ℝ i q x‖ ≤ C i * (r⁻¹) ^ i)
    (hs : tsupport q ⊆ closedBall (0 : Ambient d) (2 * r)) :
    SchwartzMap.seminorm ℝ k n (smulLeftCLM F q g) ≤
      SchwartzMap.seminorm ℝ 0 (n + 1) g * jetCutoffCoefficient C n * r := by
  have hnonneg : 0 ≤ SchwartzMap.seminorm ℝ 0 (n + 1) g * jetCutoffCoefficient C n * r :=
    mul_nonneg (mul_nonneg (apply_nonneg _ _) (jetCutoffCoefficient_nonneg C hC n)) hr.le
  apply seminorm_le_bound ℝ k n _ hnonneg
  intro x
  rw [smulLeftCLM_apply hq]
  by_cases hx : x ∈ closedBall (0 : Ambient d) (2 * r)
  · have hxr : ‖x‖ ≤ 2 * r := by simpa only [mem_closedBall, dist_zero_right] using! hx
    calc
      _ ≤ 1 * ‖iteratedFDeriv ℝ n (fun y => q y • g y) x‖ :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) (hxr.trans hrsmall)) (norm_nonneg _)
      _ ≤ _ := by
        rw [one_mul]
        exact zero_jet_localized_derivative_bound g n hz q hq.1 C hC r hr hb x hxr
  · have hnot : x ∉ tsupport q := fun h => hx (hs h)
    have heq : (fun y => q y • g y) =ᶠ[𝓝 x] (fun _ => (0 : F)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnot] with y hy
      simp only [Pi.zero_apply] at hy
      rw [hy, zero_smul]
    have hd := (heq.iteratedFDeriv ℝ n).eq_of_nhds
    rw [hd]
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero] using! hnonneg

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ShrinkingSchwartzLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap Metric Set Filter Topology
open scoped ContDiff

theorem shrinkingRadius_pos (j : ℕ) : 0 < shrinkingRadius j := by
  unfold shrinkingRadius
  positivity

theorem shrinkingRadius_small (j : ℕ) : 2 * shrinkingRadius j ≤ 1 := by
  unfold shrinkingRadius
  apply (mul_inv_le_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 2)).2
  linarith [Nat.cast_nonneg (α := ℝ) j]

theorem shrinkingRadius_tendsto : Tendsto shrinkingRadius atTop (𝓝 0) := by
  have ht : Tendsto (fun j : ℕ => (j : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  exact ht.inv_tendsto_atTop

theorem shrinking_cutoff_temperate (d j : ℕ) :
    (scaledSmoothCutoff d (shrinkingRadius j)).HasTemperateGrowth :=
  (scaledSmoothCutoff_compact d _ (shrinkingRadius_pos j)).hasTemperateGrowth
    (scaledSmoothCutoff_smooth d _)

theorem shrinkingSchwartzCutoff_apply {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : 𝓢(Ambient d, F)) (j : ℕ) (x : Ambient d) :
    shrinkingSchwartzCutoff g j x = scaledSmoothCutoff d (shrinkingRadius j) x • g x :=
  smulLeftCLM_apply_apply (shrinking_cutoff_temperate d j) g x

theorem shrinkingSchwartzCutoff_germ {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : 𝓢(Ambient d, F)) (j : ℕ) :
    (shrinkingSchwartzCutoff g j : Ambient d → F) =ᶠ[𝓝 (0 : Ambient d)] g := by
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (shrinkingRadius_pos j))] with x hx
  rw [shrinkingSchwartzCutoff_apply,
    scaledSmoothCutoff_one d _ (shrinkingRadius_pos j) x hx, one_smul]

theorem shrinkingSchwartzCutoff_seminorm_tendsto {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : 𝓢(Ambient d, F)) (k n : ℕ)
    (hz : ∀ i, i ≤ n → iteratedFDeriv ℝ i g 0 = 0) :
    Tendsto (fun j => SchwartzMap.seminorm ℝ k n (shrinkingSchwartzCutoff g j))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := scaledSmoothCutoff_derivatives d
  have hlim : Tendsto (fun j => SchwartzMap.seminorm ℝ 0 (n + 1) g *
      jetCutoffCoefficient C n * shrinkingRadius j) atTop (𝓝 0) := by
    simpa only [mul_zero] using! tendsto_const_nhds.mul shrinkingRadius_tendsto
  apply squeeze_zero (fun j => apply_nonneg _ _) _ hlim
  intro j
  exact zero_jet_localized_seminorm_bound g k n hz _ (shrinking_cutoff_temperate d j)
    C hC (shrinkingRadius j) (shrinkingRadius_pos j) (shrinkingRadius_small j)
    (hb _ (shrinkingRadius_pos j)) (scaledSmoothCutoff_support d _ (shrinkingRadius_pos j))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_SchwartzNormDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap Filter Topology Set MeasureTheory
open scoped FourierTransform ContDiff

theorem schwartzNormDivision_apply {d : ℕ} (g : 𝓢(Ambient d, ℂ))
    (hc : HasCompactSupport g) (hz : (0 : Ambient d) ∉ tsupport g) (x : Ambient d) :
    schwartzNormDivision g hc hz x = ‖x‖⁻¹ • g x := rfl

theorem schwartzNormDivision_norm_mul {d : ℕ} (g : 𝓢(Ambient d, ℂ))
    (hc : HasCompactSupport g) (hz : (0 : Ambient d) ∉ tsupport g) (x : Ambient d) :
    ‖x‖ • schwartzNormDivision g hc hz x = g x := by
  rw [schwartzNormDivision_apply]
  erw [smul_smul]
  by_cases hx : x = 0
  · subst x
    simp +instances [image_eq_zero_of_notMem_tsupport hz]
  · erw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

theorem schwartzNormDivision_inverse_mean_zero {d : ℕ} (g : 𝓢(Ambient d, ℂ))
    (hc : HasCompactSupport g) (hz : (0 : Ambient d) ∉ tsupport g) :
    (∫ x, (𝓕⁻ (schwartzNormDivision g hc hz) : 𝓢(Ambient d, ℂ)) x) = 0 := by
  apply inverse_fourier_mean_zero_of_zero_at_origin
  simp [schwartzNormDivision_apply]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_SchwartzFirstMomentTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set

theorem schwartz_first_absolute_moment_integrable {d : ℕ} (g : 𝓢(Ambient d, ℂ)) :
    Integrable (fun y : Ambient d => ‖y‖ * ‖g y‖) := by
  simpa only [pow_one] using! g.integrable_pow_mul (volume : Measure (Ambient d)) 1

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FourierPhaseDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap
open scoped FourierTransform

theorem fourierPhase_norm {d : ℕ} (ξ x : Ambient d) : ‖fourierPhase ξ x‖ = 1 := by
  simp [fourierPhase, Complex.norm_exp]

theorem fourierPhase_add {d : ℕ} (ξ x h : Ambient d) :
    fourierPhase ξ (x + h) = fourierPhase ξ x * fourierPhase ξ h := by
  unfold fourierPhase
  rw [inner_add_right, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem fourierPhase_sub {d : ℕ} (ξ x h : Ambient d) :
    fourierPhase ξ (x - h) = fourierPhase ξ x * fourierPhase ξ (-h) := by
  rw [sub_eq_add_neg, fourierPhase_add]

theorem fourierPhase_add_neg {d : ℕ} (ξ h : Ambient d) :
    fourierPhase ξ h + fourierPhase ξ (-h) =
      2 * (Real.cos (2 * Real.pi * inner ℝ ξ h) : ℂ) := by
  simp only [fourierPhase, inner_neg_right, mul_neg, Complex.ofReal_neg]
  rw [← Complex.two_cos, ← Complex.ofReal_cos]

theorem fourierPhase_second_difference {d : ℕ} (ξ x h : Ambient d) :
    symmetricSecondDifference (fourierPhase ξ) x h =
      (-2 * (1 - Real.cos (2 * Real.pi * inner ℝ ξ h)) : ℝ) • fourierPhase ξ x := by
  unfold symmetricSecondDifference
  rw [fourierPhase_add, fourierPhase_sub]
  have hs := fourierPhase_add_neg ξ h
  simp only [two_smul ℝ, Complex.real_smul]
  push_cast at hs ⊢
  linear_combination (fourierPhase ξ x) * hs

theorem schwartz_inverse_fourier_phase_integral {d : ℕ}
    (g : 𝓢(Ambient d, ℂ)) (x : Ambient d) :
    (𝓕⁻ g) x = ∫ ξ, fourierPhase ξ x * g ξ := by
  calc
    (𝓕⁻ g) x = 𝓕⁻ (g : Ambient d → ℂ) x := congrFun (fourierInv_coe g) x
    _ = ∫ ξ, fourierPhase ξ x * g ξ := by
      rw [Real.fourierInv_eq']
      rfl

theorem fourierPhase_test_integrable {d : ℕ} (g : 𝓢(Ambient d, ℂ)) (x : Ambient d) :
    Integrable (fun ξ => fourierPhase ξ x * g ξ) volume := by
  apply g.integrable.bdd_mul
  · apply Measurable.aestronglyMeasurable
    unfold fourierPhase
    fun_prop
  · exact Filter.Eventually.of_forall fun ξ => (fourierPhase_norm ξ x).le

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalSymbolBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounds for the fractional symbol

The cosine difference defining the fractional symbol is nonnegative and has quadratic
cancellation near the origin. Combining this local bound with inverse-power decay at
infinity gives integrability under upper growth bounds, in particular for volume.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter

theorem fractionalSymbolKernel_nonneg {d : ℕ} (m : ℕ) (ξ h : Ambient d) :
    0 ≤ fractionalSymbolKernel m ξ h :=
  mul_nonneg (inverseDistancePow_nonneg _ _ _) (sub_nonneg.mpr (Real.cos_le_one _))

theorem fractionalSymbolKernel_measurable {d : ℕ} (m : ℕ) (ξ : Ambient d) :
    Measurable (fractionalSymbolKernel m ξ) := by
  unfold fractionalSymbolKernel inverseDistancePow
  fun_prop

theorem one_sub_cos_inner_quadratic {d : ℕ} (ξ h : Ambient d) :
    1 - Real.cos (2 * Real.pi * inner ℝ ξ h) ≤
      (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖h‖ ^ 2 := by
  have hc : 1 - Real.cos (2 * Real.pi * inner ℝ ξ h) ≤
      (2 * Real.pi * inner ℝ ξ h) ^ 2 := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * inner ℝ ξ h),
      sq_nonneg (2 * Real.pi * inner ℝ ξ h)]
  have hi : (inner ℝ ξ h) ^ 2 ≤ ‖ξ‖ ^ 2 * ‖h‖ ^ 2 := by
    simpa only [sq_abs, mul_pow] using!
      (sq_le_sq₀ (abs_nonneg (inner ℝ ξ h))
        (mul_nonneg (norm_nonneg ξ) (norm_nonneg h))).mpr (abs_real_inner_le_norm ξ h)
  calc
    _ ≤ (2 * Real.pi * inner ℝ ξ h) ^ 2 := hc
    _ = (2 * Real.pi) ^ 2 * (inner ℝ ξ h) ^ 2 := mul_pow _ _ _
    _ ≤ (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖h‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hi (sq_nonneg _)
    _ = _ := by ring

theorem fractionalSymbolKernel_near_bound {d : ℕ} (p : ℕ) (ξ h : Ambient d) :
    ‖fractionalSymbolKernel (p + 1) ξ h‖ ≤
      ((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2) * inverseDistancePow p 0 h := by
  rw [Real.norm_of_nonneg (fractionalSymbolKernel_nonneg _ _ _)]
  by_cases hh : h = 0
  · subst h
    simp only [fractionalSymbolKernel, inner_zero_right, mul_zero, Real.cos_zero, sub_self]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (inverseDistancePow_nonneg _ _ _)
  · have hn : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr hh
    calc
      _ ≤ inverseDistancePow (p + 1 + 1) 0 h *
          ((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖h‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (one_sub_cos_inner_quadratic ξ h) (inverseDistancePow_nonneg _ _ _)
      _ = _ := by
        simp only [inverseDistancePow, dist_zero_left, pow_succ]
        field_simp

theorem fractionalSymbolKernel_far_bound {d : ℕ} (m : ℕ) (ξ h : Ambient d) :
    ‖fractionalSymbolKernel m ξ h‖ ≤ 2 * inverseDistancePow (m + 1) 0 h := by
  rw [Real.norm_of_nonneg (fractionalSymbolKernel_nonneg _ _ _)]
  have hc : 1 - Real.cos (2 * Real.pi * inner ℝ ξ h) ≤ 2 := by
    linarith [Real.neg_one_le_cos (2 * Real.pi * inner ℝ ξ h)]
  exact (mul_le_mul_of_nonneg_left hc (inverseDistancePow_nonneg _ _ _)).trans_eq (mul_comm _ _)

theorem fractionalSymbolKernel_integrable_of_growth {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth (p + 1) C μ) (ξ : Ambient d) :
    Integrable (fractionalSymbolKernel (p + 1) ξ) μ := by
  have hm : AEStronglyMeasurable (fractionalSymbolKernel (p + 1) ξ) μ :=
    (fractionalSymbolKernel_measurable (p + 1) ξ).aestronglyMeasurable
  have hnear : IntegrableOn (fractionalSymbolKernel (p + 1) ξ) (closedBall 0 1) μ := by
    have hi := (inverseDistancePow_near_integrable_and_bound p C μ hg 0 1 zero_lt_one).1
    exact (hi.const_mul ((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2)).mono' hm.restrict
      (Eventually.of_forall (fractionalSymbolKernel_near_bound p ξ))
  have hfar : IntegrableOn (fractionalSymbolKernel (p + 1) ξ) (closedExterior 0 1) μ := by
    have hi := (inverseDistancePow_closedExterior_integrable_and_bound (p + 1) C μ hg 0 1 zero_lt_one).1
    exact (hi.const_mul 2).mono' hm.restrict (Eventually.of_forall (fractionalSymbolKernel_far_bound (p + 1) ξ))
  have hs : closedBall (0 : Ambient d) 1 ∪ closedExterior 0 1 = univ := by
    ext h
    simp only [mem_union, mem_closedBall, dist_zero_right, closedExterior, mem_ofPred_eq,
      dist_zero_left, mem_univ, iff_true]
    exact le_total ‖h‖ 1
  have hi := hnear.union hfar
  rw [hs] at hi
  exact integrableOn_univ.mp hi

theorem fractionalSymbolKernel_integrable (p : ℕ) (ξ : Ambient (p + 1)) :
    Integrable (fractionalSymbolKernel (p + 1) ξ) volume :=
  fractionalSymbolKernel_integrable_of_growth p _ volume (volume_global_upper_growth (p + 1)) ξ

theorem fractionalSymbol_zero (p : ℕ) : fractionalSymbol p 0 = 0 := by
  simp [fractionalSymbol, fractionalSymbolKernel]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalSymbolInvariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric
open scoped RealInnerProductSpace

theorem fractionalSymbolKernel_isometry {d : ℕ} (m : ℕ)
    (U : Ambient d ≃ₗᵢ[ℝ] Ambient d) (ξ h : Ambient d) :
    fractionalSymbolKernel m (U ξ) (U h) = fractionalSymbolKernel m ξ h := by
  simp only [fractionalSymbolKernel, inverseDistancePow, dist_zero_left, U.norm_map, U.inner_map_map]

theorem fractionalSymbol_isometry (p : ℕ)
    (U : Ambient (p + 1) ≃ₗᵢ[ℝ] Ambient (p + 1)) (ξ : Ambient (p + 1)) :
    fractionalSymbol p (U ξ) = fractionalSymbol p ξ := by
  have h := U.measurePreserving.integral_comp U.toMeasurableEquiv.measurableEmbedding
    (fractionalSymbolKernel (p + 1) (U ξ))
  simpa only [fractionalSymbolKernel_isometry, fractionalSymbol] using! h.symm

theorem fractionalSymbolKernel_smul_pos {d : ℕ} (m : ℕ) (t : ℝ) (ht : 0 < t)
    (ξ h : Ambient d) :
    fractionalSymbolKernel m (t • ξ) h = t ^ (m + 1) * fractionalSymbolKernel m ξ (t • h) := by
  by_cases hh : h = 0
  · subst h
    simp [fractionalSymbolKernel, inverseDistancePow]
  · have hn : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr hh
    unfold fractionalSymbolKernel inverseDistancePow
    simp only [dist_zero_left, norm_smul, Real.norm_of_nonneg ht.le,
      real_inner_smul_left, real_inner_smul_right, mul_pow]
    field_simp

theorem fractionalSymbol_smul_pos (p : ℕ) (t : ℝ) (ht : 0 < t) (ξ : Ambient (p + 1)) :
    fractionalSymbol p (t • ξ) = t * fractionalSymbol p ξ := by
  have heq : fractionalSymbolKernel (p + 1) (t • ξ) = fun h =>
      t ^ (p + 1 + 1) * fractionalSymbolKernel (p + 1) ξ (t • h) :=
    funext (fractionalSymbolKernel_smul_pos (p + 1) t ht ξ)
  unfold fractionalSymbol
  rw [heq, integral_const_mul,
    Measure.integral_comp_smul_of_nonneg (volume : Measure (Ambient (p + 1)))
      (fractionalSymbolKernel (p + 1) ξ) t (hR := ht.le)]
  simp only [Ambient, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, pow_succ]
  field_simp

theorem fractionalSymbol_smul_nonneg (p : ℕ) (t : ℝ) (ht : 0 ≤ t) (ξ : Ambient (p + 1)) :
    fractionalSymbol p (t • ξ) = t * fractionalSymbol p ξ := by
  rcases ht.eq_or_lt with h | h
  · subst t
    rw [zero_smul, fractionalSymbol_zero, zero_mul]
  · exact fractionalSymbol_smul_pos p t h ξ

theorem fractionalSymbol_eq_unit_mul_norm (p : ℕ) (v : Ambient (p + 1)) (hv : ‖v‖ = 1)
    (ξ : Ambient (p + 1)) : fractionalSymbol p ξ = fractionalSymbol p v * ‖ξ‖ := by
  let U : Ambient (p + 1) ≃ₗᵢ[ℝ] Ambient (p + 1) :=
    Submodule.reflection (ℝ ∙ (ξ - ‖ξ‖ • v))ᗮ
  have hn : ‖ξ‖ = ‖‖ξ‖ • v‖ := by
    rw [norm_smul, Real.norm_of_nonneg (norm_nonneg ξ), hv, mul_one]
  have hU : U ξ = ‖ξ‖ • v := Submodule.reflection_sub hn
  calc
    _ = fractionalSymbol p (U ξ) := (fractionalSymbol_isometry p U ξ).symm
    _ = fractionalSymbol p (‖ξ‖ • v) := congrArg (fractionalSymbol p) hU
    _ = ‖ξ‖ * fractionalSymbol p v := fractionalSymbol_smul_nonneg p ‖ξ‖ (norm_nonneg ξ) v
    _ = _ := mul_comm _ _

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalSymbolPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Function Topology

theorem fractionalSymbolKernel_continuousAt {d : ℕ} (m : ℕ) (ξ h : Ambient d) (hh : h ≠ 0) :
    ContinuousAt (fractionalSymbolKernel m ξ) h := by
  unfold fractionalSymbolKernel inverseDistancePow
  have hd : ContinuousAt (fun y : Ambient d => dist 0 y) h := continuousAt_const.dist continuousAt_id
  apply ((hd.pow (m + 1)).inv₀ (pow_ne_zero _ (dist_ne_zero.mpr (Ne.symm hh)))).mul
  fun_prop

theorem fractionalSymbolKernel_exists_positive {d : ℕ} (m : ℕ) (ξ : Ambient d) (hξ : ξ ≠ 0) :
    ∃ h : Ambient d, h ≠ 0 ∧ 0 < fractionalSymbolKernel m ξ h := by
  let h : Ambient d := ((2 * ‖ξ‖ ^ 2)⁻¹ : ℝ) • ξ
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  have hi : inner ℝ ξ h = 1 / 2 := by
    dsimp [h]
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hh : h ≠ 0 := by
    intro hz
    rw [hz, inner_zero_right] at hi
    norm_num at hi
  have hp : 2 * Real.pi * inner ℝ ξ h = Real.pi := by rw [hi]; ring
  refine ⟨h, hh, ?_⟩
  unfold fractionalSymbolKernel
  rw [hp, Real.cos_pi]
  have hk : 0 < inverseDistancePow (m + 1) 0 h := by
    unfold inverseDistancePow
    exact inv_pos.mpr (pow_pos (dist_pos.mpr (Ne.symm hh)) _)
  exact mul_pos hk (by norm_num)

theorem fractionalSymbol_pos (p : ℕ) (ξ : Ambient (p + 1)) (hξ : ξ ≠ 0) :
    0 < fractionalSymbol p ξ := by
  obtain ⟨h, hh, hp⟩ := fractionalSymbolKernel_exists_positive (p + 1) ξ hξ
  have hn : {y : Ambient (p + 1) | 0 < fractionalSymbolKernel (p + 1) ξ y} ∈ 𝓝 h :=
    (fractionalSymbolKernel_continuousAt (p + 1) ξ h hh).eventually (lt_mem_nhds hp)
  have hs : 0 < (volume : Measure (Ambient (p + 1))) (support (fractionalSymbolKernel (p + 1) ξ)) :=
    ((volume : Measure (Ambient (p + 1))).measure_pos_of_mem_nhds hn).trans_le
      (measure_mono fun y hy => ne_of_gt hy)
  exact (integral_pos_iff_support_of_nonneg (fractionalSymbolKernel_nonneg (p + 1) ξ)
    (fractionalSymbolKernel_integrable p ξ)).mpr hs

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalRadialSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

theorem fractionalSymbol_eq_positive_constant_mul_norm (p : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ ξ : Ambient (p + 1), fractionalSymbol p ξ = c * ‖ξ‖ := by
  obtain ⟨v, hv⟩ := exists_norm_eq (E := Ambient (p + 1)) (show (0 : ℝ) ≤ 1 from zero_le_one)
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv
    norm_num at hv
  exact ⟨fractionalSymbol p v, fractionalSymbol_pos p v hv0,
    fractionalSymbol_eq_unit_mul_norm p v hv⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalFourierFubini
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Filter Function

theorem fractionalFourierKernel_norm (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) (q : Ambient (p + 1) × Ambient (p + 1)) :
    ‖fractionalFourierKernel p g x q‖ = fractionalSymbolKernel (p + 1) q.1 q.2 * ‖g q.1‖ := by
  unfold fractionalFourierKernel
  rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal,
    abs_of_nonneg (fractionalSymbolKernel_nonneg _ _ _),
    norm_mul, fourierPhase_norm, one_mul]

theorem fractionalFourierKernel_measurable (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) : Measurable (fractionalFourierKernel p g x) := by
  unfold fractionalFourierKernel fractionalSymbolKernel inverseDistancePow fourierPhase
  simp_rw [Complex.real_smul]
  fun_prop

theorem fractionalFourierKernel_integrable (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) :
    Integrable (fractionalFourierKernel p g x)
      ((volume : Measure (Ambient (p + 1))).prod volume) := by
  obtain ⟨c, _, hc⟩ := fractionalSymbol_eq_positive_constant_mul_norm p
  apply (integrable_prod_iff (fractionalFourierKernel_measurable p g x).aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall fun ξ =>
      (fractionalSymbolKernel_integrable p ξ).smul_const (fourierPhase ξ x * g ξ)
  · have heq : (fun ξ => ∫ h, ‖fractionalFourierKernel p g x (ξ, h)‖) =
        fun ξ => c * (‖ξ‖ * ‖g ξ‖) := by
      funext ξ
      simp_rw [fractionalFourierKernel_norm]
      rw [integral_mul_const]
      change fractionalSymbol p ξ * ‖g ξ‖ = _
      rw [hc ξ, mul_assoc]
    rw [heq]
    exact (schwartz_first_absolute_moment_integrable g).const_mul c

theorem fractionalFourierKernel_integral_section (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (x ξ : Ambient (p + 1)) :
    (∫ h, fractionalFourierKernel p g x (ξ, h)) =
      fractionalSymbol p ξ • (fourierPhase ξ x * g ξ) :=
  integral_smul_const (fractionalSymbolKernel (p + 1) ξ) (fourierPhase ξ x * g ξ)

theorem fractionalFourierKernel_integral_swap (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) :
    (∫ h, ∫ ξ, fractionalFourierKernel p g x (ξ, h)) =
      ∫ ξ, fractionalSymbol p ξ • (fourierPhase ξ x * g ξ) := by
  have hi := fractionalFourierKernel_integrable p g x
  calc
    _ = ∫ q, fractionalFourierKernel p g x q ∂(volume : Measure (Ambient (p + 1))).prod volume :=
      (integral_prod_symm (fractionalFourierKernel p g x) hi).symm
    _ = ∫ ξ, ∫ h, fractionalFourierKernel p g x (ξ, h) := integral_prod _ hi
    _ = _ := integral_congr_ae (Eventually.of_forall (fractionalFourierKernel_integral_section p g x))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalFourierMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Filter
open scoped FourierTransform

theorem schwartz_inverse_fourier_second_difference {d : ℕ}
    (g : 𝓢(Ambient d, ℂ)) (x h : Ambient d) :
    symmetricSecondDifference (𝓕⁻ g : 𝓢(Ambient d, ℂ)) x h =
      ∫ ξ, (-2 * (1 - Real.cos (2 * Real.pi * inner ℝ ξ h)) : ℝ) •
        (fourierPhase ξ x * g ξ) := by
  have hp := fourierPhase_test_integrable g (x + h)
  have hm := fourierPhase_test_integrable g (x - h)
  have hx := fourierPhase_test_integrable g x
  have hi : (∫ ξ, fourierPhase ξ (x + h) * g ξ + fourierPhase ξ (x - h) * g ξ -
      (2 : ℂ) * (fourierPhase ξ x * g ξ)) =
      (∫ ξ, fourierPhase ξ (x + h) * g ξ) + (∫ ξ, fourierPhase ξ (x - h) * g ξ) -
        (2 : ℂ) * (∫ ξ, fourierPhase ξ x * g ξ) := by
    calc
      _ = (∫ ξ, fourierPhase ξ (x + h) * g ξ + fourierPhase ξ (x - h) * g ξ) -
          ∫ ξ, (2 : ℂ) * (fourierPhase ξ x * g ξ) :=
        integral_sub (hp.add hm) (hx.const_mul (2 : ℂ))
      _ = _ := by
        erw [integral_add hp hm, integral_const_mul]
  unfold symmetricSecondDifference
  rw [schwartz_inverse_fourier_phase_integral, schwartz_inverse_fourier_phase_integral,
    schwartz_inverse_fourier_phase_integral]
  change ((∫ ξ, fourierPhase ξ (x + h) * g ξ) + (∫ ξ, fourierPhase ξ (x - h) * g ξ) -
    (2 : ℝ) • (∫ ξ, fourierPhase ξ x * g ξ)) = _
  erw [Complex.real_smul]
  norm_num only [Complex.ofReal_ofNat]
  erw [← hi]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro ξ
  calc
    _ = symmetricSecondDifference (fourierPhase ξ) x h * g ξ := by
      unfold symmetricSecondDifference
      erw [two_smul ℝ]
      ring
    _ = _ := by
      rw [fourierPhase_second_difference]
      simp only [Complex.real_smul]
      ring

theorem schwartz_inverse_fourier_fractional_kernel (p : ℕ)
    (g : 𝓢(Ambient (p + 1), ℂ)) (x h : Ambient (p + 1)) :
    fractionalSchwartzKernel (p + 1) (𝓕⁻ g : 𝓢(Ambient (p + 1), ℂ)) x h =
      (-2 : ℝ) • (∫ ξ, fractionalFourierKernel p g x (ξ, h)) := by
  unfold fractionalSchwartzKernel
  rw [schwartz_inverse_fourier_second_difference]
  erw [Complex.real_smul]
  simp +instances only [Complex.real_smul]
  erw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro ξ
  unfold fractionalFourierKernel fractionalSymbolKernel
  simp only [Complex.real_smul]
  push_cast
  ring

theorem fractionalSchwartz_inverse_fourier_multiplier (p : ℕ)
    (g : 𝓢(Ambient (p + 1), ℂ)) (x : Ambient (p + 1)) :
    fractionalSchwartzTest p (𝓕⁻ g) x =
      ∫ ξ, fractionalSymbol p ξ • (fourierPhase ξ x * g ξ) := by
  unfold fractionalSchwartzTest
  simp_rw [schwartz_inverse_fourier_fractional_kernel]
  simp +instances only [Complex.real_smul]
  erw [integral_const_mul, ← mul_assoc]
  norm_num
  exact fractionalFourierKernel_integral_swap p g x

theorem fractionalSchwartz_positive_norm_multiplier (p : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ g : 𝓢(Ambient (p + 1), ℂ), ∀ x : Ambient (p + 1),
      fractionalSchwartzTest p (𝓕⁻ g) x =
        ∫ ξ, (c * ‖ξ‖ : ℝ) • (fourierPhase ξ x * g ξ) := by
  obtain ⟨c, hc, hs⟩ := fractionalSymbol_eq_positive_constant_mul_norm p
  refine ⟨c, hc, fun g x => ?_⟩
  rw [fractionalSchwartz_inverse_fourier_multiplier]
  exact integral_congr_ae (Eventually.of_forall fun ξ => by
    dsimp only
    rw [hs ξ])

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalFourierAnnihilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Filter
open scoped FourierTransform

theorem fractionalSchwartz_norm_division_identity (p : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ g : 𝓢(Ambient (p + 1), ℂ),
      ∀ hc : HasCompactSupport g, ∀ hz : (0 : Ambient (p + 1)) ∉ tsupport g,
      ∀ x : Ambient (p + 1),
      fractionalSchwartzTest p (𝓕⁻ (schwartzNormDivision g hc hz)) x = c • (𝓕⁻ g) x := by
  obtain ⟨c, hc, hm⟩ := fractionalSchwartz_positive_norm_multiplier p
  refine ⟨c, hc, fun g hgc hgz x => ?_⟩
  rw [hm, schwartz_inverse_fourier_phase_integral]
  erw [← integral_smul c]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro ξ
  dsimp only
  calc
    _ = c • (‖ξ‖ • (fourierPhase ξ x * schwartzNormDivision g hgc hgz ξ)) :=
      mul_smul c ‖ξ‖ (fourierPhase ξ x * schwartzNormDivision g hgc hgz ξ)
    _ = c • (fourierPhase ξ x * (‖ξ‖ • schwartzNormDivision g hgc hgz ξ)) :=
      congrArg (fun z : ℂ => c • z)
        (Algebra.mul_smul_comm ‖ξ‖ (fourierPhase ξ x) (schwartzNormDivision g hgc hgz ξ)).symm
    _ = _ := by
      rw [schwartzNormDivision_norm_mul]

theorem height_inverse_fourier_zero_of_fractional_equation (p : ℕ)
    (w : Ambient (p + 1) → ℝ)
    (heq : ∀ g : 𝓢(Ambient (p + 1), ℂ), (∫ x, g x) = 0 →
      (∫ x, w x • fractionalSchwartzTest p g x) = 0)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hc : HasCompactSupport g)
    (hz : (0 : Ambient (p + 1)) ∉ tsupport g) :
    (∫ x, w x • (𝓕⁻ g) x) = 0 := by
  obtain ⟨c, hcp, hm⟩ := fractionalSchwartz_norm_division_identity p
  have h := heq (𝓕⁻ (schwartzNormDivision g hc hz))
    (schwartzNormDivision_inverse_mean_zero g hc hz)
  have hscalar : c • (∫ x, w x • (𝓕⁻ g) x) = (0 : ℂ) := by
    calc
      _ = ∫ x, c • (w x • (𝓕⁻ g) x) := (integral_smul c _).symm
      _ = ∫ x, w x • fractionalSchwartzTest p (𝓕⁻ (schwartzNormDivision g hc hz)) x := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro x
        dsimp only
        rw [hm g hc hz x]
        exact smul_comm c (w x) ((𝓕⁻ g) x)
      _ = 0 := h
  exact (smul_eq_zero.mp hscalar).resolve_left hcp.ne'

theorem represented_height_inverse_fourier_annihilates_away_zero (p : ℕ)
    (w : Ambient (p + 1) → ℝ) (T : 𝓢'(Ambient (p + 1), ℂ))
    (hT : ∀ g : 𝓢(Ambient (p + 1), ℂ), T g = ∫ x, w x • g x)
    (heq : ∀ g : 𝓢(Ambient (p + 1), ℂ), (∫ x, g x) = 0 →
      (∫ x, w x • fractionalSchwartzTest p g x) = 0)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hc : HasCompactSupport g)
    (hz : (0 : Ambient (p + 1)) ∉ tsupport g) :
    (𝓕⁻ T : 𝓢'(Ambient (p + 1), ℂ)) g = 0 := by
  rw [TemperedDistribution.fourierInv_apply, hT]
  exact height_inverse_fourier_zero_of_fractional_equation p w heq g hc hz

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_TemperedFiniteOrderBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory

theorem tempered_distribution_finite_seminorm_bound {d : ℕ}
    (T : 𝓢'(Ambient d, ℂ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ g : 𝓢(Ambient d, ℂ),
        ‖T g‖ ≤ C * s.sup (schwartzSeminormFamily ℂ (Ambient d) ℂ) g := by
  let q : Seminorm ℂ 𝓢(Ambient d, ℂ) := (normSeminorm ℂ ℂ).comp T.toLinearMap
  have hq : Continuous q := continuous_norm.comp T.continuous
  obtain ⟨s, C, hC, hbound⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℂ (Ambient d) ℂ) q hq
  refine ⟨s, C, by exact_mod_cast (pos_iff_ne_zero.mpr hC), fun g => ?_⟩
  exact hbound g

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_TemperedRealFiniteOrderBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap

theorem tempered_distribution_finite_real_seminorm_bound {d : ℕ}
    (T : 𝓢'(Ambient d, ℂ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ g : 𝓢(Ambient d, ℂ),
        ‖T g‖ ≤ C * s.sup (schwartzSeminormFamily ℝ (Ambient d) ℂ) g := by
  obtain ⟨s, C, hC, hbound⟩ := tempered_distribution_finite_seminorm_bound T
  refine ⟨s, C, hC, fun g => ?_⟩
  have heq : s.sup (schwartzSeminormFamily ℂ (Ambient d) ℂ) g =
      s.sup (schwartzSeminormFamily ℝ (Ambient d) ℂ) g := by
    simp only [Seminorm.finset_sup_apply]
    rfl
  exact (hbound g).trans_eq (congrArg (fun t : ℝ => C * t) heq)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_PointSupportedFiniteJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite jets of point-supported distributions

A finite Schwartz seminorm bound and shrinking localization show that a tempered distribution
supported at the origin annihilates tests whose derivatives vanish there through a fixed order.
Consequently it depends only on a finite jet. The final theorem applies this conclusion to the
inverse Fourier transform of a represented height distribution satisfying the fractional equation.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap Filter Topology
open scoped FourierTransform

theorem point_supported_distribution_kills_zero_jets {d : ℕ}
    (T : 𝓢'(Ambient d, ℂ))
    (hT : ∀ g : 𝓢(Ambient d, ℂ), HasCompactSupport g →
      (0 : Ambient d) ∉ tsupport g → T g = 0) :
    ∃ N : ℕ, ∀ g : 𝓢(Ambient d, ℂ),
      (∀ i, i ≤ N → iteratedFDeriv ℝ i g 0 = 0) → T g = 0 := by
  classical
  obtain ⟨s, C, hC, hbound⟩ := tempered_distribution_finite_real_seminorm_bound T
  let N : ℕ := s.sup Prod.snd
  refine ⟨N, fun g hz => ?_⟩
  let G : ℕ → 𝓢(Ambient d, ℂ) := shrinkingSchwartzCutoff g
  have hTG : ∀ j, T (G j) = T g := fun j =>
    tempered_distribution_eq_of_germ_at_zero T hT (G j) g (shrinkingSchwartzCutoff_germ g j)
  have hlim : ∀ i ∈ s, Tendsto
      (fun j => schwartzSeminormFamily ℝ (Ambient d) ℂ i (G j)) atTop (𝓝 0) := by
    intro i hi
    have hn : i.2 ≤ N := Finset.le_sup hi
    exact shrinkingSchwartzCutoff_seminorm_tendsto g i.1 i.2
      (fun k hk => hz k (hk.trans hn))
  have hsum : Tendsto (fun j => C * ∑ i ∈ s,
      schwartzSeminormFamily ℝ (Ambient d) ℂ i (G j)) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero, mul_zero] using!
      (tendsto_finsetSum s hlim).const_mul C
  have hle : ∀ j, ‖T g‖ ≤ C * ∑ i ∈ s,
      schwartzSeminormFamily ℝ (Ambient d) ℂ i (G j) := by
    intro j
    rw [← hTG j]
    apply (hbound (G j)).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    have hs := Seminorm.finset_sup_le_sum (schwartzSeminormFamily ℝ (Ambient d) ℂ) s (G j)
    simpa only [← FunLike.coeAddMonoidHom_apply, map_sum, Finset.sum_apply] using! hs
  have hzero : ‖T g‖ ≤ 0 := ge_of_tendsto hsum (Eventually.of_forall hle)
  exact norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _))

theorem point_supported_distribution_finite_jet {d : ℕ}
    (T : 𝓢'(Ambient d, ℂ))
    (hT : ∀ g : 𝓢(Ambient d, ℂ), HasCompactSupport g →
      (0 : Ambient d) ∉ tsupport g → T g = 0) :
    ∃ N : ℕ, ∀ g h : 𝓢(Ambient d, ℂ),
      (∀ i, i ≤ N → iteratedFDeriv ℝ i g 0 = iteratedFDeriv ℝ i h 0) → T g = T h := by
  obtain ⟨N, hN⟩ := point_supported_distribution_kills_zero_jets T hT
  refine ⟨N, fun g h heq => ?_⟩
  have hz : ∀ i, i ≤ N → iteratedFDeriv ℝ i (g - h) 0 = 0 := by
    intro i hi
    change iteratedFDeriv ℝ i ((g : Ambient d → ℂ) - (h : Ambient d → ℂ)) 0 = 0
    rw [iteratedFDeriv_sub_apply (g.contDiffAt i) (h.contDiffAt i), heq i hi, sub_self]
  have hh := hN (g - h) hz
  rw [map_sub, sub_eq_zero] at hh
  exact hh

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_PointSupportedJetRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap
open scoped FourierTransform

theorem point_supported_distribution_jet_representation {d : ℕ}
    (T : 𝓢'(Ambient d, ℂ))
    (hT : ∀ g : 𝓢(Ambient d, ℂ), HasCompactSupport g →
      (0 : Ambient d) ∉ tsupport g → T g = 0) :
    ∃ N : ℕ, ∃ c : JetCoordinateIndex d N → ℂ, ∀ g : 𝓢(Ambient d, ℂ),
      T g = ∑ i, c i * iteratedFDeriv ℝ i.1.val g 0
        (fun j => EuclideanSpace.basisFun (Fin d) ℝ (i.2 j)) := by
  classical
  obtain ⟨N, hN⟩ := point_supported_distribution_finite_jet T hT
  have hker : ∀ g, schwartzJetCoordinates d N g = 0 → T g = 0 := by
    intro g hg
    have heq : schwartzJetCoordinates d N g = schwartzJetCoordinates d N 0 :=
      hg.trans (map_zero _).symm
    have hh := hN g 0 ((schwartzJetCoordinates_eq_iff d N g 0).mp heq)
    simpa only [map_zero] using! hh
  obtain ⟨c, hc⟩ := linear_functional_finite_coordinate_representation
    (schwartzJetCoordinates d N) T.toLinearMap hker
  refine ⟨N, c, fun g => ?_⟩
  simpa only [schwartzJetCoordinates_apply] using! hc g

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_PointFourierPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap
open scoped FourierTransform

theorem point_supported_inverse_fourier_polynomial {d : ℕ}
    (T : 𝓢'(Ambient d, ℂ))
    (hT : ∀ g : 𝓢(Ambient d, ℂ), HasCompactSupport g →
      (0 : Ambient d) ∉ tsupport g → (𝓕⁻ T : 𝓢'(Ambient d, ℂ)) g = 0) :
    ∃ P : MvPolynomial (Fin d) ℂ, ∀ g : 𝓢(Ambient d, ℂ),
      T g = ∫ x, MvPolynomial.eval (fun j => (x j : ℂ)) P * g x := by
  obtain ⟨N, c, hc⟩ := point_supported_distribution_jet_representation (𝓕⁻ T) hT
  refine ⟨jetMomentPolynomial c, fun g => ?_⟩
  have h := hc (𝓕 g)
  rw [TemperedDistribution.fourierInv_apply, FourierTransform.fourierInv_fourier_eq] at h
  exact h.trans (fourier_jet_sum_eq_polynomial_pairing c g)

theorem represented_fractional_height_polynomial_pairing (p : ℕ)
    (w : Ambient (p + 1) → ℝ) (T : 𝓢'(Ambient (p + 1), ℂ))
    (hT : ∀ g : 𝓢(Ambient (p + 1), ℂ), T g = ∫ x, w x • g x)
    (heq : ∀ g : 𝓢(Ambient (p + 1), ℂ), (∫ x, g x) = 0 →
      (∫ x, w x • fractionalSchwartzTest p g x) = 0) :
    ∃ P : MvPolynomial (Fin (p + 1)) ℂ, ∀ g : 𝓢(Ambient (p + 1), ℂ),
      (∫ x, w x • g x) = ∫ x, MvPolynomial.eval (fun j => (x j : ℂ)) P * g x := by
  obtain ⟨P, hP⟩ := point_supported_inverse_fourier_polynomial T
    (fun g hc hz => represented_height_inverse_fourier_annihilates_away_zero p w T hT heq g hc hz)
  exact ⟨P, fun g => (hT g).symm.trans (hP g)⟩

theorem represented_fractional_height_ae_polynomial (p : ℕ)
    (w : Ambient (p + 1) → ℝ) (hw : MeasureTheory.LocallyIntegrable w)
    (T : 𝓢'(Ambient (p + 1), ℂ))
    (hT : ∀ g : 𝓢(Ambient (p + 1), ℂ), T g = ∫ x, w x • g x)
    (heq : ∀ g : 𝓢(Ambient (p + 1), ℂ), (∫ x, g x) = 0 →
      (∫ x, w x • fractionalSchwartzTest p g x) = 0) :
    ∃ P : MvPolynomial (Fin (p + 1)) ℂ,
      ∀ᵐ x, (w x : ℂ) = MvPolynomial.eval (fun j => (x j : ℂ)) P := by
  obtain ⟨P, hP⟩ := represented_fractional_height_polynomial_pairing p w T hT heq
  exact ⟨P, real_height_ae_eq_polynomial_of_pairings w hw P hP⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CommonHeightPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Function
open scoped NNReal

theorem polynomial_inherits_height_tail {d : ℕ} (q : ℕ)
    (w : Ambient d → ℝ) (P : MvPolynomial (Fin d) ℂ)
    (hP : ∀ᵐ x, (w x : ℂ) = MvPolynomial.eval (fun j => (x j : ℂ)) P)
    (R : ℝ)
    (hi : IntegrableOn (fun x => |w x| * inverseDistancePow q 0 x)
      (closedExterior 0 R)) :
    IntegrableOn (fun x => ‖MvPolynomial.eval (fun j => (x j : ℂ)) P‖ *
      inverseDistancePow q 0 x) (closedExterior 0 R) := by
  apply hi.congr
  filter_upwards [ae_restrict_of_ae hP] with x hx
  rw [← hx, Complex.norm_real, Real.norm_eq_abs]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ExteriorDilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set
open scoped Pointwise

theorem smul_closedExterior_unit {d : ℕ} (r : ℝ) (hr : 0 < r) :
    r • closedExterior (0 : Ambient d) 1 = closedExterior 0 r := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change r ≤ dist (0 : Ambient d) (r • y)
    change 1 ≤ dist (0 : Ambient d) y at hy
    simp only [dist_zero_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr] at *
    nlinarith
  · intro hx
    refine ⟨r⁻¹ • x, ?_, ?_⟩
    · change 1 ≤ dist (0 : Ambient d) (r⁻¹ • x)
      change r ≤ dist (0 : Ambient d) x at hx
      rw [dist_zero_left, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      rw [dist_zero_left] at hx
      exact (le_inv_mul_iff₀ hr).2 (by simpa using! hx)
    · change r • (r⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

theorem inverseDistancePow_origin_smul {d : ℕ} (q : ℕ)
    (r : ℝ) (hr : 0 < r) (x : Ambient d) :
    inverseDistancePow q 0 (r • x) = (r ^ q)⁻¹ * inverseDistancePow q 0 x := by
  simp only [inverseDistancePow, dist_zero_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos hr, mul_pow, mul_inv]

theorem exterior_weighted_normalized_dilation_integral {d : ℕ} (q k : ℕ)
    (f : Ambient d → ℂ) (r : ℝ) (hr : 0 < r) :
    (∫ x in closedExterior (0 : Ambient d) 1,
      ‖((r : ℂ) ^ k)⁻¹ * f (r • x)‖ * inverseDistancePow q 0 x) =
      (r ^ q * (r ^ k)⁻¹ * (r ^ d)⁻¹) *
        ∫ x in closedExterior (0 : Ambient d) r, ‖f x‖ * inverseDistancePow q 0 x := by
  have hpoint (x : Ambient d) :
      ‖((r : ℂ) ^ k)⁻¹ * f (r • x)‖ * inverseDistancePow q 0 x =
      (r ^ q * (r ^ k)⁻¹) * (‖f (r • x)‖ * inverseDistancePow q 0 (r • x)) := by
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      inverseDistancePow_origin_smul q r hr]
    have hz : r ^ q ≠ 0 := pow_ne_zero _ hr.ne'
    field_simp
  calc
    _ = ∫ x in closedExterior (0 : Ambient d) 1,
        (r ^ q * (r ^ k)⁻¹) * (‖f (r • x)‖ * inverseDistancePow q 0 (r • x)) :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = (r ^ q * (r ^ k)⁻¹) * ∫ x in closedExterior (0 : Ambient d) 1,
        (‖f (r • x)‖ * inverseDistancePow q 0 (r • x)) := integral_const_mul _ _
    _ = _ := by
      rw [Measure.setIntegral_comp_smul volume (fun x => ‖f x‖ * inverseDistancePow q 0 x)
        (closedExterior (0 : Ambient d) 1) hr.ne', smul_closedExterior_unit r hr,
        finrank_euclideanSpace_fin, abs_of_pos (inv_pos.mpr (pow_pos hr d)), smul_eq_mul]
      ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ExteriorDilationIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integrability under dilation of exterior regions

Positive dilation identifies the unit closed exterior with the closed exterior
at the dilation radius. This change of variables transports integrability of
functions on exterior regions to their rescaled compositions.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

theorem preimage_closedExterior_dilation {d : ℕ} (r : ℝ) (hr : 0 < r) :
    (fun x : Ambient d => r • x) ⁻¹' closedExterior 0 r = closedExterior 0 1 := by
  ext x
  simp only [mem_preimage, closedExterior, mem_ofPred_eq, dist_zero_left,
    norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  constructor <;> intro h <;> nlinarith

theorem integrableOn_closedExterior_comp_smul {d : ℕ}
    (f : Ambient d → ℝ) (r : ℝ) (hr : 0 < r)
    (hi : IntegrableOn f (closedExterior 0 r)) :
    IntegrableOn (fun x => f (r • x)) (closedExterior (0 : Ambient d) 1) := by
  have hh := (hi.integrable_indicator (closedExterior_measurable 0 r)).comp_smul hr.ne'
  apply (integrable_indicator_iff (closedExterior_measurable (0 : Ambient d) 1)).mp
  apply hh.congr
  filter_upwards with x
  have hx : r • x ∈ closedExterior 0 r ↔ x ∈ closedExterior 0 1 := by
    change x ∈ (fun x : Ambient d => r • x) ⁻¹' closedExterior 0 r ↔ _
    rw [preimage_closedExterior_dilation r hr]
  by_cases hs : x ∈ closedExterior (0 : Ambient d) 1
  · rw [Set.indicator_of_mem (hx.mpr hs), Set.indicator_of_mem hs]
  · rw [Set.indicator_of_notMem (fun h => hs (hx.mp h)), Set.indicator_of_notMem hs]

theorem exterior_weighted_normalized_dilation_integrable {d : ℕ} (q k : ℕ)
    (f : Ambient d → ℂ) (r : ℝ) (hr : 0 < r)
    (hi : IntegrableOn (fun x => ‖f x‖ * inverseDistancePow q 0 x) (closedExterior 0 r)) :
    IntegrableOn (fun x => ‖((r : ℂ) ^ k)⁻¹ * f (r • x)‖ * inverseDistancePow q 0 x)
      (closedExterior (0 : Ambient d) 1) := by
  have hh := (integrableOn_closedExterior_comp_smul
    (fun x => ‖f x‖ * inverseDistancePow q 0 x) r hr hi).const_mul (r ^ q * (r ^ k)⁻¹)
  apply hh.congr
  filter_upwards with x
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    inverseDistancePow_origin_smul q r hr]
  have hz : r ^ q ≠ 0 := pow_ne_zero _ hr.ne'
  field_simp

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_PolynomialHomogeneousScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

theorem homogeneous_polynomial_eval_mul {σ : Type*} (P : MvPolynomial σ ℂ)
    (n : ℕ) (hP : P.IsHomogeneous n) (r : ℂ) (x : σ → ℂ) :
    MvPolynomial.eval (fun i => r * x i) P = r ^ n * MvPolynomial.eval x P := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hd := hP (MvPolynomial.mem_support_iff.mp hs)
  simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum] at hd
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem homogeneous_polynomial_eval_real_smul {d n : ℕ}
    (P : MvPolynomial (Fin d) ℂ) (hP : P.IsHomogeneous n) (r : ℝ) (x : Ambient d) :
    MvPolynomial.eval (fun j => ((r • x) j : ℂ)) P =
      (r : ℂ) ^ n * MvPolynomial.eval (fun j => (x j : ℂ)) P := by
  have hc : (fun j => ((r • x) j : ℂ)) = (fun j => (r : ℂ) * (x j : ℂ)) := by
    funext j
    change ((r * x j : ℝ) : ℂ) = (r : ℂ) * (x j : ℂ)
    exact Complex.ofReal_mul _ _
  rw [hc]
  exact homogeneous_polynomial_eval_mul P n hP (r : ℂ) (fun j => (x j : ℂ))

theorem polynomial_scaled_eval_homogeneous_sum {d : ℕ}
    (P : MvPolynomial (Fin d) ℂ) (r : ℝ) (x : Ambient d) :
    MvPolynomial.eval (fun j => ((r • x) j : ℂ)) P =
      ∑ n ∈ Finset.range (P.totalDegree + 1), (r : ℂ) ^ n *
        MvPolynomial.eval (fun j => (x j : ℂ)) (MvPolynomial.homogeneousComponent n P) := by
  conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent P]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  exact homogeneous_polynomial_eval_real_smul _
    (MvPolynomial.homogeneousComponent_isHomogeneous n P) r x

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_HomogeneousExteriorVanishing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

theorem homogeneous_polynomial_eval_zero_of_ae_exterior {d n : ℕ}
    (P : MvPolynomial (Fin d) ℂ) (hP : P.IsHomogeneous n) (hn : n ≠ 0)
    (hae : ∀ᵐ x ∂volume.restrict (closedExterior (0 : Ambient d) 1),
      MvPolynomial.eval (fun j => (x j : ℂ)) P = 0) :
    ∀ x : Ambient d, MvPolynomial.eval (fun j => (x j : ℂ)) P = 0 := by
  let U : Set (Ambient d) := {x | 1 < ‖x‖}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hsub : U ⊆ closedExterior 0 1 := by
    intro x hx
    change 1 ≤ dist (0 : Ambient d) x
    rw [dist_zero_left]
    exact hx.le
  have hUae : (fun x : Ambient d => MvPolynomial.eval (fun j => (x j : ℂ)) P) =ᵐ[volume.restrict U]
      (fun _ => (0 : ℂ)) := ae_restrict_of_ae_restrict_of_subset hsub hae
  have hzero := Measure.eqOn_open_of_ae_eq hUae hU
    (mvPolynomial_complex_eval_continuous P).continuousOn continuous_const.continuousOn
  intro x
  by_cases hx : x = 0
  · subst x
    have h := homogeneous_polynomial_eval_real_smul P hP (0 : ℝ) (0 : Ambient d)
    simpa only [zero_smul, Complex.ofReal_zero, zero_pow hn, zero_mul] using! h
  · have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let r : ℝ := 2 / ‖x‖
    have hr : 0 < r := div_pos (by norm_num) hnx
    have hrx : r • x ∈ U := by
      change 1 < ‖r • x‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      dsimp only [r]
      rw [div_mul_cancel₀ _ hnx.ne']
      norm_num
    have h := hzero hrx
    dsimp only at h
    rw [homogeneous_polynomial_eval_real_smul P hP r x] at h
    exact (mul_eq_zero.mp h).resolve_left
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr.ne'))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_PolynomialDegreeDrop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing the top homogeneous component

The homogeneous decomposition expresses the remainder after subtracting a polynomial's
top component as a sum of strictly lower components. If the original total degree is
positive, the finite-sum degree bound makes this a strict degree reduction.
-/

namespace RieszRectifiability

noncomputable section

theorem polynomial_sub_top_eq_lower_sum {σ : Type*} (P : MvPolynomial σ ℂ) :
    P - MvPolynomial.homogeneousComponent P.totalDegree P =
      ∑ n ∈ Finset.range P.totalDegree, MvPolynomial.homogeneousComponent n P := by
  have h := MvPolynomial.sum_homogeneousComponent P
  rw [Finset.sum_range_succ] at h
  exact sub_eq_iff_eq_add.mpr h.symm

theorem polynomial_sub_top_degree_lt {σ : Type*} (P : MvPolynomial σ ℂ)
    (hpos : 0 < P.totalDegree) :
    (P - MvPolynomial.homogeneousComponent P.totalDegree P).totalDegree < P.totalDegree := by
  classical
  rw [polynomial_sub_top_eq_lower_sum]
  apply lt_of_le_of_lt (MvPolynomial.totalDegree_finsetSum _ _)
  apply (Finset.sup_lt_iff hpos).2
  intro n hn
  exact (MvPolynomial.homogeneousComponent_isHomogeneous n P).totalDegree_le.trans_lt
    (Finset.mem_range.mp hn)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_ExteriorTailLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology Set

theorem exterior_integral_tendsto_zero {d : ℕ} (μ : Measure (Ambient d))
    (a : Ambient d) (f : Ambient d → ℝ)
    (hi : IntegrableOn f (closedExterior a 1) μ) :
    Tendsto (fun j : ℕ => ∫ x in closedExterior a ((j : ℝ) + 2), f x ∂μ)
      atTop (𝓝 0) := by
  have hanti : Antitone (fun j : ℕ => closedExterior a ((j : ℝ) + 2)) := by
    intro i j hij x hx
    have hc : (i : ℝ) ≤ j := by exact_mod_cast hij
    change (i : ℝ) + 2 ≤ dist a x
    change (j : ℝ) + 2 ≤ dist a x at hx
    linarith
  have hempty : (⋂ j : ℕ, closedExterior a ((j : ℝ) + 2)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨j, hj⟩ := exists_nat_gt (dist a x)
    have hxj : (j : ℝ) + 2 ≤ dist a x := Set.mem_iInter.mp hx j
    linarith
  have hi0 : IntegrableOn f (closedExterior a ((0 : ℝ) + 2)) μ := by
    apply hi.mono_set
    intro x hx
    change 1 ≤ dist a x
    change (0 : ℝ) + 2 ≤ dist a x at hx
    linarith
  simpa only [hempty, setIntegral_empty] using! tendsto_setIntegral_of_antitone
    (fun j : ℕ => closedExterior_measurable a ((j : ℝ) + 2)) hanti ⟨0, by simpa using! hi0⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_PolynomialLeadingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Leading homogeneous terms under dilation

Along an expanding sequence of positive radii, normalization by the total
degree makes lower-degree powers vanish and preserves the top-degree power.
Applying this limit to the finite homogeneous decomposition of a polynomial
recovers its leading homogeneous component pointwise.
-/

namespace RieszRectifiability

noncomputable section

open Filter Topology

theorem polynomialExpansionRadius_pos (j : ℕ) : 0 < polynomialExpansionRadius j := by
  unfold polynomialExpansionRadius
  positivity

theorem inverse_pow_mul_pow_of_le (z : ℂ) (hz : z ≠ 0) (n N : ℕ) (hn : n ≤ N) :
    (z ^ N)⁻¹ * z ^ n = (z⁻¹) ^ (N - n) := by
  calc
    _ = (z ^ (N - n) * z ^ n)⁻¹ * z ^ n := by rw [← pow_add, Nat.sub_add_cancel hn]
    _ = _ := by
      rw [mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hz), mul_one, inv_pow]

theorem inverse_polynomialExpansionRadius_tendsto :
    Tendsto (fun j => (polynomialExpansionRadius j : ℂ)⁻¹) atTop (𝓝 0) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp shrinkingRadius_tendsto
  simpa only [Function.comp_def, shrinkingRadius, polynomialExpansionRadius, Complex.ofReal_zero,
    Complex.ofReal_inv] using! h

theorem polynomial_scale_coefficient_tendsto (N n : ℕ) (hn : n ≤ N) :
    Tendsto (fun j => ((polynomialExpansionRadius j : ℂ) ^ N)⁻¹ *
      (polynomialExpansionRadius j : ℂ) ^ n) atTop (𝓝 (if n = N then 1 else 0)) := by
  have hz : ∀ j, (polynomialExpansionRadius j : ℂ) ≠ 0 := fun j =>
    Complex.ofReal_ne_zero.mpr (polynomialExpansionRadius_pos j).ne'
  by_cases he : n = N
  · subst n
    simpa only [ite_eq_left rfl, inv_mul_cancel₀ (pow_ne_zero _ (hz _))] using!
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1))
  · have hpos : N - n ≠ 0 := by omega
    have h := inverse_polynomialExpansionRadius_tendsto.pow (N - n)
    simpa only [inverse_pow_mul_pow_of_le _ (hz _) n N hn, ite_eq_right he, zero_pow hpos] using! h

theorem polynomial_normalized_dilation_tendsto {d : ℕ}
    (P : MvPolynomial (Fin d) ℂ) (x : Ambient d) :
    Tendsto (fun j => ((polynomialExpansionRadius j : ℂ) ^ P.totalDegree)⁻¹ *
      MvPolynomial.eval (fun i => ((polynomialExpansionRadius j • x) i : ℂ)) P)
      atTop (𝓝 (MvPolynomial.eval (fun i => (x i : ℂ))
        (MvPolynomial.homogeneousComponent P.totalDegree P))) := by
  classical
  have hlim := tendsto_finsetSum (Finset.range (P.totalDegree + 1))
    (fun n hn => (polynomial_scale_coefficient_tendsto P.totalDegree n
      (Nat.le_of_lt_succ (Finset.mem_range.mp hn))).mul_const
        (MvPolynomial.eval (fun i => (x i : ℂ)) (MvPolynomial.homogeneousComponent n P)))
  have heq : (fun j => ((polynomialExpansionRadius j : ℂ) ^ P.totalDegree)⁻¹ *
      MvPolynomial.eval (fun i => ((polynomialExpansionRadius j • x) i : ℂ)) P) =
      (fun j => ∑ n ∈ Finset.range (P.totalDegree + 1),
        (((polynomialExpansionRadius j : ℂ) ^ P.totalDegree)⁻¹ *
          (polynomialExpansionRadius j : ℂ) ^ n) *
          MvPolynomial.eval (fun i => (x i : ℂ)) (MvPolynomial.homogeneousComponent n P)) := by
    funext j
    rw [polynomial_scaled_eval_homogeneous_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [heq]
  simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range,
    Nat.lt_succ_self, ite_true, if_true] using! hlim

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_PolynomialTailDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology

theorem exterior_dilation_coefficient_le_one (d k : ℕ) (hk : 2 ≤ k)
    (r : ℝ) (hr : 1 ≤ r) : r ^ (d + 2) * (r ^ k)⁻¹ * (r ^ d)⁻¹ ≤ 1 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  calc
    _ = r ^ 2 * (r ^ k)⁻¹ := by
      rw [pow_add]
      have hz : r ^ d ≠ 0 := pow_ne_zero _ hrpos.ne'
      field_simp
    _ ≤ 1 := by
      rw [← div_eq_mul_inv]
      exact (div_le_one (pow_pos hrpos k)).2 (pow_le_pow_right₀ hr hk)

theorem normalized_exterior_weighted_integral_tendsto_zero {d : ℕ}
    (k : ℕ) (hk : 2 ≤ k) (f : Ambient d → ℂ)
    (hi : IntegrableOn (fun x => ‖f x‖ * inverseDistancePow (d + 2) 0 x)
      (closedExterior 0 1)) :
    Tendsto (fun j => ∫ x in closedExterior (0 : Ambient d) 1,
      ‖((polynomialExpansionRadius j : ℂ) ^ k)⁻¹ * f (polynomialExpansionRadius j • x)‖ *
        inverseDistancePow (d + 2) 0 x) atTop (𝓝 0) := by
  have htail := exterior_integral_tendsto_zero volume (0 : Ambient d)
    (fun x => ‖f x‖ * inverseDistancePow (d + 2) 0 x) hi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
  · intro j
    exact integral_nonneg (fun x => mul_nonneg (norm_nonneg _) (inverseDistancePow_nonneg _ _ _))
  · intro j
    dsimp only
    rw [exterior_weighted_normalized_dilation_integral (d + 2) k f
      (polynomialExpansionRadius j) (polynomialExpansionRadius_pos j)]
    have hr : 1 ≤ polynomialExpansionRadius j := by
      unfold polynomialExpansionRadius
      linarith [Nat.cast_nonneg (α := ℝ) j]
    have hn : 0 ≤ ∫ x in closedExterior (0 : Ambient d) (polynomialExpansionRadius j),
        ‖f x‖ * inverseDistancePow (d + 2) 0 x :=
      integral_nonneg (fun x => mul_nonneg (norm_nonneg _) (inverseDistancePow_nonneg _ _ _))
    simpa only [one_mul, polynomialExpansionRadius] using!
      mul_le_mul_of_nonneg_right (exterior_dilation_coefficient_le_one d k hk _ hr) hn

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_IntegralZeroLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology

theorem ae_zero_of_nonnegative_integral_limit {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : ℕ → X → ℝ) (f : X → ℝ)
    (hi : ∀ j, Integrable (F j) μ) (hn : ∀ j x, 0 ≤ F j x)
    (hfm : Measurable f)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun j => F j x) atTop (𝓝 (f x)))
    (hint : Tendsto (fun j => ∫ x, F j x ∂μ) atTop (𝓝 0)) :
    ∀ᵐ x ∂μ, f x = 0 := by
  have hnn : ∀ᵐ x ∂μ, 0 ≤ f x := by
    filter_upwards [hlim] with x hx
    exact ge_of_tendsto hx (Eventually.of_forall (fun j => hn j x))
  have hL : Tendsto (fun j => ∫⁻ x, ENNReal.ofReal (F j x) ∂μ) atTop (𝓝 0) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hint
    simpa only [Function.comp_def, ENNReal.ofReal_zero,
      ofReal_integral_eq_lintegral_ofReal (hi _) (Eventually.of_forall (hn _))] using! h
  have hFat : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ 0 := by
    calc
      _ = ∫⁻ x, liminf (fun j => ENNReal.ofReal (F j x)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with x hx
        exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hx).liminf_eq.symm
      _ ≤ liminf (fun j => ∫⁻ x, ENNReal.ofReal (F j x) ∂μ) atTop :=
        lintegral_liminf_le' (fun j => (hi j).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ = 0 := hL.liminf_eq
  have hz : ∀ᵐ x ∂μ, ENNReal.ofReal (f x) = 0 :=
    (lintegral_eq_zero_iff hfm.ennreal_ofReal).mp (le_antisymm hFat (zero_le))
  filter_upwards [hz, hnn] with x hx hxnonneg
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp hx) hxnonneg

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_PolynomialLeadingExterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology

theorem polynomial_leading_component_ae_zero_exterior {d : ℕ}
    (P : MvPolynomial (Fin d) ℂ) (hk : 2 ≤ P.totalDegree)
    (hi : IntegrableOn (fun x : Ambient d =>
      ‖MvPolynomial.eval (fun j => (x j : ℂ)) P‖ * inverseDistancePow (d + 2) 0 x)
      (closedExterior 0 1)) :
    ∀ᵐ x ∂volume.restrict (closedExterior (0 : Ambient d) 1),
      MvPolynomial.eval (fun j => (x j : ℂ))
        (MvPolynomial.homogeneousComponent P.totalDegree P) = 0 := by
  let f : Ambient d → ℂ := fun x => MvPolynomial.eval (fun j => (x j : ℂ)) P
  let H : Ambient d → ℂ := fun x => MvPolynomial.eval (fun j => (x j : ℂ))
    (MvPolynomial.homogeneousComponent P.totalDegree P)
  let G : ℕ → Ambient d → ℝ := fun j x =>
    ‖((polynomialExpansionRadius j : ℂ) ^ P.totalDegree)⁻¹ *
      f (polynomialExpansionRadius j • x)‖ * inverseDistancePow (d + 2) 0 x
  have hGi : ∀ j, Integrable (G j) (volume.restrict (closedExterior 0 1)) := by
    intro j
    apply exterior_weighted_normalized_dilation_integrable (d + 2) P.totalDegree f
      (polynomialExpansionRadius j) (polynomialExpansionRadius_pos j)
    apply hi.mono_set
    intro x hx
    change 1 ≤ dist (0 : Ambient d) x
    change polynomialExpansionRadius j ≤ dist (0 : Ambient d) x at hx
    unfold polynomialExpansionRadius at hx
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hGn : ∀ j x, 0 ≤ G j x := fun j x =>
    mul_nonneg (norm_nonneg _) (inverseDistancePow_nonneg _ _ _)
  have hHm : Measurable (fun x => ‖H x‖ * inverseDistancePow (d + 2) 0 x) :=
    (mvPolynomial_complex_eval_continuous _).norm.measurable.mul
      (inverseDistancePow_measurable _ _)
  have hlim : ∀ᵐ x ∂volume.restrict (closedExterior (0 : Ambient d) 1),
      Tendsto (fun j => G j x) atTop (𝓝 (‖H x‖ * inverseDistancePow (d + 2) 0 x)) :=
    Eventually.of_forall (fun x =>
      (polynomial_normalized_dilation_tendsto P x).norm.mul_const (inverseDistancePow (d + 2) 0 x))
  have hint := normalized_exterior_weighted_integral_tendsto_zero P.totalDegree hk f hi
  have hz := ae_zero_of_nonnegative_integral_limit
    (volume.restrict (closedExterior (0 : Ambient d) 1)) G
    (fun x => ‖H x‖ * inverseDistancePow (d + 2) 0 x) hGi hGn hHm hlim hint
  filter_upwards [hz, ae_restrict_mem (closedExterior_measurable (0 : Ambient d) 1)] with x hx hmem
  have hd : 0 < dist (0 : Ambient d) x := lt_of_lt_of_le zero_lt_one hmem
  have hp : 0 < inverseDistancePow (d + 2) 0 x := by
    unfold inverseDistancePow
    positivity
  have hnorm : ‖H x‖ = 0 := (mul_eq_zero.mp hx).resolve_right hp.ne'
  exact norm_eq_zero.mp hnorm

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_PolynomialTailDegreeOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory

theorem polynomial_tail_has_degree_one_representative {d : ℕ}
    (P : MvPolynomial (Fin d) ℂ)
    (hi : IntegrableOn (fun x : Ambient d =>
      ‖MvPolynomial.eval (fun j => (x j : ℂ)) P‖ * inverseDistancePow (d + 2) 0 x)
      (closedExterior 0 1)) :
    ∃ Q : MvPolynomial (Fin d) ℂ, Q.totalDegree ≤ 1 ∧
      ∀ x : Ambient d, MvPolynomial.eval (fun j => (x j : ℂ)) P =
        MvPolynomial.eval (fun j => (x j : ℂ)) Q := by
  have aux : ∀ N : ℕ, ∀ P : MvPolynomial (Fin d) ℂ, P.totalDegree ≤ N →
      IntegrableOn (fun x : Ambient d => ‖MvPolynomial.eval (fun j => (x j : ℂ)) P‖ *
        inverseDistancePow (d + 2) 0 x) (closedExterior 0 1) →
      ∃ Q : MvPolynomial (Fin d) ℂ, Q.totalDegree ≤ 1 ∧
        ∀ x : Ambient d, MvPolynomial.eval (fun j => (x j : ℂ)) P =
          MvPolynomial.eval (fun j => (x j : ℂ)) Q := by
    intro N
    induction N with
    | zero =>
      intro P hP _
      exact ⟨P, by omega, fun _ => rfl⟩
    | succ N ih =>
      intro P hP htail
      by_cases hs : P.totalDegree ≤ 1
      · exact ⟨P, hs, fun _ => rfl⟩
      · have hhigh : 2 ≤ P.totalDegree := by omega
        have hz := homogeneous_polynomial_eval_zero_of_ae_exterior
          (MvPolynomial.homogeneousComponent P.totalDegree P)
          (MvPolynomial.homogeneousComponent_isHomogeneous P.totalDegree P)
          (by omega : P.totalDegree ≠ 0)
          (polynomial_leading_component_ae_zero_exterior P hhigh htail)
        let Q := P - MvPolynomial.homogeneousComponent P.totalDegree P
        have hQdeg : Q.totalDegree ≤ N := by
          have hd := polynomial_sub_top_degree_lt P (by omega)
          change (P - MvPolynomial.homogeneousComponent P.totalDegree P).totalDegree ≤ N
          omega
        have hQeval : ∀ x : Ambient d, MvPolynomial.eval (fun j => (x j : ℂ)) Q =
            MvPolynomial.eval (fun j => (x j : ℂ)) P := by
          intro x
          dsimp only [Q]
          rw [map_sub, hz x, sub_zero]
        have hQi : IntegrableOn (fun x : Ambient d =>
            ‖MvPolynomial.eval (fun j => (x j : ℂ)) Q‖ * inverseDistancePow (d + 2) 0 x)
            (closedExterior 0 1) := by
          apply htail.congr
          filter_upwards with x
          rw [hQeval x]
        obtain ⟨R, hR, hReq⟩ := ih Q hQdeg hQi
        exact ⟨R, hR, fun x => (hQeval x).symm.trans (hReq x)⟩
  exact aux P.totalDegree P le_rfl hi

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_AffineHeightRigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Function
open scoped NNReal

theorem represented_fractional_height_ae_affine_oai (p : ℕ)
    (w : Ambient (p + 1) → ℝ) (hw : LocallyIntegrable w)
    (T : 𝓢'(Ambient (p + 1), ℂ))
    (hT : ∀ g : 𝓢(Ambient (p + 1), ℂ), T g = ∫ x, w x • g x)
    (heq : ∀ g : 𝓢(Ambient (p + 1), ℂ), (∫ x, g x) = 0 →
      (∫ x, w x • fractionalSchwartzTest p g x) = 0)
    (htail : IntegrableOn (fun x => |w x| * inverseDistancePow (p + 1 + 2) 0 x)
      (closedExterior 0 1)) :
    ∃ c : ℝ, ∃ L : Ambient (p + 1) →L[ℝ] ℝ, ∀ᵐ x, w x = c + L x := by
  obtain ⟨P, hP⟩ := represented_fractional_height_ae_polynomial p w hw T hT heq
  have hPi := polynomial_inherits_height_tail (p + 1 + 2) w P hP 1 htail
  obtain ⟨Q, hQ, hPQ⟩ := polynomial_tail_has_degree_one_representative P hPi
  obtain ⟨c, L, hL⟩ := degree_one_polynomial_eval_affine Q hQ
  refine ⟨c.re, Complex.reCLM.comp L, ?_⟩
  filter_upwards [hP] with x hx
  have hv : (w x : ℂ) = c + L x := hx.trans ((hPQ x).trans (hL x))
  change w x = c.re + (L x).re
  simpa only [Complex.ofReal_re, Complex.add_re] using! congrArg Complex.re hv

end

end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.represented_fractional_height_ae_affine_oai := @OAI.RieszRectifiability.represented_fractional_height_ae_affine_oai
