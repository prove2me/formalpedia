-- Prove2me | solution 1 for OAI.CompleteCrouzeix.AdmissibleDomain.extremal_condition_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:35:25.644868+00:00
-- url     : https://prove2.me/submissions/ddad5103-6a74-4c29-a94e-e29e38aeb46c

import Mathlib
import Definitions.Def_StructuralCrouzeix
import Definitions.Def_OAIW2SC000
import Theorems.Thm_OAI_CompleteCrouzeix_AdmissibleDomain_ordered_modules
import Theorems.Thm_OAI_CompleteCrouzeix_AdmissibleDomain_positive_ordered
import Theorems.Thm_OAI_CompleteCrouzeix_AdmissibleDomain_resolvent_density_identification

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_CircleIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_30 u_31 u_32 u_33 u_34

open Set Filter Metric Complex
open scoped Topology ComplexConjugate

open MeasureTheory Set Complex
open scoped Topology Real
section

lemma fourier_natCast_toCircle (n : ℕ) (t : UnitAddCircle) :
    fourier (n : ℤ) t = (t.toCircle : ℂ)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, fourier_add, ih, fourier_one, pow_succ]

lemma fourier_neg_natCast_toCircle (n : ℕ) (t : UnitAddCircle) :
    fourier (-(n : ℤ)) t = ((t.toCircle : ℂ)⁻¹)^n := by
  rw [fourier_neg, fourier_natCast_toCircle, map_pow]
  congr 1
  exact (Circle.coe_inv_eq_conj t.toCircle).symm.trans (Circle.coe_inv t.toCircle)

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions
lemma integral_analytic_mul_pow {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 1)) {n : ℕ} (hn : n ≠ 0) :
    (∫ t : UnitAddCircle, (t.toCircle : ℂ)^n * f (t.toCircle : ℂ)
      ∂AddCircle.haarAddCircle) = 0 := by
  simpa only [Pi.mul_apply, Pi.pow_apply, id_eq, zero_pow hn, zero_mul] using
    integral_analytic_circle ((analyticOnNhd_id.pow n).mul hf)

lemma integral_reciprocal_analytic_mul_inv_pow {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 1)) {n : ℕ} (hn : n ≠ 0) :
    (∫ t : UnitAddCircle, ((t.toCircle : ℂ)⁻¹)^n * f (t.toCircle : ℂ)⁻¹
      ∂AddCircle.haarAddCircle) = 0 := by
  rw [unitAddCircle_integral_eq_circleAverage
      (fun z => (z⁻¹)^n * f z⁻¹)]
  rw [Real.circleAverage_zero_one_congr_inv
      (f := fun z => z^n*f z)]
  rw [← unitAddCircle_integral_eq_circleAverage]
  exact integral_analytic_mul_pow hf hn

end

open MeasureTheory Set Metric Complex Filter
open scoped Topology
section

lemma compact_parametric_hasDerivAt {α : Type u_31} [TopologicalSpace α]
    [CompactSpace α] [MeasurableSpace α] [BorelSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {U : Set ℂ} (hU : IsOpen U)
    {f f' : ℂ → α → ℂ}
    (hf : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    (hf' : ContinuousOn (Function.uncurry f') (U ×ˢ univ))
    (hd : ∀ z ∈ U, ∀ t, HasDerivAt (fun w => f w t) (f' z t) z)
    {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (fun w => ∫ t, f w t ∂μ) (∫ t, f' z t ∂μ) z := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  have hs : closedBall z (ε/2) ⊆ U := by
    exact (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεU
  obtain ⟨C,hC⟩ := (isCompact_closedBall z (ε/2)).prod isCompact_univ
    |>.exists_bound_of_continuousOn (hf'.mono (prod_mono hs (Subset.refl _)))
  have hc (w : ℂ) (hw : w ∈ U) : Continuous (f w) := by
    exact hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun t => ⟨hw,mem_univ t⟩)
  have hc' (w : ℂ) (hw : w ∈ U) : Continuous (f' w) := by
    exact hf'.comp_continuous (continuous_const.prodMk continuous_id)
      (fun t => ⟨hw,mem_univ t⟩)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := f) (F' := f') (bound := fun _ : α => C)
    (closedBall_mem_nhds z (by linarith : 0 < ε/2)) ?_ ?_ ?_ ?_ (integrable_const C) ?_).2
  · filter_upwards [hU.mem_nhds hz] with w hw
    exact (hc w hw).aestronglyMeasurable
  · exact (hc z hz).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (hc' z hz).aestronglyMeasurable
  · filter_upwards [] with t
    intro w hw
    exact hC (w,t) ⟨hw,mem_univ t⟩
  · filter_upwards [] with t
    intro w hw
    exact hd w (hs hw) t

end

open MeasureTheory Set Metric Complex Filter
open scoped Topology


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_MarkovOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u_35 u_36 u_37 u_38 u_39

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Metric Complex Filter
open scoped Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace
namespace CompleteCrouzeix

section

variable {X : Type u_37} [MeasurableSpace X] (μ : Measure X)

namespace MarkovKernel
variable {μ} (K : MarkovKernel μ) [instIsFiniteMeasureΜ : IsFiniteMeasure μ]
  {E : Type u_38} [NormedAddCommGroup E] [instInnerProductSpaceℂE : InnerProductSpace ℂ E] [instCompleteSpaceE : CompleteSpace E]

lemma toCLM_norm_le : ‖(K.toCLM : Lp E 2 μ →L[ℂ] Lp E 2 μ)‖ ≤ 1 := by
  change ‖LinearMap.mkContinuous _ 1 _‖ ≤ 1
  exact LinearMap.mkContinuous_norm_le _ (by norm_num) _

lemma applyFun_const (c : E) (x : X) :
    K.applyFun (Lp.const 2 μ c) x = c := by
  unfold applyFun
  calc _ = ∫ y, K.kernel x y • c ∂μ := by
         apply integral_congr_ae
         filter_upwards [Lp.coeFn_const (p := 2) (μ := μ) c] with y hy
         rw [hy]; rfl
       _ = c := by rw [integral_smul_const, K.row x, one_smul]

lemma toCLM_const (c : E) : K.toCLM (Lp.const 2 μ c) = Lp.const 2 μ c := by
  apply Lp.ext
  filter_upwards [K.applyLp_ae (Lp.const 2 μ c), Lp.coeFn_const (p := 2) (μ := μ) c]
    with x hx hc
  exact hx.trans ((K.applyFun_const c x).trans hc.symm)

end MarkovKernel
end
open MeasureTheory Set Metric Complex ComplexConjugate
open scoped Topology Real

namespace AnalyticBidiskKernel
variable (K : AnalyticBidiskKernel)

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_3
lemma circleB_right_nonpos_fourier (w : UnitAddCircle) (n : ℤ) (hn : n ≤ 0) :
    (∫ t, K.circleB w t * fourier n t ∂AddCircle.haarAddCircle) = 0 := by
  cases n with
  | ofNat k =>
    have hk : k = 0 := Int.natCast_nonpos_iff.mp hn
    subst k
    simpa using K.circleB_row_integral w
  | negSucc k =>
    change (∫ t, K.circleB w t * fourier (-(↑(k+1) : ℤ)) t ∂AddCircle.haarAddCircle) = 0
    simp only [fourier_neg_natCast_toCircle]
    simpa only [circleB, mul_comm] using
      integral_reciprocal_analytic_mul_inv_pow (K.right _ (inv_circle_mem w))
        (Nat.succ_ne_zero k)

lemma circleB_left_nonpos_fourier (t : UnitAddCircle) (n : ℤ) (hn : n ≤ 0) :
    (∫ w, K.circleB w t * fourier n w ∂AddCircle.haarAddCircle) = 0 := by
  cases n with
  | ofNat k =>
    have hk : k = 0 := Int.natCast_nonpos_iff.mp hn
    subst k
    simpa using K.circleB_column_integral t
  | negSucc k =>
    change (∫ w, K.circleB w t * fourier (-(↑(k+1) : ℤ)) w ∂AddCircle.haarAddCircle) = 0
    simp only [fourier_neg_natCast_toCircle]
    simpa only [circleB, mul_comm] using
      integral_reciprocal_analytic_mul_inv_pow (K.left _ (inv_circle_mem t))
        (Nat.succ_ne_zero k)

lemma conj_circleB_right_nonneg_fourier (w : UnitAddCircle) (n : ℤ) (hn : 0 ≤ n) :
    (∫ t, conj (K.circleB w t) * fourier n t ∂AddCircle.haarAddCircle) = 0 := by
  have h := congrArg conj (K.circleB_right_nonpos_fourier w (-n) (by omega))
  rw [← integral_conj] at h
  simpa only [map_mul, ← fourier_neg, neg_neg, map_zero] using h

end AnalyticBidiskKernel
end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_FourierResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u_40 u_41 u_42 u_43

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Metric Complex Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace

open scoped ComplexConjugate InnerProductSpace
namespace CompleteCrouzeix

section

section

variable {E : Type u_40} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [instCompleteSpaceE : CompleteSpace E]

lemma norm_sq_add_orthogonal
    {E : Type u_40} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (x y : E)
    (h : inner ℂ x y = 0) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x y h

namespace FourierResolution
variable (D : FourierResolution E)

lemma orthogonal (i j : Fin 3) (hij : i ≠ j) (u v : E) :
    inner ℂ (D.proj i u) (D.proj j v) = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right, D.selfAdjoint, D.proj_proj]
  simp [hij]

lemma norm_decompose (u : E) :
    ‖u‖ ^ 2 = ‖D.proj 0 u‖ ^ 2 + ‖D.proj 1 u‖ ^ 2 + ‖D.proj 2 u‖ ^ 2 := by
  conv_lhs => rw [← D.decompose u]
  rw [norm_sq_add_orthogonal]
  · rw [norm_sq_add_orthogonal]
    exact D.orthogonal 0 1 (by decide) u u
  · rw [inner_add_left, D.orthogonal 0 2 (by decide), D.orthogonal 1 2 (by decide)]
    simp

lemma adjoint_cauchy (M : E →L[ℂ] E)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M) :
    (D.cauchy M).adjoint = D.cauchyAdjoint M := by
  have h := congrArg ContinuousLinearMap.adjoint hswap
  simp only [ContinuousLinearMap.adjoint_comp, D.selfAdjoint] at h
  simp only [cauchy, cauchyAdjoint, map_add, ContinuousLinearMap.adjoint_comp,
    D.selfAdjoint, h]

lemma adjoint_markov_swap (M : E →L[ℂ] E)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M) :
    (D.proj 1).comp M.adjoint = M.adjoint.comp (D.proj 2) := by
  have h := congrArg ContinuousLinearMap.adjoint hswap
  simpa only [ContinuousLinearMap.adjoint_comp, D.selfAdjoint] using h

lemma adjoint_apply (M : E →L[ℂ] E) (u : E) :
    D.cauchyAdjoint M u = D.proj 0 u + D.proj 1 u + M.adjoint (D.proj 2 u) := rfl

lemma adjoint_positive (M : E →L[ℂ] E)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M) (u : E) :
    M.adjoint (D.proj 2 u) = D.proj 1 (M.adjoint u) := by
  exact (congrArg (fun T : E →L[ℂ] E => T u) (D.adjoint_markov_swap M hswap)).symm

lemma mean_adjoint (M : E →L[ℂ] E)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M) (u : E) :
    D.proj 0 (D.cauchyAdjoint M u) = D.proj 0 u := by
  rw [D.adjoint_apply, D.adjoint_positive M hswap]
  simp only [map_add, D.proj_proj]
  simp

lemma negative_adjoint (M : E →L[ℂ] E)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M) (u : E) :
    D.proj 2 (D.cauchyAdjoint M u) = 0 := by
  rw [D.adjoint_apply, D.adjoint_positive M hswap]
  simp only [map_add, D.proj_proj]
  simp [Fin.ext_iff]

theorem weighted_adjoint_bound (M : E →L[ℂ] E) (hM : ‖M‖ ≤ 1)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M) (u : E) :
    ‖D.cauchyAdjoint M u‖ ^ 2 + ‖D.proj 0 u‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 := by
  have hd : ‖M.adjoint (D.proj 2 u)‖ ≤ ‖D.proj 2 u‖ := by
    calc _ ≤ ‖M.adjoint‖ * ‖D.proj 2 u‖ := M.adjoint.le_opNorm _
      _ ≤ 1 * ‖D.proj 2 u‖ := by
        gcongr
        simpa using hM
      _ = _ := one_mul _
  have hadd : ‖D.proj 1 u + M.adjoint (D.proj 2 u)‖ ^ 2 ≤
      2 * (‖D.proj 1 u‖ ^ 2 + ‖D.proj 2 u‖ ^ 2) := by
    have htri := norm_add_le (D.proj 1 u) (M.adjoint (D.proj 2 u))
    have h1 := norm_nonneg (D.proj 1 u)
    have h2 := norm_nonneg (M.adjoint (D.proj 2 u))
    have h3 := norm_nonneg (D.proj 2 u)
    have h4 := norm_nonneg (D.proj 1 u + M.adjoint (D.proj 2 u))
    nlinarith [sq_nonneg (‖D.proj 1 u‖ - ‖D.proj 2 u‖)]
  have horth : inner ℂ (D.proj 0 u)
      (D.proj 1 u + M.adjoint (D.proj 2 u)) = 0 := by
    rw [D.adjoint_positive M hswap, inner_add_right,
      D.orthogonal 0 1 (by decide), D.orthogonal 0 1 (by decide)]
    simp
  rw [D.adjoint_apply, add_assoc,
    norm_sq_add_orthogonal _ _ horth,
    D.norm_decompose u]
  linarith

end FourierResolution
end

open scoped lp
variable {ι : Type u_42} {E : Type u_43} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [instCompleteSpaceE : CompleteSpace E]

open MeasureTheory

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_4
lemma scalarFourier_coefficient (j : Fin 3) (u : CircleL2) (n : ℤ) :
    fourierCoeff (scalarFourier.proj j u) n =
      if frequencyPart n = j then fourierCoeff u n else 0 := by
  simpa only [← fourierBasis_repr, scalarFourier, basisResolution] using
    basisProjection_repr (E := CircleL2) fourierBasis frequencyPart j u n

end

open MeasureTheory ComplexConjugate
open scoped Topology

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_5
lemma circle_fourier_ext {u v : CircleL2}
    (h : ∀ n : ℤ, fourierCoeff u n = fourierCoeff v n) : u = v := by
  apply fourierBasis.repr.injective
  apply lp.ext
  funext n
  simpa only [fourierBasis_repr] using h n

lemma circle_fourier_star (u : CircleL2) (n : ℤ) :
    fourierCoeff (star u : CircleL2) n = star (fourierCoeff u (-n)) := by
  rw [fourierCoeff, fourierCoeff]
  change _ = (starRingEnd ℂ) _
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star u] with t ht
  simp only [ht, Pi.star_apply, smul_eq_mul, map_mul, neg_neg,
    fourier_neg, RCLike.star_def]

lemma integral_fourier_nonzero (n : ℤ) (hn : n ≠ 0) :
    (∫ t : UnitAddCircle, fourier n t ∂AddCircle.haarAddCircle) = 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 1) n) 0
  simpa [fourierCoeff, Pi.single_eq_of_ne hn.symm] using h

lemma scalarFourier_fourier (j : Fin 3) (n : ℤ) :
    scalarFourier.proj j (fourierLp 2 n) =
      if frequencyPart n = j then fourierLp 2 n else 0 := by
  apply circle_fourier_ext
  intro k
  rw [scalarFourier_coefficient]
  have hf : fourierCoeff (fourierLp 2 n : CircleL2) k = (Pi.single n (1 : ℂ) : ℤ → ℂ) k := by
    rw [fourierCoeff_congr_ae (coeFn_fourierLp 2 n), fourierCoeff_fourier]
  by_cases h : frequencyPart n = j
  · simp only [h, ite_true, hf]
    by_cases hkn : k = n
    · subst k; simp [h]
    · simp [Pi.single_eq_of_ne hkn]
  · have hz : fourierCoeff (0 : CircleL2) k = 0 := by
      rw [fourierCoeff_congr_ae (Lp.coeFn_zero _ _ _)]
      simp [fourierCoeff]
    simp only [h, ite_false, hz, hf]
    by_cases hkn : k = n
    · subst k; simp [h]
    · simp [Pi.single_eq_of_ne hkn]

namespace AnalyticBidiskKernel
variable (K : AnalyticBidiskKernel)

lemma kernel_complex (w t : UnitAddCircle) :
    (K.kernel w t : ℂ) = 1 + K.circleB w t + conj (K.circleB w t) := by
  apply Complex.ext <;> simp [kernel, Complex.add_re, Complex.add_im]; ring

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_5
lemma scalarM_fourier_ae (n : ℤ) :
    K.scalarM (fourierLp 2 n) =ᵐ[AddCircle.haarAddCircle]
      fun w => ∫ t, (K.kernel w t : ℂ) * fourier n t ∂AddCircle.haarAddCircle := by
  filter_upwards [K.toMarkovKernel.applyLp_ae (fourierLp 2 n : CircleL2)] with w hw
  refine hw.trans ?_
  apply integral_congr_ae
  filter_upwards [coeFn_fourierLp 2 n] with t ht
  rw [ht]
  rfl

lemma scalarM_fourier_positive_ae (n : ℤ) (hn : 0 < n) :
    K.scalarM (fourierLp 2 n) =ᵐ[AddCircle.haarAddCircle]
      fun w => ∫ t, K.circleB w t * fourier n t ∂AddCircle.haarAddCircle := by
  filter_upwards [K.scalarM_fourier_ae n] with w hw
  rw [hw]
  simp_rw [K.kernel_complex, add_mul, one_mul]
  have hB : Continuous (fun t => K.circleB w t * fourier n t) :=
    (K.continuous_circleB.comp (continuous_const.prodMk continuous_id)).mul
      (fourier n).continuous
  have hBc : Continuous (fun t => conj (K.circleB w t) * fourier n t) :=
    (Complex.continuous_conj.comp
      (K.continuous_circleB.comp (continuous_const.prodMk continuous_id))).mul
      (fourier n).continuous
  have hint (f : UnitAddCircle → ℂ) (hf : Continuous f) :
      Integrable f AddCircle.haarAddCircle :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he₁ : (∫ t, fourier n t + K.circleB w t * fourier n t +
      conj (K.circleB w t) * fourier n t ∂AddCircle.haarAddCircle) =
      (∫ t, fourier n t + K.circleB w t * fourier n t ∂AddCircle.haarAddCircle) +
      (∫ t, conj (K.circleB w t) * fourier n t ∂AddCircle.haarAddCircle) :=
    integral_add ((hint _ (fourier n).continuous).add (hint _ hB)) (hint _ hBc)
  have he₂ : (∫ t, fourier n t + K.circleB w t * fourier n t ∂AddCircle.haarAddCircle) =
      (∫ t, fourier n t ∂AddCircle.haarAddCircle) +
      (∫ t, K.circleB w t * fourier n t ∂AddCircle.haarAddCircle) :=
    integral_add (hint _ (fourier n).continuous) (hint _ hB)
  rw [he₁, he₂,
    integral_fourier_nonzero n (ne_of_gt hn),
    K.conj_circleB_right_nonneg_fourier w n (le_of_lt hn), zero_add, add_zero]

lemma scalarM_fourier_positive_coefficient (n k : ℤ) (hn : 0 < n) (hk : 0 ≤ k) :
    fourierCoeff (K.scalarM (fourierLp 2 n)) k = 0 := by
  rw [fourierCoeff_congr_ae (K.scalarM_fourier_positive_ae n hn), fourierCoeff]
  simp only [smul_eq_mul]
  simp_rw [← integral_const_mul]
  have hc : Continuous (fun p : UnitAddCircle × UnitAddCircle =>
      fourier (-k) p.1 * (K.circleB p.1 p.2 * fourier n p.2)) :=
    ((fourier (-k)).continuous.comp continuous_fst).mul
      (K.continuous_circleB.mul ((fourier n).continuous.comp continuous_snd))
  rw [integral_integral_swap
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  have hz (t : UnitAddCircle) :
      (∫ w, fourier (-k) w * (K.circleB w t * fourier n t)
        ∂AddCircle.haarAddCircle) = 0 := by
    simp_rw [show ∀ w, fourier (-k) w * (K.circleB w t * fourier n t) =
      (K.circleB w t * fourier (-k) w) * fourier n t from fun w => by ring]
    rw [integral_mul_const, K.circleB_left_nonpos_fourier t (-k) (by omega), zero_mul]
  simp_rw [hz, integral_zero]

lemma scalarM_star (u : CircleL2) : K.scalarM (star u) = star (K.scalarM u) := by
  apply Lp.ext
  filter_upwards [K.toMarkovKernel.applyLp_ae (star u),
    K.toMarkovKernel.applyLp_ae u, Lp.coeFn_star (K.scalarM u)] with w hs hu hstar
  change K.toMarkovKernel.applyLp (star u) w = _
  rw [hs,hstar]
  change K.toMarkovKernel.applyFun (star u) w = conj (K.toMarkovKernel.applyLp u w)
  rw [hu]
  unfold MarkovKernel.applyFun
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star u] with t ht
  rw [ht]
  change (K.kernel w t : ℂ) * conj (u t) = conj ((K.kernel w t : ℂ) * u t)
  simp

lemma star_fourierLp (n : ℤ) :
    star (fourierLp 2 n : CircleL2) = fourierLp 2 (-n) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (fourierLp 2 n : CircleL2),
    coeFn_fourierLp 2 n, coeFn_fourierLp 2 (-n)] with t hs hn hneg
  simp only [hs,Pi.star_apply,hn,hneg,fourier_neg,RCLike.star_def]

lemma scalarM_fourier_negative_coefficient (n k : ℤ) (hn : n < 0) (hk : k ≤ 0) :
    fourierCoeff (K.scalarM (fourierLp 2 n)) k = 0 := by
  have he : (fourierLp 2 n : CircleL2) = star (fourierLp 2 (-n) : CircleL2) := by
    simpa only [neg_neg] using (star_fourierLp (-n)).symm
  rw [he,K.scalarM_star,circle_fourier_star,
    K.scalarM_fourier_positive_coefficient (-n) (-k) (by omega) (by omega),star_zero]

lemma scalarM_fourier_zero : K.scalarM (fourierLp 2 0) = fourierLp 2 0 := by
  have he : (fourierLp 2 0 : CircleL2) = Lp.const 2 AddCircle.haarAddCircle 1 := by
    apply Lp.ext
    filter_upwards [coeFn_fourierLp 2 0,
      Lp.coeFn_const (p := 2) (μ := AddCircle.haarAddCircle) (1 : ℂ)] with t hf hc
    rw [hf,hc]
    simp
  rw [he]
  exact K.toMarkovKernel.toCLM_const 1

lemma scalarM_fourier_swap (n : ℤ) :
    K.scalarM (scalarFourier.proj 1 (fourierLp 2 n)) =
      scalarFourier.proj 2 (K.scalarM (fourierLp 2 n)) := by
  rw [scalarFourier_fourier]
  rcases lt_trichotomy n 0 with hn | hn | hn
  · have hfn : frequencyPart n ≠ 1 := by simp [frequencyPart,hn.ne,not_lt.mpr hn.le]
    simp only [hfn,ite_false,map_zero]
    apply circle_fourier_ext
    intro k
    have hz : fourierCoeff (0 : CircleL2) k = 0 := by
      rw [fourierCoeff_congr_ae (Lp.coeFn_zero _ _ _)]
      simp [fourierCoeff]
    rw [hz,scalarFourier_coefficient]
    split_ifs with hfk
    · have hk : k < 0 := by
        unfold frequencyPart at hfk
        split_ifs at hfk with h0 hp <;> simp_all
        omega
      exact (K.scalarM_fourier_negative_coefficient n k hn hk.le).symm
    · rfl
  · subst n
    rw [K.scalarM_fourier_zero,scalarFourier_fourier]
    simp [frequencyPart]
  · have hfn : frequencyPart n = 1 := by simp [frequencyPart,hn.ne',hn]
    simp only [hfn,ite_true]
    apply circle_fourier_ext
    intro k
    rw [scalarFourier_coefficient]
    split_ifs with hfk
    · rfl
    · have hk : 0 ≤ k := by
        by_contra hk
        have hk' : k < 0 := by omega
        exact hfk (by simp [frequencyPart,hk'.ne,not_lt.mpr hk'.le])
      exact K.scalarM_fourier_positive_coefficient n k hn hk

lemma scalarM_swap : K.scalarM.comp (scalarFourier.proj 1) =
    (scalarFourier.proj 2).comp K.scalarM := by
  apply ContinuousLinearMap.ext_on (s := Set.range (fourierLp (T := 1) 2))
  · change ∀ x, x ∈ closure (Submodule.span ℂ (Set.range (fourierLp (T := 1) 2)) : Set CircleL2)
    change ∀ x, x ∈ (Submodule.span ℂ (Set.range (fourierLp (T := 1) 2))).topologicalClosure
    rw [span_fourierLp_closure_eq_top (by norm_num : (2 : ENNReal) ≠ ∞)]
    intro x; trivial
  · rintro _ ⟨n,rfl⟩
    exact K.scalarM_fourier_swap n

end AnalyticBidiskKernel
end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_ExteriorProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_45

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Metric Complex Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace
open scoped ComplexConjugate InnerProductSpace
open Set Metric Filter Complex
open scoped Topology

open MeasureTheory Set Complex
open scoped Topology
section

lemma interval_integral_swap_continuous {f : ℝ → ℝ → ℂ}
    (hf : ContinuousOn (Function.uncurry f) (Icc (0:ℝ) 1 ×ˢ Icc 0 1)) :
    (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, f s t) =
      ∫ t in (0:ℝ)..1, ∫ s in (0:ℝ)..1, f s t := by
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]
  apply integral_integral_swap
  rw [Measure.prod_restrict]
  exact hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

lemma analytic_segment_integral {U : Set ℂ} (hU : Convex ℝ U)
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U) {z w : ℂ} (hz : z ∈ U) (hw : w ∈ U) :
    (∫ r in (0:ℝ)..1, (w-z) * deriv F (z + (r:ℂ)*(w-z))) = F w - F z := by
  have hm : MapsTo (fun r : ℝ => z + (r:ℂ)*(w-z)) (Icc 0 1) U := by
    intro r hr
    simpa only [Complex.real_smul] using hU.add_smul_sub_mem hz hw hr
  have hc : ContinuousOn (fun r : ℝ => (w-z) * deriv F (z+(r:ℂ)*(w-z))) (Icc 0 1) :=
    continuousOn_const.mul (hF.deriv.continuousOn.comp (by fun_prop) hm)
  have hd : ∀ r ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun r : ℝ => F (z+(r:ℂ)*(w-z)))
        ((w-z)*deriv F (z+(r:ℂ)*(w-z))) r := by
    intro r hr
    have hi := (((hasDerivAt_id r).ofReal_comp).mul_const (w-z)).const_add z
    simpa only [Function.comp_def, ofReal_one, one_mul, mul_one, id_eq, mul_comm] using
      ((hF _ (hm hr)).differentiableAt.hasDerivAt).comp r hi
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1)
    (fun r hr => hd r (by simpa using hr))
    (show ContinuousOn _ (uIcc (0:ℝ) 1) by simpa using hc).intervalIntegrable
  simpa using he

theorem convex_closed_curve_remainder {U : Set ℂ} (hU : Convex ℝ U)
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U)
    {γ γ' : ℝ → ℂ} (hγ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt γ (γ' t) t)
    (hγ' : ContinuousOn γ' (Icc 0 1)) (hend : γ 1 = γ 0)
    (hcurve : MapsTo γ (Icc 0 1) U) {z : ℂ} (hz : z ∈ U)
    (hne : ∀ t ∈ Icc (0:ℝ) 1, γ t ≠ z) :
    (∫ t in (0:ℝ)..1, γ' t / (γ t-z) * (F (γ t)-F z)) = 0 := by
  have hcγ : ContinuousOn γ (Icc (0:ℝ) 1) := fun t ht =>
    (hγ t ht).continuousAt.continuousWithinAt
  have hm : MapsTo (fun p : ℝ × ℝ => z+(p.2:ℂ)*(γ p.1-z))
      (Icc 0 1 ×ˢ Icc 0 1) U := by
    intro p hp
    simpa only [Complex.real_smul] using hU.add_smul_sub_mem hz (hcurve hp.1) hp.2
  have hpath : ContinuousOn (fun p : ℝ × ℝ => z+(p.2:ℂ)*(γ p.1-z))
      (Icc 0 1 ×ˢ Icc 0 1) := by
    exact continuousOn_const.add
      ((continuous_ofReal.continuousOn.comp continuousOn_snd (fun _ hp => hp.2)).mul
        ((hcγ.comp continuousOn_fst (fun _ hp => hp.1)).sub continuousOn_const))
  have hc : ContinuousOn
      (fun p : ℝ × ℝ => γ' p.1 * deriv F (z+(p.2:ℂ)*(γ p.1-z)))
      (Icc 0 1 ×ˢ Icc 0 1) :=
    (hγ'.comp continuousOn_fst (fun _ hp => hp.1)).mul
      (hF.deriv.continuousOn.comp hpath hm)
  have hinner : ∀ r ∈ Icc (0:ℝ) 1,
      (∫ t in (0:ℝ)..1, γ' t * deriv F (z+(r:ℂ)*(γ t-z))) = 0 := by
    intro r hr
    have hct : ContinuousOn (fun t => γ' t * deriv F (z+(r:ℂ)*(γ t-z))) (Icc 0 1) :=
      hc.comp (continuousOn_id.prodMk continuousOn_const) (fun t ht => ⟨ht,hr⟩)
    by_cases hr0 : r = 0
    · subst r
      simp only [ofReal_zero, zero_mul, add_zero]
      rw [intervalIntegral.integral_mul_const]
      have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1)
        (fun t ht => hγ t (by simpa using ht)) (show ContinuousOn _ (uIcc (0:ℝ) 1) by simpa using hγ').intervalIntegrable
      rw [hi,hend,sub_self,zero_mul]
    · have hd : ∀ t ∈ Icc (0:ℝ) 1,
          HasDerivAt (fun t => F (z+(r:ℂ)*(γ t-z)))
            ((r:ℂ)*(γ' t*deriv F (z+(r:ℂ)*(γ t-z)))) t := by
        intro t ht
        have hi : HasDerivAt (fun t => z+(r:ℂ)*(γ t-z)) ((r:ℂ)*γ' t) t :=
          (((hγ t ht).sub_const z).const_mul (r:ℂ)).const_add z
        have he := ((hF (z+(r:ℂ)*(γ t-z)) (hm (x := (t,r)) ⟨ht,hr⟩)).differentiableAt.hasDerivAt).comp t hi
        simpa only [Function.comp_def, mul_left_comm, mul_comm, mul_assoc] using he
      have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1)
        (fun t ht => hd t (by simpa using ht))
        (show ContinuousOn (fun t => (r:ℂ)*(γ' t*deriv F (z+(r:ℂ)*(γ t-z)))) (uIcc (0:ℝ) 1) by
          simpa using continuousOn_const.fun_mul hct).intervalIntegrable
      rw [intervalIntegral.integral_const_mul,hend,sub_self] at hi
      exact (mul_eq_zero.mp hi).resolve_left (ofReal_ne_zero.mpr hr0)
  calc
    _ = ∫ t in (0:ℝ)..1, ∫ r in (0:ℝ)..1,
        γ' t * deriv F (z+(r:ℂ)*(γ t-z)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc (0:ℝ) 1 := by simpa using ht
      change γ' t / (γ t-z) * (F (γ t)-F z) = _
      rw [← analytic_segment_integral hU hF hz (hcurve ht'),
        ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r hr
      field_simp [sub_ne_zero.mpr (hne t ht')]
    _ = ∫ r in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
        γ' t * deriv F (z+(r:ℂ)*(γ t-z)) := interval_integral_swap_continuous hc
    _ = ∫ r in (0:ℝ)..1, (0:ℂ) := by
      apply intervalIntegral.integral_congr
      intro r hr
      exact hinner r (by simpa using hr)
    _ = 0 := intervalIntegral.integral_zero

theorem convex_closed_curve_cauchy {U : Set ℂ} (hU : Convex ℝ U)
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U)
    {γ γ' : ℝ → ℂ} (hγ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt γ (γ' t) t)
    (hγ' : ContinuousOn γ' (Icc 0 1)) (hend : γ 1 = γ 0)
    (hcurve : MapsTo γ (Icc 0 1) U) {z : ℂ} (hz : z ∈ U)
    (hne : ∀ t ∈ Icc (0:ℝ) 1, γ t ≠ z) :
    (∫ t in (0:ℝ)..1, γ' t / (γ t-z) * F (γ t)) =
      (∫ t in (0:ℝ)..1, γ' t / (γ t-z)) * F z := by
  have hcγ : ContinuousOn γ (Icc (0:ℝ) 1) := fun t ht =>
    (hγ t ht).continuousAt.continuousWithinAt
  have hquot : ContinuousOn (fun t => γ' t / (γ t-z)) (Icc (0:ℝ) 1) :=
    hγ'.div (hcγ.sub continuousOn_const) (fun t ht => sub_ne_zero.mpr (hne t ht))
  have h1 : IntervalIntegrable (fun t => γ' t / (γ t-z) * F (γ t)) volume 0 1 :=
    (show ContinuousOn _ (uIcc (0:ℝ) 1) by
      simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Pi.mul_apply, Function.comp_def] using hquot.fun_mul (hF.continuousOn.comp hcγ hcurve)).intervalIntegrable
  have h2 : IntervalIntegrable (fun t => γ' t / (γ t-z) * F z) volume 0 1 :=
    (show ContinuousOn _ (uIcc (0:ℝ) 1) by
      simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Pi.mul_apply] using hquot.fun_mul (continuousOn_const (c := F z))).intervalIntegrable
  have he := convex_closed_curve_remainder hU hF hγ hγ' hend hcurve hz hne
  simp_rw [mul_sub] at he
  rw [intervalIntegral.integral_sub h1 h2,
    intervalIntegral.integral_mul_const] at he
  exact sub_eq_zero.mp he

end

open MeasureTheory Set Complex Metric
open scoped Topology
section

lemma reciprocalResolventDenom_ne_zero {a b : ℂ} {h : ℂ → ℂ} {z : ℂ}
    (ha : a ≠ 0) (hz : ∀ t : ℂ, 1 ≤ ‖t‖ → exteriorMap a b h t ≠ z)
    {s : ℂ} (hs : s ∈ closedBall 0 1) :
    reciprocalResolventDenom a b h z s ≠ 0 := by
  by_cases hs0 : s = 0
  · subst s; simpa [reciprocalResolventDenom] using ha
  have hsi : 1 ≤ ‖s⁻¹‖ := by
    rw [norm_inv]
    exact (one_le_inv₀ (norm_pos_iff.mpr hs0)).mpr (by simpa using hs)
  have he : reciprocalResolventDenom a b h z s = s*(exteriorMap a b h s⁻¹-z) := by
    simp only [reciprocalResolventDenom, exteriorMap, inv_inv]
    field_simp
    ring
  rw [he]
  exact mul_ne_zero hs0 (sub_ne_zero.mpr (hz _ hsi))

lemma reciprocalResolvent_analytic {a b : ℂ} {h : ℂ → ℂ} {z : ℂ}
    (ha : a ≠ 0) (hh : AnalyticOnNhd ℂ h (closedBall 0 1))
    (hz : ∀ t : ℂ, 1 ≤ ‖t‖ → exteriorMap a b h t ≠ z) :
    AnalyticOnNhd ℂ (reciprocalResolvent a b h z) (closedBall 0 1) := by
  intro s hs
  exact (analyticAt_const.sub ((analyticAt_id.pow 2).mul (hh.deriv s hs))).div
    (analyticAt_const.add (analyticAt_id.mul ((analyticAt_const.add (hh s hs)).sub
      analyticAt_const))) (reciprocalResolventDenom_ne_zero ha hz hs)

lemma reciprocalResolvent_eq {a b : ℂ} {h : ℂ → ℂ} {z t : ℂ}
    (ht : t ≠ 0) (hh : DifferentiableAt ℂ h t⁻¹) :
    reciprocalResolvent a b h z t⁻¹ =
      t*deriv (exteriorMap a b h) t / (exteriorMap a b h t-z) := by
  rw [(hasDerivAt_exteriorMap ht hh).deriv]
  simp only [reciprocalResolvent, reciprocalResolventDenom, exteriorMap]
  have he : a+t⁻¹*(b+h t⁻¹-z) = t⁻¹*(a*t+b+h t⁻¹-z) := by
    field_simp; ring
  rw [he, div_mul_eq_div_div, div_inv_eq_mul]
  congr 1
  field_simp

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_10
theorem exterior_cauchy_kernel_integral {a b : ℂ} {h : ℂ → ℂ} {z : ℂ}
    (ha : a ≠ 0) (hh : AnalyticOnNhd ℂ h (closedBall 0 1))
    (hz : ∀ t : ℂ, 1 ≤ ‖t‖ → exteriorMap a b h t ≠ z) :
    (∫ t : UnitAddCircle,
      (t.toCircle : ℂ)*deriv (exteriorMap a b h) (t.toCircle : ℂ) /
        (exteriorMap a b h (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1 := by
  calc
    _ = ∫ t : UnitAddCircle, reciprocalResolvent a b h z (t.toCircle : ℂ)⁻¹
        ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with t
      apply (reciprocalResolvent_eq (Circle.coe_ne_zero _)
        (hh _ (by simp [mem_closedBall, dist_eq_norm, Circle.norm_coe])).differentiableAt).symm
    _ = reciprocalResolvent a b h z 0 :=
      integral_reciprocal_analytic (reciprocalResolvent_analytic ha hh hz)
    _ = 1 := by simp [reciprocalResolvent, reciprocalResolventDenom, ha]

lemma unitAddCircle_integral_eq_unitInterval {E : Type u_45}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℂ → E) :
    (∫ t : UnitAddCircle, f (t.toCircle : ℂ) ∂AddCircle.haarAddCircle) =
      ∫ r in (0:ℝ)..1, f (circleMap 0 1 (2*Real.pi*r)) := by
  rw [AddCircle.integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage 1 0]
  simp only [inv_one, one_smul, zero_add]
  apply intervalIntegral.integral_congr
  intro r hr
  simp only [AddCircle.toCircle_apply_mk, Circle.coe_exp, circleMap,
    ofReal_one, one_mul, zero_add, div_one]

theorem circle_convex_cauchy {U : Set ℂ} (hU : Convex ℝ U)
    {F G : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U)
    (hG : AnalyticOnNhd ℂ G (sphere 0 1))
    (hcurve : MapsTo G (sphere 0 1) U) {z : ℂ} (hz : z ∈ U)
    (hne : ∀ t ∈ sphere (0:ℂ) 1, G t ≠ z)
    (hmass : (∫ t : UnitAddCircle,
      (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ) / (G (t.toCircle : ℂ)-z)
        ∂AddCircle.haarAddCircle) = 1) :
    (∫ t : UnitAddCircle,
      ((t.toCircle : ℂ)*deriv G (t.toCircle : ℂ) / (G (t.toCircle : ℂ)-z)) *
        F (G (t.toCircle : ℂ)) ∂AddCircle.haarAddCircle) = F z := by
  let τ : ℝ → ℂ := fun r => circleMap 0 1 (2*Real.pi*r)
  let c : ℂ := (2*Real.pi:ℝ)*I
  have hc : c ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero)) I_ne_zero
  have hτ (r : ℝ) : τ r ∈ sphere (0:ℂ) 1 := by
    exact circleMap_mem_sphere 0 (by norm_num) _
  have hτc : Continuous τ := by dsimp [τ]; fun_prop
  have hτd (r : ℝ) : HasDerivAt τ (c*τ r) r := by
    have he := (hasDerivAt_circleMap 0 1 (2*Real.pi*r)).scomp r
      ((hasDerivAt_id r).const_mul (2*Real.pi))
    simpa only [Function.comp_def, id_eq, mul_one, one_mul, Complex.real_smul, τ, c,
      mul_assoc, mul_left_comm, mul_comm] using he
  have hγ (r : ℝ) : HasDerivAt (fun r => G (τ r)) (c*(τ r*deriv G (τ r))) r := by
    simpa only [Function.comp_def, mul_assoc, mul_comm, mul_left_comm] using
      ((hG _ (hτ r)).differentiableAt.hasDerivAt).comp r (hτd r)
  have hγ' : ContinuousOn (fun r => c*(τ r*deriv G (τ r))) (Icc (0:ℝ) 1) := by
    exact continuousOn_const.fun_mul (hτc.continuousOn.fun_mul
      (hG.deriv.continuousOn.comp hτc.continuousOn (fun r _ => hτ r)))
  have hend : G (τ 1) = G (τ 0) := by
    congr 1
    simpa [τ] using (periodic_circleMap 0 1) 0
  have he := convex_closed_curve_cauchy hU hF (fun r _ => hγ r) hγ' hend
    (fun r _ => hcurve (hτ r)) hz (fun r _ => hne _ (hτ r))
  have h1 : (fun r => c*(τ r*deriv G (τ r)) / (G (τ r)-z) * F (G (τ r))) =
      (fun r => c*((τ r*deriv G (τ r) / (G (τ r)-z))*F (G (τ r)))) := by
    funext r; ring
  have h2 : (fun r => c*(τ r*deriv G (τ r)) / (G (τ r)-z)) =
      (fun r => c*(τ r*deriv G (τ r) / (G (τ r)-z))) := by
    funext r; ring
  rw [h1,h2,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at he
  erw [unitAddCircle_integral_eq_unitInterval (fun t : ℂ => t*deriv G t/(G t-z))] at hmass
  erw [unitAddCircle_integral_eq_unitInterval (fun t : ℂ => (t*deriv G t/(G t-z))*F (G t))]
  change (∫ r in (0:ℝ)..1, (τ r*deriv G (τ r) / (G (τ r)-z))*F (G (τ r))) = F z
  change (∫ r in (0:ℝ)..1, τ r*deriv G (τ r) / (G (τ r)-z)) = 1 at hmass
  rw [hmass,mul_one] at he
  exact mul_left_cancel₀ hc he

end

open Set Metric Complex MeasureTheory
open scoped Topology


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_HilbertSchmidt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_48 u_49 u_50 u_51 u_52 u_53

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Metric Complex Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace
open scoped ComplexConjugate InnerProductSpace
open Set Metric Filter Complex
open scoped Topology
open MeasureTheory Set Complex
open scoped Topology
open MeasureTheory Set Complex Metric
open scoped Topology
open Set Filter Metric Complex
open scoped Topology

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

section

variable {m : Type u_48} [Fintype m] [instDecidableEqM : DecidableEq m]

theorem trace_mul_nonneg {A B : Matrix m m ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (Matrix.trace (A * B)).re := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have h := (hB.mul_mul_conjTranspose_same C).trace_nonneg
  have hr := (Complex.nonneg_iff.mp h).1
  rw [Matrix.trace_mul_cycle] at hr
  simpa only [Matrix.star_eq_conjTranspose] using hr

private theorem trace_blocks
    {m : Type u_48} [Fintype m] [DecidableEq m] (a b c d : Matrix m m ℂ) :
    (Matrix.fromBlocks a b c d).trace = a.trace + d.trace := by
  simp [Matrix.trace]

theorem block_density_hs {p q r : Matrix m m ℂ}
    (h : (Matrix.fromBlocks p rᴴ r q).PosSemidef) :
    2 * hsSq r ≤ hsSq p + hsSq q := by
  let J : Matrix (m ⊕ m) (m ⊕ m) ℂ := Matrix.fromBlocks 1 0 0 (-1)
  let Δ := Matrix.fromBlocks p rᴴ r q
  have hp : p.IsHermitian := by
    have hh := h.isHermitian
    rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_inj] at hh
    exact hh.1
  have hq : q.IsHermitian := by
    have hh := h.isHermitian
    rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_inj] at hh
    exact hh.2.2.2
  have hJ : Jᴴ = J := by simp [J, Matrix.fromBlocks_conjTranspose]
  have hΔ : Δ.PosSemidef := h
  have hj := hΔ.mul_mul_conjTranspose_same J
  rw [hJ] at hj
  have ht := trace_mul_nonneg hΔ hj
  simp only [Δ, J, Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg, Matrix.neg_mul,
    add_zero, zero_add, neg_neg, trace_blocks, Matrix.trace_add,
    Complex.add_re, Matrix.trace_neg, Complex.neg_re] at ht
  unfold hsSq
  rw [hp, hq]
  rw [Matrix.trace_mul_comm r rᴴ] at ht
  linarith

lemma block_density_norm {p q r : HSMatrix m}
    (h : (Matrix.fromBlocks (fromHS p) (fromHS r)ᴴ (fromHS r) (fromHS q)).PosSemidef) :
    2 * ‖r‖ ^ 2 ≤ ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
  simpa only [← norm_toHS_sq, toHS_fromHS] using block_density_hs h

open MeasureTheory
variable {α : Type u_50} [MeasurableSpace α] {μ : Measure α}

lemma l2_integrable_norm_sq
    {m : Type u_48} [Fintype m] [DecidableEq m] {α : Type u_50} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} (u : Lp (HSMatrix m) 2 μ) :
    Integrable (fun t => ‖u t‖ ^ 2) μ := by
  simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) u u

theorem block_density_l2 {p q r : Lp (HSMatrix m) 2 μ}
    (h : ∀ᵐ t ∂μ,
      (Matrix.fromBlocks (fromHS (p t)) (fromHS (r t))ᴴ
        (fromHS (r t)) (fromHS (q t))).PosSemidef) :
    2 * ‖r‖ ^ 2 ≤ ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
  simp only [l2_norm_sq]
  rw [← integral_const_mul, ← integral_add (l2_integrable_norm_sq p)
    (l2_integrable_norm_sq q)]
  apply integral_mono_ae ((l2_integrable_norm_sq r).const_mul 2)
    ((l2_integrable_norm_sq p).add (l2_integrable_norm_sq q))
  filter_upwards [h] with t ht
  exact block_density_norm ht

end

section
open scoped InnerProductSpace
variable {m : Type u_51} [Fintype m] [instDecidableEqM : DecidableEq m]

lemma hs_inner
    {m : Type u_51} [Fintype m] [DecidableEq m] (A B : Matrix m m ℂ) :
    inner ℂ (toHS A) (toHS B) = Matrix.trace (Aᴴ * B) := by
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, RCLike.inner_apply,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    toHS]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

lemma hsLeft_adjoint (A : Matrix m m ℂ) : (hsLeft A).adjoint = hsLeft Aᴴ := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change inner ℂ (toHS (Aᴴ * fromHS x)) y =
    inner ℂ x (toHS (A * fromHS y))
  conv_lhs => rhs; rw [← toHS_fromHS y]
  conv_rhs => lhs; rw [← toHS_fromHS x]
  rw [hs_inner, hs_inner, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

lemma hsRight_adjoint (A : Matrix m m ℂ) : (hsRight A).adjoint = hsRight Aᴴ := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change inner ℂ (toHS (fromHS x * Aᴴ)) y =
    inner ℂ x (toHS (fromHS y * A))
  conv_lhs => rhs; rw [← toHS_fromHS y]
  conv_rhs => lhs; rw [← toHS_fromHS x]
  rw [hs_inner, hs_inner, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [Matrix.mul_assoc]

end

open MeasureTheory


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_OrderedMultiplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u_54 u_55 u_56 u_57 u_58 u_59 u_60

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Metric Complex Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace
open scoped ComplexConjugate InnerProductSpace
open Set Metric Filter Complex
open scoped Topology
open MeasureTheory Set Complex
open scoped Topology
open MeasureTheory Set Complex Metric
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace CompleteCrouzeix

section

section

section

section
variable {E : Type u_54} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
namespace FourierResolution
variable (D : FourierResolution E)
variable (J : E ≃ₗᵢ⋆[ℂ] E)
    (hJJ : Function.Involutive J)
    (hJ0 : ∀ u, J (D.proj 0 u) = D.proj 0 (J u))
    (hJ1 : ∀ u, J (D.proj 1 u) = D.proj 2 (J u))

lemma nonnegative_decompose (v : E) (hv : D.proj 2 v = 0) :
    D.proj 0 v + D.proj 1 v = v := by
  simpa only [hv, add_zero] using D.decompose v

include hJ1 in

lemma hermitian_fourier_norm (v : E) (hv : D.proj 2 v = 0)
    (hv0 : J (D.proj 0 v) = D.proj 0 v) :
    ‖v + J v‖ ^ 2 = 2 * (‖v‖ ^ 2 + ‖D.proj 0 v‖ ^ 2) := by
  have hvd := D.nonnegative_decompose v hv
  have hjd : J v = D.proj 0 v + D.proj 2 (J v) := by
    calc
      J v = J (D.proj 0 v + D.proj 1 v) := congrArg J hvd.symm
      _ = _ := by rw [map_add, hv0, hJ1]
  have hn1 : ‖D.proj 2 (J v)‖ = ‖D.proj 1 v‖ := by
    rw [← hJ1, J.norm_map]
  have hsum : v + J v = (2 : ℂ) • D.proj 0 v + D.proj 1 v + D.proj 2 (J v) := by
    calc
      _ = (D.proj 0 v + D.proj 1 v) + (D.proj 0 v + D.proj 2 (J v)) :=
        congrArg₂ (· + ·) hvd.symm hjd
      _ = _ := by simp only [two_smul]; abel
  have ho1 : inner ℂ ((2 : ℂ) • D.proj 0 v) (D.proj 1 v) = 0 := by
    rw [inner_smul_left, D.orthogonal 0 1 (by decide)]
    simp
  have ho2 : inner ℂ ((2 : ℂ) • D.proj 0 v + D.proj 1 v)
      (D.proj 2 (J v)) = 0 := by
    rw [inner_add_left, inner_smul_left,
      D.orthogonal 0 2 (by decide), D.orthogonal 1 2 (by decide)]
    simp
  rw [hsum, norm_sq_add_orthogonal _ _ ho2, norm_sq_add_orthogonal _ _ ho1,
    norm_smul, hn1]
  have hn := D.norm_decompose v
  rw [hv, norm_zero, zero_pow (by decide), add_zero] at hn
  norm_num
  nlinarith

lemma adjoint_module_apply (M L : E →L[ℂ] E)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M)
    (hmod : (D.cauchy M).comp (L.comp (D.cauchy M)) = L.comp (D.cauchy M))
    (r : E) :
    D.cauchyAdjoint M (L.adjoint (D.cauchyAdjoint M r)) =
      D.cauchyAdjoint M (L.adjoint r) := by
  have h := congrArg ContinuousLinearMap.adjoint hmod
  simp only [ContinuousLinearMap.adjoint_comp, D.adjoint_cauchy M hswap] at h
  exact congrArg (fun T : E →L[ℂ] E => T r) h

include hJ0 hJ1 in
lemma hermitian_diagonal_bound (M L : E →L[ℂ] E)
    (hM : ‖M‖ ≤ 1) (hL : ‖L‖ ≤ 1)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M)
    (hmod : (D.cauchy M).comp (L.comp (D.cauchy M)) = L.comp (D.cauchy M))
    (p r : E) (hp : p = L.adjoint r) (hpJ : J p = p) :
    ‖D.cauchyAdjoint M p + J (D.cauchyAdjoint M p)‖ ^ 2 ≤
      4 * ‖D.cauchyAdjoint M r‖ ^ 2 := by
  have hdiag := D.hermitian_fourier_norm J hJ1 (D.cauchyAdjoint M p)
    (D.negative_adjoint M hswap p)
    (by rw [D.mean_adjoint M hswap, hJ0, hpJ])
  have heq : D.cauchyAdjoint M p =
      D.cauchyAdjoint M (L.adjoint (D.cauchyAdjoint M r)) := by
    rw [D.adjoint_module_apply M L hswap hmod, hp]
  have hw := D.weighted_adjoint_bound M hM hswap (L.adjoint (D.cauchyAdjoint M r))
  have hnorm : ‖L.adjoint (D.cauchyAdjoint M r)‖ ≤ ‖D.cauchyAdjoint M r‖ := by
    calc _ ≤ ‖L.adjoint‖ * ‖D.cauchyAdjoint M r‖ := L.adjoint.le_opNorm _
      _ ≤ 1 * ‖D.cauchyAdjoint M r‖ := by gcongr; simpa using hL
      _ = _ := one_mul _
  rw [hdiag, heq, D.mean_adjoint M hswap]
  nlinarith [norm_nonneg (L.adjoint (D.cauchyAdjoint M r)),
    norm_nonneg (D.cauchyAdjoint M r)]

include hJ0 hJ1 in
lemma opposite_adjoint_orthogonal (M : E →L[ℂ] E)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M)
    (r : E) (hr : D.proj 0 r = 0) :
    inner ℂ (D.cauchyAdjoint M r) (J (D.cauchyAdjoint M (J r))) = 0 := by
  have hpos : D.proj 1 (D.cauchyAdjoint M r) = D.cauchyAdjoint M r := by
    have h := D.nonnegative_decompose (D.cauchyAdjoint M r)
      (D.negative_adjoint M hswap r)
    simpa only [D.mean_adjoint M hswap, hr, zero_add] using h
  have hjr : D.proj 0 (J r) = 0 := by rw [← hJ0, hr]; simp
  have hjpos : D.proj 1 (D.cauchyAdjoint M (J r)) = D.cauchyAdjoint M (J r) := by
    have h := D.nonnegative_decompose (D.cauchyAdjoint M (J r))
      (D.negative_adjoint M hswap (J r))
    simpa only [D.mean_adjoint M hswap, hjr, zero_add] using h
  have hneg : D.proj 2 (J (D.cauchyAdjoint M (J r))) =
      J (D.cauchyAdjoint M (J r)) := by rw [← hJ1, hjpos]
  conv_lhs => lhs; rw [← hpos]
  conv_lhs => rhs; rw [← hneg]
  exact D.orthogonal 1 2 (by decide) _ _

include hJ0 hJ1 in

theorem density_comparison_core (M L R : E →L[ℂ] E)
    (hM : ‖M‖ ≤ 1) (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M)
    (hmodL : (D.cauchy M).comp (L.comp (D.cauchy M)) = L.comp (D.cauchy M))
    (hmodR : (D.cauchy M).comp (R.comp (D.cauchy M)) = R.comp (D.cauchy M))
    (p q r : E) (hp : p = L.adjoint r) (hq : q = R.adjoint r)
    (hpJ : J p = p) (hqJ : J q = q) (hr : D.proj 0 r = 0)
    (hp0 : D.proj 0 p ≠ 0) (κ : ℝ) (hκ : 0 < κ)
    (hblock : 2 * ‖(κ : ℂ) • D.cauchyAdjoint M r +
        ((κ⁻¹ : ℝ) : ℂ) • J (D.cauchyAdjoint M (J r))‖ ^ 2 ≤
      ‖D.cauchyAdjoint M p + J (D.cauchyAdjoint M p)‖ ^ 2 +
      ‖D.cauchyAdjoint M q + J (D.cauchyAdjoint M q)‖ ^ 2) : κ ≤ 2 := by
  have hg : D.cauchyAdjoint M r ≠ 0 := by
    intro hz
    apply hp0
    have hc : D.cauchyAdjoint M p = 0 := by
      rw [hp, ← D.adjoint_module_apply M L hswap hmodL, hz]
      simp
    rw [← D.mean_adjoint M hswap p, hc]
    simp
  have hgp : 0 < ‖D.cauchyAdjoint M r‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hg)
  have hdiag1 := D.hermitian_diagonal_bound J hJ0 hJ1 M L hM hL hswap hmodL p r hp hpJ
  have hdiag2 := D.hermitian_diagonal_bound J hJ0 hJ1 M R hM hR hswap hmodR q r hq hqJ
  have hortho := D.opposite_adjoint_orthogonal J hJ0 hJ1 M hswap r hr
  have hscaled : inner ℂ ((κ : ℂ) • D.cauchyAdjoint M r)
      (((κ⁻¹ : ℝ) : ℂ) • J (D.cauchyAdjoint M (J r))) = 0 := by
    rw [inner_smul_left, inner_smul_right, hortho]
    simp
  rw [norm_sq_add_orthogonal _ _ hscaled] at hblock
  have hnorm : ‖(κ : ℂ) • D.cauchyAdjoint M r‖ ^ 2 =
      κ ^ 2 * ‖D.cauchyAdjoint M r‖ ^ 2 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ, mul_pow]
  rw [hnorm] at hblock
  have hmul : κ ^ 2 * ‖D.cauchyAdjoint M r‖ ^ 2 ≤
      4 * ‖D.cauchyAdjoint M r‖ ^ 2 := by
    nlinarith [sq_nonneg (‖((κ⁻¹ : ℝ) : ℂ) • J (D.cauchyAdjoint M (J r))‖)]
  have hs : κ ^ 2 ≤ 4 := le_of_mul_le_mul_right hmul hgp
  nlinarith

end FourierResolution
end

open MeasureTheory
attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_15
lemma scalarFourier_star_zero (u : CircleL2) :
    star (scalarFourier.proj 0 u) = scalarFourier.proj 0 (star u) := by
  apply circle_fourier_ext
  intro n
  rw [circle_fourier_star, scalarFourier_coefficient, scalarFourier_coefficient,
    circle_fourier_star]
  by_cases hn : n = 0
  · subst n; simp [frequencyPart]
  · have hneg : -n ≠ 0 := neg_ne_zero.mpr hn
    by_cases hp : 0 < n <;> by_cases hm : n < 0 <;>
      simp [frequencyPart, hn, hneg, hp, hm]

lemma scalarFourier_star_positive (u : CircleL2) :
    star (scalarFourier.proj 1 u) = scalarFourier.proj 2 (star u) := by
  apply circle_fourier_ext
  intro n
  rw [circle_fourier_star, scalarFourier_coefficient, scalarFourier_coefficient,
    circle_fourier_star]
  by_cases hn : n = 0
  · subst n; simp [frequencyPart]
  · have hneg : -n ≠ 0 := neg_ne_zero.mpr hn
    by_cases hp : 0 < n
    · have hm : ¬ n < 0 := by omega
      simp [frequencyPart, hn, hneg, hp, hm]
    · have hm : n < 0 := by omega
      simp [frequencyPart, hn, hneg, hp, hm]

variable {m : Type u_55} [Fintype m] [DecidableEq m]

lemma coordinate_matrixStar (i j : m) (u : MatrixCircleL2 (m := m)) :
    l2Coordinate (i,j) (l2Star u) = star (l2Coordinate (j,i) u) := by
  apply Lp.ext
  filter_upwards [l2Coordinate_ae (i,j) (l2Star u), l2Coordinate_ae (j,i) u,
    l2StarL_ae u, Lp.coeFn_star (l2Coordinate (j,i) u)] with t hl hr hs hc
  rw [hl, hc, Pi.star_apply, hr]
  change l2StarL u t (i,j) = _
  rw [hs]
  rfl

lemma coordinate_matrixFourier (j : Fin 3) (u : MatrixCircleL2 (m := m)) (i : m × m) :
    l2Coordinate i (matrixFourier.proj j u) = scalarFourier.proj j (l2Coordinate i u) :=
  coordinate_entrywise _ _ _

lemma matrixFourier_star_zero (u : MatrixCircleL2 (m := m)) :
    l2Star (matrixFourier.proj 0 u) = matrixFourier.proj 0 (l2Star u) := by
  apply l2Coordinate_injective
  rintro ⟨i,j⟩
  rw [coordinate_matrixStar, coordinate_matrixFourier, coordinate_matrixFourier,
    coordinate_matrixStar, scalarFourier_star_zero]

lemma matrixFourier_star_positive (u : MatrixCircleL2 (m := m)) :
    l2Star (matrixFourier.proj 1 u) = matrixFourier.proj 2 (l2Star u) := by
  apply l2Coordinate_injective
  rintro ⟨i,j⟩
  rw [coordinate_matrixStar, coordinate_matrixFourier, coordinate_matrixFourier,
    coordinate_matrixStar, scalarFourier_star_positive]

end

open MeasureTheory
local instance instFactLtRealOfNat_solutions_16 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
namespace AnalyticBidiskKernel
variable (K : AnalyticBidiskKernel)
variable {m : Type u_56} [Fintype m] [instDecidableEqM : DecidableEq m]

lemma matrixM_norm_le
    (K : CompleteCrouzeix.AnalyticBidiskKernel) {m : Type u_56} [Fintype m] [DecidableEq m] :
    ‖(K.matrixM : MatrixCircleL2 (m := m) →L[ℂ] _)‖ ≤ 1 :=
  K.toMarkovKernel.toCLM_norm_le

lemma coordinate_matrixM (u : MatrixCircleL2 (m := m)) (i : m × m) :
    l2Coordinate i (K.matrixM u) = K.scalarM (l2Coordinate i u) := by
  apply Lp.ext
  filter_upwards [K.toMarkovKernel.applyLp_ae (l2Coordinate i u),
    K.toMarkovKernel.applyLp_ae u, l2Coordinate_ae i (K.matrixM u)] with t h1 h2 h3
  rw [h3]
  change (K.toMarkovKernel.applyLp u t) i = K.toMarkovKernel.applyLp (l2Coordinate i u) t
  rw [h1,h2]
  unfold MarkovKernel.applyFun
  change (EuclideanSpace.proj (𝕜 := ℂ) i) (∫ y, K.toMarkovKernel.kernel t y • u y ∂AddCircle.haarAddCircle) = _
  rw [← (EuclideanSpace.proj (𝕜 := ℂ) i).integral_comp_comm
    (K.toMarkovKernel.integrable_row_smul u t)]
  apply integral_congr_ae
  filter_upwards [l2Coordinate_ae i u] with s hs
  rw [hs]
  rfl

lemma matrixM_swap : (K.matrixM : MatrixCircleL2 (m := m) →L[ℂ] _).comp
    (matrixFourier.proj 1) = (matrixFourier.proj 2).comp K.matrixM := by
  ext1 u
  apply l2Coordinate_injective
  intro i
  rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,
    coordinate_matrixM,coordinate_matrixFourier,coordinate_matrixFourier,coordinate_matrixM]
  exact congrArg (fun L : CircleL2 →L[ℂ] CircleL2 => L (l2Coordinate i u)) K.scalarM_swap

end AnalyticBidiskKernel
end

open Set Metric Complex MeasureTheory
open scoped Topology

end

open Set Metric Complex MeasureTheory
open scoped Topology

end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_HolomorphicEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix


universe u_61 u_62 u_63 u_64

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
section

variable {A : Type u_61} [Ring A] [Algebra ℂ A]

lemma scalarJetEval_add {f g : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) (hg : AnalyticAt ℂ g β) (N : A) (s : ℕ) :
    scalarJetEval β N s (fun z => f z + g z) =
      scalarJetEval β N s f + scalarJetEval β N s g := by
  unfold scalarJetEval
  simp only [iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt,
    add_div, add_smul, Finset.sum_add_distrib]

lemma scalarJetEval_const {N : A} {s : ℕ} (hs : N^s = 0) (β c : ℂ) :
    scalarJetEval β N s (fun _ => c) = algebraMap ℂ A c := by
  simpa using scalarJetEval_polynomial hs β (C c)

lemma scalarJetEval_pow {f : ℂ → ℂ} {β : ℂ} (hf : AnalyticAt ℂ f β)
    {N : A} {s : ℕ} (hs : N^s = 0) (k : ℕ) :
    scalarJetEval β N s (fun z => f z ^ k) = (scalarJetEval β N s f) ^ k := by
  induction k with
  | zero => simpa using scalarJetEval_const hs β 1
  | succ k ih =>
    simp only [pow_succ]
    rw [scalarJetEval_mul (hf.fun_pow k) hf hs, ih]

lemma scalarJetEval_polynomial_comp {f : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) {N : A} {s : ℕ} (hs : N^s = 0) (p : ℂ[X]) :
    scalarJetEval β N s (fun z => p.eval (f z)) =
      Polynomial.aeval (scalarJetEval β N s f) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add, map_add]
    rw [scalarJetEval_add ((AnalyticOnNhd.eval_polynomial p (f β) (Set.mem_univ _)).fun_comp hf) ((AnalyticOnNhd.eval_polynomial q (f β) (Set.mem_univ _)).fun_comp hf), hp, hq]
  | monomial k c =>
    simp only [Polynomial.eval_monomial, Polynomial.aeval_monomial]
    rw [scalarJetEval_mul (analyticAt_const ..) (hf.fun_pow k) hs,
      scalarJetEval_const hs, scalarJetEval_pow hf hs]

lemma analytic_first_order_remainder {f : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R β ∧ ∀ᶠ z in nhds β,
      f z - f β = (z-β)*R z := by
  obtain ⟨R, hR, he⟩ := analytic_taylor_remainder hf 1
  refine ⟨R, hR, ?_⟩
  filter_upwards [he] with z hz
  simpa [jetPolynomial_eval, sub_eq_iff_eq_add, add_comm] using hz

lemma scalarJetEval_nilpotent_part {f : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) {N : A} {s : ℕ} (hs : N^s = 0) :
    (scalarJetEval β N s f - algebraMap ℂ A (f β)) ^ s = 0 := by
  obtain ⟨R, hR, he⟩ := analytic_first_order_remainder hf
  have hzero : scalarJetEval β N s (fun z => (f z - f β)^s) =
      scalarJetEval β N s (fun _ => (0 : ℂ)) := by
    apply scalarJetEval_eq_of_remainder (by fun_prop) (analyticAt_const ..) (hR.fun_pow s)
    filter_upwards [he] with z hz
    rw [sub_zero, hz, mul_pow]
  rw [scalarJetEval_pow (by fun_prop) hs,
    scalarJetEval_sub hf (analyticAt_const ..), scalarJetEval_const hs,
    scalarJetEval_const hs, map_zero] at hzero
  exact hzero

lemma scalarJetEval_comp {f g : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) (hg : AnalyticAt ℂ g (f β))
    {N : A} {s : ℕ} (hs : N^s = 0) :
    scalarJetEval β N s (fun z => g (f z)) =
      scalarJetEval (f β) (scalarJetEval β N s f - algebraMap ℂ A (f β)) s g := by
  let p := jetPolynomial (f β) s g
  obtain ⟨R, hR, he⟩ := analytic_taylor_remainder hg s
  obtain ⟨S, hS, hj⟩ := analytic_first_order_remainder hf
  have hRp : AnalyticAt ℂ (fun z => S z ^ s * R (f z)) β :=
    (hS.fun_pow s).fun_mul (hR.fun_comp hf)
  have hpoly : scalarJetEval β N s (fun z => g (f z)) =
      scalarJetEval β N s (fun z => p.eval (f z)) := by
    apply scalarJetEval_eq_of_remainder (hg.fun_comp hf) ((AnalyticOnNhd.eval_polynomial p (f β) (Set.mem_univ _)).fun_comp hf) hRp
    filter_upwards [hf.continuousAt.eventually he, hj] with z hz hw
    change g (f z) = p.eval (f z) + (f z-f β)^s * R (f z) at hz
    rw [hz, hw, mul_pow]
    ring
  rw [hpoly, scalarJetEval_polynomial_comp hf hs,
    scalarJetEval_taylor hg (scalarJetEval_nilpotent_part hf hs), sub_add_cancel]

end

open Module Set
open scoped DirectSum
variable {V : Type u_63} [AddCommGroup V] [Module ℂ V] [instFiniteDimensionalℂV : FiniteDimensional ℂ V]

lemma scalarJetEval_intertwine
    {V : Type u_63} [AddCommGroup V] [_root_.Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type u_64} [AddCommGroup W] [Module ℂ W]
    (L : W →ₗ[ℂ] V) (S : Module.End ℂ W) (T : Module.End ℂ V)
    (h : ∀ x, T (L x) = L (S x)) (β : ℂ) (s : ℕ) (f : ℂ → ℂ) (x : W) :
    scalarJetEval β T s f (L x) = L (scalarJetEval β S s f x) := by
  have hp (k : ℕ) (x : W) : (T^k) (L x) = L ((S^k) x) := by
    induction k generalizing x with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, h,
        pow_succ', Module.End.mul_apply]
  simp only [scalarJetEval, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, hp]

lemma primaryEval_on_generalized (T : Module.End ℂ V) (f : ℂ → ℂ)
    (β : ℂ) (x : T.maxGenEigenspace β) :
    primaryEval T f (x : V) =
      scalarJetEval β (T - algebraMap ℂ (Module.End ℂ V) β) (finrank ℂ V) f (x : V) := by
  rw [primaryEval_coe]
  exact (scalarJetEval_intertwine (T.maxGenEigenspace β).subtype
    (primaryNilpotent T β) (T - algebraMap ℂ (Module.End ℂ V) β)
    (fun _ => rfl) β (finrank ℂ V) f x).symm

lemma primaryEval_mapsTo_generalized (T : Module.End ℂ V) {f : ℂ → ℂ}
    (β : ℂ) (hf : AnalyticAt ℂ f β) :
    MapsTo (T.maxGenEigenspace β).subtype Set.univ
      ((primaryEval T f).maxGenEigenspace (f β)) := by
  intro x _
  change (x : V) ∈ (primaryEval T f).maxGenEigenspace (f β)
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
    Module.End.mem_genEigenspace_nat, LinearMap.mem_ker]
  have hp (k : ℕ) (x : T.maxGenEigenspace β) :
      ((primaryEval T f - algebraMap ℂ (Module.End ℂ V) (f β))^k) (x : V) =
        (((scalarJetEval β (primaryNilpotent T β) (finrank ℂ V) f -
          algebraMap ℂ (Module.End ℂ (T.maxGenEigenspace β)) (f β))^k) x : V) := by
    induction k generalizing x with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, LinearMap.sub_apply,
        primaryEval_coe, pow_succ', Module.End.mul_apply]
      rfl
  have he := hp (finrank ℂ V) x
  rw [scalarJetEval_nilpotent_part hf (primaryNilpotent_pow T β)] at he
  simpa only [Algebra.algebraMap_eq_smul_one,
    LinearMap.zero_apply, Submodule.coe_zero] using he

lemma primaryEval_comp (T : Module.End ℂ V) {f g : ℂ → ℂ}
    (hf : ∀ β ∈ spectrum ℂ T, AnalyticAt ℂ f β)
    (hg : ∀ β ∈ spectrum ℂ T, AnalyticAt ℂ g (f β)) :
    primaryEval T (fun z => g (f z)) = primaryEval (primaryEval T f) g := by
  apply primary_end_ext (T := T)
  intro β x
  by_cases hβ : β ∈ spectrum ℂ T
  · have hx : (x : V) ∈ (primaryEval T f).maxGenEigenspace (f β) :=
      primaryEval_mapsTo_generalized T β (hf β hβ) (by trivial : x ∈ Set.univ)
    rw [primaryEval_coe, primaryEval_on_generalized (primaryEval T f) g (f β) ⟨x, hx⟩]
    rw [scalarJetEval_comp (hf β hβ) (hg β hβ) (primaryNilpotent_pow T β)]
    symm
    apply scalarJetEval_intertwine (T.maxGenEigenspace β).subtype
    intro y
    change primaryEval T f (y : V) - (f β) • (y : V) = _
    rw [primaryEval_coe]
    rfl
  · have hspace : T.maxGenEigenspace β = ⊥ := by
      by_contra hn
      have he : T.HasGenEigenvalue β (finrank ℂ V) := by
        rwa [T.maxGenEigenspace_eq_genEigenspace_finrank β] at hn
      exact hβ (Module.End.hasEigenvalue_of_hasGenEigenvalue he).mem_spectrum
    have hx : x = 0 := by
      apply Subtype.ext
      simpa [hspace] using x.property
    simp [hx]


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_DiskCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_65 u_66 u_67 u_68 u_69 u_70 u_71 u_72 u_73 u_74 u_75 u_76 u_77 u_78 u_79 u_80

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset

section
open Filter Topology Set Module
variable {n : Type u_67} [Fintype n] [DecidableEq n]

lemma matrixAnalyticEval_polynomial (A : Matrix n n ℂ) (p : ℂ[X]) :
    matrixAnalyticEval A (fun z => p.eval z) = Polynomial.aeval A p := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [matrixAnalyticEval, AlgEquiv.apply_symm_apply, primaryEval_polynomial,
    Polynomial.aeval_algHom_apply]

end

open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

open MeasureTheory
variable {n : Type u_73} [instFintypeN : Fintype n] [instDecidableEqN : DecidableEq n]

open scoped Kronecker

variable {m : Type u_74} [instFintypeM : Fintype m] [instDecidableEqM : DecidableEq m]

lemma matrix_integral_entry {X : Type u_75} [MeasurableSpace X] {μ : Measure X}
    {L : X → Matrix n n ℂ} (hL : Integrable L μ) (i j : n) :
    (∫ t, L t ∂μ) i j = ∫ t, L t i j ∂μ :=
  ((entryCLM i j).integral_comp_comm hL).symm

lemma continuous_kron
    {n : Type u_73} [Fintype n] [DecidableEq n] {m : Type u_74} [Fintype m] [DecidableEq m]
    {X : Type u_80} [TopologicalSpace X]
    {L : X → Matrix n n ℂ} {F : X → Matrix m m ℂ}
    (hL : Continuous L) (hF : Continuous F) : Continuous (fun t => L t ⊗ₖ F t) := by
  apply continuous_matrix
  intro i j
  exact ((entryCLM i.1 j.1).continuous.comp hL).mul
    ((entryCLM i.2 j.2).continuous.comp hF)


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_CompleteResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_81 u_82 u_83 u_84 u_85 u_86 u_87 u_88 u_89 u_90

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

section
open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker

variable {n : Type u_86} {m : Type u_87} [Fintype n] [DecidableEq n] [instFintypeM : Fintype m] [instDecidableEqM : DecidableEq m]

lemma matrixAnalyticEval_id (D : Matrix n n ℂ) :
    matrixAnalyticEval D (fun z => z) = D := by
  simpa using matrixAnalyticEval_polynomial D (Polynomial.X : ℂ[X])

lemma completeAnalyticEval_const
    {n : Type u_86} {m : Type u_87} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (D : Matrix n n ℂ) (C : Matrix m m ℂ) :
    completeAnalyticEval D (fun _ => C) = (1 : Matrix n n ℂ) ⊗ₖ C := by
  ext i j
  simp only [completeAnalyticEval, matrixAnalyticEval_const, Algebra.algebraMap_eq_smul_one,
    Matrix.smul_apply, smul_eq_mul, Matrix.kroneckerMap_apply]
  ring

end

open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker
variable {n : Type u_89} {m : Type u_90} [Fintype n] [DecidableEq n] [instFintypeM : Fintype m] [instDecidableEqM : DecidableEq m]

lemma completeAnalyticEval_eqOn
    {n : Type u_89} {m : Type u_90} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (D : Matrix n n ℂ) {F G : ℂ → Matrix m m ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hDU : spectrum ℂ D ⊆ U) (he : EqOn F G U) :
    completeAnalyticEval D F = completeAnalyticEval D G := by
  ext i j
  unfold completeAnalyticEval
  apply congrArg (fun M : Matrix n n ℂ => M i.1 j.1)
  apply matrixAnalyticEval_eventuallyEq
  intro z hz
  filter_upwards [hU.mem_nhds (hDU hz)] with w hw
  rw [he hw]

lemma matrix_entry_analytic {f : ℂ → Matrix m m ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (i j : m) : AnalyticAt ℂ (fun w => f w i j) z := by
  let L : Matrix m m ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => M i j, map_add' := by intros; rfl, map_smul' := by intros; rfl }
  exact (L.toContinuousLinearMap.analyticAt (f z)).comp hf


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_PolynomialCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_91 u_92 u_93 u_94 u_95 u_96 u_97 u_98 u_99 u_100 u_101 u_102 u_103 u_104 u_105 u_106 u_107

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

section
open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker
variable {n : Type u_96} {m : Type u_97} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma matrixAnalyticEval_comp (A : Matrix n n ℂ) {f g : ℂ → ℂ}
    (hf : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ f z)
    (hg : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ g (f z)) :
    matrixAnalyticEval A (fun z => g (f z)) = matrixAnalyticEval (matrixAnalyticEval A f) g := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [matrixAnalyticEval, AlgEquiv.apply_symm_apply]
  exact primaryEval_comp _ (fun z hz => hf z (by simpa using hz))
    (fun z hz => hg z (by simpa using hz))

lemma completeAnalyticEval_comp
    {n : Type u_96} {m : Type u_97} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (A : Matrix n n ℂ) {f : ℂ → ℂ} {F : ℂ → Matrix m m ℂ}
    (hf : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ f z)
    (hF : ∀ i j, ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ (fun w => F w i j) (f z)) :
    completeAnalyticEval A (fun z => F (f z)) = completeAnalyticEval (matrixAnalyticEval A f) F := by
  ext i j
  simp only [completeAnalyticEval]
  rw [matrixAnalyticEval_comp A hf (hF _ _)]

end

open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_CauchyEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_108 u_109 u_110 u_111 u_112 u_113 u_114 u_115

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

section IntegralJets
open MeasureTheory Set Metric Complex Filter
open scoped Topology
variable {α : Type u_108} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
  [BorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]

lemma cauchyJet_hasDerivAt
    {α : Type u_108} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
    (s v : α → ℂ) (k : ℕ) {z : ℂ} {t : α}
    (hn : s t ≠ z) :
    HasDerivAt (fun w => cauchyJet s v k w t) (cauchyJet s v (k+1) z t) z := by
  have he := (hasDerivAt_const z ((k.factorial : ℂ)*v t)).div
    (((hasDerivAt_id z).const_sub (s t)).pow (k+1))
    (pow_ne_zero _ (sub_ne_zero.mpr hn))
  convert he using 1 <;> try rfl
  change ((k+1).factorial : ℂ)*v t/(s t-z)^(k+1+1) = _
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  simp only [id_eq, zero_mul, mul_neg_one, zero_sub]
  simp only [Pi.pow_apply, Nat.add_sub_cancel, pow_succ]
  field_simp

lemma cauchyJet_continuousOn
    {α : Type u_108} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
    {s v : α → ℂ} (hs : Continuous s) (hv : Continuous v)
    {U : Set ℂ} (hne : ∀ z ∈ U, ∀ t, s t ≠ z) (k : ℕ) :
    ContinuousOn (Function.uncurry (cauchyJet s v k)) (U ×ˢ univ) := by
  exact (continuous_const.mul (hv.comp continuous_snd)).continuousOn.div
    (((hs.comp continuous_snd).continuousOn.sub continuousOn_fst).pow (k+1))
    (fun p hp => pow_ne_zero _ (sub_ne_zero.mpr (hne p.1 hp.1 p.2)))

lemma cauchyJet_integrable {s v : α → ℂ} (hs : Continuous s) (hv : Continuous v)
    {z : ℂ} (hne : ∀ t, s t ≠ z) (k : ℕ) :
    Integrable (cauchyJet s v k z) μ := by
  exact ((continuous_const.mul hv).div ((hs.sub continuous_const).pow (k+1))
    (fun t => pow_ne_zero _ (sub_ne_zero.mpr (hne t)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma iteratedDeriv_cauchyIntegral {s v : α → ℂ} (hs : Continuous s) (hv : Continuous v)
    {U : Set ℂ} (hU : IsOpen U) (hne : ∀ z ∈ U, ∀ t, s t ≠ z) (k : ℕ)
    {z : ℂ} (hz : z ∈ U) :
    iteratedDeriv k (fun w => ∫ t, v t/(s t-w) ∂μ) z = ∫ t, cauchyJet s v k z t ∂μ := by
  induction k generalizing z with
  | zero => simp [cauchyJet]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k (fun w => ∫ t, v t/(s t-w) ∂μ) =ᶠ[nhds z]
        fun w => ∫ t, cauchyJet s v k w t ∂μ :=
      Filter.Eventually.mono (hU.mem_nhds hz) fun w hw => ih hw
    rw [he.deriv_eq]
    exact (compact_parametric_hasDerivAt hU (cauchyJet_continuousOn hs hv hne k)
      (cauchyJet_continuousOn hs hv hne (k+1))
      (fun w hw t => cauchyJet_hasDerivAt s v k (hne w hw t)) hz).deriv

lemma iteratedDeriv_cauchyKernel (s v : α → ℂ) (k : ℕ) {z : ℂ} {t : α}
    (hne : s t ≠ z) :
    iteratedDeriv k (fun w => v t/(s t-w)) z = cauchyJet s v k z t := by
  induction k generalizing z with
  | zero => simp [cauchyJet]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k (fun w => v t/(s t-w)) =ᶠ[nhds z]
        fun w => cauchyJet s v k w t :=
      Filter.Eventually.mono (isClosed_singleton.isOpen_compl.mem_nhds (show z ∈ ({s t} : Set ℂ)ᶜ from
        fun h => hne h.symm)) fun w hw => ih (fun h => hw h.symm)
    rw [he.deriv_eq]
    exact (cauchyJet_hasDerivAt s v k hne).deriv

end IntegralJets

section
open MeasureTheory Set Filter Module
open scoped Topology Matrix.Norms.L2Operator
variable {α : Type u_109} [MeasurableSpace α] {μ : Measure α}
  {n : Type u_110} [Fintype n] [DecidableEq n]

lemma matrix_integral_mulVec {F : α → Matrix n n ℂ} (hF : Integrable F μ) (x : n → ℂ) :
    (∫ t, F t ∂μ) *ᵥ x = ∫ t, F t *ᵥ x ∂μ := by
  let L : Matrix n n ℂ →L[ℂ] (n → ℂ) :=
    (show Matrix n n ℂ →ₗ[ℂ] (n → ℂ) from
      { toFun := fun B => B *ᵥ x
        map_add' := fun B C => Matrix.add_mulVec B C x
        map_smul' := fun c B => Matrix.smul_mulVec c B x }).toContinuousLinearMap
  exact (L.integral_comp_comm hF).symm

lemma matrixAnalyticEval_integral (A : Matrix n n ℂ) {F : ℂ → α → ℂ}
    (hi : Integrable (fun t => matrixAnalyticEval A (fun z => F z t)) μ)
    (hj : ∀ β ∈ spectrum ℂ A, ∀ k < Fintype.card n,
      Integrable (fun t => iteratedDeriv k (fun z => F z t) β) μ)
    (hd : ∀ β ∈ spectrum ℂ A, ∀ k < Fintype.card n,
      iteratedDeriv k (fun z => ∫ t, F z t ∂μ) β =
        ∫ t, iteratedDeriv k (fun z => F z t) β ∂μ) :
    matrixAnalyticEval A (fun z => ∫ t, F z t ∂μ) =
      ∫ t, matrixAnalyticEval A (fun z => F z t) ∂μ := by
  apply Matrix.toLinAlgEquiv'.injective
  apply primary_end_ext_spectrum (T := Matrix.toLinAlgEquiv' A)
  intro β hβ x
  have hb : β ∈ spectrum ℂ A := by simpa only [AlgEquiv.spectrum_eq] using hβ
  have he (f : ℂ → ℂ) :
      Matrix.toLinAlgEquiv' (matrixAnalyticEval A f) (x : n → ℂ) =
        ∑ k ∈ Finset.range (Fintype.card n),
          (iteratedDeriv k f β / (k.factorial : ℂ)) •
          (((primaryNilpotent (Matrix.toLinAlgEquiv' A) β)^k) x : n → ℂ) := by
    simp only [matrixAnalyticEval, AlgEquiv.apply_symm_apply, primaryEval_coe,
      scalarJetEval, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sum, Submodule.coe_smul]
    simp
  rw [he, Matrix.toLinAlgEquiv'_apply, matrix_integral_mulVec hi]
  simp_rw [← Matrix.toLinAlgEquiv'_apply,he]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [hd β hb k (Finset.mem_range.mp hk),integral_smul_const,integral_div]
  · intro k hk
    exact ((hj β hb k (Finset.mem_range.mp hk)).div_const _).smul_const _

lemma matrixAnalyticEval_resolvent (A : Matrix n n ℂ) {s : ℂ}
    (hs : s ∉ spectrum ℂ A) :
    matrixAnalyticEval A (fun z => (s-z)⁻¹) = (s • (1 : Matrix n n ℂ)-A)⁻¹ := by
  have hn (z : ℂ) (hz : z ∈ spectrum ℂ A) : s-z ≠ 0 :=
    sub_ne_zero.mpr (fun h => hs (h ▸ hz))
  have hf (z : ℂ) (_ : z ∈ spectrum ℂ A) : AnalyticAt ℂ (fun z => s-z) z :=
    analyticAt_const.sub analyticAt_id
  have hg (z : ℂ) (hz : z ∈ spectrum ℂ A) : AnalyticAt ℂ (fun z => (s-z)⁻¹) z :=
    (hf z hz).inv (hn z hz)
  have he : matrixAnalyticEval A (fun _ => 1) =
      matrixAnalyticEval A (fun z => (s-z)⁻¹*(s-z)) := by
    apply matrixAnalyticEval_eventuallyEq
    intro z hz
    filter_upwards [(hf z hz).continuousAt.eventually_ne (hn z hz)] with w hw
    exact (inv_mul_cancel₀ hw).symm
  rw [matrixAnalyticEval_const, map_one, matrixAnalyticEval_mul A hg hf,
    matrixAnalyticEval_sub A (f := fun _ => s) (g := fun z => z)
      (fun _ _ => analyticAt_const) (fun _ _ => analyticAt_id),
    matrixAnalyticEval_const,matrixAnalyticEval_id,Algebra.algebraMap_eq_smul_one] at he
  exact (Matrix.inv_eq_left_inv he.symm).symm

lemma matrixAnalyticEval_cauchyKernel (A : Matrix n n ℂ) {s : ℂ}
    (hs : s ∉ spectrum ℂ A) (v : ℂ) :
    matrixAnalyticEval A (fun z => v/(s-z)) = v • (s • (1 : Matrix n n ℂ)-A)⁻¹ := by
  have hg : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ (fun z => (s-z)⁻¹) z := by
    intro z hz
    have hn : s ≠ z := fun h => hs (h ▸ hz)
    exact (analyticAt_const.sub analyticAt_id).inv (sub_ne_zero.mpr hn)
  simp_rw [div_eq_mul_inv]
  rw [matrixAnalyticEval_mul A (fun _ _ => analyticAt_const) hg,
    matrixAnalyticEval_const,matrixAnalyticEval_resolvent A hs]
  simp only [Algebra.smul_def]

end

section
open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator
variable {α : Type u_111} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
  [BorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  {n : Type u_112} [Fintype n] [DecidableEq n]

theorem matrix_cauchy_integral_evaluation (A : Matrix n n ℂ)
    {s v : α → ℂ} (hs : Continuous s) (hv : Continuous v)
    {U : Set ℂ} (hU : IsOpen U) (hAU : spectrum ℂ A ⊆ U)
    (hne : ∀ z ∈ U, ∀ t, s t ≠ z) :
    matrixAnalyticEval A (fun z => ∫ t, v t/(s t-z) ∂μ) =
      ∫ t, v t • (s t • (1 : Matrix n n ℂ)-A)⁻¹ ∂μ := by
  have hn (t : α) : s t ∉ spectrum ℂ A := fun h => hne _ (hAU h) t rfl
  have he (t : α) := matrixAnalyticEval_cauchyKernel A (hn t) (v t)
  have hi : Integrable (fun t => matrixAnalyticEval A (fun z => v t/(s t-z))) μ := by
    simp_rw [he]
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    apply hv.smul
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (matrix_resolvent_analytic A (hn t)).continuousAt.comp hs.continuousAt
  rw [matrixAnalyticEval_integral A hi]
  · exact integral_congr_ae (Filter.Eventually.of_forall he)
  · intro β hβ k _
    have hd : (fun t => iteratedDeriv k (fun z => v t/(s t-z)) β) = cauchyJet s v k β :=
      funext fun t => iteratedDeriv_cauchyKernel s v k (hne β (hAU hβ) t)
    rw [hd]
    exact cauchyJet_integrable hs hv (hne β (hAU hβ)) k
  · intro β hβ k _
    rw [iteratedDeriv_cauchyIntegral hs hv hU hne k (hAU hβ)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
      (iteratedDeriv_cauchyKernel s v k (hne β (hAU hβ) t)).symm)

end

open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker
variable {α : Type u_113} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
  [BorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  {n : Type u_114} {m : Type u_115} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem complete_cauchy_integral_evaluation (A : Matrix n n ℂ)
    {s v : α → ℂ} (hs : Continuous s) (hv : Continuous v)
    {B : α → Matrix m m ℂ} (hB : Continuous B)
    {U : Set ℂ} (hU : IsOpen U) (hAU : spectrum ℂ A ⊆ U)
    (hne : ∀ z ∈ U, ∀ t, s t ≠ z) :
    completeAnalyticEval A (fun z i j => ∫ t, v t*B t i j/(s t-z) ∂μ) =
      ∫ t, (v t • (s t • (1 : Matrix n n ℂ)-A)⁻¹) ⊗ₖ B t ∂μ := by
  have hn (t : α) : s t ∉ spectrum ℂ A := fun h => hne _ (hAU h) t rfl
  have hrc := hv.smul (matrix_resolvent_continuous A hs hn)
  have hbc (i j : m) : Continuous (fun t => B t i j) := (entryCLM i j).continuous.comp hB
  have hri : Integrable (fun t => (v t • (s t • (1 : Matrix n n ℂ)-A)⁻¹) ⊗ₖ B t) μ := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    apply continuous_matrix
    intro i j
    change Continuous (fun t => (v t • (s t • (1 : Matrix n n ℂ)-A)⁻¹) i.1 j.1 * B t i.2 j.2)
    exact ((entryCLM i.1 j.1).continuous.comp hrc).mul (hbc i.2 j.2)
  ext i j
  dsimp only [completeAnalyticEval]
  have he := matrix_cauchy_integral_evaluation (μ := μ) A (s := s) (v := fun t => v t*B t i.2 j.2) hs (hv.mul (hbc i.2 j.2)) hU hAU hne
  rw [he,
    matrix_integral_entry hri]
  have ht : Integrable (fun t => (v t*B t i.2 j.2) • (s t • (1 : Matrix n n ℂ)-A)⁻¹) μ :=
    ((hv.mul (hbc i.2 j.2)).smul (matrix_resolvent_continuous A hs hn)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [matrix_integral_entry ht]
  apply integral_congr_ae
  filter_upwards [] with t
  change (v t*B t i.2 j.2) * (s t • (1 : Matrix n n ℂ)-A)⁻¹ i.1 j.1 =
    (v t*(s t • (1 : Matrix n n ℂ)-A)⁻¹ i.1 j.1)*B t i.2 j.2
  ring


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_BoundaryRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix


universe u_116 u_117 u_118 u_119 u_120 u_121 u_122 u_123 u_124 u_125 u_126 u_127 u_128 u_129 u_130 u_131 u_132 u_133 u_134 u_135 u_136 u_137 u_138 u_139 u_140 u_141 u_142 u_143 u_144 u_145 u_146 u_147 u_148 u_149 u_150 u_151 u_152 u_153

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset


open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder


open Set Filter Metric Complex
open scoped Topology ComplexConjugate

open MeasureTheory Set Complex
open scoped Topology Real

open MeasureTheory Set Complex
open scoped Topology

open MeasureTheory Set Complex Metric
open scoped Topology

section
open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder
variable {n : Type u_150} {m : Type u_151} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma boundaryDiskDensity_nonneg {D : Matrix n n ℂ} (hD : spectralRadius ℂ D < 1)
    (hc : Dᴴ*D ≤ 1) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ boundaryDiskDensity D z := by
  let E : Matrix n n ℂ := 1-z⁻¹ • D
  let R : Matrix n n ℂ := E⁻¹
  have hu : IsUnit E := stable_disk_inverse_isUnit hD (by simp [norm_inv, hz])
  have hER : E*R = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det E).mp hu)
  have hzz : star z⁻¹ * z⁻¹ = 1 := by
    change conj z⁻¹ * z⁻¹ = 1
    rw [RCLike.conj_mul, norm_inv, hz]
    norm_num
  have hdef : Eᴴ+E-Eᴴ*E = 1-Dᴴ*D := by
    dsimp [E]
    simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,Matrix.conjTranspose_smul]
    simp only [sub_mul,mul_sub,Matrix.one_mul,Matrix.mul_one,Matrix.smul_mul,Matrix.mul_smul,
      smul_smul,mul_comm z⁻¹ (star z⁻¹),hzz,one_smul]
    abel
  have hcong : Rᴴ*(1-Dᴴ*D)*R = boundaryDiskDensity D z := by
    rw [← hdef]
    have hs := congrArg Matrix.conjTranspose hER
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_one] at hs
    change Rᴴ*(Eᴴ+E-Eᴴ*E)*R = R+Rᴴ-1
    calc
      _ = (Rᴴ*Eᴴ)*R + Rᴴ*(E*R) - (Rᴴ*Eᴴ)*(E*R) := by noncomm_ring
      _ = _ := by rw [hs,hER]; simp
  rw [← hcong]
  exact (Matrix.PosSemidef.conjTranspose_mul_mul_same
    (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hc)) R).nonneg

lemma coordinate_circle_cauchy {ψ H : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (sphere 0 1))
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1)
    (hH : AnalyticOnNhd ℂ H (closedBall 0 1))
    (hmass : ∀ z ∈ ball (0:ℂ) 1,
      (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
        (ψ (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1)
    {z : ℂ} (hz : z ∈ ball (0:ℂ) 1) :
    (∫ t : UnitAddCircle, ((t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
      (ψ (t.toCircle : ℂ)-z))*H (ψ (t.toCircle : ℂ))
        ∂AddCircle.haarAddCircle) = H z := by
  apply circle_convex_cauchy (convex_closedBall (0:ℂ) 1) hH hψ
    (fun t ht => by simpa [mem_closedBall] using (hb t ht).le)
    (ball_subset_closedBall hz) _ (hmass z hz)
  intro t ht he
  have hh := hb t ht
  rw [he] at hh
  have hz' : ‖z‖ < 1 := by simpa using hz
  exact (ne_of_lt hz') hh

end

open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder
variable {n : Type u_152} {m : Type u_153} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma coordinate_circle_cauchy_matrix {ψ : ℂ → ℂ} {J : ℂ → Matrix n n ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (sphere 0 1))
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1)
    (hJ : ∀ i j, AnalyticOnNhd ℂ (fun z => J z i j) (closedBall 0 1))
    (hmass : ∀ z ∈ ball (0:ℂ) 1,
      (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
        (ψ (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1) :
    (∫ t : UnitAddCircle,
      ((t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/ψ (t.toCircle : ℂ)) •
        J (ψ (t.toCircle : ℂ)) ∂AddCircle.haarAddCircle) = J 0 := by
  have ht (t : UnitAddCircle) : (t.toCircle : ℂ) ∈ sphere (0:ℂ) 1 := by simp [Circle.norm_coe]
  have hc : Continuous (fun t : UnitAddCircle => (t.toCircle : ℂ)) := by fun_prop
  have hψc := hψ.continuousOn.comp_continuous hc ht
  have hψd := hψ.deriv.continuousOn.comp_continuous hc ht
  have hjc : Continuous (fun t : UnitAddCircle =>
      (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/ψ (t.toCircle : ℂ)) :=
    (hc.mul hψd).div hψc (fun t => norm_ne_zero_iff.mp (by rw [hb _ (ht t)]; norm_num))
  have hJc : Continuous (fun t : UnitAddCircle => J (ψ (t.toCircle : ℂ))) := by
    apply continuous_matrix
    intro i j
    exact (hJ i j).continuousOn.comp_continuous hψc
      (fun t => by simpa [mem_closedBall] using (hb _ (ht t)).le)
  have hi := (hjc.smul hJc).integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  ext i j
  erw [matrix_integral_entry hi]
  convert! coordinate_circle_cauchy hψ hb (hJ i j) hmass (z := 0) (by simp) using 1
  apply integral_congr_ae
  filter_upwards [] with t
  change (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/ψ (t.toCircle : ℂ) *
      J (ψ (t.toCircle : ℂ)) i j =
    (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/(ψ (t.toCircle : ℂ)-0) *
      J (ψ (t.toCircle : ℂ)) i j
  rw [sub_zero]

theorem complete_pulled_disk_representation {D : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) {ψ : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (sphere 0 1))
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1)
    (hmass : ∀ z ∈ ball (0:ℂ) 1,
      (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
        (ψ (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1)
    {H : ℂ → Matrix m m ℂ}
    (hH : ∀ i j, AnalyticOnNhd ℂ (fun z => H z i j) (closedBall 0 1)) :
    (∫ t : UnitAddCircle,
      (((t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/ψ (t.toCircle : ℂ)) •
        boundaryDiskDensity D (ψ (t.toCircle : ℂ))) ⊗ₖ
          H (ψ (t.toCircle : ℂ)) ∂AddCircle.haarAddCircle) = completeAnalyticEval D H := by
  let c : UnitAddCircle → ℂ := fun t => (t.toCircle : ℂ)
  let s : UnitAddCircle → ℂ := fun t => ψ (c t)
  let v : UnitAddCircle → ℂ := fun t => c t*deriv ψ (c t)
  let j : UnitAddCircle → ℂ := fun t => v t/s t
  have ht (t : UnitAddCircle) : c t ∈ sphere (0:ℂ) 1 := by simp [c, Circle.norm_coe]
  have hc : Continuous c := by dsimp [c]; fun_prop
  have hs : Continuous s := hψ.continuousOn.comp_continuous hc ht
  have hv : Continuous v := hc.mul (hψ.deriv.continuousOn.comp_continuous hc ht)
  have hsn (t : UnitAddCircle) : s t ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [show ‖s t‖ = 1 from hb _ (ht t)]; norm_num)
  have hj : Continuous j := hv.div hs hsn
  have hsb (t : UnitAddCircle) : s t ∈ closedBall (0:ℂ) 1 := by
    simpa [mem_closedBall] using (hb _ (ht t)).le
  have hHc : Continuous (fun t => H (s t)) := by
    apply continuous_matrix
    intro a b
    exact (hH a b).continuousOn.comp_continuous hs hsb
  have hspec : spectrum ℂ D ⊆ ball (0:ℂ) 1 := fun z hz => by
    simpa using stable_spectrum_norm_lt_one hD hz
  have hne (z : ℂ) (hz : z ∈ ball (0:ℂ) 1) (t : UnitAddCircle) : s t ≠ z := by
    intro he
    have hh : ‖s t‖ = 1 := hb _ (ht t)
    rw [he] at hh
    have hz' : ‖z‖ < 1 := by simpa using hz
    exact (ne_of_lt hz') hh
  let K : UnitAddCircle → Matrix (n × m) (n × m) ℂ :=
    fun t => (v t • (s t • (1 : Matrix n n ℂ)-D)⁻¹) ⊗ₖ H (s t)
  let B : UnitAddCircle → Matrix (n × m) (n × m) ℂ :=
    fun t => j t • ((1-s t • Dᴴ)⁻¹ ⊗ₖ H (s t))
  let C : UnitAddCircle → Matrix (n × m) (n × m) ℂ :=
    fun t => j t • ((1 : Matrix n n ℂ) ⊗ₖ H (s t))
  have hKc : Continuous K := continuous_kron
    (hv.smul (matrix_resolvent_continuous D hs (fun t hz => hne _ (hspec hz) t rfl))) hHc
  have hR : AnalyticOnNhd ℂ (fun z : ℂ => (1-z • Dᴴ)⁻¹) (closedBall 0 1) := by
    intro z hz
    exact scalar_matrix_inverse_analytic (stable_star_disk_inverse_isUnit hD (by simpa using hz))
  have hBc : Continuous B := hj.smul (continuous_kron
    (hR.continuousOn.comp_continuous hs hsb) hHc)
  have hCc : Continuous C := hj.smul (continuous_kron continuous_const hHc)
  have hKi := hKc.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have hBi := hBc.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have hCi := hCc.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have hKe : (∫ t, K t ∂AddCircle.haarAddCircle) = completeAnalyticEval D H := by
    rw [← complete_cauchy_integral_evaluation D hs hv hHc isOpen_ball hspec hne]
    apply completeAnalyticEval_eqOn D isOpen_ball hspec
    intro z hz
    ext a b
    have he := coordinate_circle_cauchy hψ hb (hH a b) hmass hz
    convert he using 1
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp [v,s,c]
    ring
  have hBe : (∫ t, B t ∂AddCircle.haarAddCircle) = (1 : Matrix n n ℂ) ⊗ₖ H 0 := by
    have he := coordinate_circle_cauchy_matrix hψ hb
      (J := fun z => (1-z • Dᴴ)⁻¹ ⊗ₖ H z)
      (fun a b z hz => (matrix_entry_analytic (hR z hz) a.1 b.1).mul (hH a.2 b.2 z hz)) hmass
    simpa only [B,j,v,s,c,zero_smul,sub_zero,inv_one] using he
  have hCe : (∫ t, C t ∂AddCircle.haarAddCircle) = (1 : Matrix n n ℂ) ⊗ₖ H 0 := by
    exact coordinate_circle_cauchy_matrix hψ hb
      (J := fun z => (1 : Matrix n n ℂ) ⊗ₖ H z)
      (fun a b z hz => analyticAt_const.mul (hH a.2 b.2 z hz)) hmass
  calc
    _ = ∫ t, (K t+B t-C t) ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [boundaryDiskDensity_eq hD (hb _ (ht t))]
      change (j t • (s t • (s t • (1 : Matrix n n ℂ)-D)⁻¹ +
        (1-s t • Dᴴ)⁻¹-1)) ⊗ₖ H (s t) = K t+B t-C t
      dsimp [K,B,C,j]
      ext ⟨a₁,a₂⟩ ⟨b₁,b₂⟩
      simp only [Matrix.kronecker_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.add_apply, Matrix.sub_apply]
      field_simp [hsn t]
    _ = completeAnalyticEval D H := by
      erw [integral_sub (hKi.add hBi) hCi, integral_add hKi hBi, hKe,hBe,hCe]
      abel


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_PulledDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_154 u_155 u_156

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Complex
open scoped Topology
open MeasureTheory Set Complex Metric
open scoped Topology

section
open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder
variable {n : Type u_154} [Fintype n] [DecidableEq n]

lemma pulledDiskDensity_nonneg {D : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) (hDc : Dᴴ*D ≤ 1) {ψ : ℂ → ℂ}
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1)
    (hj : ∀ t ∈ sphere (0:ℂ) 1, 0 ≤ t*deriv ψ t/ψ t) (t : UnitAddCircle) :
    0 ≤ pulledDiskDensity D ψ t := by
  have ht : (t.toCircle : ℂ) ∈ sphere (0:ℂ) 1 := by simp [Circle.norm_coe]
  exact ((Matrix.nonneg_iff_posSemidef.mp (boundaryDiskDensity_nonneg hD hDc (hb _ ht))).smul
    (hj _ ht)).nonneg

theorem pulledDiskDensity_mass {D : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) {ψ : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (sphere 0 1))
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1)
    (hmass : ∀ z ∈ ball (0:ℂ) 1,
      (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
        (ψ (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1) :
    (∫ t : UnitAddCircle, pulledDiskDensity D ψ t ∂AddCircle.haarAddCircle) = 1 := by
  have he := complete_pulled_disk_representation (m := Unit) hD hψ hb hmass
    (H := fun _ => (1 : Matrix Unit Unit ℂ)) (fun _ _ _ _ => analyticAt_const)
  rw [completeAnalyticEval_const] at he
  have hc := pulledDiskDensity_continuous hD hψ hb
  have hi := hc.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle)
    (HasCompactSupport.of_compactSpace _)
  have hkc : Continuous (fun t : UnitAddCircle =>
      (pulledDiskDensity D ψ t) ⊗ₖ (1 : Matrix Unit Unit ℂ)) :=
    continuous_kron hc continuous_const
  have hki := hkc.integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  change (∫ t : UnitAddCircle, (pulledDiskDensity D ψ t) ⊗ₖ (1 : Matrix Unit Unit ℂ)
    ∂AddCircle.haarAddCircle) = (1 : Matrix n n ℂ) ⊗ₖ (1 : Matrix Unit Unit ℂ) at he
  ext i j
  have hh := congrArg (fun M : Matrix (n × Unit) (n × Unit) ℂ => M (i,()) (j,())) he
  erw [matrix_integral_entry hki] at hh
  erw [matrix_integral_entry hi]
  simpa only [Matrix.kronecker_apply, Matrix.one_apply_eq, mul_one] using hh

end

open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder
variable {n : Type u_155} {m : Type u_156} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem interior_coordinate_exterior_representation (A : Matrix n n ℂ)
    {f g ψ G : ℂ → ℂ} {v : ℂ → Matrix m m ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hAU : spectrum ℂ A ⊆ U)
    (hf : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ f z)
    (hfd : ∀ z ∈ spectrum ℂ A, f z ∈ closedBall (0:ℂ) 1)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 1))
    (hgf : ∀ z ∈ U, g (f z) = z)
    (hv : AnalyticOnNhd ℂ v (g '' closedBall 0 1))
    (hD : spectralRadius ℂ (matrixAnalyticEval A f) < 1)
    (hψ : AnalyticOnNhd ℂ ψ (sphere 0 1))
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1)
    (hgb : ∀ t ∈ sphere (0:ℂ) 1, g (ψ t) = G t)
    (hmass : ∀ z ∈ ball (0:ℂ) 1,
      (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
        (ψ (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1) :
    completeAnalyticEval A v =
      ∫ t : UnitAddCircle, pulledDiskDensity (matrixAnalyticEval A f) ψ t ⊗ₖ
        v (G (t.toCircle : ℂ)) ∂AddCircle.haarAddCircle := by
  have hvg : AnalyticOnNhd ℂ (fun z => v (g z)) (closedBall 0 1) := by
    intro z hz
    exact (hv (g z) ⟨z,hz,rfl⟩).comp (hg z hz)
  have he : completeAnalyticEval A v =
      completeAnalyticEval (matrixAnalyticEval A f) (fun z => v (g z)) := by
    rw [← completeAnalyticEval_comp A hf
      (F := fun z => v (g z)) (fun i j z hz => matrix_entry_analytic (hvg (f z) (hfd z hz)) i j)]
    apply completeAnalyticEval_eqOn A hU hAU
    intro z hz
    change v z = v (g (f z))
    rw [hgf z hz]
  rw [he, ← complete_pulled_disk_representation hD hψ hb hmass
    (fun i j z hz => matrix_entry_analytic (hvg z hz) i j)]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [hgb _ (by simp [Circle.norm_coe])]
  rfl


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_OptimalExtremal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_188 u_189 u_190

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators Matrix.Norms.L2Operator
open Set Filter Metric Topology
open Set Filter Metric Topology
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder Pointwise
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

open Filter Topology Set Metric
open scoped Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder
variable {n : Type u_190} [Fintype n] [DecidableEq n] [Nonempty n]

lemma spectrum_matrix_similarity
    {n : Type u_190} [Fintype n] [DecidableEq n] [Nonempty n]
    {S : Matrix n n ℂ} (hS : IsUnit S) (T : Matrix n n ℂ) :
    spectrum ℂ (S*T*S⁻¹) = spectrum ℂ T := by
  rw [← hS.unit_spec, ← Matrix.coe_units_inv]
  exact spectrum.units_conjugate


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_DilationDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix


universe u_191 u_192 u_193 u_194 u_195 u_196 u_197 u_198 u_199 u_200 u_201 u_202 u_203 u_204 u_205 u_206 u_207 u_208 u_209 u_210 u_211 u_212 u_213 u_214

open MeasureTheory
open scoped ENNReal

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Kronecker

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
section
variable {n : Type u_206} {m : Type u_207} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

lemma weightedDensity_star
    {n : Type u_206} {m : Type u_207} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (L : Matrix n n ℂ) (X Y : Matrix n m ℂ) :
    (weightedDensity L X Y)ᴴ = weightedDensity Lᴴ Y X := by
  simp only [weightedDensity, Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

lemma weightedDensity_block_pos {L : Matrix n n ℂ} (hL : L.PosSemidef)
    (X Y : Matrix n m ℂ) :
    (Matrix.fromBlocks (weightedDensity L X X) (weightedDensity L X Y)ᴴ
      (weightedDensity L X Y) (weightedDensity L Y Y)).PosSemidef := by
  have hp := (hL.conjTranspose_mul_mul_same (Matrix.fromCols X Y)).transpose
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols, Matrix.fromBlocks_transpose] at hp
  rw [weightedDensity_star, hL.isHermitian.eq]
  exact hp

lemma integral_weightedDensity {T : Type u_208} [MeasurableSpace T] {μ : Measure T}
    {L : T → Matrix n n ℂ} (hL : Integrable L μ) (X Y : Matrix n m ℂ) :
    (∫ t, weightedDensity (L t) X Y ∂μ) = weightedDensity (∫ t, L t ∂μ) X Y :=
  (weightedDensityCLM X Y).integral_comp_comm hL

lemma weightedDensity_mean {T : Type u_209} [MeasurableSpace T] {μ : Measure T}
    {L : T → Matrix n n ℂ} (hL : Integrable L μ) (hmass : ∫ t, L t ∂μ = 1)
    (X Y : Matrix n m ℂ) :
    (∫ t, weightedDensity (L t) X Y ∂μ) = (Xᴴ*Y)ᵀ := by
  rw [integral_weightedDensity hL, hmass, weightedDensity, Matrix.mul_one]

lemma weightedDensity_mean_zero {T : Type u_210} [MeasurableSpace T] {μ : Measure T}
    {L : T → Matrix n n ℂ} (hL : Integrable L μ) (hmass : ∫ t, L t ∂μ = 1)
    {X Y : Matrix n m ℂ} (hXY : Xᴴ*Y = 0) :
    (∫ t, weightedDensity (L t) X Y ∂μ) = 0 := by
  rw [weightedDensity_mean hL hmass, hXY, Matrix.transpose_zero]

lemma trace_weightedDensity_one
    {n : Type u_206} {m : Type u_207} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (X : Matrix n m ℂ) :
    (weightedDensity 1 X X).trace = (‖vectorize X‖ ^ 2 : ℝ) := by
  simp only [weightedDensity, Matrix.mul_one, Matrix.trace, Matrix.diag_apply, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, vectorize]
  rw [Finset.sum_comm]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (starRingEnd ℂ) (X j i) * X j i = (‖X j i‖ : ℂ)^2
  rw [← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm]
  simp

end

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
variable {T : Type u_212} [TopologicalSpace T] [CompactSpace T] [SecondCountableTopology T]
  [MeasurableSpace T] [BorelSpace T] {μ : Measure T} [IsFiniteMeasure μ]
  {n : Type u_213} {m : Type u_214} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem actual_density_means
    {T : Type u_212} [TopologicalSpace T] [CompactSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T] {μ : MeasureTheory.Measure T}
    [MeasureTheory.IsFiniteMeasure μ] {n : Type u_213} {m : Type u_214} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (L : C(T,Matrix n n ℂ))
    (hmass : (∫ t, L t ∂μ) = 1) {X Y : Matrix n m ℂ}
    (hx : ‖vectorize X‖ = 1) (hXY : Xᴴ*Y = 0) :
    (∫ t, weightedDensity (L t) X Y ∂μ) = 0 ∧
    (∫ t, weightedDensity (L t) X X ∂μ).trace = 1 := by
  have hi : Integrable (fun t => L t) μ :=
    L.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨weightedDensity_mean_zero hi hmass hXY, ?_⟩
  rw [integral_weightedDensity hi, hmass, trace_weightedDensity_one, hx]
  norm_num


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_DensityTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


universe u_215 u_216 u_217 u_218 u_219 u_220 u_221 u_222 u_223 u_224 u_225 u_226 u_227 u_228 u_229 u_230 u_231 u_232 u_233 u_234 u_235 u_236 u_237 u_238 u_239 u_240

open Set Filter Metric Complex
open scoped Topology ComplexConjugate

open MeasureTheory Set Complex
open scoped Topology Real

open MeasureTheory Set Metric Complex Filter
open scoped Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace

open scoped ComplexConjugate InnerProductSpace

open Set Metric Filter Complex
open scoped Topology


open MeasureTheory Set Complex
open scoped Topology

open MeasureTheory Set Complex Metric
open scoped Topology

open Set Filter Metric Complex
open scoped Topology


open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator


open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
open MeasureTheory

namespace CompleteCrouzeix

section
open MeasureTheory
open scoped Matrix.Norms.L2Operator Kronecker ComplexConjugate InnerProductSpace
variable {T : Type u_236} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
  [BorelSpace T] {μ : Measure T} [IsFiniteMeasure μ]
  {n : Type u_237} {m : Type u_238} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma densityField_ae (L : C(T,Matrix n n ℂ)) (X Y : Matrix n m ℂ) :
    densityField (μ := μ) L X Y =ᵐ[μ]
      fun t => toHS (weightedDensity (L t) X Y) :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ _

end

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate Matrix.Norms.L2Operator Kronecker
variable {m : Type u_239} {n : Type u_240} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_52
lemma hsTraceLp_ae
    {m : Type u_239} [Fintype m] [DecidableEq m] (u : C(UnitAddCircle,Matrix m m ℂ)) :
    hsTraceLp u =ᵐ[AddCircle.haarAddCircle] fun t => toHS (u t) :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle _

end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_ConformalJacobian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open Set Filter Metric Complex
open scoped Topology ComplexConjugate InnerProductSpace
namespace CompleteCrouzeix

lemma circle_log_derivative_real {ψ : ℂ → ℂ} {t : ℂ}
    (ht : ‖t‖ = 1) (hψ : DifferentiableAt ℂ ψ t)
    (hb : ∀ z : ℂ, ‖z‖ = 1 → ‖ψ z‖ = 1) :
    (t*deriv ψ t/ψ t).im = 0 := by
  have hp : ‖ψ t‖ = 1 := hb t ht
  have hd (s : ℝ) : HasDerivAt (fun s : ℝ => exp ((s:ℂ)*I)*t)
      (exp ((s:ℂ)*I)*I*t) s := by
    simpa using (((hasDerivAt_id s).ofReal_comp.mul_const I).cexp.mul_const t)
  have he : HasDerivAt (fun s : ℝ => ψ (exp ((s:ℂ)*I)*t))
      (I*t*deriv ψ t) 0 := by
    simpa only [ofReal_zero, zero_mul, exp_zero, one_mul, Function.comp_def,
      smul_eq_mul] using (show HasDerivAt ψ (deriv ψ t) (exp (((0:ℝ):ℂ)*I)*t) from by simpa using hψ.hasDerivAt).scomp 0 (hd 0)
  have hn : (fun s : ℝ => ‖ψ (exp ((s:ℂ)*I)*t)‖^2) = fun _ => (1:ℝ) := by
    funext s
    rw [hb _ (by rw [norm_mul, norm_exp_ofReal_mul_I, ht, one_mul]), one_pow]
  have heq := he.norm_sq
  rw [hn] at heq
  have hz := heq.unique (hasDerivAt_const (0:ℝ) (1:ℝ))
  have hi : inner ℝ (ψ t) (I*t*deriv ψ t) = -(conj (ψ t)*(t*deriv ψ t)).im := by
    rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply']
    change (conj (ψ t)*(I*t*deriv ψ t)).re = _
    rw [show conj (ψ t)*(I*t*deriv ψ t) = I*(conj (ψ t)*(t*deriv ψ t)) by ring]
    simp
  simp only [ofReal_zero, zero_mul, exp_zero, one_mul] at hz
  rw [hi] at hz
  have hconj : (ψ t)⁻¹ = conj (ψ t) := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hp]
    simp
  rw [div_eq_mul_inv, hconj, mul_comm (t*deriv ψ t)]
  linarith

lemma circle_log_derivative_nonneg {ψ : ℂ → ℂ} {t : ℂ}
    (_ht : ‖t‖ = 1) (hψ : DifferentiableAt ℂ ψ t)
    (hb : ‖ψ t‖ = 1)
    (hin : ∀ᶠ r : ℝ in 𝓝[Iic 1] 1, ‖ψ ((r:ℂ)*t)‖ ≤ 1) :
    0 ≤ (t*deriv ψ t/ψ t).re := by
  have hd : HasDerivAt (fun r : ℝ => (r:ℂ)*t) t 1 := by
    simpa using (hasDerivAt_id (1:ℝ)).ofReal_comp.mul_const t
  have he : HasDerivAt (fun r : ℝ => ψ ((r:ℂ)*t)) (t*deriv ψ t) 1 := by
    simpa only [ofReal_one, one_mul, Function.comp_def, smul_eq_mul] using
      (show HasDerivAt ψ (deriv ψ t) (((1:ℝ):ℂ)*t) from by simpa using hψ.hasDerivAt).scomp 1 hd
  have hm : IsLocalMaxOn (fun r : ℝ => ‖ψ ((r:ℂ)*t)‖^2) (Iic 1) 1 := by
    filter_upwards [hin] with r hr
    simpa only [ofReal_one, one_mul, hb, one_pow] using
      (pow_le_pow_left₀ (norm_nonneg _) hr 2)
  have hy : (-1:ℝ) ∈ posTangentConeAt (Iic (1:ℝ)) 1 := by
    apply mem_posTangentConeAt_of_segment_subset
    apply (convex_Iic (1:ℝ)).segment_subset <;> simp
  have hh := hm.hasFDerivWithinAt_nonpos he.norm_sq.hasFDerivAt.hasFDerivWithinAt hy
  simp only [ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, ofReal_one, one_mul] at hh
  have hi : inner ℝ (ψ t) (t*deriv ψ t) = (conj (ψ t)*(t*deriv ψ t)).re := by
    rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply']; rfl
  rw [hi] at hh
  have hconj : (ψ t)⁻¹ = conj (ψ t) := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hb]
    simp
  rw [div_eq_mul_inv, hconj, mul_comm (t*deriv ψ t)]
  linarith

end CompleteCrouzeix

end

end
end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_ConformalWinding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix


open Set Filter Metric Complex
open scoped Topology ComplexConjugate

open MeasureTheory Set Complex
open scoped Topology Real

open MeasureTheory Set Complex
open scoped Topology

open MeasureTheory Set Complex Metric
open scoped Topology

attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_54
lemma circle_convex_integral_zero {K : Set ℂ} (hK : Convex ℝ K)
    {J G : ℂ → ℂ} (hJ : AnalyticOnNhd ℂ J K)
    (hG : AnalyticOnNhd ℂ G (sphere 0 1))
    (hcurve : MapsTo G (sphere 0 1) K) {a : ℂ} (ha : a ∈ K)
    (hne : ∀ t ∈ sphere (0:ℂ) 1, G t ≠ a)
    (hmass : (∫ t : UnitAddCircle,
      (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ) / (G (t.toCircle : ℂ)-a)
        ∂AddCircle.haarAddCircle) = 1) :
    (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)*
      J (G (t.toCircle : ℂ)) ∂AddCircle.haarAddCircle) = 0 := by
  have hF : AnalyticOnNhd ℂ (fun z => (z-a)*J z) K := by
    intro z hz; exact (analyticAt_id.sub analyticAt_const).mul (hJ z hz)
  have he := circle_convex_cauchy hK hF hG hcurve ha hne hmass
  simpa only [sub_self, zero_mul] using
    (show (∫ t : UnitAddCircle,
      (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)*J (G (t.toCircle : ℂ))
        ∂AddCircle.haarAddCircle) = (a-a)*J a from by
      calc
        _ = ∫ t : UnitAddCircle,
          ((t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)/(G (t.toCircle : ℂ)-a))*
            ((G (t.toCircle : ℂ)-a)*J (G (t.toCircle : ℂ)))
              ∂AddCircle.haarAddCircle := by
          apply integral_congr_ae
          filter_upwards [] with t
          have ht : (t.toCircle : ℂ) ∈ sphere (0:ℂ) 1 := by
            simp [Circle.norm_coe]
          field_simp [sub_ne_zero.mpr (hne _ ht)]
        _ = _ := he)

lemma logarithmic_dslope_derivative {f : ℂ → ℂ} {a z : ℂ}
    (hfa : f z ≠ f a) (hza : z ≠ a) (hf : DifferentiableAt ℂ f z) :
    deriv f z / (f z-f a) = 1/(z-a) + deriv (dslope f a) z / dslope f a z := by
  have hd : deriv (dslope f a) z =
      (deriv f z*(z-a)-(f z-f a))/(z-a)^2 := by
    rw [(dslope_eventuallyEq_slope_of_ne f hza).deriv_eq]
    rw [show slope f a = (fun w => (f w-f a)/(w-a)) from
      funext (fun w => slope_def_field f a w)]
    simpa only [Pi.div_apply, id_eq, mul_one] using
      ((hf.hasDerivAt.sub_const (f a)).fun_div
        ((hasDerivAt_id z).sub_const a) (sub_ne_zero.mpr hza)).deriv
  rw [hd, dslope_of_ne _ hza, slope_def_field]
  field_simp
  ring

theorem conformal_circle_mass {K V : Set ℂ} (hK : Convex ℝ K)
    (hV : IsOpen V) (hKV : K ⊆ V) {f G : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f V) (hfi : InjOn f V)
    (hG : AnalyticOnNhd ℂ G (sphere 0 1))
    (hcurve : MapsTo G (sphere 0 1) K) {a : ℂ} (ha : a ∈ K)
    (hfa : deriv f a ≠ 0)
    (hne : ∀ t ∈ sphere (0:ℂ) 1, G t ≠ a)
    (hmass : (∫ t : UnitAddCircle,
      (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ) / (G (t.toCircle : ℂ)-a)
        ∂AddCircle.haarAddCircle) = 1) :
    (∫ t : UnitAddCircle,
      (t.toCircle : ℂ)*deriv (f ∘ G) (t.toCircle : ℂ) /
        (f (G (t.toCircle : ℂ))-f a) ∂AddCircle.haarAddCircle) = 1 := by
  let J : ℂ → ℂ := fun z => deriv (dslope f a) z / dslope f a z
  have hq := analyticOnNhd_dslope hV hf (hKV ha)
  have hJ : AnalyticOnNhd ℂ J K := by
    intro z hz
    exact (hq.deriv z (hKV hz)).div (hq z (hKV hz))
      (dslope_ne_zero_of_injOn hfi (hKV ha) (hKV hz) hfa)
  have hz := circle_convex_integral_zero hK hJ hG hcurve ha hne hmass
  have ht (t : UnitAddCircle) : (t.toCircle : ℂ) ∈ sphere (0:ℂ) 1 := by
    simp [Circle.norm_coe]
  have htc : Continuous (fun t : UnitAddCircle => (t.toCircle : ℂ)) :=
    by fun_prop
  have hgc : Continuous (fun t : UnitAddCircle => G (t.toCircle : ℂ)) :=
    hG.continuousOn.comp_continuous htc ht
  have hdgc : Continuous (fun t : UnitAddCircle => deriv G (t.toCircle : ℂ)) :=
    hG.deriv.continuousOn.comp_continuous htc ht
  have h₁ : Integrable (fun t : UnitAddCircle =>
      (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)/(G (t.toCircle : ℂ)-a))
        AddCircle.haarAddCircle :=
    ((htc.mul hdgc).div (hgc.sub continuous_const)
      (fun t => sub_ne_zero.mpr (hne _ (ht t)))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h₂ : Integrable (fun t : UnitAddCircle =>
      (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)*J (G (t.toCircle : ℂ)))
        AddCircle.haarAddCircle :=
    ((htc.mul hdgc).mul
      (hJ.continuousOn.comp_continuous hgc (fun t => hcurve (ht t)))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ t : UnitAddCircle,
      ((t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)/(G (t.toCircle : ℂ)-a) +
        (t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)*J (G (t.toCircle : ℂ)))
          ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with t
      have he : f (G (t.toCircle : ℂ)) ≠ f a :=
        fun he => hne _ (ht t) (hfi (hKV (hcurve (ht t))) (hKV ha) he)
      rw [deriv_comp _ (hf _ (hKV (hcurve (ht t)))).differentiableAt
        (hG _ (ht t)).differentiableAt]
      have heq := logarithmic_dslope_derivative he (hne _ (ht t))
        (hf _ (hKV (hcurve (ht t)))).differentiableAt
      change _ = _ + _*J _
      dsimp [J]
      linear_combination ((t.toCircle : ℂ)*deriv G (t.toCircle : ℂ))*heq
    _ = 1 := by rw [integral_add h₁ h₂, hmass, hz, add_zero]


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_ResolventPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexConjugate InnerProductSpace
namespace CompleteCrouzeix

lemma eigenvalue_mem_numericalRange {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    {z : ℂ} {x : EuclideanSpace ℂ (Fin n)} (hx : x ≠ 0)
    (he : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A x = z • x) :
    z ∈ numericalRange A := by
  let y := (‖x‖⁻¹ : ℝ) • x
  have hy : ‖y‖ = 1 := by simp [y, norm_smul, norm_ne_zero_iff.mpr hx]
  have he' : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A y = z • y := by
    simp [y, ContinuousLinearMap.map_smul_of_tower, he, smul_comm (‖x‖⁻¹ : ℝ) z]
  refine ⟨y, hy, ?_⟩
  rw [he', inner_smul_right, inner_self_eq_norm_sq_to_K, hy]
  simp

theorem spectrum_subset_numericalRange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    spectrum ℂ A ⊆ numericalRange A := by
  intro z hz
  have hz' : z ∈ spectrum ℂ A.toLin' := by simpa using hz
  obtain ⟨v,hv⟩ := (Module.End.HasEigenvalue.of_mem_spectrum hz').exists_hasEigenvector
  let x : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 v
  apply eigenvalue_mem_numericalRange (x := x)
  · simpa [x] using hv.2
  · change WithLp.toLp 2 (A.toLin' v) = z • WithLp.toLp 2 v
    rw [hv.apply_eq_smul]
    rfl

lemma isUnit_resolvent_of_not_mem_numericalRange {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} {z : ℂ} (hz : z ∉ numericalRange A) :
    IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ) - A) := by
  have hs : z ∉ spectrum ℂ A := fun h => hz (spectrum_subset_numericalRange A h)
  simpa only [spectrum, resolventSet, Set.mem_compl_iff, Set.mem_ofPred_eq,
    not_not, Algebra.algebraMap_eq_smul_one] using hs

lemma posSemidef_of_unit_quadratic {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian)
    (hq : ∀ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 →
      0 ≤ (inner ℂ x (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) H x)).re) :
    H.PosSemidef := by
  apply Matrix.isPositive_toEuclideanLin_iff.mp
  refine ⟨Matrix.isSymmetric_toEuclideanLin_iff.mpr hH, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx]
  let y := (‖x‖⁻¹ : ℝ) • x
  have hy : ‖y‖ = 1 := by simp [y, norm_smul, norm_ne_zero_iff.mpr hx]
  have hxy : x = (‖x‖ : ℝ) • y := by
    simp [y, smul_smul, norm_ne_zero_iff.mpr hx]
  have h := hq y hy
  rw [inner_re_symm]
  change 0 ≤ (inner ℂ x (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) H x)).re
  rw [hxy, ContinuousLinearMap.map_smul_of_tower]
  simp only [inner_smul_left_eq_star_smul, inner_smul_right_eq_smul, starRingEnd_apply, star_trivial, Complex.smul_re, smul_eq_mul]
  exact mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) h)

lemma supporting_form_posSemidef {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {z N : ℂ}
    (hs : ∀ w ∈ numericalRange A, 0 ≤ (conj N * (z-w)).re) :
    (N • (z • (1 : Matrix (Fin n) (Fin n) ℂ)-A)ᴴ +
      conj N • (z • (1 : Matrix (Fin n) (Fin n) ℂ)-A)).PosSemidef := by
  let R := z • (1 : Matrix (Fin n) (Fin n) ℂ)-A
  apply posSemidef_of_unit_quadratic
  · change (N • Rᴴ + conj N • R).IsHermitian
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_conjTranspose, starRingEnd_apply, star_star]
    exact add_comm _ _
  · intro x hx
    let e := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
    have h := hs (inner ℂ x (e A x)) ⟨x,hx,rfl⟩
    have hr : inner ℂ x (e R x) = z-inner ℂ x (e A x) := by
      simp only [R, map_sub, map_smul, map_one, sub_apply,
        smul_apply, one_apply_eq_self,
        inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hx]
      simp
    change 0 ≤ (inner ℂ x (e (N • Rᴴ + conj N • R) x)).re
    have he : e Rᴴ = (e R).adjoint := map_star e R
    rw [map_add, map_smul, map_smul, add_apply,
      smul_apply, smul_apply,
      inner_add_right, inner_smul_right, inner_smul_right, he,
      ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm (e R x) x, hr]
    simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im] at *
    nlinarith

theorem supporting_resolvent_posSemidef {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    {z N : ℂ} (hz : z ∉ numericalRange A)
    (hs : ∀ w ∈ numericalRange A, 0 ≤ (conj N * (z-w)).re) :
    (N • (z • (1 : Matrix (Fin n) (Fin n) ℂ)-A)⁻¹ +
      (N • (z • (1 : Matrix (Fin n) (Fin n) ℂ)-A)⁻¹)ᴴ).PosSemidef := by
  let R := z • (1 : Matrix (Fin n) (Fin n) ℂ)-A
  have hu : IsUnit R := isUnit_resolvent_of_not_mem_numericalRange hz
  have h := (supporting_form_posSemidef hs).conjTranspose_mul_mul_same R⁻¹
  have hR : R*R⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det R).mp hu)
  have hRi : R⁻¹*R = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det R).mp hu)
  have hh : R⁻¹ᴴ*(N • Rᴴ + conj N • R)*R⁻¹ = N • R⁻¹ + (N • R⁻¹)ᴴ := by
    simp only [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc R⁻¹ᴴ Rᴴ R⁻¹, ← Matrix.conjTranspose_mul, hR,
      Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    simp only [Matrix.conjTranspose_smul, starRingEnd_apply]
  exact hh ▸ h

end CompleteCrouzeix

end

end
end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_DomainCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_244

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
lemma inverse_ψ {t : ℂ} (ht : t ∈ sphere (0:ℂ) 1) : D.interior.fromDisk (D.ψ t) = D.G t :=
  D.interior.left_inverse _ (D.interior.closure_subset (D.G_boundary ht).1)
lemma ψ_jacobian {t : ℂ} (ht : t ∈ sphere (0:ℂ) 1) :
    0 ≤ t*deriv D.ψ t/D.ψ t := by
  rw [Complex.nonneg_iff]
  refine ⟨circle_log_derivative_nonneg (mem_sphere_zero_iff_norm.mp ht)
    (D.ψ_analytic t ht).differentiableAt (D.ψ_boundary ht) ?_,
    (circle_log_derivative_real (mem_sphere_zero_iff_norm.mp ht)
    (D.ψ_analytic t ht).differentiableAt (fun z hz => D.ψ_boundary (mem_sphere_zero_iff_norm.mpr hz))).symm⟩
  have hi : D.exterior.radius⁻¹ < 1 := inv_lt_one_of_one_lt₀ D.exterior.radius_gt
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (lt_mem_nhds hi)] with r hr hri
  have hr0 : 0 < r := (inv_pos.mpr (zero_lt_one.trans D.exterior.radius_gt)).trans hri
  have hnorm : ‖(r:ℂ)*t‖ = r := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr0,mem_sphere_zero_iff_norm.mp ht,mul_one]
  change ‖D.interior.toDisk (D.G ((r:ℂ)*t))‖ ≤ 1
  apply mem_closedBall_zero_iff.mp (D.interior.closure_maps _)
  rcases lt_or_eq_of_le (show r ≤ 1 from hr) with hlt|rfl
  · exact subset_closure ((D.exterior.interior_iff _ (by simpa only [hnorm] using hri)).mpr
      (mem_ball_zero_iff.mpr (by simpa only [hnorm] using hlt)))
  · simpa only [ofReal_one,one_mul] using (D.G_boundary ht).1
lemma G_mass {z : ℂ} (hz : z ∈ D.domain) :
    (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv D.G (t.toCircle : ℂ) /
      (D.G (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1 := by
  apply exterior_cauchy_kernel_integral D.exterior.leading_ne
    (D.exterior.analytic_regular.mono (closedBall_subset_ball D.exterior.radius_gt))
  intro t ht
  exact D.G_ne_interior hz ht
lemma ψ_mass {z : ℂ} (hz : z ∈ ball (0:ℂ) 1) :
    (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv D.ψ (t.toCircle : ℂ) /
      (D.ψ (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1 := by
  have ha := D.interior.inverse_ball z hz
  have hfa := D.interior.right_inverse z (D.interior.closedDisk_subset (ball_subset_closedBall hz))
  have hm := conformal_circle_mass D.convex.closure D.interior.outer_open
    D.interior.closure_subset D.interior.analytic_to D.interior.injective_to D.G_analytic
    (fun t ht => (D.G_boundary ht).1) (subset_closure ha)
    (D.interior.noncritical_to _ (D.interior.closure_subset (subset_closure ha)))
    (fun t ht => D.G_ne_interior ha (mem_sphere_zero_iff_norm.mp ht).ge) (D.G_mass ha)
  simpa only [hfa,ψ,Function.comp_apply] using hm
end AdmissibleDomain

end CompleteCrouzeix

end

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_BoundaryCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_245 u_246

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
variable {n : Type u_245} {m : Type u_246} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
attribute [local instance] OAI.CompleteCrouzeix.AdmissibleDomain.instFactLtRealOfNat
lemma positive_representation [Nonempty n] (A : Matrix n n ℂ)
    (hA : spectrum ℂ A ⊆ D.domain) {v : ℂ → Matrix m m ℂ}
    (hv : AnalyticOnNhd ℂ v (closure D.domain)) :
    completeAnalyticEval A v = ∫ t : UnitAddCircle,
      pulledDiskDensity (matrixAnalyticEval A D.interior.toDisk) D.ψ t ⊗ₖ
        D.trace v hv t ∂AddCircle.haarAddCircle := by
  have hf (z : ℂ) (hz : z ∈ spectrum ℂ A) :=
    D.interior.analytic_to z (D.interior.closure_subset (subset_closure (hA hz)))
  apply interior_coordinate_exterior_representation A D.isOpen hA hf
    (fun z hz => ball_subset_closedBall (D.toDisk_maps (hA hz)))
    (D.interior.analytic_from.mono D.interior.closedDisk_subset)
    (fun z hz => D.interior.left_inverse z (D.interior.closure_subset (subset_closure hz)))
    (hv.mono (by rintro z ⟨w,hw,rfl⟩; exact D.interior.inverse_closed w hw))
    (matrixAnalyticEval_stable A hf (fun z hz => mem_ball_zero_iff.mp (D.toDisk_maps (hA hz))))
    D.ψ_analytic (fun _ ht => D.ψ_boundary ht) (fun _ ht => D.inverse_ψ ht) (fun _ hz => D.ψ_mass hz)
end AdmissibleDomain
end CompleteCrouzeix

end

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_DensityAdjoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_247 u_248

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
variable {n : Type u_247} {m : Type u_248} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_55
lemma densityField_star (L : C(UnitAddCircle,Matrix n n ℂ)) (hL : ∀ t, (L t).IsHermitian)
    (X Y : Matrix n m ℂ) :
    l2Star (densityField (μ := AddCircle.haarAddCircle) L X Y) = densityField L Y X := by
  apply Lp.ext
  filter_upwards [l2StarL_ae (densityField (μ := AddCircle.haarAddCircle) L X Y),
    densityField_ae (μ := AddCircle.haarAddCircle) L X Y,
    densityField_ae (μ := AddCircle.haarAddCircle) L Y X] with t hs hx hy
  change l2StarL (densityField L X Y) t = _
  rw [hs,hx,hy,hsStar_apply,fromHS_toHS,weightedDensity_star,(hL t).eq]
lemma hsTrace_mean_coefficient (u : C(UnitAddCircle,Matrix m m ℂ)) (ij : m × m) :
    fourierCoeff (l2Coordinate ij (hsTraceLp u)) 0 =
      (∫ t, u t ∂AddCircle.haarAddCircle) ij.1 ij.2 := by
  have hi := u.continuous.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle)
    (HasCompactSupport.of_compactSpace _)
  rw [matrix_integral_entry hi]
  simp only [fourierCoeff,neg_zero,fourier_zero,one_smul]
  apply integral_congr_ae
  filter_upwards [l2Coordinate_ae ij (hsTraceLp u),hsTraceLp_ae u] with t hc hu
  rw [hc,hu]
  rfl
lemma hsTrace_mean_zero_iff (u : C(UnitAddCircle,Matrix m m ℂ)) :
    matrixFourier.proj 0 (hsTraceLp u) = 0 ↔ (∫ t, u t ∂AddCircle.haarAddCircle) = 0 := by
  constructor
  · intro hz
    ext i j
    have hh := congrArg (fun v : MatrixCircleL2 (m := m) => fourierCoeff (l2Coordinate (i,j) v) 0) hz
    rw [coordinate_matrixFourier,scalarFourier_coefficient] at hh
    simp only [frequencyPart,hsTrace_mean_coefficient] at hh
    simpa [fourierCoeff] using hh
  · intro hz
    apply l2Coordinate_injective
    intro ij
    apply circle_fourier_ext
    intro k
    rw [coordinate_matrixFourier,scalarFourier_coefficient]
    by_cases hk : k = 0
    · subst k
      rw [show frequencyPart 0 = 0 from rfl,ite_eq_left rfl,hsTrace_mean_coefficient,hz]
      simp [fourierCoeff]
    · have hn : frequencyPart k ≠ 0 := by
        simp only [frequencyPart,ite_eq_right hk]
        split_ifs <;> decide
      simp [hn,fourierCoeff]
lemma densityField_mean_zero (L : C(UnitAddCircle,Matrix n n ℂ)) (X Y : Matrix n m ℂ)
    (h : (∫ t, weightedDensity (L t) X Y ∂AddCircle.haarAddCircle) = 0) :
    matrixFourier.proj 0 (densityField (μ := AddCircle.haarAddCircle) L X Y) = 0 := by
  let u : C(UnitAddCircle,Matrix m m ℂ) :=
    ⟨fun t => weightedDensity (L t) X Y,continuous_weightedDensity L.continuous X Y⟩
  change matrixFourier.proj 0 (hsTraceLp u) = 0
  exact (hsTrace_mean_zero_iff u).mpr h
lemma densityField_mean_nonzero (L : C(UnitAddCircle,Matrix n n ℂ)) (X : Matrix n m ℂ)
    (h : (∫ t, weightedDensity (L t) X X ∂AddCircle.haarAddCircle).trace = 1) :
    matrixFourier.proj 0 (densityField (μ := AddCircle.haarAddCircle) L X X) ≠ 0 := by
  intro hz
  let u : C(UnitAddCircle,Matrix m m ℂ) :=
    ⟨fun t => weightedDensity (L t) X X,continuous_weightedDensity L.continuous X X⟩
  change matrixFourier.proj 0 (hsTraceLp u) = 0 at hz
  have hh := (hsTrace_mean_zero_iff u).mp hz
  change (∫ t, weightedDensity (L t) X X ∂AddCircle.haarAddCircle) = 0 at hh
  rw [hh,Matrix.trace_zero] at h
  exact zero_ne_one h
lemma left_adjoint_of_ae {F : UnitAddCircle → Matrix m m ℂ}
    (L : MatrixCircleL2 (m := m) →L[ℂ] MatrixCircleL2 (m := m))
    (hL : ∀ u, L u =ᵐ[AddCircle.haarAddCircle] fun t => toHS (F t*fromHS (u t)))
    {p r : MatrixCircleL2 (m := m)}
    (hp : p =ᵐ[AddCircle.haarAddCircle] fun t => toHS ((F t)ᴴ*fromHS (r t))) :
    p = L.adjoint r := by
  apply ext_inner_right ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left,L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hp,hL u] with t hp hl
  rw [hp,hl]
  change inner ℂ (hsLeft (F t)ᴴ (r t)) (u t) = inner ℂ (r t) (hsLeft (F t) (u t))
  rw [← hsLeft_adjoint,ContinuousLinearMap.adjoint_inner_left]
lemma right_adjoint_of_ae {F : UnitAddCircle → Matrix m m ℂ}
    (R : MatrixCircleL2 (m := m) →L[ℂ] MatrixCircleL2 (m := m))
    (hR : ∀ u, R u =ᵐ[AddCircle.haarAddCircle] fun t => toHS (fromHS (u t)*F t))
    {q r : MatrixCircleL2 (m := m)}
    (hq : q =ᵐ[AddCircle.haarAddCircle] fun t => toHS (fromHS (r t)*(F t)ᴴ)) :
    q = R.adjoint r := by
  apply ext_inner_right ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left,L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hq,hR u] with t hq hr
  rw [hq,hr]
  change inner ℂ (hsRight (F t)ᴴ (r t)) (u t) = inner ℂ (r t) (hsRight (F t) (u t))
  rw [← hsRight_adjoint,ContinuousLinearMap.adjoint_inner_left]
end CompleteCrouzeix

end

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_PositiveDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u_253 u_254

namespace CompleteCrouzeix
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace AdmissibleDomain

section
variable (D : AdmissibleDomain)
variable {n : Type u_253} {m : Type u_254} [Fintype n] [DecidableEq n] [Nonempty n] [Fintype m] [DecidableEq m]
lemma positiveDensity_nonneg (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain)
    (hc : (matrixAnalyticEval A D.interior.toDisk)ᴴ * matrixAnalyticEval A D.interior.toDisk ≤ 1)
    (t : UnitAddCircle) : 0 ≤ D.positiveDensity A hA t :=
  pulledDiskDensity_nonneg (D.coordinate_stable A hA) hc
    (fun _ ht => D.ψ_boundary ht) (fun _ ht => D.ψ_jacobian ht) t
attribute [local instance] OAI.CompleteCrouzeix.AdmissibleDomain.instFactLtRealOfNat_2
lemma positiveDensity_mass (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain) :
    (∫ t, D.positiveDensity A hA t ∂AddCircle.haarAddCircle) = 1 :=
  pulledDiskDensity_mass (D.coordinate_stable A hA) D.ψ_analytic
    (fun _ ht => D.ψ_boundary ht) (fun _ hz => D.ψ_mass hz)
lemma positiveDensity_representation (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain)
    {v : ℂ → Matrix m m ℂ} (hv : AnalyticOnNhd ℂ v (closure D.domain)) :
    completeAnalyticEval A v = ∫ t, D.positiveDensity A hA t ⊗ₖ D.trace v hv t
      ∂AddCircle.haarAddCircle := D.positive_representation A hA hv
end
variable (D : AdmissibleDomain) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
lemma resolventField_posSemidef (hW : numericalRange A ⊆ D.domain) (t : UnitAddCircle) :
    (D.resolventField A t+(D.resolventField A t)ᴴ).PosSemidef := by
  apply supporting_resolvent_posSemidef
  · intro hz
    exact D.G_ne_interior (hW hz) (Circle.norm_coe t.toCircle).ge rfl
  · intro w hw
    exact D.support _ t.toCircle.2 w (subset_closure (hW hw))
end AdmissibleDomain
end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_OrderedDensities
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_255 u_256

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
variable {n : Type u_255} {m : Type u_256} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
attribute [local instance] OAI.CompleteCrouzeix.instFactLtRealOfNat_solutions_56
lemma densityField_block_bound (E : C(UnitAddCircle,Matrix n n ℂ))
    (hE : ∀ t, (E t).PosSemidef) (X Y : Matrix n m ℂ) :
    2 * ‖densityField (μ := AddCircle.haarAddCircle) E X Y‖^2 ≤
      ‖densityField (μ := AddCircle.haarAddCircle) E X X‖^2 +
      ‖densityField (μ := AddCircle.haarAddCircle) E Y Y‖^2 := by
  apply block_density_l2
  filter_upwards [densityField_ae (μ := AddCircle.haarAddCircle) E X X,
    densityField_ae (μ := AddCircle.haarAddCircle) E Y Y,
    densityField_ae (μ := AddCircle.haarAddCircle) E X Y] with t hp hq hr
  rw [hp,hq,hr,fromHS_toHS,fromHS_toHS,fromHS_toHS]
  exact weightedDensity_block_pos (hE t) X Y
lemma densityField_ordered_adjoints (Λ : C(UnitAddCircle,Matrix n n ℂ))
    (F : C(UnitAddCircle,Matrix m m ℂ)) (X Y : Matrix n m ℂ)
    (L R : MatrixCircleL2 (m := m) →L[ℂ] MatrixCircleL2 (m := m))
    (hL : ∀ u, L u =ᵐ[AddCircle.haarAddCircle] fun t => toHS (F t * fromHS (u t)))
    (hR : ∀ u, R u =ᵐ[AddCircle.haarAddCircle] fun t => toHS (fromHS (u t) * F t))
    (hord : ∀ᵐ t ∂AddCircle.haarAddCircle,
      weightedDensity (Λ t) X X = (F t)ᴴ * weightedDensity (Λ t) X Y ∧
      weightedDensity (Λ t) X Y = F t * weightedDensity (Λ t) X X ∧
      weightedDensity (Λ t) Y Y = weightedDensity (Λ t) X Y * (F t)ᴴ) :
    densityField (μ := AddCircle.haarAddCircle) Λ X X = L.adjoint (densityField Λ X Y) ∧
    densityField (μ := AddCircle.haarAddCircle) Λ Y Y = R.adjoint (densityField Λ X Y) := by
  constructor
  · apply left_adjoint_of_ae L hL
    filter_upwards [hord,densityField_ae (μ := AddCircle.haarAddCircle) Λ X X,
      densityField_ae (μ := AddCircle.haarAddCircle) Λ X Y] with t ho hp hr
    rw [hp,hr,fromHS_toHS,ho.1]
  · apply right_adjoint_of_ae R hR
    filter_upwards [hord,densityField_ae (μ := AddCircle.haarAddCircle) Λ Y Y,
      densityField_ae (μ := AddCircle.haarAddCircle) Λ X Y] with t ho hq hr
    rw [hq,hr,fromHS_toHS,ho.2.2]
end CompleteCrouzeix

end

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_DensityComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_257

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
local instance instFactLtRealOfNat_3 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {n m : ℕ} [Nonempty (Fin n)]
lemma cauchy_adjoint (m : Type u_257) [Fintype m] [DecidableEq m] :
    (D.cauchy (m := m)).adjoint = matrixFourier.cauchyAdjoint D.kernel.matrixM :=
  matrixFourier.adjoint_cauchy D.kernel.matrixM D.kernel.matrixM_swap

theorem extremal_condition_bound_oai (A : Matrix (Fin n) (Fin n) ℂ)
    (hW : numericalRange A ⊆ D.domain)
    {S : Matrix (Fin n) (Fin n) ℂ} (hS : S.IsHermitian) (hu : IsUnit S)
    (hc : (matrixAnalyticEval (S*A*S⁻¹) D.interior.toDisk)ᴴ *
      matrixAnalyticEval (S*A*S⁻¹) D.interior.toDisk ≤ 1)
    {κ : ℝ} (hκ : 0 < κ) {X Y : Matrix (Fin n) (Fin m) ℂ}
    (hX : S*X = (κ:ℂ) • X) (hY : S*Y = Y)
    (hx : ‖vectorize X‖ = 1) (hy : ‖vectorize Y‖ = 1) (hXY : Xᴴ*Y = 0)
    {F : ℂ → Matrix (Fin m) (Fin m) ℂ} (hF : AnalyticOnNhd ℂ F (closure D.domain))
    (hn : ∀ z ∈ closure D.domain, ‖F z‖ ≤ 1)
    (he : Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ)
      (completeAnalyticEval (S*A*S⁻¹) F) (vectorize X) = vectorize Y) : κ ≤ 2 := by
  have hA : spectrum ℂ A ⊆ D.domain := (spectrum_subset_numericalRange A).trans hW
  have hA' : spectrum ℂ (S*A*S⁻¹) ⊆ D.domain := by rwa [spectrum_matrix_similarity hu]
  let Λ := D.positiveDensity (S*A*S⁻¹) hA'
  have hΛ : ∀ t, (Λ t).IsHermitian := fun t =>
    (Matrix.nonneg_iff_posSemidef.mp (D.positiveDensity_nonneg (S*A*S⁻¹) hA' hc t)).isHermitian
  have hrep (v : ℂ → Matrix (Fin m) (Fin m) ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain)) :
      completeAnalyticEval (S*A*S⁻¹) v = ∫ t, Λ t ⊗ₖ D.trace v hv t ∂AddCircle.haarAddCircle :=
    D.positiveDensity_representation (S*A*S⁻¹) hA' hv
  let p := densityField (μ := AddCircle.haarAddCircle) Λ X X
  let q := densityField (μ := AddCircle.haarAddCircle) Λ Y Y
  let r := densityField (μ := AddCircle.haarAddCircle) Λ X Y
  have hpJ : l2Star p = p := densityField_star Λ hΛ X X
  have hqJ : l2Star q = q := densityField_star Λ hΛ Y Y
  obtain ⟨L,R,hLn,hRn,hLa,hRa,hLC,hRC⟩ := D.ordered_modules hF hn
  have hord := D.positive_ordered (S*A*S⁻¹) hA' hc hF hn hx hy he
  obtain ⟨hp,hq⟩ := densityField_ordered_adjoints Λ (D.trace F hF) X Y L R hLa hRa hord
  have hm := actual_density_means (μ := AddCircle.haarAddCircle) Λ
    (D.positiveDensity_mass (S*A*S⁻¹) hA') hx hXY
  have hr0 : matrixFourier.proj 0 r = 0 := densityField_mean_zero Λ X Y hm.1
  have hp0 : matrixFourier.proj 0 p ≠ 0 := densityField_mean_nonzero Λ X hm.2
  let E := hermitianField (⟨D.resolventField A,D.resolvent_continuous A hA⟩ : C(UnitAddCircle,Matrix (Fin n) (Fin n) ℂ))
  have hE : ∀ t, (E t).PosSemidef := D.resolventField_posSemidef A hW
  have hXid : densityField (μ := AddCircle.haarAddCircle) E X X =
      D.cauchy.adjoint p + l2Star (D.cauchy.adjoint p) := by
    have hh := D.resolvent_density_identification A hA hS hu Λ hΛ hrep hκ.ne' hκ.ne' hX hX
    simpa only [div_self hκ.ne',Complex.ofReal_one,one_smul,show l2Star (densityField (μ := AddCircle.haarAddCircle) Λ X X) = p from hpJ] using hh
  have hY' : S*Y = ((1:ℝ):ℂ) • Y := by
    simpa only [Complex.ofReal_one,one_smul] using hY
  have hYid : densityField (μ := AddCircle.haarAddCircle) E Y Y =
      D.cauchy.adjoint q + l2Star (D.cauchy.adjoint q) := by
    have hh := D.resolvent_density_identification A hA hS hu Λ hΛ hrep one_ne_zero one_ne_zero hY' hY'
    simpa only [div_self one_ne_zero,Complex.ofReal_one,one_smul,show l2Star (densityField (μ := AddCircle.haarAddCircle) Λ Y Y) = q from hqJ] using hh
  have hXYid : densityField (μ := AddCircle.haarAddCircle) E X Y =
      (κ:ℂ) • D.cauchy.adjoint r + ((κ⁻¹:ℝ):ℂ) • l2Star (D.cauchy.adjoint (l2Star r)) := by
    have hh := D.resolvent_density_identification A hA hS hu Λ hΛ hrep hκ.ne' one_ne_zero hX hY'
    simpa only [div_one,one_div] using hh
  have hblock := densityField_block_bound E hE X Y
  rw [hXid,hYid,hXYid,D.cauchy_adjoint (Fin m)] at hblock
  exact matrixFourier.density_comparison_core l2Star matrixFourier_star_zero matrixFourier_star_positive
    D.kernel.matrixM L R D.kernel.matrixM_norm_le hLn hRn D.kernel.matrixM_swap hLC hRC
    p q r hp hq hpJ hqJ hr0 hp0 κ hκ hblock
end AdmissibleDomain
end CompleteCrouzeix

end

end

end OAI
end

theorem solution : type_of% @OAI.CompleteCrouzeix.AdmissibleDomain.extremal_condition_bound_oai := @OAI.CompleteCrouzeix.AdmissibleDomain.extremal_condition_bound_oai
