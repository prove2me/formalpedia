-- Prove2me | solution 1 for OAI.Release061.interior_balls_from_small_slope_graphs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:02:13.960987+00:00
-- url     : https://prove2.me/submissions/92e313b0-480c-4086-af02-ef125728f03d

import Mathlib
import Definitions.Def_OAIQ025S003

section
-- module Solutions.OAIQ025_SD.Compat
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_BoundaryInjective
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.radiusCircleCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Metric Complex
open scoped Topology
noncomputable section
namespace Release061.Wiener
open scoped BigOperators ComplexConjugate Topology
open Set Filter

lemma hilbert_real {f : Space} (hf : f ∈ realSubspace) : hilbert f ∈ realSubspace := by
  rw [mem_realSubspace,← hilbert_conjugate,mem_realSubspace.mp hf]

lemma schwarzMode_differentiable (n : ℤ) : Differentiable ℂ (schwarzMode n) := by
  unfold schwarzMode
  split_ifs <;> fun_prop

lemma schwarz_coe (p : Poly) :
    schwarz (p : Space) = p.coeff.sum (fun n z => z • schwarzModeC n) := fromModes_coe _ _ _ _

lemma schwarz_norm (f : Space) : ‖schwarz f‖ ≤ 3*‖f‖ := fromModes_bound _ _ _ _

lemma schwarz_single (n : ℤ) (c : ℂ) :
    schwarz ((AddMonoidAlgebra.single n c : Poly) : Space) = c • schwarzModeC n :=
  fromModes_single _ _ _ _ _

lemma discValue_eq (f : Space) {z : ℂ} (hz : z ∈ ClosedDisc) :
    discValue f z = schwarz f ⟨z,hz⟩ := dite_eq_left hz

lemma exists_poly_seq (f : Space) : ∃ p : ℕ → Poly, Tendsto (fun j => (p j : Space)) atTop (𝓝 f) := by
  obtain ⟨s,hs,ht⟩ := mem_closure_iff_seq_limit.mp (UniformSpace.Completion.denseRange_coe f)
  choose p hp using hs
  exact ⟨p,by simpa only [hp] using ht⟩

lemma polyDisc_eq (p : Poly) {z : ℂ} (hz : z ∈ ClosedDisc) :
    polyDisc p z = discValue (p : Space) z := by
  rw [discValue_eq _ hz,schwarz_coe]
  simp only [polyDisc,Finsupp.sum,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
  rfl

lemma polyDisc_differentiable (p : Poly) : Differentiable ℂ (polyDisc p) := by
  unfold polyDisc Finsupp.sum
  apply Differentiable.fun_sum
  intro n _
  exact (differentiable_const _).mul (schwarzMode_differentiable n)

lemma polyDisc_tendsto_uniformly {p : ℕ → Poly} {f : Space}
    (h : Tendsto (fun j => (p j : Space)) atTop (𝓝 f)) :
    TendstoUniformlyOn (fun j => polyDisc (p j)) (discValue f) atTop ClosedDisc := by
  have ht := ContinuousMap.tendsto_iff_tendstoUniformly.mp (schwarz.continuous.tendsto f |>.comp h)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp ht ε hε] with j hj
  intro z hz
  rw [polyDisc_eq _ hz,discValue_eq _ hz,discValue_eq _ hz]
  exact hj ⟨z,hz⟩

lemma discValue_analytic (f : Space) : AnalyticOnNhd ℂ (discValue f) (Metric.ball 0 1) := by
  obtain ⟨p,hp⟩ := exists_poly_seq f
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  exact ((polyDisc_tendsto_uniformly hp).mono Metric.ball_subset_closedBall).tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall fun j => (polyDisc_differentiable (p j)).differentiableOn) Metric.isOpen_ball

lemma fourier_nat (j : ℕ) (θ : Circle) : fourier (j : ℤ) θ = (fourier 1 θ)^j := by
  induction j with
  | zero => simp only [Nat.cast_zero,fourier_zero,pow_zero]
  | succ j hj => rw [Nat.cast_add,Nat.cast_one,fourier_add,hj,pow_succ]

lemma schwarzMode_boundary (n : ℤ) (θ : Circle) :
    schwarzMode n (fourier 1 θ) =
      hilbertSymbol n * fourier n θ - hilbertSymbol n + Complex.I * fourier n θ := by
  by_cases hn : 0 < n
  · rw [schwarzMode,ite_eq_left hn,← fourier_nat,Int.toNat_of_nonneg hn.le,
      hilbertSymbol,ite_eq_left hn]
    ring
  · by_cases hn' : n < 0
    · rw [schwarzMode,ite_eq_right hn,hilbertSymbol,ite_eq_right hn,ite_eq_left hn']
      ring
    · have : n = 0 := by omega
      subst n
      simp [schwarzMode,hilbertSymbol]

lemma schwarz_boundary (f : Space) (θ : Circle) :
    discValue f (fourier 1 θ) = boundary (hilbert f) θ - boundary (hilbert f) 0 +
      Complex.I * boundary f θ := by
  have hz : fourier 1 θ ∈ ClosedDisc := by simpa only [ClosedDisc,Metric.mem_closedBall,dist_zero_right] using (show ‖fourier 1 θ‖ ≤ 1 by simpa only [fourier_one] using (_root_.Circle.norm_coe (AddCircle.toCircle θ)).le)
  rw [discValue_eq _ hz]
  induction f using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih p =>
    rw [poly_expansion p]
    simp only [map_sum,schwarz_single,hilbert,multiplier_single,boundary_single,
      ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,
      Finset.mul_sum]
    rw [← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    change _ * schwarzMode n (fourier 1 θ) = _
    rw [schwarzMode_boundary,fourier_eval_zero]
    ring

lemma realAlgebra_closed : IsClosed (realAlgebra : Set Space) := by
  change IsClosed {f | conjugate f = f}
  exact isClosed_eq conjugate.continuous continuous_id

instance instCompleteSpaceSubtypeSpaceMemSubalgebraRealRealAlgebra : CompleteSpace realAlgebra := realAlgebra_closed.completeSpace_coe

lemma normalizedHilbert_eval_zero (f : realAlgebra) :
    realEvaluation 0 (normalizedHilbert f) = 0 := by
  change realEvaluation 0 (realHilbert f-algebraMap ℝ realAlgebra (realEvaluation 0 (realHilbert f))) = 0
  rw [map_sub,AlgHom.commutes]
  simp

open MeasureTheory

lemma coeff_single (n m : ℤ) (z : ℂ) :
    coeff n ((AddMonoidAlgebra.single m z : Poly) : Space) = if m = n then z else 0 := by
  classical
  change fourierCLM n (boundary _) = _
  rw [boundary_single,map_smul]
  change z • fourierCoeff (fourier m) n = _
  rw [fourierCoeff_fourier]
  by_cases h : m = n <;> simp [h]

lemma coeff_coe (n : ℤ) (p : Poly) : coeff n (p : Space) = p.coeff n := by
  classical
  rw [poly_expansion p,map_sum]
  simp only [coeff_single]
  by_cases hn : p.coeff n = 0 <;> simp [hn]

lemma cutoff_bound (s : Finset ℤ) (f : Space) : ‖cutoff s f‖ ≤ ‖f‖ := by
  simpa only [cutoff,one_mul] using fromModes_bound _ 1 _ f

lemma cutoff_eq (s : Finset ℤ) (f : Space) :
    cutoff s f = ∑ n ∈ s, coeff n f • ((AddMonoidAlgebra.single n 1 : Poly) : Space) := by
  classical
  induction f using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih p =>
    change fromModes _ _ _ (p : Space) = _
    rw [fromModes_coe]
    simp only [coeff_coe,Finsupp.sum,smul_ite,smul_zero]
    exact Finset.sum_bij_ne_zero (fun n _ _ => n)
      (by intro _ _ hz; by_contra hs; simp [hs] at hz)
      (by intro a _ _ b _ _ h; exact h)
      (by
        intro n hn hz
        have hc : p.coeff n ≠ 0 := fun h => hz (by rw [h,zero_smul])
        exact ⟨n,Finsupp.mem_support_iff.mpr hc,by simpa only [ite_eq_left hn] using hz,rfl⟩)
      (by
        intro n _ hz
        have hs : n ∈ s := by by_contra h; simp [h] at hz
        rw [ite_eq_left hs])

lemma cutoff_coe_self (p : Poly) : cutoff p.coeff.support (p : Space) = p := by
  rw [cutoff_eq]
  simp only [coeff_coe]
  conv_rhs => rw [poly_expansion p]
  apply Finset.sum_congr rfl
  intro _ _
  rw [← UniformSpace.Completion.coe_smul]
  rw [AddMonoidAlgebra.smul_single,smul_eq_mul,mul_one]

lemma boundary_injective : Function.Injective boundary := by
  suffices ∀ f : Space, boundary f = 0 → f = 0 by
    intro f g h
    exact sub_eq_zero.mp (this (f-g) (by rw [map_sub,h,sub_self]))
  intro f hf
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨p,hp⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt f (half_pos hε)
  have hz : cutoff p.coeff.support f = 0 := by
    rw [cutoff_eq]
    apply Finset.sum_eq_zero
    intro n _
    have hc : coeff n f = 0 := by change fourierCLM n (boundary f) = 0; rw [hf,map_zero]
    rw [hc,zero_smul]
  have hpc : ‖(p : Space)‖ ≤ ‖(p : Space)-f‖ := by
    have h := cutoff_bound p.coeff.support ((p : Space)-f)
    rw [map_sub,cutoff_coe_self,hz,sub_zero] at h
    exact h
  have hd : ‖f-(p : Space)‖ < ε/2 := by simpa only [dist_eq_norm] using hp
  have hn := norm_add_le (f-(p : Space)) (p : Space)
  rw [sub_add_cancel,norm_sub_rev] at hn
  rw [norm_sub_rev] at hd
  linarith

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_VectorLift
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.AnalyticLift
variable {d j : ℕ} {A : Type*} [NormedCommRing A] [NormedAlgebra ℝ A] [NormOneClass A]

omit [NormOneClass A] in
lemma monomial_apply (σ : Fin j → Fin d) (x : Fin j → Fin d → A) :
    monomial σ x = ∏ i, x i (σ i) := by
  simp [monomial,ContinuousMultilinearMap.mkPiAlgebraFin_apply,List.prod_ofFn]

lemma monomial_norm_le (σ : Fin j → Fin d) : ‖monomial (A := A) σ‖ ≤ 1 := by
  apply ContinuousMultilinearMap.opNorm_le_bound zero_le_one
  intro x
  rw [monomial_apply,one_mul]
  exact (Finset.norm_prod_le _ _).trans (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    (fun i _ => norm_le_pi_norm (x i) (σ i)))

lemma coefficient_norm_le (p : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) ℝ) :
    ‖coefficient (A := A) p‖ ≤ (d : ℝ)^j * ‖p‖ := by
  classical
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : Fin j → Fin d, ‖p‖ := by
      apply Finset.sum_le_sum
      intro σ _
      rw [norm_smul]
      exact (mul_le_mul (p.unit_le_opNorm ((pi_norm_le_iff_of_nonneg zero_le_one).mpr (by
        intro i
        exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (by
          intro k
          by_cases h : k = σ i <;> simp [h]))))
        (monomial_norm_le σ) (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_one _)
    _ = _ := by simp

lemma coordinate_expansion
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) ℝ)
    (x : Fin j → Fin d → ℝ) :
    p x = ∑ σ : Fin j → Fin d, p (fun i => Pi.single (σ i) 1) * ∏ i, x i (σ i) := by
  classical
  have hx : x = fun i => ∑ k : Fin d, x i k • Pi.single k 1 := by
    funext i l
    simp [Finset.sum_apply,Pi.single_apply]
  conv_lhs => rw [hx,p.map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [p.map_smul_univ]
  simp only [smul_eq_mul,mul_comm]

omit [NormOneClass A] in
lemma evaluation_coefficient (φ : A →ₐ[ℝ] ℝ)
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) ℝ)
    (x : Fin j → Fin d → A) :
    φ (coefficient p x) = p (fun i k => φ (x i k)) := by
  classical
  rw [coordinate_expansion]
  simp only [coefficient,sum_apply,map_sum,
    smul_apply,map_smul,monomial_apply,map_prod,smul_eq_mul]

lemma radius_lower_bound (p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ)
    {r : ℝ≥0} (hr : (r : ℝ≥0∞) < p.radius) :
    (r / (d+1 : ℝ≥0) : ℝ≥0) ≤ (series (A := A) p).radius := by
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  apply (p.summable_norm_mul_pow hr).of_nonneg_of_le
  · intro j; positivity
  · intro j
    have hd : (0 : ℝ) < d+1 := by positivity
    have hd' : (d : ℝ)/(d+1) ≤ 1 := (div_le_one hd).mpr (by linarith)
    calc
      _ ≤ ((d : ℝ)^j*‖p j‖) * ((r : ℝ)/(d+1))^j := by
        exact mul_le_mul_of_nonneg_right (coefficient_norm_le (p j)) (by positivity)
      _ = ‖p j‖ * (r : ℝ)^j * ((d : ℝ)/(d+1))^j := by rw [div_pow,div_pow]; ring
      _ ≤ ‖p j‖ * (r : ℝ)^j * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity) hd') (by positivity)
      _ = _ := mul_one _

lemma radius_pos (p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ)
    (hp : 0 < p.radius) : 0 < (series (A := A) p).radius := by
  obtain ⟨r,hr0,hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp
  apply lt_of_lt_of_le _ (radius_lower_bound (A := A) p hr)
  exact ENNReal.coe_pos.mpr (div_pos (ENNReal.coe_pos.mp hr0) (by positivity))

variable [CompleteSpace A]

lemma analytic_series (p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ)
    (hp : 0 < p.radius) : AnalyticAt ℝ (series (A := A) p).sum 0 :=
  by
  have hq : 0 < (series (A := A) p).radius := radius_pos p hp
  exact ((series (A := A) p).hasFPowerSeriesOnBall hq).analyticAt

lemma evaluation_series (φ : A →ₐ[ℝ] ℝ) (L : A →L[ℝ] ℝ)
    (hL : ∀ a, L a = φ a) (hφ : ∀ a, |φ a| ≤ ‖a‖)
    {f : (Fin d → ℝ) → ℝ} {p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ}
    {R : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f p 0 R)
    {r : ℝ≥0} (hr0 : 0 < r) (hr : (r : ℝ≥0∞) < R)
    {x : Fin d → A} (hx : ‖x‖ < (r : ℝ)/(d+1)) :
    φ ((series p).sum x) = f (fun k => φ (x k)) := by
  have hpr : (r : ℝ≥0∞) < p.radius := hr.trans_le hf.r_le
  have hxr : x ∈ Metric.eball 0 (series (A := A) p).radius := by
    apply Metric.eball_subset_eball (radius_lower_bound p hpr)
    rw [Metric.eball_coe,Metric.mem_ball,dist_zero_right]
    simpa only [NNReal.coe_div,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using hx
  have hex : ‖fun k => φ (x k)‖ < r := by
    have hn : ‖fun k => φ (x k)‖ ≤ ‖x‖ := by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr ?_
      intro k
      exact (hφ (x k)).trans (norm_le_pi_norm x k)
    have hdr : (r : ℝ)/(d+1) ≤ r := div_le_self (by positivity) (le_add_of_nonneg_left (Nat.cast_nonneg d))
    exact hn.trans_lt (hx.trans_le hdr)
  have hexR : (fun k => φ (x k)) ∈ Metric.eball 0 R := by
    apply Metric.eball_subset_eball hr.le
    rw [Metric.eball_coe,Metric.mem_ball,dist_zero_right]
    exact hex
  have hh := L.hasSum (((series (A := A) p).hasFPowerSeriesOnBall
    (radius_pos p (hf.r_pos.trans_le hf.r_le))).hasSum hxr)
  simp only [zero_add,hL,series,evaluation_coefficient] at hh
  exact hh.unique (by simpa only [zero_add] using hf.hasSum hexR)

theorem exists_scalar_lift {f : (Fin d → ℝ) → ℝ} (hf : AnalyticAt ℝ f 0) :
    ∃ (ε : ℝ) (F : (Fin d → A) → A), 0 < ε ∧ AnalyticAt ℝ F 0 ∧
      ∀ (φ : A →ₐ[ℝ] ℝ) (L : A →L[ℝ] ℝ), (∀ a, L a = φ a) →
        (∀ a, |φ a| ≤ ‖a‖) → ∀ x, ‖x‖ < ε → φ (F x) = f (fun k => φ (x k)) := by
  obtain ⟨p,R,hp⟩ := hf
  obtain ⟨r,hr0,hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  refine ⟨(r : ℝ)/(d+1),(series p).sum,div_pos (ENNReal.coe_pos.mp hr0) (by positivity),
    analytic_series p (hp.r_pos.trans_le hp.r_le),?_⟩
  intro φ L hL hφ x hx
  exact evaluation_series φ L hL hφ hp (ENNReal.coe_pos.mp hr0) hr hx

theorem exists_vector_lift {k : ℕ} {f : (Fin d → ℝ) → Fin k → ℝ}
    (hf : AnalyticAt ℝ f 0) :
    ∃ (ε : ℝ) (F : (Fin d → A) → Fin k → A), 0 < ε ∧ AnalyticAt ℝ F 0 ∧
      ∀ (φ : A →ₐ[ℝ] ℝ) (L : A →L[ℝ] ℝ), (∀ a, L a = φ a) →
        (∀ a, |φ a| ≤ ‖a‖) → ∀ x, ‖x‖ < ε →
          ∀ i, φ (F x i) = f (fun j => φ (x j)) i := by
  have hfi : ∀ i, AnalyticAt ℝ (fun x => f x i) 0 := (analyticAt_pi_iff.mp hf)
  choose ε F hε hF hEval using fun i => exists_scalar_lift (A := A) (hfi i)
  have hn : ∀ᶠ x : Fin d → A in 𝓝 0, ∀ i, ‖x‖ < ε i := by
    rw [Filter.eventually_all]
    intro i
    exact (isOpen_lt continuous_norm continuous_const).mem_nhds (by simpa using hε i)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨δ,fun x i => F i x,hδ,AnalyticAt.pi hF,?_⟩
  intro φ L hL hφ x hx i
  exact hEval i φ L hL hφ x (hball (by simpa [Metric.mem_ball,dist_zero_right] using hx) i)

end Release061.AnalyticLift

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_BishopBoundarySolution
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter

namespace Release061.Wiener

lemma realEvaluation_ext {f g : realAlgebra}
    (h : ∀ θ, realEvaluation θ f = realEvaluation θ g) : f = g := by
  apply Subtype.ext
  apply boundary_injective
  ext θ
  apply Complex.ext
  · exact h θ
  · rw [realAlgebra_boundary_im,realAlgebra_boundary_im]

lemma eval_zero_input {k : ℕ} (θ : Circle) (X : Fin k → realAlgebra) :
    (fun j => realEvaluation θ (Fin.cons (α := fun _ => realAlgebra) 0 X j)) =
      Fin.cons 0 (fun i => realEvaluation θ (X i)) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;> simp

lemma cons_zero_norm {A : Type*} [NormedAddCommGroup A] {k : ℕ} (X : Fin k → A) :
    ‖Fin.cons (α := fun _ => A) 0 X‖ = ‖X‖ := by
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (by
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp
      · simpa using norm_le_pi_norm X i)
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (by
      intro i
      simpa using norm_le_pi_norm (Fin.cons (α := fun _ => A) 0 X) i.succ)

lemma exists_boundary_lift {k : ℕ} {f : (Fin (k+1) → ℝ) → Fin k → ℝ}
    (hf : AnalyticAt ℝ f 0)
    (hf0 : ∀ᶠ X in 𝓝 (0 : Fin k → ℝ), f (Fin.cons 0 X) = 0) :
    ∃ (ε : ℝ) (F : (Fin (k+1) → realAlgebra) → Fin k → realAlgebra),
      0 < ε ∧ AnalyticAt ℝ F 0 ∧
      (∀ᶠ X in 𝓝 (0 : Fin k → realAlgebra), F (Fin.cons 0 X) = 0) ∧
      (∀ x, ‖x‖ < ε → ∀ θ i,
        realEvaluation θ (F x i) = f (fun j => realEvaluation θ (x j)) i) := by
  obtain ⟨ε,F,hε,hF,hEval⟩ := AnalyticLift.exists_vector_lift (A := realAlgebra) hf
  obtain ⟨δ,hδ,hδf⟩ := Metric.mem_nhds_iff.mp hf0
  refine ⟨ε,F,hε,hF,?_,?_⟩
  · filter_upwards [Metric.ball_mem_nhds (0 : Fin k → realAlgebra) (lt_min hε hδ)] with X hX
    have hX' : ‖X‖ < min ε δ := by simpa [Metric.mem_ball,dist_zero_right] using hX
    funext i
    apply realEvaluation_ext
    intro θ
    change realEvaluation θ (F (Fin.cons 0 X) i) = realEvaluation θ 0
    rw [map_zero,hEval (realEvaluation θ) (realEvaluationCLM θ) (fun _ => rfl)
      (realEvaluation_bound θ) _ (by rw [cons_zero_norm]; exact hX'.trans_le (min_le_left _ _)),
      eval_zero_input]
    have he : ‖fun j => realEvaluation θ (X j)‖ ≤ ‖X‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun j =>
        (realEvaluation_bound θ (X j)).trans (norm_le_pi_norm X j))
    have hh := hδf (by
      simpa [Metric.mem_ball,dist_zero_right] using he.trans_lt (hX'.trans_le (min_le_right _ _)))
    exact congrFun hh i
  · intro x hx θ i
    exact hEval _ (realEvaluationCLM θ) (fun _ => rfl) (realEvaluation_bound θ) x hx i

lemma bishopInput_apply {k : ℕ} (lam : realAlgebra) (p : BishopParams k) (X : BoundarySpace k) :
    bishopInput lam (p,X) = Fin.cons (p.2.2.1 • lam+constantReal p.2.2.2) X := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;> rfl

lemma bishopRHS_smooth {k : ℕ} (lam η : realAlgebra)
    {F : (Fin (k+1) → realAlgebra) → BoundarySpace k} (hF : AnalyticAt ℝ F 0) :
    ContDiffAt ℝ ∞ (bishopRHS lam η F) 0 := by
  have hFC : ContDiffAt ℝ ∞ (F ∘ bishopInput lam) 0 := by
    have hh : ContDiffAt ℝ ∞ F (bishopInput lam (0 : BishopParams k × BoundarySpace k)) := by
      simpa only [map_zero] using hF.contDiffAt
    have hI : ContDiff ℝ ∞ (bishopInput (k := k) lam) := ContinuousLinearMap.contDiff _
    exact hh.comp 0 hI.contDiffAt
  apply contDiffAt_pi.mpr
  intro i
  have hFi := contDiffAt_pi.mp hFC i
  change ContDiffAt ℝ ∞ (fun q : BishopParams k × BoundarySpace k =>
    constantReal (q.1.1 i) + normalizedHilbert (F (bishopInput lam q) i + q.1.2.1 i • η)) 0
  apply ContDiffAt.add
  · fun_prop
  · apply normalizedHilbert.contDiff.contDiffAt.comp _
    exact hFi.add (by fun_prop)

lemma bishopRHS_zero_unknown {k : ℕ} (lam η : realAlgebra)
    {F : (Fin (k+1) → realAlgebra) → BoundarySpace k}
    (hF0 : ∀ᶠ X in 𝓝 (0 : BoundarySpace k), F (Fin.cons 0 X) = 0) :
    ∀ᶠ X in 𝓝 (0 : BoundarySpace k), bishopRHS lam η F (0,X) = 0 := by
  filter_upwards [hF0] with X hX
  funext i
  simp [bishopRHS,bishopInput_apply,hX]

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_BishopAnalyticDiscs
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.radiusCircleCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
namespace Release061

theorem smooth_fixed_point_family_unique
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : P × E → E} {F' : P × E →L[ℝ] E}
    (hF : ContDiffAt ℝ ∞ F 0) (hFd : HasFDerivAt F F' 0)
    (hF0 : F 0 = 0) (hFX : F'.comp (ContinuousLinearMap.inr ℝ P E) = 0) :
    ∃ ψ : P → E, ψ 0 = 0 ∧ ContDiffAt ℝ ∞ ψ 0 ∧
      (∀ᶠ p in 𝓝 0, ψ p = F (p,ψ p)) ∧
      HasFDerivAt ψ (F'.comp (ContinuousLinearMap.inl ℝ P E)) 0 ∧
      (∀ᶠ q in 𝓝 (0 : P × E), F q = q.2 ↔ ψ q.1 = q.2) := by
  let G : P × E → E := fun q => q.2-F q
  let G' : P × E →L[ℝ] E := ContinuousLinearMap.snd ℝ P E-F'
  have hGd : HasFDerivAt G G' 0 := hasFDerivAt_snd.sub hFd
  have hG : ContDiffAt ℝ ∞ G 0 := contDiffAt_snd.sub hF
  have hGX : (fderiv ℝ G 0).comp (ContinuousLinearMap.inr ℝ P E) =
      ContinuousLinearMap.id ℝ E := by
    rw [hGd.fderiv,ContinuousLinearMap.sub_comp,hFX,sub_zero]
    rfl
  have hGP : (fderiv ℝ G 0).comp (ContinuousLinearMap.inl ℝ P E) =
      -(F'.comp (ContinuousLinearMap.inl ℝ P E)) := by
    rw [hGd.fderiv,ContinuousLinearMap.sub_comp]
    change 0-_ = _
    exact zero_sub _
  have hi : ((fderiv ℝ G 0).comp (ContinuousLinearMap.inr ℝ P E)).IsInvertible := by
    rw [hGX]
    exact ⟨ContinuousLinearEquiv.refl ℝ E,rfl⟩
  let ψ := hG.implicitFunction (by simp) hi
  have hψ0 : ψ 0 = 0 := hG.implicitFunction_apply_self (by simp) hi
  refine ⟨ψ,hψ0,hG.contDiffAt_implicitFunction (by simp) hi,?_,?_,?_⟩
  · have hh := hG.eventually_apply_implicitFunction (by simp) hi
    filter_upwards [hh] with p hp
    change ψ p-F (p,ψ p) = (0 : E)-F 0 at hp
    rw [hF0,sub_self] at hp
    exact sub_eq_zero.mp hp
  · have hd := (hG.hasStrictFDerivAt_implicitFunction (by simp) hi).hasFDerivAt
    rw [hGX,hGP] at hd
    have hinv : (ContinuousLinearMap.id ℝ E).inverse = ContinuousLinearMap.id ℝ E :=
      ContinuousLinearMap.inverse_equiv (ContinuousLinearEquiv.refl ℝ E)
    simpa only [ψ,Prod.fst_zero,hinv,ContinuousLinearMap.neg_comp,ContinuousLinearMap.comp_neg,
      ContinuousLinearMap.id_comp,neg_neg] using hd
  · have hh := hG.eventually_apply_eq_iff_implicitFunction (by simp) hi
    filter_upwards [hh] with q hq
    change q.2-F q = (0 : E)-F 0 ↔ ψ q.1 = q.2 at hq
    rw [hF0,sub_self,sub_eq_zero,eq_comm] at hq
    exact hq

end Release061

namespace Release061.Wiener

lemma normalizedHilbert_constant (r : ℝ) : normalizedHilbert (constantReal r) = 0 := by
  have hh : hilbert (1 : Space) = 0 := by
    rw [← UniformSpace.Completion.coe_one]
    change hilbert ((AddMonoidAlgebra.single 0 1 : Poly) : Space) = 0
    rw [hilbert,multiplier_single]
    simp [hilbertSymbol]
  have hc : realHilbert (constantReal r) = 0 := by
    apply Subtype.ext
    change hilbert (algebraMap ℝ Space r) = 0
    rw [Algebra.algebraMap_eq_smul_one]
    have hs := (hilbert.restrictScalars ℝ).map_smul r (1 : Space)
    change hilbert (r • (1 : Space)) = r • hilbert 1 at hs
    rw [hs,hh,smul_zero]
  simp [normalizedHilbert,hc]

lemma realEvaluation_constant (θ : Circle) (r : ℝ) :
    realEvaluation θ (constantReal r) = r := by
  change realEvaluation θ (algebraMap ℝ realAlgebra r) = r
  exact (realEvaluation θ).commutes r

lemma constantDisc_apply (r : ℝ) (z : ClosedDisc) : constantDisc r z = (r : ℂ) := by
  simp [constantDisc]

lemma realSchwarz_boundary (f : realAlgebra) (θ : Circle)
    (hz : fourier 1 θ ∈ ClosedDisc) :
    realSchwarz f ⟨fourier 1 θ,hz⟩ =
      (realEvaluation θ (normalizedHilbert f) : ℂ)+Complex.I*(realEvaluation θ f : ℂ) := by
  change schwarz (f : Space) ⟨fourier 1 θ,hz⟩ = _
  rw [← discValue_eq _ hz,schwarz_boundary]
  apply Complex.ext
  · simp only [Complex.add_re,Complex.sub_re,Complex.ofReal_re,Complex.mul_re,
      Complex.I_re,Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
    rw [realAlgebra_boundary_im,one_mul,sub_zero,add_zero]
    change _ = realEvaluation θ (realHilbert f-constantReal (realEvaluation 0 (realHilbert f)))
    rw [map_sub,realEvaluation_constant]
    rfl
  · simp only [Complex.add_im,Complex.sub_im,Complex.ofReal_re,Complex.mul_im,
      Complex.I_re,Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,one_mul,zero_add]
    rw [real_boundary (hilbert_real (realAlgebra_mem_subspace f)) θ,
      real_boundary (hilbert_real (realAlgebra_mem_subspace f)) 0,sub_self,zero_add]
    rfl

lemma schwarz_constant (r : ℝ) :
    realSchwarz (constantReal r) = ContinuousMap.const ClosedDisc (Complex.I*(r : ℂ)) := by
  change schwarz (algebraMap ℝ Space r) = _
  rw [Algebra.algebraMap_eq_smul_one]
  have hs := (schwarz.restrictScalars ℝ).map_smul r (1 : Space)
  change schwarz (r • (1 : Space)) = r • schwarz 1 at hs
  rw [hs,← UniformSpace.Completion.coe_one]
  change r • schwarz ((AddMonoidAlgebra.single 0 1 : Poly) : Space) = _
  rw [schwarz_single]
  ext z
  simp [schwarzModeC,schwarzMode,mul_comm]

lemma bishopDisc_smooth {k : ℕ} {Y : BishopParams k → BoundarySpace k}
    (hY : ContDiffAt ℝ ∞ Y 0) : ContDiffAt ℝ ∞ (bishopDisc Y) 0 := by
  apply contDiffAt_pi.mpr
  intro i
  apply ContDiffAt.add
  · fun_prop
  · exact realSchwarz.contDiff.contDiffAt.comp _ (contDiffAt_pi.mp hY i)

lemma bishopDisc_analytic {k : ℕ} (Y : BishopParams k → BoundarySpace k) (p : BishopParams k) :
    AnalyticOnNhd ℂ (fun z : ℂ => fun i => (p.1 i : ℂ)+discValue (Y p i) z) (Metric.ball 0 1) := by
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply differentiableAt_pi.mpr
  intro i
  exact (differentiableAt_const _).add (discValue_analytic (Y p i) z hz).differentiableAt

lemma bishopDisc_boundary {k : ℕ} {X Y : BishopParams k → BoundarySpace k}
    {p : BishopParams k} (hX : ∀ i, X p i = constantReal (p.1 i)+normalizedHilbert (Y p i))
    (θ : Circle) (i : Fin k) :
    bishopDisc Y p i ⟨fourier 1 θ,fourier_mem_closedDisc θ⟩ =
      (realEvaluation θ (X p i) : ℂ)+Complex.I*(realEvaluation θ (Y p i) : ℂ) := by
  change constantDisc (p.1 i) _+realSchwarz (Y p i) _ = _
  rw [constantDisc_apply,realSchwarz_boundary,hX i,map_add,realEvaluation_constant]
  rw [Complex.ofReal_add,add_assoc]

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_BishopBoundarySolutionConstants
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
namespace Release061.Wiener

lemma bishop_constant_branch {k : ℕ} {ε : ℝ} (hε : 0 < ε)
    {f : (Fin (k+1) → ℝ) → Fin k → ℝ}
    {F : (Fin (k+1) → realAlgebra) → BoundarySpace k}
    {lam η : realAlgebra} {X : BishopParams k → BoundarySpace k}
    (hEval : ∀ x, ‖x‖ < ε → ∀ θ i,
      realEvaluation θ (F x i) = f (fun j => realEvaluation θ (x j)) i)
    (hUnique : ∀ᶠ q in 𝓝 (0 : BishopParams k × BoundarySpace k),
      bishopRHS lam η F q = q.2 ↔ X q.1 = q.2) :
    ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ),
      X (q.1,0,0,q.2) = fun i => constantReal (q.1 i) := by
  let Q : ((Fin k → ℝ) × ℝ) → BishopParams k × BoundarySpace k :=
    fun q => ((q.1,0,0,q.2),fun i => constantReal (q.1 i))
  have hQ : ContinuousAt Q 0 := by fun_prop
  have hQ0 : Q 0 = 0 := by ext <;> simp [Q]
  have hsmall : ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ), ‖bishopInput lam (Q q)‖ < ε := by
    have hc : ContinuousAt (fun q => bishopInput lam (Q q)) 0 := by fun_prop
    exact hc.eventually ((isOpen_lt continuous_norm continuous_const).mem_nhds
      (by simpa only [Set.mem_ofPred_eq,hQ0,map_zero,norm_zero] using hε))
  have hu : ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ),
      bishopRHS lam η F (Q q) = (Q q).2 ↔ X (Q q).1 = (Q q).2 :=
    (show Tendsto Q (𝓝 0) (𝓝 0) by simpa only [hQ0] using hQ.tendsto).eventually hUnique
  filter_upwards [hu,hsmall] with q hq hs
  apply hq.mp
  have hF (i : Fin k) : F (bishopInput lam (Q q)) i = constantReal (f (Fin.cons q.2 q.1) i) := by
    apply realEvaluation_ext
    intro θ
    rw [hEval _ hs,realEvaluation_constant]
    congr 2
    funext j
    dsimp only [Q]
    rw [bishopInput_apply]
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [Fin.cons_zero,zero_smul,zero_add,realEvaluation_constant]
    · simp only [Fin.cons_succ,realEvaluation_constant]
  funext i
  change constantReal (q.1 i)+normalizedHilbert (F (bishopInput lam (Q q)) i+0 • η) = constantReal (q.1 i)
  rw [hF,zero_smul,add_zero,normalizedHilbert_constant,add_zero]

theorem bishop_boundary_solution_with_constants {k : ℕ} {f : (Fin (k+1) → ℝ) → Fin k → ℝ}
    (hf : AnalyticAt ℝ f 0)
    (hf0 : ∀ᶠ X in 𝓝 (0 : Fin k → ℝ), f (Fin.cons 0 X) = 0)
    (lam η : realAlgebra) :
    ∃ X Y : BishopParams k → BoundarySpace k,
      X 0 = 0 ∧ Y 0 = 0 ∧ ContDiffAt ℝ ∞ X 0 ∧ ContDiffAt ℝ ∞ Y 0 ∧
      (∀ᶠ p in 𝓝 0,
        (∀ i, X p i = constantReal (p.1 i)+normalizedHilbert (Y p i)) ∧
        (∀ θ i, realEvaluation θ (Y p i) =
          f (Fin.cons (p.2.2.1*realEvaluation θ lam+p.2.2.2)
            (fun j => realEvaluation θ (X p j))) i + realEvaluation θ η*p.2.1 i)) ∧
      (∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ),
        X (q.1,0,0,q.2) = fun i => constantReal (q.1 i)) := by
  obtain ⟨ε,F,hε,hF,hF0,hEval⟩ := exists_boundary_lift hf hf0
  let R := bishopRHS lam η F
  have hR := bishopRHS_smooth lam η hF
  have hR0 := bishopRHS_zero_unknown lam η hF0
  have hR00 : R 0 = 0 := hR0.self_of_nhds
  have hd := (hR.differentiableAt (by simp)).hasFDerivAt
  have hRX : (fderiv ℝ R 0).comp
      (ContinuousLinearMap.inr ℝ (BishopParams k) (BoundarySpace k)) = 0 := by
    have hcomp := hd.comp 0 (ContinuousLinearMap.inr ℝ (BishopParams k) (BoundarySpace k)).hasFDerivAt
    exact hcomp.unique ((hasFDerivAt_const (0 : BoundarySpace k) (0 : BoundarySpace k)).congr_of_eventuallyEq hR0)
  obtain ⟨X,hX0,hX,hEq,_,hUnique⟩ := smooth_fixed_point_family_unique hR hd hR00 hRX
  let Y : BishopParams k → BoundarySpace k := fun p i =>
    F (bishopInput lam (p,X p)) i+p.2.1 i • η
  have hY : ContDiffAt ℝ ∞ Y 0 := by
    apply contDiffAt_pi.mpr
    intro i
    apply ContDiffAt.add
    · have hc : ContDiffAt ℝ ∞ (fun p => bishopInput lam (p,X p)) 0 := by fun_prop
      have hFin : ContDiffAt ℝ ∞ F (bishopInput lam (0,X 0)) := by
        simpa only [hX0,← Prod.zero_eq_mk,map_zero] using hF.contDiffAt
      have hh := hFin.comp 0 hc
      exact contDiffAt_pi.mp hh i
    · fun_prop
  have hY0 : Y 0 = 0 := by
    have hh := hF0.self_of_nhds
    have hz : Fin.cons (α := fun _ : Fin (k+1) => realAlgebra) 0 (0 : BoundarySpace k) = 0 := by ext j; exact Fin.cases rfl (fun _ => rfl) j
    rw [hz] at hh
    ext i
    simp [Y,hX0,← Prod.zero_eq_mk,hh]
  refine ⟨X,Y,hX0,hY0,hX,hY,?_,bishop_constant_branch hε hEval hUnique⟩
  have hsmall : ∀ᶠ p in 𝓝 0, ‖bishopInput lam (p,X p)‖ < ε := by
    have hc : ContinuousAt (fun p => bishopInput lam (p,X p)) 0 := by fun_prop
    exact hc.eventually ((isOpen_lt continuous_norm continuous_const).mem_nhds
      (by simpa [hX0,← Prod.zero_eq_mk] using hε))
  filter_upwards [hEq,hsmall] with p hp hs
  refine ⟨fun i => congrFun hp i,?_⟩
  intro θ i
  change realEvaluation θ (F (bishopInput lam (p,X p)) i+p.2.1 i • η) = _
  rw [map_add,map_smul,hEval _ hs θ i,bishopInput_apply]
  have hi : (fun j => realEvaluation θ (Fin.cons (α := fun _ => realAlgebra) (p.2.2.1 • lam+constantReal p.2.2.2) (X p) j)) =
      Fin.cons (p.2.2.1*realEvaluation θ lam+p.2.2.2) (fun j => realEvaluation θ (X p j)) := by
    ext j
    refine Fin.cases ?_ (fun _ => rfl) j
    simp only [Fin.cons_zero,map_add,map_smul,smul_eq_mul]
    change _ + realEvaluation θ (algebraMap ℝ realAlgebra p.2.2.2) = _
    rw [AlgHom.commutes]
    rfl
  rw [hi]
  simp only [smul_eq_mul,mul_comm]

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SmoothFlatWeightedFourier
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
namespace Release061

lemma weighted_summable_of_cubic_decay {a : ℤ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : ℤ, n ≠ 0 → ‖a n‖ ≤ C/|((n : ℤ) : ℝ)|^3) :
    Summable (fun n : ℤ => (1+|((n : ℤ) : ℝ)|)*‖a n‖) := by
  have hs : Summable (fun n : ℤ => 2*C*(1/(n : ℝ)^2)) :=
    (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left (2*C)
  have hif : Summable (fun n : ℤ => if n = 0 then 0 else (1+|(n : ℝ)|)*‖a n‖) := by
    apply hs.of_norm_bounded
    intro n
    split_ifs with hn
    · simp [hn]
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast (show (1 : ℤ) ≤ |n| from Int.one_le_abs hn)
    have hn0 : 0 < |(n : ℝ)| := lt_of_lt_of_le zero_lt_one hn1
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))]
    calc
      _ ≤ (1+|(n : ℝ)|)*(C/|(n : ℝ)|^3) :=
        mul_le_mul_of_nonneg_left (ha n hn) (by positivity)
      _ ≤ (2*|(n : ℝ)|)*(C/|(n : ℝ)|^3) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 2*C*(1/(n : ℝ)^2) := by
        rw [← sq_abs]
        field_simp
  apply hif.congr_cofinite
  filter_upwards [Set.Finite.compl_mem_cofinite (Set.finite_singleton (0 : ℤ))] with n hn
  simp only [Set.mem_compl_iff,Set.mem_singleton_iff] at hn
  simp [hn]

lemma fourierCoeffOn_norm_le {f : ℝ → ℂ} {C : ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, ‖f x‖ ≤ C) (n : ℤ) :
    ‖fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) f n‖ ≤ C := by
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero,div_one,one_smul]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := C) (f := fun x => fourier (-n) (x : AddCircle (1-0 : ℝ)) • f x) (by
      intro x hx
      rw [norm_smul,fourier_apply,Circle.norm_coe,one_mul]
      exact hf x (by simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc hx))
  simpa using h

lemma fourierCoeffOn_deriv_norm_le {f g : ℝ → ℂ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt f (g x) x)
    (hg : Continuous g) (he : f 0 = f 1) {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) f n‖ ≤
      ‖fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) g n‖ / |(n : ℝ)| := by
  rw [fourierCoeffOn_of_hasDerivAt (by norm_num : (0 : ℝ) < 1) hn
    (by simpa only [uIcc_of_le zero_le_one] using hf) (hg.intervalIntegrable 0 1)]
  simp only [he,sub_self,mul_zero,Complex.ofReal_one,Complex.ofReal_zero,sub_zero,one_mul,zero_sub,norm_mul,norm_div]
  simp only [norm_one,norm_neg,Complex.norm_ofNat,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_I,mul_one,Complex.norm_intCast]
  have hpos : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  have hpi : 1 ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
  have hh : 1/(2*Real.pi*|(n : ℝ)|) ≤ 1/|(n : ℝ)| :=
    one_div_le_one_div_of_le hpos (by nlinarith)
  exact (mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans_eq (by ring)

theorem smooth_flat_weighted_fourier {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f)
    (h0 : f =ᶠ[𝓝 (0 : ℝ)] 0) (h1 : f =ᶠ[𝓝 (1 : ℝ)] 0) :
    Summable (fun n : ℤ => (1+|(n : ℝ)|)*
      ‖fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) f n‖) := by
  have hc (j : ℕ) : Continuous (iteratedDeriv j f) :=
    hf.continuous_iteratedDeriv j (by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top))
  have hd (j : ℕ) (x : ℝ) : HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j+1) f x) x := by
    rw [iteratedDeriv_succ]
    exact (hf.differentiable_iteratedDeriv j (by exact_mod_cast (show (j : ℕ∞) < ⊤ from ENat.natCast_lt_top j)) x).hasDerivAt
  have he (j : ℕ) : iteratedDeriv j f 0 = iteratedDeriv j f 1 := by
    rw [h0.iteratedDeriv_eq j,h1.iteratedDeriv_eq j]
    simp
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc 3).continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl,zero_le_one⟩)
  apply weighted_summable_of_cubic_decay hC0
  intro n hn
  have hn0 : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  have hrec (j : ℕ) : ‖fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (iteratedDeriv j f) n‖ ≤
      ‖fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (iteratedDeriv (j+1) f) n‖ / |(n : ℝ)| :=
    fourierCoeffOn_deriv_norm_le (fun x _ => hd j x) (hc (j+1)) (he j) hn
  have h3 := fourierCoeffOn_norm_le hC n
  have h2 := (hrec 2).trans (div_le_div_of_nonneg_right h3 hn0.le)
  have h1' := (hrec 1).trans (div_le_div_of_nonneg_right h2 hn0.le)
  have h0' := (hrec 0).trans (div_le_div_of_nonneg_right h1' hn0.le)
  simpa only [iteratedDeriv_zero,div_div,pow_succ,pow_zero,one_mul] using h0'

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CosineBumpWeightedSummable
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
namespace Release061.Wiener

lemma exists_boundary_of_weighted_summable (f : C(Circle,ℂ))
    (hf : Summable (fun n : ℤ => weight n*‖fourierCoeff f n‖)) :
    ∃ F : Space, boundary F = f := by
  have hs : Summable (fun n : ℤ => (fourierCoeff f n) •
      ((AddMonoidAlgebra.single n 1 : Poly) : Space)) := by
    apply hf.of_norm_bounded
    intro n
    rw [norm_smul,UniformSpace.Completion.norm_coe,norm_def,wnorm_single]
    simp only [norm_one,mul_one]
    exact le_of_eq (mul_comm _ _)
  have ha : Summable (fourierCoeff f) := by
    apply hf.of_norm_bounded
    intro n
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_weight n)
  refine ⟨∑' n : ℤ, (fourierCoeff f n) • ((AddMonoidAlgebra.single n 1 : Poly) : Space),?_⟩
  have hb := boundary.hasSum hs.hasSum
  simp only [map_smul,boundary_single,one_smul] at hb
  exact hb.unique (hasSum_fourier_series_of_summable ha)

lemma exists_real_boundary_of_weighted_summable (f : C(Circle,ℝ))
    (hf : Summable (fun n : ℤ => weight n*
      ‖fourierCoeff (fun θ => (f θ : ℂ)) n‖)) :
    ∃ F : realAlgebra, ∀ θ, realEvaluation θ F = f θ := by
  let g : C(Circle,ℂ) := ⟨fun θ => f θ,by fun_prop⟩
  obtain ⟨F,hF⟩ := exists_boundary_of_weighted_summable g hf
  have hr : conjugate F = F := by
    apply boundary_injective
    ext θ
    rw [boundary_conjugate,hF]
    simp [g]
  refine ⟨⟨F,hr⟩,?_⟩
  intro θ
  change (boundary F θ).re = f θ
  rw [hF]
  rfl

lemma circleCos_coe (t : ℝ) : circleCos (t : Circle) = Real.cos (2*Real.pi*t) := by
  change (fourier 1 (t : Circle)).re = _
  rw [fourier_coe_apply,Complex.exp_re]
  simp [Complex.mul_re,Complex.mul_im]

lemma circleCos_half : circleCos ((1/2 : ℝ) : Circle) = -1 := by
  rw [circleCos_coe]
  have hh : 2*Real.pi*(1/2) = Real.pi := by ring
  rw [hh,Real.cos_pi]

lemma cosineBump_weighted_summable (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (hR2 : R < 2) :
    Summable (fun n : ℤ => weight n*
      ‖fourierCoeff (fun θ => (cosineBump r R hr hR θ : ℂ)) n‖) := by
  let B : ContDiffBump (-1 : ℝ) := ⟨r,R,hr,hR⟩
  let f : ℝ → ℂ := fun t => B (Real.cos (2*Real.pi*t))
  have hfc : ContDiff ℝ ∞ f := by
    apply Complex.ofRealCLM.contDiff.comp
    exact B.contDiff.comp (by fun_prop)
  have hevent (a : ℝ) (ha : Real.cos (2*Real.pi*a) = 1) : f =ᶠ[𝓝 a] 0 := by
    have hc : ContinuousAt (fun t : ℝ => dist (Real.cos (2*Real.pi*t)) (-1 : ℝ)) a := by fun_prop
    have hn : R < dist (Real.cos (2*Real.pi*a)) (-1 : ℝ) := by
      norm_num [ha,Real.dist_eq]
      exact hR2
    filter_upwards [hc.eventually (Ioi_mem_nhds hn)] with t ht
    change (B (Real.cos (2*Real.pi*t)) : ℂ) = 0
    rw [B.zero_of_le_dist ht.le,Complex.ofReal_zero]
  have h0 := hevent 0 (by simp)
  have h1 := hevent 1 (by simp [Real.cos_two_pi])
  have hs := Release061.smooth_flat_weighted_fourier hfc h0 h1
  have heq : (fun θ => (cosineBump r R hr hR θ : ℂ)) = AddCircle.liftIoc 1 0 f := by
    funext θ
    let t := (AddCircle.equivIoc 1 0 θ).val
    have ht : t ∈ Ioc (0 : ℝ) (0+1) := (AddCircle.equivIoc 1 0 θ).property
    have htθ : (t : Circle) = θ := AddCircle.coe_equivIoc (p := 1) (a := 0) (y := θ)
    rw [← htθ,AddCircle.liftIoc_coe_apply ht]
    simp [cosineBump,B,f,circleCos_coe]
  simpa only [weight,heq,fourierCoeff_liftIoc_eq,zero_add] using hs

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_RealMeanPositive
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
namespace Release061.Wiener

lemma smooth_cosine_lift {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (hh0 : h =ᶠ[𝓝 1] 0) :
    ∃ F : realAlgebra, ∀ θ, realEvaluation θ F = h (circleCos θ) := by
  let f : ℝ → ℂ := fun t => h (Real.cos (2*Real.pi*t))
  have hfc : ContDiff ℝ ∞ f := by
    apply Complex.ofRealCLM.contDiff.comp
    exact hh.comp (by fun_prop)
  have hevent (a : ℝ) (ha : Real.cos (2*Real.pi*a) = 1) : f =ᶠ[𝓝 a] 0 := by
    have ht : Tendsto (fun t : ℝ => Real.cos (2*Real.pi*t)) (𝓝 a) (𝓝 1) := by
      rw [← ha]
      exact (by fun_prop : ContinuousAt (fun t : ℝ => Real.cos (2*Real.pi*t)) a)
    filter_upwards [ht.eventually hh0] with t ht
    simp [f,ht]
  have hs := Release061.smooth_flat_weighted_fourier hfc (hevent 0 (by simp))
    (hevent 1 (by simp [Real.cos_two_pi]))
  let g : C(Circle,ℝ) := ⟨fun θ => h (circleCos θ),hh.continuous.comp circleCos.continuous⟩
  apply exists_real_boundary_of_weighted_summable g
  have heq : (fun θ => (g θ : ℂ)) = AddCircle.liftIoc 1 0 f := by
    funext θ
    let t := (AddCircle.equivIoc 1 0 θ).val
    have ht := (AddCircle.equivIoc 1 0 θ).property
    have htθ : (t : Circle) = θ := AddCircle.coe_equivIoc (p := 1) (a := 0) (y := θ)
    rw [← htθ,AddCircle.liftIoc_coe_apply ht]
    change (h (circleCos (t : Circle)) : ℂ) = (h (Real.cos (2*Real.pi*t)) : ℂ)
    rw [circleCos_coe]
  simpa only [weight,heq,fourierCoeff_liftIoc_eq,zero_add] using hs

theorem exists_localized_reciprocal :
    ∃ κ : realAlgebra, ∀ θ,
      dist (circleCos θ) (-1 : ℝ) ≤ 1/2 →
        (2-2*circleCos θ)*realEvaluation θ κ = 1 := by
  let B : ContDiffBump (-1 : ℝ) := ⟨3/4,1,by norm_num,by norm_num⟩
  let h : ℝ → ℝ := fun r => B r/(2-2*r)
  have he : h =ᶠ[𝓝 1] 0 := by
    have hc : ContinuousAt (fun r : ℝ => dist r (-1 : ℝ)) 1 := by fun_prop
    filter_upwards [hc.eventually (Ioi_mem_nhds (by norm_num [Real.dist_eq] : (1 : ℝ) < dist 1 (-1 : ℝ)))] with r hr
    simp [h,B.zero_of_le_dist hr.le]
  have hh : ContDiff ℝ ∞ h := by
    apply contDiff_iff_contDiffAt.mpr
    intro r
    by_cases hr : r = 1
    · subst r
      exact contDiffAt_const.congr_of_eventuallyEq he
    · exact B.contDiff.contDiffAt.div (by fun_prop) (by dsimp; intro hz; apply hr; linarith)
  obtain ⟨κ,hκ⟩ := smooth_cosine_lift hh he
  refine ⟨κ,?_⟩
  intro θ hθ
  rw [hκ]
  change (2-2*circleCos θ)*(B (circleCos θ)/(2-2*circleCos θ)) = 1
  have hB : B (circleCos θ) = 1 := B.one_of_mem_closedBall (by
    change dist (circleCos θ) (-1 : ℝ) ≤ 3/4
    linarith)
  rw [hB]
  have hr : circleCos θ ≤ -1/2 := by
    rw [Real.dist_eq] at hθ
    have hp := (le_abs_self (circleCos θ-(-1))).trans hθ
    linarith
  have hd : 2-2*circleCos θ ≠ 0 := by linarith
  rw [← mul_div_assoc,mul_one,div_self hd]

lemma real_mean_positive (g : realAlgebra) (hg : ∀ θ, 0 ≤ realEvaluation θ g)
    {θ₀ : Circle} (hθ : realEvaluation θ₀ g ≠ 0) : 0 < (coeff 0 (g : Space)).re := by
  have hcont : Continuous (fun θ => realEvaluation θ g) :=
    Complex.continuous_re.comp (boundary (g : Space)).continuous
  have hint : Integrable (fun θ => boundary (g : Space) θ) AddCircle.haarAddCircle :=
    (boundary (g : Space)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : (coeff 0 (g : Space)).re = ∫ θ, realEvaluation θ g ∂AddCircle.haarAddCircle := by
    change (fourierCoeff (boundary (g : Space)) 0).re = _
    simp only [fourierCoeff,neg_zero,fourier_zero,one_smul]
    exact (integral_re hint).symm
  rw [he]
  exact hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (HasCompactSupport.of_compactSpace _) hg hθ

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SchwarzRadialExpansion
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.radiusCircleCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
namespace Release061.Wiener

lemma schwarzMode_nat (n : ℕ) (z : ℂ) :
    schwarzMode (n : ℤ) z = Complex.I*(2*z^n-1) := by
  cases n with
  | zero => norm_num [schwarzMode]
  | succ n => simp [schwarzMode]

lemma schwarzMode_second_difference (n : ℤ) {z : ℂ} (hz : z ≠ 0) :
    2*schwarzMode n z-schwarzMode (n+1) z-schwarzMode (n-1) z =
      (2-z-z⁻¹)*(schwarzMode n z-schwarzMode n 0)+
        (if n = 0 then 2*Complex.I*(1-z) else 0) := by
  by_cases hn : 0 < n
  · obtain ⟨m,hm⟩ : ∃ m : ℕ, n = ((m+1 : ℕ) : ℤ) := by
      refine ⟨n.toNat-1,?_⟩
      have hp : 0 < n.toNat := by omega
      have he : n.toNat-1+1 = n.toNat := Nat.sub_add_cancel hp
      rw [he,Int.toNat_of_nonneg hn.le]
    subst n
    have he1 : ((m+1 : ℕ) : ℤ)+1 = ((m+2 : ℕ) : ℤ) := by omega
    have he2 : ((m+1 : ℕ) : ℤ)-1 = (m : ℤ) := by omega
    rw [he1,he2,schwarzMode_nat,schwarzMode_nat,schwarzMode_nat,schwarzMode_nat]
    have hn0 : ((m+1 : ℕ) : ℤ) ≠ 0 := by omega
    rw [ite_eq_right hn0]
    simp only [zero_pow (Nat.succ_ne_zero m),mul_zero,zero_sub,pow_succ]
    field_simp [hz]
    ring
  · by_cases hn0 : n = 0
    · subst n
      simp [schwarzMode]
      ring
    · have hn1 : ¬0 < n+1 := by omega
      have hn2 : ¬0 < n-1 := by omega
      simp only [schwarzMode,ite_eq_right hn,ite_eq_right hn1,ite_eq_right hn2,ite_eq_right hn0]
      ring

lemma vanishingFactor_mul_single (n : ℤ) (c : ℂ) :
    vanishingFactor*((AddMonoidAlgebra.single n c : Poly) : Space) =
      2*((AddMonoidAlgebra.single n c : Poly) : Space)-
      ((AddMonoidAlgebra.single (n+1) c : Poly) : Space)-
      ((AddMonoidAlgebra.single (n-1) c : Poly) : Space) := by
  simp only [vanishingFactor,sub_mul,single_mul,one_mul]
  rw [show 1+n = n+1 by omega,show -1+n = n-1 by omega]

lemma schwarz_vanishingFactor_mul (g : Space) {z : ℂ} (hz : z ∈ ClosedDisc) (hz0 : z ≠ 0) :
    discValue (vanishingFactor*g) z =
      (2-z-z⁻¹)*(discValue g z-discValue g 0)+2*Complex.I*(1-z)*coeff 0 g := by
  have h0 : (0 : ℂ) ∈ ClosedDisc := by simp [ClosedDisc]
  simp only [discValue_eq _ hz,discValue_eq _ h0]
  induction g using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih p =>
    rw [poly_expansion p,Finset.mul_sum]
    simp only [map_sum,ContinuousMap.sum_apply]
    rw [← Finset.sum_sub_distrib,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [vanishingFactor_mul_single,map_sub,map_sub]
    have h2 : schwarz (2*((AddMonoidAlgebra.single n (p.coeff n) : Poly) : Space)) =
        (2 : ℂ) • schwarz ((AddMonoidAlgebra.single n (p.coeff n) : Poly) : Space) := by
      simpa only [two_mul,two_smul] using schwarz.map_add
        ((AddMonoidAlgebra.single n (p.coeff n) : Poly) : Space)
        ((AddMonoidAlgebra.single n (p.coeff n) : Poly) : Space)
    rw [h2]
    simp only [schwarz_single,coeff_single,ContinuousMap.sub_apply,ContinuousMap.smul_apply,
      smul_eq_mul,schwarzModeC]
    have hh := schwarzMode_second_difference n hz0
    by_cases hn0 : n = 0
    · rw [ite_eq_left hn0] at hh
      rw [ite_eq_left hn0]
      linear_combination p.coeff n*hh
    · rw [ite_eq_right hn0] at hh
      rw [ite_eq_right hn0]
      linear_combination p.coeff n*hh

lemma schwarz_radial_expansion (g : Space) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    discValue (vanishingFactor*g) (1-(t : ℂ)) =
      2*Complex.I*(t : ℂ)*coeff 0 g -
        (t : ℂ)^2/(1-(t : ℂ))*(discValue g (1-(t : ℂ))-discValue g 0) := by
  have hz : (1-(t : ℂ)) ∈ ClosedDisc := by
    rw [Metric.mem_closedBall,dist_zero_right]
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ 1-t)]
    linarith
  have hz0 : (1-(t : ℂ)) ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast ne_of_gt ht1
  rw [schwarz_vanishingFactor_mul g hz hz0]
  field_simp
  ring

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_TransverseCutoffs
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
namespace Release061.Wiener

lemma vanishingReal_eval (θ : Circle) : realEvaluation θ vanishingReal = 2-2*circleCos θ := by
  change (boundary (2-((AddMonoidAlgebra.single 1 1 : Poly) : Space)-
    ((AddMonoidAlgebra.single (-1) 1 : Poly) : Space)) θ).re = _
  have h2 : boundary (2 : Space) = 2 := by
    rw [show (2 : Space) = 1+1 by ring,map_add,boundary_one]
    ring
  simp only [map_sub,h2,boundary_single,one_smul,ContinuousMap.sub_apply,
    Complex.sub_re,fourier_neg,Complex.conj_re]
  change (2 : ℂ).re-(fourier 1 θ).re-(fourier 1 θ).re = _
  norm_num [circleCos]
  ring

lemma vanishingReal_nonneg (θ : Circle) : 0 ≤ realEvaluation θ vanishingReal := by
  rw [vanishingReal_eval]
  have hn : (fourier 1 θ).re ≤ 1 := by
    apply (Complex.re_le_norm _).trans
    simpa only [fourier_one] using (_root_.Circle.norm_coe (AddCircle.toCircle θ)).le
  change 0 ≤ 2-2*(fourier 1 θ).re
  linarith

lemma coeff_zero_real (g : realAlgebra) : (coeff 0 (g : Space)).im = 0 := by
  have hint : Integrable (fun θ => boundary (g : Space) θ) AddCircle.haarAddCircle :=
    (boundary (g : Space)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (fourierCoeff (boundary (g : Space)) 0).im = 0
  simp only [fourierCoeff,neg_zero,fourier_zero,one_smul]
  have hi := integral_im hint
  change (∫ θ, (boundary (g : Space) θ).im ∂AddCircle.haarAddCircle) =
    (∫ θ, boundary (g : Space) θ ∂AddCircle.haarAddCircle).im at hi
  rw [← hi]
  simp only [realAlgebra_boundary_im,integral_zero]

lemma coeff_zero_eq_realMean (g : realAlgebra) : coeff 0 (g : Space) = (realMean g : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using coeff_zero_real g

lemma localized_division {κ : realAlgebra}
    (hκ : ∀ θ, dist (circleCos θ) (-1 : ℝ) ≤ 1/2 →
      (2-2*circleCos θ)*realEvaluation θ κ = 1)
    {Y : realAlgebra}
    (hY : ∀ θ, (1/2 : ℝ) < dist (circleCos θ) (-1 : ℝ) → realEvaluation θ Y = 0) :
    Y = vanishingReal*(κ*Y) := by
  apply realEvaluation_ext
  intro θ
  rw [map_mul,map_mul,vanishingReal_eval]
  by_cases hθ : dist (circleCos θ) (-1 : ℝ) ≤ 1/2
  · rw [← mul_assoc,hκ θ hθ,one_mul]
  · rw [hY θ (lt_of_not_ge hθ),mul_zero,mul_zero]

lemma localized_radial_expansion {κ : realAlgebra}
    (hκ : ∀ θ, dist (circleCos θ) (-1 : ℝ) ≤ 1/2 →
      (2-2*circleCos θ)*realEvaluation θ κ = 1)
    {Y : realAlgebra}
    (hY : ∀ θ, (1/2 : ℝ) < dist (circleCos θ) (-1 : ℝ) → realEvaluation θ Y = 0)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    discValue (Y : Space) (1-(t : ℂ)) =
      Complex.I*(t : ℂ)*(2*realMean (κ*Y) : ℝ) -
        (t : ℂ)^2/(1-(t : ℂ))*(discValue (κ*Y : Space) (1-(t : ℂ))-discValue (κ*Y : Space) 0) := by
  have he := congrArg (fun f : realAlgebra => (f : Space)) (localized_division hκ hY)
  change (Y : Space) = vanishingFactor*((κ*Y : realAlgebra) : Space) at he
  have hs := schwarz_radial_expansion ((κ*Y : realAlgebra) : Space) ht ht1
  rw [← he,coeff_zero_eq_realMean] at hs
  rw [hs]
  push_cast
  ring

theorem exists_transverse_cutoffs :
    ∃ lam η κ : realAlgebra,
      (∀ θ, 0 ≤ realEvaluation θ lam ∧ 0 ≤ realEvaluation θ η) ∧
      (∀ θ, (1/2 : ℝ) ≤ dist (circleCos θ) (-1 : ℝ) →
        realEvaluation θ lam = 0 ∧ realEvaluation θ η = 0) ∧
      (∀ θ, realEvaluation θ η ≠ 0 → realEvaluation θ lam = 1) ∧
      (∀ θ, dist (circleCos θ) (-1 : ℝ) ≤ 1/2 →
        (2-2*circleCos θ)*realEvaluation θ κ = 1) ∧
      0 < 2*realMean (κ*η) := by
  let L : ContDiffBump (-1 : ℝ) := ⟨1/4,1/2,by norm_num,by norm_num⟩
  let H : ContDiffBump (-1 : ℝ) := ⟨1/16,1/8,by norm_num,by norm_num⟩
  obtain ⟨lam,hlam⟩ := exists_real_boundary_of_weighted_summable
    (cosineBump (1/4) (1/2) (by norm_num) (by norm_num))
    (cosineBump_weighted_summable _ _ _ _ (by norm_num))
  obtain ⟨g,hg⟩ := exists_real_boundary_of_weighted_summable
    (cosineBump (1/16) (1/8) (by norm_num) (by norm_num))
    (cosineBump_weighted_summable _ _ _ _ (by norm_num))
  have hl (θ : Circle) : realEvaluation θ lam = L (circleCos θ) := hlam θ
  have hh (θ : Circle) : realEvaluation θ g = H (circleCos θ) := hg θ
  obtain ⟨κ,hκ⟩ := exists_localized_reciprocal
  let η := vanishingReal*g
  have hgs : ∀ θ, (1/2 : ℝ) < dist (circleCos θ) (-1 : ℝ) → realEvaluation θ g = 0 := by
    intro θ hθ
    rw [hh]
    apply H.zero_of_le_dist
    change (1/8 : ℝ) ≤ _
    linarith
  have hkg : κ*η = g := by
    have he := localized_division hκ hgs
    calc
      κ*η = vanishingReal*(κ*g) := by dsimp only [η]; ring
      _ = g := he.symm
  refine ⟨lam,η,κ,?_,?_,?_,hκ,?_⟩
  · intro θ
    rw [hl]
    refine ⟨L.nonneg,?_⟩
    change 0 ≤ realEvaluation θ (vanishingReal*g)
    rw [map_mul,hh]
    exact mul_nonneg (vanishingReal_nonneg θ) H.nonneg
  · intro θ hθ
    rw [hl]
    have hz : H (circleCos θ) = 0 := H.zero_of_le_dist (by change (1/8 : ℝ) ≤ _; linarith)
    refine ⟨L.zero_of_le_dist hθ,?_⟩
    change realEvaluation θ (vanishingReal*g) = 0
    rw [map_mul,hh,hz,mul_zero]
  · intro θ hθ
    rw [hl]
    have hgθ : H (circleCos θ) ≠ 0 := by
      intro hz
      apply hθ
      change realEvaluation θ (vanishingReal*g) = 0
      rw [map_mul,hh,hz,mul_zero]
    have hd : dist (circleCos θ) (-1 : ℝ) < (1/8 : ℝ) := by
      by_contra hn
      exact hgθ (H.zero_of_le_dist (le_of_not_gt hn))
    exact L.one_of_mem_closedBall (by change dist (circleCos θ) (-1 : ℝ) ≤ 1/4; linarith)
  · rw [hkg]
    apply mul_pos (by norm_num : (0 : ℝ) < 2)
    apply real_mean_positive g (fun θ => by rw [hh]; exact H.nonneg)
      (θ₀ := ((1/2 : ℝ) : Circle))
    rw [hh,circleCos_half,H.one_of_mem_closedBall (by simp [H,Metric.mem_closedBall])]
    exact one_ne_zero

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_BishopNormalZeroDeformation
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
namespace Release061.Wiener
open scoped Topology
open Set Filter

lemma evaluation_vector_norm_le {k : ℕ} (θ : Circle) (X : BoundarySpace k) :
    ‖(fun i => realEvaluation θ (X i))‖ ≤ ‖X‖ := by
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun i =>
    (realEvaluation_bound θ (X i)).trans (norm_le_pi_norm X i))

lemma bishop_boundary_localization {k : ℕ}
    {f : (Fin (k+1) → ℝ) → Fin k → ℝ}
    (hf0 : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), f (Fin.cons 0 x) = 0)
    {lam η : realAlgebra}
    (hcut : ∀ θ, (1/2 : ℝ) ≤ dist (circleCos θ) (-1 : ℝ) →
      realEvaluation θ lam = 0 ∧ realEvaluation θ η = 0)
    {X Y : BishopParams k → BoundarySpace k} (hX0 : X 0 = 0)
    (hX : ContinuousAt X 0)
    (hEq : ∀ᶠ p in 𝓝 0, ∀ θ i, realEvaluation θ (Y p i) =
      f (Fin.cons (p.2.2.1*realEvaluation θ lam+p.2.2.2)
        (fun j => realEvaluation θ (X p j))) i+realEvaluation θ η*p.2.1 i) :
    ∀ᶠ p in 𝓝 0,
      (p.2.2.2 = 0 → ∀ θ, (1/2 : ℝ) < dist (circleCos θ) (-1 : ℝ) →
        ∀ i, realEvaluation θ (Y p i) = 0) ∧
      (p.2.2.1 = 0 → p.2.2.2 = 0 → ∀ i, Y p i = p.2.1 i • η) := by
  obtain ⟨ε,hε,hsmall⟩ := Metric.mem_nhds_iff.mp hf0
  have hn : ∀ᶠ p in 𝓝 0, ‖X p‖ < ε := by
    have hc : Tendsto (fun p => ‖X p‖) (𝓝 0) (𝓝 0) := by
      simpa only [hX0,norm_zero] using hX.norm.tendsto
    exact (tendsto_order.mp hc).2 ε hε
  filter_upwards [hEq,hn] with p hp hnp
  have hz (θ : Circle) : f (Fin.cons 0 (fun j => realEvaluation θ (X p j))) = 0 :=
    hsmall (by simpa only [Metric.mem_ball,dist_zero_right] using
      lt_of_le_of_lt (evaluation_vector_norm_le θ (X p)) hnp)
  refine ⟨?_,?_⟩
  · intro hδ θ hθ i
    obtain ⟨hl,hη⟩ := hcut θ hθ.le
    rw [hp θ i,hl,hη,hδ,mul_zero,zero_add,hz θ,Pi.zero_apply,zero_mul,add_zero]
  · intro hα hδ i
    apply realEvaluation_ext
    intro θ
    rw [hp θ i,hα,hδ,zero_mul,zero_add,hz θ,Pi.zero_apply,zero_add,map_smul]
    exact mul_comm _ _

lemma bishopNormal_smooth {k : ℕ} (κ : realAlgebra)
    {Y : BishopParams k → BoundarySpace k} (hY : ContDiffAt ℝ ∞ Y 0) :
    ContDiffAt ℝ ∞ (bishopNormal κ Y) 0 := by
  apply contDiffAt_pi.mpr
  intro i
  dsimp only [bishopNormal]
  exact contDiffAt_const.mul (realMean.contDiff.contDiffAt.comp 0
    (contDiffAt_const.mul (contDiffAt_pi.mp hY i)))

lemma bishopNormal_zero_deformation {k : ℕ} {κ η : realAlgebra}
    {Y : BishopParams k → BoundarySpace k}
    (hY : ∀ᶠ p in 𝓝 0, p.2.2.1 = 0 → p.2.2.2 = 0 → ∀ i, Y p i = p.2.1 i • η) :
    ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × (Fin k → ℝ)),
      bishopNormal κ Y (q.1,q.2,0,0) = (2*realMean (κ*η)) • q.2 := by
  have ht : Tendsto (fun q : (Fin k → ℝ) × (Fin k → ℝ) =>
      (q.1,q.2,0,0) : _ → BishopParams k) (𝓝 0) (𝓝 0) := by
    exact (by fun_prop : ContinuousAt (fun q : (Fin k → ℝ) × (Fin k → ℝ) =>
      (q.1,q.2,0,0) : _ → BishopParams k) 0)
  filter_upwards [ht.eventually hY] with q hq
  funext i
  dsimp only [bishopNormal]
  rw [hq rfl rfl i,mul_smul_comm,map_smul]
  change 2*(q.2 i*realMean (κ*η)) = (2*realMean (κ*η))*q.2 i
  ring

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_BishopDiscRadialExpansion
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
namespace Release061

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem eventually_isUnit_partial {F : P × E → E} {c : ℝ}
    (hc : c ≠ 0) (hF : ContDiffAt ℝ 1 F 0)
    (hzero : ∀ᶠ e in 𝓝 (0 : E), F (0,e) = c • e) :
    ∀ᶠ p in 𝓝 (0 : P), IsUnit (fderiv ℝ (fun e => F (p,e)) 0) := by
  have hd0 : fderiv ℝ (fun e => F (0,e)) 0 = c • ContinuousLinearMap.id ℝ E := by
    exact (((c • ContinuousLinearMap.id ℝ E).hasFDerivAt (x := 0)).congr_of_eventuallyEq hzero).fderiv
  have hu0 : IsUnit (c • ContinuousLinearMap.id ℝ E) := by
    have h := (isUnit_iff_ne_zero.mpr hc).map (algebraMap ℝ (E →L[ℝ] E))
    simpa only [Algebra.algebraMap_eq_smul_one,ContinuousLinearMap.one_def] using h
  have hcont : ContinuousAt (fun p => fderiv ℝ (fun e => F (p,e)) 0) (0 : P) := by
    have hh : ContDiffAt ℝ 0 (fun p => fderiv ℝ (fun e => F (p,e)) 0) (0 : P) :=
      hF.fderiv contDiffAt_const (by norm_num)
    exact hh.continuousAt
  exact hcont.eventually (Units.isOpen.mem_nhds (by change IsUnit (fderiv ℝ (fun e => F (0,e)) 0); rw [hd0]; exact hu0))

end Release061

namespace Release061.Wiener

theorem bishopNormal_transverse {k : ℕ} {κ η : realAlgebra}
    {Y : BishopParams k → BoundarySpace k}
    (hY : ContDiffAt ℝ ∞ Y 0)
    (hzero : ∀ᶠ p in 𝓝 0, p.2.2.1 = 0 → p.2.2.2 = 0 → ∀ i, Y p i = p.2.1 i • η)
    (hη : 0 < 2*realMean (κ*η)) :
    ∀ᶠ α in 𝓝 (0 : ℝ), IsUnit
      (fderiv ℝ (fun e : Fin k → ℝ => bishopNormal κ Y (0,e,α,0)) 0) := by
  let F : ℝ × (Fin k → ℝ) → Fin k → ℝ := fun q => bishopNormal κ Y (0,q.2,q.1,0)
  have hF : ContDiffAt ℝ 1 F 0 := by
    have hN : ContDiffAt ℝ 1 (bishopNormal κ Y) 0 :=
      (bishopNormal_smooth κ hY).of_le (by simp)
    have hP : ContDiffAt ℝ 1 (fun q : ℝ × (Fin k → ℝ) =>
        ((0 : Fin k → ℝ),q.2,q.1,0) : _ → BishopParams k) 0 := by fun_prop
    exact hN.comp (f := fun q : ℝ × (Fin k → ℝ) =>
      ((0 : Fin k → ℝ),q.2,q.1,0)) 0 hP
  have hzq := bishopNormal_zero_deformation (κ := κ) hzero
  have ht : Tendsto (fun e : Fin k → ℝ => ((0 : Fin k → ℝ),e)) (𝓝 0) (𝓝 0) := by
    exact (by fun_prop : ContinuousAt (fun e : Fin k → ℝ => ((0 : Fin k → ℝ),e)) 0)
  have hz : ∀ᶠ e in 𝓝 (0 : Fin k → ℝ), F (0,e) = (2*realMean (κ*η)) • e := by
    exact ht.eventually hzq
  exact eventually_isUnit_partial hη.ne' hF hz

lemma bishopDisc_constant_branch {k : ℕ}
    {f : (Fin (k+1) → ℝ) → Fin k → ℝ} {lam η : realAlgebra}
    {X Y : BishopParams k → BoundarySpace k}
    (hEq : ∀ᶠ p in 𝓝 0, ∀ θ i, realEvaluation θ (Y p i) =
      f (Fin.cons (p.2.2.1*realEvaluation θ lam+p.2.2.2)
        (fun j => realEvaluation θ (X p j))) i+realEvaluation θ η*p.2.1 i)
    (hconst : ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ),
      X (q.1,0,0,q.2) = fun i => constantReal (q.1 i)) :
    ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ), ∀ i (z : ClosedDisc),
      bishopDisc Y (q.1,0,0,q.2) i z =
        (q.1 i : ℂ)+Complex.I*(f (Fin.cons q.2 q.1) i : ℂ) := by
  have ht : Tendsto (fun q : (Fin k → ℝ) × ℝ =>
      (q.1,0,0,q.2) : _ → BishopParams k) (𝓝 0) (𝓝 0) :=
    (by fun_prop : ContinuousAt (fun q : (Fin k → ℝ) × ℝ =>
      (q.1,0,0,q.2) : _ → BishopParams k) 0)
  filter_upwards [ht.eventually hEq,hconst] with q hq hc
  have he (i : Fin k) : Y (q.1,0,0,q.2) i = constantReal (f (Fin.cons q.2 q.1) i) := by
    apply realEvaluation_ext
    intro θ
    rw [hq θ i,hc,realEvaluation_constant]
    simp only [zero_mul,zero_add,Pi.zero_apply,mul_zero,add_zero,realEvaluation_constant]
  intro i z
  change constantDisc (q.1 i) z+realSchwarz (Y (q.1,0,0,q.2) i) z = _
  rw [constantDisc_apply,he]
  rw [schwarz_constant]
  rfl

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_LocalBishopData
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.radiusCircleCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
namespace Release061.Wiener
open scoped Topology
open Set Filter Metric

theorem localBishopData_exists {k : ℕ} {f : (Fin (k+1) → ℝ) → Fin k → ℝ}
    (hf : AnalyticAt ℝ f 0)
    (hf0 : ∀ᶠ X in 𝓝 (0 : Fin k → ℝ), f (Fin.cons 0 X) = 0)
    {ε : ℝ} (hε : 0 < ε) : Nonempty (LocalBishopData k f ε) := by
  obtain ⟨lam,eta,kappa,hn,hz,hs,hd,hpos⟩ := exists_transverse_cutoffs
  obtain ⟨X,Y,hX0,hY0,hX,hY,hEq,hconst⟩ := bishop_boundary_solution_with_constants hf hf0 lam eta
  have hloc := bishop_boundary_localization hf0 hz hX0 hX.continuousAt (hEq.mono fun _ h => h.2)
  have ht := bishopNormal_transverse hY (hloc.mono fun _ h => h.2) hpos
  have hconstant := bishopDisc_constant_branch (hEq.mono fun _ h => h.2) hconst
  obtain ⟨r₁,hr₁,hrc⟩ := Metric.mem_nhds_iff.mp hconstant
  have hD0 : bishopDisc Y 0 = 0 := by
    ext i z
    simp [bishopDisc,hY0]
  have hsmall : ∀ᶠ p in 𝓝 0, ‖X p‖ < ε ∧ ‖Y p‖ < ε ∧ ‖bishopDisc Y p‖ < ε := by
    have hx := hX.continuousAt.norm.eventually (eventually_lt_nhds (by simpa [hX0] using hε))
    have hy := hY.continuousAt.norm.eventually (eventually_lt_nhds (by simpa [hY0] using hε))
    have hb := (bishopDisc_smooth hY).continuousAt.norm.eventually
      (eventually_lt_nhds (by simpa [hD0] using hε))
    exact hx.and (hy.and hb)
  obtain ⟨V,hV,hXV⟩ := hX.contDiffOn (m := 1) (by simp) (by simp)
  obtain ⟨W,hW,hYW⟩ := hY.contDiffOn (m := 1) (by simp) (by simp)
  have hall : ∀ᶠ p in 𝓝 (0 : BishopParams k), p ∈ V ∧ p ∈ W ∧
      (‖X p‖ < ε ∧ ‖Y p‖ < ε ∧ ‖bishopDisc Y p‖ < ε) ∧ _ :=
    Filter.Eventually.and hV (Filter.Eventually.and hW (hsmall.and (hEq.and hloc)))
  obtain ⟨r₂,hr₂,hrall⟩ := Metric.mem_nhds_iff.mp hall
  let r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  have hdata (p : BishopParams k) (hp : p ∈ ball 0 r) :=
    hrall ((ball_subset_ball (min_le_right _ _)) hp)
  refine ⟨⟨lam,eta,kappa,X,Y,r,hr,hn,hz,hs,hd,?_,?_,?_,?_,?_,?_,ht⟩⟩
  · exact hXV.mono fun p hp => (hdata p hp).1
  · exact hYW.mono fun p hp => (hdata p hp).2.1
  · intro p hp
    exact (hdata p hp).2.2.1
  · intro p hp
    exact (hdata p hp).2.2.2.1
  · intro p hp
    exact (hdata p hp).2.2.2.2.1
  · intro q hq
    exact hrc ((ball_subset_ball (min_le_left _ _)) hq)

end Release061.Wiener

open Set Metric

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_BishopPathInterior
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.radiusCircleCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
namespace Release061.Wiener
open scoped Topology
open Set Filter Metric

lemma imaginaryVector_norm {k : ℕ} (e : Fin k → ℝ) : ‖imaginaryVector e‖ = ‖e‖ := by
  simp only [Pi.norm_def,imaginaryVector,nnnorm_mul,Complex.nnnorm_I,Complex.nnnorm_real,one_mul]

lemma bishopDisc_contDiffAt_at {k : ℕ} {Y : BishopParams k → BoundarySpace k}
    {p : BishopParams k} (hY : ContDiffAt ℝ 1 Y p) :
    ContDiffAt ℝ 1 (bishopDisc Y) p := by
  apply contDiffAt_pi.mpr
  intro i
  apply ContDiffAt.add
  · fun_prop
  · exact realSchwarz.contDiff.contDiffAt.comp _ (contDiffAt_pi.mp hY i)

lemma bishopDisc_eval_norm_le {k : ℕ} (Y : BishopParams k → BoundarySpace k)
    (p : BishopParams k) (z : ClosedDisc) :
    ‖fun i => bishopDisc Y p i z‖ ≤ ‖bishopDisc Y p‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact ((bishopDisc Y p i).norm_coe_le_norm z).trans (norm_le_pi_norm _ i)

lemma fourier_one_surjective_sphere {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ θ : Circle, fourier 1 θ = z := by
  let c : _root_.Circle := ⟨z,by simpa [Submonoid.unitSphere,Metric.mem_sphere,dist_zero_right] using hz⟩
  obtain ⟨θ,hθ⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective c
  refine ⟨θ,?_⟩
  rw [AddCircle.homeomorphCircle_apply] at hθ
  simpa only [fourier_one] using congrArg (fun x : _root_.Circle => (x : ℂ)) hθ

lemma bishopParams_mem_ball {k : ℕ} {b e : Fin k → ℝ} {s δ r : ℝ}
    (hb : ‖b‖ < r) (he : ‖e‖ < r) (hs : |s| < r) (hδ : |δ| < r) :
    (b,e,s,δ) ∈ ball (0 : BishopParams k) r := by
  simpa only [mem_ball,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_lt_iff]
    using And.intro hb (And.intro he (And.intro hs hδ))

lemma bishop_boundary_eq_graph {k : ℕ} {f : (Fin (k+1) → ℝ) → Fin k → ℝ}
    {ε : ℝ} (D : LocalBishopData k f ε) {p : BishopParams k}
    (hp : p ∈ ball 0 D.radius) (θ : Circle) :
    (fun i => bishopDisc D.Y p i ⟨fourier 1 θ,fourier_mem_closedDisc θ⟩) =
      graphPoint f ((fun i => realEvaluation θ (D.X p i)),
        p.2.2.1*realEvaluation θ D.lam+p.2.2.2)+
          realEvaluation θ D.eta • imaginaryVector p.2.1 := by
  funext i
  rw [bishopDisc_boundary (D.equation p hp).1 θ i,(D.equation p hp).2 θ i]
  simp only [graphPoint,imaginaryVector,Pi.add_apply,Pi.smul_apply,Complex.real_smul,
    Complex.ofReal_add,Complex.ofReal_mul]
  ring

lemma bishop_path_interior {k : ℕ} {f : (Fin (k+1) → ℝ) → Fin k → ℝ}
    {ε : ℝ} (D : LocalBishopData k f ε) {Ω : Set (Fin k → ℂ)}
    (hCP : DiscContinuityWithin k Ω ε)
    (p : Icc (0 : ℝ) 1 → BishopParams k) (hp : Continuous p)
    (hpr : ∀ s, p s ∈ ball 0 D.radius)
    (hbd : ∀ s θ, (fun i => bishopDisc D.Y (p s) i
      ⟨fourier 1 θ,fourier_mem_closedDisc θ⟩) ∈ Ω)
    (hstart : ∀ z, (fun i => bishopDisc D.Y (p ⟨0,by simp⟩) i z) ∈ Ω) :
    ∀ s z, (fun i => bishopDisc D.Y (p s) i z) ∈ Ω := by
  apply hCP
  · have hc : ContinuousOn (bishopDisc D.Y) (ball 0 D.radius) := by
      intro q hq
      exact (bishopDisc_contDiffAt_at
        ((D.smoothY q hq).contDiffAt (isOpen_ball.mem_nhds hq))).continuousAt.continuousWithinAt
    have hB : Continuous (fun s => bishopDisc D.Y (p s)) := hc.comp_continuous hp hpr
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp (hB.comp continuous_fst)).eval continuous_snd
  · intro s
    refine ⟨fun z i => ((p s).1 i : ℂ)+discValue (D.Y (p s) i) z,
      bishopDisc_analytic D.Y (p s),?_⟩
    intro z
    funext i
    change constantDisc ((p s).1 i) z+schwarz (D.Y (p s) i) z = _
    rw [constantDisc_apply,← discValue_eq _ z.property]
  · intro s z
    exact lt_of_le_of_lt (bishopDisc_eval_norm_le D.Y (p s) z) (D.small (p s) (hpr s)).2.2
  · intro s z hz
    obtain ⟨θ,hθ⟩ := fourier_one_surjective_sphere hz
    have heq : z = ⟨fourier 1 θ,fourier_mem_closedDisc θ⟩ := Subtype.ext hθ.symm
    simpa only [heq] using hbd s θ
  · exact hstart

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_Vector
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
namespace Release061.Wiener
open Set Filter Metric
open scoped Topology

theorem discContinuityWithin_pullback {k l : ℕ} {Ω : Set (Fin l → ℂ)}
    {S : Set (Fin k → ℂ)} {r ε : ℝ} {Φ : (Fin k → ℂ) → Fin l → ℂ}
    (hCP : DiscContinuityWithin l Ω ε)
    (hΦ : AnalyticOnNhd ℂ Φ (ball 0 r))
    (hS : ball 0 r ⊆ S) (hsmall : MapsTo Φ (ball 0 r) (ball 0 ε)) :
    DiscContinuityWithin k (S ∩ Φ ⁻¹' Ω) r := by
  intro A hA hAh hAr hbd hstart
  let B : Icc (0 : ℝ) 1 → ClosedDisc → Fin l → ℂ := fun s z => Φ (A s z)
  have hB : Continuous (Function.uncurry B) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (hΦ _ (mem_ball_zero_iff.mpr (hAr p.1 p.2))).continuousAt.comp (f := Function.uncurry A) hA.continuousAt
  have hBh (s : Icc (0 : ℝ) 1) : ∃ g : ℂ → Fin l → ℂ,
      AnalyticOnNhd ℂ g (ball 0 1) ∧ ∀ z : ClosedDisc, B s z = g z := by
    obtain ⟨g,hg,he⟩ := hAh s
    refine ⟨Φ ∘ g,hΦ.comp hg ?_,fun z => congrArg Φ (he z)⟩
    intro z hz
    rw [← he ⟨z,ball_subset_closedBall hz⟩]
    exact mem_ball_zero_iff.mpr (hAr s _)
  have hBj (s : Icc (0 : ℝ) 1) (z : ClosedDisc) : ‖B s z‖ < ε :=
    mem_ball_zero_iff.mp (hsmall (mem_ball_zero_iff.mpr (hAr s z)))
  have hBi := hCP B hB hBh hBj (fun s z hz => (hbd s z hz).2) (fun z => (hstart z).2)
  exact fun s z => ⟨hS (mem_ball_zero_iff.mpr (hAr s z)),hBi s z⟩

end Release061.Wiener

open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Complexify
variable {d j : ℕ}

lemma monomial_apply (σ : Fin j → Fin d) (x : Fin j → Fin d → ℂ) :
    monomial σ x = ∏ i, x i (σ i) := by
  simp [monomial,ContinuousMultilinearMap.mkPiAlgebraFin_apply,List.prod_ofFn]

lemma monomial_norm_le (σ : Fin j → Fin d) : ‖monomial σ‖ ≤ 1 := by
  apply ContinuousMultilinearMap.opNorm_le_bound zero_le_one
  intro x
  rw [monomial_apply,one_mul]
  exact (Finset.norm_prod_le _ _).trans (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    (fun i _ => norm_le_pi_norm (x i) (σ i)))

lemma coefficient_norm_le (p : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) ℝ) :
    ‖coefficient p‖ ≤ (d : ℝ)^j * ‖p‖ := by
  classical
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : Fin j → Fin d, ‖p‖ := by
      apply Finset.sum_le_sum
      intro σ _
      rw [norm_smul]
      exact (mul_le_mul (p.unit_le_opNorm ((pi_norm_le_iff_of_nonneg zero_le_one).mpr (by
        intro i
        exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (by
          intro k
          by_cases h : k = σ i <;> simp [h]))))
        (monomial_norm_le σ) (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_one _)
    _ = _ := by simp

lemma coordinate_expansion
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) ℝ)
    (x : Fin j → Fin d → ℝ) :
    p x = ∑ σ : Fin j → Fin d, p (fun i => Pi.single (σ i) 1) * ∏ i, x i (σ i) := by
  classical
  have hx : x = fun i => ∑ k : Fin d, x i k • Pi.single k 1 := by
    funext i l
    simp [Finset.sum_apply,Pi.single_apply]
  conv_lhs => rw [hx,p.map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [p.map_smul_univ]
  simp only [smul_eq_mul,mul_comm]

lemma coefficient_real
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) ℝ)
    (x : Fin j → Fin d → ℝ) :
    coefficient p (fun i k => (x i k : ℂ)) = (p x : ℂ) := by
  classical
  rw [coordinate_expansion]
  simp only [coefficient, sum_apply,smul_apply,monomial_apply,Complex.real_smul,
    Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_prod]

lemma radius_lower_bound (p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ)
    {r : ℝ≥0} (hr : (r : ℝ≥0∞) < p.radius) :
    (r / (d+1 : ℝ≥0) : ℝ≥0) ≤ (series p).radius := by
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  apply (p.summable_norm_mul_pow hr).of_nonneg_of_le
  · intro j; positivity
  · intro j
    have hd : (0 : ℝ) < d+1 := by positivity
    have hd' : (d : ℝ)/(d+1) ≤ 1 := (div_le_one hd).mpr (by linarith)
    calc
      _ ≤ ((d : ℝ)^j*‖p j‖) * ((r : ℝ)/(d+1))^j := by
        exact mul_le_mul_of_nonneg_right (coefficient_norm_le (p j)) (by positivity)
      _ = ‖p j‖ * (r : ℝ)^j * ((d : ℝ)/(d+1))^j := by rw [div_pow,div_pow]; ring
      _ ≤ ‖p j‖ * (r : ℝ)^j * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity) hd') (by positivity)
      _ = _ := mul_one _

lemma radius_pos (p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ)
    (hp : 0 < p.radius) : 0 < (series p).radius := by
  obtain ⟨r,hr0,hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp
  apply lt_of_lt_of_le _ (radius_lower_bound p hr)
  exact ENNReal.coe_pos.mpr (div_pos (ENNReal.coe_pos.mp hr0) (by positivity))

lemma norm_real_vector (x : Fin d → ℝ) : ‖fun i => (x i : ℂ)‖ = ‖x‖ := by
  simp only [Pi.norm_def,Complex.nnnorm_real]

lemma series_real {f : (Fin d → ℝ) → ℝ}
    {p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ} {R : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p 0 R) {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) < R) {x : Fin d → ℝ} (hx : ‖x‖ < (r : ℝ)/(d+1)) :
    (series p).sum (fun i => (x i : ℂ)) = (f x : ℂ) := by
  have hp : 0 < (series p).radius := radius_pos p hf.radius_pos
  have hxq : (fun i => (x i : ℂ)) ∈ Metric.eball 0 (series p).radius := by
    apply Metric.eball_subset_eball (radius_lower_bound p (hr.trans_le hf.r_le))
    rw [Metric.eball_coe,Metric.mem_ball,dist_zero_right,norm_real_vector]
    simpa only [NNReal.coe_div,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using hx
  have hxp : x ∈ Metric.eball 0 R := by
    apply Metric.eball_subset_eball hr.le
    rw [Metric.eball_coe,Metric.mem_ball,dist_zero_right]
    exact hx.trans_le (div_le_self (by positivity) (le_add_of_nonneg_left (Nat.cast_nonneg d)))
  have H := Complex.ofRealCLM.hasSum (hf.hasSum hxp)
  have Hq := ((series p).hasFPowerSeriesOnBall hp).hasSum hxq
  simp only [zero_add] at H Hq
  simp only [series,coefficient_real] at Hq
  exact Hq.unique H

theorem scalar {f : (Fin d → ℝ) → ℝ} (hf : AnalyticAt ℝ f 0) :
    ∃ g : (Fin d → ℂ) → ℂ, AnalyticAt ℂ g 0 ∧
      ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), g (fun i => (x i : ℂ)) = (f x : ℂ) := by
  obtain ⟨p,R,hp⟩ := hf
  obtain ⟨r,hr0,hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  refine ⟨(series p).sum,((series p).hasFPowerSeriesOnBall (radius_pos p hp.radius_pos)).analyticAt,?_⟩
  have he : 0 < (r : ℝ)/(d+1) := div_pos (ENNReal.coe_pos.mp hr0) (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0 : Fin d → ℝ) he] with x hx
  exact series_real hp hr (by simpa only [Metric.mem_ball,dist_zero_right] using hx)

theorem vector {k : ℕ} {f : (Fin d → ℝ) → Fin k → ℝ} (hf : AnalyticAt ℝ f 0) :
    ∃ g : (Fin d → ℂ) → Fin k → ℂ, AnalyticAt ℂ g 0 ∧
      ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), g (fun i => (x i : ℂ)) = fun i => (f x i : ℂ) := by
  have hfi := analyticAt_pi_iff.mp hf
  choose g hg he using fun i => scalar (hfi i)
  refine ⟨fun z i => g i z,analyticAt_pi_iff.mpr hg,?_⟩
  filter_upwards [Filter.eventually_all.mpr he] with x hx
  exact funext hx

end Release061.Complexify

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_HorizontalGraphComplexification
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Flatten
open Set Filter
open scoped Topology

theorem real_analytic_local_inverse
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {a : E} (hf : AnalyticAt ℝ f a)
    (i : E ≃L[ℝ] F) (hi : HasFDerivAt f (i : E →L[ℝ] F) a) :
    ∃ e : OpenPartialHomeomorph E F, (e : E → F) = f ∧ a ∈ e.source ∧
      AnalyticAt ℝ e.symm (f a) := by
  have hs : HasStrictFDerivAt f (i : E →L[ℝ] F) a := by
    simpa only [hi.fderiv] using hf.hasStrictFDerivAt
  let e := hs.toOpenPartialHomeomorph f
  refine ⟨e, hs.toOpenPartialHomeomorph_coe, hs.mem_toOpenPartialHomeomorph_source, ?_⟩
  obtain ⟨p, hp⟩ := hf
  have he : (e : E → F) = f := hs.toOpenPartialHomeomorph_coe
  have hpe : HasFPowerSeriesAt e p a := he ▸ hp
  have hcoeff : p 1 = (continuousMultilinearCurryFin1 ℝ E F).symm
      (i : E →L[ℝ] F) := by
    apply (continuousMultilinearCurryFin1 ℝ E F).injective
    simpa using hp.hasFDerivAt.unique hi
  simpa only [he] using
    (e.hasFPowerSeriesAt_symm hs.mem_toOpenPartialHomeomorph_source hpe hcoeff).analyticAt

end Release061.Flatten

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticReparameterization
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Flatten
open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem analytic_reparameterization [CompleteSpace E] {f : E × ℝ → E}
    (hf : AnalyticAt ℝ f 0) (hzero : ∀ᶠ x in 𝓝 (0 : E), f (x,0) = x) :
    ∃ e : OpenPartialHomeomorph (E × ℝ) (E × ℝ),
      (∀ q, e q = (f q,q.2)) ∧ (0 : E × ℝ) ∈ e.source ∧ e 0 = 0 ∧
      AnalyticAt ℝ e.symm 0 ∧
      (∀ᶠ q in 𝓝 (0 : E × ℝ), (e.symm q).2 = q.2) ∧
      (∀ᶠ x in 𝓝 (0 : E), e.symm (x,0) = (x,0)) := by
  let L := fderiv ℝ f 0
  have hd : HasFDerivAt f L 0 := hf.differentiableAt.hasFDerivAt
  have hinl : L ∘L (ContinuousLinearMap.inl ℝ E ℝ) = ContinuousLinearMap.id ℝ E := by
    have h := hd.comp (0 : E) (ContinuousLinearMap.inl ℝ E ℝ).hasFDerivAt
    have h' : HasFDerivAt (fun x : E => x) (L ∘L ContinuousLinearMap.inl ℝ E ℝ) 0 :=
      h.congr_of_eventuallyEq (hzero.mono fun x hx => hx.symm)
    exact h'.unique (hasFDerivAt_id 0)
  have hL (x : E) (u : ℝ) : L (x,u) = x+u•L (0,1) := by
    have he : (x,u) = (x,0)+u•(0,(1:ℝ)) := by simp
    rw [he,map_add,map_smul]
    have h := congrArg (fun A : E →L[ℝ] E => A x) hinl
    change L (x,0) = x at h
    rw [h]
  let H : E × ℝ → E × ℝ := fun q => (f q,q.2)
  have hH : AnalyticAt ℝ H 0 := hf.prod ((ContinuousLinearMap.snd ℝ E ℝ).analyticAt 0)
  have hHd : HasFDerivAt H (shearEquiv (L (0,1))).toContinuousLinearMap 0 := by
    have he : L.prod (ContinuousLinearMap.snd ℝ E ℝ) = (shearEquiv (L (0,1))).toContinuousLinearMap := by
      apply ContinuousLinearMap.ext
      intro q
      exact Prod.ext (hL q.1 q.2) rfl
    rw [← he]
    exact hd.prodMk hasFDerivAt_snd
  have hH0 : H 0 = 0 := by
    have h := hzero.self_of_nhds
    change f (0,0) = 0 at h
    exact Prod.ext h rfl
  obtain ⟨e,he,hem,hia⟩ := real_analytic_local_inverse hH (shearEquiv (L (0,1))) hHd
  have he0 : e 0 = 0 := by rw [he,hH0]
  refine ⟨e,(fun q => congrFun he q),hem,he0,by simpa only [hH0] using hia,?_,?_⟩
  · have htar : (0 : E × ℝ) ∈ e.target := he0 ▸ e.map_source hem
    filter_upwards [e.open_target.mem_nhds htar] with q hq
    have h := congrArg Prod.snd (e.right_inv hq)
    simpa only [he,H] using h
  · have ht : Tendsto (fun x : E => (x,(0:ℝ))) (𝓝 0) (𝓝 (0 : E × ℝ)) := by
      change Tendsto _ (𝓝 0) (𝓝 (0,(0:ℝ)))
      exact (continuous_id.prodMk continuous_const).continuousAt.tendsto
    filter_upwards [hzero,ht (e.open_source.mem_nhds hem)] with x hx hxsrc
    have h : e (x,0) = (x,0) := by rw [he]; exact Prod.ext hx rfl
    calc
      e.symm (x,0) = e.symm (e (x,0)) := congrArg e.symm h.symm
      _ = (x,0) := e.left_inv hxsrc

end Release061.Flatten

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticFamilyRegraph
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Flatten
open Set Filter
open scoped Topology

theorem analytic_family_regraph {k : ℕ}
    {G : (Fin k → ℝ) × ℝ → Fin k → ℂ} (hG : AnalyticAt ℝ G 0)
    (hG0 : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), G (x,0) = realEmbedding k x)
    {Ω : Set (Fin k → ℂ)}
    (hΩ : ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ), 0 < q.2 → G q ∈ Ω) :
    ∃ f : (Fin (k+1) → ℝ) → Fin k → ℝ, AnalyticAt ℝ f 0 ∧
      (∀ᶠ x in 𝓝 (0 : Fin k → ℝ), f (Fin.cons 0 x) = 0) ∧
      ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ), 0 < q.2 →
        (fun i => (q.1 i : ℂ)+Complex.I*(f (Fin.cons q.2 q.1) i : ℂ)) ∈ Ω := by
  have hreal : AnalyticAt ℝ (fun q => realPart k (G q)) 0 :=
    (realPart k).analyticAt _ |>.comp hG
  have hreal0 : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), realPart k (G (x,0)) = x := by
    filter_upwards [hG0] with x hx
    rw [hx]
    rfl
  obtain ⟨e,he,hem,he0,hia,hsnd,hbase⟩ := analytic_reparameterization hreal hreal0
  have hei0 : e.symm 0 = 0 := by
    calc e.symm 0 = e.symm (e 0) := congrArg e.symm he0.symm
         _ = 0 := e.left_inv hem
  let P : (Fin (k+1) → ℝ) →L[ℝ] ((Fin k → ℝ) × ℝ) :=
    (ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj i.succ)).prod
      (ContinuousLinearMap.proj 0)
  have hP (q : (Fin k → ℝ) × ℝ) : P (Fin.cons q.2 q.1) = q := by
    apply Prod.ext
    · ext i
      change (Fin.cons q.2 q.1 : Fin (k+1) → ℝ) i.succ = q.1 i
      exact Fin.cons_succ _ _ i
    · change (Fin.cons q.2 q.1 : Fin (k+1) → ℝ) 0 = q.2
      exact Fin.cons_zero _ _
  let f : (Fin (k+1) → ℝ) → Fin k → ℝ :=
    fun z => imaginaryPart k (G (e.symm (P z)))
  have ha : AnalyticAt ℝ (fun q => imaginaryPart k (G (e.symm q))) 0 := by
    have hG' : AnalyticAt ℝ G (e.symm 0) := by rwa [hei0]
    exact (imaginaryPart k).analyticAt _ |>.comp (hG'.comp hia)
  refine ⟨f,?_,?_,?_⟩
  · have ha' : AnalyticAt ℝ (fun q => imaginaryPart k (G (e.symm q))) (P 0) := by
      simpa only [map_zero] using ha
    exact ha'.comp (P.analyticAt 0)
  · filter_upwards [hbase,hG0] with x hx hx0
    change imaginaryPart k (G (e.symm (P (Fin.cons 0 x)))) = 0
    rw [hP (x,0),hx,hx0]
    ext i
    simp [imaginaryPart,realEmbedding]
  · have ht : Tendsto e.symm (𝓝 0) (𝓝 (0 : (Fin k → ℝ) × ℝ)) := by
      simpa only [hei0] using hia.continuousAt.tendsto
    have htar : (0 : (Fin k → ℝ) × ℝ) ∈ e.target := he0 ▸ e.map_source hem
    filter_upwards [e.open_target.mem_nhds htar,hsnd,ht hΩ] with q hq hqs hqi
    intro hu
    have hr : realPart k (G (e.symm q)) = q.1 := by
      have hh := congrArg Prod.fst (e.right_inv hq)
      simpa only [he] using hh
    have hEq : (fun i => (q.1 i : ℂ)+Complex.I*(f (Fin.cons q.2 q.1) i : ℂ)) = G (e.symm q) := by
      ext i
      have hi := congrFun hr i
      change (G (e.symm q) i).re = q.1 i at hi
      dsimp [f]
      rw [hP]
      change (q.1 i : ℂ)+Complex.I*((G (e.symm q) i).im : ℂ) = _
      rw [← hi,mul_comm,Complex.re_add_im]
    rw [hEq]
    exact hqi (by rwa [hqs])

end Release061.Flatten

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GraphBoundaryFirstHomotopy
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
namespace Release061

section
variable {P E : Type*} [TopologicalSpace P] [NormedAddCommGroup E]

lemma compact_image_perturbation {K : Set P} (hK : IsCompact K)
    {G : P → E} (hG : ContinuousOn G K) {Ω : Set E} (hΩ : IsOpen Ω)
    (himage : G '' K ⊆ Ω) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ K, ∀ v : E, ‖v‖ < ε → G p+v ∈ Ω := by
  obtain ⟨ε,hε,hsub⟩ := (hK.image_of_continuousOn hG).exists_thickening_subset_open hΩ himage
  refine ⟨ε,hε,?_⟩
  intro p hp v hv
  apply hsub
  apply mem_thickening_iff.mpr
  exact ⟨G p,mem_image_of_mem G hp,by simpa only [dist_eq_norm,add_sub_cancel_left] using hv⟩

end

open Set Metric
variable {E F Θ : Type*} [NormedAddCommGroup E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem graph_boundary_perturbation
    {Ω : Set F} (hΩ : IsOpen Ω) {G : E × ℝ → F}
    {r u₀ α d L M : ℝ} (hα : 0 < α)
    (hL : 1 ≤ L) (hM : 0 ≤ M) (hu : α*L+d < u₀)
    (hG : ContinuousOn G (closedBall 0 r ×ˢ Icc α (α+d)))
    (hgraph : ∀ x ∈ closedBall 0 r, ∀ u ∈ Ioo 0 u₀, G (x,u) ∈ Ω)
    {lam eta : Θ → ℝ} (hlam : ∀ θ, 0 ≤ lam θ ∧ lam θ ≤ L)
    (heta : ∀ θ, |eta θ| ≤ M)
    (hsupport : ∀ θ, eta θ ≠ 0 → lam θ = 1) :
    ∃ e₀ : ℝ, 0 < e₀ ∧ ∀ x ∈ closedBall 0 r, ∀ θ, ∀ δ ∈ Ioc 0 d,
      ∀ e : F, ‖e‖ < e₀ → G (x,α*lam θ+δ)+eta θ • e ∈ Ω := by
  have hαL : α ≤ α*L := by nlinarith
  have himage : G '' (closedBall 0 r ×ˢ Icc α (α+d)) ⊆ Ω := by
    rintro _ ⟨⟨x,u⟩,⟨hx,hu'⟩,rfl⟩
    exact hgraph x hx u ⟨lt_of_lt_of_le hα hu'.1,by linarith [hu'.2]⟩
  obtain ⟨ε,hε,hpert⟩ := compact_image_perturbation
    ((isCompact_closedBall (0 : E) r).prod isCompact_Icc) hG hΩ himage
  refine ⟨ε/(M+1),div_pos hε (by positivity),?_⟩
  intro x hx θ δ hδ e he
  by_cases hη : eta θ = 0
  · rw [hη,zero_smul,add_zero]
    exact hgraph x hx _ ⟨by nlinarith [(hlam θ).1,hδ.1],by nlinarith [(hlam θ).2,hδ.2]⟩
  · rw [hsupport θ hη,mul_one]
    apply hpert (x,α+δ) ⟨hx,⟨by linarith [hδ.1],by linarith [hδ.2]⟩⟩
    rw [norm_smul,Real.norm_eq_abs]
    have hsmall : (M+1)*‖e‖ < ε := by
      have := (lt_div_iff₀ (by positivity : 0 < M+1)).mp he
      nlinarith
    calc |eta θ| * ‖e‖ ≤ M*‖e‖ := mul_le_mul_of_nonneg_right (heta θ) (norm_nonneg _)
      _ ≤ (M+1)*‖e‖ := by nlinarith [norm_nonneg e]
      _ < ε := hsmall

omit [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] in

lemma graph_boundary_first_homotopy
    {Ω : Set F} {G : E × ℝ → F} {r u₀ α d L : ℝ}
    (hα : 0 ≤ α) (hu : α*L+d < u₀)
    (hgraph : ∀ x ∈ closedBall 0 r, ∀ u ∈ Ioo 0 u₀, G (x,u) ∈ Ω)
    {lam : Θ → ℝ} (hlam : ∀ θ, 0 ≤ lam θ ∧ lam θ ≤ L)
    {x : E} (hx : x ∈ closedBall 0 r) (θ : Θ)
    {s δ : ℝ} (hs : s ∈ Icc 0 α) (hδ : δ ∈ Ioc 0 d) :
    G (x,s*lam θ+δ) ∈ Ω := by
  apply hgraph x hx
  refine ⟨by nlinarith [(hlam θ).1,hs.1,hδ.1],?_⟩
  have hmul := mul_le_mul hs.2 (hlam θ).2 (hlam θ).1 hα
  linarith [hδ.2]

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_BishopPositiveInterior
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.radiusCircleCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
namespace Release061.Wiener
open scoped Topology
open Set Filter Metric

theorem bishop_positive_interior {k : ℕ} {f : (Fin (k+1) → ℝ) → Fin k → ℝ}
    {ε : ℝ} (D : LocalBishopData k f ε) {Ω : Set (Fin k → ℂ)}
    (hΩ : IsOpen Ω) (hCP : DiscContinuityWithin k Ω ε)
    {α d u₀ L : ℝ} (hα : 0 < α) (hαr : α < D.radius)
    (hdr : d < D.radius) (hL : 1 ≤ L) (hu : α*L+d < u₀)
    (hG : ContinuousOn (graphPoint f) (closedBall 0 ε ×ˢ Icc α (α+d)))
    (hgraph : ∀ x ∈ closedBall 0 ε, ∀ u ∈ Ioo 0 u₀, graphPoint f (x,u) ∈ Ω)
    (hlam : ∀ θ, realEvaluation θ D.lam ≤ L) :
    ∃ e₀ : ℝ, 0 < e₀ ∧ ∀ b : Fin k → ℝ, ‖b‖ < D.radius →
      ∀ e : Fin k → ℝ, ‖e‖ < e₀ → ∀ δ ∈ Ioc 0 d, ∀ z : ClosedDisc,
        (fun i => bishopDisc D.Y (b,e,α,δ) i z) ∈ Ω := by
  obtain ⟨e₁,he₁,hpert⟩ := Release061.graph_boundary_perturbation hΩ hα hL (norm_nonneg D.eta) hu
    hG hgraph (fun θ => ⟨(D.cut_nonneg θ).1,hlam θ⟩)
    (fun θ => realEvaluation_bound θ D.eta) D.cut_nested
  let e₀ := min D.radius e₁
  have he₀ : 0 < e₀ := lt_min D.radius_pos he₁
  refine ⟨e₀,he₀,?_⟩
  intro b hb e he δ hδ z
  have her : ‖e‖ < D.radius := he.trans_le (min_le_left _ _)
  have hδr : |δ| < D.radius := by rw [abs_of_pos hδ.1]; exact hδ.2.trans_lt hdr
  have hx {p : BishopParams k} (hp : p ∈ ball 0 D.radius) (θ : Circle) :
      (fun i => realEvaluation θ (D.X p i)) ∈ closedBall 0 ε := by
    exact mem_closedBall_zero_iff.mpr ((evaluation_vector_norm_le θ (D.X p)).trans (D.small p hp).1.le)
  let p₁ : Icc (0 : ℝ) 1 → BishopParams k := fun s => (b,0,(s : ℝ)*α,δ)
  have hsa (s : Icc (0 : ℝ) 1) : (s : ℝ)*α ∈ Icc 0 α :=
    ⟨mul_nonneg s.property.1 hα.le,by nlinarith [s.property.2]⟩
  have hp₁ (s : Icc (0 : ℝ) 1) : p₁ s ∈ ball 0 D.radius := by
    apply bishopParams_mem_ball hb (by simpa only [norm_zero] using D.radius_pos) _ hδr
    rw [abs_of_nonneg (hsa s).1]
    exact (hsa s).2.trans_lt hαr
  have hi₁ := bishop_path_interior D hCP p₁ (by fun_prop) hp₁ (fun s θ => ?_) (fun w => ?_)
  · let p₂ : Icc (0 : ℝ) 1 → BishopParams k := fun s => (b,(s : ℝ) • e,α,δ)
    have hse (s : Icc (0 : ℝ) 1) : ‖(s : ℝ) • e‖ ≤ ‖e‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg s.property.1]
      exact mul_le_of_le_one_left (norm_nonneg _) s.property.2
    have hp₂ (s : Icc (0 : ℝ) 1) : p₂ s ∈ ball 0 D.radius :=
      bishopParams_mem_ball hb ((hse s).trans_lt her) (by rwa [abs_of_pos hα]) hδr
    have hi₂ := bishop_path_interior D hCP p₂ (by fun_prop) hp₂ (fun s θ => ?_) (fun w => ?_)
    · simpa only [p₂,one_smul] using hi₂ ⟨1,by simp⟩ z
    · rw [bishop_boundary_eq_graph D (hp₂ s)]
      apply hpert _ (hx (hp₂ s) θ) θ δ hδ
      rw [imaginaryVector_norm]
      exact (hse s).trans_lt (he.trans_le (min_le_right _ _))
    · simpa only [p₂,p₁,zero_smul,one_mul] using hi₁ ⟨1,by simp⟩ w
  · rw [bishop_boundary_eq_graph D (hp₁ s)]
    have hz : imaginaryVector (0 : Fin k → ℝ) = 0 := by ext; simp [imaginaryVector]
    change graphPoint f ((fun i => realEvaluation θ (D.X (p₁ s) i)),
      (s : ℝ)*α*realEvaluation θ D.lam+δ)+realEvaluation θ D.eta • imaginaryVector 0 ∈ Ω
    rw [hz,smul_zero,add_zero]
    exact Release061.graph_boundary_first_homotopy hα.le hu hgraph
      (fun θ => ⟨(D.cut_nonneg θ).1,hlam θ⟩) (hx (hp₁ s) θ) θ (hsa s) hδ
  · have hq : (b,δ) ∈ ball (0 : (Fin k → ℝ) × ℝ) D.radius := by
      simpa only [mem_ball,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_lt_iff] using And.intro hb hδr
    have heq : (fun i => bishopDisc D.Y (p₁ ⟨0,by simp⟩) i w) = graphPoint f (b,δ) := by
      funext i
      simpa only [p₁,zero_mul,graphPoint] using D.constant (b,δ) hq i w
    rw [heq]
    refine hgraph b ?_ δ ?_
    · have hbε : ‖b‖ < ε := by
        have hh := (D.small (p₁ ⟨0,by simp⟩) (hp₁ ⟨0,by simp⟩)).1
        have hxconst := (D.equation (p₁ ⟨0,by simp⟩) (hp₁ ⟨0,by simp⟩)).1
        have heval : (fun i => realEvaluation (0 : Circle) (D.X (p₁ ⟨0,by simp⟩) i)) = b := by
          funext i
          rw [hxconst i]
          simp only [map_add,realEvaluation_constant,normalizedHilbert_eval_zero,add_zero,p₁]
        rw [← heval]
        exact (evaluation_vector_norm_le _ _).trans_lt hh
      exact mem_closedBall_zero_iff.mpr hbε.le
    · exact ⟨hδ.1,by have := mul_pos hα (lt_of_lt_of_le zero_lt_one hL); linarith [hδ.2]⟩

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ChoosePositiveC1Regularization
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
namespace Release061

lemma hasFDerivAt_realComplexBlock {k : ℕ} {D : (Fin k → ℝ) → Fin k → ℝ}
    (J : (Fin k → ℝ) ≃L[ℝ] (Fin k → ℝ))
    (hD : HasFDerivAt D (J : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)) 0) :
    HasFDerivAt (fun p : (Fin k → ℝ) × (Fin k → ℝ) =>
      fun i => (p.1 i : ℂ)+Complex.I*(D p.2 i : ℂ))
      (((ContinuousLinearEquiv.refl ℝ (Fin k → ℝ)).prodCongr J).trans
        (realComplexBlock k)).toContinuousLinearMap 0 := by
  have hp := ((ContinuousLinearMap.fst ℝ (Fin k → ℝ) (Fin k → ℝ)).hasFDerivAt (x := 0)).prodMk
    (hD.comp 0 (ContinuousLinearMap.snd ℝ (Fin k → ℝ) (Fin k → ℝ)).hasFDerivAt)
  exact (realComplexBlock k).hasFDerivAt.comp 0 hp

open scoped Topology
open Set Filter Metric

lemma uniformly_of_vanishing_error {ι E F : Type*} [PseudoMetricSpace F]
    {K : Set E} {f g : ι → E → F} {ψ : E → F} {l : Filter ι}
    (hf : TendstoUniformlyOn f ψ l K) {a : ι → ℝ} (ha : Tendsto a l (𝓝 0))
    (he : ∀ᶠ t in l, ∀ x ∈ K, dist (f t x) (g t x) ≤ a t) :
    TendstoUniformlyOn g ψ l K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [he,(Metric.tendstoUniformlyOn_iff.mp hf) (ε/2) (half_pos hε),
    (tendsto_order.mp ha).2 (ε/2) (half_pos hε)] with t ht hf ha
  intro x hx
  exact (dist_triangle _ _ _).trans_lt (by linarith [ht x hx,hf x hx])

theorem choose_positive_C1_regularization
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {Ω : Set F} {R : ℝ → ℝ → E → F} {ψ : E → F}
    {a : ℝ} (ha : 0 < a)
    (hv : TendstoUniformlyOn (fun t => R t 0) ψ (𝓝[Ioi 0] 0) K)
    (hd : TendstoUniformlyOn (fun t => fderiv ℝ (R t 0)) (fderiv ℝ ψ) (𝓝[Ioi 0] 0) K)
    (hδv : ∀ t ∈ Ioo 0 a, TendstoUniformlyOn (R t) (R t 0) (𝓝[Ioi 0] 0) K)
    (hδd : ∀ t ∈ Ioo 0 a, TendstoUniformlyOn (fun δ => fderiv ℝ (R t δ))
      (fderiv ℝ (R t 0)) (𝓝[Ioi 0] 0) K)
    (hδi : ∀ t ∈ Ioo 0 a, ∀ᶠ δ in 𝓝[Ioi 0] 0,
      ∀ x ∈ K, t • R t δ x ∈ Ω ∧ DifferentiableAt ℝ (R t δ) x) :
    ∃ δ : ℝ → ℝ,
      (∀ t ∈ Ioo 0 a, 0 < δ t ∧ δ t < t ∧ ∀ x ∈ K,
        t • R t (δ t) x ∈ Ω ∧ DifferentiableAt ℝ (R t (δ t)) x) ∧
      TendstoUniformlyOn (fun t => R t (δ t)) ψ (𝓝[Ioi 0] 0) K ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (R t (δ t))) (fderiv ℝ ψ) (𝓝[Ioi 0] 0) K := by
  have hex (t : ℝ) (ht : t ∈ Ioo 0 a) : ∃ δ : ℝ, 0 < δ ∧ δ < t ∧
      (∀ x ∈ K, t • R t δ x ∈ Ω ∧ DifferentiableAt ℝ (R t δ) x) ∧
      (∀ x ∈ K, dist (R t 0 x) (R t δ x) < t) ∧
      (∀ x ∈ K, dist (fderiv ℝ (R t 0) x) (fderiv ℝ (R t δ) x) < t) := by
    have hb : ∀ᶠ δ in 𝓝[Ioi 0] 0, 0 < δ ∧ δ < t := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds ht.1).filter_mono nhdsWithin_le_nhds] with δ hδ hdt
      exact ⟨hδ,hdt⟩
    have he := hb.and ((hδi t ht).and
      (((Metric.tendstoUniformlyOn_iff.mp (hδv t ht)) t ht.1).and
        ((Metric.tendstoUniformlyOn_iff.mp (hδd t ht)) t ht.1)))
    obtain ⟨δ,hδ,hi,hv,hd⟩ := he.exists
    exact ⟨δ,hδ.1,hδ.2,hi,hv,hd⟩
  let δ : ℝ → ℝ := fun t => if ht : t ∈ Ioo 0 a then (hex t ht).choose else 0
  have hs (t : ℝ) (ht : t ∈ Ioo 0 a) : 0 < δ t ∧ δ t < t ∧
      (∀ x ∈ K, t • R t (δ t) x ∈ Ω ∧ DifferentiableAt ℝ (R t (δ t)) x) ∧
      (∀ x ∈ K, dist (R t 0 x) (R t (δ t) x) < t) ∧
      (∀ x ∈ K, dist (fderiv ℝ (R t 0) x) (fderiv ℝ (R t (δ t)) x) < t) := by
    simpa only [δ,dite_eq_left ht] using (hex t ht).choose_spec
  have hsmall : ∀ᶠ t in 𝓝[Ioi 0] 0, t ∈ Ioo 0 a := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with t ht hta
    exact ⟨ht,hta⟩
  refine ⟨δ,fun t ht => ⟨(hs t ht).1,(hs t ht).2.1,(hs t ht).2.2.1⟩,?_,?_⟩
  · apply uniformly_of_vanishing_error hv (tendsto_id.mono_left nhdsWithin_le_nhds)
    filter_upwards [hsmall] with t ht
    intro x hx
    exact ((hs t ht).2.2.2.1 x hx).le
  · apply uniformly_of_vanishing_error hd (tendsto_id.mono_left nhdsWithin_le_nhds)
    filter_upwards [hsmall] with t ht
    intro x hx
    exact ((hs t ht).2.2.2.2 x hx).le

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_NoncollapseC1Scaling
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
namespace Release061
open Set Filter Metric
open scoped Topology NNReal Pointwise

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem real_approximatesLinearOn_of_fderiv_close {s : Set E} (hs : Convex ℝ s)
    {f : E → F} (L : E →L[ℝ] F) {c : ℝ≥0}
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hd : ∀ x ∈ s, ‖fderiv ℝ f x-L‖ ≤ c) :
    ApproximatesLinearOn f L s c := by
  apply LipschitzOnWith.approximatesLinearOn
  apply hs.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · intro x hx
    exact (hf x hx).sub L.differentiableAt
  · intro x hx
    change ‖fderiv ℝ (fun y => f y-L y) x‖ ≤ (c : ℝ)
    simpa only [fderiv_fun_sub (hf x hx) L.differentiableAt,L.fderiv] using hd x hx

theorem real_stable_image_ball [CompleteSpace E] [Nontrivial F]
    {f : E → F} (L : E ≃L[ℝ] F) {x : E} {y : F} {R : ℝ} (hR : 0 < R)
    (hf : ∀ z ∈ closedBall x R, DifferentiableAt ℝ f z)
    (hd : ∀ z ∈ closedBall x R,
      ‖fderiv ℝ f z-(L : E →L[ℝ] F)‖ ≤ ‖(L.symm : F →L[ℝ] E)‖⁻¹/2)
    (hc : dist y (f x) < ‖(L.symm : F →L[ℝ] E)‖⁻¹*R/4) :
    ball y (‖(L.symm : F →L[ℝ] E)‖⁻¹*R/4) ⊆ f '' closedBall x R := by
  let c : ℝ≥0 := ⟨‖(L.symm : F →L[ℝ] E)‖⁻¹/2, by positivity⟩
  have ha : ApproximatesLinearOn f (L : E →L[ℝ] F) (closedBall x R) c :=
    real_approximatesLinearOn_of_fderiv_close (c := c) (f := f)
      (convex_closedBall x R) (L : E →L[ℝ] F) hf hd
  have hsur := ha.surjOn_closedBall_of_nonlinearRightInverse L.toNonlinearRightInverse hR.le Subset.rfl
  intro z hz
  apply hsur
  change dist z (f x) ≤ (‖(L.symm : F →L[ℝ] E)‖⁻¹ -
    ‖(L.symm : F →L[ℝ] E)‖⁻¹/2)*R
  have hz' := mem_ball.mp hz
  have ht := dist_triangle z y (f x)
  linarith

theorem noncollapse_of_C1_scaling [CompleteSpace E] [Nontrivial F]
    {Ω : Set F} {ψ : E → F} {Ψ : ℝ → E → F} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (J : E ≃L[ℝ] F) (hJ : fderiv ℝ ψ 0 = (J : E →L[ℝ] F))
    (hcont : ContinuousAt (fderiv ℝ ψ) 0)
    (hderiv : TendstoUniformlyOn (fun t => fderiv ℝ (Ψ t)) (fderiv ℝ ψ)
      (𝓝[Set.Ioi 0] 0) (closedBall 0 r₀))
    (hcenter : Tendsto (fun t => Ψ t 0) (𝓝[Set.Ioi 0] 0) (𝓝 (ψ 0)))
    (hdiff : ∀ᶠ t in 𝓝[Set.Ioi 0] 0, ∀ x ∈ closedBall 0 r₀,
      DifferentiableAt ℝ (Ψ t) x)
    (himage : ∀ᶠ t in 𝓝[Set.Ioi 0] 0, ∀ x ∈ closedBall 0 r₀, t • Ψ t x ∈ Ω) :
    ∃ c C t₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < t₀ ∧ ∀ t, 0 < t → t < t₀ →
      ∃ a : F, ‖a‖ ≤ C*t ∧ ball a (c*t) ⊆ Ω := by
  let A : ℝ := ‖(J.symm : F →L[ℝ] E)‖⁻¹
  have hA : 0 < A := inv_pos.mpr J.symm.norm_pos
  have hnear : ∀ᶠ x in 𝓝 (0 : E), ‖fderiv ℝ ψ x-(J : E →L[ℝ] F)‖ < A/4 := by
    have ht : Tendsto (fun x => ‖fderiv ℝ ψ x-(J : E →L[ℝ] F)‖)
        (𝓝 (0 : E)) (𝓝 0) := by
      simpa [hJ] using (hcont.sub_const (J : E →L[ℝ] F)).norm
    exact (tendsto_order.mp ht).2 (A/4) (by positivity)
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hnear
  let R : ℝ := min r₀ (ε/2)
  have hR : 0 < R := lt_min hr₀ (half_pos hε)
  have hRr : closedBall (0 : E) R ⊆ closedBall 0 r₀ :=
    closedBall_subset_closedBall (min_le_left _ _)
  have hRε : closedBall (0 : E) R ⊆ ball 0 ε :=
    closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  let c : ℝ := A*R/4
  have hc : 0 < c := by positivity
  let C : ℝ := ‖ψ 0‖+1
  have hC : 0 < C := by positivity
  have hbd : ∀ᶠ t in 𝓝[Set.Ioi 0] 0, ‖Ψ t 0‖ < C :=
    (tendsto_order.mp hcenter.norm).2 C (by dsimp [C]; linarith)
  have hevent : ∀ᶠ t in 𝓝[Set.Ioi 0] 0,
      ‖Ψ t 0‖ < C ∧ ball (Ψ t 0) c ⊆ Ψ t '' closedBall 0 R ∧
        ∀ x ∈ closedBall 0 R, t • Ψ t x ∈ Ω := by
    filter_upwards [hbd, hdiff, himage,
      Metric.tendstoUniformlyOn_iff.mp hderiv (A/4) (by positivity)] with t ht hdt hit hclose
    refine ⟨ht, ?_, fun x hx => hit x (hRr hx)⟩
    apply real_stable_image_ball J hR (fun x hx => hdt x (hRr hx)) ?_ ?_
    · intro x hx
      have he : ‖fderiv ℝ (Ψ t) x-fderiv ℝ ψ x‖ < A/4 := by
        simpa only [dist_eq_norm, norm_sub_rev] using hclose x (hRr hx)
      have hn := hsub (hRε hx)
      change ‖fderiv ℝ ψ x-(J : E →L[ℝ] F)‖ < A/4 at hn
      have htri : ‖fderiv ℝ (Ψ t) x-(J : E →L[ℝ] F)‖ ≤
          ‖fderiv ℝ (Ψ t) x-fderiv ℝ ψ x‖ + ‖fderiv ℝ ψ x-(J : E →L[ℝ] F)‖ := by
        simpa only [dist_eq_norm] using dist_triangle (fderiv ℝ (Ψ t) x)
          (fderiv ℝ ψ x) (J : E →L[ℝ] F)
      change ‖fderiv ℝ (Ψ t) x-(J : E →L[ℝ] F)‖ ≤ A/2
      linarith
    · simpa only [dist_self] using hc
  obtain ⟨t₀,ht₀,hsmall⟩ := Metric.mem_nhdsWithin_iff.mp hevent
  refine ⟨c,C,t₀,hc,hC,ht₀,?_⟩
  intro t ht htt
  have htb : t ∈ ball (0 : ℝ) t₀ := by simpa [mem_ball,Real.dist_eq,abs_of_pos ht] using htt
  obtain ⟨hb,hball,hi⟩ := hsmall ⟨htb,ht⟩
  refine ⟨t • Ψ t 0,?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    nlinarith
  · have heq : ball (t • Ψ t 0) (c*t) = t • ball (Ψ t 0) c := by
      rw [_root_.smul_ball ht.ne']; congr 1
      rw [Real.norm_eq_abs,abs_of_pos ht,mul_comm]
    rw [heq]
    rintro y ⟨z,hz,rfl⟩
    obtain ⟨x,hx,rfl⟩ := hball hz
    exact hi x hx

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_UniformSmallOperators
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
namespace Release061

section

lemma continuousOn_uniformly_compact {P E F : Type*} [TopologicalSpace P]
    [TopologicalSpace E] [PseudoMetricSpace F]
    {K : Set E} (hK : IsCompact K) {V : Set P} {p₀ : P} (hV : V ∈ 𝓝 p₀)
    {f : P → E → F} (hf : ContinuousOn (Function.uncurry f) (V ×ˢ K)) :
    TendstoUniformlyOn f (f p₀) (𝓝 p₀) K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨W,hW,hw⟩ := hK.mem_uniformity_of_prod hf (mem_of_mem_nhds hV)
    (Metric.dist_mem_uniformity hε)
  rw [nhdsWithin_eq_nhds.mpr hV] at hW
  filter_upwards [hW] with p hp
  intro x hx
  simpa only [Set.mem_ofPred_eq,dist_comm] using hw p hp x hx

variable {P E F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma c1_partial_family {f : P × E → F} {S : Set (P × E)} (hS : IsOpen S)
    (hf : ContDiffOn ℝ 1 f S) :
    ContinuousOn (fun q : P × E => fderiv ℝ (fun x => f (q.1,x)) q.2) S := by
  have hfull : ContinuousOn (fderiv ℝ f) S := by
    intro q hq
    exact ((hf q hq).contDiffAt (hS.mem_nhds hq)).continuousAt_fderiv (by norm_num) |>.continuousWithinAt
  have heq : ∀ q ∈ S, fderiv ℝ (fun x => f (q.1,x)) q.2 =
      (fderiv ℝ f q).comp (ContinuousLinearMap.inr ℝ P E) := by
    intro q hq
    have hd := ((hf q hq).contDiffAt (hS.mem_nhds hq)).differentiableAt (by norm_num)
    exact (hd.hasFDerivAt.comp q.2 ((hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2))).fderiv
  apply ContinuousOn.congr _ heq
  exact hfull.clm_comp continuousOn_const

theorem c1_family_uniformly_compact {f : P × E → F} {S : Set (P × E)}
    (hS : IsOpen S) (hf : ContDiffOn ℝ 1 f S)
    {K : Set E} (hK : IsCompact K) {p₀ : P}
    (hKS : {p₀} ×ˢ K ⊆ S) :
    TendstoUniformlyOn (fun p x => f (p,x)) (fun x => f (p₀,x)) (𝓝 p₀) K ∧
      TendstoUniformlyOn (fun p x => fderiv ℝ (fun y => f (p,y)) x)
        (fun x => fderiv ℝ (fun y => f (p₀,y)) x) (𝓝 p₀) K := by
  obtain ⟨V,W,hV,_,hpV,hKW,hVW⟩ := generalized_tube_lemma
    isCompact_singleton hK hS hKS
  have hp : V ∈ 𝓝 p₀ := hV.mem_nhds (hpV (mem_singleton p₀))
  have hsub : V ×ˢ K ⊆ S := fun q hq => hVW ⟨hq.1,hKW hq.2⟩
  exact ⟨continuousOn_uniformly_compact hK hp (hf.continuousOn.mono hsub),
    continuousOn_uniformly_compact hK hp ((c1_partial_family hS hf).mono hsub)⟩

end

variable {ι E F G : Type*} [TopologicalSpace E]
  [NormedAddCommGroup F] [NormedAddCommGroup G]

lemma uniformly_eventually_norm_bounded {K : Set E} (hK : IsCompact K)
    {f : E → F} (hf : ContinuousOn f K) {v : ι → E → F} {l : Filter ι}
    (hv : TendstoUniformlyOn v f l K) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t in l, ∀ x ∈ K, ‖v t x‖ ≤ C := by
  obtain ⟨C,hC⟩ := (hK.image_of_continuousOn hf).isBounded.exists_norm_le
  refine ⟨1+max 0 C,by positivity,?_⟩
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hv) 1 (by norm_num)] with t ht
  intro x hx
  have hdist : ‖v t x-f x‖ < 1 := by
    simpa only [dist_eq_norm,norm_sub_rev] using ht x hx
  calc
    ‖v t x‖ = ‖(v t x-f x)+f x‖ := by rw [sub_add_cancel]
    _ ≤ ‖v t x-f x‖+‖f x‖ := norm_add_le _ _
    _ ≤ 1+max 0 C := add_le_add hdist.le ((hC _ (mem_image_of_mem f hx)).trans (le_max_right _ _))

omit [TopologicalSpace E] in
lemma uniform_zero_of_norm_bound {K : Set E} {v : ι → E → F} {l : Filter ι}
    {a : ι → ℝ} (ha : Tendsto a l (𝓝 0)) {C : ℝ}
    (hb : ∀ᶠ t in l, ∀ x ∈ K, ‖v t x‖ ≤ a t*C) :
    TendstoUniformlyOn v (fun _ => 0) l K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have he : ∀ᶠ t in l, a t*C < ε := by
    exact (tendsto_order.mp (by simpa using ha.mul_const C)).2 ε hε
  filter_upwards [hb,he] with t ht he
  intro x hx
  simpa only [dist_zero_left] using lt_of_le_of_lt (ht x hx) he

lemma uniform_small_operators [NormedSpace ℝ F] [NormedSpace ℝ G]
    {K : Set E} (hK : IsCompact K) {f : E → F} (hf : ContinuousOn f K)
    {v : ι → E → F} {l : Filter ι} (hv : TendstoUniformlyOn v f l K)
    (L : ι → F →L[ℝ] G) (hL : Tendsto (fun t => ‖L t‖) l (𝓝 0)) :
    TendstoUniformlyOn (fun t x => L t (v t x)) (fun _ => 0) l K := by
  obtain ⟨C,_,hC⟩ := uniformly_eventually_norm_bounded hK hf hv
  apply uniform_zero_of_norm_bound hL (C := C)
  filter_upwards [hC] with t ht
  intro x hx
  exact ((L t).le_opNorm _).trans (mul_le_mul_of_nonneg_left (ht x hx) (norm_nonneg _))

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_C1PerturbedFamilyLocal
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
namespace Release061
variable {P E F G : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem c1_small_operators {f : P × E → F} {S : Set (P × E)}
    (hS : IsOpen S) (hf : ContDiffOn ℝ 1 f S)
    {K : Set E} (hK : IsCompact K) {p₀ : P} (hKS : {p₀} ×ˢ K ⊆ S)
    (L : P → F →L[ℝ] G) (hL : Tendsto (fun p => ‖L p‖) (𝓝 p₀) (𝓝 0)) :
    TendstoUniformlyOn (fun p x => L p (f (p,x))) (fun _ => 0) (𝓝 p₀) K ∧
    TendstoUniformlyOn (fun p x => fderiv ℝ (fun y => L p (f (p,y))) x)
      (fun _ => 0) (𝓝 p₀) K := by
  obtain ⟨hv,hd⟩ := c1_family_uniformly_compact hS hf hK hKS
  have hbase : ContinuousOn (fun x => f (p₀,x)) K := by
    exact hf.continuousOn.comp (by fun_prop) (fun x hx => hKS ⟨rfl,hx⟩)
  have hdbase : ContinuousOn (fun x => fderiv ℝ (fun y => f (p₀,y)) x) K := by
    exact (c1_partial_family hS hf).comp
      (show ContinuousOn (fun x : E => (p₀,x)) K by fun_prop)
      (fun x hx => hKS ⟨mem_singleton p₀,hx⟩)
  refine ⟨uniform_small_operators hK hbase hv L hL,?_⟩
  obtain ⟨C,_,hC⟩ := uniformly_eventually_norm_bounded hK hdbase hd
  obtain ⟨V,W,hV,_,hpV,hKW,hVW⟩ := generalized_tube_lemma
    isCompact_singleton hK hS hKS
  have hp : V ∈ 𝓝 p₀ := hV.mem_nhds (hpV (mem_singleton p₀))
  apply uniform_zero_of_norm_bound hL (C := C)
  filter_upwards [hC,hp] with p hC hp
  intro x hx
  have hs : (p,x) ∈ S := hVW ⟨hp,hKW hx⟩
  have hdiff : DifferentiableAt ℝ (fun y => f (p,y)) x :=
    (((hf _ hs).contDiffAt (hS.mem_nhds hs)).differentiableAt (by norm_num)).comp x (by fun_prop)
  have he : fderiv ℝ (fun y => L p (f (p,y))) x =
      (L p).comp (fderiv ℝ (fun y => f (p,y)) x) :=
    ((L p).hasFDerivAt.comp x hdiff.hasFDerivAt).fderiv
  rw [he]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (hC x hx) (norm_nonneg _))

lemma c1_family_eventually_differentiable {f : P × E → F} {S : Set (P × E)}
    (hS : IsOpen S) (hf : ContDiffOn ℝ 1 f S)
    {K : Set E} (hK : IsCompact K) {p₀ : P} (hKS : {p₀} ×ˢ K ⊆ S) :
    ∀ᶠ p in 𝓝 p₀, ∀ x ∈ K, DifferentiableAt ℝ (fun y => f (p,y)) x := by
  obtain ⟨V,W,hV,_,hpV,hKW,hVW⟩ := generalized_tube_lemma
    isCompact_singleton hK hS hKS
  filter_upwards [hV.mem_nhds (hpV (mem_singleton p₀))] with p hp
  intro x hx
  have hs : (p,x) ∈ S := hVW ⟨hp,hKW hx⟩
  exact (((hf _ hs).contDiffAt (hS.mem_nhds hs)).differentiableAt (by norm_num)).comp x (by fun_prop)

theorem c1_perturbed_family {f : P × E → F} {g : P × E → G} {S : Set (P × E)}
    (hS : IsOpen S) (hf : ContDiffOn ℝ 1 f S) (hg : ContDiffOn ℝ 1 g S)
    {K : Set E} (hK : IsCompact K) {p₀ : P} (hKS : {p₀} ×ˢ K ⊆ S)
    (L : P → G →L[ℝ] F) (hL : Tendsto (fun p => ‖L p‖) (𝓝 p₀) (𝓝 0)) :
    TendstoUniformlyOn (fun p x => f (p,x)+L p (g (p,x))) (fun x => f (p₀,x)) (𝓝 p₀) K ∧
    TendstoUniformlyOn (fun p x => fderiv ℝ (fun y => f (p,y)+L p (g (p,y))) x)
      (fun x => fderiv ℝ (fun y => f (p₀,y)) x) (𝓝 p₀) K ∧
    (∀ᶠ p in 𝓝 p₀, ∀ x ∈ K, DifferentiableAt ℝ (fun y => f (p,y)+L p (g (p,y))) x) := by
  obtain ⟨hfv,hfd⟩ := c1_family_uniformly_compact hS hf hK hKS
  obtain ⟨hgv,hgd⟩ := c1_small_operators hS hg hK hKS L hL
  have hdf := c1_family_eventually_differentiable hS hf hK hKS
  have hdg := c1_family_eventually_differentiable hS hg hK hKS
  refine ⟨by simpa only [Pi.add_def,add_zero] using hfv.add hgv,?_,?_⟩
  · have hd := hfd.add hgd
    simp only [Pi.add_def,add_zero] at hd
    apply hd.congr
    filter_upwards [hdf,hdg] with p hp hq
    intro x hx
    exact (fderiv_fun_add (hp x hx) ((L p).differentiableAt.comp x (hq x hx))).symm
  · filter_upwards [hdf,hdg] with p hp hq
    intro x hx
    exact (hp x hx).add ((L p).differentiableAt.comp x (hq x hx))

theorem c1_perturbed_family_local [ProperSpace E]
    {f : P × E → F} {g : P × E → G}
    (hf : ContDiffAt ℝ 1 f 0) (hg : ContDiffAt ℝ 1 g 0)
    (L : P → G →L[ℝ] F) (hL : Tendsto (fun p => ‖L p‖) (𝓝 0) (𝓝 0)) :
    ∃ r : ℝ, 0 < r ∧
    TendstoUniformlyOn (fun p x => f (p,x)+L p (g (p,x))) (fun x => f (0,x)) (𝓝 0) (closedBall 0 r) ∧
    TendstoUniformlyOn (fun p x => fderiv ℝ (fun y => f (p,y)+L p (g (p,y))) x)
      (fun x => fderiv ℝ (fun y => f (0,y)) x) (𝓝 0) (closedBall 0 r) ∧
    (∀ᶠ p in 𝓝 (0 : P), ∀ x ∈ closedBall 0 r,
      DifferentiableAt ℝ (fun y => f (p,y)+L p (g (p,y))) x) := by
  obtain ⟨V,hV,hfV⟩ := hf.contDiffOn (le_refl _) (by simp)
  obtain ⟨W,hW,hgW⟩ := hg.contDiffOn (le_refl _) (by simp)
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hV hW)
  have hKS : {(0 : P)} ×ˢ closedBall (0 : E) (ε/2) ⊆ ball 0 ε := by
    rintro ⟨p,x⟩ ⟨hp,hx⟩
    change p = 0 at hp
    subst p
    simp only [mem_ball,dist_zero_right,Prod.norm_def,norm_zero,max_eq_right (norm_nonneg x)]
    have hi : ‖x‖ ≤ ε/2 := by simpa only [mem_closedBall,dist_zero_right] using hx
    linarith
  refine ⟨ε/2,half_pos hε,?_⟩
  exact c1_perturbed_family isOpen_ball
    (hfV.mono (fun x hx => (hsub hx).1)) (hgW.mono (fun x hx => (hsub hx).2))
    (isCompact_closedBall _ _) hKS L hL

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ScaledRadialOperatorApply
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.radiusCircleCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
namespace Release061.Wiener
open scoped Topology
open Set Filter Metric

lemma radialPoint_coe {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (radialPoint t : ℂ) = 1-(t : ℂ) := by
  simp only [radialPoint,min_eq_right ht1,max_eq_right ht]

lemma schwarzDifference_apply {k : ℕ} (z : ClosedDisc) (Y : BoundarySpace k) (i : Fin k) :
    schwarzDifference z Y i = realSchwarz (Y i) z-realSchwarz (Y i) ⟨0,by simp [ClosedDisc]⟩ := rfl

lemma schwarzDifference_norm {k : ℕ} (z : ClosedDisc) :
    ‖schwarzDifference (k := k) z‖ ≤ 6 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro Y
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [schwarzDifference_apply]
  calc
    ‖realSchwarz (Y i) z-realSchwarz (Y i) ⟨0,by simp [ClosedDisc]⟩‖ ≤
        ‖realSchwarz (Y i) z‖+‖realSchwarz (Y i) ⟨0,by simp [ClosedDisc]⟩‖ := norm_sub_le _ _
    _ ≤ ‖realSchwarz (Y i)‖+‖realSchwarz (Y i)‖ :=
      add_le_add ((realSchwarz (Y i)).norm_coe_le_norm _) ((realSchwarz (Y i)).norm_coe_le_norm _)
    _ ≤ 3*‖Y i‖+3*‖Y i‖ := add_le_add (schwarz_norm _) (schwarz_norm _)
    _ ≤ 6*‖Y‖ := by have hi := norm_le_pi_norm Y i; nlinarith

lemma scaledRadialOperator_norm_tendsto {k : ℕ} :
    Tendsto (fun t : ℝ => ‖scaledRadialOperator (k := k) t‖) (𝓝 0) (𝓝 0) := by
  have hs : Tendsto (fun t : ℝ => |-(t/(1-t))| * 6) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => |-(t/(1-t))| * 6) 0 := by fun_prop (disch := norm_num)
    simpa using hc.tendsto
  apply squeeze_zero (fun _ => norm_nonneg _) _ hs
  intro t
  rw [scaledRadialOperator,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (schwarzDifference_norm _) (abs_nonneg _)

lemma scaledRadialOperator_apply {k : ℕ} {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (Y : BoundarySpace k) (i : Fin k) :
    scaledRadialOperator t Y i =
      -(t : ℂ)/(1-(t : ℂ))*(discValue (Y i : Space) (1-(t : ℂ))-discValue (Y i : Space) 0) := by
  change (-(t/(1-t))) • (realSchwarz (Y i) (radialPoint t)-
    realSchwarz (Y i) ⟨0,by simp [ClosedDisc]⟩) = _
  have he : radialPoint t = ⟨1-(t : ℂ),radial_mem_closedDisc ht ht1⟩ :=
    Subtype.ext (radialPoint_coe ht ht1)
  rw [he]
  change (-(t/(1-t))) • (schwarz (Y i : Space) _-schwarz (Y i : Space) _) = _
  rw [← discValue_eq _ (radial_mem_closedDisc ht ht1),← discValue_eq _ (by simp [ClosedDisc])]
  simp only [Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_sub,
    Complex.ofReal_one,neg_div]

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ScaledModelC1Limit
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
namespace Release061.Wiener
open scoped Topology
open Set Filter Metric

lemma scaledDisc_eq_model {k : ℕ} {κ : realAlgebra}
    (hκ : ∀ θ, dist (circleCos θ) (-1 : ℝ) ≤ 1/2 →
      (2-2*circleCos θ)*realEvaluation θ κ = 1)
    {Y : RealDiscParams k → BoundarySpace k} {q : RealDiscParams k} {t : ℝ}
    (hY : ∀ θ, (1/2 : ℝ) < dist (circleCos θ) (-1 : ℝ) →
      ∀ i, realEvaluation θ (Y (t • q.1,q.2) i) = 0)
    (ht : 0 < t) (ht1 : t < 1) :
    scaledDisc Y t q = scaledModel κ Y t q := by
  funext i
  change t⁻¹ • (constantDisc ((t • q.1) i) (radialPoint t)+
    realSchwarz (Y (t • q.1,q.2) i) (radialPoint t)) =
    (q.1 i : ℂ)+Complex.I*(normalSlice κ Y (t • q.1,q.2) i : ℂ)+
      scaledRadialOperator t (fun j => κ*Y (t • q.1,q.2) j) i
  rw [constantDisc_apply,scaledRadialOperator_apply ht.le ht1.le]
  have he : radialPoint t = ⟨1-(t : ℂ),radial_mem_closedDisc ht.le ht1.le⟩ :=
    Subtype.ext (radialPoint_coe ht.le ht1.le)
  rw [he]
  change t⁻¹ • (↑((t • q.1) i)+schwarz (Y (t • q.1,q.2) i : Space) _) = _
  rw [← discValue_eq _ (radial_mem_closedDisc ht.le ht1.le),
    localized_radial_expansion hκ (fun θ hθ => hY θ hθ i) ht.le ht1]
  dsimp only [normalSlice,Pi.smul_apply,smul_eq_mul]
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_mul]
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  simp only [Subalgebra.coe_mul]
  field_simp [htc]
  ring

lemma normalSlice_contDiffAt {k : ℕ} (κ : realAlgebra)
    {Y : RealDiscParams k → BoundarySpace k} (hY : ContDiffAt ℝ 1 Y 0) :
    ContDiffAt ℝ 1 (normalSlice κ Y) 0 := by
  apply contDiffAt_pi.mpr
  intro i
  exact contDiffAt_const.mul (realMean.contDiff.contDiffAt.comp 0
    (contDiffAt_const.mul (contDiffAt_pi.mp hY i)))

theorem scaledModel_C1_limit {k : ℕ} (κ : realAlgebra)
    {Y : RealDiscParams k → BoundarySpace k} (hY : ContDiffAt ℝ 1 Y 0) :
    ∃ r : ℝ, 0 < r ∧
      TendstoUniformlyOn (scaledModel κ Y) (limitModel κ Y) (𝓝 0) (closedBall 0 r) ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (scaledModel κ Y t)) (fderiv ℝ (limitModel κ Y))
        (𝓝 0) (closedBall 0 r) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), ∀ q ∈ closedBall 0 r, DifferentiableAt ℝ (scaledModel κ Y t) q) := by
  let P : ℝ × RealDiscParams k → RealDiscParams k := fun v => (v.1 • v.2.1,v.2.2)
  have hP : ContDiffAt ℝ 1 P 0 := by fun_prop
  have hYP : ContDiffAt ℝ 1 (Y ∘ P) 0 := by
    have hY' : ContDiffAt ℝ 1 Y (P 0) := by simpa [P,← Prod.zero_eq_mk] using hY
    exact hY'.comp (f := P) 0 hP
  have hNP : ContDiffAt ℝ 1 (normalSlice κ Y ∘ P) 0 := by
    have hN : ContDiffAt ℝ 1 (normalSlice κ Y) (P 0) := by
      simpa [P,← Prod.zero_eq_mk] using normalSlice_contDiffAt κ hY
    exact hN.comp (f := P) 0 hP
  let F : ℝ × RealDiscParams k → Fin k → ℂ :=
    fun v i => (v.2.1 i : ℂ)+Complex.I*(normalSlice κ Y (P v) i : ℂ)
  let G : ℝ × RealDiscParams k → BoundarySpace k := fun v i => κ*Y (P v) i
  have hF : ContDiffAt ℝ 1 F 0 := by
    apply contDiffAt_pi.mpr
    intro i
    have hh := contDiffAt_pi.mp hNP i
    dsimp only [Function.comp_def] at hh
    dsimp only [F]
    refine (Complex.ofRealCLM.contDiff.contDiffAt.comp 0 (by fun_prop)).add ?_
    exact contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp 0 hh)
  have hG : ContDiffAt ℝ 1 G 0 := by
    apply contDiffAt_pi.mpr
    intro i
    exact contDiffAt_const.mul (contDiffAt_pi.mp hYP i)
  obtain ⟨r,hr,hv,hd,hdf⟩ := c1_perturbed_family_local hF hG
    (scaledRadialOperator (k := k)) scaledRadialOperator_norm_tendsto
  have hF0 : (fun x => F (0,x)) = limitModel κ Y := by
    funext x i
    dsimp only [F,P,limitModel]
    rw [zero_smul]
  have hsum (t : ℝ) : (fun x => F (t,x)+scaledRadialOperator t (G (t,x))) =
      scaledModel κ Y t := rfl
  refine ⟨r,hr,?_,?_,?_⟩
  · rw [Metric.tendstoUniformlyOn_iff] at hv ⊢
    intro ε hε
    filter_upwards [hv ε hε] with t ht
    intro x hx
    rw [← congrFun hF0 x,← congrFun (hsum t) x]
    exact ht x hx
  · change TendstoUniformlyOn
      (fun p => fderiv ℝ (fun x => F (p,x)+scaledRadialOperator p (G (p,x))))
      (fderiv ℝ (fun x => F (0,x))) _ _ at hd
    simpa only [hF0,hsum] using hd
  · simpa only [hsum] using hdf

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ScaledDiscC1Limit
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
namespace Release061
variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem c1_uniformlyOn_congr_on_open {K S : Set E} (hS : IsOpen S) (hKS : K ⊆ S)
    {f g : ι → E → F} {ψ : E → F} {l : Filter ι}
    (hEq : ∀ᶠ t in l, EqOn (f t) (g t) S)
    (hv : TendstoUniformlyOn f ψ l K)
    (hd : TendstoUniformlyOn (fun t => fderiv ℝ (f t)) (fderiv ℝ ψ) l K)
    (hf : ∀ᶠ t in l, ∀ x ∈ K, DifferentiableAt ℝ (f t) x) :
    TendstoUniformlyOn g ψ l K ∧
    TendstoUniformlyOn (fun t => fderiv ℝ (g t)) (fderiv ℝ ψ) l K ∧
    (∀ᶠ t in l, ∀ x ∈ K, DifferentiableAt ℝ (g t) x) := by
  have he (t : ι) (ht : EqOn (f t) (g t) S) (x : E) (hx : x ∈ K) :
      f t =ᶠ[𝓝 x] g t :=
    Filter.mem_of_superset (hS.mem_nhds (hKS hx)) fun y hy => ht hy
  refine ⟨hv.congr (hEq.mono fun t ht x hx => ht (hKS hx)),?_,?_⟩
  · exact hd.congr (hEq.mono fun t ht x hx => (he t ht x hx).fderiv_eq)
  · filter_upwards [hEq,hf] with t ht hf
    intro x hx
    exact (hf x hx).congr_of_eventuallyEq (he t ht x hx).symm

end Release061

namespace Release061.Wiener
open scoped Topology
open Set Filter Metric

lemma scale_first_mem_ball {k : ℕ} {q : RealDiscParams k} {r t : ℝ}
    (hq : q ∈ ball 0 r) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (t • q.1,q.2) ∈ ball (0 : RealDiscParams k) r := by
  have hq' : max ‖q.1‖ ‖q.2‖ < r := by
    simpa only [mem_ball,dist_zero_right,Prod.norm_def] using hq
  simp only [mem_ball,dist_zero_right,Prod.norm_def]
  apply lt_of_le_of_lt _ hq'
  apply max_le_max _ le_rfl
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]
  exact mul_le_of_le_one_left (norm_nonneg _) ht1

theorem scaledDisc_C1_limit {k : ℕ} {κ : realAlgebra}
    (hκ : ∀ θ, dist (circleCos θ) (-1 : ℝ) ≤ 1/2 →
      (2-2*circleCos θ)*realEvaluation θ κ = 1)
    {Y : RealDiscParams k → BoundarySpace k} (hY : ContDiffAt ℝ 1 Y 0)
    (hloc : ∀ᶠ q in 𝓝 0, ∀ θ, (1/2 : ℝ) < dist (circleCos θ) (-1 : ℝ) →
      ∀ i, realEvaluation θ (Y q i) = 0) :
    ∃ r : ℝ, 0 < r ∧
      TendstoUniformlyOn (scaledDisc Y) (limitModel κ Y) (𝓝[Ioi 0] 0) (closedBall 0 r) ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (scaledDisc Y t)) (fderiv ℝ (limitModel κ Y))
        (𝓝[Ioi 0] 0) (closedBall 0 r) ∧
      (∀ᶠ t in 𝓝[Ioi 0] (0 : ℝ), ∀ q ∈ closedBall 0 r,
        DifferentiableAt ℝ (scaledDisc Y t) q) := by
  obtain ⟨r,hr,hv,hd,hdf⟩ := scaledModel_C1_limit κ hY
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hloc
  let R := min r (ε/2)
  have hR : 0 < R := lt_min hr (half_pos hε)
  have hRr : closedBall (0 : RealDiscParams k) R ⊆ closedBall 0 r :=
    closedBall_subset_closedBall (min_le_left _ _)
  have hRε : closedBall (0 : RealDiscParams k) R ⊆ ball 0 ε :=
    closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  have heq : ∀ᶠ t in 𝓝[Ioi 0] (0 : ℝ),
      EqOn (scaledModel κ Y t) (scaledDisc Y t) (ball 0 ε) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with t ht ht1
    intro q hq
    exact (scaledDisc_eq_model hκ (hsub (scale_first_mem_ball hq ht.le ht1.le)) ht ht1).symm
  refine ⟨R,hR,?_⟩
  apply c1_uniformlyOn_congr_on_open isOpen_ball hRε heq
  · intro u hu
    exact ((hv.mono hRr) u hu).filter_mono nhdsWithin_le_nhds
  · intro u hu
    exact ((hd.mono hRr) u hu).filter_mono nhdsWithin_le_nhds
  · filter_upwards [hdf.filter_mono nhdsWithin_le_nhds] with t ht q hq
    exact ht q (hRr hq)

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ScaledDiscDeltaC1
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.radiusCircleCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
namespace Release061.Wiener
open scoped Topology
open Set Filter Metric

lemma regularizedSlice_smooth {k : ℕ} {f : (Fin (k+1) → ℝ) → Fin k → ℝ}
    {ε : ℝ} (D : LocalBishopData k f ε) {α δ : ℝ} {q : RealDiscParams k}
    (hp : (q.1,q.2,α,δ) ∈ ball 0 D.radius) :
    ContDiffAt ℝ 1 (regularizedSlice D.Y α δ) q := by
  exact ((D.smoothY _ hp).contDiffAt (isOpen_ball.mem_nhds hp)).comp q (by fun_prop)

lemma scaledDisc_regularized_joint_smooth {k : ℕ} {f : (Fin (k+1) → ℝ) → Fin k → ℝ}
    {ε : ℝ} (D : LocalBishopData k f ε) (α t : ℝ) {q : ℝ × RealDiscParams k}
    (hp : (t • q.2.1,q.2.2,α,q.1) ∈ ball 0 D.radius) :
    ContDiffAt ℝ 1 (fun p : ℝ × RealDiscParams k =>
      scaledDisc (regularizedSlice D.Y α p.1) t p.2) q := by
  have hY := ((D.smoothY _ hp).contDiffAt (isOpen_ball.mem_nhds hp)).comp q
    (show ContDiffAt ℝ 1 (fun p : ℝ × RealDiscParams k => (t • p.2.1,p.2.2,α,p.1)) q by fun_prop)
  apply ContDiffAt.const_smul
  apply contDiffAt_pi.mpr
  intro i
  change ContDiffAt ℝ 1 (fun p => constantDisc ((t • p.2.1) i) (radialPoint t)+
    realSchwarz (D.Y (t • p.2.1,p.2.2,α,p.1) i) (radialPoint t)) q
  apply ContDiffAt.add
  · simp only [constantDisc_apply]
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp q (by
      change ContDiffAt ℝ 1 (fun p : ℝ × RealDiscParams k => t * p.2.1 i) q
      fun_prop)
  · exact (ContinuousMap.evalCLM ℝ (radialPoint t)).contDiff.contDiffAt.comp q
      (realSchwarz.contDiff.contDiffAt.comp q (contDiffAt_pi.mp hY i))

lemma scaledDisc_delta_C1_limit {k : ℕ} {f : (Fin (k+1) → ℝ) → Fin k → ℝ}
    {ε : ℝ} (D : LocalBishopData k f ε) {α t r : ℝ}
    (hr : r < D.radius) (hα : |α| < D.radius) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    TendstoUniformlyOn (fun δ => scaledDisc (regularizedSlice D.Y α δ) t)
      (scaledDisc (regularizedSlice D.Y α 0) t) (𝓝 0) (closedBall 0 r) ∧
      TendstoUniformlyOn (fun δ => fderiv ℝ (scaledDisc (regularizedSlice D.Y α δ) t))
        (fderiv ℝ (scaledDisc (regularizedSlice D.Y α 0) t)) (𝓝 0) (closedBall 0 r) := by
  let Φ : ℝ × RealDiscParams k → BishopParams k := fun p => (t • p.2.1,p.2.2,α,p.1)
  let S := Φ ⁻¹' ball 0 D.radius
  have hS : IsOpen S := isOpen_ball.preimage (show Continuous Φ by fun_prop)
  apply Release061.c1_family_uniformly_compact hS
    (fun p hp => (scaledDisc_regularized_joint_smooth D α t hp).contDiffWithinAt)
    (isCompact_closedBall _ _)
  rintro ⟨δ,q⟩ ⟨hδ,hq⟩
  have hδ0 : δ = 0 := mem_singleton_iff.mp hδ
  subst δ
  have hqnorm : ‖q‖ ≤ r := mem_closedBall_zero_iff.mp hq
  apply bishopParams_mem_ball _ _ hα (by simpa only [abs_zero] using D.radius_pos)
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]
    have hb : ‖q.1‖ ≤ ‖q‖ := norm_fst_le q
    exact (mul_le_of_le_one_left (norm_nonneg _) ht1).trans_lt ((hb.trans hqnorm).trans_lt hr)
  · exact ((norm_snd_le q).trans hqnorm).trans_lt hr

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_BishopTransverseNoncollapse
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
namespace Release061.Wiener
open scoped Topology
open Set Filter Metric

lemma limitModel_contDiffAt {k : ℕ} {Y : RealDiscParams k → BoundarySpace k}
    (κ : realAlgebra) (hY : ContDiffAt ℝ 1 Y 0) :
    ContDiffAt ℝ 1 (limitModel κ Y) 0 := by
  have hN := (normalSlice_contDiffAt κ hY).comp (f := fun q : RealDiscParams k => (0,q.2)) 0
    (show ContDiffAt ℝ 1 (fun q : RealDiscParams k => (0,q.2)) 0 by fun_prop)
  apply contDiffAt_pi.mpr
  intro i
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp 0 (by fun_prop)).add
    (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp 0 (contDiffAt_pi.mp hN i)))

lemma scaledDisc_regularized_differentiable {k : ℕ}
    {f : (Fin (k+1) → ℝ) → Fin k → ℝ} {ε : ℝ}
    (D : LocalBishopData k f ε) (α t δ : ℝ) (q : RealDiscParams k)
    (hp : (t • q.1,q.2,α,δ) ∈ ball 0 D.radius) :
    DifferentiableAt ℝ (scaledDisc (regularizedSlice D.Y α δ) t) q := by
  have hjoint := scaledDisc_regularized_joint_smooth D α t (q := (δ,q)) hp
  exact (hjoint.comp q (show ContDiffAt ℝ 1 (fun x : RealDiscParams k => (δ,x)) q
    by fun_prop)).differentiableAt (by norm_num)

lemma scaledDisc_regularized_interior {k : ℕ}
    {f : (Fin (k+1) → ℝ) → Fin k → ℝ} {ε : ℝ}
    (D : LocalBishopData k f ε) {Ω : Set (Fin k → ℂ)}
    {α d r e₀ : ℝ} (hα : |α| < D.radius) (hd : 0 < d) (hdr : d < D.radius)
    (hrD : r < D.radius) (hre : r < e₀)
    (hinterior : ∀ b : Fin k → ℝ, ‖b‖ < D.radius →
      ∀ e : Fin k → ℝ, ‖e‖ < e₀ → ∀ δ ∈ Ioc 0 d, ∀ z : ClosedDisc,
        (fun i => bishopDisc D.Y (b,e,α,δ) i z) ∈ Ω)
    (t : ℝ) (ht : t ∈ Ioo 0 1) : ∀ᶠ δ in 𝓝[Ioi 0] 0,
      ∀ q ∈ closedBall (0 : RealDiscParams k) r,
        t • scaledDisc (regularizedSlice D.Y α δ) t q ∈ Ω ∧
          DifferentiableAt ℝ (scaledDisc (regularizedSlice D.Y α δ) t) q := by
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hd).filter_mono nhdsWithin_le_nhds] with δ hδ hδd
  intro q hq
  have hbn : ‖t • q.1‖ ≤ r := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2.le).trans
      ((norm_fst_le q).trans (mem_closedBall_zero_iff.mp hq))
  have hen : ‖q.2‖ ≤ r := (norm_snd_le q).trans (mem_closedBall_zero_iff.mp hq)
  have hp : (t • q.1,q.2,α,δ) ∈ ball 0 D.radius :=
    bishopParams_mem_ball (hbn.trans_lt hrD) (hen.trans_lt hrD) hα
      (by rw [abs_of_pos hδ]; exact hδd.trans hdr)
  constructor
  · dsimp only [scaledDisc]
    rw [smul_smul,mul_inv_cancel₀ ht.1.ne',one_smul]
    exact hinterior _ (hbn.trans_lt hrD) _ (hen.trans_lt hre) δ ⟨hδ,hδd.le⟩ (radialPoint t)
  · exact scaledDisc_regularized_differentiable D α t δ q hp

lemma limitModel_invertible_derivative {k : ℕ} {Y : RealDiscParams k → BoundarySpace k}
    (κ : realAlgebra) (hY : ContDiffAt ℝ 1 Y 0)
    (hunit : IsUnit (fderiv ℝ (fun e : Fin k → ℝ => normalSlice κ Y (0,e)) 0)) :
    ∃ J : RealDiscParams k ≃L[ℝ] (Fin k → ℂ),
      fderiv ℝ (limitModel κ Y) 0 = (J : RealDiscParams k →L[ℝ] (Fin k → ℂ)) := by
  let N : (Fin k → ℝ) → Fin k → ℝ := fun e => normalSlice κ Y (0,e)
  have hN : ContDiffAt ℝ 1 N 0 := (normalSlice_contDiffAt κ hY).comp 0 (by fun_prop)
  let J := ContinuousLinearEquiv.ofUnit hunit.unit
  have hJ : (J : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)) = fderiv ℝ N 0 := hunit.unit_spec
  have hND : HasFDerivAt N (J : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)) 0 := by
    rw [hJ]
    exact (hN.differentiableAt (by norm_num)).hasFDerivAt
  let Jfull := ((ContinuousLinearEquiv.refl ℝ (Fin k → ℝ)).prodCongr J).trans
    (Release061.realComplexBlock k)
  exact ⟨Jfull,(Release061.hasFDerivAt_realComplexBlock J hND).fderiv⟩

theorem bishop_transverse_noncollapse {k : ℕ} [NeZero k]
    {f : (Fin (k+1) → ℝ) → Fin k → ℝ} {ε : ℝ}
    (D : LocalBishopData k f ε) {Ω : Set (Fin k → ℂ)}
    (hΩ : IsOpen Ω) (hCP : DiscContinuityWithin k Ω ε)
    {α d u₀ L : ℝ} (hα : 0 < α) (hαr : α < D.radius)
    (hd : 0 < d) (hdr : d < D.radius) (hL : 1 ≤ L) (hu : α*L+d < u₀)
    (hG : ContinuousOn (graphPoint f) (closedBall 0 ε ×ˢ Icc α (α+d)))
    (hgraph : ∀ x ∈ closedBall 0 ε, ∀ u ∈ Ioo 0 u₀, graphPoint f (x,u) ∈ Ω)
    (hlam : ∀ θ, realEvaluation θ D.lam ≤ L)
    (htrans : IsUnit (fderiv ℝ (fun e : Fin k → ℝ => bishopNormal D.kappa D.Y (0,e,α,0)) 0)) :
    ∃ c C t₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < t₀ ∧ ∀ t, 0 < t → t < t₀ →
      ∃ a : Fin k → ℂ, ‖a‖ ≤ C*t ∧ ball a (c*t) ⊆ Ω := by
  have hαabs : |α| < D.radius := by rwa [abs_of_pos hα]
  have hp0 : ((0,0,α,0) : BishopParams k) ∈ ball 0 D.radius :=
    bishopParams_mem_ball (b := 0) (e := 0) (s := α) (δ := 0)
      (by simpa using D.radius_pos) (by simpa using D.radius_pos)
      hαabs (by simpa using D.radius_pos)
  let Y := regularizedSlice D.Y α 0
  have hY : ContDiffAt ℝ 1 Y 0 := regularizedSlice_smooth D hp0
  have hloc : ∀ᶠ q in 𝓝 (0 : RealDiscParams k), ∀ θ,
      (1/2 : ℝ) < dist (circleCos θ) (-1 : ℝ) → ∀ i, realEvaluation θ (Y q i) = 0 := by
    have hP : ContinuousAt (fun q : RealDiscParams k => (q.1,q.2,α,(0 : ℝ))) 0 := by fun_prop
    filter_upwards [hP.eventually (isOpen_ball.mem_nhds hp0)] with q hq
    exact D.localized _ hq rfl
  obtain ⟨r₁,hr₁,hv,hdv,_⟩ := scaledDisc_C1_limit D.cut_division hY hloc
  obtain ⟨e₀,he₀,hinterior⟩ := bishop_positive_interior D hΩ hCP hα hαr hdr hL hu hG hgraph hlam
  let r := min r₁ (min D.radius e₀)/2
  have hr : 0 < r := half_pos (lt_min hr₁ (lt_min D.radius_pos he₀))
  have hrr₁ : r ≤ r₁ := by dsimp [r]; linarith [min_le_left r₁ (min D.radius e₀)]
  have hrD : r < D.radius := by
    have hmin := min_le_right r₁ (min D.radius e₀)
    have hD := min_le_left D.radius e₀
    dsimp [r]; linarith
  have hre : r < e₀ := by
    have hmin := min_le_right r₁ (min D.radius e₀)
    have he := min_le_right D.radius e₀
    dsimp [r]; linarith
  have hKr : closedBall (0 : RealDiscParams k) r ⊆ closedBall 0 r₁ :=
    closedBall_subset_closedBall hrr₁
  let R : ℝ → ℝ → RealDiscParams k → Fin k → ℂ :=
    fun t δ => scaledDisc (regularizedSlice D.Y α δ) t
  have hδC1 (t : ℝ) (ht : t ∈ Ioo 0 1) :=
    scaledDisc_delta_C1_limit D hrD hαabs ht.1.le ht.2.le
  have hδi := scaledDisc_regularized_interior D hαabs hd hdr hrD hre hinterior
  obtain ⟨δ,hreg,hval,hder⟩ := Release061.choose_positive_C1_regularization (R := R) (ψ := limitModel D.kappa Y)
    (show (0 : ℝ) < 1 by norm_num) (hv.mono hKr) (hdv.mono hKr)
    (fun t ht u hu => ((hδC1 t ht).1 u hu).filter_mono nhdsWithin_le_nhds)
    (fun t ht u hu => ((hδC1 t ht).2 u hu).filter_mono nhdsWithin_le_nhds) hδi
  obtain ⟨Jfull,hfull⟩ := limitModel_invertible_derivative D.kappa hY htrans
  apply Release061.noncollapse_of_C1_scaling hr Jfull hfull
    ((limitModel_contDiffAt D.kappa hY).continuousAt_fderiv (by norm_num)) hder
    (hval.tendsto_at (mem_closedBall_self hr.le))
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with t ht ht1 q hq
    exact ((hreg t ⟨ht,ht1⟩).2.2 q hq).2
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with t ht ht1 q hq
    exact ((hreg t ⟨ht,ht1⟩).2.2 q hq).1

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_InteriorBallsAnalyticGraphs
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
namespace Release061.Wiener
open scoped Topology
open Set Filter Metric

theorem bishopData_noncollapse {k : ℕ} [NeZero k]
    {f : (Fin (k+1) → ℝ) → Fin k → ℝ} {ε : ℝ}
    (D : LocalBishopData k f ε) {Ω : Set (Fin k → ℂ)}
    (hΩ : IsOpen Ω) (hCP : DiscContinuityWithin k Ω ε)
    {u₀ : ℝ} (hu₀ : 0 < u₀)
    (hG : ContinuousOn (graphPoint f) (closedBall 0 ε ×ˢ Icc 0 u₀))
    (hgraph : ∀ x ∈ closedBall 0 ε, ∀ u ∈ Ioo 0 u₀, graphPoint f (x,u) ∈ Ω) :
    ∃ c C t₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < t₀ ∧ ∀ t, 0 < t → t < t₀ →
      ∃ a : Fin k → ℂ, ‖a‖ ≤ C*t ∧ ball a (c*t) ⊆ Ω := by
  let L := max 1 ‖D.lam‖
  have hL : 1 ≤ L := le_max_left _ _
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨a,ha,htr⟩ := Metric.mem_nhds_iff.mp D.transverse
  let α := min (min D.radius a) (u₀/(4*L))/2
  have hα : 0 < α := half_pos (lt_min (lt_min D.radius_pos ha) (div_pos hu₀ (by positivity)))
  have hαmin : α < min (min D.radius a) (u₀/(4*L)) := by dsimp [α] at hα ⊢; linarith
  have hαr : α < D.radius := (hαmin.trans_le (min_le_left _ _)).trans_le (min_le_left _ _)
  have hαa : α < a := (hαmin.trans_le (min_le_left _ _)).trans_le (min_le_right _ _)
  have hαu : α*(4*L) < u₀ :=
    (lt_div_iff₀ (by positivity)).mp (hαmin.trans_le (min_le_right _ _))
  let d := min (D.radius/2) (u₀/4)
  have hd : 0 < d := lt_min (half_pos D.radius_pos) (by positivity)
  have hdr : d < D.radius := (min_le_left _ _).trans_lt (by linarith [D.radius_pos])
  have hdu : d ≤ u₀/4 := min_le_right _ _
  have hu : α*L+d < u₀ := by nlinarith
  apply bishop_transverse_noncollapse D hΩ hCP hα hαr hd hdr hL hu
  · apply hG.mono
    intro q hq
    exact ⟨hq.1,⟨hα.le.trans hq.2.1,by
      have hαL : α ≤ α*L := by nlinarith
      linarith [hq.2.2]⟩⟩
  · exact hgraph
  · intro θ
    exact (le_abs_self _).trans ((realEvaluation_bound θ D.lam).trans (le_max_right _ _))
  · exact htr (by simpa only [mem_ball,Real.dist_eq,sub_zero,abs_of_pos hα] using hαa)

lemma graphPoint_contDiffAt {k : ℕ} {f : (Fin (k+1) → ℝ) → Fin k → ℝ}
    (hf : AnalyticAt ℝ f 0) :
    ContDiffAt ℝ 1 (graphPoint f) (0 : (Fin k → ℝ) × ℝ) := by
  have hP : ContDiffAt ℝ 1 (fun q : (Fin k → ℝ) × ℝ => (Fin.cons q.2 q.1 : Fin (k+1) → ℝ)) 0 := by
    apply contDiffAt_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp only [Fin.cons_zero,Fin.cons_succ] <;> fun_prop
  have hzero : (Fin.cons (0 : ℝ) (0 : Fin k → ℝ) : Fin (k+1) → ℝ) = 0 := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  have hf' : ContDiffAt ℝ 1 (fun q : (Fin k → ℝ) × ℝ => f (Fin.cons q.2 q.1)) 0 := by
    have hfa : ContDiffAt ℝ 1 f (Fin.cons (0 : ℝ) (0 : Fin k → ℝ)) := by rw [hzero]; exact hf.contDiffAt
    exact hfa.comp (f := fun q : (Fin k → ℝ) × ℝ => (Fin.cons q.2 q.1 : Fin (k+1) → ℝ)) (0 : (Fin k → ℝ) × ℝ) hP
  apply contDiffAt_pi.mpr
  intro i
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp 0 (by fun_prop)).add
    (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp 0 (contDiffAt_pi.mp hf' i)))

lemma discContinuityWithin_mono {k : ℕ} {Ω : Set (Fin k → ℂ)} {ε r : ℝ}
    (h : DiscContinuityWithin k Ω ε) (hr : r ≤ ε) : DiscContinuityWithin k Ω r := by
  intro A hA hAh hsmall hbd hstart
  exact h A hA hAh (fun s z => (hsmall s z).trans_le hr) hbd hstart

theorem interior_balls_from_analytic_graphs {k : ℕ} {Ω : Set (Fin k → ℂ)}
    (hΩ : IsOpen Ω) {ε : ℝ} (hε : 0 < ε) (hCP : DiscContinuityWithin k Ω ε)
    {f : (Fin (k+1) → ℝ) → Fin k → ℝ} (hf : AnalyticAt ℝ f 0)
    (hf0 : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), f (Fin.cons 0 x) = 0)
    (hgraph : ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ), 0 < q.2 → graphPoint f q ∈ Ω) :
    ∃ c C t₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < t₀ ∧ ∀ t, 0 < t → t < t₀ →
      ∃ a : Fin k → ℂ, ‖a‖ ≤ C*t ∧ ball a (c*t) ⊆ Ω := by
  have hG := graphPoint_contDiffAt hf
  obtain ⟨V,hV,hGV⟩ := hG.contDiffOn (m := 1) (by norm_num) (by norm_num)
  have hall : ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ), q ∈ V ∧
      (0 < q.2 → graphPoint f q ∈ Ω) := Filter.Eventually.and hV hgraph
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hall
  let e := min (ε/2) (r/2)
  have he : 0 < e := lt_min (half_pos hε) (half_pos hr)
  have heε : e ≤ ε := (min_le_left _ _).trans (by linarith)
  have her : e < r := (min_le_right _ _).trans_lt (by linarith)
  have hproduct : closedBall (0 : Fin k → ℝ) e ×ˢ Icc 0 (r/2) ⊆ ball 0 r := by
    rintro ⟨x,u⟩ ⟨hx,hu⟩
    rw [mem_ball,dist_zero_right,Prod.norm_def,max_lt_iff,Real.norm_eq_abs,abs_of_nonneg hu.1]
    exact ⟨(mem_closedBall_zero_iff.mp hx).trans_lt her,hu.2.trans_lt (by linarith)⟩
  have hgraphs : ∀ x ∈ closedBall 0 e, ∀ u ∈ Ioo 0 (r/2), graphPoint f (x,u) ∈ Ω := by
    intro x hx u hu
    exact (hrs (hproduct ⟨hx,⟨hu.1.le,hu.2.le⟩⟩)).2 hu.1
  by_cases hk : k = 0
  · subst k
    have h0 : (0 : Fin 0 → ℂ) ∈ Ω := by
      have hi := hgraphs 0 (mem_closedBall_self he.le) (r/4) ⟨by positivity,by linarith⟩
      simpa only [Subsingleton.elim (graphPoint f ((0 : Fin 0 → ℝ),r/4)) 0] using hi
    refine ⟨1,1,1,by norm_num,by norm_num,by norm_num,?_⟩
    intro t ht _
    refine ⟨(0 : Fin 0 → ℂ),by simpa only [norm_zero,one_mul] using ht.le,?_⟩
    intro z _
    simpa only [Subsingleton.elim z 0] using h0
  · let : NeZero k := ⟨hk⟩
    obtain ⟨D⟩ := localBishopData_exists hf hf0 he
    exact bishopData_noncollapse D hΩ (discContinuityWithin_mono hCP heε) (half_pos hr)
      (hGV.continuousOn.mono fun q hq => (hrs (hproduct hq)).1) hgraphs

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_InteriorBallsChangeCoordinates
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology NNReal

theorem interior_balls_change_coordinates
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : OpenPartialHomeomorph E F) (hem : (0 : E) ∈ e.source) (he0 : e 0 = 0)
    (he : ContDiffAt ℝ 1 e 0) (hei : ContDiffAt ℝ 1 e.symm 0)
    {Ω : Set E} {c C t₀ : ℝ} (hc : 0 < c) (hC : 0 < C) (ht₀ : 0 < t₀)
    (hballs : ∀ t, 0 < t → t < t₀ → ∃ a : E, ‖a‖ ≤ C*t ∧ ball a (c*t) ⊆ Ω) :
    ∃ d D t₁ : ℝ, 0 < d ∧ 0 < D ∧ 0 < t₁ ∧ ∀ t, 0 < t → t < t₁ →
      ∃ b : F, ‖b‖ ≤ D*t ∧ ball b (d*t) ⊆ e '' (Ω ∩ e.source) := by
  obtain ⟨L,S,hS,hL⟩ := he.exists_lipschitzOnWith
  obtain ⟨K,T,hT,hK⟩ := hei.exists_lipschitzOnWith
  have htar : (0 : F) ∈ e.target := he0 ▸ e.map_source hem
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hS (e.open_source.mem_nhds hem))
  obtain ⟨R,hR,hRt⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hT (e.open_target.mem_nhds htar))
  let d : ℝ := c/((K:ℝ)+1)
  let D : ℝ := ((L:ℝ)+1)*C
  have hKp : 0 < (K:ℝ)+1 := by positivity
  have hLp : 0 < (L:ℝ)+1 := by positivity
  have hd : 0 < d := div_pos hc hKp
  have hD : 0 < D := mul_pos hLp hC
  let t₁ := min t₀ (min (r/(C+1)) (R/(D+d+1)))
  have ht₁ : 0 < t₁ := lt_min ht₀ (lt_min (div_pos hr (by positivity)) (div_pos hR (by positivity)))
  refine ⟨d,D,t₁,hd,hD,ht₁,?_⟩
  intro t ht htt
  have htt₀ : t < t₀ := htt.trans_le (min_le_left _ _)
  have htr : t < r/(C+1) := (htt.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have htR : t < R/(D+d+1) := (htt.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hCr : C*t < r := by
    have hh := (lt_div_iff₀ (by positivity : 0 < C+1)).mp htr
    nlinarith
  have hDR : D*t+d*t < R := by
    have hh := (lt_div_iff₀ (by positivity : 0 < D+d+1)).mp htR
    nlinarith
  obtain ⟨a,ha,haball⟩ := hballs t ht htt₀
  have har : a ∈ ball (0 : E) r := mem_ball_zero_iff.mpr (ha.trans_lt hCr)
  have has : a ∈ e.source := (hrs har).2
  have hLa : ‖e a‖ ≤ (L:ℝ)*‖a‖ := by
    simpa only [he0,dist_zero_right] using
      hL.dist_le_mul a (hrs har).1 0 (hrs (mem_ball_self hr)).1
  have heb : ‖e a‖ ≤ D*t := by
    calc ‖e a‖ ≤ (L:ℝ) * ‖a‖ := hLa
         _ ≤ (L:ℝ)*(C*t) := mul_le_mul_of_nonneg_left ha L.coe_nonneg
         _ ≤ D*t := by dsimp [D]; nlinarith [L.coe_nonneg]
  have hear : e a ∈ ball (0 : F) R := mem_ball_zero_iff.mpr (heb.trans_lt (by nlinarith))
  refine ⟨e a,heb,?_⟩
  intro y hy
  have hyr : y ∈ ball (0 : F) R := by
    apply mem_ball_zero_iff.mpr
    have hn : ‖y‖ ≤ dist y (e a)+‖e a‖ := by
      simpa only [dist_zero_right] using dist_triangle y (e a) 0
    have hd' : dist y (e a) < d*t := hy
    linarith
  have hyt : y ∈ e.target := (hRt hyr).2
  have hpre : e.symm y ∈ ball a (c*t) := by
    have hdist : dist (e.symm y) a ≤ (K:ℝ) * dist y (e a) := by
      simpa only [e.left_inv has] using
        hK.dist_le_mul y (hRt hyr).1 (e a) (hRt hear).1
    have hd' : dist y (e a) < d*t := hy
    have hprod : ((K:ℝ)+1)*(d*t) = c*t := by dsimp [d]; field_simp
    have hlt : (K:ℝ)*dist y (e a) < c*t := by
      calc (K:ℝ)*dist y (e a) ≤ ((K:ℝ)+1)*dist y (e a) := by nlinarith [dist_nonneg (x:=y) (y:=e a)]
           _ < ((K:ℝ)+1)*(d*t) := mul_lt_mul_of_pos_left hd' hKp
           _ = c*t := hprod
    exact hdist.trans_lt hlt
  exact ⟨e.symm y,⟨haball hpre,e.map_target hyt⟩,e.right_inv hyt⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SmallSlopeGraphComplexification
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Flatten
open Set Filter Metric
open scoped Topology

lemma realEmbedding_norm {k : ℕ} (x : Fin k → ℝ) : ‖realEmbedding k x‖ = ‖x‖ := by
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun i => by
      simpa [realEmbedding] using norm_le_pi_norm x i
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => by
      simpa [realEmbedding] using norm_le_pi_norm (realEmbedding k x) i

lemma realPart_norm_le {k : ℕ} (z : Fin k → ℂ) : ‖realPart k z‖ ≤ ‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact (Complex.abs_re_le_norm (z i)).trans (norm_le_pi_norm z i)

lemma imaginaryPart_norm_le {k : ℕ} (z : Fin k → ℂ) : ‖imaginaryPart k z‖ ≤ ‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact (Complex.abs_im_le_norm (z i)).trans (norm_le_pi_norm z i)

lemma complexification_derivative_norm_le {k m : ℕ}
    {f : (Fin k → ℝ) → Fin m → ℝ} (hf : DifferentiableAt ℝ f 0)
    {g : (Fin k → ℂ) → Fin m → ℂ} (hg : DifferentiableAt ℂ g 0)
    (he : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), g (realEmbedding k x) = realEmbedding m (f x)) :
    ‖fderiv ℂ g 0‖ ≤ 2*‖fderiv ℝ f 0‖ := by
  have h1 := ((hg.hasFDerivAt.restrictScalars ℝ).comp 0 (realEmbedding k).hasFDerivAt)
  have h2 := ((realEmbedding m).hasFDerivAt.comp 0 hf.hasFDerivAt)
  have hreal : ∀ x, fderiv ℂ g 0 (realEmbedding k x) = realEmbedding m (fderiv ℝ f 0 x) := by
    have h1' : HasFDerivAt (fun x => realEmbedding m (f x))
        ((fderiv ℂ g 0).restrictScalars ℝ ∘L realEmbedding k) 0 :=
      h1.congr_of_eventuallyEq (he.mono fun x hx => hx.symm)
    have h := h1'.unique h2
    intro x
    exact congrArg (fun L : (Fin k → ℝ) →L[ℝ] (Fin m → ℂ) => L x) h
  apply (fderiv ℂ g 0).opNorm_le_bound (by positivity)
  intro z
  have hz : z = realEmbedding k (realPart k z)+Complex.I • realEmbedding k (imaginaryPart k z) := by
    ext i
    simpa [realEmbedding,realPart,imaginaryPart,mul_comm] using (Complex.re_add_im (z i)).symm
  calc
    ‖fderiv ℂ g 0 z‖ = ‖realEmbedding m (fderiv ℝ f 0 (realPart k z)) +
        Complex.I • realEmbedding m (fderiv ℝ f 0 (imaginaryPart k z))‖ := by
          conv_lhs => rw [hz]
          rw [map_add,map_smul,hreal,hreal]
    _ ≤ ‖fderiv ℝ f 0 (realPart k z)‖ + ‖fderiv ℝ f 0 (imaginaryPart k z)‖ := by
      simpa only [norm_smul,Complex.norm_I,one_mul,realEmbedding_norm] using norm_add_le
        (realEmbedding m (fderiv ℝ f 0 (realPart k z)))
        (Complex.I • realEmbedding m (fderiv ℝ f 0 (imaginaryPart k z)))
    _ ≤ ‖fderiv ℝ f 0‖ * ‖z‖ + ‖fderiv ℝ f 0‖ * ‖z‖ :=
      add_le_add ((fderiv ℝ f 0).le_opNorm _ |>.trans
        (mul_le_mul_of_nonneg_left (realPart_norm_le z) (norm_nonneg _)))
        ((fderiv ℝ f 0).le_opNorm _ |>.trans
        (mul_le_mul_of_nonneg_left (imaginaryPart_norm_le z) (norm_nonneg _)))
    _ = _ := by ring

theorem small_slope_graph_complexification {k : ℕ} {φ : (Fin k → ℝ) → Fin k → ℝ}
    (hφ : AnalyticAt ℝ φ 0) (hφ0 : φ 0 = 0) (hdφ : ‖fderiv ℝ φ 0‖ < 1/2) :
    ∃ e : OpenPartialHomeomorph (Fin k → ℂ) (Fin k → ℂ),
      (0 : Fin k → ℂ) ∈ e.source ∧ e 0 = 0 ∧
      AnalyticAt ℂ e 0 ∧ AnalyticAt ℂ e.symm 0 ∧
      ∀ᶠ x in 𝓝 (0 : Fin k → ℝ),
        e (realEmbedding k x) = fun i => (x i : ℂ)+Complex.I*(φ x i : ℂ) := by
  obtain ⟨Φ,hΦ,hΦeq⟩ := Release061.Complexify.vector hφ
  have hEq : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), Φ (realEmbedding k x) = realEmbedding k (φ x) := hΦeq
  have hΦ0 : Φ 0 = 0 := by
    simpa only [map_zero,hφ0] using hEq.self_of_nhds
  let L := fderiv ℂ Φ 0
  have hLn : ‖L‖ < 1 := (complexification_derivative_norm_le hφ.differentiableAt
    hΦ.differentiableAt hEq).trans_lt (by linarith)
  have hu : IsUnit (1+Complex.I • L) := by
    have hn : ‖-(Complex.I • L)‖ < 1 := by simpa only [norm_neg,norm_smul,Complex.norm_I,one_mul] using hLn
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hn
  obtain ⟨u,hu⟩ := hu
  let i := ContinuousLinearEquiv.ofUnit u
  have hi : (i : (Fin k → ℂ) →L[ℂ] (Fin k → ℂ)) = 1+Complex.I • L := hu
  let Q : (Fin k → ℂ) → Fin k → ℂ := fun z => z+Complex.I • Φ z
  have hQa : AnalyticAt ℂ Q 0 := analyticAt_id.add (hΦ.const_smul (c := Complex.I))
  have hQ0 : Q 0 = 0 := by simp only [Q,hΦ0,smul_zero,add_zero]
  have hQd : HasFDerivAt Q (i : (Fin k → ℂ) →L[ℂ] (Fin k → ℂ)) 0 := by
    rw [hi]
    exact (hasFDerivAt_id (𝕜 := ℂ) (0 : Fin k → ℂ)).add (hΦ.differentiableAt.hasFDerivAt.const_smul Complex.I)
  have hs : HasStrictFDerivAt Q (i : (Fin k → ℂ) →L[ℂ] (Fin k → ℂ)) 0 := by
    simpa only [hQd.fderiv] using hQa.hasStrictFDerivAt
  let e := hs.toOpenPartialHomeomorph Q
  have he : (e : (Fin k → ℂ) → Fin k → ℂ) = Q := hs.toOpenPartialHomeomorph_coe
  have hem : (0 : Fin k → ℂ) ∈ e.source := hs.mem_toOpenPartialHomeomorph_source
  obtain ⟨p,hp⟩ := hQa
  have hc : p 1 = (continuousMultilinearCurryFin1 ℂ (Fin k → ℂ) (Fin k → ℂ)).symm
      (i : (Fin k → ℂ) →L[ℂ] (Fin k → ℂ)) := by
    apply (continuousMultilinearCurryFin1 ℂ (Fin k → ℂ) (Fin k → ℂ)).injective
    simpa using hp.hasFDerivAt.unique hQd
  have hia := (e.hasFPowerSeriesAt_symm hem (he ▸ hp) hc).analyticAt
  refine ⟨e,hem,by rw [he,hQ0],he ▸ hp.analyticAt,?_,?_⟩
  · simpa only [he,hQ0] using hia
  · filter_upwards [hEq] with x hx
    rw [he]
    dsimp [Q]
    rw [hx]
    rfl
end Release061.Flatten

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_InteriorBallsSmallSlope
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology

theorem interior_balls_from_small_slope_graphs_oai {k : ℕ} {Ω : Set (Fin k → ℂ)}
    (hΩ : IsOpen Ω) {ε : ℝ} (hε : 0 < ε) (hCP : Wiener.DiscContinuityWithin k Ω ε)
    {φ : (Fin k → ℝ) → Fin k → ℝ} (hφ : AnalyticAt ℝ φ 0) (hφ0 : φ 0 = 0)
    (hdφ : ‖fderiv ℝ φ 0‖ < 1/2)
    {G : (Fin k → ℝ) × ℝ → Fin k → ℂ} (hG : AnalyticAt ℝ G 0)
    (hG0 : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ),
      G (x,0) = fun i => (x i : ℂ)+Complex.I*(φ x i : ℂ))
    (hGΩ : ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ), 0 < q.2 → G q ∈ Ω) :
    ∃ c C t₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < t₀ ∧ ∀ t, 0 < t → t < t₀ →
      ∃ a : Fin k → ℂ, ‖a‖ ≤ C*t ∧ ball a (c*t) ⊆ Ω := by
  obtain ⟨e,hem,he0,he,hei,hbase⟩ := Flatten.small_slope_graph_complexification hφ hφ0 hdφ
  have htar : (0 : Fin k → ℂ) ∈ e.target := he0 ▸ e.map_source hem
  have hei0 : e.symm 0 = 0 := by
    calc e.symm 0 = e.symm (e 0) := congrArg e.symm he0.symm
         _ = 0 := e.left_inv hem
  have hGzero : G 0 = 0 := by
    have hh := hG0.self_of_nhds
    change G (0,0) = fun _ => 0
    simpa only [hφ0,Pi.zero_apply,Complex.ofReal_zero,mul_zero,add_zero] using hh
  let Ω' := e.source ∩ e ⁻¹' Ω
  let G' : (Fin k → ℝ) × ℝ → Fin k → ℂ := e.symm ∘ G
  have hG' : AnalyticAt ℝ G' 0 := by
    have hi : AnalyticAt ℝ e.symm (G 0) := by rw [hGzero]; exact hei.restrictScalars
    exact hi.comp hG
  have hG'base : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), G' (x,0) = Flatten.realEmbedding k x := by
    have ht : Tendsto (Flatten.realEmbedding k) (𝓝 0) (𝓝 (0 : Fin k → ℂ)) := by
      simpa only [map_zero] using (Flatten.realEmbedding k).continuous.continuousAt.tendsto (x := 0)
    filter_upwards [hG0,hbase,ht (e.open_source.mem_nhds hem)] with x hx hx' hxs
    change e.symm (G (x,0)) = Flatten.realEmbedding k x
    rw [hx,← hx',e.left_inv hxs]
  have hG'Ω : ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ), 0 < q.2 → G' q ∈ Ω' := by
    have ht : Tendsto G (𝓝 0) (𝓝 (0 : Fin k → ℂ)) := by
      simpa only [hGzero] using hG.continuousAt.tendsto
    filter_upwards [hGΩ,ht (e.open_target.mem_nhds htar)] with q hq hqt
    intro hu
    exact ⟨e.map_target hqt,by change e (e.symm (G q)) ∈ Ω; rw [e.right_inv hqt]; exact hq hu⟩
  obtain ⟨f,hf,hf0,hfΩ⟩ := Flatten.analytic_family_regraph hG' hG'base hG'Ω
  have het : Tendsto e (𝓝 0) (𝓝 (0 : Fin k → ℂ)) := by
    simpa only [he0] using he.continuousAt.tendsto
  have hnh : ∀ᶠ z in 𝓝 (0 : Fin k → ℂ),
      AnalyticAt ℂ e z ∧ z ∈ e.source ∧ e z ∈ ball 0 ε :=
    he.eventually_analyticAt.and (Filter.Eventually.and (e.open_source.mem_nhds hem) (het (ball_mem_nhds _ hε)))
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hnh
  have hCP' : Wiener.DiscContinuityWithin k Ω' r :=
    Wiener.discContinuityWithin_pullback hCP (fun z hz => (hrs hz).1)
      (fun z hz => (hrs hz).2.1) (fun z hz => (hrs hz).2.2)
  obtain ⟨c,C,t₀,hc,hC,ht₀,hballs⟩ := Wiener.interior_balls_from_analytic_graphs
    (e.isOpen_inter_preimage hΩ) hr hCP' hf hf0 hfΩ
  have her : ContDiffAt ℝ 1 e 0 := he.restrictScalars.contDiffAt
  have heir : ContDiffAt ℝ 1 e.symm 0 := hei.restrictScalars.contDiffAt
  obtain ⟨d,D,t₁,hd,hD,ht₁,hballs'⟩ :=
    interior_balls_change_coordinates e hem he0 her heir hc hC ht₀ hballs
  refine ⟨d,D,t₁,hd,hD,ht₁,?_⟩
  intro t ht htt
  obtain ⟨a,ha,hab⟩ := hballs' t ht htt
  refine ⟨a,ha,?_⟩
  intro z hz
  obtain ⟨y,hy,rfl⟩ := hab hz
  exact hy.1.2

end Release061

end

end OAI
end

theorem solution : type_of% @OAI.Release061.interior_balls_from_small_slope_graphs_oai := @OAI.Release061.interior_balls_from_small_slope_graphs_oai
