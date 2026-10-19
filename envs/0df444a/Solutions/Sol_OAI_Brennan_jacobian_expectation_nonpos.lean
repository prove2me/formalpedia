-- Prove2me | solution 1 for OAI.Brennan.jacobian_expectation_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T20:27:29.53498+00:00
-- url     : https://prove2.me/submissions/2eaa68ac-8b7f-4340-a472-9d31eb057ede

import Mathlib
import Definitions.Def_Brennan
import Definitions.Def_OAIQWBRNK000
import Definitions.Def_OAIQWBRN000

section
-- module Solutions.OAIQW_Brennan.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434
end

section
-- module Solutions.OAIQW_Brennan.LogIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma HasLogIncrement.homotopy {H : C(unitInterval × unitInterval, ℂ)}
    (hH : ∀ p, H p ≠ 0) (hloop : ∀ s, H (s,1) = H (s,0)) {q : ℂ}
    (h : HasLogIncrement ⟨fun t => H (0,t), by fun_prop⟩ q) :
    HasLogIncrement ⟨fun t => H (1,t), by fun_prop⟩ q := by
  let := (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).contractibleSpace
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by simp⟩)
  let := (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).locallyPathConnectedSpace
  obtain ⟨A,hA⟩ := exists_log_lift_of_simplyConnected (0,0) H hH
  have hi : HasLogIncrement ⟨fun t => H (0,t), by fun_prop⟩ (A (0,1)-A (0,0)) :=
    ⟨⟨fun t => A (0,t), by fun_prop⟩, fun t => hA (0,t), rfl⟩
  have hc := log_lifts_difference_constant
    (show Continuous (fun s => A (s,1)) by fun_prop)
    (show Continuous (fun s => A (s,0)) by fun_prop)
    (fun s => by rw [hA, hA, hloop]) (0 : unitInterval) 1
  refine ⟨⟨fun t => A (1,t), by fun_prop⟩, fun t => hA (1,t), ?_⟩
  change A (1,1)-A (1,0)=q
  exact hc.trans (hi.unique h)

lemma windingNumber_homotopy (H : C(unitInterval × unitInterval, ℂ))
    (hH : ∀ p, H p ≠ 0) (hloop : ∀ s, H (s,1) = H (s,0)) :
    windingNumber ⟨fun t => H (1,t), by fun_prop⟩ =
      windingNumber ⟨fun t => H (0,t), by fun_prop⟩ := by
  apply windingNumber_eq_of_logIncrement (hloop 1)
  exact (windingNumber_spec ⟨fun t => H (0,t), by fun_prop⟩ (hloop 0)
    (fun t => hH (0,t))).homotopy hH hloop

lemma loopIndex_eventually_eq (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0)
    {a : ℂ} (ha : a ∉ range γ) : ∀ᶠ b in 𝓝 a, loopIndex γ b = loopIndex γ a := by
  have hn (t) : γ t-a ≠ 0 := sub_ne_zero.mpr (fun h => ha ⟨t,h⟩)
  obtain ⟨d,hd,hdist⟩ := isCompact_univ.exists_forall_le'
    (show ContinuousOn (fun t : unitInterval => ‖γ t-a‖) univ by fun_prop)
    (a := 0) (fun t _ => norm_pos_iff.mpr (hn t))
  filter_upwards [Metric.ball_mem_nhds a hd] with b hb
  apply windingNumber_perturb (by simp [hloop]) (by simp [hloop]) hn
  intro t
  change ‖(γ t-b)-(γ t-a)‖ < ‖γ t-a‖
  rw [show (γ t-b)-(γ t-a)=a-b by ring, norm_sub_rev]
  exact (show ‖b-a‖ < d by simpa [Metric.mem_ball, dist_eq_norm] using hb).trans_le (hdist t (mem_univ t))

lemma continuousOn_loopIndex (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) :
    ContinuousOn (loopIndex γ) (range γ)ᶜ := by
  intro a ha
  apply ContinuousAt.continuousWithinAt
  have he : loopIndex γ =ᶠ[𝓝 a] fun _ => loopIndex γ a :=
    loopIndex_eventually_eq γ hloop ha
  exact continuousAt_const.congr he.symm

lemma hasLogIncrement_constant (a : ℂ) (ha : a ≠ 0) :
    HasLogIncrement (ContinuousMap.const unitInterval a) 0 := by
  exact ⟨ContinuousMap.const unitInterval (Complex.log a),
    fun _ => Complex.exp_log ha, sub_self _⟩

lemma loopIndex_eq_zero_of_norm_lt (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0)
    {a : ℂ} (ha : ∀ t, ‖γ t‖ < ‖a‖) : loopIndex γ a = 0 := by
  have hane : a ≠ 0 := norm_pos_iff.mp ((norm_nonneg (γ 0)).trans_lt (ha 0))
  apply windingNumber_eq_of_logIncrement (by simp [hloop])
  have hh : HasLogIncrement ⟨fun t => γ t-a, by fun_prop⟩ 0 :=
    (hasLogIncrement_constant (-a) (neg_ne_zero.mpr hane)).perturb rfl
      (by simp [hloop]) (fun t => by simpa using ha t)
  simpa using hh

lemma loopIndex_zero_outside_ball (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ a : ℂ, R ≤ ‖a‖ → loopIndex γ a = 0 := by
  obtain ⟨R,-,hR⟩ := (isCompact_range γ.continuous).isBounded.exists_pos_norm_lt
  refine ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro a ha
  apply loopIndex_eq_zero_of_norm_lt γ hloop
  intro t
  exact (hR (γ t) ⟨t,rfl⟩).trans_le ((le_max_left R 1).trans ha)

lemma isOpen_windingInterior (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) :
    IsOpen (windingInterior γ) := by
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  have hc := (isCompact_range γ.continuous).isClosed.isOpen_compl.mem_nhds ha.1
  filter_upwards [hc, loopIndex_eventually_eq γ hloop ha.1] with b hb heq
  exact ⟨hb, heq ▸ ha.2⟩

lemma isBounded_windingInterior (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) :
    Bornology.IsBounded (windingInterior γ) := by
  obtain ⟨R,-,hR⟩ := loopIndex_zero_outside_ball γ hloop
  apply (Metric.isBounded_ball (x := (0 : ℂ)) (r := R)).subset
  intro a ha
  rw [Metric.mem_ball, dist_zero_right]
  by_contra h
  exact ha.2 (hR a (le_of_not_gt h))

lemma frontier_windingInterior_subset (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) :
    frontier (windingInterior γ) ⊆ range γ := by
  intro a ha
  by_contra han
  have hn : (range γ)ᶜ ∈ 𝓝 a :=
    (isCompact_range γ.continuous).isClosed.isOpen_compl.mem_nhds han
  have he := loopIndex_eventually_eq γ hloop han
  by_cases hi : loopIndex γ a = 0
  · have hh : (windingInterior γ)ᶜ ∈ 𝓝 a := by
      filter_upwards [he] with b hb
      intro hbin
      exact hbin.2 (hb.trans hi)
    exact (mem_closure_iff_nhds.1 ha.1 _ hh).elim (fun b hb => hb.1 hb.2)
  · have hnmem := ha.2
    rw [(isOpen_windingInterior γ hloop).interior_eq] at hnmem
    exact hnmem ⟨han,hi⟩

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.Distortion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma schlicht_lower_growth {f : ℂ → ℂ} (hf : Schlicht f) {z : ℂ} (hz : z ∈ disk) :
    ‖z‖/4 ≤ ‖f z‖ := by
  by_cases hzero : z = 0
  · simp [hzero,hf.2.1]
  have h := schlicht_separation hf (show (0 : ℂ) ∈ disk by simp [disk]) hz
    (norm_pos_iff.mpr hzero)
    (Metric.ball_subset_ball (show ‖z‖ ≤ 1 by exact le_of_lt (by simpa [disk] using hz)))
    (show ‖z‖ ≤ ‖z-(0 : ℂ)‖ by simp)
  simpa [hf.2.1,hf.2.2] using h

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.HalfPlane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma reciprocalDeriv_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z w : ℂ} (hz : z ∈ halfPlane) (hw : w ∈ halfPlane) :
    reciprocalDeriv (reroot f z) w = reciprocalDeriv f (affine z w) / reciprocalDeriv f z := by
  simp [reciprocalDeriv, deriv_reroot hf hz hw, div_eq_mul_inv, mul_comm]

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.CriticalMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma logarithmicJet_eq {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z : ℂ} (hz : z ∈ halfPlane) :
    logarithmicJet f z = -Complex.I * (z.im : ℂ) * deriv (deriv f) z / deriv f z := by
  have han : AnalyticAt ℂ f z := hf.1.analyticOnNhd isOpen_halfPlane z hz
  have hd : deriv f z ≠ 0 := univalent_deriv_ne_zero isOpen_halfPlane hf hz
  have hq : deriv (reciprocalDeriv f) z = -deriv (deriv f) z / (deriv f z)^2 :=
    (han.deriv.differentiableAt.hasDerivAt.inv hd).deriv
  rw [logarithmicJet, hq, reciprocalDeriv]
  field_simp

lemma fderiv_criticalMap_apply {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z : ℂ} (hz : z ∈ halfPlane) (k : ℝ) (v : ℂ) :
    fderiv ℝ (criticalMap f k) z v = deriv f z * v -
      Complex.I / (k : ℂ) * ((v.im : ℂ) * deriv f z +
        (z.im : ℂ) * (deriv (deriv f) z * v)) := by
  have han : AnalyticAt ℂ f z := hf.1.analyticOnNhd isOpen_halfPlane z hz
  have ha := han.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hb := han.deriv.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hc := Complex.ofRealCLM.hasFDerivAt.comp z Complex.imCLM.hasFDerivAt
  have hG := ha.sub ((hc.const_mul (Complex.I / (k : ℂ))).mul hb)
  have hG' : HasFDerivAt (criticalMap f k)
      (ContinuousLinearMap.restrictScalars ℝ (ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)) -
        ((Complex.I / (k : ℂ) * (z.im : ℂ)) •
          ContinuousLinearMap.restrictScalars ℝ (ContinuousLinearMap.toSpanSingleton ℂ (deriv (deriv f) z)) +
        deriv f z • (Complex.I / (k : ℂ)) •
          (Complex.ofRealCLM.comp Complex.imCLM))) z := hG
  rw [hG'.fderiv]
  change v * deriv f z -
    ((Complex.I / (k : ℂ) * (z.im : ℂ)) * (v * deriv (deriv f) z) +
      deriv f z * (Complex.I / (k : ℂ) * (v.im : ℂ))) = _
  ring

lemma criticalMap_columns {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z : ℂ} (hz : z ∈ halfPlane) (k : ℝ) (hk : k ≠ 0) :
    fderiv ℝ (criticalMap f k) z 1 = deriv f z / (k : ℂ) * ((k : ℂ) + logarithmicJet f z) ∧
    fderiv ℝ (criticalMap f k) z Complex.I =
      Complex.I * (deriv f z / (k : ℂ)) * ((k : ℂ) - 1 + logarithmicJet f z) := by
  have hd : deriv f z ≠ 0 := univalent_deriv_ne_zero isOpen_halfPlane hf hz
  have hk' : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  constructor <;> rw [fderiv_criticalMap_apply hf hz, logarithmicJet_eq hf hz] <;>
    simp only [Complex.one_im, Complex.I_im, Complex.ofReal_zero, Complex.ofReal_one,
      zero_mul, one_mul, mul_one, zero_add] <;> field_simp <;> ring

lemma critical_columns_det (u q : ℂ) (k : ℝ) :
    (u * ((k : ℂ) + q)).re * (Complex.I * u * ((k : ℂ) - 1 + q)).im -
      (Complex.I * u * ((k : ℂ) - 1 + q)).re * (u * ((k : ℂ) + q)).im =
    ‖u‖^2 * (k * (k-1) + (2*k-1)*q.re + ‖q‖^2) := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
    Complex.sq_norm, Complex.normSq_apply]
  ring

lemma normalizedJacobian_formula {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z : ℂ} (hz : z ∈ halfPlane) (k : ℝ) (hk : k ≠ 0) :
    k^2 * normalizedJacobian f k z =
      k * (k - 1) + (2*k - 1) * (logarithmicJet f z).re + ‖logarithmicJet f z‖^2 := by
  have hd : ‖deriv f z‖ ≠ 0 := norm_ne_zero_iff.mpr
    (univalent_deriv_ne_zero isOpen_halfPlane hf hz)
  obtain ⟨hc₁, hc₂⟩ := criticalMap_columns hf hz k hk
  rw [normalizedJacobian, determinant_complex_real]
  change k ^ 2 * (((fderiv ℝ (criticalMap f k) z 1).re *
    (fderiv ℝ (criticalMap f k) z Complex.I).im -
    (fderiv ℝ (criticalMap f k) z Complex.I).re *
    (fderiv ℝ (criticalMap f k) z 1).im) / ‖deriv f z‖^2) = _
  rw [hc₁, hc₂, critical_columns_det, norm_div, Complex.norm_real,
    Real.norm_eq_abs, div_pow, sq_abs]
  field_simp

lemma logarithmicJet_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z w : ℂ} (hz : z ∈ halfPlane) (hw : w ∈ halfPlane) :
    logarithmicJet (reroot f z) w = logarithmicJet f (affine z w) := by
  have hqz : reciprocalDeriv f z ≠ 0 := inv_ne_zero
    (univalent_deriv_ne_zero isOpen_halfPlane hf hz)
  have hqw : reciprocalDeriv f (affine z w) ≠ 0 := inv_ne_zero
    (univalent_deriv_ne_zero isOpen_halfPlane hf (affine_mem hz hw))
  have heq : reciprocalDeriv (reroot f z) =ᶠ[𝓝 w]
      (fun u => reciprocalDeriv f (affine z u) / reciprocalDeriv f z) := by
    filter_upwards [isOpen_halfPlane.mem_nhds hw] with u hu
    exact reciprocalDeriv_reroot hf hz hu
  have hD := ((((hasDerivAt_reciprocalDeriv hf (affine_mem hz hw)).comp w
    (hasDerivAt_affine z w)).div_const (reciprocalDeriv f z)).congr_of_eventuallyEq heq).deriv
  have him : ((affine z w).im : ℂ) = (z.im : ℂ) * (w.im : ℂ) := by
    simp [affine]
  rw [logarithmicJet, hD, reciprocalDeriv_reroot hf hz hw, logarithmicJet, him]
  field_simp

lemma criticalMap_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z w : ℂ} (hz : z ∈ halfPlane) (hw : w ∈ halfPlane) (k : ℝ) :
    criticalMap (reroot f z) k w =
      (criticalMap f k (affine z w) - f z) / ((z.im : ℂ) * deriv f z) := by
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hd : deriv f z ≠ 0 := univalent_deriv_ne_zero isOpen_halfPlane hf hz
  have him : ((affine z w).im : ℂ) = (z.im : ℂ) * (w.im : ℂ) := by
    simp [affine]
  rw [criticalMap, deriv_reroot hf hz hw]
  simp only [reroot, criticalMap, him]
  field_simp
  ring

lemma normalizedJacobian_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z w : ℂ} (hz : z ∈ halfPlane) (hw : w ∈ halfPlane) (k : ℝ) (hk : k ≠ 0) :
    normalizedJacobian (reroot f z) k w = normalizedJacobian f k (affine z w) := by
  apply (mul_left_cancel₀ (pow_ne_zero 2 hk))
  rw [normalizedJacobian_formula (reroot_normalized hf hz).1 hw k hk,
    normalizedJacobian_formula hf (affine_mem hz hw) k hk, logarithmicJet_reroot hf hz hw]

lemma differentiableAt_criticalMap {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z : ℂ} (hz : z ∈ halfPlane) (k : ℝ) :
    DifferentiableAt ℝ (criticalMap f k) z := by
  have han : AnalyticAt ℂ f z := hf.1.analyticOnNhd isOpen_halfPlane z hz
  exact ((han.differentiableAt.restrictScalars ℝ).sub
    (((Complex.ofRealCLM.differentiableAt.comp z Complex.imCLM.differentiableAt).const_mul
      (Complex.I / (k : ℂ))).mul (han.deriv.differentiableAt.restrictScalars ℝ)))

lemma critical_fiber_discrete {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} {ξ : ℂ} (hreg : ∀ z ∈ halfPlane,
      criticalMap f k z = ξ → normalizedJacobian f k z ≠ 0) :
    IsDiscrete {z | z ∈ halfPlane ∧ criticalMap f k z = ξ} := by
  rw [isDiscrete_iff_nhdsNE]
  intro z hz
  have hd : LinearMap.det (fderiv ℝ (criticalMap f k) z).toLinearMap ≠ 0 :=
    (div_ne_zero_iff.mp (hreg z hz.1 hz.2)).1
  let e : ℂ ≃L[ℝ] ℂ :=
    (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr hd)).toContinuousLinearEquiv
  have he : (e : ℂ → ℂ) = fderiv ℝ (criticalMap f k) z := by
    funext w
    exact LinearMap.equivOfIsUnitDet_apply (isUnit_iff_ne_zero.mpr hd) w
  have ha : ∃ C, AntilipschitzWith C (fderiv ℝ (criticalMap f k) z) := by
    rw [← he]
    exact ⟨_, e.antilipschitz⟩
  rw [Filter.inf_principal_eq_bot]
  filter_upwards [(differentiableAt_criticalMap hf hz.1 k).hasFDerivAt.eventually_ne ha] with w hw
  exact fun h => hw h.2

lemma finite_critical_superlevel {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} {ξ : ℂ} (hg : GoodPair f k ξ) {h : ℝ} (hh : 0 < h) :
    {z | z ∈ halfPlane ∧ criticalMap f k z = ξ ∧
      ENNReal.ofReal h ≤ potential f k ξ z}.Finite := by
  let P := {z | z ∈ halfPlane ∧ ENNReal.ofReal h ≤ potential f k ξ z}
  have hP : IsCompact P := hg.1 h hh
  have hc : ContinuousOn (criticalMap f k) P := by
    intro z hz
    exact (differentiableAt_criticalMap hf hz.1 k).continuousAt.continuousWithinAt
  have hclosed := hc.preimage_isClosed_of_isClosed hP.isClosed (isClosed_singleton (x := ξ))
  have hcompact : IsCompact (P ∩ (criticalMap f k) ⁻¹' {ξ}) :=
    hP.of_isClosed_subset hclosed inter_subset_left
  have hdiscrete := (critical_fiber_discrete hf hg.2).mono
    (show P ∩ (criticalMap f k) ⁻¹' {ξ} ⊆
      {z | z ∈ halfPlane ∧ criticalMap f k z = ξ} from fun _ hz => ⟨hz.1.1, hz.2⟩)
  convert hcompact.finite hdiscrete using 1
  ext z
  simp only [P, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff]
  tauto

lemma differentiableAt_log_norm {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g z) (hn : g z ≠ 0) :
    DifferentiableAt ℝ (fun w => Real.log ‖g w‖) z :=
  ((hg.restrictScalars ℝ).norm ℂ hn).log (norm_ne_zero_iff.mpr hn)

lemma fderiv_log_norm_apply {g : ℂ → ℂ} {d z : ℂ} (hg : HasDerivAt g d z)
    (hn : g z ≠ 0) (v : ℂ) :
    fderiv ℝ (fun w => Real.log ‖g w‖) z v = (d * v / g z).re := by
  have heq : (fun w => Real.log ‖g w‖) =
      (fun w => (1 / 2 : ℝ) * Real.log (‖g w‖ ^ 2)) := by
    funext w
    rw [Real.log_pow]
    ring
  have hh := (((hg.hasFDerivAt.restrictScalars ℝ).norm_sq).log
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hn))).const_mul (1 / 2 : ℝ)
  rw [heq, hh.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, innerSL_apply_apply]
  simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.mul_im, Complex.div_re, Complex.normSq_eq_norm_sq]
  ring

lemma differentiableAt_logPotential {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z ξ : ℂ} (hz : z ∈ halfPlane) (hp : f z ≠ ξ) (k : ℝ) :
    DifferentiableAt ℝ (logPotential f k ξ) z := by
  have hd := (hf.1 z hz).differentiableAt (isOpen_halfPlane.mem_nhds hz)
  exact ((Complex.imCLM.differentiableAt.log (ne_of_gt hz)).const_mul k).sub
    (differentiableAt_log_norm (hd.sub_const ξ) (sub_ne_zero.mpr hp))

lemma fderiv_logPotential_apply {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z ξ : ℂ} (hz : z ∈ halfPlane) (hp : f z ≠ ξ) (k : ℝ) (v : ℂ) :
    fderiv ℝ (logPotential f k ξ) z v =
      k / z.im * v.im - (deriv f z * v / (f z - ξ)).re := by
  have hd := (hf.1 z hz).differentiableAt (isOpen_halfPlane.mem_nhds hz)
  have ha := (Complex.imCLM.hasFDerivAt.log (ne_of_gt hz)).const_mul k
  simp only [Complex.imCLM_apply] at ha
  have hb := differentiableAt_log_norm (hd.sub_const ξ) (sub_ne_zero.mpr hp)
  change fderiv ℝ (fun w => k * Real.log w.im - Real.log ‖f w - ξ‖) z v = _
  rw [fderiv_fun_sub ha.differentiableAt hb,
    sub_apply, ha.fderiv,
    fderiv_log_norm_apply (hd.hasDerivAt.sub_const ξ) (sub_ne_zero.mpr hp)]
  simp only [smul_apply, smul_eq_mul, Complex.imCLM_apply, div_eq_mul_inv]
  ring

lemma criticalMap_ne_pole {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} (hk : k ≠ 0) {z ξ : ℂ} (hz : z ∈ halfPlane)
    (hc : criticalMap f k z = ξ) : f z ≠ ξ := by
  intro hp
  have hn := mul_ne_zero (mul_ne_zero (div_ne_zero Complex.I_ne_zero
      (Complex.ofReal_ne_zero.mpr hk)) (Complex.ofReal_ne_zero.mpr (ne_of_gt hz)))
    (univalent_deriv_ne_zero isOpen_halfPlane hf hz)
  apply hn
  simpa [criticalMap, hp] using hc

lemma critical_difference {f : ℂ → ℂ} {k : ℝ} {z ξ : ℂ}
    (hc : criticalMap f k z = ξ) :
    f z - ξ = Complex.I / (k : ℂ) * (z.im : ℂ) * deriv f z := by
  unfold criticalMap at hc
  linear_combination hc

lemma hasDerivAt_targetRatio {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z ξ : ℂ} (hz : z ∈ halfPlane) (hp : f z ≠ ξ) :
    HasDerivAt (targetRatio f ξ)
      ((deriv (deriv f) z * (f z - ξ) - deriv f z * deriv f z) / (f z - ξ)^2) z := by
  have han : AnalyticAt ℂ f z := hf.1.analyticOnNhd isOpen_halfPlane z hz
  exact han.deriv.differentiableAt.hasDerivAt.div
    (han.differentiableAt.hasDerivAt.sub_const ξ) (sub_ne_zero.mpr hp)

lemma secondDirectional_logPotential_one {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z ξ : ℂ} (hz : z ∈ halfPlane) (hp : f z ≠ ξ) (k : ℝ) (v : ℂ) :
    secondDirectional (logPotential f k ξ) z 1 v =
      -(deriv (targetRatio f ξ) z * v).re := by
  have hd := (hf.1 z hz).differentiableAt (isOpen_halfPlane.mem_nhds hz)
  have hn := hd.continuousAt.eventually_ne hp
  have heq : (fun w => fderiv ℝ (logPotential f k ξ) w 1) =ᶠ[𝓝 z]
      (fun w => -(targetRatio f ξ w).re) := by
    filter_upwards [isOpen_halfPlane.mem_nhds hz, hn] with w hw hne
    simp only [fderiv_logPotential_apply hf hw hne, Complex.one_im, mul_zero,
      mul_one, zero_sub, targetRatio]
  have hr := (hasDerivAt_targetRatio hf hz hp).differentiableAt.hasDerivAt
  have hh := (Complex.reCLM.hasFDerivAt.comp z
    (hr.hasFDerivAt.restrictScalars ℝ)).neg
  change HasFDerivAt (fun w => -(targetRatio f ξ w).re) _ z at hh
  rw [secondDirectional, heq.fderiv_eq, hh.fderiv]
  simp only [neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, Complex.reCLM_apply, mul_comm v]

lemma secondDirectional_logPotential_I {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z ξ : ℂ} (hz : z ∈ halfPlane) (hp : f z ≠ ξ) (k : ℝ) (v : ℂ) :
    secondDirectional (logPotential f k ξ) z Complex.I v =
      -k / z.im^2 * v.im + (deriv (targetRatio f ξ) z * v).im := by
  have hd := (hf.1 z hz).differentiableAt (isOpen_halfPlane.mem_nhds hz)
  have hn := hd.continuousAt.eventually_ne hp
  have heq : (fun w => fderiv ℝ (logPotential f k ξ) w Complex.I) =ᶠ[𝓝 z]
      (fun w => k / w.im + (targetRatio f ξ w).im) := by
    filter_upwards [isOpen_halfPlane.mem_nhds hz, hn] with w hw hne
    rw [fderiv_logPotential_apply hf hw hne,
      show deriv f w * Complex.I / (f w - ξ) =
        (deriv f w / (f w - ξ)) * Complex.I by ring]
    simp only [Complex.I_im, mul_one, Complex.mul_I_re, sub_neg_eq_add, targetRatio]
  have hr := (hasDerivAt_targetRatio hf hz hp).differentiableAt.hasDerivAt
  have ha := (((hasDerivAt_inv (ne_of_gt hz)).hasFDerivAt).comp z
    Complex.imCLM.hasFDerivAt).const_mul k
  have hb := Complex.imCLM.hasFDerivAt.comp z (hr.hasFDerivAt.restrictScalars ℝ)
  have hh := ha.add hb
  change HasFDerivAt (fun w => k * w.im⁻¹ + (targetRatio f ξ w).im) _ z at hh
  simp only [← div_eq_mul_inv] at hh
  rw [secondDirectional, heq.fderiv_eq, hh.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    Complex.imCLM_apply, mul_comm v]
  ring

lemma realHessian_logPotential {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z ξ : ℂ} (hz : z ∈ halfPlane) (hp : f z ≠ ξ) (k : ℝ) :
    realHessian (logPotential f k ξ) z =
      !![-(deriv (targetRatio f ξ) z).re, (deriv (targetRatio f ξ) z).im;
        (deriv (targetRatio f ξ) z).im, -k / z.im^2 + (deriv (targetRatio f ξ) z).re] := by
  simp only [realHessian, secondDirectional_logPotential_one hf hz hp,
    secondDirectional_logPotential_I hf hz hp, mul_one, Complex.mul_I_re,
    Complex.mul_I_im, Complex.one_im, Complex.I_im, mul_zero, mul_one, zero_add, neg_neg]

lemma trace_realHessian_logPotential {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z ξ : ℂ} (hz : z ∈ halfPlane) (hp : f z ≠ ξ) (k : ℝ) :
    Matrix.trace (realHessian (logPotential f k ξ) z) = -k / z.im^2 := by
  rw [realHessian_logPotential hf hz hp]
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]

lemma trace_realHessian_negative {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} (hk : 0 < k) {z ξ : ℂ} (hz : z ∈ halfPlane) (hp : f z ≠ ξ) :
    Matrix.trace (realHessian (logPotential f k ξ) z) < 0 := by
  rw [trace_realHessian_logPotential hf hz hp]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hk) (sq_pos_of_pos hz)

lemma potential_off_pole {f : ℂ → ℂ} {k : ℝ} {ξ z : ℂ}
    (hz : z ∈ halfPlane) (hp : f z ≠ ξ) :
    potential f k ξ z = ENNReal.ofReal (z.im^k / ‖f z - ξ‖) := by
  rw [potential, ENNReal.ofReal_rpow_of_pos hz,
    ENNReal.ofReal_div_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hp))]

lemma potential_critical_height {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} (hk : 0 < k) {z ξ : ℂ} (hz : z ∈ halfPlane)
    (hc : criticalMap f k z = ξ) :
    potential f k ξ z = ENNReal.ofReal (k * z.im^(k-1) * ‖reciprocalDeriv f z‖) := by
  have hd := univalent_deriv_ne_zero isOpen_halfPlane hf hz
  have hy : z.im ≠ 0 := ne_of_gt hz
  have hn : ‖deriv f z‖ ≠ 0 := norm_ne_zero_iff.mpr hd
  rw [potential_off_pole hz (criticalMap_ne_pole hf (ne_of_gt hk) hz hc),
    critical_difference hc, norm_mul, norm_mul, norm_div, Complex.norm_I,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hk, abs_of_pos hz, Real.rpow_sub_one hy, reciprocalDeriv, norm_inv]
  congr 1
  field_simp

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.CriticalPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma second_derivative_nonneg_at_min_zero {f f' : ℝ → ℝ} {b : ℝ}
    (hmin : IsLocalMin f 0) (hf : ∀ᶠ x in 𝓝 0, HasDerivAt f (f' x) x)
    (hf' : HasDerivAt f' b 0) : 0 ≤ b := by
  by_contra hb
  have hb : b < 0 := lt_of_not_ge hb
  have hzero : f' 0 = 0 := hmin.hasDerivAt_eq_zero hf.self_of_nhds
  have hrem := (hasDerivAt_iff_isLittleO_nhds_zero.mp hf').bound
    (by linarith : 0 < -b/2)
  have he : ∀ᶠ x in 𝓝 (0 : ℝ),
      HasDerivAt f (f' x) x ∧ f 0 ≤ f x ∧ |f' x - x*b| ≤ (-b/2)*|x| := by
    filter_upwards [hf,hmin,hrem] with x hdx hmx hrx
    exact ⟨hdx,hmx,by simpa [hzero,Real.norm_eq_abs] using hrx⟩
  obtain ⟨δ,hδ,hall⟩ := Metric.eventually_nhds_iff.mp he
  have hball {x : ℝ} (hx : x ∈ Icc 0 (δ/2)) : dist x 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hx.1]
    linarith [hx.2]
  have hc : ContinuousOn f (Icc 0 (δ/2)) := by
    intro x hx
    exact (hall (hball hx)).1.continuousAt.continuousWithinAt
  obtain ⟨c,hcint,hceq⟩ := exists_deriv_eq_slope f (by linarith : 0 < δ/2) hc
    (fun x hx => (hall (hball (Ioo_subset_Icc_self hx))).1.differentiableAt.differentiableWithinAt)
  have hcl := hall (hball (Ioo_subset_Icc_self hcint))
  rw [hcl.1.deriv] at hceq
  have hend := (hall (hball (show δ/2 ∈ Icc 0 (δ/2) by constructor <;> linarith))).2.1
  have hf'c : 0 ≤ f' c := by
    rw [hceq]
    exact div_nonneg (sub_nonneg.mpr hend) (by linarith)
  have hupper := (le_abs_self (f' c-c*b)).trans hcl.2.2
  rw [abs_of_pos hcint.1] at hupper
  nlinarith [mul_neg_of_pos_of_neg hcint.1 hb]

lemma second_directional_nonneg_at_min {u : ℂ → ℝ} {z v : ℂ}
    (hmin : IsLocalMin u z)
    (hu : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ u w)
    (hv : DifferentiableAt ℝ (fun w => fderiv ℝ u w v) z) :
    0 ≤ fderiv ℝ (fun w => fderiv ℝ u w v) z v := by
  let g : ℝ → ℂ := fun t => z + t • v
  have hg (t : ℝ) : HasDerivAt g v t := by
    simpa [g] using (hasDerivAt_id t).smul_const v |>.const_add z
  have hgz : g 0 = z := by simp [g]
  have hmin' : IsLocalMin (u ∘ g) 0 :=
    (hgz ▸ hmin).comp_continuous (hg 0).continuousAt
  have hu' : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (u ∘ g) (fderiv ℝ u (g t) v) t := by
    have ht : Tendsto g (𝓝 0) (𝓝 z) := hgz ▸ (hg 0).continuousAt
    filter_upwards [ht.eventually hu] with t ht
    exact ht.hasFDerivAt.comp_hasDerivAt t (hg t)
  have hv' : HasDerivAt (fun t => fderiv ℝ u (g t) v)
      (fderiv ℝ (fun w => fderiv ℝ u w v) z v) 0 := by
    exact (hv.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hg 0) hgz.symm)
  exact second_derivative_nonneg_at_min_zero hmin' hu' hv'

lemma differentiableAt_fderiv_logPotential_apply {f : ℂ → ℂ}
    (hf : UnivalentOn f halfPlane) {z ξ : ℂ} (hz : z ∈ halfPlane)
    (hp : f z ≠ ξ) (k : ℝ) (v : ℂ) :
    DifferentiableAt ℝ (fun w => fderiv ℝ (logPotential f k ξ) w v) z := by
  have hd := (hf.1 z hz).differentiableAt (isOpen_halfPlane.mem_nhds hz)
  have hn := hd.continuousAt.eventually_ne hp
  have heq : (fun w => fderiv ℝ (logPotential f k ξ) w v) =ᶠ[𝓝 z]
      (fun w => k / w.im * v.im - (targetRatio f ξ w * v).re) := by
    filter_upwards [isOpen_halfPlane.mem_nhds hz, hn] with w hw hne
    rw [fderiv_logPotential_apply hf hw hne]
    unfold targetRatio
    congr 2
    ring
  have ha : DifferentiableAt ℝ (fun w : ℂ => k / w.im * v.im) z := by
    have hi := (hasDerivAt_inv (ne_of_gt hz)).differentiableAt.comp z
      Complex.imCLM.differentiableAt
    simpa only [div_eq_mul_inv, Function.comp_def, Complex.imCLM_apply] using
      (hi.const_mul k).mul_const v.im
  have hb : DifferentiableAt ℝ (fun w => (targetRatio f ξ w * v).re) z :=
    Complex.reCLM.differentiableAt.comp z
      (((hasDerivAt_targetRatio hf hz hp).differentiableAt.restrictScalars ℝ).mul_const v)
  exact (ha.sub hb).congr_of_eventuallyEq heq

lemma not_isLocalMin_logPotential {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} (hk : 0 < k) {z ξ : ℂ} (hz : z ∈ halfPlane) (hp : f z ≠ ξ) :
    ¬ IsLocalMin (logPotential f k ξ) z := by
  intro hmin
  have hd := (hf.1 z hz).differentiableAt (isOpen_halfPlane.mem_nhds hz)
  have hu : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ (logPotential f k ξ) w := by
    filter_upwards [isOpen_halfPlane.mem_nhds hz, hd.continuousAt.eventually_ne hp]
      with w hw hne
    exact differentiableAt_logPotential hf hw hne k
  have h1 := second_directional_nonneg_at_min hmin hu
    (differentiableAt_fderiv_logPotential_apply hf hz hp k 1)
  have hI := second_directional_nonneg_at_min hmin hu
    (differentiableAt_fderiv_logPotential_apply hf hz hp k Complex.I)
  have ht := trace_realHessian_negative hf hk hz hp
  simp only [realHessian, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at ht
  change secondDirectional _ z 1 1 + secondDirectional _ z Complex.I Complex.I < 0 at ht
  unfold secondDirectional at ht
  linarith

lemma continuousOn_reciprocalPotential {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    (k : ℝ) (ξ : ℂ) : ContinuousOn (reciprocalPotential f k ξ) halfPlane := by
  apply ((hf.1.continuousOn.sub continuousOn_const).norm).div
    (Complex.continuous_im.continuousOn.rpow_const (fun z hz => Or.inl (ne_of_gt hz)))
  intro z hz
  exact ne_of_gt (Real.rpow_pos_of_pos hz k)

lemma reciprocalPotential_pos {f : ℂ → ℂ} {k : ℝ} {ξ z : ℂ}
    (hz : z ∈ halfPlane) (hp : f z ≠ ξ) : 0 < reciprocalPotential f k ξ z := by
  exact div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hp)) (Real.rpow_pos_of_pos hz k)

lemma log_reciprocalPotential {f : ℂ → ℂ} {k : ℝ} {ξ z : ℂ}
    (hz : z ∈ halfPlane) (hp : f z ≠ ξ) :
    Real.log (reciprocalPotential f k ξ z) = -logPotential f k ξ z := by
  rw [reciprocalPotential,Real.log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp))
    (ne_of_gt (Real.rpow_pos_of_pos hz k)),Real.log_rpow hz,logPotential]
  ring

lemma not_isLocalMax_reciprocalPotential {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} (hk : 0 < k) {z ξ : ℂ} (hz : z ∈ halfPlane) (hp : f z ≠ ξ) :
    ¬ IsLocalMax (reciprocalPotential f k ξ) z := by
  intro hmax
  apply not_isLocalMin_logPotential hf hk hz hp
  have hd := (hf.1 z hz).differentiableAt (isOpen_halfPlane.mem_nhds hz)
  filter_upwards [hmax,isOpen_halfPlane.mem_nhds hz,hd.continuousAt.eventually_ne hp]
    with w hw hwH hwne
  have hl := Real.log_le_log (reciprocalPotential_pos hwH hwne) hw
  rw [log_reciprocalPotential hwH hwne,log_reciprocalPotential hz hp] at hl
  linarith

lemma reciprocalPotential_lt_boundary {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k b : ℝ} (hk : 0 < k) (hb : 0 < b) (ξ : ℂ) {U : Set ℂ}
    (ho : IsOpen U) (hcompact : IsCompact (closure U))
    (hH : closure U ⊆ halfPlane)
    (hboundary : ∀ z ∈ frontier U, reciprocalPotential f k ξ z ≤ b)
    {z : ℂ} (hz : z ∈ U) : reciprocalPotential f k ξ z < b := by
  have hcont := (continuousOn_reciprocalPotential hf k ξ).mono hH
  obtain ⟨a,ha,hmax⟩ := hcompact.exists_isMaxOn ⟨z,subset_closure hz⟩ hcont
  have hmaxle : reciprocalPotential f k ξ a ≤ b := by
    by_contra hn
    have hab : b < reciprocalPotential f k ξ a := lt_of_not_ge hn
    have haU : a ∈ U := by
      by_contra hau
      have haf : a ∈ frontier U := ⟨ha,by simpa only [ho.interior_eq] using hau⟩
      exact (not_lt_of_ge (hboundary a haf)) hab
    have hane : f a ≠ ξ := by
      intro he
      have he0 : reciprocalPotential f k ξ a = 0 := by simp [reciprocalPotential,he]
      linarith
    exact not_isLocalMax_reciprocalPotential hf hk (hH ha) hane
      (hmax.isLocalMax (mem_of_superset (ho.mem_nhds haU) subset_closure))
  have hwhole : ∀ w ∈ closure U, reciprocalPotential f k ξ w ≤ b :=
    fun w hw => (hmax hw).trans hmaxle
  have hzle := hwhole z (subset_closure hz)
  apply lt_of_le_of_ne hzle
  intro he
  have hzne : f z ≠ ξ := by
    intro hze
    have he0 : reciprocalPotential f k ξ z = 0 := by simp [reciprocalPotential,hze]
    linarith
  apply not_isLocalMax_reciprocalPotential hf hk (hH (subset_closure hz)) hzne
  filter_upwards [ho.mem_nhds hz] with w hw
  exact (hwhole w (subset_closure hw)).trans_eq he.symm

lemma regularizedGradient_eq_zero_iff {f : ℂ → ℂ} {k : ℝ} (hk : k ≠ 0)
    {ξ z : ℂ} (hz : z ∈ halfPlane) :
    regularizedGradient f k ξ z = 0 ↔ f z = ξ ∨ criticalMap f k z = ξ := by
  have hc : ((k : ℂ)*Complex.I/(z.im : ℂ)) ≠ 0 := div_ne_zero
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr hk) Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hz))
  simp only [regularizedGradient,mul_eq_zero,hc,false_or,sub_eq_zero,map_eq_zero]

lemma differentiableAt_gradientCoefficient {z : ℂ} (hz : z ∈ halfPlane) (k : ℝ) :
    DifferentiableAt ℝ (fun w : ℂ => (k : ℂ)*Complex.I/(w.im : ℂ)) z := by
  have hn : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hi := ((hasDerivAt_inv hn).differentiableAt.restrictScalars ℝ).comp z
    ((Complex.ofRealCLM.comp Complex.imCLM).differentiableAt)
  simpa only [div_eq_mul_inv,Function.comp_def,ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply,Complex.imCLM_apply] using hi.const_mul ((k : ℂ)*Complex.I)

lemma differentiableAt_regularizedGradient {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z : ℂ} (hz : z ∈ halfPlane) (k : ℝ) (ξ : ℂ) :
    DifferentiableAt ℝ (regularizedGradient f k ξ) z := by
  have hd := ((hf.1 z hz).differentiableAt (isOpen_halfPlane.mem_nhds hz)).restrictScalars ℝ
  exact ((differentiableAt_gradientCoefficient hz k).mul (hd.sub_const ξ)).mul
    (Complex.conjCLE.differentiableAt.comp z ((differentiableAt_criticalMap hf hz k).sub_const ξ))

lemma hasFDerivAt_regularizedGradient_at_critical {f : ℂ → ℂ}
    (hf : UnivalentOn f halfPlane) {k : ℝ} {ξ z : ℂ} (hz : z ∈ halfPlane)
    (hc : criticalMap f k z = ξ) :
    HasFDerivAt (regularizedGradient f k ξ)
      ((((k : ℂ)*Complex.I/(z.im : ℂ))*(f z-ξ)) •
        (Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ (criticalMap f k) z))) z := by
  have hd := ((hf.1 z hz).differentiableAt (isOpen_halfPlane.mem_nhds hz)).restrictScalars ℝ
  have hG := (differentiableAt_criticalMap hf hz k).hasFDerivAt.sub_const ξ
  have hh := ((differentiableAt_gradientCoefficient hz k).hasFDerivAt.fun_mul
    (hd.hasFDerivAt.sub_const ξ)).fun_mul (Complex.conjCLE.hasFDerivAt.comp z hG)
  convert hh using 1 <;> first | rfl | simp only [Function.comp_def, hc, sub_self, map_zero, zero_smul, add_zero]

lemma hasFDerivAt_regularizedGradient_at_pole {f : ℂ → ℂ}
    (hf : UnivalentOn f halfPlane) {k : ℝ} {ξ z : ℂ} (hz : z ∈ halfPlane)
    (hp : f z = ξ) :
    HasFDerivAt (regularizedGradient f k ξ)
      ((((k : ℂ)*Complex.I/(z.im : ℂ))*conj (criticalMap f k z-ξ)) •
        (fderiv ℝ f z)) z := by
  have hd := ((hf.1 z hz).differentiableAt (isOpen_halfPlane.mem_nhds hz)).restrictScalars ℝ
  have hG := (differentiableAt_criticalMap hf hz k).hasFDerivAt.sub_const ξ
  have hh := ((differentiableAt_gradientCoefficient hz k).hasFDerivAt.fun_mul
    (hd.hasFDerivAt.sub_const ξ)).fun_mul (Complex.conjCLE.hasFDerivAt.comp z hG)
  convert hh using 1 <;> first | rfl | simp only [Function.comp_def, hp, sub_self, mul_zero, zero_smul, zero_add, add_zero, smul_smul, Complex.conjCLE_apply, mul_comm]

lemma det_conj_comp (A : ℂ →L[ℝ] ℂ) :
    LinearMap.det (Complex.conjCLE.toContinuousLinearMap.comp A).toLinearMap =
      -LinearMap.det A.toLinearMap := by
  rw [determinant_complex_real,determinant_complex_real]
  simp only [ContinuousLinearMap.coe_coe,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,Complex.conjCLE_apply,Complex.conj_re,Complex.conj_im]
  ring

lemma det_regularizedGradient_at_critical {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} {ξ z : ℂ} (hz : z ∈ halfPlane) (hc : criticalMap f k z = ξ) :
    LinearMap.det (fderiv ℝ (regularizedGradient f k ξ) z).toLinearMap =
      -‖((k : ℂ)*Complex.I/(z.im : ℂ))*(f z-ξ)‖^2 * ‖deriv f z‖^2 *
        normalizedJacobian f k z := by
  rw [(hasFDerivAt_regularizedGradient_at_critical hf hz hc).fderiv,
    det_complex_smul,det_conj_comp,normalizedJacobian]
  have hd : ‖deriv f z‖ ≠ 0 := norm_ne_zero_iff.mpr
    (univalent_deriv_ne_zero isOpen_halfPlane hf hz)
  field_simp

lemma det_regularizedGradient_at_pole_pos {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} (hk : k ≠ 0) {ξ z : ℂ} (hz : z ∈ halfPlane) (hp : f z = ξ) :
    0 < LinearMap.det (fderiv ℝ (regularizedGradient f k ξ) z).toLinearMap := by
  have hG : criticalMap f k z ≠ ξ := fun hc => criticalMap_ne_pole hf hk hz hc hp
  rw [(hasFDerivAt_regularizedGradient_at_pole hf hz hp).fderiv,det_complex_smul,
    det_fderiv_complex ((hf.1 z hz).differentiableAt (isOpen_halfPlane.mem_nhds hz))]
  apply mul_pos
  · apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    exact mul_ne_zero (div_ne_zero
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr hk) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr (ne_of_gt hz)))
      ((map_ne_zero (starRingEnd ℂ)).mpr (sub_ne_zero.mpr hG))
  · exact sq_pos_of_pos (norm_pos_iff.mpr (univalent_deriv_ne_zero isOpen_halfPlane hf hz))

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.Winding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma HasLogIncrement.path_trans {a b c : ℂ} {γ : Path a b} {η : Path b c}
    {p q : ℂ} (hγ : HasLogIncrement γ.toContinuousMap p)
    (hη : HasLogIncrement η.toContinuousMap q) :
    HasLogIncrement (γ.trans η).toContinuousMap (p+q) := by
  obtain ⟨A,hA,hp⟩ := hγ
  obtain ⟨B,hB,hq⟩ := hη
  let α : Path (A 0) (A 1) := ⟨A,rfl,rfl⟩
  let β : Path (A 1) (B 1+A 1-B 0) :=
    ⟨⟨fun t => B t+A 1-B 0, by fun_prop⟩, by simp, rfl⟩
  refine ⟨(α.trans β).toContinuousMap, ?_, ?_⟩
  · intro t
    change Complex.exp ((α.trans β) t) = (γ.trans η) t
    rw [Path.trans_apply,Path.trans_apply]
    split_ifs with h
    · exact hA _
    · dsimp only [β,ContinuousMap.coe_mk,Path.coe_mk_mk]
      have heA : Complex.exp (A 1) = b := (hA 1).trans γ.target
      have heB : Complex.exp (B 0) = b := (hB 0).trans η.source
      have hb : b ≠ 0 := heB ▸ Complex.exp_ne_zero (B 0)
      rw [Complex.exp_sub,Complex.exp_add,heA,heB,hB]
      exact mul_div_cancel_right₀ _ hb
  · change (α.trans β) 1-(α.trans β) 0=p+q
    simp only [Path.target,Path.source]
    linear_combination hp+hq

lemma HasLogIncrement.path_symm {a b : ℂ} {γ : Path a b} {q : ℂ}
    (hγ : HasLogIncrement γ.toContinuousMap q) :
    HasLogIncrement γ.symm.toContinuousMap (-q) := by
  obtain ⟨A,hA,hq⟩ := hγ
  refine ⟨⟨fun t => A (unitInterval.symm t), by fun_prop⟩, ?_, ?_⟩
  · exact fun t => hA (unitInterval.symm t)
  · simp only [ContinuousMap.coe_mk,unitInterval.symm_one,unitInterval.symm_zero]
    linear_combination -hq

lemma exists_path_logIncrement {a b : ℂ} (γ : Path a b) (hn : ∀ t, γ t ≠ 0) :
    ∃ q, HasLogIncrement γ.toContinuousMap q := by
  let := (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).contractibleSpace
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0,by simp⟩)
  let := (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).locallyPathConnectedSpace
  obtain ⟨A,hA⟩ := exists_log_lift_of_simplyConnected (0 : unitInterval) γ.toContinuousMap hn
  exact ⟨A 1-A 0,A,hA,rfl⟩

lemma HasLogIncrement.of_slit (γ : C(unitInterval,ℂ))
    (hγ : ∀ t, γ t ∈ Complex.slitPlane) :
    HasLogIncrement γ (Complex.log (γ 1)-Complex.log (γ 0)) := by
  exact ⟨⟨fun t => Complex.log (γ t),γ.continuous.clog hγ⟩,
    fun t => Complex.exp_log (Complex.slitPlane_ne_zero (hγ t)),rfl⟩

lemma HasLogIncrement.of_neg_slit (γ : C(unitInterval,ℂ))
    (hγ : ∀ t, -γ t ∈ Complex.slitPlane) :
    HasLogIncrement γ (Complex.log (-γ 1)-Complex.log (-γ 0)) := by
  refine ⟨⟨fun t => Complex.log (-γ t)+(Real.pi : ℂ)*Complex.I,
    ((γ.continuous.neg).clog hγ).add continuous_const⟩,?_,?_⟩
  · intro t
    simp only [ContinuousMap.coe_mk,Complex.exp_add,Complex.exp_pi_mul_I]
    rw [Complex.exp_log (Complex.slitPlane_ne_zero (hγ t))]
    ring
  · dsimp only [ContinuousMap.coe_mk]
    ring

lemma log_neg_of_im_neg {z : ℂ} (hi : z.im < 0) :
    Complex.log (-z) = Complex.log z+(Real.pi : ℂ)*Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re,norm_neg]
  · simpa [Complex.log_im] using Complex.arg_neg_eq_arg_add_pi_of_im_neg hi

lemma log_neg_of_im_pos {z : ℂ} (hi : 0 < z.im) :
    Complex.log (-z) = Complex.log z-(Real.pi : ℂ)*Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re,norm_neg]
  · simpa [Complex.log_im] using Complex.arg_neg_eq_arg_sub_pi_of_im_pos hi

lemma rectPath_logIncrement {r h : ℝ} (hr : 0 < r) (hh : 0 < h) :
    HasLogIncrement (rectPath r h).toContinuousMap (2*Real.pi*Complex.I) := by
  let a : ℂ := (-r : ℂ)-(h : ℂ)*Complex.I
  let b : ℂ := (r : ℂ)-(h : ℂ)*Complex.I
  let c : ℂ := (r : ℂ)+(h : ℂ)*Complex.I
  let d : ℂ := (-r : ℂ)+(h : ℂ)*Complex.I
  have hab (t : unitInterval) : (Path.segment a b) t ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    simp only [Path.segment_apply,AffineMap.lineMap_apply_module,a,b,Complex.add_im,
      Complex.sub_im,Complex.real_smul,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.neg_im]
    nlinarith
  have hbc (t : unitInterval) : (Path.segment b c) t ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Path.segment_apply,AffineMap.lineMap_apply_module,b,c,Complex.add_re,
      Complex.sub_re,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im]
    nlinarith
  have hcd (t : unitInterval) : (Path.segment c d) t ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    simp only [Path.segment_apply,AffineMap.lineMap_apply_module,c,d,Complex.add_im,
      Complex.real_smul,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.neg_im]
    nlinarith
  have hda (t : unitInterval) : -(Path.segment d a) t ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Path.segment_apply,AffineMap.lineMap_apply_module,d,a,Complex.add_re,
      Complex.sub_re,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.neg_re]
    nlinarith
  have h₁ := HasLogIncrement.of_slit (Path.segment a b).toContinuousMap hab
  have h₂ := HasLogIncrement.of_slit (Path.segment b c).toContinuousMap hbc
  have h₃ := HasLogIncrement.of_slit (Path.segment c d).toContinuousMap hcd
  have h₄ := HasLogIncrement.of_neg_slit (Path.segment d a).toContinuousMap hda
  have he := ((h₁.path_trans h₂).path_trans h₃).path_trans h₄
  have ha : a.im < 0 := by simpa [a] using hh
  have hd : 0 < d.im := by simpa [d] using hh
  have hla := log_neg_of_im_neg ha
  have hld := log_neg_of_im_pos hd
  convert he using 1
  · rfl
  · simp only [Path.coe_toContinuousMap,Path.target,Path.source]
    rw [hla,hld]
    ring

lemma rectPath_winding {r h : ℝ} (hr : 0 < r) (hh : 0 < h) :
    windingNumber (rectPath r h).toContinuousMap = 1 := by
  apply windingNumber_eq_of_logIncrement ((rectPath r h).target.trans (rectPath r h).source.symm)
  simpa only [Int.cast_one,one_mul] using rectPath_logIncrement hr hh

lemma windingNumber_path_symm {a b : ℂ} (γ : Path a b)
    (hc : γ 1 = γ 0) (hn : ∀ t, γ t ≠ 0) :
    windingNumber γ.symm.toContinuousMap = -windingNumber γ.toContinuousMap := by
  apply windingNumber_eq_of_logIncrement (by simpa using hc.symm)
  convert (windingNumber_spec γ.toContinuousMap hc hn).path_symm using 1
  push_cast
  ring

lemma windingNumber_four_paths {a b c d : ℂ}
    (α : Path a b) (β : Path b c) (χ : Path c d) (δ : Path d a)
    (hβc : β 1 = β 0) (hδc : δ 1 = δ 0)
    (hχ : χ.toContinuousMap = α.symm.toContinuousMap)
    (hα : ∀ t, α t ≠ 0) (hβ : ∀ t, β t ≠ 0) (hδ : ∀ t, δ t ≠ 0) :
    windingNumber (((α.trans β).trans χ).trans δ).toContinuousMap =
      windingNumber β.toContinuousMap + windingNumber δ.toContinuousMap := by
  obtain ⟨p,hp⟩ := exists_path_logIncrement α hα
  have hq := windingNumber_spec β.toContinuousMap hβc hβ
  have hr := windingNumber_spec δ.toContinuousMap hδc hδ
  have hs : HasLogIncrement χ.toContinuousMap (-p) := hχ ▸ hp.path_symm
  apply windingNumber_eq_of_logIncrement
    ((((α.trans β).trans χ).trans δ).target.trans
      (((α.trans β).trans χ).trans δ).source.symm)
  convert ((hp.path_trans hq).path_trans hs).path_trans hr using 1
  push_cast
  ring

lemma windingNumber_rect_map (H : ℂ → ℂ) (hH : Continuous H) (r h : ℝ)
    (hp : ∀ x : ℝ, H ((x : ℂ)+(h : ℂ)*Complex.I) =
      H ((x : ℂ)-(h : ℂ)*Complex.I))
    (hn : ∀ z ∈ range (rectPath r h), H z ≠ 0) :
    windingNumber (((rectPath r h).map hH).toContinuousMap) =
      windingNumber (((Path.segment ((r : ℂ)-(h : ℂ)*Complex.I)
        ((r : ℂ)+(h : ℂ)*Complex.I)).map hH).toContinuousMap) -
      windingNumber (((Path.segment ((-r : ℂ)-(h : ℂ)*Complex.I)
        ((-r : ℂ)+(h : ℂ)*Complex.I)).map hH).toContinuousMap) := by
  let a : ℂ := (-r : ℂ)-(h : ℂ)*Complex.I
  let b : ℂ := (r : ℂ)-(h : ℂ)*Complex.I
  let c : ℂ := (r : ℂ)+(h : ℂ)*Complex.I
  let d : ℂ := (-r : ℂ)+(h : ℂ)*Complex.I
  let α := (Path.segment a b).map hH
  let β := (Path.segment b c).map hH
  let χ := (Path.segment c d).map hH
  let δ := (Path.segment d a).map hH
  have hpc : H c = H b := hp r
  have hpa : H d = H a := by simpa only [Complex.ofReal_neg] using hp (-r)
  have hβc : β 1 = β 0 := β.target.trans (hpc.trans β.source.symm)
  have hδc : δ 1 = δ 0 := δ.target.trans (hpa.symm.trans δ.source.symm)
  have hχ : χ.toContinuousMap = α.symm.toContinuousMap := by
    ext t
    simp only [Path.coe_toContinuousMap,χ,α,Path.map_coe,Function.comp_apply,Path.symm_apply,
      Path.segment_apply,AffineMap.lineMap_apply_module]
    have he₁ : (1-(t:ℝ)) • c + (t:ℝ) • d =
        (((1-(t:ℝ))*r+(t:ℝ)*(-r):ℝ):ℂ)+(h:ℂ)*Complex.I := by
      simp [c,d,Complex.real_smul]
      ring
    have he₂ : (1-(unitInterval.symm t:ℝ)) • a+(unitInterval.symm t:ℝ) • b =
        (((1-(t:ℝ))*r+(t:ℝ)*(-r):ℝ):ℂ)-(h:ℂ)*Complex.I := by
      simp [a,b,Complex.real_smul]
      ring
    rw [he₁,he₂]
    exact hp _
  have hsub : range (Path.segment a b) ∪ range (Path.segment b c) ∪
      range (Path.segment c d) ∪ range (Path.segment d a) ⊆ range (rectPath r h) := by
    intro z hz
    change z ∈ range ((((Path.segment a b).trans (Path.segment b c)).trans
      (Path.segment c d)).trans (Path.segment d a))
    simpa only [Path.trans_range] using hz
  have hα : ∀ t, α t ≠ 0 := fun t => hn _ (hsub (Or.inl (Or.inl (Or.inl ⟨t,rfl⟩))))
  have hβ : ∀ t, β t ≠ 0 := fun t => hn _ (hsub (Or.inl (Or.inl (Or.inr ⟨t,rfl⟩))))
  have hδ : ∀ t, δ t ≠ 0 := fun t => hn _ (hsub (Or.inr ⟨t,rfl⟩))
  have hi := windingNumber_four_paths α β χ δ hβc hδc hχ hα hβ hδ
  have hs := windingNumber_path_symm δ hδc hδ
  have he : δ.symm.toContinuousMap = ((Path.segment a d).map hH).toContinuousMap := by
    ext t
    simp [δ,Path.segment_symm]
  rw [he] at hs
  have hg : (((rectPath r h).map hH).toContinuousMap) =
      (((α.trans β).trans χ).trans δ).toContinuousMap := by
    simp only [rectPath,Path.map_trans]
    rfl
  rw [hg,hi]
  change windingNumber β.toContinuousMap + windingNumber δ.toContinuousMap =
    windingNumber β.toContinuousMap - windingNumber ((Path.segment a d).map hH).toContinuousMap
  rw [hs]
  omega

lemma transverse_hasFDerivAt {γ : ℝ → ℂ} {d : ℂ} (hd : HasDerivAt γ d 0) :
    HasFDerivAt (fun w : ℂ => γ w.im-γ 0-w.re • (Complex.I*d))
      ((-Complex.I*d) • ContinuousLinearMap.id ℝ ℂ) 0 := by
  have h := ((hd.hasFDerivAt.comp (0 : ℂ) (Complex.imCLM.hasFDerivAt)).sub_const
    (γ 0)).sub (Complex.reCLM.hasFDerivAt.smul_const (Complex.I*d))
  have he : ContinuousLinearMap.toSpanSingleton ℝ d ∘L Complex.imCLM -
      Complex.reCLM.smulRight (Complex.I*d) =
      (-Complex.I*d) • ContinuousLinearMap.id ℝ ℂ := by
    ext z
    apply Complex.ext <;> simp [Complex.real_smul] <;> ring
  rw [he] at h
  exact h

lemma det_transverse_pos {d : ℂ} (hd : d ≠ 0) :
    0 < LinearMap.det (((-Complex.I*d) • ContinuousLinearMap.id ℝ ℂ).toLinearMap) := by
  rw [det_complex_smul]
  simp only [ContinuousLinearMap.coe_id,LinearMap.det_id,mul_one]
  exact sq_pos_of_pos (norm_pos_iff.mpr (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hd))

lemma periodic_simple_zero {γ : ℝ → ℂ} (hp : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) {t : ℝ} (ht : t ∈ Icc (-(1/2 : ℝ)) (1/2))
    (he : γ t = γ 0) : t = 0 := by
  by_cases hn : 0 ≤ t
  · exact hinj ⟨hn,by linarith [ht.2]⟩ ⟨le_rfl,by norm_num⟩ he
  · have hne : t+1 = 0 := hinj ⟨by linarith [ht.1],by linarith⟩
      ⟨le_rfl,by norm_num⟩ ((hp t).trans he)
    linarith [ht.1]

lemma transverse_unique_zero_strip {γ : ℝ → ℂ} (hc : Continuous γ)
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico (0 : ℝ) 1))
    {d : ℂ} (hd : HasDerivAt γ d 0) (hdn : d ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, |w.re| ≤ δ → |w.im| ≤ 1/2 →
      (γ w.im-γ 0-w.re • (Complex.I*d) = 0 ↔ w = 0) := by
  let H : ℂ → ℂ := fun w => γ w.im-γ 0-w.re • (Complex.I*d)
  have hH0 : H 0 = 0 := by simp [H]
  obtain ⟨_,r,hr,hlocal⟩ := exists_slit_radius_pos hH0 (transverse_hasFDerivAt hd)
    (det_transverse_pos hdn)
  let η := min (r/2) (1/4 : ℝ)
  have hη : 0 < η := lt_min (by linarith) (by norm_num)
  let K : Set ℝ := Icc (-(1/2 : ℝ)) (1/2) ∩ {t | η ≤ |t|}
  have hK : IsCompact K := isCompact_Icc.inter_right
    (isClosed_le continuous_const continuous_abs)
  obtain ⟨m,hm,hbound⟩ := hK.exists_forall_le' ((hc.sub continuous_const).norm.continuousOn)
    (a := (0 : ℝ)) (fun t ht => norm_pos_iff.mpr (sub_ne_zero.mpr (by
      intro he
      have he0 := periodic_simple_zero hp hinj ht.1 he
      have hb : η ≤ |t| := ht.2
      simp only [he0,abs_zero] at hb
      exact (not_le.mpr hη) hb)))
  let δ := min (r/2) (m/(2*‖d‖))
  have hδ : 0 < δ := lt_min (by linarith) (div_pos hm (by positivity))
  refine ⟨δ,hδ,?_⟩
  intro w hre him
  constructor
  · intro hz
    by_contra hwn
    by_cases hi : |w.im| < η
    · have hn : ‖w-0‖ < 2*r := by
        simpa only [sub_zero] using calc
          ‖w‖ ≤ |w.re|+|w.im| := Complex.norm_le_abs_re_add_abs_im w
          _ < r/2+r/2 := by
            have hδr := min_le_left (r/2) (m/(2*‖d‖))
            have hηr := min_le_left (r/2) (1/4 : ℝ)
            dsimp only [δ] at hre
            dsimp only [η] at hi
            linarith
          _ < 2*r := by linarith
      have hnon := Complex.slitPlane_ne_zero (hlocal w hn hwn)
      apply hnon
      simp only [H,hz,zero_div]
    · have hb := hbound w.im ⟨abs_le.mp him,not_lt.mp hi⟩
      change m ≤ ‖γ w.im-γ 0‖ at hb
      have he : γ w.im-γ 0 = w.re • (Complex.I*d) := sub_eq_zero.mp hz
      have hnorm : ‖γ w.im-γ 0‖ = |w.re| *‖d‖ := by
        rw [he,norm_smul,Real.norm_eq_abs,norm_mul,Complex.norm_I,one_mul]
      have hδm : δ*‖d‖ ≤ m/2 := by
        have h := min_le_right (r/2) (m/(2*‖d‖))
        have hn := norm_pos_iff.mpr hdn
        dsimp only [δ]
        apply (le_div_iff₀ hn).mp
        convert h using 1; field_simp
      have : |w.re| *‖d‖ ≤ m/2 := (mul_le_mul_of_nonneg_right hre (norm_nonneg d)).trans hδm
      linarith
  · rintro rfl
    simp

lemma convex_rectRegion (r h : ℝ) : Convex ℝ (rectRegion r h) := by
  have he : rectRegion r h = (Complex.reCLM ⁻¹' Icc (-r) r) ∩
      (Complex.imCLM ⁻¹' Icc (-h) h) := by
    ext z
    simp [rectRegion,abs_le]
  rw [he]
  exact ((convex_Icc (-r) r).linear_preimage Complex.reCLM.toLinearMap).inter
    ((convex_Icc (-h) h).linear_preimage Complex.imCLM.toLinearMap)

lemma rectPath_mem {r h : ℝ} (hr : 0 ≤ r) (hh : 0 ≤ h) (t : unitInterval) :
    rectPath r h t ∈ rectRegion r h := by
  have hs (a b : ℂ) (ha : a ∈ rectRegion r h) (hb : b ∈ rectRegion r h) :
      range (Path.segment a b) ⊆ rectRegion r h := by
    rintro _ ⟨s,rfl⟩
    simpa only [Path.segment_apply,AffineMap.lineMap_apply_module] using
      (convex_rectRegion r h) ha hb (sub_nonneg.mpr s.2.2) s.2.1 (by ring)
  have h₁ : ((-r : ℂ)-(h : ℂ)*Complex.I) ∈ rectRegion r h := by
    simp [rectRegion,abs_of_nonneg hr,abs_of_nonneg hh]
  have h₂ : ((r : ℂ)-(h : ℂ)*Complex.I) ∈ rectRegion r h := by
    simp [rectRegion,abs_of_nonneg hr,abs_of_nonneg hh]
  have h₃ : ((r : ℂ)+(h : ℂ)*Complex.I) ∈ rectRegion r h := by
    simp [rectRegion,abs_of_nonneg hr,abs_of_nonneg hh]
  have h₄ : ((-r : ℂ)+(h : ℂ)*Complex.I) ∈ rectRegion r h := by
    simp [rectRegion,abs_of_nonneg hr,abs_of_nonneg hh]
  have hb : range (rectPath r h) ⊆ rectRegion r h := by
    simp only [rectPath,Path.trans_range]
    exact union_subset (union_subset (union_subset (hs _ _ h₁ h₂) (hs _ _ h₂ h₃))
      (hs _ _ h₃ h₄)) (hs _ _ h₄ h₁)
  exact hb ⟨t,rfl⟩

lemma rectPath_ne_zero {r h : ℝ} (hr : 0 < r) (hh : 0 < h) (t : unitInterval) :
    rectPath r h t ≠ 0 := by
  obtain ⟨T,hT,_⟩ := rectPath_logIncrement hr hh
  exact (hT t ▸ Complex.exp_ne_zero (T t))

lemma winding_jump_centred {γ : ℝ → ℂ} (hc : Continuous γ)
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico (0 : ℝ) 1))
    {d : ℂ} (hd : HasDerivAt γ d 0) (hdn : d ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r ≤ δ →
      loopIndex ⟨fun t : unitInterval => γ ((t : ℝ)-1/2),
          hc.comp (continuous_subtype_val.sub continuous_const)⟩
        (γ 0+r • (Complex.I*d)) -
      loopIndex ⟨fun t : unitInterval => γ ((t : ℝ)-1/2),
          hc.comp (continuous_subtype_val.sub continuous_const)⟩
        (γ 0-r • (Complex.I*d)) = 1 := by
  let H : C(ℂ,ℂ) := ⟨fun w => γ w.im-γ 0-w.re • (Complex.I*d),
    ((hc.comp Complex.continuous_im).sub continuous_const).sub
      (Complex.continuous_re.smul continuous_const)⟩
  let A : ℂ →L[ℝ] ℂ := (-Complex.I*d) • ContinuousLinearMap.id ℝ ℂ
  obtain ⟨δ,hδ,hzero⟩ := transverse_unique_zero_strip hc hp hinj hd hdn
  refine ⟨δ,hδ,?_⟩
  intro r hr hrd
  let p := rectPath r (1/2)
  have hp0 : ∀ t, p t ≠ 0 := rectPath_ne_zero hr (by norm_num)
  have hmem : ∀ t, p t ∈ rectRegion r (1/2) := rectPath_mem hr.le (by norm_num)
  have hz : ∀ z ∈ rectRegion r (1/2), H z = 0 ↔ z ∈ ({0} : Finset ℂ) := by
    intro z hz
    simpa only [Finset.mem_singleton,H,ContinuousMap.coe_mk] using hzero z (hz.1.trans hrd) hz.2
  have hn : ∀ t, H (p t) ≠ 0 := by
    intro t ht
    exact hp0 t (Finset.mem_singleton.mp ((hz _ (hmem t)).mp ht))
  have hi := windingNumber_finite_regular_zeros (convex_rectRegion r (1/2)) {0} H
    (fun _ => A) (by intro z hz; simpa [Finset.mem_singleton,rectRegion] using
      (show |z.re| ≤ r ∧ |z.im| ≤ 1/2 from by simpa [Finset.mem_singleton.mp hz] using
        (show (0 : ℝ) ≤ r ∧ (0 : ℝ) ≤ 1/2 from ⟨hr.le,by norm_num⟩))) hz
    (by intro z hz; have he := Finset.mem_singleton.mp hz; subst z
        exact ⟨transverse_hasFDerivAt hd,ne_of_gt (det_transverse_pos hdn)⟩)
    p.toContinuousMap (p.target.trans p.source.symm) hmem hn
  have hindex : planeIndex A = 1 := by
    simp only [A,planeIndex,ite_eq_left (det_transverse_pos hdn)]
  have hpindex : loopIndex p.toContinuousMap 0 = 1 := by
    change windingNumber (⟨fun t => p t-0,by fun_prop⟩ : C(unitInterval,ℂ)) = 1
    have he : (⟨fun t => p t-0,by fun_prop⟩ : C(unitInterval,ℂ)) = p.toContinuousMap := by
      ext t; simp
    rw [he]
    exact rectPath_winding hr (by norm_num)
  simp only [Finset.sum_singleton,hindex,hpindex,mul_one] at hi
  have hperiod : ∀ x : ℝ, H ((x : ℂ)+((1/2 : ℝ) : ℂ)*Complex.I) =
      H ((x : ℂ)-((1/2 : ℝ) : ℂ)*Complex.I) := by
    intro x
    change γ (((x : ℂ)+((1/2 : ℝ) : ℂ)*Complex.I).im)-γ 0-
        (((x : ℂ)+((1/2 : ℝ) : ℂ)*Complex.I).re) • (Complex.I*d) = _
    have he : γ (1/2) = γ (-(1/2)) := by
      convert hp (-(1/2)) using 1; norm_num
    simpa only [H,ContinuousMap.coe_mk,Complex.add_im,Complex.sub_im,Complex.add_re,
      Complex.sub_re,Complex.mul_im,Complex.mul_re,Complex.ofReal_im,Complex.ofReal_re,
      Complex.I_re,Complex.I_im,zero_mul,mul_zero,mul_one,sub_zero,add_zero,zero_add,
      zero_sub] using congrArg (fun z : ℂ => z-γ 0-x • (Complex.I*d)) he
  have hstrip := windingNumber_rect_map H H.continuous r (1/2) hperiod (by
    rintro _ ⟨t,rfl⟩; exact hn t)
  have hcomp : ((rectPath r (1/2)).map H.continuous).toContinuousMap =
      H.comp p.toContinuousMap := rfl
  rw [hcomp,hi] at hstrip
  have hright : ((Path.segment ((r : ℂ)-((1/2 : ℝ) : ℂ)*Complex.I)
        ((r : ℂ)+((1/2 : ℝ) : ℂ)*Complex.I)).map H.continuous).toContinuousMap =
      (⟨fun t : unitInterval => γ ((t : ℝ)-1/2),
          hc.comp (continuous_subtype_val.sub continuous_const)⟩ : C(unitInterval,ℂ)) -
        ContinuousMap.const _ (γ 0+r • (Complex.I*d)) := by
    ext t
    simp only [Path.coe_toContinuousMap,Path.map_coe,Function.comp_apply,
      Path.segment_apply,AffineMap.lineMap_apply_module,H,ContinuousMap.coe_mk,
      ContinuousMap.sub_apply,ContinuousMap.const_apply]
    have hre : ((1-(t : ℝ)) • ((r : ℂ)-((1/2 : ℝ) : ℂ)*Complex.I)+
        (t : ℝ) • ((r : ℂ)+((1/2 : ℝ) : ℂ)*Complex.I)).re = r := by
      simp [Complex.real_smul]; ring
    have him : ((1-(t : ℝ)) • ((r : ℂ)-((1/2 : ℝ) : ℂ)*Complex.I)+
        (t : ℝ) • ((r : ℂ)+((1/2 : ℝ) : ℂ)*Complex.I)).im = (t : ℝ)-1/2 := by
      simp [Complex.real_smul]; ring
    rw [hre,him]; abel
  have hleft : ((Path.segment ((-r : ℂ)-((1/2 : ℝ) : ℂ)*Complex.I)
        ((-r : ℂ)+((1/2 : ℝ) : ℂ)*Complex.I)).map H.continuous).toContinuousMap =
      (⟨fun t : unitInterval => γ ((t : ℝ)-1/2),
          hc.comp (continuous_subtype_val.sub continuous_const)⟩ : C(unitInterval,ℂ)) -
        ContinuousMap.const _ (γ 0-r • (Complex.I*d)) := by
    ext t
    simp only [Path.coe_toContinuousMap,Path.map_coe,Function.comp_apply,
      Path.segment_apply,AffineMap.lineMap_apply_module,H,ContinuousMap.coe_mk,
      ContinuousMap.sub_apply,ContinuousMap.const_apply]
    have hre : ((1-(t : ℝ)) • ((-r : ℂ)-((1/2 : ℝ) : ℂ)*Complex.I)+
        (t : ℝ) • ((-r : ℂ)+((1/2 : ℝ) : ℂ)*Complex.I)).re = -r := by
      simp [Complex.real_smul]; ring
    have him : ((1-(t : ℝ)) • ((-r : ℂ)-((1/2 : ℝ) : ℂ)*Complex.I)+
        (t : ℝ) • ((-r : ℂ)+((1/2 : ℝ) : ℂ)*Complex.I)).im = (t : ℝ)-1/2 := by
      simp [Complex.real_smul]; ring
    rw [hre,him,neg_smul]; abel
  rw [hright,hleft] at hstrip
  exact hstrip.symm

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.LevelCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma periodicLoop_closed {γ : ℝ → ℂ} (hc : Continuous γ)
    (hp : Function.Periodic γ 1) (s : ℝ) :
    periodicLoop hc s 1 = periodicLoop hc s 0 := by
  simpa only [periodicLoop,ContinuousMap.coe_mk,show ((1 : unitInterval) : ℝ) = 1 from rfl,show ((0 : unitInterval) : ℝ) = 0 from rfl,
    zero_add,add_zero,add_comm] using hp s

lemma periodicLoop_range {γ : ℝ → ℂ} (hc : Continuous γ)
    (hp : Function.Periodic γ 1) (s : ℝ) : range (periodicLoop hc s) = range γ := by
  apply Subset.antisymm
  · rintro _ ⟨t,rfl⟩; exact ⟨(t : ℝ)+s,rfl⟩
  · rintro _ ⟨t,rfl⟩
    obtain ⟨u,hu,he⟩ := hp.exists_mem_Ico (by norm_num) t s
    refine ⟨⟨u-s,⟨by linarith [hu.1],by linarith [hu.2]⟩⟩,?_⟩
    simpa only [periodicLoop,ContinuousMap.coe_mk,sub_add_cancel] using he.symm

lemma loopIndex_periodic_shift {γ : ℝ → ℂ} (hc : Continuous γ)
    (hp : Function.Periodic γ 1) {a : ℂ} (ha : a ∉ range γ) (s : ℝ) :
    loopIndex (periodicLoop hc s) a = loopIndex (periodicLoop hc 0) a := by
  let H : C(unitInterval × unitInterval,ℂ) :=
    ⟨fun p => γ ((p.2 : ℝ)+(p.1 : ℝ)*s)-a,by fun_prop⟩
  have hi := windingNumber_homotopy H (by
    intro p; exact sub_ne_zero.mpr (fun he => ha ⟨_,he⟩)) (by
    intro t
    change γ (1+(t:ℝ)*s)-a = γ (0+(t:ℝ)*s)-a
    simpa only [zero_add,add_zero,add_comm] using congrArg (fun z : ℂ => z-a) (hp ((t:ℝ)*s)))
  simpa only [H,loopIndex,periodicLoop,show ((1 : unitInterval) : ℝ) = 1 from rfl,show ((0 : unitInterval) : ℝ) = 0 from rfl,
    ContinuousMap.coe_mk,one_mul,zero_mul] using hi

lemma transverse_displacement_not_mem {γ : ℝ → ℂ} (hp : Function.Periodic γ 1)
    {d : ℂ} {δ : ℝ}
    (hz : ∀ w : ℂ, |w.re| ≤ δ → |w.im| ≤ 1/2 →
      (γ w.im-γ 0-w.re • (Complex.I*d) = 0 ↔ w = 0))
    {r : ℝ} (hr : r ≠ 0) (hrd : |r| ≤ δ) :
    γ 0+r • (Complex.I*d) ∉ range γ := by
  rintro ⟨t,ht⟩
  obtain ⟨u,hu,he⟩ := hp.exists_mem_Ico (by norm_num) t (-(1/2))
  have hui : |u| ≤ 1/2 := abs_le.mpr ⟨hu.1,by linarith [hu.2]⟩
  let w : ℂ := (r : ℂ)+(u : ℂ)*Complex.I
  have hre : w.re = r := by simp [w]
  have him : w.im = u := by simp [w]
  have hw : w = 0 := (hz w (hre ▸ hrd) (him ▸ hui)).mp (by
    rw [hre,him,← he,ht]; abel)
  have h := congrArg Complex.re hw
  exact hr (by simpa only [hre,Complex.zero_re] using h)

lemma winding_jump {γ : ℝ → ℂ} (hc : Continuous γ)
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico (0 : ℝ) 1))
    {d : ℂ} (hd : HasDerivAt γ d 0) (hdn : d ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r ≤ δ →
      γ 0+r • (Complex.I*d) ∉ range γ ∧ γ 0-r • (Complex.I*d) ∉ range γ ∧
      loopIndex (periodicLoop hc 0) (γ 0+r • (Complex.I*d)) -
      loopIndex (periodicLoop hc 0) (γ 0-r • (Complex.I*d)) = 1 := by
  obtain ⟨δ,hδ,hjump⟩ := winding_jump_centred hc hp hinj hd hdn
  obtain ⟨ε,hε,hzero⟩ := transverse_unique_zero_strip hc hp hinj hd hdn
  refine ⟨min δ ε,lt_min hδ hε,?_⟩
  intro r hr hre
  have hn₁ := transverse_displacement_not_mem hp hzero hr.ne'
    (show |r| ≤ ε from (abs_of_pos hr).symm ▸ hre.trans (min_le_right _ _))
  have hn₂ : γ 0-r • (Complex.I*d) ∉ range γ := by
    simpa only [neg_smul,sub_eq_add_neg] using transverse_displacement_not_mem hp hzero
      (neg_ne_zero.mpr hr.ne') (show |-r| ≤ ε by
        rw [abs_neg,abs_of_pos hr]; exact hre.trans (min_le_right _ _))
  refine ⟨hn₁,hn₂,?_⟩
  have hj := hjump r hr (hre.trans (min_le_left _ _))
  change loopIndex (periodicLoop hc (-(1/2))) (γ 0+r • (Complex.I*d))-
    loopIndex (periodicLoop hc (-(1/2))) (γ 0-r • (Complex.I*d)) = 1 at hj
  rwa [loopIndex_periodic_shift hc hp hn₁,loopIndex_periodic_shift hc hp hn₂] at hj

lemma loopIndex_zero_of_re_lt (γ : C(unitInterval,ℂ)) (hloop : γ 1 = γ 0)
    {a : ℂ} (ha : ∀ t, a.re < (γ t).re) : loopIndex γ a = 0 := by
  apply windingNumber_eq_of_logIncrement (by simp [hloop])
  have h := HasLogIncrement.of_slit (⟨fun t => γ t-a,by fun_prop⟩ : C(unitInterval,ℂ))
    (fun t => Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using sub_pos.mpr (ha t))))
  simpa only [ContinuousMap.coe_mk,hloop,sub_self,Int.cast_zero,zero_mul] using h

lemma winding_leftmost_normal {γ : ℝ → ℂ} (hc : Continuous γ)
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico (0 : ℝ) 1))
    {d : ℂ} (hd : HasDerivAt γ d 0) (hdi : d.im < 0)
    (hmin : ∀ t, (γ 0).re ≤ (γ t).re) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r ≤ δ →
      γ 0+r • (Complex.I*d) ∉ range γ ∧
      loopIndex (periodicLoop hc 0) (γ 0+r • (Complex.I*d)) = 1 := by
  have hdn : d ≠ 0 := by intro he; simp only [he,Complex.zero_im] at hdi; linarith
  obtain ⟨δ,hδ,hj⟩ := winding_jump hc hp hinj hd hdn
  refine ⟨δ,hδ,?_⟩
  intro r hr hrd
  obtain ⟨hn,_,hjump⟩ := hj r hr hrd
  have hzero : loopIndex (periodicLoop hc 0) (γ 0-r • (Complex.I*d)) = 0 :=
    loopIndex_zero_of_re_lt _ (periodicLoop_closed hc hp 0) (by
      intro t
      change (γ 0-r • (Complex.I*d)).re < (γ ((t:ℝ)+0)).re
      simp only [Complex.sub_re,Complex.smul_re,Complex.mul_re,Complex.I_re,zero_mul,
        Complex.I_im,one_mul,zero_sub,smul_eq_mul]
      nlinarith [hmin ((t:ℝ)+0)])
  rw [hzero,sub_zero] at hjump
  exact ⟨hn,hjump⟩

lemma isMIntegralCurve_iff_hasDerivAt {γ : ℝ → ℂ} {v : ℂ → ℂ} :
    IsMIntegralCurve (I := 𝓘(ℝ,ℂ)) γ v ↔ ∀ t, HasDerivAt γ (v (γ t)) t := by
  constructor
  · intro h t
    have ht : HasFDerivAt γ ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t))) t :=
      hasMFDerivAt_iff_hasFDerivAt.mp (h t)
    simpa only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] using ht.hasDerivAt
  · intro h t
    apply hasMFDerivAt_iff_hasFDerivAt.mpr
    convert (h t).hasFDerivAt using 1
    rfl

lemma exists_global_curve {v : ℂ → ℂ} (hv : ContDiff ℝ 1 v)
    (hc : HasCompactSupport v) (x : ℂ) :
    ∃ γ : ℝ → ℂ, γ 0 = x ∧ ∀ t, HasDerivAt γ (v (γ t)) t := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hv (by simp)
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hv.continuous
  let L : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  have hL : ∀ z, ‖v z‖ ≤ (L : ℝ) := fun z => (hB z).trans (le_max_left _ _)
  have hm : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ)).tangent 1
      (fun z => (⟨z,v z⟩ : TangentBundle 𝓘(ℝ,ℂ) ℂ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hv
  have he : ∀ z : ℂ, ∃ γ : ℝ → ℂ, γ 0 = z ∧
      IsMIntegralCurveOn (I := 𝓘(ℝ,ℂ)) γ v (Ioo (-1) 1) := by
    intro z
    have hi : IsPicardLindelof (fun _ : ℝ => v)
        (⟨0, by norm_num⟩ : Icc (-1 : ℝ) 1) z L 0 L K := by
      refine ⟨fun _ _ => hK.lipschitzOnWith, fun _ _ => continuousOn_const,
        fun _ _ w _ => hL w, ?_⟩
      simp
    obtain ⟨γ,hγ0,hγ⟩ := hi.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    refine ⟨γ,hγ0,fun t ht => ?_⟩
    exact ((hγ t ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
  obtain ⟨γ,hγ0,hγ⟩ := exists_isMIntegralCurve_of_isMIntegralCurveOn hm (by norm_num : (0:ℝ)<1) he x
  exact ⟨γ,hγ0,isMIntegralCurve_iff_hasDerivAt.mp hγ⟩

lemma realFunctional_decomposition (p : ℂ →L[ℝ] ℝ) (w : ℂ) :
    p w = w.re * p 1 + w.im * p Complex.I := by
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
    simp [Complex.real_smul, Complex.re_add_im]
  conv_lhs => rw [hw, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]

lemma levelChartDerivative_det (p : ℂ →L[ℝ] ℝ) :
    LinearMap.det (levelChartDerivative p).toLinearMap = (p 1)^2 + (p Complex.I)^2 := by
  rw [determinant_complex_real]
  simp [levelChartDerivative, transverseCoordinate, Complex.mul_re, Complex.mul_im]
  ring

lemma levelChartDerivative_det_pos {p : ℂ →L[ℝ] ℝ} (hp : p ≠ 0) :
    0 < LinearMap.det (levelChartDerivative p).toLinearMap := by
  rw [levelChartDerivative_det]
  have hn : p 1 ≠ 0 ∨ p Complex.I ≠ 0 := by
    by_contra h
    push Not at h
    apply hp
    ext w
    rw [realFunctional_decomposition, h.1, h.2]
    simp
  rcases hn with hn|hn
  · nlinarith [sq_pos_of_ne_zero hn, sq_nonneg (p Complex.I)]
  · nlinarith [sq_pos_of_ne_zero hn, sq_nonneg (p 1)]

lemma exists_regular_level_chart {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 1 f z) (hp : fderiv ℝ f z ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, z ∈ e.source ∧
      (∀ w, (e w).re = f w) ∧
      (∀ w, (e w).im = transverseCoordinate (fderiv ℝ f z) w) := by
  let p := fderiv ℝ f z
  let Φ : ℂ → ℂ := fun w => (f w : ℂ) + Complex.I * (transverseCoordinate p w : ℂ)
  have hc : ContDiffAt ℝ 1 Φ z :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp z hf).add
      (contDiffAt_const.mul ((Complex.ofRealCLM.comp (transverseCoordinate p)).contDiff.contDiffAt))
  have hd : HasFDerivAt Φ (levelChartDerivative p) z := by
    exact (Complex.ofRealCLM.hasFDerivAt.comp z (hf.differentiableAt (by simp)).hasFDerivAt).add
      (((Complex.ofRealCLM.comp (transverseCoordinate p)).hasFDerivAt).const_mul Complex.I)
  let A : ℂ ≃L[ℝ] ℂ := (LinearMap.equivOfIsUnitDet
    (isUnit_iff_ne_zero.mpr (ne_of_gt (levelChartDerivative_det_pos hp)))).toContinuousLinearEquiv
  have hA : (A : ℂ →L[ℝ] ℂ) = levelChartDerivative p := by
    ext w
    exact LinearMap.equivOfIsUnitDet_apply _ w
  rw [← hA] at hd
  refine ⟨hc.toOpenPartialHomeomorph Φ hd (by simp),
    hc.mem_toOpenPartialHomeomorph_source hd (by simp), ?_, ?_⟩
  · intro w
    change (Φ w).re = f w
    simp [Φ]
  · intro w
    change (Φ w).im = transverseCoordinate p w
    simp [Φ]

lemma curve_local_level_cover {f : ℂ → ℝ} {γ : ℝ → ℂ} {t : ℝ} {v : ℂ}
    (hf : ContDiffAt ℝ 1 f (γ t)) (hp : fderiv ℝ f (γ t) ≠ 0)
    (hγ : ContDiffAt ℝ 1 γ t) (hd : HasDerivAt γ v t) (hv : v ≠ 0)
    (hc : ∀ s, f (γ s) = f (γ t)) {U : Set ℝ} (hU : U ∈ 𝓝 t) :
    ∀ᶠ w in 𝓝 (γ t), f w = f (γ t) → w ∈ γ '' U := by
  let p := fderiv ℝ f (γ t)
  let q := transverseCoordinate p
  have hfd := (hf.differentiableAt (by simp)).hasFDerivAt
  have hpv : p v = 0 := by
    have hh := hfd.comp_hasDerivAt t hd
    have he : (f ∘ γ) = fun _ => f (γ t) := funext hc
    rw [he] at hh
    exact hh.unique (hasDerivAt_const t _)
  have hqv : q v ≠ 0 := by
    intro hq
    have hA : IsUnit (LinearMap.det (levelChartDerivative p).toLinearMap) :=
      isUnit_iff_ne_zero.mpr (ne_of_gt (levelChartDerivative_det_pos hp))
    let A := LinearMap.equivOfIsUnitDet hA
    have hz : A v = A 0 := by
      rw [show A v = levelChartDerivative p v from LinearMap.equivOfIsUnitDet_apply _ v,
        show A 0 = levelChartDerivative p 0 from LinearMap.equivOfIsUnitDet_apply _ 0]
      simp [levelChartDerivative, hpv, show transverseCoordinate p v = 0 from hq]
    exact hv (A.injective hz)
  let ψ : ℝ → ℝ := fun s => q (γ s)
  have hψ : HasStrictDerivAt ψ (q v) t :=
    (q.contDiff.contDiffAt.comp t hγ).hasStrictDerivAt'
      (q.hasFDerivAt.comp_hasDerivAt t hd) (by simp)
  let σ := hψ.localInverse ψ (q v) t hqv
  have hσ : σ (ψ t) = t := hψ.eventually_left_inverse hqv |>.self_of_nhds
  have hσc : Tendsto σ (𝓝 (ψ t)) (𝓝 t) := by
    have ht : Tendsto σ (𝓝 (ψ t)) (𝓝 (σ (ψ t))) :=
      (hψ.to_localInverse hqv).hasDerivAt.continuousAt.tendsto
    rwa [hσ] at ht
  obtain ⟨e,het,her,hei⟩ := exists_regular_level_chart hf hp
  have hw : ∀ᶠ w in 𝓝 (γ t), w ∈ e.source := e.open_source.mem_nhds het
  have hqc : Tendsto q (𝓝 (γ t)) (𝓝 (ψ t)) := q.continuous.continuousAt.tendsto
  have hi : ∀ᶠ w in 𝓝 (γ t), ψ (σ (q w)) = q w :=
    hqc.eventually (hψ.eventually_right_inverse hqv)
  have hu : ∀ᶠ w in 𝓝 (γ t), σ (q w) ∈ U := (hσc.comp hqc).eventually hU
  have hs : ∀ᶠ w in 𝓝 (γ t), γ (σ (q w)) ∈ e.source :=
    (hγ.continuousAt.tendsto.comp (hσc.comp hqc)).eventually hw
  filter_upwards [hw,hi,hu,hs] with w hw hi hu hs hfwe
  refine ⟨σ (q w),hu, e.injOn hs hw ?_⟩
  apply Complex.ext
  · rw [her,her,hc,hfwe]
  · rw [hei,hei]
    exact hi

lemma integral_curve_contDiff_one {v : ℂ → ℂ} {γ : ℝ → ℂ}
    (hv : Continuous v) (hγ : ∀ t, HasDerivAt γ (v (γ t)) t) :
    ContDiff ℝ 1 γ := by
  apply contDiff_one_iff_deriv.mpr
  have hc : Continuous γ := continuous_iff_continuousAt.mpr fun t => (hγ t).continuousAt
  refine ⟨fun t => (hγ t).differentiableAt, ?_⟩
  have he : deriv γ = v ∘ γ := funext fun t => (hγ t).deriv
  rw [he]
  exact hv.comp hc

lemma integral_curve_first_integral {f : ℂ → ℝ} {v : ℂ → ℂ} {γ : ℝ → ℂ}
    (hf : Differentiable ℝ f) (horth : ∀ z, fderiv ℝ f z (v z) = 0)
    (hγ : ∀ t, HasDerivAt γ (v (γ t)) t) (s t : ℝ) : f (γ s) = f (γ t) := by
  have hd (t : ℝ) : HasDerivAt (fun t => f (γ t)) 0 t := by
    convert (hf (γ t)).hasFDerivAt.comp_hasDerivAt t (hγ t) using 1 <;>
      first | rfl | simp only [horth]
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) s t

lemma integral_curves_shift_eq {v : ℂ → ℂ} {γ κ : ℝ → ℂ}
    (hv : ContDiff ℝ 1 v)
    (hγ : ∀ t, HasDerivAt γ (v (γ t)) t)
    (hκ : ∀ t, HasDerivAt κ (v (κ t)) t)
    {a b : ℝ} (he : γ a = κ b) (s : ℝ) : γ (s+a) = κ (s+b) := by
  have hm : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ)).tangent 1
      (fun z => (⟨z,v z⟩ : TangentBundle 𝓘(ℝ,ℂ) ℂ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hv
  have hh := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hm
    ((isMIntegralCurve_iff_hasDerivAt.mpr hγ).comp_add a)
    ((isMIntegralCurve_iff_hasDerivAt.mpr hκ).comp_add b) (by simpa using he)
  exact congrFun hh s

lemma curve_isOpenMap_level {f : ℂ → ℝ} {γ : ℝ → ℂ} {c : ℝ}
    (hf : ContDiff ℝ 1 f) (hp : ∀ z, f z = c → fderiv ℝ f z ≠ 0)
    (hγ : ContDiff ℝ 1 γ) (hn : ∀ t, deriv γ t ≠ 0)
    (hc : ∀ t, f (γ t) = c) :
    IsOpenMap (fun t => (⟨γ t,hc t⟩ : {z : ℂ | f z = c})) := by
  intro U hU
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨t,ht,rfl⟩
  have hh := curve_local_level_cover hf.contDiffAt (hp _ (hc t)) hγ.contDiffAt
    (hγ.differentiable (by simp) t).hasDerivAt (hn t)
    (fun s => (hc s).trans (hc t).symm) (hU.mem_nhds ht)
  have hm : Tendsto (Subtype.val : {z : ℂ | f z = c} → ℂ)
      (𝓝 ⟨γ t,hc t⟩) (𝓝 (γ t)) := continuous_subtype_val.continuousAt.tendsto
  have he := hm.eventually hh
  filter_upwards [he] with w hw
  obtain ⟨s,hs,heq⟩ := hw (w.property.trans (hc t).symm)
  exact ⟨s,hs,Subtype.ext heq⟩

lemma compact_regular_level_periodic {f : ℂ → ℝ} {v : ℂ → ℂ} {c : ℝ}
    (hf : ContDiff ℝ 1 f) (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v)
    (horth : ∀ z, fderiv ℝ f z (v z) = 0)
    (hp : ∀ z, f z = c → fderiv ℝ f z ≠ 0)
    (hn : ∀ z, f z = c → v z ≠ 0)
    (hK : IsCompact {z : ℂ | f z = c}) {γ : ℝ → ℂ}
    (hγ : ∀ t, HasDerivAt γ (v (γ t)) t) (hγ0 : f (γ 0) = c) :
    ∃ T > 0, Periodic γ T := by
  let K := {z : ℂ | f z = c}
  have hc (t : ℝ) : f (γ t) = c :=
    (integral_curve_first_integral (hf.differentiable (by simp)) horth hγ t 0).trans hγ0
  let Γ : ℝ → K := fun t => ⟨γ t,hc t⟩
  have hγc := integral_curve_contDiff_one hv.continuous hγ
  have hΓo : IsOpenMap Γ := curve_isOpenMap_level hf hp hγc
    (fun t => by rw [(hγ t).deriv]; exact hn _ (hc t)) hc
  have hΓc : Continuous Γ := hγc.continuous.subtype_mk _
  have hclosed : IsClosed (range Γ) := by
    apply isOpen_compl_iff.mp
    apply isOpen_iff_mem_nhds.mpr
    intro w hw
    obtain ⟨κ,hκ0,hκ⟩ := exists_global_curve hv hvc w.val
    have hκc (s : ℝ) : f (κ s) = c := by
      rw [integral_curve_first_integral (hf.differentiable (by simp)) horth hκ s 0, hκ0]
      exact w.property
    let Δ : ℝ → K := fun s => ⟨κ s,hκc s⟩
    have hΔo : IsOpenMap Δ := curve_isOpenMap_level hf hp
      (integral_curve_contDiff_one hv.continuous hκ)
      (fun s => by rw [(hκ s).deriv]; exact hn _ (hκc s)) hκc
    have hwΔ : w ∈ range Δ := ⟨0,Subtype.ext hκ0⟩
    apply mem_of_superset (hΔo.isOpen_range.mem_nhds hwΔ)
    rintro y ⟨s,rfl⟩ ⟨t,ht⟩
    apply hw
    have he : γ t = κ s := congrArg Subtype.val ht
    refine ⟨-s+t,Subtype.ext ?_⟩
    have hh := integral_curves_shift_eq hv hγ hκ he (-s)
    simpa only [neg_add_cancel,hκ0] using hh
  have hcompact : IsCompact (range Γ) := by
    have : CompactSpace K := isCompact_iff_compactSpace.mp hK
    exact hclosed.isCompact
  have hnotinj : ¬ Injective γ := by
    intro hi
    have hΓi : Injective Γ := fun a b h => hi (congrArg Subtype.val h)
    have he := Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hΓc hΓi hΓo
    apply noncompact_univ ℝ
    apply he.isEmbedding.isCompact_iff.mpr
    simpa only [image_univ] using hcompact
  have hm : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ)).tangent 1
      (fun z => (⟨z,v z⟩ : TangentBundle 𝓘(ℝ,ℂ) ℂ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hv
  exact (xor_iff_iff_not.mp
    ((isMIntegralCurve_iff_hasDerivAt.mpr hγ).periodic_xor_injective hm)).mpr hnotinj

lemma curve_locally_injective {γ : ℝ → ℂ} {t : ℝ}
    (hγ : ContDiffAt ℝ 1 γ t) (hn : deriv γ t ≠ 0) :
    ∃ ε > 0, InjOn γ (Metric.ball t ε) := by
  obtain ⟨p,hp⟩ : ∃ p : ℂ →L[ℝ] ℝ, p (deriv γ t) ≠ 0 := by
    by_cases hr : (deriv γ t).re = 0
    · refine ⟨Complex.imCLM,fun hi => hn (Complex.ext hr hi)⟩
    · exact ⟨Complex.reCLM,hr⟩
  have hd : HasStrictDerivAt (fun s => p (γ s)) (p (deriv γ t)) t :=
    (p.contDiff.contDiffAt.comp t hγ).hasStrictDerivAt'
      (p.hasFDerivAt.comp_hasDerivAt t
        (hγ.differentiableAt (by simp)).hasDerivAt) (by simp)
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp (hd.eventually_left_inverse hp)
  refine ⟨ε,hε,fun a ha b hb he => ?_⟩
  have h₁ := hsub ha
  have h₂ := hsub hb
  change HasStrictDerivAt.localInverse (fun s => p (γ s)) (p (deriv γ t)) t hd hp (p (γ a)) = a at h₁
  change HasStrictDerivAt.localInverse (fun s => p (γ s)) (p (deriv γ t)) t hd hp (p (γ b)) = b at h₂
  rw [he] at h₁
  exact h₁.symm.trans h₂

lemma integral_curve_simple_period {v : ℂ → ℂ} {γ : ℝ → ℂ}
    (hv : ContDiff ℝ 1 v) (hγ : ∀ t, HasDerivAt γ (v (γ t)) t)
    (hn : v (γ 0) ≠ 0) (hper : ∃ T > 0, Periodic γ T) :
    ∃ T > 0, Periodic γ T ∧ InjOn γ (Ico 0 T) := by
  have hγc := integral_curve_contDiff_one hv.continuous hγ
  obtain ⟨ε,hε,hεinj⟩ := curve_locally_injective (t := 0) hγc.contDiffAt
    (by rw [(hγ 0).deriv]; exact hn)
  have hlow : ∀ t, 0 < t → γ t = γ 0 → ε ≤ t := by
    intro t ht he
    by_contra hh
    have hlt : t < ε := lt_of_not_ge hh
    have hmem : t ∈ Metric.ball (0 : ℝ) ε := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos ht] using hlt
    have hz := hεinj hmem (Metric.mem_ball_self hε) he
    linarith
  obtain ⟨T,hT,hpT⟩ := hper
  have hTr : γ T = γ 0 := by simpa using hpT 0
  let S := Icc ε T ∩ {t | γ t = γ 0}
  have hS : IsCompact S := isCompact_Icc.inter_right
    (isClosed_eq hγc.continuous continuous_const)
  obtain ⟨P,hP,hmin⟩ := hS.exists_isMinOn ⟨T,⟨⟨hlow T hT hTr,le_rfl⟩,hTr⟩⟩
    continuousOn_id
  have hPpos : 0 < P := hε.trans_le hP.1.1
  have hleast : ∀ t, 0 < t → γ t = γ 0 → P ≤ t := by
    intro t ht he
    by_cases hle : t ≤ T
    · exact hmin ⟨⟨hlow t ht he,hle⟩,he⟩
    · exact hP.1.2.trans (le_of_not_ge hle)
  have hm : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ)).tangent 1
      (fun z => (⟨z,v z⟩ : TangentBundle 𝓘(ℝ,ℂ) ℂ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hv
  have hi := isMIntegralCurve_iff_hasDerivAt.mpr hγ
  have hPP : Periodic γ P := by simpa using hi.periodic_of_eq hm hP.2
  refine ⟨P,hPpos,hPP,fun a ha b hb he => ?_⟩
  rcases lt_trichotomy a b with hab|hab|hab
  · have hper := hi.periodic_of_eq hm he.symm
    have hret : γ (b-a) = γ 0 := by simpa using hper 0
    have hh := hleast (b-a) (sub_pos.mpr hab) hret
    linarith [ha.1,hb.2]
  · exact hab
  · have hper := hi.periodic_of_eq hm he
    have hret : γ (a-b) = γ 0 := by simpa using hper 0
    have hh := hleast (a-b) (sub_pos.mpr hab) hret
    linarith [hb.1,ha.2]

lemma integral_curves_range_eq {v : ℂ → ℂ} {γ κ : ℝ → ℂ}
    (hv : ContDiff ℝ 1 v)
    (hγ : ∀ t, HasDerivAt γ (v (γ t)) t)
    (hκ : ∀ t, HasDerivAt κ (v (κ t)) t)
    {a b : ℝ} (he : γ a = κ b) : range γ = range κ := by
  apply Subset.antisymm
  · rintro _ ⟨s,rfl⟩
    refine ⟨s-a+b, ?_⟩
    have hh := integral_curves_shift_eq hv hγ hκ he (s-a)
    simpa only [sub_add_cancel] using hh.symm
  · rintro _ ⟨s,rfl⟩
    refine ⟨s-b+a, ?_⟩
    have hh := integral_curves_shift_eq hv hκ hγ he.symm (s-b)
    simpa only [sub_add_cancel] using hh.symm

lemma compact_regular_level_finite_curves {f : ℂ → ℝ} {v : ℂ → ℂ} {c : ℝ}
    (hf : ContDiff ℝ 1 f) (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v)
    (horth : ∀ z, fderiv ℝ f z (v z) = 0)
    (hp : ∀ z, f z = c → fderiv ℝ f z ≠ 0)
    (hn : ∀ z, f z = c → v z ≠ 0)
    (hK : IsCompact {z : ℂ | f z = c}) :
    ∃ C : Finset (Set ℂ), (⋃ S ∈ C, S) = {z : ℂ | f z = c} ∧
      (∀ S ∈ C, ∀ T ∈ C, S ≠ T → Disjoint S T) ∧
      ∀ S ∈ C, ∃ γ : ℝ → ℂ, ∃ P > 0,
        range γ = S ∧ (∀ t, HasDerivAt γ (v (γ t)) t) ∧
        Periodic γ P ∧ InjOn γ (Ico 0 P) := by
  classical
  let K := {z : ℂ | f z = c}
  have hE : ∀ z : K, ∃ γ : ℝ → ℂ, γ 0 = z.val ∧
      ∀ t, HasDerivAt γ (v (γ t)) t := fun z => exists_global_curve hv hvc z.val
  choose γ hγ0 hγ using hE
  have hc (z : K) (t : ℝ) : f (γ z t) = c := by
    rw [integral_curve_first_integral (hf.differentiable (by simp)) horth (hγ z) t 0,
      hγ0 z]
    exact z.property
  let Γ (z : K) : ℝ → K := fun t => ⟨γ z t,hc z t⟩
  have hΓo (z : K) : IsOpenMap (Γ z) := curve_isOpenMap_level hf hp
    (integral_curve_contDiff_one hv.continuous (hγ z))
    (fun t => by rw [(hγ z t).deriv]; exact hn _ (hc z t)) (hc z)
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover (fun z : K => range (Γ z))
    (fun z => (hΓo z).isOpen_range) (by
      intro z _
      exact mem_iUnion.mpr ⟨z,0,Subtype.ext (hγ0 z)⟩)
  let C := s.image (fun z => range (γ z))
  refine ⟨C,?_,?_,?_⟩
  · ext w
    constructor
    · intro hw
      obtain ⟨S,hS,hw⟩ := mem_iUnion₂.mp hw
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hS
      obtain ⟨t,rfl⟩ := hw
      exact hc z t
    · intro hw
      obtain ⟨z,hz,t,ht⟩ := mem_iUnion₂.mp (hs (mem_univ (⟨w,hw⟩ : K)))
      refine mem_iUnion₂.mpr ⟨range (γ z),Finset.mem_image.mpr ⟨z,hz,rfl⟩,t,?_⟩
      exact congrArg Subtype.val ht
  · intro S hS T hT hne
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hT
    apply disjoint_left.mpr
    rintro a ⟨s,hs⟩ ⟨t,ht⟩
    exact hne (integral_curves_range_eq hv (hγ z) (hγ w) (hs.trans ht.symm))
  · intro S hS
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨P,hP,hper,hinj⟩ := integral_curve_simple_period hv (hγ z)
      (hn _ (hc z 0))
      (compact_regular_level_periodic hf hv hvc horth hp hn hK (hγ z) (hc z 0))
    exact ⟨γ z,P,hP,rfl,hγ z,hper,hinj⟩

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.Turning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma convex_secantTriangle : Convex ℝ secantTriangle := by
  intro p hp q hq a b ha hb hab
  change 0 ≤ a*p.1+b*q.1 ∧ a*p.1+b*q.1 ≤ a*p.2+b*q.2 ∧ a*p.2+b*q.2 ≤ 1
  rcases hp with ⟨hp0,hpst,hp1⟩
  rcases hq with ⟨hq0,hqst,hq1⟩
  refine ⟨add_nonneg (mul_nonneg ha hp0) (mul_nonneg hb hq0),
    add_le_add (mul_le_mul_of_nonneg_left hpst ha)
      (mul_le_mul_of_nonneg_left hqst hb), ?_⟩
  calc
    _ ≤ a*1+b*1 := add_le_add (mul_le_mul_of_nonneg_left hp1 ha)
      (mul_le_mul_of_nonneg_left hq1 hb)
    _ = 1 := by simpa using hab

lemma nonempty_secantTriangle : secantTriangle.Nonempty := ⟨(0,0), by simp [secantTriangle]⟩

lemma continuous_averagedDerivative {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) :
    Continuous (fun p : ℝ × ℝ => averagedDerivative γ p.1 p.2) := by
  have hd : Continuous (deriv γ) := hγ.continuous_deriv (by norm_num)
  have hi : Continuous (fun p : ℝ × ℝ => ∫ u in Icc (0 : ℝ) 1, deriv γ (p.1+u*(p.2-p.1))) :=
    continuous_parametric_integral_of_continuous (by fun_prop) isCompact_Icc
  simpa [averagedDerivative, intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc] using hi

lemma sub_smul_averagedDerivative {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (s t : ℝ) :
    (t-s) • averagedDerivative γ s t = γ t-γ s := by
  have hd : Continuous (deriv γ) := hγ.continuous_deriv (by norm_num)
  have hD (u : ℝ) : HasDerivAt (fun v : ℝ => γ (s+v*(t-s)))
      ((t-s) • deriv γ (s+u*(t-s))) u := by
    simpa only [Function.comp_def, Pi.add_apply, id_eq, zero_add, one_mul] using ((hγ.differentiable (by norm_num) (s+u*(t-s))).hasDerivAt.scomp u
      ((hasDerivAt_const u s).add ((hasDerivAt_id u).mul_const (t-s))))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hD u)
    (((hd.comp (show Continuous (fun u : ℝ => s+u*(t-s)) by fun_prop)).const_smul (t-s)).intervalIntegrable 0 1)
  simpa [averagedDerivative, intervalIntegral.integral_smul, sub_eq_add_neg] using hFTC

lemma continuous_extendedSecant {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) :
    Continuous (extendedSecant γ) := by
  have hc := continuous_averagedDerivative hγ
  exact ((continuous_const.sub (continuous_snd.sub continuous_fst)).smul hc).sub
    ((continuous_snd.sub continuous_fst).smul (hc.comp (show Continuous (fun p : ℝ × ℝ => (p.1,p.2-1)) by fun_prop)))

lemma extendedSecant_scale {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hp : Function.Periodic γ 1) (s t : ℝ) :
    ((t-s)*(1-(t-s))) • extendedSecant γ (s,t) =
      ((1-(t-s))^2+(t-s)^2) • (γ t-γ s) := by
  have h₁ := sub_smul_averagedDerivative hγ s t
  have h₂ := sub_smul_averagedDerivative hγ s (t-1)
  rw [hp.sub_eq] at h₂
  change ((t-s)*(1-(t-s))) • ((1-(t-s)) • averagedDerivative γ s t -
    (t-s) • averagedDerivative γ s (t-1)) = _
  calc
    _ = (1-(t-s))^2 • ((t-s) • averagedDerivative γ s t) +
      (t-s)^2 • ((t-1-s) • averagedDerivative γ s (t-1)) := by
        simp only [smul_sub, smul_smul]
        module
    _ = _ := by rw [h₁, h₂, ← add_smul]

lemma extendedSecant_ne_zero {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico 0 1))
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0) {p : ℝ × ℝ}
    (hpt : p ∈ secantTriangle) : extendedSecant γ p ≠ 0 := by
  rcases p with ⟨s,t⟩
  rcases hpt with ⟨hs, hst, ht⟩
  by_cases heq : s = t
  · subst t
    simpa using hd s ⟨hs, ht⟩
  by_cases hc : s = 0 ∧ t = 1
  · rcases hc with ⟨rfl,rfl⟩
    simpa using hd 0 (by simp)
  have hst' : s < t := lt_of_le_of_ne hst heq
  have hneq : γ t ≠ γ s := by
    by_cases ht1 : t = 1
    · subst t
      rw [hp.eq]
      have hs0 : s ≠ 0 := fun h => hc ⟨h,rfl⟩
      exact fun h => hs0 ((hinj ⟨by norm_num, by norm_num⟩ ⟨hs,hst'⟩ h).symm)
    · exact fun h => (ne_of_gt hst') (hinj ⟨hs.trans hst, lt_of_le_of_ne ht ht1⟩
        ⟨hs, hst'.trans_le ht⟩ h)
  have hpos : 0 < (1-(t-s))^2+(t-s)^2 := by nlinarith [sq_nonneg (1-(t-s))]
  intro he
  have hscale := extendedSecant_scale hγ hp s t
  rw [he, smul_zero] at hscale
  exact hneq (sub_eq_zero.mp ((smul_eq_zero.mp hscale.symm).resolve_left hpos.ne'))

lemma periodic_deriv {γ : ℝ → ℂ} (hp : Function.Periodic γ 1) :
    Function.Periodic (deriv γ) 1 := by
  intro t
  rw [← deriv_comp_add_const γ 1 t]
  congr 1
  exact funext hp

lemma extendedSecant_edges {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hp : Function.Periodic γ 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    extendedSecant γ (t,1) = -extendedSecant γ (0,t) := by
  by_cases h0 : t = 0
  · subst t
    simp
  by_cases h1 : t = 1
  · subst t
    simpa using (periodic_deriv hp).eq
  have hd : t*(1-t) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.mpr (Ne.symm h1))
  apply (smul_right_injective ℂ hd)
  have ha := extendedSecant_scale hγ hp 0 t
  have hb := extendedSecant_scale hγ hp t 1
  simp only [sub_zero] at ha
  rw [hp.eq] at hb
  have he : (1-t)*(1-(1-t)) = t*(1-t) := by ring
  have he' : (1-(1-t))^2+(1-t)^2 = (1-t)^2+t^2 := by ring
  rw [he, he'] at hb
  change (t*(1-t)) • extendedSecant γ (t,1) = (t*(1-t)) • (-extendedSecant γ (0,t))
  rw [smul_neg, ha, hb, ← smul_neg]
  congr 1
  module

lemma extendedSecant_left_re_nonneg {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hp : Function.Periodic γ 1) (hm : ∀ t ∈ Icc (0 : ℝ) 1, (γ 0).re ≤ (γ t).re)
    (hd : (deriv γ 0).re = 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ (extendedSecant γ (0,t)).re := by
  by_cases h0 : t = 0
  · subst t
    simp [hd]
  by_cases h1 : t = 1
  · subst t
    simp [hd]
  have hpos : 0 < t*(1-t) := mul_pos (lt_of_le_of_ne ht.1 (Ne.symm h0))
    (sub_pos.mpr (lt_of_le_of_ne ht.2 h1))
  have hs := congrArg Complex.re (extendedSecant_scale hγ hp 0 t)
  simp only [sub_zero, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re] at hs
  have hnonneg : 0 ≤ ((1-t)^2+t^2)*((γ t).re-(γ 0).re) :=
    mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sub_nonneg.mpr (hm t ht))
  nlinarith

lemma exists_secant_log {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico 0 1))
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0) :
    ∃ A : C(secantTriangle, ℂ), A triangleOrigin = Complex.log (deriv γ 0) ∧
      ∀ p, Complex.exp (A p) = extendedSecant γ p := by
  let := convex_secantTriangle.contractibleSpace nonempty_secantTriangle
  let := convex_secantTriangle.locallyPathConnectedSpace
  let S : C(secantTriangle, ℂ) :=
    ⟨fun p => extendedSecant γ p, (continuous_extendedSecant hγ).comp continuous_subtype_val⟩
  have he : Complex.exp (Complex.log (deriv γ 0)) = S triangleOrigin := by
    simpa [S, triangleOrigin] using Complex.exp_log (hd 0 (by simp))
  obtain ⟨A, ⟨hA0,hA⟩, -⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts S he
    (fun p => extendedSecant_ne_zero hγ hp hinj hd p.property)
  exact ⟨A, hA0, fun p => congrFun hA p⟩

lemma continuous_log_unique.{u_1} {X : Type u_1} [TopologicalSpace X] [PreconnectedSpace X]
    {A B : X → ℂ} (hA : Continuous A) (hB : Continuous B)
    (h : ∀ x, Complex.exp (A x) = Complex.exp (B x)) {x : X} (hx : A x = B x) : A = B := by
  exact Complex.isCoveringMap_exp.eq_of_comp_eq hA hB
    (by funext y; exact Subtype.ext (h y)) x hx

lemma continuous_triangleLeft : Continuous triangleLeft := by
  unfold triangleLeft
  fun_prop

lemma continuous_triangleTop : Continuous triangleTop := by
  unfold triangleTop
  fun_prop

lemma continuous_triangleDiag : Continuous triangleDiag := by
  unfold triangleDiag
  fun_prop

lemma mem_slitPlane_of_re_nonneg {z : ℂ} (hz : z ≠ 0) (hr : 0 ≤ z.re) :
    z ∈ Complex.slitPlane := by
  by_cases hi : z.im = 0
  · left
    exact lt_of_le_of_ne hr (fun he => hz (Complex.ext he.symm hi))
  · exact Or.inr hi

lemma log_neg_of_downward {z : ℂ} (hr : z.re = 0) (hi : z.im < 0) :
    Complex.log (-z) = Complex.log z + (Real.pi : ℂ)*Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re, norm_neg]
  · have ha := Complex.arg_eq_neg_pi_div_two_iff.mpr ⟨hr,hi⟩
    have hb : Complex.arg (-z) = Real.pi/2 :=
      Complex.arg_eq_pi_div_two_iff.mpr ⟨by simpa using hr, by simpa using hi⟩
    simp only [Complex.log_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, ha, hb]
    ring

lemma tangent_turning_log {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico 0 1))
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0)
    (hm : ∀ t ∈ Icc (0 : ℝ) 1, (γ 0).re ≤ (γ t).re)
    (hr : (deriv γ 0).re = 0) (hi : (deriv γ 0).im < 0) :
    ∃ T : C(unitInterval, ℂ), (∀ t, Complex.exp (T t) = deriv γ t) ∧
      T 1 = T 0 + (2*Real.pi : ℝ)*Complex.I := by
  obtain ⟨A,hA0,hA⟩ := exists_secant_log hγ hp hinj hd
  have hleftc : Continuous (fun t : unitInterval =>
      Complex.log (extendedSecant γ (triangleLeft t))) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (continuousAt_clog (mem_slitPlane_of_re_nonneg
      (extendedSecant_ne_zero hγ hp hinj hd (triangleLeft t).property)
      (extendedSecant_left_re_nonneg hγ hp hm hr t.property))).comp (f := fun u : unitInterval => extendedSecant γ (triangleLeft u))
      ((continuous_extendedSecant hγ).comp
        (continuous_subtype_val.comp continuous_triangleLeft)).continuousAt
  have hleft : (fun t : unitInterval => A (triangleLeft t)) =
      (fun t : unitInterval => Complex.log (extendedSecant γ (triangleLeft t))) := by
    apply continuous_log_unique (x := (0 : unitInterval)) (A.continuous.comp continuous_triangleLeft) hleftc
    · intro t
      dsimp only [Function.comp_def]
      rw [hA, Complex.exp_log
        (extendedSecant_ne_zero hγ hp hinj hd (triangleLeft t).property)]
    · simpa [Function.comp_def, triangleLeft, triangleOrigin] using hA0
  have hcorner : A triangleCorner = A triangleOrigin + (Real.pi : ℂ)*Complex.I := by
    have hcl := congrFun hleft 1
    have hcl' : A triangleCorner = Complex.log (-deriv γ 0) := by
      simpa [triangleLeft, triangleCorner] using hcl
    rw [hcl', hA0, log_neg_of_downward hr hi]
  have htop : (fun t : unitInterval => A (triangleTop t)) =
      (fun t : unitInterval => A (triangleLeft t) + (Real.pi : ℂ)*Complex.I) := by
    apply continuous_log_unique (x := (0 : unitInterval)) (A.continuous.comp continuous_triangleTop)
      ((A.continuous.comp continuous_triangleLeft).add continuous_const)
    · intro t
      dsimp only [Function.comp_def, Pi.add_apply]
      rw [Complex.exp_add, hA, hA, Complex.exp_pi_mul_I, mul_neg_one]
      exact extendedSecant_edges hγ hp t.property
    · exact hcorner
  refine ⟨⟨fun t => A (triangleDiag t), A.continuous.comp continuous_triangleDiag⟩,
    fun t => ?_, ?_⟩
  · exact (hA (triangleDiag t)).trans (extendedSecant_diag γ t)
  · have hpt := congrFun htop 1
    change A triangleEnd = A triangleCorner + (Real.pi : ℂ)*Complex.I at hpt
    change A triangleEnd = A triangleOrigin + (↑(2*Real.pi) : ℂ)*Complex.I
    rw [hpt, hcorner]
    push_cast
    ring

lemma regular_level_sublevel_nhds {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 1 f z) (hp : fderiv ℝ f z ≠ 0)
    {W : Set ℂ} (hW : W ∈ 𝓝 z) :
    ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ U ⊆ W ∧
      IsPreconnected (U ∩ {w | f w < f z}) ∧
      (U ∩ {w | f w < f z}).Nonempty := by
  obtain ⟨e,hz,her,_⟩ := exists_regular_level_chart hf hp
  have het : e z ∈ e.target := e.map_source hz
  have hn : e.target ∩ e.symm ⁻¹' W ∈ 𝓝 (e z) :=
    inter_mem (e.open_target.mem_nhds het) (by
      have ht := (e.continuousAt_symm het).preimage_mem_nhds
        (show W ∈ 𝓝 (e.symm (e z)) by rwa [e.left_inv hz])
      exact ht)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hn
  let B := Metric.ball (e z) r
  let U := e.source ∩ e ⁻¹' B
  have hBo : IsOpen B := Metric.isOpen_ball
  have hBU : ∀ b ∈ B, b ∈ e.target ∧ e.symm b ∈ U := by
    intro b hb
    have hbt := (hball hb).1
    exact ⟨hbt,e.map_target hbt,by simpa only [mem_preimage,e.right_inv hbt] using hb⟩
  have hUo : IsOpen U := e.isOpen_inter_preimage hBo
  have hzU : z ∈ U := ⟨hz,by simpa [B] using hr⟩
  have hUW : U ⊆ W := by
    intro w hw
    have h := (hball hw.2).2
    simpa only [mem_preimage,e.left_inv hw.1] using h
  have he : U ∩ {w | f w < f z} = e.symm '' (B ∩ {b | b.re < f z}) := by
    ext w
    constructor
    · rintro ⟨hw,hfw⟩
      exact ⟨e w,⟨hw.2,by simpa only [mem_ofPred,her] using hfw⟩,e.left_inv hw.1⟩
    · rintro ⟨b,⟨hb,hbr⟩,rfl⟩
      refine ⟨(hBU b hb).2,?_⟩
      have hh := her (e.symm b)
      rw [e.right_inv (hBU b hb).1] at hh
      change f (e.symm b) < f z
      rw [← hh]
      exact hbr
  have hconv : Convex ℝ (B ∩ {b : ℂ | b.re < f z}) :=
    (convex_ball (e z) r).inter ((convex_Iio (f z)).linear_preimage Complex.reCLM.toLinearMap)
  have hpc : IsPreconnected (U ∩ {w | f w < f z}) := by
    rw [he]
    exact hconv.isPreconnected.image e.symm (e.continuousOn_symm.mono (by
      intro b hb; exact (hBU b hb.1).1))
  refine ⟨U,hUo,hzU,hUW,hpc,?_⟩
  rw [he]
  apply Nonempty.image
  refine ⟨e z - (r/2 : ℝ),?_,?_⟩
  · change dist (e z-(r/2 : ℝ)) (e z) < r
    rw [dist_eq_norm,sub_sub_cancel_left,norm_neg,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (by linarith : (0 : ℝ) < r/2)]
    linarith
  · change (e z - (r/2 : ℝ)).re < f z
    rw [Complex.sub_re,Complex.ofReal_re,her]
    linarith

lemma regular_level_frequently_below {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 1 f z) (hp : fderiv ℝ f z ≠ 0) :
    ∃ᶠ w in 𝓝 z, f w < f z := by
  rw [frequently_iff]
  intro P hP
  obtain ⟨U,_,_,hUP,_,w,hwU,hwf⟩ := regular_level_sublevel_nhds hf hp hP
  exact ⟨w,hUP hwU,hwf⟩

lemma regular_level_local_integer {f : ℂ → ℝ} {j : ℂ → ℤ} {c : ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 1 f z) (hp : fderiv ℝ f z ≠ 0) (hz : f z = c)
    (hj : ContinuousOn j {w | f w ≠ c}) (hj0 : ∀ w, c < f w → j w = 0) :
    ∃ n : ℤ, ∀ᶠ w in 𝓝 z, f w ≠ c → j w = if f w < c then n else 0 := by
  obtain ⟨U,hUo,hzU,_,hpc,w₀,hw₀,hfw₀⟩ := regular_level_sublevel_nhds hf hp
    (show (univ : Set ℂ) ∈ 𝓝 z from univ_mem)
  refine ⟨j w₀,?_⟩
  filter_upwards [hUo.mem_nhds hzU] with w hw hne
  by_cases hlt : f w < c
  · rw [ite_eq_left hlt]
    have hdisc := (hpc.image j (hj.mono (by
      intro v hv
      have hh : f v < f z := hv.2
      exact ne_of_lt (by simpa only [hz] using hh)))).subsingleton
    exact hdisc ⟨w,⟨hw,by change f w < f z; simpa only [hz] using hlt⟩,rfl⟩ ⟨w₀,⟨hw₀,hfw₀⟩,rfl⟩
  · rw [ite_eq_right hlt]
    exact hj0 w (lt_of_le_of_ne (not_lt.mp hlt) hne.symm)

lemma regular_level_local_integer_unique {f : ℂ → ℝ} {j : ℂ → ℤ} {c : ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 1 f z) (hp : fderiv ℝ f z ≠ 0) (hz : f z = c)
    {m n : ℤ}
    (hm : ∀ᶠ w in 𝓝 z, f w ≠ c → j w = if f w < c then m else 0)
    (hn : ∀ᶠ w in 𝓝 z, f w ≠ c → j w = if f w < c then n else 0) : m = n := by
  obtain ⟨w,hw,hmw,hnw⟩ := ((regular_level_frequently_below hf hp).and_eventually
    (hm.and hn)).exists
  have hlt : f w < c := by simpa only [hz] using hw
  have hm' := hmw hlt.ne
  have hn' := hnw hlt.ne
  simpa only [ite_eq_left hlt] using hm'.symm.trans hn'

lemma regular_level_integer_constant_along {f : ℂ → ℝ} {j : ℂ → ℤ}
    {c : ℝ} {γ : ℝ → ℂ} (hc : Continuous γ)
    (hf : ∀ t, ContDiffAt ℝ 1 f (γ t)) (hp : ∀ t, fderiv ℝ f (γ t) ≠ 0)
    (hz : ∀ t, f (γ t) = c) (hj : ContinuousOn j {w | f w ≠ c})
    (hj0 : ∀ w, c < f w → j w = 0) :
    ∃ n : ℤ, ∀ t, ∀ᶠ w in 𝓝 (γ t),
      f w ≠ c → j w = if f w < c then n else 0 := by
  choose n hn using fun t => regular_level_local_integer (hf t) (hp t) (hz t) hj hj0
  have hnc : Continuous n := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have he : ∀ᶠ s in 𝓝 t, n s = n t := by
      filter_upwards [(hc.tendsto t).eventually (hn t).eventually_nhds] with s hs
      exact (regular_level_local_integer_unique (hf s) (hp s) (hz s) hs (hn s)).symm
    exact continuousAt_const.congr (he.mono fun _ h => h.symm)
  refine ⟨n 0,fun t => ?_⟩
  have he : n t = n 0 := TotallyDisconnectedSpace.eq_of_continuous n hnc t 0
  simpa only [he] using hn t

lemma regular_level_loop_local_index {f : ℂ → ℝ} {c : ℝ} {γ : ℝ → ℂ}
    (hc : Continuous γ) (hp : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) {d : ℂ}
    (hd : HasDerivAt γ d 0) (hdi : d.im < 0)
    (hmin : ∀ t, (γ 0).re ≤ (γ t).re)
    (hf : ∀ t, ContDiffAt ℝ 1 f (γ t))
    (hreg : ∀ t, fderiv ℝ f (γ t) ≠ 0) (hz : ∀ t, f (γ t) = c)
    (hbelow : ∀ w, w ∉ range γ → loopIndex (periodicLoop hc 0) w ≠ 0 → f w < c) :
    ∀ t, ∀ᶠ w in 𝓝 (γ t), f w ≠ c →
      loopIndex (periodicLoop hc 0) w = if f w < c then 1 else 0 := by
  have hj : ContinuousOn (loopIndex (periodicLoop hc 0)) {w | f w ≠ c} :=
    (continuousOn_loopIndex _ (periodicLoop_closed hc hp 0)).mono (by
      intro w hw
      rintro ⟨t,rfl⟩
      exact hw (hz ((t:ℝ)+0)))
  have hj0 : ∀ w, c < f w → loopIndex (periodicLoop hc 0) w = 0 := by
    intro w hw
    by_contra hn
    have hwr : w ∉ range γ := by rintro ⟨t,rfl⟩; linarith [hz t]
    exact (hbelow w hwr hn).not_gt hw
  obtain ⟨n,hn⟩ := regular_level_integer_constant_along hc hf hreg hz hj hj0
  obtain ⟨δ,hδ,hjump⟩ := winding_leftmost_normal hc hp hinj hd hdi hmin
  have ht : Tendsto (fun r : ℝ => γ 0+r • (Complex.I*d)) (𝓝 0) (𝓝 (γ 0)) := by
    have h : Continuous (fun r : ℝ => γ 0+r • (Complex.I*d)) := by fun_prop
    simpa only [zero_smul,add_zero] using h.tendsto 0
  obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp (ht.eventually (hn 0))
  let r := min δ ε /2
  have hr : 0 < r := by dsimp [r]; exact half_pos (lt_min hδ hε)
  have hrd : r ≤ δ := by dsimp [r]; linarith [min_le_left δ ε]
  have hre : r < ε := by dsimp [r]; linarith [min_le_right δ ε]
  obtain ⟨hoff,hi⟩ := hjump r hr hrd
  have hlt := hbelow _ hoff (by rw [hi]; norm_num)
  have hh := he (show r ∈ Metric.ball (0 : ℝ) ε by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hr] using hre) hlt.ne
  have hne : n = 1 := by simpa only [ite_eq_left hlt,hi] using hh.symm
  simpa only [hne] using hn

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.LevelIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma sum_loopIndex_sublevel.{u_1} {ι : Type u_1} [Fintype ι] [DecidableEq ι]
    (γ : ι → C(unitInterval,ℂ)) (hclosed : ∀ i, γ i 1 = γ i 0)
    {f : ℂ → ℝ} {c : ℝ} (hf : Continuous f)
    (hcover : ∀ z, f z = c ↔ ∃ i, z ∈ range (γ i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (range (γ i)) (range (γ j)))
    (hlocal : ∀ i z, z ∈ range (γ i) → ∀ᶠ w in 𝓝 z, f w ≠ c →
      loopIndex (γ i) w = if f w < c then 1 else 0)
    (hbelow : ∀ i w, w ∉ range (γ i) → loopIndex (γ i) w ≠ 0 → f w < c)
    (habove : ∃ z, c < f z) :
    ∀ z, f z ≠ c → ∑ i, loopIndex (γ i) z = if f z < c then 1 else 0 := by
  let J : ℂ → ℤ := fun z => if f z = c then 0 else
    ∑ i, loopIndex (γ i) z - if f z < c then 1 else 0
  have hzero (i : ι) (z : ℂ) (hz : c ≤ f z) (hoff : z ∉ range (γ i)) :
      loopIndex (γ i) z = 0 := by
    by_contra hn
    exact (hbelow i z hoff hn).not_ge hz
  have hcont : Continuous J := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : f z = c
    · obtain ⟨i,hiz⟩ := (hcover z).mp hz
      have hj : ∀ᶠ w in 𝓝 z, ∀ j, j ≠ i → loopIndex (γ j) w = 0 := by
        apply Filter.eventually_all.mpr
        intro j
        by_cases hji : j = i
        · exact Filter.Eventually.of_forall (fun _ h => (h hji).elim)
        · have hoff : z ∉ range (γ j) := by
            intro hjz
            exact Set.disjoint_left.mp (hdisjoint i j (Ne.symm hji)) hiz hjz
          have hjz := hzero j z hz.ge hoff
          filter_upwards [loopIndex_eventually_eq (γ j) (hclosed j) hoff] with w hw _
          exact hw.trans hjz
      have he : ∀ᶠ w in 𝓝 z, J w = 0 := by
        filter_upwards [hlocal i z hiz,hj] with w hw hjw
        dsimp only [J]
        by_cases hwe : f w = c
        · rw [ite_eq_left hwe]
        · rw [ite_eq_right hwe]
          have hs : ∑ j, loopIndex (γ j) w = loopIndex (γ i) w := by
            apply Finset.sum_eq_single i
            · intro j _ hji; exact hjw j hji
            · simp
          rw [hs,hw hwe,sub_self]
      exact continuousAt_const.congr (he.mono fun _ h => h.symm)
    · have hgood (i) : z ∉ range (γ i) := fun hi => hz ((hcover z).mpr ⟨i,hi⟩)
      have hj : ∀ᶠ w in 𝓝 z, ∀ i, loopIndex (γ i) w = loopIndex (γ i) z :=
        Filter.eventually_all.mpr fun i => loopIndex_eventually_eq (γ i) (hclosed i) (hgood i)
      have hsign : ∀ᶠ w in 𝓝 z, f w ≠ c ∧ (f w < c ↔ f z < c) := by
        by_cases hlt : f z < c
        · filter_upwards [(isOpen_lt hf continuous_const).mem_nhds hlt] with w hw
          exact ⟨hw.ne,iff_of_true hw hlt⟩
        · have hgt : c < f z := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hz)
          filter_upwards [(isOpen_lt continuous_const hf).mem_nhds hgt] with w hw
          exact ⟨hw.ne',iff_of_false hw.not_gt hlt⟩
      have he : ∀ᶠ w in 𝓝 z, J w = J z := by
        filter_upwards [hj,hsign] with w hjw hw
        simp only [J,ite_eq_right hz,ite_eq_right hw.1]
        rw [Finset.sum_congr rfl (fun i _ => hjw i)]
        simp only [hw.2]
      exact continuousAt_const.congr (he.mono fun _ h => h.symm)
  obtain ⟨a,ha⟩ := habove
  have hJa : J a = 0 := by
    have hs : ∀ i, loopIndex (γ i) a = 0 := fun i =>
      hzero i a ha.le (fun hi => ha.ne ((hcover a).mpr ⟨i,hi⟩).symm)
    simp only [J,ite_eq_right ha.ne',ite_eq_right ha.not_gt,hs,Finset.sum_const_zero,sub_zero]
  intro z hz
  have he := (TotallyDisconnectedSpace.eq_of_continuous J hcont z a).trans hJa
  change (if f z = c then (0 : ℤ) else _) = 0 at he
  rw [ite_eq_right hz,sub_eq_zero] at he
  exact he

lemma windingNumber_normal_field {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico (0 : ℝ) 1))
    (hd : ∀ t, deriv γ t ≠ 0)
    (hm : ∀ t, (γ 0).re ≤ (γ t).re)
    (hr : (deriv γ 0).re = 0) (hi : (deriv γ 0).im < 0)
    (X : C(ℂ,ℂ)) (hX : ∀ t, X (γ t) ≠ 0)
    (horth : ∀ t, (X (γ t)*(conj (deriv γ t))).re = 0) :
    windingNumber (X.comp (periodicLoop hγ.continuous 0)) = 1 := by
  let T : C(unitInterval,ℂ) := ⟨fun t => deriv γ t,
    (hγ.continuous_deriv (by simp)).comp continuous_subtype_val⟩
  let R : C(unitInterval,ℂ) := ⟨fun t => X (γ t)/deriv γ t, by
    apply Continuous.div
    · exact X.continuous.comp (hγ.continuous.comp continuous_subtype_val)
    · exact T.continuous
    · exact fun t => hd t⟩
  have hTloop : T 1 = T 0 := (periodic_deriv hp).eq
  have hRloop : R 1 = R 0 := by
    change X (γ 1)/deriv γ 1 = X (γ 0)/deriv γ 0
    rw [hp.eq,(periodic_deriv hp).eq]
  have hRn (t) : R t ≠ 0 := div_ne_zero (hX t) (hd t)
  have hRslit (t) : R t ∈ Complex.slitPlane := by
    apply Or.inr
    have hre : (R t).re = 0 := by
      change (X (γ t)/deriv γ t).re = 0
      rw [Complex.div_re,← add_div]
      have hh := horth t
      simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,mul_neg,sub_neg_eq_add] at hh
      rw [hh,zero_div]
    intro him
    exact hRn t (Complex.ext hre him)
  have hwindR : windingNumber R = 0 := by
    apply windingNumber_eq_of_logIncrement hRloop
    simpa only [hRloop,sub_self,Int.cast_zero,zero_mul] using HasLogIncrement.of_slit R hRslit
  have hwindT : windingNumber T = 1 := by
    apply windingNumber_eq_of_logIncrement hTloop
    obtain ⟨A,hA,hinc⟩ := tangent_turning_log hγ hp hinj (fun t _ => hd t)
      (fun t _ => hm t) hr hi
    refine ⟨A,hA,?_⟩
    rw [hinc,add_sub_cancel_left]
    simp only [Int.cast_one,one_mul]
    push_cast
    ring
  have he : X.comp (periodicLoop hγ.continuous 0) = T*R := by
    ext t
    change X (γ ((t:ℝ)+0)) = deriv γ t*(X (γ t)/deriv γ t)
    rw [add_zero,mul_div_cancel₀ _ (hd t)]
  rw [he,windingNumber_mul T R hTloop hRloop (fun t => hd t) hRn,hwindT,hwindR,add_zero]

lemma periodic_simple_eq_of_near {γ : ℝ → ℂ} (hp : Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) {a b : ℝ}
    (he : γ a = γ b) (hab : |a-b| < 1) : a = b := by
  have hh (t : ℝ) : γ (Int.fract t) = γ t := by
    simpa only [Int.fract,mul_one] using hp.sub_int_mul_eq (x := t) ⌊t⌋
  have hfr : Int.fract a = Int.fract b := hinj
    ⟨Int.fract_nonneg a,Int.fract_lt_one a⟩ ⟨Int.fract_nonneg b,Int.fract_lt_one b⟩
    ((hh a).trans (he.trans (hh b).symm))
  obtain ⟨n,hn⟩ := Int.fract_eq_fract.mp hfr
  rw [hn] at hab
  have hnlo : (-1 : ℤ) < n := by exact_mod_cast (abs_lt.mp hab).1
  have hnhi : n < (1 : ℤ) := by exact_mod_cast (abs_lt.mp hab).2
  have hn0 : n = 0 := by omega
  rw [hn0,Int.cast_zero] at hn
  exact sub_eq_zero.mp hn

lemma periodic_simple_shift {γ : ℝ → ℂ} (hp : Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) (s : ℝ) :
    InjOn (fun t => γ (t+s)) (Ico (0 : ℝ) 1) := by
  intro a ha b hb he
  have hh : |(a+s)-(b+s)| < 1 := by
    rw [abs_lt]
    constructor <;> linarith [ha.1,ha.2,hb.1,hb.2]
  have heq := periodic_simple_eq_of_near hp hinj he hh
  linarith

lemma periodic_simple_reverse {γ : ℝ → ℂ} (hp : Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) :
    InjOn (fun t => γ (-t)) (Ico (0 : ℝ) 1) := by
  intro a ha b hb he
  have hh : |(-a)-(-b)| < 1 := by
    rw [abs_lt]
    constructor <;> linarith [ha.1,ha.2,hb.1,hb.2]
  have heq := periodic_simple_eq_of_near hp hinj he hh
  linarith

lemma orient_unit_curve {γ : ℝ → ℂ} (hc : ContDiff ℝ 1 γ)
    (hp : Periodic γ 1) (hinj : InjOn γ (Ico (0 : ℝ) 1))
    (hd : ∀ t, deriv γ t ≠ 0) :
    ∃ η : ℝ → ℂ, range η = range γ ∧ ContDiff ℝ 1 η ∧
      Periodic η 1 ∧ InjOn η (Ico (0 : ℝ) 1) ∧ (∀ t, deriv η t ≠ 0) ∧
      (∀ t, (η 0).re ≤ (η t).re) ∧ (deriv η 0).re = 0 ∧ (deriv η 0).im < 0 := by
  have hk : IsCompact (range γ) := by
    rw [← periodicLoop_range hc.continuous hp 0]
    exact isCompact_range (periodicLoop hc.continuous 0).continuous
  obtain ⟨z,⟨s,hs⟩,hmin⟩ := hk.exists_isMinOn ⟨γ 0,⟨0,rfl⟩⟩
    Complex.continuous_re.continuousOn
  subst z
  let η : ℝ → ℂ := fun t => γ (t+s)
  have hηr : range η = range γ := by
    apply Subset.antisymm
    · rintro _ ⟨t,rfl⟩; exact ⟨t+s,rfl⟩
    · rintro _ ⟨t,rfl⟩; exact ⟨t-s,by simp only [η,sub_add_cancel]⟩
  have hηc : ContDiff ℝ 1 η := hc.comp (contDiff_id.add contDiff_const)
  have hηp : Periodic η 1 := hp.add_const s
  have hηinj : InjOn η (Ico (0 : ℝ) 1) := periodic_simple_shift hp hinj s
  have hηd (t) : deriv η t ≠ 0 := by
    dsimp only [η]
    rw [deriv_comp_add_const]
    exact hd (t+s)
  have hηmin (t) : (η 0).re ≤ (η t).re := by
    simpa only [η,zero_add] using
      (show (γ s).re ≤ (γ (t+s)).re from hmin ⟨t+s,rfl⟩)
  have hlocal : IsLocalMin (fun t => (η t).re) 0 :=
    Filter.Eventually.of_forall hηmin
  have hηre : (deriv η 0).re = 0 := hlocal.hasDerivAt_eq_zero
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0
      ((hηc.differentiable (by simp)) 0).hasDerivAt)
  by_cases hi : (deriv η 0).im < 0
  · exact ⟨η,hηr,hηc,hηp,hηinj,hηd,hηmin,hηre,hi⟩
  · have him : 0 < (deriv η 0).im := lt_of_le_of_ne (not_lt.mp hi) (by
      intro he
      exact hηd 0 (Complex.ext hηre he.symm))
    let κ : ℝ → ℂ := fun t => η (-t)
    have hκr : range κ = range η := by
      apply Subset.antisymm
      · rintro _ ⟨t,rfl⟩; exact ⟨-t,rfl⟩
      · rintro _ ⟨t,rfl⟩; exact ⟨-t,by simp [κ]⟩
    refine ⟨κ,hκr.trans hηr,hηc.comp contDiff_id.neg,?_,
      periodic_simple_reverse hηp hηinj,?_,?_,?_,?_⟩
    · intro t
      change η (-(t+1)) = η (-t)
      rw [show -(t+1) = -t-1 by ring,hηp.sub_eq]
    · intro t
      dsimp only [κ]
      rw [deriv_comp_neg]
      exact neg_ne_zero.mpr (hηd (-t))
    · intro t
      simpa only [κ,neg_zero] using hηmin (-t)
    · dsimp only [κ]
      rw [deriv_comp_neg,neg_zero,Complex.neg_re,hηre,neg_zero]
    · dsimp only [κ]
      rw [deriv_comp_neg,neg_zero,Complex.neg_im]
      exact neg_neg_of_pos him

lemma orient_periodic_curve {γ : ℝ → ℂ} {P : ℝ} (hP : 0 < P)
    (hc : ContDiff ℝ 1 γ) (hp : Periodic γ P) (hinj : InjOn γ (Ico (0 : ℝ) P))
    (hd : ∀ t, deriv γ t ≠ 0) :
    ∃ η : ℝ → ℂ, range η = range γ ∧ ContDiff ℝ 1 η ∧
      Periodic η 1 ∧ InjOn η (Ico (0 : ℝ) 1) ∧ (∀ t, deriv η t ≠ 0) ∧
      (∀ t, (η 0).re ≤ (η t).re) ∧ (deriv η 0).re = 0 ∧ (deriv η 0).im < 0 := by
  let κ : ℝ → ℂ := fun t => γ (P*t)
  have hκr : range κ = range γ := by
    apply Subset.antisymm
    · rintro _ ⟨t,rfl⟩; exact ⟨P*t,rfl⟩
    · rintro _ ⟨t,rfl⟩; exact ⟨t/P,by simp [κ,mul_div_cancel₀ _ hP.ne']⟩
  have hκc : ContDiff ℝ 1 κ := hc.comp (contDiff_const.mul contDiff_id)
  have hκp : Periodic κ 1 := by
    intro t
    change γ (P*(t+1)) = γ (P*t)
    rw [mul_add,mul_one,hp]
  have hκinj : InjOn κ (Ico (0 : ℝ) 1) := by
    intro a ha b hb he
    have heq := hinj ⟨mul_nonneg hP.le ha.1,by nlinarith [ha.2]⟩
      ⟨mul_nonneg hP.le hb.1,by nlinarith [hb.2]⟩ he
    exact (mul_left_cancel₀ hP.ne') heq
  have hκd (t) : deriv κ t ≠ 0 := by
    dsimp only [κ]
    rw [deriv_comp_mul_left]
    exact smul_ne_zero hP.ne' (hd (P*t))
  obtain ⟨η,hηr,hh⟩ := orient_unit_curve hκc hκp hκinj hκd
  exact ⟨η,hηr.trans hκr,hh⟩

lemma regular_level_index_sum.{u_1} {ι : Type u_1} [Fintype ι] [DecidableEq ι]
    {f : ℂ → ℝ} {c : ℝ} (hf : Continuous f)
    (γ : ι → ℝ → ℂ) (hc : ∀ i, ContDiff ℝ 1 (γ i))
    (hp : ∀ i, Periodic (γ i) 1) (hi : ∀ i, InjOn (γ i) (Ico (0 : ℝ) 1))
    (hd : ∀ i t, deriv (γ i) t ≠ 0)
    (hm : ∀ i t, (γ i 0).re ≤ (γ i t).re)
    (hr : ∀ i, (deriv (γ i) 0).re = 0) (hdown : ∀ i, (deriv (γ i) 0).im < 0)
    (hlevel : ∀ i t, f (γ i t) = c)
    (hfreg : ∀ z, f z = c → ContDiffAt ℝ 1 f z ∧ fderiv ℝ f z ≠ 0)
    (hcover : ∀ z, f z = c ↔ ∃ i, z ∈ range (γ i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (range (γ i)) (range (γ j)))
    (hbelow : ∀ i w, w ∉ range (γ i) →
      loopIndex (periodicLoop (hc i).continuous 0) w ≠ 0 → f w < c)
    (habove : ∃ z, c < f z)
    {K : Set ℂ} (hK : Convex ℝ K) (hγK : ∀ i t, γ i t ∈ K)
    (s : Finset ℂ) (X : C(ℂ,ℂ)) (A : ℂ → ℂ →L[ℝ] ℂ)
    (hsK : ∀ z ∈ s, z ∈ K) (hzero : ∀ z ∈ K, X z = 0 ↔ z ∈ s)
    (hD : ∀ z ∈ s, HasFDerivAt X (A z) z ∧ LinearMap.det (A z).toLinearMap ≠ 0)
    (hX : ∀ i t, X (γ i t) ≠ 0)
    (horth : ∀ i t, (X (γ i t)*conj (deriv (γ i) t)).re = 0) :
    ∑ a ∈ s, (if f a < c then planeIndex (A a) else 0) = (Fintype.card ι : ℤ) := by
  let Γ (i : ι) := periodicLoop (hc i).continuous 0
  have hΓclosed (i) : Γ i 1 = Γ i 0 := periodicLoop_closed _ (hp i) 0
  have hΓrange (i) : range (Γ i) = range (γ i) := periodicLoop_range _ (hp i) 0
  have hΓlocal (i) (z) (hz : z ∈ range (Γ i)) :
      ∀ᶠ w in 𝓝 z, f w ≠ c → loopIndex (Γ i) w = if f w < c then 1 else 0 := by
    rw [hΓrange i] at hz
    obtain ⟨t,rfl⟩ := hz
    exact regular_level_loop_local_index (hc i).continuous (hp i) (hi i)
      (((hc i).differentiable (by simp)) 0).hasDerivAt (hdown i) (hm i)
      (fun t => (hfreg _ (hlevel i t)).1) (fun t => (hfreg _ (hlevel i t)).2)
      (hlevel i) (hbelow i) t
  have hsum := sum_loopIndex_sublevel Γ hΓclosed hf
    (by intro z; simp only [hΓrange]; exact hcover z)
    (by intro i j hij; rw [hΓrange,hΓrange]; exact hdisjoint i j hij)
    hΓlocal (by intro i w hw; rw [hΓrange] at hw; exact hbelow i w hw) habove
  have hnotlevel (a) (ha : a ∈ s) : f a ≠ c := by
    intro hal
    obtain ⟨i,t,ht⟩ := (hcover a).mp hal
    exact hX i t (ht ▸ (hzero a (hsK a ha)).mpr ha)
  have hindex (i) : (1 : ℤ) = ∑ a ∈ s, planeIndex (A a)*loopIndex (Γ i) a := by
    have h := windingNumber_finite_regular_zeros hK s X A hsK hzero hD (Γ i) (hΓclosed i)
      (fun t => hγK i ((t:ℝ)+0)) (fun t => hX i ((t:ℝ)+0))
    rw [windingNumber_normal_field (hc i) (hp i) (hi i) (hd i) (hm i) (hr i)
      (hdown i) X (hX i) (horth i)] at h
    exact h
  calc
    ∑ a ∈ s, (if f a < c then planeIndex (A a) else 0) =
        ∑ a ∈ s, planeIndex (A a)*(∑ i, loopIndex (Γ i) a) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hsum a (hnotlevel a ha)]
      split_ifs <;> simp
    _ = ∑ i, ∑ a ∈ s, planeIndex (A a)*loopIndex (Γ i) a := by
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ _i : ι, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (hindex i).symm
    _ = (Fintype.card ι : ℤ) := by simp

lemma tangentGradient_orthogonal (f : ℂ → ℝ) (z : ℂ) :
    fderiv ℝ f z (tangentGradient f z) = 0 := by
  rw [realFunctional_decomposition]
  simp only [tangentGradient,Complex.add_re,Complex.add_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.neg_re,Complex.neg_im,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im]
  ring

lemma tangentGradient_ne_zero {f : ℂ → ℝ} {z : ℂ} (h : fderiv ℝ f z ≠ 0) :
    tangentGradient f z ≠ 0 := by
  intro he
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  simp only [tangentGradient,Complex.add_re,Complex.add_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.neg_re,Complex.neg_im,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.zero_re,Complex.zero_im] at hre him
  apply h
  ext w
  rw [realFunctional_decomposition]
  simp only [zero_mul,one_mul,sub_zero,neg_zero,zero_add,add_zero,neg_eq_zero] at hre him
  simp only [him,hre,mul_zero,add_zero,zero_apply]

lemma tangentGradient_contDiff {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (tangentGradient f) := by
  have hd := hf.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)
  exact ((Complex.ofRealCLM.contDiff.comp (hd.clm_apply contDiff_const)).neg).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hd.clm_apply contDiff_const)))

lemma tangentGradient_hasCompactSupport {f : ℂ → ℝ} {d : ℝ}
    (hs : HasCompactSupport (fun z => f z-d)) : HasCompactSupport (tangentGradient f) := by
  have hD := hs.fderiv ℝ
  apply hD.mono'
  intro z hz
  by_contra hn
  have hzer : fderiv ℝ (fun z => f z-d) z = 0 := notMem_support.mp
    (fun h => hn (subset_tsupport _ h))
  have hfzero : fderiv ℝ f z = 0 := by simpa only [fderiv_sub_const] using hzer
  exact hz (by simp only [tangentGradient,hfzero,zero_apply,
    Complex.ofReal_zero,neg_zero,mul_zero,add_zero])

lemma compact_regular_level_oriented_curves {f : ℂ → ℝ} {c d : ℝ}
    (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport (fun z => f z-d))
    (hreg : ∀ z, f z = c → fderiv ℝ f z ≠ 0)
    (hK : IsCompact {z | f z = c}) :
    ∃ C : Finset (Set ℂ), (⋃ S ∈ C, S) = {z | f z = c} ∧
      (∀ S ∈ C, ∀ T ∈ C, S ≠ T → Disjoint S T) ∧
      ∀ S ∈ C, ∃ γ : ℝ → ℂ, range γ = S ∧ ContDiff ℝ 1 γ ∧
        Periodic γ 1 ∧ InjOn γ (Ico (0 : ℝ) 1) ∧ (∀ t, deriv γ t ≠ 0) ∧
        (∀ t, (γ 0).re ≤ (γ t).re) ∧ (deriv γ 0).re = 0 ∧ (deriv γ 0).im < 0 := by
  obtain ⟨C,hC,hdis,hcurves⟩ := compact_regular_level_finite_curves
    (hf.of_le (by norm_num)) (tangentGradient_contDiff hf) (tangentGradient_hasCompactSupport hs)
    (tangentGradient_orthogonal f) hreg (fun z hz => tangentGradient_ne_zero (hreg z hz)) hK
  refine ⟨C,hC,hdis,?_⟩
  intro S hS
  obtain ⟨γ,P,hP,hrange,hD,hper,hinj⟩ := hcurves S hS
  have hlevel (t) : f (γ t) = c := by
    have hm : γ t ∈ ⋃ S ∈ C, S := mem_iUnion₂.mpr ⟨S,hS,hrange ▸ mem_range_self t⟩
    rwa [hC] at hm
  obtain ⟨η,hηrange,hη⟩ := orient_periodic_curve hP
    (integral_curve_contDiff_one (tangentGradient_contDiff hf).continuous hD)
    hper hinj (fun t => by rw [(hD t).deriv]; exact tangentGradient_ne_zero (hreg _ (hlevel t)))
  exact ⟨η,hηrange.trans hrange,hη⟩

lemma loopIndex_zero_of_im_lt (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0)
    {a : ℂ} (ha : ∀ t, a.im < (γ t).im) : loopIndex γ a = 0 := by
  have hslit (t) : γ t-a ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    exact ne_of_gt (sub_pos.mpr (ha t))
  apply windingNumber_eq_of_logIncrement (by simp [hloop])
  refine ⟨⟨fun t => Complex.log (γ t-a), ?_⟩, ?_, ?_⟩
  · exact Continuous.clog (by fun_prop) hslit
  · intro t
    exact Complex.exp_log (Complex.slitPlane_ne_zero (hslit t))
  · simp [hloop]

lemma closure_windingInterior_subset_halfPlane (γ : C(unitInterval, ℂ))
    (hloop : γ 1 = γ 0) (hγ : ∀ t, γ t ∈ halfPlane) :
    closure (windingInterior γ) ⊆ halfPlane := by
  obtain ⟨d,hd,hdist⟩ := isCompact_univ.exists_forall_le'
    (show ContinuousOn (fun t : unitInterval => (γ t).im) univ by fun_prop)
    (a := 0) (fun t _ => hγ t)
  have hsub : windingInterior γ ⊆ {a : ℂ | d ≤ a.im} := by
    intro a ha
    by_contra hn
    exact ha.2 (loopIndex_zero_of_im_lt γ hloop
      (fun t => (lt_of_not_ge hn).trans_le (hdist t (mem_univ t))))
  have hc := closure_minimal hsub (isClosed_le continuous_const Complex.continuous_im)
  intro a ha
  exact hd.trans_le (hc ha)

lemma reciprocalPotential_lt_on_windingInterior {f : ℂ → ℂ}
    (hf : UnivalentOn f halfPlane) {k b : ℝ} (hk : 0 < k) (hb : 0 < b) (ξ : ℂ)
    (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) (hγ : ∀ t, γ t ∈ halfPlane)
    (hlevel : ∀ t, reciprocalPotential f k ξ (γ t) = b)
    {z : ℂ} (hz : z ∈ windingInterior γ) : reciprocalPotential f k ξ z < b := by
  apply reciprocalPotential_lt_boundary hf hk hb ξ (isOpen_windingInterior γ hloop)
    ((isBounded_windingInterior γ hloop).isCompact_closure)
    (closure_windingInterior_subset_halfPlane γ hloop hγ) _ hz
  intro w hw
  obtain ⟨t,rfl⟩ := frontier_windingInterior_subset γ hloop hw
  exact (hlevel t).le

lemma extend_compact_sublevel {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℝ}
    (hf : ∀ z ∈ U, ContDiffAt ℝ 2 f z) {d : ℝ}
    (hK : IsCompact {z | z ∈ U ∧ f z ≤ d}) :
    ∃ F : ℂ → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport (fun z => F z-d) ∧
      (∀ z, z ∈ U → f z ≤ d → F =ᶠ[𝓝 z] f) ∧
      (∀ z ∉ U, F z = d) ∧
      (∀ z c, c < d → (F z ≤ c ↔ z ∈ U ∧ f z ≤ c)) ∧
      (∀ z c, c < d → (F z < c ↔ z ∈ U ∧ f z < c)) := by
  obtain ⟨χ,hχc,hχK,hχU,hχ1,hχrange⟩ := exists_smooth_cutoff hK hU
    (fun _ h => h.1)
  let F := fun z => χ z*(f z-d)+d
  have heq (z) (hz : z ∈ U) (hzd : f z ≤ d) : F =ᶠ[𝓝 z] f := by
    filter_upwards [hχ1 z ⟨hz,hzd⟩] with w hw
    simp only [F,hw,one_mul,sub_add_cancel]
  have hzero (z) (hz : z ∉ tsupport χ) : F =ᶠ[𝓝 z] fun _ => d := by
    filter_upwards [isClosed_tsupport χ |>.isOpen_compl.mem_nhds hz] with w hw
    have hh : χ w = 0 := notMem_support.mp (fun h => hw (subset_tsupport χ h))
    simp only [F,hh,zero_mul,zero_add]
  have hFc : ContDiff ℝ 2 F := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ tsupport χ
    · exact ((hχc.contDiffAt.mul ((hf z (hχU hz)).sub contDiffAt_const)).add
        contDiffAt_const)
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero z hz)
  have hFK : HasCompactSupport (fun z => F z-d) := by
    apply hχK.mono'
    intro z hz
    by_contra hn
    have hh := (hzero z hn).self_of_nhds
    exact hz (sub_eq_zero.mpr hh)
  have hFd (z) (hz : z ∉ U) : F z = d :=
    (hzero z (fun h => hz (hχU h))).self_of_nhds
  have hlarge (z) (hz : z ∈ U) (hdz : d ≤ f z) : d ≤ F z := by
    dsimp only [F]
    exact le_add_of_nonneg_left (mul_nonneg (hχrange z).1 (sub_nonneg.mpr hdz))
  refine ⟨F,hFc,hFK,heq,hFd,?_,?_⟩
  · intro z c hc
    constructor
    · intro hz
      have hzU : z ∈ U := by
        by_contra hn
        rw [hFd z hn] at hz
        exact hc.not_ge hz
      have hzd : f z ≤ d := by
        by_contra hn
        exact hc.not_ge ((hlarge z hzU (not_le.mp hn).le).trans hz)
      exact ⟨hzU,(heq z hzU hzd).self_of_nhds ▸ hz⟩
    · rintro ⟨hzU,hz⟩
      rwa [(heq z hzU (hz.trans hc.le)).self_of_nhds]
  · intro z c hc
    constructor
    · intro hz
      have hzU : z ∈ U := by
        by_contra hn
        rw [hFd z hn] at hz
        exact hc.not_gt hz
      have hzd : f z ≤ d := by
        by_contra hn
        exact hc.not_gt ((hlarge z hzU (not_le.mp hn).le).trans_lt hz)
      exact ⟨hzU,(heq z hzU hzd).self_of_nhds ▸ hz⟩
    · rintro ⟨hzU,hz⟩
      rwa [(heq z hzU (hz.le.trans hc.le)).self_of_nhds]

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.CriticalCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma squaredReciprocalPotential_eq_sq {f : ℂ → ℂ} {k : ℝ} {ξ z : ℂ}
    (hz : z ∈ halfPlane) :
    squaredReciprocalPotential f k ξ z = (reciprocalPotential f k ξ z)^2 := by
  rw [squaredReciprocalPotential,reciprocalPotential,div_pow]
  have he : z.im^(-2*k) = ((z.im^k)^2)⁻¹ := by
    rw [show -2*k = -(k*2) by ring, Real.rpow_neg hz.le, Real.rpow_mul hz.le,
      Real.rpow_two]
  rw [he,div_eq_mul_inv]

lemma contDiffAt_squaredReciprocalPotential {f : ℂ → ℂ}
    (hf : UnivalentOn f halfPlane) {z : ℂ} (hz : z ∈ halfPlane) (k : ℝ) (ξ : ℂ) :
    ContDiffAt ℝ 2 (squaredReciprocalPotential f k ξ) z := by
  have hc : ContDiffAt ℝ 2 f z :=
    (hf.1.analyticOnNhd isOpen_halfPlane z hz).contDiffAt.restrict_scalars ℝ
  exact ((hc.sub contDiffAt_const).norm_sq ℂ).mul
    (Complex.imCLM.contDiff.contDiffAt.rpow_const_of_ne (ne_of_gt hz))

lemma potential_ge_iff_reciprocalPotential_le {f : ℂ → ℂ} {k h : ℝ}
    (hk : 0 ≤ k) (hh : 0 < h) {ξ z : ℂ} (hz : z ∈ halfPlane) :
    ENNReal.ofReal h ≤ potential f k ξ z ↔ reciprocalPotential f k ξ z ≤ h⁻¹ := by
  have hy := Real.rpow_pos_of_pos hz k
  rw [potential,ENNReal.ofReal_rpow_of_nonneg hz.le hk,
    ENNReal.le_div_iff_mul_le
      (Or.inr (ne_of_gt (ENNReal.ofReal_pos.mpr hy))) (Or.inl ENNReal.ofReal_ne_top),
    ← ENNReal.ofReal_mul hh.le,ENNReal.ofReal_le_ofReal_iff hy.le,reciprocalPotential,
    div_le_iff₀ hy,inv_mul_eq_div,le_div_iff₀ hh]
  exact mul_comm h ‖f z-ξ‖ ▸ Iff.rfl

lemma compact_squaredReciprocal_sublevel {f : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    {ξ : ℂ} (hg : GoodPair f k ξ) {d : ℝ} (hd : 0 < d) :
    IsCompact {z | z ∈ halfPlane ∧ squaredReciprocalPotential f k ξ z ≤ d} := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have he : {z | z ∈ halfPlane ∧ squaredReciprocalPotential f k ξ z ≤ d} =
      {z | z ∈ halfPlane ∧ ENNReal.ofReal ((Real.sqrt d)⁻¹) ≤ potential f k ξ z} := by
    ext z
    constructor
    · rintro ⟨hz,hzval⟩
      refine ⟨hz,(potential_ge_iff_reciprocalPotential_le hk (inv_pos.mpr hs) hz).mpr ?_⟩
      rw [inv_inv]
      rw [squaredReciprocalPotential_eq_sq hz] at hzval
      nlinarith [Real.sq_sqrt hd.le]
    · rintro ⟨hz,hzval⟩
      have hv := (potential_ge_iff_reciprocalPotential_le hk (inv_pos.mpr hs) hz).mp hzval
      rw [inv_inv] at hv
      refine ⟨hz,?_⟩
      rw [squaredReciprocalPotential_eq_sq hz]
      have hn : 0 ≤ reciprocalPotential f k ξ z := div_nonneg (norm_nonneg _) (Real.rpow_nonneg hz.le _)
      nlinarith [Real.sq_sqrt hd.le]
  rw [he]
  exact hg.1 _ (inv_pos.mpr hs)

lemma regularizedGradient_formula {f : ℂ → ℂ} {k : ℝ} (hk : k ≠ 0)
    {ξ z : ℂ} (hz : z ∈ halfPlane) :
    regularizedGradient f k ξ z =
      ((k : ℂ)*Complex.I/(z.im : ℂ))*((‖f z-ξ‖^2 : ℝ) : ℂ) -
        (f z-ξ)*conj (deriv f z) := by
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hkc : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  have he : conj (criticalMap f k z-ξ) = conj (f z-ξ) +
      Complex.I/(k : ℂ)*(z.im : ℂ)*conj (deriv f z) := by
    simp only [criticalMap, div_eq_mul_inv, map_sub, map_mul, map_inv₀, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [regularizedGradient,he,mul_add, mul_assoc _ (f z-ξ),Complex.mul_conj',
    ← Complex.ofReal_pow]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

lemma fderiv_squaredReciprocalPotential_apply {f : ℂ → ℂ}
    (hf : UnivalentOn f halfPlane) {k : ℝ} (hk : k ≠ 0)
    {ξ z : ℂ} (hz : z ∈ halfPlane) (v : ℂ) :
    fderiv ℝ (squaredReciprocalPotential f k ξ) z v =
      -2*z.im^(-2*k)*(regularizedGradient f k ξ z * conj v).re := by
  have hd := (((hf.1 z hz).differentiableAt (isOpen_halfPlane.mem_nhds hz)).hasDerivAt.sub_const ξ).hasFDerivAt.restrictScalars ℝ
  have hy := Complex.imCLM.hasFDerivAt.rpow_const (p := -2*k) (Or.inl (ne_of_gt hz))
  have hu := hd.norm_sq.fun_mul hy
  simp only [Complex.imCLM_apply] at hu
  change (fderiv ℝ (fun w => ‖f w - ξ‖ ^ 2 * w.im ^ (-2*k)) z) v = _
  rw [hu.fderiv]
  simp only [smul_apply,add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars',ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul,innerSL_apply_apply,Complex.imCLM_apply]
  rw [regularizedGradient_formula hk hz,Real.rpow_sub hz,Real.rpow_one]
  simp only [Complex.inner,Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
    Complex.sub_re,Complex.sub_im,Complex.div_re,Complex.div_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.normSq_ofReal]
  field_simp [ne_of_gt (show 0 < z.im from hz)]
  ring

lemma fderiv_squaredReciprocalPotential_eq_zero_iff {f : ℂ → ℂ}
    (hf : UnivalentOn f halfPlane) {k : ℝ} (hk : k ≠ 0)
    {ξ z : ℂ} (hz : z ∈ halfPlane) :
    fderiv ℝ (squaredReciprocalPotential f k ξ) z = 0 ↔
      regularizedGradient f k ξ z = 0 := by
  constructor
  · intro hzero
    have hh := fderiv_squaredReciprocalPotential_apply hf hk (ξ := ξ) hz
      (regularizedGradient f k ξ z)
    rw [hzero, zero_apply, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re] at hh
    have hp := Real.rpow_pos_of_pos hz (-2*k)
    have hn := norm_nonneg (regularizedGradient f k ξ z)
    apply norm_eq_zero.mp
    have hsq : ‖regularizedGradient f k ξ z‖^2 = 0 :=
      (mul_eq_zero.mp hh.symm).resolve_left (mul_ne_zero (by norm_num) (ne_of_gt hp))
    nlinarith
  · intro hzero
    ext v
    rw [fderiv_squaredReciprocalPotential_apply hf hk hz v, hzero]
    simp

lemma det_regularizedGradient_ne_zero {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} (hk : k ≠ 0) {ξ : ℂ} (hg : GoodPair f k ξ)
    {z : ℂ} (hz : z ∈ halfPlane) (hzero : regularizedGradient f k ξ z = 0) :
    LinearMap.det (fderiv ℝ (regularizedGradient f k ξ) z).toLinearMap ≠ 0 := by
  rcases (regularizedGradient_eq_zero_iff hk hz).mp hzero with hp | hc
  · exact ne_of_gt (det_regularizedGradient_at_pole_pos hf hk hz hp)
  · rw [det_regularizedGradient_at_critical hf hz hc]
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact neg_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr
          (mul_ne_zero (div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hk)
            Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr (ne_of_gt hz)))
            (sub_ne_zero.mpr (criticalMap_ne_pole hf hk hz hc)))))
      · exact pow_ne_zero 2 (norm_ne_zero_iff.mpr
          (univalent_deriv_ne_zero isOpen_halfPlane hf hz))
    · exact hg.2 z hz hc

lemma compact_convex_halfPlane_envelope {P : Set ℂ} (hP : IsCompact P)
    (hPH : P ⊆ halfPlane) :
    ∃ K : Set ℂ, IsCompact K ∧ Convex ℝ K ∧ P ⊆ K ∧ K ⊆ halfPlane := by
  obtain ⟨η,hη,hheight⟩ := hP.exists_forall_le' Complex.continuous_im.continuousOn hPH
  obtain ⟨R,hR⟩ := hP.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨Metric.closedBall 0 R ∩ {z : ℂ | η ≤ z.im},
    (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const Complex.continuous_im),
    (convex_closedBall (0 : ℂ) R).inter (convex_halfSpace_im_ge η),?_,?_⟩
  · exact fun z hz => ⟨hR hz,hheight z hz⟩
  · exact fun z hz => hη.trans_le hz.2

lemma continuous_extension_near_compact {K U : Set ℂ} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {x : ℂ → ℂ}
    (hx : ∀ z ∈ U, ContinuousAt x z) :
    ∃ X : C(ℂ,ℂ), ∀ z ∈ K, (X : ℂ → ℂ) =ᶠ[𝓝 z] x := by
  obtain ⟨χ,hχc,_hχK,hχU,hχ1,_hχrange⟩ := exists_smooth_cutoff hK hU hKU
  let X := fun z => (χ z : ℂ)*x z
  have hX : Continuous X := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z ∈ tsupport χ
    · exact (Complex.continuous_ofReal.continuousAt.comp hχc.continuous.continuousAt).mul
        (hx z (hχU hz))
    · have he : X =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [isClosed_tsupport χ |>.isOpen_compl.mem_nhds hz] with w hw
        have hzero : χ w = 0 := notMem_support.mp (fun h => hw (subset_tsupport χ h))
        simp only [X,hzero,Complex.ofReal_zero,zero_mul]
      exact continuousAt_const.congr he.symm
  refine ⟨⟨X,hX⟩,?_⟩
  intro z hz
  filter_upwards [hχ1 z hz] with w hw
  simp only [ContinuousMap.coe_mk,X,hw,Complex.ofReal_one,one_mul]

lemma squaredReciprocalPotential_lt_windingInterior {f : ℂ → ℂ}
    (hf : UnivalentOn f halfPlane) {k c : ℝ} (hk : 0 < k) (hc : 0 < c) (ξ : ℂ)
    (γ : C(unitInterval,ℂ)) (hloop : γ 1 = γ 0) (hγ : ∀ t, γ t ∈ halfPlane)
    (hlevel : ∀ t, squaredReciprocalPotential f k ξ (γ t) = c)
    {z : ℂ} (hz : z ∈ windingInterior γ) :
    z ∈ halfPlane ∧ squaredReciprocalPotential f k ξ z < c := by
  have hzH := closure_windingInterior_subset_halfPlane γ hloop hγ (subset_closure hz)
  have hb : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hl (t) : reciprocalPotential f k ξ (γ t) = Real.sqrt c := by
    have hsq := hlevel t
    rw [squaredReciprocalPotential_eq_sq (hγ t)] at hsq
    have hn : 0 ≤ reciprocalPotential f k ξ (γ t) :=
      div_nonneg (norm_nonneg _) (Real.rpow_nonneg (hγ t).le _)
    nlinarith [Real.sq_sqrt hc.le]
  have hh := reciprocalPotential_lt_on_windingInterior hf hk hb ξ γ hloop hγ hl hz
  have hn : 0 ≤ reciprocalPotential f k ξ z :=
    div_nonneg (norm_nonneg _) (Real.rpow_nonneg hzH.le _)
  refine ⟨hzH,?_⟩
  rw [squaredReciprocalPotential_eq_sq hzH]
  nlinarith [Real.sq_sqrt hc.le]

lemma regular_potential_level_index_sum {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} (hk : 0 < k) {ξ : ℂ} (hg : GoodPair f k ξ) {c : ℝ} (hc : 0 < c)
    (hreg : ∀ z ∈ halfPlane, squaredReciprocalPotential f k ξ z = c →
      regularizedGradient f k ξ z ≠ 0) :
    ∃ (s : Finset ℂ) (N : ℕ),
      (∀ z ∈ s, z ∈ halfPlane ∧ regularizedGradient f k ξ z = 0) ∧
      (∀ z ∈ halfPlane, squaredReciprocalPotential f k ξ z < c →
        (z ∈ s ↔ regularizedGradient f k ξ z = 0)) ∧
      (∑ z ∈ s, if squaredReciprocalPotential f k ξ z < c then
        planeIndex (fderiv ℝ (regularizedGradient f k ξ) z) else 0) = (N : ℤ) ∧
      ((∃ z ∈ halfPlane, f z = ξ) → 1 ≤ N) := by
  classical
  let u := squaredReciprocalPotential f k ξ
  let x := regularizedGradient f k ξ
  let d := c+1
  have hcd : c < d := by dsimp [d]; linarith
  have hd : 0 < d := hc.trans hcd
  have hP := compact_squaredReciprocal_sublevel hk.le hg hd
  obtain ⟨K,hK,hKcv,hPK,hKH⟩ := compact_convex_halfPlane_envelope hP (fun _ h => h.1)
  obtain ⟨F,hFc,hFs,hFeq,hFout,hFle,hFlt⟩ := extend_compact_sublevel isOpen_halfPlane
    (fun z hz => contDiffAt_squaredReciprocalPotential hf hz k ξ) hP
  have hlevel (z) (hz : F z = c) : z ∈ halfPlane ∧ u z = c := by
    have hh := (hFle z c hcd).mp hz.le
    exact ⟨hh.1, ((hFeq z hh.1 (hh.2.trans hcd.le)).self_of_nhds).symm.trans hz⟩
  have hFreg (z) (hz : F z = c) : fderiv ℝ F z ≠ 0 := by
    obtain ⟨hzH,huz⟩ := hlevel z hz
    rw [(hFeq z hzH (huz.le.trans hcd.le)).fderiv_eq]
    exact fun hh => hreg z hzH huz ((fderiv_squaredReciprocalPotential_eq_zero_iff
      hf (ne_of_gt hk) hzH).mp hh)
  have hL : IsCompact {z | F z = c} := hP.of_isClosed_subset
    (isClosed_eq hFc.continuous continuous_const)
    (fun z hz => ⟨(hlevel z hz).1, (hlevel z hz).2.le.trans hcd.le⟩)
  obtain ⟨C,hC,hdis,hcurves⟩ := compact_regular_level_oriented_curves hFc hFs hFreg hL
  let ι := {S : Set ℂ // S ∈ C}
  choose γ hγrange hγc hγp hγi hγd hγm hγr hγdown using
    (fun S : ι => hcurves S.1 S.2)
  have hγlevel (i : ι) (t : ℝ) : F (γ i t) = c := by
    have hh : γ i t ∈ ⋃ S ∈ C, S := mem_iUnion₂.mpr
      ⟨i.1,i.2,hγrange i ▸ mem_range_self t⟩
    rwa [hC] at hh
  have hγH (i : ι) (t : ℝ) : γ i t ∈ halfPlane := (hlevel _ (hγlevel i t)).1
  have hγu (i : ι) (t : ℝ) : u (γ i t) = c := (hlevel _ (hγlevel i t)).2
  have hcover (z) : F z = c ↔ ∃ i : ι, z ∈ range (γ i) := by
    constructor
    · intro hz
      have hm : z ∈ ⋃ S ∈ C, S := hC.symm ▸ hz
      obtain ⟨S,hS,hzS⟩ := mem_iUnion₂.mp hm
      exact ⟨⟨S,hS⟩, (hγrange ⟨S,hS⟩).symm ▸ hzS⟩
    · rintro ⟨i,t,rfl⟩
      exact hγlevel i t
  have hγdis (i j : ι) (hij : i ≠ j) : Disjoint (range (γ i)) (range (γ j)) := by
    rw [hγrange,hγrange]
    exact hdis i.1 i.2 j.1 j.2 (Subtype.val_injective.ne hij)
  have hbelow (i : ι) (w : ℂ) (hw : w ∉ range (γ i))
      (hind : loopIndex (periodicLoop (hγc i).continuous 0) w ≠ 0) : F w < c := by
    have hw' : w ∈ windingInterior (periodicLoop (hγc i).continuous 0) :=
      ⟨by rwa [periodicLoop_range _ (hγp i) 0],hind⟩
    have hh := squaredReciprocalPotential_lt_windingInterior hf hk hc ξ
      (periodicLoop (hγc i).continuous 0) (periodicLoop_closed _ (hγp i) 0)
      (fun t => hγH i ((t:ℝ)+0)) (fun t => hγu i ((t:ℝ)+0)) hw'
    exact (hFlt w c hcd).mpr hh
  have hFzero : F 0 = d := hFout 0 (by simp [halfPlane])
  have habove : ∃ z, c < F z := ⟨0,hFzero ▸ hcd⟩
  obtain ⟨X,hXeq⟩ := continuous_extension_near_compact hK isOpen_halfPlane hKH
    (fun z hz => (differentiableAt_regularizedGradient hf hz k ξ).continuousAt)
  have hfinite : {z | z ∈ K ∧ x z = 0}.Finite := finite_regular_zeros_on_compact hK
    (fun z hz => (differentiableAt_regularizedGradient hf (hKH hz) k ξ).continuousAt.continuousWithinAt)
    (fun z hz hzero => ⟨differentiableAt_regularizedGradient hf (hKH hz) k ξ,
      det_regularizedGradient_ne_zero hf (ne_of_gt hk) hg (hKH hz) hzero⟩)
  let s := hfinite.toFinset
  have hs (z) : z ∈ s ↔ z ∈ K ∧ x z = 0 := hfinite.mem_toFinset
  have hsK (z) (hz : z ∈ s) : z ∈ K := ((hs z).mp hz).1
  have hXzero (z) (hz : z ∈ K) : X z = 0 ↔ z ∈ s := by
    rw [(hXeq z hz).self_of_nhds,hs]
    exact ⟨fun h => ⟨hz,h⟩,fun h => h.2⟩
  have hD (z) (hz : z ∈ s) :
      HasFDerivAt X (fderiv ℝ x z) z ∧ LinearMap.det (fderiv ℝ x z).toLinearMap ≠ 0 := by
    refine ⟨(differentiableAt_regularizedGradient hf (hKH (hsK z hz)) k ξ).hasFDerivAt.congr_of_eventuallyEq
      (hXeq z (hsK z hz)),?_⟩
    exact det_regularizedGradient_ne_zero hf (ne_of_gt hk) hg (hKH (hsK z hz)) ((hs z).mp hz).2
  have hγK (i : ι) (t : ℝ) : γ i t ∈ K := hPK ⟨hγH i t,(hγu i t).le.trans hcd.le⟩
  have hX (i : ι) (t : ℝ) : X (γ i t) ≠ 0 := by
    rw [(hXeq _ (hγK i t)).self_of_nhds]
    exact hreg _ (hγH i t) (hγu i t)
  have horth (i : ι) (t : ℝ) : (X (γ i t)*conj (deriv (γ i) t)).re = 0 := by
    have he : HasDerivAt (fun q => F (γ i q))
        (fderiv ℝ F (γ i t) (deriv (γ i) t)) t :=
      ((hFc.differentiable (by norm_num)) _).hasFDerivAt.comp_hasDerivAt t
        (((hγc i).differentiable (by norm_num)) t).hasDerivAt
    have he0 : fderiv ℝ F (γ i t) (deriv (γ i) t) = 0 :=
      (he.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun q => (hγlevel i q).symm))).unique (hasDerivAt_const t c)
    rw [(hFeq _ (hγH i t) ((hγu i t).le.trans hcd.le)).fderiv_eq,
      fderiv_squaredReciprocalPotential_apply hf (ne_of_gt hk) (hγH i t)] at he0
    rw [(hXeq _ (hγK i t)).self_of_nhds]
    exact (mul_eq_zero.mp he0).resolve_left (mul_ne_zero (by norm_num)
      (ne_of_gt (Real.rpow_pos_of_pos (hγH i t) (-2*k))))
  have hsum := regular_level_index_sum hFc.continuous γ hγc hγp hγi hγd hγm hγr hγdown
    hγlevel (fun z hz => ⟨hFc.contDiffAt.of_le (by norm_num),hFreg z hz⟩)
    hcover hγdis hbelow habove hKcv hγK s X (fderiv ℝ x) hsK hXzero hD hX horth
  refine ⟨s,Fintype.card ι,?_,?_,?_,?_⟩
  · intro z hz
    exact ⟨hKH (hsK z hz),((hs z).mp hz).2⟩
  · intro z hzH hzu
    rw [hs]
    exact ⟨fun h => h.2,fun hx => ⟨hPK ⟨hzH,hzu.le.trans hcd.le⟩,hx⟩⟩
  · convert hsum using 1
    apply Finset.sum_congr rfl
    intro z hz
    simp only [show (F z < c) ↔ u z < c from (hFlt z c hcd).trans
      (and_iff_right (hKH (hsK z hz)))]
    rfl
  · rintro ⟨z,hzH,hpole⟩
    have huz : u z = 0 := by simp [u,squaredReciprocalPotential,hpole]
    have hFz : F z = 0 := (hFeq z hzH (huz.le.trans hd.le)).self_of_nhds.trans huz
    obtain ⟨w,hw⟩ := intermediate_value_univ z 0 hFc.continuous
      (show c ∈ Icc (F z) (F 0) by rw [hFz,hFzero]; exact ⟨hc.le,hcd.le⟩)
    obtain ⟨i,_hi⟩ := (hcover w).mp hw
    exact Nat.succ_le_iff.mpr (Fintype.card_pos_iff.mpr ⟨i⟩)

lemma planeIndex_regularizedGradient_at_critical {f : ℂ → ℂ}
    (hf : UnivalentOn f halfPlane) {k : ℝ} (hk : k ≠ 0)
    {ξ z : ℂ} (hz : z ∈ halfPlane) (hcrit : criticalMap f k z = ξ) :
    planeIndex (fderiv ℝ (regularizedGradient f k ξ) z) =
      if normalizedJacobian f k z < 0 then 1 else -1 := by
  have hp : 0 < ‖((k : ℂ)*Complex.I/(z.im : ℂ))*(f z-ξ)‖^2 * ‖deriv f z‖^2 := by
    apply mul_pos
    · apply sq_pos_of_pos
      apply norm_pos_iff.mpr
      exact mul_ne_zero (div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hk)
        Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr (ne_of_gt hz)))
        (sub_ne_zero.mpr (criticalMap_ne_pole hf hk hz hcrit))
    · exact sq_pos_of_pos (norm_pos_iff.mpr (univalent_deriv_ne_zero isOpen_halfPlane hf hz))
  rw [planeIndex,det_regularizedGradient_at_critical hf hz hcrit]
  congr 1
  apply propext
  rw [neg_mul,neg_mul,neg_pos]
  constructor
  · intro h
    by_contra hn
    exact (not_lt_of_ge (mul_nonneg hp.le (le_of_not_gt hn))) h
  · exact mul_neg_of_pos_of_neg hp

lemma critical_count_strict_sublevel {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} (hk : 0 < k) {ξ : ℂ} (hg : GoodPair f k ξ) {c : ℝ} (hc : 0 < c)
    (hreg : ∀ z ∈ halfPlane, squaredReciprocalPotential f k ξ z = c →
      regularizedGradient f k ξ z ≠ 0) :
    let critical := {z | z ∈ halfPlane ∧ criticalMap f k z = ξ ∧
      squaredReciprocalPotential f k ξ z < c}
    critical.Finite ∧ ({z ∈ critical | 0 < normalizedJacobian f k z}).ncard ≤
      ({z ∈ critical | normalizedJacobian f k z < 0}).ncard := by
  classical
  dsimp only
  obtain ⟨s,N,hs,hsall,hsum,hpole⟩ := regular_potential_level_index_sum hf hk hg hc hreg
  let u := squaredReciprocalPotential f k ξ
  let p := s.filter (fun z => u z < c ∧ f z = ξ)
  let m := s.filter (fun z => u z < c ∧ criticalMap f k z = ξ ∧ normalizedJacobian f k z < 0)
  let a := s.filter (fun z => u z < c ∧ criticalMap f k z = ξ ∧ 0 < normalizedJacobian f k z)
  have hcritmem (z) (hz : z ∈ halfPlane) (hG : criticalMap f k z = ξ) (hu : u z < c) : z ∈ s :=
    (hsall z hz hu).mpr ((regularizedGradient_eq_zero_iff (ne_of_gt hk) hz).mpr (Or.inr hG))
  have hfinite : {z | z ∈ halfPlane ∧ criticalMap f k z = ξ ∧ u z < c}.Finite :=
    s.finite_toSet.subset (fun z hz => hcritmem z hz.1 hz.2.1 hz.2.2)
  have hmset : {z | (z ∈ halfPlane ∧ criticalMap f k z = ξ ∧ u z < c) ∧
      normalizedJacobian f k z < 0} = (m : Set ℂ) := by
    ext z
    simp only [m,Finset.mem_coe,Finset.mem_filter,mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hz,hG,hu⟩,hJ⟩
      exact ⟨hcritmem z hz hG hu,hu,hG,hJ⟩
    · rintro ⟨hz,hu,hG,hJ⟩
      exact ⟨⟨(hs z hz).1,hG,hu⟩,hJ⟩
  have haset : {z | (z ∈ halfPlane ∧ criticalMap f k z = ξ ∧ u z < c) ∧
      0 < normalizedJacobian f k z} = (a : Set ℂ) := by
    ext z
    simp only [a,Finset.mem_coe,Finset.mem_filter,mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hz,hG,hu⟩,hJ⟩
      exact ⟨hcritmem z hz hG hu,hu,hG,hJ⟩
    · rintro ⟨hz,hu,hG,hJ⟩
      exact ⟨⟨(hs z hz).1,hG,hu⟩,hJ⟩
  have hpcard : p.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro z hz w hw
    obtain ⟨hz,huz,hpz⟩ := Finset.mem_filter.mp hz
    obtain ⟨hw,huw,hpw⟩ := Finset.mem_filter.mp hw
    exact hf.2 (hs z hz).1 (hs w hw).1 (hpz.trans hpw.symm)
  have hpN : p.card ≤ N := by
    by_cases hpe : p = ∅
    · simp [hpe]
    · obtain ⟨z,hz⟩ := Finset.nonempty_iff_ne_empty.mpr hpe
      obtain ⟨hz,huz,hpz⟩ := Finset.mem_filter.mp hz
      exact hpcard.trans (hpole ⟨z,(hs z hz).1,hpz⟩)
  have hterm (z) (hz : z ∈ s) :
      (if u z < c then planeIndex (fderiv ℝ (regularizedGradient f k ξ) z) else 0) =
        (if u z < c ∧ f z = ξ then (1 : ℤ) else 0) +
        (if u z < c ∧ criticalMap f k z = ξ ∧ normalizedJacobian f k z < 0 then 1 else 0) -
        (if u z < c ∧ criticalMap f k z = ξ ∧ 0 < normalizedJacobian f k z then 1 else 0) := by
    by_cases hu : u z < c
    · simp only [hu,true_and,ite_true]
      rcases (regularizedGradient_eq_zero_iff (ne_of_gt hk) (hs z hz).1).mp (hs z hz).2 with hpz | hG
      · have hGn : criticalMap f k z ≠ ξ := fun h => criticalMap_ne_pole hf (ne_of_gt hk) (hs z hz).1 h hpz
        simp [hpz,hGn,planeIndex,det_regularizedGradient_at_pole_pos hf (ne_of_gt hk) (hs z hz).1 hpz]
      · have hpn := criticalMap_ne_pole hf (ne_of_gt hk) (hs z hz).1 hG
        rw [planeIndex_regularizedGradient_at_critical hf (ne_of_gt hk) (hs z hz).1 hG]
        rcases lt_or_gt_of_ne (hg.2 z (hs z hz).1 hG) with hJ | hJ
        · simp [hpn,hG,hJ,not_lt_of_ge hJ.le]
        · simp [hpn,hG,hJ,not_lt_of_ge hJ.le]
    · simp [hu]
  have heuler : (p.card : ℤ) + m.card - a.card = N := by
    rw [← hsum]
    calc
      (p.card : ℤ) + m.card - a.card =
          ∑ z ∈ s, ((if u z < c ∧ f z = ξ then (1 : ℤ) else 0) +
            (if u z < c ∧ criticalMap f k z = ξ ∧ normalizedJacobian f k z < 0 then 1 else 0) -
            (if u z < c ∧ criticalMap f k z = ξ ∧ 0 < normalizedJacobian f k z then 1 else 0)) := by
        simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_boole,p,m,a]
      _ = _ := Finset.sum_congr rfl (fun z hz => (hterm z hz).symm)
  refine ⟨hfinite,?_⟩
  change ({z | (z ∈ halfPlane ∧ criticalMap f k z = ξ ∧ u z < c) ∧
      0 < normalizedJacobian f k z}).ncard ≤
    ({z | (z ∈ halfPlane ∧ criticalMap f k z = ξ ∧ u z < c) ∧
      normalizedJacobian f k z < 0}).ncard
  rw [haset,hmset,Set.ncard_coe_finset,Set.ncard_coe_finset]
  omega

lemma finite_critical_squared_sublevel {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} (hk : 0 ≤ k) {ξ : ℂ} (hg : GoodPair f k ξ) {d : ℝ} (hd : 0 < d) :
    {z | z ∈ halfPlane ∧ criticalMap f k z = ξ ∧
      squaredReciprocalPotential f k ξ z ≤ d}.Finite := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  apply (finite_critical_superlevel hf hg (h := (Real.sqrt d)⁻¹) (inv_pos.mpr hs)).subset
  intro z hz
  refine ⟨hz.1,hz.2.1,(potential_ge_iff_reciprocalPotential_le hk (inv_pos.mpr hs) hz.1).mpr ?_⟩
  rw [inv_inv]
  have hh := hz.2.2
  rw [squaredReciprocalPotential_eq_sq hz.1] at hh
  nlinarith [Real.sq_sqrt hd.le]

lemma potential_ge_iff_squaredReciprocal_le {f : ℂ → ℂ} {k h : ℝ}
    (hk : 0 ≤ k) (hh : 0 < h) {ξ z : ℂ} (hz : z ∈ halfPlane) :
    ENNReal.ofReal h ≤ potential f k ξ z ↔
      squaredReciprocalPotential f k ξ z ≤ (h⁻¹)^2 := by
  rw [potential_ge_iff_reciprocalPotential_le hk hh hz,squaredReciprocalPotential_eq_sq hz]
  exact (sq_le_sq₀ (div_nonneg (norm_nonneg _) (Real.rpow_nonneg hz.le _))
    (inv_nonneg.mpr hh.le)).symm

lemma finset_gap_above (s : Finset ℝ) (r d : ℝ) (hrd : r < d) :
    ∃ c, r < c ∧ c < d ∧ ∀ a ∈ s, r < a → c < a := by
  classical
  induction s using Finset.induction_on generalizing d with
  | empty =>
    obtain ⟨c,hrc,hcd⟩ := exists_between hrd
    exact ⟨c,hrc,hcd,by simp⟩
  | @insert a s ha ih =>
    by_cases hra : r < a
    · obtain ⟨c,hrc,hcd,hcs⟩ := ih (min d a) (lt_min hrd hra)
      refine ⟨c,hrc,hcd.trans_le (min_le_left _ _),?_⟩
      intro b hb hrb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hcd.trans_le (min_le_right _ _)
      · exact hcs b hb hrb
    · obtain ⟨c,hrc,hcd,hcs⟩ := ih d hrd
      refine ⟨c,hrc,hcd,?_⟩
      intro b hb hrb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact (hra hrb).elim
      · exact hcs b hb hrb

theorem critical_count {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {k : ℝ} (hk : 0 < k) {ξ : ℂ} (hg : GoodPair f k ξ) {h : ℝ} (hh : 0 < h) :
    let critical := {z | z ∈ halfPlane ∧ criticalMap f k z = ξ ∧
      ENNReal.ofReal h ≤ potential f k ξ z}
    critical.Finite ∧ ({z ∈ critical | 0 < normalizedJacobian f k z}).ncard ≤
      ({z ∈ critical | normalizedJacobian f k z < 0}).ncard := by
  classical
  let u := squaredReciprocalPotential f k ξ
  let r := (h⁻¹)^2
  have hr : 0 < r := sq_pos_of_pos (inv_pos.mpr hh)
  have hd : 0 < r+1 := by linarith
  have hfinite := finite_critical_squared_sublevel hf hk.le hg hd
  let s := hfinite.toFinset.image u
  obtain ⟨c,hrc,hcd,hcs⟩ := finset_gap_above s r (r+1) (by linarith)
  have hcmem (z) (hz : z ∈ halfPlane) (hG : criticalMap f k z = ξ)
      (hu : u z ≤ r+1) : u z ∈ s :=
    Finset.mem_image.mpr ⟨z,hfinite.mem_toFinset.mpr ⟨hz,hG,hu⟩,rfl⟩
  have hcut (z) (hz : z ∈ halfPlane) (hG : criticalMap f k z = ξ) : u z < c ↔ u z ≤ r := by
    constructor
    · intro huc
      by_contra hn
      have hru : r < u z := lt_of_not_ge hn
      exact (hcs (u z) (hcmem z hz hG (huc.trans hcd).le) hru).not_gt huc
    · exact fun h => h.trans_lt hrc
  have hreg (z) (hz : z ∈ halfPlane) (huc : u z = c) : regularizedGradient f k ξ z ≠ 0 := by
    intro hzero
    rcases (regularizedGradient_eq_zero_iff (ne_of_gt hk) hz).mp hzero with hp | hG
    · have huz : u z = 0 := by simp [u,squaredReciprocalPotential,hp]
      linarith
    · have hmem := hcmem z hz hG (huc.le.trans hcd.le)
      have hcc := hcs (u z) hmem (hrc.trans_eq huc.symm)
      linarith
  have hc := critical_count_strict_sublevel hf hk hg (hr.trans hrc) hreg
  have he : {z | z ∈ halfPlane ∧ criticalMap f k z = ξ ∧ ENNReal.ofReal h ≤ potential f k ξ z} =
      {z | z ∈ halfPlane ∧ criticalMap f k z = ξ ∧ u z < c} := by
    ext z
    constructor
    · rintro ⟨hz,hG,hV⟩
      exact ⟨hz,hG,(hcut z hz hG).mpr ((potential_ge_iff_squaredReciprocal_le hk.le hh hz).mp hV)⟩
    · rintro ⟨hz,hG,hu⟩
      exact ⟨hz,hG,(potential_ge_iff_squaredReciprocal_le hk.le hh hz).mpr ((hcut z hz hG).mp hu)⟩
  dsimp only
  rw [he]
  exact hc

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.RankPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma continuous_class_deriv : Continuous (fun p : DiskClass × halfPlane => deriv (classFun p.1) p.2) := by
  simpa only [iteratedDeriv_one] using continuous_classJet_eval 1

lemma continuous_class_deriv_deriv :
    Continuous (fun p : DiskClass × halfPlane => deriv (deriv (classFun p.1)) p.2) := by
  simpa only [show 2 = 1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using continuous_classJet_eval 2

lemma continuous_class_criticalMap (k : ℝ) :
    Continuous (fun p : DiskClass × halfPlane => criticalMap (classFun p.1) k p.2) := by
  exact continuous_classFun_eval.sub ((continuous_const.mul
    (Complex.continuous_ofReal.comp (Complex.continuous_im.comp
      (continuous_subtype_val.comp continuous_snd)))).mul continuous_class_deriv)

lemma continuous_class_fderiv_criticalMap (k : ℝ) :
    Continuous (fun p : DiskClass × halfPlane => fderiv ℝ (criticalMap (classFun p.1) k) p.2) := by
  let A : ℂ →L[ℝ] ℂ := 1
  let B : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.imCLM
  have he (p : DiskClass × halfPlane) : fderiv ℝ (criticalMap (classFun p.1) k) p.2 =
      deriv (classFun p.1) p.2 • A -
      (Complex.I / (k : ℂ) * (p.2.val.im : ℂ) * deriv (deriv (classFun p.1)) p.2) • A -
      (Complex.I / (k : ℂ) * deriv (classFun p.1) p.2) • B := by
    ext v
    rw [fderiv_criticalMap_apply (classFun_schlicht p.1).1 p.2.property]
    change _ = deriv (classFun p.1) p.2 * v -
      (Complex.I / (k : ℂ) * (p.2.val.im : ℂ) * deriv (deriv (classFun p.1)) p.2) * v -
      (Complex.I / (k : ℂ) * deriv (classFun p.1) p.2) * (v.im : ℂ)
    ring
  simp_rw [he]
  have hy : Continuous (fun p : DiskClass × halfPlane => (p.2.val.im : ℂ)) :=
    Complex.continuous_ofReal.comp (Complex.continuous_im.comp (continuous_subtype_val.comp continuous_snd))
  exact ((continuous_class_deriv.smul continuous_const).sub
    (((continuous_const.mul hy).mul continuous_class_deriv_deriv).smul continuous_const)).sub
    ((continuous_const.mul continuous_class_deriv).smul continuous_const)

lemma continuous_class_normalizedJacobian (k : ℝ) :
    Continuous (fun p : DiskClass × halfPlane => normalizedJacobian (classFun p.1) k p.2) := by
  apply (ContinuousLinearMap.continuous_det.comp (continuous_class_fderiv_criticalMap k)).div
    (continuous_class_deriv.norm.pow 2)
  intro p
  exact pow_ne_zero _ (norm_ne_zero_iff.mpr
    (univalent_deriv_ne_zero isOpen_halfPlane (classFun_schlicht p.1).1 p.2.property))

lemma criticalHeight_pos {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) {k : ℝ} (hk : 0 < k)
    {z : ℂ} (hz : z ∈ halfPlane) : 0 < criticalHeight f k z := by
  exact mul_pos (mul_pos hk (Real.rpow_pos_of_pos hz _))
    (norm_pos_iff.mpr (inv_ne_zero (univalent_deriv_ne_zero isOpen_halfPlane hf hz)))

lemma continuous_class_criticalHeight (k : ℝ) :
    Continuous (fun p : DiskClass × halfPlane => criticalHeight (classFun p.1) k p.2) := by
  have hy : Continuous (fun p : DiskClass × halfPlane => p.2.val.im^(k-1)) :=
    (Complex.continuous_im.comp (continuous_subtype_val.comp continuous_snd)).rpow_const
      (fun p => Or.inl (ne_of_gt p.2.property))
  have hh : Continuous (fun p : DiskClass × halfPlane =>
      k * p.2.val.im^(k-1) * ‖deriv (classFun p.1) p.2‖⁻¹) :=
    (continuous_const.mul hy).mul (continuous_class_deriv.norm.inv₀
      (fun p => norm_ne_zero_iff.mpr (univalent_deriv_ne_zero isOpen_halfPlane
        (classFun_schlicht p.1).1 p.2.property)))
  exact hh.congr (fun p => by simp only [criticalHeight,reciprocalDeriv,norm_inv])

lemma continuousOn_prod_of_continuous_subtype.{u_1, u_2, u_3} {P : Type u_1} {X : Type u_2} {Y : Type u_3}
    [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} {F : P → X → Y}
    (hF : Continuous (fun q : P × s => F q.1 q.2)) :
    ContinuousOn (fun q : P × X => F q.1 q.2) (univ ×ˢ s) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact hF.comp (continuous_subtype_val.fst.prodMk
    (continuous_subtype_val.snd.subtype_mk (fun q => q.property.2)))

lemma criticalMap_congr {f g : ℂ → ℂ} (he : EqOn f g halfPlane) (k : ℝ) :
    EqOn (criticalMap f k) (criticalMap g k) halfPlane := by
  intro z hz
  rw [criticalMap,criticalMap,he hz,he.deriv isOpen_halfPlane hz]

lemma normalizedJacobian_congr {f g : ℂ → ℂ} (he : EqOn f g halfPlane) (k : ℝ) :
    EqOn (normalizedJacobian f k) (normalizedJacobian g k) halfPlane := by
  intro z hz
  have hG : criticalMap f k =ᶠ[𝓝 z] criticalMap g k := by
    filter_upwards [isOpen_halfPlane.mem_nhds hz] with w hw
    exact criticalMap_congr he k hw
  rw [normalizedJacobian,normalizedJacobian,hG.fderiv_eq,he.deriv isOpen_halfPlane hz]

lemma criticalHeight_congr {f g : ℂ → ℂ} (he : EqOn f g halfPlane) (k : ℝ) :
    EqOn (criticalHeight f k) (criticalHeight g k) halfPlane := by
  intro z hz
  rw [criticalHeight,criticalHeight,reciprocalDeriv,reciprocalDeriv,he.deriv isOpen_halfPlane hz]

lemma goodPair_congr {f g : ℂ → ℂ} (he : EqOn f g halfPlane) (k : ℝ) (ξ : ℂ) :
    GoodPair f k ξ ↔ GoodPair g k ξ := by
  have hs (δ : ℝ) : {z | z ∈ halfPlane ∧ ENNReal.ofReal δ ≤ potential f k ξ z} =
      {z | z ∈ halfPlane ∧ ENNReal.ofReal δ ≤ potential g k ξ z} := by
    ext z
    by_cases hz : z ∈ halfPlane
    · simp only [mem_ofPred_eq,hz,true_and,potential,he hz]
    · simp only [mem_ofPred_eq,hz,false_and]
  simp only [GoodPair,hs]
  apply and_congr_right
  intro _
  constructor <;> intro h z hz hG
  · rw [← normalizedJacobian_congr he k hz]
    exact h z hz ((criticalMap_congr he k hz).trans hG)
  · rw [normalizedJacobian_congr he k hz]
    exact h z hz ((criticalMap_congr he k hz).symm.trans hG)

lemma affineHome_apply (t : ℂ) (ht : t ∈ halfPlane) (z : ℂ) :
    affineHome t ht z = affine t z := rfl

lemma affine_mem_iff {t : ℂ} (ht : t ∈ halfPlane) (z : ℂ) :
    affine t z ∈ halfPlane ↔ z ∈ halfPlane := by
  change 0 < (affine t z).im ↔ 0 < z.im
  simp only [affine,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
    zero_mul,zero_add,add_zero]
  exact mul_pos_iff_of_pos_left ht

lemma heightScaleInverse_pos {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) (k : ℝ)
    {t : ℂ} (ht : t ∈ halfPlane) : 0 < heightScaleInverse f k t :=
  div_pos (Real.rpow_pos_of_pos ht _) (norm_pos_iff.mpr (univalent_deriv_ne_zero isOpen_halfPlane hf ht))

lemma reciprocalPotential_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) (k : ℝ)
    {t z : ℂ} (ht : t ∈ halfPlane) (hz : z ∈ halfPlane) (ξ : ℂ) :
    reciprocalPotential (reroot f t) k (rerootTarget f t ξ) z =
      heightScaleInverse f k t * reciprocalPotential f k ξ (affine t z) := by
  have he : reroot f t z-rerootTarget f t ξ =
      (f (affine t z)-ξ)/((t.im : ℂ)*deriv f t) := by
    simp only [reroot,rerootTarget,← sub_div]
    congr 1
    ring
  have hn : ‖deriv f t‖ ≠ 0 := norm_ne_zero_iff.mpr (univalent_deriv_ne_zero isOpen_halfPlane hf ht)
  have hpow : z.im^k ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hz k)
  have him : (affine t z).im = t.im*z.im := by simp [affine]
  rw [reciprocalPotential,he,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht,
    reciprocalPotential,him,Real.mul_rpow ht.le hz.le,heightScaleInverse,Real.rpow_sub_one (ne_of_gt ht)]
  have htp : t.im^k ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht _)
  field_simp

lemma criticalHeight_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) (k : ℝ)
    {t z : ℂ} (ht : t ∈ halfPlane) (hz : z ∈ halfPlane) :
    criticalHeight (reroot f t) k z = criticalHeight f k (affine t z) / heightScaleInverse f k t := by
  have him : (affine t z).im = t.im*z.im := by simp [affine]
  have hn : ‖deriv f t‖ ≠ 0 := norm_ne_zero_iff.mpr (univalent_deriv_ne_zero isOpen_halfPlane hf ht)
  have hp : t.im^(k-1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht _)
  rw [criticalHeight,reciprocalDeriv_reroot hf ht hz,norm_div,criticalHeight,him,
    Real.mul_rpow ht.le hz.le,heightScaleInverse]
  simp only [reciprocalDeriv,norm_inv]
  field_simp

lemma criticalMap_reroot_fiber {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) (k : ℝ)
    {t z : ℂ} (ht : t ∈ halfPlane) (hz : z ∈ halfPlane) (ξ : ℂ) :
    criticalMap (reroot f t) k z = rerootTarget f t ξ ↔ criticalMap f k (affine t z) = ξ := by
  rw [criticalMap_reroot hf ht hz,rerootTarget,div_left_inj' (mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (ne_of_gt ht)) (univalent_deriv_ne_zero isOpen_halfPlane hf ht)),sub_left_inj]

lemma potential_level_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) {k : ℝ} (hk : 0 ≤ k)
    {t : ℂ} (ht : t ∈ halfPlane) (ξ : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    {z | z ∈ halfPlane ∧ ENNReal.ofReal δ ≤ potential (reroot f t) k (rerootTarget f t ξ) z} =
      (affineHome t ht) ⁻¹' {w | w ∈ halfPlane ∧
        ENNReal.ofReal (δ*heightScaleInverse f k t) ≤ potential f k ξ w} := by
  have hc := heightScaleInverse_pos hf k ht
  ext z
  simp only [mem_ofPred_eq,mem_preimage,affineHome_apply,affine_mem_iff ht]
  apply and_congr_right
  intro hz
  rw [potential_ge_iff_reciprocalPotential_le hk hδ hz,
    potential_ge_iff_reciprocalPotential_le hk (mul_pos hδ hc) (affine_mem ht hz),
    reciprocalPotential_reroot hf k ht hz ξ,mul_inv_rev]
  rw [mul_comm,← le_div_iff₀ hc,div_eq_mul_inv]
  rw [mul_comm δ⁻¹]

lemma goodPair_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) {k : ℝ} (hk : 0 < k)
    {t : ℂ} (ht : t ∈ halfPlane) (ξ : ℂ) :
    GoodPair (reroot f t) k (rerootTarget f t ξ) ↔ GoodPair f k ξ := by
  have hc := heightScaleInverse_pos hf k ht
  constructor
  · rintro ⟨hcompact,hregular⟩
    constructor
    · intro δ hδ
      have h := hcompact (δ/heightScaleInverse f k t) (div_pos hδ hc)
      rw [potential_level_reroot hf hk.le ht ξ (div_pos hδ hc),div_mul_cancel₀ _ (ne_of_gt hc)] at h
      exact (affineHome t ht).isCompact_preimage.mp h
    · intro w hw hG
      let z := (affineHome t ht).symm w
      have he : affine t z = w := (affineHome t ht).apply_symm_apply w
      have hz : z ∈ halfPlane := (affine_mem_iff ht z).mp (he.symm ▸ hw)
      have hr := hregular z hz ((criticalMap_reroot_fiber hf k ht hz ξ).mpr (he.symm ▸ hG))
      rwa [normalizedJacobian_reroot hf ht hz k (ne_of_gt hk),he] at hr
  · rintro ⟨hcompact,hregular⟩
    constructor
    · intro δ hδ
      rw [potential_level_reroot hf hk.le ht ξ hδ]
      exact (affineHome t ht).isCompact_preimage.mpr (hcompact _ (mul_pos hδ hc))
    · intro z hz hG
      rw [normalizedJacobian_reroot hf ht hz k (ne_of_gt hk)]
      exact hregular _ (affine_mem ht hz) ((criticalMap_reroot_fiber hf k ht hz ξ).mp hG)

lemma orderRank_strictMonoOn.{u_1} {α : Type u_1} [LinearOrder α] {S : Set α}
    (hfin : ∀ x ∈ S, (S ∩ Iio x).Finite) : StrictMonoOn (orderRank S) S := by
  intro x hx y hy hxy
  apply Set.ncard_lt_ncard _ (hfin y hy)
  refine ssubset_iff_subset_ne.mpr ⟨?_,?_⟩
  · exact fun a ha => ⟨ha.1,ha.2.trans hxy⟩
  · intro he
    have : x ∈ S ∩ Iio x := he ▸ (show x ∈ S ∩ Iio y from ⟨hx,hxy⟩)
    exact lt_irrefl x this.2

lemma orderRank_injOn.{u_1} {α : Type u_1} [LinearOrder α] {S : Set α}
    (hfin : ∀ x ∈ S, (S ∩ Iio x).Finite) : InjOn (orderRank S) S :=
  (orderRank_strictMonoOn hfin).injOn

lemma orderRank_finset_enum.{u_1} {α : Type u_1} [LinearOrder α] (s : Finset α)
    (j : Fin s.card) : orderRank (s : Set α) (s.orderEmbOfFin rfl j) = j.val := by
  classical
  let e := s.orderEmbOfFin rfl
  have he : (s : Set α) ∩ Iio (e j) = e '' Iio j := by
    ext a
    constructor
    · intro ha
      obtain ⟨i,rfl⟩ := (s.range_orderEmbOfFin rfl).symm ▸ ha.1
      exact ⟨i,e.lt_iff_lt.mp ha.2,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨s.orderEmbOfFin_mem rfl i,e.strictMono hi⟩
  rw [orderRank,he,Set.ncard_image_of_injective _ e.injective]
  rw [← Finset.coe_Iio,Set.ncard_coe_finset,Fin.card_Iio]

lemma exists_orderRank_of_finite_initial.{u_1} {α : Type u_1} [LinearOrder α]
    {S A : Set α} (hA : A.Finite) (hAS : A ⊆ S)
    (hinit : ∀ x ∈ A, ∀ y ∈ S, y < x → y ∈ A)
    {j : ℕ} (hj : j < A.ncard) : ∃ x ∈ A, orderRank S x = j := by
  classical
  let s := hA.toFinset
  have hscard : s.card = A.ncard := (Set.ncard_eq_toFinset_card A hA).symm
  let x : α := s.orderEmbOfFin rfl ⟨j,by simpa [hscard] using hj⟩
  have hx : x ∈ A := hA.mem_toFinset.mp (s.orderEmbOfFin_mem rfl ⟨j,by simpa [hscard] using hj⟩)
  refine ⟨x,hx,?_⟩
  have he : S ∩ Iio x = A ∩ Iio x := by
    ext y
    exact ⟨fun hy => ⟨hinit x hx y hy.1 hy.2,hy.2⟩,fun hy => ⟨hAS hy.1,hy.2⟩⟩
  calc
    orderRank S x = orderRank A x := congrArg Set.ncard he
    _ = j := by simpa only [s,Set.Finite.coe_toFinset] using
      orderRank_finset_enum s ⟨j,by simpa [hscard] using hj⟩

lemma heightOrder_lt_iff (H : ℂ → ℝ) (z w : ℂ) :
    @LT.lt ℂ (heightOrder H).toLT z w ↔ heightPrecedes H z w := by
  change heightKey H z < heightKey H w ↔ _
  simp only [heightKey,Prod.Lex.toLex_lt_toLex,neg_lt_neg_iff,neg_inj,heightPrecedes]

lemma heightOrder_height_le {H : ℂ → ℝ} {z w : ℂ}
    (h : @LT.lt ℂ (heightOrder H).toLT z w) : H w ≤ H z := by
  rcases (heightOrder_lt_iff H z w).mp h with h | ⟨h,_⟩
  · exact h.le
  · exact h.ge

lemma heightRank_pred_finite {H : ℂ → ℝ} {S : Set ℂ} {z : ℂ}
    (hfin : (S ∩ {w | H z ≤ H w}).Finite) :
    @Set.Finite ℂ (S ∩ @Iio ℂ (heightOrder H).toPreorder z) := by
  exact hfin.subset (fun w hw => ⟨hw.1,heightOrder_height_le hw.2⟩)

lemma heightRank_lt_segment {H : ℂ → ℝ} {S : Set ℂ} {z : ℂ} (hz : z ∈ S)
    (hfin : (S ∩ {w | H z ≤ H w}).Finite) :
    heightRank H S z < (S ∩ {w | H z ≤ H w}).ncard := by
  let _ := heightOrder H
  apply Set.ncard_lt_ncard _ hfin
  refine ssubset_iff_subset_ne.mpr ⟨fun w hw => ⟨hw.1,heightOrder_height_le hw.2⟩,?_⟩
  intro he
  have : z ∈ S ∩ Iio z := he ▸ (show z ∈ S ∩ {w | H z ≤ H w} from ⟨hz,show H z ≤ H z from le_refl _⟩)
  exact lt_irrefl z this.2

lemma exists_equal_heightRank {H : ℂ → ℝ} {A B : Set ℂ} {z : ℂ}
    (hz : z ∈ A) (hAf : (A ∩ {w | H z ≤ H w}).Finite)
    (hBf : (B ∩ {w | H z ≤ H w}).Finite)
    (hc : (A ∩ {w | H z ≤ H w}).ncard ≤ (B ∩ {w | H z ≤ H w}).ncard) :
    ∃ w ∈ B, H z ≤ H w ∧ heightRank H B w = heightRank H A z := by
  let _ := heightOrder H
  have hj := (heightRank_lt_segment hz hAf).trans_le hc
  obtain ⟨w,hw,hr⟩ := exists_orderRank_of_finite_initial hBf inter_subset_left
    (fun x hx y hy hyx => ⟨hy,hx.2.trans (heightOrder_height_le hyx)⟩) hj
  exact ⟨w,hw.1,hw.2,hr⟩

lemma heightRank_injOn {H : ℂ → ℝ} {S : Set ℂ}
    (hfin : ∀ z ∈ S, (S ∩ {w | H z ≤ H w}).Finite) : InjOn (heightRank H S) S :=
  @orderRank_injOn ℂ (heightOrder H) S (fun z hz => heightRank_pred_finite (hfin z hz))

lemma heightRank_eq_ncard (H : ℂ → ℝ) (S : Set ℂ) (z : ℂ) :
    heightRank H S z = {w | w ∈ S ∧ heightPrecedes H w z}.ncard := by
  let := heightOrder H
  rw [heightRank,orderRank]
  congr 1
  ext w
  exact and_congr_right (fun _ => heightOrder_lt_iff H w z)

lemma rankPartner_spec {H : ℂ → ℝ} {A B : Set ℂ} {z : ℂ}
    (h : ∃ w ∈ B, heightRank H B w = heightRank H A z) :
    rankPartner H A B z ∈ B ∧
      heightRank H B (rankPartner H A B z) = heightRank H A z := by
  rw [rankPartner,dite_eq_left h]
  exact h.choose_spec

lemma rankPartner_eq {H : ℂ → ℝ} {A B : Set ℂ} {z w : ℂ}
    (hri : InjOn (heightRank H B) B) (hw : w ∈ B)
    (hr : heightRank H B w = heightRank H A z) : rankPartner H A B z = w := by
  have hs := rankPartner_spec ⟨w,hw,hr⟩
  exact hri hs.1 hw (hs.2.trans hr.symm)

lemma criticalHeight_count {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) {k : ℝ} (hk : 0 < k)
    {ξ : ℂ} (hg : GoodPair f k ξ) {h : ℝ} (hh : 0 < h) :
    (positiveFiber f k ξ ∩ {z | h ≤ criticalHeight f k z}).Finite ∧
    (negativeFiber f k ξ ∩ {z | h ≤ criticalHeight f k z}).Finite ∧
    (positiveFiber f k ξ ∩ {z | h ≤ criticalHeight f k z}).ncard ≤
      (negativeFiber f k ξ ∩ {z | h ≤ criticalHeight f k z}).ncard := by
  have he : {z | z ∈ halfPlane ∧ criticalMap f k z = ξ ∧
      ENNReal.ofReal h ≤ potential f k ξ z} =
      {z | z ∈ halfPlane ∧ criticalMap f k z = ξ ∧ h ≤ criticalHeight f k z} := by
    ext z
    constructor
    · rintro ⟨hz,hG,hv⟩
      refine ⟨hz,hG,?_⟩
      rw [potential_critical_height hf hk hz hG] at hv
      exact (ENNReal.ofReal_le_ofReal_iff (criticalHeight_pos hf hk hz).le).mp hv
    · rintro ⟨hz,hG,hv⟩
      refine ⟨hz,hG,?_⟩
      rw [potential_critical_height hf hk hz hG]
      exact ENNReal.ofReal_le_ofReal hv
  have hc := critical_count hf hk hg hh
  dsimp only at hc
  rw [he] at hc
  have hp : {z ∈ {z | z ∈ halfPlane ∧ criticalMap f k z = ξ ∧ h ≤ criticalHeight f k z} |
      0 < normalizedJacobian f k z} = positiveFiber f k ξ ∩ {z | h ≤ criticalHeight f k z} := by
    ext z
    simp only [mem_ofPred_eq,mem_inter_iff,positiveFiber]
    tauto
  have hn : {z ∈ {z | z ∈ halfPlane ∧ criticalMap f k z = ξ ∧ h ≤ criticalHeight f k z} |
      normalizedJacobian f k z < 0} = negativeFiber f k ξ ∩ {z | h ≤ criticalHeight f k z} := by
    ext z
    simp only [mem_ofPred_eq,mem_inter_iff,negativeFiber]
    tauto
  refine ⟨hc.1.subset (fun z hz => ⟨hz.1.1,hz.1.2.1,hz.2⟩),
    hc.1.subset (fun z hz => ⟨hz.1.1,hz.1.2.1,hz.2⟩),?_⟩
  rw [hp,hn] at hc
  exact hc.2

lemma criticalHeight_rank_inj {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) {k : ℝ} (hk : 0 < k)
    {ξ : ℂ} (hg : GoodPair f k ξ) :
    InjOn (heightRank (criticalHeight f k) (positiveFiber f k ξ)) (positiveFiber f k ξ) ∧
    InjOn (heightRank (criticalHeight f k) (negativeFiber f k ξ)) (negativeFiber f k ξ) := by
  constructor
  · exact heightRank_injOn (fun z hz =>
      (criticalHeight_count hf hk hg (criticalHeight_pos hf hk hz.1)).1)
  · exact heightRank_injOn (fun z hz =>
      (criticalHeight_count hf hk hg (criticalHeight_pos hf hk hz.1)).2.1)

lemma exists_critical_equalRank {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) {k : ℝ} (hk : 0 < k)
    {ξ : ℂ} (hg : GoodPair f k ξ) {z : ℂ} (hz : z ∈ positiveFiber f k ξ) :
    ∃ w ∈ negativeFiber f k ξ, criticalHeight f k z ≤ criticalHeight f k w ∧
      heightRank (criticalHeight f k) (negativeFiber f k ξ) w =
        heightRank (criticalHeight f k) (positiveFiber f k ξ) z := by
  have hc := criticalHeight_count hf hk hg (criticalHeight_pos hf hk hz.1)
  exact exists_equal_heightRank hz hc.1 hc.2.1 hc.2.2

lemma criticalPair_spec {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) {k : ℝ} (hk : 0 < k)
    {z : ℂ} (hz : z ∈ halfPlane) (hJ : 0 < normalizedJacobian f k z)
    (hg : GoodPair f k (criticalMap f k z)) :
    criticalPair f k z ∈ halfPlane ∧ criticalMap f k (criticalPair f k z) = criticalMap f k z ∧
      normalizedJacobian f k (criticalPair f k z) < 0 ∧
      criticalHeight f k z ≤ criticalHeight f k (criticalPair f k z) := by
  obtain ⟨w,hw,hh,hr⟩ := exists_critical_equalRank hf hk hg ⟨hz,rfl,hJ⟩
  have he : criticalPair f k z = w := rankPartner_eq (criticalHeight_rank_inj hf hk hg).2 hw hr
  rw [he]
  exact ⟨hw.1,hw.2.1,hw.2.2,hh⟩

lemma criticalPair_injective {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) {k : ℝ} (hk : 0 < k) :
    InjOn (criticalPair f k) {z | z ∈ halfPlane ∧ 0 < normalizedJacobian f k z ∧
      GoodPair f k (criticalMap f k z)} := by
  intro z hz w hw he
  have hsz := criticalPair_spec hf hk hz.1 hz.2.1 hz.2.2
  have hsw := criticalPair_spec hf hk hw.1 hw.2.1 hw.2.2
  have hG : criticalMap f k z = criticalMap f k w := by rw [← hsz.2.1,he,hsw.2.1]
  have hri := (criticalHeight_rank_inj hf hk hz.2.2).1
  have hze := exists_critical_equalRank hf hk hz.2.2 (show z ∈ positiveFiber f k (criticalMap f k z) from ⟨hz.1,rfl,hz.2.1⟩)
  have hwe := exists_critical_equalRank hf hk hz.2.2 (show w ∈ positiveFiber f k (criticalMap f k z) from ⟨hw.1,hG.symm,hw.2.1⟩)
  have hzr := rankPartner_spec (show ∃ v ∈ negativeFiber f k (criticalMap f k z),
      heightRank (criticalHeight f k) (negativeFiber f k (criticalMap f k z)) v =
        heightRank (criticalHeight f k) (positiveFiber f k (criticalMap f k z)) z from by
    obtain ⟨v,hv,_,hr⟩ := hze; exact ⟨v,hv,hr⟩)
  have hwr := rankPartner_spec (show ∃ v ∈ negativeFiber f k (criticalMap f k z),
      heightRank (criticalHeight f k) (negativeFiber f k (criticalMap f k z)) v =
        heightRank (criticalHeight f k) (positiveFiber f k (criticalMap f k z)) w from by
    obtain ⟨v,hv,_,hr⟩ := hwe; exact ⟨v,hv,hr⟩)
  apply hri ⟨hz.1,rfl,hz.2.1⟩ ⟨hw.1,hG.symm,hw.2.1⟩
  rw [← hzr.2,← hwr.2]
  apply congrArg
  simpa only [criticalPair,← hG] using he

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.BorelPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma joint_locally_injective.{u_1} {P : Type u_1} [TopologicalSpace P]
    {F : P → ℂ → ℂ} {DF : P → ℂ → ℂ →L[ℝ] ℂ} {s : Set ℂ}
    (hs : IsOpen s) (hder : ∀ p z, z ∈ s → HasFDerivAt (F p) (DF p z) z)
    (hc : ContinuousOn (fun q : P × ℂ => DF q.1 q.2) (univ ×ˢ s))
    {p : P} {z : ℂ} (hz : z ∈ s) (he : LinearMap.det (DF p z).toLinearMap ≠ 0) :
    ∃ U : Set (P × ℂ), IsOpen U ∧ (p,z) ∈ U ∧
      InjOn (fun q : P × ℂ => (q.1,F q.1 q.2)) U := by
  let e : ℂ ≃L[ℝ] ℂ :=
    (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr he)).toContinuousLinearEquiv
  have heq : (e : ℂ →L[ℝ] ℂ) = DF p z := by
    ext v
    exact LinearMap.equivOfIsUnitDet_apply (isUnit_iff_ne_zero.mpr he) v
  let c : ℝ≥0 := ‖(e.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ / 2
  have hn : 0 < ‖(e.symm : ℂ →L[ℝ] ℂ)‖₊ := by exact_mod_cast e.symm.norm_pos
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hclt : c < ‖(e.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ := by
    dsimp [c]
    exact half_lt_self (inv_pos.mpr hn)
  have hcAt : ContinuousAt (fun q : P × ℂ => DF q.1 q.2) (p,z) := hc.continuousAt ((isOpen_univ.prod hs).mem_nhds ⟨mem_univ p,hz⟩)
  have hnb : {q : P × ℂ | q.2 ∈ s ∧ ‖DF q.1 q.2-(e : ℂ →L[ℝ] ℂ)‖₊ < c} ∈ 𝓝 (p,z) := by
    apply Filter.inter_mem
    · exact continuous_snd.continuousAt.preimage_mem_nhds (hs.mem_nhds hz)
    · exact ((hcAt.sub continuousAt_const).nnnorm).eventually
        (gt_mem_nhds (by simpa only [Pi.sub_apply,heq,sub_self,nnnorm_zero] using hcpos))
  obtain ⟨u,hu,v,hv,huv⟩ := mem_nhds_prod_iff.mp hnb
  obtain ⟨u',hu'u,hu'o,hpu⟩ := mem_nhds_iff.mp hu
  obtain ⟨r,hr,hvr⟩ := Metric.mem_nhds_iff.mp hv
  refine ⟨u' ×ˢ Metric.ball z r,hu'o.prod Metric.isOpen_ball,⟨hpu,Metric.mem_ball_self hr⟩,?_⟩
  rintro ⟨p1,z1⟩ h1 ⟨p2,z2⟩ h2 hh
  have hp : p1 = p2 := congrArg Prod.fst hh
  subst p2
  have hbound (w : ℂ) (hw : w ∈ Metric.ball z r) :
      w ∈ s ∧ ‖DF p1 w-(e : ℂ →L[ℝ] ℂ)‖₊ < c :=
    huv (show (p1,w) ∈ u ×ˢ v from ⟨hu'u h1.1,hvr hw⟩)
  have hLip : LipschitzOnWith c (fun w => F p1 w-e w) (Metric.ball z r) := by
    apply (convex_ball z r).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun w hw => ((hder p1 w (hbound w hw).1).sub e.hasFDerivAt).hasFDerivWithinAt)
    exact fun w hw => (hbound w hw).2.le
  have hInj := hLip.approximatesLinearOn.injOn (Or.inr hclt)
  exact Prod.ext rfl (hInj h1.2 h2.2 (congrArg Prod.snd hh))

lemma countable_joint_injective_partition.{u_1} {P : Type u_1} [TopologicalSpace P]
    [SecondCountableTopology P] [MeasurableSpace P] [BorelSpace P]
    {F : P → ℂ → ℂ} {DF : P → ℂ → ℂ →L[ℝ] ℂ} {s : Set ℂ}
    (hs : IsOpen s) (hder : ∀ p z, z ∈ s → HasFDerivAt (F p) (DF p z) z)
    (hc : ContinuousOn (fun q : P × ℂ => DF q.1 q.2) (univ ×ˢ s)) :
    ∃ p : ℕ → Set (P × ℂ), (∀ n, MeasurableSet (p n)) ∧
      Pairwise (Disjoint on p) ∧
      (⋃ n, p n) = {q | q.2 ∈ s ∧ LinearMap.det (DF q.1 q.2).toLinearMap ≠ 0} ∧
      ∀ n, InjOn (fun q : P × ℂ => (q.1,F q.1 q.2)) (p n) := by
  classical
  let t : Set (P × ℂ) := {q | q.2 ∈ s ∧ LinearMap.det (DF q.1 q.2).toLinearMap ≠ 0}
  have htopen : IsOpen t := by
    have h : IsOpen ((univ ×ˢ s) ∩ (fun q : P × ℂ => DF q.1 q.2) ⁻¹' {d | d.det ≠ 0}) :=
      hc.isOpen_inter_preimage (isOpen_univ.prod hs)
        (isClosed_eq ContinuousLinearMap.continuous_det continuous_const).isOpen_compl
    convert h using 1
    ext q
    simp [t]
  have hlocal (q : t) : ∃ U : Set (P × ℂ), IsOpen U ∧ q.val ∈ U ∧
      InjOn (fun q : P × ℂ => (q.1,F q.1 q.2)) U :=
    joint_locally_injective hs hder hc q.property.1 q.property.2
  choose U hUo hUq hUi using hlocal
  by_cases he : t = ∅
  · refine ⟨fun _ => ∅,by simp,by simp [Pairwise],?_,by simp⟩
    simpa using he.symm
  · have : Nonempty t := Set.nonempty_coe_sort.mpr (Set.nonempty_iff_ne_empty.mpr he)
    obtain ⟨j,hj⟩ := (show IsLindelof t from HereditarilyLindelofSpace.isLindelof t).indexed_countable_subcover
      U hUo (fun q hq => mem_iUnion.mpr ⟨⟨q,hq⟩,hUq ⟨q,hq⟩⟩)
    let q : ℕ → Set (P × ℂ) := fun n => t ∩ U (j n)
    refine ⟨disjointed q,?_,disjoint_disjointed q,?_,?_⟩
    · intro n
      exact MeasurableSet.disjointed (fun n => htopen.measurableSet.inter (hUo (j n)).measurableSet) n
    · rw [iUnion_disjointed]
      ext z
      simp only [mem_iUnion,mem_inter_iff,q]
      exact ⟨fun ⟨_,hz,_⟩ => hz,fun hz => by obtain ⟨n,hn⟩ := mem_iUnion.mp (hj hz); exact ⟨n,hz,hn⟩⟩
    · intro n
      exact (hUi (j n)).mono ((disjointed_subset q n).trans inter_subset_right)

lemma exists_borel_partial_inverse.{u_1, u_2} {X : Type u_1} {Y : Type u_2}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} {s : Set X} (hs : MeasurableSet s) (hf : ContinuousOn f s) (hi : InjOn f s) :
    ∃ b : Y → X, Measurable b ∧ MeasurableSet (f '' s) ∧
      (∀ y ∈ f '' s, b y ∈ s ∧ f (b y) = y) ∧ ∀ x ∈ s, b (f x) = x := by
  classical
  have hm := hf.measurableEmbedding hs hi
  by_cases hne : s.Nonempty
  · let : Nonempty s := Set.nonempty_coe_sort.mpr hne
    let b : Y → X := fun y => (hm.invFun y).val
    refine ⟨b,measurable_subtype_coe.comp hm.measurable_invFun,?_,?_,?_⟩
    · simpa only [Set.range_domRestrict] using hm.measurableSet_range
    · rintro y ⟨x,hx,rfl⟩
      have hb : b (f x) = x := congrArg Subtype.val (hm.leftInverse_invFun ⟨x,hx⟩)
      exact ⟨hb.symm ▸ hx,congrArg f hb⟩
    · intro x hx
      exact congrArg Subtype.val (hm.leftInverse_invFun ⟨x,hx⟩)
  · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hne
    refine ⟨fun _ => Classical.arbitrary X,measurable_const,?_,?_,?_⟩ <;> simp [he]

lemma fiber_count_eq_tsum_branches.{u_1, u_2} {X : Type u_1} {Y : Type u_2} [MeasurableSpace X] [MeasurableSingletonClass X]
    {f : X → Y} {s : Set X} {p : ℕ → Set X} {b : ℕ → Y → X}
    (hp : Pairwise (Disjoint on p)) (hu : (⋃ n, p n) = s)
    (hi : ∀ n, InjOn f (p n))
    (hb : ∀ n y, y ∈ f '' p n → b n y ∈ p n ∧ f (b n y) = y)
    (hinv : ∀ n x, x ∈ p n → b n (f x) = x)
    (R : X → Prop) (y : Y) :
    Measure.count {x | x ∈ s ∧ f x = y ∧ R x} =
      ∑' n, if y ∈ f '' p n ∧ R (b n y) then (1 : ℝ≥0∞) else 0 := by
  classical
  have he : {x | x ∈ s ∧ f x = y ∧ R x} = ⋃ n, {x | x ∈ p n ∧ f x = y ∧ R x} := by
    rw [← hu]
    ext x
    simp only [mem_ofPred_eq,mem_iUnion]
    aesop
  have hsub (n) : ({x | x ∈ p n ∧ f x = y ∧ R x} : Set X).Subsingleton := by
    intro x hx z hz
    exact hi n hx.1 hz.1 (hx.2.1.trans hz.2.1.symm)
  rw [he,measure_iUnion]
  · apply tsum_congr
    intro n
    by_cases hy : y ∈ f '' p n ∧ R (b n y)
    · rw [ite_eq_left hy]
      have hx : {x | x ∈ p n ∧ f x = y ∧ R x} = {b n y} := by
        apply Set.Subsingleton.eq_singleton_of_mem (hsub n)
        exact ⟨(hb n y hy.1).1,(hb n y hy.1).2,hy.2⟩
      rw [hx,Measure.count_singleton]
    · rw [ite_eq_right hy]
      have hx : {x | x ∈ p n ∧ f x = y ∧ R x} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        apply hy
        refine ⟨⟨x,hx.1,hx.2.1⟩,?_⟩
        rw [← hx.2.1,hinv n x hx.1]
        exact hx.2.2
      rw [hx,measure_empty]
  · exact pairwise_disjoint_mono hp (fun n => fun x hx => hx.1)
  · intro n
    exact (hsub n).countable.measurableSet

lemma measurable_fiber_count_branches.{u_1, u_2, u_3} {X : Type u_1} {Y : Type u_2} {Q : Type u_3}
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Y] [MeasurableSpace Q]
    {f : X → Y} {s : Set X} {p : ℕ → Set X} {b : ℕ → Y → X}
    (hp : Pairwise (Disjoint on p)) (hu : (⋃ n, p n) = s)
    (hi : ∀ n, InjOn f (p n)) (hbm : ∀ n, Measurable (b n))
    (hdm : ∀ n, MeasurableSet (f '' p n))
    (hb : ∀ n y, y ∈ f '' p n → b n y ∈ p n ∧ f (b n y) = y)
    (hinv : ∀ n x, x ∈ p n → b n (f x) = x)
    {R : Q → X → Prop} (hR : MeasurableSet {q : Q × X | R q.1 q.2})
    {y : Q → Y} (hy : Measurable y) :
    Measurable (fun q => Measure.count {x | x ∈ s ∧ f x = y q ∧ R q x}) := by
  classical
  have he : (fun q => Measure.count {x | x ∈ s ∧ f x = y q ∧ R q x}) =
      fun q => ∑' n, if y q ∈ f '' p n ∧ R q (b n (y q)) then (1 : ℝ≥0∞) else 0 := by
    funext q
    exact fiber_count_eq_tsum_branches hp hu hi hb hinv (R q) (y q)
  rw [he]
  apply Measurable.tsum
  intro n
  apply Measurable.ite
  · exact (hdm n |>.preimage hy).inter
      (hR.preimage (measurable_id.prodMk ((hbm n).comp hy)))
  · exact measurable_const
  · exact measurable_const

lemma measurable_branch_selection.{u_1, u_2} {Q : Type u_1} {X : Type u_2} [MeasurableSpace Q] [MeasurableSpace X]
    {b : ℕ → Q → X} {M : ℕ → Set Q} {f : Q → X}
    (hb : ∀ n, Measurable (b n)) (hM : ∀ n, MeasurableSet (M n))
    (he : ∀ q, ∃ n, q ∈ M n) (hf : ∀ n q, q ∈ M n → f q = b n q) : Measurable f := by
  intro T hT
  have hset : f ⁻¹' T = ⋃ n, M n ∩ (b n) ⁻¹' T := by
    ext q
    constructor
    · intro hq
      obtain ⟨n,hn⟩ := he q
      exact mem_iUnion.mpr ⟨n,hn,by simpa only [mem_preimage,← hf n q hn] using hq⟩
    · intro hq
      obtain ⟨n,hn,ht⟩ := mem_iUnion.mp hq
      simpa only [mem_preimage,hf n q hn] using ht
  rw [hset]
  exact MeasurableSet.iUnion (fun n => (hM n).inter (hT.preimage (hb n)))

lemma exists_borelBranches.{u_1, u_2} {X : Type u_1} {Y : Type u_2}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} {s : Set X} (hf : ContinuousOn f s)
    (hp : ∃ p : ℕ → Set X, (∀ n, MeasurableSet (p n)) ∧ Pairwise (Disjoint on p) ∧
      (⋃ n, p n) = s ∧ ∀ n, InjOn f (p n)) : Nonempty (BorelBranches f s) := by
  obtain ⟨p,hpm,hpd,hpc,hpi⟩ := hp
  have hb (n) := exists_borel_partial_inverse (hpm n)
    (hf.mono (show p n ⊆ s from hpc ▸ subset_iUnion p n)) (hpi n)
  choose b hbm him hbr hbl using hb
  exact ⟨⟨p,b,hpm,hpd,hpc,hpi,hbm,him,hbr,hbl⟩⟩

lemma BorelBranches.measurable_count.{u_1, u_2, u_3} {X : Type u_1} {Y : Type u_2} {Q : Type u_3}
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Y] [MeasurableSpace Q]
    {f : X → Y} {s : Set X} (B : BorelBranches f s)
    {R : Q → X → Prop} (hR : MeasurableSet {q : Q × X | R q.1 q.2})
    {y : Q → Y} (hy : Measurable y) :
    Measurable (fun q => Measure.count {x | x ∈ s ∧ f x = y q ∧ R q x}) :=
  measurable_fiber_count_branches B.disjoint B.cover B.injective B.measurable_branch
    B.measurable_image B.right_inv B.left_inv hR hy

lemma count_product_fiber.{u_1, u_2, u_3} {P : Type u_1} {X : Type u_2} {Y : Type u_3} [MeasurableSpace P] [MeasurableSingletonClass P]
    [MeasurableSpace X] [MeasurableSingletonClass X] (F : P → X → Y)
    (R : P × X → Prop) (p : P) (y : Y) :
    Measure.count {q : P × X | (q.1,F q.1 q.2) = (p,y) ∧ R q} =
      Measure.count {x | F p x = y ∧ R (p,x)} := by
  have he : {q : P × X | (q.1,F q.1 q.2) = (p,y) ∧ R q} =
      (fun x => (p,x)) '' {x | F p x = y ∧ R (p,x)} := by
    ext q
    constructor
    · rintro ⟨hq,hR⟩
      obtain rfl : q.1 = p := congrArg Prod.fst hq
      exact ⟨q.2,⟨congrArg Prod.snd hq,hR⟩,rfl⟩
    · rintro ⟨x,⟨hx,hR⟩,rfl⟩
      exact ⟨Prod.ext rfl hx,hR⟩
  rw [he]
  exact Measure.count_injective_image (fun _ _ h => congrArg Prod.snd h) _

lemma count_subtype_set.{u_1} {X : Type u_1} [MeasurableSpace X] [MeasurableSingletonClass X]
    (s : Set X) (R : X → Prop) :
    Measure.count {x : s | R x} = Measure.count {x : X | x ∈ s ∧ R x} := by
  rw [← Measure.count_injective_image (f := (Subtype.val : s → X)) Subtype.val_injective]
  congr 1
  ext x
  simp only [mem_image,mem_ofPred_eq,Subtype.exists,exists_prop]
  aesop

lemma continuous_jointCriticalMap (k : ℝ) : Continuous (jointCriticalMap k) :=
  continuous_fst.prodMk (continuous_class_criticalMap k)

lemma exists_class_branches (k : ℝ) : Nonempty (BorelBranches (jointCriticalMap k) (nonsingularClass k)) := by
  apply exists_borelBranches (continuous_jointCriticalMap k).continuousOn
  obtain ⟨p,hpm,hpd,hpc,hpi⟩ := countable_joint_injective_partition isOpen_halfPlane
    (fun g z hz => (differentiableAt_criticalMap (classFun_schlicht g).1 hz k).hasFDerivAt)
    (continuousOn_prod_of_continuous_subtype (F := fun g z => fderiv ℝ (criticalMap (classFun g) k) z) (continuous_class_fderiv_criticalMap k))
  let e : DiskClass × halfPlane → DiskClass × ℂ := fun q => (q.1,q.2)
  have hem : Measurable e := measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)
  let u : ℕ → Set (DiskClass × halfPlane) := fun n => e ⁻¹' p n
  refine ⟨u,fun n => (hpm n).preimage hem,?_,?_,?_⟩
  · intro n m hnm
    exact (hpd hnm).preimage e
  · ext q
    have hc : (∃ n, e q ∈ p n) ↔ (e q).2 ∈ halfPlane ∧
        LinearMap.det (fderiv ℝ (criticalMap (classFun q.1) k) q.2).toLinearMap ≠ 0 := by
      rw [← mem_iUnion,hpc]
      rfl
    simp only [mem_iUnion,mem_preimage,u]
    rw [hc]
    simp only [e,q.2.property,true_and,nonsingularClass,mem_ofPred_eq,normalizedJacobian]
    exact ((div_ne_zero_iff).trans (and_iff_left
      (pow_ne_zero _ (norm_ne_zero_iff.mpr (univalent_deriv_ne_zero isOpen_halfPlane
        (classFun_schlicht q.1).1 q.2.property))))).symm
  · intro n q hq r hr he
    have hz : e q = e r := hpi n hq hr he
    have hfst : q.1 = r.1 := congrArg (fun x : DiskClass × ℂ => x.1) hz
    have hsnd : q.2.val = r.2.val := congrArg (fun x : DiskClass × ℂ => x.2) hz
    exact Prod.ext hfst (Subtype.ext hsnd)

lemma measurableSet_classPrecedes (k : ℝ) :
    MeasurableSet {p : (DiskClass × halfPlane) × (DiskClass × halfPlane) | classPrecedes k p.1 p.2} := by
  have hH := (continuous_class_criticalHeight k).measurable
  have hr : Measurable (fun q : DiskClass × halfPlane => q.2.val.re) :=
    Complex.continuous_re.measurable.comp (measurable_subtype_coe.comp measurable_snd)
  have hi : Measurable (fun q : DiskClass × halfPlane => q.2.val.im) :=
    Complex.continuous_im.measurable.comp (measurable_subtype_coe.comp measurable_snd)
  exact (measurableSet_lt (hH.comp measurable_snd) (hH.comp measurable_fst)).union
    ((measurableSet_eq_fun (hH.comp measurable_fst) (hH.comp measurable_snd)).inter
      ((measurableSet_lt (hr.comp measurable_fst) (hr.comp measurable_snd)).union
        ((measurableSet_eq_fun (hr.comp measurable_fst) (hr.comp measurable_snd)).inter
          (measurableSet_lt (hi.comp measurable_fst) (hi.comp measurable_snd)))))

lemma measurable_classRankCount (k σ : ℝ) : Measurable (classRankCount k σ) := by
  let B := Classical.choice (exists_class_branches k)
  apply B.measurable_count _ (continuous_jointCriticalMap k).measurable
  exact (measurableSet_lt measurable_const
    (measurable_const.mul ((continuous_class_normalizedJacobian k).measurable.comp measurable_snd))).inter
    ((measurableSet_classPrecedes k).preimage measurable_swap)

lemma signedFiber_one (f : ℂ → ℂ) (k : ℝ) (ξ : ℂ) :
    signedFiber f k ξ 1 = positiveFiber f k ξ := by ext z; simp [signedFiber,positiveFiber]

lemma signedFiber_neg_one (f : ℂ → ℂ) (k : ℝ) (ξ : ℂ) :
    signedFiber f k ξ (-1) = negativeFiber f k ξ := by ext z; simp [signedFiber,negativeFiber]

lemma classRankCount_eq_count (k σ : ℝ) (q : DiskClass × halfPlane) :
    classRankCount k σ q = Measure.count {w | w ∈ signedFiber (classFun q.1) k
      (criticalMap (classFun q.1) k q.2) σ ∧ heightPrecedes (criticalHeight (classFun q.1) k) w q.2} := by
  let R : DiskClass × halfPlane → Prop := fun r =>
    0 < σ * normalizedJacobian (classFun r.1) k r.2 ∧ classPrecedes k r q
  have he : {r | r ∈ nonsingularClass k ∧ jointCriticalMap k r = jointCriticalMap k q ∧ R r} =
      {r : DiskClass × halfPlane | jointCriticalMap k r = jointCriticalMap k q ∧ R r} := by
    ext r
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_,h⟩
      intro hz
      have hp := h.2.1
      rw [hz,mul_zero] at hp
      exact lt_irrefl 0 hp
  change Measure.count {r | r ∈ nonsingularClass k ∧ jointCriticalMap k r = jointCriticalMap k q ∧ R r} = _
  rw [he]
  simp only [jointCriticalMap]
  rw [count_product_fiber (fun g (z : halfPlane) => criticalMap (classFun g) k z) R]
  change Measure.count {w : halfPlane | criticalMap (classFun q.1) k w = criticalMap (classFun q.1) k q.2 ∧
    0 < σ * normalizedJacobian (classFun q.1) k w ∧ heightPrecedes (criticalHeight (classFun q.1) k) w q.2} = _
  rw [count_subtype_set halfPlane (fun w : ℂ => criticalMap (classFun q.1) k w = criticalMap (classFun q.1) k q.2 ∧
    0 < σ * normalizedJacobian (classFun q.1) k w ∧ heightPrecedes (criticalHeight (classFun q.1) k) w q.2)]
  congr 1
  ext w
  simp only [mem_ofPred_eq,signedFiber]
  tauto

lemma classRankCount_eq_heightRank {k : ℝ} (hk : 0 < k) (σ : ℝ) (q : DiskClass × halfPlane)
    (hg : GoodPair (classFun q.1) k (criticalMap (classFun q.1) k q.2)) :
    classRankCount k σ q =
      (heightRank (criticalHeight (classFun q.1) k)
        (signedFiber (classFun q.1) k (criticalMap (classFun q.1) k q.2) σ) q.2 : ℝ≥0∞) := by
  rw [classRankCount_eq_count,heightRank_eq_ncard]
  have hpos := criticalHeight_pos (classFun_schlicht q.1).1 hk q.2.property
  have hc := critical_count (classFun_schlicht q.1).1 hk hg hpos
  have hf : {w | w ∈ signedFiber (classFun q.1) k (criticalMap (classFun q.1) k q.2) σ ∧
      heightPrecedes (criticalHeight (classFun q.1) k) w q.2}.Finite := by
    apply hc.1.subset
    intro w hw
    refine ⟨hw.1.1,hw.1.2.1,?_⟩
    rw [potential_critical_height (classFun_schlicht q.1).1 hk hw.1.1 hw.1.2.1]
    apply ENNReal.ofReal_le_ofReal
    exact heightOrder_height_le ((heightOrder_lt_iff _ _ _).mpr hw.2)
  rw [Measure.count_apply_finite _ hf,← Set.ncard_eq_toFinset_card _ hf]

lemma heightRank_transport_on {H H' : ℂ → ℝ} {S S' : Set ℂ} (e : ℂ ≃ ℂ)
    (hS : ∀ w, w ∈ S' ↔ e w ∈ S) (z : ℂ)
    (hord : ∀ w ∈ S', heightPrecedes H' w z ↔ heightPrecedes H (e w) (e z)) :
    heightRank H' S' z = heightRank H S (e z) := by
  rw [heightRank_eq_ncard,heightRank_eq_ncard]
  apply Set.ncard_congr (fun w _ => e w)
  · intro w hw
    exact ⟨(hS w).mp hw.1,(hord w hw.1).mp hw.2⟩
  · intro a b _ _ hab
    exact e.injective hab
  · intro w hw
    have hm : e.symm w ∈ S' := (hS _).mpr (by simpa using hw.1)
    exact ⟨e.symm w,⟨hm,(hord _ hm).mpr (by simpa using hw.2)⟩,e.apply_symm_apply w⟩

lemma heightPrecedes_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) (k : ℝ)
    {t z w : ℂ} (ht : t ∈ halfPlane) (hz : z ∈ halfPlane) (hw : w ∈ halfPlane) :
    heightPrecedes (criticalHeight (reroot f t) k) z w ↔
      heightPrecedes (criticalHeight f k) (affine t z) (affine t w) := by
  have hc := heightScaleInverse_pos hf k ht
  have hre (v : ℂ) : (affine t v).re = t.re+t.im*v.re := by simp [affine]
  have him (v : ℂ) : (affine t v).im = t.im*v.im := by simp [affine]
  simp only [heightPrecedes,criticalHeight_reroot hf k ht hz,criticalHeight_reroot hf k ht hw,
    div_lt_div_iff_of_pos_right hc,div_left_inj' (ne_of_gt hc),hre,him,
    add_lt_add_iff_left,add_right_inj,mul_lt_mul_iff_right₀ (show 0 < t.im from ht),mul_right_inj' (ne_of_gt (show 0 < t.im from ht))]

lemma signedFiber_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) {k : ℝ} (hk : 0 < k)
    {t : ℂ} (ht : t ∈ halfPlane) (ξ : ℂ) (σ : ℝ) (w : ℂ) :
    w ∈ signedFiber (reroot f t) k (rerootTarget f t ξ) σ ↔
      affine t w ∈ signedFiber f k ξ σ := by
  simp only [signedFiber,mem_ofPred_eq,affine_mem_iff ht]
  apply and_congr_right
  intro hw
  rw [criticalMap_reroot_fiber hf k ht hw,normalizedJacobian_reroot hf ht hw k (ne_of_gt hk)]

lemma heightRank_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) {k : ℝ} (hk : 0 < k)
    {t z : ℂ} (ht : t ∈ halfPlane) (hz : z ∈ halfPlane) (ξ : ℂ) (σ : ℝ) :
    heightRank (criticalHeight (reroot f t) k) (signedFiber (reroot f t) k (rerootTarget f t ξ) σ) z =
      heightRank (criticalHeight f k) (signedFiber f k ξ σ) (affine t z) := by
  apply heightRank_transport_on (affineHome t ht).toEquiv
    (signedFiber_reroot hf hk ht ξ σ) z
  intro w hw
  exact heightPrecedes_reroot hf k ht hw.1 hz

lemma criticalPair_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane) {k : ℝ} (hk : 0 < k)
    {t z : ℂ} (ht : t ∈ halfPlane) (hz : z ∈ halfPlane)
    (hJ : 0 < normalizedJacobian f k (affine t z))
    (hg : GoodPair f k (criticalMap f k (affine t z))) :
    affine t (criticalPair (reroot f t) k z) = criticalPair f k (affine t z) := by
  let f' := reroot f t
  have hf' : UnivalentOn f' halfPlane := (reroot_normalized hf ht).1
  have hG : criticalMap f' k z = rerootTarget f t (criticalMap f k (affine t z)) :=
    criticalMap_reroot hf ht hz k
  have hg' : GoodPair f' k (criticalMap f' k z) := by
    rw [hG]
    exact (goodPair_reroot hf hk ht _).mpr hg
  have hJ' : 0 < normalizedJacobian f' k z := by
    rw [normalizedJacobian_reroot hf ht hz k (ne_of_gt hk)]
    exact hJ
  have hs := criticalPair_spec hf' hk hz hJ' hg'
  have hr := rankPartner_spec (show ∃ w ∈ negativeFiber f' k (criticalMap f' k z),
      heightRank (criticalHeight f' k) (negativeFiber f' k (criticalMap f' k z)) w =
        heightRank (criticalHeight f' k) (positiveFiber f' k (criticalMap f' k z)) z from by
    obtain ⟨w,hw,_,he⟩ := exists_critical_equalRank hf' hk hg' ⟨hz,rfl,hJ'⟩
    exact ⟨w,hw,he⟩)
  have hr' : heightRank (criticalHeight f k)
      (negativeFiber f k (criticalMap f k (affine t z))) (affine t (criticalPair f' k z)) =
      heightRank (criticalHeight f k) (positiveFiber f k (criticalMap f k (affine t z))) (affine t z) := by
    have h := hr.2
    change heightRank (criticalHeight f' k) (negativeFiber f' k (criticalMap f' k z)) (criticalPair f' k z) = _ at h
    rw [← signedFiber_neg_one,← signedFiber_one,hG,
      heightRank_reroot hf hk ht hs.1 _ (-1),heightRank_reroot hf hk ht hz _ 1,
      signedFiber_neg_one,signedFiber_one] at h
    exact h
  have hm : affine t (criticalPair f' k z) ∈ negativeFiber f k (criticalMap f k (affine t z)) := by
    rw [← signedFiber_neg_one,← signedFiber_reroot hf hk ht _ (-1),← hG,signedFiber_neg_one]
    exact ⟨hs.1,hs.2.1,hs.2.2.1⟩
  exact (rankPartner_eq (criticalHeight_rank_inj hf hk hg).2 hm hr').symm

lemma heightRank_congr_on {H H' : ℂ → ℝ} {S : Set ℂ} (hS : S ⊆ halfPlane)
    (he : EqOn H H' halfPlane) {z : ℂ} (hz : z ∈ halfPlane) :
    heightRank H S z = heightRank H' S z := by
  rw [heightRank_eq_ncard,heightRank_eq_ncard]
  congr 1
  ext w
  apply and_congr_right
  intro hw
  simp only [heightPrecedes,he hz,he (hS hw)]

lemma signedFiber_congr {f g : ℂ → ℂ} (he : EqOn f g halfPlane) (k : ℝ) (ξ : ℂ) (σ : ℝ) :
    signedFiber f k ξ σ = signedFiber g k ξ σ := by
  ext z
  simp only [signedFiber,mem_ofPred_eq]
  apply and_congr_right
  intro hz
  rw [criticalMap_congr he k hz,normalizedJacobian_congr he k hz]

lemma criticalPair_congr {f g : ℂ → ℂ} (hf : UnivalentOn f halfPlane) (hg : UnivalentOn g halfPlane)
    (he : EqOn f g halfPlane) {k : ℝ} (hk : 0 < k) {z : ℂ} (hz : z ∈ halfPlane)
    (hJ : 0 < normalizedJacobian f k z) (hgood : GoodPair f k (criticalMap f k z)) :
    criticalPair f k z = criticalPair g k z := by
  have hG := criticalMap_congr he k hz
  have hgood' : GoodPair g k (criticalMap g k z) := by
    rw [← hG]
    exact (goodPair_congr he k _).mp hgood
  have hs := criticalPair_spec hf hk hz hJ hgood
  have hr := rankPartner_spec (show ∃ w ∈ negativeFiber f k (criticalMap f k z),
      heightRank (criticalHeight f k) (negativeFiber f k (criticalMap f k z)) w =
        heightRank (criticalHeight f k) (positiveFiber f k (criticalMap f k z)) z from by
    obtain ⟨w,hw,_,hr⟩ := exists_critical_equalRank hf hk hgood ⟨hz,rfl,hJ⟩
    exact ⟨w,hw,hr⟩)
  have hneg : negativeFiber f k (criticalMap f k z) = negativeFiber g k (criticalMap g k z) := by
    rw [← signedFiber_neg_one,← signedFiber_neg_one,signedFiber_congr he,hG]
  have hpos : positiveFiber f k (criticalMap f k z) = positiveFiber g k (criticalMap g k z) := by
    rw [← signedFiber_one,← signedFiber_one,signedFiber_congr he,hG]
  have hr' := hr.2
  change heightRank (criticalHeight f k) (negativeFiber f k (criticalMap f k z)) (criticalPair f k z) = _ at hr'
  rw [heightRank_congr_on (fun w hw => hw.1) (criticalHeight_congr he k) hs.1,
    heightRank_congr_on (fun w hw => hw.1) (criticalHeight_congr he k) hz,hneg,hpos] at hr'
  exact (rankPartner_eq (criticalHeight_rank_inj hg hk hgood').2 (hneg ▸ hr.1) hr').symm

lemma class_normalizedJacobian_reroot (g : DiskClass) {k : ℝ} (hk : 0 < k)
    (t w : halfPlane) :
    normalizedJacobian (classFun (rerootClass g t)) k w =
      normalizedJacobian (classFun g) k (affine t w) := by
  rw [normalizedJacobian_congr (classFun_rerootClass g t) k w.property,
    normalizedJacobian_reroot (classFun_schlicht g).1 t.property w.property k (ne_of_gt hk)]

lemma class_goodPair_reroot (g : DiskClass) {k : ℝ} (hk : 0 < k) (t w : halfPlane) :
    GoodPair (classFun (rerootClass g t)) k
        (criticalMap (classFun (rerootClass g t)) k w) ↔
      GoodPair (classFun g) k (criticalMap (classFun g) k (affine t w)) := by
  rw [criticalMap_congr (classFun_rerootClass g t) k w.property,
    goodPair_congr (classFun_rerootClass g t) k,
    criticalMap_reroot (classFun_schlicht g).1 t.property w.property k]
  exact goodPair_reroot (classFun_schlicht g).1 hk t.property _

lemma class_criticalPair_reroot (g : DiskClass) {k : ℝ} (hk : 0 < k) (t w : halfPlane)
    (hj : 0 < normalizedJacobian (classFun g) k (affine t w))
    (hg : GoodPair (classFun g) k (criticalMap (classFun g) k (affine t w))) :
    affine t (criticalPair (classFun (rerootClass g t)) k w) =
      criticalPair (classFun g) k (affine t w) := by
  have hj' : 0 < normalizedJacobian (classFun (rerootClass g t)) k w := by
    rw [class_normalizedJacobian_reroot g hk t w]; exact hj
  have hg' := (class_goodPair_reroot g hk t w).mpr hg
  rw [criticalPair_congr (classFun_schlicht (rerootClass g t)).1
      (reroot_normalized (classFun_schlicht g).1 t.property).1
      (classFun_rerootClass g t) hk w.property hj' hg']
  exact criticalPair_reroot (classFun_schlicht g).1 hk t.property w.property hj hg

lemma class_normalizedJacobian_root (g : DiskClass) {k : ℝ} (hk : 0 < k) (z : halfPlane) :
    normalizedJacobian (classFun (rerootClass g z)) k Complex.I =
      normalizedJacobian (classFun g) k z := by
  simpa only [halfOne,affine_I] using class_normalizedJacobian_reroot g hk z halfOne

lemma class_goodPair_root (g : DiskClass) {k : ℝ} (hk : 0 < k) (z : halfPlane) :
    GoodPair (classFun (rerootClass g z)) k
        (criticalMap (classFun (rerootClass g z)) k Complex.I) ↔
      GoodPair (classFun g) k (criticalMap (classFun g) k z) := by
  simpa only [halfOne,affine_I] using class_goodPair_reroot g hk z halfOne

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.AreaTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma BorelBranches.fiberSum_eq.{u_1, u_2} {X : Type u_1} {Y : Type u_2} [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} {s : Set X} (B : BorelBranches f s) (u : X → ℝ≥0∞) (y : Y) :
    fiberSum f s u y = ∑' n, (f '' B.part n).indicator (fun y => u (B.branch n y)) y := by
  classical
  have he : {x | x ∈ s ∧ f x = y} = ⋃ n, {x | x ∈ B.part n ∧ f x = y} := by
    ext x
    simp only [mem_ofPred_eq]
    rw [show x ∈ s ↔ x ∈ ⋃ n, B.part n from by rw [B.cover]]
    simp only [mem_ofPred_eq,mem_iUnion]
    aesop
  rw [fiberSum,he,ENNReal.tsum_biUnion]
  · apply tsum_congr
    intro n
    by_cases hy : y ∈ f '' B.part n
    · have hx : {x | x ∈ B.part n ∧ f x = y} = {B.branch n y} := by
        ext x
        constructor
        · intro hx
          exact mem_singleton_iff.mpr (B.injective n hx.1 (B.right_inv n y hy).1
            (hx.2.trans (B.right_inv n y hy).2.symm))
        · rintro rfl
          exact B.right_inv n y hy
      rw [hx,tsum_singleton,indicator_of_mem hy]
    · have hx : {x | x ∈ B.part n ∧ f x = y} = ∅ := by
        exact eq_empty_iff_forall_notMem.mpr (fun x hx => hy ⟨x,hx.1,hx.2⟩)
      simp [hx,hy]
  · intro n _ m _ hnm
    exact (B.disjoint hnm).mono (fun _ h => h.1) (fun _ h => h.1)

lemma BorelBranches.measurable_fiberSum.{u_1, u_2} {X : Type u_1} {Y : Type u_2} [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} {s : Set X} (B : BorelBranches f s) {u : X → ℝ≥0∞} (hu : Measurable u) :
    Measurable (fiberSum f s u) := by
  have he := funext (B.fiberSum_eq u)
  rw [he]
  exact Measurable.tsum (fun n => (hu.comp (B.measurable_branch n)).indicator (B.measurable_image n))

lemma weighted_area_formula_regular {f : ℂ → ℂ} {s : Set ℂ}
    (hs : MeasurableSet s) (hf : ∀ z ∈ s, ContDiffAt ℝ 1 f z)
    (hreg : ∀ z ∈ s, LinearMap.det (fderiv ℝ f z).toLinearMap ≠ 0)
    {u : ℂ → ℝ≥0∞} (hu : Measurable u) :
    Measurable (fiberSum f s u) ∧
    (∫⁻ z in s, ENNReal.ofReal |LinearMap.det (fderiv ℝ f z).toLinearMap| * u z) =
      ∫⁻ y, fiberSum f s u y := by
  let B := Classical.choice (exists_borelBranches
    (fun z hz => (hf z hz).continuousAt.continuousWithinAt)
    (exists_countable_injective_partition hs hf hreg))
  have hsub (n : ℕ) : B.part n ⊆ s := fun z hz => by rw [← B.cover]; exact mem_iUnion.mpr ⟨n,hz⟩
  have hder (n : ℕ) (z : ℂ) (hz : z ∈ B.part n) :
      HasFDerivWithinAt f (fderiv ℝ f z) (B.part n) z :=
    ((hf z (hsub n hz)).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  refine ⟨B.measurable_fiberSum hu,?_⟩
  calc
    (∫⁻ z in s, ENNReal.ofReal |LinearMap.det (fderiv ℝ f z).toLinearMap| * u z) =
        ∑' n, ∫⁻ z in B.part n, ENNReal.ofReal |LinearMap.det (fderiv ℝ f z).toLinearMap| * u z := by
      conv_lhs => rw [← B.cover]
      exact lintegral_iUnion B.measurable_part B.disjoint _
    _ = ∑' n, ∫⁻ y in f '' B.part n, u (B.branch n y) := by
      apply tsum_congr
      intro n
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (B.measurable_part n) (hder n) (B.injective n)]
      apply setLIntegral_congr_fun (B.measurable_part n)
      intro z hz
      dsimp only
      rw [B.left_inv n z hz]
    _ = ∫⁻ y, fiberSum f s u y := by
      rw [funext (B.fiberSum_eq u),lintegral_tsum]
      · exact tsum_congr (fun n => (lintegral_indicator (B.measurable_image n) _).symm)
      · exact fun n => ((hu.comp (B.measurable_branch n)).indicator (B.measurable_image n)).aemeasurable

lemma fiberSum_mono_injective.{u_1, u_2} {X : Type u_1} {Y : Type u_2} {f : X → Y} {s t : Set X} {u v : X → ℝ≥0∞}
    (R : X → X) (y : Y)
    (hR : ∀ x ∈ s, f x = y → R x ∈ t ∧ f (R x) = y)
    (hinj : InjOn R {x | x ∈ s ∧ f x = y})
    (hle : ∀ x ∈ s, f x = y → u x ≤ v (R x)) :
    fiberSum f s u y ≤ fiberSum f t v y := by
  let e : {x | x ∈ s ∧ f x = y} → {x | x ∈ t ∧ f x = y} := fun x =>
    ⟨R x,hR x x.property.1 x.property.2⟩
  have hi : Injective e := fun a b h => Subtype.ext
    (hinj a.property b.property (congrArg Subtype.val h))
  exact ENNReal.summable.tsum_le_tsum_of_inj e hi (fun _ _ => zero_le)
    (fun x => hle x x.property.1 x.property.2) ENNReal.summable

lemma contDiffAt_criticalMap {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z : ℂ} (hz : z ∈ halfPlane) (k : ℝ) : ContDiffAt ℝ 1 (criticalMap f k) z := by
  have han : AnalyticAt ℂ f z := hf.1.analyticOnNhd isOpen_halfPlane z hz
  have hc : ContDiffAt ℝ 1 (fun w : ℂ => (w.im : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z Complex.imCLM.contDiff.contDiffAt
  exact (han.contDiffAt.restrict_scalars ℝ).sub
    ((contDiffAt_const.mul hc).mul (han.deriv.contDiffAt.restrict_scalars ℝ))

lemma measurableSet_halfPlane_pred (P : ℂ → Prop)
    (hP : MeasurableSet {z : halfPlane | P z}) :
    MeasurableSet {z : ℂ | z ∈ halfPlane ∧ P z} := by
  have h := isOpen_halfPlane.measurableSet.subtype_image hP
  convert h using 1
  ext z
  simp only [mem_ofPred_eq,mem_image,Subtype.exists,exists_prop]
  aesop

lemma measurableSet_jacobianRegion (g : DiskClass) (k σ : ℝ) :
    MeasurableSet (jacobianRegion g k σ) := by
  apply measurableSet_halfPlane_pred
  exact measurableSet_lt measurable_const
    (measurable_const.mul (((continuous_class_normalizedJacobian k).comp
      (continuous_const.prodMk continuous_id)).measurable))

lemma jacobianRegion_regular (g : DiskClass) (k σ : ℝ) {z : ℂ}
    (hz : z ∈ jacobianRegion g k σ) :
    LinearMap.det (fderiv ℝ (criticalMap (classFun g) k) z).toLinearMap ≠ 0 := by
  intro hzero
  have h := hz.2
  simp only [normalizedJacobian,hzero,zero_div,mul_zero] at h
  exact lt_irrefl 0 h

attribute [local irreducible] classWeight

lemma measurable_targetDensity (g : DiskClass) (β : ℝ) : Measurable (targetDensity g β) := by
  have hc : ContinuousOn (fun z : ℂ => ENNReal.ofReal (z.im^(β-1)*‖reciprocalDeriv (classFun g) z‖^4)) halfPlane := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hm : Continuous (fun z : halfPlane => (g,z)) := continuous_const.prodMk continuous_id
    have hq : Continuous (fun z : halfPlane => classWeight g z) := continuous_classWeight.comp hm
    have hp : Continuous (fun z : halfPlane => z.val.im^(β-1)) :=
      (Complex.continuous_im.comp continuous_subtype_val).rpow_const (fun z => Or.inl (ne_of_gt z.property))
    convert ENNReal.continuous_ofReal.comp (hp.mul (hq.pow 2)) using 1
    funext z
    simp only [domRestrict_apply,Function.comp_apply,Pi.mul_apply,Pi.pow_apply,classWeight,← pow_mul]
  exact hc.measurable_piecewise continuousOn_const isOpen_halfPlane.measurableSet

lemma transportDensity_jacobian (g : DiskClass) (β k σ : ℝ) (hσ : |σ| = 1)
    {z : ℂ} (hz : z ∈ jacobianRegion g k σ) :
    transportDensity g β z * ENNReal.ofReal (σ * normalizedJacobian (classFun g) k z) =
      ENNReal.ofReal |LinearMap.det (fderiv ℝ (criticalMap (classFun g) k) z).toLinearMap| * targetDensity g β z := by
  have hD : 0 < ‖deriv (classFun g) z‖ := norm_pos_iff.mpr
    (univalent_deriv_ne_zero isOpen_halfPlane (classFun_schlicht g).1 hz.1)
  have habs : |normalizedJacobian (classFun g) k z| = σ * normalizedJacobian (classFun g) k z := by
    rw [← one_mul |normalizedJacobian (classFun g) k z|,← hσ,← abs_mul,abs_of_pos hz.2]
  have hdet : |LinearMap.det (fderiv ℝ (criticalMap (classFun g) k) z).toLinearMap| =
      ‖deriv (classFun g) z‖^2 * (σ * normalizedJacobian (classFun g) k z) := by
    rw [← habs,normalizedJacobian,abs_div,abs_pow,abs_norm]
    field_simp
  rw [transportDensity,targetDensity,indicator_of_mem hz.1,hdet]
  simp only [reciprocalDeriv,norm_inv]
  rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hz.1.le _) (sq_nonneg _)),
    ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) hz.2.le)]
  congr 1
  field_simp

lemma transport_area (g : DiskClass) (β k σ : ℝ) (hσ : |σ| = 1)
    {h : ℂ → ℝ≥0∞} (hm : Measurable h) :
    (∫⁻ z in halfPlane, transportDensity g β z *
      ENNReal.ofReal (σ * normalizedJacobian (classFun g) k z) * h z) =
    ∫⁻ ξ, fiberSum (criticalMap (classFun g) k) (jacobianRegion g k σ)
      (fun z => targetDensity g β z*h z) ξ := by
  have hs := measurableSet_jacobianRegion g k σ
  have he := (weighted_area_formula_regular hs
    (fun z hz => contDiffAt_criticalMap (classFun_schlicht g).1 hz.1 k)
    (fun z hz => jacobianRegion_regular g k σ hz)
    ((measurable_targetDensity g β).mul hm)).2
  refine Eq.trans ?_ he
  have hzero : (fun z => transportDensity g β z *
      ENNReal.ofReal (σ * normalizedJacobian (classFun g) k z) * h z) =ᶠ[ae (volume.restrict halfPlane)]
      (jacobianRegion g k σ).indicator (fun z => transportDensity g β z *
        ENNReal.ofReal (σ * normalizedJacobian (classFun g) k z) * h z) := by
    filter_upwards [ae_restrict_mem isOpen_halfPlane.measurableSet] with z hz
    by_cases hj : 0 < σ * normalizedJacobian (classFun g) k z
    · rw [indicator_of_mem (show z ∈ jacobianRegion g k σ from ⟨hz,hj⟩)]
    · rw [indicator_of_notMem (show z ∉ jacobianRegion g k σ from fun h => hj h.2),
        ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hj),mul_zero,zero_mul]
  rw [lintegral_congr_ae hzero,lintegral_indicator hs,Measure.restrict_restrict hs]
  have hinter : jacobianRegion g k σ ∩ halfPlane = jacobianRegion g k σ :=
    inter_eq_left.mpr (fun z hz => hz.1)
  rw [hinter]
  apply setLIntegral_congr_fun hs
  intro z hz
  dsimp only
  rw [transportDensity_jacobian g β k σ hσ hz,mul_assoc]
  rfl

lemma targetDensity_eq_height (g : DiskClass) {β k : ℝ} (hk : 0 < k)
    (hb : β-1 = 4*(k-1)) {z : ℂ} (hz : z ∈ halfPlane) :
    targetDensity g β z = ENNReal.ofReal ((criticalHeight (classFun g) k z/k)^4) := by
  rw [targetDensity,indicator_of_mem hz,criticalHeight,hb,mul_comm (4 : ℝ),Real.rpow_mul hz.le]
  congr 1
  simp only [Real.rpow_ofNat]
  field_simp

lemma targetDensity_le_pair (g : DiskClass) {β k : ℝ} (hk : 0 < k)
    (hb : β-1 = 4*(k-1)) {z : ℂ} (hz : z ∈ halfPlane)
    (hJ : 0 < normalizedJacobian (classFun g) k z)
    (hg : GoodPair (classFun g) k (criticalMap (classFun g) k z)) :
    targetDensity g β z ≤ targetDensity g β (criticalPair (classFun g) k z) := by
  have hs := criticalPair_spec (classFun_schlicht g).1 hk hz hJ hg
  rw [targetDensity_eq_height g hk hb hz,targetDensity_eq_height g hk hb hs.1]
  apply ENNReal.ofReal_le_ofReal
  gcongr
  · exact div_nonneg (criticalHeight_pos (classFun_schlicht g).1 hk hz).le hk.le
  · exact hs.2.2.2

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.BoundaryTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight

lemma measurable_diskCayley : Measurable diskCayley :=
  (measurable_id.sub_const _).div (measurable_id.add_const _)

lemma measurableSet_outsideCore : MeasurableSet outsideCore :=
  isOpen_halfPlane.measurableSet.inter (measurableSet_le measurable_const measurable_diskCayley.norm)

lemma classFun_lower_outsideCore (g : DiskClass) {z : ℂ} (hz : z ∈ outsideCore) :
    (1/16 : ℝ) ≤ ‖classFun g z‖ := by
  have hl := schlicht_lower_growth g.2 (diskCayley_maps hz.1)
  have he : ‖classFun g z‖ = 2*‖diskExtend g.1 (diskCayley z)‖ := by
    simp [classFun,diskToHalf]
  rw [he]
  have hm := hz.2
  linarith

lemma classFun_ne_zero_outsideCore (g : DiskClass) {z : ℂ} (hz : z ∈ outsideCore) :
    classFun g z ≠ 0 := by
  exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le (by norm_num) (classFun_lower_outsideCore g hz)))

attribute [local irreducible] classFun

lemma measurable_planeClassValue : Measurable (fun p : DiskClass × ℂ => planeClassValue p.1 p.2) := by
  classical
  let s : Set (DiskClass × ℂ) := Prod.snd ⁻¹' halfPlane
  have hc : Continuous (fun p : s => classFun p.val.1 p.val.2) := by
    exact continuous_classFun_eval.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun p => p.2)))
  simpa only [planeClassValue,s,Set.mem_preimage,dite_eq_ite] using
    hc.measurable.dite (measurable_const (a := (0 : ℂ)))
      (isOpen_halfPlane.measurableSet.preimage measurable_snd)

lemma planeClassValue_eq (g : DiskClass) {z : ℂ} (hz : z ∈ halfPlane) :
    planeClassValue g z = classFun g z := by simp [planeClassValue,hz]

lemma integral_closedBall_translate.{u_1} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (z : ℂ) (r : ℝ) :
    (∫ w in Metric.closedBall (0 : ℂ) r, f (w+z)) = ∫ w in Metric.closedBall z r, f w := by
  have he : (fun w : ℂ => w+z) ⁻¹' Metric.closedBall z r = Metric.closedBall 0 r := by
    ext w
    simp [Metric.mem_closedBall,dist_eq_norm]
  rw [← he]
  exact (measurePreserving_add_right volume z).setIntegral_preimage_emb
    (Homeomorph.addRight z).measurableEmbedding f _

lemma volume_real_closedBall_complex (z : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (Metric.closedBall z r) = Real.pi*r^2 := by
  rw [measureReal_def,Complex.volume_closedBall,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr]
  simp only [ENNReal.coe_toReal,NNReal.coe_real_pi]
  ring

lemma holomorphic_sq_submean_center {f : ℂ → ℂ} {z : ℂ} {R r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball z R)) (hr : 0 < r) (hrR : r < R) :
    Real.pi*r^2*‖f z‖^2 ≤ ∫ w in Metric.closedBall z r, ‖f w‖^2 := by
  have hfd : DifferentiableOn ℂ (fun w => f (w+z)) (Metric.ball 0 R) := by
    apply hf.comp (differentiable_id.add_const z).differentiableOn
    intro w hw
    simpa [Metric.mem_ball,dist_eq_norm] using hw
  have hh := holomorphic_sq_submean hfd hr hrR
  rw [integral_closedBall_translate (fun w => ‖f w‖^2) z r] at hh
  simpa only [volume_real_closedBall_complex 0 hr.le,zero_add] using hh

lemma holomorphic_sq_submean_lintegral {f : ℂ → ℂ} {z : ℂ} {R r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball z R)) (hr : 0 < r) (hrR : r < R) :
    ENNReal.ofReal (Real.pi*r^2*‖f z‖^2) ≤
      ∫⁻ w in Metric.closedBall z r, ENNReal.ofReal (‖f w‖^2) := by
  have hi : IntegrableOn (fun w => ‖f w‖^2) (Metric.closedBall z r) volume := ((hf.continuousOn.mono (Metric.closedBall_subset_ball hrR)).norm.pow 2).integrableOn_compact
    (isCompact_closedBall z r)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (holomorphic_sq_submean_center hf hr hrR)

lemma finite_density_compact_tail (s : Set ℂ) (b : ℂ → ℝ≥0∞)
    (hf : (∫⁻ z in s, b z) < ∞) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : Set ℂ, IsCompact K ∧ (∫⁻ z in s \ K, b z) < ε := by
  let ν := (volume.restrict s).withDensity b
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity hf.ne
  obtain ⟨K,hKsub,hK,hKε⟩ := (MeasurableSet.univ (α := ℂ)).exists_isCompact_sdiff_lt
    (μ := ν) (measure_ne_top ν univ) hε.ne'
  refine ⟨K,hK,?_⟩
  have he : ν (univ \ K) = ∫⁻ z in s \ K, b z := by
    dsimp only [ν]
    have heK : (univ \ K : Set ℂ) = Kᶜ := by ext z; simp
    rw [heK]
    rw [withDensity_apply _ hK.isClosed.measurableSet.compl]
    rw [Measure.restrict_restrict hK.isClosed.measurableSet.compl]
    have hsK : Kᶜ ∩ s = s \ K := by ext z; simp [and_comm]
    rw [hsK]
  rwa [he] at hKε

lemma weighted_holomorphic_tail {q : ℂ → ℂ} {s : Set ℂ} {a R₀ : ℝ}
    (ha : 0 ≤ a) (hR₀ : 0 ≤ R₀)
    (hs : ∀ z : ℂ, 0 < z.im → R₀ < ‖z‖ → z ∈ s)
    (hq : ∀ z ∈ s, DifferentiableAt ℂ q z)
    (hfin : (∫⁻ z in s, ENNReal.ofReal (z.im^a*‖q z‖^2)) < ∞) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, 0 < z.im → R ≤ ‖z‖ →
      z.im^(a+2)*‖q z‖^2 < ε := by
  intro ε hε
  let C : ℝ := 16*(2 : ℝ)^a/Real.pi
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨K,hK,hKε⟩ := finite_density_compact_tail s
    (fun z => ENNReal.ofReal (z.im^a*‖q z‖^2)) hfin
    (ENNReal.ofReal_pos.mpr (div_pos hε hC))
  obtain ⟨M,hM⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨2*(max R₀ M+1),fun z hy hz => ?_⟩
  have hn : 0 < ‖z‖ := by nlinarith [le_max_left R₀ M]
  have hball (w : ℂ) (hw : w ∈ Metric.ball z (z.im/2)) :
      0 < w.im ∧ R₀ < ‖w‖ ∧ w ∉ K := by
    have hd : ‖w-z‖ < z.im/2 := by simpa only [Metric.mem_ball,dist_eq_norm] using hw
    have hi := Complex.abs_im_le_norm (w-z)
    have him : z.im/2 < w.im := by
      rw [Complex.sub_im] at hi
      have hl := neg_le_of_abs_le hi
      linarith
    have himz : z.im ≤ ‖z‖ := (le_abs_self _).trans (Complex.abs_im_le_norm z)
    have hnw := norm_sub_norm_le z w
    have hdist : ‖z-w‖ = ‖w-z‖ := norm_sub_rev z w
    rw [hdist] at hnw
    have hnw' : max R₀ M < ‖w‖ := by nlinarith
    refine ⟨by linarith,lt_of_le_of_lt (le_max_left _ _) hnw',?_⟩
    intro hwK
    have hm := hM hwK
    simp only [Metric.mem_closedBall,dist_zero_right] at hm
    exact (not_lt_of_ge (hm.trans (le_max_right _ _))) hnw'
  have hhol : DifferentiableOn ℂ q (Metric.ball z (z.im/2)) := fun w hw =>
    (hq w (hs w (hball w hw).1 (hball w hw).2.1)).differentiableWithinAt
  have hsmall : Metric.closedBall z (z.im/4) ⊆ Metric.ball z (z.im/2) :=
    Metric.closedBall_subset_ball (by linarith)
  have hsub : Metric.closedBall z (z.im/4) ⊆ s \ K := by
    intro w hw
    obtain ⟨hwi,hwn,hwK⟩ := hball w (hsmall hw)
    exact ⟨hs w hwi hwn,hwK⟩
  have hmean := holomorphic_sq_submean_lintegral hhol (by linarith : 0 < z.im/4) (by linarith)
  have hcomp (w : ℂ) (hw : w ∈ Metric.closedBall z (z.im/4)) :
      z.im^a*‖q w‖^2 ≤ (2 : ℝ)^a*(w.im^a*‖q w‖^2) := by
    have hwi := (hball w (hsmall hw)).1
    have hd : ‖w-z‖ ≤ z.im/4 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hw
    have hi := Complex.abs_im_le_norm (w-z)
    rw [Complex.sub_im] at hi
    have hl := neg_le_of_abs_le hi
    have hle : z.im ≤ 2*w.im := by linarith
    have hh := Real.rpow_le_rpow hy.le hle ha
    rw [Real.mul_rpow (by norm_num) hwi.le] at hh
    nlinarith [sq_nonneg ‖q w‖]
  have hweighted : ENNReal.ofReal (z.im^a)*(∫⁻ w in Metric.closedBall z (z.im/4), ENNReal.ofReal (‖q w‖^2)) ≤
      ENNReal.ofReal ((2 : ℝ)^a)*(∫⁻ w in s \ K, ENNReal.ofReal (w.im^a*‖q w‖^2)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply le_trans ?_ (lintegral_mono_set hsub)
    apply setLIntegral_mono' measurableSet_closedBall
    intro w hw
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hy.le _),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
    exact ENNReal.ofReal_le_ofReal (hcomp w hw)
  have hineq : ENNReal.ofReal (z.im^(a+2)*‖q z‖^2) ≤
      ENNReal.ofReal C*(∫⁻ w in s \ K, ENNReal.ofReal (w.im^a*‖q w‖^2)) := by
    have hh := (mul_le_mul' (le_refl (ENNReal.ofReal (z.im^a))) hmean).trans hweighted
    have hmul : ENNReal.ofReal (z.im^a)*ENNReal.ofReal (Real.pi*(z.im/4)^2*‖q z‖^2) =
        ENNReal.ofReal (Real.pi/16)*ENNReal.ofReal (z.im^(a+2)*‖q z‖^2) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hy.le _),
        ← ENNReal.ofReal_mul (by positivity),Real.rpow_add hy,Real.rpow_two]
      congr 1
      ring
    rw [hmul] at hh
    apply (ENNReal.mul_le_mul_iff_right (by positivity : ENNReal.ofReal (Real.pi/16) ≠ 0)
      ENNReal.ofReal_ne_top).mp
    have he : ENNReal.ofReal (Real.pi/16)*ENNReal.ofReal C = ENNReal.ofReal ((2 : ℝ)^a) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      dsimp only [C]
      field_simp
    rw [← mul_assoc,he]
    exact hh
  have hh := hineq.trans_lt ((ENNReal.mul_lt_mul_iff_right (ENNReal.ofReal_pos.mpr hC).ne'
    ENNReal.ofReal_ne_top).mpr hKε)
  have he : ENNReal.ofReal C*ENNReal.ofReal (ε/C) = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_mul hC.le,mul_div_cancel₀ ε (ne_of_gt hC)]
  rw [he] at hh
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mp hh

lemma quartic_tail_proper {F : ℂ → ℂ} {a R₀ : ℝ}
    (ha : 0 ≤ a) (ht : HasQuarticTail F a)
    (hzero : ∀ z : ℂ, 0 < z.im → R₀ < ‖z‖ → F z ≠ 0)
    (hc : ContinuousOn F {z | 0 < z.im}) {K : Set ℂ} (hK : IsCompact K)
    {η : ℝ} (hη : 0 < η) : IsCompact ({z : ℂ | η ≤ z.im} ∩ F ⁻¹' K) := by
  obtain ⟨M₀,hM₀⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  let M := max M₀ 1
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_right M₀ 1)
  have hδ : 0 < η^a*M⁻¹^4 := mul_pos (Real.rpow_pos_of_pos hη _) (pow_pos (inv_pos.mpr hM) _)
  obtain ⟨R,hR⟩ := ht (η^a*M⁻¹^4) hδ
  have hb : {z : ℂ | η ≤ z.im} ∩ F ⁻¹' K ⊆ Metric.closedBall 0 (max R (R₀+1)) := by
    intro z hz
    rw [Metric.mem_closedBall,dist_zero_right]
    by_contra! hzn
    have hy : 0 < z.im := hη.trans_le hz.1
    have hznR : R ≤ ‖z‖ := (le_max_left _ _).trans hzn.le
    have hzn₀ : R₀ < ‖z‖ := by linarith [le_max_right R (R₀+1)]
    have hFn : 0 < ‖F z‖ := norm_pos_iff.mpr (hzero z hy hzn₀)
    have hFle : ‖F z‖ ≤ M := by
      have hh := hM₀ hz.2
      exact (show ‖F z‖ ≤ M₀ by simpa using hh).trans (le_max_left _ _)
    have hpow : M⁻¹^4 ≤ ‖F z‖⁻¹^4 :=
      pow_le_pow_left₀ (inv_nonneg.mpr hM.le) ((inv_le_inv₀ hM hFn).mpr hFle) 4
    have hheight := Real.rpow_le_rpow hη.le hz.1 ha
    have hle := mul_le_mul hheight hpow (by positivity) (Real.rpow_nonneg hy.le _)
    exact (not_lt_of_ge hle) (hR z hy hznR)
  apply (isCompact_closedBall (0 : ℂ) (max R (R₀+1))).of_isClosed_subset _ hb
  exact (hc.mono (fun z hz => hη.trans_le hz)).preimage_isClosed_of_isClosed
    (isClosed_le continuous_const Complex.continuous_im) hK.isClosed

lemma quartic_tail_height_bound {F : ℂ → ℂ} {a R₀ : ℝ}
    (ha : 0 ≤ a) (ht : HasQuarticTail F a)
    (hzero : ∀ z : ℂ, 0 < z.im → R₀ < ‖z‖ → F z ≠ 0)
    (hc : ContinuousOn F {z | 0 < z.im}) {K : Set ℂ} (hK : IsCompact K) :
    ∃ H : ℝ, 0 < H ∧ ∀ z : ℂ, 0 < z.im → F z ∈ K → z.im ≤ H := by
  have hk := quartic_tail_proper ha ht hzero hc hK (by norm_num : (0 : ℝ) < 1)
  obtain ⟨M,hM⟩ := hk.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨max M 1,lt_of_lt_of_le (by norm_num) (le_max_right M 1),fun z _ hz => ?_⟩
  by_cases hy : 1 ≤ z.im
  · have hh : ‖z‖ ≤ M := by simpa using hM ⟨hy,hz⟩
    exact ((le_abs_self z.im).trans (Complex.abs_im_le_norm z)).trans (hh.trans (le_max_left _ _))
  · exact (le_of_lt (lt_of_not_ge hy)).trans (le_max_right _ _)

lemma quartic_tail_iff_power {F : ℂ → ℂ} {k : ℝ} (ht : HasQuarticTail F (4*k)) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, 0 < z.im → R ≤ ‖z‖ →
      z.im^k*‖F z‖⁻¹ < ε := by
  intro ε hε
  obtain ⟨R,hR⟩ := ht (ε^4) (pow_pos hε _)
  refine ⟨R,fun z hz hzr => ?_⟩
  have hh := hR z hz hzr
  have he : z.im^(4*k)*‖F z‖⁻¹^4 = (z.im^k*‖F z‖⁻¹)^4 := by
    rw [mul_comm (4 : ℝ) k,Real.rpow_mul hz.le,Real.rpow_ofNat,mul_pow]
  rw [he] at hh
  by_contra! hle
  exact (not_lt_of_ge (pow_le_pow_left₀ hε.le hle 4)) hh

lemma outsideCore_of_norm {z : ℂ} (hz : z ∈ halfPlane) (hn : 3 < ‖z‖) :
    z ∈ outsideCore := by
  refine ⟨hz,?_⟩
  change (1/2 : ℝ) ≤ ‖(z-Complex.I)/(z+Complex.I)‖
  rw [norm_div,le_div_iff₀ (norm_pos_iff.mpr (cayley_den_ne_zero hz))]
  have h₁ : ‖z‖ ≤ ‖z-Complex.I‖+1 := by
    simpa only [sub_add_cancel,Complex.norm_I] using norm_add_le (z-Complex.I) Complex.I
  have h₂ : ‖z+Complex.I‖ ≤ ‖z‖+1 := by
    simpa only [Complex.norm_I] using norm_add_le z Complex.I
  linarith

lemma class_quartic_tail (g : DiskClass) {β : ℝ} (hβ : 1 < β)
    (hfin : (∫⁻ z in outsideCore,
      ENNReal.ofReal (z.im^(β+1)*‖classFun g z‖⁻¹^4)) < ∞) :
    HasQuarticTail (classFun g) (β+3) := by
  let q : ℂ → ℂ := fun z => (classFun g z)⁻¹^2
  have hnorm (z : ℂ) : ‖q z‖^2 = ‖classFun g z‖⁻¹^4 := by
    simp only [q,norm_pow,norm_inv,← pow_mul]
  have hhol (z : ℂ) (hz : z ∈ outsideCore) : DifferentiableAt ℂ q z :=
    (((classFun_schlicht g).1.1.differentiableAt
      (isOpen_halfPlane.mem_nhds hz.1)).inv (classFun_ne_zero_outsideCore g hz)).pow 2
  have hfq : (∫⁻ z in outsideCore, ENNReal.ofReal (z.im^(β+1)*‖q z‖^2)) < ∞ := by
    simpa only [hnorm] using hfin
  have hh := weighted_holomorphic_tail (by linarith : 0 ≤ β+1) (by norm_num : (0 : ℝ) ≤ 3)
    (fun z hz hn => outsideCore_of_norm hz hn) hhol hfq
  intro ε hε
  obtain ⟨R,hR⟩ := hh ε hε
  refine ⟨R,fun z hz hzr => ?_⟩
  have he : β+1+2 = β+3 := by ring
  simpa only [he,hnorm] using hR z hz hzr

lemma class_proper_preimage (g : DiskClass) {β : ℝ} (hβ : 1 < β)
    (hfin : (∫⁻ z in outsideCore,
      ENNReal.ofReal (z.im^(β+1)*‖classFun g z‖⁻¹^4)) < ∞)
    {K : Set ℂ} (hK : IsCompact K) {η : ℝ} (hη : 0 < η) :
    IsCompact ({z : ℂ | η ≤ z.im} ∩ classFun g ⁻¹' K) :=
  quartic_tail_proper (by linarith : 0 ≤ β+3) (class_quartic_tail g hβ hfin)
    (fun z hz hn => classFun_ne_zero_outsideCore g (outsideCore_of_norm hz hn))
    (classFun_schlicht g).1.1.continuousOn hK hη

lemma class_preimage_height_bound (g : DiskClass) {β : ℝ} (hβ : 1 < β)
    (hfin : (∫⁻ z in outsideCore,
      ENNReal.ofReal (z.im^(β+1)*‖classFun g z‖⁻¹^4)) < ∞)
    {K : Set ℂ} (hK : IsCompact K) :
    ∃ H : ℝ, 0 < H ∧ ∀ z : ℂ, 0 < z.im → classFun g z ∈ K → z.im ≤ H :=
  quartic_tail_height_bound (by linarith : 0 ≤ β+3) (class_quartic_tail g hβ hfin)
    (fun z hz hn => classFun_ne_zero_outsideCore g (outsideCore_of_norm hz hn))
    (classFun_schlicht g).1.1.continuousOn hK

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.TraceIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun

lemma traceFlux_contDiffAt {g : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hg : ContDiffAt ℝ 2 g p) (ε : ℝ) :
    ContDiffAt ℝ 1 (traceFluxX g ε) p ∧ ContDiffAt ℝ 1 (traceFluxY g ε) p := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ g) p := hg.fderiv_right (by norm_num)
  have htr : ContDiffAt ℝ 1 g p := hg.of_le (by norm_num)
  constructor
  · unfold traceFluxX; fun_prop
  · unfold traceFluxY; fun_prop

lemma divergence_traceFlux {g : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hg : ContDiffAt ℝ 2 g p) (ε : ℝ) :
    fderiv ℝ (traceFluxX g ε) p (1,0)+fderiv ℝ (traceFluxY g ε) p (0,1) =
      (p.2-ε)*pairLaplacian g p := by
  have hdg := hg.differentiableAt (by norm_num)
  have hddg := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hx := hddg.hasFDerivAt.clm_apply (hasFDerivAt_const ((1,0) : ℝ × ℝ) p)
  have hy := hddg.hasFDerivAt.clm_apply (hasFDerivAt_const ((0,1) : ℝ × ℝ) p)
  have hs : HasFDerivAt (fun p : ℝ × ℝ => p.2-ε) (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.sub_const ε
  unfold traceFluxX traceFluxY
  have hfx := (hs.mul hx).fderiv
  have hfy := ((hs.mul hy).sub hdg.hasFDerivAt).fderiv
  change fderiv ℝ (fun p => (p.2-ε)*fderiv ℝ g p (1,0)) p = _ at hfx
  change fderiv ℝ (fun p => (p.2-ε)*fderiv ℝ g p (0,1)-g p) p = _ at hfy
  rw [hfx,hfy]
  simp [pairLaplacian,ContinuousLinearMap.flip_apply,mul_add]

lemma continuousAt_pairLaplacian {g : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hg : ContDiffAt ℝ 2 g p) : ContinuousAt (pairLaplacian g) p := by
  have hh : ContDiffAt ℝ 0 (fderiv ℝ (fderiv ℝ g)) p :=
    (hg.fderiv_right (m := 1) (by norm_num)).fderiv_right (by norm_num)
  have hc := hh.continuousAt
  unfold pairLaplacian
  fun_prop

lemma rectangle_trace_identity {g : ℝ × ℝ → ℝ} {R ε Y : ℝ}
    (hR : 0 ≤ R) (hεY : ε ≤ Y)
    (hg : ∀ p ∈ Icc (-R,ε) (R,Y), ContDiffAt ℝ 2 g p)
    (htop : ∀ x ∈ Icc (-R) R, g (x,Y) = 0 ∧ fderiv ℝ g (x,Y) (0,1) = 0)
    (hside : ∀ y ∈ Icc ε Y,
      fderiv ℝ g (-R,y) (1,0) = 0 ∧ fderiv ℝ g (R,y) (1,0) = 0) :
    (∫ p in Icc (-R,ε) (R,Y), (p.2-ε)*pairLaplacian g p) =
      ∫ x in -R..R, g (x,ε) := by
  have hf : ContinuousOn (traceFluxX g ε) (Icc (-R,ε) (R,Y)) :=
    fun p hp => ((traceFlux_contDiffAt (hg p hp) ε).1.continuousAt).continuousWithinAt
  have hh : ContinuousOn (traceFluxY g ε) (Icc (-R,ε) (R,Y)) :=
    fun p hp => ((traceFlux_contDiffAt (hg p hp) ε).2.continuousAt).continuousWithinAt
  have hint : IntegrableOn (fun p : ℝ × ℝ => (p.2-ε)*pairLaplacian g p)
      (Icc (-R,ε) (R,Y)) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    intro p hp
    have hc : ContinuousAt (fun p : ℝ × ℝ => (p.2-ε)*pairLaplacian g p) p :=
      (continuous_snd.continuousAt.sub_const ε).mul (continuousAt_pairLaplacian (hg p hp))
    exact hc.continuousWithinAt
  have heq (p : ℝ × ℝ) (hp : p ∈ Icc (-R,ε) (R,Y)) := divergence_traceFlux (hg p hp) ε
  have hi : IntegrableOn (fun p => fderiv ℝ (traceFluxX g ε) p (1,0)+
      fderiv ℝ (traceFluxY g ε) p (0,1)) (Icc (-R,ε) (R,Y)) volume :=
    hint.congr (ae_restrict_of_forall_mem measurableSet_Icc (fun p hp => (heq p hp).symm))
  have hb := integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    (traceFluxX g ε) (traceFluxY g ε) (fderiv ℝ (traceFluxX g ε))
    (fderiv ℝ (traceFluxY g ε)) (-R,ε) (R,Y) ⟨by linarith,hεY⟩ hf hh
    (fun p hp => ((traceFlux_contDiffAt (hg p ⟨⟨hp.1.1.le,hp.2.1.le⟩,⟨hp.1.2.le,hp.2.2.le⟩⟩) ε).1.differentiableAt (by norm_num)).hasFDerivAt)
    (fun p hp => ((traceFlux_contDiffAt (hg p ⟨⟨hp.1.1.le,hp.2.1.le⟩,⟨hp.1.2.le,hp.2.2.le⟩⟩) ε).2.differentiableAt (by norm_num)).hasFDerivAt) hi
  rw [setIntegral_congr_fun measurableSet_Icc heq] at hb
  have ht : (∫ x in -R..R, traceFluxY g ε (x,Y)) = 0 := by
    calc
      _ = ∫ _ in -R..R, (0 : ℝ) := ?_
      _ = 0 := by simp
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (-R) R := by simpa only [uIcc_of_le (by linarith : -R ≤ R)] using hx
    simp [traceFluxY,(htop x hx').1,(htop x hx').2]
  have hl : (∫ y in ε..Y, traceFluxX g ε (-R,y)) = 0 := by
    calc
      _ = ∫ _ in ε..Y, (0 : ℝ) := ?_
      _ = 0 := by simp
    apply intervalIntegral.integral_congr
    intro y hy
    simp [traceFluxX,(hside y (by simpa only [uIcc_of_le hεY] using hy)).1]
  have hr : (∫ y in ε..Y, traceFluxX g ε (R,y)) = 0 := by
    calc
      _ = ∫ _ in ε..Y, (0 : ℝ) := ?_
      _ = 0 := by simp
    apply intervalIntegral.integral_congr
    intro y hy
    simp [traceFluxX,(hside y (by simpa only [uIcc_of_le hεY] using hy)).2]
  change _ = ((∫ x in -R..R, traceFluxY g ε (x,Y)) - ∫ x in -R..R, traceFluxY g ε (x,ε)) +
    (∫ y in ε..Y, traceFluxX g ε (R,y)) - ∫ y in ε..Y, traceFluxX g ε (-R,y) at hb
  rw [ht,hl,hr] at hb
  simpa only [traceFluxY,sub_self,zero_mul,zero_sub,
    intervalIntegral.integral_neg,sub_neg_eq_add,zero_add,add_zero,sub_zero] using hb

lemma half_trace_rectangle {g : ℝ × ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hc : ∀ p : ℝ × ℝ, 0 < p.2 → ContDiffAt ℝ 2 g p)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hs : ∀ p : ℝ × ℝ, ε/2 ≤ p.2 → g p ≠ 0 → p ∈ K) :
    ∃ R : ℝ, 0 < R ∧ ε ≤ R ∧ Integrable (fun x : ℝ => g (x,ε)) ∧
      (∫ x : ℝ, g (x,ε)) =
        ∫ p in Icc (-R,ε) (R,R), (p.2-ε)*pairLaplacian g p := by
  obtain ⟨M,hM⟩ := hK.isBounded.subset_closedBall (0 : ℝ × ℝ)
  let R := max M ε+1
  have hR : 0 < R := by dsimp only [R]; linarith [le_max_right M ε]
  have hεR : ε ≤ R := by dsimp only [R]; linarith [le_max_right M ε]
  have hMR : M < R := by dsimp only [R]; linarith [le_max_left M ε]
  have hz (p : ℝ × ℝ) (hy : ε/2 ≤ p.2) (hn : M < ‖p‖) : g p = 0 := by
    by_contra hg
    have hh : ‖p‖ ≤ M := by simpa using hM (hs p hy hg)
    exact (not_lt_of_ge hh) hn
  have hznhd (p : ℝ × ℝ) (hy : ε/2 < p.2) (hn : M < ‖p‖) :
      g =ᶠ[𝓝 p] (0 : ℝ × ℝ → ℝ) := by
    have hy' : {q : ℝ × ℝ | ε/2 < q.2} ∈ 𝓝 p :=
      (isOpen_lt continuous_const continuous_snd).mem_nhds hy
    have hn' : {q : ℝ × ℝ | M < ‖q‖} ∈ 𝓝 p :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds hn
    filter_upwards [hy',hn'] with q hq₁ hq₂
    exact hz q hq₁.le hq₂
  have hd (p : ℝ × ℝ) (hy : ε/2 < p.2) (hn : M < ‖p‖) : fderiv ℝ g p = 0 := by
    rw [(hznhd p hy hn).fderiv_eq,fderiv_zero]
    rfl
  have htop (x : ℝ) (_hx : x ∈ Icc (-R) R) :
      g (x,R) = 0 ∧ fderiv ℝ g (x,R) (0,1) = 0 := by
    have hn : M < ‖(x,R)‖ := hMR.trans_le (by simpa only [Real.norm_eq_abs,abs_of_pos hR] using norm_snd_le (x,R))
    exact ⟨hz (x,R) (by linarith) hn,by rw [hd (x,R) (by linarith) hn]; rfl⟩
  have hside (y : ℝ) (hy : y ∈ Icc ε R) :
      fderiv ℝ g (-R,y) (1,0) = 0 ∧ fderiv ℝ g (R,y) (1,0) = 0 := by
    have h₁ : M < ‖(-R,y)‖ := hMR.trans_le (by simpa only [Real.norm_eq_abs,abs_neg,abs_of_pos hR] using norm_fst_le (-R,y))
    have h₂ : M < ‖(R,y)‖ := hMR.trans_le (by simpa only [Real.norm_eq_abs,abs_of_pos hR] using norm_fst_le (R,y))
    rw [hd (-R,y) (by linarith [hy.1]) h₁,hd (R,y) (by linarith [hy.1]) h₂]
    simp
  have hbox (p : ℝ × ℝ) (hp : p ∈ Icc (-R,ε) (R,R)) : ContDiffAt ℝ 2 g p :=
    hc p (hε.trans_le hp.1.2)
  have hb := rectangle_trace_identity hR.le hεR hbox htop hside
  have hzero (x : ℝ) (hx : x ∉ Icc (-R) R) : g (x,ε) = 0 := by
    apply hz (x,ε) (by linarith)
    have hh : R < |x| := by
      have hh : x < -R ∨ R < x := by simpa only [mem_Icc,not_and_or,not_le] using hx
      rcases hh with hh | hh
      · exact (lt_neg_of_lt_neg hh).trans_le (neg_le_abs x)
      · exact hh.trans_le (le_abs_self x)
    exact hMR.trans (hh.trans_le (norm_fst_le (x,ε)))
  have hcont : Continuous (fun x : ℝ => g (x,ε)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hc (x,ε) hε).continuousAt.comp (f := fun x : ℝ => (x,ε))
      (continuous_id.prodMk continuous_const).continuousAt
  have hint := hcont.continuousOn.integrableOn_compact (μ := volume) (isCompact_Icc (a := -R) (b := R))
  have hline : (∫ x in -R..R, g (x,ε)) = ∫ x : ℝ, g (x,ε) := by
    rw [intervalIntegral.integral_of_le (by linarith : -R ≤ R),
      setIntegral_congr_set Ioc_ae_eq_Icc]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  exact ⟨R,hR,hεR,hint.integrable_of_forall_notMem_eq_zero hzero,(hline.symm.trans hb.symm)⟩

lemma ofReal_integral_le_lintegral_abs.{u_1} {α : Type u_1} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal |f x| ∂μ := by
  rw [← ofReal_integral_eq_lintegral_ofReal hf.abs (Eventually.of_forall (fun x => abs_nonneg (f x)))]
  exact ENNReal.ofReal_le_ofReal (integral_mono hf hf.abs (fun x => le_abs_self _))

lemma half_trace_lintegral_le {g : ℝ × ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hc : ∀ p : ℝ × ℝ, 0 < p.2 → ContDiffAt ℝ 2 g p)
    (hn : ∀ p : ℝ × ℝ, 0 ≤ g p)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hs : ∀ p : ℝ × ℝ, ε/2 ≤ p.2 → g p ≠ 0 → p ∈ K) :
    (∫⁻ x : ℝ, ENNReal.ofReal (g (x,ε))) ≤
      ∫⁻ p in {p : ℝ × ℝ | ε ≤ p.2}, ENNReal.ofReal ((p.2-ε)*|pairLaplacian g p|) := by
  obtain ⟨R,_,_,hi,he⟩ := half_trace_rectangle hε hc hK hs
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun x => hn (x,ε))),he]
  have hi₂ : IntegrableOn (fun p : ℝ × ℝ => (p.2-ε)*pairLaplacian g p)
      (Icc (-R,ε) (R,R)) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    intro p hp
    have hp' : 0 < p.2 := hε.trans_le hp.1.2
    have hh : ContinuousAt (fun p : ℝ × ℝ => (p.2-ε)*pairLaplacian g p) p :=
      (continuous_snd.continuousAt.sub_const ε).mul (continuousAt_pairLaplacian (hc p hp'))
    exact hh.continuousWithinAt
  refine (ofReal_integral_le_lintegral_abs hi₂).trans ?_
  calc
    (∫⁻ p in Icc (-R,ε) (R,R), ENNReal.ofReal |(p.2-ε)*pairLaplacian g p|) =
        ∫⁻ p in Icc (-R,ε) (R,R), ENNReal.ofReal ((p.2-ε)*|pairLaplacian g p|) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro p hp
      simp only [abs_mul,abs_of_nonneg (sub_nonneg.mpr hp.1.2)]
    _ ≤ _ := lintegral_mono_set (fun p hp => hp.1.2)

lemma secondReal_comp {ψ : ℂ → ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hψ : ContDiffAt ℝ 2 ψ (F z)) (hF : ContDiffAt ℝ 2 F z) (u v : ℂ) :
    secondReal (ψ ∘ F) z u v =
      fderiv ℝ ψ (F z) (complexSecondReal F z u v) +
      secondReal ψ (F z) (fderiv ℝ F z u) (fderiv ℝ F z v) := by
  have hdψ := hψ.differentiableAt (by norm_num)
  have hdF := hF.differentiableAt (by norm_num)
  have hddψ := (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hddF := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he : fderiv ℝ (ψ ∘ F) =ᶠ[𝓝 z] fun w =>
      (fderiv ℝ ψ (F w)).comp (fderiv ℝ F w) := by
    filter_upwards [hF.eventually (by simp),hdF.continuousAt.eventually (hψ.eventually (by simp))] with w hFw hψw
    exact fderiv_comp w (hψw.differentiableAt (by norm_num)) (hFw.differentiableAt (by norm_num))
  have hh := ((hddψ.hasFDerivAt.comp z hdF.hasFDerivAt).clm_comp hddF.hasFDerivAt).congr_of_eventuallyEq he
  rw [secondReal,hh.fderiv]
  simp [secondReal,complexSecondReal,ContinuousLinearMap.compL_apply]

lemma bilinear_complex_rotation (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (c : ℂ) :
    B c c + B (c*Complex.I) (c*Complex.I) = ‖c‖^2*(B 1 1+B Complex.I Complex.I) := by
  have hc : c = c.re • (1 : ℂ)+c.im • Complex.I := by simp
  have hci : c*Complex.I = (-c.im) • (1 : ℂ)+c.re • Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  have hn : ‖c‖^2 = c.re^2+c.im^2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply,pow_two]
  rw [hci,hc]
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
  rw [← hc,hn]
  ring

lemma laplacian_eq_secondReal (f : ℂ → ℝ) (z : ℂ) :
    Laplacian.laplacian f z = secondReal f z 1 1+secondReal f z Complex.I Complex.I := by
  simp [laplacian_eq_iteratedFDeriv_complexPlane,iteratedFDeriv_two_apply,secondReal]

lemma laplacian_eq_complexSecondReal (f : ℂ → ℂ) (z : ℂ) :
    Laplacian.laplacian f z = complexSecondReal f z 1 1+complexSecondReal f z Complex.I Complex.I := by
  simp [laplacian_eq_iteratedFDeriv_complexPlane,iteratedFDeriv_two_apply,complexSecondReal]

lemma fderiv_real_complex_apply {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) (v : ℂ) : fderiv ℝ F z v = deriv F z*v := by
  rw [(hF.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv]
  simp [smul_eq_mul,mul_comm]

lemma laplacian_holomorphic_comp {ψ : ℂ → ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hψ : ContDiffAt ℝ 2 ψ (F z)) (hF : AnalyticAt ℂ F z) :
    Laplacian.laplacian (ψ ∘ F) z = ‖deriv F z‖^2*Laplacian.laplacian ψ (F z) := by
  rw [laplacian_eq_secondReal,secondReal_comp hψ (hF.contDiffAt.restrict_scalars ℝ),
    secondReal_comp hψ (hF.contDiffAt.restrict_scalars ℝ)]
  have hz := hF.harmonicAt.2.eq_of_nhds
  rw [laplacian_eq_complexSecondReal] at hz
  change complexSecondReal F z 1 1+complexSecondReal F z Complex.I Complex.I = 0 at hz
  have he : fderiv ℝ ψ (F z) (complexSecondReal F z 1 1)+
      fderiv ℝ ψ (F z) (complexSecondReal F z Complex.I Complex.I) = 0 := by
    rw [← map_add,hz,map_zero]
  simp only [fderiv_real_complex_apply hF.differentiableAt,mul_one]
  have hb := bilinear_complex_rotation (fderiv ℝ (fderiv ℝ ψ) (F z)) (deriv F z)
  rw [laplacian_eq_secondReal]
  dsimp only [secondReal] at *
  linarith

lemma pairLaplacian_complex (f : ℂ → ℝ) (p : ℝ × ℝ) :
    pairLaplacian (f ∘ Complex.equivRealProdCLM.symm) p =
      Laplacian.laplacian f (Complex.equivRealProdCLM.symm p) := by
  have he := Complex.equivRealProdCLM.symm.iteratedFDerivWithin_comp_right
    f (s := univ) uniqueDiffOn_univ (mem_univ (Complex.equivRealProdCLM.symm p)) 2
  simp only [preimage_univ,iteratedFDerivWithin_univ] at he
  have h₁ := congrArg (fun B => B ![((1,0) : ℝ × ℝ),(1,0)]) he
  have h₂ := congrArg (fun B => B ![((0,1) : ℝ × ℝ),(0,1)]) he
  simp only [iteratedFDeriv_two_apply,ContinuousMultilinearMap.compContinuousLinearMap_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,ContinuousLinearEquiv.coe_coe] at h₁ h₂
  have hc₁ : Complex.equivRealProdCLM.symm (1,0) = 1 := by simp [Complex.equivRealProdCLM_symm_apply]
  have hc₂ : Complex.equivRealProdCLM.symm (0,1) = Complex.I := by simp [Complex.equivRealProdCLM_symm_apply]
  rw [hc₁] at h₁
  rw [hc₂] at h₂
  rw [pairLaplacian,h₁,h₂,laplacian_eq_secondReal]
  rfl

lemma laplacian_eq_zero_outside_tsupport {ψ : ℂ → ℝ} {z : ℂ}
    (hz : z ∉ tsupport ψ) : Laplacian.laplacian ψ z = 0 := by
  have he := notMem_tsupport_iff_eventuallyEq.mp hz
  have hh := laplacian_congr_nhds he
  exact hh.eq_of_nhds.trans (by
    change Laplacian.laplacian (fun _ : ℂ => (0 : ℝ)) z = 0
    rw [laplacian_const]
    rfl)

lemma continuous_laplacian {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 2 ψ) :
    Continuous (Laplacian.laplacian ψ) := by
  have hh : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ ψ)) :=
    (hψ.fderiv_right (m := 1) (by norm_num)).fderiv_right (by norm_num)
  have hc := hh.continuous
  have he : Laplacian.laplacian ψ = fun z => secondReal ψ z 1 1+secondReal ψ z Complex.I Complex.I :=
    funext (laplacian_eq_secondReal ψ)
  rw [he]
  unfold secondReal
  fun_prop

lemma compactSupport_laplacian {ψ : ℂ → ℝ} (hψ : HasCompactSupport ψ) :
    HasCompactSupport (Laplacian.laplacian ψ) := by
  apply hψ.mono'
  intro z hz
  by_contra hn
  exact hz (laplacian_eq_zero_outside_tsupport hn)

lemma conformal_lintegral_le {F : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    (hF : ∀ z ∈ s, DifferentiableAt ℂ F z) (hi : InjOn F s) (b : ℂ → ℝ≥0∞) :
    (∫⁻ z in s, ENNReal.ofReal (‖deriv F z‖^2)*b (F z)) ≤ ∫⁻ w, b w := by
  have he := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun z hz => (hF z hz).hasFDerivAt.restrictScalars ℝ |>.hasFDerivWithinAt) hi b
  have hh : (∫⁻ z in s, ENNReal.ofReal (‖deriv F z‖^2)*b (F z)) = ∫⁻ w in F '' s, b w := by
    rw [he]
    apply setLIntegral_congr_fun hs
    intro z hz
    have hd := (hF z hz).hasFDerivAt.restrictScalars ℝ
    have hf : (ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ F z)) = fderiv ℝ F z := hd.fderiv.symm
    dsimp only
    rw [hf]
    have hd' : (fderiv ℝ F z).det = ‖deriv F z‖^2 := det_fderiv_complex (hF z hz)
    rw [hd',abs_of_nonneg (sq_nonneg _)]
  rw [hh]
  exact lintegral_mono' Measure.restrict_le_self le_rfl

lemma conformal_cutoff_trace_bound {F : ℂ → ℂ} {ψ : ℂ → ℝ}
    (hF : ∀ z : ℂ, 0 < z.im → AnalyticAt ℂ F z)
    (hi : InjOn F {z : ℂ | 0 < z.im})
    (hψ : ContDiff ℝ 2 ψ) (hn : ∀ w, 0 ≤ ψ w) (_hψK : HasCompactSupport ψ)
    (hproper : ∀ η : ℝ, 0 < η → IsCompact ({z : ℂ | η ≤ z.im} ∩ F ⁻¹' tsupport ψ))
    {H : ℝ} (hH : 0 ≤ H)
    (hheight : ∀ z : ℂ, 0 < z.im → F z ∈ tsupport ψ → z.im ≤ H) :
    ∀ ε : ℝ, 0 < ε → (∫⁻ x : ℝ, ENNReal.ofReal (ψ (F (x+ε*Complex.I)))) ≤
      ENNReal.ofReal H * ∫⁻ w : ℂ, ENNReal.ofReal |Laplacian.laplacian ψ w| := by
  intro ε hε
  let C := Complex.equivRealProdCLM.symm
  let g : ℝ × ℝ → ℝ := (ψ ∘ F) ∘ C
  have hc (p : ℝ × ℝ) (hp : 0 < p.2) : ContDiffAt ℝ 2 g p := by
    have hz : 0 < (C p).im := hp
    exact (hψ.contDiffAt.comp _ ((hF (C p) hz).contDiffAt.restrict_scalars ℝ)).comp _ C.contDiff.contDiffAt
  have hK := (hproper (ε/2) (by linarith)).image Complex.equivRealProdCLM.continuous
  have hs (p : ℝ × ℝ) (hp : ε/2 ≤ p.2) (hg : g p ≠ 0) :
      p ∈ Complex.equivRealProdCLM '' ({z : ℂ | ε/2 ≤ z.im} ∩ F ⁻¹' tsupport ψ) := by
    refine ⟨C p,⟨hp,subset_closure hg⟩,?_⟩
    exact Complex.equivRealProdCLM.apply_symm_apply p
  have ht := half_trace_lintegral_le hε hc (fun p => hn _) hK hs
  have ht' : (∫⁻ x : ℝ, ENNReal.ofReal (ψ (F (x+ε*Complex.I)))) ≤
      ∫⁻ z in {z : ℂ | ε ≤ z.im}, ENNReal.ofReal ((z.im-ε)*|Laplacian.laplacian (ψ ∘ F) z|) := by
    have he := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding
      (fun p : ℝ × ℝ => ENNReal.ofReal ((p.2-ε)*|pairLaplacian g p|)) {p : ℝ × ℝ | ε ≤ p.2}
    have hh : (∫⁻ p in {p : ℝ × ℝ | ε ≤ p.2}, ENNReal.ofReal ((p.2-ε)*|pairLaplacian g p|)) =
        ∫⁻ z in {z : ℂ | ε ≤ z.im}, ENNReal.ofReal ((z.im-ε)*|Laplacian.laplacian (ψ ∘ F) z|) := by
      rw [← he]
      apply lintegral_congr
      intro z
      dsimp only [g,C]
      rw [pairLaplacian_complex]
      rfl
    rw [hh] at ht
    simpa only [g,C,Function.comp_apply,Complex.equivRealProdCLM_symm_apply] using ht
  refine ht'.trans ?_
  have hmeas : MeasurableSet {z : ℂ | ε ≤ z.im} := isClosed_le continuous_const Complex.continuous_im |>.measurableSet
  calc
    (∫⁻ z in {z : ℂ | ε ≤ z.im}, ENNReal.ofReal ((z.im-ε)*|Laplacian.laplacian (ψ ∘ F) z|)) ≤
        ∫⁻ z in {z : ℂ | ε ≤ z.im}, ENNReal.ofReal H *
          (ENNReal.ofReal (‖deriv F z‖^2)*ENNReal.ofReal |Laplacian.laplacian ψ (F z)|) := by
      apply setLIntegral_mono' hmeas
      intro z hz
      rw [laplacian_holomorphic_comp hψ.contDiffAt (hF z (hε.trans_le hz)),
        abs_mul,abs_of_nonneg (sq_nonneg _),← ENNReal.ofReal_mul (sq_nonneg _),
        ← ENNReal.ofReal_mul hH]
      apply ENNReal.ofReal_le_ofReal
      by_cases hd : Laplacian.laplacian ψ (F z) = 0
      · simp [hd]
      have hm : F z ∈ tsupport ψ := by
        by_contra hh
        exact hd (laplacian_eq_zero_outside_tsupport hh)
      nlinarith [sq_nonneg ‖deriv F z‖,abs_nonneg (Laplacian.laplacian ψ (F z)),
        hheight z (hε.trans_le hz) hm,
        mul_nonneg (sq_nonneg ‖deriv F z‖) (abs_nonneg (Laplacian.laplacian ψ (F z)))]
    _ = ENNReal.ofReal H * ∫⁻ z in {z : ℂ | ε ≤ z.im},
        ENNReal.ofReal (‖deriv F z‖^2)*ENNReal.ofReal |Laplacian.laplacian ψ (F z)| :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
      exact mul_le_mul le_rfl (conformal_lintegral_le hmeas
        (fun z hz => (hF z (hε.trans_le hz)).differentiableAt)
        (hi.mono (fun z hz => hε.trans_le hz))
        (fun w => ENNReal.ofReal |Laplacian.laplacian ψ w|)) zero_le zero_le

lemma exists_trace_smooth_cutoff (K : Set ℂ) (hK : IsCompact K) :
    ∃ ψ : ℂ → ℝ, ContDiff ℝ 2 ψ ∧ (∀ w, 0 ≤ ψ w) ∧ HasCompactSupport ψ ∧
      ∀ w ∈ K, ψ w = 1 := by
  obtain ⟨R,hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  let b : ContDiffBump (0 : ℂ) := ⟨max R 0+1,max R 0+2,by positivity,by linarith⟩
  refine ⟨b,b.contDiff,b.nonneg',b.hasCompactSupport,fun w hw => ?_⟩
  apply b.one_of_mem_closedBall
  exact Metric.closedBall_subset_closedBall (by dsimp [b]; linarith [le_max_left R 0]) (hR hw)

lemma conformal_trace_bound {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, 0 < z.im → AnalyticAt ℂ F z)
    (hi : InjOn F {z : ℂ | 0 < z.im})
    (hproper : ∀ K : Set ℂ, IsCompact K → ∀ η : ℝ, 0 < η →
      IsCompact ({z : ℂ | η ≤ z.im} ∩ F ⁻¹' K))
    (hheight : ∀ K : Set ℂ, IsCompact K → ∃ H : ℝ, 0 < H ∧
      ∀ z : ℂ, 0 < z.im → F z ∈ K → z.im ≤ H)
    {K : Set ℂ} (hK : IsCompact K) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ ε : ℝ, 0 < ε →
      volume {x : ℝ | F (x+ε*Complex.I) ∈ K} ≤ C := by
  obtain ⟨ψ,hψ,hn,hψK,hψone⟩ := exists_trace_smooth_cutoff K hK
  obtain ⟨H,hH,hHb⟩ := hheight (tsupport ψ) hψK
  let C := ENNReal.ofReal H * ∫⁻ w : ℂ, ENNReal.ofReal |Laplacian.laplacian ψ w|
  have hfin : C < ∞ := by
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    have hi := (continuous_laplacian hψ).integrable_of_hasCompactSupport (μ := volume) (compactSupport_laplacian hψK)
    simpa only [HasFiniteIntegral,← ofReal_norm,Real.norm_eq_abs] using hi.hasFiniteIntegral
  refine ⟨C,hfin,fun ε hε => ?_⟩
  have hb := conformal_cutoff_trace_bound hF hi hψ hn hψK
    (hproper (tsupport ψ) hψK) hH.le hHb ε hε
  refine le_trans ?_ hb
  have hcont : Continuous (fun x : ℝ => F (x+ε*Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hz : 0 < (x+ε*Complex.I : ℂ).im := by simpa using hε
    exact (hF _ hz).continuousAt.comp (f := fun x : ℝ => (x+ε*Complex.I : ℂ))
      (by fun_prop)
  have hm : MeasurableSet {x : ℝ | F (x+ε*Complex.I) ∈ K} :=
    hK.isClosed.measurableSet.preimage hcont.measurable
  rw [← lintegral_indicator_one hm]
  apply lintegral_mono
  intro x
  by_cases hx : F (x+ε*Complex.I) ∈ K
  · simp [hx,hψone _ hx]
  · simp [hx]

lemma class_trace_bound (g : DiskClass) {β : ℝ} (hβ : 1 < β)
    (hfin : (∫⁻ z in outsideCore,
      ENNReal.ofReal (z.im^(β+1)*‖classFun g z‖⁻¹^4)) < ∞)
    {K : Set ℂ} (hK : IsCompact K) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ ε : ℝ, 0 < ε →
      volume {x : ℝ | classFun g (x+ε*Complex.I) ∈ K} ≤ C := by
  apply conformal_trace_bound
    (fun z hz => (classFun_schlicht g).1.1.analyticAt (isOpen_halfPlane.mem_nhds hz))
    (classFun_schlicht g).1.2
    (fun _ hK η hη => class_proper_preimage g hβ hfin hK hη)
    (fun _ hK => class_preimage_height_bound g hβ hfin hK) hK

lemma uniform_relative_class_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (g : DiskClass) (w : ℂ), |w.re| ≤ 1 →
      (1/2 : ℝ) ≤ w.im → w.im ≤ 1 → ‖classFun g w‖ ≤ M := by
  let B : Set (ℝ × ℝ) := Icc (-1,1/2) (1,1)
  let K : Set ℂ := Complex.equivRealProdCLM.symm '' B
  have hK : IsCompact K := isCompact_Icc.image Complex.equivRealProdCLM.symm.continuous
  have hKsub : K ⊆ Set.range (fun w : halfPlane => (w : ℂ)) := by
    rintro _ ⟨p,hp,rfl⟩
    refine ⟨⟨Complex.equivRealProdCLM.symm p,?_⟩,rfl⟩
    change 0 < p.2
    linarith [hp.1.2]
  have hKs : IsCompact ((fun w : halfPlane => (w : ℂ)) ⁻¹' K) :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK hKsub
  have hprod := (isCompact_univ (X := DiskClass)).prod hKs
  obtain ⟨M,hM⟩ := hprod.exists_bound_of_continuousOn continuous_classFun_eval.continuousOn
  refine ⟨max M 0,le_max_right _ _,fun g w hx hy hyy => ?_⟩
  have hw : w ∈ halfPlane := by change 0 < w.im; linarith
  have hmem : (g,⟨w,hw⟩) ∈ (univ : Set DiskClass) ×ˢ ((fun w : halfPlane => (w : ℂ)) ⁻¹' K) := by
    refine ⟨mem_univ _,⟨(w.re,w.im),?_,?_⟩⟩
    · exact ⟨⟨(abs_le.mp hx).1,hy⟩,⟨(abs_le.mp hx).2,hyy⟩⟩
    · exact Complex.equivRealProdCLM.symm_apply_apply w
  exact (hM _ hmem).trans (le_max_left _ _)

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.BoundaryEscape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun

lemma halfPlane_ball_subset {z : ℂ} (_hz : z ∈ halfPlane) :
    Metric.ball z z.im ⊆ halfPlane := by
  intro w hw
  have hh : ‖w-z‖ < z.im := by simpa only [Metric.mem_ball,dist_eq_norm] using hw
  have hb := Complex.abs_im_le_norm (w-z)
  change 0 < w.im
  simp only [Complex.sub_im] at hb
  linarith [neg_le_abs (w.im-z.im)]

lemma omitted_quarter_bound {F : ℂ → ℂ} (hf : UnivalentOn F halfPlane)
    {z ξ : ℂ} (hz : z ∈ halfPlane) (hξ : ξ ∉ F '' halfPlane) :
    z.im*‖deriv F z‖ ≤ 4*‖F z-ξ‖ := by
  have hr : 0 < z.im := hz
  have hb := univalent_ball_quarter hr
    (show UnivalentOn F (Metric.ball z z.im) from ⟨hf.1.mono (halfPlane_ball_subset hz),hf.2.mono (halfPlane_ball_subset hz)⟩)
  have hn : ξ ∉ Metric.ball (F z) (z.im*‖deriv F z‖/4) := by
    intro hh
    exact hξ ((image_mono (halfPlane_ball_subset hz)) (hb hh))
  have hn' : z.im*‖deriv F z‖/4 ≤ ‖F z-ξ‖ := by
    simpa only [Metric.mem_ball,dist_eq_norm,not_lt,norm_sub_rev] using hn
  linarith

lemma class_omitted_cell_bound {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ (g : DiskClass) (w : ℂ), |w.re| ≤ 1 → (1/2 : ℝ) ≤ w.im → w.im ≤ 1 → ‖classFun g w‖ ≤ M)
    (g : DiskClass) {h x y x' : ℝ} {ξ : ℂ} (hh : 0 < h)
    (hy : h ≤ y) (hyy : y ≤ 2*h) (hxx : |x'-x| ≤ h)
    (hξ : ξ ∉ classFun g '' halfPlane) :
    ‖classFun g (x'+h*Complex.I)-ξ‖ ≤ (1+4*M)*‖classFun g (x+y*Complex.I)-ξ‖ := by
  let z : ℂ := x+y*Complex.I
  let w : ℂ := ((x'-x)/y : ℝ)+(h/y : ℝ)*Complex.I
  have hy0 : 0 < y := hh.trans_le hy
  have hz : z ∈ halfPlane := by simpa [z,halfPlane] using hy0
  have hwy : w.im = h/y := by simp [w]
  have hwx : w.re = (x'-x)/y := by simp [w]
  have hw : w ∈ halfPlane := by simpa [halfPlane,hwy] using (div_pos hh hy0)
  have hwr : |w.re| ≤ 1 := by rw [hwx,abs_div,abs_of_pos hy0]; exact (div_le_one hy0).mpr (hxx.trans hy)
  have hwl : (1/2 : ℝ) ≤ w.im := by rw [hwy,le_div_iff₀ hy0]; linarith
  have hwu : w.im ≤ 1 := by rw [hwy]; exact (div_le_one hy0).mpr hy
  have hwa : affine z w = x'+h*Complex.I := by
    apply Complex.ext <;> simp [affine,z,w,Complex.mul_re,Complex.mul_im]
    · field_simp
      ring
    · field_simp
  have hd : ‖deriv (classFun g) z‖ > 0 := norm_pos_iff.mpr (univalent_deriv_ne_zero isOpen_halfPlane (classFun_schlicht g).1 hz)
  have hm := hb (rerootClass g ⟨z,hz⟩) w hwr hwl hwu
  rw [classFun_rerootClass _ _ hw,reroot,hwa,norm_div,norm_mul,Complex.norm_real] at hm
  have hzim : z.im = y := by simp [z]
  rw [hzim,Real.norm_eq_abs,abs_of_pos hy0] at hm
  have hm' := (div_le_iff₀ (mul_pos hy0 hd)).mp hm
  have hq := omitted_quarter_bound (classFun_schlicht g).1 hz hξ
  rw [hzim] at hq
  have hsum := norm_add_le (classFun g (x'+h*Complex.I)-classFun g z) (classFun g z-ξ)
  simp only [sub_add_sub_cancel] at hsum
  have hhq := mul_le_mul_of_nonneg_left hq hM
  dsimp only [z] at *
  nlinarith

lemma interior_positive_superlevel_height {F : ℂ → ℂ} {k δ : ℝ}
    (hk : 0 < k) (_hδ : 0 < δ)
    (hi : InjOn F {z : ℂ | 0 < z.im})
    (hopen : ∀ z : ℂ, 0 < z.im → map F (𝓝 z) = 𝓝 (F z))
    {ξ : ℂ} (hξ : ξ ∈ F '' {z : ℂ | 0 < z.im}) :
    ∃ η : ℝ, 0 < η ∧ ∀ z : ℂ, 0 < z.im →
      ‖F z-ξ‖ ≤ z.im^k/δ → η ≤ z.im := by
  obtain ⟨z₀,hz₀,rfl⟩ := hξ
  change 0 < z₀.im at hz₀
  have hn : {z : ℂ | z₀.im/2 < z.im} ∈ 𝓝 z₀ :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds (by change z₀.im/2 < z₀.im; linarith)
  have hn' := image_mem_map (m := F) hn
  rw [hopen z₀ hz₀] at hn'
  obtain ⟨r,hr,hrB⟩ := Metric.mem_nhds_iff.mp hn'
  have hc : ContinuousAt (fun y : ℝ => y^k/δ) 0 :=
    (Real.continuous_rpow_const hk.le).continuousAt.div_const δ
  have he : (0 : ℝ)^k/δ = 0 := by rw [Real.zero_rpow (ne_of_gt hk),zero_div]
  have hevent : ∀ᶠ y : ℝ in 𝓝 0, y^k/δ < r := by
    have hh := hc.eventually (gt_mem_nhds (show (0 : ℝ)^k/δ < r by rwa [he]))
    exact hh
  obtain ⟨a,ha,haB⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨min a (z₀.im/2),lt_min ha (by linarith),fun z hz hzw => ?_⟩
  by_contra! hsmall
  have hza : z.im < a := hsmall.trans_le (min_le_left _ _)
  have hm : F z ∈ Metric.ball (F z₀) r := by
    rw [Metric.mem_ball,dist_eq_norm]
    exact hzw.trans_lt (haB (by simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hz] using hza))
  obtain ⟨w,hw,hwe⟩ := hrB hm
  have hwH : 0 < w.im := by change z₀.im/2 < w.im at hw; linarith
  have hwz : w = z := hi hwH hz hwe
  subst w
  change z₀.im/2 < z.im at hw
  exact (not_lt_of_ge hw.le) (hsmall.trans_le (min_le_right _ _))

lemma positive_superlevel_compact {F : ℂ → ℂ} {k δ : ℝ} {ξ : ℂ}
    (hk : 0 ≤ k) (hδ : 0 < δ)
    (hc : ContinuousOn F {z : ℂ | 0 < z.im})
    (ht : HasQuarticTail F (4*k))
    (hp : ∀ K : Set ℂ, IsCompact K → ∀ η : ℝ, 0 < η →
      IsCompact ({z : ℂ | η ≤ z.im} ∩ F ⁻¹' K))
    (hheight : ∃ η : ℝ, 0 < η ∧ ∀ z : ℂ, 0 < z.im →
      ‖F z-ξ‖ ≤ z.im^k/δ → η ≤ z.im) :
    IsCompact (closedPositiveSuperlevel F k δ ξ) := by
  obtain ⟨η,hη,hηb⟩ := hheight
  obtain ⟨R₀,hR₀⟩ := (hp (Metric.closedBall (0 : ℂ) (2*‖ξ‖+1))
    (isCompact_closedBall _ _) η hη).isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨R₁,hR₁⟩ := quartic_tail_iff_power ht (δ/2) (by linarith)
  have hb : closedPositiveSuperlevel F k δ ξ ⊆ Metric.closedBall 0 (max R₀ R₁) := by
    intro z hz
    rw [Metric.mem_closedBall,dist_zero_right]
    by_contra! hn
    have hno : 2*‖ξ‖+1 < ‖F z‖ := by
      by_contra! hle
      have hh := hR₀ ⟨hηb z hz.1 hz.2,by simpa using hle⟩
      have hh' : ‖z‖ ≤ R₀ := by simpa using hh
      linarith [le_max_left R₀ R₁]
    have hFn : 0 < ‖F z‖ := by nlinarith [norm_nonneg ξ]
    have ht' := hR₁ z hz.1 ((le_max_right _ _).trans hn.le)
    rw [← div_eq_mul_inv,div_lt_iff₀ hFn] at ht'
    have hpot := (le_div_iff₀ hδ).mp hz.2
    have hnorm : ‖F z‖ ≤ ‖F z-ξ‖+‖ξ‖ := by
      simpa only [sub_add_cancel] using norm_add_le (F z-ξ) ξ
    nlinarith
  have he : closedPositiveSuperlevel F k δ ξ =
      {z : ℂ | η ≤ z.im} ∩ (fun z => ‖F z-ξ‖-z.im^k/δ) ⁻¹' Iic 0 := by
    ext z
    constructor
    · intro hz
      exact ⟨hηb z hz.1 hz.2,sub_nonpos.mpr hz.2⟩
    · intro hz
      exact ⟨hη.trans_le hz.1,sub_nonpos.mp hz.2⟩
  have hcc : ContinuousOn (fun z : ℂ => ‖F z-ξ‖-z.im^k/δ) {z : ℂ | η ≤ z.im} := by
    apply ((hc.mono (fun z hz => hη.trans_le hz)).sub continuousOn_const).norm.sub
    exact ((Real.continuous_rpow_const hk).comp Complex.continuous_im).continuousOn.div_const δ
  apply (isCompact_closedBall (0 : ℂ) (max R₀ R₁)).of_isClosed_subset _ hb
  rw [he]
  exact hcc.preimage_isClosed_of_isClosed (isClosed_le continuous_const Complex.continuous_im) isClosed_Iic

lemma realCell_disjoint {h : ℝ} (hh : 0 < h) : Pairwise (Function.onFun Disjoint (realCell h)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hhij : (i : ℝ)+1 ≤ j := by exact_mod_cast Int.add_one_le_iff.mpr hij
    have hm := mul_le_mul_of_nonneg_right hhij hh.le
    exact (not_lt_of_ge (hm.trans hy.1)) hx.2
  · have hhji : (j : ℝ)+1 ≤ i := by exact_mod_cast Int.add_one_le_iff.mpr hji
    have hm := mul_le_mul_of_nonneg_right hhji hh.le
    exact (not_lt_of_ge (hm.trans hx.1)) hy.2

lemma measure_realCell {h : ℝ} (_hh : 0 ≤ h) (j : ℤ) :
    volume (realCell h j) = ENNReal.ofReal h := by
  rw [realCell,Real.volume_Ico]
  congr 1
  ring

lemma mem_realCell_floor {h : ℝ} (hh : 0 < h) (x : ℝ) : x ∈ realCell h ⌊x/h⌋ := by
  constructor
  · exact (le_div_iff₀ hh).mp (Int.floor_le _)
  · exact (div_lt_iff₀ hh).mp (Int.lt_floor_add_one _)

lemma realCell_length_bound {h : ℝ} (_hh : 0 < h) {j : ℤ} {x x' : ℝ}
    (hx : x ∈ realCell h j) (hx' : x' ∈ realCell h j) : |x'-x| ≤ h := by
  rw [abs_le]
  constructor <;> dsimp [realCell] at hx hx' <;> nlinarith [hx.1,hx.2,hx'.1,hx'.2]

lemma cell_target_cover_bound {h r : ℝ} (hh : 0 < h) (hr : 0 ≤ r)
    (W : Set ℤ) (centers : ℤ → ℂ) {S : Set ℝ} {C : ℝ≥0∞}
    (hsub : ∀ j ∈ W, realCell h j ⊆ S) (hS : volume S ≤ C) :
    volume (⋃ j : W, Metric.closedBall (centers j) r) ≤
      (ENNReal.ofReal (Real.pi*r^2)/ENNReal.ofReal h)*C := by
  have hlen : (∑' j : W, ENNReal.ofReal h) ≤ C := by
    have hd : Pairwise (Function.onFun Disjoint (fun j : W => realCell h j)) := by
      intro i j hij
      exact realCell_disjoint hh (fun he => hij (Subtype.ext he))
    have he := measure_iUnion (μ := volume) hd (fun _ => measurableSet_Ico)
    simp only [measure_realCell hh.le] at he
    rw [← he]
    exact (measure_mono (iUnion_subset (fun (j : W) => hsub j.val j.property))).trans hS
  have harea (j : W) : volume (Metric.closedBall (centers j) r) = ENNReal.ofReal (Real.pi*r^2) := by
    rw [Complex.volume_closedBall]
    have hpi : (NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
      rw [ENNReal.ofReal,ENNReal.coe_inj]
      apply Subtype.ext
      exact (Real.coe_toNNReal Real.pi Real.pi_pos.le).symm
    rw [hpi,ENNReal.ofReal_mul Real.pi_pos.le,ENNReal.ofReal_pow hr]
    exact mul_comm _ _
  calc
    _ ≤ ∑' j : W, volume (Metric.closedBall (centers j) r) := measure_iUnion_le _
    _ = ∑' j : W, (ENNReal.ofReal (Real.pi*r^2)/ENNReal.ofReal h)*ENNReal.ofReal h := by
      apply tsum_congr
      intro j
      rw [harea]
      exact (ENNReal.div_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hh)) ENNReal.ofReal_ne_top).symm
    _ = (ENNReal.ofReal (Real.pi*r^2)/ENNReal.ofReal h)*(∑' j : W, ENNReal.ofReal h) := ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul le_rfl hlen zero_le zero_le

lemma summable_geometric_ofReal {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' n : ℕ, ENNReal.ofReal (r^n)) < ∞ := by
  have hs : Summable (fun n : ℕ => (⟨r^n,pow_nonneg hr0 n⟩ : ℝ≥0)) :=
    NNReal.summable_coe.mp (summable_geometric_of_lt_one hr0 hr1)
  have ht := ENNReal.tsum_coe_ne_top_iff_summable.mpr hs
  apply lt_top_iff_ne_top.mpr
  convert ht using 1
  congr 1
  ext n
  exact ENNReal.ofReal_eq_coe_nnreal (pow_nonneg hr0 n)

lemma ae_eventually_outside_geometric_covers {E : ℕ → Set ℂ} {C : ℝ≥0∞} (hC : C < ∞)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hE : ∀ n, volume (E n) ≤ C*ENNReal.ofReal (r^n)) :
    ∀ᵐ ξ : ℂ, ∀ᶠ n : ℕ in atTop, ξ ∉ E n := by
  apply ae_eventually_notMem
  apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hE)
  rw [ENNReal.tsum_mul_left]
  exact ne_of_lt (ENNReal.mul_lt_top hC (summable_geometric_ofReal hr0 hr1))

lemma dyadicHeight_pos (n : ℕ) : 0 < dyadicHeight n := pow_pos (by norm_num) n

lemma dyadicHeight_le_one (n : ℕ) : dyadicHeight n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)

lemma exists_dyadic_slab {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    ∃ n : ℕ, dyadicHeight n ≤ y ∧ y ≤ 2*dyadicHeight n := by
  obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near_of_lt_one hy hy1
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1)
  refine ⟨n+1,hn.le,?_⟩
  dsimp [dyadicHeight]
  rw [pow_succ]
  nlinarith

lemma dyadicHeight_antitone : Antitone dyadicHeight := by
  intro m n hmn
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn

lemma small_height_dyadic_slab (N : ℕ) {y : ℝ} (hy : 0 < y) (hyN : y < dyadicHeight N) :
    ∃ n ≥ N, dyadicHeight n ≤ y ∧ y ≤ 2*dyadicHeight n := by
  obtain ⟨n,hn,hn'⟩ := exists_dyadic_slab hy (hyN.le.trans (dyadicHeight_le_one N))
  refine ⟨n,?_,hn,hn'⟩
  by_contra! h
  exact (not_lt_of_ge ((dyadicHeight_antitone h.le).trans hn)) hyN

lemma slab_power_bound {k h y : ℝ} (hk : 1 ≤ k) (hh : 0 < h) (hh1 : h ≤ 1)
    (hy : 0 ≤ y) (hyh : y ≤ 2*h) : y^k ≤ (2 : ℝ)^k*h := by
  calc
    y^k ≤ (2*h)^k := Real.rpow_le_rpow hy hyh (by linarith)
    _ = (2 : ℝ)^k*h^k := Real.mul_rpow (by norm_num) hh.le
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_le_one hh.le hh1 hk) (by positivity)

lemma omitted_targets_cover {F : ℂ → ℂ} {k L R δ : ℝ}
    (hk : 1 ≤ k) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hcell : ∀ h x y x' : ℝ, ∀ ξ : ℂ, 0 < h → h ≤ y → y ≤ 2*h → |x'-x| ≤ h →
      ξ ∉ F '' {z : ℂ | 0 < z.im} →
      ‖F (x'+h*Complex.I)-ξ‖ ≤ L*‖F (x+y*Complex.I)-ξ‖)
    (htrace : ∀ K : Set ℂ, IsCompact K → ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ ε : ℝ, 0 < ε →
      volume {x : ℝ | F (x+ε*Complex.I) ∈ K} ≤ C) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      volume (omittedTargets F k R δ h) ≤ C*ENNReal.ofReal h := by
  let D := L*(2 : ℝ)^k/δ
  have hD : 0 ≤ D := div_nonneg (mul_nonneg hL (by positivity)) hδ.le
  let K := Metric.closedBall (0 : ℂ) (R+D)
  obtain ⟨C,hC,hCt⟩ := htrace K (isCompact_closedBall _ _)
  refine ⟨ENNReal.ofReal (Real.pi*D^2)*C, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC,fun h hh hh1 => ?_⟩
  let W : Set ℤ := {j | ∃ ξ ∈ omittedTargets F k R δ h,
    ∃ x y : ℝ, x ∈ realCell h j ∧ h ≤ y ∧ y ≤ 2*h ∧ ‖F (x+y*Complex.I)-ξ‖ ≤ y^k/δ}
  let center (j : ℤ) := F ((((j : ℝ)+1/2)*h : ℝ)+h*Complex.I)
  have hb {j : ℤ} {ξ : ℂ} (hξ : ξ ∈ omittedTargets F k R δ h)
      {x y x' : ℝ} (hx : x ∈ realCell h j) (hy : h ≤ y) (hyy : y ≤ 2*h)
      (hFw : ‖F (x+y*Complex.I)-ξ‖ ≤ y^k/δ) (hx' : x' ∈ realCell h j) :
      ‖F (x'+h*Complex.I)-ξ‖ ≤ D*h := by
    have ht := hcell h x y x' ξ hh hy hyy (realCell_length_bound hh hx hx') hξ.1
    have hp := div_le_div_of_nonneg_right (slab_power_bound hk hh hh1 (hh.le.trans hy) hyy) hδ.le
    have hp' := mul_le_mul_of_nonneg_left (hFw.trans hp) hL
    dsimp [D]
    calc
      _ ≤ L*((2 : ℝ)^k*h/δ) := ht.trans hp'
      _ = _ := by ring
  have hsub (j : ℤ) (hj : j ∈ W) : realCell h j ⊆ {x : ℝ | F (x+h*Complex.I) ∈ K} := by
    rcases hj with ⟨ξ,hξ,x,y,hx,hy,hyy,hFw⟩
    intro x' hx'
    have hhB := hb hξ hx hy hyy hFw hx'
    have hn := norm_add_le (F (x'+h*Complex.I)-ξ) ξ
    simp only [sub_add_cancel] at hn
    change F (x'+h*Complex.I) ∈ Metric.closedBall (0 : ℂ) (R+D)
    rw [Metric.mem_closedBall,dist_zero_right]
    nlinarith [hξ.2.1,mul_le_of_le_one_right hD hh1]
  have hcovered : omittedTargets F k R δ h ⊆ ⋃ j : W, Metric.closedBall (center j) (D*h) := by
    intro ξ hξ
    obtain ⟨x,y,hy,hyy,hFw⟩ := hξ.2.2
    let j : ℤ := ⌊x/h⌋
    have hx : x ∈ realCell h j := mem_realCell_floor hh _
    have hj : j ∈ W := ⟨ξ,hξ,x,y,hx,hy,hyy,hFw⟩
    apply mem_iUnion.mpr
    refine ⟨⟨j,hj⟩,?_⟩
    rw [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev]
    change ‖F ((((j : ℝ)+1/2)*h : ℝ)+h*Complex.I)-ξ‖ ≤ D*h
    exact hb (x' := ((j : ℝ)+1/2)*h) hξ hx hy hyy hFw (by constructor <;> nlinarith)
  calc
    _ ≤ volume (⋃ j : W, Metric.closedBall (center j) (D*h)) := measure_mono hcovered
    _ ≤ (ENNReal.ofReal (Real.pi*(D*h)^2)/ENNReal.ofReal h)*C :=
      cell_target_cover_bound hh (mul_nonneg hD hh.le) W center hsub (hCt h hh)
    _ = _ := by
      rw [← ENNReal.ofReal_div_of_pos hh]
      have he : Real.pi*(D*h)^2/h = (Real.pi*D^2)*h := by field_simp
      rw [he,ENNReal.ofReal_mul (by positivity)]
      ring

lemma ae_omitted_positive_superlevel_height {F : ℂ → ℂ} {k L R δ : ℝ}
    (hk : 1 ≤ k) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hcell : ∀ h x y x' : ℝ, ∀ ξ : ℂ, 0 < h → h ≤ y → y ≤ 2*h → |x'-x| ≤ h →
      ξ ∉ F '' {z : ℂ | 0 < z.im} →
      ‖F (x'+h*Complex.I)-ξ‖ ≤ L*‖F (x+y*Complex.I)-ξ‖)
    (htrace : ∀ K : Set ℂ, IsCompact K → ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ ε : ℝ, 0 < ε →
      volume {x : ℝ | F (x+ε*Complex.I) ∈ K} ≤ C) :
    ∀ᵐ ξ : ℂ, ξ ∉ F '' {z : ℂ | 0 < z.im} → ‖ξ‖ ≤ R →
      ∃ η : ℝ, 0 < η ∧ ∀ z : ℂ, 0 < z.im →
        ‖F z-ξ‖ ≤ z.im^k/δ → η ≤ z.im := by
  obtain ⟨C,hC,hCb⟩ := omitted_targets_cover hk hL hδ hcell htrace (R := R)
  have hae := ae_eventually_outside_geometric_covers hC
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
    (E := fun n => omittedTargets F k R δ (dyadicHeight n))
    (fun n => hCb _ (dyadicHeight_pos n) (dyadicHeight_le_one n))
  filter_upwards [hae] with ξ hξ
  intro ho hR
  obtain ⟨N,hN⟩ := eventually_atTop.mp hξ
  refine ⟨dyadicHeight N,dyadicHeight_pos N,fun z hz hzw => ?_⟩
  by_contra! hh
  obtain ⟨n,hn,hy,hyy⟩ := small_height_dyadic_slab N hz hh
  apply hN n hn
  refine ⟨ho,hR,z.re,z.im,hy,hyy,?_⟩
  simpa only [Complex.re_add_im] using hzw

lemma ae_positive_superlevel_height {F : ℂ → ℂ} {k L : ℝ}
    (hk : 1 ≤ k) (hL : 0 ≤ L)
    (hi : InjOn F {z : ℂ | 0 < z.im})
    (hopen : ∀ z : ℂ, 0 < z.im → map F (𝓝 z) = 𝓝 (F z))
    (hcell : ∀ h x y x' : ℝ, ∀ ξ : ℂ, 0 < h → h ≤ y → y ≤ 2*h → |x'-x| ≤ h →
      ξ ∉ F '' {z : ℂ | 0 < z.im} →
      ‖F (x'+h*Complex.I)-ξ‖ ≤ L*‖F (x+y*Complex.I)-ξ‖)
    (htrace : ∀ K : Set ℂ, IsCompact K → ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ ε : ℝ, 0 < ε →
      volume {x : ℝ | F (x+ε*Complex.I) ∈ K} ≤ C) :
    ∀ᵐ ξ : ℂ, ∀ δ : ℝ, 0 < δ →
      ∃ η : ℝ, 0 < η ∧ ∀ z : ℂ, 0 < z.im →
        ‖F z-ξ‖ ≤ z.im^k/δ → η ≤ z.im := by
  have hae : ∀ᵐ ξ : ℂ, ∀ R n : ℕ,
      ξ ∉ F '' {z : ℂ | 0 < z.im} → ‖ξ‖ ≤ R →
      ∃ η : ℝ, 0 < η ∧ ∀ z : ℂ, 0 < z.im →
        ‖F z-ξ‖ ≤ z.im^k/(1/(n+1 : ℝ)) → η ≤ z.im := by
    apply ae_all_iff.mpr
    intro R
    apply ae_all_iff.mpr
    intro n
    exact ae_omitted_positive_superlevel_height hk hL (by positivity) hcell htrace
  filter_upwards [hae] with ξ hξ
  intro δ hδ
  by_cases ho : ξ ∈ F '' {z : ℂ | 0 < z.im}
  · exact interior_positive_superlevel_height (by linarith) hδ hi hopen ho
  obtain ⟨R,hR⟩ := exists_nat_ge ‖ξ‖
  obtain ⟨n,hn⟩ := exists_nat_gt (1/δ)
  have hn0 : 0 < (n+1 : ℝ) := by positivity
  have hnδ : 1/(n+1 : ℝ) ≤ δ := by
    apply (div_le_iff₀ hn0).mpr
    have hh := (div_lt_iff₀ hδ).mp hn
    nlinarith
  obtain ⟨η,hη,hηb⟩ := hξ R n ho hR
  refine ⟨η,hη,fun z hz hzw => ?_⟩
  exact hηb z hz (hzw.trans (div_le_div_of_nonneg_left (Real.rpow_nonneg hz.le _) (by positivity) hnδ))

lemma ae_positive_superlevel_compact {F : ℂ → ℂ} {k L : ℝ}
    (hk : 1 ≤ k) (hL : 0 ≤ L)
    (hc : ContinuousOn F {z : ℂ | 0 < z.im})
    (hi : InjOn F {z : ℂ | 0 < z.im})
    (hopen : ∀ z : ℂ, 0 < z.im → map F (𝓝 z) = 𝓝 (F z))
    (ht : HasQuarticTail F (4*k))
    (hp : ∀ K : Set ℂ, IsCompact K → ∀ η : ℝ, 0 < η →
      IsCompact ({z : ℂ | η ≤ z.im} ∩ F ⁻¹' K))
    (hcell : ∀ h x y x' : ℝ, ∀ ξ : ℂ, 0 < h → h ≤ y → y ≤ 2*h → |x'-x| ≤ h →
      ξ ∉ F '' {z : ℂ | 0 < z.im} →
      ‖F (x'+h*Complex.I)-ξ‖ ≤ L*‖F (x+y*Complex.I)-ξ‖)
    (htrace : ∀ K : Set ℂ, IsCompact K → ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ ε : ℝ, 0 < ε →
      volume {x : ℝ | F (x+ε*Complex.I) ∈ K} ≤ C) :
    ∀ᵐ ξ : ℂ, ∀ δ : ℝ, 0 < δ → IsCompact (closedPositiveSuperlevel F k δ ξ) := by
  filter_upwards [ae_positive_superlevel_height hk hL hi hopen hcell htrace] with ξ hξ
  intro δ hδ
  exact positive_superlevel_compact (by linarith) hδ hc ht hp (hξ δ hδ)

lemma class_ae_compact_superlevels (g : DiskClass) {β : ℝ} (hβ : 1 < β)
    (hfin : (∫⁻ z in outsideCore,
      ENNReal.ofReal (z.im^(β+1)*‖classFun g z‖⁻¹^4)) < ∞) :
    ∀ᵐ ξ : ℂ, ∀ δ : ℝ, 0 < δ →
      IsCompact (closedPositiveSuperlevel (classFun g) ((β+3)/4) δ ξ) := by
  obtain ⟨M,hM,hMb⟩ := uniform_relative_class_bound
  have ht : HasQuarticTail (classFun g) (4*((β+3)/4)) := by
    convert class_quartic_tail g hβ hfin using 1; ring
  apply ae_positive_superlevel_compact (by linarith : 1 ≤ (β+3)/4)
    (by linarith : 0 ≤ 1+4*M) (classFun_schlicht g).1.1.continuousOn
    (classFun_schlicht g).1.2 _ ht
    (fun _ hK _ hη => class_proper_preimage g hβ hfin hK hη)
    (fun _ _ _ _ _ hh hy hyy hxx hξ => class_omitted_cell_bound hM hMb g hh hy hyy hxx hξ)
    (fun _ hK => class_trace_bound g hβ hfin hK)
  intro z hz
  have hd := ((classFun_schlicht g).1.1.analyticAt (isOpen_halfPlane.mem_nhds hz)).contDiffAt (n := 1)
  exact (hd.hasStrictDerivAt (by norm_num)).map_nhds_eq
    (univalent_deriv_ne_zero isOpen_halfPlane (classFun_schlicht g).1 hz)

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.GoodPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun

lemma compact_sublevels_iff_exhaustion.{u_1} {X : Type u_1} [TopologicalSpace X] [T2Space X]
    (K : CompactExhaustion X) {f : X → ℝ} (hf : Continuous f) :
    (∀ r : ℝ, IsCompact {x | f x ≤ r}) ↔
      ∀ n : ℕ, ∃ m : ℕ, ∀ x : X, x ∉ K m → (n : ℝ) ≤ f x := by
  constructor
  · intro h n
    obtain ⟨m,hm⟩ := K.exists_superset_of_isCompact (h n)
    refine ⟨m,fun x hx => ?_⟩
    by_contra! hh
    exact hx (hm hh.le)
  · intro h r
    obtain ⟨n,hn⟩ := exists_nat_gt r
    obtain ⟨m,hm⟩ := h n
    apply (K.isCompact m).of_isClosed_subset (isClosed_le hf continuous_const)
    intro x hx
    by_contra hh
    exact (not_lt_of_ge ((hm x hh).trans hx)) hn

lemma measurableSet_compact_sublevels.{u_1, u_2} {P : Type u_1} {X : Type u_2}
    [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    [TopologicalSpace X] [T2Space X] [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X]
    {f : P → X → ℝ} (hp : ∀ x, Continuous (fun p => f p x))
    (hx : ∀ p, Continuous (f p)) :
    MeasurableSet {p | ∀ r : ℝ, IsCompact {x | f p x ≤ r}} := by
  let K := CompactExhaustion.choice X
  have he : {p | ∀ r : ℝ, IsCompact {x | f p x ≤ r}} =
      ⋂ n : ℕ, ⋃ m : ℕ, ⋂ x : X, ⋂ (_ : x ∉ K m), {p | (n : ℝ) ≤ f p x} := by
    ext p
    simp only [mem_ofPred_eq,mem_iInter,mem_iUnion]
    exact compact_sublevels_iff_exhaustion K (hx p)
  rw [he]
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iUnion
  intro m
  apply IsClosed.measurableSet
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro _
  exact isClosed_le continuous_const (hp x)

lemma compact_sublevels_iff_positive.{u_1} {X : Type u_1} [TopologicalSpace X] [T2Space X]
    {f : X → ℝ} (hf : Continuous f) :
    (∀ r : ℝ, IsCompact {x | f x ≤ r}) ↔ ∀ r : ℝ, 0 < r → IsCompact {x | f x ≤ r} := by
  refine ⟨fun h r _ => h r,fun h r => ?_⟩
  exact (h (max r 1) (lt_of_lt_of_le (by norm_num) (le_max_right _ _))).of_isClosed_subset
    (isClosed_le hf continuous_const) (fun x hx => (show f x ≤ r from hx).trans (le_max_left _ _))

lemma compact_positive_superlevels_iff {F : ℂ → ℂ} (k : ℝ) (ξ : ℂ)
    (hc : ContinuousOn F halfPlane) :
    (∀ δ : ℝ, 0 < δ → IsCompact (closedPositiveSuperlevel F k δ ξ)) ↔
      ∀ r : ℝ, IsCompact {z : halfPlane | ‖F z-ξ‖/z.val.im^k ≤ r} := by
  have hy (z : halfPlane) : 0 < z.val.im^k := Real.rpow_pos_of_pos z.property k
  have hcont : Continuous (fun z : halfPlane => ‖F z-ξ‖/z.val.im^k) := by
    refine ((hc.domRestrict.sub continuous_const).norm).div ?_ (fun z => ne_of_gt (hy z))
    exact (Complex.continuous_im.comp continuous_subtype_val).rpow_const
      (fun z => Or.inl (ne_of_gt z.property))
  rw [compact_sublevels_iff_positive hcont]
  have he (r : ℝ) (hr : 0 < r) :
      Subtype.val '' {z : halfPlane | ‖F z-ξ‖/z.val.im^k ≤ r} =
        closedPositiveSuperlevel F k (1/r) ξ := by
    ext z
    simp only [mem_image,mem_ofPred_eq,closedPositiveSuperlevel]
    constructor
    · rintro ⟨w,hw,rfl⟩
      refine ⟨w.property,?_⟩
      rw [div_le_iff₀ (hy w)] at hw
      simpa only [one_div, div_inv_eq_mul, mul_comm r] using hw
    · rintro ⟨hz,hzv⟩
      refine ⟨⟨z,hz⟩,?_,rfl⟩
      rw [div_le_iff₀ (hy ⟨z,hz⟩)]
      simpa only [one_div, div_inv_eq_mul, mul_comm r] using hzv
  constructor
  · intro h r hr
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    rw [he r hr]
    exact h (1/r) (by positivity)
  · intro h δ hδ
    have hh := (h (1/δ) (by positivity)).image continuous_subtype_val
    rw [he (1/δ) (by positivity)] at hh
    simpa only [one_div_one_div] using hh

lemma measurableSet_compact_positive_superlevels.{u_1} {P : Type u_1}
    [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    {F : P → ℂ → ℂ} (hF : Continuous (fun p : P × halfPlane => F p.1 p.2)) (k : ℝ) :
    MeasurableSet {p : P × ℂ | ∀ δ : ℝ, 0 < δ →
      IsCompact (closedPositiveSuperlevel (F p.1) k δ p.2)} := by
  let f : (P × ℂ) → halfPlane → ℝ := fun p z => ‖F p.1 z-p.2‖/z.val.im^k
  have hc (p : P × ℂ) : ContinuousOn (F p.1) halfPlane := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact hF.comp (continuous_const.prodMk continuous_id)
  have he : {p : P × ℂ | ∀ δ : ℝ, 0 < δ →
      IsCompact (closedPositiveSuperlevel (F p.1) k δ p.2)} =
      {p | ∀ r : ℝ, IsCompact {z : halfPlane | f p z ≤ r}} := by
    ext p
    exact compact_positive_superlevels_iff k p.2 (hc p)
  rw [he]
  apply measurableSet_compact_sublevels
  · intro z
    exact (((hF.comp (continuous_fst.prodMk continuous_const)).sub continuous_snd).norm).div_const _
  · intro p
    refine (((hc p).domRestrict.sub continuous_const).norm).div ?_
      (fun z => ne_of_gt (Real.rpow_pos_of_pos z.property k))
    exact (Complex.continuous_im.comp continuous_subtype_val).rpow_const
      (fun z => Or.inl (ne_of_gt z.property))

lemma measurableSet_regular_parameters.{u_1, u_2, u_3} {P : Type u_1} {X : Type u_2} {Y : Type u_3}
    [TopologicalSpace P] [SigmaCompactSpace P]
    [TopologicalSpace X] [SigmaCompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [T2Space P]
    [MeasurableSpace P] [BorelSpace P] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology P] [SecondCountableTopology Y]
    {F : P → X → Y} {J : P → X → ℝ}
    (hF : Continuous (fun q : P × X => F q.1 q.2))
    (hJ : Continuous (fun q : P × X => J q.1 q.2)) :
    MeasurableSet {q : P × Y | ∀ x, F q.1 x = q.2 → J q.1 x ≠ 0} := by
  let Z : Set (P × X) := {q | J q.1 q.2 = 0}
  let M : P × X → P × Y := fun q => (q.1,F q.1 q.2)
  have hZ : IsSigmaCompact Z := isSigmaCompact_univ.of_isClosed_subset
    (isClosed_eq hJ continuous_const) (subset_univ _)
  have hM : Continuous M := continuous_fst.prodMk hF
  have him : MeasurableSet (M '' Z) := by
    obtain ⟨K,hK,he⟩ := hZ.image hM
    rw [← he]
    exact MeasurableSet.iUnion (fun n => (hK n).isClosed.measurableSet)
  have he : {q : P × Y | ∀ x, F q.1 x = q.2 → J q.1 x ≠ 0} = (M '' Z)ᶜ := by
    ext q
    constructor
    · intro h ⟨⟨p,x⟩,hx,hq⟩
      have hp : p = q.1 := congrArg Prod.fst hq
      have hf : F p x = q.2 := congrArg Prod.snd hq
      exact h x (hp ▸ hf) (hp ▸ hx)
    · intro h x hx hJx
      exact h ⟨(q.1,x),hJx,Prod.ext rfl hx⟩
  rw [he]
  exact him.compl

lemma ae_regular_values {f : ℂ → ℂ} {s : Set ℂ}
    (hf : ∀ z ∈ s, DifferentiableAt ℝ f z) :
    ∀ᵐ ξ ∂volume, ∀ z ∈ s, f z = ξ → LinearMap.det (fderiv ℝ f z).toLinearMap ≠ 0 := by
  let t : Set ℂ := {z | z ∈ s ∧ LinearMap.det (fderiv ℝ f z).toLinearMap = 0}
  have hz : volume (f '' t) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (fun z hz => (hf z hz.1).hasFDerivAt.hasFDerivWithinAt) (fun z hz => hz.2)
  filter_upwards [show ∀ᵐ ξ ∂volume, ξ ∉ f '' t from ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using hz)] with ξ hξ z hzs hfz hdet
  exact hξ ⟨z,⟨hzs,hdet⟩,hfz⟩

lemma potential_superlevel_eq_closed {f : ℂ → ℂ} {k δ : ℝ} (hk : 0 ≤ k) (hδ : 0 < δ) (ξ : ℂ) :
    {z | z ∈ halfPlane ∧ ENNReal.ofReal δ ≤ potential f k ξ z} =
      closedPositiveSuperlevel f k δ ξ := by
  ext z
  by_cases hz : z ∈ halfPlane
  · simp only [mem_ofPred_eq,closedPositiveSuperlevel,show 0 < z.im from hz,hz,true_and]
    rw [potential_ge_iff_reciprocalPotential_le hk hδ hz,reciprocalPotential,
      div_le_iff₀ (Real.rpow_pos_of_pos hz k),inv_mul_eq_div]
  · simp only [mem_ofPred_eq,hz,false_and,closedPositiveSuperlevel]
    exact iff_false_intro (fun h => hz h.1) |>.symm

lemma measurableSet_class_goodPairs {k : ℝ} (hk : 0 ≤ k) :
    MeasurableSet {p : DiskClass × ℂ | GoodPair (classFun p.1) k p.2} := by
  have hcompact := measurableSet_compact_positive_superlevels continuous_classFun_eval k
  have hregular := measurableSet_regular_parameters (F := fun g (z : halfPlane) => criticalMap (classFun g) k z) (J := fun g (z : halfPlane) => normalizedJacobian (classFun g) k z) (continuous_class_criticalMap k)
    (continuous_class_normalizedJacobian k)
  have he : {p : DiskClass × ℂ | GoodPair (classFun p.1) k p.2} =
      {p : DiskClass × ℂ | ∀ δ : ℝ, 0 < δ →
        IsCompact (closedPositiveSuperlevel (classFun p.1) k δ p.2)} ∩
      {p : DiskClass × ℂ | ∀ z : halfPlane,
        criticalMap (classFun p.1) k z = p.2 → normalizedJacobian (classFun p.1) k z ≠ 0} := by
    ext p
    simp only [mem_inter_iff,mem_ofPred_eq,GoodPair]
    constructor
    · rintro ⟨hc,hr⟩
      exact ⟨fun δ hδ => (potential_superlevel_eq_closed hk hδ p.2) ▸ hc δ hδ,
        fun z => hr z z.property⟩
    · rintro ⟨hc,hr⟩
      exact ⟨fun δ hδ => (potential_superlevel_eq_closed hk hδ p.2).symm ▸ hc δ hδ,
        fun z hz => hr ⟨z,hz⟩⟩
  rw [he]
  exact hcompact.inter hregular

lemma class_ae_goodPairs (g : DiskClass) {β : ℝ} (hβ : 1 < β)
    (hfin : (∫⁻ z in outsideCore,
      ENNReal.ofReal (z.im^(β+1)*‖classFun g z‖⁻¹^4)) < ∞) :
    ∀ᵐ ξ : ℂ, GoodPair (classFun g) ((β+3)/4) ξ := by
  have hc := class_ae_compact_superlevels g hβ hfin
  have hr := ae_regular_values (s := halfPlane)
    (fun z hz => differentiableAt_criticalMap (classFun_schlicht g).1 hz ((β+3)/4))
  filter_upwards [hc,hr] with ξ hc hr
  refine ⟨fun δ hδ => ?_,fun z hz hG => ?_⟩
  · rw [potential_superlevel_eq_closed (by linarith : 0 ≤ (β+3)/4) hδ]
    exact hc δ hδ
  · exact div_ne_zero (hr z hz hG) (pow_ne_zero _ (norm_ne_zero_iff.mpr
      (univalent_deriv_ne_zero isOpen_halfPlane (classFun_schlicht g).1 hz)))

lemma measurableSet_pairingDomain {k : ℝ} (hk : 0 ≤ k) : MeasurableSet (pairingDomain k) := by
  have hJ : Measurable (fun q : DiskClass × halfPlane => normalizedJacobian (classFun q.1) k q.2) :=
    (continuous_class_normalizedJacobian k).measurable
  have hG := (measurableSet_class_goodPairs hk).preimage (continuous_jointCriticalMap k).measurable
  change MeasurableSet {q : DiskClass × halfPlane | GoodPair (classFun q.1) k (criticalMap (classFun q.1) k q.2)} at hG
  exact (measurableSet_lt measurable_const hJ).inter hG

lemma criticalPair_eq_of_classRanks {k : ℝ} (hk : 0 < k) (q r : DiskClass × halfPlane)
    (hg : GoodPair (classFun q.1) k (criticalMap (classFun q.1) k q.2))
    (he : jointCriticalMap k r = jointCriticalMap k q)
    (hJ : normalizedJacobian (classFun r.1) k r.2 < 0)
    (hr : classRankCount k (-1) r = classRankCount k 1 q) :
    criticalPair (classFun q.1) k q.2 = r.2 := by
  rcases q with ⟨g,z⟩
  rcases r with ⟨h,w⟩
  have hp : h = g := congrArg Prod.fst he
  subst h
  have hG : criticalMap (classFun g) k w = criticalMap (classFun g) k z := congrArg Prod.snd he
  have hgw : GoodPair (classFun g) k (criticalMap (classFun g) k w) := hG ▸ hg
  rw [classRankCount_eq_heightRank hk (-1) (g,w) hgw,
    classRankCount_eq_heightRank hk 1 (g,z) hg,signedFiber_neg_one,signedFiber_one,hG] at hr
  have heq : heightRank (criticalHeight (classFun g) k) (negativeFiber (classFun g) k (criticalMap (classFun g) k z)) w =
      heightRank (criticalHeight (classFun g) k) (positiveFiber (classFun g) k (criticalMap (classFun g) k z)) z := by
    exact_mod_cast hr
  exact rankPartner_eq (criticalHeight_rank_inj (classFun_schlicht g).1 hk hg).2 ⟨w.property,hG,hJ⟩ heq

lemma measurable_criticalPair {k : ℝ} (hk : 0 < k) :
    Measurable (fun q : pairingDomain k => criticalPair (classFun q.val.1) k q.val.2) := by
  let B := Classical.choice (exists_class_branches k)
  let y : pairingDomain k → DiskClass × ℂ := fun q => jointCriticalMap k q.val
  let b : ℕ → pairingDomain k → DiskClass × halfPlane := fun n q => B.branch n (y q)
  let M : ℕ → Set (pairingDomain k) := fun n => {q | y q ∈ jointCriticalMap k '' B.part n ∧
    normalizedJacobian (classFun (b n q).1) k (b n q).2 < 0 ∧
    classRankCount k (-1) (b n q) = classRankCount k 1 q.val}
  have hym : Measurable y := (continuous_jointCriticalMap k).measurable.comp measurable_subtype_coe
  have hbm (n) : Measurable (b n) := (B.measurable_branch n).comp hym
  apply measurable_branch_selection (b := fun n q => (b n q).2.val) (M := M)
  · intro n
    exact measurable_subtype_coe.comp ((hbm n).snd)
  · intro n
    exact ((B.measurable_image n).preimage hym).inter
      ((measurableSet_lt ((continuous_class_normalizedJacobian k).measurable.comp (hbm n)) measurable_const).inter
        (measurableSet_eq_fun ((measurable_classRankCount k (-1)).comp (hbm n))
          ((measurable_classRankCount k 1).comp measurable_subtype_coe)))
  · intro q
    obtain ⟨w,hw,_,hr⟩ := exists_critical_equalRank (classFun_schlicht q.val.1).1 hk q.property.2
      (show q.val.2.val ∈ positiveFiber (classFun q.val.1) k (criticalMap (classFun q.val.1) k q.val.2) from
        ⟨q.val.2.property,rfl,q.property.1⟩)
    let r : DiskClass × halfPlane := (q.val.1,⟨w,hw.1⟩)
    have hG : jointCriticalMap k r = y q := Prod.ext rfl hw.2.1
    have hns : r ∈ nonsingularClass k := ne_of_lt hw.2.2
    obtain ⟨n,hn⟩ := mem_iUnion.mp (B.cover.symm ▸ hns)
    have hb : b n q = r := by
      dsimp [b]
      rw [← hG]
      exact B.left_inv n r hn
    refine ⟨n,⟨⟨r,hn,hG⟩,?_,?_⟩⟩
    · simpa only [hb] using hw.2.2
    · rw [hb,classRankCount_eq_heightRank hk (-1) r (by simpa only [r,hw.2.1] using q.property.2),
        classRankCount_eq_heightRank hk 1 q.val q.property.2,signedFiber_neg_one,signedFiber_one]
      simpa only [r,hw.2.1] using congrArg (fun n : ℕ => (n : ℝ≥0∞)) hr
  · intro n q hq
    exact criticalPair_eq_of_classRanks hk q.val (b n q) q.property.2
      (B.right_inv n (y q) hq.1).2 hq.2.1 hq.2.2

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.TransportBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun

lemma measurableSet_transportWindow {k : ℝ} (hk : 0 < k) (N : ℝ) :
    MeasurableSet (transportWindow k N) := by
  have hr := measurable_criticalPair hk
  have hz : Measurable (fun q : pairingDomain k => (q.val.2 : ℂ)) :=
    measurable_subtype_coe.comp (measurable_subtype_coe.snd)
  have hm : MeasurableSet {q : pairingDomain k |
      displacementWindow N q.val.2 (criticalPair (classFun q.val.1) k q.val.2)} :=
    (measurableSet_le (Complex.measurable_im.comp hz)
      (measurable_const.mul (Complex.measurable_im.comp hr))).inter
    ((measurableSet_le (Complex.measurable_im.comp hr)
      (measurable_const.mul (Complex.measurable_im.comp hz))).inter
    (measurableSet_le (((Complex.measurable_re.comp hr).sub (Complex.measurable_re.comp hz)).abs)
      (measurable_const.mul (Complex.measurable_im.comp hz))))
  have h := (measurableSet_pairingDomain hk.le).subtype_image hm
  convert h using 1
  ext q
  simp only [transportWindow,mem_ofPred_eq,mem_image,Subtype.exists,exists_prop]
  aesop

lemma displacementWindow_affine (N : ℝ) {t : ℂ} (ht : t ∈ halfPlane) (z w : ℂ) :
    displacementWindow N (affine t z) (affine t w) ↔ displacementWindow N z w := by
  have him (v : ℂ) : (affine t v).im = t.im*v.im := by simp [affine]
  have hre : (affine t w).re-(affine t z).re = t.im*(w.re-z.re) := by simp [affine]; ring
  simp only [displacementWindow,him,hre,abs_mul,abs_of_pos (show 0<t.im from ht)]
  simp only [show N*(t.im*w.im) = t.im*(N*w.im) from by ring,
    show N*(t.im*z.im) = t.im*(N*z.im) from by ring,
    mul_le_mul_iff_right₀ (show 0<t.im from ht)]

lemma transportWindow_root (g : DiskClass) {k : ℝ} (hk : 0 < k) (N : ℝ) (z : halfPlane) :
    (rerootClass g z,halfOne) ∈ transportWindow k N ↔ (g,z) ∈ transportWindow k N := by
  have hJ := class_normalizedJacobian_root g hk z
  have hG := class_goodPair_root g hk z
  change (0 < normalizedJacobian (classFun (rerootClass g z)) k Complex.I ∧
    GoodPair (classFun (rerootClass g z)) k (criticalMap (classFun (rerootClass g z)) k Complex.I)) ∧ _ ↔
    (0 < normalizedJacobian (classFun g) k z ∧ GoodPair (classFun g) k (criticalMap (classFun g) k z)) ∧ _
  rw [hJ,hG]
  apply and_congr_right
  intro h
  have he := class_criticalPair_reroot g hk z halfOne (by simpa only [halfOne,affine_I] using h.1)
    (by simpa only [halfOne,affine_I] using h.2)
  simp only [halfOne,affine_I] at he
  change displacementWindow N Complex.I (criticalPair (classFun (rerootClass g z)) k Complex.I) ↔
    displacementWindow N z (criticalPair (classFun g) k z)
  rw [← displacementWindow_affine N z.property Complex.I,affine_I,he]

lemma displacementWindow_mono {N M : ℝ} (hNM : N ≤ M) {z w : ℂ}
    (hz : z ∈ halfPlane) (hw : w ∈ halfPlane) (h : displacementWindow N z w) :
    displacementWindow M z w :=
  ⟨h.1.trans (mul_le_mul_of_nonneg_right hNM hw.le),
    h.2.1.trans (mul_le_mul_of_nonneg_right hNM hz.le),
    h.2.2.trans (mul_le_mul_of_nonneg_right hNM hz.le)⟩

lemma exists_displacementWindow {z w : ℂ} (hz : z ∈ halfPlane) (hw : w ∈ halfPlane) :
    ∃ n : ℕ, displacementWindow (n+1) z w := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max (z.im/w.im) (max (w.im/z.im) (|w.re-z.re|/z.im)))
  refine ⟨n,?_,?_,?_⟩
  · exact (div_le_iff₀ hw).mp ((le_max_left _ _).trans (by exact_mod_cast hn.le.trans (le_add_of_nonneg_right zero_le_one)))
  · exact (div_le_iff₀ hz).mp (((le_max_left _ _).trans (le_max_right _ _)).trans (by exact_mod_cast hn.le.trans (le_add_of_nonneg_right zero_le_one)))
  · exact (div_le_iff₀ hz).mp (((le_max_right _ _).trans (le_max_right _ _)).trans (by exact_mod_cast hn.le.trans (le_add_of_nonneg_right zero_le_one)))

lemma transportWindow_mono {k : ℝ} (hk : 0 < k) {N M : ℝ} (hNM : N ≤ M) :
    transportWindow k N ⊆ transportWindow k M := by
  rintro ⟨g,z⟩ ⟨hp,hw⟩
  exact ⟨hp,displacementWindow_mono hNM z.property
    (criticalPair_spec (classFun_schlicht g).1 hk z.property hp.1 hp.2).1 hw⟩

lemma iUnion_transportWindow {k : ℝ} (hk : 0 < k) :
    (⋃ n : ℕ, transportWindow k (n+1)) = pairingDomain k := by
  ext q
  constructor
  · rintro ⟨_,⟨n,rfl⟩,hq⟩
    exact hq.1
  · intro hq
    obtain ⟨n,hn⟩ := exists_displacementWindow q.2.property
      (criticalPair_spec (classFun_schlicht q.1).1 hk q.2.property hq.1 hq.2).1
    exact mem_iUnion.mpr ⟨n,hq,hn⟩

lemma transportSlice_iff (g : DiskClass) (k N : ℝ) (z : halfPlane) :
    z.val ∈ transportSlice g k N ↔ (g,z) ∈ transportWindow k N := by
  simp only [transportSlice,transportWindow,pairingDomain,mem_ofPred_eq,z.property,true_and,and_assoc]

lemma measurableSet_transportSlice (g : DiskClass) {k : ℝ} (hk : 0 < k) (N : ℝ) :
    MeasurableSet (transportSlice g k N) := by
  apply measurableSet_halfPlane_pred
  have hm : Measurable (fun z : halfPlane => (g,z)) := measurable_const.prodMk measurable_id
  have h := (measurableSet_transportWindow hk N).preimage hm
  convert h using 1
  ext z
  exact and_assoc.symm

lemma measurableSet_transportBox (R a b : ℝ) : MeasurableSet (transportBox R a b) :=
  (measurableSet_le Complex.measurable_re.abs measurable_const).inter
    ((measurableSet_le measurable_const Complex.measurable_im).inter
      (measurableSet_le Complex.measurable_im measurable_const))

lemma pair_mem_enlargedBox {N R Y : ℝ} (hN : 1 ≤ N) {z w : ℂ}
    (hz : z ∈ transportBox R 1 Y) (hw : displacementWindow N z w) :
    w ∈ transportBox (R+N*Y) (1/N) (N*Y) := by
  have hn : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hab : |w.re| ≤ |z.re|+|w.re-z.re| := by
    calc |w.re| = |z.re+(w.re-z.re)| := by congr 1; ring
         _ ≤ |z.re|+|w.re-z.re| := abs_add_le _ _
  refine ⟨hab.trans (add_le_add hz.1 (hw.2.2.trans (mul_le_mul_of_nonneg_left hz.2.2 hn.le))),?_,
    hw.2.1.trans (mul_le_mul_of_nonneg_left hz.2.2 hn.le)⟩
  rw [div_le_iff₀ hn]
  nlinarith [hw.1,hz.2.1]

lemma fiberSum_mul_indicator.{u_1, u_2} {X : Type u_1} {Y : Type u_2} (f : X → Y) (s t : Set X)
    (u : X → ℝ≥0∞) (y : Y) :
    fiberSum f s (fun x => u x * t.indicator 1 x) y = fiberSum f (s ∩ t) u y := by
  classical
  rw [fiberSum,fiberSum,tsum_subtype {x | x ∈ s ∧ f x = y} (fun x => u x * t.indicator 1 x),
    tsum_subtype {x | x ∈ s ∩ t ∧ f x = y} u]
  apply tsum_congr
  intro x
  by_cases hs : x ∈ s <;> by_cases ht : x ∈ t <;> by_cases hy : f x = y <;>
    simp [hs,ht,hy]

lemma transport_box (g : DiskClass) {β k N R Y : ℝ} (hk : 0 < k)
    (hb : β-1 = 4*(k-1)) (hN : 1 ≤ N) :
    (∫⁻ z in halfPlane, transportDensity g β z * ENNReal.ofReal (normalizedJacobian (classFun g) k z) *
      (transportSlice g k N ∩ transportBox R 1 Y).indicator 1 z) ≤
    ∫⁻ z in halfPlane, transportDensity g β z * ENNReal.ofReal (-normalizedJacobian (classFun g) k z) *
      (transportBox (R+N*Y) (1/N) (N*Y)).indicator 1 z := by
  let S := transportSlice g k N ∩ transportBox R 1 Y
  let T := transportBox (R+N*Y) (1/N) (N*Y)
  have hs : MeasurableSet S := (measurableSet_transportSlice g hk N).inter (measurableSet_transportBox R 1 Y)
  have ht : MeasurableSet T := measurableSet_transportBox _ _ _
  have hp := transport_area g β k 1 (by norm_num) (measurable_const.indicator hs : Measurable (S.indicator (1 : ℂ → ℝ≥0∞)))
  have hn := transport_area g β k (-1) (by norm_num) (measurable_const.indicator ht : Measurable (T.indicator (1 : ℂ → ℝ≥0∞)))
  simp only [one_mul] at hp
  simp only [neg_one_mul] at hn
  apply le_trans hp.le
  apply le_trans ?_ hn.symm.le
  apply lintegral_mono
  intro ξ
  apply le_trans (fiberSum_mul_indicator (criticalMap (classFun g) k) (jacobianRegion g k 1) S (targetDensity g β) ξ).le
  apply le_trans ?_ (fiberSum_mul_indicator (criticalMap (classFun g) k) (jacobianRegion g k (-1)) T (targetDensity g β) ξ).symm.le
  apply fiberSum_mono_injective (criticalPair (classFun g) k) ξ
  · intro z hz hG
    have hsz := hz.2.1
    have hpair := criticalPair_spec (classFun_schlicht g).1 hk hsz.1 hsz.2.1 hsz.2.2.1
    exact ⟨⟨⟨hpair.1,by simpa only [neg_one_mul] using neg_pos.mpr hpair.2.2.1⟩,
      pair_mem_enlargedBox hN hz.2.2 hsz.2.2.2⟩,hpair.2.1.trans hG⟩
  · apply (criticalPair_injective (classFun_schlicht g).1 hk).mono
    intro z hz
    exact ⟨hz.1.2.1.1,hz.1.2.1.2.1,hz.1.2.1.2.2.1⟩
  · intro z hz _
    exact targetDensity_le_pair g hk hb hz.2.1.1 hz.2.1.2.1 hz.2.1.2.2.1

lemma measurableSet_exceptionSlice (g : DiskClass) {k : ℝ} (hk : 0 < k) :
    MeasurableSet {z : ℂ | z ∈ halfPlane ∧ ¬GoodPair (classFun g) k (criticalMap (classFun g) k z)} := by
  apply measurableSet_halfPlane_pred
  have hm : Measurable (fun z : halfPlane => (g,criticalMap (classFun g) k z)) :=
    (continuous_const.prodMk ((continuous_class_criticalMap k).comp
      (show Continuous (fun z : halfPlane => (g,z)) from continuous_const.prodMk continuous_id))).measurable
  exact ((measurableSet_class_goodPairs hk.le).preimage hm).compl

lemma exceptional_transport_zero (g : DiskClass) {β k : ℝ} (hk : 0 < k)
    (hg : ∀ᵐ ξ : ℂ, GoodPair (classFun g) k ξ) :
    (∫⁻ z in halfPlane, transportDensity g β z * ENNReal.ofReal (normalizedJacobian (classFun g) k z) *
      {z : ℂ | z ∈ halfPlane ∧ ¬GoodPair (classFun g) k (criticalMap (classFun g) k z)}.indicator 1 z) = 0 := by
  have hs := measurableSet_exceptionSlice g hk
  have he := transport_area g β k 1 (by norm_num)
    (measurable_const.indicator hs : Measurable ({z : ℂ | z ∈ halfPlane ∧ ¬GoodPair (classFun g) k (criticalMap (classFun g) k z)}.indicator (1 : ℂ → ℝ≥0∞)))
  simp only [one_mul] at he
  refine he.trans ?_
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hg] with ξ hξ
  unfold fiberSum
  apply ENNReal.tsum_eq_zero.mpr
  intro z
  have hn : z.val ∉ {z : ℂ | z ∈ halfPlane ∧ ¬GoodPair (classFun g) k (criticalMap (classFun g) k z)} := by
    rintro ⟨_,hbad⟩
    exact hbad (z.property.2.symm ▸ hξ)
  exact (congrArg (targetDensity g β z * ·) (indicator_of_notMem (f := (1 : ℂ → ℝ≥0∞)) hn)).trans (mul_zero _)

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.ExpectedDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun
attribute [local irreducible] rerootClass

lemma halfRetract_of_mem {z : ℂ} (hz : z ∈ halfPlane) : halfRetract z = ⟨z,hz⟩ := by
  simp only [halfRetract,dite_eq_left hz]

lemma measurable_halfRetract : Measurable halfRetract := by
  have hm : Measurable (fun z : ℂ => (halfRetract z : ℂ)) := by
    have he : (fun z : ℂ => (halfRetract z : ℂ)) = (fun z => if z ∈ halfPlane then z else Complex.I) := by
      funext z
      by_cases hz : z ∈ halfPlane <;> simp [halfRetract,halfOne,hz]
    rw [he]
    exact measurable_id.piecewise isOpen_halfPlane.measurableSet measurable_const
  exact hm.subtype_mk

lemma measurable_averagedDensity (β : ℝ) {Φ : DiskClass → ℝ≥0∞} (hΦ : Measurable Φ) :
    Measurable (averagedDensity β Φ) := by
  have hm : Measurable (fun p : DiskClass × ℂ => (p.1,halfRetract p.2)) :=
    measurable_fst.prodMk (measurable_halfRetract.comp measurable_snd)
  exact ((((Complex.measurable_im.comp measurable_snd).pow_const (β-1)).ennreal_ofReal.mul
    (continuous_classWeight.measurable.comp hm).ennreal_ofReal).mul
    (hΦ.comp (continuous_rerootClass.measurable.comp hm))).indicator
      (isOpen_halfPlane.measurableSet.preimage measurable_snd)

lemma averagedDensity_of_mem (β : ℝ) (Φ : DiskClass → ℝ≥0∞) (g : DiskClass) (z : halfPlane) :
    averagedDensity β Φ (g,z) = transportDensity g β z * Φ (rerootClass g z) := by
  rw [averagedDensity,indicator_of_mem (show (g,(z : ℂ)) ∈ {p : DiskClass × ℂ | p.2 ∈ halfPlane} from z.property)]
  simp only [halfRetract_of_mem z.property]
  rw [transportDensity,ENNReal.ofReal_mul (Real.rpow_nonneg z.property.le _)]
  simp only [classWeight]

lemma weighted_averagedDensity (P : ProbabilityMeasure DiskClass) (β : ℝ)
    (hP : ∀ z : halfPlane, ∀ f : DiskClass → ℝ≥0∞, Measurable f →
      (∫⁻ g, ENNReal.ofReal (classWeight g z)*f (rerootClass g z) ∂(P : Measure DiskClass)) =
        ENNReal.ofReal (z.val.im^(-β))*(∫⁻ g, f g ∂(P : Measure DiskClass)))
    {Φ : DiskClass → ℝ≥0∞} (hΦ : Measurable Φ) (z : halfPlane) :
    (∫⁻ g, averagedDensity β Φ (g,z) ∂(P : Measure DiskClass)) =
      ENNReal.ofReal (z.val.im⁻¹) * ∫⁻ g, Φ g ∂(P : Measure DiskClass) := by
  have hm : Measurable (fun g : DiskClass => ENNReal.ofReal (classWeight g z)*Φ (rerootClass g z)) := by
    have hp : Measurable (fun g : DiskClass => (g,z)) := measurable_id.prodMk measurable_const
    exact ((continuous_classWeight.measurable.comp hp).ennreal_ofReal).mul
      (hΦ.comp (continuous_rerootClass.measurable.comp hp))
  have he : (fun g : DiskClass => averagedDensity β Φ (g,z)) =
      fun g => ENNReal.ofReal (z.val.im^(β-1)) *
        (ENNReal.ofReal (classWeight g z)*Φ (rerootClass g z)) := by
    funext g
    rw [averagedDensity,indicator_of_mem (show (g,(z : ℂ)) ∈ {p : DiskClass × ℂ | p.2 ∈ halfPlane} from z.property)]
    simp only [halfRetract_of_mem z.property,mul_assoc]
  rw [he,lintegral_const_mul _ hm,hP z Φ hΦ,← mul_assoc,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg z.property.le _),← Real.rpow_add z.property]
  congr 2
  rw [show β-1 + -β = (-1 : ℝ) from by ring,Real.rpow_neg_one]

lemma root_test_zero_of_averaging (P : ProbabilityMeasure DiskClass) (β : ℝ)
    (hP : ∀ z : halfPlane, ∀ f : DiskClass → ℝ≥0∞, Measurable f →
      (∫⁻ g, ENNReal.ofReal (classWeight g z)*f (rerootClass g z) ∂(P : Measure DiskClass)) =
        ENNReal.ofReal (z.val.im^(-β))*(∫⁻ g, f g ∂(P : Measure DiskClass)))
    {Φ : DiskClass → ℝ≥0∞} (hΦ : Measurable Φ)
    (hzero : ∀ᵐ g ∂(P : Measure DiskClass), (∫⁻ z in halfPlane, averagedDensity β Φ (g,z)) = 0) :
    (∫⁻ g, Φ g ∂(P : Measure DiskClass)) = 0 := by
  have hm := measurable_averagedDensity β hΦ
  have hz : (∫⁻ z in halfPlane, ∫⁻ g, averagedDensity β Φ (g,z) ∂(P : Measure DiskClass)) = 0 :=
    (lintegral_lintegral_swap (f := fun g z => averagedDensity β Φ (g,z)) (μ := (P : Measure DiskClass)) (ν := volume.restrict halfPlane) hm.aemeasurable).symm.trans (lintegral_eq_zero_of_ae_eq_zero hzero)
  have ha := (lintegral_eq_zero_iff hm.lintegral_prod_left').mp hz
  have : (ae (volume.restrict halfPlane)).NeBot := ae_restrict_neBot.mpr
    (ne_of_gt (isOpen_halfPlane.measure_pos volume ⟨Complex.I,by simp [halfPlane]⟩))
  obtain ⟨z,hz,hz0⟩ := ((ae_restrict_mem isOpen_halfPlane.measurableSet).and ha).exists
  have he := weighted_averagedDensity P β hP hΦ ⟨z,hz⟩
  change (∫⁻ g, averagedDensity β Φ (g,z) ∂(P : Measure DiskClass)) = 0 at hz0
  exact (mul_eq_zero.mp (he.symm.trans hz0)).resolve_left (ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr hz)))

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.InverseDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun
attribute [local irreducible] rerootClass

lemma affineInverse_re (z : ℂ) : (affineInverse z).re = -z.re/z.im := by
  simp [affineInverse,Complex.div_ofReal_re]

lemma affineInverse_im (z : ℂ) : (affineInverse z).im = z.im⁻¹ := by
  simp [affineInverse,Complex.div_ofReal_im]

lemma affineInverse_mem {z : ℂ} (hz : z ∈ halfPlane) : affineInverse z ∈ halfPlane := by
  simpa only [halfPlane,mem_ofPred_eq,affineInverse_im] using inv_pos.mpr hz

lemma affineInverse_invol {z : ℂ} (hz : z ∈ halfPlane) : affineInverse (affineInverse z) = z := by
  have hn : z.im ≠ 0 := ne_of_gt hz
  apply Complex.ext
  · simp only [affineInverse_re,affineInverse_im,neg_div,neg_neg,div_inv_eq_mul]
    exact div_mul_cancel₀ _ hn
  · simp only [affineInverse_im,inv_inv]

lemma affineInverse_injOn : InjOn affineInverse halfPlane := by
  intro z hz w hw he
  simpa only [affineInverse_invol hz,affineInverse_invol hw] using congrArg affineInverse he

lemma affineInverse_affine {z : ℂ} (hz : z ∈ halfPlane) : affine z (affineInverse z) = Complex.I := by
  have hn : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  rw [affine,affineInverse,mul_div_cancel₀ _ hn]
  ring

lemma hasFDerivAt_affineInverse {z : ℂ} (hz : z ∈ halfPlane) :
    HasFDerivAt affineInverse
      (((z.im : ℂ)⁻¹) • (-(Complex.ofRealCLM.comp Complex.reCLM)) +
        (-(z.re : ℂ)+Complex.I) •
          ((-((z.im : ℂ)^2)⁻¹) • (Complex.ofRealCLM.comp Complex.imCLM))) z := by
  have hn : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hi := (hasFDerivAt_inv' (𝕜 := ℝ) hn).comp z
    (Complex.ofRealCLM.comp Complex.imCLM).hasFDerivAt
  have h := ((Complex.ofRealCLM.comp Complex.reCLM).hasFDerivAt.neg.add_const Complex.I).mul hi
  convert! h using 1
  ext v
  simp only [add_apply,smul_apply,neg_apply,Pi.neg_apply,ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply,Complex.reCLM_apply,Complex.imCLM_apply,
    ContinuousLinearMap.mulLeftRight_apply,Function.comp_apply,smul_eq_mul]
  ring

lemma differentiableAt_affineInverse {z : ℂ} (hz : z ∈ halfPlane) : DifferentiableAt ℝ affineInverse z :=
  (hasFDerivAt_affineInverse hz).differentiableAt

lemma fderiv_affineInverse_apply {z : ℂ} (hz : z ∈ halfPlane) (v : ℂ) :
    fderiv ℝ affineInverse z v =
      (-(v.re : ℂ)*(z.im : ℂ)-(-(z.re : ℂ)+Complex.I)*(v.im : ℂ))/(z.im : ℂ)^2 := by
  have hn : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  rw [(hasFDerivAt_affineInverse hz).fderiv]
  simp only [add_apply,smul_apply,neg_apply,
    ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,Complex.reCLM_apply,Complex.imCLM_apply,
    smul_eq_mul]
  field_simp
  ring

lemma det_affineInverse {z : ℂ} (hz : z ∈ halfPlane) :
    (fderiv ℝ affineInverse z).det = z.im⁻¹^3 := by
  change LinearMap.det (fderiv ℝ affineInverse z).toLinearMap = _
  rw [determinant_complex_real]
  change (fderiv ℝ affineInverse z 1).re*(fderiv ℝ affineInverse z Complex.I).im-
    (fderiv ℝ affineInverse z Complex.I).re*(fderiv ℝ affineInverse z 1).im = _
  rw [fderiv_affineInverse_apply hz,fderiv_affineInverse_apply hz]
  simp only [Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im,Complex.ofReal_one,
    Complex.ofReal_zero,neg_zero,zero_mul,mul_zero,mul_one,sub_zero,zero_sub,neg_mul,
    ← Complex.ofReal_pow,Complex.div_ofReal_re,Complex.div_ofReal_im,
    Complex.neg_re,Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im]
  field_simp [ne_of_gt (show 0 < z.im from hz)]
  ring

lemma affineInverse_change_variables {s : Set ℂ} (hs : MeasurableSet s) (hsub : s ⊆ halfPlane)
    (hInv : affineInverse '' s = s) (f : ℂ → ℝ≥0∞) :
    (∫⁻ z in s, f z ∂volume) = ∫⁻ z in s, ENNReal.ofReal (z.im⁻¹^3)*f (affineInverse z) ∂volume := by
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun z hz => (differentiableAt_affineInverse (hsub hz)).hasFDerivAt.hasFDerivWithinAt)
    (affineInverse_injOn.mono hsub) f
  rw [hInv] at h
  refine h.trans (setLIntegral_congr_fun hs (fun z hz => ?_))
  rw [det_affineInverse (hsub hz),abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (hsub hz).le) _)]

lemma diskCayley_affineInverse {z : ℂ} (hz : z ∈ halfPlane) :
    diskCayley (affineInverse z) = (z-Complex.I)/(star (z+Complex.I)) := by
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have h₁ : affineInverse z-Complex.I = -(z-Complex.I)/(z.im : ℂ) := by
    rw [affineInverse,div_sub' hy]
    congr 1
    apply Complex.ext <;> simp
  have h₂ : affineInverse z+Complex.I = -star (z+Complex.I)/(z.im : ℂ) := by
    rw [affineInverse,div_add' _ _ _ hy]
    congr 1
    apply Complex.ext <;> simp
  rw [diskCayley,h₁,h₂,div_div_div_cancel_right₀ hy,neg_div_neg_eq]

lemma diskCayley_affineInverse_norm {z : ℂ} (hz : z ∈ halfPlane) :
    ‖diskCayley (affineInverse z)‖ = ‖diskCayley z‖ := by
  rw [diskCayley_affineInverse hz,diskCayley,norm_div,norm_div,norm_star]

lemma affineInverse_mem_outsideCore {z : ℂ} (hz : z ∈ outsideCore) : affineInverse z ∈ outsideCore :=
  ⟨affineInverse_mem hz.1,by simpa only [diskCayley_affineInverse_norm hz.1] using hz.2⟩

lemma affineInverse_image_outsideCore : affineInverse '' outsideCore = outsideCore := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact affineInverse_mem_outsideCore hw
  · intro hz
    exact ⟨affineInverse z,affineInverse_mem_outsideCore hz,affineInverse_invol hz.1⟩

lemma reroot_at_affineInverse (g : DiskClass) {z : ℂ} (hz : z ∈ halfPlane) :
    classFun (rerootClass g ⟨z,hz⟩) (affineInverse z) =
      -classFun g z/((z.im : ℂ)*deriv (classFun g) z) := by
  rw [classFun_rerootClass g ⟨z,hz⟩ (affineInverse_mem hz)]
  simp only [reroot,affineInverse_affine hz,(classFun_schlicht g).2.1,zero_sub]

lemma classWeight_inverse_value (g : DiskClass) {z : ℂ} (hz : z ∈ outsideCore) :
    classWeight g ⟨z,hz.1⟩ *
      ‖classFun (rerootClass g ⟨z,hz.1⟩) (affineInverse z)‖⁻¹^4 =
    z.im^4*(‖deriv (classFun g) z‖^2*‖classFun g z‖⁻¹^4) := by
  have hn := classFun_ne_zero_outsideCore g hz
  have hd := univalent_deriv_ne_zero isOpen_halfPlane (classFun_schlicht g).1 hz.1
  have hy : 0 < z.im := hz.1
  rw [classWeight,reciprocalDeriv,reroot_at_affineInverse g hz.1]
  simp only [norm_inv,norm_div,norm_neg,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hy]
  field_simp

lemma inverse_area_bound {f : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    (hf : ∀ z ∈ s, DifferentiableAt ℂ f z) (hi : InjOn f s)
    (hmin : ∀ z ∈ s, (1/16 : ℝ) ≤ ‖f z‖) :
    (∫⁻ z in s, ENNReal.ofReal (‖deriv f z‖^2*‖f z‖⁻¹^4)) ≤
      ENNReal.ofReal (256*Real.pi) := by
  have hn (z : ℂ) (hz : z ∈ s) : f z ≠ 0 := by
    have := hmin z hz
    exact norm_ne_zero_iff.mp (ne_of_gt (by linarith))
  have hd (z : ℂ) (hz : z ∈ s) := (hf z hz).hasDerivAt.inv (hn z hz)
  have hhi : InjOn (fun z => (f z)⁻¹) s := by
    intro z hz w hw he
    exact hi hz hw (inv_inj.mp he)
  have he := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun z hz => ((hd z hz).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hhi (fun _ => (1 : ℝ≥0∞))
  have hJac (z : ℂ) (hz : z ∈ s) :
      |(fderiv ℝ (fun z => (f z)⁻¹) z).det| = ‖deriv f z‖^2*‖f z‖⁻¹^4 := by
    have hdet : (fderiv ℝ (fun z => (f z)⁻¹) z).det = ‖deriv (fun z => (f z)⁻¹) z‖^2 := by
      exact det_fderiv_complex (hd z hz).differentiableAt
    rw [hdet,abs_of_nonneg (sq_nonneg _)]
    have hdr : deriv (fun z => (f z)⁻¹) z = -deriv f z/f z^2 := (hd z hz).deriv
    rw [hdr]
    change ‖(-deriv f z/f z^2 : ℂ)‖^2 = ‖deriv f z‖^2*‖f z‖⁻¹^4
    rw [Complex.norm_div,norm_neg,Complex.norm_pow]
    simp only [div_eq_mul_inv,inv_pow]
    ring
  have he' : (∫⁻ z in s, ENNReal.ofReal (‖deriv f z‖^2*‖f z‖⁻¹^4)) =
      volume ((fun z => (f z)⁻¹) '' s) := by
    simp only [lintegral_const,one_mul,Measure.restrict_apply_univ] at he
    change _ = volume (f⁻¹ '' s)
    rw [he]
    apply setLIntegral_congr_fun hs
    intro z hz
    dsimp only
    rw [mul_one]
    have hfm := (hd z hz).hasFDerivAt.restrictScalars ℝ
    have hh : (ContinuousLinearMap.restrictScalars ℝ
        (ContinuousLinearMap.toSpanSingleton ℂ (-deriv f z/f z^2))) =
        fderiv ℝ (fun z => (f z)⁻¹) z := by
      exact hfm.fderiv.symm
    rw [hh,hJac z hz]
  rw [he']
  have hsub : (fun z => (f z)⁻¹) '' s ⊆ Metric.closedBall 0 16 := by
    rintro _ ⟨z,hz,rfl⟩
    simp only [Metric.mem_closedBall,dist_zero_right,norm_inv]
    exact (inv_le_comm₀ (norm_pos_iff.mpr (hn z hz)) (by norm_num)).mpr (by simpa using hmin z hz)
  calc
    _ ≤ volume (Metric.closedBall (0 : ℂ) 16) := measure_mono hsub
    _ = _ := by
      rw [Complex.volume_closedBall]
      have hp : (NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
        rw [ENNReal.ofReal,ENNReal.coe_inj]
        apply Subtype.ext
        exact (Real.coe_toNNReal Real.pi Real.pi_pos.le).symm
      rw [hp,ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 256)]
      norm_num [mul_comm]

lemma measurable_planeClassDeriv : Measurable (fun p : DiskClass × ℂ => planeClassDeriv p.1 p.2) := by
  classical
  let s : Set (DiskClass × ℂ) := Prod.snd ⁻¹' halfPlane
  have hc : Continuous (fun p : s => deriv (classFun p.val.1) p.val.2) := by
    have h : Continuous (fun p : DiskClass × halfPlane => deriv (classFun p.1) p.2) := by
      simpa only [iteratedDeriv_one] using continuous_classJet_eval 1
    exact h.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun p => p.2)))
  simpa only [planeClassDeriv,s,Set.mem_preimage,dite_eq_ite] using
    hc.measurable.dite (measurable_const (a := (0 : ℂ)))
      (isOpen_halfPlane.measurableSet.preimage measurable_snd)

lemma planeClassDeriv_eq (g : DiskClass) {z : ℂ} (hz : z ∈ halfPlane) :
    planeClassDeriv g z = deriv (classFun g) z := by simp [planeClassDeriv,hz]

lemma measurable_inverseDensity : Measurable (Function.uncurry inverseDensity) :=
  (measurable_planeClassValue.norm.inv.pow_const 4).ennreal_ofReal

lemma measurable_inverseJacDensity : Measurable (Function.uncurry inverseJacDensity) :=
  ((measurable_planeClassDeriv.norm.pow_const 2).mul
    (measurable_planeClassValue.norm.inv.pow_const 4)).ennreal_ofReal

lemma measurable_weightedInverseArea (β : ℝ) : Measurable (weightedInverseArea β) := by
  apply Measurable.lintegral_prod_right
  exact (((Complex.continuous_im.comp continuous_snd).measurable.pow measurable_const).ennreal_ofReal).mul
    measurable_inverseDensity

lemma inverseJacDensity_integral_le (g : DiskClass) :
    (∫⁻ z in outsideCore, inverseJacDensity g z) ≤ ENNReal.ofReal (256*Real.pi) := by
  have he : (∫⁻ z in outsideCore, inverseJacDensity g z) =
      ∫⁻ z in outsideCore, ENNReal.ofReal (‖deriv (classFun g) z‖^2*‖classFun g z‖⁻¹^4) := by
    apply setLIntegral_congr_fun measurableSet_outsideCore
    intro z hz
    simp only [inverseJacDensity,planeClassValue_eq g hz.1,planeClassDeriv_eq g hz.1]
  rw [he]
  exact inverse_area_bound measurableSet_outsideCore
    (fun _ hz => (classFun_schlicht g).1.1.differentiableAt (isOpen_halfPlane.mem_nhds hz.1))
    ((classFun_schlicht g).1.2.mono (fun _ h => h.1))
    (fun _ hz => classFun_lower_outsideCore g hz)

attribute [local irreducible] inverseDensity inverseJacDensity

lemma weighted_inverse_identity (P : ProbabilityMeasure DiskClass) (β : ℝ)
    (hP : HasWeightedLaw P β) {z : ℂ} (hz : z ∈ outsideCore) :
    (∫⁻ g, inverseJacDensity g z ∂(P : Measure DiskClass)) =
      ENNReal.ofReal (z.im^(-β-4)) *
        (∫⁻ g, inverseDensity g (affineInverse z) ∂(P : Measure DiskClass)) := by
  have hy : 0 < z.im := hz.1
  have hden : Measurable (fun g => inverseDensity g (affineInverse z)) :=
    measurable_inverseDensity.comp (measurable_id.prodMk measurable_const)
  have he := hP ⟨z,hz.1⟩ _ hden
  have hid (g : DiskClass) :
      ENNReal.ofReal (classWeight g ⟨z,hz.1⟩)*inverseDensity (rerootClass g ⟨z,hz.1⟩) (affineInverse z) =
        ENNReal.ofReal (z.im^4)*inverseJacDensity g z := by
    simp only [inverseDensity,inverseJacDensity,planeClassValue_eq _ (affineInverse_mem hz.1),
      planeClassValue_eq _ hz.1,planeClassDeriv_eq _ hz.1]
    rw [← ENNReal.ofReal_mul (classWeight_pos g ⟨z,hz.1⟩).le,
      classWeight_inverse_value g hz,ENNReal.ofReal_mul (pow_nonneg hy.le 4)]
  simp_rw [hid] at he
  have hJac : Measurable (fun g => inverseJacDensity g z) :=
    measurable_inverseJacDensity.comp (measurable_id.prodMk measurable_const)
  rw [lintegral_const_mul _ hJac] at he
  have hpow : ENNReal.ofReal (z.im^4) * ENNReal.ofReal (z.im^(-β-4)) = ENNReal.ofReal (z.im^(-β)) := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hy.le 4),← Real.rpow_natCast,← Real.rpow_add hy]
    congr 1
    congr 1
    ring
  apply (ENNReal.mul_right_inj (by positivity : ENNReal.ofReal (z.im^4) ≠ 0) ENNReal.ofReal_ne_top).mp
  rw [← mul_assoc,hpow]
  exact he

lemma weightedInverseArea_expectation_le (P : ProbabilityMeasure DiskClass) (β : ℝ)
    (hP : HasWeightedLaw P β) :
    (∫⁻ g, weightedInverseArea β g ∂(P : Measure DiskClass)) ≤ ENNReal.ofReal (256*Real.pi) := by
  let A (z : ℂ) := ∫⁻ g, inverseJacDensity g z ∂(P : Measure DiskClass)
  let B (z : ℂ) := ∫⁻ g, inverseDensity g z ∂(P : Measure DiskClass)
  have hswap : (∫⁻ g, weightedInverseArea β g ∂(P : Measure DiskClass)) =
      ∫⁻ z in outsideCore, ENNReal.ofReal (z.im^(β+1))*B z := by
    unfold weightedInverseArea
    rw [lintegral_lintegral_swap]
    · apply lintegral_congr
      intro z
      have hm : Measurable (fun g => inverseDensity g z) :=
        measurable_inverseDensity.comp (measurable_id.prodMk measurable_const)
      exact lintegral_const_mul _ hm
    · exact ((((Complex.continuous_im.comp continuous_snd).measurable.pow measurable_const).ennreal_ofReal).mul
        measurable_inverseDensity).aemeasurable
  have hpoint (z : ℂ) (hz : z ∈ outsideCore) :
      ENNReal.ofReal (z.im^(β+1))*B z = ENNReal.ofReal (z.im⁻¹^3)*A (affineInverse z) := by
    have hy : 0 < z.im := hz.1
    dsimp only [A]
    rw [weighted_inverse_identity P β hP (affineInverse_mem_outsideCore hz),
      affineInverse_invol hz.1,affineInverse_im,← mul_assoc]
    congr 1
    rw [← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr hy.le) 3)]
    congr 1
    rw [Real.inv_rpow hy.le]
    have he : (z.im⁻¹^3 : ℝ) = z.im^(-3 : ℝ) := by
      rw [Real.rpow_neg hy.le]
      norm_cast
      simp
    rw [he,← Real.rpow_neg hy.le,← Real.rpow_add hy]
    congr 1
    ring
  rw [hswap,setLIntegral_congr_fun measurableSet_outsideCore hpoint,
    ← affineInverse_change_variables measurableSet_outsideCore (fun _ h => h.1)
      affineInverse_image_outsideCore A]
  have hswap₂ : (∫⁻ z in outsideCore, A z) =
      ∫⁻ g, (∫⁻ z in outsideCore, inverseJacDensity g z) ∂(P : Measure DiskClass) := by
    exact (lintegral_lintegral_swap measurable_inverseJacDensity.aemeasurable).symm
  rw [hswap₂]
  calc
    _ ≤ ∫⁻ _ : DiskClass, ENNReal.ofReal (256*Real.pi) ∂(P : Measure DiskClass) :=
      lintegral_mono inverseJacDensity_integral_le
    _ = _ := by simp

lemma weightedInverseArea_ae_finite (P : ProbabilityMeasure DiskClass) (β : ℝ)
    (hP : HasWeightedLaw P β) :
    ∀ᵐ g ∂(P : Measure DiskClass), weightedInverseArea β g < ∞ :=
  ae_lt_top (measurable_weightedInverseArea β)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (weightedInverseArea_expectation_le P β hP))

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.ExpectedTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun
attribute [local irreducible] rerootClass
attribute [local irreducible] inverseDensity inverseJacDensity

lemma lintegral_Icc_inv {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫⁻ y in Icc a b, ENNReal.ofReal y⁻¹) = ENNReal.ofReal (Real.log (b/a)) := by
  have hc : ContinuousOn (fun y : ℝ => y⁻¹) (Icc a b) :=
    continuousOn_id.inv₀ (fun y hy => ne_of_gt (ha.trans_le hy.1))
  have hi : IntegrableOn (fun y : ℝ => y⁻¹) (Icc a b) volume := hc.integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab,integral_inv_of_pos ha (ha.trans_le hab)]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact inv_nonneg.mpr (ha.le.trans hy.1)

lemma lintegral_transportBox_inv {R a b : ℝ} (hR : 0 ≤ R) (ha : 0 < a) (hab : a ≤ b) :
    (∫⁻ z in transportBox R a b, ENNReal.ofReal z.im⁻¹) =
      ENNReal.ofReal (2*R*Real.log (b/a)) := by
  have he : Complex.measurableEquivRealProd ⁻¹' (Icc (-R) R ×ˢ Icc a b) = transportBox R a b := by
    ext z
    simp only [Complex.measurableEquivRealProd_apply,mem_preimage,mem_prod,mem_Icc,transportBox,mem_ofPred_eq,abs_le]
  have hprod := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding (fun p : ℝ × ℝ => ENNReal.ofReal p.2⁻¹)
    (Icc (-R) R ×ˢ Icc a b)
  rw [he] at hprod
  change (∫⁻ z in transportBox R a b, ENNReal.ofReal z.im⁻¹) = _ at hprod
  rw [hprod,show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    setLIntegral_prod _ (by fun_prop)]
  dsimp only
  rw [lintegral_Icc_inv ha hab,
    lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc]
  rw [show R - -R = 2*R from by ring,mul_comm,← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*R)]

lemma measurable_rootJac (k σ : ℝ) : Measurable (rootJac k σ) := by
  exact (measurable_const.mul ((continuous_class_normalizedJacobian k).comp
    (continuous_id.prodMk (continuous_const (y := halfOne)))).measurable).ennreal_ofReal

lemma rootJac_reroot (g : DiskClass) {k : ℝ} (hk : 0 < k) (σ : ℝ) (z : halfPlane) :
    rootJac k σ (rerootClass g z) = ENNReal.ofReal (σ * normalizedJacobian (classFun g) k z) := by
  rw [rootJac,class_normalizedJacobian_root g hk z]

lemma measurableSet_rootWindow {k : ℝ} (hk : 0 < k) (N : ℝ) : MeasurableSet (rootWindow k N) :=
  (measurableSet_transportWindow hk N).preimage (measurable_id.prodMk measurable_const)

lemma measurable_windowTest {k : ℝ} (hk : 0 < k) (N : ℝ) : Measurable (windowTest k N) :=
  (measurable_rootJac k 1).indicator (measurableSet_rootWindow hk N)

lemma averagedDensity_window (g : DiskClass) (β : ℝ) {k : ℝ} (hk : 0 < k) (N : ℝ) (z : halfPlane) :
    averagedDensity β (windowTest k N) (g,z) =
      transportDensity g β z * ENNReal.ofReal (normalizedJacobian (classFun g) k z) *
        (transportSlice g k N).indicator 1 z := by
  rw [averagedDensity_of_mem,windowTest]
  have he : rerootClass g z ∈ rootWindow k N ↔ z.val ∈ transportSlice g k N :=
    (transportWindow_root g hk N z).trans (transportSlice_iff g k N z).symm
  by_cases hz : z.val ∈ transportSlice g k N
  · rw [indicator_of_mem (he.mpr hz),rootJac_reroot g hk 1 z,one_mul,indicator_of_mem hz]
    simp
  · rw [indicator_of_notMem (fun h => hz (he.mp h)),indicator_of_notMem hz]
    simp

lemma measurableSet_rootException {k : ℝ} (hk : 0 < k) : MeasurableSet (rootException k) := by
  have hm : Measurable (fun g : DiskClass => (g,criticalMap (classFun g) k Complex.I)) :=
    continuous_id.measurable.prodMk (((continuous_class_criticalMap k).comp
      (continuous_id.prodMk (continuous_const (y := halfOne)))).measurable)
  exact ((measurableSet_class_goodPairs hk.le).preimage hm).compl

lemma measurable_exceptionTest {k : ℝ} (hk : 0 < k) : Measurable (exceptionTest k) :=
  (measurable_rootJac k 1).indicator (measurableSet_rootException hk)

lemma averagedDensity_exception (g : DiskClass) (β : ℝ) {k : ℝ} (hk : 0 < k) (z : halfPlane) :
    averagedDensity β (exceptionTest k) (g,z) =
      transportDensity g β z * ENNReal.ofReal (normalizedJacobian (classFun g) k z) *
        {z : ℂ | z ∈ halfPlane ∧ ¬GoodPair (classFun g) k (criticalMap (classFun g) k z)}.indicator 1 z := by
  rw [averagedDensity_of_mem,exceptionTest]
  have he := class_goodPair_root g hk z
  by_cases hg : GoodPair (classFun g) k (criticalMap (classFun g) k z)
  · rw [indicator_of_notMem (show rerootClass g z ∉ rootException k from fun h => h (he.mpr hg)),
      indicator_of_notMem (show z.val ∉ {z : ℂ | z ∈ halfPlane ∧ ¬GoodPair (classFun g) k (criticalMap (classFun g) k z)} from fun h => h.2 hg)]
    simp
  · rw [indicator_of_mem (show rerootClass g z ∈ rootException k from fun h => hg (he.mp h)),
      rootJac_reroot g hk 1 z,one_mul,indicator_of_mem (show z.val ∈ {z : ℂ | z ∈ halfPlane ∧ ¬GoodPair (classFun g) k (criticalMap (classFun g) k z)} from ⟨z.property,hg⟩)]
    simp

lemma exceptionTest_integral_zero (P : ProbabilityMeasure DiskClass) (β : ℝ)
    (hP : HasWeightedLaw P β) {k : ℝ} (hk : 0 < k)
    (hg : ∀ᵐ g ∂(P : Measure DiskClass), ∀ᵐ ξ : ℂ, GoodPair (classFun g) k ξ) :
    (∫⁻ g, exceptionTest k g ∂(P : Measure DiskClass)) = 0 := by
  apply root_test_zero_of_averaging P β hP (measurable_exceptionTest hk)
  filter_upwards [hg] with g hg
  refine Eq.trans ?_ (exceptional_transport_zero g (β := β) hk hg)
  apply setLIntegral_congr_fun isOpen_halfPlane.measurableSet
  intro z hz
  exact averagedDensity_exception g β hk ⟨z,hz⟩

lemma averagedDensity_box (P : ProbabilityMeasure DiskClass) (β : ℝ)
    (hP : HasWeightedLaw P β) {Φ : DiskClass → ℝ≥0∞} (hΦ : Measurable Φ)
    {R a b : ℝ} (hR : 0 ≤ R) (ha : 0 < a) (hab : a ≤ b) :
    (∫⁻ g, ∫⁻ z in transportBox R a b, averagedDensity β Φ (g,z) ∂volume ∂(P : Measure DiskClass)) =
      ENNReal.ofReal (2*R*Real.log (b/a)) * ∫⁻ g, Φ g ∂(P : Measure DiskClass) := by
  rw [lintegral_lintegral_swap (f := fun g z => averagedDensity β Φ (g,z)) (μ := (P : Measure DiskClass)) (ν := volume.restrict (transportBox R a b)) (measurable_averagedDensity β hΦ).aemeasurable]
  have he : (∫⁻ z in transportBox R a b, ∫⁻ g, averagedDensity β Φ (g,z) ∂(P : Measure DiskClass)) =
      ∫⁻ z in transportBox R a b, ENNReal.ofReal z.im⁻¹ * ∫⁻ g, Φ g ∂(P : Measure DiskClass) := by
    apply setLIntegral_congr_fun (measurableSet_transportBox R a b)
    intro z hz
    exact weighted_averagedDensity P β hP hΦ ⟨z,ha.trans_le hz.2.1⟩
  rw [he,lintegral_mul_const _ (by fun_prop),lintegral_transportBox_inv hR ha hab]

lemma setLIntegral_mul_indicator_one {S T : Set ℂ} (hS : MeasurableSet S) (hST : S ⊆ T)
    (f : ℂ → ℝ≥0∞) :
    (∫⁻ z in T, f z * S.indicator 1 z) = ∫⁻ z in S, f z := by
  have he : (fun z => f z * S.indicator 1 z) = S.indicator f := by
    funext z
    by_cases hz : z ∈ S <;> simp [hz]
  rw [he,setLIntegral_indicator hS,inter_eq_left.mpr hST]

lemma transport_box_averaged (g : DiskClass) {β k N R Y : ℝ} (hk : 0 < k)
    (hb : β-1 = 4*(k-1)) (hN : 1 ≤ N) :
    (∫⁻ z in transportBox R 1 Y, averagedDensity β (windowTest k N) (g,z)) ≤
      ∫⁻ z in transportBox (R+N*Y) (1/N) (N*Y), averagedDensity β (rootJac k (-1)) (g,z) := by
  have hn : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hB : transportBox R 1 Y ⊆ halfPlane := fun z hz => lt_of_lt_of_le zero_lt_one hz.2.1
  have hB' : transportBox (R+N*Y) (1/N) (N*Y) ⊆ halfPlane := fun z hz =>
    lt_of_lt_of_le (one_div_pos.mpr hn) hz.2.1
  have he := transport_box g hk hb hN (R := R) (Y := Y)
  have hp : (∫⁻ z in halfPlane, transportDensity g β z*ENNReal.ofReal (normalizedJacobian (classFun g) k z)*
      (transportSlice g k N ∩ transportBox R 1 Y).indicator 1 z) =
      ∫⁻ z in transportBox R 1 Y, averagedDensity β (windowTest k N) (g,z) := by
    have hid : (fun z => transportDensity g β z*ENNReal.ofReal (normalizedJacobian (classFun g) k z)*
      (transportSlice g k N ∩ transportBox R 1 Y).indicator 1 z) =
      fun z => (transportDensity g β z*ENNReal.ofReal (normalizedJacobian (classFun g) k z)*
        (transportSlice g k N).indicator 1 z)*(transportBox R 1 Y).indicator 1 z := by
      funext z
      rw [inter_indicator_one]
      simp only [Pi.mul_apply,mul_assoc]
    rw [hid,setLIntegral_mul_indicator_one (measurableSet_transportBox _ _ _) hB]
    apply setLIntegral_congr_fun (measurableSet_transportBox _ _ _)
    intro z hz
    exact (averagedDensity_window g β hk N ⟨z,hB hz⟩).symm
  have hm : (∫⁻ z in halfPlane, transportDensity g β z*ENNReal.ofReal (-normalizedJacobian (classFun g) k z)*
      (transportBox (R+N*Y) (1/N) (N*Y)).indicator 1 z) =
      ∫⁻ z in transportBox (R+N*Y) (1/N) (N*Y), averagedDensity β (rootJac k (-1)) (g,z) := by
    rw [setLIntegral_mul_indicator_one (measurableSet_transportBox _ _ _) hB']
    apply setLIntegral_congr_fun (measurableSet_transportBox _ _ _)
    intro z hz
    symm
    exact (averagedDensity_of_mem β (rootJac k (-1)) g ⟨z,hB' hz⟩).trans
      (congrArg (transportDensity g β z * ·) (by simpa only [neg_one_mul] using rootJac_reroot g hk (-1) ⟨z,hB' hz⟩))
  exact hp.symm.trans_le (he.trans_eq hm)

lemma expected_transport_box (P : ProbabilityMeasure DiskClass) (β : ℝ)
    (hP : HasWeightedLaw P β) {k N R Y : ℝ} (hk : 0 < k)
    (hb : β-1 = 4*(k-1)) (hN : 1 ≤ N) (hR : 0 ≤ R) (hY : 1 ≤ Y) :
    ENNReal.ofReal (2*R*Real.log Y) * (∫⁻ g, windowTest k N g ∂(P : Measure DiskClass)) ≤
      ENNReal.ofReal (2*(R+N*Y)*Real.log (N^2*Y)) * (∫⁻ g, rootJac k (-1) g ∂(P : Measure DiskClass)) := by
  have hn : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hny : 1 / N ≤ N*Y := by
    rw [div_le_iff₀ hn]
    have hc := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hY hn.le) hn.le
    nlinarith [sq_nonneg (N-1)]
  have hp := averagedDensity_box P β hP (measurable_windowTest hk N) hR zero_lt_one hY
  have hm := averagedDensity_box P β hP (measurable_rootJac k (-1))
    (add_nonneg hR (mul_nonneg hn.le (zero_le_one.trans hY))) (one_div_pos.mpr hn) hny
  simp only [div_one] at hp
  rw [show N*Y/(1/N) = N^2*Y from by field_simp] at hm
  rw [← hp,← hm]
  exact lintegral_mono (fun g => transport_box_averaged g hk hb hN)

lemma transport_ratio_tendsto (N : ℝ) :
    Tendsto (fun Y : ℝ => (1+N/Y)*(1+2*Real.log N/Real.log Y)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun Y : ℝ => N/Y) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h2 : Tendsto (fun Y : ℝ => 2*Real.log N/Real.log Y) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add h1).mul ((tendsto_const_nhds (x := (1 : ℝ))).add h2)

lemma transport_box_limit {A B : ℝ≥0∞} (hA : A ≠ ∞) (hB : B ≠ ∞)
    {N : ℝ} (hN : 1 ≤ N)
    (h : ∀ Y : ℝ, 1 < Y →
      ENNReal.ofReal (2*Y^2*Real.log Y)*A ≤
        ENNReal.ofReal (2*(Y^2+N*Y)*Real.log (N^2*Y))*B) : A ≤ B := by
  have hn : 0 < N := zero_lt_one.trans_le hN
  have hineq : ∀ Y : ℝ, 1 < Y → A.toReal ≤ (1+N/Y)*(1+2*Real.log N/Real.log Y)*B.toReal := by
    intro Y hY
    have hy : 0 < Y := zero_lt_one.trans hY
    have hl : 0 < Real.log Y := Real.log_pos hY
    have hny : 1 < N^2*Y := by nlinarith [sq_nonneg (N-1)]
    have hlny : 0 ≤ Real.log (N^2*Y) := Real.log_nonneg hny.le
    have hb := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB) (h Y hY)
    rw [ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*Y^2*Real.log Y),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*(Y^2+N*Y)*Real.log (N^2*Y))] at hb
    have hlog : Real.log (N^2*Y) = 2*Real.log N + Real.log Y := by
      rw [Real.log_mul (by positivity) (ne_of_gt hy),Real.log_pow]
      norm_num
    rw [hlog] at hb
    apply (mul_le_mul_iff_right₀ (show 0 < 2*Y^2*Real.log Y by positivity)).mp
    calc
      _ ≤ 2*(Y^2+N*Y)*(2*Real.log N+Real.log Y)*B.toReal := hb
      _ = _ := by field_simp; ring
  apply (ENNReal.toReal_le_toReal hA hB).mp
  have ht := (transport_ratio_tendsto N).mul_const B.toReal
  simp only [one_mul] at ht
  apply ge_of_tendsto ht
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with Y hY
  exact hineq Y hY

lemma rootJac_integral_lt_top (P : ProbabilityMeasure DiskClass) (k σ : ℝ) :
    (∫⁻ g, rootJac k σ g ∂(P : Measure DiskClass)) < ∞ := by
  have hc : Continuous (fun g : DiskClass => σ*normalizedJacobian (classFun g) k Complex.I) :=
    continuous_const.mul ((continuous_class_normalizedJacobian k).comp
      (continuous_id.prodMk (continuous_const (y := halfOne))))
  have hi : Integrable (fun g : DiskClass => σ*normalizedJacobian (classFun g) k Complex.I) (P : Measure DiskClass) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply lt_of_le_of_lt (lintegral_mono (fun g => ENNReal.ofReal_le_ofReal (le_abs_self _)))
  exact (hasFiniteIntegral_iff_norm _).mp hi.2

lemma windowTest_le (k N : ℝ) (g : DiskClass) : windowTest k N g ≤ rootJac k 1 g := by
  by_cases hg : g ∈ rootWindow k N <;> simp [windowTest,indicator_of_mem,indicator_of_notMem,hg]

lemma windowTest_integral_lt_top (P : ProbabilityMeasure DiskClass) (k N : ℝ) :
    (∫⁻ g, windowTest k N g ∂(P : Measure DiskClass)) < ∞ :=
  (lintegral_mono (windowTest_le k N)).trans_lt (rootJac_integral_lt_top P k 1)

lemma windowTest_mono {k : ℝ} (hk : 0 < k) :
    Monotone (fun n : ℕ => windowTest k (n+1)) := by
  intro n m hnm g
  have hs : rootWindow k (n+1) ⊆ rootWindow k (m+1) :=
    fun g hg => transportWindow_mono hk (by exact_mod_cast Nat.add_le_add_right hnm 1) hg
  by_cases hg : g ∈ rootWindow k (n+1)
  · simp only [windowTest,indicator_of_mem hg,indicator_of_mem (hs hg),le_refl]
  · simp only [windowTest,indicator_of_notMem hg]
    exact bot_le

lemma iSup_windowTest {k : ℝ} (hk : 0 < k) (g : DiskClass) :
    (⨆ n : ℕ, windowTest k (n+1) g) =
      {g : DiskClass | (g,halfOne) ∈ pairingDomain k}.indicator (rootJac k 1) g := by
  by_cases hg : (g,halfOne) ∈ pairingDomain k
  · rw [indicator_of_mem (show g ∈ {g : DiskClass | (g,halfOne) ∈ pairingDomain k} from hg)]
    apply le_antisymm (iSup_le (fun n : ℕ => windowTest_le k (n+1) g))
    have hu : (g,halfOne) ∈ ⋃ n : ℕ, transportWindow k (n+1) := (iUnion_transportWindow hk).symm ▸ hg
    obtain ⟨n,hn⟩ := mem_iUnion.mp hu
    have he : windowTest k (n+1) g = rootJac k 1 g := indicator_of_mem (show g ∈ rootWindow k (n+1) from hn) _
    exact he ▸ le_iSup (fun n : ℕ => windowTest k (n+1) g) n
  · rw [indicator_of_notMem (show g ∉ {g : DiskClass | (g,halfOne) ∈ pairingDomain k} from hg)]
    apply le_antisymm _ bot_le
    apply iSup_le
    intro n
    apply le_of_eq
    apply indicator_of_notMem
    intro hn
    exact hg hn.1

lemma rootJac_eq_window_exception {k : ℝ} (hk : 0 < k) (g : DiskClass) :
    rootJac k 1 g = (⨆ n : ℕ, windowTest k (n+1) g) + exceptionTest k g := by
  rw [iSup_windowTest hk g,exceptionTest]
  by_cases hG : GoodPair (classFun g) k (criticalMap (classFun g) k Complex.I)
  · rw [indicator_of_notMem (show g ∉ rootException k from fun h => h hG),add_zero]
    by_cases hJ : 0 < normalizedJacobian (classFun g) k Complex.I
    · exact (indicator_of_mem (show g ∈ {g : DiskClass | (g,halfOne) ∈ pairingDomain k} from ⟨hJ,hG⟩) _).symm
    · rw [indicator_of_notMem (show g ∉ {g : DiskClass | (g,halfOne) ∈ pairingDomain k} from fun h => hJ h.1)]
      exact ENNReal.ofReal_eq_zero.mpr (by simpa only [one_mul] using le_of_not_gt hJ)
  · rw [indicator_of_mem (show g ∈ rootException k from hG),indicator_of_notMem (show g ∉ {g : DiskClass | (g,halfOne) ∈ pairingDomain k} from fun h => hG h.2),zero_add]

lemma jacobian_positive_le_negative (P : ProbabilityMeasure DiskClass) (β : ℝ)
    (hP : HasWeightedLaw P β) {k : ℝ} (hk : 0 < k)
    (hb : β-1 = 4*(k-1))
    (hg : ∀ᵐ g ∂(P : Measure DiskClass), ∀ᵐ ξ : ℂ, GoodPair (classFun g) k ξ) :
    (∫⁻ g, rootJac k 1 g ∂(P : Measure DiskClass)) ≤ ∫⁻ g, rootJac k (-1) g ∂(P : Measure DiskClass) := by
  have hw (n : ℕ) : (∫⁻ g, windowTest k (n+1) g ∂(P : Measure DiskClass)) ≤ ∫⁻ g, rootJac k (-1) g ∂(P : Measure DiskClass) := by
    apply transport_box_limit (N := (n:ℝ)+1) (windowTest_integral_lt_top P k (n+1)).ne (rootJac_integral_lt_top P k (-1)).ne
      (by have h := Nat.cast_nonneg (α := ℝ) n; linarith : (1 : ℝ) ≤ n+1)
    intro Y hY
    exact expected_transport_box P β hP hk hb (by have h := Nat.cast_nonneg (α := ℝ) n; linarith) (sq_nonneg Y) hY.le
  have he (g : DiskClass) := rootJac_eq_window_exception hk g
  simp_rw [he]
  rw [lintegral_add_left (Measurable.iSup (fun n : ℕ => measurable_windowTest hk (n+1))),
    exceptionTest_integral_zero P β hP hk hg,add_zero,lintegral_iSup (fun n : ℕ => measurable_windowTest hk (n+1)) (windowTest_mono hk)]
  exact iSup_le hw

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.Moments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun
attribute [local irreducible] rerootClass
attribute [local irreducible] inverseDensity inverseJacDensity

lemma jacobian_expectation_nonpos_oai (P : ProbabilityMeasure DiskClass) (β : ℝ)
    (hP : HasWeightedLaw P β) (hβ : 1 < β) :
    (∫ g, normalizedJacobian (classFun g) ((β+3)/4) Complex.I ∂(P : Measure DiskClass)) ≤ 0 := by
  have hk : 0 < (β+3)/4 := by linarith
  have hg : ∀ᵐ g ∂(P : Measure DiskClass), ∀ᵐ ξ : ℂ, GoodPair (classFun g) ((β+3)/4) ξ := by
    filter_upwards [weightedInverseArea_ae_finite P β hP] with g hg
    apply class_ae_goodPairs g hβ
    have he : weightedInverseArea β g = (∫⁻ z in outsideCore,
        ENNReal.ofReal (z.im^(β+1)*‖classFun g z‖⁻¹^4)) := by
      simp only [weightedInverseArea,inverseDensity]
      apply setLIntegral_congr_fun measurableSet_outsideCore
      intro z hz
      dsimp only
      rw [planeClassValue_eq g hz.1,ENNReal.ofReal_mul (Real.rpow_nonneg hz.1.le _)]
    exact he ▸ hg
  have hi := jacobian_positive_le_negative P β hP hk (by ring) hg
  have hc : Continuous (fun g : DiskClass => normalizedJacobian (classFun g) ((β+3)/4) Complex.I) :=
    (continuous_class_normalizedJacobian _).comp
      (continuous_id.prodMk (continuous_const (y := halfOne)))
  have hInt := hc.integrable_of_hasCompactSupport (μ := (P : Measure DiskClass)) (HasCompactSupport.of_compactSpace _)
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hInt]
  have ht := ENNReal.toReal_mono (rootJac_integral_lt_top P ((β+3)/4) (-1)).ne hi
  simpa only [rootJac,one_mul,neg_one_mul,sub_nonpos] using ht

end Brennan

end

end OAI
end

theorem solution : type_of% @OAI.Brennan.jacobian_expectation_nonpos_oai := @OAI.Brennan.jacobian_expectation_nonpos_oai
