-- Prove2me | solution 1 for OAI.CircleDomainRigidity.MatchedConformalEnds.MatchedRealMask.global_sobolev_of_published_inputs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T05:56:01.297212+00:00
-- url     : https://prove2.me/submissions/40f0dc00-9441-44f1-b427-7a64e8d6f4f8

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C010
import Theorems.Thm_OAI_CircleDomainRigidity_AppendingSequence_exists_tracked_global_weak_limit
import Theorems.Thm_OAI_CircleDomainRigidity_CompactScalarModel_FlattenedSourceSelection_compact_tests
import Theorems.Thm_OAI_CircleDomainRigidity_exists_signed_compact_scalar_circle_model
import Theorems.Thm_OAI_CircleDomainRigidity_exists_small_selected_height_data

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScaledCutoffEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dirichlet energy of a smooth planar cutoff is unchanged by dilation.
This supplies the fixed energy budget for disjoint concentric transition
annuli used to make cutoffs of arbitrarily small energy. -/
open Set Function MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 theorem dilatedCutoff_smooth {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (r : ℝ) :
    ContDiff ℝ ∞ (dilatedCutoff f r) := hf.comp (contDiff_id.const_smul _)

 theorem dilatedCutoff_compact {f : ℂ → ℝ} (hs : HasCompactSupport f)
    {r : ℝ} (hr : r ≠ 0) : HasCompactSupport (dilatedCutoff f r) := by
  let e : ℂ ≃ₜ ℂ := Homeomorph.smul (isUnit_iff_ne_zero.mpr (inv_ne_zero hr)).unit
  exact hs.comp_homeomorph e

 theorem dilatedCutoff_fderiv {f : ℂ → ℝ} (hf : Differentiable ℝ f) (r : ℝ) (z : ℂ) :
    fderiv ℝ (dilatedCutoff f r) z = r⁻¹ • fderiv ℝ f (r⁻¹ • z) := by
  have hd := (hf (r⁻¹ • z)).hasFDerivAt.comp z ((hasFDerivAt_id z).const_smul r⁻¹)
  change fderiv ℝ (f ∘ fun w : ℂ => r⁻¹ • w) z = _
  rw [hd.fderiv]
  ext w
  simp

 theorem smooth_cutoff_energy_integrable {f : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    Integrable (fun z => ‖fderiv ℝ f z‖^2) := by
  have hd : Continuous (fderiv ℝ f) :=
    (hf.fderiv_right (m := (↑(⊤ : ℕ∞))) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuous
  apply (hd.norm.pow 2).integrable_of_hasCompactSupport
  apply (hs.fderiv (𝕜 := ℝ)).mono'
  intro z hz
  by_contra hzero
  apply hz
  change ‖fderiv ℝ f z‖^2 = 0
  simp only [image_eq_zero_of_notMem_tsupport hzero, norm_zero, zero_pow (by decide : 2 ≠ 0)]

 theorem dilatedCutoff_energy {f : ℂ → ℝ} (hf : Differentiable ℝ f)
    {r : ℝ} (hr : 0 < r) :
    (∫ z, ‖fderiv ℝ (dilatedCutoff f r) z‖^2) = ∫ z, ‖fderiv ℝ f z‖^2 := by
  simp_rw [dilatedCutoff_fderiv hf, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hr), mul_pow]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume (fun z : ℂ => ‖fderiv ℝ f z‖^2) hr.le]
  simp only [Complex.finrank_real_complex, smul_eq_mul]
  field_simp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_AnnularCutoffs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concentric smooth cutoffs whose transition annuli are disjoint.
Each dilation has the same Dirichlet energy in dimension two. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 theorem dilated_unitCutoff_one {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ ≤ r) :
    dilatedCutoff unitAnnularCutoff r z = 1 := by
  apply unitAnnularCutoff.one_of_mem_closedBall
  simp only [unitAnnularCutoff, mem_closedBall, dist_zero_right]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  exact (inv_mul_le_iff₀ hr).mpr (by simpa using hz)

 theorem dilated_unitCutoff_support {r : ℝ} (hr : 0 < r) :
    support (dilatedCutoff unitAnnularCutoff r) ⊆ ball (0 : ℂ) (2*r) := by
  intro z hz
  have hh : r⁻¹ • z ∈ support (unitAnnularCutoff : ℂ → ℝ) := hz
  rw [unitAnnularCutoff.support_eq] at hh
  simp only [unitAnnularCutoff, mem_ball, dist_zero_right] at hh
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)] at hh
  have hn := (inv_mul_lt_iff₀ hr).mp hh
  simpa only [mem_ball, dist_zero_right, mul_comm] using hn

 theorem dilated_unitCutoff_derivative_annulus {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : fderiv ℝ (dilatedCutoff unitAnnularCutoff r) z ≠ 0) :
    r ≤ ‖z‖ ∧ ‖z‖ ≤ 2*r := by
  have hd : fderiv ℝ (unitAnnularCutoff : ℂ → ℝ) (r⁻¹ • z) ≠ 0 := by
    intro hh
    apply hz
    rw [dilatedCutoff_fderiv ((unitAnnularCutoff.contDiff : ContDiff ℝ ∞ (unitAnnularCutoff : ℂ → ℝ)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)), hh, smul_zero]
  constructor
  · by_contra hn
    have hsmall : r⁻¹ • z ∈ ball (0 : ℂ) unitAnnularCutoff.rIn := by
      simp only [unitAnnularCutoff, mem_ball, dist_zero_right]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      exact (inv_mul_lt_iff₀ hr).mpr (by simpa using (lt_of_not_ge hn))
    have he := unitAnnularCutoff.eventuallyEq_one_of_mem_ball hsmall
    exact hd (by simpa using he.fderiv_eq)
  · have hm := support_fderiv_subset ℝ hd
    rw [unitAnnularCutoff.tsupport_eq] at hm
    simp only [unitAnnularCutoff, mem_closedBall, dist_zero_right] at hm
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)] at hm
    simpa only [mul_comm] using (inv_mul_le_iff₀ hr).mp hm

 theorem separated_dilatedCutoff_derivatives
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hrs : 2*r < s) (z : ℂ) :
    fderiv ℝ (dilatedCutoff unitAnnularCutoff r) z = 0 ∨
      fderiv ℝ (dilatedCutoff unitAnnularCutoff s) z = 0 := by
  by_cases hz : fderiv ℝ (dilatedCutoff unitAnnularCutoff r) z = 0
  · exact Or.inl hz
  · right
    by_contra hw
    have ha := dilated_unitCutoff_derivative_annulus hr hz
    have hb := dilated_unitCutoff_derivative_annulus hs hw
    linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_AnnularRadii
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete decreasing sequence of separated transition radii. -/
open Set Function MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 theorem annularRadius_pos {R : ℝ} (hR : 0 < R) (n : ℕ) : 0 < annularRadius R n := by
  exact div_pos hR (pow_pos (by norm_num) _)

 theorem annularRadius_antitone {R : ℝ} (hR : 0 ≤ R) : Antitone (annularRadius R) := by
  intro i j hij
  exact div_le_div_of_nonneg_left hR (pow_pos (by norm_num) _)
    (pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right hij 1))

 theorem annularRadius_separated {R : ℝ} (hR : 0 < R) {i j : ℕ} (hij : i < j) :
    2*annularRadius R j < annularRadius R i := by
  have hi : 0 < (4 : ℝ)^(i+1) := pow_pos (by norm_num) _
  have hj : 0 < (4 : ℝ)^(j+1) := pow_pos (by norm_num) _
  have hpow : (4 : ℝ)^(i+1)*4 ≤ 4^(j+1) := by
    rw [← pow_succ]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  change 2*(R / 4^(j+1)) < R / 4^(i+1)
  rw [← mul_div_assoc, div_lt_div_iff₀ hj hi]
  nlinarith [mul_pos hR hi, mul_le_mul_of_nonneg_left hpow hR.le]

 theorem annular_cutoff_derivatives_disjoint {R : ℝ} (hR : 0 < R) (z : ℂ) (i j : ℕ)
    (hij : i ≠ j) :
    fderiv ℝ (dilatedCutoff unitAnnularCutoff (annularRadius R i)) z = 0 ∨
      fderiv ℝ (dilatedCutoff unitAnnularCutoff (annularRadius R j)) z = 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact (separated_dilatedCutoff_derivatives (annularRadius_pos hR j) (annularRadius_pos hR i)
      (annularRadius_separated hR h) z).symm
  · exact separated_dilatedCutoff_derivatives (annularRadius_pos hR i) (annularRadius_pos hR j)
      (annularRadius_separated hR h) z

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DisjointCutoffAverages
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging cutoffs with disjoint transition sets divides their common
Dirichlet energy by the number of cutoffs. -/
open Set Function MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 theorem norm_sq_sum_disjoint {I E : Type*} [NormedAddCommGroup E]
    (s : Finset I) (v : I → E)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → v i = 0 ∨ v j = 0) :
    ‖∑ i ∈ s, v i‖^2 = ∑ i ∈ s, ‖v i‖^2 := by
  classical
  by_cases hn : ∃ i ∈ s, v i ≠ 0
  · obtain ⟨i, hi, hvi⟩ := hn
    have hz (j) (hj : j ∈ s) (hji : j ≠ i) : v j = 0 := (h j hj i hi hji).resolve_right hvi
    rw [Finset.sum_eq_single i (fun j hj hji => hz j hj hji) (by simp [hi]),
      Finset.sum_eq_single i (fun j hj hji => by simp [hz j hj hji]) (by simp [hi])]
  · have hz (i) (hi : i ∈ s) : v i = 0 := by
      by_contra hne
      exact hn ⟨i, hi, hne⟩
    rw [Finset.sum_eq_zero (fun i hi => hz i hi),
      Finset.sum_eq_zero (fun i hi => by simp [hz i hi])]
    simp

 theorem cutoffAverage_smooth (f : ℕ → ℂ → ℝ) (hf : ∀ i, ContDiff ℝ ∞ (f i)) (N : ℕ) :
    ContDiff ℝ ∞ (cutoffAverage f N) :=
  contDiff_const.mul (ContDiff.sum (fun i _ => hf i))

 theorem cutoffAverage_fderiv (f : ℕ → ℂ → ℝ) (hf : ∀ i, Differentiable ℝ (f i)) (N : ℕ) (z : ℂ) :
    fderiv ℝ (cutoffAverage f N) z =
      (N : ℝ)⁻¹ • ∑ i ∈ Finset.range N, fderiv ℝ (f i) z := by
  exact ((HasFDerivAt.fun_sum (fun i _ => (hf i z).hasFDerivAt)).const_mul (N : ℝ)⁻¹).fderiv

 theorem cutoffAverage_compact (f : ℕ → ℂ → ℝ) (hs : ∀ i, HasCompactSupport (f i)) (N : ℕ) :
    HasCompactSupport (cutoffAverage f N) := by
  have hh : HasCompactSupport (fun z : ℂ => ∑ i ∈ Finset.range N, f i z) := by
    simpa only [Finset.sum_fn] using
      (HasCompactSupport.finset_sum (s := Finset.range N) (f := f) (fun i _ => hs i))
  change HasCompactSupport ((fun _ : ℂ => (N : ℝ)⁻¹) *
    (fun z : ℂ => ∑ i ∈ Finset.range N, f i z))
  exact hh.mul_left

 theorem cutoffAverage_mem_unit (f : ℕ → ℂ → ℝ)
    (hf : ∀ i z, f i z ∈ Icc (0 : ℝ) 1) {N : ℕ} (hN : 0 < N) (z : ℂ) :
    cutoffAverage f N z ∈ Icc (0 : ℝ) 1 := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range N, f i z := Finset.sum_nonneg (fun i _ => (hf i z).1)
  have hsum1 : ∑ i ∈ Finset.range N, f i z ≤ (N : ℝ) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range N, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (hf i z).2)
      _ = _ := by simp
  change 0 ≤ (N : ℝ)⁻¹ * _ ∧ (N : ℝ)⁻¹ * _ ≤ 1
  exact ⟨mul_nonneg (inv_pos.mpr hn).le hsum0, (inv_mul_le_iff₀ hn).mpr (by simpa using hsum1)⟩

 theorem cutoffAverage_one (f : ℕ → ℂ → ℝ) {N : ℕ} (hN : 0 < N) {z : ℂ}
    (hf : ∀ i ∈ Finset.range N, f i z = 1) : cutoffAverage f N z = 1 := by
  simp only [cutoffAverage, Finset.sum_congr rfl hf, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne')

 theorem cutoffAverage_energy (f : ℕ → ℂ → ℝ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hs : ∀ i, HasCompactSupport (f i))
    (hdisj : ∀ z i j, i ≠ j → fderiv ℝ (f i) z = 0 ∨ fderiv ℝ (f j) z = 0)
    {C : ℝ} (hC : ∀ i, (∫ z, ‖fderiv ℝ (f i) z‖^2) = C)
    {N : ℕ} (hN : 0 < N) :
    (∫ z, ‖fderiv ℝ (cutoffAverage f N) z‖^2) = (N : ℝ)⁻¹*C := by
  have hdiff (i) : Differentiable ℝ (f i) := (hf i).differentiable (by simp)
  have he (z : ℂ) : ‖fderiv ℝ (cutoffAverage f N) z‖^2 =
      (N : ℝ)⁻¹^2 * ∑ i ∈ Finset.range N, ‖fderiv ℝ (f i) z‖^2 := by
    rw [cutoffAverage_fderiv f hdiff N, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N)), mul_pow]
    rw [norm_sq_sum_disjoint (Finset.range N) _ (fun i _ j _ hij => hdisj z i j hij)]
  simp_rw [he]
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => smooth_cutoff_energy_integrable (hf i) (hs i))]
  simp only [hC, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  field_simp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmallEnergyCutoff
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth planar cutoffs with arbitrarily small Dirichlet energy,
constructed by averaging disjoint concentric transition annuli. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 theorem annularAverage_smooth (R : ℝ) (N : ℕ) : ContDiff ℝ ∞ (annularAverage R N) :=
  cutoffAverage_smooth _ (fun _ => dilatedCutoff_smooth unitAnnularCutoff.contDiff _) N

 theorem annularAverage_compact {R : ℝ} (hR : 0 < R) (N : ℕ) :
    HasCompactSupport (annularAverage R N) :=
  cutoffAverage_compact _ (fun i => dilatedCutoff_compact unitAnnularCutoff.hasCompactSupport
    (annularRadius_pos hR i).ne') N

 theorem annularAverage_mem_unit (R : ℝ) {N : ℕ} (hN : 0 < N) (z : ℂ) :
    annularAverage R N z ∈ Icc (0 : ℝ) 1 :=
  cutoffAverage_mem_unit _ (fun _ _ => ⟨unitAnnularCutoff.nonneg, unitAnnularCutoff.le_one⟩) hN z

 theorem annularAverage_one {R : ℝ} (hR : 0 < R) {N : ℕ} (hN : 0 < N)
    {z : ℂ} (hz : ‖z‖ ≤ annularRadius R N) : annularAverage R N z = 1 := by
  apply cutoffAverage_one _ hN
  intro i hi
  exact dilated_unitCutoff_one (annularRadius_pos hR i)
    (hz.trans (annularRadius_antitone hR.le (Finset.mem_range.mp hi).le))

 theorem annularAverage_tsupport {R : ℝ} (hR : 0 < R) (N : ℕ) :
    tsupport (annularAverage R N) ⊆ ball (0 : ℂ) R := by
  have hsub : support (annularAverage R N) ⊆ closedBall (0 : ℂ) (R/2) := by
    intro z hz
    by_contra hzout
    apply hz
    change (N : ℝ)⁻¹ * (∑ i ∈ Finset.range N, dilatedCutoff unitAnnularCutoff (annularRadius R i) z) = 0
    rw [Finset.sum_eq_zero, mul_zero]
    intro i _
    by_contra hne
    have hzin := dilated_unitCutoff_support (annularRadius_pos hR i) hne
    have hb := annularRadius_antitone hR.le (Nat.zero_le i)
    have hzero : annularRadius R 0 = R/4 := by simp [annularRadius]
    rw [hzero] at hb
    apply hzout
    rw [mem_closedBall, dist_zero_right]
    have hzlt : ‖z‖ < 2*annularRadius R i := by simpa only [mem_ball, dist_zero_right] using hzin
    linarith
  have hcl : tsupport (annularAverage R N) ⊆ closedBall (0 : ℂ) (R/2) :=
    closure_minimal hsub isClosed_closedBall
  intro z hz
  have hh := hcl hz
  rw [mem_closedBall, dist_zero_right] at hh
  rw [mem_ball, dist_zero_right]
  linarith

 theorem annularAverage_energy {R : ℝ} (hR : 0 < R) {N : ℕ} (hN : 0 < N) :
    (∫ z, ‖fderiv ℝ (annularAverage R N) z‖^2) =
      (N : ℝ)⁻¹ * ∫ z, ‖fderiv ℝ (unitAnnularCutoff : ℂ → ℝ) z‖^2 := by
  apply cutoffAverage_energy _
    (fun _ => dilatedCutoff_smooth unitAnnularCutoff.contDiff _)
    (fun i => dilatedCutoff_compact unitAnnularCutoff.hasCompactSupport (annularRadius_pos hR i).ne')
    (annular_cutoff_derivatives_disjoint hR)
    (fun i => dilatedCutoff_energy
      ((unitAnnularCutoff.contDiff : ContDiff ℝ ∞ (unitAnnularCutoff : ℂ → ℝ)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (annularRadius_pos hR i)) hN

 theorem exists_small_energy_cutoff_zero {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∃ f : ℂ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ ball 0 R ∧ (∀ z, f z ∈ Icc (0 : ℝ) 1) ∧
      (∀ᶠ z in 𝓝 (0 : ℂ), f z = 1) ∧ (∫ z, ‖fderiv ℝ f z‖^2) < ε := by
  let C := ∫ z, ‖fderiv ℝ (unitAnnularCutoff : ℂ → ℝ) z‖^2
  have ht : Tendsto (fun N : ℕ => (N : ℝ)⁻¹*C) atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const C
  obtain ⟨N, henergy, hN⟩ := ((ht.eventually (gt_mem_nhds hε)).and (eventually_gt_atTop 0)).exists
  refine ⟨annularAverage R N, annularAverage_smooth R N, annularAverage_compact hR N,
    annularAverage_tsupport hR N, annularAverage_mem_unit R hN, ?_, ?_⟩
  · filter_upwards [ball_mem_nhds (0 : ℂ) (annularRadius_pos hR N)] with z hz
    exact annularAverage_one hR hN (by simpa only [mem_ball, dist_zero_right] using (Metric.mem_ball.mp hz).le)
  · rw [annularAverage_energy hR hN]
    exact henergy

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CenteredSmallCutoffs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small-energy smooth cutoffs centered at each actual omitted source
point, with their support inside a prescribed ball. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 theorem translatedCutoff_fderiv {f : ℂ → ℝ} (hf : Differentiable ℝ f) (c z : ℂ) :
    fderiv ℝ (translatedCutoff f c) z = fderiv ℝ f (z-c) := by
  have hd := (hf (z-c)).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const c)
  change fderiv ℝ (fun w : ℂ => f (w-c)) z = _
  simpa only [id_eq, Function.comp_def, ContinuousLinearMap.comp_id] using hd.fderiv

 theorem translatedCutoff_energy {f : ℂ → ℝ} (hf : Differentiable ℝ f) (c : ℂ) :
    (∫ z, ‖fderiv ℝ (translatedCutoff f c) z‖^2) = ∫ z, ‖fderiv ℝ f z‖^2 := by
  simp_rw [translatedCutoff_fderiv hf]
  exact integral_sub_right_eq_self (fun z : ℂ => ‖fderiv ℝ f z‖^2) c

 theorem exists_small_energy_cutoff (c : ℂ) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∃ f : ℂ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ ball c R ∧ (∀ z, f z ∈ Icc (0 : ℝ) 1) ∧
      (∀ᶠ z in 𝓝 c, f z = 1) ∧ (∫ z, ‖fderiv ℝ f z‖^2) < ε := by
  obtain ⟨f, hf, hs, hsupport, hunit, hone, henergy⟩ := exists_small_energy_cutoff_zero hR hε
  let g := translatedCutoff f c
  have he : g = f ∘ (Homeomorph.addRight (-c)) := by
    funext z
    change f (z-c) = f (z + -c)
    rw [sub_eq_add_neg]
  refine ⟨g, hf.comp (contDiff_id.sub contDiff_const), ?_, ?_, (fun z => hunit (z-c)), ?_, ?_⟩
  · rw [he]
    exact hs.comp_homeomorph (Homeomorph.addRight (-c))
  · rw [he, tsupport_comp_eq_preimage]
    intro z hz
    change z + -c ∈ tsupport f at hz
    have hh := hsupport hz
    simpa only [mem_ball, dist_zero_right, dist_eq_norm, sub_eq_add_neg, neg_zero, add_zero] using hh
  · have ht : Tendsto (fun z : ℂ => z-c) (𝓝 c) (𝓝 0) := by
      simpa only [id_eq, sub_self] using
        (tendsto_id : Tendsto (fun z : ℂ => z) (𝓝 c) (𝓝 c)).sub_const c
    exact ht.eventually hone
  · rw [translatedCutoff_energy (hf.differentiable (by simp))]
    exact henergy

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.KLS_Sobolev_Witnesses
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Matrix
open scoped ENNReal NNReal Convolution Pointwise

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem MemW1pWitness.weakGrad_norm_memLp
    {p : ℝ≥0∞} {Ω : Set E} {f : E → ℝ} {μ : Measure E}
    (hw : MemW1pWitness p f Ω μ) :
    MemLp (fun x => ‖hw.weakGrad x‖) p (μ.restrict Ω) := by
  let _ := (inferInstance : NeZero d)
  exact hw.weakGrad_memLp.norm

end DeGiorgi

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothJordanNeighborhoods
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite smooth Jordan neighborhoods

The contour construction in Section 1 of the Koebe manuscript is derived
from the smooth cutoff and regular level, scalar Sard, compact
one-manifold classification, and planar Schoenflies. Outer selection and containment
give the finite family of Jordan neighborhoods.
-/

open Set Filter Function
open scoped Topology ContDiff Manifold

namespace CircleDomainRigidity

/-- Actual finite smooth Jordan disks covering a chosen compact part of an
obstacle, with disjoint closures contained in the prescribed physical open
set. Its complement is required connected and unbounded precisely for the
hole-filling containment argument. -/
theorem exists_finite_smooth_jordan_cover
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {A F V : Set ℂ} (hA : IsCompact A) (hAF : A ⊆ F)
    (hFA : IsClosed (F \ A)) (hV : IsOpen V) (hAV : A ⊆ V)
    (hVconn : IsPreconnected Vᶜ) (hVunbounded : ¬ Bornology.IsBounded Vᶜ) :
    ∃ (f : ℂ → ℝ) (t : ℝ)
      (γ : ConnectedComponents {z // f z = t} → Circle → ℂ)
      (H : ConnectedComponents {z // f z = t} → ℂ ≃ₜ ℂ)
      (s : Set (ConnectedComponents {z // f z = t})),
      s.Finite ∧ A ⊆ ⋃ i ∈ s, jordanInterior (H i) ∧
      s.Pairwise (fun i j => Disjoint (closure (jordanInterior (H i)))
        (closure (jordanInterior (H j)))) ∧
      (∀ i ∈ s, closure (jordanInterior (H i)) ⊆ V) ∧
      ∀ i ∈ s, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧
        Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (H i)) = range (γ i) ∧
        Disjoint (frontier (jordanInterior (H i))) F := by
  classical
  obtain ⟨f, t, hf, ht, hU, hAU, hUc, hUV, _, hlevel, hregular, havoid, _⟩ :=
    exists_regular_superlevel_isolating_obstacle hsard hA hAF hFA hV hAV
  obtain ⟨hfinite, γ, hγ, hγdisj, hγcover⟩ :=
    compact_regular_level_circle_contours hf hregular hlevel
  let : Finite (ConnectedComponents {z // f z = t}) := hfinite
  choose H hH using fun i => hschoenflies (γ i) (hγ i).2.continuous (hγ i).2.injective
  have hfront (i) : frontier (jordanInterior (H i)) = range (γ i) :=
    frontier_jordanInterior_eq_circle_range (H i) (γ i) (hH i)
  have hUd : frontier {z | t < f z} = {z | f z = t} :=
    frontier_superlevel_eq_regular_level hf.continuous hregular
  have hfrontlevel (i) : frontier (jordanInterior (H i)) ⊆ {z | f z = t} := by
    rw [hfront, ← hγcover]
    exact subset_iUnion (fun i => range (γ i)) i
  have hpair : Pairwise (fun i j => Disjoint (frontier (jordanInterior (H i)))
      (frontier (jordanInterior (H j)))) := by
    intro i j hij
    simpa only [hfront] using hγdisj hij
  obtain ⟨s, hs, hsd, hdom, _⟩ := exists_outer_jordanInteriors H hpair
  let : Finite s := hs.to_subtype
  have hsd' : Pairwise (Disjoint on fun i : s => closure (jordanInterior (H i))) := by
    intro i j hij
    exact hsd i.property j.property (fun h => hij (Subtype.ext h))
  have hcover : frontier {z | t < f z} ⊆ ⋃ i : s, closure (jordanInterior (H i)) := by
    intro z hz
    rw [hUd, ← hγcover] at hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    have hi' : z ∈ closure (jordanInterior (H i)) := by
      apply frontier_subset_closure
      simpa only [hfront] using hi
    obtain ⟨j, hj, hij⟩ := hdom i
    exact mem_iUnion.mpr ⟨⟨j, hj⟩, hij hi'⟩
  have hUcover : {z | t < f z} ⊆ ⋃ i : s, jordanInterior (H i) :=
    open_subset_finite_jordanInteriors_of_frontier_subset (fun i : s => H i) hsd'
      hU (hUc.isBounded.subset subset_closure) hcover
      (fun i => hUd.symm ▸ hfrontlevel i)
  refine ⟨f, t, γ, H, s, hs, ?_, hsd, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hUcover (hAU hz))
    exact mem_iUnion₂.mpr ⟨i, i.property, hi⟩
  · intro i _
    apply closed_jordanInterior_subset_of_unbounded_connected_compl (H i) hVconn hVunbounded
    intro z hz
    apply hUV
    apply frontier_subset_closure
    rw [hUd]
    exact hfrontlevel i hz
  · intro i _
    exact ⟨(hγ i).1, (hγ i).2, hfront i, havoid.mono_left (hfrontlevel i)⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_IntegralLineAbsoluteContinuity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A linewise integral bound yields actual absolute continuity, without
first choosing a measurable representative for the bounded potential. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

theorem absolutelyContinuousOnInterval_of_dist_le
    {f : ℝ → X} {g : ℝ → Y} {a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hfg : ∀x ∈ uIcc a b, ∀y ∈ uIcc a b, dist (f x) (f y) ≤ dist (g x) (g y)) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hg ε hε
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  apply lt_of_le_of_lt _ (h E hE hlen)
  exact Finset.sum_le_sum fun i hi => hfg _ (hE.1 i hi).1 _ (hE.1 i hi).2

theorem absolutelyContinuousOnInterval_of_integral_bound
    {f : ℝ → X} {g : ℝ → ℝ} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b)
    (hfg : ∀x ∈ uIcc a b, ∀y ∈ uIcc a b,
      dist (f x) (f y) ≤ ∫t in uIoc x y, g t) :
    AbsolutelyContinuousOnInterval f a b := by
  apply absolutelyContinuousOnInterval_of_dist_le
    (hg.absolutelyContinuousOnInterval_intervalIntegral (left_mem_uIcc))
  intro x hx y hy
  apply (hfg x hx y hy).trans
  rw [Real.dist_eq, intervalIntegral.integral_interval_sub_left
    (hg.mono_set' (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc left_mem_uIcc hx)))
    (hg.mono_set' (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc left_mem_uIcc hy))),
    intervalIntegral.abs_intervalIntegral_eq]
  simpa only [uIoc_comm y x] using (le_abs_self (∫t in uIoc x y, g t))

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocallyFiniteL2Sum
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! L² control of a pointwise finite sum by the sum of its local error
norms. This applies to the countable partition-of-unity error terms. -/

open Set Filter MeasureTheory Function
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem finiteSupport_hasSum_finsum {ι : Type*} (f : ι → ℝ)
    (hf : HasFiniteSupport f) : HasSum f (∑ᶠ i, f i) := by
  rw [← show (∑' i, f i) = ∑ᶠ i, f i from tsum_eq_finsum hf]
  exact (summable_of_hasFiniteSupport hf).hasSum

theorem aestronglyMeasurable_finsum_of_pointFinite
    {ι : Type*} [Countable ι] (μ : Measure EuclideanPlane)
    (f : ι → EuclideanPlane → ℝ) (hf : ∀i, AEStronglyMeasurable (f i) μ)
    (hfin : ∀x, HasFiniteSupport (fun i => f i x)) :
    AEStronglyMeasurable (fun x => ∑ᶠ i, f i x) μ := by
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ι))
    (f := fun s x => ∑ i ∈ s, f i x)
  · intro s
    exact Finset.aestronglyMeasurable_fun_sum s (fun i _ => hf i)
  · exact Eventually.of_forall fun x => finiteSupport_hasSum_finsum _ (hfin x)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalSmoothPartition
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact smooth partition functions on an open planar domain. The
family is locally finite in the domain, allowing accumulation at its boundary. -/

open Set Function Filter TopologicalSpace
open scoped Topology Manifold

noncomputable section

namespace CircleDomainRigidity

theorem exists_openPlanePartition
    (Ω : Opens EuclideanPlane) (U : Ω → Set Ω) (hU : ∀x, U x ∈ 𝓝 x) :
    ∃ (ι : Type) (_ : Countable ι) (ρ : OpenPlanePartition Ω ι) (c : ι → Ω),
      ∀i, tsupport (ρ.weight i) ⊆ Subtype.val '' U (c i) := by
  let : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  obtain ⟨ι, b, hb⟩ := SmoothBumpCovering.exists_isSubordinate
    (𝓘(ℝ, EuclideanPlane)) (M := Ω) isClosed_univ (fun x _ => hU x)
  let : Encodable ι := b.locallyFinite.encodable (fun i => (b i).nonempty_support)
  let ρ := b.toSmoothPartitionOfUnity
  have hc (i : ι) : HasCompactSupport (ρ i) :=
    (b i).hasCompactSupport.of_isClosed_subset isClosed_closure
      (closure_mono (b.support_toSmoothPartitionOfUnity_subset i))
  let ψ : ι → EuclideanPlane → ℝ := fun i => Subtype.val.extend (ρ i) 0
  have hon (i : ι) (x : Ω) : ψ i x = ρ i x :=
    congrFun (Function.extend_comp Subtype.val_injective (ρ i) 0) x
  have hsub (i : ι) : tsupport (ψ i) ⊆ Subtype.val '' U (b.c i) := by
    apply ((hc i).tsupport_extend_zero_subset continuous_subtype_val).trans
    exact image_mono (hb.toSmoothPartitionOfUnity i)
  have hin (i : ι) : tsupport (ψ i) ⊆ Ω :=
    (hsub i).trans (image_subset_iff.mpr (fun x _ => x.property))
  have hsmooth (i : ι) : ContDiff ℝ (⊤ : ℕ∞) (ψ i) := by
    apply contMDiff_iff_contDiff.mp
    exact ContMDiff.extend_zero (hc i) (ρ i).contMDiff
  have hloc : LocallyFinite (fun i => Subtype.val ⁻¹' Function.support (ψ i) :
      ι → Set Ω) := by
    have heq : (fun i => Subtype.val ⁻¹' Function.support (ψ i) : ι → Set Ω) =
        fun i => Function.support (ρ i) := by
      funext i
      ext x
      simp only [mem_preimage, Function.mem_support, hon]
    rw [heq]
    exact ρ.locallyFinite
  have hn (i : ι) (x : EuclideanPlane) : 0 ≤ ψ i x := by
    by_cases hx : x ∈ Ω
    · rw [show x = ((⟨x, hx⟩ : Ω) : EuclideanPlane) from rfl, hon]
      exact ρ.nonneg i _
    · have hz : ψ i x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hin i h))
      rw [hz]
  refine ⟨ι, inferInstance, ⟨ψ, hsmooth,
    fun i => (hc i).extend_zero continuous_subtype_val, hin, hloc, hn, ?_⟩, b.c, hsub⟩
  intro x
  simp only [hon]
  exact ρ.sum_eq_one (mem_univ x)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeightedSobolevErrors
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative error estimates for multiplying local Sobolev
approximations by smooth partition functions. -/

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem aestronglyMeasurable_mul_of_support
    {V : Set EuclideanPlane} (hV : MeasurableSet V)
    {f ψ : EuclideanPlane → ℝ} (hf : AEStronglyMeasurable f (volume.restrict V))
    (hψ : Continuous ψ) (hs : Function.support ψ ⊆ V) :
    AEStronglyMeasurable (fun x => ψ x * f x) volume := by
  have hi : V.indicator (fun x => ψ x * f x) = fun x => ψ x * f x := by
    funext x
    by_cases hx : x ∈ V
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx, Function.notMem_support.mp (fun h => hx (hs h)), zero_mul]
  rw [← hi]
  exact (aestronglyMeasurable_indicator_iff hV).2 (hψ.aestronglyMeasurable.restrict.mul hf)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PartitionMixing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth mixing on an open planar domain. The locally finite sum is
represented by an actual finite sum in a neighborhood of each point. -/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity
namespace OpenPlanePartition

variable {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
  (ρ : OpenPlanePartition Ω ι)

theorem point_finite (x : EuclideanPlane) : HasFiniteSupport (fun i => ρ.weight i x) := by
  by_cases hx : x ∈ Ω
  · exact ρ.locallyFinite.point_finite ⟨x, hx⟩
  · have hz : ∀i, ρ.weight i x = 0 := fun i =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (ρ.inside i h))
    change (Function.support (fun i => ρ.weight i x)).Finite
    apply finite_empty.subset
    intro i hi
    exact False.elim (hi (hz i))

end OpenPlanePartition

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PartitionGradientBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive partition preserves a common pointwise bound on local
weak-gradient components, and hence their common L² bound. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem partition_component_pointFinite
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
    (ρ : OpenPlanePartition Ω ι) (G : ι → EuclideanPlane → ℝ) (x : EuclideanPlane) :
    HasFiniteSupport (fun j => ρ.weight j x * G j x) := by
  apply (ρ.point_finite x).subset
  intro j hj
  by_contra hn
  apply hj
  change ρ.weight j x * G j x = 0
  rw [show ρ.weight j x = 0 from not_not.mp hn, zero_mul]

theorem partition_component_aestronglyMeasurable
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, MeasurableSet (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (G : ι → EuclideanPlane → ℝ)
    (hG : ∀j, AEStronglyMeasurable (G j) (volume.restrict (W j))) :
    AEStronglyMeasurable (fun x => ∑ᶠ j, ρ.weight j x * G j x) volume := by
  exact aestronglyMeasurable_finsum_of_pointFinite volume _
    (fun j => aestronglyMeasurable_mul_of_support (hW j) (hG j) (ρ.smooth j).continuous
      ((subset_tsupport (ρ.weight j)).trans (hsub j)))
    (partition_component_pointFinite ρ G)

theorem partition_component_bound
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, MeasurableSet (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (G : ι → EuclideanPlane → ℝ) (g : EuclideanPlane → ℝ)
    (hG : ∀j, ∀ᵐ x ∂volume.restrict (W j), |G j x| ≤ g x) :
    ∀ᵐ x ∂volume.restrict Ω, |∑ᶠ j, ρ.weight j x * G j x| ≤ g x := by
  have hglobal : ∀ᵐ x ∂(volume : Measure EuclideanPlane), ∀j, x ∈ W j → |G j x| ≤ g x :=
    ae_all_iff.mpr (fun j => (ae_restrict_iff' (hW j)).1 (hG j))
  filter_upwards [ae_restrict_of_ae hglobal, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
  have hb : (∑ᶠ j, ρ.weight j x * G j x) ∈ Icc (-g x) (g x) := by
    simpa only [smul_eq_mul] using (convex_Icc (-g x) (g x)).finsum_mem
      (fun j => ρ.nonneg j x) (ρ.sum_one ⟨x, hxΩ⟩)
      (fun j hj => abs_le.mp (hx j (hsub j (subset_tsupport (ρ.weight j) hj))))
  exact abs_le.mpr hb

theorem partition_component_memLp
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, MeasurableSet (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (G : ι → EuclideanPlane → ℝ)
    (hGm : ∀j, AEStronglyMeasurable (G j) (volume.restrict (W j)))
    {g : EuclideanPlane → ℝ} (hg : MemLp g 2 (volume.restrict Ω))
    (hG : ∀j, ∀ᵐ x ∂volume.restrict (W j), |G j x| ≤ g x) :
    MemLp (fun x => ∑ᶠ j, ρ.weight j x * G j x) 2 (volume.restrict Ω) := by
  apply hg.of_le (partition_component_aestronglyMeasurable ρ W hW hsub G hGm).restrict
  filter_upwards [partition_component_bound ρ W hW hsub G g hG] with x hx
  simpa only [Real.norm_eq_abs] using hx.trans (le_abs_self (g x))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_FiniteCompletionUniformization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite uniformization of the actual terminal-disk complement

The complementary components are exactly the closed physical terminal
caps. In particular they are finite and nondegenerate. The published
finite circle theorem therefore applies after compact metric
uniformization; the resulting map is conformal on the retained core.
-/

open Set Function Filter
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem isConnected_openCompletedRegion {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))) :
    IsConnected (openCompletedRegion H) := by
  let S : Set ℂ := (⋃ i, closure (jordanInterior (H i)))ᶜ
  have hS : IsPreconnected S := isPreconnected_exterior_finite_jordanInteriors H hdisj
  have hinf : (∞ : Sphere) ∈ closure (((↑) : ℂ → Sphere) '' S) := by
    have hmem : ∀ᶠ z : ℂ in coclosedCompact ℂ, z ∈ S := by
      rw [coclosedCompact_eq_cocompact]
      exact (isCompact_iUnion fun i => isCompact_closure_jordanInterior (H i)).compl_mem_cocompact
    exact mem_closure_of_tendsto OnePoint.tendsto_coe_infty
      (hmem.mono fun z hz => ⟨z, hz, rfl⟩)
  have hsub : ((↑) : ℂ → Sphere) '' S ⊆ openCompletedRegion H := by
    rintro _ ⟨z, hz, rfl⟩ hb
    obtain ⟨i, x, hx, heq⟩ := mem_iUnion.mp hb
    have hxz : x = z := OnePoint.coe_injective heq
    exact hz (mem_iUnion.mpr ⟨i, hxz ▸ hx⟩)
  have hupper : openCompletedRegion H ⊆ closure (((↑) : ℂ → Sphere) '' S) := by
    intro p hp
    cases p using OnePoint.rec with
    | infty => exact hinf
    | coe z =>
      apply subset_closure
      refine ⟨z, ?_, rfl⟩
      intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact hp (mem_iUnion.mpr ⟨i, z, hi, rfl⟩)
  refine ⟨⟨∞, ?_⟩, (hS.image _ OnePoint.continuous_coe.continuousOn).subset_closure hsub hupper⟩
  intro hb
  obtain ⟨i, z, _, heq⟩ := mem_iUnion.mp hb
  exact OnePoint.coe_ne_infty z heq

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ExteriorDecay
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A uniform principal remainder estimate

The same coefficient-area input gives decay at infinity, uniformly in
the finite model. This is stronger than a uniform bounded remainder and
preserves the zero constant term when passing to a limit.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem norm_exterior_series_le_two_inv {c : ℕ → ℂ} {z w : ℂ}
    (hc : ∀ n, ‖c n‖ ≤ 1) (hz : 2 ≤ ‖z‖)
    (hw : HasSum (fun n => c n * (z⁻¹) ^ (n + 1)) w) : ‖w‖ ≤ 2 * ‖z‖⁻¹ := by
  let r : ℝ := ‖z‖⁻¹
  have hr0 : 0 ≤ r := inv_nonneg.mpr (norm_nonneg z)
  have hrhalf : r ≤ 1 / 2 := by
    dsimp only [r]
    simpa only [one_div] using
      (inv_le_inv₀ (by linarith : 0 < ‖z‖) (by norm_num : (0 : ℝ) < 2)).mpr hz
  have hr1 : r < 1 := by linarith
  have hg : HasSum (fun n : ℕ => r ^ (n + 1)) (r / (1 - r)) := by
    simpa only [pow_succ', div_eq_mul_inv] using (hasSum_geometric_of_lt_one hr0 hr1).mul_left r
  have hle := hw.norm_le_of_bounded hg (fun n => show ‖c n * (z⁻¹) ^ (n + 1)‖ ≤ r ^ (n + 1) from by
    rw [norm_mul, norm_pow, norm_inv]
    exact mul_le_of_le_one_left (pow_nonneg hr0 _) (hc n))
  refine hle.trans ?_
  change r / (1 - r) ≤ 2 * r
  apply (div_le_iff₀ (by linarith : 0 < 1 - r)).mpr
  nlinarith [mul_nonneg hr0 (show 0 ≤ 1 - 2 * r by linarith)]

theorem ExteriorCoefficientAreaTheorem.exterior_decay
    (harea : ExteriorCoefficientAreaTheorem) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {z | 1 < ‖z‖}) (hinj : InjOn F {z | 1 < ‖z‖})
    (hnorm : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ∀ z : ℂ, 2 ≤ ‖z‖ → ‖F z - z‖ ≤ 2 * ‖z‖⁻¹ := by
  obtain ⟨c, hc, hbound, hseries⟩ := harea F hF hinj hnorm
  intro z hz
  exact norm_exterior_series_le_two_inv (norm_coefficient_le_one hc hbound) hz
    (hseries z (by linarith))

theorem ExteriorCoefficientAreaTheorem.scaled_exterior_decay
    (harea : ExteriorCoefficientAreaTheorem) {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F {z | R < ‖z‖}) (hinj : InjOn F {z | R < ‖z‖})
    (hnorm : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ∀ z : ℂ, 2 * R ≤ ‖z‖ → ‖F z - z‖ ≤ 2 * R ^ 2 / ‖z‖ := by
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hnormR : ‖(R : ℂ)‖ = R := by simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  let H : ℂ → ℂ := fun z => F ((R : ℂ) * z) / (R : ℂ)
  have harg {z : ℂ} (hz : 1 < ‖z‖) : R < ‖(R : ℂ) * z‖ := by
    rw [norm_mul, hnormR]
    nlinarith
  have hH : DifferentiableOn ℂ H {z | 1 < ‖z‖} := by
    intro z hz
    have hfd := (hF _ (harg hz)).differentiableAt
      ((isOpen_lt continuous_const continuous_norm).mem_nhds (harg hz))
    exact ((hfd.comp z ((differentiableAt_id.const_mul (R : ℂ)))).div_const _).differentiableWithinAt
  have hHi : InjOn H {z | 1 < ‖z‖} := by
    intro z hz w hw heq
    have heq' : F ((R : ℂ) * z) = F ((R : ℂ) * w) := (div_left_inj' hRc).mp heq
    exact mul_left_cancel₀ hRc (hinj (harg hz) (harg hw) heq')
  have hnH := principal_remainder_rescale hRc hnorm
  intro z hz
  have hnormquot : ‖z / (R : ℂ)‖ = ‖z‖ / R := by rw [norm_div, hnormR]
  have hquot : 2 ≤ ‖z / (R : ℂ)‖ := by
    rw [hnormquot]
    exact (le_div_iff₀ hR).mpr (by linarith)
  have hb := harea.exterior_decay hH hHi hnH (z / (R : ℂ)) hquot
  have heq : H (z / (R : ℂ)) - z / (R : ℂ) = (F z - z) / (R : ℂ) := by
    dsimp only [H]
    rw [mul_div_cancel₀ z hRc]
    ring
  rw [heq, norm_div, hnormR, hnormquot] at hb
  have hzn : 0 < ‖z‖ := by linarith
  have hb' := (div_le_iff₀ hR).mp hb
  calc
    ‖F z - z‖ ≤ 2 * (‖z‖ / R)⁻¹ * R := hb'
    _ = 2 * R ^ 2 / ‖z‖ := by field_simp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_NormalFamilyInputs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Classical normal-family inputs

The two propositions are classical consequences of Ahlfors,
*Complex Analysis*, third edition (1979):

* Chapter 5, Theorem 15, p. 224 (Montel compactness), in its diagonal
  exhaustion form, with the varying-domain convention of Chapter 5,
  Section 1.1, pp. 176–177. Holomorphy of the locally uniform limit
  follows from Mathlib.
* Chapter 5, Theorem 2, p. 178 (Hurwitz), applied to injective maps as in
  Chapter 6, Section 1.1, p. 231. Discarding finitely many initial terms
  gives the eventually holomorphic and injective formulation.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem holomorphic_limit_on_exhaustion
    {D : ℕ → Set ℂ} {F : ℕ → ℂ → ℂ} {s : ℕ → ℕ} {f : ℂ → ℂ}
    (hD : ∀ n, IsOpen (D n)) (hmono : Monotone D)
    (hF : ∀ n, DifferentiableOn ℂ (F n) (D n)) (hs : StrictMono s)
    (hlim : TendstoLocallyUniformlyOn (fun n => F (s n)) f atTop (⋃ n, D n)) :
    DifferentiableOn ℂ f (⋃ n, D n) := by
  intro z hz
  obtain ⟨m, hm⟩ := mem_iUnion.mp hz
  have hFm : ∀ᶠ n in atTop, DifferentiableOn ℂ (F (s n)) (D m) := by
    filter_upwards [hs.tendsto_atTop.eventually_ge_atTop m] with n hn
    exact (hF (s n)).mono (hmono hn)
  have hf := (hlim.mono (subset_iUnion D m)).differentiableOn hFm (hD m)
  exact (hf.differentiableAt ((hD m).mem_nhds hm)).differentiableWithinAt

theorem univalent_limit_on_exhaustion
    (hhurwitz : HurwitzUnivalentLimit)
    {D : ℕ → Set ℂ} {F : ℕ → ℂ → ℂ} {s : ℕ → ℕ} {f : ℂ → ℂ}
    (hD : ∀ n, IsOpen (D n)) (hconn : ∀ n, IsConnected (D n))
    (hmono : Monotone D) (hF : ∀ n, DifferentiableOn ℂ (F n) (D n))
    (hFi : ∀ n, InjOn (F n) (D n)) (hs : StrictMono s)
    (hlim : TendstoLocallyUniformlyOn (fun n => F (s n)) f atTop (⋃ n, D n))
    (hnonconst : ∀ n, ¬ ∃ c : ℂ, ∀ z ∈ D n, f z = c) :
    InjOn f (⋃ n, D n) := by
  have hfm (m : ℕ) : InjOn f (D m) := by
    apply hhurwitz (D m) (fun n => F (s n)) f (hD m) (hconn m)
    · filter_upwards [hs.tendsto_atTop.eventually_ge_atTop m] with n hn
      exact ⟨(hF (s n)).mono (hmono hn), (hFi (s n)).mono (hmono hn)⟩
    · exact hlim.mono (subset_iUnion D m)
    · exact hnonconst m
  intro z hz w hw heq
  obtain ⟨m, hm⟩ := mem_iUnion.mp hz
  obtain ⟨n, hn⟩ := mem_iUnion.mp hw
  exact hfm (max m n) (hmono (le_max_left _ _) hm) (hmono (le_max_right _ _) hn) heq

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_NormalizedLimits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalized limits on exhausting retained cores

The uniform finite-model bounds give local boundedness. The common
decaying exterior remainder passes to the limit and prevents a constant
limit on any retained core containing the exterior. Hurwitz then gives
global injectivity. A further subsequence retains all these conclusions
and converges for every marked complementary disk simultaneously.
-/

open Set Filter Function Asymptotics Bornology Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem exterior_decay_le_radius {R t : ℝ} (hR : 0 < R) (ht : 2 * R ≤ t) :
    2 * R ^ 2 / t ≤ R := by
  apply (div_le_iff₀ (by linarith : 0 < t)).mpr
  nlinarith

theorem not_constant_of_exterior_decay
    {D : Set ℂ} {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hD : {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D)
    (hbound : ∀ z : ℂ, 2 * R ≤ ‖z‖ → ‖f z - z‖ ≤ 2 * R ^ 2 / ‖z‖) :
    ¬ ∃ c : ℂ, ∀ z ∈ D, f z = c := by
  rintro ⟨c, hc⟩
  let t : ℝ := 2 * R + ‖c‖ + 1
  have ht : 0 < t := by dsimp only [t] <;> positivity
  have htn : ‖(t : ℂ)‖ = t := by simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have hlarge : 2 * R ≤ ‖(t : ℂ)‖ := by
    rw [htn]
    dsimp only [t]
    linarith [norm_nonneg c]
  have hb := (hbound (t : ℂ) hlarge).trans (exterior_decay_le_radius hR hlarge)
  rw [hc _ (hD hlarge)] at hb
  have hnorm := norm_le_norm_sub_add (t : ℂ) c
  rw [norm_sub_rev, htn] at hnorm
  dsimp only [t] at hnorm
  linarith

theorem principal_remainder_of_exterior_decay
    {f : ℂ → ℂ} {R : ℝ}
    (hbound : ∀ z : ℂ, 2 * R ≤ ‖z‖ → ‖f z - z‖ ≤ 2 * R ^ 2 / ‖z‖) :
    (fun z => f z - z) =O[cobounded ℂ] (fun z => z⁻¹) := by
  apply isBigO_iff.mpr
  refine ⟨2 * R ^ 2, ?_⟩
  filter_upwards [eventually_cobounded_le_norm (E := ℂ) (2 * R)] with z hz
  simpa only [norm_inv, div_eq_mul_inv] using hbound z hz

theorem exists_normalized_univalent_limit
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit)
    {D : ℕ → Set ℂ} {F : ℕ → ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hD : ∀ n, IsOpen (D n)) (hconn : ∀ n, IsConnected (D n))
    (hmono : Monotone D) (hF : ∀ n, DifferentiableOn ℂ (F n) (D n))
    (hFi : ∀ n, InjOn (F n) (D n))
    (hext : {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D 0)
    (hbounded : ∀ n z, z ∈ D n → ‖z‖ ≤ 4 * R → ‖F n z‖ ≤ 5 * R)
    (hdecay : ∀ n z, 2 * R ≤ ‖z‖ → ‖F n z - z‖ ≤ 2 * R ^ 2 / ‖z‖) :
    ∃ (s : ℕ → ℕ) (f : ℂ → ℂ), StrictMono s ∧
      TendstoLocallyUniformlyOn (fun n => F (s n)) f atTop (⋃ n, D n) ∧
      DifferentiableOn ℂ f (⋃ n, D n) ∧ InjOn f (⋃ n, D n) ∧
      (fun z => f z - z) =O[cobounded ℂ] (fun z => z⁻¹) ∧
      ∀ z : ℂ, 2 * R ≤ ‖z‖ → ‖f z - z‖ ≤ 2 * R ^ 2 / ‖z‖ := by
  have hlocal : ∀ K : Set ℂ, IsCompact K → K ⊆ ⋃ n, D n →
      ∃ M : ℝ, ∀ n z, z ∈ K → z ∈ D n → ‖F n z‖ ≤ M := by
    intro K hK _
    obtain ⟨A, hA⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
    refine ⟨A + 5 * R, ?_⟩
    intro n z hzK hzD
    have hzA : ‖z‖ ≤ A := by simpa only [mem_closedBall, dist_zero_right] using hA hzK
    by_cases hz : ‖z‖ ≤ 4 * R
    · linarith [hbounded n z hzD hz, norm_nonneg z]
    · have hlarge : 2 * R ≤ ‖z‖ := by linarith
      have hb := (hdecay n z hlarge).trans (exterior_decay_le_radius hR hlarge)
      have hn := norm_le_norm_sub_add (F n z) z
      linarith
  obtain ⟨s, f, hs, hlim⟩ := hmontel D F hD hmono hF hlocal
  have hlimdecay : ∀ z : ℂ, 2 * R ≤ ‖z‖ → ‖f z - z‖ ≤ 2 * R ^ 2 / ‖z‖ := by
    intro z hz
    have hzU : z ∈ ⋃ n, D n := mem_iUnion.mpr ⟨0, hext hz⟩
    exact le_of_tendsto ((hlim.tendsto_at hzU).sub tendsto_const_nhds).norm
      (Eventually.of_forall (fun n => hdecay (s n) z hz))
  have hnonconst (n : ℕ) : ¬ ∃ c : ℂ, ∀ z ∈ D n, f z = c :=
    not_constant_of_exterior_decay hR (hext.trans (hmono (Nat.zero_le n))) hlimdecay
  exact ⟨s, f, hs, hlim, holomorphic_limit_on_exhaustion hD hmono hF hs hlim,
    univalent_limit_on_exhaustion hhurwitz hD hconn hmono hF hFi hs hlim hnonconst,
    principal_remainder_of_exterior_decay hlimdecay, hlimdecay⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereModelLimits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Applying normalized compactness to sphere models

All complex-plane hypotheses of the compactness theorem are obtained
from actual normalized smooth sphere equivalences and their retained
holomorphic cores. The exterior estimate follows from the univalent
area theorem.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem finite_part_injOn
    {f fi : Sphere → Sphere} {Q V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi Q V)
    (hinf : OnePoint.infty ∈ Q) (hfix : f OnePoint.infty = OnePoint.infty)
    {D : Set ℂ} (hDQ : ∀ z ∈ D, (z : Sphere) ∈ Q) :
    InjOn (fun z : ℂ => finiteCoord (f (z : Sphere))) D := by
  intro z hz w hw he
  apply OnePoint.coe_injective
  apply heq.bijOn.injOn (hDQ z hz) (hDQ w hw)
  calc
    f (z : Sphere) = ((finiteCoord (f (z : Sphere)) : ℂ) : Sphere) :=
      (coe_finiteCoord (heq.finite_forward hinf hfix (hDQ z hz))).symm
    _ = ((finiteCoord (f (w : Sphere)) : ℂ) : Sphere) := congrArg ((↑) : ℂ → Sphere) he
    _ = f (w : Sphere) := coe_finiteCoord (heq.finite_forward hinf hfix (hDQ w hw))

theorem finite_part_differentiableOn
    {f fi : Sphere → Sphere} {Q V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi Q V)
    (hinf : OnePoint.infty ∈ Q) (hfix : f OnePoint.infty = OnePoint.infty)
    {D : Set ℂ} (hD : IsOpen D) (hDQ : ∀ z ∈ D, (z : Sphere) ∈ Q)
    (hconf : IsConformalOn f (((↑) : ℂ → Sphere) '' D)) :
    DifferentiableOn ℂ (fun z : ℂ => finiteCoord (f (z : Sphere))) D := by
  intro z hz
  exact (analyticAt_finite_map_of_conformal (OnePoint.isOpenMap_coe D hD)
    hconf (mem_image_of_mem _ hz)
    (heq.finite_forward hinf hfix (hDQ z hz))).differentiableAt.differentiableWithinAt

theorem normalized_sphere_model_exterior_decay
    (harea : ExteriorCoefficientAreaTheorem)
    {f fi : Sphere → Sphere} {Q V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi Q V) {R : ℝ} (hR : 0 < R)
    (hsource : ((((↑) : ℂ → Sphere) '' Metric.ball 0 R)ᶜ) ⊆ Q)
    (hconf : IsConformalOn f ((((↑) : ℂ → Sphere) '' Metric.closedBall 0 R)ᶜ))
    (hnorm : IsPrincipalNormalized f) :
    ∀ z : ℂ, 2 * R ≤ ‖z‖ →
      ‖finiteCoord (f (z : Sphere)) - z‖ ≤ 2 * R ^ 2 / ‖z‖ := by
  have hinf : OnePoint.infty ∈ Q := hsource (by simp)
  have hDQ : ∀ z : ℂ, z ∈ {z | R < ‖z‖} → (z : Sphere) ∈ Q := by
    intro z hz
    apply hsource
    simpa only [OnePoint.coe_injective.mem_set_image, Metric.mem_ball,
      dist_zero_right, mem_compl_iff, not_lt] using hz.le
  apply harea.scaled_exterior_decay hR
  · apply finite_part_differentiableOn heq hinf hnorm.1
      (isOpen_lt continuous_const continuous_norm) hDQ
    apply hconf.mono
    rintro _ ⟨z, hz, rfl⟩
    simpa only [OnePoint.coe_injective.mem_set_image, Metric.mem_closedBall,
      dist_zero_right, mem_compl_iff, not_le] using (show R < ‖z‖ from hz)
  · exact finite_part_injOn heq hinf hnorm.1 hDQ
  · exact hnorm.2

theorem exists_normalized_limit_of_sphere_models
    (harea : ExteriorCoefficientAreaTheorem)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit)
    (f fi : ℕ → Sphere → Sphere) (Q V : ℕ → Set Sphere)
    (heq : ∀ n, IsSmoothSphereEquivalence (f n) (fi n) (Q n) (V n))
    (hV : ∀ n, IsOpen (V n))
    {D : ℕ → Set ℂ} (hD : ∀ n, IsOpen (D n))
    (hconn : ∀ n, IsConnected (D n)) (hmono : Monotone D)
    (hDQ : ∀ n z, z ∈ D n → (z : Sphere) ∈ Q n)
    (hcore : ∀ n, IsConformalOn (f n) (((↑) : ℂ → Sphere) '' D n))
    {R : ℝ} (hR : 0 < R)
    (hsource : ∀ n, ((((↑) : ℂ → Sphere) '' Metric.ball 0 R)ᶜ) ⊆ Q n)
    (hconf : ∀ n, IsConformalOn (f n)
      ((((↑) : ℂ → Sphere) '' Metric.closedBall 0 R)ᶜ))
    (hnorm : ∀ n, IsPrincipalNormalized (f n))
    (hext : {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D 0) :
    ∃ (s : ℕ → ℕ) (F : ℂ → ℂ), StrictMono s ∧
      TendstoLocallyUniformlyOn (fun n (z : ℂ) => finiteCoord (f (s n) (z : Sphere))) F
        atTop (⋃ n, D n) ∧
      DifferentiableOn ℂ F (⋃ n, D n) ∧ InjOn F (⋃ n, D n) ∧
      (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹) ∧
      ∀ z : ℂ, 2 * R ≤ ‖z‖ → ‖F z - z‖ ≤ 2 * R ^ 2 / ‖z‖ := by
  have hinf (n : ℕ) : OnePoint.infty ∈ Q n := hsource n (by simp)
  apply exists_normalized_univalent_limit hmontel hhurwitz hR hD hconn hmono
    (fun n => finite_part_differentiableOn (heq n) (hinf n) (hnorm n).1
      (hD n) (hDQ n) (hcore n))
    (fun n => finite_part_injOn (heq n) (hinf n) (hnorm n).1 (hDQ n)) hext
  · intro n z hz hzn
    obtain ⟨_, hbound⟩ := normalized_model_uniform_bound harea (heq n) (hV n)
      hR (hsource n) (hconf n) (hnorm n)
    obtain ⟨w, hw, hweq⟩ := hbound z (hDQ n z hz) hzn
    have he : w = finiteCoord (f n (z : Sphere)) := by
      have := congrArg finiteCoord hweq
      simpa only [finiteCoord_coe] using this
    simpa only [Metric.mem_closedBall, dist_zero_right, he] using hw
  · intro n
    exact normalized_sphere_model_exterior_decay harea (heq n) hR
      (hsource n) (hconf n) (hnorm n)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_LimitSphereExtension
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Extending a principally normalized limit across infinity

The uniform principal remainder does more than prevent a constant
limit: it gives continuity on the sphere and chart derivative one at
infinity. This step needs no further analytic input.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem continuousAt_extendAtInfinity_infty {F : ℂ → ℂ}
    (hF : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ContinuousAt (extendAtInfinity F) OnePoint.infty := by
  rw [OnePoint.continuousAt_infty']
  change Tendsto (fun z : ℂ => (F z : Sphere)) (coclosedCompact ℂ) (𝓝 OnePoint.infty)
  have hcoe : Tendsto ((↑) : ℂ → Sphere) (cobounded ℂ) (𝓝 OnePoint.infty) := by
    simpa only [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] using
      (OnePoint.tendsto_coe_infty (X := ℂ))
  rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
  exact hcoe.comp (principal_tendsto_cobounded hF)

theorem hasDerivAt_extendAtInfinity_chart {F : ℂ → ℂ}
    (hF : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    HasDerivAt (fun u => chart OnePoint.infty
      (extendAtInfinity F (chartSymm OnePoint.infty u))) 1 0 := by
  let G : ℂ → ℂ := fun u => chart OnePoint.infty
    (extendAtInfinity F (chartSymm OnePoint.infty u))
  have hG0 : G 0 = 0 := by simp [G, chart, chartSymm, sphereInv, finiteCoord]
  have hGu (u : ℂ) (hu : u ≠ 0) : G u = (F u⁻¹)⁻¹ := by
    simp only [G, chart, chartSymm, ite_true, if_true]
    have hsu : sphereInv (u : Sphere) = (u⁻¹ : ℂ) := by simp [sphereInv, hu]
    rw [hsu, extendAtInfinity_coe, finiteCoord_sphereInv_coe]
  have hid : Tendsto (fun u : ℂ => u) (𝓝[≠] (0 : ℂ)) (𝓝 0) := nhdsWithin_le_nhds
  have he := hid.mul ((principal_remainder_tendsto_zero hF).comp
    (tendsto_inv₀_nhdsNE_zero (α := ℂ)))
  have hprod : Tendsto (fun u : ℂ => u * F u⁻¹) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℂ))).add he
    simp only [zero_mul, add_zero] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu' : u ≠ 0 := hu
    change 1 + u * (F u⁻¹ - u⁻¹) = u * F u⁻¹
    rw [mul_sub, mul_inv_cancel₀ hu']
    ring
  apply hasDerivAt_iff_tendsto_slope.mpr
  have h := hprod.inv₀ one_ne_zero
  simp only [inv_one] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu' : u ≠ 0 := hu
  change (u * F u⁻¹)⁻¹ = slope G 0 u
  rw [slope_def_field, hG0, sub_zero, sub_zero, hGu u hu', div_eq_mul_inv, mul_inv_rev]

theorem isConformalAt_extendAtInfinity_infty {F : ℂ → ℂ}
    (hF : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    IsConformalAt (extendAtInfinity F) OnePoint.infty := by
  refine ⟨continuousAt_extendAtInfinity_infty hF, 1, one_ne_zero, ?_⟩
  simpa only [extendAtInfinity_infty, chart_infty_self] using hasDerivAt_extendAtInfinity_chart hF

theorem isPrincipalNormalized_extendAtInfinity {F : ℂ → ℂ}
    (hF : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    IsPrincipalNormalized (extendAtInfinity F) :=
  ⟨rfl, by simpa only [extendAtInfinity_coe, finiteCoord_coe] using hF⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_LimitConformality
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conformality of the normalized limit

`HurwitzZeroFreeLimit` records the zero-free form of the same published
Hurwitz theorem already used for injective limits: Ahlfors, *Complex
Analysis*, third edition (1979), Chapter 5, Theorem 2, p. 178. Applied
to the derivatives, it gives a nonzero limiting derivative unless the
limit is constant. The latter alternative is ruled out on each core.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem finite_part_deriv_ne_zero
    {f : Sphere → Sphere} {z : ℂ}
    (hf : IsConformalAt f (z : Sphere)) (hfinite : f (z : Sphere) ≠ OnePoint.infty) :
    deriv (fun w : ℂ => finiteCoord (f (w : Sphere))) z ≠ 0 := by
  obtain ⟨_, d, hd, hder⟩ := hf
  have he : (fun w => chart (f (z : Sphere)) (f (chartSymm (z : Sphere) w))) =
      (fun w : ℂ => finiteCoord (f (w : Sphere))) := by
    funext w
    simp only [chart, hfinite, ite_false, if_false, chartSymm_coe_apply]
  rw [he, chart_coe_self] at hder
  rwa [hder.deriv]

theorem deriv_ne_zero_of_holomorphic_limits
    (hhurwitz : HurwitzZeroFreeLimit)
    {D : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hD : IsOpen D) (hconn : IsConnected D)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) D ∧ ∀ z ∈ D, deriv (F n) z ≠ 0)
    (hlim : TendstoLocallyUniformlyOn F f atTop D)
    (hnonconst : ¬ ∃ c : ℂ, ∀ z ∈ D, f z = c) :
    ∀ z ∈ D, deriv f z ≠ 0 := by
  have hdiff : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) D := hF.mono fun _ h => h.1
  have hderdiff : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (deriv (F n)) D ∧ ∀ z ∈ D, deriv (F n) z ≠ 0 := by
    filter_upwards [hF] with n hn
    exact ⟨hn.1.deriv hD, hn.2⟩
  have hderlim := hlim.deriv hdiff hD
  rcases hhurwitz D (fun n => deriv (F n)) (deriv f) hD hconn hderdiff hderlim with hz | hn
  · exact (hnonconst (hD.exists_is_const_of_deriv_eq_zero hconn.isPreconnected
      (hlim.differentiableOn hdiff hD) (fun z hzD => hz z hzD))).elim
  · exact hn

theorem deriv_ne_zero_on_exhaustion
    (hhurwitz : HurwitzZeroFreeLimit)
    {D : ℕ → Set ℂ} {F : ℕ → ℂ → ℂ} {s : ℕ → ℕ} {f : ℂ → ℂ}
    (hD : ∀ n, IsOpen (D n)) (hconn : ∀ n, IsConnected (D n)) (hmono : Monotone D)
    (hF : ∀ n, DifferentiableOn ℂ (F n) (D n))
    (hFn : ∀ n z, z ∈ D n → deriv (F n) z ≠ 0) (hs : StrictMono s)
    (hlim : TendstoLocallyUniformlyOn (fun n => F (s n)) f atTop (⋃ n, D n))
    (hnonconst : ∀ n, ¬ ∃ c : ℂ, ∀ z ∈ D n, f z = c) :
    ∀ z ∈ ⋃ n, D n, deriv f z ≠ 0 := by
  intro z hz
  obtain ⟨m, hm⟩ := mem_iUnion.mp hz
  apply deriv_ne_zero_of_holomorphic_limits hhurwitz (hD m) (hconn m) ?_
    (hlim.mono (subset_iUnion D m)) (hnonconst m) z hm
  filter_upwards [hs.tendsto_atTop.eventually_ge_atTop m] with n hn
  exact ⟨(hF (s n)).mono (hmono hn), fun w hw => hFn (s n) w (hmono hn hw)⟩

theorem isConformalOn_extendAtInfinity
    {D : Set ℂ} {F : ℂ → ℂ} (hD : IsOpen D) (hF : DifferentiableOn ℂ F D)
    (hd : ∀ z ∈ D, deriv F z ≠ 0)
    (hnorm : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    IsConformalOn (extendAtInfinity F) (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}) := by
  rintro p (⟨z, hz, rfl⟩ | hp)
  · exact isConformalAt_extendAtInfinity_coe
      ((hF z hz).differentiableAt (hD.mem_nhds hz)) (hd z hz)
  · rw [mem_singleton_iff] at hp
    subst p
    exact isConformalAt_extendAtInfinity_infty hnorm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_NormalizedLimitEquivalence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The normalized limit as a sphere conformal equivalence

The source includes infinity. The inverse on the image is constructed
by the local inverse theorem, so the limiting map satisfies the same
two-sided conformal predicate as the final circle-domain target.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem isOpen_finite_domain_with_infty
    {D : Set ℂ} (hD : IsOpen D) {R : ℝ}
    (hext : {z : ℂ | R ≤ ‖z‖} ⊆ D) :
    IsOpen (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}) := by
  have hc : IsCompact Dᶜ := by
    apply (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hD.isClosed_compl
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hn
    exact hz (hext (le_of_lt (lt_of_not_ge hn)))
  apply (OnePoint.isOpen_iff_of_mem' (by simp)).mpr
  simpa only [preimage_union, OnePoint.coe_injective.preimage_image,
    OnePoint.coe_preimage_infty, union_empty] using And.intro hc hD

theorem injOn_extendAtInfinity
    {D : Set ℂ} {F : ℂ → ℂ} (hF : InjOn F D) :
    InjOn (extendAtInfinity F) (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}) := by
  rintro p (⟨z, hz, rfl⟩ | hp) q (⟨w, hw, rfl⟩ | hq) he
  · exact congrArg ((↑) : ℂ → Sphere) (hF hz hw (OnePoint.coe_injective he))
  · rw [mem_singleton_iff] at hq
    subst q
    exact (OnePoint.coe_ne_infty (F z) he).elim
  · rw [mem_singleton_iff] at hp
    subst p
    exact (OnePoint.coe_ne_infty (F w) he.symm).elim
  · rw [mem_singleton_iff] at hp hq
    exact hp.trans hq.symm

theorem normalized_limit_conformal_equivalence
    {D : Set ℂ} {F : ℂ → ℂ} (hD : IsOpen D)
    (hF : DifferentiableOn ℂ F D) (hFi : InjOn F D)
    (hd : ∀ z ∈ D, deriv F z ≠ 0)
    (hnorm : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹))
    {R : ℝ} (hext : {z : ℂ | R ≤ ‖z‖} ⊆ D) :
    IsConformalEquivalence (extendAtInfinity F)
      (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty})
      (extendAtInfinity F '' (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty})) :=
  isConformalEquivalence_of_injOn (isConformalOn_extendAtInfinity hD hF hd hnorm)
    (isOpen_finite_domain_with_infty hD hext) (injOn_extendAtInfinity hFi)

theorem exists_conformal_limit_of_sphere_models
    (harea : ExteriorCoefficientAreaTheorem)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit)
    (hzero : HurwitzZeroFreeLimit)
    (f fi : ℕ → Sphere → Sphere) (Q V : ℕ → Set Sphere)
    (heq : ∀ n, IsSmoothSphereEquivalence (f n) (fi n) (Q n) (V n))
    (hV : ∀ n, IsOpen (V n))
    {D : ℕ → Set ℂ} (hD : ∀ n, IsOpen (D n))
    (hconn : ∀ n, IsConnected (D n)) (hmono : Monotone D)
    (hDQ : ∀ n z, z ∈ D n → (z : Sphere) ∈ Q n)
    (hcore : ∀ n, IsConformalOn (f n) (((↑) : ℂ → Sphere) '' D n))
    {R : ℝ} (hR : 0 < R)
    (hsource : ∀ n, ((((↑) : ℂ → Sphere) '' Metric.ball 0 R)ᶜ) ⊆ Q n)
    (hconf : ∀ n, IsConformalOn (f n)
      ((((↑) : ℂ → Sphere) '' Metric.closedBall 0 R)ᶜ))
    (hnorm : ∀ n, IsPrincipalNormalized (f n))
    (hext : {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D 0) :
    ∃ (s : ℕ → ℕ) (F : ℂ → ℂ), StrictMono s ∧
      TendstoLocallyUniformlyOn (fun n (z : ℂ) => finiteCoord (f (s n) (z : Sphere))) F
        atTop (⋃ n, D n) ∧
      IsPrincipalNormalized (extendAtInfinity F) ∧
      IsConformalEquivalence (extendAtInfinity F)
        (((↑) : ℂ → Sphere) '' (⋃ n, D n) ∪ {OnePoint.infty})
        (extendAtInfinity F '' (((↑) : ℂ → Sphere) '' (⋃ n, D n) ∪ {OnePoint.infty})) := by
  obtain ⟨s, F, hs, hlim, hF, hFi, hFnorm, hdecay⟩ :=
    exists_normalized_limit_of_sphere_models harea hmontel hhurwitz f fi Q V heq hV
      hD hconn hmono hDQ hcore hR hsource hconf hnorm hext
  have hinf (n : ℕ) : OnePoint.infty ∈ Q n := hsource n (by simp)
  have hdiff (n : ℕ) :
      DifferentiableOn ℂ (fun z : ℂ => finiteCoord (f n (z : Sphere))) (D n) :=
    finite_part_differentiableOn (heq n) (hinf n) (hnorm n).1 (hD n) (hDQ n) (hcore n)
  have hnonzero (n : ℕ) (z : ℂ) (hz : z ∈ D n) :
      deriv (fun w : ℂ => finiteCoord (f n (w : Sphere))) z ≠ 0 :=
    finite_part_deriv_ne_zero (hcore n _ (mem_image_of_mem _ hz))
      ((heq n).finite_forward (hinf n) (hnorm n).1 (hDQ n z hz))
  have hnonconst (n : ℕ) : ¬ ∃ c : ℂ, ∀ z ∈ D n, F z = c :=
    not_constant_of_exterior_decay hR (hext.trans (hmono (Nat.zero_le n))) hdecay
  have hd := deriv_ne_zero_on_exhaustion hzero hD hconn hmono hdiff hnonzero hs hlim hnonconst
  refine ⟨s, F, hs, hlim, isPrincipalNormalized_extendAtInfinity hFnorm, ?_⟩
  exact normalized_limit_conformal_equivalence (isOpen_iUnion hD) hF hFi hd hFnorm
    (hext.trans (subset_iUnion D 0))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ConnectedCoreExhaustion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Connected retained-core exhaustions

Compact exhaustion and paths in an open plane domain give nested connected
open cores with compact closure in that domain. Adjoining one fixed exterior
then gives the cofinite cores required by normalized model compactness.
-/

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_connected_plane_exhaustion
    {G : Set ℂ} (hG : IsOpen G) (hconn : IsConnected G)
    {z₀ : ℂ} (hz₀ : z₀ ∈ G) :
    ∃ U : ℕ → Set ℂ,
      (∀ n, IsOpen (U n)) ∧ (∀ n, IsConnected (U n)) ∧ Monotone U ∧
      (∀ n, IsCompact (closure (U n)) ∧ closure (U n) ⊆ G) ∧
      (⋃ n, U n) = G ∧ z₀ ∈ U 0 := by
  let : LocallyCompactSpace G := hG.locallyCompactSpace
  let : LocallyPathConnectedSpace G := hG.locallyPathConnectedSpace
  let C := CompactExhaustion.choice G
  let x₀ : G := ⟨z₀, hz₀⟩
  obtain ⟨k₀, hk₀⟩ := C.exists_mem x₀
  let A : ℕ → Set G := fun n => connectedComponentIn (interior (C (n + k₀ + 1))) x₀
  have hxA (n : ℕ) : x₀ ∈ A n := by
    apply mem_connectedComponentIn
    apply C.subset_interior (by omega : k₀ < n + k₀ + 1)
    exact hk₀
  have hAo (n : ℕ) : IsOpen (A n) := isOpen_interior.connectedComponentIn
  have hAc (n : ℕ) : IsConnected (A n) :=
    ⟨⟨x₀, hxA n⟩, isPreconnected_connectedComponentIn⟩
  have hAm : Monotone A := by
    intro m n hmn
    exact connectedComponentIn_mono _ (interior_mono (C.subset (by omega)))
  let U : ℕ → Set ℂ := fun n => Subtype.val '' A n
  have hUclosed (n : ℕ) : closure (U n) ⊆ Subtype.val '' C (n + k₀ + 1) := by
    apply closure_minimal _ ((C.isCompact _).image continuous_subtype_val).isClosed
    exact image_mono ((connectedComponentIn_subset _ _).trans interior_subset)
  refine ⟨U, fun n => hG.isOpenMap_subtype_val _ (hAo n),
    fun n => (hAc n).image _ continuous_subtype_val.continuousOn,
    fun m n hmn => image_mono (hAm hmn), ?_, ?_, ⟨x₀, hxA 0, rfl⟩⟩
  · intro n
    exact ⟨((C.isCompact _).image continuous_subtype_val).of_isClosed_subset
      isClosed_closure (hUclosed n), (hUclosed n).trans (by rintro _ ⟨x, _, rfl⟩; exact x.property)⟩
  · apply Subset.antisymm
    · exact iUnion_subset fun n => by rintro _ ⟨x, _, rfl⟩; exact x.property
    · intro z hz
      let x : G := ⟨z, hz⟩
      have hj : Joined x₀ x := (hG.isConnected_iff_isPathConnected.mp hconn).joinedIn
        z₀ hz₀ z hz |>.joined_subtype
      let γ := hj.somePath
      obtain ⟨k, hk⟩ := C.exists_superset_of_isCompact (isCompact_range γ.continuous)
      have hrange : range γ ⊆ interior (C (k + k₀ + 1)) :=
        hk.trans (C.subset_interior (by omega : k < k + k₀ + 1))
      have hx : x ∈ A k :=
        (isConnected_range γ.continuous).isPreconnected.subset_connectedComponentIn
          (by exact ⟨0, γ.source⟩) hrange (by exact ⟨1, γ.target⟩)
      exact mem_iUnion.mpr ⟨k, x, hx, rfl⟩

/-- The cofinite cores retain a full fixed exterior, while the closure
of every core stays in the original domain. -/
theorem exists_cofinite_connected_plane_exhaustion
    {G : Set ℂ} (hG : IsOpen G) (hconn : IsConnected G)
    {R : ℝ} (hR : 0 < R) (hext : {z : ℂ | R ≤ ‖z‖} ⊆ G) :
    ∃ D : ℕ → Set ℂ,
      (∀ n, IsOpen (D n)) ∧ (∀ n, IsConnected (D n)) ∧ Monotone D ∧
      (∀ n, closure (D n) ⊆ G) ∧ (⋃ n, D n) = G ∧
      {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D 0 := by
  let z₀ : ℂ := (2 * R : ℝ)
  have hnorm : ‖z₀‖ = 2 * R := by
    simp only [z₀, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * R)]
  have hz₀ : z₀ ∈ G := hext (by change R ≤ ‖z₀‖; rw [hnorm]; linarith)
  obtain ⟨U, hUo, hUc, hUm, hUcl, hUunion, hbase⟩ :=
    exists_connected_plane_exhaustion hG hconn hz₀
  let E : Set ℂ := (closedBall (0 : ℂ) R)ᶜ
  have hEo : IsOpen E := isClosed_closedBall.isOpen_compl
  have hEc : IsConnected E := isConnected_complex_exterior_closedBall hR.le
  have hzE : z₀ ∈ E := by
    simpa only [E, mem_compl_iff, mem_closedBall, dist_zero_right, not_le, hnorm] using
      (by linarith : R < 2 * R)
  have hEcl : closure E ⊆ G := by
    rw [closure_compl, interior_closedBall (0 : ℂ) hR.ne']
    intro z hz
    apply hext
    change R ≤ ‖z‖
    simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt] using hz
  refine ⟨fun n => U n ∪ E, fun n => (hUo n).union hEo,
    fun n => (hUc n).union ⟨z₀, hUm (Nat.zero_le n) hbase, hzE⟩ hEc,
    fun m n hmn => union_subset_union_left E (hUm hmn), ?_, ?_, ?_⟩
  · intro n
    rw [closure_union]
    exact union_subset (hUcl n).2 hEcl
  · ext z
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨n, hz | hz⟩
      · exact (hUcl n).2 (subset_closure hz)
      · exact hEcl (subset_closure hz)
    · intro hz
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hUunion.symm ▸ hz)
      exact ⟨n, Or.inl hn⟩
  · intro z hz
    right
    have hz' : 2 * R ≤ ‖z‖ := hz
    change z ∉ closedBall (0 : ℂ) R
    rw [mem_closedBall, dist_zero_right, not_le]
    linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereCoreExhaustion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual source cores for domains containing infinity

The open connected cores exhaust the given domain. Their finite closures,
with infinity added, are compact subsets of the domain and can therefore
be prescribed in the finite-transfer construction.
-/

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem isClosed_finite_set_with_infty {C : Set ℂ} (hC : IsClosed C) :
    IsClosed (((↑) : ℂ → Sphere) '' C ∪ {OnePoint.infty}) := by
  have he : (((↑) : ℂ → Sphere) '' C ∪ {OnePoint.infty})ᶜ =
      ((↑) : ℂ → Sphere) '' Cᶜ := by
    ext p
    cases p using OnePoint.rec with
    | infty => simp
    | coe z => simp only [mem_compl_iff, mem_union, OnePoint.coe_injective.mem_set_image,
        mem_singleton_iff, OnePoint.coe_ne_infty, or_false]
  rw [← isOpen_compl_iff, he]
  exact OnePoint.isOpen_image_coe.mpr hC.isOpen_compl

theorem exists_sphere_connected_core_exhaustion
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) :
    ∃ (R : ℝ) (D : ℕ → Set ℂ) (K : ℕ → Set Sphere),
      0 < R ∧ (∀ n, IsOpen (D n)) ∧ (∀ n, IsConnected (D n)) ∧ Monotone D ∧
      (∀ n, K n = ((↑) : ℂ → Sphere) '' closure (D n) ∪ {OnePoint.infty}) ∧
      (∀ n, IsCompact (K n) ∧ K n ⊆ G) ∧
      (∀ n, ((↑) : ℂ → Sphere) '' D n ∪ {OnePoint.infty} ⊆ interior (K n)) ∧
      (⋃ n, ((↑) : ℂ → Sphere) '' D n ∪ {OnePoint.infty}) = G ∧
      {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D 0 ∧
      ((((↑) : ℂ → Sphere) '' ball 0 R)ᶜ) ⊆ G := by
  let A : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' G
  have hA : IsOpen A := hG.preimage OnePoint.continuous_coe
  have hAc : IsCompact Aᶜ := ((OnePoint.isOpen_iff_of_mem hinf).mp hG).2
  obtain ⟨R, hR, hbound⟩ := hAc.isBounded.exists_pos_norm_lt
  have hext : {z : ℂ | R ≤ ‖z‖} ⊆ A := by
    intro z hz
    by_contra hzA
    exact (not_lt_of_ge hz) (hbound z hzA)
  have hAn : A.Nonempty := by
    refine ⟨(R : ℂ), hext ?_⟩
    change R ≤ ‖(R : ℂ)‖
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, le_refl]
  have hconnA : IsConnected A := ⟨hAn,
    (finite_part_connected_unbounded hconn.isPreconnected (mem_interior_iff_mem_nhds.mpr (hG.mem_nhds hinf))).1⟩
  obtain ⟨D, hDo, hDc, hDm, hDcl, hDunion, hDexterior⟩ :=
    exists_cofinite_connected_plane_exhaustion hA hconnA hR hext
  let K : ℕ → Set Sphere := fun n => ((↑) : ℂ → Sphere) '' closure (D n) ∪ {OnePoint.infty}
  have hDG (n : ℕ) : ((↑) : ℂ → Sphere) '' D n ∪ {OnePoint.infty} ⊆ G := by
    rintro p (⟨z, hz, rfl⟩ | hp)
    · exact hDcl n (subset_closure hz)
    · exact mem_singleton_iff.mp hp ▸ hinf
  have hDE (n : ℕ) : {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D n :=
    hDexterior.trans (hDm (Nat.zero_le n))
  refine ⟨R, D, K, hR, hDo, hDc, hDm, fun _ => rfl, ?_, ?_, ?_, hDexterior, ?_⟩
  · intro n
    refine ⟨(isClosed_finite_set_with_infty isClosed_closure).isCompact, ?_⟩
    rintro p (⟨z, hz, rfl⟩ | hp)
    · exact hDcl n hz
    · exact mem_singleton_iff.mp hp ▸ hinf
  · intro n
    apply interior_maximal ?_ (isOpen_finite_domain_with_infty (hDo n) (hDE n))
    exact union_subset_union_left _ (image_mono subset_closure)
  · apply Subset.antisymm (iUnion_subset hDG)
    intro p hp
    cases p using OnePoint.rec with
    | infty => exact mem_iUnion.mpr ⟨0, Or.inr rfl⟩
    | coe z =>
      have hz : z ∈ A := hp
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hDunion.symm ▸ hz)
      exact mem_iUnion.mpr ⟨n, Or.inl ⟨z, hn, rfl⟩⟩
  · intro p hp
    cases p using OnePoint.rec with
    | infty => exact hinf
    | coe z =>
      apply hext
      change R ≤ ‖z‖
      simpa only [OnePoint.coe_injective.mem_set_image, mem_compl_iff, mem_ball,
        dist_zero_right, not_lt] using hp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ConnectedCoreNeighborhood
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compact connected neighborhoods inside the source

A compact subset of a domain containing infinity lies strictly inside a
compact connected subset of that domain which also contains a neighborhood
of infinity. This lets successive finite Jordan cores retain earlier ones.
-/

open Set Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem closure_finite_domain_with_infty (D : Set ℂ) :
    closure (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}) =
      ((↑) : ℂ → Sphere) '' closure D ∪ {OnePoint.infty} := by
  apply Subset.antisymm
  · exact closure_minimal (union_subset_union_left _ (image_mono subset_closure))
      (isClosed_finite_set_with_infty isClosed_closure)
  · apply union_subset
    · exact (image_closure_subset_closure_image OnePoint.continuous_coe).trans
        (closure_mono subset_union_left)
    · exact subset_union_right.trans subset_closure

theorem isConnected_finite_domain_with_infty
    {D : Set ℂ} (hD : IsConnected D) {R : ℝ}
    (hext : {z : ℂ | R ≤ ‖z‖} ⊆ D) :
    IsConnected (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}) := by
  have hunbounded : ¬ Bornology.IsBounded D := by
    intro h
    have hc := (isBounded_closedBall (x := (0 : ℂ)) (r := R)).union h
    apply NormedSpace.unbounded_univ ℝ ℂ
    apply hc.subset
    intro z _
    by_cases hz : ‖z‖ ≤ R
    · exact Or.inl (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
    · exact Or.inr (hext (le_of_lt (lt_of_not_ge hz)))
  have hinf := infty_mem_closure_image_of_unbounded hunbounded
  apply (hD.image _ OnePoint.continuous_coe.continuousOn).subset_closure subset_union_left
  exact union_subset subset_closure (singleton_subset_iff.mpr hinf)

theorem exists_compact_connected_core_neighborhood
    {G S : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hS : IsCompact S) (hSG : S ⊆ G) :
    ∃ P : Set Sphere, IsCompact P ∧ IsConnected P ∧ P ⊆ G ∧
      S ⊆ interior P ∧ OnePoint.infty ∈ interior P := by
  obtain ⟨R, D, K, hR, hDo, hDc, hDm, hKdef, hK, hDK, hcover, hext, _⟩ :=
    exists_sphere_connected_core_exhaustion hG hconn hinf
  let U : ℕ → Set Sphere := fun n => ((↑) : ℂ → Sphere) '' D n ∪ {OnePoint.infty}
  have hUo (n : ℕ) : IsOpen (U n) :=
    isOpen_finite_domain_with_infty (hDo n) (hext.trans (hDm (Nat.zero_le n)))
  have hUm : Monotone U := fun _ _ h => union_subset_union_left _ (image_mono (hDm h))
  obtain ⟨n, hn⟩ := hS.elim_directed_cover U hUo
    (fun p hp => hcover.symm ▸ hSG hp) hUm.directed_le
  refine ⟨K n, (hK n).1, ?_, (hK n).2, hn.trans (hDK n), hDK n (Or.inr rfl)⟩
  rw [hKdef n, ← closure_finite_domain_with_infty]
  exact (isConnected_finite_domain_with_infty (hDc n)
    (hext.trans (hDm (Nat.zero_le n)))).closure

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ClosedJordanCore
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Closed cores bounded by a finite disjoint Jordan family

The closed common exterior is regular closed, its interior is the already
constructed connected open completed region, and its boundary is exactly
the union of the specified Jordan curves.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem interior_finite_disjoint_closed
    {I : Type*} [Finite I] (C : I → Set Sphere)
    (hC : ∀ i, IsClosed (C i)) (hd : Pairwise (Disjoint on C)) :
    interior (⋃ i, C i) = ⋃ i, interior (C i) := by
  classical
  apply Subset.antisymm
  · intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp (interior_subset hp)
    let B : Set Sphere := ⋃ j : {j : I // j ≠ i}, C j
    have hB : IsClosed B := isClosed_iUnion_of_finite fun j => hC j
    have hpB : p ∉ B := by
      intro h
      obtain ⟨j, hj⟩ := mem_iUnion.mp h
      exact Set.disjoint_left.mp (hd j.property.symm) hi hj
    have hsub : interior (⋃ j, C j) ∩ Bᶜ ⊆ C i := by
      rintro q ⟨hq, hqB⟩
      obtain ⟨j, hj⟩ := mem_iUnion.mp (interior_subset hq)
      by_cases hji : j = i
      · exact hji ▸ hj
      · exact (hqB (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)).elim
    exact mem_iUnion.mpr ⟨i, interior_maximal hsub (isOpen_interior.inter hB.isOpen_compl) ⟨hp, hpB⟩⟩
  · exact iUnion_subset fun i => interior_mono (subset_iUnion C i)

theorem closure_interior_closedJordanCore
    {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))) :
    closure (interior (closedJordanCore H)) = closedJordanCore H := by
  rw [interior_closedJordanCore, openCompletedRegion, closure_compl,
    interior_finite_disjoint_closed (fun i => closedTerminalCap (H i))
      (fun i => (isCompact_closedTerminalCap (H i)).isClosed) (disjoint_closedTerminalCaps H hd)]
  simp only [interior_closedTerminalCap, closedJordanCore]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PrescribedJordanCore
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A finite smooth Jordan core retaining a prescribed connected set

Sard, compact one-manifold classification and Schoenflies produce disjoint
smooth filled contours around the complement. Their common exterior stays
in the original domain and retains the prescribed compact set in its interior.
-/

open Set Function
open scoped Topology Manifold ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem exists_prescribed_jordan_core
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {G P : Set Sphere} (hG : IsOpen G) (hP : IsCompact P) (hPG : P ⊆ G)
    (hconn : IsPreconnected P) (hinf : OnePoint.infty ∈ interior P) :
    ∃ (n : ℕ) (H : Fin n → ℂ ≃ₜ ℂ) (γ : Fin n → Circle → ℂ),
      Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) ∧
      closedJordanCore H ⊆ G ∧ P ⊆ interior (closedJordanCore H) ∧
      (∀ i, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧ Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (H i)) = range (γ i)) := by
  let A : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' Gᶜ
  let V : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' Pᶜ
  have hinfG : OnePoint.infty ∈ G := hPG (interior_subset hinf)
  have hAc : IsCompact A := isCompact_finite_preimage hG.isClosed_compl
    (by simpa only [mem_compl_iff, not_not] using hinfG)
  have hVo : IsOpen V := hP.isClosed.isOpen_compl.preimage OnePoint.continuous_coe
  have hAV : A ⊆ V := preimage_mono (compl_subset_compl.mpr hPG)
  have hVc : IsPreconnected Vᶜ ∧ ¬ Bornology.IsBounded Vᶜ := by
    simpa only [V, ← preimage_compl, compl_compl] using
      finite_part_connected_unbounded hconn hinf
  obtain ⟨f, t, γ₀, H₀, s, hs, hcover, hdisj, hinside, hcurves⟩ :=
    exists_finite_smooth_jordan_cover hsard hschoenflies hAc (Subset.refl A)
      (by simp only [sdiff_self, isClosed_empty]) hVo hAV hVc.1 hVc.2
  let : Fintype s := hs.fintype
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let H : Fin (Fintype.card s) → ℂ ≃ₜ ℂ := fun i => H₀ (e.symm i)
  let γ : Fin (Fintype.card s) → Circle → ℂ := fun i => γ₀ (e.symm i)
  have hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) := by
    intro i j hij
    exact hdisj (e.symm i).property (e.symm j).property
      (fun h => hij (e.symm.injective (Subtype.ext h)))
  have hcover' : A ⊆ ⋃ i, jordanInterior (H i) := by
    intro z hz
    obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp (hcover hz)
    refine mem_iUnion.mpr ⟨e ⟨j, hj⟩, ?_⟩
    simpa only [H, e.symm_apply_apply] using hzj
  have hinside' (i : Fin (Fintype.card s)) : closure (jordanInterior (H i)) ⊆ V :=
    hinside _ (e.symm i).property
  refine ⟨Fintype.card s, H, γ, hd, ?_, ?_, ?_⟩
  · intro p hp
    by_contra hpG
    cases p using OnePoint.rec with
    | infty => exact hpG hinfG
    | coe z =>
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover' hpG)
      exact hp (mem_iUnion.mpr ⟨i, z, hi, rfl⟩)
  · rw [interior_closedJordanCore]
    intro p hp hbad
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hbad
    exact hinside' i hz hp
  · intro i
    obtain ⟨hsm, hemb, hfront, _⟩ := hcurves _ (e.symm i).property
    exact ⟨hsm, hemb, hfront⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothJordanExhaustion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A strict exhaustion by finite smooth Jordan cores

Every prescribed compact subset is retained in the interior of a finite
Jordan core. Recursive application retains the preceding core and the next
compact exhaustion set. The construction uses Sard, one-manifold
classification, and Schoenflies.
-/

open Set Function
open scoped Topology Manifold ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

namespace SmoothJordanCore

variable {G : Set Sphere} (C : SmoothJordanCore G)

theorem regular : closure (interior C.carrier) = C.carrier :=
  closure_interior_closedJordanCore C.disk C.disjoint

theorem connected_interior : IsConnected (interior C.carrier) := by
  rw [carrier, interior_closedJordanCore]
  exact isConnected_openCompletedRegion C.disk C.disjoint

theorem infty_interior : OnePoint.infty ∈ interior C.carrier := by
  rw [carrier, interior_closedJordanCore]
  intro h
  obtain ⟨i, z, _, hz⟩ := mem_iUnion.mp h
  exact OnePoint.coe_ne_infty z hz

end SmoothJordanCore

theorem exists_smooth_jordan_core_containing
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {G S : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hS : IsCompact S) (hSG : S ⊆ G) :
    ∃ C : SmoothJordanCore G, S ⊆ interior C.carrier := by
  obtain ⟨P, hPc, hPconn, hPG, hSP, hinfP⟩ :=
    exists_compact_connected_core_neighborhood hG hconn hinf hS hSG
  obtain ⟨n, H, γ, hd, hKG, hPK, hcurves⟩ :=
    exists_prescribed_jordan_core hsard hschoenflies hG hPc hPG hPconn.isPreconnected hinfP
  let C : SmoothJordanCore G := ⟨n, H, γ, hd, hKG,
    fun i => (hcurves i).1, fun i => (hcurves i).2.1, fun i => (hcurves i).2.2⟩
  exact ⟨C, (hSP.trans interior_subset).trans hPK⟩

theorem exists_smooth_jordan_exhaustion
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) :
    ∃ C : ℕ → SmoothJordanCore G,
      (∀ n, (C n).carrier ⊆ interior (C (n + 1)).carrier) ∧
      (⋃ n, interior (C n).carrier) = G := by
  classical
  obtain ⟨R, D, K, _, _, _, _, _, hK, hDK, hcover, _, _⟩ :=
    exists_sphere_connected_core_exhaustion hG hconn hinf
  have hex (S : Set Sphere) (hS : IsCompact S) (hSG : S ⊆ G) :=
    exists_smooth_jordan_core_containing hsard hschoenflies hG hconn hinf hS hSG
  let initial : SmoothJordanCore G := Classical.choose (hex (K 0) (hK 0).1 (hK 0).2)
  have hinitial : K 0 ⊆ interior initial.carrier :=
    Classical.choose_spec (hex (K 0) (hK 0).1 (hK 0).2)
  let next (n : ℕ) (C : SmoothJordanCore G) : SmoothJordanCore G :=
    Classical.choose (hex (C.carrier ∪ K (n + 1))
      (C.isCompact.union (hK (n + 1)).1) (union_subset C.subset (hK (n + 1)).2))
  have hnext (n : ℕ) (C : SmoothJordanCore G) :
      C.carrier ∪ K (n + 1) ⊆ interior (next n C).carrier :=
    Classical.choose_spec (hex (C.carrier ∪ K (n + 1))
      (C.isCompact.union (hK (n + 1)).1) (union_subset C.subset (hK (n + 1)).2))
  let C : ℕ → SmoothJordanCore G := fun n => Nat.rec initial next n
  have hstep (n : ℕ) : C (n + 1) = next n (C n) := rfl
  have hretain (n : ℕ) : K n ⊆ interior (C n).carrier := by
    cases n with
    | zero => exact hinitial
    | succ n => exact subset_union_right.trans (hnext n (C n))
  refine ⟨C, fun n => subset_union_left.trans (hnext n (C n)), ?_⟩
  apply Subset.antisymm
  · exact iUnion_subset fun n => interior_subset.trans (C n).subset
  · intro p hp
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover.symm ▸ hp)
    exact mem_iUnion.mpr ⟨n, hretain n (interior_subset (hDK n hn))⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ImageCoreBoundary
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Images of compact retained cores

A conformal injection on an open neighborhood carries a compact core's
interior and boundary to the interior and boundary of its image. Regular
closed cores remain regular closed. These facts use local openness, not a
boundary extension of the conformal map.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem frontier_image_of_continuous_open
    {f : Sphere → Sphere} {G K : Set Sphere}
    (hc : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S))
    (hG : IsOpen G) (hi : InjOn f G) (hK : IsCompact K) (hKG : K ⊆ G) :
    frontier (f '' K) = f '' frontier K := by
  have hfc : IsClosed (f '' K) := (hK.image_of_continuousOn (hc.mono hKG)).isClosed
  rw [frontier, hfc.closure_eq, interior_image_of_continuous_open hc ho hG hi hKG,
    frontier, hK.isClosed.closure_eq]
  exact ((hi.mono hKG).image_sdiff_subset interior_subset).symm

theorem closure_image_interior_of_continuous
    {f : Sphere → Sphere} {G K : Set Sphere}
    (hf : ContinuousOn f G) (hK : IsCompact K) (hKG : K ⊆ G)
    (hregular : closure (interior K) = K) :
    closure (f '' interior K) = f '' K := by
  have hc : ContinuousOn f K := hf.mono hKG
  apply Subset.antisymm
  · exact closure_minimal (image_mono interior_subset) (hK.image_of_continuousOn hc).isClosed
  · have hci : ContinuousOn f (closure (interior K)) := hregular.symm ▸ hc
    simpa only [hregular] using hci.image_closure

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanCoreRecognition
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Recognizing the exterior bounded by a finite Jordan family

A regular closed sphere set with connected interior containing infinity
and with finitely many disjoint Jordan boundary curves is exactly their
common closed exterior. The filled disks are disjoint. This supplies the
image-side identification of retained cores without assuming orientation
or a boundary extension theorem.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem unbounded_preconnected_subset_jordan_exterior
    {T : Set ℂ} (hT : IsPreconnected T) (hunbounded : ¬ Bornology.IsBounded T)
    (H : ℂ ≃ₜ ℂ) (havoid : Disjoint T (frontier (jordanInterior H))) :
    T ⊆ (closure (jordanInterior H))ᶜ := by
  have hsplit : T ⊆ jordanInterior H ∨ T ⊆ (closure (jordanInterior H))ᶜ := by
    apply hT.subset_or_subset (jordanInterior_isOpen H) isClosed_closure.isOpen_compl
    · exact Set.disjoint_left.mpr fun _ hx hy => hy (subset_closure hx)
    · intro z hz
      by_cases hi : z ∈ jordanInterior H
      · exact Or.inl hi
      · right
        intro hc
        exact Set.disjoint_left.mp havoid hz (by
          rw [(jordanInterior_isOpen H).frontier_eq]
          exact ⟨hc, hi⟩)
  rcases hsplit with h | h
  · exact (hunbounded ((isCompact_closure_jordanInterior H).isBounded.subset
      (h.trans subset_closure))).elim
  · exact h

theorem sphere_jordan_core_recognition
    {I : Type*} [Finite I] {A : Set Sphere}
    (hregular : closure (interior A) = A)
    (hconn : IsPreconnected (interior A)) (hinf : OnePoint.infty ∈ interior A)
    (H : I → ℂ ≃ₜ ℂ)
    (hpair : Pairwise (fun i j => Disjoint (frontier (jordanInterior (H i)))
      (frontier (jordanInterior (H j)))))
    (hfront : frontier A = ⋃ i, ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i))) :
    Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) ∧
      Aᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (H i) := by
  have hAclosed : IsClosed A := hregular ▸ isClosed_closure
  let T : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' interior A
  have hT := finite_part_connected_unbounded hconn (by
    simpa only [interior_interior] using hinf)
  have hfrontA (i : I) : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i)) ⊆ frontier A := by
    rw [hfront]
    exact subset_iUnion (fun j : I => ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H j))) i
  have hTout (i : I) : T ⊆ (closure (jordanInterior (H i)))ᶜ := by
    apply unbounded_preconnected_subset_jordan_exterior hT.1 hT.2 (H i)
    apply Set.disjoint_left.mpr
    intro z hz hzfront
    have hzf := hfrontA i (mem_image_of_mem _ hzfront)
    exact hzf.2 hz
  have hAout (i : I) : A ⊆ (((↑) : ℂ → Sphere) '' jordanInterior (H i))ᶜ := by
    rw [← hregular]
    apply closure_minimal ?_ (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen (H i))).isClosed_compl
    intro p hp hinside
    obtain ⟨z, hz, rfl⟩ := hinside
    exact hTout i hp (subset_closure hz)
  have hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) := by
    intro i j hij
    rcases disjoint_or_nested_jordanInteriors (H i) (H j) (hpair hij) with hd | hn | hn
    · exact hd
    · obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior (H i)).nonempty
      have hzA : (z : Sphere) ∈ A := by
        simpa only [hAclosed.closure_eq] using frontier_subset_closure
          (hfrontA i (mem_image_of_mem _ hz))
      exact (hAout j hzA (mem_image_of_mem _ (hn (frontier_subset_closure hz)))).elim
    · obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior (H j)).nonempty
      have hzA : (z : Sphere) ∈ A := by
        simpa only [hAclosed.closure_eq] using frontier_subset_closure
          (hfrontA j (mem_image_of_mem _ hz))
      exact (hAout i hzA (mem_image_of_mem _ (hn (frontier_subset_closure hz)))).elim
  let U : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' Aᶜ
  have hUo : IsOpen U := hAclosed.isOpen_compl.preimage OnePoint.continuous_coe
  have hUb : Bornology.IsBounded U := by
    have hc := ((OnePoint.isOpen_iff_of_mem hinf).mp isOpen_interior).2
    apply hc.isBounded.subset
    intro z hz hzint
    exact hz (interior_subset hzint)
  have hprefront : frontier U = ((↑) : ℂ → Sphere) ⁻¹' frontier A := by
    change frontier (((↑) : ℂ → Sphere) ⁻¹' Aᶜ) = _
    rw [← OnePoint.isOpenEmbedding_coe.isOpenMap.preimage_frontier_eq_frontier_preimage
      OnePoint.continuous_coe, frontier_compl]
  have hcover : frontier U ⊆ ⋃ i, closure (jordanInterior (H i)) := by
    intro z hz
    rw [hprefront] at hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hfront ▸ hz)
    have hzi : z ∈ frontier (jordanInterior (H i)) := OnePoint.coe_injective.mem_set_image.mp hi
    exact mem_iUnion.mpr ⟨i, frontier_subset_closure hzi⟩
  have hselected (i : I) : frontier (jordanInterior (H i)) ⊆ frontier U := by
    intro z hz
    rw [hprefront]
    exact hfrontA i (mem_image_of_mem _ hz)
  have hUfill := open_subset_finite_jordanInteriors_of_frontier_subset H hd hUo hUb hcover hselected
  refine ⟨hd, Subset.antisymm ?_ ?_⟩
  · intro p hp
    cases p using OnePoint.rec with
    | infty => exact (hp (interior_subset hinf)).elim
    | coe z =>
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hUfill hp)
      exact mem_iUnion.mpr ⟨i, z, hi, rfl⟩
  · intro p hp hpA
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact hAout i hpA hi

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ImageCoreJordan
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual Jordan disks bounded by an image core

Schoenflies is applied only to the images of the given boundary circles.
The image-core theorem then proves that their filled sides are pairwise
disjoint and exhaust the complement of the image core.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_jordan_image_core_of_continuous_open
    (hschoenflies : PlanarSchoenflies)
    {f : Sphere → Sphere} {G K : Set Sphere}
    (hG : IsOpen G) (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hK : IsCompact K) (hKG : K ⊆ G)
    (hregular : closure (interior K) = K)
    (hconn : IsPreconnected (interior K)) (hinf : OnePoint.infty ∈ interior K)
    (hfix : f OnePoint.infty = OnePoint.infty)
    {I : Type*} [Finite I] (γ : I → Circle → ℂ)
    (hγ : ∀ i, Continuous (γ i)) (hγinj : ∀ i, Injective (γ i))
    (hγpair : Pairwise (fun i j => Disjoint (range (γ i)) (range (γ j))))
    (hfront : frontier K = ⋃ i, ((↑) : ℂ → Sphere) '' range (γ i)) :
    ∃ H : I → ℂ ≃ₜ ℂ,
      (∀ i, frontier (jordanInterior (H i)) =
        range (fun t => finiteCoord (f ((γ i t : ℂ) : Sphere)))) ∧
      Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) ∧
      (f '' K)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (H i) := by
  have hγK (i : I) (t : Circle) : ((γ i t : ℂ) : Sphere) ∈ K := by
    apply hK.isClosed.closure_eq ▸ frontier_subset_closure
    rw [hfront]
    exact mem_iUnion.mpr ⟨i, γ i t, ⟨t, rfl⟩, rfl⟩
  have hinfG : OnePoint.infty ∈ G := hKG (interior_subset hinf)
  have hfinite (i : I) (t : Circle) : f ((γ i t : ℂ) : Sphere) ≠ OnePoint.infty :=
    finite_image_of_fixes_infty hi hinfG hfix (hKG (hγK i t))
  let δ : I → Circle → ℂ := fun i t => finiteCoord (f ((γ i t : ℂ) : Sphere))
  have hcoords (i : I) (t : Circle) : (δ i t : Sphere) = f ((γ i t : ℂ) : Sphere) :=
    CannonMobius.coe_coordinate (hfinite i t)
  have hδ (i : I) : Continuous (δ i) := by
    apply OnePoint.isOpenEmbedding_coe.isInducing.continuous_iff.mpr
    have he : ((↑) : ℂ → Sphere) ∘ δ i = f ∘ ((↑) : ℂ → Sphere) ∘ γ i :=
      funext (hcoords i)
    rw [he]
    exact hf.comp_continuous (OnePoint.continuous_coe.comp (hγ i))
      (fun t => hKG (hγK i t))
  have hδinj (i : I) : Injective (δ i) := by
    intro x y hxy
    apply hγinj i
    apply OnePoint.coe_injective
    apply hi (hKG (hγK i x)) (hKG (hγK i y))
    exact (hcoords i x).symm.trans ((congrArg ((↑) : ℂ → Sphere) hxy).trans (hcoords i y))
  choose H hH using fun i => hschoenflies (δ i) (hδ i) (hδinj i)
  have hHfront (i : I) : frontier (jordanInterior (H i)) = range (δ i) :=
    frontier_jordanInterior_eq_circle_range (H i) (δ i) (hH i)
  have hHp : Pairwise (fun i j => Disjoint (frontier (jordanInterior (H i)))
      (frontier (jordanInterior (H j)))) := by
    intro i j hij
    rw [hHfront i, hHfront j]
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx⟩ ⟨y, hy⟩
    have he : ((γ i x : ℂ) : Sphere) = ((γ j y : ℂ) : Sphere) := by
      apply hi (hKG (hγK i x)) (hKG (hγK j y))
      exact (hcoords i x).symm.trans
        ((congrArg ((↑) : ℂ → Sphere) (hx.trans hy.symm)).trans (hcoords j y))
    exact Set.disjoint_left.mp (hγpair hij) ⟨x, rfl⟩ ⟨y, OnePoint.coe_injective he.symm⟩
  have himages (i : I) : f '' (((↑) : ℂ → Sphere) '' range (γ i)) =
      ((↑) : ℂ → Sphere) '' range (δ i) := by
    ext p
    constructor
    · rintro ⟨_, ⟨_, ⟨t, rfl⟩, rfl⟩, rfl⟩
      exact ⟨δ i t, ⟨t, rfl⟩, hcoords i t⟩
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨((γ i t : ℂ) : Sphere), ⟨γ i t, ⟨t, rfl⟩, rfl⟩, (hcoords i t).symm⟩
  have htargetfront : frontier (f '' K) =
      ⋃ i, ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i)) := by
    rw [frontier_image_of_continuous_open hf ho hG hi hK hKG, hfront, image_iUnion]
    congr 1
    funext i
    rw [hHfront i]
    exact himages i
  have htargetint := interior_image_of_continuous_open hf ho hG hi hKG
  have htargetregular : closure (interior (f '' K)) = f '' K := by
    rw [htargetint]
    exact closure_image_interior_of_continuous hf hK hKG hregular
  have htargetconn : IsPreconnected (interior (f '' K)) := by
    rw [htargetint]
    exact hconn.image f (hf.mono (interior_subset.trans hKG))
  have htargetinf : OnePoint.infty ∈ interior (f '' K) := by
    rw [htargetint]
    exact ⟨OnePoint.infty, hinf, hfix⟩
  obtain ⟨hd, he⟩ := sphere_jordan_core_recognition htargetregular htargetconn htargetinf H hHp htargetfront
  exact ⟨H, hHfront, hd, he⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanIntersectionConnectivity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Connectivity on the inside of a retained Jordan boundary

A radial clamp onto a slightly smaller disk fixes any prescribed pair of
interior points and maps the whole domain into its intersection with the
disk. The inner circle stays in the domain by compactness of the retained
boundary. This proves the connectedness needed to track source and image
sides under refinement.
-/

open Set Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem continuous_radialClamp {r : ℝ} (hr : 0 < r) : Continuous (radialClamp r) := by
  apply (continuous_const.div (continuous_const.max continuous_norm) ?_).smul continuous_id
  intro z
  exact ne_of_gt (lt_of_lt_of_le hr (le_max_left _ _))

theorem radialClamp_eq_self {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ ≤ r) :
    radialClamp r z = z := by
  simp only [radialClamp, max_eq_left hz, div_self hr.ne', one_smul]

theorem norm_radialClamp_of_le {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : r ≤ ‖z‖) :
    ‖radialClamp r z‖ = r := by
  have hn : ‖z‖ ≠ 0 := ne_of_gt (hr.trans_le hz)
  rw [radialClamp, max_eq_right hz, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hr.le (norm_nonneg z)), div_mul_cancel₀ _ hn]

theorem inner_circle_subset_of_retained_boundary
    {W : Set ℂ} (hW : IsOpen W) (hboundary : sphere (0 : ℂ) 1 ⊆ W) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < 1 → 1 - r < δ → sphere (0 : ℂ) r ⊆ W := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_sphere (0 : ℂ) 1).exists_cthickening_subset_open hW hboundary
  refine ⟨δ, hδ, ?_⟩
  intro r hr hr1 hnear z hz
  have hzn : ‖z‖ = r := mem_sphere_zero_iff_norm.mp hz
  let w : ℂ := r⁻¹ • z
  have hwn : ‖w‖ = 1 := by
    simp only [w, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, hzn,
      inv_mul_cancel₀ hr.ne']
  have hzw : z = r • w := by simp only [w, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  apply hsub
  apply mem_cthickening_of_dist_le z w δ (sphere (0 : ℂ) 1)
    (mem_sphere_zero_iff_norm.mpr hwn)
  calc
    dist z w = ‖(r - 1) • w‖ := by rw [hzw, dist_eq_norm, sub_smul, one_smul]
    _ = 1 - r := by rw [norm_smul, Real.norm_eq_abs, hwn, mul_one, abs_of_neg (sub_neg.mpr hr1)]; ring
    _ ≤ δ := hnear.le

theorem isPreconnected_inter_unitDisk
    {W : Set ℂ} (hW : IsOpen W) (hconn : IsPreconnected W)
    (hboundary : sphere (0 : ℂ) 1 ⊆ W) :
    IsPreconnected (W ∩ ball 0 1) := by
  obtain ⟨δ, hδ, hcircle⟩ := inner_circle_subset_of_retained_boundary hW hboundary
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  have hxn : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx.2
  have hyn : ‖y‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hy.2
  have hmax : max (max ‖x‖ ‖y‖) (1 - δ) < 1 :=
    max_lt (max_lt hxn hyn) (by linarith)
  obtain ⟨r, hrlo, hrhi⟩ := exists_between hmax
  have hxr : ‖x‖ < r := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hrlo)
  have hyr : ‖y‖ < r := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hrlo)
  have hr : 0 < r := (norm_nonneg x).trans_lt hxr
  have hnear : 1 - r < δ := by linarith [le_max_right (max ‖x‖ ‖y‖) (1 - δ)]
  have hmap : radialClamp r '' W ⊆ W ∩ ball 0 1 := by
    rintro _ ⟨z, hz, rfl⟩
    by_cases hzr : ‖z‖ ≤ r
    · rw [radialClamp_eq_self hr hzr]
      exact ⟨hz, by simpa only [mem_ball, dist_zero_right] using hzr.trans_lt hrhi⟩
    · have he := norm_radialClamp_of_le hr (le_of_lt (lt_of_not_ge hzr))
      exact ⟨hcircle r hr hrhi hnear (mem_sphere_zero_iff_norm.mpr he), by
        simpa only [mem_ball, dist_zero_right, he] using hrhi⟩
  refine ⟨radialClamp r '' W, hmap, ?_, ?_, hconn.image _ (continuous_radialClamp hr).continuousOn⟩
  · exact ⟨x, hx.1, radialClamp_eq_self hr hxr.le⟩
  · exact ⟨y, hy.1, radialClamp_eq_self hr hyr.le⟩

theorem isPreconnected_inter_jordanInterior
    {W : Set ℂ} (hW : IsOpen W) (hconn : IsPreconnected W)
    (H : ℂ ≃ₜ ℂ) (hboundary : frontier (jordanInterior H) ⊆ W) :
    IsPreconnected (W ∩ jordanInterior H) := by
  have hpre : IsPreconnected (H ⁻¹' W) := H.isPreconnected_preimage.mpr hconn
  have hbd : sphere (0 : ℂ) 1 ⊆ H ⁻¹' W := by
    intro z hz
    apply hboundary
    rw [frontier_jordanInterior]
    exact mem_image_of_mem _ hz
  have hi := isPreconnected_inter_unitDisk (hW.preimage H.continuous) hpre hbd
  have he : H '' ((H ⁻¹' W) ∩ ball 0 1) = W ∩ jordanInterior H := by
    rw [image_preimage_inter]
    rfl
  exact he ▸ hi.image H H.continuous.continuousOn

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanSideCorrespondence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Correspondence of the source and image sides of a core boundary

Connectivity of the source on a disk's inside, together with local openness
at its retained boundary, determines which target Jordan disk it maps into.
This tracks the labels of boundary curves without extending the conformal
map across any omitted component.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem isPreconnected_sphere_jordan_intersection
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsPreconnected G)
    (hinf : OnePoint.infty ∈ G) (H : ℂ ≃ₜ ℂ)
    (hboundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G) :
    IsPreconnected (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) := by
  let W : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' G
  have hW : IsPreconnected W := (finite_part_connected_unbounded hconn
    (mem_interior_iff_mem_nhds.mpr (hG.mem_nhds hinf))).1
  have hi := isPreconnected_inter_jordanInterior (hG.preimage OnePoint.continuous_coe) hW H
    (fun z hz => hboundary (mem_image_of_mem _ hz))
  have he : ((↑) : ℂ → Sphere) '' (W ∩ jordanInterior H) =
      G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H) := image_preimage_inter _ _ _
  exact he ▸ hi.image _ OnePoint.continuous_coe.continuousOn

theorem open_image_jordan_side_subset
    {I : Type*} [Finite I] (H J : I → ℂ ≃ₜ ℂ)
    (hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))))
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hKG : closedJordanCore H ⊆ G)
    {f : Sphere → Sphere} (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hboundary : ∀ i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i)))
    (himage : (f '' closedJordanCore H)ᶜ =
      ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J i)) (i : I) :
    f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (H i))) ⊆
      ((↑) : ℂ → Sphere) '' jordanInterior (J i) := by
  classical
  let S : Set Sphere := G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (H i))
  let O : Set Sphere := ((↑) : ℂ → Sphere) '' jordanInterior (J i)
  have hOo : IsOpen O := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen (J i))
  have hKclosed : IsClosed (closedJordanCore H) :=
    (isOpen_iUnion fun j => OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen (H j))).isClosed_compl
  have hsrcboundary (j : I) : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H j)) ⊆ G := by
    intro q hq
    apply hKG
    have hfq : q ∈ frontier (closedJordanCore H) := by
      rw [frontier_closedJordanCore H hd]
      exact mem_iUnion.mpr ⟨j, hq⟩
    simpa only [hKclosed.closure_eq] using frontier_subset_closure hfq
  have hS : IsPreconnected S :=
    isPreconnected_sphere_jordan_intersection hG hconn.isPreconnected hinf (H i) (hsrcboundary i)
  have hfrontO : frontier O = ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i)) :=
    frontier_sphere_image_jordanInterior (J i)
  have havoid : Disjoint (f '' S) (frontier O) := by
    apply Set.disjoint_left.mpr
    rintro q ⟨x, hx, rfl⟩ hq
    rw [hfrontO, ← hboundary i] at hq
    obtain ⟨y, hy, he⟩ := hq
    have hyx : y = x := hi (hsrcboundary i hy) hx.1 he
    rw [hyx] at hy
    obtain ⟨z, hz, hez⟩ := hy
    obtain ⟨w, hw, hew⟩ := hx.2
    have hwz : w = z := OnePoint.coe_injective (hew.trans hez.symm)
    exact hz.2 ((jordanInterior_isOpen (H i)).interior_eq.symm ▸ (hwz ▸ hw))
  obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior (H i)).nonempty
  let x : Sphere := (z : Sphere)
  have hxfront : x ∈ ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i)) := ⟨z, hz, rfl⟩
  let B : Set Sphere := ⋃ j : {j : I // j ≠ i}, closedTerminalCap (H j)
  have hBclosed : IsClosed B := isClosed_iUnion_of_finite fun j =>
    (isCompact_closedTerminalCap (H j)).isClosed
  have hxB : x ∉ B := by
    intro h
    obtain ⟨j, w, hw, he⟩ := mem_iUnion.mp h
    have hwz : w = z := OnePoint.coe_injective he
    exact Set.disjoint_left.mp (hd j.property.symm) (frontier_subset_closure hz) (hwz ▸ hw)
  let N : Set Sphere := G ∩ Bᶜ
  have hN : IsOpen N := hG.inter hBclosed.isOpen_compl
  have hxN : x ∈ N := ⟨hsrcboundary i hxfront, hxB⟩
  have hfN : IsOpen (f '' N) := ho _ hN inter_subset_left
  have hfxfront : f x ∈ frontier O := by
    rw [hfrontO, ← hboundary i]
    exact mem_image_of_mem _ hxfront
  obtain ⟨y, hyN, hyO⟩ := mem_closure_iff_nhds.mp (frontier_subset_closure hfxfront)
    (f '' N) (hfN.mem_nhds (mem_image_of_mem _ hxN))
  obtain ⟨w, hwN, rfl⟩ := hyN
  have hwK : w ∉ closedJordanCore H := by
    intro hw
    have htarget : f w ∈ (f '' closedJordanCore H)ᶜ := by
      rw [himage]
      exact mem_iUnion.mpr ⟨i, hyO⟩
    exact htarget (mem_image_of_mem _ hw)
  have hwS : w ∈ S := by
    refine ⟨hwN.1, ?_⟩
    have hwU : w ∈ ⋃ j, ((↑) : ℂ → Sphere) '' jordanInterior (H j) := not_not.mp hwK
    obtain ⟨j, v, hv, he⟩ := mem_iUnion.mp hwU
    by_cases hji : j = i
    · exact hji ▸ ⟨v, hv, he⟩
    · exact (hwN.2 (mem_iUnion.mpr ⟨⟨j, hji⟩, v, subset_closure hv, he⟩)).elim
  have hmeet : (f '' S ∩ O).Nonempty := ⟨f w, mem_image_of_mem _ hwS, hyO⟩
  have hcover : f '' S ⊆ O ∪ (closure O)ᶜ := by
    intro q hq
    by_cases hqo : q ∈ O
    · exact Or.inl hqo
    · right
      intro hqc
      exact Set.disjoint_left.mp havoid hq ⟨hqc, by
        simpa only [hOo.interior_eq] using hqo⟩
  exact (hS.image f (hf.mono inter_subset_left)).subset_left_of_subset_union
    hOo isClosed_closure.isOpen_compl
    (Set.disjoint_left.mpr fun _ h₁ h₂ => h₂ (subset_closure h₁)) hcover hmeet


theorem open_image_jordan_side_eq
    {I : Type*} [Finite I] (H J : I → ℂ ≃ₜ ℂ)
    (hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))))
    (hJd : Pairwise (Disjoint on fun i => closure (jordanInterior (J i))))
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hKG : closedJordanCore H ⊆ G)
    {f : Sphere → Sphere} (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hboundary : ∀ i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i)))
    (himage : (f '' closedJordanCore H)ᶜ =
      ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J i)) (i : I) :
    f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (H i))) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J i)) := by
  have hsides := open_image_jordan_side_subset H J hd hG hconn hinf hKG hf ho hi hboundary himage
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨mem_image_of_mem _ hx.1, hsides i (mem_image_of_mem _ hx)⟩
  · rintro y ⟨⟨x, hx, rfl⟩, hy⟩
    have hnotK : x ∉ closedJordanCore H := by
      intro hxK
      have hnot : f x ∈ (f '' closedJordanCore H)ᶜ := by
        rw [himage]
        exact mem_iUnion.mpr ⟨i, hy⟩
      exact hnot (mem_image_of_mem _ hxK)
    obtain ⟨j, hj⟩ := mem_iUnion.mp (not_not.mp hnotK)
    have hj' := hsides j (mem_image_of_mem f ⟨hx, hj⟩)
    have hji : j = i := by
      by_contra hne
      exact Set.disjoint_left.mp (disjoint_closedTerminalCaps J hJd hne)
        (by obtain ⟨z, hz, he⟩ := hj'; exact ⟨z, subset_closure hz, he⟩)
        (by obtain ⟨z, hz, he⟩ := hy; exact ⟨z, subset_closure hz, he⟩)
    exact ⟨x, ⟨hx, hji ▸ hj⟩, rfl⟩


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedImageCores
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matched source and target Jordan cores

The actual mapped boundary parametrizations identify each target disk's
label. Both inclusions of the corresponding source/target side equality
are proved, so refinement can carry those labels to end components.
-/

open Set Function
open scoped Topology Manifold ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem exists_matched_image_core_of_continuous_open
    (hschoenflies : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G)
    {f : Sphere → Sphere} (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hfix : f OnePoint.infty = OnePoint.infty) (C : SmoothJordanCore G) :
    ∃ J : Fin C.count → ℂ ≃ₜ ℂ,
      Pairwise (Disjoint on fun i => closure (jordanInterior (J i))) ∧
      (f '' C.carrier)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J i) ∧
      (∀ i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (C.disk i))) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i))) ∧
      ∀ i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (C.disk i))) =
        f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J i)) := by
  have hsrcfront : frontier C.carrier = ⋃ i, ((↑) : ℂ → Sphere) '' range (C.curve i) := by
    rw [SmoothJordanCore.carrier, frontier_closedJordanCore C.disk C.disjoint]
    simp only [C.boundary]
  have hcurvesG (i : Fin C.count) (t : Circle) : ((C.curve i t : ℂ) : Sphere) ∈ G := by
    apply C.subset
    have hfront : ((C.curve i t : ℂ) : Sphere) ∈ frontier C.carrier := by
      rw [hsrcfront]
      exact mem_iUnion.mpr ⟨i, C.curve i t, ⟨t, rfl⟩, rfl⟩
    simpa only [C.isCompact.isClosed.closure_eq] using frontier_subset_closure hfront
  obtain ⟨J, hJfront, hJd, hJe⟩ := exists_jordan_image_core_of_continuous_open hschoenflies hG hf ho hi
    C.isCompact C.subset C.regular C.connected_interior.isPreconnected C.infty_interior hfix
    C.curve (fun i => (C.embedding i).continuous) (fun i => (C.embedding i).injective)
    (by
      intro i j hij
      apply (C.disjoint hij).mono
      · rw [← C.boundary i]
        exact frontier_subset_closure
      · rw [← C.boundary j]
        exact frontier_subset_closure) hsrcfront
  have hboundary (i : Fin C.count) :
      f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (C.disk i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i)) := by
    rw [C.boundary i, hJfront i, image_image, ← range_comp, ← range_comp]
    congr 1
    funext t
    exact (CannonMobius.coe_coordinate
      (finite_image_of_fixes_infty hi hinf hfix (hcurvesG i t))).symm
  refine ⟨J, hJd, hJe, hboundary, ?_⟩
  exact open_image_jordan_side_eq C.disk J C.disjoint hJd hG hconn hinf C.subset
    hf ho hi hboundary hJe


theorem exists_matched_jordan_exhaustion_of_continuous_open
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G)
    {f : Sphere → Sphere} (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hfix : f OnePoint.infty = OnePoint.infty) :
    ∃ (C : ℕ → SmoothJordanCore G) (J : (n : ℕ) → Fin (C n).count → ℂ ≃ₜ ℂ),
      (∀ n, (C n).carrier ⊆ interior (C (n + 1)).carrier) ∧
      (⋃ n, interior (C n).carrier) = G ∧
      (∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (J n i)))) ∧
      (∀ n, (f '' (C n).carrier)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J n i)) ∧
      (∀ n i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i))) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J n i))) ∧
      ∀ n i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk i))) =
        f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J n i)) := by
  classical
  obtain ⟨C, hs, hc⟩ := exists_smooth_jordan_exhaustion hsard hschoenflies hG hconn hinf
  choose J hd he hb hi' using fun n => exists_matched_image_core_of_continuous_open hschoenflies hG hconn hinf hf ho hi hfix (C n)
  exact ⟨C, J, hs, hc, hd, he, hb, hi'⟩

theorem exists_matched_jordan_exhaustion
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G)
    {f : Sphere → Sphere} (hf : IsConformalOn f G) (hi : InjOn f G)
    (hfix : f OnePoint.infty = OnePoint.infty) :
    ∃ (C : ℕ → SmoothJordanCore G) (J : (n : ℕ) → Fin (C n).count → ℂ ≃ₜ ℂ),
      (∀ n, (C n).carrier ⊆ interior (C (n + 1)).carrier) ∧
      (⋃ n, interior (C n).carrier) = G ∧
      (∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (J n i)))) ∧
      (∀ n, (f '' (C n).carrier)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J n i)) ∧
      (∀ n i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i))) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J n i))) ∧
      ∀ n i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk i))) =
        f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J n i)) :=
  exists_matched_jordan_exhaustion_of_continuous_open hsard hschoenflies hG hconn hinf
    (fun p hp => (hf p hp).1.continuousWithinAt)
    (fun _ hS hSG => hf.isOpen_image hG hS hSG) hi hfix


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PrincipalExteriorGerm
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A holomorphic exterior map tending to the identity has an actual
principal Laurent germ. The first two divided differences give the
coefficient and the analytic remainder; no Laurent estimate is assumed. -/
open Set Filter Function Asymptotics Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem invertedPrincipalRemainder_analytic {F : ℂ → ℂ}
    (hF : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ F z)
    (ht : Tendsto (fun z => F z - z) (cobounded ℂ) (𝓝 0)) :
    AnalyticAt ℂ (invertedPrincipalRemainder F) 0 := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · have hd := (tendsto_inv₀_nhdsNE_zero (α := ℂ)).eventually hF
    filter_upwards [hd, self_mem_nhdsWithin] with w hw hw0
    have hn : w ≠ 0 := hw0
    have hi : DifferentiableAt ℂ (fun z : ℂ => z⁻¹) w := differentiableAt_inv hn
    have hh := (hw.comp w hi).sub hi
    apply hh.congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hn] with z hz
    exact Function.update_of_ne hz _ _
  · exact continuousAt_update_same.mpr
      (ht.comp (tendsto_inv₀_nhdsNE_zero (α := ℂ)))

 theorem principal_exterior_expansion {F : ℂ → ℂ}
    (hF : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ F z)
    (ht : Tendsto (fun z => F z - z) (cobounded ℂ) (𝓝 0)) :
    ∃ (c : ℂ) (T : ℂ → ℂ), AnalyticAt ℂ T 0 ∧
      ∀ z : ℂ, z ≠ 0 → F z - z = c * z⁻¹ + z⁻¹ ^ 2 * T z⁻¹ := by
  let u := invertedPrincipalRemainder F
  have hu : AnalyticAt ℂ u 0 := invertedPrincipalRemainder_analytic hF ht
  have hu0 : u 0 = 0 := Function.update_self _ _ _
  let v := dslope u 0
  let T := dslope v 0
  have hv : AnalyticAt ℂ v 0 := analyticAt_dslope_zero hu
  refine ⟨v 0, T, analyticAt_dslope_zero hv, ?_⟩
  intro z hz
  have h1 : z⁻¹ * v z⁻¹ = u z⁻¹ := by
    simpa only [sub_zero, smul_eq_mul, hu0] using sub_smul_dslope u 0 z⁻¹
  have h2 : z⁻¹ * T z⁻¹ = v z⁻¹ - v 0 := by
    simpa only [sub_zero, smul_eq_mul] using sub_smul_dslope v 0 z⁻¹
  have he : u z⁻¹ = F z - z := by
    dsimp only [u, invertedPrincipalRemainder]
    rw [Function.update_of_ne (inv_ne_zero hz), inv_inv]
  rw [he] at h1
  linear_combination -h1 - z⁻¹ * h2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RectangleNeighborhoods
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact rectangles form a neighborhood basis inside a planar open
set; countably many of their interiors suffice to patch measurability. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology

namespace CircleDomainRigidity

theorem exists_closed_rectangle_inside_open
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {p : ℝ × ℝ} (hp : p ∈ U) :
    ∃a b c d : ℝ, a < b ∧ c < d ∧ p ∈ Ioo a b ×ˢ Ioo c d ∧
      Icc a b ×ˢ Icc c d ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  refine ⟨p.1 - ε/2, p.1 + ε/2, p.2 - ε/2, p.2 + ε/2,
    by linarith, by linarith, ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, ?_⟩
  intro q hq
  apply hball
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
  constructor <;> apply abs_lt.mpr
  · constructor <;> linarith [hq.1.1, hq.1.2]
  · constructor <;> linarith [hq.2.1, hq.2.2]

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_PrincipalCoefficientLimit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first principal coefficient as a limit. Composition adds the actual
coefficients, and the published area theorem bounds each coefficient on a
fixed exterior disk. -/
open Set Filter Function Asymptotics Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem hasPrincipalCoefficient_of_expansion {F T : ℂ → ℂ} {b : ℂ}
    (hT : ContinuousAt T 0)
    (hexp : ∀ z : ℂ, z ≠ 0 → F z-z = b*z⁻¹+z⁻¹^2*T z⁻¹) :
    HasPrincipalCoefficient F b := by
  have hi := tendsto_inv₀_cobounded (α := ℂ)
  have hlim := (tendsto_const_nhds (x := b)).add (hi.mul (hT.tendsto.comp hi))
  simp only [zero_mul, add_zero] at hlim
  apply hlim.congr'
  have hn : ∀ᶠ z : ℂ in cobounded ℂ, z ≠ 0 := by
    rw [Metric.cobounded_eq_cocompact]
    exact isCompact_singleton.compl_mem_cocompact
  filter_upwards [hn] with z hz
  dsimp only [Function.comp_apply]
  rw [hexp z hz]
  field_simp

 theorem exists_principal_coefficient {F : ℂ → ℂ}
    (hd : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ F z)
    (hn : (fun z => F z-z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ∃ b, HasPrincipalCoefficient F b := by
  obtain ⟨b, T, hT, hexp⟩ := principal_exterior_expansion hd (principal_remainder_tendsto_zero hn)
  exact ⟨b, hasPrincipalCoefficient_of_expansion hT.continuousAt hexp⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactScalarModel
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar models with a globally deformed round complement. This is the
smaller class needed for coefficient extremality: it contains the actual
circle models and is closed under plane homeomorphisms. The deformation
retains every complementary component, rather than just its boundary. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 namespace CompactScalarModel
 variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem normalized (M : CompactScalarModel G u) :
    IsPrincipalNormalized (extendAtInfinity M.function) :=
  isPrincipalNormalized_extendAtInfinity M.coefficient_limit.bigO

 theorem image_open (M : CompactScalarModel G u) :
    IsOpen (extendAtInfinity M.function '' G) := by
  rw [M.image_eq]
  exact M.deformation.onePointCongr.isOpenMap _ M.round_circle.1

 end CompactScalarModel

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CutoffEnergyAlgebra
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary two-coordinate product estimate for a compact cutoff. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity

 theorem plane_norm_sq (v : EuclideanPlane) : ‖v‖^2 = v 0^2+v 1^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ComplexWeakGradient
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.horizontalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complex chart preserves covector norms, including differences,
and identifies the gradients used by the physical Sobolev witnesses. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem complex_plane_covector_norm (L : ℂ →L[ℝ] ℝ) :
    ‖planeCovectorGradient (L.comp complexPlaneCoordinates.toContinuousLinearMap)‖ = ‖L‖ := by
  have he : ‖planeCovectorGradient (L.comp complexPlaneCoordinates.toContinuousLinearMap)‖^2 = ‖L‖^2 := by
    rw [plane_norm_sq, complexCovector_norm_sq]
    simp only [planeCovectorGradient, planePair_zero, planePair_one,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      complexPlaneCoordinates_zero, complexPlaneCoordinates_one]
  nlinarith [norm_nonneg (planeCovectorGradient (L.comp complexPlaneCoordinates.toContinuousLinearMap)),
    norm_nonneg L]

 theorem complexLocalScalarWitness_gradient
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f D) (hL : MemLp f 2 (volume.restrict D))
    (hE : MemLp (fderiv ℝ f) 2 (volume.restrict D)) (x : EuclideanPlane) :
    (complexLocalScalarWitness hD hf hL hE).weakGrad x =
      planeCovectorGradient (fderiv ℝ (f ∘ complexPlaneCoordinates) x) := by
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  funext i
  fin_cases i <;> simp [complexLocalScalarWitness, planeCovectorGradient]

 theorem complex_weak_gradient_ae
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f D) (hE : MemLp (fderiv ℝ f) 2 (volume.restrict D))
    (W : DeGiorgi.MemW1pWitness 2 (f ∘ complexPlaneCoordinates)
      (complexPlaneCoordinates ⁻¹' D)) :
    W.weakGrad =ᵐ[volume.restrict (complexPlaneCoordinates ⁻¹' D)] fun x =>
      planeCovectorGradient ((fderiv ℝ f (complexPlaneCoordinates x)).comp
        complexPlaneCoordinates.toContinuousLinearMap) := by
  have hL : MemLp f 2 (volume.restrict D) := by
    have hmp := complexPlaneCoordinates_measurePreserving.restrict_preimage hD.measurableSet
    have hb := W.memLp.comp_measurePreserving
      (hmp.symm complexPlaneCoordinates.toHomeomorph.toMeasurableEquiv)
    change MemLp (fun z => f (complexPlaneCoordinates (complexPlaneCoordinates.symm z))) 2
      (volume.restrict D) at hb
    simpa only [complexPlaneCoordinates.apply_symm_apply] using hb
  let V := complexLocalScalarWitness hD hf hL hE
  have he := W.ae_eq (hD.preimage complexPlaneCoordinates.continuous) V
  filter_upwards [he, ae_restrict_mem (hD.preimage complexPlaneCoordinates.continuous).measurableSet] with x hx hxD
  rw [hx, complexLocalScalarWitness_gradient]
  congr 1
  rw [fderiv_comp x ((hf.contDiffAt (hD.mem_nhds hxD)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    complexPlaneCoordinates.differentiableAt, complexPlaneCoordinates.fderiv]

 theorem complex_weak_gradient_difference_norm
    {D : Set ℂ} (hD : IsOpen D) {f g : ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f D) (hg : ContDiffOn ℝ ∞ g D)
    (hEf : MemLp (fderiv ℝ f) 2 (volume.restrict D))
    (hEg : MemLp (fderiv ℝ g) 2 (volume.restrict D))
    (Wf : DeGiorgi.MemW1pWitness 2 (f ∘ complexPlaneCoordinates) (complexPlaneCoordinates ⁻¹' D))
    (Wg : DeGiorgi.MemW1pWitness 2 (g ∘ complexPlaneCoordinates) (complexPlaneCoordinates ⁻¹' D)) :
    (fun x => ‖Wf.weakGrad x-Wg.weakGrad x‖) =ᵐ[volume.restrict (complexPlaneCoordinates ⁻¹' D)]
      fun x => ‖fderiv ℝ f (complexPlaneCoordinates x)-fderiv ℝ g (complexPlaneCoordinates x)‖ := by
  filter_upwards [complex_weak_gradient_ae hD hf hEf Wf,
    complex_weak_gradient_ae hD hg hEg Wg] with x hfx hgx
  rw [hfx, hgx, ← planeCovectorGradient_sub, ← ContinuousLinearMap.sub_comp,
    complex_plane_covector_norm]

 theorem complex_weak_gradient_difference_L2
    {D : Set ℂ} (hD : IsOpen D) {f g : ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f D) (hg : ContDiffOn ℝ ∞ g D)
    (hEf : MemLp (fderiv ℝ f) 2 (volume.restrict D))
    (hEg : MemLp (fderiv ℝ g) 2 (volume.restrict D))
    (Wf : DeGiorgi.MemW1pWitness 2 (f ∘ complexPlaneCoordinates) (complexPlaneCoordinates ⁻¹' D))
    (Wg : DeGiorgi.MemW1pWitness 2 (g ∘ complexPlaneCoordinates) (complexPlaneCoordinates ⁻¹' D)) :
    eLpNorm (fun x => Wf.weakGrad x-Wg.weakGrad x) 2
      (volume.restrict (complexPlaneCoordinates ⁻¹' D)) =
    eLpNorm (fun z => fderiv ℝ f z-fderiv ℝ g z) 2 (volume.restrict D) := by
  have hW := Wf.weakGrad_memLp.aestronglyMeasurable.sub Wg.weakGrad_memLp.aestronglyMeasurable
  have hE := hEf.aestronglyMeasurable.sub hEg.aestronglyMeasurable
  calc
    _ = eLpNorm (fun x => ‖Wf.weakGrad x-Wg.weakGrad x‖) 2
        (volume.restrict (complexPlaneCoordinates ⁻¹' D)) := (eLpNorm_norm _).symm
    _ = eLpNorm (fun x => ‖fderiv ℝ f (complexPlaneCoordinates x)-fderiv ℝ g (complexPlaneCoordinates x)‖) 2
        (volume.restrict (complexPlaneCoordinates ⁻¹' D)) :=
      eLpNorm_congr_ae (complex_weak_gradient_difference_norm hD hf hg hEf hEg Wf Wg)
    _ = eLpNorm (fun z => ‖fderiv ℝ f z-fderiv ℝ g z‖) 2 (volume.restrict D) :=
      eLpNorm_comp_measurePreserving hE.norm
        (complexPlaneCoordinates_measurePreserving.restrict_preimage hD.measurableSet)
    _ = _ := eLpNorm_norm _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PriorityWeights
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable priority weights form a subprobability distribution. The
remaining mass belongs to the original horizontal coordinate. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem priorityRemainder_succ (χ : ℕ → ℝ) (n : ℕ) :
    priorityRemainder χ (n+1) = priorityRemainder χ n*(1-χ n) := by
  simp only [priorityRemainder, Finset.prod_range_succ]

 theorem priorityRemainder_mem_unit {χ : ℕ → ℝ} (hχ : ∀ n, χ n ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    priorityRemainder χ n ∈ Icc (0 : ℝ) 1 := by
  induction n with
  | zero => simp [priorityRemainder]
  | succ n ih =>
    rw [priorityRemainder_succ]
    have h0 : 0 ≤ 1-χ n := by linarith [(hχ n).2]
    exact ⟨mul_nonneg ih.1 h0,
      (mul_le_mul ih.2 (by linarith [(hχ n).1] : 1-χ n ≤ 1) h0 zero_le_one).trans_eq (one_mul 1)⟩

 theorem priorityWeight_nonneg {χ : ℕ → ℝ} (hχ : ∀ n, χ n ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    0 ≤ priorityWeight χ n := mul_nonneg (hχ n).1 (priorityRemainder_mem_unit hχ n).1

 theorem priorityWeight_sum (χ : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, priorityWeight χ i = 1-priorityRemainder χ n := by
  induction n with
  | zero => simp [priorityRemainder]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, priorityRemainder_succ]
    dsimp only [priorityWeight]
    ring

 theorem priorityWeight_summable {χ : ℕ → ℝ} (hχ : ∀ n, χ n ∈ Icc (0 : ℝ) 1) :
    Summable (priorityWeight χ) := by
  apply summable_of_sum_range_le (c := 1) (priorityWeight_nonneg hχ)
  intro n
  rw [priorityWeight_sum]
  linarith [(priorityRemainder_mem_unit hχ n).1]

 theorem priorityWeight_tsum_mem_unit {χ : ℕ → ℝ} (hχ : ∀ n, χ n ∈ Icc (0 : ℝ) 1) :
    (∑' n, priorityWeight χ n) ∈ Icc (0 : ℝ) 1 := by
  refine ⟨tsum_nonneg (priorityWeight_nonneg hχ), ?_⟩
  apply Real.tsum_le_of_sum_range_le (priorityWeight_nonneg hχ)
  intro n
  rw [priorityWeight_sum]
  linarith [(priorityRemainder_mem_unit hχ n).1]

 theorem priorityInfiniteValue_norm_le {χ c : ℕ → ℝ} (hχ : ∀ n, χ n ∈ Icc (0 : ℝ) 1)
    {B x : ℝ} (hc : ∀ n, ‖c n‖ ≤ B) (hx : ‖x‖ ≤ B) :
    ‖priorityInfiniteValue χ c x‖ ≤ B := by
  have hw := priorityWeight_tsum_mem_unit hχ
  have hrem : 0 ≤ 1-∑' n, priorityWeight χ n := by linarith [hw.2]
  have hsum : ‖∑' n, priorityWeight χ n*c n‖ ≤ (∑' n, priorityWeight χ n)*B := by
    have h := tsum_of_norm_bounded (f := fun n => priorityWeight χ n*c n)
      ((priorityWeight_summable hχ).mul_right B).hasSum (fun n => by
      rw [norm_mul, Real.norm_eq_abs (priorityWeight χ n), abs_of_nonneg (priorityWeight_nonneg hχ n)]
      exact mul_le_mul_of_nonneg_left (hc n) (priorityWeight_nonneg hχ n))
    simpa only [(priorityWeight_summable hχ).tsum_mul_right] using h
  calc
    ‖priorityInfiniteValue χ c x‖ ≤ ‖(1-∑' n, priorityWeight χ n)*x‖ +
      ‖∑' n, priorityWeight χ n*c n‖ := norm_add_le _ _
    _ ≤ (1-∑' n, priorityWeight χ n)*B+(∑' n, priorityWeight χ n)*B := by
      rw [norm_mul, Real.norm_eq_abs (1-∑' n, priorityWeight χ n), abs_of_nonneg hrem]
      exact add_le_add (mul_le_mul_of_nonneg_left hx hrem) hsum
    _ = B := by ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ConcentratedCutoffs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cutoffs whose centers lie in a closed set and whose radii tend to
zero have a common finite tail vanishing near each point of its complement. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem concentrated_cutoffs_eventually_zero
    {X : Type*} [MetricSpace X] {B : Set X} (hB : IsClosed B)
    (c : ℕ → X) (hc : ∀ n, c n ∈ B) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (χ : ℕ → X → ℝ) (hs : ∀ n, support (χ n) ⊆ ball (c n) (r n))
    {x : X} (hx : x ∉ B) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ y ∈ V, χ n y = 0 := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hB.isOpen_compl.mem_nhds hx)
  have hsmall : ∀ᶠ n in atTop, r n < δ/2 := hr.eventually (gt_mem_nhds (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  refine ⟨ball x (δ/2), isOpen_ball, mem_ball_self (by linarith), N, ?_⟩
  intro n hn y hy
  by_contra hne
  have hyc := hs n hne
  have hcx : dist (c n) x < δ := by
    calc
      dist (c n) x ≤ dist (c n) y+dist y x := dist_triangle _ _ _
      _ < δ/2+δ/2 := add_lt_add (by simpa only [dist_comm] using hyc.trans (hN n hn)) hy
      _ = δ := by ring
  exact (hball hcx) (hc n)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ProjectionJordanCap
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous extension of the inverse carries a matched closed Jordan
cap into its source cap. The boundary identity prevents crossing the source
curve, and a domain point identifies the correct side. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem inverse_projection_matched_cap
    {G : Set Sphere} (hG : IsOpen G) {f P : Sphere → Sphere}
    (hP : Continuous P)
    (hInv : ∀ x ∈ G, P (f x) = x)
    (hOut : ∀ y ∉ f '' G, P y ∈ Gᶜ)
    (H J : ℂ ≃ₜ ℂ)
    (hFront : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G)
    (hBoundary : f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior J))
    (hSide : f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior J)) :
    P '' closedTerminalCap J ⊆ closedTerminalCap H := by
  let U : Set Sphere := ((↑) : ℂ → Sphere) '' jordanInterior H
  let V : Set Sphere := ((↑) : ℂ → Sphere) '' jordanInterior J
  have hU : IsOpen U := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H)
  have hV : IsOpen V := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen J)
  have hUF : frontier U = ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) :=
    frontier_sphere_image_jordanInterior H
  have hVF : frontier V = ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) :=
    frontier_sphere_image_jordanInterior J
  have hAvoid : Disjoint (P '' V) (frontier U) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨y, hy, rfl⟩ hpy
    have hpyG : P y ∈ G := hFront (hUF ▸ hpy)
    have hyf : y = f (P y) :=
      (inverse_projection_fiber_on_domain hInv hOut hpyG).mp rfl
    have hyFront : y ∈ frontier V := by
      rw [hVF, ← hBoundary, hyf]
      exact mem_image_of_mem _ (hUF ▸ hpy)
    exact hyFront.2 (hV.interior_eq.symm ▸ hy)
  have hMeet : (P '' V ∩ U).Nonempty := by
    obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior H).nonempty
    have hzF : (z : Sphere) ∈ frontier U := hUF.symm ▸ ⟨z, hz, rfl⟩
    obtain ⟨x, hxG, hxU⟩ := mem_closure_iff_nhds.mp (frontier_subset_closure hzF)
      G (hG.mem_nhds (hFront ⟨z, hz, rfl⟩))
    have hfx : f x ∈ V := by
      have hh : f x ∈ f '' G ∩ V := hSide ▸ mem_image_of_mem f ⟨hxG, hxU⟩
      exact hh.2
    exact ⟨P (f x), ⟨f x, hfx, rfl⟩, by simpa only [hInv x hxG] using hxU⟩
  have hCover : P '' V ⊆ U ∪ (closure U)ᶜ := by
    intro y hy
    by_cases hyU : y ∈ U
    · exact Or.inl hyU
    · exact Or.inr fun hycl => Set.disjoint_left.mp hAvoid hy
        ⟨hycl, by simpa only [hU.interior_eq] using hyU⟩
  have hconn : IsPreconnected V :=
    (isConnected_jordanInterior J).isPreconnected.image _ OnePoint.continuous_coe.continuousOn
  have hsub : P '' V ⊆ U := (hconn.image P hP.continuousOn).subset_left_of_subset_union
    hU isClosed_closure.isOpen_compl
    (Set.disjoint_left.mpr fun _ h₁ h₂ => h₂ (subset_closure h₁)) hCover hMeet
  have hcl : P '' closure V ⊆ closure U :=
    hP.continuousOn.image_closure.trans (closure_mono hsub)
  simpa only [U, V, closedTerminalCap, closure_sphere_image_jordanInterior] using hcl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelProjectionFibers
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fiber identification for the actual coefficient-extremal scalar model.
Only the already cited geometric inputs construct its matched exhaustion. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem projection_surjective (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ) :
    Surjective M.projection := by
  obtain ⟨C, J, hstrict, hcover, hd, he, hb, hs⟩ := exists_matched_jordan_exhaustion
    hsard hsch hG hconn hinf M.conformal.1 M.conformal.bijOn.injOn rfl
  intro q
  by_cases hq : q ∈ G
  · exact ⟨extendAtInfinity M.function q, M.projection_inverse q hq⟩
  · obtain ⟨b, p, hp, hsource, htarget, _⟩ := corresponding_target_end_of_source hG
      M.conformal.1 M.conformal.bijOn.injOn C J hstrict hcover hd he hb hs hq
    refine ⟨p, ?_⟩
    have hmem : M.projection p ∈ connectedComponentIn Gᶜ q := by
      rw [hsource]
      apply mem_iInter.mpr
      intro n
      have hfront : ((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk (b n))) ⊆ G := by
        intro x hx
        apply (C n).subset
        have hh : x ∈ frontier (C n).carrier := by
          rw [SmoothJordanCore.carrier, frontier_closedJordanCore (C n).disk (C n).disjoint]
          exact mem_iUnion.mpr ⟨b n, hx⟩
        simpa only [(C n).isCompact.isClosed.closure_eq] using frontier_subset_closure hh
      apply inverse_projection_matched_cap hG M.projection_continuous
        M.projection_inverse M.projection_outside ((C n).disk (b n)) (J n (b n))
        hfront (hb n (b n)) (hs n (b n))
      exact mem_image_of_mem _ (mem_iInter.mp (htarget ▸ mem_connectedComponentIn hp) n)
    have hsingle : connectedComponentIn Gᶜ q = {q} :=
      (hTD _ (connectedComponentIn_subset _ _) isPreconnected_connectedComponentIn).eq_singleton_of_mem
        (mem_connectedComponentIn hq)
    simpa only [hsingle, mem_singleton_iff] using hmem

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_TargetArea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Target area from the exterior area theorem

Ahlfors, *Conformal Invariants* (1973), Exterior Area Theorem, supplies the
area bound for the set omitted by a normalized univalent exterior map.
The numerical bound yields the target-area estimate by change of variables
and disjointness of the image and omitted disks.
-/

open MeasureTheory Metric Set Function Bornology
open scoped ENNReal

namespace CircleDomainRigidity

/-- Complex change of variables identifies image area with Dirichlet area
of an injective holomorphic map. -/
theorem integral_norm_deriv_sq_eq_image_area {f : ℂ → ℂ} {U : Set ℂ}
    (hU : MeasurableSet U) (hf : ∀ z ∈ U, DifferentiableAt ℂ f z)
    (hinj : InjOn f U) :
    (∫ z in U, ‖deriv f z‖ ^ 2) = (volume (f '' U)).toReal := by
  let L : ℂ → ℂ →L[ℝ] ℂ := fun z =>
    (ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)).restrictScalars ℝ
  have hL : ∀ z ∈ U, HasFDerivWithinAt f (L z) U z :=
    fun z hz => ((hf z hz).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hdet (z : ℂ) : (L z).det = ‖deriv f z‖ ^ 2 := by
    simp [L, ContinuousLinearMap.det, LinearMap.det_restrictScalars,
      Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq]
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume hU hL hinj
    (fun _ : ℂ => (1 : ℝ))
  simpa [hdet, measureReal_def] using h.symm

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ModelScalarEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual source horizontal section is smooth off the dust and has
finite differential energy on each bounded source region. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem horizontalSection_plane_smooth (M : CompactScalarModel G u) (hG : IsOpen G) :
    ContDiffOn ℝ ∞ (fun z : ℂ => M.horizontalSection (z : Sphere)) {z : ℂ | (z : Sphere) ∈ G} := by
  let D := {z : ℂ | (z : Sphere) ∈ G}
  have hD : IsOpen D := hG.preimage OnePoint.continuous_coe
  have hf : DifferentiableOn ℂ M.function D := fun z hz =>
    (finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz)).differentiableWithinAt
  have hc : ContDiffOn ℝ ∞ M.function D := (hf.contDiffOn hD).restrict_scalars ℝ
  apply (Complex.reCLM.contDiff.comp_contDiffOn hc).congr
  intro z hz
  simpa only [Function.comp_apply, Complex.reCLM_apply, extendAtInfinity_coe, finiteCoord_coe] using
    M.horizontalSection_on_domain hz

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_IndicatorL2Energy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert a small weighted mass of a changed set into the exact L2
error contribution used by source priority interpolation. -/
open Set Function Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem indicator_L2_norm_lt_of_energy_lt
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {g : X → ℝ}
    (hg : MemLp g 2 μ) {S : Set X} (hS : MeasurableSet S)
    {τ : ℝ} (hτ : 0 < τ)
    (hE : (∫⁻ x in S, ENNReal.ofReal (g x^2) ∂μ) < ENNReal.ofReal (τ^2)) :
    (eLpNorm (S.indicator g) 2 μ).toReal < τ := by
  have hi := (hg.restrict S).integrable_sq
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun x => sq_nonneg (g x)))
  rw [← he] at hE
  have hb : (∫ x in S, g x^2 ∂μ) < τ^2 := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hE
  have hp : (fun x => (S.indicator g x)^2) = S.indicator (fun x => g x^2) := by
    funext x
    by_cases hx : x ∈ S
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, zero_pow (by decide : 2 ≠ 0)]
  have hn := integral_sq_eq_eLpNorm_toReal_sq (hg.indicator hS)
  rw [hp, integral_indicator hS] at hn
  rw [hn] at hb
  nlinarith [ENNReal.toReal_nonneg (a := eLpNorm (S.indicator g) 2 μ)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PriorityFinite
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the finite recursive interpolation with the
priority-weight formula, for passage from local finite sums to the
countable interpolation. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

variable {E : Type*}

 theorem priorityBlend_append (L M : List ((E → ℝ) × ℝ)) (X : E → ℝ) :
    priorityBlend (L++M) X = priorityBlend L (priorityBlend M X) := by
  induction L with
  | nil => rfl
  | cons e L ih => simp only [List.cons_append, priorityBlend, ih]

 theorem priorityResidual_append (L M : List ((E → ℝ) × ℝ)) (p : E) :
    priorityResidual (L++M) p = priorityResidual L p*priorityResidual M p := by
  induction L with
  | nil => simp [priorityResidual]
  | cons e L ih => simp only [List.cons_append, priorityResidual, ih] <;> ring

 theorem priorityBlend_sub (L : List ((E → ℝ) × ℝ)) (X Y : E → ℝ) (p : E) :
    priorityBlend L X p-priorityBlend L Y p = priorityResidual L p*(X p-Y p) := by
  induction L with
  | nil => simp [priorityBlend, priorityResidual]
  | cons e L ih =>
    change e.1 p*e.2+(1-e.1 p)*priorityBlend L X p-
      (e.1 p*e.2+(1-e.1 p)*priorityBlend L Y p) =
      (1-e.1 p)*priorityResidual L p*(X p-Y p)
    calc
      _ = (1-e.1 p)*(priorityBlend L X p-priorityBlend L Y p) := by ring
      _ = _ := by rw [ih]; ring

 theorem priorityList_succ (χ : ℕ → E → ℝ) (c : ℕ → ℝ) (n : ℕ) :
    priorityList χ c (n+1) = priorityList χ c n++[(χ n,c n)] := by
  simp [priorityList, List.range_succ]

 theorem priorityList_residual (χ : ℕ → E → ℝ) (c : ℕ → ℝ) (n : ℕ) (p : E) :
    priorityResidual (priorityList χ c n) p = priorityRemainder (fun i => χ i p) n := by
  induction n with
  | zero => simp [priorityList, priorityResidual, priorityRemainder]
  | succ n ih =>
    rw [priorityList_succ, priorityResidual_append, ih, priorityRemainder_succ]
    simp [priorityResidual]

 theorem priorityList_value (χ : ℕ → E → ℝ) (c : ℕ → ℝ) (X : E → ℝ) (n : ℕ) (p : E) :
    priorityBlend (priorityList χ c n) X p =
      priorityRemainder (fun i => χ i p) n*X p +
        ∑ i ∈ Finset.range n, priorityWeight (fun j => χ j p) i*c i := by
  induction n with
  | zero => simp [priorityList, priorityBlend, priorityRemainder]
  | succ n ih =>
    rw [priorityList_succ, priorityBlend_append]
    have h := priorityBlend_sub (priorityList χ c n) (priorityBlend [(χ n,c n)] X) X p
    rw [priorityList_residual, ih] at h
    simp only [priorityBlend] at h
    rw [priorityRemainder_succ, Finset.sum_range_succ]
    dsimp only [priorityBlend, priorityWeight] at h ⊢
    nlinarith only [h]

 theorem priorityInfiniteValue_eq_finite {χ : ℕ → E → ℝ} (c : ℕ → ℝ) (X : E → ℝ)
    {N : ℕ} {p : E} (hz : ∀ n, N ≤ n → χ n p = 0) :
    priorityInfiniteValue (fun n => χ n p) c (X p) = priorityBlend (priorityList χ c N) X p := by
  have hw (n : ℕ) (hn : n ∉ Finset.range N) : priorityWeight (fun i => χ i p) n = 0 := by
    rw [priorityWeight, hz n (by simpa only [Finset.mem_range, not_lt] using hn), zero_mul]
  have hs : (∑' n, priorityWeight (fun i => χ i p) n) =
      ∑ n ∈ Finset.range N, priorityWeight (fun i => χ i p) n := tsum_eq_sum hw
  have hsc : (∑' n, priorityWeight (fun i => χ i p) n*c n) =
      ∑ n ∈ Finset.range N, priorityWeight (fun i => χ i p) n*c n :=
    tsum_eq_sum (fun n hn => by rw [hw n hn, zero_mul])
  rw [priorityInfiniteValue, hs, hsc, priorityWeight_sum, priorityList_value]
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PrioritySmooth
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The priority formula is smooth off the closed source dust because
its shrinking cutoff supports have a common locally vanishing tail. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem priorityBlend_contDiffAt {L : List ((E → ℝ) × ℝ)} {X : E → ℝ} {p : E}
    (hX : ContDiffAt ℝ ∞ X p) (hL : ∀ e ∈ L, ContDiffAt ℝ ∞ e.1 p) :
    ContDiffAt ℝ ∞ (priorityBlend L X) p := by
  induction L with
  | nil => exact hX
  | cons e L ih =>
    have he := hL e (by simp)
    exact (he.mul contDiffAt_const).add ((contDiffAt_const.sub he).mul
      (ih (fun a ha => hL a (by simp [ha]))))

 theorem priorityInfiniteValue_contDiffAt
    (χ : ℕ → E → ℝ) (c : ℕ → ℝ) (X : E → ℝ) {p : E}
    (hX : ContDiffAt ℝ ∞ X p) (hχ : ∀ n, ContDiffAt ℝ ∞ (χ n) p)
    (hz : ∃ N : ℕ, ∀ᶠ q in 𝓝 p, ∀ n, N ≤ n → χ n q = 0) :
    ContDiffAt ℝ ∞ (fun q => priorityInfiniteValue (fun n => χ n q) c (X q)) p := by
  obtain ⟨N, hN⟩ := hz
  have hL : ∀ e ∈ priorityList χ c N, ContDiffAt ℝ ∞ e.1 p := by
    intro e he
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp he
    exact hχ n
  apply (priorityBlend_contDiffAt hX hL).congr_of_eventuallyEq
  filter_upwards [hN] with q hq
  exact priorityInfiniteValue_eq_finite c X hq

 theorem priorityInfiniteValue_smooth_off_dust
    {B : Set E} (hB : IsClosed B) (b : ℕ → E) (hb : ∀ n, b n ∈ B)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (χ : ℕ → E → ℝ) (hχ : ∀ n, ContDiff ℝ ∞ (χ n))
    (hs : ∀ n, support (χ n) ⊆ Metric.ball (b n) (r n))
    (c : ℕ → ℝ) (X : E → ℝ) (hX : ContDiffOn ℝ ∞ X Bᶜ) :
    ContDiffOn ℝ ∞ (fun q => priorityInfiniteValue (fun n => χ n q) c (X q)) Bᶜ := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  apply priorityInfiniteValue_contDiffAt χ c X
    ((hX p hp).contDiffAt (hB.isOpen_compl.mem_nhds hp)) (fun n => (hχ n).contDiffAt)
  obtain ⟨V, hV, hpV, N, hN⟩ := concentrated_cutoffs_eventually_zero hB b hb r hr χ hs hp
  exact ⟨N, Filter.mem_of_superset (hV.mem_nhds hpV) (fun q hq n hn => hN n hn q hq)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelWorkingCoordinates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized model coordinates have local source Sobolev
witnesses on each bounded working region. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem working_coordinate_memLp (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (R : ℝ) :
    MemLp (fun z => (M.function z).re) 2
      (volume.restrict ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 R)) ∧
    MemLp (fun z => (M.function z).im) 2
      (volume.restrict ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 R)) := by
  let D := {z : ℂ | (z : Sphere) ∈ G}
  let U := D ∩ ball (0 : ℂ) R
  have hU : IsOpen U := (hG.preimage OnePoint.continuous_coe).inter isOpen_ball
  let : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr
    ((measure_mono (inter_subset_right : U ⊆ ball 0 R)).trans_lt measure_ball_lt_top).ne
  have hf : ContinuousOn M.function U :=
    (show DifferentiableOn ℂ M.function D from fun z hz =>
      (finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz)).differentiableWithinAt).continuousOn.mono inter_subset_left
  obtain ⟨K,_,hK⟩ := M.function_bounded_on_source_ball hinf R
  constructor
  · exact MemLp.of_bound ((Complex.continuous_re.comp_continuousOn hf).aestronglyMeasurable hU.measurableSet) K
      ((ae_restrict_mem hU.measurableSet).mono (fun z hz =>
        (Complex.abs_re_le_norm (M.function z)).trans (hK z hz.1 hz.2)))
  · exact MemLp.of_bound ((Complex.continuous_im.comp_continuousOn hf).aestronglyMeasurable hU.measurableSet) K
      ((ae_restrict_mem hU.measurableSet).mono (fun z hz =>
        (Complex.abs_im_le_norm (M.function z)).trans (hK z hz.1 hz.2)))

 theorem working_coordinate_witnesses (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (R : ℝ) :
    Nonempty (DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).re)
      (physicalPlaneDomain G ∩ ball 0 R)) ∧
    Nonempty (DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).im)
      (physicalPlaneDomain G ∩ ball 0 R)) := by
  let D := {z : ℂ | (z : Sphere) ∈ G}
  have hD : IsOpen D := hG.preimage OnePoint.continuous_coe
  have hf : ContDiffOn ℝ ∞ M.function D :=
    ((show DifferentiableOn ℂ M.function D from fun z hz =>
      (finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz)).differentiableWithinAt).contDiffOn hD).restrict_scalars ℝ
  have he : complexPlaneCoordinates ⁻¹' (D ∩ ball 0 R) = physicalPlaneDomain G ∩ ball 0 R := by
    ext x
    simp only [mem_preimage, mem_inter_iff, D, mem_ofPred_eq, mem_ball, dist_zero_right,
      complexPlaneCoordinates_norm]
    rfl
  obtain ⟨hLr,hLi⟩ := M.working_coordinate_memLp hG hinf R
  obtain ⟨hEr,hEi⟩ := M.source_coordinate_memLp hG hinf R
  have Wr := complexLocalScalarWitness (hD.inter isOpen_ball)
    ((Complex.reCLM.contDiff.comp_contDiffOn hf).mono inter_subset_left) hLr hEr
  have Wi := complexLocalScalarWitness (hD.inter isOpen_ball)
    ((Complex.imCLM.contDiff.comp_contDiffOn hf).mono inter_subset_left) hLi hEi
  rw [he] at Wr Wi
  exact ⟨⟨Wr⟩,⟨Wi⟩⟩

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ModelPriorityWeakError
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.horizontalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the selected priority error to the actual compact source
Sobolev witness. On the working disk the source cutoff is one. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem priority_weak_error (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    {R d A L δ ε : ℝ} (H : ControlledHeight R d)
    {W : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    (S : FlattenedSourceSelection M H W A L δ ε)
    (η : ℂ → ℝ)
    (hη : ∀ z ∈ {z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 L, η z = 1)
    (Wp : DeGiorgi.MemW1pWitness 2
      (fun x => η (complexPlaneCoordinates x)*priorityInfiniteValue
        (fun n => S.cutoff n (complexPlaneCoordinates x)) S.value
        (M.horizontalSection (planeSphere x))) (physicalPlaneDomain G ∩ ball 0 L))
    (Wx : DeGiorgi.MemW1pWitness 2
      (fun x => (M.function (complexPlaneCoordinates x)).re) (physicalPlaneDomain G ∩ ball 0 L)) :
    (eLpNorm (fun x => Wp.weakGrad x-Wx.weakGrad x) 2
      (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal < ε := by
  let D := {z : ℂ | (z : Sphere) ∈ G}
  let V := D ∩ ball (0 : ℂ) L
  let X := fun z : ℂ => M.horizontalSection (z : Sphere)
  let P := fun z : ℂ => priorityInfiniteValue (fun n => S.cutoff n z) S.value (X z)
  have hD : IsOpen D := hG.preimage OnePoint.continuous_coe
  have hV : IsOpen V := hD.inter isOpen_ball
  have he : complexPlaneCoordinates ⁻¹' V = physicalPlaneDomain G ∩ ball 0 L := by
    ext x
    simp only [mem_preimage, mem_inter_iff, V, D, mem_ofPred_eq, mem_ball,
      dist_zero_right, complexPlaneCoordinates_norm]
    rfl
  have hXs : ContDiffOn ℝ ∞ X V := (M.horizontalSection_plane_smooth hG).mono inter_subset_left
  have hPs : ContDiffOn ℝ ∞ P V := by
    have hh := priorityInfiniteValue_smooth_off_dust hD.isClosed_compl S.center
      S.center_outside S.radius S.radius_tendsto S.cutoff S.cutoff_smooth S.cutoff_support
      S.value X (by simpa only [compl_compl] using M.horizontalSection_plane_smooth hG)
    exact (show ContDiffOn ℝ ∞ P D from by simpa only [compl_compl] using hh).mono inter_subset_left
  have hXE : MemLp (fderiv ℝ X) 2 (volume.restrict V) := M.horizontalSection_plane_memLp hG hinf L
  have hPE : MemLp (fderiv ℝ P) 2 (volume.restrict V) := by
    have hmaj := S.priority_error_memLp.norm.add hXE.norm
    apply hmaj.of_le
      ((hPs.continuousOn_fderiv_of_isOpen hV (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).aestronglyMeasurable hV.measurableSet)
    exact Eventually.of_forall (fun z => by
      change ‖fderiv ℝ P z‖ ≤ ‖‖fderiv ℝ P z-fderiv ℝ X z‖+‖fderiv ℝ X z‖‖
      rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      calc
        _ = ‖(fderiv ℝ P z-fderiv ℝ X z)+fderiv ℝ X z‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _)
  let WP : DeGiorgi.MemW1pWitness 2 (P ∘ complexPlaneCoordinates) (complexPlaneCoordinates ⁻¹' V) := by
    apply localSobolevChangeDomain (V := complexPlaneCoordinates ⁻¹' V) (Wp.congr_ae ?_) he.symm
    filter_upwards [ae_restrict_mem ((isOpen_physicalPlaneDomain hG).inter isOpen_ball).measurableSet] with x hx
    change η (complexPlaneCoordinates x)*P (complexPlaneCoordinates x) = P (complexPlaneCoordinates x)
    rw [hη _ ⟨hx.1, by simpa only [mem_ball, dist_zero_right, complexPlaneCoordinates_norm] using hx.2⟩, one_mul]
  let WX : DeGiorgi.MemW1pWitness 2 (X ∘ complexPlaneCoordinates) (complexPlaneCoordinates ⁻¹' V) := by
    apply localSobolevChangeDomain (V := complexPlaneCoordinates ⁻¹' V) (Wx.congr_ae ?_) he.symm
    filter_upwards [ae_restrict_mem ((isOpen_physicalPlaneDomain hG).inter isOpen_ball).measurableSet] with x hx
    exact (show X (complexPlaneCoordinates x) = (M.function (complexPlaneCoordinates x)).re from by
      simpa only [X, planeSphere, extendAtInfinity_coe, finiteCoord_coe] using M.horizontalSection_on_domain hx.1).symm
  have hn := complex_weak_gradient_difference_L2 hV hPs hXs hPE hXE WP WX
  have hgradP : WP.weakGrad = Wp.weakGrad := by rfl
  have hgradX : WX.weakGrad = Wx.weakGrad := by rfl
  rw [hgradP, hgradX, he] at hn
  rw [hn]
  exact S.priority_error

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ModelSourceTracePairs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The null trace pairs on the actual target complement pull back to
all source ends through the constructed surjective projection. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem section_target_complement (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {q : ℂ} (hq : (q : Sphere) ∉ G) :
    let p := invFun M.projection (q : Sphere)
    finiteCoord p ∈ complexPlaneCoordinates '' (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ ∧
      planeSphere (complexPlaneCoordinates.symm (finiteCoord p)) = p ∧
      M.projection p = (q : Sphere) := by
  let p := invFun M.projection (q : Sphere)
  have hpq : M.projection p = (q : Sphere) :=
    rightInverse_invFun (M.projection_surjective hsard hsch hG hconn hinf hTD) _
  have hpout : p ∉ extendAtInfinity M.function '' G := by
    rintro ⟨x, hx, he⟩
    have hh : M.projection p = x := by rw [← he, M.projection_inverse x hx]
    exact hq ((hh.symm.trans hpq) ▸ hx)
  have hpinf : p ≠ OnePoint.infty := by
    rintro h
    exact hpout (h.symm ▸ ⟨_, hinf, rfl⟩)
  have hplane : planeSphere (complexPlaneCoordinates.symm (finiteCoord p)) = p := by
    simpa only [planeSphere, complexPlaneCoordinates.apply_symm_apply] using coe_finiteCoord hpinf
  refine ⟨?_, hplane, hpq⟩
  refine ⟨complexPlaneCoordinates.symm (finiteCoord p), ?_, complexPlaneCoordinates.apply_symm_apply _⟩
  simpa only [physicalPlaneDomain, mem_compl_iff, mem_preimage, hplane] using hpout

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelScalarPullback
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact global Sobolev target scalar constant on the omitted
components descends to a compact continuous source scalar, with the
conformally transported Sobolev witness on the source domain. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 theorem planeInverseTransport_extendAtInfinity (f : ℂ → ℂ)
    (v : EuclideanPlane → ℝ) (x : EuclideanPlane) :
    planeInverseTransport (extendAtInfinity f) v x =
      sphereFromPlaneFunction v (extendAtInfinity f (planeSphere x)) := by
  simp only [planeInverseTransport, Function.comp_apply, sphereRealMap,
    planeSphere, extendAtInfinity_coe, finiteCoord_coe, sphereFromPlaneFunction_coe]
  rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ModelCompactHeightTrace
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact descended height has exactly the previously constructed
trace at every source end. Compactification does not change null-pair data. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem scalar_section_on_domain (M : CompactScalarModel G u)
    (v : EuclideanPlane → ℝ) {q : Sphere} (hq : q ∈ G) :
    sphereFromPlaneFunction v (invFun M.projection q) =
      sphereFromPlaneFunction v (extendAtInfinity M.function q) := by
  have hh : M.projection (invFun M.projection q) = q :=
    invFun_eq ⟨extendAtInfinity M.function q, M.projection_inverse q hq⟩
  exact congrArg (sphereFromPlaneFunction v)
    ((inverse_projection_fiber_on_domain M.projection_inverse M.projection_outside hq).mp hh)

 theorem compact_height_trace (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {R d : ℝ} (H : ControlledHeight R d) (T : ℝ → ℝ) (η : EuclideanPlane → ℝ)
    (hη : ∀ x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G), η x = 1)
    {q : ℂ} (hq : (q : Sphere) ∉ G) :
    sphereFromPlaneFunction (fun x => η x*T (H.height (complexPlaneCoordinates x)))
      (invFun M.projection (q : Sphere)) = T (M.heightSection H (q : Sphere)) := by
  obtain ⟨hp, hplane, _⟩ := M.section_target_complement hsard hsch hG hconn hinf hTD hq
  let p := invFun M.projection (q : Sphere)
  have hout : complexPlaneCoordinates.symm (finiteCoord p) ∉
      physicalPlaneDomain (extendAtInfinity M.function '' G) := by
    obtain ⟨x, hx, heq⟩ := hp
    have he : complexPlaneCoordinates.symm (finiteCoord p) = x := by
      rw [← heq, complexPlaneCoordinates.symm_apply_apply]
    simpa only [he, mem_compl_iff] using hx
  change sphereFromPlaneFunction _ p = _
  change planeSphere (complexPlaneCoordinates.symm (finiteCoord p)) = p at hplane
  conv_lhs => rw [← hplane]
  simp only [planeSphere, sphereFromPlaneFunction_coe,
    hη _ hout, one_mul, complexPlaneCoordinates.apply_symm_apply, heightSection]
  rfl

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_PriorityTracePairs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Priority modification preserves every trace pair whose other
coordinate is constant on its cutoff supports. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity

 theorem priorityInfiniteValue_eq_outside_support
    {X : Type*} (χ : ℕ → X → ℝ) (c : ℕ → ℝ) (v : X → ℝ)
    {x : X} (hx : x ∉ ⋃ n, support (χ n)) :
    priorityInfiniteValue (fun n => χ n x) c (v x) = v x := by
  have hzero (n : ℕ) : χ n x = 0 := by
    by_contra hh
    exact hx (mem_iUnion.mpr ⟨n, hh⟩)
  simp only [priorityInfiniteValue, priorityWeight, hzero, zero_mul, tsum_zero,
    sub_zero, one_mul, add_zero]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LocalHeightDifference
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The flattened height minus the genuine vertical coordinate has an
explicit local weak gradient and a controlled compact cutoff. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem subtractSobolevWitness_gradient {U : Set EuclideanPlane} {u v : EuclideanPlane → ℝ}
    (Wu : DeGiorgi.MemW1pWitness 2 u U) (Wv : DeGiorgi.MemW1pWitness 2 v U) (x : EuclideanPlane) :
    (subtractSobolevWitness Wu Wv).weakGrad x = Wu.weakGrad x-Wv.weakGrad x := by
  simp only [subtractSobolevWitness, DeGiorgi.MemW1pWitness.congr_ae,
    DeGiorgi.MemW1pWitness.add, DeGiorgi.MemW1pWitness.smul, neg_one_smul, sub_eq_add_neg]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ModelCompactTransport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact target scalars have finite source L2 norm even when their
values do not descend across the source dust. This permits transport
of the actual vertical error, which need not be constant on holes. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem source_bounded_over_compact_target (M : CompactScalarModel G u)
    (hinf : OnePoint.infty ∈ G) {K : Set EuclideanPlane} (hK : IsCompact K) :
    ∃ R ≥ 0, ∀ z : ℂ, (z : Sphere) ∈ G →
      complexPlaneCoordinates.symm (M.function z) ∈ K → ‖z‖ ≤ R := by
  let C := M.projection '' (planeSphere '' K)
  have hC : IsCompact C := (hK.image continuous_planeSphere).image M.projection_continuous
  have hno : OnePoint.infty ∉ C := by
    rintro ⟨p, ⟨x, hx, rfl⟩, hp⟩
    have hh : planeSphere x = OnePoint.infty :=
      (inverse_projection_fiber_on_domain M.projection_inverse M.projection_outside hinf).mp
        (by simpa only [extendAtInfinity_infty] using hp)
    exact OnePoint.coe_ne_infty (complexPlaneCoordinates x) hh
  obtain ⟨R, hR⟩ := (hC.image_of_continuousOn
    (continuousOn_finiteCoord_of_avoids_infty hno)).isBounded.exists_norm_le
  refine ⟨max R 0, le_max_right _ _, fun z hz hk => ?_⟩
  apply (hR z ?_).trans (le_max_left _ _)
  refine ⟨(z : Sphere), ?_, by simp only [finiteCoord_coe]⟩
  refine ⟨(M.function z : Sphere), ?_, ?_⟩
  · exact ⟨_, hk, by simp only [planeSphere, complexPlaneCoordinates.apply_symm_apply]⟩
  · simpa only [extendAtInfinity_coe] using M.projection_inverse _ hz

 theorem compact_target_pullback_memLp (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    {v : EuclideanPlane → ℝ} (hv : Continuous v) (hs : HasCompactSupport v) :
    MemLp (planeInverseTransport (extendAtInfinity M.function) v) 2
      (volume.restrict (physicalPlaneDomain G)) := by
  let w := planeInverseTransport (extendAtInfinity M.function) v
  have hw (x : EuclideanPlane) : w x = v (complexPlaneCoordinates.symm
      (M.function (complexPlaneCoordinates x))) := by
    change planeInverseTransport (extendAtInfinity M.function) v x = _
    rw [planeInverseTransport_extendAtInfinity]
    simp only [planeSphere, extendAtInfinity_coe, sphereFromPlaneFunction_coe]
  have hD : IsOpen {z : ℂ | (z : Sphere) ∈ G} := hG.preimage OnePoint.continuous_coe
  have hf : ContinuousOn M.function {z : ℂ | (z : Sphere) ∈ G} :=
    (show DifferentiableOn ℂ M.function _ from fun z hz =>
      (finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz)).differentiableWithinAt).continuousOn
  have hc : ContinuousOn w (physicalPlaneDomain G) := by
    have hh := (hv.comp complexPlaneCoordinates.symm.continuous).continuousOn.comp
      (hf.comp complexPlaneCoordinates.continuous.continuousOn (fun _ hx => hx)) (mapsTo_univ _ _)
    exact hh.congr (fun x _ => hw x)
  obtain ⟨R, _, hR⟩ := M.source_bounded_over_compact_target hinf hs.isCompact
  obtain ⟨B, hB⟩ := hv.bounded_above_of_compact_support hs
  have hI : MemLp ((closedBall (0 : EuclideanPlane) R).indicator (fun _ => B)) 2 volume :=
    memLp_indicator_const 2 measurableSet_closedBall B
      (Or.inr (measure_closedBall_lt_top.ne))
  apply (hI.restrict _).of_le (hc.aestronglyMeasurable (isOpen_physicalPlaneDomain hG).measurableSet)
  filter_upwards [ae_restrict_mem (isOpen_physicalPlaneDomain hG).measurableSet] with x hx
  by_cases hxs : complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x)) ∈ tsupport v
  · have hxR : x ∈ closedBall (0 : EuclideanPlane) R := by
      rw [mem_closedBall_zero_iff]
      simpa only [complexPlaneCoordinates_norm] using hR _ hx hxs
    rw [indicator_of_mem hxR, hw]
    exact (hB _).trans (le_abs_self B)
  · rw [hw, image_eq_zero_of_notMem_tsupport hxs, norm_zero]
    exact norm_nonneg _

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelHeightSourceError
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the transported compact vertical error with the
actual source height error on a region retained by the target cutoff.
The energy comparison uses uniqueness of weak gradients. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem compact_height_error_on_source (M : CompactScalarModel G u)
    {R d : ℝ} (H : ControlledHeight R d) (T : ℝ → ℝ) (η : EuclideanPlane → ℝ)
    {x : EuclideanPlane} (hx : x ∈ physicalPlaneDomain G)
    (hη : η (complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x))) = 1) :
    planeInverseTransport (extendAtInfinity M.function)
      (fun y => η y*(T (H.height (complexPlaneCoordinates y))-y 1)) x =
    sphereFromPlaneFunction (fun y => η y*T (H.height (complexPlaneCoordinates y)))
      (invFun M.projection (planeSphere x))-(M.function (complexPlaneCoordinates x)).im := by
  rw [M.scalar_section_on_domain _ hx, planeInverseTransport_extendAtInfinity]
  simp only [planeSphere, extendAtInfinity_coe, sphereFromPlaneFunction_coe,
    complexPlaneCoordinates.apply_symm_apply, hη, one_mul]
  rfl

 theorem compact_height_source_error_energy (M : CompactScalarModel G u)
    {R d : ℝ} (H : ControlledHeight R d) (T : ℝ → ℝ) (η : EuclideanPlane → ℝ)
    {U : Set EuclideanPlane} (hU : IsOpen U) (hUG : U ⊆ physicalPlaneDomain G)
    (hη : ∀ x ∈ U, η (complexPlaneCoordinates.symm
      (M.function (complexPlaneCoordinates x))) = 1)
    (Q : DeGiorgi.MemW1pWitness 2 (fun x =>
      sphereFromPlaneFunction (fun y => η y*T (H.height (complexPlaneCoordinates y)))
        (invFun M.projection (planeSphere x))) U)
    (Y : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).im) U)
    (E : DeGiorgi.MemW1pWitness 2
      (planeInverseTransport (extendAtInfinity M.function)
        (fun y => η y*(T (H.height (complexPlaneCoordinates y))-y 1))) (physicalPlaneDomain G)) :
    (∫ x in U, ‖Q.weakGrad x-Y.weakGrad x‖^2) ≤
      ∫ x in physicalPlaneDomain G, E.weakGrad x 0^2+E.weakGrad x 1^2 := by
  let W := subtractSobolevWitness Q Y
  let E' := (E.restrict hU hUG).congr_ae
    ((ae_restrict_mem hU.measurableSet).mono (fun x hx =>
      M.compact_height_error_on_source H T η (hUG hx) (hη x hx)))
  have he := W.ae_eq hU E'
  have he' : ∀ᵐ x ∂volume.restrict U, Q.weakGrad x-Y.weakGrad x = E.weakGrad x := by
    filter_upwards [he] with x hx
    simpa only [W, subtractSobolevWitness_gradient, E',
      DeGiorgi.MemW1pWitness.congr_ae, DeGiorgi.MemW1pWitness.restrict] using hx
  have hi : Integrable (fun x => ‖E.weakGrad x‖^2) (volume.restrict (physicalPlaneDomain G)) :=
    E.weakGrad_norm_memLp.integrable_sq
  calc
    _ = ∫ x in U, ‖E.weakGrad x‖^2 := integral_congr_ae
      (he'.mono (fun _ hx => congrArg (fun z : EuclideanPlane => ‖z‖^2) hx))
    _ ≤ ∫ x in physicalPlaneDomain G, ‖E.weakGrad x‖^2 :=
      setIntegral_mono_set hi (Eventually.of_forall (fun _ => sq_nonneg _))
        (Eventually.of_forall hUG)
    _ = _ := by simp only [plane_norm_sq]

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelHeightWorkingError
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform and L2 errors for the actual compact descended height on a
source working region whose image is retained by the target cutoff. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem compact_height_uniform_error (M : CompactScalarModel G u)
    {R d ζ δ : ℝ} (H : ControlledHeight R d) (T : ℝ → ℝ)
    (hT : ∀ t, |T t-t| ≤ ζ) (η : EuclideanPlane → ℝ)
    {x : EuclideanPlane} (hx : x ∈ physicalPlaneDomain G)
    (hη : η (complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x))) = 1)
    (hH : |H.height (M.function (complexPlaneCoordinates x))-
      (M.function (complexPlaneCoordinates x)).im| ≤ δ) :
    |sphereFromPlaneFunction (fun y => η y*T (H.height (complexPlaneCoordinates y)))
      (invFun M.projection (planeSphere x))-(M.function (complexPlaneCoordinates x)).im| ≤ ζ+δ := by
  rw [M.scalar_section_on_domain _ hx]
  simp only [planeSphere, extendAtInfinity_coe, sphereFromPlaneFunction_coe, hη,
    complexPlaneCoordinates.apply_symm_apply, one_mul]
  exact (abs_sub_le _ _ _).trans (add_le_add (hT _) hH)

 theorem compact_height_source_error_L2 (M : CompactScalarModel G u)
    {R d : ℝ} (H : ControlledHeight R d) (T : ℝ → ℝ) (η : EuclideanPlane → ℝ)
    {U : Set EuclideanPlane} (hU : IsOpen U) (hUG : U ⊆ physicalPlaneDomain G)
    (hη : ∀ x ∈ U, η (complexPlaneCoordinates.symm
      (M.function (complexPlaneCoordinates x))) = 1)
    (Q : DeGiorgi.MemW1pWitness 2 (fun x =>
      sphereFromPlaneFunction (fun y => η y*T (H.height (complexPlaneCoordinates y)))
        (invFun M.projection (planeSphere x))) U)
    (Y : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).im) U)
    (E : DeGiorgi.MemW1pWitness 2
      (planeInverseTransport (extendAtInfinity M.function)
        (fun y => η y*(T (H.height (complexPlaneCoordinates y))-y 1))) (physicalPlaneDomain G))
    {B : ℝ} (hE : (∫ x in physicalPlaneDomain G, E.weakGrad x 0^2+E.weakGrad x 1^2) ≤ B) :
    (eLpNorm (fun x => Q.weakGrad x-Y.weakGrad x) 2 (volume.restrict U)).toReal^2 ≤ B := by
  have hm := Q.weakGrad_memLp.sub Y.weakGrad_memLp
  have hn := integral_sq_eq_eLpNorm_toReal_sq hm.norm
  rw [eLpNorm_norm _] at hn
  change (eLpNorm (Q.weakGrad-Y.weakGrad) 2 (volume.restrict U)).toReal^2 ≤ B
  rw [← hn]
  exact (M.compact_height_source_error_energy H T η hU hUG hη Q Y E).trans hE

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelPairWorkingError
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Outside the actual changed horizontal support, only the vertical
error remains in the selected two-coordinate source map. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem planePair_same_first_norm (a b c : ℝ) :
    ‖planePair a b-planePair a c‖ = |b-c| := by
  have h : ‖planePair a b-planePair a c‖^2 = (b-c)^2 := by
    rw [plane_norm_sq]
    simp only [PiLp.sub_apply, planePair_zero, planePair_one, sub_self, zero_pow (by decide : 2 ≠ 0), zero_add]
  nlinarith [norm_nonneg (planePair a b-planePair a c), abs_nonneg (b-c), sq_abs (b-c)]

namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem compact_pair_error_outside_support (M : CompactScalarModel G u)
    {R d ζ δ : ℝ} (H : ControlledHeight R d) (T : ℝ → ℝ)
    (hT : ∀ t, |T t-t| ≤ ζ) (η : ℂ → ℝ) (θ : EuclideanPlane → ℝ)
    (χ : ℕ → ℂ → ℝ) (c : ℕ → ℝ)
    {x : EuclideanPlane} (hx : x ∈ physicalPlaneDomain G)
    (hη : η (complexPlaneCoordinates x) = 1)
    (hθ : θ (complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x))) = 1)
    (hH : |H.height (M.function (complexPlaneCoordinates x))-
      (M.function (complexPlaneCoordinates x)).im| ≤ δ)
    (hs : complexPlaneCoordinates x ∉ ⋃ n, support (χ n)) :
    ‖planePair (M.compactPrioritySource χ c η x) (M.compactHeightSource H T θ x)-
      planePair ((M.function (complexPlaneCoordinates x)).re) ((M.function (complexPlaneCoordinates x)).im)‖ ≤ ζ+δ := by
  have hp : M.compactPrioritySource χ c η x = (M.function (complexPlaneCoordinates x)).re := by
    simp only [compactPrioritySource, hη, one_mul]
    rw [priorityInfiniteValue_eq_outside_support χ c (fun z : ℂ => M.horizontalSection (z : Sphere)) hs]
    simpa only [planeSphere, extendAtInfinity_coe, finiteCoord_coe] using M.horizontalSection_on_domain hx
  rw [hp, planePair_same_first_norm]
  exact M.compact_height_uniform_error H T hT θ hx hθ hH

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_HolomorphicWeakRows
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.horizontalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Holomorphic source coordinates have equal row energy. Consequently
controlling the selected horizontal changed-set energy controls the
whole reference differential used by the barrier comparison. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem complex_weak_gradient_norm
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f D) (hE : MemLp (fderiv ℝ f) 2 (volume.restrict D))
    (W : DeGiorgi.MemW1pWitness 2 (f ∘ complexPlaneCoordinates) (complexPlaneCoordinates ⁻¹' D)) :
    (fun x => ‖W.weakGrad x‖) =ᵐ[volume.restrict (complexPlaneCoordinates ⁻¹' D)]
      fun x => ‖fderiv ℝ f (complexPlaneCoordinates x)‖ := by
  filter_upwards [complex_weak_gradient_ae hD hf hE W] with x hx
  rw [hx, complex_plane_covector_norm]

 theorem holomorphic_weak_rows_norm_eq
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f D)
    (hEr : MemLp (fderiv ℝ (fun z => (f z).re)) 2 (volume.restrict D))
    (hEi : MemLp (fderiv ℝ (fun z => (f z).im)) 2 (volume.restrict D))
    (Wr : DeGiorgi.MemW1pWitness 2 (fun x => (f (complexPlaneCoordinates x)).re)
      (complexPlaneCoordinates ⁻¹' D))
    (Wi : DeGiorgi.MemW1pWitness 2 (fun x => (f (complexPlaneCoordinates x)).im)
      (complexPlaneCoordinates ⁻¹' D)) :
    (fun x => ‖Wr.weakGrad x‖) =ᵐ[volume.restrict (complexPlaneCoordinates ⁻¹' D)]
      fun x => ‖Wi.weakGrad x‖ := by
  have hs : ContDiffOn ℝ ∞ f D := (hf.contDiffOn hD).restrict_scalars ℝ
  have hr := complex_weak_gradient_norm hD (Complex.reCLM.contDiff.comp_contDiffOn hs) hEr Wr
  have hi := complex_weak_gradient_norm hD (Complex.imCLM.contDiff.comp_contDiffOn hs) hEi Wi
  filter_upwards [hr,hi,ae_restrict_mem (hD.preimage complexPlaneCoordinates.continuous).measurableSet] with x hxr hxi hx
  rw [hxr,hxi]
  change ‖fderiv ℝ (fun z => (f z).re) (complexPlaneCoordinates x)‖ =
    ‖fderiv ℝ (fun z => (f z).im) (complexPlaneCoordinates x)‖
  have hd := (hf _ hx).differentiableAt (hD.mem_nhds hx)
  have he := (holomorphic_real_fderiv_norm_sq hd).trans (holomorphic_imag_fderiv_norm_sq hd).symm
  nlinarith [norm_nonneg (fderiv ℝ (fun z => (f z).re) (complexPlaneCoordinates x)),
    norm_nonneg (fderiv ℝ (fun z => (f z).im) (complexPlaneCoordinates x))]

 theorem weak_pair_indicator_bound
    {U S : Set EuclideanPlane} (hS : MeasurableSet S)
    {a b : EuclideanPlane → EuclideanPlane}
    (ha : MemLp a 2 (volume.restrict U)) (hb : MemLp b 2 (volume.restrict U))
    (heq : (fun x => ‖a x‖) =ᵐ[volume.restrict U] fun x => ‖b x‖) :
    (eLpNorm (S.indicator (fun x => ‖weakPairDifferential (a x) (b x)‖)) 2
      (volume.restrict U)).toReal ≤
      2*(eLpNorm (S.indicator (fun x => ‖a x‖)) 2 (volume.restrict U)).toReal := by
  have hA := ha.norm.indicator hS
  have hB := (weakPairDifferential_memLp ha hb).1.norm.indicator hS
  have hz : MemLp (fun _ : EuclideanPlane => (0 : ℝ)) 2 (volume.restrict U) := MemLp.zero'
  have hh := l2_three_term_bound (a := 2) (b := 0) (c := 0) (by norm_num) le_rfl le_rfl
    hB.aestronglyMeasurable hA hz hz
    (Eventually.of_forall (fun x => by exact indicator_nonneg (fun _ _ => norm_nonneg _) x))
    (Eventually.of_forall (fun _ => le_rfl)) (Eventually.of_forall (fun _ => le_rfl)) (by
      filter_upwards [heq] with x hx
      by_cases hs : x ∈ S
      · simp only [indicator_of_mem hs, Real.norm_eq_abs, abs_norm, zero_mul, add_zero]
        exact (weakPairDifferential_norm_le _ _).trans (by rw [← hx]; ring_nf; exact le_rfl)
      · simp only [indicator_of_notMem hs, norm_zero, mul_zero, add_zero, le_refl])
  simpa only [zero_mul, add_zero] using hh.2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ModelWorkingGradients
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reference rows on a source working disk are the actual model
coordinate gradients, with equal norms and the exact horizontal norm. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem working_rows_norm_eq (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (L : ℝ)
    (Wx : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).re)
      (physicalPlaneDomain G ∩ ball 0 L))
    (Wy : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).im)
      (physicalPlaneDomain G ∩ ball 0 L)) :
    (fun x => ‖Wx.weakGrad x‖) =ᵐ[volume.restrict (physicalPlaneDomain G ∩ ball 0 L)]
      fun x => ‖Wy.weakGrad x‖ := by
  let D := {z : ℂ | (z : Sphere) ∈ G}
  have hD : IsOpen D := hG.preimage OnePoint.continuous_coe
  have he : complexPlaneCoordinates ⁻¹' (D ∩ ball 0 L) = physicalPlaneDomain G ∩ ball 0 L := by
    ext x
    simp only [mem_preimage, mem_inter_iff, D, mem_ofPred_eq, mem_ball,
      dist_zero_right, complexPlaneCoordinates_norm]
    rfl
  obtain ⟨hEr,hEi⟩ := M.source_coordinate_memLp hG hinf L
  have hf : DifferentiableOn ℂ M.function (D ∩ ball 0 L) := fun z hz =>
    (finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz.1)).differentiableWithinAt
  have h := holomorphic_weak_rows_norm_eq (hD.inter isOpen_ball) hf hEr hEi
  rw [he] at h
  exact h Wx Wy

 theorem working_horizontal_norm (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (L : ℝ)
    (Wx : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).re)
      (physicalPlaneDomain G ∩ ball 0 L)) :
    (fun x => ‖Wx.weakGrad x‖) =ᵐ[volume.restrict (physicalPlaneDomain G ∩ ball 0 L)]
      fun x => ‖fderiv ℝ (fun z : ℂ => M.horizontalSection (z : Sphere)) (complexPlaneCoordinates x)‖ := by
  let D := {z : ℂ | (z : Sphere) ∈ G}
  have hD : IsOpen D := hG.preimage OnePoint.continuous_coe
  have he : complexPlaneCoordinates ⁻¹' (D ∩ ball 0 L) = physicalPlaneDomain G ∩ ball 0 L := by
    ext x
    simp only [mem_preimage, mem_inter_iff, D, mem_ofPred_eq, mem_ball,
      dist_zero_right, complexPlaneCoordinates_norm]
    rfl
  have hf : DifferentiableOn ℂ M.function D := fun z hz =>
    (finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz)).differentiableWithinAt
  have hs : ContDiffOn ℝ ∞ (fun z => (M.function z).re) (D ∩ ball 0 L) := (Complex.reCLM.contDiff.comp_contDiffOn ((hf.contDiffOn hD).restrict_scalars ℝ)).mono
    (inter_subset_left : D ∩ ball 0 L ⊆ D)
  have hn := complex_weak_gradient_norm (hD.inter isOpen_ball) hs
    (M.source_coordinate_memLp hG hinf L).1
  rw [he] at hn
  filter_upwards [hn Wx, ae_restrict_mem ((isOpen_physicalPlaneDomain hG).inter isOpen_ball).measurableSet] with x hx hxU
  rw [hx]
  congr 1
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [hD.mem_nhds hxU.1] with z hz
  exact (show M.horizontalSection (z : Sphere) = (M.function z).re from by
    simpa only [planeSphere, extendAtInfinity_coe, finiteCoord_coe] using M.horizontalSection_on_domain hz).symm

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelSelectedSupport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.horizontalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual selected support has small energy for the entire reference
map, by conformality and the retained horizontal support budget. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem selected_support_error (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    {R d A L δ ε : ℝ} (H : ControlledHeight R d)
    {W : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    (S : FlattenedSourceSelection M H W A L δ ε)
    (Wx : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).re)
      (physicalPlaneDomain G ∩ ball 0 L))
    (Wy : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).im)
      (physicalPlaneDomain G ∩ ball 0 L)) :
    (eLpNorm ((complexPlaneCoordinates ⁻¹' ⋃ n, support (S.cutoff n)).indicator
      (fun x => ‖weakPairDifferential (Wx.weakGrad x) (Wy.weakGrad x)‖)) 2
        (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal < 2*ε := by
  let C := ⋃ n, support (S.cutoff n)
  have hC : MeasurableSet C := MeasurableSet.iUnion
    (fun n => (S.cutoff_smooth n).continuous.isOpen_support.measurableSet)
  have hCp : MeasurableSet (complexPlaneCoordinates ⁻¹' C) :=
    hC.preimage complexPlaneCoordinates.continuous.measurable
  have hb := weak_pair_indicator_bound hCp Wx.weakGrad_memLp Wy.weakGrad_memLp
    (M.working_rows_norm_eq hG hinf L Wx Wy)
  have he : eLpNorm ((complexPlaneCoordinates ⁻¹' C).indicator (fun x => ‖Wx.weakGrad x‖)) 2
      (volume.restrict (physicalPlaneDomain G ∩ ball 0 L)) =
      eLpNorm (C.indicator (fun z => ‖fderiv ℝ (fun w : ℂ => M.horizontalSection (w : Sphere)) z‖)) 2
        (volume.restrict ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 L)) := by
    have hn := M.working_horizontal_norm hG hinf L Wx
    have hind : (complexPlaneCoordinates ⁻¹' C).indicator (fun x => ‖Wx.weakGrad x‖) =ᵐ[
        volume.restrict (physicalPlaneDomain G ∩ ball 0 L)]
        (C.indicator (fun z => ‖fderiv ℝ (fun w : ℂ => M.horizontalSection (w : Sphere)) z‖)) ∘
          complexPlaneCoordinates := by
      filter_upwards [hn] with x hx
      by_cases hc : complexPlaneCoordinates x ∈ C
      · simpa only [indicator_of_mem hc, indicator_of_mem (show x ∈ complexPlaneCoordinates ⁻¹' C from hc), Function.comp_apply] using hx
      · simp only [Function.comp_apply, indicator_of_notMem hc,
          indicator_of_notMem (show x ∉ complexPlaneCoordinates ⁻¹' C from hc)]
    rw [eLpNorm_congr_ae hind]
    have hD := (hG.preimage OnePoint.continuous_coe).inter (isOpen_ball (x := (0 : ℂ)) (ε := L))
    have hp : complexPlaneCoordinates ⁻¹' ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 L) =
        physicalPlaneDomain G ∩ ball 0 L := by
      ext x
      simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_ball, dist_zero_right,
        complexPlaneCoordinates_norm]
      rfl
    have hm := (M.horizontalSection_plane_memLp hG hinf L).norm.indicator hC
    have hh := eLpNorm_comp_measurePreserving hm.aestronglyMeasurable
      (complexPlaneCoordinates_measurePreserving.restrict_preimage hD.measurableSet) (p := 2)
    simpa only [hp] using hh
  rw [he] at hb
  exact hb.trans_lt (mul_lt_mul_of_pos_left S.support_error (by norm_num))

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ModelSelectedBarrier
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual selected compact source pair satisfies the quantitative
barrier comparison. Its horizontal, vertical and support terms are
proved from the selection and transported height-error witness. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem selected_barrier_error (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    {R d A L δ ε : ℝ} (H : ControlledHeight R d)
    {Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    (S : FlattenedSourceSelection M H Wold A L δ ε)
    (η : ℂ → ℝ) (θ : EuclideanPlane → ℝ)
    (hη : ∀ z ∈ {z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 L, η z = 1)
    (hθ : ∀ x ∈ physicalPlaneDomain G ∩ ball 0 L,
      θ (complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x))) = 1)
    (hp : Continuous (M.compactPrioritySource S.cutoff S.value η))
    (hq : Continuous (M.compactHeightSource H (flattenValues S.heightValues) θ))
    (Wp : DeGiorgi.MemW1pWitness 2 (M.compactPrioritySource S.cutoff S.value η)
      (physicalPlaneDomain G ∩ ball 0 L))
    (Wq : DeGiorgi.MemW1pWitness 2 (M.compactHeightSource H (flattenValues S.heightValues) θ)
      (physicalPlaneDomain G ∩ ball 0 L))
    (Wx : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).re)
      (physicalPlaneDomain G ∩ ball 0 L))
    (Wy : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).im)
      (physicalPlaneDomain G ∩ ball 0 L))
    (E : DeGiorgi.MemW1pWitness 2 (planeInverseTransport (extendAtInfinity M.function)
      (fun y => θ y*(flattenValues S.heightValues (H.height (complexPlaneCoordinates y))-y 1)))
      (physicalPlaneDomain G))
    {ν δv : ℝ} (hν : 0 ≤ ν) (hδ : 0 ≤ δ) (hδv : 0 ≤ δv)
    (hE : (∫ x in physicalPlaneDomain G, E.weakGrad x 0^2+E.weakGrad x 1^2) ≤ ν^2)
    (hheight : ∀ x ∈ physicalPlaneDomain G ∩ ball 0 L,
      |H.height (M.function (complexPlaneCoordinates x))-(M.function (complexPlaneCoordinates x)).im| ≤ δv)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    {B M₁ M₂ : ℝ} (hB : 0 ≤ B) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hΦb : ∀ z, ‖Φ z‖ ≤ B) (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ M₁)
    (hlip : ∀ z w, ‖fderiv ℝ Φ z-fderiv ℝ Φ w‖ ≤ M₂*‖z-w‖) :
    ∃ W : DeGiorgi.MemW1pWitness 2 (fun x => Φ (planePair
        (M.compactPrioritySource S.cutoff S.value η x)
        (M.compactHeightSource H (flattenValues S.heightValues) θ x)))
      (physicalPlaneDomain G ∩ ball 0 L),
      (eLpNorm (fun x => W.weakGrad x-planeCovectorGradient
        ((fderiv ℝ Φ (planePair ((M.function (complexPlaneCoordinates x)).re)
          ((M.function (complexPlaneCoordinates x)).im))).comp
          (weakPairDifferential (Wx.weakGrad x) (Wy.weakGrad x)))) 2
            (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal ≤
      M₁*(ε+ν)+(M₂*(δ+δv))*(eLpNorm
        (fun x => weakPairDifferential (Wx.weakGrad x) (Wy.weakGrad x)) 2
          (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal+4*M₁*ε := by
  let U := physicalPlaneDomain G ∩ ball (0 : EuclideanPlane) L
  let C := complexPlaneCoordinates ⁻¹' ⋃ n, support (S.cutoff n)
  have hU : IsOpen U := (isOpen_physicalPlaneDomain hG).inter isOpen_ball
  have hUf : volume U ≠ (⊤ : ℝ≥0∞) := ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  have hC : MeasurableSet C := (MeasurableSet.iUnion
    (fun n => (S.cutoff_smooth n).continuous.isOpen_support.measurableSet)).preimage
      complexPlaneCoordinates.continuous.measurable
  have hpE := M.priority_weak_error hG hinf H S η hη Wp Wx
  have hqE := M.compact_height_source_error_L2 H (flattenValues S.heightValues) θ
    hU inter_subset_left hθ Wq Wy E hE
  have hqE' : (eLpNorm (fun x => Wq.weakGrad x-Wy.weakGrad x) 2 (volume.restrict U)).toReal ≤ ν := by
    nlinarith [ENNReal.toReal_nonneg (a := eLpNorm (fun x => Wq.weakGrad x-Wy.weakGrad x) 2 (volume.restrict U))]
  have hsE := M.selected_support_error hG hinf H S Wx Wy
  obtain ⟨W,hW,hn⟩ := local_weak_barrier_bound hU hUf hC hp hq Wp Wq Wx Wy
    hΦ hB hM₁ hM₂ (add_nonneg hδ hδv) hΦb hbound hlip (fun x hx hxc =>
      M.compact_pair_error_outside_support H (flattenValues S.heightValues)
        (fun t => (S.height_close t).le) η θ S.cutoff S.value hx.1
        (hη _ ⟨hx.1, by simpa only [mem_ball, dist_zero_right, complexPlaneCoordinates_norm] using hx.2⟩)
        (hθ x hx) (hheight x hx) hxc)
  refine ⟨W,hn.trans ?_⟩
  have h₁ := mul_le_mul_of_nonneg_left (add_le_add hpE.le hqE') hM₁
  have h₂ := mul_le_mul_of_nonneg_left hsE.le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM₁)
  calc
    _ ≤ M₁*(ε+ν)+(M₂*(δ+δv))*(eLpNorm
        (fun x => weakPairDifferential (Wx.weakGrad x) (Wy.weakGrad x)) 2
        (volume.restrict U)).toReal+(2*M₁)*(2*ε) :=
      add_le_add (add_le_add h₁ le_rfl) h₂
    _ = _ := by ring

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_BarrierErrorBudgets
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose the finite numerical budgets in the order required by the
near-extremal model construction. No analytic conclusion is assumed. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_barrier_error_budget {η M₁ M₂ N : ℝ}
    (hη : 0 < η) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hN : 0 ≤ N) :
    ∃ t : ℝ, 0 < t ∧ M₁*(t+t)+(M₂*(t+t))*N+4*M₁*t < η/3 := by
  let C := 6*M₁+2*M₂*N+1
  have hC : 0 < C := by dsimp only [C] <;> positivity
  let t := (η/3)/C
  have ht : 0 < t := div_pos (by positivity) hC
  have he : t*C = η/3 := div_mul_cancel₀ _ hC.ne'
  refine ⟨t,ht,?_⟩
  have he' : M₁*(t+t)+(M₂*(t+t))*N+4*M₁*t = t*C-t := by dsimp only [C] <;> ring
  rw [he',he]
  linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ModelUniformBounds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform omitted-set and working-disk bounds for the actual compact
scalar models. The constants depend on the source exterior radius alone. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem uniform_omitted_and_image_bound (M : CompactScalarModel G u)
    (harea : ExteriorCoefficientAreaTheorem) (hG : IsOpen G)
    {R : ℝ} (hR : 0 < R)
    (hsource : (((↑) : ℂ → Sphere) '' ball 0 R)ᶜ ⊆ G) :
    (∀ z : ℂ, (z : Sphere) ∉ extendAtInfinity M.function '' G → ‖z‖ ≤ 3*R) ∧
      ∀ z : ℂ, (z : Sphere) ∈ G → ‖z‖ ≤ 4*R → ‖M.function z‖ ≤ 5*R := by
  obtain ⟨hfc,hmap,fi,hfic,hfimap,hl,hr⟩ := M.conformal
  have heq : IsSmoothSphereEquivalence (extendAtInfinity M.function) fi G
      (extendAtInfinity M.function '' G) :=
    ⟨fun p hp => hfc.isSmoothSphereAt hG hp, hmap,
      fun p hp => hfic.isSmoothSphereAt M.image_open hp, hfimap, hl, hr⟩
  have hc : IsConformalOn (extendAtInfinity M.function)
      ((((↑) : ℂ → Sphere) '' closedBall 0 R)ᶜ) := by
    intro p hp
    exact hfc p (hsource ((compl_subset_compl.mpr (image_mono ball_subset_closedBall)) hp))
  obtain ⟨hF,hbound⟩ := normalized_model_uniform_bound harea heq M.image_open hR hsource hc M.normalized
  constructor
  · intro z hz
    obtain ⟨w,hw,he⟩ := hF (z : Sphere) hz
    have hzw : w = z := OnePoint.coe_injective he
    simpa only [hzw, mem_closedBall, dist_zero_right] using hw
  · intro z hz hzr
    obtain ⟨w,hw,he⟩ := hbound z hz hzr
    have hzw : w = M.function z := OnePoint.coe_injective (by simpa only [extendAtInfinity_coe] using he)
    simpa only [hzw, mem_closedBall, dist_zero_right] using hw

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelSelectedBounds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform bounds on the actual selected priority traces. The selected
horizontal values are values on the model complement, not extra data. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem outside_of_projection_outside (M : CompactScalarModel G u)
    {p : Sphere} (hp : M.projection p ∉ G) : p ∉ extendAtInfinity M.function '' G := by
  rintro ⟨q,hq,rfl⟩
  exact hp ((M.projection_inverse q hq).symm ▸ hq)

 theorem finiteCoord_bound_of_projection_outside (M : CompactScalarModel G u)
    (hinf : OnePoint.infty ∈ G) {C : ℝ}
    (hC : ∀ z : ℂ, (z : Sphere) ∉ extendAtInfinity M.function '' G → ‖z‖ ≤ C)
    {p : Sphere} (hp : M.projection p ∉ G) : ‖finiteCoord p‖ ≤ C := by
  have hout := M.outside_of_projection_outside hp
  cases p using OnePoint.rec with
  | infty => exact (hout ⟨OnePoint.infty,hinf,rfl⟩).elim
  | coe z => exact hC z hout

 theorem horizontalSection_trace_bound (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {C : ℝ} (hC : ∀ z : ℂ, (z : Sphere) ∉ extendAtInfinity M.function '' G → ‖z‖ ≤ C)
    {z : ℂ} (hz : (z : Sphere) ∉ G) : ‖M.horizontalSection (z : Sphere)‖ ≤ C := by
  obtain ⟨_,_,hproj⟩ := M.section_target_complement hsard hsch hG hconn hinf hTD hz
  have hh := M.finiteCoord_bound_of_projection_outside hinf hC (by rw [hproj]; exact hz)
  exact (Complex.abs_re_le_norm _).trans hh

 theorem FlattenedSourceSelection.value_bound (M : CompactScalarModel G u)
    {R d : ℝ} {H : ControlledHeight R d}
    {W : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    {A L δ ε : ℝ} (S : FlattenedSourceSelection M H W A L δ ε)
    (hinf : OnePoint.infty ∈ G) {C : ℝ}
    (hC : ∀ z : ℂ, (z : Sphere) ∉ extendAtInfinity M.function '' G → ‖z‖ ≤ C) (n : ℕ) :
    ‖S.value n‖ ≤ C := by
  rw [S.value_eq]
  apply (Complex.abs_re_le_norm _).trans
  apply M.finiteCoord_bound_of_projection_outside hinf hC
  rw [S.target_projection]
  exact S.center_outside n

 theorem FlattenedSourceSelection.priority_trace_bound (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {R d : ℝ} {H : ControlledHeight R d}
    {W : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    {A L δ ε : ℝ} (S : FlattenedSourceSelection M H W A L δ ε)
    {C : ℝ} (hC : ∀ z : ℂ, (z : Sphere) ∉ extendAtInfinity M.function '' G → ‖z‖ ≤ C)
    {z : ℂ} (hz : (z : Sphere) ∉ G) :
    ‖priorityInfiniteValue (fun n => S.cutoff n z) S.value (M.horizontalSection (z : Sphere))‖ ≤ C := by
  exact priorityInfiniteValue_norm_le (fun n => S.cutoff_unit n z)
    (S.value_bound M hinf hC) (M.horizontalSection_trace_bound hsard hsch hG hconn hinf hTD hC hz)

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_SelectedTraceBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected compact pair has a uniform trace bound, obtained from
the actual omitted set and controlled-height closeness. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem planePair_norm_le (a b : ℝ) : ‖planePair a b‖ ≤ |a|+|b| := by
  have he : ‖planePair a b‖^2 = a^2+b^2 := by simp only [plane_norm_sq, planePair_zero, planePair_one]
  nlinarith [norm_nonneg (planePair a b), abs_nonneg a, abs_nonneg b, sq_abs a, sq_abs b,
    mul_nonneg (abs_nonneg a) (abs_nonneg b)]

namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem selected_pair_trace_bound (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {R d A L δ ε C v : ℝ} (H : ControlledHeight R d)
    {Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    (S : FlattenedSourceSelection M H Wold A L δ ε)
    (hC : ∀ z : ℂ, (z : Sphere) ∉ extendAtInfinity M.function '' G → ‖z‖ ≤ C)
    (hH : ∀ z ∈ closedBall 0 C, |H.height z-z.im| ≤ v)
    (η : ℂ → ℝ) (hη : ∀ z : ℂ, (z : Sphere) ∉ G → η z = 1)
    (θ : EuclideanPlane → ℝ)
    (hθ : ∀ x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G), θ x = 1)
    {z : ℂ} (hz : (z : Sphere) ∉ G) :
    ‖planePair
      (sphereFromPlaneFunction (M.compactPrioritySource S.cutoff S.value η) (z : Sphere))
      (sphereFromPlaneFunction (M.compactHeightSource H (flattenValues S.heightValues) θ) (z : Sphere))‖
      ≤ 2*C+δ+v := by
  have hp := S.priority_trace_bound M hsard hsch hG hconn hinf hTD hC hz
  have hp' : |sphereFromPlaneFunction (M.compactPrioritySource S.cutoff S.value η) (z : Sphere)| ≤ C := by
    simpa only [sphereFromPlaneFunction_coe, compactPrioritySource,
      complexPlaneCoordinates.apply_symm_apply, hη z hz, one_mul, Real.norm_eq_abs] using hp
  have hqeq : sphereFromPlaneFunction (M.compactHeightSource H (flattenValues S.heightValues) θ)
      (z : Sphere) = flattenValues S.heightValues (M.heightSection H (z : Sphere)) := by
    simpa only [sphereFromPlaneFunction_coe, compactHeightSource, planeSphere,
      complexPlaneCoordinates.apply_symm_apply] using
        M.compact_height_trace hsard hsch hG hconn hinf hTD H (flattenValues S.heightValues) θ hθ hz
  have hfinite := M.finiteCoord_bound_of_projection_outside hinf hC
    (show M.projection (invFun M.projection (z : Sphere)) ∉ G from by
      rw [(M.section_target_complement hsard hsch hG hconn hinf hTD hz).2.2]
      exact hz)
  have hh := hH (finiteCoord (invFun M.projection (z : Sphere)))
    (mem_closedBall_zero_iff.mpr hfinite)
  have hy := Complex.abs_im_le_norm (finiteCoord (invFun M.projection (z : Sphere)))
  have hheight : |M.heightSection H (z : Sphere)| ≤ v+C := by
    have ht := abs_sub_le (H.height (finiteCoord (invFun M.projection (z : Sphere))))
      (finiteCoord (invFun M.projection (z : Sphere))).im 0
    simp only [sub_zero, heightSection] at *
    linarith
  have hq' : |sphereFromPlaneFunction (M.compactHeightSource H (flattenValues S.heightValues) θ)
      (z : Sphere)| ≤ δ+v+C := by
    rw [hqeq]
    have ht := abs_sub_le (flattenValues S.heightValues (M.heightSection H (z : Sphere)))
      (M.heightSection H (z : Sphere)) 0
    simp only [sub_zero] at ht
    linarith [S.height_close (M.heightSection H (z : Sphere))]
  exact (planePair_norm_le _ _).trans (by linarith)

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothCutoffLinePayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth balloon derivative bound pays for all line increments,
including segments crossing components on which the raw scalar jumps. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem smooth_line_increment_payment {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) {x y : ℝ}
    (hg : IntervalIntegrable g volume x y)
    (hb : ∀ t ∈ uIcc x y, |deriv f t| ≤ g t) :
    |f x-f y| ≤ ∫ t in uIoc x y, g t := by
  have hi : IntervalIntegrable (deriv f) volume x y :=
    hf.continuous_deriv_one.intervalIntegrable x y
  have he := intervalIntegral.integral_deriv_eq_sub
    (fun z (_ : z ∈ uIcc y x) => hf.differentiable_one z) hi.symm
  rw [← he,← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
  rw [uIoc_comm y x]
  apply integral_mono_ae hi.norm.def' hg.def'
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  exact hb t (uIoc_subset_uIcc ht)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_NormedAffineLinePayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unit affine lines in a real normed space pay through the actual
Fréchet derivative. This includes both coordinate directions in a rectangle. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem normed_affine_line_increment {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ∀ z, ‖fderiv ℝ f z‖ ≤ g z) (z e : E) (he : ‖e‖ ≤ 1) {x y : ℝ}
    (hgi : IntervalIntegrable (fun t => g (z+t • e)) volume x y) :
    |f (z+x • e)-f (z+y • e)| ≤ ∫ t in uIoc x y, g (z+t • e) := by
  apply smooth_line_increment_payment (hf.comp (by fun_prop)) hgi
  intro t _
  have hline : HasDerivAt (fun s : ℝ => z+s • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add z
  have hder := ((hf.differentiable_one (z+t • e)).hasFDerivAt.comp_hasDerivAt t hline).deriv
  rw [hder,← Real.norm_eq_abs]
  exact ((fderiv ℝ f (z+t • e)).unit_le_opNorm e he).trans (hg _)

 theorem smooth_horizontal_increment {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (y x₁ x₂ : ℝ) : |f (x₁,y)-f (x₂,y)| ≤
      ∫ t in uIoc x₁ x₂, ‖fderiv ℝ f (t,y)‖ := by
  have hc : Continuous (fun t : ℝ => ‖fderiv ℝ f (t,y)‖) :=
    hf.continuous_fderiv (by norm_num) |>.norm |>.comp (by fun_prop)
  simpa only [Prod.smul_mk,Prod.mk_add_mk,smul_eq_mul,mul_one,mul_zero,zero_add,add_zero] using
    normed_affine_line_increment hf (fun _ => le_rfl) (0,y) (1,0) (by simp)
      (by simpa only [Prod.smul_mk,Prod.mk_add_mk,smul_eq_mul,mul_one,mul_zero,zero_add,add_zero]
        using hc.intervalIntegrable x₁ x₂)

 theorem smooth_vertical_increment {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (x y₁ y₂ : ℝ) : |f (x,y₁)-f (x,y₂)| ≤
      ∫ t in uIoc y₁ y₂, ‖fderiv ℝ f (x,t)‖ := by
  have hc : Continuous (fun t : ℝ => ‖fderiv ℝ f (x,t)‖) :=
    hf.continuous_fderiv (by norm_num) |>.norm |>.comp (by fun_prop)
  simpa only [Prod.smul_mk,Prod.mk_add_mk,smul_eq_mul,mul_one,mul_zero,zero_add,add_zero] using
    normed_affine_line_increment hf (fun _ => le_rfl) (x,0) (0,1) (by simp)
      (by simpa only [Prod.smul_mk,Prod.mk_add_mk,smul_eq_mul,mul_one,mul_zero,zero_add,add_zero]
        using hc.intervalIntegrable y₁ y₂)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelExteriorEstimate
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized model retains the pointwise exterior estimate
needed on the fixed outer source collar. -/
open Set Function Filter MeasureTheory Metric Asymptotics Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem exterior_deviation_le (M : CompactScalarModel G u)
    (harea : ExteriorCoefficientAreaTheorem) {R : ℝ} (hR : 0 < R)
    (hsource : (((↑) : ℂ → Sphere) '' ball 0 R)ᶜ ⊆ G) :
    ∀ z : ℂ, 2*R ≤ ‖z‖ → ‖M.function z-z‖ ≤ R := by
  have hsub {z : ℂ} (hz : R < ‖z‖) : (z : Sphere) ∈ G := by
    apply hsource
    rintro ⟨w,hw,he⟩
    have hwz : w = z := OnePoint.coe_injective he
    subst w
    have := mem_ball_zero_iff.mp hw
    linarith
  have hf : DifferentiableOn ℂ M.function {z | R < ‖z‖} := fun z hz =>
    (finite_differentiable_of_sphere_conformal (M.conformal.1 _ (hsub hz))).differentiableWithinAt
  have hi : InjOn M.function {z | R < ‖z‖} := by
    intro z hz w hw he
    apply OnePoint.coe_injective
    apply M.conformal.bijOn.injOn (hsub hz) (hsub hw)
    simpa only [extendAtInfinity_coe] using congrArg ((↑) : ℂ → Sphere) he
  have hn : (fun z : ℂ => M.function z-z) =O[cobounded ℂ] (fun z => z⁻¹) := by
    simpa only [extendAtInfinity_coe, finiteCoord_coe] using M.normalized.2
  exact harea.scaled_exterior_bound hR hf hi hn

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_OuterBarrierMargin
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict separation from every trace center on the fixed outer
source collar, from the genuine exterior and vertical error estimates. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem outer_pair_margin {P H z c : EuclideanPlane} {a e C r η : ℝ}
    (hPH : ‖P-H‖ ≤ e) (hHz : ‖H-z‖ ≤ a) (hc : ‖c‖ ≤ C)
    (hz : r+η+e+a+C ≤ ‖z‖) : r+η ≤ ‖P-c‖ := by
  have h₁ : ‖z‖ ≤ ‖z-H‖+‖H‖ := by
    simpa only [sub_add_cancel] using norm_add_le (z-H) H
  have h₂ : ‖H‖ ≤ ‖H-P‖+‖P-c‖+‖c‖ := by
    have hh := norm_add_le (H-P) ((P-c)+c)
    simpa only [sub_add_cancel, add_assoc] using hh.trans
      (add_le_add le_rfl (norm_add_le (P-c) c))
  rw [norm_sub_rev z H] at h₁
  rw [norm_sub_rev H P] at h₂
  linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PhysicalSmallBarrier
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.horizontalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smooth planar barriers with arbitrarily small energy and
uniform first/second differential bounds for all their translates. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_physical_small_barrier {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∃ (Φ : EuclideanPlane → ℝ) (r M₁ M₂ : ℝ),
      0 < r ∧ 0 ≤ M₁ ∧ 0 ≤ M₂ ∧ ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧
      tsupport Φ ⊆ ball 0 R ∧ (∀ x, Φ x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ ball 0 r, Φ x = 1) ∧
      (∫ x, ‖planeCovectorGradient (fderiv ℝ Φ x)‖^2) < ε ∧
      (∀ x, ‖fderiv ℝ Φ x‖ ≤ M₁) ∧
      (∀ x y, ‖fderiv ℝ Φ x-fderiv ℝ Φ y‖ ≤ M₂*‖x-y‖) := by
  obtain ⟨f,hf,hs,hsR,hunit,hone,henergy⟩ := exists_small_energy_cutoff 0 hR hε
  let Φ := f ∘ complexPlaneCoordinates
  have hΦ : ContDiff ℝ ∞ Φ := hf.comp complexPlaneCoordinates.contDiff
  have hsΦ : HasCompactSupport Φ := hs.comp_homeomorph complexPlaneCoordinates.toHomeomorph
  have hsup : tsupport Φ ⊆ ball 0 R := by
    rw [show Φ = f ∘ complexPlaneCoordinates.toHomeomorph from rfl, tsupport_comp_eq_preimage]
    intro x hx
    have hh := hsR hx
    change complexPlaneCoordinates x ∈ ball (0 : ℂ) R at hh
    simpa only [mem_ball, dist_zero_right, complexPlaneCoordinates_norm] using hh
  have hΦone : ∀ᶠ x in 𝓝 (0 : EuclideanPlane), Φ x = 1 := by
    have ht : Tendsto complexPlaneCoordinates (𝓝 (0 : EuclideanPlane)) (𝓝 (0 : ℂ)) := by
      simpa only [map_zero] using complexPlaneCoordinates.continuous.tendsto (0 : EuclideanPlane)
    exact ht.eventually hone
  obtain ⟨r,hr,hrΦ⟩ := Metric.mem_nhds_iff.mp hΦone
  obtain ⟨C,hC⟩ := (hsΦ.fderiv ℝ).exists_bound_of_continuous (hΦ.continuous_fderiv (by simp))
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hsΦ.fderiv ℝ)
    (hΦ.fderiv_right (m := (⊤ : ℕ∞)) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he : (∫ x, ‖planeCovectorGradient (fderiv ℝ Φ x)‖^2) = ∫ z, ‖fderiv ℝ f z‖^2 := by
    calc
      _ = ∫ x, ‖fderiv ℝ f (complexPlaneCoordinates x)‖^2 := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => by
          dsimp only [Φ]
          rw [fderiv_comp x (hf.differentiable (by simp) _) complexPlaneCoordinates.differentiableAt,
            complexPlaneCoordinates.fderiv, complex_plane_covector_norm])
      _ = _ := complexPlaneCoordinates_measurePreserving.integral_comp
        complexPlaneCoordinates.toHomeomorph.measurableEmbedding (fun z : ℂ => ‖fderiv ℝ f z‖^2)
  refine ⟨Φ,r,max C 0,K,hr,le_max_right _ _,K.coe_nonneg,hΦ,hsΦ,hsup,
    (fun x => hunit _),hrΦ,he.trans_lt henergy,?_,?_⟩
  · intro x
    exact (hC x).trans (le_max_left _ _)
  · intro x y
    simpa only [dist_eq_norm] using hK.dist_le_mul x y

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_TranslatedPhysicalBarrier
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translating a physical barrier preserves its energy and derivative
bounds; the plateau and support move to the selected trace center. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem translatedPhysicalBarrier_energy {Φ : EuclideanPlane → ℝ}
    (hΦ : Differentiable ℝ Φ) (c : EuclideanPlane) :
    (∫ x, ‖planeCovectorGradient (fderiv ℝ (translatedPhysicalBarrier Φ c) x)‖^2) =
      ∫ x, ‖planeCovectorGradient (fderiv ℝ Φ x)‖^2 := by
  simp_rw [translatedPhysicalBarrier_fderiv hΦ]
  exact integral_sub_right_eq_self (fun x => ‖planeCovectorGradient (fderiv ℝ Φ x)‖^2) c

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_IncrementDerivativeBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Increment domination passes to derivatives. The integral criterion
then yields the linewise weak-gradient bound used by the barrier. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

theorem abs_derivative_le_of_increment_domination
    {f F : ℝ → ℝ} {x f' F' : ℝ}
    (hf : HasDerivAt f f' x) (hF : HasDerivAt F F' x)
    (h : ∀ᶠ y in 𝓝 x, |f y - f x| ≤ |F y - F x|) : |f'| ≤ |F'| := by
  apply le_of_tendsto_of_tendsto hf.tendsto_slope.abs hF.tendsto_slope.abs
  filter_upwards [h.filter_mono nhdsWithin_le_nhds] with y hy
  simp only [slope, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)

theorem ae_abs_deriv_le_of_integral_bound
    {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b)
    (hgnonneg : ∀ᵐ x ∂volume.restrict (Icc a b), 0 ≤ g x)
    (hbound : ∀x ∈ Icc a b, ∀y ∈ Icc a b,
      |f x - f y| ≤ ∫t in uIoc x y, g t) :
    ∀ᵐ x ∂volume.restrict (Icc a b), |deriv f x| ≤ g x := by
  have hac : AbsolutelyContinuousOnInterval f a b :=
    absolutelyContinuousOnInterval_of_integral_bound hg (by
      simpa only [uIcc_of_le hab, Real.dist_eq] using hbound)
  have hd := hac.ae_differentiableAt
  have hH := hg.ae_hasDerivAt_integral
  have hi : ∀ᵐ x ∂volume.restrict (Icc a b), x ∈ Ioo a b := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [show ∀ᵐ x : ℝ, x ≠ a by simp [ae_iff], show ∀ᵐ x : ℝ, x ≠ b by simp [ae_iff]] with x hxa hxb hx
    exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
  filter_upwards [ae_restrict_of_ae hd, ae_restrict_of_ae hH, hgnonneg, hi] with x hdx hHx hpos hx
  have hdx' : DifferentiableAt ℝ f x := hdx (by simpa only [uIcc_of_le hab] using ⟨hx.1.le, hx.2.le⟩)
  have hHx' := hHx (by simpa only [uIcc_of_le hab] using (show x ∈ Icc a b from ⟨hx.1.le, hx.2.le⟩))
    a left_mem_uIcc
  have hdom : ∀ᶠ y in 𝓝 x, |f y - f x| ≤
      |(∫t in a..y, g t) - ∫t in a..x, g t| := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    apply (hbound y ⟨hy.1.le, hy.2.le⟩ x ⟨hx.1.le, hx.2.le⟩).trans
    rw [intervalIntegral.integral_interval_sub_left
      (hg.mono_set' (uIoc_subset_uIoc_of_uIcc_subset_uIcc
        (uIcc_subset_uIcc left_mem_uIcc (by simpa only [uIcc_of_le hab] using (show y ∈ Icc a b from ⟨hy.1.le, hy.2.le⟩)))))
      (hg.mono_set' (uIoc_subset_uIoc_of_uIcc_subset_uIcc
        (uIcc_subset_uIcc left_mem_uIcc (by simpa only [uIcc_of_le hab] using (show x ∈ Icc a b from ⟨hx.1.le, hx.2.le⟩))))),
      intervalIntegral.abs_intervalIntegral_eq]
    simpa only [uIoc_comm x y] using (le_abs_self (∫t in uIoc y x, g t))
  simpa only [abs_of_nonneg hpos] using
    abs_derivative_le_of_increment_domination hdx'.hasDerivAt hHx' hdom

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_MeasurableLineDerivatives
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On an open set, almost everywhere line differentiability of a measurable
function makes its line derivative measurable. The proof uses actual
difference quotients of the zero extension, so no continuity across the
exceptional lines is required. -/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Measure.IsAddRightInvariant μ]

/-- A Borel representative agrees with the line derivative at every
differentiability point outside one fixed null set. This implication form
can be sliced by Fubini before asserting almost everywhere differentiability. -/
theorem exists_measurable_lineDeriv_representative
    {U : Set E} (hU : IsOpen U) {f : E → ℝ} (v : E)
    (hf : AEStronglyMeasurable f (μ.restrict U)) :
    ∃ G : E → ℝ, Measurable G ∧
      ∀ᵐ x ∂μ, x ∈ U → LineDifferentiableAt ℝ f x v →
        G x = lineDeriv ℝ f x v := by
  let F : E → ℝ := U.indicator f
  have hF : AEStronglyMeasurable F μ :=
    (aestronglyMeasurable_indicator_iff hU.measurableSet).2 hf
  let F₀ := hF.mk F
  let h : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let q : ℕ → E → ℝ := fun n x => (h n)⁻¹ * (F₀ (x + h n • v) - F₀ x)
  have hq (n : ℕ) : Measurable (q n) :=
    ((hF.measurable_mk.comp (continuous_id.add continuous_const).measurable).sub
      hF.measurable_mk).const_mul _
  refine ⟨fun x => limsup (fun n => q n x) atTop, Measurable.limsup hq, ?_⟩
  have he (n : ℕ) : ∀ᵐ x ∂μ, F (x + h n • v) = F₀ (x + h n • v) :=
    (measurePreserving_add_right μ (h n • v)).quasiMeasurePreserving.ae hF.ae_eq_mk
  filter_upwards [hF.ae_eq_mk, ae_all_iff.2 he] with x hx₀ hx₁ hx hd
  have hx₀' : F x = F₀ x := hx₀
  have hh : Tendsto h atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall (fun n => by
        change 1 / ((n : ℝ) + 1) ≠ 0
        positivity)⟩
  have hlim := hd.hasDerivAt.tendsto_slope_zero.comp hh
  have hin : ∀ᶠ n in atTop, x + h n • v ∈ U := by
    have ht : Tendsto (fun n => x + h n • v) atTop (𝓝 x) := by
      simpa only [zero_smul, add_zero] using
        tendsto_const_nhds.add ((tendsto_nhds_of_tendsto_nhdsWithin hh).smul_const v)
    exact ht (hU.mem_nhds hx)
  have hq_lim : Tendsto (fun n => q n x) atTop (𝓝 (lineDeriv ℝ f x v)) := by
    apply hlim.congr'
    filter_upwards [hin] with n hn
    simp only [q, ← hx₀', ← hx₁ n, F, indicator_of_mem hn,
      indicator_of_mem hx, zero_add, zero_smul, add_zero, smul_eq_mul, Function.comp_apply]
  exact hq_lim.limsup_eq

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RectangleDerivativeRepresentatives
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable representatives of the two ACL derivatives in a physical
rectangle. The null set is chosen before slicing, and exceptional lines
are discarded only after applying Fubini. -/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem ae_mem_Ioo_of_Icc (a b : ℝ) :
    ∀ᵐ x ∂volume.restrict (Icc a b), x ∈ Ioo a b := by
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [show ∀ᵐ x : ℝ, x ≠ a by simp [ae_iff],
    show ∀ᵐ x : ℝ, x ≠ b by simp [ae_iff]] with x hxa hxb hx
  exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩

theorem lineDeriv_horizontal (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    lineDeriv ℝ f p (1, 0) = deriv (fun t => f (t, p.2)) p.1 := by
  rcases p with ⟨x, y⟩
  simp only [lineDeriv, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero,
    Prod.mk_add_mk, add_zero]
  simpa only [add_zero] using deriv_comp_const_add (fun t => f (t, y)) x 0

theorem lineDeriv_vertical (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    lineDeriv ℝ f p (0, 1) = deriv (fun t => f (p.1, t)) p.2 := by
  rcases p with ⟨x, y⟩
  simp only [lineDeriv, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero,
    Prod.mk_add_mk, add_zero]
  simpa only [add_zero] using deriv_comp_const_add (fun t => f (x, t)) y 0

theorem exists_measurable_horizontal_derivative
    (f : ℝ × ℝ → ℝ) {a b c d : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hac : ∀ᵐ y ∂volume.restrict (Icc c d),
      AbsolutelyContinuousOnInterval (fun x => f (x, y)) a b) :
    ∃ G : ℝ × ℝ → ℝ, Measurable G ∧
      ∀ᵐ y ∂volume.restrict (Icc c d), ∀ᵐ x ∂volume.restrict (Icc a b),
        G (x, y) = deriv (fun t => f (t, y)) x := by
  let : Measure.IsAddRightInvariant (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  obtain ⟨G, hG, hrep⟩ := exists_measurable_lineDeriv_representative
    (isOpen_Ioo.prod isOpen_Ioo) (1, 0) hf
  have hrep' : ∀ᵐ y ∂volume, ∀ᵐ x ∂volume,
      (x, y) ∈ Ioo a b ×ˢ Ioo c d → LineDifferentiableAt ℝ f (x, y) (1, 0) →
        G (x, y) = lineDeriv ℝ f (x, y) (1, 0) := by
    have hr := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae (by
        simpa only [Measure.volume_eq_prod] using hrep)
    exact Measure.ae_ae_of_ae_prod hr
  refine ⟨G, hG, ?_⟩
  filter_upwards [hac, ae_mem_Ioo_of_Icc c d, ae_restrict_of_ae hrep'] with y hy hyI hyr
  filter_upwards [ae_mem_Ioo_of_Icc a b,
    ae_restrict_of_ae hy.ae_differentiableAt, ae_restrict_of_ae hyr] with x hxI hxd hxr
  have hd := hxd (Icc_subset_uIcc ⟨hxI.1.le, hxI.2.le⟩)
  have hline : LineDifferentiableAt ℝ f (x, y) (1, 0) := by
    have h : HasDerivAt (fun t => f (t, y)) (deriv (fun t => f (t, y)) x) (x + 0) := by
      simpa only [add_zero] using hd.hasDerivAt
    have ht := h.comp_const_add x 0
    simpa only [LineDifferentiableAt, Prod.smul_mk, smul_eq_mul, mul_one,
      mul_zero, Prod.mk_add_mk, add_zero] using ht.differentiableAt
  exact (hxr ⟨hxI, hyI⟩ hline).trans (lineDeriv_horizontal f (x, y))

theorem exists_measurable_vertical_derivative
    (f : ℝ × ℝ → ℝ) {a b c d : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hac : ∀ᵐ x ∂volume.restrict (Icc a b),
      AbsolutelyContinuousOnInterval (fun y => f (x, y)) c d) :
    ∃ G : ℝ × ℝ → ℝ, Measurable G ∧
      ∀ᵐ x ∂volume.restrict (Icc a b), ∀ᵐ y ∂volume.restrict (Icc c d),
        G (x, y) = deriv (fun t => f (x, t)) y := by
  let : Measure.IsAddRightInvariant (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  obtain ⟨G, hG, hrep⟩ := exists_measurable_lineDeriv_representative
    (isOpen_Ioo.prod isOpen_Ioo) (0, 1) hf
  have hrep' : ∀ᵐ x ∂volume, ∀ᵐ y ∂volume,
      (x, y) ∈ Ioo a b ×ˢ Ioo c d → LineDifferentiableAt ℝ f (x, y) (0, 1) →
        G (x, y) = lineDeriv ℝ f (x, y) (0, 1) :=
    Measure.ae_ae_of_ae_prod (by simpa only [Measure.volume_eq_prod] using hrep)
  refine ⟨G, hG, ?_⟩
  filter_upwards [hac, ae_mem_Ioo_of_Icc a b, ae_restrict_of_ae hrep'] with x hx hxI hxr
  filter_upwards [ae_mem_Ioo_of_Icc c d,
    ae_restrict_of_ae hx.ae_differentiableAt, ae_restrict_of_ae hxr] with y hyI hyd hyr
  have hd := hyd (Icc_subset_uIcc ⟨hyI.1.le, hyI.2.le⟩)
  have hline : LineDifferentiableAt ℝ f (x, y) (0, 1) := by
    have h : HasDerivAt (fun t => f (x, t)) (deriv (fun t => f (x, t)) y) (y + 0) := by
      simpa only [add_zero] using hd.hasDerivAt
    have ht := h.comp_const_add y 0
    simpa only [LineDifferentiableAt, Prod.smul_mk, smul_eq_mul, mul_one,
      mul_zero, Prod.mk_add_mk, add_zero] using ht.differentiableAt
  exact (hyr ⟨hxI, hyI⟩ hline).trans (lineDeriv_vertical f (x, y))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ACLWeakDerivatives
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integration by parts for the Borel representatives of ACL derivatives.
This converts the actual slice derivative into a planar weak derivative. -/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem integral_mul_horizontal_deriv_eq_neg
    {f G : ℝ × ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b)
    (hf : Integrable f (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hG : Integrable G (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hac : ∀ᵐ y ∂volume.restrict (Icc c d),
      AbsolutelyContinuousOnInterval (fun x => f (x, y)) a b)
    (hrep : ∀ᵐ y ∂volume.restrict (Icc c d), ∀ᵐ x ∂volume.restrict (Icc a b),
      G (x, y) = deriv (fun t => f (t, y)) x)
    {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : HasCompactSupport φ) (hsub : tsupport φ ⊆ Ioo a b ×ˢ Ioo c d) :
    (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ φ p) (1, 0)) =
      -(∫p in Icc a b ×ˢ Icc c d, G p * φ p) := by
  have hcD : Continuous (fun p => (fderiv ℝ φ p) (1, 0)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨C, hC⟩ := hcD.bounded_above_of_compact_support (hsupp.fderiv_apply (𝕜 := ℝ) (1, 0))
  obtain ⟨D, hD⟩ := hφ.continuous.bounded_above_of_compact_support hsupp
  have hl : Integrable (fun p => f p * (fderiv ℝ φ p) (1, 0))
      (volume.restrict (Icc a b ×ˢ Icc c d)) :=
    hf.mul_bdd hcD.aestronglyMeasurable (Eventually.of_forall hC)
  have hr : Integrable (fun p => G p * φ p)
      (volume.restrict (Icc a b ×ˢ Icc c d)) :=
    hG.mul_bdd hφ.continuous.aestronglyMeasurable (Eventually.of_forall hD)
  have hp (x y : ℝ) : deriv (fun t => φ (t, y)) x = (fderiv ℝ φ (x, y)) (1, 0) := by
    exact ((hφ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))).deriv
  have hzero (x y : ℝ) (hx : x ∉ Ioo a b) : φ (x, y) = 0 := by
    by_contra hn
    exact hx (hsub (subset_tsupport φ hn)).1
  have hline : ∀ᵐ y ∂volume.restrict (Icc c d),
      (∫x in Icc a b, f (x, y) * (fderiv ℝ φ (x, y)) (1, 0)) =
        -(∫x in Icc a b, G (x, y) * φ (x, y)) := by
    filter_upwards [hac, hrep] with y hy hyr
    have hφline : AbsolutelyContinuousOnInterval (fun x => φ (x, y)) a b :=
      ((hφ.comp (contDiff_id.prodMk contDiff_const)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffOn.absolutelyContinuousOnInterval
    have hi := hy.integral_mul_deriv_eq_deriv_mul hφline
    rw [hzero b y (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top), hzero a y (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top), mul_zero, mul_zero, sub_self,
      zero_sub] at hi
    simp only [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc] at hi
    calc
      _ = ∫x in Icc a b, f (x, y) * deriv (fun t => φ (t, y)) x := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => congrArg (fun z => f (x, y) * z) (hp x y).symm
      _ = -(∫x in Icc a b, deriv (fun t => f (t, y)) x * φ (x, y)) := hi
      _ = -(∫x in Icc a b, G (x, y) * φ (x, y)) := by
        congr 1
        exact integral_congr_ae (hyr.mono fun x hx => congrArg (fun z => z * φ (x, y)) hx.symm)
  have he : (volume : Measure (ℝ × ℝ)).restrict (Icc a b ×ˢ Icc c d) =
      (volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  rw [he] at hl hr ⊢
  rw [integral_prod_symm _ hl, integral_prod_symm _ hr, ← integral_neg]
  exact integral_congr_ae hline

theorem integral_mul_vertical_deriv_eq_neg
    {f G : ℝ × ℝ → ℝ} {a b c d : ℝ} (hcd : c ≤ d)
    (hf : Integrable f (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hG : Integrable G (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hac : ∀ᵐ x ∂volume.restrict (Icc a b),
      AbsolutelyContinuousOnInterval (fun y => f (x, y)) c d)
    (hrep : ∀ᵐ x ∂volume.restrict (Icc a b), ∀ᵐ y ∂volume.restrict (Icc c d),
      G (x, y) = deriv (fun t => f (x, t)) y)
    {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : HasCompactSupport φ) (hsub : tsupport φ ⊆ Ioo a b ×ˢ Ioo c d) :
    (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ φ p) (0, 1)) =
      -(∫p in Icc a b ×ˢ Icc c d, G p * φ p) := by
  let e := ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  have hswap : MeasurePreserving e
      (volume.restrict (Icc c d ×ˢ Icc a b))
      (volume.restrict (Icc a b ×ˢ Icc c d)) := by
    change MeasurePreserving Prod.swap _ _
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, ← Measure.prod_restrict]
    exact Measure.measurePreserving_swap
  have hs : tsupport (φ ∘ e) ⊆ Ioo c d ×ˢ Ioo a b := by
    change tsupport (φ ∘ e.toHomeomorph) ⊆ _
    rw [tsupport_comp_eq_preimage φ e.toHomeomorph]
    intro p hp
    exact ⟨(hsub hp).2, (hsub hp).1⟩
  have hi := integral_mul_horizontal_deriv_eq_neg hcd
    (hswap.integrable_comp_of_integrable hf) (hswap.integrable_comp_of_integrable hG)
    hac hrep (hφ.comp e.contDiff) (hsupp.comp_homeomorph e.toHomeomorph) hs
  have hd (p : ℝ × ℝ) :
      (fderiv ℝ (φ ∘ e) p) (1, 0) = (fderiv ℝ φ (e p)) (0, 1) := by
    rw [fderiv_comp p (hφ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt e.differentiableAt,
      e.fderiv]
    rfl
  simp only [Function.comp_apply, hd] at hi
  calc
    _ = ∫p in Icc c d ×ˢ Icc a b, f (e p) * (fderiv ℝ φ (e p)) (0, 1) :=
      (hswap.integral_comp e.toHomeomorph.measurableEmbedding _).symm
    _ = -(∫p in Icc c d ×ˢ Icc a b, G (e p) * φ (e p)) := hi
    _ = _ := congrArg Neg.neg (hswap.integral_comp e.toHomeomorph.measurableEmbedding
      (fun p => G p * φ p))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RectangleSobolev
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ACL and an L² bound on the line derivatives produce an actual local
Sobolev gradient. All gradient fields here are constructed Borel functions. -/

open Set Filter MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem rectangle_restrict_Ioo_eq_Icc (a b c d : ℝ) :
    (volume : Measure (ℝ × ℝ)).restrict (Ioo a b ×ˢ Ioo c d) =
      volume.restrict (Icc a b ×ˢ Icc c d) := by
  rw [Measure.volume_eq_prod]
  exact Measure.restrict_congr_set (Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc)

theorem exists_rectangle_weak_gradient
    {f ρ : ℝ × ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : MemLp f 2 (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hρ : Measurable ρ) (hρ₂ : MemLp ρ 2 (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hacx : ∀ᵐ y ∂volume.restrict (Icc c d),
      AbsolutelyContinuousOnInterval (fun x => f (x, y)) a b)
    (hacy : ∀ᵐ x ∂volume.restrict (Icc a b),
      AbsolutelyContinuousOnInterval (fun y => f (x, y)) c d)
    (hbx : ∀ᵐ y ∂volume.restrict (Icc c d), ∀ᵐ x ∂volume.restrict (Icc a b),
      |deriv (fun t => f (t, y)) x| ≤ ρ (x, y))
    (hby : ∀ᵐ x ∂volume.restrict (Icc a b), ∀ᵐ y ∂volume.restrict (Icc c d),
      |deriv (fun t => f (x, t)) y| ≤ ρ (x, y)) :
    ∃ Gx Gy : ℝ × ℝ → ℝ, Measurable Gx ∧ Measurable Gy ∧
      MemLp Gx 2 (volume.restrict (Icc a b ×ˢ Icc c d)) ∧
      MemLp Gy 2 (volume.restrict (Icc a b ×ˢ Icc c d)) ∧
      (∀ᵐ p ∂volume.restrict (Icc a b ×ˢ Icc c d), |Gx p| ≤ ρ p ∧ |Gy p| ≤ ρ p) ∧
      ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ioo c d →
        (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ φ p) (1, 0)) =
          -(∫p in Icc a b ×ˢ Icc c d, Gx p * φ p) ∧
        (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ φ p) (0, 1)) =
          -(∫p in Icc a b ×ˢ Icc c d, Gy p * φ p) := by
  let : IsFiniteMeasure ((volume : Measure (ℝ × ℝ)).restrict (Icc a b ×ˢ Icc c d)) :=
    isFiniteMeasure_restrict.mpr (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have hfmeas : AEStronglyMeasurable f (volume.restrict (Ioo a b ×ˢ Ioo c d)) := by
    rw [rectangle_restrict_Ioo_eq_Icc]
    exact hf.aestronglyMeasurable
  obtain ⟨Gx, hGx, hrx⟩ := exists_measurable_horizontal_derivative f hfmeas hacx
  obtain ⟨Gy, hGy, hry⟩ := exists_measurable_vertical_derivative f hfmeas hacy
  have hx : ∀ᵐ y ∂volume.restrict (Icc c d), ∀ᵐ x ∂volume.restrict (Icc a b),
      |Gx (x, y)| ≤ ρ (x, y) := by
    filter_upwards [hrx, hbx] with y hy hb
    filter_upwards [hy, hb] with x hx hb
    simpa only [hx] using hb
  have hy : ∀ᵐ x ∂volume.restrict (Icc a b), ∀ᵐ y ∂volume.restrict (Icc c d),
      |Gy (x, y)| ≤ ρ (x, y) := by
    filter_upwards [hry, hby] with x hx hb
    filter_upwards [hx, hb] with y hy hb
    simpa only [hy] using hb
  have hmeasx : MeasurableSet {p : ℝ × ℝ | |Gx p| ≤ ρ p} :=
    by simpa only [Real.norm_eq_abs] using measurableSet_le hGx.norm hρ
  have hmeasy : MeasurableSet {p : ℝ × ℝ | |Gy p| ≤ ρ p} :=
    by simpa only [Real.norm_eq_abs] using measurableSet_le hGy.norm hρ
  have hBx : ∀ᵐ p ∂volume.restrict (Icc a b ×ˢ Icc c d), |Gx p| ≤ ρ p := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact (Measure.ae_prod_iff_ae_ae hmeasx).2 ((Measure.ae_ae_comm hmeasx).2 hx)
  have hBy : ∀ᵐ p ∂volume.restrict (Icc a b ×ˢ Icc c d), |Gy p| ≤ ρ p := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact (Measure.ae_prod_iff_ae_ae hmeasy).2 hy
  have hx₂ : MemLp Gx 2 (volume.restrict (Icc a b ×ˢ Icc c d)) :=
    hρ₂.of_le hGx.aestronglyMeasurable (hBx.mono fun p hp => by
      simpa only [Real.norm_eq_abs] using hp.trans (le_abs_self _))
  have hy₂ : MemLp Gy 2 (volume.restrict (Icc a b ×ˢ Icc c d)) :=
    hρ₂.of_le hGy.aestronglyMeasurable (hBy.mono fun p hp => by
      simpa only [Real.norm_eq_abs] using hp.trans (le_abs_self _))
  refine ⟨Gx, Gy, hGx, hGy, hx₂, hy₂, hBx.and hBy, ?_⟩
  intro φ hφ hs hsub
  exact ⟨integral_mul_horizontal_deriv_eq_neg hab (hf.integrable (by norm_num))
    (hx₂.integrable (by norm_num)) hacx hrx hφ hs hsub,
    integral_mul_vertical_deriv_eq_neg hcd (hf.integrable (by norm_num))
    (hy₂.integrable (by norm_num)) hacy hry hφ hs hsub⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PlanarSobolevTransport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport the actual planar weak derivative identities to the
Euclidean coordinates of the repository's Sobolev approximation library. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem weakPartial_of_planar_identity
    {f G : ℝ × ℝ → ℝ} {a b c d : ℝ} (i : Fin 2) (v : ℝ × ℝ)
    (hv : euclideanPlaneCoordinates (EuclideanSpace.single i 1) = v)
    (hweak : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b ×ˢ Ioo c d →
      (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ ψ p) v) =
        -(∫p in Icc a b ×ˢ Icc c d, G p * ψ p)) :
    DeGiorgi.HasWeakPartialDeriv i (G ∘ euclideanPlaneCoordinates)
      (f ∘ euclideanPlaneCoordinates)
      (euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c d)) := by
  intro φ hφ hs hsub
  let e := euclideanPlaneCoordinates
  change (∫x in e ⁻¹' (Ioo a b ×ˢ Ioo c d),
    f (e x) * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) =
      -(∫x in e ⁻¹' (Ioo a b ×ˢ Ioo c d), G (e x) * φ x)
  change e (EuclideanSpace.single i 1) = v at hv
  let ψ : ℝ × ℝ → ℝ := φ ∘ e.symm
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp e.symm.contDiff
  have hsψ : HasCompactSupport ψ := hs.comp_homeomorph e.symm.toHomeomorph
  have hsubψ : tsupport ψ ⊆ Ioo a b ×ˢ Ioo c d := by
    change tsupport (φ ∘ e.symm.toHomeomorph) ⊆ _
    rw [tsupport_comp_eq_preimage]
    intro p hp
    have hh := hsub hp
    change e (e.symm p) ∈ Ioo a b ×ˢ Ioo c d at hh
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hh
  have hd (p : ℝ × ℝ) :
      (fderiv ℝ ψ p) v = (fderiv ℝ φ (e.symm p)) (EuclideanSpace.single i 1) := by
    rw [fderiv_comp p (hφ.differentiable (by simp)).differentiableAt e.symm.differentiableAt,
      e.symm.fderiv]
    change (fderiv ℝ φ (e.symm p)) (e.symm v) = _
    rw [← hv, ContinuousLinearEquiv.symm_apply_apply]
  have hp := hweak ψ hψ hsψ hsubψ
  rw [← rectangle_restrict_Ioo_eq_Icc] at hp
  have hmp : MeasurePreserving e (volume.restrict (e ⁻¹' (Ioo a b ×ˢ Ioo c d)))
      (volume.restrict (Ioo a b ×ˢ Ioo c d)) :=
    euclideanPlaneCoordinates_measurePreserving.restrict_preimage
      (isOpen_Ioo.prod isOpen_Ioo).measurableSet
  calc
    _ = ∫x in e ⁻¹' (Ioo a b ×ˢ Ioo c d), f (e x) * (fderiv ℝ ψ (e x)) v := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by simp only [hd,
        ContinuousLinearEquiv.symm_apply_apply]
    _ = ∫p in Ioo a b ×ˢ Ioo c d, f p * (fderiv ℝ ψ p) v :=
      hmp.integral_comp e.toHomeomorph.measurableEmbedding
        (fun p => f p * (fderiv ℝ ψ p) v)
    _ = -(∫p in Ioo a b ×ˢ Ioo c d, G p * ψ p) := hp
    _ = _ := by
      rw [← hmp.integral_comp e.toHomeomorph.measurableEmbedding (fun p => G p * ψ p)]
      simp only [ψ, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeightedSobolevTransport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Preserve a common pointwise derivative bound when transporting rectangle
weak derivatives into the Euclidean Sobolev witness. -/

open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

theorem exists_bounded_rectangle_sobolev_witness
    {f Gx Gy r : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hf : MemLp f 2 (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hx : MemLp Gx 2 (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hy : MemLp Gy 2 (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hbound : ∀ᵐ p ∂volume.restrict (Icc a b ×ˢ Icc c d),
      |Gx p| ≤ r p ∧ |Gy p| ≤ r p)
    (hweak : ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ioo c d →
      (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ φ p) (1, 0)) =
        -(∫p in Icc a b ×ˢ Icc c d, Gx p * φ p) ∧
      (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ φ p) (0, 1)) =
        -(∫p in Icc a b ×ˢ Icc c d, Gy p * φ p)) :
    ∃H : DeGiorgi.MemW1pWitness 2 (f ∘ euclideanPlaneCoordinates)
        (euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c d)),
      ∀i : Fin 2, ∀ᵐ x ∂volume.restrict
        (euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c d)),
        |H.weakGrad x i| ≤ r (euclideanPlaneCoordinates x) := by
  let W := Ioo a b ×ˢ Ioo c d
  have hmp := euclideanPlaneCoordinates_measurePreserving.restrict_preimage (s := W)
    (isOpen_Ioo.prod isOpen_Ioo).measurableSet
  have hf' : MemLp f 2 (volume.restrict W) := by rwa [rectangle_restrict_Ioo_eq_Icc]
  have hx' : MemLp Gx 2 (volume.restrict W) := by rwa [rectangle_restrict_Ioo_eq_Icc]
  have hy' : MemLp Gy 2 (volume.restrict W) := by rwa [rectangle_restrict_Ioo_eq_Icc]
  have hb' : ∀ᵐ p ∂volume.restrict W, |Gx p| ≤ r p ∧ |Gy p| ≤ r p := by
    rwa [rectangle_restrict_Ioo_eq_Icc]
  let G : EuclideanPlane → EuclideanPlane := fun x =>
    WithLp.toLp 2 fun i => if i = 0 then Gx (euclideanPlaneCoordinates x)
      else Gy (euclideanPlaneCoordinates x)
  let H : DeGiorgi.MemW1pWitness 2 (f ∘ euclideanPlaneCoordinates)
      (euclideanPlaneCoordinates ⁻¹' W) := {
    memLp := hf'.comp_measurePreserving hmp
    weakGrad := G
    weakGrad_component_memLp := by
      intro i
      fin_cases i
      · exact hx'.comp_measurePreserving hmp
      · exact hy'.comp_measurePreserving hmp
    isWeakGrad := by
      intro i
      fin_cases i
      · exact weakPartial_of_planar_identity 0 (1, 0) euclideanPlaneCoordinates_single_zero
          (fun φ hφ hs hsub => (hweak φ hφ hs hsub).1)
      · exact weakPartial_of_planar_identity 1 (0, 1) euclideanPlaneCoordinates_single_one
          (fun φ hφ hs hsub => (hweak φ hφ hs hsub).2) }
  refine ⟨H, ?_⟩
  intro i
  have hb := hmp.quasiMeasurePreserving.ae hb'
  filter_upwards [hb] with x hx
  fin_cases i
  · exact hx.1
  · exact hx.2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_CountableTraceEnumeration
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enumerate a countable family without repetitions. Missing natural
codes carry zero radii, so empty and finite families use the same bounds. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

 theorem traceEnumeration_encode {ι E : Type*} [Encodable ι] (v : ι → E) (e : E) (i : ι) :
    traceEnumeration v e (Encodable.encode i) = v i :=
  Encodable.encode_injective.extend_apply v (fun _ => e) i

 theorem traceEnumeration_missing {ι E : Type*} [Encodable ι] (v : ι → E) (e : E)
    {n : ℕ} (hn : n ∉ Set.range (Encodable.encode : ι → ℕ)) : traceEnumeration v e n = e :=
  Function.extend_apply' v (fun _ => e) n hn

 theorem traceEnumeration_nonneg {ι : Type*} [Encodable ι] {v : ι → ℝ}
    (hv : ∀ i, 0 ≤ v i) : ∀ n, 0 ≤ traceEnumeration v 0 n := by
  intro n
  by_cases hn : n ∈ Set.range (Encodable.encode : ι → ℕ)
  · obtain ⟨i,rfl⟩ := hn
    rw [traceEnumeration_encode]
    exact hv i
  · rw [traceEnumeration_missing v 0 hn]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_FiniteTraceMask
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite lower-envelope masks for the common-point trace argument.
The variation is paid only on intervals in which the corresponding cutoff
is active. These estimates precede the Sobolev and infinite-mask limits. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] Classical.propDecidable

 theorem finiteTraceMask_bounds {X : Type*} {cutoff : ℕ → X → ℝ}
    (hcutoff : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) (I : ℕ → Set ℝ) (x : X) (t : ℝ) (n : ℕ) :
    finiteTraceMask cutoff I x t n ∈ Icc (0:ℝ) 1 := by
  induction n with
  | zero => exact ⟨zero_le_one,le_rfl⟩
  | succ n ih =>
    simp only [finiteTraceMask,mem_Icc]
    constructor
    · apply le_min ih.1
      split_ifs
      · exact (hcutoff n x).1
      · exact zero_le_one
    · exact (min_le_left _ _).trans ih.2

 theorem finiteTraceMask_antitone {X : Type*} (cutoff : ℕ → X → ℝ) (I : ℕ → Set ℝ)
    (x : X) (t : ℝ) : Antitone (finiteTraceMask cutoff I x t) := by
  apply antitone_nat_of_succ_le
  intro n
  exact min_le_left _ _

 theorem finiteTraceMask_le_active {X : Type*} {cutoff : ℕ → X → ℝ} {I : ℕ → Set ℝ}
    {x : X} {t : ℝ} {j n : ℕ} (hj : j < n) (ht : t ∈ I j) :
    finiteTraceMask cutoff I x t n ≤ cutoff j x := by
  have he : finiteTraceMask cutoff I x t (j+1) ≤ cutoff j x := by
    simpa only [finiteTraceMask,ite_eq_left ht] using
      min_le_right (finiteTraceMask cutoff I x t j) (cutoff j x)
  exact ((finiteTraceMask_antitone cutoff I x t) hj).trans he

 theorem finiteTraceMask_zero_of_active {X : Type*} {cutoff : ℕ → X → ℝ}
    (hcutoff : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    {x : X} {t : ℝ} {j n : ℕ} (hj : j < n) (ht : t ∈ I j) (hz : cutoff j x = 0) :
    finiteTraceMask cutoff I x t n = 0 := by
  apply le_antisymm
  · simpa only [hz] using finiteTraceMask_le_active (cutoff := cutoff) (x := x) hj ht
  · exact (finiteTraceMask_bounds hcutoff I x t n).1

 theorem finiteTraceMask_variation {X : Type*} (cutoff : ℕ → X → ℝ) (I : ℕ → Set ℝ)
    (x y : X) (t : ℝ) (n : ℕ) :
    |finiteTraceMask cutoff I x t n-finiteTraceMask cutoff I y t n| ≤
      ∑ j ∈ Finset.range n, (I j).indicator (fun _ => |cutoff j x-cutoff j y|) t := by
  induction n with
  | zero => simp [finiteTraceMask]
  | succ n ih =>
    have hs : 0 ≤ ∑ j ∈ Finset.range n, (I j).indicator (fun _ => |cutoff j x-cutoff j y|) t :=
      Finset.sum_nonneg (fun j _ => indicator_nonneg (fun _ _ => abs_nonneg _) t)
    rw [finiteTraceMask,finiteTraceMask,Finset.sum_range_succ]
    have hh := abs_min_sub_min_le_max (finiteTraceMask cutoff I x t n)
      (if t ∈ I n then cutoff n x else 1) (finiteTraceMask cutoff I y t n)
      (if t ∈ I n then cutoff n y else 1)
    apply hh.trans
    apply max_le
    · apply ih.trans
      exact le_add_of_nonneg_right (indicator_nonneg (fun _ _ => abs_nonneg _) _)
    · by_cases ht : t ∈ I n
      · simp only [ite_eq_left ht,indicator_of_mem ht]
        exact le_add_of_nonneg_left hs
      · simp only [ite_eq_right ht,sub_self,abs_zero,indicator_of_notMem ht,add_zero]
        exact hs

 theorem finiteTraceMask_measurable {X : Type*} (cutoff : ℕ → X → ℝ) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (x : X) (n : ℕ) :
    Measurable (fun t => finiteTraceMask cutoff I x t n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact ih.min (Measurable.ite (hI n) measurable_const measurable_const)

 theorem finiteTraceMask_tendsto {X : Type*} {cutoff : ℕ → X → ℝ}
    (hcutoff : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) (I : ℕ → Set ℝ) (x : X) (t : ℝ) :
    Tendsto (finiteTraceMask cutoff I x t) atTop (𝓝 (infiniteTraceMask cutoff I x t)) := by
  apply tendsto_atTop_ciInf (finiteTraceMask_antitone cutoff I x t)
  exact ⟨0,fun _ ⟨n,hn⟩ => hn ▸ (finiteTraceMask_bounds hcutoff I x t n).1⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceMaskPrimitive
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integral primitives of the actual finite and infinite trace masks.
The finite spatial variation is bounded by interval lengths times cutoff
variation, while endpoint changes are always one-Lipschitz. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem finiteTraceMask_norm_le {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) (I : ℕ → Set ℝ) (x : X) (s : ℝ) (n : ℕ) :
    ‖finiteTraceMask cutoff I x s n‖ ≤ 1 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (finiteTraceMask_bounds hc I x s n).1]
  exact (finiteTraceMask_bounds hc I x s n).2

 theorem finiteTraceMask_intervalIntegrable {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (x : X) (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun s => finiteTraceMask cutoff I x s n) volume a b := by
  apply intervalIntegrable_iff.mpr
  exact (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a b).def'.mono'
    ((finiteTraceMask_measurable cutoff hI x n).aestronglyMeasurable.restrict)
    (Eventually.of_forall (fun s => finiteTraceMask_norm_le hc I x s n))

 theorem finiteTracePrimitive_sub {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (x : X) (n : ℕ) (a s t : ℝ) :
    finiteTracePrimitive cutoff I a x t n-finiteTracePrimitive cutoff I a x s n =
      ∫ u in s..t, finiteTraceMask cutoff I x u n :=
  intervalIntegral.integral_interval_sub_left
    (finiteTraceMask_intervalIntegrable hc hI x n a t)
    (finiteTraceMask_intervalIntegrable hc hI x n a s)

 theorem finiteTracePrimitive_lipschitz {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (x : X) (n : ℕ) (a : ℝ) :
    LipschitzWith 1 (fun t => finiteTracePrimitive cutoff I a x t n) := by
  apply LipschitzWith.of_dist_le_mul
  intro t s
  rw [Real.dist_eq,Real.dist_eq,← Real.norm_eq_abs,finiteTracePrimitive_sub hc hI]
  simpa only [NNReal.coe_one,one_mul] using
    intervalIntegral.norm_integral_le_of_norm_le_const (C := 1) (a := s) (b := t)
      (fun u _ => finiteTraceMask_norm_le hc I x u n)

 theorem finiteTracePrimitive_variation {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    (x y : X) (a t : ℝ) (n : ℕ) :
    |finiteTracePrimitive cutoff I a x t n-finiteTracePrimitive cutoff I a y t n| ≤
      ∑ j ∈ Finset.range n, volume.real (I j)*|cutoff j x-cutoff j y| := by
  let p := fun s => ∑ j ∈ Finset.range n, (I j).indicator (fun _ => |cutoff j x-cutoff j y|) s
  have hi (j : ℕ) : Integrable ((I j).indicator (fun _ => |cutoff j x-cutoff j y|)) volume :=
    (integrableOn_const (hIf j)).integrable_indicator (hI j)
  have hp : Integrable p volume := integrable_finsetSum _ (fun j _ => hi j)
  have hp0 (s : ℝ) : 0 ≤ p s :=
    Finset.sum_nonneg (fun j _ => indicator_nonneg (fun _ _ => abs_nonneg _) s)
  rw [finiteTracePrimitive,finiteTracePrimitive,← intervalIntegral.integral_sub
    (finiteTraceMask_intervalIntegrable hc hI x n a t)
    (finiteTraceMask_intervalIntegrable hc hI y n a t),← Real.norm_eq_abs]
  calc
    _ ≤ ∫ s in uIoc a t, ‖finiteTraceMask cutoff I x s n-finiteTraceMask cutoff I y s n‖ :=
      intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ s in uIoc a t, p s := integral_mono_of_nonneg
      (Eventually.of_forall (fun _ => norm_nonneg _)) hp.restrict
      (Eventually.of_forall (fun s => by
        simpa only [Real.norm_eq_abs] using finiteTraceMask_variation cutoff I x y s n))
    _ ≤ ∫ s, p s := integral_mono_measure Measure.restrict_le_self (Eventually.of_forall hp0) hp
    _ = _ := by
      rw [integral_finsetSum _ (fun j _ => hi j)]
      apply Finset.sum_congr rfl
      intro j _
      exact integral_indicator_const _ (hI j)

 theorem infiniteTraceMask_bounds {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) (I : ℕ → Set ℝ) (x : X) (s : ℝ) :
    infiniteTraceMask cutoff I x s ∈ Icc (0:ℝ) 1 :=
  isClosed_Icc.mem_of_tendsto (finiteTraceMask_tendsto hc I x s)
    (Eventually.of_forall (fun n => finiteTraceMask_bounds hc I x s n))

 theorem finiteTracePrimitive_tendsto {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (x : X) (a t : ℝ) :
    Tendsto (fun n => finiteTracePrimitive cutoff I a x t n) atTop
      (𝓝 (infiniteTracePrimitive cutoff I a x t)) := by
  have ht : Tendsto (fun n => ∫ s in uIoc a t, finiteTraceMask cutoff I x s n) atTop
      (𝓝 (∫ s in uIoc a t, infiniteTraceMask cutoff I x s)) :=
    tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => (finiteTraceMask_measurable cutoff hI x n).aestronglyMeasurable.restrict)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a t).def'
      (fun n => Eventually.of_forall (fun s => finiteTraceMask_norm_le hc I x s n))
      (Eventually.of_forall (fun s => finiteTraceMask_tendsto hc I x s))
  simpa only [finiteTracePrimitive,infiniteTracePrimitive,
    intervalIntegral.intervalIntegral_eq_integral_uIoc] using
    ht.const_smul (if a ≤ t then (1 : ℝ) else -1)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceMaskTail
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A tail which is inactive outside one scalar interval changes the
entire primitive by at most that interval's length. This is the local
finite approximation used at accumulating common-point components. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] Classical.propDecidable

 theorem infiniteTraceMask_measurable {X : Type*} (cutoff : ℕ → X → ℝ)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (x : X) :
    Measurable (infiniteTraceMask cutoff I x) :=
  Measurable.iInf (fun n => finiteTraceMask_measurable cutoff hI x n)

 theorem infiniteTraceMask_intervalIntegrable {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (x : X) (a b : ℝ) :
    IntervalIntegrable (infiniteTraceMask cutoff I x) volume a b := by
  apply intervalIntegrable_iff.mpr
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a b).def'.mono'
    ((infiniteTraceMask_measurable cutoff hI x).aestronglyMeasurable.restrict)
  apply Eventually.of_forall
  intro s
  rw [Real.norm_eq_abs,abs_of_nonneg (infiniteTraceMask_bounds hc I x s).1]
  exact (infiniteTraceMask_bounds hc I x s).2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TracePrimitiveContinuity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint continuity of finite primitives follows from the explicit
finite variation bound. Uniformly small scalar tails then prove the
continuity of the actual infinite masked scalar at a common point. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem finiteTracePrimitive_continuous {X : Type*} [TopologicalSpace X]
    {cutoff : ℕ → X → ℝ} (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1)
    (hcc : ∀ j, Continuous (cutoff j)) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    (a : ℝ) (n : ℕ) :
    Continuous (fun p : X × ℝ => finiteTracePrimitive cutoff I a p.1 p.2 n) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let B := fun q : X × ℝ => |q.2-p.2|+
    ∑ j ∈ Finset.range n, volume.real (I j)*|cutoff j q.1-cutoff j p.1|
  have hB : Continuous B := by dsimp only [B]; fun_prop
  have hB0 : B p = 0 := by simp [B]
  have hb : Tendsto B (𝓝 p) (𝓝 0) := hB0 ▸ hB.continuousAt.tendsto
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) _ hb
  intro q
  calc
    _ ≤ dist (finiteTracePrimitive cutoff I a q.1 q.2 n)
          (finiteTracePrimitive cutoff I a q.1 p.2 n)+
        dist (finiteTracePrimitive cutoff I a q.1 p.2 n)
          (finiteTracePrimitive cutoff I a p.1 p.2 n) := dist_triangle _ _ _
    _ ≤ B q := by
      apply add_le_add
      · simpa only [NNReal.coe_one,one_mul,Real.dist_eq] using
          (finiteTracePrimitive_lipschitz hc hI q.1 n a).dist_le_mul q.2 p.2
      · simpa only [Real.dist_eq] using finiteTracePrimitive_variation hc hI hIf q.1 p.1 a p.2 n

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TracePrimitivePlateau
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On an indexed component neighborhood an active zero cutoff fixes the
upper endpoint of the primitive. Late intervals absorbed by that same
zero interval have no effect, so the infinite masked scalar is locally
an actual finite continuous primitive, even when the raw scalar jumps. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem infiniteTraceMask_zero_of_active {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    {x : X} {t : ℝ} {j : ℕ} (ht : t ∈ I j) (hz : cutoff j x = 0) :
    infiniteTraceMask cutoff I x t = 0 := by
  apply tendsto_nhds_unique (finiteTraceMask_tendsto hc I x t)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop j] with n hn
  exact (finiteTraceMask_zero_of_active hc hn ht hz).symm

 theorem infiniteTracePrimitive_plateau {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) {x : X} {j : ℕ}
    (hconv : OrdConnected (I j)) (hz : cutoff j x = 0) {s t : ℝ}
    (hs : s ∈ I j) (ht : t ∈ I j) (a : ℝ) :
    infiniteTracePrimitive cutoff I a x s = infiniteTracePrimitive cutoff I a x t := by
  apply sub_eq_zero.mp
  rw [infiniteTracePrimitive,infiniteTracePrimitive,
    intervalIntegral.integral_interval_sub_left
      (infiniteTraceMask_intervalIntegrable hc hI x a s)
      (infiniteTraceMask_intervalIntegrable hc hI x a t)]
  calc
    _ = ∫ u in t..s, (0 : ℝ) := intervalIntegral.integral_congr (fun u hu =>
      infiniteTraceMask_zero_of_active hc (hconv.uIcc_subset ht hs hu) hz)
    _ = 0 := by simp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceMaskLinePayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual mask primitive inherits line payment from its scalar
cutoffs. Finite interval-length sums are dominated by the density before
passing to the infinite mask; no differentiability of minima is used. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem infiniteTracePrimitive_lipschitz {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (x : X) (a : ℝ) :
    LipschitzWith 1 (infiniteTracePrimitive cutoff I a x) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  apply le_of_tendsto (show Tendsto (fun n =>
      dist (finiteTracePrimitive cutoff I a x s n) (finiteTracePrimitive cutoff I a x t n))
      atTop (𝓝 (dist (infiniteTracePrimitive cutoff I a x s)
        (infiniteTracePrimitive cutoff I a x t))) from
    (finiteTracePrimitive_tendsto hc hI x a s).dist (finiteTracePrimitive_tendsto hc hI x a t))
  exact Eventually.of_forall (fun n => (finiteTracePrimitive_lipschitz hc hI x n a).dist_le_mul s t)

 theorem masked_scalar_increment
    {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (a : ℝ) (b : X → ℝ) {x y : X} {c : ℝ}
    (hfix : ∀ t, |infiniteTracePrimitive cutoff I a x t-infiniteTracePrimitive cutoff I a y t| ≤ c) :
    |infiniteTracePrimitive cutoff I a x (b x)-infiniteTracePrimitive cutoff I a y (b y)| ≤
      |b x-b y|+c := by
  calc
    _ ≤ |infiniteTracePrimitive cutoff I a x (b x)-infiniteTracePrimitive cutoff I a x (b y)|+
        |infiniteTracePrimitive cutoff I a x (b y)-infiniteTracePrimitive cutoff I a y (b y)| :=
      abs_sub_le _ _ _
    _ ≤ |b x-b y|+c := add_le_add (by
      simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using
        (infiniteTracePrimitive_lipschitz hc hI x a).dist_le_mul (b x) (b y)) (hfix (b y))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceMaskAEPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial payment needs only an almost-everywhere density bound. This
version applies to the actual L² sum furnished by ball synthesis. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem trace_primitive_line_payment_ae
    {cutoff : ℕ → ℝ → ℝ} (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    {g : ℕ → ℝ → ℝ} {P : ℝ → ℝ} {L R : ℝ}
    (hg : ∀ j, IntervalIntegrable (g j) volume L R) (hP : IntervalIntegrable P volume L R)
    (hcut : ∀ j, ∀ x ∈ uIcc L R, ∀ y ∈ uIcc L R,
      |cutoff j x-cutoff j y| ≤ ∫ s in uIoc x y, g j s)
    (hdom : ∀ n, ∀ᵐ s ∂volume.restrict (uIoc L R),
      ∑ j ∈ Finset.range n, volume.real (I j)*g j s ≤ P s)
    (a t : ℝ) {x y : ℝ} (hx : x ∈ uIcc L R) (hy : y ∈ uIcc L R) :
    |infiniteTracePrimitive cutoff I a x t-infiniteTracePrimitive cutoff I a y t| ≤
      ∫ s in uIoc x y, P s := by
  have hsub : uIoc x y ⊆ uIoc L R :=
    uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc hx hy)
  have hg' (j : ℕ) : IntegrableOn (g j) (uIoc x y) volume := (hg j).def'.mono_set hsub
  have hP' : IntegrableOn P (uIoc x y) volume := hP.def'.mono_set hsub
  have hfinite (n : ℕ) :
      |finiteTracePrimitive cutoff I a x t n-finiteTracePrimitive cutoff I a y t n| ≤
        ∫ s in uIoc x y, P s := by
    apply (finiteTracePrimitive_variation hc hI hIf x y a t n).trans
    calc
      _ ≤ ∑ j ∈ Finset.range n, volume.real (I j)*(∫ s in uIoc x y, g j s) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hcut j x hx y hy) (measureReal_nonneg)
      _ = ∫ s in uIoc x y, ∑ j ∈ Finset.range n, volume.real (I j)*g j s := by
        rw [integral_finsetSum _ (fun j _ => (hg' j).const_mul _)]
        exact Finset.sum_congr rfl (fun j _ => (integral_const_mul _ _).symm)
      _ ≤ ∫ s in uIoc x y, P s := by
        apply integral_mono_ae (integrable_finsetSum _ (fun j _ => (hg' j).const_mul _)) hP'
        exact ae_restrict_of_ae_restrict_of_subset hsub (hdom n)
  exact le_of_tendsto
    (((finiteTracePrimitive_tendsto hc hI x a t).sub
      (finiteTracePrimitive_tendsto hc hI y a t)).abs)
    (Eventually.of_forall hfinite)

 theorem masked_scalar_ACL_of_line_payment_ae
    {cutoff : ℕ → ℝ → ℝ} (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    {g : ℕ → ℝ → ℝ} {P Q b : ℝ → ℝ} {L R : ℝ}
    (hg : ∀ j, IntervalIntegrable (g j) volume L R)
    (hP : IntervalIntegrable P volume L R) (hQ : IntervalIntegrable Q volume L R)
    (hcut : ∀ j, ∀ x ∈ uIcc L R, ∀ y ∈ uIcc L R,
      |cutoff j x-cutoff j y| ≤ ∫ s in uIoc x y, g j s)
    (hdom : ∀ n, ∀ᵐ s ∂volume.restrict (uIoc L R),
      ∑ j ∈ Finset.range n, volume.real (I j)*g j s ≤ P s)
    (hb : ∀ x ∈ uIcc L R, ∀ y ∈ uIcc L R, |b x-b y| ≤ ∫ s in uIoc x y, Q s)
    (a : ℝ) : AbsolutelyContinuousOnInterval
      (fun x => infiniteTracePrimitive cutoff I a x (b x)) L R := by
  apply absolutelyContinuousOnInterval_of_integral_bound (hQ.add hP)
  intro x hx y hy
  rw [Real.dist_eq,integral_add (hQ.def'.mono_set
    (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc hx hy)))
    (hP.def'.mono_set (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc hx hy)))]
  exact (masked_scalar_increment hc hI a b (fun t =>
    trace_primitive_line_payment_ae hc hI hIf hg hP hcut hdom a t hx hy)).trans
    (add_le_add (hb x hx y hy) le_rfl)

 theorem masked_scalar_derivative_of_line_payment_ae
    {cutoff : ℕ → ℝ → ℝ} (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    {g : ℕ → ℝ → ℝ} {P Q b : ℝ → ℝ} {L R : ℝ} (hLR : L ≤ R)
    (hg : ∀ j, IntervalIntegrable (g j) volume L R)
    (hP : IntervalIntegrable P volume L R) (hQ : IntervalIntegrable Q volume L R)
    (hnonneg : ∀ᵐ x ∂volume.restrict (Icc L R), 0 ≤ Q x+P x)
    (hcut : ∀ j, ∀ x ∈ uIcc L R, ∀ y ∈ uIcc L R,
      |cutoff j x-cutoff j y| ≤ ∫ s in uIoc x y, g j s)
    (hdom : ∀ n, ∀ᵐ s ∂volume.restrict (uIoc L R),
      ∑ j ∈ Finset.range n, volume.real (I j)*g j s ≤ P s)
    (hb : ∀ x ∈ uIcc L R, ∀ y ∈ uIcc L R, |b x-b y| ≤ ∫ s in uIoc x y, Q s)
    (a : ℝ) : ∀ᵐ x ∂volume.restrict (Icc L R),
      |deriv (fun x => infiniteTracePrimitive cutoff I a x (b x)) x| ≤ Q x+P x := by
  apply ae_abs_deriv_le_of_integral_bound hLR (hQ.add hP) hnonneg
  intro x hx y hy
  have hx' : x ∈ uIcc L R := by simpa only [uIcc_of_le hLR] using hx
  have hy' : y ∈ uIcc L R := by simpa only [uIcc_of_le hLR] using hy
  rw [integral_add (hQ.def'.mono_set
    (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc hx' hy')))
    (hP.def'.mono_set (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc hx' hy')))]
  exact (masked_scalar_increment hc hI a b (fun t =>
    trace_primitive_line_payment_ae hc hI hIf hg hP hcut hdom a t hx' hy')).trans
    (add_le_add (hb x hx' y hy') le_rfl)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TracePrimitiveMeasurability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability and a uniform bound for the actual infinite primitive;
the raw endpoint only needs to be measurable. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem finiteTraceMask_comp {X Y : Type*} (cutoff : ℕ → X → ℝ)
    (I : ℕ → Set ℝ) (φ : Y → X) (y : Y) (t : ℝ) (n : ℕ) :
    finiteTraceMask (fun j z => cutoff j (φ z)) I y t n =
      finiteTraceMask cutoff I (φ y) t n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [finiteTraceMask,ih]

 theorem infiniteTraceMask_comp {X Y : Type*} (cutoff : ℕ → X → ℝ)
    (I : ℕ → Set ℝ) (φ : Y → X) (y : Y) (t : ℝ) :
    infiniteTraceMask (fun j z => cutoff j (φ z)) I y t =
      infiniteTraceMask cutoff I (φ y) t := by
  simp only [infiniteTraceMask,finiteTraceMask_comp]

 theorem infiniteTracePrimitive_comp {X Y : Type*} (cutoff : ℕ → X → ℝ)
    (I : ℕ → Set ℝ) (φ : Y → X) (a : ℝ) (y : Y) (t : ℝ) :
    infiniteTracePrimitive (fun j z => cutoff j (φ z)) I a y t =
      infiniteTracePrimitive cutoff I a (φ y) t := by
  simp only [infiniteTracePrimitive,infiniteTraceMask_comp]

 theorem infinite_masked_scalar_measurable {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) (hcc : ∀ j, Continuous (cutoff j))
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j))
    (hIf : ∀ j, volume (I j) ≠ ∞) {b : X → ℝ} (hb : Measurable b) (a : ℝ) :
    Measurable (fun x => infiniteTracePrimitive cutoff I a x (b x)) := by
  apply measurable_of_tendsto_metrizable
    (f := fun n x => finiteTracePrimitive cutoff I a x (b x) n)
  · intro n
    exact (finiteTracePrimitive_continuous hc hcc hI hIf a n).measurable.comp
      (measurable_id.prodMk hb)
  · exact tendsto_pi_nhds.mpr (fun x => finiteTracePrimitive_tendsto hc hI x a (b x))

 theorem infiniteTracePrimitive_norm_le {X : Type*} {cutoff : ℕ → X → ℝ}
    (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (a : ℝ) (x : X) (t : ℝ) :
    ‖infiniteTracePrimitive cutoff I a x t‖ ≤ ‖t-a‖ := by
  simpa only [infiniteTracePrimitive,intervalIntegral.integral_same,dist_zero_right,
    NNReal.coe_one,one_mul,Real.dist_eq,Real.norm_eq_abs] using
    (infiniteTracePrimitive_lipschitz hc hI x a).dist_le_mul t a

 theorem infinite_masked_scalar_memLp {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {cutoff : ℕ → X → ℝ} (hc : ∀ j x, cutoff j x ∈ Icc (0:ℝ) 1)
    (hcc : ∀ j, Continuous (cutoff j)) {I : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    {b : X → ℝ} (hbm : Measurable b) (hb : MemLp b 2 μ) (a : ℝ) :
    MemLp (fun x => infiniteTracePrimitive cutoff I a x (b x)) 2 μ := by
  apply (hb.sub (memLp_const a)).of_le
    (infinite_masked_scalar_measurable hc hcc hI hIf hbm a).aestronglyMeasurable
  exact Eventually.of_forall (fun x => infiniteTracePrimitive_norm_le hc hI a x (b x))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RectangleSliceData
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fubini data for a single rectangle, retaining the actual measurable
predicate and the actual L² density on almost every coordinate line. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem rectangle_ae_slices {a b c d : ℝ} {P : ℝ × ℝ → Prop}
    (hP : MeasurableSet {p | P p})
    (hae : ∀ᵐ p ∂volume.restrict (Icc a b ×ˢ Icc c d), P p) :
    (∀ᵐ y ∂volume.restrict (Icc c d), ∀ᵐ x ∂volume.restrict (Icc a b), P (x,y)) ∧
    (∀ᵐ x ∂volume.restrict (Icc a b), ∀ᵐ y ∂volume.restrict (Icc c d), P (x,y)) := by
  rw [Measure.volume_eq_prod,← Measure.prod_restrict] at hae
  have h := (Measure.ae_prod_iff_ae_ae hP).mp hae
  exact ⟨(Measure.ae_ae_comm hP).mp h,h⟩

 theorem rectangle_L2_line_integrable {P : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hP : MemLp P 2 (volume.restrict (Icc a b ×ˢ Icc c d))) :
    (∀ᵐ y ∂volume.restrict (Icc c d),
      IntervalIntegrable (fun x => P (x,y)) volume a b) ∧
    (∀ᵐ x ∂volume.restrict (Icc a b),
      IntervalIntegrable (fun y => P (x,y)) volume c d) := by
  let : IsFiniteMeasure (volume.restrict (Icc a b ×ˢ Icc c d) : Measure (ℝ × ℝ)) :=
    isFiniteMeasure_restrict.mpr (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have hi := hP.integrable (by norm_num)
  rw [Measure.volume_eq_prod,← Measure.prod_restrict] at hi
  constructor
  · filter_upwards [hi.prod_left_ae] with y hy
    exact intervalIntegrable_iff.mpr ((show IntegrableOn (fun x => P (x,y)) (Icc a b) volume from hy).mono_set
      (by simpa only [uIoc_of_le hab] using Ioc_subset_Icc_self))
  · filter_upwards [hi.prod_right_ae] with x hx
    exact intervalIntegrable_iff.mpr ((show IntegrableOn (fun y => P (x,y)) (Icc c d) volume from hx).mono_set
      (by simpa only [uIoc_of_le hcd] using Ioc_subset_Icc_self))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceMaskRectangle
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual infinite mask is locally Sobolev wherever its raw scalar
is smooth. The gradient is constructed from line payments and Fubini;
only the square-integrable sum of the actual cutoff gradients is used. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem continuous_memLp_rectangle {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (a b c d : ℝ) : MemLp f 2 (volume.restrict (Icc a b ×ˢ Icc c d)) := by
  let : IsFiniteMeasure (volume.restrict (Icc a b ×ˢ Icc c d) : Measure (ℝ × ℝ)) :=
    isFiniteMeasure_restrict.mpr (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable.restrict C
    ((ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)).mono fun p hp => hC p hp)

 theorem smooth_masked_scalar_rectangle_sobolev
    {cutoff : ℕ → (ℝ × ℝ) → ℝ} (hs : ∀ j, ContDiff ℝ 1 (cutoff j))
    (hc : ∀ j p, cutoff j p ∈ Icc (0:ℝ) 1)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    {b : ℝ × ℝ → ℝ} (hb : ContDiff ℝ 1 b)
    {P : ℝ × ℝ → ℝ} (hPm : Measurable P) (hP0 : ∀ p, 0 ≤ P p)
    {a₁ a₂ b₁ b₂ : ℝ} (ha : a₁ ≤ a₂) (hb' : b₁ ≤ b₂)
    (hP2 : MemLp P 2 (volume.restrict (Icc a₁ a₂ ×ˢ Icc b₁ b₂)))
    (hdom : ∀ n, ∀ᵐ p ∂volume.restrict (Icc a₁ a₂ ×ˢ Icc b₁ b₂),
      ∑ j ∈ Finset.range n, volume.real (I j)*‖fderiv ℝ (cutoff j) p‖ ≤ P p)
    (a : ℝ) :
    ∃ W : DeGiorgi.MemW1pWitness 2
      ((fun p => infiniteTracePrimitive cutoff I a p (b p)) ∘ euclideanPlaneCoordinates)
      (euclideanPlaneCoordinates ⁻¹' (Ioo a₁ a₂ ×ˢ Ioo b₁ b₂)),
      ∀ i : Fin 2, ∀ᵐ z ∂volume.restrict
        (euclideanPlaneCoordinates ⁻¹' (Ioo a₁ a₂ ×ˢ Ioo b₁ b₂)),
        |W.weakGrad z i| ≤ ‖fderiv ℝ b (euclideanPlaneCoordinates z)‖+P (euclideanPlaneCoordinates z) := by
  let U : ℝ × ℝ → ℝ := fun p => infiniteTracePrimitive cutoff I a p (b p)
  let Q : ℝ × ℝ → ℝ := fun p => ‖fderiv ℝ b p‖
  let ρ : ℝ × ℝ → ℝ := fun p => Q p+P p
  have hQc : Continuous Q := (hb.continuous_fderiv (by norm_num)).norm
  have hgc (j : ℕ) : Continuous (fun p => ‖fderiv ℝ (cutoff j) p‖) :=
    ((hs j).continuous_fderiv (by norm_num)).norm
  have hρm : Measurable ρ := hQc.measurable.add hPm
  have hρ2 : MemLp ρ 2 (volume.restrict (Icc a₁ a₂ ×ˢ Icc b₁ b₂)) :=
    (continuous_memLp_rectangle hQc _ _ _ _).add hP2
  let : IsFiniteMeasure (volume.restrict (Icc a₁ a₂ ×ˢ Icc b₁ b₂) : Measure (ℝ × ℝ)) :=
    isFiniteMeasure_restrict.mpr (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have hU2 : MemLp U 2 (volume.restrict (Icc a₁ a₂ ×ˢ Icc b₁ b₂)) :=
    infinite_masked_scalar_memLp hc (fun j => (hs j).continuous) hI hIf hb.continuous.measurable
      (continuous_memLp_rectangle hb.continuous _ _ _ _) a
  have hPi := rectangle_L2_line_integrable ha hb' hP2
  have hD (n : ℕ) := rectangle_ae_slices
    (measurableSet_le (Finset.measurable_sum _ (fun j _ =>
      measurable_const.mul (hgc j).measurable)) hPm) (hdom n)
  have hDx : ∀ᵐ y ∂volume.restrict (Icc b₁ b₂), ∀ n,
      ∀ᵐ x ∂volume.restrict (Icc a₁ a₂),
        ∑ j ∈ Finset.range n, volume.real (I j)*‖fderiv ℝ (cutoff j) (x,y)‖ ≤ P (x,y) :=
    ae_all_iff.mpr (fun n => (hD n).1)
  have hDy : ∀ᵐ x ∂volume.restrict (Icc a₁ a₂), ∀ n,
      ∀ᵐ y ∂volume.restrict (Icc b₁ b₂),
        ∑ j ∈ Finset.range n, volume.real (I j)*‖fderiv ℝ (cutoff j) (x,y)‖ ≤ P (x,y) :=
    ae_all_iff.mpr (fun n => (hD n).2)
  have hx : ∀ᵐ y ∂volume.restrict (Icc b₁ b₂),
      AbsolutelyContinuousOnInterval (fun x => U (x,y)) a₁ a₂ ∧
      ∀ᵐ x ∂volume.restrict (Icc a₁ a₂), |deriv (fun t => U (t,y)) x| ≤ ρ (x,y) := by
    filter_upwards [hPi.1,hDx] with y hiy hdy
    have hg (j : ℕ) : IntervalIntegrable (fun x => ‖fderiv ℝ (cutoff j) (x,y)‖) volume a₁ a₂ :=
      ((hgc j).comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    have hq : IntervalIntegrable (fun x => Q (x,y)) volume a₁ a₂ :=
      (hQc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    have hd (n : ℕ) : ∀ᵐ x ∂volume.restrict (uIoc a₁ a₂),
        ∑ j ∈ Finset.range n, volume.real (I j)*‖fderiv ℝ (cutoff j) (x,y)‖ ≤ P (x,y) :=
      ae_restrict_of_ae_restrict_of_subset (by simpa only [uIoc_of_le ha] using Ioc_subset_Icc_self) (hdy n)
    have hcut : ∀ j, ∀ x ∈ uIcc a₁ a₂, ∀ z ∈ uIcc a₁ a₂,
        |cutoff j (x,y)-cutoff j (z,y)| ≤ ∫ t in uIoc x z, ‖fderiv ℝ (cutoff j) (t,y)‖ :=
      fun j x _ z _ => smooth_horizontal_increment (hs j) y x z
    have hraw : ∀ x ∈ uIcc a₁ a₂, ∀ z ∈ uIcc a₁ a₂,
        |b (x,y)-b (z,y)| ≤ ∫ t in uIoc x z, Q (t,y) :=
      fun x _ z _ => smooth_horizontal_increment hb y x z
    constructor
    · simpa only [U,infiniteTracePrimitive_comp] using
        masked_scalar_ACL_of_line_payment_ae (fun j x => hc j (x,y)) hI hIf hg hiy hq
          hcut hd hraw a
    · simpa only [U,ρ,Q,infiniteTracePrimitive_comp] using
        masked_scalar_derivative_of_line_payment_ae (fun j x => hc j (x,y)) hI hIf ha hg hiy hq
          (Eventually.of_forall fun x => add_nonneg (norm_nonneg _) (hP0 _)) hcut hd hraw a
  have hy : ∀ᵐ x ∂volume.restrict (Icc a₁ a₂),
      AbsolutelyContinuousOnInterval (fun y => U (x,y)) b₁ b₂ ∧
      ∀ᵐ y ∂volume.restrict (Icc b₁ b₂), |deriv (fun t => U (x,t)) y| ≤ ρ (x,y) := by
    filter_upwards [hPi.2,hDy] with x hix hdx
    have hg (j : ℕ) : IntervalIntegrable (fun y => ‖fderiv ℝ (cutoff j) (x,y)‖) volume b₁ b₂ :=
      ((hgc j).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    have hq : IntervalIntegrable (fun y => Q (x,y)) volume b₁ b₂ :=
      (hQc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    have hd (n : ℕ) : ∀ᵐ y ∂volume.restrict (uIoc b₁ b₂),
        ∑ j ∈ Finset.range n, volume.real (I j)*‖fderiv ℝ (cutoff j) (x,y)‖ ≤ P (x,y) :=
      ae_restrict_of_ae_restrict_of_subset (by simpa only [uIoc_of_le hb'] using Ioc_subset_Icc_self) (hdx n)
    have hcut : ∀ j, ∀ y ∈ uIcc b₁ b₂, ∀ z ∈ uIcc b₁ b₂,
        |cutoff j (x,y)-cutoff j (x,z)| ≤ ∫ t in uIoc y z, ‖fderiv ℝ (cutoff j) (x,t)‖ :=
      fun j y _ z _ => smooth_vertical_increment (hs j) x y z
    have hraw : ∀ y ∈ uIcc b₁ b₂, ∀ z ∈ uIcc b₁ b₂,
        |b (x,y)-b (x,z)| ≤ ∫ t in uIoc y z, Q (x,t) :=
      fun y _ z _ => smooth_vertical_increment hb x y z
    constructor
    · simpa only [U,infiniteTracePrimitive_comp] using
        masked_scalar_ACL_of_line_payment_ae (fun j y => hc j (x,y)) hI hIf hg hix hq
          hcut hd hraw a
    · simpa only [U,ρ,Q,infiniteTracePrimitive_comp] using
        masked_scalar_derivative_of_line_payment_ae (fun j y => hc j (x,y)) hI hIf hb' hg hix hq
          (Eventually.of_forall fun y => add_nonneg (norm_nonneg _) (hP0 _)) hcut hd hraw a
  obtain ⟨Gx,Gy,_,_,hGx,hGy,hbound,hweak⟩ := exists_rectangle_weak_gradient ha hb' hU2 hρm hρ2
    (hx.mono fun _ h => h.1) (hy.mono fun _ h => h.1)
    (hx.mono fun _ h => h.2) (hy.mono fun _ h => h.2)
  exact exists_bounded_rectangle_sobolev_witness hU2 hGx hGy hbound hweak

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothRectangleExtension
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth function on a neighborhood of a closed rectangle has a
compactly supported smooth extension agreeing there on an open set. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_rectangle_cutoff_one_near {K Ω : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    ∃ (η : (ℝ × ℝ) → ℝ) (V : Set (ℝ × ℝ)),
      ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧ tsupport η ⊆ Ω ∧
      IsOpen V ∧ K ⊆ V ∧ ∀ x ∈ V, η x = 1 := by
  obtain ⟨δ,hδ,hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  obtain ⟨η,hη,_,hsupp,hone⟩ := exists_contDiff_support_eq_eq_one_iff
    isOpen_thickening isClosed_cthickening
    (cthickening_subset_thickening' hδ (half_lt_self hδ) K) (n := (⊤ : ℕ∞))
  have hs : tsupport η ⊆ cthickening δ K := by
    rw [tsupport,hsupp]
    exact closure_thickening_subset_cthickening δ K
  refine ⟨η,thickening (δ/2) K,hη,
    (hK.cthickening (r := δ)).of_isClosed_subset isClosed_closure hs,
    hs.trans hδΩ,isOpen_thickening,self_subset_thickening (half_pos hδ) K,?_⟩
  intro x hx
  exact (hone x).1 (thickening_subset_cthickening (δ/2) K hx)

 theorem exists_smooth_rectangle_extension {Ω K : Set (ℝ × ℝ)}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {b : (ℝ × ℝ) → ℝ} (hb : ContDiffOn ℝ 1 b Ω) :
    ∃ (g : (ℝ × ℝ) → ℝ) (V : Set (ℝ × ℝ)), ContDiff ℝ 1 g ∧
      HasCompactSupport g ∧ IsOpen V ∧ K ⊆ V ∧ EqOn g b V ∧
      EqOn (fderiv ℝ g) (fderiv ℝ b) V := by
  obtain ⟨η,V,hη,hηs,hηΩ,hV,hKV,hη1⟩ := exists_rectangle_cutoff_one_near hK hΩ hKΩ
  let g : (ℝ × ℝ) → ℝ := fun x => η x*b x
  have hg : ContDiff ℝ 1 g := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Ω
    · exact (hη.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt.mul (hb.contDiffAt (hΩ.mem_nhds hx))
    · have hx' : x ∉ tsupport η := fun hh => hx (hηΩ hh)
      apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hx'] with y hy
      change η y*b y = 0
      rw [image_eq_zero_of_notMem_tsupport hy,zero_mul]
  have he : EqOn g b V := fun x hx => by change η x*b x = b x; rw [hη1 x hx,one_mul]
  refine ⟨g,V,hg,hηs.mul_right,hV,hKV,he,?_⟩
  intro x hx
  exact (he.eventuallyEq_of_mem (hV.mem_nhds hx)).fderiv_eq

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_LocalTraceMaskSobolev
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local mask witness uses only smoothness of the raw scalar on the
actual source open set; a compact cutoff constructs the auxiliary global
extension and its differential agrees on the requested rectangle. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem local_masked_scalar_rectangle_sobolev
    {cutoff : ℕ → (ℝ × ℝ) → ℝ} (hs : ∀ j, ContDiff ℝ 1 (cutoff j))
    (hc : ∀ j p, cutoff j p ∈ Icc (0:ℝ) 1)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) {b : ℝ × ℝ → ℝ} (hb : ContDiffOn ℝ 1 b Ω)
    {P : ℝ × ℝ → ℝ} (hPm : Measurable P) (hP0 : ∀ p, 0 ≤ P p)
    {a₁ a₂ b₁ b₂ : ℝ} (ha : a₁ ≤ a₂) (hb' : b₁ ≤ b₂)
    (hbox : Icc a₁ a₂ ×ˢ Icc b₁ b₂ ⊆ Ω)
    (hP2 : MemLp P 2 (volume.restrict (Icc a₁ a₂ ×ˢ Icc b₁ b₂)))
    (hdom : ∀ n, ∀ᵐ p ∂volume.restrict (Icc a₁ a₂ ×ˢ Icc b₁ b₂),
      ∑ j ∈ Finset.range n, volume.real (I j)*‖fderiv ℝ (cutoff j) p‖ ≤ P p)
    (a : ℝ) :
    ∃ W : DeGiorgi.MemW1pWitness 2
      ((fun p => infiniteTracePrimitive cutoff I a p (b p)) ∘ euclideanPlaneCoordinates)
      (euclideanPlaneCoordinates ⁻¹' (Ioo a₁ a₂ ×ˢ Ioo b₁ b₂)),
      ∀ i : Fin 2, ∀ᵐ z ∂volume.restrict
        (euclideanPlaneCoordinates ⁻¹' (Ioo a₁ a₂ ×ˢ Ioo b₁ b₂)),
        |W.weakGrad z i| ≤ ‖fderiv ℝ b (euclideanPlaneCoordinates z)‖+P (euclideanPlaneCoordinates z) := by
  obtain ⟨g,V,hg,_,hV,hKV,he,hde⟩ := exists_smooth_rectangle_extension hΩ
    (isCompact_Icc.prod isCompact_Icc) hbox hb
  obtain ⟨W,hW⟩ := smooth_masked_scalar_rectangle_sobolev hs hc hI hIf hg hPm hP0 ha hb' hP2 hdom a
  have hOV : Ioo a₁ a₂ ×ˢ Ioo b₁ b₂ ⊆ V :=
    (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self).trans hKV
  have hmeas : MeasurableSet (euclideanPlaneCoordinates ⁻¹' (Ioo a₁ a₂ ×ˢ Ioo b₁ b₂)) :=
    ((isOpen_Ioo.prod isOpen_Ioo).preimage euclideanPlaneCoordinates.continuous).measurableSet
  have hE : ((fun p => infiniteTracePrimitive cutoff I a p (g p)) ∘ euclideanPlaneCoordinates) =ᵐ[
      volume.restrict (euclideanPlaneCoordinates ⁻¹' (Ioo a₁ a₂ ×ˢ Ioo b₁ b₂))]
      ((fun p => infiniteTracePrimitive cutoff I a p (b p)) ∘ euclideanPlaneCoordinates) := by
    filter_upwards [ae_restrict_mem hmeas] with z hz
    simp only [Function.comp_apply,he (hOV hz)]
  refine ⟨W.congr_ae hE,?_⟩
  intro i
  filter_upwards [hW i,ae_restrict_mem hmeas] with z hz hzV
  simpa only [DeGiorgi.MemW1pWitness.congr_ae,hde (hOV hzV)] using hz

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceBalloonRadii
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit shrinking balloon radii. The geometric extra radii reserve
at least half of every zero-radius balloon after all later deletions. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] Classical.propDecidable

 theorem traceExtraRadius_pos (j : ℕ) : 0 < traceExtraRadius j := by
  exact pow_pos (by norm_num) j

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedScalarIntervals
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual intervals for the matched disks. Their lengths are square
summable and their centers represent values of the closed correspondence.
Unused natural codes are harmless shrinking intervals at one fixed fiber. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}

variable [Encodable D.IndexedMatchedPair]

 theorem MatchedRoundDisks.traceWidth_pos (E : D.MatchedRoundDisks) (L : ℝ≥0) (n : ℕ) :
    0 < E.traceWidth L n :=
  add_pos_of_nonneg_of_pos (mul_nonneg L.coe_nonneg
    (traceEnumeration_nonneg E.target_nonneg n)) (traceExtraRadius_pos n)

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceEnumerationUnion
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function
noncomputable section
namespace CircleDomainRigidity

 theorem traceEnumeration_iUnion {ι X : Type*} [Encodable ι] (V : ι → Set X) :
    (⋃ n, traceEnumeration V ∅ n) = ⋃ j, V j := by
  ext x
  constructor
  · intro hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    by_cases h : n ∈ Set.range (Encodable.encode : ι → ℕ)
    · obtain ⟨j,rfl⟩ := h
      rw [traceEnumeration_encode] at hn
      exact mem_iUnion.mpr ⟨j,hn⟩
    · rw [traceEnumeration_missing V ∅ h] at hn
      exact hn.elim
  · intro hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨Encodable.encode j,by simpa only [traceEnumeration_encode] using hj⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceMaskPlateauSobolev
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On a zero-cutoff neighborhood the primitive has a fixed endpoint.
Consequently its local Sobolev regularity does not require regularity of
the raw scalar, including point-to-disk component matches. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem fixed_endpoint_mask_rectangle_sobolev
    {cutoff : ℕ → (ℝ × ℝ) → ℝ} (hs : ∀ j, ContDiff ℝ 1 (cutoff j))
    (hc : ∀ j p, cutoff j p ∈ Icc (0:ℝ) 1)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    {P : ℝ × ℝ → ℝ} (hPm : Measurable P) (hP0 : ∀ p, 0 ≤ P p)
    {a₁ a₂ b₁ b₂ : ℝ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂)
    (hP2 : MemLp P 2 (volume.restrict (Icc a₁ a₂ ×ˢ Icc b₁ b₂)))
    (hdom : ∀ n, ∀ᵐ p ∂volume.restrict (Icc a₁ a₂ ×ˢ Icc b₁ b₂),
      ∑ j ∈ Finset.range n, volume.real (I j)*‖fderiv ℝ (cutoff j) p‖ ≤ P p)
    (a β : ℝ) :
    ∃ W : DeGiorgi.MemW1pWitness 2
      ((fun p => infiniteTracePrimitive cutoff I a p β) ∘ euclideanPlaneCoordinates)
      (euclideanPlaneCoordinates ⁻¹' (Ioo a₁ a₂ ×ˢ Ioo b₁ b₂)),
      ∀ i : Fin 2, ∀ᵐ z ∂volume.restrict
        (euclideanPlaneCoordinates ⁻¹' (Ioo a₁ a₂ ×ˢ Ioo b₁ b₂)),
        |W.weakGrad z i| ≤ P (euclideanPlaneCoordinates z) := by
  simpa only [fderiv_const_apply,norm_zero,zero_add] using
    smooth_masked_scalar_rectangle_sobolev hs hc hI hIf
      (b := fun _ => β) contDiff_const hPm hP0 ha hb hP2 hdom a

 theorem plateau_mask_rectangle_sobolev
    {cutoff : ℕ → (ℝ × ℝ) → ℝ} (hs : ∀ j, ContDiff ℝ 1 (cutoff j))
    (hc : ∀ j p, cutoff j p ∈ Icc (0:ℝ) 1)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    {P b : ℝ × ℝ → ℝ} (hPm : Measurable P) (hP0 : ∀ p, 0 ≤ P p)
    {a₁ a₂ b₁ b₂ : ℝ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂)
    (hP2 : MemLp P 2 (volume.restrict (Icc a₁ a₂ ×ˢ Icc b₁ b₂)))
    (hdom : ∀ n, ∀ᵐ p ∂volume.restrict (Icc a₁ a₂ ×ˢ Icc b₁ b₂),
      ∑ j ∈ Finset.range n, volume.real (I j)*‖fderiv ℝ (cutoff j) p‖ ≤ P p)
    {j : ℕ} (hconv : OrdConnected (I j)) {β : ℝ} (hβ : β ∈ I j)
    (hlocal : ∀ p ∈ Ioo a₁ a₂ ×ˢ Ioo b₁ b₂, cutoff j p = 0 ∧ b p ∈ I j)
    (a : ℝ) :
    ∃ W : DeGiorgi.MemW1pWitness 2
      ((fun p => infiniteTracePrimitive cutoff I a p (b p)) ∘ euclideanPlaneCoordinates)
      (euclideanPlaneCoordinates ⁻¹' (Ioo a₁ a₂ ×ˢ Ioo b₁ b₂)),
      ∀ i : Fin 2, ∀ᵐ z ∂volume.restrict
        (euclideanPlaneCoordinates ⁻¹' (Ioo a₁ a₂ ×ˢ Ioo b₁ b₂)),
        |W.weakGrad z i| ≤ P (euclideanPlaneCoordinates z) := by
  obtain ⟨W,hW⟩ := fixed_endpoint_mask_rectangle_sobolev hs hc hI hIf hPm hP0 ha hb hP2 hdom a β
  have he : ((fun p => infiniteTracePrimitive cutoff I a p β) ∘ euclideanPlaneCoordinates) =ᵐ[
      volume.restrict (euclideanPlaneCoordinates ⁻¹' (Ioo a₁ a₂ ×ˢ Ioo b₁ b₂))]
      ((fun p => infiniteTracePrimitive cutoff I a p (b p)) ∘ euclideanPlaneCoordinates) := by
    filter_upwards [ae_restrict_mem ((isOpen_Ioo.prod isOpen_Ioo).preimage
      euclideanPlaneCoordinates.continuous).measurableSet] with z hz
    exact (infiniteTracePrimitive_plateau hc hI hconv (hlocal _ hz).1 (hlocal _ hz).2 hβ a).symm
  exact ⟨W.congr_ae he,hW⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalWeakGradientEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Locality identifies the actual Sobolev gradient and its energy. A
zero exterior contributes no energy; the intervening circle is null. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem weakGradient_eq_on_subset
    {Ω V : Set EuclideanPlane} (hV : IsOpen V) (hVΩ : V ⊆ Ω)
    {u v : EuclideanPlane → ℝ}
    (Hu : DeGiorgi.MemW1pWitness 2 u Ω) (Hv : DeGiorgi.MemW1pWitness 2 v V)
    (heq : EqOn u v V) :
    Hu.weakGrad =ᵐ[volume.restrict V] Hv.weakGrad := by
  let H := Hu.restrict hV hVΩ
  have hi (i : Fin 2) : (fun x => Hu.weakGrad x i) =ᵐ[volume.restrict V]
      fun x => Hv.weakGrad x i := by
    apply (weakPartial_congrOn hV (H.isWeakGrad i) heq).ae_eq hV (Hv.isWeakGrad i)
    · exact (H.weakGrad_component_memLp i).locallyIntegrable (by norm_num)
    · exact (Hv.weakGrad_component_memLp i).locallyIntegrable (by norm_num)
  filter_upwards [ae_all_iff.mpr hi] with x hx
  ext i
  exact hx i

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PartitionTestDecomposition
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Only finitely many members of a locally finite open-domain partition
meet a compactly supported test. Their products sum exactly to the test. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
namespace OpenPlanePartition

 theorem finite_test_decomposition {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
    (ρ : OpenPlanePartition Ω ι) {φ : EuclideanPlane → ℝ}
    (hs : HasCompactSupport φ) (hsub : tsupport φ ⊆ Ω) :
    ∃ F : Finset ι, φ = fun x => ∑ j ∈ F, ρ.weight j x*φ x := by
  classical
  have hK : IsCompact ((Subtype.val : Ω → EuclideanPlane) ⁻¹' tsupport φ) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hs (by simpa only [Subtype.range_coe] using hsub)
  have hfin := ρ.locallyFinite.finite_nonempty_inter_compact hK
  refine ⟨hfin.toFinset,?_⟩
  funext x
  by_cases hx : φ x = 0
  · simp only [hx,mul_zero,Finset.sum_const_zero]
  · have hxK : x ∈ tsupport φ := subset_tsupport φ hx
    have hxΩ : x ∈ Ω := hsub hxK
    have hin : support (fun j => ρ.weight j x) ⊆ hfin.toFinset := by
      intro j hj
      apply hfin.mem_toFinset.mpr
      exact ⟨⟨x,hxΩ⟩,hj,hxK⟩
    have hw : (∑ᶠ j, ρ.weight j x) = ∑ j ∈ hfin.toFinset, ρ.weight j x :=
      finsum_eq_sum_of_support_subset _ hin
    rw [← Finset.sum_mul,← hw,ρ.sum_one ⟨x,hxΩ⟩,one_mul]

end OpenPlanePartition
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeakPartialLocality
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak partial derivatives are local on an open plane domain. The
proof decomposes each compact test into finitely many actual smooth
partition products; it does not assume a global Sobolev gluing theorem. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem weakPartial_test_on_superset {u g : EuclideanPlane → ℝ} {i : Fin 2}
    {V Ω : Set EuclideanPlane} (hVΩ : V ⊆ Ω)
    (hw : DeGiorgi.HasWeakPartialDeriv i g u V)
    {φ : EuclideanPlane → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hs : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ V) :
    (∫ x in Ω, u x*fderiv ℝ φ x (EuclideanSpace.single i 1)) = -(∫ x in Ω, g x*φ x) := by
  have heq (S : Set EuclideanPlane) (hVS : V ⊆ S) :
      (∫ x in S, u x*fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x, u x*fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ φ y (EuclideanSpace.single i 1))
      (fun hh => hx (hVS (hsub (tsupport_fderiv_apply_subset ℝ _ hh)))) ,mul_zero]
  have geq (S : Set EuclideanPlane) (hVS : V ⊆ S) :
      (∫ x in S, g x*φ x) = ∫ x, g x*φ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hVS (hsub hh))),mul_zero]
  rw [heq Ω hVΩ,geq Ω hVΩ,← heq V Subset.rfl,← geq V Subset.rfl]
  exact hw φ hφ hs hsub

 theorem weakPartial_test_finite_sum {u g : EuclideanPlane → ℝ} {i : Fin 2}
    {Ω : Set EuclideanPlane} (hu : LocallyIntegrable u (volume.restrict Ω))
    (hg : LocallyIntegrable g (volume.restrict Ω)) {ι : Type*}
    (F : Finset ι) (ψ : ι → EuclideanPlane → ℝ)
    (hψ : ∀ j ∈ F, ContDiff ℝ (⊤ : ℕ∞) (ψ j))
    (hs : ∀ j ∈ F, HasCompactSupport (ψ j))
    (hw : ∀ j ∈ F, (∫ x in Ω, u x*fderiv ℝ (ψ j) x (EuclideanSpace.single i 1)) =
      -(∫ x in Ω, g x*ψ j x)) :
    (∫ x in Ω, u x*fderiv ℝ (fun y => ∑ j ∈ F, ψ j y) x (EuclideanSpace.single i 1)) =
      -(∫ x in Ω, g x*(∑ j ∈ F, ψ j x)) := by
  have hIu (j : ι) (hj : j ∈ F) : Integrable
      (fun x => u x*fderiv ℝ (ψ j) x (EuclideanSpace.single i 1)) (volume.restrict Ω) := by
    simpa only [smul_eq_mul] using hu.integrable_smul_right_of_hasCompactSupport
      (((hψ j hj).continuous_fderiv (by simp)).clm_apply continuous_const)
      ((hs j hj).fderiv_apply (𝕜 := ℝ) _)
  have hIg (j : ι) (hj : j ∈ F) : Integrable (fun x => g x*ψ j x) (volume.restrict Ω) := by
    simpa only [smul_eq_mul] using hg.integrable_smul_right_of_hasCompactSupport
      (hψ j hj).continuous (hs j hj)
  have hd (x : EuclideanPlane) :
      fderiv ℝ (fun y => ∑ j ∈ F, ψ j y) x (EuclideanSpace.single i 1) =
        ∑ j ∈ F, fderiv ℝ (ψ j) x (EuclideanSpace.single i 1) := by
    rw [fderiv_fun_sum (fun j hj => (hψ j hj).differentiable (by simp) x)]
    simp only [sum_apply]
  simp_rw [hd,Finset.mul_sum]
  rw [integral_finsetSum _ hIu,integral_finsetSum _ hIg]
  calc
    _ = ∑ j ∈ F, -(∫ x in Ω, g x*ψ j x) := Finset.sum_congr rfl hw
    _ = -(∑ j ∈ F, ∫ x in Ω, g x*ψ j x) := Finset.sum_neg_distrib _

 theorem weakPartial_of_local {u g : EuclideanPlane → ℝ} {i : Fin 2}
    {Ω : Set EuclideanPlane} (hΩ : IsOpen Ω)
    (hu : LocallyIntegrable u (volume.restrict Ω))
    (hg : LocallyIntegrable g (volume.restrict Ω))
    (hloc : ∀ x ∈ Ω, ∃ V : Set EuclideanPlane, IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
      DeGiorgi.HasWeakPartialDeriv i g u V) :
    DeGiorgi.HasWeakPartialDeriv i g u Ω := by
  classical
  let O : TopologicalSpace.Opens EuclideanPlane := ⟨Ω,hΩ⟩
  choose V hV hxV hVΩ hw using (fun x : O => hloc x x.property)
  obtain ⟨ι,_,ρ,c,hsub⟩ := exists_openPlanePartition O
    (fun x => Subtype.val ⁻¹' V x) (fun x => (hV x).preimage continuous_subtype_val |>.mem_nhds (hxV x))
  intro φ hφ hs hφΩ
  obtain ⟨F,hF⟩ := ρ.finite_test_decomposition hs hφΩ
  let ψ : ι → EuclideanPlane → ℝ := fun j x => ρ.weight j x*φ x
  have hψ (j : ι) : ContDiff ℝ (⊤ : ℕ∞) (ψ j) := (ρ.smooth j).mul hφ
  have hsψ (j : ι) : HasCompactSupport (ψ j) := (ρ.compact j).mul_right
  have hψV (j : ι) : tsupport (ψ j) ⊆ V (c j) := by
    apply tsupport_mul_subset_left.trans
    intro x hx
    obtain ⟨p,hp,rfl⟩ := hsub j hx
    exact hp
  have hid (j : ι) : (∫ x in Ω, u x*fderiv ℝ (ψ j) x (EuclideanSpace.single i 1)) =
      -(∫ x in Ω, g x*ψ j x) :=
    weakPartial_test_on_superset (hVΩ (c j)) (hw (c j)) (hψ j) (hsψ j) (hψV j)
  have htest := weakPartial_test_finite_sum hu hg F ψ
    (fun j _ => hψ j) (fun j _ => hsψ j) (fun j _ => hid j)
  change (∫ x in Ω, u x*fderiv ℝ φ x (EuclideanSpace.single i 1)) = -(∫ x in Ω, g x*φ x)
  have hsum : (fun y => ∑ j ∈ F, ψ j y) = φ := hF.symm
  rw [hsum] at htest
  simpa only [congrFun hsum] using htest

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PartitionWeakGradient
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual global weak gradients from local Sobolev witnesses. Uniqueness
on overlaps identifies the partition sum with each local gradient, and
finite test decomposition proves the global weak identity. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem partition_gradient_eq_local
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (V : ι → Set EuclideanPlane)
    (hV : ∀ j, IsOpen (V j)) (hVΩ : ∀ j, V j ⊆ Ω)
    (hsub : ∀ j, tsupport (ρ.weight j) ⊆ V j)
    {u : EuclideanPlane → ℝ} (W : ∀ j, DeGiorgi.MemW1pWitness 2 u (V j))
    (j : ι) (k : Fin 2) :
    (fun x => ∑ᶠ l, ρ.weight l x*(W l).weakGrad x k) =ᵐ[volume.restrict (V j)]
      (fun x => (W j).weakGrad x k) := by
  have hpair (l : ι) : ∀ᵐ x ∂volume, x ∈ V j ∩ V l →
      (W j).weakGrad x = (W l).weakGrad x := by
    apply (ae_restrict_iff' ((hV j).inter (hV l)).measurableSet).mp
    exact weakGradient_eq_on_subset ((hV j).inter (hV l)) inter_subset_left (W j)
      ((W l).restrict ((hV j).inter (hV l)) inter_subset_right) (fun _ _ => rfl)
  have hall := ae_all_iff.mpr hpair
  filter_upwards [ae_restrict_of_ae hall,ae_restrict_mem (hV j).measurableSet] with x hx hxV
  calc
    _ = ∑ᶠ l, ρ.weight l x*(W j).weakGrad x k := by
      apply finsum_congr
      intro l
      by_cases hl : ρ.weight l x = 0
      · simp only [hl,zero_mul]
      · rw [hx l ⟨hxV,hsub l (subset_tsupport (ρ.weight l) hl)⟩]
    _ = (∑ᶠ l, ρ.weight l x)*(W j).weakGrad x k := (finsum_mul _ _).symm
    _ = (W j).weakGrad x k := by rw [ρ.sum_one ⟨x,hVΩ j hxV⟩,one_mul]

 theorem exists_partition_weak_gradient
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (V : ι → Set EuclideanPlane)
    (hV : ∀ j, IsOpen (V j)) (hVΩ : ∀ j, V j ⊆ Ω)
    (hsub : ∀ j, tsupport (ρ.weight j) ⊆ V j)
    {u : EuclideanPlane → ℝ} (hu : MemLp u 2 (volume.restrict Ω))
    (W : ∀ j, DeGiorgi.MemW1pWitness 2 u (V j))
    {P : EuclideanPlane → ℝ} (hP : MemLp P 2 (volume.restrict Ω))
    (hbound : ∀ j k, ∀ᵐ x ∂volume.restrict (V j), |(W j).weakGrad x k| ≤ P x) :
    ∃ H : DeGiorgi.MemW1pWitness 2 u Ω,
      ∀ k : Fin 2, ∀ᵐ x ∂volume.restrict Ω, |H.weakGrad x k| ≤ P x := by
  let G : Fin 2 → EuclideanPlane → ℝ := fun k x => ∑ᶠ j, ρ.weight j x*(W j).weakGrad x k
  have hG (k : Fin 2) : MemLp (G k) 2 (volume.restrict Ω) :=
    partition_component_memLp ρ V (fun j => (hV j).measurableSet) hsub
      (fun j x => (W j).weakGrad x k) (fun j => (W j).weakGrad_component_memLp k |>.aestronglyMeasurable)
      hP (fun j => hbound j k)
  have hGbound (k : Fin 2) : ∀ᵐ x ∂volume.restrict Ω, |G k x| ≤ P x :=
    partition_component_bound ρ V (fun j => (hV j).measurableSet) hsub
      (fun j x => (W j).weakGrad x k) P (fun j => hbound j k)
  have hweak (k : Fin 2) : DeGiorgi.HasWeakPartialDeriv k (G k) u Ω := by
    apply weakPartial_of_local Ω.isOpen (hu.locallyIntegrable (by norm_num))
      ((hG k).locallyIntegrable (by norm_num))
    intro x hx
    have hex : ∃ j, ρ.weight j x ≠ 0 := by
      by_contra! hz
      have hone := ρ.sum_one ⟨x,hx⟩
      simp only [hz,finsum_zero] at hone
      exact zero_ne_one hone
    obtain ⟨j,hj⟩ := hex
    refine ⟨V j,hV j,hsub j (subset_tsupport (ρ.weight j) hj),hVΩ j,?_⟩
    exact ((W j).isWeakGrad k).congr_ae Filter.EventuallyEq.rfl
      (partition_gradient_eq_local ρ V hV hVΩ hsub W j k).symm
  let H : DeGiorgi.MemW1pWitness 2 u Ω := {
    memLp := hu
    weakGrad := fun x => WithLp.toLp 2 (fun k => G k x)
    weakGrad_component_memLp := hG
    isWeakGrad := hweak }
  exact ⟨H,hGbound⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalSobolevGluing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local Sobolev witnesses with one integrable gradient majorant give
an actual witness on the whole open set, with a finite total energy. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_local_sobolev_gluing {Ω : Set EuclideanPlane} (hΩ : IsOpen Ω)
    {u P : EuclideanPlane → ℝ} (hu : MemLp u 2 (volume.restrict Ω))
    (hP : MemLp P 2 (volume.restrict Ω))
    (hloc : ∀ x ∈ Ω, ∃ V : Set EuclideanPlane, IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
      ∃ W : DeGiorgi.MemW1pWitness 2 u V, ∀ k : Fin 2,
        ∀ᵐ y ∂volume.restrict V, |W.weakGrad y k| ≤ P y) :
    ∃ H : DeGiorgi.MemW1pWitness 2 u Ω,
      (∀ k : Fin 2, ∀ᵐ x ∂volume.restrict Ω, |H.weakGrad x k| ≤ P x) ∧
      (∫ x in Ω, ‖H.weakGrad x‖^2) ≤ 2*(∫ x in Ω, P x^2) := by
  classical
  let O : TopologicalSpace.Opens EuclideanPlane := ⟨Ω,hΩ⟩
  choose V hV hxV hVΩ W hW using (fun x : O => hloc x x.property)
  obtain ⟨ι,inst,ρ,c,hsub⟩ := exists_openPlanePartition O
    (fun x => Subtype.val ⁻¹' V x) (fun x => (hV x).preimage continuous_subtype_val |>.mem_nhds (hxV x))
  let : Countable ι := inst
  have hsub' (j : ι) : tsupport (ρ.weight j) ⊆ V (c j) := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := hsub j hx
    exact hp
  obtain ⟨H,hH⟩ := exists_partition_weak_gradient ρ (fun j => V (c j))
    (fun j => hV (c j)) (fun j => hVΩ (c j)) hsub' hu
    (fun j => W (c j)) hP (fun j k => hW (c j) k)
  refine ⟨H,hH,?_⟩
  have hpoint : ∀ᵐ x ∂volume.restrict Ω, ‖H.weakGrad x‖^2 ≤ 2*P x^2 := by
    filter_upwards [hH 0,hH 1] with x hx0 hx1
    rw [plane_norm_sq]
    have hp : 0 ≤ P x := (abs_nonneg _).trans hx0
    have h0 := mul_self_le_mul_self (abs_nonneg _) hx0
    have h1 := mul_self_le_mul_self (abs_nonneg _) hx1
    simp only [← sq, sq_abs] at h0 h1
    nlinarith
  calc
    _ ≤ ∫ x in Ω, 2*P x^2 := integral_mono_ae H.weakGrad_memLp.norm.integrable_sq
      (hP.integrable_sq.const_mul 2) hpoint
    _ = _ := integral_const_mul _ _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceMaskOpenSobolev
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local smooth and plateau witnesses join on the actual open union.
The source differential is charged only on the original domain, and
balloon derivatives are charged to the constructed global L² density. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem trace_mask_open_sobolev
    {cutoff : ℕ → (ℝ × ℝ) → ℝ} (hs : ∀ j, ContDiff ℝ 1 (cutoff j))
    (hc : ∀ j p, cutoff j p ∈ Icc (0:ℝ) 1)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ∞)
    (hconv : ∀ j, OrdConnected (I j)) (β : ℕ → ℝ) (hβ : ∀ j, β j ∈ I j)
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) {b : ℝ × ℝ → ℝ} (hb : ContDiffOn ℝ 1 b Ω)
    (hb2 : MemLp (fderiv ℝ b) 2 (volume.restrict Ω))
    (V : ℕ → Set (ℝ × ℝ)) (hV : ∀ j, IsOpen (V j))
    (hv : ∀ j p, p ∈ V j → cutoff j p = 0 ∧ b p ∈ I j)
    {P : ℝ × ℝ → ℝ} (hPm : Measurable P) (hP0 : ∀ p, 0 ≤ P p) (hP2 : MemLp P 2 volume)
    (hdom : ∀ n, ∀ᵐ p ∂volume,
      ∑ j ∈ Finset.range n, volume.real (I j)*‖fderiv ℝ (cutoff j) p‖ ≤ P p)
    (a : ℝ) (hu : Continuous (fun p => infiniteTracePrimitive cutoff I a p (b p)))
    (hus : HasCompactSupport (fun p => infiniteTracePrimitive cutoff I a p (b p))) :
    ∃ W : DeGiorgi.MemW1pWitness 2
      ((fun p => infiniteTracePrimitive cutoff I a p (b p)) ∘ euclideanPlaneCoordinates)
      (euclideanPlaneCoordinates ⁻¹' (Ω ∪ ⋃ j, V j)),
      ∀ k : Fin 2, ∀ᵐ x ∂volume.restrict (euclideanPlaneCoordinates ⁻¹' (Ω ∪ ⋃ j, V j)),
        |W.weakGrad x k| ≤
          Ω.indicator (fun p => ‖fderiv ℝ b p‖) (euclideanPlaneCoordinates x)+P (euclideanPlaneCoordinates x) := by
  let O := Ω ∪ ⋃ j, V j
  let Q := Ω.indicator (fun p => ‖fderiv ℝ b p‖)
  let U := fun p => infiniteTracePrimitive cutoff I a p (b p)
  have hO : IsOpen O := hΩ.union (isOpen_iUnion hV)
  have hQm : Measurable Q := (measurable_fderiv ℝ b).norm.indicator hΩ.measurableSet
  have hQ0 (p : ℝ × ℝ) : 0 ≤ Q p := indicator_nonneg (fun _ _ => norm_nonneg _) p
  have hQ2 : MemLp Q 2 volume := (memLp_indicator_iff_restrict hΩ.measurableSet).mpr hb2.norm
  have hEopen : IsOpen (euclideanPlaneCoordinates ⁻¹' O) := hO.preimage euclideanPlaneCoordinates.continuous
  have hUE : MemLp (U ∘ euclideanPlaneCoordinates) 2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' O)) :=
    ((hu.comp euclideanPlaneCoordinates.continuous).memLp_of_hasCompactSupport
      (hus.comp_homeomorph euclideanPlaneCoordinates.toHomeomorph)).restrict _
  have hPE : MemLp (fun x => Q (euclideanPlaneCoordinates x)+P (euclideanPlaneCoordinates x))
      2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' O)) :=
    ((hQ2.add hP2).comp_measurePreserving euclideanPlaneCoordinates_measurePreserving).restrict _
  have hloc : ∀ x ∈ euclideanPlaneCoordinates ⁻¹' O, ∃ T : Set EuclideanPlane,
      IsOpen T ∧ x ∈ T ∧ T ⊆ euclideanPlaneCoordinates ⁻¹' O ∧
      ∃ W : DeGiorgi.MemW1pWitness 2 (U ∘ euclideanPlaneCoordinates) T,
        ∀ k : Fin 2, ∀ᵐ y ∂volume.restrict T,
          |W.weakGrad y k| ≤ Q (euclideanPlaneCoordinates y)+P (euclideanPlaneCoordinates y) := by
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨a₁,a₂,b₁,b₂,ha,hb',hxp,hbox⟩ := exists_closed_rectangle_inside_open hΩ hx
      let T := euclideanPlaneCoordinates ⁻¹' (Ioo a₁ a₂ ×ˢ Ioo b₁ b₂)
      have hT : IsOpen T := (isOpen_Ioo.prod isOpen_Ioo).preimage euclideanPlaneCoordinates.continuous
      have hTΩ : ∀ y ∈ T, euclideanPlaneCoordinates y ∈ Ω :=
        fun y hy => hbox ((Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self) hy)
      obtain ⟨W,hW⟩ := local_masked_scalar_rectangle_sobolev hs hc hI hIf hΩ hb hPm hP0
        ha.le hb'.le hbox (hP2.restrict _) (fun n => ae_restrict_of_ae (hdom n)) a
      refine ⟨T,hT,hxp,(fun y hy => Or.inl (hTΩ y hy)),W,?_⟩
      intro k
      filter_upwards [hW k,ae_restrict_mem hT.measurableSet] with y hy hyT
      simpa only [Q,indicator_of_mem (hTΩ y hyT)] using hy
    · obtain ⟨j,hxj⟩ := mem_iUnion.mp hx
      obtain ⟨a₁,a₂,b₁,b₂,ha,hb',hxp,hbox⟩ := exists_closed_rectangle_inside_open (hV j) hxj
      let T := euclideanPlaneCoordinates ⁻¹' (Ioo a₁ a₂ ×ˢ Ioo b₁ b₂)
      have hT : IsOpen T := (isOpen_Ioo.prod isOpen_Ioo).preimage euclideanPlaneCoordinates.continuous
      have hTV : ∀ y ∈ T, euclideanPlaneCoordinates y ∈ V j :=
        fun y hy => hbox ((Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self) hy)
      obtain ⟨W,hW⟩ := plateau_mask_rectangle_sobolev hs hc hI hIf hPm hP0
        ha.le hb'.le (hP2.restrict _) (fun n => ae_restrict_of_ae (hdom n))
        (hconv j) (hβ j) (fun p hp => hv j p (hbox ((Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self) hp))) a
      refine ⟨T,hT,hxp,(fun y hy => Or.inr (mem_iUnion.mpr ⟨j,hTV y hy⟩)),W,?_⟩
      intro k
      filter_upwards [hW k] with y hy
      exact hy.trans (le_add_of_nonneg_left (hQ0 _))
  obtain ⟨W,hW,_⟩ := exists_local_sobolev_gluing hEopen hUE hPE hloc
  exact ⟨W,hW⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedRealMaskSobolev
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the proved open-set Sobolev gluing to the constructed masks.
The only scalar hypotheses concern the actual smooth pullback on the original domain. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}
variable [Encodable D.IndexedMatchedPair]

 theorem realPlaneDomain_open {G : Set Sphere} (hG : IsOpen G) : IsOpen (realPlaneDomain G) :=
  hG.preimage (OnePoint.continuous_coe.comp Complex.equivRealProdCLM.symm.continuous)

omit [Encodable D.IndexedMatchedPair] in
 theorem physical_maskDomain (W : D.IndexedMatchedPair → Set ℂ) :
    physicalPlaneDomain (maskDomain G W) = euclideanPlaneCoordinates ⁻¹'
      (realPlaneDomain G ∪ ⋃ j, Complex.equivRealProdCLM.symm ⁻¹' W j) := by
  ext x
  change ((complexPlaneCoordinates x : Sphere) ∈ G ∨
    (complexPlaneCoordinates x : Sphere) ∈ ⋃ j, ((↑) : ℂ → Sphere) '' W j) ↔ _
  simp only [mem_preimage,mem_union,mem_iUnion,realPlaneDomain,mem_ofPred_eq]
  constructor
  · rintro (h | ⟨j,z,hz,he⟩)
    · exact Or.inl h
    · have hzx : z = complexPlaneCoordinates x := OnePoint.coe_injective he
      exact Or.inr ⟨j,by simpa only [hzx,complexPlaneCoordinates,ContinuousLinearEquiv.trans_apply] using hz⟩
  · rintro (h | ⟨j,hj⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j,complexPlaneCoordinates x,hj,rfl⟩

 theorem MatchedRealMask.sobolev
    {E : D.MatchedRoundDisks} {hG : IsOpen G} {hf : IsConformalEquivalence f G (f '' G)}
    {φ : Sphere → ℝ} {L : ℝ≥0} {m : ℕ} (M : MatchedRealMask E hG hf φ L m)
    (hb : ContDiffOn ℝ 1 (D.realSelectedScalar hG hf φ) (realPlaneDomain G))
    (hb2 : MemLp (fderiv ℝ (D.realSelectedScalar hG hf φ)) 2 (volume.restrict (realPlaneDomain G))) :
    Nonempty (DeGiorgi.MemW1pWitness 2
      (D.realMaskValue E hG hf φ L M.cutoff ∘ euclideanPlaneCoordinates)
      (physicalPlaneDomain (maskDomain G M.neighborhood))) := by
  let V : ℕ → Set (ℝ × ℝ) := traceEnumeration (fun j => Complex.equivRealProdCLM.symm ⁻¹' M.neighborhood j) ∅
  have hVo (n : ℕ) : IsOpen (V n) := by
    by_cases hn : n ∈ Set.range (Encodable.encode : D.IndexedMatchedPair → ℕ)
    · obtain ⟨j,rfl⟩ := hn
      dsimp only [V]
      rw [traceEnumeration_encode]
      exact (M.neighborhood_open j).preimage Complex.equivRealProdCLM.symm.continuous
    · dsimp only [V]
      rw [traceEnumeration_missing _ _ hn]
      exact isOpen_empty
  have hVz (n : ℕ) (p : ℝ × ℝ) (hp : p ∈ V n) : M.cutoff n p = 0 ∧
      D.realSelectedScalar hG hf φ p ∈ E.traceInterval hG hf φ L n := by
    by_cases hn : n ∈ Set.range (Encodable.encode : D.IndexedMatchedPair → ℕ)
    · obtain ⟨j,rfl⟩ := hn
      dsimp only [V] at hp
      rw [traceEnumeration_encode] at hp
      simpa only [ContinuousLinearEquiv.apply_symm_apply,realSelectedScalar] using
        M.neighborhood_zero j (Complex.equivRealProdCLM.symm p) hp
    · dsimp only [V] at hp
      rw [traceEnumeration_missing _ _ hn] at hp
      exact hp.elim
  obtain ⟨H,_⟩ := trace_mask_open_sobolev M.smooth M.unit
    (fun _ => measurableSet_Ioo) (fun _ => by simp)
    (fun _ => ordConnected_Ioo) (E.traceScalarCenter hG hf φ)
    (fun j => ⟨sub_lt_self _ (E.traceWidth_pos L j),lt_add_of_pos_right _ (E.traceWidth_pos L j)⟩)
    (realPlaneDomain_open hG) hb hb2 V hVo hVz
    M.density_measurable M.density_nonneg M.density_memLp
    (fun n => M.pays.mono (fun _ h => h n)) 0 M.continuous M.compact
  have he : physicalPlaneDomain (maskDomain G M.neighborhood) =
      euclideanPlaneCoordinates ⁻¹' (realPlaneDomain G ∪ ⋃ j, V j) := by
    dsimp only [V]
    rw [traceEnumeration_iUnion]
    exact physical_maskDomain M.neighborhood
  rw [he]
  exact ⟨H⟩

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SelectedOldError
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected old coordinates obey the requested uniform and gradient
norm errors, after choosing the squared energy budget below the tolerance. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem FlattenedSourceSelection.old_errors (M : CompactScalarModel G u)
    {R d A L e δ : ℝ} {H : ControlledHeight R d}
    {Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    (S : FlattenedSourceSelection M H Wold A L e e)
    (hδ : 0 < δ) (heδ : e ≤ δ) (heδsq : e ≤ δ^2) (i : Fin m) :
    (∀ x, |flattenValues (S.oldValues i) (u i x)-u i x| < δ) ∧
    (eLpNorm (fun x => (S.oldWitness i).weakGrad x-(Wold i).weakGrad x) 2
      (volume.restrict (physicalPlaneDomain G))).toReal < δ := by
  refine ⟨fun x => (S.old_close i (u i x)).trans_le heδ,?_⟩
  have hm := ((S.oldWitness i).weakGrad_memLp.sub (Wold i).weakGrad_memLp).norm
  have hE : (∫⁻ x in physicalPlaneDomain G,
      ENNReal.ofReal (‖(S.oldWitness i).weakGrad x-(Wold i).weakGrad x‖^2)) <
        ENNReal.ofReal (δ^2) := (S.old_error i).trans_le (ENNReal.ofReal_le_ofReal heδsq)
  have hi := indicator_L2_norm_lt_of_energy_lt hm MeasurableSet.univ hδ
    (by simpa only [Measure.restrict_univ, Pi.sub_apply] using hE)
  have hnorm : AEStronglyMeasurable
      (fun x => (S.oldWitness i).weakGrad x-(Wold i).weakGrad x)
      (volume.restrict (physicalPlaneDomain G)) :=
    ((S.oldWitness i).weakGrad_memLp.sub (Wold i).weakGrad_memLp).aestronglyMeasurable
  have hi' : (eLpNorm (fun x => ‖(S.oldWitness i).weakGrad x-(Wold i).weakGrad x‖) 2
      (volume.restrict (physicalPlaneDomain G))).toReal < δ := by
    simpa only [indicator_univ, Pi.sub_apply] using hi
  rwa [eLpNorm_norm _] at hi'

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SelectedOuterMargin
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected compact coordinates are separated from every bounded
trace center on the unchanged outer source collar. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem planePair_eq_complex_symm (z : ℂ) :
    planePair z.re z.im = complexPlaneCoordinates.symm z := by
  apply complexPlaneCoordinates.injective
  apply Complex.ext <;> simp [complexPlaneCoordinates_apply]

 theorem planePair_sub_norm (z : ℂ) (x : EuclideanPlane) :
    ‖planePair z.re z.im-x‖ = ‖z-complexPlaneCoordinates x‖ := by
  rw [planePair_eq_complex_symm]
  rw [← complexPlaneCoordinates_norm (complexPlaneCoordinates.symm z-x),
    map_sub, complexPlaneCoordinates.apply_symm_apply]

namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem selected_pair_outer_margin (M : CompactScalarModel G u)
    (harea : ExteriorCoefficientAreaTheorem)
    {R d R₀ A L δ ε v C r σ : ℝ} (H : ControlledHeight R d)
    {Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    (S : FlattenedSourceSelection M H Wold A L δ ε)
    (hR₀ : 0 < R₀) (hsource : (((↑) : ℂ → Sphere) '' ball 0 R₀)ᶜ ⊆ G)
    (η : ℂ → ℝ) (θ : EuclideanPlane → ℝ)
    {x : EuclideanPlane} (hx : x ∈ physicalPlaneDomain G)
    (hη : η (complexPlaneCoordinates x) = 1)
    (hθ : θ (complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x))) = 1)
    (hH : |H.height (M.function (complexPlaneCoordinates x))-
      (M.function (complexPlaneCoordinates x)).im| ≤ v)
    (hs : complexPlaneCoordinates x ∉ ⋃ n, support (S.cutoff n))
    (hxR : 2*R₀ ≤ ‖x‖) {c : EuclideanPlane} (hc : ‖c‖ ≤ C)
    (hmargin : r+σ+(δ+v)+R₀+C ≤ ‖x‖) :
    r+σ ≤ ‖planePair (M.compactPrioritySource S.cutoff S.value η x)
      (M.compactHeightSource H (flattenValues S.heightValues) θ x)-c‖ := by
  have hp := M.compact_pair_error_outside_support H (flattenValues S.heightValues)
    (fun t => (S.height_close t).le) η θ S.cutoff S.value hx hη hθ hH hs
  have hex := M.exterior_deviation_le harea hR₀ hsource (complexPlaneCoordinates x)
    (by simpa only [complexPlaneCoordinates_norm] using hxR)
  have hmodel : ‖planePair (M.function (complexPlaneCoordinates x)).re
      (M.function (complexPlaneCoordinates x)).im-x‖ ≤ R₀ := by
    rwa [planePair_sub_norm]
  exact outer_pair_margin hp hmodel hc hmargin

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ComplexPhysicalGradient
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.horizontalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complex-chart gradient identification in terms of the physical
classical differential of the represented scalar. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem complex_weak_physical_gradient_ae
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f D) (hE : MemLp (fderiv ℝ f) 2 (volume.restrict D))
    (W : DeGiorgi.MemW1pWitness 2 (f ∘ complexPlaneCoordinates)
      (complexPlaneCoordinates ⁻¹' D)) :
    W.weakGrad =ᵐ[volume.restrict (complexPlaneCoordinates ⁻¹' D)] fun x =>
      planeCovectorGradient (fderiv ℝ (f ∘ complexPlaneCoordinates) x) := by
  filter_upwards [complex_weak_gradient_ae hD hf hE W,
    ae_restrict_mem (hD.preimage complexPlaneCoordinates.continuous).measurableSet] with x hx hxD
  rw [hx]
  congr 1
  rw [fderiv_comp x ((hf.contDiffAt (hD.mem_nhds hxD)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    complexPlaneCoordinates.differentiableAt, complexPlaneCoordinates.fderiv]

 theorem weakPairDifferential_covectors (a b : EuclideanPlane →L[ℝ] ℝ) :
    weakPairDifferential (planeCovectorGradient a) (planeCovectorGradient b) =
      a.smulRight (EuclideanSpace.single (0 : Fin 2) 1)+
      b.smulRight (EuclideanSpace.single (1 : Fin 2) 1) := by
  unfold weakPairDifferential planeCovectorGradient
  rw [← plane_covector_of_basis a, ← plane_covector_of_basis b]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ModelSmoothBarrier
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.horizontalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth compact target barrier has its actual smooth source
Sobolev witness and no greater Dirichlet energy, by conformal transport. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem smooth_barrier_pullback (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hs : HasCompactSupport Φ) :
    ∃ V : DeGiorgi.MemW1pWitness 2
        (planeInverseTransport (extendAtInfinity M.function) Φ) (physicalPlaneDomain G),
      (∀ x, V.weakGrad x = planeCovectorGradient
        (fderiv ℝ (planeInverseTransport (extendAtInfinity M.function) Φ) x)) ∧
      (∫ x in physicalPlaneDomain G, ‖V.weakGrad x‖^2) ≤
        ∫ x : EuclideanPlane, ‖planeCovectorGradient (fderiv ℝ Φ x)‖^2 := by
  obtain ⟨hfc,hmap,fi,hfic,hfimap,hl,hr⟩ := M.conformal
  have heq : IsSmoothSphereEquivalence fi (extendAtInfinity M.function)
      (extendAtInfinity M.function '' G) G :=
    ⟨fun p hp => hfic.isSmoothSphereAt M.image_open hp, hfimap,
      fun p hp => hfc.isSmoothSphereAt hG hp, hmap, hr, hl⟩
  have hfi : fi OnePoint.infty = OnePoint.infty := by
    simpa only [extendAtInfinity_infty] using hl _ hinf
  have hparts (i : Fin 2) : MemLp (fun x => fderiv ℝ Φ x (EuclideanSpace.single i 1)) 2 volume :=
    ((hΦ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hs.fderiv_apply (𝕜 := ℝ) _)
  obtain ⟨hF,hD,hE⟩ := smooth_plane_energy_transport heq M.image_open hG
    ⟨_,hinf,rfl⟩ hfi hfic hΦ.contDiffOn (fun i => (hparts i).restrict _)
  let V := smoothPlaneSobolevWitness (isOpen_physicalPlaneDomain hG) hF
    (M.compact_target_pullback_memLp hG hinf hΦ.continuous hs) hD
  have hv (x : EuclideanPlane) : V.weakGrad x = planeCovectorGradient
      (fderiv ℝ (planeInverseTransport (extendAtInfinity M.function) Φ) x) := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
    funext i
    fin_cases i <;> simp [V, smoothPlaneSobolevWitness, planeCovectorGradient]
  have hi : Integrable (fun x : EuclideanPlane => (fderiv ℝ Φ x (EuclideanSpace.single 0 1))^2+
      (fderiv ℝ Φ x (EuclideanSpace.single 1 1))^2) volume :=
    (hparts 0).integrable_sq.add (hparts 1).integrable_sq
  refine ⟨V,hv,?_⟩
  calc
    _ = ∫ x in physicalPlaneDomain G,
        (fderiv ℝ (planeInverseTransport (extendAtInfinity M.function) Φ) x (EuclideanSpace.single 0 1))^2+
        (fderiv ℝ (planeInverseTransport (extendAtInfinity M.function) Φ) x (EuclideanSpace.single 1 1))^2 := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by dsimp only; rw [hv x, plane_norm_sq]; simp only [planeCovectorGradient,planePair_zero,planePair_one])
    _ = _ := hE
    _ ≤ ∫ x : EuclideanPlane, (fderiv ℝ Φ x (EuclideanSpace.single 0 1))^2+
        (fderiv ℝ Φ x (EuclideanSpace.single 1 1))^2 :=
      setIntegral_le_integral hi (Eventually.of_forall (fun x => add_nonneg (sq_nonneg _) (sq_nonneg _)))
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by dsimp only; rw [plane_norm_sq]; simp only [planeCovectorGradient,planePair_zero,planePair_one])

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ModelBarrierGradient
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.horizontalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reference differential in the selected barrier comparison is
exactly the weak gradient of the actual conformal pullback barrier. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem reference_barrier_value (M : CompactScalarModel G u)
    (Φ : EuclideanPlane → ℝ) (x : EuclideanPlane) :
    planeInverseTransport (extendAtInfinity M.function) Φ x =
      Φ (planePair ((M.function (complexPlaneCoordinates x)).re)
        ((M.function (complexPlaneCoordinates x)).im)) := by
  rw [planeInverseTransport_extendAtInfinity]
  simp only [planeSphere, extendAtInfinity_coe, sphereFromPlaneFunction_coe]
  congr 1
  apply complexPlaneCoordinates.injective
  rw [complexPlaneCoordinates.apply_symm_apply]
  simp only [complexPlaneCoordinates_apply, planePair_zero, planePair_one]

 theorem reference_barrier_gradient (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (L : ℝ)
    (Wx : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).re)
      (physicalPlaneDomain G ∩ ball 0 L))
    (Wy : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).im)
      (physicalPlaneDomain G ∩ ball 0 L))
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (V : DeGiorgi.MemW1pWitness 2 (planeInverseTransport (extendAtInfinity M.function) Φ)
      (physicalPlaneDomain G))
    (hV : ∀ x, V.weakGrad x = planeCovectorGradient
      (fderiv ℝ (planeInverseTransport (extendAtInfinity M.function) Φ) x)) :
    V.weakGrad =ᵐ[volume.restrict (physicalPlaneDomain G ∩ ball 0 L)] fun x =>
      planeCovectorGradient ((fderiv ℝ Φ (planePair ((M.function (complexPlaneCoordinates x)).re)
        ((M.function (complexPlaneCoordinates x)).im))).comp
          (weakPairDifferential (Wx.weakGrad x) (Wy.weakGrad x))) := by
  let D := {z : ℂ | (z : Sphere) ∈ G} ∩ ball (0 : ℂ) L
  have hD : IsOpen D := (hG.preimage OnePoint.continuous_coe).inter isOpen_ball
  have he : complexPlaneCoordinates ⁻¹' D = physicalPlaneDomain G ∩ ball 0 L := by
    ext x
    simp only [D, mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_ball, dist_zero_right,
      complexPlaneCoordinates_norm]
    rfl
  have hf : DifferentiableOn ℂ M.function D := fun z hz =>
    (finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz.1)).differentiableWithinAt
  have hs : ContDiffOn ℝ ∞ M.function D := (hf.contDiffOn hD).restrict_scalars ℝ
  have hx := complex_weak_physical_gradient_ae hD
    (Complex.reCLM.contDiff.comp_contDiffOn hs) (M.source_coordinate_memLp hG hinf L).1
  have hy := complex_weak_physical_gradient_ae hD
    (Complex.imCLM.contDiff.comp_contDiffOn hs) (M.source_coordinate_memLp hG hinf L).2
  rw [he] at hx hy
  filter_upwards [hx Wx,hy Wy,
    ae_restrict_mem ((isOpen_physicalPlaneDomain hG).inter isOpen_ball).measurableSet] with x hxr hxi hxD
  rw [hV x, hxr, hxi, weakPairDifferential_covectors]
  congr 1
  have hf' : DifferentiableAt ℝ (fun x => M.function (complexPlaneCoordinates x)) x :=
    ((hs.contDiffAt (hD.mem_nhds (show complexPlaneCoordinates x ∈ D from by
      change x ∈ complexPlaneCoordinates ⁻¹' D
      rw [he]
      exact hxD))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp x
        complexPlaneCoordinates.differentiableAt
  have hr := Complex.reCLM.differentiableAt.comp x hf'
  have hi := Complex.imCLM.differentiableAt.comp x hf'
  have hc := (hΦ.differentiable (by simp) _).hasFDerivAt.comp x
    (hasFDerivAt_planePair hr.hasFDerivAt hi.hasFDerivAt)
  rw [funext (M.reference_barrier_value Φ)]
  exact hc.fderiv

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_BarrierEnergyAssembly
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Turn the proved reference-comparison bound into the total source
barrier energy. The reference is constructed by conformal transport. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity


namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem barrier_energy_from_reference (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (L : ℝ)
    (Wx : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).re)
      (physicalPlaneDomain G ∩ ball 0 L))
    (Wy : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).im)
      (physicalPlaneDomain G ∩ ball 0 L))
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hs : HasCompactSupport Φ)
    {f : EuclideanPlane → ℝ} (W : DeGiorgi.MemW1pWitness 2 f (physicalPlaneDomain G ∩ ball 0 L))
    {r s : ℝ} (hs0 : 0 ≤ s)
    (henergy : (∫ x : EuclideanPlane, ‖planeCovectorGradient (fderiv ℝ Φ x)‖^2) ≤ s^2)
    (herror : (eLpNorm (fun x => W.weakGrad x-planeCovectorGradient
      ((fderiv ℝ Φ (planePair ((M.function (complexPlaneCoordinates x)).re)
        ((M.function (complexPlaneCoordinates x)).im))).comp
          (weakPairDifferential (Wx.weakGrad x) (Wy.weakGrad x)))) 2
      (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal ≤ r) :
    (eLpNorm W.weakGrad 2 (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal ≤ r+s := by
  let U := physicalPlaneDomain G ∩ ball (0 : EuclideanPlane) L
  obtain ⟨V,hV,hVE⟩ := M.smooth_barrier_pullback hG hinf hΦ hs
  have hVr := V.weakGrad_memLp.restrict (ball (0 : EuclideanPlane) L)
  rw [Measure.restrict_restrict measurableSet_ball, inter_comm] at hVr
  have hpart : (∫ x in U, ‖V.weakGrad x‖^2) ≤ s^2 := by
    apply le_trans (setIntegral_mono_set V.weakGrad_norm_memLp.integrable_sq
      (Eventually.of_forall (fun x => sq_nonneg _)) (Eventually.of_forall inter_subset_left))
    exact hVE.trans henergy
  have hn := integral_sq_eq_eLpNorm_toReal_sq hVr.norm
  rw [eLpNorm_norm _] at hn
  have hnorm : (eLpNorm V.weakGrad 2 (volume.restrict U)).toReal ≤ s := by
    rw [hn] at hpart
    nlinarith [ENNReal.toReal_nonneg (a := eLpNorm V.weakGrad 2 (volume.restrict U))]
  have hfield := M.reference_barrier_gradient hG hinf L Wx Wy hΦ V hV
  have heq : (fun x => W.weakGrad x-V.weakGrad x) =ᵐ[volume.restrict U]
      (fun x => W.weakGrad x-planeCovectorGradient
        ((fderiv ℝ Φ (planePair ((M.function (complexPlaneCoordinates x)).re)
          ((M.function (complexPlaneCoordinates x)).im))).comp
            (weakPairDifferential (Wx.weakGrad x) (Wy.weakGrad x)))) := by
    filter_upwards [hfield] with x hx
    rw [hx]
  have hdiff : (eLpNorm (fun x => W.weakGrad x-V.weakGrad x) 2 (volume.restrict U)).toReal ≤ r := by
    rw [eLpNorm_congr_ae heq]
    exact herror
  exact (l2_norm_le_error_add W.weakGrad_memLp hVr).trans (add_le_add hdiff hnorm)

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmallSelectedBarrierEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small selected-coordinate errors give a strict total source barrier
bound, uniformly for any smooth barrier with the specified constants. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem small_selected_barrier_energy (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    {R d A L e t η N : ℝ} (H : ControlledHeight R d)
    {Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    (S : FlattenedSourceSelection M H Wold A L e e)
    (he : 0 ≤ e) (het : e ≤ t) (ht : 0 ≤ t) (hηpos : 0 < η)
    (ζ : ℂ → ℝ) (θ : EuclideanPlane → ℝ)
    (hζ : ∀ z ∈ {z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 L, ζ z = 1)
    (hθ : ∀ x ∈ physicalPlaneDomain G ∩ ball 0 L,
      θ (complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x))) = 1)
    (hp : Continuous (M.compactPrioritySource S.cutoff S.value ζ))
    (hq : Continuous (M.compactHeightSource H (flattenValues S.heightValues) θ))
    (Wp : DeGiorgi.MemW1pWitness 2 (M.compactPrioritySource S.cutoff S.value ζ)
      (physicalPlaneDomain G ∩ ball 0 L))
    (Wq : DeGiorgi.MemW1pWitness 2 (M.compactHeightSource H (flattenValues S.heightValues) θ)
      (physicalPlaneDomain G ∩ ball 0 L))
    (Wx : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).re)
      (physicalPlaneDomain G ∩ ball 0 L))
    (Wy : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).im)
      (physicalPlaneDomain G ∩ ball 0 L))
    (E : DeGiorgi.MemW1pWitness 2 (planeInverseTransport (extendAtInfinity M.function)
      (fun y => θ y*(flattenValues S.heightValues (H.height (complexPlaneCoordinates y))-y 1)))
      (physicalPlaneDomain G))
    (hE : (∫ x in physicalPlaneDomain G, E.weakGrad x 0^2+E.weakGrad x 1^2) ≤ t^2)
    (hheight : ∀ x ∈ physicalPlaneDomain G ∩ ball 0 L,
      |H.height (M.function (complexPlaneCoordinates x))-(M.function (complexPlaneCoordinates x)).im| ≤ e)
    (hN : (eLpNorm (fun x => weakPairDifferential (Wx.weakGrad x) (Wy.weakGrad x)) 2
      (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal ≤ N)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hsΦ : HasCompactSupport Φ)
    {B M₁ M₂ : ℝ} (hB : 0 ≤ B) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hΦb : ∀ z, ‖Φ z‖ ≤ B) (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ M₁)
    (hlip : ∀ z w, ‖fderiv ℝ Φ z-fderiv ℝ Φ w‖ ≤ M₂*‖z-w‖)
    (henergy : (∫ x, ‖planeCovectorGradient (fderiv ℝ Φ x)‖^2) ≤ (η/3)^2)
    (hbudget : M₁*(t+t)+(M₂*(t+t))*N+4*M₁*t < η/3) :
    ∃ W : DeGiorgi.MemW1pWitness 2 (fun x => Φ (planePair
        (M.compactPrioritySource S.cutoff S.value ζ x)
        (M.compactHeightSource H (flattenValues S.heightValues) θ x)))
      (physicalPlaneDomain G ∩ ball 0 L),
      (eLpNorm W.weakGrad 2 (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal < η := by
  obtain ⟨W,hW⟩ := M.selected_barrier_error hG hinf H S ζ θ hζ hθ hp hq Wp Wq Wx Wy E
    ht he he hE hheight (hΦ.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hB hM₁ hM₂ hΦb hbound hlip
  have hfirst : M₁*(e+t) ≤ M₁*(t+t) :=
    mul_le_mul_of_nonneg_left (add_le_add het le_rfl) hM₁
  have hsecond : (M₂*(e+e))*(eLpNorm
      (fun x => weakPairDifferential (Wx.weakGrad x) (Wy.weakGrad x)) 2
      (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal ≤ (M₂*(t+t))*N :=
    mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add het het) hM₂) hN
      ENNReal.toReal_nonneg (mul_nonneg hM₂ (add_nonneg ht ht))
  have hthird : 4*M₁*e ≤ 4*M₁*t := mul_le_mul_of_nonneg_left het (by positivity)
  have herror := hW.trans ((add_le_add (add_le_add hfirst hsecond) hthird))
  have htotal := M.barrier_energy_from_reference hG hinf L Wx Wy hΦ hsΦ W
    (show 0 ≤ η/3 by positivity) henergy herror
  refine ⟨W,?_⟩
  linarith

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FixedDiskCutoffs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.horizontalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed source and target cutoffs are chosen before the near-extremal
model, so their derivative constants do not depend on that model. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 theorem exists_complex_disk_cutoff {r R : ℝ} (hrR : r < R) :
    ∃ f : ℂ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ ball 0 R ∧ (∀ z, f z ∈ Icc (0 : ℝ) 1) ∧
      (∀ z ∈ closedBall 0 r, f z = 1) := by
  obtain ⟨f,hf,hs,hsub,hu,hf1⟩ := exists_smooth_planar_cutoff
    (isCompact_closedBall (0 : ℂ) r) isOpen_ball (closedBall_subset_ball hrR)
  exact ⟨f,hf,hs,hsub,hu,fun z hz => hf1.self_of_nhdsSet z hz⟩

 theorem exists_physical_disk_cutoff {r R : ℝ} (hrR : r < R) :
    ∃ (f : EuclideanPlane → ℝ) (C : ℝ), 0 ≤ C ∧
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ ball 0 R ∧
      (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧ (∀ x ∈ closedBall 0 r, f x = 1) ∧
      (∀ x, ‖fderiv ℝ f x‖ ≤ C) := by
  obtain ⟨g,hg,hgs,hgsub,hgu,hg1⟩ := exists_complex_disk_cutoff hrR
  let f := g ∘ complexPlaneCoordinates
  have hf : ContDiff ℝ ∞ f := hg.comp complexPlaneCoordinates.contDiff
  have hs : HasCompactSupport f := hgs.comp_homeomorph complexPlaneCoordinates.toHomeomorph
  obtain ⟨C,hC⟩ := (hs.fderiv ℝ).exists_bound_of_continuous (hf.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  refine ⟨f,max C 0,le_max_right _ _,hf,hs,?_,fun x => hgu _,?_,
    fun x => (hC x).trans (le_max_left _ _)⟩
  · rw [show f = g ∘ complexPlaneCoordinates.toHomeomorph from rfl, tsupport_comp_eq_preimage]
    intro x hx
    have hz := hgsub hx
    change complexPlaneCoordinates x ∈ ball (0 : ℂ) R at hz
    simpa only [mem_ball, dist_zero_right, complexPlaneCoordinates_norm] using hz
  · intro x hx
    apply hg1
    simpa only [mem_closedBall, dist_zero_right, complexPlaneCoordinates_norm] using hx

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ModelUniformRowEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform image bounds give a uniform energy budget for the reference
rows on the actual source working disk. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem horizontalSection_fderiv_norm_sq (M : CompactScalarModel G u)
    (hG : IsOpen G) {z : ℂ} (hz : (z : Sphere) ∈ G) :
    ‖fderiv ℝ (fun w : ℂ => M.horizontalSection (w : Sphere)) z‖^2 = ‖deriv M.function z‖^2 := by
  have hh : (fun w : ℂ => M.horizontalSection (w : Sphere)) =ᶠ[𝓝 z]
      (fun w => (M.function w).re) := by
    filter_upwards [(hG.preimage OnePoint.continuous_coe).mem_nhds hz] with w hw
    simpa only [extendAtInfinity_coe,finiteCoord_coe] using M.horizontalSection_on_domain hw
  rw [hh.fderiv_eq]
  exact holomorphic_real_fderiv_norm_sq (finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz))

 theorem working_row_energy_le (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (L : ℝ)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ z : ℂ, (z : Sphere) ∈ G → z ∈ ball 0 L → ‖M.function z‖ ≤ K)
    (Wx : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).re)
      (physicalPlaneDomain G ∩ ball 0 L)) :
    (∫ x in physicalPlaneDomain G ∩ ball 0 L, ‖Wx.weakGrad x‖^2) ≤ Real.pi*K^2 := by
  let D := {z : ℂ | (z : Sphere) ∈ G} ∩ ball (0 : ℂ) L
  have hD : IsOpen D := (hG.preimage OnePoint.continuous_coe).inter isOpen_ball
  have he : complexPlaneCoordinates ⁻¹' D = physicalPlaneDomain G ∩ ball 0 L := by
    ext x
    simp only [D, mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_ball, dist_zero_right,
      complexPlaneCoordinates_norm]
    rfl
  have hder := integral_norm_deriv_sq_eq_image_area hD.measurableSet
    (fun z hz => finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz.1))
    (fun z hz w hw he => by
      apply OnePoint.coe_injective
      apply M.conformal.bijOn.injOn hz.1 hw.1
      simpa only [extendAtInfinity_coe] using congrArg ((↑) : ℂ → Sphere) he)
  have hsub : M.function '' D ⊆ closedBall 0 K := by
    rintro _ ⟨z,hz,rfl⟩
    simpa only [mem_closedBall, dist_zero_right] using hbound z hz.1 hz.2
  have hvol : (volume (M.function '' D)).toReal ≤ Real.pi*K^2 := by
    have hv : (volume (M.function '' D)).toReal ≤ (volume (closedBall (0 : ℂ) K)).toReal :=
      ENNReal.toReal_mono measure_closedBall_lt_top.ne (measure_mono hsub)
    simpa only [Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.coe_toReal, NNReal.coe_real_pi, ENNReal.toReal_ofReal hK, mul_comm] using hv
  calc
    _ = ∫ x in physicalPlaneDomain G ∩ ball 0 L,
        ‖fderiv ℝ (fun w : ℂ => M.horizontalSection (w : Sphere)) (complexPlaneCoordinates x)‖^2 := by
      apply integral_congr_ae
      filter_upwards [M.working_horizontal_norm hG hinf L Wx] with x hx
      rw [hx]
    _ = ∫ z in D, ‖fderiv ℝ (fun w : ℂ => M.horizontalSection (w : Sphere)) z‖^2 := by
      rw [← he]
      exact complexPlaneCoordinates_measurePreserving.setIntegral_preimage_emb
        complexPlaneCoordinates.toHomeomorph.measurableEmbedding
          (fun z : ℂ => ‖fderiv ℝ (fun w : ℂ => M.horizontalSection (w : Sphere)) z‖^2) D
    _ = ∫ z in D, ‖deriv M.function z‖^2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hD.measurableSet] with z hz
      exact M.horizontalSection_fderiv_norm_sq hG hz.1
    _ = (volume (M.function '' D)).toReal := hder
    _ ≤ _ := hvol

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ModelUniformJointEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common explicit L2 budget for the actual model's joint reference
differential, obtained from image area and holomorphic row equality. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem working_joint_norm_le (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (L : ℝ)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ z : ℂ, (z : Sphere) ∈ G → z ∈ ball 0 L → ‖M.function z‖ ≤ K)
    (Wx : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).re)
      (physicalPlaneDomain G ∩ ball 0 L))
    (Wy : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).im)
      (physicalPlaneDomain G ∩ ball 0 L)) :
    (eLpNorm (fun x => weakPairDifferential (Wx.weakGrad x) (Wy.weakGrad x)) 2
      (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal ≤ 2*(Real.pi*K^2+1) := by
  have hE := M.working_row_energy_le hG hinf L hK hbound Wx
  have hn := integral_sq_eq_eLpNorm_toReal_sq Wx.weakGrad_norm_memLp
  rw [eLpNorm_norm _] at hn
  rw [hn] at hE
  have hrow : (eLpNorm Wx.weakGrad 2 (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal ≤
      Real.pi*K^2+1 := by
    have ha : 0 ≤ Real.pi*K^2 := mul_nonneg Real.pi_pos.le (sq_nonneg _)
    nlinarith [sq_nonneg ((eLpNorm Wx.weakGrad 2
      (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal-1)]
  have heq := eLpNorm_congr_norm_ae (M.working_rows_norm_eq hG hinf L Wx Wy) (p := 2)
  have hb := (weakPairDifferential_memLp Wx.weakGrad_memLp Wy.weakGrad_memLp).2
  rw [← heq] at hb
  linarith


end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelFixedWorkingBounds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common source and image radii for the appending construction.
The estimates are independent of the finite test family. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

 theorem exterior_source_mono {G : Set Sphere} {a R : ℝ} (haR : a ≤ R)
    (hsource : (((↑) : ℂ → Sphere) '' ball 0 a)ᶜ ⊆ G) :
    (((↑) : ℂ → Sphere) '' ball 0 R)ᶜ ⊆ G :=
  (compl_subset_compl.mpr (image_mono (ball_subset_ball haR))).trans hsource

namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem fixed_working_image_bound (M : CompactScalarModel G u)
    (harea : ExteriorCoefficientAreaTheorem) (hG : IsOpen G)
    {a : ℝ} (ha : 0 < a) (hsource : (((↑) : ℂ → Sphere) '' ball 0 a)ᶜ ⊆ G)
    {z : ℂ} (hz : (z : Sphere) ∈ G) (hzn : ‖z‖ ≤ 67*a) : ‖M.function z‖ ≤ 85*a := by
  have hR : 0 < 17*a := by positivity
  have hsource' := exterior_source_mono (show a ≤ 17*a by linarith) hsource
  have hb := (M.uniform_omitted_and_image_bound harea hG hR hsource').2 z hz
    (show ‖z‖ ≤ 4*(17*a) by linarith)
  linarith

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_AppendingPairData
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite appending construction, before choosing its inner
contours. The resulting fields concern the original source functions. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_appending_pair_data
    {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
    (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcoarea : PlanarSobolevCoarea)
    (hG : IsOpen G) (hconn : IsConnected G) (hinf : OnePoint.infty ∈ G)
    (hTD : IsTotallyDisconnected Gᶜ)
    (hB : IsCompact {z : ℂ | (z : Sphere) ∉ G})
    (hBne : {z : ℂ | (z : Sphere) ∉ G}.Nonempty)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G))
    (hpairs : ∀ i j, i ≠ j → volume ((fun x =>
      (sphereFromPlaneFunction (u i) x,sphereFromPlaneFunction (u j) x)) '' Gᶜ) = 0)
    (hne : Nonempty (CompactScalarModel G u))
    {a δ η : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hη : 0 < η)
    (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ ball 0 a)
    (hsource : (((↑) : ℂ → Sphere) '' ball 0 a)ᶜ ⊆ G) :
    Nonempty (AppendingPairData G u Wold a δ η) := by
  obtain ⟨ζ,hζ,hsζ,hsζ66,hζunit,hζ65⟩ := exists_complex_disk_cutoff
    (show 65*a < 66*a by linarith)
  obtain ⟨θ,Cθ,hCθ,hθ,hsθ,hsθ100,hθunit,hθ85,hθd⟩ := exists_physical_disk_cutoff
    (show 85*a < 100*a by linarith)
  obtain ⟨Φ,r,M₁,M₂,hr,hM₁,hM₂,hΦ,hsΦ,hsΦ4,hΦunit,hΦone,hΦE,hΦD,hΦDD⟩ :=
    exists_physical_small_barrier (show 0 < 4*a by positivity)
      (show 0 < (η/3)^2 by positivity)
  let N := 2*(Real.pi*(85*a)^2+1)
  have hN : 0 ≤ N := by dsimp only [N] <;> positivity
  obtain ⟨t,ht,htbudget⟩ := exists_barrier_error_budget hη hM₁ hM₂ hN
  let b := min t (min δ (min (δ^2) a))
  have hb : 0 < b := by dsimp only [b] <;> positivity
  obtain ⟨e,he,heb,d,hd,hde,M,H,S,hH,hS,E,hHz,hE⟩ := exists_small_selected_height_data
    hsolver hprincipal hgreen harea hsard hsch hcoarea hG hconn hinf hTD hB hBne
    hu hs Wold hne ha hsource (hBa.trans (ball_subset_ball (show a ≤ 2*a by linarith)))
    (100*a) (67*a) θ hθ hsθ hsθ100 hCθ hθunit hθd hb ht
  have het : e ≤ t := (heb.trans_le (min_le_left _ _)).le
  have heδ : e ≤ δ := (heb.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have heδsq : e ≤ δ^2 := (heb.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))).le
  have hea : e ≤ a := (heb.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))).le
  have hζB : ∀ z : ℂ, (z : Sphere) ∉ G → ζ z = 1 := fun z hz =>
    hζ65 z (ball_subset_closedBall ((ball_subset_ball (show a ≤ 65*a by linarith)) (hBa hz)))
  have hθF : ∀ x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G), θ x = 1 := by
    intro x hx
    apply hθ85
    have hbnd := (M.uniform_omitted_and_image_bound harea hG ha hsource).1
      (complexPlaneCoordinates x) hx
    rw [mem_closedBall_zero_iff]
    have hn : ‖x‖ ≤ 3*a := by simpa only [complexPlaneCoordinates_norm] using hbnd
    linarith
  have hsζ67 : tsupport ζ ⊆ ball 0 (67*a) :=
    hsζ66.trans (ball_subset_ball (by linarith))
  obtain ⟨hc,hcomp,⟨Wt⟩,hpair⟩ := S.compact_tests M hsard hsch hcoarea
    hG hconn hinf hTD hu hs hpairs H hHz Wold ζ hζ hsζ hζB hsζ67 θ hθ hsθ hsθ100 hθF
  let p := M.compactPrioritySource S.cutoff S.value ζ
  let q := M.compactHeightSource H (flattenValues S.heightValues) θ
  have hpc : Continuous p := hc (Fin.succ (0 : Fin (m+1)))
  have hqc' : Continuous q := hc 0
  have hps : HasCompactSupport p := hcomp (Fin.succ (0 : Fin (m+1)))
  have hqs : HasCompactSupport q := hcomp 0
  let Wp : DeGiorgi.MemW1pWitness 2 p (physicalPlaneDomain G) := Wt (Fin.succ (0 : Fin (m+1)))
  let Wq : DeGiorgi.MemW1pWitness 2 q (physicalPlaneDomain G) := Wt 0
  have hopen := (isOpen_physicalPlaneDomain hG).inter (isOpen_ball (x := (0 : EuclideanPlane)) (ε := 65*a))
  let Wp65 := Wp.restrict hopen inter_subset_left
  let Wq65 := Wq.restrict hopen inter_subset_left
  obtain ⟨⟨Wx⟩,⟨Wy⟩⟩ := M.working_coordinate_witnesses hG hinf (65*a)
  let S65 := S.restrictWorking M hG hinf (show 65*a ≤ 67*a by linarith)
  have hζwork : ∀ z ∈ {z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 (65*a), ζ z = 1 :=
    fun z hz => hζ65 z (ball_subset_closedBall hz.2)
  have hθwork : ∀ x ∈ physicalPlaneDomain G ∩ ball 0 (65*a),
      θ (complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x))) = 1 := by
    intro x hx
    apply hθ85
    rw [mem_closedBall_zero_iff]
    have hbnd := M.fixed_working_image_bound harea hG ha hsource hx.1
      (show ‖complexPlaneCoordinates x‖ ≤ 67*a by
        rw [complexPlaneCoordinates_norm]; have := mem_ball_zero_iff.mp hx.2; linarith)
    simpa only [← complexPlaneCoordinates_norm (complexPlaneCoordinates.symm _),
      complexPlaneCoordinates.apply_symm_apply] using hbnd
  have hheight : ∀ x ∈ physicalPlaneDomain G ∩ ball 0 (65*a),
      |H.height (M.function (complexPlaneCoordinates x))-(M.function (complexPlaneCoordinates x)).im| ≤ e := by
    intro x hx
    apply (hH _ _).le
    rw [mem_closedBall_zero_iff]
    have hbnd := M.fixed_working_image_bound harea hG ha hsource hx.1
      (show ‖complexPlaneCoordinates x‖ ≤ 67*a by
        rw [complexPlaneCoordinates_norm]; have := mem_ball_zero_iff.mp hx.2; linarith)
    linarith
  have hNwork := M.working_joint_norm_le hG hinf (65*a)
    (show 0 ≤ 85*a by positivity) (fun z hz hzn => M.fixed_working_image_bound harea hG ha hsource hz
      (by have := mem_ball_zero_iff.mp hzn; linarith)) Wx Wy
  have hsmall : ∀ c : EuclideanPlane,
      ∃ V : DeGiorgi.MemW1pWitness 2 (fun x => Φ (planePair (p x) (q x)-c))
        (physicalPlaneDomain G ∩ ball 0 (65*a)),
        (eLpNorm V.weakGrad 2 (volume.restrict (physicalPlaneDomain G ∩ ball 0 (65*a)))).toReal < η := by
    intro c
    obtain ⟨hcs,hcc,_,hcu,_,hcD,hcDD⟩ := translatedPhysicalBarrier_data hΦ hsΦ hsΦ4 hΦunit hΦone hΦD hΦDD c
    have hcE : (∫ x, ‖planeCovectorGradient (fderiv ℝ (translatedPhysicalBarrier Φ c) x)‖^2) ≤ (η/3)^2 := by
      rw [translatedPhysicalBarrier_energy (hΦ.differentiable (by simp))]
      exact hΦE.le
    exact M.small_selected_barrier_energy hG hinf H S65 he.le het ht.le hη ζ θ hζwork hθwork
      hpc hqc' Wp65 Wq65 Wx Wy E hE.le hheight hNwork hcs hcc
      (show (0 : ℝ) ≤ 1 by norm_num) hM₁ hM₂
      (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hcu z).1]; exact (hcu z).2)
      hcD hcDD hcE htbudget
  refine ⟨{
    old := fun i => flattenValues (S.oldValues i) ∘ u i
    p := p, q := q, old_continuous := ?_, old_compact := ?_
    old_witness := S.oldWitness
    old_close := fun i => (S.old_errors M hδ heδ heδsq i).1
    old_error := fun i => (S.old_errors M hδ heδ heδsq i).2
    p_continuous := hpc, q_continuous := hqc', p_compact := hps, q_compact := hqs
    p_witness := Wp, q_witness := Wq, pair_null := hpair
    barrier := Φ, radius := r, radius_pos := hr, barrier_smooth := hΦ, barrier_compact := hsΦ
    barrier_support := hsΦ4, barrier_unit := hΦunit, barrier_one := hΦone
    small_energy := hsmall, trace_bound := ?_, outer_margin := ?_ }⟩
  · intro i
    exact (flattenValues_lipschitz (S.old_open i).measurableSet).continuous.comp (hu i)
  · intro i
    exact (hs i).comp_left (flattenValues_zero _)
  · intro z hz
    cases z using OnePoint.rec with
    | infty => exact (hz hinf).elim
    | coe z =>
      have hh := M.selected_pair_trace_bound hsard hsch hG hconn hinf hTD H S
        (M.uniform_omitted_and_image_bound harea hG ha hsource).1
        (fun z hz => (hH z (closedBall_subset_closedBall (show 3*a ≤ 100*a by linarith) hz)).le)
        ζ hζB θ hθF hz
      exact hh.trans (by linarith)
  · intro x hx hx63 hx65 c hc
    have hζx := hζ65 (complexPlaneCoordinates x)
      (mem_closedBall_zero_iff.mpr (by simpa only [complexPlaneCoordinates_norm] using hx65))
    have himage := M.fixed_working_image_bound harea hG ha hsource hx
      (show ‖complexPlaneCoordinates x‖ ≤ 67*a by rw [complexPlaneCoordinates_norm]; linarith)
    have hθx := hθ85 (complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x)))
      (mem_closedBall_zero_iff.mpr (by
        simpa only [← complexPlaneCoordinates_norm (complexPlaneCoordinates.symm _),
          complexPlaneCoordinates.apply_symm_apply] using himage))
    have hHx := (hH (M.function (complexPlaneCoordinates x))
      (mem_closedBall_zero_iff.mpr (by linarith))).le
    have hxs : complexPlaneCoordinates x ∉ ⋃ n, support (S.cutoff n) := by
      intro hh
      obtain ⟨n,hn⟩ := mem_iUnion.mp hh
      have hn' := mem_ball_zero_iff.mp (hS n hn)
      rw [complexPlaneCoordinates_norm] at hn'
      linarith
    have hm := M.selected_pair_outer_margin (r := 4*a) (σ := a) (C := 8*a) (v := e)
      harea H S ha hsource ζ θ hx hζx hθx hHx hxs
      (show 2*a ≤ ‖x‖ by linarith) hc (by linarith)
    calc
      5*a = 4*a+a := by ring
      _ ≤ ‖planePair (p x) (q x)-c‖ := hm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_BoundedEnergyWeakClosure
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.horizontalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Almost everywhere convergence of bounded continuous scalars and a
uniform global Dirichlet budget produce a global weak gradient. Compact
support is needed only for the test functions, not for a common support
of the approximating scalars. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem weakPartial_of_bounded_ae_pointwise_weak_limit
    {u : ℕ → EuclideanPlane → ℝ} {v : EuclideanPlane → ℝ}
    (hu : ∀ n, Continuous (u n)) {C : ℝ}
    (hb : ∀ n x, ‖u n x‖ ≤ C)
    (hp : ∀ᵐ x ∂volume, Tendsto (fun n => u n x) atTop (𝓝 (v x)))
    {i : Fin 2} {g : ℕ → EuclideanPlane → ℝ}
    (hw : ∀ n, DeGiorgi.HasWeakPartialDeriv i (g n) (u n) univ)
    (G : Lp ℝ 2 (volume : Measure EuclideanPlane))
    (hG : ∀ w : Lp ℝ 2 (volume : Measure EuclideanPlane),
      Tendsto (fun n => ∫ x, g n x*w x) atTop (𝓝 (∫ x, G x*w x))) :
    DeGiorgi.HasWeakPartialDeriv i G v univ := by
  intro φ hφ hs _
  simp only [Measure.restrict_univ]
  let ψ := fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)
  have hψ : Continuous ψ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsψ : HasCompactSupport ψ := hs.fderiv_apply (𝕜 := ℝ) _
  have hl : Tendsto (fun n => ∫ x, u n x*ψ x) atTop (𝓝 (∫ x, v x*ψ x)) := by
    apply tendsto_integral_of_dominated_convergence (bound := fun x => C*‖ψ x‖)
    · exact fun n => (hu n).aestronglyMeasurable.mul hψ.aestronglyMeasurable
    · exact (hψ.integrable_of_hasCompactSupport hsψ).norm.const_mul C
    · exact fun n => Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hb n x) (norm_nonneg _)
    · exact hp.mono (fun x hx => hx.mul_const _)
  have hr := tendsto_pairings_with_memLp_test hG (hφ.continuous.memLp_of_hasCompactSupport hs)
  have he : (fun n => ∫ x, u n x*ψ x) = (fun n => -(∫ x, g n x*φ x)) := by
    funext n
    simpa only [Measure.restrict_univ] using hw n φ hφ hs (subset_univ _)
  rw [he] at hl
  exact tendsto_nhds_unique hl hr.neg

 theorem exists_bounded_energy_weak_gradient
    {u : ℕ → EuclideanPlane → ℝ} {v : EuclideanPlane → ℝ}
    (W : ℕ → EuclideanPlane → EuclideanPlane)
    (hWL : ∀ n, MemLp (W n) 2 volume)
    (hW : ∀ n, DeGiorgi.HasWeakGrad (W n) (u n) univ)
    (hu : ∀ n, Continuous (u n)) {C : ℝ} (hb : ∀ n x, ‖u n x‖ ≤ C)
    (hp : ∀ᵐ x ∂volume, Tendsto (fun n => u n x) atTop (𝓝 (v x)))
    {B : ℝ} (hB : ∀ n, (∫ x, ‖W n x‖^2) ≤ B) :
    ∃ g : EuclideanPlane → EuclideanPlane,
      MemLp g 2 volume ∧ DeGiorgi.HasWeakGrad g v univ ∧ (∫ x, ‖g x‖^2) ≤ B := by
  let u₀ := fun n x => W n x (0 : Fin 2)
  let u₁ := fun n x => W n x (1 : Fin 2)
  have hm₀ (n : ℕ) : MemLp (u₀ n) 2 volume := by
    exact memLp_piLp_iff.mp (hWL n) 0
  have hm₁ (n : ℕ) : MemLp (u₁ n) 2 volume := by
    exact memLp_piLp_iff.mp (hWL n) 1
  have he (n : ℕ) : (∫ x, u₀ n x^2+u₁ n x^2) ≤ B := by
    simpa only [plane_norm_sq] using hB n
  have hn (n : ℕ) : ‖(hm₀ n).toLp (u₀ n)‖ ≤ B+1 ∧ ‖(hm₁ n).toLp (u₁ n)‖ ≤ B+1 := by
    have h0 : ‖(hm₀ n).toLp (u₀ n)‖^2 = ∫ x, u₀ n x^2 := by
      rw [Lp.norm_toLp,integral_sq_eq_eLpNorm_toReal_sq (hm₀ n)]
    have h1 : ‖(hm₁ n).toLp (u₁ n)‖^2 = ∫ x, u₁ n x^2 := by
      rw [Lp.norm_toLp,integral_sq_eq_eLpNorm_toReal_sq (hm₁ n)]
    have hh := he n
    rw [integral_add (hm₀ n).integrable_sq (hm₁ n).integrable_sq,← h0,← h1] at hh
    constructor <;> nlinarith [sq_nonneg (‖(hm₀ n).toLp (u₀ n)‖-1),
      sq_nonneg (‖(hm₁ n).toLp (u₁ n)‖-1),sq_nonneg ‖(hm₀ n).toLp (u₀ n)‖,
      sq_nonneg ‖(hm₁ n).toLp (u₁ n)‖]
  obtain ⟨G₀,_,s,hs,h0⟩ := exists_L2_weak_subsequence volume u₀ hm₀ (B+1) (fun n => (hn n).1)
  obtain ⟨G₁,_,t,ht,h1⟩ := exists_L2_weak_subsequence volume (u₁ ∘ s)
    (fun n => hm₁ (s n)) (B+1) (fun n => (hn (s n)).2)
  let σ := s ∘ t
  have hσ : StrictMono σ := hs.comp ht
  have h0' (w : Lp ℝ 2 (volume : Measure EuclideanPlane)) := (h0 w).comp ht.tendsto_atTop
  let g : EuclideanPlane → EuclideanPlane := fun x => planePair (G₀ x) (G₁ x)
  refine ⟨g,?_,?_,?_⟩
  · apply memLp_piLp_iff.mpr
    intro i
    fin_cases i
    · change MemLp (fun x => planePair (G₀ x) (G₁ x) 0) 2 volume
      simpa only [planePair_zero] using Lp.memLp G₀
    · change MemLp (fun x => planePair (G₀ x) (G₁ x) 1) 2 volume
      simpa only [planePair_one] using Lp.memLp G₁
  · intro i
    fin_cases i
    · change DeGiorgi.HasWeakPartialDeriv 0 (fun x => planePair (G₀ x) (G₁ x) 0) v univ
      simpa only [planePair_zero] using weakPartial_of_bounded_ae_pointwise_weak_limit (fun n => hu (σ n))
        (fun n => hb (σ n)) (hp.mono (fun _ hx => hx.comp hσ.tendsto_atTop))
        (fun n => hW (σ n) 0) G₀ h0'
    · change DeGiorgi.HasWeakPartialDeriv 1 (fun x => planePair (G₀ x) (G₁ x) 1) v univ
      simpa only [planePair_one] using weakPartial_of_bounded_ae_pointwise_weak_limit (fun n => hu (σ n))
        (fun n => hb (σ n)) (hp.mono (fun _ hx => hx.comp hσ.tendsto_atTop))
        (fun n => hW (σ n) 1) G₁ h1
  · have hh := paired_L2_energy_le (fun n => hm₀ (σ n)) (fun n => hm₁ (σ n)) G₀ G₁
      (ε := fun _ => 0) tendsto_const_nhds
      (Eventually.of_forall (fun n => by simpa only [add_zero] using he (σ n)))
      (h0' G₀) (h1 G₁)
    simpa only [g,plane_norm_sq,planePair_zero,planePair_one] using hh

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactScalarModelFromCircle
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed circle model belongs to the coefficient-extremal class. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
 theorem CompactScalarCircleModel.exists_coefficient
    {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
    (M : CompactScalarCircleModel G u) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) :
    ∃ b : ℂ, HasPrincipalCoefficient M.function b := by
  have hm : ∀ᶠ z : ℂ in cobounded ℂ, (z : Sphere) ∈ G := by
    have ht : Tendsto (fun z : ℂ => (z : Sphere)) (cobounded ℂ) (𝓝 OnePoint.infty) := by
      simpa only [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] using
        (OnePoint.tendsto_coe_infty : Tendsto (fun z : ℂ => (z : Sphere)) _ _)
    exact ht.eventually (hG.mem_nhds hinf)
  apply exists_principal_coefficient
  · exact hm.mono fun z hz => finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz)
  · simpa only [extendAtInfinity_coe, finiteCoord_coe] using M.normalized.2

 theorem nonempty_compactScalarModel_of_circle
    {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (hs : ∀ i, HasCompactSupport (u i))
    (hM : Nonempty (CompactScalarCircleModel G u)) : Nonempty (CompactScalarModel G u) := by
  obtain ⟨M⟩ := hM
  obtain ⟨b, hb⟩ := M.exists_coefficient hG hinf
  exact ⟨M.toCompactScalarModel hinf hs b hb⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PublishedAppendingPair
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite appending pairs obtained from finite-list conformal models. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r00162c_1 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_appending_pair_of_published_inputs
    (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
    (hsob : PlanarSobolevCoarea)
    (hcross : UnitDiskAlternatingContinua)
    (hplane : PlanarLipschitzFiberCoarea)
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit) (hzero : HurwitzZeroFreeLimit)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {m : ℕ} (u : Fin m → EuclideanPlane → ℝ)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (H : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G))
    (hpair : ∀ i j, i ≠ j → volume
      ((fun p => (sphereFromPlaneFunction (u i) p, sphereFromPlaneFunction (u j) p)) '' Gᶜ) = 0) :
    ∀ {a δ η : ℝ}, 0 < a → 0 < δ → 0 < η →
      {z : ℂ | (z : Sphere) ∉ G} ⊆ ball 0 a →
      {z : ℂ | (z : Sphere) ∉ G}.Nonempty →
      Nonempty (AppendingPairData G u H a δ η) := by
  intro a δ η ha hδ hη hBa hBne
  have hsource : (((↑) : ℂ → Sphere) '' ball 0 a)ᶜ ⊆ G := by
    intro p hp
    by_contra hpG
    cases p using OnePoint.rec with
    | infty => exact hpG hinf
    | coe z => exact hp ⟨z,hBa hpG,rfl⟩
  have hB : IsCompact {z : ℂ | (z : Sphere) ∉ G} :=
    isCompact_finite_preimage hG.isClosed_compl (not_not.mpr hinf)
  have hmodel := exists_signed_compact_scalar_circle_model hcross hplane hcoarea hLusin
    hsard hsch hsep hcollar hselect hgreen harea hcompact hfinite hmontel hhurwitz hzero
    harcs hstandard hpath hdual hlift hG hconn hinf hTD u hu hs H hpair
  exact exists_appending_pair_data hsolver hprincipal hgreen harea hsard hsch hsob
    hG hconn hinf hTD hB hBne hu hs H hpair
    (nonempty_compactScalarModel_of_circle hG hinf hs hmodel) ha hδ hη hBa hsource

theorem finiteAppendingSupply_of_published_inputs
    (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
    (hsob : PlanarSobolevCoarea)
    (hcross : UnitDiskAlternatingContinua)
    (hplane : PlanarLipschitzFiberCoarea)
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit) (hzero : HurwitzZeroFreeLimit)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {a : ℝ} (ha : 0 < a) (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ ball 0 a)
    (hBne : {z : ℂ | (z : Sphere) ∉ G}.Nonempty) : FiniteAppendingSupply G a := by
  intro T δ η hδ hη
  exact exists_appending_pair_of_published_inputs hsolver hprincipal hsob hcross hplane hcoarea hLusin
    hsard hsch hsep hcollar hselect hgreen harea hcompact hfinite hmontel hhurwitz hzero
    harcs hstandard hpath hdual hlift hG hconn hinf hTD T.test T.continuous T.compact
    T.witness T.pair_null ha hδ hη hBa hBne

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ScalarModelSequenceLimit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A sequence of actual finite scalar circle models has a normalized
conformal subsequential limit on the entire fixed source domain. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem scalar_models_conformal_limit
    (harea : ExteriorCoefficientAreaTheorem)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit)
    (hzero : HurwitzZeroFreeLimit)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) {a : ℝ} (ha : 0 < a)
    (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ ball 0 a)
    (T : ℕ → FiniteCompactTests G)
    (M : ∀ n, CompactScalarCircleModel G (T n).test) :
    ∃ (s : ℕ → ℕ) (F : ℂ → ℂ), StrictMono s ∧
      TendstoLocallyUniformlyOn (fun n => (M (s n)).function) F atTop
        {z : ℂ | (z : Sphere) ∈ G} ∧
      IsPrincipalNormalized (extendAtInfinity F) ∧
      IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G) := by
  let D : Set ℂ := {z : ℂ | (z : Sphere) ∈ G}
  have hD : IsOpen D := hG.preimage OnePoint.continuous_coe
  have hext : {z : ℂ | a ≤ ‖z‖} ⊆ D := by
    intro z hz
    by_contra hn
    have hb := hBa hn
    rw [mem_ball,dist_zero_right] at hb
    exact (not_lt_of_ge hz) hb
  have hDn : D.Nonempty := by
    refine ⟨(a : ℂ), hext ?_⟩
    simp only [mem_ofPred_eq,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha,le_refl]
  have hDc : IsConnected D := ⟨hDn,
    (finite_part_connected_unbounded hconn.isPreconnected
      (mem_interior_iff_mem_nhds.mpr (hG.mem_nhds hinf))).1⟩
  let f : ℕ → Sphere → Sphere := fun n => extendAtInfinity (M n).function
  let V : ℕ → Set Sphere := fun n => f n '' G
  have hV : ∀ n, IsOpen (V n) := fun n => (M n).circle.1
  choose fi hfi using fun n => (M n).conformal.exists_smooth_inverse hG (hV n)
  have hsource : (((↑) : ℂ → Sphere) '' ball 0 a)ᶜ ⊆ G := by
    intro p hp
    cases p using OnePoint.rec with
    | infty => exact hinf
    | coe z =>
        apply hext
        change a ≤ ‖z‖
        by_contra hz
        exact hp ⟨z, by simpa only [mem_ball,dist_zero_right] using lt_of_not_ge hz, rfl⟩
  have hclosed : (((↑) : ℂ → Sphere) '' closedBall 0 a)ᶜ ⊆ G :=
    (compl_subset_compl.mpr (image_mono ball_subset_closedBall)).trans hsource
  obtain ⟨s,F,hs,hlim,hnorm,hconf⟩ := exists_conformal_limit_of_sphere_models
    harea hmontel hhurwitz hzero f fi (fun _ => G) V hfi hV
    (fun _ => hD) (fun _ => hDc) (fun _ _ _ => Subset.rfl)
    (fun _ _ hz => hz) (fun n p hp => (M n).conformal.1 p (by
      obtain ⟨z,hz,rfl⟩ := hp
      exact hz)) ha (fun _ => hsource)
    (fun n p hp => (M n).conformal.1 p (hclosed hp)) (fun n => (M n).normalized)
    (fun z hz => hext (by
      change a ≤ ‖z‖
      change 2*a ≤ ‖z‖ at hz
      linarith))
  have hfinite : (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}) = G := by
    ext p
    cases p using OnePoint.rec with
    | infty => simp [hinf]
    | coe z => simp [D]
  refine ⟨s,F,hs,?_,hnorm,?_⟩
  · simpa only [iUnion_const, f, extendAtInfinity_coe, finiteCoord_coe] using hlim
  · simpa only [iUnion_const,hfinite] using hconf

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RecursiveCircleModels
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Select actual circle models for the recursively constructed finite
families, then extract their normalized conformal limit. The model supply
in the intermediate construction is discharged by the published-input
finite-list theorem below. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T

 theorem exists_models_and_limit
    (harea : ExteriorCoefficientAreaTheorem)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit)
    (hzero : HurwitzZeroFreeLimit)
    (hconn : IsConnected G)
    (hmodels : ∀ S : FiniteCompactTests G, Nonempty (CompactScalarCircleModel G S.test)) :
    ∃ M : ∀ n, CompactScalarCircleModel G (states n).family.test,
      ∃ (s : ℕ → ℕ) (F : ℂ → ℂ), StrictMono s ∧
        TendstoLocallyUniformlyOn (fun n => (M (s n)).function) F atTop
          {z : ℂ | (z : Sphere) ∈ G} ∧
        IsPrincipalNormalized (extendAtInfinity F) ∧
        IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G) := by
  let M := fun n => Classical.choice (hmodels (states n).family)
  obtain ⟨s,F,hs,hlim,hnorm,hconf⟩ := scalar_models_conformal_limit
    harea hmontel hhurwitz hzero hG hconn hinf ha hBa (fun n => (states n).family) M
  exact ⟨M,s,F,hs,hlim,hnorm,hconf⟩

end AppendingSequence
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r00162c_2 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_recursive_models_of_published_inputs
    (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
    (hsob : PlanarSobolevCoarea)
    (hcross : UnitDiskAlternatingContinua)
    (hplane : PlanarLipschitzFiberCoarea)
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit) (hzero : HurwitzZeroFreeLimit)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {a : ℝ} (ha : 0 < a) (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ ball 0 a)
    (hBne : {z : ℂ | (z : Sphere) ∉ G}.Nonempty)
    {ε : ℝ} (hε : 0 < ε) (T : FiniteCompactTests G) :
    ∃ hsupply : FiniteAppendingSupply G a,
      let states := appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T
      ∃ M : ∀ n, CompactScalarCircleModel G (states n).family.test,
        ∃ (s : ℕ → ℕ) (F : ℂ → ℂ), StrictMono s ∧
          TendstoLocallyUniformlyOn (fun n => (M (s n)).function) F atTop
            {z : ℂ | (z : Sphere) ∈ G} ∧
          IsPrincipalNormalized (extendAtInfinity F) ∧
          IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G) := by
  let hsupply := finiteAppendingSupply_of_published_inputs hsolver hprincipal hsob hcross hplane
    hcoarea hLusin hsard hsch hsep hcollar hselect hgreen harea hcompact hfinite
    hmontel hhurwitz hzero harcs hstandard hpath hdual hlift hG hconn hinf hTD ha hBa hBne
  refine ⟨hsupply, ?_⟩
  apply AppendingSequence.exists_models_and_limit hsupply hsard hsch hG hinf hTD
    ha hBa hε T harea hmontel hhurwitz hzero hconn
  intro S
  exact exists_signed_compact_scalar_circle_model hcross hplane hcoarea hLusin hsard hsch hsep hcollar hselect hgreen harea hcompact hfinite hmontel hhurwitz hzero
    harcs hstandard hpath hdual hlift hG hconn hinf hTD S.test S.continuous S.compact
    S.witness S.pair_null

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_DustSobolevExtension
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact continuous Sobolev functions extend across removable dust.
The approximate global gradients come from the actual recursive finite
models, and a second weak limit removes the approximation error. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r00162c_3 : BorelSpace Sphere := ⟨rfl⟩
theorem dust_sobolev_extension_of_published_inputs
    (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
    (hsob : PlanarSobolevCoarea)
    (hcross : UnitDiskAlternatingContinua)
    (hplane : PlanarLipschitzFiberCoarea)
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit) (hzero : HurwitzZeroFreeLimit)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {a : ℝ} (ha : 0 < a) (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ ball 0 a)
    (hBne : {z : ℂ | (z : Sphere) ∉ G}.Nonempty)
    (hrem : IsConformallyRemovable Gᶜ)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (hs : HasCompactSupport u)
    (W : DeGiorgi.MemW1pWitness 2 u (physicalPlaneDomain G)) :
    ∃ V : DeGiorgi.MemW1pWitness 2 u univ,
      (∫ x, ‖V.weakGrad x‖^2) ≤ (‖W.weakGrad_memLp.toLp W.weakGrad‖+1)^2 := by
  let N := ‖W.weakGrad_memLp.toLp W.weakGrad‖
  let e := fun n : ℕ => 1/((n:ℝ)+1)
  have hepos (n : ℕ) : 0 < e n := by dsimp only [e] <;> positivity
  have hele (n : ℕ) : e n ≤ 1 := by
    dsimp only [e]
    apply (div_le_one (by positivity)).mpr
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have het : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let T := FiniteCompactTests.singleton u hu hs W
  have hap (n : ℕ) : ∃ (v : C(Sphere,ℝ)) (g : EuclideanPlane → EuclideanPlane),
      (∀ p, |v p-sphereFromPlaneFunction u p| ≤ e n/4) ∧
      MemLp g 2 volume ∧ DeGiorgi.HasWeakGrad g (fun x => v (planeSphere x)) univ ∧
      (∫ x, ‖g x‖^2) ≤ (N+e n/4)^2 := by
    obtain ⟨hsupply,M,σ,F,hσ,hlim,hnorm,hF⟩ := exists_recursive_models_of_published_inputs
      hsolver hprincipal hsob hcross hplane hcoarea hLusin hsard hsch hsep hcollar hselect
      hgreen harea hcompact hfinite hmontel hhurwitz hzero harcs hstandard hpath hdual hlift
      hG hconn hinf hTD ha hBa hBne (hepos n) T
    exact AppendingSequence.exists_tracked_global_weak_limit hsupply hsard hsch hG hinf hTD
      ha hBa (hepos n) T hprincipal harea hconn hrem M hσ hnorm hF hlim (0 : Fin 1)
  choose v g hclose hg hw hE using hap
  have hvcont (n : ℕ) : Continuous (fun x => v n (planeSphere x)) :=
    (v n).continuous.comp continuous_planeSphere
  obtain ⟨C,hC⟩ := hu.bounded_above_of_compact_support hs
  have hbound (n : ℕ) (x : EuclideanPlane) : ‖v n (planeSphere x)‖ ≤ C+1 := by
    have hh : |v n (planeSphere x)-u x| ≤ e n/4 := by
      simpa only [planeSphere,sphereFromPlaneFunction_coe,complexPlaneCoordinates.symm_apply_apply]
        using hclose n (planeSphere x)
    calc
      _ = ‖(v n (planeSphere x)-u x)+u x‖ := by congr 1; ring
      _ ≤ ‖v n (planeSphere x)-u x‖+‖u x‖ := norm_add_le _ _
      _ ≤ e n/4+C := add_le_add (by simpa only [Real.norm_eq_abs] using hh) (hC x)
      _ ≤ C+1 := by linarith [hele n]
  have hp (x : EuclideanPlane) :
      Tendsto (fun n => v n (planeSphere x)) atTop (𝓝 (u x)) := by
    apply Metric.tendsto_atTop.mpr
    intro δ hδ
    have ht : Tendsto (fun n => e n/4) atTop (𝓝 0) := by simpa using het.div_const 4
    obtain ⟨n,hn⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
    refine ⟨n,fun k hk => ?_⟩
    have hh : |v k (planeSphere x)-u x| ≤ e k/4 := by
      simpa only [planeSphere,sphereFromPlaneFunction_coe,complexPlaneCoordinates.symm_apply_apply]
        using hclose k (planeSphere x)
    simpa only [Real.dist_eq] using hh.trans_lt (hn k hk)
  have henergy (n : ℕ) : (∫ x, ‖g n x‖^2) ≤ (N+1)^2 := by
    apply (hE n).trans
    have hN : 0 ≤ N := norm_nonneg _
    have hnp : 0 ≤ N+e n/4 := by positivity
    gcongr
    linarith [hele n]
  obtain ⟨G,hGmem,hGweak,hGE⟩ := exists_bounded_energy_weak_gradient g hg hw hvcont hbound
    (Eventually.of_forall hp) henergy
  let V : DeGiorgi.MemW1pWitness 2 u univ := {
    memLp := by simpa only [Measure.restrict_univ] using hu.memLp_of_hasCompactSupport hs
    weakGrad := G
    weakGrad_component_memLp := fun i => by
      simpa only [Measure.restrict_univ] using memLp_piLp_iff.mp hGmem i
    isWeakGrad := hGweak }
  exact ⟨V,hGE⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedMaskGlobalSobolev
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed matched masks extend across their actual residual
removable dust. All conditional inputs are exactly those of the proved
dust Sobolev theorem; no trace or extension conclusion is assumed. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}
variable [Encodable D.IndexedMatchedPair]

 local instance localInst_r00162c_4 : BorelSpace Sphere := ⟨rfl⟩
theorem MatchedRealMask.global_sobolev_of_published_inputs_oai
    (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
    (hsob : PlanarSobolevCoarea)
    (hcross : UnitDiskAlternatingContinua)
    (hplane : PlanarLipschitzFiberCoarea)
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit) (hzero : HurwitzZeroFreeLimit)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    {E : D.MatchedRoundDisks} {hG : IsOpen G} {hf : IsConformalEquivalence f G (f '' G)}
    {φ : Sphere → ℝ} {L : ℝ≥0} {m : ℕ} (M : MatchedRealMask E hG hf φ L m)
    (hinf : OnePoint.infty ∈ G)
    (hb : ContDiffOn ℝ 1 (D.realSelectedScalar hG hf φ) (realPlaneDomain G))
    (hb2 : MemLp (fderiv ℝ (D.realSelectedScalar hG hf φ)) 2 (volume.restrict (realPlaneDomain G))) :
    Nonempty (DeGiorgi.MemW1pWitness 2
      (D.realMaskValue E hG hf φ L M.cutoff ∘ euclideanPlaneCoordinates) univ) := by
  let O := maskDomain G M.neighborhood
  obtain ⟨H⟩ := M.sobolev hb hb2
  have hi : OnePoint.infty ∈ O := Or.inl hinf
  have hu : Continuous (D.realMaskValue E hG hf φ L M.cutoff ∘ euclideanPlaneCoordinates) :=
    M.continuous.comp euclideanPlaneCoordinates.continuous
  have hus : HasCompactSupport (D.realMaskValue E hG hf φ L M.cutoff ∘ euclideanPlaneCoordinates) :=
    M.compact.comp_homeomorph euclideanPlaneCoordinates.toHomeomorph
  by_cases hempty : Oᶜ = ∅
  · have he : O = univ := by
      apply Set.eq_univ_of_forall
      intro q
      by_contra hq
      have hq' : q ∈ Oᶜ := hq
      rw [hempty] at hq'
      exact hq'
    simpa only [O,he,physicalPlaneDomain,preimage_univ] using (show Nonempty
      (DeGiorgi.MemW1pWitness 2 (D.realMaskValue E hG hf φ L M.cutoff ∘ euclideanPlaneCoordinates)
        (physicalPlaneDomain O)) from ⟨H⟩)
  · have hne : {z : ℂ | (z : Sphere) ∉ O}.Nonempty := by
      obtain ⟨q,hq⟩ := Set.nonempty_iff_ne_empty.mpr hempty
      cases q using OnePoint.rec with
      | infty => exact (hq hi).elim
      | coe z => exact ⟨z,hq⟩
    obtain ⟨a,ha,hbound⟩ := ((OnePoint.isOpen_iff_of_mem hi).mp M.domain_open).2.isBounded.exists_pos_norm_lt
    obtain ⟨V,_⟩ := dust_sobolev_extension_of_published_inputs hsolver hprincipal hsob hcross hplane
      hcoarea hLusin hsard hsch hsep hcollar hselect hgreen harea hcompact hfinite hmontel
      hhurwitz hzero harcs hstandard hpath hdual hlift M.domain_open M.domain_connected hi M.domain_dust
      ha (fun z hz => by simpa only [mem_ball,dist_zero_right] using hbound z hz)
      hne M.domain_removable hu hus H
    exact ⟨V⟩

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

theorem solution : type_of% @OAI.CircleDomainRigidity.MatchedConformalEnds.MatchedRealMask.global_sobolev_of_published_inputs_oai := @OAI.CircleDomainRigidity.MatchedConformalEnds.MatchedRealMask.global_sobolev_of_published_inputs_oai
