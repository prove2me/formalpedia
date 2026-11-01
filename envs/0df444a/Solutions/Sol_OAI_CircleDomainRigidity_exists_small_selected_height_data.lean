-- Prove2me | solution 1 for OAI.CircleDomainRigidity.exists_small_selected_height_data
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T05:51:57.930782+00:00
-- url     : https://prove2.me/submissions/e4977a57-e9b2-4528-a3fc-4a334b904527

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C010
import Theorems.Thm_OAI_CircleDomainRigidity_exists_principal_conductivity_energy_scalar

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_LinePayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Energy paid by a line crossing a barrier

A barrier that is zero at an end of `[-L, L]` and equals one somewhere
on the segment has squared derivative integral at least `1 / (2 * L)`.
This follows from the fundamental theorem of calculus and the integral
Cauchy–Schwarz inequality.

Both absolutely continuous and `C¹` restrictions satisfy this estimate.
Fubini's theorem gives the rectangular energy lower bound when horizontal
slices are almost everywhere absolutely continuous.
-/

open MeasureTheory Set

namespace CircleDomainRigidity

/-- Cauchy–Schwarz against the constant function on a finite interval,
written without square roots. -/
theorem integral_sq_le_length_mul_integral_sq {g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hg : IntervalIntegrable g volume a b)
    (hg2 : IntervalIntegrable (fun x => g x ^ 2) volume a b) :
    (∫ x in a..b, g x) ^ 2 ≤ (b - a) * (∫ x in a..b, g x ^ 2) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  let J := ∫ x in a..b, g x
  have hpoly : (fun x => ((b - a) * g x - J) ^ 2) =
      (fun x => (b - a) ^ 2 * g x ^ 2 - (2 * (b - a) * J) * g x + J ^ 2) := by
    funext x
    ring
  have hnonneg := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab.le
    (fun x => sq_nonneg ((b - a) * g x - J))
  rw [hpoly, intervalIntegral.integral_add
      ((hg2.const_mul _).sub (hg.const_mul _)) intervalIntegrable_const,
    intervalIntegral.integral_sub (hg2.const_mul _) (hg.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul] at hnonneg
  have hmul : (b - a) * J ^ 2 ≤
      (b - a) * ((b - a) * (∫ x in a..b, g x ^ 2)) := by
    dsimp [J] at *
    nlinarith
  exact le_of_mul_le_mul_left hmul (sub_pos.mpr hab)

end CircleDomainRigidity

end OAI
end

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
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SummableEnergyCutoffs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A prescribed positive summable budget gives actual smooth source
cutoffs with summable L2 differential norms and an almost everywhere
summable pointwise differential majorant. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem smooth_cutoff_gradient_memLp {f : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    MemLp (fderiv ℝ f) 2 volume :=
  (hf.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).memLp_of_hasCompactSupport (hs.fderiv (𝕜 := ℝ))

 theorem smooth_cutoff_energy_eq_norm_sq {f : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    (∫ z, ‖fderiv ℝ f z‖^2) = (eLpNorm (fderiv ℝ f) 2 volume).toReal^2 := by
  have hm := smooth_cutoff_gradient_memLp hf hs
  simpa only [eLpNorm_norm _] using integral_sq_eq_eLpNorm_toReal_sq hm.norm

 theorem exists_summable_energy_cutoffs
    (c : ℕ → ℂ) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hsum : Summable ε) :
    ∃ χ : ℕ → ℂ → ℝ,
      (∀ n, ContDiff ℝ ∞ (χ n) ∧ HasCompactSupport (χ n) ∧
        tsupport (χ n) ⊆ ball (c n) (r n) ∧ (∀ z, χ n z ∈ Icc (0 : ℝ) 1) ∧
        (∀ᶠ z in 𝓝 (c n), χ n z = 1) ∧ MemLp (fderiv ℝ (χ n)) 2 volume ∧
        (eLpNorm (fderiv ℝ (χ n)) 2 volume).toReal < ε n) ∧
      Summable (fun n => (eLpNorm (fderiv ℝ (χ n)) 2 volume).toReal) ∧
      (∑' n, (eLpNorm (fderiv ℝ (χ n)) 2 volume).toReal) ≤ ∑' n, ε n ∧
      (∀ᵐ z ∂volume, Summable (fun n => ‖fderiv ℝ (χ n) z‖)) := by
  choose χ hχ using fun n => exists_small_energy_cutoff (c n) (hr n) (sq_pos_of_pos (hε n))
  have hdata (n : ℕ) : ContDiff ℝ ∞ (χ n) ∧ HasCompactSupport (χ n) ∧
      tsupport (χ n) ⊆ ball (c n) (r n) ∧ (∀ z, χ n z ∈ Icc (0 : ℝ) 1) ∧
      (∀ᶠ z in 𝓝 (c n), χ n z = 1) ∧ MemLp (fderiv ℝ (χ n)) 2 volume ∧
      (eLpNorm (fderiv ℝ (χ n)) 2 volume).toReal < ε n := by
    obtain ⟨hf, hs, hsup, hu, ho, he⟩ := hχ n
    refine ⟨hf, hs, hsup, hu, ho, smooth_cutoff_gradient_memLp hf hs, ?_⟩
    rw [smooth_cutoff_energy_eq_norm_sq hf hs] at he
    nlinarith [hε n, ENNReal.toReal_nonneg (a := eLpNorm (fderiv ℝ (χ n)) 2 volume)]
  have hbound (n : ℕ) : (eLpNorm (fderiv ℝ (χ n)) 2 volume).toReal ≤ ε n := (hdata n).2.2.2.2.2.2.le
  have hsm : Summable (fun n => (eLpNorm (fderiv ℝ (χ n)) 2 volume).toReal) :=
    Summable.of_nonneg_of_le (fun _ => ENNReal.toReal_nonneg) hbound hsum
  refine ⟨χ, hdata, hsm, hsm.tsum_le_tsum hbound hsum, ?_⟩
  have hfin : (∑' n, eLpNorm (fderiv ℝ (χ n)) 2 volume) < (⊤ : ℝ≥0∞) := by
    apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun n => ?_)) hsum.tsum_ofReal_lt_top
    rw [← ENNReal.ofReal_toReal (hdata n).2.2.2.2.2.1.2.ne]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  exact summable_norm_of_tsum_eLpNorm_ne_top (p := 2) (μ := volume)
    (f := fun n => fderiv ℝ (χ n)) (by norm_num) (fun n => (hdata n).2.2.2.2.2.1.1) hfin.ne

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_L2SummableMajorant
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pointwise sum of the cutoff differential norms is itself in L2,
with the sum of their L2 norms as a bound. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem l2_tsum_of_summable_norms (g : ℕ → ℂ → ℝ)
    (hg : ∀ n, MemLp (g n) 2 volume)
    (hs : Summable (fun n => (eLpNorm (g n) 2 volume).toReal)) :
    MemLp (fun z => ∑' n, g n z) 2 volume ∧
      (eLpNorm (fun z => ∑' n, g n z) 2 volume).toReal ≤
        ∑' n, (eLpNorm (g n) 2 volume).toReal := by
  let F : ℕ → Lp ℝ 2 volume := fun n => (hg n).toLp (g n)
  have hnorm : Summable (fun n => ‖F n‖) := by
    simpa only [F, Lp.norm_toLp] using hs
  have hfinite : (∑' n, ‖F n‖ₑ) ≠ (⊤ : ℝ≥0∞) := by
    have hh := hs.tsum_ofReal_lt_top
    have he (n : ℕ) : ENNReal.ofReal (eLpNorm (g n) 2 volume).toReal = eLpNorm (g n) 2 volume :=
      ENNReal.ofReal_toReal (hg n).eLpNorm_ne_top
    simp_rw [he] at hh
    simpa only [F, Lp.enorm_toLp] using hh.ne
  have hvalues : ∀ᵐ z ∂volume, ∀ n, F n z = g n z :=
    ae_all_iff.mpr (fun n => (hg n).coeFn_toLp)
  have hae : (⇑(∑' n, F n) : ℂ → ℝ) =ᵐ[volume] (fun z => ∑' n, g n z) := by
    filter_upwards [Lp.coeFn_tsum hfinite, hvalues] with z hz hv
    rw [hz]
    exact tsum_congr hv
  refine ⟨(Lp.memLp (∑' n, F n)).ae_eq hae, ?_⟩
  rw [← eLpNorm_congr_ae hae, ← Lp.norm_def]
  simpa only [F, Lp.norm_toLp] using norm_tsum_le_tsum_norm hnorm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_L2AdditiveMajorant
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A scalar L2 majorant bounds the differential error of the actual
priority interpolation. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem l2_norm_le_of_additive_majorant
    {U : Set ℂ} {D : ℂ → (ℂ →L[ℝ] ℝ)} {g h : ℂ → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hD : AEStronglyMeasurable D (volume.restrict U))
    (hg : MemLp g 2 (volume.restrict U)) (hh : MemLp h 2 (volume.restrict U))
    (hg0 : ∀ᵐ z ∂volume.restrict U, 0 ≤ g z)
    (hh0 : ∀ᵐ z ∂volume.restrict U, 0 ≤ h z)
    (hbound : ∀ᵐ z ∂volume.restrict U, ‖D z‖ ≤ a*g z+h z) :
    MemLp D 2 (volume.restrict U) ∧
      (eLpNorm D 2 (volume.restrict U)).toReal ≤
        a*(eLpNorm g 2 (volume.restrict U)).toReal +
          (eLpNorm h 2 (volume.restrict U)).toReal := by
  let v : ℂ → ℝ := fun z => a*g z+h z
  have hv : MemLp v 2 (volume.restrict U) := (hg.const_mul a).add hh
  have hb : ∀ᵐ z ∂volume.restrict U, ‖D z‖ ≤ ‖v z‖ := by
    filter_upwards [hbound, hg0, hh0] with z hz hzg hzh
    simpa only [v, Real.norm_eq_abs, abs_of_nonneg (add_nonneg (mul_nonneg ha hzg) hzh)] using hz
  have hd := hv.of_le hD hb
  refine ⟨hd, ?_⟩
  apply (ENNReal.toReal_mono hv.eLpNorm_ne_top (eLpNorm_mono_ae hb)).trans
  have hsum := eLpNorm_add_le (μ := volume.restrict U) (p := 2) (f := fun z => a*g z) (g := h)
    (hg.const_mul a).aestronglyMeasurable hh.aestronglyMeasurable (by norm_num)
  have hh' : eLpNorm (fun z => a*g z) 2 (volume.restrict U) ≠ ∞ := (hg.const_mul a).eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hh', hh.eLpNorm_ne_top⟩) hsum
  rw [ENNReal.toReal_add hh' hh.eLpNorm_ne_top] at hreal
  have he : eLpNorm (fun z => a*g z) 2 (volume.restrict U) =
      ENNReal.ofReal a * eLpNorm g 2 (volume.restrict U) := by
    change eLpNorm (a • g) 2 (volume.restrict U) = _
    simpa only [Real.enorm_eq_ofReal_abs, abs_of_nonneg ha] using
      eLpNorm_const_smul a g 2 (volume.restrict U)
  rw [he, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha] at hreal
  exact hreal

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
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CompactMollifierSampling
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform sampling control on compact sets, including exact preservation
of constant regions and smooth cutoffs equal to one near a compact set. -/

open Set Filter MeasureTheory Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem planarMollifier_samples_eventually
    {K V : Set EuclideanPlane} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∀ᶠ n in atTop, ∀x ∈ K,
      ball x (DeGiorgi.shrinkingBump (d := 2) n).rOut ⊆ V := by
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hV hKV
  have hr : ∀ᶠ n in atTop, (DeGiorgi.shrinkingBump (d := 2) n).rOut < δ :=
    (tendsto_order.1 tendsto_planarMollifier_radius).2 δ hδ
  filter_upwards [hr] with n hn x hx y hy
  apply hδV
  exact mem_cthickening_of_dist_le y x δ K hx
    ((mem_ball.1 hy).le.trans hn.le)

end CircleDomainRigidity

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
-- module Solutions.Q146_CD.CircleDomains_Topology_ComponentTopology
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Topological parts of the component argument

The quotient theorem below proves the totally disconnected dust conclusion
from the component-collapse properties of the quotient.  Moore's 1925
sphere-decomposition theorem supplies the sphere realization; that published
input is not assumed to provide the dust conclusion for free.
-/

open Set Topology

namespace CircleDomainRigidity

theorem IsComplementaryComponent.disjoint_of_ne {G K L : Set Sphere}
    (hK : IsComplementaryComponent G K) (hL : IsComplementaryComponent G L)
    (hne : K ≠ L) : Disjoint K L := by
  obtain ⟨p, _, rfl⟩ := hK
  obtain ⟨q, _, rfl⟩ := hL
  apply Set.disjoint_left.mpr
  intro x hpx hqx
  exact hne ((connectedComponentIn_eq hpx).trans (connectedComponentIn_eq hqx).symm)

/-- No countability is imposed on point components.  The components with
nonempty interior are countable by separability. -/
theorem countable_complementaryComponents_with_interior (G : Set Sphere) :
    {K : Set Sphere | IsComplementaryComponent G K ∧ (interior K).Nonempty}.Countable := by
  let : TopologicalSpace.SeparableSpace Sphere :=
    (OnePoint.isDenseEmbedding_coe (X := ℂ)).separableSpace
  let A := {K : Set Sphere | IsComplementaryComponent G K ∧ (interior K).Nonempty}
  have hdisj : A.PairwiseDisjoint id := by
    intro K hK L hL hne
    exact hK.1.disjoint_of_ne hL.1 hne
  exact hdisj.countable_of_nonempty_interior (fun _ hK => hK.2)

end CircleDomainRigidity

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
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalRoundIntegrals
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transport of round-disk integrals and smooth partial derivatives
between the physical Euclidean plane and the complex plane. -/
open Set Filter Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem physical_complex_partial {a : EuclideanPlane → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (x v : EuclideanPlane) :
    fderiv ℝ (fun z => a (complexPlaneCoordinates.symm z)) (complexPlaneCoordinates x)
      (complexPlaneCoordinates v) = fderiv ℝ a x v := by
  change fderiv ℝ (a ∘ complexPlaneCoordinates.symm) (complexPlaneCoordinates x)
    (complexPlaneCoordinates v) = _
  rw [fderiv_comp (complexPlaneCoordinates x) (ha.differentiable (by simp)).differentiableAt
      complexPlaneCoordinates.symm.differentiableAt, complexPlaneCoordinates.symm.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ComplexScalarEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact complex-chart energy of a smooth physical scalar, and its
convergence under positive mollification. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem complex_scalar_energy_pointwise {u : EuclideanPlane → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x : EuclideanPlane) :
    ‖fderiv ℝ (u ∘ complexPlaneCoordinates.symm) (complexPlaneCoordinates x)‖^2 =
      (fderiv ℝ u x (EuclideanSpace.single 0 1))^2 +
      (fderiv ℝ u x (EuclideanSpace.single 1 1))^2 := by
  rw [complexCovector_norm_sq]
  change (fderiv ℝ (fun z => u (complexPlaneCoordinates.symm z))
      (complexPlaneCoordinates x) 1)^2 +
    (fderiv ℝ (fun z => u (complexPlaneCoordinates.symm z))
      (complexPlaneCoordinates x) Complex.I)^2 = _
  rw [← complexPlaneCoordinates_zero, physical_complex_partial hu,
    ← complexPlaneCoordinates_one, physical_complex_partial hu]

 theorem complex_scalar_energy_integral {u : EuclideanPlane → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (U : Set ℂ) :
    (∫ z in U, ‖fderiv ℝ (u ∘ complexPlaneCoordinates.symm) z‖^2) =
      ∫ x in complexPlaneCoordinates ⁻¹' U,
        (fderiv ℝ u x (EuclideanSpace.single 0 1))^2 +
        (fderiv ℝ u x (EuclideanSpace.single 1 1))^2 := by
  rw [← complexPlaneCoordinates_measurePreserving.setIntegral_preimage_emb
    complexPlaneCoordinates.toHomeomorph.measurableEmbedding
    (fun z => ‖fderiv ℝ (u ∘ complexPlaneCoordinates.symm) z‖^2) U]
  apply integral_congr_ae
  exact Eventually.of_forall (complex_scalar_energy_pointwise hu)

 theorem complex_mollification_energy_tendsto {u : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u univ) (hs : HasCompactSupport u) (U : Set ℂ) :
    Tendsto (fun n => ∫ z in U,
      ‖fderiv ℝ ((planarMollification u n) ∘ complexPlaneCoordinates.symm) z‖^2)
      atTop (𝓝 (∫ x in complexPlaneCoordinates ⁻¹' U,
        hu.weakGrad x 0^2 + hu.weakGrad x 1^2)) := by
  have hL : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using hu.memLp
  have ht := planarMollification_energy_tendsto hu hs (complexPlaneCoordinates ⁻¹' U)
  exact ht.congr' (Eventually.of_forall (fun n =>
    (complex_scalar_energy_integral (planarMollification_smooth
      (hL.locallyIntegrable (by norm_num)) n) U).symm))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConductivityEnergyBounds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two separate nonnegative terms in the conductivity identity:
small error from the vertical coordinate and vanishing energy on the
coefficient support. Local ordinary energy is then uniformly bounded. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace PlaneLocalWeakComplex

 theorem conductivity_energy_bounds {f : EuclideanPlane → ℂ}
    (D : PlaneLocalWeakComplex f) {F : Set EuclideanPlane}
    {n : ℕ} (hn : 2 ≤ n) {c d : ℝ} (hcd : c ≤ d)
    (heq : (∫ x, (D.imagGradient x 0)^2 + (D.imagGradient x 1-1)^2) +
      ((n : ℝ)-1) * (∫ x in F, (D.imagGradient x 0)^2 + (D.imagGradient x 1)^2) =
        2 * Real.pi * c) :
    (∫ x, (D.imagGradient x 0)^2 + (D.imagGradient x 1-1)^2) ≤ 2 * Real.pi * d ∧
    (∫ x in F, (D.imagGradient x 0)^2 + (D.imagGradient x 1)^2) ≤
      2 * Real.pi * d / ((n : ℝ)-1) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < (n : ℝ)-1 := by linarith
  have hH : 0 ≤ ∫ x, (D.imagGradient x 0)^2 + (D.imagGradient x 1-1)^2 :=
    integral_nonneg (fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hE : 0 ≤ ∫ x in F, (D.imagGradient x 0)^2 + (D.imagGradient x 1)^2 :=
    integral_nonneg (fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hbudget : 2 * Real.pi * c ≤ 2 * Real.pi * d :=
    mul_le_mul_of_nonneg_left hcd (by positivity)
  constructor
  · nlinarith [mul_nonneg hp.le hE]
  · apply (le_div_iff₀ hp).mpr
    nlinarith

 theorem imag_local_energy_le_error {f : EuclideanPlane → ℂ}
    (D : PlaneLocalWeakComplex f) (R : ℝ)
    (hH : Integrable (fun x => (D.imagGradient x 0)^2 + (D.imagGradient x 1-1)^2)) :
    (∫ x in Metric.ball 0 R, (D.imagGradient x 0)^2 + (D.imagGradient x 1)^2) ≤
      2 * (∫ x, (D.imagGradient x 0)^2 + (D.imagGradient x 1-1)^2) +
      2 * (volume (Metric.ball (0 : EuclideanPlane) R)).toReal := by
  let μ := volume.restrict (Metric.ball (0 : EuclideanPlane) R)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hE : Integrable (fun x => (D.imagGradient x 0)^2 + (D.imagGradient x 1)^2) μ :=
    (D.imag_memLp R 0).integrable_sq.add (D.imag_memLp R 1).integrable_sq
  have hB : Integrable (fun x => 2 * ((D.imagGradient x 0)^2 +
      (D.imagGradient x 1-1)^2) + 2) μ := (hH.restrict.const_mul 2).add (integrable_const 2)
  have hle : (∫ x, (D.imagGradient x 0)^2 + (D.imagGradient x 1)^2 ∂μ) ≤
      ∫ x, 2 * ((D.imagGradient x 0)^2 + (D.imagGradient x 1-1)^2) + 2 ∂μ := by
    apply integral_mono hE hB
    intro x
    nlinarith [sq_nonneg (D.imagGradient x 0), sq_nonneg (D.imagGradient x 1-2)]
  rw [integral_add (hH.restrict.const_mul 2) (integrable_const 2), integral_const_mul,
    integral_const] at hle
  have hmono : (∫ x in Metric.ball 0 R, (D.imagGradient x 0)^2 + (D.imagGradient x 1-1)^2) ≤
      ∫ x, (D.imagGradient x 0)^2 + (D.imagGradient x 1-1)^2 :=
    setIntegral_le_integral hH (Eventually.of_forall (fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _)))
  simp only [μ, Measure.real, Measure.restrict_apply_univ, smul_eq_mul] at hle
  nlinarith [hle, hmono]

end PlaneLocalWeakComplex
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LogarithmicEnergyBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrating the circle energy inequality against dt/t produces the
logarithmic factor in the coordinate modulus. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem logarithmic_radial_bound {E : ℝ → ℝ} {r R B K : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hE : ContinuousOn E (Icc r R))
    (hcircle : ∀ t ∈ Ioo r R, B ≤ K*t^2*E t) :
    B*Real.log (R/r) ≤ K*(∫ t in r..R, t*E t) := by
  have hR : 0 < R := hr.trans_le hrR
  have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Icc r R) :=
    continuousOn_id.inv₀ (fun t ht => ne_of_gt (hr.trans_le ht.1))
  have hi : IntervalIntegrable (fun t => B*t⁻¹) volume r R :=
    (continuousOn_const.mul hinv).intervalIntegrable_of_Icc hrR
  have he : IntervalIntegrable (fun t => K*(t*E t)) volume r R :=
    (continuousOn_const.mul (continuousOn_id.mul hE)).intervalIntegrable_of_Icc hrR
  have hle := intervalIntegral.integral_mono_on_of_le_Ioo hrR hi he (fun t ht => by
    have ht0 : 0 < t := hr.trans ht.1
    have h : B ≤ (K*(t*E t))*t := by nlinarith [hcircle t ht]
    simpa only [div_eq_mul_inv] using (div_le_iff₀ ht0).mpr h)
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hr hR,
    intervalIntegral.integral_const_mul] at hle
  exact hle

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RealPolarAnnulus
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real polar integration, specialized to continuous energy densities on
bounded annuli. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem integral_polar_annulus {g : ℂ → ℝ} (hg : Continuous g)
    {a b : ℝ} (ha : 0 ≤ a) :
    (∫ z in {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b}, g z) =
      ∫ r in Ioo a b, ∫ θ in Ioo (-Real.pi) Real.pi,
        r * g (Complex.polarCoord.symm (r, θ)) := by
  let A := {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b}
  let S := Ioo a b
  let T := Ioo (-Real.pi) Real.pi
  let f : ℝ × ℝ → ℝ := fun p => p.1 * g (Complex.polarCoord.symm p)
  have hA : MeasurableSet A := (isOpen_lt continuous_const continuous_norm).measurableSet.inter
    (isOpen_lt continuous_norm continuous_const).measurableSet
  have hP : MeasurableSet polarCoord.target := polarCoord.open_target.measurableSet
  have hf : Continuous f := by
    apply Continuous.mul continuous_fst
    apply hg.comp
    change Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p)
    simp_rw [Complex.polarCoord_symm_apply]
    fun_prop
  have hfi : IntegrableOn f (S ×ˢ T) :=
    ((hf.continuousOn.integrableOn_compact
      ((isCompact_Icc : IsCompact (Icc a b)).prod isCompact_Icc))).mono_set
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hpolar := Complex.integral_comp_polarCoord_symm (A.indicator g)
  rw [integral_indicator hA] at hpolar
  calc
    _ = ∫ p in polarCoord.target,
        p.1 * (A.indicator g) (Complex.polarCoord.symm p) := hpolar.symm
    _ = ∫ p, (S ×ˢ T).indicator f p := by
      rw [← integral_indicator hP]
      apply integral_congr_ae
      filter_upwards [] with p
      by_cases hp : p ∈ polarCoord.target
      · have hp0 : 0 < p.1 := hp.1
        have hmem : Complex.polarCoord.symm p ∈ A ↔ p.1 ∈ S := by
          simp only [A, S, mem_ofPred_eq, mem_Ioo, Complex.norm_polarCoord_symm,
            abs_of_pos hp0]
        by_cases hS : p.1 ∈ S
        · have hST : p ∈ S ×ˢ T := ⟨hS, hp.2⟩
          rw [indicator_of_mem hp, indicator_of_mem hST, indicator_of_mem (hmem.mpr hS)]
        · have hST : p ∉ S ×ˢ T := fun h => hS h.1
          rw [indicator_of_mem hp, indicator_of_notMem hST,
            indicator_of_notMem (fun h => hS (hmem.mp h)), mul_zero]
      · have hST : p ∉ S ×ˢ T := by
          rintro ⟨hS, hT⟩
          exact hp ⟨lt_of_le_of_lt ha hS.1, hT⟩
        rw [indicator_of_notMem hp, indicator_of_notMem hST]
    _ = ∫ p in S ×ˢ T, f p := integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)
    _ = _ := setIntegral_prod f hfi

 theorem integral_polar_annulus_circle {g : ℂ → ℝ} (hg : Continuous g)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ z in {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b}, g z) =
      ∫ r in a..b, r * (∫ θ in (0 : ℝ)..(2*Real.pi), g (circleMap 0 r θ)) := by
  rw [integral_polar_annulus hg ha, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r _
  have hp := ((periodic_circleMap 0 r).comp g).intervalIntegral_add_eq (-Real.pi) 0
  have hends : -Real.pi + 2*Real.pi = Real.pi := by ring
  simp only [hends, zero_add, Function.comp_def] at hp
  dsimp only
  rw [← hp, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Ioc_eq_integral_Ioo, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro θ _
  simp [circleMap, Complex.polarCoord_symm_apply, Complex.exp_mul_I]

 theorem integral_polar_annulus_center {g : ℂ → ℝ} (hg : Continuous g)
    (c : ℂ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ z in {z : ℂ | a < dist z c ∧ dist z c < b}, g z) =
      ∫ r in a..b, r * (∫ θ in (0 : ℝ)..(2*Real.pi), g (circleMap c r θ)) := by
  let A := {z : ℂ | a < dist z c ∧ dist z c < b}
  have he : ((fun z : ℂ => c+z) ⁻¹' A) = {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b} := by
    ext z
    simp [A, dist_eq_norm]
  have ht := (measurePreserving_add_left volume c).setIntegral_preimage_emb
    (Homeomorph.addLeft c).measurableEmbedding g A
  rw [he] at ht
  have hh := integral_polar_annulus_circle (g := fun z => g (c+z))
    (hg.comp (continuous_const.add continuous_id)) ha hab
  rw [← ht, hh]
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp [circleMap]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_HomeomorphicCoordinateRange
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A coordinate of a plane homeomorphism has no interior extremum.
Its bounds on the boundary of any compact set hold throughout that set. -/
open Set Filter Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem homeomorphic_im_not_local_max (H : ℂ ≃ₜ ℂ) (z : ℂ) :
    ¬ IsLocalMax (fun w => (H w).im) z := by
  intro h
  have ho : IsOpenMap (fun w => (H w).im) :=
    (Complex.imCLM.isOpenMap Complex.im_surjective).comp H.isOpenMap
  apply (isLocalMaxOn_univ_iff.mpr h).not_nhds_le_map
  simpa only [nhdsWithin_univ] using ho.nhds_le z

 theorem homeomorphic_im_not_local_min (H : ℂ ≃ₜ ℂ) (z : ℂ) :
    ¬ IsLocalMin (fun w => (H w).im) z := by
  intro h
  have ho : IsOpenMap (fun w => (H w).im) :=
    (Complex.imCLM.isOpenMap Complex.im_surjective).comp H.isOpenMap
  apply (isLocalMinOn_univ_iff.mpr h).not_nhds_le_map
  simpa only [nhdsWithin_univ] using ho.nhds_le z

 theorem homeomorphic_im_le_of_boundary (H : ℂ ≃ₜ ℂ) {K : Set ℂ} (hK : IsCompact K)
    {C : ℝ} (hbd : ∀ z ∈ frontier K, (H z).im ≤ C) :
    ∀ z ∈ K, (H z).im ≤ C := by
  intro z hz
  obtain ⟨w, hw, hmax⟩ := hK.exists_isMaxOn ⟨z, hz⟩
    (Complex.continuous_im.comp H.continuous).continuousOn
  have hwi : w ∉ interior K := fun hi => homeomorphic_im_not_local_max H w
    (hmax.isLocalMax (mem_interior_iff_mem_nhds.mp hi))
  have hwb : w ∈ frontier K := ⟨subset_closure hw, hwi⟩
  exact (hmax hz).trans (hbd w hwb)

 theorem homeomorphic_im_ge_of_boundary (H : ℂ ≃ₜ ℂ) {K : Set ℂ} (hK : IsCompact K)
    {C : ℝ} (hbd : ∀ z ∈ frontier K, C ≤ (H z).im) :
    ∀ z ∈ K, C ≤ (H z).im := by
  intro z hz
  obtain ⟨w, hw, hmin⟩ := hK.exists_isMinOn ⟨z, hz⟩
    (Complex.continuous_im.comp H.continuous).continuousOn
  have hwi : w ∉ interior K := fun hi => homeomorphic_im_not_local_min H w
    (hmin.isLocalMin (mem_interior_iff_mem_nhds.mp hi))
  have hwb : w ∈ frontier K := ⟨subset_closure hw, hwi⟩
  exact (hbd w hwb).trans (hmin hz)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothCircleOscillation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth circle variation controls a homeomorphic height on the enclosed
disk. This is the boundary step of the logarithmic modulus estimate. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem smooth_circle_anchor_bound {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (c : ℂ) (r : ℝ) {θ : ℝ} (hθ : θ ∈ Icc 0 (2*Real.pi)) :
    |f (circleMap c r θ)-f (circleMap c r 0)| ≤ smoothCircleVariation f c r := by
  let g := f ∘ circleMap c r
  have hg : ContDiff ℝ 1 g := hf.comp (contDiff_circleMap c r)
  have hgd : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  have hFTC : (∫ t in (0 : ℝ)..θ, deriv g t) = g θ-g 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => (hg.differentiable (by norm_num) t).hasDerivAt)
      (hgd.intervalIntegrable 0 θ)
  have hI : IntervalIntegrable (fun t => |deriv g t|) volume 0 (2*Real.pi) :=
    hgd.abs.intervalIntegrable _ _
  calc
    _ = |∫ t in (0 : ℝ)..θ, deriv g t| := by rw [hFTC]; rfl
    _ ≤ ∫ t in (0 : ℝ)..θ, |deriv g t| := by
      simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm (f := deriv g) (μ := volume) hθ.1
    _ ≤ smoothCircleVariation f c r :=
      intervalIntegral.integral_mono_interval le_rfl hθ.1 hθ.2
        (Eventually.of_forall (fun t => abs_nonneg (deriv g t))) hI

 theorem smoothCircleVariation_sq_le {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (c : ℂ) (r : ℝ) :
    (smoothCircleVariation f c r)^2 ≤
      2*Real.pi*(∫ θ in (0 : ℝ)..(2*Real.pi), (deriv (f ∘ circleMap c r) θ)^2) := by
  have hd : Continuous (deriv (f ∘ circleMap c r)) :=
    (hf.comp (contDiff_circleMap c r)).continuous_deriv (by norm_num)
  simpa only [smoothCircleVariation, sub_zero, sq_abs] using
    integral_sq_le_length_mul_integral_sq (by positivity : (0 : ℝ) ≤ 2*Real.pi)
      (hd.abs.intervalIntegrable _ _) ((hd.abs.pow 2).intervalIntegrable _ _)

 theorem homeomorphic_pair_le_circle_variation (φ : ℂ ≃ₜ ℂ)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (c : ℂ) {r ε : ℝ} (hr : 0 < r)
    (happrox : ∀ z ∈ sphere c r, |(φ z).im-f z| ≤ ε)
    {x y : ℂ} (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    |(φ x).im-(φ y).im| ≤ 2*(smoothCircleVariation f c r+ε) := by
  let a := f (circleMap c r 0)
  let B := smoothCircleVariation f c r+ε
  have hbd : ∀ z ∈ frontier (closedBall c r), |(φ z).im-a| ≤ B := by
    intro z hz
    rw [frontier_closedBall c hr.ne'] at hz
    have hz' : z ∈ sphere c |r| := by simpa only [abs_of_pos hr] using hz
    rw [← image_circleMap_Ioc c r] at hz'
    obtain ⟨θ, hθ, rfl⟩ := hz'
    have hθ' : θ ∈ Icc 0 (2*Real.pi) := ⟨hθ.1.le, hθ.2⟩
    have ha := smooth_circle_anchor_bound hf c r hθ'
    have he := happrox (circleMap c r θ) (by simpa only [abs_of_pos hr] using circleMap_mem_sphere' c r θ)
    calc
      _ ≤ |(φ (circleMap c r θ)).im-f (circleMap c r θ)| + |f (circleMap c r θ)-a| :=
        abs_sub_le _ _ _
      _ ≤ B := by dsimp only [a, B] <;> linarith
  have hhi := homeomorphic_im_le_of_boundary φ (isCompact_closedBall c r)
    (C := a+B) (fun z hz => by linarith [(abs_le.mp (hbd z hz)).2])
  have hlo := homeomorphic_im_ge_of_boundary φ (isCompact_closedBall c r)
    (C := a-B) (fun z hz => by linarith [(abs_le.mp (hbd z hz)).1])
  have hxhi := hhi x hx
  have hyhi := hhi y hy
  have hxlo := hlo x hx
  have hylo := hlo y hy
  apply abs_le.mpr
  dsimp only [B] at *
  constructor <;> linarith

 theorem smooth_circle_deriv_sq_le {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (c : ℂ) (r θ : ℝ) :
    (deriv (f ∘ circleMap c r) θ)^2 ≤
      r^2 * ‖fderiv ℝ f (circleMap c r θ)‖^2 := by
  have he := ((hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt θ
    (hasDerivAt_circleMap c r θ)).deriv
  rw [he]
  have h := (fderiv ℝ f (circleMap c r θ)).le_opNorm (circleMap 0 r θ*Complex.I)
  rw [norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero, Real.norm_eq_abs] at h
  have hsq := pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa only [mul_pow, sq_abs, mul_comm] using hsq

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothLogarithmicModulus
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A logarithmic modulus for a homeomorphic height, expressed using a
uniformly close smooth approximation and its actual annular energy. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem smoothCircleVariation_nonneg {f : ℂ → ℝ} (c : ℂ) (r : ℝ) :
    0 ≤ smoothCircleVariation f c r :=
  intervalIntegral.integral_nonneg (by positivity) (fun _ _ => abs_nonneg _)

 theorem homeomorphic_pair_sq_le_circle_energy (φ : ℂ ≃ₜ ℂ)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (c : ℂ) {r ε : ℝ} (hr : 0 < r)
    (_hε : 0 ≤ ε) (happrox : ∀ z ∈ sphere c r, |(φ z).im-f z| ≤ ε)
    {x y : ℂ} (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    |(φ x).im-(φ y).im|^2 - 8*ε^2 ≤
      16*Real.pi*r^2*(∫ θ in (0 : ℝ)..(2*Real.pi),
        ‖fderiv ℝ f (circleMap c r θ)‖^2) := by
  have hp := homeomorphic_pair_le_circle_variation φ hf c hr happrox hx hy
  have hv := smoothCircleVariation_nonneg (f := f) c r
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hp 2
  have hder := smoothCircleVariation_sq_le hf c r
  have hg : Continuous (fun θ => ‖fderiv ℝ f (circleMap c r θ)‖^2) :=
    (((hf.continuous_fderiv (by norm_num)).comp (continuous_circleMap c r)).norm.pow 2)
  have hd : Continuous (fun θ => (deriv (f ∘ circleMap c r) θ)^2) :=
    ((hf.comp (contDiff_circleMap c r)).continuous_deriv (by norm_num)).pow 2
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by positivity : (0 : ℝ) ≤ 2*Real.pi)
    (hd.intervalIntegrable _ _) ((continuous_const.mul hg).intervalIntegrable _ _)
    (fun θ _ => smooth_circle_deriv_sq_le hf c r θ)
  simp only [Pi.mul_apply] at hi
  rw [intervalIntegral.integral_const_mul] at hi
  have hder' := hder.trans (mul_le_mul_of_nonneg_left hi
    (by positivity : 0 ≤ 2*Real.pi))
  nlinarith [sq_nonneg (smoothCircleVariation f c r-ε)]

 theorem homeomorphic_pair_logarithmic_smooth_bound (φ : ℂ ≃ₜ ℂ) (c : ℂ)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) {r R ε : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hε : 0 ≤ ε)
    (happrox : ∀ z ∈ closedBall c R, |(φ z).im-f z| ≤ ε)
    {x y : ℂ} (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    (|(φ x).im-(φ y).im|^2-8*ε^2)*Real.log (R/r) ≤
      16*Real.pi*(∫ z in {z : ℂ | r < dist z c ∧ dist z c < R}, ‖fderiv ℝ f z‖^2) := by
  let E : ℝ → ℝ := fun t => ∫ θ in (0 : ℝ)..(2*Real.pi),
    ‖fderiv ℝ f (circleMap c t θ)‖^2
  have hc : Continuous (fun p : ℝ × ℝ => circleMap c p.1 p.2) := by
    unfold circleMap
    fun_prop
  have hE : Continuous E :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (((hf.continuous_fderiv (by norm_num)).comp hc).norm.pow 2) _ _
  have hcircle : ∀ t ∈ Ioo r R,
      |(φ x).im-(φ y).im|^2-8*ε^2 ≤ 16*Real.pi*t^2*E t := by
    intro t ht
    apply homeomorphic_pair_sq_le_circle_energy φ hf c (hr.trans ht.1) hε
    · intro z hz
      exact happrox z ((closedBall_subset_closedBall ht.2.le) (sphere_subset_closedBall hz))
    · exact closedBall_subset_closedBall ht.1.le hx
    · exact closedBall_subset_closedBall ht.1.le hy
  have h := logarithmic_radial_bound hr hrR hE.continuousOn hcircle
  have heq := integral_polar_annulus_center
    ((hf.continuous_fderiv (by norm_num)).norm.pow 2) c hr.le hrR
  change (∫ z in {z : ℂ | r < dist z c ∧ dist z c < R}, ‖fderiv ℝ f z‖^2) =
    (∫ t in r..R, t*E t) at heq
  rwa [← heq] at h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_HeightSmoothApproximation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing the smooth annular estimate through uniform approximation
and convergence of the actual Dirichlet energies. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem homeomorphic_height_log_bound_of_smooth_approximation (φ : ℂ ≃ₜ ℂ) (c : ℂ)
    (f : ℕ → ℂ → ℝ) (hf : ∀ n, ContDiff ℝ 1 (f n))
    {r R E : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (huniform : ∀ ε > 0, ∀ᶠ n in atTop,
      ∀ z ∈ closedBall c R, |(φ z).im-f n z| ≤ ε)
    (henergy : Tendsto (fun n => ∫ z in {z : ℂ | r < dist z c ∧ dist z c < R},
      ‖fderiv ℝ (f n) z‖^2) atTop (𝓝 E))
    {x y : ℂ} (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    |(φ x).im-(φ y).im|^2 * Real.log (R/r) ≤ 16*Real.pi*E := by
  have he (ε : ℝ) (hε : 0 < ε) :
      (|(φ x).im-(φ y).im|^2-8*ε^2)*Real.log (R/r) ≤ 16*Real.pi*E := by
    apply ge_of_tendsto ((tendsto_const_nhds (x := 16*Real.pi)).mul henergy)
    filter_upwards [huniform ε hε] with n hn
    exact homeomorphic_pair_logarithmic_smooth_bound φ c (hf n) hr hrR hε.le hn hx hy
  have hzero : Tendsto (fun n : ℕ => (1 : ℝ)/((n : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have ht := (((tendsto_const_nhds (x := |(φ x).im-(φ y).im|^2)).sub
    ((tendsto_const_nhds (x := (8 : ℝ))).mul (hzero.pow 2))).mul
    (tendsto_const_nhds (x := Real.log (R/r))))
  have hle := le_of_tendsto ht (Eventually.of_forall (fun n => he (1/((n : ℝ)+1))
    (by positivity)))
  simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero] using hle

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CompactSobolevHeightModulus
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic coordinate estimate for an actual compact Sobolev
representative. All approximations are constructed by positive convolution. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem compact_sobolev_height_log_bound (φ : ℂ ≃ₜ ℂ) (c : ℂ)
    {u : EuclideanPlane → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u univ)
    (hc : Continuous u) (hs : HasCompactSupport u)
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (heq : ∀ z ∈ closedBall c R, u (complexPlaneCoordinates.symm z) = (φ z).im)
    {x y : ℂ} (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    |(φ x).im-(φ y).im|^2 * Real.log (R/r) ≤
      16*Real.pi*(∫ p in complexPlaneCoordinates ⁻¹'
        {z : ℂ | r < dist z c ∧ dist z c < R}, hu.weakGrad p 0^2+hu.weakGrad p 1^2) := by
  let f : ℕ → ℂ → ℝ := fun n => planarMollification u n ∘ complexPlaneCoordinates.symm
  have hL : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using hu.memLp
  have hf (n : ℕ) : ContDiff ℝ 1 (f n) :=
    ((planarMollification_smooth (hL.locallyIntegrable (by norm_num)) n).comp
      complexPlaneCoordinates.symm.contDiff).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  apply homeomorphic_height_log_bound_of_smooth_approximation φ c f hf hr hrR ?_
    (complex_mollification_energy_tendsto hu hs _) hx hy
  intro ε hε
  have hK := (isCompact_closedBall c R).image complexPlaneCoordinates.symm.continuous
  have ht := planarMollification_uniform_on_compact hL.aestronglyMeasurable hK
    isOpen_univ (subset_univ _) hc.continuousOn hε
  filter_upwards [ht] with n hn z hz
  have hh := hn (complexPlaneCoordinates.symm z) ⟨z, hz, rfl⟩
  dsimp only [f, comp_apply]
  rw [← heq z hz, abs_sub_comm]
  exact hh.le

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalSobolevHeightModulus
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact cutoffs remove the global L2 hypothesis from the height
estimate while preserving the actual local weak gradient on the annulus. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem local_sobolev_height_log_bound (φ : ℂ ≃ₜ ℂ) (c : ℂ)
    (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    {x y : ℂ} (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    |(φ x).im-(φ y).im|^2 * Real.log (R/r) ≤
      16*Real.pi*(∫ p in complexPlaneCoordinates ⁻¹'
        {z : ℂ | r < dist z c ∧ dist z c < R}, D.imagGradient p 0^2+D.imagGradient p 1^2) := by
  let v : EuclideanPlane → ℝ := fun p => (φ (complexPlaneCoordinates p)).im
  let Ω : Set EuclideanPlane := ball 0 (‖c‖+R+1)
  let K : Set EuclideanPlane := complexPlaneCoordinates.symm '' closedBall c R
  have hΩ : IsOpen Ω := isOpen_ball
  have hK : IsCompact K := (isCompact_closedBall c R).image complexPlaneCoordinates.symm.continuous
  have hKΩ : K ⊆ Ω := by
    rintro p ⟨z, hz, rfl⟩
    have htri : ‖z‖ ≤ dist z c + ‖c‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (z-c) c
    have he := complexPlaneCoordinates_norm (complexPlaneCoordinates.symm z)
    simp only [ContinuousLinearEquiv.apply_symm_apply] at he
    change ‖complexPlaneCoordinates.symm z-0‖ < ‖c‖+R+1
    rw [sub_zero, ← he]
    exact lt_of_le_of_lt htri (by linarith [mem_closedBall.mp hz])
  obtain ⟨η, V, hη, hsη, _, hsΩ, hV, hKV, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hK hΩ hKΩ
  have hVΩ : V ⊆ Ω := by
    intro p hp
    apply hsΩ
    apply subset_tsupport η
    rw [Function.mem_support, hone p hp]
    exact one_ne_zero
  have hv : Continuous v := Complex.continuous_im.comp
    (φ.continuous.comp complexPlaneCoordinates.continuous)
  let H := D.imagWitness (φ.continuous.comp complexPlaneCoordinates.continuous) (‖c‖+R+1)
  obtain ⟨W⟩ := exists_global_compact_cutoff_witness hΩ H.memW1p hη hsη hsΩ
  let A := complexPlaneCoordinates ⁻¹' {z : ℂ | r < dist z c ∧ dist z c < R}
  have hAK : A ⊆ K := by
    intro p hp
    exact ⟨complexPlaneCoordinates p, hp.2.le, complexPlaneCoordinates.symm_apply_apply p⟩
  have hAV : A ⊆ V := hAK.trans hKV
  have hgrad (i : Fin 2) :
      (fun p => W.weakGrad p i) =ᵐ[volume.restrict A] fun p => D.imagGradient p i := by
    have h := weakGrad_eq_on_cutoff_plateau hV hVΩ H W hone i
    exact h.filter_mono (ae_mono (Measure.restrict_mono hAV le_rfl))
  have heq : ∀ z ∈ closedBall c R,
      (η (complexPlaneCoordinates.symm z)*v (complexPlaneCoordinates.symm z)) = (φ z).im := by
    intro z hz
    have hpK : complexPlaneCoordinates.symm z ∈ K := by
      exact ⟨z, hz, rfl⟩
    rw [hone _ (hKV hpK), one_mul]
    simp only [v, ContinuousLinearEquiv.apply_symm_apply]
  have hb := compact_sobolev_height_log_bound φ c W (hη.continuous.mul hv)
    hsη.mul_right hr hrR heq hx hy
  have hi : (∫ p in A, W.weakGrad p 0^2+W.weakGrad p 1^2) =
      ∫ p in A, D.imagGradient p 0^2+D.imagGradient p 1^2 := by
    apply integral_congr_ae
    filter_upwards [hgrad 0, hgrad 1] with p h0 h1
    rw [h0, h1]
  change _ ≤ 16*Real.pi*(∫ p in A, _) at hb ⊢
  rwa [hi] at hb

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_HeightEnergyModulus
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common energy-error budget yields local equicontinuity of actual
homeomorphic height coordinates, with no common distortion constant. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem height_log_bound_from_error (φ : ℂ ≃ₜ ℂ) (c : ℂ)
    (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    {r R T B : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hT : ‖c‖+R < T)
    (hI : Integrable (fun p => D.imagGradient p 0^2+(D.imagGradient p 1-1)^2))
    (hB : (∫ p, D.imagGradient p 0^2+(D.imagGradient p 1-1)^2) ≤ B)
    {x y : ℂ} (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    |(φ x).im-(φ y).im|^2 * Real.log (R/r) ≤
      16*Real.pi*(2*B+2*(volume (ball (0 : EuclideanPlane) T)).toReal) := by
  let A := complexPlaneCoordinates ⁻¹' {z : ℂ | r < dist z c ∧ dist z c < R}
  have hAB : A ⊆ ball (0 : EuclideanPlane) T := by
    intro p hp
    have htri : ‖complexPlaneCoordinates p‖ ≤ dist (complexPlaneCoordinates p) c+‖c‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (complexPlaneCoordinates p-c) c
    rw [complexPlaneCoordinates_norm] at htri
    exact mem_ball.mpr (by rw [dist_zero_right]; linarith [hp.2])
  have hi : IntegrableOn (fun p => D.imagGradient p 0^2+D.imagGradient p 1^2) (ball 0 T) :=
    (D.imag_memLp T 0).integrable_sq.add (D.imag_memLp T 1).integrable_sq
  have hm := setIntegral_mono_set hi
    (Eventually.of_forall (fun p => add_nonneg (sq_nonneg (D.imagGradient p 0))
      (sq_nonneg (D.imagGradient p 1)))) (Eventually.of_forall (fun p hp => hAB hp))
  have he := D.imag_local_energy_le_error T hI
  have hb : (∫ p in A, D.imagGradient p 0^2+D.imagGradient p 1^2) ≤
      2*B+2*(volume (ball (0 : EuclideanPlane) T)).toReal := by
    exact hm.trans (he.trans (by linarith))
  exact (local_sobolev_height_log_bound φ c D hr hrR hx hy).trans
    (mul_le_mul_of_nonneg_left hb (by positivity))

 theorem homeomorphic_heights_equicontinuous {ι : Type*}
    (φ : ι → ℂ ≃ₜ ℂ)
    (D : ∀ i, PlaneLocalWeakComplex (fun x => φ i (complexPlaneCoordinates x)))
    {B : ℝ} (hB0 : 0 ≤ B)
    (hI : ∀ i, Integrable (fun p => (D i).imagGradient p 0^2+((D i).imagGradient p 1-1)^2))
    (hB : ∀ i, (∫ p, (D i).imagGradient p 0^2+((D i).imagGradient p 1-1)^2) ≤ B) :
    Equicontinuous (fun i z => (φ i z).im) := by
  intro c
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  let T := ‖c‖+2
  let C := 16*Real.pi*(2*B+2*(volume (ball (0 : EuclideanPlane) T)).toReal)
  have hC : 0 ≤ C := by dsimp only [C] <;> positivity
  let L := (C+1)/ε^2
  have hL : 0 < L := div_pos (by linarith) (sq_pos_of_pos hε)
  let δ := Real.exp (-L)
  have hδ : 0 < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hL.le))
  have hlog : Real.log (1/δ) = L := by
    dsimp only [δ]
    rw [one_div, Real.log_inv, Real.log_exp, neg_neg]
  have hEL : ε^2*L = C+1 := by
    dsimp only [L]
    field_simp
  refine ⟨δ, hδ, ?_⟩
  intro z hz i
  have hh := height_log_bound_from_error (φ i) c (D i) hδ hδ1
    (T := T) (by dsimp only [T] <;> linarith) (hI i) (hB i)
    (x := c) (y := z) (mem_closedBall_self hδ.le) (mem_closedBall.mpr hz.le)
  rw [hlog] at hh
  change |(φ i c).im-(φ i z).im|^2*L ≤ C at hh
  rw [Real.dist_eq]
  by_contra hn
  have hp := pow_le_pow_left₀ hε.le (le_of_not_gt hn) 2
  have hm := mul_le_mul_of_nonneg_right hp hL.le
  nlinarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_HeightCompactness
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact-open Ascoli extraction used for real height coordinates. -/
open Set Function Filter Topology
open scoped Topology UniformConvergence
noncomputable section
namespace CircleDomainRigidity

 theorem locally_uniform_height_subsequence (f : ℕ → C(ℂ, ℝ))
    (he : Equicontinuous (fun n z => f n z))
    (hb : ∀ z : ℂ, ∃ B : ℝ, ∀ n, |f n z| ≤ B) :
    ∃ (v : C(ℂ, ℝ)) (s : ℕ → ℕ), StrictMono s ∧
      TendstoLocallyUniformly (fun n z => f (s n) z) v atTop := by
  let S : Set C(ℂ, ℝ) := range f
  let chooseIndex : S → ℕ := fun g => Classical.choose g.property
  have hchoose (g : S) : f (chooseIndex g) = g := Classical.choose_spec g.property
  have hse : Equicontinuous (fun g : S => ((g : C(ℂ, ℝ)) : ℂ → ℝ)) := by
    have hh := he.comp chooseIndex
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext g z
    exact congrArg (fun a : C(ℂ, ℝ) => a z) (hchoose g).symm
  have hcover : ⋃₀ {K : Set ℂ | IsCompact K} = univ := by
    apply eq_univ_of_forall
    intro z
    exact mem_sUnion.mpr ⟨{z}, isCompact_singleton, mem_singleton z⟩
  let : T2Space (ℂ →ᵤ[{K : Set ℂ | IsCompact K}] ℝ) :=
    UniformOnFun.t2Space_of_covering hcover
  have hclosed : IsClosedEmbedding
      (UniformOnFun.ofFun {K : Set ℂ | IsCompact K} ∘
        (fun g : C(ℂ, ℝ) => (g : ℂ → ℝ))) :=
    ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
  have hc : IsCompact (closure S) :=
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (fun K hK => hK) hclosed
      (fun K _ => hse.equicontinuousOn K) (fun _ _ z _ => by
        obtain ⟨B, hB⟩ := hb z
        refine ⟨Icc (-B) B, isCompact_Icc, ?_⟩
        rintro g ⟨n, rfl⟩
        exact abs_le.mp (hB n))
  obtain ⟨v, _, s, hs, hv⟩ := hc.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  refine ⟨v, s, hs, ?_⟩
  exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hv

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_HomeomorphicHeightBounds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common exterior bound gives common bounds for homeomorphic height
coordinates on each compact disk, by the proved boundary range principle. -/
open Set Function Filter Metric Asymptotics Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem homeomorphic_height_bound {φ : ℂ ≃ₜ ℂ} {R S : ℝ}
    (hR : 0 < R) (hS : 2*R ≤ S)
    (hb : ∀ z : ℂ, 2*R ≤ ‖z‖ → ‖φ z-z‖ ≤ R) :
    ∀ z ∈ closedBall (0 : ℂ) S, |(φ z).im| ≤ S+R := by
  have hSp : 0 < S := lt_of_lt_of_le (mul_pos (by norm_num) hR) hS
  have hfront (z : ℂ) (hz : z ∈ frontier (closedBall (0 : ℂ) S)) : |(φ z).im| ≤ S+R := by
    have hn : ‖z‖ = S := by
      simpa only [frontier_closedBall (0 : ℂ) hSp.ne', mem_sphere, dist_zero_right] using hz
    have hnorm : ‖φ z‖ ≤ R+S := by
      calc
        ‖φ z‖ = ‖(φ z-z)+z‖ := by rw [sub_add_cancel]
        _ ≤ ‖φ z-z‖ + ‖z‖ := norm_add_le _ _
        _ ≤ R+S := add_le_add (hb z (by rw [hn]; exact hS)) hn.le
    exact (Complex.abs_im_le_norm (φ z)).trans (by linarith)
  have hu := homeomorphic_im_le_of_boundary φ (isCompact_closedBall (0 : ℂ) S)
    (fun z hz => (abs_le.mp (hfront z hz)).2)
  have hl := homeomorphic_im_ge_of_boundary φ (isCompact_closedBall (0 : ℂ) S)
    (fun z hz => (abs_le.mp (hfront z hz)).1)
  exact fun z hz => abs_le.mpr ⟨hl z hz, hu z hz⟩

 theorem normalized_homeomorphic_height_bound
    (harea : ExteriorCoefficientAreaTheorem) {φ : ℂ ≃ₜ ℂ} {R S : ℝ}
    (hR : 0 < R) (hS : 2*R ≤ S)
    (hh : DifferentiableOn ℂ φ {z | R < ‖z‖})
    (hnorm : (fun z => φ z-z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ∀ z ∈ closedBall (0 : ℂ) S, |(φ z).im| ≤ S+R :=
  homeomorphic_height_bound hR hS
    (harea.scaled_exterior_bound hR hh φ.injective.injOn hnorm)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConductivityHeightCompactness
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Locally uniform compactness of the actual normalized conductivity
heights from their energy budget and common exterior disk. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem conductivity_height_subsequence
    (harea : ExteriorCoefficientAreaTheorem)
    (φ : ℕ → ℂ ≃ₜ ℂ)
    (D : ∀ n, PlaneLocalWeakComplex (fun x => φ n (complexPlaneCoordinates x)))
    {B R : ℝ} (hB0 : 0 ≤ B) (hR : 0 < R)
    (hI : ∀ n, Integrable (fun p => (D n).imagGradient p 0^2+((D n).imagGradient p 1-1)^2))
    (hB : ∀ n, (∫ p, (D n).imagGradient p 0^2+((D n).imagGradient p 1-1)^2) ≤ B)
    (hh : ∀ n, DifferentiableOn ℂ (φ n) {z | R < ‖z‖})
    (hnorm : ∀ n, (fun z => φ n z-z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ∃ (v : C(ℂ, ℝ)) (s : ℕ → ℕ), StrictMono s ∧
      TendstoLocallyUniformly (fun n z => (φ (s n) z).im) v atTop := by
  let f : ℕ → C(ℂ, ℝ) := fun n => ⟨fun z => (φ n z).im,
    Complex.continuous_im.comp (φ n).continuous⟩
  apply locally_uniform_height_subsequence f
    (homeomorphic_heights_equicontinuous φ D hB0 hI hB)
  intro z
  let S := max (2*R) ‖z‖
  refine ⟨S+R, ?_⟩
  intro n
  exact normalized_homeomorphic_height_bound harea hR (le_max_left _ _)
    (hh n) (hnorm n) z (mem_closedBall.mpr (by
      simpa only [dist_zero_right] using le_max_right (2*R) ‖z‖))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RestrictedWeakPairing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting global weak L2 pairings to a finite-measure set, with a
fixed scalar added to each field. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem restricted_shifted_weak_pairing
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {F : Set X}
    (hF : MeasurableSet F) [IsFiniteMeasure (μ.restrict F)]
    {u : ℕ → X → ℝ} (hu : ∀ n, MemLp (u n) 2 μ)
    (G : Lp ℝ 2 μ)
    (h : ∀ w : Lp ℝ 2 μ, Tendsto (fun n => ∫ p, u n p*w p ∂μ) atTop
      (𝓝 (∫ p, G p*w p ∂μ))) (a : ℝ) (w : Lp ℝ 2 (μ.restrict F)) :
    Tendsto (fun n => ∫ p in F, (u n p+a)*w p ∂μ) atTop
      (𝓝 (∫ p in F, (G p+a)*w p ∂μ)) := by
  let ψ : X → ℝ := F.indicator w
  have hψ : MemLp ψ 2 μ := (memLp_indicator_iff_restrict hF).mpr (Lp.memLp w)
  have he (f : X → ℝ) : (∫ p, f p*hψ.toLp ψ p ∂μ) = ∫ p in F, f p*w p ∂μ := by
    calc
      _ = ∫ p, f p*ψ p ∂μ := by
        apply integral_congr_ae
        filter_upwards [hψ.coeFn_toLp] with p hp
        rw [hp]
      _ = ∫ p, F.indicator (fun p => f p*w p) p ∂μ := by
        congr 1
        funext p
        by_cases hp : p ∈ F <;> simp [ψ, hp]
      _ = _ := integral_indicator hF
  have hl := h (hψ.toLp ψ)
  simp only [he] at hl
  have hwa : Integrable (fun p => a*w p) (μ.restrict F) :=
    ((Lp.memLp w).integrable (by norm_num)).const_mul a
  have he₀ (n : ℕ) : (∫ p in F, (u n p+a)*w p ∂μ) =
      (∫ p in F, u n p*w p ∂μ)+(∫ p in F, a*w p ∂μ) := by
    simp only [add_mul]
    exact integral_add (((hu n).restrict F).integrable_mul (Lp.memLp w)) hwa
  have he₁ : (∫ p in F, (G p+a)*w p ∂μ) =
      (∫ p in F, G p*w p ∂μ)+(∫ p in F, a*w p ∂μ) := by
    simp only [add_mul]
    exact integral_add (((Lp.memLp G).restrict F).integrable_mul (Lp.memLp w)) hwa
  simpa only [← he₀, ← he₁] using hl.add_const (∫ p in F, a*w p ∂μ)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConductivityWeakFields
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global L2 weak limits of the two error-gradient components of the
actual conductivity heights. The paired energy budget is retained. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem PlaneLocalWeakComplex.imag_aestronglyMeasurable
    {f : EuclideanPlane → ℂ} (D : PlaneLocalWeakComplex f) (i : Fin 2) :
    AEStronglyMeasurable (fun p => D.imagGradient p i) volume :=
  (aecover_ball (μ := volume) (x := (0 : EuclideanPlane)) tendsto_id).aestronglyMeasurable
    (fun R => (D.imag_memLp R i).aestronglyMeasurable)

 theorem PlaneLocalWeakComplex.error_memLp
    {f : EuclideanPlane → ℂ} (D : PlaneLocalWeakComplex f)
    (hI : Integrable (fun p => D.imagGradient p 0^2+(D.imagGradient p 1-1)^2)) :
    MemLp (fun p => D.imagGradient p 0) 2 volume ∧
      MemLp (fun p => D.imagGradient p 1-1) 2 volume := by
  have hm0 := D.imag_aestronglyMeasurable 0
  have hm1 : AEStronglyMeasurable (fun p => D.imagGradient p 1-1) volume :=
    (D.imag_aestronglyMeasurable 1).sub aestronglyMeasurable_const
  constructor
  · apply (memLp_two_iff_integrable_sq hm0).mpr
    exact hI.mono' (hm0.pow 2) (Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact le_add_of_nonneg_right (sq_nonneg _)))
  · apply (memLp_two_iff_integrable_sq hm1).mpr
    exact hI.mono' (hm1.pow 2) (Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact le_add_of_nonneg_left (sq_nonneg _)))

 theorem conductivity_weak_error_fields
    (f : ℕ → EuclideanPlane → ℂ) (D : ∀ n, PlaneLocalWeakComplex (f n))
    {B : ℝ}
    (hI : ∀ n, Integrable (fun p => (D n).imagGradient p 0^2+((D n).imagGradient p 1-1)^2))
    (hB : ∀ n, (∫ p, (D n).imagGradient p 0^2+((D n).imagGradient p 1-1)^2) ≤ B) :
    ∃ (G₀ G₁ : Lp ℝ 2 (volume : Measure EuclideanPlane)) (s : ℕ → ℕ),
      StrictMono s ∧
      (∀ w : Lp ℝ 2 (volume : Measure EuclideanPlane),
        Tendsto (fun n => ∫ p, (D (s n)).imagGradient p 0*w p) atTop
          (𝓝 (∫ p, G₀ p*w p))) ∧
      (∀ w : Lp ℝ 2 (volume : Measure EuclideanPlane),
        Tendsto (fun n => ∫ p, ((D (s n)).imagGradient p 1-1)*w p) atTop
          (𝓝 (∫ p, G₁ p*w p))) ∧
      (∫ p, G₀ p^2+G₁ p^2) ≤ B := by
  let u₀ : ℕ → EuclideanPlane → ℝ := fun n p => (D n).imagGradient p 0
  let u₁ : ℕ → EuclideanPlane → ℝ := fun n p => (D n).imagGradient p 1-1
  have hm₀ (n : ℕ) : MemLp (u₀ n) 2 volume := ((D n).error_memLp (hI n)).1
  have hm₁ (n : ℕ) : MemLp (u₁ n) 2 volume := ((D n).error_memLp (hI n)).2
  have hnorm (n : ℕ) : ‖(hm₀ n).toLp (u₀ n)‖ ≤ B+1 ∧
      ‖(hm₁ n).toLp (u₁ n)‖ ≤ B+1 := by
    have hn0 : ‖(hm₀ n).toLp (u₀ n)‖^2 = ∫ p, u₀ n p^2 := by
      rw [Lp.norm_toLp, integral_sq_eq_eLpNorm_toReal_sq (hm₀ n)]
    have hn1 : ‖(hm₁ n).toLp (u₁ n)‖^2 = ∫ p, u₁ n p^2 := by
      rw [Lp.norm_toLp, integral_sq_eq_eLpNorm_toReal_sq (hm₁ n)]
    have hb := hB n
    change (∫ p, u₀ n p^2+u₁ n p^2) ≤ B at hb
    rw [integral_add (hm₀ n).integrable_sq (hm₁ n).integrable_sq, ← hn0, ← hn1] at hb
    constructor <;> nlinarith [sq_nonneg (‖(hm₀ n).toLp (u₀ n)‖-1),
      sq_nonneg (‖(hm₁ n).toLp (u₁ n)‖-1), sq_nonneg ‖(hm₀ n).toLp (u₀ n)‖,
      sq_nonneg ‖(hm₁ n).toLp (u₁ n)‖]
  obtain ⟨G₀, _, s₀, hs₀, h₀⟩ := exists_L2_weak_subsequence volume u₀ hm₀ (B+1)
    (fun n => (hnorm n).1)
  obtain ⟨G₁, _, s₁, hs₁, h₁⟩ := exists_L2_weak_subsequence volume (u₁ ∘ s₀)
    (fun n => hm₁ (s₀ n)) (B+1) (fun n => (hnorm (s₀ n)).2)
  let s := s₀ ∘ s₁
  have hlim₀ (w : Lp ℝ 2 (volume : Measure EuclideanPlane)) :
      Tendsto (fun n => ∫ p, u₀ (s n) p*w p) atTop (𝓝 (∫ p, G₀ p*w p)) :=
    (h₀ w).comp hs₁.tendsto_atTop
  refine ⟨G₀, G₁, s, hs₀.comp hs₁, hlim₀, h₁, ?_⟩
  exact paired_L2_energy_le (fun n => hm₀ (s n)) (fun n => hm₁ (s n)) G₀ G₁
    (ε := fun _ => 0) tendsto_const_nhds
    (Eventually.of_forall (fun n => by simpa only [add_zero] using hB (s n)))
    (hlim₀ G₀) (h₁ G₁)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_HeightTestLimit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact test pairings converge for the locally bounded pointwise
limit of the actual continuous height functions. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem height_test_integral_tendsto
    (f : ℕ → EuclideanPlane → ℝ) (hf : ∀ n, Continuous (f n))
    {v : EuclideanPlane → ℝ}
    (hp : ∀ p, Tendsto (fun n => f n p) atTop (𝓝 (v p)))
    (hb : ∀ K : Set EuclideanPlane, IsCompact K →
      ∃ C : ℝ, ∀ n p, p ∈ K → ‖f n p‖ ≤ C)
    {ψ : EuclideanPlane → ℝ} (hψ : Continuous ψ) (hs : HasCompactSupport ψ) :
    Tendsto (fun n => ∫ p, f n p*ψ p) atTop (𝓝 (∫ p, v p*ψ p)) := by
  obtain ⟨C, hC⟩ := hb (tsupport ψ) hs.isCompact
  apply tendsto_integral_of_dominated_convergence (bound := fun p => C*‖ψ p‖)
  · intro n
    exact (hf n).aestronglyMeasurable.mul hψ.aestronglyMeasurable
  · exact (hψ.integrable_of_hasCompactSupport hs).norm.const_mul C
  · intro n
    apply Eventually.of_forall
    intro p
    by_cases hp : p ∈ tsupport ψ
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC n p hp) (norm_nonneg _)
    · simp only [image_eq_zero_of_notMem_tsupport hp, mul_zero, norm_zero, le_refl]
  · exact Eventually.of_forall (fun p => (hp p).mul_const (ψ p))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeakHeightIdentification
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of weak error-gradient limits with the derivatives
of the actual continuous height limit. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem weak_height_identification
    (f : ℕ → EuclideanPlane → ℂ) (D : ∀ n, PlaneLocalWeakComplex (f n))
    (hf : ∀ n, Continuous (f n)) {v : EuclideanPlane → ℝ}
    (hp : ∀ p, Tendsto (fun n => (f n p).im) atTop (𝓝 (v p)))
    (hb : ∀ K : Set EuclideanPlane, IsCompact K →
      ∃ C : ℝ, ∀ n p, p ∈ K → ‖(f n p).im‖ ≤ C)
    (hI : ∀ n, Integrable (fun p => (D n).imagGradient p 0^2+((D n).imagGradient p 1-1)^2))
    (G₀ G₁ : Lp ℝ 2 (volume : Measure EuclideanPlane))
    (h₀ : ∀ w : Lp ℝ 2 (volume : Measure EuclideanPlane),
      Tendsto (fun n => ∫ p, (D n).imagGradient p 0*w p) atTop (𝓝 (∫ p, G₀ p*w p)))
    (h₁ : ∀ w : Lp ℝ 2 (volume : Measure EuclideanPlane),
      Tendsto (fun n => ∫ p, ((D n).imagGradient p 1-1)*w p) atTop (𝓝 (∫ p, G₁ p*w p))) :
    DeGiorgi.HasWeakGrad (heightLimitGradient G₀ G₁) v univ := by
  have hpair {u : ℕ → EuclideanPlane → ℝ} {G : EuclideanPlane → ℝ}
      (h : ∀ w : Lp ℝ 2 (volume : Measure EuclideanPlane),
        Tendsto (fun n => ∫ p, u n p*w p) atTop (𝓝 (∫ p, G p*w p)))
      {ψ : EuclideanPlane → ℝ} (hψ : MemLp ψ 2 volume) :
      Tendsto (fun n => ∫ p, u n p*ψ p) atTop (𝓝 (∫ p, G p*ψ p)) := by
    have he (a : EuclideanPlane → ℝ) :
        (∫ p, a p*hψ.toLp ψ p) = ∫ p, a p*ψ p := by
      apply integral_congr_ae
      filter_upwards [hψ.coeFn_toLp] with p hp
      rw [hp]
    simpa only [he] using h (hψ.toLp ψ)
  intro i ψ hψ hs _
  simp only [Measure.restrict_univ]
  let test : EuclideanPlane → ℝ := fun p => fderiv ℝ ψ p (EuclideanSpace.single i 1)
  have ht : Continuous test := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hst : HasCompactSupport test := hs.fderiv_apply (𝕜 := ℝ) _
  have hl := height_test_integral_tendsto (fun n p => (f n p).im)
    (fun n => Complex.continuous_im.comp (hf n)) hp hb ht hst
  have hψL : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hs
  have hright : Tendsto (fun n => ∫ p, (D n).imagGradient p i*ψ p) atTop
      (𝓝 (∫ p, heightLimitGradient G₀ G₁ p i*ψ p)) := by
    fin_cases i
    · simpa [heightLimitGradient] using hpair h₀ hψL
    · have hh := (hpair h₁ hψL).add_const (∫ p, ψ p)
      have hψI : Integrable ψ volume := hψ.continuous.integrable_of_hasCompactSupport hs
      have he (n : ℕ) : (∫ p, ((D n).imagGradient p 1-1)*ψ p)+(∫ p, ψ p) =
          ∫ p, (D n).imagGradient p 1*ψ p := by
        have hadd := integral_add (((D n).error_memLp (hI n)).2.integrable_mul hψL) hψI
        simp only [Pi.mul_apply] at hadd
        rw [← hadd]
        congr 1
        funext p
        ring
      have hG : (∫ p, G₁ p*ψ p)+(∫ p, ψ p) = ∫ p, (G₁ p+1)*ψ p := by
        have hadd := integral_add ((Lp.memLp G₁).integrable_mul hψL) hψI
        simp only [Pi.mul_apply] at hadd
        rw [← hadd]
        congr 1
        funext p
        ring
      simpa [he, hG, heightLimitGradient] using hh
  have hweak (n : ℕ) : (∫ p, (f n p).im*test p) =
      -(∫ p, (D n).imagGradient p i*ψ p) := by
    simpa only [Measure.restrict_univ] using (D n).imag_weak i ψ hψ hs (subset_univ _)
  have hh : Tendsto (fun n => -(∫ p, (D n).imagGradient p i*ψ p)) atTop
      (𝓝 (∫ p, v p*test p)) := hl.congr' (Eventually.of_forall hweak)
  exact tendsto_nhds_unique hh hright.neg

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeakHeightNull
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vanishing complementary energies force the actual limiting height
gradient to vanish there, including on positive-area dust. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem weak_height_gradient_zero
    (f : ℕ → EuclideanPlane → ℂ) (D : ∀ n, PlaneLocalWeakComplex (f n))
    (hI : ∀ n, Integrable (fun p => (D n).imagGradient p 0^2+((D n).imagGradient p 1-1)^2))
    (G₀ G₁ : Lp ℝ 2 (volume : Measure EuclideanPlane))
    (h₀ : ∀ w : Lp ℝ 2 (volume : Measure EuclideanPlane),
      Tendsto (fun n => ∫ p, (D n).imagGradient p 0*w p) atTop (𝓝 (∫ p, G₀ p*w p)))
    (h₁ : ∀ w : Lp ℝ 2 (volume : Measure EuclideanPlane),
      Tendsto (fun n => ∫ p, ((D n).imagGradient p 1-1)*w p) atTop (𝓝 (∫ p, G₁ p*w p)))
    {F : Set EuclideanPlane} (hF : MeasurableSet F) (hFfin : volume F < ∞)
    (he : Tendsto (fun n => ∫ p in F,
      (D n).imagGradient p 0^2+(D n).imagGradient p 1^2) atTop (𝓝 0)) :
    ∀ᵐ p ∂volume.restrict F, heightLimitGradient G₀ G₁ p = 0 := by
  let μ := volume.restrict F
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hFfin.ne
  have hG₀ : MemLp G₀ 2 μ := (Lp.memLp G₀).restrict F
  have hG₁ : MemLp (fun p => G₁ p+1) 2 μ := ((Lp.memLp G₁).restrict F).add (memLp_const 1)
  let V₀ := hG₀.toLp G₀
  let V₁ := hG₁.toLp (fun p => G₁ p+1)
  have hm₀ (n : ℕ) : MemLp (fun p => (D n).imagGradient p 0) 2 μ :=
    (((D n).error_memLp (hI n)).1).restrict F
  have hm₁ (n : ℕ) : MemLp (fun p => (D n).imagGradient p 1) 2 μ := by
    have hh := ((((D n).error_memLp (hI n)).2).restrict F).add (memLp_const (1 : ℝ))
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    simp only [Pi.add_apply]
    ring
  have hp₀ (w : Lp ℝ 2 μ) :
      Tendsto (fun n => ∫ p, (D n).imagGradient p 0*w p ∂μ) atTop
        (𝓝 (∫ p, V₀ p*w p ∂μ)) := by
    have hh := restricted_shifted_weak_pairing hF
      (fun n => ((D n).error_memLp (hI n)).1) G₀ h₀ 0 w
    simp only [add_zero] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    apply integral_congr_ae
    filter_upwards [hG₀.coeFn_toLp] with p hp
    rw [hp]
  have hp₁ (w : Lp ℝ 2 μ) :
      Tendsto (fun n => ∫ p, (D n).imagGradient p 1*w p ∂μ) atTop
        (𝓝 (∫ p, V₁ p*w p ∂μ)) := by
    have hh := restricted_shifted_weak_pairing hF
      (fun n => ((D n).error_memLp (hI n)).2) G₁ h₁ 1 w
    simp only [sub_add_cancel] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    apply integral_congr_ae
    filter_upwards [hG₁.coeFn_toLp] with p hp
    rw [hp]
  have hb : (∫ p, V₀ p^2+V₁ p^2 ∂μ) ≤ 0 :=
    paired_L2_energy_le hm₀ hm₁ V₀ V₁ (B := 0) he (Eventually.of_forall (fun n => by
      change (∫ p in F, (D n).imagGradient p 0^2+(D n).imagGradient p 1^2) ≤
        0+(∫ p in F, (D n).imagGradient p 0^2+(D n).imagGradient p 1^2)
      exact le_add_of_nonneg_left (le_refl 0)))
      (hp₀ V₀) (hp₁ V₁)
  have hi : Integrable (fun p => V₀ p^2+V₁ p^2) μ :=
    (Lp.memLp V₀).integrable_sq.add (Lp.memLp V₁).integrable_sq
  have hzero : (∫ p, V₀ p^2+V₁ p^2 ∂μ) = 0 :=
    le_antisymm hb (integral_nonneg (fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun p => add_nonneg (sq_nonneg (V₀ p)) (sq_nonneg (V₁ p))) hi).mp hzero
  filter_upwards [hae, hG₀.coeFn_toLp, hG₁.coeFn_toLp] with p hp h0 h1
  change V₀ p^2+V₁ p^2 = 0 at hp
  change V₀ p = G₀ p at h0
  change V₁ p = G₁ p+1 at h1
  rw [h0, h1] at hp
  have hp' : G₀ p^2+(G₁ p+1)^2 = 0 := hp
  have hz0 : G₀ p = 0 := by nlinarith [sq_nonneg (G₁ p+1)]
  have hz1 : G₁ p+1 = 0 := by nlinarith [sq_nonneg (G₀ p)]
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  funext i
  fin_cases i <;> simp [heightLimitGradient, hz0, hz1]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConductivityHeightLimit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continuous height limit and its actual weak derivatives, with the
original error budget and zero gradient on the conductivity support. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_conductivity_height_limit
    (harea : ExteriorCoefficientAreaTheorem)
    (φ : ℕ → ℂ ≃ₜ ℂ)
    (D : ∀ n, PlaneLocalWeakComplex (fun p => φ n (complexPlaneCoordinates p)))
    {B R : ℝ} (hB0 : 0 ≤ B) (hR : 0 < R)
    (hI : ∀ n, Integrable (fun p => (D n).imagGradient p 0^2+((D n).imagGradient p 1-1)^2))
    (hB : ∀ n, (∫ p, (D n).imagGradient p 0^2+((D n).imagGradient p 1-1)^2) ≤ B)
    (hh : ∀ n, DifferentiableOn ℂ (φ n) {z | R < ‖z‖})
    (hnorm : ∀ n, (fun z => φ n z-z) =O[cobounded ℂ] (fun z => z⁻¹))
    {F : Set EuclideanPlane} (hF : IsCompact F)
    (hFE : Tendsto (fun n => ∫ p in F,
      (D n).imagGradient p 0^2+(D n).imagGradient p 1^2) atTop (𝓝 0)) :
    ∃ (v : C(ℂ, ℝ)) (G₀ G₁ : Lp ℝ 2 (volume : Measure EuclideanPlane)) (s : ℕ → ℕ),
      StrictMono s ∧ TendstoLocallyUniformly (fun n z => (φ (s n) z).im) v atTop ∧
      DeGiorgi.HasWeakGrad (heightLimitGradient G₀ G₁) (v ∘ complexPlaneCoordinates) univ ∧
      (∫ p, G₀ p^2+G₁ p^2) ≤ B ∧
      (∀ᵐ p ∂volume.restrict F, heightLimitGradient G₀ G₁ p = 0) := by
  obtain ⟨v, s₀, hs₀, hv⟩ := conductivity_height_subsequence harea φ D hB0 hR hI hB hh hnorm
  obtain ⟨G₀, G₁, s₁, hs₁, h₀, h₁, henergy⟩ := conductivity_weak_error_fields
    (fun n p => φ (s₀ n) (complexPlaneCoordinates p)) (fun n => D (s₀ n))
    (fun n => hI (s₀ n)) (fun n => hB (s₀ n))
  let s := s₀ ∘ s₁
  have hs : StrictMono s := hs₀.comp hs₁
  have hlim : TendstoLocallyUniformly (fun n z => (φ (s n) z).im) v atTop := by
    intro U hU z
    obtain ⟨O, hO, h⟩ := hv U hU z
    exact ⟨O, hO, hs₁.tendsto_atTop.eventually h⟩
  have hpoint (p : EuclideanPlane) :
      Tendsto (fun n => (φ (s n) (complexPlaneCoordinates p)).im) atTop
        (𝓝 (v (complexPlaneCoordinates p))) :=
    hlim.tendstoLocallyUniformlyOn.tendsto_at (mem_univ _)
  have hbounded (K : Set EuclideanPlane) (hK : IsCompact K) :
      ∃ C : ℝ, ∀ n p, p ∈ K → ‖(φ (s n) (complexPlaneCoordinates p)).im‖ ≤ C := by
    obtain ⟨S, hS⟩ := hK.isBounded.subset_ball 0
    let T := max (2*R) S
    refine ⟨T+R, ?_⟩
    intro n p hp
    have hpT : complexPlaneCoordinates p ∈ closedBall 0 T := by
      have hpS : ‖p‖ < S := by simpa only [mem_ball, dist_zero_right] using hS hp
      simpa only [mem_closedBall, dist_zero_right, complexPlaneCoordinates_norm] using
        hpS.le.trans (le_max_right (2*R) S)
    simpa only [Real.norm_eq_abs] using normalized_homeomorphic_height_bound harea hR
      (le_max_left (2*R) S) (hh (s n)) (hnorm (s n)) (complexPlaneCoordinates p) hpT
  have hw := weak_height_identification (fun n p => φ (s n) (complexPlaneCoordinates p))
    (fun n => D (s n)) (fun n => (φ (s n)).continuous.comp complexPlaneCoordinates.continuous)
    hpoint hbounded (fun n => hI (s n)) G₀ G₁ h₀ h₁
  have hz := weak_height_gradient_zero (fun n p => φ (s n) (complexPlaneCoordinates p))
    (fun n => D (s n)) (fun n => hI (s n)) G₀ G₁ h₀ h₁ hF.measurableSet
    hF.measure_lt_top (hFE.comp hs.tendsto_atTop)
  exact ⟨v, G₀, G₁, s, hs, hlim, hw, henergy, hz⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalMollificationCongruence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local almost-everywhere equality is preserved by mollification
where the actual averaging ball stays inside the equality region. -/
open Set Filter MeasureTheory Metric Function
open scoped Topology Convolution
noncomputable section
namespace CircleDomainRigidity

 theorem planarMollification_congr_on_ball {u v : EuclideanPlane → ℝ}
    {U : Set EuclideanPlane} (huv : ∀ᵐ y ∂volume, y ∈ U → u y = v y)
    (n : ℕ) (x : EuclideanPlane)
    (hball : ball x (DeGiorgi.shrinkingBump (d := 2) n).rOut ⊆ U) :
    planarMollification u n x = planarMollification v n x := by
  let κ := (DeGiorgi.shrinkingBump (d := 2) n).normed volume
  have hflip (f : EuclideanPlane → ℝ) : planarMollification f n x =
      ∫ y, f y * κ (x-y) := by
    rw [planarMollification, ← convolution_flip]
    change (∫ y, κ (x-y) * f y) = _
    apply integral_congr_ae
    exact Eventually.of_forall (fun y => mul_comm _ _)
  rw [hflip u, hflip v]
  apply integral_congr_ae
  filter_upwards [huv] with y hy
  by_cases hk : κ (x-y) = 0
  · rw [hk, mul_zero, mul_zero]
  · have hm : x-y ∈ support κ := hk
    rw [(DeGiorgi.shrinkingBump (d := 2) n).support_normed_eq] at hm
    have hd : y ∈ ball x (DeGiorgi.shrinkingBump (d := 2) n).rOut := by
      simpa only [mem_ball, dist_eq_norm, sub_zero, norm_sub_rev] using hm
    rw [hy (hball hd)]

 theorem planarMollification_neg (u : EuclideanPlane → ℝ) (n : ℕ) :
    planarMollification (fun x => -u x) n = fun x => -planarMollification u n x := by
  funext x
  simp only [planarMollification, convolution, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul, mul_neg, integral_neg]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalCauchyRiemann
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real Cauchy–Riemann equations in the actual physical plane
coordinates imply complex differentiability. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity

 theorem differentiableAt_complex_of_real_linear {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z)
    (hI : fderiv ℝ f z Complex.I = Complex.I * fderiv ℝ f z 1) :
    DifferentiableAt ℂ f z := by
  let A : ℂ →L[ℂ] ℂ := (fderiv ℝ f z 1) • ContinuousLinearMap.id ℂ ℂ
  apply (hasFDerivAt_of_restrictScalars ℝ hf.hasFDerivAt (f' := A) ?_).differentiableAt
  ext w
  change fderiv ℝ f z 1 * w = fderiv ℝ f z w
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_rhs => rw [hw, map_add, map_smul, map_smul, hI]
  simp only [Complex.real_smul]
  conv_lhs => rw [← Complex.re_add_im w]
  ring

 theorem complexifyPair_differentiableAt {a b : EuclideanPlane → ℝ} {x : EuclideanPlane}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (hX : fderiv ℝ a x (EuclideanSpace.single 0 1) =
      fderiv ℝ b x (EuclideanSpace.single 1 1))
    (hY : fderiv ℝ a x (EuclideanSpace.single 1 1) =
      -fderiv ℝ b x (EuclideanSpace.single 0 1)) :
    DifferentiableAt ℂ (complexifyPair a b) (complexPlaneCoordinates x) := by
  have haa : HasFDerivAt a (fderiv ℝ a x)
      (complexPlaneCoordinates.symm (complexPlaneCoordinates x)) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using ha.hasFDerivAt
  have hbb : HasFDerivAt b (fderiv ℝ b x)
      (complexPlaneCoordinates.symm (complexPlaneCoordinates x)) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hb.hasFDerivAt
  have hax := haa.comp (complexPlaneCoordinates x) complexPlaneCoordinates.symm.hasFDerivAt
  have hbx := hbb.comp (complexPlaneCoordinates x) complexPlaneCoordinates.symm.hasFDerivAt
  have har := Complex.ofRealCLM.hasFDerivAt.comp _ hax
  have hbr := Complex.ofRealCLM.hasFDerivAt.comp _ hbx
  have hd := har.add (hbr.const_mul Complex.I)
  apply differentiableAt_complex_of_real_linear hd.differentiableAt
  rw [hd.fderiv]
  have h0 : complexPlaneCoordinates.symm (1 : ℂ) = EuclideanSpace.single 0 1 := by
    apply complexPlaneCoordinates.injective
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    apply Complex.ext <;> simp [complexPlaneCoordinates_apply]
  have h1 : complexPlaneCoordinates.symm Complex.I = EuclideanSpace.single 1 1 := by
    apply complexPlaneCoordinates.injective
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    apply Complex.ext <;> simp [complexPlaneCoordinates_apply]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearEquiv.coe_coe,
    Complex.ofRealCLM_apply, smul_eq_mul, h0, h1]
  rw [hX, hY]
  apply Complex.ext <;> simp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalComplexWeyl
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local Weyl lemma for the actual weak complex differential. Positive
mollification preserves the Cauchy–Riemann equations on smaller compact
sets, and locally uniform convergence identifies the holomorphic limit. -/
open Set Filter Function MeasureTheory Metric
open scoped Topology Convolution
noncomputable section
namespace CircleDomainRigidity

 theorem complexifyPair_mollification_tendsto {a b : EuclideanPlane → ℝ}
    (ha : Continuous a) (hb : Continuous b) :
    TendstoLocallyUniformly
      (fun n => complexifyPair (planarMollification a n) (planarMollification b n))
      (complexifyPair a b) atTop := by
  apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
  intro K hK
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hKi : IsCompact (complexPlaneCoordinates.symm '' K) := hK.image
    complexPlaneCoordinates.symm.continuous
  have hpa := planarMollification_uniform_on_compact ha.aestronglyMeasurable hKi
    isOpen_univ (subset_univ _) ha.continuousOn (half_pos hε)
  have hpb := planarMollification_uniform_on_compact hb.aestronglyMeasurable hKi
    isOpen_univ (subset_univ _) hb.continuousOn (half_pos hε)
  filter_upwards [hpa, hpb] with n hnA hnB z hz
  have hzi : complexPlaneCoordinates.symm z ∈ complexPlaneCoordinates.symm '' K :=
    mem_image_of_mem _ hz
  have he : complexifyPair a b z - complexifyPair (planarMollification a n)
      (planarMollification b n) z =
      ((a (complexPlaneCoordinates.symm z) - planarMollification a n (complexPlaneCoordinates.symm z) : ℝ) : ℂ) +
      Complex.I * ((b (complexPlaneCoordinates.symm z) - planarMollification b n (complexPlaneCoordinates.symm z) : ℝ) : ℂ) := by
    simp only [complexifyPair, Complex.ofReal_sub]
    ring
  rw [dist_eq_norm, he]
  apply lt_of_le_of_lt (norm_add_le _ _)
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm (a _), abs_sub_comm (b _)]
  linarith [hnA _ hzi, hnB _ hzi]

namespace PlaneLocalWeakComplex

 theorem mollified_differentiableAt {f : EuclideanPlane → ℂ}
    (D : PlaneLocalWeakComplex f) (hf : Continuous f) {U : Set EuclideanPlane}
    (hcr : ∀ᵐ x ∂volume, x ∈ U →
      D.realGradient x 0 = D.imagGradient x 1 ∧ D.realGradient x 1 = -D.imagGradient x 0)
    (n : ℕ) (x : EuclideanPlane)
    (hball : ball x (DeGiorgi.shrinkingBump (d := 2) n).rOut ⊆ U) :
    DifferentiableAt ℂ
      (complexifyPair (planarMollification (fun y => (f y).re) n)
        (planarMollification (fun y => (f y).im) n)) (complexPlaneCoordinates x) := by
  have ha : LocallyIntegrable (fun y => (f y).re) volume :=
    (Complex.continuous_re.comp hf).locallyIntegrable
  have hb : LocallyIntegrable (fun y => (f y).im) volume :=
    (Complex.continuous_im.comp hf).locallyIntegrable
  apply complexifyPair_differentiableAt
    ((planarMollification_smooth ha n).differentiable (by simp) x)
    ((planarMollification_smooth hb n).differentiable (by simp) x)
  · rw [planarMollification_derivative_of_weak ha 0 (D.real_weak 0),
      planarMollification_derivative_of_weak hb 1 (D.imag_weak 1)]
    exact planarMollification_congr_on_ball (hcr.mono fun y hy hyU => (hy hyU).1) n x hball
  · rw [planarMollification_derivative_of_weak ha 1 (D.real_weak 1),
      planarMollification_derivative_of_weak hb 0 (D.imag_weak 0)]
    change planarMollification (fun y => D.realGradient y 1) n x =
      -planarMollification (fun y => D.imagGradient y 0) n x
    calc
      _ = planarMollification (fun y => -D.imagGradient y 0) n x :=
        planarMollification_congr_on_ball (hcr.mono fun y hy hyU => (hy hyU).2) n x hball
      _ = _ := congrFun (planarMollification_neg (fun y => D.imagGradient y 0) n) x

 theorem holomorphic_on_of_cauchyRiemann {f : EuclideanPlane → ℂ}
    (D : PlaneLocalWeakComplex f) (hf : Continuous f) {U : Set EuclideanPlane} (hU : IsOpen U)
    (hcr : ∀ᵐ x ∂volume, x ∈ U →
      D.realGradient x 0 = D.imagGradient x 1 ∧ D.realGradient x 1 = -D.imagGradient x 0) :
    DifferentiableOn ℂ (fun z => f (complexPlaneCoordinates.symm z))
      (complexPlaneCoordinates '' U) := by
  rintro z ⟨x, hx, rfl⟩
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let K := closedBall x (r/2)
  let V := complexPlaneCoordinates '' ball x (r/2)
  have hK : IsCompact K := isCompact_closedBall x (r/2)
  have hKU : K ⊆ U := (closedBall_subset_ball (half_lt_self hr)).trans hsub
  have hV : IsOpen V := complexPlaneCoordinates.toHomeomorph.isOpenMap _ isOpen_ball
  have hxV : complexPlaneCoordinates x ∈ V :=
    mem_image_of_mem _ (mem_ball_self (half_pos hr))
  let fn (n : ℕ) := complexifyPair (planarMollification (fun y => (f y).re) n)
    (planarMollification (fun y => (f y).im) n)
  have hfn : ∀ᶠ n in atTop, DifferentiableOn ℂ (fn n) V := by
    filter_upwards [planarMollifier_samples_eventually hK hU hKU] with n hn
    rintro w ⟨y, hy, rfl⟩
    exact (D.mollified_differentiableAt hf hcr n y (hn y (ball_subset_closedBall hy))).differentiableWithinAt
  have hlim : TendstoLocallyUniformly fn (fun z => f (complexPlaneCoordinates.symm z)) atTop := by
    have hh := complexifyPair_mollification_tendsto
      (Complex.continuous_re.comp hf) (Complex.continuous_im.comp hf)
    apply hh.congr_right
    intro w
    apply Complex.ext <;> simp [complexifyPair]
  have hlimV : TendstoLocallyUniformlyOn fn (fun z => f (complexPlaneCoordinates.symm z)) atTop V :=
    (tendstoLocallyUniformlyOn_univ.mpr hlim).mono (subset_univ V)
  have hd := hlimV.differentiableOn hfn hV
  exact (hd.differentiableAt (hV.mem_nhds hxV)).differentiableWithinAt

end PlaneLocalWeakComplex
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConductivityExterior
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed principal conductivity homeomorphism is holomorphic
off its coefficient support. Its principal Laurent germ and uniform
exterior decay follow from the proved local Weyl lemma. -/
open Set Filter Function MeasureTheory Asymptotics Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem PlaneLocalWeakComplex.conductivity_holomorphic_off
    {φ : ℂ → ℂ} (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    (hφ : Continuous φ) {F : Set EuclideanPlane} (hF : IsClosed F) (n : ℕ)
    (hsys : ∀ᵐ x ∂volume,
      D.realGradient x 0 = conductivityValue F n x * D.imagGradient x 1 ∧
      D.realGradient x 1 = -conductivityValue F n x * D.imagGradient x 0) :
    DifferentiableOn ℂ φ (complexPlaneCoordinates '' F)ᶜ := by
  have hcr : ∀ᵐ x ∂volume, x ∈ Fᶜ →
      D.realGradient x 0 = D.imagGradient x 1 ∧ D.realGradient x 1 = -D.imagGradient x 0 := by
    filter_upwards [hsys] with x hx hxF
    simpa only [conductivityValue, ite_eq_right hxF, one_mul, neg_mul, one_mul] using hx
  have hh := D.holomorphic_on_of_cauchyRiemann (hφ.comp complexPlaneCoordinates.continuous)
    hF.isOpen_compl hcr
  simpa only [ContinuousLinearEquiv.apply_symm_apply,
    image_compl_eq complexPlaneCoordinates.bijective] using hh

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevJacobianLocality
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact Sobolev replacements agreeing outside a closed region have
the same Jacobian integral over that region. This is the interior
replacement step in the conductivity area computation. -/
open Set Filter Function MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem weakGradient_eq_on_open {u v : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u univ) (hv : DeGiorgi.MemW1pWitness 2 v univ)
    {U : Set EuclideanPlane} (hU : IsOpen U) (heq : EqOn u v U) (i : Fin 2) :
    (fun x => hu.weakGrad x i) =ᵐ[volume.restrict U] fun x => hv.weakGrad x i := by
  let huU := hu.restrict hU (subset_univ U)
  let hvU := hv.restrict hU (subset_univ U)
  have hh := weakPartial_congrOn hU (huU.isWeakGrad i) heq
  exact hh.ae_eq hU (hvU.isWeakGrad i)
    ((huU.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
    ((hvU.weakGrad_component_memLp i).locallyIntegrable (by norm_num))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CompactWeakDerivativeIntegral
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact Sobolev perturbations contribute zero total first derivative.
The support and integrability of the actual weak derivative are proved,
so the boundary-flux replacement does not assume an unproved trace fact. -/
open Set Filter Function MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem compact_weakGradient_zero_off {u : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u univ) (i : Fin 2) :
    ∀ᵐ x ∂volume, x ∉ tsupport u → hu.weakGrad x i = 0 := by
  have heq : EqOn u (fun x => (0 : ℝ) * u x) (tsupport u)ᶜ := by
    intro x hx
    simp only [zero_mul]
    exact image_eq_zero_of_notMem_tsupport hx
  have hh := weakGradient_eq_on_open hu (hu.smul 0) isClosed_closure.isOpen_compl heq i
  have hh' := (ae_restrict_iff' isClosed_closure.measurableSet.compl).mp hh
  filter_upwards [hh'] with x hx hxU
  simpa only [DeGiorgi.MemW1pWitness.smul, zero_smul, PiLp.zero_apply] using hx hxU

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_HolomorphicHomeomorph
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A holomorphic plane homeomorphism has a holomorphic inverse on the
image domain. Isolated critical points are removed from the continuous
inverse; the chain rule then excludes them altogether. -/
open Set Filter Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem holomorphicHomeomorph_deriv_not_locally_zero
    (φ : ℂ ≃ₜ ℂ) {U : Set ℂ} (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U)
    {z : ℂ} (hz : z ∈ U) : ¬ ∀ᶠ w in 𝓝 z, deriv φ w = 0 := by
  intro hzero
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp ((show ∀ᶠ w in 𝓝 z, w ∈ U from hU.mem_nhds hz).and hzero)
  have hsub : ball z r ⊆ U := fun w hw => (hball (by simpa only [mem_ball] using hw)).1
  obtain ⟨c, hc⟩ := isOpen_ball.exists_is_const_of_deriv_eq_zero
    (convex_ball z r).isPreconnected (hφ.mono hsub)
    (fun w hw => (hball (by simpa only [mem_ball] using hw)).2)
  let w : ℂ := z + (r/2 : ℝ)
  have hw : w ∈ ball z r := by
    rw [mem_ball, dist_eq_norm]
    dsimp only [w]
    rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have heq : w = z := φ.injective ((hc w hw).trans (hc z (mem_ball_self hr)).symm)
  have hr0 : (r/2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  exact hr0 (Complex.ofReal_injective (add_left_cancel (show z + (r/2 : ℝ) = z+0 by
    simpa only [add_zero] using heq)))

 theorem holomorphicHomeomorph_inverse_differentiableAt
    (φ : ℂ ≃ₜ ℂ) {U : Set ℂ} (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U)
    {z : ℂ} (hz : z ∈ U) : DifferentiableAt ℂ φ.symm (φ z) := by
  have ha := hφ.analyticAt (hU.mem_nhds hz)
  have hn : ∀ᶠ w in 𝓝[≠] z, deriv φ w ≠ 0 :=
    ha.deriv.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (holomorphicHomeomorph_deriv_not_locally_zero φ hU hφ hz)
  have ht : Tendsto φ.symm (𝓝[≠] (φ z)) (𝓝[≠] z) := by
    change map φ.symm (𝓝[≠] (φ z)) ≤ 𝓝[≠] z
    rw [φ.symm.map_punctured_nhds_eq, φ.symm_apply_apply]
  apply (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    ?_ φ.symm.continuous.continuousAt).differentiableAt
  have hu : ∀ᶠ y in 𝓝 (φ z), φ.symm y ∈ U := by
    have ht₀ : Tendsto φ.symm (𝓝 (φ z)) (𝓝 z) := by
      simpa only [φ.symm_apply_apply] using φ.symm.continuous.tendsto (φ z)
    exact ht₀.eventually (hU.mem_nhds hz)
  filter_upwards [ht.eventually hn, hu.filter_mono nhdsWithin_le_nhds] with y hy hyU
  have hcont : ContDiffAt ℂ 1 φ (φ.symm y) :=
    (hφ.analyticAt (hU.mem_nhds hyU)).contDiffAt
  have hs := hcont.hasStrictDerivAt'
    ((hφ _ hyU).differentiableAt (hU.mem_nhds hyU)).hasDerivAt (by norm_num)
  have hi := hs.to_local_left_inverse hy (Eventually.of_forall φ.symm_apply_apply)
  simpa only [φ.apply_symm_apply] using hi.hasDerivAt.differentiableAt

 theorem holomorphicHomeomorph_deriv_ne_zero
    (φ : ℂ ≃ₜ ℂ) {U : Set ℂ} (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U)
    {z : ℂ} (hz : z ∈ U) : deriv φ z ≠ 0 := by
  have hf := ((hφ z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hi := (holomorphicHomeomorph_inverse_differentiableAt φ hU hφ hz).hasDerivAt
  have hh := (hi.comp z hf).deriv
  have hid : ((φ.symm : ℂ → ℂ) ∘ (φ : ℂ → ℂ)) = id := funext φ.symm_apply_apply
  have hidder : deriv (id : ℂ → ℂ) z = 1 := (hasDerivAt_id z).deriv
  rw [hid, hidder] at hh
  intro hzero
  rw [hzero, mul_zero] at hh
  exact one_ne_zero hh

 theorem holomorphicHomeomorph_conformal (φ : ℂ ≃ₜ ℂ) {U : Set ℂ}
    (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U)
    (hb : (fun z => φ z-z) =O[Bornology.cobounded ℂ] (fun z => z⁻¹)) :
    IsConformalOn φ.onePointCongr (((↑) : ℂ → Sphere) '' U ∪ {OnePoint.infty}) := by
  have he : (φ.onePointCongr : Sphere → Sphere) = extendAtInfinity φ := by
    funext p
    cases p using OnePoint.rec <;> rfl
  rw [he]
  exact isConformalOn_extendAtInfinity hU hφ
    (fun z hz => holomorphicHomeomorph_deriv_ne_zero φ hU hφ hz) hb

end CircleDomainRigidity

end

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

 theorem HasPrincipalCoefficient.norm_le_of_exterior
    {F : ℂ → ℂ} {b : ℂ} (hb : HasPrincipalCoefficient F b)
    (harea : ExteriorCoefficientAreaTheorem) {R : ℝ} (hR : 0 < R)
    (hd : DifferentiableOn ℂ F {z | R < ‖z‖}) (hinj : InjOn F {z | R < ‖z‖}) :
    ‖b‖ ≤ 2*R^2 := by
  apply le_of_tendsto hb.norm
  have he := harea.scaled_exterior_decay hR hd hinj hb.bigO
  filter_upwards [eventually_cobounded_le_norm (E := ℂ) (2*R)] with z hz
  have hn : 0 < ‖z‖ := lt_of_lt_of_le (by positivity) hz
  rw [norm_mul]
  calc
    ‖z‖ * ‖F z-z‖ ≤ ‖z‖ * (2*R^2/‖z‖) := mul_le_mul_of_nonneg_left (he z hz) (norm_nonneg _)
    _ = 2*R^2 := by field_simp

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
-- module Solutions.Q146_CD.CircleDomains_Uniformization_ScalarModelCoefficients
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common exterior radius bounds the actual coefficient of every model.
Consequently the retained model class has near-maximal real coefficients. -/
open Set Function Filter Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 namespace CompactScalarModel
 variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem coefficient_bound (M : CompactScalarModel G u)
    (harea : ExteriorCoefficientAreaTheorem) {R : ℝ} (hR : 0 < R)
    (hsource : ∀ z : ℂ, R < ‖z‖ → (z : Sphere) ∈ G) :
    ‖M.coefficient‖ ≤ 2*R^2 := by
  apply M.coefficient_limit.norm_le_of_exterior harea hR
  · intro z hz
    exact (finite_differentiable_of_sphere_conformal (M.conformal.1 _ (hsource z hz))).differentiableWithinAt
  · intro z hz w hw he
    apply OnePoint.coe_injective
    apply M.conformal.bijOn.injOn (hsource z hz) (hsource w hw)
    exact congrArg ((↑) : ℂ → Sphere) he

 theorem coefficientSet_bddAbove (harea : ExteriorCoefficientAreaTheorem)
    {R : ℝ} (hR : 0 < R) (hsource : ∀ z : ℂ, R < ‖z‖ → (z : Sphere) ∈ G) :
    BddAbove (coefficientSet G u) := by
  refine ⟨2*R^2, ?_⟩
  rintro _ ⟨M, rfl⟩
  exact (Complex.re_le_norm M.coefficient).trans (M.coefficient_bound harea hR hsource)

 theorem exists_near_maximal (hne : Nonempty (CompactScalarModel G u))
    {d : ℝ} (hd : 0 < d) :
    ∃ M : CompactScalarModel G u,
      sSup (coefficientSet G u)-d < M.coefficient.re := by
  have hS : (coefficientSet G u).Nonempty := by
    obtain ⟨M⟩ := hne
    exact ⟨M.coefficient.re, M, rfl⟩
  obtain ⟨b, ⟨M, rfl⟩, hb⟩ := exists_lt_of_lt_csSup hS
    (show sSup (coefficientSet G u)-d < sSup (coefficientSet G u) by linarith)
  exact ⟨M, hb⟩

 theorem increment_le_of_near_maximal (M N : CompactScalarModel G u)
    (hbound : BddAbove (coefficientSet G u)) {d : ℝ}
    (hnear : sSup (coefficientSet G u)-d ≤ M.coefficient.re)
    {c : ℂ} (hc : N.coefficient = M.coefficient+c) : c.re ≤ d := by
  have hN : N.coefficient.re ≤ sSup (coefficientSet G u) :=
    le_csSup hbound ⟨N, rfl⟩
  rw [hc, Complex.add_re] at hN
  linarith

 end CompactScalarModel

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ScalarModelConductivity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual conductivity postcomposition stays in the retained model
class. Near maximality therefore bounds its first coefficient and both
terms of its proved global energy identity. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem complement_compact (M : CompactScalarModel G u) (hinf : OnePoint.infty ∈ G) :
    IsCompact (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ := by
  have hi : OnePoint.infty ∈ extendAtInfinity M.function '' G := ⟨_, hinf, rfl⟩
  have hK := (isCompact_finite_preimage M.image_open.isClosed_compl (not_not.mpr hi)).image
    complexPlaneCoordinates.symm.continuous
  convert hK using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  constructor
  · intro hx
    exact ⟨complexPlaneCoordinates x, hx, complexPlaneCoordinates.symm_apply_apply x⟩
  · rintro ⟨z, hz, rfl⟩
    change planeSphere (complexPlaneCoordinates.symm z) ∉ extendAtInfinity M.function '' G
    simpa only [planeSphere, ContinuousLinearEquiv.apply_symm_apply, mem_preimage, mem_compl_iff] using hz

 theorem conductivity_conformal (M : CompactScalarModel G u)
    (φ : ℂ ≃ₜ ℂ) (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    (hb : (fun z => φ z-z) =O[cobounded ℂ] (fun z => z⁻¹))
    (n : ℕ)
    (hsys : ∀ᵐ x ∂volume,
      D.realGradient x 0 = conductivityValue (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ n x * D.imagGradient x 1 ∧
      D.realGradient x 1 = -conductivityValue (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ n x * D.imagGradient x 0) :
    IsConformalEquivalence φ.onePointCongr (extendAtInfinity M.function '' G)
      (φ.onePointCongr '' (extendAtInfinity M.function '' G)) := by
  let Ω := extendAtInfinity M.function '' G
  let F := (physicalPlaneDomain Ω)ᶜ
  have hF : IsClosed F := (isOpen_physicalPlaneDomain M.image_open).isClosed_compl
  have hh := D.conductivity_holomorphic_off φ.continuous hF n hsys
  have hC : IsConformalOn φ.onePointCongr
      (((↑) : ℂ → Sphere) '' (complexPlaneCoordinates '' F)ᶜ ∪ {OnePoint.infty}) :=
    holomorphicHomeomorph_conformal φ
      ((complexPlaneCoordinates.toHomeomorph.isClosedMap _ hF).isOpen_compl) hh hb
  apply isConformalEquivalence_of_injOn (hC.mono ?_) M.image_open φ.onePointCongr.injective.injOn
  intro p hp
  cases p using OnePoint.rec with
  | infty => exact Or.inr rfl
  | coe z =>
    apply Or.inl
    refine ⟨z, ?_, rfl⟩
    rintro ⟨x, hx, hxz⟩
    apply hx
    change (complexPlaneCoordinates x : Sphere) ∈ Ω
    simpa only [hxz] using hp

 theorem conductivity_coefficient_le (M : CompactScalarModel G u)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (hbound : BddAbove (coefficientSet G u)) {d : ℝ}
    (hnear : sSup (coefficientSet G u)-d ≤ M.coefficient.re)
    (φ : ℂ ≃ₜ ℂ) (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    (hscalar : CompactScalarPullback φ)
    (hFc : IsCompact (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ)
    (c : ℂ) (hc : HasPrincipalCoefficient φ c) (n : ℕ) (_hn : 1 ≤ n)
    (hsys : ∀ᵐ x ∂volume,
      D.realGradient x 0 = conductivityValue (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ n x * D.imagGradient x 1 ∧
      D.realGradient x 1 = -conductivityValue (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ n x * D.imagGradient x 0) :
    c.re ≤ d := by
  let N := M.postcomposeWithScalarTransport φ
    (fun i => hscalar _ (M.scalar_continuous hu hs i) (M.scalar_compact i)
      (M.witness i) _ hFc (M.gradient_zero i)) c hc
    (M.conductivity_conformal φ D hc.bigO n hsys)
  exact M.increment_le_of_near_maximal N hbound hnear rfl

 theorem near_extremal_conductivity_energy (M : CompactScalarModel G u)
    (hsolver : PrincipalConductivityScalarSolver) (_hprincipal : PrincipalRealBeltrami)
    (hgreen : UnorientedFiniteCircleGreenFormula)
    (hinf : OnePoint.infty ∈ G)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (hbound : BddAbove (coefficientSet G u)) {d : ℝ}
    (hnear : sSup (coefficientSet G u)-d ≤ M.coefficient.re)
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ (φ : ℂ ≃ₜ ℂ) (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x))) (c : ℂ),
      HasPrincipalCoefficient φ c ∧
      (∀ᵐ x ∂volume,
        D.realGradient x 0 = conductivityValue (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ n x * D.imagGradient x 1 ∧
        D.realGradient x 1 = -conductivityValue (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ n x * D.imagGradient x 0) ∧
      Integrable (fun x => (D.imagGradient x 0)^2+(D.imagGradient x 1-1)^2) ∧
      (∫ x, (D.imagGradient x 0)^2+(D.imagGradient x 1-1)^2) ≤ 2*Real.pi*d ∧
      (∫ x in (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
        (D.imagGradient x 0)^2+(D.imagGradient x 1)^2) ≤ 2*Real.pi*d/((n : ℝ)-1) := by
  obtain ⟨φ, D, c, T, hT, _ht, hexp, hsys, _hh, hI, hE, hscalar⟩ :=
    exists_principal_conductivity_energy_scalar hsolver hgreen (M.complement_compact hinf) n hn
  have hc := hasPrincipalCoefficient_of_expansion hT.continuousAt hexp
  have hcd := M.conductivity_coefficient_le hu hs hbound hnear φ D hscalar (M.complement_compact hinf) c hc n (by omega) hsys
  obtain ⟨hH, hF⟩ := D.conductivity_energy_bounds hn hcd hE
  exact ⟨φ, D, c, hc, hsys, hI, hH, hF⟩

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_LimitHeightBounds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quantitative local and exterior bounds survive in the actual
locally uniform height limit. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem limit_height_exterior_bound
    (harea : ExteriorCoefficientAreaTheorem)
    (φ : ℕ → ℂ ≃ₜ ℂ) {v : ℂ → ℝ}
    (hv : TendstoLocallyUniformly (fun n z => (φ n z).im) v atTop)
    {R : ℝ} (hR : 0 < R)
    (hh : ∀ n, DifferentiableOn ℂ (φ n) {z | R < ‖z‖})
    (hnorm : ∀ n, (fun z => φ n z-z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ∀ z : ℂ, 2*R ≤ ‖z‖ → |v z-z.im| ≤ 2*R^2/‖z‖ := by
  intro z hz
  have hp : Tendsto (fun n => (φ n z).im) atTop (𝓝 (v z)) :=
    hv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)
  apply le_of_tendsto ((hp.sub_const z.im).abs)
  apply Eventually.of_forall
  intro n
  calc
    |(φ n z).im-z.im| = |(φ n z-z).im| := by rw [Complex.sub_im]
    _ ≤ ‖φ n z-z‖ := Complex.abs_im_le_norm _
    _ ≤ _ := harea.scaled_exterior_decay hR (hh n) (φ n).injective.injOn (hnorm n) z hz

 theorem limit_height_local_bound
    (harea : ExteriorCoefficientAreaTheorem)
    (φ : ℕ → ℂ ≃ₜ ℂ) {v : ℂ → ℝ}
    (hv : TendstoLocallyUniformly (fun n z => (φ n z).im) v atTop)
    {R S : ℝ} (hR : 0 < R) (hS : 2*R ≤ S)
    (hh : ∀ n, DifferentiableOn ℂ (φ n) {z | R < ‖z‖})
    (hnorm : ∀ n, (fun z => φ n z-z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ∀ z ∈ closedBall (0 : ℂ) S, |v z| ≤ S+R := by
  intro z hz
  have hp : Tendsto (fun n => (φ n z).im) atTop (𝓝 (v z)) :=
    hv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)
  apply le_of_tendsto hp.abs
  exact Eventually.of_forall (fun n =>
    normalized_homeomorphic_height_bound harea hR hS (hh n) (hnorm n) z hz)

 theorem limit_height_log_bound
    (φ : ℕ → ℂ ≃ₜ ℂ)
    (D : ∀ n, PlaneLocalWeakComplex (fun p => φ n (complexPlaneCoordinates p)))
    {v : ℂ → ℝ} (hv : TendstoLocallyUniformly (fun n z => (φ n z).im) v atTop)
    {B : ℝ}
    (hI : ∀ n, Integrable (fun p => (D n).imagGradient p 0^2+((D n).imagGradient p 1-1)^2))
    (hB : ∀ n, (∫ p, (D n).imagGradient p 0^2+((D n).imagGradient p 1-1)^2) ≤ B)
    (c : ℂ) {r R T : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hT : ‖c‖+R < T)
    {x y : ℂ} (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    |v x-v y|^2*Real.log (R/r) ≤
      16*Real.pi*(2*B+2*(volume (ball (0 : EuclideanPlane) T)).toReal) := by
  have hp (z : ℂ) : Tendsto (fun n => (φ n z).im) atTop (𝓝 (v z)) :=
    hv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)
  apply le_of_tendsto ((((hp x).sub (hp y)).abs.pow 2).mul_const _)
  exact Eventually.of_forall (fun n =>
    height_log_bound_from_error (φ n) c (D n) hr hrR hT (hI n) (hB n) hx hy)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_LimitHeightEquicontinuity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform compactness for heights when the retained model varies but
the error-energy budgets remain bounded. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem heights_equicontinuous_of_log_bound {ι : Type*} (v : ι → ℂ → ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hlog : ∀ i c r, 0 < r → r ≤ 1 → ∀ z ∈ closedBall c r,
      |v i c-v i z|^2*Real.log (1/r) ≤
        16*Real.pi*(2*B+2*(volume (ball (0 : EuclideanPlane) (‖c‖+2))).toReal)) :
    Equicontinuous v := by
  intro c
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  let C := 16*Real.pi*(2*B+2*(volume (ball (0 : EuclideanPlane) (‖c‖+2))).toReal)
  have hC : 0 ≤ C := by dsimp only [C] <;> positivity
  let L := (C+1)/ε^2
  have hL : 0 < L := div_pos (by linarith) (sq_pos_of_pos hε)
  let δ := Real.exp (-L)
  have hδ : 0 < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hL.le)
  have hlg : Real.log (1/δ) = L := by
    dsimp only [δ]
    rw [one_div, Real.log_inv, Real.log_exp, neg_neg]
  have hEL : ε^2*L = C+1 := by dsimp only [L]; field_simp
  refine ⟨δ, hδ, ?_⟩
  intro z hz i
  have hh := hlog i c δ hδ hδ1 z (mem_closedBall.mpr hz.le)
  rw [hlg] at hh
  change |v i c-v i z|^2*L ≤ C at hh
  rw [Real.dist_eq]
  by_contra hn
  have hp := pow_le_pow_left₀ hε.le (le_of_not_gt hn) 2
  have hm := mul_le_mul_of_nonneg_right hp hL.le
  nlinarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_NearExtremalHeight
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Applying the constructed conductivity sequence to a nearly extremal
retained model. The continuous limit, weak gradient and complementary
zero-gradient statement are conclusions of the construction. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem exists_near_extremal_height_at_radius (M : CompactScalarModel G u)
    (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hinf : OnePoint.infty ∈ G)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (hbound : BddAbove (coefficientSet G u)) {d : ℝ} (hd : 0 < d)
    (hnear : sSup (coefficientSet G u)-d ≤ M.coefficient.re)
    {R : ℝ} (hR : 0 < R)
    (hFR : complexPlaneCoordinates ''
      (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ ⊆ ball 0 R) :
    ∃ (v : C(ℂ, ℝ)) (G₀ G₁ : Lp ℝ 2 (volume : Measure EuclideanPlane))
      (φ : ℕ → ℂ ≃ₜ ℂ),
      TendstoLocallyUniformly (fun n z => (φ n z).im) v atTop ∧
      DeGiorgi.HasWeakGrad (heightLimitGradient G₀ G₁) (v ∘ complexPlaneCoordinates) univ ∧
      (∫ p, G₀ p^2+G₁ p^2) ≤ 2*Real.pi*d ∧
      (∀ᵐ p ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
        heightLimitGradient G₀ G₁ p = 0) ∧
      (∀ n, DifferentiableOn ℂ (φ n) {z | R < ‖z‖}) ∧
      (∀ n, (fun z => φ n z-z) =O[cobounded ℂ] (fun z => z⁻¹)) ∧
      (∀ c r, 0 < r → r ≤ 1 → ∀ z ∈ closedBall c r,
        |v c-v z|^2*Real.log (1/r) ≤
          16*Real.pi*(2*(2*Real.pi*d)+2*(volume (ball (0 : EuclideanPlane) (‖c‖+2))).toReal)) := by
  let F := (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ
  have hF : IsCompact F := M.complement_compact hinf
  have H (n : ℕ) := M.near_extremal_conductivity_energy hsolver hprincipal hgreen hinf
    hu hs hbound hnear (n+2) (by omega)
  choose φ D c hc hsys hI hE hFE using H
  have hh (n : ℕ) : DifferentiableOn ℂ (φ n) {z | R < ‖z‖} := by
    apply ((D n).conductivity_holomorphic_off (φ n).continuous hF.isClosed (n+2) (hsys n)).mono
    intro z hz hzF
    have hSz : ‖z‖ < R := by simpa only [mem_ball, dist_zero_right] using hFR hzF
    exact (not_lt_of_ge hz.le) hSz
  have hsmall : Tendsto (fun n => ∫ p in F,
      (D n).imagGradient p 0^2+(D n).imagGradient p 1^2) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => 2*Real.pi*d/((n : ℝ)+1)) atTop (𝓝 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2*Real.pi*d)
      simpa only [mul_one_div, mul_zero] using h
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    · intro n
      exact integral_nonneg (fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
    · intro n
      have he : (((n+2 : ℕ) : ℝ)-1) = (n : ℝ)+1 := by push_cast <;> ring
      simpa only [he] using hFE n
  obtain ⟨v, G₀, G₁, s, _hs, hv, hw, he, hz⟩ := exists_conductivity_height_limit harea φ D
    (by positivity : 0 ≤ 2*Real.pi*d) hR hI hE hh (fun n => (hc n).bigO) hF hsmall
  refine ⟨v, G₀, G₁, φ ∘ s, hv, hw, he, hz, fun n => hh (s n),
    fun n => (hc (s n)).bigO, ?_⟩
  intro c r hr hr1 z hz
  exact limit_height_log_bound (φ ∘ s) (fun n => D (s n)) hv
    (fun n => hI (s n)) (fun n => hE (s n)) c hr hr1
    (T := ‖c‖+2) (by linarith) (mem_closedBall_self hr.le) hz

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalZeroGradientConstant
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous planar Sobolev function with zero weak gradient on a
connected open set is constant there and on its closure. The proved local
complex Weyl lemma reduces this to the holomorphic open mapping theorem. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem constant_on_closure_of_zero_weak_gradient
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (G : EuclideanPlane → EuclideanPlane)
    (hw : DeGiorgi.HasWeakGrad G u univ)
    (hLp : ∀ R i, MemLp (fun p => G p i) 2 (volume.restrict (Metric.ball 0 R)))
    {U : Set EuclideanPlane} (hU : IsOpen U) (hconn : IsConnected U)
    (hz : ∀ᵐ p ∂volume.restrict U, G p = 0) :
    ∃ c : ℝ, ∀ p ∈ closure U, u p = c := by
  let f : EuclideanPlane → ℂ := fun p => (u p : ℂ)
  let D : PlaneLocalWeakComplex f := {
    realGradient := G
    imagGradient := fun _ => 0
    real_weak := by simpa only [f, Complex.ofReal_re] using hw
    imag_weak := by
      intro i ψ hψ hs hsub
      simp [f]
    real_memLp := hLp
    imag_memLp := fun _ _ => MemLp.zero }
  have hz' : ∀ᵐ p ∂volume, p ∈ U → G p = 0 := by
    exact (ae_restrict_iff' hU.measurableSet).mp hz
  have hcr : ∀ᵐ p ∂volume, p ∈ U →
      D.realGradient p 0 = D.imagGradient p 1 ∧
      D.realGradient p 1 = -D.imagGradient p 0 := by
    filter_upwards [hz'] with p hp hpU
    simp [D, hp hpU]
  have hd := D.holomorphic_on_of_cauchyRiemann (Complex.continuous_ofReal.comp hu) hU hcr
  let V := complexPlaneCoordinates '' U
  have hV : IsOpen V := complexPlaneCoordinates.toHomeomorph.isOpenMap _ hU
  have hcV : IsConnected V := hconn.image _ complexPlaneCoordinates.continuous.continuousOn
  have ha : AnalyticOnNhd ℂ (fun z => f (complexPlaneCoordinates.symm z)) V :=
    fun z hz => hd.analyticAt (hV.mem_nhds hz)
  obtain ⟨c, hc⟩ := ha.eq_const_of_im_eq_const (c₀ := 0) (fun _ _ => rfl) hV hcV
  have hcu : U ⊆ {p | u p = c.re} := by
    intro p hp
    have hh := congrArg Complex.re (hc (complexPlaneCoordinates p) ⟨p, hp, rfl⟩)
    change u p = c.re
    simpa only [f, ContinuousLinearEquiv.symm_apply_apply, Complex.ofReal_re] using hh
  exact ⟨c.re, fun p hp => (closure_minimal hcu (isClosed_eq hu continuous_const)) hp⟩

 theorem constant_on_homeomorphic_disk
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (G : EuclideanPlane → EuclideanPlane)
    (hw : DeGiorgi.HasWeakGrad G u univ)
    (hLp : ∀ R i, MemLp (fun p => G p i) 2 (volume.restrict (Metric.ball 0 R)))
    (e : ℂ ≃ₜ EuclideanPlane) (c : ℂ) {r : ℝ} (hr : 0 < r)
    (hz : ∀ᵐ p ∂volume.restrict (e '' Metric.closedBall c r), G p = 0) :
    ∃ a : ℝ, ∀ p ∈ e '' Metric.closedBall c r, u p = a := by
  have hU : IsOpen (e '' Metric.ball c r) := e.isOpenMap _ Metric.isOpen_ball
  have hc : IsConnected (Metric.ball c r) :=
    ⟨⟨c, Metric.mem_ball_self hr⟩, (convex_ball c r).isPreconnected⟩
  have hUc : IsConnected (e '' Metric.ball c r) := hc.image _ e.continuous.continuousOn
  have hzU : ∀ᵐ p ∂volume.restrict (e '' Metric.ball c r), G p = 0 :=
    hz.filter_mono (ae_mono (Measure.restrict_mono (image_mono Metric.ball_subset_closedBall) le_rfl))
  obtain ⟨a, ha⟩ := constant_on_closure_of_zero_weak_gradient hu G hw hLp hU hUc hzU
  rw [← e.image_closure, closure_ball c hr.ne'] at ha
  exact ⟨a, ha⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_VerticalWeakConstant
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalization of a zero-error height: its only possible freedom
is an additive constant, which exterior decay then removes. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem vertical_translation_of_weak_gradient
    {v : EuclideanPlane → ℝ} (hv : Continuous v)
    (hw : DeGiorgi.HasWeakGrad (heightLimitGradient 0 0) v univ) :
    ∃ c : ℝ, ∀ p, v p = p 1+c := by
  have hY (i : Fin 2) : DeGiorgi.HasWeakPartialDeriv i
      (fun _ : EuclideanPlane => if i = 0 then 0 else 1) (fun p => p 1) univ := by
    have h := weakPartial_of_smooth_on isOpen_univ
      verticalLinear.contDiff.contDiffOn i
    convert h using 1
    · funext p
      fin_cases i <;> simp [ContinuousLinearMap.fderiv, verticalLinear_apply]
    · rfl
  have hw' (i : Fin 2) : DeGiorgi.HasWeakPartialDeriv i
      (fun _ : EuclideanPlane => if i = 0 then 0 else 1) v univ := by
    apply (hw i).congr_ae (Filter.EventuallyEq.rfl) ?_
    simp only [Measure.restrict_univ]
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume : Measure EuclideanPlane)] with p hp
    simp [heightLimitGradient]
  have hz : DeGiorgi.HasWeakGrad (fun _ => 0) (fun p => v p-p 1) univ := by
    intro i ψ hψ hs hsub
    have h0 := hw' i ψ hψ hs hsub
    have h1 := hY i ψ hψ hs hsub
    simp only [Measure.restrict_univ] at h0 h1 ⊢
    let t : EuclideanPlane → ℝ := fun p => fderiv ℝ ψ p (EuclideanSpace.single i 1)
    have ht : Continuous t := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hts : HasCompactSupport t := hs.fderiv_apply (𝕜 := ℝ) _
    have hvi : Integrable (fun p => v p*t p) volume := (hv.mul ht).integrable_of_hasCompactSupport hts.mul_left
    have hyi : Integrable (fun p => verticalLinear p*t p) volume := (verticalLinear.continuous.mul ht).integrable_of_hasCompactSupport hts.mul_left
    simp only [PiLp.zero_apply, zero_mul, integral_zero, neg_zero]
    simp_rw [sub_mul]
    change (∫ p, v p*t p-verticalLinear p*t p) = 0
    rw [integral_sub hvi hyi]
    change (∫ p, v p*t p)-(∫ p, p 1*t p) = 0
    exact sub_eq_zero.mpr (h0.trans h1.symm)
  obtain ⟨c, hc⟩ := constant_on_closure_of_zero_weak_gradient
    (hv.sub verticalLinear.continuous) (fun _ => 0) hz (fun _ _ => MemLp.zero)
    isOpen_univ isConnected_univ (Eventually.of_forall (fun _ => rfl))
  refine ⟨c, fun p => ?_⟩
  have h := hc p (by simp)
  change v p-p 1=c at h
  linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_HeightNormalization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior decay removes the additive constant in a zero-error height. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem normalized_vertical_weak_gradient
    {v : ℂ → ℝ} (hv : Continuous v)
    (hw : DeGiorgi.HasWeakGrad (heightLimitGradient 0 0) (v ∘ complexPlaneCoordinates) univ)
    {R A : ℝ} (hdecay : ∀ z : ℂ, R ≤ ‖z‖ → |v z-z.im| ≤ A/‖z‖) :
    v = Complex.im := by
  obtain ⟨c, hc⟩ := vertical_translation_of_weak_gradient
    (hv.comp complexPlaneCoordinates.continuous) hw
  have hcz (z : ℂ) : v z = z.im+c := by
    have h := hc (complexPlaneCoordinates.symm z)
    have hy : (complexPlaneCoordinates.symm z) 1 = z.im :=
      congrArg Complex.im (complexPlaneCoordinates.apply_symm_apply z)
    simpa only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply, hy] using h
  have hc0 : c = 0 := by
    by_contra hn
    have hcp : 0 < |c| := abs_pos.mpr hn
    let T := max R ((|A|+1)/|c|)
    have hT : 0 < T := lt_of_lt_of_le (div_pos (by positivity) hcp) (le_max_right _ _)
    have hnorm : ‖(⟨T, 0⟩ : ℂ)‖ = T := by
      change ‖(T : ℂ)‖ = T
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
    have h := hdecay (⟨T, 0⟩ : ℂ) (by rw [hnorm]; exact le_max_left _ _)
    rw [hcz, add_sub_cancel_left, hnorm] at h
    have hm : |c| * T ≤ A := (le_div_iff₀ hT).mp h
    have ht : |A|+1 ≤ |c| * T := by
      have ht := mul_le_mul_of_nonneg_left (le_max_right R ((|A|+1)/|c|)) hcp.le
      rwa [mul_div_cancel₀ _ hcp.ne'] at ht
    linarith [le_abs_self A]
  funext z
  simpa only [hc0, add_zero] using hcz z

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_VanishingL2Pairings
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vanishing quadratic energy forces every fixed L² pairing to vanish. -/
open Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem tendsto_L2_pairing_zero_of_energy
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {g : ℕ → X → ℝ} (hg : ∀ n, MemLp (g n) 2 μ)
    {b : ℕ → ℝ} (hb : Tendsto b atTop (𝓝 0))
    (he : ∀ n, (∫ x, g n x^2 ∂μ) ≤ b n)
    {w : X → ℝ} (hw : MemLp w 2 μ) :
    Tendsto (fun n => ∫ x, g n x*w x ∂μ) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n => (eLpNorm (g n) 2 μ).toReal^2) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    · exact fun n => sq_nonneg _
    · intro n
      change (eLpNorm (g n) 2 μ).toReal^2 ≤ b n
      rw [← integral_sq_eq_eLpNorm_toReal_sq (hg n)]
      exact he n
  have hn : Tendsto (fun n => (eLpNorm (g n) 2 μ).toReal) atTop (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      Real.sqrt_zero] using h
  apply squeeze_zero_norm' _ (by simpa using hn.mul_const (eLpNorm w 2 μ).toReal)
  exact Eventually.of_forall (fun n => by
    simpa only [Real.norm_eq_abs] using abs_integral_mul_le_eLpNorm_two (hg n) hw)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_HeightZeroEnergyLimit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A locally uniform limit of the constructed heights with vanishing
error energy has exactly the vertical weak derivative. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem height_zero_energy_limit
    (v : ℕ → C(ℂ, ℝ)) (G₀ G₁ : ℕ → Lp ℝ 2 (volume : Measure EuclideanPlane))
    (hw : ∀ n, DeGiorgi.HasWeakGrad (heightLimitGradient (G₀ n) (G₁ n))
      (v n ∘ complexPlaneCoordinates) univ)
    {V : ℂ → ℝ} (hv : TendstoLocallyUniformly (fun n z => v n z) V atTop)
    (hb : ∀ K : Set ℂ, IsCompact K → ∃ C : ℝ, ∀ n z, z ∈ K → |v n z| ≤ C)
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hE : ∀ n, (∫ p, G₀ n p^2+G₁ n p^2) ≤ e n) :
    DeGiorgi.HasWeakGrad (heightLimitGradient 0 0) (V ∘ complexPlaneCoordinates) univ := by
  let f : ℕ → EuclideanPlane → ℂ := fun n p => ⟨0, v n (complexPlaneCoordinates p)⟩
  let D (n : ℕ) : PlaneLocalWeakComplex (f n) := {
    realGradient := fun _ => 0
    imagGradient := heightLimitGradient (G₀ n) (G₁ n)
    real_weak := by intro i ψ hψ hs hsub; simp [f]
    imag_weak := hw n
    real_memLp := fun _ _ => MemLp.zero
    imag_memLp := fun R => (heightLimitWitness (G₀ n) (G₁ n)
      ((v n).continuous.comp complexPlaneCoordinates.continuous) (hw n) R).weakGrad_component_memLp }
  have hI (n : ℕ) : Integrable
      (fun p => (D n).imagGradient p 0^2+((D n).imagGradient p 1-1)^2) := by
    have heq : (fun p => (D n).imagGradient p 0^2+((D n).imagGradient p 1-1)^2) =
        (fun p => G₀ n p^2+G₁ n p^2) := by
      funext p
      simp [D, heightLimitGradient]
    rw [heq]
    exact (Lp.memLp (G₀ n)).integrable_sq.add (Lp.memLp (G₁ n)).integrable_sq
  have h0 (n : ℕ) : (∫ p, G₀ n p^2) ≤ e n := by
    have h := hE n
    rw [integral_add (Lp.memLp (G₀ n)).integrable_sq (Lp.memLp (G₁ n)).integrable_sq] at h
    have hp : 0 ≤ (∫ p, G₁ n p^2) := integral_nonneg (fun p => sq_nonneg (G₁ n p))
    linarith
  have h1 (n : ℕ) : (∫ p, G₁ n p^2) ≤ e n := by
    have h := hE n
    rw [integral_add (Lp.memLp (G₀ n)).integrable_sq (Lp.memLp (G₁ n)).integrable_sq] at h
    have hp : 0 ≤ (∫ p, G₀ n p^2) := integral_nonneg (fun p => sq_nonneg (G₀ n p))
    linarith
  have hz (w : Lp ℝ 2 (volume : Measure EuclideanPlane)) :
      (∫ p, (0 : Lp ℝ 2 (volume : Measure EuclideanPlane)) p*w p) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume : Measure EuclideanPlane)] with p hp
    simp
  apply weak_height_identification f D
    (fun n => Complex.equivRealProdCLM.symm.continuous.comp
      (continuous_const.prodMk ((v n).continuous.comp complexPlaneCoordinates.continuous)))
  · intro p
    exact hv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ _)
  · intro K hK
    obtain ⟨C, hC⟩ := hb (complexPlaneCoordinates '' K) (hK.image complexPlaneCoordinates.continuous)
    exact ⟨C, fun n p hp => by simpa only [f, Real.norm_eq_abs] using hC n _ ⟨p, hp, rfl⟩⟩
  · exact hI
  · intro w
    simpa [D, heightLimitGradient, hz] using
      tendsto_L2_pairing_zero_of_energy (fun n => Lp.memLp (G₀ n)) he h0 (Lp.memLp w)
  · intro w
    simpa [D, heightLimitGradient, hz] using
      tendsto_L2_pairing_zero_of_energy (fun n => Lp.memLp (G₁ n)) he h1 (Lp.memLp w)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_HeightVanishingConvergence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactness and uniqueness turn the energy tending to zero into
locally uniform convergence to the vertical coordinate. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem heights_tendsto_vertical_of_energy
    (v : ℕ → C(ℂ, ℝ)) (G₀ G₁ : ℕ → Lp ℝ 2 (volume : Measure EuclideanPlane))
    (hw : ∀ n, DeGiorgi.HasWeakGrad (heightLimitGradient (G₀ n) (G₁ n))
      (v n ∘ complexPlaneCoordinates) univ)
    (heq : Equicontinuous (fun n z => v n z))
    (hb : ∀ K : Set ℂ, IsCompact K → ∃ C : ℝ, ∀ n z, z ∈ K → |v n z| ≤ C)
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hE : ∀ n, (∫ p, G₀ n p^2+G₁ n p^2) ≤ e n)
    {R A : ℝ} (hd : ∀ n z, R ≤ ‖z‖ → |v n z-z.im| ≤ A/‖z‖) :
    TendstoLocallyUniformly (fun n z => v n z) Complex.im atTop := by
  let Y : C(ℂ, ℝ) := ⟨Complex.im, Complex.continuous_im⟩
  have ht : Tendsto v atTop (𝓝 Y) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨V, s, hs, hv⟩ := locally_uniform_height_subsequence (v ∘ ns) (heq.comp ns)
      (fun z => by
        obtain ⟨C, hC⟩ := hb {z} isCompact_singleton
        exact ⟨C, fun n => hC (ns n) z (mem_singleton z)⟩)
    have hwV := height_zero_energy_limit (fun n => v (ns (s n)))
      (fun n => G₀ (ns (s n))) (fun n => G₁ (ns (s n)))
      (fun n => hw (ns (s n))) hv
      (fun K hK => by
        obtain ⟨C, hC⟩ := hb K hK
        exact ⟨C, fun n => hC (ns (s n))⟩)
      (he.comp (hns.comp hs.tendsto_atTop)) (fun n => hE (ns (s n)))
    have hdV : ∀ z : ℂ, R ≤ ‖z‖ → |V z-z.im| ≤ A/‖z‖ := by
      intro z hz
      apply le_of_tendsto ((hv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)).sub_const z.im).abs
      exact Eventually.of_forall (fun n => hd (ns (s n)) z hz)
    have hV : V = Y := ContinuousMap.ext (congrFun
      (normalized_vertical_weak_gradient V.continuous hwV hdV))
    refine ⟨s, ?_⟩
    rw [hV] at hv
    exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr hv
  exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp ht

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_UniformHeightCloseness
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common error threshold for all heights in an equicontinuous,
normalized family. The threshold may depend on the compact test set. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem uniform_height_closeness {ι : Type*}
    (v : ι → C(ℂ, ℝ)) (G₀ G₁ : ι → Lp ℝ 2 (volume : Measure EuclideanPlane))
    (hw : ∀ i, DeGiorgi.HasWeakGrad (heightLimitGradient (G₀ i) (G₁ i))
      (v i ∘ complexPlaneCoordinates) univ)
    (heq : Equicontinuous (fun i z => v i z))
    (hb : ∀ K : Set ℂ, IsCompact K → ∃ C : ℝ, ∀ i z, z ∈ K → |v i z| ≤ C)
    (e : ι → ℝ) (hE : ∀ i, (∫ p, G₀ i p^2+G₁ i p^2) ≤ e i)
    {R A : ℝ} (hd : ∀ i z, R ≤ ‖z‖ → |v i z-z.im| ≤ A/‖z‖)
    {K : Set ℂ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ i, e i < δ → ∀ z ∈ K, |v i z-z.im| < ε := by
  by_contra hn
  push Not at hn
  have hbad (n : ℕ) : ∃ i, e i < 1/((n : ℝ)+1) ∧
      ∃ z ∈ K, ε ≤ |v i z-z.im| := hn _ (by positivity)
  choose ix hix z hz hbadz using hbad
  have hn0 (i : ι) : 0 ≤ e i :=
    (integral_nonneg (fun p => add_nonneg (sq_nonneg (G₀ i p)) (sq_nonneg (G₁ i p)))).trans (hE i)
  have he : Tendsto (fun n => e (ix n)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      (fun n => hn0 (ix n)) (fun n => (hix n).le)
  have hlim := heights_tendsto_vertical_of_energy (v ∘ ix) (G₀ ∘ ix) (G₁ ∘ ix)
    (fun n => hw (ix n)) (heq.comp ix)
    (fun L hL => by
      obtain ⟨C, hC⟩ := hb L hL
      exact ⟨C, fun n => hC (ix n)⟩)
    he (fun n => hE (ix n)) (fun n => hd (ix n))
  have hU := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    (hlim.tendstoLocallyUniformlyOn.mono (subset_univ K))
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.mp hU ε hε).exists
  have hclose : |v (ix n) (z n)-(z n).im| < ε := by
    simpa only [Function.comp_apply, Real.dist_eq, abs_sub_comm] using hn (z n) (hz n)
  exact (not_lt_of_ge (hbadz n)) hclose

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ControlledHeight
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative data proved for the actual nearly extremal height. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem exists_controlled_height (M : CompactScalarModel G u)
    (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hinf : OnePoint.infty ∈ G)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (hbound : BddAbove (coefficientSet G u)) {d : ℝ} (hd : 0 < d)
    (hnear : sSup (coefficientSet G u)-d ≤ M.coefficient.re)
    {R : ℝ} (hR : 0 < R)
    (hFR : complexPlaneCoordinates ''
      (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ ⊆ ball 0 R) :
    ∃ H : ControlledHeight R d,
      ∀ᵐ p ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
        heightLimitGradient H.error₀ H.error₁ p = 0 := by
  obtain ⟨v, G₀, G₁, φ, hv, hw, hE, hz, hh, hn, hl⟩ :=
    M.exists_near_extremal_height_at_radius hsolver hprincipal hgreen harea hinf hu hs hbound hd hnear hR hFR
  exact ⟨{
    height := v
    error₀ := G₀
    error₁ := G₁
    weak_gradient := hw
    error_bound := hE
    log_bound := hl
    local_bound := fun _ hS => limit_height_local_bound harea φ hv hR hS hh hn
    exterior_bound := limit_height_exterior_bound harea φ hv hR hh hn
    approximants := φ
    height_limit := hv }, hz⟩

end CompactScalarModel

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevCoareaFiniteLevels
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coarea integral is finite on each bounded measurable set. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem local_gradient_integrableOn_bounded
    {V : EuclideanPlane → EuclideanPlane}
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {E : Set EuclideanPlane} (hb : IsBounded E) : IntegrableOn (fun p => ‖V p‖) E := by
  obtain ⟨R, hR⟩ := hb.subset_ball 0
  have hV : MemLp V 2 (volume.restrict E) :=
    (memLp_piLp_iff.mpr (hLp R)).mono_measure (Measure.restrict_mono hR le_rfl)
  let : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  exact hV.norm.integrable (by norm_num)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevNullLevels
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coarea forces the actual weak gradient to vanish on the preimage
of any null set of scalar values. In particular, every fixed level has
zero gradient almost everywhere; no regularity of the level is assumed. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem sobolev_gradient_zero_on_null_values
    (hcoarea : PlanarSobolevCoarea)
    {v : EuclideanPlane → ℝ} (hv : Continuous v)
    {V : EuclideanPlane → EuclideanPlane} (hw : DeGiorgi.HasWeakGrad V v univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {E : Set EuclideanPlane} (hE : MeasurableSet E) (hb : IsBounded E)
    {N : Set ℝ} (hN : MeasurableSet N) (hNzero : volume N = 0) :
    ∀ᵐ p ∂volume.restrict (E ∩ v ⁻¹' N), V p = 0 := by
  let A := E ∩ v ⁻¹' N
  have hA : MeasurableSet A := hE.inter (hv.measurable hN)
  have hAb : IsBounded A := hb.subset inter_subset_left
  obtain ⟨hm, he⟩ := hcoarea v hv V hw hLp A hA hAb (fun _ => 1) measurable_const
  have hz : (∫⁻ t, sobolevLevelIntegral A v (fun _ => 1) t) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    have havoid : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ N := by
      simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hNzero
    filter_upwards [havoid] with t ht
    have htn : t ∉ N := ht
    have hempty : A ∩ {p | v p = t} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact htn (hp.2 ▸ hp.1.2)
    simp only [sobolevLevelIntegral, hempty, Measure.restrict_empty, lintegral_zero_measure, Pi.zero_apply]
  simp only [one_mul] at he
  have hnorm : AEMeasurable (fun p => ENNReal.ofReal ‖V p‖) (volume.restrict A) :=
    (local_gradient_integrableOn_bounded hLp hAb).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have ha := (lintegral_eq_zero_iff' hnorm).mp (he.symm.trans hz)
  filter_upwards [ha] with p hp
  exact norm_eq_zero.mp (le_antisymm (ENNReal.ofReal_eq_zero.mp hp) (norm_nonneg _))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalSobolevNullLevels
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero-gradient conclusion on scalar null values is local on any
open source domain. Compact cutoffs reduce it to planar
coarea; an exhaustion covers the entire domain. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem local_sobolev_gradient_zero_on_null_values_compact
    (hcoarea : PlanarSobolevCoarea)
    {U K : Set EuclideanPlane} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (W : DeGiorgi.MemW1pWitness 2 u U)
    {N : Set ℝ} (hN : MeasurableSet N) (hNz : volume N = 0) :
    ∀ᵐ p ∂volume.restrict (K ∩ u ⁻¹' N), W.weakGrad p = 0 := by
  obtain ⟨η, V, hη, hsη, _, hsub, hV, hKV, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hK hU hKU
  have hVU : V ⊆ U := by
    intro p hp
    apply hsub
    apply subset_tsupport η
    change η p ≠ 0
    rw [hone p hp]
    exact one_ne_zero
  let w := fun p => η p*u p
  obtain ⟨Ww⟩ := exists_global_compact_cutoff_witness hU W.memW1p hη hsη hsub
  have hwK : EqOn w u K := fun p hp => by dsimp only [w]; rw [hone p (hKV hp), one_mul]
  have hsame : K ∩ w ⁻¹' N = K ∩ u ⁻¹' N := by
    ext p
    constructor <;> intro hp
    · exact ⟨hp.1, by change u p ∈ N; rw [← hwK hp.1]; exact hp.2⟩
    · exact ⟨hp.1, by change w p ∈ N; rw [hwK hp.1]; exact hp.2⟩
  have hWL (i : Fin 2) : MemLp (fun p => Ww.weakGrad p i) 2 volume := by
    simpa only [Measure.restrict_univ] using Ww.weakGrad_component_memLp i
  have hz := sobolev_gradient_zero_on_null_values hcoarea (hη.continuous.mul hu) Ww.isWeakGrad
    (fun R i => (hWL i).restrict (Metric.ball 0 R)) hK.measurableSet hK.isBounded hN hNz
  change ∀ᵐ p ∂volume.restrict (K ∩ w ⁻¹' N), Ww.weakGrad p = 0 at hz
  rw [hsame] at hz
  have hg (i : Fin 2) : (fun p => Ww.weakGrad p i) =ᵐ[volume.restrict (K ∩ u ⁻¹' N)]
      fun p => W.weakGrad p i :=
    (weakGrad_eq_on_cutoff_plateau hV hVU W Ww hone i).filter_mono
      (ae_mono (Measure.restrict_mono (inter_subset_left.trans hKV) le_rfl))
  filter_upwards [hz, hg 0, hg 1] with p hp hp0 hp1
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  funext i
  fin_cases i
  · simpa [hp] using hp0.symm
  · simpa [hp] using hp1.symm

 theorem local_sobolev_gradient_zero_on_null_values
    (hcoarea : PlanarSobolevCoarea)
    {U : Set EuclideanPlane} (hU : IsOpen U)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (W : DeGiorgi.MemW1pWitness 2 u U)
    {N : Set ℝ} (hN : MeasurableSet N) (hNz : volume N = 0) :
    ∀ᵐ p ∂volume.restrict (U ∩ u ⁻¹' N), W.weakGrad p = 0 := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let K := CompactExhaustion.choice U
  let L : ℕ → Set EuclideanPlane := fun n => Subtype.val '' K n
  have hL (n : ℕ) : IsCompact (L n) := (K.isCompact n).image continuous_subtype_val
  have hLU (n : ℕ) : L n ⊆ U := by rintro p ⟨q, _, rfl⟩; exact q.property
  have hn (n : ℕ) : ∀ᵐ p ∂volume, p ∈ L n ∩ u ⁻¹' N → W.weakGrad p = 0 :=
    (ae_restrict_iff' ((hL n).measurableSet.inter (hu.measurable hN))).mp
      (local_sobolev_gradient_zero_on_null_values_compact hcoarea hU (hL n) (hLU n) hu W hN hNz)
  rw [ae_restrict_iff' (hU.measurableSet.inter (hu.measurable hN))]
  filter_upwards [ae_all_iff.mpr hn] with p hp hpU
  obtain ⟨n, hn⟩ := K.exists_mem (⟨p, hpU.1⟩ : U)
  exact hp n ⟨⟨⟨p, hpU.1⟩, hn, rfl⟩, hpU.2⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScalarEnergyMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pushforward of scalar Dirichlet energy has no atoms. This is
applied on the whole support of an old test, or on the fixed bounded
region used for the height. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem scalarEnergyMeasure_finite
    {E : Set EuclideanPlane} {v : EuclideanPlane → ℝ} {V : EuclideanPlane → EuclideanPlane}
    (hV : MemLp V 2 (volume.restrict E)) : IsFiniteMeasure (scalarEnergyMeasure E v V) := by
  have hi := hV.norm.integrable_sq
  have hfin : (∫⁻ p in E, ENNReal.ofReal (‖V p‖^2)) < ∞ := by
    simpa only [hasFiniteIntegral_iff_enorm, Real.enorm_eq_ofReal_abs,
      abs_sq] using hi.hasFiniteIntegral
  let := isFiniteMeasure_withDensity hfin.ne
  exact Measure.isFiniteMeasure_map _ _

 theorem exists_small_open_energy_cover
    (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    {C : Set ℝ} (hC : C.Countable) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ O : Set ℝ, C ⊆ O ∧ IsOpen O ∧ volume O < ε ∧ μ O < ε := by
  obtain ⟨U, hCU, hU, hμU⟩ :=
    C.exists_isOpen_lt_of_lt (μ := μ) ε (by rw [hC.measure_zero μ]; exact hε)
  obtain ⟨V, hCV, hV, hvolV⟩ :=
    C.exists_isOpen_lt_of_lt (μ := volume) ε (by rw [hC.measure_zero volume]; exact hε)
  exact ⟨U ∩ V, subset_inter hCU hCV, hU.inter hV,
    (measure_mono inter_subset_right).trans_lt hvolV,
    (measure_mono inter_subset_left).trans_lt hμU⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalScalarEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small open neighborhoods of countably many values for the actual
finite-energy scalar on an arbitrary open source domain. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem local_scalar_energy_nullSingleton
    (hcoarea : PlanarSobolevCoarea)
    {U : Set EuclideanPlane} (hU : IsOpen U)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (W : DeGiorgi.MemW1pWitness 2 u U) :
    NullSingletonClass (scalarEnergyMeasure U u W.weakGrad) := by
  constructor
  intro t
  rw [scalarEnergyMeasure, Measure.map_apply hu.measurable (measurableSet_singleton t),
    withDensity_apply _ (hu.measurable (measurableSet_singleton t)),
    Measure.restrict_restrict (hu.measurable (measurableSet_singleton t))]
  apply lintegral_eq_zero_of_ae_eq_zero
  have hz := local_sobolev_gradient_zero_on_null_values hcoarea hU hu W
    (measurableSet_singleton t) (measure_singleton t)
  rw [inter_comm] at hz
  filter_upwards [hz] with p hp
  simp only [hp, norm_zero, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero, Pi.zero_apply]

 theorem exists_small_open_local_energy_cover
    (hcoarea : PlanarSobolevCoarea)
    {U : Set EuclideanPlane} (hU : IsOpen U)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (W : DeGiorgi.MemW1pWitness 2 u U)
    {C : Set ℝ} (hC : C.Countable) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ O : Set ℝ, C ⊆ O ∧ IsOpen O ∧ volume O < ε ∧
      scalarEnergyMeasure U u W.weakGrad O < ε := by
  let μ := scalarEnergyMeasure U u W.weakGrad
  let : IsFiniteMeasure μ := scalarEnergyMeasure_finite (memLp_piLp_iff.mpr W.weakGrad_component_memLp)
  let : NullSingletonClass μ := local_scalar_energy_nullSingleton hcoarea hU hu W
  exact exists_small_open_energy_cover μ hC hε

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScalarFlattening
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual scalar map flattening an open set of prescribed values.
It is one-Lipschitz, stays uniformly close to the identity, and is locally
constant on the open set, even when that open set is dense. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal Interval
noncomputable section
namespace CircleDomainRigidity

 theorem flattenValues_locally_constant {O : Set ℝ} (hO : IsOpen O) {x : ℝ} (hx : x ∈ O) :
    ∃ U ∈ 𝓝 x, EqOn (flattenValues O) (fun _ => flattenValues O x) U := by
  obtain ⟨a, b, ⟨hax, hxb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hO.mem_nhds hx)
  refine ⟨Ioo a b, Ioo_mem_nhds hax hxb, ?_⟩
  intro y hy
  have hzero : (∫ s in x..y, Oᶜ.indicator (fun _ => (1 : ℝ)) s) = 0 := by
    apply intervalIntegral.integral_zero_ae
    exact Eventually.of_forall fun s hs => by
      have hsO : s ∈ O := hab ⟨lt_of_lt_of_le (lt_min hax hy.1) (le_of_lt hs.1),
        lt_of_le_of_lt hs.2 (max_lt hxb hy.2)⟩
      simp [hsO]
  have h := flattenValues_sub hO.measurableSet x y
  rw [hzero] at h
  exact sub_eq_zero.mp h

 theorem flattenValues_close {O : Set ℝ} (hO : MeasurableSet O) (hOfin : volume O ≠ ∞) (t : ℝ) :
    |flattenValues O t - t| ≤ (volume O).toReal := by
  have hI : IntervalIntegrable (O.indicator (fun _ => (1 : ℝ))) volume 0 t := by
    apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 t).mono_fun
      ((measurable_const.indicator hO).aestronglyMeasurable)
    exact Eventually.of_forall fun s => by by_cases hs : s ∈ O <;> simp [hs]
  have hsum : flattenValues O t + (∫ s in (0 : ℝ)..t, O.indicator (fun _ => (1 : ℝ)) s) = t := by
    rw [flattenValues, ← intervalIntegral.integral_add (flattenValues_integrable hO 0 t) hI]
    have heq : (fun s => Oᶜ.indicator (fun _ => (1 : ℝ)) s +
        O.indicator (fun _ => (1 : ℝ)) s) = fun _ => (1 : ℝ) := by
      funext s
      by_cases hs : s ∈ O <;> simp [hs]
    rw [heq, intervalIntegral.integral_const]
    simp
  have hbound := intervalIntegral.norm_integral_le_integral_norm_uIoc
    (f := O.indicator (fun _ => (1 : ℝ))) (a := 0) (b := t) (μ := volume)
  have heq : (fun s => ‖O.indicator (fun _ => (1 : ℝ)) s‖) =
      O.indicator (fun _ => (1 : ℝ)) := by
    funext s
    by_cases hs : s ∈ O <;> simp [hs]
  rw [heq] at hbound
  change ‖∫ s in (0 : ℝ)..t, O.indicator (fun _ => (1 : ℝ)) s‖ ≤
    ∫ s, O.indicator (1 : ℝ → ℝ) s ∂(volume.restrict (Ι (0 : ℝ) t)) at hbound
  rw [integral_indicator_one hO] at hbound
  have hm : ((volume.restrict (Ι (0 : ℝ) t)) O).toReal ≤ (volume O).toReal :=
    ENNReal.toReal_mono hOfin (Measure.restrict_apply_le _ _)
  have he : flattenValues O t - t = -(∫ s in (0 : ℝ)..t, O.indicator (fun _ => (1 : ℝ)) s) := by
    linarith
  rw [he, abs_neg]
  have hb : |∫ s in (0 : ℝ)..t, O.indicator (fun _ => (1 : ℝ)) s| ≤
      ((volume.restrict (Ι (0 : ℝ) t)) O).toReal := by
    simpa only [Real.norm_eq_abs, measureReal_def] using hbound
  exact hb.trans hm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScalarFlatteningEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The flattening construction retains a genuine Sobolev witness. Its
squared gradient error is exactly the energy above the removed values. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem flattenedGradient_energy_error (E : Set EuclideanPlane)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (V : EuclideanPlane → EuclideanPlane)
    {O : Set ℝ} (hO : MeasurableSet O) :
    (∫⁻ p in E, ENNReal.ofReal (‖flattenedGradient O u V p - V p‖^2)) =
      scalarEnergyMeasure E u V O := by
  rw [scalarEnergyMeasure, Measure.map_apply hu.measurable hO,
    withDensity_apply _ (hu.measurable hO)]
  rw [← lintegral_indicator (hu.measurable hO)]
  apply lintegral_congr
  intro p
  by_cases hp : u p ∈ O <;> simp [flattenedGradient, hp]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CountableValueFlattening
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous uniform and energy control while flattening countably
many prescribed scalar values. The Sobolev chain rule gives a witness on
the open domain. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_countable_value_flattening
    (hcoarea : PlanarSobolevCoarea)
    {U : Set EuclideanPlane} (hU : IsOpen U)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (W : DeGiorgi.MemW1pWitness 2 u U)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ p ∈ U, u p ∈ Icc (-B) B)
    {C : Set ℝ} (hC : C.Countable) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ O : Set ℝ, ∃ W' : DeGiorgi.MemW1pWitness 2 (flattenValues O ∘ u) U,
      IsOpen O ∧ C ⊆ O ∧ LipschitzWith 1 (flattenValues O) ∧
      (∀ t, |flattenValues O t-t| < δ) ∧
      (∫⁻ p in U, ENNReal.ofReal (‖W'.weakGrad p-W.weakGrad p‖^2)) < ENNReal.ofReal ε ∧
      (∀ c ∈ C, ∃ V ∈ 𝓝 c, EqOn (flattenValues O) (fun _ => flattenValues O c) V) ∧
      (∀ p, W.weakGrad p = 0 → W'.weakGrad p = 0) := by
  obtain ⟨O, hCO, hO, hvol, henergy⟩ := exists_small_open_local_energy_cover
    hcoarea hU hu W hC (lt_min (ENNReal.ofReal_pos.mpr hδ) (ENNReal.ofReal_pos.mpr hε))
  let W' := flattenedSobolevWitness hU hu W hB hb hO
  have hvolδ := hvol.trans_le (min_le_left _ _)
  have hOfin : volume O ≠ ∞ := (hvolδ.trans_le (le_of_lt ENNReal.ofReal_lt_top)).ne
  refine ⟨O, W', hO, hCO, flattenValues_lipschitz hO.measurableSet, ?_, ?_, ?_, ?_⟩
  · intro t
    exact (flattenValues_close hO.measurableSet hOfin t).trans_lt
      (ENNReal.toReal_lt_of_lt_ofReal hvolδ)
  · change (∫⁻ p in U, ENNReal.ofReal
      (‖flattenedGradient O u W.weakGrad p-W.weakGrad p‖^2)) < ENNReal.ofReal ε
    rw [flattenedGradient_energy_error U hu W.weakGrad hO.measurableSet]
    exact henergy.trans_le (min_le_right _ _)
  · intro c hc
    exact flattenValues_locally_constant hO (hCO hc)
  · intro p hp
    change flattenedGradient O u W.weakGrad p = 0
    by_cases hpu : u p ∈ O <;> simp [flattenedGradient, hpu, hp]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LocalHeightFlattening
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual height admits simultaneous uniform and local energy
flattening at the countably many selected end values. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem ControlledHeight.exists_local_value_flattening
    (hcoarea : PlanarSobolevCoarea) {R d : ℝ} (H : ControlledHeight R d)
    (A : ℝ) {C : Set ℝ} (hC : C.Countable)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    let W := heightLimitWitness H.error₀ H.error₁
      (H.height.continuous.comp complexPlaneCoordinates.continuous) H.weak_gradient A
    ∃ O : Set ℝ, ∃ W' : DeGiorgi.MemW1pWitness 2
      (flattenValues O ∘ H.height ∘ complexPlaneCoordinates) (ball 0 A),
      IsOpen O ∧ C ⊆ O ∧ LipschitzWith 1 (flattenValues O) ∧
      (∀ t, |flattenValues O t-t| < δ) ∧
      (∫⁻ p in ball 0 A, ENNReal.ofReal (‖W'.weakGrad p-W.weakGrad p‖^2)) < ENNReal.ofReal ε ∧
      (∀ c ∈ C, ∃ V ∈ 𝓝 c, EqOn (flattenValues O) (fun _ => flattenValues O c) V) ∧
      (∀ p, W.weakGrad p = 0 → W'.weakGrad p = 0) := by
  have hv := H.height.continuous.comp complexPlaneCoordinates.continuous
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : EuclideanPlane) A).bddAbove_image hv.norm.continuousOn
  apply exists_countable_value_flattening hcoarea isOpen_ball hv
    (heightLimitWitness H.error₀ H.error₁ hv H.weak_gradient A)
    (le_max_right B 0) ?_ hC hδ hε
  intro p hp
  apply abs_le.mp
  have hh : ‖H.height (complexPlaneCoordinates p)‖ ≤ B :=
    hB ⟨p, ball_subset_closedBall hp, rfl⟩
  exact (show |H.height (complexPlaneCoordinates p)| ≤ B from hh).trans (le_max_left _ _)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FlattenedHeightError
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.horizontalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative energy of the flattened height relative to the physical
vertical coordinate. The bound tends to zero with the actual height
error and the chosen flattening energy. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem norm_add_sq_le_twice {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a+b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
  have h := (sq_le_sq₀ (norm_nonneg (a+b))
    (add_nonneg (norm_nonneg a) (norm_nonneg b))).mpr (norm_add_le a b)
  nlinarith [sq_nonneg (‖a‖-‖b‖)]

 theorem heightLimitGradient_vertical_error (g₀ g₁ : Lp ℝ 2 (volume : Measure EuclideanPlane))
    (x : EuclideanPlane) :
    ‖heightLimitGradient g₀ g₁ x-EuclideanSpace.single (1 : Fin 2) 1‖^2 =
      g₀ x^2+g₁ x^2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, heightLimitGradient]

 theorem ControlledHeight.flattened_energy_error {R d : ℝ} (H : ControlledHeight R d)
    (A : ℝ) {v : EuclideanPlane → ℝ}
    (W : DeGiorgi.MemW1pWitness 2 v (ball 0 A)) {ε : ℝ} (hε : 0 < ε)
    (he : (∫⁻ x in ball 0 A,
      ENNReal.ofReal (‖W.weakGrad x-heightLimitGradient H.error₀ H.error₁ x‖^2)) < ENNReal.ofReal ε) :
    (∫ x in ball 0 A, ‖W.weakGrad x-EuclideanSpace.single (1 : Fin 2) 1‖^2) <
      2*ε+4*Real.pi*d := by
  let Y : EuclideanPlane := EuclideanSpace.single (1 : Fin 2) 1
  let V := heightLimitGradient H.error₀ H.error₁
  let W₀ := heightLimitWitness H.error₀ H.error₁
    (H.height.continuous.comp complexPlaneCoordinates.continuous) H.weak_gradient A
  let : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanPlane) A)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hF := (W.weakGrad_memLp.sub W₀.weakGrad_memLp).norm.integrable_sq
  change Integrable (fun x => ‖W.weakGrad x-V x‖^2) (volume.restrict (ball 0 A)) at hF
  have hB := (W₀.weakGrad_memLp.sub (memLp_const Y)).norm.integrable_sq
  change Integrable (fun x => ‖V x-Y‖^2) (volume.restrict (ball 0 A)) at hB
  have hW := (W.weakGrad_memLp.sub (memLp_const Y)).norm.integrable_sq
  change Integrable (fun x => ‖W.weakGrad x-Y‖^2) (volume.restrict (ball 0 A)) at hW
  have he' : (∫ x in ball 0 A, ‖W.weakGrad x-V x‖^2) < ε := by
    apply (ENNReal.ofReal_lt_ofReal_iff hε).mp
    rw [ofReal_integral_eq_lintegral_ofReal hF (Eventually.of_forall (fun _ => sq_nonneg _))]
    exact he
  have hlim : (∫ x in ball 0 A, ‖V x-Y‖^2) ≤ 2*Real.pi*d := by
    calc
      _ = ∫ x in ball 0 A, H.error₀ x^2+H.error₁ x^2 := by
        apply integral_congr_ae
        exact Eventually.of_forall (heightLimitGradient_vertical_error _ _)
      _ ≤ ∫ x, H.error₀ x^2+H.error₁ x^2 :=
        setIntegral_le_integral ((Lp.memLp H.error₀).integrable_sq.add (Lp.memLp H.error₁).integrable_sq)
          (Eventually.of_forall (fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _)))
      _ ≤ _ := H.error_bound
  have hbound : (∫ x in ball 0 A, ‖W.weakGrad x-Y‖^2) ≤
      2*(∫ x in ball 0 A, ‖W.weakGrad x-V x‖^2)+
      2*(∫ x in ball 0 A, ‖V x-Y‖^2) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hF.const_mul 2) (hB.const_mul 2)]
    apply integral_mono hW ((hF.const_mul 2).add (hB.const_mul 2))
    intro x
    change ‖W.weakGrad x-Y‖^2 ≤ 2*‖W.weakGrad x-V x‖^2+2*‖V x-Y‖^2
    simpa only [sub_add_sub_cancel] using
      norm_add_sq_le_twice (W.weakGrad x-V x) (V x-Y)
  change (∫ x in ball 0 A, ‖W.weakGrad x-Y‖^2) < _
  nlinarith

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

 theorem cutoff_gradient_square_bound {η u a b c d C₀ C₁ e : ℝ}
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (he : 0 ≤ e)
    (hη : |η| ≤ C₀) (hu : |u| ≤ e) (hc : |c| ≤ C₁) (hd : |d| ≤ C₁) :
    (η*a+c*u)^2+(η*b+d*u)^2 ≤ 2*C₀^2*(a^2+b^2)+4*C₁^2*e^2 := by
  have hηsq : η^2 ≤ C₀^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg η) hC₀).mpr hη
  have ha := mul_le_mul_of_nonneg_right hηsq (sq_nonneg a)
  have hb := mul_le_mul_of_nonneg_right hηsq (sq_nonneg b)
  have hcu : |c*u| ≤ C₁*e := by
    rw [abs_mul]
    exact mul_le_mul hc hu (abs_nonneg u) hC₁
  have hdu : |d*u| ≤ C₁*e := by
    rw [abs_mul]
    exact mul_le_mul hd hu (abs_nonneg u) hC₁
  have hcs : (c*u)^2 ≤ (C₁*e)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (c*u)) (mul_nonneg hC₁ he)).mpr hcu
  have hds : (d*u)^2 ≤ (C₁*e)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (d*u)) (mul_nonneg hC₁ he)).mpr hdu
  nlinarith [sq_nonneg (η*a-c*u), sq_nonneg (η*b-d*u)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactValueFlattening
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Flattening preserves compact support of the old source tests, in
addition to their continuous representatives and quantitative errors. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_compact_value_flattening
    (hcoarea : PlanarSobolevCoarea) {U : Set EuclideanPlane} (hU : IsOpen U)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (hs : HasCompactSupport u)
    (W : DeGiorgi.MemW1pWitness 2 u U) {C : Set ℝ} (hC : C.Countable)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ O : Set ℝ, ∃ W' : DeGiorgi.MemW1pWitness 2 (flattenValues O ∘ u) U,
      IsOpen O ∧ C ⊆ O ∧ Continuous (flattenValues O ∘ u) ∧
      HasCompactSupport (flattenValues O ∘ u) ∧
      (∀ t, |flattenValues O t-t| < δ) ∧
      (∫⁻ p in U, ENNReal.ofReal (‖W'.weakGrad p-W.weakGrad p‖^2)) < ENNReal.ofReal ε ∧
      (∀ p, W.weakGrad p = 0 → W'.weakGrad p = 0) := by
  obtain ⟨B, hB⟩ := hu.bounded_above_of_compact_support hs
  have hb : ∀ p ∈ U, u p ∈ Icc (-max B 0) (max B 0) := by
    intro p _
    apply abs_le.mp
    exact (show |u p| ≤ B from hB p).trans (le_max_left _ _)
  obtain ⟨O, W', hO, hCO, hLip, hclose, henergy, _, hzero⟩ :=
    exists_countable_value_flattening hcoarea hU hu W (le_max_right B 0) hb hC hδ hε
  exact ⟨O, W', hO, hCO, hLip.continuous.comp hu,
    hs.comp_left (flattenValues_zero O), hclose, henergy, hzero⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FlattenedEndNeighborhoods
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finitely many flattened coordinates have a common constancy
neighborhood at each specified end value. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem flattened_coordinates_constant_near
    {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    (f : ι → X → ℝ) {p : X} (hf : ∀ i, ContinuousAt (f i) p)
    (O : ι → Set ℝ) (hO : ∀ i, IsOpen (O i)) (hp : ∀ i, f i p ∈ O i) :
    ∃ V : Set X, IsOpen V ∧ p ∈ V ∧
      ∀ i, EqOn (fun x => flattenValues (O i) (f i x))
        (fun _ => flattenValues (O i) (f i p)) V := by
  have hi (i : ι) : ∀ᶠ x in 𝓝 p,
      flattenValues (O i) (f i x) = flattenValues (O i) (f i p) := by
    obtain ⟨W, hW, hconst⟩ := flattenValues_locally_constant (hO i) (hp i)
    exact ((hf i).eventually hW).mono (fun x hx => hconst hx)
  have hall : ∀ᶠ x in 𝓝 p, ∀ i,
      flattenValues (O i) (f i x) = flattenValues (O i) (f i p) :=
    Filter.eventually_all.mpr hi
  obtain ⟨V, hsub, hV, hpV⟩ := mem_nhds_iff.mp hall
  exact ⟨V, hV, hpV, fun i x hx => hsub hx i⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PriorityInterpolation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite priority interpolation of a horizontal coordinate. Overlaps
of the cutoff supports are allowed; the derivative estimate is uniform
in the number of cutoffs. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
 theorem priorityBlend_norm_le {L : List ((E → ℝ) × ℝ)} {X : E → ℝ} {p : E} {B : ℝ}
    (hX : ‖X p‖ ≤ B) (hL : ∀ e ∈ L, e.1 p ∈ Icc (0 : ℝ) 1 ∧ ‖e.2‖ ≤ B) :
    ‖priorityBlend L X p‖ ≤ B := by
  induction L with
  | nil => exact hX
  | cons e L ih =>
    have he := hL e (by simp)
    have ht := ih (fun a ha => hL a (by simp [ha]))
    have h0 : 0 ≤ 1-e.1 p := by linarith [he.1.2]
    calc
      ‖priorityBlend (e::L) X p‖ ≤ ‖e.1 p*e.2‖+‖(1-e.1 p)*priorityBlend L X p‖ := norm_add_le _ _
      _ = e.1 p*‖e.2‖+(1-e.1 p)*‖priorityBlend L X p‖ := by
        simp only [norm_mul, Real.norm_eq_abs (e.1 p), abs_of_nonneg he.1.1,
          Real.norm_eq_abs (1-e.1 p), abs_of_nonneg h0]
      _ ≤ e.1 p*B+(1-e.1 p)*B := add_le_add
        (mul_le_mul_of_nonneg_left he.2 he.1.1) (mul_le_mul_of_nonneg_left ht h0)
      _ = B := by ring

 theorem priorityBlend_differentiableAt {L : List ((E → ℝ) × ℝ)} {X : E → ℝ} {p : E}
    (hX : DifferentiableAt ℝ X p) (hL : ∀ e ∈ L, DifferentiableAt ℝ e.1 p) :
    DifferentiableAt ℝ (priorityBlend L X) p := by
  induction L with
  | nil => exact hX
  | cons e L ih =>
    have he := hL e (by simp)
    exact (he.mul_const e.2).add ((differentiableAt_const 1).sub he |>.mul
      (ih (fun a ha => hL a (by simp [ha]))))

 theorem priorityBlend_derivative_bound {L : List ((E → ℝ) × ℝ)} {X : E → ℝ} {p : E} {B : ℝ}
    (hX : DifferentiableAt ℝ X p) (hXbound : ‖X p‖ ≤ B)
    (hL : ∀ e ∈ L, DifferentiableAt ℝ e.1 p ∧ e.1 p ∈ Icc (0 : ℝ) 1 ∧ ‖e.2‖ ≤ B) :
    ‖fderiv ℝ (priorityBlend L X) p-priorityResidual L p • fderiv ℝ X p‖ ≤
      2*B*(L.map (fun e => ‖fderiv ℝ e.1 p‖)).sum := by
  induction L with
  | nil => simp [priorityBlend, priorityResidual]
  | cons e L ih =>
    have he := hL e (by simp)
    have ht (a) (ha : a ∈ L) := hL a (by simp [ha])
    have htd := priorityBlend_differentiableAt hX (fun a ha => (ht a ha).1)
    have htb := priorityBlend_norm_le hXbound (fun a ha => (ht a ha).2)
    have hdiff := (he.1.hasFDerivAt.mul_const e.2).add
      (((hasFDerivAt_const (1 : ℝ) p).sub he.1.hasFDerivAt).mul htd.hasFDerivAt)
    have hform : fderiv ℝ (priorityBlend (e::L) X) p =
        (e.2-priorityBlend L X p) • fderiv ℝ e.1 p +
          (1-e.1 p) • fderiv ℝ (priorityBlend L X) p := by
      have hdEq := hdiff.fderiv
      change fderiv ℝ (priorityBlend (e::L) X) p = _ at hdEq
      simp only [Pi.sub_apply, zero_sub] at hdEq
      rw [hdEq]
      module
    have herror : fderiv ℝ (priorityBlend (e::L) X) p -
        priorityResidual (e::L) p • fderiv ℝ X p =
        (e.2-priorityBlend L X p) • fderiv ℝ e.1 p + (1-e.1 p) •
          (fderiv ℝ (priorityBlend L X) p-priorityResidual L p • fderiv ℝ X p) := by
      rw [hform]
      dsimp only [priorityResidual]
      module
    have hnonneg : 0 ≤ 1-e.1 p := by linarith [he.2.1.2]
    have hcoef : ‖1-e.1 p‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      linarith [he.2.1.1]
    have hval : ‖e.2-priorityBlend L X p‖ ≤ 2*B :=
      (norm_sub_le _ _).trans (by linarith [he.2.2, htb])
    rw [herror, List.map_cons, List.sum_cons, mul_add]
    calc
      _ ≤ ‖(e.2-priorityBlend L X p) • fderiv ℝ e.1 p‖ +
          ‖(1-e.1 p) • (fderiv ℝ (priorityBlend L X) p-priorityResidual L p • fderiv ℝ X p)‖ :=
        norm_add_le _ _
      _ ≤ 2*B*‖fderiv ℝ e.1 p‖ +
          ‖fderiv ℝ (priorityBlend L X) p-priorityResidual L p • fderiv ℝ X p‖ := by
        simp only [norm_smul]
        exact add_le_add (mul_le_mul_of_nonneg_right hval (norm_nonneg _))
          ((mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)).trans_eq (one_mul _))
      _ ≤ _ := add_le_add le_rfl (ih ht)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PriorityWeights
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

 theorem priorityWeighted_summable {χ c : ℕ → ℝ} (hχ : ∀ n, χ n ∈ Icc (0 : ℝ) 1)
    {B : ℝ} (hc : ∀ n, ‖c n‖ ≤ B) : Summable (fun n => priorityWeight χ n*c n) := by
  apply Summable.of_norm_bounded ((priorityWeight_summable hχ).mul_right B)
  intro n
  rw [norm_mul, Real.norm_eq_abs (priorityWeight χ n), abs_of_nonneg (priorityWeight_nonneg hχ n)]
  exact mul_le_mul_of_nonneg_left (hc n) (priorityWeight_nonneg hχ n)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PriorityStability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stability of the countable interpolation under changes in its
active scalar values. Cutoffs equal to zero need no coefficient bound. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem priorityInfiniteValue_stability
    {χ c d : ℕ → ℝ} (hχ : ∀ n, χ n ∈ Icc (0 : ℝ) 1)
    {B C ε x y : ℝ} (hc : ∀ n, ‖c n‖ ≤ B) (hd : ∀ n, ‖d n‖ ≤ C)
    (hxy : ‖x-y‖ ≤ ε) (hcd : ∀ n, χ n = 0 ∨ ‖c n-d n‖ ≤ ε) :
    ‖priorityInfiniteValue χ c x-priorityInfiniteValue χ d y‖ ≤ ε := by
  have hw := priorityWeight_tsum_mem_unit hχ
  have hrem : 0 ≤ 1-∑' n, priorityWeight χ n := by linarith [hw.2]
  have hcs := priorityWeighted_summable hχ hc
  have hds := priorityWeighted_summable hχ hd
  have hdiff : (∑' n, priorityWeight χ n*(c n-d n)) =
      (∑' n, priorityWeight χ n*c n)-(∑' n, priorityWeight χ n*d n) := by
    simp_rw [mul_sub]
    exact hcs.tsum_sub hds
  have hterm (n : ℕ) : ‖priorityWeight χ n*(c n-d n)‖ ≤ priorityWeight χ n*ε := by
    rcases hcd n with hn | hn
    · simp [priorityWeight, hn]
    · rw [norm_mul, Real.norm_eq_abs (priorityWeight χ n), abs_of_nonneg (priorityWeight_nonneg hχ n)]
      exact mul_le_mul_of_nonneg_left hn (priorityWeight_nonneg hχ n)
  have hsum : ‖∑' n, priorityWeight χ n*(c n-d n)‖ ≤ (∑' n, priorityWeight χ n)*ε := by
    have h := tsum_of_norm_bounded (f := fun n => priorityWeight χ n*(c n-d n))
      ((priorityWeight_summable hχ).mul_right ε).hasSum hterm
    simpa only [(priorityWeight_summable hχ).tsum_mul_right] using h
  have heq : priorityInfiniteValue χ c x-priorityInfiniteValue χ d y =
      (1-∑' n, priorityWeight χ n)*(x-y)+∑' n, priorityWeight χ n*(c n-d n) := by
    rw [priorityInfiniteValue, priorityInfiniteValue, hdiff]
    ring
  rw [heq]
  calc
    _ ≤ ‖(1-∑' n, priorityWeight χ n)*(x-y)‖+‖∑' n, priorityWeight χ n*(c n-d n)‖ := norm_add_le _ _
    _ ≤ (1-∑' n, priorityWeight χ n)*ε+(∑' n, priorityWeight χ n)*ε := by
      rw [norm_mul, Real.norm_eq_abs (1-∑' n, priorityWeight χ n), abs_of_nonneg hrem]
      exact add_le_add (mul_le_mul_of_nonneg_left hxy hrem) hsum
    _ = ε := by ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PriorityTermination
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A cutoff equal to one terminates the priority interpolation. Its
continuity near a nonpoint end therefore does not require a trace of
the original horizontal coordinate at that end. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem priorityRemainder_zero_of_one {χ : ℕ → ℝ} {j n : ℕ} (hj : χ j = 1) (hjn : j < n) :
    priorityRemainder χ n = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hjn)
  simp only [hj, sub_self]

 theorem priorityWeight_zero_after_one {χ : ℕ → ℝ} {j n : ℕ} (hj : χ j = 1) (hjn : j < n) :
    priorityWeight χ n = 0 := by
  rw [priorityWeight, priorityRemainder_zero_of_one hj hjn, mul_zero]

 theorem priorityInfiniteValue_eq_prefix {χ c : ℕ → ℝ} {j : ℕ} (hj : χ j = 1) (x : ℝ) :
    priorityInfiniteValue χ c x = ∑ n ∈ Finset.range (j+1), priorityWeight χ n*c n := by
  have hw : (∑' n, priorityWeight χ n) = 1 := by
    have hsum : (∑' n, priorityWeight χ n) = ∑ n ∈ Finset.range (j+1), priorityWeight χ n := by
      apply tsum_eq_sum
      intro n hn
      have hn' : j+1 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
      exact priorityWeight_zero_after_one hj (by omega)
    rw [hsum, priorityWeight_sum, priorityRemainder_zero_of_one hj (Nat.lt_succ_self j), sub_zero]
  rw [priorityInfiniteValue, hw, sub_self, zero_mul, zero_add]
  apply tsum_eq_sum
  intro n hn
  rw [priorityWeight_zero_after_one hj (by
    have hn' : j+1 ≤ n := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hn)
    omega), zero_mul]

 theorem priorityWeight_continuousAt {X : Type*} [TopologicalSpace X]
    {χ : ℕ → X → ℝ} {p : X} (hχ : ∀ n, ContinuousAt (χ n) p) (n : ℕ) :
    ContinuousAt (fun q => priorityWeight (fun i => χ i q) n) p := by
  apply (hχ n).mul
  exact tendsto_finsetProd _ (fun i _ => continuousAt_const.sub (hχ i))

 theorem priorityInfiniteValue_continuousAt_of_one {X : Type*} [TopologicalSpace X]
    {χ : ℕ → X → ℝ} {p : X} (hχ : ∀ n, ContinuousAt (χ n) p)
    (c : ℕ → ℝ) (x : X → ℝ) {j : ℕ} (hj : ∀ᶠ q in 𝓝 p, χ j q = 1) :
    ContinuousAt (fun q => priorityInfiniteValue (fun i => χ i q) c (x q)) p := by
  have hfinite : ContinuousAt (fun q =>
      ∑ n ∈ Finset.range (j+1), priorityWeight (fun i => χ i q) n*c n) p :=
    tendsto_finsetSum _ (fun n _ => (priorityWeight_continuousAt hχ n).mul continuousAt_const)
  apply hfinite.congr_of_eventuallyEq
  filter_upwards [hj] with q hq
  exact priorityInfiniteValue_eq_prefix (χ := fun i => χ i q) (c := c) hq (x q)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_PriorityPointTrace
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity at a point end: early cutoffs are retained exactly, while
all later active scalar values approach the original point trace. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem priorityTruncatedValues_bound {c : ℕ → ℝ} {B : ℝ} (hc : ∀ n, ‖c n‖ ≤ B)
    (a : ℝ) (N n : ℕ) : ‖priorityTruncatedValues c a N n‖ ≤ max B ‖a‖ := by
  by_cases hn : n < N
  · simp only [priorityTruncatedValues, ite_eq_left hn]
    exact (hc n).trans (le_max_left _ _)
  · simp only [priorityTruncatedValues, ite_eq_right hn]
    exact le_max_right _ _

 theorem priorityInfiniteValue_constant_tail {χ c : ℕ → ℝ}
    (hχ : ∀ n, χ n ∈ Icc (0 : ℝ) 1) {B : ℝ} (hc : ∀ n, ‖c n‖ ≤ B) (a : ℝ) (N : ℕ) :
    priorityInfiniteValue χ (priorityTruncatedValues c a N) a =
      a + ∑ n ∈ Finset.range N, priorityWeight χ n*(c n-a) := by
  let d := priorityTruncatedValues c a N
  have hds := priorityWeighted_summable hχ (priorityTruncatedValues_bound hc a N)
  have has := (priorityWeight_summable hχ).mul_right a
  have hdiff : (∑' n, priorityWeight χ n*(d n-a)) =
      (∑' n, priorityWeight χ n*d n)-(∑' n, priorityWeight χ n)*a := by
    simp_rw [mul_sub]
    rw [hds.tsum_sub has, (priorityWeight_summable hχ).tsum_mul_right]
  have hfinite : (∑' n, priorityWeight χ n*(d n-a)) =
      ∑ n ∈ Finset.range N, priorityWeight χ n*(c n-a) := by
    calc
      _ = ∑ n ∈ Finset.range N, priorityWeight χ n*(d n-a) := by
        apply tsum_eq_sum
        intro n hn
        simp only [d, priorityTruncatedValues, ite_eq_right (by simpa only [Finset.mem_range] using hn),
          sub_self, mul_zero]
      _ = _ := Finset.sum_congr rfl (fun n hn => by
        simp only [d, priorityTruncatedValues, ite_eq_left (Finset.mem_range.mp hn)])
  change (1-∑' n, priorityWeight χ n)*a+(∑' n, priorityWeight χ n*d n) = _
  rw [← hfinite, hdiff]
  ring

 theorem priorityInfiniteValue_continuousAt_point_trace
    {X : Type*} [TopologicalSpace X] {p : X}
    (χ : ℕ → X → ℝ) (c : ℕ → ℝ) (x : X → ℝ)
    (hχc : ∀ n, ContinuousAt (χ n) p)
    (hχ : ∀ q n, χ n q ∈ Icc (0 : ℝ) 1)
    {B : ℝ} (hc : ∀ n, ‖c n‖ ≤ B) (hx : ContinuousAt x p)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ᶠ q in 𝓝 p,
      ∀ n, N ≤ n → χ n q ≠ 0 → ‖c n-x p‖ ≤ ε) :
    ContinuousAt (fun q => priorityInfiniteValue (fun n => χ n q) c (x q)) p := by
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  let δ := ε/4
  have hδ : 0 < δ := by dsimp [δ] <;> positivity
  obtain ⟨N, hN⟩ := htail δ hδ
  let d := priorityTruncatedValues c (x p) N
  let Q := fun q => priorityInfiniteValue (fun n => χ n q) d (x p)
  have hQ : ContinuousAt Q p := by
    have hh : ContinuousAt (fun q => x p+
        ∑ n ∈ Finset.range N, priorityWeight (fun i => χ i q) n*(c n-x p)) p :=
      continuousAt_const.add (tendsto_finsetSum _ (fun n _ =>
        (priorityWeight_continuousAt hχc n).mul continuousAt_const))
    apply hh.congr_of_eventuallyEq
    exact Eventually.of_forall fun q => priorityInfiniteValue_constant_tail (hχ q) hc (x p) N
  have hnearX : ∀ᶠ q in 𝓝 p, ‖x q-x p‖ < δ := by
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp hx) δ hδ
  have hnearQ : ∀ᶠ q in 𝓝 p, dist (Q q) (Q p) < δ :=
    (Metric.tendsto_nhds.mp hQ) δ hδ
  have hcompare (q : X) (hq : ∀ n, N ≤ n → χ n q ≠ 0 → ‖c n-x p‖ ≤ δ)
      (hxq : ‖x q-x p‖ ≤ δ) :
      dist (priorityInfiniteValue (fun n => χ n q) c (x q)) (Q q) ≤ δ := by
    apply priorityInfiniteValue_stability (hχ q) hc (priorityTruncatedValues_bound hc (x p) N) hxq
    intro n
    by_cases hz : χ n q = 0
    · exact Or.inl hz
    · apply Or.inr
      by_cases hn : n < N
      · simp only [priorityTruncatedValues, ite_eq_left hn, sub_self, norm_zero]
        exact hδ.le
      · simpa only [d, priorityTruncatedValues, ite_eq_right hn] using hq n (Nat.le_of_not_gt hn) hz
  have hp : dist (priorityInfiniteValue (fun n => χ n p) c (x p)) (Q p) ≤ δ :=
    hcompare p (mem_of_mem_nhds hN) (by simpa only [sub_self, norm_zero] using hδ.le)
  filter_upwards [hN, hnearX, hnearQ] with q hq hxq hQq
  have hqq := hcompare q hq hxq.le
  calc
    _ ≤ dist (priorityInfiniteValue (fun n => χ n q) c (x q)) (Q q)+
        dist (Q q) (Q p)+dist (Q p) (priorityInfiniteValue (fun n => χ n p) c (x p)) :=
      dist_triangle4 _ _ _ _
    _ < ε := by rw [dist_comm (Q p)] ; dsimp [δ] at hqq hQq hp <;> linarith

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
-- module Solutions.Q146_CD.CircleDomains_Selection_PointFiberConcentration
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed inverse projections turn concentration of source supports into
concentration of the selected target values at every singleton fiber. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem closed_map_singleton_value_neighborhood
    {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    {P : X → Y} (hP : IsClosedMap P) {p : X}
    (hfiber : P ⁻¹' {P p} = {p}) {a : X → ℝ} (ha : ContinuousAt a p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z, dist (P z) (P p) < δ → ‖a z-a p‖ < ε := by
  have hn : a ⁻¹' ball (a p) ε ∈ 𝓝 p := ha.preimage_mem_nhds (ball_mem_nhds _ hε)
  obtain ⟨U, hUn, hU, hpU⟩ := mem_nhds_iff.mp hn
  have hV : IsOpen (kernImage P U) := isClosedMap_iff_kernImage.mp hP hU
  have hpV : P p ∈ kernImage P U := by
    intro z hz
    have hzmem : z ∈ P ⁻¹' {P p} := hz
    rw [hfiber] at hzmem
    simpa only [mem_singleton_iff.mp hzmem] using hpU
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hpV)
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  have hzU : z ∈ U := hball hz rfl
  simpa only [mem_preimage, mem_ball, dist_eq_norm] using hUn hzU

 theorem closed_map_section_value_continuousAt
    {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    {P : X → Y} (hP : IsClosedMap P) {p : X}
    (hfiber : P ⁻¹' {P p} = {p}) {a : X → ℝ} (ha : ContinuousAt a p)
    (s : Y → X) (hs : ∀ y, P (s y) = y) :
    ContinuousAt (a ∘ s) (P p) := by
  have hsp : s (P p) = p := by
    have hh : s (P p) ∈ P ⁻¹' {P p} := hs (P p)
    rwa [hfiber, mem_singleton_iff] at hh
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hnear⟩ := closed_map_singleton_value_neighborhood hP hfiber ha hε
  filter_upwards [ball_mem_nhds (P p) hδ] with y hy
  simpa only [comp_apply, hsp, dist_eq_norm] using hnear (s y) (by rwa [hs y])

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
-- module Solutions.Q146_CD.CircleDomains_Selection_ProjectionEndFibers
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fibers of the continuous inverse projection are the complementary
components when the original complement is dust, by the matched Jordan
exhaustion. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem inverse_projection_component_eq_fiber
    {G : Set Sphere} (hG : IsOpen G) (hTD : IsTotallyDisconnected Gᶜ)
    {f P : Sphere → Sphere} (hf : IsConformalOn f G) (hi : InjOn f G)
    (hP : Continuous P) (hInv : ∀ x ∈ G, P (f x) = x)
    (hOut : ∀ y ∉ f '' G, P y ∈ Gᶜ)
    (C : ℕ → SmoothJordanCore G) (J : (n : ℕ) → Fin (C n).count → ℂ ≃ₜ ℂ)
    (hstrict : ∀ n, (C n).carrier ⊆ interior (C (n+1)).carrier)
    (hcover : (⋃ n, interior (C n).carrier) = G)
    (hJd : ∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (J n i))))
    (hJe : ∀ n, (f '' (C n).carrier)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J n i))
    (hboundary : ∀ n i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J n i)))
    (hside : ∀ n i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk i))) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J n i)))
    {p : Sphere} (hp : p ∈ (f '' G)ᶜ) :
    connectedComponentIn (f '' G)ᶜ p = P ⁻¹' {P p} := by
  have hfront (n : ℕ) (i : Fin (C n).count) :
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i)) ⊆ G := by
    intro x hx
    apply (C n).subset
    have hh : x ∈ frontier (C n).carrier := by
      rw [SmoothJordanCore.carrier, frontier_closedJordanCore (C n).disk (C n).disjoint]
      exact mem_iUnion.mpr ⟨i, hx⟩
    simpa only [(C n).isCompact.isClosed.closure_eq] using frontier_subset_closure hh
  have hcap (n : ℕ) (i : Fin (C n).count) := inverse_projection_matched_cap hG hP hInv hOut
    ((C n).disk i) (J n i) (hfront n i) (hboundary n i) (hside n i)
  have hvalue (b : (n : ℕ) → Fin (C n).count) (q : Sphere) (hq : q ∈ Gᶜ)
      (hs : connectedComponentIn Gᶜ q = ⋂ n, closedTerminalCap ((C n).disk (b n)))
      {z : Sphere} (hz : z ∈ ⋂ n, closedTerminalCap (J n (b n))) : P z = q := by
    have hmem : P z ∈ connectedComponentIn Gᶜ q := by
      rw [hs]
      exact mem_iInter.mpr fun n => hcap n (b n) (mem_image_of_mem P (mem_iInter.mp hz n))
    have hsingle : connectedComponentIn Gᶜ q = {q} :=
      (hTD _ (connectedComponentIn_subset _ _) isPreconnected_connectedComponentIn).eq_singleton_of_mem
        (mem_connectedComponentIn hq)
    simpa only [hsingle, mem_singleton_iff] using hmem
  obtain ⟨b, q, hq, hs, ht, _⟩ := corresponding_source_end_of_target hG hf hi C J
    hstrict hcover hJd hJe hboundary hside hp
  have hpp : P p = q := hvalue b q hq hs (ht ▸ mem_connectedComponentIn hp)
  apply Subset.antisymm
  · intro z hz
    change P z = P p
    exact (hvalue b q hq hs (ht ▸ hz)).trans hpp.symm
  · intro z hz
    have he : P z = P p := hz
    have hzOut : z ∈ (f '' G)ᶜ := by
      rintro ⟨x, hx, rfl⟩
      exact hOut p hp (by rw [← he, hInv x hx]; exact hx)
    obtain ⟨b', q', hq', hs', ht', _⟩ := corresponding_source_end_of_target hG hf hi C J
      hstrict hcover hJd hJe hboundary hside hzOut
    have hqq : q' = q := (hvalue b' q' hq' hs' (ht' ▸ mem_connectedComponentIn hzOut)).symm.trans
      (he.trans hpp)
    have hb : b' = b := by
      funext n
      by_contra hne
      have hq₁ : q ∈ closedTerminalCap ((C n).disk (b n)) :=
        mem_iInter.mp (hs ▸ mem_connectedComponentIn hq) n
      have hq₂ : q ∈ closedTerminalCap ((C n).disk (b' n)) := by
        rw [← hqq]
        exact mem_iInter.mp (hs' ▸ mem_connectedComponentIn hq') n
      exact Set.disjoint_left.mp (disjoint_closedTerminalCaps (C n).disk (C n).disjoint hne) hq₂ hq₁
    rw [ht]
    rw [hb] at ht'
    exact ht' ▸ mem_connectedComponentIn hzOut

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

 theorem projection_fiber (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {p : Sphere} (hp : p ∉ extendAtInfinity M.function '' G) :
    M.projection ⁻¹' {M.projection p} =
      connectedComponentIn (extendAtInfinity M.function '' G)ᶜ p := by
  obtain ⟨C, J, hstrict, hcover, hd, he, hb, hs⟩ := exists_matched_jordan_exhaustion
    hsard hsch hG hconn hinf M.conformal.1 M.conformal.bijOn.injOn rfl
  exact (inverse_projection_component_eq_fiber hG hTD M.conformal.1 M.conformal.bijOn.injOn
    M.projection_continuous M.projection_inverse M.projection_outside
    C J hstrict hcover hd he hb hs hp).symm

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

 theorem projection_closed (M : CompactScalarModel G u) : IsClosedMap M.projection :=
  M.projection_continuous.isClosedMap

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ClosedMapDescent
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous scalar constant on each compact fiber descends through
a closed quotient. Only continuity along the relevant fiber is needed. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem closed_map_section_continuousAt_of_fiber
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {P : X → Y} (hP : IsClosedMap P) (s : Y → X) (hs : ∀ y, P (s y) = y)
    {a : X → ℝ} {q : Y} {v : ℝ}
    (ha : ∀ z, P z = q → ContinuousAt a z)
    (hc : ∀ z, P z = q → a z = v) :
    ContinuousAt (a ∘ s) q ∧ a (s q) = v := by
  have hvalue : a (s q) = v := hc _ (hs q)
  refine ⟨?_, hvalue⟩
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  let U := interior (a ⁻¹' ball v ε)
  have hU : IsOpen U := isOpen_interior
  have hfiber : P ⁻¹' {q} ⊆ U := by
    intro z hz
    apply mem_interior_iff_mem_nhds.mpr
    have hn : ball v ε ∈ 𝓝 (a z) := by rw [hc z hz]; exact ball_mem_nhds _ hε
    exact (ha z hz).preimage_mem_nhds hn
  have hV : IsOpen (kernImage P U) := isClosedMap_iff_kernImage.mp hP hU
  have hqV : q ∈ kernImage P U := fun _ hz => hfiber hz
  filter_upwards [hV.mem_nhds hqV] with y hy
  have hsy : s y ∈ U := hy (hs y)
  have hnear := interior_subset hsy
  simpa only [mem_preimage, mem_ball, comp_apply, hvalue] using hnear

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ModelHeightComponents
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous zero-gradient height is constant on every actual
complementary component of a retained deformed circle model. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem height_constant_on_components (M : CompactScalarModel G u)
    (hinf : OnePoint.infty ∈ G) {v : ℂ → ℝ} (hv : Continuous v)
    (V : EuclideanPlane → EuclideanPlane)
    (hw : DeGiorgi.HasWeakGrad V (v ∘ complexPlaneCoordinates) univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    (hz : ∀ᵐ p ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      V p = 0)
    {p q : EuclideanPlane} (hp : p ∉ physicalPlaneDomain (extendAtInfinity M.function '' G))
    (hq : planeSphere q ∈ connectedComponentIn (extendAtInfinity M.function '' G)ᶜ (planeSphere p)) :
    v (complexPlaneCoordinates p) = v (complexPlaneCoordinates q) := by
  let Ω := extendAtInfinity M.function '' G
  let e := M.deformation.onePointCongr
  have he : e '' M.roundDomain = Ω := M.image_eq.symm
  have hec : e '' M.roundDomainᶜ = Ωᶜ := by rw [e.image_compl, he]
  have hp0 : e.symm (planeSphere p) ∈ M.roundDomainᶜ := by
    intro hh
    apply hp
    change planeSphere p ∈ Ω
    rw [← he]
    exact ⟨_, hh, e.apply_symm_apply _⟩
  let K := connectedComponentIn M.roundDomainᶜ (e.symm (planeSphere p))
  have hKimage : e '' K = connectedComponentIn Ωᶜ (planeSphere p) := by
    simpa only [hec, e.apply_symm_apply] using e.image_connectedComponentIn hp0
  have hpk : e.symm (planeSphere p) ∈ K := mem_connectedComponentIn hp0
  have hqk : e.symm (planeSphere q) ∈ K := by
    have hq' : planeSphere q ∈ e '' K := by rwa [hKimage]
    obtain ⟨a, ha, haq⟩ := hq'
    simpa only [← haq, e.symm_apply_apply] using ha
  rcases M.round_circle.2.2 (e.symm (planeSphere p)) hp0 with hsingle | hround
  · obtain ⟨a, ha⟩ := hsingle
    change K = {a} at ha
    have hpq : e.symm (planeSphere p) = e.symm (planeSphere q) := by
      rw [ha] at hpk hqk
      exact (mem_singleton_iff.mp hpk).trans (mem_singleton_iff.mp hqk).symm
    have hh := congrArg e hpq
    simp only [e.apply_symm_apply] at hh
    exact congrArg v (OnePoint.coe_injective hh)
  · change IsRoundClosedDisk K at hround
    have hiΩ : OnePoint.infty ∈ Ω := ⟨_, hinf, rfl⟩
    have hiround : OnePoint.infty ∈ M.roundDomain := by
      rw [← he] at hiΩ
      obtain ⟨a, ha, hai⟩ := hiΩ
      have haInf : a = OnePoint.infty := by
        apply e.injective
        exact hai
      rwa [haInf] at ha
    have hiK : OnePoint.infty ∉ K := by
      intro hh
      exact (connectedComponentIn_subset _ _ hh) hiround
    obtain ⟨c, r, hr, hK⟩ := isRoundClosedDisk_eq_euclidean hround hiK
    let E : ℂ ≃ₜ EuclideanPlane := M.deformation.trans complexPlaneCoordinates.symm.toHomeomorph
    have hE (z : ℂ) : planeSphere (E z) = e (z : Sphere) := by
      change ((complexPlaneCoordinates (complexPlaneCoordinates.symm (M.deformation z)) : ℂ) : Sphere) = _
      rw [complexPlaneCoordinates.apply_symm_apply]
      rfl
    have hsub : E '' Metric.closedBall c r ⊆ (physicalPlaneDomain Ω)ᶜ := by
      rintro a ⟨z, hz', rfl⟩
      change planeSphere (E z) ∈ Ωᶜ
      rw [hE, ← hec]
      apply mem_image_of_mem
      apply connectedComponentIn_subset M.roundDomainᶜ (e.symm (planeSphere p))
      change (z : Sphere) ∈ K
      rw [hK]
      exact ⟨z, hz', rfl⟩
    have hzE : ∀ᵐ a ∂volume.restrict (E '' Metric.closedBall c r), V a = 0 :=
      hz.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    obtain ⟨a, ha⟩ := constant_on_homeomorphic_disk (hv.comp complexPlaneCoordinates.continuous)
      V hw hLp E c hr hzE
    have hmem (t : EuclideanPlane) (ht : e.symm (planeSphere t) ∈ K) :
        t ∈ E '' Metric.closedBall c r := by
      have hback : e.symm (planeSphere t) =
          ((M.deformation.symm (complexPlaneCoordinates t) : ℂ) : Sphere) := rfl
      rw [hback, hK, OnePoint.coe_injective.mem_set_image] at ht
      refine ⟨M.deformation.symm (complexPlaneCoordinates t), ht, ?_⟩
      change complexPlaneCoordinates.symm
        (M.deformation (M.deformation.symm (complexPlaneCoordinates t))) = t
      rw [M.deformation.apply_symm_apply, complexPlaneCoordinates.symm_apply_apply]
    exact (ha p (hmem p hpk)).trans (ha q (hmem q hqk)).symm

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelHeightDescent
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.horizontalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed conductivity height descends continuously through
the actual source projection, including every nonpoint end. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem height_constant_on_sphere_components (M : CompactScalarModel G u)
    (hinf : OnePoint.infty ∈ G) {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ x ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ x = 0)
    {p q : Sphere} (hp : p ∉ extendAtInfinity M.function '' G)
    (hq : q ∈ connectedComponentIn (extendAtInfinity M.function '' G)ᶜ p) :
    H.height (finiteCoord p) = H.height (finiteCoord q) := by
  have hqout := connectedComponentIn_subset _ _ hq
  cases p using OnePoint.rec with
  | infty => exact (hp ⟨_, hinf, rfl⟩).elim
  | coe z =>
    cases q using OnePoint.rec with
    | infty => exact (hqout ⟨_, hinf, rfl⟩).elim
    | coe w =>
      have hp' : complexPlaneCoordinates.symm z ∉ physicalPlaneDomain (extendAtInfinity M.function '' G) := by
        simpa only [physicalPlaneDomain, mem_preimage, planeSphere, complexPlaneCoordinates.apply_symm_apply] using hp
      have hq' : planeSphere (complexPlaneCoordinates.symm w) ∈
          connectedComponentIn (extendAtInfinity M.function '' G)ᶜ (planeSphere (complexPlaneCoordinates.symm z)) := by
        simpa only [planeSphere, complexPlaneCoordinates.apply_symm_apply] using hq
      simpa only [finiteCoord_coe, complexPlaneCoordinates.apply_symm_apply] using
        M.height_constant_on_components hinf H.height.continuous
          (heightLimitGradient H.error₀ H.error₁) H.weak_gradient
          (fun r i => (heightLimitWitness H.error₀ H.error₁
            (H.height.continuous.comp complexPlaneCoordinates.continuous) H.weak_gradient r).weakGrad_component_memLp i)
          hHz hp' hq'

 theorem heightSection_continuousAt_end (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ x ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ x = 0)
    {q : Sphere} (hq : q ∈ Gᶜ) (hqinf : q ≠ OnePoint.infty) :
    ContinuousAt (M.heightSection H) q := by
  have hsurj := M.projection_surjective hsard hsch hG hconn hinf hTD
  let p := invFun M.projection q
  have hpq : M.projection p = q := rightInverse_invFun hsurj q
  have hpOut : p ∉ extendAtInfinity M.function '' G := by
    rintro ⟨x, hx, he⟩
    have hpx : M.projection p = x := by rw [← he, M.projection_inverse x hx]
    have heq : x = q := hpx.symm.trans hpq
    exact hq (heq ▸ hx)
  apply (closed_map_section_continuousAt_of_fiber M.projection_closed (invFun M.projection)
    (rightInverse_invFun hsurj) (a := fun z => H.height (finiteCoord z)) (v := H.height (finiteCoord p)) ?_ ?_).1
  · intro z hz
    have hzinf : z ≠ OnePoint.infty := by
      intro he
      have hi : M.projection OnePoint.infty = OnePoint.infty := by
        simpa only [extendAtInfinity_infty] using M.projection_inverse _ hinf
      rw [he, hi] at hz
      exact hqinf hz.symm
    exact H.height.continuous.continuousAt.comp
      ((continuousOn_finiteCoord_of_avoids_infty (S := {OnePoint.infty}ᶜ) (by simp)).continuousAt
        (isClosed_singleton.isOpen_compl.mem_nhds hzinf))
  · intro z hz
    have hzp : z ∈ connectedComponentIn (extendAtInfinity M.function '' G)ᶜ p := by
      rw [← M.projection_fiber hsard hsch hG hconn hinf hTD hpOut]
      exact hz.trans hpq.symm
    exact (M.height_constant_on_sphere_components hinf H hHz hpOut hzp).symm

 theorem heightSection_continuousAt (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ x ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ x = 0)
    {q : Sphere} (hqinf : q ≠ OnePoint.infty) :
    ContinuousAt (M.heightSection H) q := by
  by_cases hq : q ∈ G
  · have hsurj := M.projection_surjective hsard hsch hG hconn hinf hTD
    have hsingle (z : Sphere) (hz : M.projection z = q) :
        z = extendAtInfinity M.function q :=
      (inverse_projection_fiber_on_domain M.projection_inverse M.projection_outside hq).mp hz
    apply (closed_map_section_continuousAt_of_fiber M.projection_closed (invFun M.projection)
      (rightInverse_invFun hsurj) (a := fun z => H.height (finiteCoord z))
      (v := H.height (finiteCoord (extendAtInfinity M.function q))) ?_ ?_).1
    · intro z hz
      have hzinf : z ≠ OnePoint.infty := by
        intro he
        have hi : M.projection OnePoint.infty = OnePoint.infty := by
          simpa only [extendAtInfinity_infty] using M.projection_inverse _ hinf
        rw [he, hi] at hz
        exact hqinf hz.symm
      exact H.height.continuous.continuousAt.comp
        ((continuousOn_finiteCoord_of_avoids_infty (S := {OnePoint.infty}ᶜ) (by simp)).continuousAt
          (isClosed_singleton.isOpen_compl.mem_nhds hzinf))
    · intro z hz
      rw [hsingle z hz]
  · exact M.heightSection_continuousAt_end hsard hsch hG hconn hinf hTD H hHz hq hqinf

 theorem heightSection_plane_continuous (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ x ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ x = 0) :
    Continuous (fun z : ℂ => M.heightSection H (z : Sphere)) := by
  rw [continuous_iff_continuousAt]
  intro z
  exact (M.heightSection_continuousAt hsard hsch hG hconn hinf hTD H hHz
    (OnePoint.coe_ne_infty z)).comp OnePoint.continuous_coe.continuousAt

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ModelFlattenedNeighborhoods
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common open source neighborhoods are constructed for the flattened
old tests and the actual descended height. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem exists_common_flattened_neighborhoods (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (hu : ∀ i, Continuous (u i))
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ p ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ p = 0)
    (b : ℕ → ℂ) (O : Fin m → Set ℝ) (hO : ∀ i, IsOpen (O i))
    (V : Set ℝ) (hV : IsOpen V)
    (hbO : ∀ n i, sphereFromPlaneFunction (u i) (b n : Sphere) ∈ O i)
    (hbV : ∀ n, M.heightSection H (b n : Sphere) ∈ V) :
    ∃ W : ℕ → Set ℂ, (∀ n, IsOpen (W n) ∧ b n ∈ W n) ∧
      (∀ n i, EqOn (fun q : ℂ => flattenValues (O i) (sphereFromPlaneFunction (u i) (q : Sphere)))
        (fun _ => flattenValues (O i) (sphereFromPlaneFunction (u i) (b n : Sphere))) (W n)) ∧
      ∀ n, EqOn (fun q : ℂ => flattenValues V (M.heightSection H (q : Sphere)))
        (fun _ => flattenValues V (M.heightSection H (b n : Sphere))) (W n) := by
  have hUc (i : Fin m) : Continuous (fun q : ℂ => sphereFromPlaneFunction (u i) (q : Sphere)) := by
    simpa only [sphereFromPlaneFunction_coe, Function.comp_def] using (hu i).comp complexPlaneCoordinates.symm.continuous
  have hHc := M.heightSection_plane_continuous hsard hsch hG hconn hinf hTD H hHz
  have hex (n : ℕ) : ∃ W : Set ℂ, IsOpen W ∧ b n ∈ W ∧
      (∀ i, EqOn (fun q : ℂ => flattenValues (O i) (sphereFromPlaneFunction (u i) (q : Sphere)))
        (fun _ => flattenValues (O i) (sphereFromPlaneFunction (u i) (b n : Sphere))) W) ∧
      EqOn (fun q : ℂ => flattenValues V (M.heightSection H (q : Sphere)))
        (fun _ => flattenValues V (M.heightSection H (b n : Sphere))) W := by
    obtain ⟨A, hA, hbA, hconst⟩ := flattened_coordinates_constant_near
      (fun (i : Fin m) (q : ℂ) => sphereFromPlaneFunction (u i) (q : Sphere))
      (fun i => (hUc i).continuousAt) O hO (hbO n)
    obtain ⟨J, hJ, hflat⟩ := flattenValues_locally_constant hV (hbV n)
    have hev : Filter.Eventually (fun q : ℂ => flattenValues V (M.heightSection H (q : Sphere)) =
        flattenValues V (M.heightSection H (b n : Sphere))) (𝓝 (b n)) :=
      (hHc.continuousAt.eventually hJ).mono (fun q hq => hflat hq)
    obtain ⟨C, hCsub, hC, hbC⟩ := mem_nhds_iff.mp hev
    exact ⟨A ∩ C, hA.inter hC, ⟨hbA, hbC⟩,
      fun i q hq => hconst i hq.1, fun q hq => hCsub hq.2⟩
  choose W hW using hex
  exact ⟨W, fun n => ⟨(hW n).1, (hW n).2.1⟩,
    fun n => (hW n).2.2.1, fun n => (hW n).2.2.2⟩

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_NonpointModelEnds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual model has only countably many nonpoint source ends. Its
nontrivial target components are deformed positive-radius round disks,
so every such component has nonempty interior. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem nonpoint_component_interior (M : CompactScalarModel G u)
    (hinf : OnePoint.infty ∈ G) {p : Sphere} (hp : p ∉ extendAtInfinity M.function '' G)
    (hnt : (connectedComponentIn (extendAtInfinity M.function '' G)ᶜ p).Nontrivial) :
    (interior (connectedComponentIn (extendAtInfinity M.function '' G)ᶜ p)).Nonempty := by
  let Ω := extendAtInfinity M.function '' G
  let e := M.deformation.onePointCongr
  have he : e '' M.roundDomain = Ω := M.image_eq.symm
  have hec : e '' M.roundDomainᶜ = Ωᶜ := by rw [e.image_compl, he]
  have hq : e.symm p ∈ M.roundDomainᶜ := by
    intro hh
    apply hp
    change p ∈ Ω
    rw [← he]
    exact ⟨_, hh, e.apply_symm_apply _⟩
  let K := connectedComponentIn M.roundDomainᶜ (e.symm p)
  have hKi : e '' K = connectedComponentIn Ωᶜ p := by
    simpa only [hec, e.apply_symm_apply] using e.image_connectedComponentIn hq
  rcases M.round_circle.2.2 (e.symm p) hq with hsingle | hround
  · obtain ⟨a, ha⟩ := hsingle
    change K = {a} at ha
    have hh : (connectedComponentIn Ωᶜ p).Subsingleton := by
      rw [← hKi, ha, image_singleton]
      exact subsingleton_singleton
    exact (hnt.not_subsingleton hh).elim
  · change IsRoundClosedDisk K at hround
    have hiΩ : OnePoint.infty ∈ Ω := ⟨_, hinf, rfl⟩
    have hiround : OnePoint.infty ∈ M.roundDomain := by
      rw [← he] at hiΩ
      obtain ⟨a, ha, hai⟩ := hiΩ
      have haInf : a = OnePoint.infty := by
        apply e.injective
        exact hai
      rwa [haInf] at ha
    have hiK : OnePoint.infty ∉ K := by
      intro hh
      exact (connectedComponentIn_subset _ _ hh) hiround
    obtain ⟨c, r, hr, hK⟩ := isRoundClosedDisk_eq_euclidean hround hiK
    let V := e '' (((↑) : ℂ → Sphere) '' Metric.ball c r)
    have hV : IsOpen V := e.isOpenMap _ (OnePoint.isOpen_image_coe.mpr Metric.isOpen_ball)
    have hsub : V ⊆ connectedComponentIn Ωᶜ p := by
      rw [← hKi, hK]
      exact image_mono (image_mono Metric.ball_subset_closedBall)
    exact ⟨e (c : Sphere), interior_maximal hsub hV
      ⟨(c : Sphere), ⟨c, Metric.mem_ball_self hr, rfl⟩, rfl⟩⟩

 theorem countable_nonpoint_source_ends (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ) :
    {q : Sphere | q ∈ Gᶜ ∧ (M.projection ⁻¹' {q}).Nontrivial}.Countable := by
  classical
  let Ω := extendAtInfinity M.function '' G
  let value : Set Sphere → Sphere := fun K =>
    if h : K.Nonempty then M.projection h.choose else OnePoint.infty
  apply ((countable_complementaryComponents_with_interior Ω).image value).mono
  intro q hq
  obtain ⟨p, hp⟩ := hq.2.nonempty
  have hpq : M.projection p = q := hp
  have hpOut : p ∉ Ω := by
    rintro ⟨x, hx, rfl⟩
    exact hq.1 (by rw [← hpq, M.projection_inverse x hx]; exact hx)
  let K := connectedComponentIn Ωᶜ p
  have hK : K.Nonempty := ⟨p, mem_connectedComponentIn hpOut⟩
  have hfiber : M.projection ⁻¹' {q} = K := by
    rw [← hpq]
    exact M.projection_fiber hsard hsch hG hconn hinf hTD hpOut
  have hnt : K.Nontrivial := hfiber ▸ hq.2
  refine ⟨K, ⟨⟨p, hpOut, rfl⟩, M.nonpoint_component_interior hinf hpOut hnt⟩, ?_⟩
  change (if h : K.Nonempty then M.projection h.choose else OnePoint.infty) = q
  rw [dite_eq_left hK]
  have hh : hK.choose ∈ M.projection ⁻¹' {q} := hfiber.symm ▸ hK.choose_spec
  exact hh

 theorem exists_enumerated_source_ends (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (hne : {q : ℂ | (q : Sphere) ∉ G}.Nonempty) :
    ∃ b : ℕ → ℂ, (∀ n, (b n : Sphere) ∉ G) ∧
      ∀ q : ℂ, (q : Sphere) ∉ G → (M.projection ⁻¹' {(q : Sphere)}).Nontrivial →
        ∃ n, b n = q := by
  let S := {q : ℂ | (q : Sphere) ∉ G ∧ (M.projection ⁻¹' {(q : Sphere)}).Nontrivial}
  have hS : S.Countable := by
    apply ((M.countable_nonpoint_source_ends hsard hsch hG hconn hinf hTD).image finiteCoord).mono
    intro q hq
    exact ⟨(q : Sphere), hq, finiteCoord_coe q⟩
  obtain ⟨q₀, hq₀⟩ := hne
  let b := enumerateCountable hS q₀
  refine ⟨b, ?_, ?_⟩
  · intro n
    have hb := range_enumerateCountable_subset hS q₀ (mem_range_self n)
    rcases hb with he | he
    · simpa only [b, he, mem_ofPred_eq] using hq₀
    · exact he.1
  · intro q hq hnt
    exact subset_range_enumerate hS q₀ ⟨hq, hnt⟩

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelPriorityData
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual countable ends, selected target points and a common horizontal
bound for priority interpolation. The enumeration may repeat a harmless
point end when the nonpoint family is finite or empty. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem exists_priority_source_data (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (hB : IsCompact {q : ℂ | (q : Sphere) ∉ G})
    (hne : {q : ℂ | (q : Sphere) ∉ G}.Nonempty) :
    ∃ (b : ℕ → ℂ) (z : ℕ → Sphere) (K : ℝ),
      0 ≤ K ∧ (∀ n, (b n : Sphere) ∉ G) ∧
      (∀ n, M.projection (z n) = (b n : Sphere)) ∧
      (∀ n, ‖(finiteCoord (z n)).re‖ ≤ K) ∧
      (∀ q : ℂ, (q : Sphere) ∉ G → (M.projection ⁻¹' {(q : Sphere)}).Nontrivial →
        ∃ n, b n = q) := by
  obtain ⟨b, hb, hc⟩ := M.exists_enumerated_source_ends hsard hsch hG hconn hinf hTD hne
  let z := fun n => invFun M.projection (b n : Sphere)
  have hz (n : ℕ) : M.projection (z n) = (b n : Sphere) :=
    rightInverse_invFun (M.projection_surjective hsard hsch hG hconn hinf hTD) _
  obtain ⟨K, hK, hbound⟩ := M.projection_bounded_lifts hinf hB
  refine ⟨b, z, K, hK, hb, hz, ?_, hc⟩
  intro n
  apply (show ‖(finiteCoord (z n)).re‖ ≤ ‖finiteCoord (z n)‖ by
    simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (finiteCoord (z n))).trans
  apply hbound
  rw [hz n]
  exact ⟨b n, hb n, rfl⟩

end CompactScalarModel
end CircleDomainRigidity

end

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
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PriorityLocalDerivative
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The countable horizontal interpolation has the finite derivative
bound at every point where the tail cutoffs vanish on a neighborhood. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem priorityList_derivative_cost (χ : ℕ → E → ℝ) (c : ℕ → ℝ) (N : ℕ) (p : E) :
    ((priorityList χ c N).map (fun e => ‖fderiv ℝ e.1 p‖)).sum =
      ∑ n ∈ Finset.range N, ‖fderiv ℝ (χ n) p‖ := by
  induction N with
  | zero => simp [priorityList]
  | succ N ih => simp only [priorityList_succ, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      ih, Finset.sum_range_succ]

 theorem priorityInfiniteValue_local_derivative
    (χ : ℕ → E → ℝ) (c : ℕ → ℝ) (X : E → ℝ) {p : E} {B : ℝ}
    (hX : DifferentiableAt ℝ X p) (hXb : ‖X p‖ ≤ B)
    (hχ : ∀ n, DifferentiableAt ℝ (χ n) p ∧ χ n p ∈ Icc (0 : ℝ) 1)
    (hc : ∀ n, ‖c n‖ ≤ B)
    (hs : Summable (fun n => ‖fderiv ℝ (χ n) p‖))
    (hz : ∃ N : ℕ, ∀ᶠ q in 𝓝 p, ∀ n, N ≤ n → χ n q = 0) :
    DifferentiableAt ℝ (fun q => priorityInfiniteValue (fun n => χ n q) c (X q)) p ∧
    ‖fderiv ℝ (fun q => priorityInfiniteValue (fun n => χ n q) c (X q)) p-
        (1-∑' n, priorityWeight (fun j => χ j p) n) • fderiv ℝ X p‖ ≤
      2*B*(∑' n, ‖fderiv ℝ (χ n) p‖) := by
  obtain ⟨N, hz⟩ := hz
  have hpz : ∀ n, N ≤ n → χ n p = 0 := mem_of_mem_nhds hz
  have hlocal : (fun q => priorityInfiniteValue (fun n => χ n q) c (X q)) =ᶠ[𝓝 p]
      priorityBlend (priorityList χ c N) X := by
    filter_upwards [hz] with q hq
    exact priorityInfiniteValue_eq_finite c X hq
  have hL (e) (he : e ∈ priorityList χ c N) :
      DifferentiableAt ℝ e.1 p ∧ e.1 p ∈ Icc (0 : ℝ) 1 ∧ ‖e.2‖ ≤ B := by
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp he
    exact ⟨(hχ n).1, (hχ n).2, hc n⟩
  have hfd := priorityBlend_differentiableAt hX (fun e he => (hL e he).1)
  refine ⟨hfd.congr_of_eventuallyEq hlocal, ?_⟩
  have hcoef : 1-∑' n, priorityWeight (fun j => χ j p) n =
      priorityResidual (priorityList χ c N) p := by
    have hw : (∑' n, priorityWeight (fun j => χ j p) n) =
        ∑ n ∈ Finset.range N, priorityWeight (fun j => χ j p) n := by
      apply tsum_eq_sum
      intro n hn
      rw [priorityWeight, hpz n (by simpa only [Finset.mem_range, not_lt] using hn), zero_mul]
    rw [hw, priorityWeight_sum, priorityList_residual]
    ring
  rw [hlocal.fderiv_eq, hcoef]
  have hfinite := priorityBlend_derivative_bound hX hXb hL
  rw [priorityList_derivative_cost] at hfinite
  apply hfinite.trans
  apply mul_le_mul_of_nonneg_left (hs.sum_le_tsum (Finset.range N) (fun n _ => norm_nonneg _))
  linarith [norm_nonneg (X p)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PriorityDerivativeError
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The horizontal interpolation differs from the original derivative
only by its cutoff-gradient error and the original gradient on the union
of cutoff supports. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem priorityInfiniteValue_derivative_error
    (χ : ℕ → E → ℝ) (c : ℕ → ℝ) (X : E → ℝ) {p : E} {B : ℝ}
    (hX : DifferentiableAt ℝ X p) (hXb : ‖X p‖ ≤ B)
    (hχ : ∀ n, DifferentiableAt ℝ (χ n) p ∧ χ n p ∈ Icc (0 : ℝ) 1)
    (hc : ∀ n, ‖c n‖ ≤ B)
    (hs : Summable (fun n => ‖fderiv ℝ (χ n) p‖))
    (hz : ∃ N : ℕ, ∀ᶠ q in 𝓝 p, ∀ n, N ≤ n → χ n q = 0) :
    ‖fderiv ℝ (fun q => priorityInfiniteValue (fun n => χ n q) c (X q)) p -
      fderiv ℝ X p‖ ≤
      2*B*(∑' n, ‖fderiv ℝ (χ n) p‖) +
        (⋃ n, support (χ n)).indicator (fun q => ‖fderiv ℝ X q‖) p := by
  classical
  let a : ℝ := ∑' n, priorityWeight (fun j => χ j p) n
  have ha := priorityWeight_tsum_mem_unit (fun n => (hχ n).2)
  have hbound := (priorityInfiniteValue_local_derivative χ c X hX hXb hχ hc hs hz).2
  let D := fderiv ℝ (fun q => priorityInfiniteValue (fun n => χ n q) c (X q)) p
  let V := fderiv ℝ X p
  have he : D-V = (D-(1-a) • V) + (-a) • V := by module
  have hnorm : ‖D-V‖ ≤ ‖D-(1-a) • V‖ + a*‖V‖ := by
    rw [he]
    apply (norm_add_le _ _).trans_eq
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg ha.1]
  have hrem : a*‖V‖ ≤ (⋃ n, support (χ n)).indicator (fun q => ‖fderiv ℝ X q‖) p := by
    by_cases hp : p ∈ ⋃ n, support (χ n)
    · rw [indicator_of_mem hp]
      exact (mul_le_mul_of_nonneg_right ha.2 (norm_nonneg V)).trans_eq (one_mul _)
    · have hpz (n : ℕ) : χ n p = 0 := by
        by_contra hn
        exact hp (mem_iUnion.mpr ⟨n, hn⟩)
      have haz : a = 0 := by
        simp only [a, priorityWeight, hpz, zero_mul, tsum_zero]
      rw [haz, zero_mul, indicator_of_notMem hp]
  exact hnorm.trans (add_le_add hbound hrem)

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
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PriorityL2Error
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source L2 error of priority interpolation is bounded by the
summable cutoff gradient and the original gradient on the changed set. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem cutoff_gradient_summable_of_local_tail
    {χ : ℕ → ℂ → ℝ} {p : ℂ}
    (hz : ∃ N : ℕ, ∀ᶠ q in 𝓝 p, ∀ n, N ≤ n → χ n q = 0) :
    Summable (fun n => ‖fderiv ℝ (χ n) p‖) := by
  obtain ⟨N, hN⟩ := hz
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro n hn
  have he : χ n =ᶠ[𝓝 p] (fun _ => 0) :=
    hN.mono (fun q hq => hq n (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hn)))
  rw [he.fderiv_eq]
  simp

 theorem priority_source_L2_error
    {B U : Set ℂ} (hB : IsClosed B) (hU : IsOpen U) (hUB : U ⊆ Bᶜ)
    (b : ℕ → ℂ) (hb : ∀ n, b n ∈ B) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (χ : ℕ → ℂ → ℝ) (hχ : ∀ n, ContDiff ℝ ∞ (χ n))
    (hunit : ∀ n z, χ n z ∈ Icc (0 : ℝ) 1)
    (hs : ∀ n, support (χ n) ⊆ ball (b n) (r n))
    (c : ℕ → ℝ) (X : ℂ → ℝ) (hX : ContDiffOn ℝ ∞ X Bᶜ)
    {K : ℝ} (hK : 0 ≤ K) (hc : ∀ n, ‖c n‖ ≤ K) (hXb : ∀ z ∈ U, ‖X z‖ ≤ K)
    (hDX : MemLp (fderiv ℝ X) 2 (volume.restrict U))
    (hA : MemLp (fun z => ∑' n, ‖fderiv ℝ (χ n) z‖) 2 volume) :
    let P := fun z => priorityInfiniteValue (fun n => χ n z) c (X z)
    let S := ⋃ n, support (χ n)
    MemLp (fun z => fderiv ℝ P z-fderiv ℝ X z) 2 (volume.restrict U) ∧
      (eLpNorm (fun z => fderiv ℝ P z-fderiv ℝ X z) 2 (volume.restrict U)).toReal ≤
        2*K*(eLpNorm (fun z => ∑' n, ‖fderiv ℝ (χ n) z‖) 2 (volume.restrict U)).toReal +
          (eLpNorm (S.indicator (fun z => ‖fderiv ℝ X z‖)) 2 (volume.restrict U)).toReal := by
  let P := fun z => priorityInfiniteValue (fun n => χ n z) c (X z)
  let S := ⋃ n, support (χ n)
  have hPs : ContDiffOn ℝ ∞ P U :=
    (priorityInfiniteValue_smooth_off_dust hB b hb r hr χ hχ hs c X hX).mono hUB
  have hXs := hX.mono hUB
  have hD : AEStronglyMeasurable (fun z => fderiv ℝ P z-fderiv ℝ X z) (volume.restrict U) :=
    ((hPs.continuousOn_fderiv_of_isOpen hU (by simp)).sub
      (hXs.continuousOn_fderiv_of_isOpen hU (by simp))).aestronglyMeasurable hU.measurableSet
  have hS : MeasurableSet S :=
    MeasurableSet.iUnion (fun n => ((hχ n).continuous.isOpen_preimage _ isOpen_ne).measurableSet)
  apply l2_norm_le_of_additive_majorant (by positivity) hD (hA.restrict U) (hDX.norm.indicator hS)
  · exact Eventually.of_forall (fun z => tsum_nonneg (fun n => norm_nonneg _))
  · exact Eventually.of_forall (fun z => indicator_nonneg (fun _ _ => norm_nonneg _) z)
  · filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    obtain ⟨V, hV, hzV, N, hN⟩ := concentrated_cutoffs_eventually_zero hB b hb r hr χ hs (hUB hz)
    have htail : ∃ N : ℕ, ∀ᶠ q in 𝓝 z, ∀ n, N ≤ n → χ n q = 0 :=
      ⟨N, Filter.mem_of_superset (hV.mem_nhds hzV) (fun q hq n hn => hN n hn q hq)⟩
    exact priorityInfiniteValue_derivative_error χ c X
      ((hXs.contDiffAt (hU.mem_nhds hz)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hXb z hz)
      (fun n => ⟨(hχ n).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z, hunit n z⟩) hc
      (cutoff_gradient_summable_of_local_tail htail) htail

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CountableEnergyNeighborhoods
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countably many source points admit shrinking prescribed neighborhoods
whose union has arbitrarily small mass for an atomless finite energy measure. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_shrinking_energy_balls
    (μ : Measure ℂ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (c : ℕ → ℂ) (O : ℕ → Set ℂ) (hO : ∀ n, O n ∈ 𝓝 (c n))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧ Tendsto r atTop (𝓝 0) ∧
      (∀ n, ball (c n) (r n) ⊆ O n) ∧ μ (⋃ n, ball (c n) (r n)) < ε := by
  have hcount : (range c).Countable := countable_range c
  obtain ⟨V, hCV, hV, hμV⟩ := (range c).exists_isOpen_lt_of_lt (μ := μ) ε
    (by rw [hcount.measure_zero μ]; exact hε)
  have hballs (n : ℕ) : ∃ s : ℝ, 0 < s ∧ ball (c n) s ⊆ O n ∩ V :=
    Metric.mem_nhds_iff.mp (Filter.inter_mem (hO n) (hV.mem_nhds (hCV (mem_range_self n))))
  choose s hs hsub using hballs
  let r : ℕ → ℝ := fun n => min (s n) ((n : ℝ)+1)⁻¹
  refine ⟨r, (fun n => lt_min (hs n) (by positivity)), ?_, ?_, ?_⟩
  · apply squeeze_zero (fun n => (le_min (hs n).le (by positivity)))
      (fun n => min_le_right _ _) ?_
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · intro n
    exact (ball_subset_ball (min_le_left _ _)).trans ((hsub n).trans inter_subset_left)
  · apply (measure_mono (iUnion_subset (fun n => ?_))).trans_lt hμV
    exact (ball_subset_ball (min_le_left _ _)).trans ((hsub n).trans inter_subset_right)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PriorityCutoffSelection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous source selection: shrinking supports have small total
weighted mass, while their smooth cutoff gradients have a prescribed
summable budget. Overlap of the supports is allowed. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_priority_cutoffs
    {E : Set ℂ} {g : ℂ → ℝ} (hg : MemLp g 2 (volume.restrict E))
    (c : ℕ → ℂ) (O : ℕ → Set ℂ) (hO : ∀ n, O n ∈ 𝓝 (c n))
    {δ : ℝ≥0∞} (hδ : 0 < δ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hsum : Summable ε) :
    ∃ (r : ℕ → ℝ) (χ : ℕ → ℂ → ℝ),
      (∀ n, 0 < r n) ∧ Tendsto r atTop (𝓝 0) ∧
      (∀ n, ball (c n) (r n) ⊆ O n) ∧
      (∫⁻ z in ⋃ n, ball (c n) (r n), ENNReal.ofReal (g z^2) ∂volume.restrict E) < δ ∧
      (∀ n, ContDiff ℝ (↑(⊤ : ℕ∞)) (χ n) ∧ HasCompactSupport (χ n) ∧
        tsupport (χ n) ⊆ ball (c n) (r n) ∧ (∀ z, χ n z ∈ Icc (0 : ℝ) 1) ∧
        (∀ᶠ z in 𝓝 (c n), χ n z = 1)) ∧
      MemLp (fun z => ∑' n, ‖fderiv ℝ (χ n) z‖) 2 volume ∧
      (eLpNorm (fun z => ∑' n, ‖fderiv ℝ (χ n) z‖) 2 volume).toReal ≤ ∑' n, ε n := by
  let μ := (volume.restrict E).withDensity (fun z => ENNReal.ofReal (g z^2))
  have hfin : (∫⁻ z, ENNReal.ofReal (g z^2) ∂volume.restrict E) < ∞ := by
    simpa only [hasFiniteIntegral_iff_enorm, Real.enorm_eq_ofReal_abs, abs_sq] using
      hg.integrable_sq.hasFiniteIntegral
  let : IsFiniteMeasure μ := isFiniteMeasure_withDensity hfin.ne
  obtain ⟨r, hr, hrt, hsub, hmass⟩ := exists_shrinking_energy_balls μ c O hO hδ
  obtain ⟨χ, hχ, hnorm, hnormsum, _⟩ := exists_summable_energy_cutoffs c r hr ε hε hsum
  have hM (n : ℕ) := (hχ n).2.2.2.2.2.1
  have hnorm' : Summable (fun n => (eLpNorm (fun z => ‖fderiv ℝ (χ n) z‖) 2 volume).toReal) := by
    simpa only [eLpNorm_norm _] using hnorm
  obtain ⟨hmajorant, hmajorantNorm⟩ := l2_tsum_of_summable_norms
    (fun n z => ‖fderiv ℝ (χ n) z‖) (fun n => (hM n).norm) hnorm'
  refine ⟨r, χ, hr, hrt, hsub, ?_, ?_, hmajorant, ?_⟩
  · dsimp only [μ] at hmass
    rwa [withDensity_apply _ (isOpen_iUnion (fun _ => isOpen_ball)).measurableSet] at hmass
  · intro n
    exact ⟨(hχ n).1, (hχ n).2.1, (hχ n).2.2.1, (hχ n).2.2.2.1, (hχ n).2.2.2.2.1⟩
  · apply hmajorantNorm.trans
    simpa only [eLpNorm_norm _] using hnormsum

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PrioritySupportEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retain the small energy of the altered support, as required by the
third term in the actual saved-barrier estimate. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_priority_L2_approximation_with_support
    {B U : Set ℂ} (hB : IsClosed B) (hU : IsOpen U) (hUB : U ⊆ Bᶜ)
    (b : ℕ → ℂ) (hb : ∀ n, b n ∈ B)
    (O : ℕ → Set ℂ) (hO : ∀ n, O n ∈ 𝓝 (b n))
    (c : ℕ → ℝ) (X : ℂ → ℝ) (hX : ContDiffOn ℝ ∞ X Bᶜ)
    {K : ℝ} (hK : 0 ≤ K) (hc : ∀ n, ‖c n‖ ≤ K) (hXb : ∀ z ∈ U, ‖X z‖ ≤ K)
    (hDX : MemLp (fderiv ℝ X) 2 (volume.restrict U))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℕ → ℝ) (χ : ℕ → ℂ → ℝ),
      (∀ n, 0 < r n) ∧ Tendsto r atTop (𝓝 0) ∧
      (∀ n, ball (b n) (r n) ⊆ O n) ∧
      (∀ n, ContDiff ℝ ∞ (χ n) ∧ HasCompactSupport (χ n) ∧
        tsupport (χ n) ⊆ ball (b n) (r n) ∧ (∀ z, χ n z ∈ Icc (0 : ℝ) 1) ∧
        (∀ᶠ z in 𝓝 (b n), χ n z = 1)) ∧
      let P := fun z => priorityInfiniteValue (fun n => χ n z) c (X z)
      MemLp (fun z => fderiv ℝ P z-fderiv ℝ X z) 2 (volume.restrict U) ∧
        (eLpNorm (fun z => fderiv ℝ P z-fderiv ℝ X z) 2 (volume.restrict U)).toReal < ε ∧
        (eLpNorm ((⋃ n, support (χ n)).indicator (fun z => ‖fderiv ℝ X z‖))
          2 (volume.restrict U)).toReal < ε := by
  let τ := ε/(2*(2*K+1))
  have hτ : 0 < τ := div_pos hε (by positivity)
  let a : ℕ → ℝ := fun n => τ/2/2^n
  have ha : ∀ n, 0 < a n := fun n => by dsimp [a] <;> positivity
  have has : HasSum a τ := hasSum_geometric_two' τ
  obtain ⟨r, χ, hr, hrt, hrO, hmass, hχ, hA, hAnorm⟩ :=
    exists_priority_cutoffs hDX.norm b O hO
      (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hτ)) a ha has.summable
  have hs (n : ℕ) : support (χ n) ⊆ ball (b n) (r n) :=
    (subset_tsupport (χ n)).trans (hχ n).2.2.1
  have hχs (n : ℕ) : ContDiff ℝ ∞ (χ n) := (hχ n).1
  have hχu (n : ℕ) (z : ℂ) : χ n z ∈ Icc (0 : ℝ) 1 := (hχ n).2.2.2.1 z
  obtain ⟨hP, hPn⟩ := priority_source_L2_error hB hU hUB b hb r hrt χ hχs hχu hs
    c X hX hK hc hXb hDX hA
  have hAn : (eLpNorm (fun z => ∑' n, ‖fderiv ℝ (χ n) z‖) 2 (volume.restrict U)).toReal ≤ τ := by
    apply (ENNReal.toReal_mono hA.eLpNorm_ne_top
      (eLpNorm_mono_measure _ Measure.restrict_le_self)).trans
    simpa only [has.tsum_eq] using hAnorm
  let S := ⋃ n, support (χ n)
  have hS : MeasurableSet S := MeasurableSet.iUnion (fun n =>
    ((hχs n).continuous.isOpen_preimage _ isOpen_ne).measurableSet)
  have hSE : S ⊆ ⋃ n, ball (b n) (r n) := iUnion_mono hs
  have hI : (eLpNorm (S.indicator (fun z => ‖fderiv ℝ X z‖)) 2 (volume.restrict U)).toReal < τ := by
    apply indicator_L2_norm_lt_of_energy_lt hDX.norm hS hτ
    exact (lintegral_mono_set hSE).trans_lt hmass
  refine ⟨r, χ, hr, hrt, hrO, hχ, hP, ?_, ?_⟩
  swap
  · exact hI.trans_le (div_le_self hε.le (by nlinarith))
  have hnum : (2*K+1)*τ = ε/2 := by
    dsimp [τ]
    have hden : 2*K+1 ≠ 0 := ne_of_gt (by linarith)
    field_simp [hden]
  calc
    _ ≤ 2*K*(eLpNorm (fun z => ∑' n, ‖fderiv ℝ (χ n) z‖) 2 (volume.restrict U)).toReal +
        (eLpNorm (S.indicator (fun z => ‖fderiv ℝ X z‖)) 2 (volume.restrict U)).toReal := hPn
    _ < 2*K*τ+τ := add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hAn (by positivity)) hI
    _ = (2*K+1)*τ := by ring
    _ = ε/2 := hnum
    _ < ε := by linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ChartFiberConcentration
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concentrating Euclidean supports control selected values through a
closed sphere projection. No comparison of chart and sphere metrics is
needed. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem concentrated_fiber_values_in_chart
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [PseudoMetricSpace Z]
    {P : X → Y} (hP : IsClosedMap P) (e : Z → Y) (he : Continuous e)
    {p : X} {q : Z} (_hpq : P p = e q) (hfiber : P ⁻¹' {e q} = {p})
    {a : X → ℝ} (ha : ContinuousAt a p)
    (z : ℕ → X) (b : ℕ → Z) (hz : ∀ n, P (z n) = e (b n))
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (χ : ℕ → Z → ℝ) (hs : ∀ n, support (χ n) ⊆ ball (b n) (r n)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ᶠ y in 𝓝 q,
      ∀ n, N ≤ n → χ n y ≠ 0 → ‖a (z n)-a p‖ ≤ ε := by
  intro ε hε
  obtain ⟨U, hUnear, hU, hpU⟩ := mem_nhds_iff.mp
    (ha.preimage_mem_nhds (ball_mem_nhds _ hε))
  have hV : IsOpen (kernImage P U) := isClosedMap_iff_kernImage.mp hP hU
  have hqV : e q ∈ kernImage P U := by
    intro x hx
    have hx' : x ∈ P ⁻¹' {e q} := hx
    rw [hfiber, mem_singleton_iff] at hx'
    exact hx' ▸ hpU
  have hpre : e ⁻¹' kernImage P U ∈ 𝓝 q :=
    (hV.preimage he).mem_nhds hqV
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hr.eventually (gt_mem_nhds (show 0 < δ/2 by linarith)))
  refine ⟨N, ?_⟩
  filter_upwards [ball_mem_nhds q (show 0 < δ/2 by linarith)] with y hy
  intro n hn hχ
  have hb : b n ∈ ball q δ := by
    calc
      dist (b n) q ≤ dist (b n) y+dist y q := dist_triangle _ _ _
      _ < δ/2+δ/2 := add_lt_add (by simpa only [dist_comm] using (hs n hχ).trans (hN n hn)) hy
      _ = δ := by ring
  have hzU : z n ∈ U := hball hb (hz n)
  exact (show ‖a (z n)-a p‖ < ε by
    simpa only [mem_preimage, mem_ball, dist_eq_norm] using hUnear hzU).le

 theorem priority_continuousAt_singleton_fiber_in_chart
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [PseudoMetricSpace Z]
    {P : X → Y} (hP : IsClosedMap P) (e : Z → Y) (he : Continuous e)
    {p : X} {q : Z} (hpq : P p = e q) (hfiber : P ⁻¹' {e q} = {p})
    {a : X → ℝ} (ha : ContinuousAt a p)
    (z : ℕ → X) (b : ℕ → Z) (hz : ∀ n, P (z n) = e (b n))
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (χ : ℕ → Z → ℝ) (hs : ∀ n, support (χ n) ⊆ ball (b n) (r n))
    (hχc : ∀ n, ContinuousAt (χ n) q) (hχ : ∀ y n, χ n y ∈ Icc (0 : ℝ) 1)
    {K : ℝ} (hb : ∀ n, ‖a (z n)‖ ≤ K) {x : Z → ℝ}
    (hx : ContinuousAt x q) (hxq : x q = a p) :
    ContinuousAt (fun y => priorityInfiniteValue (fun n => χ n y) (fun n => a (z n)) (x y)) q := by
  apply priorityInfiniteValue_continuousAt_point_trace χ (fun n => a (z n)) x hχc hχ hb hx
  rw [hxq]
  exact concentrated_fiber_values_in_chart hP e he hpq hfiber ha z b hz r hr χ hs

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelPriorityContinuity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual priority horizontal coordinate is continuous on the full
finite source plane. Nonpoint ends use a terminating cutoff, and singleton
fibers use the closed projection and shrinking Euclidean supports. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem priority_horizontal_plane_continuous (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (z : ℕ → Sphere) (b : ℕ → ℂ) (hz : ∀ n, M.projection (z n) = (b n : Sphere))
    (hcover : ∀ q : ℂ, (q : Sphere) ∉ G → (M.projection ⁻¹' {(q : Sphere)}).Nontrivial →
      ∃ n, b n = q)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (χ : ℕ → ℂ → ℝ) (hχc : ∀ n, Continuous (χ n))
    (hs : ∀ n, support (χ n) ⊆ ball (b n) (r n))
    (hχ : ∀ q n, χ n q ∈ Icc (0 : ℝ) 1)
    (hone : ∀ n, ∀ᶠ q in 𝓝 (b n), χ n q = 1)
    {K : ℝ} (hb : ∀ n, ‖(finiteCoord (z n)).re‖ ≤ K) :
    Continuous (fun q : ℂ => priorityInfiniteValue (fun n => χ n q)
      (fun n => (finiteCoord (z n)).re) (M.horizontalSection (q : Sphere))) := by
  have hsurj := M.projection_surjective hsard hsch hG hconn hinf hTD
  rw [continuous_iff_continuousAt]
  intro q
  by_cases hnt : (M.projection ⁻¹' {(q : Sphere)}).Nontrivial
  · have hq : (q : Sphere) ∉ G := by
      intro hq
      have hsub : (M.projection ⁻¹' {(q : Sphere)}).Subsingleton := by
        intro x hx y hy
        exact ((inverse_projection_fiber_on_domain M.projection_inverse M.projection_outside hq).mp hx).trans
          ((inverse_projection_fiber_on_domain M.projection_inverse M.projection_outside hq).mp hy).symm
      exact hnt.not_subsingleton hsub
    obtain ⟨n, hn⟩ := hcover q hq hnt
    apply priorityInfiniteValue_continuousAt_of_one (fun n => (hχc n).continuousAt)
      (fun n => (finiteCoord (z n)).re) (fun q => M.horizontalSection (q : Sphere))
    simpa only [hn] using hone n
  · let p := invFun M.projection (q : Sphere)
    have hpq : M.projection p = (q : Sphere) := rightInverse_invFun hsurj _
    have hfiber : M.projection ⁻¹' {(q : Sphere)} = {p} := by
      ext x
      constructor
      · intro hx
        by_contra hxp
        exact hnt ⟨x, hx, p, hpq, hxp⟩
      · rintro rfl
        exact hpq
    have hpinf : p ≠ OnePoint.infty := by
      intro he
      have hi : M.projection OnePoint.infty = OnePoint.infty := by
        simpa only [extendAtInfinity_infty] using M.projection_inverse _ hinf
      rw [he, hi] at hpq
      exact OnePoint.coe_ne_infty q hpq.symm
    have ha : ContinuousAt (fun p : Sphere => (finiteCoord p).re) p :=
      Complex.continuous_re.continuousAt.comp
        ((continuousOn_finiteCoord_of_avoids_infty (S := {OnePoint.infty}ᶜ) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousAt
          (isClosed_singleton.isOpen_compl.mem_nhds hpinf))
    have hfp : M.projection ⁻¹' {M.projection p} = {p} := by rwa [hpq]
    have hx : ContinuousAt (fun q : ℂ => M.horizontalSection (q : Sphere)) q := by
      have hh := closed_map_section_value_continuousAt M.projection_closed hfp ha
        (invFun M.projection) (rightInverse_invFun hsurj)
      rw [hpq] at hh
      exact hh.comp OnePoint.continuous_coe.continuousAt
    exact priority_continuousAt_singleton_fiber_in_chart M.projection_closed
      ((↑) : ℂ → Sphere) OnePoint.continuous_coe hpq hfiber ha z b hz r hr χ hs
      (fun n => (hχc n).continuousAt) hχ hb hx rfl

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelPrioritySupport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual horizontal priority selection retains both its gradient
error and the energy of the altered support for the barrier estimate. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem exists_horizontal_priority_with_support (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (b : ℕ → ℂ) (hb : ∀ n, (b n : Sphere) ∉ G)
    (z : ℕ → Sphere) (hz : ∀ n, M.projection (z n) = (b n : Sphere))
    (hcover : ∀ q : ℂ, (q : Sphere) ∉ G → (M.projection ⁻¹' {(q : Sphere)}).Nontrivial →
      ∃ n, b n = q)
    {K : ℝ} (hc : ∀ n, ‖(finiteCoord (z n)).re‖ ≤ K)
    (W : ℕ → Set ℂ) (hW : ∀ n, W n ∈ 𝓝 (b n))
    (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℕ → ℝ) (χ : ℕ → ℂ → ℝ),
      (∀ n, 0 < r n) ∧ Tendsto r atTop (𝓝 0) ∧
      (∀ n, ball (b n) (r n) ⊆ W n) ∧
      (∀ n, ContDiff ℝ ∞ (χ n) ∧ HasCompactSupport (χ n) ∧
        tsupport (χ n) ⊆ ball (b n) (r n) ∧ (∀ q, χ n q ∈ Icc (0 : ℝ) 1) ∧
        (∀ᶠ q in 𝓝 (b n), χ n q = 1)) ∧
      let X := fun q : ℂ => M.horizontalSection (q : Sphere)
      let P := fun q => priorityInfiniteValue (fun n => χ n q) (fun n => (finiteCoord (z n)).re) (X q)
      Continuous P ∧
      MemLp (fun q => fderiv ℝ P q-fderiv ℝ X q) 2
        (volume.restrict ({q : ℂ | (q : Sphere) ∈ G} ∩ ball 0 R)) ∧
      (eLpNorm (fun q => fderiv ℝ P q-fderiv ℝ X q) 2
        (volume.restrict ({q : ℂ | (q : Sphere) ∈ G} ∩ ball 0 R))).toReal < ε ∧
      (eLpNorm ((⋃ n, support (χ n)).indicator (fun q => ‖fderiv ℝ X q‖)) 2
        (volume.restrict ({q : ℂ | (q : Sphere) ∈ G} ∩ ball 0 R))).toReal < ε := by
  let D := {q : ℂ | (q : Sphere) ∈ G}
  let B := Dᶜ
  let X := fun q : ℂ => M.horizontalSection (q : Sphere)
  have hD : IsOpen D := hG.preimage OnePoint.continuous_coe
  obtain ⟨A, hA, hbound⟩ := M.function_bounded_on_source_ball hinf R
  let L := max K A
  have hL : 0 ≤ L := hA.trans (le_max_right _ _)
  have hX : ContDiffOn ℝ ∞ X Bᶜ := by
    simpa only [B, compl_compl] using M.horizontalSection_plane_smooth hG
  have hXb : ∀ q ∈ D ∩ ball 0 R, ‖X q‖ ≤ L := by
    intro q hq
    have he : X q = (M.function q).re := by
      simpa only [X, extendAtInfinity_coe, finiteCoord_coe] using M.horizontalSection_on_domain hq.1
    rw [he]
    exact (show ‖(M.function q).re‖ ≤ ‖M.function q‖ by
      simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (M.function q)).trans
      ((hbound q hq.1 hq.2).trans (le_max_right _ _))
  obtain ⟨r, χ, hr, hrt, hrW, hχ, hLp, he, hsupport⟩ := exists_priority_L2_approximation_with_support
    hD.isClosed_compl (hD.inter isOpen_ball) (by simpa only [B, compl_compl] using (inter_subset_left : D ∩ ball 0 R ⊆ D))
    b hb W hW (fun n => (finiteCoord (z n)).re) X hX hL
    (fun n => (hc n).trans (le_max_left _ _)) hXb
    (M.horizontalSection_plane_memLp hG hinf R) hε
  refine ⟨r, χ, hr, hrt, hrW, hχ, ?_, hLp, he, hsupport⟩
  exact M.priority_horizontal_plane_continuous hsard hsch hG hconn hinf hTD z b hz hcover r hrt χ
    (fun n => (hχ n).1.continuous)
    (fun n => (subset_tsupport (χ n)).trans (hχ n).2.2.1)
    (fun q n => (hχ n).2.2.2.1 q) (fun n => (hχ n).2.2.2.2) hc

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
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CompactCutoffEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.horizontalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative global energy for a compact cutoff of a local Sobolev
error. This applies to the flattened height minus the vertical coordinate. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem compact_cutoff_energy_bound {U : Set EuclideanPlane} (hU : IsOpen U)
    (hUf : volume U ≠ ∞) {u η : EuclideanPlane → ℝ}
    (W : DeGiorgi.MemW1pWitness 2 u U)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hs : HasCompactSupport η) (hsub : tsupport η ⊆ U)
    {C₀ C₁ e : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (he : 0 ≤ e)
    (hηb : ∀ x, |η x| ≤ C₀) (hηd : ∀ x, ‖fderiv ℝ η x‖ ≤ C₁)
    (hub : ∀ x ∈ U, |u x| ≤ e) :
    ∃ V : DeGiorgi.MemW1pWitness 2 (fun x => η x*u x) univ,
      (∫ x, ‖V.weakGrad x‖^2) ≤
        2*C₀^2*(∫ x in U, ‖W.weakGrad x‖^2)+4*C₁^2*e^2*(volume U).toReal := by
  let J := W.mul_smooth_bounded_p (by norm_num) hU hη hC₀ hC₁ hηb hηd
  obtain ⟨V⟩ := exists_global_compact_cutoff_witness hU W.memW1p hη hs hsub
  have hVG := (V.restrict hU (subset_univ U)).ae_eq hU J
  change V.weakGrad =ᵐ[volume.restrict U] J.weakGrad at hVG
  have hparts (x : EuclideanPlane) (i : Fin 2) :
      J.weakGrad x i = η x*W.weakGrad x i+fderiv ℝ η x (EuclideanSpace.single i 1)*u x := by
    simp only [J, DeGiorgi.MemW1pWitness.mul_smooth_bounded_p, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul]
  have hd (x : EuclideanPlane) (i : Fin 2) :
      |fderiv ℝ η x (EuclideanSpace.single i 1)| ≤ C₁ := by
    have hh := (fderiv ℝ η x).le_opNorm (EuclideanSpace.single i 1)
    have hh' : |fderiv ℝ η x (EuclideanSpace.single i 1)| ≤ ‖fderiv ℝ η x‖ := by
      simpa only [Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one] using hh
    exact hh'.trans (hηd x)
  have hbound : ∀ x ∈ U, ‖J.weakGrad x‖^2 ≤
      2*C₀^2*‖W.weakGrad x‖^2+4*C₁^2*e^2 := by
    intro x hx
    rw [plane_norm_sq, hparts x 0, hparts x 1, plane_norm_sq]
    exact cutoff_gradient_square_bound hC₀ hC₁ he (hηb x) (hub x hx) (hd x 0) (hd x 1)
  have hz : ∀ᵐ x ∂volume, x ∉ U → ‖V.weakGrad x‖^2 = 0 := by
    filter_upwards [compact_weakGradient_zero_off V 0, compact_weakGradient_zero_off V 1] with x h0 h1 hx
    have hx' : x ∉ tsupport (fun x => η x*u x) := fun h => hx (hsub (tsupport_mul_subset_left h))
    rw [plane_norm_sq, h0 hx', h1 hx']
    norm_num
  have hJi := J.weakGrad_norm_memLp.integrable_sq
  have hWi := W.weakGrad_norm_memLp.integrable_sq
  let : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUf
  have hci : Integrable (fun _ : EuclideanPlane => 4*C₁^2*e^2) (volume.restrict U) := integrable_const _
  refine ⟨V, ?_⟩
  calc
    _ = ∫ x in U, ‖V.weakGrad x‖^2 := (setIntegral_eq_integral_of_ae_compl_eq_zero hz).symm
    _ = ∫ x in U, ‖J.weakGrad x‖^2 := integral_congr_ae (hVG.mono (fun _ hx => congrArg (fun z : EuclideanPlane => ‖z‖^2) hx))
    _ ≤ ∫ x in U, 2*C₀^2*‖W.weakGrad x‖^2+4*C₁^2*e^2 :=
      integral_mono_ae hJi ((hWi.const_mul _).add hci)
        ((ae_restrict_mem hU.measurableSet).mono fun x hx => hbound x hx)
    _ = _ := by
      rw [integral_add (hWi.const_mul _) hci, integral_const_mul, integral_const]
      simp only [Measure.restrict_apply_univ, Measure.real, smul_eq_mul]
      ring

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

 theorem ControlledHeight.compact_flattened_error_energy {R d : ℝ} (H : ControlledHeight R d)
    (A : ℝ) (T : ℝ → ℝ)
    (W : DeGiorgi.MemW1pWitness 2 (fun x => T (H.height (complexPlaneCoordinates x))) (ball 0 A))
    {ε δ ζ C₀ C₁ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) (hζ : 0 ≤ ζ)
    (he : (∫⁻ x in ball 0 A,
      ENNReal.ofReal (‖W.weakGrad x-heightLimitGradient H.error₀ H.error₁ x‖^2)) < ENNReal.ofReal ε)
    (hT : ∀ t, |T t-t| ≤ ζ)
    (hclose : ∀ x ∈ ball (0 : EuclideanPlane) A,
      |H.height (complexPlaneCoordinates x)-x 1| ≤ δ)
    (η : EuclideanPlane → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hs : HasCompactSupport η) (hsub : tsupport η ⊆ ball 0 A)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hηb : ∀ x, |η x| ≤ C₀) (hηd : ∀ x, ‖fderiv ℝ η x‖ ≤ C₁) :
    ∃ V : DeGiorgi.MemW1pWitness 2
        (fun x => η x*(T (H.height (complexPlaneCoordinates x))-x 1)) univ,
      (∫ x, ‖V.weakGrad x‖^2) ≤
        2*C₀^2*(2*ε+4*Real.pi*d)+4*C₁^2*(ζ+δ)^2*(volume (ball (0 : EuclideanPlane) A)).toReal := by
  let E := subtractSobolevWitness W (verticalLocalWitness A)
  have hbound : ∀ x ∈ ball (0 : EuclideanPlane) A,
      |T (H.height (complexPlaneCoordinates x))-x 1| ≤ ζ+δ := by
    intro x hx
    calc
      _ ≤ |T (H.height (complexPlaneCoordinates x))-H.height (complexPlaneCoordinates x)|+
          |H.height (complexPlaneCoordinates x)-x 1| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add (hT _) (hclose x hx)
  obtain ⟨V, hV⟩ := compact_cutoff_energy_bound isOpen_ball measure_ball_lt_top.ne E hη hs hsub
    hC₀ hC₁ (add_nonneg hζ hδ) hηb hηd hbound
  have hE : (∫ x in ball 0 A, ‖E.weakGrad x‖^2) < 2*ε+4*Real.pi*d := by
    convert H.flattened_energy_error A W hε he using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext x
    rw [subtractSobolevWitness_gradient]
    rfl
  refine ⟨V, hV.trans ?_⟩
  have hm := mul_le_mul_of_nonneg_left hE.le (show 0 ≤ 2*C₀^2 by positivity)
  exact add_le_add hm le_rfl

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

 theorem compact_target_pullback_energy (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    {v : EuclideanPlane → ℝ} (hv : Continuous v) (hs : HasCompactSupport v)
    (V : DeGiorgi.MemW1pWitness 2 v univ) :
    ∃ W : DeGiorgi.MemW1pWitness 2
        (planeInverseTransport (extendAtInfinity M.function) v) (physicalPlaneDomain G),
      (∫ x in physicalPlaneDomain G, W.weakGrad x 0^2+W.weakGrad x 1^2) ≤
        ∫ x in physicalPlaneDomain (extendAtInfinity M.function '' G),
          V.weakGrad x 0^2+V.weakGrad x 1^2 := by
  obtain ⟨hfc, hmap, fi, hfic, hfimap, hl, hr⟩ := M.conformal
  have heq : IsSmoothSphereEquivalence fi (extendAtInfinity M.function)
      (extendAtInfinity M.function '' G) G :=
    ⟨fun p hp => hfic.isSmoothSphereAt M.image_open hp, hfimap,
      fun p hp => hfc.isSmoothSphereAt hG hp, hmap, hr, hl⟩
  have hfi : fi OnePoint.infty = OnePoint.infty := by
    simpa only [extendAtInfinity_infty] using hl _ hinf
  exact sobolev_conformal_transport heq M.image_open hG ⟨_, hinf, rfl⟩ hfi hfic hv hs V
    (fun _ _ => rfl) (M.compact_target_pullback_memLp hG hinf hv hs)

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelHeightErrorTransport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual flattened vertical error has a small source Sobolev
witness, by conformal transport of its compact target cutoff. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem compact_height_error_transport (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    {R d : ℝ} (H : ControlledHeight R d) (A : ℝ) (T : ℝ → ℝ) (hTc : Continuous T)
    (W : DeGiorgi.MemW1pWitness 2 (fun x => T (H.height (complexPlaneCoordinates x))) (ball 0 A))
    {ε δ ζ C₀ C₁ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) (hζ : 0 ≤ ζ)
    (he : (∫⁻ x in ball 0 A,
      ENNReal.ofReal (‖W.weakGrad x-heightLimitGradient H.error₀ H.error₁ x‖^2)) < ENNReal.ofReal ε)
    (hT : ∀ t, |T t-t| ≤ ζ)
    (hclose : ∀ x ∈ ball (0 : EuclideanPlane) A,
      |H.height (complexPlaneCoordinates x)-x 1| ≤ δ)
    (η : EuclideanPlane → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hs : HasCompactSupport η) (hsub : tsupport η ⊆ ball 0 A)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hηb : ∀ x, |η x| ≤ C₀) (hηd : ∀ x, ‖fderiv ℝ η x‖ ≤ C₁) :
    let v := fun x => η x*(T (H.height (complexPlaneCoordinates x))-x 1)
    ∃ E : DeGiorgi.MemW1pWitness 2
        (planeInverseTransport (extendAtInfinity M.function) v) (physicalPlaneDomain G),
      (∫ x in physicalPlaneDomain G, E.weakGrad x 0^2+E.weakGrad x 1^2) ≤
        2*C₀^2*(2*ε+4*Real.pi*d)+4*C₁^2*(ζ+δ)^2*(volume (ball (0 : EuclideanPlane) A)).toReal := by
  obtain ⟨V, hV⟩ := H.compact_flattened_error_energy A T W hε hδ hζ he hT hclose
    η hη hs hsub hC₀ hC₁ hηb hηd
  have hc : Continuous (fun x => η x*(T (H.height (complexPlaneCoordinates x))-x 1)) :=
    hη.continuous.mul ((hTc.comp (H.height.continuous.comp complexPlaneCoordinates.continuous)).sub
      verticalLinear.continuous)
  obtain ⟨E, hE⟩ := M.compact_target_pullback_energy hG hinf hc hs.mul_right V
  refine ⟨E, hE.trans (le_trans ?_ hV)⟩
  have hi : Integrable (fun x => ‖V.weakGrad x‖^2) volume := by
    simpa only [Measure.restrict_univ] using V.weakGrad_norm_memLp.integrable_sq
  have htarget := setIntegral_le_integral hi (Eventually.of_forall (fun _ => sq_nonneg _))
    (s := physicalPlaneDomain (extendAtInfinity M.function '' G))
  simpa only [plane_norm_sq] using htarget

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

 theorem exists_height_error_scale (C₀ C₁ V : ℝ) {ν b : ℝ}
    (hν : 0 < ν) (hb : 0 < b) :
    ∃ t : ℝ, 0 < t ∧ t < b ∧
      2*C₀^2*(2*t+4*Real.pi*t)+4*C₁^2*(t+t)^2*V < ν^2 := by
  let E := fun t : ℝ => 2*C₀^2*(2*t+4*Real.pi*t)+4*C₁^2*(t+t)^2*V
  have hc : Continuous E := by dsimp only [E]; fun_prop
  have hzero : E 0 < ν^2 := by dsimp only [E] <;> nlinarith [sq_pos_of_pos hν]
  have ho : IsOpen ({t : ℝ | E t < ν^2} ∩ Iio b) :=
    (isOpen_lt hc continuous_const).inter isOpen_Iio
  have hn := ho.mem_nhds (show (0 : ℝ) ∈ {t : ℝ | E t < ν^2} ∩ Iio b from ⟨hzero,hb⟩)
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hn
  have ht : r/2 ∈ ball (0 : ℝ) r := by
    simp only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    linarith
  exact ⟨r/2,half_pos hr,(hsub ht).2,(hsub ht).1⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ControlledHeightCloseness
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The height tolerance is uniform over all retained models with one
fixed exterior radius. Only the near-extremality error must shrink. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem controlled_heights_close {R : ℝ}
    {K : Set ℂ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ d, 0 < d → d < δ → ∀ H : ControlledHeight R d,
      ∀ z ∈ K, |H.height z-z.im| < ε := by
  let I := Σ d : {d : ℝ // 0 < d ∧ d ≤ 1}, ControlledHeight R d.1
  let v : I → C(ℂ, ℝ) := fun i => i.2.height
  have heq : Equicontinuous (fun i z => v i z) := by
    apply heights_equicontinuous_of_log_bound (B := 2*Real.pi) _ (by positivity)
    intro i c r hr hr1 z hz
    have h := i.2.log_bound c r hr hr1 z hz
    have hd : 2*Real.pi*i.1.1 ≤ 2*Real.pi :=
      mul_le_of_le_one_right (by positivity) i.1.2.2
    exact h.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have hb (L : Set ℂ) (hL : IsCompact L) :
      ∃ C : ℝ, ∀ i z, z ∈ L → |v i z| ≤ C := by
    obtain ⟨S, hS⟩ := hL.isBounded.subset_ball 0
    let T := max (2*R) S
    refine ⟨T+R, fun i z hz => i.2.local_bound T (le_max_left _ _) z ?_⟩
    exact ball_subset_closedBall ((ball_subset_ball (le_max_right _ _)) (hS hz))
  obtain ⟨δ, hδ, hc⟩ := uniform_height_closeness v (fun i => i.2.error₀)
    (fun i => i.2.error₁) (fun i => i.2.weak_gradient) heq hb
    (fun i => 2*Real.pi*i.1.1) (fun i => i.2.error_bound)
    (fun i => i.2.exterior_bound) hK hε
  refine ⟨min 1 (δ/(2*Real.pi)), lt_min zero_lt_one (div_pos hδ (by positivity)), ?_⟩
  intro d hd hdδ H z hz
  let i : I := ⟨⟨d, hd, hdδ.le.trans (min_le_left _ _)⟩, H⟩
  apply hc i ?_ z hz
  change 2*Real.pi*d < δ
  have h := (lt_div_iff₀ (by positivity : 0 < 2*Real.pi)).mp
    (hdδ.trans_le (min_le_right _ _))
  nlinarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_NearExtremalHeightCloseness
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform compact-set closeness for the actual model heights, together
with their zero gradient on the actual complement. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem uniform_near_extremal_height
    {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
    (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hinf : OnePoint.infty ∈ G)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (hbound : BddAbove (CompactScalarModel.coefficientSet G u))
    {R : ℝ} (hR : 0 < R) {K : Set ℂ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (M : CompactScalarModel G u) d, 0 < d → d < δ →
      sSup (CompactScalarModel.coefficientSet G u)-d ≤ M.coefficient.re →
      complexPlaneCoordinates '' (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ ⊆
        ball 0 R →
      ∃ H : ControlledHeight R d,
        (∀ᵐ p ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
          heightLimitGradient H.error₀ H.error₁ p = 0) ∧
        (∀ z ∈ K, |H.height z-z.im| < ε) := by
  obtain ⟨δ, hδ, hc⟩ := controlled_heights_close (R := R) hK hε
  refine ⟨δ, hδ, ?_⟩
  intro M d hd hdδ hnear hFR
  obtain ⟨H, hz⟩ := M.exists_controlled_height hsolver hprincipal hgreen harea hinf hu hs
    hbound hd hnear hR hFR
  exact ⟨H, hz, hc d hd hdδ H⟩

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
-- module Solutions.Q146_CD.CircleDomains_Selection_NearMaximalHeightSelection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Select an actual nearly maximal model and its actual controlled height,
with prescribed compact closeness and a prescribed small deficit. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_close_model_height
    {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
    (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (hne : Nonempty (CompactScalarModel G u))
    {R : ℝ} (hR : 0 < R) (hsource : (((↑) : ℂ → Sphere) '' ball 0 R)ᶜ ⊆ G)
    {K : Set ℂ} (hK : IsCompact K) {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap) :
    ∃ d : ℝ, 0 < d ∧ d < cap ∧ ∃ M : CompactScalarModel G u,
      ∃ H : ControlledHeight (3*R+1) d,
        (∀ᵐ p ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
          heightLimitGradient H.error₀ H.error₁ p = 0) ∧
        (∀ z ∈ K, |H.height z-z.im| < ε) := by
  have hsf : ∀ z : ℂ, R < ‖z‖ → (z : Sphere) ∈ G := by
    intro z hz
    apply hsource
    rintro ⟨w,hw,he⟩
    have hwz : w = z := OnePoint.coe_injective he
    subst w
    have := mem_ball_zero_iff.mp hw
    linarith
  have hRt : 0 < 3*R+1 := by linarith
  obtain ⟨δ,hδ,hclose⟩ := uniform_near_extremal_height hsolver hprincipal hgreen harea
    hinf hu hs (CompactScalarModel.coefficientSet_bddAbove harea hR hsf) hRt hK hε
  let d := min δ cap / 2
  have hd : 0 < d := half_pos (lt_min hδ hcap)
  have hdδ : d < δ := (half_lt_self (lt_min hδ hcap)).trans_le (min_le_left _ _)
  have hdc : d < cap := (half_lt_self (lt_min hδ hcap)).trans_le (min_le_right _ _)
  obtain ⟨M,hM⟩ := CompactScalarModel.exists_near_maximal hne hd
  have htarget : complexPlaneCoordinates ''
      (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ ⊆ ball 0 (3*R+1) := by
    rintro z ⟨x,hx,rfl⟩
    have hx' : (complexPlaneCoordinates x : Sphere) ∉ extendAtInfinity M.function '' G := hx
    have hb := (M.uniform_omitted_and_image_bound harea hG hR hsource).1 _ hx'
    exact mem_ball_zero_iff.mpr (by linarith)
  obtain ⟨H,hHz,hH⟩ := hclose M d hd hdδ hM.le htarget
  exact ⟨d,hd,hdc,M,H,hHz,hH⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SelectedHeightError
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected flattening and the nearly maximal deficit give an actual
transported error witness with the prescribed small source energy. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem height_error_energy_mono {C₀ C₁ V e d : ℝ}
    (hd : d ≤ e) :
    2*C₀^2*(2*e+4*Real.pi*d)+4*C₁^2*(e+e)^2*V ≤
      2*C₀^2*(2*e+4*Real.pi*e)+4*C₁^2*(e+e)^2*V := by
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hd (by positivity))
  · positivity

namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem FlattenedSourceSelection.exists_small_height_error
    (M : CompactScalarModel G u) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    {R d A L e : ℝ} (H : ControlledHeight R d)
    {Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    (S : FlattenedSourceSelection M H Wold A L e e) (he : 0 < e) (hde : d ≤ e)
    (θ : EuclideanPlane → ℝ) (hθ : ContDiff ℝ ∞ θ) (hsθ : HasCompactSupport θ)
    (hθA : tsupport θ ⊆ ball 0 A) {C : ℝ} (hC : 0 ≤ C)
    (hθunit : ∀ x, θ x ∈ Icc (0 : ℝ) 1) (hθd : ∀ x, ‖fderiv ℝ θ x‖ ≤ C)
    (hclose : ∀ x ∈ ball (0 : EuclideanPlane) A,
      |H.height (complexPlaneCoordinates x)-x 1| ≤ e)
    {ν : ℝ} (hbudget : 2*(2*e+4*Real.pi*e)+4*C^2*(e+e)^2*
      (volume (ball (0 : EuclideanPlane) A)).toReal < ν^2) :
    ∃ E : DeGiorgi.MemW1pWitness 2 (planeInverseTransport (extendAtInfinity M.function)
        (fun y => θ y*(flattenValues S.heightValues (H.height (complexPlaneCoordinates y))-y 1)))
        (physicalPlaneDomain G),
      (∫ x in physicalPlaneDomain G, E.weakGrad x 0^2+E.weakGrad x 1^2) < ν^2 := by
  obtain ⟨E,hE⟩ := M.compact_height_error_transport hG hinf H A
    (flattenValues S.heightValues) (flattenValues_lipschitz S.height_open.measurableSet).continuous
    S.heightWitness he he.le he.le S.height_error (fun t => (S.height_close t).le) hclose
    θ hθ hsθ hθA (show (0 : ℝ) ≤ 1 by norm_num) hC
    (fun x => by rw [abs_of_nonneg (hθunit x).1]; exact (hθunit x).2) hθd
  refine ⟨E,hE.trans_lt ?_⟩
  have hm := height_error_energy_mono (C₀ := 1) (C₁ := C)
    (V := (volume (ball (0 : EuclideanPlane) A)).toReal) hde
  norm_num only [one_pow, mul_one] at hm
  simpa only [one_pow, mul_one] using hm.trans_lt hbudget

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelLocalizedSelection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The simultaneous selection may keep every changed support in a
prescribed source disk containing the dust. This leaves the outer
working collar unchanged. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem exists_flattened_source_selection_in_ball (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcoarea : PlanarSobolevCoarea)
    (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (hB : IsCompact {z : ℂ | (z : Sphere) ∉ G})
    (hne : {z : ℂ | (z : Sphere) ∉ G}.Nonempty)
    {C : ℝ} (hC : {z : ℂ | (z : Sphere) ∉ G} ⊆ ball 0 C)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (W : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G))
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ x ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ x = 0)
    (A L : ℝ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ S : FlattenedSourceSelection M H W A L δ ε,
      ∀ n, support (S.cutoff n) ⊆ ball 0 C := by
  classical
  obtain ⟨b,z,K,_,hb,hz,hK,hcover⟩ := M.exists_priority_source_data hsard hsch hG hconn hinf hTD hB hne
  have hex (i : Fin m) := exists_compact_value_flattening hcoarea
    (isOpen_physicalPlaneDomain hG) (hu i) (hs i) (W i)
    (C := range (fun n => sphereFromPlaneFunction (u i) (b n : Sphere))) (countable_range _) hδ hε
  choose O WO hO hCO hOc hOs hOclose hOerror hOzero using hex
  obtain ⟨V,WV,hV,hCV,_,hVclose,hVerror,_,_⟩ := H.exists_local_value_flattening hcoarea A
    (C := range (fun n => M.heightSection H (b n : Sphere))) (countable_range _) hδ hε
  obtain ⟨N,hN,hOld,hHeight⟩ := M.exists_common_flattened_neighborhoods hsard hsch
    hG hconn hinf hTD hu H hHz b O hO V hV
    (fun n i => hCO i (mem_range_self n)) (fun n => hCV (mem_range_self n))
  obtain ⟨r,χ,hr,hrt,hrN,hχ,hPc,hPe,hPerror,hSerror⟩ :=
    M.exists_horizontal_priority_with_support hsard hsch hG hconn hinf hTD
      b hb z hz hcover hK (fun n => N n ∩ ball 0 C)
      (fun n => ((hN n).1.inter isOpen_ball).mem_nhds ⟨(hN n).2, hC (hb n)⟩) L hε
  refine ⟨{
    oldValues := O, old_open := hO, oldWitness := WO, old_close := hOclose, old_error := hOerror
    heightValues := V, height_open := hV, heightWitness := WV, height_close := hVclose
    height_error := hVerror
    center := b, center_outside := hb, target := z, target_projection := hz, radius := r, radius_pos := hr, radius_tendsto := hrt
    cutoff := χ, cutoff_smooth := fun n => (hχ n).1
    cutoff_support := fun n => (subset_tsupport _).trans (hχ n).2.2.1
    cutoff_unit := fun n => (hχ n).2.2.2.1
    value := fun n => (finiteCoord (z n)).re, value_eq := fun _ => rfl
    priority_continuous := hPc, priority_error_memLp := hPe
    priority_error := hPerror, support_error := hSerror
    old_constant := ?_, height_constant := ?_ }, ?_⟩
  · intro i n
    refine ⟨flattenValues (O i) (sphereFromPlaneFunction (u i) (b n : Sphere)), ?_⟩
    intro x hx
    exact hOld n i (hrN n ((hχ n).2.2.1 (subset_tsupport _ hx.2))).1
  · intro n
    refine ⟨flattenValues V (M.heightSection H (b n : Sphere)), ?_⟩
    intro x hx
    exact hHeight n (hrN n ((hχ n).2.2.1 (subset_tsupport _ hx.2))).1

  · intro n x hx
    exact (hrN n ((hχ n).2.2.1 (subset_tsupport _ hx))).2

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PreparedHeightSelection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose the actual model, height, common flattenings and priority
supports after fixing the cutoff constants and the desired energy budget. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_small_selected_height_data_oai
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
    (hne : Nonempty (CompactScalarModel G u))
    {R C : ℝ} (hR : 0 < R) (hsource : (((↑) : ℂ → Sphere) '' ball 0 R)ᶜ ⊆ G)
    (hC : {z : ℂ | (z : Sphere) ∉ G} ⊆ ball 0 C)
    (A L : ℝ) (θ : EuclideanPlane → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hsθ : HasCompactSupport θ) (hθA : tsupport θ ⊆ ball 0 A)
    {Cθ : ℝ} (hCθ : 0 ≤ Cθ) (hθunit : ∀ x, θ x ∈ Icc (0 : ℝ) 1)
    (hθd : ∀ x, ‖fderiv ℝ θ x‖ ≤ Cθ)
    {b t : ℝ} (hb : 0 < b) (ht : 0 < t) :
    ∃ e : ℝ, 0 < e ∧ e < b ∧ ∃ d : ℝ, 0 < d ∧ d < e ∧
      ∃ M : CompactScalarModel G u, ∃ H : ControlledHeight (3*R+1) d,
      ∃ S : CompactScalarModel.FlattenedSourceSelection M H Wold A L e e,
        (∀ z ∈ closedBall 0 A, |H.height z-z.im| < e) ∧
        (∀ n, support (S.cutoff n) ⊆ ball 0 C) ∧
        ∃ E : DeGiorgi.MemW1pWitness 2 (planeInverseTransport (extendAtInfinity M.function)
          (fun y => θ y*(flattenValues S.heightValues (H.height (complexPlaneCoordinates y))-y 1)))
          (physicalPlaneDomain G),
          (∀ᵐ x ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
            heightLimitGradient H.error₀ H.error₁ x = 0) ∧
          (∫ x in physicalPlaneDomain G, E.weakGrad x 0^2+E.weakGrad x 1^2) < t^2 := by
  obtain ⟨e,he,heb,hbudget⟩ := exists_height_error_scale 1 Cθ
    (volume (ball (0 : EuclideanPlane) A)).toReal ht hb
  obtain ⟨d,hd,hde,M,H,hHz,hclose⟩ := exists_close_model_height hsolver hprincipal hgreen harea
    hG hinf hu hs hne hR hsource (isCompact_closedBall (0 : ℂ) A) he he
  obtain ⟨S,hS⟩ := M.exists_flattened_source_selection_in_ball hsard hsch hcoarea
    hG hconn hinf hTD hB hBne hC hu hs Wold H hHz A L he he
  have hclose' : ∀ x ∈ ball (0 : EuclideanPlane) A,
      |H.height (complexPlaneCoordinates x)-x 1| ≤ e := by
    intro x hx
    have hz : complexPlaneCoordinates x ∈ closedBall (0 : ℂ) A := by
      simpa only [mem_closedBall, dist_zero_right, complexPlaneCoordinates_norm] using
        (show ‖x‖ ≤ A from (mem_ball_zero_iff.mp hx).le)
    exact (hclose _ hz).le
  have hbudget' : 2*(2*e+4*Real.pi*e)+4*Cθ^2*(e+e)^2*
      (volume (ball (0 : EuclideanPlane) A)).toReal < t^2 := by
    simpa only [one_pow, mul_one] using hbudget
  obtain ⟨E,hE⟩ := S.exists_small_height_error M hG hinf H he hde.le θ hθ hsθ hθA
    hCθ hθunit hθd hclose' hbudget'
  exact ⟨e,he,heb,d,hd,hde,M,H,S,hclose,hS,E,hHz,hE⟩

end CircleDomainRigidity

end

end OAI
end

theorem solution : type_of% @OAI.CircleDomainRigidity.exists_small_selected_height_data_oai := @OAI.CircleDomainRigidity.exists_small_selected_height_data_oai
