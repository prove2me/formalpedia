-- Prove2me | solution 1 for GlobalTheory.Cyc.AveragingRankOne.rank_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:15:22.236494+00:00
-- url     : https://prove2.me/submissions/69bcff11-bfeb-4353-924f-80e35f7bb1c8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerTraceAlmostSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOrbitPadicComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsRest
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTateMaximalIdealKillsFirstCohomology
import Theorems.Thm_GlobalTheory_Cyc_AveragingRankOne_step
import Theorems.Thm_GlobalTheory_Cyc_IsCyc_continuous
import Theorems.Thm_GlobalTheory_T_continuous_orbit_padicComplex


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.AveragingRankOne
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.AveragingRankOne
theorem _root_.solution (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (hact : IsActC act)
    (K : FinExt l) (a : PadicComplex l) (ha : a ∈ inC (Kinf K)) (ha1 : ‖a‖ < 1)
    (c : GQ l → PadicComplex l) (hcont : ContinuousOn c (Hinf K))
    (hc : ∀ g ∈ Hinf K, ∀ h ∈ Hinf K, c (g * h) = c g + act g (c h))
    (ht : ∀ g ∈ Hinf K, ‖c g‖ ≤ 1) :
    ∃ x : PadicComplex l, ‖x‖ ≤ 1 ∧ ∀ h ∈ Hinf K, a * c h = act h x - x := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact ⟨0, by simp, by simp⟩
  have hapos : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have hfix : ∀ g ∈ Hinf K, act g a = a := by
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    intro g hg
    rw [hact.1, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg a₀ ha₀]
  let Q : ℕ → PadicComplex l → Prop := fun n y =>
    ‖y‖ ≤ 1 ∧ ∀ h ∈ Hinf K, ‖a * c h - (act h y - y)‖ ≤ ‖a‖ * (1 / 2) ^ n
  have hstep : ∀ n y, Q n y → ∃ y', Q (n + 1) y' ∧ dist y y' ≤ 1 * (1 / 2 : ℝ) ^ n := by
    rintro n y ⟨hy1, hy⟩
    obtain ⟨x, hx, hx'⟩ := step act hact K a ha ha1 (fun g => c g - a⁻¹ * (act g y - y))
      (hcont.sub (continuousOn_const.mul
        ((GlobalTheory.T.continuous_orbit_padicComplex l act hact y).continuousOn.sub continuousOn_const)))
      (fun g hg h hh => by
        simp only [hc g hg h hh, map_mul, map_sub, map_inv₀, hfix g hg, RingAut.mul_apply]
        ring)
      ((1 / 2) ^ n) (‖a‖ * (1 / 2) ^ (n + 1)) (by positivity) (by positivity)
      (fun g hg => by
        have e : c g - a⁻¹ * (act g y - y) = a⁻¹ * (a * c g - (act g y - y)) := by
          field_simp
        rw [e, norm_mul, norm_inv, inv_mul_le_iff₀ hapos]
        exact hy g hg)
    refine ⟨y + x, ⟨?_, fun h hh => ?_⟩, ?_⟩
    · refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy1 (hx.trans ?_))
      exact pow_le_one₀ (by norm_num) (by norm_num)
    · have e : a * c h - (act h (y + x) - (y + x)) =
          a * (c h - a⁻¹ * (act h y - y)) - (act h x - x) := by
        rw [map_add]; field_simp; ring
      rw [e]; exact hx' h hh
    · simpa [dist_eq_norm] using hx
  choose! f hfQ hfd using hstep
  let y : ℕ → PadicComplex l := fun n => Nat.rec 0 f n
  have hQ : ∀ n, Q n (y n) := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simp [y], fun h hh => ?_⟩
      simpa [y] using mul_le_mul_of_nonneg_left (ht h hh) hapos.le
    | succ n ih => exact hfQ n _ ih
  have hcau : CauchySeq y :=
    cauchySeq_of_le_geometric (1 / 2) 1 (by norm_num) fun n => hfd n _ (hQ n)
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨x, le_of_tendsto' hx.norm fun n => (hQ n).1, fun h hh => ?_⟩
  have hiso : Continuous (act h) :=
    (AddMonoidHomClass.isometry_of_norm (act h) (hact.2 h)).continuous
  have h1 : Filter.Tendsto (fun n => ‖a * c h - (act h (y n) - y n)‖) Filter.atTop
      (nhds ‖a * c h - (act h x - x)‖) :=
    (tendsto_const_nhds.sub (((hiso.tendsto x).comp hx).sub hx)).norm
  have h2 : Filter.Tendsto (fun n : ℕ => ‖a‖ * (1 / 2 : ℝ) ^ n) Filter.atTop (nhds (‖a‖ * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
  have := le_of_tendsto_of_tendsto' h1 h2 fun n => (hQ n).2 h hh
  rw [mul_zero, norm_le_zero_iff, sub_eq_zero] at this
  exact this
end GlobalTheory.Cyc.AveragingRankOne
