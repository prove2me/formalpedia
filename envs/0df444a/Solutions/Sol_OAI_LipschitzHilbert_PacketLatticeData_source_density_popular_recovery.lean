-- Prove2me | solution 1 for OAI.LipschitzHilbert.PacketLatticeData.source_density_popular_recovery
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:00:05.164049+00:00
-- url     : https://prove2.me/submissions/e6d1ae0f-92d9-40aa-ad7f-38a0a9135ce8

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_LipschitzHilbert
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_PacketLatticeData_eventually_actual_packet_recovery
import Theorems.Thm_OAI_LipschitzHilbert_PacketLatticeData_source_assigned_selector_mask_good_set
import Theorems.Thm_OAI_LipschitzHilbert_eventually_source_simultaneous_count_universal

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SlicedIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! From almost-everywhere line estimates to planar estimates, including
the area-preserving coordinates of a fixed reference slope. -/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem integral_slopeShear (s : ℝ) (f : ℝ × ℝ → ℝ) :
    (∫ z, f (slopeShear s z) ∂volume.prod volume) = ∫ z, f z ∂volume.prod volume :=
  (slopeShear_measurePreserving s).integral_comp (slopeShear s).measurableEmbedding f

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual decaying top weights and their motion along a reference line. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

namespace SlopeBox

theorem radius_nonnegative (T : SlopeBox) (z : ℝ × ℝ) : 0 ≤ T.radius z :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem weight_pos (T : SlopeBox) {K : ℝ} (hK : 0 < K) (D : ℝ) (z : ℝ × ℝ) :
    0 < T.weight K D z := by
  unfold weight
  have hr := T.radius_nonnegative z
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) D)
    (Real.rpow_pos_of_pos (by positivity) _)

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeightIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability and exact area scaling for the actual decaying top weights. -/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

theorem planeDivide_apply (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (z : ℝ × ℝ) :
    planeDivide a b ha hb z = (z.1 / a, z.2 / b) := by
  rfl

theorem map_planeDivide (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Measure.map (planeDivide a b ha hb) (volume.prod volume) =
      (ENNReal.ofReal |a| * ENNReal.ofReal |b|) • (volume.prod volume) := by
  have hmap (c : ℝ) (hc : c ≠ 0) :
      Measure.map (fun x : ℝ => x * c⁻¹) volume = ENNReal.ofReal |c| • volume := by
    simpa only [smul_eq_mul, Module.finrank_self, pow_one, inv_inv, mul_comm] using
      (Measure.map_addHaar_smul (μ := (volume : Measure ℝ)) (inv_ne_zero hc))
  change Measure.map (Prod.map (fun x => x * a⁻¹) (fun y => y * b⁻¹)) _ = _
  rw [← Measure.map_prod_map volume volume (by fun_prop) (by fun_prop), hmap a ha, hmap b hb,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]

theorem integral_planeDivide (f : ℝ × ℝ → ℝ) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∫ z, f (planeDivide a b ha hb z) ∂volume.prod volume) =
      (|a| * |b|) * ∫ z, f z ∂volume.prod volume := by
  rw [← integral_map_equiv (planeDivide a b ha hb), map_planeDivide, integral_smul_measure]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]

theorem topProfile_nonnegative (D : ℝ) (z : ℝ × ℝ) : 0 ≤ topProfile D z :=
  Real.rpow_nonneg (by positivity) _

namespace SlopeBox

theorem normalizedCoordinates_eq (T : SlopeBox) (K : ℝ) (hK : 0 < K) (z : ℝ × ℝ) :
    T.normalizedCoordinates K hK z = (T.horizontal z / K, T.transverse z / K) := by
  ext <;> simp [normalizedCoordinates, planeDivide_apply, slopeShear, horizontal, transverse]
  <;> ring

theorem weight_eq_topProfile (T : SlopeBox) (K D : ℝ) (hK : 0 < K) (z : ℝ × ℝ) :
    T.weight K D z = 2 ^ D * topProfile D (T.normalizedCoordinates K hK z) := by
  rw [normalizedCoordinates_eq]
  simp only [weight, topProfile, radius, abs_div, abs_of_pos hK, add_div]

/-- Exact area scaling: all dependence on the box and the dilation is
`K² * length * width`, while the remaining integral is a fixed constant. -/
theorem integral_weight (T : SlopeBox) {K : ℝ} (hK : 0 < K) (D : ℝ) :
    (∫ z, T.weight K D z ∂volume.prod volume) =
      (2 ^ D * ∫ z, topProfile D z ∂volume.prod volume) *
        K ^ 2 * T.length * T.width := by
  have heq : T.weight K D = fun z => 2 ^ D *
      ((fun z => topProfile D (planeDivide (K * T.length) (K * T.width)
        (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne') z)) ∘
        slopeShear (-T.slope)) (z - (T.x, T.y)) := by
    funext z
    exact T.weight_eq_topProfile K D hK z
  rw [heq, integral_const_mul, integral_sub_right_eq_self]
  simp only [Function.comp_apply]
  rw [integral_slopeShear (-T.slope) (fun z => topProfile D
    (planeDivide (K * T.length) (K * T.width)
      (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne') z)),
    integral_planeDivide, abs_of_pos (mul_pos hK T.length_pos),
    abs_of_pos (mul_pos hK T.width_pos)]
  ring

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopAreaDiscard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the exponential total-top-area exception to a small fraction
of the testing set, using only the manuscript's area and disparity bounds. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem eventually_top_area_factor (b H : ℝ) :
    ∀ᶠ L : ℝ in atTop, L^b*Real.exp (-6*L) ≤ (1/2)*L^(-H) := by
  have hsmall := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (b+H) 6 (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),
    hsmall.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))] with L hL hsmall
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have h := mul_le_mul_of_nonneg_right hsmall.le (Real.rpow_nonneg hL0.le (-H))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [mul_right_comm, ← Real.rpow_add hL0]
  congr 2
  ring

theorem top_area_discard_numeric (L b H N F S : ℝ)
    (hL : 0 < L) (hN : 0 ≤ N) (hF : 0 ≤ F)
    (hNupper : N ≤ Real.exp (2*L)) (harea : S ≤ L^b*N^2*F)
    (hsmall : L^b*Real.exp (-6*L) ≤ (1/2)*L^(-H)) :
    Real.exp (-10*L)*S ≤ (1/2)*L^(-H)*F := by
  have hNsq := pow_le_pow_left₀ hN hNupper 2
  have hExp : (Real.exp (2*L))^2 = Real.exp (4*L) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hExp] at hNsq
  calc
    _ ≤ Real.exp (-10*L)*(L^b*N^2*F) :=
      mul_le_mul_of_nonneg_left harea (Real.exp_pos _).le
    _ ≤ Real.exp (-10*L)*(L^b*Real.exp (4*L)*F) := by gcongr
    _ = (L^b*Real.exp (-6*L))*F := by
      rw [show Real.exp (-10*L)*(L^b*Real.exp (4*L)*F) =
        L^b*(Real.exp (-10*L)*Real.exp (4*L))*F by ring, ← Real.exp_add]
      rw [show -10*L+4*L = -6*L by ring]
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall hF

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual rounded dyadic parameters in the manuscript. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert.SourceParameters

theorem log_step_bounds {L : ℝ} (hL : 0 ≤ L) :
    L ^ (7 / 10 : ℝ) ≤ Real.log (step L) ∧
      Real.log (step L) ≤ L ^ (7 / 10 : ℝ) + 2 * Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr : 0 ≤ L ^ (7 / 10 : ℝ) / (2 * Real.log 2) := by positivity
  have hlo := Nat.le_ceil (L ^ (7 / 10 : ℝ) / (2 * Real.log 2))
  have hhi := (Nat.ceil_lt_add_one hr).le
  rw [step, Real.log_pow, stepExponent, Nat.cast_mul, Nat.cast_ofNat]
  constructor
  · have h := mul_le_mul_of_nonneg_right hlo (show 0 ≤ 2 * Real.log 2 by positivity)
    have heq : L ^ (7 / 10 : ℝ) / (2 * Real.log 2) * (2 * Real.log 2) =
        L ^ (7 / 10 : ℝ) := div_mul_cancel₀ _ (by positivity)
    rw [heq] at h
    nlinarith
  · have h := mul_le_mul_of_nonneg_right hhi (show 0 ≤ 2 * Real.log 2 by positivity)
    have heq : (L ^ (7 / 10 : ℝ) / (2 * Real.log 2) + 1) * (2 * Real.log 2) =
        L ^ (7 / 10 : ℝ) + 2 * Real.log 2 := by
      rw [add_mul, div_mul_cancel₀ _ (by positivity), one_mul]
    rw [heq] at h
    nlinarith

theorem log_branching_le {L : ℝ} (hL : 0 ≤ L) :
    Real.log (branching L) ≤
      (Real.log L ^ 2 + 1) * (L ^ (7 / 10 : ℝ) + 2 * Real.log 2) := by
  rw [branching, Real.log_pow]
  have hK : (blockCount L : ℝ) ≤ Real.log L ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (sq_nonneg (Real.log L))).le
  exact mul_le_mul hK (log_step_bounds hL).2
    (Real.log_nonneg (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))) (by positivity)

/-- The actual rounded dyadic branching satisfies the scale separation
`B^100 ≤ exp(L^0.9)` eventually, with no real-valued stand-in for `B`. -/
theorem eventually_branching_separation :
    ∀ᶠ L : ℝ in atTop, branching L ^ 100 ≤ Real.exp (L ^ (9 / 10 : ℝ)) := by
  have hlog := isLittleO_log_rpow_rpow_atTop (r := 2) (s := 1 / 5) (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10)).eventually_ge_atTop (2 * Real.log 2),
    hlog.bound (by norm_num : (0 : ℝ) < 1 / 400)] with L hL hlogL hpow hsmall
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hp7 : 0 ≤ L ^ (7 / 10 : ℝ) := Real.rpow_nonneg hL0.le _
  have hp2 : 0 ≤ L ^ (1 / 5 : ℝ) := Real.rpow_nonneg hL0.le _
  have hlogsq : 1 ≤ Real.log L ^ 2 := by nlinarith
  rw [Real.rpow_two] at hsmall
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log L)),
    abs_of_nonneg hp2] at hsmall
  have hcrude : Real.log (branching L) ≤ 4 * L ^ (7 / 10 : ℝ) * Real.log L ^ 2 := by
    apply (log_branching_le hL0.le).trans
    nlinarith [mul_le_mul (show Real.log L ^ 2 + 1 ≤ 2 * Real.log L ^ 2 by linarith)
      (show L ^ (7 / 10 : ℝ) + 2 * Real.log 2 ≤ 2 * L ^ (7 / 10 : ℝ) by linarith)
      (by positivity : 0 ≤ L ^ (7 / 10 : ℝ) + 2 * Real.log 2)
      (by positivity : 0 ≤ 2 * Real.log L ^ 2)]
  have hpower : L ^ (7 / 10 : ℝ) * L ^ (1 / 5 : ℝ) = L ^ (9 / 10 : ℝ) := by
    rw [← Real.rpow_add hL0]
    norm_num
  have hbound : 100 * Real.log (branching L) ≤ L ^ (9 / 10 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hsmall (mul_nonneg (by norm_num : (0 : ℝ) ≤ 400) hp7)
    nlinarith
  calc
    branching L ^ 100 = Real.exp (100 * Real.log (branching L)) := by
      have heq : Real.log (branching L ^ (100 : ℕ)) = (100 : ℝ) * Real.log (branching L) := by
        simpa only [Nat.cast_ofNat] using (Real.log_pow (branching L) 100)
      rw [← heq, Real.exp_log (pow_pos (branching_pos L) _)]
    _ ≤ Real.exp (L ^ (9 / 10 : ℝ)) := Real.exp_le_exp.mpr hbound

end LipschitzHilbert.SourceParameters

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCountParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual dyadic source parameters meet the counting hypotheses. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert.SourceParameters

theorem blockCount_pos {L : ℝ} (hL : 1 < L) : 0 < blockCount L := by
  apply Nat.one_le_ceil_iff.mpr
  exact sq_pos_of_pos (Real.log_pos hL)

theorem one_lt_step {L : ℝ} (hL : 0 < L) : 1 < step L := by
  apply (Real.log_pos_iff (step_pos L).le).mp
  exact (Real.rpow_pos_of_pos hL _).trans_le (log_step_bounds hL.le).1

theorem log_branching_lower {L : ℝ} (hL : 1 < L) :
    L ^ (7 / 10 : ℝ) ≤ Real.log (branching L) := by
  have hstep := one_lt_step (zero_lt_one.trans hL)
  have hK : (1 : ℝ) ≤ blockCount L := by exact_mod_cast blockCount_pos hL
  calc
    L ^ (7 / 10 : ℝ) ≤ Real.log (step L) := (log_step_bounds (zero_lt_one.trans hL).le).1
    _ ≤ (blockCount L : ℝ) * Real.log (step L) :=
      le_mul_of_one_le_left (Real.log_nonneg hstep.le) hK
    _ = Real.log (branching L) := (Real.log_pow _ _).symm

theorem eventually_branching_ge (c : ℝ) : ∀ᶠ L : ℝ in atTop, c ≤ branching L := by
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10)).eventually_ge_atTop
      (Real.log (max c 1))] with L hL hpow
  have hmax : 0 < max c 1 := zero_lt_one.trans_le (le_max_right _ _)
  apply (le_max_left c 1).trans
  exact (Real.log_le_log_iff hmax (branching_pos L)).mp
    (hpow.trans (log_branching_lower (by linarith)))

end LipschitzHilbert.SourceParameters

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePredictableDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial bounds for the source predictable-motion
coefficient, before its dyadic gain is absorbed. -/

noncomputable section
namespace LipschitzHilbert

theorem source_blockCount_le_square {L : ℝ} (hL : 5 ≤ L) :
    (SourceParameters.blockCount L : ℝ) ≤ L^2 := by
  have hL0 : 0 ≤ L := by linarith
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hlog : Real.log L ≤ 2*Real.sqrt L := by
    have hb := Real.log_le_rpow_div hL0 (by norm_num : (0:ℝ)<1/2)
    rw [← Real.sqrt_eq_rpow] at hb
    linarith
  have hsq : Real.log L^2 ≤ 4*L := by
    have ht := pow_le_pow_left₀ hlog0 hlog 2
    have hr := Real.sq_sqrt hL0
    nlinarith
  have hceil : (SourceParameters.blockCount L : ℝ) ≤ Real.log L^2+1 :=
    (Nat.ceil_lt_add_one (sq_nonneg (Real.log L))).le
  exact hceil.trans (by nlinarith)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedSelectorControlledGoodSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concentration and mask removal use the auxiliary jet bound belonging
only to the smaller dilation. The larger central normalization does not
enter the mask exponent choice. All physical coefficients are preserved. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem source_assigned_selector_mask_good_set_with_jet_control (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (cStar cEta CEta cb Cb F : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hF : 0 ≤ F)
    (hgap : cStar < cEta*cb)
    (aWeight aw p s Hloss Lip : ℝ) (D K H J₀ : ℕ)
    (haWeight : 0 ≤ aWeight) (haw : 0 ≤ aw) (hp : 0 ≤ p) (hs : 0 ≤ s)
    (hHloss : 0 ≤ Hloss) (hLip : 0 ≤ Lip) (hD : 4 ≤ D) :
    ∃ A Cn L0 : ℝ, aWeight < A ∧ 2 < A ∧ 0 < Cn ∧ 2 ≤ L0 ∧
    ∀ L : ℝ, L0 ≤ L →
    ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
      (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [∀ j l, Fintype (Item j l)] (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ),
    ∀ (scale ratioBound : ℝ) (hratio : 1 ≤ ratioBound)
      (hcontrol : |scale/P.width| ≤ ratioBound),
      ((P.withJetControl scale ratioBound hratio hcontrol).referenceEnvelopeConstant ≤ L^p) →
      6+2*(8*D+1) ≤ P.order →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k,
        planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w : ℝ)
      (hw : 0 < w) (hcone : 0 ≤ cone) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
      (∀ top, P.width ≤ L^aWeight*(T top).width) →
      (∀ top, scale = 4*(L^aWeight*(T top).width)) →
      (∀ q ∈ packets,
        |P.actualX q.1 q.2.1 q.2.2-(T (assigned q)).x|+P.length q.1 ≤
          L^aWeight*(T (assigned q)).length) →
      (∀ q ∈ packets,
        |P.actualZ q.1 q.2.1 q.2.2+(oldSlope-(T (assigned q)).slope)*
          P.actualX q.1 q.2.1 q.2.2-
          ((T (assigned q)).y-(T (assigned q)).slope*(T (assigned q)).x)|+P.width ≤
            L^aWeight*(T (assigned q)).width) →
    ∀ (angle : τ → ℝ) (small wide radius : ℝ) (E J : ℕ),
      (∀ top, 0 < angle top) → 0 < small → small ≤ 1 →
      wide ≤ small*(2:ℝ)^J → 1 ≤ wide*((2:ℝ)^E)^4 → radius ≤ K →
      (∀ top j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l => oldSlope+P.rowSlope j l) (angle top*(2:ℝ)^j.val) H) →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) →
      (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        b j l k s ≠ 0 →
        |s-(oldSlope+P.rowSlope j l)| ≤ radius*(angle top*(2:ℝ)^j.val)) →
      (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        |s-(T top).slope| ≤ small*(angle top*(2:ℝ)^j.val) →
        ‖b j l k s-b j l k (T top).slope‖ ≤
          Lip*(|s-(T top).slope|/(angle top*(2:ℝ)^j.val))) →
      (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        (wide*((2:ℝ)^E)^4)*(angle top*(2:ℝ)^j.val) < |s-(T top).slope| →
        b j l k s = 0) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f →
      (∀ z, ‖f z‖ ≤ 1) →
      (∀ q ∈ packets, ∀ k xi eta,
        planarAngularFourier (P.physicalPacket oldSlope q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ q ∈ packets, ∀ k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket
          oldSlope q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ top j l, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        (∃ k, b j l k (T top).slope ≠ 0) →
        cb*w/P.length j ≤ |oldSlope+P.rowSlope j l-(T top).slope| ∧
          |oldSlope+P.rowSlope j l-(T top).slope| ≤ Cb*w/P.length j) →
      J ≤ J₀ → E = SourceParameters.stepExponent L*SourceParameters.blockCount L →
      (∀ q ∈ packets, P.referenceCondition oldSlope (T (assigned q)).slope
        (R (assigned q)) cone w q.1 q.2.1) →
    ∀ l r : ℝ, (∀ i, |(T i).slope| ≤ 1) →
    ∀ (u : Plane → ℝ) (lip : ℝ≥0), LipschitzWith lip u →
      300*((2*lip:ℝ≥0):ℝ)*(r-l) ≤ 1 →
    ∀ witness : τ → Set (ℝ×ℝ), (∀ i, MeasurableSet (witness i)) →
      (Pairwise fun i j => Disjoint (witness i) (witness j)) →
      (∀ i z, z ∈ witness i → z.1 ∈ Icc l r ∧ (T i).radius z ≤ L^aw) →
      (∀ i z, z ∈ witness i → |u (planeCoordinates z)-(T i).slope| ≤
        (T i).width/(12*(T i).length)) →
      (∀ i, ENNReal.ofReal (L^(-aw)*(T i).length*(T i).width) ≤
        (volume.prod volume) (witness i)) → 0 < ∑ i, (T i).area →
    ∀ (ratio : ℝ) (Fset : Set (ℝ×ℝ)), 0 < ratio → MeasurableSet Fset →
      (volume.prod volume) Fset ≠ ∞ →
      (∀ z ∈ Fset, z.1 ∈ Icc l r) → ratio ≤ Real.exp (2*L) →
      (∑ i, (T i).area) ≤ L^s*ratio^2*(volume.prod volume).real Fset →
      let Q := fun top => (P.assignedTopFamily packets assigned top).referenceFamily
        oldSlope (T top).slope (R top) cone w F hw hcone hF hwide hfrequency
      let orig := fun top j (l : (Q top).labels j) =>
        ((P.assignedTopFamily packets assigned top).referenceOriginalLabel
          oldSlope (T top).slope (R top) cone w j l).val.2
      let a := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
        alt j (orig top j l) u.val k
      let ha := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
        hAlt j (orig top j l) u.val k
      ∃ G : Set (ℝ×ℝ), MeasurableSet G ∧ G ⊆ Fset ∧
        (volume.prod volume) (Fset\G) ≤ ENNReal.ofReal (L^(-Hloss)*(volume.prod volume).real Fset) ∧
        (∀ z ∈ G, (∑ i, (T i).weight (L^(A+2)) (D:ℝ) z) ≤ ratio*L^Cn) ∧
        (∀ top lower upper, lower ≤ upper → upper ≤ N → ∀ z ∈ G, ∀ yy,
          |yy-(z.2-(T top).slope*z.1)| ≤ (T top).width →
          let V := ((Q top).withProfile (a top) (ha top)).rawInterval
            (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig top j l) u.val)
            0 lower upper
          ‖V z.1 yy‖+(T top).width*‖covariantSignal P.frequency
            (fun k y => V z.1 y k) yy‖ ≤ L^(2*p+8)*((T top).weight (L^aWeight) (D:ℝ) z)^8) ∧
        let original := fun z => ∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q
        let masked := fun z => ∑ q ∈ packets, P.physicalMaskedValue alt hAlt oldSlope b v f
          (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z q
        IntegrableOn (fun z => ‖original z-masked z‖) G (volume.prod volume) ∧
        (∫ z in G, ‖original z-masked z‖ ∂volume.prod volume) ≤
          L^(-Hloss)*ratio*(volume.prod volume).real Fset := by
  obtain ⟨A,Cn,L0,haA,hA,hCn,hL0,hgood⟩ := source_assigned_selector_mask_good_set
    hVariation hLL cStar cEta CEta cb Cb F hcStar hcEta hCEta hcb hCb hF hgap
    aWeight aw p s Hloss Lip D K H J₀ haWeight haw hp hs hHloss hLip hD
  refine ⟨A,Cn,L0,haA,hA,hCn,hL0,?_⟩
  intro L hL τ κ _ _ N Label Item _ P packets assigned scale ratioBound hratio hcontrol hP horder alt hAlt T oldSlope R cone w
    hw hcone hwide hfrequency hwidth hscaleEq hX hZ angle small wide radius E J
    hangle hsmall hsmall1 hwideScale hwide1 hradius hlocal b hb hb1 hsupport hnear hfar
    v hv f hf hf1 hspectrum haltSpectrum hsep hJ hE hcondition l r hslopes u lip hu hlength
    witness hW hdisj hinside hclose hsize hSpos ratio Fset hNmass hFset hFfinite hFstrip hNupper hS
    Q orig a ha
  have h := hgood L hL τ κ N Label Item (P.withJetControl scale ratioBound hratio hcontrol) packets assigned
    hP horder alt hAlt T oldSlope R cone w hw hcone hwide hfrequency hwidth hscaleEq hX hZ
    angle small wide radius E J hangle hsmall hsmall1 hwideScale hwide1 hradius hlocal
    b hb hb1 hsupport hnear hfar v hv f hf hf1 hspectrum haltSpectrum hsep hJ hE
    hcondition l r hslopes u lip hu hlength witness hW hdisj hinside hclose hsize hSpos
    ratio Fset hNmass hFset hFfinite hFstrip hNupper hS
  exact h

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedSelectorJointGoodSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common fixed set for the actual original selector coefficients,
mask removal and the simultaneous direction count at the larger dilation.
All numerical choices precede the finite packet and top families. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem source_assigned_selector_joint_good_set (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (cStar cEta CEta cb Cb F : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hF : 0 ≤ F)
    (hgap : cStar < cEta*cb)
    (aWeight aw p s Hloss Lip : ℝ) (D K H J₀ : ℕ)
    (haWeight : 0 ≤ aWeight) (haw : 0 ≤ aw) (hp : 0 ≤ p) (hs : 0 ≤ s)
    (hHloss : 0 ≤ Hloss) (hLip : 0 ≤ Lip) (hD : 4 ≤ D) :
    ∃ A Cn Ct L0 : ℝ, aWeight < A ∧ 2 < A ∧ 0 < Cn ∧ 0 < Ct ∧ 2 ≤ L0 ∧
    ∀ L : ℝ, L0 ≤ L →
    ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
      (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [∀ j l, Fintype (Item j l)] (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ),
    ∀ (scale ratioBound : ℝ) (hratioBound : 1 ≤ ratioBound)
      (hcontrol : |scale/P.width| ≤ ratioBound),
      (P.withJetControl scale ratioBound hratioBound hcontrol).referenceEnvelopeConstant ≤ L^p →
      6+2*(8*D+1) ≤ P.order →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k,
        planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w : ℝ)
      (hw : 0 < w) (hcone : 0 ≤ cone) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
      (∀ top, P.width ≤ L^aWeight*(T top).width) →
      (∀ top, scale = 4*(L^aWeight*(T top).width)) →
      (∀ q ∈ packets,
        |P.actualX q.1 q.2.1 q.2.2-(T (assigned q)).x|+P.length q.1 ≤
          L^aWeight*(T (assigned q)).length) →
      (∀ q ∈ packets,
        |P.actualZ q.1 q.2.1 q.2.2+(oldSlope-(T (assigned q)).slope)*
          P.actualX q.1 q.2.1 q.2.2-
          ((T (assigned q)).y-(T (assigned q)).slope*(T (assigned q)).x)|+P.width ≤
            L^aWeight*(T (assigned q)).width) →
    ∀ (angle : τ → ℝ) (small wide radius : ℝ) (E J : ℕ),
      (∀ top, 0 < angle top) → 0 < small → small ≤ 1 →
      wide ≤ small*(2:ℝ)^J → 1 ≤ wide*((2:ℝ)^E)^4 → radius ≤ K →
      (∀ top j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l => oldSlope+P.rowSlope j l) (angle top*(2:ℝ)^j.val) H) →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) →
      (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        b j l k s ≠ 0 →
        |s-(oldSlope+P.rowSlope j l)| ≤ radius*(angle top*(2:ℝ)^j.val)) →
      (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        |s-(T top).slope| ≤ small*(angle top*(2:ℝ)^j.val) →
        ‖b j l k s-b j l k (T top).slope‖ ≤
          Lip*(|s-(T top).slope|/(angle top*(2:ℝ)^j.val))) →
      (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        (wide*((2:ℝ)^E)^4)*(angle top*(2:ℝ)^j.val) < |s-(T top).slope| →
        b j l k s = 0) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f →
      (∀ z, ‖f z‖ ≤ 1) →
      (∀ q ∈ packets, ∀ k xi eta,
        planarAngularFourier (P.physicalPacket oldSlope q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ q ∈ packets, ∀ k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket
          oldSlope q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ top j l, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        (∃ k, b j l k (T top).slope ≠ 0) →
        cb*w/P.length j ≤ |oldSlope+P.rowSlope j l-(T top).slope| ∧
          |oldSlope+P.rowSlope j l-(T top).slope| ≤ Cb*w/P.length j) →
      J ≤ J₀ → E = SourceParameters.stepExponent L*SourceParameters.blockCount L →
      (∀ q ∈ packets, P.referenceCondition oldSlope (T (assigned q)).slope
        (R (assigned q)) cone w q.1 q.2.1) →
    ∀ l r : ℝ, (∀ i, |(T i).slope| ≤ 1) →
    ∀ (u : Plane → ℝ), LipschitzWith 1 u → 600*(r-l) ≤ 1 →
    ∀ witness : τ → Set (ℝ×ℝ), (∀ i, MeasurableSet (witness i)) →
      (Pairwise fun i j => Disjoint (witness i) (witness j)) →
      (∀ i z, z ∈ witness i → z.1 ∈ Icc l r ∧ (T i).radius z ≤ L^aw) →
      (∀ i z, z ∈ witness i → |u (planeCoordinates z)-(T i).slope| ≤
        (T i).width/(12*(T i).length)) →
      (∀ i, ENNReal.ofReal (L^(-aw)*(T i).length*(T i).width) ≤
        (volume.prod volume) (witness i)) → 0 < ∑ i, (T i).area →
    ∀ (ratio : ℝ) (Fset : Set (ℝ×ℝ)), 0 < ratio → MeasurableSet Fset →
      (volume.prod volume) Fset ≠ ∞ →
      (∀ z ∈ Fset, z.1 ∈ Icc l r) → ratio ≤ Real.exp (2*L) →
      (∑ i, (T i).area) ≤ L^s*ratio^2*(volume.prod volume).real Fset →
    ∀ widthScale timeScale : ℝ,
      Real.exp (L^(9/10:ℝ)) ≤ widthScale →
      widthScale ≤ 2*Real.exp (L^(9/10:ℝ)) →
      0 ≤ timeScale → timeScale ≤ Real.exp (-(L^(97/100:ℝ))) →
      (∀ i, (T i).length ≤ timeScale) →
      (∀ i, (volume.prod volume) (witness i) ≠ ∞) →
      (∀ i z, z ∈ witness i → |u (planeCoordinates z)-(T i).slope| ≤ w/(T i).length) →
      (∀ i, (T i).width = widthScale*(T i).length*(w/(T i).length)) →
      let Q := fun top => (P.assignedTopFamily packets assigned top).referenceFamily
        oldSlope (T top).slope (R top) cone w F hw hcone hF hwide hfrequency
      let orig := fun top j (l : (Q top).labels j) =>
        ((P.assignedTopFamily packets assigned top).referenceOriginalLabel
          oldSlope (T top).slope (R top) cone w j l).val.2
      let a := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
        alt j (orig top j l) u.val k
      let ha := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
        hAlt j (orig top j l) u.val k
      ∃ G : Set (ℝ×ℝ), MeasurableSet G ∧ G ⊆ Fset ∧
        (volume.prod volume) (Fset\G) ≤ ENNReal.ofReal (L^(-Hloss)*(volume.prod volume).real Fset) ∧
        (∀ z ∈ G, (∑ i, (T i).weight (L^(A+2)) (D:ℝ) z) ≤ ratio*L^Cn) ∧
        (∀ top lower upper, lower ≤ upper → upper ≤ N → ∀ z ∈ G, ∀ yy,
          |yy-(z.2-(T top).slope*z.1)| ≤ (T top).width →
          let V := ((Q top).withProfile (a top) (ha top)).rawInterval
            (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig top j l) u.val)
            0 lower upper
          ‖V z.1 yy‖+(T top).width*‖covariantSignal P.frequency
            (fun k y => V z.1 y k) yy‖ ≤ L^(2*p+8)*((T top).weight (L^aWeight) (D:ℝ) z)^8) ∧
        let original := fun z => ∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q
        let masked := fun z => ∑ q ∈ packets, P.physicalMaskedValue alt hAlt oldSlope b v f
          (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z q
        IntegrableOn (fun z => ‖original z-masked z‖) G (volume.prod volume) ∧
        (∫ z in G, ‖original z-masked z‖ ∂volume.prod volume) ≤
          L^(-Hloss)*ratio*(volume.prod volume).real Fset ∧
        ∀ z ∈ G, ∀ rho : ℝ, 0 < rho → ∀ I : Finset τ,
          (∀ i ∈ I, (T i).radius z ≤ L^(A+2)) →
          (∀ i ∈ I, w/(T i).length ≤ rho/(SourceParameters.branching L)^2) →
          (∀ i ∈ I, ∀ j ∈ I, |(T i).slope-(T j).slope| ≤ SourceParameters.branching L*rho) →
          (∀ i ∈ I, ∀ j ∈ I, i ≠ j → rho ≤ |(T i).slope-(T j).slope|) →
          (I.card:ℝ) ≤ L^Ct/100 := by
  obtain ⟨A,Cn,Lmask,haA,hA,hCn,hLm,hmask⟩ := source_assigned_selector_mask_good_set_with_jet_control
    hVariation hLL cStar cEta CEta cb Cb F hcStar hcEta hCEta hcb hCb hF hgap
    aWeight aw p s (Hloss+1) Lip D K H J₀ haWeight haw hp hs (by linarith) hLip hD
  let pg := aw+A+4
  let tg := 2*aw+pg+2
  have hap : aw+1 ≤ pg := by dsimp [pg]; linarith
  have hkp : (A+2)+1 ≤ pg := by dsimp [pg]; linarith
  have ht : 2*aw+pg+1 ≤ tg := by dsimp [tg]; linarith
  obtain ⟨Lcount,hLcount⟩ := eventually_atTop.mp
    (eventually_source_simultaneous_count_universal 2 aw (A+2) pg tg 9 1 10 haw hap hkp ht
      (by norm_num) (by norm_num))
  obtain ⟨Larea,hLarea⟩ := eventually_atTop.mp (eventually_top_area_factor s Hloss)
  let L0 := max Lmask (max Lcount Larea)
  refine ⟨A,Cn,tg+4,L0,haA,hA,hCn,?_,hLm.trans (le_max_left _ _),?_⟩
  · dsimp [tg,pg]; linarith
  intro L hL τ κ _ _ N Label Item _ P packets assigned scale ratioBound hratioBound hcontrol hP horder alt hAlt T oldSlope R cone w
    hw hcone hwide hfrequency hwidth hscaleEq hX hZ angle small wide radius E J
    hangle hsmall hsmall1 hwideScale hwide1 hradius hlocal b hb hb1 hsupport hnear hfar
    v hv f hf hf1 hspectrum haltSpectrum hsep hJ hE hcondition l r hslopes u hu hlength
    witness hW hdisj hinside hclose hsize hSpos ratio Fset hratio hFset hFfinite hFstrip hNupper hS
    widthScale timeScale hwidthLow hwidthHigh htimeLow htimeHigh htopLength hWfinite hprecision hwidthExact
    Q orig a ha
  have hLmL : Lmask ≤ L := (le_max_left _ _).trans hL
  have hLcL : Lcount ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLaL : Larea ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hL2 : 2 ≤ L := hLm.trans hLmL
  have hLpos : 0 < L := by linarith
  have hlength' : 300*((2*(1:ℝ≥0):ℝ≥0):ℝ)*(r-l) ≤ 1 := by norm_num; exact hlength
  obtain ⟨G₁,hG₁,hG₁F,harea₁,hcount₁,htop₁,hint₁,herror₁⟩ :=
    hmask L hLmL τ κ N Label Item P packets assigned scale ratioBound hratioBound hcontrol hP horder alt hAlt T oldSlope R cone w
      hw hcone hwide hfrequency hwidth hscaleEq hX hZ
      angle small wide radius E J hangle hsmall hsmall1 hwideScale hwide1 hradius hlocal
      b hb hb1 hsupport hnear hfar v hv f hf hf1 hspectrum haltSpectrum hsep hJ hE
      hcondition l r hslopes u 1 hu hlength' witness hW hdisj hinside hclose hsize hSpos
      ratio Fset hratio hFset hFfinite hFstrip hNupper hS
  have huProd : LipschitzWith 2 (fun z => u (planeCoordinates z)) := by
    simpa only [mul_one] using product_slope_lipschitz u hu
  have hareaReal (i : τ) : L^(-aw)*(T i).length*(T i).width ≤ (volume.prod volume).real (witness i) := by
    have h := ENNReal.toReal_mono (hWfinite i) (hsize i)
    have hn : 0 ≤ L^(-aw)*(T i).length*(T i).width :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hLpos.le _) (T i).length_pos.le) (T i).width_pos.le
    rw [ENNReal.toReal_ofReal hn] at h
    exact h
  obtain ⟨bad,hbad,hbadfin,hbadarea,hseparated⟩ := hLcount L hLcL
    (fun z => u (planeCoordinates z)) huProd τ widthScale timeScale hwidthLow hwidthHigh
    htimeLow htimeHigh T (fun i => w/(T i).length) witness htopLength hW hWfinite
    (fun i z hz => (hinside i z hz).2) hareaReal
    (fun i z hz => by simpa only [one_mul] using hprecision i z hz)
    (fun i => (div_pos hw (T i).length_pos).le) hwidthExact
  have hbadArea : (volume.prod volume) bad ≤
      ENNReal.ofReal ((1/2)*L^(-Hloss)*(volume.prod volume).real Fset) := by
    have hr := top_area_discard_numeric L s Hloss ratio ((volume.prod volume).real Fset)
      (∑ i, (T i).area) hLpos hratio.le measureReal_nonneg hNupper hS (hLarea L hLaL)
    have hb : (volume.prod volume).real bad ≤ (1/2)*L^(-Hloss)*(volume.prod volume).real Fset := by
      apply le_trans ?_ hr
      simpa only [SlopeBox.area,mul_comm] using hbadarea
    rw [← ENNReal.ofReal_toReal hbadfin]
    exact ENNReal.ofReal_le_ofReal hb
  have hpower : L^(-(Hloss+1)) ≤ (1/2)*L^(-Hloss) := by
    have hi : L⁻¹ ≤ (1/2:ℝ) := by
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hL2
    calc
      _ = L^(-Hloss)*L⁻¹ := by rw [← Real.rpow_neg_one,← Real.rpow_add hLpos]; congr 1; ring
      _ ≤ L^(-Hloss)*(1/2) := mul_le_mul_of_nonneg_left hi (by positivity)
      _ = _ := mul_comm _ _
  let G := G₁ \ bad
  have hGG₁ : G ⊆ G₁ := sdiff_subset
  refine ⟨G,hG₁.diff hbad,hGG₁.trans hG₁F,?_,?_,?_,?_,?_,?_⟩
  · have hsub : Fset \ G ⊆ (Fset \ G₁) ∪ bad := by
      intro z hz
      by_cases hg : z ∈ G₁
      · exact Or.inr (by by_contra hn; exact hz.2 ⟨hg,hn⟩)
      · exact Or.inl ⟨hz.1,hg⟩
    calc
      _ ≤ (volume.prod volume) (Fset \ G₁)+(volume.prod volume) bad :=
        (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ ENNReal.ofReal ((1/2)*L^(-Hloss)*(volume.prod volume).real Fset)+
          ENNReal.ofReal ((1/2)*L^(-Hloss)*(volume.prod volume).real Fset) := add_le_add
        (harea₁.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hpower measureReal_nonneg))) hbadArea
      _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  · exact fun z hz => hcount₁ z (hGG₁ hz)
  · exact fun top lower upper hlu hup z hz => htop₁ top lower upper hlu hup z (hGG₁ hz)
  · exact hint₁.mono_set hGG₁
  · have herr := setIntegral_mono_set hint₁
      (Filter.Eventually.of_forall (fun z => norm_nonneg _))
      (Filter.Eventually.of_forall hGG₁)
    apply herr.trans (herror₁.trans ?_)
    have hh : L^(-(Hloss+1)) ≤ L^(-Hloss) := hpower.trans (by nlinarith [Real.rpow_nonneg hLpos.le (-Hloss)])
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hratio.le) measureReal_nonneg
  · intro z hz rho hrho I hsig hprec hspan hsep
    exact hseparated z hz.2 rho hrho I hsig hprec hspan hsep

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceWeightPointwiseBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary pointwise consequences of the actual top weights and the
polynomial count cutoff. They supply the uniform weight and logarithmic
mass bounds used in central interpolation and boundary averaging. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert

theorem SlopeBox.weight_le_two_rpow (T : SlopeBox) {K D : ℝ}
    (hK : 0 < K) (hD : 0 ≤ D) (z : ℝ×ℝ) : T.weight K D z ≤ (2:ℝ)^D := by
  unfold weight
  have hb : 1 ≤ 1+T.radius z/K := le_add_of_nonneg_right
    (div_nonneg (T.radius_nonnegative z) hK.le)
  exact mul_le_of_le_one_right (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_le_one_of_one_le_of_nonpos hb (neg_nonpos.mpr hD))

theorem SlopeBox.weight_mono_dilation (T : SlopeBox) {K K' D : ℝ}
    (hK : 0 < K) (hKK : K ≤ K') (hD : 0 ≤ D) (z : ℝ×ℝ) :
    T.weight K D z ≤ T.weight K' D z := by
  have hK' : 0 < K' := hK.trans_le hKK
  have hr := T.radius_nonnegative z
  have hb : 0 < 1+T.radius z/K' := by positivity
  unfold weight
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
  apply Real.rpow_le_rpow_of_nonpos hb _ (neg_nonpos.mpr hD)
  linarith [div_le_div_of_nonneg_left (T.radius_nonnegative z) hK hKK]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceWideLogMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's full disparity window reaches log ratio = 2L.
Its polynomial top-count factor therefore needs a third logarithmic
unit. The same phase subpower bound survives this extra fixed unit. -/
noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert
open PhaseCombinatorics

theorem eventually_count_log_bound_wide (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ n N : ℝ, n ≤ L^C*N → 0 < N → Real.log N ≤ 2*L →
      Real.log (max 1 n) ≤ 3*L := by
  have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero C 1 (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),
    ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with L hL hsmall
  intro n N hn hN hlog
  have hNexp : N ≤ Real.exp (2*L) := (Real.log_le_iff_le_exp hN).mp hlog
  have hpoly : L^C ≤ Real.exp L := by
    have h := mul_le_mul_of_nonneg_right hsmall.le (Real.exp_pos L).le
    simpa only [one_mul,neg_mul,one_mul,mul_assoc,← Real.exp_add,neg_add_cancel,
      Real.exp_zero,mul_one] using h
  have hexp : L^C*N ≤ Real.exp (3*L) := by
    calc
      _ ≤ Real.exp L*Real.exp (2*L) := mul_le_mul hpoly hNexp hN.le (Real.exp_pos _).le
      _ = _ := by rw [←Real.exp_add]; congr 1; ring
  have hmax : max 1 n ≤ Real.exp (3*L) := max_le
    (Real.one_le_exp (by linarith)) (hn.trans hexp)
  exact (Real.log_le_iff_le_exp (lt_of_lt_of_le zero_lt_one (le_max_left 1 n))).mpr hmax


end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedSelectorCentralGoodSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common set supplies the larger-weight concentration and logarithmic
count required by actual central recovery. The small jet control still
precedes the mask choice. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem source_assigned_selector_central_good_set (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (cStar cEta CEta cb Cb F : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hF : 0 ≤ F)
    (hgap : cStar < cEta*cb)
    (aWeight aw p s Hloss Lip : ℝ) (D K H J₀ : ℕ)
    (haWeight : 0 ≤ aWeight) (haw : 0 ≤ aw) (hp : 0 ≤ p) (hs : 0 ≤ s)
    (hHloss : 0 ≤ Hloss) (hLip : 0 ≤ Lip) (hD : 4 ≤ D) :
    ∃ A Cn Ct L0 : ℝ, aWeight < A ∧ 2 < A ∧ 0 < Cn ∧ 0 < Ct ∧ 2 ≤ L0 ∧
    ∀ L : ℝ, L0 ≤ L →
    ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
      (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [∀ j l, Fintype (Item j l)] (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ),
    ∀ (scale ratioBound : ℝ) (hratioBound : 1 ≤ ratioBound)
      (hcontrol : |scale/P.width| ≤ ratioBound),
      (P.withJetControl scale ratioBound hratioBound hcontrol).referenceEnvelopeConstant ≤ L^p →
      6+2*(8*D+1) ≤ P.order →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k,
        planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w : ℝ)
      (hw : 0 < w) (hcone : 0 ≤ cone) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
      (∀ top, P.width ≤ L^aWeight*(T top).width) →
      (∀ top, scale = 4*(L^aWeight*(T top).width)) →
      (∀ q ∈ packets,
        |P.actualX q.1 q.2.1 q.2.2-(T (assigned q)).x|+P.length q.1 ≤
          L^aWeight*(T (assigned q)).length) →
      (∀ q ∈ packets,
        |P.actualZ q.1 q.2.1 q.2.2+(oldSlope-(T (assigned q)).slope)*
          P.actualX q.1 q.2.1 q.2.2-
          ((T (assigned q)).y-(T (assigned q)).slope*(T (assigned q)).x)|+P.width ≤
            L^aWeight*(T (assigned q)).width) →
    ∀ (angle : τ → ℝ) (small wide radius : ℝ) (E J : ℕ),
      (∀ top, 0 < angle top) → 0 < small → small ≤ 1 →
      wide ≤ small*(2:ℝ)^J → 1 ≤ wide*((2:ℝ)^E)^4 → radius ≤ K →
      (∀ top j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l => oldSlope+P.rowSlope j l) (angle top*(2:ℝ)^j.val) H) →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) →
      (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        b j l k s ≠ 0 →
        |s-(oldSlope+P.rowSlope j l)| ≤ radius*(angle top*(2:ℝ)^j.val)) →
      (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        |s-(T top).slope| ≤ small*(angle top*(2:ℝ)^j.val) →
        ‖b j l k s-b j l k (T top).slope‖ ≤
          Lip*(|s-(T top).slope|/(angle top*(2:ℝ)^j.val))) →
      (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        (wide*((2:ℝ)^E)^4)*(angle top*(2:ℝ)^j.val) < |s-(T top).slope| →
        b j l k s = 0) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f →
      (∀ z, ‖f z‖ ≤ 1) →
      (∀ q ∈ packets, ∀ k xi eta,
        planarAngularFourier (P.physicalPacket oldSlope q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ q ∈ packets, ∀ k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket
          oldSlope q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ top j l, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        (∃ k, b j l k (T top).slope ≠ 0) →
        cb*w/P.length j ≤ |oldSlope+P.rowSlope j l-(T top).slope| ∧
          |oldSlope+P.rowSlope j l-(T top).slope| ≤ Cb*w/P.length j) →
      J ≤ J₀ → E = SourceParameters.stepExponent L*SourceParameters.blockCount L →
      (∀ q ∈ packets, P.referenceCondition oldSlope (T (assigned q)).slope
        (R (assigned q)) cone w q.1 q.2.1) →
    ∀ l r : ℝ, (∀ i, |(T i).slope| ≤ 1) →
    ∀ (u : Plane → ℝ), LipschitzWith 1 u → 600*(r-l) ≤ 1 →
    ∀ witness : τ → Set (ℝ×ℝ), (∀ i, MeasurableSet (witness i)) →
      (Pairwise fun i j => Disjoint (witness i) (witness j)) →
      (∀ i z, z ∈ witness i → z.1 ∈ Icc l r ∧ (T i).radius z ≤ L^aw) →
      (∀ i z, z ∈ witness i → |u (planeCoordinates z)-(T i).slope| ≤
        (T i).width/(12*(T i).length)) →
      (∀ i, ENNReal.ofReal (L^(-aw)*(T i).length*(T i).width) ≤
        (volume.prod volume) (witness i)) → 0 < ∑ i, (T i).area →
    ∀ (ratio : ℝ) (Fset : Set (ℝ×ℝ)), 0 < ratio → MeasurableSet Fset →
      (volume.prod volume) Fset ≠ ∞ →
      (∀ z ∈ Fset, z.1 ∈ Icc l r) → ratio ≤ Real.exp (2*L) → Real.log ratio ≤ 2*L →
      (∑ i, (T i).area) ≤ L^s*ratio^2*(volume.prod volume).real Fset →
    ∀ widthScale timeScale : ℝ,
      Real.exp (L^(9/10:ℝ)) ≤ widthScale →
      widthScale ≤ 2*Real.exp (L^(9/10:ℝ)) →
      0 ≤ timeScale → timeScale ≤ Real.exp (-(L^(97/100:ℝ))) →
      (∀ i, (T i).length ≤ timeScale) →
      (∀ i, (volume.prod volume) (witness i) ≠ ∞) →
      (∀ i z, z ∈ witness i → |u (planeCoordinates z)-(T i).slope| ≤ w/(T i).length) →
      (∀ i, (T i).width = widthScale*(T i).length*(w/(T i).length)) →
      let Q := fun top => (P.assignedTopFamily packets assigned top).referenceFamily
        oldSlope (T top).slope (R top) cone w F hw hcone hF hwide hfrequency
      let orig := fun top j (l : (Q top).labels j) =>
        ((P.assignedTopFamily packets assigned top).referenceOriginalLabel
          oldSlope (T top).slope (R top) cone w j l).val.2
      let a := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
        alt j (orig top j l) u.val k
      let ha := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
        hAlt j (orig top j l) u.val k
      ∃ G : Set (ℝ×ℝ), MeasurableSet G ∧ G ⊆ Fset ∧
        (volume.prod volume) (Fset\G) ≤ ENNReal.ofReal (L^(-Hloss)*(volume.prod volume).real Fset) ∧
        (∀ z ∈ G, ∀ i, (T i).weight (L^(A+2)) (D:ℝ) z ≤ (2:ℝ)^D) ∧
        (∀ z ∈ G, Real.log (max 1 (∑ i, (T i).weight (L^(A+2)) (D:ℝ) z)) ≤ 3*L) ∧
        (∀ z ∈ G, (∑ i, (T i).weight (L^(A+2)) (D:ℝ) z) ≤ ratio*L^Cn) ∧
        (∀ top lower upper, lower ≤ upper → upper ≤ N → ∀ z ∈ G, ∀ yy,
          |yy-(z.2-(T top).slope*z.1)| ≤ (T top).width →
          let V := ((Q top).withProfile (a top) (ha top)).rawInterval
            (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig top j l) u.val)
            0 lower upper
          ‖V z.1 yy‖+(T top).width*‖covariantSignal P.frequency
            (fun k y => V z.1 y k) yy‖ ≤ L^(2*p+8)*((T top).weight (L^(A+2)) (D:ℝ) z)^8) ∧
        let original := fun z => ∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q
        let masked := fun z => ∑ q ∈ packets, P.physicalMaskedValue alt hAlt oldSlope b v f
          (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z q
        IntegrableOn (fun z => ‖original z-masked z‖) G (volume.prod volume) ∧
        (∫ z in G, ‖original z-masked z‖ ∂volume.prod volume) ≤
          L^(-Hloss)*ratio*(volume.prod volume).real Fset ∧
        ∀ z ∈ G, ∀ rho : ℝ, 0 < rho → ∀ I : Finset τ,
          (∀ i ∈ I, (T i).radius z ≤ L^(A+2)) →
          (∀ i ∈ I, w/(T i).length ≤ rho/(SourceParameters.branching L)^2) →
          (∀ i ∈ I, ∀ j ∈ I, |(T i).slope-(T j).slope| ≤ SourceParameters.branching L*rho) →
          (∀ i ∈ I, ∀ j ∈ I, i ≠ j → rho ≤ |(T i).slope-(T j).slope|) →
          (I.card:ℝ) ≤ L^Ct/100 := by
  obtain ⟨A,Cn,Ct,Lbase,haA,hA,hCn,hCt,hLbase,hjoint⟩ := source_assigned_selector_joint_good_set
    hVariation hLL cStar cEta CEta cb Cb F hcStar hcEta hCEta hcb hCb hF hgap
    aWeight aw p s Hloss Lip D K H J₀ haWeight haw hp hs hHloss hLip hD
  obtain ⟨Llog,hLlog⟩ := eventually_atTop.mp (eventually_count_log_bound_wide Cn)
  refine ⟨A,Cn,Ct,max Lbase Llog,haA,hA,hCn,hCt,
    hLbase.trans (le_max_left _ _),?_⟩
  intro L hL τ κ _ _ N Label Item _ P packets assigned scale ratioBound hratioBound hcontrol
    hP horder alt hAlt T oldSlope R cone w hw hcone hwide hfrequency hwidth hscaleEq hX hZ
    angle small wide radius E J hangle hsmall hsmall1 hwideScale hwide1 hradius hlocal
    b hb hb1 hsupport hnear hfar v hv f hf hf1 hspectrum haltSpectrum hsep hJ hE hcondition
    l r hslopes u hu hlength witness hW hdisj hinside hclose hsize hSpos ratio Fset hratio
    hFset hFfinite hFstrip hNupper hlogRatio hS widthScale timeScale hwidthLow hwidthHigh
    htimeLow htimeHigh htopLength hWfinite hprecision hwidthExact Q orig a ha
  have hLb : Lbase ≤ L := (le_max_left _ _).trans hL
  have hLl : Llog ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := by linarith [hLbase.trans hLb]
  have hLpos : 0 < L := zero_lt_one.trans_le hL1
  have hKpos : 0 < L^(A+2) := Real.rpow_pos_of_pos hLpos _
  have hKsmall : 0 < L^aWeight := Real.rpow_pos_of_pos hLpos _
  have hDD : 0 ≤ (D:ℝ) := Nat.cast_nonneg _
  obtain ⟨G,hG,hGF,harea,hcount,hconc,hint,herror,hseparated⟩ := hjoint L hLb τ κ N Label Item
    P packets assigned scale ratioBound hratioBound hcontrol hP horder alt hAlt T oldSlope R cone w
    hw hcone hwide hfrequency hwidth hscaleEq hX hZ angle small wide radius E J hangle hsmall
    hsmall1 hwideScale hwide1 hradius hlocal b hb hb1 hsupport hnear hfar v hv f hf hf1
    hspectrum haltSpectrum hsep hJ hE hcondition l r hslopes u hu hlength witness hW hdisj
    hinside hclose hsize hSpos ratio Fset hratio hFset hFfinite hFstrip hNupper hS
    widthScale timeScale hwidthLow hwidthHigh htimeLow htimeHigh htopLength hWfinite
    hprecision hwidthExact
  refine ⟨G,hG,hGF,harea,?_,?_,hcount,?_,hint,herror,hseparated⟩
  · intro z _ i
    simpa only [Real.rpow_natCast] using (T i).weight_le_two_rpow hKpos hDD z
  · intro z hz
    apply hLlog L hLl _ ratio _ hratio hlogRatio
    simpa only [mul_comm] using hcount z hz
  · intro top lower upper hlu hup z hz yy hyy
    have hwgt := (T top).weight_mono_dilation hKsmall
      (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith : aWeight ≤ A+2)) hDD z
    exact (hconc top lower upper hlu hup z hz yy hyy).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ ((T top).weight_pos hKsmall (D:ℝ) z).le hwgt 8)
        (Real.rpow_nonneg hLpos.le _))

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataDensityForest
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary density produces the literal top assignment and witnesses
needed for packet concentration. No disjoint-witness premise is imposed. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem PacketDensityForest.area_budget
    {P : PacketLatticeData N κ Label Item} {packets : Finset P.PacketIndex}
    {oldSlope L a cone w tau : ℝ} {E : Set (ℝ×ℝ)} {u : ℝ×ℝ → ℝ}
    (forest : PacketDensityForest P packets oldSlope L a cone w tau E u)
    (hL : 2 ≤ L) (ratio Fmass : ℝ) (hF : 0 ≤ Fmass)
    (hEF : (volume.prod volume).real E ≤ ratio^2*Fmass) :
    (∑ i, (forest.top i).area) ≤ L^(a+1)*ratio^2*Fmass := by
  have hLp : 0 < L := by linarith
  calc
    _ ≤ 2*L^a*(volume.prod volume).real E := forest.area
    _ ≤ 2*L^a*(ratio^2*Fmass) := mul_le_mul_of_nonneg_left hEF (by positivity)
    _ ≤ (L*L^a)*(ratio^2*Fmass) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hLp.le _))
        (mul_nonneg (sq_nonneg _) hF)
    _ = _ := by rw [Real.rpow_add hLp,Real.rpow_one]; ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataJetBudget
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smaller concentration normalization has a polynomial bound that
does not involve the later mask exponent. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem smallJetControl_referenceEnvelopeConstant (P : PacketLatticeData N κ Label Item)
    {L a p width : ℝ} (hL : 16 ≤ L) (ha : 0 ≤ a)
    (hw : 0 ≤ width) (hwidth : width ≤ P.width)
    (hprofile : (2^P.order*P.profileBound)*3^(2*P.order) ≤ L^p) :
    (P.withJetControl (4*(L^a*width)) (4*L^a)
      (smallJetRatio_ge_one (by linarith) ha)
      (P.smallJetScale_control (by linarith) hw hwidth)).referenceEnvelopeConstant ≤
      L^(p+2*a+1) := by
  have hL0 : 0 < L := by linarith
  rw [withJetControl_referenceEnvelopeConstant]
  calc
    _ = ((2^P.order*P.profileBound)*3^(2*P.order))*(16*(L^a)^2) := by ring
    _ ≤ L^p*(16*(L^a)^2) := mul_le_mul_of_nonneg_right hprofile (by positivity)
    _ ≤ L^p*(L*(L^a)^2) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hL (sq_nonneg _)) (Real.rpow_nonneg hL0.le _)
    _ = L^(p+2*a+1) := by
      calc
        _ = L^p*(L^(1:ℝ)*(L^a)^(2:ℝ)) := by rw [Real.rpow_one,Real.rpow_two]
        _ = L^(p+(1+a*2)) := by
          rw [← Real.rpow_mul hL0.le, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
        _ = _ := by congr 1; ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataDensityCentralGoodSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual density forest supplies every geometric and witness input
of the common concentration, mask-removal and direction-count theorem.
The small auxiliary jet bound is derived from the raw profile bound. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem source_density_selector_central_good_set (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (cStar cEta CEta cb Cb F : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hF : 0 ≤ F)
    (hgap : cStar < cEta*cb)
    (aDensity p0 Hloss Lip : ℝ) (D K H J₀ : ℕ)
    (haDensity : 0 ≤ aDensity) (hp0 : 0 ≤ p0)
    (hHloss : 0 ≤ Hloss) (hLip : 0 ≤ Lip) (hD : 4 ≤ D) :
    ∃ A Cn Ct L0 : ℝ, aDensity+3 < A ∧ 2 < A ∧ 0 < Cn ∧ 0 < Ct ∧ 16 ≤ L0 ∧
    ∀ L : ℝ, L0 ≤ L →
    ∀ (κ : Type) [Fintype κ]
      (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [∀ j l, Fintype (Item j l)] (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (oldSlope cone w tau : ℝ)
      (Eset : Set (ℝ×ℝ)) (field : Plane → ℝ)
      (forest : PacketDensityForest P packets oldSlope L aDensity cone w tau Eset
        (fun z => field (planeCoordinates z))),
      let T := forest.top
      let assigned := forest.assigned
      let R := fun i => (T i).length
      (2^P.order*P.profileBound)*3^(2*P.order) ≤ L^p0 →
      6+2*(8*D+1) ≤ P.order →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k,
        planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (hw : 0 < w) (hcone : 0 ≤ cone) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
    ∀ (angle : forest.keepers → ℝ) (small wide radius : ℝ) (E J : ℕ),
      (∀ top, 0 < angle top) → 0 < small → small ≤ 1 →
      wide ≤ small*(2:ℝ)^J → 1 ≤ wide*((2:ℝ)^E)^4 → radius ≤ K →
      (∀ top j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l => oldSlope+P.rowSlope j l) (angle top*(2:ℝ)^j.val) H) →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) →
      (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        b j l k s ≠ 0 →
        |s-(oldSlope+P.rowSlope j l)| ≤ radius*(angle top*(2:ℝ)^j.val)) →
      (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        |s-(T top).slope| ≤ small*(angle top*(2:ℝ)^j.val) →
        ‖b j l k s-b j l k (T top).slope‖ ≤
          Lip*(|s-(T top).slope|/(angle top*(2:ℝ)^j.val))) →
      (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        (wide*((2:ℝ)^E)^4)*(angle top*(2:ℝ)^j.val) < |s-(T top).slope| →
        b j l k s = 0) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f →
      (∀ z, ‖f z‖ ≤ 1) →
      (∀ q ∈ packets, ∀ k xi eta,
        planarAngularFourier (P.physicalPacket oldSlope q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ q ∈ packets, ∀ k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket
          oldSlope q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ top j l, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        (∃ k, b j l k (T top).slope ≠ 0) →
        cb*w/P.length j ≤ |oldSlope+P.rowSlope j l-(T top).slope| ∧
          |oldSlope+P.rowSlope j l-(T top).slope| ≤ Cb*w/P.length j) →
      J ≤ J₀ → E = SourceParameters.stepExponent L*SourceParameters.blockCount L →
    ∀ l r : ℝ, (∀ i, |(T i).slope| ≤ 1) →
      LipschitzWith 1 field → 600*(r-l) ≤ 1 →
      (∀ z ∈ Eset, z.1 ∈ Icc l r) →
    ∀ (ratio : ℝ) (Fset : Set (ℝ×ℝ)), 0 < ratio → MeasurableSet Fset →
      (volume.prod volume) Fset ≠ ∞ →
      (∀ z ∈ Fset, z.1 ∈ Icc l r) → ratio ≤ Real.exp (2*L) → Real.log ratio ≤ 2*L →
      (volume.prod volume).real Eset ≤ ratio^2*(volume.prod volume).real Fset →
    ∀ widthScale : ℝ,
      Real.exp (L^(9/10:ℝ)) ≤ widthScale →
      widthScale ≤ 2*Real.exp (L^(9/10:ℝ)) →
      0 ≤ tau → tau ≤ Real.exp (-(L^(97/100:ℝ))) →
      P.width = widthScale*w →
      let Q := fun top => (P.assignedTopFamily packets assigned top).referenceFamily
        oldSlope (T top).slope (R top) cone w F hw hcone hF hwide hfrequency
      let orig := fun top j (l : (Q top).labels j) =>
        ((P.assignedTopFamily packets assigned top).referenceOriginalLabel
          oldSlope (T top).slope (R top) cone w j l).val.2
      let a := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
        alt j (orig top j l) u.val k
      let ha := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
        hAlt j (orig top j l) u.val k
      ∃ G : Set (ℝ×ℝ), MeasurableSet G ∧ G ⊆ Fset ∧
        (volume.prod volume) (Fset\G) ≤ ENNReal.ofReal (L^(-Hloss)*(volume.prod volume).real Fset) ∧
        (∀ z ∈ G, ∀ i, (T i).weight (L^(A+2)) (D:ℝ) z ≤ (2:ℝ)^D) ∧
        (∀ z ∈ G, Real.log (max 1 (∑ i, (T i).weight (L^(A+2)) (D:ℝ) z)) ≤ 3*L) ∧
        (∀ z ∈ G, (∑ i, (T i).weight (L^(A+2)) (D:ℝ) z) ≤ ratio*L^Cn) ∧
        (∀ top lower upper, lower ≤ upper → upper ≤ N → ∀ z ∈ G, ∀ yy,
          |yy-(z.2-(T top).slope*z.1)| ≤ (T top).width →
          let V := ((Q top).withProfile (a top) (ha top)).rawInterval
            (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig top j l) u.val)
            0 lower upper
          ‖V z.1 yy‖+(T top).width*‖covariantSignal P.frequency
            (fun k y => V z.1 y k) yy‖ ≤ L^(2*(p0+2*(aDensity+3)+1)+8)*((T top).weight (L^(A+2)) (D:ℝ) z)^8) ∧
        let original := fun z => ∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q
        let masked := fun z => ∑ q ∈ packets, P.physicalMaskedValue alt hAlt oldSlope b v f
          (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z q
        IntegrableOn (fun z => ‖original z-masked z‖) G (volume.prod volume) ∧
        (∫ z in G, ‖original z-masked z‖ ∂volume.prod volume) ≤
          L^(-Hloss)*ratio*(volume.prod volume).real Fset ∧
        ∀ z ∈ G, ∀ rho : ℝ, 0 < rho → ∀ I : Finset forest.keepers,
          (∀ i ∈ I, (T i).radius z ≤ L^(A+2)) →
          (∀ i ∈ I, w/(T i).length ≤ rho/(SourceParameters.branching L)^2) →
          (∀ i ∈ I, ∀ j ∈ I, |(T i).slope-(T j).slope| ≤ SourceParameters.branching L*rho) →
          (∀ i ∈ I, ∀ j ∈ I, i ≠ j → rho ≤ |(T i).slope-(T j).slope|) →
          (I.card:ℝ) ≤ L^Ct/100 := by
  obtain ⟨A,Cn,Ct,Lbase,haA,hA,hCn,hCt,_hLbase,hmain⟩ := source_assigned_selector_central_good_set
    hVariation hLL cStar cEta CEta cb Cb F hcStar hcEta hCEta hcb hCb hF hgap
    (aDensity+3) (aDensity+2) (p0+2*(aDensity+3)+1) (aDensity+1) Hloss Lip D K H J₀
    (by linarith) (by linarith) (by linarith) (by linarith) hHloss hLip hD
  refine ⟨A,Cn,Ct,max Lbase 16,haA,hA,hCn,hCt,le_max_right _ _,?_⟩
  intro L hL κ _ N Label Item _ P packets oldSlope cone w tau Eset field forest T assigned R
    hprofile horder alt hAlt hw hcone hwide hfrequency
    angle small wide radius E J hangle hsmall hsmall1 hwideScale hwide1 hradius hlocal
    b hb hb1 hsupport hnear hfar v hv f hf hf1 hspectrum haltSpectrum hsep hJ hE
    l r hslopes hfield hlength hEstrip ratio Fset hratio hFset hFfinite hFstrip hNupper hlogRatio hEF
    widthScale hwidthLow hwidthHigh htimeLow htimeHigh hwidthExact
  have hLb : Lbase ≤ L := (le_max_left _ _).trans hL
  have hL16 : 16 ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hP := P.smallJetControl_referenceEnvelopeConstant hL16 (by linarith : 0 ≤ aDensity+3)
    P.width_pos.le (le_refl P.width) hprofile
  have hwidth (i : forest.keepers) : P.width ≤ L^(aDensity+3)*(T i).width := by
    rw [forest.width]
    exact le_mul_of_one_le_left P.width_pos.le (Real.one_le_rpow hL1 (by linarith))
  have hscale (i : forest.keepers) : 4*(L^(aDensity+3)*P.width) =
      4*(L^(aDensity+3)*(T i).width) := by rw [forest.width]
  have hS : (∑ i, (T i).area) ≤ L^(aDensity+1)*ratio^2*(volume.prod volume).real Fset :=
    forest.area_budget (by linarith) ratio _ measureReal_nonneg hEF
  have hwidthIdentity (i : forest.keepers) : (T i).width =
      widthScale*(T i).length*(w/(T i).length) := by
    rw [forest.width,hwidthExact]
    field_simp [(T i).length_pos.ne']
  exact hmain L hLb forest.keepers κ N Label Item P packets assigned
    (4*(L^(aDensity+3)*P.width)) (4*L^(aDensity+3))
    (smallJetRatio_ge_one hL1 (by linarith))
    (P.smallJetScale_control hLp P.width_pos.le (le_refl P.width)) hP horder
    alt hAlt T oldSlope R cone w hw hcone hwide hfrequency hwidth hscale
    forest.horizontal forest.transverse angle small wide radius E J hangle hsmall hsmall1
    hwideScale hwide1 hradius hlocal b hb hb1 hsupport hnear hfar v hv f hf hf1
    hspectrum haltSpectrum hsep hJ hE forest.reference l r hslopes field hfield hlength
    forest.witness forest.measurable forest.disjoint
    (fun i z hz => ⟨hEstrip z (forest.subset i hz),forest.radius i z hz⟩)
    forest.close forest.mass forest.area_pos ratio Fset hratio hFset hFfinite hFstrip hNupper
    hlogRatio hS widthScale tau hwidthLow hwidthHigh htimeLow htimeHigh forest.short
    forest.finite forest.precision hwidthIdentity

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataRecenteredSelector
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selector mesh and physical centers survive exact recentering.
Only selected items enter the packet-top and mask-cone conclusions. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem reference_angular_mesh (w : ℝ) (j : Fin N) :
    (w/P.topLength)*(2:ℝ)^j.val = w/P.length j := by
  unfold length
  field_simp

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTotalWeightBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two different mass budgets used in the assembly: integrating
the top count on the testing set costs N|F|, whereas integrating all
weights on the plane costs N²|F|. Their polynomial losses are explicit. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace LipschitzHilbert

theorem eventually_source_global_weight_integral (D k s : ℝ) (_hD : 2 < D) :
    ∀ᶠ L : ℝ in atTop, ∀ (τ : Type*) (tops : Finset τ) (T : τ → SlopeBox)
      (Nmass Fmass : ℝ), 0 ≤ Nmass → 0 ≤ Fmass →
      (∑ t ∈ tops, (T t).area) ≤ L^s*Nmass^2*Fmass →
      (∑ t ∈ tops, ∫ x, (T t).weight (L^k) D x ∂volume.prod volume) ≤
        L^(s+2*k+1)*Nmass^2*Fmass := by
  let C := (2:ℝ)^D*∫ x, topProfile D x ∂volume.prod volume
  have hC : 0 ≤ C := mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (integral_nonneg (topProfile_nonnegative D))
  filter_upwards [eventually_ge_atTop (max 1 C)] with L hL
  intro τ tops T Nmass Fmass hN hF harea
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hCL : C ≤ L := (le_max_right _ _).trans hL
  have hK : 0 < L^k := Real.rpow_pos_of_pos hL0 _
  have heq : (∑ t ∈ tops, ∫ x, (T t).weight (L^k) D x ∂volume.prod volume) =
      C*(L^k)^2*(∑ t ∈ tops, (T t).area) := by
    simp_rw [SlopeBox.integral_weight _ hK D]
    unfold SlopeBox.area
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    dsimp only [C]
    ring
  have hpower : L*(L^k)^2*L^s = L^(s+2*k+1) := by
    calc
      _ = L^((1:ℝ))*((L^k)^((2:ℝ)))*L^s := by rw [Real.rpow_one,Real.rpow_two]
      _ = L^(1+k*2+s) := by rw [←Real.rpow_mul hL0.le,←Real.rpow_add hL0,←Real.rpow_add hL0]
      _ = _ := by congr 1; ring
  rw [heq]
  calc
    _ ≤ C*(L^k)^2*(L^s*Nmass^2*Fmass) :=
      mul_le_mul_of_nonneg_left harea (mul_nonneg hC (sq_nonneg _))
    _ ≤ L*(L^k)^2*(L^s*Nmass^2*Fmass) := by gcongr
    _ = _ := by rw [show L*(L^k)^2*(L^s*Nmass^2*Fmass) =
        (L*(L^k)^2*L^s)*Nmass^2*Fmass by ring,hpower]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataDensityJetNormalization
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The late mask normalization preserves the actual density forest,
physical packet sums and masks. Its analytic constant has an explicit
polynomial bound after the mask exponent has been chosen. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem maskJetControl_referenceEnvelopeConstant (P : PacketLatticeData N κ Label Item)
    {L A p F cone : ℝ} (hL : 16 ≤ L) (hA : 0 ≤ A)
    (hF : 0 ≤ F) (hcone : 0 ≤ cone) (hfactor : F*cone+2 ≤ L)
    (hprofile : (2^P.order*P.profileBound)*3^(2*P.order) ≤ L^p) :
    (F*cone+2)*(P.withJetControl (4*(L^(A+2)*P.width)) (4*L^(A+2))
      (smallJetRatio_ge_one (by linarith) (by linarith))
      (P.smallJetScale_control (by linarith) P.width_pos.le (le_refl P.width))).referenceEnvelopeConstant ≤
      L^(p+2*(A+2)+2) := by
  have hLp : 0 < L := by linarith
  have h := P.smallJetControl_referenceEnvelopeConstant hL (by linarith : 0 ≤ A+2)
    P.width_pos.le (le_refl P.width) hprofile
  calc
    _ ≤ (F*cone+2)*L^(p+2*(A+2)+1) := mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ L*L^(p+2*(A+2)+1) := mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hLp.le _)
    _ = L^(p+2*(A+2)+2) := by
      conv_lhs => lhs; rw [← Real.rpow_one L]
      rw [← Real.rpow_add hLp]
      congr 1
      ring

theorem mask_referenceEnvelopeConstant_of_ratio (P : PacketLatticeData N κ Label Item)
    {L A p F cone : ℝ} (hL : 16 ≤ L) (hA : 0 ≤ A)
    (hF : 0 ≤ F) (hcone : 0 ≤ cone) (hfactor : F*cone+2 ≤ L)
    (hratio : P.ratioBound = 4*L^(A+2))
    (hprofile : (2^P.order*P.profileBound)*3^(2*P.order) ≤ L^p) :
    (F*cone+2)*P.referenceEnvelopeConstant ≤ L^(p+2*(A+2)+2) := by
  have h := P.maskJetControl_referenceEnvelopeConstant hL hA hF hcone hfactor hprofile
  simpa only [PacketLatticeData.referenceEnvelopeConstant,withJetControl,hratio] using h

theorem PacketDensityForest.mask_geometry
    {P : PacketLatticeData N κ Label Item} {packets : Finset P.PacketIndex}
    {oldSlope L a cone w tau A : ℝ} {E : Set (ℝ×ℝ)} {u : ℝ×ℝ → ℝ}
    (forest : PacketDensityForest P packets oldSlope L a cone w tau E u)
    (hL : 1 ≤ L) (hA : a+3 ≤ A+2) :
    (∀ q ∈ packets,
      |P.actualX q.1 q.2.1 q.2.2-(forest.top (forest.assigned q)).x|+P.length q.1 ≤
        L^(A+2)*(forest.top (forest.assigned q)).length) ∧
    (∀ q ∈ packets,
      |P.actualZ q.1 q.2.1 q.2.2+(oldSlope-(forest.top (forest.assigned q)).slope)*
        P.actualX q.1 q.2.1 q.2.2-
        ((forest.top (forest.assigned q)).y-
          (forest.top (forest.assigned q)).slope*(forest.top (forest.assigned q)).x)|+P.width ≤
        L^(A+2)*(forest.top (forest.assigned q)).width) := by
  have hp := Real.rpow_le_rpow_of_exponent_le hL hA
  exact ⟨fun q hq => (forest.horizontal q hq).trans
    (mul_le_mul_of_nonneg_right hp (forest.top (forest.assigned q)).length_pos.le),
    fun q hq => (forest.transverse q hq).trans
      (mul_le_mul_of_nonneg_right hp (forest.top (forest.assigned q)).width_pos.le)⟩

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataDensitySelectorGoodSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Specialize common-set concentration to the manuscript's original
physical selector mesh, support, and Lipschitz bounds. This step precedes
popular recovery and introduces no extra selector assumptions. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

private theorem selector_far_of_reference {N : ℕ} {κ : Type}
    {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
    [Fintype κ] [∀ j l, Fintype (Item j l)]
    (P : PacketLatticeData N κ Label Item)
    (oldSlope t R cone w cutoff : ℝ) (hw : 0 < w) (hcut : 2*cone ≤ cutoff)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hsupport : ∀ j l k s, b j l k s ≠ 0 →
      |s-(oldSlope+P.rowSlope j l)| ≤ cone*(w/P.length j))
    (j : Fin N) (l : P.labels j) (k : κ) (s : ℝ)
    (hcondition : P.referenceCondition oldSlope t R cone w j l)
    (hs : cutoff*((w/P.topLength)*(2:ℝ)^j.val) < |s-t|) : b j l k s = 0 := by
  by_contra hn
  rw [P.reference_angular_mesh w j] at hs
  have ht : |s-t| ≤ (2*cone)*(w/P.length j) := by
    calc
      _ ≤ |s-(oldSlope+P.rowSlope j l)|+|oldSlope+P.rowSlope j l-t| := abs_sub_le _ _ _
      _ ≤ cone*(w/P.length j)+cone*w/P.length j := add_le_add (hsupport j l k s hn) hcondition.2
      _ = _ := by ring
  exact (not_lt_of_ge (ht.trans (mul_le_mul_of_nonneg_right hcut
    (div_pos hw (P.length_pos j)).le))) hs

theorem source_density_selector_good_set (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (cStar cEta CEta cb Cb F cone : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hF : 0 ≤ F)
    (hcone : 0 ≤ cone) (hgap : cStar < cEta*cb)
    (aDensity p0 Hloss Lip : ℝ) (D K H J₀ : ℕ)
    (haDensity : 0 ≤ aDensity) (hp0 : 0 ≤ p0)
    (hHloss : 0 ≤ Hloss) (hLip : 0 ≤ Lip) (hD : 4 ≤ D)
    (hconeK : cone ≤ K) (hJ : 2*cone+1 ≤ (2:ℝ)^J₀) :
    ∃ A Cn Ct L0 : ℝ, aDensity+3 < A ∧ 2 < A ∧ 0 < Cn ∧ 0 < Ct ∧ 16 ≤ L0 ∧
    ∀ L : ℝ, L0 ≤ L →
    ∀ (κ : Type) [Fintype κ]
      (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [∀ j l, Fintype (Item j l)] (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (oldSlope w tau : ℝ)
      (Eset : Set (ℝ×ℝ)) (field : Plane → ℝ)
      (forest : PacketDensityForest P packets oldSlope L aDensity cone w tau Eset
        (fun z => field (planeCoordinates z))),
      let T := forest.top
      let assigned := forest.assigned
      let R := fun i => (T i).length
      (2^P.order*P.profileBound)*3^(2*P.order) ≤ L^p0 →
      6+2*(8*D+1) ≤ P.order →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k,
        planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (hw : 0 < w) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) →
      (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 →
        |s-(oldSlope+P.rowSlope j l)| ≤ cone*(w/P.length j)) →
      (∀ j l k s t, ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(w/P.length j))) →
      (∀ j l k s, b j l k s ≠ 0 →
        cb*w/P.length j ≤ |s-(oldSlope+P.rowSlope j l)| ∧
          |s-(oldSlope+P.rowSlope j l)| ≤ Cb*w/P.length j) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => oldSlope+P.rowSlope j l) (w/P.length j) H) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f →
      (∀ z, ‖f z‖ ≤ 1) →
      (∀ q ∈ packets, ∀ k xi eta,
        planarAngularFourier (P.physicalPacket oldSlope q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ q ∈ packets, ∀ k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket
          oldSlope q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
    ∀ l r : ℝ, (∀ i, |(T i).slope| ≤ 1) →
      LipschitzWith 1 field → 600*(r-l) ≤ 1 →
      (∀ z ∈ Eset, z.1 ∈ Icc l r) →
    ∀ (ratio : ℝ) (Fset : Set (ℝ×ℝ)), 0 < ratio → MeasurableSet Fset →
      (volume.prod volume) Fset ≠ ∞ →
      (∀ z ∈ Fset, z.1 ∈ Icc l r) → ratio ≤ Real.exp (2*L) → Real.log ratio ≤ 2*L →
      (volume.prod volume).real Eset ≤ ratio^2*(volume.prod volume).real Fset →
    ∀ widthScale : ℝ,
      Real.exp (L^(9/10:ℝ)) ≤ widthScale →
      widthScale ≤ 2*Real.exp (L^(9/10:ℝ)) →
      0 ≤ tau → tau ≤ Real.exp (-(L^(97/100:ℝ))) →
      P.width = widthScale*w →
      let Q := fun top => (P.assignedTopFamily packets assigned top).referenceFamily
        oldSlope (T top).slope (R top) cone w F hw hcone hF hwide hfrequency
      let orig := fun top j (l : (Q top).labels j) =>
        ((P.assignedTopFamily packets assigned top).referenceOriginalLabel
          oldSlope (T top).slope (R top) cone w j l).val.2
      let a := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
        alt j (orig top j l) u.val k
      let ha := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
        hAlt j (orig top j l) u.val k
      ∃ G : Set (ℝ×ℝ), MeasurableSet G ∧ G ⊆ Fset ∧
        (volume.prod volume) (Fset\G) ≤ ENNReal.ofReal (L^(-Hloss)*(volume.prod volume).real Fset) ∧
        (∀ z ∈ G, ∀ i, (T i).weight (L^(A+2)) (D:ℝ) z ≤ (2:ℝ)^D) ∧
        (∀ z ∈ G, Real.log (max 1 (∑ i, (T i).weight (L^(A+2)) (D:ℝ) z)) ≤ 3*L) ∧
        (∀ z ∈ G, (∑ i, (T i).weight (L^(A+2)) (D:ℝ) z) ≤ ratio*L^Cn) ∧
        (∀ top lower upper, lower ≤ upper → upper ≤ N → ∀ z ∈ G, ∀ yy,
          |yy-(z.2-(T top).slope*z.1)| ≤ (T top).width →
          let V := ((Q top).withProfile (a top) (ha top)).rawInterval
            (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig top j l) u.val)
            0 lower upper
          ‖V z.1 yy‖+(T top).width*‖covariantSignal P.frequency
            (fun k y => V z.1 y k) yy‖ ≤ L^(2*(p0+2*(aDensity+3)+1)+8)*((T top).weight (L^(A+2)) (D:ℝ) z)^8) ∧
        let original := fun z => ∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q
        let masked := fun z => ∑ q ∈ packets, P.physicalMaskedValue alt hAlt oldSlope b v f
          (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z q
        IntegrableOn (fun z => ‖original z-masked z‖) G (volume.prod volume) ∧
        (∫ z in G, ‖original z-masked z‖ ∂volume.prod volume) ≤
          L^(-Hloss)*ratio*(volume.prod volume).real Fset ∧
        ∀ z ∈ G, ∀ rho : ℝ, 0 < rho → ∀ I : Finset forest.keepers,
          (∀ i ∈ I, (T i).radius z ≤ L^(A+2)) →
          (∀ i ∈ I, w/(T i).length ≤ rho/(SourceParameters.branching L)^2) →
          (∀ i ∈ I, ∀ j ∈ I, |(T i).slope-(T j).slope| ≤ SourceParameters.branching L*rho) →
          (∀ i ∈ I, ∀ j ∈ I, i ≠ j → rho ≤ |(T i).slope-(T j).slope|) →
          (I.card:ℝ) ≤ L^Ct/100 := by
  obtain ⟨A,Cn,Ct,L0,haA,hA,hCn,hCt,hL0,hgood⟩ := source_density_selector_central_good_set
    hVariation hLL cStar cEta CEta cb Cb F hcStar hcEta hCEta hcb hCb hF hgap
    aDensity p0 Hloss Lip D K H J₀ haDensity hp0 hHloss hLip hD
  refine ⟨A,Cn,Ct,L0,haA,hA,hCn,hCt,hL0,?_⟩
  intro L hL κ _ N Label Item _ P packets oldSlope w tau Eset field forest T assigned R
    hprofile horder alt hAlt hw hwide hfrequency b hb hb1 hsupp hmotion hactive hlocal
    v hv f hf hf1 hspectrum haltSpectrum l r hslopes hfield hstrip hEstrip
    ratio Fset hratio hFset hFfinite hFstrip hratioExp hloghigh hratioEq
    widthScale hwidthLow hwidthHigh htimeLow htimeHigh hwidthEq
  have hangle : 0 < w/P.topLength := div_pos hw P.topLength_pos
  have hwide1 : 1 ≤ (2*cone+1)*((2:ℝ)^(SourceParameters.stepExponent L*SourceParameters.blockCount L))^4 :=
    one_le_mul_of_one_le_of_one_le (by linarith only [hcone]) (one_le_pow₀ (one_le_pow₀ (by norm_num)))
  exact hgood L hL κ N Label Item P packets oldSlope cone w tau Eset field forest hprofile horder
      alt hAlt hw hcone hwide hfrequency (fun _ => w/P.topLength) 1 (2*cone+1) cone
      (SourceParameters.stepExponent L*SourceParameters.blockCount L) J₀
      (fun _ => hangle) (by norm_num) (le_refl _) (by simpa only [one_mul] using hJ)
      hwide1 hconeK
      (by intro i j; simpa only [P.reference_angular_mesh w j] using hlocal j)
      b hb hb1
      (by intro i j l k s _ hs; simpa only [P.reference_angular_mesh w j] using hsupp j l k s hs)
      (by intro i j l k s _ _; simpa only [P.reference_angular_mesh w j] using hmotion j l k s (T i).slope)
      (by
        intro i j l k s hc hs
        apply selector_far_of_reference P oldSlope (T i).slope (T i).length cone w
          ((2*cone+1)*((2:ℝ)^(SourceParameters.stepExponent L*SourceParameters.blockCount L))^4)
          hw _ b hsupp j l k s hc hs
        have hpow : 1 ≤ ((2:ℝ)^(SourceParameters.stepExponent L*SourceParameters.blockCount L))^4 :=
          one_le_pow₀ (one_le_pow₀ (by norm_num))
        nlinarith only [mul_le_mul_of_nonneg_left hpow (by linarith only [hcone] : 0 ≤ 2*cone+1),hcone])
      v hv f hf hf1 hspectrum haltSpectrum
      (by
        intro i j l _ hk
        obtain ⟨k,hk⟩ := hk
        simpa only [abs_sub_comm] using hactive j l k (T i).slope hk)
      (le_refl _) rfl l r hslopes hfield hstrip hEstrip ratio Fset hratio hFset hFfinite hFstrip
      hratioExp hloghigh hratioEq widthScale hwidthLow hwidthHigh htimeLow htimeHigh hwidthEq

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceParentWidth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The parent residual cone fits the manuscript's physical packet
width W=mw. The actual dyadic branching is much smaller than m;
no enlargement of the source packet profiles is required. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert.SourceParameters

theorem eventually_parent_reference_width (cone : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ m w W : ℝ,
      Real.exp (L^(9/10:ℝ)) ≤ m → 0 < w → W = m*w →
      (cone+branching L^3)*w ≤ W ∧ (cone+branching L^2)*w ≤ W := by
  filter_upwards [eventually_branching_ge (max 2 cone),eventually_branching_separation]
    with L hlarge hseparation
  intro m w W hm hw hW
  have hB2 : 2 ≤ branching L := (le_max_left _ _).trans hlarge
  have hB1 : 1 ≤ branching L := by linarith
  have hcone : cone ≤ branching L := (le_max_right _ _).trans hlarge
  have hB3 : branching L ≤ branching L^3 := le_self_pow₀ hB1 (by norm_num)
  have hc : cone+branching L^3 ≤ branching L^4 := by
    have hp : 0 ≤ branching L^3 := by positivity
    have hh := mul_le_mul_of_nonneg_right hB2 hp
    rw [show branching L*branching L^3 = branching L^4 by ring] at hh
    linarith
  have hbudget : cone+branching L^3 ≤ m := hc.trans
    ((pow_le_pow_right₀ hB1 (by norm_num : 4 ≤ 100)).trans (hseparation.trans hm))
  have hsmall : cone+branching L^2 ≤ m := by
    have hp := pow_le_pow_right₀ hB1 (by norm_num : 2 ≤ 3)
    linarith
  subst W
  exact ⟨mul_le_mul_of_nonneg_right hbudget hw.le,mul_le_mul_of_nonneg_right hsmall hw.le⟩

end LipschitzHilbert.SourceParameters

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataDensityGoodRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common concentration set gives popular recovery. The deleted-area
and mask losses, global weight budget and numerical parameters follow from
the common-set estimates and the density forest. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem source_density_recovery_of_good_set
    (hVariation : LepingleInput)
    (cStar cEta CEta cb Cb F c0 cone Lip aDensity p0 qEnergy decay : ℝ)
    (D K H : ℕ)
    (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta)
    (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hF : 0 ≤ F) (hc0 : 0 < c0)
    (hcone : 0 ≤ cone) (hconeK : cone ≤ K) (hLip : 0 ≤ Lip)
    (haDensity : 0 ≤ aDensity) (hp0 : 0 ≤ p0) (hqEnergy : 0 ≤ qEnergy)
    (hdecay : 0 ≤ decay) (hD : 4 ≤ D)
    (hgap : cStar < cEta*cb)
    (A Cn Ct : ℝ) (haA : aDensity+3 < A) (hA : 2 < A) (hCn : 0 < Cn) (hCt : 0 < Ct) :

    let loss := 2*(qEnergy+decay+1)
    ∀ᶠ L : ℝ in atTop,
    ∀ (κ : Type) [Fintype κ] (N : ℕ) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (oldSlope w tau : ℝ)
      (hw : 0 < w) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
      P.scale = 4*(L^(A+2)*P.width) → P.ratioBound = 4*L^(A+2) →
      (2^P.order*P.profileBound)*3^(2*P.order) ≤ L^p0 →
      6+2*(8*D+1) ≤ P.order →
    ∀ (Eset Fset : Set (ℝ×ℝ)) (field : Plane → ℝ)
      (forest : PacketDensityForest P packets oldSlope L aDensity cone w tau Eset
        (fun z => field (planeCoordinates z))),
      let T := forest.top
      let assigned := forest.assigned
      (∀ i, |(T i).slope| ≤ 1) →
    ∀ (l r : ℝ), LipschitzWith 1 field → 600*(r-l) ≤ 1 →
      (∀ z ∈ Eset, z.1 ∈ Icc l r) → (∀ z ∈ Fset, z.1 ∈ Icc l r) →
      MeasurableSet Fset → (volume.prod volume) Fset ≠ ∞ →
      0 < (volume.prod volume).real Fset →
    ∀ (ratio widthScale : ℝ), 0 < ratio → L/2 ≤ Real.log ratio → Real.log ratio ≤ 2*L →
      (volume.prod volume).real Eset = ratio^2*(volume.prod volume).real Fset →
      Real.exp (L^(9/10:ℝ)) ≤ widthScale → widthScale ≤ 2*Real.exp (L^(9/10:ℝ)) →
      P.width = widthScale*w → 0 ≤ tau → tau ≤ Real.exp (-(L^(97/100:ℝ))) →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 → |s-(oldSlope+P.rowSlope j l)| ≤ cone*(w/P.length j)) →
      (∀ j l k s t, ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(w/P.length j))) →
      (∀ j l k s, b j l k s ≠ 0 →
        cb*w/P.length j ≤ |s-(oldSlope+P.rowSlope j l)| ∧
          |s-(oldSlope+P.rowSlope j l)| ≤ Cb*w/P.length j) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => oldSlope+P.rowSlope j l) (w/P.length j) H) →
      (∀ k, c0/w ≤ |P.frequency k|) →
      (∀ j l u k xi eta,
        planarAngularFourier (P.physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
          |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l u k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
          |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (g : AngularGrid) (start : ℝ), (g.branching:ℝ) = SourceParameters.step L →
      (∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/P.length j) 0) →
      (∀ i, start ≤ (T i).slope ∧ (T i).slope ≤ start+g.rootWidth) →
      (∫ z, ‖∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q‖^2
        ∂volume.prod volume) ≤ (L^qEnergy)^2*(volume.prod volume).real Eset →
      let R := fun i => (T i).length
      let Q := fun top => (P.assignedTopFamily packets assigned top).referenceFamily
        oldSlope (T top).slope (R top) cone w F hw hcone hF hwide hfrequency
      let orig := fun top j (l : (Q top).labels j) =>
        ((P.assignedTopFamily packets assigned top).referenceOriginalLabel
          oldSlope (T top).slope (R top) cone w j l).val.2
      let a := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
        alt j (orig top j l) u.val k
      let ha := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
        hAlt j (orig top j l) u.val k
      ∀ G : Set (ℝ×ℝ), (MeasurableSet G ∧ G ⊆ Fset ∧
        (volume.prod volume) (Fset\G) ≤ ENNReal.ofReal (L^(-loss)*(volume.prod volume).real Fset) ∧
        (∀ z ∈ G, ∀ i, (T i).weight (L^(A+2)) (D:ℝ) z ≤ (2:ℝ)^D) ∧
        (∀ z ∈ G, Real.log (max 1 (∑ i, (T i).weight (L^(A+2)) (D:ℝ) z)) ≤ 3*L) ∧
        (∀ z ∈ G, (∑ i, (T i).weight (L^(A+2)) (D:ℝ) z) ≤ ratio*L^Cn) ∧
        (∀ top lower upper, lower ≤ upper → upper ≤ N → ∀ z ∈ G, ∀ yy,
          |yy-(z.2-(T top).slope*z.1)| ≤ (T top).width →
          let V := ((Q top).withProfile (a top) (ha top)).rawInterval
            (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig top j l) u.val)
            0 lower upper
          ‖V z.1 yy‖+(T top).width*‖covariantSignal P.frequency
            (fun k y => V z.1 y k) yy‖ ≤ L^(2*(p0+2*(aDensity+3)+1)+8)*((T top).weight (L^(A+2)) (D:ℝ) z)^8) ∧
        let original := fun z => ∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q
        let masked := fun z => ∑ q ∈ packets, P.physicalMaskedValue alt hAlt oldSlope b v f
          (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z q
        IntegrableOn (fun z => ‖original z-masked z‖) G (volume.prod volume) ∧
        (∫ z in G, ‖original z-masked z‖ ∂volume.prod volume) ≤
          L^(-loss)*ratio*(volume.prod volume).real Fset ∧
        ∀ z ∈ G, ∀ rho : ℝ, 0 < rho → ∀ I : Finset forest.keepers,
          (∀ i ∈ I, (T i).radius z ≤ L^(A+2)) →
          (∀ i ∈ I, w/(T i).length ≤ rho/(SourceParameters.branching L)^2) →
          (∀ i ∈ I, ∀ j ∈ I, |(T i).slope-(T j).slope| ≤ SourceParameters.branching L*rho) →
          (∀ i ∈ I, ∀ j ∈ I, i ≠ j → rho ≤ |(T i).slope-(T j).slope|) →
          (I.card:ℝ) ≤ L^Ct/100) →
      (∫ z in Fset, ‖∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q‖
        ∂volume.prod volume) ≤ L^(-decay)*ratio*(volume.prod volume).real Fset := by
  intro loss
  let pProfile := p0+2*(A+2)+2
  let qEnv := 2*(p0+2*(aDensity+3)+1)+8
  let m := max (max (2*(qEnv+6)+2) Cn) (aDensity+2*(A+2)+2)
  let AM := 4*(max (3*pProfile+13) (2*pProfile+17)+3/2)
  have hpProfile : 0 ≤ pProfile := by dsimp [pProfile]; linarith only [hp0,hA]
  have hqEnv : 0 ≤ qEnv := by dsimp [qEnv]; linarith only [hp0,haDensity]
  have hAM : 0 < AM := by
    have h := le_max_left (3*pProfile+13) (2*pProfile+17)
    dsimp [AM]
    linarith only [h,hpProfile]
  have hm : 0 ≤ m := le_trans (by linarith only [hqEnv] : 0 ≤ 2*(qEnv+6)+2)
    ((le_max_left _ _).trans (le_max_left _ _))
  have hqm : 2*(qEnv+6)+2 ≤ m := (le_max_left _ _).trans (le_max_left _ _)
  have hCnm : Cn ≤ m := (le_max_right _ _).trans (le_max_left _ _)
  have hDreal : 2 < (D:ℝ) := by exact_mod_cast (by omega : 2 < D)
  have hweight : (1:ℝ) ≤ 2^D := one_le_pow₀ (by norm_num)
  have hrec := eventually_actual_packet_recovery hVariation
    qEnergy (aDensity+1) pProfile qEnv Cn ((2:ℝ)^D) F c0 AM (Ct+1) m decay A
    cStar cEta CEta cb Cb Lip cone D K H
    hpProfile hqEnv hCn.le hweight hF hc0 hAM (le_refl _)
    hDreal (by linarith only [hCt]) hm hqm hCnm hdecay (by linarith only [hA])
    hcStar hcEta hCEta hcb hCb hLip hgap hcone hconeK
  have hglobal := eventually_source_global_weight_integral (D:ℝ) (A+2) (aDensity+1) hDreal
  filter_upwards [hrec,hglobal,SourceParameters.eventually_parent_reference_width cone,
    eventually_ge_atTop (max 16 (F*cone+2))] with L hrecover hglobal hparent hlarge
  intro κ _ N Label Item _ P packets oldSlope w tau hw hwide hfrequency hscale hratioBound hprofile horder
    Eset Fset field forest T assigned hslopes l r hfield hstrip hEstrip hFstrip hFset hFfinite hFpositive
    ratio widthScale hratio hloglow hloghigh hratioEq hwidthLow hwidthHigh hwidthEq htimeLow htimeHigh
    alt hAlt b hb hb1 hsupp hmotion hactive hlocal hfrequencyLo hspectrum haltSpectrum
    v hv f hf hf1 g start hbranch hzero hslope henergy R Q orig a ha G hGbounds
  rcases hGbounds with ⟨hG,hGF,hGarea,hweightG,hlogG,hcountG,hconcG,hintG,hmaskG,hsepG⟩
  have hL16 : 16 ≤ L := (le_max_left _ _).trans hlarge
  have hfactor : F*cone+2 ≤ L := (le_max_right _ _).trans hlarge
  have hL1 : 1 ≤ L := by linarith only [hL16]
  have hLp : 0 < L := by linarith only [hL16]
  have hwidePair := hparent widthScale w P.width hwidthLow hw hwidthEq
  have hGfinite : (volume.prod volume) G ≠ ∞ := measure_ne_top_of_subset hGF hFfinite
  have hGmeasure : (volume.prod volume).real G ≤ (volume.prod volume).real Fset :=
    measureReal_mono hGF hFfinite
  have hGfixed : (volume.prod volume).real (Fset\G) ≤
      (L^(-qEnergy-(decay+1)))^2*(volume.prod volume).real Fset := by
    have ht := ENNReal.toReal_mono (by simp) hGarea
    rw [ENNReal.toReal_ofReal (by positivity)] at ht
    have heq : L^(-loss) = (L^(-qEnergy-(decay+1)))^2 := by
      rw [← Real.rpow_two,← Real.rpow_mul hLp.le]
      congr 1
      dsimp [loss]
      ring
    exact heq ▸ ht
  have hmask : (∫ z in G, ‖(∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q)-
      ∑ q ∈ packets, P.physicalMaskedValue alt hAlt oldSlope b v f
        (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z q‖ ∂volume.prod volume) ≤
      L^(-(decay+1))*ratio*(volume.prod volume).real Fset :=
    hmaskG.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hL1 (by dsimp [loss]; linarith only [hqEnergy,hdecay])) hratio.le)
      measureReal_nonneg)
  have hgeom := forest.mask_geometry hL1 (by linarith only [haA] : aDensity+3 ≤ A+2)
  have hglobalBudget : (∑ i : forest.keepers, ∫ z, (T i).weight (L^(A+2)) (D:ℝ) z
      ∂volume.prod volume) ≤ L^m*ratio^2*(volume.prod volume).real Fset := by
    have h := hglobal forest.keepers Finset.univ T ratio ((volume.prod volume).real Fset)
      hratio.le measureReal_nonneg
        (forest.area_budget (by linarith only [hL16]) ratio _ measureReal_nonneg hratioEq.le)
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hL1
        (by dsimp [m]; linarith [le_max_right (max (2*(qEnv+6)+2) Cn) (aDensity+2*(A+2)+2)]))
        (sq_nonneg ratio)) measureReal_nonneg)
  have hcore1 := hrecover forest.keepers κ N Label Item P Finset.univ T packets assigned oldSlope w hw hwide
    hfrequency hfrequencyLo
    (P.mask_referenceEnvelopeConstant_of_ratio hL16 (by linarith only [hA]) hF hcone hfactor hratioBound hprofile)
    alt hAlt b hb hb1 hsupp v hv f hf hf1 hmotion hactive hspectrum haltSpectrum
  have hcore2 := hcore1 hwidePair.2 hwidePair.1 hlocal
    (by
      intro i _
      rw [forest.width]
      exact le_mul_of_one_le_left P.width_pos.le (Real.one_le_rpow hL1 (by linarith only [hA])))
    (by omega)
    (by
      intro i _
      change P.scale = 4*(L^(A+2)*(forest.top i).width)
      rw [forest.width]
      exact hscale)
    hgeom.1 hgeom.2 (fun _ _ => Finset.mem_univ _) (fun q hq => (forest.reference q hq).1)
    forest.reference g hbranch
    (by
      intro i _
      rw [forest.width]
      have h := hwidePair.2
      nlinarith only [h, mul_nonneg hcone hw.le])
    hzero
    (by
      intro i _
      have h := hzero i.val.val.1
      simp only [AngularGrid.eligible,pow_zero,mul_one]
      apply (div_le_div_of_nonneg_left hw.le (P.length_pos _) (forest.seed_short i)).trans
      simpa only [AngularGrid.eligible,pow_zero,mul_one] using h)
  have hcore3 := hcore2 (SourceParameters.blockCount_pos (by linarith only [hL16])) (source_blockCount_le_square (by linarith only [hL16]))
    (2*L^Ct) ratio (L^qEnv)
    (by nlinarith only [Real.one_le_rpow hL1 hCt.le])
    (by
      calc
        _ ≤ L*L^Ct := mul_le_mul_of_nonneg_right (by linarith only [hL16] : (2:ℝ) ≤ L) (Real.rpow_nonneg hLp.le _)
        _ = L^(Ct+1) := by rw [Real.rpow_add hLp,Real.rpow_one]; ring)
    hratio (hloghigh.trans (by linarith only [hL16])) (Real.rpow_nonneg hLp.le _) (le_refl _)
  have hcore4 := hcore3 G hG
    (by intro z hz i _; exact hweightG z hz i)
    hlogG
    (by intro z hz; simpa only [mul_comm] using hcountG z hz)
    (by intro z hz i _ lower upper hlu hup yy hyy; exact hconcG i lower upper hlu hup z hz yy hyy)
    (by
      intro z hz rho hrho I _ hrad hprec hcluster hsep
      exact (hsepG z hz rho hrho I hrad hprec hcluster hsep).trans
        (by have hp := Real.rpow_nonneg hLp.le Ct; linarith only [hp]))
  exact hcore4 start ((volume.prod volume).real Fset) hFpositive hloglow hGfinite hGmeasure
    (fun i _ => hslope i) hglobalBudget
    Fset Eset hFset hFfinite rfl hGF hratioEq henergy hGfixed
    (by
      rw [hratioEq]
      simpa only [SlopeBox.area,mul_assoc] using
        (forest.area_budget (by linarith only [hL16]) ratio _ measureReal_nonneg hratioEq.le)) hmask

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataDensityPopularRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Popular recovery from an actual density forest. The common good set,
its deleted area, the mask error, all count/concentration hypotheses, and
the global weight budget are constructed before invoking recovery. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem source_density_popular_recovery_oai
    (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (cStar cEta CEta cb Cb F c0 cone Lip aDensity p0 qEnergy decay : ℝ)
    (D K H J₀ : ℕ)
    (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta)
    (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hF : 0 ≤ F) (hc0 : 0 < c0)
    (hcone : 0 ≤ cone) (hconeK : cone ≤ K) (hLip : 0 ≤ Lip)
    (haDensity : 0 ≤ aDensity) (hp0 : 0 ≤ p0) (hqEnergy : 0 ≤ qEnergy)
    (hdecay : 0 ≤ decay) (hD : 4 ≤ D)
    (hgap : cStar < cEta*cb) (hJ : 2*cone+1 ≤ (2:ℝ)^J₀) :
    ∃ A L0 : ℝ, aDensity+3 < A ∧ 16 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (κ : Type) [Fintype κ] (N : ℕ) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (oldSlope w tau : ℝ), 0 < w →
      P.scale = 4*(L^(A+2)*P.width) → P.ratioBound = 4*L^(A+2) →
      (2^P.order*P.profileBound)*3^(2*P.order) ≤ L^p0 →
      6+2*(8*D+1) ≤ P.order →
    ∀ (Eset Fset : Set (ℝ×ℝ)) (field : Plane → ℝ)
      (forest : PacketDensityForest P packets oldSlope L aDensity cone w tau Eset
        (fun z => field (planeCoordinates z))),
      let T := forest.top
      (∀ i, |(T i).slope| ≤ 1) →
    ∀ (l r : ℝ), LipschitzWith 1 field → 600*(r-l) ≤ 1 →
      (∀ z ∈ Eset, z.1 ∈ Icc l r) → (∀ z ∈ Fset, z.1 ∈ Icc l r) →
      MeasurableSet Fset → (volume.prod volume) Fset ≠ ∞ →
      0 < (volume.prod volume).real Fset →
    ∀ (ratio widthScale : ℝ), 0 < ratio → L/2 ≤ Real.log ratio → Real.log ratio ≤ 2*L →
      (volume.prod volume).real Eset = ratio^2*(volume.prod volume).real Fset →
      Real.exp (L^(9/10:ℝ)) ≤ widthScale → widthScale ≤ 2*Real.exp (L^(9/10:ℝ)) →
      P.width = widthScale*w → 0 ≤ tau → tau ≤ Real.exp (-(L^(97/100:ℝ))) →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 → |s-(oldSlope+P.rowSlope j l)| ≤ cone*(w/P.length j)) →
      (∀ j l k s t, ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(w/P.length j))) →
      (∀ j l k s, b j l k s ≠ 0 →
        cb*w/P.length j ≤ |s-(oldSlope+P.rowSlope j l)| ∧
          |s-(oldSlope+P.rowSlope j l)| ≤ Cb*w/P.length j) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => oldSlope+P.rowSlope j l) (w/P.length j) H) →
      (∀ k, c0/w ≤ |P.frequency k|) → (∀ k, |P.frequency k| ≤ F/w) →
      (∀ j l u k xi eta,
        planarAngularFourier (P.physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
          |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l u k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
          |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (g : AngularGrid) (start : ℝ), (g.branching:ℝ) = SourceParameters.step L →
      (∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/P.length j) 0) →
      (∀ i, start ≤ (T i).slope ∧ (T i).slope ≤ start+g.rootWidth) →
      (∫ z, ‖∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q‖^2
        ∂volume.prod volume) ≤ (L^qEnergy)^2*(volume.prod volume).real Eset →
      (∫ z in Fset, ‖∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q‖
        ∂volume.prod volume) ≤ L^(-decay)*ratio*(volume.prod volume).real Fset := by
  let loss := 2*(qEnergy+decay+1)
  obtain ⟨A,Cn,Ct,Lgood,haA,hA,hCn,hCt,_hLgood,hgood⟩ := source_density_selector_good_set
    hVariation hLL cStar cEta CEta cb Cb F cone hcStar hcEta hCEta hcb hCb hF hcone hgap
    aDensity p0 loss Lip D K H J₀ haDensity hp0 (by dsimp [loss]; linarith only [hqEnergy,hdecay]) hLip hD
    hconeK hJ
  have hfinish := source_density_recovery_of_good_set hVariation
    cStar cEta CEta cb Cb F c0 cone Lip aDensity p0 qEnergy decay D K H
    hcStar hcEta hCEta hcb hCb hF hc0 hcone hconeK hLip haDensity hp0 hqEnergy hdecay hD hgap
    A Cn Ct haA hA hCn hCt
  obtain ⟨L0,hL0⟩ := eventually_atTop.mp
    (hfinish.and ((SourceParameters.eventually_parent_reference_width cone).and
      (eventually_ge_atTop (max Lgood (max 16 (F*cone+2))))))
  refine ⟨A,max L0 16,haA,le_max_right _ _,?_⟩
  intro L hL κ _ N Label Item _ P packets oldSlope w tau hw hscale hratioBound hprofile horder
    Eset Fset field forest T hslopes l r hfield hstrip hEstrip hFstrip hFset hFfinite hFpositive
    ratio widthScale hratio hloglow hloghigh hratioEq hwidthLow hwidthHigh hwidthEq htimeLow htimeHigh
    alt hAlt b hb hb1 hsupp hmotion hactive hlocal hfrequencyLo hfrequency hspectrum haltSpectrum
    v hv f hf hf1 g start hbranch hzero hslope henergy
  have hLbase : L0 ≤ L := (le_max_left _ _).trans hL
  obtain ⟨hfinish,hparent,hlarge⟩ := hL0 L hLbase
  have hLg : Lgood ≤ L := (le_max_left _ _).trans hlarge
  have hL16 : 16 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hfactor : F*cone+2 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hL1 : 1 ≤ L := by linarith only [hL16]
  have hLp : 0 < L := by linarith only [hL16]
  have hwidePair := hparent widthScale w P.width hwidthLow hw hwidthEq
  have hwide : cone*w ≤ P.width := (mul_le_mul_of_nonneg_right
    (le_add_of_nonneg_right (sq_nonneg (SourceParameters.branching L))) hw.le).trans hwidePair.2
  have hratioExp : ratio ≤ Real.exp (2*L) :=
    (Real.log_le_iff_le_exp hratio).mp (hloghigh.trans (by linarith only [hL16]))
  obtain ⟨G,hG,hGF,hGarea,hweightG,hlogG,hcountG,hconcG,hintG,hmaskG,hsepG⟩ :=
    hgood L hLg κ N Label Item P packets oldSlope w tau Eset field forest hprofile horder
      alt hAlt hw hwide hfrequency b hb hb1 hsupp hmotion hactive hlocal v hv f hf hf1
      (fun q _ => hspectrum q.1 q.2.1 q.2.2)
      (fun q _ => haltSpectrum q.1 q.2.1 q.2.2)
      l r hslopes hfield hstrip hEstrip ratio Fset hratio hFset hFfinite hFstrip
      hratioExp hloghigh hratioEq.le widthScale hwidthLow hwidthHigh htimeLow htimeHigh hwidthEq
  exact hfinish κ N Label Item P packets oldSlope w tau hw hwide hfrequency hscale hratioBound hprofile horder
    Eset Fset field forest hslopes l r hfield hstrip hEstrip hFstrip hFset hFfinite hFpositive
    ratio widthScale hratio hloglow hloghigh hratioEq hwidthLow hwidthHigh hwidthEq htimeLow htimeHigh
    alt hAlt b hb hb1 hsupp hmotion hactive hlocal hfrequencyLo hspectrum haltSpectrum
    v hv f hf hf1 g start hbranch hzero hslope henergy G
    ⟨hG,hGF,hGarea,hweightG,hlogG,hcountG,hconcG,hintG,hmaskG,hsepG⟩

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.PacketLatticeData.source_density_popular_recovery_oai := @OAI.LipschitzHilbert.PacketLatticeData.source_density_popular_recovery_oai
