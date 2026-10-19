-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff32.coarse32
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T14:21:16.886783+00:00
-- url     : https://prove2.me/submissions/d5944a03-85b4-4962-b146-4e6c7e7e50c7

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Coordinates
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_GapComparison
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_antitoneOn_scalarEnvelope
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_exists_normalized_failure
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_normalized_pair_sum_le
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Coarse localization on the window 32 ≤ p ≤ 50

All quantities are scaled so that the three singleton norms sum to 3.
With `T` the total norm (`T < 3q ≤ 1158/1000`) and `G` the pair-gap sum,
failure gives `K G < 3 - T` with `K > 0.448 p ≥ 14.336`.

Pass 0: each pair sum `v` has a coordinate `i` and sign `s` with
`‖v‖ - 8/100 ≤ s v_i` (from `‖v‖ ≤ 3^{1/p} max |v_i|`); the three coordinates
are distinct and the triple is oriented as in the cutoff-50 argument.
Pass 1: the oriented box forces every non-dominant pair coordinate to be at most
half the dominant one, hence `‖v‖ ≤ v_dom (1 + 2^{1-p}/p)`, i.e. tail `≤ 10^{-5}`.
The box then follows linearly.
-/

namespace Hl32Coarse
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

section Basic
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]

theorem lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → E) = 0 := by
  simp [lpNorm, hp.ne']

theorem lpNorm_add {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    lpNorm p (x + y) ≤ lpNorm p x + lpNorm p y := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  simpa only [lpNorm_eq_piLp hp0, ← WithLp.toLp_add] using
    norm_add_le (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y)

theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i

theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : lpNorm p (c • x) = |c| * lpNorm p x := by
  unfold lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)

theorem pairGap_nonneg {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    0 ≤ pairGap (lpNorm p) x y := sub_nonneg.mpr (lpNorm_add hp x y)

theorem pairGapSum_nonneg {p : ℝ} (hp : 1 ≤ p) (x y z : ι → E) :
    0 ≤ pairGapSum (lpNorm p) x y z :=
  add_nonneg (add_nonneg (pairGap_nonneg hp x y) (pairGap_nonneg hp x z))
    (pairGap_nonneg hp y z)

end Basic

section Deficit
variable {ι : Type*} [Fintype ι]

theorem hlawkaDeficit_eq (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x y z =
      K * pairGapSum (lpNorm p) x y z - tripleGap (lpNorm p) x y z := by
  unfold hlawkaDeficit pairGapSum pairGap tripleGap
  ring

theorem hlawkaDeficit_swap_left (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K y x z = hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, add_comm, add_left_comm, add_assoc]

theorem hlawkaDeficit_swap_right (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x z y = hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, add_comm, add_left_comm, add_assoc]

theorem hlawkaDeficit_smul {p : ℝ} (hp : 0 < p) (K c : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K (c • x) (c • y) (c • z) = |c| * hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← smul_add, lpNorm_smul hp]
  ring

theorem scalarEnvelopeRoot_lt_one {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hq1 : q < 1) :
    scalarEnvelopeRoot p q < 1 := by
  have hpow : q ^ p < 1 := by
    simpa only [Real.one_rpow] using Real.rpow_lt_rpow hq hq1 hp
  have hbase : 0 ≤ (1 + q ^ p) / 2 := by positivity
  have hroot := Real.rpow_lt_rpow hbase (show (1 + q ^ p) / 2 < 1 by linarith)
    (one_div_pos.mpr hp)
  simpa only [Real.one_rpow, scalarEnvelopeRoot] using hroot

theorem scalarEnvelope_denominator_pos {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hq1 : q < 1) :
    0 < 2 * (1 - scalarEnvelopeRoot p q) := by
  have h := scalarEnvelopeRoot_lt_one hp hq hq1
  linarith

theorem failure_ne_zero {p K : ℝ} (hp : 1 ≤ p) (hK : 1 ≤ K)
    (x y z : ι → ℝ) (hf : hlawkaDeficit p K x y z < 0) :
    x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 := by
  have hfirst (u v w : ι → ℝ) (h : hlawkaDeficit p K u v w < 0) : u ≠ 0 := by
    intro hu
    subst u
    simp only [hlawkaDeficit, lpNorm_zero (zero_lt_one.trans_le hp), zero_add] at h
    have ht := lpNorm_add hp v w
    have hm := mul_nonneg (sub_nonneg.mpr hK)
      (show 0 ≤ lpNorm p v + lpNorm p w - lpNorm p (v + w) by linarith)
    nlinarith
  refine ⟨hfirst x y z hf, hfirst y x z ?_, hfirst z x y ?_⟩
  · rwa [hlawkaDeficit_swap_left]
  · rwa [hlawkaDeficit_swap_left, hlawkaDeficit_swap_right]

theorem normalized_failure_total_lt_one {p K : ℝ} (hp : 1 ≤ p) (hK : 0 ≤ K)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p K x y z < 0) : lpNorm p (x + y + z) < 1 := by
  rw [hlawkaDeficit_eq, tripleGap, hS] at hf
  have hprod := mul_nonneg hK (pairGapSum_nonneg hp x y z)
  linarith

theorem normalized_failure_ratio_lt_envelope {p K : ℝ} (hp : 1 < p) (hK : 1 ≤ K)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p K x y z < 0) :
    K < scalarEnvelope p (lpNorm p (x + y + z)) := by
  have hp0 := zero_lt_one.trans hp
  have hn := failure_ne_zero hp.le hK x y z hf
  have hq0 := lpNorm_nonneg p (x + y + z)
  have hq1 := normalized_failure_total_lt_one hp.le (by linarith) x y z hS hf
  have hP := normalized_pair_sum_le hp x y z hn.1 hn.2.1 hn.2.2 hS
  have hden := scalarEnvelope_denominator_pos hp0 hq0 hq1
  have hgap : 2 * (1 - scalarEnvelopeRoot p (lpNorm p (x + y + z))) ≤
      pairGapSum (lpNorm p) x y z := by
    dsimp only [pairGapSum, pairGap]
    linarith
  have hgap0 : 0 < pairGapSum (lpNorm p) x y z := hden.trans_le hgap
  have hR : K < (1 - lpNorm p (x + y + z)) / pairGapSum (lpNorm p) x y z := by
    rw [lt_div_iff₀ hgap0]
    rw [hlawkaDeficit_eq, tripleGap, hS] at hf
    linarith
  exact hR.trans_le (div_le_div_of_nonneg_left (by linarith) hden hgap)

/-- The envelope hypothesis at `q` confines the normalized total below `q`. -/
theorem normalized_failure_total_lt_q {p K q : ℝ} (hp : 1 < p) (hK : 1 ≤ K)
    (hq0 : 0 < q) (hq1 : q < 1) (henvelope : scalarEnvelope p q < K)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p K x y z < 0) :
    lpNorm p (x + y + z) < q := by
  have hT1 := normalized_failure_total_lt_one hp.le (by linarith) x y z hS hf
  have henv := normalized_failure_ratio_lt_envelope hp hK x y z hS hf
  by_contra hn
  have hle : q ≤ lpNorm p (x + y + z) := le_of_not_gt hn
  have hm := antitoneOn_scalarEnvelope hp.le
    (show q ∈ Set.Ico 0 1 from ⟨hq0.le, hq1⟩)
    (show lpNorm p (x + y + z) ∈ Set.Ico 0 1 from ⟨lpNorm_nonneg p _, hT1⟩) hle
  linarith

end Deficit

/-- Scaled normalization: singleton norms sum to 3, each at most the total,
and the total is below `3q`. -/
theorem scaled_failure {p K q : ℝ} (hp : 1 < p) (hK : 1 ≤ K)
    (hq0 : 0 < q) (hq1 : q < 1) (henvelope : scalarEnvelope p q < K)
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p K x y z < 0) :
    ∃ x y z : Fin 3 → ℝ, hlawkaDeficit p K x y z < 0 ∧
      lpNorm p x + lpNorm p y + lpNorm p z = 3 ∧
      lpNorm p x ≤ lpNorm p (x + y + z) ∧
      lpNorm p y ≤ lpNorm p (x + y + z) ∧
      lpNorm p z ≤ lpNorm p (x + y + z) ∧
      lpNorm p (x + y + z) < 3 * q := by
  have hp0 : 0 < p := by linarith
  obtain ⟨x, y, z, hf, hS, hxT, hyT, hzT⟩ := exists_normalized_failure hp0 hK x y z hf
  have hT := normalized_failure_total_lt_q hp hK hq0 hq1 henvelope x y z hS hf
  have h3 : |(3 : ℝ)| = 3 := abs_of_pos (by norm_num)
  have hsum : (3 : ℝ) • x + (3 : ℝ) • y + (3 : ℝ) • z = (3 : ℝ) • (x + y + z) := by
    rw [smul_add, smul_add]
  refine ⟨(3 : ℝ) • x, (3 : ℝ) • y, (3 : ℝ) • z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlawkaDeficit_smul hp0, h3]
    linarith
  · rw [lpNorm_smul hp0, lpNorm_smul hp0, lpNorm_smul hp0, h3]
    linarith
  · rw [hsum, lpNorm_smul hp0, lpNorm_smul hp0, h3]
    linarith
  · rw [hsum, lpNorm_smul hp0, lpNorm_smul hp0, h3]
    linarith
  · rw [hsum, lpNorm_smul hp0, lpNorm_smul hp0, h3]
    linarith
  · rw [hsum, lpNorm_smul hp0, h3]
    linarith

/-! ### Pass 0: one large signed coordinate in every pair sum -/

theorem lpNorm_le_three_root_mul_max {p : ℝ} (hp : 0 < p) (x : Fin 3 → ℝ)
    (i : Fin 3) (hi : ∀ j, |x j| ≤ |x i|) :
    lpNorm p x ≤ (3 : ℝ) ^ (1 / p) * |x i| := by
  have hsum : (∑ j, |x j| ^ p) ≤ 3 * |x i| ^ p := by
    calc
      _ ≤ ∑ _ : Fin 3, |x i| ^ p :=
        Finset.sum_le_sum fun j _ ↦ Real.rpow_le_rpow (abs_nonneg _) (hi j) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun j _ ↦ Real.rpow_nonneg (abs_nonneg (x j)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (abs_nonneg _) _),
    ← Real.rpow_mul (abs_nonneg (x i)), mul_one_div_cancel hp.ne', Real.rpow_one] at h
  simpa only [lpNorm, Real.norm_eq_abs] using h

theorem inverse_three_root_deficit (p : ℝ) :
    1 - ((3 : ℝ) ^ (1 / p))⁻¹ ≤ Real.log 3 / p := by
  have h := Real.add_one_le_exp (-(Real.log 3 / p))
  have he : ((3 : ℝ) ^ (1 / p))⁻¹ = Real.exp (-(Real.log 3 / p)) := by
    rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_neg]
    congr 1
    ring
  rw [he]
  linarith

theorem exists_signed_coord {p : ℝ} (hp : 32 ≤ p) (v : Fin 3 → ℝ)
    (hv : lpNorm p v ≤ 232 / 100) :
    ∃ i : Fin 3, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ lpNorm p v - 8 / 100 ≤ s * v i := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  obtain ⟨i, _, hi⟩ := Finset.univ.exists_max_image (fun i ↦ |v i|) Finset.univ_nonempty
  have hmax := lpNorm_le_three_root_mul_max hp0 v i (fun j ↦ hi j (Finset.mem_univ _))
  set c := ((3 : ℝ) ^ (1 / p))⁻¹ with hcdef
  have hc0 : 0 < c := by rw [hcdef]; positivity
  have hmax' : c * lpNorm p v ≤ |v i| := by
    have hm := mul_le_mul_of_nonneg_left hmax hc0.le
    have he : c * ((3 : ℝ) ^ (1 / p) * |v i|) = |v i| := by
      rw [hcdef, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    rw [he] at hm
    exact hm
  have hd : 1 - c ≤ Real.log 3 / p := inverse_three_root_deficit p
  have hlog3 : Real.log 3 < 11 / 10 := by linarith [Real.log_three_lt_d9]
  have hlogp : Real.log 3 / p ≤ 11 / 320 := by
    rw [div_le_iff₀ hp0]
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
    nlinarith
  have hn0 := lpNorm_nonneg p v
  have hbound : lpNorm p v - |v i| ≤ 8 / 100 := by
    have h1 : (1 - c) * lpNorm p v ≤ 11 / 320 * lpNorm p v :=
      mul_le_mul_of_nonneg_right (hd.trans hlogp) hn0
    have h2 : 11 / 320 * lpNorm p v ≤ 11 / 320 * (232 / 100) :=
      mul_le_mul_of_nonneg_left hv (by norm_num)
    nlinarith
  by_cases hi0 : 0 ≤ v i
  · rw [abs_of_nonneg hi0] at hbound
    exact ⟨i, 1, Or.inl rfl, by linarith⟩
  · rw [abs_of_neg (lt_of_not_ge hi0)] at hbound
    exact ⟨i, -1, Or.inr rfl, by linarith⟩

/-- Two pairs sharing a vector cannot share their dominant coordinate. -/
theorem signed_conflict {a b c Na Nb Nc P1 P2 T G s r : ℝ}
    (hs : s = 1 ∨ s = -1) (hr : r = 1 ∨ r = -1)
    (ha : |a| ≤ Na) (hb : |b| ≤ Nb) (hc : |c| ≤ Nc) (hcol : |a + b + c| ≤ T)
    (h1 : P1 - 8 / 100 ≤ s * a + s * b) (h2 : P2 - 8 / 100 ≤ r * a + r * c)
    (hP1 : Na + Nb - P1 ≤ G) (hP2 : Na + Nc - P2 ≤ G)
    (hG : G < 15 / 100) (hNa : 6 / 10 < Na) (hS : Na + Nb + Nc = 3) (hT : T < 2) :
    False := by
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have hc' := abs_le.mp hc
  have hcol' := abs_le.mp hcol
  rcases hs with rfl | rfl <;> rcases hr with rfl | rfl <;> linarith

/-! ### Pass 1: a dominant coordinate with half-size tail -/

theorem norm_le_dominant_half {p : ℝ} (hp : 1 < p)
    (v : Fin 3 → ℝ) (k : Fin 3) (hm : 0 ≤ v k)
    (hsmall : ∀ i, i ≠ k → |v i| ≤ v k * (1 / 2)) :
    lpNorm p v ≤ v k * (1 + 2 * (1 / 2 : ℝ) ^ p / p) := by
  have hp0 : 0 < p := by linarith
  have hpow (i : Fin 3) (hi : i ≠ k) :
      |v i| ^ p ≤ (v k) ^ p * (1 / 2 : ℝ) ^ p := by
    have h := Real.rpow_le_rpow (abs_nonneg (v i)) (hsmall i hi) hp0.le
    rw [Real.mul_rpow hm (by norm_num)] at h
    exact h
  have hsum : (∑ i, |v i| ^ p) ≤ (v k) ^ p * (1 + 2 * (1 / 2 : ℝ) ^ p) := by
    fin_cases k
    · change 0 ≤ v 0 at hm
      have hleft : |v 1| ^ p ≤ v 0 ^ p * (1 / 2 : ℝ) ^ p := hpow 1 (by decide)
      have hright : |v 2| ^ p ≤ v 0 ^ p * (1 / 2 : ℝ) ^ p := hpow 2 (by decide)
      simp only [Fin.sum_univ_three]
      change |v 0| ^ p + |v 1| ^ p + |v 2| ^ p ≤ v 0 ^ p * (1 + 2 * (1 / 2 : ℝ) ^ p)
      rw [abs_of_nonneg hm]
      nlinarith
    · change 0 ≤ v 1 at hm
      have hleft : |v 0| ^ p ≤ v 1 ^ p * (1 / 2 : ℝ) ^ p := hpow 0 (by decide)
      have hright : |v 2| ^ p ≤ v 1 ^ p * (1 / 2 : ℝ) ^ p := hpow 2 (by decide)
      simp only [Fin.sum_univ_three]
      change |v 0| ^ p + |v 1| ^ p + |v 2| ^ p ≤ v 1 ^ p * (1 + 2 * (1 / 2 : ℝ) ^ p)
      rw [abs_of_nonneg hm]
      nlinarith
    · change 0 ≤ v 2 at hm
      have hleft : |v 0| ^ p ≤ v 2 ^ p * (1 / 2 : ℝ) ^ p := hpow 0 (by decide)
      have hright : |v 1| ^ p ≤ v 2 ^ p * (1 / 2 : ℝ) ^ p := hpow 1 (by decide)
      simp only [Fin.sum_univ_three]
      change |v 0| ^ p + |v 1| ^ p + |v 2| ^ p ≤ v 2 ^ p * (1 + 2 * (1 / 2 : ℝ) ^ p)
      rw [abs_of_nonneg hm]
      nlinarith
  have hnorm := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg (v i)) p)
    hsum (one_div_nonneg.mpr hp0.le)
  rw [Real.mul_rpow (Real.rpow_nonneg hm _) (by positivity),
    ← Real.rpow_mul hm, mul_one_div_cancel hp0.ne', Real.rpow_one] at hnorm
  have hroot := rpow_one_add_le_one_add_mul_self
    (s := 2 * (1 / 2 : ℝ) ^ p) (p := 1 / p)
    (by have h := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) p; linarith)
    (by positivity) (by simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp.le))
  have hmul := mul_le_mul_of_nonneg_left hroot hm
  change lpNorm p v ≤ _ at hnorm
  calc
    _ ≤ v k * (1 + 1 / p * (2 * (1 / 2 : ℝ) ^ p)) := hnorm.trans hmul
    _ = _ := by ring

theorem dominant_half {p : ℝ} (hp : 32 ≤ p) (v : Fin 3 → ℝ) (k : Fin 3)
    (hm : 0 ≤ v k) (h3 : v k ≤ 3) (hsmall : ∀ i, i ≠ k → |v i| ≤ v k * (1 / 2)) :
    lpNorm p v ≤ v k + 1 / 100000 := by
  have hp0 : 0 < p := by linarith
  have hnorm := norm_le_dominant_half (by linarith : 1 < p) v k hm hsmall
  have hpow : (1 / 2 : ℝ) ^ p ≤ 1 / 10 ^ 9 := by
    have h1 : (1 / 2 : ℝ) ^ p ≤ (1 / 2) ^ (32 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hp
    have h2 : (1 / 2 : ℝ) ^ (32 : ℝ) = (1 / 2) ^ (32 : ℕ) := Real.rpow_natCast _ _
    rw [h2] at h1
    exact h1.trans (by norm_num)
  have ht0 : 0 ≤ 2 * (1 / 2 : ℝ) ^ p / p := by positivity
  have ht : 2 * (1 / 2 : ℝ) ^ p / p ≤ 2 / 10 ^ 9 := by
    calc
      _ ≤ 2 * (1 / 2 : ℝ) ^ p := div_le_self (by positivity) (by linarith)
      _ ≤ _ := by linarith
  have hm1 : v k * (2 * (1 / 2 : ℝ) ^ p / p) ≤ 3 * (2 / 10 ^ 9) :=
    mul_le_mul h3 ht ht0 (by norm_num)
  nlinarith

/-! ### The oriented core -/

/-- From the three pass-0 coordinate facts, the oriented scaled triple lies in
the coarse box. -/
theorem oriented_core {p : ℝ} (hp : 32 ≤ p) (u v w : Fin 3 → ℝ)
    (hS : lpNorm p u + lpNorm p v + lpNorm p w = 3)
    (hu : lpNorm p u ≤ lpNorm p (u + v + w))
    (hv : lpNorm p v ≤ lpNorm p (u + v + w))
    (hw : lpNorm p w ≤ lpNorm p (u + v + w))
    (hT : lpNorm p (u + v + w) < 1158 / 1000)
    (hG : (14336 / 1000 : ℝ) * pairGapSum (lpNorm p) u v w + lpNorm p (u + v + w) < 3)
    (h0 : lpNorm p (v + w) - 8 / 100 ≤ v 0 + w 0)
    (h1 : lpNorm p (u + w) - 8 / 100 ≤ u 1 + w 1)
    (h2 : lpNorm p (u + v) - 8 / 100 ≤ u 2 + v 2) :
    ∀ j i, if j = i then -(1158 / 1000 : ℝ) ≤ (![u, v, w] : Triple) j i ∧
        (![u, v, w] : Triple) j i ≤ -(555 / 1000 : ℝ)
      else (79 / 100 : ℝ) ≤ (![u, v, w] : Triple) j i ∧
        (![u, v, w] : Triple) j i ≤ (1158 / 1000 : ℝ) := by
  have hp1 : 1 ≤ p := by linarith
  have guv := pairGap_nonneg hp1 u v
  have guw := pairGap_nonneg hp1 u w
  have gvw := pairGap_nonneg hp1 v w
  dsimp only [pairGapSum, pairGap] at hG guv guw gvw
  have hu' (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 u i)
  have hv' (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 v i)
  have hw' (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 w i)
  have hc (i : Fin 3) : |u i + v i + w i| ≤ lpNorm p (u + v + w) :=
    norm_apply_le_lpNorm hp1 (u + v + w) i
  have hc' (i : Fin 3) := abs_le.mp (hc i)
  have hu0 := hu' 0; have hu1 := hu' 1; have hu2 := hu' 2
  have hv0 := hv' 0; have hv1 := hv' 1; have hv2 := hv' 2
  have hw0 := hw' 0; have hw1 := hw' 1; have hw2 := hw' 2
  have hc0 := hc' 0; have hc1 := hc' 1; have hc2 := hc' 2
  -- Pass 1 on each pair.
  have r0 : lpNorm p (v + w) ≤ v 0 + w 0 + 1 / 100000 := by
    apply dominant_half hp (v + w) 0
    · show 0 ≤ v 0 + w 0; linarith
    · show v 0 + w 0 ≤ 3; linarith
    · intro i hi
      fin_cases i
      · exact absurd rfl hi
      · show |v 1 + w 1| ≤ (v 0 + w 0) * (1 / 2)
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · show |v 2 + w 2| ≤ (v 0 + w 0) * (1 / 2)
        exact abs_le.mpr ⟨by linarith, by linarith⟩
  have r1 : lpNorm p (u + w) ≤ u 1 + w 1 + 1 / 100000 := by
    apply dominant_half hp (u + w) 1
    · show 0 ≤ u 1 + w 1; linarith
    · show u 1 + w 1 ≤ 3; linarith
    · intro i hi
      fin_cases i
      · show |u 0 + w 0| ≤ (u 1 + w 1) * (1 / 2)
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · exact absurd rfl hi
      · show |u 2 + w 2| ≤ (u 1 + w 1) * (1 / 2)
        exact abs_le.mpr ⟨by linarith, by linarith⟩
  have r2 : lpNorm p (u + v) ≤ u 2 + v 2 + 1 / 100000 := by
    apply dominant_half hp (u + v) 2
    · show 0 ≤ u 2 + v 2; linarith
    · show u 2 + v 2 ≤ 3; linarith
    · intro i hi
      fin_cases i
      · show |u 0 + v 0| ≤ (u 2 + v 2) * (1 / 2)
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · show |u 1 + v 1| ≤ (u 2 + v 2) * (1 / 2)
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · exact absurd rfl hi
  intro j i
  fin_cases j <;> fin_cases i <;> simp <;> constructor <;> linarith

/-! ### Assembly -/

theorem orient_add (e : Equiv.Perm (Fin 3)) (s x y : Fin 3 → ℝ) :
    orient e s (x + y) = orient e s x + orient e s y := by
  ext i
  exact mul_add _ _ _

theorem lpNorm_orient (p : ℝ) (e : Equiv.Perm (Fin 3)) (s x : Fin 3 → ℝ)
    (hs : ∀ i, |s i| = 1) : lpNorm p (orient e s x) = lpNorm p x := by
  calc
    _ = lpNorm p (x ∘ e) := by simp [lpNorm, orient, hs, Real.norm_eq_abs]
    _ = _ := lpNorm_comp_equiv p x e

theorem hlawkaDeficit_orient (p K : ℝ) (e : Equiv.Perm (Fin 3)) (s x y z : Fin 3 → ℝ)
    (hs : ∀ i, |s i| = 1) :
    hlawkaDeficit p K (orient e s x) (orient e s y) (orient e s z) =
      hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← orient_add, lpNorm_orient p e s _ hs]

theorem coarse_box32 {p q : ℝ} (hp : 32 ≤ p)
    (hlinear : (448 / 1000 : ℝ) * p < cyclicConstant p)
    (hq0 : 0 < q) (hq : q ≤ 386 / 1000)
    (henvelope : scalarEnvelope p q < cyclicConstant p)
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    ∃ X : Triple,
      (∀ j i, if j = i then -(1158 / 1000 : ℝ) ≤ X j i ∧ X j i ≤ -(555 / 1000 : ℝ)
               else (79 / 100 : ℝ) ≤ X j i ∧ X j i ≤ (1158 / 1000 : ℝ)) ∧
      lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 ∧
      lpNorm p (X 0 + X 1 + X 2) < 3 * q ∧
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448 / 1000) * p) ∧
      tripleDeficit p (cyclicConstant p) X < 0 := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 < p := by linarith
  set K := cyclicConstant p with hKdef
  have hK : (14336 / 1000 : ℝ) < K := by linarith
  obtain ⟨x, y, z, hf, hS, hxT, hyT, hzT, hTq⟩ :=
    scaled_failure hp1 (by linarith) hq0 (by linarith) henvelope x y z hf
  set T := lpNorm p (x + y + z) with hTdef
  have hT : T < 1158 / 1000 := by linarith
  -- Failure gives `K G < 3 - T`.
  have hG0 := pairGapSum_nonneg hp1.le x y z
  have hKG : K * pairGapSum (lpNorm p) x y z < 3 - T := by
    have h := hf
    rw [hlawkaDeficit_eq, tripleGap, hS] at h
    linarith
  have hG : (14336 / 1000 : ℝ) * pairGapSum (lpNorm p) x y z + T < 3 := by
    have := mul_le_mul_of_nonneg_right hK.le hG0
    linarith
  have hGp : pairGapSum (lpNorm p) x y z < 2 / ((448 / 1000) * p) := by
    rw [lt_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hlinear.le hG0
    nlinarith
  have hxy0 := pairGap_nonneg hp1.le x y
  have hxz0 := pairGap_nonneg hp1.le x z
  have hyz0 := pairGap_nonneg hp1.le y z
  have hGsplit := hG
  dsimp only [pairGapSum, pairGap] at hGsplit hxy0 hxz0 hyz0
  -- Pass 0.
  have hNx := lpNorm_nonneg p x
  have hNy := lpNorm_nonneg p y
  have hNz := lpNorm_nonneg p z
  obtain ⟨i, s, hs, hsxy⟩ := exists_signed_coord hp (x + y)
    (by linarith [lpNorm_add hp1.le x y])
  obtain ⟨j, r, hr, hrxz⟩ := exists_signed_coord hp (x + z)
    (by linarith [lpNorm_add hp1.le x z])
  obtain ⟨k, t, ht, htyz⟩ := exists_signed_coord hp (y + z)
    (by linarith [lpNorm_add hp1.le y z])
  simp only [Pi.add_apply, mul_add] at hsxy hrxz htyz
  have hxa (l : Fin 3) : |x l| ≤ lpNorm p x := norm_apply_le_lpNorm hp1.le x l
  have hya (l : Fin 3) : |y l| ≤ lpNorm p y := norm_apply_le_lpNorm hp1.le y l
  have hza (l : Fin 3) : |z l| ≤ lpNorm p z := norm_apply_le_lpNorm hp1.le z l
  have habs (l : Fin 3) : |x l + y l + z l| ≤ T := norm_apply_le_lpNorm hp1.le (x + y + z) l
  have hij : i ≠ j := by
    intro heq
    subst j
    exact signed_conflict (G := 14 / 100) hs hr (hxa i) (hya i) (hza i) (habs i) hsxy hrxz
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  have hik : i ≠ k := by
    intro heq
    subst k
    have hcol : |y i + x i + z i| ≤ T := by
      rw [show y i + x i + z i = x i + y i + z i by ring]; exact habs i
    exact signed_conflict (G := 14 / 100) (P1 := lpNorm p (x + y)) hs ht (hya i) (hxa i) (hza i) hcol (by linarith) htyz
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  have hjk : j ≠ k := by
    intro heq
    subst k
    have hcol : |z j + x j + y j| ≤ T := by
      rw [show z j + x j + y j = x j + y j + z j by ring]; exact habs j
    exact signed_conflict (G := 14 / 100) (P1 := lpNorm p (x + z)) (P2 := lpNorm p (y + z)) hr ht (hza j) (hxa j) (hya j) hcol (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  -- Orientation.
  let f : Fin 3 → Fin 3 := ![k, j, i]
  have hfInj : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f, Ne.symm hij, Ne.symm hik, Ne.symm hjk]
  let e : Equiv.Perm (Fin 3) := Equiv.ofBijective f hfInj.bijective_of_finite
  let signs : Fin 3 → ℝ := ![t, r, s]
  have hsigns : ∀ l, |signs l| = 1 := by
    intro l
    fin_cases l
    · rcases ht with rfl | rfl <;> norm_num [signs]
    · rcases hr with rfl | rfl <;> norm_num [signs]
    · rcases hs with rfl | rfl <;> norm_num [signs]
  let u := orient e signs x
  let v := orient e signs y
  let w := orient e signs z
  have hu : lpNorm p u = lpNorm p x := lpNorm_orient p e signs x hsigns
  have hv : lpNorm p v = lpNorm p y := lpNorm_orient p e signs y hsigns
  have hw : lpNorm p w = lpNorm p z := lpNorm_orient p e signs z hsigns
  have hsumNorm : lpNorm p (u + v + w) = T := by
    dsimp [u, v, w]
    rw [← orient_add, ← orient_add, lpNorm_orient p e signs _ hsigns]
  have huv : lpNorm p (u + v) = lpNorm p (x + y) := by
    dsimp [u, v]; rw [← orient_add, lpNorm_orient p e signs _ hsigns]
  have huw : lpNorm p (u + w) = lpNorm p (x + z) := by
    dsimp [u, w]; rw [← orient_add, lpNorm_orient p e signs _ hsigns]
  have hvw : lpNorm p (v + w) = lpNorm p (y + z) := by
    dsimp [v, w]; rw [← orient_add, lpNorm_orient p e signs _ hsigns]
  have hpgs : pairGapSum (lpNorm p) u v w = pairGapSum (lpNorm p) x y z := by
    simp only [pairGapSum, pairGap, hu, hv, hw, huv, huw, hvw]
  have e0 : v 0 + w 0 = t * y k + t * z k := by simp [v, w, orient, e, f, signs]
  have e1 : u 1 + w 1 = r * x j + r * z j := by simp [u, w, orient, e, f, signs]
  have e2 : u 2 + v 2 = s * x i + s * y i := by simp [u, v, orient, e, f, signs]
  have hbox := oriented_core hp u v w (by rw [hu, hv, hw]; exact hS)
    (by rw [hu, hsumNorm]; exact hxT) (by rw [hv, hsumNorm]; exact hyT)
    (by rw [hw, hsumNorm]; exact hzT) (by rw [hsumNorm]; exact hT)
    (by rw [hpgs, hsumNorm]; exact hG)
    (by rw [hvw, e0]; exact htyz) (by rw [huw, e1]; exact hrxz)
    (by rw [huv, e2]; exact hsxy)
  refine ⟨![u, v, w], hbox, ?_, ?_, ?_, ?_⟩
  · change lpNorm p u + lpNorm p v + lpNorm p w = 3
    rw [hu, hv, hw]; exact hS
  · change lpNorm p (u + v + w) < 3 * q
    rw [hsumNorm]; exact hTq
  · change pairGapSum (lpNorm p) u v w < 2 / ((448 / 1000) * p)
    rw [hpgs]; exact hGp
  · change hlawkaDeficit p K u v w < 0
    dsimp [u, v, w]
    rwa [hlawkaDeficit_orient p K e signs x y z hsigns]

end Hl32Coarse

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff32.coarse32 : ∀ p : ℝ, 32 ≤ p → p ≤ 50 →
    (448 / 1000 : ℝ) * p < cyclicConstant p →
    ∀ q : ℝ, 0 < q → q ≤ 386 / 1000 → scalarEnvelope p q < cyclicConstant p →
    ∀ x y z : Fin 3 → ℝ, hlawkaDeficit p (cyclicConstant p) x y z < 0 →
      ∃ X : Triple,
        (∀ j i, if j = i then -(1158 / 1000 : ℝ) ≤ X j i ∧ X j i ≤ -(555 / 1000 : ℝ)
                 else (79 / 100 : ℝ) ≤ X j i ∧ X j i ≤ (1158 / 1000 : ℝ)) ∧
        lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 ∧
        lpNorm p (X 0 + X 1 + X 2) < 3 * q ∧
        pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448 / 1000) * p) ∧
        tripleDeficit p (cyclicConstant p) X < 0 := by
  intro p hp _ hlin q hq0 hq henv x y z hf
  exact Hl32Coarse.coarse_box32 hp hlin hq0 hq henv x y z hf

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open HlawkaSchatten.DiagonalCutoff32

theorem solution : ∀ p : ℝ, 32 ≤ p → p ≤ 50 →
    (448 / 1000 : ℝ) * p < cyclicConstant p →
    ∀ q : ℝ, 0 < q → q ≤ 386 / 1000 → scalarEnvelope p q < cyclicConstant p →
    ∀ x y z : Fin 3 → ℝ, hlawkaDeficit p (cyclicConstant p) x y z < 0 →
      ∃ X : Triple,
        (∀ j i, if j = i then -(1158 / 1000 : ℝ) ≤ X j i ∧ X j i ≤ -(555 / 1000 : ℝ)
                 else (79 / 100 : ℝ) ≤ X j i ∧ X j i ≤ (1158 / 1000 : ℝ)) ∧
        lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3 ∧
        lpNorm p (X 0 + X 1 + X 2) < 3 * q ∧
        pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < 2 / ((448 / 1000) * p) ∧
        tripleDeficit p (cyclicConstant p) X < 0 := by
  exact HlawkaSchatten.DiagonalCutoff32.coarse32
