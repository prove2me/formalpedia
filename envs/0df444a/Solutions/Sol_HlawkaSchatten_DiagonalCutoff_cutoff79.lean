-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff.cutoff79
-- status  : ACCEPTED   (prove)
-- author  : @sorry_not_sorry
-- created : 2026-10-08T00:40:24.952394+00:00
-- url     : https://prove2.me/submissions/d75db892-315f-4215-afd3-efd06f955356

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxConvexity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ComplexTransfer
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Coordinates
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_CyclicWitness
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_OrbitAveraging
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_antitoneOn_scalarEnvelope
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclicConstant_le_of_complex_constant
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclic_denominator_pos
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclic_maximum_attained
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_exists_normalized_failure
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_normalized_pair_sum_le
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_real_bound_of_fin_three
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff_convex_box79
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff_cutoff80
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff_scalar_window79

namespace HlawkaCached79Curvature
open HlawkaSchatten.DiagonalConstruction
def codexEntryBox : Set Triple := {X | ∀ j i, |X j i - cyclicCenter j i| ≤ (195/1000 : ℝ)}
theorem convex_codexEntryBox : Convex ℝ codexEntryBox := by
  intro X hX Y hY a b ha hb hab j i
  have heq : (a • X + b • Y) j i - cyclicCenter j i =
      a * (X j i - cyclicCenter j i) + b * (Y j i - cyclicCenter j i) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [congrArg (fun t : ℝ ↦ t * cyclicCenter j i) hab]
  rw [heq]
  calc
    _ ≤ |a * (X j i - cyclicCenter j i)| + |b * (Y j i - cyclicCenter j i)| := abs_add_le _ _
    _ = a * |X j i - cyclicCenter j i| + b * |Y j i - cyclicCenter j i| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * (195 / 1000) + b * (195 / 1000) :=
      add_le_add (mul_le_mul_of_nonneg_left (hX j i) ha)
        (mul_le_mul_of_nonneg_left (hY j i) hb)
    _ = 195 / 1000 := by nlinarith




theorem convexOn_tripleDeficit {p K : ℝ} (hp : 79 ≤ p)
    (hK : (23/50 : ℝ)*p ≤ K) (hKp : K ≤ p/2) :
    ConvexOn ℝ codexEntryBox (tripleDeficit p K) :=
  HlawkaSchatten.DiagonalCutoff.convex_box79 p K hp hK hKp
end HlawkaCached79Curvature


/- Local module: Solutions.Hlawka84_Localization -/
/- Adapted from Ezzeri Esa's Apache-2.0 development and Claude Opus 5.5's
accepted cutoff-87 localization proof, with new cutoff-84 parameters. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace HlawkaCodex79Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open HlawkaCached79Curvature (codexEntryBox)

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]


theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _


theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]

@[simp]

theorem lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → E) = 0 := by
  simp [lpNorm, hp.ne']

@[simp]

theorem lpNorm_neg (p : ℝ) (x : ι → E) : lpNorm p (-x) = lpNorm p x := by
  simp [lpNorm]


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



/-- The two non-dominant coordinates retain their positive power contribution. -/
theorem norm_le_dominant_with_tail {p : ℝ} (hp : 1 < p)
    (v : Fin 3 → ℝ) (k : Fin 3) (hm : 0 ≤ v k)
    (hsmall : ∀ i, i ≠ k → |v i| ≤ v k / 2) :
    lpNorm p v ≤ v k * (1 + 2 * (1 / 2 : ℝ) ^ p / p) := by
  have hp0 : 0 < p := by linarith
  have hpow (i : Fin 3) (hi : i ≠ k) :
      |v i| ^ p ≤ (v k) ^ p * (1 / 2 : ℝ) ^ p := by
    have h := Real.rpow_le_rpow (abs_nonneg (v i)) (hsmall i hi) hp0.le
    rw [show v k / 2 = v k * (1 / 2) by ring,
      Real.mul_rpow hm (by norm_num)] at h
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
    (s := 2 * (1 / 2 : ℝ) ^ p) (p := 1 / p) (by have h := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) p; linarith)
    (by positivity) (by simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp.le))
  have hmul := mul_le_mul_of_nonneg_left hroot hm
  change lpNorm p v ≤ _ at hnorm
  calc
    _ ≤ v k * (1 + 1 / p * (2 * (1 / 2 : ℝ) ^ p)) := hnorm.trans hmul
    _ = _ := by ring


/-- The strict pair gap absorbs a uniformly bounded, nonzero tail. -/
theorem pair_coordinate_deficit {p : ℝ} (hp : 79 ≤ p)
    (x y : Fin 3 → ℝ) (k : Fin 3)
    (hx : lpNorm p x ≤ 9 / 25) (hy : lpNorm p y ≤ 9 / 25)
    (hgap : pairGap (lpNorm p) x y < 100 / (69 * p))
    (hm : 0 ≤ x k + y k)
    (hsmall : ∀ i, i ≠ k → |x i + y i| ≤ (x k + y k) / 2) :
    lpNorm p x + lpNorm p y - (x k + y k) < 20023 / (13800 * p) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  have ha : (1 / 2 : ℝ) ^ p ≤ 1 / 1024 := by
    calc
      _ ≤ (1 / 2 : ℝ) ^ (10 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
      _ = _ := by norm_num
  have hnorm := norm_le_dominant_with_tail (by linarith : 1 < p) (x + y) k hm hsmall
  have hm' : x k + y k ≤ 18 / 25 := by
    have hxk := (le_abs_self (x k)).trans (norm_apply_le_lpNorm hp1 x k)
    have hyk := (le_abs_self (y k)).trans (norm_apply_le_lpNorm hp1 y k)
    linarith
  have ht0 : 0 ≤ 2 * (1 / 2 : ℝ) ^ p / p := by positivity
  have ht : 2 * (1 / 2 : ℝ) ^ p / p ≤ 1 / (512 * p) := by
    apply (mul_le_mul_iff_left₀ hp0).mp
    field_simp
    nlinarith
  have hm1 := mul_le_mul_of_nonneg_left ht hm
  have hm2 := mul_le_mul_of_nonneg_right hm' (show 0 ≤ 1 / (512 * p) by positivity)
  have htail : (18 / 25 : ℝ) * (1 / (512 * p)) < 1 / (600 * p) := by
    apply (mul_lt_mul_iff_left₀ hp0).mp
    field_simp
    norm_num
  change lpNorm p (x + y) ≤ (x k + y k) * (1 + 2 * (1 / 2 : ℝ) ^ p / p) at hnorm
  have hE : 100 / (69 * p) + 1 / (600 * p) = 20023 / (13800 * p) := by field_simp; ring
  dsimp only [pairGap] at hgap
  rw [← hE]
  nlinarith


/-- A coarse cyclic box is sufficient for the refined coordinate estimate. -/
theorem coarse_pair_dominance (X : Triple)
    (hbox : ∀ j i, |3 * X j i - cyclicCenter j i| ≤ (1 / 3 : ℝ))
    (a b k : Fin 3) (hab : a ≠ b) (hak : a ≠ k) (hbk : b ≠ k) :
    0 ≤ X a k + X b k ∧
      ∀ i, i ≠ k → |X a i + X b i| ≤ (X a k + X b k) / 2 := by
  have hak' := abs_le.mp (hbox a k)
  have hbk' := abs_le.mp (hbox b k)
  simp only [cyclicCenter, if_neg (Ne.symm hak), if_neg (Ne.symm hbk)] at hak' hbk'
  refine ⟨by linarith, ?_⟩
  intro i hik
  have ha := abs_le.mp (hbox a i)
  have hb := abs_le.mp (hbox b i)
  have hie : i = a ∨ i = b := by
    fin_cases a <;> fin_cases b <;> fin_cases k <;> fin_cases i <;> simp_all
  rcases hie with rfl | rfl
  · simp only [cyclicCenter, ite_true, if_neg hab] at ha hb
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · simp only [cyclicCenter, ite_true, if_neg (Ne.symm hab)] at ha hb
    exact abs_le.mpr ⟨by linarith, by linarith⟩


/-- The second localization stage keeps the orientation fixed. -/
theorem codex79_bootstrap {p : ℝ} (hp : 79 ≤ p) (x y z : Fin 3 → ℝ)
    (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hx : lpNorm p x ≤ 9 / 25)
    (hy : lpNorm p y ≤ 9 / 25)
    (hz : lpNorm p z ≤ 9 / 25)
    (hT : lpNorm p (x + y + z) ≤ 9 / 25)
    (hgap : pairGapSum (lpNorm p) x y z < 100 / (69 * p))
    (hbox : ∀ j i, |3 * (![x,y,z] : Triple) j i - cyclicCenter j i| ≤ (1 / 3 : ℝ)) :
    ![((32 / 10 : ℝ)) • x, ((32 / 10 : ℝ)) • y, ((32 / 10 : ℝ)) • z] ∈ codexEntryBox := by
  have hp1 : 1 ≤ p := by linarith
  have hxy0 : 0 ≤ pairGap (lpNorm p) x y := sub_nonneg.mpr (lpNorm_add hp1 x y)
  have hxz0 : 0 ≤ pairGap (lpNorm p) x z := sub_nonneg.mpr (lpNorm_add hp1 x z)
  have hyz0 : 0 ≤ pairGap (lpNorm p) y z := sub_nonneg.mpr (lpNorm_add hp1 y z)
  have hxy := coarse_pair_dominance ![x,y,z] hbox 0 1 2 (by decide) (by decide) (by decide)
  have hxz := coarse_pair_dominance ![x,y,z] hbox 0 2 1 (by decide) (by decide) (by decide)
  have hyz := coarse_pair_dominance ![x,y,z] hbox 1 2 0 (by decide) (by decide) (by decide)
  dsimp only [pairGapSum] at hgap
  have hxyE := pair_coordinate_deficit hp x y 2 hx hy (by linarith) hxy.1 hxy.2
  have hxzE := pair_coordinate_deficit hp x z 1 hx hz (by linarith) hxz.1 hxz.2
  have hyzE := pair_coordinate_deficit hp y z 0 hy hz (by linarith) hyz.1 hyz.2
  have hE : 20023 / (13800 * p) ≤ (20023 / 1090200 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hxi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 x i)
  have hyi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 y i)
  have hzi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 z i)
  have ht (i : Fin 3) : x i + y i + z i ≤ 9 / 25 :=
    ((le_abs_self (x i + y i + z i)).trans
      (norm_apply_le_lpNorm hp1 (x + y + z) i)).trans hT
  intro j i
  fin_cases j <;> fin_cases i <;>
    norm_num [cyclicCenter, Pi.smul_apply, smul_eq_mul, abs_le] <;>
    constructor <;> linarith! [hxi 0, hxi 1, hxi 2, hyi 0, hyi 1, hyi 2,
      hzi 0, hzi 1, hzi 2, ht 0, ht 1, ht 2]


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


theorem normalized_failure_total_lt_q0 {p : ℝ} (hp : 79 ≤ p)
    (hlinear : (23 / 50 : ℝ) * p < cyclicConstant p)
    (henvelope : scalarEnvelope p (9 / 25) < cyclicConstant p)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    lpNorm p (x + y + z) < 9 / 25 := by
  have hp1 : 1 < p := by linarith
  have hK : 1 ≤ cyclicConstant p := by linarith
  have hq1 := normalized_failure_total_lt_one hp1.le (by linarith) x y z hS hf
  have henv := normalized_failure_ratio_lt_envelope hp1 hK x y z hS hf
  by_contra hn
  have hq0 : (9 / 25 : ℝ) ≤ lpNorm p (x + y + z) := le_of_not_gt hn
  have hm := antitoneOn_scalarEnvelope hp1.le
    (show (9 / 25 : ℝ) ∈ Set.Ico 0 1 by norm_num)
    (show lpNorm p (x + y + z) ∈ Set.Ico 0 1 from ⟨lpNorm_nonneg p _, hq1⟩) hq0
  linarith [henvelope]


/-- The scalar data used by the coordinate argument. -/
theorem normalized_failure_confinement {p : ℝ} (hp : 79 ≤ p)
    (hlinear : (23 / 50 : ℝ) * p < cyclicConstant p)
    (henvelope : scalarEnvelope p (9 / 25) < cyclicConstant p)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hx : lpNorm p x ≤ lpNorm p (x + y + z))
    (hy : lpNorm p y ≤ lpNorm p (x + y + z))
    (hz : lpNorm p z ≤ lpNorm p (x + y + z))
    (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    (1 / 3 ≤ lpNorm p (x + y + z) ∧ lpNorm p (x + y + z) < 9 / 25) ∧
      pairGapSum (lpNorm p) x y z < 100 / (69 * p) ∧
      (7 / 25 < lpNorm p x ∧ lpNorm p x < 9 / 25) ∧
      (7 / 25 < lpNorm p y ∧ lpNorm p y < 9 / 25) ∧
      (7 / 25 < lpNorm p z ∧ lpNorm p z < 9 / 25) := by
  have hp1 : 1 < p := by linarith
  have hq := normalized_failure_total_lt_q0 hp hlinear henvelope x y z hS hf
  have hqLower : 1 / 3 ≤ lpNorm p (x + y + z) := by linarith
  have hD := pairGapSum_nonneg hp1.le x y z
  have hK := hlinear
  have hmul := mul_le_mul_of_nonneg_right hK.le hD
  have hf' := hf
  rw [hlawkaDeficit_eq, tripleGap, hS] at hf'
  have hsmall : pairGapSum (lpNorm p) x y z < 100 / (69 * p) := by
    rw [lt_div_iff₀ (show 0 < 69 * p by linarith)]
    nlinarith
  exact ⟨⟨hqLower, hq⟩, hsmall, ⟨by linarith, hx.trans_lt hq⟩,
    ⟨by linarith, hy.trans_lt hq⟩, ⟨by linarith, hz.trans_lt hq⟩⟩


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


theorem signed_entry_le_norm {p s : ℝ} (hp : 1 ≤ p) (hs : |s| = 1)
    (x : Fin 3 → ℝ) (i : Fin 3) : s * x i ≤ lpNorm p x := by
  calc
    _ ≤ |s * x i| := le_abs_self _
    _ = |x i| := by rw [abs_mul, hs, one_mul]
    _ ≤ _ := norm_apply_le_lpNorm hp x i


/-- Small pair gap forces two large entries with one common sign. -/
theorem exists_large_signed_pair {p : ℝ} (hp : 79 ≤ p) (x y : Fin 3 → ℝ)
    (hx : lpNorm p x < 9 / 25) (hy : lpNorm p y < 9 / 25)
    (hgap : pairGap (lpNorm p) x y < 100 / (69 * p)) :
    ∃ i : Fin 3, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      lpNorm p x - 9 / (4 * p) < s * x i ∧
      lpNorm p y - 9 / (4 * p) < s * y i := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  obtain ⟨i, _, hi⟩ := Finset.univ.exists_max_image (fun i ↦ |(x + y) i|)
    Finset.univ_nonempty
  have hmax := lpNorm_le_three_root_mul_max hp0 (x + y) i (fun j ↦ hi j (Finset.mem_univ _))
  let c := ((3 : ℝ) ^ (1 / p))⁻¹
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hmax' : c * lpNorm p (x + y) ≤ |x i + y i| := by
    have hm := mul_le_mul_of_nonneg_left hmax hc0.le
    have he : c * ((3 : ℝ) ^ (1 / p) * |(x + y) i|) = |(x + y) i| := by
      dsimp [c]
      rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    rw [he] at hm
    exact hm
  have hd : 1 - c ≤ Real.log 3 / p := inverse_three_root_deficit p
  have hlog3 : Real.log 3 < 11 / 10 := by linarith [Real.log_three_lt_d9]
  have hs0 : 0 ≤ lpNorm p x + lpNorm p y := add_nonneg (lpNorm_nonneg p x) (lpNorm_nonneg p y)
  have hbound : lpNorm p x + lpNorm p y - |x i + y i| < 9 / (4 * p) := by
    have hS : lpNorm p x + lpNorm p y < 18 / 25 := by linarith
    have hdef := mul_le_mul_of_nonneg_right hd hs0
    have hg := pairGap_nonneg hp1 x y
    have hgap' := mul_le_mul_of_nonneg_right hc1 hg
    have hlogP : 0 ≤ Real.log 3 / p := by positivity
    have hSlog := mul_le_mul_of_nonneg_left hS.le hlogP
    have hlogDiv := (div_lt_div_iff_of_pos_right hp0).mpr hlog3
    have hlogLast := mul_lt_mul_of_pos_right hlogDiv (by norm_num : (0 : ℝ) < 18 / 25)
    dsimp only [pairGap] at hgap hg hgap'
    have hnum : Real.log 3 / p * (18 / 25 : ℝ) + 100 / (69 * p) < 9 / (4 * p) := by
      have hrat : (11 / 10 : ℝ) / p * (18 / 25) + 100 / (69 * p) < 9 / (4 * p) := by
        apply (mul_lt_mul_iff_left₀ hp0).mp
        field_simp
        norm_num
      linarith
    nlinarith
  by_cases hi0 : 0 ≤ x i + y i
  · rw [abs_of_nonneg hi0] at hbound
    have hxi := signed_entry_le_norm hp1 (s := 1) (by norm_num) x i
    have hyi := signed_entry_le_norm hp1 (s := 1) (by norm_num) y i
    exact ⟨i, 1, Or.inl rfl, by linarith, by linarith⟩
  · rw [abs_of_neg (lt_of_not_ge hi0)] at hbound
    have hxi := signed_entry_le_norm hp1 (s := -1) (by norm_num) x i
    have hyi := signed_entry_le_norm hp1 (s := -1) (by norm_num) y i
    exact ⟨i, -1, Or.inr rfl, by linarith, by linarith⟩


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


private theorem signed_row_conflict {a b c A B C q E s r : ℝ}
    (hs : s = 1 ∨ s = -1) (hr : r = 1 ∨ r = -1)
    (ha : E < A) (hsum : q < A + B + C - 3 * E)
    (hsa : A - E < s * a) (hsb : B - E < s * b)
    (hra : A - E < r * a) (hrc : C - E < r * c)
    (habs : |a + b + c| ≤ q) : False := by
  have heq : r = s := by
    rcases hs with rfl | rfl <;> rcases hr with rfl | rfl <;> first | rfl | exfalso; linarith
  subst r
  have hsabs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hu : s * (a + b + c) ≤ q := by
    calc
      _ ≤ |s * (a + b + c)| := le_abs_self _
      _ = |a + b + c| := by rw [abs_mul, hsabs, one_mul]
      _ ≤ q := habs
  nlinarith


private theorem oriented_triple_in_coarse_box {p : ℝ} (hp : 79 ≤ p)
    (x y z : Fin 3 → ℝ)
    (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hx : 7 / 25 < lpNorm p x ∧ lpNorm p x < 9 / 25)
    (hy : 7 / 25 < lpNorm p y ∧ lpNorm p y < 9 / 25)
    (hz : 7 / 25 < lpNorm p z ∧ lpNorm p z < 9 / 25)
    (hT : lpNorm p (x + y + z) < 9 / 25)
    (hx1 : lpNorm p x - 9 / (4 * p) < x 1)
    (hx2 : lpNorm p x - 9 / (4 * p) < x 2)
    (hy0 : lpNorm p y - 9 / (4 * p) < y 0)
    (hy2 : lpNorm p y - 9 / (4 * p) < y 2)
    (hz0 : lpNorm p z - 9 / (4 * p) < z 0)
    (hz1 : lpNorm p z - 9 / (4 * p) < z 1) :
    ∀ j i, |3 * (![x,y,z] : Triple) j i - cyclicCenter j i| ≤ (1 / 3 : ℝ) := by
  have hp1 : 1 ≤ p := by linarith
  have hE : 9 / (4 * p) ≤ (9 / 316 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hxi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 x i)
  have hyi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 y i)
  have hzi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 z i)
  have ht (i : Fin 3) : x i + y i + z i < 9 / 25 :=
    ((le_abs_self (x i + y i + z i)).trans
      (norm_apply_le_lpNorm hp1 (x + y + z) i)).trans_lt hT
  intro j i
  fin_cases j <;> fin_cases i <;>
    norm_num [cyclicCenter, Pi.smul_apply, smul_eq_mul, abs_le] <;>
    constructor <;> linarith! [hxi 0, hxi 1, hxi 2, hyi 0, hyi 1, hyi 2,
      hzi 0, hzi 1, hzi 2, ht 0, ht 1, ht 2]



theorem codex79_exists_failure_in_codexEntryBox {p : ℝ} (hp : 79 ≤ p)
    (hlinear : (23 / 50 : ℝ) * p < cyclicConstant p)
    (henvelope : scalarEnvelope p (9 / 25) < cyclicConstant p)
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    ∃ X ∈ codexEntryBox, tripleDeficit p (cyclicConstant p) X < 0 := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 < p := by linarith
  obtain ⟨x, y, z, hf, hS, hxT, hyT, hzT⟩ :=
    exists_normalized_failure hp0 (by linarith : 1 ≤ cyclicConstant p) x y z hf
  obtain ⟨⟨_, hT⟩, hgap, hx, hy, hz⟩ :=
    normalized_failure_confinement hp hlinear henvelope x y z hS hxT hyT hzT hf
  have hxy0 := pairGap_nonneg hp1.le x y
  have hxz0 := pairGap_nonneg hp1.le x z
  have hyz0 := pairGap_nonneg hp1.le y z
  have hgapTotal := hgap
  dsimp only [pairGapSum] at hgap
  obtain ⟨i, s, hs, hsx, hsy⟩ := exists_large_signed_pair hp x y hx.2 hy.2 (by linarith)
  obtain ⟨j, r, hr, hrx, hrz⟩ := exists_large_signed_pair hp x z hx.2 hz.2 (by linarith)
  obtain ⟨k, t, ht, hty, htz⟩ := exists_large_signed_pair hp y z hy.2 hz.2 (by linarith)
  have hE : 9 / (4 * p) ≤ (9 / 316 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have habs (l : Fin 3) : |x l + y l + z l| ≤ lpNorm p (x + y + z) :=
    norm_apply_le_lpNorm hp1.le (x + y + z) l
  have hij : i ≠ j := by
    intro heq
    subst j
    exact signed_row_conflict hs hr (by linarith [hx.1]) (by linarith)
      hsx hsy hrx hrz (habs i)
  have hik : i ≠ k := by
    intro heq
    subst k
    have hsym : |y i + x i + z i| ≤ lpNorm p (x + y + z) := by
      simpa only [add_comm, add_left_comm, add_assoc] using habs i
    exact signed_row_conflict hs ht (by linarith [hy.1]) (by linarith)
      hsy hsx hty htz hsym
  have hjk : j ≠ k := by
    intro heq
    subst k
    have hsym : |z j + x j + y j| ≤ lpNorm p (x + y + z) := by
      simpa only [add_comm, add_left_comm, add_assoc] using habs j
    exact signed_row_conflict hr ht (by linarith [hz.1]) (by linarith)
      hrz hrx htz hty hsym
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
  have hsumNorm : lpNorm p (u + v + w) = lpNorm p (x + y + z) := by
    dsimp [u, v, w]
    rw [← orient_add, ← orient_add, lpNorm_orient p e signs _ hsigns]
  have hcoarse : ∀ j i, |3 * (![u,v,w] : Triple) j i - cyclicCenter j i| ≤ (1 / 3 : ℝ) := by
    apply oriented_triple_in_coarse_box hp u v w
    · rwa [hu, hv, hw]
    · rwa [hu]
    · rwa [hv]
    · rwa [hw]
    · rwa [hsumNorm]
    · simpa [hu, u, orient, e, f, signs] using hrx
    · simpa [hu, u, orient, e, f, signs] using hsx
    · simpa [hv, v, orient, e, f, signs] using hty
    · simpa [hv, v, orient, e, f, signs] using hsy
    · simpa [hw, w, orient, e, f, signs] using htz
    · simpa [hw, w, orient, e, f, signs] using hrz
  have hgapOriented : pairGapSum (lpNorm p) u v w < 100 / (69 * p) := by
    dsimp [u,v,w]
    simpa only [pairGapSum, pairGap, ← orient_add, lpNorm_orient p e signs _ hsigns] using hgapTotal
  refine ⟨![((32 / 10 : ℝ)) • u, ((32 / 10 : ℝ)) • v, ((32 / 10 : ℝ)) • w], ?_, ?_⟩
  · apply codex79_bootstrap hp u v w
    · rwa [hu,hv,hw]
    · rw [hu]; exact hx.2.le
    · rw [hv]; exact hy.2.le
    · rw [hw]; exact hz.2.le
    · rw [hsumNorm]; exact hT.le
    · exact hgapOriented
    · exact hcoarse
  · change hlawkaDeficit p (cyclicConstant p) (((32 / 10 : ℝ)) • u) (((32 / 10 : ℝ)) • v) (((32 / 10 : ℝ)) • w) < 0
    rw [hlawkaDeficit_smul hp0]
    have hfail : hlawkaDeficit p (cyclicConstant p) u v w < 0 := by
      dsimp [u, v, w]
      rwa [hlawkaDeficit_orient p (cyclicConstant p) e signs x y z hsigns]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < (32 / 10 : ℝ))]
    linarith

end HlawkaCodex79Localization


/- Local module: Solutions.Hlawka85_Integration -/
/- Adapted from the accepted cutoff-87 transfer development, itself
from Ezzeri Esa's Apache-2.0 Hlawka construction. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace HlawkaCached84Transfer85Integration
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction MeasureTheory

section NormLaws
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]


theorem lpNorm_const {p : ℝ} (hp : 0 < p) (x : E) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (fun _ : ι ↦ x) = (Fintype.card ι : ℝ) ^ (1 / p) * ‖x‖ := by
  unfold _root_.HlawkaSchatten.DiagonalConstruction.lpNorm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg x), mul_one_div_cancel hp.ne', Real.rpow_one]


theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (c • x) = |c| * _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p x := by
  unfold _root_.HlawkaSchatten.DiagonalConstruction.lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]


theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold HlawkaSchatten.DiagonalConstruction.lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)

end NormLaws


theorem cyclicA_pos {p t : ℝ} (ht : 0 ≤ t) : 0 < cyclicA p t := by
  unfold cyclicA
  exact Real.rpow_pos_of_pos (by positivity) _


theorem continuous_cyclicA {p : ℝ} (hp : 0 < p) : Continuous (cyclicA p) := by
  exact ((Real.continuous_rpow_const hp.le).add continuous_const).rpow_const
    (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))


theorem continuous_cyclicB {p : ℝ} (hp : 0 < p) : Continuous (cyclicB p) := by
  apply Continuous.rpow_const _ (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))
  exact (continuous_const.mul
    ((continuous_const.sub continuous_id).abs.rpow_const
      (fun _ ↦ Or.inr hp.le))).add continuous_const


theorem continuousOn_cyclicRatio {p : ℝ} (hp : 1 < p) :
    ContinuousOn (cyclicRatio p) (Set.Ici 0) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  apply ContinuousOn.div
  · exact ((continuous_const.mul (continuous_cyclicA hp0)).sub
      (continuous_const.mul (continuous_const.sub continuous_id).abs)).continuousOn
  · exact ((continuous_const.mul (continuous_cyclicA hp0)).sub
      (continuous_const.mul (continuous_cyclicB hp0))).continuousOn
  · intro t ht
    exact (cyclic_denominator_pos hp ht).ne'


theorem cyclicRatio_le_constant {p t : ℝ} (hp : 1 < p)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) : cyclicRatio p t ≤ cyclicConstant p := by
  have hc := (continuousOn_cyclicRatio hp).mono
    (show Set.Icc (1 / 2 : ℝ) 2 ⊆ Set.Ici 0 from fun s hs ↦ by
      simp only [Set.mem_Ici]; linarith [hs.1])
  exact le_csSup (isCompact_Icc.image_of_continuousOn hc).bddAbove
    (Set.mem_image_of_mem (cyclicRatio p) ht)


theorem cyclicRatio_two (p : ℝ) : cyclicRatio p 2 = 1 := by
  have hA : 0 < cyclicA p 2 := cyclicA_pos (by norm_num)
  have hB : cyclicB p 2 = cyclicA p 2 := by
    norm_num [cyclicA, cyclicB, add_comm]
  rw [cyclicRatio, hB]
  norm_num only [sub_self, abs_zero, mul_zero, sub_zero]
  have hden : 6 * cyclicA p 2 - 3 * cyclicA p 2 = 3 * cyclicA p 2 := by ring
  rw [hden, div_self (by positivity)]


theorem one_le_cyclicConstant {p : ℝ} (hp : 1 < p) : 1 ≤ cyclicConstant p := by
  rw [← cyclicRatio_two p]
  exact cyclicRatio_le_constant hp (by norm_num)


theorem lpNorm_cyclicX {p t : ℝ} (ht : 0 ≤ t) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicX t) = cyclicA p t := by
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicX, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring


theorem lpNorm_cyclicY {p t : ℝ} (ht : 0 ≤ t) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicY t) = cyclicA p t := by
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicY, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring


theorem lpNorm_cyclicZ {p t : ℝ} (ht : 0 ≤ t) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicZ t) = cyclicA p t := by
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicZ, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring


theorem lpNorm_cyclicXY (p t : ℝ) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicX t + cyclicY t) = cyclicB p t := by
  have he : cyclicX t + cyclicY t = ![1 - t, 1 - t, 2] := by
    ext i
    fin_cases i <;> simp [cyclicX, cyclicY] <;> ring
  rw [he]
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicB, Fin.sum_univ_three]
  congr 1
  ring


theorem lpNorm_cyclicXZ (p t : ℝ) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicX t + cyclicZ t) = cyclicB p t := by
  have he : cyclicX t + cyclicZ t = ![1 - t, 2, 1 - t] := by
    ext i
    fin_cases i <;> simp [cyclicX, cyclicZ] <;> ring
  rw [he]
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicB, Fin.sum_univ_three]
  congr 1
  ring


theorem lpNorm_cyclicYZ (p t : ℝ) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicY t + cyclicZ t) = cyclicB p t := by
  have he : cyclicY t + cyclicZ t = ![2, 1 - t, 1 - t] := by
    ext i
    fin_cases i <;> simp [cyclicY, cyclicZ] <;> ring
  rw [he]
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicB, Fin.sum_univ_three]
  congr 1
  ring


theorem lpNorm_cyclicXYZ {p : ℝ} (hp : 0 < p) (t : ℝ) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicX t + cyclicY t + cyclicZ t) =
      (3 : ℝ) ^ (1 / p) * |2 - t| := by
  have he : cyclicX t + cyclicY t + cyclicZ t = fun _ ↦ 2 - t := by
    ext i
    fin_cases i <;> simp [cyclicX, cyclicY, cyclicZ] <;> ring
  rw [he, lpNorm_const hp]
  simp


theorem cyclic_tripleGap {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) :
    tripleGap (_root_.HlawkaSchatten.DiagonalConstruction.lpNorm p) (cyclicX t) (cyclicY t) (cyclicZ t) =
      3 * cyclicA p t - (3 : ℝ) ^ (1 / p) * |2 - t| := by
  rw [tripleGap, lpNorm_cyclicX ht, lpNorm_cyclicY ht, lpNorm_cyclicZ ht,
    lpNorm_cyclicXYZ hp]
  ring


theorem cyclic_pairGapSum {p t : ℝ} (ht : 0 ≤ t) :
    pairGapSum (_root_.HlawkaSchatten.DiagonalConstruction.lpNorm p) (cyclicX t) (cyclicY t) (cyclicZ t) =
      6 * cyclicA p t - 3 * cyclicB p t := by
  simp only [pairGapSum, pairGap, lpNorm_cyclicX ht, lpNorm_cyclicY ht,
    lpNorm_cyclicZ ht, lpNorm_cyclicXY, lpNorm_cyclicXZ, lpNorm_cyclicYZ]
  ring

section Deficit
variable {ι : Type*} [Fintype ι]


theorem hlawkaDeficit_eq (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x y z =
      K * pairGapSum (_root_.HlawkaSchatten.DiagonalConstruction.lpNorm p) x y z - tripleGap (_root_.HlawkaSchatten.DiagonalConstruction.lpNorm p) x y z := by
  unfold hlawkaDeficit pairGapSum pairGap tripleGap
  ring


theorem hlawkaDeficit_smul {p : ℝ} (hp : 0 < p) (K c : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K (c • x) (c • y) (c • z) = |c| * hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← smul_add, lpNorm_smul hp]
  ring

end Deficit


section CircleTransfer

instance circleMeasure_isProbability : IsProbabilityMeasure circleMeasure :=
  ⟨by simpa only [TopologicalSpace.PositiveCompacts.coe_top] using
    (Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts Circle)))⟩


theorem continuous_circle_projection_power {p : ℝ} (hp : 0 < p) (z : ℂ) :
    Continuous (fun u : Circle ↦ |((u : ℂ) * z).re| ^ p) := by
  exact ((Complex.continuous_re.comp (continuous_subtype_val.mul continuous_const)).abs).rpow_const
    (fun _ ↦ Or.inr hp.le)


theorem circleMoment_pos {p : ℝ} (hp : 0 < p) : 0 < circleMoment p := by
  have hc : Continuous (fun u : Circle ↦ |(u : ℂ).re| ^ p) := by
    simpa only [mul_one] using continuous_circle_projection_power hp 1
  exact integral_pos_of_integrable_nonneg_nonzero hc
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (fun u ↦ Real.rpow_nonneg (abs_nonneg _) _) (x := (1 : Circle)) (by simp)


theorem integral_circle_projection_power {p : ℝ} (hp : 0 < p) (z : ℂ) :
    (∫ u : Circle, |((u : ℂ) * z).re| ^ p ∂circleMeasure) = circleMoment p * ‖z‖ ^ p := by
  by_cases hz : z = 0
  · simp [hz, hp.ne']
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let v : Circle := ⟨z / (‖z‖ : ℂ), mem_sphere_zero_iff_norm.mpr (by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z), div_self hn])⟩
  have hv : (v : ℂ) * (‖z‖ : ℂ) = z := div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hn)
  have hre (u : Circle) : ((u : ℂ) * z).re = ‖z‖ * ((v * u : Circle) : ℂ).re := by
    calc
      _ = (((v : ℂ) * (u : ℂ)) * (‖z‖ : ℂ)).re := by
        congr 1
        conv_lhs => rw [← hv]
        ring
      _ = _ := by simp only [Circle.coe_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]; ring
  simp_rw [hre, abs_mul, abs_of_nonneg (norm_nonneg z),
    Real.mul_rpow (norm_nonneg z) (abs_nonneg _)]
  rw [integral_const_mul]
  have hrot : (∫ a : Circle, |((v * a : Circle) : ℂ).re| ^ p ∂circleMeasure) = circleMoment p :=
    integral_mul_left_eq_self (μ := circleMeasure) (fun a : Circle ↦ |(a : ℂ).re| ^ p) v
  change ‖z‖ ^ p * (∫ a : Circle, |((v * a : Circle) : ℂ).re| ^ p ∂circleMeasure) = _
  rw [hrot]
  exact mul_comm _ _

variable {ι : Type*} [Fintype ι]


theorem continuous_projectionPower {p : ℝ} (hp : 0 < p) (z : ι → ℂ) :
    Continuous (projectionPower p z) :=
  continuous_finsetSum _ fun i _ ↦ continuous_circle_projection_power hp (z i)


theorem integral_projectionPower {p : ℝ} (hp : 0 < p) (z : ι → ℂ) :
    (∫ u : Circle, projectionPower p z u ∂circleMeasure) = circleMoment p * ∑ i, ‖z i‖ ^ p := by
  unfold projectionPower
  rw [integral_finsetSum Finset.univ (fun i _ ↦
    (continuous_circle_projection_power hp (z i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  simp only [integral_circle_projection_power hp, Finset.mul_sum]

variable {κ : Type*} [Fintype κ]

omit [Fintype ι] [Fintype κ] in

theorem finiteProjection_add (p : ℝ) (w : κ → ℝ) (u : κ → Circle) (z v : ι → ℂ) :
    finiteProjection p w u (z + v) = finiteProjection p w u z + finiteProjection p w u v := by
  ext k
  simp [finiteProjection, mul_add, Complex.add_re]


theorem lpNorm_finiteProjection {p : ℝ} (hp : 0 < p) (w : κ → ℝ) (u : κ → Circle)
    (hw : ∀ k, 0 ≤ w k) (z : ι → ℂ) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (finiteProjection p w u z) = (∑ k, w k * projectionPower p z (u k)) ^ (1 / p) := by
  unfold _root_.HlawkaSchatten.DiagonalConstruction.lpNorm
  congr 1
  simp only [finiteProjection, Fintype.sum_prod_type, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (hw _) _)]
  simp_rw [Real.mul_rpow (Real.rpow_nonneg (hw _) _) (abs_nonneg _),
    ← Real.rpow_mul (hw _), one_div_mul_cancel hp.ne', Real.rpow_one]
  simp only [projectionPower, Finset.mul_sum]


theorem continuous_powerDeficit {p : ℝ} (hp : 0 < p) (K : ℝ) : Continuous (powerDeficit p K) := by
  have hc (i : Fin 7) : Continuous (fun a : Fin 7 → ℝ ↦ (a i) ^ (1 / p)) :=
    (continuous_apply i).rpow_const (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))
  exact ((continuous_const.mul (((hc 0).add (hc 1)).add (hc 2))).add (hc 6)).sub
    (continuous_const.mul (((hc 3).add (hc 4)).add (hc 5)))


theorem continuous_sevenProjections {p : ℝ} (hp : 0 < p) (x y z : ι → ℂ) :
    Continuous (sevenProjections p x y z) :=
  continuous_pi fun k ↦ continuous_projectionPower hp (sevenVectors x y z k)


theorem powerDeficit_nonneg_on_projection_hull {p : ℝ} (hp : 1 < p)
    (hreal : HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p)) (x y z : ι → ℂ) :
    convexHull ℝ (Set.range (sevenProjections p x y z)) ⊆
      {a | 0 ≤ powerDeficit p (cyclicConstant p) a} := by
  classical
  intro a ha
  have hp0 : 0 < p := by linarith
  obtain ⟨κ, _, w, points, hw, _, hpoints, hsum⟩ := mem_convexHull_iff_exists_fintype.mp ha
  choose u hu using hpoints
  have hsum' : ∑ k, w k • sevenProjections p x y z (u k) = a := by
    simpa only [hu] using hsum
  let R : (ι → ℂ) → κ × ι → ℝ := finiteProjection p w u
  have hadd (v v' : ι → ℂ) : R (v + v') = R v + R v' := finiteProjection_add p w u v v'
  have hn (k : Fin 7) : lpNorm p (R (sevenVectors x y z k)) = (a k) ^ (1 / p) := by
    rw [lpNorm_finiteProjection hp0 w u hw]
    congr 1
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sevenProjections] using
      congrFun hsum' k
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  have h3 := hn 3
  have h4 := hn 4
  have h5 := hn 5
  have h6 := hn 6
  change lpNorm p (R x) = (a 0) ^ (1 / p) at h0
  change lpNorm p (R y) = (a 1) ^ (1 / p) at h1
  change lpNorm p (R z) = (a 2) ^ (1 / p) at h2
  change lpNorm p (R (x + y)) = (a 3) ^ (1 / p) at h3
  change lpNorm p (R (x + z)) = (a 4) ^ (1 / p) at h4
  change lpNorm p (R (y + z)) = (a 5) ^ (1 / p) at h5
  change lpNorm p (R (x + y + z)) = (a 6) ^ (1 / p) at h6
  have h := real_bound_of_fin_three hp (by linarith [one_le_cyclicConstant hp]) hreal (R x) (R y) (R z)
  simp only [tripleGap, pairGapSum, pairGap, ← hadd] at h
  change 0 ≤ powerDeficit p (cyclicConstant p) a
  unfold powerDeficit
  rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6]
  nlinarith


/-- The sharp constant passes from real coordinates to complex coordinates. -/
theorem complex_hlawka_bound {p : ℝ} (hp : 1 < p)
    (hreal : HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p)) :
    HasHlawkaConstant (lpNorm p : (ι → ℂ) → ℝ) (cyclicConstant p) := by
  intro x y z
  have hp0 : 0 < p := by linarith
  let F := sevenProjections p x y z
  let m : Fin 7 → ℝ := ∫ u : Circle, F u ∂circleMeasure
  have hcont : Continuous F := continuous_sevenProjections hp0 x y z
  have hfi : Integrable F circleMeasure :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hm : m ∈ closure (convexHull ℝ (Set.range F)) := by
    apply (convex_convexHull ℝ (Set.range F)).closure.integral_mem isClosed_closure _ hfi
    exact Filter.Eventually.of_forall fun u ↦
      subset_closure (subset_convexHull ℝ (Set.range F) (Set.mem_range_self u))
  have hclosed : IsClosed {a | 0 ≤ powerDeficit p (cyclicConstant p) a} :=
    isClosed_le continuous_const (continuous_powerDeficit hp0 _)
  have hnon : 0 ≤ powerDeficit p (cyclicConstant p) m :=
    (closure_minimal (powerDeficit_nonneg_on_projection_hull hp hreal x y z) hclosed) hm
  have hcoord (k : Fin 7) : m k = circleMoment p * ∑ i, ‖sevenVectors x y z k i‖ ^ p := by
    calc
      _ = ∫ u : Circle, F u k ∂circleMeasure :=
        ((ContinuousLinearMap.proj k : (Fin 7 → ℝ) →L[ℝ] ℝ).integral_comp_comm hfi).symm
      _ = _ := integral_projectionPower hp0 (sevenVectors x y z k)
  let c := circleMoment p ^ (1 / p)
  have hc : 0 < c := Real.rpow_pos_of_pos (circleMoment_pos hp0) _
  have hroot (k : Fin 7) : (m k) ^ (1 / p) = c * lpNorm p (sevenVectors x y z k) := by
    rw [hcoord, Real.mul_rpow (circleMoment_pos hp0).le
      (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _)]
    rfl
  simp only [powerDeficit, hroot] at hnon
  change 0 ≤ (2 * cyclicConstant p - 1) *
      (c * lpNorm p x + c * lpNorm p y + c * lpNorm p z) + c * lpNorm p (x + y + z) -
    cyclicConstant p * (c * lpNorm p (x + y) + c * lpNorm p (x + z) + c * lpNorm p (y + z)) at hnon
  have hscaled : 0 ≤ c * (cyclicConstant p * pairGapSum (lpNorm p) x y z -
      tripleGap (lpNorm p) x y z) := by
    convert hnon using 1
    unfold pairGapSum pairGap tripleGap
    ring
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hc).mp hscaled)

end CircleTransfer


/-- A real bound in dimension three gives uniform complex sharpness,
including the empty coordinate dimension. -/
theorem isLeast_of_real_bound {p : ℝ} (hp : 1 < p)
    (hreal : HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p)) :
    IsLeast {C : ℝ | ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C} (cyclicConstant p) := by
  constructor
  · intro n
    exact complex_hlawka_bound hp hreal
  · intro C hC
    exact cyclicConstant_le_of_complex_constant hp (n := 3) (by rfl) (hC 3)

end HlawkaCached84Transfer85Integration


/- Local module: Solutions.Hlawka84_Integration -/
/- Box transfer adapted from the accepted cutoff87 development of Ezzeri
Esa's construction, preserving the generic85 norm and circle transfer proofs. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace HlawkaCodex79Integration
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open HlawkaCached84Transfer85Integration
open HlawkaCached79Curvature (codexEntryBox convex_codexEntryBox)
theorem conjugate_mem_codexEntryBox (e : Equiv.Perm (Fin 3)) {X : Triple} (hX : X ∈ codexEntryBox) :
    conjugate e X ∈ codexEntryBox := by
  intro j i
  simpa [conjugate, cyclicCenter, e.injective.eq_iff] using hX (e j) (e i)

private def permutations : Fin 6 → Equiv.Perm (Fin 3) :=
  ![Equiv.refl _, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
    (Equiv.swap 0 1).trans (Equiv.swap 1 2), (Equiv.swap 1 2).trans (Equiv.swap 0 1)]


private theorem tripleDeficit_conjugate_six (p K : ℝ) (X : Triple) (k : Fin 6) :
    tripleDeficit p K (conjugate (permutations k) X) = tripleDeficit p K X := by
  have he (e : Equiv.Perm (Fin 3)) :
      tripleDeficit p K (conjugate e X) = hlawkaDeficit p K (X (e 0)) (X (e 1)) (X (e 2)) := by
    have hsum (u v : Fin 3 → ℝ) : u ∘ e + v ∘ e = (u + v) ∘ e := rfl
    change hlawkaDeficit p K (X (e 0) ∘ e) (X (e 1) ∘ e) (X (e 2) ∘ e) = _
    simp only [hlawkaDeficit, hsum, lpNorm_comp_equiv]
  rw [he]
  fin_cases k <;> simp [permutations, tripleDeficit, hlawkaDeficit, Equiv.swap_apply_def,
    add_comm, add_left_comm, add_assoc]


theorem orbitAverage_apply (X : Triple) (j i : Fin 3) :
    orbitAverage X j i = if i = j then averageDiagonal X else averageOffDiagonal X := by
  fin_cases j <;> fin_cases i <;>
    norm_num [orbitAverage, permutations, conjugate, Fin.sum_univ_succ, Equiv.swap_apply_def,
      averageDiagonal, averageOffDiagonal, Fin.ext_iff] <;> ring!


theorem orbitAverage_mem_codexEntryBox {X : Triple} (hX : X ∈ codexEntryBox) : orbitAverage X ∈ codexEntryBox := by
  apply convex_codexEntryBox.sum_mem (t := Finset.univ)
  · intros; norm_num
  · norm_num
  · intro k _
    exact conjugate_mem_codexEntryBox _ hX


theorem tripleDeficit_orbitAverage_le {p K : ℝ}
    (hc : ConvexOn ℝ codexEntryBox (tripleDeficit p K)) {X : Triple} (hX : X ∈ codexEntryBox) :
    tripleDeficit p K (orbitAverage X) ≤ tripleDeficit p K X := by
  have h := hc.map_sum_le (t := Finset.univ) (w := fun _ : Fin 6 ↦ (1 / 6 : ℝ))
    (p := fun k ↦ conjugate (permutations k) X) (by intros; norm_num) (by norm_num)
    (fun _ _ ↦ conjugate_mem_codexEntryBox _ hX)
  change tripleDeficit p K (orbitAverage X) ≤ _ at h
  simp only [tripleDeficit_conjugate_six, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, nsmul_eq_mul] at h
  norm_num at h
  linarith


theorem average_parameter_bounds {X : Triple} (hX : X ∈ codexEntryBox) :
    0 < averageOffDiagonal X ∧ -averageDiagonal X / averageOffDiagonal X ∈ Set.Icc (1 / 2) 2 := by
  have hbar := orbitAverage_mem_codexEntryBox hX
  have hd := hbar 0 0
  have ho := hbar 0 1
  rw [orbitAverage_apply] at hd ho
  norm_num [cyclicCenter, abs_le] at hd ho
  have hop : 0 < averageOffDiagonal X := by linarith
  exact ⟨hop, (le_div_iff₀ hop).mpr (by linarith), (div_le_iff₀ hop).mpr (by linarith)⟩


theorem orbitAverage_eq_cyclic (X : Triple) (ho : averageOffDiagonal X ≠ 0) :
    orbitAverage X = ![averageOffDiagonal X • cyclicX (-averageDiagonal X / averageOffDiagonal X),
      averageOffDiagonal X • cyclicY (-averageDiagonal X / averageOffDiagonal X),
      averageOffDiagonal X • cyclicZ (-averageDiagonal X / averageOffDiagonal X)] := by
  ext j i
  rw [orbitAverage_apply]
  fin_cases j <;> fin_cases i <;> norm_num [cyclicX, cyclicY, cyclicZ] <;> field_simp


theorem tripleDeficit_orbitAverage_nonneg {p : ℝ} (hp : 1 < p) {X : Triple} (hX : X ∈ codexEntryBox) :
    0 ≤ tripleDeficit p (cyclicConstant p) (orbitAverage X) := by
  obtain ⟨ho, ht⟩ := average_parameter_bounds hX
  let t := -averageDiagonal X / averageOffDiagonal X
  have ht0 : 0 ≤ t := by dsimp [t]; linarith [ht.1]
  have hratio := cyclicRatio_le_constant hp ht
  have hD := cyclic_denominator_pos hp ht0
  rw [cyclicRatio, div_le_iff₀ hD] at hratio
  have hcyclic : 0 ≤ hlawkaDeficit p (cyclicConstant p) (cyclicX t) (cyclicY t) (cyclicZ t) := by
    rw [hlawkaDeficit_eq, cyclic_tripleGap (zero_lt_one.trans hp) ht0, cyclic_pairGapSum ht0]
    exact sub_nonneg.mpr hratio
  rw [orbitAverage_eq_cyclic X ho.ne']
  change 0 ≤ hlawkaDeficit p (cyclicConstant p) (averageOffDiagonal X • cyclicX t)
    (averageOffDiagonal X • cyclicY t) (averageOffDiagonal X • cyclicZ t)
  rw [hlawkaDeficit_smul (zero_lt_one.trans hp)]
  exact mul_nonneg (abs_nonneg _) hcyclic


theorem tripleDeficit_nonneg_of_convex {p : ℝ} (hp : 1 < p)
    (hc : ConvexOn ℝ codexEntryBox (tripleDeficit p (cyclicConstant p)))
    {X : Triple} (hX : X ∈ codexEntryBox) : 0 ≤ tripleDeficit p (cyclicConstant p) X :=
  (tripleDeficit_orbitAverage_nonneg hp hX).trans (tripleDeficit_orbitAverage_le hc hX)


/-- Localization and convexity suffice for the real three-coordinate bound. -/
theorem real_bound_of_box_convex {p : ℝ} (hp : 1 < p)
    (hlocal : ∀ x y z : Fin 3 → ℝ,
      hlawkaDeficit p (cyclicConstant p) x y z < 0 →
        ∃ X ∈ codexEntryBox, tripleDeficit p (cyclicConstant p) X < 0)
    (hc : ConvexOn ℝ codexEntryBox (tripleDeficit p (cyclicConstant p))) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  intro x y z
  by_contra hn
  have hf : hlawkaDeficit p (cyclicConstant p) x y z < 0 := by
    rw [hlawkaDeficit_eq]
    linarith
  obtain ⟨X, hX, hneg⟩ := hlocal x y z hf
  exact (not_lt_of_ge (tripleDeficit_nonneg_of_convex hp hc hX)) hneg


end HlawkaCodex79Integration


/- Local module: Solutions.Hlawka84_CyclicUpperBound -/

set_option autoImplicit false

namespace HlawkaCodex79Scalars
open HlawkaSchatten.DiagonalConstruction

theorem cyclicA_lower {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) :
    1 + (69 / 100 : ℝ) / p ≤ cyclicA p t := by
  have hlog : (69 / 100 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have he := Real.add_one_le_exp (Real.log 2 * (1 / p))
  have hr : 1 + (69 / 100 : ℝ) / p ≤ (2 : ℝ) ^ (1 / p) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have hm := mul_le_mul_of_nonneg_right hlog (one_div_nonneg.mpr hp.le)
    simp only [div_eq_mul_inv, one_mul] at he hm ⊢
    linarith
  exact hr.trans (Real.rpow_le_rpow (by norm_num)
    (by linarith [Real.rpow_nonneg ht p])
    (one_div_nonneg.mpr hp.le))

theorem cyclicB_upper {p t : ℝ} (hp : 79 ≤ p) (ht : t ∈ Set.Icc (1 / 2) 2) :
    cyclicB p t ≤ 2 + (1 / p) / 100 := by
  have hp0 : 0 < p := by linarith
  have hx0 : 0 ≤ 1 / p := by positivity
  have hx1 : 1 / p ≤ 1 := (div_le_iff₀ hp0).mpr (by linarith)
  have habs : |1-t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hpow : (2 : ℝ) ^ p ≥ 400 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show (9 : ℝ) ≤ p by linarith)
    norm_num at h
    linarith
  have htwo : 0 < (2 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
  have htail : 4 / (2 : ℝ) ^ p ≤ 1 / 100 := by
    rw [div_le_iff₀ htwo]
    linarith
  have hb : cyclicB p t ≤ (2 + (2 : ℝ) ^ p) ^ (1 / p) := by
    apply Real.rpow_le_rpow (by positivity) _ hx0
    have h := Real.rpow_le_rpow (abs_nonneg _) habs hp0.le
    simp only [Real.one_rpow] at h
    linarith
  have heq : (2 + (2 : ℝ) ^ p) ^ (1 / p) =
      2 * (1 + 2 / (2 : ℝ) ^ p) ^ (1 / p) := by
    rw [show 2 + (2 : ℝ) ^ p = (2 : ℝ) ^ p * (1 + 2 / (2 : ℝ) ^ p) by
      field_simp; ring,
      Real.mul_rpow htwo.le (by positivity), ← Real.rpow_mul (by norm_num),
      mul_one_div_cancel hp0.ne', Real.rpow_one]
  have hconc := rpow_one_add_le_one_add_mul_self
    (s := 2 / (2 : ℝ) ^ p)
    (by linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 2) htwo.le]) hx0 hx1
  rw [heq] at hb
  have hm := mul_le_mul_of_nonneg_left hconc (by norm_num : (0 : ℝ) ≤ 2)
  have ht0 := mul_le_mul_of_nonneg_right htail hx0
  have halg : 2 * (1 + (1/p) * (2 / (2 : ℝ) ^ p)) =
      2 + (4 / (2 : ℝ) ^ p) * (1/p) := by ring
  rw [halg] at hm
  nlinarith

theorem cyclicRatio_le_half_exponent {p t : ℝ} (hp : 79 ≤ p)
    (ht : t ∈ Set.Icc (1 / 2) 2) : cyclicRatio p t ≤ p / 2 := by
  have hp0 : 0 < p := by linarith
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hden := cyclic_denominator_pos (show 1 < p by linarith) ht0
  have hA := cyclicA_lower (t := t) hp0 ht0
  have hB := cyclicB_upper hp ht
  have htA : t ≤ cyclicA p t := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg ht0 p)
      (show t ^ p ≤ t ^ p + 2 by linarith) (one_div_nonneg.mpr hp0.le)
    rw [← Real.rpow_mul ht0, mul_one_div_cancel hp0.ne', Real.rpow_one] at h
    exact h
  have hthree : 1 ≤ (3 : ℝ) ^ (1/p) := Real.one_le_rpow (by norm_num) (by positivity)
  have hnum : 3 * cyclicA p t - (3 : ℝ) ^ (1/p) * |2-t| ≤ 4 * cyclicA p t - 2 := by
    have h := mul_le_mul_of_nonneg_right hthree (abs_nonneg (2-t))
    rw [abs_of_nonneg (by linarith [ht.2])] at h
    rw [abs_of_nonneg (by linarith [ht.2])]
    nlinarith
  have hx : 1 / p ≤ 1 / 79 := (one_div_le_one_div_of_le (by norm_num) hp)
  have hpx : p * (1/p) = 1 := mul_one_div_cancel hp0.ne'
  have hAl := mul_le_mul_of_nonneg_left hA (show 0 ≤ 3*p-4 by linarith)
  have hBu := mul_le_mul_of_nonneg_left hB (show 0 ≤ 3*p/2 by positivity)
  have hfinal : 4 * cyclicA p t - 2 ≤ (p/2) * (6 * cyclicA p t - 3 * cyclicB p t) := by
    simp only [div_eq_mul_inv, one_mul] at hAl hBu hpx hx ⊢
    nlinarith
  exact (div_le_iff₀ hden).mpr (hnum.trans hfinal)

theorem cyclicConstant_le_half_exponent {p : ℝ} (hp : 79 ≤ p) :
    cyclicConstant p ≤ p / 2 := by
  obtain ⟨t, ht, he⟩ := cyclic_maximum_attained (show 1 < p by linarith)
  rw [← he]
  exact cyclicRatio_le_half_exponent hp ht

end HlawkaCodex79Scalars


/- Local module: Solutions.Hlawka84_Window -/

set_option autoImplicit false

namespace HlawkaCodex79
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem real_three_window {p : ℝ} (hp : 79 ≤ p) (hp' : p ≤ 80) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  have hp1 : 1 < p := by linarith
  have hlinear := (HlawkaSchatten.DiagonalCutoff.scalar_window79 p hp hp').1
  have hKp := HlawkaCodex79Scalars.cyclicConstant_le_half_exponent hp
  exact HlawkaCodex79Integration.real_bound_of_box_convex hp1
    (HlawkaCodex79Localization.codex79_exists_failure_in_codexEntryBox hp hlinear
      ((HlawkaSchatten.DiagonalCutoff.scalar_window79 p hp hp').2))
    (HlawkaCached79Curvature.convexOn_tripleDeficit hp hlinear.le hKp)

theorem complex_least_window {p : ℝ} (hp : 79 ≤ p) (hp' : p ≤ 80) :
    IsLeast {C : ℝ | ∀ n : ℕ, HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C}
      (cyclicConstant p) :=
  HlawkaCached84Transfer85Integration.isLeast_of_real_bound (by linarith) (real_three_window hp hp')

theorem complex_least_tail80 {p : ℝ} (hp : 80 ≤ p) :
    IsLeast {C : ℝ | ∀ n : ℕ, HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C}
      (cyclicConstant p) := HlawkaSchatten.DiagonalCutoff.cutoff80 p hp

end HlawkaCodex79


/- Local module: Solutions.Sol_HlawkaSchatten_DiagonalCutoff_cutoff79 -/
set_option autoImplicit false
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
/-- The new coupled curvature and scalar localization handle [79,80];
the accepted cutoff80 theorem provides the remaining tail. -/
theorem solution : ∀ p : ℝ, 79 ≤ p →
    IsLeast {C : ℝ | ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C} (cyclicConstant p) := by
  intro p hp
  by_cases h80 : 80 ≤ p
  · exact HlawkaCodex79.complex_least_tail80 h80
  exact HlawkaCodex79.complex_least_window hp (by linarith)
