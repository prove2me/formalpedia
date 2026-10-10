-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff.local_failure62
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-10T07:38:43.232993+00:00
-- url     : https://prove2.me/submissions/8b77732a-f9a3-457f-a624-48e981149aa5

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxHessian
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_exists_normalized_failure
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_normalized_pair_sum_le
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_antitoneOn_scalarEnvelope
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Coordinates
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib
set_option autoImplicit false
/- Solutions/Hlawka62_AsymmetricBoxBounds.lean -/
set_option autoImplicit false
namespace HlawkaCodex62Geometry
open HlawkaSchatten.DiagonalConstruction
noncomputable abbrev entryMin : ℝ := 28719/38750
noncomputable abbrev entryMax : ℝ := 10929/10000
noncomputable abbrev radius : ℝ := 1733/8000
def asymmetricBox : Set Triple := {X | ∀ j i,
  if j = i then -entryMax ≤ X j i ∧ X j i ≤ -entryMin
  else entryMin ≤ X j i ∧ X j i ≤ entryMax}
theorem asymmetricBox_of_radius_upper (X : Triple)
    (hr : ∀ j i, |X j i - cyclicCenter j i| ≤ radius)
    (hu : ∀ j i, |X j i| ≤ entryMax) : X ∈ asymmetricBox := by
  intro j i
  have h := abs_le.mp (hr j i)
  have h' := abs_le.mp (hu j i)
  by_cases he : j = i
  · simp only [he, cyclicCenter, ite_true] at h h' ⊢
    constructor <;> norm_num [entryMin, entryMax, radius] at * <;> linarith!
  · simp only [cyclicCenter, if_neg (Ne.symm he), if_neg he] at h h' ⊢
    constructor <;> norm_num [entryMin, entryMax, radius] at * <;> linarith!
theorem asymmetricBox_of_norm_data (X : Triple) (N : Fin 3 → ℝ)
    (hS : ∑ j, N j = 3) (hN : ∀ j, N j ≤ entryMax)
    (hcoord : ∀ j i, |X j i| ≤ N j)
    (hT : ∀ i, ∑ j, X j i ≤ entryMax)
    (hpair : ∀ i, 3-N i-(453/6200 : ℝ) ≤ (∑ j, X j i)-X i i) :
    X ∈ asymmetricBox := by
  have h0 := hN 0
  have h1 := hN 1
  have h2 := hN 2
  simp only [Fin.sum_univ_three] at hS
  intro j i
  have hc := abs_le.mp (hcoord j i)
  have hn := hN j
  have ht := hT i
  have hp := hpair i
  by_cases he : j = i
  · subst j
    simp only [ite_true]
    constructor
    · linarith!
    · norm_num [entryMin, entryMax] at *
      linarith!
  · simp only [if_neg he]
    refine ⟨?_, by linarith!⟩
    have hc0 := abs_le.mp (hcoord 0 i)
    have hc1 := abs_le.mp (hcoord 1 i)
    have hc2 := abs_le.mp (hcoord 2 i)
    fin_cases j <;> fin_cases i <;> first
    | exact (he rfl).elim
    | norm_num [Fin.sum_univ_three, Fin.ext_iff, entryMin, entryMax] at *; linarith!

theorem column_total_bounds (X : Triple) (hX : X ∈ asymmetricBox) (i : Fin 3) :
    2*entryMin-entryMax ≤ ∑ j, X j i ∧ ∑ j, X j i ≤ 2*entryMax-entryMin := by
  have h0 := hX 0 i
  have h1 := hX 1 i
  have h2 := hX 2 i
  fin_cases i <;> norm_num [Fin.sum_univ_three, Fin.ext_iff] at * <;> constructor <;> linarith!
theorem dominant_pair_bounds (X : Triple) (hX : X ∈ asymmetricBox)
    (a b k : Fin 3) (hak : a ≠ k) (hbk : b ≠ k) :
    2*entryMin ≤ X a k + X b k ∧ X a k + X b k ≤ 2*entryMax := by
  have ha := hX a k
  have hb := hX b k
  simp only [if_neg hak, if_neg hbk] at ha hb
  constructor <;> linarith!
theorem canceled_pair_bounds (X : Triple) (hX : X ∈ asymmetricBox)
    (a b k i : Fin 3) (hab : a ≠ b) (hak : a ≠ k) (hbk : b ≠ k) (hik : i ≠ k) :
    |X a i + X b i| ≤ entryMax-entryMin := by
  have hi : i = a ∨ i = b := by
    fin_cases a <;> fin_cases b <;> fin_cases k <;> fin_cases i <;> simp_all
  have ha := hX a i
  have hb := hX b i
  rcases hi with rfl | rfl
  · simp only [ite_true, if_neg (Ne.symm hab)] at ha hb
    exact abs_le.mpr ⟨by linarith!, by linarith!⟩
  · simp only [ite_true, if_neg hab] at ha hb
    exact abs_le.mpr ⟨by linarith!, by linarith!⟩
theorem rectangular_power_base :
    ((entryMax-entryMin)*(2*entryMax-entryMin)) /
      ((2*entryMin)*(2*entryMin-entryMax)) < (9/10 : ℝ) := by norm_num
end HlawkaCodex62Geometry
/- Solutions/Hlawka62_Localization.lean -/
/- Adapted from Ezzeri Esa's Apache-2.0 development and Claude Opus 5.5's
accepted cutoff-87 localization proof, with new cutoff-80 parameters and retained row-norm upper bounds. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace HlawkaCodex62Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open HlawkaCodex62Geometry (asymmetricBox)

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
    (hsmall : ∀ i, i ≠ k → |v i| ≤ v k * (5 / 6)) :
    lpNorm p v ≤ v k * (1 + 2 * (5 / 6 : ℝ) ^ p / p) := by
  have hp0 : 0 < p := by linarith
  have hpow (i : Fin 3) (hi : i ≠ k) :
      |v i| ^ p ≤ (v k) ^ p * (5 / 6 : ℝ) ^ p := by
    have h := Real.rpow_le_rpow (abs_nonneg (v i)) (hsmall i hi) hp0.le
    rw [Real.mul_rpow hm (by norm_num)] at h
    exact h
  have hsum : (∑ i, |v i| ^ p) ≤ (v k) ^ p * (1 + 2 * (5 / 6 : ℝ) ^ p) := by
    fin_cases k
    · change 0 ≤ v 0 at hm
      have hleft : |v 1| ^ p ≤ v 0 ^ p * (5 / 6 : ℝ) ^ p := hpow 1 (by decide)
      have hright : |v 2| ^ p ≤ v 0 ^ p * (5 / 6 : ℝ) ^ p := hpow 2 (by decide)
      simp only [Fin.sum_univ_three]
      change |v 0| ^ p + |v 1| ^ p + |v 2| ^ p ≤ v 0 ^ p * (1 + 2 * (5 / 6 : ℝ) ^ p)
      rw [abs_of_nonneg hm]
      nlinarith
    · change 0 ≤ v 1 at hm
      have hleft : |v 0| ^ p ≤ v 1 ^ p * (5 / 6 : ℝ) ^ p := hpow 0 (by decide)
      have hright : |v 2| ^ p ≤ v 1 ^ p * (5 / 6 : ℝ) ^ p := hpow 2 (by decide)
      simp only [Fin.sum_univ_three]
      change |v 0| ^ p + |v 1| ^ p + |v 2| ^ p ≤ v 1 ^ p * (1 + 2 * (5 / 6 : ℝ) ^ p)
      rw [abs_of_nonneg hm]
      nlinarith
    · change 0 ≤ v 2 at hm
      have hleft : |v 0| ^ p ≤ v 2 ^ p * (5 / 6 : ℝ) ^ p := hpow 0 (by decide)
      have hright : |v 1| ^ p ≤ v 2 ^ p * (5 / 6 : ℝ) ^ p := hpow 1 (by decide)
      simp only [Fin.sum_univ_three]
      change |v 0| ^ p + |v 1| ^ p + |v 2| ^ p ≤ v 2 ^ p * (1 + 2 * (5 / 6 : ℝ) ^ p)
      rw [abs_of_nonneg hm]
      nlinarith
  have hnorm := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg (v i)) p)
    hsum (one_div_nonneg.mpr hp0.le)
  rw [Real.mul_rpow (Real.rpow_nonneg hm _) (by positivity),
    ← Real.rpow_mul hm, mul_one_div_cancel hp0.ne', Real.rpow_one] at hnorm
  have hroot := rpow_one_add_le_one_add_mul_self
    (s := 2 * (5 / 6 : ℝ) ^ p) (p := 1 / p) (by have h := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 5/6) p; linarith)
    (by positivity) (by simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp.le))
  have hmul := mul_le_mul_of_nonneg_left hroot hm
  change lpNorm p v ≤ _ at hnorm
  calc
    _ ≤ v k * (1 + 1 / p * (2 * (5 / 6 : ℝ) ^ p)) := hnorm.trans hmul
    _ = _ := by ring


/-- The strict pair gap absorbs a uniformly bounded, nonzero tail. -/
theorem pair_coordinate_deficit {p : ℝ} (hp : 62 ≤ p)
    (x y : Fin 3 → ℝ) (k : Fin 3)
    (hx : lpNorm p x ≤ 3643/10000) (hy : lpNorm p y ≤ 3643/10000)
    (hgap : pairGap (lpNorm p) x y < 3 / (2 * p))
    (hm : 0 ≤ x k + y k)
    (hsmall : ∀ i, i ≠ k → |x i + y i| ≤ (5 / 6) * (x k + y k)) :
    lpNorm p x + lpNorm p y - (x k + y k) < 151 / (100 * p) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  have ha : (5 / 6 : ℝ) ^ p ≤ 1 / 10000 := by
    have hpow : (5 / 6 : ℝ) ^ p ≤ (5 / 6) ^ (62 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
    have h70 : (5 / 6 : ℝ) ^ (62 : ℝ) < 1 / 10000 := by
      have h4 : (6 / 5 : ℝ) ^ 4 = 1296 / 625 := by norm_num
      have h8 : (6 / 5 : ℝ) ^ 8 = (1296 / 625) ^ 2 := by
        rw [show (6 / 5 : ℝ) ^ 8 = ((6 / 5 : ℝ) ^ 4) ^ 2 by ring, h4]
      have h16 : (6 / 5 : ℝ) ^ 16 = ((1296 / 625) ^ 2) ^ 2 := by
        rw [show (6 / 5 : ℝ) ^ 16 = ((6 / 5 : ℝ) ^ 8) ^ 2 by ring, h8]
      have h32 : (6 / 5 : ℝ) ^ 32 = (((1296 / 625) ^ 2) ^ 2) ^ 2 := by
        rw [show (6 / 5 : ℝ) ^ 32 = ((6 / 5 : ℝ) ^ 16) ^ 2 by ring, h16]
      have h64 : (6 / 5 : ℝ) ^ 64 = ((((1296 / 625) ^ 2) ^ 2) ^ 2) ^ 2 := by
        rw [show (6 / 5 : ℝ) ^ 64 = ((6 / 5 : ℝ) ^ 32) ^ 2 by ring, h32]
      have hbig : (14400 : ℝ) < (6 / 5) ^ 64 := by
        rw [h64]
        norm_num
      have h62 : (6 / 5 : ℝ) ^ 62 = (6 / 5) ^ 64 * (5 / 6) ^ 2 := by
        have hpow62 : (6 / 5 : ℝ) ^ 64 = (6 / 5) ^ 62 * (6 / 5) ^ 2 := by ring
        rw [hpow62]
        field_simp
      have h10000 : (10000 : ℝ) < (6 / 5) ^ 62 := by
        rw [h62]
        have hpos : (0 : ℝ) < (5 / 6) ^ 2 := by norm_num
        have hmul := mul_lt_mul_of_pos_right hbig hpos
        have heq : (14400 : ℝ) * ((5 / 6) ^ 2) = 10000 := by norm_num
        nlinarith [hmul, heq]
      have h62real : (5 / 6 : ℝ) ^ (62 : ℝ) = (5 / 6) ^ (62 : ℕ) := Real.rpow_natCast _ _
      have hinv : (5 / 6 : ℝ) ^ (62 : ℕ) = ((6 / 5) ^ 62)⁻¹ := by
        rw [show (5 / 6 : ℝ) = (6 / 5)⁻¹ by norm_num, inv_pow]
      rw [h62real, hinv]
      simpa [one_div] using (inv_lt_inv₀ (by positivity) (by norm_num)).mpr h10000
    exact hpow.trans h70.le
  have hsmall' : ∀ i, i ≠ k → |(x + y) i| ≤ (x + y) k * (5 / 6) := by
    intro i hi
    simpa [Pi.add_apply, mul_comm] using hsmall i hi
  have hnorm := norm_le_dominant_with_tail (by linarith : 1 < p) (x + y) k hm hsmall'
  have hm' : x k + y k ≤ 73/100 := by
    have hxk := (le_abs_self (x k)).trans (norm_apply_le_lpNorm hp1 x k)
    have hyk := (le_abs_self (y k)).trans (norm_apply_le_lpNorm hp1 y k)
    linarith
  have ht0 : 0 ≤ 2 * (5 / 6 : ℝ) ^ p / p := by positivity
  have ht : 2 * (5 / 6 : ℝ) ^ p / p ≤ 1 / (5000 * p) := by
    apply (mul_le_mul_iff_left₀ hp0).mp
    field_simp
    linarith [ha]
  have hm1 := mul_le_mul_of_nonneg_left ht hm
  have hm2 := mul_le_mul_of_nonneg_right hm' (show 0 ≤ 1 / (5000 * p) by positivity)
  have htail : (73/100 : ℝ) * (1 / (5000 * p)) < 1 / (600 * p) := by
    apply (mul_lt_mul_iff_left₀ hp0).mp
    field_simp
    norm_num
  change lpNorm p (x + y) ≤ (x k + y k) * (1 + 2 * (5 / 6 : ℝ) ^ p / p) at hnorm
  have hE : 3 / (2 * p) + 1 / (600 * p) < 151 / (100 * p) := by
    apply (mul_lt_mul_iff_left₀ hp0).mp
    field_simp
    norm_num
  dsimp only [pairGap] at hgap
  nlinarith


/-- A coarse cyclic box is sufficient for the refined coordinate estimate. -/
theorem coarse_pair_dominance (X : Triple)
    (hbox : ∀ j i, |3 * X j i - cyclicCenter j i| ≤ (9 / 20 : ℝ))
    (a b k : Fin 3) (hab : a ≠ b) (hak : a ≠ k) (hbk : b ≠ k) :
    0 ≤ X a k + X b k ∧
      ∀ i, i ≠ k → |X a i + X b i| ≤ (5 / 6) * (X a k + X b k) := by
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
theorem codex62_bootstrap {p : ℝ} (hp : 62 ≤ p) (x y z : Fin 3 → ℝ)
    (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hx : lpNorm p x ≤ 3643/10000) (hy : lpNorm p y ≤ 3643/10000) (hz : lpNorm p z ≤ 3643/10000)
    (hT : lpNorm p (x+y+z) ≤ 3643/10000)
    (hgap : pairGapSum (lpNorm p) x y z < 3/(2*p))
    (hbox : ∀ j i, |3 * (![x,y,z] : Triple) j i - cyclicCenter j i| ≤ (9/20 : ℝ)) :
    ![(3 : ℝ) • x, (3 : ℝ) • y, (3 : ℝ) • z] ∈ asymmetricBox := by
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
  have hE : 151/(100*p) ≤ (151/6200 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hxi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 x i)
  have hyi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 y i)
  have hzi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 z i)
  have ht (i : Fin 3) : x i+y i+z i ≤ 3643/10000 :=
    ((le_abs_self _).trans (norm_apply_le_lpNorm hp1 (x+y+z) i)).trans hT
  apply HlawkaCodex62Geometry.asymmetricBox_of_norm_data
    ![(3 : ℝ) • x, (3 : ℝ) • y, (3 : ℝ) • z]
    ![3*lpNorm p x, 3*lpNorm p y, 3*lpNorm p z]
  · rw [Fin.sum_univ_three]
    change 3*lpNorm p x + 3*lpNorm p y + 3*lpNorm p z = 3
    linarith
  · intro j
    fin_cases j <;> norm_num [HlawkaCodex62Geometry.entryMax] <;> linarith
  · intro j i
    fin_cases j <;> simp [Pi.smul_apply, smul_eq_mul, abs_mul]
    all_goals first
    | exact norm_apply_le_lpNorm hp1 x i
    | exact norm_apply_le_lpNorm hp1 y i
    | exact norm_apply_le_lpNorm hp1 z i
  · intro i
    rw [Fin.sum_univ_three]
    change 3*x i+3*y i+3*z i ≤ (10929/10000 : ℝ)
    linarith [ht i]
  · intro i
    rw [Fin.sum_univ_three]
    fin_cases i
    · change 3-3*lpNorm p x-(453/6200 : ℝ) ≤ (3*x 0+3*y 0+3*z 0)-3*x 0
      linarith [hS,hyzE,hE]
    · change 3-3*lpNorm p y-(453/6200 : ℝ) ≤ (3*x 1+3*y 1+3*z 1)-3*y 1
      linarith [hS,hxzE,hE]
    · change 3-3*lpNorm p z-(453/6200 : ℝ) ≤ (3*x 2+3*y 2+3*z 2)-3*z 2
      linarith [hS,hxyE,hE]


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


theorem normalized_failure_total_lt_q0 {p : ℝ} (hp : 62 ≤ p)
    (hlinear : (23 / 50 : ℝ) * p < cyclicConstant p)
    (henvelope : scalarEnvelope p (3643/10000) < cyclicConstant p)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    lpNorm p (x + y + z) < 3643/10000 := by
  have hp1 : 1 < p := by linarith
  have hK : 1 ≤ cyclicConstant p := by linarith
  have hq1 := normalized_failure_total_lt_one hp1.le (by linarith) x y z hS hf
  have henv := normalized_failure_ratio_lt_envelope hp1 hK x y z hS hf
  by_contra hn
  have hq0 : (3643/10000 : ℝ) ≤ lpNorm p (x + y + z) := le_of_not_gt hn
  have hm := antitoneOn_scalarEnvelope hp1.le
    (show (3643/10000 : ℝ) ∈ Set.Ico 0 1 by norm_num)
    (show lpNorm p (x + y + z) ∈ Set.Ico 0 1 from ⟨lpNorm_nonneg p _, hq1⟩) hq0
  linarith [henvelope]


/-- The scalar data used by the coordinate argument. -/
theorem normalized_failure_confinement {p : ℝ} (hp : 62 ≤ p)
    (hlinear : (23 / 50 : ℝ) * p < cyclicConstant p)
    (henvelope : scalarEnvelope p (3643/10000) < cyclicConstant p)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hx : lpNorm p x ≤ lpNorm p (x + y + z))
    (hy : lpNorm p y ≤ lpNorm p (x + y + z))
    (hz : lpNorm p z ≤ lpNorm p (x + y + z))
    (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    (1 / 3 ≤ lpNorm p (x + y + z) ∧ lpNorm p (x + y + z) < 3643/10000) ∧
      pairGapSum (lpNorm p) x y z < 3 / (2 * p) ∧
      (27/100 < lpNorm p x ∧ lpNorm p x < 3643/10000) ∧
      (27/100 < lpNorm p y ∧ lpNorm p y < 3643/10000) ∧
      (27/100 < lpNorm p z ∧ lpNorm p z < 3643/10000) := by
  have hp1 : 1 < p := by linarith
  have hq := normalized_failure_total_lt_q0 hp hlinear henvelope x y z hS hf
  have hqLower : 1 / 3 ≤ lpNorm p (x + y + z) := by linarith
  have hD := pairGapSum_nonneg hp1.le x y z
  have hK := hlinear
  have hmul := mul_le_mul_of_nonneg_right hK.le hD
  have hf' := hf
  rw [hlawkaDeficit_eq, tripleGap, hS] at hf'
  have hsmall : pairGapSum (lpNorm p) x y z < 3 / (2 * p) := by
    rw [lt_div_iff₀ (show 0 < 2 * p by linarith)]
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
theorem exists_large_signed_pair {p : ℝ} (hp : 62 ≤ p) (x y : Fin 3 → ℝ)
    (hx : lpNorm p x < 3643/10000) (hy : lpNorm p y < 3643/10000)
    (hgap : pairGap (lpNorm p) x y < 3 / (2 * p)) :
    ∃ i : Fin 3, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      lpNorm p x - 12 / (5 * p) < s * x i ∧
      lpNorm p y - 12 / (5 * p) < s * y i := by
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
  have hbound : lpNorm p x + lpNorm p y - |x i + y i| < 12 / (5 * p) := by
    have hS : lpNorm p x + lpNorm p y < 73/100 := by linarith
    have hdef := mul_le_mul_of_nonneg_right hd hs0
    have hg := pairGap_nonneg hp1 x y
    have hgap' := mul_le_mul_of_nonneg_right hc1 hg
    have hlogP : 0 ≤ Real.log 3 / p := by positivity
    have hSlog := mul_le_mul_of_nonneg_left hS.le hlogP
    have hlogDiv := (div_lt_div_iff_of_pos_right hp0).mpr hlog3
    have hlogLast := mul_lt_mul_of_pos_right hlogDiv (by norm_num : (0 : ℝ) < 73/100)
    dsimp only [pairGap] at hgap hg hgap'
    have hnum : Real.log 3 / p * (73/100 : ℝ) + 3 / (2 * p) < 12 / (5 * p) := by
      have hrat : (11 / 10 : ℝ) / p * (73/100) + 3 / (2 * p) < 12 / (5 * p) := by
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


private theorem oriented_triple_in_coarse_box {p : ℝ} (hp : 62 ≤ p)
    (x y z : Fin 3 → ℝ)
    (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hx : 27/100 < lpNorm p x ∧ lpNorm p x < 3643/10000)
    (hy : 27/100 < lpNorm p y ∧ lpNorm p y < 3643/10000)
    (hz : 27/100 < lpNorm p z ∧ lpNorm p z < 3643/10000)
    (hT : lpNorm p (x + y + z) < 3643/10000)
    (hx1 : lpNorm p x - 12 / (5 * p) < x 1)
    (hx2 : lpNorm p x - 12 / (5 * p) < x 2)
    (hy0 : lpNorm p y - 12 / (5 * p) < y 0)
    (hy2 : lpNorm p y - 12 / (5 * p) < y 2)
    (hz0 : lpNorm p z - 12 / (5 * p) < z 0)
    (hz1 : lpNorm p z - 12 / (5 * p) < z 1) :
    ∀ j i, |3 * (![x,y,z] : Triple) j i - cyclicCenter j i| ≤ (9 / 20 : ℝ) := by
  have hp1 : 1 ≤ p := by linarith
  have hE : 12 / (5 * p) ≤ (6/155 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hxi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 x i)
  have hyi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 y i)
  have hzi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 z i)
  have ht (i : Fin 3) : x i + y i + z i < 3643/10000 :=
    ((le_abs_self (x i + y i + z i)).trans
      (norm_apply_le_lpNorm hp1 (x + y + z) i)).trans_lt hT
  intro j i
  fin_cases j <;> fin_cases i <;>
    norm_num [cyclicCenter, Pi.smul_apply, smul_eq_mul, abs_le] <;>
    constructor <;> linarith! [hxi 0, hxi 1, hxi 2, hyi 0, hyi 1, hyi 2,
      hzi 0, hzi 1, hzi 2, ht 0, ht 1, ht 2]



theorem codex62_exists_failure_in_asymmetricBox {p : ℝ} (hp : 62 ≤ p)
    (hlinear : (23 / 50 : ℝ) * p < cyclicConstant p)
    (henvelope : scalarEnvelope p (3643/10000) < cyclicConstant p)
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    ∃ X ∈ asymmetricBox, tripleDeficit p (cyclicConstant p) X < 0 := by
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
  have hE : 12 / (5 * p) ≤ (6/155 : ℝ) := by
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
  have hcoarse : ∀ j i, |3 * (![u,v,w] : Triple) j i - cyclicCenter j i| ≤ (9 / 20 : ℝ) := by
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
  have hgapOriented : pairGapSum (lpNorm p) u v w < 3 / (2 * p) := by
    dsimp [u,v,w]
    simpa only [pairGapSum, pairGap, ← orient_add, lpNorm_orient p e signs _ hsigns] using hgapTotal
  refine ⟨![(3 : ℝ) • u, (3 : ℝ) • v, (3 : ℝ) • w], ?_, ?_⟩
  · apply codex62_bootstrap hp u v w
    · rwa [hu,hv,hw]
    · rw [hu]; exact hx.2.le
    · rw [hv]; exact hy.2.le
    · rw [hw]; exact hz.2.le
    · rw [hsumNorm]; exact hT.le
    · exact hgapOriented
    · exact hcoarse
  · change hlawkaDeficit p (cyclicConstant p) ((3 : ℝ) • u) ((3 : ℝ) • v) ((3 : ℝ) • w) < 0
    rw [hlawkaDeficit_smul hp0]
    have hfail : hlawkaDeficit p (cyclicConstant p) u v w < 0 := by
      dsimp [u, v, w]
      rwa [hlawkaDeficit_orient p (cyclicConstant p) e signs x y z hsigns]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    linarith

end HlawkaCodex62Localization

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution : ∀ p : ℝ, 62 ≤ p →
    (23 / 50 : ℝ) * p < cyclicConstant p →
    scalarEnvelope p (3643 / 10000) < cyclicConstant p →
    ∀ x y z : Fin 3 → ℝ,
      hlawkaDeficit p (cyclicConstant p) x y z < 0 →
        ∃ X ∈ ({X : Triple | ∀ j i,
          if j = i then -(10929 / 10000 : ℝ) ≤ X j i ∧ X j i ≤ -(28719 / 38750 : ℝ)
          else (28719 / 38750 : ℝ) ≤ X j i ∧ X j i ≤ (10929 / 10000 : ℝ)} : Set Triple),
          tripleDeficit p (cyclicConstant p) X < 0 := by
  intro p hp hlin henv x y z hf
  simpa [HlawkaCodex62Geometry.asymmetricBox, HlawkaCodex62Geometry.entryMin,
      HlawkaCodex62Geometry.entryMax] using
    HlawkaCodex62Localization.codex62_exists_failure_in_asymmetricBox hp hlin henv x y z hf
