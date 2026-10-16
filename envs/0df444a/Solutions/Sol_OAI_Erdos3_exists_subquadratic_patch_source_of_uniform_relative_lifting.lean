-- Prove2me | solution 1 for OAI.Erdos3.exists_subquadratic_patch_source_of_uniform_relative_lifting
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T05:26:51.432419+00:00
-- url     : https://prove2.me/submissions/e6bd1387-80d6-496c-88ae-692f98ad5611
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1323
import Definitions.Def_OAIErdos3B1331
import Definitions.Def_OAIErdos3B1342
import Definitions.Def_OAIErdos3B1380
import Theorems.Thm_OAI_Erdos3_RelativePatchSliceConclusion_mono
import Theorems.Thm_OAI_Erdos3_RepresentativeWindow_crtPatch_value_residues
import Theorems.Thm_OAI_Erdos3_distinct_prime_moduli_coprime
import Theorems.Thm_OAI_Erdos3_exists_crt_counting_contradiction
import Theorems.Thm_OAI_Erdos3_exists_polynomial_scored_crt_representative_patch
import Theorems.Thm_OAI_Erdos3_exists_scored_windowed_crt_patch
import Theorems.Thm_OAI_Erdos3_subquadratic_patch_source_of_relative_family

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AbsoluteIncrementBudgets
namespace OAI

section

namespace Erdos3

theorem absolute_normalization_budget (C : ℕ) {p alpha : ℝ} (hp : 2 ≤ p)
    (halpha : 0 < alpha) (hlower : Real.exp (-p) ≤ alpha) :
    (p + 2) ^ C ≤ (p + 2) ^ (C + 1) ∧
      Real.exp (-((p + 2) ^ (C + 1))) / alpha ≤ Real.exp (-((p + 2) ^ C)) := by
  have hb : 1 ≤ p + 2 := by linarith
  have hpow : 1 ≤ (p + 2) ^ C := one_le_pow₀ hb
  have hs : (p + 2) ^ C + p ≤ (p + 2) ^ (C + 1) := by
    rw [pow_succ]
    nlinarith [mul_nonneg (by linarith : 0 ≤ p + 1) (sub_nonneg.mpr hpow)]
  refine ⟨by linarith, (div_le_iff₀ halpha).mpr ?_⟩
  calc
    _ ≤ Real.exp (-((p + 2) ^ C) - p) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-((p + 2) ^ C)) * Real.exp (-p) := by rw [sub_eq_add_neg, Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_left hlower (Real.exp_pos _).le

theorem exists_absolute_side_budget (Csc k : ℕ) (hk : 0 < k) {xi : ℝ} (hxi : 0 < xi) :
    ∃ C : ℕ, 2 ≤ C ∧ Csc < C ∧ ∀ p : ℝ, 2 ≤ p →
      (p + 2) ^ Csc ≤ (p + 2) ^ C ∧
      (64 * (k : ℝ)) ≤ Real.exp ((p + 2) ^ C) ∧
      100 * (1 + xi) * Real.exp ((p + 2) ^ Csc) ≤ Real.exp ((p + 2) ^ C) := by
  obtain ⟨ell, hell⟩ := exists_nat_ge (Real.log (64 * (k : ℝ)))
  obtain ⟨b, hb⟩ := exists_nat_ge (Real.log (100 * (1 + xi)))
  obtain ⟨D, hD, hbound⟩ := exists_natPolynomial_fixed_power_budget
    ((Polynomial.X + 2) ^ Csc + Polynomial.C ell + Polynomial.C b)
  let C := max D (Csc + 1)
  refine ⟨C, hD.trans (le_max_left _ _), by dsimp [C]; omega, ?_⟩
  intro p hp
  have hp0 : 0 ≤ p := by linarith
  have hbase : 1 ≤ p + 2 := by linarith
  have hpoly : (p + 2) ^ Csc + ell + b ≤ (p + 2) ^ D := by
    simpa [Polynomial.eval₂_pow] using hbound p hp0
  have hDC : (p + 2) ^ D ≤ (p + 2) ^ C := pow_le_pow_right₀ hbase (le_max_left _ _)
  have hsum := hpoly.trans hDC
  have hell0 : (0 : ℝ) ≤ ell := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hpow0 : 0 ≤ (p + 2) ^ Csc := pow_nonneg (by linarith) _
  have hside : Real.log (64 * (k : ℝ)) ≤ (p + 2) ^ C := by linarith
  have hscore : Real.log (100 * (1 + xi)) + (p + 2) ^ Csc ≤ (p + 2) ^ C := by linarith
  refine ⟨by linarith, ?_, ?_⟩
  · calc
      _ = Real.exp (Real.log (64 * (k : ℝ))) := (Real.exp_log (by positivity)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hside
  · calc
      _ = Real.exp (Real.log (100 * (1 + xi)) + (p + 2) ^ Csc) := by
        rw [Real.exp_add, Real.exp_log (by positivity)]
      _ ≤ _ := Real.exp_le_exp.mpr hscore

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AmplificationFinalCostGrowth
namespace OAI

section

open Filter

namespace Erdos3

theorem amplificationResource_ge_two {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K) (j : ℕ) :
    2 ≤ amplificationResource p D K j := by
  induction j with
  | zero =>
    change 2 ≤ (2 + p) ^ D
    have h := pow_le_pow_right₀ (show 1 ≤ 2 + p by linarith) hD
    simp only [pow_one] at h
    linarith
  | succ j ih =>
    change 2 ≤ (2 + amplificationResource p D K j) ^ K
    have h := pow_le_pow_right₀ (show 1 ≤ 2 + amplificationResource p D K j by linarith) hK
    simp only [pow_one] at h
    linarith

theorem amplificationResource_room {x : ℝ} (hx : 0 ≤ x) (E : ℕ) :
    x + (2 + x) ^ E ≤ (2 + x) ^ (E + 1) := by
  have hp : 1 ≤ (2 + x) ^ E := one_le_pow₀ (by linarith)
  rw [pow_succ]
  nlinarith

end Erdos3

end

section

namespace Erdos3

theorem levelCoefficient_pos {K : ℝ} (hK : 1 < K) : 0 < levelCoefficient K := by
  unfold levelCoefficient
  exact one_div_pos.mpr (mul_pos (by norm_num) (Real.log_pos hK))

end Erdos3

end

section

namespace Erdos3

theorem amplificationResource_add_two_le_succ {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K) (j : ℕ) :
    amplificationResource p D K j + 2 ≤ amplificationResource p D K (j + 1) := by
  have hj := amplificationResource_ge_two hp hD hK j
  have hpow := pow_le_pow_right₀
    (show 1 ≤ 2 + amplificationResource p D K j by linarith) hK
  simpa only [pow_one, amplificationResource, add_comm] using hpow

theorem amplificationResource_strictMono {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K) :
    StrictMono (amplificationResource p D K) := by
  apply strictMono_nat_of_lt_succ
  intro j
  have h := amplificationResource_add_two_le_succ hp hD hK j
  linarith

theorem amplificationResource_monotone {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K) :
    Monotone (amplificationResource p D K) :=
  (amplificationResource_strictMono hp hD hK).monotone

theorem amplificationResource_zero_le {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K) (j : ℕ) :
    amplificationResource p D K 0 ≤ amplificationResource p D K j :=
  amplificationResource_monotone hp hD hK (Nat.zero_le j)

theorem amplificationResource_parameter_le_zero {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) : p ≤ amplificationResource p D K 0 := by
  have hpow := pow_le_pow_right₀ (show 1 ≤ 2 + p by linarith) hD
  simp only [pow_one] at hpow
  change p ≤ (2 + p) ^ D
  linarith

theorem amplificationResource_parameter_le {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K) (j : ℕ) :
    p ≤ amplificationResource p D K j :=
  (amplificationResource_parameter_le_zero hp hD).trans
    (amplificationResource_zero_le hp hD hK j)

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.LowDensityAmplification
namespace OAI

section

namespace Erdos3

open Filter

theorem LowDensityThreshold.raw_target_lt_one {H a : ℝ}
    (h : LowDensityThreshold H a) (hH : 1 < H) : H * a < 1 := by
  have hHa : 0 < H * a := mul_pos (by linarith) h.1
  have hstrict := mul_lt_mul_of_pos_right hH hHa
  nlinarith [h.2]

theorem LowDensityThreshold.mul_of_next {κ H a : ℝ}
    (h : LowDensityThreshold (κ * H ^ 2) a) (hH : 1 < H) (hκH : 1 ≤ κ ^ 2 * H) :
    LowDensityThreshold H (H * a) := by
  refine ⟨mul_pos (by linarith) h.1, ?_⟩
  have hscale := mul_le_mul_of_nonneg_right hκH
    (mul_nonneg (pow_nonneg (by linarith : 0 ≤ H) 3) h.1.le)
  have hid : (κ ^ 2 * H) * (H ^ 3 * a) = (κ * H ^ 2) ^ 2 * a := by ring
  rw [hid] at hscale
  have hlast := hscale.trans h.2
  nlinarith

theorem LowDensityThreshold.of_next {κ H a : ℝ}
    (h : LowDensityThreshold (κ * H ^ 2) a) (hH : 1 < H) (hκH : 1 ≤ κ ^ 2 * H) :
    LowDensityThreshold H a ∧ a ≤ H * a := by
  have hmul := h.mul_of_next hH hκH
  have hmono : a ≤ H * a := by nlinarith [h.1]
  exact ⟨⟨h.1, (mul_le_mul_of_nonneg_left hmono (sq_nonneg H)).trans hmul.2⟩, hmono⟩

theorem amplificationGain_low_density_parameters {κ H₀ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hH : 1 < H₀) (hκH : 1 ≤ κ ^ 2 * H₀) (j : ℕ) :
    1 < amplificationGain κ H₀ j ∧ 1 ≤ κ ^ 2 * amplificationGain κ H₀ j := by
  induction j with
  | zero => exact ⟨hH, hκH⟩
  | succ j ih =>
    let H := amplificationGain κ H₀ j
    have hH0 : 0 < H := by dsimp only [H]; linarith [ih.1]
    have hkk : κ ^ 2 < κ := by nlinarith
    have hκH' : 1 < κ * H :=
      ih.2.trans_lt (mul_lt_mul_of_pos_right hkk hH0)
    have hgrow : H < κ * H ^ 2 := by
      have h := mul_lt_mul_of_pos_right hκH' hH0
      nlinarith
    constructor
    · exact ih.1.trans hgrow
    · exact ih.2.trans (mul_le_mul_of_nonneg_left hgrow.le (sq_nonneg κ))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchAmplification
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem RelativePatchAbsoluteRule.mono {s n₀ d₀ : ℕ} {p p' a Λ : ℝ}
    (h : RelativePatchAbsoluteRule s n₀ p a Λ d₀) (hpp : p ≤ p') :
    RelativePatchAbsoluteRule s n₀ p' a Λ d₀ := by
  intro N hprime hinj hratio hsize f hf hfree hmean
  exact (h N hprime hinj hratio
    (fun i => (Real.exp_le_exp.mpr hpp).trans (hsize i)) f hf hfree hmean).mono le_rfl hpp

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

namespace ResidueBoxSlice


end ResidueBoxSlice

namespace VectorPolynomial

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice


end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace ResidueBoxSlice

variable {X : Type*} {N : X → ℕ} {q : ℕ}

theorem integerAffine_mem_integerBox [Fintype X] [DecidableEq X]
    (S : ResidueBoxSlice N q) {x : X → ℤ} (hx : x ∈ integerBox S.length) :
    S.integerAffine x ∈ integerBox N := by
  have hx' := (mem_integerBox S.length x).mp hx
  apply (mem_integerBox N _).mpr
  intro i
  have hnat : (x i).toNat < S.length i := by
    have := hx' i
    omega
  have hin := S.inside i (x i).toNat hnat
  have hcast : (S.start i : ℤ) + (q : ℤ) * ((x i).toNat : ℤ) < (N i : ℤ) := by
    exact_mod_cast hin
  rw [Int.toNat_of_nonneg (hx' i).1] at hcast
  exact ⟨add_nonneg (Int.natCast_nonneg _) (mul_nonneg (Int.natCast_nonneg _) (hx' i).1),
    hcast⟩

theorem pullback_mem_Icc [Fintype X] [DecidableEq X]
    (S : ResidueBoxSlice N q) {f : (X → ℤ) → ℝ}
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ x ∈ integerBox S.length, S.integerPullback f x ∈ Set.Icc (0 : ℝ) 1 := by
  intro x hx
  exact hf _ (S.integerAffine_mem_integerBox hx)

theorem pullback_apFree [Fintype X] [DecidableEq X]
    (S : ResidueBoxSlice N q) (hq : 0 < q) {f : (X → ℤ) → ℝ} {k : ℕ}
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} k) :
    IntegerVectorAPFree
      {x | x ∈ integerBox S.length ∧ S.integerPullback f x ≠ 0} k := by
  intro a d hd
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have hstep : (fun j => (q : ℤ) * d j) ≠ 0 := by
    intro he
    apply hd
    funext j
    exact (mul_eq_zero.mp (congrFun he j)).resolve_left hq0
  obtain ⟨i, hi⟩ := hfree (S.integerAffine a) (fun j => (q : ℤ) * d j) hstep
  refine ⟨i, ?_⟩
  rintro ⟨hx, hf⟩
  apply hi
  have he : S.integerAffine a + (i.val : ℤ) • (fun j => (q : ℤ) * d j) =
      S.integerAffine (a + (i.val : ℤ) • d) := by
    funext j
    simp only [integerAffine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he]
  exact ⟨S.integerAffine_mem_integerBox hx, hf⟩

end ResidueBoxSlice

theorem relativePatchBoxScore_pullback {X : Type*} [Fintype X] [DecidableEq X]
    {s d q : ℕ} {N : X → ℕ} (S : ResidueBoxSlice N q)
    (f : (X → ℤ) → ℝ) (a : ℝ) (A : PolynomialPatch X s d) :
    relativePatchBoxScore S.length (S.integerPullback f) a A =
      relativePatchSliceScore S f a A := by
  classical
  symm
  unfold relativePatchSliceScore relativePatchBoxScore
  apply Finset.expect_bij (fun t _ i => ((t i).val : ℤ))
  · intro t _
    exact (mem_integerBox S.length _).mpr (fun i =>
      ⟨Int.natCast_nonneg _, by exact_mod_cast (t i).isLt⟩)
  · intro t _
    simp only [ResidueBoxSlice.integerPullback, ResidueBoxSlice.integerAffine_finPoint,
      Int.cast_natCast]
  · intro t _ u _ h
    funext i
    apply Fin.ext
    exact_mod_cast congrFun h i
  · intro x hx
    have hx' := (mem_integerBox S.length x).mp hx
    refine ⟨fun i => ⟨(x i).toNat, by have := hx' i; omega⟩, by simp only [Finset.mem_univ], ?_⟩
    funext i
    exact Int.toNat_of_nonneg (hx' i).1

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem relativePatchDistinctWeights_le_degree {X : Type*} {s d : ℕ}
    (A : PolynomialPatch X s d) : relativePatchDistinctWeights A ≤ s := by
  have hsub : Finset.univ.image A.weight ⊆ Finset.Icc 1 s := by
    intro w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_Icc.mpr ⟨A.weight_pos i, A.weight_le i⟩
  have h := Finset.card_le_card hsub
  simpa only [relativePatchDistinctWeights, Nat.card_Icc, Nat.add_sub_cancel] using h

theorem RelativePatchPowerInductionRule.amplify
    {s n₀ E D : ℕ} [NeZero n₀] {τ x H a : ℝ}
    (hrelative : RelativePatchPowerInductionRule s n₀ s τ E)
    (hx : 2 ≤ x) (hn : (n₀ : ℝ) ≤ x) (hH : 1 ≤ H)
    (ha : Real.exp (-x) ≤ a) (hraw : H * (H * a) ≤ 1)
    (hfirst : RelativePatchAbsoluteRule s n₀ x a (H * a) D)
    (hsecond : RelativePatchAbsoluteRule s n₀ x (H * a) (H * (H * a)) D) :
    RelativePatchAbsoluteRule s n₀ (x + (x + 2) ^ E) a
      (((1 - τ) ^ (s + 1) * H ^ 2) * a) ((s + 1) * D) := by
  intro N hprime hinj hratio hsize f hf hfree hmean
  have hx0 : 0 ≤ x := by linarith
  have hcost : 0 ≤ (x + 2) ^ E := pow_nonneg (by linarith) _
  obtain ⟨q, hq, S, d, A, hlength, hd, hcomplexity, hscore⟩ :=
    hfirst N hprime hinj hratio
      (fun i => (Real.exp_le_exp.mpr (le_add_of_nonneg_right hcost)).trans (hsize i))
      f hf hfree hmean
  have hlength' : ∀ i, Real.exp ((x + 2) ^ E) ≤ (S.length i : ℝ) := by
    intro i
    calc
      Real.exp ((x + 2) ^ E) = Real.exp (-x) * Real.exp (x + (x + 2) ^ E) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-x) * (N i : ℝ) :=
        mul_le_mul_of_nonneg_left (hsize i) (Real.exp_pos _).le
      _ ≤ (S.length i : ℝ) := hlength i
  have ha0 : 0 ≤ a := (Real.exp_pos _).le.trans ha
  have hab : a ≤ H * a := by nlinarith
  have hbb : H * a ≤ H * (H * a) := by
    exact mul_le_mul_of_nonneg_left hab (by linarith)
  have hnew := hrelative x (H * a) (H * (H * a)) D hx (ha.trans hab) hbb hraw
    hsecond (Fin n₀) (by simpa using hn) S.length hlength'
    (S.integerPullback f) (S.pullback_mem_Icc hf) (S.pullback_apFree hq hfree)
    d A hcomplexity (relativePatchDistinctWeights_le_degree A)
    (by rw [relativePatchBoxScore_pullback]; exact hscore)
  have hcomposed := hnew.comp S hq hx0 hlength
  have hrank : D + s * d ≤ (s + 1) * D := by nlinarith
  convert hcomposed.mono hrank le_rfl using 1
  ring

theorem LowDensityRelativeAbsoluteRule.amplify
    {s n₀ E D : ℕ} [NeZero n₀] {τ p x H : ℝ}
    (hrelative : RelativePatchPowerInductionRule s n₀ s τ E)
    (hprevious : LowDensityRelativeAbsoluteRule s n₀ p H D x)
    (hx : 2 ≤ x) (hn : (n₀ : ℝ) ≤ x) (hpx : p ≤ x) (hH : 1 < H)
    (hdiscount : 1 ≤ ((1 - τ) ^ (s + 1)) ^ 2 * H) :
    LowDensityRelativeAbsoluteRule s n₀ p ((1 - τ) ^ (s + 1) * H ^ 2)
      ((s + 1) * D) (x + (x + 2) ^ E) := by
  intro a ha hlow
  obtain ⟨hlow₁, hab⟩ := hlow.of_next hH hdiscount
  have hlow₂ := hlow.mul_of_next hH hdiscount
  exact hrelative.amplify hx hn hH.le
    ((Real.exp_le_exp.mpr (neg_le_neg hpx)).trans ha)
    (hlow₂.raw_target_lt_one hH).le
    (hprevious a ha hlow₁) (hprevious (H * a) (ha.trans hab) hlow₂)

theorem LowDensityRelativeAbsoluteRule.amplify_power
    {s n₀ E D : ℕ} [NeZero n₀] {τ p x H : ℝ}
    (hrelative : RelativePatchPowerInductionRule s n₀ s τ E)
    (hprevious : LowDensityRelativeAbsoluteRule s n₀ p H D x)
    (hx : 2 ≤ x) (hn : (n₀ : ℝ) ≤ x) (hpx : p ≤ x) (hH : 1 < H)
    (hdiscount : 1 ≤ ((1 - τ) ^ (s + 1)) ^ 2 * H) :
    LowDensityRelativeAbsoluteRule s n₀ p ((1 - τ) ^ (s + 1) * H ^ 2)
      ((s + 1) * D) ((2 + x) ^ (E + 1)) := by
  intro a ha hlow
  exact ((LowDensityRelativeAbsoluteRule.amplify hrelative hprevious hx hn hpx hH hdiscount) a ha hlow).mono
    (by simpa only [add_comm x 2] using amplificationResource_room (by linarith : 0 ≤ x) E)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AxisCompression
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

end Erdos3

end

section

universe u

namespace Erdos3

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

end Erdos3

end

section

namespace Erdos3.PositiveShiftBasis

universe u

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

universe u

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

universe u

theorem CyclicNiltestUpperComparison.mono_budget
    {degree N : ℕ} [NeZero N] {P Q epsilon delta : ℝ} {f g : ZMod N → ℝ}
    (h : CyclicNiltestUpperComparison.{u} degree N Q epsilon f g)
    (hPQ : P ≤ Q) (hdelta : epsilon ≤ delta) :
    CyclicNiltestUpperComparison.{u} degree N P delta f g := by
  intro L _ _ s dim _ _ _ _ D hs T hT hcomp
  exact (h D hs T hT (hcomp.mono hPQ)).trans hdelta

namespace PositiveShiftBasis

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

end PositiveShiftBasis
end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DensityNormalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem density_lower_bound_of_log_inverse {alpha p : ℝ} (halpha : 0 < alpha)
    (hlog : Real.log (1 / alpha) ≤ p) : Real.exp (-p) ≤ alpha := by
  have he : Real.log alpha ≥ -p := by
    rw [Real.log_div (by norm_num) halpha.ne', Real.log_one, zero_sub] at hlog
    linarith
  calc
    _ ≤ Real.exp (Real.log alpha) := Real.exp_le_exp.mpr he
    _ = alpha := Real.exp_log halpha

theorem normalized_density_bounds {X : Type*} (f : X → ℝ) {alpha p : ℝ}
    (halpha : 0 < alpha) (hlower : Real.exp (-p) ≤ alpha)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (x : X) :
    0 ≤ f x / alpha ∧ f x / alpha ≤ Real.exp p := by
  refine ⟨div_nonneg (hf x).1 halpha.le, ?_⟩
  apply (div_le_iff₀ halpha).mpr
  calc
    f x ≤ 1 := (hf x).2
    _ = Real.exp p * Real.exp (-p) := by rw [← Real.exp_add]; simp
    _ ≤ Real.exp p * alpha := mul_le_mul_of_nonneg_left hlower (Real.exp_pos p).le

theorem normalized_density_mean {X : Type*} [Fintype X] (f : X → ℝ) {alpha : ℝ}
    (halpha : 0 < alpha) (hmean : (𝔼 x, f x) = alpha) :
    (𝔼 x, f x / alpha) = 1 := by
  rw [← Finset.expect_div, hmean, div_self halpha.ne']

theorem support_normalized_density {X : Type*} (f : X → ℝ) {alpha : ℝ}
    (halpha : alpha ≠ 0) : Function.support (fun x => f x / alpha) = Function.support f := by
  ext x
  simp [Function.mem_support, halpha]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PositiveScoreComparison
namespace OAI

section

universe u

namespace Erdos3

open scoped BigOperators TensorProduct

theorem CyclicNiltestUpperComparison.of_positive_scores {degree N : ℕ} [NeZero N]
    {P epsilon : ℝ} {f g : ZMod N → ℝ}
    (h : ∀ T : ZMod N → ℝ, PositiveCyclicNiltest.{u} degree N P T →
      (𝔼 x, (f x - g x) * T x) ≤ epsilon) :
    CyclicNiltestUpperComparison.{u} degree N P epsilon f g := by
  intro L _ _ s dim _ _ _ _ D hs T hT hTc
  exact h (fun x => (T.evalCyclic N (fun _ => x)).re)
    (.of_test D hs T hT hTc (fun _ => rfl))

theorem exists_positive_score_of_not_upperComparison {degree N : ℕ} [NeZero N]
    {P epsilon : ℝ} {f g : ZMod N → ℝ}
    (h : ¬ CyclicNiltestUpperComparison.{u} degree N P epsilon f g) :
    ∃ T : ZMod N → ℝ, PositiveCyclicNiltest.{u} degree N P T ∧
      epsilon < 𝔼 x, (f x - g x) * T x := by
  by_contra hnone
  apply h
  apply CyclicNiltestUpperComparison.of_positive_scores
  intro T hT
  by_contra he
  exact hnone ⟨T, hT, lt_of_not_ge he⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AbsoluteCRTWindow
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem prime_product_unit_of_lt {J : Type*} [Fintype J] (N : J → ℕ)
    (hprime : ∀ j, (N j).Prime) {a : ℕ} (ha : 0 < a) (hlt : ∀ j, a < N j) :
    IsUnit (a : ZMod (∏ j, N j)) := by
  apply (ZMod.isUnit_iff_coprime a _).mpr
  apply Nat.coprime_fintype_prod_right_iff.mpr
  intro j
  exact ((hprime j).coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ha (hlt j))).symm

theorem modulus_le_product {J : Type*} [Fintype J] (N : J → ℕ)
    (hpos : ∀ j, 0 < N j) (j : J) : N j ≤ ∏ i, N i :=
  Finset.single_le_prod' (fun i _ => hpos i) (Finset.mem_univ j)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_absolute_crt_score {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ Csc : ℕ, 2 ≤ Csc ∧ ∃ C : ℕ, 2 ≤ C ∧ Csc < C ∧ ∃ xi : ℝ, 0 < xi ∧
    ∀ (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)]
      (hprime : ∀ j, (N j).Prime) (hinj : Function.Injective N)
      (f : ((j : J) → ZMod (N j)) → ℝ) {alpha p : ℝ},
      0 < alpha → 2 ≤ p → Real.log (1 / alpha) ≤ p →
      (∀ j, Real.exp ((p + 2) ^ C) ≤ N j) →
      (∀ u, 0 ≤ f u ∧ f u ≤ 1) → (𝔼 u, f u) = alpha →
      IntegerVectorAPFree (residueBoxIntegerPoint N '' Function.support f) k →
      let hN := distinct_prime_moduli_coprime N hprime hinj
      ∃ T : ZMod (∏ j, N j) → ℝ,
        PositiveCyclicNiltest.{0} (k - 2) (∏ j, N j) ((p + 2) ^ Csc) T ∧
        Real.exp (-((p + 2) ^ Csc)) ≤
          (𝔼 x, (f (ZMod.prodEquivPi N hN x) - (1 + xi) * alpha) * T x) ∧
        ((∏ j, N j : ℕ) : ℝ)⁻¹ ≤
          (𝔼 x, (f (ZMod.prodEquivPi N hN x) - (1 + xi) * alpha) * T x) /
            (100 * (1 + xi)) := by
  classical
  obtain ⟨C0, hC0, xi, hxi, hcontra⟩ := exists_crt_counting_contradiction (J := J) k hk
  let Csc := C0 + 1
  obtain ⟨C, hC, hstrict, hbudget⟩ := exists_absolute_side_budget Csc k (by omega) hxi
  refine ⟨Csc, by dsimp [Csc]; omega, C, hC, hstrict, xi, hxi, ?_⟩
  intro N _ _ hprime hinj f alpha p halpha hp hlog hsize hf hmean hfree
  let hN := distinct_prime_moduli_coprime N hprime hinj
  let original : ZMod (∏ j, N j) → ℝ := fun x => f (ZMod.prodEquivPi N hN x)
  let normalized : ((j : J) → ZMod (N j)) → ℝ := fun u => f u / alpha
  have hlower := density_lower_bound_of_log_inverse halpha hlog
  have hnumb := absolute_normalization_budget C0 hp halpha hlower
  have hb := hbudget p hp
  have hside (j) : 64 * k ≤ N j := by exact_mod_cast hb.2.1.trans (hsize j)
  let j0 : J := Classical.choice inferInstance
  have hprod : (N j0 : ℝ) ≤ (∏ j, N j : ℕ) := by
    exact_mod_cast modulus_le_product N (fun j => (hprime j).pos) j0
  have hlarge : Real.exp ((p + 2) ^ C0) ≤ (∏ j, N j : ℕ) :=
    (Real.exp_le_exp.mpr (hnumb.1.trans hb.1)).trans ((hsize j0).trans hprod)
  have hunit (a : ℕ) (ha : 1 ≤ a) (hak : a < k) : IsUnit (a : ZMod (∏ j, N j)) := by
    apply prime_product_unit_of_lt N hprime ha
    intro j
    have hj := hside j
    omega
  have hodd : Odd (∏ j, N j) := Nat.coprime_two_left.mp
    ((ZMod.isUnit_iff_coprime 2 _).mp (hunit 2 (by omega) (by omega)))
  have horiginal : (𝔼 x, original x) = alpha := by
    calc
      _ = 𝔼 u, f u := Fintype.expect_equiv (ZMod.prodEquivPi N hN).toEquiv _ _ (fun _ => rfl)
      _ = alpha := hmean
  have hnormalized : (𝔼 x : ZMod (∏ j, N j), normalized (ZMod.prodEquivPi N hN x)) = 1 :=
    normalized_density_mean original halpha horiginal
  have hnormfree : IntegerVectorAPFree (residueBoxIntegerPoint N '' Function.support normalized) k := by
    dsimp only [normalized]
    rw [support_normalized_density f halpha.ne']
    exact hfree
  have hnot := hcontra N hN hp hodd hlarge hside hunit normalized
    (normalized_density_bounds f halpha hlower hf) hnormalized hnormfree
  have hnotScore : ¬ CyclicNiltestUpperComparison.{0} (k - 2) (∏ j, N j)
      ((p + 2) ^ Csc) (Real.exp (-((p + 2) ^ Csc))) original (fun _ => (1 + xi) * alpha) := by
    intro hcomp
    have hn : CyclicNiltestUpperComparison.{0} (k - 2) (∏ j, N j)
        ((p + 2) ^ Csc) (Real.exp (-((p + 2) ^ Csc)) / alpha)
        (fun x => original x / alpha) (fun _ => 1 + xi) :=
      CyclicNiltestUpperComparison.normalize hcomp halpha
    exact hnot (CyclicNiltestUpperComparison.mono_budget hn hnumb.1 hnumb.2)
  obtain ⟨T, hT, hscore⟩ := exists_positive_score_of_not_upperComparison hnotScore
  refine ⟨T, hT, hscore.le, ?_⟩
  have hbig : 100 * (1 + xi) * Real.exp ((p + 2) ^ Csc) ≤ (∏ j, N j : ℕ) :=
    hb.2.2.trans ((hsize j0).trans hprod)
  have hM : 0 < 100 * (1 + xi) := by positivity
  calc
    _ = 1 / ((∏ j, N j : ℕ) : ℝ) := (one_div _).symm
    _ ≤ 1 / (100 * (1 + xi) * Real.exp ((p + 2) ^ Csc)) :=
      one_div_le_one_div_of_le (mul_pos hM (Real.exp_pos _)) hbig
    _ = Real.exp (-((p + 2) ^ Csc)) / (100 * (1 + xi)) := by
      simp [Real.exp_neg, div_eq_mul_inv, mul_comm]
    _ ≤ _ := div_le_div_of_nonneg_right hscore.le hM.le

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem density_test_score_abs_le {f T alpha xi : ℝ}
    (hf : 0 ≤ f ∧ f ≤ 1) (hT : 0 ≤ T ∧ T ≤ 1)
    (halpha : 0 ≤ alpha ∧ alpha ≤ 1) (hxi : 0 ≤ xi) :
    |(f - (1 + xi) * alpha) * T| ≤ 1 + xi := by
  have hM : 0 ≤ 1 + xi := by positivity
  have hc0 := mul_nonneg hM halpha.1
  have hc1 : (1 + xi) * alpha ≤ 1 + xi :=
    mul_le_of_le_one_right hM halpha.2
  have hdiff : |f - (1 + xi) * alpha| ≤ 1 + xi := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [abs_mul, abs_of_nonneg hT.1]
  exact (mul_le_mul_of_nonneg_right hdiff hT.1).trans (mul_le_of_le_one_right hM hT.2)

theorem exists_absolute_crt_window {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ Csc : ℕ, 2 ≤ Csc ∧ ∃ C : ℕ, 2 ≤ C ∧ Csc < C ∧
      ∃ Cwindow : ℕ, 2 ≤ Cwindow ∧ ∃ xi : ℝ, 0 < xi ∧
      ∀ (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)]
        (hprime : ∀ j, (N j).Prime) (hinj : Function.Injective N)
        (f : ((j : J) → ZMod (N j)) → ℝ) {alpha p : ℝ},
        0 < alpha → 2 ≤ p → Real.log (1 / alpha) ≤ p →
        (∀ j, Real.exp ((p + 2) ^ C) ≤ N j) →
        (∀ u, 0 ≤ f u ∧ f u ≤ 1) → (𝔼 u, f u) = alpha →
        IntegerVectorAPFree (residueBoxIntegerPoint N '' Function.support f) k →
        let hN := distinct_prime_moduli_coprime N hprime hinj
        ∃ (T : ZMod (∏ j, N j) → ℝ) (w : RepresentativeWindow),
          PositiveCyclicNiltest.{0} (k - 2) (∏ j, N j) ((p + 2) ^ Csc) T ∧
          Real.log (2 + (w.lip : ℝ)) ≤ (p + 2) ^ Cwindow ∧
          Real.exp (-((p + 2) ^ Cwindow)) ≤
            𝔼 u : (j : J) → ZMod (N j),
              ((f u - (1 + xi) * alpha) * T ((ZMod.prodEquivPi N hN).symm u)) *
                (w.crtPatch N hN (k - 2) (by omega)).value (fun j => ((u j).val : ℝ)) := by
  obtain ⟨Csc, hCsc, C, hC, hstrict, xi, hxi, habsolute⟩ :=
    exists_absolute_crt_score (J := J) k hk
  obtain ⟨D, hD, hwindow⟩ := exists_polynomial_scored_crt_representative_patch
  obtain ⟨a, ha⟩ := exists_nat_ge (Real.log (1 + xi))
  obtain ⟨Cwindow, hCwindow, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    (((Polynomial.X + 2) ^ Csc + Polynomial.C a + 2) ^ D)
  refine ⟨Csc, hCsc, C, hC, hstrict, Cwindow, hCwindow, xi, hxi, ?_⟩
  intro N _ _ hprime hinj f alpha p halpha hp hlog hsize hf hmean hfree
  let hN := distinct_prime_moduli_coprime N hprime hinj
  obtain ⟨T, hT, hscore, hmod⟩ := habsolute N hprime hinj f halpha hp hlog hsize hf hmean hfree
  let F : ZMod (∏ j, N j) → ℝ :=
    fun x => (f (ZMod.prodEquivPi N hN x) - (1 + xi) * alpha) * T x
  let sigma : ℝ := 𝔼 x, F x
  let q : ℝ := (p + 2) ^ Csc + a
  have hp0 : 0 ≤ p := by linarith
  have hpow0 : 0 ≤ (p + 2) ^ Csc := by positivity
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hq : 0 ≤ q := add_nonneg hpow0 ha0
  have hM : 0 < 1 + xi := by positivity
  have hMexp : 1 + xi ≤ Real.exp q := by
    apply (Real.log_le_iff_le_exp hM).mp
    exact ha.trans (by dsimp only [q]; linarith)
  have hsig : Real.exp (-q) ≤ sigma :=
    (Real.exp_le_exp.mpr (show -q ≤ -((p + 2) ^ Csc) by dsimp only [q]; linarith)).trans hscore
  have halpha1 : alpha ≤ 1 := by
    rw [← hmean]
    exact (Finset.expect_le_expect (fun u _ => (hf u).2)).trans_eq (Fintype.expect_const 1)
  have hcap (x : ZMod (∏ j, N j)) : |F x| ≤ 1 + xi :=
    density_test_score_abs_le (hf _) (hT.unit_interval x) ⟨halpha.le, halpha1⟩ hxi.le
  obtain ⟨w, hw, hws⟩ := hwindow N hN (k - 2) (by omega) F hq hM hMexp hsig
    hcap le_rfl (by simpa only [one_div] using hmod)
  have hb : (q + 2) ^ D ≤ (p + 2) ^ Cwindow := by
    simpa [Polynomial.eval₂_pow, q] using hbudget p hp0
  refine ⟨T, w, hT, hw.trans hb, ?_⟩
  have hs := (Real.exp_le_exp.mpr (neg_le_neg hb)).trans hws
  have he (u : (j : J) → ZMod (N j)) :
      F ((ZMod.prodEquivPi N hN).symm u) =
        (f u - (1 + xi) * alpha) * T ((ZMod.prodEquivPi N hN).symm u) := by
    dsimp only [F]
    rw [RingEquiv.apply_symm_apply]
  simpa only [he] using hs

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AbsoluteCRTPolynomialPatch
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_absolute_crt_patch {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
      ∀ (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)]
        (_hprime : ∀ j, (N j).Prime) (_hinj : Function.Injective N)
        (f : ((j : J) → ZMod (N j)) → ℝ) {alpha p : ℝ},
        0 < alpha → 2 ≤ p → Real.log (1 / alpha) ≤ p →
        (∀ j, Real.exp ((p + 2) ^ C) ≤ N j) →
        (∀ x, 0 ≤ f x ∧ f x ≤ 1) → (𝔼 x, f x) = alpha →
        IntegerVectorAPFree (residueBoxIntegerPoint N '' Function.support f) k →
        ∃ d : ℕ, ∃ P : PolynomialPatch J (k - 2) d,
          (d : ℝ) + Real.log (2 + (P.kernel.lip : ℝ)) ≤ (p + 2) ^ C ∧
          Real.exp (-((p + 2) ^ C)) ≤
            (𝔼 x, (f x - (1 + xi) * alpha) * P.value (fun j => ((x j).val : ℝ))) := by
  obtain ⟨Csc, _, Cside, hCside, _, Cwindow, _, xi, hxi, hwindow⟩ :=
    exists_absolute_crt_window (J := J) k hk
  obtain ⟨A, _, hconvert⟩ := exists_scored_windowed_crt_patch.{0} (k - 2) (by omega)
  obtain ⟨B, _, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    (((Polynomial.X + 2) ^ (max Csc Cwindow) + 2) ^ A)
  let C := max Cside B
  refine ⟨C, hCside.trans (le_max_left _ _), xi, hxi, ?_⟩
  intro N _ _ hprime hinj f alpha p halpha hp hlog hsize hf hmean hfree
  have hp0 : 0 ≤ p := by linarith
  have hbase : 1 ≤ p + 2 := by linarith
  have hside : (p + 2) ^ Cside ≤ (p + 2) ^ C :=
    pow_le_pow_right₀ hbase (le_max_left _ _)
  obtain ⟨T, w, hT, hw, hscore⟩ := hwindow N hprime hinj f halpha hp hlog
    (fun j => (Real.exp_le_exp.mpr hside).trans (hsize j)) hf hmean hfree
  let q := (p + 2) ^ (max Csc Cwindow)
  have hq : 0 ≤ q := pow_nonneg (by linarith) _
  have hsc : (p + 2) ^ Csc ≤ q := pow_le_pow_right₀ hbase (le_max_left _ _)
  have hwin : (p + 2) ^ Cwindow ≤ q := pow_le_pow_right₀ hbase (le_max_right _ _)
  let hN := distinct_prime_moduli_coprime N hprime hinj
  have hs : Real.exp (-q) ≤
      (𝔼 x, ((f x - (1 + xi) * alpha) * T ((ZMod.prodEquivPi N hN).symm x)) *
        w.value ((((ZMod.prodEquivPi N hN).symm x).val : ℝ) / (∏ j, N j : ℕ))) := by
    apply (Real.exp_le_exp.mpr (neg_le_neg hwin)).trans
    simpa only [RepresentativeWindow.crtPatch_value_residues] using hscore
  obtain ⟨d, P, hP, hscoreP⟩ := hconvert N hN T w (fun x => f x - (1 + xi) * alpha)
    hq (hT.mono le_rfl hsc) (hw.trans hwin) hs
  have hbound : (q + 2) ^ A ≤ (p + 2) ^ C := by
    apply le_trans _ (pow_le_pow_right₀ hbase (le_max_right _ _))
    simpa [q, Polynomial.eval₂_pow] using hbudget p hp0
  exact ⟨d, P, hP.trans hbound, (Real.exp_le_exp.mpr (neg_le_neg hbound)).trans hscoreP⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ProductiveAbsoluteCRTPatches
namespace OAI

section

namespace Erdos3

namespace IntegerVectorAPFree

variable {I J : Type*} {k : ℕ}

theorem mono {A B : Set (I → ℤ)} (hA : IntegerVectorAPFree A k) (hBA : B ⊆ A) :
    IntegerVectorAPFree B k := by
  intro a d hd
  obtain ⟨i, hi⟩ := hA a d hd
  exact ⟨i, fun h => hi (hBA h)⟩

end IntegerVectorAPFree

namespace BooleanCubeKernel

theorem joint_sample_progression_free {K X : Type*} [Fintype K]
    {A : Set (X → ℤ)} {k : ℕ} (hA : IntegerVectorAPFree A k) (hk : 2 ≤ k)
    (z : (X → ℤ) × (Option K × X → ℤ)) (domain : Set (K → ℤ))
    (hinj : Set.InjOn (fun x => jointIntegerPhysicalSite x z) domain) :
    IntegerVectorAPFree (domain ∩ (fun x => jointIntegerPhysicalSite x z) ⁻¹' A) k := by
  classical
  let L : (K → ℤ) →+ (X → ℤ) :=
    (Matrix.of (fun i j => z.2 (some j,i))).mulVecLin.toAddMonoidHom
  let b : X → ℤ := fun i => z.1 i + z.2 (none,i)
  have he (x : K → ℤ) : jointIntegerPhysicalSite x z = b + L x := by
    funext i
    change z.1 i + (z.2 (none,i) + ∑ j, x j * z.2 (some j,i)) =
      (z.1 i + z.2 (none,i)) + ∑ j, z.2 (some j,i) * x j
    rw [← add_assoc]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h := hA.affine_preimage hk L b domain (by simpa only [he] using hinj)
  simpa only [he] using h

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

namespace IntegerVectorAPFree

end IntegerVectorAPFree

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem PolynomialPatch.positive_score_target_lt_one {σ Ω : Type*} [Fintype Ω]
    {s d : ℕ} (P : PolynomialPatch σ s d) (t : Ω → σ → ℝ) (f : Ω → ℝ)
    (hf : ∀ x, f x ≤ 1) {b : ℝ}
    (hscore : 0 < 𝔼 x, (f x - b) * P.value (t x)) : b < 1 := by
  by_contra h
  have hb : 1 ≤ b := le_of_not_gt h
  have hnonpos : (𝔼 x, (f x - b) * P.value (t x)) ≤ 0 := by
    calc
      _ ≤ 𝔼 _x : Ω, (0 : ℝ) := Finset.expect_le_expect
        (fun x _ => mul_nonpos_of_nonpos_of_nonneg
          (by linarith [hf x]) (P.value_mem_Icc _).1)
      _ = 0 := by simp
  exact (not_lt_of_ge hnonpos) hscore

theorem exists_absolute_crt_threshold_rule {J : Type*} [Fintype J] [DecidableEq J]
    [Nonempty J] (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
      ∀ {p a : ℝ}, 2 ≤ p → Real.exp (-p) ≤ a →
      ∀ (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)],
        (∀ j, (N j).Prime) → Function.Injective N →
        (∀ j, Real.exp ((p + 2) ^ C) ≤ N j) →
        ∀ f : ((j : J) → ZMod (N j)) → ℝ,
          (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) → a ≤ (𝔼 x, f x) →
          IntegerVectorAPFree (residueBoxIntegerPoint N '' Function.support f) k →
          (1 + xi) * a < 1 ∧ ∃ d : ℕ, ∃ P : PolynomialPatch J (k - 2) d,
            (d : ℝ) ≤ (p + 2) ^ C ∧
            (P.kernel.lip : ℝ) + 1 ≤ Real.exp ((p + 2) ^ C) ∧
            Real.exp (-((p + 2) ^ C)) ≤
              (𝔼 x, (f x - (1 + xi) * a) * P.value (fun j => ((x j).val : ℝ))) := by
  obtain ⟨C, hC, xi, hxi, hpatch⟩ := exists_absolute_crt_patch (J := J) k hk
  refine ⟨C, hC, xi, hxi, ?_⟩
  intro p a hp ha N _ _ hprime hinj hsize f hf hmean hfree
  let alpha := 𝔼 x, f x
  have halpha : 0 < alpha := (Real.exp_pos (-p)).trans_le (ha.trans hmean)
  have hlog : Real.log (1 / alpha) ≤ p := by
    rw [one_div, Real.log_inv]
    have h := Real.log_le_log (Real.exp_pos (-p)) (ha.trans hmean)
    rw [Real.log_exp] at h
    linarith
  obtain ⟨d, P, hcost, hscore⟩ := hpatch N hprime hinj f halpha hp hlog hsize hf rfl hfree
  have hlognonneg : 0 ≤ Real.log (2 + (P.kernel.lip : ℝ)) :=
    Real.log_nonneg (by linarith [P.kernel.lip.coe_nonneg])
  have hlip : Real.log (2 + (P.kernel.lip : ℝ)) ≤ (p + 2) ^ C := by
    linarith [Nat.cast_nonneg (α := ℝ) d]
  have hscore' : Real.exp (-((p + 2) ^ C)) ≤
      (𝔼 x, (f x - (1 + xi) * a) * P.value (fun j => ((x j).val : ℝ))) := by
    apply hscore.trans
    apply Finset.expect_le_expect
    intro x _
    apply mul_le_mul_of_nonneg_right _ (P.value_mem_Icc _).1
    have h := mul_le_mul_of_nonneg_left hmean (show 0 ≤ 1 + xi by linarith)
    dsimp only [alpha] at *
    linarith
  refine ⟨P.positive_score_target_lt_one _ f (fun x => (hf x).2)
    ((Real.exp_pos _).trans_le hscore'), d, P, by linarith, ?_, hscore'⟩
  · have h := Real.exp_le_exp.mpr hlip
    rw [Real.exp_log (by positivity : 0 < 2 + (P.kernel.lip : ℝ))] at h
    linarith

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedProductivePathPullback
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {nX : ℕ} {N : Fin nX → ℕ}
    {widths : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ}
    {bases : Finset (Fin nX → ℤ)} {test : (Fin nX → ℝ) → ℝ} {gain : ℝ}
    {z : bases × rectangularWeightIndices 0 widths 1}

namespace AllocatedPathProductivity

variable (hproductive : AllocatedPathProductivity B U b S N widths bases test gain z)

include hproductive

theorem physical_injOn :
    Set.InjOn (fun q => jointIntegerPhysicalSite q (z.1.val, z.2.val))
      (↑(integerBox (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)))) := by
  intro u hu v hv huv
  exact congrArg Subtype.val (hproductive.1 (a₁ := ⟨u, hu⟩) (a₂ := ⟨v, hv⟩) huv)

theorem pullback_mem_Icc {f : (Fin nX → ℤ) → ℝ}
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ q ∈ integerBox (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)),
      f (jointIntegerPhysicalSite q (z.1.val, z.2.val)) ∈ Set.Icc (0 : ℝ) 1 := by
  intro q hq
  exact hf _ (hproductive.2.2 ⟨q, hq⟩)

theorem pullback_apFree {f : (Fin nX → ℤ) → ℝ} {k : ℕ} (hk : 2 ≤ k)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} k) :
    IntegerVectorAPFree
      {q | q ∈ integerBox (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)) ∧
        f (jointIntegerPhysicalSite q (z.1.val, z.2.val)) ≠ 0} k := by
  apply (joint_sample_progression_free hfree hk (z.1.val, z.2.val)
    (↑(integerBox (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S))))
    hproductive.physical_injOn).mono
  intro q hq
  exact ⟨hq.1, hproductive.2.2 ⟨q, hq.1⟩, hq.2⟩

end AllocatedPathProductivity
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AmplificationSourceResourceBudget
namespace OAI

section

namespace Erdos3

theorem amplificationSourceLogCoefficient_pos (D : ℕ) {E : ℕ} (hE : 1 ≤ E) :
    0 < amplificationSourceLogCoefficient D E := by
  unfold amplificationSourceLogCoefficient
  have hE0 : (0 : ℝ) < E := by exact_mod_cast (show 0 < E by omega)
  positivity

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativeAmplificationDiscount
namespace OAI

section

namespace Erdos3

theorem exists_relative_amplification_discount (s : ℕ) {H : ℝ} (hH : 1 < H) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 / 2 ∧
      let κ := (1 - τ) ^ (s + 1)
      0 < κ ∧ κ < 1 ∧ 1 < κ * H ∧ 1 ≤ κ ^ 2 * H := by
  have hH0 : 0 < H := by linarith
  have hn : (1 : ℝ) ≤ (s + 1 : ℕ) := by exact_mod_cast Nat.succ_pos s
  let τ := (H - 1) / (4 * (s + 1 : ℕ) * H)
  have ht : 0 < τ := div_pos (by linarith) (by positivity)
  have ht4 : τ ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (s + 1 : ℕ) * H)).mpr
    have hm := mul_le_mul_of_nonneg_right hn hH0.le
    nlinarith
  have ht1 : 0 < 1 - τ := by linarith
  let κ := (1 - τ) ^ (s + 1)
  have hk : 0 < κ := pow_pos ht1 _
  have hk1 : κ < 1 := pow_lt_one₀ ht1.le (by linarith) (by omega)
  have hbern := one_add_mul_le_pow (a := -τ) (by linarith : -2 ≤ -τ) (2 * (s + 1))
  have hpow : (1 + -τ) ^ (2 * (s + 1)) = κ ^ 2 := by
    rw [Nat.mul_comm, pow_mul]
    rfl
  rw [hpow] at hbern
  have heq : 4 * (s + 1 : ℕ) * H * τ = H - 1 := by
    dsimp only [τ]
    field_simp
  have hmul := mul_le_mul_of_nonneg_right hbern hH0.le
  push_cast at hmul heq
  have hsq : 1 ≤ κ ^ 2 * H := by nlinarith
  have hkk : κ ^ 2 < κ := by nlinarith
  have hgain : 1 < κ * H := hsq.trans_lt (mul_lt_mul_of_pos_right hkk hH0)
  exact ⟨τ, ht, by linarith, hk, hk1, hgain, hsq⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchPositivePowerInduction
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem integerBox_real_expect_eq_residue {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) [∀ i, NeZero (N i)] (f : (X → ℤ) → ℝ) :
    (𝔼 x ∈ integerBox N, f x) = 𝔼 u, f (residueBoxIntegerPoint N u) := by
  symm
  apply Finset.expect_bij (fun u _ => residueBoxIntegerPoint N u)
  · intro u _
    exact (mem_integerBox N _).mpr (fun i =>
      ⟨Int.natCast_nonneg _, by
        change ((u i).val : ℤ) < N i
        exact_mod_cast (u i).val_lt⟩)
  · intro u _
    rfl
  · intro u _ v _ h
    funext i
    apply ZMod.val_injective
    have hi := congrFun h i
    dsimp only [residueBoxIntegerPoint] at hi
    exact_mod_cast hi
  · intro x hx
    have hx' := (mem_integerBox N x).mp hx
    refine ⟨fun i => (x i : ZMod (N i)), Finset.mem_univ _, ?_⟩
    funext i
    dsimp only [residueBoxIntegerPoint]
    rw [ZMod.val_intCast, Int.emod_eq_of_lt (hx' i).1 (hx' i).2]

theorem relativePatchSliceScore_identity {X : Type*} [Fintype X]
    {s d : ℕ} (N : X → ℕ) (f : (X → ℤ) → ℝ) (a : ℝ)
    (A : PolynomialPatch X s d) :
    relativePatchSliceScore (ResidueBoxSlice.identity N) f a A =
      relativePatchBoxScore N f a A := by
  unfold relativePatchSliceScore relativePatchBoxScore
  simp only [ResidueBoxSlice.identity, ResidueBoxSlice.point, zero_add, one_mul]
  apply Finset.expect_bij (fun t _ i => ((t i).val : ℤ))
  · intro t _
    exact (mem_integerBox N _).mpr (fun i =>
      ⟨Int.natCast_nonneg _, by exact_mod_cast (t i).isLt⟩)
  · intro t _
    simp only [Int.cast_natCast]
  · intro t _ u _ h
    funext i
    apply Fin.ext
    exact_mod_cast congrFun h i
  · intro x hx
    have hx' := (mem_integerBox N x).mp hx
    refine ⟨fun i => ⟨(x i).toNat, by have := hx' i; omega⟩, Finset.mem_univ _, ?_⟩
    funext i
    exact Int.toNat_of_nonneg (hx' i).1

theorem exists_initial_relative_absolute_rule (n₀ : ℕ) [NeZero n₀]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
      ∀ {p a : ℝ}, 2 ≤ p → Real.exp (-p) ≤ a →
        RelativePatchAbsoluteRule (k - 2) n₀ ((p + 2) ^ (C + 1)) a ((1 + xi) * a)
          ⌊(p + 2) ^ C⌋₊ := by
  obtain ⟨C, hC, xi, hxi, habs⟩ := exists_absolute_crt_threshold_rule (J := Fin n₀) k hk
  refine ⟨C, hC, xi, hxi, ?_⟩
  intro p a hp ha N hprime hinj _hcomparable hN f hf hfree hmean
  let : ∀ i, NeZero (N i) := fun i => ⟨(hprime i).ne_zero⟩
  let : NeZero (∏ i, N i) := ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => (hprime i).ne_zero)⟩
  let x := (p + 2) ^ C
  let cost := (p + 2) ^ (C + 1)
  have hx : 0 ≤ x := pow_nonneg (by linarith) _
  have hcost : 2 * x ≤ cost := by
    dsimp only [cost]
    rw [pow_succ]
    change 2 * x ≤ x * (p + 2)
    nlinarith
  have hxcost : x ≤ cost := by linarith
  have hmem (u : ∀ i, ZMod (N i)) : residueBoxIntegerPoint N u ∈ integerBox N :=
    (mem_integerBox N _).mpr (fun i => ⟨Int.natCast_nonneg _, by
      change ((u i).val : ℤ) < N i
      exact_mod_cast (u i).val_lt⟩)
  have hf' : ∀ u, f (residueBoxIntegerPoint N u) ∈ Set.Icc (0 : ℝ) 1 := fun u => hf _ (hmem u)
  have hmean' : a ≤ 𝔼 u, f (residueBoxIntegerPoint N u) := by
    rwa [integerBox_real_expect_eq_residue] at hmean
  have hfree' : IntegerVectorAPFree
      (residueBoxIntegerPoint N '' Function.support (fun u => f (residueBoxIntegerPoint N u))) k := by
    have hfreeK : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} k := by
      simpa only [Nat.sub_add_cancel (by omega : 2 ≤ k)] using hfree
    intro z d hd
    obtain ⟨i, hi⟩ := hfreeK z d hd
    refine ⟨i, ?_⟩
    rintro ⟨u, hu, he⟩
    apply hi
    rw [← he]
    exact ⟨hmem u, hu⟩
  obtain ⟨_, d, A, hd, hLip, hscore⟩ := habs hp ha N hprime hinj
    (fun i => (Real.exp_le_exp.mpr hxcost).trans (hN i)) (fun u => f (residueBoxIntegerPoint N u))
    hf' hmean' hfree'
  refine ⟨1, by decide, ResidueBoxSlice.identity N, d, A, ?_, Nat.le_floor hd, ?_, ?_⟩
  · intro i
    change Real.exp (-cost) * (N i : ℝ) ≤ (N i : ℝ)
    exact (mul_le_mul_of_nonneg_right
      (Real.exp_le_one_iff.mpr (by linarith)) (Nat.cast_nonneg _)).trans_eq (one_mul _)
  · have hlog : Real.log (1 + (A.kernel.lip : ℝ)) ≤ x := by
      have hh := Real.log_le_log (by positivity : (0 : ℝ) < 1 + A.kernel.lip)
        (by simpa only [add_comm] using hLip)
      rwa [Real.log_exp] at hh
    unfold relativePatchComplexity
    linarith
  · rw [relativePatchSliceScore_identity]
    unfold relativePatchBoxScore
    let : DecidableEq (Fin n₀) := Classical.decEq _
    rw [integerBox_real_expect_eq_residue]
    apply (Real.exp_le_exp.mpr (neg_le_neg hxcost)).trans
    convert hscore using 1
    congr 1
    congr 1
    ext; simp

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial
open scoped BigOperators TensorProduct Classical

namespace ResidueBoxSlice

end ResidueBoxSlice

namespace PolynomialPatch.LowestLayerModel


end PolynomialPatch.LowestLayerModel
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators


end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3
open VectorPolynomial
open scoped BigOperators TensorProduct

namespace PolynomialPatch.LowestLayerModel

end PolynomialPatch.LowestLayerModel
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators


end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators TensorProduct Classical

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial Module
open scoped BigOperators TensorProduct Classical

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial Module
open scoped BigOperators TensorProduct Classical

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RelativePatchAmplificationIteration
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem LowDensityRelativeAbsoluteRule.iterate
    {s n₀ E D₀ D : ℕ} [NeZero n₀] {τ p H₀ : ℝ}
    (hrelative : RelativePatchPowerInductionRule s n₀ s τ E)
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hn : (n₀ : ℝ) ≤ (2 + p) ^ D)
    (hκ : 0 < (1 - τ) ^ (s + 1)) (hκ1 : (1 - τ) ^ (s + 1) < 1)
    (hH : 1 < H₀) (hκH : 1 ≤ ((1 - τ) ^ (s + 1)) ^ 2 * H₀)
    (hbase : LowDensityRelativeAbsoluteRule s n₀ p H₀ D₀ ((2 + p) ^ D)) :
    ∀ j : ℕ, LowDensityRelativeAbsoluteRule s n₀ p
      (amplificationGain ((1 - τ) ^ (s + 1)) H₀ j)
      ((s + 1) ^ j * D₀) (amplificationResource p D (E + 1) j) := by
  intro j
  induction j with
  | zero => simpa only [amplificationGain, amplificationResource, pow_zero, one_mul] using hbase
  | succ j ih =>
    obtain ⟨hgain, hdiscount⟩ := amplificationGain_low_density_parameters hκ hκ1 hH hκH j
    have hparam := amplificationResource_parameter_le hp hD (by omega : 1 ≤ E + 1) j
    have hdim := hn.trans (amplificationResource_zero_le hp hD (by omega : 1 ≤ E + 1) j)
    have hstep := LowDensityRelativeAbsoluteRule.amplify_power hrelative ih
      (amplificationResource_ge_two hp hD (by omega) j) hdim hparam hgain hdiscount
    simpa only [amplificationGain, amplificationResource, pow_succ, Nat.mul_assoc,
      Nat.mul_left_comm, Nat.mul_comm] using hstep

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AmplificationSourceRankBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem amplificationSourceRankLogConstant_pos {b C : ℕ} {K : ℝ}
    (hb : 1 ≤ b) (hK : 1 < K) :
    0 < amplificationSourceRankLogConstant b C K := by
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hprod := mul_nonneg (levelCoefficient_pos hK).le (Real.log_nonneg hb')
  unfold amplificationSourceRankLogConstant
  have := Nat.cast_nonneg (α := ℝ) C
  linarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformRelativePatchSource
namespace OAI

section

open Filter
open scoped Topology

namespace Erdos3

end Erdos3

end

section

namespace Erdos3
open Filter

end Erdos3

end

section

namespace Erdos3

open Filter
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical
open Filter

theorem exists_subquadratic_patch_source_of_uniform_relative_lifting_oai
    (s n₀ : ℕ) [NeZero n₀] (hs : 1 ≤ s)
    (hlifting : ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
      ∃ E : ℕ, 2 ≤ E ∧ RelativePatchPowerInductionRule s n₀ s τ E) :
    ∃ κ H₀ K B D pmin : ℝ,
      0 < κ ∧ 1 < κ * H₀ ∧ 2 ≤ K ∧ 0 < B ∧ 0 < D ∧
      SubquadraticPatchSource (s + 2) s κ H₀ K 1 1 B D pmin (Real.log 2) := by
  obtain ⟨C, hC, xi, hxi, hinitial⟩ :=
    exists_initial_relative_absolute_rule n₀ (s + 2) (by omega)
  have hH : 1 < 1 + xi := by linarith
  obtain ⟨τ, hτ, hτhalf, hκ, hκ1, hκgain, hκH⟩ :=
    exists_relative_amplification_discount s hH
  obtain ⟨E, hE, hrelative⟩ := hlifting τ hτ hτhalf
  have hfamily : ∀ p : ℝ, 2 ≤ p → (n₀ : ℝ) ≤ p → ∀ j : ℕ,
      LowDensityRelativeAbsoluteRule s n₀ p
        (amplificationGain ((1 - τ) ^ (s + 1)) (1 + xi) j)
        ((s + 1) ^ j * ⌊(p + 2) ^ C⌋₊)
        (amplificationResource p (C + 1) (E + 1) j) := by
    intro p hp hn j
    apply LowDensityRelativeAbsoluteRule.iterate hrelative hp (by omega)
      (hn.trans (amplificationResource_parameter_le_zero (K := E + 1) hp (by omega)))
      hκ hκ1 hH hκH _ j
    intro a ha _
    simpa only [Nat.add_sub_cancel, add_comm (2 : ℝ) p] using hinitial hp ha
  obtain ⟨pmin, hsource⟩ := subquadratic_patch_source_of_relative_family
    (by omega : 1 ≤ C) hE hrelative hκ hκ1 hH hκH hfamily
  refine ⟨(1 - τ) ^ (s + 1), 1 + xi, (E + 1 : ℕ),
    amplificationSourceRankLogConstant (s + 1) C (E + 1),
    amplificationSourceLogCoefficient (C + 1) E, pmin, hκ, hκgain,
    ?_, ?_, amplificationSourceLogCoefficient_pos _ (by omega), ?_⟩
  · exact_mod_cast (show 2 ≤ E + 1 by omega)
  · exact amplificationSourceRankLogConstant_pos (by omega) (by exact_mod_cast (show 1 < E + 1 by omega))
  · simpa only [Nat.cast_add, Nat.cast_one] using hsource

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.exists_subquadratic_patch_source_of_uniform_relative_lifting_oai := @OAI.Erdos3.exists_subquadratic_patch_source_of_uniform_relative_lifting_oai
