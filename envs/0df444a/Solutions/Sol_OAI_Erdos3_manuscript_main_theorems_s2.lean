-- Prove2me | solution 1 for OAI.Erdos3.manuscript_main_theorems_s2
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-10-28T22:37:52.493304+00:00
-- url     : https://prove2.me/submissions/b4a1163c-9fc5-4318-a76d-51dc81426fa0

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B252
import Theorems.Thm_OAI_Erdos3_exists_initial_relative_absolute_rule_s2
import Theorems.Thm_OAI_Erdos3_exists_manuscriptRelativePatchPower_s2
import Theorems.Thm_OAI_Erdos3_quantitative_density_of_patch_source_s2
import Theorems.Thm_OAI_Erdos3_subquadratic_patch_source_of_relative_family_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Results.Basic
namespace OAI

section

namespace Erdos3

theorem HasAP.of_le {A : Set ℕ} {k l : ℕ} (h : HasAP A k) (hlk : l ≤ k) :
    HasAP A l := by
  obtain ⟨a, d, hd, h⟩ := h
  exact ⟨a, d, hd, fun i hi ↦ h i (hi.trans_le hlk)⟩

theorem card_le_extremalNumber {k N : ℕ} {S : Finset ℕ}
    (hSN : S ⊆ Finset.Icc 1 N) (hS : APFree (S : Set ℕ) k) :
    S.card ≤ extremalNumber k N := by
  classical
  exact Finset.le_sup (f := Finset.card)
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSN, hS⟩)

theorem card_le_extremalNumber_of_interval {k N t : ℕ} {S : Finset ℕ}
    (hSN : S ⊆ Finset.Icc (t + 1) (t + N)) (hS : APFree (S : Set ℕ) k) :
    S.card ≤ extremalNumber k N := by
  classical
  let T := S.image (fun n ↦ n - t)
  have hT : T ⊆ Finset.Icc 1 N := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    have hxN := Finset.mem_Icc.mp (hSN hx)
    apply Finset.mem_Icc.mpr
    omega
  have hfree : APFree (T : Set ℕ) k := by
    apply (hS.affine_preimage t 1 (by omega)).mono
    intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    have hxN := Finset.mem_Icc.mp (hSN hx)
    have heq : t + 1 * (x - t) = x := by omega
    simpa only [Set.mem_preimage, heq, Finset.mem_coe] using hx
  have hcard : T.card = S.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    have hxN := Finset.mem_Icc.mp (hSN hx)
    have hyN := Finset.mem_Icc.mp (hSN hy)
    change x - t = y - t at hxy
    omega
  rw [← hcard]
  exact card_le_extremalNumber hT hfree

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchAmplification
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem RelativePatchSliceConclusion.mono {X : Type*} [Fintype X] {s : ℕ}
    {N : X → ℕ} {f : (X → ℤ) → ℝ} {target : ℝ} {rankBound rankBound' : ℕ}
    {cost cost' : ℝ} (h : RelativePatchSliceConclusion s N f target rankBound cost)
    (hrank : rankBound ≤ rankBound') (hcost : cost ≤ cost') :
    RelativePatchSliceConclusion s N f target rankBound' cost' := by
  obtain ⟨q, hq, S, d, A, hlength, hd, hcomplexity, hscore⟩ := h
  have he : Real.exp (-cost') ≤ Real.exp (-cost) :=
    Real.exp_le_exp.mpr (neg_le_neg hcost)
  exact ⟨q, hq, S, d, A, fun i =>
    (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _)).trans (hlength i),
    hd.trans hrank, hcomplexity.trans hcost, he.trans hscore⟩

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem scalarNativeDimension_pos (s : ℕ) : 0 < scalarNativeDimension s := by
  unfold scalarNativeDimension
  positivity

end Erdos3.VectorPolynomial

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Results.Reciprocal
namespace OAI

section

open scoped BigOperators

namespace Erdos3

theorem reciprocalTerm_nonneg (A : Set ℕ) (n : ℕ) : 0 ≤ reciprocalTerm A n := by
  classical
  unfold reciprocalTerm
  split_ifs <;> positivity

theorem dyadic_sum_le {k m : ℕ} {S : Finset ℕ}
    (hS : APFree (S : Set ℕ) k)
    (hSm : ∀ n ∈ S, 2 ^ m ≤ n ∧ n < 2 ^ (m + 1)) :
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤ (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m := by
  have hp : 0 < (2 : ℕ) ^ m := by positivity
  have hinterval : S ⊆ Finset.Icc (2 ^ m - 1 + 1) (2 ^ m - 1 + 2 ^ m) := by
    intro n hn
    have h := hSm n hn
    rw [pow_succ] at h
    apply Finset.mem_Icc.mpr
    omega
  have hcard := card_le_extremalNumber_of_interval hinterval hS
  calc
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤ ∑ _n ∈ S, ((2 : ℝ) ^ m)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      apply inv_anti₀ (by positivity)
      exact_mod_cast (hSm n hn).1
    _ = (S.card : ℝ) / 2 ^ m := by simp [div_eq_mul_inv]
    _ ≤ (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hcard

theorem reciprocal_sum_le_dyadic_tsum {k : ℕ}
    (hseries : Summable fun m : ℕ ↦ (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m)
    {S : Finset ℕ} (hS : APFree (S : Set ℕ) k) (hpos : ∀ n ∈ S, n ≠ 0) :
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤
      ∑' m : ℕ, (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m := by
  classical
  calc
    (∑ n ∈ S, (n : ℝ)⁻¹) =
        ∑ m ∈ S.image (Nat.log 2), ∑ n ∈ S with Nat.log 2 n = m, (n : ℝ)⁻¹ :=
      (Finset.sum_fiberwise_of_maps_to (s := S) (g := Nat.log 2)
        (fun n hn ↦ Finset.mem_image.mpr ⟨n, hn, rfl⟩)
        (fun n : ℕ ↦ (n : ℝ)⁻¹)).symm
    _ ≤ ∑ m ∈ S.image (Nat.log 2), (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m := by
      apply Finset.sum_le_sum
      intro m hm
      apply dyadic_sum_le (hS.mono (by intro n hn; exact (Finset.mem_filter.mp hn).1))
      intro n hn
      obtain ⟨hn, heq⟩ := Finset.mem_filter.mp hn
      rw [← heq]
      exact ⟨Nat.pow_log_le_self 2 (hpos n hn), Nat.lt_pow_succ_log_self (by omega) n⟩
    _ ≤ ∑' m : ℕ, (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m :=
      hseries.sum_le_tsum _ (fun _ _ ↦ by positivity)

theorem summable_reciprocal_of_APFree {k : ℕ}
    (hseries : Summable fun m : ℕ ↦ (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m)
    {A : Set ℕ} (hA : APFree A k) : Summable (reciprocalTerm A) := by
  classical
  apply summable_of_sum_le (fun n ↦ reciprocalTerm_nonneg A n)
    (c := ∑' m : ℕ, (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m)
  intro S
  let T := S.filter (fun n ↦ n ∈ A ∧ n ≠ 0)
  have hT : APFree (T : Set ℕ) k :=
    hA.mono (by intro n hn; exact (Finset.mem_filter.mp hn).2.1)
  have hpos : ∀ n ∈ T, n ≠ 0 := fun n hn ↦ (Finset.mem_filter.mp hn).2.2
  have heq : (∑ n ∈ S, reciprocalTerm A n) = ∑ n ∈ T, (n : ℝ)⁻¹ := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hmem : n ∈ A <;> by_cases hn0 : n = 0 <;>
      simp [reciprocalTerm, hmem, hn0]
  rw [heq]
  exact reciprocal_sum_le_dyadic_tsum hseries hT hpos

theorem hasAP_of_not_summable_reciprocal {k : ℕ}
    (hseries : Summable fun m : ℕ ↦ (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m)
    {A : Set ℕ} (hA : ¬ Summable (reciprocalTerm A)) : HasAP A k := by
  by_contra hfree
  exact hA (summable_reciprocal_of_APFree hseries hfree)

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

theorem eventually_exp_loglog_rpow_le {c η : ℝ} (hc : 0 < c) (hη : 0 < η)
    (B : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (-c * (Real.log (Real.log x)) ^ (1 + η)) ≤
        ((Real.log x) ^ B)⁻¹ := by
  have hloglog : Tendsto (fun x : ℝ ↦ Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hpow := (tendsto_rpow_atTop hη).comp hloglog
  filter_upwards [hpow.eventually (eventually_ge_atTop (B / c)),
    hloglog.eventually (eventually_gt_atTop 0), eventually_gt_atTop (1 : ℝ)] with
    x hlarge hz hx
  have hBc : B ≤ c * (Real.log (Real.log x)) ^ η := by
    exact (div_le_iff₀ hc).mp hlarge |>.trans_eq (mul_comm _ _)
  have hmul := mul_le_mul_of_nonneg_left hBc hz.le
  have hpower : (Real.log (Real.log x)) ^ (1 + η) =
      Real.log (Real.log x) * (Real.log (Real.log x)) ^ η := by
    rw [Real.rpow_add hz, Real.rpow_one]
  rw [Real.rpow_def_of_pos (Real.log_pos hx), ← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  rw [hpower]
  nlinarith

theorem QuantitativeDensityBound.eventually_logarithmic {k : ℕ}
    (h : QuantitativeDensityBound k) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      (extremalNumber k N : ℝ) ≤ C * N / (Real.log N) ^ B := by
  obtain ⟨C, c, η, hC, hc, hη, hbound⟩ := h
  refine ⟨C, hC, ?_⟩
  have htail := tendsto_natCast_atTop_atTop.eventually
    (eventually_exp_loglog_rpow_le hc hη B)
  filter_upwards [htail, eventually_ge_atTop 3] with N hN hN3
  apply (hbound N hN3).trans
  simpa only [div_eq_mul_inv] using
    mul_le_mul_of_nonneg_left hN (show 0 ≤ C * (N : ℝ) by positivity)

theorem summable_dyadic_of_eventually_logarithmic {k : ℕ} {C B : ℝ}
    (hB : 1 < B)
    (hbound : ∀ᶠ N : ℕ in atTop,
      (extremalNumber k N : ℝ) ≤ C * N / (Real.log N) ^ B) :
    Summable (fun m : ℕ ↦ (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsum : Summable (fun m : ℕ ↦ (C / (Real.log 2) ^ B) * ((m : ℝ) ^ B)⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr hB).mul_left _
  apply hsum.of_norm_bounded_eventually_nat
  have hpow : Tendsto (fun m : ℕ ↦ (2 : ℕ) ^ m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  filter_upwards [hpow.eventually hbound] with m hm
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hden : (0 : ℝ) < 2 ^ m := by positivity
  have hcast : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m := by norm_cast
  rw [hcast, Real.log_pow, Real.mul_rpow (by positivity) hlog2.le] at hm
  calc
    (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m
        ≤ (C * 2 ^ m / ((m : ℝ) ^ B * (Real.log 2) ^ B)) / 2 ^ m :=
      div_le_div_of_nonneg_right hm hden.le
    _ = (C / (Real.log 2) ^ B) * ((m : ℝ) ^ B)⁻¹ := by
      field_simp

theorem QuantitativeDensityBound.summable_dyadic {k : ℕ}
    (h : QuantitativeDensityBound k) :
    Summable (fun m : ℕ ↦ (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m) := by
  obtain ⟨C, _hC, htail⟩ := h.eventually_logarithmic 2
  exact summable_dyadic_of_eventually_logarithmic (by norm_num) htail

theorem QuantitativeDensityBound.hasAP {k : ℕ} (h : QuantitativeDensityBound k)
    {A : Set ℕ} (hA : ¬ Summable (reciprocalTerm A)) : HasAP A k :=
  hasAP_of_not_summable_reciprocal h.summable_dyadic hA

theorem reciprocalProgressionTheorem_of_quantitativeDensityTheorem
    (h : QuantitativeDensityTheorem) : ReciprocalProgressionTheorem := by
  intro A hA k
  by_cases hk : 3 ≤ k
  · exact (h k hk).hasAP hA
  · exact ((h 3 le_rfl).hasAP hA).of_le (by omega)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical
open Filter

theorem exists_subquadratic_patch_source_of_uniform_relative_lifting
    (s n₀ : ℕ) [NeZero n₀] (hs : 1 ≤ s)
    (hlifting : ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
      ∃ E : ℕ, 2 ≤ E ∧ RelativePatchPowerInductionRule s n₀ s τ E) :
    ∃ κ H₀ K B D pmin : ℝ,
      0 < κ ∧ 1 < κ * H₀ ∧ 2 ≤ K ∧ 0 < B ∧ 0 < D ∧
      SubquadraticPatchSource (s + 2) s κ H₀ K 1 1 B D pmin (Real.log 2) := by
  obtain ⟨C, hC, xi, hxi, hinitial⟩ :=
    exists_initial_relative_absolute_rule_s2 n₀ (s + 2) (by omega)
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
  obtain ⟨pmin, hsource⟩ := subquadratic_patch_source_of_relative_family_s2
    (by omega : 1 ≤ C) hE hrelative hκ hκ1 hH hκH hfamily
  refine ⟨(1 - τ) ^ (s + 1), 1 + xi, (E + 1 : ℕ),
    amplificationSourceRankLogConstant (s + 1) C (E + 1),
    amplificationSourceLogCoefficient (C + 1) E, pmin, hκ, hκgain,
    ?_, ?_, amplificationSourceLogCoefficient_pos _ (by omega), ?_⟩
  · exact_mod_cast (show 2 ≤ E + 1 by omega)
  · exact amplificationSourceRankLogConstant_pos (by omega) (by exact_mod_cast (show 1 < E + 1 by omega))
  · simpa only [Nat.cast_add, Nat.cast_one] using hsource

theorem quantitative_density_bound_of_uniform_relative_lifting
    (k n₀ : ℕ) [NeZero n₀] (hk : 3 ≤ k)
    (hlifting : ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
      ∃ E : ℕ, 2 ≤ E ∧ RelativePatchPowerInductionRule (k - 2) n₀ (k - 2) τ E) :
    QuantitativeDensityBound k := by
  obtain ⟨κ, H₀, K, B, D, pmin, hκ, hgain, hK, hB, hD, hsource⟩ :=
    exists_subquadratic_patch_source_of_uniform_relative_lifting (k - 2) n₀ (by omega) hlifting
  have hresult := quantitative_density_of_patch_source_s2 (by omega : 0 < (k - 2) + 2)
    hκ hgain hK (by norm_num : (1 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 1) hB hD hsource
  simpa only [Nat.sub_add_cancel (by omega : 2 ≤ k)] using hresult

theorem manuscript_targets_of_uniform_relative_lifting
    (hlifting : ∀ k : ℕ, 3 ≤ k → ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
        ∃ E : ℕ, 2 ≤ E ∧ RelativePatchPowerInductionRule (k - 2) n₀ (k - 2) τ E) :
    QuantitativeDensityTheorem ∧ ReciprocalProgressionTheorem := by
  have hquant : QuantitativeDensityTheorem := by
    intro k hk
    obtain ⟨n₀, hn₀, hrelative⟩ := hlifting k hk
    let : NeZero n₀ := ⟨Nat.ne_of_gt hn₀⟩
    exact quantitative_density_bound_of_uniform_relative_lifting k n₀ hk hrelative
  exact ⟨hquant, reciprocalProgressionTheorem_of_quantitativeDensityTheorem hquant⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Results.Conclusions
namespace OAI

section

namespace Erdos3

theorem manuscript_main_theorems :
    QuantitativeDensityTheorem ∧ ReciprocalProgressionTheorem := by
  apply manuscript_targets_of_uniform_relative_lifting
  intro k hk
  refine ⟨VectorPolynomial.scalarNativeDimension (k - 2),
    VectorPolynomial.scalarNativeDimension_pos (k - 2), ?_⟩
  intro discount hdiscount hhalf
  exact exists_manuscriptRelativePatchPower_s2 (k - 2) (by omega) discount hdiscount hhalf

theorem manuscriptReciprocalProgressionTheorem_oai : ReciprocalProgressionTheorem :=
  manuscript_main_theorems.2

end Erdos3

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.manuscript_main_theorems := @OAI.Erdos3.manuscript_main_theorems
