-- Prove2me | solution 1 for MasulloRH.exists_critical_zero_pairs_tendsto_gap_zero
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:42:19.679748+00:00
-- url     : https://prove2.me/submissions/93e3bbe8-e43d-4f7a-a89a-21443a65819c

import Theorems.Thm_RiemannVonMangoldt_riemann_von_mangoldt
import Theorems.Thm_Zeta23_thmA0_cumulative
import Definitions.Def_RiemannVonMangoldt_ZeroCounts

open Asymptotics Filter Set
open scoped Topology

namespace MasulloAudit

private theorem exists_close_pair_of_card (S : Finset ℝ) {T δ : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ)
    (hS : ∀ x ∈ S, 0 ≤ x ∧ x ≤ T) (hcard : T / δ + 1 < (S.card : ℝ)) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ |a - b| < δ := by
  classical
  by_contra! h
  let bin : S → Fin (⌊T / δ⌋₊ + 1) := fun x ↦
    ⟨⌊(x : ℝ) / δ⌋₊, Nat.lt_succ_of_le
      (Nat.floor_mono (div_le_div_of_nonneg_right (hS x x.property).2 hδ.le))⟩
  have hbin : Function.Injective bin := by
    intro a b hab
    apply Subtype.ext
    by_contra hne
    have hfloor : ⌊(a : ℝ) / δ⌋₊ = ⌊(b : ℝ) / δ⌋₊ := congrArg Fin.val hab
    have ha0 : 0 ≤ (a : ℝ) / δ := div_nonneg (hS a a.property).1 hδ.le
    have hb0 : 0 ≤ (b : ℝ) / δ := div_nonneg (hS b b.property).1 hδ.le
    have hau := Nat.lt_floor_add_one ((a : ℝ) / δ)
    have hbu := Nat.lt_floor_add_one ((b : ℝ) / δ)
    have hal := Nat.floor_le ha0
    have hbl := Nat.floor_le hb0
    rw [hfloor] at hau hal
    have hdiff : |(a : ℝ) - (b : ℝ)| < δ := by
      rw [abs_sub_lt_iff]
      constructor
      · have hle : (a : ℝ) / δ - (b : ℝ) / δ < 1 := by linarith
        rw [← sub_div] at hle
        simpa using (div_lt_iff₀ hδ).mp hle
      · have hle : (b : ℝ) / δ - (a : ℝ) / δ < 1 := by linarith
        rw [← sub_div] at hle
        simpa using (div_lt_iff₀ hδ).mp hle
    exact (not_lt.mpr (h a a.property b b.property hne)) hdiff
  have hleN : S.card ≤ ⌊T / δ⌋₊ + 1 := by
    simpa using Fintype.card_le_of_injective bin hbin
  have hleR : (S.card : ℝ) ≤ (⌊T / δ⌋₊ : ℝ) + 1 := by exact_mod_cast hleN
  exact (not_lt.mpr (hleR.trans (add_le_add (Nat.floor_le (div_nonneg hT hδ.le)) le_rfl))) hcard

/-- A superlinear count of distinct points forces arbitrarily small positive gaps. -/
theorem exists_frequency_pairs_tendsto_zero (Z : Set ℝ)
    (hcount : ∀ C : ℝ, 0 < C → ∃ T : ℝ, 1 ≤ T ∧ ∃ S : Finset ℝ,
      (∀ x ∈ S, x ∈ Z ∧ 0 ≤ x ∧ x ≤ T) ∧ C * T < (S.card : ℝ)) :
    ∃ a b : ℕ → Z, (∀ n, a n ≠ b n) ∧
      Tendsto (fun n ↦ ((a n : Z) : ℝ) - ((b n : Z) : ℝ)) atTop (𝓝 0) := by
  have hclose (δ : ℝ) (hδ : 0 < δ) :
      ∃ a b : Z, a ≠ b ∧ |(a : ℝ) - (b : ℝ)| < δ := by
    obtain ⟨T, hT, S, hS, hcard⟩ := hcount (1 / δ + 1) (by positivity)
    have ht0 := zero_le_one.trans hT
    have hlower : T / δ + 1 ≤ (1 / δ + 1) * T := by
      calc
        _ ≤ T / δ + T := add_le_add le_rfl hT
        _ = _ := by ring
    obtain ⟨a, ha, b, hb, hab, hδab⟩ :=
      exists_close_pair_of_card S ht0 hδ (fun x hx ↦ (hS x hx).2) (hlower.trans_lt hcard)
    exact ⟨⟨a, (hS a ha).1⟩, ⟨b, (hS b hb).1⟩, fun he ↦ hab (congrArg Subtype.val he), hδab⟩
  have hseq (n : ℕ) := hclose (1 / ((n : ℝ) + 1)) (by positivity)
  choose a b hab hgap using hseq
  refine ⟨a, b, hab, tendsto_zero_iff_norm_tendsto_zero.mpr ?_⟩
  exact squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _))
    (Eventually.of_forall (fun n ↦ by simpa only [Real.norm_eq_abs] using (hgap n).le))
    tendsto_one_div_add_atTop_nhds_zero_nat



private lemma zetaZeroCount_eq (T : ℝ) :
    RiemannVonMangoldt.zetaZeroCount T = (Zeta23.Ncount 0 T : ℝ) := by
  unfold RiemannVonMangoldt.zetaZeroCount Zeta23.Ncount
  have hs : {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im ≤ T ∧ riemannZeta s = 0} =
      Zeta23.zerosIn 0 T := by
    ext s
    simp only [Zeta23.zerosIn, Zeta23.IsNontrivialZero, Set.mem_ofPred_eq]
    tauto
  have hf : (Zeta23.zerosIn 0 T).Finite := Zeta23.ZetaSeam.finite_window_holds 0 T
  rw [hs, Nat.cast_finsum_mem hf]
  rfl

private lemma eventually_count_gt_linear
    (hcount : (fun T : ℝ ↦ RiemannVonMangoldt.zetaZeroCount T -
      (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi))) =O[atTop] Real.log)
    (C : ℝ) : ∀ᶠ T in atTop, (C * T : ℝ) < Zeta23.Ncount 0 T := by
  let P := 2 * Real.pi
  have hP : 0 < P := by unfold P; positivity
  obtain ⟨K, hK, herror⟩ := Asymptotics.isBigO_iff'.mp hcount
  have htlog := Real.tendsto_log_atTop.eventually_gt_atTop (2 * (P * C + Real.log P + 1))
  filter_upwards [herror, eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (2 * P * K), htlog] with
    T hTerror hT hTlarge hlog
  have hT0 : 0 < T := by linarith
  have hlog0 := Real.log_nonneg hT
  change ‖RiemannVonMangoldt.zetaZeroCount T -
    (T / P * Real.log (T / P) - T / P)‖ ≤ K * ‖Real.log T‖ at hTerror
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hlog0, zetaZeroCount_eq,
    Real.log_div hT0.ne' hP.ne'] at hTerror
  have hKle : K ≤ T / (2 * P) := by
    exact (le_div_iff₀ (by positivity)).2 (by linarith only [hTlarge])
  have hmul := mul_le_mul_of_nonneg_right hKle hlog0
  have hlower := (abs_le.mp hTerror).1
  have hev : P * C + Real.log P + 1 < Real.log T / 2 := by linarith
  have hproduct := mul_lt_mul_of_pos_left hev (div_pos hT0 hP)
  have heq : T / P * (P * C) = C * T := by field_simp
  have heq2 : T / P * (Real.log T / 2) = T / (2 * P) * Real.log T := by ring
  have heq3 : T / P * (Real.log T - Real.log P) - T / P =
      T / P * Real.log T - T / P * (Real.log P + 1) := by ring
  have heq4 : T / P * Real.log T = 2 * (T / (2 * P) * Real.log T) := by ring
  rw [heq3, heq4] at hlower
  rw [heq2, show P * C + Real.log P + 1 = P * C + (Real.log P + 1) by ring, mul_add, heq]
    at hproduct
  linarith

private def criticalFrequency (t : ℝ) : Prop :=
  0 < t ∧ riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = 0

private theorem criticalFrequency_count
    (hcount : (fun T : ℝ ↦ RiemannVonMangoldt.zetaZeroCount T -
      (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi))) =O[atTop] Real.log)
    (C : ℝ) (_hC : 0 < C) : ∃ T : ℝ, 1 ≤ T ∧ ∃ S : Finset ℝ,
      (∀ x ∈ S, x ∈ {t | criticalFrequency t} ∧ 0 ≤ x ∧ x ≤ T) ∧ C * T < (S.card : ℝ) := by
  obtain ⟨T₀, hdensity⟩ := Zeta23.thmA0_cumulative (1 / 6) (by norm_num)
  have hev : ∀ᶠ T : ℝ in atTop, 1 ≤ T ∧ T₀ ≤ T ∧ 2 * C * T < (Zeta23.Ncount 0 T : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop T₀,
      eventually_count_gt_linear hcount (2 * C)] with T hT hT₀ hcountT
    exact ⟨hT, hT₀, hcountT⟩
  obtain ⟨T, hT, hT₀, hcountT⟩ := hev.exists
  have hf : (Zeta23.zerosIn 0 T ∩ {ρ : ℂ | ρ.re = 1 / 2}).Finite :=
    (Zeta23.ZetaSeam.finite_window_holds 0 T).subset Set.inter_subset_left
  let Z := hf.toFinset
  classical
  refine ⟨T, hT, Z.image Complex.im, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    have h : s ∈ Zeta23.zerosIn 0 T ∩ {ρ : ℂ | ρ.re = 1 / 2} := hf.mem_toFinset.mp hs
    have hs' : s = (1 / 2 : ℂ) + (s.im : ℂ) * Complex.I := by
      apply Complex.ext
      · simpa [Complex.div_ofNat_re] using h.2
      · simp
    exact ⟨⟨h.1.2.1, hs' ▸ h.1.1.1⟩, h.1.2.1.le, h.1.2.2⟩
  · have hfiber : Set.InjOn Complex.im (Z : Set ℂ) := by
      intro x hx y hy him
      have hx' := (hf.mem_toFinset.mp hx).2
      have hy' := (hf.mem_toFinset.mp hy).2
      exact Complex.ext (hx'.trans hy'.symm) him
    rw [Finset.card_image_of_injOn hfiber]
    change C * T < (hf.toFinset.card : ℝ)
    rw [← Set.ncard_eq_toFinset_card _ hf]
    have hB := hdensity T hT₀
    norm_num at hB
    exact lt_of_lt_of_le (by linarith) hB

/-- The arithmetic bridge from the cumulative count and the distinct critical-zero proportion. -/
private theorem exists_critical_zero_pairs_tendsto_gap_zero_of_rvm
    (hcount : (fun T : ℝ ↦ RiemannVonMangoldt.zetaZeroCount T -
      (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi))) =O[atTop] Real.log) :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n ∧ 0 < b n ∧ a n ≠ b n ∧
        riemannZeta ((1 / 2 : ℂ) + (a n : ℂ) * Complex.I) = 0 ∧
        riemannZeta ((1 / 2 : ℂ) + (b n : ℂ) * Complex.I) = 0) ∧
      Tendsto (fun n ↦ a n - b n) atTop (𝓝 0) := by
  obtain ⟨a, b, hab, hgap⟩ := exists_frequency_pairs_tendsto_zero {t | criticalFrequency t}
    (criticalFrequency_count hcount)
  refine ⟨fun n ↦ a n, fun n ↦ b n, fun n ↦ ?_, hgap⟩
  exact ⟨(a n).property.1, (b n).property.1, fun h ↦ hab n (Subtype.ext h),
    (a n).property.2, (b n).property.2⟩

end MasulloAudit

theorem solution :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n ∧ 0 < b n ∧ a n ≠ b n ∧
        riemannZeta ((1 / 2 : ℂ) + (a n : ℂ) * Complex.I) = 0 ∧
        riemannZeta ((1 / 2 : ℂ) + (b n : ℂ) * Complex.I) = 0) ∧
      Tendsto (fun n ↦ a n - b n) atTop (𝓝 0) :=
  MasulloAudit.exists_critical_zero_pairs_tendsto_gap_zero_of_rvm
    RiemannVonMangoldt.riemann_von_mangoldt
