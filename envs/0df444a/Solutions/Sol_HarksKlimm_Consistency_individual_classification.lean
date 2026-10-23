-- Prove2me | solution 1 for HarksKlimm.Consistency.individual_classification
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T18:10:09.916659+00:00
-- url     : https://prove2.me/submissions/6b68ea3b-624c-4177-bde5-eeac12f4730a

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_ShiftHull
import Definitions.Def_HarksKlimm_Consistency_IsMonotonic
import Definitions.Def_HarksKlimm_Consistency_IsAffine
import Definitions.Def_HarksKlimm_Consistency_IsExponential
-- ===== module A

noncomputable section
set_option linter.unusedSectionVars false
open scoped NNReal
open Filter Topology

namespace X5HK

/-- Continuous additive functions on `ℝ≥0` are linear. -/
lemma cauchy_nn (f : ℝ≥0 → ℝ) (hf : Continuous f) (hadd : ∀ x y, f (x + y) = f x + f y) :
    ∀ x, f x = f 1 * x := by
  have h0 : f 0 = 0 := by have := hadd 0 0; simp at this; linarith
  have hn : ∀ (n : ℕ) (x : ℝ≥0), f (n * x) = n * f x := by
    intro n x
    induction n with
    | zero => simp [h0]
    | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, hadd, ih]; push_cast; ring
  have hq : ∀ (m N : ℕ), 0 < N → f ((m : ℝ≥0) / N) = (m : ℝ) / N * f 1 := by
    intro m N hN
    have hN' : (N : ℝ≥0) ≠ 0 := by exact_mod_cast hN.ne'
    have h1 : f 1 = N * f (1 / N) := by
      rw [← hn]; congr 1; field_simp
    have h2 : f ((m : ℝ≥0) / N) = m * f (1 / N) := by
      rw [← hn]; congr 1; field_simp
    rw [h2, h1]
    have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  intro x
  set s : ℕ → ℝ≥0 := fun N => (⌊((N + 1 : ℕ) : ℝ≥0) * x⌋₊ : ℝ≥0) / ((N + 1 : ℕ) : ℝ≥0)
  have hs : Tendsto s atTop (𝓝 x) := by
    rw [← NNReal.tendsto_coe]
    have hup : ∀ N : ℕ, ((s N : ℝ≥0) : ℝ) ≤ x := by
      intro N
      have hpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
      simp only [s, NNReal.coe_div, NNReal.coe_natCast]
      rw [div_le_iff₀ hpos]
      have := Nat.floor_le (show (0 : ℝ≥0) ≤ ((N + 1 : ℕ) : ℝ≥0) * x from zero_le)
      have := (NNReal.coe_le_coe.mpr this)
      simp only [NNReal.coe_natCast, NNReal.coe_mul] at this
      linarith
    have hlow : ∀ N : ℕ, (x : ℝ) - 1 / ((N + 1 : ℕ) : ℝ) ≤ ((s N : ℝ≥0) : ℝ) := by
      intro N
      have hpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
      simp only [s, NNReal.coe_div, NNReal.coe_natCast]
      rw [le_div_iff₀ hpos]
      have := Nat.lt_floor_add_one (((N + 1 : ℕ) : ℝ≥0) * x)
      have := (NNReal.coe_lt_coe.mpr this)
      simp only [NNReal.coe_natCast, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one] at this
      have e : ((x : ℝ) - 1 / ((N + 1 : ℕ) : ℝ)) * ((N + 1 : ℕ) : ℝ) =
          ((N + 1 : ℕ) : ℝ) * x - 1 := by field_simp
      rw [e]; push_cast at this ⊢; linarith
    have hl : Tendsto (fun N : ℕ => (x : ℝ) - 1 / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 x) := by
      have : Tendsto (fun N : ℕ => 1 / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
        have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        refine this.congr fun N => ?_
        push_cast; ring
      simpa using (tendsto_const_nhds (x := (x : ℝ))).sub this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlow hup
  have h1 : Tendsto (fun N => f (s N)) atTop (𝓝 (f x)) := (hf.tendsto x).comp hs
  have h2 : Tendsto (fun N => f (s N)) atTop (𝓝 (f 1 * x)) := by
    have : (fun N => f (s N)) = fun N => f 1 * ((s N : ℝ≥0) : ℝ) := by
      funext N
      simp only [s]
      rw [hq _ _ (Nat.succ_pos N)]
      simp only [NNReal.coe_div, NNReal.coe_natCast]
      ring
    rw [this]
    exact (continuous_const.mul NNReal.continuous_coe).tendsto x |>.comp hs
  exact tendsto_nhds_unique h1 h2

/-- Integer separation of two non-collinear vectors. -/
lemma int_sep {u1 v1 u2 v2 : ℝ} (hD : u1 * v2 - u2 * v1 ≠ 0) :
    ∃ a1 a2 : ℤ, 0 < a1 * u1 + a2 * v1 ∧ a1 * u2 + a2 * v2 < 0 := by
  set D := u1 * v2 - u2 * v1
  set σ : ℝ := if 0 < D then 1 else -1
  have hσD : σ * D = |D| := by
    simp only [σ]; split_ifs with h
    · rw [abs_of_pos h]; ring
    · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp h) hD)]; ring
  have hDpos : 0 < |D| := abs_pos.mpr hD
  set α1 := σ * (v2 + v1)
  set α2 := -σ * (u2 + u1)
  have e1 : α1 * u1 + α2 * v1 = |D| := by rw [← hσD]; simp only [α1, α2, D]; ring
  have e2 : α1 * u2 + α2 * v2 = -|D| := by rw [← hσD]; simp only [α1, α2, D]; ring
  set S := |u1| + |v1| + |u2| + |v2| + 1
  have hS : 0 < S := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (S / |D|)
  have hND : S < N * |D| := by rwa [div_lt_iff₀ hDpos] at hN
  refine ⟨round (N * α1), round (N * α2), ?_, ?_⟩
  · have r1 := abs_sub_round (N * α1)
    have r2 := abs_sub_round (N * α2)
    have k1 : |(round (N * α1) - N * α1) * u1| ≤ 1 / 2 * |u1| := by
      rw [abs_mul, abs_sub_comm]; exact mul_le_mul_of_nonneg_right r1 (abs_nonneg _)
    have k2 : |(round (N * α2) - N * α2) * v1| ≤ 1 / 2 * |v1| := by
      rw [abs_mul, abs_sub_comm]; exact mul_le_mul_of_nonneg_right r2 (abs_nonneg _)
    have eq : (round (N * α1) : ℝ) * u1 + round (N * α2) * v1 =
        N * (α1 * u1 + α2 * v1) + ((round (N * α1) - N * α1) * u1 +
          (round (N * α2) - N * α2) * v1) := by ring
    rw [eq, e1]
    have := neg_abs_le ((round (N * α1) - N * α1) * u1)
    have := neg_abs_le ((round (N * α2) - N * α2) * v1)
    have := abs_nonneg u2; have := abs_nonneg v2
    nlinarith
  · have r1 := abs_sub_round (N * α1)
    have r2 := abs_sub_round (N * α2)
    have k1 : |(round (N * α1) - N * α1) * u2| ≤ 1 / 2 * |u2| := by
      rw [abs_mul, abs_sub_comm]; exact mul_le_mul_of_nonneg_right r1 (abs_nonneg _)
    have k2 : |(round (N * α2) - N * α2) * v2| ≤ 1 / 2 * |v2| := by
      rw [abs_mul, abs_sub_comm]; exact mul_le_mul_of_nonneg_right r2 (abs_nonneg _)
    have eq : (round (N * α1) : ℝ) * u2 + round (N * α2) * v2 =
        N * (α1 * u2 + α2 * v2) + ((round (N * α1) - N * α1) * u2 +
          (round (N * α2) - N * α2) * v2) := by ring
    rw [eq, e2]
    have := le_abs_self ((round (N * α1) - N * α1) * u2)
    have := le_abs_self ((round (N * α2) - N * α2) * v2)
    have := abs_nonneg u1; have := abs_nonneg v1
    nlinarith

end X5HK

-- ===== module B

noncomputable section
set_option linter.unusedSectionVars false
open scoped NNReal
open Filter Topology HarksKlimm.Consistency

namespace X5HK

lemma mono_exp (K φ B : ℝ) : IsMonotonic (fun x : ℝ≥0 => K * Real.exp (φ * x) + B) := by
  have hm : 0 ≤ φ → Monotone (fun x : ℝ≥0 => Real.exp (φ * x)) := fun hφ x y hxy =>
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast hxy) hφ)
  have ha : φ ≤ 0 → Antitone (fun x : ℝ≥0 => Real.exp (φ * x)) := fun hφ x y hxy =>
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (by exact_mod_cast hxy) hφ)
  rcases le_total 0 K with hK | hK <;> rcases le_total 0 φ with hφ | hφ
  · left; intro x y hxy; have := hm hφ hxy; simp only; nlinarith
  · right; intro x y hxy; have := ha hφ hxy; simp only; nlinarith
  · right; intro x y hxy; have := hm hφ hxy; simp only; nlinarith
  · left; intro x y hxy; have := ha hφ hxy; simp only; nlinarith

lemma mono_aff (s B : ℝ) : IsMonotonic (fun x : ℝ≥0 => s * x + B) := by
  rcases le_total 0 s with hs | hs
  · left; intro x y hxy
    have : (x : ℝ) ≤ y := by exact_mod_cast hxy
    simp only; nlinarith
  · right; intro x y hxy
    have : (x : ℝ) ≤ y := by exact_mod_cast hxy
    simp only; nlinarith

theorem main (C : Set (ℝ≥0 → ℝ)) (hC : ∀ c ∈ C, Continuous c) :
    (∀ h ∈ ShiftHull C, IsMonotonic h) ↔
      ∀ c ∈ C, (∃ φ : ℝ, IsExponential φ c) ∨ IsAffine c := by
  constructor
  swap
  · rintro hR h ⟨a1, a2, c, δ, hc, hδ, hh⟩
    rcases hR c hc with ⟨φ, a, b, hab⟩ | ⟨a, b, hab⟩
    · have : h = fun x : ℝ≥0 => (a * (a1 + a2 * Real.exp (φ * δ))) * Real.exp (φ * x) +
          (a1 + a2) * b := by
        funext x
        rw [hh, hab, hab, NNReal.coe_add,
          show φ * ((x : ℝ) + δ) = φ * x + φ * δ by ring, Real.exp_add]; ring
      rw [this]; exact mono_exp _ _ _
    · have : h = fun x : ℝ≥0 => ((a1 + a2) * a) * x + ((a1 + a2) * b + a2 * a * δ) := by
        funext x
        rw [hh, hab, hab, NNReal.coe_add]; ring
      rw [this]; exact mono_aff _ _
  intro hL c hc
  have hcc := hC c hc
  have hcomb : ∀ (a1 a2 : ℤ) (δ : ℝ≥0), 0 < δ →
      IsMonotonic (fun x => (a1 : ℝ) * c x + (a2 : ℝ) * c (x + δ)) := fun a1 a2 δ hδ =>
    hL _ ⟨a1, a2, c, δ, hc, hδ, fun x => rfl⟩
  -- collinearity of increments
  have hcol_le : ∀ δ : ℝ≥0, 0 < δ → ∀ x1 y1 x2 y2 : ℝ≥0, x1 ≤ y1 → x2 ≤ y2 →
      (c y1 - c x1) * (c (y2 + δ) - c (x2 + δ)) =
        (c y2 - c x2) * (c (y1 + δ) - c (x1 + δ)) := by
    intro δ hδ x1 y1 x2 y2 h1 h2
    by_contra hne
    obtain ⟨a1, a2, hp, hn⟩ := int_sep (sub_ne_zero.mpr hne)
    rcases hcomb a1 a2 δ hδ with hm | ha
    · have := hm h2; simp only at this; nlinarith
    · have := ha h1; simp only at this; nlinarith
  have hcol : ∀ δ : ℝ≥0, 0 < δ → ∀ x1 y1 x2 y2 : ℝ≥0,
      (c y1 - c x1) * (c (y2 + δ) - c (x2 + δ)) =
        (c y2 - c x2) * (c (y1 + δ) - c (x1 + δ)) := by
    intro δ hδ x1 y1 x2 y2
    rcases le_total x1 y1 with h1 | h1 <;> rcases le_total x2 y2 with h2 | h2
    · exact hcol_le δ hδ x1 y1 x2 y2 h1 h2
    · have := hcol_le δ hδ x1 y1 y2 x2 h1 h2; linear_combination -this
    · have := hcol_le δ hδ y1 x1 x2 y2 h1 h2; linear_combination -this
    · have := hcol_le δ hδ y1 x1 y2 x2 h1 h2; linear_combination this
  by_cases hconst : ∀ x, c x = c 0
  · right; exact ⟨0, c 0, fun x => by simp [hconst x]⟩
  push_neg at hconst
  obtain ⟨y0, hy0⟩ := hconst
  have hu0 : c y0 - c 0 ≠ 0 := sub_ne_zero.mpr hy0
  set k : ℝ≥0 → ℝ := fun δ => (c (y0 + δ) - c δ) / (c y0 - c 0) with hkdef
  set g : ℝ≥0 → ℝ := fun x => c x - c 0 with hgdef
  have hgc : Continuous g := hcc.sub continuous_const
  have hg0 : g 0 = 0 := by simp [g]
  have hk0 : k 0 = 1 := by simp only [k, add_zero]; exact div_self hu0
  have hrel : ∀ δ x, g (x + δ) = g δ + k δ * g x := by
    intro δ x
    rcases eq_or_ne δ 0 with rfl | hδ
    · rw [hk0, hg0, add_zero]; ring
    · have := hcol δ (pos_iff_ne_zero.mpr hδ) 0 x 0 y0
      simp only [zero_add] at this
      have key : (c (y0 + δ) - c δ) / (c y0 - c 0) * (c x - c 0) = c (x + δ) - c δ := by
        rw [div_mul_eq_mul_div, div_eq_iff hu0]; linear_combination this
      simp only [g, k]
      linarith
  by_cases hk : ∀ δ, k δ = 1
  · right
    have hadd : ∀ x y, g (x + y) = g x + g y := by
      intro x y; rw [hrel y x, hk y]; ring
    have := cauchy_nn g hgc hadd
    exact ⟨g 1, c 0, fun x => by have := this x; simp only [g] at this ⊢; linarith⟩
  push_neg at hk
  obtain ⟨δ0, hδ0⟩ := hk
  have hk1 : 1 - k δ0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hδ0)
  have hsym : ∀ x, g x * (1 - k δ0) = g δ0 * (1 - k x) := by
    intro x
    have e1 := hrel δ0 x
    have e2 := hrel x δ0
    rw [add_comm] at e2
    linear_combination e1 - e2
  set Cc := g δ0 / (1 - k δ0) with hCc
  have hg : ∀ x, g x = Cc * (1 - k x) := by
    intro x
    have := hsym x
    rw [hCc]; field_simp; linear_combination this
  by_cases hC0 : Cc = 0
  · right
    refine ⟨0, c 0, fun x => ?_⟩
    have := hg x; rw [hC0, zero_mul] at this
    simp only [g] at this; simp; linarith
  left
  have hkf : ∀ x, k x = 1 - g x / Cc := by
    intro x; rw [hg x]; field_simp; ring
  have hkc : Continuous k := by
    have : k = fun x => 1 - g x / Cc := funext hkf
    rw [this]; exact continuous_const.sub (hgc.div_const _)
  have hmul : ∀ x δ, k (x + δ) = k x * k δ := by
    intro x δ
    have e := hrel δ x
    rw [hg, hg, hg] at e
    have : Cc * (k (x + δ) - k x * k δ) = 0 := by linear_combination -e
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hC0
    · linarith
  have hpow : ∀ (n : ℕ) (y : ℝ≥0), k (n * y) = k y ^ n := by
    intro n y
    induction n with
    | zero => simp [hk0]
    | succ m ih => rw [Nat.cast_succ, add_mul, one_mul, hmul, ih, pow_succ]
  have hpos : ∀ x, 0 < k x := by
    intro x
    have hev : ∀ᶠ y in 𝓝 (0 : ℝ≥0), 0 < k y :=
      (hkc.tendsto 0).eventually (lt_mem_nhds (by rw [hk0]; exact one_pos))
    have ht : Tendsto (fun n : ℕ => x / (n : ℝ≥0)) atTop (𝓝 0) := by
      rw [← NNReal.tendsto_coe]
      simpa using tendsto_const_div_atTop_nhds_zero_nat (x : ℝ)
    obtain ⟨n, hn, hn1⟩ := ((ht.eventually hev).and (eventually_ge_atTop 1)).exists
    have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have : x = (n : ℝ≥0) * (x / n) := by field_simp
    rw [this, hpow]
    exact pow_pos hn _
  set L : ℝ≥0 → ℝ := fun x => Real.log (k x)
  have hLc : Continuous L := hkc.log fun x => (hpos x).ne'
  have hLadd : ∀ x y, L (x + y) = L x + L y := by
    intro x y
    simp only [L]; rw [hmul, Real.log_mul (hpos x).ne' (hpos y).ne']
  have hL1 := cauchy_nn L hLc hLadd
  refine ⟨L 1, -Cc, c 0 + Cc, fun x => ?_⟩
  have hkx : k x = Real.exp (L 1 * x) := by
    rw [← hL1 x]; simp only [L]; rw [Real.exp_log (hpos x)]
  have := hg x
  simp only [g] at this
  rw [← hkx]
  linarith

end X5HK

end

set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

theorem solution (C : Set (ℝ≥0 → ℝ))
    (hC : ∀ c ∈ C, Continuous c) :
    (∀ h ∈ ShiftHull C, IsMonotonic h) ↔
      ∀ c ∈ C, (∃ φ : ℝ, IsExponential φ c) ∨ IsAffine c :=
  X5HK.main C hC

