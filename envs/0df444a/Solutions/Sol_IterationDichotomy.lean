-- Prove2me | solution 1 for IterationDichotomy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:14:42.60673+00:00
-- url     : https://prove2.me/submissions/25ce51dd-d78e-4dc1-b77a-1ab87365b6af

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_IterationDichotomy

set_option autoImplicit false

theorem _root_.solution (σ δ θ : ℝ) (hσ : 1 < σ) (hδ : 0 < δ) (hθ0 : 0 < θ)
    (v : Plane → ℝ) (R : ℕ → ℝ) (hR0 : R 0 = 1) (hRpos : ∀ l : ℕ, 0 < R l)
    (hGood : ∀ (l : ℕ) (y : Plane), ‖y‖ < R l → |v y| ≤ R l ^ σ)
    (hsand : ∀ l : ℕ, R l ^ (1 - σ) * ‖gradient v 0‖ ≤ δ →
        θ * R l ≤ R (l + 1) ∧ R (l + 1) ≤ R l / 4) :
    ((∀ l : ℕ, R l ^ (1 - σ) * ‖gradient v 0‖ ≤ δ) ↔ gradient v 0 = 0)
      ∧ ((∀ l : ℕ, R l ^ (1 - σ) * ‖gradient v 0‖ ≤ δ) →
          Filter.Tendsto R Filter.atTop (nhds 0)
            ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ y : Plane, ‖y‖ < r → |v y| ≤ θ ^ (-σ) * r ^ σ)
      ∧ (gradient v 0 ≠ 0 →
          ∃ L : ℕ, ¬ (R L ^ (1 - σ) * ‖gradient v 0‖ ≤ δ)
            ∧ ∀ l < L, R l ^ (1 - σ) * ‖gradient v 0‖ ≤ δ) := by
  classical
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hσ1 : (0 : ℝ) < σ - 1 := by linarith
  -- STEP 1:  under full continuation the radii decay geometrically, hence to `0`.
  have hgeo : (∀ l : ℕ, R l ^ (1 - σ) * ‖gradient v 0‖ ≤ δ) →
      Filter.Tendsto R Filter.atTop (nhds 0) := by
    intro hcont
    have hquart : ∀ l : ℕ, R l ≤ (1 / 4 : ℝ) ^ l := by
      intro l
      induction l with
      | zero => rw [hR0]; norm_num
      | succ n ih =>
        have h := (hsand n (hcont n)).2
        calc R (n + 1) ≤ R n / 4 := h
          _ ≤ (1 / 4 : ℝ) ^ n / 4 := by linarith
          _ = (1 / 4 : ℝ) ^ (n + 1) := by ring
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun _ : ℕ => (0 : ℝ)) (h := fun l : ℕ => (1 / 4 : ℝ) ^ l)
      tendsto_const_nhds
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
      (fun l => le_of_lt (hRpos l)) hquart
  -- STEP 2:  conclusion (1).
  have hback : gradient v 0 = 0 → ∀ l : ℕ, R l ^ (1 - σ) * ‖gradient v 0‖ ≤ δ := by
    intro h0 l
    rw [h0, norm_zero, mul_zero]
    exact le_of_lt hδ
  have hfwd : (∀ l : ℕ, R l ^ (1 - σ) * ‖gradient v 0‖ ≤ δ) → gradient v 0 = 0 := by
    intro hcont
    by_contra hne
    have hc : 0 < ‖gradient v 0‖ := norm_pos_iff.mpr hne
    have hinv : ∀ l : ℕ, R l ^ (1 - σ) = (R l ^ (σ - 1))⁻¹ := by
      intro l
      rw [show (1 - σ) = -(σ - 1) by ring, Real.rpow_neg (le_of_lt (hRpos l))]
    have hkey : ∀ l : ℕ, ‖gradient v 0‖ / δ ≤ R l ^ (σ - 1) := by
      intro l
      have hp : 0 < R l ^ (σ - 1) := Real.rpow_pos_of_pos (hRpos l) _
      have h := hcont l
      rw [hinv l, inv_mul_eq_div, div_le_iff₀ hp] at h
      rw [div_le_iff₀ hδ]
      linarith
    have htend : Filter.Tendsto (fun l => R l ^ (σ - 1)) Filter.atTop (nhds 0) := by
      have h := (hgeo hcont).rpow_const (Or.inr (le_of_lt hσ1))
      rwa [Real.zero_rpow (ne_of_gt hσ1)] at h
    obtain ⟨l, hl⟩ :=
      (Filter.Tendsto.eventually_lt_const (div_pos hc hδ) htend).exists
    exact absurd (hkey l) (not_le.mpr hl)
  refine ⟨⟨hfwd, hback⟩, ?_, ?_⟩
  · -- STEP 3:  conclusion (2).
    intro hcont
    refine ⟨hgeo hcont, ?_⟩
    intro r hr0 hr1 y hy
    -- bracket `r` between consecutive radii;  `R` is not assumed monotone
    have hev : ∀ᶠ l in Filter.atTop, R l < r :=
      Filter.Tendsto.eventually_lt_const hr0 (hgeo hcont)
    obtain ⟨Nn, hNn⟩ := Filter.eventually_atTop.mp hev
    obtain ⟨ℓ, hℓdef⟩ : ∃ m : ℕ, m = Nat.findGreatest (fun l => r ≤ R l) Nn := ⟨_, rfl⟩
    have hP0 : r ≤ R 0 := by rw [hR0]; exact hr1
    have hℓP : r ≤ R ℓ := by
      rw [hℓdef]
      exact Nat.findGreatest_spec (P := fun l => r ≤ R l) (Nat.zero_le Nn) hP0
    have hnext : R (ℓ + 1) < r := by
      by_cases hle : ℓ + 1 ≤ Nn
      · have hgr := Nat.findGreatest_is_greatest (k := ℓ + 1) (P := fun l => r ≤ R l) (n := Nn)
          (by rw [← hℓdef]; omega) hle
        exact not_le.mp hgr
      · exact hNn (ℓ + 1) (by omega)
    have hgood : |v y| ≤ R ℓ ^ σ := hGood ℓ y (lt_of_lt_of_le hy hℓP)
    have hRlt : R ℓ < r * θ⁻¹ := by
      have h2 : θ * R ℓ < r := lt_of_le_of_lt (hsand ℓ (hcont ℓ)).1 hnext
      rw [← div_eq_mul_inv]
      exact (lt_div_iff₀' hθ0).mpr h2
    calc |v y| ≤ R ℓ ^ σ := hgood
      _ ≤ (r * θ⁻¹) ^ σ :=
          Real.rpow_le_rpow (le_of_lt (hRpos ℓ)) (le_of_lt hRlt) (le_of_lt hσ0)
      _ = r ^ σ * (θ⁻¹) ^ σ :=
          Real.mul_rpow (le_of_lt hr0) (le_of_lt (inv_pos.mpr hθ0))
      _ = r ^ σ * (θ ^ σ)⁻¹ := by rw [Real.inv_rpow (le_of_lt hθ0)]
      _ = θ ^ (-σ) * r ^ σ := by rw [← Real.rpow_neg (le_of_lt hθ0)]; ring
  · -- STEP 4:  conclusion (3), the LEAST failing index.
    intro hne
    have hex : ∃ l : ℕ, ¬ (R l ^ (1 - σ) * ‖gradient v 0‖ ≤ δ) :=
      not_forall.mp (fun h => hne (hfwd h))
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    intro l hl
    exact not_not.mp (Nat.find_min hex hl)
