-- Prove2me | solution 1 for GenericBudgets.IdenticalPrefs.theorem_8_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T07:25:16.134933+00:00
-- url     : https://prove2.me/submissions/09451ea3-5bef-4d55-89ce-0edc1a177677

import Mathlib
import Definitions.Def_GenericBudgets_AlmostEqual_Setting

set_option autoImplicit false

namespace GB81

open GenericBudgets.AlmostEqual

lemma fin2_eq (a b : Fin 2) (h : a = 0 ↔ b = 0) : a = b := by
  revert a b; decide

lemma fin2_one (a : Fin 2) : a = 1 ↔ ¬ a = 0 := by
  revert a; decide

lemma bundle_one_eq {m : ℕ} (σ : Fin m → Fin 2) : bundle σ 1 = (bundle σ 0)ᶜ := by
  ext j
  simp only [bundle, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
  exact fin2_one (σ j)

lemma w_compl {m : ℕ} {w : Finset (Fin m) → ℝ} (hw : IsStandardValuation w)
    (S : Finset (Fin m)) : w Sᶜ = 1 - w S := by
  have h := Finset.sum_add_sum_compl S (fun j => w {j})
  have h1 := hw.normalized
  rw [hw.additive] at h1
  rw [hw.additive Sᶜ, hw.additive S]
  linarith

lemma w_le_one {m : ℕ} {w : Finset (Fin m) → ℝ} (hw : IsStandardValuation w)
    (S : Finset (Fin m)) : w S ≤ 1 := by
  have := w_compl hw S
  have := hw.nonneg Sᶜ
  linarith

lemma price_smul {m : ℕ} {w : Finset (Fin m) → ℝ} (hw : IsStandardValuation w) (c : ℝ)
    (S : Finset (Fin m)) : price (fun j => c * w {j}) S = c * w S := by
  unfold price
  rw [← Finset.mul_sum, ← hw.additive]

def alloc {m : ℕ} (S : Finset (Fin m)) : Fin m → Fin 2 := fun j => if j ∈ S then 0 else 1

lemma bundle_alloc {m : ℕ} (S : Finset (Fin m)) : bundle (alloc S) 0 = S := by
  ext j
  by_cases h : j ∈ S <;> simp [bundle, alloc, h]

lemma allPO {m : ℕ} (v : Fin 2 → Finset (Fin m) → ℝ) (hw : IsStandardValuation (v 0))
    (h1 : v 1 = v 0) (σ : Fin m → Fin 2) : IsPO v σ := by
  intro σ' hne
  have hb : bundle σ' 0 ≠ bundle σ 0 := by
    intro h; apply hne; funext j
    apply fin2_eq
    have := Finset.ext_iff.mp h j
    simpa [bundle] using this
  have hne' : v 0 (bundle σ' 0) ≠ v 0 (bundle σ 0) := fun h => hb (hw.strict h)
  rcases lt_or_gt_of_ne hne' with h | h
  · exact ⟨0, h⟩
  · refine ⟨1, ?_⟩
    rw [h1, bundle_one_eq, bundle_one_eq, w_compl hw, w_compl hw]
    linarith

theorem main {m : ℕ} (v : Fin 2 → Finset (Fin m) → ℝ)
    (hv : ∀ i, IsStandardValuation (v i)) (hsame : v 0 = v 1)
    (b : Fin 2 → ℝ) (hb : ∀ i, 0 < b i) (hsum : b 0 + b 1 = 1) (hlt : b 1 < b 0)
    (hR : ∃ i, ¬ InR v b i) :
    ∃ (σ : Fin m → Fin 2) (p : Fin m → ℝ), IsCE v b σ p ∧ ∀ i, GetsTruncatedShare v b σ i := by
  classical
  have hw := hv 0
  have h1 : v 1 = v 0 := hsame.symm
  have hb0 := hb 0
  have hb1 := hb 1
  have hc : ∀ σ : Fin m → Fin 2, v 1 (bundle σ 1) = 1 - v 0 (bundle σ 0) := by
    intro σ; rw [h1, bundle_one_eq, w_compl hw]
  -- agent 1's exceptional set equals agent 0's
  have hR0 : ¬ InR v b 0 := by
    obtain ⟨i, hi⟩ := hR
    by_cases hi0 : i = 0
    · subst hi0; exact hi
    · have hi1 : i = 1 := (fin2_one i).mpr hi0
      subst hi1
      intro h0; apply hi
      obtain ⟨σ, σ', hPσ, hPσ', hlt', hbet, heq⟩ := h0
      refine ⟨σ', σ, hPσ', hPσ, ?_, ?_, ?_⟩
      · rw [hc, hc]; linarith
      · intro τ hτ hh
        simp only [hc] at hh
        exact hbet τ hτ ⟨by linarith [hh.2], by linarith [hh.1]⟩
      · rw [hc, hc, show (1:ℝ) - b 1 = b 0 by linarith]
        rw [show (1:ℝ) - b 0 = b 1 by linarith] at heq
        linear_combination -heq
  obtain ⟨f, hf⟩ : ∃ f : (Fin m → Fin 2) → ℝ, ∀ σ, f σ = v 0 (bundle σ 0) := ⟨_, fun _ => rfl⟩
  have hf1 : ∀ σ, f σ ≤ 1 := fun σ => by rw [hf]; exact w_le_one hw _
  have hf0 : ∀ σ, 0 ≤ f σ := fun σ => by rw [hf]; exact hw.nonneg _
  have hconst : f (fun _ => 0) = 1 := by
    rw [hf]
    have : bundle (fun _ : Fin m => (0 : Fin 2)) 0 = Finset.univ := by ext j; simp [bundle]
    rw [this, hw.normalized]
  obtain ⟨σs, hσs_mem, hσs_min⟩ := Finset.exists_min_image
    (Finset.univ.filter (fun σ => ∀ τ, f σ < f τ → b 0 * (1 - f σ) < b 1 * f τ)) f
    ⟨fun _ => 0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun τ h => by
      rw [hconst] at h; linarith [hf1 τ]⟩⟩
  have hPs : ∀ τ, f σs < f τ → b 0 * (1 - f σs) < b 1 * f τ := (Finset.mem_filter.mp hσs_mem).2
  have hQ : ∀ τ, f τ < f σs → b 1 * f σs < b 0 * (1 - f τ) := by
    intro τ0 hτ0
    obtain ⟨ρ, hρ_mem, hρ_max⟩ := Finset.exists_max_image
      (Finset.univ.filter (fun τ => f τ < f σs)) f
      ⟨τ0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hτ0⟩⟩
    have hρlt : f ρ < f σs := (Finset.mem_filter.mp hρ_mem).2
    have hτ0ρ : f τ0 ≤ f ρ := hρ_max τ0 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hτ0⟩)
    have hnP : ∃ τ', f ρ < f τ' ∧ b 1 * f τ' ≤ b 0 * (1 - f ρ) := by
      by_contra hcon
      push Not at hcon
      have := hσs_min ρ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩)
      linarith
    obtain ⟨τ', hρτ', hle⟩ := hnP
    have hτ'ge : f σs ≤ f τ' := by
      by_contra hcon
      push Not at hcon
      have := hρ_max τ' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩)
      linarith
    have hge : b 1 * f σs ≤ b 0 * (1 - f ρ) := by
      have := mul_le_mul_of_nonneg_left hτ'ge hb1.le
      linarith
    rcases lt_or_eq_of_le hge with h | h
    · have := mul_le_mul_of_nonneg_left hτ0ρ hb0.le
      linarith
    · exfalso; apply hR0
      refine ⟨ρ, σs, allPO v hw h1 ρ, allPO v hw h1 σs, ?_, ?_, ?_⟩
      · rw [← hf, ← hf]; exact hρlt
      · intro τ _ hh
        rw [← hf, ← hf, ← hf] at hh
        have := hρ_max τ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh.2⟩)
        linarith [hh.1]
      · rw [← hf, ← hf, show (1:ℝ) - b 0 = b 1 by linarith]
        linarith
  -- Finset-level consequences
  set x := f σs with hxdef
  have hx : v 0 (bundle σs 0) = x := (hf σs).symm
  have hP' : ∀ T : Finset (Fin m), x < v 0 T → b 0 * (1 - x) < b 1 * v 0 T := by
    intro T hT
    have := hPs (alloc T) (by rw [hf, bundle_alloc]; exact hT)
    rw [hf, bundle_alloc] at this
    exact this
  have hQ' : ∀ T : Finset (Fin m), 1 - x < v 0 T → b 1 * x < b 0 * v 0 T := by
    intro T hT
    have hlt2 : f (alloc Tᶜ) < x := by rw [hf, bundle_alloc, w_compl hw]; linarith
    have := hQ (alloc Tᶜ) hlt2
    rw [hf, bundle_alloc, w_compl hw] at this
    linarith
  have hx0 : 0 < x := by
    by_contra hcon
    push Not at hcon
    have hxz : x = 0 := le_antisymm hcon (hf0 _)
    have := hPs (fun _ => 0) (by rw [hconst, hxz]; norm_num)
    rw [hconst, hxz] at this
    linarith
  have hx1 : x ≤ 1 := hf1 _
  -- the price scale
  obtain ⟨c, hc0, hcx, hcy, hcT0, hcT1⟩ : ∃ c : ℝ, 0 ≤ c ∧ c * x ≤ b 0 ∧ c * (1 - x) ≤ b 1 ∧
      (∀ T : Finset (Fin m), x < v 0 T → b 0 < c * v 0 T) ∧
      (∀ T : Finset (Fin m), 1 - x < v 0 T → b 1 < c * v 0 T) := by
    rcases lt_or_eq_of_le hx1 with hxl | hxe
    · have h1x : 0 < 1 - x := by linarith
      refine ⟨min (b 0 / x) (b 1 / (1 - x)), le_min (div_nonneg hb0.le hx0.le)
        (div_nonneg hb1.le h1x.le), ?_, ?_, ?_, ?_⟩
      · exact (le_div_iff₀ hx0).mp (min_le_left _ _)
      · exact (le_div_iff₀ h1x).mp (min_le_right _ _)
      · intro T hT
        have hwT : 0 < v 0 T := by linarith
        apply (div_lt_iff₀ hwT).mp
        apply lt_min
        · rw [div_lt_div_iff₀ hwT hx0]
          exact mul_lt_mul_of_pos_left hT hb0
        · rw [div_lt_div_iff₀ hwT h1x]
          exact hP' T hT
      · intro T hT
        have hwT : 0 < v 0 T := by linarith
        apply (div_lt_iff₀ hwT).mp
        apply lt_min
        · rw [div_lt_div_iff₀ hwT hx0]
          exact hQ' T hT
        · rw [div_lt_div_iff₀ hwT h1x]
          exact mul_lt_mul_of_pos_left hT hb1
    · refine ⟨b 0, hb0.le, by rw [hxe]; linarith, by rw [hxe]; linarith, ?_, ?_⟩
      · intro T hT
        have := w_le_one hw T
        linarith
      · intro T hT
        have := hQ' T hT
        rw [hxe] at this
        linarith
  refine ⟨σs, fun j => c * v 0 {j}, ⟨fun j => mul_nonneg hc0 (hw.nonneg _), ?_⟩, ?_⟩
  · rw [Fin.forall_fin_two]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [price_smul hw, hx]; exact hcx
    · intro T hT
      rw [price_smul hw]
      rw [hx] at hT
      exact hcT0 T hT
    · rw [h1, bundle_one_eq]
      refine ⟨?_, ?_⟩
      · rw [price_smul hw, w_compl hw, hx]; exact hcy
      · intro T hT
        rw [price_smul hw]
        rw [w_compl hw, hx] at hT
        exact hcT1 T hT
  · rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · intro σ' _ hle
      rw [hx]
      by_contra hgt
      push Not at hgt
      have h2 := hP' _ hgt
      have h3 := mul_le_mul_of_nonneg_left hle hb1.le
      have h4 : b 0 * (1 - x) < b 0 * b 1 := by linarith
      have h5 := lt_of_mul_lt_mul_left h4 hb0.le
      linarith
    · intro σ' _ hle
      rw [h1] at hle ⊢
      rw [bundle_one_eq σs, w_compl hw, hx]
      by_contra hgt
      push Not at hgt
      have h2 := hQ' _ hgt
      have h3 := mul_le_mul_of_nonneg_left hle hb0.le
      have h4 : b 1 * x < b 1 * b 0 := by linarith
      have h5 := lt_of_mul_lt_mul_left h4 hb1.le
      linarith

end GB81

open GenericBudgets.AlmostEqual in
theorem solution {m : ℕ} (v : Fin 2 → Finset (Fin m) → ℝ)
    (hv : ∀ i, GenericBudgets.AlmostEqual.IsStandardValuation (v i)) (hsame : v 0 = v 1)
    (b : Fin 2 → ℝ) (hb : ∀ i, 0 < b i) (hsum : b 0 + b 1 = 1) (hlt : b 1 < b 0)
    (hR : ∃ i, ¬ GenericBudgets.AlmostEqual.InR v b i) :
    ∃ (σ : Fin m → Fin 2) (p : Fin m → ℝ), GenericBudgets.AlmostEqual.IsCE v b σ p ∧ ∀ i, GenericBudgets.AlmostEqual.GetsTruncatedShare v b σ i := by
  exact GB81.main v hv hsame b hb hsum hlt hR
