-- Prove2me | solution 1 for NashBargainingProblem.Axiomatic.nash_axioms_force_nash_product_max
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T17:27:16.287337+00:00
-- url     : https://prove2.me/submissions/03fc248f-635d-4aef-94b2-936ea413a64b

import Mathlib
import Theorems.Thm_NashBargainingProblem_Axiomatic_nash_product_maximizer_exists_unique
import Theorems.Thm_NashBargainingProblem_Axiomatic_sum_le_two_of_one_one_max
import Theorems.Thm_NashBargainingProblem_Axiomatic_exists_enclosing_square
import Theorems.Thm_NashBargainingProblem_Axiomatic_square_unique_symmetric_undominated

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NashWork

def Qh (h : ℝ) : Set (ℝ × ℝ) := {u | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h}

theorem nash_product_maximizer_exists_unique (S : Set (ℝ × ℝ))
    (hS_compact : IsCompact S) (hS_convex : Convex ℝ S) (hS_zero : ((0 : ℝ), (0 : ℝ)) ∈ S)
    (hS_gain : ∃ s ∈ S, 0 < s.1 ∧ 0 < s.2) :
    ∃! p : ℝ × ℝ, p ∈ S ∧ 0 < p.1 ∧ 0 < p.2 ∧
      ∀ s ∈ S, 0 ≤ s.1 → 0 ≤ s.2 → s ≠ p → s.1 * s.2 < p.1 * p.2 :=
  NashBargainingProblem.Axiomatic.nash_product_maximizer_exists_unique S hS_compact hS_convex hS_zero hS_gain

theorem sum_le_two_of_one_one_max (S : Set (ℝ × ℝ))
    (hS_convex : Convex ℝ S) (h11 : ((1 : ℝ), (1 : ℝ)) ∈ S)
    (hmax : ∀ s ∈ S, 0 ≤ s.1 → 0 ≤ s.2 → s.1 * s.2 ≤ 1) :
    ∀ u ∈ S, u.1 + u.2 ≤ 2 :=
  NashBargainingProblem.Axiomatic.sum_le_two_of_one_one_max S hS_convex h11 hmax

theorem exists_enclosing_square (S : Set (ℝ × ℝ))
    (hS_compact : IsCompact S) (hS_le : ∀ u ∈ S, u.1 + u.2 ≤ 2) :
    ∃ h : ℝ, 0 < h ∧
      S ⊆ {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h} ∧
      IsCompact {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h} ∧
      Convex ℝ {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h} ∧
      (∀ a b : ℝ,
        (a, b) ∈ {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h} ↔
        (b, a) ∈ {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h}) :=
  NashBargainingProblem.Axiomatic.exists_enclosing_square S hS_compact hS_le

theorem square_unique_symmetric_undominated (h : ℝ) (hh : 0 < h) (p : ℝ × ℝ)
    (hp : p ∈ {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h}) :
    (p.1 = p.2 ∧
      ∀ t ∈ {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h},
        ¬ (p.1 < t.1 ∧ p.2 < t.2)) ↔ p = ((1 : ℝ), (1 : ℝ)) :=
  NashBargainingProblem.Axiomatic.square_unique_symmetric_undominated h hh p hp

def BSet : Set (Set (ℝ × ℝ) × (ℝ × ℝ)) :=
  {P | IsCompact P.1 ∧ Convex ℝ P.1 ∧ P.2 ∈ P.1 ∧ ∃ s ∈ P.1, P.2.1 < s.1 ∧ P.2.2 < s.2}

theorem affine_mem_BSet {S : Set (ℝ × ℝ)} {d : ℝ × ℝ} (h : (S, d) ∈ BSet)
    (α₁ α₂ β₁ β₂ : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (L : ℝ × ℝ → ℝ × ℝ)
    (hL : ∀ s : ℝ × ℝ, L s = (α₁ * s.1 + β₁, α₂ * s.2 + β₂)) : (L '' S, L d) ∈ BSet := by
  obtain ⟨hc, hv, hd, s0, hs0, hs0a, hs0b⟩ := h
  have hLc : Continuous L := by
    have : L = fun s => (α₁ * s.1 + β₁, α₂ * s.2 + β₂) := funext hL
    rw [this]; fun_prop
  refine ⟨hc.image hLc, ?_, ⟨d, hd, rfl⟩, ⟨L s0, ⟨s0, hs0, rfl⟩, ?_, ?_⟩⟩
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv', rfl⟩ a b ha hb hab
    refine ⟨a • u + b • v, hv hu hv' ha hb hab, ?_⟩
    rw [hL, hL, hL]
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; linear_combination (-β₁) * hab
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; linear_combination (-β₂) * hab
  · rw [hL, hL]; simp only; nlinarith
  · rw [hL, hL]; simp only; nlinarith

theorem nash_axioms_force_nash_product_max
    (B : Set (Set (ℝ × ℝ) × (ℝ × ℝ)))
    (hB : B = {P | IsCompact P.1 ∧ Convex ℝ P.1 ∧ P.2 ∈ P.1 ∧
      ∃ s ∈ P.1, P.2.1 < s.1 ∧ P.2.2 < s.2})
    (g : B → ℝ × ℝ)
    -- g is a bargaining solution: it selects a point of S
    (h_sel : ∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B), g ⟨(S, d), h⟩ ∈ S)
    -- INV: invariance under positive affine rescalings of the two utilities
    (h_inv : ∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B)
            (α₁ α₂ β₁ β₂ : ℝ) (L : ℝ × ℝ → ℝ × ℝ), 0 < α₁ → 0 < α₂ →
            (∀ s : ℝ × ℝ, L s = (α₁ * s.1 + β₁, α₂ * s.2 + β₂)) →
            ∀ h' : (L '' S, L d) ∈ B, g ⟨(L '' S, L d), h'⟩ = L (g ⟨(S, d), h⟩))
    -- SYM: symmetric problems get symmetric outcomes
    (h_sym : ∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B), d.1 = d.2 →
            (∀ s₁ s₂ : ℝ, (s₁, s₂) ∈ S ↔ (s₂, s₁) ∈ S) →
            (g ⟨(S, d), h⟩).1 = (g ⟨(S, d), h⟩).2)
    -- IIA: independence of irrelevant alternatives
    (h_iia : ∀ (S T : Set (ℝ × ℝ)) (d : ℝ × ℝ) (hS : (S, d) ∈ B) (hT : (T, d) ∈ B),
            S ⊆ T → g ⟨(T, d), hT⟩ ∈ S → g ⟨(S, d), hS⟩ = g ⟨(T, d), hT⟩)
    -- PAR: Pareto efficiency (a point of S strictly improved upon by some t ∈ S is never chosen)
    (h_par : ∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B), ∀ s ∈ S, ∀ t ∈ S,
            s.1 < t.1 → s.2 < t.2 → g ⟨(S, d), h⟩ ≠ s) :
    ∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B),
      d.1 ≤ (g ⟨(S, d), h⟩).1 ∧ d.2 ≤ (g ⟨(S, d), h⟩).2 ∧
      ∀ s ∈ S, d.1 ≤ s.1 → d.2 ≤ s.2 → s ≠ g ⟨(S, d), h⟩ →
        (s.1 - d.1) * (s.2 - d.2) <
          ((g ⟨(S, d), h⟩).1 - d.1) * ((g ⟨(S, d), h⟩).2 - d.2) := by
  have hB' : B = BSet := hB
  subst hB'
  intro S d h
  -- Step 1: translate the disagreement point to the origin.
  obtain ⟨L1, hL1⟩ : ∃ L : ℝ × ℝ → ℝ × ℝ,
      ∀ s, L s = (1 * s.1 + (-d.1), 1 * s.2 + (-d.2)) := ⟨_, fun _ => rfl⟩
  have hB1 : (L1 '' S, L1 d) ∈ BSet :=
    affine_mem_BSet h 1 1 (-d.1) (-d.2) one_pos one_pos L1 hL1
  have hinv1 := h_inv S d h 1 1 (-d.1) (-d.2) L1 one_pos one_pos hL1 hB1
  have hd0 : L1 d = ((0 : ℝ), (0 : ℝ)) := by rw [hL1]; ext <;> simp
  have hL1inj : ∀ x y, L1 x = L1 y → x = y := by
    intro x y hxy
    rw [hL1, hL1] at hxy
    simp only [Prod.mk.injEq] at hxy
    exact Prod.ext (by linarith [hxy.1]) (by linarith [hxy.2])
  obtain ⟨hc1, hv1, hd1, s1, hs1, hs1a, hs1b⟩ := hB1
  have hd1' : ((0 : ℝ), (0 : ℝ)) ∈ L1 '' S := hd0 ▸ hd1
  have hs1a' : 0 < s1.1 := by simpa [hd0] using hs1a
  have hs1b' : 0 < s1.2 := by simpa [hd0] using hs1b
  -- Step 2: the Nash point p of the translated problem, and its rescaling to (1, 1).
  obtain ⟨p, ⟨hpS, hp1, hp2, hpmax⟩, -⟩ :=
    nash_product_maximizer_exists_unique (L1 '' S) hc1 hv1 hd1' ⟨s1, hs1, hs1a', hs1b'⟩
  have hB1 : (L1 '' S, L1 d) ∈ BSet := ⟨hc1, hv1, hd1, s1, hs1, hs1a, hs1b⟩
  set α₁ : ℝ := 1 / p.1 with hα₁def
  set α₂ : ℝ := 1 / p.2 with hα₂def
  have hα₁ : 0 < α₁ := by positivity
  have hα₂ : 0 < α₂ := by positivity
  obtain ⟨L2, hL2⟩ : ∃ L : ℝ × ℝ → ℝ × ℝ, ∀ s, L s = (α₁ * s.1 + 0, α₂ * s.2 + 0) :=
    ⟨_, fun _ => rfl⟩
  have hB2 : (L2 '' (L1 '' S), L2 (L1 d)) ∈ BSet :=
    affine_mem_BSet hB1 α₁ α₂ 0 0 hα₁ hα₂ L2 hL2
  have hinv2 := h_inv (L1 '' S) (L1 d) hB1 α₁ α₂ 0 0 L2 hα₁ hα₂ hL2 hB2
  have hL2inj : ∀ x y, L2 x = L2 y → x = y := by
    intro x y hxy
    rw [hL2, hL2] at hxy
    simp only [Prod.mk.injEq] at hxy
    exact Prod.ext (by nlinarith [hxy.1]) (by nlinarith [hxy.2])
  have e1 : α₁ * p.1 = 1 := by simp only [hα₁def]; field_simp
  have e2 : α₂ * p.2 = 1 := by simp only [hα₂def]; field_simp
  have hLp : L2 p = ((1 : ℝ), (1 : ℝ)) := by rw [hL2, e1, e2]; simp
  have h11 : ((1 : ℝ), (1 : ℝ)) ∈ L2 '' (L1 '' S) := by
    rw [← hLp]; exact ⟨p, hpS, rfl⟩
  have hmax2 : ∀ s ∈ L2 '' (L1 '' S), 0 ≤ s.1 → 0 ≤ s.2 → s.1 * s.2 ≤ 1 := by
    intro s hs h1 h2
    by_cases hs11 : s = ((1 : ℝ), (1 : ℝ))
    · subst hs11; simp
    · obtain ⟨u, hu, rfl⟩ := hs
      rw [hL2] at h1 h2 ⊢
      simp only at h1 h2 ⊢
      have hu1 : 0 ≤ u.1 := by nlinarith
      have hu2 : 0 ≤ u.2 := by nlinarith
      have hup : u ≠ p := fun h' => hs11 (by rw [h', hL2, e1, e2]; simp)
      have := hpmax u hu hu1 hu2 hup
      have hpos : 0 < α₁ * α₂ := mul_pos hα₁ hα₂
      nlinarith [mul_pos hα₁ hα₂]
  -- Step 3: the set lies under the line u₁ + u₂ = 2, hence in a symmetric square.
  obtain ⟨hc2, hv2, hd2, s2, hs2, hs2a, hs2b⟩ := hB2
  have hB2 : (L2 '' (L1 '' S), L2 (L1 d)) ∈ BSet := ⟨hc2, hv2, hd2, s2, hs2, hs2a, hs2b⟩
  have hsum := sum_le_two_of_one_one_max _ hv2 h11 hmax2
  obtain ⟨hh0, hhpos, hsub, hcomp, hconv, hsymm⟩ := exists_enclosing_square _ hc2 hsum
  have hD2z : L2 (L1 d) = ((0 : ℝ), (0 : ℝ)) := by rw [hd0, hL2]; simp
  have hD2Q : L2 (L1 d) ∈ Qh hh0 := hsub hd2
  have h11Q : ((1 : ℝ), (1 : ℝ)) ∈ Qh hh0 := hsub h11
  have hBQ : (Qh hh0, L2 (L1 d)) ∈ BSet :=
    ⟨hcomp, hconv, hD2Q, (1, 1), h11Q, by rw [hD2z]; norm_num, by rw [hD2z]; norm_num⟩
  -- Step 4: the axioms pin the solution of the square at (1, 1).
  have hq_sel := h_sel (Qh hh0) (L2 (L1 d)) hBQ
  have hq_sym := h_sym (Qh hh0) (L2 (L1 d)) hBQ (by rw [hD2z]) hsymm
  have hq_und : ∀ t ∈ Qh hh0, ¬ ((g ⟨(Qh hh0, L2 (L1 d)), hBQ⟩).1 < t.1 ∧
      (g ⟨(Qh hh0, L2 (L1 d)), hBQ⟩).2 < t.2) := fun t ht ⟨a, b⟩ =>
    h_par (Qh hh0) (L2 (L1 d)) hBQ _ hq_sel t ht a b rfl
  have hq11 : g ⟨(Qh hh0, L2 (L1 d)), hBQ⟩ = ((1 : ℝ), (1 : ℝ)) :=
    (square_unique_symmetric_undominated hh0 hhpos _ hq_sel).1 ⟨hq_sym, hq_und⟩
  have hiia := h_iia (L2 '' (L1 '' S)) (Qh hh0) (L2 (L1 d)) hB2 hBQ hsub (hq11 ▸ h11)
  rw [hq11] at hiia
  -- Step 5: undo the rescaling and the translation.
  rw [hinv2] at hiia
  have hg1 : g ⟨(L1 '' S, L1 d), hB1⟩ = p := hL2inj _ _ (by rw [hiia, hLp])
  rw [hinv1] at hg1
  have hP : L1 (g ⟨(S, d), h⟩) = p := hg1
  have hP1 := congrArg Prod.fst hP
  have hP2 := congrArg Prod.snd hP
  rw [hL1] at hP1 hP2
  simp only at hP1 hP2
  refine ⟨by linarith, by linarith, ?_⟩
  intro s hs hs1' hs2' hne
  have hne' : L1 s ≠ p := fun h' => hne (hL1inj _ _ (h'.trans hP.symm))
  have := hpmax (L1 s) ⟨s, hs, rfl⟩ (by rw [hL1]; simp only; linarith)
    (by rw [hL1]; simp only; linarith) hne'
  rw [hL1] at this
  simp only at this
  nlinarith

end NashWork

theorem solution
    (B : Set (Set (ℝ × ℝ) × (ℝ × ℝ)))
    (hB : B = {P | IsCompact P.1 ∧ Convex ℝ P.1 ∧ P.2 ∈ P.1 ∧
      ∃ s ∈ P.1, P.2.1 < s.1 ∧ P.2.2 < s.2})
    (g : B → ℝ × ℝ)
    -- g is a bargaining solution: it selects a point of S
    (h_sel : ∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B), g ⟨(S, d), h⟩ ∈ S)
    -- INV: invariance under positive affine rescalings of the two utilities
    (h_inv : ∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B)
            (α₁ α₂ β₁ β₂ : ℝ) (L : ℝ × ℝ → ℝ × ℝ), 0 < α₁ → 0 < α₂ →
            (∀ s : ℝ × ℝ, L s = (α₁ * s.1 + β₁, α₂ * s.2 + β₂)) →
            ∀ h' : (L '' S, L d) ∈ B, g ⟨(L '' S, L d), h'⟩ = L (g ⟨(S, d), h⟩))
    -- SYM: symmetric problems get symmetric outcomes
    (h_sym : ∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B), d.1 = d.2 →
            (∀ s₁ s₂ : ℝ, (s₁, s₂) ∈ S ↔ (s₂, s₁) ∈ S) →
            (g ⟨(S, d), h⟩).1 = (g ⟨(S, d), h⟩).2)
    -- IIA: independence of irrelevant alternatives
    (h_iia : ∀ (S T : Set (ℝ × ℝ)) (d : ℝ × ℝ) (hS : (S, d) ∈ B) (hT : (T, d) ∈ B),
            S ⊆ T → g ⟨(T, d), hT⟩ ∈ S → g ⟨(S, d), hS⟩ = g ⟨(T, d), hT⟩)
    -- PAR: Pareto efficiency (a point of S strictly improved upon by some t ∈ S is never chosen)
    (h_par : ∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B), ∀ s ∈ S, ∀ t ∈ S,
            s.1 < t.1 → s.2 < t.2 → g ⟨(S, d), h⟩ ≠ s) :
    ∀ (S : Set (ℝ × ℝ)) (d : ℝ × ℝ) (h : (S, d) ∈ B),
      d.1 ≤ (g ⟨(S, d), h⟩).1 ∧ d.2 ≤ (g ⟨(S, d), h⟩).2 ∧
      ∀ s ∈ S, d.1 ≤ s.1 → d.2 ≤ s.2 → s ≠ g ⟨(S, d), h⟩ →
        (s.1 - d.1) * (s.2 - d.2) <
          ((g ⟨(S, d), h⟩).1 - d.1) * ((g ⟨(S, d), h⟩).2 - d.2) :=
  NashWork.nash_axioms_force_nash_product_max B hB g h_sel h_inv h_sym h_iia h_par

#print axioms solution
