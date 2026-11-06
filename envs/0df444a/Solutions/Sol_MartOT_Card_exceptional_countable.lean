-- Prove2me | solution 1 for MartOT.Card.exceptional_countable
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T06:16:39.862542+00:00
-- url     : https://prove2.me/submissions/47f5b5d2-fa76-448c-8adb-7156e7300eba

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Theorems.Thm_MartOT_Card_lemma_3_2
import Theorems.Thm_MartOT_Card_exists_index_off_chord
import Theorems.Thm_MartOT_Card_local_sign

open MeasureTheory

namespace Mot8Aux

noncomputable def m3 (l1 l2 l3 : NNReal) (p1 p2 p3 : ℝ × ℝ) : Measure (ℝ × ℝ) :=
  (l1 : ENNReal) • Measure.dirac p1 + (l2 : ENNReal) • Measure.dirac p2 +
    (l3 : ENNReal) • Measure.dirac p3

lemma ofReal_toENNReal (r : ℝ) : ((r : EReal)).toENNReal = ENNReal.ofReal r := by
  simp

lemma lint3 (l1 l2 l3 : NNReal) (p1 p2 p3 : ℝ × ℝ) (g : ℝ × ℝ → ENNReal) :
    ∫⁻ x, g x ∂(m3 l1 l2 l3 p1 p2 p3) = l1 * g p1 + l2 * g p2 + l3 * g p3 := by
  simp [m3, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac]
  rfl

lemma cost3 (l1 l2 l3 : NNReal) (p1 p2 p3 : ℝ × ℝ) (f : ℝ × ℝ → ℝ) :
    MartOT.Var.integralE (m3 l1 l2 l3 p1 p2 p3) f =
      (((l1 : ℝ) * f p1 + l2 * f p2 + l3 * f p3 : ℝ) : EReal) := by
  unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  rw [lint3, lint3]
  have key : ∀ (l : NNReal) (r : ℝ), (l : ENNReal) * ((r : EReal)).toENNReal =
      ENNReal.ofReal (l * max r 0) := by
    intro l r
    rw [ofReal_toENNReal, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
    congr 1
    rw [ENNReal.ofReal_max, ENNReal.ofReal_zero]; simp
  have key' : ∀ (l : NNReal) (r : ℝ), (l : ENNReal) * (-(r : EReal)).toENNReal =
      ENNReal.ofReal (l * max (-r) 0) := by
    intro l r
    rw [← EReal.coe_neg, key]
  simp only [key, key']
  have add3 : ∀ A B C : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ C →
      ENNReal.ofReal A + ENNReal.ofReal B + ENNReal.ofReal C = ENNReal.ofReal (A + B + C) := by
    intro A B C hA hB hC
    rw [ENNReal.ofReal_add (by positivity) hC, ENNReal.ofReal_add hA hB]
  rw [add3 ((l1 : ℝ) * max (f p1) 0) ((l2 : ℝ) * max (f p2) 0) ((l3 : ℝ) * max (f p3) 0)
      (by positivity) (by positivity) (by positivity),
    add3 ((l1 : ℝ) * max (-f p1) 0) ((l2 : ℝ) * max (-f p2) 0) ((l3 : ℝ) * max (-f p3) 0)
      (by positivity) (by positivity) (by positivity)]
  rw [EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal, ← EReal.coe_sub]
  congr 1
  have hA : (0 : ℝ) ≤ (l1 : ℝ) * max (f p1) 0 + (l2 : ℝ) * max (f p2) 0 + (l3 : ℝ) * max (f p3) 0 := by
    positivity
  have hB : (0 : ℝ) ≤ (l1 : ℝ) * max (-f p1) 0 + (l2 : ℝ) * max (-f p2) 0 +
      (l3 : ℝ) * max (-f p3) 0 := by
    positivity
  rw [max_eq_left hA, max_eq_left hB]
  have h1 : ∀ r : ℝ, max r 0 - max (-r) 0 = r := by
    intro r; rcases le_total r 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have := h1 (f p1); have := h1 (f p2); have := h1 (f p3)
  linear_combination (l1 : ℝ) * h1 (f p1) + (l2 : ℝ) * h1 (f p2) + (l3 : ℝ) * h1 (f p3)

lemma map3 (l1 l2 l3 : NNReal) (p1 p2 p3 : ℝ × ℝ) (g : ℝ × ℝ → ℝ) (hg : Measurable g) :
    (m3 l1 l2 l3 p1 p2 p3).map g = (l1 : ENNReal) • Measure.dirac (g p1) +
      (l2 : ENNReal) • Measure.dirac (g p2) + (l3 : ENNReal) • Measure.dirac (g p3) := by
  simp [m3, Measure.map_add _ _ hg, Measure.map_smul, Measure.map_dirac' hg]

lemma integrable3 (l1 l2 l3 : NNReal) (p1 p2 p3 : ℝ × ℝ) (F : ℝ × ℝ → ℝ) :
    Integrable F (m3 l1 l2 l3 p1 p2 p3) := by
  unfold m3
  refine ((Integrable.add_measure ?_ ?_).add_measure ?_) <;>
    exact (integrable_dirac (by simp)).smul_measure (by simp)

lemma integral3 (l1 l2 l3 : NNReal) (p1 p2 p3 : ℝ × ℝ) (F : ℝ × ℝ → ℝ) :
    ∫ x, F x ∂(m3 l1 l2 l3 p1 p2 p3) = (l1 : ℝ) * F p1 + l2 * F p2 + l3 * F p3 := by
  unfold m3
  have i : ∀ (l : NNReal) (p : ℝ × ℝ), Integrable F ((l : ENNReal) • Measure.dirac p) :=
    fun l p => (integrable_dirac (by simp)).smul_measure (by simp)
  rw [integral_add_measure ((i _ _).add_measure (i _ _)) (i _ _),
    integral_add_measure (i _ _) (i _ _)]
  simp [integral_dirac, NNReal.smul_def]

end Mot8Aux

open Mot8Aux in
theorem solution (μ : Measure ℝ) (h : ℝ → ℝ) (hh : ContDiff ℝ 2 h) (k : ℕ)
    (hk : ∀ s t : ℝ, {x : ℝ | deriv h x = s * x + t}.encard ≤ k)
    (Γ : Set (ℝ × ℝ))
    (hΓ : ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ Γ →
        ∀ α' : Measure (ℝ × ℝ),
          MartOT.Var.IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
          MartOT.Var.cost (fun x y => h (y - x)) (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤
            MartOT.Var.cost (fun x y => h (y - x)) α') :
    {x : ℝ | μ {x} = 0 ∧ ((k + 1 : ℕ) : ℕ∞) ≤ {y : ℝ | (x, y) ∈ Γ}.encard}.Countable := by
  classical
  apply Set.Countable.mono (s₂ := {x : ℝ | ((k + 1 : ℕ) : ℕ∞) ≤ {y : ℝ | (x, y) ∈ Γ}.encard})
    (fun x hx => hx.2)
  by_contra hA
  obtain ⟨a, b, hb, hbΓ, happ⟩ := MartOT.Card.lemma_3_2 (k + 1) (Nat.succ_pos k) Γ hA
  obtain ⟨i, hi0, hik, hD'⟩ := MartOT.Card.exists_index_off_chord h k hk a b hb
  have h0i : b 0 < b i := hb (by rw [Fin.lt_def]; simpa using hi0)
  have hik' : b i < b (Fin.last k) := hb (by rw [Fin.lt_def]; simpa using hik)
  set b0 := b 0 with hb0
  set bk := b (Fin.last k) with hbk
  set bi := b i with hbi
  set D := deriv h (bi - a) - ((1 - (bi - b0) / (bk - b0)) * deriv h (b0 - a) +
      (bi - b0) / (bk - b0) * deriv h (bk - a)) with hDdef
  have hD : D ≠ 0 := by
    intro h0
    apply hD' (a + 1) (by linarith)
    rw [h0, zero_mul]
  obtain ⟨ε₁, hε₁, hsign⟩ := MartOT.Card.local_sign h hh a b0 bk bi h0i hik' hD
  set ε := min ε₁ (min (bi - b0) (bk - bi)) with hεdef
  have hε : 0 < ε := lt_min hε₁ (lt_min (by linarith) (by linarith))
  obtain ⟨a', β, ha'β, hβ, ha', hneg, hne⟩ : ∃ a' β : ℝ, (a', β) ∈ Γ ∧ |bi - β| < ε ∧
      |a - a'| < ε ∧ D * (a' - a) < 0 ∧ a' ≠ a := by
    rcases lt_or_gt_of_ne hD with hDn | hDp
    · obtain ⟨⟨a', haa', b', _, hb'Γ, hda, hdb⟩, _⟩ := happ ε hε
      exact ⟨a', b' i, hb'Γ i, hdb i, hda, mul_neg_of_neg_of_pos hDn (by linarith),
        ne_of_gt haa'⟩
    · obtain ⟨_, ⟨a', haa', b', _, hb'Γ, hda, hdb⟩⟩ := happ ε hε
      exact ⟨a', b' i, hb'Γ i, hdb i, hda, mul_neg_of_pos_of_neg hDp (by linarith),
        ne_of_lt haa'⟩
  have hsg := hsign β a' (lt_of_lt_of_le hβ (min_le_left _ _))
    (abs_pos.2 (sub_ne_zero.2 (Ne.symm hne))) (lt_of_lt_of_le ha' (min_le_left _ _))
  set l := (β - b0) / (bk - b0) with hl
  have hlt : (h (β - a) + l * h (bk - a') + (1 - l) * h (b0 - a')) -
      (h (β - a') + l * h (bk - a) + (1 - l) * h (b0 - a)) < 0 := by
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hsg with hc | hc
    · exact absurd hc.2 (not_lt.2 hneg.le)
    · exact hc.1
  have hβ' : |bi - β| < min (bi - b0) (bk - bi) := lt_of_lt_of_le hβ (min_le_right _ _)
  rw [abs_lt] at hβ'
  have hβ0 : b0 < β := by linarith [min_le_left (bi - b0) (bk - bi), hβ'.2]
  have hβk : β < bk := by linarith [min_le_right (bi - b0) (bk - bi), hβ'.1]
  have hbkb0 : 0 < bk - b0 := by linarith
  have hl0 : 0 ≤ l := div_nonneg (by linarith) hbkb0.le
  have hl1 : 0 ≤ 1 - l := by
    rw [sub_nonneg, hl, div_le_one hbkb0]; linarith
  have hβl : l * bk + (1 - l) * b0 = β := by
    rw [hl]; field_simp; ring
  set p1 : ℝ × ℝ := (a, bk)
  set p2 : ℝ × ℝ := (a, b0)
  set p3 : ℝ × ℝ := (a', β)
  have h12 : p1 ≠ p2 := by
    intro e; have := congrArg Prod.snd e; simp [p1, p2] at this; linarith
  have h13 : p1 ≠ p3 := by
    intro e; have := congrArg Prod.fst e; exact hne (by simpa [p1, p3] using this.symm)
  have h23 : p2 ≠ p3 := by
    intro e; have := congrArg Prod.fst e; exact hne (by simpa [p2, p3] using this.symm)
  let w : ℝ × ℝ → NNReal := fun p =>
    if p = p1 then l.toNNReal else if p = p2 then (1 - l).toNNReal else 1
  let S : Finset (ℝ × ℝ) := {p1, p2, p3}
  have hsum : ∑ p ∈ S, (w p : ENNReal) • Measure.dirac p =
      m3 l.toNNReal (1 - l).toNNReal 1 p1 p2 p3 := by
    simp only [S]
    rw [Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
      Finset.sum_singleton]
    simp only [w, if_pos rfl, if_neg h12.symm, if_neg h13.symm, if_neg h23.symm, m3, if_true]
    rw [add_assoc]
  have hS : (↑S : Set (ℝ × ℝ)) ⊆ Γ := by
    intro p hp
    simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact hbΓ (Fin.last k)
    · exact hbΓ 0
    · exact ha'β
  let α' := m3 l.toNNReal (1 - l).toNNReal 1 (a', bk) (a', b0) (a, β)
  have hone : ((l.toNNReal : ENNReal) + ((1 - l).toNNReal : ENNReal)) = 1 := by
    rw [← ENNReal.coe_add, ← Real.toNNReal_add hl0 hl1]; simp
  have hcomp : MartOT.Var.IsCompetitor (m3 l.toNNReal (1 - l).toNNReal 1 p1 p2 p3) α' := by
    refine ⟨?_, ?_, integrable3 _ _ _ _ _ _ _, integrable3 _ _ _ _ _ _ _, ?_⟩
    · simp only [α', map3 _ _ _ _ _ _ _ measurable_fst, p1, p2, p3]
      rw [← add_smul, ← add_smul, hone, one_smul, one_smul, ENNReal.coe_one, one_smul,
        one_smul, add_comm]
    · simp only [α', map3 _ _ _ _ _ _ _ measurable_snd, p1, p2, p3]
    · intro ρ _ _
      simp only [α', integral3, p1, p2, p3]
      rw [Real.coe_toNNReal _ hl0, Real.coe_toNNReal _ hl1, NNReal.coe_one]
      linear_combination (ρ a - ρ a') * hβl
  have key := hΓ S w hS α' (hsum ▸ hcomp)
  rw [hsum] at key
  unfold MartOT.Var.cost at key
  rw [cost3, cost3, EReal.coe_le_coe_iff] at key
  simp only [α', p1, p2, p3, Real.coe_toNNReal _ hl0, Real.coe_toNNReal _ hl1,
    NNReal.coe_one, one_mul] at key
  linarith
