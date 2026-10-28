-- Prove2me | solution 1 for HetExponomial.ChoiceProb.eq_16
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T01:53:13.613605+00:00
-- url     : https://prove2.me/submissions/d5828e78-9868-4013-972c-b23c05c7077a

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model

open MeasureTheory ProbabilityTheory

namespace HetExponomial.ChoiceProb

lemma sum_affine {n : ℕ} (u lam : Fin n → ℝ) (i : Fin n) (B : Finset (Fin n)) (z : ℝ) :
    ∑ j ∈ B, lam j * (u j - u i + z) =
      (∑ j ∈ B, lam j * (u j - u i)) + (∑ j ∈ B, lam j) * z := by
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma tailInt_eq {n : ℕ} (u lam : Fin n → ℝ) (i : Fin n) (hlam : ∀ j, 0 < lam j) (x c : ℝ)
    (hne : (betterThan u x).Nonempty) :
    tailInt u lam i x c =
      Real.exp (-(∑ j ∈ betterThan u x, lam j * (u j - u i))) *
        (Real.exp (-((∑ j ∈ betterThan u x, lam j) * c)) / (∑ j ∈ betterThan u x, lam j)) := by
  have hΛ : 0 < ∑ j ∈ betterThan u x, lam j := Finset.sum_pos (fun j _ => hlam j) hne
  unfold tailInt
  simp_rw [sum_affine]
  have : ∀ z : ℝ, Real.exp (-((∑ j ∈ betterThan u x, lam j * (u j - u i)) +
      (∑ j ∈ betterThan u x, lam j) * z)) =
      Real.exp (-(∑ j ∈ betterThan u x, lam j * (u j - u i))) *
        Real.exp ((-(∑ j ∈ betterThan u x, lam j)) * z) := by
    intro z; rw [← Real.exp_add]; congr 1; ring
  simp_rw [this]
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith)]
  congr 1
  rw [neg_div_neg_eq]; congr 2; ring

lemma tail_integrableOn {n : ℕ} (u lam : Fin n → ℝ) (i : Fin n) (hlam : ∀ j, 0 < lam j) (x c : ℝ)
    (hne : (betterThan u x).Nonempty) :
    IntegrableOn (fun z => Real.exp (-(∑ j ∈ betterThan u x, lam j * (u j - u i + z)))) (Set.Ioi c) := by
  have hΛ : 0 < ∑ j ∈ betterThan u x, lam j := Finset.sum_pos (fun j _ => hlam j) hne
  simp_rw [sum_affine]
  have : ∀ z : ℝ, Real.exp (-((∑ j ∈ betterThan u x, lam j * (u j - u i)) +
      (∑ j ∈ betterThan u x, lam j) * z)) =
      Real.exp (-(∑ j ∈ betterThan u x, lam j * (u j - u i))) *
        Real.exp ((-(∑ j ∈ betterThan u x, lam j)) * z) := by
    intro z; rw [← Real.exp_add]; congr 1; ring
  simp_rw [this]
  exact (integrableOn_exp_mul_Ioi (by linarith) c).const_mul _

lemma sum_max_eq {n : ℕ} (u lam : Fin n → ℝ) (i : Fin n) (x z : ℝ)
    (h1 : ∀ j, x ≤ u j → 0 ≤ u j - u i + z) (h2 : ∀ j, ¬ x ≤ u j → u j - u i + z ≤ 0) :
    ∑ j, lam j * max (u j - u i + z) 0 = ∑ j ∈ betterThan u x, lam j * (u j - u i + z) := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => x ≤ u j)]
  have e1 : ∑ j ∈ Finset.univ.filter (fun j => x ≤ u j), lam j * max (u j - u i + z) 0 =
      ∑ j ∈ betterThan u x, lam j * (u j - u i + z) := by
    unfold betterThan
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [max_eq_left (h1 j (Finset.mem_filter.mp hj).2)]
  have e2 : ∑ j ∈ Finset.univ.filter (fun j => ¬ x ≤ u j), lam j * max (u j - u i + z) 0 = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [max_eq_right (h2 j (Finset.mem_filter.mp hj).2)]; simp
  rw [e1, e2, add_zero]

lemma level_exists {n : ℕ} (u : Fin n → ℝ) (j : Fin n) : ∃ v, level u v = u j := by
  have h1 : u j ∈ levels u := Finset.mem_image_of_mem _ (Finset.mem_univ j)
  have h := Finset.range_orderEmbOfFin (levels u) (rfl : (levels u).card = (levels u).card)
  have h2 : u j ∈ Set.range ((levels u).orderEmbOfFin (rfl : (levels u).card = (levels u).card)) := by
    rw [h]; exact_mod_cast h1
  obtain ⟨v, hv⟩ := h2
  exact ⟨v, hv⟩

lemma exists_eq_level {n : ℕ} (u : Fin n → ℝ) (v : Fin (levels u).card) : ∃ j, u j = level u v := by
  have h := Finset.orderEmbOfFin_mem (levels u) (rfl : (levels u).card = (levels u).card) v
  have h' : level u v ∈ Finset.image u Finset.univ := h
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h'
  exact ⟨j, hj⟩


/-- the summand in (16) -/
noncomputable def Tw {n : ℕ} (u lam : Fin n → ℝ) (i : Fin n) (w : Fin (levels u).card) : ℝ :=
  tailInt u lam i (level u w) (u i - level u w) -
    if 0 < w.val then
      tailInt u lam i (level u w)
        (u i - level u ⟨w.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) w.isLt⟩)
    else 0

lemma nonempty_better {n : ℕ} (u : Fin n → ℝ) (w : Fin (levels u).card) :
    (betterThan u (level u w)).Nonempty := by
  obtain ⟨j, hj⟩ := exists_eq_level u w
  exact ⟨j, by simp [betterThan, hj]⟩

lemma g_eq_on {n : ℕ} (u lam : Fin n → ℝ) (i : Fin n) (w : Fin (levels u).card) (z : ℝ)
    (hz1 : u i - level u w < z) (hz2 : ∀ p : Fin (levels u).card, p < w → z ≤ u i - level u p) :
    lam i * Real.exp (-(∑ j, lam j * max (u j - u i + z) 0)) =
      lam i * Real.exp (-(∑ j ∈ betterThan u (level u w), lam j * (u j - u i + z))) := by
  congr 3
  refine sum_max_eq u lam i _ z (fun j hj => by linarith) (fun j hj => ?_)
  obtain ⟨v, hv⟩ := level_exists u j
  have hvw : v < w := by
    rw [← (level u).lt_iff_lt, hv]; exact not_le.mp hj
  have := hz2 v hvw
  rw [← hv]; linarith

lemma eq16_induct {n : ℕ} (u lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (i : Fin n)
    (k : Fin (levels u).card) :
    ∀ m : ℕ, ∀ hm : m < (levels u).card, m ≤ k.val →
      IntegrableOn (fun z => lam i * Real.exp (-(∑ j, lam j * max (u j - u i + z) 0)))
          (Set.Ioi (u i - level u ⟨m, hm⟩)) ∧
      ∫ z in Set.Ioi (u i - level u ⟨m, hm⟩),
          lam i * Real.exp (-(∑ j, lam j * max (u j - u i + z) 0)) =
        lam i * ∑ w ∈ Finset.univ.filter (fun w : Fin (levels u).card => w ≤ ⟨m, hm⟩), Tw u lam i w := by
  intro m
  induction m with
  | zero =>
    intro hm _
    have hcongr : Set.EqOn (fun z => lam i * Real.exp (-(∑ j, lam j * max (u j - u i + z) 0)))
        (fun z => lam i * Real.exp (-(∑ j ∈ betterThan u (level u ⟨0, hm⟩), lam j * (u j - u i + z))))
        (Set.Ioi (u i - level u ⟨0, hm⟩)) := by
      intro z hz
      exact g_eq_on u lam i ⟨0, hm⟩ z hz (fun p hp => absurd hp (by simp [Fin.lt_def]))
    have hint : IntegrableOn (fun z => lam i * Real.exp (-(∑ j ∈ betterThan u (level u ⟨0, hm⟩), lam j * (u j - u i + z))))
        (Set.Ioi (u i - level u ⟨0, hm⟩)) :=
      (tail_integrableOn u lam i hlam (level u ⟨0, hm⟩) (u i - level u ⟨0, hm⟩)
      (nonempty_better u ⟨0, hm⟩)).const_mul (lam i)
    refine ⟨hint.congr_fun hcongr.symm measurableSet_Ioi, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul]
    have hfilt : Finset.univ.filter (fun w : Fin (levels u).card => w ≤ ⟨0, hm⟩) = {⟨0, hm⟩} := by
      ext w; simp [Fin.le_def, Fin.ext_iff]
    rw [hfilt, Finset.sum_singleton]
    unfold Tw tailInt
    simp
  | succ m ih =>
    intro hm hmk
    have hm' : m < (levels u).card := by omega
    obtain ⟨ihI, ihV⟩ := ih hm' (by omega)
    set w : Fin (levels u).card := ⟨m + 1, hm⟩ with hw
    set p : Fin (levels u).card := ⟨m, hm'⟩ with hp
    have hpw : p < w := by simp [hw, hp, Fin.lt_def]
    have hlev : level u p < level u w := (level u).lt_iff_lt.mpr hpw
    have hle : u i - level u w ≤ u i - level u p := by linarith
    have hcongr : Set.EqOn (fun z => lam i * Real.exp (-(∑ j, lam j * max (u j - u i + z) 0)))
        (fun z => lam i * Real.exp (-(∑ j ∈ betterThan u (level u w), lam j * (u j - u i + z))))
        (Set.Ioc (u i - level u w) (u i - level u p)) := by
      intro z hz
      refine g_eq_on u lam i w z hz.1 (fun q hq => ?_)
      have : q ≤ p := by simp only [hw, hp, Fin.lt_def, Fin.le_def] at hq ⊢; omega
      have : level u q ≤ level u p := (level u).le_iff_le.mpr this
      linarith [hz.2]
    have hE1 := tail_integrableOn u lam i hlam (level u w) (u i - level u w) (nonempty_better u w)
    have hE2 := tail_integrableOn u lam i hlam (level u w) (u i - level u p) (nonempty_better u w)
    have hIoc : IntegrableOn (fun z => lam i * Real.exp (-(∑ j, lam j * max (u j - u i + z) 0)))
        (Set.Ioc (u i - level u w) (u i - level u p)) := by
      have h0 : IntegrableOn (fun z => lam i * Real.exp (-(∑ j ∈ betterThan u (level u w), lam j * (u j - u i + z))))
          (Set.Ioi (u i - level u w)) := hE1.const_mul (lam i)
      have := h0.mono_set (fun x (hx : x ∈ Set.Ioc (u i - level u w) (u i - level u p)) => hx.1)
      exact this.congr_fun hcongr.symm measurableSet_Ioc
    have hunion : Set.Ioc (u i - level u w) (u i - level u p) ∪ Set.Ioi (u i - level u p) =
        Set.Ioi (u i - level u w) := Set.Ioc_union_Ioi_eq_Ioi hle
    refine ⟨?_, ?_⟩
    · rw [← hunion]; exact hIoc.union ihI
    · rw [← hunion, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hIoc ihI, ihV]
      rw [setIntegral_congr_fun measurableSet_Ioc hcongr, integral_const_mul]
      have hsplit : ∫ z in Set.Ioc (u i - level u w) (u i - level u p),
          Real.exp (-(∑ j ∈ betterThan u (level u w), lam j * (u j - u i + z))) =
          tailInt u lam i (level u w) (u i - level u w) -
            tailInt u lam i (level u w) (u i - level u p) := by
        have h := setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
          (hE1.mono_set Set.Ioc_subset_Ioi_self) hE2
        rw [hunion] at h
        unfold tailInt
        linarith
      rw [hsplit]
      have hfilt : Finset.univ.filter (fun v : Fin (levels u).card => v ≤ w) =
          insert w (Finset.univ.filter (fun v : Fin (levels u).card => v ≤ p)) := by
        ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          hw, hp, Fin.le_def, Fin.ext_iff]; omega
      have hnot : w ∉ Finset.univ.filter (fun v : Fin (levels u).card => v ≤ p) := by
        simp [hw, hp, Fin.le_def]
      rw [hfilt, Finset.sum_insert hnot]
      have hTw : Tw u lam i w = tailInt u lam i (level u w) (u i - level u w) -
            tailInt u lam i (level u w) (u i - level u p) := by
        unfold Tw
        rw [if_pos (by simp [hw])]
        have e : (⟨w.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) w.isLt⟩ : Fin (levels u).card) = p :=
          Fin.ext (by simp [hw, hp])
        rw [e]
      rw [hTw]; ring

theorem eq16_core {n : ℕ} (u lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (i : Fin n)
    (k : Fin (levels u).card) (hk : level u k = u i) :
    ∫ z in Set.Ioi 0, lam i * Real.exp (-(∑ j, lam j * max (u j - u i + z) 0)) =
      lam i * ∑ w ∈ Finset.univ.filter (fun w => w ≤ k), Tw u lam i w := by
  have := (eq16_induct u lam hlam i k k.val k.isLt le_rfl).2
  simpa [hk] using this

end HetExponomial.ChoiceProb


open HetExponomial.ChoiceProb in
theorem solution {n : ℕ} (hn : 2 ≤ n) (u lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (i : Fin n)
    (k : Fin (levels u).card) (hk : level u k = u i) :
    ∫ z in Set.Ioi 0, lam i * Real.exp (-(∑ j, lam j * max (u j - u i + z) 0)) =
      lam i * ∑ w ∈ Finset.univ.filter (fun w => w ≤ k),
        (tailInt u lam i (level u w) (u i - level u w) -
          if 0 < w.val then
            tailInt u lam i (level u w)
              (u i - level u ⟨w.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) w.isLt⟩)
          else 0) :=
  eq16_core u lam hlam i k hk
