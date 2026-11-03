-- Prove2me | solution 1 for GreedWorks.OnlineTime.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:24:58.724134+00:00
-- url     : https://prove2.me/submissions/efeb444a-e1a8-414a-959e-2f56d36914f4

import Mathlib
import Definitions.Def_GreedWorks_OnlineTime_Greedy

open GreedWorks.OnlineTime Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace Lemma6Helper

variable {M : Type*} [Fintype M] {n : ℕ}

private lemma interval_cover_bound_aux (m : ℕ) :
    ∀ (S : Finset (Fin n)) (_hcard : S.card = m) (s len : Fin n → ℝ)
      (_hlen : ∀ l ∈ S, 0 ≤ len l) (a b : ℝ)
      (_hcov : ∀ t, a ≤ t → t < b → ∃ l ∈ S, s l ≤ t ∧ t < s l + len l),
      b - a ≤ ∑ l ∈ S, len l := by
  induction m with
  | zero =>
    intro S hcard s len _ a b hcov
    have hS : S = ∅ := Finset.card_eq_zero.mp hcard
    rw [hS, Finset.sum_empty]
    by_contra! hpos
    have hab : a < b := by linarith
    obtain ⟨l, hl, _⟩ := hcov a (le_refl a) hab
    rw [hS] at hl
    exact Finset.notMem_empty l hl
  | succ m ih =>
    intro S hcard s len hlen a b hcov
    by_cases hab : a < b
    · obtain ⟨l₀, hl₀S, hsl₀, hlt₀⟩ := hcov a (le_refl a) hab
      let S' := S.erase l₀
      have hcard' : S'.card = m := by
        rw [Finset.card_erase_of_mem hl₀S, hcard]
        omega
      have hlen' : ∀ l ∈ S', 0 ≤ len l := fun l hl => hlen l (Finset.mem_of_mem_erase hl)
      let a' := s l₀ + len l₀
      have hcov' : ∀ t, a' ≤ t → t < b → ∃ l ∈ S', s l ≤ t ∧ t < s l + len l := by
        intro t ha't htb
        obtain ⟨l, hlS, hsl, hlt⟩ := hcov t (by linarith) htb
        have hne : l ≠ l₀ := by
          intro heq
          subst heq
          linarith
        exact ⟨l, Finset.mem_erase.mpr ⟨hne, hlS⟩, hsl, hlt⟩
      have hstep := ih S' hcard' s len hlen' a' b hcov'
      have hsum : ∑ l ∈ S', len l + len l₀ = ∑ l ∈ S, len l :=
        Finset.sum_erase_add S len hl₀S
      linarith
    · have hsum_nonneg : 0 ≤ ∑ l ∈ S, len l := Finset.sum_nonneg hlen
      linarith

private lemma interval_cover_bound (S : Finset (Fin n)) (s len : Fin n → ℝ)
    (hlen : ∀ l ∈ S, 0 ≤ len l) (a b : ℝ)
    (hcov : ∀ t, a ≤ t → t < b → ∃ l ∈ S, s l ≤ t ∧ t < s l + len l) :
    b - a ≤ ∑ l ∈ S, len l :=
  interval_cover_bound_aux S.card S rfl s len hlen a b hcov

private def runSet (c : ℝ) (r : Fin n → ℕ) (p : M → Fin n → ℝ) (m : Fin n → M) (s : Fin n → ℝ)
    (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun l : Fin n =>
    m l = m j ∧ modRelease c r p (m j) j ≤ s l ∧ s l < s j)

private def crossSet (c : ℝ) (r : Fin n → ℕ) (p : M → Fin n → ℝ) (m : Fin n → M) (s : Fin n → ℝ)
    (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun l : Fin n =>
    m l = m j ∧ s l < modRelease c r p (m j) j ∧ modRelease c r p (m j) j < s l + p (m l) l)

private lemma start_le_bound (elig : M → Fin n → Prop) (r : Fin n → ℕ)
    (p : M → Fin n → ℝ) (hp : ∀ i j, elig i j → 1 ≤ p i j) (w : Fin n → ℝ)
    (c : ℝ) (hc : 0 < c) (m : Fin n → M) (s : Fin n → ℝ)
    (hG : IsGreedy c r p w elig m s) (j : Fin n) :
    s j ≤ (1 + 1 / c) * modRelease c r p (m j) j +
      ∑ l ∈ runSet c r p m s j, p (m j) l := by
  let r_ij := modRelease c r p (m j) j
  have hr_ij_nonneg : 0 ≤ r_ij := by
    unfold r_ij modRelease
    exact le_trans (Nat.cast_nonneg (r j)) (le_max_left _ _)
  let R := runSet c r p m s j
  let C := crossSet c r p m s j
  have hp_nonneg : ∀ l : Fin n, 0 ≤ p (m l) l := by
    intro l
    have h1 := hp (m l) l (hG.1 l).1
    linarith
  have hcov : ∀ t, r_ij ≤ t → t < s j →
      ∃ l ∈ R ∪ C, s l ≤ t ∧ t < s l + p (m l) l := by
    intro t hrt hts
    obtain ⟨l, hml, hsl, hlt⟩ := hG.2.2.2.1 j t hrt hts
    refine ⟨l, ?_, hsl, hlt⟩
    rw [Finset.mem_union]
    by_cases h : r_ij ≤ s l
    · left
      simp only [R, runSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hml, h, lt_of_le_of_lt hsl hts⟩
    · right
      simp only [C, crossSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hml, lt_of_not_ge h, lt_of_le_of_lt hrt hlt⟩
  have hbound := interval_cover_bound (R ∪ C) s (fun l => p (m l) l)
    (fun l _ => hp_nonneg l) r_ij (s j) hcov
  have hunion : ∑ l ∈ R ∪ C, p (m l) l ≤ ∑ l ∈ R, p (m l) l + ∑ l ∈ C, p (m l) l := by
    have h1 := Finset.sum_union_inter (s₁ := R) (s₂ := C) (f := fun l => p (m l) l)
    have h2 : 0 ≤ ∑ l ∈ R ∩ C, p (m l) l := Finset.sum_nonneg (fun l _ => hp_nonneg l)
    linarith
  have hR_eq : ∑ l ∈ R, p (m l) l = ∑ l ∈ R, p (m j) l := by
    refine Finset.sum_congr rfl (fun l hl => ?_)
    have hml : m l = m j := (Finset.mem_filter.mp hl).2.1
    rw [hml]
  have hC_card : C.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro l₁ hl₁ l₂ hl₂
    by_contra hne
    have hm1 : m l₁ = m j := (Finset.mem_filter.mp hl₁).2.1
    have hs1 : s l₁ < r_ij := (Finset.mem_filter.mp hl₁).2.2.1
    have he1 : r_ij < s l₁ + p (m l₁) l₁ := (Finset.mem_filter.mp hl₁).2.2.2
    have hm2 : m l₂ = m j := (Finset.mem_filter.mp hl₂).2.1
    have hs2 : s l₂ < r_ij := (Finset.mem_filter.mp hl₂).2.2.1
    have he2 : r_ij < s l₂ + p (m l₂) l₂ := (Finset.mem_filter.mp hl₂).2.2.2
    have hdisj := hG.2.2.1 l₁ l₂ hne (hm1.trans hm2.symm)
    have hmem1 : r_ij ∈ Set.Ico (s l₁) (s l₁ + p (m l₁) l₁) := ⟨le_of_lt hs1, he1⟩
    have hmem2 : r_ij ∈ Set.Ico (s l₂) (s l₂ + p (m l₂) l₂) := ⟨le_of_lt hs2, he2⟩
    exact Set.disjoint_left.mp hdisj hmem1 hmem2
  have hC_sum : ∑ l ∈ C, p (m l) l ≤ (1 / c) * r_ij := by
    calc ∑ l ∈ C, p (m l) l
        ≤ ∑ _l ∈ C, ((1 / c) * r_ij) := by
          refine Finset.sum_le_sum (fun l hl => ?_)
          have hs_lt : s l < r_ij := (Finset.mem_filter.mp hl).2.2.1
          have hmod_le : modRelease c r p (m l) l ≤ s l := hG.2.1 l
          have hcp_le : c * p (m l) l ≤ modRelease c r p (m l) l := le_max_right _ _
          have hcp_lt : c * p (m l) l ≤ r_ij := le_trans hcp_le (le_trans hmod_le (le_of_lt hs_lt))
          have hmul := mul_le_mul_of_nonneg_left hcp_lt (le_of_lt (one_div_pos.mpr hc))
          have hc_ne : c ≠ 0 := ne_of_gt hc
          have hrew : (1 / c) * (c * p (m l) l) = p (m l) l := by
            field_simp [hc_ne]
          linarith
      _ = (C.card : ℝ) * ((1 / c) * r_ij) := by simp [nsmul_eq_mul]
      _ ≤ 1 * ((1 / c) * r_ij) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast hC_card
      _ = (1 / c) * r_ij := one_mul _
  linarith

private def pairTerm (p : M → Fin n → ℝ) (w : Fin n → ℝ) (m : Fin n → M)
    (a b : Fin n) : ℝ :=
  if w a / p (m a) a ≤ w b / p (m a) b then w a * p (m a) b else w b * p (m a) a

private lemma cost_eq_base_add_sum (c : ℝ) (r : Fin n → ℕ) (p : M → Fin n → ℝ) (w : Fin n → ℝ)
    (m : Fin n → M) (s : Fin n → ℝ) (a : Fin n) :
    cost c r p w m s a (m a) =
      w a * ((1 + 1 / c) * modRelease c r p (m a) a + p (m a) a) +
        ∑ b ∈ waiting r m s (m a) a, pairTerm p w m a b := by
  unfold cost
  have hsplit := (Finset.sum_filter_add_sum_filter_not (waiting r m s (m a) a)
    (fun b => w a / p (m a) a ≤ w b / p (m a) b) (pairTerm p w m a)).symm
  have h1 : ∑ b ∈ (waiting r m s (m a) a).filter (fun b => w a / p (m a) a ≤ w b / p (m a) b),
        pairTerm p w m a b =
      w a * ∑ b ∈ (waiting r m s (m a) a).filter (fun b => w a / p (m a) a ≤ w b / p (m a) b),
        p (m a) b := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    have hle : w a / p (m a) a ≤ w b / p (m a) b := (Finset.mem_filter.mp hb).2
    simp [pairTerm, hle]
  have h2 : (waiting r m s (m a) a).filter (fun b => ¬ w a / p (m a) a ≤ w b / p (m a) b) =
      (waiting r m s (m a) a).filter (fun b => w b / p (m a) b < w a / p (m a) a) := by
    ext b; simp [not_le]
  have h3 : ∑ b ∈ (waiting r m s (m a) a).filter (fun b => ¬ w a / p (m a) a ≤ w b / p (m a) b),
        pairTerm p w m a b =
      ∑ b ∈ (waiting r m s (m a) a).filter (fun b => w b / p (m a) b < w a / p (m a) a),
        w b * p (m a) a := by
    rw [h2]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    have hlt : w b / p (m a) b < w a / p (m a) a := (Finset.mem_filter.mp hb).2
    have hnle : ¬ w a / p (m a) a ≤ w b / p (m a) b := not_le.mpr hlt
    simp [pairTerm, hnle]
  rw [hsplit, h1, h3]
  ring

private lemma pairTerm_ge_indicators (elig : M → Fin n → Prop) (r : Fin n → ℕ)
    (p : M → Fin n → ℝ) (hp : ∀ i j, elig i j → 1 ≤ p i j)
    (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j)
    (c : ℝ) (m : Fin n → M) (s : Fin n → ℝ)
    (hG : IsGreedy c r p w elig m s) (a b : Fin n) (hb : b ∈ waiting r m s (m a) a) :
    (if b ∈ runSet c r p m s a then w a * p (m a) b else 0) +
      (if a ∈ runSet c r p m s b then w b * p (m b) a else 0) ≤
      pairTerm p w m a b := by
  have hmb : m b = m a := (Finset.mem_filter.mp hb).2.2.1
  have hpa_pos : 0 < p (m a) a := by
    have := hp (m a) a (hG.1 a).1; linarith
  have hpb_pos : 0 < p (m a) b := by
    rw [← hmb]
    have := hp (m b) b (hG.1 b).1; linarith
  by_cases hba : b ∈ runSet c r p m s a
  · have hsb_lt : s b < s a := (Finset.mem_filter.mp hba).2.2.2
    have hmod_a : modRelease c r p (m a) a ≤ s b := (Finset.mem_filter.mp hba).2.2.1
    have hnot_ab : a ∉ runSet c r p m s b := by
      intro hab
      have hsa_lt : s a < s b := (Finset.mem_filter.mp hab).2.2.2
      linarith
    have hprio : w a / p (m a) a ≤ w b / p (m a) b := by
      have h := hG.2.2.2.2 b a hmb.symm hmod_a hsb_lt
      rwa [hmb] at h
    rw [if_pos hba, if_neg hnot_ab, add_zero]
    unfold pairTerm
    rw [if_pos hprio]
  · by_cases hab : a ∈ runSet c r p m s b
    · have hsa_lt : s a < s b := (Finset.mem_filter.mp hab).2.2.2
      have hmod_b : modRelease c r p (m b) b ≤ s a := (Finset.mem_filter.mp hab).2.2.1
      have hprio : w b / p (m a) b ≤ w a / p (m a) a := by
        have h := hG.2.2.2.2 a b hmb hmod_b hsa_lt
        rwa [hmb] at h
      rw [if_neg hba, if_pos hab, zero_add]
      unfold pairTerm
      split_ifs with hle
      · have heq : w a / p (m a) a = w b / p (m a) b := le_antisymm hle hprio
        have hpa_ne : p (m a) a ≠ 0 := ne_of_gt hpa_pos
        have hpb_ne : p (m a) b ≠ 0 := ne_of_gt hpb_pos
        have hmul : w a * p (m a) b = w b * p (m a) a :=
          (div_eq_div_iff hpa_ne hpb_ne).mp heq
        rw [hmb]
        linarith
      · rw [hmb]
    · rw [if_neg hba, if_neg hab, add_zero]
      unfold pairTerm
      split_ifs
      · exact mul_nonneg (hw a) (le_of_lt hpb_pos)
      · exact mul_nonneg (hw b) (le_of_lt hpa_pos)

private lemma mem_waiting_of_mem_runSet_lt (c : ℝ) (r : Fin n → ℕ) (p : M → Fin n → ℝ)
    (w : Fin n → ℝ) (elig : M → Fin n → Prop) (m : Fin n → M) (s : Fin n → ℝ)
    (hG : IsGreedy c r p w elig m s) {j l : Fin n} (hl : l ∈ runSet c r p m s j) :
    (l < j → l ∈ waiting r m s (m j) j) ∧
      (j < l → j ∈ waiting r m s (m l) l) := by
  have hml : m l = m j := (Finset.mem_filter.mp hl).2.1
  have hmod_j : modRelease c r p (m j) j ≤ s l := (Finset.mem_filter.mp hl).2.2.1
  have hsl_lt : s l < s j := (Finset.mem_filter.mp hl).2.2.2
  refine ⟨fun hlt => ?_, fun hgt => ?_⟩
  · simp only [waiting, Finset.mem_filter, Finset.mem_univ, true_and]
    have hrj : (r j : ℝ) ≤ modRelease c r p (m j) j := le_max_left _ _
    exact ⟨hlt, hml, le_trans hrj hmod_j⟩
  · simp only [waiting, Finset.mem_filter, Finset.mem_univ, true_and]
    have hrl : (r l : ℝ) ≤ modRelease c r p (m l) l := le_max_left _ _
    have hmod_l : modRelease c r p (m l) l ≤ s l := hG.2.1 l
    exact ⟨hgt, hml.symm, le_trans hrl (le_trans hmod_l (le_of_lt hsl_lt))⟩

private lemma sum_finset_eq_sum_univ (S : Finset (Fin n)) (f : Fin n → ℝ) :
    ∑ b ∈ S, f b = ∑ b : Fin n, if b ∈ S then f b else 0 := by
  rw [← Finset.sum_filter]
  have h : (Finset.univ : Finset (Fin n)).filter (fun b => b ∈ S) = S := by
    ext b; simp
  rw [h]

end Lemma6Helper

open Lemma6Helper

theorem solution {M : Type*} [Fintype M] [Nonempty M] {n : ℕ}
    (elig : M → Fin n → Prop) (_hElig : ∀ j, ∃ i, elig i j)
    (r : Fin n → ℕ) (_hr : Monotone r)
    (p : M → Fin n → ℝ) (hp : ∀ i j, elig i j → 1 ≤ p i j)
    (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j)
    (c : ℝ) (hc : 0 < c) (m : Fin n → M) (s : Fin n → ℝ)
    (hG : IsGreedy c r p w elig m s) :
    nominalValue p w m s ≤ ∑ j : Fin n, cost c r p w m s j (m j) := by
  have hcost_sum : ∑ a : Fin n, cost c r p w m s a (m a) =
      ∑ a : Fin n, w a * ((1 + 1 / c) * modRelease c r p (m a) a + p (m a) a) +
        ∑ a : Fin n, ∑ b ∈ waiting r m s (m a) a, pairTerm p w m a b := by
    simp_rw [cost_eq_base_add_sum]
    rw [Finset.sum_add_distrib]
  have hpair_ge : ∑ j : Fin n, w j * (∑ l ∈ runSet c r p m s j, p (m j) l) ≤
      ∑ a : Fin n, ∑ b ∈ waiting r m s (m a) a, pairTerm p w m a b := by
    have hstep1 : ∑ a : Fin n, ∑ b ∈ waiting r m s (m a) a,
          ((if b ∈ runSet c r p m s a then w a * p (m a) b else 0) +
            (if a ∈ runSet c r p m s b then w b * p (m b) a else 0)) ≤
        ∑ a : Fin n, ∑ b ∈ waiting r m s (m a) a, pairTerm p w m a b := by
      refine Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b hb => ?_))
      exact pairTerm_ge_indicators elig r p hp w hw c m s hG a b hb
    refine le_trans ?_ hstep1
    simp_rw [Finset.sum_add_distrib]
    have hpart1 : ∑ a : Fin n, ∑ b ∈ waiting r m s (m a) a,
          (if b ∈ runSet c r p m s a then w a * p (m a) b else 0) =
        ∑ j : Fin n, ∑ l : Fin n,
          (if l ∈ runSet c r p m s j ∧ l < j then w j * p (m j) l else 0) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [sum_finset_eq_sum_univ]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      by_cases hl : l ∈ runSet c r p m s j
      · by_cases hlt : l < j
        · have hw_mem := (mem_waiting_of_mem_runSet_lt c r p w elig m s hG hl).1 hlt
          simp [hl, hlt, hw_mem]
        · have hnot : l ∉ waiting r m s (m j) j := by
            intro hw_mem
            exact hlt (Finset.mem_filter.mp hw_mem).2.1
          simp [hl, hlt, hnot]
      · simp [hl]
    have hpart2 : ∑ a : Fin n, ∑ b ∈ waiting r m s (m a) a,
          (if a ∈ runSet c r p m s b then w b * p (m b) a else 0) =
        ∑ j : Fin n, ∑ l : Fin n,
          (if l ∈ runSet c r p m s j ∧ j < l then w j * p (m j) l else 0) := by
      simp_rw [sum_finset_eq_sum_univ (waiting r m s _ _)]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
      by_cases hl : l ∈ runSet c r p m s j
      · by_cases hgt : j < l
        · have hw_mem := (mem_waiting_of_mem_runSet_lt c r p w elig m s hG hl).2 hgt
          simp [hl, hgt, hw_mem]
        · have hnot : j ∉ waiting r m s (m l) l := by
            intro hw_mem
            exact hgt (Finset.mem_filter.mp hw_mem).2.1
          simp [hl, hgt, hnot]
      · simp [hl]
    rw [hpart1, hpart2, ← Finset.sum_add_distrib]
    refine le_of_eq (Finset.sum_congr rfl (fun j _ => ?_))
    rw [Finset.mul_sum, sum_finset_eq_sum_univ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    by_cases hl : l ∈ runSet c r p m s j
    · have hsl : s l < s j := (Finset.mem_filter.mp hl).2.2.2
      have hne : l ≠ j := by
        intro heq; subst heq; linarith
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hn : ¬ j < l := not_lt_of_gt hlt
        simp [hl, hlt, hn]
      · have hn : ¬ l < j := not_lt_of_gt hgt
        simp [hl, hgt, hn]
    · simp [hl]
  unfold nominalValue nominalCompletion
  have hjob : ∀ j : Fin n,
      w j * (s j + p (m j) j) ≤
        w j * ((1 + 1 / c) * modRelease c r p (m j) j + p (m j) j) +
          w j * ∑ l ∈ runSet c r p m s j, p (m j) l := by
    intro j
    have hsj := start_le_bound elig r p hp w c hc m s hG j
    have hmul := mul_le_mul_of_nonneg_left (add_le_add_right hsj (p (m j) j)) (hw j)
    linarith
  have hsum_jobs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun j _ => hjob j)
  rw [Finset.sum_add_distrib] at hsum_jobs
  linarith
