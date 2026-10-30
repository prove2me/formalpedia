-- Prove2me | solution 1 for MirrorBP.JEA.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T18:33:20.812346+00:00
-- url     : https://prove2.me/submissions/8c5f56b3-4329-4ccc-b245-7a7354ed76d9

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_SPP

set_option linter.unusedSectionVars false

namespace MirrorBP.JEA.Lemma5Aux

open Finset MirrorBP.JEA

variable {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]

/-- total flow on admissible triples -/
def tot (P D : Ty → Finset V) (y : V → Ty → V → ℝ) : ℝ :=
  ∑ τ, ∑ j ∈ P τ, ∑ k ∈ D τ, y j τ k

/-- number of occurrences of the triple `(a, τ', b)` along a walk of length `s` -/
noncomputable def cnt (s : ℕ) (j : ℕ → V) (τ : ℕ → Ty) (a : V) (τ' : Ty) (b : V) : ℝ :=
  ∑ r ∈ range s, if j r = a ∧ τ r = τ' ∧ j (r + 1) = b then (1 : ℝ) else 0

theorem collapse (P D : Ty → Finset V) (j : ℕ → V) (τ : ℕ → Ty) (r : ℕ)
    (hmem : j r ∈ P (τ r) ∧ j (r + 1) ∈ D (τ r)) (g : V → Ty → V → ℝ) :
    ∑ τ', ∑ a ∈ P τ', ∑ b ∈ D τ',
      (if j r = a ∧ τ r = τ' ∧ j (r + 1) = b then (1 : ℝ) else 0) * g a τ' b
      = g (j r) (τ r) (j (r + 1)) := by
  rw [Finset.sum_eq_single (τ r)]
  · rw [Finset.sum_eq_single_of_mem (j r) hmem.1]
    · rw [Finset.sum_eq_single_of_mem (j (r + 1)) hmem.2]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
    · intro a _ ha
      apply Finset.sum_eq_zero
      intro b _
      simp [Ne.symm ha]
  · intro τ' _ hτ
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    simp [Ne.symm hτ]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem cnt_sum (P D : Ty → Finset V) (j : ℕ → V) (τ : ℕ → Ty) (g : V → Ty → V → ℝ) :
    ∀ s : ℕ, (∀ r < s, j r ∈ P (τ r) ∧ j (r + 1) ∈ D (τ r)) →
    ∑ τ', ∑ a ∈ P τ', ∑ b ∈ D τ', cnt s j τ a τ' b * g a τ' b
      = ∑ r ∈ range s, g (j r) (τ r) (j (r + 1)) := by
  intro s
  induction s with
  | zero => intro _; simp [cnt]
  | succ s ih =>
    intro hmem
    have h1 := ih (fun r hr => hmem r (by omega))
    have h2 := collapse P D j τ s (hmem s (by omega)) g
    simp only [cnt, Finset.sum_range_succ, add_mul, Finset.sum_add_distrib] at h1 h2 ⊢
    rw [h1, h2]

theorem cnt_nonneg (s : ℕ) (j : ℕ → V) (τ : ℕ → Ty) (a : V) (τ' : Ty) (b : V) :
    0 ≤ cnt s j τ a τ' b := by
  unfold cnt
  apply Finset.sum_nonneg
  intro r _
  split_ifs <;> norm_num

theorem cnt_le (s : ℕ) (j : ℕ → V) (τ : ℕ → Ty) (a : V) (τ' : Ty) (b : V) :
    cnt s j τ a τ' b ≤ s := by
  unfold cnt
  calc (∑ r ∈ range s, if j r = a ∧ τ r = τ' ∧ j (r + 1) = b then (1 : ℝ) else 0)
      ≤ ∑ r ∈ range s, (1 : ℝ) := by
        apply Finset.sum_le_sum; intro r _; split_ifs <;> norm_num
    _ = s := by simp

theorem netOut_sub (P D : Ty → Finset V) (y c : V → Ty → V → ℝ) (ε : ℝ) (S : Finset V) :
    netOut P D (fun a τ b => y a τ b - ε * c a τ b) S = netOut P D y S - ε * netOut P D c S := by
  simp only [netOut, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => by ring

theorem tot_sub (P D : Ty → Finset V) (y c : V → Ty → V → ℝ) (ε : ℝ) :
    tot P D (fun a τ b => y a τ b - ε * c a τ b) = tot P D y - ε * tot P D c := by
  simp only [tot, Finset.mul_sum, ← Finset.sum_sub_distrib]

theorem netOut_cycle (P D : Ty → Finset V) (s : ℕ) (j : ℕ → V) (τ : ℕ → Ty)
    (hmem : ∀ r < s, j r ∈ P (τ r) ∧ j (r + 1) ∈ D (τ r)) (hcl : j s = j 0) (S : Finset V) :
    netOut P D (cnt s j τ) S = 0 := by
  unfold netOut
  rw [cnt_sum P D j τ (fun a _ b => (if a ∈ S then (1 : ℝ) else 0) - (if b ∈ S then 1 else 0)) s hmem]
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  have e1 := Finset.sum_range_succ (fun r => if j r ∈ S then (1 : ℝ) else 0) s
  have e2 := Finset.sum_range_succ' (fun r => if j r ∈ S then (1 : ℝ) else 0) s
  rw [hcl] at e1
  linarith

theorem tot_cycle (P D : Ty → Finset V) (s : ℕ) (j : ℕ → V) (τ : ℕ → Ty)
    (hmem : ∀ r < s, j r ∈ P (τ r) ∧ j (r + 1) ∈ D (τ r)) :
    tot P D (cnt s j τ) = s := by
  have := cnt_sum P D j τ (fun _ _ _ => 1) s hmem
  simp only [mul_one] at this
  unfold tot; rw [this]; simp

theorem sum_ind_range (M n : ℕ) (h : n ≤ M) :
    (∑ l ∈ range M, if l < n then (1 : ℝ) else 0) = n := by
  rw [Finset.sum_boole]
  have : (range M).filter (fun l => l < n) = range n := by
    ext l; simp; omega
  rw [this]; simp


/-- strict reachability along admissible triples with positive flow -/
def SReach (P D : Ty → Finset V) (y : V → Ty → V → ℝ) (a c : V) : Prop :=
  ∃ s : ℕ, 0 < s ∧ ∃ j : ℕ → V, ∃ τ : ℕ → Ty, j 0 = a ∧ j s = c ∧
    ∀ r < s, j r ∈ P (τ r) ∧ j (r + 1) ∈ D (τ r) ∧ 0 < y (j r) (τ r) (j (r + 1))

theorem sreach_edge (P D : Ty → Finset V) (y : V → Ty → V → ℝ) (a b : V) (τ0 : Ty)
    (ha : a ∈ P τ0) (hb : b ∈ D τ0) (hy : 0 < y a τ0 b) : SReach P D y a b := by
  refine ⟨1, by norm_num, fun n => if n = 0 then a else b, fun _ => τ0, by simp, by simp, ?_⟩
  intro r hr
  have : r = 0 := by omega
  subst this
  simp [ha, hb, hy]

theorem sreach_prepend (P D : Ty → Finset V) (y : V → Ty → V → ℝ) (a b c : V) (τ0 : Ty)
    (ha : a ∈ P τ0) (hb : b ∈ D τ0) (hy : 0 < y a τ0 b) (h : SReach P D y b c) :
    SReach P D y a c := by
  obtain ⟨s, hs, j, τ, h0, hsj, hr⟩ := h
  refine ⟨s + 1, by omega, fun n => if n = 0 then a else j (n - 1),
    fun n => if n = 0 then τ0 else τ (n - 1), by simp, by simp [hsj], ?_⟩
  intro r hr'
  rcases Nat.eq_zero_or_pos r with h | h
  · subst h; simp [ha, hy, h0, hb]
  · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have := hr r' (by omega)
    simpa using this

theorem exists_acyclic (P D : Ty → Finset V) (z : V → Ty → V → ℝ)
    (hz0 : ∀ τ, ∀ a ∈ P τ, ∀ b ∈ D τ, 0 ≤ z a τ b) :
    ∃ y : V → Ty → V → ℝ, (∀ a τ b, 0 ≤ y a τ b) ∧
      (∀ τ, ∀ a ∈ P τ, ∀ b ∈ D τ, y a τ b ≤ z a τ b) ∧
      (∀ S, netOut P D y S = netOut P D z S) ∧ (∀ a, ¬ SReach P D y a a) := by
  classical
  let zc : V → Ty → V → ℝ := fun a τ b => if a ∈ P τ ∧ b ∈ D τ then z a τ b else 0
  have hzc0 : 0 ≤ zc := by
    intro a τ b
    show 0 ≤ zc a τ b
    simp only [zc]
    split_ifs with h
    · exact hz0 τ a h.1 b h.2
    · exact le_rfl
  have hnet_zc : ∀ S, netOut P D zc S = netOut P D z S := by
    intro S
    unfold netOut
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a ha =>
      Finset.sum_congr rfl fun b hb => ?_
    simp [zc, ha, hb]
  let Y : Set (V → Ty → V → ℝ) :=
    Set.Icc 0 zc ∩ {y | ∀ S, netOut P D y S = netOut P D z S}
  have hcont_net : ∀ S, Continuous (fun y : V → Ty → V → ℝ => netOut P D y S) := by
    intro S
    unfold netOut
    fun_prop
  have hcont_tot : Continuous (fun y : V → Ty → V → ℝ => tot P D y) := by
    unfold tot
    fun_prop
  have hYc : IsCompact Y := by
    apply isCompact_Icc.inter_right
    have : {y : V → Ty → V → ℝ | ∀ S, netOut P D y S = netOut P D z S}
        = ⋂ S, {y | netOut P D y S = netOut P D z S} := by
      ext y; simp
    rw [this]
    exact isClosed_iInter fun S => isClosed_eq (hcont_net S) continuous_const
  have hYne : Y.Nonempty := ⟨zc, ⟨hzc0, le_rfl⟩, hnet_zc⟩
  obtain ⟨y, hyY, hmin⟩ := hYc.exists_isMinOn hYne hcont_tot.continuousOn
  obtain ⟨⟨hy0, hyz⟩, hynet⟩ := hyY
  refine ⟨y, fun a τ b => hy0 a τ b, ?_, hynet, ?_⟩
  · intro τ a ha b hb
    have := hyz a τ b
    simpa [zc, ha, hb] using this
  · rintro a ⟨s, hs, j, τ, h0, hsj, hr⟩
    have hmem : ∀ r < s, j r ∈ P (τ r) ∧ j (r + 1) ∈ D (τ r) :=
      fun r h => ⟨(hr r h).1, (hr r h).2.1⟩
    have hne : (range s).Nonempty := ⟨0, by simp [hs]⟩
    set m0 := (range s).inf' hne (fun r => y (j r) (τ r) (j (r + 1))) with hm0
    have hm0pos : 0 < m0 := by
      rw [hm0, Finset.lt_inf'_iff]
      intro r hr'
      exact (hr r (by simpa using hr')).2.2
    have hspos : (0 : ℝ) < s := by exact_mod_cast hs
    set ε := m0 / s with hε
    have hεpos : 0 < ε := div_pos hm0pos hspos
    let y' : V → Ty → V → ℝ := fun a τ' b => y a τ' b - ε * cnt s j τ a τ' b
    have hy'Y : y' ∈ Y := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro a' τ' b'
        show 0 ≤ y a' τ' b' - ε * cnt s j τ a' τ' b'
        by_cases hc : cnt s j τ a' τ' b' = 0
        · rw [hc, mul_zero, sub_zero]; exact hy0 a' τ' b'
        · obtain ⟨r, hrs, hrm⟩ : ∃ r ∈ range s, j r = a' ∧ τ r = τ' ∧ j (r + 1) = b' := by
            by_contra hcon
            push_neg at hcon
            apply hc
            unfold cnt
            apply Finset.sum_eq_zero
            intro r hrs
            rw [if_neg]
            intro hh
            exact hcon r hrs hh.1 hh.2.1 hh.2.2
          obtain ⟨e1, e2, e3⟩ := hrm
          have hle : m0 ≤ y a' τ' b' := by
            rw [← e1, ← e2, ← e3]
            exact Finset.inf'_le _ hrs
          have hcl := cnt_le s j τ a' τ' b'
          have : ε * cnt s j τ a' τ' b' ≤ m0 := by
            calc ε * cnt s j τ a' τ' b' ≤ ε * s :=
                  mul_le_mul_of_nonneg_left hcl hεpos.le
              _ = m0 := by rw [hε]; field_simp
          linarith
      · intro a' τ' b'
        show y a' τ' b' - ε * cnt s j τ a' τ' b' ≤ zc a' τ' b'
        have := hyz a' τ' b'
        have := cnt_nonneg s j τ a' τ' b'
        have : 0 ≤ ε * cnt s j τ a' τ' b' := mul_nonneg hεpos.le this
        linarith
      · intro S
        show netOut P D (fun a τ' b => y a τ' b - ε * cnt s j τ a τ' b) S = netOut P D z S
        rw [netOut_sub, netOut_cycle P D s j τ hmem (by rw [hsj, h0]) S, mul_zero, sub_zero]
        exact hynet S
    have h1 := hmin hy'Y
    simp only [Set.mem_setOf_eq] at h1
    have h2 : tot P D y' = tot P D y - ε * s := by
      show tot P D (fun a τ' b => y a τ' b - ε * cnt s j τ a τ' b) = _
      rw [tot_sub, tot_cycle P D s j τ hmem]
    have : 0 < ε * s := mul_pos hεpos hspos
    linarith

theorem tot_le_of_acyclic (P D : Ty → Finset V) (y z : V → Ty → V → ℝ) (r : ℝ)
    (hy0 : ∀ a τ b, 0 ≤ y a τ b) (hnet : ∀ S, netOut P D y S = netOut P D z S)
    (hacyc : ∀ a, ¬ SReach P D y a a) (hr : ∀ S, |netOut P D z S| ≤ r) :
    tot P D y ≤ ((Fintype.card V - 1 : ℕ) : ℝ) * r := by
  classical
  let rk : V → ℕ := fun a => (univ.filter (fun c => SReach P D y a c)).card
  have hrk_le : ∀ a, rk a ≤ Fintype.card V - 1 := by
    intro a
    have hsub : univ.filter (fun c => SReach P D y a c) ⊆ univ.erase a := by
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      rintro rfl
      exact hacyc c hc
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at this
    exact this
  have hrk_lt : ∀ τ, ∀ a ∈ P τ, ∀ b ∈ D τ, 0 < y a τ b → rk b < rk a := by
    intro τ a ha b hb hpos
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨b, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact sreach_edge P D y a b τ ha hb hpos
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hacyc b
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact sreach_prepend P D y a b c τ ha hb hpos hc
  set M := Fintype.card V - 1 with hM
  let A : ℕ → Finset V := fun l => univ.filter (fun i => l < rk i)
  have key : ∑ l ∈ range M, netOut P D y (A l)
      = ∑ τ, ∑ a ∈ P τ, ∑ b ∈ D τ, y a τ b * ((rk a : ℝ) - rk b) := by
    unfold netOut
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    have e1 := sum_ind_range M (rk a) (hrk_le a)
    have e2 := sum_ind_range M (rk b) (hrk_le b)
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [e1, e2]
  have hge : tot P D y ≤ ∑ l ∈ range M, netOut P D y (A l) := by
    rw [key]
    unfold tot
    refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun a ha =>
      Finset.sum_le_sum fun b hb => ?_
    rcases (hy0 a τ b).lt_or_eq with hpos | hzero
    · have := hrk_lt τ a ha b hb hpos
      have : (rk b : ℝ) + 1 ≤ rk a := by exact_mod_cast this
      nlinarith
    · rw [← hzero]; simp
  have hle : ∑ l ∈ range M, netOut P D y (A l) ≤ ∑ l ∈ range M, r := by
    refine Finset.sum_le_sum fun l _ => ?_
    rw [hnet]
    exact (le_abs_self _).trans (hr _)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
  linarith


end MirrorBP.JEA.Lemma5Aux

open MirrorBP.JEA MirrorBP.JEA.Lemma5Aux Finset

theorem solution {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
    (P D : Ty → Finset V) (w : V → Ty → V → ℝ)
    (hm : 1 < Fintype.card V) (hP : ∀ τ, (P τ).Nonempty) (hD : ∀ τ, (D τ).Nonempty)
    (hw : ∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1)
    (φ : Ty → ℝ) (r : ℝ) (z : V → Ty → V → ℝ) (hz : relaxedFeasZ P D φ r z) :
    ∃ zS zD : V → Ty → V → ℝ,
      (∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, z j τ k = zS j τ k + zD j τ k) ∧
      sppFeasZ P D φ zS ∧ IsAcyclicFlow P D zD ∧ relaxedFeasZ P D φ r zD := by
  obtain ⟨y, hy0, hyz, hynet, hacyc⟩ := exists_acyclic P D z hz.1.2
  refine ⟨fun a τ b => z a τ b - 1 * y a τ b, y, fun τ j _ k _ => by ring, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i
    rw [netOut_sub, hynet, one_mul, sub_self]
  · intro τ
    calc ∑ j ∈ P τ, ∑ k ∈ D τ, (z j τ k - 1 * y j τ k) ≤ ∑ j ∈ P τ, ∑ k ∈ D τ, z j τ k := by
          refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
          linarith [hy0 j τ k]
      _ ≤ φ τ := hz.1.1 τ
  · intro τ j hj k hk
    show 0 ≤ z j τ k - 1 * y j τ k
    linarith [hyz τ j hj k hk]
  · intro s j τ hs hcl hall
    exact hacyc (j 0) ⟨s, hs, j, τ, rfl, hcl, hall⟩
  · refine ⟨⟨fun τ => ?_, fun τ j _ k _ => hy0 j τ k⟩, fun S => ?_⟩
    · calc ∑ j ∈ P τ, ∑ k ∈ D τ, y j τ k ≤ ∑ j ∈ P τ, ∑ k ∈ D τ, z j τ k :=
            Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => hyz τ j hj k hk
        _ ≤ φ τ := hz.1.1 τ
    · rw [hynet]; exact hz.2 S
