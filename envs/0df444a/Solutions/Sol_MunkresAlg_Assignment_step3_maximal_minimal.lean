-- Prove2me | solution 1 for MunkresAlg.Assignment.step3_maximal_minimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:44:06.525321+00:00
-- url     : https://prove2.me/submissions/41a07509-6ce0-465b-9399-82b1d2e4dd90

import Mathlib
import Definitions.Def_HeldWolfeCrowder_Assignment_Setting
import Definitions.Def_MunkresAlg_Assignment_Basic
import Definitions.Def_MunkresAlg_Assignment_Algorithm



namespace MunkresAlg.Assignment

open Classical

inductive Seq {n : ℕ} (s : State n) : List (Fin n × Fin n) → Prop
  | last (p : Fin n × Fin n) (h : ∀ q ∈ s.starred, q.2 ≠ p.2) : Seq s [p]
  | cons (p w q : Fin n × Fin n) (rest : List (Fin n × Fin n)) (hw : w ∈ s.starred)
      (hc : w.2 = p.2) (hq : q ∈ s.primed) (hr : q.1 = w.1) (h : Seq s (q :: rest)) :
      Seq s (p :: w :: q :: rest)

def IsAlt {n : ℕ} (s : State n) (zs : List (Fin n × Fin n)) : Prop :=
  zs.length % 2 = 1 ∧
  (∀ i (h : 2 * i + 1 < zs.length),
      zs[2 * i + 1] ∈ s.starred ∧ zs[2 * i + 1].2 = zs[2 * i].2) ∧
  (∀ i (h : 2 * i + 2 < zs.length),
      zs[2 * i + 2] ∈ s.primed ∧ zs[2 * i + 2].1 = zs[2 * i + 1].1) ∧
  (∀ z ∈ zs.getLast?, ∀ q ∈ s.starred, q.2 ≠ z.2)

theorem alt_of_seq {n : ℕ} {s : State n} {zs : List (Fin n × Fin n)} (h : Seq s zs) :
    IsAlt s zs := by
  induction h with
  | last p h =>
    refine ⟨by simp, ?_, ?_, ?_⟩
    · intro i hi; exact absurd hi (by simp)
    · intro i hi; exact absurd hi (by simp)
    · intro z hz; simp at hz; subst hz; exact h
  | cons p w q rest hw hc hq hr h ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp at h1 ⊢; omega
    · intro i hi
      rcases i with _ | i
      · exact ⟨hw, hc⟩
      · have := h2 i (by simp at hi ⊢; omega)
        simp only [Nat.mul_succ, List.getElem_cons_succ]
        simpa using this
    · intro i hi
      rcases i with _ | i
      · exact ⟨hq, hr⟩
      · have := h3 i (by simp at hi ⊢; omega)
        simp only [Nat.mul_succ, List.getElem_cons_succ]
        simpa using this
    · intro z hz
      simp only [List.getLast?_cons_cons] at hz
      exact h4 z hz

theorem seq_of_alt {n : ℕ} {s : State n} : ∀ (N : ℕ) (zs : List (Fin n × Fin n)), zs.length ≤ N →
    zs ≠ [] → IsAlt s zs → Seq s zs := by
  intro N
  induction N with
  | zero => intro zs hl hne; exact absurd (List.length_eq_zero_iff.mp (by omega)) hne
  | succ N ih =>
    intro zs hl _ hA
    obtain ⟨h1, h2, h3, h4⟩ := hA
    rcases zs with _ | ⟨p, l⟩
    · simp at h1
    rcases l with _ | ⟨w, l⟩
    · apply Seq.last
      intro q hq; exact h4 p (by simp) q hq
    · rcases l with _ | ⟨q, rest⟩
      · simp at h1
      · have e1 := h2 0 (by simp)
        have e2 := h3 0 (by simp)
        simp at e1 e2
        apply Seq.cons p w q rest e1.1 e1.2 e2.1 e2.2
        apply ih (q :: rest) (by simp at hl ⊢; omega) (by simp)
        refine ⟨by simp at h1 ⊢; omega, ?_, ?_, ?_⟩
        · intro i hi
          have := h2 (i+1) (by simp at hi ⊢; omega)
          simp only [Nat.mul_succ, List.getElem_cons_succ] at this
          simpa using this
        · intro i hi
          have := h3 (i+1) (by simp at hi ⊢; omega)
          simp only [Nat.mul_succ, List.getElem_cons_succ] at this
          simpa using this
        · intro z hz
          apply h4 z
          simpa [List.getLast?_cons_cons] using hz

theorem isStep2Seq_iff {n : ℕ} (s : State n) (z₀ : Fin n × Fin n) (zs : List (Fin n × Fin n)) :
    IsStep2Seq s z₀ zs ↔ zs.head? = some z₀ ∧ Seq s zs := by
  constructor
  · rintro ⟨h0, h1, h2, h3, h4⟩
    refine ⟨h0, seq_of_alt zs.length zs le_rfl ?_ ⟨h1, h2, h3, h4⟩⟩
    rintro rfl; simp at h0
  · rintro ⟨h0, hs⟩
    obtain ⟨h1, h2, h3, h4⟩ := alt_of_seq hs
    exact ⟨h0, h1, h2, h3, h4⟩

theorem greedyStar_inv {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (L : List (Fin n × Fin n)) :
    ∀ S : Finset (Fin n × Fin n), IsIndepZeros B S →
      IsIndepZeros B (L.foldl (fun S z => if B z.1 z.2 = 0 ∧ ∀ q ∈ S, q.1 ≠ z.1 ∧ q.2 ≠ z.2 then insert z S else S) S) := by
  induction L with
  | nil => intro S h; exact h
  | cons z L ih =>
    intro S hS
    simp only [List.foldl_cons]
    apply ih
    split_ifs with hc
    · obtain ⟨hI, hz⟩ := hS
      refine ⟨?_, ?_⟩
      · intro p hp q hq hpq
        rw [Finset.mem_insert] at hp hq
        rcases hp with rfl | hp <;> rcases hq with rfl | hq
        · exact absurd rfl hpq
        · have := hc.2 q hq
          exact ⟨fun h => this.1 h.symm, fun h => this.2 h.symm⟩
        · exact hc.2 p hp
        · exact hI p hp q hq hpq
      · intro p hp
        rw [Finset.mem_insert] at hp
        rcases hp with rfl | hp
        · exact hc.1
        · exact hz p hp
    · exact hS

theorem ps_core {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n)
    (hs : IsStart A s) :
    IsIndepZeros s.A s.starred := by
  obtain ⟨L, -, -, rfl⟩ := hs
  have h := greedyStar_inv (prelimMatrix A) L ∅ ⟨by intro p hp; simp at hp, by intro p hp; simp at hp⟩
  unfold enterStep1
  split_ifs <;> exact h


structure Inv {n : ℕ} (s : State n) (rk : Fin n × Fin n → ℕ) : Prop where
  nonneg : ∀ i j, 0 ≤ s.A i j
  indep : IsIndepZeros s.A s.starred
  pzero : ∀ p ∈ s.primed, s.A p.1 p.2 = 0
  prow : ∀ p ∈ s.primed, ∀ q ∈ s.primed, p.1 = q.1 → p = q
  pnotstar : ∀ p ∈ s.primed, p ∉ s.starred
  once : ∀ z ∈ s.starred, (z.1 ∈ s.rowCov ↔ z.2 ∉ s.colCov)
  rowstar : ∀ r ∈ s.rowCov, ∃ z ∈ s.starred, z.1 = r
  rowprime : ∀ r ∈ s.rowCov, ∃ p ∈ s.primed, p.1 = r
  colstar : ∀ c ∈ s.colCov, ∃ z ∈ s.starred, z.2 = c
  pcol : ∀ p ∈ s.primed, p.2 ∉ s.colCov
  prowcov : ∀ p ∈ s.primed, p.1 ∈ s.rowCov ∨ s.phase = Phase.step2 p
  s2 : ∀ z₀, s.phase = Phase.step2 z₀ → z₀ ∈ s.primed ∧ NonCovered s z₀ ∧
      (∀ q ∈ s.starred, q.1 ≠ z₀.1) ∧ (∀ p ∈ s.primed, p ≠ z₀ → p.1 ∈ s.rowCov)
  order : ∀ p ∈ s.primed, ∀ w ∈ s.starred, w.2 = p.2 →
      ∃ q ∈ s.primed, q.1 = w.1 ∧ rk q < rk p
  s3 : s.phase = Phase.step3 → ∀ p, NonCovered s p → s.A p.1 p.2 ≠ 0
  small : s.phase ≠ Phase.done → s.starred.card < n
  donecol : s.phase = Phase.done → colsOf s.starred = Finset.univ

theorem card_colsOf {n : ℕ} {S : Finset (Fin n × Fin n)} (h : Independent S) :
    (colsOf S).card = S.card := by
  unfold colsOf
  apply Finset.card_image_of_injOn
  intro p hp q hq hpq
  by_contra hne
  exact (h p hp q hq hne).2 hpq

theorem small_of {n : ℕ} {S : Finset (Fin n × Fin n)} (h : Independent S)
    (hne : colsOf S ≠ Finset.univ) : S.card < n := by
  rw [← card_colsOf h]
  have := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hne)
  simpa using this

theorem inv_reset_aux {n : ℕ} (u : State n) (rk : Fin n × Fin n → ℕ) (ph : Phase n)
    (hA : ∀ i j, 0 ≤ u.A i j) (hind : IsIndepZeros u.A u.starred) (hp : u.primed = ∅)
    (hr : u.rowCov = ∅) (hc : u.colCov = colsOf u.starred)
    (hph : ph = Phase.step1 ∨ ph = Phase.done)
    (hne : ph ≠ Phase.done → colsOf u.starred ≠ Finset.univ)
    (hdone : ph = Phase.done → colsOf u.starred = Finset.univ) :
    Inv { u with phase := ph } rk := by
  have hp3 : ph ≠ Phase.step3 := by rcases hph with h | h <;> rw [h] <;> simp
  have hp2 : ∀ z, ph ≠ Phase.step2 z := by intro z; rcases hph with h | h <;> rw [h] <;> simp
  have e1 : ({ u with phase := ph } : State n).primed = ∅ := hp
  have e2 : ({ u with phase := ph } : State n).rowCov = ∅ := hr
  have e3 : ({ u with phase := ph } : State n).colCov = colsOf u.starred := hc
  refine ⟨hA, hind, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hdone⟩
  · intro p hp'; rw [e1] at hp'; exact absurd hp' (Finset.notMem_empty _)
  · intro p hp'; rw [e1] at hp'; exact absurd hp' (Finset.notMem_empty _)
  · intro p hp'; rw [e1] at hp'; exact absurd hp' (Finset.notMem_empty _)
  · intro z hz
    show z.1 ∈ ({ u with phase := ph } : State n).rowCov ↔ z.2 ∉ ({ u with phase := ph } : State n).colCov
    rw [e2, e3]
    simp only [Finset.notMem_empty, false_iff, not_not]
    unfold colsOf
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  · intro r hr'; rw [e2] at hr'; exact absurd hr' (Finset.notMem_empty _)
  · intro r hr'; rw [e2] at hr'; exact absurd hr' (Finset.notMem_empty _)
  · intro c hc'
    rw [e3] at hc'
    unfold colsOf at hc'
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc'
    exact ⟨z, hz, rfl⟩
  · intro p hp'; rw [e1] at hp'; exact absurd hp' (Finset.notMem_empty _)
  · intro p hp'; rw [e1] at hp'; exact absurd hp' (Finset.notMem_empty _)
  · intro z hz; exact absurd hz (hp2 z)
  · intro p hp'; rw [e1] at hp'; exact absurd hp' (Finset.notMem_empty _)
  · intro h; exact absurd h hp3
  · intro h; exact small_of hind.1 (hne h)

theorem inv_reset {n : ℕ} (u : State n) (rk : Fin n × Fin n → ℕ)
    (hA : ∀ i j, 0 ≤ u.A i j) (hind : IsIndepZeros u.A u.starred) (hp : u.primed = ∅)
    (hr : u.rowCov = ∅) (hc : u.colCov = colsOf u.starred) :
    Inv (enterStep1 u) rk := by
  unfold enterStep1
  split_ifs with h
  · exact inv_reset_aux u rk _ hA hind hp hr hc (Or.inr rfl) (by intro h'; exact absurd rfl h') (fun _ => by rw [← hc]; exact h)
  · exact inv_reset_aux u rk _ hA hind hp hr hc (Or.inl rfl) (by rw [← hc]; exact h |> fun x => fun _ => x) (fun h' => absurd h' (by simp))

theorem rowReduce_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    0 ≤ rowReduce A i j := by
  unfold rowReduce
  have : _ ≤ A i j := Finset.inf'_le (A i) (Finset.mem_univ j)
  linarith

theorem prelim_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    0 ≤ prelimMatrix A i j := by
  unfold prelimMatrix colReduce
  have : _ ≤ rowReduce A i j := Finset.inf'_le (fun i' => rowReduce A i' j) (Finset.mem_univ i)
  have h2 := rowReduce_nonneg A i j
  linarith

theorem inv_start {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n) (hs : IsStart A s) :
    Inv s (fun _ => 0) := by
  obtain ⟨L, -, -, rfl⟩ := hs
  apply inv_reset
  · exact prelim_nonneg A
  · exact greedyStar_inv (prelimMatrix A) L ∅ ⟨by intro p hp; simp at hp, by intro p hp; simp at hp⟩
  · rfl
  · rfl
  · rfl


theorem not_nc_of_star {n : ℕ} {s : State n} {rk : Fin n × Fin n → ℕ} (hI : Inv s rk)
    {z : Fin n × Fin n} (hz : z ∈ s.starred) : ¬ NonCovered s z :=
  fun ⟨h1, h2⟩ => h1 ((hI.once z hz).2 h2)

theorem prime_old_notnc {n : ℕ} {s : State n} {rk : Fin n × Fin n → ℕ} (hI : Inv s rk)
    (hphase : s.phase = Phase.step1) {p : Fin n × Fin n} (hnc : NonCovered s p) :
    p ∉ s.primed := by
  intro hp
  rcases hI.prowcov p hp with h | h
  · exact hnc.1 h
  · rw [hphase] at h; exact absurd h (by simp)

theorem inv_prime_go2 {n : ℕ} {s : State n} {rk : Fin n × Fin n → ℕ} (hI : Inv s rk)
    (p : Fin n × Fin n) (hphase : s.phase = Phase.step1) (hzero : s.A p.1 p.2 = 0)
    (hnc : NonCovered s p) (hnostar : ∀ q ∈ s.starred, q.1 ≠ p.1) :
    Inv { s with primed := insert p s.primed, phase := Phase.step2 p }
      (Function.update rk p (s.primed.sup rk + 1)) := by
  have hpn : p ∉ s.primed := prime_old_notnc hI hphase hnc
  have hold : ∀ q ∈ s.primed, q.1 ∈ s.rowCov := by
    intro q hq
    rcases hI.prowcov q hq with h | h
    · exact h
    · rw [hphase] at h; exact absurd h (by simp)
  have hrk : ∀ q ∈ s.primed, Function.update rk p (s.primed.sup rk + 1) q = rk q := by
    intro q hq
    have : q ≠ p := fun h => hpn (h ▸ hq)
    simp [Function.update_apply, this]
  have hrkp : Function.update rk p (s.primed.sup rk + 1) p = s.primed.sup rk + 1 := by simp
  refine ⟨hI.nonneg, hI.indep, ?_, ?_, ?_, hI.once, hI.rowstar, ?_, hI.colstar, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hzero
    · exact hI.pzero q hq
  · intro q hq q' hq' hrow
    have hq0 : q ∈ insert p s.primed := hq
    have hq0' : q' ∈ insert p s.primed := hq'
    rcases Finset.mem_insert.mp hq0 with h1 | h1 <;> rcases Finset.mem_insert.mp hq0' with h2 | h2
    · rw [h1, h2]
    · have := hold q' h2
      rw [← hrow, h1] at this
      exact absurd this hnc.1
    · have := hold q h1
      rw [hrow, h2] at this
      exact absurd this hnc.1
    · exact hI.prow q h1 q' h2 hrow
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact fun h => not_nc_of_star hI h hnc
    · exact hI.pnotstar q hq
  · intro r hr
    obtain ⟨q, hq, h⟩ := hI.rowprime r hr
    exact ⟨q, Finset.mem_insert_of_mem hq, h⟩
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hnc.2
    · exact hI.pcol q hq
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Or.inr rfl
    · exact Or.inl (hold q hq)
  · intro z0 hz0
    have : p = z0 := by
      have := hz0
      simp only [Phase.step2.injEq] at this
      exact this
    subst this
    refine ⟨Finset.mem_insert_self _ _, hnc, hnostar, ?_⟩
    intro q hq hne
    replace hq : q ∈ insert _ s.primed := hq
    rcases Finset.mem_insert.mp hq with h | hq
    · exact absurd h hne
    · exact hold q hq
  · intro q hq w hw hwq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · have h1 : w.1 ∈ s.rowCov := (hI.once w hw).2 (hwq ▸ hnc.2)
      obtain ⟨q', hq', hq'1⟩ := hI.rowprime w.1 h1
      refine ⟨q', Finset.mem_insert_of_mem hq', hq'1, ?_⟩
      rw [hrk q' hq', hrkp]
      have := Finset.le_sup (f := rk) hq'
      omega
    · obtain ⟨q', hq', h1, h2⟩ := hI.order q hq w hw hwq
      refine ⟨q', Finset.mem_insert_of_mem hq', h1, ?_⟩
      rw [hrk q' hq', hrk q hq]; exact h2
  · intro h; exact absurd h (by simp)
  · intro h; exact hI.small (by rw [hphase]; simp)
  · intro h; exact absurd h (by simp)

theorem inv_prime_cover {n : ℕ} {s : State n} {rk : Fin n × Fin n → ℕ} (hI : Inv s rk)
    (p z : Fin n × Fin n) (hphase : s.phase = Phase.step1) (hzero : s.A p.1 p.2 = 0)
    (hnc : NonCovered s p) (hz : z ∈ s.starred) (hrow : z.1 = p.1) :
    Inv { s with primed := insert p s.primed, rowCov := insert p.1 s.rowCov,
                 colCov := s.colCov.erase z.2 }
      (Function.update rk p (s.primed.sup rk + 1)) := by
  have hpn : p ∉ s.primed := prime_old_notnc hI hphase hnc
  have hold : ∀ q ∈ s.primed, q.1 ∈ s.rowCov := by
    intro q hq
    rcases hI.prowcov q hq with h | h
    · exact h
    · rw [hphase] at h; exact absurd h (by simp)
  have hrk : ∀ q ∈ s.primed, Function.update rk p (s.primed.sup rk + 1) q = rk q := by
    intro q hq
    have : q ≠ p := fun h => hpn (h ▸ hq)
    simp [Function.update_apply, this]
  have hrkp : Function.update rk p (s.primed.sup rk + 1) p = s.primed.sup rk + 1 := by simp
  refine ⟨hI.nonneg, hI.indep, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hzero
    · exact hI.pzero q hq
  · intro q hq q' hq' hrow'
    have hq0 : q ∈ insert p s.primed := hq
    have hq0' : q' ∈ insert p s.primed := hq'
    rcases Finset.mem_insert.mp hq0 with h1 | h1 <;> rcases Finset.mem_insert.mp hq0' with h2 | h2
    · rw [h1, h2]
    · have := hold q' h2
      rw [← hrow', h1] at this
      exact absurd this hnc.1
    · have := hold q h1
      rw [hrow', h2] at this
      exact absurd this hnc.1
    · exact hI.prow q h1 q' h2 hrow'
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact fun h => not_nc_of_star hI h hnc
    · exact hI.pnotstar q hq
  · intro y hy
    show y.1 ∈ insert p.1 s.rowCov ↔ y.2 ∉ s.colCov.erase z.2
    by_cases hy1 : y.1 = p.1
    · have hyz : y = z := by
        by_contra hne
        exact (hI.indep.1 y hy z hz hne).1 (hy1.trans hrow.symm)
      have hy2 : y.2 = z.2 := by rw [hyz]
      refine ⟨fun _ => ?_, fun _ => ?_⟩
      · rw [hy2]; exact Finset.notMem_erase _ _
      · exact Finset.mem_insert.mpr (Or.inl hy1)
    · have hyz : y ≠ z := fun h => hy1 (h ▸ hrow ▸ rfl)
      have hc2 : y.2 ≠ z.2 := (hI.indep.1 y hy z hz hyz).2
      simp [Finset.mem_insert, hy1, Finset.mem_erase, hc2]
      exact hI.once y hy
  · intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact ⟨z, hz, hrow⟩
    · exact hI.rowstar r hr
  · intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact ⟨p, Finset.mem_insert_self _ _, rfl⟩
    · obtain ⟨q, hq, h⟩ := hI.rowprime r hr
      exact ⟨q, Finset.mem_insert_of_mem hq, h⟩
  · intro c hc
    exact hI.colstar c (Finset.mem_of_mem_erase hc)
  · intro q hq
    show q.2 ∉ s.colCov.erase z.2
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact fun h => hnc.2 (Finset.mem_of_mem_erase h)
    · exact fun h => hI.pcol q hq (Finset.mem_of_mem_erase h)
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Or.inl (Finset.mem_insert_self _ _)
    · exact Or.inl (Finset.mem_insert_of_mem (hold q hq))
  · intro z0 hz0
    have h' : s.phase = Phase.step2 z0 := hz0
    rw [hphase] at h'
    exact absurd h' (by simp)
  · intro q hq w hw hwq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · have h1 : w.1 ∈ s.rowCov := (hI.once w hw).2 (hwq ▸ hnc.2)
      obtain ⟨q', hq', hq'1⟩ := hI.rowprime w.1 h1
      refine ⟨q', Finset.mem_insert_of_mem hq', hq'1, ?_⟩
      rw [hrk q' hq', hrkp]
      have := Finset.le_sup (f := rk) hq'
      omega
    · obtain ⟨q', hq', h1, h2⟩ := hI.order q hq w hw hwq
      refine ⟨q', Finset.mem_insert_of_mem hq', h1, ?_⟩
      rw [hrk q' hq', hrk q hq]; exact h2
  · intro h
    have h' : s.phase = Phase.step3 := h
    rw [hphase] at h'
    exact absurd h' (by simp)
  · intro _; exact hI.small (by rw [hphase]; simp)
  · intro h
    have h' : s.phase = Phase.done := h
    rw [hphase] at h'
    exact absurd h' (by simp)

theorem inv_to_step3 {n : ℕ} {s : State n} {rk : Fin n × Fin n → ℕ} (hI : Inv s rk)
    (hphase : s.phase = Phase.step1)
    (hnone : ∀ p : Fin n × Fin n, NonCovered s p → s.A p.1 p.2 ≠ 0) :
    Inv { s with phase := Phase.step3 } rk := by
  refine ⟨hI.nonneg, hI.indep, hI.pzero, hI.prow, hI.pnotstar, hI.once, hI.rowstar, hI.rowprime,
    hI.colstar, hI.pcol, ?_, ?_, hI.order, ?_, ?_, ?_⟩
  · intro q hq
    rcases hI.prowcov q hq with h | h
    · exact Or.inl h
    · rw [hphase] at h; exact absurd h (by simp)
  · intro z0 h; exact absurd h (by simp)
  · intro _ p hp; exact hnone p hp
  · intro _; exact hI.small (by rw [hphase]; simp)
  · intro h; exact absurd h (by simp)

theorem inv_reduce {n : ℕ} {s : State n} {rk : Fin n × Fin n → ℕ} (hI : Inv s rk)
    (h : ℝ) (hphase : s.phase = Phase.step3) (hmin : ∃ p, NonCovered s p ∧ s.A p.1 p.2 = h)
    (hle : ∀ q, NonCovered s q → h ≤ s.A q.1 q.2) :
    Inv { s with
        A := fun i j => s.A i j + (if i ∈ s.rowCov then h else 0) - (if j ∈ s.colCov then 0 else h)
        phase := Phase.step1 } rk := by
  have hh : 0 ≤ h := by
    obtain ⟨p, _, hp⟩ := hmin
    rw [← hp]; exact hI.nonneg _ _
  have hpr : ∀ q ∈ s.primed, q.1 ∈ s.rowCov := by
    intro q hq
    rcases hI.prowcov q hq with h | h
    · exact h
    · rw [hphase] at h; exact absurd h (by simp)
  refine ⟨?_, ⟨hI.indep.1, ?_⟩, ?_, hI.prow, hI.pnotstar, hI.once, hI.rowstar, hI.rowprime,
    hI.colstar, hI.pcol, ?_, ?_, hI.order, ?_, ?_, ?_⟩
  · intro i j
    show 0 ≤ s.A i j + (if i ∈ s.rowCov then h else 0) - (if j ∈ s.colCov then 0 else h)
    have h0 := hI.nonneg i j
    by_cases hi : i ∈ s.rowCov <;> by_cases hj : j ∈ s.colCov <;> simp [hi, hj] <;> try linarith
    exact hle (i, j) ⟨hi, hj⟩
  · intro z hz
    show s.A z.1 z.2 + (if z.1 ∈ s.rowCov then h else 0) - (if z.2 ∈ s.colCov then 0 else h) = 0
    have h0 := hI.indep.2 z hz
    have := hI.once z hz
    by_cases hi : z.1 ∈ s.rowCov
    · have hj : z.2 ∉ s.colCov := this.1 hi
      simp [hi, hj, h0]
    · have hj : z.2 ∈ s.colCov := by
        by_contra hj; exact hi (this.2 hj)
      simp [hi, hj, h0]
  · intro q hq
    show s.A q.1 q.2 + (if q.1 ∈ s.rowCov then h else 0) - (if q.2 ∈ s.colCov then 0 else h) = 0
    have h0 := hI.pzero q hq
    have hi := hpr q hq
    have hj := hI.pcol q hq
    simp [hi, hj, h0]
  · intro q hq
    exact Or.inl (hpr q hq)
  · intro z0 h'; exact absurd h' (by simp)
  · intro h'; exact absurd h' (by simp)
  · intro _; exact hI.small (by rw [hphase]; simp)
  · intro h; exact absurd h (by simp)


theorem seq_cons_rk {n : ℕ} {s : State n} {rk : Fin n × Fin n → ℕ} (hI : Inv s rk)
    {p w q : Fin n × Fin n} (hp : p ∈ s.primed) (hw : w ∈ s.starred) (hc : w.2 = p.2)
    (hq : q ∈ s.primed) (hr : q.1 = w.1) : rk q < rk p := by
  obtain ⟨q', hq', h1, h2⟩ := hI.order p hp w hw hc
  have : q = q' := hI.prow q hq q' hq' (hr.trans h1.symm)
  rw [this]; exact h2

theorem seq_exists {n : ℕ} {s : State n} {rk : Fin n × Fin n → ℕ} (hI : Inv s rk) :
    ∀ N : ℕ, ∀ p ∈ s.primed, rk p < N → ∃ l, Seq s (p :: l) := by
  intro N
  induction N with
  | zero => intro p _ h; omega
  | succ N ih =>
    intro p hp hlt
    by_cases hex : ∃ w ∈ s.starred, w.2 = p.2
    · obtain ⟨w, hw, hc⟩ := hex
      have h1 : w.1 ∈ s.rowCov := (hI.once w hw).2 (hc ▸ hI.pcol p hp)
      obtain ⟨q, hq, hq1⟩ := hI.rowprime w.1 h1
      have hlt' := seq_cons_rk hI hp hw hc hq hq1
      obtain ⟨l, hl⟩ := ih q hq (by omega)
      exact ⟨w :: q :: l, Seq.cons p w q l hw hc hq hq1 hl⟩
    · push_neg at hex
      exact ⟨[], Seq.last p (fun q hq => hex q hq)⟩

theorem seq_unique {n : ℕ} {s : State n} {rk : Fin n × Fin n → ℕ} (hI : Inv s rk)
    {zs : List (Fin n × Fin n)} (h : Seq s zs) :
    ∀ p l1 l2, zs = p :: l1 → Seq s (p :: l2) → l1 = l2 := by
  induction h with
  | last p0 h0 =>
    intro p l1 l2 heq h2
    simp at heq
    obtain ⟨rfl, rfl⟩ := heq
    cases h2 with
    | last => rfl
    | cons _ w q rest hw hc hq hr h' => exact absurd hc (h0 w hw)
  | cons p0 w q rest hw hc hq hr h ih =>
    intro p l1 l2 heq h2
    simp at heq
    obtain ⟨rfl, rfl⟩ := heq
    cases h2 with
    | last _ h0 => exact absurd hc (h0 w hw)
    | cons _ w' q' rest' hw' hc' hq' hr' h' =>
      have hww : w = w' := by
        by_contra hne
        exact (hI.indep.1 w hw w' hw' hne).2 (hc.trans hc'.symm)
      subst hww
      have hqq : q = q' := hI.prow q hq q' hq' (hr.trans hr'.symm)
      subst hqq
      have := ih q rest rest' rfl h'
      rw [this]

theorem seq_below {n : ℕ} {s : State n} {rk : Fin n × Fin n → ℕ} (hI : Inv s rk)
    {zs : List (Fin n × Fin n)} (h : Seq s zs) :
    ∀ p l, zs = p :: l → p ∈ s.primed → ∀ x ∈ l,
      (x ∈ s.primed ∧ rk x < rk p) ∨ (x ∈ s.starred ∧ ∃ q ∈ s.primed, q.1 = x.1 ∧ rk q < rk p) := by
  induction h with
  | last p0 h0 =>
    intro p l heq _ x hx
    simp at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp at hx
  | cons p0 w q rest hw hc hq hr h ih =>
    intro p l heq hp x hx
    simp at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hlt := seq_cons_rk hI hp hw hc hq hr
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact Or.inr ⟨hw, q, hq, hr, hlt⟩
    · exact Or.inl ⟨hq, hlt⟩
    · rcases ih q rest rfl hq x hx with ⟨h1, h2⟩ | ⟨h1, q', h2, h3, h4⟩
      · exact Or.inl ⟨h1, by omega⟩
      · exact Or.inr ⟨h1, q', h2, h3, by omega⟩

theorem seq_nodup {n : ℕ} {s : State n} {rk : Fin n × Fin n → ℕ} (hI : Inv s rk)
    {zs : List (Fin n × Fin n)} (h : Seq s zs) :
    ∀ p l, zs = p :: l → p ∈ s.primed → zs.Nodup := by
  induction h with
  | last p0 h0 => intro p l heq _; simp
  | cons p0 w q rest hw hc hq hr h ih =>
    intro p l heq hp
    simp at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hnd := ih q rest rfl hq
    have hbelow := seq_below hI (Seq.cons p0 w q rest hw hc hq hr h) p0 (w :: q :: rest) rfl hp
    have hbelow' := seq_below hI h q rest rfl hq
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, hnd⟩⟩
    · intro hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hI.pnotstar _ hp hw
      · rcases hbelow _ (List.mem_cons_of_mem _ hm) with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact lt_irrefl _ h2
        · exact hI.pnotstar _ hp h1
    · intro hm
      rcases List.mem_cons.mp hm with hm | hm
      · exact hI.pnotstar _ hq (hm ▸ hw)
      · rcases hbelow' _ hm with ⟨h1, _⟩ | ⟨h1, q', h2, h3, h4⟩
        · exact hI.pnotstar _ h1 hw
        · have hqq : q' = q := hI.prow q' h2 q hq (by rw [h3, hr])
          rw [hqq] at h4; exact lt_irrefl _ h4

def evs {α : Type*} : List α → List α
  | [] => []
  | [p] => [p]
  | p :: _ :: l => p :: evs l

def ods {α : Type*} : List α → List α
  | [] => []
  | [_] => []
  | _ :: w :: l => w :: ods l

theorem evs_cons2 {α : Type*} (p w : α) (l : List α) : evs (p :: w :: l) = p :: evs l := rfl
theorem ods_cons2 {α : Type*} (p w : α) (l : List α) : ods (p :: w :: l) = w :: ods l := rfl

theorem ods_starred {n : ℕ} {s : State n} {zs : List (Fin n × Fin n)} (h : Seq s zs) :
    ∀ x ∈ ods zs, x ∈ s.starred := by
  induction h with
  | last p h0 => intro x hx; simp [ods] at hx
  | cons p w q rest hw hc hq hr h ih =>
    intro x hx
    rw [ods_cons2] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hw
    · exact ih x hx

theorem evs_primed {n : ℕ} {s : State n} {zs : List (Fin n × Fin n)} (h : Seq s zs) :
    ∀ p l, zs = p :: l → p ∈ s.primed → ∀ x ∈ evs zs, x ∈ s.primed := by
  induction h with
  | last p0 h0 =>
    intro p l heq hp x hx
    simp at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp [evs] at hx; rw [hx]; exact hp
  | cons p0 w q rest hw hc hq hr h ih =>
    intro p l heq hp x hx
    simp at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [evs_cons2] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hp
    · exact ih q rest rfl hq x hx

theorem evs_length {n : ℕ} {s : State n} {zs : List (Fin n × Fin n)} (h : Seq s zs) :
    (evs zs).length = (ods zs).length + 1 := by
  induction h with
  | last p h0 => simp [evs, ods]
  | cons p w q rest hw hc hq hr h ih =>
    rw [evs_cons2, ods_cons2]; simp only [List.length_cons]; omega

theorem mem_evs_ods {n : ℕ} {s : State n} {zs : List (Fin n × Fin n)} (h : Seq s zs) :
    ∀ x, x ∈ zs ↔ x ∈ evs zs ∨ x ∈ ods zs := by
  induction h with
  | last p h0 => intro x; simp [evs, ods]
  | cons p w q rest hw hc hq hr h ih =>
    intro x
    rw [evs_cons2, ods_cons2]
    have := ih x
    simp only [List.mem_cons] at this ⊢
    tauto

theorem evs_ods_sublist {n : ℕ} {s : State n} {zs : List (Fin n × Fin n)} (h : Seq s zs) :
    (evs zs).Sublist zs ∧ (ods zs).Sublist zs := by
  induction h with
  | last p h0 => simp [evs, ods]
  | cons p w q rest hw hc hq hr h ih =>
    rw [evs_cons2, ods_cons2]
    exact ⟨List.Sublist.cons₂ p (ih.1.cons w), (List.Sublist.cons₂ w ih.2).cons p⟩


theorem evs_col {n : ℕ} {s : State n} {rk : Fin n × Fin n → ℕ} (hI : Inv s rk)
    {zs : List (Fin n × Fin n)} (h : Seq s zs) :
    ∀ e ∈ evs zs, ∀ w ∈ s.starred, w ∉ ods zs → w.2 ≠ e.2 := by
  induction h with
  | last p h0 =>
    intro e he w hw _
    simp [evs] at he; subst he
    exact h0 w hw
  | cons p w0 q rest hw0 hc hq hr h ih =>
    intro e he w hw hnot
    rw [evs_cons2] at he
    rw [ods_cons2] at hnot
    rcases List.mem_cons.mp he with rfl | he
    · intro hwe
      apply hnot
      have : w = w0 := by
        by_contra hne
        exact (hI.indep.1 w hw w0 hw0 hne).2 (hwe.trans hc.symm)
      rw [this]; exact List.mem_cons_self
    · exact ih e he w hw (fun hm => hnot (List.mem_cons_of_mem _ hm))

theorem evs_row {n : ℕ} {s : State n} {zs : List (Fin n × Fin n)} (h : Seq s zs) :
    ∀ p l, zs = p :: l → ∀ e ∈ evs zs, e = p ∨ ∃ b ∈ ods zs, b.1 = e.1 := by
  induction h with
  | last p0 h0 =>
    intro p l heq e he
    simp at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp [evs] at he; exact Or.inl he
  | cons p0 w q rest hw hc hq hr h ih =>
    intro p l heq e he
    simp at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [evs_cons2] at he
    rcases List.mem_cons.mp he with rfl | he
    · exact Or.inl rfl
    · right
      rcases ih q rest rfl e he with rfl | ⟨b, hb, hb1⟩
      · exact ⟨w, by rw [ods_cons2]; exact List.mem_cons_self, hr.symm⟩
      · exact ⟨b, by rw [ods_cons2]; exact List.mem_cons_of_mem _ hb, hb1⟩

theorem evs_col_inj {n : ℕ} {s : State n} {rk : Fin n × Fin n → ℕ} (hI : Inv s rk)
    {zs : List (Fin n × Fin n)} (h : Seq s zs) :
    zs.Nodup → ∀ e ∈ evs zs, ∀ e' ∈ evs zs, e.2 = e'.2 → e = e' := by
  induction h with
  | last p h0 =>
    intro _ e he e' he' _
    simp [evs] at he he'; rw [he, he']
  | cons p w q rest hw hc hq hr h ih =>
    intro hnd e he e' he' hee
    rw [evs_cons2] at he he'
    have hnd' := List.nodup_cons.mp hnd
    have hnd2 := List.nodup_cons.mp hnd'.2
    have hwo : w ∉ ods (q :: rest) := fun hm =>
      hnd2.1 ((evs_ods_sublist h).2.subset hm)
    rcases List.mem_cons.mp he with h1 | h1 <;> rcases List.mem_cons.mp he' with h2 | h2
    · rw [h1, h2]
    · exact absurd (hc.trans ((congrArg Prod.snd h1).symm.trans hee)) (evs_col hI h e' h2 w hw hwo)
    · exact absurd (hc.trans ((congrArg Prod.snd h2).symm.trans hee.symm)) (evs_col hI h e h1 w hw hwo)
    · exact ih hnd2.2 e h1 e' h2 hee

theorem aug_eq {n : ℕ} {s : State n} {rk : Fin n × Fin n → ℕ} (hI : Inv s rk)
    {zs : List (Fin n × Fin n)} (h : Seq s zs) (p : Fin n × Fin n) (l : List (Fin n × Fin n))
    (hzs : zs = p :: l) (hp : p ∈ s.primed) :
    (s.starred \ zs.toFinset) ∪ (s.primed ∩ zs.toFinset) =
      (s.starred \ (ods zs).toFinset) ∪ (evs zs).toFinset := by
  ext x
  have a1 : x ∈ evs zs → x ∈ s.primed := evs_primed h p l hzs hp x
  have a2 : x ∈ ods zs → x ∈ s.starred := ods_starred h x
  have a3 : x ∈ s.primed → x ∉ s.starred := hI.pnotstar x
  have a4 := mem_evs_ods h x
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, List.mem_toFinset]
  tauto

theorem aug_props {n : ℕ} {s : State n} {rk : Fin n × Fin n → ℕ} (hI : Inv s rk)
    (z₀ : Fin n × Fin n) (hph : s.phase = Phase.step2 z₀) (zs : List (Fin n × Fin n))
    (hseq : IsStep2Seq s z₀ zs) :
    Independent ((s.starred \ zs.toFinset) ∪ (s.primed ∩ zs.toFinset)) ∧
    (∀ x ∈ (s.starred \ zs.toFinset) ∪ (s.primed ∩ zs.toFinset), s.A x.1 x.2 = 0) ∧
    ((s.starred \ zs.toFinset) ∪ (s.primed ∩ zs.toFinset)).card = s.starred.card + 1 := by
  obtain ⟨hhead, hS⟩ := (isStep2Seq_iff s z₀ zs).mp hseq
  obtain ⟨hz0p, hz0nc, hz0row, -⟩ := hI.s2 z₀ hph
  have hzs : zs = z₀ :: zs.tail := by
    rcases zs with _ | ⟨a, l⟩
    · simp at hhead
    · simp at hhead; simp [hhead]
  rw [aug_eq hI hS z₀ zs.tail hzs hz0p]
  have hnd := seq_nodup hI hS z₀ zs.tail hzs hz0p
  have hev : ∀ x ∈ evs zs, x ∈ s.primed := evs_primed hS z₀ zs.tail hzs hz0p
  have hod : ∀ x ∈ ods zs, x ∈ s.starred := ods_starred hS
  have hrow := evs_row hS z₀ zs.tail hzs
  -- independence between an old star and a new star
  have cross : ∀ x ∈ s.starred, x ∉ ods zs → ∀ y ∈ evs zs, x.1 ≠ y.1 ∧ x.2 ≠ y.2 := by
    intro x hx hxo y hy
    refine ⟨?_, evs_col hI hS y hy x hx hxo⟩
    rcases hrow y hy with rfl | ⟨b, hb, hb1⟩
    · exact fun h => hz0row x hx h
    · intro h
      have : x = b := by
        by_contra hne
        exact (hI.indep.1 x hx b (hod b hb) hne).1 (h.trans hb1.symm)
      exact hxo (this ▸ hb)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset] at hx hy
    rcases hx with ⟨hx1, hx2⟩ | hx <;> rcases hy with ⟨hy1, hy2⟩ | hy
    · exact hI.indep.1 x hx1 y hy1 hxy
    · exact cross x hx1 hx2 y hy
    · have := cross y hy1 hy2 x hx
      exact ⟨fun h => this.1 h.symm, fun h => this.2 h.symm⟩
    · refine ⟨fun h => hxy (hI.prow x (hev x hx) y (hev y hy) h), fun h => hxy ?_⟩
      exact evs_col_inj hI hS hnd x hx y hy h
  · intro x hx
    simp only [Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset] at hx
    rcases hx with ⟨hx1, _⟩ | hx
    · exact hI.indep.2 x hx1
    · exact hI.pzero x (hev x hx)
  · have hnd1 := (evs_ods_sublist hS).1.nodup hnd
    have hnd2 := (evs_ods_sublist hS).2.nodup hnd
    have hlen := evs_length hS
    have hsub : (ods zs).toFinset ⊆ s.starred := by
      intro x hx; exact hod x (List.mem_toFinset.mp hx)
    have hdisj : Disjoint (s.starred \ (ods zs).toFinset) (evs zs).toFinset := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      exact hI.pnotstar x (hev x (List.mem_toFinset.mp hx')) (Finset.mem_sdiff.mp hx).1
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_sdiff_of_subset hsub,
      List.toFinset_card_of_nodup hnd1, List.toFinset_card_of_nodup hnd2]
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd2] at this
    omega

theorem inv_augment {n : ℕ} {s : State n} {rk : Fin n × Fin n → ℕ} (hI : Inv s rk)
    (z₀ : Fin n × Fin n) (hph : s.phase = Phase.step2 z₀) (zs : List (Fin n × Fin n))
    (hseq : IsStep2Seq s z₀ zs) :
    Inv (enterStep1 (augmentState s zs)) (fun _ => 0) := by
  obtain ⟨h1, h2, h3⟩ := aug_props hI z₀ hph zs hseq
  apply inv_reset
  · exact hI.nonneg
  · exact ⟨h1, h2⟩
  · rfl
  · rfl
  · rfl

theorem inv_step {n : ℕ} {s t : State n} {rk : Fin n × Fin n → ℕ} (hI : Inv s rk)
    (hst : Step s t) : ∃ rk', Inv t rk' := by
  cases hst with
  | prime_go2 p hphase hzero hnc hnostar => exact ⟨_, inv_prime_go2 hI p hphase hzero hnc hnostar⟩
  | prime_cover p z hphase hzero hnc hz hrow => exact ⟨_, inv_prime_cover hI p z hphase hzero hnc hz hrow⟩
  | to_step3 hphase hnone => exact ⟨_, inv_to_step3 hI hphase hnone⟩
  | augment z₀ zs hphase hseq => exact ⟨_, inv_augment hI z₀ hphase zs hseq⟩
  | reduce h hphase hmin hle => exact ⟨_, inv_reduce hI h hphase hmin hle⟩

theorem reachable_inv {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {s : State n}
    (hs : Reachable A s) : ∃ rk, Inv s rk := by
  obtain ⟨s₀, h0, hr⟩ := hs
  induction hr with
  | refl => exact ⟨_, inv_start A s₀ h0⟩
  | tail _ hst ih =>
    obtain ⟨rk, hI⟩ := ih
    exact inv_step hI hst

theorem lg_core {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (R C : Finset (Fin n))
    (hcov : CoversZeros B R C) :
    maxIndepZeros B ≤ R.card + C.card := by
  unfold maxIndepZeros
  apply Finset.sup_le
  intro S hS
  rw [Finset.mem_filter] at hS
  obtain ⟨hI, hz⟩ := hS.2
  have h1 : (S.filter (fun p => p.1 ∈ R)).card ≤ R.card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp
      exact hp.2
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
      by_contra hne
      exact (hI p hp.1 q hq.1 hne).1 hpq
  have h2 : (S.filter (fun p => ¬ p.1 ∈ R)).card ≤ C.card := by
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp
      rcases hcov p.1 p.2 (hz p hp.1) with h | h
      · exact absurd h hp.2
      · exact h
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
      by_contra hne
      exact (hI p hp.1 q hq.1 hne).2 hpq
  have := Finset.card_filter_add_card_filter_not (s := S) (fun p => p.1 ∈ R)
  omega


theorem seq_split {n : ℕ} {zs : List (Fin n × Fin n)} {z₀ : Fin n × Fin n}
    (h : zs.head? = some z₀) : zs = z₀ :: zs.tail := by
  rcases zs with _ | ⟨a, l⟩
  · simp at h
  · simp at h; simp [h]

theorem step2_core {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n)
    (z₀ : Fin n × Fin n) (hs : Reachable A s) (hph : s.phase = Phase.step2 z₀) :
    (∃ zs, IsStep2Seq s z₀ zs) ∧
    (∀ zs zs', IsStep2Seq s z₀ zs → IsStep2Seq s z₀ zs' → zs = zs') ∧
    (∀ zs, IsStep2Seq s z₀ zs → zs.Nodup) ∧
    (z₀ ∈ s.primed ∧ NonCovered s z₀ ∧ ∀ p ∈ s.primed, NonCovered s p → p = z₀) := by
  obtain ⟨rk, hI⟩ := reachable_inv hs
  obtain ⟨hz0p, hz0nc, _, hoth⟩ := hI.s2 z₀ hph
  refine ⟨?_, ?_, ?_, hz0p, hz0nc, ?_⟩
  · obtain ⟨l, hl⟩ := seq_exists hI (rk z₀ + 1) z₀ hz0p (Nat.lt_succ_self _)
    exact ⟨z₀ :: l, (isStep2Seq_iff s z₀ _).mpr ⟨rfl, hl⟩⟩
  · intro zs zs' h1 h2
    obtain ⟨e1, q1⟩ := (isStep2Seq_iff s z₀ zs).mp h1
    obtain ⟨e2, q2⟩ := (isStep2Seq_iff s z₀ zs').mp h2
    have s1 := seq_split e1
    have s2 := seq_split e2
    rw [s1] at q1
    rw [s2] at q2
    rw [s1, s2, seq_unique hI q1 z₀ zs.tail zs'.tail rfl q2]
  · intro zs h1
    obtain ⟨e1, q1⟩ := (isStep2Seq_iff s z₀ zs).mp h1
    exact seq_nodup hI q1 z₀ zs.tail (seq_split e1) hz0p
  · intro p hp hnc
    by_contra hne
    exact hnc.1 (hoth p hp hne)

theorem enterStep1_starred {n : ℕ} (u : State n) : (enterStep1 u).starred = u.starred := by
  unfold enterStep1; split_ifs <;> rfl

theorem enterStep1_A {n : ℕ} (u : State n) : (enterStep1 u).A = u.A := by
  unfold enterStep1; split_ifs <;> rfl

theorem step2_count_core {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s t : State n)
    (z₀ : Fin n × Fin n) (hs : Reachable A s) (hph : s.phase = Phase.step2 z₀)
    (hst : Step s t) :
    IsIndepZeros t.A t.starred ∧ t.starred.card = s.starred.card + 1 := by
  obtain ⟨rk, hI⟩ := reachable_inv hs
  cases hst with
  | prime_go2 p hphase => exact absurd (hph.symm.trans hphase) (by simp)
  | prime_cover p z hphase => exact absurd (hph.symm.trans hphase) (by simp)
  | to_step3 hphase => exact absurd (hph.symm.trans hphase) (by simp)
  | reduce h hphase => exact absurd (hph.symm.trans hphase) (by simp)
  | augment z₁ zs hphase hseq =>
    obtain ⟨h1, h2, h3⟩ := aug_props hI z₁ hphase zs hseq
    rw [enterStep1_starred, enterStep1_A]
    exact ⟨⟨h1, h2⟩, h3⟩

theorem cover_card_le {n : ℕ} {s : State n} {rk : Fin n × Fin n → ℕ} (hI : Inv s rk) :
    s.rowCov.card + s.colCov.card ≤ s.starred.card := by
  have h1 : s.rowCov.card ≤ (s.starred.filter (fun z => z.1 ∈ s.rowCov)).card := by
    calc s.rowCov.card ≤ ((s.starred.filter (fun z => z.1 ∈ s.rowCov)).image Prod.fst).card := by
          apply Finset.card_le_card
          intro r hr
          obtain ⟨z, hz, hz1⟩ := hI.rowstar r hr
          exact Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hz, hz1 ▸ hr⟩, hz1⟩
      _ ≤ _ := Finset.card_image_le
  have h2 : s.colCov.card ≤ (s.starred.filter (fun z => z.2 ∈ s.colCov)).card := by
    calc s.colCov.card ≤ ((s.starred.filter (fun z => z.2 ∈ s.colCov)).image Prod.snd).card := by
          apply Finset.card_le_card
          intro r hr
          obtain ⟨z, hz, hz1⟩ := hI.colstar r hr
          exact Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hz, hz1 ▸ hr⟩, hz1⟩
      _ ≤ _ := Finset.card_image_le
  have hd : Disjoint (s.starred.filter (fun z => z.1 ∈ s.rowCov))
      (s.starred.filter (fun z => z.2 ∈ s.colCov)) := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    obtain ⟨hzs, hr⟩ := Finset.mem_filter.mp hz1
    obtain ⟨_, hc⟩ := Finset.mem_filter.mp hz2
    exact (hI.once z hzs).1 hr hc
  have h3 := Finset.card_union_of_disjoint hd
  have h4 : (s.starred.filter (fun z => z.1 ∈ s.rowCov) ∪
      s.starred.filter (fun z => z.2 ∈ s.colCov)).card ≤ s.starred.card :=
    Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  omega

theorem step3_core {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n)
    (hs : Reachable A s) (hph : s.phase = Phase.step3) :
    ∃ h : ℝ, 0 < h ∧ (∃ p, NonCovered s p ∧ s.A p.1 p.2 = h) ∧
      (∀ q, NonCovered s q → h ≤ s.A q.1 q.2) ∧
      (∀ p ∈ s.starred ∪ s.primed,
        (p.1 ∈ s.rowCov ∧ p.2 ∉ s.colCov) ∨ (p.1 ∉ s.rowCov ∧ p.2 ∈ s.colCov)) ∧
      ∀ t, Step s t →
        (∀ i j, i ∉ s.rowCov → j ∉ s.colCov → t.A i j = s.A i j - h) ∧
        (∀ i j, i ∈ s.rowCov → j ∈ s.colCov → t.A i j = s.A i j + h) ∧
        (∀ i j, (i ∈ s.rowCov ∧ j ∉ s.colCov) ∨ (i ∉ s.rowCov ∧ j ∈ s.colCov) →
          t.A i j = s.A i j) ∧
        (∀ p ∈ s.starred ∪ s.primed, t.A p.1 p.2 = 0) ∧
        maxIndepZeros s.A ≤ maxIndepZeros t.A := by
  obtain ⟨rk, hI⟩ := reachable_inv hs
  have hsmall := hI.small (by rw [hph]; simp)
  have hcnt := cover_card_le hI
  have hRn : s.rowCov.card < n := by omega
  have hCn : s.colCov.card < n := by omega
  have hi : ∃ i : Fin n, i ∉ s.rowCov := by
    by_contra hc; push_neg at hc
    have : s.rowCov = Finset.univ := Finset.eq_univ_iff_forall.mpr hc
    rw [this] at hRn; simp at hRn
  have hj : ∃ j : Fin n, j ∉ s.colCov := by
    by_contra hc; push_neg at hc
    have : s.colCov = Finset.univ := Finset.eq_univ_iff_forall.mpr hc
    rw [this] at hCn; simp at hCn
  obtain ⟨i0, hi0⟩ := hi
  obtain ⟨j0, hj0⟩ := hj
  have hne : (Finset.univ.filter (fun p : Fin n × Fin n => NonCovered s p)).Nonempty :=
    ⟨(i0, j0), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi0, hj0⟩⟩
  obtain ⟨p0, hp0, hmin⟩ := Finset.exists_min_image _ (fun p : Fin n × Fin n => s.A p.1 p.2) hne
  have hp0nc : NonCovered s p0 := (Finset.mem_filter.mp hp0).2
  have hle : ∀ q, NonCovered s q → s.A p0.1 p0.2 ≤ s.A q.1 q.2 := fun q hq =>
    hmin q (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩)
  have hpos : 0 < s.A p0.1 p0.2 :=
    lt_of_le_of_ne (hI.nonneg _ _) (fun h => hI.s3 hph p0 hp0nc h.symm)
  have hprim : ∀ q ∈ s.primed, q.1 ∈ s.rowCov := by
    intro q hq
    rcases hI.prowcov q hq with h | h
    · exact h
    · rw [hph] at h; exact absurd h (by simp)
  have honce : ∀ p ∈ s.starred ∪ s.primed,
      (p.1 ∈ s.rowCov ∧ p.2 ∉ s.colCov) ∨ (p.1 ∉ s.rowCov ∧ p.2 ∈ s.colCov) := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · by_cases h : p.1 ∈ s.rowCov
      · exact Or.inl ⟨h, (hI.once p hp).1 h⟩
      · refine Or.inr ⟨h, ?_⟩
        by_contra hc; exact h ((hI.once p hp).2 hc)
    · exact Or.inl ⟨hprim p hp, hI.pcol p hp⟩
  refine ⟨s.A p0.1 p0.2, hpos, ⟨p0, hp0nc, rfl⟩, hle, honce, ?_⟩
  intro t hst
  cases hst with
  | prime_go2 p hphase => exact absurd (hph.symm.trans hphase) (by simp)
  | prime_cover p z hphase => exact absurd (hph.symm.trans hphase) (by simp)
  | to_step3 hphase => exact absurd (hph.symm.trans hphase) (by simp)
  | augment z₀ zs hphase => exact absurd (hph.symm.trans hphase) (by simp)
  | reduce h' hphase hmin' hle' =>
    obtain ⟨p', hp'nc, hp'eq⟩ := hmin'
    have hh : h' = s.A p0.1 p0.2 := by
      have h1 := hle' p0 hp0nc
      have h2 := hle p' hp'nc
      linarith
    rw [← hh]
    have hz : ∀ p ∈ s.starred ∪ s.primed,
        s.A p.1 p.2 + (if p.1 ∈ s.rowCov then h' else 0) - (if p.2 ∈ s.colCov then 0 else h') = 0 := by
      intro p hp
      have h0 : s.A p.1 p.2 = 0 := by
        rcases Finset.mem_union.mp hp with hp | hp
        · exact hI.indep.2 p hp
        · exact hI.pzero p hp
      rcases honce p hp with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · simp [ha, hb, h0]
      · simp [ha, hb, h0]
    refine ⟨?_, ?_, ?_, hz, ?_⟩
    · intro i j hi hj; show s.A i j + (if i ∈ s.rowCov then h' else 0) - (if j ∈ s.colCov then 0 else h') = s.A i j - h'
      simp [hi, hj]
    · intro i j hi hj; show s.A i j + (if i ∈ s.rowCov then h' else 0) - (if j ∈ s.colCov then 0 else h') = s.A i j + h'
      simp [hi, hj]
    · intro i j hij; show s.A i j + (if i ∈ s.rowCov then h' else 0) - (if j ∈ s.colCov then 0 else h') = s.A i j
      rcases hij with ⟨hi, hj⟩ | ⟨hi, hj⟩ <;> simp [hi, hj]
    · have hcover : CoversZeros s.A s.rowCov s.colCov := by
        intro i j hij
        by_contra hc
        push_neg at hc
        exact hI.s3 hph (i, j) ⟨hc.1, hc.2⟩ hij
      calc maxIndepZeros s.A ≤ s.rowCov.card + s.colCov.card := lg_core s.A _ _ hcover
        _ ≤ s.starred.card := hcnt
        _ ≤ _ := by
          unfold maxIndepZeros
          apply Finset.le_sup (f := Finset.card)
          exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
            ⟨hI.indep.1, fun z hz' => hz z (Finset.mem_union_left _ hz')⟩⟩

theorem r2_core {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) :
    HeldWolfeCrowder.Assignment.IsOptimalAssignment A σ ↔
      HeldWolfeCrowder.Assignment.IsOptimalAssignment (fun i j => A i j - u i - v j) σ := by
  have key : ∀ τ : Equiv.Perm (Fin n),
      HeldWolfeCrowder.Assignment.assignCost (fun i j => A i j - u i - v j) τ =
      HeldWolfeCrowder.Assignment.assignCost A τ - ∑ i, u i - ∑ j, v j := by
    intro τ
    unfold HeldWolfeCrowder.Assignment.assignCost
    simp only [Finset.sum_sub_distrib]
    have : ∑ r, u (τ r) = ∑ i, u i := Equiv.sum_comp τ u
    rw [this]
  unfold HeldWolfeCrowder.Assignment.IsOptimalAssignment
  constructor
  · intro h τ
    rw [key, key]
    have := h τ
    linarith
  · intro h τ
    have := h τ
    rw [key, key] at this
    linarith


theorem indep_card_le {n : ℕ} {S : Finset (Fin n × Fin n)} (h : Independent S) : S.card ≤ n := by
  rw [← card_colsOf h]
  have := Finset.card_le_univ (colsOf S)
  simpa using this

theorem maxIndep_le_n {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : maxIndepZeros B ≤ n := by
  unfold maxIndepZeros
  apply Finset.sup_le
  intro S hS
  exact indep_card_le (Finset.mem_filter.mp hS).2.1

def Form {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n) : Prop :=
  ∃ u v : Fin n → ℝ, ∀ i j, s.A i j = A i j - u i - v j

theorem form_start {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n) (hs : IsStart A s) :
    Form A s := by
  obtain ⟨L, -, -, rfl⟩ := hs
  rw [Form]
  refine ⟨fun i => if h : (Finset.univ : Finset (Fin n)).Nonempty then Finset.univ.inf' h (A i) else 0,
    fun j => if h : (Finset.univ : Finset (Fin n)).Nonempty then
      Finset.univ.inf' h (fun i' => rowReduce A i' j) else 0, ?_⟩
  intro i j
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨j, Finset.mem_univ j⟩
  rw [enterStep1_A]
  show colReduce (rowReduce A) i j = _
  simp only [colReduce, rowReduce, dif_pos hne]

theorem form_step {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {s t : State n} (hf : Form A s)
    (hst : Step s t) : Form A t := by
  obtain ⟨u, v, hf⟩ := hf
  cases hst with
  | prime_go2 p hphase => exact ⟨u, v, hf⟩
  | prime_cover p z hphase => exact ⟨u, v, hf⟩
  | to_step3 hphase => exact ⟨u, v, hf⟩
  | augment z₀ zs hphase => exact ⟨u, v, fun i j => by rw [enterStep1_A]; exact hf i j⟩
  | reduce h hphase hmin hle =>
    refine ⟨fun i => u i - (if i ∈ s.rowCov then h else 0),
      fun j => v j + (if j ∈ s.colCov then 0 else h), ?_⟩
    intro i j
    show s.A i j + (if i ∈ s.rowCov then h else 0) - (if j ∈ s.colCov then 0 else h) = _
    rw [hf i j]; ring

theorem reachable_form {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {s : State n}
    (hs : Reachable A s) : Form A s := by
  obtain ⟨s₀, h0, hr⟩ := hs
  induction hr with
  | refl => exact form_start A s₀ h0
  | tail _ hst ih => exact form_step ih hst

theorem exists_step {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n) (hs : Reachable A s)
    (hne : s.phase ≠ Phase.done) : ∃ t, Step s t := by
  cases hph : s.phase with
  | step1 =>
    by_cases hex : ∃ p : Fin n × Fin n, NonCovered s p ∧ s.A p.1 p.2 = 0
    · obtain ⟨p, hnc, hz⟩ := hex
      by_cases hst : ∃ z ∈ s.starred, z.1 = p.1
      · obtain ⟨z, hz', hrow⟩ := hst
        exact ⟨_, Step.prime_cover s p z hph hz hnc hz' hrow⟩
      · push_neg at hst
        exact ⟨_, Step.prime_go2 s p hph hz hnc hst⟩
    · exact ⟨_, Step.to_step3 s hph (fun p hp hz => hex ⟨p, hp, hz⟩)⟩
  | step2 z₀ =>
    obtain ⟨⟨zs, hzs⟩, _⟩ := step2_core A s z₀ hs hph
    exact ⟨_, Step.augment s z₀ zs hph hzs⟩
  | step3 =>
    obtain ⟨h, _, ⟨p, hp, hpe⟩, hle, _⟩ := step3_core A s hs hph
    exact ⟨_, Step.reduce s h hph ⟨p, hp, hpe⟩ hle⟩
  | done => exact absurd hph hne

noncomputable def rankOf {n : ℕ} (s : State n) : ℕ :=
  match s.phase with
  | Phase.step1 => if ∃ p, NonCovered s p ∧ s.A p.1 p.2 = 0 then 1 else 3
  | Phase.step2 _ => 0
  | Phase.step3 => 2
  | Phase.done => 0

theorem rank_step2 {n : ℕ} {t : State n} {z : Fin n × Fin n} (h : t.phase = Phase.step2 z) :
    rankOf t = 0 := by simp [rankOf, h]
theorem rank_step3 {n : ℕ} {t : State n} (h : t.phase = Phase.step3) : rankOf t = 2 := by
  simp [rankOf, h]
theorem rank_step1_nc {n : ℕ} {t : State n} (h : t.phase = Phase.step1)
    (hex : ∃ p, NonCovered t p ∧ t.A p.1 p.2 = 0) : rankOf t = 1 := by
  simp [rankOf, h, hex]
theorem rank_step1_no {n : ℕ} {t : State n} (h : t.phase = Phase.step1)
    (hex : ¬ ∃ p, NonCovered t p ∧ t.A p.1 p.2 = 0) : rankOf t = 3 := by
  simp only [rankOf, h]; rw [if_neg hex]
theorem rank_le {n : ℕ} (t : State n) : rankOf t ≤ 3 := by
  unfold rankOf
  split <;> (try split) <;> omega

noncomputable def mu {n : ℕ} (s : State n) : ℕ × ℕ × ℕ :=
  (n - maxIndepZeros s.A, n - s.starred.card, 3 * (n - s.rowCov.card) + rankOf s)

def RR : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))

theorem lex3 {a b c a' b' c' : ℕ}
    (h : a < a' ∨ (a = a' ∧ (b < b' ∨ (b = b' ∧ c < c')))) : RR (a, b, c) (a', b', c') := by
  rcases h with h | ⟨rfl, h | ⟨rfl, h⟩⟩
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ (Prod.Lex.left _ _ h)
  · exact Prod.Lex.right _ (Prod.Lex.right _ h)

theorem step_mu_lt {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {s t : State n} (hs : Reachable A s)
    (hst : Step s t) : RR (mu t) (mu s) := by
  obtain ⟨rk, hI⟩ := reachable_inv hs
  unfold mu
  cases hst with
  | prime_go2 p hphase hzero hnc hnostar =>
    apply lex3
    right; refine ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩
    have h1 : rankOf ({ s with primed := insert p s.primed, phase := Phase.step2 p } : State n) = 0 :=
      rank_step2 rfl
    have h2 : rankOf s = 1 := rank_step1_nc hphase ⟨p, hnc, hzero⟩
    show 3 * (n - s.rowCov.card) + rankOf ({ s with primed := insert p s.primed, phase := Phase.step2 p } : State n) < _
    omega
  | prime_cover p z hphase hzero hnc hz hrow =>
    apply lex3
    right; refine ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩
    have h2 : rankOf s = 1 := rank_step1_nc hphase ⟨p, hnc, hzero⟩
    have h3 := rank_le ({ s with primed := insert p s.primed, rowCov := insert p.1 s.rowCov, colCov := s.colCov.erase z.2 } : State n)
    have h4 : (insert p.1 s.rowCov).card = s.rowCov.card + 1 := Finset.card_insert_of_notMem hnc.1
    have h5 : (insert p.1 s.rowCov).card ≤ n := by
      have := Finset.card_le_univ (insert p.1 s.rowCov); simpa using this
    show 3 * (n - (insert p.1 s.rowCov).card) + rankOf ({ s with primed := insert p s.primed, rowCov := insert p.1 s.rowCov, colCov := s.colCov.erase z.2 } : State n) < _
    omega
  | to_step3 hphase hnone =>
    apply lex3
    right; refine ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩
    have h2 : rankOf s = 3 := rank_step1_no hphase (fun ⟨p, hp, hz⟩ => hnone p hp hz)
    have h1 : rankOf ({ s with phase := Phase.step3 } : State n) = 2 := rank_step3 rfl
    show 3 * (n - s.rowCov.card) + rankOf ({ s with phase := Phase.step3 } : State n) < _
    omega
  | augment z₀ zs hphase hseq =>
    obtain ⟨h1, h2, h3⟩ := aug_props hI z₀ hphase zs hseq
    apply lex3
    right
    have hc : (enterStep1 (augmentState s zs)).starred.card = s.starred.card + 1 := by
      rw [enterStep1_starred]; exact h3
    have hle : s.starred.card + 1 ≤ n := by
      rw [← h3]; exact indep_card_le h1
    refine ⟨by rw [enterStep1_A]; rfl, Or.inl ?_⟩
    show n - (enterStep1 (augmentState s zs)).starred.card < n - s.starred.card
    omega
  | reduce h hphase hmin hle =>
    obtain ⟨h0, _, _, _, _, hall⟩ := step3_core A s hs hphase
    have hmono := (hall _ (Step.reduce s h hphase hmin hle)).2.2.2.2
    have hmax := maxIndep_le_n
      ({ s with A := fun i j => s.A i j + (if i ∈ s.rowCov then h else 0) - (if j ∈ s.colCov then 0 else h), phase := Phase.step1 } : State n).A
    apply lex3
    by_cases hlt : maxIndepZeros s.A < maxIndepZeros
      ({ s with A := fun i j => s.A i j + (if i ∈ s.rowCov then h else 0) - (if j ∈ s.colCov then 0 else h), phase := Phase.step1 } : State n).A
    · left; omega
    · right
      refine ⟨by omega, Or.inr ⟨rfl, ?_⟩⟩
      obtain ⟨p, hp, hpe⟩ := hmin
      have h1 : rankOf ({ s with A := fun i j => s.A i j + (if i ∈ s.rowCov then h else 0) - (if j ∈ s.colCov then 0 else h), phase := Phase.step1 } : State n) = 1 := by
        apply rank_step1_nc rfl
        refine ⟨p, hp, ?_⟩
        show s.A p.1 p.2 + (if p.1 ∈ s.rowCov then h else 0) - (if p.2 ∈ s.colCov then 0 else h) = 0
        simp [hp.1, hp.2, hpe]
      have h2 : rankOf s = 2 := rank_step3 hphase
      show 3 * (n - s.rowCov.card) + rankOf ({ s with A := fun i j => s.A i j + (if i ∈ s.rowCov then h else 0) - (if j ∈ s.colCov then 0 else h), phase := Phase.step1 } : State n) < _
      omega

theorem acc_core {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ s : State n, Reachable A s → Acc (fun t s => Step s t) s := by
  have wfRR : WellFounded RR :=
    WellFounded.prod_lex wellFounded_lt (WellFounded.prod_lex wellFounded_lt wellFounded_lt)
  have wf : WellFounded (fun a b : State n => RR (mu a) (mu b)) := InvImage.wf mu wfRR
  intro s
  induction s using wf.induction with
  | _ s ih =>
    intro hs
    constructor
    intro t hst
    obtain ⟨s0, h0, hr⟩ := hs
    exact ih t (step_mu_lt ⟨s0, h0, hr⟩ hst) ⟨s0, h0, hr.tail hst⟩

theorem done_core {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n) (hs : Reachable A s)
    (hdone : s.phase = Phase.done) :
    ∃ σ : Equiv.Perm (Fin n), s.starred = Finset.univ.image (fun r => (σ r, r)) ∧
      HeldWolfeCrowder.Assignment.IsOptimalAssignment A σ := by
  obtain ⟨rk, hI⟩ := reachable_inv hs
  have hcol := hI.donecol hdone
  have hcolex : ∀ r : Fin n, ∃ z ∈ s.starred, z.2 = r := by
    intro r
    have : r ∈ colsOf s.starred := by rw [hcol]; exact Finset.mem_univ r
    unfold colsOf at this
    obtain ⟨z, hz, e⟩ := Finset.mem_image.mp this
    exact ⟨z, hz, e⟩
  choose z hz1 hz2 using hcolex
  have hmem : ∀ r, ((z r).1, r) ∈ s.starred := by
    intro r
    have := hz1 r
    rwa [show ((z r).1, r) = z r from Prod.ext rfl (hz2 r).symm]
  have inj : Function.Injective (fun r => (z r).1) := by
    intro r r' h
    by_contra hne
    exact (hI.indep.1 _ (hmem r) _ (hmem r') (fun h' => hne (congrArg Prod.snd h'))).1 h
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp inj)
  have hσ : ∀ r, σ r = (z r).1 := fun r => rfl
  have hstar : s.starred = Finset.univ.image (fun r => (σ r, r)) := by
    ext w
    constructor
    · intro hw
      refine Finset.mem_image.mpr ⟨w.2, Finset.mem_univ _, ?_⟩
      have : w = ((z w.2).1, w.2) := by
        by_contra hne
        exact (hI.indep.1 _ hw _ (hmem w.2) hne).2 rfl
      rw [hσ]; exact this.symm
    · intro hw
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hw
      rw [hσ]; exact hmem r
  refine ⟨σ, hstar, ?_⟩
  have hopt : HeldWolfeCrowder.Assignment.IsOptimalAssignment s.A σ := by
    intro τ
    have h0 : HeldWolfeCrowder.Assignment.assignCost s.A σ = 0 := by
      unfold HeldWolfeCrowder.Assignment.assignCost
      apply Finset.sum_eq_zero
      intro r _
      have := hI.indep.2 _ (hmem r)
      rw [hσ]; exact this
    rw [h0]
    unfold HeldWolfeCrowder.Assignment.assignCost
    exact Finset.sum_nonneg (fun r _ => hI.nonneg _ _)
  obtain ⟨u, v, hf⟩ := reachable_form hs
  have : s.A = fun i j => A i j - u i - v j := by
    funext i j; exact hf i j
  rw [this] at hopt
  exact (r2_core A u v σ).mpr hopt

theorem munkres_core {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (∃ s₀, IsStart A s₀) ∧
    (∀ s₀, IsStart A s₀ → Acc (fun t s => Step s t) s₀) ∧
    (∀ s, Reachable A s → s.phase ≠ Phase.done → ∃ t, Step s t) ∧
    (∀ s, Reachable A s → s.phase = Phase.done →
      ∃ σ : Equiv.Perm (Fin n), s.starred = Finset.univ.image (fun r => (σ r, r)) ∧
        HeldWolfeCrowder.Assignment.IsOptimalAssignment A σ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨_, Finset.univ.toList, Finset.nodup_toList _, fun i j _ => by simp, rfl⟩
  · intro s₀ h0
    exact acc_core A s₀ ⟨s₀, h0, Relation.ReflTransGen.refl⟩
  · intro s hs hne
    exact exists_step A s hs hne
  · intro s hs hd
    exact done_core A s hs hd


theorem reach_tail {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {s t : State n} (hs : Reachable A s)
    (hst : Step s t) : Reachable A t := by
  obtain ⟨s0, h0, hr⟩ := hs
  exact ⟨s0, h0, hr.tail hst⟩

theorem maxIndep_le_stars {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {s : State n}
    (hs : Reachable A s) (hph : s.phase = Phase.step3) :
    maxIndepZeros s.A ≤ s.starred.card := by
  obtain ⟨rk, hI⟩ := reachable_inv hs
  have hcover : CoversZeros s.A s.rowCov s.colCov := by
    intro i j hij
    by_contra hc
    push_neg at hc
    exact hI.s3 hph (i, j) ⟨hc.1, hc.2⟩ hij
  exact (lg_core s.A _ _ hcover).trans (cover_card_le hI)

theorem le_maxIndep {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} {S : Finset (Fin n × Fin n)}
    (h : IsIndepZeros B S) : S.card ≤ maxIndepZeros B := by
  unfold maxIndepZeros
  exact Finset.le_sup (f := Finset.card)
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), h⟩)

theorem step2_card_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {s₂ : State n} {z : Fin n × Fin n}
    (hr : Reachable A s₂) (hph : s₂.phase = Phase.step2 z) :
    s₂.starred.card + 1 ≤ maxIndepZeros s₂.A := by
  obtain ⟨⟨zs, hzs⟩, _⟩ := step2_core A _ z hr hph
  have hstep := Step.augment _ z zs hph hzs
  obtain ⟨hind, hcard⟩ := step2_count_core A _ _ z hr hph hstep
  have hle := le_maxIndep hind
  have e1 : (enterStep1 (augmentState s₂ zs)).A = s₂.A := enterStep1_A _
  have e2 : (enterStep1 (augmentState s₂ zs)).starred.card = s₂.starred.card + 1 := hcard
  rw [e1] at hle
  omega

theorem chain_R {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {s₁ : State n} (hr1 : Reachable A s₁)
    {u : State n} (hu : Relation.ReflTransGen Step1Move s₁ u) :
    Reachable A u ∧ u.A = s₁.A ∧ u.starred = s₁.starred ∧ s₁.rowCov ⊆ u.rowCov ∧
      (u.rowCov = s₁.rowCov → u.colCov = s₁.colCov) := by
  induction hu with
  | refl => exact ⟨hr1, rfl, rfl, Finset.Subset.refl _, fun _ => rfl⟩
  | tail hab hbc ih =>
    rename_i b c
    obtain ⟨hr, hA, hS, hsub, himp⟩ := ih
    obtain ⟨hst, hph⟩ := hbc
    refine ⟨reach_tail hr hst, ?_⟩
    cases hst with
    | prime_go2 p hphase => exact ⟨hA, hS, hsub, himp⟩
    | prime_cover p z hphase hzero hnc hz hrow =>
      refine ⟨hA, hS, hsub.trans (Finset.subset_insert _ _), ?_⟩
      intro heq
      exfalso
      have : p.1 ∈ s₁.rowCov := by rw [← heq]; exact Finset.mem_insert_self _ _
      exact hnc.1 (hsub this)
    | to_step3 hphase hnone => exact ⟨hA, hS, hsub, himp⟩
    | augment z₀ zs hphase => exact absurd (hph.symm.trans hphase) (by simp)
    | reduce h hphase => exact absurd (hph.symm.trans hphase) (by simp)

theorem stronger_core {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s s₁ : State n)
    (hs : Reachable A s) (hph : s.phase = Phase.step3) (h1 : Step s s₁)
    (heq : maxIndepZeros s₁.A = maxIndepZeros s.A) :
    ∀ s₂ : State n, Relation.ReflTransGen Step1Move s₁ s₂ → s₂.phase ≠ Phase.step1 →
      s₂.phase = Phase.step3 ∧ s.rowCov ⊆ s₂.rowCov ∧ s.rowCov.card < s₂.rowCov.card := by
  have hr1 := reach_tail hs h1
  intro s₂ hs₂ hne
  cases hs₂ with
  | refl =>
    exfalso; apply hne
    cases h1 with
    | reduce h hphase => rfl
    | prime_go2 p hphase => exact absurd (hph.symm.trans hphase) (by simp)
    | prime_cover p z hphase => exact absurd (hph.symm.trans hphase) (by simp)
    | to_step3 hphase => exact absurd (hph.symm.trans hphase) (by simp)
    | augment z₀ zs hphase => exact absurd (hph.symm.trans hphase) (by simp)
  | tail hab hbc =>
    rename_i u
    obtain ⟨hru, hA, hS, hsub, himp⟩ := chain_R hr1 hab
    obtain ⟨hst, hphu⟩ := hbc
    -- the facts about s₁ coming from the reduce step
    have hs1 : ∃ h : ℝ, (∃ p, NonCovered s p ∧ s.A p.1 p.2 = h) ∧ s₁.rowCov = s.rowCov ∧
        s₁.colCov = s.colCov ∧ s₁.starred = s.starred ∧
        (∃ p, NonCovered s p ∧ s₁.A p.1 p.2 = 0) := by
      cases h1 with
      | reduce h hphase hmin hle =>
        obtain ⟨p, hp, hpe⟩ := hmin
        refine ⟨h, ⟨p, hp, hpe⟩, rfl, rfl, rfl, p, hp, ?_⟩
        show s.A p.1 p.2 + (if p.1 ∈ s.rowCov then h else 0) - (if p.2 ∈ s.colCov then 0 else h) = 0
        simp [hp.1, hp.2, hpe]
      | prime_go2 p hphase => exact absurd (hph.symm.trans hphase) (by simp)
      | prime_cover p z hphase => exact absurd (hph.symm.trans hphase) (by simp)
      | to_step3 hphase => exact absurd (hph.symm.trans hphase) (by simp)
      | augment z₀ zs hphase => exact absurd (hph.symm.trans hphase) (by simp)
    obtain ⟨h, _, hR, hC, hSt, p0, hp0, hp0z⟩ := hs1
    cases hst with
    | prime_cover p z hphase => exact absurd hphu hne
    | augment z₀ zs hphase => exact absurd (hphu.symm.trans hphase) (by simp)
    | reduce h hphase => exact absurd (hphu.symm.trans hphase) (by simp)
    | prime_go2 p hphase hzero hnc hnostar =>
      exfalso
      have hrv := reach_tail hru (Step.prime_go2 u p hphase hzero hnc hnostar)
      have hc := step2_card_le hrv (z := p) rfl
      have hm := maxIndep_le_stars hs hph
      have e1 : ({ u with primed := insert p u.primed, phase := Phase.step2 p } : State n).A = s₁.A := hA
      have e2 : ({ u with primed := insert p u.primed, phase := Phase.step2 p } : State n).starred = s.starred := by
        show u.starred = s.starred
        rw [hS, hSt]
      rw [e1, e2] at hc
      omega
    | to_step3 hphase hnone =>
      refine ⟨rfl, ?_, ?_⟩
      · intro r hr; exact hsub (hR ▸ hr)
      · by_contra hlt
        have hsub' : s.rowCov ⊆ u.rowCov := fun r hr => hsub (hR ▸ hr)
        have heq' : s.rowCov = u.rowCov :=
          Finset.eq_of_subset_of_card_le hsub' (by
            have : u.rowCov.card ≤ s.rowCov.card := not_lt.mp hlt
            exact this)
        have hcol := himp (heq'.symm.trans hR.symm)
        apply hnone p0 ⟨by rw [← heq']; exact hp0.1, by rw [hcol, hC]; exact hp0.2⟩
        rw [hA]; exact hp0z


theorem RR_trans {a b c : ℕ × ℕ × ℕ} (h1 : RR a b) (h2 : RR b c) : RR a c := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  obtain ⟨c1, c2, c3⟩ := c
  have inv : ∀ {a b c a' b' c' : ℕ}, RR (a, b, c) (a', b', c') →
      a < a' ∨ (a = a' ∧ (b < b' ∨ (b = b' ∧ c < c'))) := by
    intro a b c a' b' c' h
    rcases h with ⟨_, _, h⟩ | ⟨_, h⟩
    · exact Or.inl h
    · right
      refine ⟨rfl, ?_⟩
      rcases h with ⟨_, _, h⟩ | ⟨_, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨rfl, h⟩
  have := inv h1
  have := inv h2
  apply lex3
  omega

theorem RR_inv {a b c a' b' c' : ℕ} (h : RR (a, b, c) (a', b', c')) :
    a < a' ∨ (a = a' ∧ (b < b' ∨ (b = b' ∧ c < c'))) := by
  rcases h with ⟨_, _, h⟩ | ⟨_, h⟩
  · exact Or.inl h
  · right
    refine ⟨rfl, ?_⟩
    rcases h with ⟨_, _, h⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨rfl, h⟩

theorem chain_pairwise {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} :
    ∀ ss : List (State n), List.IsChain Step ss → (∀ s ∈ ss.head?, Reachable A s) →
      (∀ y ∈ ss, Reachable A y) ∧ List.Pairwise (fun x y => RR (mu y) (mu x)) ss := by
  intro ss
  induction ss with
  | nil => intro _ _; exact ⟨by simp, List.Pairwise.nil⟩
  | cons x rest ih =>
    intro hch hh
    have hx : Reachable A x := hh x (by simp)
    cases rest with
    | nil =>
      refine ⟨?_, by simp⟩
      intro y hy; simp at hy; rw [hy]; exact hx
    | cons y rest' =>
      rw [List.isChain_cons_cons] at hch
      have hy : Reachable A y := reach_tail hx hch.1
      obtain ⟨hr, hp⟩ := ih hch.2 (fun s hs => by simp at hs; rw [← hs]; exact hy)
      refine ⟨?_, ?_⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hx
        · exact hr z hz
      · rw [List.pairwise_cons]
        refine ⟨?_, hp⟩
        intro z hz
        have h1 := step_mu_lt hx hch.1
        rcases List.mem_cons.mp hz with rfl | hz
        · exact h1
        · have := (List.pairwise_cons.mp hp).1 z hz
          exact RR_trans this h1

theorem count_core {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (ss : List (State n))
    (hchain : List.IsChain Step ss) (hhead : ∀ s ∈ ss.head?, Reachable A s) (m : ℕ)
    (hm : ∀ s ∈ ss, s.phase = Phase.step3 → maxIndepZeros s.A = m) :
    (ss.filter (fun s => s.phase = Phase.step3)).length ≤ n := by
  obtain ⟨hr, hp⟩ := chain_pairwise (A := A) ss hchain hhead
  -- facts at step 3 states
  have hfacts : ∀ y ∈ ss, y.phase = Phase.step3 → y.starred.card = m ∧ y.rowCov.card < n := by
    intro y hy h3
    obtain ⟨rk, hI⟩ := reachable_inv (hr y hy)
    have h1 := le_maxIndep hI.indep
    have h2 := maxIndep_le_stars (hr y hy) h3
    have h4 := hm y hy h3
    have h5 := hI.small (by rw [h3]; simp)
    have h6 := cover_card_le hI
    refine ⟨by omega, by omega⟩
  have hpf : List.Pairwise (fun x y => RR (mu y) (mu x)) (ss.filter (fun s => s.phase = Phase.step3)) :=
    hp.filter _
  have hpf2 : List.Pairwise (fun x y : State n => x.rowCov.card < y.rowCov.card)
      (ss.filter (fun s => s.phase = Phase.step3)) := by
    refine List.Pairwise.imp_of_mem ?_ hpf
    intro a b ha hb hab
    have ha' := List.mem_filter.mp ha
    have hb' := List.mem_filter.mp hb
    have ha3 : a.phase = Phase.step3 := by simpa using ha'.2
    have hb3 : b.phase = Phase.step3 := by simpa using hb'.2
    obtain ⟨sa, ra⟩ := hfacts a ha'.1 ha3
    obtain ⟨sb, rb⟩ := hfacts b hb'.1 hb3
    unfold mu at hab
    have := RR_inv hab
    have e1 : rankOf a = 2 := rank_step3 ha3
    have e2 : rankOf b = 2 := rank_step3 hb3
    have e3 := hm a ha'.1 ha3
    have e4 := hm b hb'.1 hb3
    have ma := maxIndep_le_n a.A
    have ra' := Finset.card_le_univ a.rowCov
    have rb' := Finset.card_le_univ b.rowCov
    simp only [Fintype.card_fin] at ra' rb'
    omega
  have hnd : ((ss.filter (fun s => s.phase = Phase.step3)).map (fun y => y.rowCov.card)).Nodup := by
    rw [List.nodup_iff_pairwise_ne]  -- Pairwise (≠)
    rw [List.pairwise_map]
    exact hpf2.imp (fun h => ne_of_lt h)
  have hsub : ((ss.filter (fun s => s.phase = Phase.step3)).map (fun y => y.rowCov.card)).toFinset
      ⊆ Finset.range n := by
    intro k hk
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    have hy' := List.mem_filter.mp hy
    have h3 : y.phase = Phase.step3 := by simpa using hy'.2
    exact Finset.mem_range.mpr (hfacts y hy'.1 h3).2
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, List.length_map] at this
  simpa using this


theorem maxmin_core {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n)
    (hs : Reachable A s) (hph : s.phase = Phase.step3) :
    CoversZeros s.A s.rowCov s.colCov ∧
    (∀ p ∈ s.starred, (p.1 ∈ s.rowCov ∧ p.2 ∉ s.colCov) ∨ (p.1 ∉ s.rowCov ∧ p.2 ∈ s.colCov)) ∧
    s.rowCov.card + s.colCov.card = s.starred.card ∧
    (IsIndepZeros s.A s.starred ∧ s.starred.card = maxIndepZeros s.A) ∧
    (∀ R C : Finset (Fin n), CoversZeros s.A R C →
      s.rowCov.card + s.colCov.card ≤ R.card + C.card) := by
  obtain ⟨rk, hI⟩ := reachable_inv hs
  have hcover : CoversZeros s.A s.rowCov s.colCov := by
    intro i j hij
    by_contra hc
    push_neg at hc
    exact hI.s3 hph (i, j) ⟨hc.1, hc.2⟩ hij
  have h1 := le_maxIndep hI.indep
  have h2 := maxIndep_le_stars hs hph
  have h3 := cover_card_le hI
  have h4 := lg_core s.A _ _ hcover
  refine ⟨hcover, ?_, by omega, ⟨hI.indep, by omega⟩, ?_⟩
  · intro p hp
    by_cases h : p.1 ∈ s.rowCov
    · exact Or.inl ⟨h, (hI.once p hp).1 h⟩
    · refine Or.inr ⟨h, ?_⟩
      by_contra hc; exact h ((hI.once p hp).2 hc)
  · intro R C hRC
    have := lg_core s.A R C hRC
    omega

def LineZero {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i, ∃ j, B i j = 0) ∧ (∀ j, ∃ i, B i j = 0)

theorem prelim_linezero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : LineZero (prelimMatrix A) := by
  constructor
  · intro i
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨i, Finset.mem_univ i⟩
    obtain ⟨j0, _, hj0⟩ := Finset.exists_mem_eq_inf' hne (A i)
    refine ⟨j0, ?_⟩
    have hz : rowReduce A i j0 = 0 := by
      unfold rowReduce; rw [← hj0]; ring
    unfold prelimMatrix colReduce
    have h1 : Finset.univ.inf' ⟨i, Finset.mem_univ i⟩ (fun i' => rowReduce A i' j0) ≤ rowReduce A i j0 :=
      Finset.inf'_le (fun i' => rowReduce A i' j0) (Finset.mem_univ i)
    have h2 : 0 ≤ Finset.univ.inf' ⟨i, Finset.mem_univ i⟩ (fun i' => rowReduce A i' j0) := by
      apply Finset.le_inf'
      intro i' _; exact rowReduce_nonneg A i' j0
    show rowReduce A i j0 - _ = 0
    linarith
  · intro j
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨j, Finset.mem_univ j⟩
    obtain ⟨i0, _, hi0⟩ := Finset.exists_mem_eq_inf' hne (fun i' => rowReduce A i' j)
    refine ⟨i0, ?_⟩
    unfold prelimMatrix colReduce
    show rowReduce A i0 j - _ = 0
    have : Finset.univ.inf' ⟨i0, Finset.mem_univ i0⟩ (fun i' => rowReduce A i' j) = rowReduce A i0 j := by
      rw [← hi0]
    rw [this]; ring

theorem linezero_step {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {s t : State n} (hs : Reachable A s)
    (hl : LineZero s.A) (hst : Step s t) : LineZero t.A := by
  obtain ⟨rk, hI⟩ := reachable_inv hs
  cases hst with
  | prime_go2 p hphase => exact hl
  | prime_cover p z hphase => exact hl
  | to_step3 hphase => exact hl
  | augment z₀ zs hphase => rw [enterStep1_A]; exact hl
  | reduce h hphase hmin hle =>
    obtain ⟨p0, hp0, hp0e⟩ := hmin
    have hh : 0 ≤ h := by rw [← hp0e]; exact hI.nonneg _ _
    constructor
    · intro i
      by_cases hi : i ∈ s.rowCov
      · obtain ⟨z, hz, hz1⟩ := hI.rowstar i hi
        refine ⟨z.2, ?_⟩
        have hzc : z.2 ∉ s.colCov := (hI.once z hz).1 (hz1 ▸ hi)
        show s.A i z.2 + (if i ∈ s.rowCov then h else 0) - (if z.2 ∈ s.colCov then 0 else h) = 0
        have := hI.indep.2 z hz
        rw [← hz1] at hi ⊢
        simp [hi, hzc, this]
      · obtain ⟨j, hj⟩ := hl.1 i
        have hjc : j ∈ s.colCov := by
          by_contra hc
          exact hI.s3 hphase (i, j) ⟨hi, hc⟩ hj
        refine ⟨j, ?_⟩
        show s.A i j + (if i ∈ s.rowCov then h else 0) - (if j ∈ s.colCov then 0 else h) = 0
        simp [hi, hjc, hj]
    · intro j
      by_cases hj : j ∈ s.colCov
      · obtain ⟨z, hz, hz2⟩ := hI.colstar j hj
        refine ⟨z.1, ?_⟩
        have hzr : z.1 ∉ s.rowCov := fun hr => (hI.once z hz).1 hr (hz2 ▸ hj)
        show s.A z.1 j + (if z.1 ∈ s.rowCov then h else 0) - (if j ∈ s.colCov then 0 else h) = 0
        have := hI.indep.2 z hz
        rw [← hz2] at hj ⊢
        simp [hzr, hj, this]
      · obtain ⟨i, hi⟩ := hl.2 j
        have hir : i ∈ s.rowCov := by
          by_contra hc
          exact hI.s3 hphase (i, j) ⟨hc, hj⟩ hi
        refine ⟨i, ?_⟩
        show s.A i j + (if i ∈ s.rowCov then h else 0) - (if j ∈ s.colCov then 0 else h) = 0
        simp [hir, hj, hi]

theorem linezero_core {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n)
    (hs : Reachable A s) :
    (∀ i, ∃ j, s.A i j = 0) ∧ (∀ j, ∃ i, s.A i j = 0) := by
  obtain ⟨s₀, h0, hr⟩ := hs
  induction hr with
  | refl =>
    obtain ⟨L, -, -, rfl⟩ := h0
    rw [enterStep1_A]
    exact prelim_linezero A
  | tail hab hbc ih => exact linezero_step ⟨s₀, h0, hab⟩ ih hbc

theorem sumdec_core {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s t : State n) (h : ℝ)
    (hs : Reachable A s) (hph : s.phase = Phase.step3)
    (hmin : ∃ p, NonCovered s p ∧ s.A p.1 p.2 = h) (hle : ∀ q, NonCovered s q → h ≤ s.A q.1 q.2)
    (hst : Step s t) :
    ∑ i, ∑ j, t.A i j =
      ∑ i, ∑ j, s.A i j - (n : ℝ) * ((n : ℝ) - (maxIndepZeros s.A : ℝ)) * h := by
  obtain ⟨-, -, hcard, ⟨-, hmax⟩, -⟩ := maxmin_core A s hs hph
  cases hst with
  | prime_go2 p hphase => exact absurd (hph.symm.trans hphase) (by simp)
  | prime_cover p z hphase => exact absurd (hph.symm.trans hphase) (by simp)
  | to_step3 hphase => exact absurd (hph.symm.trans hphase) (by simp)
  | augment z₀ zs hphase => exact absurd (hph.symm.trans hphase) (by simp)
  | reduce h' hphase hmin' hle' =>
    obtain ⟨p', hp', hpe'⟩ := hmin'
    obtain ⟨p, hp, hpe⟩ := hmin
    have hh : h' = h := by
      have h1 := hle' p hp
      have h2 := hle p' hp'
      linarith
    subst hh
    show ∑ i, ∑ j, (s.A i j + (if i ∈ s.rowCov then h' else 0) - (if j ∈ s.colCov then 0 else h')) = _
    have hb : ∀ j, (if j ∈ s.colCov then (0:ℝ) else h') = h' - (if j ∈ s.colCov then h' else 0) := by
      intro j; split_ifs <;> ring
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hb]
    simp only [← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
      Finset.sum_sub_distrib]
    have hc : (s.rowCov.card : ℝ) + (s.colCov.card : ℝ) = (maxIndepZeros s.A : ℝ) := by
      have : s.rowCov.card + s.colCov.card = maxIndepZeros s.A := by omega
      exact_mod_cast this
    rw [← hc]
    ring

end MunkresAlg.Assignment

open MunkresAlg.Assignment


theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n)
    (hs : Reachable A s) (hph : s.phase = Phase.step3) :
    CoversZeros s.A s.rowCov s.colCov ∧
    (∀ p ∈ s.starred, (p.1 ∈ s.rowCov ∧ p.2 ∉ s.colCov) ∨ (p.1 ∉ s.rowCov ∧ p.2 ∈ s.colCov)) ∧
    s.rowCov.card + s.colCov.card = s.starred.card ∧
    (IsIndepZeros s.A s.starred ∧ s.starred.card = maxIndepZeros s.A) ∧
    (∀ R C : Finset (Fin n), CoversZeros s.A R C →
      s.rowCov.card + s.colCov.card ≤ R.card + C.card) := by
  exact maxmin_core A s hs hph
