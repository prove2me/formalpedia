-- Prove2me | solution 1 for MunkresAlg.Assignment.step3_transformation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:28:39.680887+00:00
-- url     : https://prove2.me/submissions/b7e623bd-3b4d-49f0-b34e-45dfb08dd9f1

import Mathlib
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
    (hne : ph ≠ Phase.done → colsOf u.starred ≠ Finset.univ) :
    Inv { u with phase := ph } rk := by
  have hp3 : ph ≠ Phase.step3 := by rcases hph with h | h <;> rw [h] <;> simp
  have hp2 : ∀ z, ph ≠ Phase.step2 z := by intro z; rcases hph with h | h <;> rw [h] <;> simp
  have e1 : ({ u with phase := ph } : State n).primed = ∅ := hp
  have e2 : ({ u with phase := ph } : State n).rowCov = ∅ := hr
  have e3 : ({ u with phase := ph } : State n).colCov = colsOf u.starred := hc
  refine ⟨hA, hind, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · exact inv_reset_aux u rk _ hA hind hp hr hc (Or.inr rfl) (by intro h'; exact absurd rfl h')
  · exact inv_reset_aux u rk _ hA hind hp hr hc (Or.inl rfl) (by rw [← hc]; exact h |> fun x => fun _ => x)

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
  refine ⟨hI.nonneg, hI.indep, ?_, ?_, ?_, hI.once, hI.rowstar, ?_, hI.colstar, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  refine ⟨hI.nonneg, hI.indep, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

theorem inv_to_step3 {n : ℕ} {s : State n} {rk : Fin n × Fin n → ℕ} (hI : Inv s rk)
    (hphase : s.phase = Phase.step1)
    (hnone : ∀ p : Fin n × Fin n, NonCovered s p → s.A p.1 p.2 ≠ 0) :
    Inv { s with phase := Phase.step3 } rk := by
  refine ⟨hI.nonneg, hI.indep, hI.pzero, hI.prow, hI.pnotstar, hI.once, hI.rowstar, hI.rowprime,
    hI.colstar, hI.pcol, ?_, ?_, hI.order, ?_, ?_⟩
  · intro q hq
    rcases hI.prowcov q hq with h | h
    · exact Or.inl h
    · rw [hphase] at h; exact absurd h (by simp)
  · intro z0 h; exact absurd h (by simp)
  · intro _ p hp; exact hnone p hp
  · intro _; exact hI.small (by rw [hphase]; simp)

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
    hI.colstar, hI.pcol, ?_, ?_, hI.order, ?_, ?_⟩
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

end MunkresAlg.Assignment

open MunkresAlg.Assignment


theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n)
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
  exact step3_core A s hs hph
