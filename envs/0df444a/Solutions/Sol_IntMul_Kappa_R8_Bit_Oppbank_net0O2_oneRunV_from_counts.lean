-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_oneRunV_from_counts
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:30:28.132383+00:00
-- url     : https://prove2.me/submissions/aacbbbd1-9571-49df-86da-011475800c5e

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunMom2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunMom2
open Finset

private noncomputable def hw (e : Edge 529) : ℕ :=
  (Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0

private noncomputable def edgeCount (w : ℕ) : ℕ :=
  (net0O.edges.filter (fun e : Edge 529 => decide (hw e = w))).length

private def histMult (w : ℕ) : ℕ :=
  ((oppbankHist.filter (fun p : ℕ × ℕ => decide (p.1 = w))).map (fun p => p.2)).sum

private theorem oppbankHist_fst_nodup : (oppbankHist.map (·.1)).Nodup := by
  decide

private theorem histMult_of_mem (p : ℕ × ℕ) (hp : p ∈ oppbankHist) :
    histMult p.1 = p.2 := by
  unfold histMult
  set L := oppbankHist.filter (fun q : ℕ × ℕ => decide (q.1 = p.1))
  have hcount : (oppbankHist.map (·.1)).count p.1 = 1 :=
    List.count_eq_one_of_mem oppbankHist_fst_nodup (List.mem_map_of_mem (f := (·.1)) hp)
  have hlen : L.length = 1 := by
    have hrel : (oppbankHist.map (·.1)).count p.1 = L.length := by
      rw [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
      rfl
    omega
  obtain ⟨q, hq⟩ := List.length_eq_one_iff.mp hlen
  have hpL : p ∈ L := List.mem_filter.mpr ⟨hp, by simp [L]⟩
  have hpq : p = q := by
    have : p ∈ [q] := hq ▸ hpL
    simpa using this
  simp [L, hq, hpq]

private theorem sum_map_eq_sum_count {α : Type*} (L : List α) (S : Finset ℕ)
    (f : α → ℕ) (g : ℕ → ℝ) (hmem : ∀ a ∈ L, f a ∈ S) :
    (L.map fun a => g (f a)).sum =
      ∑ w ∈ S, ((L.filter (fun a => decide (f a = w))).length : ℝ) * g w := by
  classical
  induction L with
  | nil => simp
  | cons a L ih =>
    have hmemL : ∀ x ∈ L, f x ∈ S := fun x hx => hmem x (List.mem_cons_of_mem a hx)
    have ha : f a ∈ S := hmem a List.mem_cons_self
    simp only [List.map_cons, List.sum_cons]
    rw [ih hmemL]
    have hterm : ∀ w ∈ S,
        (((a :: L).filter (fun x => decide (f x = w))).length : ℝ) * g w =
          ((if f a = w then (1 : ℕ) else 0) : ℝ) * g w +
            ((L.filter (fun x => decide (f x = w))).length : ℝ) * g w := by
      intro w _
      by_cases hf : f a = w
      · simp [hf, Nat.cast_add, add_mul]; abel
      · simp [hf]
    have hsplit :
        (∑ w ∈ S, (((a :: L).filter (fun x => decide (f x = w))).length : ℝ) * g w) =
          g (f a) + ∑ w ∈ S, ((L.filter (fun x => decide (f x = w))).length : ℝ) * g w := by
      simp_rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
      have hite :
          (∑ w ∈ S, ((if f a = w then (1 : ℕ) else 0) : ℝ) * g w) = g (f a) := by
        simp only [Nat.cast_one, ite_mul, one_mul, zero_mul]
        simpa [ha] using Finset.sum_ite_eq (s := S) (a := f a) (b := g)
      rw [hite]
    linarith [hsplit]

private theorem nodup_sum_eq_finset_sum {α : Type*} [DecidableEq α]
    {β : Type*} [AddCommMonoid β] (L : List α) (hn : L.Nodup) (F : α → β) :
    (L.map F).sum = ∑ x ∈ L.toFinset, F x := by
  classical
  have hval : L.toFinset.val = ↑L := by
    rw [List.toFinset_val, hn.dedup]
  calc
    (L.map F).sum = ((↑L : Multiset α).map F).sum := by
      rw [Multiset.map_coe, Multiset.sum_coe]
    _ = (L.toFinset.val.map F).sum := by rw [hval]
    _ = ∑ x ∈ L.toFinset, F x := (Finset.sum_eq_multiset_sum L.toFinset F).symm

private theorem hist_sum_eq_sum_mult (g : ℕ → ℝ) :
    (oppbankHist.map fun p => (p.2 : ℝ) * g p.1).sum =
      ∑ w ∈ (oppbankHist.map (·.1)).toFinset, (histMult w : ℝ) * g w := by
  classical
  have hn := oppbankHist_fst_nodup
  have hmap :
      oppbankHist.map (fun p => (p.2 : ℝ) * g p.1) =
        (oppbankHist.map (·.1)).map fun w => (histMult w : ℝ) * g w := by
    refine List.ext_getElem (by simp) fun n h₁ h₂ => ?_
    simp only [List.getElem_map]
    have hp : oppbankHist[n] ∈ oppbankHist := List.getElem_mem _
    rw [show (oppbankHist[n]).2 = histMult (oppbankHist[n]).1 from (histMult_of_mem _ hp).symm]; rfl
  rw [hmap]
  exact nodup_sum_eq_finset_sum (oppbankHist.map (·.1)) hn fun w => (histMult w : ℝ) * g w

private theorem edge_mem_hist_keys
    (h : ∀ w, edgeCount w = histMult w) :
    ∀ e ∈ net0O.edges, hw e ∈ (oppbankHist.map (·.1)).toFinset := by
  intro e he
  by_contra hnotin
  have hc := h (hw e)
  have hzm : histMult (hw e) = 0 := by
    unfold histMult
    have : oppbankHist.filter (fun p : ℕ × ℕ => decide (p.1 = hw e)) = [] := by
      refine List.filter_eq_nil_iff.mpr ?_
      intro p hp
      simp only [decide_eq_true_eq]
      intro hp1
      apply hnotin
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, hp1⟩)
    simp [this]
  have hze : edgeCount (hw e) = 0 := by rw [hc, hzm]
  unfold edgeCount at hze
  have hem : e ∈ net0O.edges.filter (fun e' : Edge 529 => decide (hw e' = hw e)) :=
    List.mem_filter.mpr ⟨he, by simp⟩
  have hne : net0O.edges.filter (fun e' : Edge 529 => decide (hw e' = hw e)) ≠ [] :=
    List.ne_nil_of_mem hem
  exact hne (List.length_eq_zero_iff.mp hze)

theorem solution (τ : ℝ)
    (h : ∀ w : ℕ,
      (net0O.edges.filter
          (fun e : Edge 529 =>
            decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = w))).length =
        ((oppbankHist.filter (fun p : ℕ × ℕ => decide (p.1 = w))).map (fun p => p.2)).sum) :
    (net0O.edges.map fun e =>
        oneRunV τ ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0)).sum =
      (oppbankHist.map fun p => (p.2 : ℝ) * oneRunV τ p.1).sum := by
  classical
  set g : ℕ → ℝ := oneRunV τ
  let S : Finset ℕ := (oppbankHist.map (·.1)).toFinset
  have hh : ∀ w, edgeCount w = histMult w := by
    intro w
    exact h w
  have hmem := edge_mem_hist_keys hh
  have hL :
      (net0O.edges.map fun e => g (hw e)).sum =
        ∑ w ∈ S, (edgeCount w : ℝ) * g w := by
    simpa [edgeCount] using
      sum_map_eq_sum_count (α := Edge 529) net0O.edges S hw g hmem
  have hR :
      (oppbankHist.map fun p => (p.2 : ℝ) * g p.1).sum =
        ∑ w ∈ S, (histMult w : ℝ) * g w :=
    hist_sum_eq_sum_mult g
  change (net0O.edges.map fun e => g (hw e)).sum =
    (oppbankHist.map fun p => (p.2 : ℝ) * g p.1).sum
  rw [hL, hR]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [hh w]
