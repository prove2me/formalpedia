-- Prove2me | solution 1 for KKBinPacking.GeometricGrouping.algorithm2_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-02T12:24:27.340714+00:00
-- url     : https://prove2.me/submissions/e04dd93a-25f4-405f-890f-3daf94e1c012
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_KKBinPacking_GeometricGrouping_alg2_step3_card_le
import Theorems.Thm_KKBinPacking_GeometricGrouping_alg2_iterations_le
import Theorems.Thm_KKBinPacking_GeometricGrouping_alg2_lin_telescoping
import Theorems.Thm_KKBinPacking_GeometricGrouping_geomGroup_bounds
import Theorems.Thm_KKBinPacking_GeometricGrouping_lin_le_opt
import Theorems.Thm_KKBinPacking_GeometricGrouping_anyFit_card_le

set_option autoImplicit false

open KKBinPacking.Shared KKBinPacking.GeometricGrouping

private lemma filter_sum_le (I : Multiset ℝ) (p : ℝ → Prop) [DecidablePred p]
    (hI : ∀ x ∈ I, 0 ≤ x) : (I.filter p).sum ≤ I.sum := by
  revert hI
  induction I using Multiset.induction_on with
  | empty => simp
  | @cons a I ih =>
    intro hI
    have ha := hI a (by simp)
    have htail := ih (fun x hx => hI x (by simp [hx]))
    by_cases hpa : p a <;> simp [hpa] <;> linarith

private lemma opt_filter_le (I : Multiset ℝ) (hI : IsInstance I)
    (p : ℝ → Prop) [DecidablePred p] : OPT (I.filter p) ≤ OPT I := by
  classical
  have hex : {B : ℕ | ∃ P : Multiset (Multiset ℝ),
      IsPacking I P ∧ Multiset.card P = B}.Nonempty := by
    refine ⟨I.card, I.map (fun x => ({x} : Multiset ℝ)), ?_, by simp⟩
    constructor
    · exact Multiset.sum_map_singleton I
    · intro b hb
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hb
      simpa using (hI x hx).2.le
  obtain ⟨P, hP, hcard⟩ := Nat.sInf_mem hex
  apply Nat.sInf_le
  refine ⟨P.map (Multiset.filter p), ?_, ?_⟩
  · constructor
    · simp [← Multiset.filter_join, hP.1]
    · intro b hb
      obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.mp hb
      apply le_trans (filter_sum_le c p ?_) (hP.2 c hc)
      intro x hx
      exact (hI x (hP.1 ▸ Multiset.mem_join.mpr ⟨c, hc, hx⟩)).1.le
  · simpa only [Multiset.card_map, OPT] using hcard

private lemma anyFit_packing (P : Multiset (Multiset ℝ)) (S : Multiset ℝ)
    (Q : Multiset (Multiset ℝ)) (h : AnyFit P S Q)
    (hS : IsInstance S) (hP : ∀ b ∈ P, b.sum ≤ 1) :
    Q.join = P.join + S ∧ ∀ b ∈ Q, b.sum ≤ 1 := by
  classical
  revert hS hP
  induction h with
  | done P =>
    intro _ hP
    exact ⟨by simp, hP⟩
  | intoBin P S Q p b hp hb hfit hrec ih =>
    intro hS hP
    have hS' : IsInstance (S.erase p) := fun x hx =>
      hS x (Multiset.mem_of_mem_erase hx)
    have hP' : ∀ c ∈ P.erase b + {p ::ₘ b}, c.sum ≤ 1 := by
      intro c hc
      simp only [Multiset.mem_add, Multiset.mem_singleton] at hc
      rcases hc with hc | rfl
      · exact hP c (Multiset.mem_of_mem_erase hc)
      · simpa [add_comm] using hfit
    obtain ⟨heq, hlegal⟩ := ih hS' hP'
    refine ⟨heq.trans ?_, hlegal⟩
    have hb' := Multiset.cons_erase hb
    have hp' := Multiset.cons_erase hp
    conv_rhs => rw [← hb', ← hp']
    simp [add_left_comm, add_comm]
  | newBin P S Q p hp hfull hrec ih =>
    intro hS hP
    have hS' : IsInstance (S.erase p) := fun x hx =>
      hS x (Multiset.mem_of_mem_erase hx)
    have hP' : ∀ c ∈ P + {{p}}, c.sum ≤ 1 := by
      intro c hc
      simp only [Multiset.mem_add, Multiset.mem_singleton] at hc
      rcases hc with hc | rfl
      · exact hP c hc
      · simpa using (hS p hp).2.le
    obtain ⟨heq, hlegal⟩ := ih hS' hP'
    refine ⟨heq.trans ?_, hlegal⟩
    conv_rhs => rw [← Multiset.cons_erase hp]
    simp [add_assoc]

/-- Reduction of the complete algorithm estimate to its counting, LP, grouping,
iteration, and insertion milestones. The imported open milestones remain obligations. -/
theorem solution (k : ℕ) (hk : 2 ≤ k) (g : ℝ) (hg0 : 0 < g) (hg1 : g ≤ 1 / 2)
    (I : Multiset ℝ) (hI : IsInstance I) (hS : 1 ≤ SIZE I)
    (P : Multiset (Multiset ℝ)) (hP : Alg2Run k g I P) :
    IsPacking I P ∧
      (Multiset.card P : ℝ) ≤
        max ((1 + 2 * g) * (OPT I : ℝ) + 1)
          ((OPT I : ℝ) + (1 + Real.log (SIZE I) / Real.log k) *
              (1 + 4 * (k : ℝ) + 2 * (k : ℝ) * Real.log (1 / g)) +
            2 + (2 / (1 - 1 / (k : ℝ))) * Real.log (1 / g)) := by
  classical
  obtain ⟨tr, rfl⟩ := hP
  let P₀ := alg2Step3Bins tr.t tr.Bp tr.PJ' tr.P3
  have hs3 := alg2_step3_card_le k hk g hg0 I hI tr
  have hsmall : IsInstance (I.filter (fun p => p ≤ g)) :=
    fun x hx => hI x (Multiset.mem_filter.mp hx).1
  have hpfull := anyFit_packing P₀ (I.filter (fun p => p ≤ g)) tr.P
    tr.P_insert hsmall hs3.1.2
  have hpartition : I.filter (fun p => g < p) + I.filter (fun p => p ≤ g) = I := by
    simpa only [not_lt] using Multiset.filter_add_not (fun p => g < p) I
  refine ⟨⟨?_, hpfull.2⟩, ?_⟩
  · exact hpfull.1.trans (by rw [hs3.1.1, hpartition])
  have hcard : (tr.P.card : ℝ) ≤ max (P₀.card : ℝ) ((1 + 2 * g) * (OPT I : ℝ) + 1) := by
    apply anyFit_card_le I hI (2 * g) (by positivity) (by linarith) P₀
    · simpa using hs3.1
    · simpa using tr.P_insert
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
  have hlogg : 0 ≤ Real.log (1 / g) := Real.log_nonneg (by
    apply (le_div_iff₀ hg0).mpr
    linarith)
  have hcoeff : 0 ≤ 1 + 4 * (k : ℝ) + 2 * (k : ℝ) * Real.log (1 / g) := by positivity
  have hlogI : 0 ≤ Real.log (SIZE I) := Real.log_nonneg hS
  have hfactor : 0 ≤ 1 + Real.log (SIZE I) / Real.log k := by positivity
  have hmain : (P₀.card : ℝ) ≤ (OPT I : ℝ) +
      (1 + Real.log (SIZE I) / Real.log k) *
        (1 + 4 * (k : ℝ) + 2 * (k : ℝ) * Real.log (1 / g)) +
      2 + (2 / (1 - 1 / (k : ℝ))) * Real.log (1 / g) := by
    by_cases ht : tr.t = 0
    · have hzero := hs3.2
      simp only [ht, Finset.range_zero, Finset.sum_empty, Nat.cast_zero,
        zero_mul, zero_add] at hzero
      have hprod := mul_nonneg hfactor hcoeff
      have hopt : (0 : ℝ) ≤ OPT I := by positivity
      simp only [P₀, ht]
      linarith
    · have htpos : 1 ≤ tr.t := by omega
      have hinst : IsInstance (tr.inst 0) := by
        rw [tr.inst_zero]
        exact fun x hx => hI x (Multiset.mem_filter.mp hx).1
      have hsize_le : SIZE (tr.inst 0) ≤ SIZE I := by
        rw [tr.inst_zero]
        exact filter_sum_le I _ (fun x hx => (hI x hx).1.le)
      have hden : 0 < 1 - 1 / (k : ℝ) := by
        have : 1 / (k : ℝ) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
        linarith
      have hinitpos : 0 < SIZE (tr.inst 0) := by
        have hlo := tr.loop_run 0 (by omega)
        have hterm : 0 ≤ (1 / (1 - 1 / (k : ℝ))) * Real.log (1 / g) := by positivity
        dsimp [alg2Threshold] at hlo
        linarith
      have hne : tr.inst 0 ≠ 0 := by
        intro he
        simp [he, SIZE] at hinitpos
      have hlin : LIN (geomJ k (tr.inst 0)) ≤ (OPT I : ℝ) := by
        apply le_trans (geomGroup_bounds (tr.inst 0) hinst hne k hk).2.1.1
        apply le_trans (lin_le_opt (tr.inst 0) hinst)
        rw [tr.inst_zero]
        exact_mod_cast opt_filter_le I hI (fun p => g < p)
      have hit : (tr.t : ℝ) ≤ 1 + Real.log (SIZE I) / Real.log k := by
        have hit₀ := alg2_iterations_le k hk g hg0 (by linarith) I hI tr htpos
        have hlogs := Real.log_le_log hinitpos hsize_le
        have hquot := div_le_div_of_nonneg_right hlogs hlogk.le
        linarith
      have hprincipal := (alg2_lin_telescoping k hk g hg0 I hI tr).2
      have hcount := hs3.2
      have hmul := mul_le_mul_of_nonneg_right hit hcoeff
      dsimp [P₀]
      nlinarith
  exact hcard.trans (max_le (hmain.trans (le_max_right _ _)) (le_max_left _ _))
