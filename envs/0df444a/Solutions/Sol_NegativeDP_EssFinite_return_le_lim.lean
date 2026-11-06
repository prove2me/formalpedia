-- Prove2me | solution 1 for NegativeDP.EssFinite.return_le_lim
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T02:56:33.680719+00:00
-- url     : https://prove2.me/submissions/0da211e1-c439-4860-bdbd-761c72dc41d3

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_EssFinite_Model
import Theorems.Thm_NegativeDP_OptEq_theorem82

open MeasureTheory ProbabilityTheory Filter Topology
open DiscountedDP.Stationary (Hist Plan MarkovPlan MarkovPlan.toPlan stationary IsGenerated IsGeneratedPlan)

namespace NDP3Aux

open NegativeDP.Stationary NegativeDP.OptEq NegativeDP.EssFinite

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

theorem Ta_congr (P : NegativeDP.Stationary.Problem S A) {s : S} {a b : A}
    (h : NegativeDP.EssFinite.ActEquiv P s a b) (u : S → EReal) :
    Ta P a u s = Ta P b u s := by
  unfold Ta
  rw [h.2]
  simp only [h.1]

theorem T_eq_Ta (P : NegativeDP.Stationary.Problem S A) (f : {g : S → A // Measurable g})
    (u : S → EReal) (s : S) : NegativeDP.Stationary.T P f u s = Ta P (f.1 s) u s := rfl

theorem Ta_mono (P : NegativeDP.Stationary.Problem S A) (a : A) {u v : S → EReal}
    (huv : ∀ t, u t ≤ v t) (s : S) : Ta P a u s ≤ Ta P a v s := by
  unfold Ta
  rw [EReal.neg_le_neg_iff]
  exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr (lintegral_mono fun t =>
    add_le_add le_rfl (EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (huv t))))

theorem T_mono (P : NegativeDP.Stationary.Problem S A) (f : {g : S → A // Measurable g})
    {u v : S → EReal} (huv : ∀ t, u t ≤ v t) (s : S) :
    NegativeDP.Stationary.T P f u s ≤ NegativeDP.Stationary.T P f v s :=
  Ta_mono P (f.1 s) huv s

theorem U_mono (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A)
    {u v : S → EReal} (huv : ∀ t, u t ≤ v t) (s : S) : U P π u s ≤ U P π v s :=
  iSup_mono fun n => T_mono P (π n) huv s

theorem T_nonpos (P : NegativeDP.Stationary.Problem S A) (f : {g : S → A // Measurable g})
    (u : S → EReal) (s : S) : NegativeDP.Stationary.T P f u s ≤ 0 := by
  unfold NegativeDP.Stationary.T
  rw [EReal.neg_le, neg_zero]
  exact EReal.coe_ennreal_nonneg _

theorem U_nonpos (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A)
    (u : S → EReal) (s : S) : U P π u s ≤ 0 :=
  iSup_le fun n => T_nonpos P (π n) u s

/-- Under essential finiteness, `U u (s) = sup_a T_a u (s)`. -/
theorem U_eq_iSup_Ta (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A)
    (h : EssentiallyFinite P π) (u : S → EReal) (s : S) :
    U P π u s = ⨆ a : A, Ta P a u s := by
  obtain ⟨pieces, -, -, hcov, hrep⟩ := h
  apply le_antisymm
  · exact iSup_le fun n => le_iSup (fun a => Ta P a u s) ((π n).1 s)
  · refine iSup_le fun a => ?_
    have hs : s ∈ ⋃ n, pieces n := by rw [hcov]; trivial
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hs
    obtain ⟨i, -, hi⟩ := hrep k s hk a
    rw [← Ta_congr P hi u]
    exact le_iSup (fun n => NegativeDP.Stationary.T P (π n) u s) i

/-- Under essential finiteness, at each state only finitely many rules matter. -/
theorem piece_bound (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A)
    (h : EssentiallyFinite P π) (s : S) :
    ∃ k, ∀ (u : S → EReal) n, ∃ i ≤ k,
      NegativeDP.Stationary.T P (π n) u s = NegativeDP.Stationary.T P (π i) u s := by
  obtain ⟨pieces, -, -, hcov, hrep⟩ := h
  have hs : s ∈ ⋃ n, pieces n := by rw [hcov]; trivial
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hs
  refine ⟨k, fun u n => ?_⟩
  obtain ⟨i, hik, hi⟩ := hrep k s hk ((π n).1 s)
  exact ⟨i, hik, (Ta_congr P hi u).symm⟩

/-- Under essential finiteness, the supremum defining `U u (s)` is attained by a rule `π i`
with `i ≤ k`, where `k` depends only on `s`. -/
theorem U_attained (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A)
    (h : EssentiallyFinite P π) (s : S) :
    ∃ k, ∀ u : S → EReal, ∃ i ≤ k, U P π u s = NegativeDP.Stationary.T P (π i) u s := by
  obtain ⟨k, hk⟩ := piece_bound P π h s
  refine ⟨k, fun u => ?_⟩
  obtain ⟨i0, hi0, hmax⟩ := Finset.exists_max_image (Finset.range (k + 1))
    (fun i => NegativeDP.Stationary.T P (π i) u s) ⟨0, by simp⟩
  refine ⟨i0, Nat.lt_succ_iff.mp (Finset.mem_range.mp hi0), le_antisymm ?_
    (le_iSup (fun n => NegativeDP.Stationary.T P (π n) u s) i0)⟩
  refine iSup_le fun n => ?_
  obtain ⟨i, hik, hi⟩ := hk u n
  rw [hi]
  exact hmax i (Finset.mem_range.mpr (Nat.lt_succ_of_le hik))

theorem iter_succ_le (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) :
    ∀ n s, (U P π)^[n + 1] 0 s ≤ (U P π)^[n] 0 s := by
  intro n
  induction n with
  | zero => intro s; simpa using U_nonpos P π 0 s
  | succ n ih =>
    intro s
    rw [show (U P π)^[n+1+1] 0 s = U P π ((U P π)^[n+1] 0) s from
        congrFun (Function.iterate_succ_apply' _ _ _) s,
      show (U P π)^[n+1] 0 s = U P π ((U P π)^[n] 0) s from
        congrFun (Function.iterate_succ_apply' _ _ _) s]
    exact U_mono P π ih s

theorem iter_antitone (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) (s : S) :
    Antitone (fun n => (U P π)^[n] 0 s) :=
  antitone_nat_of_succ_le fun n => iter_succ_le P π n s

theorem I_nonpos (P : NegativeDP.Stationary.Problem S A) (σ : Plan (S := S) (A := A)) (s : S) :
    NegativeDP.Stationary.I P σ s ≤ 0 := by
  unfold NegativeDP.Stationary.I
  rw [EReal.neg_le, neg_zero]
  exact EReal.coe_ennreal_nonneg _

theorem vstar_nonpos (P : NegativeDP.Stationary.Problem S A) (s : S) :
    NegativeDP.Stationary.vstar P s ≤ 0 :=
  iSup_le fun σ => I_nonpos P σ s

theorem vstar_le_iter (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A)
    (h : EssentiallyFinite P π) : ∀ n s, NegativeDP.Stationary.vstar P s ≤ (U P π)^[n] 0 s := by
  intro n
  induction n with
  | zero => intro s; simpa using vstar_nonpos P s
  | succ n ih =>
    intro s
    rw [Function.iterate_succ_apply', U_eq_iSup_Ta P π h, theorem82 P s]
    exact iSup_mono fun a => Ta_mono P a ih s

end NDP3Aux

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

theorem solution (P : NegativeDP.Stationary.Problem S A) (πstar : MarkovPlan S A)
    (h : NegativeDP.EssFinite.EssentiallyFinite P πstar) :
    (∀ s, Antitone (fun n => (NegativeDP.OptEq.U P πstar)^[n] 0 s)) ∧
      ∀ (σ : Plan (S := S) (A := A)) (s : S), NegativeDP.Stationary.I P σ s ≤ ⨅ n, (NegativeDP.OptEq.U P πstar)^[n] 0 s :=
  ⟨fun s => NDP3Aux.iter_antitone P πstar s, fun σ s =>
    (le_iSup (fun σ => NegativeDP.Stationary.I P σ s) σ).trans
      (le_iInf fun n => NDP3Aux.vstar_le_iter P πstar h n s)⟩
