-- Prove2me | solution 1 for NegativeDP.EssFinite.lim_le_U_lim
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T02:56:34.379735+00:00
-- url     : https://prove2.me/submissions/bdd51259-62bf-45e0-ae16-4aeba86939ee

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_EssFinite_Model

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

/-! ### Measurability -/

theorem measurable_T (P : NegativeDP.Stationary.Problem S A) (f : {g : S → A // Measurable g})
    {u : S → EReal} (hu : Measurable u) : Measurable (NegativeDP.Stationary.T P f u) := by
  have hg : Measurable (fun s : S => (s, f.1 s)) := measurable_id.prodMk f.2
  have : IsMarkovKernel P.q := P.q_markov
  have hF : Measurable (fun st : S × S =>
      ENNReal.ofReal (-P.r (st.1, f.1 st.1, st.2)) + (-(u st.2)).toENNReal) := by
    refine Measurable.add (f := fun st : S × S => ENNReal.ofReal (-P.r (st.1, f.1 st.1, st.2)))
      (g := fun st : S × S => (-(u st.2)).toENNReal) ?_ ?_
    · exact ENNReal.measurable_ofReal.comp ((P.r_measurable.comp
        (measurable_fst.prodMk ((f.2.comp measurable_fst).prodMk measurable_snd))).neg)
    · exact EReal.continuous_toENNReal.measurable.comp
        (continuous_neg.measurable.comp (hu.comp measurable_snd))
  have hL := hF.lintegral_kernel_prod_right' (κ := P.q.comap (fun s : S => (s, f.1 s)) hg)
  have : NegativeDP.Stationary.T P f u = fun s => -(((∫⁻ t, ENNReal.ofReal (-P.r (s, f.1 s, t))
      + (-(u t)).toENNReal ∂(P.q.comap (fun s : S => (s, f.1 s)) hg) s : ENNReal)) : EReal) := by
    funext s; rfl
  rw [this]
  exact continuous_neg.measurable.comp (measurable_coe_ennreal_ereal.comp hL)

theorem measurable_U (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A)
    {u : S → EReal} (hu : Measurable u) : Measurable (U P π u) := by
  have : U P π u = fun s => ⨆ n : ℕ, NegativeDP.Stationary.T P (π n) u s := rfl
  rw [this]
  exact Measurable.iSup fun n => measurable_T P (π n) hu

theorem measurable_iter (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) :
    ∀ n, Measurable ((U P π)^[n] 0) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    rw [Function.iterate_succ']
    exact measurable_U P π ih

/-- Monotone convergence for `T` along a decreasing sequence. -/
theorem T_tendsto_of_antitone (P : NegativeDP.Stationary.Problem S A)
    (f : {g : S → A // Measurable g}) (v : ℕ → S → EReal) (hv : ∀ n, Measurable (v n))
    (hanti : ∀ t, Antitone (fun n => v n t)) (s : S) :
    Tendsto (fun n => NegativeDP.Stationary.T P f (v n) s) atTop
      (𝓝 (NegativeDP.Stationary.T P f (fun t => ⨅ n, v n t) s)) := by
  unfold NegativeDP.Stationary.T
  set G : ℕ → S → ENNReal := fun n t => ENNReal.ofReal (-P.r (s, f.1 s, t)) + (-(v n t)).toENNReal
  have hGmono : Monotone G := by
    intro m n hmn t
    exact add_le_add le_rfl (EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hanti t hmn)))
  have hGmeas : ∀ n, Measurable (G n) := fun n =>
    Measurable.add (f := fun t => ENNReal.ofReal (-P.r (s, f.1 s, t)))
      (g := fun t => (-(v n t)).toENNReal)
      (ENNReal.measurable_ofReal.comp ((P.r_measurable.comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id))).neg))
      (EReal.continuous_toENNReal.measurable.comp
      (continuous_neg.measurable.comp (hv n)))
  have hpt : ∀ t, ENNReal.ofReal (-P.r (s, f.1 s, t)) + (-(⨅ n, v n t)).toENNReal = ⨆ n, G n t := by
    intro t
    have h1 : Tendsto (fun n => G n t) atTop
        (𝓝 (ENNReal.ofReal (-P.r (s, f.1 s, t)) + (-(⨅ n, v n t)).toENNReal)) := by
      refine tendsto_const_nhds.add ?_
      exact (EReal.continuous_toENNReal.tendsto _).comp
        ((continuous_neg.tendsto _).comp (tendsto_atTop_iInf (hanti t)))
    exact tendsto_nhds_unique h1 (tendsto_atTop_iSup fun m n hmn => hGmono hmn t)
  have hint : (∫⁻ t, ENNReal.ofReal (-P.r (s, f.1 s, t)) + (-(⨅ n, v n t)).toENNReal
      ∂P.q (s, f.1 s)) = ⨆ n, ∫⁻ t, G n t ∂P.q (s, f.1 s) := by
    simp_rw [hpt]
    exact lintegral_iSup hGmeas hGmono
  rw [hint]
  refine (continuous_neg.tendsto _).comp ((continuous_coe_ennreal_ereal.tendsto _).comp ?_)
  exact tendsto_atTop_iSup fun m n hmn => lintegral_mono fun t => hGmono hmn t

/-- The limit of value iteration. -/
noncomputable def wlim (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) (s : S) : EReal :=
  ⨅ n, (U P π)^[n] 0 s

theorem measurable_wlim (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) :
    Measurable (wlim P π) :=
  Measurable.iInf fun n => measurable_iter P π n

theorem wlim_le_U_wlim (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A)
    (h : EssentiallyFinite P π) (s : S) : wlim P π s ≤ U P π (wlim P π) s := by
  by_contra hlt
  push Not at hlt
  -- every rule falls strictly below `wlim s` after finitely many steps
  have hT : ∀ i, ∃ N, NegativeDP.Stationary.T P (π i) ((U P π)^[N] 0) s < wlim P π s := by
    intro i
    have hlim := T_tendsto_of_antitone P (π i) (fun n => (U P π)^[n] 0) (measurable_iter P π)
      (fun t => iter_antitone P π t) s
    have hle : NegativeDP.Stationary.T P (π i) (wlim P π) s < wlim P π s :=
      lt_of_le_of_lt (le_iSup (fun n => NegativeDP.Stationary.T P (π n) (wlim P π) s) i) hlt
    exact (hlim.eventually (gt_mem_nhds hle)).exists
  choose N hN using hT
  obtain ⟨k, hk⟩ := U_attained P π h s
  set M := (Finset.range (k + 1)).sup N
  obtain ⟨i, hik, hi⟩ := hk ((U P π)^[M] 0)
  have hNM : N i ≤ M := Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_of_le hik))
  have h1 : (U P π)^[M + 1] 0 s < wlim P π s := by
    rw [Function.iterate_succ_apply', hi]
    exact lt_of_le_of_lt (T_mono P (π i) (fun t => iter_antitone P π t hNM) s) (hN i)
  exact absurd (iInf_le (fun n => (U P π)^[n] 0 s) (M + 1)) (not_le.mpr h1)

end NDP3Aux

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

theorem solution (P : NegativeDP.Stationary.Problem S A) (πstar : MarkovPlan S A)
    (h : NegativeDP.EssFinite.EssentiallyFinite P πstar) :
    ∀ s, (⨅ n, (NegativeDP.OptEq.U P πstar)^[n] 0 s) ≤ NegativeDP.OptEq.U P πstar (fun t => ⨅ n, (NegativeDP.OptEq.U P πstar)^[n] 0 t) s :=
  fun s => NDP3Aux.wlim_le_U_wlim P πstar h s
