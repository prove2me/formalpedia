-- Prove2me | solution 1 for NegativeDP.EssFinite.theorem91
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T02:58:34.625204+00:00
-- url     : https://prove2.me/submissions/34b11976-e920-45c1-8cb4-b7fb70994639

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_EssFinite_Model
import Theorems.Thm_NegativeDP_EssFinite_return_le_lim
import Theorems.Thm_NegativeDP_EssFinite_lim_le_U_lim
import Theorems.Thm_NegativeDP_Stationary_theorem51f

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

noncomputable def wlim (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) (s : S) : EReal :=
  ⨅ n, (U P π)^[n] 0 s

theorem measurable_wlim (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) :
    Measurable (wlim P π) :=
  Measurable.iInf fun n => measurable_iter P π n

theorem exists_conserving_rule (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A)
    (h : EssentiallyFinite P π) : ∃ f : {g : S → A // Measurable g},
      ∀ s, wlim P π s ≤ NegativeDP.Stationary.T P f (wlim P π) s := by
  classical
  have hex : ∀ s, ∃ i, wlim P π s ≤ NegativeDP.Stationary.T P (π i) (wlim P π) s := by
    intro s
    obtain ⟨k, hk⟩ := U_attained P π h s
    obtain ⟨i, -, hi⟩ := hk (wlim P π)
    exact ⟨i, hi ▸ NegativeDP.EssFinite.lim_le_U_lim P π h s⟩
  have hmeas : ∀ i, MeasurableSet {s | wlim P π s ≤ NegativeDP.Stationary.T P (π i) (wlim P π) s} :=
    fun i => measurableSet_le (measurable_wlim P π) (measurable_T P (π i) (measurable_wlim P π))
  refine ⟨⟨fun s => (π (Nat.find (hex s))).1 s, Measurable.find (fun n => (π n).2) hmeas hex⟩,
    fun s => ?_⟩
  exact Nat.find_spec (hex s)

end NDP3Aux

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

theorem solution (P : NegativeDP.Stationary.Problem S A) (πstar : MarkovPlan S A)
    (h : NegativeDP.EssFinite.EssentiallyFinite P πstar) :
    (∀ s, Tendsto (fun n => (NegativeDP.OptEq.U P πstar)^[n] 0 s) atTop (𝓝 (NegativeDP.Stationary.vstar P s))) ∧
      ∃ f : {g : S → A // Measurable g}, NegativeDP.Stationary.IsOptimal P (stationary f).toPlan := by
  obtain ⟨hanti, hret⟩ := NegativeDP.EssFinite.return_le_lim P πstar h
  obtain ⟨f, hf⟩ := NDP3Aux.exists_conserving_rule P πstar h
  have hw0 : ∀ t, NDP3Aux.wlim P πstar t ≤ 0 := fun t =>
    iInf_le (fun n => (NegativeDP.OptEq.U P πstar)^[n] 0 t) 0
  have hiter : ∀ n t, NDP3Aux.wlim P πstar t ≤ (NegativeDP.Stationary.T P f)^[n] 0 t := by
    intro n
    induction n with
    | zero => exact hw0
    | succ n ih =>
      intro t
      rw [Function.iterate_succ_apply']
      exact (hf t).trans (NDP3Aux.T_mono P f ih t)
  have hIf : ∀ s, NDP3Aux.wlim P πstar s ≤ NegativeDP.Stationary.I P (stationary f).toPlan s :=
    fun s => ge_of_tendsto' ((NegativeDP.Stationary.theorem51f P f).2.2 s) (fun n => hiter n s)
  have hv : ∀ s, NegativeDP.Stationary.vstar P s = NDP3Aux.wlim P πstar s := fun s =>
    le_antisymm (iSup_le fun σ => hret σ s)
      ((hIf s).trans (le_iSup (fun σ => NegativeDP.Stationary.I P σ s) _))
  refine ⟨fun s => ?_, f, fun s => ?_⟩
  · rw [hv s]
    exact tendsto_atTop_iInf (hanti s)
  · rw [hv s]
    exact hIf s
