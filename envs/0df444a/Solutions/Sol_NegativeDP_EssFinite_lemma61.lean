-- Prove2me | solution 1 for NegativeDP.EssFinite.lemma61
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T02:59:29.993237+00:00
-- url     : https://prove2.me/submissions/6ee23c0e-ec73-42de-9435-22c70d256578

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_EssFinite_Model
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

theorem plan_ext {p q : Plan (S := S) (A := A)} (h : ∀ k, p.κ k = q.κ k) : p = q := by
  cases p; cases q
  congr
  funext k
  exact h k

/-- A Markov plan is its first rule followed by its shift. -/
theorem toPlan_eq_prefix (σ : MarkovPlan S A) :
    σ.toPlan = prefixPlan (σ 0) (MarkovPlan.toPlan (fun k => σ (k + 1))) := by
  apply plan_ext
  intro k
  cases k with
  | zero => rfl
  | succ k => exact Kernel.ext fun h => rfl

/-- A `π`-generated rule has `T u ≤ U u`. -/
theorem T_le_U_of_generated (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A)
    (f : {g : S → A // Measurable g}) (hf : IsGenerated π f) (u : S → EReal) (s : S) :
    NegativeDP.Stationary.T P f u s ≤ U P π u s := by
  obtain ⟨pieces, -, -, hcov, hpc⟩ := hf
  have hs : s ∈ ⋃ n, pieces n := by rw [hcov]; trivial
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hs
  rw [T_eq_Ta, hpc k s hk]
  exact le_iSup (fun n => NegativeDP.Stationary.T P (π n) u s) k

theorem I_generated_le_iter (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) :
    ∀ n (σ : MarkovPlan S A), IsGeneratedPlan π σ → ∀ s,
      NegativeDP.Stationary.I P σ.toPlan s ≤ (U P π)^[n] 0 s := by
  intro n
  induction n with
  | zero =>
    intro σ _ s
    simp only [Function.iterate_zero, id_eq, Pi.zero_apply]
    unfold NegativeDP.Stationary.I
    rw [EReal.neg_le, neg_zero]
    exact EReal.coe_ennreal_nonneg _
  | succ n ih =>
    intro σ hσ s
    have hshift : IsGeneratedPlan π (fun k => σ (k + 1)) := fun k => hσ (k + 1)
    rw [toPlan_eq_prefix σ, ← (theorem51f P (σ 0)).1, Function.iterate_succ_apply']
    exact (T_mono P (σ 0) (ih _ hshift) s).trans (T_le_U_of_generated P π (σ 0) (hσ 0) _ s)

end NDP3Aux

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

theorem solution (P : NegativeDP.Stationary.Problem S A) (πhat : MarkovPlan S A) :
    ∃ w : S → EReal,
      (∀ s, Tendsto (fun n => (NegativeDP.OptEq.U P πhat)^[n] 0 s) atTop (𝓝 (w s))) ∧
      (∀ s, (⨆ σ : {σ : MarkovPlan S A // IsGeneratedPlan πhat σ}, NegativeDP.Stationary.I P σ.1.toPlan s) ≤ w s) ∧
      ∀ s, (⨆ f : {f : {g : S → A // Measurable g} // IsGenerated πhat f},
              NegativeDP.Stationary.I P (stationary f.1).toPlan s) ≤
            ⨆ σ : {σ : MarkovPlan S A // IsGeneratedPlan πhat σ}, NegativeDP.Stationary.I P σ.1.toPlan s := by
  refine ⟨fun s => ⨅ n, (NegativeDP.OptEq.U P πhat)^[n] 0 s, fun s =>
    tendsto_atTop_iInf (NDP3Aux.iter_antitone P πhat s), fun s => ?_, fun s => ?_⟩
  · exact iSup_le fun σ => le_iInf fun n => NDP3Aux.I_generated_le_iter P πhat n σ.1 σ.2 s
  · exact iSup_le fun f => le_iSup (fun σ : {σ : MarkovPlan S A // IsGeneratedPlan πhat σ} =>
      NegativeDP.Stationary.I P σ.1.toPlan s) ⟨stationary f.1, fun _ => f.2⟩
