-- Prove2me | solution 1 for NegativeDP.OptEq.theorem52b
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:52:39.324992+00:00
-- url     : https://prove2.me/submissions/a6974864-ed43-4104-aaf7-13ca3d7b678c

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_OptEq_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan stationary IsGenerated IsGeneratedPlan)

namespace Aux_NegativeDP_OptEq_theorem52b

/-- Adding a real constant on the right is an order automorphism of `EReal`. -/
noncomputable def addIso (c : ℝ) : EReal ≃o EReal where
  toFun e := e + (c : EReal)
  invFun e := e + ((-c : ℝ) : EReal)
  left_inv e := by
    show e + (c : EReal) + ((-c : ℝ) : EReal) = e
    rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]
  right_inv e := by
    show e + ((-c : ℝ) : EReal) + (c : EReal) = e
    rw [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]
  map_rel_iff' := by
    intro a b
    show a + (c : EReal) ≤ b + (c : EReal) ↔ a ≤ b
    constructor
    · intro h
      have h2 := add_le_add h (le_refl ((-c : ℝ) : EReal))
      rwa [add_assoc, add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero,
        add_zero, add_zero] at h2
    · intro h
      exact add_le_add h le_rfl

theorem iSup_add {ι : Sort*} (c : ℝ) (f : ι → EReal) :
    (⨆ i, f i) + (c : EReal) = ⨆ i, (f i + (c : EReal)) :=
  (addIso c).map_iSup f

theorem pointwise (a : EReal) (c : ℝ) (ha : 0 ≤ a) (hac : 0 ≤ a - (c : EReal)) :
    (a - (c : EReal)).toENNReal + ENNReal.ofReal c = a.toENNReal + ENNReal.ofReal (-c) := by
  induction a with
  | bot => exact absurd ha (by simp)
  | top => simp
  | coe r =>
    rw [← EReal.coe_sub, EReal.real_coe_toENNReal, EReal.real_coe_toENNReal]
    have hr : 0 ≤ r := by exact_mod_cast ha
    have hrc : 0 ≤ r - c := by
      have : ((r - c : ℝ) : EReal) = (r : EReal) - (c : EReal) := EReal.coe_sub r c
      rw [← this] at hac; exact_mod_cast hac
    rcases le_or_gt 0 c with hc | hc
    · rw [ENNReal.ofReal_of_nonpos (by linarith : -c ≤ 0), add_zero, ← ENNReal.ofReal_add hrc hc]
      ring_nf
    · rw [ENNReal.ofReal_of_nonpos hc.le, add_zero, ← ENNReal.ofReal_add hr (by linarith)]
      ring_nf

theorem final (I I' : ℝ≥0∞) (c : ℝ) (h : I' + ENNReal.ofReal c = I + ENNReal.ofReal (-c)) :
    -((I' : EReal)) = -((I : EReal)) + (c : EReal) := by
  by_cases hI : I = ⊤
  · have hI' : I' = ⊤ := by
      rw [hI, top_add] at h
      by_contra hne
      exact ENNReal.add_ne_top.mpr ⟨hne, ENNReal.ofReal_ne_top⟩ h
    rw [hI, hI']
    simp
  · have hI' : I' ≠ ⊤ := by
      intro hI'
      rw [hI', top_add] at h
      exact ENNReal.add_ne_top.mpr ⟨hI, ENNReal.ofReal_ne_top⟩ h.symm
    have h2 := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_add hI' ENNReal.ofReal_ne_top, ENNReal.toReal_add hI ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal', ENNReal.toReal_ofReal'] at h2
    rw [← EReal.coe_ennreal_toReal hI, ← EReal.coe_ennreal_toReal hI', ← EReal.coe_neg,
      ← EReal.coe_neg, ← EReal.coe_add, EReal.coe_eq_coe_iff]
    have : max c 0 - max (-c) 0 = c := by
      rcases le_or_gt 0 c with hc | hc
      · rw [max_eq_left hc, max_eq_right (by linarith)]; ring
      · rw [max_eq_right hc.le, max_eq_left (by linarith)]; ring
    linarith

end Aux_NegativeDP_OptEq_theorem52b

open NegativeDP.OptEq Aux_NegativeDP_OptEq_theorem52b in
theorem solution {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) (u : S → EReal) (c : ℝ)
    (hu : NegativeDP.Stationary.IsNegM u) (huc : NegativeDP.Stationary.IsNegM (fun t => u t + (c : EReal))) :
    ∀ s, U P π (fun t => u t + (c : EReal)) s = U P π u s + (c : EReal) := by
  intro s
  haveI := P.q_markov
  have hT : ∀ n, NegativeDP.Stationary.T P (π n) (fun t => u t + (c : EReal)) s =
      NegativeDP.Stationary.T P (π n) u s + (c : EReal) := by
    intro n
    unfold NegativeDP.Stationary.T
    apply final
    have hpt : ∀ t, ENNReal.ofReal (-P.r (s, (π n).1 s, t)) + (-(u t + (c : EReal))).toENNReal +
        ENNReal.ofReal c = ENNReal.ofReal (-P.r (s, (π n).1 s, t)) + (-(u t)).toENNReal +
        ENNReal.ofReal (-c) := by
      intro t
      have hneg : -(u t + (c : EReal)) = -(u t) - (c : EReal) :=
        EReal.neg_add (Or.inr (EReal.coe_ne_top c)) (Or.inr (EReal.coe_ne_bot c))
      have ha : 0 ≤ -(u t) := EReal.neg_nonneg.mpr (hu.2 t)
      have hac : 0 ≤ -(u t) - (c : EReal) := by
        rw [← hneg]; exact EReal.neg_nonneg.mpr (huc.2 t)
      rw [hneg, add_assoc, add_assoc, pointwise _ c ha hac]
    have hprob : ∀ x, IsProbabilityMeasure (P.q x) := fun x => inferInstance
    rw [← mul_one (ENNReal.ofReal c), ← mul_one (ENNReal.ofReal (-c)),
      ← measure_univ (μ := P.q (s, (π n).1 s)), ← lintegral_const, ← lintegral_const,
      ← lintegral_add_right _ measurable_const, ← lintegral_add_right _ measurable_const]
    exact lintegral_congr hpt
  unfold U
  rw [iSup_add]
  exact iSup_congr hT
