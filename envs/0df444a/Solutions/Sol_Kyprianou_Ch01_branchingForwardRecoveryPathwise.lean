-- Prove2me | solution 1 for Kyprianou.Ch01.branchingForwardRecoveryPathwise
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:20:47.855057+00:00
-- url     : https://prove2.me/submissions/93e30d53-f821-4192-899d-e6642099c8ff

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.WithBot
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open Kyprianou.Ch01 MeasureTheory
set_option autoImplicit false

namespace BFRAux
open scoped NNReal

theorem exists_between_top (t : ℝ≥0) (h : WithTop ℝ≥0) (ht : (t : WithTop ℝ≥0) < h) :
    ∃ m : ℝ≥0, t < m ∧ (m : WithTop ℝ≥0) < h := by
  induction h using WithTop.recTopCoe with
  | top => exact ⟨t + 1, by simp, WithTop.coe_lt_top _⟩
  | coe e =>
    have := WithTop.coe_lt_coe.mp ht
    obtain ⟨m, h1, h2⟩ := exists_between this
    exact ⟨m, h1, WithTop.coe_lt_coe.mpr h2⟩

theorem sInf_eq (J : ℝ≥0 → ℝ) (hmono : Monotone J) (t : ℝ≥0) (h : WithTop ℝ≥0)
    (ht : (t : WithTop ℝ≥0) < h)
    (hstrict : ∀ s : ℝ≥0, t < s → (s : WithTop ℝ≥0) < h → J t < J s) :
    sInf {s : ℝ≥0 | J t < J s} = t ∧ ∃ s, J t < J s := by
  obtain ⟨m, hm1, hm2⟩ := exists_between_top t h ht
  refine ⟨?_, ⟨m, hstrict m hm1 hm2⟩⟩
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro a ha
    by_cases hah : (a : WithTop ℝ≥0) < h
    · exact csInf_le (OrderBot.bddBelow {s : ℝ≥0 | J t < J s})
        (show a ∈ {s : ℝ≥0 | J t < J s} from hstrict a ha hah)
    · have hma : m ≤ a := by
        by_contra hc
        have : a < m := not_le.mp hc
        exact hah (lt_trans (WithTop.coe_lt_coe.mpr this) hm2)
      exact le_trans (csInf_le (OrderBot.bddBelow {s : ℝ≥0 | J t < J s})
        (show m ∈ {s : ℝ≥0 | J t < J s} from hstrict m hm1 hm2)) hma
  · apply le_csInf ⟨m, hstrict m hm1 hm2⟩
    intro s hs
    by_contra hlt0
    have hlt := not_le.mp hlt0
    exact absurd (hmono hlt.le) (not_le.mpr hs)

end BFRAux

theorem solution
    {Ω : Type*} (Y : NNReal → Ω → ℕ) (ω : Ω)
    (hlocalint : ∀ t : NNReal,
      IntervalIntegrable (fun s : ℝ => (Y (Real.toNNReal s) ω : ℝ))
        volume 0 (t : ℝ))
    (hpositive : ∀ t : NNReal,
      (t : WithTop NNReal) < populationExtinction Y ω → 0 < Y t ω) :
    ∀ t : NNReal, (t : WithTop NNReal) < populationExtinction Y ω →
      branchingToPoisson Y
        (Real.toNNReal (branchingOccupation Y t ω)) ω = Y t ω := by
  intro t ht
  set f : ℝ → ℝ := fun s => (Y (Real.toNNReal s) ω : ℝ) with hf
  set J : NNReal → ℝ := fun s => branchingOccupation Y s ω with hJ
  have hII : ∀ a b : NNReal, IntervalIntegrable f volume (a : ℝ) (b : ℝ) :=
    fun a b => (hlocalint a).symm.trans (hlocalint b)
  have hdiff : ∀ a b : NNReal, J b - J a = ∫ s in (a : ℝ)..(b : ℝ), f s := by
    intro a b
    simp only [hJ, branchingOccupation]
    rw [sub_eq_iff_eq_add', intervalIntegral.integral_add_adjacent_intervals (hlocalint a) (hII a b)]
  have hmono : Monotone J := by
    intro a b hab
    have := hdiff a b
    have h0 : 0 ≤ ∫ s in (a : ℝ)..(b : ℝ), f s :=
      intervalIntegral.integral_nonneg (by exact_mod_cast hab) (fun s _ => by simp [hf])
    linarith
  have hnonneg : 0 ≤ J t := by
    have := hmono (show (0:NNReal) ≤ t from t.2)
    have h0 : J 0 = 0 := by simp [hJ, branchingOccupation]
    linarith
  have hstrict : ∀ s : NNReal, t < s → (s : WithTop NNReal) < populationExtinction Y ω →
      J t < J s := by
    intro s hts hs
    have hpos : 0 < ∫ u in (t : ℝ)..(s : ℝ), f u := by
      apply intervalIntegral.intervalIntegral_pos_of_pos_on (hII t s)
      · intro u hu
        have hu0 : 0 ≤ u := le_trans t.2 hu.1.le
        have hus : Real.toNNReal u ≤ s := by
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu0]; exact hu.2.le
        have := hpositive (Real.toNNReal u) (lt_of_le_of_lt (WithTop.coe_le_coe.mpr hus) hs)
        simp only [hf]; exact_mod_cast this
      · exact_mod_cast hts
    have := hdiff t s
    linarith
  obtain ⟨hinf, hex⟩ := BFRAux.sInf_eq J hmono t _ ht hstrict
  have hc : ((Real.toNNReal (branchingOccupation Y t ω) : NNReal) : ℝ) = branchingOccupation Y t ω :=
    Real.coe_toNNReal _ hnonneg
  have hS : {s : NNReal | ((Real.toNNReal (branchingOccupation Y t ω) : NNReal) : ℝ) <
      branchingOccupation Y s ω} = {s : NNReal | J t < J s} := by
    ext s; simp only [Set.mem_ofPred_eq, hc, hJ]
  have hex' : ∃ s : NNReal, ((Real.toNNReal (branchingOccupation Y t ω) : NNReal) : ℝ) <
      branchingOccupation Y s ω := by
    obtain ⟨s, hs⟩ := hex; exact ⟨s, by rw [hc]; exact hs⟩
  have hinv : inverseBranchingOccupation Y (Real.toNNReal (branchingOccupation Y t ω)) ω =
      ((t : NNReal) : WithTop NNReal) := by
    unfold inverseBranchingOccupation
    simp only [hex', if_true]
    rw [hS, hinf]
  unfold branchingToPoisson
  rw [hinv]
