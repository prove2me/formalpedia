-- Prove2me | solution 1 for LasserreFC.FinConv.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T12:25:47.625584+00:00
-- url     : https://prove2.me/submissions/0f6fe766-4175-4ef5-a4b7-a1e89a8dc1b7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LasserreFC_FinConv_Setting
import Definitions.Def_LasserreFC_FinConv_Hierarchy
import Theorems.Thm_LasserreFC_FinConv_theorem_3_1
import Theorems.Thm_LasserreFC_FinConv_theorem_2_4
import Theorems.Thm_LasserreFC_FinConv_epsilon_feasible
import Theorems.Thm_LasserreFC_FinConv_value_le_fmin_monotone

open MvPolynomial LasserreFC.FinConv

theorem solution {n m1 m2 : ℕ} (P : POP n m1 m2) (harch : IsArchimedean P)
    (fmin : ℝ) (hfmin : IsLeast ((fun x => eval x P.f) '' P.K) fmin)
    (hopt : ∀ u ∈ P.K, IsMinOn (fun x => eval x P.f) P.K u → OptCond P u) :
    ∃ k : ℕ, lasserreValue P k = (fmin : EReal) := by
  -- Theorem 3.1: the optimality conditions imply BHC at every global minimizer
  have hbhc : ∀ u ∈ P.K, IsMinOn (fun x => eval x P.f) P.K u → IsBHC P u :=
    fun u hu hmin => theorem_3_1 P u hu hmin.localize (hopt u hu hmin)
  -- Theorem 2.4 (Marshall): f - fmin ∈ I(V) + Q(g)
  have hrep := theorem_2_4 P harch fmin hfmin hbhc
  -- uniform order k0 at which fmin - ε is feasible for every ε > 0
  obtain ⟨k0, hk0⟩ := epsilon_feasible P fmin hrep
  refine ⟨k0, le_antisymm ((value_le_fmin_monotone P fmin hfmin).1 k0) ?_⟩
  refine le_of_forall_lt fun c hc => ?_
  obtain ⟨x, hcx, hxf⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  have hxf' : x < fmin := by exact_mod_cast hxf
  have hmem : P.f - C (fmin - (fmin - x)) ∈ trunc P k0 := hk0 (fmin - x) (by linarith)
  have hle : ((fmin - (fmin - x) : ℝ) : EReal) ≤ lasserreValue P k0 :=
    le_sSup ⟨_, hmem, rfl⟩
  have : fmin - (fmin - x) = x := by ring
  rw [this] at hle
  exact lt_of_lt_of_le hcx hle
