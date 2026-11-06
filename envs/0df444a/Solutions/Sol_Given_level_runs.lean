-- Prove2me | solution 1 for Given.level_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:27:45.266644+00:00
-- url     : https://prove2.me/submissions/ccce400c-593f-48fe-8dc6-ef797097dfc3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Given_Networks
import Definitions.Def_Printed_End
import Mathlib.Tactic
import Definitions.Def_Given_Level
import Theorems.Thm_Given_level_one
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_key
import Theorems.Thm_Eight_Level_eqExpansion_words
import Theorems.Thm_Given_stGridGiven
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Prog_abs_value_le
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_bind_runs
import Theorems.Thm_Groundwork_Stepped_natAbs_sum_le
import Theorems.Thm_Groundwork_Stepped_ofFun_runs
import Theorems.Thm_Groundwork_Stepped_sumRange_runs
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_st4_cnt
import Theorems.Thm_Groundwork_TM_st4_src
import Theorems.Thm_Groundwork_TM_st4_t1
import Theorems.Thm_Groundwork_TM_st4_t2
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
import Theorems.Thm_Groundwork_TM_update_withIO
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
import Theorems.Thm_P2M_Eight_Level_netOf__sized_t_6d348568ee7d
import Theorems.Thm_P2M_Eight_Level_value_netOf__39744228d791
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Printed_AchievedBy_mono
import Theorems.Thm_Printed_level_size_printed
import Theorems.Thm_Printed_level_time_printed
import Theorems.Thm_Printed_size_units
import Theorems.Thm_Printed_stAskServes
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
import Theorems.Thm_QueryMachines_QueryMachine_close_bind
import Theorems.Thm_QueryMachines_QueryMachine_close_both
import Theorems.Thm_QueryMachines_QueryMachine_close_branch
import Theorems.Thm_QueryMachines_QueryMachine_close_const
import Theorems.Thm_QueryMachines_QueryMachine_close_foldRange
import Theorems.Thm_QueryMachines_QueryMachine_close_foldWhile
import Theorems.Thm_QueryMachines_QueryMachine_close_gated
import Theorems.Thm_QueryMachines_QueryMachine_close_ite
import Theorems.Thm_QueryMachines_QueryMachine_close_lift
import Theorems.Thm_QueryMachines_QueryMachine_close_mapAsk
import Theorems.Thm_QueryMachines_QueryMachine_close_mapIn
import Theorems.Thm_QueryMachines_QueryMachine_close_mapOut
import Theorems.Thm_QueryMachines_QueryMachine_close_optBind
import Theorems.Thm_QueryMachines_QueryMachine_close_prodRange
import Theorems.Thm_QueryMachines_QueryMachine_close_query
import Theorems.Thm_QueryMachines_QueryMachine_close_subst
import Theorems.Thm_QueryMachines_QueryMachine_close_sumRange
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.Host.upd_none
attribute [local simp] Groundwork.Host.withIO_none
attribute [local simp] Groundwork.Host.withIO_some
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.TM.st4_cnt
attribute [local simp] Groundwork.TM.st4_src
attribute [local simp] Groundwork.TM.st4_t1
attribute [local simp] Groundwork.TM.st4_t2
attribute [local simp] Groundwork.TM.st_a
attribute [local simp] Groundwork.TM.st_b
attribute [local simp] Groundwork.TM.st_cnt
attribute [local simp] Groundwork.TM.st_main
attribute [local simp] Groundwork.TM.upd4_cnt
attribute [local simp] Groundwork.TM.upd4_src
attribute [local simp] Groundwork.TM.upd4_t1
attribute [local simp] Groundwork.TM.upd4_t2
attribute [local simp] Groundwork.TM.upd_a
attribute [local simp] Groundwork.TM.upd_b
attribute [local simp] Groundwork.TM.upd_main
attribute [local simp] Groundwork.TM.update_withIO
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit
attribute [local simp] QueryMachines.QueryMachine.close_bind
attribute [local simp] QueryMachines.QueryMachine.close_both
attribute [local simp] QueryMachines.QueryMachine.close_branch
attribute [local simp] QueryMachines.QueryMachine.close_const
attribute [local simp] QueryMachines.QueryMachine.close_foldRange
attribute [local simp] QueryMachines.QueryMachine.close_foldWhile
attribute [local simp] QueryMachines.QueryMachine.close_gated
attribute [local simp] QueryMachines.QueryMachine.close_ite
attribute [local simp] QueryMachines.QueryMachine.close_lift
attribute [local simp] QueryMachines.QueryMachine.close_mapAsk
attribute [local simp] QueryMachines.QueryMachine.close_mapIn
attribute [local simp] QueryMachines.QueryMachine.close_mapOut
attribute [local simp] QueryMachines.QueryMachine.close_optBind
attribute [local simp] QueryMachines.QueryMachine.close_prodRange
attribute [local simp] QueryMachines.QueryMachine.close_query
attribute [local simp] QueryMachines.QueryMachine.close_subst
attribute [local simp] QueryMachines.QueryMachine.close_sumRange



set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine Printed
namespace Given
theorem _root_.solution {K g C₁ : ℕ} {e : ℝ} {NM : NetMachine} (hK : 2 ≤ K) (hg : K ≤ g) (h0 : 0 ≤ e) (hNM : ComputesNetworks NM C₁ g K e) :
    ∃ Cc' : ℕ, ∀ (c : List Unit × List Unit) (lam B : ℕ) (W : ℕ → List Bool → ℤ), c.1.length = lam → c.2.length = B → 1 ≤ lam → (∀ w < g * g, ∀ z ∈ words ((g * g - 1) * lam), |W w z| < 2 ^ B) →
      ∃ T : ℕ, (Stepped.bind (Stepped.sumRange (numPat8 g fun c : List Unit × List Unit => c.1.length)
            (Stepped.ite (useRowP g fun c : List Unit × List Unit => c.1.length) (networkOnSteps g NM ((gridProcs g false).close (tables (g * g) lam W))) (networkOnSteps g NM ((gridProcs g true).close (tables (g * g) lam W)))))
          (Stepped.ofFun fun p : (List Unit × List Unit) × ℤ => p.2 / ((2 ^ (tOf p.1.1.length * nRect g) : ℕ) : ℤ))).Runs c T (Cc' * (B + lam) ^ Cc') (Inst.ZW lam [] (listTables (g * g) W)) ∧
        (T : ℝ) ≤ Cc' * (2 : ℝ) ^ (((rho + 2 / K) * e + 2 / K) * (((g * g : ℕ) : ℝ)) ^ 2 * lam) * ((B : ℝ) + lam) ^ Cc' := by
  have hg1 : 1 ≤ g := by omega
  obtain ⟨a, ha⟩ := stGridGiven g hg1
  obtain ⟨A1, hA1⟩ := level_time_printed g K a C₁ hK hg h0 (nRect g)
  obtain ⟨A2, hA2⟩ := level_size_printed g a C₁ (nRect g)
  refine ⟨A1 + A2, fun c n B W hcl hcB hl hW => ?_⟩
  have hBd : BoundedInst n B (listTables (g * g) W) := fun v θ h1 h2 => (stAskServes (List Unit × List Unit) (g * g) n B W c hW v θ h1 h2).2
  have hnet := fun (y : ℕ) (hy : y < (tOf n + 1) ^ nRect g) (tr : Bool) => ha tr c n B W y hcl hcB hl hW hy
  obtain ⟨Rm, hRm⟩ : ∃ Rm : Inst (Fin (g * g)) (List Bool), Rm = listTables (g * g) W := ⟨_, rfl⟩
  obtain ⟨O, hOd⟩ : ∃ O, O = tables (g * g) n W := ⟨_, rfl⟩
  rw [← hRm, ← hOd]
  rw [← hRm] at hBd
  simp only [← hRm, ← hOd] at hnet
  obtain ⟨M, hM⟩ : ∃ M, M = (tOf n + 1) * nRect g := ⟨_, rfl⟩
  obtain ⟨S', hS'⟩ : ∃ S', S' = size c + size (g * g) + g * g * (2 * n + 2) + B + 3 + a * (size c + B + n) ^ a + 2 := ⟨_, rfl⟩
  obtain ⟨Zt, hZt⟩ : ∃ Zt : ℕ → ℤ, Zt = fun y => Eight.Zι (gridR0 g g n Rm) (Level.patOf g n y) := ⟨_, rfl⟩
  obtain ⟨bd, hbd⟩ : ∃ bd : ℝ, bd = (((3 * C₁ : ℕ) : ℝ) + 1) * (2 : ℝ) ^ (e * (rho * ((g : ℝ) ^ 4 * n) + (g : ℝ) ^ 3 * n + 2 * (g : ℝ) ^ 4) + (e + 2) * ((g : ℝ) * ((g ^ 3 * n : ℕ) : ℝ)) / K)
        * (((g ^ 3 * n : ℕ) : ℝ) + ((g * B + g ^ 2 * n + 1 : ℕ) : ℝ)) ^ C₁ * ((a * (B + n) ^ a : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hS'] at hnet
  have htn : tOf n ≤ n := by unfold tOf; omega
  have hNp : (tOf n + 1) ^ nRect g ≤ 2 ^ M := by
    rw [hM, pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
  -- one ι
  have key : ∀ y : ℕ, ∃ τ : ℕ, y < (tOf n + 1) ^ nRect g →
      (Stepped.ite (useRowP g fun c : List Unit × List Unit => c.1.length) (networkOnSteps g NM ((gridProcs g false).close O)) (networkOnSteps g NM ((gridProcs g true).close O))).Runs (c, y) τ
        (size c + (M + 1) + C₁ * (g ^ 3 * n + (g * B + g ^ 2 * n + 1)) ^ C₁ + S' + 5) (Zt y) ∧ (τ : ℝ) + 1 ≤ bd := by
    intro y
    by_cases hy : y < (tOf n + 1) ^ nRect g
    swap
    · exact ⟨0, fun h => absurd h hy⟩
    obtain ⟨τ, hτ1, hτ2⟩ := level_one h0 hg1 hNM hcl hl (hnet y hy)
    have hsz : size (c, y) ≤ size c + (M + 1) := by
      have := Nat.size_le.2 (hy.trans_le hNp)
      simp only [size_prod, size_nat]
      omega
    refine ⟨τ, fun _ => ⟨?_, ?_⟩⟩
    · rw [hZt]
      exact hτ1.mono le_rfl (by omega)
    · rw [hbd]
      exact hτ2
  choose τ hτ using key
  -- the loop
  obtain ⟨v, hv⟩ : ∃ v, v = g * (g ^ 3 * n + (g * B + g ^ 2 * tOf n)) + g * g * (g * B + g ^ 2 * tOf n) := ⟨_, rfl⟩
  have hN : numPat8 g (fun c : List Unit × List Unit => c.1.length) c = (tOf n + 1) ^ nRect g := by
    show (tOf c.1.length + 1) ^ nRect g = _
    rw [hcl]
  have habs : ∀ y < (tOf n + 1) ^ nRect g, (Zt y).natAbs ≤ 2 ^ v := fun y hy => by
    have h0 : Network.value (J := Fin g) (netOfι g false n y Rm) = Zt y := by rw [hZt]; exact value_netOfι hl g false y Rm
    have h1 := Groundwork.Prog.abs_value_le (J := Fin g) (netOfι g false n y Rm) (netOfι_sized_t hl g false y hBd)
    rw [h0, Int.abs_eq_natAbs, Fintype.card_fin, ← hv] at h1
    exact_mod_cast h1
  have hrun := Stepped.sumRange_runs (N := numPat8 g fun c : List Unit × List Unit => c.1.length) (a := c)
    (M := Stepped.ite (useRowP g fun c : List Unit × List Unit => c.1.length) (networkOnSteps g NM ((gridProcs g false).close O)) (networkOnSteps g NM ((gridProcs g true).close O)))
    τ Zt (2 ^ v) (size c + (M + 1) + C₁ * (g ^ 3 * n + (g * B + g ^ 2 * n + 1)) ^ C₁ + S' + 5)
    (fun y hy => (hτ y (hN ▸ hy)).1) (fun y hy => habs y (hN ▸ hy))
  rw [hN] at hrun
  -- the division
  have hZ : ((2 : ℤ) ^ tOf n) ^ nRect g * Inst.ZW n [] Rm = ∑ y ∈ range ((tOf n + 1) ^ nRect g), Zt y := by
    rw [hZt, ← pow_mul]
    exact eqExpansion_words hl Rm
  have hdiv : (∑ y ∈ range ((tOf n + 1) ^ nRect g), Zt y) / ((2 ^ (tOf c.1.length * nRect g) : ℕ) : ℤ) = Inst.ZW n [] Rm := by
    rw [← hZ, hcl, ← pow_mul]
    push_cast
    exact Int.mul_ediv_cancel_left _ (by positivity)
  have hfin := Stepped.ofFun_runs (fun p : (List Unit × List Unit) × ℤ => p.2 / ((2 ^ (tOf p.1.1.length * nRect g) : ℕ) : ℤ)) (c, ∑ y ∈ range ((tOf n + 1) ^ nRect g), Zt y)
  simp only [hdiv] at hfin
  have hall := Stepped.bind_runs hrun hfin
  refine ⟨_, hall.mono le_rfl ?_, ?_⟩
  · -- sizes
    have hsc : size c = 2 * n + 1 + (2 * B + 1) := by rw [size_prod, size_units, size_units, hcl, hcB]
    have h2 := hA2 (size c) B n M hl hg1
      (by
        rw [hM]
        calc (tOf n + 1) * nRect g ≤ 2 * n * nRect g := Nat.mul_le_mul_right _ (by omega)
          _ = 2 * nRect g * n := by ring)
      (by omega)
    have h3 : A2 * (B + n) ^ A2 ≤ (A1 + A2) * (B + n) ^ (A1 + A2) :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
    have hB' : g * B + g ^ 2 * tOf n ≤ g * B + g ^ 2 * n + 1 := by
      have := Nat.mul_le_mul_left (g ^ 2) htn
      omega
    have hv' : v ≤ g * (g ^ 3 * n + (g * B + g ^ 2 * n + 1)) + g * g * (g * B + g ^ 2 * n + 1) := by
      rw [hv]
      exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.add_le_add_left hB' _)) (Nat.mul_le_mul_left _ hB')
    have s1 : size ((tOf n + 1) ^ nRect g) ≤ M + 2 := by
      rw [size_nat]
      have := Nat.size_le_size hNp
      rw [Nat.size_pow] at this
      omega
    have hNV : (tOf n + 1) ^ nRect g * 2 ^ v ≤ 2 ^ (M + v) := by
      rw [pow_add]
      exact Nat.mul_le_mul_right _ hNp
    have s2 : size ((tOf n + 1) ^ nRect g * 2 ^ v) ≤ M + v + 2 := by
      rw [size_nat]
      have := Nat.size_le_size hNV
      rw [Nat.size_pow] at this
      omega
    have hSum : (∑ y ∈ range ((tOf n + 1) ^ nRect g), Zt y).natAbs ≤ 2 ^ (M + v) := by
      refine (Int.natAbs_sum_le _ _).trans (le_trans ?_ hNV)
      calc ∑ y ∈ range ((tOf n + 1) ^ nRect g), (Zt y).natAbs ≤ ∑ _y ∈ range ((tOf n + 1) ^ nRect g), 2 ^ v :=
            Finset.sum_le_sum fun y hy => habs y (Finset.mem_range.1 hy)
        _ = (tOf n + 1) ^ nRect g * 2 ^ v := by rw [Finset.sum_const, card_range, smul_eq_mul]
    have s3 : size (∑ y ∈ range ((tOf n + 1) ^ nRect g), Zt y) ≤ M + v + 2 := by
      rw [size_int]
      have := Nat.size_le_size hSum
      rw [Nat.size_pow] at this
      omega
    have hZle : (Inst.ZW n [] Rm).natAbs ≤ 2 ^ (M + v) := by
      refine le_trans ?_ hSum
      rw [← hZ, Int.natAbs_mul]
      exact Nat.le_mul_of_pos_left _ (Int.natAbs_pos.2 (by positivity))
    have s4 : size (Inst.ZW n [] Rm) ≤ M + v + 2 := by
      rw [size_int]
      have := Nat.size_le_size hZle
      rw [Nat.size_pow] at this
      omega
    have e5 : size (c, ∑ y ∈ range ((tOf n + 1) ^ nRect g), Zt y) = size c + size (∑ y ∈ range ((tOf n + 1) ^ nRect g), Zt y) := rfl
    rw [e5]
    omega
  · -- steps
    have hsum : ((∑ y ∈ range ((tOf n + 1) ^ nRect g), (τ y + 1) : ℕ) : ℝ) ≤ (((tOf n + 1) ^ nRect g : ℕ) : ℝ) * bd := by
      rw [Nat.cast_sum]
      calc _ ≤ ∑ _y ∈ range ((tOf n + 1) ^ nRect g), bd :=
            Finset.sum_le_sum fun y hy => by
              have := (hτ y (Finset.mem_range.1 hy)).2
              push_cast
              exact this
        _ = _ := by rw [Finset.sum_const, card_range, nsmul_eq_mul]
    have h4 := hA1 B n hl
    rw [← hbd] at h4
    have h5 : ((∑ y ∈ range ((tOf n + 1) ^ nRect g), (τ y + 1) + 1 + 1 : ℕ) : ℝ) =
        ((∑ y ∈ range ((tOf n + 1) ^ nRect g), (τ y + 1) : ℕ) : ℝ) + 2 := by push_cast; ring
    rw [h5]
    refine le_trans (by linarith) (h4.trans ?_)
    have hBl : (1 : ℝ) ≤ (B : ℝ) + n := by
      have h5 : (1 : ℝ) ≤ n := by exact_mod_cast hl
      have h6 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg _
      linarith
    gcongr
    · exact_mod_cast Nat.le_add_right A1 A2
    · exact Nat.le_add_right A1 A2
end Given
