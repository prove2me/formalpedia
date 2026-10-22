-- Prove2me | solution 1 for HardyCapset20261020.Cert.case028_finite4_129
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-21T05:59:30.525474+00:00
-- url     : https://prove2.me/submissions/683d14c6-7b7e-4011-bd72-7c9853bc6edd

import Definitions.Def_HardyCapsetEvaluationData028V420261021
import Theorems.Thm_HardyCapset20261020_Cert_fast_baseline_lookup
import Definitions.Def_HardyCapsetCertificate02820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
import Theorems.Thm_HardyCapset20261020_Cert_boolean_check_completion_bound
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option autoImplicit false
namespace HardyCapset20261020.Cert
private theorem range_list_sum (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

@[cbv_eval] theorem dotCode_list (n q : ℕ) :
    dotCode n q = (((List.range 8).map (fun i => digit n i * digit q i)).sum % 3) := by
  unfold dotCode natDot
  rw [range_list_sum, ← Fin.sum_univ_eq_sum_range]

@[cbv_eval] theorem coefficient_list (r : Row) (j : ℕ) :
    coefficient r j = ((List.range r.vars.size).map
      (fun k => if entry r.vars k = j then entry r.coeff k else 0)).sum := by
  unfold coefficient
  rw [range_list_sum, ← Fin.sum_univ_eq_sum_range]

@[cbv_eval] theorem cost_list (c : Certificate) :
    cost c = ((List.range c.rows.size).map
      (fun k => c.rows[k]!.weight * c.rows[k]!.bound)).sum := by
  unfold cost
  rw [range_list_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  simp [k.isLt]
end HardyCapset20261020.Cert
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
-- Keep arithmetic operations intact until their arguments are values. The
-- built-in literal evaluators then return kernel-checked equality proofs.
attribute [cbv_opaque] Nat.add Nat.mul Nat.sub Nat.ble
namespace HardyCapset20261020.Cert
@[cbv_eval] theorem decide_le_nat (a b : Nat) : decide (a ≤ b) = a.ble b := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Nat.ble_eq]
@[cbv_eval] theorem decide_lt_nat (a b : Nat) : decide (a < b) = a.succ.ble b := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Nat.ble_eq, Nat.succ_le_iff]
end HardyCapset20261020.Cert
namespace HardyCapset20261020.Cert
private theorem evaluation_base_size : baseArray.size = 512 := by decide_cbv
attribute [cbv_eval] fast_baseline_lookup evaluation_base_size
attribute [cbv_opaque] baseArray
end HardyCapset20261020.Cert
attribute [cbv_opaque] HardyCapset20261020.Cert.certificate028
open HardyCapset20261020 HardyCapset20261020.Cert
@[cbv_eval] private theorem evaluation_normal : certificate028.normal = (evaluationDataV4028_normal : Nat) := rfl
@[cbv_eval] private theorem evaluation_level : certificate028.level = (evaluationDataV4028_level : Nat) := rfl
@[cbv_eval] private theorem evaluation_pool : certificate028.pool = (evaluationDataV4028_pool : Array Nat) := rfl
@[cbv_eval] private theorem evaluation_denominator : certificate028.denominator = (evaluationDataV4028_denominator : Nat) := rfl
@[cbv_eval] private theorem evaluation_rows : certificate028.rows = (evaluationDataV4028_rows : Array Row) := rfl
@[cbv_eval] private theorem evaluation_coverRows : certificate028.coverRows = (evaluationDataV4028_coverRows : Array (Array Nat)) := rfl


set_option autoImplicit false
namespace HardyCapset20261020.Cert
attribute [-cbv_eval] cost_list
@[cbv_eval] theorem cost_fold (c : Certificate) :
    cost c = (c.rows.toList.map (fun r => r.weight * r.bound)).sum := by
  have h (a : Array Row) : (List.range a.size).map (fun i => a[i]!) = a.toList := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      have hi : i < a.size := by simpa using h₂
      simp only [List.getElem_map, List.getElem_range]
      simpa only [Array.getElem_toList] using getElem!_pos a i hi
  rw [cost_list, ← h c.rows, List.map_map]
  rfl
end HardyCapset20261020.Cert

private theorem cycle_edge_bound (a b : Bool) (h : (!(a && b)) = true) :
    (if a then 1 else 0) + (if b then 1 else 0) ≤ 1 := by
  cases a <;> cases b <;> simp_all

private theorem row516_capacity (xs : List Bool) (h : legalB er028_516 xs = true) :
    selectedCost er028_516 xs ≤ er028_516.bound := by
  have he := (Bool.and_eq_true_iff.mp h).1

  have e0 : (!(readBit xs 0 && readBit xs 1)) = true :=
    List.all_eq_true.mp he (⟨0, 1, 413⟩ : Edge) (by decide)
  have b0 := cycle_edge_bound _ _ e0

  have e1 : (!(readBit xs 1 && readBit xs 2)) = true :=
    List.all_eq_true.mp he (⟨1, 2, 253⟩ : Edge) (by decide)
  have b1 := cycle_edge_bound _ _ e1

  have e2 : (!(readBit xs 2 && readBit xs 3)) = true :=
    List.all_eq_true.mp he (⟨2, 3, 375⟩ : Edge) (by decide)
  have b2 := cycle_edge_bound _ _ e2

  have e3 : (!(readBit xs 3 && readBit xs 4)) = true :=
    List.all_eq_true.mp he (⟨3, 4, 107⟩ : Edge) (by decide)
  have b3 := cycle_edge_bound _ _ e3

  have e4 : (!(readBit xs 4 && readBit xs 5)) = true :=
    List.all_eq_true.mp he (⟨4, 5, 230⟩ : Edge) (by decide)
  have b4 := cycle_edge_bound _ _ e4

  have e5 : (!(readBit xs 5 && readBit xs 6)) = true :=
    List.all_eq_true.mp he (⟨5, 6, 326⟩ : Edge) (by decide)
  have b5 := cycle_edge_bound _ _ e5

  have e6 : (!(readBit xs 6 && readBit xs 7)) = true :=
    List.all_eq_true.mp he (⟨6, 7, 230⟩ : Edge) (by decide)
  have b6 := cycle_edge_bound _ _ e6

  have e7 : (!(readBit xs 7 && readBit xs 8)) = true :=
    List.all_eq_true.mp he (⟨7, 8, 223⟩ : Edge) (by decide)
  have b7 := cycle_edge_bound _ _ e7

  have e8 : (!(readBit xs 8 && readBit xs 9)) = true :=
    List.all_eq_true.mp he (⟨8, 9, 348⟩ : Edge) (by decide)
  have b8 := cycle_edge_bound _ _ e8

  have e9 : (!(readBit xs 9 && readBit xs 10)) = true :=
    List.all_eq_true.mp he (⟨9, 10, 223⟩ : Edge) (by decide)
  have b9 := cycle_edge_bound _ _ e9

  have e10 : (!(readBit xs 10 && readBit xs 0)) = true :=
    List.all_eq_true.mp he (⟨10, 0, 227⟩ : Edge) (by decide)
  have b10 := cycle_edge_bound _ _ e10

  change ((if readBit xs 0 then 1 else 0) + ((if readBit xs 1 then 1 else 0) + ((if readBit xs 2 then 1 else 0) + ((if readBit xs 3 then 1 else 0) + ((if readBit xs 4 then 1 else 0) + ((if readBit xs 5 then 1 else 0) + ((if readBit xs 6 then 1 else 0) + ((if readBit xs 7 then 1 else 0) + ((if readBit xs 8 then 1 else 0) + ((if readBit xs 9 then 1 else 0) + ((if readBit xs 10 then 1 else 0) + 0))))))))))) ≤ 5
  omega

private theorem row516_pattern : patternB er028_516 = true := by
  apply List.all_eq_true.mpr
  intro xs _
  by_cases h : legalB er028_516 xs = true
  · have hb := row516_capacity xs h
    simp [h, hb]
  · have hh : legalB er028_516 xs = false := Bool.eq_false_iff.mpr h
    simp [hh]

private theorem row516_checked : rowB certificate028 certificate028.rows[516]! = true := by
  change rowB certificate028 er028_516 = true
  unfold rowB
  rw [row516_pattern]
  decide_cbv

private theorem interval_checked :
    (List.range 4).all (fun k => ((if 516+k < certificate028.rows.size then rowB certificate028 certificate028.rows[516+k]! else true) &&
    (if 516+k < certificate028.pool.size then localCoverB certificate028 (516+k) else true))) = true := by
  change ((rowB certificate028 certificate028.rows[516]! && localCoverB certificate028 516) && ((rowB certificate028 certificate028.rows[517]! && localCoverB certificate028 517) && ((rowB certificate028 certificate028.rows[518]! && localCoverB certificate028 518) && ((rowB certificate028 certificate028.rows[519]! && localCoverB certificate028 519) && true)))) = true
  rw [row516_checked]
  decide_cbv
theorem solution (j : Fin 4) :
    ((if 516+j.val < certificate028.rows.size then rowB certificate028 certificate028.rows[516+j.val]! else true) &&
    (if 516+j.val < certificate028.pool.size then localCoverB certificate028 (516+j.val) else true)) = true := by
  exact List.all_eq_true.mp interval_checked j.val (List.mem_range.mpr j.isLt)
#print axioms solution
