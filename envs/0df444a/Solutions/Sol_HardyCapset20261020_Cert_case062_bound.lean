-- Prove2me | solution 1 for HardyCapset20261020.Cert.case062_bound
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-20T19:41:51.058809+00:00
-- url     : https://prove2.me/submissions/02eaf2b8-d7df-48b4-91c8-ffafbee44e2d

import Theorems.Thm_HardyCapset20261020_Cert_fast_baseline_lookup
import Definitions.Def_HardyCapsetCertificate06220261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
import Theorems.Thm_HardyCapset20261020_Cert_case062_blockers0
import Theorems.Thm_HardyCapset20261020_Cert_case062_blockers1
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
attribute [cbv_opaque] HardyCapset20261020.Cert.certificate062
open HardyCapset20261020 HardyCapset20261020.Cert
@[cbv_eval] private theorem evaluation_normal : certificate062.normal = (271 : Nat) := rfl
@[cbv_eval] private theorem evaluation_level : certificate062.level = (0 : Nat) := rfl
@[cbv_eval] private theorem evaluation_pool : certificate062.pool = (#[34, 59, 271, 277, 280, 289, 312, 321, 341, 350, 352, 384, 422, 431, 433, 465, 525, 534, 542, 545, 551, 560, 580, 589, 597, 623, 661, 670, 678, 704, 761, 763, 764, 767, 776, 839, 920, 1032, 1064, 1073, 1145, 1154, 1245, 1269, 1271, 1275, 1516, 1517, 1519, 1522, 1531, 1594, 1675, 1728, 1729, 1731, 1761, 1974, 2035, 2044, 2116, 2125, 2315, 2341, 2387, 2413, 2438, 2583, 2655, 2677, 2799, 2871, 3161, 3280, 3283, 3289, 3361, 3370, 3373, 3554, 3644, 4009, 4099, 4132, 4280, 4283, 4292, 4364, 4370, 4373, 4502, 4528, 4574, 4600, 4625, 4770, 4842, 4864, 4986, 5058, 5348, 5467, 5470, 5476, 5548, 5557, 5560, 5741, 5831, 6196, 6286, 6319, 6467, 6470, 6479, 6551, 6557, 6560] : Array Nat) := rfl
@[cbv_eval] private theorem evaluation_denominator : certificate062.denominator = (1 : Nat) := rfl
@[cbv_eval] private theorem evaluation_rows : certificate062.rows = (#[{ vars := #[1, 11], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 69⟩], triples := #[] }, { vars := #[3, 55], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 108⟩], triples := #[] }, { vars := #[31, 42], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 108⟩], triples := #[] }, { vars := #[31, 54], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 36⟩], triples := #[] }, { vars := #[45, 48], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 9⟩], triples := #[] }, { vars := #[47, 49], coeff := #[1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 147⟩], triples := #[] }, { vars := #[2, 4, 5], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[2, 10, 14], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[18, 20, 21], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[18, 25, 29], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[2, 32, 57, 0], coeff := #[1, 1, 1, 1], bound := 2, weight := 1, edges := #[⟨0, 3, 36⟩, ⟨2, 3, 108⟩], triples := #[⟨0, 1, 2⟩] }, { vars := #[2, 70, 92, 53], coeff := #[1, 1, 1, 1], bound := 2, weight := 1, edges := #[⟨0, 3, 108⟩, ⟨1, 3, 412⟩], triples := #[⟨0, 1, 2⟩] }, { vars := #[18, 65, 95, 43], coeff := #[1, 1, 1, 1], bound := 2, weight := 1, edges := #[⟨0, 3, 182⟩, ⟨2, 3, 307⟩], triples := #[⟨0, 1, 2⟩] }, { vars := #[6], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[7], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[8], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[9], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[12], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[13], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[15], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[16], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[17], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[19], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[22], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[23], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[24], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[26], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[27], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[28], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[30], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[33], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[34], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[35], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[36], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[37], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[38], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[39], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[40], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[41], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[44], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[46], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[50], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[51], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[52], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[56], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[58], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[59], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[60], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[61], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[62], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[63], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[64], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[66], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[67], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[68], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[69], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[71], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[72], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[73], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[74], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[75], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[76], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[77], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[78], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[79], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[80], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[81], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[82], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[83], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[84], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[85], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[86], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[87], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[88], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[89], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[90], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[91], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[93], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[94], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[96], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[97], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[98], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[99], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[100], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[101], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[102], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[103], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[104], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[105], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[106], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[107], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[108], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[109], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[110], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[111], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[112], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[113], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[114], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[115], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[116], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[117], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }] : Array Row) := rfl
@[cbv_eval] private theorem evaluation_coverRows : certificate062.coverRows = (#[#[10], #[0], #[6, 7, 10, 11], #[1], #[6], #[6], #[13], #[14], #[15], #[16], #[7], #[0], #[17], #[18], #[7], #[19], #[20], #[21], #[8, 9, 12], #[22], #[8], #[8], #[23], #[24], #[25], #[9], #[26], #[27], #[28], #[9], #[29], #[2, 3], #[10], #[30], #[31], #[32], #[33], #[34], #[35], #[36], #[37], #[38], #[2], #[12], #[39], #[4], #[40], #[5], #[4], #[5], #[41], #[42], #[43], #[11], #[3], #[1], #[44], #[10], #[45], #[46], #[47], #[48], #[49], #[50], #[51], #[12], #[52], #[53], #[54], #[55], #[11], #[56], #[57], #[58], #[59], #[60], #[61], #[62], #[63], #[64], #[65], #[66], #[67], #[68], #[69], #[70], #[71], #[72], #[73], #[74], #[75], #[76], #[11], #[77], #[78], #[12], #[79], #[80], #[81], #[82], #[83], #[84], #[85], #[86], #[87], #[88], #[89], #[90], #[91], #[92], #[93], #[94], #[95], #[96], #[97], #[98], #[99], #[100]] : Array (Array Nat)) := rfl

private theorem all_blocks : (List.range 6561).all
    (fun q => blockB certificate062 q certificate062.blockers[q]!) = true := by
  apply List.all_eq_true.mpr
  intro q hq
  have hq' : q < 6561 := List.mem_range.mp hq
  by_cases h : q < 3328
  · simpa only [Nat.zero_add] using case062_blockers0 ⟨q,h⟩
  · have hle : 3328 ≤ q := by omega
    simpa only [Nat.add_sub_of_le hle] using
      case062_blockers1 ⟨q-3328,by omega⟩
private theorem rows_check : certificate062.rows.toList.all (rowB certificate062) = true := by
  decide_cbv
private theorem covers_check : (List.range certificate062.pool.size).all (localCoverB certificate062) = true := by
  decide_cbv
private theorem cost_check : decide (cost certificate062 < certificate062.denominator * (deletedCount certificate062+1)) = true := by
  decide_cbv
theorem solution : CompletionBound (decode 271) (0 : ZMod 3) := by
  have hs : certificate062.blockers.size = 6561 := by
    simp only [certificate062, binaryBlockers, Array.size_ofFn]
  have hb : CompletionBound (decode certificate062.normal) certificate062.level := by
    apply boolean_check_completion_bound
    unfold verifyB
    rw [hs, all_blocks, rows_check, covers_check, cost_check]
    decide_cbv
  exact hb
#print axioms solution
