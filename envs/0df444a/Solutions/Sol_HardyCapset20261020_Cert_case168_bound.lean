-- Prove2me | solution 1 for HardyCapset20261020.Cert.case168_bound
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-20T22:50:53.216892+00:00
-- url     : https://prove2.me/submissions/715e233d-af8f-454e-9f35-efcf22dff41c

import Theorems.Thm_HardyCapset20261020_Cert_fast_baseline_lookup
import Definitions.Def_HardyCapsetCertificate16820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
import Theorems.Thm_HardyCapset20261020_Cert_case168_blockers0
import Theorems.Thm_HardyCapset20261020_Cert_case168_blockers1
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
attribute [cbv_opaque] HardyCapset20261020.Cert.certificate168
open HardyCapset20261020 HardyCapset20261020.Cert
@[cbv_eval] private theorem evaluation_normal : certificate168.normal = (2215 : Nat) := rfl
@[cbv_eval] private theorem evaluation_level : certificate168.level = (0 : Nat) := rfl
@[cbv_eval] private theorem evaluation_pool : certificate168.pool = (#[278, 281, 290, 304, 307, 316, 353, 379, 434, 460, 518, 524, 533, 544, 550, 559, 596, 622, 677, 703, 761, 764, 767, 776, 839, 920, 1001, 1068, 1077, 1149, 1158, 1244, 1308, 1317, 1389, 1398, 1516, 1519, 1522, 1531, 1594, 1675, 1756, 1797, 1806, 1878, 1887, 1999, 2037, 2046, 2118, 2127, 2201, 2204, 2210, 2213, 2215, 2273, 2276, 2314, 2343, 2346, 2354, 2357, 2386, 2415, 2418, 2438, 2583, 2655, 2678, 2826, 2898, 2921, 2924, 2927, 2936, 2999, 3069, 3080, 3141, 3161, 3280, 3283, 3289, 3361, 3370, 3373, 3404, 3523, 3526, 3535, 3607, 3613, 3616, 3798, 3870, 4009, 4099, 4255, 4345, 4387, 4390, 4396, 4399, 4430, 4459, 4462, 4503, 4506, 4529, 4540, 4543, 4575, 4578, 4601, 4624, 4743, 4815, 4864, 4986, 5058, 5229, 5301, 5495, 5585, 5741, 5831, 5836, 5839, 5842, 5851, 5914, 5958, 5995, 6030, 6076, 6224, 6227, 6233, 6305, 6314, 6317, 6319, 6467, 6470, 6479, 6551, 6557, 6560] : Array Nat) := rfl
@[cbv_eval] private theorem evaluation_denominator : certificate168.denominator = (1 : Nat) := rfl
@[cbv_eval] private theorem evaluation_rows : certificate168.rows = (#[{ vars := #[0, 70, 105], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[3, 56, 119], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[10, 67, 105], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[13, 56, 116], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[27, 56, 148], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[30, 56, 144], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[32, 56, 142], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[35, 56, 138], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[43, 93, 105], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[46, 89, 105], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[48, 87, 105], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[51, 83, 105], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[56, 59, 64], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[56, 82, 100], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[56, 86, 99], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[56, 90, 98], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[56, 94, 97], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[105, 110, 115], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[105, 124, 149], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[105, 125, 145], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[105, 126, 141], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[105, 127, 137], coeff := #[1, 1, 1], bound := 2, weight := 1, edges := #[], triples := #[⟨0, 1, 2⟩] }, { vars := #[1], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[2], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[4], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[5], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[6], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[7], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[8], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[9], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[11], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[12], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[14], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[15], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[16], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[17], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[18], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[19], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[20], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[21], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[22], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[23], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[24], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[25], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[26], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[28], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[29], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[31], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[33], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[34], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[36], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[37], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[38], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[39], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[40], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[41], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[42], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[44], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[45], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[47], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[49], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[50], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[52], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[53], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[54], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[55], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[57], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[58], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[60], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[61], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[62], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[63], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[65], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[66], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[68], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[69], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[71], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[72], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[73], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[74], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[75], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[76], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[77], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[78], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[79], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[80], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[81], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[84], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[85], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[88], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[91], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[92], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[95], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[96], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[101], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[102], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[103], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[104], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[106], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[107], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[108], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[109], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[111], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[112], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[113], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[114], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[117], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[118], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[120], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[121], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[122], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[123], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[128], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[129], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[130], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[131], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[132], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[133], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[134], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[135], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[136], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[139], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[140], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[143], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[146], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }, { vars := #[147], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }] : Array Row) := rfl
@[cbv_eval] private theorem evaluation_coverRows : certificate168.coverRows = (#[#[0], #[22], #[23], #[1], #[24], #[25], #[26], #[27], #[28], #[29], #[2], #[30], #[31], #[3], #[32], #[33], #[34], #[35], #[36], #[37], #[38], #[39], #[40], #[41], #[42], #[43], #[44], #[4], #[45], #[46], #[5], #[47], #[6], #[48], #[49], #[7], #[50], #[51], #[52], #[53], #[54], #[55], #[56], #[8], #[57], #[58], #[9], #[59], #[10], #[60], #[61], #[11], #[62], #[63], #[64], #[65], #[1, 3, 4, 5, 6, 7, 12, 13, 14, 15, 16], #[66], #[67], #[12], #[68], #[69], #[70], #[71], #[12], #[72], #[73], #[2], #[74], #[75], #[0], #[76], #[77], #[78], #[79], #[80], #[81], #[82], #[83], #[84], #[85], #[86], #[13], #[11], #[87], #[88], #[14], #[10], #[89], #[9], #[15], #[90], #[91], #[8], #[16], #[92], #[93], #[16], #[15], #[14], #[13], #[94], #[95], #[96], #[97], #[0, 2, 8, 9, 10, 11, 17, 18, 19, 20, 21], #[98], #[99], #[100], #[101], #[17], #[102], #[103], #[104], #[105], #[17], #[3], #[106], #[107], #[1], #[108], #[109], #[110], #[111], #[18], #[19], #[20], #[21], #[112], #[113], #[114], #[115], #[116], #[117], #[118], #[119], #[120], #[21], #[7], #[121], #[122], #[20], #[6], #[123], #[5], #[19], #[124], #[125], #[4], #[18]] : Array (Array Nat)) := rfl

private theorem all_blocks : (List.range 6561).all
    (fun q => blockB certificate168 q certificate168.blockers[q]!) = true := by
  apply List.all_eq_true.mpr
  intro q hq
  have hq' : q < 6561 := List.mem_range.mp hq
  by_cases h : q < 3328
  · simpa only [Nat.zero_add] using case168_blockers0 ⟨q,h⟩
  · have hle : 3328 ≤ q := by omega
    simpa only [Nat.add_sub_of_le hle] using
      case168_blockers1 ⟨q-3328,by omega⟩
private theorem rows_check : certificate168.rows.toList.all (rowB certificate168) = true := by
  decide_cbv
private theorem covers_check : (List.range certificate168.pool.size).all (localCoverB certificate168) = true := by
  decide_cbv
private theorem cost_check : decide (cost certificate168 < certificate168.denominator * (deletedCount certificate168+1)) = true := by
  decide_cbv
theorem solution : CompletionBound (decode 2215) (0 : ZMod 3) := by
  have hs : certificate168.blockers.size = 6561 := by
    simp only [certificate168, binaryBlockers, Array.size_ofFn]
  have hb : CompletionBound (decode certificate168.normal) certificate168.level := by
    apply boolean_check_completion_bound
    unfold verifyB
    rw [hs, all_blocks, rows_check, covers_check, cost_check]
    decide_cbv
  exact hb
#print axioms solution
