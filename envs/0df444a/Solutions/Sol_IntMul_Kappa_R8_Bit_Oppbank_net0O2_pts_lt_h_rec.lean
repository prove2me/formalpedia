-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_pts_lt_h_rec
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T06:47:46.62409+00:00
-- url     : https://prove2.me/submissions/103548ef-5166-4692-a2b1-8e34fd4e1fb0

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
open IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank (NR h v)
open IntMul.Kappa.R8.Bit.Oppbank.LocSlots (INJ TPTS)

private theorem pts_flat_chunk_0 :
    ((List.range 50).map (fun k => (0 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_1 :
    ((List.range 50).map (fun k => (50 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_2 :
    ((List.range 50).map (fun k => (100 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_3 :
    ((List.range 50).map (fun k => (150 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_4 :
    ((List.range 50).map (fun k => (200 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_5 :
    ((List.range 50).map (fun k => (250 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_6 :
    ((List.range 50).map (fun k => (300 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_7 :
    ((List.range 50).map (fun k => (350 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_8 :
    ((List.range 50).map (fun k => (400 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_9 :
    ((List.range 50).map (fun k => (450 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_10 :
    ((List.range 50).map (fun k => (500 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_11 :
    ((List.range 50).map (fun k => (550 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_12 :
    ((List.range 50).map (fun k => (600 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_13 :
    ((List.range 50).map (fun k => (650 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_14 :
    ((List.range 50).map (fun k => (700 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_15 :
    ((List.range 50).map (fun k => (750 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_16 :
    ((List.range 50).map (fun k => (800 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_17 :
    ((List.range 50).map (fun k => (850 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_18 :
    ((List.range 50).map (fun k => (900 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_19 :
    ((List.range 50).map (fun k => (950 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_20 :
    ((List.range 50).map (fun k => (1000 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_21 :
    ((List.range 50).map (fun k => (1050 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_22 :
    ((List.range 50).map (fun k => (1100 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_23 :
    ((List.range 50).map (fun k => (1150 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_24 :
    ((List.range 50).map (fun k => (1200 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_25 :
    ((List.range 50).map (fun k => (1250 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_26 :
    ((List.range 50).map (fun k => (1300 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_27 :
    ((List.range 50).map (fun k => (1350 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_28 :
    ((List.range 50).map (fun k => (1400 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_29 :
    ((List.range 50).map (fun k => (1450 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_30 :
    ((List.range 50).map (fun k => (1500 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_31 :
    ((List.range 50).map (fun k => (1550 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_32 :
    ((List.range 50).map (fun k => (1600 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_33 :
    ((List.range 50).map (fun k => (1650 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_34 :
    ((List.range 50).map (fun k => (1700 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_35 :
    ((List.range 50).map (fun k => (1750 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_36 :
    ((List.range 50).map (fun k => (1800 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_37 :
    ((List.range 50).map (fun k => (1850 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_38 :
    ((List.range 50).map (fun k => (1900 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_39 :
    ((List.range 50).map (fun k => (1950 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_40 :
    ((List.range 50).map (fun k => (2000 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_41 :
    ((List.range 50).map (fun k => (2050 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_42 :
    ((List.range 50).map (fun k => (2100 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_43 :
    ((List.range 50).map (fun k => (2150 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_44 :
    ((List.range 50).map (fun k => (2200 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_45 :
    ((List.range 50).map (fun k => (2250 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_46 :
    ((List.range 50).map (fun k => (2300 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_47 :
    ((List.range 50).map (fun k => (2350 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_48 :
    ((List.range 50).map (fun k => (2400 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_49 :
    ((List.range 50).map (fun k => (2450 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_50 :
    ((List.range 50).map (fun k => (2500 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_51 :
    ((List.range 50).map (fun k => (2550 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_52 :
    ((List.range 50).map (fun k => (2600 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_53 :
    ((List.range 50).map (fun k => (2650 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_54 :
    ((List.range 50).map (fun k => (2700 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_55 :
    ((List.range 50).map (fun k => (2750 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_56 :
    ((List.range 50).map (fun k => (2800 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_57 :
    ((List.range 50).map (fun k => (2850 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_58 :
    ((List.range 50).map (fun k => (2900 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_59 :
    ((List.range 50).map (fun k => (2950 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_60 :
    ((List.range 50).map (fun k => (3000 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_61 :
    ((List.range 50).map (fun k => (3050 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_62 :
    ((List.range 50).map (fun k => (3100 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_63 :
    ((List.range 50).map (fun k => (3150 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_64 :
    ((List.range 50).map (fun k => (3200 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_65 :
    ((List.range 50).map (fun k => (3250 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_66 :
    ((List.range 50).map (fun k => (3300 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_67 :
    ((List.range 50).map (fun k => (3350 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_68 :
    ((List.range 50).map (fun k => (3400 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_69 :
    ((List.range 50).map (fun k => (3450 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_70 :
    ((List.range 50).map (fun k => (3500 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_71 :
    ((List.range 50).map (fun k => (3550 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_72 :
    ((List.range 50).map (fun k => (3600 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_73 :
    ((List.range 50).map (fun k => (3650 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_74 :
    ((List.range 50).map (fun k => (3700 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_75 :
    ((List.range 50).map (fun k => (3750 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_76 :
    ((List.range 50).map (fun k => (3800 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_77 :
    ((List.range 50).map (fun k => (3850 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_78 :
    ((List.range 50).map (fun k => (3900 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_79 :
    ((List.range 50).map (fun k => (3950 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_80 :
    ((List.range 50).map (fun k => (4000 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_81 :
    ((List.range 50).map (fun k => (4050 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_82 :
    ((List.range 50).map (fun k => (4100 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_83 :
    ((List.range 50).map (fun k => (4150 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_84 :
    ((List.range 50).map (fun k => (4200 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_85 :
    ((List.range 50).map (fun k => (4250 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_86 :
    ((List.range 50).map (fun k => (4300 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_87 :
    ((List.range 50).map (fun k => (4350 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_88 :
    ((List.range 50).map (fun k => (4400 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_89 :
    ((List.range 50).map (fun k => (4450 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_90 :
    ((List.range 50).map (fun k => (4500 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_91 :
    ((List.range 50).map (fun k => (4550 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_92 :
    ((List.range 50).map (fun k => (4600 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_93 :
    ((List.range 50).map (fun k => (4650 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_94 :
    ((List.range 50).map (fun k => (4700 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_95 :
    ((List.range 50).map (fun k => (4750 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_96 :
    ((List.range 50).map (fun k => (4800 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_97 :
    ((List.range 50).map (fun k => (4850 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_98 :
    ((List.range 50).map (fun k => (4900 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_99 :
    ((List.range 50).map (fun k => (4950 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_100 :
    ((List.range 50).map (fun k => (5000 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_101 :
    ((List.range 50).map (fun k => (5050 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_102 :
    ((List.range 50).map (fun k => (5100 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_103 :
    ((List.range 50).map (fun k => (5150 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_104 :
    ((List.range 50).map (fun k => (5200 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_105 :
    ((List.range 50).map (fun k => (5250 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_chunk_106 :
    ((List.range 13).map (fun k => (5300 : ℕ) + k)).all
      (fun idx => decide (fieldOf TPTS 5 idx < 23)) = true := by
  decide

private theorem pts_flat_flat (idx : ℕ) (hidx : idx < 5313) : fieldOf TPTS 5 idx < 23 := by
  if h : idx < 50 then
    have hk : idx - 0 < 50 := by omega
    have hall := pts_flat_chunk_0
    have hmem : 0 + (idx - 0) ∈
        (List.range 50).map (fun k => (0 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 0, List.mem_range.mpr hk, by omega⟩
    have heq : 0 + (idx - 0) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 100 then
    have hk : idx - 50 < 50 := by omega
    have hall := pts_flat_chunk_1
    have hmem : 50 + (idx - 50) ∈
        (List.range 50).map (fun k => (50 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 50, List.mem_range.mpr hk, by omega⟩
    have heq : 50 + (idx - 50) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 150 then
    have hk : idx - 100 < 50 := by omega
    have hall := pts_flat_chunk_2
    have hmem : 100 + (idx - 100) ∈
        (List.range 50).map (fun k => (100 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 100, List.mem_range.mpr hk, by omega⟩
    have heq : 100 + (idx - 100) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 200 then
    have hk : idx - 150 < 50 := by omega
    have hall := pts_flat_chunk_3
    have hmem : 150 + (idx - 150) ∈
        (List.range 50).map (fun k => (150 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 150, List.mem_range.mpr hk, by omega⟩
    have heq : 150 + (idx - 150) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 250 then
    have hk : idx - 200 < 50 := by omega
    have hall := pts_flat_chunk_4
    have hmem : 200 + (idx - 200) ∈
        (List.range 50).map (fun k => (200 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 200, List.mem_range.mpr hk, by omega⟩
    have heq : 200 + (idx - 200) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 300 then
    have hk : idx - 250 < 50 := by omega
    have hall := pts_flat_chunk_5
    have hmem : 250 + (idx - 250) ∈
        (List.range 50).map (fun k => (250 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 250, List.mem_range.mpr hk, by omega⟩
    have heq : 250 + (idx - 250) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 350 then
    have hk : idx - 300 < 50 := by omega
    have hall := pts_flat_chunk_6
    have hmem : 300 + (idx - 300) ∈
        (List.range 50).map (fun k => (300 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 300, List.mem_range.mpr hk, by omega⟩
    have heq : 300 + (idx - 300) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 400 then
    have hk : idx - 350 < 50 := by omega
    have hall := pts_flat_chunk_7
    have hmem : 350 + (idx - 350) ∈
        (List.range 50).map (fun k => (350 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 350, List.mem_range.mpr hk, by omega⟩
    have heq : 350 + (idx - 350) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 450 then
    have hk : idx - 400 < 50 := by omega
    have hall := pts_flat_chunk_8
    have hmem : 400 + (idx - 400) ∈
        (List.range 50).map (fun k => (400 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 400, List.mem_range.mpr hk, by omega⟩
    have heq : 400 + (idx - 400) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 500 then
    have hk : idx - 450 < 50 := by omega
    have hall := pts_flat_chunk_9
    have hmem : 450 + (idx - 450) ∈
        (List.range 50).map (fun k => (450 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 450, List.mem_range.mpr hk, by omega⟩
    have heq : 450 + (idx - 450) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 550 then
    have hk : idx - 500 < 50 := by omega
    have hall := pts_flat_chunk_10
    have hmem : 500 + (idx - 500) ∈
        (List.range 50).map (fun k => (500 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 500, List.mem_range.mpr hk, by omega⟩
    have heq : 500 + (idx - 500) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 600 then
    have hk : idx - 550 < 50 := by omega
    have hall := pts_flat_chunk_11
    have hmem : 550 + (idx - 550) ∈
        (List.range 50).map (fun k => (550 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 550, List.mem_range.mpr hk, by omega⟩
    have heq : 550 + (idx - 550) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 650 then
    have hk : idx - 600 < 50 := by omega
    have hall := pts_flat_chunk_12
    have hmem : 600 + (idx - 600) ∈
        (List.range 50).map (fun k => (600 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 600, List.mem_range.mpr hk, by omega⟩
    have heq : 600 + (idx - 600) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 700 then
    have hk : idx - 650 < 50 := by omega
    have hall := pts_flat_chunk_13
    have hmem : 650 + (idx - 650) ∈
        (List.range 50).map (fun k => (650 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 650, List.mem_range.mpr hk, by omega⟩
    have heq : 650 + (idx - 650) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 750 then
    have hk : idx - 700 < 50 := by omega
    have hall := pts_flat_chunk_14
    have hmem : 700 + (idx - 700) ∈
        (List.range 50).map (fun k => (700 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 700, List.mem_range.mpr hk, by omega⟩
    have heq : 700 + (idx - 700) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 800 then
    have hk : idx - 750 < 50 := by omega
    have hall := pts_flat_chunk_15
    have hmem : 750 + (idx - 750) ∈
        (List.range 50).map (fun k => (750 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 750, List.mem_range.mpr hk, by omega⟩
    have heq : 750 + (idx - 750) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 850 then
    have hk : idx - 800 < 50 := by omega
    have hall := pts_flat_chunk_16
    have hmem : 800 + (idx - 800) ∈
        (List.range 50).map (fun k => (800 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 800, List.mem_range.mpr hk, by omega⟩
    have heq : 800 + (idx - 800) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 900 then
    have hk : idx - 850 < 50 := by omega
    have hall := pts_flat_chunk_17
    have hmem : 850 + (idx - 850) ∈
        (List.range 50).map (fun k => (850 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 850, List.mem_range.mpr hk, by omega⟩
    have heq : 850 + (idx - 850) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 950 then
    have hk : idx - 900 < 50 := by omega
    have hall := pts_flat_chunk_18
    have hmem : 900 + (idx - 900) ∈
        (List.range 50).map (fun k => (900 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 900, List.mem_range.mpr hk, by omega⟩
    have heq : 900 + (idx - 900) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 1000 then
    have hk : idx - 950 < 50 := by omega
    have hall := pts_flat_chunk_19
    have hmem : 950 + (idx - 950) ∈
        (List.range 50).map (fun k => (950 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 950, List.mem_range.mpr hk, by omega⟩
    have heq : 950 + (idx - 950) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 1050 then
    have hk : idx - 1000 < 50 := by omega
    have hall := pts_flat_chunk_20
    have hmem : 1000 + (idx - 1000) ∈
        (List.range 50).map (fun k => (1000 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 1000, List.mem_range.mpr hk, by omega⟩
    have heq : 1000 + (idx - 1000) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 1100 then
    have hk : idx - 1050 < 50 := by omega
    have hall := pts_flat_chunk_21
    have hmem : 1050 + (idx - 1050) ∈
        (List.range 50).map (fun k => (1050 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 1050, List.mem_range.mpr hk, by omega⟩
    have heq : 1050 + (idx - 1050) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 1150 then
    have hk : idx - 1100 < 50 := by omega
    have hall := pts_flat_chunk_22
    have hmem : 1100 + (idx - 1100) ∈
        (List.range 50).map (fun k => (1100 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 1100, List.mem_range.mpr hk, by omega⟩
    have heq : 1100 + (idx - 1100) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 1200 then
    have hk : idx - 1150 < 50 := by omega
    have hall := pts_flat_chunk_23
    have hmem : 1150 + (idx - 1150) ∈
        (List.range 50).map (fun k => (1150 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 1150, List.mem_range.mpr hk, by omega⟩
    have heq : 1150 + (idx - 1150) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 1250 then
    have hk : idx - 1200 < 50 := by omega
    have hall := pts_flat_chunk_24
    have hmem : 1200 + (idx - 1200) ∈
        (List.range 50).map (fun k => (1200 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 1200, List.mem_range.mpr hk, by omega⟩
    have heq : 1200 + (idx - 1200) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 1300 then
    have hk : idx - 1250 < 50 := by omega
    have hall := pts_flat_chunk_25
    have hmem : 1250 + (idx - 1250) ∈
        (List.range 50).map (fun k => (1250 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 1250, List.mem_range.mpr hk, by omega⟩
    have heq : 1250 + (idx - 1250) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 1350 then
    have hk : idx - 1300 < 50 := by omega
    have hall := pts_flat_chunk_26
    have hmem : 1300 + (idx - 1300) ∈
        (List.range 50).map (fun k => (1300 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 1300, List.mem_range.mpr hk, by omega⟩
    have heq : 1300 + (idx - 1300) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 1400 then
    have hk : idx - 1350 < 50 := by omega
    have hall := pts_flat_chunk_27
    have hmem : 1350 + (idx - 1350) ∈
        (List.range 50).map (fun k => (1350 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 1350, List.mem_range.mpr hk, by omega⟩
    have heq : 1350 + (idx - 1350) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 1450 then
    have hk : idx - 1400 < 50 := by omega
    have hall := pts_flat_chunk_28
    have hmem : 1400 + (idx - 1400) ∈
        (List.range 50).map (fun k => (1400 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 1400, List.mem_range.mpr hk, by omega⟩
    have heq : 1400 + (idx - 1400) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 1500 then
    have hk : idx - 1450 < 50 := by omega
    have hall := pts_flat_chunk_29
    have hmem : 1450 + (idx - 1450) ∈
        (List.range 50).map (fun k => (1450 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 1450, List.mem_range.mpr hk, by omega⟩
    have heq : 1450 + (idx - 1450) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 1550 then
    have hk : idx - 1500 < 50 := by omega
    have hall := pts_flat_chunk_30
    have hmem : 1500 + (idx - 1500) ∈
        (List.range 50).map (fun k => (1500 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 1500, List.mem_range.mpr hk, by omega⟩
    have heq : 1500 + (idx - 1500) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 1600 then
    have hk : idx - 1550 < 50 := by omega
    have hall := pts_flat_chunk_31
    have hmem : 1550 + (idx - 1550) ∈
        (List.range 50).map (fun k => (1550 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 1550, List.mem_range.mpr hk, by omega⟩
    have heq : 1550 + (idx - 1550) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 1650 then
    have hk : idx - 1600 < 50 := by omega
    have hall := pts_flat_chunk_32
    have hmem : 1600 + (idx - 1600) ∈
        (List.range 50).map (fun k => (1600 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 1600, List.mem_range.mpr hk, by omega⟩
    have heq : 1600 + (idx - 1600) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 1700 then
    have hk : idx - 1650 < 50 := by omega
    have hall := pts_flat_chunk_33
    have hmem : 1650 + (idx - 1650) ∈
        (List.range 50).map (fun k => (1650 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 1650, List.mem_range.mpr hk, by omega⟩
    have heq : 1650 + (idx - 1650) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 1750 then
    have hk : idx - 1700 < 50 := by omega
    have hall := pts_flat_chunk_34
    have hmem : 1700 + (idx - 1700) ∈
        (List.range 50).map (fun k => (1700 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 1700, List.mem_range.mpr hk, by omega⟩
    have heq : 1700 + (idx - 1700) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 1800 then
    have hk : idx - 1750 < 50 := by omega
    have hall := pts_flat_chunk_35
    have hmem : 1750 + (idx - 1750) ∈
        (List.range 50).map (fun k => (1750 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 1750, List.mem_range.mpr hk, by omega⟩
    have heq : 1750 + (idx - 1750) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 1850 then
    have hk : idx - 1800 < 50 := by omega
    have hall := pts_flat_chunk_36
    have hmem : 1800 + (idx - 1800) ∈
        (List.range 50).map (fun k => (1800 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 1800, List.mem_range.mpr hk, by omega⟩
    have heq : 1800 + (idx - 1800) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 1900 then
    have hk : idx - 1850 < 50 := by omega
    have hall := pts_flat_chunk_37
    have hmem : 1850 + (idx - 1850) ∈
        (List.range 50).map (fun k => (1850 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 1850, List.mem_range.mpr hk, by omega⟩
    have heq : 1850 + (idx - 1850) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 1950 then
    have hk : idx - 1900 < 50 := by omega
    have hall := pts_flat_chunk_38
    have hmem : 1900 + (idx - 1900) ∈
        (List.range 50).map (fun k => (1900 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 1900, List.mem_range.mpr hk, by omega⟩
    have heq : 1900 + (idx - 1900) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 2000 then
    have hk : idx - 1950 < 50 := by omega
    have hall := pts_flat_chunk_39
    have hmem : 1950 + (idx - 1950) ∈
        (List.range 50).map (fun k => (1950 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 1950, List.mem_range.mpr hk, by omega⟩
    have heq : 1950 + (idx - 1950) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 2050 then
    have hk : idx - 2000 < 50 := by omega
    have hall := pts_flat_chunk_40
    have hmem : 2000 + (idx - 2000) ∈
        (List.range 50).map (fun k => (2000 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 2000, List.mem_range.mpr hk, by omega⟩
    have heq : 2000 + (idx - 2000) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 2100 then
    have hk : idx - 2050 < 50 := by omega
    have hall := pts_flat_chunk_41
    have hmem : 2050 + (idx - 2050) ∈
        (List.range 50).map (fun k => (2050 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 2050, List.mem_range.mpr hk, by omega⟩
    have heq : 2050 + (idx - 2050) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 2150 then
    have hk : idx - 2100 < 50 := by omega
    have hall := pts_flat_chunk_42
    have hmem : 2100 + (idx - 2100) ∈
        (List.range 50).map (fun k => (2100 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 2100, List.mem_range.mpr hk, by omega⟩
    have heq : 2100 + (idx - 2100) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 2200 then
    have hk : idx - 2150 < 50 := by omega
    have hall := pts_flat_chunk_43
    have hmem : 2150 + (idx - 2150) ∈
        (List.range 50).map (fun k => (2150 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 2150, List.mem_range.mpr hk, by omega⟩
    have heq : 2150 + (idx - 2150) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 2250 then
    have hk : idx - 2200 < 50 := by omega
    have hall := pts_flat_chunk_44
    have hmem : 2200 + (idx - 2200) ∈
        (List.range 50).map (fun k => (2200 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 2200, List.mem_range.mpr hk, by omega⟩
    have heq : 2200 + (idx - 2200) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 2300 then
    have hk : idx - 2250 < 50 := by omega
    have hall := pts_flat_chunk_45
    have hmem : 2250 + (idx - 2250) ∈
        (List.range 50).map (fun k => (2250 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 2250, List.mem_range.mpr hk, by omega⟩
    have heq : 2250 + (idx - 2250) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 2350 then
    have hk : idx - 2300 < 50 := by omega
    have hall := pts_flat_chunk_46
    have hmem : 2300 + (idx - 2300) ∈
        (List.range 50).map (fun k => (2300 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 2300, List.mem_range.mpr hk, by omega⟩
    have heq : 2300 + (idx - 2300) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 2400 then
    have hk : idx - 2350 < 50 := by omega
    have hall := pts_flat_chunk_47
    have hmem : 2350 + (idx - 2350) ∈
        (List.range 50).map (fun k => (2350 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 2350, List.mem_range.mpr hk, by omega⟩
    have heq : 2350 + (idx - 2350) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 2450 then
    have hk : idx - 2400 < 50 := by omega
    have hall := pts_flat_chunk_48
    have hmem : 2400 + (idx - 2400) ∈
        (List.range 50).map (fun k => (2400 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 2400, List.mem_range.mpr hk, by omega⟩
    have heq : 2400 + (idx - 2400) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 2500 then
    have hk : idx - 2450 < 50 := by omega
    have hall := pts_flat_chunk_49
    have hmem : 2450 + (idx - 2450) ∈
        (List.range 50).map (fun k => (2450 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 2450, List.mem_range.mpr hk, by omega⟩
    have heq : 2450 + (idx - 2450) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 2550 then
    have hk : idx - 2500 < 50 := by omega
    have hall := pts_flat_chunk_50
    have hmem : 2500 + (idx - 2500) ∈
        (List.range 50).map (fun k => (2500 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 2500, List.mem_range.mpr hk, by omega⟩
    have heq : 2500 + (idx - 2500) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 2600 then
    have hk : idx - 2550 < 50 := by omega
    have hall := pts_flat_chunk_51
    have hmem : 2550 + (idx - 2550) ∈
        (List.range 50).map (fun k => (2550 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 2550, List.mem_range.mpr hk, by omega⟩
    have heq : 2550 + (idx - 2550) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 2650 then
    have hk : idx - 2600 < 50 := by omega
    have hall := pts_flat_chunk_52
    have hmem : 2600 + (idx - 2600) ∈
        (List.range 50).map (fun k => (2600 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 2600, List.mem_range.mpr hk, by omega⟩
    have heq : 2600 + (idx - 2600) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 2700 then
    have hk : idx - 2650 < 50 := by omega
    have hall := pts_flat_chunk_53
    have hmem : 2650 + (idx - 2650) ∈
        (List.range 50).map (fun k => (2650 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 2650, List.mem_range.mpr hk, by omega⟩
    have heq : 2650 + (idx - 2650) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 2750 then
    have hk : idx - 2700 < 50 := by omega
    have hall := pts_flat_chunk_54
    have hmem : 2700 + (idx - 2700) ∈
        (List.range 50).map (fun k => (2700 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 2700, List.mem_range.mpr hk, by omega⟩
    have heq : 2700 + (idx - 2700) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 2800 then
    have hk : idx - 2750 < 50 := by omega
    have hall := pts_flat_chunk_55
    have hmem : 2750 + (idx - 2750) ∈
        (List.range 50).map (fun k => (2750 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 2750, List.mem_range.mpr hk, by omega⟩
    have heq : 2750 + (idx - 2750) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 2850 then
    have hk : idx - 2800 < 50 := by omega
    have hall := pts_flat_chunk_56
    have hmem : 2800 + (idx - 2800) ∈
        (List.range 50).map (fun k => (2800 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 2800, List.mem_range.mpr hk, by omega⟩
    have heq : 2800 + (idx - 2800) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 2900 then
    have hk : idx - 2850 < 50 := by omega
    have hall := pts_flat_chunk_57
    have hmem : 2850 + (idx - 2850) ∈
        (List.range 50).map (fun k => (2850 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 2850, List.mem_range.mpr hk, by omega⟩
    have heq : 2850 + (idx - 2850) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 2950 then
    have hk : idx - 2900 < 50 := by omega
    have hall := pts_flat_chunk_58
    have hmem : 2900 + (idx - 2900) ∈
        (List.range 50).map (fun k => (2900 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 2900, List.mem_range.mpr hk, by omega⟩
    have heq : 2900 + (idx - 2900) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 3000 then
    have hk : idx - 2950 < 50 := by omega
    have hall := pts_flat_chunk_59
    have hmem : 2950 + (idx - 2950) ∈
        (List.range 50).map (fun k => (2950 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 2950, List.mem_range.mpr hk, by omega⟩
    have heq : 2950 + (idx - 2950) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 3050 then
    have hk : idx - 3000 < 50 := by omega
    have hall := pts_flat_chunk_60
    have hmem : 3000 + (idx - 3000) ∈
        (List.range 50).map (fun k => (3000 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 3000, List.mem_range.mpr hk, by omega⟩
    have heq : 3000 + (idx - 3000) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 3100 then
    have hk : idx - 3050 < 50 := by omega
    have hall := pts_flat_chunk_61
    have hmem : 3050 + (idx - 3050) ∈
        (List.range 50).map (fun k => (3050 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 3050, List.mem_range.mpr hk, by omega⟩
    have heq : 3050 + (idx - 3050) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 3150 then
    have hk : idx - 3100 < 50 := by omega
    have hall := pts_flat_chunk_62
    have hmem : 3100 + (idx - 3100) ∈
        (List.range 50).map (fun k => (3100 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 3100, List.mem_range.mpr hk, by omega⟩
    have heq : 3100 + (idx - 3100) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 3200 then
    have hk : idx - 3150 < 50 := by omega
    have hall := pts_flat_chunk_63
    have hmem : 3150 + (idx - 3150) ∈
        (List.range 50).map (fun k => (3150 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 3150, List.mem_range.mpr hk, by omega⟩
    have heq : 3150 + (idx - 3150) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 3250 then
    have hk : idx - 3200 < 50 := by omega
    have hall := pts_flat_chunk_64
    have hmem : 3200 + (idx - 3200) ∈
        (List.range 50).map (fun k => (3200 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 3200, List.mem_range.mpr hk, by omega⟩
    have heq : 3200 + (idx - 3200) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 3300 then
    have hk : idx - 3250 < 50 := by omega
    have hall := pts_flat_chunk_65
    have hmem : 3250 + (idx - 3250) ∈
        (List.range 50).map (fun k => (3250 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 3250, List.mem_range.mpr hk, by omega⟩
    have heq : 3250 + (idx - 3250) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 3350 then
    have hk : idx - 3300 < 50 := by omega
    have hall := pts_flat_chunk_66
    have hmem : 3300 + (idx - 3300) ∈
        (List.range 50).map (fun k => (3300 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 3300, List.mem_range.mpr hk, by omega⟩
    have heq : 3300 + (idx - 3300) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 3400 then
    have hk : idx - 3350 < 50 := by omega
    have hall := pts_flat_chunk_67
    have hmem : 3350 + (idx - 3350) ∈
        (List.range 50).map (fun k => (3350 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 3350, List.mem_range.mpr hk, by omega⟩
    have heq : 3350 + (idx - 3350) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 3450 then
    have hk : idx - 3400 < 50 := by omega
    have hall := pts_flat_chunk_68
    have hmem : 3400 + (idx - 3400) ∈
        (List.range 50).map (fun k => (3400 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 3400, List.mem_range.mpr hk, by omega⟩
    have heq : 3400 + (idx - 3400) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 3500 then
    have hk : idx - 3450 < 50 := by omega
    have hall := pts_flat_chunk_69
    have hmem : 3450 + (idx - 3450) ∈
        (List.range 50).map (fun k => (3450 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 3450, List.mem_range.mpr hk, by omega⟩
    have heq : 3450 + (idx - 3450) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 3550 then
    have hk : idx - 3500 < 50 := by omega
    have hall := pts_flat_chunk_70
    have hmem : 3500 + (idx - 3500) ∈
        (List.range 50).map (fun k => (3500 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 3500, List.mem_range.mpr hk, by omega⟩
    have heq : 3500 + (idx - 3500) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 3600 then
    have hk : idx - 3550 < 50 := by omega
    have hall := pts_flat_chunk_71
    have hmem : 3550 + (idx - 3550) ∈
        (List.range 50).map (fun k => (3550 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 3550, List.mem_range.mpr hk, by omega⟩
    have heq : 3550 + (idx - 3550) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 3650 then
    have hk : idx - 3600 < 50 := by omega
    have hall := pts_flat_chunk_72
    have hmem : 3600 + (idx - 3600) ∈
        (List.range 50).map (fun k => (3600 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 3600, List.mem_range.mpr hk, by omega⟩
    have heq : 3600 + (idx - 3600) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 3700 then
    have hk : idx - 3650 < 50 := by omega
    have hall := pts_flat_chunk_73
    have hmem : 3650 + (idx - 3650) ∈
        (List.range 50).map (fun k => (3650 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 3650, List.mem_range.mpr hk, by omega⟩
    have heq : 3650 + (idx - 3650) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 3750 then
    have hk : idx - 3700 < 50 := by omega
    have hall := pts_flat_chunk_74
    have hmem : 3700 + (idx - 3700) ∈
        (List.range 50).map (fun k => (3700 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 3700, List.mem_range.mpr hk, by omega⟩
    have heq : 3700 + (idx - 3700) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 3800 then
    have hk : idx - 3750 < 50 := by omega
    have hall := pts_flat_chunk_75
    have hmem : 3750 + (idx - 3750) ∈
        (List.range 50).map (fun k => (3750 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 3750, List.mem_range.mpr hk, by omega⟩
    have heq : 3750 + (idx - 3750) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 3850 then
    have hk : idx - 3800 < 50 := by omega
    have hall := pts_flat_chunk_76
    have hmem : 3800 + (idx - 3800) ∈
        (List.range 50).map (fun k => (3800 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 3800, List.mem_range.mpr hk, by omega⟩
    have heq : 3800 + (idx - 3800) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 3900 then
    have hk : idx - 3850 < 50 := by omega
    have hall := pts_flat_chunk_77
    have hmem : 3850 + (idx - 3850) ∈
        (List.range 50).map (fun k => (3850 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 3850, List.mem_range.mpr hk, by omega⟩
    have heq : 3850 + (idx - 3850) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 3950 then
    have hk : idx - 3900 < 50 := by omega
    have hall := pts_flat_chunk_78
    have hmem : 3900 + (idx - 3900) ∈
        (List.range 50).map (fun k => (3900 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 3900, List.mem_range.mpr hk, by omega⟩
    have heq : 3900 + (idx - 3900) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 4000 then
    have hk : idx - 3950 < 50 := by omega
    have hall := pts_flat_chunk_79
    have hmem : 3950 + (idx - 3950) ∈
        (List.range 50).map (fun k => (3950 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 3950, List.mem_range.mpr hk, by omega⟩
    have heq : 3950 + (idx - 3950) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 4050 then
    have hk : idx - 4000 < 50 := by omega
    have hall := pts_flat_chunk_80
    have hmem : 4000 + (idx - 4000) ∈
        (List.range 50).map (fun k => (4000 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 4000, List.mem_range.mpr hk, by omega⟩
    have heq : 4000 + (idx - 4000) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 4100 then
    have hk : idx - 4050 < 50 := by omega
    have hall := pts_flat_chunk_81
    have hmem : 4050 + (idx - 4050) ∈
        (List.range 50).map (fun k => (4050 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 4050, List.mem_range.mpr hk, by omega⟩
    have heq : 4050 + (idx - 4050) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 4150 then
    have hk : idx - 4100 < 50 := by omega
    have hall := pts_flat_chunk_82
    have hmem : 4100 + (idx - 4100) ∈
        (List.range 50).map (fun k => (4100 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 4100, List.mem_range.mpr hk, by omega⟩
    have heq : 4100 + (idx - 4100) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 4200 then
    have hk : idx - 4150 < 50 := by omega
    have hall := pts_flat_chunk_83
    have hmem : 4150 + (idx - 4150) ∈
        (List.range 50).map (fun k => (4150 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 4150, List.mem_range.mpr hk, by omega⟩
    have heq : 4150 + (idx - 4150) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 4250 then
    have hk : idx - 4200 < 50 := by omega
    have hall := pts_flat_chunk_84
    have hmem : 4200 + (idx - 4200) ∈
        (List.range 50).map (fun k => (4200 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 4200, List.mem_range.mpr hk, by omega⟩
    have heq : 4200 + (idx - 4200) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 4300 then
    have hk : idx - 4250 < 50 := by omega
    have hall := pts_flat_chunk_85
    have hmem : 4250 + (idx - 4250) ∈
        (List.range 50).map (fun k => (4250 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 4250, List.mem_range.mpr hk, by omega⟩
    have heq : 4250 + (idx - 4250) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 4350 then
    have hk : idx - 4300 < 50 := by omega
    have hall := pts_flat_chunk_86
    have hmem : 4300 + (idx - 4300) ∈
        (List.range 50).map (fun k => (4300 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 4300, List.mem_range.mpr hk, by omega⟩
    have heq : 4300 + (idx - 4300) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 4400 then
    have hk : idx - 4350 < 50 := by omega
    have hall := pts_flat_chunk_87
    have hmem : 4350 + (idx - 4350) ∈
        (List.range 50).map (fun k => (4350 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 4350, List.mem_range.mpr hk, by omega⟩
    have heq : 4350 + (idx - 4350) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 4450 then
    have hk : idx - 4400 < 50 := by omega
    have hall := pts_flat_chunk_88
    have hmem : 4400 + (idx - 4400) ∈
        (List.range 50).map (fun k => (4400 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 4400, List.mem_range.mpr hk, by omega⟩
    have heq : 4400 + (idx - 4400) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 4500 then
    have hk : idx - 4450 < 50 := by omega
    have hall := pts_flat_chunk_89
    have hmem : 4450 + (idx - 4450) ∈
        (List.range 50).map (fun k => (4450 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 4450, List.mem_range.mpr hk, by omega⟩
    have heq : 4450 + (idx - 4450) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 4550 then
    have hk : idx - 4500 < 50 := by omega
    have hall := pts_flat_chunk_90
    have hmem : 4500 + (idx - 4500) ∈
        (List.range 50).map (fun k => (4500 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 4500, List.mem_range.mpr hk, by omega⟩
    have heq : 4500 + (idx - 4500) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 4600 then
    have hk : idx - 4550 < 50 := by omega
    have hall := pts_flat_chunk_91
    have hmem : 4550 + (idx - 4550) ∈
        (List.range 50).map (fun k => (4550 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 4550, List.mem_range.mpr hk, by omega⟩
    have heq : 4550 + (idx - 4550) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 4650 then
    have hk : idx - 4600 < 50 := by omega
    have hall := pts_flat_chunk_92
    have hmem : 4600 + (idx - 4600) ∈
        (List.range 50).map (fun k => (4600 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 4600, List.mem_range.mpr hk, by omega⟩
    have heq : 4600 + (idx - 4600) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 4700 then
    have hk : idx - 4650 < 50 := by omega
    have hall := pts_flat_chunk_93
    have hmem : 4650 + (idx - 4650) ∈
        (List.range 50).map (fun k => (4650 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 4650, List.mem_range.mpr hk, by omega⟩
    have heq : 4650 + (idx - 4650) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 4750 then
    have hk : idx - 4700 < 50 := by omega
    have hall := pts_flat_chunk_94
    have hmem : 4700 + (idx - 4700) ∈
        (List.range 50).map (fun k => (4700 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 4700, List.mem_range.mpr hk, by omega⟩
    have heq : 4700 + (idx - 4700) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 4800 then
    have hk : idx - 4750 < 50 := by omega
    have hall := pts_flat_chunk_95
    have hmem : 4750 + (idx - 4750) ∈
        (List.range 50).map (fun k => (4750 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 4750, List.mem_range.mpr hk, by omega⟩
    have heq : 4750 + (idx - 4750) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 4850 then
    have hk : idx - 4800 < 50 := by omega
    have hall := pts_flat_chunk_96
    have hmem : 4800 + (idx - 4800) ∈
        (List.range 50).map (fun k => (4800 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 4800, List.mem_range.mpr hk, by omega⟩
    have heq : 4800 + (idx - 4800) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 4900 then
    have hk : idx - 4850 < 50 := by omega
    have hall := pts_flat_chunk_97
    have hmem : 4850 + (idx - 4850) ∈
        (List.range 50).map (fun k => (4850 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 4850, List.mem_range.mpr hk, by omega⟩
    have heq : 4850 + (idx - 4850) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 4950 then
    have hk : idx - 4900 < 50 := by omega
    have hall := pts_flat_chunk_98
    have hmem : 4900 + (idx - 4900) ∈
        (List.range 50).map (fun k => (4900 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 4900, List.mem_range.mpr hk, by omega⟩
    have heq : 4900 + (idx - 4900) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 5000 then
    have hk : idx - 4950 < 50 := by omega
    have hall := pts_flat_chunk_99
    have hmem : 4950 + (idx - 4950) ∈
        (List.range 50).map (fun k => (4950 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 4950, List.mem_range.mpr hk, by omega⟩
    have heq : 4950 + (idx - 4950) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 5050 then
    have hk : idx - 5000 < 50 := by omega
    have hall := pts_flat_chunk_100
    have hmem : 5000 + (idx - 5000) ∈
        (List.range 50).map (fun k => (5000 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 5000, List.mem_range.mpr hk, by omega⟩
    have heq : 5000 + (idx - 5000) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 5100 then
    have hk : idx - 5050 < 50 := by omega
    have hall := pts_flat_chunk_101
    have hmem : 5050 + (idx - 5050) ∈
        (List.range 50).map (fun k => (5050 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 5050, List.mem_range.mpr hk, by omega⟩
    have heq : 5050 + (idx - 5050) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 5150 then
    have hk : idx - 5100 < 50 := by omega
    have hall := pts_flat_chunk_102
    have hmem : 5100 + (idx - 5100) ∈
        (List.range 50).map (fun k => (5100 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 5100, List.mem_range.mpr hk, by omega⟩
    have heq : 5100 + (idx - 5100) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 5200 then
    have hk : idx - 5150 < 50 := by omega
    have hall := pts_flat_chunk_103
    have hmem : 5150 + (idx - 5150) ∈
        (List.range 50).map (fun k => (5150 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 5150, List.mem_range.mpr hk, by omega⟩
    have heq : 5150 + (idx - 5150) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 5250 then
    have hk : idx - 5200 < 50 := by omega
    have hall := pts_flat_chunk_104
    have hmem : 5200 + (idx - 5200) ∈
        (List.range 50).map (fun k => (5200 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 5200, List.mem_range.mpr hk, by omega⟩
    have heq : 5200 + (idx - 5200) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else if h : idx < 5300 then
    have hk : idx - 5250 < 50 := by omega
    have hall := pts_flat_chunk_105
    have hmem : 5250 + (idx - 5250) ∈
        (List.range 50).map (fun k => (5250 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 5250, List.mem_range.mpr hk, by omega⟩
    have heq : 5250 + (idx - 5250) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)
  else
    have hk : idx - 5300 < 13 := by omega
    have hall := pts_flat_chunk_106
    have hmem : 5300 + (idx - 5300) ∈
        (List.range 13).map (fun k => (5300 : ℕ) + k) := by
      refine List.mem_map.mpr ⟨idx - 5300, List.mem_range.mpr hk, by omega⟩
    have heq : 5300 + (idx - 5300) = idx := by omega
    rw [heq] at hmem
    exact of_decide_eq_true ((List.all_eq_true.1 hall) _ hmem)

theorem solution (T k : ℕ) (hT : T < v) (hk : k < 3) : pts T k < h := by
  have hidx : 3 * T + k < 5313 := by
    simp only [v] at hT; omega
  simpa [pts, h] using pts_flat_flat (3 * T + k) hidx

