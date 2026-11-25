-- Prove2me | solution 1 for GlobalTheory.BorelUMod.conj_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:35:27.84478+00:00
-- url     : https://prove2.me/submissions/5021fb3c-aae3-44b1-89da-dc923be61b19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_RelIndexMulMeasure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexEqOfSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnipLatIsOpenIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsTerTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealWeight
import Theorems.Thm_GlobalTheory_BorelUMod_v_eq_exp
import Theorems.Thm_GlobalTheory_BorelUMod_conj_entry
import Theorems.Thm_GlobalTheory_BorelUMod_isWeight_zero
import Theorems.Thm_GlobalTheory_BorelUMod_mem_unipLat
import Theorems.Thm_GlobalTheory_BorelUMod_mem_upLat
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp Formalism.UG
open scoped NNReal
noncomputable section
open GlobalTheory GlobalTheory.BorelUMod
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
namespace GlobalTheory.BorelUMod
theorem _root_.solution {σ : L →+* L} [LocallyCompactSpace (GU σ n)] (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (t : torusU σ n) (u : (borelU σ n).U) :
    conjAut (borelU σ n).U ⟨(borelU σ n).s t, (borelU σ n).Q_le_normalizer ((borelU σ n).s_mem _)⟩ u ∈
      unipLat hσ (isWeight_ord hσ t) ↔ u ∈ unipLat hσ isWeight_zero := by
  rw [mem_unipLat, mem_unipLat, mem_upLat, mem_upLat]
  have e : ∀ i j, ((conjAut (borelU σ n).U
      ⟨(borelU σ n).s t, (borelU σ n).Q_le_normalizer ((borelU σ n).s_mem _)⟩ u).1.1.val - 1) i j =
      t.1 i * (u.1.1.val - 1) i j * (t.1 j : L)⁻¹ := conj_entry t.1 u.1.1
  simp only [e]
  refine and_congr (forall₃_congr fun i j _ => by simp) (forall₃_congr fun i j _ => ?_)
  rw [map_mul, map_mul, map_inv₀, v_eq_exp (t.1 i).ne_zero, v_eq_exp (t.1 j).ne_zero, mul_right_comm,
    ← WithZero.exp_neg, ← WithZero.exp_add, neg_zero, WithZero.exp_zero, neg_sub', sub_eq_add_neg]
  exact mul_le_iff_le_one_right WithZero.exp_pos
end GlobalTheory.BorelUMod
