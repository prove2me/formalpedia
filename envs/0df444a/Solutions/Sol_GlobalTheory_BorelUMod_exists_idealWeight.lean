-- Prove2me | solution 1 for GlobalTheory.BorelUMod.exists_idealWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:29:59.092345+00:00
-- url     : https://prove2.me/submissions/a7aba659-66be-471e-a728-bb77530d6fb3

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
theorem _root_.solution {c : Fin n → Fin n → ℤ} :
    ∃ C : Fin n → Fin n → ℤ, IsWeight C ∧ IsIdealWeight c C ∧ IsIdealWeight (fun _ _ => 0) C := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ i j, |c i j| ≤ M := by
    obtain ⟨M, hM⟩ := (Set.finite_range fun p : Fin n × Fin n => (c p.1 p.2).natAbs).bddAbove
    exact ⟨M, fun i j => by
      have : (c i j).natAbs ≤ M := hM ⟨(i, j), rfl⟩
      rw [← Int.natCast_natAbs]; exact_mod_cast this⟩
  have key : ∀ d : Fin n → Fin n → ℤ, (∀ i j, |d i j| ≤ M) →
      IsIdealWeight d fun i j => (M : ℤ) * (n + i.val - j.val) := by
    intro d hd
    have hM0 : (0 : ℤ) ≤ M := Int.natCast_nonneg M
    refine ⟨fun i j _ => ?_, fun i j k h1 _ => ?_, fun i j k _ h2 => ?_⟩
    · have h1 : (1 : ℤ) ≤ n + i.val - j.val := by have := j.2; omega
      nlinarith [abs_le.1 (hd i j)]
    · have h1 : (1 : ℤ) ≤ j.val - i.val := by have := Fin.lt_def.1 h1; omega
      nlinarith [abs_le.1 (hd i j)]
    · have h1 : (1 : ℤ) ≤ k.val - j.val := by have := Fin.lt_def.1 h2; omega
      nlinarith [abs_le.1 (hd j k)]
  refine ⟨_, ⟨fun i j => ?_, fun i j k _ _ => ?_⟩, key c hM, key _ fun _ _ => by simp⟩
  · have := i.2
    have := j.2
    simp only [Fin.val_rev]
    congr 1
    omega
  · have hM0 : (0 : ℤ) ≤ M := Int.natCast_nonneg M
    have h1 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
    nlinarith
end GlobalTheory.BorelUMod
