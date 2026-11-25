-- Prove2me | solution 1 for GlobalTheory.Phase.val_trans_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:02:15.283698+00:00
-- url     : https://prove2.me/submissions/c8c1b272-ba68-45f6-883e-93003a2822cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitarySiegelThetaTransformationLawStandar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EqOfSiegelThetaSeriesRationalEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TransSUnique
import Theorems.Thm_GlobalTheory_Phase_transS_unique
import Theorems.Thm_GlobalTheory_SW_FourierJ_ft_level
import Theorems.Thm_GlobalTheory_SW_FourierJ_trans_J


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase
namespace GlobalTheory.Phase
theorem _root_.solution : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι],
    Even (Fintype.card κ) → ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB φ → IsSB ψ →
      TransS (Matrix.J ι ℚ) φ ψ → ∀ y, ∃ (u : ℂ) (y' : Matrix κ ι ℚ),
        Ph u ∧ ψ y = u * haar (fun x => φ x * chr y' x) := by
  intro κ ι _ _ _ ⟨p, hp⟩ φ ψ ⟨R, hR, h⟩ hψ ht y
  have e := transS_unique (SymplecticGroup.J_mem ι ℚ) hψ
    ⟨R, hR, FourierJ.ft_level hR h _⟩ ht (FourierJ.trans_J hp hR h)
  refine ⟨I ^ (Fintype.card ι * p), y, ⟨4, by norm_num, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul]; simp [Complex.I_pow_four]
  · rw [e]
    simp only [FourierJ.ft, FourierJ.pr, FourierJ.ech, chr]
end GlobalTheory.Phase
