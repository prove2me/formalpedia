-- Prove2me | solution 1 for GlobalTheory.ThetaPow.posDef_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:02:28.462915+00:00
-- url     : https://prove2.me/submissions/335cd60c-f644-43e8-a688-c42b602dd9e7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasSumPolyDerivMulProdAddMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ThetaCharBlockDiagonal
import Theorems.Thm_GlobalTheory_ThetaPow_dotProduct_blocks
import Theorems.Thm_GlobalTheory_ThetaPow_mulVec_blocks
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
noncomputable section
open Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ThetaPow
variable {j g G : ℕ}
namespace GlobalTheory.ThetaPow
theorem _root_.solution (e : Fin j × Fin g ≃ Fin G) {M : Matrix (Fin g) (Fin g) ℝ} (hM : M.PosDef) :
    (Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
        M (e.symm p).2 (e.symm q).2 else 0 : Matrix (Fin G) (Fin G) ℝ).PosDef := by
  refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩
  · ext p q
    have h := hM.1.apply (e.symm p).2 (e.symm q).2
    simp only [conjTranspose_apply, of_apply, star_trivial] at h ⊢
    by_cases hpq : (e.symm p).1 = (e.symm q).1
    · rw [if_pos hpq, if_pos hpq.symm, h]
    · rw [if_neg hpq, if_neg (Ne.symm hpq)]
  · rw [dotProduct_blocks e]
    simp only [mulVec_blocks]
    obtain ⟨p, hp⟩ := Function.ne_iff.1 hx
    refine Finset.sum_pos' (fun i _ => ?_) ⟨(e.symm p).1, Finset.mem_univ _, ?_⟩
    · exact hM.posSemidef.dotProduct_mulVec_nonneg _
    · refine (posDef_iff_dotProduct_mulVec.1 hM).2 (x := fun k => x (e ((e.symm p).1, k))) ?_
      refine Function.ne_iff.2 ⟨(e.symm p).2, ?_⟩
      simpa using hp
end GlobalTheory.ThetaPow
