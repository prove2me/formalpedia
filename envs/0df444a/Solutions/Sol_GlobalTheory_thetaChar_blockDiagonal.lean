-- Prove2me | solution 1 for GlobalTheory.thetaChar_blockDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:35:09.301114+00:00
-- url     : https://prove2.me/submissions/1b50d13d-c197-43ac-8ca6-b37cb4242c5f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasSumPolyDerivMulProdAddMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ThetaCharBlockDiagonal
import Theorems.Thm_GlobalTheory_ThetaPow_posDef_blocks
import Theorems.Thm_GlobalTheory_ThetaPow_thTerm_blocks
import Theorems.Thm_GlobalTheory_CanTh_hasSum_prod_thTerm
import Theorems.Thm_GlobalTheory_CanTh_mem_thetaDomain
import Theorems.Thm_GlobalTheory_CanTh_thetaChar_eq_tsum
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
open GlobalTheory
open ThetaPow
namespace GlobalTheory
theorem _root_.solution (j g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ) (G : ℕ)
    (e : Fin j × Fin g ≃ Fin G) (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) :
    let τ' : Matrix (Fin G) (Fin G) ℂ := Matrix.of fun p q =>
      if (e.symm p).1 = (e.symm q).1 then τ (e.symm p).2 (e.symm q).2 else 0
    τ'.IsSymm ∧ (τ'.map Complex.im).PosDef ∧ ∀ z : Fin G → ℂ,
      thetaChar τ' (fun p => (a (e.symm p).2 : ℂ)) (fun p => (b (e.symm p).2 : ℂ)) z =
        ∏ i : Fin j, thetaChar τ (fun k => (a k : ℂ)) (fun k => (b k : ℂ)) (fun k => z (e (i, k))) := by
  intro τ'
  refine ⟨?_, ?_, fun z => ?_⟩
  · ext p q
    simp only [τ', transpose_apply, of_apply]
    by_cases hpq : (e.symm p).1 = (e.symm q).1
    · rw [if_pos hpq, if_pos hpq.symm, hs.apply]
    · rw [if_neg hpq, if_neg (Ne.symm hpq)]
  · convert posDef_blocks e hp using 1
    ext p q
    simp only [τ', map_apply, of_apply]
    split_ifs <;> simp
  · rw [CanTh.thetaChar_eq_tsum τ' (fun p => a (e.symm p).2) (fun p => b (e.symm p).2) z]
    simp only [τ', thTerm_blocks]
    rw [(blockEquiv e).tsum_eq
      (fun m => ∏ i : Fin j, CanTh.thTerm τ a b (fun k => z (e (i, k))) (m i))]
    exact (CanTh.hasSum_prod_thTerm (τ := fun _ : Fin j => τ) (fun _ => CanTh.mem_thetaDomain hp)
      (fun _ => a) (fun _ => b) (fun i k => z (e (i, k)))).tsum_eq
end GlobalTheory
