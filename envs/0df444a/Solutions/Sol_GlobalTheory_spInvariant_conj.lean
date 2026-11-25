-- Prove2me | solution 1 for GlobalTheory.spInvariant_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:45:42.387345+00:00
-- url     : https://prove2.me/submissions/db4db85e-75d6-4317-9656-243024dfa475

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FiniteAbsLeOneMulMemRange
import Theorems.Thm_GlobalTheory_spAct_spDiag_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spDiag_mem_sp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology
open GlobalTheory
variable {g : ℕ} {H : Matrix (Fin g) (Fin g) ℂ → ℂ}
namespace GlobalTheory
theorem _root_.solution (hH : IsSpInvariant g H) (U : (Matrix (Fin g) (Fin g) ℤ)ˣ)
    {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g)) :
    H ((U : Matrix (Fin g) (Fin g) ℤ).map (Int.cast : ℤ → ℂ) * τ *
      ((U : Matrix (Fin g) (Fin g) ℤ).map (Int.cast : ℤ → ℂ))ᵀ) = H τ := by
  rw [← spAct_spDiag_eq]
  exact hH _ (spDiag_mem_sp U) τ hτ
end GlobalTheory
