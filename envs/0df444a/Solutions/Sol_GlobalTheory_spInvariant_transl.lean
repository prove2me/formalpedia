-- Prove2me | solution 1 for GlobalTheory.spInvariant_transl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:20.675209+00:00
-- url     : https://prove2.me/submissions/f4dfd0f7-c455-4c42-bb49-5c24ddfd6ad5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FiniteAbsLeOneMulMemRange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spAct_spTransl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spTransl_mem_sp


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
theorem _root_.solution (hH : IsSpInvariant g H) {B : Matrix (Fin g) (Fin g) ℤ} (hB : B.IsSymm)
    {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g)) :
    H (τ + B.map (Int.cast : ℤ → ℂ)) = H τ := by
  rw [← spAct_spTransl]
  exact hH _ (spTransl_mem_sp hB) τ hτ
end GlobalTheory
