-- Prove2me | solution 1 for GlobalTheory.rankOneCurve_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:47.089782+00:00
-- url     : https://prove2.me/submissions/08a1a5fb-98e6-43a1-a8a4-bf9069be0890

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FiniteAbsLeOneMulMemRange
import Theorems.Thm_GlobalTheory_rankOneCurve_map_im

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
variable {e : Fin g} {Z : Matrix (Fin g) (Fin g) ℂ} (hZs : Z.IsSymm) (hZe : ∀ i, Z i e = 0)
  (hZ : ∀ u : Fin g → ℝ, u e = 1 → ∀ y : ℝ, 0 < y →
    (Z.map Complex.im + y • vecMulVec u u).PosDef)
include hZs hZ
namespace GlobalTheory
theorem _root_.solution {R : Matrix (Fin g) (Fin g) ℝ} (hR : R.IsSymm) {u : Fin g → ℝ}
    (hu : u e = 1) {s : ℂ} (hs : 0 < s.im) : rankOneCurve Z R u s ∈ SiegelH (Fin g) := by
  refine ⟨?_, ?_⟩
  · ext i j
    simp only [rankOneCurve, transpose_apply, of_apply, hZs.apply i j, hR.apply i j]
    ring
  · rw [rankOneCurve_map_im]
    exact hZ u hu _ hs
end GlobalTheory
