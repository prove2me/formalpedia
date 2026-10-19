-- Prove2me | solution 1 for OAI.PerfectMatchingPSD.main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:28:15.184488+00:00
-- url     : https://prove2.me/submissions/e66b4f47-c9e0-4f44-ae90-681d91069bf2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/Main.lean:L53-L61
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.PerfectMatchingPSD.main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_PerfectMatchingPSD_main) verbatim and is proved by it.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AdmissibleTables
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CutGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SequentialTests
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialInterpolation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixInterpolation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GoodCells
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellDecoder
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingConversion
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Padding
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Parameters
import Theorems.Thm_OAI_PerfectMatchingPSD_main_nat

-- ---- from OAI.Combinatorics.MatchingPSD.Main ----
namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing MatchingInterpolation Matrix Filter Asymptotics
open scoped BigOperators MatrixOrder

theorem main : MainClaim := by
  intro C _hC
  obtain ⟨n₀,hn₀,hmain⟩ := main_nat ⌈C⌉₊
  refine ⟨n₀,hn₀,?_⟩
  intro n hn heven
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hpow := Real.rpow_le_rpow_of_exponent_le hn1 (Nat.le_ceil C)
  rw [Real.rpow_natCast] at hpow
  exact hpow.trans_lt (hmain n hn heven)

end PerfectMatchingPSD

end OAI

-- ---- mission target ----
open OAI OAI.PerfectMatchingPSD
open MatchingSmoothing MatchingInterpolation Matrix Filter Asymptotics
open scoped BigOperators MatrixOrder

namespace OAI
namespace PerfectMatchingPSD
theorem _root_.solution : MainClaim := by
  first
    | exact OAI.PerfectMatchingPSD.main
    | (apply OAI.PerfectMatchingPSD.main <;> assumption)
    | (intros; apply OAI.PerfectMatchingPSD.main <;> assumption)
end PerfectMatchingPSD
end OAI
