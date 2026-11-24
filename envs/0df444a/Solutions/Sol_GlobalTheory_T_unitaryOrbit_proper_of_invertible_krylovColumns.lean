-- Prove2me | solution 1 for GlobalTheory.T.unitaryOrbit_proper_of_invertible_krylovColumns
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:25:58.095927+00:00
-- url     : https://prove2.me/submissions/cafaf631-5156-4fd9-a3ff-a299b2cf9b7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryOrbitProperOfInvertibleKrylovColumns
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryOrbitProperOfInvertibleKrylovColumnsStatement
import Theorems.Thm_GlobalTheory_JR_orbit_proper_of_columns


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Ω : Set (Inv r F)) (s : Inv r F → Hn r F E) (h : Inv r F → Matrix (Fin r) (Fin r) E), IsCompact Ω → ContinuousOn s Ω → ContinuousOn h Ω → (∀ a ∈ Ω, IsUnit (h a).det ∧ Bm (s a).toGl = h a) → ∀ C : Set (Hn r F E), IsCompact C → IsCompact {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C} := by
  first | exact @GlobalTheory.JR.orbit_proper_of_columns | exact GlobalTheory.JR.orbit_proper_of_columns | (intros; apply GlobalTheory.JR.orbit_proper_of_columns <;> assumption)
end _root_.GlobalTheory.T
