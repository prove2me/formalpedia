-- Prove2me | solution 1 for GlobalTheory.OrbCpt.orbit_cpt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:50:46.715725+00:00
-- url     : https://prove2.me/submissions/e1b9b43f-7c81-48ef-8ee5-53246b4ef7e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompactPreimageNormCentralizerHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjugatesSeparableMatrixCompactModCentralizer
import Theorems.Thm_GlobalTheory_OrbCpt_gl_orbit_cpt
import Theorems.Thm_GlobalTheory_OrbCpt_unitary_orbit_cpt
import Theorems.Thm_GlobalTheory_T_exists_compact_preimage_norm_centralizer_hermitian


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology Polynomial
noncomputable section
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.OrbCpt
namespace GlobalTheory.OrbCpt
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), (∀ (A₀ : Matrix (Fin r) (Fin r) F), A₀.charpoly.Separable → ∀ Z : Set (Matrix (Fin r) (Fin r) F), IsCompact Z → ∃ C : Set (GL (Fin r) F), IsCompact C ∧ ∀ g : GL (Fin r) F, (g : Matrix (Fin r) (Fin r) F) * A₀ * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) ∈ Z → ∃ c ∈ C, ∃ t : GL (Fin r) F, (t : Matrix (Fin r) (Fin r) F) * A₀ = A₀ * (t : Matrix (Fin r) (Fin r) F) ∧ g = c * t) ∧ ∀ (A₀ : Matrix (Fin r) (Fin r) E), A₀.IsHermitian → A₀.charpoly.Separable → ∀ Z : Set (Matrix (Fin r) (Fin r) E), IsCompact Z → ∃ C : Set (Matrix.unitaryGroup (Fin r) E), IsCompact C ∧ ∀ g : Matrix.unitaryGroup (Fin r) E, g.1 * A₀ * star g.1 ∈ Z → ∃ c ∈ C, ∃ t : Matrix.unitaryGroup (Fin r) E, t.1 * A₀ = A₀ * t.1 ∧ g = c * t := fun F E _ _ _ _ _ r =>
  ⟨fun A₀ hs Z hZ => gl_orbit_cpt A₀ hs Z hZ,
    fun A₀ hH hs Z hZ => unitary_orbit_cpt GlobalTheory.T.exists_compact_preimage_norm_centralizer_hermitian F E r A₀ hH hs Z hZ⟩
end GlobalTheory.OrbCpt
