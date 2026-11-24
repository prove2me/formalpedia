-- Prove2me | solution 1 for GlobalTheory.EtIsom.cayley_hasInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:03:11.24735+00:00
-- url     : https://prove2.me/submissions/5af4f0d5-206a-4e3b-be69-357d6fd73183

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockInvariantsIffIsometry
import Theorems.Thm_GlobalTheory_EtIsom_cayley
import Theorems.Thm_GlobalTheory_EtIsom_hasInv_parts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.EtIsom
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}
namespace GlobalTheory.EtIsom
theorem _root_.solution {lam : F} {a : A.K} {X : Hn r F E} (hX : HasInv X (A.invK τ p lam a)) :
    X.1.1 ^ r + ∑ i : Fin r, algebraMap F E (p i) • X.1.1 ^ (i : ℕ) = 0 := by
  have h := cayley X.1.1
  simp only [(hasInv_parts A hX).1] at h
  exact h
end GlobalTheory.EtIsom
