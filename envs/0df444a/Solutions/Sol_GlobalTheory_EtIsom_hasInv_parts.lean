-- Prove2me | solution 1 for GlobalTheory.EtIsom.hasInv_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:40:48.571831+00:00
-- url     : https://prove2.me/submissions/11497c00-d177-4ca8-ac02-ffc8feff8293

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockInvariantsIffIsometry

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
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}
namespace GlobalTheory.EtIsom
theorem _root_.solution {lam : F} {a : A.K} {X : Hn r F E} (hX : HasInv X (A.invK τ p lam a)) :
    (∀ i : Fin r, X.1.1.charpoly.coeff i = algebraMap F E (p i)) ∧
      ∀ i : Fin r, star X.2.1 ⬝ᵥ (X.1.1 ^ (i : ℕ) *ᵥ X.2.1) = algebraMap F E (Algebra.trace F A.K (τ ^ (i : ℕ) * a)) := by
  unfold HasInv GlobalTheory.JR.inv Hn.toGl Inv.map Et.invK at hX
  exact ⟨fun i => congrFun (congrArg Prod.fst hX) i, fun i => congrFun (congrArg (fun t => t.2.1) hX) i⟩
end GlobalTheory.EtIsom
