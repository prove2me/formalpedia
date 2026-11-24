-- Prove2me | solution 1 for GlobalTheory.EtIsom.mom_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:33:46.758534+00:00
-- url     : https://prove2.me/submissions/5be97601-8c5d-4b69-87d9-fc5111e74d57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockInvariantsIffIsometry
import Theorems.Thm_GlobalTheory_EtIsom_rec_eq
import Theorems.Thm_GlobalTheory_EtIsom_hasInv_parts
import Theorems.Thm_GlobalTheory_EtIsom_mat_rec
import Theorems.Thm_GlobalTheory_EtIsom_trace_rec
import Theorems.Thm_GlobalTheory_EtIsom_cayley_hasInv

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
theorem _root_.solution (hG : A.IsGen τ p) {lam : F} {a : A.K} {X : Hn r F E} (hX : HasInv X (A.invK τ p lam a)) (n : ℕ) :
    star X.2.1 ⬝ᵥ (X.1.1 ^ n *ᵥ X.2.1) = algebraMap F E (Algebra.trace F A.K (τ ^ n * a)) := by
  refine rec_eq (fun i => algebraMap F E (p i)) (fun n => star X.2.1 ⬝ᵥ (X.1.1 ^ n *ᵥ X.2.1))
    (fun n => algebraMap F E (Algebra.trace F A.K (τ ^ n * a))) (fun m => ?_) (trace_rec A hG a)
    (fun n hn => (hasInv_parts A hX).2 ⟨n, hn⟩) n
  rw [mat_rec _ _ (cayley_hasInv A hX), dotProduct_neg, dotProduct_sum]
  simp only [dotProduct_smul, smul_eq_mul]
end GlobalTheory.EtIsom
