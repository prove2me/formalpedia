-- Prove2me | solution 1 for GlobalTheory.EtIsom.isom_to_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:43:15.619308+00:00
-- url     : https://prove2.me/submissions/340bf637-de15-4669-85a4-f2154d27966c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockInvariantsIffIsometry
import Theorems.Thm_GlobalTheory_EtIsom_trace_map
import Theorems.Thm_GlobalTheory_EtIsom_mat_mulVec
import Theorems.Thm_GlobalTheory_EtIsom_mat_pow_mulVec
import Theorems.Thm_GlobalTheory_EtIsom_mat_selfAdjoint
import Theorems.Thm_GlobalTheory_EtIsom_mat_charpoly
import Theorems.Thm_GlobalTheory_T_etaleHermitianPair_structure_facts


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
theorem _root_.solution (hG : A.IsGen τ p) (lam : F) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)) (hj : A.IsIsom x j) :
    ∃ Ax : selfAdjoint (Matrix (Fin r) (Fin r) E), (∀ z, j (algebraMap A.K A.L τ * z) = Ax.1 *ᵥ j z) ∧
      ∀ y, HasInv ((Ax, j y, lam) : Hn r F E) (A.invK τ p lam (x * A.NL y)) := by
  refine ⟨⟨mat A (τ := τ) j, mat_selfAdjoint A hj⟩, fun z => (mat_mulVec A j z).symm, fun y => ?_⟩
  unfold HasInv GlobalTheory.JR.inv Hn.toGl Inv.map Et.invK
  refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun i => ?_) rfl)
  · exact mat_charpoly A hG i
  · show star (j y) ⬝ᵥ (mat A (τ := τ) j ^ (i : ℕ) *ᵥ j y) =
      algebraMap F E (Algebra.trace F A.K (τ ^ (i : ℕ) * (x * A.NL y)))
    rw [mat_pow_mulVec, hj, ← trace_map A hG]
    congr 1
    rw [map_mul, map_mul, (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).1 y]
    ring
end GlobalTheory.EtIsom
