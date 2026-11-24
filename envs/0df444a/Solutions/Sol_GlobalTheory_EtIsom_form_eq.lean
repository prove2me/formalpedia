-- Prove2me | solution 1 for GlobalTheory.EtIsom.form_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:52:12.869385+00:00
-- url     : https://prove2.me/submissions/66896807-5558-49e0-8cb5-c6e43f470e13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockInvariantsIffIsometry
import Theorems.Thm_GlobalTheory_EtIsom_bL_apply
import Theorems.Thm_GlobalTheory_EtIsom_trace_map
import Theorems.Thm_GlobalTheory_EtIsom_star_smul_vec
import Theorems.Thm_GlobalTheory_EtIsom_star_smul_L
import Theorems.Thm_GlobalTheory_EtIsom_herm_gram
import Theorems.Thm_GlobalTheory_EtIsom_star_bL

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
theorem _root_.solution (hG : A.IsGen τ p) (a : A.K) (M : Matrix (Fin r) (Fin r) E) (hM : M.conjTranspose = M)
    (b : Fin r → E) (hmom : ∀ n : ℕ, star b ⬝ᵥ (M ^ n *ᵥ b) = algebraMap F E (Algebra.trace F A.K (τ ^ n * a)))
    (φ : A.L →ₗ[E] (Fin r → E)) (hφb : ∀ i, φ (bL A hG i) = M ^ (i : ℕ) *ᵥ b) (w w' : A.L) :
    star (φ w) ⬝ᵥ φ w' = Algebra.trace E A.L (algebraMap A.K A.L a * star w * w') := by
  rw [← (bL A hG).sum_repr w, ← (bL A hG).sum_repr w']
  simp only [map_sum, map_smul, star_sum, star_smul_vec, star_smul_L, hφb, sum_dotProduct, dotProduct_sum,
    smul_dotProduct, dotProduct_smul, Finset.mul_sum, Finset.sum_mul, smul_mul_assoc, mul_smul_comm, smul_eq_mul,
    herm_gram M hM, hmom, star_bL]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [bL_apply, bL_apply, ← map_mul, ← map_mul, trace_map A hG, pow_add]
  ring_nf
end GlobalTheory.EtIsom
