-- Prove2me | solution 1 for GlobalTheory.EtIsom.vec_li
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:17:21.216052+00:00
-- url     : https://prove2.me/submissions/f484b080-8765-409a-9eef-14d086889d30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockInvariantsIffIsometry
import Theorems.Thm_GlobalTheory_EtIsom_herm_gram
import Theorems.Thm_GlobalTheory_EtIsom_mom_all
import Theorems.Thm_GlobalTheory_EtIsom_detH

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
theorem _root_.solution (hG : A.IsGen τ p) {lam : F} {a : A.K} (ha : IsUnit a) {X : Hn r F E}
    (hX : HasInv X (A.invK τ p lam a)) : LinearIndependent E (fun i : Fin r => X.1.1 ^ (i : ℕ) *ᵥ X.2.1) := by
  have hAh : X.1.1.conjTranspose = X.1.1 := by rw [← Matrix.star_eq_conjTranspose]; exact X.1.2
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hdet : ((algebraMap F E).mapMatrix
      (Matrix.of fun i k : Fin r => Algebra.trace F A.K (τ ^ ((i : ℕ) + (k : ℕ)) * a))).det ≠ 0 := by
    rw [← RingHom.map_det]
    exact (map_ne_zero _).mpr (detH A hG ha)
  have h0 : (algebraMap F E).mapMatrix
      (Matrix.of fun i k : Fin r => Algebra.trace F A.K (τ ^ ((i : ℕ) + (k : ℕ)) * a)) *ᵥ g = 0 := by
    funext k
    have := congrArg (fun v => star (X.1.1 ^ (k : ℕ) *ᵥ X.2.1) ⬝ᵥ v) hg
    simp only [dotProduct_sum, dotProduct_smul, herm_gram _ hAh, mom_all A hG hX, dotProduct_zero,
      smul_eq_mul] at this
    simpa [Matrix.mulVec, dotProduct, mul_comm] using this
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet h0)
end GlobalTheory.EtIsom
