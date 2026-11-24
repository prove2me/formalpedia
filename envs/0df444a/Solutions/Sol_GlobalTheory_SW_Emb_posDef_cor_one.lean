-- Prove2me | solution 1 for GlobalTheory.SW.Emb.posDef_cor_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:26:10.451019+00:00
-- url     : https://prove2.me/submissions/a67ac64a-5a2a-47af-ad6e-01498c1977c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EmbeddingCompatibleWithWeilAndDenominator
import Theorems.Thm_GlobalTheory_SW_Emb_cor_conjTranspose
import Theorems.Thm_GlobalTheory_SW_Emb_cor_mulVec
import Theorems.Thm_GlobalTheory_SW_Emb_cons_dot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Emb
noncomputable section
variable {R S : Type} [CommRing R] [CommRing S] {N : ℕ}
namespace GlobalTheory.SW.Emb
theorem _root_.solution (A : Matrix (Fin N) (Fin N) ℂ) (h : A.PosDef) : (cor 1 A).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · rw [Matrix.IsHermitian, cor_conjTranspose, h.1.eq]
    simp
  · obtain ⟨a, v, rfl⟩ : ∃ (a : ℂ) (v : Fin N → ℂ), x = Fin.cons a v :=
      ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
    have hs : star (Fin.cons a v : Fin (N + 1) → ℂ) = Fin.cons (star a) (star v) := by
      ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
    rw [cor_mulVec, hs, cons_dot, one_mul]
    by_cases hv : v = 0
    · subst hv
      have ha : a ≠ 0 := by
        rintro rfl; exact hx (by ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp)
      simp only [Matrix.mulVec_zero, dotProduct_zero, add_zero]
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
      exact_mod_cast Complex.normSq_pos.mpr ha
    · have h1 : 0 ≤ star a * a := by
        rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]; exact_mod_cast Complex.normSq_nonneg a
      exact add_pos_of_nonneg_of_pos h1 (h.dotProduct_mulVec_pos hv)
end GlobalTheory.SW.Emb
