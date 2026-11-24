-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GramWedge.posSemidef_smul_gram_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:05:21.52417+00:00
-- url     : https://prove2.me/submissions/0facf1b0-f7a1-444e-9130-984de38a75d6

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativityInfinitePlaces
import Theorems.Thm_GlobalTheory_CompanionTheory_GramWedge_star_dotProduct_self
import Theorems.Thm_GlobalTheory_CompanionTheory_GramWedge_sum_norm_mulVec_sq_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.Rg.BcB.D1
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GramWedge
namespace GlobalTheory.CompanionTheory.GramWedge
theorem _root_.solution {ι ι' κ : Type} [Fintype ι] [Fintype ι'] [Fintype κ] [DecidableEq κ]
    (g : Matrix ι' ι ℂ) (A : Matrix ι κ ℂ) :
    (((((Fintype.card ι * Fintype.card ι' : ℝ) * sz g ^ 2 : ℝ) : ℂ) • (Aᴴ * A)) -
      (g * A)ᴴ * (g * A)).PosSemidef := by
  set c : ℝ := (Fintype.card ι * Fintype.card ι' : ℝ) * sz g ^ 2 with hc
  have hG : (Aᴴ * A).IsHermitian := isHermitian_conjTranspose_mul_self A
  have hH : ((g * A)ᴴ * (g * A)).IsHermitian := isHermitian_conjTranspose_mul_self _
  refine PosSemidef.of_dotProduct_mulVec_nonneg
    ((hG.smul (show star (c : ℂ) = c from Complex.conj_ofReal c)).sub hH) fun x => ?_
  have e : ∀ {α : Type} [Fintype α] (B : Matrix α κ ℂ),
      star x ⬝ᵥ ((Bᴴ * B) *ᵥ x) = star (B *ᵥ x) ⬝ᵥ (B *ᵥ x) := by
    intro α _ B
    rw [← mulVec_mulVec, star_mulVec, dotProduct_mulVec]
  have e1 := e A
  have e2 : star x ⬝ᵥ (((g * A)ᴴ * (g * A)) *ᵥ x) = star (g *ᵥ (A *ᵥ x)) ⬝ᵥ (g *ᵥ (A *ᵥ x)) := by
    rw [e (g * A), mulVec_mulVec]
  rw [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, e1, e2, star_dotProduct_self,
    star_dotProduct_self, smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
  exact Complex.zero_le_real.2 (sub_nonneg.2 (sum_norm_mulVec_sq_le g (A *ᵥ x)))
end GlobalTheory.CompanionTheory.GramWedge
