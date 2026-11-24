-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalDens.inv_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:49:45.176092+00:00
-- url     : https://prove2.me/submissions/35f10694-aef7-4ad3-aa21-24b295c682bc

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardPreimageHom
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_red_one
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_red_pow_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalDens
open PositivityTheory.PfSWUS.Loc
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.LocalDens
theorem _root_.solution (ϖ : R) (k : ℕ) {a : ℕ} (N : Matrix (Fin a) (Fin a) R) :
    ∃ h, red ϖ k ((1 + ϖ • N) * h) = 1 ∧ red ϖ k (h * (1 + ϖ • N)) = 1 := by
  refine ⟨∑ i ∈ Finset.range k, (ϖ • (-N)) ^ i, ?_, ?_⟩
  · have h1 : (1 + ϖ • N) = 1 - ϖ • (-N) := by simp
    rw [h1, mul_neg_geom_sum, smul_pow]
    have : (1 - ϖ ^ k • (-N) ^ k : Matrix (Fin a) (Fin a) R) = 1 + ϖ ^ (k + 0) • (-(-N) ^ k) := by
      simp [sub_eq_add_neg]
    rw [this, red_add, red_pow_smul, red_one, add_zero]
  · have h1 : (1 + ϖ • N) = 1 - ϖ • (-N) := by simp
    rw [h1, geom_sum_mul_neg, smul_pow]
    have : (1 - ϖ ^ k • (-N) ^ k : Matrix (Fin a) (Fin a) R) = 1 + ϖ ^ (k + 0) • (-(-N) ^ k) := by
      simp [sub_eq_add_neg]
    rw [this, red_add, red_pow_smul, red_one, add_zero]
end GlobalTheory.CompanionTheory.LocalDens
