-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckCasSplit.reH_lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:59:26.914308+00:00
-- url     : https://prove2.me/submissions/ce68791a-514b-4658-a6d9-acdfed4e4016

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CasimirSplitting
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckCasSplit_hpk_herm
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckCasSplit_hpk_sq
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckCasSplit_flip_facts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckCasSplit
open Formalism.FourierDecayAlt.ThreeDimData CompanionTheory.D.Upq.Sm
open PI.UpqRep (InLieHpk)
variable {k r : ℕ}
namespace GlobalTheory.CompanionTheory.ZuckCasSplit
theorem _root_.solution (Y : Mx k r) : InLieHpk k r (reH k r Y) := by
  obtain ⟨h3, h4⟩ := flip_facts _ Y (hpk_herm k r) (hpk_sq k r)
  show (reH k r Y)ᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * reH k r Y = 0
  simp only [reH, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, h3, h4]
  have : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [this, ← smul_add]
  abel_nf
  simp
end GlobalTheory.CompanionTheory.ZuckCasSplit
