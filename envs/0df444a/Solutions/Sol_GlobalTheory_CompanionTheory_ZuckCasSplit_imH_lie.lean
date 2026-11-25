-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckCasSplit.imH_lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:56:48.569704+00:00
-- url     : https://prove2.me/submissions/4c2c0ae2-dc00-46c5-99f1-464895593529

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
theorem _root_.solution (Y : Mx k r) : InLieHpk k r (imH k r Y) := by
  obtain ⟨h3, h4⟩ := flip_facts _ Y (hpk_herm k r) (hpk_sq k r)
  show (imH k r Y)ᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * imH k r Y = 0
  simp only [imH, sub_neg_eq_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, h3, h4]
  have : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
    simp
  rw [this, neg_smul, add_comm (Yᴴ * _), neg_add_cancel]
end GlobalTheory.CompanionTheory.ZuckCasSplit
