-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckCasSplit.flip_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:54:31.593922+00:00
-- url     : https://prove2.me/submissions/60fc40a1-4c82-4d44-9907-5ab507c92aad

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CasimirSplitting

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
theorem _root_.solution {n : ℕ} (Hm Y : Matrix (Fin n) (Fin n) ℂ) (h1 : Hmᴴ = Hm) (h2 : Hm * Hm = 1) :
    (Hm * Yᴴ * Hm)ᴴ * Hm = Hm * Y ∧ Hm * (Hm * Yᴴ * Hm) = Yᴴ * Hm := by
  constructor
  · simp only [Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, h2,
      Matrix.mul_one]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
end GlobalTheory.CompanionTheory.ZuckCasSplit
