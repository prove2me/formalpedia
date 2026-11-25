-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckCasSplit.hpk_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:04:19.671612+00:00
-- url     : https://prove2.me/submissions/e1e55af6-359d-4cfb-ab07-0460b156500b

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CasimirSplitting
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckCasSplit_hpk_row

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
theorem _root_.solution (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := by
  ext i j
  obtain ⟨j₀, s, hs, h1, h2⟩ := hpk_row k r i
  simp only [Matrix.mul_apply, h1, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, h2,
    Matrix.one_apply]
  by_cases hij : i = j
  · simp [hij, hs]
  · simp [hij, Ne.symm hij]
end GlobalTheory.CompanionTheory.ZuckCasSplit
