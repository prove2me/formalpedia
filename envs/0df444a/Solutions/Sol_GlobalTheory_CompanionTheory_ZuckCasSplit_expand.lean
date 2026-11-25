-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckCasSplit.expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:09.111599+00:00
-- url     : https://prove2.me/submissions/08c6790d-688b-449c-8e8b-1497c4a9dd65

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
set_option linter.unusedSectionVars false
variable {ι κ V : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.ZuckCasSplit
theorem _root_.solution {R α : Type} [Ring R] [Fintype α] (E A B : α → α → R) (Q : R)
    (h1 : ∑ a, ∑ b, A a b * B b a = Q) (h2 : ∑ a, ∑ b, B a b * A b a = Q) :
    ∑ a, ∑ b, (E a b + (A a b + B a b)) * (E b a + (A b a + B b a)) =
      ∑ a, ∑ b, (E a b + A a b) * (E b a + A b a) + ∑ a, ∑ b, (E a b + B a b) * (E b a + B b a)
        - ∑ a, ∑ b, E a b * E b a + (Q + Q) := by
  nth_rewrite 1 [← h1]
  rw [← h2]
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  abel
end GlobalTheory.CompanionTheory.ZuckCasSplit
