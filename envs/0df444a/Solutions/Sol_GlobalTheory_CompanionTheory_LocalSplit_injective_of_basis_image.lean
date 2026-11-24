-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalSplit.injective_of_basis_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:49:40.814577+00:00
-- url     : https://prove2.me/submissions/553c4ec1-6e33-49e9-885d-adbeb2de7415

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalFreeKernelSplitting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalSplit
namespace GlobalTheory.CompanionTheory.LocalSplit
theorem _root_.solution {k V U ι : Type} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup U] [Module k U] (b : Module.Basis ι k V) (g : V →ₗ[k] U)
    (h : LinearIndependent k (g ∘ b)) : Function.Injective g := by
  have hg : ⇑g = (Finsupp.linearCombination k (g ∘ b)) ∘ b.repr := by
    funext x
    conv_lhs => rw [← b.linearCombination_repr x]
    simp [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  rw [hg]
  exact (show Function.Injective (Finsupp.linearCombination k (g ∘ b)) from h).comp b.repr.injective
end GlobalTheory.CompanionTheory.LocalSplit
