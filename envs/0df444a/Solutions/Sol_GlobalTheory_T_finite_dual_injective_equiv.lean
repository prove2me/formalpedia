-- Prove2me | solution 1 for GlobalTheory.T.finite_dual_injective_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:09:33.620391+00:00
-- url     : https://prove2.me/submissions/5882c714-1dd9-41f5-ae7e-bebb415786f5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteDualInjectiveEquiv
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNormalised_a407f4592f87c8cd
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteDualInjectiveEquivStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_ZModDual_equiv_dual_of_injective_pair


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X] [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y], (∃ f : Y →ₗ[ZMod n] Module.Dual (ZMod n) X, Function.Injective f) → (∃ g : X →ₗ[ZMod n] Module.Dual (ZMod n) Y, Function.Injective g) → Nonempty (Y ≃ₗ[ZMod n] Module.Dual (ZMod n) X) ∧ Nat.card X = Nat.card Y := by
  first | exact @GlobalTheory.CompanionTheory.ZModDual.equiv_dual_of_injective_pair | exact GlobalTheory.CompanionTheory.ZModDual.equiv_dual_of_injective_pair | (intros; apply GlobalTheory.CompanionTheory.ZModDual.equiv_dual_of_injective_pair <;> assumption)
end _root_.GlobalTheory.T
