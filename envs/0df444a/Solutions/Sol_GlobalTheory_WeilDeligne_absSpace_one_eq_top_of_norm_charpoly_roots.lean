-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.absSpace_one_eq_top_of_norm_charpoly_roots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:18:59.46295+00:00
-- url     : https://prove2.me/submissions/b90af01c-4f39-49f7-a905-8dda8ecde8b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_TemperedOfLpDimLeOneOfUnitEigenvalues
import Theorems.Thm_GlobalTheory_WeilDeligne_absSpace_eq_bot_of_norm_charpoly_roots

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.WeilDeligne
namespace GlobalTheory.WeilDeligne
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} (hs : f.IsSemisimple) (hf : ∀ α ∈ f.charpoly.roots, ‖α‖ = 1) :
    absSpace f 1 = ⊤ := by
  rw [eq_top_iff, ← hs.iSup_eigenspace_eq_top]
  refine iSup_le fun α => ?_
  by_cases hα : ‖α‖ = 1
  · exact le_iSup₂_of_le (f := fun (β : ℂ) (_ : ‖β‖ = 1) => f.eigenspace β) α hα le_rfl
  · have := absSpace_eq_bot_of_norm_charpoly_roots hf hα
    rw [eq_bot_iff] at this
    refine le_trans ?_ (bot_le : (⊥ : Submodule ℂ V) ≤ absSpace f 1)
    exact le_trans (le_iSup₂_of_le (f := fun (β : ℂ) (_ : ‖β‖ = ‖α‖) => f.eigenspace β) α rfl le_rfl) this
end GlobalTheory.WeilDeligne
