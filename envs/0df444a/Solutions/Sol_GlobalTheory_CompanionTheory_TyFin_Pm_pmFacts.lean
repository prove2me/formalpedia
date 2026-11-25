-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Pm.pmFacts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:24:13.736737+00:00
-- url     : https://prove2.me/submissions/421b16ab-13f0-4c2b-83cc-e667dfdd8522

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PermutationMatrixProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Pm_pm_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Pm_pm_conj
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Pm_cj_pm_parab
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Pm_blkGL_glEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.Pm
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.TyFin.Pm
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.PmFacts := by
  intro K _ _ _ ι _ _ σ
  refine ⟨pm_apply σ, pm_conj σ, fun s b => cj_pm_parab b σ, ?_⟩
  intro s b χ g
  unfold hcFun
  exact Finset.prod_congr rfl fun c _ => congrArg (χ c) (blkGL_glEquiv b σ c g
    (σ.subtypeEquiv (p := fun i => (b ∘ σ) i = c) (q := fun j => b j = c) fun _ => Iff.rfl) fun _ => rfl)
end GlobalTheory.CompanionTheory.TyFin.Pm
