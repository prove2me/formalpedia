-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeInj.act_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:36:59.773097+00:00
-- url     : https://prove2.me/submissions/fcf02a0d-174c-421d-9d01-6477ca085615

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IrreducibleHomFixedVectors
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeInj_act_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeInj
variable {G : Type} [Group G]
namespace GlobalTheory.CompanionTheory.HeckeInj
theorem _root_.solution {V M : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ G V) (A : M →ₗ[ℂ] V) (h : G) (x : G →₀ M) :
    act ρ A (Finsupp.lmapDomain M ℂ (fun g => h * g) x) = ρ h (act ρ A x) := by
  have : act ρ A ∘ₗ Finsupp.lmapDomain M ℂ (fun g => h * g) = ρ h ∘ₗ act ρ A := by
    refine Finsupp.lhom_ext fun a b => ?_
    simp [act_single, Finsupp.mapDomain_single]
  exact LinearMap.congr_fun this x
end GlobalTheory.CompanionTheory.HeckeInj
