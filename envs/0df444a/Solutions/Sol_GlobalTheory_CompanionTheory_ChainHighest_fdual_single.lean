-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ChainHighest.fdual_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:23:01.28711+00:00
-- url     : https://prove2.me/submissions/6108eed3-e14e-4785-ad92-b676329bf028

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistsCocycleOfMapToDegreeOneTerm
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ChainHighest
open CompanionTheory.D.DSIC
open Formalism.REAL (KHighest IsWeight)
open PI.UpqRep (lowK)
namespace GlobalTheory.CompanionTheory.ChainHighest
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {U : Type} [AddCommGroup U] [Module ℂ U]
    (EU : Fin n → Fin n → Module.End ℂ U) (g : Fin n → Fin n → Finset (NC ε) → Finset (NC ε) → ℝ)
    (hg : ∀ (c d : Fin n) (x : Ch ε U) (A : Finset (NC ε)), Gop ε c d x A = ∑ B, (g c d A B : ℂ) • x B)
    (a b : Fin n) (A B : Finset (NC ε)) (u : U) :
    Fdual ε EU a b (Pi.single A u) B =
      (Pi.single A (EU a b u) : Ch ε U) B - (g b a B A : ℂ) • u := by
  unfold Fdual
  rw [LinearMap.sub_apply, Pi.sub_apply, lift_apply, hg]
  congr 1
  · by_cases h : B = A
    · subst h; simp
    · simp [h]
  · rw [Finset.sum_eq_single A]
    · simp
    · intro C _ hC; simp [hC]
    · simp
end GlobalTheory.CompanionTheory.ChainHighest
