-- Prove2me | solution 1 for GlobalTheory.HilbFam.aut_perm_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:51:59.005402+00:00
-- url     : https://prove2.me/submissions/ece900b5-d8a7-4388-86eb-99ad2b953d96

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AutEmbInjective
import Theorems.Thm_GlobalTheory_HilbFam_autEmb_apply
import Theorems.Thm_GlobalTheory_HilbFam_autEmb_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam
namespace GlobalTheory.HilbFam
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (g : ℂ ≃+* ℂ),
    ∃ π : Equiv.Perm (Emb F), ∀ (i : Emb F) (y : F), g ((i y : ℝ) : ℂ) = ((π i y : ℝ) : ℂ) := by
  intro F _ _ _ g
  refine ⟨Equiv.ofBijective (autEmb g) (Finite.injective_iff_bijective.mp (autEmb_injective g)), ?_⟩
  intro i y
  exact (autEmb_apply g i y).symm
end GlobalTheory.HilbFam
