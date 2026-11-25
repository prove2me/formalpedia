-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Lat.patch_of_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:36:24.704325+00:00
-- url     : https://prove2.me/submissions/9698a474-6fb2-40ed-bfce-41a48691e5dd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_MemEigSpOfMemHtDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]
namespace GlobalTheory.CompanionTheory.Ar
namespace Lat
theorem _root_.solution (S : Finset ℕ) (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) {q : Cpt ξ} {p : ℕ} (hp : p ∈ S)
    (hq : InFibre ξ p q) (hu : ∀ p' ∈ S, InFibre ξ p' q → p' = p) : Lat.patch S L₀ Lp q = Lp p q := by
  simp only [Lat.patch]; rw [if_pos ⟨p, hp, hq⟩]
  refine le_antisymm (iInf₂_le_of_le p hp (iInf_le _ hq)) (le_iInf₂ fun p' hp' => le_iInf fun h => ?_)
  rw [hu p' hp' h]
end Lat
end GlobalTheory.CompanionTheory.Ar
