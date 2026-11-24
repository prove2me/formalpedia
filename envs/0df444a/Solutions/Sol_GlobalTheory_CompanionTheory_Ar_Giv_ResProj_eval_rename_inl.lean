-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Giv.ResProj.eval_rename_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:18:30.996996+00:00
-- url     : https://prove2.me/submissions/5c89f65e-0bc0-446d-b3fd-14e77a22fdc5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Proportional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MultihomogeneousNonvanishingOnJoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Giv
open GlobalTheory.CompanionTheory.Ar.Giv.ResProj
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
variable {M : ℕ}
local notation "𝔅" => (fun _ : Unit => Fin M)
namespace GlobalTheory.CompanionTheory.Ar.Giv.ResProj
theorem _root_.solution (z : (Σ k, joinIdx ι 𝔅 k) → ℂ) (f : MRing ι) :
    eval z (map (Int.castRingHom ℂ) (rename (joinInl ι 𝔅) f)) =
      eval (z ∘ joinInl ι 𝔅) (map (Int.castRingHom ℂ) f) := by
  rw [map_rename, eval_rename]
end GlobalTheory.CompanionTheory.Ar.Giv.ResProj
