-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Giv.ResProj.evC_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:21:40.102494+00:00
-- url     : https://prove2.me/submissions/0dd3feb7-c381-45ca-92a6-ef5379676001

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
theorem _root_.solution (G : Fin M → MRing ι) (z : (Σ k, ι k) → ℂ) (F : MRing (joinIdx ι 𝔅)) :
    evC z (subst G F) = evC (joinVec z fun q => evC z (G q.2)) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [evC, subst]
  | add p q hp hq =>
    simp only [evC, map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p n hp =>
    simp only [evC, map_mul] at hp ⊢
    rw [hp]
    congr 1
    obtain ⟨k | ⟨⟩, i⟩ := n
    · simp [subst, joinVec]
    · simp [subst, joinVec, evC]
end GlobalTheory.CompanionTheory.Ar.Giv.ResProj
