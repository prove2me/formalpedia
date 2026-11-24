-- Prove2me | solution 1 for GlobalTheory.BoxSection.exists_boxSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:49:48.32429+00:00
-- url     : https://prove2.me/submissions/14728a76-8023-40e1-9639-ffa5cf1d72c4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusProdSec
import Theorems.Thm_GlobalTheory_BoxSection_mem_nonzeroLocus_prodSec
import Theorems.Thm_GlobalTheory_BoxSection_exists_point

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.BoxSection
namespace GlobalTheory.BoxSection
theorem _root_.solution : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [GrpObj G] (j : ℕ) (p : Out.IsPowGrp G' G j) (L : LB G.left) (t : Fin j → L.Sec), L.IsLB → ∃ t' : (Out.boxLB L p.pr).Sec, (∀ (jj : Fin j → L.ι) (h : ∀ i, (Out.boxLB L p.pr).U jj ≤ (p.pr i).left ⁻¹ᵁ L.U (jj i)), t'.f jj = ∏ i, ((p.pr i).left.appLE _ _ (h i)).hom ((t i).f (jj i))) ∧ ∀ s : S, (∀ i, ∃ x : G.left, G.hom x = s ∧ x ∈ Out.nonzeroLocus (t i)) → ∃ y : G'.left, G'.hom y = s ∧ y ∈ Out.nonzeroLocus t' := by
  intro S G' G _ _ j p L t _
  refine ⟨prodSec L (fun i => (p.pr i).left) t, fun _ _ => rfl, fun s hs => ?_⟩
  choose x hx hx' using hs
  obtain ⟨y, hy, hy'⟩ := exists_point p.pr p.lim s x hx
  exact ⟨y, hy, mem_nonzeroLocus_prodSec L _ t y fun i => (hy' i).symm ▸ hx' i⟩
end GlobalTheory.BoxSection
