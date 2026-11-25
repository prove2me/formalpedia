-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HopfSys.exists_unit_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:39:58.019049+00:00
-- url     : https://prove2.me/submissions/19511e66-bfbe-4529-8422-65e6aec62ad6

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechTripleRestrictCompositeInjectiveCohomologyFo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge Limits
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HopfSys
variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {P : Type} [SemilatticeInf P] (S : Sys A.left P)
  [IsSeparated A.hom]
namespace GlobalTheory.CompanionTheory.HopfSys
theorem _root_.solution (hR : IsField R) : ∃ a₀, η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤ := by
  letI := hR.toField
  haveI hu : Unique (𝟙_ (Over (Sp R))).left := inferInstanceAs (Unique (PrimeSpectrum R))
  have h1 : η[A].left default ∈ ⨆ a, (S.u a).1 := by rw [S.cover]; trivial
  obtain ⟨a₀, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 h1
  refine ⟨a₀, top_le_iff.1 fun x _ ↦ ?_⟩
  rw [Subsingleton.elim x default]
  exact ha
end GlobalTheory.CompanionTheory.HopfSys
