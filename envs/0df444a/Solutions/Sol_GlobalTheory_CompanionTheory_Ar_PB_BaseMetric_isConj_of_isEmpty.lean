-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.BaseMetric.isConj_of_isEmpty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:48:01.477149+00:00
-- url     : https://prove2.me/submissions/2923fa90-2a2f-4563-9f93-09c9e5be41df

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_GlueApplyOfNotInFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsetOfMemNhds
import Definitions.Def_Development_AutomorphicSpectrum_Statements_MetricStatements_ExistsFlagModelBaseMetric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S S' S'' : Finset ℕ}
  {Ω Ω' Ω'' : Type} [Field Ω] [Field Ω'] [Field Ω''] {K K' K'' : Type} [Fintype K] [Fintype K'] [Fintype K'']
  {J : K → Type} {J' : K' → Type} {J'' : K'' → Type} {x : (Σ k, J k) → Ω} {x' : (Σ k, J' k) → Ω'}
  {x'' : (Σ k, J'' k) → Ω''}
variable {A' : HodgeCpt Y S' x'} {A : HodgeCpt Y S x} {h : A'.X ⟶ A.X} {i : Ω →+* Ω'} {j : A.Li →+ A'.Li}
variable {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
variable {Ψ : Type} {N j n : ℕ} {M : FlagModel y Ψ N j}
namespace GlobalTheory.CompanionTheory.Ar.PB
namespace BaseMetric
theorem _root_.solution (BM : BaseMetric M n) [IsEmpty (NonPluckerBlocks M.blk)]
    (h : ∀ p, IsConjInvariantH (BM.hom p)) : BM.IsConj := by
  refine ⟨fun x x' _ => ?_, fun p z _ _ _ _ => h p z⟩
  obtain rfl : x' = x := BM.Rb.inj _ _ (fun h => by simpa using h.2 1 trivial)
    ⟨fun _ => 1, fun _ => one_ne_zero, funext fun q => isEmptyElim q.1⟩
  exact ⟨Iff.rfl, rfl⟩
end BaseMetric
end GlobalTheory.CompanionTheory.Ar.PB
