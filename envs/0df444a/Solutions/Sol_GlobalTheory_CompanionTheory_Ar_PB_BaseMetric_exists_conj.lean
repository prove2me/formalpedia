-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.BaseMetric.exists_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:52:58.038077+00:00
-- url     : https://prove2.me/submissions/81df012e-b43b-46e4-ba7b-6b69f6064935

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_GlueApplyOfNotInFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsetOfMemNhds
import Definitions.Def_Development_AutomorphicSpectrum_Statements_MetricStatements_ExistsFlagModelBaseMetric
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_conj_mem_mcPts

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
theorem _root_.solution (BM : BaseMetric M n) (x : BM.Rb.X) :
    ∃ x', SameOrbit (BM.Rb.lift x' x') fun q => starRingEnd ℂ (BM.Rb.lift x x q) :=
  BM.Rb.surj _ (conj_mem_mcPts (BM.Rb.mem x x (BM.Rb.mem_U x))) fun h => by simpa using h.2 1 trivial
end BaseMetric
end GlobalTheory.CompanionTheory.Ar.PB
