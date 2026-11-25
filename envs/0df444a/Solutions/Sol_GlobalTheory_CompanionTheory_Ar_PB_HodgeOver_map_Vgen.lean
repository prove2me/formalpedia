-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.HodgeOver.map_Vgen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:13:13.756366+00:00
-- url     : https://prove2.me/submissions/6cecb37e-0549-418e-8e4a-b38abd1f4083

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_GlueApplyOfNotInFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsetOfMemNhds
import Definitions.Def_Development_AutomorphicSpectrum_Statements_MetricStatements_ExistsFlagModelBaseMetric
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_HodgeOver_map_act

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
namespace GlobalTheory.CompanionTheory.Ar.PB
namespace HodgeOver
theorem _root_.solution (a : HodgeOver A' A h i j) (s : CMType H ⊕ CMType H) {w : A.Li} (hw : w ∈ A.Vgen s) :
    j w ∈ A'.Vgen s := by
  refine (Submodule.mem_iInf _).2 fun t => ?_
  have h1 : A.ρ t w - A.emb s t • w = 0 := (Submodule.mem_iInf _).1 hw t
  show A'.ρ t (j w) - A'.emb s t • j w = 0
  have e : A'.emb s t = i (A.emb s t) := by
    show A'.cst _ = i (A.cst _)
    rw [a.2.2.1]; rfl
  rw [← a.map_act, e, ← a.2.2.2.1.1, ← map_sub, h1, map_zero]
end HodgeOver
end GlobalTheory.CompanionTheory.Ar.PB
