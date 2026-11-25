-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.HodgeOver.map_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:58:45.988482+00:00
-- url     : https://prove2.me/submissions/e57687b2-fb9e-43b0-9393-142685dc8f6f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_GlueApplyOfNotInFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsetOfMemNhds
import Definitions.Def_Development_AutomorphicSpectrum_Statements_MetricStatements_ExistsFlagModelBaseMetric
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm


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
theorem _root_.solution (a : HodgeOver A' A h i j) (t : 𝓞 E) (w : A.Li) : j (A.ρ t w) = A'.ρ t (j w) := by
  refine A'.M.inj (Over.OverMorphism.ext (A'.m.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)))
  have h1 := a.2.2.2.2 (A.ρ t w)
  rw [A.act t w, Over.comp_left, Category.assoc, A.m.act] at h1
  refine h1.trans ?_
  rw [A'.act t (j w), Over.comp_left, Category.assoc, A'.m.act, ← Category.assoc (A'.M.pt (j w)).left]
  have h2 := a.2.2.2.2 w
  simp only [SABMap.φ] at h2
  rw [h2, Category.assoc, Category.assoc]
end HodgeOver
end GlobalTheory.CompanionTheory.Ar.PB
