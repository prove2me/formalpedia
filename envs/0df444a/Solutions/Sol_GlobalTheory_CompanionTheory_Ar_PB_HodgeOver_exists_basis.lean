-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.HodgeOver.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:24:52.608052+00:00
-- url     : https://prove2.me/submissions/cf3793bf-9c71-4749-b544-e88218e395e1

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_GlueApplyOfNotInFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsetOfMemNhds
import Definitions.Def_Development_AutomorphicSpectrum_Statements_MetricStatements_ExistsFlagModelBaseMetric
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_HodgeOver_map_Vgen
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_nonempty_basis_Vgen
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
theorem _root_.solution (a : HodgeOver A' A h i j) (s : CMType H ⊕ CMType H)
    (b : Module.Basis (Fin (labelRk D s)) Ω (A.Vgen s)) :
    ∃ b' : Module.Basis (Fin (labelRk D s)) Ω' (A'.Vgen s), ∀ k, (b' k : A'.Li) = j (b k) := by
  obtain ⟨B⟩ := nonempty_basis_Vgen A' s
  have := Module.Finite.of_basis B
  have h1 := a.2.2.2.1.2 _ _ (b.linearIndependent.map' (A.Vgen s).subtype (Submodule.ker_subtype _))
  let w : Fin (labelRk D s) → A'.Vgen s := fun k => ⟨j (b k), a.map_Vgen s (b k).2⟩
  have h2 : LinearIndependent Ω' w := LinearIndependent.of_comp (A'.Vgen s).subtype h1
  exact ⟨basisOfLinearIndependentOfCardEqFinrank' w h2 (Module.finrank_eq_card_basis B).symm, fun k => by simp [w]⟩
end HodgeOver
end GlobalTheory.CompanionTheory.Ar.PB
