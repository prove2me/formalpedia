-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.FlagTie.IsTotal.central
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:40:38.272457+00:00
-- url     : https://prove2.me/submissions/e37b9420-0d5a-45a3-ba2b-fe32de905be8

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
namespace GlobalTheory.CompanionTheory.Ar.PB
namespace FlagTie.IsTotal
theorem _root_.solution {M : FlagModel y (CMType H) (D.p + D.q) D.p} {𝔐 : HodgeCpt Y S M.x}
    {tie : FlagTie M 𝔐} {𝔐' : HodgeCpt Y S y} {Fl : 𝔐'.Flag} {xdeg : CMType H × Fin (D.p + D.q) → K → ℤ}
    {e : CMType H × Fin (D.p + D.q) → Φ} (ht : tie.IsTotal 𝔐' Fl xdeg e)
    {F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk} (hF : M.IsFrame F) (τ : CMType H) (k : Fin (D.p + D.q))
    (hk : M.blk (τ, k) = none) :
    algebraMap M.Ω Φ (detFac D.p k (F.T τ)) = algebraMap M.Ω Φ ((∏ k', M.x ⟨k', F.c k'⟩ ^ M.b (τ, k) k') * F.υ (τ, k)) *
      (∏ m ∈ Finset.Iic k, e (τ, m)) * detFac D.p k (M.g τ) := by
  have h1 := ht.2.2.2 τ k
  rw [hk, Option.elim_none] at h1
  rw [← hF.2.2.2 (τ, k) hk, map_mul]
  linear_combination (-algebraMap M.Ω Φ (detFac D.p k (F.T τ))) * h1
end FlagTie.IsTotal
end GlobalTheory.CompanionTheory.Ar.PB
