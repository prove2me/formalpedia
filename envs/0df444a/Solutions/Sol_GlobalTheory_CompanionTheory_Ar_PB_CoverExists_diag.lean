-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.CoverExists.diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:41:38.354819+00:00
-- url     : https://prove2.me/submissions/c15552e8-94a1-4956-a134-125359444ecc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_GlueApplyOfNotInFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsetOfMemNhds
import Definitions.Def_Development_AutomorphicSpectrum_Statements_MetricStatements_ExistsFlagModelBaseMetric
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_HodgeOver_refl
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_BasesOver_refl

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
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S S' : Finset ℕ}
  {Ω : Type} [Field Ω] [CharZero Ω] {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)]
  {x₀ : (Σ k, J₀ k) → Ω}
namespace GlobalTheory.CompanionTheory.Ar.PB
namespace CoverExists
theorem _root_.solution (hb : CoverExists) {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type}
    [Field Φ] {y : (Σ k, ι k) → Φ} {M : FlagModel y (CMType H) (D.p + D.q) D.p} {𝔐 : HodgeCpt Y S M.x}
    (tie : FlagTie M 𝔐) {d : ℕ} (hd : 𝔐.IsCover d) :
    ∃ Cv : FlagCover M M, Cv.v = id ∧ d * Cv.deg = d ∧ Cv.deg = 1 := by
  obtain ⟨Cv, -, h1, -, h2⟩ := hb E H D l Xo c Y S S K ι Φ y K ι Φ y M M 𝔐 𝔐 tie tie id id (RingHom.id _) (𝟙 _)
    (AddMonoidHom.id _) d d ⟨Function.injective_id, Function.injective_id, fun _ => rfl, fun q _ => ⟨q, rfl⟩⟩
    (fun _ => rfl) (HodgeOver.refl 𝔐) (BasesOver.refl _ _) hd hd
  refine ⟨Cv, h1, h2, ?_⟩
  rw [FlagCover.deg, h1]
  exact IntermediateField.relfinrank_self _
end CoverExists
end GlobalTheory.CompanionTheory.Ar.PB
