-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.HodgeOver.refl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:42:29.597989+00:00
-- url     : https://prove2.me/submissions/d07d8a50-7a3d-49d2-b15b-7aa092e3c17d

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
namespace GlobalTheory.CompanionTheory.Ar.PB
namespace HodgeOver
theorem _root_.solution (A : HodgeCpt Y S x) : HodgeOver A A (𝟙 _) (RingHom.id Ω) (AddMonoidHom.id _) := by
  have e : dualMap (RingHom.id Ω) = RingHom.id _ := RingHom.ext fun a => TrivSqZeroExt.inl_fst_add_inr_snd_eq a
  refine ⟨?_, (Category.id_comp _).symm, rfl, ⟨fun _ _ => rfl, fun _ _ h => h⟩, fun w => ?_⟩
  · show A.ξ ≫ 𝟙 _ = Spec.map (𝟙 _) ≫ A.ξ
    rw [Spec.map_id, Category.id_comp, Category.comp_id]
  · rw [e]
    show _ = Spec.map (𝟙 _) ≫ _
    rw [Spec.map_id, Category.id_comp]
    rfl
end HodgeOver
end GlobalTheory.CompanionTheory.Ar.PB
