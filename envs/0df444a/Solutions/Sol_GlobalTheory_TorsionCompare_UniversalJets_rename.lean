-- Prove2me | solution 1 for GlobalTheory.TorsionCompare.UniversalJets.rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:33:03.464904+00:00
-- url     : https://prove2.me/submissions/051c11fa-127c-44c8-889f-d3e4fc68ea59

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_OriginChartMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NotIsUnitNatCastOfIsLocalHom

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
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionCompare
variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G]
namespace GlobalTheory.TorsionCompare
namespace UniversalJets
theorem _root_.solution {σ σ' : Type} (e : σ → σ') (e' : σ' → σ)
    (h : ∀ j, e' (e j) = j) (h' : ∀ j, e (e' j) = j)
    {x : ∀ m : ℕ, algOver R (JetR R σ m) ⟶ G} (hx : UniversalJets G x) :
    UniversalJets G (renameChart e x) := by
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨fun m => ?_, fun m => ?_, fun κ m y hy => ?_⟩
  · unfold renameChart
    have : (jetTruncR R σ' m).comp (jetRename e (m + 1)) =
        (jetRename e m).comp (jetTruncR R σ m) := jet_ext fun j => by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, jetRename_zR]
      exact (jetRename_zR e m j).symm
    rw [← Category.assoc, ← algOverHom_comp, this, algOverHom_comp, Category.assoc, h1]
  · unfold renameChart
    have : (jetZeroR R σ' m).comp (jetRename e m) =
        (jetRename e 0).comp (jetZeroR R σ m) := jet_ext fun j => by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, jetRename_zR]
      exact (jetRename_zR e 0 j).symm
    rw [← Category.assoc, ← algOverHom_comp, this, algOverHom_comp, Category.assoc, h2,
      ← Category.assoc, comp_toUnit]
  · obtain ⟨ψ, ⟨hψ0, hψ⟩, huniq⟩ := h3 κ m y hy
    refine ⟨ψ.comp (jetRename e' m), ⟨fun j => ?_, ?_⟩, ?_⟩
    · rw [AlgHom.comp_apply, jetRename_zR]; exact hψ0 _
    · unfold renameChart
      rw [← Category.assoc, ← algOverHom_comp, AlgHom.comp_assoc,
        jetRename_comp_of_inverse e e' h, AlgHom.comp_id]
      exact hψ
    · rintro χ ⟨hχ0, hχ⟩
      have : χ.comp (jetRename e m) = ψ := huniq _ ⟨fun j => by
        rw [AlgHom.comp_apply, jetRename_zR]; exact hχ0 _, by
        rw [algOverHom_comp, Category.assoc]; exact hχ⟩
      rw [← this, AlgHom.comp_assoc, jetRename_comp_of_inverse e' e h', AlgHom.comp_id]
end UniversalJets
end GlobalTheory.TorsionCompare
