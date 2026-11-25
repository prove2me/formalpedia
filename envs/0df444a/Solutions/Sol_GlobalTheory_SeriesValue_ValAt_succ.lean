-- Prove2me | solution 1 for GlobalTheory.SeriesValue.ValAt.succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:17:05.126349+00:00
-- url     : https://prove2.me/submissions/29491a7a-f72b-48d0-8903-b541079c7b7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAlgHomValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLieCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueJet
import Theorems.Thm_GlobalTheory_SeriesValue_jetIn_zR
import Theorems.Thm_GlobalTheory_JetSer_jetAlg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SeriesValue
open ReciprocityTheory.ChartRestriction.G.Chart GlobalTheory.JetSer GlobalTheory.ChartBaseChange GlobalTheory.TorsionCharacter ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev addOf)
variable {V : Type} [CommRing V] {G : Over (Spec (CommRingCat.of V))} [GrpObj G] {d : ℕ}
variable {O : Type} [CommRing O] [Algebra V O]
variable {x : Fam G (Fin d)} {u : PS O 1 d} {A : Type} [CommRing A] [Algebra O A]
namespace GlobalTheory.SeriesValue
namespace ValAt
theorem _root_.solution (hx : IsUnivChart G d x) {m : ℕ} {g : Spec (CommRingCat.of A) ⟶ G.left} {z : Fin d → A} {k : A}
    (h : ValAt x u m g z k) : ValAt x u (m + 1) g z k := by
  obtain ⟨ψ, h1, h2, h3⟩ := h
  refine ⟨ψ.comp (jetTruncR O _ m), fun q => h1 q, ?_, ?_⟩
  · have e : ((jetTruncR O (Fin 1 × Fin d) m).restrictScalars V).comp (jetIn V d O (m + 1)) =
        (jetIn V d O m).comp (jetTruncR V (Fin d) m) := jet_ext fun j => by
      show jetTruncR O _ m (jetIn V d O (m + 1) (zR _ j)) = jetIn V d O m (zR _ j)
      rw [jetIn_zR, jetIn_zR]
      rfl
    rw [h2, ← hx.1 m, Over.comp_left, ← Category.assoc, spMap_left, ← Spec.map_comp]
    refine congrArg (fun φ => Spec.map (CommRingCat.ofHom φ) ≫ (x (m + 1)).left) ?_
    exact RingHom.ext fun a => congrArg ψ (AlgHom.congr_fun e a).symm
  · rw [h3, AlgHom.comp_apply, ((jetAlg O _).2.1 m u).1]
end ValAt
end GlobalTheory.SeriesValue
