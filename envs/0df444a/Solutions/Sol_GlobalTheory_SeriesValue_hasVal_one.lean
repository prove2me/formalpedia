-- Prove2me | solution 1 for GlobalTheory.SeriesValue.hasVal_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:21:42.877716+00:00
-- url     : https://prove2.me/submissions/878e2365-bfaa-4a44-b4c6-b6a4924d1392

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAlgHomValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLieCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueJet
import Theorems.Thm_GlobalTheory_SeriesValue_jetIn_zR
import Theorems.Thm_GlobalTheory_ChartBaseChange_chart_aug
import Theorems.Thm_GlobalTheory_JetSer_jetAlg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
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
theorem _root_.solution (hx : IsUnivChart G d x) (hu : MvPowerSeries.constantCoeff u = 1) :
    HasVal x u (1 : specV (algebraMap V O) A ⟶ G).left (1 : A) := by
  let _ : Algebra V A := ((algebraMap O A).comp (algebraMap V O)).toAlgebra
  have : IsScalarTower V O A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ψ : JetR O (Fin 1 × Fin d) 0 →ₐ[O] A := (Algebra.ofId O A).comp (jetAug O _ 0)
  have hψ : ∀ r, ψ (zR 0 r) = 0 := fun r => by
    show algebraMap O A (jetAug O _ 0 _) = 0
    rw [jetAug_zR, map_zero]
  refine ⟨0, 0, ψ, hψ, ?_, ?_⟩
  · have e : (ψ.restrictScalars V).comp (jetIn V d O 0) = (Algebra.ofId V A).comp (jetAug V _ 0) := jet_ext fun j => by
      show ψ (jetIn V d O 0 _) = algebraMap V A (jetAug V _ 0 _)
      rw [jetIn_zR, hψ, jetAug_zR, map_zero]
    have : spMap ((ψ.restrictScalars V).comp (jetIn V d O 0)) ≫ x 0 = 1 := by
      rw [e, ← spMap_comp, Category.assoc, chart_aug hx, MonObj.comp_one]
    exact (congrArg (·.left) this).symm
  · show 1 = algebraMap O A (jetAug O _ 0 _)
    rw [((jetAlg O _).2.1 0 u).2, hu, map_one]
end GlobalTheory.SeriesValue
