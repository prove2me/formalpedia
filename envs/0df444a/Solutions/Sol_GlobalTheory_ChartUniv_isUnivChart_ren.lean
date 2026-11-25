-- Prove2me | solution 1 for GlobalTheory.ChartUniv.isUnivChart_ren
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:17:45.296282+00:00
-- url     : https://prove2.me/submissions/71b3d01f-7385-45b4-8826-ba901f472f52

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsUniversalChartOfFormalGroupChart
import Theorems.Thm_GlobalTheory_ChartUniv_jetZero_zR
import Theorems.Thm_GlobalTheory_ChartUniv_jetRen_zR
import Theorems.Thm_GlobalTheory_ChartUniv_univ_all
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetZero_zR
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
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChartUniv
open ReciprocityTheory.ChartRestriction.G.Chart
variable {R : Type} [CommRing R]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
namespace GlobalTheory.ChartUniv
theorem _root_.solution [IsLocalRing R] [Smooth G.hom] {κ : Type} {d : ℕ} (e : κ ≃ Fin d)
    (x : ∀ m, sp (R₀ := R) (JetR R κ m) ⟶ G)
    (ht : ∀ m, spMap (jetTruncR R κ m) ≫ x (m + 1) = x m)
    (h0 : ∀ m, spMap (jetZeroR R κ m) ≫ x m = 1)
    (hu : ∀ (κ' : Type) (m : ℕ) (y : sp (R₀ := R) (JetR R κ' m) ⟶ G), spMap (jetZeroR R κ' m) ≫ y = 1 →
      ∃! ψ : JetR R κ m →ₐ[R] JetR R κ' m, (∀ j, jetZeroR R κ' m (ψ (zR m j)) = 0) ∧ y = spMap ψ ≫ x m) :
    IsUnivChart G d (fun m => spMap (jetRen e m) ≫ x m) := by
  refine ⟨fun m => ?_, fun m => ?_, fun A _ _ aug m hA y hy => ?_⟩
  · have : (jetTruncR R (Fin d) m).comp (jetRen e (m + 1)) = (jetRen e m).comp (jetTruncR R κ m) :=
      jet_ext fun j => by
        rw [AlgHom.comp_apply, AlgHom.comp_apply, jetRen_zR]
        exact (jetRen_zR (R := R) e m j).symm
    show _ ≫ _ ≫ _ = _ ≫ _
    rw [← Category.assoc, spMap_comp, this, ← spMap_comp, Category.assoc, ht]
  · have : (jetZeroR R (Fin d) m).comp (jetRen e m) = (jetRen e 0).comp (jetZeroR R κ m) :=
      jet_ext fun j => by
        rw [AlgHom.comp_apply, AlgHom.comp_apply, jetRen_zR, jetZero_zR, jetZero_zR, map_zero]
    show _ ≫ _ ≫ _ = _
    rw [← Category.assoc, spMap_comp, this, ← spMap_comp, Category.assoc, h0, comp_one']
  · obtain ⟨ψ, ⟨h1, h2⟩, hψ⟩ := univ_all (x m) (h0 m) (fun κ' => hu κ' m) A aug hA y hy
    have e1 : (jetRen (R := R) e m).comp (jetRen e.symm m) = AlgHom.id R _ :=
      jet_ext fun j => by rw [AlgHom.comp_apply, jetRen_zR, jetRen_zR, e.apply_symm_apply]; rfl
    have e2 : (jetRen (R := R) e.symm m).comp (jetRen e m) = AlgHom.id R _ :=
      jet_ext fun j => by rw [AlgHom.comp_apply, jetRen_zR, jetRen_zR, e.symm_apply_apply]; rfl
    have a1 : (jetAug R κ m).comp (jetRen e.symm m) = jetAug R (Fin d) m :=
      jet_ext fun j => by rw [AlgHom.comp_apply, jetRen_zR, jetAug_zR, jetAug_zR]
    have a2 : (jetAug R (Fin d) m).comp (jetRen e m) = jetAug R κ m :=
      jet_ext fun j => by rw [AlgHom.comp_apply, jetRen_zR, jetAug_zR, jetAug_zR]
    refine ⟨ψ.comp (jetRen e.symm m), ⟨?_, ?_⟩, ?_⟩
    · rw [← AlgHom.comp_assoc, h1, a1]
    · show y = _ ≫ _ ≫ _
      rw [← Category.assoc, spMap_comp, AlgHom.comp_assoc, e2, AlgHom.comp_id]
      exact h2
    · rintro φ ⟨g1, g2⟩
      have : φ.comp (jetRen e m) = ψ := hψ _ ⟨by rw [← AlgHom.comp_assoc, g1, a2], by
        rw [← spMap_comp, Category.assoc]; exact g2⟩
      rw [← this, AlgHom.comp_assoc, e1, AlgHom.comp_id]
end GlobalTheory.ChartUniv
