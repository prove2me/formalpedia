-- Prove2me | solution 1 for GlobalTheory.ChartUniv.univ_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:04:35.340522+00:00
-- url     : https://prove2.me/submissions/d605a946-0cbf-4e33-aa48-d51177dbeed5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsUniversalChartOfFormalGroupChart
import Theorems.Thm_GlobalTheory_ChartUniv_jetAug_eq
import Theorems.Thm_GlobalTheory_ChartUniv_jetZero_zR
import Theorems.Thm_GlobalTheory_ChartUniv_aug_comp_iff
import Theorems.Thm_P2M_GlobalTheory_ChartUniv_spMap_id__b39f24ee8cf8
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetZero_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_univChartLoc
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
theorem _root_.solution [IsLocalRing R] [Smooth G.hom] {κ : Type} {m : ℕ} (x : sp (R₀ := R) (JetR R κ m) ⟶ G)
    (h0 : spMap (jetZeroR R κ m) ≫ x = 1)
    (hu : ∀ (κ' : Type) (y : sp (R₀ := R) (JetR R κ' m) ⟶ G), spMap (jetZeroR R κ' m) ≫ y = 1 →
      ∃! ψ : JetR R κ m →ₐ[R] JetR R κ' m, (∀ j, jetZeroR R κ' m (ψ (zR m j)) = 0) ∧ y = spMap ψ ≫ x)
    (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (hA : (RingHom.ker aug) ^ (m + 1) = ⊥)
    (y : sp (R₀ := R) A ⟶ G) (hy : spMap aug ≫ y = 1) :
    ∃! ψ : JetR R κ m →ₐ[R] A, aug.comp ψ = jetAug R κ m ∧ y = spMap ψ ≫ x := by
  obtain ⟨n, z, -, hz0, hzu⟩ := univChartLoc G
  have hxa : spMap (jetAug R κ m) ≫ x = 1 := by
    rw [jetAug_eq, ← spMap_comp, Category.assoc, h0, comp_one']
  obtain ⟨α, ⟨ha1, ha2⟩, -⟩ := hzu (JetR R κ m) (jetAug R κ m) m (ker_jetAug_pow κ m) x hxa
  obtain ⟨β, ⟨hb1, hb2⟩, -⟩ := hu (Fin n) (z m) (hz0 m)
  have hb1' := (aug_comp_iff β).2 hb1
  have hab : α.comp β = AlgHom.id R _ := by
    refine (hu κ x h0).unique ⟨(aug_comp_iff _).1 ?_, ?_⟩ ⟨fun j => jetZero_zR κ m j, ?_⟩
    · rw [← AlgHom.comp_assoc, ha1, hb1']
    · rw [← spMap_comp, Category.assoc, ← hb2, ← ha2]
    · rw [spMap_id', Category.id_comp]
  obtain ⟨ψ, ⟨h1, h2⟩, hψ⟩ := hzu A aug m hA y hy
  refine ⟨ψ.comp β, ⟨?_, ?_⟩, ?_⟩
  · rw [← AlgHom.comp_assoc, h1, hb1']
  · rw [← spMap_comp, Category.assoc, ← hb2, ← h2]
  · rintro φ ⟨g1, g2⟩
    have : φ.comp α = ψ := hψ _ ⟨by rw [← AlgHom.comp_assoc, g1, ha1], by
      rw [← spMap_comp, Category.assoc, ← ha2, ← g2]⟩
    rw [← this, AlgHom.comp_assoc, hab, AlgHom.comp_id]
end GlobalTheory.ChartUniv
