-- Prove2me | solution 1 for GlobalTheory.EndDivisible.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:26:23.646493+00:00
-- url     : https://prove2.me/submissions/39f35751-8121-415e-85e7-e42dcfed6dc8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfLocalOnBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeOfSumEqZero
import Theorems.Thm_GlobalTheory_EndDivisible_gs_appLE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.EndDivisible
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic TopologicalSpace
namespace GlobalTheory.EndDivisible
theorem _root_.solution {X W Y S : Scheme.{0}} [IsIntegral X] [Y.IsSeparated] [IsAffine S] (f : X ⟶ W)
    (w : W ⟶ Y) (g : X ⟶ S) (hS : IsField Γ(S, ⊤)) (D : W.Opens) (hD : IsAffineOpen D) (z : X) (hz : f z ∈ D)
    (h : ∀ a : Γ(W, D), ∃ c : Γ(S, ⊤), gs g z ⊤ c = gs f z D a) : ∃ p : S ⟶ Y, f ≫ w = g ≫ p := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVD⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show z ∈ ((f ⁻¹ᵁ D : X.Opens) : Set X) from hz)
      (f ⁻¹ᵁ D).isOpen
  have hVD' : V ≤ f ⁻¹ᵁ D := hVD
  have : Nonempty V := ⟨⟨z, hzV⟩⟩
  let κ := (g.appLE ⊤ V le_top).hom
  let φ := (f.appLE D V hVD').hom
  have hκ : Function.Injective κ := by
    letI := hS.toField
    exact κ.injective
  have hr : ∀ a, φ a ∈ κ.range := fun a => by
    obtain ⟨c, hc⟩ := h a
    refine ⟨c, germ_injective_of_isIntegral X z hzV ?_⟩
    refine (gs_eq (𝟙 X) z V hzV _).symm.trans (Eq.trans ?_ (gs_eq (𝟙 X) z V hzV _))
    refine (gs_appLE (𝟙 X) g z ⊤ V le_top hzV c).trans
      (Eq.trans ?_ (gs_appLE (𝟙 X) f z D V hVD' hzV a).symm)
    rw [Category.id_comp, Category.id_comp, hc]
  let e : Γ(S, ⊤) ≃+* κ.range := RingEquiv.ofBijective κ.rangeRestrict
    ⟨fun a b hab => hκ (congrArg Subtype.val hab), κ.rangeRestrict_surjective⟩
  let χ : Γ(W, D) ⟶ Γ(S, ⊤) := CommRingCat.ofHom (e.symm.toRingHom.comp (φ.codRestrict κ.range hr))
  have hχ : f.appLE D V hVD' = χ ≫ g.appLE ⊤ V le_top := by
    ext a
    exact (congrArg Subtype.val (e.apply_symm_apply ⟨φ a, hr a⟩)).symm
  refine ⟨S.isoSpec.hom ≫ Spec.map χ ≫ hD.fromSpec ≫ w, ?_⟩
  have : IsDominant hV.fromSpec := ⟨by
    rw [DenseRange, hV.range_fromSpec]
    exact V.isOpen.dense ⟨z, hzV⟩⟩
  refine ext_of_isDominant hV.fromSpec ?_
  rw [← Category.assoc, ← hD.SpecMap_appLE_fromSpec f hV hVD', ← Category.assoc hV.fromSpec,
    ← (isAffineOpen_top S).SpecMap_appLE_fromSpec g hV le_top, hχ, IsAffineOpen.fromSpec_top]
  simp
end GlobalTheory.EndDivisible
