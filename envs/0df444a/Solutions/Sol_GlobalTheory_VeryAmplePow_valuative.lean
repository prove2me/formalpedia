-- Prove2me | solution 1 for GlobalTheory.VeryAmplePow.valuative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:11:44.174947+00:00
-- url     : https://prove2.me/submissions/e770487a-2ea3-4261-b67a-8b3e78beb66f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem
import Theorems.Thm_GlobalTheory_VeryAmplePow_isUnit_gs
import Theorems.Thm_GlobalTheory_VeryAmplePow_gs_appLE
import Theorems.Thm_GlobalTheory_VeryAmplePow_gs_appTop
import Theorems.Thm_GlobalTheory_VeryAmplePow_isUnit_iff_mem
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
open GlobalTheory GlobalTheory.VeryAmplePow
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
namespace GlobalTheory.VeryAmplePow
theorem _root_.solution {Y : Scheme.{0}} {M : LB Y} {I : Type} (s : I → LB.Sec M) (hcov : ⨆ i, nonzeroLocus (s i) = ⊤)
    (i : I) (ρ : I → Γ(Y, nonzeroLocus (s i)))
    (hρ : ∀ j (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (k : M.ι), r z ∈ nonzeroLocus (s i) → r z ∈ M.U k →
      gs r z _ ((s j).f k) = gs r z _ (ρ j) * gs r z _ ((s i).f k))
    (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (l : Spec (.of V) ⟶ Y) (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ l) ⁻¹ᵁ nonzeroLocus (s i))
    (H : ∀ j, ∃ a : Γ(Spec (.of V), ⊤), (Spec.map (CommRingCat.ofHom (algebraMap V K))).appTop.hom a =
        ((Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ l).appLE _ ⊤ h).hom (ρ j)) :
    ⊤ ≤ l ⁻¹ᵁ nonzeroLocus (s i) := by
  let q : Spec (.of K) ⟶ Spec (.of V) := Spec.map (CommRingCat.ofHom (algebraMap V K))
  let p : Spec (.of V) := IsLocalRing.closedPoint V
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show l p ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
  obtain ⟨c, hc⟩ := Opens.mem_iSup.1 hk
  have hc' : l p ∈ M.U c := Y.basicOpen_le _ hc
  have ht : ⊤ ≤ l ⁻¹ᵁ M.U c := (Scheme.preimage_eq_top_of_closedPoint_mem l hc').ge
  have inj : Function.Injective q.appTop.hom := by
    have e : q.appTop = (Scheme.ΓSpecIso (.of V)).hom ≫ CommRingCat.ofHom (algebraMap V K) ≫
        (Scheme.ΓSpecIso (.of K)).inv := by
      rw [← Scheme.ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
    rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.coe_comp, RingHom.coe_comp]
    exact ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).1.comp
      (IsFractionRing.injective V K)).comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of V)).hom).1
  obtain ⟨a, ha⟩ := H k
  replace ha : q.appTop.hom a = ((q ≫ l).appLE _ ⊤ h).hom (ρ k) := ha
  have e : (l.appLE _ ⊤ ht).hom ((s k).f c) = a * (l.appLE _ ⊤ ht).hom ((s i).f c) := by
    refine inj (fn_ext fun z _ => ?_)
    rw [map_mul, ha, gs_mul _ z ⊤ trivial, gs_appTop, gs_appTop, gs_appLE _ _ _ _ ⊤ _ trivial,
      gs_appLE _ _ _ _ ⊤ _ trivial, gs_appLE _ _ _ _ ⊤ _ trivial]
    simp only [Category.id_comp]
    exact hρ k _ (q ≫ l) z c (h trivial) (ht trivial)
  have e' := congrArg (gs (𝟙 _) p ⊤) e
  rw [gs_mul _ p ⊤ trivial, gs_appLE _ _ _ _ ⊤ _ trivial, gs_appLE _ _ _ _ ⊤ _ trivial, Category.id_comp] at e'
  have u := (isUnit_gs l p _ hc' _).2 hc
  rw [e'] at u
  exact (Scheme.preimage_eq_top_of_closedPoint_mem l
    ((isUnit_iff_mem (s i) l p hc').1 (isUnit_of_mul_isUnit_right u))).ge
end GlobalTheory.VeryAmplePow
