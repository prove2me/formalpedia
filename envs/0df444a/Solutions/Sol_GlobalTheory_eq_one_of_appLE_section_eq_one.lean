-- Prove2me | solution 1 for GlobalTheory.eq_one_of_appLE_section_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:52:07.107963+00:00
-- url     : https://prove2.me/submissions/542e1272-dc98-4e6f-95cf-df6095c10c17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOneOfAppLESectionEqOne
import Theorems.Thm_GlobalTheory_RigidFunction_not_mem_basicOpen_fibre
import Theorems.Thm_GlobalTheory_isReduced_of_smooth_of_isReduced


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (X : Scheme.{0}) (P : Over X) (e : X ⟶ P.left), e ≫ P.hom = 𝟙 X → Smooth P.hom → GeometricallyIntegral P.hom → (IsReduced X ∧ genericPoints X ⊆ abLocus P) → (∀ (V : X.Opens) (u : Γ(P.left, P.hom ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (P.hom ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) := by
  intro X P e he hsm hgi hXg V u h hu
  obtain ⟨hred, hgen⟩ := hXg
  have := hsm
  have := hgi
  have : IsReduced P.left := GlobalTheory.isReduced_of_smooth_of_isReduced P.hom

  have h0 : (e.appLE _ V h).hom (u - 1) = 0 := by rw [map_sub, map_one, hu, sub_self]
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  by_contra hne
  rw [← TopologicalSpace.Opens.not_nonempty_iff_eq_bot, not_not] at hne

  have hopen := P.hom.isOpenMap _ (P.left.basicOpen (u - 1)).isOpen
  obtain ⟨x₀, ⟨y, hy, hyx₀⟩, hxg⟩ :=
    (dense_iff_closure_eq.mpr genericPoints.closure).inter_open_nonempty _ hopen (hne.image _)
  have hxV : x₀ ∈ V := by
    rw [← hyx₀]
    exact P.left.basicOpen_le _ hy
  have hxnot : e x₀ ∉ P.left.basicOpen (u - 1) := by
    intro hm
    have hmem : x₀ ∈ X.basicOpen ((e.appLE _ V h).hom (u - 1)) := by
      rw [Scheme.basicOpen_appLE]
      exact ⟨hxV, hm⟩
    rw [h0, Scheme.basicOpen_zero] at hmem
    exact hmem

  let K := AlgebraicClosure (X.residueField x₀)
  let t : Spec (.of K) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x₀) K)) ≫ X.fromSpecResidueField x₀
  have ht : ∀ z, t z = x₀ := by
    intro z
    have hz : t z ∈ Set.range (X.fromSpecResidueField x₀) := ⟨_, (Scheme.Hom.comp_apply _ _ z).symm⟩
    rwa [Scheme.range_fromSpecResidueField] at hz
  let pt : Spec (.of K) := IsLocalRing.closedPoint K
  have : IsProper (pullback.snd P.hom t) := hgen hxg K t ⟨pt, ht pt⟩
  have : IsIntegral (pullback P.hom t) :=
    hgi.geometrically_isIntegral t (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  have hpt : P.hom (e x₀) = t pt := by
    rw [ht, ← Scheme.Hom.comp_apply, he]
    rfl
  obtain ⟨a, ha, -⟩ := Scheme.Pullback.exists_preimage_pullback (e x₀) pt hpt
  obtain ⟨b, hb, -⟩ := Scheme.Pullback.exists_preimage_pullback y pt (hyx₀.trans (ht pt).symm)
  have hfib := RigidFunction.not_mem_basicOpen_fibre pullback.condition V
    (fun z => by rw [ht z]; exact hxV) (u - 1) a b (by rw [ha]; exact hxnot)
  rw [hb] at hfib
  exact hfib hy
end GlobalTheory
