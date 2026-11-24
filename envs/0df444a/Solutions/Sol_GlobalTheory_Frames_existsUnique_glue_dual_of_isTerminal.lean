-- Prove2me | solution 1 for GlobalTheory.Frames.existsUnique_glue_dual_of_isTerminal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:51:00.334237+00:00
-- url     : https://prove2.me/submissions/f2f2147c-ea5e-4079-9bf6-d1f4220eb82e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueDual
import Theorems.Thm_GlobalTheory_Frames_spMap_dualMap_left
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_IsAway_lift
import Theorems.Thm_GlobalTheory_SqZero_agree_of_isAway
import Theorems.Thm_GlobalTheory_SqZero_away_ext
import Theorems.Thm_GlobalTheory_SqZero_away_glue
import Theorems.Thm_GlobalTheory_SqZero_dualMap_comp
import Theorems.Thm_GlobalTheory_SqZero_isAway_awayHom
import Theorems.Thm_GlobalTheory_SqZero_span_range_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
noncomputable section
open GlobalTheory GlobalTheory.Frames
namespace GlobalTheory.Frames
theorem _root_.solution {R : Type} [CommRing R] (hR : IsTerminal (Sp R)) {S : Type} [CommRing S]
    [Algebra R S] (Y : Scheme.{0}) {κ : Type} (h : κ → S) (hs : Ideal.span (Set.range h) = ⊤)
    (w : ∀ i, Sp (DualNumber (Localization.Away (h i))) ⟶ Y)
    (hw : ∀ i j (α : Localization.Away (h i) →+* Localization.Away (h i * h j))
      (β : Localization.Away (h j) →+* Localization.Away (h i * h j)),
      α.comp (algebraMap S (Localization.Away (h i))) = (algebraMap S (Localization.Away (h i * h j))) →
      β.comp (algebraMap S (Localization.Away (h j))) = (algebraMap S (Localization.Away (h i * h j))) →
      spMap (dualMap α) ≫ w i = spMap (dualMap β) ≫ w j) :
    ∃! w₀ : Sp (DualNumber S) ⟶ Y, ∀ i, spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w₀ = w i := by
  let X : Over (Spec (CommRingCat.of R)) := Over.mk (hR.from Y)
  let w' : ∀ i, Chart.sp (R₀ := R) (DualNumber (Localization.Away (h i))) ⟶ X := fun i =>
    Over.homMk (w i) (hR.hom_ext _ _)
  let q : ∀ k, S →ₐ[R] Localization.Away (h k) := fun k => SqZero.awayHom R (h k)
  have hq : ∀ k, SqZero.IsAway (q k) (h k) := fun k => SqZero.isAway_awayHom _
  let p : ∀ k l, S →ₐ[R] Localization.Away (h k * h l) := fun k l => SqZero.awayHom R (h k * h l)
  have hp : ∀ k l, SqZero.IsAway (p k l) (h k * h l) := fun k l => SqZero.isAway_awayHom _
  choose a ha using fun k l => (hq k).lift (p k l)
    (isUnit_of_mul_isUnit_left (by rw [← map_mul]; exact (hp k l).unit))
  choose b hb using fun k l => (hq l).lift (p k l)
    (isUnit_of_mul_isUnit_right (by rw [← map_mul]; exact (hp k l).unit))
  have hs' := SqZero.span_range_map hs (SqZero.inlS R S)
  obtain ⟨z, hz⟩ := SqZero.away_glue (X := X) hs' (fun k => SqZero.dualMap (q k))
    (fun k => (hq k).dualMap) w' (fun k l =>
      SqZero.agree_of_isAway (hq k).dualMap (hq l).dualMap (a₀ := SqZero.dualMap (a k l))
        (b₀ := SqZero.dualMap (b k l)) (by rw [SqZero.dualMap_comp, SqZero.dualMap_comp, ha, hb])
        (by rw [SqZero.dualMap_comp, ha, ← map_mul]; exact (hp k l).dualMap)
        (Over.OverMorphism.ext (by
          rw [Over.comp_left, Over.comp_left, spMap_dualMap_left, spMap_dualMap_left]
          exact hw k l _ _ (RingHom.ext fun x => AlgHom.congr_fun (ha k l) x)
            (RingHom.ext fun x => AlgHom.congr_fun (hb k l) x))))
  have hz' : ∀ i, spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ z.left = w i := fun i => by
    have : (Chart.spMap (SqZero.dualMap (q i))).left ≫ z.left = w i := congrArg CommaMorphism.left (hz i)
    rw [spMap_dualMap_left] at this
    exact this
  refine ⟨z.left, hz', fun y hy => ?_⟩
  let y' : Chart.sp (R₀ := R) (DualNumber S) ⟶ X := Over.homMk y (hR.hom_ext _ _)
  have : y' = z := SqZero.away_ext (X := X) hs' (fun k => SqZero.dualMap (q k))
    (fun k => (hq k).dualMap) fun k => Over.OverMorphism.ext (by
      rw [Over.comp_left, Over.comp_left, spMap_dualMap_left]
      exact (hy k).trans (hz' k).symm)
  exact congrArg CommaMorphism.left this
end GlobalTheory.Frames
