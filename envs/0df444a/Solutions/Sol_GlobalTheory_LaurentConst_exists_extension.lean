-- Prove2me | solution 1 for GlobalTheory.LaurentConst.exists_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:40:03.476344+00:00
-- url     : https://prove2.me/submissions/3556168d-942a-476d-af51-a2762ce12182

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentConst
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {W Z : Scheme.{0}}
namespace GlobalTheory.LaurentConst
theorem _root_.solution {Y : Scheme.{0}} (p : Y ⟶ S) [UniversallyClosed p] {L : Type} [Field L]
    (s : Spec (.of L) ⟶ S) (x : Spec (.of (LaurentSeries L)) ⟶ Y)
    (hx : x ≫ p = Spec.map (CommRingCat.ofHom HahnSeries.C) ≫ s) :
    ∃ y : Spec (.of (PowerSeries L)) ⟶ Y,
      Spec.map (CommRingCat.ofHom (HahnSeries.ofPowerSeries ℤ L)) ≫ y = x ∧
      y ≫ p = Spec.map (CommRingCat.ofHom PowerSeries.C) ≫ s := by
  have h : ValuativeCriterion.Existence p := by
    have : UniversallyClosed p := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at this
    exact this.1
  obtain ⟨⟨l⟩⟩ := h
    { R := PowerSeries L, K := LaurentSeries L, i₁ := x
      i₂ := Spec.map (CommRingCat.ofHom PowerSeries.C) ≫ s
      commSq := ⟨by
        rw [hx, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
        congr 3
        exact RingHom.ext fun c ↦ (HahnSeries.ofPowerSeries_C c).symm⟩ }
  exact ⟨l.l, l.fac_left, l.fac_right⟩
end GlobalTheory.LaurentConst
