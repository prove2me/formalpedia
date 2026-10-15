-- Prove2me | solution 1 for OAI.ReverseLogKodaira.SmoothDimension.smooth_fiber_dimension
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T03:07:51.519252+00:00
-- url     : https://prove2.me/submissions/a0a6ec0b-6acb-4385-ac12-30e957312090

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/SmoothCharts.lean:L253-L294
-- (upload_full_project.md Phase 4): solution for node OAI.ReverseLogKodaira.SmoothDimension.smooth_fiber_dimension. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Adjunction
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_BaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_RelativeCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Specialization
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LocalCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_FiberCharts
import Theorems.Thm_OAI_ReverseLogKodaira_SmoothDimension_smooth_relative_dimension_subtraction

-- ---- from OAI.AlgebraicGeometry.LogKodaira.SmoothCharts ----
namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.SmoothDimension

 

end ReverseLogKodaira.SmoothDimension

namespace ReverseLogKodaira.SmoothDimension

 

end ReverseLogKodaira.SmoothDimension

namespace ReverseLogKodaira.RelativeCharts

 

end ReverseLogKodaira.RelativeCharts

namespace ReverseLogKodaira.RelativeCharts

end ReverseLogKodaira.RelativeCharts

namespace ReverseLogKodaira.SmoothProjectiveVariety

 

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothDimension

 

theorem smooth_fiber_dimension {K : Type*} [Field K]
    {X Y T : Scheme} [Nonempty T]
    (sX : X ⟶ Spec (CommRingCat.of K)) (sY : Y ⟶ Spec (CommRingCat.of K))
    (a b : ℕ) [SmoothOfRelativeDimension a sX] [SmoothOfRelativeDimension b sY]
    (f : X ⟶ Y) (h : f ≫ sY = sX)
    (y : Spec (CommRingCat.of K) ⟶ Y) (i : T ⟶ X) (sT : T ⟶ Spec (CommRingCat.of K))
    (sq : IsPullback i sT f y) (U : Y.Opens) (hy : Set.range y ⊆ U)
    (hf : Smooth (f ∣_ U)) :
    b ≤ a ∧ SmoothOfRelativeDimension (a - b) sT := by
  classical
  let y' : Spec (CommRingCat.of K) ⟶ U := IsOpenImmersion.lift U.ι y (by simpa using hy)
  have hi : Set.range i ⊆ (f ⁻¹ᵁ U : Set X) := by
    rintro _ ⟨z, rfl⟩
    change f (i z) ∈ U
    rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]
    exact hy ⟨_, rfl⟩
  let i' : T ⟶ (f ⁻¹ᵁ U) := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι i (by simpa using hi)
  let : Nonempty (f ⁻¹ᵁ U) := ⟨i' (Classical.arbitrary T)⟩
  let sa : (f ⁻¹ᵁ U).toScheme ⟶ Spec (CommRingCat.of K) := (f ⁻¹ᵁ U).ι ≫ sX
  let sb : U.toScheme ⟶ Spec (CommRingCat.of K) := U.ι ≫ sY
  let : SmoothOfRelativeDimension a sa := by
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + a) ((f ⁻¹ᵁ U).ι ≫ sX))
  let : SmoothOfRelativeDimension b sb := by
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + b) (U.ι ≫ sY))
  let := hf
  have hab : f ∣_ U ≫ sb = sa := by
    dsimp only [sa, sb]
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, h]
  obtain ⟨hle, hr⟩ := smooth_relative_dimension_subtraction sa sb a b (f ∣_ U) hab
  refine ⟨hle, ?_⟩
  have hw : i' ≫ (f ∣_ U) = sT ≫ y' := by
    apply (cancel_mono U.ι).mp
    simp only [Category.assoc, y', IsOpenImmersion.lift_fac]
    rw [morphismRestrict_ι, ← Category.assoc]
    simp only [i', IsOpenImmersion.lift_fac, sq.w]
  have ho : IsPullback (i' ≫ (f ⁻¹ᵁ U).ι) sT f (y' ≫ U.ι) := by
    simpa only [i', y', IsOpenImmersion.lift_fac] using sq
  have hs := ho.of_right hw (isPullback_morphismRestrict f U).flip
  let := smoothOfRelativeDimension_isStableUnderBaseChange (a - b)
  exact MorphismProperty.of_isPullback hs hr

end ReverseLogKodaira.SmoothDimension

end

end OAI

-- ---- platform node ----
open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.SmoothDimension
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem solution {K : Type*} [Field K]
    {X Y T : Scheme} [Nonempty T]
    (sX : X ⟶ Spec (CommRingCat.of K)) (sY : Y ⟶ Spec (CommRingCat.of K))
    (a b : ℕ) [SmoothOfRelativeDimension a sX] [SmoothOfRelativeDimension b sY]
    (f : X ⟶ Y) (h : f ≫ sY = sX)
    (y : Spec (CommRingCat.of K) ⟶ Y) (i : T ⟶ X) (sT : T ⟶ Spec (CommRingCat.of K))
    (sq : IsPullback i sT f y) (U : Y.Opens) (hy : Set.range y ⊆ U)
    (hf : Smooth (f ∣_ U)) :
    b ≤ a ∧ SmoothOfRelativeDimension (a - b) sT := by
  first
    | exact OAI.ReverseLogKodaira.SmoothDimension.smooth_fiber_dimension sX sY a b f h y i sT sq U hy hf
    | exact OAI.ReverseLogKodaira.SmoothDimension.smooth_fiber_dimension
    | (apply OAI.ReverseLogKodaira.SmoothDimension.smooth_fiber_dimension <;> assumption)
    | (intros; apply OAI.ReverseLogKodaira.SmoothDimension.smooth_fiber_dimension <;> assumption)
