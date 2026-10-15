-- Prove2me | solution 1 for OAI.ReverseLogKodaira.SmoothDimension.smooth_relative_dimension_subtraction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:34:45.77898+00:00
-- url     : https://prove2.me/submissions/7e93b1c5-1f0f-489b-bd16-2a169d03a447

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/SmoothCharts.lean:L72-L121
-- (upload_full_project.md Phase 4): solution for node OAI.ReverseLogKodaira.SmoothDimension.smooth_relative_dimension_subtraction. The node keeps its source
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
import Theorems.Thm_OAI_ReverseLogKodaira_SmoothDimension_smooth_dimension_unique

-- ---- from OAI.AlgebraicGeometry.LogKodaira.SmoothCharts ----
namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.SmoothDimension

 

end ReverseLogKodaira.SmoothDimension

namespace ReverseLogKodaira.SmoothDimension

 

theorem smooth_relative_dimension_subtraction {K : Type*} [Field K]
    {X Y : Scheme} [Nonempty X] (sX : X ⟶ Spec (CommRingCat.of K))
    (sY : Y ⟶ Spec (CommRingCat.of K)) (a b : ℕ)
    [SmoothOfRelativeDimension a sX] [SmoothOfRelativeDimension b sY]
    (f : X ⟶ Y) [Smooth f] (h : f ≫ sY = sX) :
    b ≤ a ∧ SmoothOfRelativeDimension (a - b) f := by
  classical
  have chart (x : X) :
      ∃ (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V)
        (_ : x ∈ V) (e : V ≤ f ⁻¹ᵁ U),
        RingHom.IsStandardSmoothOfRelativeDimension (a - b) (f.appLE U V e).hom ∧ b ≤ a := by
    obtain ⟨U, hU, V, hV, hx, e, hf⟩ := Smooth.exists_isStandardSmooth f x
    let : Nonempty V := ⟨⟨x, hx⟩⟩
    let := (f.appLE U V e).hom.toAlgebra
    let : Algebra.IsStandardSmooth Γ(Y, U) Γ(X, V) := hf
    obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := hf.out
    let := hσ
    let := hι
    have hr : RingHom.IsStandardSmoothOfRelativeDimension P.dimension
        (f.appLE U V e).hom := P.isStandardSmoothOfRelativeDimension rfl
    let : IsAffine U := hU
    let : IsAffine V := hV
    have hrel : SmoothOfRelativeDimension P.dimension (f.resLE U V e) := by
      rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension P.dimension)]
      apply ((RingHom.locally_respectsIso RingHom.isStandardSmoothOfRelativeDimension_respectsIso).arrow_mk_iso_iff
        (arrowResLEAppIso f U V e)).mpr
      exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hr
    let := hrel
    let hsa : SmoothOfRelativeDimension a (V.ι ≫ sX) := by
      simpa only [Nat.zero_add] using
        (inferInstance : SmoothOfRelativeDimension (0 + a) (V.ι ≫ sX))
    let hsb : SmoothOfRelativeDimension b (U.ι ≫ sY) := by
      simpa only [Nat.zero_add] using
        (inferInstance : SmoothOfRelativeDimension (0 + b) (U.ι ≫ sY))
    have he : f.resLE U V e ≫ (U.ι ≫ sY) = V.ι ≫ sX := by
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, h]
    have hh : SmoothOfRelativeDimension (P.dimension + b) (V.ι ≫ sX) := by
      rw [← he]
      infer_instance
    let := hh
    have hd := smooth_dimension_unique V.toScheme (V.ι ≫ sX) a (P.dimension + b)
    have hdim : a - b = P.dimension := by omega
    exact ⟨U, hU, V, hV, hx, e, hdim ▸ hr, by omega⟩
  constructor
  · obtain ⟨U, hU, V, hV, hx, e, hr, hab⟩ := chart (Classical.arbitrary X)
    exact hab
  · constructor
    intro x
    obtain ⟨U, hU, V, hV, hx, e, hr, hab⟩ := chart x
    exact ⟨U, hU, V, hV, hx, e, hr⟩

end ReverseLogKodaira.SmoothDimension

namespace ReverseLogKodaira.RelativeCharts

 

end ReverseLogKodaira.RelativeCharts

namespace ReverseLogKodaira.RelativeCharts

end ReverseLogKodaira.RelativeCharts

namespace ReverseLogKodaira.SmoothProjectiveVariety

 

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothDimension

 

end ReverseLogKodaira.SmoothDimension

end

end OAI

-- ---- platform node ----
open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.SmoothDimension
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem solution {K : Type*} [Field K]
    {X Y : Scheme} [Nonempty X] (sX : X ⟶ Spec (CommRingCat.of K))
    (sY : Y ⟶ Spec (CommRingCat.of K)) (a b : ℕ)
    [SmoothOfRelativeDimension a sX] [SmoothOfRelativeDimension b sY]
    (f : X ⟶ Y) [Smooth f] (h : f ≫ sY = sX) :
    b ≤ a ∧ SmoothOfRelativeDimension (a - b) f := by
  first
    | exact OAI.ReverseLogKodaira.SmoothDimension.smooth_relative_dimension_subtraction sX sY a b f h
    | exact OAI.ReverseLogKodaira.SmoothDimension.smooth_relative_dimension_subtraction
    | (apply OAI.ReverseLogKodaira.SmoothDimension.smooth_relative_dimension_subtraction <;> assumption)
    | (intros; apply OAI.ReverseLogKodaira.SmoothDimension.smooth_relative_dimension_subtraction <;> assumption)
