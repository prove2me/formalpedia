-- Prove2me | solution 1 for OAI.ReverseLogKodaira.SmoothProjectiveVariety.exists_relative_log_chart
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:39:46.030976+00:00
-- url     : https://prove2.me/submissions/26eef142-0411-4a4c-bd73-4d7faf5fbb4a

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/SmoothCharts.lean:L200-L245
-- (upload_full_project.md Phase 4): solution for node OAI.ReverseLogKodaira.SmoothProjectiveVariety.exists_relative_log_chart. The node keeps its source
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
import Theorems.Thm_OAI_ReverseLogKodaira_RelativeCharts_exists_standard_chart_over_smooth_open
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

lemma smooth_dimension_restrict_le {X Y : Scheme} (f : X ⟶ Y) (n : ℕ)
    (U V : Y.Opens) (h : U ≤ V) [SmoothOfRelativeDimension n (f ∣_ V)] :
    SmoothOfRelativeDimension n (f ∣_ U) := by
  have ho : IsPullback (X.homOfLE (f.preimage_mono h) ≫ (f ⁻¹ᵁ V).ι)
      (f ∣_ U) f (Y.homOfLE h ≫ V.ι) := by
    simpa only [Scheme.homOfLE_ι] using (isPullback_morphismRestrict f U).flip
  have hs := ho.of_right (morphismRestrict_homOfLE f U V h).symm
    (isPullback_morphismRestrict f V).flip
  let := smoothOfRelativeDimension_isStableUnderBaseChange n
  exact MorphismProperty.of_isPullback hs (inferInstance : SmoothOfRelativeDimension n (f ∣_ V))

end ReverseLogKodaira.RelativeCharts

namespace ReverseLogKodaira.SmoothProjectiveVariety

 

theorem exists_relative_log_chart
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D)
    (U : Y.scheme.affineOpens) (hU : U.1 ≤ D.complement)
    (O : X.scheme.Opens) (x : X.scheme) (hx : x ∈ O) (hfx : f.hom x ∈ U.1) :
    ∃ (V : X.scheme.affineOpens), x ∈ V.1 ∧ V.1 ≤ O ∧
      ∃ (e : V.1 ≤ f.hom ⁻¹ᵁ U.1),
        RingHom.IsStandardSmoothOfRelativeDimension (X.dimension - Y.dimension)
          (f.hom.appLE U.1 V.1 e).hom ∧
        ∃ t : Γ(X.scheme, V.1), t ≠ 0 ∧ E.ideal.ideal V = Ideal.span {t} := by
  classical
  let Q := D.complement
  let P := f.hom ⁻¹ᵁ Q
  let : Nonempty P := ⟨⟨x, hU hfx⟩⟩
  let sP : P.toScheme ⟶ complexBase := P.ι ≫ X.structural
  let sQ : Q.toScheme ⟶ complexBase := Q.ι ≫ Y.structural
  let : SmoothOfRelativeDimension X.dimension sP := by
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + X.dimension) (P.ι ≫ X.structural))
  let : SmoothOfRelativeDimension Y.dimension sQ := by
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + Y.dimension) (Q.ι ≫ Y.structural))
  let : Smooth (f.hom ∣_ Q) := by
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using f.smooth
  have hw : (f.hom ∣_ Q) ≫ sQ = sP := by
    dsimp only [sP, sQ, P, Q]
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, f.over_base]
  have hr := (SmoothDimension.smooth_relative_dimension_subtraction
    sP sQ X.dimension Y.dimension (f.hom ∣_ Q) hw).2
  let := hr
  let := RelativeCharts.smooth_dimension_restrict_le f.hom
    (X.dimension - Y.dimension) U.1 Q hU
  obtain ⟨A, hxA, t, ht, hEt⟩ := E.union_cartier x
  obtain ⟨V, hxV, hVO, e, hsm⟩ :=
    RelativeCharts.exists_standard_chart_over_smooth_open f.hom (X.dimension - Y.dimension)
      U (O ⊓ A.1) x ⟨hx, hxA⟩ hfx
  have hVA : V.1 ≤ A.1 := fun z hz => (hVO hz).2
  let : Nonempty V.1 := ⟨⟨x, hxV⟩⟩
  let tV := X.scheme.presheaf.map (homOfLE hVA).op t
  refine ⟨V, hxV, fun z hz => (hVO hz).1, e, hsm, tV, ?_, ?_⟩
  · simpa only [map_zero] using
      ((map_injective_of_isIntegral X.scheme (homOfLE hVA)).ne ht)
  · change E.ideal.ideal A = Ideal.span {t} at hEt
    rw [← E.ideal.map_ideal (show V ≤ A from hVA), hEt, Ideal.map_span]
    simp only [Set.image_singleton]
    rfl

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothDimension

 

end ReverseLogKodaira.SmoothDimension

end

end OAI

-- ---- platform node ----
open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.SmoothProjectiveVariety
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem solution
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D)
    (U : Y.scheme.affineOpens) (hU : U.1 ≤ D.complement)
    (O : X.scheme.Opens) (x : X.scheme) (hx : x ∈ O) (hfx : f.hom x ∈ U.1) :
    ∃ (V : X.scheme.affineOpens), x ∈ V.1 ∧ V.1 ≤ O ∧
      ∃ (e : V.1 ≤ f.hom ⁻¹ᵁ U.1),
        RingHom.IsStandardSmoothOfRelativeDimension (X.dimension - Y.dimension)
          (f.hom.appLE U.1 V.1 e).hom ∧
        ∃ t : Γ(X.scheme, V.1), t ≠ 0 ∧ E.ideal.ideal V = Ideal.span {t} := by
  first
    | exact OAI.ReverseLogKodaira.SmoothProjectiveVariety.exists_relative_log_chart f U hU O x hx hfx
    | exact OAI.ReverseLogKodaira.SmoothProjectiveVariety.exists_relative_log_chart
    | (apply OAI.ReverseLogKodaira.SmoothProjectiveVariety.exists_relative_log_chart <;> assumption)
    | (intros; apply OAI.ReverseLogKodaira.SmoothProjectiveVariety.exists_relative_log_chart <;> assumption)
