-- Prove2me | solution 1 for OAI.ReverseLogKodaira.RelativeCharts.exists_standard_chart_over_smooth_open
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:38:32.325868+00:00
-- url     : https://prove2.me/submissions/97509db1-1cff-401e-89b4-58d799ceff46

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/SmoothCharts.lean:L129-L177
-- (upload_full_project.md Phase 4): solution for node OAI.ReverseLogKodaira.RelativeCharts.exists_standard_chart_over_smooth_open. The node keeps its source
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

 

theorem exists_standard_chart_over_smooth_open
    {X Y : Scheme} (f : X ⟶ Y) (n : ℕ)
    (U : Y.affineOpens) [SmoothOfRelativeDimension n (f ∣_ U.1)] (V : X.Opens) (x : X) (hx : x ∈ V)
    (hfx : f x ∈ U.1) :
    ∃ (W : X.affineOpens), x ∈ W.1 ∧ W.1 ≤ V ∧
      ∃ (e : W.1 ≤ f ⁻¹ᵁ U.1),
        RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U.1 W.1 e).hom := by
  classical
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hx₀, hV₀le⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (V ⊓ f ⁻¹ᵁ U.1 : X.Opens) from ⟨hx, hfx⟩)
      (V ⊓ f ⁻¹ᵁ U.1).isOpen
  have e₀ : V₀ ≤ f ⁻¹ᵁ U.1 := fun z hz => (hV₀le hz).2
  let : IsAffine V₀ := hV₀
  have hres : SmoothOfRelativeDimension n (f.resLE U.1 V₀ e₀) := by
    unfold Scheme.Hom.resLE
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + n)
        (X.homOfLE e₀ ≫ f ∣_ U.1))
  have hlocal : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      (f.appLE U.1 V₀ e₀).hom := by
    apply ((RingHom.locally_respectsIso
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso).arrow_mk_iso_iff
        (arrowResLEAppIso f U.1 V₀ e₀)).mp
    exact (HasRingHomProperty.iff_of_isAffine
      (P := @SmoothOfRelativeDimension n)).mp hres
  obtain ⟨s, hs, hsm⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).mp hlocal
  let hprime := (hV₀.primeIdealOf ⟨x, hx₀⟩)
  obtain ⟨t, ht, htx⟩ : ∃ t ∈ s, t ∉ hprime.asIdeal := by
    by_contra! hh
    have hle : Ideal.span (s : Set Γ(X, V₀)) ≤ hprime.asIdeal :=
      Ideal.span_le.mpr hh
    rw [hs] at hle
    exact hprime.isPrime.ne_top (top_unique hle)
  have hxB : x ∈ X.basicOpen t := by
    have hm : hV₀.fromSpec (hV₀.primeIdealOf ⟨x, hx₀⟩) ∈ X.basicOpen t := by
      change hV₀.primeIdealOf ⟨x, hx₀⟩ ∈ hV₀.fromSpec ⁻¹ᵁ X.basicOpen t
      rw [hV₀.fromSpec_preimage_basicOpen]
      exact htx
    have he : hV₀.fromSpec (hV₀.primeIdealOf ⟨x, hx₀⟩) = x :=
      hV₀.fromSpec_primeIdealOf ⟨x, hx₀⟩
    exact he ▸ hm
  let e : X.basicOpen t ≤ f ⁻¹ᵁ U.1 := (X.basicOpen_le t).trans e₀
  refine ⟨⟨X.basicOpen t, hV₀.basicOpen t⟩, hxB,
    (X.basicOpen_le t).trans (fun z hz => (hV₀le hz).1), e, ?_⟩
  let := hV₀.isLocalization_basicOpen t
  have h := hsm t ht Γ(X, X.basicOpen t)
  convert h using 1
  exact congrArg CommRingCat.Hom.hom (f.appLE_map e₀ (homOfLE (X.basicOpen_le t)).op).symm

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
open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.RelativeCharts
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem solution
    {X Y : Scheme} (f : X ⟶ Y) (n : ℕ)
    (U : Y.affineOpens) [SmoothOfRelativeDimension n (f ∣_ U.1)] (V : X.Opens) (x : X) (hx : x ∈ V)
    (hfx : f x ∈ U.1) :
    ∃ (W : X.affineOpens), x ∈ W.1 ∧ W.1 ≤ V ∧
      ∃ (e : W.1 ≤ f ⁻¹ᵁ U.1),
        RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U.1 W.1 e).hom := by
  first
    | exact OAI.ReverseLogKodaira.RelativeCharts.exists_standard_chart_over_smooth_open f n U V x hx hfx
    | exact OAI.ReverseLogKodaira.RelativeCharts.exists_standard_chart_over_smooth_open
    | (apply OAI.ReverseLogKodaira.RelativeCharts.exists_standard_chart_over_smooth_open <;> assumption)
    | (intros; apply OAI.ReverseLogKodaira.RelativeCharts.exists_standard_chart_over_smooth_open <;> assumption)
