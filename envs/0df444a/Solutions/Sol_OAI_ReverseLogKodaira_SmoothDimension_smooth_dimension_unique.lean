-- Prove2me | solution 1 for OAI.ReverseLogKodaira.SmoothDimension.smooth_dimension_unique
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:31:37.887585+00:00
-- url     : https://prove2.me/submissions/765b862b-f117-487e-a4e1-bd153869ed84

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/SmoothCharts.lean:L14-L64
-- (upload_full_project.md Phase 4): solution for node OAI.ReverseLogKodaira.SmoothDimension.smooth_dimension_unique. The node keeps its source
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

 

theorem smooth_dimension_unique {K : Type*} [Field K]
    (X : Scheme) [Nonempty X] (f : X ⟶ Spec (CommRingCat.of K)) (n m : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension m f] : n = m := by
  classical
  let x : X := Classical.arbitrary X
  have chart (d : ℕ) [SmoothOfRelativeDimension d f] :
      ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V) (e : V ≤ f ⁻¹ᵁ ⊤),
        RingHom.IsStandardSmoothOfRelativeDimension d (f.appLE ⊤ V e).hom := by
    obtain ⟨U, hU, V, hV, hx, e, hf⟩ :=
      SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
        (n := d) (f := f) x
    have hUt : U = ⊤ := by
      apply top_unique
      intro y _
      have ht := e hx
      change f x ∈ U at ht
      simpa only [Subsingleton.elim y (f x)] using ht
    subst U
    exact ⟨V, hV, hx, e, hf⟩
  obtain ⟨V, hV, hxV, eV, hn⟩ := chart n
  obtain ⟨W, hW, hxW, eW, hm⟩ := chart m
  obtain ⟨r, t, hrt, hxr⟩ := exists_basicOpen_le_affine_inter hV hW x ⟨hxV, hxW⟩
  have refine_chart (d : ℕ) (A : X.Opens) (hA : IsAffineOpen A)
      (eA : A ≤ f ⁻¹ᵁ ⊤)
      (hd : RingHom.IsStandardSmoothOfRelativeDimension d (f.appLE ⊤ A eA).hom)
      (a : Γ(X, A)) :
      RingHom.IsStandardSmoothOfRelativeDimension d
        (f.appLE ⊤ (X.basicOpen a) ((X.basicOpen_le a).trans eA)).hom := by
    let := hA.isLocalization_basicOpen a
    have hz := RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway
      (Rᵣ := Γ(X, X.basicOpen a)) a
    have hc := RingHom.IsStandardSmoothOfRelativeDimension.comp hz hd
    simpa only [Nat.zero_add, RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
      Scheme.Hom.appLE_map] using hc
  have hnr := refine_chart n V hV eV hn r
  have hmt := refine_chart m W hW eW hm t
  have hmr : RingHom.IsStandardSmoothOfRelativeDimension m
      (f.appLE ⊤ (X.basicOpen r) ((X.basicOpen_le r).trans eV)).hom := by
    exact (f.appLE_congr ((X.basicOpen_le r).trans eV) rfl hrt
      (fun {_ _} h => RingHom.IsStandardSmoothOfRelativeDimension m h.hom)).mpr hmt
  let : Nonempty (X.basicOpen r) := ⟨⟨x, hxr⟩⟩
  let := (f.appLE ⊤ (X.basicOpen r) ((X.basicOpen_le r).trans eV)).hom.toAlgebra
  let : Algebra.IsStandardSmoothOfRelativeDimension n
      Γ(Spec (CommRingCat.of K), ⊤) Γ(X, X.basicOpen r) := hnr
  let : Algebra.IsStandardSmoothOfRelativeDimension m
      Γ(Spec (CommRingCat.of K), ⊤) Γ(X, X.basicOpen r) := hmr
  have hnrank := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := Γ(Spec (CommRingCat.of K), ⊤)) (S := Γ(X, X.basicOpen r)) n
  have hmrank := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := Γ(Spec (CommRingCat.of K), ⊤)) (S := Γ(X, X.basicOpen r)) m
  exact_mod_cast hnrank.symm.trans hmrank

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

 

end ReverseLogKodaira.SmoothDimension

end

end OAI

-- ---- platform node ----
open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.SmoothDimension
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem solution {K : Type*} [Field K]
    (X : Scheme) [Nonempty X] (f : X ⟶ Spec (CommRingCat.of K)) (n m : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension m f] : n = m := by
  first
    | exact OAI.ReverseLogKodaira.SmoothDimension.smooth_dimension_unique X f n m
    | exact OAI.ReverseLogKodaira.SmoothDimension.smooth_dimension_unique
    | (apply OAI.ReverseLogKodaira.SmoothDimension.smooth_dimension_unique <;> assumption)
    | (intros; apply OAI.ReverseLogKodaira.SmoothDimension.smooth_dimension_unique <;> assumption)
