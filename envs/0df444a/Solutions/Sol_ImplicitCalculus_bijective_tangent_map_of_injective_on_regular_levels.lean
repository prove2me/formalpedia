-- Prove2me | solution 1 for ImplicitCalculus.bijective_tangent_map_of_injective_on_regular_levels
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T16:10:58.436374+00:00
-- url     : https://prove2.me/submissions/a7e059d9-b468-4634-857a-a33b3b8cfc0f

import Definitions.Def_GrayStability_Basic
import Theorems.Thm_ImplicitCalculus_tangent_map_of_mapsTo_regular_level
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open GrayStability
open scoped ContDiff Topology

theorem solution {n c : ℕ} (F G : E n → E c)
    (hF : ContDiff ℝ ∞ F) (hG : Differentiable ℝ G)
    (f : E n → E n) (hf : Differentiable ℝ f)
    (hmap : Set.MapsTo f (levelSet F) (levelSet G))
    (y : E n) (hy : y ∈ levelSet F)
    (hDy : Function.Surjective (fderiv ℝ F y))
    (hDfy : Function.Surjective (fderiv ℝ G (f y)))
    (hinj : Set.InjOn (fderiv ℝ f y) (tangentSpace F y)) :
    Set.BijOn (fderiv ℝ f y) (tangentSpace F y) (tangentSpace G (f y)) := by
  have htan : Set.MapsTo (fderiv ℝ f y) (tangentSpace F y)
      (tangentSpace G (f y)) := by
    intro v hv
    exact ImplicitCalculus.tangent_map_of_mapsTo_regular_level
      F (fderiv ℝ F y) y v (hF.hasStrictFDerivAt (by simp)) hDy hv
      f G (hf y) (hG (f y))
      (Filter.Eventually.of_forall (fun z hz => by
        have hzM : z ∈ levelSet F := hz.trans hy
        exact (hmap hzM).trans (hmap hy).symm))
  let A := (fderiv ℝ F y).toLinearMap
  let B := (fderiv ℝ G (f y)).toLinearMap
  let L : A.ker →ₗ[ℝ] B.ker :=
    { toFun := fun v => ⟨fderiv ℝ f y v, htan v.property⟩
      map_add' := by intros; apply Subtype.ext; simp
      map_smul' := by intros; apply Subtype.ext; simp }
  have hdim : Module.finrank ℝ A.ker = Module.finrank ℝ B.ker := by
    have ha := A.finrank_range_add_finrank_ker
    have hb := B.finrank_range_add_finrank_ker
    have hra : A.range = ⊤ := LinearMap.range_eq_top.mpr hDy
    have hrb : B.range = ⊤ := LinearMap.range_eq_top.mpr hDfy
    rw [hra, finrank_top] at ha
    rw [hrb, finrank_top] at hb
    omega
  have hLi : Function.Injective L := by
    intro v w h
    apply Subtype.ext
    exact hinj v.property w.property (congrArg Subtype.val h)
  have hLs : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hLi
  refine ⟨htan, hinj, ?_⟩
  intro w hw
  obtain ⟨v, hv⟩ := hLs ⟨w, hw⟩
  exact ⟨v, v.property, congrArg Subtype.val hv⟩



