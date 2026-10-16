-- Prove2me | solution 1 for OAI.PermanentBorder.PolarAnalysis.simple_after_elimination
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:43:46.962408+00:00
-- url     : https://prove2.me/submissions/748cefd1-7f25-4a00-9471-47a48e778f26

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/KernelCharts.lean:L367-L386
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.PolarAnalysis.simple_after_elimination. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts

-- ---- from OAI.Algebra.Determinantal.KernelCharts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace PermanentBorder.Multigraded
open MvPolynomial
open scoped Classical

section Reindex
variable {ι σ E L V : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [Fintype E] [Fintype L] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

end Reindex
end PermanentBorder.Multigraded

namespace PermanentBorder.KernelBilinear
open MvPolynomial
open scoped Classical

variable {κ : Type} [Fintype κ] {n : ℕ}

end PermanentBorder.KernelBilinear

namespace PermanentBorder.Multigraded
open MvPolynomial
open scoped Classical
variable {σ : Type*} [DecidableEq σ]
end PermanentBorder.Multigraded

namespace PermanentBorder.KernelBilinear
open MvPolynomial
open scoped Classical
variable {κ : Type} [Fintype κ] {n : ℕ}
end PermanentBorder.KernelBilinear

namespace PermanentBorder.PolarAnalysis
open Filter
open scoped Topology

section Elimination
variable {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

 theorem isInvertible_of_injective (T : V →L[ℂ] V) (hT : Function.Injective T) :
    T.IsInvertible := by
  have hs : Function.Surjective T := LinearMap.injective_iff_surjective.mp hT
  obtain ⟨u, hu⟩ := ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hT,hs⟩
  exact ⟨ContinuousLinearEquiv.ofUnit u,hu⟩

theorem invertible_elimination (R : (V × W) →L[ℂ] V) (E : (V × W) →L[ℂ] W)
    (g : V →L[ℂ] W)
    (hE : (E ∘L ContinuousLinearMap.inr ℂ V W).IsInvertible)
    (he : E ∘L ((ContinuousLinearMap.id ℂ V).prod g) = 0)
    (hR : (R ∘L ((ContinuousLinearMap.id ℂ V).prod g)).IsInvertible) :
    (R.prod E).IsInvertible := by
  apply isInvertible_of_injective
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro z hz
  have hrz : R z = 0 := congrArg Prod.fst hz
  have hez : E z = 0 := congrArg Prod.snd hz
  have heg : E (z.1,g z.1) = 0 := by
    have h := congrArg (fun T : (V →L[ℂ] W) => T z.1) he
    simpa using h
  have hsub : E (0,z.2-g z.1) = 0 := by
    have hh : (0,z.2-g z.1) = z - (z.1,g z.1) := by ext <;> simp
    rw [hh, map_sub,hez,heg,sub_self]
  have hdw : z.2 = g z.1 := by
    have hm : (E ∘L ContinuousLinearMap.inr ℂ V W) (z.2-g z.1) =
        (E ∘L ContinuousLinearMap.inr ℂ V W) 0 := by
      rw [map_zero]
      exact hsub
    exact sub_eq_zero.mp (hE.bijective.injective hm)
  have hdx : z.1 = 0 := by
    apply hR.bijective.injective
    rw [map_zero]
    change R (z.1,g z.1) = 0
    simpa only [← hdw,Prod.eta] using hrz
  exact Prod.ext hdx (by simpa [hdx] using hdw)

theorem simple_after_elimination {R : V × W → V} {E : V × W → W}
    {g : V → W} {x : V}
    (hR : DifferentiableAt ℂ R (x,g x)) (hE : DifferentiableAt ℂ E (x,g x))
    (hg : DifferentiableAt ℂ g x)
    (he : (fun y => E (y,g y)) =ᶠ[𝓝 x] 0)
    (haux : (fderiv ℂ E (x,g x) ∘L ContinuousLinearMap.inr ℂ V W).IsInvertible)
    (hs : (fderiv ℂ (fun y => R (y,g y)) x).IsInvertible) :
    (fderiv ℂ (fun z => (R z,E z)) (x,g x)).IsInvertible := by
  let graph := (ContinuousLinearMap.id ℂ V).prod (fderiv ℂ g x)
  have hgraph : HasFDerivAt (fun y => (y,g y)) graph x :=
    (hasFDerivAt_id x).prodMk hg.hasFDerivAt
  have he' : fderiv ℂ E (x,g x) ∘L graph = 0 := by
    have hd := hE.hasFDerivAt.comp x hgraph
    have hz := (hasFDerivAt_const (𝕜 := ℂ) (0 : W) x).congr_of_eventuallyEq he
    exact hd.unique hz
  have hr' : (fderiv ℂ R (x,g x) ∘L graph).IsInvertible := by
    have hd := hR.hasFDerivAt.comp x hgraph
    rwa [← hd.fderiv]
  rw [(hR.hasFDerivAt.prodMk hE.hasFDerivAt).fderiv]
  exact invertible_elimination _ _ _ haux he' hr'
end Elimination
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Calculus
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

end Calculus
end PermanentBorder.PolarAnalysis.Schur

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.PolarAnalysis
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.PermanentBorder.PolarAnalysis.simple_after_elimination := @_root_.OAI.PermanentBorder.PolarAnalysis.simple_after_elimination
