-- Prove2me | solution 1 for OAI.PermanentBorder.PolarAnalysis.simple_polarPair_unit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:49:41.288015+00:00
-- url     : https://prove2.me/submissions/7b983e9d-4f6c-4e44-9290-46a5d0dca503

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/SchurDifferentials.lean:L376-L409
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.PolarAnalysis.simple_polarPair_unit. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials

-- ---- from OAI.Algebra.Determinantal.SchurDifferentials ----
namespace OAI

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis
section Multiplier
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem simple_unit_multiplier_iff {T : E → (F →L[ℂ] F)} {g : E → F} {x : E}
    (hT : DifferentiableAt ℂ T x) (hg : DifferentiableAt ℂ g x)
    (hz : g x = 0) (hu : (T x).IsInvertible) :
    (fderiv ℂ (fun y => T y (g y)) x).IsInvertible ↔ (fderiv ℂ g x).IsInvertible := by
  rw [fderiv_clm_apply hT hg, hz, map_zero, add_zero]
  obtain ⟨e,he⟩ := hu
  rw [← he]
  exact ContinuousLinearMap.isInvertible_equiv_comp

 theorem triangularMultiplier_invertible (c : ℂ) (d : F) (hc : c ≠ 0) :
    (triangularMultiplier c d).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := triangularMultiplier c⁻¹ (-((c⁻¹*c⁻¹) • d)))
  · ext z <;> simp [smul_smul, hc]
  · ext z <;> simp [smul_smul, hc]

 theorem differentiableAt_triangularMultiplier {c : E → ℂ} {d : E → F} {x : E}
    (hc : DifferentiableAt ℂ c x) (hd : DifferentiableAt ℂ d x) :
    DifferentiableAt ℂ (fun y => triangularMultiplier (c y) (d y)) x := by
  apply DifferentiableAt.add (hc.smul_const _) ?_
  apply (differentiableAt_const (c := ContinuousLinearMap.inr ℂ ℂ F)).clm_comp
  exact ((ContinuousLinearMap.smulRightL ℂ (ℂ × F) F
    (ContinuousLinearMap.fst ℂ ℂ F)).differentiableAt.comp x hd)

end Multiplier
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open Filter
open scoped Topology
variable {T V : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {κ : Type*} [Fintype κ]

 theorem differentiableAt_polarPair {F : T → ℂ} {ψ : V → T} {h : κ → T} {x : V}
    (hF : ContDiffAt ℂ 2 F (ψ x)) (hψ : DifferentiableAt ℂ ψ x) :
    DifferentiableAt ℂ (polarPair F ψ h) x := by
  apply DifferentiableAt.prodMk
  · exact (hF.differentiableAt (by norm_num)).comp x hψ
  · apply differentiableAt_pi.mpr
    intro i
    have hd : DifferentiableAt ℂ (fderiv ℂ F) (ψ x) :=
      (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
    exact (hd.clm_apply (differentiableAt_const (h i))).comp x hψ

 theorem simple_polarPair_unit {F c S : T → ℂ} {ψ : V → T} {h : κ → T} {x : V}
    (hc : ContDiffAt ℂ 2 c (ψ x)) (hS : ContDiffAt ℂ 2 S (ψ x))
    (hψ : DifferentiableAt ℂ ψ x)
    (hFS : F =ᶠ[𝓝 (ψ x)] (fun y => c y * S y)) (hcx : c (ψ x) ≠ 0)
    (hz : polarPair F ψ h x = 0)
    (hsimple : (fderiv ℂ (polarPair F ψ h) x).IsInvertible) :
    polarPair S ψ h x = 0 ∧ (fderiv ℂ (polarPair S ψ h) x).IsInvertible := by
  let U : V → ((ℂ × (κ → ℂ)) →L[ℂ] (ℂ × (κ → ℂ))) :=
    fun y => triangularMultiplier (c (ψ y)) (fun i => fderiv ℂ c (ψ y) (h i))
  have hg := differentiableAt_polarPair (h := h) hS hψ
  have hU : DifferentiableAt ℂ U x := by
    apply differentiableAt_triangularMultiplier
    · exact (hc.differentiableAt (by norm_num)).comp x hψ
    · exact (differentiableAt_polarPair (h := h) hc hψ).snd
  have hu : (U x).IsInvertible := triangularMultiplier_invertible _ _ hcx
  have he : polarPair F ψ h =ᶠ[𝓝 x] (fun y => U y (polarPair S ψ h y)) := by
    have hlocal : ∀ᶠ z in 𝓝 (ψ x),
        (F z,fun i => fderiv ℂ F z (h i)) =
          triangularMultiplier (c z) (fun i => fderiv ℂ c z (h i))
            (S z,fun i => fderiv ℂ S z (h i)) := by
      filter_upwards [hFS, hFS.fderiv (𝕜 := ℂ), hc.eventually (by norm_num), hS.eventually (by norm_num)]
        with z h0 h1 hc' hS'
      rw [h1, fderiv_fun_mul (hc'.differentiableAt (by norm_num))
        (hS'.differentiableAt (by norm_num)), triangularMultiplier_apply]
      apply Prod.ext h0
      ext i
      simp
    exact hψ.continuousAt.eventually hlocal
  have hsz : polarPair S ψ h x = 0 := by
    apply hu.bijective.injective
    rw [map_zero, ← he.eq_of_nhds, hz]
  refine ⟨hsz, ?_⟩
  apply (simple_unit_multiplier_iff hU hg hsz hu).mp
  rwa [← he.fderiv_eq]
end PermanentBorder.PolarAnalysis

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.PolarAnalysis
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.PermanentBorder.PolarAnalysis.simple_polarPair_unit := @_root_.OAI.PermanentBorder.PolarAnalysis.simple_polarPair_unit
