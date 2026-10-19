-- Prove2me | solution 1 for OAI.ArnoldCounterexample.CriticalBound.haar_homotopy_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:24:13.378987+00:00
-- url     : https://prove2.me/submissions/355c5b73-9de1-48a8-9ae5-aaa77f54b2db

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Volume.lean:L21-L69
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.CriticalBound.haar_homotopy_invariant. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates
import Definitions.Def_OAI_Geometry_Arnold_Extension
import Definitions.Def_OAI_Geometry_Arnold_Deformation
import Definitions.Def_OAI_Geometry_Arnold_Exterior
import Definitions.Def_OAI_Geometry_Arnold_Homotopy
import Definitions.Def_OAI_Geometry_Arnold_Volume
import Theorems.Thm_OAI_ArnoldCounterexample_CriticalBound_contDiff_multilinear_apply
import Theorems.Thm_OAI_ArnoldCounterexample_CriticalBound_hasDerivAt_integral_of_compact
import Theorems.Thm_OAI_ArnoldCounterexample_CriticalBound_integral_extDeriv_rightMul_eq_zero
import Theorems.Thm_OAI_ArnoldCounterexample_Forms_cylinder_homotopy_identity

-- ---- from OAI.Geometry.Arnold.Differentiation ----
namespace OAI

universe uE uF uG

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator

namespace ArnoldCounterexample.CriticalBound

theorem contDiff_alternating_apply {E : Type uE} {F : Type uF} {G : Type uG}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {k : ℕ∞ω} {n : ℕ} {f : E → F [⋀^Fin n]→L[ℝ] G}
    (hf : ContDiff ℝ k f) {v : Fin n → E → F} (hv : ∀ i, ContDiff ℝ k (v i)) :
    ContDiff ℝ k (fun x ↦ f x (v · x)) := by
  convert! contDiff_multilinear_apply ((ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ).contDiff.comp hf) hv using 1

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open VectorField

end ArnoldCounterexample.CriticalBound

end

end OAI

-- ---- from OAI.Geometry.Arnold.Orbit ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator

namespace ArnoldCounterexample

namespace CriticalBound
open Matrix

lemma rotGen_skew (a b : Fin 5) : star (rotGen a b) = -rotGen a b := by
  ext i j
  simp [rotGen, Matrix.star_apply, Matrix.single_apply, sub_eq_add_neg, and_comm]

end CriticalBound
end ArnoldCounterexample

namespace ArnoldCounterexample.CriticalBound

lemma generators_skew (i : Fin 6) : star (generators i) = -generators i := by
  fin_cases i <;> exact rotGen_skew _ _

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound

attribute [local instance] OAI.ArnoldCounterexample.CriticalBound.instTopologicalSpaceRM
end ArnoldCounterexample.CriticalBound

end

end OAI

-- ---- from OAI.Geometry.Arnold.Homotopy ----
namespace OAI

universe uE uD uF

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open ContinuousAlternatingMap

open scoped BigOperators ContDiff
open ContinuousAlternatingMap

namespace ArnoldCounterexample.Forms
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma sliceContraction_contDiff {n : ℕ}
    (Θ : ℝ × E → (ℝ × E) [⋀^Fin (n + 1)]→L[ℝ] ℝ)
    (hΘ : ContDiff ℝ ∞ Θ) (t : ℝ) : ContDiff ℝ ∞ (sliceContraction Θ t) := by
  exact (cylinderContraction n).contDiff.comp (hΘ.comp (contDiff_const.prodMk contDiff_id))

end ArnoldCounterexample.Forms

end

end OAI

-- ---- from OAI.Geometry.Arnold.Volume ----
namespace OAI

universe uE uF

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open ContinuousAlternatingMap

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms ContinuousAlternatingMap

attribute [local instance] OAI.ArnoldCounterexample.CriticalBound.instTopologicalSpaceRM_3
/-- The Haar integral of a closed horizontal cylinder form is independent of
its slice. The bracket condition is algebraic. -/
theorem haar_homotopy_invariant
    (Θ : ℝ × RM → (ℝ × RM) [⋀^Fin 6]→L[ℝ] ℝ)
    (hΘ : ContDiff ℝ ∞ Θ) (hclosed : ∀ p, extDeriv Θ p = 0)
    (hvertical : ∀ (t : ℝ) (A : O5) (i j : Fin 5),
      sliceContraction Θ t A
        (Matrix.vecCons ((A : RM) * (generators i.castSucc * generators j.succ -
          generators j.succ * generators i.castSucc))
          (j.removeNth (i.castSucc.removeNth (fun k ↦ (A : RM) * generators k)))) = 0)
    (a b : ℝ) :
    (∫ A : O5, Θ (a, A) (fun i ↦ (0, (A : RM) * generators i)) ∂haar) =
    (∫ A : O5, Θ (b, A) (fun i ↦ (0, (A : RM) * generators i)) ∂haar) := by
  let : CompactSpace O5 := o5_compactSpace
  let : BorelSpace O5 := o5_borelSpace
  let F : ℝ → O5 → ℝ := fun t A ↦ Θ (t, A) (fun i ↦ (0, (A : RM) * generators i))
  let D : ℝ → O5 → ℝ := fun t A ↦
    (fderiv ℝ Θ (t, A) (1, 0)) (fun i ↦ (0, (A : RM) * generators i))
  have hF : Continuous (Function.uncurry F) := by
    have h := contDiff_alternating_apply hΘ (v := fun i p ↦ (0, p.2 * generators i))
      (fun i ↦ (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × RM ↦ (0 : ℝ))).prodMk
        (contDiff_snd.mul contDiff_const))
    exact h.continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hD : Continuous (Function.uncurry D) := by
    have hd : ContDiff ℝ ∞ (fun p : ℝ × RM ↦ fderiv ℝ Θ p (1, 0)) :=
      (hΘ.fderiv_right (by simp)).clm_apply contDiff_const
    have h := contDiff_alternating_apply hd (v := fun i p ↦ (0, p.2 * generators i))
      (fun i ↦ (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × RM ↦ (0 : ℝ))).prodMk
        (contDiff_snd.mul contDiff_const))
    exact h.continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hd (t : ℝ) (A : O5) : HasDerivAt (fun s ↦ F s A) (D t A) t := by
    have h := ((ContinuousAlternatingMap.apply ℝ (ℝ × RM) ℝ
      (fun i ↦ (0, (A : RM) * generators i))).hasFDerivAt).comp_hasDerivAt t
        ((hΘ.differentiable (by simp) (t, A)).hasFDerivAt.comp_hasDerivAt t
          ((hasDerivAt_id t).prodMk (hasDerivAt_const t (A : RM))))
    exact h
  have dzero (t : ℝ) : ∫ A : O5, D t A ∂haar = 0 := by
    have hz := integral_extDeriv_rightMul_eq_zero (sliceContraction Θ t)
      (sliceContraction_contDiff Θ hΘ t) generators generators_skew (hvertical t)
    convert hz using 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun A ↦
      (cylinder_homotopy_identity Θ (hΘ.differentiable (by simp)) t A
        (hclosed (t, A)) (fun i ↦ (A : RM) * generators i)).symm)
  have hder (t : ℝ) : HasDerivAt (fun s ↦ ∫ A, F s A ∂haar) 0 t := by
    convert hasDerivAt_integral_of_compact haar hF hD hd t using 1
    exact (dzero t).symm
  exact is_const_of_deriv_eq_zero (fun t ↦ (hder t).differentiableAt)
    (fun t ↦ (hder t).deriv) a b

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms ContinuousAlternatingMap

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.Forms
open ContinuousAlternatingMap

end ArnoldCounterexample.Forms

namespace ArnoldCounterexample.Forms

end ArnoldCounterexample.Forms

namespace ArnoldCounterexample.Forms
open ContinuousAlternatingMap

end ArnoldCounterexample.Forms

namespace ArnoldCounterexample.Forms
open ContinuousAlternatingMap

end ArnoldCounterexample.Forms

end

end OAI

-- ---- platform node ----
open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.CriticalBound
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open ContinuousAlternatingMap
open ArnoldCounterexample.Forms ContinuousAlternatingMap
attribute [local instance] OAI.ArnoldCounterexample.CriticalBound.instTopologicalSpaceRM_3


theorem solution : type_of% @_root_.OAI.ArnoldCounterexample.CriticalBound.haar_homotopy_invariant := @_root_.OAI.ArnoldCounterexample.CriticalBound.haar_homotopy_invariant
