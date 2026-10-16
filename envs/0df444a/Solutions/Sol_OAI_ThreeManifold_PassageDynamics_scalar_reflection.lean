-- Prove2me | solution 1 for OAI.ThreeManifold.PassageDynamics.scalar_reflection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:46:28.555992+00:00
-- url     : https://prove2.me/submissions/9fe024a8-a463-4c58-8c54-5d3ab819f0b4

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Returning.lean:L1031-L1050
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.PassageDynamics.scalar_reflection. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning

-- ---- from OAI.Geometry.ConjugatePoints.Returning ----
namespace OAI

noncomputable section

/-!
# Returning neck geodesics, passage dynamics, and index bounds.
-/

open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
namespace ThreeManifold.Neck
open Matrix
open scoped Matrix.Norms.Elementwise

end ThreeManifold.Neck

namespace ThreeManifold.Turning

end ThreeManifold.Turning

namespace ThreeManifold.DirectTurning

section
open Set MeasureTheory Neck Matrix
open scoped Interval Topology

end

open Neck Matrix Set MeasureTheory Turning
open scoped Interval Topology Matrix.Norms.Elementwise

end ThreeManifold.DirectTurning

open Set MeasureTheory
open scoped Interval
namespace ThreeManifold.ReturningTime

end ThreeManifold.ReturningTime

open Set MeasureTheory
open scoped Interval
namespace ThreeManifold.ReturningCoefficients
open Neck Matrix

end ThreeManifold.ReturningCoefficients

open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.Cometric
open Neck Matrix

end ThreeManifold.Cometric

open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ReturningCoefficients
open Neck Cometric Matrix

end ThreeManifold.ReturningCoefficients

open Set Filter
open scoped Topology ContDiff
namespace ThreeManifold.PassageDynamics

lemma smooth_autonomous_unique {V : (ℝ × ℝ) → (ℝ × ℝ)}
    (hV : ContDiff ℝ ∞ V) {f g : ℝ → ℝ × ℝ} {a b c : ℝ}
    (hc : c ∈ Ioo a b) (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfd : ∀ s ∈ Ioo a b, HasDerivAt f (V (f s)) s)
    (hgd : ∀ s ∈ Ioo a b, HasDerivAt g (V (g s)) s)
    (heq : f c = g c) : EqOn f g (Icc a b) := by
  have hcomp := (isCompact_Icc.image_of_continuousOn hf).union (isCompact_Icc.image_of_continuousOn hg)
  obtain ⟨R, hR⟩ := hcomp.isBounded.subset_closedBall (0 : ℝ × ℝ)
  obtain ⟨K, hK⟩ := hV.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : ℝ × ℝ) R) (isCompact_closedBall (0 : ℝ × ℝ) R)
  exact ODE_solution_unique_of_mem_Icc (v := fun _ => V)
    (s := fun _ => Metric.closedBall (0 : ℝ × ℝ) R) (fun _ _ => hK) hc hf hfd
    (fun s hs => hR (Or.inl ⟨s, Ioo_subset_Icc_self hs, rfl⟩)) hg hgd
    (fun s hs => hR (Or.inr ⟨s, Ioo_subset_Icc_self hs, rfl⟩)) heq

lemma scalarVectorField_smooth {F₁ : ℝ → ℝ} (hF : ContDiff ℝ ∞ F₁) :
    ContDiff ℝ ∞ (scalarVectorField F₁) :=
  contDiff_snd.prodMk ((hF.comp contDiff_fst).neg.div_const 2)

lemma scalar_equations_unique {F₁ : ℝ → ℝ} (hF : ContDiff ℝ ∞ F₁)
    {t v u w : ℝ → ℝ} {a b c : ℝ} (hc : c ∈ Ioo a b)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-F₁ (t s) / 2) s)
    (hu : ∀ s ∈ Icc a b, HasDerivAt u (w s) s)
    (hw : ∀ s ∈ Icc a b, HasDerivAt w (-F₁ (u s) / 2) s)
    (htc : t c = u c) (hvc : v c = w c) :
    EqOn t u (Icc a b) ∧ EqOn v w (Icc a b) := by
  have hh := smooth_autonomous_unique (scalarVectorField_smooth hF) hc
    ((HasDerivAt.continuousOn ht).prodMk (HasDerivAt.continuousOn hv))
    ((HasDerivAt.continuousOn hu).prodMk (HasDerivAt.continuousOn hw))
    (fun s hs => (ht s (Ioo_subset_Icc_self hs)).prodMk (hv s (Ioo_subset_Icc_self hs)))
    (fun s hs => (hu s (Ioo_subset_Icc_self hs)).prodMk (hw s (Ioo_subset_Icc_self hs)))
    (Prod.ext htc hvc)
  exact ⟨fun s hs => congrArg Prod.fst (hh hs), fun s hs => congrArg Prod.snd (hh hs)⟩

lemma scalar_reflection {F₁ : ℝ → ℝ} (hF : ContDiff ℝ ∞ F₁)
    {t v : ℝ → ℝ} {a b c : ℝ} (hc : c ∈ Ioo a b) (hab : a + b = 2 * c)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-F₁ (t s) / 2) s)
    (hvc : v c = 0) :
    ∀ s ∈ Icc a b, t (2 * c - s) = t s ∧ v (2 * c - s) = -v s := by
  have hr (s : ℝ) (hs : s ∈ Icc a b) : 2 * c - s ∈ Icc a b :=
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have htd (s : ℝ) (hs : s ∈ Icc a b) :
      HasDerivAt (fun u => t (2 * c - u)) (-v (2 * c - s)) s := by
    convert (ht _ (hr s hs)).comp s ((hasDerivAt_id s).const_sub (2 * c)) using 1 <;>
      (first | rfl | simp)
  have hvd (s : ℝ) (hs : s ∈ Icc a b) :
      HasDerivAt (fun u => -v (2 * c - u)) (-F₁ (t (2 * c - s)) / 2) s := by
    convert ((hv _ (hr s hs)).comp s ((hasDerivAt_id s).const_sub (2 * c))).neg using 1 <;>
      (first | rfl | ring)
  obtain ⟨htu, hvw⟩ := scalar_equations_unique hF hc ht hv htd hvd
    (by congr 1; ring) (by rw [show 2 * c - c = c by ring, hvc, neg_zero])
  intro s hs
  exact ⟨(htu hs).symm, by linarith [hvw hs]⟩

end ThreeManifold.PassageDynamics

open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ReturningPassage

section
-- [generator] trimmed: open Neck Cometric ReturningCoefficients ReturningTime PassageDynamics Matrix
open Neck Cometric ReturningCoefficients PassageDynamics Matrix

end

-- [generator] trimmed: open Neck Cometric ReturningCoefficients ReturningTime PassageDynamics Matrix DirectTurning Turning
open Neck Cometric ReturningCoefficients PassageDynamics Matrix DirectTurning Turning

end ThreeManifold.ReturningPassage

namespace ThreeManifold.Neck

section
open Set Matrix MeasureTheory
open scoped ContDiff Interval Topology Matrix.Norms.Elementwise

end

section
open Set Matrix Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

end

open Set Matrix Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.Neck

namespace ThreeManifold.ReturningPassage

section
open Neck Cometric Turning Set Matrix Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

end

section
open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning
open scoped ContDiff Topology Matrix.Norms.Elementwise

end

open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning ReturningCoefficients
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.ReturningPassage

namespace ThreeManifold.Neck
open Set Matrix MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.Neck

namespace ThreeManifold.ReturningPassage
open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning ReturningCoefficients
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.ReturningPassage

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.PassageDynamics
open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set MeasureTheory
open scoped Interval
open Set MeasureTheory
open scoped Interval
open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
open Set Filter
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.ThreeManifold.PassageDynamics.scalar_reflection := @_root_.OAI.ThreeManifold.PassageDynamics.scalar_reflection
