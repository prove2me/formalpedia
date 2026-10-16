-- Prove2me | solution 1 for OAI.ThreeManifold.Neck.normal_index_integral
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:54:41.929123+00:00
-- url     : https://prove2.me/submissions/a817b725-6bfa-4133-b6d6-4e1c85565e7f

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Returning.lean:L1816-L1893
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.Neck.normal_index_integral. The node keeps its source
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
import Theorems.Thm_OAI_ThreeManifold_Neck_coordinate_index_integral
import Theorems.Thm_OAI_ThreeManifold_Neck_index_density_identity
import Theorems.Thm_OAI_ThreeManifold_Neck_pairing_hasDerivAt

-- ---- from OAI.Geometry.ConjugatePoints.Neck ----
namespace OAI

noncomputable section

/-!
# Tensor identities and the local and torus neck metrics.
-/

open Set Manifold Bundle Filter Topology
open scoped ContDiff

namespace ThreeManifold.Tensor
open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

end ThreeManifold.Tensor

namespace ThreeManifold.Neck
open Matrix
open scoped Matrix Matrix.Norms.Elementwise

lemma pairing_add_left (A : TMat) (u v w : TVec) :
    pairing A (u + v) w = pairing A u w + pairing A v w := by
  simp only [pairing, add_dotProduct]
lemma pairing_add_right (A : TMat) (u v w : TVec) :
    pairing A u (v + w) = pairing A u v + pairing A u w := by
  simp only [pairing, Matrix.mulVec_add, dotProduct_add]
lemma pairing_smul_right (A : TMat) (r : ℝ) (u v : TVec) :
    pairing A u (r • v) = r * pairing A u v := by
  simp only [pairing, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
lemma pairing_symm {A : TMat} (hA : Aᵀ = A) (u v : TVec) :
    pairing A u v = pairing A v u := by
  unfold pairing
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hA, dotProduct_comm]

lemma metric_symm {Q : TMat} (hQ : Qᵀ = Q) (U V : Vec) :
    metric Q U V = metric Q V U := by
  rw [metric, metric, pairing_symm hQ]
  ring

lemma pairing_inverse {P Q : TMat} (hQP : Q * P = 1) (u v : TVec) :
    pairing Q u (P *ᵥ v) = dotProduct u v := by
  simp only [pairing, Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]

lemma metric_gamma {P Q : TMat} (hQP : Q * P = 1) (A : TMat) (U V W : Vec) :
    metric Q U (gamma P A V W) =
      -(1 / 2 : ℝ) * U.1 * pairing A V.2 W.2 +
       (1 / 2 : ℝ) * V.1 * pairing A U.2 W.2 +
       (1 / 2 : ℝ) * W.1 * pairing A U.2 V.2 := by
  simp only [metric, gamma, pairing_smul_right, pairing_add_right,
    pairing_inverse hQP]
  simp only [pairing]
  ring

lemma pairing_matrix_smul (A : TMat) (r : ℝ) (u v : TVec) :
    pairing (r • A) u v = r * pairing A u v := by
  simp only [pairing, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

lemma continuous_pairing : Continuous (fun p : TMat × TVec × TVec =>
    pairing p.1 p.2.1 p.2.2) := by
  unfold pairing Matrix.mulVec dotProduct
  fun_prop

lemma continuousOn_pairing {X : Type*} [TopologicalSpace X]
    {A : X → TMat} {u v : X → TVec} {S : Set X}
    (hA : ContinuousOn A S) (hu : ContinuousOn u S) (hv : ContinuousOn v S) :
    ContinuousOn (fun s => pairing (A s) (u s) (v s)) S :=
  continuous_pairing.comp_continuousOn (hA.prodMk (hu.prodMk hv))

lemma continuousOn_energy {X : Type*} [TopologicalSpace X] {S : Set X}
    {Q A B : X → TMat} {T V Vdot : X → Vec}
    (hQ : ContinuousOn Q S) (hA : ContinuousOn A S) (hB : ContinuousOn B S)
    (hT : ContinuousOn T S) (hV : ContinuousOn V S) (hVdot : ContinuousOn Vdot S) :
    ContinuousOn (fun s => coordinateEnergyDensity (Q s) (A s) (B s)
      (T s) (V s) (Vdot s)) S := by
  unfold coordinateEnergyDensity
  exact ((hVdot.fst.pow 2).add (continuousOn_pairing hQ hVdot.snd hVdot.snd)).add
    (((continuousOn_const.mul hV.fst).mul (continuousOn_pairing hA hVdot.snd hT.snd))) |>.add
    ((continuousOn_const.mul (hV.fst.pow 2)).mul (continuousOn_pairing hB hT.snd hT.snd))

lemma continuousOn_boundaryJet {X : Type*} [TopologicalSpace X] {S : Set X}
    {P A B : X → TMat} {T V Vdot : X → Vec}
    (hP : ContinuousOn P S) (hA : ContinuousOn A S) (hB : ContinuousOn B S)
    (hT : ContinuousOn T S) (hV : ContinuousOn V S) (hVdot : ContinuousOn Vdot S) :
    ContinuousOn (fun s => boundaryJet (P s) (A s) (B s)
      (T s) (V s) (Vdot s)) S := by
  unfold boundaryJet
  have hS : ContinuousOn (fun s => A s * P s * A s) S := (hA.mul hP).mul hA
  exact ((((((continuousOn_const.mul (continuousOn_pairing hA hT.snd hT.snd)).mul
    (continuousOn_pairing hA hV.snd hV.snd)).sub
    (hT.fst.mul (continuousOn_pairing hA hVdot.snd hV.snd))).sub
    ((continuousOn_const.mul (hT.fst.pow 2)).mul (continuousOn_pairing hB hV.snd hV.snd))).add
    (hVdot.fst.mul (continuousOn_pairing hA hV.snd hT.snd))).add
    (hV.fst.mul (continuousOn_pairing hA hVdot.snd hT.snd))).add
    ((hV.fst.mul hT.fst).mul (continuousOn_pairing hB hV.snd hT.snd)) |>.sub
    ((hV.fst.mul hT.fst).mul (continuousOn_pairing hS hV.snd hT.snd))

end ThreeManifold.Neck

open Set Filter
open scoped Topology ContDiff

namespace ThreeManifold.Cometric
open Matrix
open scoped Matrix.Norms.Elementwise

attribute [fun_prop] χ_deriv_smooth χ_deriv2_smooth

end ThreeManifold.Cometric

namespace ThreeManifold.LocalNeck

section
open Manifold Bundle Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

open Cometric Neck

end

open Manifold Bundle Set Filter Cometric Neck Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

end ThreeManifold.LocalNeck

namespace ThreeManifold.TorusNeck

section
open Set Filter Topology Manifold Bundle
open scoped ContDiff Matrix.Norms.Elementwise
open LocalNeck QuotientConstruction

open Cometric Neck
end

open Set Filter Manifold Bundle Neck Cometric LocalNeck Matrix
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.TorusNeck

end

end OAI

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

lemma metric_compatibility_jet {P Q A : TMat} (hQP : Q * P = 1) (hA : Aᵀ = A)
    (T V W : Vec) : T.1 * pairing A V.2 W.2 =
      metric Q V (gamma P A T W) + metric Q W (gamma P A T V) := by
  simp only [metric_gamma hQP, pairing_symm hA W.2 V.2,
    pairing_symm hA W.2 T.2,
    pairing_symm hA T.2 V.2]
  ring

lemma metric_hasDerivAt {Q : ℝ → TMat} {A : TMat} {t : ℝ → ℝ}
    {V W : ℝ → Vec} {V' W' : Vec} {v s : ℝ}
    (hQ : HasDerivAt Q A (t s)) (ht : HasDerivAt t v s)
    (hV : HasDerivAt V V' s) (hW : HasDerivAt W W' s) :
    HasDerivAt (fun r => metric (Q (t r)) (V r) (W r))
      (metric (Q (t s)) V' (W s) + metric (v • A) (0, (V s).2) (0, (W s).2) +
        metric (Q (t s)) (V s) W') s := by
  have hv1 := (ContinuousLinearMap.fst ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hV
  have hv2 := (ContinuousLinearMap.snd ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hV
  have hw1 := (ContinuousLinearMap.fst ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hW
  have hw2 := (ContinuousLinearMap.snd ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hW
  have hp := pairing_hasDerivAt (hQ.scomp s ht) hv2 hw2
  convert! (hv1.mul hw1).add hp using 1
  simp only [metric, zero_mul, zero_add, Function.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  ring

lemma pairing_neg_right (Q : TMat) (x y : TVec) :
    pairing Q x (-y) = -pairing Q x y := by
  simp only [pairing, Matrix.mulVec_neg, dotProduct_neg]

lemma tangential_hasDerivAt {P A : TMat} {Q : ℝ → TMat} {t : ℝ → ℝ}
    {T V : ℝ → Vec} {D : Vec} {s : ℝ}
    (hQP : Q (t s) * P = 1) (hQs : (Q (t s))ᵀ = Q (t s)) (hA : Aᵀ = A)
    (hQ : HasDerivAt Q A (t s)) (ht : HasDerivAt t (T s).1 s)
    (hT : HasDerivAt T (-gamma P A (T s) (T s)) s)
    (hV : HasDerivAt V D s) :
    HasDerivAt (fun r => metric (Q (t r)) (V r) (T r))
      (metric (Q (t s)) (D + gamma P A (T s) (V s)) (T s)) s := by
  apply (metric_hasDerivAt hQ ht hV hT).congr_deriv
  have hc := metric_compatibility_jet hQP hA (T s) (V s) (T s)
  simp only [metric, zero_mul, zero_add, pairing_matrix_smul] at hc ⊢
  dsimp only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
  simp only [pairing_add_left, pairing_neg_right]
  have hg := metric_symm hQs (T s) (gamma P A (T s) (V s))
  unfold metric at hg
  linarith

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

lemma normal_index_integral
    {P Q A B : ℝ → TMat} {t v w : ℝ → ℝ} {u z : ℝ → TVec}
    {wd : ℝ → ℝ} {zd : ℝ → TVec} {a c m : ℝ}
    (hP : ContinuousOn (P ∘ t) (uIcc a c))
    (hQ : ContinuousOn (Q ∘ t) (uIcc a c))
    (hA : ContinuousOn (A ∘ t) (uIcc a c))
    (hB : ContinuousOn (B ∘ t) (uIcc a c))
    (hv : ContinuousOn v (uIcc a c)) (hu : ContinuousOn u (uIcc a c))
    (hw : ContinuousOn w (uIcc a c)) (hz : ContinuousOn z (uIcc a c))
    (hwd : ContinuousOn wd (uIcc a c)) (hzd : ContinuousOn zd (uIcc a c))
    (hQP : ∀ s ∈ uIcc a c, Q (t s) * P (t s) = 1)
    (hQs : ∀ s ∈ uIcc a c, (Q (t s))ᵀ = Q (t s))
    (hPs : ∀ s ∈ uIcc a c, (P (t s))ᵀ = P (t s))
    (hAs : ∀ s ∈ uIcc a c, (A (t s))ᵀ = A (t s))
    (hBs : ∀ s ∈ uIcc a c, (B (t s))ᵀ = B (t s))
    (ht : ∀ s ∈ uIcc a c, HasDerivAt t (v s) s)
    (hv' : ∀ s ∈ uIcc a c,
      HasDerivAt v ((1 / 2 : ℝ) * pairing (A (t s)) (u s) (u s)) s)
    (hu' : ∀ s ∈ uIcc a c,
      HasDerivAt u (-v s • (P (t s) *ᵥ (A (t s) *ᵥ u s))) s)
    (hQ' : ∀ s ∈ uIcc a c, HasDerivAt Q (A (t s)) (t s))
    (hA' : ∀ s ∈ uIcc a c, HasDerivAt A (B (t s)) (t s))
    (hw' : ∀ s ∈ uIcc a c, HasDerivAt w (wd s) s)
    (hz' : ∀ s ∈ uIcc a c, HasDerivAt z (zd s) s)
    (hlin : ∀ s ∈ uIcc a c,
      HasDerivAt (fun r => metric (Q (t r)) (w r, z r) (v r, u r)) m s) :
    (∫ s in a..c, normalDensity (P (t s)) (Q (t s)) (A (t s)) (B (t s))
      (v s, u s) (w s, z s) (wd s, zd s)) =
      (∫ s in a..c, coordinateEnergyDensity (Q (t s)) (A (t s)) (B (t s))
        (v s, u s) (w s, z s) (wd s, zd s)) -
      (boundaryTerm (A (t c)) (v c, u c) (w c, z c) -
        boundaryTerm (A (t a)) (v a, u a) (w a, z a)) - (c - a) * m ^ 2 := by
  have hTi (s : ℝ) (hs : s ∈ uIcc a c) : HasDerivAt (fun r => (v r, u r))
      (-gamma (P (t s)) (A (t s)) (v s, u s) (v s, u s)) s := by
    apply ((hv' s hs).prodMk (hu' s hs)).congr_deriv
    apply Prod.ext
    · simp only [gamma, Prod.fst_neg, neg_mul, neg_neg]
    · simp only [gamma, Prod.snd_neg]
      module
  have hm (s : ℝ) (hs : s ∈ uIcc a c) :
      metric (Q (t s)) ((wd s, zd s) + gamma (P (t s)) (A (t s))
        (v s, u s) (w s, z s)) (v s, u s) = m := by
    exact (tangential_hasDerivAt (hQP s hs) (hQs s hs) (hAs s hs) (hQ' s hs)
      (ht s hs) (hTi s hs) ((hw' s hs).prodMk (hz' s hs))).unique (hlin s hs)
  let E := fun s => coordinateEnergyDensity (Q (t s)) (A (t s)) (B (t s))
    (v s, u s) (w s, z s) (wd s, zd s)
  let D := fun s => boundaryJet (P (t s)) (A (t s)) (B (t s))
    (v s, u s) (w s, z s) (wd s, zd s)
  have hEc : ContinuousOn E (uIcc a c) :=
    continuousOn_energy hQ hA hB (hv.prodMk hu) (hw.prodMk hz) (hwd.prodMk hzd)
  have hDc : ContinuousOn D (uIcc a c) :=
    continuousOn_boundaryJet hP hA hB (hv.prodMk hu) (hw.prodMk hz) (hwd.prodMk hzd)
  have hI := coordinate_index_integral hP hQ hA hB hv hu hw hz hwd hzd hQP
    hQs hPs hAs hBs ht hv' hu' hA' hw' hz'
  have heq : (∫ s in a..c, normalDensity (P (t s)) (Q (t s)) (A (t s)) (B (t s))
      (v s, u s) (w s, z s) (wd s, zd s)) = (∫ s in a..c, E s - D s - m ^ 2) := by
    apply intervalIntegral.integral_congr
    intro s hs
    change normalDensity (P (t s)) (Q (t s)) (A (t s)) (B (t s))
      (v s, u s) (w s, z s) (wd s, zd s) = E s - D s - m ^ 2
    unfold normalDensity
    rw [index_density_identity (hQP s hs) (hQs s hs) (hPs s hs)
      (hAs s hs) (hBs s hs), hm s hs]
  have hsub : (∫ s in a..c, E s - D s - m ^ 2) =
      (∫ s in a..c, E s - D s) - (∫ _s in a..c, m ^ 2) :=
    intervalIntegral.integral_sub ((hEc.sub hDc).intervalIntegrable) intervalIntegrable_const
  rw [heq, hsub, intervalIntegral.integral_const, smul_eq_mul]
  have hED : (∫ s in a..c, E s - D s) =
      (∫ s in a..c, coordinateEnergyDensity (Q (t s)) (A (t s)) (B (t s))
        (v s, u s) (w s, z s) (wd s, zd s)) -
      (boundaryTerm (A (t c)) (v c, u c) (w c, z c) -
        boundaryTerm (A (t a)) (v a, u a) (w a, z a)) := by
    rw [← hI]
    apply intervalIntegral.integral_congr
    intro s hs
    exact (index_density_identity (hQP s hs) (hQs s hs) (hPs s hs)
      (hAs s hs) (hBs s hs) (v s, u s) (w s, z s) (wd s, zd s)).symm
  rw [hED]

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
open OAI OAI.ThreeManifold OAI.ThreeManifold.Neck
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
open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
open Set Matrix Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise


theorem solution : type_of% @_root_.OAI.ThreeManifold.Neck.normal_index_integral := @_root_.OAI.ThreeManifold.Neck.normal_index_integral
