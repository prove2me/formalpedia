-- Prove2me | solution 1 for OAI.ThreeManifold.Neck.coordinate_index_integral
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:20:05.278539+00:00
-- url     : https://prove2.me/submissions/e1f41a4c-6309-42e8-a4dd-828023a37a1c

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Neck.lean:L365-L421
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.Neck.coordinate_index_integral. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Theorems.Thm_OAI_ThreeManifold_Neck_boundaryTerm_hasDerivAt
import Theorems.Thm_OAI_ThreeManifold_Neck_index_density_identity

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

lemma coordinate_index_integral
    {P Q A B : ℝ → TMat} {t v w : ℝ → ℝ} {u z : ℝ → TVec}
    {wd : ℝ → ℝ} {zd : ℝ → TVec} {a c : ℝ}
    (hP : ContinuousOn (P ∘ t) (Set.uIcc a c))
    (hQ : ContinuousOn (Q ∘ t) (Set.uIcc a c))
    (hA : ContinuousOn (A ∘ t) (Set.uIcc a c))
    (hB : ContinuousOn (B ∘ t) (Set.uIcc a c))
    (hv : ContinuousOn v (Set.uIcc a c)) (hu : ContinuousOn u (Set.uIcc a c))
    (hw : ContinuousOn w (Set.uIcc a c)) (hz : ContinuousOn z (Set.uIcc a c))
    (hwd : ContinuousOn wd (Set.uIcc a c)) (hzd : ContinuousOn zd (Set.uIcc a c))
    (hQP : ∀ s ∈ Set.uIcc a c, Q (t s) * P (t s) = 1)
    (hQs : ∀ s ∈ Set.uIcc a c, (Q (t s))ᵀ = Q (t s))
    (hPs : ∀ s ∈ Set.uIcc a c, (P (t s))ᵀ = P (t s))
    (hAs : ∀ s ∈ Set.uIcc a c, (A (t s))ᵀ = A (t s))
    (hBs : ∀ s ∈ Set.uIcc a c, (B (t s))ᵀ = B (t s))
    (ht : ∀ s ∈ Set.uIcc a c, HasDerivAt t (v s) s)
    (hv' : ∀ s ∈ Set.uIcc a c,
      HasDerivAt v ((1 / 2 : ℝ) * pairing (A (t s)) (u s) (u s)) s)
    (hu' : ∀ s ∈ Set.uIcc a c,
      HasDerivAt u (-v s • (P (t s) *ᵥ (A (t s) *ᵥ u s))) s)
    (hA' : ∀ s ∈ Set.uIcc a c, HasDerivAt A (B (t s)) (t s))
    (hw' : ∀ s ∈ Set.uIcc a c, HasDerivAt w (wd s) s)
    (hz' : ∀ s ∈ Set.uIcc a c, HasDerivAt z (zd s) s) :
    (∫ s in a..c,
      metric (Q (t s)) ((wd s, zd s) + gamma (P (t s)) (A (t s)) (v s, u s) (w s, z s))
        ((wd s, zd s) + gamma (P (t s)) (A (t s)) (v s, u s) (w s, z s)) -
      metric (Q (t s)) (w s, z s)
        (curvatureJet (P (t s)) (A (t s)) (B (t s)) (w s, z s) (v s, u s) (v s, u s))) =
    (∫ s in a..c,
      coordinateEnergyDensity (Q (t s)) (A (t s)) (B (t s))
        (v s, u s) (w s, z s) (wd s, zd s)) -
      (boundaryTerm (A (t c)) (v c, u c) (w c, z c) -
        boundaryTerm (A (t a)) (v a, u a) (w a, z a)) := by
  let e (s : ℝ) := coordinateEnergyDensity (Q (t s)) (A (t s)) (B (t s))
    (v s, u s) (w s, z s) (wd s, zd s)
  let b (s : ℝ) := boundaryJet (P (t s)) (A (t s)) (B (t s))
    (v s, u s) (w s, z s) (wd s, zd s)
  have he : ContinuousOn e (Set.uIcc a c) :=
    continuousOn_energy hQ hA hB (hv.prodMk hu) (hw.prodMk hz) (hwd.prodMk hzd)
  have hb : ContinuousOn b (Set.uIcc a c) :=
    continuousOn_boundaryJet hP hA hB (hv.prodMk hu) (hw.prodMk hz) (hwd.prodMk hzd)
  have hderiv : ∀ s ∈ Set.uIcc a c,
      HasDerivAt (fun r => boundaryTerm (A (t r)) (v r, u r) (w r, z r)) (b s) s := by
    intro s hs
    exact boundaryTerm_hasDerivAt (hPs s hs) (hAs s hs) (hBs s hs)
      (hA' s hs) (ht s hs) (hv' s hs) (hu' s hs) (hw' s hs) (hz' s hs)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hb.intervalIntegrable
  calc
    _ = ∫ s in a..c, e s - b s := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact index_density_identity (hQP s hs) (hQs s hs) (hPs s hs) (hAs s hs)
        (hBs s hs) _ _ _
    _ = (∫ s in a..c, e s) - ∫ s in a..c, b s :=
      intervalIntegral.integral_sub he.intervalIntegrable hb.intervalIntegrable
    _ = _ := by rw [hFTC]

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

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.Neck
open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Matrix
open scoped Matrix Matrix.Norms.Elementwise


theorem solution : type_of% @_root_.OAI.ThreeManifold.Neck.coordinate_index_integral := @_root_.OAI.ThreeManifold.Neck.coordinate_index_integral
