-- Prove2me | solution 1 for OAI.ThreeManifold.NonpositiveMetric.CNMidpoint.axisShift_mul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:27:28.108212+00:00
-- url     : https://prove2.me/submissions/4c9a0090-394c-4479-9847-d9b9fca0c73d

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Convexity.lean:L512-L533
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.NonpositiveMetric.CNMidpoint.axisShift_mul. The node keeps its source
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
import Definitions.Def_OAI_Geometry_ConjugatePoints_Index
import Definitions.Def_OAI_Geometry_ConjugatePoints_CompactMetric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Curvature
import Definitions.Def_OAI_Geometry_ConjugatePoints_Geodesics
import Definitions.Def_OAI_Geometry_ConjugatePoints_Continuation
import Definitions.Def_OAI_Geometry_ConjugatePoints_Distance
import Definitions.Def_OAI_Geometry_ConjugatePoints_Convexity
import Theorems.Thm_OAI_ThreeManifold_NonpositiveMetric_CNMidpoint_projection_angle

-- ---- from OAI.Geometry.ConjugatePoints.Convexity ----
namespace OAI

noncomputable section

/-!
# Midpoint convexity, minsets, and the semisimple shear obstruction.
-/

section
open Set Filter Topology
namespace ThreeManifold.NonpositiveMetric
variable (X : Type*) [MetricSpace X]

namespace CNMidpoint
variable {X} (C : CNMidpoint X)
include C

lemma mid_dist_left (x y : X) : dist (C.mid x y) x = dist x y / 2 := by
  have hx := C.cn x y x
  have hy := C.cn x y y
  simp only [dist_self,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_add,add_zero,dist_comm y x] at hx hy
  have ht := dist_triangle x (C.mid x y) y
  rw [dist_comm x (C.mid x y)] at ht
  nlinarith [(show 0 ≤ dist (C.mid x y) x from dist_nonneg),(show 0 ≤ dist (C.mid x y) y from dist_nonneg),(show 0 ≤ dist x y from dist_nonneg),
    sq_nonneg (dist (C.mid x y) x-dist (C.mid x y) y)]
lemma mid_dist_right (x y : X) : dist (C.mid x y) y = dist x y / 2 := by
  have hx := C.mid_dist_left x y
  have hy := C.cn x y y
  simp only [dist_self,zero_pow (by norm_num : (2:ℕ) ≠ 0),add_zero] at hy
  have ht := dist_triangle x (C.mid x y) y
  rw [dist_comm x (C.mid x y),hx] at ht
  nlinarith [(show 0 ≤ dist (C.mid x y) y from dist_nonneg),(show 0 ≤ dist x y from dist_nonneg)]

lemma eq_mid_of_dist_le {x y z : X} (hx : dist x z ≤ dist x y /2)
    (hy : dist y z ≤ dist x y /2) : z = C.mid x y := by
  have hh := C.cn x y z
  have he : dist (C.mid x y) z = 0 := by
    nlinarith [(show 0 ≤ dist x z from dist_nonneg),(show 0 ≤ dist y z from dist_nonneg),(show 0 ≤ dist x y from dist_nonneg),(show 0 ≤ dist (C.mid x y) z from dist_nonneg)]
  exact (dist_eq_zero.mp he).symm
lemma mid_comm (x y : X) : C.mid x y = C.mid y x := by
  apply C.eq_mid_of_dist_le
  · rw [dist_comm, C.mid_dist_right,dist_comm x y]
  · rw [dist_comm, C.mid_dist_left,dist_comm x y]
lemma mid_common (x y z : X) : dist (C.mid x z) (C.mid y z) ≤ dist x y /2 := by
  have h := C.cn x z (C.mid y z)
  have hx := C.cn y z x
  rw [dist_comm x (C.mid y z),dist_comm z (C.mid y z),C.mid_dist_right] at h
  rw [dist_comm y x,dist_comm z x] at hx
  nlinarith [(show 0 ≤ dist x y from dist_nonneg),(show 0 ≤ dist (C.mid x z) (C.mid y z) from dist_nonneg)]

lemma mid_convex (x y z w : X) :
    dist (C.mid x y) (C.mid z w) ≤ (dist x z + dist y w)/2 := by
  have h1 := C.mid_common x z y
  have h2 := C.mid_common y w z
  rw [C.mid_comm y z,C.mid_comm w z] at h2
  exact (dist_triangle (C.mid x y) (C.mid z y) (C.mid z w)).trans (by linarith)

end CNMidpoint
end ThreeManifold.NonpositiveMetric
end

section
open Set Filter Topology Function
namespace ThreeManifold.NonpositiveMetric.CNMidpoint

section
variable {X : Type*} [MetricSpace X] (C : CNMidpoint X)

include C

lemma quadrilateral (a b c d : X) :
    dist a c ^2 + dist b d ^2 ≤
      dist a b ^2 + dist b c ^2 + dist c d ^2 + dist d a ^2 := by
  have hb := C.cn a c b
  have hd := C.cn a c d
  have ht := dist_triangle b (C.mid a c) d
  rw [dist_comm b (C.mid a c)] at ht
  rw [dist_comm c b] at hb
  rw [dist_comm a d] at hd
  have hn : 0 ≤ dist b d := dist_nonneg
  have hsq : dist b d ^2 ≤ (dist (C.mid a c) b + dist (C.mid a c) d)^2 :=
    (sq_le_sq₀ hn (add_nonneg dist_nonneg dist_nonneg)).mpr ht
  nlinarith [sq_nonneg (dist (C.mid a c) b - dist (C.mid a c) d)]

lemma projection_nonexpansive {S : Set X} (hS : C.MidConvex S)
    {x y p q : X} (hp : p ∈ S) (hq : q ∈ S)
    (hm : ∀ z ∈ S, dist x p ≤ dist x z) (hn : ∀ z ∈ S, dist y q ≤ dist y z) :
    dist p q ≤ dist x y := by
  have h1 := C.projection_angle hS hp hm hq
  have h2 := C.projection_angle hS hq hn hp
  have h3 := C.quadrilateral x y q p
  rw [dist_comm q p] at h2 h3
  rw [dist_comm p x] at h3
  nlinarith [(show 0 ≤ dist p q from dist_nonneg),(show 0 ≤ dist x y from dist_nonneg)]

lemma projection_unique {S : Set X} (hS : C.MidConvex S)
    {x p q : X} (hp : p ∈ S) (hq : q ∈ S)
    (hm : ∀ z ∈ S, dist x p ≤ dist x z) (hn : ∀ z ∈ S, dist x q ≤ dist x z) : p = q := by
  have hh := C.projection_nonexpansive hS hp hq hm hn
  simpa using hh

end

section
variable {X : Type*} [MetricSpace X] (C : CNMidpoint X)
include C

end

section
variable {X : Type*} [MetricSpace X] (C : CNMidpoint X)

include C

end

section
variable {X : Type*} [MetricSpace X] (C : CNMidpoint X)
include C
lemma line_midpoint {c : ℝ → X} (hc : Isometry c) (s t : ℝ) :
    c ((s+t)/2) = C.mid (c s) (c t) := by
  have he : (s+t)/2 = midpoint ℝ s t := by simp [midpoint_eq_smul_add]; ring
  apply C.eq_mid_of_dist_le
  · rw [hc.dist_eq,hc.dist_eq,he,dist_left_midpoint]
    norm_num
    linarith
  · rw [hc.dist_eq,hc.dist_eq,he,dist_right_midpoint]
    norm_num
    linarith

lemma line_midConvex {c : ℝ → X} (hc : Isometry c) : C.MidConvex (range c) := by
  rintro _ ⟨s,rfl⟩ _ ⟨t,rfl⟩
  exact ⟨(s+t)/2,C.line_midpoint hc s t⟩

omit C in
lemma lineCoordinate_min [ProperSpace X] (c : ℝ → X) (hc : Isometry c) (x : X) (s : ℝ) :
    dist x (c (lineCoordinate c hc x)) ≤ dist x (c s) :=
  (exists_line_coordinate c hc x).choose_spec s

lemma lineCoordinate_unique [ProperSpace X] (c : ℝ → X) (hc : Isometry c) {x : X} {r : ℝ}
    (hm : ∀ s, dist x (c r) ≤ dist x (c s)) : lineCoordinate c hc x = r := by
  apply hc.injective
  apply C.projection_unique (C.line_midConvex hc) (mem_range_self _) (mem_range_self _)
  · rintro _ ⟨s,rfl⟩; exact lineCoordinate_min c hc x s
  · rintro _ ⟨s,rfl⟩; exact hm s

lemma lineCoordinate_nonexpansive [ProperSpace X] (c : ℝ → X) (hc : Isometry c) (x y : X) :
    dist (lineCoordinate c hc x) (lineCoordinate c hc y) ≤ dist x y := by
  rw [← hc.dist_eq]
  apply C.projection_nonexpansive (C.line_midConvex hc) (mem_range_self _) (mem_range_self _)
  · rintro _ ⟨s,rfl⟩; exact lineCoordinate_min c hc x s
  · rintro _ ⟨s,rfl⟩; exact lineCoordinate_min c hc y s

lemma lineCoordinate_shift [ProperSpace X] (c : ℝ → X) (hc : Isometry c)
    {f : X → X} (hf : Isometry f) (L : ℝ) (hshift : ∀ t, f (c t) = c (t+L)) (x : X) :
    lineCoordinate c hc (f x) = lineCoordinate c hc x + L := by
  apply C.lineCoordinate_unique c hc
  intro s
  rw [← hshift]
  have he : c s = f (c (s-L)) := by rw [hshift]; congr 1; ring
  rw [he,hf.dist_eq,hf.dist_eq]
  exact lineCoordinate_min c hc x (s-L)

omit C in

lemma nonexpansive_of_period {u : ℝ → ℝ} (hu : ∀ s t, dist (u s) (u t) ≤ dist s t)
    {L : ℝ} (hL : 0 < L) (hp : ∀ t, u (t+L) = u t + L) (t : ℝ) : u t = u 0 + t := by
  have hn (n : ℕ) (s : ℝ) : u (s+(n:ℝ)*L) = u s + (n:ℝ)*L := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ]
      rw [show s+((n:ℝ)+1)*L = (s+(n:ℝ)*L)+L by ring,hp,ih]
      ring
  obtain ⟨n,hnn⟩ := exists_nat_gt (|t|/L)
  have hb : |t| < (n:ℝ)*L := (div_lt_iff₀ hL).mp hnn
  have hpos := hn n 0
  have hneg := hn n (-(n:ℝ)*L)
  simp only [zero_add] at hpos
  have hz : -(n:ℝ)*L+(n:ℝ)*L = 0 := by ring
  rw [hz] at hneg
  have h1 := hu t ((n:ℝ)*L)
  have h2 := hu t (-(n:ℝ)*L)
  rw [Real.dist_eq,Real.dist_eq,hpos] at h1
  rw [Real.dist_eq,Real.dist_eq] at h2
  rw [abs_of_nonpos (by linarith [le_abs_self t] : t-(n:ℝ)*L ≤ 0)] at h1
  rw [abs_of_nonneg (by linarith [neg_abs_le t] : 0 ≤ t- -(n:ℝ)*L)] at h2
  have ha := (abs_le.mp h1).1
  have hb := (abs_le.mp h2).2
  linarith

lemma parallel_line_coordinate [ProperSpace X] (c d : ℝ → X) (hc : Isometry c) (hd : Isometry d)
    {f : X → X} (hf : Isometry f) {L : ℝ} (hL : 0 < L)
    (hfc : ∀ t, f (c t) = c (t+L)) (hfd : ∀ t, f (d t) = d (t+L)) (t : ℝ) :
    lineCoordinate c hc (d t) = lineCoordinate c hc (d 0) + t := by
  apply nonexpansive_of_period (L := L) (fun s t => ?_) hL (fun s => ?_) t
  · exact (C.lineCoordinate_nonexpansive c hc _ _).trans_eq (hd.dist_eq s t)
  · rw [← hfd,C.lineCoordinate_shift c hc hf L hfc]

end

section
variable {X : Type*} [MetricSpace X] (C : CNMidpoint X)

lemma bounded_midpoint_convex_constant {r : ℝ → ℝ}
    (hm : ∀ s t, r ((s+t)/2) ≤ (r s+r t)/2)
    {B : ℝ} (hB : ∀ t, r t ≤ B) (s t : ℝ) : r t ≤ r s := by
  have hh (n : ℕ) : ∀ u, r u ≤ (1-(1/2:ℝ)^n)*r s + (1/2:ℝ)^n*B := by
    induction n with
    | zero => simpa using hB
    | succ n ih =>
      intro u
      have hc := hm s (2*u-s)
      rw [show (s+(2*u-s))/2=u by ring] at hc
      rw [pow_succ (1/2:ℝ) n]
      linarith [ih (2*u-s)]
  have ht : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hl := ge_of_tendsto (((tendsto_const_nhds.sub ht).mul_const (r s)).add (ht.mul_const B))
    (Filter.Eventually.of_forall (fun n => hh n t))
  simpa using hl

include C
lemma parallel_line_separation [ProperSpace X] (c d : ℝ → X) (hc : Isometry c) (hd : Isometry d)
    {f : X → X} (hf : Isometry f) {L : ℝ} (hL : 0 < L)
    (hfc : ∀ t, f (c t) = c (t+L)) (hfd : ∀ t, f (d t) = d (t+L))
    (a t : ℝ) : dist (c (a+t)) (d t) = dist (c a) (d 0) := by
  let r : ℝ → ℝ := fun s => dist (c (a+s)) (d s)
  have hr : Continuous r := (hc.continuous.comp (continuous_const.add continuous_id)).dist hd.continuous
  have hp : Function.Periodic r L := by
    intro s
    change dist (c (a+(s+L))) (d (s+L)) = dist (c (a+s)) (d s)
    rw [← add_assoc,← hfc,← hfd,hf.dist_eq]
  obtain ⟨B,hB⟩ := (hp.compact_of_continuous (ne_of_gt hL) hr).bddAbove
  have hb (s : ℝ) : r s ≤ B := hB (mem_range_self s)
  have hm (s u : ℝ) : r ((s+u)/2) ≤ (r s+r u)/2 := by
    have hh := C.mid_convex (c (a+s)) (c (a+u)) (d s) (d u)
    rw [← C.line_midpoint hc,← C.line_midpoint hd] at hh
    convert hh using 1 ; dsimp [r]
    congr 3
    ring
  have he : r t = r 0 := le_antisymm (bounded_midpoint_convex_constant hm hb 0 t)
    (bounded_midpoint_convex_constant hm hb t 0)
  simpa only [r,add_zero] using he

theorem parallel_line_distance [ProperSpace X] (c d : ℝ → X) (hc : Isometry c) (hd : Isometry d)
    {f : X → X} (hf : Isometry f) {L : ℝ} (hL : 0 < L)
    (hfc : ∀ t, f (c t) = c (t+L)) (hfd : ∀ t, f (d t) = d (t+L)) (s t : ℝ) :
    dist (c s) (d t)^2 =
      (s-(lineCoordinate c hc (d 0)+t))^2 + dist (c (lineCoordinate c hc (d 0))) (d 0)^2 := by
  let a := lineCoordinate c hc (d 0)
  let R := dist (c a) (d 0)
  have hsep := C.parallel_line_separation c d hc hd hf hL hfc hfd a
  have hlow (u v : ℝ) : (u-v)^2+R^2 ≤ dist (c (a+u)) (d v)^2 := by
    have ha := C.projection_angle (C.line_midConvex hc)
      (mem_range_self (lineCoordinate c hc (d v)))
      (x := d v) (fun z hz => by
        obtain ⟨w,rfl⟩ := hz
        exact lineCoordinate_min c hc (d v) w) (mem_range_self (a+u))
    rw [C.parallel_line_coordinate c d hc hd hf hL hfc hfd] at ha
    change dist (d v) (c (a+v))^2 + dist (c (a+v)) (c (a+u))^2 ≤ _ at ha
    rw [dist_comm (d v) (c (a+v)),hsep v,hc.dist_eq,Real.dist_eq,sq_abs,
      dist_comm (d v) (c (a+u))] at ha
    dsimp [R]
    nlinarith
  have he (u v : ℝ) : dist (c (a+u)) (d v)^2 = (u-v)^2+R^2 := by
    have hq := C.quadrilateral (c (a+u)) (c (a+v)) (d v) (d u)
    rw [hc.dist_eq,hd.dist_eq,dist_comm (d u) (c (a+u)),hsep u,hsep v,
      Real.dist_eq,Real.dist_eq,sq_abs,sq_abs] at hq
    have h1 := hlow u v
    have h2 := hlow v u
    dsimp [R] at h1 h2 ⊢
    nlinarith
  have hh := he (s-a) t
  rw [show a+(s-a)=s by ring] at hh
  change dist (c s) (d t)^2 = (s-(a+t))^2+R^2
  nlinarith

end

section
variable {X : Type*} [MetricSpace X] [ProperSpace X] (C : CNMidpoint X)

include C
lemma centralizer_line_distance {f : X ≃ᵢ X} (c : ℝ → X) (hc : Isometry c)
    {L : ℝ} (hL : 0 < L) (hfc : ∀ t, f (c t) = c (t+L))
    (g : X ≃ᵢ X) (hfg : Commute f g) (s t : ℝ) :
    dist (c s) (g (c t))^2 = (s-t)^2 - 2*(s-t)*axisShift c hc g + dist (c 0) (g (c 0))^2 := by
  have hcomm (u : ℝ) : f (g (c u)) = g (c (u+L)) := by
    calc f (g (c u)) = g (f (c u)) := congrArg (fun e : X ≃ᵢ X => e (c u)) hfg.eq
         _ = _ := congrArg g (hfc u)
  have hh := C.parallel_line_distance c (fun u => g (c u)) hc
    (g.isometry.comp hc) f.isometry hL hfc hcomm s t
  have h0 := C.parallel_line_distance c (fun u => g (c u)) hc
    (g.isometry.comp hc) f.isometry hL hfc hcomm 0 0
  dsimp [axisShift] at *
  nlinarith

omit C in
lemma linear_bounded_zero {a B : ℝ} (h : ∀ t : ℝ, a*t ≤ B) : a = 0 := by
  by_contra ha
  have hh := h ((B+1)/a)
  have he : a*((B+1)/a)=B+1 := by field_simp
  rw [he] at hh
  linarith

lemma axisShift_mul {f : X ≃ᵢ X} (c : ℝ → X) (hc : Isometry c)
    {L : ℝ} (hL : 0 < L) (hfc : ∀ t, f (c t) = c (t+L))
    (g h : X ≃ᵢ X) (hfg : Commute f g) (hfh : Commute f h) :
    axisShift c hc (g*h) = axisShift c hc g + axisShift c hc h := by
  let a := axisShift c hc g
  let b := axisShift c hc h
  let e := axisShift c hc (g*h)
  have hb (s : ℝ) : (2*(a+b-e))*s ≤ a^2+2*a*b+dist (c 0) (h (c 0))^2 := by
    have hq := C.quadrilateral (c s) (g (c (s-a))) (g (h (c 0))) (c 0)
    have hgh : Commute f (g*h) := hfg.mul_right hfh
    have h1 := C.centralizer_line_distance c hc hL hfc (g*h) hgh s 0
    have h2 := C.centralizer_line_distance c hc hL hfc g hfg 0 (s-a)
    have h3 := C.centralizer_line_distance c hc hL hfc g hfg s (s-a)
    have h4 := C.centralizer_line_distance c hc hL hfc h hfh (s-a) 0
    change dist (c s) (g (h (c 0)))^2 = _ at h1
    rw [dist_comm (g (c (s-a))) (c 0),dist_comm (g (h (c 0))) (c 0),
      g.isometry.dist_eq,hc.dist_eq,Real.dist_eq,sq_abs] at hq
    dsimp [a,b,e] at *
    nlinarith
  have hh := linear_bounded_zero hb
  dsimp [a,b,e] at hh
  linarith

end

section
variable {X : Type*} [MetricSpace X] (C : CNMidpoint X)

include C
end

variable {X : Type*} [MetricSpace X] (C : CNMidpoint X)
include C

end ThreeManifold.NonpositiveMetric.CNMidpoint
end

open Set Filter Topology Function
namespace ThreeManifold.NonpositiveMetric.CNMidpoint
variable {X : Type*} [MetricSpace X] [ProperSpace X] (C : CNMidpoint X)
include C

end ThreeManifold.NonpositiveMetric.CNMidpoint

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.NonpositiveMetric OAI.ThreeManifold.NonpositiveMetric.CNMidpoint
open Set Filter Topology Function


theorem solution : type_of% @_root_.OAI.ThreeManifold.NonpositiveMetric.CNMidpoint.axisShift_mul := @_root_.OAI.ThreeManifold.NonpositiveMetric.CNMidpoint.axisShift_mul
