-- Prove2me | solution 1 for OAI.ThreeManifold.NonpositiveMetric.CNMidpoint.cyclic_shear_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:29:03.401576+00:00
-- url     : https://prove2.me/submissions/9f78ba2b-d06c-4949-ac07-81b14cdb718d

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Convexity.lean:L696-L729
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.NonpositiveMetric.CNMidpoint.cyclic_shear_obstruction. The node keeps its source
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
import Theorems.Thm_OAI_ThreeManifold_NonpositiveMetric_CNMidpoint_axisShift_mul
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
lemma mid_isometry {f : X → X} (hf : Isometry f) (x y : X) :
    f (C.mid x y) = C.mid (f x) (f y) := by
  apply C.eq_mid_of_dist_le
  · rw [hf.dist_eq,hf.dist_eq,dist_comm,C.mid_dist_left]
  · rw [hf.dist_eq,hf.dist_eq,dist_comm,C.mid_dist_right]

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

lemma minimum_step_two {f : X → X} (hf : Isometry f) {x : X}
    (hm : ∀ y, dist x (f x) ≤ dist y (f y)) : dist x (f (f x)) = 2*dist x (f x) := by
  have hlow := hm (C.mid x (f x))
  rw [C.mid_isometry hf] at hlow
  have hb := C.mid_common x (f (f x)) (f x)
  rw [C.mid_comm (f (f x)) (f x)] at hb
  have hu := dist_triangle x (f x) (f (f x))
  rw [hf.dist_eq] at hu
  linarith

lemma minimum_midpoint {f : X → X} (hf : Isometry f) {x : X}
    (hm : ∀ y, dist x (f x) ≤ dist y (f y)) :
    f x = C.mid x (f (f x)) := by
  apply C.eq_mid_of_dist_le
  · rw [C.minimum_step_two hf hm]
    linarith
  · rw [dist_comm,hf.dist_eq,C.minimum_step_two hf hm]
    linarith
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
lemma isometry_iterate {f : X → X} (hf : Isometry f) (n : ℕ) : Isometry (f^[n]) := by
  induction n with
  | zero => exact isometry_id
  | succ n ih => simpa only [Function.iterate_succ] using ih.comp hf
include C

lemma minimum_iterate_displacement {f : X → X} (hf : Isometry f) {x : X}
    (n : ℕ) : dist (f^[n] x) (f (f^[n] x)) = dist x (f x) := by
  let _ := C
  rw [← Function.iterate_succ_apply' f n x,Function.iterate_succ_apply f n x]
  exact (isometry_iterate hf n).dist_eq x (f x)

theorem minimizing_orbit_linear {f : X → X} (hf : Isometry f) {x : X}
    (hm : ∀ y, dist x (f x) ≤ dist y (f y)) (n : ℕ) :
    dist x (f^[n] x) = (n:ℝ)*dist x (f x) := by
  let L := dist x (f x)
  have hL : 0 ≤ L := dist_nonneg
  have htwo : dist x (f (f x)) = 2*L := C.minimum_step_two hf hm
  have hmid : f x = C.mid x (f (f x)) := C.minimum_midpoint hf hm
  have hmidn (k : ℕ) : f^[k+1] x = C.mid (f^[k] x) (f^[k+2] x) := by
    have hh := congrArg (f^[k]) hmid
    rw [C.mid_isometry (isometry_iterate hf k)] at hh
    simpa only [Function.iterate_succ_apply] using hh
  have htwon (k : ℕ) : dist (f^[k] x) (f^[k+2] x) = 2*L := by
    convert ((isometry_iterate hf k).dist_eq x (f (f x))).trans htwo using 1
    simp only [Function.iterate_succ_apply]
  have hstep (k : ℕ) (hk : dist x (f^[k] x) = (k:ℝ)*L)
      (hk1 : dist x (f^[k+1] x) = ((k:ℝ)+1)*L) :
      dist x (f^[k+2] x) = ((k:ℝ)+2)*L := by
    have hh := C.cn (f^[k] x) (f^[k+2] x) x
    rw [← hmidn k,dist_comm (f^[k+1] x) x,dist_comm (f^[k] x) x,
      dist_comm (f^[k+2] x) x,htwon,hk,hk1] at hh
    have hu := dist_triangle x (f^[k+1] x) (f^[k+2] x)
    have he := C.minimum_iterate_displacement (x := x) hf (k+1)
    rw [← Function.iterate_succ_apply' f (k+1) x] at he
    rw [he,hk1] at hu
    have hd : 0 ≤ dist x (f^[k+2] x) := dist_nonneg
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [mul_nonneg hk0 hL]
  have hall : ∀ k : ℕ, dist x (f^[k] x) = (k:ℝ)*L ∧
      dist x (f^[k+1] x) = ((k:ℝ)+1)*L := by
    intro k
    induction k with
    | zero => simp [L]
    | succ k ih =>
      constructor
      · simpa only [Nat.cast_add,Nat.cast_one] using ih.2
      · have hh := hstep k ih.1 ih.2
        simpa only [Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using hh
  exact (hall n).1
end

section
variable {X : Type*} [MetricSpace X] (C : CNMidpoint X)

lemma minset_closed {f : X → X} (hf : Isometry f) : IsClosed (minset f) := by
  have he : minset f = ⋂ y, {x | dist x (f x) ≤ dist y (f y)} := by
    ext x
    simp [minset]
  rw [he]
  exact isClosed_iInter fun y => isClosed_le (continuous_id.dist hf.continuous) continuous_const

lemma minset_midConvex {f : X → X} (hf : Isometry f) : C.MidConvex (minset f) := by
  intro x hx y hy z
  have hh := C.mid_convex x y (f x) (f y)
  rw [← C.mid_isometry hf] at hh
  have he : dist x (f x) = dist y (f y) := le_antisymm (hx y) (hy x)
  rw [← he] at hh
  exact hh.trans (by linarith [hx z])

lemma minset_map {f g : X → X} (hg : Isometry g) (hcomm : Function.Commute f g)
    {x : X} (hx : x ∈ minset f) : g x ∈ minset f := by
  intro y
  rw [hcomm x,hg.dist_eq]
  exact hx y

lemma minset_preimage {f g : X → X} (hg : Isometry g) (hcomm : Function.Commute f g)
    {x : X} (hx : g x ∈ minset f) : x ∈ minset f := by
  intro y
  have hh := hx y
  rw [hcomm x,hg.dist_eq] at hh
  exact hh

include C

theorem commuting_common_minimum [ProperSpace X] {f g : X → X}
    (hf : Isometry f) (hg : Isometry g) (hgs : Surjective g)
    (hcomm : Function.Commute f g) (hfmin : (minset f).Nonempty)
    {x : X} (hgmin : x ∈ minset g) :
    ∃ p, p ∈ minset f ∧ p ∈ minset g := by
  obtain ⟨p,hp,hm⟩ := exists_projection (minset_closed hf) hfmin x
  have hgp := minset_map hg hcomm hp
  have hgm : ∀ z ∈ minset f, dist (g x) (g p) ≤ dist (g x) z := by
    intro z hz
    obtain ⟨w,rfl⟩ := hgs z
    rw [hg.dist_eq,hg.dist_eq]
    exact hm w (minset_preimage hg hcomm hz)
  have hle := C.projection_nonexpansive (C.minset_midConvex hf) hp hgp hm hgm
  exact ⟨p,hp,fun z => hle.trans (hgmin z)⟩

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
lemma lineCoordinate_self (c : ℝ → X) (hc : Isometry c) (t : ℝ) :
    lineCoordinate c hc (c t) = t := by
  apply C.lineCoordinate_unique c hc
  intro s
  rw [dist_self]
  exact dist_nonneg

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

lemma axisShift_one (c : ℝ → X) (hc : Isometry c) : axisShift c hc 1 = 0 := by
  exact C.lineCoordinate_self c hc 0

lemma axisShift_self {f : X ≃ᵢ X} (c : ℝ → X) (hc : Isometry c)
    {L : ℝ} (hfc : ∀ t, f (c t) = c (t+L)) : axisShift c hc f = L := by
  dsimp [axisShift]
  rw [hfc,zero_add,C.lineCoordinate_self]

lemma axisShift_inv {f : X ≃ᵢ X} (c : ℝ → X) (hc : Isometry c)
    {L : ℝ} (hL : 0 < L) (hfc : ∀ t, f (c t) = c (t+L))
    (g : X ≃ᵢ X) (hfg : Commute f g) : axisShift c hc g⁻¹ = -axisShift c hc g := by
  have hh := C.axisShift_mul c hc hL hfc g g⁻¹ hfg hfg.inv_right
  rw [mul_inv_cancel,C.axisShift_one] at hh
  linarith

lemma axisShift_commutator {f : X ≃ᵢ X} (c : ℝ → X) (hc : Isometry c)
    {L : ℝ} (hL : 0 < L) (hfc : ∀ t, f (c t) = c (t+L))
    (g h : X ≃ᵢ X) (hfg : Commute f g) (hfh : Commute f h) :
    axisShift c hc (g*h*g⁻¹*h⁻¹) = 0 := by
  rw [C.axisShift_mul c hc hL hfc _ _ ((hfg.mul_right hfh).mul_right hfg.inv_right) hfh.inv_right,
    C.axisShift_mul c hc hL hfc _ _ (hfg.mul_right hfh) hfg.inv_right,
    C.axisShift_mul c hc hL hfc _ _ hfg hfh,
    C.axisShift_inv c hc hL hfc _ hfg,C.axisShift_inv c hc hL hfc _ hfh]
  ring

end

section
variable {X : Type*} [MetricSpace X] (C : CNMidpoint X)

lemma equiv_pow_iterate (f : X ≃ᵢ X) (n : ℕ) (x : X) : (f^n) x = f^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ',IsometryEquiv.mul_apply,ih,Function.iterate_succ_apply']

include C
lemma minimizing_zpow_dist (f : X ≃ᵢ X) {x : X}
    (hm : ∀ y, dist x (f x) ≤ dist y (f y)) (k : ℤ) :
    dist x ((f^k) x) = |(k:ℝ)| * dist x (f x) := by
  have hn (n : ℕ) : dist x ((f^n) x) = (n:ℝ)*dist x (f x) := by
    rw [equiv_pow_iterate]
    exact C.minimizing_orbit_linear f.isometry hm n
  rcases Int.eq_nat_or_neg k with ⟨n,rfl | rfl⟩
  · simpa using hn n
  · rw [zpow_neg,zpow_natCast]
    have hh := (f^n).isometry.dist_eq x ((f^n)⁻¹ x)
    rw [IsometryEquiv.apply_inv_self] at hh
    rw [← hh,dist_comm,hn]
    simp

lemma minimizing_zpow_dist_pair (f : X ≃ᵢ X) {x : X}
    (hm : ∀ y, dist x (f x) ≤ dist y (f y)) (k l : ℤ) :
    dist ((f^k) x) ((f^l) x) = |(l:ℝ)-(k:ℝ)| * dist x (f x) := by
  have he : (f^k) ((f^(l-k)) x) = (f^l) x := by
    rw [← IsometryEquiv.mul_apply,← zpow_add]
    congr 2
    omega
  rw [← he,(f^k).isometry.dist_eq,C.minimizing_zpow_dist f hm,Int.cast_sub]

omit C in
lemma axisJoin_shift (f : X ≃ᵢ X) (q : ℝ → X) (t : ℝ) :
    axisJoin f q (t+1) = f (axisJoin f q t) := by
  simp only [axisJoin,Int.floor_add_one,Int.fract_add_one,zpow_add,zpow_one]
  rw [IsometryEquiv.mul_apply]
  have hh : f ^ Int.floor t * f = f * f ^ Int.floor t := (Commute.refl f).zpow_left _
  exact congrArg (fun e : X ≃ᵢ X => e (q (Int.fract t))) hh

omit C in
lemma axisJoin_zero (f : X ≃ᵢ X) (q : ℝ → X) : axisJoin f q 0 = q 0 := by
  simp [axisJoin]

omit C in
lemma axisJoin_start_dist (f : X ≃ᵢ X) {q : ℝ → X} {x : X} {L : ℝ}
    (hq0 : q 0 = x) (hqd : ∀ s t, dist (q s) (q t) = |s-t| * L) (t : ℝ) :
    dist ((f^Int.floor t) x) (axisJoin f q t) = Int.fract t * L := by
  rw [axisJoin,← hq0,(f^Int.floor t).isometry.dist_eq,hqd]
  simp only [zero_sub,abs_neg,abs_of_nonneg (Int.fract_nonneg t)]

omit C in
lemma axisJoin_end_dist (f : X ≃ᵢ X) {q : ℝ → X} {x : X} {L : ℝ}
    (hq1 : q 1 = f x) (hqd : ∀ s t, dist (q s) (q t) = |s-t| * L) (t : ℝ) :
    dist (axisJoin f q t) ((f^(Int.floor t+1)) x) = (1-Int.fract t) * L := by
  rw [axisJoin,zpow_add,zpow_one,IsometryEquiv.mul_apply,← hq1,
    (f^Int.floor t).isometry.dist_eq,hqd,abs_of_nonpos (by linarith [Int.fract_lt_one t])]
  ring

lemma axisJoin_dist (f : X ≃ᵢ X) {q : ℝ → X} {x : X}
    (hm : ∀ y, dist x (f x) ≤ dist y (f y)) (hq0 : q 0 = x) (hq1 : q 1 = f x)
    (hqd : ∀ s t, dist (q s) (q t) = |s-t| * dist x (f x)) (s t : ℝ) :
    dist (axisJoin f q s) (axisJoin f q t) = |s-t| * dist x (f x) := by
  suffices hh : ∀ s t : ℝ, s ≤ t →
      dist (axisJoin f q s) (axisJoin f q t) = (t-s)*dist x (f x) by
    rcases le_total s t with h | h
    · rw [hh s t h,abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [dist_comm,hh t s h,abs_of_nonneg (sub_nonneg.mpr h)]
  intro s t hst
  let L := dist x (f x)
  have hL : 0 ≤ L := dist_nonneg
  have hfl : Int.floor s ≤ Int.floor t := Int.floor_mono hst
  have hs := axisJoin_start_dist f hq0 hqd s
  have ht := axisJoin_end_dist f hq1 hqd t
  have hlo := dist_triangle ((f^Int.floor s) x) (axisJoin f q s) ((f^(Int.floor t+1)) x)
  have hlo2 := dist_triangle (axisJoin f q s) (axisJoin f q t) ((f^(Int.floor t+1)) x)
  rw [C.minimizing_zpow_dist_pair f hm,Int.cast_add,Int.cast_one,
    abs_of_nonneg (by exact_mod_cast (show 0 ≤ Int.floor t+1-Int.floor s by omega)),hs] at hlo
  rw [ht] at hlo2
  have hslow : (Int.floor s:ℝ)+Int.fract s=s := by dsimp only [Int.fract]; ring
  have htlow : (Int.floor t:ℝ)+Int.fract t=t := by dsimp only [Int.fract]; ring
  have hu : dist (axisJoin f q s) (axisJoin f q t) ≤ (t-s)*L := by
    rcases eq_or_lt_of_le hfl with he | hlt
    · rw [axisJoin,axisJoin,← he,(f^Int.floor s).isometry.dist_eq,hqd]
      have hh : Int.fract s - Int.fract t = s-t := by simp only [Int.fract,he]; ring
      rw [hh,abs_of_nonpos (sub_nonpos.mpr hst)]
      dsimp [L]; nlinarith
    · have h1 := dist_triangle (axisJoin f q s) ((f^(Int.floor s+1)) x) (axisJoin f q t)
      have h2 := dist_triangle ((f^(Int.floor s+1)) x) ((f^Int.floor t) x) (axisJoin f q t)
      rw [axisJoin_end_dist f hq1 hqd] at h1
      rw [C.minimizing_zpow_dist_pair f hm,Int.cast_add,Int.cast_one,
        abs_of_nonneg (by exact_mod_cast (show 0 ≤ Int.floor t-(Int.floor s+1) by omega)),
        axisJoin_start_dist f hq0 hqd] at h2
      dsimp [L] at *
      nlinarith
  dsimp [L] at *
  nlinarith

end

variable {X : Type*} [MetricSpace X] (C : CNMidpoint X)
include C

theorem exists_minimizing_axis (f : X ≃ᵢ X) {x : X}
    (hm : ∀ y, dist x (f x) ≤ dist y (f y)) (hL : 0 < dist x (f x))
    (hs : ∃ q : ℝ → X, q 0 = x ∧ q 1 = f x ∧
      ∀ s t, dist (q s) (q t) = |s-t| * dist x (f x)) :
    ∃ c : ℝ → X, Isometry c ∧ c 0 = x ∧
      ∀ t, f (c t) = c (t+dist x (f x)) := by
  obtain ⟨q,hq0,hq1,hqd⟩ := hs
  let L := dist x (f x)
  let c : ℝ → X := fun t => axisJoin f q (t/L)
  refine ⟨c,?_,?_,?_⟩
  · apply Isometry.of_dist_eq
    intro s t
    dsimp only [c]
    rw [C.axisJoin_dist f hm hq0 hq1 hqd,← sub_div,abs_div,abs_of_pos hL,Real.dist_eq]
    exact div_mul_cancel₀ _ (ne_of_gt hL)
  · simpa only [c,zero_div,axisJoin_zero] using hq0
  · intro t
    dsimp only [c,L]
    rw [show (t+dist x (f x))/dist x (f x) = t/dist x (f x)+1 by
      field_simp,axisJoin_shift]
end ThreeManifold.NonpositiveMetric.CNMidpoint
end

open Set Filter Topology Function
namespace ThreeManifold.NonpositiveMetric.CNMidpoint
variable {X : Type*} [MetricSpace X] [ProperSpace X] (C : CNMidpoint X)
include C

theorem cyclic_shear_obstruction
    (hs : ∀ x y : X, ∃ q : ℝ → X, q 0 = x ∧ q 1 = y ∧
      ∀ s t, dist (q s) (q t) = |s-t| * dist x y)
    (f h a b c d : X ≃ᵢ X)
    (hfmin : (minset f).Nonempty) (hhmin : (minset h).Nonempty)
    (hfpos : ∀ x, f x ≠ x) (hhpos : ∀ x, h x ≠ x)
    (hfh : Commute f h) (hfa : Commute f a) (hfb : Commute f b)
    (hhc : Commute h c) (hhd : Commute h d)
    (hrel : h = a*b*a⁻¹*b⁻¹) (hrel2 : h*f = c*d*c⁻¹*d⁻¹) : False := by
  obtain ⟨x,hx⟩ := hhmin
  have hcom : Function.Commute (f : X → X) (h : X → X) :=
    fun y => congrArg (fun e : X ≃ᵢ X => e y) hfh.eq
  obtain ⟨p,hpf,hph⟩ := C.commuting_common_minimum f.isometry h.isometry h.surjective hcom hfmin hx
  have hLf : 0 < dist p (f p) := dist_pos.mpr (Ne.symm (hfpos p))
  have hLh : 0 < dist p (h p) := dist_pos.mpr (Ne.symm (hhpos p))
  obtain ⟨u,hu,hu0,huf⟩ := C.exists_minimizing_axis f hpf hLf (hs p (f p))
  obtain ⟨v,hv,hv0,hvh⟩ := C.exists_minimizing_axis h hph hLh (hs p (h p))
  have hτu : axisShift u hu h = 0 := by
    rw [hrel]
    exact C.axisShift_commutator u hu hLf huf a b hfa hfb
  have hτv : axisShift v hv f = -dist p (h p) := by
    have hz : axisShift v hv (h*f) = 0 := by
      rw [hrel2]
      exact C.axisShift_commutator v hv hLh hvh c d hhc hhd
    rw [C.axisShift_mul v hv hLh hvh h f (Commute.refl h) hfh.symm,
      C.axisShift_self v hv hvh] at hz
    linarith
  have hfu : u (dist p (f p)) = f p := by simpa [hu0] using (huf 0).symm
  have hhv : v (dist p (h p)) = h p := by simpa [hv0] using (hvh 0).symm
  have h1 := C.centralizer_line_distance u hu hLf huf h hfh (dist p (f p)) 0
  have h2 := C.centralizer_line_distance v hv hLh hvh f hfh.symm (dist p (h p)) 0
  rw [hu0,hfu,hτu] at h1
  rw [hv0,hhv,hτv,dist_comm (h p) (f p)] at h2
  nlinarith

end ThreeManifold.NonpositiveMetric.CNMidpoint

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.NonpositiveMetric OAI.ThreeManifold.NonpositiveMetric.CNMidpoint
open Set Filter Topology Function


theorem solution : type_of% @_root_.OAI.ThreeManifold.NonpositiveMetric.CNMidpoint.cyclic_shear_obstruction := @_root_.OAI.ThreeManifold.NonpositiveMetric.CNMidpoint.cyclic_shear_obstruction
