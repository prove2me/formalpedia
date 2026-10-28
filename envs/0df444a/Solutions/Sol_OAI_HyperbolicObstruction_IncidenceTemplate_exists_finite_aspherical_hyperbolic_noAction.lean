-- Prove2me | solution 1 for OAI.HyperbolicObstruction.IncidenceTemplate.exists_finite_aspherical_hyperbolic_noAction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T05:54:21.766459+00:00
-- url     : https://prove2.me/submissions/fbee0915-702c-468c-bf8c-b3955c69e789

import Mathlib
import Definitions.Def_HyperbolicObstruction
import Definitions.Def_OAIQ034H011

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_CATZero
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.TangentRay.instPseudoMetricSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap

noncomputable section

noncomputable section
namespace HyperbolicObstruction

namespace ConeData
variable {X : Type*} [MetricSpace X] (T : ConeData X)

theorem normSq_nonneg (x : X) : 0 ≤ T.normSq x := sq_nonneg _

theorem scale_mul {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (x : X) :
    T.scale r (T.scale s x) = T.scale (r * s) x := by
  have hd := T.dist_sq (T.scale r (T.scale s x)) (T.scale (r * s) x)
  rw [T.normSq_scale hr, T.normSq_scale hs, T.normSq_scale (mul_nonneg hr hs),
    T.pairing_scale hr (mul_nonneg hr hs), T.pairing_scale_left hs,
    T.pairing_self] at hd
  apply dist_eq_zero.mp
  nlinarith [sq_nonneg (dist (T.scale r (T.scale s x)) (T.scale (r * s) x))]

theorem pairing_add_left (h : CATZero X) (x y : X) :
    T.pairing x (T.add h x y) = T.normSq x + T.pairing x y := by
  unfold add
  rw [T.pairing_scale_right (by norm_num)]
  unfold pairing
  rw [T.normSq_mid h, CATZero.dist_left_mid h]
  ring

theorem pairing_add_right (h : CATZero X) (x y : X) :
    T.pairing y (T.add h x y) = T.pairing x y + T.normSq y := by
  unfold add
  rw [T.pairing_scale_right (by norm_num)]
  unfold pairing
  rw [T.normSq_mid h, dist_comm y (CATZero.mid h x y), CATZero.dist_mid_right h]
  ring


@[simp] theorem add_vertex (h : CATZero X) (x : X) :
    T.add h x T.vertex = x := by
  have hn := T.normSq_add h x T.vertex
  have hp := T.pairing_add_left h x T.vertex
  rw [T.pairing_comm x T.vertex, T.pairing_vertex] at hn hp
  rw [T.normSq_vertex] at hn
  have hd := T.dist_sq x (T.add h x T.vertex)
  rw [hn, hp] at hd
  symm
  exact dist_eq_zero.mp (by nlinarith [dist_nonneg (x := x) (y := T.add h x T.vertex)])

theorem Opposite.symm {c d : X} (hop : T.Opposite c d) : T.Opposite d c := by
  refine ⟨hop.1.symm, ?_⟩
  rw [T.pairing_comm, hop.2, hop.1]

theorem Parallel.symm {c d x : X} (hx : T.Parallel c d x) : T.Parallel d c x := by
  unfold Parallel at *
  linarith

theorem normSq_translate (h : CATZero X) (c x : X) {t : ℝ} (ht : 0 ≤ t) :
    T.normSq (T.translate h c t x) =
      T.normSq x + t ^ 2 * T.normSq c + 2 * t * T.pairing c x := by
  unfold translate
  rw [T.normSq_add h, T.normSq_scale ht, T.pairing_scale_right ht,
    T.pairing_comm x c]
  ring

theorem pairing_translate_base (h : CATZero X) (c x : X) {t : ℝ} (ht : 0 ≤ t) :
    T.pairing x (T.translate h c t x) = T.normSq x + t * T.pairing c x := by
  unfold translate
  rw [T.pairing_add_left h, T.pairing_scale_right ht, T.pairing_comm x c]

theorem pairing_translate_axis (h : CATZero X) (c x : X) {t : ℝ} (ht : 0 ≤ t) :
    T.pairing c (T.translate h c t x) = T.pairing c x + t * T.normSq c := by
  rcases eq_or_lt_of_le ht with he | hpos
  · subst t
    simp [translate, T.scale_zero, T.add_vertex]
  · have hp := T.pairing_add_right h x (T.scale t c)
    rw [T.pairing_scale_left ht, T.pairing_scale_right ht, T.normSq_scale ht,
      T.pairing_comm x c] at hp
    change t * T.pairing c (T.translate h c t x) = _ at hp
    nlinarith

theorem pairing_translate_ge (h : CATZero X) (c x w : X) {t : ℝ} (ht : 0 ≤ t) :
    T.pairing w x + t * T.pairing w c ≤ T.pairing w (T.translate h c t x) := by
  have hp := T.pairing_add h w x (T.scale t c)
  rwa [T.pairing_scale_right ht] at hp

/-- Translating towards either end of an axis preserves its parallel set. -/
theorem parallel_translate (h : CATZero X) {c d x : X} (hop : T.Opposite c d)
    (hx : T.Parallel c d x) {t : ℝ} (ht : 0 ≤ t) :
    T.Parallel c d (T.translate h c t x) := by
  have hz := T.opposite_pairing h hop (T.translate h c t x)
  have hp := T.pairing_translate_ge h c x d ht
  rw [T.pairing_comm d c, hop.2] at hp
  unfold Parallel at hx ⊢
  rw [T.pairing_translate_axis h c x ht] at hz ⊢
  nlinarith

/-- The two cone translations are inverse on the parallel set. -/
theorem translate_inverse (h : CATZero X) {c d x : X} (hop : T.Opposite c d)
    (hx : T.Parallel c d x) {t : ℝ} (ht : 0 ≤ t) :
    T.translate h d t (T.translate h c t x) = x := by
  have hyp := T.parallel_translate h hop hx ht
  have hyc := T.pairing_translate_axis h c x ht
  have hy := T.normSq_translate h c x ht
  have hz := T.normSq_translate h d (T.translate h c t x) ht
  have hzx := T.pairing_translate_ge h d (T.translate h c t x) x ht
  rw [T.pairing_translate_base h c x ht, T.pairing_comm x d] at hzx
  have hd := T.dist_sq x (T.translate h d t (T.translate h c t x))
  unfold Parallel at hx hyp
  rw [← hop.1] at hz
  have hnorm : T.normSq (T.translate h d t (T.translate h c t x)) = T.normSq x := by
    nlinarith
  rw [hnorm] at hd
  symm
  apply dist_eq_zero.mp
  nlinarith [dist_nonneg (x := x) (y := T.translate h d t (T.translate h c t x))]

/-- Exact scalar-product translation formula on the parallel set. It is the
needed parallel-set splitting identity, proved without a product theorem. -/
theorem pairing_translate (h : CATZero X) {c d x y : X} (hop : T.Opposite c d)
    (hx : T.Parallel c d x) (hy : T.Parallel c d y) {t : ℝ} (ht : 0 ≤ t) :
    T.pairing x (T.translate h c t y) = T.pairing x y + t * T.pairing c x := by
  have hlo := T.pairing_translate_ge h c y x ht
  have hhi := T.pairing_translate_ge h d (T.translate h c t y) x ht
  rw [T.translate_inverse h hop hy ht, T.pairing_comm x d] at hhi
  rw [T.pairing_comm x c] at hlo
  unfold Parallel at hx
  nlinarith


theorem add_comm (h : CATZero X) (x y : X) : T.add h x y = T.add h y x := by
  have hm : CATZero.mid h y x = CATZero.mid h x y := by
    apply CATZero.eq_segment_of_dist h (t := 1 / 2) (by norm_num)
    · rw [dist_comm x (CATZero.mid h y x), CATZero.dist_mid_right h, dist_comm y x]
      ring
    · rw [dist_comm (CATZero.mid h y x) y, CATZero.dist_left_mid h, dist_comm y x]
      ring
  unfold add
  rw [hm]

theorem pairing_translates_same (h : CATZero X) {c d x y : X}
    (hop : T.Opposite c d) (hx : T.Parallel c d x) (hy : T.Parallel c d y)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    T.pairing (T.translate h c s x) (T.translate h c t y) =
      T.pairing x y + s * T.pairing c y + t * T.pairing c x +
        s * t * T.normSq c := by
  rw [T.pairing_translate h hop (T.parallel_translate h hop hx hs) hy ht,
    T.pairing_comm (T.translate h c s x) y, T.pairing_translate h hop hy hx hs,
    T.pairing_translate_axis h c x hs, T.pairing_comm y x]
  ring

theorem pairing_translates_opposite (h : CATZero X) {c d x y : X}
    (hop : T.Opposite c d) (hx : T.Parallel c d x) (hy : T.Parallel c d y)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    T.pairing (T.translate h c s x) (T.translate h d t y) =
      T.pairing x y + s * T.pairing c y - t * T.pairing c x -
        s * t * T.normSq c := by
  have hpx := T.parallel_translate h hop hx hs
  have hc := T.pairing_translate_axis h c x hs
  rw [T.pairing_translate h (hop.symm T) (hpx.symm T) (hy.symm T) ht,
    T.pairing_comm (T.translate h c s x) y, T.pairing_translate h hop hy hx hs,
    T.pairing_comm y x]
  unfold Parallel at hpx
  nlinarith

/-- Opposite orthogonal pairs have opposite cone sums. This is a small
flat-square rigidity statement, using the proved translation identity. -/
theorem opposite_add_of_orthogonal (h : CATZero X) {u u' v v' : X}
    (hu : T.Opposite u u') (hv : T.Opposite v v')
    (huv : T.pairing u v = 0) (huv' : T.pairing u v' = 0)
    (hu'v : T.pairing u' v = 0) (hu'v' : T.pairing u' v' = 0) :
    T.Opposite (T.add h u v) (T.add h u' v') := by
  have hpv : T.Parallel u u' v := by simp [Parallel, huv, hu'v]
  have hpv' : T.Parallel u u' v' := by simp [Parallel, huv', hu'v']
  have hp := T.pairing_translates_opposite h hu hpv hpv'
    (s := 1) (t := 1) (by norm_num) (by norm_num)
  simp only [translate, T.scale_one, one_mul, mul_one, huv, huv', hv.2,
    T.add_comm h v u, T.add_comm h v' u'] at hp
  constructor
  · rw [T.normSq_add h, T.normSq_add h, huv, hu'v', hu.1, hv.1]
  · rw [hp, T.normSq_add h, huv]
    ring

/-- Unit vectors satisfy the lower Cauchy bound without any ambient linear
structure. This is just the triangle inequality of the cone. -/
theorem pairing_unit_lower {x y : X} (hx : T.normSq x = 1) (hy : T.normSq y = 1) :
    -1 ≤ T.pairing x y := by
  have hnx : dist T.vertex x = 1 := by
    dsimp [normSq] at hx
    nlinarith [dist_nonneg (x := T.vertex) (y := x)]
  have hny : dist T.vertex y = 1 := by
    dsimp [normSq] at hy
    nlinarith [dist_nonneg (x := T.vertex) (y := y)]
  have hd := dist_triangle x T.vertex y
  rw [dist_comm x T.vertex, hnx, hny] at hd
  unfold pairing
  rw [hx, hy]
  nlinarith [dist_nonneg (x := x) (y := y)]

/-- Source Lemma `geom:antipodal`, in an algebraic form that avoids a
local-to-global theorem in the completed space of directions. -/
theorem exceptional_antipodes (h : CATZero X) {c d x y z : X}
    (hc : T.normSq c = 1) (hd : T.normSq d = 1)
    (hdy : T.pairing d y = 1 / 2) (hdx : T.pairing d x = 1 / 2)
    (hyz : T.Opposite y z) (hz : z = T.add h c x) : T.Opposite c d := by
  have hp := T.opposite_pairing h hyz d
  rw [T.pairing_comm y d, T.pairing_comm z d, hdy] at hp
  have hs := T.pairing_add h d c x
  rw [← hz, hdx, T.pairing_comm d c] at hs
  have hlo := T.pairing_unit_lower hc hd
  constructor
  · rw [hc, hd]
  · rw [hc]
    linarith


theorem eq_of_normSq_pairing {x y : X} (hn : T.normSq x = T.normSq y)
    (hp : T.normSq x ≤ T.pairing x y) : x = y := by
  have hd := T.dist_sq x y
  rw [← hn] at hd
  apply dist_eq_zero.mp
  nlinarith [dist_nonneg (x := x) (y := y)]

theorem pairing_add_add (h : CATZero X) (x y u v : X) :
    T.pairing x u + T.pairing x v + T.pairing y u + T.pairing y v ≤
      T.pairing (T.add h x y) (T.add h u v) := by
  have ha := T.pairing_add h (T.add h u v) x y
  have hx := T.pairing_add h x u v
  have hy := T.pairing_add h y u v
  rw [T.pairing_comm (T.add h u v) x, T.pairing_comm (T.add h u v) y,
    T.pairing_comm (T.add h u v) (T.add h x y)] at ha
  linarith

theorem add_eq_of_pairings (h : CATZero X) {x y u v : X}
    (hn : T.normSq (T.add h x y) = T.normSq (T.add h u v))
    (hp : T.normSq (T.add h x y) ≤
      T.pairing x u + T.pairing x v + T.pairing y u + T.pairing y v) :
    T.add h x y = T.add h u v :=
  T.eq_of_normSq_pairing hn (hp.trans (T.pairing_add_add h x y u v))

/-- The transverse-square conclusion used in the final obstruction. The
four original vectors are not assumed to lie in a plane or a vector space. -/
theorem opposite_cross_sums (h : CATZero X) {p q r s : X}
    (hnp : T.normSq p = 3 / 4) (hnq : T.normSq q = 3 / 4)
    (hnr : T.normSq r = 3 / 4) (hns : T.normSq s = 3 / 4)
    (hpq : T.pairing p q = -1 / 4) (hpr : T.pairing p r = -1 / 4)
    (hps : T.pairing p s = -1 / 4) (hqr : T.pairing q r = -1 / 4)
    (hqs : T.pairing q s = -1 / 4) (hrs : T.pairing r s = -1 / 4)
    (hop : T.Opposite (T.add h p q) (T.add h r s)) :
    T.Opposite (T.add h p r) (T.add h q s) := by
  let c := T.add h p q
  let d := T.add h r s
  change T.Opposite c d at hop
  have hc : T.normSq c = 1 := by simp [c, T.normSq_add, hnp, hnq, hpq]; norm_num
  have hd : T.normSq d = 1 := by simp [d, T.normSq_add, hnr, hns, hrs]; norm_num
  have hcp : T.pairing c p = 1 / 2 := by
    rw [T.pairing_comm]; dsimp [c]; rw [T.pairing_add_left, hnp, hpq]; norm_num
  have hcq : T.pairing c q = 1 / 2 := by
    rw [T.pairing_comm]; dsimp [c]; rw [T.pairing_add_right, hnq, hpq]; norm_num
  have hdr : T.pairing d r = 1 / 2 := by
    rw [T.pairing_comm]; dsimp [d]; rw [T.pairing_add_left, hnr, hrs]; norm_num
  have hds : T.pairing d s = 1 / 2 := by
    rw [T.pairing_comm]; dsimp [d]; rw [T.pairing_add_right, hns, hrs]; norm_num
  have hcr : T.pairing c r = -1 / 2 := by
    have hlo := T.pairing_add h r p q
    rw [T.pairing_comm r p, T.pairing_comm r q, hpr, hqr,
      T.pairing_comm r (T.add h p q)] at hlo
    have hhi := T.opposite_pairing h hop r
    rw [hdr] at hhi
    change _ ≤ T.pairing c r at hlo
    linarith
  have hcs : T.pairing c s = -1 / 2 := by
    have hlo := T.pairing_add h s p q
    rw [T.pairing_comm s p, T.pairing_comm s q, hps, hqs,
      T.pairing_comm s (T.add h p q)] at hlo
    have hhi := T.opposite_pairing h hop s
    rw [hds] at hhi
    change _ ≤ T.pairing c s at hlo
    linarith
  have hdp : T.pairing d p = -1 / 2 := by
    have hlo := T.pairing_add h p r s
    rw [hpr, hps, T.pairing_comm p (T.add h r s)] at hlo
    have hhi := T.opposite_pairing h hop p
    rw [hcp] at hhi
    change _ ≤ T.pairing d p at hlo
    linarith
  have hdq : T.pairing d q = -1 / 2 := by
    have hlo := T.pairing_add h q r s
    rw [hqr, hqs, T.pairing_comm q (T.add h r s)] at hlo
    have hhi := T.opposite_pairing h hop q
    rw [hcq] at hhi
    change _ ≤ T.pairing d q at hlo
    linarith
  have hpp : T.Parallel c d p := by norm_num [Parallel, hcp, hdp]
  have hpq' : T.Parallel c d q := by norm_num [Parallel, hcq, hdq]
  have hpr' : T.Parallel c d r := by norm_num [Parallel, hcr, hdr]
  have hps' : T.Parallel c d s := by norm_num [Parallel, hcs, hds]
  let u := T.translate h d (1 / 2) p
  let u' := T.translate h d (1 / 2) q
  let v := T.translate h c (1 / 2) r
  let v' := T.translate h c (1 / 2) s
  have hnu : T.normSq u = 1 / 2 := by
    dsimp [u]; rw [T.normSq_translate h d p (by norm_num), hnp, hd, hdp]; norm_num
  have hnu' : T.normSq u' = 1 / 2 := by
    dsimp [u']; rw [T.normSq_translate h d q (by norm_num), hnq, hd, hdq]; norm_num
  have hnv : T.normSq v = 1 / 2 := by
    dsimp [v]; rw [T.normSq_translate h c r (by norm_num), hnr, hc, hcr]; norm_num
  have hnv' : T.normSq v' = 1 / 2 := by
    dsimp [v']; rw [T.normSq_translate h c s (by norm_num), hns, hc, hcs]; norm_num
  have huu' : T.pairing u u' = -1 / 2 := by
    dsimp [u, u']
    rw [T.pairing_translates_same h (hop.symm T) (hpp.symm T) (hpq'.symm T)
      (by norm_num) (by norm_num), hpq, hdp, hdq, hd]
    norm_num
  have hvv' : T.pairing v v' = -1 / 2 := by
    dsimp [v, v']
    rw [T.pairing_translates_same h hop hpr' hps' (by norm_num) (by norm_num),
      hrs, hcr, hcs, hc]
    norm_num
  have huv : T.pairing u v = 0 := by
    dsimp [u, v]
    rw [T.pairing_translates_opposite h (hop.symm T) (hpp.symm T) (hpr'.symm T)
      (by norm_num) (by norm_num), hpr, hdp, hdr, hd]
    norm_num
  have huv' : T.pairing u v' = 0 := by
    dsimp [u, v']
    rw [T.pairing_translates_opposite h (hop.symm T) (hpp.symm T) (hps'.symm T)
      (by norm_num) (by norm_num), hps, hdp, hds, hd]
    norm_num
  have hu'v : T.pairing u' v = 0 := by
    dsimp [u', v]
    rw [T.pairing_translates_opposite h (hop.symm T) (hpq'.symm T) (hpr'.symm T)
      (by norm_num) (by norm_num), hqr, hdq, hdr, hd]
    norm_num
  have hu'v' : T.pairing u' v' = 0 := by
    dsimp [u', v']
    rw [T.pairing_translates_opposite h (hop.symm T) (hpq'.symm T) (hps'.symm T)
      (by norm_num) (by norm_num), hqs, hdq, hds, hd]
    norm_num
  have hu : T.Opposite u u' := by constructor <;> norm_num [hnu, hnu', huu']
  have hv : T.Opposite v v' := by constructor <;> norm_num [hnv, hnv', hvv']
  have ha : T.add h p r = T.add h u v := by
    apply T.add_eq_of_pairings h
    · norm_num [T.normSq_add, hnp, hnr, hpr, hnu, hnv, huv]
    · have hpu := T.pairing_translate h (hop.symm T) (hpp.symm T) (hpp.symm T)
        (t := 1 / 2) (by norm_num)
      have hpv := T.pairing_translate h hop hpp hpr' (t := 1 / 2) (by norm_num)
      have hru := T.pairing_translate h (hop.symm T) (hpr'.symm T) (hpp.symm T)
        (t := 1 / 2) (by norm_num)
      have hrv := T.pairing_translate h hop hpr' hpr' (t := 1 / 2) (by norm_num)
      change T.pairing p u = _ at hpu
      change T.pairing p v = _ at hpv
      change T.pairing r u = _ at hru
      change T.pairing r v = _ at hrv
      rw [T.normSq_add, hnp, hnr, hpr, hpu, hpv, hru, hrv,
        T.pairing_self, T.pairing_self, hnp, hdp, hpr, hcp, T.pairing_comm r p,
        hpr, hdr, hnr, hcr]
      norm_num
  have hb : T.add h q s = T.add h u' v' := by
    apply T.add_eq_of_pairings h
    · norm_num [T.normSq_add, hnq, hns, hqs, hnu', hnv', hu'v']
    · have hqu := T.pairing_translate h (hop.symm T) (hpq'.symm T) (hpq'.symm T)
        (t := 1 / 2) (by norm_num)
      have hqv := T.pairing_translate h hop hpq' hps' (t := 1 / 2) (by norm_num)
      have hsu := T.pairing_translate h (hop.symm T) (hps'.symm T) (hpq'.symm T)
        (t := 1 / 2) (by norm_num)
      have hsv := T.pairing_translate h hop hps' hps' (t := 1 / 2) (by norm_num)
      change T.pairing q u' = _ at hqu
      change T.pairing q v' = _ at hqv
      change T.pairing s u' = _ at hsu
      change T.pairing s v' = _ at hsv
      rw [T.normSq_add, hnq, hns, hqs, hqu, hqv, hsu, hsv,
        T.pairing_self, T.pairing_self, hnq, hdq, hqs, hcq, T.pairing_comm s q,
        hqs, hds, hns, hcs]
      norm_num
  rw [ha, hb]
  exact T.opposite_add_of_orthogonal h hu hv huv huv' hu'v hu'v'


/-- Final algebraic contradiction in Proposition `prop:no-configuration`.
The five line indices are AB, AC, AD, BC, BD, respectively. All geometric
input here is explicit; no Hilbert-space or associativity assumption is used. -/
theorem five_line_fans_contradiction (h : CATZero X) (ℓ : Fin 5 → X)
    (hn : ∀ i, T.normSq (ℓ i) = 3 / 4)
    (hp : ∀ i j, i ≠ j → T.pairing (ℓ i) (ℓ j) = -1 / 4)
    (hA : T.add h (ℓ 0) (ℓ 1) = T.add h (ℓ 1) (ℓ 2))
    (hB : T.add h (ℓ 0) (ℓ 3) = T.add h (ℓ 3) (ℓ 4))
    (hop : T.Opposite (T.add h (ℓ 1) (ℓ 3)) (T.add h (ℓ 2) (ℓ 4))) : False := by
  have hcross := T.opposite_cross_sums h (hn 1) (hn 3) (hn 2) (hn 4)
    (hp 1 3 (by decide)) (hp 1 2 (by decide)) (hp 1 4 (by decide))
    (hp 3 2 (by decide)) (hp 3 4 (by decide)) (hp 2 4 (by decide)) hop
  have hnorm : T.normSq (T.add h (ℓ 1) (ℓ 2)) = 1 := by
    rw [T.normSq_add, hn 1, hn 2, hp 1 2 (by decide)]
    norm_num
  have hneg := hcross.2
  rw [hnorm] at hneg
  have hpos := T.pairing_add_add h (ℓ 0) (ℓ 1) (ℓ 0) (ℓ 3)
  rw [T.pairing_self, hn 0, hp 0 3 (by decide), hp 1 0 (by decide),
    hp 1 3 (by decide), hA, hB] at hpos
  linarith

end ConeData
end HyperbolicObstruction

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeData
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section

noncomputable section
namespace HyperbolicObstruction
namespace ConeData
variable {X : Type*} [MetricSpace X] (T : ConeData X)

/-- Two-vector affine combinations in a metric cone agree with its metric
segments; associativity has not been assumed. -/
theorem segment_eq_add_scale (h : CATZero X) (x y : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    CATZero.segment h x y t = T.add h (T.scale (1 - t) x) (T.scale t y) := by
  let z := T.add h (T.scale (1 - t) x) (T.scale t y)
  have ht' : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  have hn := T.normSq_add h (T.scale (1 - t) x) (T.scale t y)
  rw [T.normSq_scale ht', T.normSq_scale ht.1, T.pairing_scale ht' ht.1] at hn
  have hpx := T.pairing_add h x (T.scale (1 - t) x) (T.scale t y)
  rw [T.pairing_scale_right ht', T.pairing_scale_right ht.1, T.pairing_self] at hpx
  have hpy := T.pairing_add h y (T.scale (1 - t) x) (T.scale t y)
  rw [T.pairing_scale_right ht', T.pairing_scale_right ht.1, T.pairing_self,
    T.pairing_comm y x] at hpy
  have hxz := T.dist_sq x z
  have hyz := T.dist_sq y z
  have hxy := T.dist_sq x y
  change T.normSq z = _ at hn
  change _ ≤ T.pairing x z at hpx
  change _ ≤ T.pairing y z at hpy
  have hx : dist x z ≤ t * dist x y := by
    nlinarith [mul_nonneg ht.1 (dist_nonneg (x := x) (y := y)),
      dist_nonneg (x := x) (y := z)]
  have hy : dist z y ≤ (1 - t) * dist x y := by
    rw [dist_comm]
    nlinarith [mul_nonneg ht' (dist_nonneg (x := x) (y := y)),
      dist_nonneg (x := y) (y := z)]
  have htri := dist_triangle x z y
  symm
  exact CATZero.eq_segment_of_dist h ht (by linarith) (by linarith)

theorem parallel_scale {c d x : X} (hx : T.Parallel c d x) {r : ℝ} (hr : 0 ≤ r) :
    T.Parallel c d (T.scale r x) := by
  unfold Parallel at hx ⊢
  rw [T.pairing_scale_right hr, T.pairing_scale_right hr]
  nlinarith

/-- Distance between opposite translations of one point in the parallel set. -/
theorem dist_opposite_translates_sq (h : CATZero X) {c d x : X}
    (hop : T.Opposite c d) (hx : T.Parallel c d x) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    dist (T.translate h c r x) (T.translate h d s x) ^ 2 =
      (r + s) ^ 2 * T.normSq c := by
  have hpx := T.parallel_translate h hop hx hr
  have hp := T.pairing_translate h hop.symm hpx.symm hx.symm hs
  rw [T.pairing_comm (T.translate h c r x) x, T.pairing_translate_base h c x hr] at hp
  have ha := T.pairing_translate_axis h c x hr
  unfold Parallel at hx hpx
  rw [T.dist_sq, T.normSq_translate h c x hr, T.normSq_translate h d x hs, hp, ← hop.1]
  nlinarith

theorem dist_opposite_segments_sq (h : CATZero X) {c d x : X}
    (hop : T.Opposite c d) (hx : T.Parallel c d x) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist (CATZero.segment h x c t) (CATZero.segment h x d t) ^ 2 = t ^ 2 * dist c d ^ 2 := by
  rw [T.segment_eq_add_scale h x c ht, T.segment_eq_add_scale h x d ht]
  change dist (T.translate h c t (T.scale (1 - t) x))
    (T.translate h d t (T.scale (1 - t) x)) ^ 2 = _
  rw [T.dist_opposite_translates_sq h hop (T.parallel_scale hx (sub_nonneg.mpr ht.2)) ht.1 ht.1,
    T.dist_sq c d, hop.2, ← hop.1]
  ring

end ConeData

end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
open Filter Topology UniformSpace
namespace TangentCone
variable {X : Type*} [MetricSpace X] (h : CATZero X)

/-- Equality in the original midpoint CN comparison puts the opposite
endpoint logs and the third log in their common parallel set, and the log
preserves both remaining triangle sides. -/
theorem midpoint_equality_parallel (o x y : X)
    (heq : dist o (CATZero.mid h x y) ^ 2 =
      (dist o x ^ 2 + dist o y ^ 2) / 2 - dist x y ^ 2 / 4) :
    (coneData h (CATZero.mid h x y)).Parallel
      (log h (CATZero.mid h x y) x) (log h (CATZero.mid h x y) y)
        (log h (CATZero.mid h x y) o) ∧
    dist (log h (CATZero.mid h x y) o) (log h (CATZero.mid h x y) x) = dist o x ∧
    dist (log h (CATZero.mid h x y) o) (log h (CATZero.mid h x y) y) = dist o y := by
  let m := CATZero.mid h x y
  let T := coneData h m
  let H := catZero h m
  have hop := opposite_mid_logs h x y
  have hc := T.opposite_pairing H hop (log h m o)
  have hx := pairing_log_ge h m x o
  have hy := pairing_log_ge h m y o
  have hmx : dist m x = dist x y / 2 := by
    rw [dist_comm]; exact CATZero.dist_left_mid h x y
  have hmy : dist m y = dist x y / 2 := CATZero.dist_mid_right h x y
  have hmo : dist m o ^ 2 = (dist o x ^ 2 + dist o y ^ 2) / 2 - dist x y ^ 2 / 4 := by
    rwa [dist_comm] at heq
  rw [hmx, hmo, dist_comm x o] at hx
  rw [hmy, hmo, dist_comm y o] at hy
  have hpar : T.Parallel (log h m x) (log h m y) (log h m o) := by
    unfold ConeData.Parallel
    dsimp only [T] at hc ⊢
    linarith
  refine ⟨hpar, ?_, ?_⟩
  · have hd := T.dist_sq (log h m x) (log h m o)
    dsimp only [T] at hd
    rw [normSq_log, normSq_log, hmx, hmo, dist_comm (log h m x) (log h m o)] at hd
    nlinarith [dist_nonneg (x := log h m o) (y := log h m x), dist_nonneg (x := o) (y := x)]
  · have hd := T.dist_sq (log h m y) (log h m o)
    dsimp only [T] at hd
    rw [normSq_log, normSq_log, hmy, hmo, dist_comm (log h m y) (log h m o)] at hd
    nlinarith [dist_nonneg (x := log h m o) (y := log h m y), dist_nonneg (x := o) (y := y)]

/-- The radial distance consequence of flat-triangle rigidity, proved via the
parallel set of the opposite logs at the midpoint. -/
theorem radial_distance_of_midpoint_equality (o x y : X)
    (heq : dist o (CATZero.mid h x y) ^ 2 =
      (dist o x ^ 2 + dist o y ^ 2) / 2 - dist x y ^ 2 / 4)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist (CATZero.segment h o x t) (CATZero.segment h o y t) = t * dist x y := by
  obtain ⟨hpar, hx, hy⟩ := midpoint_equality_parallel h o x y heq
  let m := CATZero.mid h x y
  let T := coneData h m
  let H := catZero h m
  have he := T.dist_opposite_segments_sq H (opposite_mid_logs h x y) hpar ht
  rw [← CATZero.map_segment_of_dist h H (log h m) (dist_log_le h m) o x hx ht,
    ← CATZero.map_segment_of_dist h H (log h m) (dist_log_le h m) o y hy ht,
    log_dist_mid_endpoints] at he
  have hlo := dist_log_le h m (CATZero.segment h o x t) (CATZero.segment h o y t)
  have hhi := CATZero.radial_contraction h o x y ht
  have hlo' := (sq_le_sq₀ dist_nonneg dist_nonneg).mpr hlo
  rw [he] at hlo'
  nlinarith [mul_nonneg ht.1 (dist_nonneg (x := x) (y := y)),
    dist_nonneg (x := CATZero.segment h o x t) (y := CATZero.segment h o y t)]

/-- The tangent log preserves the base side of a triangle with midpoint CN
equality. This is the exact flat-triangle transfer needed by the obstruction. -/
theorem log_dist_of_midpoint_equality (o x y : X)
    (heq : dist o (CATZero.mid h x y) ^ 2 =
      (dist o x ^ 2 + dist o y ^ 2) / 2 - dist x y ^ 2 / 4) :
    dist (log h o x) (log h o y) = dist x y := by
  rw [log, log, Completion.dist_eq, TangentRay.dist_def]
  change CATZero.tangentDist h o x y 1 1 = _
  apply tendsto_nhds_unique (CATZero.tangentDist_tendsto h o x y (by norm_num) (by norm_num))
  apply tendsto_const_nhds.congr'
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  filter_upwards [show ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t from eventually_mem_nhdsWithin,
    ht.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))] with t ht0 ht1
  rw [mul_one, radial_distance_of_midpoint_equality h o x y heq ⟨ht0.le, ht1⟩]
  field_simp

theorem log_mid_of_midpoint_equality (o x y : X)
    (heq : dist o (CATZero.mid h x y) ^ 2 =
      (dist o x ^ 2 + dist o y ^ 2) / 2 - dist x y ^ 2 / 4) :
    log h o (CATZero.mid h x y) = CATZero.mid (catZero h o) (log h o x) (log h o y) :=
  CATZero.map_segment_of_dist h (catZero h o) (log h o) (dist_log_le h o) x y
    (log_dist_of_midpoint_equality h o x y heq) (by norm_num)

end TangentCone
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
namespace CATZero
variable {X : Type*} [MetricSpace X]

/-- A CN equality at any nontrivial interior point implies equality at the
midpoint. The proof uses only convexity on the appropriate half-segment. -/
theorem midpoint_equality_of_interior (h : CATZero X) (o x y : X) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (heq : dist o (segment h x y t) ^ 2 = (1 - t) * dist o x ^ 2 + t * dist o y ^ 2 -
      t * (1 - t) * dist x y ^ 2) :
    dist o (mid h x y) ^ 2 = (dist o x ^ 2 + dist o y ^ 2) / 2 - dist x y ^ 2 / 4 := by
  have hhalf (a b : X) (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1 / 2)
      (he : dist o (segment h a b s) ^ 2 = (1 - s) * dist o a ^ 2 + s * dist o b ^ 2 -
        s * (1 - s) * dist a b ^ 2) :
      dist o (mid h a b) ^ 2 = (dist o a ^ 2 + dist o b ^ 2) / 2 - dist a b ^ 2 / 4 := by
    have hc := segment_cn h a (mid h a b) o (t := 2 * s) ⟨by positivity, by linarith⟩
    have hsm : segment h a (mid h a b) (2 * s) = segment h a b s := by
      unfold mid
      rw [segment_mul h a b ⟨by positivity, by linarith⟩ (by norm_num)]
      congr 1
      ring
    rw [hsm, he, dist_left_mid] at hc
    apply le_antisymm (mid_cn h a b o)
    apply (mul_le_mul_iff_of_pos_left hs0).mp
    nlinarith
  by_cases htt : t ≤ 1 / 2
  · exact hhalf x y t ht.1 htt heq
  · have he : dist o (segment h y x (1 - t)) ^ 2 =
        (1 - (1 - t)) * dist o y ^ 2 + (1 - t) * dist o x ^ 2 -
          (1 - t) * (1 - (1 - t)) * dist y x ^ 2 := by
      rw [segment_reverse h x y ⟨ht.1.le, ht.2.le⟩, heq, dist_comm y x]
      ring
    have hh := hhalf y x (1 - t) (by linarith [ht.2]) (by linarith) he
    rw [mid_swap, dist_comm y x] at hh
    linarith

end CATZero

namespace TangentCone
variable {X : Type*} [MetricSpace X] (h : CATZero X)

theorem log_dist_of_interior_equality (o x y : X) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (heq : dist o (CATZero.segment h x y t) ^ 2 =
      (1 - t) * dist o x ^ 2 + t * dist o y ^ 2 - t * (1 - t) * dist x y ^ 2) :
    dist (log h o x) (log h o y) = dist x y :=
  log_dist_of_midpoint_equality h o x y (CATZero.midpoint_equality_of_interior h o x y ht heq)

end TangentCone
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
namespace ConeData
variable {X : Type*} [MetricSpace X] (T : ConeData X)

theorem dist_scale {r : ℝ} (hr : 0 ≤ r) (x y : X) :
    dist (T.scale r x) (T.scale r y) = r * dist x y := by
  have he := T.radial_metric r r hr hr x y
  nlinarith [dist_nonneg (x := T.scale r x) (y := T.scale r y),
    mul_nonneg hr (dist_nonneg (x := x) (y := y))]

theorem scale_segment (h : CATZero X) {r : ℝ} (hr : 0 ≤ r) (x y : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    T.scale r (CATZero.segment h x y t) =
      CATZero.segment h (T.scale r x) (T.scale r y) t := by
  apply CATZero.eq_segment_of_dist h ht
  · rw [T.dist_scale hr, T.dist_scale hr, CATZero.segment_left h x y ht]
    ring
  · rw [T.dist_scale hr, T.dist_scale hr, CATZero.segment_right h x y ht]
    ring

theorem scale_add (h : CATZero X) {r : ℝ} (hr : 0 ≤ r) (x y : X) :
    T.scale r (T.add h x y) = T.add h (T.scale r x) (T.scale r y) := by
  unfold add
  rw [T.scale_mul hr (by norm_num), mul_comm r 2,
    ← T.scale_mul (by norm_num) hr, CATZero.mid,
    T.scale_segment h hr x y (by norm_num)]
  rfl

end ConeData

namespace TangentCone
open Filter Topology UniformSpace
variable {X : Type*} [MetricSpace X] (h : CATZero X)

theorem log_radial (o x : X) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    log h o (CATZero.segment h o x t) = (coneData h o).scale t (log h o x) := by
  change log h o (CATZero.segment h o x t) = scaleN h o t.toNNReal (log h o x)
  rw [log, log, scaleN_coe]
  apply dist_eq_zero.mp
  rw [Completion.dist_eq, TangentRay.dist_def]
  dsimp only [TangentRay.log, TangentRay.scale, NNReal.coe_one, NNReal.coe_mul, mul_one]
  rw [Real.coe_toNNReal _ ht.1, mul_one,
    CATZero.tangentDist_radial_left h o x x ht (by norm_num) ht.1,
    one_mul, CATZero.tangentDist_same]
  simp

/-- Equality of distances at all sufficiently small radial fractions transfers
exactly to the completed tangent cone. -/
theorem log_dist_of_radial_equal (o x y : X)
    (heq : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      dist (CATZero.segment h o x t) (CATZero.segment h o y t) = t * dist x y) :
    dist (log h o x) (log h o y) = dist x y := by
  rw [log, log, Completion.dist_eq, TangentRay.dist_def]
  change CATZero.tangentDist h o x y 1 1 = _
  apply tendsto_nhds_unique (CATZero.tangentDist_tendsto h o x y (by norm_num) (by norm_num))
  apply tendsto_const_nhds.congr'
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  filter_upwards [show ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t from eventually_mem_nhdsWithin,
    ht.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))] with t ht0 ht1
  rw [mul_one, heq t ⟨ht0, ht1⟩]
  field_simp

/-- The fixed-fraction angle test of the source suffices; no exchange of
ultralimits and angles is used. -/
theorem log_dist_of_right_fractional (o x y : X)
    (hsq : dist x y ^ 2 = dist o x ^ 2 + dist o y ^ 2)
    (hlower : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      t ^ 2 * (dist o x ^ 2 + dist o y ^ 2) ≤
        dist (CATZero.segment h o x t) (CATZero.segment h o y t) ^ 2) :
    dist (log h o x) (log h o y) = dist x y := by
  apply log_dist_of_radial_equal h o x y
  intro t ht
  have hc := CATZero.radial_contraction h o x y ⟨ht.1.le, ht.2⟩
  have hl := hlower t ht
  rw [← hsq] at hl
  nlinarith [mul_nonneg ht.1.le (dist_nonneg (x := x) (y := y)),
    dist_nonneg (x := CATZero.segment h o x t) (y := CATZero.segment h o y t)]

end TangentCone
end HyperbolicObstruction

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_CATZeroFurther
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section

namespace HyperbolicObstruction
namespace CATZero
variable {X : Type*} [MetricSpace X]

/-- The midpoint part of square rigidity, retaining just the metric data
needed later. -/
theorem square_mid (h : CATZero X) {p q r s : X}
    (hpq : dist p q ^ 2 = 1) (hqr : dist q r ^ 2 = 1)
    (hrs : dist r s ^ 2 = 1) (hsp : dist s p ^ 2 = 1)
    (hpr : dist p r ^ 2 = 2) (hqs : dist q s ^ 2 = 2) :
    mid h p r = mid h q s := by
  have hq := quadrilateral h p q r s
  rw [hpq, hqr, hrs, hsp, hpr, hqs] at hq
  apply dist_eq_zero.mp
  nlinarith [dist_nonneg (x := mid h p r) (y := mid h q s)]

end CATZero
namespace TangentCone
variable {X : Type*} [MetricSpace X] (h : CATZero X)

/-- The fan midpoint identity, derived from a metric square and the central
flatness of its line diagonal. -/
theorem fan_identity (c x y a b : X)
    (hcx : dist c x ^ 2 = 3 / 4) (hcy : dist c y ^ 2 = 3 / 4)
    (hca : dist c a ^ 2 = 3 / 4) (hcb : dist c b ^ 2 = 3 / 4)
    (hxa : dist x a ^ 2 = 1) (hay : dist a y ^ 2 = 1)
    (hyb : dist y b ^ 2 = 1) (hbx : dist b x ^ 2 = 1)
    (hxy : dist x y ^ 2 = 2) (hab : dist a b ^ 2 = 2)
    (hflat : dist c (CATZero.mid h a b) ^ 2 = 1 / 4) :
    (coneData h c).pairing (log h c x) (log h c y) = -1 / 4 ∧
    (coneData h c).add (catZero h c) (log h c x) (log h c y) =
      (coneData h c).add (catZero h c) (log h c a) (log h c b) := by
  have hm := CATZero.square_mid h hxa hay hyb hbx hxy hab
  have heab : dist c (CATZero.mid h a b) ^ 2 =
      (dist c a ^ 2 + dist c b ^ 2) / 2 - dist a b ^ 2 / 4 := by
    rw [hca, hcb, hab, hflat]
    norm_num
  have hexy : dist c (CATZero.mid h x y) ^ 2 =
      (dist c x ^ 2 + dist c y ^ 2) / 2 - dist x y ^ 2 / 4 := by
    rw [hm, hflat, hcx, hcy, hxy]
    norm_num
  constructor
  · unfold ConeData.pairing
    rw [normSq_log, normSq_log, log_dist_of_midpoint_equality h c x y hexy, hcx, hcy, hxy]
    norm_num
  · unfold ConeData.add
    rw [← log_mid_of_midpoint_equality h c x y hexy,
      ← log_mid_of_midpoint_equality h c a b heab, hm]

/-- Source exceptional-incidence identity. Its hypotheses are entirely metric,
including the fixed-fraction test; no flat triangle or cone identity is assumed. -/
theorem exceptional_identity (c p q z k : X)
    (hcp : dist c p ^ 2 = 3 / 4) (hcq : dist c q ^ 2 = 3 / 4)
    (hcz : dist c z ^ 2 = 3 / 4) (hck : dist c k ^ 2 = 3 / 4)
    (hpq : dist p q ^ 2 = 2) (hpz : dist p z ^ 2 = 2) (hqz : dist q z ^ 2 = 2)
    (hcj : dist c (CATZero.mid h p q) ^ 2 = 1 / 4)
    (hkj : dist k (CATZero.mid h p q) ^ 2 = 1 / 2) (hkz : dist k z ^ 2 = 1)
    (hfrac : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      t ^ 2 * (1 / 2 + 1) ≤ dist (CATZero.segment h k (CATZero.mid h p q) t)
        (CATZero.segment h k z t) ^ 2) :
    log h c k = (coneData h c).add (catZero h c)
      ((coneData h c).add (catZero h c) (log h c p) (log h c q)) (log h c z) := by
  let j := CATZero.mid h p q
  let b := CATZero.segment h j z (1 / 3)
  have hjz : dist j z ^ 2 = 3 / 2 := by
    have hlo := hfrac 1 (by norm_num)
    rw [(CATZero.segment_spec h k j).2.1, (CATZero.segment_spec h k z).2.1] at hlo
    have hhi := CATZero.mid_cn h p q z
    rw [dist_comm z p, dist_comm z q, hpz, hqz, hpq, dist_comm z j] at hhi
    norm_num at hlo
    linarith
  have hlogk : dist (log h k j) (log h k z) = dist j z := by
    apply log_dist_of_right_fractional h k j z
    · rw [hjz, hkj, hkz]
      norm_num
    · intro t ht
      rw [hkj, hkz]
      exact hfrac t ht
  have hkb : dist k b ^ 2 = 1 / 3 := by
    have he := cn_eq_of_log_dist h k j z hlogk (t := 1 / 3) (by norm_num)
    rw [hkj, hkz, hjz] at he
    dsimp only [b]
    linarith
  have hcb : dist c b ^ 2 ≤ 1 / 12 := by
    have he := CATZero.segment_cn h j z c (t := 1 / 3) (by norm_num)
    rw [hcj, hcz, hjz] at he
    exact le_trans he (by norm_num)
  have hkbl : dist k b = 2 / 3 * dist c k := by
    nlinarith [dist_nonneg (x := k) (y := b), dist_nonneg (x := c) (y := k)]
  have hcbl : dist c b = 1 / 3 * dist c k := by
    have htri := dist_triangle c b k
    rw [dist_comm b k, hkbl] at htri
    nlinarith [dist_nonneg (x := c) (y := b), dist_nonneg (x := c) (y := k)]
  have hb : b = CATZero.segment h c k (1 / 3) := by
    apply CATZero.eq_segment_of_dist h (by norm_num)
    · exact hcbl
    · rw [dist_comm, hkbl]
      ring
  have hec : dist c b ^ 2 =
      (1 - 1 / 3) * dist c j ^ 2 + (1 / 3) * dist c z ^ 2 -
        (1 / 3) * (1 - 1 / 3) * dist j z ^ 2 := by
    rw [hcbl, hcj, hcz, hjz, mul_pow, hck]
    norm_num
  have hlogc := log_dist_of_interior_equality h c j z (t := 1 / 3) (by norm_num) hec
  have hmap := CATZero.map_segment_of_dist h (catZero h c) (log h c) (dist_log_le h c)
    j z hlogc (t := 1 / 3) (by norm_num)
  have hlogb : log h c b = (coneData h c).scale (1 / 3) (log h c k) := by
    rw [hb, log_radial h c k (by norm_num)]
  have hsum : log h c k = (coneData h c).add (catZero h c)
      ((coneData h c).scale 2 (log h c j)) (log h c z) := by
    have he := congrArg ((coneData h c).scale 3) hmap
    change (coneData h c).scale 3 (log h c b) = _ at he
    rw [hlogb, (coneData h c).scale_mul (by norm_num) (by norm_num)] at he
    norm_num only [show (3 : ℝ) * (1 / 3) = 1 by norm_num, (coneData h c).scale_one] at he
    rw [(coneData h c).segment_eq_add_scale (catZero h c) _ _ (by norm_num),
      (coneData h c).scale_add (catZero h c) (by norm_num),
      (coneData h c).scale_mul (by norm_num) (by norm_num),
      (coneData h c).scale_mul (by norm_num) (by norm_num)] at he
    norm_num at he
    simpa only [(coneData h c).scale_one] using he
  have hepq : dist c j ^ 2 = (dist c p ^ 2 + dist c q ^ 2) / 2 - dist p q ^ 2 / 4 := by
    rw [hcj, hcp, hcq, hpq]
    norm_num
  rw [hsum, log_mid_of_midpoint_equality h c p q hepq]
  rfl

end TangentCone
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction

theorem MetricSquare.mid_eq {X : Type*} [MetricSpace X] {p q r s : X}
    (hs : MetricSquare p q r s) (h : CATZero X) : CATZero.mid h p r = CATZero.mid h q s :=
  CATZero.square_mid h hs.side₀ hs.side₁ hs.side₂ hs.side₃ hs.diagonal₀ hs.diagonal₁

/-- The complete finite CAT(0) metric obstruction from Section 6. The proof
constructs the completed tangent cone and all rigidity identities internally. -/
theorem no_finite_obstruction {X : Type*} [MetricSpace X] (h : CATZero X)
    (D : FiniteObstructionData h) : False := by
  let T := TangentCone.coneData h D.c
  let H := TangentCone.catZero h D.c
  let L : Fin 6 → TangentCone h D.c := fun i => TangentCone.log h D.c (D.line i)
  let U : Fin 4 → TangentCone h D.c := fun i => TangentCone.log h D.c (D.x i)
  let V : Fin 4 → TangentCone h D.c := fun i => TangentCone.log h D.c (D.y i)
  let M : Fin 4 → TangentCone h D.c := fun i => T.add H (U i) (V i)
  have hnL (i) : T.normSq (L i) = 3 / 4 := by
    exact (TangentCone.normSq_log h D.c (D.line i)).trans (D.radiusLine i)
  have hnU (i) : T.normSq (U i) = 3 / 4 := by
    exact (TangentCone.normSq_log h D.c (D.x i)).trans (D.radiusX i)
  have hnV (i) : T.normSq (V i) = 3 / 4 := by
    exact (TangentCone.normSq_log h D.c (D.y i)).trans (D.radiusY i)
  have hpL (a b) (hne : a ≠ b) : T.pairing (L a) (L b) = -1 / 4 := by
    have he : dist D.c (CATZero.mid h (D.line a) (D.line b)) ^ 2 =
        (dist D.c (D.line a) ^ 2 + dist D.c (D.line b) ^ 2) / 2 -
          dist (D.line a) (D.line b) ^ 2 / 4 := by
      rw [D.lineFlat a b hne, D.radiusLine a, D.radiusLine b, D.lineDist a b hne]
      norm_num
    have hd := TangentCone.log_dist_of_midpoint_equality h D.c (D.line a) (D.line b) he
    change dist (L a) (L b) = _ at hd
    rw [ConeData.pairing, hnL, hnL, hd, D.lineDist a b hne]
    norm_num
  have hfan (i a b) (ha : a ∈ fullLines i) (hb : b ∈ fullLines i) (hne : a ≠ b) :
      T.pairing (U i) (V i) = -1 / 4 ∧ M i = T.add H (L a) (L b) := by
    have hs := D.square i a b ha hb hne
    exact TangentCone.fan_identity h D.c (D.x i) (D.y i) (D.line a) (D.line b)
      (D.radiusX i) (D.radiusY i) (D.radiusLine a) (D.radiusLine b)
      hs.side₀ hs.side₁ hs.side₂ hs.side₃ hs.diagonal₀ hs.diagonal₁ (D.lineFlat a b hne)
  have hA₁ := hfan 0 0 1 (by decide) (by decide) (by decide)
  have hA₂ := hfan 0 1 2 (by decide) (by decide) (by decide)
  have hB₁ := hfan 1 0 3 (by decide) (by decide) (by decide)
  have hB₂ := hfan 1 3 4 (by decide) (by decide) (by decide)
  have hC := hfan 2 1 3 (by decide) (by decide) (by decide)
  have hD := hfan 3 2 4 (by decide) (by decide) (by decide)
  have hnM₂ : T.normSq (M 2) = 1 := by
    change T.normSq (T.add H (U 2) (V 2)) = 1
    rw [T.normSq_add, hnU, hnV, hC.1]
    norm_num
  have hnM₃ : T.normSq (M 3) = 1 := by
    change T.normSq (T.add H (U 3) (V 3)) = 1
    rw [T.normSq_add, hnU, hnV, hD.1]
    norm_num
  have hmy : T.pairing (M 3) (V 3) = 1 / 2 := by
    rw [T.pairing_comm]
    change T.pairing (V 3) (T.add H (U 3) (V 3)) = _
    rw [T.pairing_add_right, hD.1, hnV]
    norm_num
  have hmx : T.pairing (M 3) (U 3) = 1 / 2 := by
    rw [T.pairing_comm]
    change T.pairing (U 3) (T.add H (U 3) (V 3)) = _
    rw [T.pairing_add_left, hD.1, hnU]
    norm_num
  have hmid : D.c = CATZero.mid h (D.y 3) (D.line 5) := by
    have hc := CATZero.mid_cn h (D.y 3) (D.line 5) D.c
    rw [D.radiusY, D.radiusLine] at hc
    apply dist_eq_zero.mp
    nlinarith [D.missing, dist_nonneg (x := D.c) (y := CATZero.mid h (D.y 3) (D.line 5))]
  have hop : T.Opposite (V 3) (L 5) := by
    have he := TangentCone.opposite_mid_logs h (D.y 3) (D.line 5)
    rw [← hmid] at he
    exact he
  have hsC := D.square 2 5 1 (by decide) (by decide) (by decide)
  have hcj : dist D.c (CATZero.mid h (D.x 2) (D.y 2)) ^ 2 = 1 / 4 := by
    rw [hsC.mid_eq h]
    exact D.lineFlat 5 1 (by decide)
  have hkj : dist (D.line 5) (CATZero.mid h (D.x 2) (D.y 2)) ^ 2 = 1 / 2 := by
    rw [hsC.mid_eq h, CATZero.dist_left_mid, div_pow, D.lineDist 5 1 (by decide)]
    norm_num
  have hex : L 5 = T.add H (M 2) (U 3) :=
    TangentCone.exceptional_identity h D.c (D.x 2) (D.y 2) (D.x 3) (D.line 5)
      (D.radiusX 2) (D.radiusY 2) (D.radiusX 3) (D.radiusLine 5)
      hsC.diagonal₀ D.twoStepX D.twoStepY hcj hkj D.loose D.fractional
  have hopex : T.Opposite (M 2) (M 3) :=
    T.exceptional_antipodes H hnM₂ hnM₃ hmy hmx hop hex
  apply T.five_line_fans_contradiction H (fun i : Fin 5 => L i.castSucc)
  · intro i
    exact hnL i.castSucc
  · intro i j hij
    exact hpL i.castSucc j.castSucc (fun he => hij (Fin.ext (congrArg (fun k : Fin 6 => k.val) he)))
  · exact hA₁.2.symm.trans hA₂.2
  · exact hB₁.2.symm.trans hB₂.2
  · change T.Opposite (T.add H (L 1) (L 3)) (T.add H (L 2) (L 4))
    rw [← hC.2, ← hD.2]
    exact hopex

end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
namespace CATZero
open Filter Topology
variable {X : Type*} [MetricSpace X]

/-- The elementary endpoint estimate behind first variation: fixing one
radial endpoint changes a comparison product by at most a first-order error.
It follows from the triangle inequality and convexity of the real square. -/
theorem radialPairing_endpoint_gap (h : CATZero X) (o x y : X) {a b : ℝ}
    (ha : a ∈ Set.Ioc (0 : ℝ) 1) (hb : b ∈ Set.Ioc (0 : ℝ) 1) :
    2 * b * (radialPairing h o x y a b - radialPairing h o x y a 1) ≤
      a * dist o x ^ 2 := by
  let u := dist (segment h o x a) (segment h o y b)
  let v := dist (segment h o x a) y
  have htri : v ≤ u + (1 - b) * dist o y := by
    have he := dist_triangle (segment h o x a) (segment h o y b) y
    rw [segment_right h o y ⟨hb.1.le, hb.2⟩] at he
    exact he
  have huv : v ^ 2 ≤ (u + (1 - b) * dist o y) ^ 2 := by
    have hv : 0 ≤ v := dist_nonneg
    have hu : 0 ≤ u := dist_nonneg
    nlinarith [mul_nonneg (sub_nonneg.mpr hb.2) (dist_nonneg (x := o) (y := y))]
  have hs : b * v ^ 2 ≤ u ^ 2 + b * (1 - b) * dist o y ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left huv hb.1.le,
      mul_nonneg (sub_nonneg.mpr hb.2) (sq_nonneg (u - b * dist o y))]
  have he₁ : 2 * a * radialPairing h o x y a 1 =
      a ^ 2 * dist o x ^ 2 + dist o y ^ 2 - v ^ 2 := by
    dsimp [radialPairing, v]
    rw [(segment_spec h o y).2.1]
    field_simp [ha.1.ne', hb.1.ne']
  have he₂ : 2 * a * b * radialPairing h o x y a b =
      a ^ 2 * dist o x ^ 2 + b ^ 2 * dist o y ^ 2 - u ^ 2 := by
    dsimp [radialPairing, u]
    field_simp [ha.1.ne', hb.1.ne']
  apply (mul_le_mul_iff_of_pos_left ha.1).mp
  have he₁' := congrArg (fun z : ℝ => b * z) he₁
  nlinarith [mul_nonneg hb.1.le (mul_nonneg (sq_nonneg a) (sq_nonneg (dist o x)))]

/-- First-variation comparison product along a quadratic radial parameter.
This suffices for the minimizer argument and avoids any assumed angle theorem. -/
theorem radialPairing_endpoint_tendsto (h : CATZero X) (o x y : X) :
    Tendsto (fun t : ℝ => radialPairing h o x y (t ^ 2) 1) (𝓝[>] 0)
      (𝓝 (tangentPairing h o x y)) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have htp : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := eventually_mem_nhdsWithin
  have hlim := radialPairing_tendsto h o x y (by simpa using ht.pow 2) ht
    (htp.mono fun _ hh => sq_pos_of_pos hh) htp
  have hlo : Tendsto (fun t : ℝ => radialPairing h o x y (t ^ 2) t -
      t * dist o x ^ 2 / 2) (𝓝[>] 0) (𝓝 (tangentPairing h o x y)) := by
    simpa using hlim.sub ((ht.mul_const (dist o x ^ 2)).div_const 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [htp, ht.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with t ht0 ht1
    have hts : t ^ 2 ∈ Set.Ioc (0 : ℝ) 1 := ⟨sq_pos_of_pos ht0, by nlinarith⟩
    have he := radialPairing_endpoint_gap h o x y hts ⟨ht0, ht1⟩
    apply (mul_le_mul_iff_of_pos_left ht0).mp
    nlinarith
  · filter_upwards [htp, ht.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with t ht0 ht1
    exact radialPairing_le_tangentPairing h o x y ⟨sq_pos_of_pos ht0, by nlinarith⟩
      (by norm_num)

end CATZero
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
namespace CATZero
open Filter Topology
variable {X : Type*} [MetricSpace X] {ι : Type*} [Fintype ι]

/-- A finite squared-distance minimizer has nonpositive directional product
sum. The proof uses the actual comparison-product limit, not first variation
as an imported hypothesis. -/
theorem tangentPairing_sum_nonpos_of_minimum (h : CATZero X) (o : X) (y : ι → X)
    (hmin : ∀ x : X, (∑ i, dist o (y i) ^ 2) ≤ ∑ i, dist x (y i) ^ 2) (z : X) :
    (∑ i, tangentPairing h o z (y i)) ≤ 0 := by
  have hbound (a : ℝ) (ha : a ∈ Set.Ioc (0 : ℝ) 1) :
      (∑ i, radialPairing h o z (y i) a 1) ≤
        a * (Fintype.card ι : ℝ) * dist o z ^ 2 / 2 := by
    have he (i : ι) : dist (segment h o z a) (y i) ^ 2 =
        a ^ 2 * dist o z ^ 2 + dist o (y i) ^ 2 -
          2 * a * radialPairing h o z (y i) a 1 := by
      dsimp [radialPairing]
      rw [(segment_spec h o (y i)).2.1]
      field_simp [ha.1.ne']
      ring
    have hes := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun i _ => he i)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum] at hes
    have hm := hmin (segment h o z a)
    apply (mul_le_mul_iff_of_pos_left ha.1).mp
    nlinarith
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have htp : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := eventually_mem_nhdsWithin
  have hlim := tendsto_finsetSum Finset.univ
    (fun i _ => radialPairing_endpoint_tendsto h o z (y i))
  have hr : Tendsto (fun t : ℝ => t ^ 2 * (Fintype.card ι : ℝ) * dist o z ^ 2 / 2)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (((ht.pow 2).mul_const (Fintype.card ι : ℝ)).mul_const
      (dist o z ^ 2)).div_const 2
  apply le_of_tendsto_of_tendsto hlim hr
  filter_upwards [htp, ht.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with t ht0 ht1
  exact hbound (t ^ 2) ⟨sq_pos_of_pos ht0, by nlinarith⟩

end CATZero
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
namespace TangentCone
open UniformSpace
variable {X : Type*} [MetricSpace X] (h : CATZero X) (o : X)

theorem pairing_ray_log (p : TangentRay h o) (y : X) :
    (coneData h o).pairing (p : TangentCone h o) (log h o y) =
      (p.weight : ℝ) * CATZero.tangentPairing h o p.point y := by
  unfold ConeData.pairing ConeData.normSq
  change (dist (vertex h o) (p : TangentCone h o) ^ 2 +
    dist (vertex h o) (log h o y) ^ 2 - dist (p : TangentCone h o) (log h o y) ^ 2) / 2 = _
  rw [dist_vertex_log, vertex, log, Completion.dist_eq, Completion.dist_eq,
    TangentRay.dist_vertex, TangentRay.dist_sq]
  dsimp only [TangentRay.log, NNReal.coe_one]
  ring

/-- The tangent barycenter inequality at an actual finite squared-distance
minimizer, extended to the completed cone by density. -/
theorem pairing_sum_nonpos_of_minimum {ι : Type*} [Fintype ι] (y : ι → X)
    (hmin : ∀ x : X, (∑ i, dist o (y i) ^ 2) ≤ ∑ i, dist x (y i) ^ 2)
    (v : TangentCone h o) : (∑ i, (coneData h o).pairing v (log h o (y i))) ≤ 0 := by
  induction v using Completion.induction_on with
  | hp =>
    apply isClosed_le _ continuous_const
    unfold ConeData.pairing ConeData.normSq
    fun_prop
  | ih p =>
    simp_rw [pairing_ray_log]
    rw [← Finset.mul_sum]
    exact mul_nonpos_of_nonneg_of_nonpos p.weight.coe_nonneg
      (CATZero.tangentPairing_sum_nonpos_of_minimum h o y hmin p.point)

end TangentCone
end HyperbolicObstruction

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ClosedCoverGluing
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! Literal continuous gluing on locally finite closed covers. This is used for
cell-by-cell homotopies; it does not assume cell extensions exist. -/
noncomputable section
open scoped Topology unitInterval
namespace HyperbolicObstruction.ClosedCoverGluing
variable {J X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (S : J → Set X) (φ : ∀ j, C(S j,Y))
  (agree : ∀ i j x (hi : x ∈ S i) (hj : x ∈ S j), φ i ⟨x,hi⟩ = φ j ⟨x,hj⟩)
  (cover : ⋃ j, S j = Set.univ) (closed : ∀ j, IsClosed (S j))
  (finite : LocallyFinite S)

lemma gluePrism_apply (H : ∀ j, C(I × S j,Y))
    (ha : ∀ i j (t : I) x (hi : x ∈ S i) (hj : x ∈ S j),
      H i (t,⟨x,hi⟩) = H j (t,⟨x,hj⟩)) (j : J) (t : I) (x : S j) :
    gluePrism S cover closed finite H ha (t,x) = H j (t,x) := by
  dsimp only [gluePrism]
  exact glue_eq _ _ _ _ _ _ j (t,(x : X)) x.property

end HyperbolicObstruction.ClosedCoverGluing
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_GeometricAction
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section

namespace HyperbolicObstruction
namespace CATZero
variable {X : Type*} [MetricSpace X]

theorem dist_mid_mid_sq_le (h : CATZero X) (a b c d : X) :
    dist (mid h a b) (mid h c d) ^ 2 ≤ (dist a c ^ 2 + dist b d ^ 2) / 2 := by
  have he := dist_mid_mid_le h a b c d
  have hn := dist_nonneg (x := mid h a b) (y := mid h c d)
  have ha := dist_nonneg (x := a) (y := c)
  have hb := dist_nonneg (x := b) (y := d)
  nlinarith [sq_nonneg (dist a c - dist b d)]

theorem isometry_mid (h : CATZero X) (e : X ≃ᵢ X) (a b : X) :
    e (mid h a b) = mid h (e a) (e b) :=
  map_segment_of_dist h h e (fun a b => (e.isometry.dist_eq a b).le) a b
    (e.isometry.dist_eq a b) (by norm_num)

/-- Crossed-midpoint convexity turns a minimum of a symmetric displacement
energy into a minimum of the squared distances to the fixed orbit tuple. -/
theorem orbit_minimum_of_energy_minimum {ι : Type*} [Fintype ι]
    (h : CATZero X) (e : ι → X ≃ᵢ X) (σ : ι ≃ ι)
    (hinv : ∀ i, e (σ i) = (e i).symm) (o : X)
    (hmin : ∀ y : X, (∑ i, dist o (e i o) ^ 2) ≤ ∑ i, dist y (e i y) ^ 2) :
    ∀ y : X, (∑ i, dist o (e i o) ^ 2) ≤ ∑ i, dist y (e i o) ^ 2 := by
  intro y
  have hc (i : ι) : dist (mid h o y) (e i (mid h o y)) ^ 2 ≤
      (dist o (e i y) ^ 2 + dist y (e i o) ^ 2) / 2 := by
    rw [isometry_mid, mid_swap h (e i y) (e i o)]
    exact dist_mid_mid_sq_le h o y (e i y) (e i o)
  have he (i : ι) : dist o (e i y) = dist y (e (σ i) o) := by
    rw [hinv i, dist_comm y]
    simpa using ((e i).symm.isometry.dist_eq o (e i y)).symm
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hc i)
  simp_rw [he] at hs
  simp only [← Finset.sum_div, Finset.sum_add_distrib] at hs
  rw [σ.sum_comp (fun i => dist y (e i o) ^ 2)] at hs
  have hm := hmin (mid h o y)
  linarith

end CATZero

/-- The zero-barycenter conclusion, for any attained symmetric
isometric displacement-energy minimum. -/
theorem energy_tangent_barycenter {X : Type*} [MetricSpace X] {ι : Type*} [Fintype ι]
    (h : CATZero X) (e : ι → X ≃ᵢ X) (σ : ι ≃ ι)
    (hinv : ∀ i, e (σ i) = (e i).symm) (o : X)
    (hmin : ∀ y : X, (∑ i, dist o (e i o) ^ 2) ≤ ∑ i, dist y (e i y) ^ 2)
    (v : TangentCone h o) :
    (∑ i, (TangentCone.coneData h o).pairing v (TangentCone.log h o (e i o))) ≤ 0 :=
  TangentCone.pairing_sum_nonpos_of_minimum h o (fun i => e i o)
    (CATZero.orbit_minimum_of_energy_minimum h e σ hinv o hmin) v

end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
namespace GeometricAction
open Filter Topology
variable {G X : Type*} [Group G] [MetricSpace X]

/-- Displacement is invariant under simultaneous point/generator conjugation. -/
theorem displacement_conjugate (A : GeometricAction G X) (g s : G) (x : X) :
    dist x (A.act (g⁻¹ * s * g) x) = dist (A.act g x) (A.act s (A.act g x)) := by
  calc
    _ = dist (A.act g x) (A.act g (A.act (g⁻¹ * s * g) x)) :=
      ((A.act g).isometry.dist_eq _ _).symm
    _ = _ := by simp [map_mul, IsometryEquiv.mul_apply]

/-- Properness and cocompactness give an attained displacement-energy minimum.
No CAT(0) assumption is needed for this compactness step. -/
theorem energy_minimum [Nonempty X] [ProperSpace X] {ι : Type*} [Fintype ι]
    (A : GeometricAction G X) (S : ι → G) :
    ∃ o : X, ∀ y : X, (∑ i, dist o (A.act (S i) o) ^ 2) ≤
      ∑ i, dist y (A.act (S i) y) ^ 2 := by
  classical
  let E (x : X) : ℝ := ∑ i, dist x (A.act (S i) x) ^ 2
  have hE : Continuous E := by
    unfold E
    fun_prop
  have hn (x : X) : 0 ≤ E x := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : BddBelow (Set.range E) := ⟨0, by rintro _ ⟨x, rfl⟩; exact hn x⟩
  obtain ⟨v, hvanti, hv, hvr⟩ := exists_seq_tendsto_sInf (Set.range_nonempty E) hb
  choose u hu using hvr
  obtain ⟨C, hC, hcover⟩ := A.cocompact
  choose g c hc hgc using fun n : ℕ => hcover (u n)
  let x₀ : X := Classical.arbitrary X
  obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall x₀
  have hv₀ : 0 ≤ v 0 := by rw [← hu 0]; exact hn _
  let B := Metric.closedBall x₀ (R + v 0 + 1)
  have hCB : C ⊆ B := by
    intro x hx
    have hr := hR hx
    change dist x x₀ ≤ _ at hr ⊢
    linarith
  let H : Set G := {s | ∃ x ∈ B, A.act s x ∈ B}
  have hH : H.Finite := A.proper B (isCompact_closedBall _ _)
  have hd (n : ℕ) (i : ι) : dist (u n) (A.act (S i) (u n)) ≤ v 0 + 1 := by
    have hi : dist (u n) (A.act (S i) (u n)) ^ 2 ≤ E (u n) := by
      change dist (u n) (A.act (S i) (u n)) ^ 2 ≤ ∑ j, dist (u n) (A.act (S j) (u n)) ^ 2
      exact Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
        sq_nonneg (dist (u n) (A.act (S j) (u n)))) (Finset.mem_univ i)
    rw [hu n] at hi
    have hvn := hvanti (Nat.zero_le n)
    nlinarith [sq_nonneg (dist (u n) (A.act (S i) (u n)) - 1 / 2)]
  have hconj (n : ℕ) (i : ι) : (g n)⁻¹ * S i * g n ∈ H := by
    refine ⟨c n, hCB (hc n), ?_⟩
    have hdr : dist (c n) (A.act ((g n)⁻¹ * S i * g n) (c n)) ≤ v 0 + 1 := by
      rw [displacement_conjugate, hgc n]
      exact hd n i
    have hcr := hR (hc n)
    have ht := dist_triangle (A.act ((g n)⁻¹ * S i * g n) (c n)) (c n) x₀
    rw [dist_comm (A.act _ _) (c n)] at ht
    change dist (c n) x₀ ≤ R at hcr
    change dist (A.act _ _) x₀ ≤ _
    linarith
  let : Fintype H := hH.fintype
  let q (n : ℕ) : ι → H := fun i => ⟨(g n)⁻¹ * S i * g n, hconj n i⟩
  have hf : ∃ᶠ n : ℕ in atTop, ∃ k : ι → H, q n = k :=
    Filter.Frequently.of_forall fun n => ⟨q n, rfl⟩
  obtain ⟨k, hk⟩ := Filter.frequently_exists.mp hf
  obtain ⟨φ, hφ, hq⟩ := Filter.extraction_of_frequently_atTop hk
  obtain ⟨z, _, ψ, hψ, hz⟩ := hC.tendsto_subseq (fun n => hc (φ n))
  let E' (x : X) : ℝ := ∑ i, dist x (A.act ((g (φ 0))⁻¹ * S i * g (φ 0)) x) ^ 2
  have hE' : Continuous E' := by
    unfold E'
    fun_prop
  have heq (n : ℕ) : E' (c (φ (ψ n))) = v (φ (ψ n)) := by
    have hh (i : ι) : (g (φ 0))⁻¹ * S i * g (φ 0) =
        (g (φ (ψ n)))⁻¹ * S i * g (φ (ψ n)) := by
      exact congrArg Subtype.val (congrFun ((hq 0).trans (hq (ψ n)).symm) i)
    simp_rw [E', hh, displacement_conjugate, hgc]
    exact hu _
  have hez : E' z = sInf (Set.range E) := by
    apply tendsto_nhds_unique ((hE'.tendsto z).comp hz)
    have hlim := hv.comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop)
    exact hlim.congr' (Filter.Eventually.of_forall fun n => (heq n).symm)
  refine ⟨A.act (g (φ 0)) z, ?_⟩
  intro y
  have hx : E (A.act (g (φ 0)) z) = E' z := by
    simp_rw [E, E', ← displacement_conjugate]
  change E _ ≤ E y
  rw [hx, hez]
  exact csInf_le hb (Set.mem_range_self y)

end GeometricAction
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
namespace GeometricAction
variable {G X : Type*} [Group G] [MetricSpace X]

/-- An infinite group with a proper action cannot have zero displacement
energy on a finite generating tuple. -/
theorem energy_pos [Infinite G] {ι : Type*} [Fintype ι]
    (A : GeometricAction G X) (S : ι → G)
    (hgen : Subgroup.closure (Set.range S) = ⊤) (o : X) :
    0 < ∑ i, dist o (A.act (S i) o) ^ 2 := by
  classical
  have hn : 0 ≤ ∑ i, dist o (A.act (S i) o) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_contra hp
  have he : (∑ i, dist o (A.act (S i) o) ^ 2) = 0 := le_antisymm (not_lt.mp hp) hn
  have hs (i : ι) : A.act (S i) o = o := by
    have hi : dist o (A.act (S i) o) ^ 2 ≤ ∑ j, dist o (A.act (S j) o) ^ 2 :=
      Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
        sq_nonneg (dist o (A.act (S j) o))) (Finset.mem_univ i)
    rw [he] at hi
    exact (dist_eq_zero.mp (by nlinarith [dist_nonneg (x := o) (y := A.act (S i) o)])).symm
  have hfix (g : G) : A.act g o = o := by
    have hg : g ∈ Subgroup.closure (Set.range S) := by rw [hgen]; trivial
    induction hg using Subgroup.closure_induction with
    | mem a ha => obtain ⟨i, rfl⟩ := ha; exact hs i
    | one => simp
    | mul a b _ _ ha hb => simp [map_mul, IsometryEquiv.mul_apply, ha, hb]
    | inv a _ ha =>
      have hh := congrArg (fun x => (A.act a)⁻¹ x) ha
      simpa using hh.symm
  have hf := A.proper {o} isCompact_singleton
  have hall : ({g : G | ∃ x ∈ ({o} : Set X), A.act g x ∈ ({o} : Set X)}) = Set.univ := by
    ext g
    simp [hfix g]
  rw [hall] at hf
  exact Set.infinite_univ hf

end GeometricAction
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
open scoped BigOperators

/-- Splitting off the last coordinate of a uniform independent tuple. -/
theorem expect_snoc {ι : Type*} [Fintype ι] (n : ℕ) (f : (Fin (n + 1) → ι) → ℝ) :
    (𝔼 a, f a) = 𝔼 a : Fin n → ι, 𝔼 i : ι, f (Fin.snoc a i) := by
  calc
    _ = 𝔼 p : ι × (Fin n → ι), f (Fin.snoc p.2 p.1) := by
      apply Fintype.expect_equiv (Fin.snocEquiv (fun _ : Fin (n + 1) => ι)).symm
      intro a
      simp
    _ = 𝔼 i : ι, 𝔼 a : Fin n → ι, f (Fin.snoc a i) := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
    _ = _ := Finset.expect_comm _ _ _

namespace ConeData
variable {X : Type*} [MetricSpace X] (T : ConeData X)

theorem normSq_segment_pairing (h : CATZero X) (x y : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    T.normSq (CATZero.segment h x y t) = (1 - t) ^ 2 * T.normSq x +
      t ^ 2 * T.normSq y + 2 * t * (1 - t) * T.pairing x y := by
  rw [T.normSq_segment h x y ht, T.dist_sq]
  ring

theorem reciprocal_mem (n : ℕ) : 1 / (n + 1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · positivity
  · exact (div_le_one (by positivity : (0 : ℝ) < n + 1)).mpr (by
      have hn : (0 : ℝ) ≤ n := by positivity
      linarith)

/-- Deterministic concavity for the ordered mean; no associative cone
addition is used. -/
theorem pairing_inductiveMean (h : CATZero X) (w : X) (n : ℕ) (v : Fin n → X) :
    (∑ i, T.pairing w (v i)) ≤ (n : ℝ) * T.pairing w (T.inductiveMean h n v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have hi := ih (fun i => v i.castSucc)
    have hc := T.pairing_segment h w (T.inductiveMean h n (fun i => v i.castSucc))
      (v (Fin.last n)) (reciprocal_mem n)
    have hh : (n : ℝ) * T.pairing w (T.inductiveMean h n (fun i => v i.castSucc)) +
        T.pairing w (v (Fin.last n)) ≤
        (n + 1 : ℝ) * T.pairing w (T.inductiveMean h (n + 1) v) := by
      calc
        _ = (n + 1 : ℝ) * ((1 - 1 / (n + 1 : ℝ)) *
          T.pairing w (T.inductiveMean h n (fun i => v i.castSucc)) +
          (1 / (n + 1 : ℝ)) * T.pairing w (v (Fin.last n))) := by
            field_simp
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hc (by positivity)
    push_cast
    linarith

/-- One genuinely independent averaging step, using the zero-barycenter
inequality rather than any linear ambient vector space. -/
theorem expected_step {ι : Type*} [Fintype ι] [Nonempty ι]
    (h : CATZero X) (v : ι → X)
    (hbar : ∀ u, (𝔼 i, T.pairing u (v i)) ≤ 0)
    (hen : (𝔼 i, T.normSq (v i)) = 1) (u : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (𝔼 i, T.normSq (CATZero.segment h u (v i) t)) ≤ (1 - t) ^ 2 * T.normSq u + t ^ 2 := by
  simp_rw [T.normSq_segment_pairing h u _ ht]
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const, hen, mul_one]
  have hh := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ht.1) (sub_nonneg.mpr ht.2)) (hbar u)
  linarith

theorem expected_inductiveMean_step {ι : Type*} [Fintype ι] [Nonempty ι]
    (h : CATZero X) (v : ι → X)
    (hbar : ∀ u, (𝔼 i, T.pairing u (v i)) ≤ 0)
    (hen : (𝔼 i, T.normSq (v i)) = 1) (n : ℕ) :
    (𝔼 a : Fin (n + 1) → ι, T.normSq (T.inductiveMean h (n + 1) (v ∘ a))) ≤
      (1 - 1 / (n + 1 : ℝ)) ^ 2 *
        (𝔼 a : Fin n → ι, T.normSq (T.inductiveMean h n (v ∘ a))) +
          (1 / (n + 1 : ℝ)) ^ 2 := by
  rw [expect_snoc]
  simp only [inductiveMean, Function.comp_apply, Fin.snoc_castSucc, Fin.snoc_last]
  calc
    _ ≤ 𝔼 a : Fin n → ι, ((1 - 1 / (n + 1 : ℝ)) ^ 2 *
        T.normSq (T.inductiveMean h n (v ∘ a)) + (1 / (n + 1 : ℝ)) ^ 2) := by
      apply Finset.expect_le_expect
      intro a _
      exact T.expected_step h v hbar hen (T.inductiveMean h n (v ∘ a)) (reciprocal_mem n)
    _ = _ := by
      rw [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]

/-- The exact 1/t mean-square decay for t independent uniform samples. -/
theorem expected_inductiveMean {ι : Type*} [Fintype ι] [Nonempty ι]
    (h : CATZero X) (v : ι → X)
    (hbar : ∀ u, (𝔼 i, T.pairing u (v i)) ≤ 0)
    (hen : (𝔼 i, T.normSq (v i)) = 1) (n : ℕ) :
    (𝔼 a : Fin (n + 1) → ι, T.normSq (T.inductiveMean h (n + 1) (v ∘ a))) ≤
      1 / (n + 1 : ℝ) := by
  induction n with
  | zero =>
    have hh := T.expected_inductiveMean_step h v hbar hen 0
    simpa using hh
  | succ n ih =>
    calc
      _ ≤ (1 - 1 / ((n + 1 : ℕ) + 1 : ℝ)) ^ 2 *
          (𝔼 a : Fin (n + 1) → ι, T.normSq (T.inductiveMean h (n + 1) (v ∘ a))) +
          (1 / ((n + 1 : ℕ) + 1 : ℝ)) ^ 2 :=
        T.expected_inductiveMean_step h v hbar hen (n + 1)
      _ ≤ (1 - 1 / ((n + 1 : ℕ) + 1 : ℝ)) ^ 2 * (1 / (n + 1 : ℝ)) +
          (1 / ((n + 1 : ℕ) + 1 : ℝ)) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left ih (sq_nonneg _)) le_rfl
      _ = _ := by
        push_cast
        field_simp
        ring

end ConeData
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
open scoped BigOperators

namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

theorem expect_uniform [Nonempty α] (f : α → ℝ) :
    (uniform : FiniteLaw α).expect f = 𝔼 a, f a := by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [expect, uniform, ← Finset.mul_sum]
  ring

theorem expect_map (μ : FiniteLaw α) (f : α → β) (g : β → ℝ) :
    (μ.map f).expect g = μ.expect (g ∘ f) := by
  classical
  unfold expect map
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

/-- Exact finite total-variation comparison, with the constant 2B. -/
theorem expect_sub_bound (μ ν : FiniteLaw α) (f : α → ℝ) {B : ℝ}
    (hB : ∀ a, |f a| ≤ B) :
    |μ.expect f - ν.expect f| ≤ 2 * B * μ.totalVariation ν := by
  have he : μ.expect f - ν.expect f = ∑ a, (μ.mass a - ν.mass a) * f a := by
    simp [expect, sub_mul, Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ a, |(μ.mass a - ν.mass a) * f a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, |μ.mass a - ν.mass a| * B := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hB a) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; unfold totalVariation; ring

end FiniteLaw
end HyperbolicObstruction

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FiniteLaw
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section

namespace HyperbolicObstruction
open scoped BigOperators

namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

theorem expect_comm (μ : FiniteLaw α) (ν : FiniteLaw β) (f : α → β → ℝ) :
    μ.expect (fun a => ν.expect (f a)) = ν.expect (fun b => μ.expect (fun a => f a b)) := by
  simp only [expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem expect_le_of_totalVariation (μ ν : FiniteLaw α) (f : α → ℝ) {B η : ℝ}
    (hB : 0 ≤ B) (hf : ∀ a, |f a| ≤ B) (hη : μ.totalVariation ν ≤ η) :
    μ.expect f ≤ ν.expect f + 2 * B * η := by
  have hh := (abs_le.mp (μ.expect_sub_bound ν f hf)).2
  have hm := mul_le_mul_of_nonneg_left hη (show (0 : ℝ) ≤ 2 * B by positivity)
  linarith

theorem totalVariation_comm (μ ν : FiniteLaw α) : μ.totalVariation ν = ν.totalVariation μ := by
  unfold totalVariation
  simp_rw [abs_sub_comm (μ.mass _) (ν.mass _)]

end FiniteLaw

namespace ConeData
variable {X : Type*} [MetricSpace X] (T : ConeData X)

theorem abs_pairing_le (x y : X) :
    |T.pairing x y| ≤ dist T.vertex x * dist T.vertex y := by
  have ha := dist_nonneg (x := T.vertex) (y := x)
  have hb := dist_nonneg (x := T.vertex) (y := y)
  have hd := dist_nonneg (x := x) (y := y)
  have hab : dist x y ≤ dist T.vertex x + dist T.vertex y := by
    simpa [dist_comm] using dist_triangle x T.vertex y
  have hba : |dist T.vertex x - dist T.vertex y| ≤ dist x y := by
    have h₁ := dist_triangle T.vertex x y
    have h₂ := dist_triangle T.vertex y x
    rw [dist_comm y x] at h₂
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hs := sq_le_sq₀ (abs_nonneg (dist T.vertex x - dist T.vertex y)) hd |>.mpr hba
  have hs' := sq_le_sq₀ hd (add_nonneg ha hb) |>.mpr hab
  rw [sq_abs] at hs
  unfold pairing normSq
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem normSq_inductiveMean_le (h : CATZero X) {M : ℝ} (hM : 0 ≤ M)
    (n : ℕ) (v : Fin n → X) (hv : ∀ i, dist T.vertex (v i) ≤ M) :
    T.normSq (T.inductiveMean h n v) ≤ M ^ 2 := by
  induction n with
  | zero => simpa [inductiveMean] using sq_nonneg M
  | succ n ih =>
    have hi := ih (fun i => v i.castSucc) (fun i => hv i.castSucc)
    have hl : T.normSq (v (Fin.last n)) ≤ M ^ 2 :=
      (sq_le_sq₀ dist_nonneg hM).mpr (hv _)
    have ht := reciprocal_mem n
    have hc := T.normSq_segment h (T.inductiveMean h n (fun i => v i.castSucc))
      (v (Fin.last n)) ht
    have hh := add_le_add (mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left hl ht.1)
    have hd := mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
      (sq_nonneg (dist (T.inductiveMean h n (fun i => v i.castSucc)) (v (Fin.last n))))
    change T.normSq (CATZero.segment h _ _ _) ≤ _
    nlinarith

/-- The manuscript's quantitative conditional test. The hypotheses describe
an actual finite coupling, with all of its branch and leaf errors explicit.
The action-dependent function is not required to be independent of the law. -/
theorem conditional_test {α β ι : Type*} [Fintype α] [Fintype β]
    [Fintype ι] [Nonempty ι] (h : CATZero X)
    (μ : FiniteLaw α) (κ : FiniteLaw β) (v : ι → X)
    (hbar : ∀ u, (𝔼 i, T.pairing u (v i)) ≤ 0)
    (hen : (𝔼 i, T.normSq (v i)) = 1)
    (test : α → X) (letter : α → ι) (n : ℕ)
    (branch : Fin (n + 1) → β → α)
    (agree : ∀ j b, test (branch j b) = test (branch 0 b))
    {M B η : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hv : ∀ i, dist T.vertex (v i) ≤ M)
    (htest : ∀ a, dist T.vertex (test a) ≤ B)
    (hbranch : ∀ j, (κ.map (branch j)).totalVariation μ ≤ η)
    (hleaf : (κ.map (fun b j => letter (branch j b))).totalVariation
      (FiniteLaw.uniform : FiniteLaw (Fin (n + 1) → ι)) ≤ η) :
    μ.expect (fun a => T.pairing (test a) (v (letter a))) ≤
      B * Real.sqrt (1 / (n + 1 : ℝ) + 2 * M ^ 2 * η) + 2 * B * M * η := by
  let f : α → ℝ := fun a => T.pairing (test a) (v (letter a))
  let ℓ : β → (Fin (n + 1) → ι) := fun b j => letter (branch j b)
  let mean : (Fin (n + 1) → ι) → X := fun a => T.inductiveMean h (n + 1) (v ∘ a)
  let U : FiniteLaw (Fin (n + 1)) := FiniteLaw.uniform
  have hf : ∀ a, |f a| ≤ B * M := by
    intro a
    exact (T.abs_pairing_le _ _).trans
      (mul_le_mul (htest a) (hv _) dist_nonneg hB)
  have hb : μ.expect f ≤ κ.expect (fun b => U.expect (fun j => f (branch j b))) +
      2 * B * M * η := by
    have hh : ∀ j, μ.expect f ≤ κ.expect (fun b => f (branch j b)) + 2 * (B * M) * η := by
      intro j
      have hj := μ.expect_le_of_totalVariation (κ.map (branch j)) f (η := η) (mul_nonneg hB hM) hf
        (by rw [FiniteLaw.totalVariation_comm]; exact hbranch j)
      rw [FiniteLaw.expect_map] at hj
      exact hj
    have he := U.expect_mono hh
    rw [U.expect_const, U.expect_add, U.expect_const, FiniteLaw.expect_comm] at he
    nlinarith
  have hmean : κ.expect (fun b => T.normSq (mean (ℓ b))) ≤
      1 / (n + 1 : ℝ) + 2 * M ^ 2 * η := by
    have hh := (κ.map ℓ).expect_le_of_totalVariation FiniteLaw.uniform
      (fun a => T.normSq (mean a)) (sq_nonneg M)
      (fun a => by
        rw [abs_of_nonneg (T.normSq_nonneg _)]
        exact T.normSq_inductiveMean_le h hM _ _ (fun i => hv _)) hleaf
    rw [FiniteLaw.expect_map, FiniteLaw.expect_uniform] at hh
    have hi := T.expected_inductiveMean h v hbar hen n
    exact hh.trans (add_le_add hi le_rfl)
  have hp : ∀ b, U.expect (fun j => f (branch j b)) ≤
      B * dist T.vertex (mean (ℓ b)) := by
    intro b
    have hi := T.pairing_inductiveMean h (test (branch 0 b)) (n + 1) (v ∘ ℓ b)
    have hd : (0 : ℝ) < n + 1 := by positivity
    have hc : U.expect (fun j => f (branch j b)) ≤ T.pairing (test (branch 0 b)) (mean (ℓ b)) := by
      rw [FiniteLaw.expect_uniform, Fintype.expect_eq_sum_div_card]
      simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
      apply (div_le_iff₀ hd).mpr
      have he : (∑ j, f (branch j b)) = ∑ j, T.pairing (test (branch 0 b)) (v (ℓ b j)) := by
        apply Finset.sum_congr rfl
        intro j _
        change T.pairing (test (branch j b)) (v _) = _
        rw [agree j b]
      rw [he]
      simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, mul_comm] using hi
    exact hc.trans ((le_abs_self _).trans ((T.abs_pairing_le _ _).trans
      (mul_le_mul_of_nonneg_right (htest _) dist_nonneg)))
  have hs := κ.expect_le_sqrt (fun b => dist T.vertex (mean (ℓ b)))
  have hs' := Real.sqrt_le_sqrt hmean
  have hfinal := κ.expect_mono hp
  rw [κ.expect_mul] at hfinal
  calc
    _ ≤ κ.expect (fun b => U.expect (fun j => f (branch j b))) + 2 * B * M * η := hb
    _ ≤ B * κ.expect (fun b => dist T.vertex (mean (ℓ b))) + 2 * B * M * η :=
      add_le_add hfinal le_rfl
    _ ≤ B * Real.sqrt (1 / (n + 1 : ℝ) + 2 * M ^ 2 * η) + 2 * B * M * η :=
      add_le_add (mul_le_mul_of_nonneg_left (hs.trans hs') hB) le_rfl

end ConeData
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
open scoped BigOperators
open Filter Topology

/-- Passing to the limit in the quantitative conditional test, first with
sample size fixed and then letting it tend to infinity. -/
theorem conditional_test_eventually {a : ℕ → ℝ} {B M : ℝ}
    (hbound : ∀ n : ℕ, ∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧
      ∀ᶠ ν in atTop, a ν ≤ B * Real.sqrt (1 / (n + 1 : ℝ) + 2 * M ^ 2 * η ν) +
        2 * B * M * η ν) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ ν in atTop, a ν < ε := by
  intro ε hε
  have hz : Tendsto (fun n : ℕ => B * Real.sqrt (1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto (0 : ℝ) |>.comp
      tendsto_one_div_add_atTop_nhds_zero_nat).const_mul B
  obtain ⟨n, hn⟩ := (hz.eventually (gt_mem_nhds hε)).exists
  obtain ⟨η, hη, hineq⟩ := hbound n
  have ht : Tendsto (fun ν => B * Real.sqrt (1 / (n + 1 : ℝ) + 2 * M ^ 2 * η ν) +
      2 * B * M * η ν) atTop (𝓝 (B * Real.sqrt (1 / (n + 1 : ℝ)))) := by
    have hsum : Tendsto (fun ν => 1 / (n + 1 : ℝ) + 2 * M ^ 2 * η ν) atTop
        (𝓝 (1 / (n + 1 : ℝ) + 2 * M ^ 2 * 0)) :=
      tendsto_const_nhds.add (hη.const_mul (2 * M ^ 2))
    have hh := ((Real.continuous_sqrt.tendsto _).comp hsum).const_mul B
    simpa using hh.add (hη.const_mul (2 * B * M))
  filter_upwards [hineq, ht.eventually (gt_mem_nhds hn)] with ν hν hν'
  exact hν.trans_lt hν'

namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

theorem expect_le_density (μ ν : FiniteLaw α) {R : ℝ}
    (hm : ∀ a, μ.mass a ≤ R * ν.mass a) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    μ.expect f ≤ R * ν.expect f := by
  unfold expect
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ => by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hm a) (hf a)

theorem expect_map_le_uniform [Nonempty β] (μ : FiniteLaw α) (e : α → β) {R : ℝ}
    (hm : ∀ b, (μ.map e).mass b ≤ R / Fintype.card β)
    (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    μ.expect (f ∘ e) ≤ R * (𝔼 b, f b) := by
  have hh := (μ.map e).expect_le_density uniform (R := R)
    (fun b => by simpa [uniform, div_eq_mul_inv] using hm b) f hf
  rwa [expect_map, expect_uniform] at hh

end FiniteLaw

end HyperbolicObstruction

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MetricHexagon
attribute [-instance] _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section


noncomputable section


noncomputable section

noncomputable section
namespace HyperbolicObstruction
namespace CoreGeometry

namespace MetricCore
variable {X : Type*} [MetricSpace X] {z : Vertex → X} (D : MetricCore z)

include D

/-- No CAT(0) space contains the exact limiting core configuration of
Proposition `configuration`, including its exceptional fractional test. -/
theorem impossible (h : CATZero X) (he : ExceptionalTest h z) : False :=
  no_finite_obstruction h (D.toObstruction h he)

end MetricCore
end CoreGeometry
end HyperbolicObstruction


noncomputable section
open scoped BigOperators ENNReal
namespace HyperbolicObstruction
namespace MetricScale
universe u

variable {r : ℝ} {hr : 0 < r} {X : Type u} [MetricSpace X]

variable (h : CATZero X)
include h

lemma val_segment (x y : Space r hr X) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (CATZero.segment (catZero h) x y t).val = CATZero.segment h x.val y.val t := by
  let z : Space r hr X := ⟨CATZero.segment h x.val y.val t⟩
  have he : z = CATZero.segment (catZero h) x y t := by
    apply CATZero.eq_segment_of_dist (catZero h) ht
    · change r * dist x.val (CATZero.segment h x.val y.val t) = t * (r * dist x.val y.val)
      rw [CATZero.segment_left h _ _ ht]
      ring
    · change r * dist (CATZero.segment h x.val y.val t) y.val = (1 - t) * (r * dist x.val y.val)
      rw [CATZero.segment_right h _ _ ht]
      ring
  exact congrArg Space.val he.symm

end MetricScale


end HyperbolicObstruction
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MetricProduct
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators ENNReal
namespace HyperbolicObstruction

namespace MetricProduct
universe u v
variable {ι : Type u} [Fintype ι] {X : ι → Type v} [∀ i, MetricSpace (X i)]

variable (h : ∀ i, CATZero (X i))

include h

lemma apply_segment (x y : PiLp 2 X) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : ι) :
    CATZero.segment (catZero h) x y t i = CATZero.segment (h i) (x i) (y i) t := by
  have he : segment h x y t = CATZero.segment (catZero h) x y t := by
    apply CATZero.eq_segment_of_dist (catZero h) ht
    · have hh := segment_dist h x y (s := 0) (by norm_num) ht
      rw [segment_zero, zero_sub, abs_neg, abs_of_nonneg ht.1] at hh
      exact hh
    · have hh := segment_dist h x y ht (t := 1) (by norm_num)
      rw [segment_one, abs_of_nonpos (sub_nonpos.mpr ht.2)] at hh
      simpa only [neg_sub] using hh
  exact congrArg (fun z : PiLp 2 X => z i) he.symm

end MetricProduct
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
namespace MeanProduct
open scoped BigOperators
universe u v
variable (ι : Type u) [Fintype ι] [Nonempty ι]

variable (X : ι → Type v) [∀ i, MetricSpace (X i)]

variable {ι X}

omit [∀ index, MetricSpace (X index)] in
lemma ofFn_apply (x : ∀ i, X i) (i : ι) : apply (ofFn ι X x) i = x i := rfl

variable (h : ∀ i, CATZero (X i))
include h

lemma apply_segment (x y : Space ι X) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : ι) :
    apply (CATZero.segment (catZero h) x y t) i =
      CATZero.segment (h i) (apply x i) (apply y i) t := by
  unfold apply
  rw [MetricScale.val_segment (MetricProduct.catZero h) x y ht,
    MetricProduct.apply_segment h _ _ ht]

end MeanProduct
end HyperbolicObstruction


noncomputable section
open Filter Topology
namespace HyperbolicObstruction
namespace MetricLimit
universe u
variable (U : Ultrafilter ℕ) (X : ℕ → Type u) [∀ n, MetricSpace (X n)] (o : ∀ n, X n)

variable {U X o}

variable (h : ∀ n, CATZero (X n))

include h

/-- Uniqueness identifies actual chosen limit segments, not just their endpoints. -/
lemma point_segment (x y : Bounded U X o) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    point (segment h x y t) = CATZero.segment (catZero h) (point x) (point y) t := by
  apply CATZero.eq_segment_of_dist (catZero h) ht
  · have he := segment_dist h x y (s := 0) (by norm_num) ht
    rw [segment_zero, zero_sub, abs_neg, abs_of_nonneg ht.1] at he
    exact he
  · have he := segment_dist h x y ht (t := 1) (by norm_num)
    rw [segment_one, abs_of_nonpos (sub_nonpos.mpr ht.2)] at he
    simpa only [neg_sub] using he

end MetricLimit
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
open Filter Topology

namespace MetricLimit
universe u
variable {U : Ultrafilter ℕ} {X : ℕ → Type u} [∀ n, MetricSpace (X n)] {o : ∀ n, X n}

lemma tendsto_point_dist_sq (x y : Bounded U X o) :
    Tendsto (fun n => dist (x.val n) (y.val n) ^ 2) U (𝓝 (dist (point x) (point y) ^ 2)) :=
  (tendsto_point_dist x y).pow 2

lemma lower_of_eventually (hU : (U : Filter ℕ) ≤ atTop) (x y : Bounded U X o) {a : ℝ}
    (ha : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, a - ε ≤ dist (x.val n) (y.val n) ^ 2) :
    a ≤ dist (point x) (point y) ^ 2 := by
  by_contra hn
  have he : 0 < (a - dist (point x) (point y) ^ 2) / 2 := by linarith
  have hh := le_of_tendsto_of_tendsto tendsto_const_nhds (tendsto_point_dist_sq x y) (hU (ha _ he))
  linarith

end MetricLimit
end HyperbolicObstruction



noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace MetricScale
universe u
variable {r : ℝ} {hr : 0 < r} {X : Type u} [MetricSpace X]

lemma action_val {G : Type*} [Group G] (A : G →* (X ≃ᵢ X)) (g : G) (x : Space r hr X) :
    (action A g x).val = A g x.val := rfl

end MetricScale

namespace IsometricAction
variable {G X : Type*} [Group G] [MetricSpace X]

theorem displacement_prod_le (A : G →* (X ≃ᵢ X)) (x : X) (w : List G) :
    dist x (A w.prod x) ≤ (w.map (fun g => dist x (A g x))).sum := by
  induction w with
  | nil => simp
  | cons g w ih =>
    simpa only [List.prod_cons, List.map_cons, List.sum_cons] using
      (displacement_mul_le A x g w.prod).trans (add_le_add le_rfl ih)

theorem six_letter_displacement_bound {α ι : Type*} [Fintype α] [Fintype ι]
    [Nonempty ι] (A : G →* (X ≃ᵢ X)) (x : X) (letter : ι → G)
    (hen : (𝔼 i, dist x (A (letter i) x) ^ 2) = 1)
    (a : G) (κ : FiniteLaw α) (row : α → Fin 5 → ι)
    (hrow : ∀ b, (List.ofFn (letter ∘ row b)).prod = a⁻¹)
    {R : ℝ} (hmarg : ∀ j i, (κ.map (fun b => row b j)).mass i ≤ R / Fintype.card ι) :
    dist x (A a x) ^ 2 ≤ 25 * R := by
  have hb : ∀ b, dist x (A a x) ^ 2 ≤ 5 * ∑ j, dist x (A (letter (row b j)) x) ^ 2 := by
    intro b
    have hp := displacement_prod_le A x (List.ofFn (letter ∘ row b))
    rw [hrow b, displacement_inv A x a, List.map_ofFn, List.sum_ofFn] at hp
    have hc := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun j : Fin 5 => dist x (A (letter (row b j)) x))
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at hc
    have hs := (sq_le_sq₀ dist_nonneg (Finset.sum_nonneg (fun _ _ => dist_nonneg))).mpr hp
    exact hs.trans hc
  have hh := κ.expect_mono hb
  rw [κ.expect_const, κ.expect_mul, κ.expect_sum] at hh
  have hj : ∀ j : Fin 5, κ.expect (fun b => dist x (A (letter (row b j)) x) ^ 2) ≤ R := by
    intro j
    have he := κ.expect_map_le_uniform (fun b => row b j) (hmarg j)
      (fun i => dist x (A (letter i) x) ^ 2) (fun _ => sq_nonneg _)
    simpa only [Function.comp_def, hen, mul_one] using he
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 5))) => hj j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat] at hs
  linarith

/-- Exact normalized displacement minimum obtained by rescaling the actual action. -/
theorem normalized_minimum [Nonempty X] [ProperSpace X] [Infinite G]
    {ι : Type*} [Fintype ι] [Nonempty ι] (A : GeometricAction G X) (letter : ι → G)
    (hgen : Subgroup.closure (Set.range letter) = ⊤) :
    ∃ r : ℝ, ∃ hr : 0 < r, ∃ o : MetricScale.Space r hr X,
      (𝔼 i, dist o (MetricScale.action A.act (letter i) o) ^ 2) = 1 ∧
      ∀ y : MetricScale.Space r hr X,
        (∑ i, dist o (MetricScale.action A.act (letter i) o) ^ 2) ≤
        ∑ i, dist y (MetricScale.action A.act (letter i) y) ^ 2 := by
  obtain ⟨x, hx⟩ := A.energy_minimum letter
  let E : ℝ := 𝔼 i, dist x (A.act (letter i) x) ^ 2
  have hE : 0 < E := by
    dsimp only [E]
    rw [Fintype.expect_eq_sum_div_card]
    exact div_pos (A.energy_pos letter hgen x) (by positivity)
  let r : ℝ := 1 / Real.sqrt E
  have hr : 0 < r := one_div_pos.mpr (Real.sqrt_pos.mpr hE)
  have hrsq : r ^ 2 = 1 / E := by
    dsimp only [r]
    rw [div_pow, one_pow, Real.sq_sqrt hE.le]
  refine ⟨r, hr, ⟨x⟩, ?_, ?_⟩
  · simp only [MetricScale.dist_eq, MetricScale.action_val, mul_pow]
    rw [← Finset.mul_expect, hrsq]
    exact one_div_mul_cancel hE.ne'
  · intro y
    simp only [MetricScale.dist_eq, MetricScale.action_val, mul_pow, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hx y.val) (sq_nonneg r)

end IsometricAction
end HyperbolicObstruction


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConditionalStar
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators ENNReal
noncomputable section
noncomputable section
open Filter Topology
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open Filter Topology

namespace HyperbolicObstruction

namespace ConditionalStar
variable {F L Ω : Type*} [DecidableEq F] {label : Ω → F → L} {I : Finset F} {k : ℕ}

lemma agree (b : ConditionalStar label I k) (j : Fin (k + 1)) (i : F) (hi : i ∈ I) :
    label (branch j b) i = label (branch 0 b) i := b.property j i hi

end ConditionalStar

namespace EnergyOrbit
variable {L X : Type*} [Fintype L] [MetricSpace X] {M : ℝ} (O : EnergyOrbit L X M)

lemma normSq_vector (i : L) : O.cone.normSq (O.vector i) = dist O.base (O.isom i O.base) ^ 2 :=
  TangentCone.normSq_log O.cat O.base _

lemma norm_vector (i : L) : dist O.cone.vertex (O.vector i) = dist O.base (O.isom i O.base) := by
  have he := O.normSq_vector i
  exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp he

lemma barycenter (u : O.Cone) : (𝔼 i, O.cone.pairing u (O.vector i)) ≤ 0 := by
  rw [Fintype.expect_eq_sum_div_card]
  exact div_nonpos_of_nonpos_of_nonneg
    (energy_tangent_barycenter O.cat O.isom O.inverse O.symmetric O.base O.minimum u)
    (by positivity)

lemma energy_vector : (𝔼 i, O.cone.normSq (O.vector i)) = 1 := by
  simp_rw [O.normSq_vector]
  exact O.energy

lemma barycenter_read (σ : L ≃ L) (u : O.Cone) :
    (𝔼 i, O.cone.pairing u (O.vector (σ i))) ≤ 0 := by
  rw [Fintype.expect_eq_sum_div_card, σ.sum_comp (fun i => O.cone.pairing u (O.vector i))]
  simpa only [Fintype.expect_eq_sum_div_card] using O.barycenter u

lemma energy_read (σ : L ≃ L) : (𝔼 i, O.cone.normSq (O.vector (σ i))) = 1 := by
  rw [Fintype.expect_eq_sum_div_card, σ.sum_comp (fun i => O.cone.normSq (O.vector i))]
  simpa only [Fintype.expect_eq_sum_div_card] using O.energy_vector

end EnergyOrbit

namespace SamplingSequence
universe u v w
variable {F : Type u} [DecidableEq F] {Admissible : Finset F → Prop}
  {L Ω : ℕ → Type v} [∀ n, Fintype (L n)] [∀ n, Nonempty (L n)]
  [∀ n, DecidableEq (L n)] [∀ n, Fintype (Ω n)] [∀ n, Nonempty (Ω n)]
  {label : ∀ n, Ω n → F → L n} (S : SamplingSequence F Admissible L Ω label)
  {X : ℕ → Type w} [∀ n, MetricSpace (X n)] {M : ℝ}
  (O : ∀ n, EnergyOrbit (L n) (X n) M)

include S

/-- The conditional test applies to arbitrary bounded action-dependent tests,
including tests using inverses of any field labels. -/
theorem conditional {I : Finset F} {e : F} (he : e ∉ I) (hI : Admissible (insert e I))
    (σ : ∀ n, L n ≃ L n) (test : ∀ n, Ω n → (O n).Cone)
    (depends : ∀ n a b, (∀ i ∈ I, label n a i = label n b i) → test n a = test n b)
    {B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (htest : ∀ n a, dist (O n).cone.vertex (test n a) ≤ B) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (𝔼 a, (O n).cone.pairing (test n a) ((O n).vector (σ n (label n a e)))) < ε := by
  apply conditional_test_eventually
  intro k
  obtain ⟨η, hη, hκ⟩ := S.star I e he hI k
  refine ⟨η, hη, ?_⟩
  filter_upwards [hκ] with n hn
  obtain ⟨κ, hbranch, hleaf⟩ := hn
  have hh := (O n).cone.conditional_test (TangentCone.catZero (O n).cat (O n).base)
    (FiniteLaw.uniform : FiniteLaw (Ω n)) κ (fun i => (O n).vector (σ n i))
    ((O n).barycenter_read (σ n)) ((O n).energy_read (σ n))
    (test n) (fun a => label n a e) k ConditionalStar.branch
    (fun j b => depends n _ _ (fun i hi => ConditionalStar.agree b j i hi)) hM hB
    (fun i => by rw [(O n).norm_vector]; exact (O n).bound _)
    (htest n) hbranch hleaf
  rwa [FiniteLaw.expect_uniform] at hh

/-- Single-field convergence remains usable uniformly after the action has
been chosen: the displacement functions only need the uniform letter bound. -/
theorem edge_energy (e : F) (σ : ∀ n, L n ≃ L n) (hM : 0 ≤ M) :
    Tendsto (fun n => 𝔼 a, dist (O n).base ((O n).isom (σ n (label n a e)) (O n).base) ^ 2)
      atTop (𝓝 1) := by
  let η (n : ℕ) := ((FiniteLaw.uniform : FiniteLaw (Ω n)).map (fun a => label n a e)).totalVariation
    FiniteLaw.uniform
  have he : ∀ n, |(𝔼 a, dist (O n).base ((O n).isom (σ n (label n a e)) (O n).base) ^ 2) - 1| ≤
      2 * M ^ 2 * η n := by
    intro n
    have hb : ∀ i, |dist (O n).base ((O n).isom (σ n i) (O n).base) ^ 2| ≤ M ^ 2 := by
      intro i
      rw [abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ dist_nonneg hM).mpr ((O n).bound _)
    have hh := (((FiniteLaw.uniform : FiniteLaw (Ω n)).map (fun a => label n a e))).expect_sub_bound
      FiniteLaw.uniform (fun i => dist (O n).base ((O n).isom (σ n i) (O n).base) ^ 2) hb
    simp only [FiniteLaw.expect_map, FiniteLaw.expect_uniform, Fintype.expect_eq_sum_div_card,
      Function.comp_def] at hh
    rw [(σ n).sum_comp (fun i => dist (O n).base ((O n).isom i (O n).base) ^ 2)] at hh
    have hn := (O n).energy
    rw [Fintype.expect_eq_sum_div_card] at hn
    rw [hn] at hh
    simpa only [Fintype.expect_eq_sum_div_card] using hh
  have ht : Tendsto (fun n => 2 * M ^ 2 * η n) atTop (𝓝 0) := by
    simpa using (S.singleton e).const_mul (2 * M ^ 2)
  have hz : Tendsto (fun n => (𝔼 a, dist (O n).base ((O n).isom (σ n (label n a e)) (O n).base) ^ 2) - 1) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ ht
    filter_upwards [] with n
    simpa only [Real.norm_eq_abs] using he n
  have hh := hz.add_const 1
  simpa only [sub_add_cancel, zero_add] using hh

end SamplingSequence
end HyperbolicObstruction


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace EnergyOrbit

/-- Six-letter relative counts provide the bound M=8 for the rescaled genuine
geometric action; no bound on the action is assumed before sampling. -/
theorem exists_of_geometric {L G X : Type*} [Fintype L] [Nonempty L] [Group G]
    [Infinite G] [MetricSpace X] [Nonempty X] [ProperSpace X]
    (hX : CATZero X) (A : GeometricAction G X) (letter : L → G) (inv : L ≃ L)
    (hinv : ∀ i, letter (inv i) = (letter i)⁻¹)
    (hgen : Subgroup.closure (Set.range letter) = ⊤)
    (Row : L → Type*) [∀ i, Fintype (Row i)] (κ : ∀ i, FiniteLaw (Row i))
    (row : ∀ i, Row i → Fin 5 → L)
    (hrow : ∀ i b, (List.ofFn (letter ∘ row i b)).prod = (letter i)⁻¹)
    (hmarg : ∀ i j a, ((κ i).map (fun b => row i b j)).mass a ≤ 2 / Fintype.card L) :
    ∃ r : ℝ, ∃ hr : 0 < r, ∃ O : EnergyOrbit L (MetricScale.Space r hr X) 8,
      ∀ i, O.isom i = MetricScale.action A.act (letter i) := by
  obtain ⟨r, hr, o, hen, hmin⟩ := IsometricAction.normalized_minimum A letter hgen
  refine ⟨r, hr, ⟨MetricScale.catZero hX, o, fun i => MetricScale.action A.act (letter i),
    inv, ?_, hmin, hen, ?_⟩, fun _ => rfl⟩
  · intro i
    rw [hinv, map_inv]
    rfl
  · intro i
    have hh := IsometricAction.six_letter_displacement_bound
      (MetricScale.action A.act) o letter hen (letter i) (κ i) (row i) (hrow i) (hmarg i)
    nlinarith [dist_nonneg (x := o) (y := MetricScale.action A.act (letter i) o)]

end EnergyOrbit

namespace IsometricAction
variable {G X : Type*} [Group G] [MetricSpace X]

lemma displacement_mul_dist (A : G →* (X ≃ᵢ X)) (o : X) (g k : G) :
    dist o (A (g * k) o) = dist (A g⁻¹ o) (A k o) := by
  have hh := (A g).isometry.dist_eq (A g⁻¹ o) (A k o)
  have hg : A g (A g⁻¹ o) = o := by
    rw [← IsometryEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [hg, ← IsometryEquiv.mul_apply, ← map_mul] at hh
  exact hh

end IsometricAction

namespace OrbitWord
variable {F L Ω G X : Type*} [Group G]

lemma nil (label : Ω → F → L) (σ : F → L ≃ L) (letter : L → G) (a : Ω) :
    word label σ letter a [] = 1 := rfl

lemma cons (label : Ω → F → L) (σ : F → L ≃ L) (letter : L → G) (a : Ω) (e : F) (w : List F) :
    word label σ letter a (e :: w) = letter (σ e (label a e)) * word label σ letter a w := rfl

lemma depends (label : Ω → F → L) (σ : F → L ≃ L) (letter : L → G) (a b : Ω) (w : List F)
    (he : ∀ i ∈ w, label a i = label b i) : word label σ letter a w = word label σ letter b w := by
  unfold word
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [he i hi]

lemma bound [MetricSpace X] (A : G →* (X ≃ᵢ X)) (o : X) (label : Ω → F → L)
    (σ : F → L ≃ L) (letter : L → G) {M : ℝ}
    (hb : ∀ i, dist o (A (letter i) o) ≤ M) (a : Ω) (w : List F) :
    dist o (A (word label σ letter a w) o) ≤ w.length * M := by
  induction w with
  | nil => simp [nil]
  | cons e w ih =>
    rw [cons]
    have hh := (IsometricAction.displacement_mul_le A o (letter (σ e (label a e))) _).trans (add_le_add (hb (σ e (label a e))) ih)
    simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm M] using hh

end OrbitWord

namespace SamplingSequence
universe u v w z
variable {F : Type u} [DecidableEq F] {Admissible : Finset F → Prop}
  {L Ω : ℕ → Type v} [∀ n, Fintype (L n)] [∀ n, Nonempty (L n)]
  [∀ n, DecidableEq (L n)] [∀ n, Fintype (Ω n)] [∀ n, Nonempty (Ω n)]
  {label : ∀ n, Ω n → F → L n} (S : SamplingSequence F Admissible L Ω label)
  {X : ℕ → Type w} [∀ n, MetricSpace (X n)] {M : ℝ}
  (O : ∀ n, EnergyOrbit (L n) (X n) M)
  {G : ℕ → Type z} [∀ n, Group (G n)]
  (A : ∀ n, G n →* (X n ≃ᵢ X n)) (letter : ∀ n, L n → G n)
  (hact : ∀ n i, A n (letter n i) = (O n).isom i)
include S hact

/-- Path lower bounds are produced from the sampling assertions and the action,
not postulated as a limiting configuration. The proof uses only finite sums and
one-sided vanishing errors, so the spaces/actions can vary with n. -/
theorem word_lower (down : ∀ I J, I ⊆ J → Admissible J → Admissible I)
    (σ : ∀ n, F → L n ≃ L n) (hM : 0 ≤ M) (w : List F) (hw : w.Nodup)
    (hadm : Admissible w.toFinset) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (w.length : ℝ) - ε ≤
        𝔼 a, dist (O n).base (A n (OrbitWord.word (label n) (σ n) (letter n) a w) (O n).base) ^ 2 := by
  induction w with
  | nil =>
    intro ε hε
    filter_upwards [] with n
    simpa [OrbitWord.nil] using hε.le
  | cons e w ih =>
    have hnot : e ∉ w.toFinset := by simpa using (List.nodup_cons.mp hw).1
    have hadm' : Admissible w.toFinset := down _ _ (by simp) hadm
    have hw' := (List.nodup_cons.mp hw).2
    let test (n : ℕ) (a : Ω n) : (O n).Cone := TangentCone.log (O n).cat (O n).base
      (A n (OrbitWord.word (label n) (σ n) (letter n) a w) (O n).base)
    let σ' (n : ℕ) : L n ≃ L n := (σ n e).trans (O n).inverse
    have htest : ∀ n a, dist (O n).cone.vertex (test n a) ≤ w.length * M := by
      intro n a
      change dist (TangentCone.vertex (O n).cat (O n).base) (test n a) ≤ _
      rw [TangentCone.dist_vertex_log]
      exact OrbitWord.bound (A n) (O n).base (label n) (σ n) (letter n)
        (fun i => by rw [hact]; exact (O n).bound i) a w
    have hc := S.conditional O hnot (by simpa using hadm) σ' test
      (fun n a b hab => by
        dsimp only [test]
        rw [OrbitWord.depends (label n) (σ n) (letter n) a b w
          (fun i hi => hab i (by simpa using hi))])
      hM (mul_nonneg (by positivity) hM) htest
    have hedge := S.edge_energy O e σ' hM
    have hineq (n : ℕ) :
        (𝔼 a, dist (O n).base (A n (OrbitWord.word (label n) (σ n) (letter n) a w) (O n).base) ^ 2) +
        (𝔼 a, dist (O n).base ((O n).isom (σ' n (label n a e)) (O n).base) ^ 2) -
        2 * (𝔼 a, (O n).cone.pairing (test n a) ((O n).vector (σ' n (label n a e)))) ≤
        𝔼 a, dist (O n).base (A n (OrbitWord.word (label n) (σ n) (letter n) a (e :: w)) (O n).base) ^ 2 := by
      rw [← Finset.expect_add_distrib, Finset.mul_expect, ← Finset.expect_sub_distrib]
      apply Finset.expect_le_expect
      intro a _
      have he : (O n).isom (σ' n (label n a e)) = (A n (letter n (σ n e (label n a e)))).symm := by
        simpa only [σ', Equiv.trans_apply, hact] using (O n).symmetric (σ n e (label n a e))
      have hp := TangentCone.pairing_log_ge (O n).cat (O n).base
        (A n (OrbitWord.word (label n) (σ n) (letter n) a w) (O n).base)
        ((O n).isom (σ' n (label n a e)) (O n).base)
      have hd : dist (O n).base (A n (OrbitWord.word (label n) (σ n) (letter n) a (e :: w)) (O n).base) =
          dist (A n (OrbitWord.word (label n) (σ n) (letter n) a w) (O n).base)
            ((O n).isom (σ' n (label n a e)) (O n).base) := by
        rw [OrbitWord.cons, IsometricAction.displacement_mul_dist, dist_comm, he, map_inv]
        rfl
      rw [hd]
      change _ - 2 * (O n).cone.pairing
        (TangentCone.log (O n).cat (O n).base _) (TangentCone.log (O n).cat (O n).base _) ≤ _
      linarith
    intro ε hε
    have h1 := ih hw' hadm' (ε / 3) (by positivity)
    have h2 := hedge.eventually (lt_mem_nhds (show 1 - ε / 3 < (1 : ℝ) by linarith))
    have h3 := hc (ε / 6) (by positivity)
    filter_upwards [h1, h2, h3] with n hn₁ hn₂ hn₃
    have hh := hineq n
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

end SamplingSequence
end HyperbolicObstruction

noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace CATZero
variable {X : Type*} [MetricSpace X]

lemma isometry_segment (h : CATZero X) (e : X ≃ᵢ X) (x y : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    e (segment h x y t) = segment h (e x) (e y) t :=
  map_segment_of_dist h h e (fun a b => (e.isometry.dist_eq a b).le) x y
    (e.isometry.dist_eq x y) ht

/-- Comparison at fixed fractions is taken before forming the ultralimit. -/
lemma fractional_log_comparison (h : CATZero X) (o x y : X) {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    a ^ 2 * dist o x ^ 2 + b ^ 2 * dist o y ^ 2 -
      2 * a * b * (TangentCone.coneData h o).pairing
        (TangentCone.log h o x) (TangentCone.log h o y) ≤
      dist (segment h o x a) (segment h o y b) ^ 2 := by
  have hh := (sq_le_sq₀ dist_nonneg dist_nonneg).mpr
    (TangentCone.dist_log_le h o (segment h o x a) (segment h o y b))
  rw [TangentCone.log_radial h o x ha, TangentCone.log_radial h o y hb,
    (TangentCone.coneData h o).dist_sq,
    (TangentCone.coneData h o).normSq_scale ha.1,
    (TangentCone.coneData h o).normSq_scale hb.1,
    (TangentCone.coneData h o).pairing_scale ha.1 hb.1,
    TangentCone.normSq_log, TangentCone.normSq_log] at hh
  nlinarith only [hh]

end CATZero

namespace SamplingSequence
universe u v w
variable {F : Type u} [DecidableEq F] {Admissible : Finset F → Prop}
  {L Ω : ℕ → Type v} [∀ n, Fintype (L n)] [∀ n, Nonempty (L n)]
  [∀ n, DecidableEq (L n)] [∀ n, Fintype (Ω n)] [∀ n, Nonempty (Ω n)]
  {label : ∀ n, Ω n → F → L n} (S : SamplingSequence F Admissible L Ω label)
  {X : ℕ → Type w} [∀ n, MetricSpace (X n)] {M : ℝ}
  (O : ∀ n, EnergyOrbit (L n) (X n) M)
include S

/-- Uniform fractional-distance comparison for any bounded point function of
I, after translations depending on the whole match. -/
theorem fractional_error {I : Finset F} {e : F} (he : e ∉ I)
    (hI : Admissible (insert e I)) (σ : ∀ n, L n ≃ L n)
    (test : ∀ n, Ω n → X n)
    (depends : ∀ n a b, (∀ i ∈ I, label n a i = label n b i) → test n a = test n b)
    {B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (htest : ∀ n a, dist (O n).base (test n a) ≤ B)
    (frame : ∀ n, Ω n → X n ≃ᵢ X n) {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      a ^ 2 * (𝔼 m, dist (frame n m (O n).base) (frame n m (test n m)) ^ 2) +
        b ^ 2 * (𝔼 m, dist (frame n m (O n).base)
          (frame n m ((O n).isom (σ n (label n m e)) (O n).base)) ^ 2) - ε ≤
      𝔼 m, dist
        (CATZero.segment (O n).cat (frame n m (O n).base) (frame n m (test n m)) a)
        (CATZero.segment (O n).cat (frame n m (O n).base)
          (frame n m ((O n).isom (σ n (label n m e)) (O n).base)) b) ^ 2 := by
  let logTest (n : ℕ) (m : Ω n) := TangentCone.log (O n).cat (O n).base (test n m)
  have hc := S.conditional O he hI σ logTest
    (fun n m k hh => by simp only [logTest, depends n m k hh]) hM hB
    (fun n m => by
      change dist (TangentCone.vertex _ _) _ ≤ B
      rw [TangentCone.dist_vertex_log]
      exact htest n m)
  intro ε hε
  filter_upwards [hc (ε / 2) (by positivity)] with n hn
  have hi := Finset.expect_le_expect (s := Finset.univ)
    (fun (m : Ω n) _ => CATZero.fractional_log_comparison (O n).cat (O n).base
      (test n m) ((O n).isom (σ n (label n m e)) (O n).base) ha hb)
  simp only [Finset.expect_sub_distrib, Finset.expect_add_distrib, ← Finset.mul_expect] at hi
  simp only [(frame n _).isometry.dist_eq, ← CATZero.isometry_segment (O n).cat (frame n _) _ _ ha,
    ← CATZero.isometry_segment (O n).cat (frame n _) _ _ hb] 
  have hab : 0 ≤ 2 * a * b := mul_nonneg (mul_nonneg (by norm_num) ha.1) hb.1
  have hab' : 2 * a * b ≤ 2 := by nlinarith [mul_le_mul ha.2 hb.2 hb.1 (by norm_num : (0:ℝ) ≤ 1)]
  have he' := mul_le_mul_of_nonneg_left hn.le hab
  change 2 * a * b * (𝔼 m, (O n).cone.pairing
    (TangentCone.log (O n).cat (O n).base (test n m))
    (TangentCone.log (O n).cat (O n).base ((O n).isom (σ n (label n m e)) (O n).base))) ≤ _ at he'
  nlinarith

end SamplingSequence
end HyperbolicObstruction
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordDisk
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.WordPictures.instNormalFreeGroupPictureSubgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


/-! Algebraic van Kampen existence, with actual words and area-counted local
moves (not a finiteness or isoperimetric assumption). Free cancellation has
zero cost; each orientation of a listed relator disk has cost one. -/
noncomputable section
namespace HyperbolicObstruction.WordPictures

variable {A : Type*}

lemma relators_in_null (R : Set (Word A)) : FreeGroup.mk '' R ⊆ nullSubgroup R := by
  rintro _ ⟨w,hw,rfl⟩
  exact ⟨w,rfl,1,by simpa using (Homotopy.move (Move.face [] [] w hw))⟩

/-- Null words in the ordinary presented group have a finite area-counted
word disk. No boundedness, reducedness or planarity premise is required. -/
theorem existence {R : Set (Word A)} (w : Word A)
    (h : PresentedGroup.mk (FreeGroup.mk '' R) (FreeGroup.mk w) = 1) :
    ∃ n, Homotopy R w [] n := by
  have hg := PresentedGroup.mk_eq_one_iff.mp h
  have hh := (Subgroup.normalClosure_le_normal (relators_in_null R)) hg
  obtain ⟨v,he,n,hv⟩ := hh
  exact ⟨n,by simpa using (Homotopy.free he.symm).trans hv⟩

end HyperbolicObstruction.WordPictures
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Graph
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.IncidenceTemplate.instFieldFintype _root_.OAI.HyperbolicObstruction.LetterPresentation.group
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
namespace MasterGraph
open IncidenceTemplate

namespace Path
variable {a b c : Vertex}

lemma fields_length (p : Path a b) : p.fields.length = p.length := by
  induction p with
  | nil => rfl
  | cons s p ih => simp only [fields, List.length_cons, length, ih]

end Path

lemma core_adj_ne {a b : CoreGeometry.Vertex} (h : CoreGeometry.Adjacent a b) : a ≠ b := by
  cases a <;> cases b <;> first | exact h.elim | exact Sum.inl_ne_inr | exact Sum.inr_ne_inl

lemma coreEdge_eq {a b c d : CoreGeometry.Vertex} (h : CoreGeometry.Adjacent a b)
    (h' : CoreGeometry.Adjacent c d) (he : coreEdge h = coreEdge h') :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    first | exact h.elim | exact h'.elim |
      (have hv := congrArg Subtype.val he;
        simp only [coreEdge, Prod.mk.injEq] at hv; aesop)

lemma coreEdge_fan {a b : CoreGeometry.Vertex} (h : CoreGeometry.Adjacent a b) (i : Fin 7) :
    coreEdge h ∈ fan i ↔ CoreGeometry.InFan i a b := by
  cases a <;> cases b <;> first | exact h.elim |
    (unfold fan; rw [Finset.mem_filter]; simp [coreEdge, isLoose, CoreGeometry.InFan])

lemma coreEdge_ne_consecutive {a b c : CoreGeometry.Vertex} (h : CoreGeometry.Adjacent a b)
    (h' : CoreGeometry.Adjacent b c) (hne : a ≠ c) : coreEdge h ≠ coreEdge h' := by
  intro he
  rcases coreEdge_eq h h' he with hh | hh
  · exact core_adj_ne h hh.1
  · exact hne hh.1

lemma coreEdge_ne_third {a b c d : CoreGeometry.Vertex} (h : CoreGeometry.Adjacent a b)
    (h' : CoreGeometry.Adjacent b c) (h'' : CoreGeometry.Adjacent c d) (hne : a ≠ c) :
    coreEdge h ≠ coreEdge h'' := by
  intro he
  rcases coreEdge_eq h h'' he with hh | hh
  · exact hne hh.1
  · exact core_adj_ne h' hh.2

lemma corePath_three_nodup {a b c d : CoreGeometry.Vertex} (h : CoreGeometry.Adjacent a b)
    (h' : CoreGeometry.Adjacent b c) (h'' : CoreGeometry.Adjacent c d)
    (hac : a ≠ c) (hbd : b ≠ d) :
    [(.inl (coreEdge h) : Field), .inl (coreEdge h'), .inl (coreEdge h'')].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, Sum.inl.injEq,
    not_or, List.nodup_nil, and_true, not_false_eq_true]
  exact ⟨⟨coreEdge_ne_consecutive h h' hac, coreEdge_ne_third h h' h'' hac⟩,
    coreEdge_ne_consecutive h' h'' hbd⟩

lemma admissible_down (I J : Finset Field) (hIJ : I ⊆ J) (hJ : Admissible J) : Admissible I := by
  rcases hJ with ⟨hzero, hcard, hfan⟩ | ⟨τ, hτ, hc⟩
  · left
    refine ⟨Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => ?_), ?_, ?_⟩
    · have hh := Finset.toRight_subset_toRight hIJ hx
      rw [hzero] at hh
      exact Finset.notMem_empty _ hh
    · exact (Finset.card_le_card (Finset.toLeft_subset_toLeft hIJ)).trans hcard
    · intro i
      exact (Finset.card_le_card (Finset.inter_subset_inter (Finset.toLeft_subset_toLeft hIJ)
        (Finset.Subset.refl _))).trans (hfan i)
  · exact Or.inr ⟨τ, hIJ.trans hτ, (Finset.card_le_card hIJ).trans hc⟩

lemma admissible_core_triple (e f g : Edge)
    (hq : ∀ i, ¬(e ∈ fan i ∧ f ∈ fan i ∧ g ∈ fan i)) :
    Admissible {(.inl e : Field), .inl f, .inl g} := by
  left
  refine ⟨by ext x; simp, ?_⟩
  have hleft : ({(.inl e : Field), .inl f, .inl g} : Finset Field).toLeft = {e,f,g} := by
    ext x
    simp
  rw [hleft]
  refine ⟨Finset.card_le_three, fun i => ?_⟩
  unfold fanCount
  have hpair (a b : Edge) : ({a,b} : Finset Edge).card ≤ 2 := Finset.card_le_two
  by_cases he : e ∈ fan i
  · by_cases hf : f ∈ fan i
    · have hg : g ∉ fan i := fun hg => hq i ⟨he, hf, hg⟩
      apply (Finset.card_le_card (show {e,f,g} ∩ fan i ⊆ {e,f} from ?_)).trans (hpair e f)
      intro x hx
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx.1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (hg (h ▸ hx.2)).elim
    · apply (Finset.card_le_card (show {e,f,g} ∩ fan i ⊆ {e,g} from ?_)).trans (hpair e g)
      intro x hx
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx.1 with h | h | h
      · exact Or.inl h
      · exact (hf (h ▸ hx.2)).elim
      · exact Or.inr h
  · apply (Finset.card_le_card (show {e,f,g} ∩ fan i ⊆ {f,g} from ?_)).trans (hpair f g)
    intro x hx
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx.1 with h | h | h
    · exact (he (h ▸ hx.2)).elim
    · exact Or.inl h
    · exact Or.inr h

lemma corePath_three_admissible {a b c d : CoreGeometry.Vertex} (h : CoreGeometry.Adjacent a b)
    (h' : CoreGeometry.Adjacent b c) (h'' : CoreGeometry.Adjacent c d)
    (hq : CoreGeometry.ThreeQuota a b c d) :
    Admissible [(.inl (coreEdge h) : Field), .inl (coreEdge h'), .inl (coreEdge h'')].toFinset := by
  simp only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]
  apply admissible_core_triple
  intro i hi
  exact hq i ⟨(coreEdge_fan h i).mp hi.1, (coreEdge_fan h' i).mp hi.2.1,
    (coreEdge_fan h'' i).mp hi.2.2⟩

end MasterGraph
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_GraphAction
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.IncidenceTemplate.instFieldFintype _root_.OAI.HyperbolicObstruction.LetterPresentation.group
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
namespace MasterGraph
open IncidenceTemplate

namespace Path
variable {G L : Type*} [Group G] {a b c : Vertex}

lemma compatible_congr (p : Path a b) {σ τ : Field → Bool}
    (h : ∀ f ∈ p.fields, σ f = τ f) (hp : p.Compatible σ) : p.Compatible τ := by
  induction p with
  | nil => trivial
  | cons s p ih =>
    exact ⟨(h s.field (by simp [fields])).symm.trans hp.1,
      ih (fun f hf => h f (by simp [fields, hf])) hp.2⟩

lemma exists_compatible (p : Path a b) (h : p.fields.Nodup) : ∃ σ, p.Compatible σ := by
  classical
  induction p with
  | nil => exact ⟨fun _ => true, trivial⟩
  | cons s p ih =>
    obtain ⟨σ, hσ⟩ := ih (List.nodup_cons.mp h).2
    refine ⟨Function.update σ s.field s.forward, ?_, ?_⟩
    · simp
    · apply p.compatible_congr (σ := σ) _ hσ
      intro f hf
      rw [Function.update_of_ne]
      intro he
      exact (List.nodup_cons.mp h).1 (he ▸ hf)

lemma eval_word (p : Path a b) {σ : Field → Bool} (hσ : p.Compatible σ)
    (label : Field → L) (letter : L → G) (inv : L ≃ L)
    (hinv : ∀ i, letter (inv i) = (letter i)⁻¹) :
    p.eval label letter = OrbitWord.word (fun _ : Unit => label) (read inv σ) letter () p.fields := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    simp only [eval, fields, OrbitWord.cons, ih hσ.2]
    congr 1
    cases hs : s.forward <;> simp [Step.value, read, hσ.1, hs, hinv]

end Path

namespace Potential
variable {L G : Type*} [Group G] {label : Field → L} {letter : L → G}
  (g : Potential label letter)

lemma orbit_path {X : Type*} [MetricSpace X] (A : G →* (X ≃ᵢ X)) (o : X)
    {a b : Vertex} (p : Path a b) :
    dist (A (g.val a) o) (A (g.val b) o) = dist o (A (p.eval label letter) o) := by
  rw [g.path p, map_mul, IsometryEquiv.mul_apply]
  exact (A (g.val a)).isometry.dist_eq _ _

end Potential
end MasterGraph
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SixRows
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace SixTable
variable {A : Type*} [Fintype A] [DecidableEq A]

lemma row_card_sum (w : (Fin 6 → A) → Bool) (u : A) (j : Fin 5) :
    (Fintype.card (Rows w u) : ℝ) = ∑ v : A, count 0 j.succ u v w := by
  simp_rw [← card_row_fiber]
  rw [← Nat.cast_sum,FiniteLaw.card_fibers]

variable [Nonempty A]

/-- The literal uniform law on the six-letter relators with first letter u has
all five remaining marginal densities at most twice uniform. -/
theorem marginal_bound {δ τ : ℝ} {w : (Fin 6 → A) → Bool}
    (hτ : τ ≤ 1/3) (h : ¬BadPairs δ τ w) (u : A) :
    letI := rows_nonempty (by linarith : τ < 1) h u
    ∀ j v, (((FiniteLaw.uniform : FiniteLaw (Rows w u)).map (fun x => row w u x j)).mass v)
      ≤ 2 / Fintype.card A := by
  let := rows_nonempty (by linarith : τ < 1) h u
  intro j v
  rw [FiniteLaw.uniform_map_mass,card_row_fiber]
  have hn : 0 < (Fintype.card A:ℝ) := by exact_mod_cast Fintype.card_pos (α := A)
  have hr : 0 < (Fintype.card (Rows w u):ℝ) := by exact_mod_cast Fintype.card_pos (α := Rows w u)
  have hp : 0 < (Fintype.card A:ℝ)^(1-δ) := Real.rpow_pos_of_pos hn _
  have hx := (count_bounds h (Ne.symm (Fin.succ_ne_zero j)) u v).2.le
  have hsum : (Fintype.card A:ℝ)*((1-τ)*(Fintype.card A:ℝ)^(1-δ)) ≤
      (Fintype.card (Rows w u):ℝ) := by
    rw [row_card_sum w u j]
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun v _ =>
        (count_bounds h (Ne.symm (Fin.succ_ne_zero j)) u v).1.le)
  rw [div_le_div_iff₀ hr hn]
  have ha : (1+τ)*(Fintype.card A:ℝ)^(1-δ) ≤
      2*((1-τ)*(Fintype.card A:ℝ)^(1-δ)) := by nlinarith
  calc
    count 0 j.succ u v w * Fintype.card A ≤
        (2*((1-τ)*(Fintype.card A:ℝ)^(1-δ)))*Fintype.card A :=
      mul_le_mul_of_nonneg_right (hx.trans ha) hn.le
    _ = 2*((Fintype.card A:ℝ)*((1-τ)*(Fintype.card A:ℝ)^(1-δ))) := by ring
    _ ≤ 2*Fintype.card (Rows w u) := mul_le_mul_of_nonneg_left hsum (by norm_num)

end SixTable
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Presentation
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction

namespace LetterPresentation
open IncidenceTemplate MasterGraph
variable (n : ℕ)

variable (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma letter_inv (a : Alphabet n) : letter n w d (inverseLetter n a) = (letter n w d a)⁻¹ := by
  simp only [letter,freeLetter_inv,map_inv]

lemma letter_generates : Subgroup.closure (Set.range (letter n w d)) = ⊤ := by
  apply top_unique
  rw [← PresentedGroup.closure_range_of (Relator n w d)]
  apply Subgroup.closure_mono
  rintro _ ⟨i,rfl⟩
  exact ⟨(i,true),rfl⟩

lemma six_relator (x : Fin 6 → Alphabet n) (hx : d x = true) :
    (List.ofFn (letter n w d ∘ x)).prod = 1 := by
  have hh := PresentedGroup.one_of_mem (show Relator n w d ((List.ofFn (freeLetter n ∘ x)).prod) from Relator.six x hx)
  simpa only [map_list_prod,List.map_ofFn,Function.comp_def,letter] using hh


lemma six_tail_relator (u : Alphabet n) (x : SixTable.Rows d u) :
    (List.ofFn (letter n w d ∘ SixTable.row d u x)).prod = (letter n w d u)⁻¹ := by
  have hh := six_relator n w d x.val x.property.2
  rw [List.ofFn_succ,List.prod_cons] at hh
  have hu : (letter n w d ∘ x.val) 0 = letter n w d u := congrArg _ x.property.1
  rw [hu] at hh
  exact eq_inv_of_mul_eq_one_right hh

end LetterPresentation
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_CoreWordGraph
attribute [-instance] _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.CoreWordGraph
open IncidenceTemplate CoreGeometry MasterGraph LetterPresentation SimpleGraph
variable (S : Finset IncidenceTemplate.Edge)

lemma cycle_length {a : CoreGeometry.Vertex} (p : (graph S).Walk a a) (hp : p.IsCycle) :
    p.length ≤ 18 := by
  have h := hp.nodup_dropLast_support
  have hd := h.length_le_card
  have hl := p.length_support
  have hd' : p.support.dropLast.length ≤ 18 := by simpa using hd
  simpa using hd'

end HyperbolicObstruction.CoreWordGraph
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FiniteSampling
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.LetterPresentation.group
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate

lemma ConditionalTest.singleton_bound {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (e : Field) {w : TableModel.Entry (A := A) rowSupport → Bool} {η : ℝ}
    (h : ((singletonData e).test 0).Satisfies w η) :
    ∃ hne : Nonempty (StarModel.Matches rowSupport w), letI := hne
      ((FiniteLaw.uniform : FiniteLaw (StarModel.Matches rowSupport w)).map (fun a => a.val e)).totalVariation
        FiniteLaw.uniform ≤ 2*η := by
  classical
  obtain ⟨hne,κ,hb,hl⟩ := h
  let := hne
  refine ⟨hne,?_⟩
  let f : StarModel.Matches rowSupport w → A := fun a => a.val e
  let g : (Fin 1 → A) → A := fun a => a 0
  have hu : (FiniteLaw.uniform : FiniteLaw (Fin 1 → A)).map g = FiniteLaw.uniform :=
    FiniteLaw.map_uniform_equiv (Equiv.funUnique (Fin 1) A)
  have ha := FiniteLaw.totalVariation_map_le
    (FiniteLaw.uniform : FiniteLaw (StarModel.Matches rowSupport w))
    (κ.map (ConditionalStar.branch 0)) f
  have hb' : (FiniteLaw.uniform : FiniteLaw (StarModel.Matches rowSupport w)).totalVariation
      (κ.map (ConditionalStar.branch 0)) ≤ η := by
    rw [FiniteLaw.totalVariation_comm]
    exact hb 0
  have hc := FiniteLaw.totalVariation_map_le
    (κ.map (fun z j => (ConditionalStar.branch j z).val e))
    (FiniteLaw.uniform : FiniteLaw (Fin 1 → A)) g
  rw [hu,FiniteLaw.map_map] at hc
  rw [FiniteLaw.map_map] at ha
  have hh := FiniteLaw.totalVariation_triangle
    ((FiniteLaw.uniform : FiniteLaw (StarModel.Matches rowSupport w)).map f)
    (κ.map (g ∘ (fun z j => (ConditionalStar.branch j z).val e))) FiniteLaw.uniform
  change _ ≤ 2*η
  exact hh.trans (by dsimp only [g,f,Function.comp_def] at *; linarith)

end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_DiagonalSampling
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate

lemma stageError_tendsto : Tendsto stageError atTop (𝓝 0) := by
  have ht : Tendsto (fun m : ℕ => m+4) atTop atTop :=
    tendsto_atTop_mono (f := id) (fun m => Nat.le_add_right m 4) tendsto_id
  change Tendsto (fun m : ℕ => (1:ℝ) / ((m:ℝ)+4)) atTop (𝓝 0)
  simpa only [Function.comp_def,Nat.cast_add,Nat.cast_ofNat] using
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp ht


end IncidenceTemplate
end HyperbolicObstruction
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_GraphSquares
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.IncidenceTemplate.instFieldFintype _root_.OAI.HyperbolicObstruction.LetterPresentation.group
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
namespace MasterGraph
open IncidenceTemplate

lemma code_injective : Function.Injective code := by
  intro e f hh
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  all_goals
    have he := e.val.2.isLt
    have hf := f.val.2.isLt
    unfold code at hh
    omega

/-- Every literal nonbacktracking core two-path is one of the ninety
square slots, up to reversal. -/
lemma twoPath_complete {a b c : CoreGeometry.Vertex}
    (hab : CoreGeometry.Adjacent a b) (hbc : CoreGeometry.Adjacent b c) (hac : a ≠ c) :
    ∃ τ : TwoPath, (left τ = a ∧ middle τ = b ∧ right τ = c) ∨
      (left τ = c ∧ middle τ = b ∧ right τ = a) := by
  rcases a with r | l <;> rcases b with r' | l' <;> rcases c with r'' | l''
  all_goals first | exact hab.elim | exact hbc.elim | skip
  · have hne : r ≠ r'' := fun he => hac (congrArg Sum.inl he)
    let e : Edge := ⟨(r,l'), hab⟩
    let f : Edge := ⟨(r'',l'), hbc⟩
    have hcode : code e ≠ code f := fun he => hne (congrArg (fun e : Edge => e.val.1) (code_injective he))
    by_cases hlt : code e < code f
    · refine ⟨⟨(e,f), hlt, Or.inr rfl⟩, Or.inl ?_⟩
      simp [left, middle, right, e, f, hne]
    · refine ⟨⟨(f,e), lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm hcode), Or.inr rfl⟩, Or.inr ?_⟩
      simp [left, middle, right, e, f, Ne.symm hne]
  · have hne : l ≠ l'' := fun he => hac (congrArg Sum.inr he)
    let e : Edge := ⟨(r',l), hab⟩
    let f : Edge := ⟨(r',l''), hbc⟩
    have hcode : code e ≠ code f := fun he => hne (congrArg (fun e : Edge => e.val.2) (code_injective he))
    by_cases hlt : code e < code f
    · refine ⟨⟨(e,f), hlt, Or.inl rfl⟩, Or.inl ?_⟩
      simp [left, middle, right, e, f]
    · refine ⟨⟨(f,e), lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm hcode), Or.inl rfl⟩, Or.inr ?_⟩
      simp [left, middle, right, e, f]

lemma square_core_ne (τ : TwoPath) : τ.val.1 ≠ τ.val.2 := by
  intro he
  have hh := τ.property.1
  rw [he] at hh
  exact (lt_irrefl _ hh)

lemma admissible_square_pair (τ : TwoPath) (e f : Field)
    (he : e ∈ squareSupport τ) (hf : f ∈ squareSupport τ) : Admissible {e,f} := by
  exact Or.inr ⟨τ, by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro he hf,
    Finset.card_le_two⟩

lemma first_mem_square (τ : TwoPath) : (first τ).field ∈ squareSupport τ := by
  simp [first_field, squareSupport]
lemma second_mem_square (τ : TwoPath) : (second τ).field ∈ squareSupport τ := by
  simp [second_field, squareSupport]
lemma fresh_mem_square (τ : TwoPath) (j : Fin 2) : (.inr (τ,j) : Field) ∈ squareSupport τ := by
  fin_cases j <;> simp [squareSupport]

end MasterGraph
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_OrbitLimit
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace OrbitLimit
universe u v
variable {L Ω : ℕ → Type u} [∀ n, Fintype (L n)]
  [∀ n, Fintype (Ω n)] [∀ n, Nonempty (Ω n)]
  {X : ℕ → Type v} [∀ n, MetricSpace (X n)] {M : ℝ}
  (O : ∀ n, EnergyOrbit (L n) (X n) M)

variable (U : Ultrafilter ℕ)

variable {O U}
lemma tendsto_dist_sq (x y : Array (Ω := Ω) O) :
    Tendsto (fun n => 𝔼 m, dist (x.val n m) (y.val n m) ^ 2) U
      (𝓝 (dist (point O U x) (point O U y) ^ 2)) := by
  convert MetricLimit.tendsto_point_dist_sq (boundedSection O U x) (boundedSection O U y) using 1
  · funext n
    exact (MeanProduct.dist_sq ((boundedSection O U x).val n) ((boundedSection O U y).val n)).symm
  · rfl

lemma dist_sq_eq (hU : (U : Filter ℕ) ≤ atTop) (x y : Array (Ω := Ω) O) {a : ℝ}
    (h : Tendsto (fun n => 𝔼 m, dist (x.val n m) (y.val n m) ^ 2) atTop (𝓝 a)) :
    dist (point O U x) (point O U y) ^ 2 = a :=
  tendsto_nhds_unique (tendsto_dist_sq x y) (h.mono_left hU)

lemma dist_sq_lower (hU : (U : Filter ℕ) ≤ atTop) (x y : Array (Ω := Ω) O) {a : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      a - ε ≤ 𝔼 m, dist (x.val n m) (y.val n m) ^ 2) :
    a ≤ dist (point O U x) (point O U y) ^ 2 := by
  apply MetricLimit.lower_of_eventually hU (boundedSection O U x) (boundedSection O U y)
  intro ε hε
  simpa only [boundedSection, MeanProduct.dist_sq, MeanProduct.ofFn_apply] using h ε hε

omit [∀ n, Fintype (Ω n)] [∀ n, Nonempty (Ω n)] in
lemma segment_val (x y : Array (Ω := Ω) O) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (m : Ω n) :
    (segment x y t).val n m = CATZero.segment (O n).cat (x.val n m) (y.val n m) t := by
  simp only [segment, dite_eq_left ht]

lemma section_segment (x y : Array (Ω := Ω) O) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    boundedSection O U (segment x y t) =
      MetricLimit.segment (productCat (Ω := Ω) O) (boundedSection O U x) (boundedSection O U y) t := by
  apply MetricLimit.Bounded.ext
  funext n
  rw [MetricLimit.segment_val _ _ _ ht]
  apply MetricScale.Space.ext
  apply PiLp.ext
  intro m
  change (segment x y t).val n m = MeanProduct.apply
    (CATZero.segment (productCat (Ω := Ω) O n) _ _ t) m
  rw [segment_val x y ht, MeanProduct.apply_segment (fun _ => (O n).cat) _ _ ht]
  rfl

lemma point_segment (x y : Array (Ω := Ω) O) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    point O U (segment x y t) = CATZero.segment (catZero O U) (point O U x) (point O U y) t := by
  unfold point
  rw [section_segment x y ht]
  exact MetricLimit.point_segment _ _ _ ht

end OrbitLimit
end HyperbolicObstruction

noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace SamplingSequence
open OrbitLimit
universe u v w z
variable {F : Type u} [DecidableEq F] {Admissible : Finset F → Prop}
  {L Ω : ℕ → Type v} [∀ n, Fintype (L n)] [∀ n, Nonempty (L n)]
  [∀ n, DecidableEq (L n)] [∀ n, Fintype (Ω n)] [∀ n, Nonempty (Ω n)]
  {label : ∀ n, Ω n → F → L n} (S : SamplingSequence F Admissible L Ω label)
  {X : ℕ → Type w} [∀ n, MetricSpace (X n)] {M : ℝ}
  (O : ∀ n, EnergyOrbit (L n) (X n) M)
  {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ atTop)
include S hU

/-- Every actual labelled edge has unit limiting squared length, including
edges whose orientation is read backwards. -/
lemma limit_edge (x y : OrbitLimit.Array (Ω := Ω) O) (e : F)
    (σ : ∀ n, L n ≃ L n) (hM : 0 ≤ M)
    (hxy : ∀ n m, dist (x.val n m) (y.val n m) =
      dist (O n).base ((O n).isom (σ n (label n m e)) (O n).base)) :
    dist (point O U x) (point O U y) ^ 2 = 1 := by
  apply dist_sq_eq hU
  simpa only [hxy] using S.edge_energy O e σ hM

/-- The full distinct-field path estimate in the genuine mean-product
ultralimit. -/
lemma limit_path {G : ℕ → Type z} [∀ n, Group (G n)]
    (A : ∀ n, G n →* (X n ≃ᵢ X n)) (letter : ∀ n, L n → G n)
    (hact : ∀ n i, A n (letter n i) = (O n).isom i)
    (down : ∀ I J, I ⊆ J → Admissible J → Admissible I)
    (x y : OrbitLimit.Array (Ω := Ω) O) (σ : ∀ n, F → L n ≃ L n) (hM : 0 ≤ M)
    (w : List F) (hw : w.Nodup) (hadm : Admissible w.toFinset)
    (hxy : ∀ n m, dist (x.val n m) (y.val n m) =
      dist (O n).base (A n (OrbitWord.word (label n) (σ n) (letter n) m w) (O n).base)) :
    (w.length : ℝ) ≤ dist (point O U x) (point O U y) ^ 2 := by
  apply dist_sq_lower hU
  simpa only [hxy] using S.word_lower O A letter hact down σ hM w hw hadm

/-- Fixed-fraction points pass through the product ultralimit before making
any angle assertion. This is the precise exceptional ternary test. -/
lemma limit_fractional {I : Finset F} {e : F} (he : e ∉ I)
    (hI : Admissible (insert e I)) (σ : ∀ n, L n ≃ L n)
    (test : ∀ n, Ω n → X n)
    (depends : ∀ n a b, (∀ i ∈ I, label n a i = label n b i) → test n a = test n b)
    {B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (htest : ∀ n m, dist (O n).base (test n m) ≤ B)
    (frame : ∀ n, Ω n → X n ≃ᵢ X n)
    (o x y : OrbitLimit.Array (Ω := Ω) O)
    (ho : ∀ n m, o.val n m = frame n m (O n).base)
    (hx : ∀ n m, x.val n m = frame n m (test n m))
    (hy : ∀ n m, y.val n m = frame n m ((O n).isom (σ n (label n m e)) (O n).base))
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    a ^ 2 * dist (point O U o) (point O U x) ^ 2 +
      b ^ 2 * dist (point O U o) (point O U y) ^ 2 ≤
      dist (CATZero.segment (catZero O U) (point O U o) (point O U x) a)
        (CATZero.segment (catZero O U) (point O U o) (point O U y) b) ^ 2 := by
  rw [← point_segment o x ha, ← point_segment o y hb]
  apply le_of_forall_pos_le_add
  intro ε hε
  have he' := S.fractional_error O he hI σ test depends hM hB htest frame ha hb ε hε
  have hh : ∀ᶠ n in (U : Filter ℕ),
      a ^ 2 * (𝔼 m, dist (o.val n m) (x.val n m) ^ 2) +
        b ^ 2 * (𝔼 m, dist (o.val n m) (y.val n m) ^ 2) - ε ≤
      𝔼 m, dist ((OrbitLimit.segment o x a).val n m) ((OrbitLimit.segment o y b).val n m) ^ 2 := by
    filter_upwards [hU he'] with n hn
    simpa only [OrbitLimit.segment_val _ _ ha, OrbitLimit.segment_val _ _ hb, ho, hx, hy] using hn
  have ht := le_of_tendsto_of_tendsto
    ((((tendsto_dist_sq o x).const_mul (a ^ 2)).add ((tendsto_dist_sq o y).const_mul (b ^ 2))).sub_const ε)
    (tendsto_dist_sq (OrbitLimit.segment o x a) (OrbitLimit.segment o y b)) hh
  linarith

end SamplingSequence
end HyperbolicObstruction
end
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_GraphLimit
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.IncidenceTemplate.instFieldFintype _root_.OAI.HyperbolicObstruction.LetterPresentation.group
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace MasterGraph
open IncidenceTemplate OrbitLimit
universe u v w
variable {L Ω : ℕ → Type u} [∀ n, Fintype (L n)] [∀ n, Nonempty (L n)]
  [∀ n, DecidableEq (L n)] [∀ n, Fintype (Ω n)] [∀ n, Nonempty (Ω n)]
  {label : ∀ n, Ω n → Field → L n}
  {X : ℕ → Type v} [∀ n, MetricSpace (X n)] {M : ℝ}
  (O : ∀ n, EnergyOrbit (L n) (X n) M)
  {G : ℕ → Type w} [∀ n, Group (G n)]
  (A : ∀ n, G n →* (X n ≃ᵢ X n)) (letter : ∀ n, L n → G n)
  (hact : ∀ n i, A n (letter n i) = (O n).isom i)
  (g : ∀ n m, Potential (label n m) (letter n)) (hM : 0 ≤ M)

variable (S : SamplingSequence Field Admissible L Ω label)
  {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ atTop)
  (inv : ∀ n, L n ≃ L n) (hinv : ∀ n i, letter n (inv n i) = (letter n i)⁻¹)

include S hU in
lemma side {a b : Vertex} (s : Step a b) :
    dist (limit (U := U) O A letter hact g hM a) (limit (U := U) O A letter hact g hM b) ^ 2 = 1 := by
  apply S.limit_edge O hU _ _ s.field (fun n => Equiv.refl (L n)) hM
  intro n m
  change dist (A n ((g n m).val a) (O n).base) (A n ((g n m).val b) (O n).base) = _
  rw [(g n m).orbit_path (A n) (O n).base (.cons s (.nil _))]
  simp only [Path.eval, mul_one, Equiv.refl_apply]
  cases hs : s.forward
  · simp only [Step.value, hs, Bool.false_eq_true, ↓reduceIte,
      IsometricAction.displacement_inv, hact]
  · simp only [Step.value, hs, ↓reduceIte, hact]

include S hU hinv in
lemma path_lower {a b : Vertex} (p : Path a b) (hp : p.fields.Nodup)
    (hadm : Admissible p.fields.toFinset) :
    (p.length : ℝ) ≤ dist (limit (U := U) O A letter hact g hM a) (limit (U := U) O A letter hact g hM b) ^ 2 := by
  obtain ⟨σ,hσ⟩ := p.exists_compatible hp
  rw [← p.fields_length]
  apply S.limit_path O hU A letter hact admissible_down _ _
    (fun n => Path.read (inv n) σ) hM p.fields hp hadm
  intro n m
  change dist (A n ((g n m).val a) (O n).base) (A n ((g n m).val b) (O n).base) = _
  rw [(g n m).orbit_path (A n) (O n).base p]
  have he := p.eval_word hσ (label n m) (letter n) (inv n) (hinv n)
  simp only [he, OrbitWord.word]

include S hU hinv in
lemma square_twoStep (τ : TwoPath) :
    dist (limit (U := U) O A letter hact g hM (.inl (left τ)))
      (limit (U := U) O A letter hact g hM (.inl (right τ))) ^ 2 = 2 := by
  let a := limit (U := U) O A letter hact g hM (.inl (left τ))
  let b := limit (U := U) O A letter hact g hM (.inl (middle τ))
  let c := limit (U := U) O A letter hact g hM (.inl (right τ))
  let d := limit (U := U) O A letter hact g hM (.inr τ)
  have hab : dist a b ^ 2 = 1 := side O A letter hact g hM S hU (first τ)
  have hbc : dist b c ^ 2 = 1 := side O A letter hact g hM S hU (second τ)
  have hcd : dist c d ^ 2 = 1 := side O A letter hact g hM S hU (Step.pos (.inr (τ,0)))
  have hda : dist d a ^ 2 = 1 := by
    simpa only [source, target, show (1 : Fin 2) ≠ 0 from by decide, ↓reduceIte] using
      side O A letter hact g hM S hU (Step.pos (.inr (τ,1)))
  have hac : 2 ≤ dist a c ^ 2 := by
    let p := Path.cons (first τ) (.cons (second τ) (.nil _))
    have hp : p.fields.Nodup := by simpa [p, Path.fields, first_field, second_field] using square_core_ne τ
    have ha : Admissible p.fields.toFinset := by
      simpa only [p, Path.fields, List.toFinset_cons, List.toFinset_nil, Finset.insert_empty] using
        admissible_square_pair τ _ _ (first_mem_square τ) (second_mem_square τ)
    exact path_lower O A letter hact g hM S hU inv hinv p hp ha
  have hbd : 2 ≤ dist b d ^ 2 := by
    let p := Path.cons (second τ) (.cons (Step.pos (.inr (τ,0))) (.nil _))
    have hp : p.fields.Nodup := by simp [p, Path.fields, second_field, Step.pos]
    have ha : Admissible p.fields.toFinset := by
      simpa only [p, Path.fields, Step.pos, List.toFinset_cons, List.toFinset_nil, Finset.insert_empty] using
        admissible_square_pair τ _ _ (second_mem_square τ) (fresh_mem_square τ 0)
    exact path_lower O A letter hact g hM S hU inv hinv p hp ha
  have hq := CATZero.quadrilateral (OrbitLimit.catZero O U) a b c d
  rw [hab,hbc,hcd,hda] at hq
  nlinarith [sq_nonneg (dist (CATZero.mid (OrbitLimit.catZero O U) a c)
    (CATZero.mid (OrbitLimit.catZero O U) b d))]

include S hU hinv in
/-- Source Proposition configuration (i), constructed from matches, paths,
unit edge expectations, and decorating-square rigidity. -/
theorem metricCore : CoreGeometry.MetricCore
    (fun v => limit (U := U) O A letter hact g hM (.inl v)) := by
  constructor
  · intro a b hab
    exact side O A letter hact g hM S hU (coreStep hab)
  · intro a b c hab hbc hac
    obtain ⟨τ, hh | hh⟩ := twoPath_complete hab hbc hac
    · rw [← hh.1, ← hh.2.2]
      exact square_twoStep O A letter hact g hM S hU inv hinv τ
    · rw [← hh.1, ← hh.2.2, dist_comm]
      exact square_twoStep O A letter hact g hM S hU inv hinv τ
  · intro a b c d hab hbc hcd hac hbd hq
    let p := Path.cons (coreStep hab) (.cons (coreStep hbc) (.cons (coreStep hcd) (.nil _)))
    have hp : p.fields.Nodup := by
      simpa only [p, Path.fields, coreStep_field] using corePath_three_nodup hab hbc hcd hac hbd
    have ha : Admissible p.fields.toFinset := by
      simpa only [p, Path.fields, coreStep_field] using corePath_three_admissible hab hbc hcd hq
    exact path_lower O A letter hact g hM S hU inv hinv p hp ha

end MasterGraph
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RankCollection
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate.Occurrences

lemma GoodUpTo.mono {M L n : ℕ} {α β δ : ℝ} {w : Entry (SymmetricAlphabet n) → Bool}
    (h : GoodUpTo M α β δ w) (hLM : L ≤ M) : GoodUpTo L α β δ w := by
  intro b
  exact h.rank_bound b.shape ((Nat.le_of_lt_succ b.1.isLt).trans hLM)
    ((Nat.le_of_lt_succ b.2.1.isLt).trans hLM)
    ((Nat.le_of_lt_succ b.2.2.1.isLt).trans hLM)
    ((Nat.le_of_lt_succ b.2.2.2.1.isLt).trans hLM)

end IncidenceTemplate.Occurrences
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SimpleLetterPresentation
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.LetterPresentation
open IncidenceTemplate CoreGeometry MasterGraph SimpleGraph
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma simpleWordRelator_length {z : List (Alphabet n)} (hz : SimpleWordRelator n w d z) :
    z.length ≤ 18 := by
  cases hz with
  | fan l i present v p hp =>
      rw [GraphWordFilling.word_length]; exact CoreWordGraph.cycle_length _ p hp
  | top l present fans v p hp =>
      rw [GraphWordFilling.word_length]; exact CoreWordGraph.cycle_length _ p hp
  | square => simp [literalSquare]
  | six => simp

/-- Finiteness is proved from literal words, including coinciding labels and
repeated rows, not asserted as an extra presentation hypothesis. -/
theorem simpleWordRelator_finite : Set.Finite {z | SimpleWordRelator n w d z} := by
  let g : (Σ k : Fin 19, Fin k.val → Alphabet n) → List (Alphabet n) := fun x => List.ofFn x.2
  apply (Set.finite_range g).subset
  intro z hz
  refine ⟨⟨⟨z.length,by have hh := simpleWordRelator_length n w d hz; omega⟩,
    fun i => z[i]⟩,?_⟩
  exact List.ofFn_get z

end HyperbolicObstruction.LetterPresentation
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SamplingStage
attribute [-instance] _root_.OAI.HyperbolicObstruction.Coincidence.instDecidablePredForallBoolRankBad _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.IncidenceTemplate.Occurrences.BoundedShape.instDecidablePredForallEntrySymmetricAlphabetBoolGood _root_.OAI.HyperbolicObstruction.IncidenceTemplate.Occurrences.Shape.instDecidablePredForallEntrySymmetricAlphabetBoolGood _root_.OAI.HyperbolicObstruction.IncidenceTemplate.Occurrences.instDecidablePredForallEntrySymmetricAlphabetBoolGoodUpTo _root_.OAI.HyperbolicObstruction.IncidenceTemplate.SamplingStage.instNonemptyRows _root_.OAI.HyperbolicObstruction.LetterPresentation.group
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate

namespace SamplingStage
variable {δ : ℕ → ℝ} (s : ∀ m, SamplingStage m (δ m))

/-- The genuine pure combinatorial sampling sequence, obtained by diagonalizing
actual finite table realizations. The laws in its conclusion are not hypotheses. -/
theorem samplingSequence : SamplingSequence Field Admissible (Alphabet s) (Matches s) (label s) where
  singleton e := by
    have hh : ∀ m, (((FiniteLaw.uniform : FiniteLaw ((Matches s) m)).map
        (fun a => (label s) m a e)).totalVariation FiniteLaw.uniform) ≤ 2*stageError m := by
      intro m
      exact ((ConditionalTest.singleton_bound e ((s m).tests (singletonData e) 0 (Nat.zero_le _))).choose_spec)
    exact squeeze_zero (fun m => FiniteLaw.totalVariation_nonneg _ _) hh
      (by simpa using stageError_tendsto.const_mul 2)
  star I e he ha k := by
    let p : ConditionalData := ⟨(I,e),he,ha⟩
    refine ⟨stageError,stageError_tendsto,?_⟩
    filter_upwards [eventually_ge_atTop k] with m hm
    obtain ⟨hne,κ,hb,hl⟩ := (s m).tests p k hm
    exact ⟨κ,hb,hl⟩

end SamplingStage

end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RankSampling
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.IncidenceTemplate.SamplingStage.instNonemptyRows _root_.OAI.HyperbolicObstruction.LetterPresentation.group
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate

lemma rankSelectedStage_good (M : ℕ → ℕ) (m : ℕ) :
    Occurrences.GoodUpTo (M m) (samplingParameter m) (8*samplingParameter m) (samplingParameter m)
      (Sum.elim (rankSelectedStage M m).master (rankSelectedStage M m).six) :=
  (actualRankSamplingStage M m).rank_good

end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Exceptional
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.IncidenceTemplate.instFieldFintype _root_.OAI.HyperbolicObstruction.LetterPresentation.group
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open Filter Topology
namespace HyperbolicObstruction
namespace CoreGeometry.MetricCore
variable {Y : Type*} [MetricSpace Y] {z : CoreGeometry.Vertex → Y}
  (D : CoreGeometry.MetricCore z) (h : CATZero Y)
include D

lemma exceptional_radius :
    dist (z (.inr 4)) (CATZero.mid h (z (.inl 2)) (z (.inl 9))) ^ 2 = 1 / 2 := by
  have hm := CATZero.square_mid h
    (D.side (.inl 2) (.inr 4) (by decide))
    (D.side (.inr 4) (.inl 9) (by decide))
    (D.side (.inl 9) (.inr 1) (by decide))
    (D.side (.inr 1) (.inl 2) (by decide))
    (D.twoStep (.inl 2) (.inr 4) (.inl 9) (by decide) (by decide) (by decide))
    (D.twoStep (.inr 4) (.inl 2) (.inr 1) (by decide) (by decide) (by decide))
  rw [hm, CATZero.mid, CATZero.segment_left h _ _ (by norm_num)]
  have hd := D.twoStep (.inr 4) (.inl 2) (.inr 1) (by decide) (by decide) (by decide)
  nlinarith
end CoreGeometry.MetricCore

namespace MasterGraph
open IncidenceTemplate OrbitLimit

lemma exc_not : (.inl excD : Field) ∉ excI := by decide
lemma exc_admissible : Admissible (insert (.inl excD) excI) := by
  left
  constructor
  · decide
  · unfold CoreAdmissible
    decide

universe u v w
variable {L Ω : ℕ → Type u} [∀ n, Fintype (L n)]
  {label : ∀ n, Ω n → Field → L n}
  {X : ℕ → Type v} [∀ n, MetricSpace (X n)] {M : ℝ}
  (O : ∀ n, EnergyOrbit (L n) (X n) M)
  {G : ℕ → Type w} [∀ n, Group (G n)]
  (A : ∀ n, G n →* (X n ≃ᵢ X n)) (letter : ∀ n, L n → G n)
  (hact : ∀ n i, A n (letter n i) = (O n).isom i)
  (g : ∀ n m, Potential (label n m) (letter n)) (hM : 0 ≤ M)
  (inv : ∀ n, L n ≃ L n) (hinv : ∀ n i, letter n (inv n i) = (letter n i)⁻¹)

include hinv in
lemma array_inverse (e : Edge) (n : ℕ) (m : Ω n) :
    (array O A letter hact g hM (.inl (.inl e.val.1))).val n m =
      A n ((g n m).val (.inl (.inr e.val.2)))
        ((O n).isom (inv n (label n m (.inl e))) (O n).base) := by
  have he := (g n m).step (Step.neg (.inl e))
  simp only [source, target, Step.value, Step.neg, Bool.false_eq_true, ↓reduceIte] at he
  change A n ((g n m).val (.inl (.inl e.val.1))) (O n).base = _
  rw [he, map_mul, IsometryEquiv.mul_apply, ← hinv, hact]

lemma excTest_depends (n : ℕ) (a b : Ω n)
    (hab : ∀ i ∈ excI, label n a i = label n b i) :
    excTest (label := label) O inv n a = excTest (label := label) O inv n b := by
  have hc := hab (.inl excC) (by simp [excI])
  have hy := hab (.inl excY) (by simp [excI])
  simp only [excTest, hc, hy]

lemma excTest_bound (n : ℕ) (m : Ω n) : dist (O n).base (excTest (label := label) O inv n m) ≤ 2 * M := by
  let x := (O n).isom (inv n (label n m (.inl excC))) (O n).base
  let y := (O n).isom (inv n (label n m (.inl excY))) (O n).base
  have hx : dist (O n).base x ≤ M := (O n).bound _
  have hy : dist (O n).base y ≤ M := (O n).bound _
  have hxy : dist x y ≤ 2 * M := by
    have ht := dist_triangle x (O n).base y
    rw [dist_comm x (O n).base] at ht
    linarith
  have ht := dist_triangle (O n).base x (excTest (label := label) O inv n m)
  change dist (O n).base (excTest (label := label) O inv n m) ≤ _
  change dist (O n).base (excTest (label := label) O inv n m) ≤ dist (O n).base x +
    dist x (CATZero.segment (O n).cat x y (1/2)) at ht
  rw [CATZero.segment_left _ _ _ (by norm_num)] at ht
  linarith

variable [∀ index, Nonempty (L index)] [∀ index, DecidableEq (L index)]
  [∀ index, Fintype (Ω index)] [∀ index, Nonempty (Ω index)]
  (S : SamplingSequence Field Admissible L Ω label)
  {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ atTop)

include hinv S hU in
/-- The source's decisive test is applied to the two actual C fields and
loose D field; its test depends only on the indicated two labels. -/
theorem exceptionalTest : CoreGeometry.ExceptionalTest (OrbitLimit.catZero O U)
    (fun v => limit (U := U) O A letter hact g hM (.inl v)) := by
  let p := array O A letter hact g hM (.inl (.inl 2))
  let q := array O A letter hact g hM (.inl (.inl 9))
  let o := array O A letter hact g hM (.inl (.inr 4))
  let z := array O A letter hact g hM (.inl (.inl 3))
  let J := OrbitLimit.segment p q (1/2)
  let frame (n : ℕ) (m : Ω n) := A n ((g n m).val (.inl (.inr 4)))
  have hhalf : (1/2 : ℝ) ∈ Set.Icc 0 1 := by norm_num
  have hp (n : ℕ) (m : Ω n) : p.val n m =
      frame n m ((O n).isom (inv n (label n m (.inl excC))) (O n).base) :=
    array_inverse O A letter hact g hM inv hinv excC n m
  have hq (n : ℕ) (m : Ω n) : q.val n m =
      frame n m ((O n).isom (inv n (label n m (.inl excY))) (O n).base) :=
    array_inverse O A letter hact g hM inv hinv excY n m
  have hJ (n : ℕ) (m : Ω n) : J.val n m = frame n m (excTest (label := label) O inv n m) := by
    rw [OrbitLimit.segment_val p q hhalf, hp, hq]
    exact (CATZero.isometry_segment (O n).cat (frame n m) _ _ hhalf).symm
  have hz (n : ℕ) (m : Ω n) : z.val n m =
      frame n m ((O n).isom (inv n (label n m (.inl excD))) (O n).base) :=
    array_inverse O A letter hact g hM inv hinv excD n m
  have hJlim : point O U J = CATZero.mid (OrbitLimit.catZero O U) (point O U p) (point O U q) :=
    OrbitLimit.point_segment p q hhalf
  have D := metricCore O A letter hact g hM S hU inv hinv
  have hrad : dist (point O U o) (point O U J) ^ 2 = 1 / 2 := by
    rw [hJlim]
    exact D.exceptional_radius (OrbitLimit.catZero O U)
  have hside : dist (point O U o) (point O U z) ^ 2 = 1 :=
    D.side (.inr 4) (.inl 3) (by decide)
  intro t ht
  have he := S.limit_fractional O hU exc_not exc_admissible inv (excTest (label := label) O inv)
    (excTest_depends O inv) hM (show 0 ≤ 2 * M by positivity) (excTest_bound O inv) frame
    o J z (fun _ _ => rfl) hJ hz (a := t) (b := t) ⟨ht.1.le,ht.2⟩ ⟨ht.1.le,ht.2⟩
  rw [hrad, hside, hJlim] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  ring

include O A letter hact g hM hinv S hU in
/-- No sequence of consistent literal-master-pattern actions with the
sampling conclusions can exist. -/
theorem impossible_sequence : False :=
  (metricCore O A letter hact g hM S hU inv hinv).impossible (OrbitLimit.catZero O U)
    (exceptionalTest O A letter hact g hM inv hinv S hU)

end MasterGraph
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Selection
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.IncidenceTemplate.instFieldFintype _root_.OAI.HyperbolicObstruction.LetterPresentation.group
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open Filter Topology
namespace HyperbolicObstruction

universe a b c

attribute [instance] CATActionWitness.metric CATActionWitness.nonempty
  CATActionWitness.proper CATActionWitness.complete

lemma catActionWitness_iff {G : Type a} [Group G] :
    Nonempty (CATActionWitness.{a,b} G) ↔ ¬ NoGeometricCATZeroAction.{b} G := by
  classical
  constructor
  · rintro ⟨W⟩ h
    exact (h W.Space W.metric W.nonempty W.proper W.complete W.cat).false W.action
  · intro h
    simp only [NoGeometricCATZeroAction, not_forall] at h
    obtain ⟨X, m, hn, hp, hc, hcat, ha⟩ := h
    exact ⟨⟨X, m, hn, hp, hc, hcat, Classical.choice (not_isEmpty_iff.mp ha)⟩⟩

namespace SamplingSequence
variable {F : Type*} [DecidableEq F] {Adm : Finset F → Prop}
  {L Ω : ℕ → Type*} [∀ n, Fintype (L n)] [∀ n, Nonempty (L n)]
  [∀ n, DecidableEq (L n)] [∀ n, Fintype (Ω n)] [∀ n, Nonempty (Ω n)]
  {label : ∀ n, Ω n → F → L n}

theorem reindex (S : SamplingSequence F Adm L Ω label) (f : ℕ → ℕ)
    (hf : Tendsto f atTop atTop) :
    @SamplingSequence F _ Adm (L ∘ f) (Ω ∘ f)
      (fun n => inferInstanceAs (Fintype (L (f n))))
      (fun n => inferInstanceAs (Nonempty (L (f n))))
      (fun n => inferInstanceAs (DecidableEq (L (f n))))
      (fun n => inferInstanceAs (Fintype (Ω (f n))))
      (fun n => inferInstanceAs (Nonempty (Ω (f n))))
      (fun n => label (f n)) := by
  let : ∀ n, Fintype ((L ∘ f) n) := fun n => inferInstanceAs (Fintype (L (f n)))
  let : ∀ n, Nonempty ((L ∘ f) n) := fun n => inferInstanceAs (Nonempty (L (f n)))
  let : ∀ n, DecidableEq ((L ∘ f) n) := fun n => inferInstanceAs (DecidableEq (L (f n)))
  let : ∀ n, Fintype ((Ω ∘ f) n) := fun n => inferInstanceAs (Fintype (Ω (f n)))
  let : ∀ n, Nonempty ((Ω ∘ f) n) := fun n => inferInstanceAs (Nonempty (Ω (f n)))
  refine ⟨fun e => (S.singleton e).comp hf, ?_⟩
  intro I e he ha k
  obtain ⟨η, hη, hh⟩ := S.star I e he ha k
  exact ⟨η ∘ f, hη.comp hf, hf.eventually hh⟩
end SamplingSequence

namespace MasterGraph
open IncidenceTemplate
variable {L Ω : ℕ → Type a} [∀ n, Fintype (L n)] [∀ n, Nonempty (L n)]
  [∀ n, DecidableEq (L n)] [∀ n, Fintype (Ω n)] [∀ n, Nonempty (Ω n)]
  {label : ∀ n, Ω n → Field → L n}
  {G : ℕ → Type c} [∀ n, Group (G n)] [∀ n, Infinite (G n)]
  (letter : ∀ n, L n → G n) (inv : ∀ n, L n ≃ L n)
  (hinv : ∀ n i, letter n (inv n i) = (letter n i)⁻¹)
  (hgen : ∀ n, Subgroup.closure (Set.range (letter n)) = ⊤)
  (g : ∀ n m, Potential (label n m) (letter n))
  (S : SamplingSequence Field Admissible L Ω label)
  (Row : ∀ n, L n → Type a) [∀ n i, Fintype (Row n i)]
  (κ : ∀ n i, FiniteLaw (Row n i)) (row : ∀ n i, Row n i → Fin 5 → L n)
  (hrow : ∀ n i r, (List.ofFn (letter n ∘ row n i r)).prod = (letter n i)⁻¹)
  (hmarg : ∀ n i j l, ((κ n i).map (fun r => row n i r j)).mass l ≤ 2 / Fintype.card (L n))

include hinv hgen g S κ hrow hmarg in
/-- The geometric half of selection: any infinite-group sequence with the
literal sampling assertions and six-letter rows has a no-action member. -/
theorem exists_noAction : ∃ n, NoGeometricCATZeroAction.{b} (G n) := by
  classical
  by_contra! h
  have hw (n : ℕ) : Nonempty (CATActionWitness.{c,b} (G n)) := catActionWitness_iff.mpr (h n)
  let W n := Classical.choice (hw n)
  have hn (n : ℕ) := EnergyOrbit.exists_of_geometric (W n).cat (W n).action
    (letter n) (inv n) (hinv n) (hgen n) (Row n) (κ n) (row n) (hrow n) (hmarg n)
  choose r hr O hO using hn
  let A (n : ℕ) := MetricScale.action (W n).action.act (r := r n) (hr := hr n)
  have hact (n : ℕ) (i : L n) : A n (letter n i) = (O n).isom i := (hO n i).symm
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  exact impossible_sequence O A letter hact g (by norm_num) inv hinv S hU

include hinv hgen g S κ hrow hmarg in
/-- Eventually the groups admit no geometric CAT(0) action. -/
theorem eventually_noAction : ∀ᶠ n in atTop, NoGeometricCATZeroAction.{b} (G n) := by
  classical
  by_contra h
  obtain ⟨f, hf, hn⟩ := exists_seq_forall_of_frequently (show ∃ᶠ n in atTop,
    ¬ NoGeometricCATZeroAction.{b} (G n) from by simpa only [Filter.Frequently, not_not] using h)
  let : ∀ n, Fintype ((L ∘ f) n) := fun n => inferInstanceAs (Fintype (L (f n)))
  let : ∀ n, Nonempty ((L ∘ f) n) := fun n => inferInstanceAs (Nonempty (L (f n)))
  let : ∀ n, DecidableEq ((L ∘ f) n) := fun n => inferInstanceAs (DecidableEq (L (f n)))
  let : ∀ n, Fintype ((Ω ∘ f) n) := fun n => inferInstanceAs (Fintype (Ω (f n)))
  let : ∀ n, Nonempty ((Ω ∘ f) n) := fun n => inferInstanceAs (Nonempty (Ω (f n)))
  let : ∀ n, Group ((G ∘ f) n) := fun n => inferInstanceAs (Group (G (f n)))
  let : ∀ n, Infinite ((G ∘ f) n) := fun n => inferInstanceAs (Infinite (G (f n)))
  let R (n : ℕ) := Row (f n)
  let : ∀ n i, Fintype (R n i) := fun n i => inferInstanceAs (Fintype (Row (f n) i))
  obtain ⟨n, hh⟩ := exists_noAction (L := L ∘ f) (Ω := Ω ∘ f) (G := G ∘ f)
    (fun n => letter (f n)) (fun n => inv (f n)) (fun n => hinv (f n))
    (fun n => hgen (f n)) (fun n => g (f n)) (S.reindex f hf) R
    (fun n => κ (f n)) (fun n => row (f n)) (fun n => hrow (f n)) (fun n => hmarg (f n))
  exact hn n hh

end MasterGraph
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SelectedPresentation
attribute [-instance] _root_.OAI.HyperbolicObstruction.Coincidence.instDecidablePredForallBoolRankBad _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeInteriorFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.IncidenceTemplate.Occurrences.BoundedShape.instDecidablePredForallEntrySymmetricAlphabetBoolGood _root_.OAI.HyperbolicObstruction.IncidenceTemplate.Occurrences.Shape.instDecidablePredForallEntrySymmetricAlphabetBoolGood _root_.OAI.HyperbolicObstruction.IncidenceTemplate.Occurrences.instDecidablePredForallEntrySymmetricAlphabetBoolGoodUpTo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate
namespace SamplingStage
variable {δ : ℕ → ℝ} (s : ∀ m, SamplingStage m (δ m))

lemma letter_inverse (m : ℕ) (i : (Alphabet s) m) :
    letter s m (inverse s m i) = (letter s m i)⁻¹ :=
  LetterPresentation.letter_inv _ _ _ _

lemma letter_generates (m : ℕ) : Subgroup.closure (Set.range (letter s m)) = ⊤ :=
  LetterPresentation.letter_generates _ _ _

lemma row_relation (m : ℕ) (u : (Alphabet s) m) (x : Rows s m u) :
    (List.ofFn (letter s m ∘ row s m u x)).prod = (letter s m u)⁻¹ :=
  LetterPresentation.six_tail_relator _ _ _ _ _

lemma marginal (m : ℕ) (u : (Alphabet s) m) (j : Fin 5) (i : (Alphabet s) m) :
    (((rowLaw s m u).map (fun x => row s m u x j)).mass i) ≤ 2 / Fintype.card ((Alphabet s) m) :=
  SixTable.marginal_bound (stageError_le_third m) (s m).six_good u j i

/-- Concrete no-action conclusion for the literal random letter presentations,
provided the still-missing diagram argument proves those same groups infinite.
The sampling laws, relator potentials, row relations and marginals are proved,
not supplied by this hypothesis. -/
theorem eventually_noAction [∀ m, Infinite (LetterGroup s m)] :
    ∀ᶠ m in atTop, NoGeometricCATZeroAction (LetterGroup s m) :=
  MasterGraph.eventually_noAction (letter s) (inverse s) (letter_inverse s)
    (letter_generates s) (potential s) (samplingSequence s) (Rows s) (rowLaw s)
    (row s) (row_relation s) (marginal s)

end SamplingStage
end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LiftedDiagramSampling
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.IncidenceTemplate
open CoreGeometry LetterPresentation ConeSkeleton PictureSwitch WordPictures
open Occurrences.Shape
attribute [local instance] Classical.propDecidable

lemma finalDiagramStage_good (m : ℕ) :
    Occurrences.GoodUpTo (finalDiagramCutoff m) (samplingParameter m) (8*samplingParameter m)
      (samplingParameter m) (Sum.elim (finalDiagramStage m).master (finalDiagramStage m).six) :=
  rankSelectedStage_good finalDiagramCutoff m

/-- Finite-letter linear filling for the same final selected arrays. -/
theorem finalDiagramStage_linear (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ word : List (LetterPresentation.Alphabet (finalDiagramStage m).size),
      PresentedGroup.mk (Relator (finalDiagramStage m).size (finalDiagramStage m).master
        (finalDiagramStage m).six) (FreeGroup.mk word) = 1 →
      ∃ a, WordPictures.Homotopy (SimpleWordRelator (finalDiagramStage m).size
        (finalDiagramStage m).master (finalDiagramStage m).six) word [] a ∧
        (a : ℝ) ≤ C * word.length := by
  let h := original_letter_linear_filling_list (samplingParameter_pos m)
    (by linarith [samplingParameter_pos m] : 7*samplingParameter m < 8*samplingParameter m)
    (samplingParameter_pos m)
  obtain ⟨C,_hM,hC,hh⟩ := h.choose_spec
  refine ⟨C,hC,?_⟩
  apply hh (finalDiagramStage m).size (finalDiagramStage m).master (finalDiagramStage m).six
  exact (finalDiagramStage_good m).mono ((le_max_left _ _).trans (le_max_left _ _))

/-- All lifted cellular coefficients vanish for every mapped spherical picture
for the final selected arrays. Unlike projected chain sums, coefficients for
different deck translates of one cell may be chosen independently. -/
theorem finalDiagramStage_lifted_chain_zero (m : ℕ)
    (G : Type) [Group G] (A : Type) [AddCommGroup A]
    (voltage : Dart (finalDiagramStage m).size (finalDiagramStage m).master → G)
    (hv : ∀ e, voltage (rev (finalDiagramStage m).size (finalDiagramStage m).master e) = (voltage e)⁻¹)
    (hcell : ∀ a : Cell (finalDiagramStage m).size (finalDiagramStage m).master (finalDiagramStage m).six,
      (List.ofFn (fun i => voltage (side (finalDiagramStage m).size (finalDiagramStage m).master
        (finalDiagramStage m).six a i))).prod = 1)
    (c : G → Top (finalDiagramStage m).size (finalDiagramStage m).master → MacroGraph.graph.Dart → A)
    (hc : ∀ g a e, c g a e.symm = -c g a e)
    (f : G → FrozenCell (finalDiagramStage m).size (finalDiagramStage m).master (finalDiagramStage m).six → A)
    (P : WalkPicture.{0} (liftedWalkTarget (finalDiagramStage m).size (finalDiagramStage m).master
      (finalDiagramStage m).six voltage hv hcell c hc f))
    (hm : P.FrozenMapped (liftedFrozenTarget (finalDiagramStage m).size (finalDiagramStage m).master
      (finalDiagramStage m).six voltage hv hcell c hc f)) : P.chain = 0 := by
  let h := uniform_actual_lifted_chain_zero.{0,0,0} (samplingParameter_pos m)
    (by linarith [samplingParameter_pos m] : 7*samplingParameter m < 8*samplingParameter m)
    (samplingParameter_pos m)
  exact h.choose_spec.2 (finalDiagramStage m).size (finalDiagramStage m).master (finalDiagramStage m).six
    ((finalDiagramStage_good m).mono (le_max_right _ _)) G A voltage hv hcell c hc f P hm

end HyperbolicObstruction.IncidenceTemplate
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ElementaryCone
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable

lemma macroCellDart_orientation (c : MacroCell) : macroOrientation (macroCellDart c) = 1 :=
  (macroCell_representative c).choose_spec.2

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FaceChainSelection
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! Counting one selected position on each actual indexed face. -/
noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D S A : Type*} [Fintype D] [DecidableEq D] [AddCommMonoid A]

omit [DecidableEq D] in
lemma faceChain_eq_selected (f : Perm D) (w : D → A) (hw : ∀ x, w (f x) = w x)
    (p : D → Prop) (hp : ∀ a, ∃! b, f.SameCycle a b ∧ p b) :
    faceChain f w hw = ∑ x : Subtype p, w x.val := by
  let j : Subtype p → Quotient (SameCycle.setoid f) := fun x => Quotient.mk _ x.val
  have hj : Function.Bijective j := by
    constructor
    · intro x y he
      have hxy : f.SameCycle x.val y.val := Quotient.exact he
      obtain ⟨b,hb,hub⟩ := hp x.val
      exact Subtype.ext ((hub x.val ⟨SameCycle.rfl,x.property⟩).trans
        (hub y.val ⟨hxy,y.property⟩).symm)
    · intro q
      induction q using Quotient.inductionOn with | h a =>
        obtain ⟨b,hb,_⟩ := hp a
        exact ⟨⟨b,hb.2⟩,Quotient.sound hb.1.symm⟩
  let e := Equiv.ofBijective j hj
  unfold faceChain classSum
  exact (Fintype.sum_equiv e (fun x : Subtype p => w x.val) _ (fun x => rfl)).symm

omit [DecidableEq D] in
lemma faceChain_eq_ite (f : Perm D) (w : D → A) (hw : ∀ x, w (f x) = w x)
    (p : D → Prop) (hp : ∀ a, ∃! b, f.SameCycle a b ∧ p b) :
    faceChain f w hw = ∑ x : D, if p x then w x else 0 := by
  rw [faceChain_eq_selected f w hw p hp]
  exact HyperbolicObstruction.sum_subtype_eq_ite p w

omit [Fintype D] [DecidableEq D] in
lemma IndexedFaceMap.selected (f : Perm D) (t : Perm S) (j : D → S)
    (hm : IndexedFaceMap f t j) (p : S → Prop)
    (hp : ∀ s, ∃! z, t.SameCycle s z ∧ p z) :
    ∀ a, ∃! b, f.SameCycle a b ∧ p (j b) := by
  intro a
  obtain ⟨s,hs,hus⟩ := hp (j a)
  obtain ⟨b,hb,hjb⟩ := hm.orbit_surjective a hs.1
  refine ⟨b,⟨hb,hjb ▸ hs.2⟩,?_⟩
  intro y hy
  have hys := hus (j y) ⟨semiconj_perm_sameCycle hm.commute hy.1,hy.2⟩
  exact hm.injective (hy.1.symm.trans hb) (hys.trans hjb.symm)

namespace PolygonTarget.Boundary
variable {C L V : Type*} (B : Boundary C L V)

lemma cell_cycle {s t : B.Side} (h : B.next.SameCycle s t) : s.1 = t.1 := by
  exact sameCycle_one.mp (semiconj_perm_sameCycle
    (t := (1 : Perm C)) (j := fun s : B.Side => s.1) (fun _ => rfl) h)

lemma marked_unique (mark : ∀ c, Fin (B.size c)) (s : B.Side) :
    ∃! t : B.Side, B.next.SameCycle s t ∧ t.2.2 = mark t.1 := by
  rcases s with ⟨c,b,i⟩
  refine ⟨⟨c,b,mark c⟩,⟨B.side_sameCycle c b i (mark c),rfl⟩,?_⟩
  rintro ⟨a,z,j⟩ ⟨hh,hj⟩
  have ha := B.cell_cycle hh
  have hz := B.orientation_cycle hh
  dsimp at ha hz hj
  subst a; subst z; subst j
  rfl
end PolygonTarget.Boundary
end HyperbolicObstruction.PictureSwitch
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FinitePolyhedron
attribute [-instance] _root_.OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.closedFace_compact _root_.OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.deckContinuous _root_.OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.totalSpace_t2 _root_.OAI.HyperbolicObstruction.FinitePolyhedron.openStar_contractible _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! Literal barycentric realizations of finite abstract complexes. No abstract
CW or homotopy replacement is used in the definitions. -/
noncomputable section
open scoped Topology
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [Fintype V]

lemma joined_of_simplex (K : AbstractSimplicialComplex V) {s : Finset V} (hs : s ∈ K.faces)
    (x y : Carrier K) (hx : x.val ∈ simplex s) (hy : y.val ∈ simplex s) : Joined x y := by
  exact (((simplex_convex s).isPathConnected ⟨x.val,hx⟩).joinedIn x.val hx y.val hy).mono
    (simplex_subset_carrier K hs) |>.joined_subtype

lemma vertex_joined_of_edge [DecidableEq V] (K : AbstractSimplicialComplex V) {a b : V}
    (hab : {a,b} ∈ K.faces) : Joined (vertex K a) (vertex K b) :=
  joined_of_simplex K hab _ _ (vertex_mem_simplex K (by simp)) (vertex_mem_simplex K (by simp))

lemma exists_joined_vertex (K : AbstractSimplicialComplex V) (x : Carrier K) :
    ∃ v : V, Joined x (vertex K v) := by
  obtain ⟨s,hs,hx⟩ := x.property.2.2
  obtain ⟨v,hv⟩ := (K.isRelLowerSet_faces hs).1
  exact ⟨v,joined_of_simplex K hs x _ ⟨x.property.1,x.property.2.1,hx⟩ (vertex_mem_simplex K hv)⟩

lemma pathConnected_of_vertex_connected (K : AbstractSimplicialComplex V) (v : V)
    (h : ∀ w, Joined (vertex K v) (vertex K w)) : PathConnectedSpace (Carrier K) := by
  refine ⟨⟨vertex K v⟩, fun x y => ?_⟩
  obtain ⟨a,ha⟩ := exists_joined_vertex K x
  obtain ⟨b,hb⟩ := exists_joined_vertex K y
  exact ha.trans ((h a).symm.trans ((h b).trans hb.symm))

end HyperbolicObstruction.FinitePolyhedron
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FinitePolygonModel
attribute [-instance] _root_.OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.closedFace_compact _root_.OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.deckContinuous _root_.OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.totalSpace_t2 _root_.OAI.HyperbolicObstruction.FinitePolyhedron.openStar_contractible _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite simplicial model of a literal finite polygon incidence system.
All edges are split three times, and every boundary occurrence has its own
collar vertex. Thus loops, repeated boundary vertices and parallel edges are
not silently identified. The carrier/homotopy comparison is a later theorem. -/
noncomputable section

namespace HyperbolicObstruction.FinitePolygonModel
open FinitePolyhedron

namespace Data
variable {V E C : Type*}
variable (P : Data V E C)

variable [DecidableEq V] [DecidableEq E] [DecidableEq C]

variable [Fintype V] [Fintype E] [Fintype C]

lemma joined_of_facet (f : P.Facet) {a b : P.Vertex} (ha : a ∈ P.facet f) (hb : b ∈ P.facet f) :
    Joined (vertex P.complex a) (vertex P.complex b) :=
  vertex_joined_of_edge P.complex (P.edge_of_facet f ha hb)

lemma mid_joined_start (e : E) (b : Bool) :
    Joined (vertex P.complex (P.mid e b)) (vertex P.complex (P.old (P.start (e,b)))) := by
  cases b
  · exact P.joined_of_facet (.inl (e,2)) (by simp [facet,graphFace]) (by simp [facet,graphFace])
  · exact P.joined_of_facet (.inl (e,0)) (by simp [facet,graphFace]) (by simp [facet,graphFace])

lemma endpoints_joined (e : E) :
    Joined (vertex P.complex (P.old (P.start (e,true))))
      (vertex P.complex (P.old (P.start (e,false)))) :=
  (P.mid_joined_start e true).symm.trans
    ((P.joined_of_facet (.inl (e,1)) (by simp [facet,graphFace]) (by simp [facet,graphFace])).trans
      (P.mid_joined_start e false))

lemma outer_joined_base (q : P.Position) :
    Joined (vertex P.complex (P.outer q)) (vertex P.complex (P.base q)) :=
  P.joined_of_facet (.inr (q,0)) (by simp [facet,collarFace]) (by simp [facet,collarFace])

lemma apex_joined_outer (c : C) :
    Joined (vertex P.complex (P.apex c))
      (vertex P.complex (P.outer ⟨c,(⟨0,P.positive c⟩,0)⟩)) :=
  P.joined_of_facet (.inr (⟨c,(⟨0,P.positive c⟩,0)⟩,2))
    (by simp [facet,collarFace]) (by simp [facet,collarFace])

/-- Connectedness is reduced exactly to the old graph, not assumed for the
new carrier. -/
lemma pathConnected_of_graph (v : V)
    (h : ∀ w : V, Joined (vertex P.complex (P.old v)) (vertex P.complex (P.old w))) :
    PathConnectedSpace (Carrier P.complex) := by
  have hm : ∀ e b, Joined (vertex P.complex (P.old v)) (vertex P.complex (P.mid e b)) :=
    fun e b => (h (P.start (e,b))).trans (P.mid_joined_start e b).symm
  have hb : ∀ q, Joined (vertex P.complex (P.old v)) (vertex P.complex (P.base q)) := by
    intro q
    dsimp [base,dartStart]
    split_ifs
    · exact h _
    · exact hm _ _
    · exact hm _ _
  have ho : ∀ q, Joined (vertex P.complex (P.old v)) (vertex P.complex (P.outer q)) :=
    fun q => (hb q).trans (P.outer_joined_base q).symm
  apply pathConnected_of_vertex_connected P.complex (P.old v)
  rintro ((w|⟨e,b⟩)|(c|q))
  · exact h w
  · exact hm e b
  · exact (ho _).trans (P.apex_joined_outer c).symm
  · exact ho q

end Data
end HyperbolicObstruction.FinitePolygonModel
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedWordPicture
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.WordPictures.instNormalFreeGroupPictureSubgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Persistent cell identities on word pictures. Unlike a bare relator witness,
this marking remembers which actual cell each interior face uses. -/
noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V : Type*}
  {R : Set (Word E)} {w : Word E}
  (B : PolygonTarget.Boundary C (E × Bool) V) (P : WordPicture R w)

namespace Indexing
variable {B P} (I : Indexing B P)

variable {A : Type*} [AddCommGroup A]

lemma cornerWeight_opposite (weight : C → A) (s : Option B.Side) :
    cornerWeight weight (s.map B.opposite) = - cornerWeight weight s := by
  cases s with
  | none => exact (neg_zero).symm
  | some s =>
    rcases s with ⟨c,b,i⟩
    by_cases hi : i.val = 0 <;> cases b <;>
      simp [cornerWeight,PolygonTarget.Boundary.opposite,PolygonTarget.Boundary.weight,hi]

lemma mirror_chain (hrev : B.rev = invLetter) (weight : C → A) :
    (I.mirror hrev).chain weight = - I.chain weight := by
  change (∑ x : P.Dart, cornerWeight weight ((I.index x).map B.opposite)) = _
  simp only [cornerWeight_opposite,Finset.sum_neg_distrib,chain]

end Indexing
end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedPictureAppend
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.WordPictures.instNormalFreeGroupPictureSubgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V : Type*} {R : Set (Word E)} {u v : Word E}
  {B : PolygonTarget.Boundary C (E × Bool) V}
  {P : WordPicture R u} {Q : WordPicture R v}
namespace Indexing
variable (I : Indexing B P) (J : Indexing B Q)
  (hp : P.outside ≠ []) (hq : Q.outside ≠ [])

variable {A : Type*} [AddCommGroup A]
lemma append_chain (weight : C → A) :
    (I.appendNonempty J hp hq).chain weight = I.chain weight + J.chain weight := by
  change (∑ x : P.Dart ⊕ Q.Dart, cornerWeight weight (Sum.elim I.index J.index x)) = _
  rw [Fintype.sum_sum_type]
  rfl

end Indexing
end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedPictureFold
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V : Type*} {R : Set (Word E)} {w : Word E}
  {B : PolygonTarget.Boundary C (E × Bool) V} {P : WordPicture R w}
namespace Indexing
variable (I : Indexing B P) {l r : List P.Dart} {a b : P.Dart}
  (he : P.outside = l++a::b::r) (hc : P.label a = invLetter (P.label b))

variable {A : Type*} [AddCommGroup A]
lemma fold_chain (weight : C → A) : (I.foldAt he hc).chain weight = I.chain weight := by
  have ha : I.index a = none := (I.outside a).mpr (by rw [he]; simp)
  have hb : I.index b = none := (I.outside b).mpr (by rw [he]; simp)
  change (∑ x : {x : P.Dart // OffPair a b x}, cornerWeight weight (I.index x.val)) = _
  erw [HyperbolicObstruction.sum_subtype_eq_ite (OffPair a b)
    (fun x : P.Dart => cornerWeight weight (I.index x))]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hxa : x = a
  · subst x; simp [OffPair,ha,cornerWeight]
  by_cases hxb : x = b
  · subst x; simp [OffPair,hb,cornerWeight]
  simp [OffPair,hxa,hxb]

end Indexing
end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedPictureReduction
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V A : Type*} [AddCommGroup A]
  {R : Set (Word E)} {w : Word E}
  {B : PolygonTarget.Boundary C (E × Bool) V} {P : WordPicture R w}
namespace Indexing
variable (I : Indexing B P) (weight : C → A)

lemma of_eq {v : Word E} (hw : w = v) :
    ∃ Q : WordPicture R v, ∃ J : Indexing B Q, J.chain weight = I.chain weight := by
  subst v
  exact ⟨P,I,rfl⟩

lemma of_step {v : Word E} (h : FreeGroup.Red.Step w v) :
    ∃ Q : WordPicture R v, ∃ J : Indexing B Q, J.chain weight = I.chain weight := by
  cases h with
  | @not l r x b =>
    obtain ⟨ls,rs,he,hl,hrs⟩ := List.map_eq_append_iff.mp P.word
    obtain ⟨a,rs',hr,ha,hrs'⟩ := List.map_eq_cons_iff.mp hrs
    obtain ⟨b',rs'',hr',hb,hrs''⟩ := List.map_eq_cons_iff.mp hrs'
    have hout : P.outside = ls++a::b'::rs'' := by rw [he,hr,hr']
    have hc : P.label a = invLetter (P.label b') := by rw [ha,hb]; simp [invLetter]
    have hw : (ls++rs'').map P.label = l++r := by rw [List.map_append,hl,hrs'']
    obtain ⟨Q,J,hJ⟩ := (I.foldAt hout hc).of_eq weight hw
    exact ⟨Q,J,hJ.trans (I.fold_chain hout hc weight)⟩

lemma of_red {v : Word E} (h : FreeGroup.Red w v) :
    ∃ Q : WordPicture R v, ∃ J : Indexing B Q, J.chain weight = I.chain weight := by
  induction h with
  | refl => exact ⟨P,I,rfl⟩
  | tail h h' ih =>
    obtain ⟨Q,J,hJ⟩ := ih
    obtain ⟨S,K,hK⟩ := J.of_step weight h'
    exact ⟨S,K,hK.trans hJ⟩

end Indexing
end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedDiskUniqueness
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disk-chain uniqueness follows from actual genus-zero sphere vanishing.
All operations retain the originally chosen precise interior cell identities. -/
noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture.Indexing
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V A : Type*} [AddCommGroup A]
  {R : Set (Word E)} {B : PolygonTarget.Boundary C (E × Bool) V}
  (hrev : B.rev = invLetter) (weight : C → A)
  (H : ∀ (S : WordPicture R []) (K : Indexing B S), K.chain weight = 0)

include hrev H in
lemma chain_unique {w : Word E} (P Q : WordPicture R w)
    (I : Indexing B P) (J : Indexing B Q) : I.chain weight = J.chain weight := by
  classical
  by_cases hw : w = []
  · subst w
    rw [H P I,H Q J]
  have hp : P.outside ≠ [] := by
    intro hp; apply hw; rw [← P.word,hp]; rfl
  have hq : Q.mirror.outside ≠ [] := by
    intro hq
    have hq' : Q.outside = [] := List.reverse_eq_nil_iff.mp hq
    apply hw; rw [← Q.word,hq']; rfl
  let K := I.appendNonempty (J.mirror hrev) hp hq
  have hred : FreeGroup.Red (w ++ FreeGroup.invRev w) [] := by
    have he : FreeGroup.reduce (w ++ FreeGroup.invRev w) = [] := by
      rw [← FreeGroup.toWord_mk,← FreeGroup.mul_mk,← FreeGroup.inv_mk,mul_inv_cancel,FreeGroup.toWord_one]
    simpa only [he] using (FreeGroup.reduce.red (L := w ++ FreeGroup.invRev w))
  obtain ⟨S,L,hL⟩ := K.of_red weight hred
  have hz := H S L
  rw [hL] at hz
  change (I.appendNonempty (J.mirror hrev) hp hq).chain weight = 0 at hz
  rw [append_chain,mirror_chain] at hz
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hz)

include hrev H in
lemma chain_free_eq {u v : Word E} (P : WordPicture R u) (Q : WordPicture R v)
    (I : Indexing B P) (J : Indexing B Q) (he : FreeGroup.mk u = FreeGroup.mk v) :
    I.chain weight = J.chain weight := by
  obtain ⟨w,hu,hv⟩ := FreeGroup.Red.exact.mp he
  obtain ⟨P',I',hI⟩ := I.of_red weight hu
  obtain ⟨Q',J',hJ⟩ := J.of_red weight hv
  exact hI.symm.trans ((chain_unique hrev weight H P' Q' I' J').trans hJ)

end HyperbolicObstruction.WordPictures.WordPicture.Indexing
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedPictureBasic
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact cell disks, free spurs and cyclic basepoint changes with persistent
cell-side identities. -/
noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V A : Type*} [AddCommGroup A]
  {R : Set (Word E)} {w : Word E} {B : PolygonTarget.Boundary C (E × Bool) V}

namespace Indexing

lemma empty_chain (weight : C → A) : (empty B R).chain weight = 0 := by
  change (∑ x : PEmpty, cornerWeight (B := B) weight (PEmpty.elim x)) = 0
  exact Finset.sum_eq_zero (fun x _ => PEmpty.elim x)

lemma freePair_chain (weight : C → A) (a : E × Bool) : (freePair B R a).chain weight = 0 := by
  simp [chain,freePair,cornerWeight]

end Indexing

variable (B) (hrev : B.rev = invLetter) (c : C)

lemma cellDisk_chain (weight : C → A) :
    (cellDiskIndex B hrev c).chain weight = -weight c := by
  classical
  change (∑ x : Bool × Fin (B.size c), Indexing.cornerWeight weight
    (if x.1 then none else some ⟨c,false,x.2⟩)) = _
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool,Bool.false_eq_true,ite_false,ite_true,Indexing.cornerWeight,
    PolygonTarget.Boundary.weight,Finset.sum_const_zero]
  have he : (∑ i : Fin (B.size c), if i.val = 0 then -weight c else 0) = -weight c := by
    have hh : ∀ i : Fin (B.size c), i.val = 0 ↔ i = ⟨0,B.positive c⟩ := fun i => by simp only [Fin.ext_iff]
    simp only [hh,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simpa only [zero_add] using he

end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedPictureClosed
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary _root_.OAI.HyperbolicObstruction.WordPictures.instNormalFreeGroupPictureSubgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V : Type*} {R : Set (Word E)}
  {B : PolygonTarget.Boundary C (E × Bool) V} {P : WordPicture R []}
namespace Indexing
variable (I : Indexing B P)

variable {A : Type*} [AddCommGroup A]
  (hrev : B.rev = invLetter) (weight : C → A)

lemma closed_chain : (I.closedPicture hrev weight).chain = I.chain weight := by
  let T := B.target weight (fun _ => false) (by intro _ impossible; cases impossible)
  have hh := faceChain_eq_ite P.pairing.face (B.weight weight ∘ I.closedIndex)
    (fun x => by rw [Function.comp_apply,I.closed_mapped.commute]; rfl)
    (fun x => (I.closedIndex x).2.2 = (⟨0,B.positive (I.closedIndex x).1⟩ : Fin _))
    (I.closed_mapped.selected _ _ _ _ (B.marked_unique (fun c => ⟨0,B.positive c⟩)))
  change faceChain P.pairing.face (B.weight weight ∘ I.closedIndex) _ = _
  rw [hh]
  apply Finset.sum_congr rfl
  intro x _
  rw [I.closedIndex_spec]
  simp only [cornerWeight,Function.comp_apply,Fin.ext_iff]

end Indexing
end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedPictureExistence
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal nullword disks with chosen persistent cell identities. -/
noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V : Type*} {R : Set (Word E)} {w : Word E}

variable {B : PolygonTarget.Boundary C (E × Bool) V} (P : WordPicture R w)

variable (B)
lemma indexing_exists (hrev : B.rev = invLetter)
    (P : WordPicture (Set.range B.attachingWord) w) : Nonempty (Indexing B P) := by
  let T := B.target (fun _ => (0 : ℤ)) (fun _ => false) (by intro l h; cases h)
  have hex : ∀ x : P.InsideDart, ∃ xs : List P.InsideDart, ∃ ys : List B.Side,
      IsBoundary P.insideFace xs ∧ x ∈ xs ∧ IsBoundary B.next ys ∧
        xs.map (P.label ∘ Subtype.val) = ys.map B.sideLabel := by
    intro x
    obtain ⟨xs,hs,hxm,hr⟩ := P.interior x.val x.property
    have hdis : ∀ a ∈ xs, a ∉ P.outside := by
      intro a ha hoa
      exact x.property (P.boundary.mem_of_sameCycle hoa (hs.sameCycle ha hxm))
    have hb : IsBoundary P.insideFace (xs.attachWith (fun a => a ∉ P.outside) hdis) :=
      hs.lift hdis P.insideFace (fun _ _ => rfl)
    have hm : x ∈ xs.attachWith (fun a => a ∉ P.outside) hdis :=
      (List.mem_attachWith hdis x).mpr hxm
    rcases hr with ⟨c,hc⟩ | ⟨c,hc⟩
    · refine ⟨_,B.positiveSides c,hb,hm,B.positiveSides_boundary c,?_⟩
      simpa only [Function.comp_def,List.attachWith_map_val,B.positiveSides_label] using hc.symm
    · refine ⟨_,(B.positiveSides c).reverse.map B.opposite,hb,hm,T.reverse_boundary (B.positiveSides_boundary c),?_⟩
      have hh := T.reverse_boundary_labels (xs := B.positiveSides c)
      change ((B.positiveSides c).reverse.map B.opposite).map B.sideLabel =
        ((B.positiveSides c).map (B.rev ∘ B.sideLabel)).reverse at hh
      rw [hh,hrev]
      have he : ((B.positiveSides c).map (invLetter ∘ B.sideLabel)).reverse =
          FreeGroup.invRev (B.attachingWord c) := by
        rw [← List.map_map,B.positiveSides_label]
        rfl
      rw [he,hc,FreeGroup.invRev_invRev]
      exact List.attachWith_map_val hdis
  obtain ⟨j,hj,hl⟩ := indexedFaceMap_exists P.insideFace B.next
    (P.label ∘ Subtype.val) B.sideLabel hex
  exact ⟨Indexing.ofInterior P j hj (fun x => (hl x).symm)⟩

end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltageCellGluing
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Genuine homotopy gluing on the locally finite family of closed lifted
simplices, with no alteration of the voltage-cover topology. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)
  {X : Type*} [TopologicalSpace X]

variable (H : ∀ q : FaceAnchor (K := K) × G, C(I × closedFace (K := K) q.1.val.1,X))
  (ha : ∀ i j t x y,
    v.faceLift i.1.property.1 i.1.property.2 i.2 x = v.faceLift j.1.property.1 j.1.property.2 j.2 y →
      H i (t,x) = H j (t,y))

lemma glueFaceHomotopies_apply (q : FaceAnchor (K := K) × G) (t : I)
    (x : closedFace (K := K) q.1.val.1) :
    v.glueFaceHomotopies H ha (t,v.faceLift q.1.property.1 q.1.property.2 q.2 x) = H q (t,x) := by
  rw [glueFaceHomotopies,ClosedCoverGluing.gluePrism_apply _ _ _ _ _ _ q t
    ⟨_,Set.mem_range_self x⟩]
  change H q (t,(v.faceLiftHomeomorph q).symm ((v.faceLiftHomeomorph q) x)) = _
  rw [(v.faceLiftHomeomorph q).symm_apply_apply]

lemma glueFaceHomotopies_endpoint (f : v.TotalSpace → X) (t : I)
    (hf : ∀ q x, H q (t,x) = f (v.faceLift q.1.property.1 q.1.property.2 q.2 x))
    (e : v.TotalSpace) : v.glueFaceHomotopies H ha (t,e) = f e := by
  obtain ⟨q,hq⟩ := Set.iUnion_eq_univ_iff.mp v.liftedClosedFace_cover e
  obtain ⟨x,rfl⟩ := hq
  rw [glueFaceHomotopies_apply,hf]

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltagePrismGluing
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine dimension-two contraction gluing theorem. Its local input is a
continuous prism for each face, compatible with the SAME edge prisms. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V] {K : AbstractSimplicialComplex V}
  {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  (v : Voltage K G)

variable (z : v.TotalSpace)

variable (E : v.EdgePrisms z)

variable (F : ∀ (s : Finset V) (hs : s ∈ K.faces), v.FacePrism z E s hs)

variable (hd : ∀ s ∈ K.faces, s.card ≤ 3)

lemma contraction_initial (e : v.TotalSpace) : v.contraction z E F hd (0,e) = e := by
  apply v.glueFaceHomotopies_endpoint
  intro q x
  exact ((F _ _).initial _ x).trans (v.anchoredFacePrism_lift z E F q x)
lemma contraction_final (e : v.TotalSpace) : v.contraction z E F hd (1,e) = z := by
  apply v.glueFaceHomotopies_endpoint (f := fun _ => z)
  intro q x
  exact (F _ _).final _ x

lemma contraction_edge {a b : V} (h : {a,b} ∈ K.faces) (g : G) (t r : I) :
    v.contraction z E F hd (t,v.edgeLift h g r) = E.H h g (t,r) := by
  let q : FaceAnchor (K := K) × G := (⟨({a,b},a),h,by simp⟩,g)
  change v.glueFaceHomotopies _ _ (t,v.faceLift h (a := a) (by simp) g (edgePoint h r)) = _
  rw [v.glueFaceHomotopies_apply (q := q)]
  exact (F _ _).edge h _ g t r (edgePoint h r)
    (v.anchoredFacePrism_lift z E F q (edgePoint h r))

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltageFacePrisms
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constructions of the actual face-prism input: every edge, and every
nondegenerate triangle with a literal three-sided contracting prism. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
open TriangleSquare
variable {V : Type*} [Fintype V] [DecidableEq V] {K : AbstractSimplicialComplex V}
  {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  (v : Voltage K G) (z : v.TotalSpace) (E : v.EdgePrisms z)

variable {a b : V} (h : {a,b} ∈ K.faces)

variable {c : V} (ht : {a,b,c} ∈ K.faces) (hi : Function.Injective ![a,b,c])
variable (H : G → C(I × Triangle,v.TotalSpace))
  (h0 : ∀ g p, H g (0,p) = v.triangleLift ht g p)
  (h1 : ∀ g p, H g (1,p) = z)
  (hb : ∀ g t r, H g (t,quotient (r,0)) = E.H (edge_of_subset K ht (by simp) (by simp) : {a,b} ∈ K.faces) g (t,r))
  (hl : ∀ g t r, H g (t,quotient (0,r)) = E.H (edge_of_subset K ht (by simp) (by simp) : {a,c} ∈ K.faces) g (t,r))
  (hr : ∀ g t r, H g (t,quotient (1,r)) = E.H (edge_of_subset K ht (by simp) (by simp) : {b,c} ∈ K.faces) (g*v.value a b) (t,r))

variable (hd : ∀ s ∈ K.faces, s.card ≤ 3)
  (hf : ∀ s (hs : s ∈ K.faces), s.card = 3 → Nonempty (v.FacePrism z E s hs))

lemma fromTrianglePrisms_initial (e : v.TotalSpace) : v.fromTrianglePrisms z E hd hf (0,e) = e :=
  v.contraction_initial z E _ hd e
lemma fromTrianglePrisms_final (e : v.TotalSpace) : v.fromTrianglePrisms z E hd hf (1,e) = z :=
  v.contraction_final z E _ hd e

lemma fromTrianglePrisms_edge {a b : V} (h : {a,b} ∈ K.faces) (g : G) (t r : I) :
    v.fromTrianglePrisms z E hd hf (t,v.edgeLift h g r) = E.H h g (t,r) :=
  v.contraction_edge z E _ hd h g t r

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PrismConcat
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! Continuous concatenation of literal prisms, with pointwise restriction
identities. No change in the endpoint maps is hidden by homotopy classes. -/
noncomputable section
open scoped Topology unitInterval
namespace HyperbolicObstruction.PrismConcat
variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

lemma constant_at (F G : C(I × Y,X)) (h : ∀ y, F (1,y) = G (0,y))
    (y : Y) (x : X) (hF : ∀ t, F (t,y) = x) (hG : ∀ t, G (t,y) = x) (t : I) :
    concat F G h (t,y) = x := by
  unfold concat
  simp only [ContinuousMap.Homotopy.coe_toContinuousMap,ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hF _
  · exact hG _

end HyperbolicObstruction.PrismConcat
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltageGraphHomotopy
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A coherent contraction of the actual lifted one-skeleton. The negative
orientation uses spatial reversal of the SAME square, not another choice. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

variable [SimplyConnectedSpace v.TotalSpace] (z : v.TotalSpace)

omit [LinearOrder V] in
lemma vertexTrack_fixed (a : V) (g : G) (h : v.vertexLift a g = z) (t : I) :
    v.vertexTrack z a g t = z := by
  simp [vertexTrack,h]

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltageTriangleContraction
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal contracting prism on each lifted triangle once its genuine pi2
obstruction is the coboundary of the constructed directed cochain. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
open TriangleSquare HSpacePathObstruction
variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)
  [SimplyConnectedSpace v.TotalSpace] (z : v.TotalSpace)
  (L : G → V → V → v.LoopClass z)
  (hs : ∀ g a, L g a a = 1)
  (hr : ∀ {a b}, {a,b} ∈ K.faces → ∀ g, L (g*v.value a b) b a = (L g a b)⁻¹)

lemma correctedEdge_fixed (a : V) (g : G) (he : v.vertexLift a g = z) (t r : I) :
    v.correctedEdge z L (edge_self K a) g (t,r) = z := by
  apply PrismConcat.constant_at
  · intro t
    change v.edgeHomotopy z (edge_self K a) g (t,r) = z
    simp only [edgeHomotopy,ite_true,eq_self]
    exact v.vertexTrack_fixed z a g he t
  · intro t
    change ((Path.refl (Path.refl z)).trans (v.correctionLoop z L (edge_self K a) g)) t r = z
    simp only [correctionLoop,ite_true,eq_self,Path.refl_trans_refl]
    rfl

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PolygonContraction
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A global continuous contraction of the literal polygon voltage cover,
constructed by cochain correction and locally finite closed-cell gluing. -/
noncomputable section

open scoped Topology unitInterval

namespace HyperbolicObstruction.FinitePolygonModel.Data
open FinitePolyhedron FinitePolyhedron.Voltage
variable {V E C G : Type*} [Fintype V] [Fintype E] [Fintype C]
  [DecidableEq V] [DecidableEq E] [DecidableEq C] [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (P : Data V E C) (ρ : E → G)
  (hc : ∀ c, (List.ofFn (fun i => signed ρ (P.side c i))).prod = 1)
  [LinearOrder P.Vertex] [SimplyConnectedSpace (P.voltage ρ hc).TotalSpace]
  (z : (P.voltage ρ hc).TotalSpace)

variable (w : G × E → Additive ((P.voltage ρ hc).LoopClass z))

attribute [local instance] OAI.HyperbolicObstruction.FinitePolygonModel.Data.instCommGroupLoopClassVertexVoltage
variable (hw : ∀ d c, (∑ i : Fin (P.size c),
    signedCochain ρ w (d*((List.ofFn (fun i => signed ρ (P.side c i))).take i.val).prod) (P.side c i)) =
    ∑ i : Fin (P.size c), ∑ j : Fin 3,
      P.triangleWeight (P.obstructionWeight ρ hc z) (d*P.cornerOffset ρ ⟨c,(i,j)⟩) ⟨c,(i,j)⟩)
lemma coverContraction_initial (e : (P.voltage ρ hc).TotalSpace) :
    P.coverContraction ρ hc z w hw (0,e) = e :=
  (P.voltage ρ hc).fromTrianglePrisms_initial _ _ _ _ e
lemma coverContraction_final (e : (P.voltage ρ hc).TotalSpace) :
    P.coverContraction ρ hc z w hw (1,e) = z :=
  (P.voltage ρ hc).fromTrianglePrisms_final _ _ _ _ e

lemma coverContraction_fixed (a : P.Vertex) (g : G)
    (he : (P.voltage ρ hc).vertexLift a g = z) (t : I) :
    P.coverContraction ρ hc z w hw (t,z) = z := by
  have hz : (P.voltage ρ hc).edgeLift (edge_self P.complex a) g 0 = z :=
    ((P.voltage ρ hc).edgeLift_self a g 0).trans he
  calc
    P.coverContraction ρ hc z w hw (t,z) =
        P.coverContraction ρ hc z w hw (t,(P.voltage ρ hc).edgeLift (edge_self P.complex a) g 0) :=
      congrArg (fun e => P.coverContraction ρ hc z w hw (t,e)) hz.symm
    _ = z := by
      rw [coverContraction,(P.voltage ρ hc).fromTrianglePrisms_edge]
      exact (P.voltage ρ hc).correctedEdge_fixed z (P.obstructionCochain ρ hc z w) a g he t 0

end HyperbolicObstruction.FinitePolygonModel.Data
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedFillingValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction

/-! The integral filling value of a literal nullword. This is a consequence
of constructed disks and sphere vanishing, not a replacement hypothesis. -/

namespace IndexedFilling
open HyperbolicObstruction.WordPictures HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V A : Type*} [AddCommGroup A]
  (B : PolygonTarget.Boundary C (E × Bool) V) (weight : C → A)

variable {B weight}
namespace HasChain
lemma empty : HasChain B weight [] 0 := by
  refine ⟨WordPicture.empty _,Indexing.empty B _,?_⟩
  rw [Indexing.empty_chain,neg_zero]

lemma exists_of_null (hrev : B.rev = invLetter) {w : Word E} (h : Null B w) :
    ∃ z, HasChain B weight w z := by
  obtain ⟨P⟩ := literal_picture_existence w h
  obtain ⟨I⟩ := indexing_exists B hrev P
  exact ⟨-I.chain weight,P,I,by rw [neg_neg]⟩

lemma free_unique (hrev : B.rev = invLetter) (hz : SphereZero B weight)
    {u v : Word E} {a b : A} (ha : HasChain B weight u a) (hb : HasChain B weight v b)
    (he : FreeGroup.mk u = FreeGroup.mk v) : a = b := by
  obtain ⟨P,I,hI⟩ := ha
  obtain ⟨Q,J,hJ⟩ := hb
  have hh := Indexing.chain_free_eq hrev weight hz P Q I J he
  rw [hI,hJ] at hh
  exact neg_injective hh

lemma add (hz : SphereZero B weight) {u v : Word E} {a b : A}
    (ha : HasChain B weight u a) (hb : HasChain B weight v b) :
    HasChain B weight (u++v) (a+b) := by
  obtain ⟨P,I,hI⟩ := ha
  obtain ⟨Q,J,hJ⟩ := hb
  by_cases hu : u = []
  · subst u
    have ha : a = 0 := neg_eq_zero.mp (hI.symm.trans (hz P I))
    simpa only [List.nil_append,ha,zero_add] using (show HasChain B weight v b from ⟨Q,J,hJ⟩)
  by_cases hv : v = []
  · subst v
    have hb : b = 0 := neg_eq_zero.mp (hJ.symm.trans (hz Q J))
    simpa only [List.append_nil,hb,add_zero] using (show HasChain B weight u a from ⟨P,I,hI⟩)
  have hp : P.outside ≠ [] := fun h => hu (by rw [←P.word,h]; rfl)
  have hq : Q.outside ≠ [] := fun h => hv (by rw [←Q.word,h]; rfl)
  refine ⟨P.appendNonempty Q hp hq,I.appendNonempty J hp hq,?_⟩
  rw [Indexing.append_chain,hI,hJ,neg_add]

lemma mirror (hrev : B.rev = invLetter) {w : Word E} {a : A}
    (h : HasChain B weight w a) : HasChain B weight (FreeGroup.invRev w) (-a) := by
  obtain ⟨P,I,hI⟩ := h
  exact ⟨P.mirror,I.mirror hrev,by rw [Indexing.mirror_chain,hI]⟩

lemma rotate {w : Word E} {a : A} (h : HasChain B weight w a) (k : ℕ) :
    HasChain B weight (w.rotate k) a := by
  obtain ⟨P,I,hI⟩ := h
  exact ⟨P.rotate k,I.rotate k,hI⟩

lemma freePair (e : E × Bool) : HasChain B weight [e,invLetter e] 0 :=
  ⟨WordPicture.freePair _ e,Indexing.freePair B _ e,by rw [Indexing.freePair_chain,neg_zero]⟩

lemma conjugateLetter (hz : SphereZero B weight) {w : Word E} {a : A}
    (h : HasChain B weight w a) (e : E × Bool) :
    HasChain B weight (e::(w++[invLetter e])) a := by
  have hh := ((h.add hz (freePair (B := B) (weight := weight) (invLetter e))).rotate (w.length+1))
  have he : (w++[invLetter e,invLetter (invLetter e)]).rotate (w.length+1) = e::(w++[invLetter e]) := by
    rw [invLetter_invLetter]
    simpa only [List.append_assoc,List.singleton_append,List.length_append,List.length_singleton]
      using (List.rotate_append_length_eq (w++[invLetter e]) [e])
  simpa only [he,add_zero] using hh

lemma conjugate (hz : SphereZero B weight) {w : Word E} {a : A}
    (h : HasChain B weight w a) (q : Word E) :
    HasChain B weight (q++w++FreeGroup.invRev q) a := by
  induction q with
  | nil => simpa using h
  | cons e q ih =>
    have hh := ih.conjugateLetter hz e
    rw [FreeGroup.invRev_cons,show FreeGroup.invRev [e] = [invLetter e] from rfl]
    simpa only [List.cons_append,List.append_assoc] using hh

lemma cell (hrev : B.rev = invLetter) (c : C) :
    HasChain B weight (B.attachingWord c) (weight c) :=
  ⟨cellDisk B c,cellDiskIndex B hrev c,cellDisk_chain B hrev c weight⟩
end HasChain

lemma value_spec (hrev : B.rev = invLetter) {w : Word E} (hw : Null B w) :
    HasChain B weight w (value (B := B) (weight := weight) w) := by
  have h := HasChain.exists_of_null (weight := weight) hrev hw
  simp only [value,dite_eq_left h]
  exact h.choose_spec

end IndexedFilling

/-! Literal walks in a signed incidence graph, with componentwise root paths.
No connectedness or universal-cover assertion is assumed. -/

namespace SignedWalks

section
open HyperbolicObstruction.WordPictures
variable {E V : Type*} (start : E × Bool → V)

namespace Walk
variable {start} {x y z : V} {u v : Word E}
lemma nil_iff : Walk start x y [] ↔ x = y := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil _

lemma cons_iff {e : E × Bool} : Walk start x y (e::u) ↔
    x = start e ∧ Walk start (start (invLetter e)) y u := by
  constructor
  · intro h; cases h with | cons e h => exact ⟨rfl,h⟩
  · rintro ⟨rfl,h⟩; exact .cons e h

lemma take_drop (h : Walk start x y u) (n : ℕ) :
    ∃ z, Walk start x z (u.take n) ∧ Walk start z y (u.drop n) := by
  induction h generalizing n with
  | nil x => exact ⟨x,by simpa using (Walk.nil (start := start) x),by simpa using (Walk.nil (start := start) x)⟩
  | cons e h ih =>
    cases n with
    | zero => exact ⟨start e,.nil _,.cons e h⟩
    | succ n =>
      obtain ⟨z,hz,hz'⟩ := ih n
      exact ⟨z,.cons e hz,hz'⟩

lemma get_start (h : Walk start x y u) (i : ℕ) (hi : i < u.length) :
    Walk start x (start u[i]) (u.take i) ∧
      Walk start (start (invLetter u[i])) y (u.drop (i+1)) := by
  obtain ⟨z,hz,hz'⟩ := h.take_drop i
  have he : u.drop i = u[i] :: u.drop (i+1) := List.drop_eq_getElem_cons hi
  rw [he,cons_iff] at hz'
  exact ⟨hz'.1 ▸ hz,hz'.2⟩

lemma adjacent (h : Walk start x y u) (i : ℕ) (hi : i+1 < u.length) :
    start u[i+1] = start (invLetter u[i]) := by
  obtain ⟨hpre,htail⟩ := h.get_start i (by omega)
  have he := List.drop_eq_getElem_cons hi
  rw [he,cons_iff] at htail
  exact htail.1.symm

lemma first (h : Walk start x y u) (hu : 0 < u.length) : start u[0] = x := by
  obtain ⟨hp,ht⟩ := h.get_start 0 hu
  exact (nil_iff.mp hp).symm

lemma last (h : Walk start x y u) (hu : 0 < u.length) :
    start (invLetter u[u.length-1]) = y := by
  obtain ⟨hp,ht⟩ := h.get_start (u.length-1) (by omega)
  have he : u.length-1+1 = u.length := by omega
  rw [he,List.drop_length,nil_iff] at ht
  exact ht

lemma closed_rotate (h : Walk start x x u) (hu : 0 < u.length) (i : Fin u.length) :
    start u[(finRotate u.length i).val] = start (invLetter u[i.val]) := by
  let : NeZero u.length := ⟨by omega⟩
  by_cases hi : i.val+1 < u.length
  · have he : (finRotate u.length i).val = i.val+1 := by
      rw [finRotate_apply]
      simp only [Fin.val_add,Fin.val_one']
      rw [Nat.add_mod_mod,Nat.mod_eq_of_lt hi]
    simpa only [he] using h.adjacent i.val hi
  · have hl : i.val = u.length-1 := by omega
    have he : (finRotate u.length i).val = 0 := by
      rw [finRotate_apply]
      simp only [Fin.val_add,Fin.val_one']
      rw [Nat.add_mod_mod]
      have hh : i.val+1 = u.length := by omega
      rw [hh,Nat.mod_self]
    simpa only [he,hl,h.first hu] using (h.last hu).symm
end Walk

lemma rootWord_walk (x : V) : Walk start (root start x) x (rootWord start x) :=
  (root_reach start x).choose_spec

lemma root_eq {x y : V} (h : (reach start).r x y) : root start x = root start y :=
  congrArg Quotient.out (Quotient.sound h)

lemma edge_root (e : E × Bool) : root start (start e) = root start (start (invLetter e)) :=
  root_eq start ⟨[e],Walk.single e⟩

lemma correction_walk (e : E × Bool) :
    Walk start (root start (start e)) (root start (start e)) (correction start e) := by
  have h := ((rootWord_walk start (start e)).append (Walk.single e)).append
    (rootWord_walk start (start (invLetter e))).reverse
  rw [←edge_root start e] at h
  exact h

end

open HyperbolicObstruction.WordPictures
variable {E V : Type*} {start : E × Bool → V}

lemma Walk.ofFn_vertices (n : ℕ) (f : Fin n → E × Bool) (vs : ℕ → V)
    (hs : ∀ i, start (f i) = vs i.val)
    (ht : ∀ i, start (invLetter (f i)) = vs (i.val+1)) :
    Walk start (vs 0) (vs n) (List.ofFn f) := by
  induction n generalizing vs with
  | zero => exact .nil _
  | succ n ih =>
    have hh := ih (fun i => f i.succ) (fun k => vs (k+1))
      (fun i => hs i.succ) (fun i => by simpa only [Fin.val_succ] using ht i.succ)
    have ht0 := ht (0 : Fin (n+1))
    have hs0 := hs (0 : Fin (n+1))
    simp only [Fin.val_zero,zero_add] at ht0 hs0
    rw [←ht0] at hh
    have hc := Walk.cons (f 0) hh
    rw [hs0] at hc
    simpa only [List.ofFn_succ] using hc

lemma Walk.ofFn_closed {n : ℕ} (hn : 0 < n) (f : Fin n → E × Bool)
    (hc : ∀ i, start (f (finRotate n i)) = start (invLetter (f i))) :
    Walk start (start (f ⟨0,hn⟩)) (start (f ⟨0,hn⟩)) (List.ofFn f) := by
  let : NeZero n := ⟨by omega⟩
  let vs : ℕ → V := fun k => start (f ⟨k%n,Nat.mod_lt _ hn⟩)
  have hs : ∀ i, start (f i) = vs i.val := by
    intro i
    dsimp [vs]
    congr 2
    exact (Fin.ext (Nat.mod_eq_of_lt i.isLt)).symm
  have ht : ∀ i, start (invLetter (f i)) = vs (i.val+1) := by
    intro i
    rw [←hc]
    dsimp [vs]
    congr 2
    rw [finRotate_apply]
    apply Fin.ext
    simp only [Fin.val_add,Fin.val_one',Nat.add_mod_mod]
  simpa only [vs,Nat.zero_mod,Nat.mod_self] using Walk.ofFn_vertices n f vs hs ht

/-- Product of rooted edge corrections is exactly the rooted original path;
all intermediate paths cancel in the free group, before taking any quotient. -/
lemma correction_telescope (root : V → Word E) {x y : V} {u : Word E}
    (h : Walk start x y u) :
    FreeGroup.mk (u.flatMap (fun e => root (start e) ++ [e] ++ FreeGroup.invRev (root (start (invLetter e))))) =
      FreeGroup.mk (root x ++ u ++ FreeGroup.invRev (root y)) := by
  induction h with
  | nil x =>
    simp only [List.flatMap_nil,List.append_nil]
    rw [←FreeGroup.mul_mk,←FreeGroup.inv_mk,mul_inv_cancel]
    rfl
  | cons e h ih =>
    simp only [List.flatMap_cons]
    rw [←FreeGroup.mul_mk,ih]
    simp only [←FreeGroup.mul_mk,←FreeGroup.inv_mk]
    change (FreeGroup.mk (root (start e)) * FreeGroup.mk [e] * (FreeGroup.mk (root (start (invLetter e))))⁻¹) *
      (FreeGroup.mk (root (start (invLetter e))) * FreeGroup.mk _ * (FreeGroup.mk (root _))⁻¹) =
      FreeGroup.mk (root (start e)) * (FreeGroup.mk [e] * FreeGroup.mk _) * (FreeGroup.mk (root _))⁻¹
    group

lemma correction_reverse (root : V → Word E) (e : E × Bool) :
    FreeGroup.mk (root (start (invLetter e)) ++ [invLetter e] ++ FreeGroup.invRev (root (start (invLetter (invLetter e))))) =
      (FreeGroup.mk (root (start e) ++ [e] ++ FreeGroup.invRev (root (start (invLetter e)))))⁻¹ := by
  simp only [invLetter_invLetter,←FreeGroup.mul_mk,←FreeGroup.inv_mk,mul_inv_rev,inv_inv]
  have he : FreeGroup.mk [invLetter e] = (FreeGroup.mk [e])⁻¹ := by
    change FreeGroup.mk (FreeGroup.invRev [e]) = _
    exact FreeGroup.inv_mk.symm
  rw [he]
  group

end SignedWalks

/-! A literal disk-chain left inverse for the integral cell boundary. The
rooted-edge construction avoids assuming an arbitrary-cycle sphere producer. -/

namespace IndexedFilling
open HyperbolicObstruction.WordPictures HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch SignedWalks
attribute [local instance] Classical.propDecidable
variable {C E V A : Type*} [AddCommGroup A]
  (B : PolygonTarget.Boundary C (E × Bool) V) (weight : C → A)

variable (hrev : B.rev = invLetter) (hz : SphereZero B weight)
  (hloop : ∀ x w, Walk B.start x x w → Null B w)

include hloop in
lemma correction_null (e : E × Bool) : Null B (correction B.start e) :=
  hloop _ _ (correction_walk B.start e)

variable {B weight}

lemma HasChain.flatMap {T : Type*} {xs : List T} {f : T → Word E} {a : T → A}
    (hz : SphereZero B weight) (h : ∀ x ∈ xs, HasChain B weight (f x) (a x)) :
    HasChain B weight (xs.flatMap f) (xs.map a).sum := by
  induction xs with
  | nil => exact HasChain.empty
  | cons x xs ih =>
    simpa only [List.flatMap_cons,List.map_cons,List.sum_cons] using
      (h x (by simp)).add hz (ih (fun y hy => h y (by simp [hy])))

variable (B weight)

include hrev hz hloop in
lemma correction_value_reverse (e : E × Bool) :
    value (B := B) (weight := weight) (correction B.start (invLetter e)) =
      -value (B := B) (weight := weight) (correction B.start e) := by
  have hp := value_spec (weight := weight) hrev (correction_null B hloop e)
  have hn := value_spec (weight := weight) hrev (correction_null B hloop (invLetter e))
  apply hn.free_unique hrev hz (hp.mirror hrev)
  exact (correction_reverse (rootWord B.start) e).trans FreeGroup.inv_mk

include hrev hz hloop in
lemma leftInverse_letter (e : E × Bool) :
    leftInverse B weight (letterChain e) = value (B := B) (weight := weight) (correction B.start e) := by
  rcases e with ⟨e,b⟩
  cases b with
  | true => simp [leftInverse,letterChain,edgeValue]
  | false =>
    have hh := correction_value_reverse B weight hrev hz hloop (e,true)
    simpa only [leftInverse,letterChain,Bool.false_eq_true,ite_false,map_neg,
      Finsupp.linearCombination_single,one_smul,edgeValue,invLetter,Bool.not_true] using hh.symm

include hrev hz hloop in
lemma leftInverse_cell (c : C) : leftInverse B weight (cellBoundary B c) = weight c := by
  have hc : Walk B.start (B.start (B.label c ⟨0,B.positive c⟩))
      (B.start (B.label c ⟨0,B.positive c⟩)) (B.attachingWord c) :=
    Walk.ofFn_closed (B.positive c) (B.label c) (by simpa only [hrev] using B.closed c)
  have hsum := HasChain.flatMap (xs := B.attachingWord c) hz
    (fun e _ => value_spec (weight := weight) hrev (correction_null B hloop e))
  have hcell := (HasChain.cell (weight := weight) hrev c).conjugate hz
    (rootWord B.start (B.start (B.label c ⟨0,B.positive c⟩)))
  have he := hsum.free_unique hrev hz hcell (correction_telescope (rootWord B.start) hc)
  simp only [cellBoundary,map_sum,leftInverse_letter B weight hrev hz hloop]
  simpa only [PolygonTarget.Boundary.attachingWord,List.map_ofFn,List.sum_ofFn,Function.comp_def] using he

include hrev hz hloop in
lemma leftInverse_boundary (z : C →₀ ℤ) :
    leftInverse B weight (boundary B z) = Finsupp.linearCombination ℤ weight z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | single c a =>
    simp only [boundary,Finsupp.linearCombination_single,map_smul,
      leftInverse_cell B weight hrev hz hloop]

/-- Exact d₂ injectivity, once closed graph loops have actual disks and every
closed genus-zero diagram has zero full independent-cell chain. -/
theorem boundary_injective (hrev : B.rev = invLetter)
    (hz : SphereZero B (fun c => Finsupp.single c (1 : ℤ)))
    (hloop : ∀ x w, Walk B.start x x w → Null B w) :
    Function.Injective (boundary B) := by
  have hh (z : C →₀ ℤ) := leftInverse_boundary B (fun c => Finsupp.single c (1 : ℤ)) hrev hz hloop z
  have hid : Finsupp.linearCombination ℤ (fun c => Finsupp.single c (1 : ℤ)) = (LinearMap.id : (C →₀ ℤ) →ₗ[ℤ] (C →₀ ℤ)) := by
    ext c a
    simp
  rw [hid] at hh
  exact Function.LeftInverse.injective hh

end IndexedFilling

/-! Subdivision of permutation cycles, with exact orbit-count preservation. -/

/-! Local elementary triangle incidence induces the exact radial contraction. -/
namespace ConeSkeleton

/-! Exact deck coordinates on the old and two radial sides of every triangle. -/

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)

lemma elementaryWalkIndex_frozen_injective
    {s t : ElementaryLiftSide n w d v hv hcell}
    (hs : elementaryTop n w d v hv hcell s = false)
    (h : elementaryWalkIndex n w d v hv hcell s = elementaryWalkIndex n w d v hv hcell t) : s = t := by
  rcases s with ⟨⟨g,c|c⟩,b,i⟩
  · cases hs
  · rcases t with ⟨⟨k,a|a⟩,z,j⟩
    · cases h
    · change (g,Sum.inr (⟨c,b,i⟩ : (frozenBoundary n w d).Side)) =
        (k,Sum.inr (⟨a,z,j⟩ : (frozenBoundary n w d).Side)) at h
      obtain ⟨rfl,h⟩ := Prod.mk.inj h
      have h := Sum.inr.inj h
      cases h
      rfl

variable {A : Type*} [AddCommGroup A]
  (tc : G → Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ g a e, tc g a e.symm = -tc g a e) (fc : G → FrozenCell n w d → A)

lemma elementary_frozen_next (s : ElementaryLiftSide n w d v hv hcell)
    (hs : elementaryTop n w d v hv hcell s = false) :
    elementaryWalkIndex n w d v hv hcell ((elementaryLiftedBoundary n w d v hv hcell).next s) =
      (liftedFrozenTarget n w d v hv hcell tc hc fc).next (elementaryWalkIndex n w d v hv hcell s) := by
  rcases s with ⟨⟨g,c|c⟩,b,i⟩
  · cases hs
  · rfl

end

/-! Every genuine elementary genus-zero picture contracts to the unchanged
macro/frozen target, preserving the literal original-group deck coordinates. -/

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)
variable {A : Type*} [AddCommGroup A] (weight : G × ElementaryCell n w d → A)
  (P : CellPicture (elementaryRawTarget n w d v hv hcell weight))
  (tc : G → Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ g a e, tc g a e.symm = -tc g a e) (fc : G → FrozenCell n w d → A)

lemma elementaryMacro_frozenMapped :
    (elementaryMacroPicture n w d v hv hcell weight P tc hc fc).FrozenMapped
      (liftedFrozenTarget n w d v hv hcell tc hc fc) := by
  let Q := elementaryMacroPicture n w d v hv hcell weight P tc hc fc
  have ht (x : Q.FrozenDart) : elementaryTop n w d v hv hcell (P.index x.val.val) = false := by
    rw [elementaryTop_walk]
    exact x.property
  have hf (x : Q.FrozenDart) : (Q.frozenFace x).val.val = P.pairing.face x.val.val := by
    exact elementaryContract_frozen_next n w d v hv hcell weight P x.val
      (by change ¬ elementaryTop n w d v hv hcell (P.index x.val.val) = true; rw [ht x]; decide)
  constructor
  · intro x
    change elementaryWalkIndex n w d v hv hcell (P.index (Q.frozenFace x).val.val) = _
    rw [hf,P.mapped.commute]
    exact elementary_frozen_next n w d v hv hcell tc hc fc _ (ht x)
  · intro x y hxy he
    apply Subtype.ext
    apply Subtype.ext
    apply P.mapped.injective (semiconj_perm_sameCycle hf hxy)
    exact elementaryWalkIndex_frozen_injective n w d v hv hcell (ht x) he

end

/-! The radial contraction preserves every independent lifted elementary-cell
coefficient, not just an augmentation or a projection to the old edges. -/

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)
variable {A : Type*} [AddCommGroup A]
  (tc : G → Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ g a e, tc g a e.symm = -tc g a e) (fc : G → FrozenCell n w d → A)

lemma elementary_selected_weight (s : ElementaryLiftSide n w d v hv hcell) :
    (if elementarySideRole n w d v hv hcell s = 0 then
      (liftedWalkTarget n w d v hv hcell tc hc fc).weight (elementaryWalkIndex n w d v hv hcell s) else 0) =
    (@ite A (s.2.2 = elementaryMarkPosition n w d s.1.2)
      (instDecidableEqFin _ s.2.2 (elementaryMarkPosition n w d s.1.2))
      ((elementaryLiftedBoundary n w d v hv hcell).weight (elementaryMacroWeight n w d tc fc) s) 0) := by
  rcases s with ⟨⟨g,a|a⟩,b,i⟩
  · change Fin 3 at i
    cases b <;> fin_cases i
    · exact (ite_eq_right (by decide : (1 : Fin 3) ≠ 0)).trans
        (ite_eq_right (by decide : (0 : Fin 3) ≠ 1)).symm
    · exact (ite_eq_left rfl).trans ((hc g a.1 (macroCellDart a.2)).trans (ite_eq_left rfl).symm)
    · exact (ite_eq_right (by decide : (2 : Fin 3) ≠ 0)).trans
        (ite_eq_right (by decide : (2 : Fin 3) ≠ 1)).symm
    · exact (ite_eq_right (by decide : (2 : Fin 3) ≠ 0)).trans
        (ite_eq_right (by decide : (0 : Fin 3) ≠ 1)).symm
    · exact (ite_eq_left rfl).trans (ite_eq_left rfl).symm
    · exact (ite_eq_right (by decide : (1 : Fin 3) ≠ 0)).trans
        (ite_eq_right (by decide : (2 : Fin 3) ≠ 1)).symm
  · change Fin ((frozenBoundary n w d).size a) at i
    have hrole : elementarySideRole n w d v hv hcell (⟨(g,.inr a),b,i⟩) = 0 :=
      elementaryRole_frozen n w d v hv hcell _ rfl
    rw [hrole,ite_eq_left rfl]
    change (if i.val = 0 then (frozenBoundary n w d).weight (fc g) ⟨a,b,i⟩ else 0) = _
    have he : (i.val = 0) = (i = (⟨0,(frozenBoundary n w d).positive a⟩ : Fin _)) :=
      propext ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    exact ite_congr (c := i = (⟨0,(frozenBoundary n w d).positive a⟩ : Fin _))
      he (fun _ => by cases b <;> rfl) (fun _ => rfl)

variable (P : CellPicture (elementaryRawTarget n w d v hv hcell (elementaryMacroWeight n w d tc fc)))

lemma elementaryMacro_chain :
    (elementaryMacroPicture n w d v hv hcell (elementaryMacroWeight n w d tc fc) P tc hc fc).chain = P.chain := by
  let B := elementaryLiftedBoundary n w d v hv hcell
  let weight := elementaryMacroWeight n w d tc fc
  have hh := faceChain_eq_ite P.pairing.face
    ((elementaryRawTarget n w d v hv hcell weight).weight ∘ P.index)
    (fun x => by change B.weight weight (P.index (P.pairing.face x)) = _
                 rw [P.mapped.commute]; rfl)
    (fun x => (P.index x).2.2 = elementaryMarkPosition n w d (P.index x).1.2)
    (P.mapped.selected _ _ _ _ (B.marked_unique (fun a => elementaryMarkPosition n w d a.2)))
  change _ = faceChain _ _ _
  rw [hh]
  change (∑ x : {a : P.Dart // elementarySideRole n w d v hv hcell (P.index a) = 0},
    (liftedWalkTarget n w d v hv hcell tc hc fc).weight
      (elementaryWalkIndex n w d v hv hcell (P.index x.val))) = _
  erw [HyperbolicObstruction.sum_subtype_eq_ite
    (fun a : P.Dart => elementarySideRole n w d v hv hcell (P.index a) = 0)
    (fun a : P.Dart => (liftedWalkTarget n w d v hv hcell tc hc fc).weight
      (elementaryWalkIndex n w d v hv hcell (P.index a)))]
  apply Finset.sum_congr rfl
  intro x _
  simpa only [Function.comp_apply, elementaryRawTarget, PolygonTarget.Boundary.target]
    using elementary_selected_weight n w d v hv hcell tc hc fc (P.index x)

end

/-! Every genus-zero picture over the literal elementary lifted-cell boundary
has zero FULL cellular chain, by exact radial contraction. -/
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable
universe u v z
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type v} [Group G] {A : Type z} [AddCommGroup A]
  (weight : G × ElementaryCell n w d → A)

omit [_root_.Group G] in
lemma elementaryTopWeight_symm (g : G) (a : Top n w) (e : MacroGraph.graph.Dart) :
    elementaryTopWeight n w d weight g a e.symm = - elementaryTopWeight n w d weight g a e := by
  simp only [elementaryTopWeight,macroCell_symm,macroOrientation_symm,neg_zsmul]

omit [_root_.Group G] in
lemma elementaryMacroWeight_eq :
    elementaryMacroWeight n w d (elementaryTopWeight n w d weight)
      (fun g a => weight (g,.inr a)) = weight := by
  funext x
  rcases x with ⟨g,⟨a,e⟩|a⟩
  · simp only [elementaryMacroWeight,elementaryTopWeight,macroCellDart_cell,
      macroCellDart_orientation,one_zsmul]
  · rfl

end ConeSkeleton

/-! Lifting actual word homotopies to the voltage cover, with the negative
orientation based at the positive lift's initial endpoint. -/
namespace VoltageWords

section
open HyperbolicObstruction.WordPictures
variable {A G : Type*} [Group G]

lemma liftWord_append (v : A → G) (g : G) (w z : Word A) :
    liftWord v g (w++z) = liftWord v g w ++ liftWord v (g * total v w) z := by
  induction w generalizing g with
  | nil => simp
  | cons e w ih => simp only [List.cons_append,liftWord_cons,ih,total_cons,mul_assoc]

lemma liftWord_inv (v : A → G) (g : G) (w : Word A) :
    liftWord v (g * total v w) (FreeGroup.invRev w) = FreeGroup.invRev (liftWord v g w) := by
  induction w generalizing g with
  | nil => simp
  | cons e w ih =>
    rw [FreeGroup.invRev_cons,liftWord_append,total_cons,← mul_assoc,ih]
    rw [total_inv]
    conv_rhs => rw [liftWord_cons,FreeGroup.invRev_cons]
    simp only [invRev_singleton,liftWord_cons,liftWord_nil]
    change _ ++ [liftLetter v (((g * voltage v e) * total v w) * (total v w)⁻¹) (invLetter e)] =
      _ ++ [invLetter (liftLetter v g e)]
    rw [mul_inv_cancel_right,liftLetter_inv]

lemma liftWord_step (v : A → G) (g : G) {w z : Word A} (h : FreeGroup.Red.Step w z) :
    FreeGroup.Red.Step (liftWord v g w) (liftWord v g z) := by
  cases h with
  | @not l r a b =>
    simp only [liftWord_append,liftWord_cons]
    have he : (a,!b) = invLetter (a,b) := rfl
    rw [he,voltage_inv,liftLetter_inv,mul_inv_cancel_right]
    exact FreeGroup.Red.Step.not

lemma move_lift (v : A → G) {R : Set (Word A)}
    (hR : ∀ w ∈ R, total v w = 1) {w z : Word A} {n : ℕ} (h : Move R w z n) (g : G) :
    Move (Relators v R) (liftWord v g w) (liftWord v g z) n := by
  cases h with
  | free h => exact Move.free (liftWord_step v g h)
  | face l r w hw =>
    simp only [liftWord_append,total_append,hR w hw,mul_one]
    exact Move.face _ _ _ ⟨g * total v l,w,hw,rfl⟩
  | reverseFace l r w hw =>
    have hi : liftWord v (g * total v l) (FreeGroup.invRev w) =
        FreeGroup.invRev (liftWord v (g * total v l) w) := by
      simpa only [hR w hw,mul_one] using liftWord_inv v (g * total v l) w
    simp only [liftWord_append,total_append,total_inv,hR w hw,inv_one,mul_one,hi]
    exact Move.reverseFace _ _ _ ⟨g * total v l,w,hw,rfl⟩

/-- An actual area-preserving homotopy lift. Closed relators, free cancellation
and both orientations are derived, not assumed as a cover's simple connectivity. -/
theorem homotopy_lift (v : A → G) {R : Set (Word A)}
    (hR : ∀ w ∈ R, total v w = 1) {w z : Word A} {n : ℕ} (h : Homotopy R w z n) (g : G) :
    Homotopy (Relators v R) (liftWord v g w) (liftWord v g z) n := by
  induction h with
  | refl => exact WordPictures.Homotopy.refl _
  | move h => exact WordPictures.Homotopy.move (move_lift v hR h g)
  | symm h ih => exact WordPictures.Homotopy.symm ih
  | trans h h' ih ih' => exact WordPictures.Homotopy.trans ih ih'

end

open HyperbolicObstruction.WordPictures HyperbolicObstruction.PictureSwitch
variable {A G V C : Type*} [Group G]

lemma liftWord_ofFn (v : A → G) (g : G) (w : Word A) :
    liftWord v g w = List.ofFn (fun i : Fin w.length =>
      liftLetter v (g * total v (w.take i.val)) w[i.val]) := by
  induction w generalizing g with
  | nil => rfl
  | cons e w ih =>
    rw [liftWord_cons,ih,List.ofFn_succ]
    congr 1
    · simp only [Fin.val_zero,List.take_zero,total_nil,mul_one,List.getElem_cons_zero]
    · apply congrArg List.ofFn
      funext i
      simp only [Fin.val_succ,List.take_succ_cons,total_cons,List.getElem_cons_succ,mul_assoc]

lemma liftWord_ofFn' (v : A → G) (g : G) {m : ℕ} (w : Fin m → A × Bool) :
    liftWord v g (List.ofFn w) = List.ofFn (fun i : Fin m =>
      liftLetter v (g * ((List.ofFn (voltage v ∘ w)).take i.val).prod) (w i)) := by
  rw [liftWord_ofFn]
  apply List.ext_getElem
  · simp only [List.length_ofFn]
  · intro i hi₁ hi₂
    simp only [List.getElem_ofFn,total,List.map_take,List.map_ofFn]

variable (B : PolygonTarget.Boundary C (A × Bool) V) (v : A → G)
  (hinv : B.rev = invLetter)
  (hc : ∀ c, total v (B.attachingWord c) = 1)

lemma lifted_attachingWord (c : G × C) :
    (liftedBoundary B v hinv hc).attachingWord c = liftWord v c.1 (B.attachingWord c.2) := by
  simp only [PolygonTarget.Boundary.attachingWord]
  rw [liftWord_ofFn']
  rfl

lemma lifted_relators : Set.range (liftedBoundary B v hinv hc).attachingWord =
    Relators v (Set.range B.attachingWord) := by
  ext z
  constructor
  · rintro ⟨c,rfl⟩
    exact ⟨c.1,B.attachingWord c.2,⟨c.2,rfl⟩,lifted_attachingWord B v hinv hc c⟩
  · rintro ⟨g,w,⟨c,rfl⟩,rfl⟩
    exact ⟨(g,c),lifted_attachingWord B v hinv hc (g,c)⟩

/-- A null word in the base polygon bouquet, lifted from any deck coordinate,
is a null word in the actual independently indexed cover presentation. -/
theorem lifted_nullWord (g : G) (w : Word A)
    (hw : PresentedGroup.mk (FreeGroup.mk '' Set.range B.attachingWord) (FreeGroup.mk w) = 1) :
    PresentedGroup.mk (FreeGroup.mk '' Set.range (liftedBoundary B v hinv hc).attachingWord)
      (FreeGroup.mk (liftWord v g w)) = 1 := by
  obtain ⟨k,hk⟩ := WordPictures.existence w hw
  have hl := homotopy_lift v (by rintro w ⟨c,rfl⟩; exact hc c) hk g
  rw [← lifted_relators B v hinv hc] at hl
  exact WordPictures.sound hl

end VoltageWords

/-!
The actual elementary triangles imply the compressed cone polygon equations.
Unlike the redundant polygon bouquet, this presentation retains exactly the
elementary indexed top triangles.
-/

section

lemma prod_gauge_telescope {H : Type*} [Group H] (u x : ℕ → H) (k : ℕ) :
    (List.ofFn (fun i : Fin k => u i.val * x i.val * (u (i.val+1))⁻¹)).prod =
      u 0 * (List.ofFn (fun i : Fin k => x i.val)).prod * (u k)⁻¹ := by
  induction k generalizing u x with
  | zero => simp only [List.ofFn_zero,List.prod_nil,mul_one,mul_inv_cancel]
  | succ k ih =>
    simp only [List.ofFn_succ,List.prod_cons,Fin.val_zero,Fin.val_succ]
    rw [ih (fun i => u (i+1)) (fun i => x (i+1))]
    group

/-- Ordered, noncommutative telescope around a cyclic boundary. -/
lemma prod_gauge_cycle {H : Type*} [Group H] {k : ℕ} (hk : 0 < k)
    (u x : Fin k → H) :
    (List.ofFn (fun i => u i * x i * (u (finRotate k i))⁻¹)).prod =
      u ⟨0,hk⟩ * (List.ofFn x).prod * (u ⟨0,hk⟩)⁻¹ := by
  let u' : ℕ → H := fun j => u ⟨j % k,Nat.mod_lt _ hk⟩
  let x' : ℕ → H := fun j => x ⟨j % k,Nat.mod_lt _ hk⟩
  have hzero : u' 0 = u ⟨0,hk⟩ := by simp only [u',Nat.zero_mod]
  have hlast : u' k = u ⟨0,hk⟩ := by simp only [u',Nat.mod_self]
  have hx (i : Fin k) : x' i.val = x i := by simp only [x',Nat.mod_eq_of_lt i.isLt]
  have hu (i : Fin k) : u' i.val = u i := by simp only [u',Nat.mod_eq_of_lt i.isLt]
  have hn (i : Fin k) : u' (i.val+1) = u (finRotate k i) := by
    apply congrArg u
    apply Fin.ext
    cases k with
    | zero => omega
    | succ k =>
      rw [finRotate_apply,Fin.val_add_one]
      split_ifs with hi
      · subst i; simp only [Fin.val_last,Nat.mod_self]
      · exact Nat.mod_eq_of_lt (by have := i.isLt; have hv : i.val ≠ k := fun h => hi (Fin.ext h); omega)
  have hh := prod_gauge_telescope u' x' k
  simpa only [hu,hx,hn,hzero,hlast] using hh

namespace ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- Every closed elementary boundary with trivial original-group voltage is
null in the elementary-cell edge-bouquet. Open paths are deliberately excluded:
the extra fan/top apex gauges do not vanish on open paths. -/
theorem elementary_closed_null {ell : ℕ} (hell : 0 < ell) (word : Fin ell → ElementaryDart n w)
    (closed : ∀ i, elementaryStart n w (word (finRotate ell i)) =
      elementaryStart n w (elementaryRev n w (word i)))
    (hvol : (List.ofFn (fun i => elementaryVoltage n w (letterVoltage n w d) (word i))).prod = 1) :
    PresentedGroup.mk (FreeGroup.mk '' Set.range (elementaryBoundary n w d).attachingWord)
      (FreeGroup.mk (List.ofFn word)) = 1 := by
  rw [elementaryPolygonValue_word,List.map_ofFn]
  have he : (fun i => elementaryPolygonValue n w d (word i)) =
      (fun i => elementaryGauge n w d (elementaryStart n w (word i)) *
        elementaryComparison n w d (elementaryVoltage n w (letterVoltage n w d) (word i)) *
          (elementaryGauge n w d (elementaryStart n w (word (finRotate ell i))))⁻¹) := by
    funext i
    rw [closed,elementary_gauge]
  simp only [Function.comp_def]
  rw [he,prod_gauge_cycle hell]
  have hv := congrArg (elementaryComparison n w d) hvol
  rw [map_list_prod,List.map_ofFn,map_one] at hv
  simp only [Function.comp_def] at hv
  rw [hv,mul_one,mul_inv_cancel]

end ConeSkeleton
end

namespace VoltageWords
open HyperbolicObstruction.WordPictures HyperbolicObstruction.PictureSwitch
variable {A G V C : Type*} [Group G]

lemma decode_inverse (v : A → G) (e : (G × A) × Bool) :
    (encode v).symm (invLetter e) =
      (((encode v).symm e).1 * voltage v ((encode v).symm e).2,
        invLetter ((encode v).symm e).2) := by
  apply (encode v).injective
  rw [Equiv.apply_symm_apply,encode_reverse,Equiv.apply_symm_apply]

/-- The deck coordinate at every corner is forced by the literal prefix. -/
lemma cycle_deck_prefix (v : A → G) {m : ℕ} (hm : 0 < m)
    (w : Fin m → A × Bool) (g : Fin m → G)
    (hg : ∀ i, g (finRotate m i) = g i * voltage v (w i)) (i : Fin m) :
    g i = g ⟨0,hm⟩ * ((List.ofFn (voltage v ∘ w)).take i.val).prod := by
  cases m with
  | zero => omega
  | succ m =>
    induction i using Fin.inductionOn with
    | zero => simp only [Fin.val_zero,List.take_zero,List.prod_nil,mul_one]; rfl
    | @succ i ih =>
      have he : finRotate (m+1) i.castSucc = i.succ := by
        rw [finRotate_apply]
        apply Fin.ext
        rw [Fin.val_add_one,ite_eq_right]
        · rfl
        · intro h
          have hh := congrArg Fin.val h
          simp only [Fin.val_castSucc,Fin.val_last] at hh
          omega
      rw [← he,hg,ih]
      have hp := List.prod_take_succ (List.ofFn (voltage v ∘ w)) i.val
        (by simp only [List.length_ofFn]; omega)
      rw [List.getElem_ofFn] at hp
      change _ = _ * ((List.ofFn (voltage v ∘ w)).take ((finRotate (m+1) i.castSucc).val)).prod
      rw [he]
      simp only [Fin.val_succ]
      rw [hp,mul_assoc]
      rfl
lemma cycle_voltage (v : A → G) {m : ℕ} (hm : 0 < m)
    (w : Fin m → A × Bool) (g : Fin m → G)
    (hg : ∀ i, g (finRotate m i) = g i * voltage v (w i)) :
    total v (List.ofFn w) = 1 := by
  have he (i : Fin m) : voltage v (w i) =
      (g i)⁻¹ * (1 : G) * ((g (finRotate m i))⁻¹)⁻¹ := by rw [hg]; group
  simp only [total,List.map_ofFn,Function.comp_def]
  simp_rw [he]
  rw [HyperbolicObstruction.prod_gauge_cycle hm]
  simp

variable (B : PolygonTarget.Boundary C (A × Bool) V) (v : A → G)
  (hinv : B.rev = invLetter)
variable {m : ℕ} (hm : 0 < m) (w : Fin m → (G × A) × Bool)
  (closed : ∀ i, liftedStart B v (w (finRotate m i)) = liftedStart B v (invLetter (w i)))

include closed

lemma closed_decks (i : Fin m) :
    ((encode v).symm (w (finRotate m i))).1 =
      ((encode v).symm (w i)).1 * voltage v ((encode v).symm (w i)).2 := by
  have hh := congrArg Prod.fst (closed i)
  simpa only [liftedStart,decode_inverse] using hh

include hinv in
lemma projected_closed (i : Fin m) :
    B.start ((encode v).symm (w (finRotate m i))).2 =
      B.start (B.rev ((encode v).symm (w i)).2) := by
  have hh := congrArg Prod.snd (closed i)
  simpa only [liftedStart,decode_inverse,hinv] using hh

lemma closed_is_lift :
    List.ofFn w = liftWord v (((encode v).symm (w ⟨0,hm⟩)).1)
      (List.ofFn (fun i => ((encode v).symm (w i)).2)) := by
  rw [liftWord_ofFn']
  apply congrArg List.ofFn
  funext i
  rw [← cycle_deck_prefix v hm (fun j => ((encode v).symm (w j)).2)
      (fun j => ((encode v).symm (w j)).1) (closed_decks B v w closed) i]
  exact (encode v).apply_symm_apply (w i) |>.symm

include hm in
lemma projected_voltage :
    total v (List.ofFn (fun i => ((encode v).symm (w i)).2)) = 1 :=
  cycle_voltage v hm _ (fun j => ((encode v).symm (w j)).1) (closed_decks B v w closed)

end VoltageWords

/-! Actual genus-zero disks for every closed elementary loop in the original
letter voltage cover. No cycle-representation or asphericity hypothesis. -/

namespace ConeSkeleton

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch WordPictures
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

variable {ell : ℕ} (hell : 0 < ell)
  (word : Fin ell → (LetterPresentation.Group n w d × ElementaryEdge n w) × Bool)
  (closed : ∀ i, (elementaryEncodedBoundary n w d).start (word (finRotate ell i)) =
    (elementaryEncodedBoundary n w d).start (invLetter (word i)))

include hell closed

/-- Every closed loop in this incidence cover is a null word in its exact lifted
polygon presentation. This is not a topological universal-cover assertion. -/
theorem elementary_encoded_null :
    PresentedGroup.mk (FreeGroup.mk '' Set.range (elementaryEncodedBoundary n w d).attachingWord)
      (FreeGroup.mk (List.ofFn word)) = 1 := by
  let v := elementaryPositiveVoltage n w d
  let B := elementaryBoundary n w d
  let base : Fin ell → ElementaryDart n w := fun i => ((VoltageWords.encode v).symm (word i)).2
  have hclosed : ∀ i, B.start (base (finRotate ell i)) = B.start (B.rev (base i)) :=
    VoltageWords.projected_closed B v rfl word closed
  have hvol : (List.ofFn (fun i => elementaryVoltage n w (letterVoltage n w d) (base i))).prod = 1 := by
    simp only [elementaryVoltage_signed]
    simpa only [VoltageWords.total,List.map_ofFn,Function.comp_def] using
      VoltageWords.projected_voltage B v hell word closed
  have hbase := elementary_closed_null n w d hell base hclosed hvol
  rw [VoltageWords.closed_is_lift B v hell word closed]
  exact VoltageWords.lifted_nullWord B v rfl (elementaryTotal_cell n w d) _ _ hbase

end

/-! Signed-edge encoding preserves all individual cell identities and the
closed-picture chain. Sphere vanishing therefore applies to indexed disks. -/

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch WordPictures SignedWalks
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- Every componentwise closed walk, including the empty walk, has an actual
literal nullword certificate. No graph-connectedness hypothesis is needed. -/
theorem elementary_encoded_walk_null (x) (u)
    (h : Walk (elementaryEncodedBoundary n w d).start x x u) :
    IndexedFilling.Null (elementaryEncodedBoundary n w d) u := by
  by_cases hu : u = []
  · subst u
    change PresentedGroup.mk _ (1 : FreeGroup _) = 1
    exact map_one _
  have hpos : 0 < u.length := List.length_pos_iff.mpr hu
  have hc : ∀ i : Fin u.length,
      (elementaryEncodedBoundary n w d).start u[(finRotate u.length i).val] =
        (elementaryEncodedBoundary n w d).start (invLetter u[i.val]) :=
    h.closed_rotate hpos
  have hh := elementary_encoded_null n w d hpos (fun i : Fin u.length => u[i.val]) hc
  simpa only [IndexedFilling.Null,List.ofFn_getElem] using hh

end

/-! Actual integral boundaries for the uncompressed cone cells. -/
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch IntegralIncidence

end ConeSkeleton

section

/-! Full independent lifted-cell d₂ injectivity. Rooted nullword disks, glued
with their exact cell identities, now resolve the algebraic cycle frontier. -/

namespace VoltageWords
open HyperbolicObstruction.IndexedFilling
variable {E G : Type*} [Group G]
lemma letterChain_encode (v : E → G) (e : G × (E × Bool)) :
    letterChain (encode v e) = IntegralIncidence.edgeChain (voltage v) e := by
  rcases e with ⟨g,e,b⟩
  cases b <;> rfl
end VoltageWords

namespace ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch WordPictures
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma elementaryEncoded_cellBoundary
    (c : LetterPresentation.Group n w d × ElementaryCell n w d) :
    IndexedFilling.cellBoundary (elementaryEncodedBoundary n w d) c =
      (elementaryPolygons n w d).faceBoundary (elementaryVoltage n w (letterVoltage n w d)) c := by
  unfold IndexedFilling.cellBoundary IntegralIncidence.Polygons.faceBoundary
  apply Finset.sum_congr rfl
  intro i _
  change Fin (elementarySize n w d c.2) at i
  rw [elementaryEncoded_label,VoltageWords.letterChain_encode]
  have he : VoltageWords.voltage (elementaryPositiveVoltage n w d) =
      elementaryVoltage n w (letterVoltage n w d) := funext (fun e => (elementaryVoltage_signed n w d e).symm)
  rw [he]
  rfl

lemma elementaryEncoded_boundary :
    IndexedFilling.boundary (elementaryEncodedBoundary n w d) = letterBoundary₂ n w d := by
  unfold IndexedFilling.boundary letterBoundary₂ IntegralIncidence.Polygons.d₂
  exact congrArg (Finsupp.linearCombination ℤ) (funext (elementaryEncoded_cellBoundary n w d))

end ConeSkeleton
end

/-! No reselection: the same final arrays already have the precise uniform
lifted-picture estimate. Apply the new disk-chain left inverse to those arrays. -/

namespace IncidenceTemplate

section
open CoreGeometry LetterPresentation ConeSkeleton PictureSwitch WordPictures
attribute [local instance] Classical.propDecidable

lemma finalDiagramStage_elementary_sphere_zero (m : ℕ)
    (G A : Type) [Group G] [AddCommGroup A]
    (v : Dart (finalSize m) (finalMaster m) → G)
    (hv : ∀ e, v (rev (finalSize m) (finalMaster m) e) = (v e)⁻¹)
    (hc : ∀ a : Cell (finalSize m) (finalMaster m) (finalSix m),
      (List.ofFn (fun i => v (side (finalSize m) (finalMaster m) (finalSix m) a i))).prod = 1)
    (weight : G × ElementaryCell (finalSize m) (finalMaster m) (finalSix m) → A)
    : ∀ P : CellPicture.{0} (elementaryRawTarget (finalSize m) (finalMaster m) (finalSix m)
      v hv hc weight), P.chain = 0 := by
  have he := elementaryMacroWeight_eq (finalSize m) (finalMaster m) (finalSix m) weight
  rw [←he]
  intro P
  rw [←elementaryMacro_chain (finalSize m) (finalMaster m) (finalSix m) v hv hc
    (elementaryTopWeight (finalSize m) (finalMaster m) (finalSix m) weight)
    (elementaryTopWeight_symm (finalSize m) (finalMaster m) (finalSix m) weight)
    (fun g a => weight (g,.inr a)) P]
  exact finalDiagramStage_lifted_chain_zero m G A v hv hc _ _ _ _
    (elementaryMacro_frozenMapped (finalSize m) (finalMaster m) (finalSix m) v hv hc _ P _ _ _)

lemma finalDiagramStage_indexed_sphere_zero (m : ℕ) :
    IndexedFilling.SphereZero (elementaryEncodedBoundary (finalSize m) (finalMaster m) (finalSix m))
      (fun c => Finsupp.single c (1 : ℤ)) := by
  intro P I
  have hz := finalDiagramStage_elementary_sphere_zero m
    (LetterPresentation.Group (finalSize m) (finalMaster m) (finalSix m))
    ((LetterPresentation.Group (finalSize m) (finalMaster m) (finalSix m) ×
      ElementaryCell (finalSize m) (finalMaster m) (finalSix m)) →₀ ℤ)
    (letterVoltage (finalSize m) (finalMaster m) (finalSix m))
    (letterVoltage_rev (finalSize m) (finalMaster m) (finalSix m))
    (letterVoltage_cell (finalSize m) (finalMaster m) (finalSix m))
    (fun c => Finsupp.single c 1)
    (elementaryDecodePicture (finalSize m) (finalMaster m) (finalSix m) (fun c => Finsupp.single c 1)
      (I.closedPicture rfl (fun c => Finsupp.single c 1)))
  exact (WordPicture.Indexing.closed_chain I rfl _).symm.trans hz

/-- Injectivity of the full d₂ for the selected arrays. -/
theorem finalDiagramStage_boundary_injective (m : ℕ) :
    Function.Injective (letterBoundary₂ (finalSize m) (finalMaster m) (finalSix m)) := by
  rw [←elementaryEncoded_boundary]
  exact IndexedFilling.boundary_injective _ rfl (finalDiagramStage_indexed_sphere_zero m)
    (elementary_encoded_walk_null (finalSize m) (finalMaster m) (finalSix m))

end

/-! Arbitrary-valued cell cochains of the same chosen arrays extend to edges.
This is the full polygonal obstruction extension, not only a basis-vector
injectivity statement. -/

open CoreGeometry LetterPresentation ConeSkeleton PictureSwitch WordPictures
attribute [local instance] Classical.propDecidable

lemma finalDiagramStage_indexed_sphere_zero_weight (m : ℕ) (A : Type) [AddCommGroup A]
    (weight : LetterPresentation.Group (finalSize m) (finalMaster m) (finalSix m) ×
      ElementaryCell (finalSize m) (finalMaster m) (finalSix m) → A) :
    IndexedFilling.SphereZero
      (elementaryEncodedBoundary (finalSize m) (finalMaster m) (finalSix m)) weight := by
  intro P I
  have hz := finalDiagramStage_elementary_sphere_zero m
    (LetterPresentation.Group (finalSize m) (finalMaster m) (finalSix m)) A
    (letterVoltage (finalSize m) (finalMaster m) (finalSix m))
    (letterVoltage_rev (finalSize m) (finalMaster m) (finalSix m))
    (letterVoltage_cell (finalSize m) (finalMaster m) (finalSix m)) weight
    (elementaryDecodePicture (finalSize m) (finalMaster m) (finalSix m) weight
      (I.closedPicture rfl weight))
  exact (WordPicture.Indexing.closed_chain I rfl _).symm.trans hz

/-- The literal lifted-edge cochain whose coboundary is any prescribed
independent lifted-cell cochain. No sphere-map producer is assumed. -/
theorem finalDiagramStage_extend_cochain (m : ℕ) (A : Type) [AddCommGroup A]
    (weight : LetterPresentation.Group (finalSize m) (finalMaster m) (finalSix m) ×
      ElementaryCell (finalSize m) (finalMaster m) (finalSix m) → A) :
    ∀ c, IndexedFilling.leftInverse
      (elementaryEncodedBoundary (finalSize m) (finalMaster m) (finalSix m)) weight
      (IndexedFilling.cellBoundary
        (elementaryEncodedBoundary (finalSize m) (finalMaster m) (finalSix m)) c) = weight c :=
  IndexedFilling.leftInverse_cell _ weight rfl
    (finalDiagramStage_indexed_sphere_zero_weight m A weight)
    (elementary_encoded_walk_null (finalSize m) (finalMaster m) (finalSix m))

end IncidenceTemplate

/-! The actual elementary incidence data now defines an actual finite
barycentric polyhedron. This file proves compactness and connectivity only;
no CW-universal-cover comparison is smuggled in as a structure field. -/

namespace ConeSkeleton
open CoreGeometry IncidenceTemplate LetterPresentation FinitePolyhedron
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
attribute [local instance] Classical.propDecidable

attribute [local instance] OAI.HyperbolicObstruction.ConeSkeleton.instDecidableEqElementaryVertex
attribute [local instance] OAI.HyperbolicObstruction.ConeSkeleton.instDecidableEqElementaryEdge
attribute [local instance] OAI.HyperbolicObstruction.ConeSkeleton.instDecidableEqElementaryCell
lemma elementary_old_connected (v : ElementaryVertex n w) :
    Joined (elementaryBasepoint n w d)
      (vertex (elementarySimplicialComplex n w d) ((elementaryPolygonData n w d).old v)) := by
  change @Joined (Carrier ((elementaryPolygonData n w d).complex)) _ _ _
  rcases v with (u|f)|a
  · cases u
    exact Joined.refl _
  · simpa only [elementaryBasepoint, elementaryBaseVertex, elementaryPolygonData,
      elementarySimplicialComplex, elementaryStart, start, macroVertex] using
      ((elementaryPolygonData n w d).endpoints_joined (.inl (.inr ⟨f,fanBase f.val.1⟩))).symm
  · simpa only [elementaryBasepoint, elementaryBaseVertex, elementaryPolygonData,
      elementarySimplicialComplex, elementaryStart, start, macroVertex] using
      ((elementaryPolygonData n w d).endpoints_joined (.inr (a,.inr ()))).symm

instance elementaryPolyhedron_pathConnected : PathConnectedSpace (elementaryPolyhedron n w d) :=
  (elementaryPolygonData n w d).pathConnected_of_graph (.inl (.inl ())) (elementary_old_connected n w d)

instance elementaryFinite_pathConnected :
    PathConnectedSpace (elementaryFiniteComplex n w d).Carrier := by
  refine ⟨⟨elementaryFiniteBasepoint n w d⟩, fun x y => ?_⟩
  simpa only [Homeomorph.apply_symm_apply] using (PathConnectedSpace.joined ((elementaryFiniteHomeomorph n w d).symm x)
    ((elementaryFiniteHomeomorph n w d).symm y)).map (elementaryFiniteHomeomorph n w d).continuous

end ConeSkeleton

/-! Restricting any flat voltage on the actual triangulation to the original
indexed graph. Literal cap triangles prove every original boundary relation. -/

/-! Genuine continuous fundamental groups are generated by the finite edges. -/

/-! New subdivision, collar and cone edges do not create fundamental-group
generators. This concerns the actual barycentric realization. -/

section

/-! Literal monodromy detects rooted edge words. -/

open scoped Topology
open Set
namespace FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

lemma detect_based_chain (o : V) (R : ∀ a, FinitePolyhedron.EdgeChain K o a)
    (hR : ∀ a, EdgeChain.eval v (R a) = 1) {a b : V} (p : FinitePolyhedron.EdgeChain K a b) :
    v.detect o (RootedPaths.based o (fun a => (R a).pathClass) p.pathClass) = EdgeChain.eval v p := by
  have hmono (a : V) (g : G) : v.isCoveringMap.monodromy (R a).pathClass (v.vertexFiber o g) =
      v.vertexFiber a g := by rw [EdgeChain.monodromy,hR,mul_one]
  have hsymm (a : V) (g : G) : v.isCoveringMap.monodromy (R a).pathClass.symm (v.vertexFiber a g) =
      v.vertexFiber o g := by rw [←hmono a g,v.monodromy_symm]
  apply (v.detect_eq_iff o _ _).mpr
  change _ = (v.isCoveringMap.monodromy ((R a).pathClass.trans (p.pathClass.trans (R b).pathClass.symm)) _).val
  rw [v.isCoveringMap.monodromy_trans_apply,hmono,v.isCoveringMap.monodromy_trans_apply,
    EdgeChain.monodromy,one_mul,hsymm]
  exact v.smul_vertexFiber o _

lemma detect_edgeLoop (o : V) (R : ∀ a, FinitePolyhedron.EdgeChain K o a)
    (hR : ∀ a, EdgeChain.eval v (R a) = 1) {a b : V} (h : {a,b} ∈ K.faces) :
    v.detect o (RootedPaths.edgeLoop o (fun a => (R a).pathClass) a b) = v.value a b := by
  have hh := v.detect_based_chain o R hR (.cons h (.nil b))
  simpa only [FinitePolyhedron.EdgeChain.pathClass_cons,FinitePolyhedron.EdgeChain.pathClass_nil,
    Path.Homotopic.Quotient.trans_refl,EdgeChain.eval_cons,EdgeChain.eval_nil,mul_one,
    RootedPaths.edgeLoop_of_edge o (fun a => (R a).pathClass) h] using hh

end FinitePolyhedron.Voltage
end

/-! The literal polygon presentation maps to the actual pi1, and its tree
normalization has no hidden van Kampen hypothesis. -/

/-! Identification of the actual finite elementary polyhedron's pi1 with the
original letter presentation, using actual path classes and voltage covers. -/

section

/-! The arbitrary obstruction cochain on the literal collar triangles of the
SAME chosen arrays extends to their literal directed lifted edges. -/

namespace FinitePolygonModel.Data
lemma map_edgeChain {E G B : Type*} [Group G] [AddCommGroup B]
    (v : E → G) (F : ((G × E) →₀ ℤ) →ₗ[ℤ] B) (g : G) (e : E × Bool) :
    F (IntegralIncidence.edgeChain (signed v) (g,e)) =
      signedCochain v (fun x => F (Finsupp.single x 1)) g e := by
  rcases e with ⟨e,b⟩
  cases b <;> simp [IntegralIncidence.edgeChain,signed,signedCochain]
end FinitePolygonModel.Data
namespace IncidenceTemplate
open CoreGeometry LetterPresentation ConeSkeleton FinitePolygonModel
attribute [local instance] Classical.propDecidable
variable (m : ℕ) (B : Type) [AddCommGroup B]
variable (T : (LetterPresentation.Group (finalSize m) (finalMaster m) (finalSix m)) → Data.Position (elementaryPolygonData (finalSize m) (finalMaster m) (finalSix m)) → Fin 3 → B)

lemma finalTriangleEdgeWeight_equation (g : (LetterPresentation.Group (finalSize m) (finalMaster m) (finalSix m))) (c : ElementaryCell (finalSize m) (finalMaster m) (finalSix m)) :
    (∑ i : Fin ((elementaryPolygonData (finalSize m) (finalMaster m) (finalSix m)).size c), Data.signedCochain (fun e => elementaryVoltage (finalSize m) (finalMaster m) (letterVoltage (finalSize m) (finalMaster m) (finalSix m)) (e,true)) (finalTriangleEdgeWeight m B T)
      (g * ((List.ofFn (fun i => Data.signed (fun e => elementaryVoltage (finalSize m) (finalMaster m) (letterVoltage (finalSize m) (finalMaster m) (finalSix m)) (e,true)) ((elementaryPolygonData (finalSize m) (finalMaster m) (finalSix m)).side c i))).take i.val).prod) ((elementaryPolygonData (finalSize m) (finalMaster m) (finalSix m)).side c i)) =
    ∑ i : Fin ((elementaryPolygonData (finalSize m) (finalMaster m) (finalSix m)).size c), ∑ j : Fin 3,
      (elementaryPolygonData (finalSize m) (finalMaster m) (finalSix m)).triangleWeight T (g * (elementaryPolygonData (finalSize m) (finalMaster m) (finalSix m)).cornerOffset (fun e => elementaryVoltage (finalSize m) (finalMaster m) (letterVoltage (finalSize m) (finalMaster m) (finalSix m)) (e,true)) ⟨c,(i,j)⟩) ⟨c,(i,j)⟩ := by
  have hh := finalDiagramStage_extend_cochain m B (finalTrianglePolygonWeight m B T) (g,c)
  rw [elementaryEncoded_cellBoundary] at hh
  have hv : elementaryVoltage (finalSize m) (finalMaster m)
      (letterVoltage (finalSize m) (finalMaster m) (finalSix m)) = Data.signed
      (fun e => elementaryVoltage (finalSize m) (finalMaster m)
        (letterVoltage (finalSize m) (finalMaster m) (finalSix m)) (e,true)) := by
    funext e; exact (elementarySignedVoltage _ _ _ e).symm
  rw [hv] at hh
  simp only [IntegralIncidence.Polygons.faceBoundary,map_sum,
    IntegralIncidence.Polygons.liftedSide,IntegralIncidence.Polygons.offset,Data.map_edgeChain] at hh
  exact hh

end IncidenceTemplate
end

section

/-! The converse monodromy criterion, for an actual covering map. This does
not assume a universal cover: it proves path connectivity and simple
connectivity from bijectivity of the monodromy action on one fiber. -/

open Set Function

lemma simplyConnected_of_fundamentalGroup_subsingleton {E : Type*} [TopologicalSpace E]
    [PathConnectedSpace E] (e₀ : E) [Subsingleton (FundamentalGroup E e₀)] :
    SimplyConnectedSpace E := by
  apply simply_connected_iff_paths_homotopic.mpr
  refine ⟨inferInstance,fun x y => ⟨fun p q => ?_⟩⟩
  let a : Path.Homotopic.Quotient e₀ x := .mk (PathConnectedSpace.somePath e₀ x)
  let b : Path.Homotopic.Quotient e₀ y := .mk (PathConnectedSpace.somePath e₀ y)
  have he : a.trans (p.trans b.symm) = a.trans (q.trans b.symm) :=
    Subsingleton.elim (α := FundamentalGroup E e₀) _ _
  have := congrArg (fun r : Path.Homotopic.Quotient e₀ e₀ => a.symm.trans (r.trans b)) he
  simp only [Path.Homotopic.Quotient.trans_assoc
    ] at this
  simpa only [← Path.Homotopic.Quotient.trans_assoc,Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans,Path.Homotopic.Quotient.trans_refl] using this

namespace Covering
variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}
  (cov : IsCoveringMap p) (e₀ : E)

lemma pathConnected_of_monodromy_surjective [PathConnectedSpace X]
    (hs : Surjective (fun γ : FundamentalGroup X (p e₀) => cov.monodromy γ ⟨e₀,rfl⟩)) :
    PathConnectedSpace E := by
  have joined₀ (e : E) : Joined e₀ e := by
    let γ : Path.Homotopic.Quotient (p e₀) (p e) :=
      .mk (PathConnectedSpace.somePath _ _)
    obtain ⟨a,ha⟩ := (cov.monodromy_bijective γ).2 ⟨e,rfl⟩
    obtain ⟨r,hr⟩ := hs a
    let r' : Path.Homotopic.Quotient e₀ a.val :=
      (cov.liftPathQuotient r ⟨e₀,rfl⟩).cast rfl (congrArg Subtype.val hr).symm
    let γ' : Path.Homotopic.Quotient a.val e :=
      (cov.liftPathQuotient γ a).cast rfl (congrArg Subtype.val ha).symm
    exact ⟨(r'.trans γ').out⟩
  exact ⟨⟨e₀⟩,fun e f => (joined₀ e).symm.trans (joined₀ f)⟩

lemma fundamentalGroup_subsingleton_of_monodromy_injective
    (hi : Injective (fun γ : FundamentalGroup X (p e₀) => cov.monodromy γ ⟨e₀,rfl⟩)) :
    Subsingleton (FundamentalGroup E e₀) := by
  refine ⟨fun r s => cov.injective_path_homotopic_map e₀ e₀ (hi ?_)⟩
  change cov.monodromy (Path.Homotopic.Quotient.map r ⟨p,cov.continuous⟩) ⟨e₀,rfl⟩ =
    cov.monodromy (Path.Homotopic.Quotient.map s ⟨p,cov.continuous⟩) ⟨e₀,rfl⟩
  exact (cov.monodromy_map r).trans (cov.monodromy_map s).symm

lemma simplyConnected_of_monodromy_bijective [PathConnectedSpace X]
    (h : Bijective (fun γ : FundamentalGroup X (p e₀) => cov.monodromy γ ⟨e₀,rfl⟩)) :
    SimplyConnectedSpace E := by
  let := pathConnected_of_monodromy_surjective cov e₀ h.2
  let := fundamentalGroup_subsingleton_of_monodromy_injective cov e₀ h.1
  exact simplyConnected_of_fundamentalGroup_subsingleton e₀

end Covering
end

/-! The actual voltage cover is universal whenever its proved monodromy
comparison is bijective. No simple-connectivity premise on the total space
is substituted for the producer. -/

namespace FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

lemma monodromy_bijective_of_detect (o : V) (h : Function.Bijective (v.detect o)) :
    Function.Bijective (fun γ : FundamentalGroup (Carrier K) (vertex K o) =>
      v.isCoveringMap.monodromy γ (v.vertexFiber o 1)) := by
  constructor
  · intro r s hrs
    apply MulOpposite.op_injective
    apply h.1
    apply (v.detect_eq_iff o (MulOpposite.op r) (v.detect o (MulOpposite.op s))).mpr
    exact ((v.detect_eq_iff o (MulOpposite.op s) _).mp rfl).trans (congrArg Subtype.val hrs).symm
  · intro e
    obtain ⟨g,hg⟩ := (v.same_fiber_iff_orbit e.val (v.vertexFiber o 1).val).mp e.property
    obtain ⟨r,hr⟩ := h.2 g
    refine ⟨r.unop,Subtype.ext ?_⟩
    exact ((v.detect_eq_iff o r g).mp hr).symm.trans hg

lemma simplyConnected_of_detect [PathConnectedSpace (Carrier K)] (o : V)
    (h : Function.Bijective (v.detect o)) : SimplyConnectedSpace v.TotalSpace := by
  apply Covering.simplyConnected_of_monodromy_bijective v.isCoveringMap (v.vertexFiber o 1).val
  exact v.monodromy_bijective_of_detect o h

end FinitePolyhedron.Voltage

/-! The literal voltage bundle is an actual simply connected covering
of the actual finite polygon realization. We construct its connectivity from
monodromy, rather than naming an abstract universal cover as a hypothesis. -/

namespace ConeSkeleton
open CoreGeometry IncidenceTemplate LetterPresentation FinitePolyhedron FinitePolygonModel
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma elementaryTopologyToLetter_bijective :
    Function.Bijective (elementaryTopologyToLetter n w d) := by
  have left : Function.LeftInverse (elementaryTopologyToLetter n w d)
      (elementaryLetterToTopology n w d) := fun x =>
    DFunLike.congr_fun (elementaryTopology_leftInverse n w d) x
  have right : Function.RightInverse (elementaryTopologyToLetter n w d)
      (elementaryLetterToTopology n w d) := by
    intro x
    obtain ⟨g,rfl⟩ := elementaryLetterToTopology_surjective n w d x
    rw [left]
  exact ⟨right.injective,left.surjective⟩

attribute [local instance] OAI.HyperbolicObstruction.ConeSkeleton.instTopologicalSpaceGroup_1
attribute [local instance] OAI.HyperbolicObstruction.ConeSkeleton.instDiscreteTopologyGroup_1
instance elementarySourceUniversalCover_simplyConnected :
    SimplyConnectedSpace (elementarySourceVoltage n w d).TotalSpace := by
  apply Voltage.simplyConnected_of_detect (elementarySourceVoltage n w d)
    (elementaryBaseVertex n w d)
  exact elementaryTopologyToLetter_bijective n w d

end ConeSkeleton

/-! Exact higher homotopy identification for the constructed simply connected
voltage covering of the actual frozen finite polyhedron. -/

namespace ConeSkeleton
attribute [local instance] Classical.propDecidable
open CoreGeometry IncidenceTemplate LetterPresentation FinitePolyhedron
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

attribute [local instance] OAI.HyperbolicObstruction.ConeSkeleton.instTopologicalSpaceGroup_2
attribute [local instance] OAI.HyperbolicObstruction.ConeSkeleton.instDiscreteTopologyGroup_2
lemma elementaryAspherical_iff :
    (elementaryFiniteComplex n w d).Aspherical (elementaryFiniteBasepoint n w d) ↔
      ∀ k : ℕ, Subsingleton (HomotopyGroup.Pi (k+2)
        (elementarySourceVoltage n w d).TotalSpace (elementaryUniversalBasepoint n w d)) := by
  constructor <;> intro h k
  · exact (elementaryHigherCoverEquiv n w d k).subsingleton_congr.mpr (h k)
  · exact (elementaryHigherCoverEquiv n w d k).subsingleton_congr.mp (h k)

end ConeSkeleton

section

/-! A literal basepoint-fixing contraction kills the actual cube-relative
homotopy groups, with no Hurewicz/Whitehead assumption. -/
open scoped Topology unitInterval
namespace BasedHigherContraction
variable {X : Type*} [TopologicalSpace X] (z : X) (H : C(I × X,X))
  (h0 : ∀ x, H (0,x) = x) (h1 : ∀ x, H (1,x) = z) (hz : ∀ t, H (t,z) = z)
  {N : Type*}

include h0 h1 hz in
lemma subsingleton : Subsingleton (HomotopyGroup N X z) := by
  refine ⟨?_⟩
  intro a b
  induction a using Quotient.ind with | _ a =>
  induction b using Quotient.ind with | _ b =>
  apply Quotient.sound
  exact ⟨(nullhomotopy z H h0 h1 hz a).trans (nullhomotopy z H h0 h1 hz b).symm⟩

end BasedHigherContraction
end

section

/-! Literal area-counted edge-disk calculus on the frozen finite-complex
model. All path algebra below uses only the challenge's stutters and spurs. -/
namespace FiniteComplex
variable (K : FiniteComplex)
namespace DiskHomotopy
variable {K}
lemma contextual {p q : List K.Vertex} {n : ℕ} (h : K.DiskHomotopy p q n)
    (l r : List K.Vertex) : K.DiskHomotopy (l++p++r) (l++q++r) n := by
  induction h with
  | refl => exact .refl _
  | move h =>
    apply DiskHomotopy.move
    cases h with
    | stutter l' r' a => simpa only [List.append_assoc] using DiskMove.stutter (l++l') (r'++r) a
    | spur l' r' a b h => simpa only [List.append_assoc] using DiskMove.spur (l++l') (r'++r) a b h
    | triangle l' r' a b c h hn =>
      simpa only [List.append_assoc] using DiskMove.triangle (l++l') (r'++r) a b c h hn
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'

lemma reverse {p q : List K.Vertex} {n : ℕ} (h : K.DiskHomotopy p q n) :
    K.DiskHomotopy p.reverse q.reverse n := by
  induction h with
  | refl => exact .refl _
  | move h =>
    cases h with
    | stutter l r a =>
      simpa [List.reverse_append,List.append_assoc] using
        (DiskHomotopy.move (DiskMove.stutter r.reverse l.reverse a))
    | spur l r a b h =>
      simpa [List.reverse_append,List.append_assoc] using
        (DiskHomotopy.move (DiskMove.spur r.reverse l.reverse a b h))
    | triangle l r a b c h hn =>
      have he : ({c,b,a} : Finset K.Vertex) = {a,b,c} := by ext; simp; tauto
      simpa [List.reverse_append,List.append_assoc] using
        (DiskHomotopy.move (DiskMove.triangle r.reverse l.reverse c b a (he.symm ▸ h) (he.symm ▸ hn)))
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
end DiskHomotopy

end FiniteComplex
namespace FinitePolyhedron.EdgeChain
open HyperbolicObstruction.FiniteComplex
variable {K : FiniteComplex}

lemma nodes_eq_starts {a b : K.Vertex} (p : K.Chain a b) : p.nodes = p.starts ++ [b] := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [nodes,starts,ih,List.cons_append]

lemma nodes_eq_steps {a b : K.Vertex} (p : K.Chain a b) : p.nodes = a :: p.steps := by
  induction p with
  | nil => rfl
  | cons h p ih => change _ :: p.nodes = _ :: _ :: p.steps; rw [ih]

lemma nodes_append' {a b c : K.Vertex} (p : K.Chain a b) (q : K.Chain b c) :
    (p.append q).nodes = p.nodes ++ q.steps := by
  rw [nodes_append,nodes_eq_starts p,nodes_eq_steps q,List.append_assoc]
  rfl

lemma append_assoc {a b c d : K.Vertex} (p : K.Chain a b) (q : K.Chain b c) (r : K.Chain c d) :
    (p.append q).append r = p.append (q.append r) := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [FinitePolyhedron.EdgeChain.append,ih]

lemma nodes_reverse {a b : K.Vertex} (p : K.Chain a b) : p.reverse.nodes = p.nodes.reverse := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    rw [reverse,nodes_append',ih]
    simp only [single,steps,nodes,List.reverse_cons]

lemma nodes_injective {a b : K.Vertex} : Function.Injective (nodes (K := K) (a := a) (b := b)) := by
  intro p
  induction p with
  | nil a =>
    intro q h
    cases q with
    | nil => rfl
    | cons he q =>
      have hh := congrArg List.length h
      simp only [nodes] at hh
      rw [nodes_eq_steps q] at hh
      simp only [List.length_cons,List.length_nil] at hh
      omega
  | @cons a c b he p ih =>
    intro q h
    cases q with
    | nil =>
      have hh := congrArg List.length h
      simp only [nodes] at hh
      rw [nodes_eq_steps p] at hh
      simp only [List.length_cons,List.length_nil] at hh
      omega
    | @cons _ d _ hf q =>
      have h' := List.cons.inj h
      have hd : c = d := by
        have hh := h'.2
        rw [nodes_eq_steps p,nodes_eq_steps q] at hh
        exact (List.cons.inj hh).1
      subst d
      exact congrArg (FinitePolyhedron.EdgeChain.cons he) (ih h'.2)

@[simp] lemma reverse_reverse {a b : K.Vertex} (p : K.Chain a b) : p.reverse.reverse = p := by
  apply nodes_injective
  simp only [nodes_reverse,List.reverse_reverse]

lemma reverse_append {a b c : K.Vertex} (p : K.Chain a b) (q : K.Chain b c) :
    (p.append q).reverse = q.reverse.append p.reverse := by
  apply nodes_injective
  rw [nodes_reverse,nodes_append',List.reverse_append,nodes_append,nodes_reverse]
  have hq : q.steps.reverse = q.reverse.starts := by
    have h := nodes_reverse q
    rw [nodes_eq_starts q.reverse,nodes_eq_steps q,List.reverse_cons] at h
    exact List.append_cancel_right h |>.symm
  rw [hq]

namespace Homotopy
variable {a b c : K.Vertex} {p q : K.Chain a b} {n : ℕ}
lemma refl (p : K.Chain a b) : p.Homotopy p 0 := DiskHomotopy.refl _
lemma symm (h : p.Homotopy q n) : q.Homotopy p n := DiskHomotopy.symm h
lemma trans {r : K.Chain a b} {m : ℕ} (h : p.Homotopy q n) (h' : q.Homotopy r m) :
    p.Homotopy r (n+m) := DiskHomotopy.trans h h'
lemma trans_zero {r : K.Chain a b} (h : p.Homotopy q n) (h' : q.Homotopy r 0) :
    p.Homotopy r n := by simpa using h.trans h'
lemma zero_trans {r : K.Chain a b} (h : p.Homotopy q 0) (h' : q.Homotopy r n) :
    p.Homotopy r n := by simpa using h.trans h'
lemma append_right (h : p.Homotopy q n) (r : K.Chain b c) :
    (p.append r).Homotopy (q.append r) n := by
  unfold Homotopy
  simpa only [nodes_append',List.nil_append] using h.contextual [] r.steps
lemma append_left (h : p.Homotopy q n) {c : K.Vertex} (r : K.Chain c a) :
    (r.append p).Homotopy (r.append q) n := by
  unfold Homotopy
  simpa only [nodes_append,List.append_nil] using h.contextual r.starts []
lemma reverse (h : p.Homotopy q n) : p.reverse.Homotopy q.reverse n := by
  unfold Homotopy
  simpa only [nodes_reverse] using DiskHomotopy.reverse h
end Homotopy

lemma cancel {a b : K.Vertex} (p : K.Chain a b) :
    (p.append p.reverse).Homotopy (.nil a) 0 := by
  induction p with
  | nil a => exact .refl _
  | @cons a b c he p ih =>
    have hre : K.Edge b a := by simpa only [Edge,Finset.pair_comm] using he
    have h := (ih.append_right (single hre)).append_left (single he)
    have hh : ((single he).append (single hre)).Homotopy (.nil a) 0 := by
      change K.DiskHomotopy [a,b,a] [a] 0
      exact DiskHomotopy.move (by simpa only [List.nil_append,List.append_nil] using DiskMove.spur (K := K) [] [] a b he)
    apply Homotopy.zero_trans ?_ hh
    simpa only [single,FinitePolyhedron.EdgeChain.append,reverse,append_assoc] using h

lemma cancel_left {a b : K.Vertex} (p : K.Chain a b) :
    (p.reverse.append p).Homotopy (.nil b) 0 := by simpa only [reverse_reverse] using cancel p.reverse

end FinitePolyhedron.EdgeChain
end

/-! Rooted path algebra with exact zero-cost spur cancellations. This is a
literal triangular disk calculus, not an appeal to topological equivalence. -/
namespace FinitePolyhedron.EdgeChain
open HyperbolicObstruction.FiniteComplex
variable {K : FiniteComplex}

lemma single_self (a : K.Vertex) :
    (single (FinitePolyhedron.edge_self K.complex a)).Homotopy (.nil a) 0 := by
  change K.DiskHomotopy [a,a] [a] 0
  exact DiskHomotopy.move (by simpa using DiskMove.stutter (K := K) [] [] a)

lemma triangle {a b c : K.Vertex} (h : {a,b,c} ∈ K.complex.faces)
    (hab : K.Edge a b) (hbc : K.Edge b c) (hac : K.Edge a c) :
    ∃ k ≤ 1, ((single hab).append (single hbc)).Homotopy (single hac) k := by
  change ∃ k ≤ 1, K.DiskHomotopy [a,b,c] [a,c] k
  by_cases hab' : a = b
  · subst b
    exact ⟨0,by omega,DiskHomotopy.move (by simpa using DiskMove.stutter (K := K) [] [c] a)⟩
  by_cases hbc' : b = c
  · subst c
    exact ⟨0,by omega,DiskHomotopy.move (by simpa using DiskMove.stutter (K := K) [a] [] b)⟩
  by_cases hac' : a = c
  · subst c
    have hh : K.DiskHomotopy [a,b,a] [a] 0 := DiskHomotopy.move (by simpa using DiskMove.spur (K := K) [] [] a b hab)
    have ht : K.DiskHomotopy [a,a] [a] 0 := DiskHomotopy.move (by simpa using DiskMove.stutter (K := K) [] [] a)
    exact ⟨0,by omega,by simpa using hh.trans ht.symm⟩
  · exact ⟨1,le_rfl,DiskHomotopy.move (by simpa using DiskMove.triangle (K := K) [] [] a b c h (by simp [hab',hbc',hac']))⟩

variable (o : K.Vertex) (R : ∀ a, K.Chain o a)

lemma based_nil (a : K.Vertex) : (based o R (.nil a)).Homotopy (.nil o) 0 := cancel (R a)

lemma based_append {a b c : K.Vertex} (p : K.Chain a b) (q : K.Chain b c) :
    ((based o R p).append (based o R q)).Homotopy (based o R (p.append q)) 0 := by
  have h := ((cancel_left (R b)).append_right (q.append (R c).reverse)).append_left ((R a).append p)
  simpa only [based,append_assoc,append] using h

lemma based_homotopy {a b : K.Vertex} {p q : K.Chain a b} {k : ℕ} (h : p.Homotopy q k) :
    (based o R p).Homotopy (based o R q) k :=
  (h.append_right (R b).reverse).append_left (R a)

lemma based_route (hR : R o = .nil o) (a : K.Vertex) :
    (based o R (R a)).Homotopy (.nil o) 0 := by
  simpa only [based,hR,append] using cancel (R a)

lemma unbase {a : K.Vertex} {p : K.Chain a a} {k : ℕ}
    (h : (based o R p).Homotopy (.nil o) k) : p.Homotopy (.nil a) k := by
  let r := R a
  have left : ((r.reverse.append r).append p).Homotopy p 0 := by
    simpa only [append] using (cancel_left r).append_right p
  have right : (p.append (r.reverse.append r)).Homotopy p 0 := by
    simpa only [append_nil] using (cancel_left r).append_left p
  have both : ((r.reverse.append r).append (p.append (r.reverse.append r))).Homotopy p 0 := by
    simpa only [append_assoc] using (left.append_right (r.reverse.append r)).trans_zero right
  have mid := (h.append_right r).append_left r.reverse
  have cancelR := cancel_left r
  have head : ((r.reverse.append (based o R p)).append r).Homotopy p 0 := by
    simpa only [based,append_assoc] using both
  have tail : ((r.reverse.append (.nil o)).append r).Homotopy (.nil a) 0 := by
    simpa only [append_nil] using cancelR
  have mid' : ((r.reverse.append (based o R p)).append r).Homotopy
      ((r.reverse.append (.nil o)).append r) k := by
    simpa only [append_assoc] using mid
  exact head.symm.zero_trans (mid'.trans_zero tail)

end FinitePolyhedron.EdgeChain

section

/-! A proved edge-and-triangle presentation of the actual fundamental group
of a finite barycentric realization. The rooted routes are actual edge paths;
no van Kampen theorem or fundamental-group comparison is postulated. -/

attribute [local instance] Classical.propDecidable
open Set
namespace FinitePolyhedron.EdgePresentation
variable {V : Type*} [Fintype V] [DecidableEq V] (K : AbstractSimplicialComplex V)

variable (o : V) (R : ∀ a, EdgeChain K o a)

omit [Fintype V] in
lemma voltage_value {a b : V} (h : {a,b} ∈ K.faces) :
    (voltage K o R).value a b = gen K o R h := dite_eq_left h

omit [Fintype V] in
lemma eval_eq_mk {a b : V} (p : EdgeChain K a b) :
    Voltage.EdgeChain.eval (voltage K o R) p = PresentedGroup.mk (show Set (FreeGroup (Generator K)) from Relation K o R) (freeEval K p) := by
  induction p with
  | nil a => simp
  | cons h q ih => rw [Voltage.EdgeChain.eval_cons,voltage_value K o R h,ih,freeEval_cons,map_mul]; rfl

omit [Fintype V] in
lemma eval_route (a : V) : Voltage.EdgeChain.eval (voltage K o R) (R a) = 1 := by
  rw [eval_eq_mk]
  exact PresentedGroup.one_of_mem (Relation.route a)

lemma toTopology_mk (hR : R o = .nil o) (z : FreeGroup (Generator K)) :
    toTopology K o R hR (PresentedGroup.mk (show Set (FreeGroup (Generator K)) from Relation K o R) z) =
      FreeGroup.lift (topGenerator K o R) z := rfl

lemma toTopology_chain (hR : R o = .nil o) {a b : V} (p : EdgeChain K a b) :
    toTopology K o R hR (PresentedGroup.mk (show Set (FreeGroup (Generator K)) from Relation K o R) (freeEval K p)) =
      RootedPaths.based o (routeClasses K o R) p.pathClass := by rw [toTopology_mk,lift_freeEval]

lemma toTopology_injective (hR : R o = .nil o) : Function.Injective (toTopology K o R hR) := by
  let : TopologicalSpace (PresentationGroup K o R) := ⊥
  let : DiscreteTopology (PresentationGroup K o R) := ⟨rfl⟩
  let f := (voltage K o R).detect o
  have hcomp : f.comp (toTopology K o R hR) = MonoidHom.id _ := by
    apply PresentedGroup.ext
    rintro ⟨⟨a,b⟩,h⟩
    change (voltage K o R).detect o (toTopology K o R hR (gen K o R h)) = gen K o R h
    rw [toTopology_gen]
    exact ((voltage K o R).detect_edgeLoop o R (eval_route K o R) h).trans (voltage_value K o R h)
  have hl : Function.LeftInverse f (toTopology K o R hR) := fun x => DFunLike.congr_fun hcomp x
  exact hl.injective

lemma toTopology_surjective (hR : R o = .nil o) : Function.Surjective (toTopology K o R hR) := by
  intro y
  obtain ⟨p,hp⟩ := Quotient.exists_rep y.unop
  obtain ⟨c,hc⟩ := edgePath_representative K p
  refine ⟨PresentedGroup.mk (show Set (FreeGroup (Generator K)) from Relation K o R) (freeEval K c),?_⟩
  rw [toTopology_chain]
  have hRo : routeClasses K o R o = .refl _ := by simp [routeClasses,hR]
  rw [RootedPaths.based_loop o (routeClasses K o R) hRo]
  apply MulOpposite.unop_injective
  exact (Path.Homotopic.Quotient.eq.mpr hc).symm.trans hp

end FinitePolyhedron.EdgePresentation
end

/-! Quantitative finite-presentation change, with all word substitutions and
comparison disks constructed. Relator disks are used only after establishing
that the corresponding literal words are null. -/
namespace WordPictures
variable {A B G : Type*} [Group G]

lemma signedWords_rev (f : A → Word B) (a : A × Bool) :
    signedWords f (a.1,!a.2) = FreeGroup.invRev (signedWords f a) := by
  rcases a with ⟨a,b⟩
  cases b <;> simp [signedWords]

lemma signedWords_eval (p : FreeGroup A →* G) (q : FreeGroup B →* G)
    (f : A → Word B) (hf : ∀ a, q (FreeGroup.mk (f a)) = p (FreeGroup.of a)) (a : A × Bool) :
    q (FreeGroup.mk (signedWords f a)) = p (FreeGroup.mk [a]) := by
  rcases a with ⟨a,b⟩
  cases b
  · change q ((FreeGroup.mk (f a))⁻¹) = p ((FreeGroup.of a)⁻¹)
    rw [map_inv,map_inv,hf]
  · exact hf a

lemma flatMap_eval (p : FreeGroup A →* G) (q : FreeGroup B →* G)
    (f : A × Bool → Word B) (hf : ∀ a, q (FreeGroup.mk (f a)) = p (FreeGroup.mk [a]))
    (z : Word A) : q (FreeGroup.mk (z.flatMap f)) = p (FreeGroup.mk z) := by
  induction z with
  | nil => exact (map_one q).trans (map_one p).symm
  | cons a z ih =>
    change q (FreeGroup.mk (f a ++ z.flatMap f)) = p (FreeGroup.mk ([a] ++ z))
    rw [← FreeGroup.mul_mk,← FreeGroup.mul_mk,map_mul,map_mul,hf,ih]

lemma exists_word (p : FreeGroup A →* G) (hp : Function.Surjective p) (g : G) :
    ∃ z : Word A, p (FreeGroup.mk z) = g := by
  obtain ⟨a,ha⟩ := hp g
  obtain ⟨z,hz⟩ := Quot.exists_rep a
  exact ⟨z,(congrArg p hz).trans ha⟩

namespace Homotopy
variable {R : Set (Word A)}

lemma append_both {z z' t t' : Word A} {k l : ℕ}
    (h : Homotopy R z z' k) (h' : Homotopy R t t' l) :
    Homotopy R (z++t) (z'++t') (k+l) := by
  have h₁ : Homotopy R (z++t) (z'++t) k := by simpa using h.contextual [] t
  have h₂ : Homotopy R (z'++t) (z'++t') l := by simpa using h'.contextual z' []
  exact h₁.trans h₂

lemma of_null_difference {z t : Word A} {k : ℕ}
    (h : Homotopy R (z ++ FreeGroup.invRev t) [] k) : Homotopy R z t k := by
  have h₀ : Homotopy R z ((z ++ FreeGroup.invRev t) ++ t) 0 :=
    Homotopy.free (by simp only [← FreeGroup.mul_mk,← FreeGroup.inv_mk]; group)
  have h₁ : Homotopy R ((z ++ FreeGroup.invRev t) ++ t) t k := by
    simpa using h.contextual [] t
  simpa using h₀.trans h₁

/-- A finite per-letter change of boundary words accumulates only linearly. -/
lemma compare_flatMap {B : Type*} (f : B × Bool → Word A) (g : B × Bool → Word A)
    (D : ℕ) (h : ∀ b, ∃ k ≤ D, Homotopy R (f b) (g b) k) (z : Word B) :
    ∃ k ≤ D*z.length, Homotopy R (z.flatMap f) (z.flatMap g) k := by
  induction z with
  | nil => exact ⟨0,by simp,.refl _⟩
  | cons b z ih =>
    obtain ⟨k,hk,hh⟩ := h b
    obtain ⟨l,hl,hz⟩ := ih
    refine ⟨k+l,?_,hh.append_both hz⟩
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
    omega
end Homotopy

lemma flatMap_length_le (f : A × Bool → Word B) (L : ℕ)
    (hf : ∀ a, (f a).length ≤ L) (z : Word A) : (z.flatMap f).length ≤ L*z.length := by
  induction z with
  | nil => simp
  | cons a z ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one]
    have := hf a
    omega

/-- Main quantitative substitution calculation. Both comparison disks and
old-relator disks are supplied as explicit literal Homotopy certificates. -/
lemma linear_of_substitutions {R : Set (Word A)} {S : Set (Word B)}
    (p : FreeGroup A →* G) (q : FreeGroup B →* G)
    (c : B × Bool → Word A) (d : A × Bool → Word B)
    (hd : ∀ a, d (a.1,!a.2) = FreeGroup.invRev (d a))
    (hc : ∀ b, p (FreeGroup.mk (c b)) = q (FreeGroup.mk [b]))
    (M D L : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hlength : ∀ b, (c b).length ≤ L)
    (hR : ∀ z ∈ R, ∃ a ≤ M, Homotopy S (z.flatMap d) [] a)
    (hcomp : ∀ b, ∃ a ≤ D, Homotopy S [b] ((c b).flatMap d) a)
    (hfill : ∀ z : Word A, p (FreeGroup.mk z) = 1 →
      ∃ a, Homotopy R z [] a ∧ (a : ℝ) ≤ C*z.length) :
    ∀ z : Word B, q (FreeGroup.mk z) = 1 →
      ∃ a, Homotopy S z [] a ∧ (a : ℝ) ≤ ((D : ℝ) + M*C*L)*z.length := by
  intro z hz
  have hz' : p (FreeGroup.mk (z.flatMap c)) = 1 := (flatMap_eval q p c hc z).trans hz
  obtain ⟨a,ha,hbound⟩ := hfill _ hz'
  obtain ⟨b,hb,hbfill⟩ := ha.substitute d hd hR
  obtain ⟨k,hk,hkfill⟩ := Homotopy.compare_flatMap (R := S) (fun b => [b])
    (fun b => (c b).flatMap d) D hcomp z
  have hleft : z.flatMap (fun b => [b]) = z := by simp
  rw [hleft,← List.flatMap_assoc] at hkfill
  refine ⟨k+b,by simpa using hkfill.trans hbfill,?_⟩
  have hk' : (k : ℝ) ≤ D*z.length := by exact_mod_cast hk
  have hb' : (b : ℝ) ≤ M*a := by exact_mod_cast hb
  have hlen : ((z.flatMap c).length : ℝ) ≤ L*z.length := by
    exact_mod_cast flatMap_length_le c L hlength z
  have ha' : (a : ℝ) ≤ C*(L*z.length) := hbound.trans (mul_le_mul_of_nonneg_left hlen hC)
  have hb'' := hb'.trans (mul_le_mul_of_nonneg_left ha' (Nat.cast_nonneg M))
  push_cast
  nlinarith

/-! Finite change of presentation preserves the literal linear disk bound.
All finite comparison disks are produced by ordinary algebraic van Kampen
existence; they are not introduced as extra geometric hypotheses. -/

lemma finitely_bounded [Fintype B] (f : B → ℕ) : ∃ M : ℕ, ∀ b, f b ≤ M :=
  ⟨Finset.univ.sup f,fun b => Finset.le_sup (f := f) (Finset.mem_univ b)⟩

/-- The target completeness premise is only the unquantified normal-closure
criterion, proved independently for every presentation used below. -/
theorem finite_change [Finite B] {R : Set (Word A)} {S : Set (Word B)}
    (p : FreeGroup A →* G) (hp : Function.Surjective p)
    (q : FreeGroup B →* G) (hq : Function.Surjective q)
    (finR : R.Finite) (validR : ∀ z ∈ R, p (FreeGroup.mk z) = 1)
    (completeS : ∀ z : Word B, q (FreeGroup.mk z) = 1 → ∃ k, Homotopy S z [] k)
    (C : ℝ) (hC : 0 ≤ C)
    (fillR : ∀ z : Word A, p (FreeGroup.mk z) = 1 →
      ∃ k, Homotopy R z [] k ∧ (k : ℝ) ≤ C*z.length) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z : Word B, q (FreeGroup.mk z) = 1 →
      ∃ k, Homotopy S z [] k ∧ (k : ℝ) ≤ D*z.length := by
  classical
  let := Fintype.ofFinite B
  let := finR.fintype
  choose c hc using (fun b : B => exists_word p hp (q (FreeGroup.of b)))
  choose d hd using (fun a : A => exists_word q hq (p (FreeGroup.of a)))
  let cc := signedWords c
  let dd := signedWords d
  have cc_eval : ∀ b, p (FreeGroup.mk (cc b)) = q (FreeGroup.mk [b]) :=
    signedWords_eval q p c hc
  have dd_eval : ∀ a, q (FreeGroup.mk (dd a)) = p (FreeGroup.mk [a]) :=
    signedWords_eval p q d hd
  have old_disks : ∀ z : R, ∃ k, Homotopy S (z.val.flatMap dd) [] k := by
    intro z
    apply completeS
    exact (flatMap_eval p q dd dd_eval z.val).trans (validR z.val z.property)
  choose old_cost old_disk using old_disks
  obtain ⟨M,hM⟩ := finitely_bounded old_cost
  have comparisons : ∀ b : B × Bool, ∃ k, Homotopy S [b] ((cc b).flatMap dd) k := by
    intro b
    apply (completeS ([b] ++ FreeGroup.invRev ((cc b).flatMap dd)) ?_).imp
      (fun k hk => hk.of_null_difference)
    rw [← FreeGroup.mul_mk, ← FreeGroup.inv_mk, map_mul, map_inv,
      flatMap_eval p q dd dd_eval, cc_eval, mul_inv_cancel]
  choose compare_cost compare_disk using comparisons
  obtain ⟨D,hD⟩ := finitely_bounded compare_cost
  obtain ⟨L,hL⟩ := finitely_bounded (fun b => (cc b).length)
  refine ⟨D+M*C*L,by positivity,?_⟩
  apply linear_of_substitutions p q cc dd (signedWords_rev d) cc_eval M D L C hC hL
  · intro z hz
    exact ⟨old_cost ⟨z,hz⟩,hM _,old_disk ⟨z,hz⟩⟩
  · intro b
    exact ⟨compare_cost b,hD b,compare_disk b⟩
  · exact fillR

end WordPictures

/-! Literal finite relator words for the proved actual fundamental-group
presentation, including exact rooted route words. -/

namespace FinitePolyhedron.EdgePresentation
variable {V : Type*} [Fintype V] [DecidableEq V] (K : AbstractSimplicialComplex V)

omit [Fintype V] in
lemma mk_chainWord {a b : V} (p : EdgeChain K a b) : FreeGroup.mk (chainWord K p) = freeEval K p := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    change FreeGroup.mk ([(⟨_,h⟩,true)] ++ chainWord K p) = _
    rw [←FreeGroup.mul_mk,ih]
    rfl

variable (o : V) (R : ∀ a, EdgeChain K o a)

omit [Fintype V] in
lemma relation_image : FreeGroup.mk '' WordRelation K o R = Relation K o R := by
  ext r
  constructor
  · rintro ⟨z,hz,rfl⟩
    cases hz with
    | self a => exact Relation.self a
    | triangle h hab hbc hac => exact Relation.triangle h hab hbc hac
    | route a => rw [mk_chainWord]; exact Relation.route a
  · intro hr
    cases hr with
    | self a => exact ⟨_,WordRelation.self a,rfl⟩
    | triangle h hab hbc hac => exact ⟨_,WordRelation.triangle h hab hbc hac,rfl⟩
    | route a => exact ⟨_,WordRelation.route a,mk_chainWord K (R a)⟩

lemma wordToTopology_surjective (hR : R o = .nil o) : Function.Surjective (wordToTopology K o R hR) :=
  (toTopology_surjective K o R hR).comp (PresentedGroup.mk_surjective _)

lemma word_to_disk (hR : R o = .nil o) (z : WordPictures.Word (Generator K))
    (hz : wordToTopology K o R hR (FreeGroup.mk z) = 1) :
    ∃ k, WordPictures.Homotopy (WordRelation K o R) z [] k := by
  apply WordPictures.existence
  rw [relation_image]
  apply toTopology_injective K o R hR
  simpa only [wordToTopology,MonoidHom.comp_apply,map_one] using hz

end FinitePolyhedron.EdgePresentation

/-! Realization of ordinary word disks as literal triangular edge disks over
the frozen finite polyhedron. Free-group folds become actual zero-cost spurs. -/

namespace FiniteComplex

section
open FinitePolyhedron FinitePolyhedron.EdgeChain
variable (K : FiniteComplex) (o : K.Vertex) (R : ∀ a, K.Chain o a)

lemma wordChain_append (z t : WordPictures.Word K.EdgeGenerator) :
    wordChain K o R (z++t) = (wordChain K o R z).append (wordChain K o R t) := by
  induction z with
  | nil => rfl
  | cons e z ih => simp only [List.cons_append,wordChain,ih,append_assoc]

lemma signedChain_reverse (e : K.EdgeGenerator × Bool) :
    signedChain K o R (e.1,!e.2) = (signedChain K o R e).reverse := by
  rcases e with ⟨e,b⟩
  cases b <;> simp [signedChain]

lemma wordChain_reverse (z : WordPictures.Word K.EdgeGenerator) :
    wordChain K o R (FreeGroup.invRev z) = (wordChain K o R z).reverse := by
  induction z with
  | nil => rfl
  | cons e z ih =>
    rw [FreeGroup.invRev_cons,wordChain_append,ih]
    change (wordChain K o R z).reverse.append ((signedChain K o R (e.1,!e.2)).append (.nil o)) = _
    rw [append_nil,signedChain_reverse]
    exact (reverse_append _ _).symm

lemma wordChain_context {z t : WordPictures.Word K.EdgeGenerator} {k : ℕ}
    (h : (wordChain K o R z).Homotopy (wordChain K o R t) k)
    (l r : WordPictures.Word K.EdgeGenerator) :
    (wordChain K o R (l++z++r)).Homotopy (wordChain K o R (l++t++r)) k := by
  simpa only [wordChain_append,append_assoc] using
    (h.append_right (wordChain K o R r)).append_left (wordChain K o R l)

lemma wordChain_free {z t : WordPictures.Word K.EdgeGenerator} (h : FreeGroup.Red.Step z t) :
    (wordChain K o R z).Homotopy (wordChain K o R t) 0 := by
  cases h with
  | @not l r e b =>
    have hh : (wordChain K o R [(e,b),(e,!b)]).Homotopy (wordChain K o R []) 0 := by
      change ((signedChain K o R (e,b)).append ((signedChain K o R (e,!b)).append (.nil o))).Homotopy (.nil o) 0
      rw [append_nil,show signedChain K o R (e,!b) = (signedChain K o R (e,b)).reverse from signedChain_reverse K o R (e,b)]
      exact cancel _
    simpa only [List.append_nil,List.append_assoc,List.cons_append,List.nil_append] using wordChain_context K o R hh l r

lemma wordChain_homotopy {S : Set (WordPictures.Word K.EdgeGenerator)} {M : ℕ}
    (rel : ∀ z ∈ S, ∃ k ≤ M, (wordChain K o R z).Homotopy (.nil o) k)
    {z t : WordPictures.Word K.EdgeGenerator} {a : ℕ} (h : WordPictures.Homotopy S z t a) :
    ∃ k ≤ M*a, (wordChain K o R z).Homotopy (wordChain K o R t) k := by
  induction h with
  | refl => exact ⟨0,by simp,DiskHomotopy.refl _⟩
  | move h =>
    cases h with
    | free h => exact ⟨0,by simp,wordChain_free K o R h⟩
    | face l r z hz =>
      obtain ⟨k,hk,hh⟩ := rel z hz
      exact ⟨k,by simpa using hk,by simpa using wordChain_context K o R (show (wordChain K o R z).Homotopy (wordChain K o R []) k from hh) l r⟩
    | reverseFace l r z hz =>
      obtain ⟨k,hk,hh⟩ := rel z hz
      have hh' : (wordChain K o R (FreeGroup.invRev z)).Homotopy (wordChain K o R []) k := by
        simpa only [wordChain_reverse,wordChain,reverse] using hh.reverse
      exact ⟨k,by simpa using hk,by simpa using wordChain_context K o R hh' l r⟩
  | symm _ ih => obtain ⟨k,hk,hh⟩ := ih; exact ⟨k,hk,hh.symm⟩
  | trans h h' ih ih' =>
    obtain ⟨k,hk,hh⟩ := ih
    obtain ⟨l,hl,hh'⟩ := ih'
    exact ⟨k+l,by rw [Nat.mul_add]; omega,hh.trans hh'⟩

lemma wordChain_chainWord {a b : K.Vertex} (p : K.Chain a b) :
    (wordChain K o R (EdgePresentation.chainWord K.complex p)).Homotopy (based o R p) 0 := by
  induction p with
  | nil a => exact (based_nil o R a).symm
  | cons h p ih =>
    exact (ih.append_left (generatorChain K o R ⟨_,h⟩)).trans_zero (based_append o R (single h) p)

lemma wordChain_relator (hR : R o = .nil o)
    (z : WordPictures.Word K.EdgeGenerator) (hz : EdgePresentation.WordRelation K.complex o R z) :
    ∃ k ≤ 1, (wordChain K o R z).Homotopy (.nil o) k := by
  cases hz with
  | self a =>
    have hh := (based_homotopy o R (single_self (K := K) a)).trans_zero (based_nil o R a)
    exact ⟨0,by omega,by simpa [wordChain,signedChain,generatorChain] using hh⟩
  | route a =>
    exact ⟨0,by omega,(wordChain_chainWord K o R (R a)).trans_zero (based_route o R hR a)⟩
  | @triangle a b c hf hab hbc hac =>
    obtain ⟨k,hk,hh⟩ := triangle (K := K) hf hab hbc hac
    have h₁ := (based_append o R (single hab) (single hbc)).zero_trans (based_homotopy o R hh)
    have h₂ := (h₁.append_right (based o R (single hac)).reverse).trans_zero (cancel (based o R (single hac)))
    refine ⟨k,hk,?_⟩
    simpa [wordChain,signedChain,generatorChain,append_assoc] using h₂

/-- A literal word disk in the intrinsic triangular presentation becomes an
actual disk of no more triangular faces; route cancellations have zero area. -/
lemma word_disk_realization (hR : R o = .nil o)
    {z : WordPictures.Word K.EdgeGenerator} {a : ℕ}
    (h : WordPictures.Homotopy (EdgePresentation.WordRelation K.complex o R) z [] a) :
    ∃ k ≤ a, (wordChain K o R z).Homotopy (.nil o) k := by
  simpa only [Nat.one_mul,wordChain] using wordChain_homotopy K o R (wordChain_relator K o R hR) h

end

/-! The challenge's literal disk moves preserve every triangular voltage.
This is valid even for the untyped intermediate lists in DiskHomotopy. -/
open FinitePolyhedron
variable (K : FiniteComplex) {G : Type*} [Group G] (v : Voltage K.complex G)

lemma pathValue_prefix {a : K.Vertex} {u t : List K.Vertex}
    (h : pathValue K v (a::u) = pathValue K v (a::t)) (l : List K.Vertex) :
    pathValue K v (l++a::u) = pathValue K v (l++a::t) := by
  induction l with
  | nil => exact h
  | cons b l ih =>
    cases l with
    | nil => exact congrArg (v.value b a * ·) h
    | cons c l => exact congrArg (v.value b c * ·) ih

lemma diskMove_sound {p q : List K.Vertex} {k : ℕ} (h : K.DiskMove p q k) :
    pathValue K v p = pathValue K v q := by
  cases h with
  | stutter l r a =>
    simp only [List.append_assoc,List.cons_append,List.nil_append]
    apply pathValue_prefix K v (l := l)
    simp only [pathValue,v.self,one_mul]
  | spur l r a b he =>
    simp only [List.append_assoc,List.cons_append,List.nil_append]
    apply pathValue_prefix K v (l := l)
    simp only [pathValue,v.reverse he]
    group
  | triangle l r a b c hf hn =>
    simp only [List.append_assoc,List.cons_append,List.nil_append]
    apply pathValue_prefix K v (l := l)
    simp only [pathValue,←mul_assoc,v.triangle a b c hf]

lemma diskHomotopy_sound {p q : List K.Vertex} {k : ℕ} (h : K.DiskHomotopy p q k) :
    pathValue K v p = pathValue K v q := by
  induction h with
  | refl => rfl
  | move h => exact diskMove_sound K v h
  | symm h ih => exact ih.symm
  | trans h h' ih ih' => exact ih.trans ih'

lemma chain_pathValue {a b : K.Vertex} (p : K.Chain a b) :
    pathValue K v p.nodes = Voltage.EdgeChain.eval v p := by
  induction p with
  | nil => rfl
  | @cons a b c h p ih =>
    change pathValue K v (a::p.nodes) = v.value a b * _
    rw [EdgeChain.nodes_eq_steps p,pathValue,←EdgeChain.nodes_eq_steps p,ih]
    rfl

end FiniteComplex

/-! Group-isomorphism transport for geometric actions. -/
section
universe u v w

lemma NoGeometricCATZeroAction.of_mulEquiv {G : Type v} {H : Type w} [Group G] [Group H]
    (e : G ≃* H) (h : NoGeometricCATZeroAction.{u} G) : NoGeometricCATZeroAction.{u} H := by
  intro X m hn hp hc hz
  let := m
  let := hn
  let := hp
  let := hc
  have := h X m hn hp hc hz
  exact ⟨fun A => isEmptyElim (A.pullback e)⟩

end

section

/-! Transfer of linear word filling to literal triangular disk filling.
All disk-null loops are handled,
with the same list length convention `length - 1`. -/

namespace FinitePolyhedron.EdgeChain
open HyperbolicObstruction.FiniteComplex
variable {K : FiniteComplex}

lemma nodes_ofListEnd (a b : K.Vertex) (t : List K.Vertex)
    (h : K.EdgePath (a :: (t ++ [b]))) :
    (ofListEnd a b t h).nodes = a :: (t ++ [b]) := by
  induction t generalizing a with
  | nil => rfl
  | cons c t ih => simp only [ofListEnd,nodes,ih,List.cons_append]

lemma chainWord_length {a b : K.Vertex} (p : K.Chain a b) :
    (EdgePresentation.chainWord K.complex p).length = p.nodes.length - 1 := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [EdgePresentation.chainWord,List.length_cons,nodes,ih]
    rw [nodes_eq_steps p]
    simp
end FinitePolyhedron.EdgeChain

namespace FiniteComplex
open FinitePolyhedron FinitePolyhedron.EdgeChain
variable (K : FiniteComplex) (o : K.Vertex) (R : ∀ a, K.Chain o a) (hR : R o = .nil o)

lemma disk_word_null {a : K.Vertex} (p : K.Chain a a)
    (hd : ∃ k, K.Disk p.nodes k) :
    EdgePresentation.wordToTopology K.complex o R hR
      (FreeGroup.mk (EdgePresentation.chainWord K.complex p)) = 1 := by
  obtain ⟨k,b,h⟩ := hd
  have hh := diskHomotopy_sound K (EdgePresentation.voltage K.complex o R) h
  rw [chain_pathValue,EdgePresentation.eval_eq_mk] at hh
  change _ = 1 at hh
  rw [EdgePresentation.wordToTopology,MonoidHom.comp_apply,EdgePresentation.mk_chainWord,hh,map_one]

/-- Intrinsic word area gives literal triangular disk area with no loss. -/
theorem linearDiskFilling_of_intrinsic (C : ℝ) (_ : 0 ≤ C)
    (fill : ∀ z : WordPictures.Word K.EdgeGenerator,
      EdgePresentation.wordToTopology K.complex o R hR (FreeGroup.mk z) = 1 →
      ∃ k, WordPictures.Homotopy (EdgePresentation.WordRelation K.complex o R) z [] k ∧
        (k : ℝ) ≤ C*z.length) : K.LinearDiskFilling C := by
  intro p hp hc hd
  obtain ⟨a,t,hp'|hp'⟩ := hc
  · subst p
    let q := ofListEnd a a t hp
    have hq : q.nodes = a :: (t ++ [a]) := nodes_ofListEnd a a t hp
    have hd' : ∃ k, K.Disk q.nodes k := by simpa only [hq] using hd
    obtain ⟨k,hk,hbound⟩ := fill (EdgePresentation.chainWord K.complex q)
      (disk_word_null K o R hR q hd')
    obtain ⟨l,hl,hreal⟩ := word_disk_realization K o R hR hk
    have hbased := (wordChain_chainWord K o R q).symm.zero_trans hreal
    have hback := unbase o R hbased
    refine ⟨l,⟨a,?_⟩,?_⟩
    · change K.DiskHomotopy q.nodes [a] l at hback
      simpa only [hq] using hback
    · rw [chainWord_length,hq] at hbound
      exact le_trans (by exact_mod_cast hl) hbound
  · subst p
    exact ⟨0,⟨a,DiskHomotopy.refl _⟩,by simp⟩

include R hR in
/-- Quantitative finite-presentation change, followed by literal geometric
realization, produces the exact main's triangular filling assertion. -/
theorem linearDiskFilling_of_presentation {A G : Type*} [Group G]
    (S : Set (WordPictures.Word A)) (p : FreeGroup A →* G) (hp : Function.Surjective p)
    (e : G ≃* RootedPaths.PiOne (K := K.complex) o)
    (finS : S.Finite) (validS : ∀ z ∈ S, p (FreeGroup.mk z) = 1)
    (C : ℝ) (hC : 0 ≤ C)
    (fill : ∀ z : WordPictures.Word A, p (FreeGroup.mk z) = 1 →
      ∃ k, WordPictures.Homotopy S z [] k ∧ (k : ℝ) ≤ C*z.length) :
    ∃ D : ℝ, 0 ≤ D ∧ K.LinearDiskFilling D := by
  obtain ⟨D,hD,hfill⟩ := WordPictures.finite_change
    (e.toMonoidHom.comp p) (e.surjective.comp hp)
    (EdgePresentation.wordToTopology K.complex o R hR)
    (EdgePresentation.wordToTopology_surjective K.complex o R hR) finS
    (fun z hz => by simp only [MonoidHom.comp_apply,validS z hz,map_one])
    (EdgePresentation.word_to_disk K.complex o R hR) C hC
    (fun z hz => fill z (e.injective (by
      change e (p (FreeGroup.mk z)) = 1 at hz
      exact hz.trans (map_one e).symm)))
  exact ⟨D,hD,linearDiskFilling_of_intrinsic K o R hR D hD hfill⟩

lemma nonempty_vertex (x : K.Carrier) : Nonempty K.Vertex := by
  by_contra h
  have : IsEmpty K.Vertex := not_nonempty_iff.mp h
  have hs := x.property.2.1
  simp at hs

/-- Basepoint-independent form of the faithful finite-presentation transfer. -/
theorem linearDiskFilling_of_piOne [PathConnectedSpace K.Carrier]
    {A G : Type*} [Group G] (x : K.Carrier)
    (S : Set (WordPictures.Word A)) (p : FreeGroup A →* G) (hp : Function.Surjective p)
    (e : G ≃* FundamentalGroup K.Carrier x)
    (finS : S.Finite) (validS : ∀ z ∈ S, p (FreeGroup.mk z) = 1)
    (C : ℝ) (hC : 0 ≤ C)
    (fill : ∀ z : WordPictures.Word A, p (FreeGroup.mk z) = 1 →
      ∃ k, WordPictures.Homotopy S z [] k ∧ (k : ℝ) ≤ C*z.length) :
    ∃ D : ℝ, 0 ≤ D ∧ K.LinearDiskFilling D := by
  let : PathConnectedSpace (FinitePolyhedron.Carrier K.complex) := ‹PathConnectedSpace K.Carrier›
  obtain ⟨o⟩ := nonempty_vertex K x
  let e' : G ≃* RootedPaths.PiOne (K := K.complex) o :=
    e.trans ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x (vertex K.complex o)).trans
      (groupOppositeEquiv _).symm)
  exact linearDiskFilling_of_presentation K o (edgeRoutes K.complex o)
    (edgeRoutes_self K.complex o) S p hp e' finS validS C hC fill

end FiniteComplex
end

/-! Actual homotopy-equivalence invariance of the fundamental group. -/

/-! The literal finite barycentric complex has exactly the original letter group,
not a conditional presentation of it. -/

namespace ConeSkeleton

/-! Infinitude can be obtained without a topological Euler theorem: the many
six-letter cells alone inject into the original letter-edge module of any
finite cover. Their cardinality exceeds the number of original generators. -/

open IncidenceTemplate CoreGeometry LetterPresentation IntegralIncidence
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma sixCellIndex_injective : Function.Injective (sixCellIndex n w d) := by
  intro x y h
  have hh : x.1 = y.1 ∧ x.2 = y.2 := by
    simpa only [sixCellIndex,Prod.mk.injEq,Sum.inr.injEq] using h
  exact Prod.ext hh.1 hh.2

lemma originalEdgeChain_map (g : LetterPresentation.Group n w d) (a : Alphabet n) :
    Finsupp.lmapDomain ℤ ℤ (originalEdgeIndex n w d)
      (edgeChain (fun a : Alphabet n => elementaryVoltage n w (letterVoltage n w d)
        ((.inl (.inl a.1)),a.2)) (g,a)) =
    edgeChain (elementaryVoltage n w (letterVoltage n w d)) (g,(.inl (.inl a.1),a.2)) := by
  rcases a with ⟨a,b⟩
  cases b <;> simp only [edgeChain,Bool.false_eq_true,ite_false,ite_true,map_neg,
    Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,originalEdgeIndex]

lemma sixFaceBoundary_map (c : LetterPresentation.Group n w d × Six n d) :
    Finsupp.lmapDomain ℤ ℤ (originalEdgeIndex n w d) (sixFaceBoundary n w d c) =
      (elementaryPolygons n w d).faceBoundary (elementaryVoltage n w (letterVoltage n w d))
        (sixCellIndex n w d c) := by
  unfold sixFaceBoundary Polygons.faceBoundary
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [originalEdgeChain_map]
  rfl

lemma sixBoundary_map (z : SixChain n w d) :
    Finsupp.lmapDomain ℤ ℤ (originalEdgeIndex n w d) (sixBoundary n w d z) =
      letterBoundary₂ n w d (Finsupp.lmapDomain ℤ ℤ (sixCellIndex n w d) z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | single c a =>
    simp only [sixBoundary,Finsupp.linearCombination_single,map_smul,
      letterBoundary₂,Polygons.d₂]
    rw [sixFaceBoundary_map]
    simp only [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,
      Finsupp.linearCombination_single]

lemma sixBoundary_injective (h : Function.Injective (letterBoundary₂ n w d)) :
    Function.Injective (sixBoundary n w d) := by
  intro x y he
  apply Finsupp.mapDomain_injective (sixCellIndex_injective n w d)
  apply h
  change letterBoundary₂ n w d (Finsupp.lmapDomain ℤ ℤ (sixCellIndex n w d) x) =
    letterBoundary₂ n w d (Finsupp.lmapDomain ℤ ℤ (sixCellIndex n w d) y)
  rw [←sixBoundary_map,←sixBoundary_map,he]

lemma six_card_le_of_finite [Fintype (LetterPresentation.Group n w d)]
    (h : Function.Injective (letterBoundary₂ n w d)) : Fintype.card (Six n d) ≤ n+1 := by
  have hk := LinearMap.finrank_le_finrank_of_injective (sixBoundary_injective n w d h)
  simp only [Module.finrank_finsupp_self,Fintype.card_prod,Fintype.card_fin] at hk
  have hp := Fintype.card_pos (α := LetterPresentation.Group n w d)
  nlinarith

/-- An exact algebraic infinitude criterion for the actual presentation. -/
theorem infinite_of_boundary_and_six (h : Function.Injective (letterBoundary₂ n w d))
    (hs : n+1 < Fintype.card (Six n d)) : Infinite (LetterPresentation.Group n w d) := by
  rcases finite_or_infinite (LetterPresentation.Group n w d) with hf | hi
  · let := Fintype.ofFinite (LetterPresentation.Group n w d)
    exact False.elim (Nat.not_lt_of_ge (six_card_le_of_finite n w d h) hs)
  · exact hi

end ConeSkeleton

section

namespace SixTable
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

lemma included_pair_of_good {δ ε : ℝ} (he : ε < 1)
    {d : (Fin 6 → A) → Bool} (hd : ¬ BadPairs δ ε d)
    {r q : Fin 6} (hrq : r ≠ q) (u v : A) :
    ∃ x : Fin 6 → A, d x = true ∧ x r = u ∧ x q = v := by
  have hh : |count r q u v d - (Fintype.card A : ℝ)^(1-δ)| <
      ε*(Fintype.card A : ℝ)^(1-δ) :=
    lt_of_not_ge (fun h => hd ⟨⟨(r,q),hrq⟩,u,v,h⟩)
  have hp : 0 < (Fintype.card A : ℝ)^(1-δ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast Fintype.card_pos (α := A)) _
  have hc : 0 < count r q u v d := by
    have hlo := (abs_lt.mp hh).1
    nlinarith
  by_contra hn
  have hz : count r q u v d = 0 := by
    unfold count
    apply Finset.sum_eq_zero
    intro x hx
    have hpair := (mem_pairTrials hrq u v x).mp hx
    have hfalse : d x = false := Bool.eq_false_iff.mpr (fun h => hn ⟨x,h,hpair⟩)
    simp [hfalse]
  linarith

lemma card_included_at_least_pairs {δ ε : ℝ} (he : ε < 1)
    {d : (Fin 6 → A) → Bool} (hd : ¬ BadPairs δ ε d) :
    Fintype.card A * Fintype.card A ≤ Fintype.card {x : Fin 6 → A // d x = true} := by
  classical
  let f : {x : Fin 6 → A // d x = true} → A × A := fun x => (x.val 0,x.val 1)
  have hs : Function.Surjective f := by
    rintro ⟨u,v⟩
    obtain ⟨x,hx,hr,hq⟩ := included_pair_of_good he hd (by decide : (0 : Fin 6) ≠ 1) u v
    exact ⟨⟨x,hx⟩,Prod.ext hr hq⟩
  simpa only [Fintype.card_prod] using Fintype.card_le_of_surjective f hs
end SixTable

namespace IncidenceTemplate
open LetterPresentation
lemma SamplingStage.many_six {m : ℕ} {δ : ℝ} (s : SamplingStage m δ) :
    s.size+1 < Fintype.card (ConeSkeleton.Six s.size s.six) := by
  have hh := SixTable.card_included_at_least_pairs
    ((stageError_le_third m).trans_lt (by norm_num : (1:ℝ)/3 < 1)) s.six_good
  rw [card_symmetricAlphabet] at hh
  simp only [←Nat.card_eq_fintype_card] at hh ⊢
  change 2*(s.size+1)*(2*(s.size+1)) ≤ Nat.card (ConeSkeleton.Six s.size s.six) at hh
  nlinarith
end IncidenceTemplate
end

/-! The same supplied final arrays yield infinite groups unconditionally.
This discharges the last group-action-side hypothesis; the finite-polyhedron
realization and group-to-topology consequences are still separate obligations. -/
namespace IncidenceTemplate

section
open CoreGeometry LetterPresentation ConeSkeleton

/-- Infinitude via the independent six-cell rank obstruction, with all
finite-table/cardinality and d₂ hypotheses discharged. -/
instance finalDiagramStage_infinite (m : ℕ) :
    Infinite (SamplingStage.LetterGroup finalDiagramStage m) :=
  infinite_of_boundary_and_six (finalSize m) (finalMaster m) (finalSix m)
    (finalDiagramStage_boundary_injective m) ((finalDiagramStage m).many_six)

/-- The no-action conclusion for the selected original groups,
without an infinitude assumption. -/
theorem finalDiagramStage_noAction :
    ∀ᶠ m in Filter.atTop, NoGeometricCATZeroAction (SamplingStage.LetterGroup finalDiagramStage m) :=
  SamplingStage.eventually_noAction finalDiagramStage

/-! The selected presentations give actual connected finite polyhedra
whose fundamental groups admit no geometric CAT(0) action. -/
open CoreGeometry LetterPresentation ConeSkeleton
universe u

instance finalFinite_pathConnected (m : ℕ) : PathConnectedSpace (finalFiniteComplex m).Carrier :=
  elementaryFinite_pathConnected (finalSize m) (finalMaster m) (finalSix m)

instance finalFinite_infinite (m : ℕ) :
    Infinite (FundamentalGroup (finalFiniteComplex m).Carrier (finalFiniteBasepoint m)) :=
  Infinite.of_injective (finalFinitePiOneEquiv m) (finalFinitePiOneEquiv m).injective

theorem finalFinite_noAction : ∀ᶠ m in Filter.atTop,
    NoGeometricCATZeroAction.{u}
      (FundamentalGroup (finalFiniteComplex m).Carrier (finalFiniteBasepoint m)) :=
  finalDiagramStage_noAction.mono fun m h => h.of_mulEquiv (finalFinitePiOneEquiv m)

end

/-! The very same selected finite complex now satisfies the original main's
literal triangular linear disk inequality, in addition to its pi1 obstruction.
No picture-producer or filling-transfer hypothesis remains. -/
section
open CoreGeometry LetterPresentation ConeSkeleton
universe u

lemma finalFinite_linear (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ (finalFiniteComplex m).LinearDiskFilling C := by
  obtain ⟨C,hC,fill⟩ := finalDiagramStage_linear m
  apply FiniteComplex.linearDiskFilling_of_piOne (finalFiniteComplex m)
    (finalFiniteBasepoint m)
    (SimpleWordRelator (finalSize m) (finalMaster m) (finalSix m))
    (PresentedGroup.mk (Relator (finalSize m) (finalMaster m) (finalSix m)))
    (PresentedGroup.mk_surjective _) (finalFinitePiOneEquiv m)
    (simpleWordRelator_finite _ _ _) ?_ C hC.le fill
  intro z hz
  apply PresentedGroup.one_of_mem
  rw [← wordRelator_image]
  exact ⟨z,simpleWordRelator_original _ _ _ hz,rfl⟩

end

/-! The SAME selected arrays give a literal basepoint-fixing contraction of
 their actual universal cover. In particular the full higher-homotopy clause
 of the unchanged finite-model theorem is discharged, unconditionally. -/

open CoreGeometry LetterPresentation ConeSkeleton FinitePolyhedron FinitePolygonModel
attribute [local instance] Classical.propDecidable
universe u
variable (m : ℕ)

attribute [local instance] OAI.HyperbolicObstruction.IncidenceTemplate.instDecidableEqElementaryVertexFinalSizeFinalMaster_1
attribute [local instance] OAI.HyperbolicObstruction.IncidenceTemplate.instDecidableEqElementaryEdgeFinalSizeFinalMaster_1
attribute [local instance] OAI.HyperbolicObstruction.IncidenceTemplate.instDecidableEqElementaryCellFinalSizeFinalMasterFinalSix_1
attribute [local instance] OAI.HyperbolicObstruction.IncidenceTemplate.instTopologicalSpaceGroupFinalSizeFinalMasterFinalSix
attribute [local instance] OAI.HyperbolicObstruction.IncidenceTemplate.instDiscreteTopologyGroupFinalSizeFinalMasterFinalSix
lemma finalCover_higher (k : ℕ) : Subsingleton (HomotopyGroup.Pi (k+2)
    (elementarySourceVoltage (finalSize m) (finalMaster m) (finalSix m)).TotalSpace
    (elementaryUniversalBasepoint (finalSize m) (finalMaster m) (finalSix m))) := by
  let P := elementaryPolygonData (finalSize m) (finalMaster m) (finalSix m)
  let ρ := fun e => elementaryVoltage (finalSize m) (finalMaster m)
    (letterVoltage (finalSize m) (finalMaster m) (finalSix m)) (e,true)
  have hc : ∀ c, (List.ofFn (fun i => Data.signed ρ (P.side c i))).prod = 1 := by
    dsimp only [P,ρ]
    intro c
    simpa only [elementarySignedVoltage,elementaryPolygonData] using
      elementaryLetterVoltage_cell (finalSize m) (finalMaster m) (finalSix m) c
  let v := P.voltage ρ hc
  let z : v.TotalSpace := elementaryUniversalBasepoint (finalSize m) (finalMaster m) (finalSix m)
  let : LinearOrder P.Vertex := linearOrderOfSTO WellOrderingRel
  let : SimplyConnectedSpace v.TotalSpace :=
    elementarySourceUniversalCover_simplyConnected (finalSize m) (finalMaster m) (finalSix m)
  let : CommGroup (v.LoopClass z) := HSpaceFundamental.commGroup
  let T := P.obstructionWeight ρ hc z
  let w := finalTriangleEdgeWeight m (Additive (v.LoopClass z)) T
  have hw := finalTriangleEdgeWeight_equation m (Additive (v.LoopClass z)) T
  change Subsingleton (HomotopyGroup.Pi (k+2) v.TotalSpace z)
  apply BasedHigherContraction.subsingleton z (P.coverContraction ρ hc z w hw)
    (P.coverContraction_initial ρ hc z w hw) (P.coverContraction_final ρ hc z w hw)
  exact P.coverContraction_fixed ρ hc z w hw (elementaryBaseVertex (finalSize m) (finalMaster m) (finalSix m)) 1 rfl

lemma finalFinite_aspherical : (finalFiniteComplex m).Aspherical (finalFiniteBasepoint m) := by
  apply (elementaryAspherical_iff (finalSize m) (finalMaster m) (finalSix m)).mpr
  exact finalCover_higher m

end IncidenceTemplate

/-! Elementary facts about WordLength and WordDistance for the four-point
characterization of hyperbolicity. -/

/-! Cochains are evaluated on the actual area-counted word homotopies.
Free folds contribute exactly zero; each literal relator contributes its
own cochain integral. No planar realization hypothesis is needed. -/
namespace WordPictures
variable {A G : Type*} [Group G]
namespace Cochain
variable (φ : FreeGroup A →* G) (ω : G → G → ℝ)

lemma integral_append (g : G) (u v : Word A) :
    integral φ ω g (u++v)=integral φ ω g u+integral φ ω (g*value φ u) v := by
  induction u generalizing g with
  | nil => simp
  | cons a u ih => simp only [List.cons_append,integral_cons,value_cons,ih,mul_assoc]; ring

variable (hω : ∀ x y, ω x y = -ω y x)
include hω
lemma integral_reverse (g : G) (w : Word A) :
    integral φ ω (g*value φ w) (FreeGroup.invRev w) = -integral φ ω g w := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w a ih =>
    rcases a with ⟨a,b⟩
    simp only [FreeGroup.invRev_append,integral_append,value_append]
    rw [show FreeGroup.invRev [(a,b)]=[(a,!b)] by simp [FreeGroup.invRev]]
    simp only [integral_cons,integral_nil,value_cons,value_nil,mul_one,letter_flip]
    simp only [mul_assoc,mul_inv_cancel,mul_one,ih,add_zero]
    rw [hω]
    ring

lemma integral_reduction {u v : Word A} (h : FreeGroup.Red.Step u v) (g : G) :
    integral φ ω g u=integral φ ω g v := by
  cases h with
  | not =>
    simp only [integral_append,integral_cons,      letter_flip,mul_assoc,mul_inv_cancel,mul_one,mul_one]
    rw [hω]
    ring

variable {R : Set (Word A)}
include hω
lemma move_bound (hv : ∀ w ∈ R, value φ w=1) (D : ℝ)
    (hD : ∀ g w, w∈R → |integral φ ω g w| ≤ D)
    {u v : Word A} {n : ℕ} (h : Move R u v n) (g : G) :
    |integral φ ω g u-integral φ ω g v| ≤ n*D := by
  cases h with
  | free h => simp [integral_reduction φ ω hω h g]
  | face l r w hw =>
    simp only [integral_append,value_append,hv w hw,mul_one,Nat.cast_one,one_mul]
    convert hD (g*value φ l) w hw using 1; congr 1; ring
  | reverseFace l r w hw =>
    have hh : integral φ ω (g*value φ l) (FreeGroup.invRev w) =
        -integral φ ω (g*value φ l) w := by
      simpa only [hv w hw,mul_one] using integral_reverse φ ω hω (g*value φ l) w
    simp only [integral_append,value_append,value_reverse,hv w hw,inv_one,mul_one,
      Nat.cast_one,one_mul,hh]
    convert hD (g*value φ l) w hw using 1
    all_goals try with_reducible_and_instances rfl
    rw [show integral φ ω g l + -integral φ ω (g*value φ l) w + integral φ ω (g*value φ l) r -
      (integral φ ω g l+integral φ ω (g*value φ l) r) = -integral φ ω (g*value φ l) w by ring,
      abs_neg]

lemma homotopy_bound (hv : ∀ w ∈ R, value φ w=1) (D : ℝ) (_ : 0 ≤ D)
    (hD : ∀ g w, w∈R → |integral φ ω g w| ≤ D)
    {u v : Word A} {n : ℕ} (h : Homotopy R u v n) (g : G) :
    |integral φ ω g u-integral φ ω g v| ≤ n*D := by
  induction h with
  | refl => simp
  | move h => exact move_bound φ ω hω hv D hD h g
  | symm h ih => simpa only [abs_sub_comm] using ih
  | trans h h' ih ih' =>
    calc
      _ ≤ |integral φ ω g _-integral φ ω g _| +
          |integral φ ω g _-integral φ ω g _| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add ih ih'
      _ = _ := by push_cast; ring

end Cochain
end WordPictures

/-! Finite unit-speed vertex paths; all indices are bounded explicitly. -/
section
open Finset
namespace VertexPath
variable {X : Type*}
lemma sub_finish (p : VertexPath X) {i j : ℕ} (hij : i ≤ j) : (p.sub i j).finish=p.point j := by
  simp [finish,Nat.add_sub_of_le hij]
lemma append_at_left (p q : VertexPath X) {i : ℕ} (hi : i ≤ p.length) :
    (p.append q).point i=p.point i := ite_eq_left hi
lemma append_at_right (p q : VertexPath X) (h : p.finish=q.start) (j : ℕ) :
    (p.append q).point (p.length+j)=q.point j := by
  by_cases hj : j=0
  · simpa [hj,append,finish,start] using h
  · simp [append,show ¬p.length+j ≤ p.length by omega]
lemma append_finish (p q : VertexPath X) (h : p.finish=q.start) :
    (p.append q).finish=q.finish := append_at_right p q h _
lemma integral_append (p q : VertexPath X) (h : p.finish=q.start) (ω : X→X→ℝ) :
    (p.append q).integral ω=p.integral ω+q.integral ω := by
  unfold integral
  rw [append_length,Finset.sum_range_add]
  congr 1
  · apply sum_congr rfl
    intro i hi
    rw [append_at_left p q (by simpa using le_of_lt (mem_range.mp hi)),
      append_at_left p q (by simpa [Nat.add_one_le_iff] using mem_range.mp hi)]
  · apply sum_congr rfl
    intro i hi
    rw [append_at_right p q h,show p.length+i+1=p.length+(i+1) by omega,
      append_at_right p q h]
lemma integral_reverse (p : VertexPath X) (ω : X→X→ℝ)
    (hω : ∀ x y, ω x y = -ω y x) : p.reverse.integral ω= -p.integral ω := by
  unfold integral
  rw [reverse_length,←Finset.sum_range_reflect (fun i => ω (p.reverse.point i) (p.reverse.point (i+1)))]
  simp only [reverse_at,←Finset.sum_neg_distrib]
  apply sum_congr rfl
  intro i hi
  have hi := mem_range.mp hi
  rw [show p.length-(p.length-1-i)=i+1 by omega,
    show p.length-(p.length-1-i+1)=i by omega]
  exact hω _ _

variable [MetricSpace X]
lemma unit_sub {p : VertexPath X} (hp : p.Unit) {i j : ℕ} (hj : j ≤ p.length) :
    (p.sub i j).Unit := by
  intro k hk
  change dist (p.point (i+k)) (p.point (i+(k+1)))  ≤  1
  rw [←Nat.add_assoc]
  exact hp _ (by change k<j-i at hk; omega)
lemma unit_reverse {p : VertexPath X} (hp : p.Unit) : p.reverse.Unit := by
  intro i hi
  change dist (p.point (p.length-i)) (p.point (p.length-(i+1)))  ≤  1
  rw [dist_comm,show p.length-i=p.length-(i+1)+1 by change i<p.length at hi; omega]
  exact hp _ (by change i<p.length at hi; omega)
lemma unit_append {p q : VertexPath X} (hp : p.Unit) (hq : q.Unit)
    (h : p.finish=q.start) : (p.append q).Unit := by
  intro i hi
  by_cases hip : i<p.length
  · rw [append_at_left p q (le_of_lt hip),append_at_left p q (by omega)]
    exact hp i hip
  · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (show p.length ≤ i by omega)
    rw [append_at_right p q h,show p.length+j+1=p.length+(j+1) by omega,
      append_at_right p q h]
    exact hq j (by change p.length+j<p.length+q.length at hi; omega)
lemma dist_le {p : VertexPath X} (hp : p.Unit) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) :
    dist (p.point i) (p.point j)  ≤  (j:ℝ)-i := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hij
  induction k with
  | zero => simp
  | succ k ih =>
    have htri := dist_triangle (p.point i) (p.point (i+k)) (p.point (i+(k+1)))
    have hstep := hp (i+k) (by omega)
    have hrec := ih (by omega) (by omega)
    rw [←Nat.add_assoc] at htri
    simp only [Nat.add_assoc] at htri hstep
    push_cast at *
    linarith
lemma geodesic_of_end {p : VertexPath X} (hp : p.Unit)
    (h : dist p.start p.finish=p.length) : p.Geodesic := by
  have hh : ∀ i ≤ p.length, ∀ j ≤ p.length, i ≤ j →
      dist (p.point i) (p.point j)=(j:ℝ)-i := by
    intro i hi j hj hij
    apply le_antisymm (dist_le hp hij hj)
    have h1:=dist_le hp (Nat.zero_le i) hi
    have h2:=dist_le hp hj (le_refl _)
    have ht:=dist_triangle4 (p.point 0) (p.point i) (p.point j) (p.point p.length)
    change dist (p.point 0) (p.point p.length)=(p.length:ℝ) at h
    simp only [Nat.cast_zero,sub_zero] at h1
    linarith
  intro i hi j hj
  rcases le_total i j with hij|hji
  · rw [hh i hi j hj hij,abs_of_nonpos (by exact_mod_cast sub_nonpos.mpr (show (i:ℝ) ≤ j by exact_mod_cast hij))]; ring
  · rw [dist_comm,hh j hj i hi hji,abs_of_nonneg (by exact_mod_cast sub_nonneg.mpr (show (j:ℝ) ≤ i by exact_mod_cast hji))]
lemma geodesic_unit {p : VertexPath X} (hp : p.Geodesic) : p.Unit := by
  intro i hi
  rw [hp i (by omega) (i+1) (by omega)]
  norm_num
lemma geodesic_quasi {p : VertexPath X} (hp : p.Geodesic) {c : ℝ} (hc : 1 ≤ c) : p.Quasi c := by
  intro i hi j hj
  rw [hp i hi j hj]
  exact le_mul_of_one_le_left (abs_nonneg _) hc

end VertexPath
end

namespace WordPictures.Cochain
variable {A G : Type*} [Group G]
variable (φ : FreeGroup A →* G)
lemma path_cons_succ (g : G) (a : A×Bool) (w : Word A) (i : ℕ) :
    (path φ g (a::w)).point (i+1)=(path φ (g*letter φ a) w).point i := by
  simp only [path,List.take_succ_cons,value_cons,mul_assoc]
lemma path_integral (ω : G→G→ℝ) (g : G) (w : Word A) :
    (path φ g w).integral ω=integral φ ω g w := by
  induction w generalizing g with
  | nil => simp [VertexPath.integral,path]
  | cons a w ih =>
    simp only [VertexPath.integral,path_length,List.length_cons,Finset.sum_range_succ']
    simp only [path_cons_succ,path_point_zero,integral_cons]
    rw [show (∑ i∈Finset.range w.length,
      ω ((path φ (g*letter φ a) w).point i) ((path φ (g*letter φ a) w).point (i+1))) =
      (path φ (g*letter φ a) w).integral ω from rfl,ih]
    exact add_comm _ _

variable (S : Finset G) (hS : Subgroup.closure (S : Set G)=⊤)
variable [MetricSpace G] (hd : ∀ x y : G, dist x y=WordDistance S x y)
include hS hd
omit hS in
lemma path_unit (H : ∀ a, WordLength S (letter φ a) ≤ 1) (g : G) (w : Word A) :
    (path φ g w).Unit := by
  induction w generalizing g with
  | nil => intro i hi; simp at hi
  | cons a w ih =>
    intro i hi
    cases i with
    | zero =>
      rw [path_point_zero,path_cons_succ,path_point_zero]
      rw [hd]
      change (WordLength S (g⁻¹*(g*letter φ a)) : ℝ) ≤ 1
      simp only [inv_mul_cancel_left]
      exact_mod_cast H a
    | succ i =>
      rw [path_cons_succ,path_cons_succ]
      exact ih (g*letter φ a) i (by simpa using hi)

lemma edge_letter (H : ∀ a∈S, ∃ b : A, φ (FreeGroup.of b)=a)
    {x y : G} (h : dist x y ≤ 1) :
    x=y ∨ ∃ a : A×Bool, y=x*letter φ a := by
  rw [hd] at h
  change (WordLength S (x⁻¹*y):ℝ) ≤ 1 at h
  have hn : WordLength S (x⁻¹*y) ≤ 1 := by exact_mod_cast h
  obtain ⟨w,hw,hgood,he⟩ := WordLength.attained S hS (x⁻¹*y)
  have hwlen : w.length ≤ 1 := hw ▸ hn
  cases w with
  | nil => left; exact inv_mul_eq_one.mp (by simpa using he.symm)
  | cons a w =>
    have hw0 : w=[] := List.length_eq_zero_iff.mp (by simpa using hwlen)
    subst w
    have ha:=hgood a (by simp)
    simp only [List.prod_cons,List.prod_nil,mul_one] at he
    right
    rcases ha with ha|ha
    · obtain ⟨b,hb⟩:=H a ha
      refine ⟨(b,true),?_⟩
      have hletter : letter φ (b,true)=a := hb
      rw [hletter,he,mul_inv_cancel_left]
    · obtain ⟨b,hb⟩:=H a⁻¹ ha
      refine ⟨(b,false),?_⟩
      have hletter : letter φ (b,false)=a := by
        have hh:=letter_flip φ b true
        simpa only [Bool.not_true,show letter φ (b,true)=a⁻¹ from hb,inv_inv] using hh
      rw [hletter,he,mul_inv_cancel_left]

lemma represent_path (H : ∀ a∈S, ∃ b : A, φ (FreeGroup.of b)=a)
    (ω : G→G→ℝ) (hω : ∀ x, ω x x=0) (p : VertexPath G) (hp : p.Unit) :
    ∃ w : Word A, w.length ≤ p.length ∧ p.start*value φ w=p.finish ∧
      integral φ ω p.start w=p.integral ω := by
  have aux : ∀ (n : ℕ) (v : ℕ→G), (∀ i<n, dist (v i) (v (i+1)) ≤ 1) →
      ∃ w : Word A, w.length ≤ n ∧ v 0*value φ w=v n ∧
        integral φ ω (v 0) w=∑ i∈Finset.range n, ω (v i) (v (i+1)) := by
    intro n
    induction n with
    | zero => intro v hv; exact ⟨[],by simp,by simp,by simp⟩
    | succ n ih =>
      intro v hv
      obtain ⟨w,hw,hend,hint⟩:=ih v (fun i hi => hv i (by omega))
      rcases edge_letter φ S hS hd H (hv n (by omega)) with he|⟨a,ha⟩
      · refine ⟨w,by omega,hend.trans he,?_⟩
        rw [Finset.sum_range_succ,←hint,←he,hω,add_zero]
      · refine ⟨w++[a],by simp; omega,?_,?_⟩
        · simpa only [value_append,←mul_assoc,hend,letter] using ha.symm
        · rw [integral_append,hend,integral_cons,integral_nil,hint,Finset.sum_range_succ,←ha,
            add_zero]
  exact aux p.length p.point hp

omit hS hd in
omit [MetricSpace G] in
lemma represent_good (H : ∀ a∈S, ∃ b : A, φ (FreeGroup.of b)=a)
    (w : List G) (hw : WordLength.Good S w) :
    ∃ v : Word A, v.length=w.length ∧ value φ v=w.prod := by
  induction w with
  | nil => exact ⟨[],rfl,value_nil φ⟩
  | cons a w ih =>
    obtain ⟨v,hv,hprod⟩:=ih (fun b hb => hw b (List.mem_cons_of_mem a hb))
    have ha:=hw a (by simp)
    have hh : ∃ b : A×Bool, letter φ b=a := by
      rcases ha with ha|ha
      · obtain ⟨b,hb⟩:=H a ha
        exact ⟨(b,true),hb⟩
      · obtain ⟨b,hb⟩:=H a⁻¹ ha
        refine ⟨(b,false),?_⟩
        have hh:=letter_flip φ b true
        simpa only [Bool.not_true,show letter φ (b,true)=a⁻¹ from hb,inv_inv] using hh
    obtain ⟨b,hb⟩:=hh
    exact ⟨b::v,by simp [hv],by simp [hb,hprod]⟩

lemma geodesic_exists (H : ∀ a∈S, ∃ b : A, φ (FreeGroup.of b)=a)
    (Hstep : ∀ a, WordLength S (letter φ a) ≤ 1) (x y : G) :
    ∃ p : VertexPath G, p.start=x ∧ p.finish=y ∧ p.Geodesic := by
  obtain ⟨w,hlen,hgood,hprod⟩:=WordLength.attained S hS (x⁻¹*y)
  obtain ⟨v,hv,hvprod⟩:=represent_good φ S H w hgood
  let p:=path φ x v
  have hp:=path_unit φ S hd Hstep x v
  have hs : p.start=x := path_start φ x v
  have he : p.finish=y := by simp [p,hvprod,hprod]
  refine ⟨p,hs,he,VertexPath.geodesic_of_end hp ?_⟩
  rw [hs,he,hd]
  change (WordLength S (x⁻¹*y):ℝ)=v.length
  rw [hv,hlen]

end WordPictures.Cochain

section
open Finset
open scoped NNReal
namespace VertexPath
variable {X : Type*} [MetricSpace X]
omit [MetricSpace X] in
lemma tentWeight_antisymm (f u : X→ℝ) (x y : X) :
    tentWeight f u x y= -tentWeight f u y x := by unfold tentWeight; ring
omit [MetricSpace X] in
lemma integral_shift (p : VertexPath X) (f u : X→ℝ) (c : ℝ) :
    p.integral (tentWeight (fun x => f x-c) u)=p.integral (tentWeight f u)-
      c*(u p.finish-u p.start) := by
  have he : ∀ i, tentWeight (fun x => f x-c) u (p.point i) (p.point (i+1)) =
      tentWeight f u (p.point i) (p.point (i+1)) - c*(u (p.point (i+1))-u (p.point i)) := by
    intro i; unfold tentWeight; ring
  simp only [integral,he]
  rw [sum_sub_distrib,←mul_sum,Finset.sum_range_sub (fun i => u (p.point i))]
  rfl

lemma quadratic_bound (p : VertexPath X) (hp : p.Unit) (hc : p.finish=p.start)
    (f u : X→ℝ) {K : ℝ≥0} (hf : LipschitzWith 1 f) (hu : LipschitzWith K u) :
    |p.integral (tentWeight f u)| ≤ K*(p.length:ℝ)^2 := by
  have hs:=integral_shift p f u (f p.start)
  rw [hc,sub_self,mul_zero,sub_zero] at hs
  rw [←hs]
  let F := fun x => f x-f p.start
  have hb : ∀ i ≤ p.length, |F (p.point i)| ≤ p.length := by
    intro i hi
    have hh:=hf.dist_le_mul (p.point i) p.start
    have hd:=dist_le hp (Nat.zero_le i) hi
    simp only [NNReal.coe_one,one_mul,Real.dist_eq] at hh
    dsimp only [F]
    simp only [Nat.cast_zero,sub_zero] at hd
    rw [dist_comm] at hd
    have hiR : (i:ℝ) ≤ p.length := by exact_mod_cast hi
    exact hh.trans (by change dist (p.point i) (p.point 0) ≤ _; linarith)
  have he : ∀ i∈range p.length,
      |tentWeight F u (p.point i) (p.point (i+1))| ≤ K*p.length := by
    intro i hi
    have hi:=mem_range.mp hi
    have h1:=hb i (by omega)
    have h2:=hb (i+1) (by omega)
    have h3:=hu.dist_le_mul (p.point (i+1)) (p.point i)
    have h4:=hp i hi
    rw [dist_comm] at h4
    simp only [Real.dist_eq] at h3
    have hu' : |u (p.point (i+1))-u (p.point i)| ≤ K := by
      exact h3.trans (by simpa using mul_le_mul_of_nonneg_left h4 K.coe_nonneg)
    unfold tentWeight
    rw [abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    calc
      _ ≤ ((|F (p.point i)|+|F (p.point (i+1))|)/2)*|u (p.point (i+1))-u (p.point i)| := by
        gcongr; exact abs_add_le _ _
      _ ≤ (((p.length:ℝ)+p.length)/2)*K := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ∑ i∈range p.length, |tentWeight F u (p.point i) (p.point (i+1))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i∈range p.length, (K:ℝ)*p.length := sum_le_sum he
    _ = _ := by simp; ring

end VertexPath
end
section

open scoped NNReal
namespace WordPictures.Cochain
variable {A G : Type*} [Group G] [MetricSpace G]
variable (φ : FreeGroup A →* G) (S : Finset G)
    (hS : Subgroup.closure (S : Set G)=⊤)
    (hd : ∀ x y : G, dist x y=WordDistance S x y)

include hS hd
lemma linear_of_filling {R : Set (Word A)} {C : ℝ} (hC : 0 ≤ C) {L : ℕ}
    (H : ∀ a∈S, ∃ b : A, φ (FreeGroup.of b)=a)
    (Hstep : ∀ a, WordLength S (letter φ a) ≤ 1)
    (hv : ∀ w∈R, value φ w=1) (hL : ∀ w∈R, w.length ≤ L)
    (hfill : ∀ w, value φ w=1 → ∃ a, Homotopy R w [] a ∧ (a:ℝ) ≤ C*w.length) :
    CochainLinear G (3*(L:ℝ)^2*C) := by
  intro p hp hc f u hf hu
  let ω:=VertexPath.tentWeight f u
  have hω : ∀ x y, ω x y= -ω y x := VertexPath.tentWeight_antisymm f u
  have hω0 : ∀x, ω x x=0 := by intro x; simp [ω,VertexPath.tentWeight]
  have hD : ∀ g w, w∈R → |integral φ ω g w| ≤ 3*(L:ℝ)^2 := by
    intro g w hw
    have huPath:=path_unit φ S hd Hstep g w
    have hcPath : (path φ g w).finish=(path φ g w).start := by simp [hv w hw]
    have hb:=VertexPath.quadratic_bound (path φ g w) huPath hcPath f u hf hu
    rw [path_integral,path_length] at hb
    apply hb.trans
    have hle : (w.length:ℝ) ≤ L := by exact_mod_cast hL w hw
    norm_num only [NNReal.coe_ofNat] at *
    gcongr
  obtain ⟨w,hlen,hend,hint⟩:=represent_path φ S hS hd H ω hω0 p hp
  have he : value φ w=1 := by
    apply mul_left_cancel (a:=p.start)
    simpa only [mul_one,hc] using hend
  obtain ⟨a,ha,harea⟩:=hfill w he
  have hb:=homotopy_bound φ ω hω hv (3*(L:ℝ)^2) (by positivity) hD ha p.start
  simp only [integral_nil,sub_zero,hint] at hb
  have hlenR : (w.length:ℝ) ≤ p.length := by exact_mod_cast hlen
  have harea' : (a:ℝ) ≤ C*p.length := harea.trans (mul_le_mul_of_nonneg_left hlenR hC)
  calc
    _ ≤ (a:ℝ)*(3*(L:ℝ)^2) := hb
    _ ≤ (C*p.length)*(3*(L:ℝ)^2) := mul_le_mul_of_nonneg_right harea' (by positivity)
    _ = _ := by ring

end WordPictures.Cochain
end

namespace VertexPath

section
open Finset Set
open scoped NNReal
variable {X : Type*} [MetricSpace X]
lemma quasi_injective {p : VertexPath X} {c : ℝ} (hp : p.Quasi c) :
    Function.Injective (fun i : Fin (p.length+1) => p.point i) := by
  intro i j he
  dsimp only at he
  have hh:=hp i (by omega) j (by omega)
  rw [he,dist_self,mul_zero] at hh
  have hh0:=abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
  apply Fin.ext
  exact_mod_cast sub_eq_zero.mp hh0
lemma quasi_extension {p : VertexPath X} {c : ℝ≥0} (hp : p.Quasi c) :
    ∃ u : X→ℝ, LipschitzWith c u ∧ ∀ i ≤ p.length, u (p.point i)=i := by
  let P : Fin (p.length+1)→X:=fun i => p.point i
  let v : X→ℝ:=fun x => (Function.invFun P x).val
  have hP:=quasi_injective hp
  have hv : ∀ i : Fin (p.length+1), v (P i)=i.val := by
    intro i
    dsimp only [v]
    rw [Function.leftInverse_invFun hP]
  have hvl : LipschitzOnWith c v (Set.range P) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    rw [hv,hv,Real.dist_eq]
    exact hp i (by omega) j (by omega)
  obtain ⟨u,hu,he⟩:=hvl.extend_real
  refine ⟨u,hu,fun i hi => ?_⟩
  exact (he ⟨⟨i,by omega⟩,rfl⟩).symm.trans (hv ⟨i,by omega⟩)

lemma tent_lipschitz (b : X) (R : ℝ) :
    LipschitzWith 1 (fun x => max 0 (R-dist b x)) := by
  apply LipschitzWith.const_max
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,NNReal.coe_one,one_mul]
  rw [show R-dist b x-(R-dist b y)=dist b y-dist b x by ring]
  simpa only [dist_comm] using abs_dist_sub_le y x b

lemma nearest (p : VertexPath X) (x : X) :
    ∃ i ≤ p.length, ∀ j ≤ p.length, dist x (p.point i) ≤ dist x (p.point j) := by
  obtain ⟨i,hi,hmin⟩:=Finset.exists_min_image (Finset.range (p.length+1))
    (fun i => dist x (p.point i)) (by simp)
  exact ⟨i,by simpa using hi,fun j hj => hmin j (by simpa using hj)⟩

lemma maximum_nearest (p q : VertexPath X)
    (hint : ∀ x y : X, ∃ n : ℕ, dist x y=n) :
    ∃ k ≤ p.length, ∃ R : ℕ,
      (∀ j ≤ q.length, (R:ℝ) ≤ dist (p.point k) (q.point j)) ∧
      (∀ i ≤ p.length, ∃ j ≤ q.length, dist (p.point i) (q.point j) ≤ R) := by
  choose j hj hmin using fun i : ℕ => nearest q (p.point i)
  obtain ⟨k,hk,hmax⟩:=Finset.exists_max_image (Finset.range (p.length+1))
    (fun i => dist (p.point i) (q.point (j i))) (by simp)
  obtain ⟨R,hR⟩:=hint (p.point k) (q.point (j k))
  refine ⟨k,by simpa using hk,R,?_,?_⟩
  · intro t ht
    rw [←hR]
    exact hmin k t ht
  · intro i hi
    exact ⟨j i,hj i,hR ▸ hmax i (by simpa using hi)⟩

lemma geodesic_length {p : VertexPath X} (hp : p.Geodesic) :
    dist p.start p.finish=p.length := by simpa [start,finish] using hp 0 (by omega) p.length (le_refl _)
lemma geodesic_sub {p : VertexPath X} (hp : p.Geodesic) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) :
    (p.sub i j).Geodesic := by
  intro k hk l hl
  change dist (p.point (i+k)) (p.point (i+l))=|(k:ℝ)-l|
  rw [hp _ (by change k ≤ j-i at hk; omega) _ (by change l ≤ j-i at hl; omega)]
  push_cast
  congr 1
  ring

end

section
open Finset
variable {X : Type*} [MetricSpace X]
omit [MetricSpace X] in
lemma integral_sub_eq (p : VertexPath X) (ω : X→X→ℝ) (s t : ℕ) :
    (p.sub s t).integral ω=∑ i∈Ico s t, ω (p.point i) (p.point (i+1)) := by
  rw [sum_Ico_eq_sum_range]
  simp only [integral,sub_length,sub_at,Nat.add_assoc]
omit [MetricSpace X] in
lemma integral_sub_mono (p : VertexPath X) (ω : X→X→ℝ) {a b s t : ℕ}
    (hsa : s ≤ a) (hbt : b ≤ t)
    (hω : ∀ i∈Ico s t, 0 ≤ ω (p.point i) (p.point (i+1))) :
    (p.sub a b).integral ω ≤ (p.sub s t).integral ω := by
  rw [integral_sub_eq,integral_sub_eq]
  apply sum_le_sum_of_subset_of_nonneg
  · intro i hi
    simp only [mem_Ico] at *
    omega
  · intro i hi _
    exact hω i hi
omit [MetricSpace X] in
lemma integral_tent_zero (p : VertexPath X) (f u : X→ℝ)
    (hf : ∀ i ≤ p.length, f (p.point i)=0) : p.integral (tentWeight f u)=0 := by
  apply sum_eq_zero
  intro i hi
  have hi:=mem_range.mp hi
  simp [tentWeight,hf i (by omega),hf (i+1) (by omega)]
lemma arithmetic_tent_sum (n : ℕ) :
    (∑ i∈range n, ((n:ℝ)-i-1/2))=(n:ℝ)^2/2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have he : ∀ i, ((n+1:ℕ):ℝ)-i-1/2=((n:ℝ)-i-1/2)+1 := by intro i; push_cast; ring
    simp only [he,sum_add_distrib,sum_const,card_range,nsmul_eq_mul,mul_one,ih]
    push_cast
    ring

/-- A tent centered on a long unit path sees a quadratic amount of integral.
The coordinate function is the actual Lipschitz index extension. -/
lemma integral_tent_lower (p : VertexPath X) (hp : p.Unit) (u : X→ℝ)
    (hu : ∀ i ≤ p.length, u (p.point i)=i) {R k s t : ℕ}
    (hs : s ≤ k) (ht : k+R ≤ t) (htp : t ≤ p.length) :
    (R:ℝ)^2/2 ≤ (p.sub s t).integral (tentWeight
      (fun x => max 0 ((R:ℝ)-dist (p.point k) x)) u) := by
  let f:=fun x => max 0 ((R:ℝ)-dist (p.point k) x)
  have hn : ∀ i∈Ico s t, 0 ≤ tentWeight f u (p.point i) (p.point (i+1)) := by
    intro i hi
    have hi:=mem_Ico.mp hi
    unfold tentWeight
    rw [hu i (by omega),hu (i+1) (by omega)]
    have he : ((i+1:ℕ):ℝ)-(i:ℝ)=1 := by simp
    rw [he,mul_one]
    exact div_nonneg (add_nonneg (le_max_left _ _) (le_max_left _ _)) (by norm_num)
  have hb : ∀ i ≤ R, (R:ℝ)-i ≤ f (p.point (k+i)) := by
    intro i hi
    have hd:=dist_le hp (show k ≤ k+i by omega) (show k+i ≤ p.length by omega)
    have hm:=le_max_right (0:ℝ) ((R:ℝ)-dist (p.point k) (p.point (k+i)))
    dsimp only [f]
    push_cast at hd
    linarith
  have hsmall : (R:ℝ)^2/2 ≤ (p.sub k (k+R)).integral (tentWeight f u) := by
    rw [integral,sub_length,Nat.add_sub_cancel_left,←arithmetic_tent_sum R]
    apply sum_le_sum
    intro i hi
    have hi:=mem_range.mp hi
    simp only [sub_at,tentWeight]
    rw [hu (k+i) (by omega),hu (k+(i+1)) (by omega)]
    have h1:=hb i (by omega)
    have h2:=hb (i+1) (by omega)
    push_cast at *
    nlinarith
  exact hsmall.trans (integral_sub_mono p (tentWeight f u) hs ht hn)

end

section
variable {X : Type*} [MetricSpace X]
omit [MetricSpace X] in
lemma between_start (p : VertexPath X) (i j : ℕ) : (p.between i j).start=p.point i := by
  unfold between
  split_ifs with h
  · exact sub_start p i j
  · rw [reverse_start,sub_finish p (by omega)]
omit [MetricSpace X] in
lemma between_finish (p : VertexPath X) (i j : ℕ) : (p.between i j).finish=p.point j := by
  unfold between
  split_ifs with h
  · exact sub_finish p h
  · rw [reverse_finish,sub_start]
lemma between_unit {p : VertexPath X} (hp : p.Unit) {i j : ℕ}
    (hi : i ≤ p.length) (hj : j ≤ p.length) : (p.between i j).Unit := by
  unfold between
  split_ifs
  · exact unit_sub hp hj
  · exact unit_reverse (unit_sub hp hi)
omit [MetricSpace X] in
lemma between_length_real (p : VertexPath X) (i j : ℕ) :
    ((p.between i j).length:ℝ)=|(i:ℝ)-j| := by
  unfold between
  split_ifs with h
  · rw [sub_length,Nat.cast_sub h,abs_of_nonpos (by exact_mod_cast sub_nonpos.mpr (show (i:ℝ) ≤ j by exact_mod_cast h))]
    ring
  · rw [reverse_length,sub_length,Nat.cast_sub (by omega),abs_of_nonneg (by exact_mod_cast sub_nonneg.mpr (show (j:ℝ) ≤ i by exact_mod_cast (show j ≤ i by omega))) ]
lemma between_length_le {p : VertexPath X} {c : ℝ} (hp : p.Quasi c) {i j : ℕ}
    (hi : i ≤ p.length) (hj : j ≤ p.length) :
    ((p.between i j).length:ℝ) ≤ c*dist (p.point i) (p.point j) := by
  rw [between_length_real]
  exact hp i hi j hj
omit [MetricSpace X] in
lemma between_point (p : VertexPath X) {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    {k : ℕ} (hk : k ≤ (p.between i j).length) :
    ∃ l ≤ p.length, (p.between i j).point k=p.point l := by
  unfold between at *
  split_ifs at * with h
  · exact ⟨i+k,by change k ≤ j-i at hk; omega,rfl⟩
  · exact ⟨j+(i-j-k),by change k ≤ i-j at hk; omega,rfl⟩

/-- A connector of length at most R stays outside the R-tent whenever its
initial vertex is 2R away, or is already on the comparison path. -/
lemma outside_connector
    (hgeo : ∀ x y : X, ∃ c : VertexPath X, c.start=x ∧ c.finish=y ∧ c.Geodesic)
    (q : VertexPath X) (b x : X) (R : ℝ) (hR : 0 ≤ R)
    (hq : ∀ j ≤ q.length, R ≤ dist b (q.point j))
    (hnear : ∃ j ≤ q.length, dist x (q.point j) ≤ R)
    (hfar : (∃ j ≤ q.length, x=q.point j) ∨ 2*R ≤ dist b x) :
    ∃ j ≤ q.length, ∃ c : VertexPath X,
      c.start=x ∧ c.finish=q.point j ∧ c.Unit ∧ (c.length:ℝ) ≤ R ∧
        ∀ i ≤ c.length, R ≤ dist b (c.point i) := by
  rcases hfar with ⟨j,hj,hx⟩|hfar
  · refine ⟨j,hj,⟨0,fun _ => x⟩,rfl,hx,?_,?_,?_⟩
    · intro i hi; exact (Nat.not_lt_zero i hi).elim
    · simpa using hR
    · intro i hi
      simpa only [hx] using hq j hj
  · obtain ⟨j,hj,hjR⟩:=hnear
    obtain ⟨c,hs,he,hc⟩:=hgeo x (q.point j)
    have hlen : (c.length:ℝ) ≤ R := by rw [←geodesic_length hc,hs,he]; exact hjR
    refine ⟨j,hj,c,hs,he,geodesic_unit hc,hlen,?_⟩
    intro i hi
    have hd:=dist_le (geodesic_unit hc) (Nat.zero_le i) hi
    have hiR : (i:ℝ) ≤ c.length := by exact_mod_cast hi
    have ht:=dist_triangle b (c.point i) x
    change c.point 0=x at hs
    simp only [Nat.cast_zero,sub_zero,hs] at hd
    rw [dist_comm (c.point i) x] at ht
    linarith

end

variable {X : Type*} [MetricSpace X]
lemma end_dist_le {p : VertexPath X} (hp : p.Unit) : dist p.start p.finish ≤ p.length := by
  simpa [start,finish] using dist_le hp (Nat.zero_le p.length) (le_refl _)

/-- Localized-loop proof of uniform Morse stability. The loop has length at
most 56R and its tent integral at least R²/2. -/
lemma cochain_morse_max {K : ℝ} (hK : 0 ≤ K) (hco : CochainLinear X K)
    (hgeo : ∀ x y : X, ∃ c : VertexPath X, c.start=x ∧ c.finish=y ∧ c.Geodesic)
    (p q : VertexPath X) (hp : p.Unit) (hqp : p.Quasi 3) (hq : q.Unit) (hqq : q.Quasi 3)
    (hstart : p.start=q.start) (hfinish : p.finish=q.finish)
    {k R : ℕ} (hk : k ≤ p.length)
    (hfarq : ∀ j ≤ q.length, (R:ℝ) ≤ dist (p.point k) (q.point j))
    (hnear : ∀ i ≤ p.length, ∃ j ≤ q.length, dist (p.point i) (q.point j) ≤ R) :
    (R:ℝ) ≤ 112*K := by
  let s:=k-6*R
  let t:=min p.length (k+6*R)
  have hs : s ≤ k := Nat.sub_le _ _
  have hslen : s ≤ p.length := hs.trans hk
  have htlen : t ≤ p.length := min_le_left _ _
  have hkt : k ≤ t := le_min hk (by omega)
  have hst : s ≤ t := hs.trans hkt
  have hkR : k+R ≤ p.length := by
    have hh:=hfarq q.length (le_refl _)
    have hd:=dist_le hp hk (le_refl _)
    change p.point p.length=q.point q.length at hfinish
    rw [←hfinish] at hh
    have hr : (k:ℝ)+R ≤ p.length := by linarith
    exact_mod_cast hr
  have hRt : k+R ≤ t := le_min hkR (by omega)
  have hslength : t-s ≤ 12*R := by dsimp only [s,t]; omega
  have hsfar : (∃ j ≤ q.length, p.point s=q.point j) ∨
      2*(R:ℝ) ≤ dist (p.point k) (p.point s) := by
    by_cases hs0 : s=0
    · left
      exact ⟨0,Nat.zero_le _,by simpa only [hs0,start] using hstart⟩
    · right
      have he : k=s+6*R := by dsimp only [s] at *; omega
      have her : (k:ℝ)=(s:ℝ)+6*R := by exact_mod_cast he
      have hh:=hqp k hk s hslen
      have ha:=le_abs_self ((k:ℝ)-s)
      linarith
  have htfar : (∃ j ≤ q.length, p.point t=q.point j) ∨
      2*(R:ℝ) ≤ dist (p.point k) (p.point t) := by
    by_cases hte : t=p.length
    · left
      exact ⟨q.length,le_refl _,by simpa only [hte,finish] using hfinish⟩
    · right
      have he : t=k+6*R := by
        change min p.length (k+6*R)=k+6*R
        by_cases hh : p.length ≤ k+6*R
        · exact False.elim (hte (min_eq_left hh))
        · exact min_eq_right (le_of_not_ge hh)
      have her : (t:ℝ)=(k:ℝ)+6*R := by exact_mod_cast he
      have hh:=hqp k hk t htlen
      have ha:=neg_le_abs ((k:ℝ)-t)
      linarith
  obtain ⟨js,hjs,cs,hcss,hcse,hcs,hcslen,hcsfar⟩:=
    outside_connector hgeo q (p.point k) (p.point s) R (Nat.cast_nonneg R)
      hfarq (hnear s hslen) hsfar
  obtain ⟨jt,hjt,ct,hcts,hcte,hct,hctlen,hctfar⟩:=
    outside_connector hgeo q (p.point k) (p.point t) R (Nat.cast_nonneg R)
      hfarq (hnear t htlen) htfar
  let a:=p.sub s t
  let b:=q.between jt js
  have haUnit : a.Unit:=unit_sub hp htlen
  have hbUnit : b.Unit:=between_unit hq hjt hjs
  have has : a.start=p.point s:=sub_start p s t
  have hae : a.finish=p.point t:=sub_finish p hst
  have hbs : b.start=q.point jt:=between_start q jt js
  have hbe : b.finish=q.point js:=between_finish q jt js
  have h1 : a.finish=ct.start:=hae.trans hcts.symm
  have h2 : (a.append ct).finish=b.start :=
    (append_finish a ct h1).trans (hcte.trans hbs.symm)
  have h3 : ((a.append ct).append b).finish=cs.reverse.start := by
    rw [append_finish _ _ h2,hbe,reverse_start,hcse]
  let loop:=((a.append ct).append b).append cs.reverse
  have hloop : loop.Unit:=unit_append (unit_append (unit_append haUnit hct h1) hbUnit h2)
    (unit_reverse hcs) h3
  have hclosed : loop.finish=loop.start := by
    rw [show loop.finish=cs.reverse.finish from append_finish _ _ h3,reverse_finish,hcss]
    simp only [loop,append_start,has]
  have haLen : (a.length:ℝ) ≤ 12*R := by exact_mod_cast hslength
  have hbLen : (b.length:ℝ) ≤ 3*((ct.length:ℝ)+a.length+cs.length) := by
    have hd:=dist_triangle4 (q.point jt) (p.point t) (p.point s) (q.point js)
    have hdct:=end_dist_le hct
    have hda:=end_dist_le haUnit
    have hdcs:=end_dist_le hcs
    rw [hcts,hcte,dist_comm] at hdct
    rw [has,hae,dist_comm] at hda
    rw [hcss,hcse] at hdcs
    have hh:=between_length_le hqq hjt hjs
    change (b.length:ℝ) ≤ _ at hh
    linarith
  have hlen : (loop.length:ℝ) ≤ 56*R := by
    simp only [loop,append_length,reverse_length,Nat.cast_add]
    linarith
  obtain ⟨u,hu,huindex⟩:=quasi_extension (c:=(3:NNReal)) hqp
  let f:=fun x => max 0 ((R:ℝ)-dist (p.point k) x)
  let ω:=tentWeight f u
  have hf : LipschitzWith 1 f:=tent_lipschitz _ _
  have hcs0 : cs.integral ω=0 := integral_tent_zero cs f u (fun i hi =>
    max_eq_left (sub_nonpos.mpr (hcsfar i hi)))
  have hct0 : ct.integral ω=0 := integral_tent_zero ct f u (fun i hi =>
    max_eq_left (sub_nonpos.mpr (hctfar i hi)))
  have hb0 : b.integral ω=0 := by
    apply integral_tent_zero b f u
    intro i hi
    obtain ⟨j,hj,hij⟩:=between_point q hjt hjs hi
    change max 0 ((R:ℝ)-dist (p.point k) (b.point i))=0
    rw [hij]
    exact max_eq_left (sub_nonpos.mpr (hfarq j hj))
  have hint : loop.integral ω=a.integral ω := by
    rw [show loop.integral ω=(((a.append ct).append b).integral ω+cs.reverse.integral ω)
      from integral_append _ _ h3 ω,
      integral_append _ _ h2,integral_append _ _ h1,
      integral_reverse cs ω (tentWeight_antisymm f u),hcs0,hct0,hb0]
    ring
  have hlo:=integral_tent_lower p hp u huindex hs hRt htlen
  change (R:ℝ)^2/2 ≤ a.integral ω at hlo
  have hupper:=hco loop hloop hclosed f u hf hu
  change |loop.integral ω| ≤ K*loop.length at hupper
  rw [hint] at hupper
  have hupp : a.integral ω ≤ K*(56*R) :=
    (le_abs_self _).trans (hupper.trans (mul_le_mul_of_nonneg_left hlen hK))
  have hR : 0 ≤ (R:ℝ):=Nat.cast_nonneg _
  by_cases hR0 : R=0
  · simp only [hR0,Nat.cast_zero]; positivity
  · have hRp : 0 < (R:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hR0
    nlinarith

lemma cochain_morse {K : ℝ} (hK : 0 ≤ K) (hco : CochainLinear X K)
    (hgeo : ∀ x y : X, ∃ c : VertexPath X, c.start=x ∧ c.finish=y ∧ c.Geodesic)
    (hint : ∀ x y : X, ∃ n : ℕ, dist x y=n)
    (p q : VertexPath X) (hp : p.Unit) (hqp : p.Quasi 3) (hq : q.Unit) (hqq : q.Quasi 3)
    (hstart : p.start=q.start) (hfinish : p.finish=q.finish) :
    ∀ i ≤ p.length, ∃ j ≤ q.length, dist (p.point i) (q.point j) ≤ 112*K := by
  obtain ⟨k,hk,R,hfar,hnear⟩:=maximum_nearest p q hint
  have hb:=cochain_morse_max hK hco hgeo p q hp hqp hq hqq hstart hfinish hk hfar hnear
  intro i hi
  obtain ⟨j,hj,hij⟩:=hnear i hi
  exact ⟨j,hj,hij.trans hb⟩

lemma geodesic_reverse {p : VertexPath X} (hp : p.Geodesic) : p.reverse.Geodesic := by
  apply geodesic_of_end (unit_reverse (geodesic_unit hp))
  rw [reverse_start,reverse_finish,dist_comm,geodesic_length hp,reverse_length]

/-- Joining at a nearest vertex produces a 3-quasigeodesic, with no additive
error. This avoids any planar-diagram or simple-boundary assumption. -/
lemma nearest_append_quasi {p q : VertexPath X} (hp : p.Geodesic) (hq : q.Geodesic)
    (he : p.finish=q.start)
    (hnear : ∀ i ≤ p.length, dist p.finish q.finish ≤ dist (p.point i) q.finish) :
    (p.append q).Quasi 3 := by
  have cross : ∀ i ≤ p.length, ∀ j ≤ q.length,
      (p.length:ℝ)-i+j ≤ 3*dist (p.point i) (q.point j) := by
    intro i hi j hj
    have h1:=dist_triangle (p.point i) (q.point j) q.finish
    have h2:=dist_triangle (p.point i) (q.point j) q.start
    have hn:=hnear i hi
    have hqp : dist q.start q.finish=q.length := geodesic_length hq
    have hjR : (j:ℝ) ≤ q.length := by exact_mod_cast hj
    have hiR : (i:ℝ) ≤ p.length := by exact_mod_cast hi
    have hqj : dist (q.point j) q.finish=(q.length:ℝ)-j := by
      rw [finish,hq j hj q.length (le_refl _),abs_of_nonpos (by linarith)]; ring
    have hjq : dist (q.point j) q.start=(j:ℝ) := by
      rw [start,hq j hj 0 (Nat.zero_le _),Nat.cast_zero,sub_zero,abs_of_nonneg (Nat.cast_nonneg _)]
    have hpi : dist (p.point i) q.start=(p.length:ℝ)-i := by
      rw [←he,finish,hp i hi p.length (le_refl _),abs_of_nonpos (by linarith)]; ring
    rw [he] at hn
    rw [hqp] at hn
    rw [hqj] at h1
    rw [hpi,hjq] at h2
    linarith
  have ordered : ∀ i ≤ (p.append q).length, ∀ j ≤ (p.append q).length, i ≤ j →
      (j:ℝ)-i ≤ 3*dist ((p.append q).point i) ((p.append q).point j) := by
    intro i hi j hj hij
    by_cases hip : i ≤ p.length
    · rw [append_at_left p q hip]
      by_cases hjp : j ≤ p.length
      · rw [append_at_left p q hjp,hp i hip j hjp,
          abs_of_nonpos (by exact_mod_cast sub_nonpos.mpr (show (i:ℝ) ≤ j by exact_mod_cast hij))]
        have : (i:ℝ) ≤ j := by exact_mod_cast hij
        linarith
      · obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le (show p.length ≤ j by omega)
        rw [append_at_right p q he]
        have hh:=cross i hip k (by change p.length+k ≤ p.length+q.length at hj; omega)
        push_cast
        linarith
    · obtain ⟨s,rfl⟩:=Nat.exists_eq_add_of_le (show p.length ≤ i by omega)
      obtain ⟨t,rfl⟩:=Nat.exists_eq_add_of_le (show p.length ≤ j by omega)
      have hs : s ≤ q.length := by change p.length+s ≤ p.length+q.length at hi; omega
      have ht : t ≤ q.length := by change p.length+t ≤ p.length+q.length at hj; omega
      rw [append_at_right p q he,append_at_right p q he,hq s hs t ht,
        abs_of_nonpos (by exact_mod_cast sub_nonpos.mpr (show (s:ℝ) ≤ t by exact_mod_cast (show s ≤ t by omega)))]
      push_cast
      have : (s:ℝ) ≤ t := by exact_mod_cast (show s ≤ t by omega)
      linarith
  intro i hi j hj
  rcases le_total i j with hij|hji
  · rw [abs_of_nonpos (by exact_mod_cast sub_nonpos.mpr (show (i:ℝ) ≤ j by exact_mod_cast hij))]
    linarith [ordered i hi j hj hij]
  · rw [abs_of_nonneg (by exact_mod_cast sub_nonneg.mpr (show (j:ℝ) ≤ i by exact_mod_cast hji)),dist_comm]
    exact ordered j hj i hi hji

lemma cochain_thin {K : ℝ} (hK : 0 ≤ K) (hco : CochainLinear X K)
    (hgeo : ∀ x y : X, ∃ c : VertexPath X, c.start=x ∧ c.finish=y ∧ c.Geodesic)
    (hint : ∀ x y : X, ∃ n : ℕ, dist x y=n) : ThinTriangles X (112*K) := by
  intro p q r hp hq hr hps hpe hqe i hi
  obtain ⟨k,hk,hmin⟩:=nearest p q.finish
  obtain ⟨s,hss,hse,hs⟩:=hgeo (p.point k) q.finish
  by_cases hik : i ≤ k
  · let a:=p.sub 0 k
    have ha : a.Geodesic:=geodesic_sub hp (Nat.zero_le _) hk
    have hae : a.finish=s.start := (sub_finish p (Nat.zero_le k)).trans hss.symm
    have hnear : ∀ j ≤ a.length, dist a.finish s.finish ≤ dist (a.point j) s.finish := by
      intro j hj
      rw [sub_finish p (Nat.zero_le k),hse,dist_comm (p.point k),dist_comm (a.point j)]
      simpa only [a,sub_at,Nat.zero_add] using hmin j (by change j ≤ k-0 at hj; omega)
    have hstart : (a.append s).start=q.start := by
      rw [append_start]; exact hps
    have hfinish : (a.append s).finish=q.finish := (append_finish a s hae).trans hse
    obtain ⟨j,hj,hij⟩:=cochain_morse hK hco hgeo hint (a.append s) q
      (unit_append (geodesic_unit ha) (geodesic_unit hs) hae)
      (nearest_append_quasi ha hs hae hnear) (geodesic_unit hq) (geodesic_quasi hq (by norm_num))
      hstart hfinish i (by change i ≤ (k-0)+s.length; omega)
    left
    refine ⟨j,hj,?_⟩
    simpa only [append_at_left a s (show i ≤ a.length by exact hik),a,sub_at,Nat.zero_add] using hij
  · let a:=(p.sub k p.length).reverse
    have ha : a.Geodesic:=geodesic_reverse (geodesic_sub hp hk (le_refl _))
    have hae : a.finish=s.start := by simp only [a,reverse_finish,sub_start]; exact hss.symm
    have hnear : ∀ j ≤ a.length, dist a.finish s.finish ≤ dist (a.point j) s.finish := by
      intro j hj
      simp only [a,reverse_finish,sub_start,reverse_at,sub_at,sub_length,hse]
      rw [dist_comm (p.point k),dist_comm (p.point _)]
      exact hmin _ (by omega)
    have hstart : (a.append s).start=r.start := by
      rw [append_start,show a.start=p.finish by
        exact (reverse_start (p.sub k p.length)).trans (sub_finish p hk)]
      exact hpe
    have hfinish : (a.append s).finish=r.finish := (append_finish a s hae).trans (hse.trans hqe)
    let j:=p.length-i
    have hj : j ≤ a.length := by change p.length-i ≤ p.length-k; omega
    obtain ⟨l,hl,hil⟩:=cochain_morse hK hco hgeo hint (a.append s) r
      (unit_append (geodesic_unit ha) (geodesic_unit hs) hae)
      (nearest_append_quasi ha hs hae hnear) (geodesic_unit hr) (geodesic_quasi hr (by norm_num))
      hstart hfinish j (hj.trans (Nat.le_add_right _ _))
    right
    refine ⟨l,hl,?_⟩
    rw [append_at_left a s hj] at hil
    simpa only [a,reverse_at,sub_at,sub_length,j,show k+(p.length-k-(p.length-i))=i by omega] using hil

lemma product_nonneg (o x y : X) : 0 ≤ product o x y := by
  have h:=dist_triangle x o y
  rw [dist_comm x o] at h
  unfold product; linarith
lemma product_le_left (o x y : X) : product o x y ≤ dist o x := by
  have h:=dist_triangle o x y
  unfold product; linarith
lemma product_le_right (o x y : X) : product o x y ≤ dist o y := by
  have h:=dist_triangle o y x
  rw [dist_comm y x] at h
  unfold product; linarith
lemma geodesic_start_dist {p : VertexPath X} (hp : p.Geodesic) {i : ℕ} (hi : i ≤ p.length) :
    dist p.start (p.point i)=i := by
  rw [start,hp 0 (Nat.zero_le _) i hi]
  simp
lemma geodesic_finish_dist {p : VertexPath X} (hp : p.Geodesic) {i : ℕ} (hi : i ≤ p.length) :
    dist (p.point i) p.finish=(p.length:ℝ)-i := by
  rw [finish,hp i hi p.length (le_refl _),abs_of_nonpos (by exact_mod_cast sub_nonpos.mpr (show (i:ℝ) ≤ p.length by exact_mod_cast hi))]
  ring

lemma thin_initial_close {D : ℝ} (hD : 0 ≤ D) (hthin : ThinTriangles X D)
    (hgeo : ∀ x y : X, ∃ c : VertexPath X, c.start=x ∧ c.finish=y ∧ c.Geodesic)
    {p q : VertexPath X} (hp : p.Geodesic) (hq : q.Geodesic) (he : p.start=q.start)
    {i : ℕ} (hi : (i:ℝ)+D < product p.start p.finish q.finish) :
    i ≤ p.length ∧ i ≤ q.length ∧ dist (p.point i) (q.point i) ≤ 2*D := by
  have hip : i ≤ p.length := by
    have hh:=product_le_left p.start p.finish q.finish
    rw [geodesic_length hp] at hh
    have h : (i:ℝ) ≤ p.length := by linarith
    exact_mod_cast h
  have hiq : i ≤ q.length := by
    have hh:=product_le_right p.start p.finish q.finish
    rw [he,geodesic_length hq] at hh
    have hi' := hi
    rw [he] at hi'
    have h : (i:ℝ) ≤ q.length := by linarith
    exact_mod_cast h
  refine ⟨hip,hiq,?_⟩
  obtain ⟨r,hrs,hre,hr⟩:=hgeo p.finish q.finish
  rcases hthin p q r hp hq hr he hrs.symm hre.symm i hip with ⟨j,hj,hxy⟩|⟨j,hj,hxy⟩
  · have hdist : |(i:ℝ)-j| ≤ D := by
      have hh:=abs_dist_sub_le (p.point i) (q.point j) p.start
      rw [dist_comm (p.point i),geodesic_start_dist hp hip,
        dist_comm (q.point j),he,geodesic_start_dist hq hj] at hh
      exact hh.trans hxy
    have ht:=dist_triangle (p.point i) (q.point j) (q.point i)
    rw [hq j hj i hiq,abs_sub_comm] at ht
    linarith
  · have h1:=dist_triangle p.start (p.point i) (r.point j)
    have h2:=dist_triangle p.start (r.point j) q.finish
    have h3:=dist_triangle (p.point i) (r.point j) p.finish
    have hpstart:=geodesic_start_dist hp hip
    have hpend:=geodesic_finish_dist hp hip
    have hrstart:=geodesic_start_dist hr hj
    have hrend:=geodesic_finish_dist hr hj
    have hpLen:=geodesic_length hp
    have hrLen:=geodesic_length hr
    rw [hrs,dist_comm] at hrstart
    rw [hre] at hrend
    rw [hrs,hre] at hrLen
    unfold product at hi
    linarith

lemma thin_product {D : ℝ} (hD : 0 ≤ D) (hthin : ThinTriangles X D)
    (hgeo : ∀ x y : X, ∃ c : VertexPath X, c.start=x ∧ c.finish=y ∧ c.Geodesic)
    (o a b c : X) :
    min (product o a b) (product o b c) ≤ product o a c+(3*D+2) := by
  let R:=min (product o a b) (product o b c)
  by_cases hsmall : R ≤ D+1
  · have hn:=product_nonneg o a c
    change R ≤ _
    linarith
  · have hpos : 0 ≤ R-D-1 := by linarith
    let i:=⌊R-D-1⌋₊
    have hile : (i:ℝ) ≤ R-D-1 := Nat.floor_le hpos
    have hir : R-D-1 < (i:ℝ)+1 := Nat.lt_floor_add_one _
    obtain ⟨p,hps,hpe,hp⟩:=hgeo o a
    obtain ⟨q,hqs,hqe,hq⟩:=hgeo o b
    obtain ⟨r,hrs,hre,hr⟩:=hgeo o c
    have hab : (i:ℝ)+D < product p.start p.finish q.finish := by
      rw [hps,hpe,hqe]
      have hh:=min_le_left (product o a b) (product o b c)
      change R ≤ _ at hh
      linarith
    have hbc : (i:ℝ)+D < product q.start q.finish r.finish := by
      rw [hqs,hqe,hre]
      have hh:=min_le_right (product o a b) (product o b c)
      change R ≤ _ at hh
      linarith
    obtain ⟨hip,hiq,hpq⟩:=thin_initial_close hD hthin hgeo hp hq (hps.trans hqs.symm) hab
    obtain ⟨_,hir',hqr⟩:=thin_initial_close hD hthin hgeo hq hr (hqs.trans hrs.symm) hbc
    have hpr:=dist_triangle (p.point i) (q.point i) (r.point i)
    have ht:=dist_triangle4 a (p.point i) (r.point i) c
    have hpa:=geodesic_finish_dist hp hip
    have hrc:=geodesic_finish_dist hr hir'
    have hpLen:=geodesic_length hp
    have hrLen:=geodesic_length hr
    rw [hpe,dist_comm] at hpa
    rw [hre] at hrc
    rw [hps,hpe] at hpLen
    rw [hrs,hre] at hrLen
    change R ≤ _
    unfold product
    linarith

lemma thin_fourpoint {D : ℝ} (hD : 0 ≤ D) (hthin : ThinTriangles X D)
    (hgeo : ∀ x y : X, ∃ c : VertexPath X, c.start=x ∧ c.finish=y ∧ c.Geodesic)
    (a b c d : X) :
    dist a c+dist b d ≤ max (dist a b+dist c d) (dist a d+dist b c)+2*(3*D+2) := by
  have hh:=thin_product hD hthin hgeo a b c d
  unfold product at hh
  rcases le_total ((dist a b+dist a c-dist b c)/2) ((dist a c+dist a d-dist c d)/2) with h|h
  · rw [min_eq_left h] at hh
    have hmax:=le_max_right (dist a b+dist c d) (dist a d+dist b c)
    linarith
  · rw [min_eq_right h] at hh
    have hmax:=le_max_left (dist a b+dist c d) (dist a d+dist b c)
    linarith

end VertexPath

/-! A quantitative proof that linear word-homotopy filling bounds imply
four-point hyperbolicity. -/
namespace WordPictures
open Cochain
variable {A G : Type*} [Group G] [Finite A]
lemma wordHyperbolic_of_linear (φ : FreeGroup A →* G) (hφ : Function.Surjective φ)
    {R : Set (Word A)} {C : ℝ} (hC : 0 ≤ C) {L : ℕ}
    (hv : ∀ w∈R, φ (FreeGroup.mk w)=1) (hL : ∀ w∈R, w.length ≤ L)
    (hfill : ∀ w, φ (FreeGroup.mk w)=1 → ∃ a, Homotopy R w [] a ∧ (a:ℝ) ≤ C*w.length) :
    WordHyperbolic G := by
  classical
  let := Fintype.ofFinite A
  let S : Finset G:=Finset.univ.image (fun a : A => φ (FreeGroup.of a))
  have hSrange : (S:Set G)=Set.range (fun a : A => φ (FreeGroup.of a)) := by
    simp only [S,Finset.coe_image,Finset.coe_univ,Set.image_univ]
  have hS : Subgroup.closure (S:Set G)=⊤ := by
    rw [hSrange,←FreeGroup.lift_surjective_iff_closure_range_eq_top]
    have he : FreeGroup.lift (fun a : A => φ (FreeGroup.of a))=φ := by
      ext a; simp
    rw [he]
    exact hφ
  have H : ∀ a∈S, ∃ b : A, φ (FreeGroup.of b)=a := by
    intro a ha
    exact Finset.mem_image.mp ha |>.imp (fun b hb => hb.2)
  have Hstep : ∀ a : A×Bool, WordLength S (letter φ a) ≤ 1 := by
    rintro ⟨a,b⟩
    have ha : φ (FreeGroup.of a)∈S := Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
    have hh : letter φ (a,b)∈S ∨ (letter φ (a,b))⁻¹∈S := by
      cases b
      · right
        have he:=letter_flip φ a true
        rw [Bool.not_true] at he
        rw [he,inv_inv]
        exact ha
      · exact Or.inl ha
    simpa only [List.prod_singleton,List.length_singleton] using
      WordLength.le_length S (w:=[letter φ (a,b)]) (by
        intro g hg; simpa only [List.mem_singleton.mp hg] using hh)
  let := WordDistance.metric S hS
  have hd : ∀ x y : G, dist x y=WordDistance S x y := fun _ _ => rfl
  have hgeo:=geodesic_exists φ S hS hd H Hstep
  have hint : ∀ x y : G, ∃ n : ℕ, dist x y=n := fun x y => ⟨WordLength S (x⁻¹*y),rfl⟩
  have hco:=linear_of_filling φ S hS hd hC H Hstep hv hL hfill
  let K : ℝ:=3*(L:ℝ)^2*C
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hthin:=VertexPath.cochain_thin hK hco hgeo hint
  refine ⟨S,hS,3*(112*K)+2,by positivity,?_⟩
  intro a b c d
  exact VertexPath.thin_fourpoint (by positivity) hthin hgeo a b c d

end WordPictures

/-! All clauses of the exact main except exclusion of compatible locally
CAT(-1) finite homotopy models. The complete literal hyperbolicity consequence
is now unconditional, on the SAME finite aspherical complex. -/
namespace IncidenceTemplate
open CoreGeometry LetterPresentation ConeSkeleton
universe u

lemma finalFinite_hyperbolic (m : ℕ) :
    WordHyperbolic (FundamentalGroup (finalFiniteComplex m).Carrier (finalFiniteBasepoint m)) := by
  let p:=PresentedGroup.mk (Relator (finalSize m) (finalMaster m) (finalSix m))
  let e:=finalFinitePiOneEquiv m
  let φ:=e.toMonoidHom.comp p
  obtain ⟨C,hC,hfill⟩:=finalDiagramStage_linear m
  apply WordPictures.wordHyperbolic_of_linear φ
    (e.surjective.comp (PresentedGroup.mk_surjective _)) hC.le (L:=18)
    (R:=SimpleWordRelator (finalSize m) (finalMaster m) (finalSix m))
  · intro w hw
    change e (p (FreeGroup.mk w))=1
    have hh : p (FreeGroup.mk w)=1 := by
      apply PresentedGroup.one_of_mem
      rw [←wordRelator_image]
      exact ⟨w,simpleWordRelator_original _ _ _ hw,rfl⟩
    rw [hh,map_one]
  · exact fun w hw => simpleWordRelator_length _ _ _ hw
  · intro w hw
    apply hfill w
    apply e.injective
    change e (p (FreeGroup.mk w))=1 at hw
    rw [map_one]
    exact hw

/-- SAME-model complete construction and word-hyperbolicity. It deliberately
omits, rather than assumes, the remaining Cartan-Hadamard/deck consequence. -/
theorem exists_finite_aspherical_hyperbolic_noAction_oai :
    ∃ K : FiniteComplex, ∃ x : K.Carrier, ∃ C : ℝ,
    ConnectedSpace K.Carrier ∧ K.Aspherical x ∧ Infinite (FundamentalGroup K.Carrier x) ∧
      0 ≤ C ∧ K.LinearDiskFilling C ∧
      NoGeometricCATZeroAction.{u} (FundamentalGroup K.Carrier x) ∧
      WordHyperbolic (FundamentalGroup K.Carrier x) := by
  obtain ⟨m,hm⟩:=finalFinite_noAction.exists
  obtain ⟨C,hC,hfill⟩:=finalFinite_linear m
  exact ⟨finalFiniteComplex m,finalFiniteBasepoint m,C,inferInstance,finalFinite_aspherical m,
    inferInstance,hC,hfill,hm,finalFinite_hyperbolic m⟩

end IncidenceTemplate

/-! The real comparison inequality needed to pass the manuscript's exact
cosh-midpoint CAT(-1) definition to the Euclidean CN midpoint inequality. -/

/-! The global cosh-midpoint comparison implies whole-segment CAT(0)
comparison. No completeness or globalization
hypothesis is hidden in this elementary curvature-monotonicity step. -/

/-! The finite difference maximum principle required for local geodesic
continuation. Endpoint estimates are literal, with no convergence assumption. -/

/-! Literal equal-time interpolation of finite geodesic polygons. -/
open Set Metric

end HyperbolicObstruction

end

end OAI
end

theorem solution.{u} : type_of% @OAI.HyperbolicObstruction.IncidenceTemplate.exists_finite_aspherical_hyperbolic_noAction_oai.{u} := @OAI.HyperbolicObstruction.IncidenceTemplate.exists_finite_aspherical_hyperbolic_noAction_oai.{u}
