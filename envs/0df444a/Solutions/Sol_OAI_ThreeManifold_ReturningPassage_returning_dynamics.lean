-- Prove2me | solution 1 for OAI.ThreeManifold.ReturningPassage.returning_dynamics
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:47:48.815368+00:00
-- url     : https://prove2.me/submissions/010b4b9c-9fdc-4743-beb3-c1ee2f691a1b

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Returning.lean:L1234-L1282
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.ReturningPassage.returning_dynamics. The node keeps its source
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
import Theorems.Thm_OAI_ThreeManifold_Neck_pairing_hasDerivAt
import Theorems.Thm_OAI_ThreeManifold_PassageDynamics_scalar_reflection

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

lemma pairing_matrix_neg (A : TMat) (u v : TVec) :
    pairing (-A) u v = -pairing A u v := by
  simp only [pairing, Matrix.neg_mulVec, dotProduct_neg]

end ThreeManifold.Neck

open Set Filter
open scoped Topology ContDiff

namespace ThreeManifold.Cometric
open Matrix
open scoped Matrix.Norms.Elementwise

lemma P_smooth (δ : ℝ) : ContDiff ℝ ∞ (P δ) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> dsimp [P] <;> fun_prop

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

lemma convex_chord {H v₀ : ℝ} (hH : 0 < H) {v : ℝ → ℝ}
    (hv : ConvexOn ℝ (Icc 0 H) v) (h0 : v 0 = v₀) (h1 : v H = 0)
    {s : ℝ} (hs : s ∈ Icc 0 H) : v s ≤ v₀ * (1 - s / H) := by
  have hw0 : 0 ≤ 1 - s / H := sub_nonneg.mpr ((div_le_one hH).mpr hs.2)
  have hw1 : 0 ≤ s / H := div_nonneg hs.1 hH.le
  have hh := hv.2 (show (0 : ℝ) ∈ Icc 0 H from ⟨le_rfl, hH.le⟩)
    (show H ∈ Icc 0 H from ⟨hH.le, le_rfl⟩) hw0 hw1 (by ring : 1 - s / H + s / H = 1)
  simp only [smul_eq_mul, h0, h1, mul_zero, zero_add, add_zero, div_mul_cancel₀ _ hH.ne'] at hh
  nlinarith [hh]

lemma integral_chord_square {H v₀ : ℝ} (hH : 0 < H) :
    (∫ s in (0 : ℝ)..H, (v₀ * (1 - s / H)) ^ 2) = H * v₀ ^ 2 / 3 := by
  let f : ℝ → ℝ := fun s => v₀ ^ 2 * (s - s ^ 2 / H + s ^ 3 / (3 * H ^ 2))
  have hd (s : ℝ) : HasDerivAt f ((v₀ * (1 - s / H)) ^ 2) s := by
    have hh := (((hasDerivAt_id s).sub (((hasDerivAt_id s).pow 2).div_const H)).add
      (((hasDerivAt_id s).pow 3).div_const (3 * H ^ 2))).const_mul (v₀ ^ 2)
    convert hh using 1 <;> (first | rfl | (dsimp only [id]; field_simp; ring))
  have hc : Continuous (fun s : ℝ => (v₀ * (1 - s / H)) ^ 2) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) (hc.intervalIntegrable 0 H)]
  dsimp [f]
  field_simp
  ring

lemma half_chord_integral {H v₀ : ℝ} (hH : 0 < H) (hv₀ : 0 ≤ v₀) {v : ℝ → ℝ}
    (hc : ContinuousOn v (Icc 0 H)) (hv : ConvexOn ℝ (Icc 0 H) v)
    (hn : ∀ s ∈ Icc 0 H, 0 ≤ v s) (h0 : v 0 = v₀) (h1 : v H = 0) :
    (∫ s in (0 : ℝ)..H, v s ^ 2) ≤ H * v₀ ^ 2 / 3 := by
  rw [← integral_chord_square hH]
  apply intervalIntegral.integral_mono_on hH.le
  · exact (hc.pow 2).intervalIntegrable_of_Icc hH.le
  · exact (show Continuous (fun s : ℝ => (v₀ * (1 - s / H)) ^ 2) from by
      fun_prop).intervalIntegrable 0 H
  · intro s hs
    have hh := convex_chord hH hv h0 h1 hs
    have hr : 0 ≤ v₀ * (1 - s / H) := mul_nonneg hv₀
      (sub_nonneg.mpr ((div_le_one hH).mpr hs.2))
    nlinarith [hn s hs, mul_nonneg (sub_nonneg.mpr hh) (add_nonneg (hn s hs) hr)]

lemma full_chord_integral {L v₀ : ℝ} (hL : 0 < L) (hv₀ : 0 ≤ v₀) {v : ℝ → ℝ}
    (hc : ContinuousOn v (Icc 0 L)) (hv : ConvexOn ℝ (Icc 0 (L / 2)) v)
    (hn : ∀ s ∈ Icc 0 (L / 2), 0 ≤ v s) (h0 : v 0 = v₀) (h1 : v (L / 2) = 0)
    (hsym : ∀ s ∈ Icc 0 L, v (L - s) = -v s) :
    (∫ s in (0 : ℝ)..L, v s ^ 2) ≤ L * v₀ ^ 2 / 3 := by
  have hH : 0 < L / 2 := half_pos hL
  have hsub : Icc (0 : ℝ) (L / 2) ⊆ Icc 0 L := Icc_subset_Icc le_rfl (by linarith)
  have hi : IntervalIntegrable (fun s => v s ^ 2) volume 0 L :=
    (hc.pow 2).intervalIntegrable_of_Icc hL.le
  have hi0 := hi.mono_set (show uIcc (0 : ℝ) (L / 2) ⊆ uIcc 0 L from by
    simpa only [uIcc_of_le hL.le, uIcc_of_le hH.le] using hsub)
  have hi1 := hi.mono_set (show uIcc (L / 2) L ⊆ uIcc 0 L from by
    simp only [uIcc_of_le hL.le, uIcc_of_le (show L / 2 ≤ L by linarith)]
    exact Icc_subset_Icc hH.le le_rfl)
  have heq : (∫ s in L / 2..L, v s ^ 2) = ∫ s in (0 : ℝ)..L / 2, v s ^ 2 := by
    have hh := intervalIntegral.integral_comp_sub_left (a := 0) (b := L / 2)
      (fun s => v s ^ 2) L
    have hminus : L - L / 2 = L / 2 := by ring
    simp only [sub_zero, hminus] at hh
    rw [← hh]
    apply intervalIntegral.integral_congr
    intro s hs
    have hss : s ∈ Icc 0 L := hsub (by simpa only [uIcc_of_le hH.le] using hs)
    change v (L - s) ^ 2 = v s ^ 2
    rw [hsym s hss]
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals hi0 hi1, heq]
  have hb := half_chord_integral hH hv₀ (hc.mono hsub) hv hn h0 h1
  linarith

lemma velocity_convex {H : ℝ} {t v F₁ F₂ : ℝ → ℝ}
    (ht : ∀ s ∈ Icc 0 H, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 H, HasDerivAt v (-F₁ (t s) / 2) s)
    (hF : ∀ s ∈ Icc 0 H, HasDerivAt F₁ (F₂ (t s)) (t s))
    (hn : ∀ s ∈ Icc 0 H, 0 ≤ v s)
    (hFn : ∀ s ∈ Icc 0 H, F₂ (t s) ≤ 0) : ConvexOn ℝ (Icc 0 H) v := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 H)
    (fun s hs => (hv s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hv s (interior_subset hs)).hasDerivWithinAt)
    (f'' := fun s => -F₂ (t s) * v s / 2)
  · intro s hs
    have h := ((hF s (interior_subset hs)).comp s (ht s (interior_subset hs))).neg.div_const 2
    convert h.hasDerivWithinAt using 1 <;> (first | rfl | ring)
  · intro s hs
    exact div_nonneg (mul_nonneg (neg_nonneg.mpr (hFn s (interior_subset hs)))
      (hn s (interior_subset hs))) (by norm_num)

lemma height_concave {H : ℝ} {t v F₁ : ℝ → ℝ}
    (ht : ∀ s ∈ Icc 0 H, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 H, HasDerivAt v (-F₁ (t s) / 2) s)
    (hFn : ∀ s ∈ Icc 0 H, 0 ≤ F₁ (t s)) : ConcaveOn ℝ (Icc 0 H) t := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 H)
    (fun s hs => (ht s hs).continuousAt.continuousWithinAt)
    (fun s hs => (ht s (interior_subset hs)).hasDerivWithinAt)
    (fun s hs => (hv s (interior_subset hs)).hasDerivWithinAt)
  intro s hs
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hFn s (interior_subset hs)))
    (by norm_num)

end ThreeManifold.ReturningTime

open Set MeasureTheory
open scoped Interval
namespace ThreeManifold.ReturningCoefficients
open Neck Matrix

lemma constant_pairing_deriv {P : ℝ → TMat} {D : TMat} {u : ℝ}
    (hP : HasDerivAt P D u) (p q : TVec) :
    HasDerivAt (fun t => pairing (P t) p q) (pairing D p q) u := by
  simpa only [pairing, zero_dotProduct, Matrix.mulVec_zero, dotProduct_zero,
    zero_add, add_zero] using
    (pairing_hasDerivAt hP (hasDerivAt_const u p) (hasDerivAt_const u q))

lemma derivative_antitone {P₁ P₂ : ℝ → TMat} {T : ℝ}
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt P₁ (P₂ t) t)
    (hc : ∀ t ∈ Icc 0 T, ∀ p, pairing (P₂ t) p p ≤ 0) (p : TVec) :
    AntitoneOn (fun t => pairing (P₁ t) p p) (Icc 0 T) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
  · exact fun t ht => (constant_pairing_deriv (hd t ht) p p).continuousAt.continuousWithinAt
  · intro t ht
    exact (constant_pairing_deriv (hd t (interior_subset ht)) p p).hasDerivWithinAt
  · intro t ht
    exact hc t (interior_subset ht) p

end ThreeManifold.ReturningCoefficients

open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.Cometric
open Neck Matrix

lemma coordinateCometric_smooth (right : Bool) (δ : ℝ) :
    ContDiff ℝ ∞ (coordinateCometric right δ) := by
  cases right
  · exact P_smooth δ
  · exact (congruenceCLM (C₂ δ)).contDiff.comp
      ((P_smooth δ).comp (contDiff_const.sub contDiff_id))

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

lemma cannot_reach_equilibrium {F₁ : ℝ → ℝ} (hF : ContDiff ℝ ∞ F₁)
    {t v : ℝ → ℝ} {a b c : ℝ} (hc : c ∈ Ioo a b)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-F₁ (t s) / 2) s)
    (hvc : v c = 0) (hFc : F₁ (t c) = 0) :
    ∀ s ∈ Icc a b, t s = t c ∧ v s = 0 := by
  have huc (s : ℝ) : HasDerivAt (fun _ : ℝ => t c) (0 : ℝ) s := hasDerivAt_const s (t c)
  have hwc (s : ℝ) : HasDerivAt (fun _ : ℝ => (0 : ℝ)) (-F₁ (t c) / 2) s := by
    simpa only [hFc, neg_zero, zero_div] using (hasDerivAt_const s (0 : ℝ))
  obtain ⟨hu, hw⟩ := scalar_equations_unique hF hc ht hv
    (fun s _ => huc s) (fun s _ => hwc s) rfl hvc
  exact fun s hs => ⟨hu hs, hw hs⟩

lemma positive_return_has_stationary_maximum {t v : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L) (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (h0 : t 0 = 0) (hL0 : t L = 0) (hpos : ∀ s ∈ Ioo 0 L, 0 < t s) :
    ∃ c ∈ Ioo 0 L, 0 < t c ∧ v c = 0 ∧ IsMaxOn t (Icc 0 L) c := by
  obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hL.le) (HasDerivAt.continuousOn ht)
  have hp := hpos (L / 2) ⟨by linarith, by linarith⟩
  have hcm : 0 < t c := lt_of_lt_of_le hp (hmax ⟨by linarith, by linarith⟩)
  have hc' : c ∈ Ioo 0 L := by
    constructor
    · by_contra hn
      have he : c = 0 := by linarith [hc.1]
      rw [he, h0] at hcm
      exact lt_irrefl _ hcm
    · by_contra hn
      have he : c = L := by linarith [hc.2]
      rw [he, hL0] at hcm
      exact lt_irrefl _ hcm
  refine ⟨c, hc', hcm, ?_, hmax⟩
  exact (hmax.isLocalMax (Icc_mem_nhds hc'.1 hc'.2)).hasDerivAt_eq_zero (ht c hc)

lemma return_midpoint {F₁ : ℝ → ℝ} (hF : ContDiff ℝ ∞ F₁)
    {t v : ℝ → ℝ} {L c : ℝ} (hc : c ∈ Ioo 0 L)
    (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-F₁ (t s) / 2) s)
    (h0 : t 0 = 0) (hL0 : t L = 0) (hpos : ∀ s ∈ Ioo 0 L, 0 < t s)
    (hvc : v c = 0) : c = L / 2 := by
  rcases lt_trichotomy c (L / 2) with h | h | h
  · have hsub : Icc (0 : ℝ) (2 * c) ⊆ Icc 0 L := Icc_subset_Icc le_rfl (by linarith)
    have hh := scalar_reflection hF (show c ∈ Ioo (0 : ℝ) (2 * c) from
      ⟨hc.1, by linarith [hc.1]⟩) (by ring : 0 + 2 * c = 2 * c)
      (fun s hs => ht s (hsub hs)) (fun s hs => hv s (hsub hs)) hvc
    have he := (hh 0 ⟨le_rfl, by linarith [hc.1]⟩).1
    simp only [sub_zero, h0] at he
    have hp := hpos (2 * c) ⟨by linarith [hc.1], by linarith⟩
    exact False.elim (by linarith)
  · exact h
  · have hsub : Icc (2 * c - L) L ⊆ Icc 0 L := Icc_subset_Icc (by linarith) le_rfl
    have hh := scalar_reflection hF (show c ∈ Ioo (2 * c - L) L from
      ⟨by linarith [hc.2], hc.2⟩) (by ring : 2 * c - L + L = 2 * c)
      (fun s hs => ht s (hsub hs)) (fun s hs => hv s (hsub hs)) hvc
    have he := (hh L ⟨by linarith [hc.2], le_rfl⟩).1
    rw [hL0] at he
    have hp := hpos (2 * c - L) ⟨by linarith, by linarith [hc.2]⟩
    exact False.elim (by linarith)

lemma actual_return_symmetry {F₁ : ℝ → ℝ} (hF : ContDiff ℝ ∞ F₁)
    {t v : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-F₁ (t s) / 2) s)
    (h0 : t 0 = 0) (hL0 : t L = 0) (hpos : ∀ s ∈ Ioo 0 L, 0 < t s) :
    v (L / 2) = 0 ∧ IsMaxOn t (Icc 0 L) (L / 2) ∧
      ∀ s ∈ Icc 0 L, t (L - s) = t s ∧ v (L - s) = -v s := by
  obtain ⟨c, hc, _, hvc, hm⟩ := positive_return_has_stationary_maximum hL ht h0 hL0 hpos
  have he := return_midpoint hF hc ht hv h0 hL0 hpos hvc
  subst c
  refine ⟨hvc, hm, ?_⟩
  have hh := scalar_reflection hF (show L / 2 ∈ Ioo (0 : ℝ) L from
    ⟨by linarith, by linarith⟩) (by ring : 0 + L = 2 * (L / 2)) ht hv hvc
  simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hh

lemma force_nonneg_at_top {t v F F₁ : ℝ → ℝ} {L c energy : ℝ}
    (hc : c ∈ Icc 0 L) (htop : 0 < t c)
    (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (h0 : t 0 = 0) (hvc : v c = 0)
    (henergy : ∀ s ∈ Icc 0 L, F (t s) + v s ^ 2 = energy)
    (hFd : HasDerivAt F (F₁ (t c)) (t c)) : 0 ≤ F₁ (t c) := by
  have hsub : Icc (0 : ℝ) c ⊆ Icc 0 L := Icc_subset_Icc le_rfl hc.2
  have hIVT := intermediate_value_Icc hc.1 ((HasDerivAt.continuousOn ht).mono hsub)
  rw [h0] at hIVT
  have hmax : IsMaxOn F (Icc 0 (t c)) (t c) := by
    intro u hu
    obtain ⟨s, hs, hsu⟩ := hIVT hu
    have hh := henergy s (hsub hs)
    have htopE := henergy c hc
    rw [hvc, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at htopE
    rw [hsu] at hh
    change F u ≤ F (t c)
    calc
      F u ≤ F u + v s ^ 2 := le_add_of_nonneg_right (sq_nonneg (v s))
      _ = energy := hh
      _ = F (t c) := htopE.symm
  have hy : 0 - t c ∈ posTangentConeAt (Icc 0 (t c)) (t c) :=
    sub_mem_posTangentConeAt_of_segment_subset ((convex_Icc (0 : ℝ) (t c)).segment_subset
      ⟨htop.le, le_rfl⟩ ⟨le_rfl, htop.le⟩)
  have hh := hmax.localize.hasFDerivWithinAt_nonpos hFd.hasFDerivAt.hasFDerivWithinAt hy
  have he : -(t c) * F₁ (t c) ≤ 0 := by simpa using hh
  nlinarith

lemma force_pos_at_top {F F₁ : ℝ → ℝ} (hF : ContDiff ℝ ∞ F₁)
    {t v : ℝ → ℝ} {L c energy : ℝ} (hc : c ∈ Ioo 0 L) (htop : 0 < t c)
    (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-F₁ (t s) / 2) s)
    (h0 : t 0 = 0) (hvc : v c = 0)
    (henergy : ∀ s ∈ Icc 0 L, F (t s) + v s ^ 2 = energy)
    (hFd : HasDerivAt F (F₁ (t c)) (t c)) : 0 < F₁ (t c) := by
  have hnon := force_nonneg_at_top (Ioo_subset_Icc_self hc) htop ht h0 hvc henergy hFd
  apply lt_of_le_of_ne hnon
  intro he
  have heq := cannot_reach_equilibrium hF hc ht hv hvc he.symm
  have hh := (heq 0 ⟨le_rfl, le_trans hc.1.le hc.2.le⟩).1
  rw [h0] at hh
  linarith

lemma return_velocity_strictAnti {F₁ : ℝ → ℝ} {t v : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-F₁ (t s) / 2) s)
    (ht : MapsTo t (Icc 0 L) (Icc 0 (t (L / 2))))
    (hanti : AntitoneOn F₁ (Icc 0 (t (L / 2))))
    (hforce : 0 < F₁ (t (L / 2))) (hvc : v (L / 2) = 0) :
    StrictAntiOn v (Icc 0 L) ∧ 0 < v 0 ∧
      (∀ s ∈ Icc 0 (L / 2), 0 ≤ v s) := by
  have hF (s : ℝ) (hs : s ∈ Icc 0 L) : 0 < F₁ (t s) :=
    lt_of_lt_of_le hforce (hanti (ht hs)
      (ht ⟨by linarith, by linarith⟩) (ht hs).2)
  have hsa : StrictAntiOn v (Icc 0 L) := by
    apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc 0 L)
      (HasDerivAt.continuousOn hv)
      (fun s hs => (hv s (interior_subset hs)).hasDerivWithinAt)
    intro s hs
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (hF s (interior_subset hs))) (by norm_num)
  refine ⟨hsa, ?_, ?_⟩
  · have hh := hsa ⟨le_rfl, hL.le⟩ ⟨by linarith, by linarith⟩ (by linarith : 0 < L / 2)
    rwa [hvc] at hh
  · intro s hs
    have hh := hsa.antitoneOn ⟨hs.1, by linarith [hs.2]⟩ ⟨by linarith, by linarith⟩ hs.2
    rwa [hvc] at hh

end ThreeManifold.PassageDynamics

open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ReturningPassage

section
open Neck Cometric ReturningCoefficients ReturningTime PassageDynamics Matrix

lemma contDiff_pairing_const {R : ℝ → TMat} {n : WithTop ℕ∞}
    (hR : ContDiff ℝ n R) (p q : TVec) : ContDiff ℝ n (fun u => pairing (R u) p q) := by
  simp only [pairing, Matrix.mulVec, dotProduct]
  fun_prop

lemma force_smooth (right : Bool) (δ : ℝ) (p : TVec) :
    ContDiff ℝ ∞ (force right δ p) :=
  contDiff_pairing_const (contDiff_infty_iff_deriv.mp (coordinateCometric_smooth right δ)).2 p p

lemma potential_hasDerivAt (right : Bool) (δ : ℝ) (p : TVec) (u : ℝ) :
    HasDerivAt (potential right δ p) (force right δ p u) u :=
  constant_pairing_deriv ((coordinateCometric_smooth right δ).differentiable
    (by simp)).differentiableAt.hasDerivAt p p

lemma force_hasDerivAt (right : Bool) (δ : ℝ) (p : TVec) (u : ℝ) :
    HasDerivAt (force right δ p) (forceDerivative right δ p u) u :=
  constant_pairing_deriv ((contDiff_infty_iff_deriv.mp
    (coordinateCometric_smooth right δ)).2.differentiable (by simp)).differentiableAt.hasDerivAt p p

lemma force_antitone {right : Bool} {δ T : ℝ} {p : TVec}
    (hT : T ≤ 1)
    (hc : ∀ u ∈ Icc 0 1, ∀ q, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q) :
    AntitoneOn (force right δ p) (Icc 0 T) := by
  apply derivative_antitone (P₂ := deriv (deriv (coordinateCometric right δ)))
    (fun u _ => ((contDiff_infty_iff_deriv.mp (coordinateCometric_smooth right δ)).2.differentiable
      (by simp)).differentiableAt.hasDerivAt)
  intro u hu q
  have hh := hc u ⟨hu.1, hu.2.trans hT⟩ q
  change 0 ≤ pairing (-deriv (deriv (coordinateCometric right δ)) u) q q at hh
  rw [pairing_matrix_neg] at hh
  linarith

theorem returning_dynamics {right : Bool} {δ L : ℝ} {p : TVec} {t v : ℝ → ℝ}
    (hL : 0 < L)
    (hconc : ∀ u ∈ Icc 0 1, ∀ q, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q)
    (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-force right δ p (t s) / 2) s)
    (h0 : t 0 = 0) (h1 : t L = 0)
    (hrange : ∀ s ∈ Ioo 0 L, t s ∈ Ioo 0 1)
    (henergy : ∀ s ∈ Icc 0 L, potential right δ p (t s) + v s ^ 2 = 1) :
    let T := t (L / 2)
    0 < v 0 ∧ v (L / 2) = 0 ∧ T ∈ Ioo 0 1 ∧
    MapsTo t (Icc 0 L) (Icc 0 T) ∧
    (∀ s ∈ Icc 0 L, t (L - s) = t s ∧ v (L - s) = -v s) ∧
    (∀ u ∈ Icc 0 T, 0 < force right δ p u) ∧
    ConvexOn ℝ (Icc 0 (L / 2)) v ∧
    ConcaveOn ℝ (Icc 0 (L / 2)) t ∧
      (∫ s in (0 : ℝ)..L, v s ^ 2) ≤ L * v 0 ^ 2 / 3 := by
  have hc : L / 2 ∈ Ioo (0 : ℝ) L := ⟨by linarith, by linarith⟩
  have hpos := fun s hs => (hrange s hs).1
  obtain ⟨hvc, hmax, hsym⟩ := actual_return_symmetry (force_smooth right δ p) hL ht hv h0 h1 hpos
  have hmaps : MapsTo t (Icc 0 L) (Icc 0 (t (L / 2))) := by
    intro s hs
    refine ⟨?_, hmax hs⟩
    rcases eq_or_lt_of_le hs.1 with he | he
    · rw [← he, h0]
    · rcases eq_or_lt_of_le hs.2 with he' | he'
      · rw [he', h1]
      · exact (hpos s ⟨he, he'⟩).le
  have htop := force_pos_at_top (force_smooth right δ p) hc (hpos _ hc) ht hv h0 hvc henergy
    (potential_hasDerivAt right δ p _)
  have hanti := force_antitone (hrange _ hc).2.le hconc (p := p)
  have hforce (u : ℝ) (hu : u ∈ Icc 0 (t (L / 2))) : 0 < force right δ p u :=
    lt_of_lt_of_le htop (hanti hu ⟨(hrange _ hc).1.le, le_rfl⟩ hu.2)
  obtain ⟨_, hv0, hvnon⟩ := return_velocity_strictAnti hL hv hmaps hanti htop hvc
  have hsub : Icc (0 : ℝ) (L / 2) ⊆ Icc 0 L := Icc_subset_Icc le_rfl (by linarith)
  have hvconv : ConvexOn ℝ (Icc 0 (L / 2)) v := by
    apply velocity_convex (fun s hs => ht s (hsub hs)) (fun s hs => hv s (hsub hs))
      (fun s _ => force_hasDerivAt right δ p (t s)) hvnon
    intro s hs
    have hu := hmaps (hsub hs)
    have hh := hconc (t s) ⟨hu.1, hu.2.trans (hrange _ hc).2.le⟩ p
    change 0 ≤ pairing (-deriv (deriv (coordinateCometric right δ)) (t s)) p p at hh
    rw [pairing_matrix_neg] at hh
    exact neg_nonneg.mp hh
  have htconc : ConcaveOn ℝ (Icc 0 (L / 2)) t :=
    height_concave (fun s hs => ht s (hsub hs)) (fun s hs => hv s (hsub hs))
      (fun s hs => (hforce _ (hmaps (hsub hs))).le)
  refine ⟨hv0, hvc, hrange _ hc, hmaps, hsym, hforce, hvconv, htconc, ?_⟩
  exact full_chord_integral hL hv0.le (HasDerivAt.continuousOn hv) hvconv hvnon rfl hvc
    (fun s hs => (hsym s hs).2)

end

open Neck Cometric ReturningCoefficients ReturningTime PassageDynamics Matrix DirectTurning Turning

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
open OAI OAI.ThreeManifold OAI.ThreeManifold.ReturningPassage
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
open Neck Cometric ReturningCoefficients PassageDynamics Matrix


theorem solution : type_of% @_root_.OAI.ThreeManifold.ReturningPassage.returning_dynamics := @_root_.OAI.ThreeManifold.ReturningPassage.returning_dynamics
