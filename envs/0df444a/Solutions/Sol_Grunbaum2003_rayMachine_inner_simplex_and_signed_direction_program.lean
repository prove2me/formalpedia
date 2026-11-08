-- Prove2me | solution 1 for Grunbaum2003.rayMachine_inner_simplex_and_signed_direction_program
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T18:41:32.259541+00:00
-- url     : https://prove2.me/submissions/2c23d6ee-a6f3-4bf8-8ffb-8d13188e0b52

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators

noncomputable section

namespace Grunbaum2003.RayInner

def axis {d : ℕ} (i : Fin d) : Fin d → ℝ := fun j => if j = i then 1 else 0
def ones (d : ℕ) : Fin d → ℝ := fun _ => 1

theorem sum_axis_eq {d : ℕ} (c : Fin d → ℝ) :
    (∑ i : Fin d, c i • axis i) = c := by
  classical
  ext j
  simp [axis, Finset.sum_apply]

theorem convex_sum_mem_le_one {d : ℕ} {I : Type*} [Fintype I]
    {P : Set (Fin d → ℝ)} (hconv : Convex ℝ P) (hzero : (0 : Fin d → ℝ) ∈ P)
    (w : I → ℝ) (z : I → Fin d → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i ≤ 1) (hz : ∀ i, z i ∈ P) :
    (∑ i, w i • z i) ∈ P := by
  classical
  let w' : Option I → ℝ := fun i => match i with
    | none => 1 - ∑ j, w j
    | some j => w j
  let z' : Option I → Fin d → ℝ := fun i => match i with
    | none => 0
    | some j => z j
  have hw' : ∀ i ∈ (Finset.univ : Finset (Option I)), 0 ≤ w' i := by
    intro i _
    cases i with
    | none => exact sub_nonneg.mpr hsum
    | some i => exact hw i
  have hs' : ∑ i : Option I, w' i = 1 := by
    simp only [Fintype.sum_option, w']
    ring
  have hz' : ∀ i ∈ (Finset.univ : Finset (Option I)), z' i ∈ P := by
    intro i _
    cases i with
    | none => exact hzero
    | some i => exact hz i
  have h := hconv.sum_mem hw' hs' hz'
  simpa only [Fintype.sum_option, w', z', smul_zero, zero_add] using h

def samplePoint {d : ℕ} (t : Fin d → ℝ) (s : ℝ) : Option (Fin d) → Fin d → ℝ
  | none => (-s) • ones d
  | some i => t i • axis i

def sampleHull {d : ℕ} (t : Fin d → ℝ) (s : ℝ) : Set (Fin d → ℝ) :=
  convexHull ℝ (Set.range (samplePoint t s))

theorem samplePoint_mem_hull {d : ℕ} (t : Fin d → ℝ) (s : ℝ) (i : Option (Fin d)) :
    samplePoint t s i ∈ sampleHull t s :=
  subset_convexHull ℝ _ (Set.mem_range_self i)

theorem sampleHull_subset {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (t : Fin d → ℝ) (s : ℝ)
    (hneg : (-s) • ones d ∈ P) (hpos : ∀ i, t i • axis i ∈ P) :
    sampleHull t s ⊆ P := by
  apply convexHull_min _ hconv
  rintro _ ⟨i, rfl⟩
  cases i with
  | none => exact hneg
  | some i => exact hpos i

theorem weighted_sample_sum {d : ℕ} (t : Fin d → ℝ) (s c : ℝ)
    (ht : ∀ i, t i ≠ 0) (hs : s ≠ 0) :
    (∑ i : Option (Fin d),
      (match i with | none => c / s | some j => c / t j) • samplePoint t s i) = 0 := by
  classical
  rw [Fintype.sum_option]
  change (c / s) • ((-s) • ones d) + ∑ i, (c / t i) • (t i • axis i) = 0
  have hpos (i : Fin d) : (c / t i) • (t i • axis i) = c • axis i := by
    rw [smul_smul, div_mul_cancel₀ c (ht i)]
  rw [smul_smul, mul_neg, div_mul_cancel₀ c hs,
    Finset.sum_congr rfl (fun i _ => hpos i), sum_axis_eq]
  ext j
  simp only [Pi.add_apply, Pi.smul_apply, ones, smul_eq_mul, mul_one, Pi.zero_apply,
    neg_add_cancel]

theorem zero_mem_sampleHull {d : ℕ} (t : Fin d → ℝ) (s : ℝ)
    (ht : ∀ i, 0 < t i) (hs : 0 < s) : (0 : Fin d → ℝ) ∈ sampleHull t s := by
  classical
  let C := s⁻¹ + ∑ i, (t i)⁻¹
  have hC : 0 < C := add_pos_of_pos_of_nonneg (inv_pos.mpr hs)
    (Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (ht i).le))
  let c := C⁻¹
  let w : Option (Fin d) → ℝ := fun i => match i with
    | none => c / s
    | some j => c / t j
  have hw : ∀ i ∈ (Finset.univ : Finset (Option (Fin d))), 0 ≤ w i := by
    intro i _
    cases i with
    | none => exact div_nonneg (inv_nonneg.mpr hC.le) hs.le
    | some i => exact div_nonneg (inv_nonneg.mpr hC.le) (ht i).le
  have hsum : ∑ i : Option (Fin d), w i = 1 := by
    simp only [Fintype.sum_option, w, div_eq_mul_inv, ← Finset.mul_sum]
    rw [← mul_add]
    exact inv_mul_cancel₀ hC.ne'
  have h := (convex_convexHull ℝ (Set.range (samplePoint t s))).sum_mem hw hsum
    (fun i _ => samplePoint_mem_hull t s i)
  change (∑ i : Option (Fin d), w i • samplePoint t s i) ∈ sampleHull t s at h
  simpa only [w, weighted_sample_sum t s c (fun i => (ht i).ne') hs.ne'] using h

end Grunbaum2003.RayInner

namespace Grunbaum2003.RayInner

def sampleScale {d : ℕ} (t : Fin d → ℝ) (s : ℝ) : ℝ :=
  (1 + s⁻¹ + ∑ i, (t i)⁻¹)⁻¹

theorem sampleScale_pos_capacity {d : ℕ} (t : Fin d → ℝ) (s : ℝ)
    (ht : ∀ i, 0 < t i) (hs : 0 < s) :
    0 < sampleScale t s ∧
      sampleScale t s / s + ∑ i, sampleScale t s / t i ≤ 1 := by
  have hsum : 0 ≤ ∑ i, (t i)⁻¹ :=
    Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (ht i).le)
  have hden : 0 < 1 + s⁻¹ + ∑ i, (t i)⁻¹ := by
    linarith only [inv_pos.mpr hs, hsum]
  have ha : 0 < sampleScale t s := inv_pos.mpr hden
  have hprod : sampleScale t s * (1 + s⁻¹ + ∑ i, (t i)⁻¹) = 1 :=
    inv_mul_cancel₀ hden.ne'
  refine ⟨ha, ?_⟩
  calc
    sampleScale t s / s + ∑ i, sampleScale t s / t i =
        sampleScale t s * (1 + s⁻¹ + ∑ i, (t i)⁻¹) - sampleScale t s := by
      simp only [div_eq_mul_inv, ← Finset.mul_sum]
      ring
    _ = 1 - sampleScale t s := by rw [hprod]
    _ ≤ 1 := sub_le_self 1 ha.le

theorem signed_axes_mem_of_samples {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hzero : (0 : Fin d → ℝ) ∈ P)
    (t : Fin d → ℝ) (s : ℝ) (ht : ∀ i, 0 < t i) (hs : 0 < s)
    (hneg : (-s) • ones d ∈ P) (hpos : ∀ i, t i • axis i ∈ P) :
    ∀ i : Fin d, sampleScale t s • axis i ∈ P ∧ (-sampleScale t s) • axis i ∈ P := by
  classical
  let a := sampleScale t s
  have ha : 0 < a := (sampleScale_pos_capacity t s ht hs).1
  have hcap : a / s + ∑ j, a / t j ≤ 1 := (sampleScale_pos_capacity t s ht hs).2
  have hratio (j : Fin d) : 0 ≤ a / t j := div_nonneg ha.le (ht j).le
  have hrpole : 0 ≤ a / s := div_nonneg ha.le hs.le
  intro i
  constructor
  · have hiSum : a / t i ≤ ∑ j, a / t j :=
      Finset.single_le_sum (fun j _ => hratio j) (Finset.mem_univ i)
    have hiOne : a / t i ≤ 1 := by linarith only [hiSum, hcap, hrpole]
    have h := hconv hzero (hpos i) (sub_nonneg.mpr hiOne) (hratio i)
      (sub_add_cancel 1 (a / t i))
    simpa only [smul_zero, zero_add, smul_smul, div_mul_cancel₀ a (ht i).ne'] using h
  · let w : Option (Fin d) → ℝ := fun j => match j with
      | none => a / s
      | some j => if j = i then 0 else a / t j
    have hw : ∀ j, 0 ≤ w j := by
      intro j
      cases j with
      | none => exact hrpole
      | some j =>
          dsimp only [w]
          split_ifs
          · exact le_rfl
          · exact hratio j
    have hsum : ∑ j : Option (Fin d), w j ≤ 1 := by
      rw [Fintype.sum_option]
      change a / s + ∑ j, (if j = i then 0 else a / t j) ≤ 1
      calc
        _ ≤ a / s + ∑ j, a / t j := by
          apply add_le_add le_rfl
          apply Finset.sum_le_sum
          intro j _
          by_cases hj : j = i
          · rw [if_pos hj]
            exact hratio j
          · rw [if_neg hj]
        _ ≤ 1 := hcap
    have hz : ∀ j, samplePoint t s j ∈ P := by
      intro j
      cases j with
      | none => exact hneg
      | some j => exact hpos j
    have h := convex_sum_mem_le_one hconv hzero w (samplePoint t s) hw hsum hz
    have hterm (j : Fin d) :
        (if j = i then 0 else a / t j) • (t j • axis j) =
          if j = i then 0 else a • axis j := by
      by_cases hj : j = i
      · simp only [hj, ite_true, zero_smul]
      · simp only [hj, ite_false, smul_smul, div_mul_cancel₀ a (ht j).ne']
    have hfull : (∑ j : Fin d, a • axis j) = a • ones d := by
      rw [sum_axis_eq]
      ext j
      simp only [Pi.smul_apply, ones, smul_eq_mul, mul_one]
    have hremove : (∑ j : Fin d, if j = i then 0 else a • axis j) =
        a • ones d - a • axis i := by
      have heq (j : Fin d) : (if j = i then 0 else a • axis j) =
          a • axis j - (if j = i then a • axis i else 0) := by
        by_cases hj : j = i <;> simp only [hj, ite_true, ite_false, sub_self, sub_zero]
      rw [Finset.sum_congr rfl (fun j _ => heq j), Finset.sum_sub_distrib, hfull]
      simp
    have hpoint : (∑ j : Option (Fin d), w j • samplePoint t s j) = (-a) • axis i := by
      rw [Fintype.sum_option]
      change (a / s) • ((-s) • ones d) +
        (∑ j, (if j = i then 0 else a / t j) • (t j • axis j)) = (-a) • axis i
      rw [Finset.sum_congr rfl (fun j _ => hterm j), hremove,
        smul_smul, mul_neg, div_mul_cancel₀ a hs.ne']
      simp only [neg_smul]
      abel
    exact hpoint ▸ h

theorem signed_axes_mem_sampleHull {d : ℕ} (t : Fin d → ℝ) (s : ℝ)
    (ht : ∀ i, 0 < t i) (hs : 0 < s) :
    ∀ i : Fin d, sampleScale t s • axis i ∈ sampleHull t s ∧
      (-sampleScale t s) • axis i ∈ sampleHull t s := by
  apply signed_axes_mem_of_samples (convex_convexHull ℝ _)
    (zero_mem_sampleHull t s ht hs) t s ht hs
  · exact samplePoint_mem_hull t s none
  · intro i
    exact samplePoint_mem_hull t s (some i)

end Grunbaum2003.RayInner

namespace Grunbaum2003.RayInner

def directionScale {d : ℕ} (a : ℝ) (u : Fin d → ℝ) : ℝ :=
  a / (1 + ∑ i, |u i|)

theorem directionScale_pos {d : ℕ} {a : ℝ} (ha : 0 < a) (u : Fin d → ℝ) :
    0 < directionScale a u :=
  div_pos ha (add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun i _ => abs_nonneg (u i))))

theorem directional_point_mem {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hzero : (0 : Fin d → ℝ) ∈ P)
    {a : ℝ} (ha : 0 < a)
    (haxes : ∀ i : Fin d, a • axis i ∈ P ∧ (-a) • axis i ∈ P)
    (u : Fin d → ℝ) : directionScale a u • u ∈ P := by
  classical
  let D := 1 + ∑ i, |u i|
  have hD : 0 < D := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun i _ => abs_nonneg (u i)))
  let w : Fin d → ℝ := fun i => |u i| / D
  let z : Fin d → Fin d → ℝ := fun i =>
    if 0 ≤ u i then a • axis i else (-a) • axis i
  have hw : ∀ i, 0 ≤ w i := fun i => div_nonneg (abs_nonneg (u i)) hD.le
  have hsum : ∑ i, w i ≤ 1 := by
    change (∑ i, |u i| / D) ≤ 1
    rw [← Finset.sum_div]
    apply (div_le_iff₀ hD).mpr
    dsimp only [D]
    linarith only [Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
      abs_nonneg (u i))]
  have hz : ∀ i, z i ∈ P := by
    intro i
    dsimp only [z]
    split_ifs
    · exact (haxes i).1
    · exact (haxes i).2
  have h := convex_sum_mem_le_one hconv hzero w z hw hsum hz
  have hterm (i : Fin d) : w i • z i = (a / D * u i) • axis i := by
    dsimp only [w, z]
    by_cases hi : 0 ≤ u i
    · rw [if_pos hi, abs_of_nonneg hi, smul_smul]
      congr 1
      ring
    · rw [if_neg hi, abs_of_neg (lt_of_not_ge hi), smul_smul]
      congr 1
      ring
  have hpoint : (∑ i, w i • z i) = directionScale a u • u := by
    rw [Finset.sum_congr rfl (fun i _ => hterm i), sum_axis_eq]
    rfl
  exact hpoint ▸ h

theorem signed_direction_mem {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hzero : (0 : Fin d → ℝ) ∈ P)
    {a : ℝ} (ha : 0 < a)
    (haxes : ∀ i : Fin d, a • axis i ∈ P ∧ (-a) • axis i ∈ P)
    (u : Fin d → ℝ) :
    0 < directionScale a u ∧
      (-directionScale a u) • u ∈ P ∧ directionScale a u • u ∈ P := by
  refine ⟨directionScale_pos ha u, ?_, directional_point_mem hconv hzero ha haxes u⟩
  have h := directional_point_mem hconv hzero ha haxes (-u)
  simpa only [directionScale, Pi.neg_apply, abs_neg, smul_neg, neg_smul] using h

theorem signed_direction_mem_sampleHull {d : ℕ} (t : Fin d → ℝ) (s : ℝ)
    (ht : ∀ i, 0 < t i) (hs : 0 < s) (u : Fin d → ℝ) :
    0 < directionScale (sampleScale t s) u ∧
      (-directionScale (sampleScale t s) u) • u ∈ sampleHull t s ∧
      directionScale (sampleScale t s) u • u ∈ sampleHull t s :=
  signed_direction_mem (convex_convexHull ℝ _) (zero_mem_sampleHull t s ht hs)
    (sampleScale_pos_capacity t s ht hs).1 (signed_axes_mem_sampleHull t s ht hs) u

end Grunbaum2003.RayInner

namespace Grunbaum2003

theorem nonneg_smul_frontier_mem_iff {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {b : Fin d → ℝ} (hb : b ∈ frontier P) {s : ℝ} (hs : 0 ≤ s) :
    s • b ∈ P ↔ s ≤ 1 := by
  constructor
  · intro hsb
    by_contra hle
    have hsone : 1 < s := lt_of_not_ge hle
    have hspos : 0 < s := zero_lt_one.trans hsone
    have hinv : s⁻¹ < 1 := by
      rw [inv_eq_one_div, div_lt_iff₀ hspos]
      simpa only [one_mul] using hsone
    have hi := hconv.combo_interior_self_mem_interior hzero hsb
      (sub_pos.mpr hinv) (inv_nonneg.mpr hspos.le) (sub_add_cancel 1 s⁻¹)
    have hbint : b ∈ interior P := by
      simpa only [smul_zero, zero_add, smul_smul, inv_mul_cancel₀ hspos.ne', one_smul]
        using hi
    exact hb.2 hbint
  · intro hsone
    have hi := hconv (interior_subset hzero) (hclosed.frontier_subset hb)
      (sub_nonneg.mpr hsone) hs (sub_add_cancel 1 s)
    simpa only [smul_zero, zero_add] using hi

theorem frontier_eq_of_pos_smul {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {b c : Fin d → ℝ} (hb : b ∈ frontier P) (hc : c ∈ frontier P)
    {s : ℝ} (hs : 0 < s) (hcb : c = s • b) : c = b := by
  have hsle : s ≤ 1 := (nonneg_smul_frontier_mem_iff hconv hclosed hzero hb hs.le).mp
    (hcb ▸ hclosed.frontier_subset hc)
  have hsge : 1 ≤ s := by
    by_contra h
    have hslt : s < 1 := lt_of_not_ge h
    have hi := hconv.combo_interior_self_mem_interior hzero (hclosed.frontier_subset hb)
      (sub_pos.mpr hslt) hs.le (sub_add_cancel 1 s)
    have hcint : c ∈ interior P := by
      rw [hcb]
      simpa only [smul_zero, zero_add] using hi
    exact hc.2 hcint
  rw [hcb, le_antisymm hsle hsge, one_smul]

theorem rayOracle_eq_at_nonzero {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle₁ oracle₂ : (Fin d → ℝ) → (Fin d → ℝ)}
    (h₁ : IsPolytopeRayOracle P oracle₁) (h₂ : IsPolytopeRayOracle P oracle₂)
    {x : Fin d → ℝ} (hx : x ≠ 0) : oracle₁ x = oracle₂ x := by
  obtain ⟨hb, t, ht, hbt⟩ := h₁ x hx
  obtain ⟨hc, u, hu, hcu⟩ := h₂ x hx
  apply frontier_eq_of_pos_smul hconv hclosed hzero hc hb (div_pos ht hu)
  rw [hbt, hcu, smul_smul, div_mul_cancel₀ t hu.ne']

theorem rayOracle_mem_iff_coordinate_ratio {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (x : Fin d → ℝ) (j : Fin d) (hxj : x j ≠ 0) :
    x ∈ P ↔ 1 ≤ oracle x j / x j := by
  have hx : x ≠ 0 := by
    intro h
    exact hxj (congrFun h j)
  obtain ⟨hb, t, ht, hbt⟩ := horacle x hx
  have hxscale : x = t⁻¹ • oracle x := by
    rw [hbt, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  have hratio : oracle x j / x j = t := by
    rw [hbt]
    change (t * x j) / x j = t
    exact mul_div_cancel_right₀ t hxj
  rw [hratio, hxscale, nonneg_smul_frontier_mem_iff hconv hclosed hzero hb
    (inv_nonneg.mpr ht.le)]
  rw [inv_eq_one_div, div_le_iff₀ ht]
  simp only [one_mul]

theorem rayOracle_eq_self_iff_frontier {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    {x : Fin d → ℝ} (hx : x ≠ 0) :
    oracle x = x ↔ x ∈ frontier P := by
  constructor
  · intro heq
    exact heq ▸ (horacle x hx).1
  · intro hxfront
    obtain ⟨hb, t, ht, hbt⟩ := horacle x hx
    exact frontier_eq_of_pos_smul hconv hclosed hzero hxfront hb ht hbt

end Grunbaum2003

namespace Grunbaum2003.RayInner

def negativeDirection (d : ℕ) : Fin d → ℝ := (-1 : ℝ) • ones d

theorem axis_ne_zero {d : ℕ} (i : Fin d) : axis i ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp only [axis, ite_true, Pi.zero_apply] at hi
  exact one_ne_zero hi

theorem negativeDirection_ne_zero {d : ℕ} (j : Fin d) : negativeDirection d ≠ 0 := by
  intro h
  have hj := congrFun h j
  simp only [negativeDirection, ones, Pi.smul_apply, smul_eq_mul, mul_one,
    Pi.zero_apply, neg_eq_zero] at hj
  exact one_ne_zero hj

def initialDirections (d : ℕ) : List (Fin d → ℝ) :=
  (List.finRange d).map axis ++ [negativeDirection d]

theorem initialDirections_length (d : ℕ) : (initialDirections d).length = d + 1 := by
  simp only [initialDirections, List.length_append, List.length_map, List.length_finRange,
    List.length_singleton]

theorem initialDirections_nonzero {d : ℕ} (hd : 0 < d) :
    ∀ v ∈ initialDirections d, v ≠ 0 := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
    exact axis_ne_zero i
  · have hv' : v = negativeDirection d := List.mem_singleton.mp hv
    rw [hv']
    exact negativeDirection_ne_zero ⟨0, hd⟩

def positiveScale {d : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (i : Fin d) : ℝ :=
  oracle (axis i) i

def negativeScale {d : ℕ} (j : Fin d) (oracle : (Fin d → ℝ) → Fin d → ℝ) : ℝ :=
  -oracle (negativeDirection d) j

def actualSample {d : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) :
    Option (Fin d) → Fin d → ℝ
  | none => oracle (negativeDirection d)
  | some i => oracle (axis i)

def actualSampleHull {d : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) : Set (Fin d → ℝ) :=
  convexHull ℝ (Set.range (actualSample oracle))

def innerDirectionScale {d : ℕ} (j : Fin d)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (u : Fin d → ℝ) : ℝ :=
  directionScale (sampleScale (positiveScale oracle) (negativeScale j oracle)) u

theorem rayOracle_positive_samples {d : ℕ} {P : Set (Fin d → ℝ)}
    {oracle : (Fin d → ℝ) → Fin d → ℝ} (horacle : IsPolytopeRayOracle P oracle) :
    ∀ i : Fin d, 0 < positiveScale oracle i ∧
      oracle (axis i) = positiveScale oracle i • axis i := by
  intro i
  obtain ⟨_, t, ht, hanswer⟩ := horacle (axis i) (axis_ne_zero i)
  have hcoord : positiveScale oracle i = t := by
    dsimp only [positiveScale]
    rw [hanswer]
    simp only [Pi.smul_apply, smul_eq_mul, axis, ite_true, mul_one]
  exact ⟨hcoord.symm ▸ ht, hcoord.symm ▸ hanswer⟩

theorem rayOracle_negative_sample {d : ℕ} {P : Set (Fin d → ℝ)}
    {oracle : (Fin d → ℝ) → Fin d → ℝ} (horacle : IsPolytopeRayOracle P oracle)
    (j : Fin d) : 0 < negativeScale j oracle ∧
      oracle (negativeDirection d) = (-negativeScale j oracle) • ones d := by
  obtain ⟨_, s, hs, hanswer⟩ := horacle (negativeDirection d) (negativeDirection_ne_zero j)
  have hcoord : negativeScale j oracle = s := by
    dsimp only [negativeScale]
    rw [hanswer]
    simp only [negativeDirection, ones, Pi.smul_apply, smul_eq_mul, mul_one,
      mul_neg_one, neg_neg]
  refine ⟨hcoord.symm ▸ hs, ?_⟩
  rw [hcoord, hanswer, negativeDirection, smul_smul, mul_neg_one]

theorem actualSampleHull_eq {d : ℕ} {P : Set (Fin d → ℝ)}
    {oracle : (Fin d → ℝ) → Fin d → ℝ} (horacle : IsPolytopeRayOracle P oracle)
    (j : Fin d) :
    actualSampleHull oracle = sampleHull (positiveScale oracle) (negativeScale j oracle) := by
  have hfamily : actualSample oracle = samplePoint (positiveScale oracle) (negativeScale j oracle) := by
    funext i
    cases i with
    | none => exact (rayOracle_negative_sample horacle j).2
    | some i => exact (rayOracle_positive_samples horacle i).2
  change convexHull ℝ (Set.range (actualSample oracle)) = _
  rw [hfamily]
  rfl

theorem actualSampleHull_subset {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    {oracle : (Fin d → ℝ) → Fin d → ℝ} (horacle : IsPolytopeRayOracle P oracle)
    (j : Fin d) : actualSampleHull oracle ⊆ P := by
  apply convexHull_min _ hconv
  rintro _ ⟨i, rfl⟩
  cases i with
  | none => exact hclosed.frontier_subset (horacle _ (negativeDirection_ne_zero j)).1
  | some i => exact hclosed.frontier_subset (horacle _ (axis_ne_zero i)).1

theorem rayOracle_inner_sample_hull {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    {oracle : (Fin d → ℝ) → Fin d → ℝ} (horacle : IsPolytopeRayOracle P oracle)
    (j : Fin d) :
    actualSampleHull oracle ⊆ P ∧ (0 : Fin d → ℝ) ∈ actualSampleHull oracle ∧
      ∀ u : Fin d → ℝ, 0 < innerDirectionScale j oracle u ∧
        (-innerDirectionScale j oracle u) • u ∈ actualSampleHull oracle ∧
        innerDirectionScale j oracle u • u ∈ actualSampleHull oracle := by
  have ht := fun i => (rayOracle_positive_samples horacle i).1
  have hs := (rayOracle_negative_sample horacle j).1
  refine ⟨actualSampleHull_subset hconv hclosed horacle j, ?_, ?_⟩
  · rw [actualSampleHull_eq horacle j]
    exact zero_mem_sampleHull _ _ ht hs
  · intro u
    simpa only [actualSampleHull_eq horacle j, innerDirectionScale] using
      signed_direction_mem_sampleHull (positiveScale oracle) (negativeScale j oracle) ht hs u

theorem rayOracle_signed_inner_points {d : ℕ} {P : Set (Fin d → ℝ)}
    (hd : 0 < d) (hP : IsDPolytope P)
    {oracle : (Fin d → ℝ) → Fin d → ℝ} (horacle : IsPolytopeRayOracle P oracle)
    (u : Fin d → ℝ) :
    0 < innerDirectionScale ⟨0, hd⟩ oracle u ∧
      (-innerDirectionScale ⟨0, hd⟩ oracle u) • u ∈ P ∧
      innerDirectionScale ⟨0, hd⟩ oracle u • u ∈ P := by
  obtain ⟨V, hV, _, hPV⟩ := hP.1
  have hconv : Convex ℝ P := by rw [hPV]; exact convex_convexHull ℝ V
  have hclosed : IsClosed P := by rw [hPV]; exact hV.isClosed_convexHull ℝ
  have h := rayOracle_inner_sample_hull hconv hclosed horacle ⟨0, hd⟩
  exact ⟨(h.2.2 u).1, h.1 (h.2.2 u).2.1, h.1 (h.2.2 u).2.2⟩

theorem zero_dimensional_inner_points {P : Set (Fin 0 → ℝ)}
    (hP : IsDPolytope P) (u : Fin 0 → ℝ) :
    (0 : ℝ) < 1 ∧ (-1 : ℝ) • u ∈ P ∧ (1 : ℝ) • u ∈ P := by
  obtain ⟨V, _, ⟨v, hv⟩, hPV⟩ := hP.1
  have hvP : v ∈ P := by
    rw [hPV]
    exact subset_convexHull ℝ V hv
  have hm : (-1 : ℝ) • u = v := by funext i; exact Fin.elim0 i
  have hp : (1 : ℝ) • u = v := by funext i; exact Fin.elim0 i
  exact ⟨zero_lt_one, hm.symm ▸ hvP, hp.symm ▸ hvP⟩

end Grunbaum2003.RayInner

namespace Grunbaum2003.RayInnerProgram

def directionEntry (d n j : ℕ) : ℚ :=
  if n < d then if j = n then 1 else 0 else -1

def bodyLength (d : ℕ) : ℕ := (d + 1) * (d + 2)

def bodyInstruction (d k : ℕ) : RayInstruction :=
  let n := k / (d + 2)
  let j := k % (d + 2)
  if j < d then .constant (j : ℤ) (directionEntry d n j) (k + 2)
  else if j = d then .query (k + 2)
  else .shift (d : ℤ) (k + 2)

def innerSampleProgram (d : ℕ) : List RayInstruction :=
  if d = 0 then [.halt] else
    .shift (d : ℤ) 1 ::
      (List.ofFn (fun k : Fin (bodyLength d) => bodyInstruction d k.val) ++
        [.shift (-(((d + 2) * d : ℕ) : ℤ)) (bodyLength d + 2), .halt])

private theorem packed_lt {m n i j : ℕ} (hi : i < m) (hj : j < n) :
    i * n + j < m * n := by
  calc
    i * n + j < i * n + n := Nat.add_lt_add_left hj _
    _ = (i + 1) * n := (Nat.succ_mul i n).symm
    _ ≤ m * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hi)

private theorem block_div_mod (d n j : ℕ) (hj : j < d + 2) :
    (n * (d + 2) + j) / (d + 2) = n ∧
      (n * (d + 2) + j) % (d + 2) = j := by
  have hB : 0 < d + 2 := by omega
  have heq : n * (d + 2) + j = j + (d + 2) * n := by ac_rfl
  rw [heq]
  constructor
  · rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hj, Nat.zero_add]
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]

theorem initial_fetch {d : ℕ} (hd : 0 < d) :
    (innerSampleProgram d)[0]? = some (.shift (d : ℤ) 1) := by
  simp only [innerSampleProgram, if_neg (Nat.ne_of_gt hd), List.getElem?_cons_zero]

theorem block_fetch {d n j : ℕ} (hd : 0 < d) (hn : n < d + 1) (hj : j < d + 2) :
    (innerSampleProgram d)[1 + n * (d + 2) + j]? =
      some (if j < d then .constant (j : ℤ) (directionEntry d n j) (n * (d + 2) + j + 2)
        else if j = d then .query (n * (d + 2) + j + 2)
        else .shift (d : ℤ) (n * (d + 2) + j + 2)) := by
  have hk : n * (d + 2) + j < bodyLength d := packed_lt hn hj
  have hidx : 1 + n * (d + 2) + j = (n * (d + 2) + j) + 1 := by omega
  rw [hidx]
  simp only [innerSampleProgram, if_neg (Nat.ne_of_gt hd), List.getElem?_cons_succ,
    List.getElem?_append, List.length_ofFn, hk, ↓reduceIte,
    List.getElem?_ofFn, ↓reduceDIte, bodyInstruction,
    (block_div_mod d n j hj).1, (block_div_mod d n j hj).2]

theorem final_shift_fetch {d : ℕ} (hd : 0 < d) :
    (innerSampleProgram d)[1 + bodyLength d]? =
      some (.shift (-(((d + 2) * d : ℕ) : ℤ)) (bodyLength d + 2)) := by
  rw [show 1 + bodyLength d = bodyLength d + 1 by omega]
  simp only [innerSampleProgram, if_neg (Nat.ne_of_gt hd), List.getElem?_cons_succ,
    List.getElem?_append, List.length_ofFn, lt_self_iff_false, ↓reduceIte,
    Nat.sub_self, List.getElem?_cons_zero]

theorem final_halt_fetch {d : ℕ} (hd : 0 < d) :
    (innerSampleProgram d)[bodyLength d + 2]? = some .halt := by
  have hn : ¬ bodyLength d + 1 < bodyLength d := by omega
  have hs : bodyLength d + 1 - bodyLength d = 1 := by omega
  simp only [innerSampleProgram, if_neg (Nat.ne_of_gt hd), List.getElem?_cons_succ,
    List.getElem?_append, List.length_ofFn, hn, ↓reduceIte, hs,
    List.getElem?_cons_succ, List.getElem?_cons_zero]

private theorem run_add {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration) :
    rayMachineRun program oracle (a + b) c =
      (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b) := by
  induction a generalizing c with
  | zero => simp only [Nat.zero_add, rayMachineRun, Option.bind_some]
  | succ a ih => simp only [Nat.succ_add, rayMachineRun, ih, Option.bind_assoc]

private theorem run_succ_last {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (a : ℕ) (c : RayConfiguration) :
    rayMachineRun program oracle (a + 1) c =
      (rayMachineRun program oracle a c).bind (rayMachineStep program oracle) := by
  rw [run_add program oracle a 1 c]
  simp only [rayMachineRun, Option.bind_fun_some]

private theorem run_constants {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (base : ℕ) (h : ℤ)
    (values : Fin d → ℚ) (c : RayConfiguration) (hpc : c.pc = base) (hhead : c.head = h)
    (hfetch : ∀ i : Fin d, program[base + i.val]? =
      some (.constant (i.val : ℤ) (values i) (base + i.val + 1))) :
    ∃ c' : RayConfiguration, rayMachineRun program oracle d c = some c' ∧
      c'.pc = base + d ∧ c'.head = h ∧ c'.queries = c.queries ∧
      (∀ i : Fin d, c'.tape (h + (i.val : ℤ)) = (values i : ℝ)) ∧
      ∀ z : ℤ, (z < h ∨ h + (d : ℤ) ≤ z) → c'.tape z = c.tape z := by
  classical
  have hrun : ∀ n, n ≤ d → ∃ c' : RayConfiguration,
      rayMachineRun program oracle n c = some c' ∧
      c'.pc = base + n ∧ c'.head = h ∧ c'.queries = c.queries ∧
      (∀ i : Fin d, i.val < n → c'.tape (h + (i.val : ℤ)) = (values i : ℝ)) ∧
      ∀ z : ℤ, (z < h ∨ h + (d : ℤ) ≤ z) → c'.tape z = c.tape z := by
    intro n
    induction n with
    | zero =>
        intro _
        refine ⟨c, rfl, ?_, hhead, rfl, ?_, ?_⟩
        · simpa only [Nat.add_zero] using hpc
        · intro i hi
          omega
        · intro _ _
          rfl
    | succ n ih =>
        intro hn
        obtain ⟨b, hb, hbpc, hbhead, hbq, hbtape, hbframe⟩ := ih (by omega)
        have hnd : n < d := by omega
        let b' : RayConfiguration :=
          { b with
            pc := base + n + 1
            tape := Function.update b.tape (h + (n : ℤ)) (values ⟨n, hnd⟩ : ℝ) }
        have hinst : program[b.pc]? = some
            (.constant (n : ℤ) (values ⟨n, hnd⟩) (base + n + 1)) := by
          rw [hbpc]
          exact hfetch ⟨n, hnd⟩
        have hstep : rayMachineStep program oracle b = some b' := by
          simp only [rayMachineStep, hinst, hbhead, b']
        refine ⟨b', ?_, ?_, hbhead, hbq, ?_, ?_⟩
        · rw [run_succ_last, hb, Option.bind_some, hstep]
        · change base + n + 1 = base + (n + 1)
          omega
        · intro i hi
          by_cases hin : i.val = n
          · have haddr : h + (i.val : ℤ) = h + (n : ℤ) := by omega
            change Function.update b.tape (h + (n : ℤ))
              (values ⟨n, hnd⟩ : ℝ) (h + (i.val : ℤ)) = _
            rw [haddr, Function.update_self]
            exact congrArg (fun j : Fin d => (values j : ℝ)) (Fin.ext hin.symm)
          · have hi' : i.val < n := by omega
            have haddr : h + (i.val : ℤ) ≠ h + (n : ℤ) := by omega
            simpa only [b', Function.update_of_ne haddr] using hbtape i hi'
        · intro z hz
          have haddr : z ≠ h + (n : ℤ) := by omega
          simpa only [b', Function.update_of_ne haddr] using hbframe z hz
  obtain ⟨c', hc', hpc', hhead', hq', htape', hframe'⟩ := hrun d le_rfl
  exact ⟨c', hc', hpc', hhead', hq', fun i => htape' i i.isLt, hframe'⟩

private def writeVector {d : ℕ} (tape : ℤ → ℝ) (h : ℤ) (v : Fin d → ℝ) (z : ℤ) : ℝ :=
  if hz : 0 ≤ z - h ∧ z - h < (d : ℤ) then
    v ⟨(z - h).toNat, by omega⟩ else tape z

private theorem writeVector_at {d : ℕ} (tape : ℤ → ℝ) (h : ℤ) (v : Fin d → ℝ)
    (i : Fin d) : writeVector tape h v (h + (i.val : ℤ)) = v i := by
  have hi : 0 ≤ h + (i.val : ℤ) - h ∧ h + (i.val : ℤ) - h < (d : ℤ) := by omega
  rw [writeVector, dif_pos hi]
  congr 1
  apply Fin.ext
  simp only [add_sub_cancel_left, Int.toNat_natCast]

private theorem writeVector_frame {d : ℕ} (tape : ℤ → ℝ) (h : ℤ) (v : Fin d → ℝ)
    (z : ℤ) (hz : z < h ∨ h + (d : ℤ) ≤ z) : writeVector tape h v z = tape z := by
  have hn : ¬ (0 ≤ z - h ∧ z - h < (d : ℤ)) := by omega
  simp only [writeVector, dif_neg hn]

private theorem run_sample_block {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (base : ℕ) (h : ℤ)
    (values : Fin d → ℚ) (c : RayConfiguration) (hpc : c.pc = base) (hhead : c.head = h)
    (hfetch : ∀ i : Fin d, program[base + i.val]? =
      some (.constant (i.val : ℤ) (values i) (base + i.val + 1)))
    (hquery : program[base + d]? = some (.query (base + d + 1)))
    (hshift : program[base + d + 1]? = some (.shift (d : ℤ) (base + d + 2)))
    (hnonzero : (fun i : Fin d => (values i : ℝ)) ≠ 0) :
    ∃ c' : RayConfiguration, rayMachineRun program oracle (d + 2) c = some c' ∧
      c'.pc = base + d + 2 ∧ c'.head = h + (d : ℤ) ∧ c'.queries = c.queries + 1 ∧
      (∀ i : Fin d, c'.tape (h + (i.val : ℤ)) = oracle (fun j => (values j : ℝ)) i) ∧
      ∀ z : ℤ, (z < h ∨ h + (d : ℤ) ≤ z) → c'.tape z = c.tape z := by
  classical
  obtain ⟨b, hb, hbpc, hbhead, hbq, hbtape, hbframe⟩ :=
    run_constants program oracle base h values c hpc hhead hfetch
  let v : Fin d → ℝ := fun i => (values i : ℝ)
  have hv : (fun i : Fin d => b.tape (h + (i.val : ℤ))) = v := funext hbtape
  have hvne : v ≠ 0 := hnonzero
  let b' : RayConfiguration :=
    { b with
      pc := base + d + 1
      queries := c.queries + 1
      tape := writeVector b.tape h (oracle v) }
  let b'' : RayConfiguration :=
    { b' with
      pc := base + d + 2
      head := h + (d : ℤ) }
  have hstepQuery : rayMachineStep program oracle b = some b' := by
    simp only [rayMachineStep, hbpc, hquery, hbhead, hv, hvne, ↓reduceIte,
      hbq, b']
    rfl
  have hstepShift : rayMachineStep program oracle b' = some b'' := by
    simp only [rayMachineStep, b', hshift, b'', hbhead]
  have htwo : rayMachineRun program oracle 2 b = some b'' := by
    simp only [rayMachineRun, hstepQuery, hstepShift, Option.bind_some]
  refine ⟨b'', ?_, rfl, rfl, rfl, ?_, ?_⟩
  · rw [run_add program oracle d 2 c, hb, Option.bind_some, htwo]
  · intro i
    exact writeVector_at b.tape h (oracle v) i
  · intro z hz
    change writeVector b.tape h (oracle v) z = c.tape z
    rw [writeVector_frame b.tape h (oracle v) z hz]
    exact hbframe z hz

def queryVector (d n : ℕ) : Fin d → ℝ := fun i => (directionEntry d n i.val : ℝ)

theorem queryVector_axis {d : ℕ} (i : Fin d) :
    queryVector d i.val = RayInner.axis i := by
  funext j
  by_cases hj : j.val = i.val
  · have hji : j = i := Fin.ext hj
    subst j
    simp only [queryVector, directionEntry, if_pos i.isLt, ite_true,
      Rat.cast_one, RayInner.axis]
  · have hji : j ≠ i := fun h => hj (congrArg Fin.val h)
    simp only [queryVector, directionEntry, if_pos i.isLt, if_neg hj,
      Rat.cast_zero, RayInner.axis, if_neg hji]

theorem queryVector_pole (d : ℕ) :
    queryVector d d = RayInner.negativeDirection d := by
  funext j
  simp only [queryVector, directionEntry, lt_self_iff_false, ↓reduceIte,
    Rat.cast_neg, Rat.cast_one, RayInner.negativeDirection, RayInner.ones,
    Pi.smul_apply, smul_eq_mul, mul_one]

private theorem queryVector_nonzero {d n : ℕ} (hd : 0 < d) (hn : n < d + 1) :
    queryVector d n ≠ 0 := by
  by_cases hnd : n < d
  · exact (queryVector_axis ⟨n, hnd⟩).symm ▸ RayInner.axis_ne_zero ⟨n, hnd⟩
  · have heq : n = d := by omega
    rw [heq, queryVector_pole]
    exact RayInner.negativeDirection_ne_zero ⟨0, hd⟩

private theorem run_initial_block {d n : ℕ} (hd : 0 < d) (hn : n < d + 1)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (c : RayConfiguration)
    (hpc : c.pc = 1 + n * (d + 2)) (hhead : c.head = (((n + 1) * d : ℕ) : ℤ)) :
    ∃ c' : RayConfiguration,
      rayMachineRun (innerSampleProgram d) oracle (d + 2) c = some c' ∧
      c'.pc = 1 + (n + 1) * (d + 2) ∧
      c'.head = (((n + 2) * d : ℕ) : ℤ) ∧ c'.queries = c.queries + 1 ∧
      (∀ i : Fin d, c'.tape ((((n + 1) * d : ℕ) : ℤ) + (i.val : ℤ)) =
        oracle (queryVector d n) i) ∧
      ∀ z : ℤ, (z < (((n + 1) * d : ℕ) : ℤ) ∨
        (((n + 2) * d : ℕ) : ℤ) ≤ z) → c'.tape z = c.tape z := by
  have hconst : ∀ i : Fin d,
      (innerSampleProgram d)[(1 + n * (d + 2)) + i.val]? =
        some (.constant (i.val : ℤ) (directionEntry d n i.val)
          ((1 + n * (d + 2)) + i.val + 1)) := by
    intro i
    have h := block_fetch hd hn (show i.val < d + 2 by omega)
    have hnext : n * (d + 2) + i.val + 2 = (1 + n * (d + 2)) + i.val + 1 := by omega
    simpa only [if_pos i.isLt, hnext] using h
  have hquery : (innerSampleProgram d)[(1 + n * (d + 2)) + d]? =
      some (.query ((1 + n * (d + 2)) + d + 1)) := by
    have h := block_fetch hd hn (show d < d + 2 by omega)
    have hnext : n * (d + 2) + d + 2 = (1 + n * (d + 2)) + d + 1 := by omega
    simpa only [lt_self_iff_false, ↓reduceIte, hnext] using h
  have hshift : (innerSampleProgram d)[(1 + n * (d + 2)) + d + 1]? =
      some (.shift (d : ℤ) ((1 + n * (d + 2)) + d + 2)) := by
    have h := block_fetch hd hn (show d + 1 < d + 2 by omega)
    have hlt : ¬ d + 1 < d := by omega
    have hne : d + 1 ≠ d := by omega
    have hidx : 1 + n * (d + 2) + (d + 1) = (1 + n * (d + 2)) + d + 1 := by omega
    have hnext : n * (d + 2) + (d + 1) + 2 = (1 + n * (d + 2)) + d + 2 := by omega
    simpa only [if_neg hlt, if_neg hne, hidx, hnext] using h
  obtain ⟨b, hb, hbpc, hbhead, hbq, hbtape, hbframe⟩ :=
    run_sample_block (innerSampleProgram d) oracle (1 + n * (d + 2))
      (((n + 1) * d : ℕ) : ℤ) (fun i => directionEntry d n i.val)
      c hpc hhead hconst hquery hshift (queryVector_nonzero hd hn)
  have hpc' : (1 + n * (d + 2)) + d + 2 = 1 + (n + 1) * (d + 2) := by
    rw [Nat.succ_mul]
    omega
  have hhead' : (((n + 1) * d : ℕ) : ℤ) + (d : ℤ) = (((n + 2) * d : ℕ) : ℤ) := by
    exact_mod_cast (show (n + 1) * d + d = (n + 2) * d by ring)
  refine ⟨b, hb, hbpc.trans hpc', hbhead.trans hhead', hbq, hbtape, ?_⟩
  intro z hz
  apply hbframe
  simpa only [hhead'] using hz

private theorem run_blocks {d : ℕ} (hd : 0 < d)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (c : RayConfiguration)
    (hpc : c.pc = 1) (hhead : c.head = (d : ℤ)) :
    ∀ n, n ≤ d + 1 → ∃ b : RayConfiguration,
      rayMachineRun (innerSampleProgram d) oracle (n * (d + 2)) c = some b ∧
      b.pc = 1 + n * (d + 2) ∧ b.head = (((n + 1) * d : ℕ) : ℤ) ∧
      b.queries = c.queries + n ∧
      (∀ i : Fin (d + 1), i.val < n → ∀ j : Fin d,
        b.tape ((((i.val + 1) * d + j.val : ℕ) : ℤ)) =
          oracle (queryVector d i.val) j) ∧
      ∀ z : ℤ, (z < (d : ℤ) ∨ (((n + 1) * d : ℕ) : ℤ) ≤ z) →
        b.tape z = c.tape z := by
  intro n
  induction n with
  | zero =>
      intro _
      refine ⟨c, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [Nat.zero_mul, rayMachineRun]
      · simpa only [Nat.zero_mul, Nat.add_zero] using hpc
      · simpa only [Nat.zero_add, Nat.one_mul] using hhead
      · simp only [Nat.add_zero]
      · intro i hi
        omega
      · intro _ _
        rfl
  | succ n ih =>
      intro hn
      obtain ⟨b, hb, hbpc, hbhead, hbq, hbtape, hbframe⟩ := ih (by omega)
      have hnd : n < d + 1 := by omega
      obtain ⟨b', hb', hbpc', hbhead', hbq', hbtape', hbframe'⟩ :=
        run_initial_block hd hnd oracle b hbpc hbhead
      refine ⟨b', ?_, hbpc', hbhead', ?_, ?_, ?_⟩
      · rw [Nat.succ_mul, run_add, hb, Option.bind_some, hb']
      · rw [hbq', hbq]
        omega
      · intro i hi j
        by_cases hin : i.val = n
        · simpa only [hin, Nat.cast_add] using hbtape' j
        · have hilt : i.val < n := by omega
          have haddrNat : (i.val + 1) * d + j.val < (n + 1) * d :=
            packed_lt (Nat.succ_lt_succ hilt) j.isLt
          have haddr : ((((i.val + 1) * d + j.val : ℕ) : ℤ)) <
              (((n + 1) * d : ℕ) : ℤ) := by exact_mod_cast haddrNat
          rw [hbframe' _ (Or.inl haddr)]
          exact hbtape i hilt j
      · intro z hz
        have hlowNat : d ≤ (n + 1) * d := by
          simpa only [Nat.one_mul] using
            Nat.mul_le_mul_right d (show 1 ≤ n + 1 by omega)
        have hstepNat : (n + 1) * d ≤ (n + 2) * d :=
          Nat.mul_le_mul_right d (by omega)
        have hlow : (d : ℤ) ≤ (((n + 1) * d : ℕ) : ℤ) := by exact_mod_cast hlowNat
        have hstep : (((n + 1) * d : ℕ) : ℤ) ≤ (((n + 2) * d : ℕ) : ℤ) := by
          exact_mod_cast hstepNat
        rcases hz with hz | hz
        · rw [hbframe' z (Or.inl (lt_of_lt_of_le hz hlow))]
          exact hbframe z (Or.inl hz)
        · rw [hbframe' z (Or.inr hz)]
          exact hbframe z (Or.inr (hstep.trans hz))

theorem innerSampleProgram_correct {d : ℕ} (hd : 0 < d)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (tape : ℤ → ℝ) (q : ℕ) :
    ∃ c : RayConfiguration,
      rayMachineRun (innerSampleProgram d) oracle (bodyLength d + 2)
        ⟨0, 0, tape, q⟩ = some c ∧
      c.pc = bodyLength d + 2 ∧
      (innerSampleProgram d)[c.pc]? = some .halt ∧ c.head = 0 ∧
      c.queries = q + (d + 1) ∧
      (∀ i : Fin (d + 1), ∀ j : Fin d,
        c.tape ((((i.val + 1) * d + j.val : ℕ) : ℤ)) =
          oracle (queryVector d i.val) j) ∧
      ∀ z : ℤ, (z < (d : ℤ) ∨ (((d + 2) * d : ℕ) : ℤ) ≤ z) →
        c.tape z = tape z := by
  let start : RayConfiguration := ⟨1, (d : ℤ), tape, q⟩
  have hfirst : rayMachineStep (innerSampleProgram d) oracle ⟨0, 0, tape, q⟩ = some start := by
    simp only [rayMachineStep, initial_fetch hd, zero_add, start]
  have hrunfirst : rayMachineRun (innerSampleProgram d) oracle 1
      ⟨0, 0, tape, q⟩ = some start := by
    simp only [rayMachineRun, hfirst, Option.bind_some]
  obtain ⟨b, hb, hbpc, hbhead, hbq, hbtape, hbframe⟩ :=
    run_blocks hd oracle start rfl rfl (d + 1) le_rfl
  let finish : RayConfiguration :=
    { b with
      pc := bodyLength d + 2
      head := 0 }
  have hbpc' : b.pc = 1 + bodyLength d := hbpc
  have hbhead' : b.head = (((d + 2) * d : ℕ) : ℤ) := hbhead
  have hfinal : rayMachineStep (innerSampleProgram d) oracle b = some finish := by
    simp only [rayMachineStep, hbpc', final_shift_fetch hd, hbhead', add_neg_cancel, finish]
  have hafter : rayMachineRun (innerSampleProgram d) oracle (bodyLength d + 1) start =
      some finish := by
    change rayMachineRun (innerSampleProgram d) oracle (((d + 1) * (d + 2)) + 1) start = _
    rw [run_succ_last, hb, Option.bind_some, hfinal]
  have htotal : rayMachineRun (innerSampleProgram d) oracle (bodyLength d + 2)
      ⟨0, 0, tape, q⟩ = some finish := by
    rw [show bodyLength d + 2 = 1 + (bodyLength d + 1) by omega,
      run_add, hrunfirst, Option.bind_some, hafter]
  refine ⟨finish, htotal, rfl, final_halt_fetch hd, rfl, ?_, ?_, ?_⟩
  · exact hbq
  · intro i j
    exact hbtape i i.isLt j
  · intro z hz
    exact hbframe z hz

theorem all_initial_query_vectors_nonzero {d : ℕ} (hd : 0 < d) :
    ∀ i : Fin (d + 1), queryVector d i.val ≠ 0 :=
  fun i => queryVector_nonzero hd i.isLt

theorem innerSampleProgram_zero
    (oracle : (Fin 0 → ℝ) → Fin 0 → ℝ) (tape : ℤ → ℝ) (q : ℕ) :
    rayMachineRun (innerSampleProgram 0) oracle 0 ⟨0, 0, tape, q⟩ =
      some ⟨0, 0, tape, q⟩ ∧
      (innerSampleProgram 0)[0]? = some .halt := ⟨rfl, rfl⟩

theorem stored_scales {d : ℕ} (hd : 0 < d)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (c : RayConfiguration)
    (hstored : ∀ i : Fin (d + 1), ∀ j : Fin d,
      c.tape ((((i.val + 1) * d + j.val : ℕ) : ℤ)) =
        oracle (queryVector d i.val) j) :
    (∀ i : Fin d, c.tape ((((i.val + 1) * d + i.val : ℕ) : ℤ)) =
      RayInner.positiveScale oracle i) ∧
      -c.tape ((((d + 1) * d : ℕ) : ℤ)) =
        RayInner.negativeScale ⟨0, hd⟩ oracle := by
  constructor
  · intro i
    simpa only [Fin.val_castSucc, queryVector_axis, RayInner.positiveScale] using
      hstored i.castSucc i
  · have h := hstored (Fin.last d) ⟨0, hd⟩
    simp only [Fin.val_last, queryVector_pole, Nat.add_zero] at h
    exact congrArg Neg.neg h

end Grunbaum2003.RayInnerProgram

namespace Grunbaum2003

theorem rayMachine_inner_simplex_and_signed_direction_program :
    ∃ (axis : ∀ {d : ℕ}, Fin d → Fin d → ℝ)
      (negativeDirection : ∀ d : ℕ, Fin d → ℝ)
      (positiveScale : ∀ {d : ℕ}, ((Fin d → ℝ) → Fin d → ℝ) → Fin d → ℝ)
      (negativeScale : ∀ {d : ℕ}, Fin d → ((Fin d → ℝ) → Fin d → ℝ) → ℝ)
      (sampleScale : ∀ {d : ℕ}, (Fin d → ℝ) → ℝ → ℝ)
      (directionScale : ∀ {d : ℕ}, ℝ → (Fin d → ℝ) → ℝ)
      (innerSampleProgram : ℕ → List RayInstruction)
      (queryVector : ∀ d : ℕ, ℕ → Fin d → ℝ),
      (∀ (d : ℕ) (i j : Fin d), axis i j = if j = i then 1 else 0) ∧
      (∀ (d : ℕ) (j : Fin d), negativeDirection d j = -1) ∧
      (∀ (d : ℕ) (oracle : (Fin d → ℝ) → Fin d → ℝ) (i : Fin d),
        positiveScale oracle i = oracle (axis i) i) ∧
      (∀ (d : ℕ) (j : Fin d) (oracle : (Fin d → ℝ) → Fin d → ℝ),
        negativeScale j oracle = -oracle (negativeDirection d) j) ∧
      (∀ (d : ℕ) (t : Fin d → ℝ) (s : ℝ),
        sampleScale t s = (1 + s⁻¹ + ∑ i, (t i)⁻¹)⁻¹) ∧
      (∀ (d : ℕ) (a : ℝ) (u : Fin d → ℝ),
        directionScale a u = a / (1 + ∑ i, |u i|)) ∧
      (∀ (d : ℕ) (hd : 0 < d) (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
        (oracle : (Fin d → ℝ) → Fin d → ℝ) (horacle : IsPolytopeRayOracle P oracle)
        (u : Fin d → ℝ),
        let a := directionScale (sampleScale (positiveScale oracle) (negativeScale ⟨0, hd⟩ oracle)) u
        0 < a ∧ (-a) • u ∈ P ∧ a • u ∈ P) ∧
      (∀ (d : ℕ) (hd : 0 < d) (oracle : (Fin d → ℝ) → Fin d → ℝ) (tape : ℤ → ℝ) (q : ℕ),
        ∃ c : RayConfiguration,
          rayMachineRun (innerSampleProgram d) oracle ((d + 1) * (d + 2) + 2)
            {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
          c.pc = (d + 1) * (d + 2) + 2 ∧
          (innerSampleProgram d)[c.pc]? = some .halt ∧
          c.head = 0 ∧
          c.queries = q + (d + 1) ∧
          (∀ i : Fin (d + 1), ∀ j : Fin d,
            c.tape ((((i.val + 1) * d + j.val : ℕ) : ℤ)) = oracle (queryVector d i.val) j) ∧
          (∀ i : Fin d,
            c.tape ((((i.val + 1) * d + i.val : ℕ) : ℤ)) = positiveScale oracle i) ∧
          (-c.tape ((((d + 1) * d : ℕ) : ℤ)) = negativeScale ⟨0, hd⟩ oracle) ∧
          (∀ z : ℤ, (z < (d : ℤ) ∨ (((d + 2) * d : ℕ) : ℤ) ≤ z) → c.tape z = tape z)) := by
  refine ⟨@RayInner.axis, RayInner.negativeDirection, @RayInner.positiveScale,
    @RayInner.negativeScale, @RayInner.sampleScale, @RayInner.directionScale,
    RayInnerProgram.innerSampleProgram, RayInnerProgram.queryVector,
    fun _ _ _ => rfl, ?_, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ => rfl, fun _ _ _ => rfl, ?_, ?_⟩
  · intro d j
    change (-1 : ℝ) * 1 = -1
    ring
  · intro d hd P hP oracle horacle u
    exact RayInner.rayOracle_signed_inner_points hd hP horacle u
  · intro d hd oracle tape q
    obtain ⟨c, hrun, hpc, hhalt, hhead, hq, hstored, hframe⟩ :=
      RayInnerProgram.innerSampleProgram_correct hd oracle tape q
    obtain ⟨hpos, hneg⟩ := RayInnerProgram.stored_scales hd oracle c hstored
    exact ⟨c, hrun, hpc, hhalt, hhead, hq, hstored, hpos, hneg, hframe⟩

end Grunbaum2003
end

theorem solution :
    ∃ (axis : ∀ {d : ℕ}, Fin d → Fin d → ℝ)
      (negativeDirection : ∀ d : ℕ, Fin d → ℝ)
      (positiveScale : ∀ {d : ℕ}, ((Fin d → ℝ) → Fin d → ℝ) → Fin d → ℝ)
      (negativeScale : ∀ {d : ℕ}, Fin d → ((Fin d → ℝ) → Fin d → ℝ) → ℝ)
      (sampleScale : ∀ {d : ℕ}, (Fin d → ℝ) → ℝ → ℝ)
      (directionScale : ∀ {d : ℕ}, ℝ → (Fin d → ℝ) → ℝ)
      (innerSampleProgram : ℕ → List Grunbaum2003.RayInstruction)
      (queryVector : ∀ d : ℕ, ℕ → Fin d → ℝ),
      (∀ (d : ℕ) (i j : Fin d), axis i j = if j = i then 1 else 0) ∧
      (∀ (d : ℕ) (j : Fin d), negativeDirection d j = -1) ∧
      (∀ (d : ℕ) (oracle : (Fin d → ℝ) → Fin d → ℝ) (i : Fin d),
        positiveScale oracle i = oracle (axis i) i) ∧
      (∀ (d : ℕ) (j : Fin d) (oracle : (Fin d → ℝ) → Fin d → ℝ),
        negativeScale j oracle = -oracle (negativeDirection d) j) ∧
      (∀ (d : ℕ) (t : Fin d → ℝ) (s : ℝ),
        sampleScale t s = (1 + s⁻¹ + ∑ i, (t i)⁻¹)⁻¹) ∧
      (∀ (d : ℕ) (a : ℝ) (u : Fin d → ℝ),
        directionScale a u = a / (1 + ∑ i, |u i|)) ∧
      (∀ (d : ℕ) (hd : 0 < d) (P : Set (Fin d → ℝ)) (hP : Grunbaum2003.IsDPolytope P)
        (oracle : (Fin d → ℝ) → Fin d → ℝ) (horacle : Grunbaum2003.IsPolytopeRayOracle P oracle)
        (u : Fin d → ℝ),
        let a := directionScale (sampleScale (positiveScale oracle) (negativeScale ⟨0, hd⟩ oracle)) u
        0 < a ∧ (-a) • u ∈ P ∧ a • u ∈ P) ∧
      (∀ (d : ℕ) (hd : 0 < d) (oracle : (Fin d → ℝ) → Fin d → ℝ) (tape : ℤ → ℝ) (q : ℕ),
        ∃ c : Grunbaum2003.RayConfiguration,
          Grunbaum2003.rayMachineRun (innerSampleProgram d) oracle ((d + 1) * (d + 2) + 2)
            {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
          c.pc = (d + 1) * (d + 2) + 2 ∧
          (innerSampleProgram d)[c.pc]? = some .halt ∧
          c.head = 0 ∧
          c.queries = q + (d + 1) ∧
          (∀ i : Fin (d + 1), ∀ j : Fin d,
            c.tape ((((i.val + 1) * d + j.val : ℕ) : ℤ)) = oracle (queryVector d i.val) j) ∧
          (∀ i : Fin d,
            c.tape ((((i.val + 1) * d + i.val : ℕ) : ℤ)) = positiveScale oracle i) ∧
          (-c.tape ((((d + 1) * d : ℕ) : ℤ)) = negativeScale ⟨0, hd⟩ oracle) ∧
          (∀ z : ℤ, (z < (d : ℤ) ∨ (((d + 2) * d : ℕ) : ℤ) ≤ z) → c.tape z = tape z)) :=
  Grunbaum2003.rayMachine_inner_simplex_and_signed_direction_program
