-- Prove2me | solution 1 for OAI.TriangularBilliards.irrational_triangle_billiard
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T18:02:16.249598+00:00
-- url     : https://prove2.me/submissions/8746c4e4-9c26-4052-8a53-8f9aca65d348

import Mathlib
import Definitions.Def_IrrationalTriangleBilliard

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
alias Finset.prod_le_prod₀ := Finset.prod_le_prod
alias Finset.prod_le_one₀ := Finset.prod_le_one
alias Finset.one_le_prod₀ := Finset.one_le_prod
alias List.Nodup.getElem?_inj := List.getElem?_inj
end OAICompat434

universe uIota uAlpha uBeta uE uG uGamma uF uA uH uC uKappa

section
section
namespace OAI

/-!
The phase space is represented in the ambient plane × circle, with measure
supported on the interior of the triangle. Values on side-collision states
at a fixed time are immaterial to the modulo-null-set conclusion. The
trajectories themselves include the collisions and impose specular reflection.
-/

open MeasureTheory Set
open scoped ENNReal symmDiff

noncomputable section

namespace TriangularBilliards

namespace Triangle

end Triangle

end TriangularBilliards
end

end OAI
end
end

section
section
namespace OAI

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
namespace TriangularBilliards

/-! Elementary facts about complete specular trajectories. -/

lemma reflect_add (e v w : ℂ) : reflect e (v + w) = reflect e v + reflect e w := by
  simp [reflect, mul_add]

lemma reflect_real_smul (e v : ℂ) (r : ℝ) :
    reflect e (r • v) = r • reflect e v := by
  simp only [reflect, star_smul, star_trivial, mul_smul_comm]

lemma reflect_involutive {e : ℂ} (he : e ≠ 0) (v : ℂ) :
    reflect e (reflect e v) = v := by
  simp only [reflect, star_mul', star_div₀, star_star]
  field_simp [he, star_ne_zero.mpr he]

lemma reflect_norm {e : ℂ} (he : e ≠ 0) (v : ℂ) : ‖reflect e v‖ = ‖v‖ := by
  simp [reflect, norm_ne_zero_iff.mpr he]

lemma reflect_tangent {e : ℂ} (he : e ≠ 0) : reflect e e = e := by
  exact div_mul_cancel₀ e (star_ne_zero.mpr he)

lemma reflect_normal {e : ℂ} (he : e ≠ 0) :
    reflect e (Complex.I * e) = -(Complex.I * e) := by
  have h : star e ≠ 0 := star_ne_zero.mpr he
  simp only [reflect, star_mul', Complex.star_def, Complex.conj_I]
  have hc : (starRingEnd ℂ) e ≠ 0 := by simpa only [Complex.star_def] using h
  field_simp [hc]

namespace FlightChain

lemma exists_flight {Q : Triangle} {z : Phase} (c : FlightChain Q z) (t : ℝ) :
    ∃ n : ℤ, c.time n ≤ t ∧ t < c.time (n + 1) := by
  let S : Set ℤ := {n | c.time n ≤ t}
  have hne : S.Nonempty := by
    obtain ⟨n, hn⟩ := c.unbounded_below t
    exact ⟨n, hn.le⟩
  have hbd : BddAbove S := by
    obtain ⟨m, hm⟩ := c.unbounded_above t
    refine ⟨m, ?_⟩
    intro n hn
    exact (c.increasing.lt_iff_lt.mp (lt_of_le_of_lt hn hm)).le
  refine ⟨sSup S, Int.csSup_mem hne hbd, ?_⟩
  by_contra h
  have hsucc : sSup S + 1 ∈ S := le_of_not_gt h
  have hh := le_csSup hbd hsucc
  omega

lemma flight_index_unique {Q : Triangle} {z : Phase} (c : FlightChain Q z)
    {t : ℝ} {n m : ℤ} (hn : c.time n ≤ t ∧ t < c.time (n + 1))
    (hm : c.time m ≤ t ∧ t < c.time (m + 1)) : n = m := by
  apply le_antisymm
  · by_contra h
    have hmn : m + 1 ≤ n := by omega
    have := c.increasing.monotone hmn
    linarith [hn.1, hm.2]
  · by_contra h
    have hnm : n + 1 ≤ m := by omega
    have := c.increasing.monotone hnm
    linarith [hm.1, hn.2]

lemma at_of_flight {Q : Triangle} {z : Phase} (c : FlightChain Q z)
    {t : ℝ} {n : ℤ} (hn : c.time n ≤ t ∧ t < c.time (n + 1)) :
    c.at t = (c.point n + (t - c.time n) • (c.direction n : ℂ), c.direction n) := by
  classical
  have hex := c.exists_flight t
  have hi := c.flight_index_unique (Classical.choose_spec hex) hn
  simp only [FlightChain.at, dite_eq_left hex, hi]

lemma at_zero {Q : Triangle} {z : Phase} (c : FlightChain Q z) : c.at 0 = z := by
  have h : c.time 0 ≤ 0 ∧ 0 < c.time (0 + 1) := by
    simpa using And.intro c.zero_before.le c.zero_after
  rw [c.at_of_flight h]
  apply Prod.ext
  · simpa using c.start_point.symm
  · exact c.start_direction.symm

lemma initial_inside {Q : Triangle} {z : Phase} (c : FlightChain Q z) : z.1 ∈ Q.table := by
  have h := c.inside 0 0 c.zero_before (by simpa using c.zero_after)
  rw [c.start_point]
  simpa only [zero_sub] using h

lemma position_at_interior {Q : Triangle} {z : Phase} (c : FlightChain Q z)
    {t : ℝ} {n : ℤ} (h₁ : c.time n < t) (h₂ : t < c.time (n + 1)) :
    (c.at t).1 ∈ Q.table := by
  rw [c.at_of_flight ⟨h₁.le, h₂⟩]
  exact c.inside n t h₁ h₂

lemma constant_direction_on_flight {Q : Triangle} {z : Phase} (c : FlightChain Q z)
    {t : ℝ} {n : ℤ} (h : c.time n ≤ t ∧ t < c.time (n + 1)) :
    (c.at t).2 = c.direction n := by
  rw [c.at_of_flight h]

lemma unit_speed_on_flight {Q : Triangle} {z : Phase} (c : FlightChain Q z)
    {s t : ℝ} {n : ℤ} (hs : c.time n ≤ s ∧ s < c.time (n + 1))
    (ht : c.time n ≤ t ∧ t < c.time (n + 1)) :
    dist (c.at s).1 (c.at t).1 = |s - t| := by
  rw [c.at_of_flight hs, c.at_of_flight ht]
  simp only [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul]
  rw [norm_smul, Circle.norm_coe]
  simp [Real.norm_eq_abs]

end FlightChain

lemma billiardFlow_zero (Q : Triangle) (z : Phase) : billiardFlow Q 0 z = z := by
  classical
  by_cases h : Nonempty (FlightChain Q z)
  · simp only [billiardFlow, dite_eq_left h, FlightChain.at_zero]
  · simp only [billiardFlow, dite_eq_right h]

namespace Triangle

lemma isOpen_table (Q : Triangle) : IsOpen Q.table := isOpen_interior

lemma measurableSet_table (Q : Triangle) : MeasurableSet Q.table :=
  Q.isOpen_table.measurableSet

lemma table_nonempty (Q : Triangle) : Q.table.Nonempty := by
  apply interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
  apply Q.nondegenerate.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
  simp [Complex.finrank_real_complex]

lemma area_pos (Q : Triangle) : 0 < volume Q.table :=
  Q.isOpen_table.measure_pos volume Q.table_nonempty

lemma area_lt_top (Q : Triangle) : volume Q.table < ⊤ := by
  apply lt_of_le_of_lt (measure_mono interior_subset)
  exact ((finite_range Q.vertex).isCompact_convexHull ℝ).measure_lt_top

lemma normalized_area_univ (Q : Triangle) :
    ((volume Q.table)⁻¹ • volume.restrict Q.table) univ = 1 := by
  simp only [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel Q.area_pos.ne' Q.area_lt_top.ne

lemma tangent_ne_zero (Q : Triangle) (i : Fin 3) : Q.tangent i ≠ 0 := by
  simp only [tangent, sub_ne_zero]
  exact Q.nondegenerate.injective.ne (by decide +revert)

end Triangle

lemma angularMeasure_univ : angularMeasure univ = 1 := by
  rw [angularMeasure, Measure.map_apply Circle.exp.continuous.measurable MeasurableSet.univ]
  simp only [preimage_univ, Measure.smul_apply, Measure.restrict_apply_univ,
    Real.volume_Ico, sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top

instance angularMeasure_probability : IsProbabilityMeasure angularMeasure :=
  ⟨angularMeasure_univ⟩

lemma phaseMeasure_univ (Q : Triangle) : phaseMeasure Q univ = 1 := by
  rw [phaseMeasure, ← univ_prod_univ, Measure.prod_prod,
    Q.normalized_area_univ, angularMeasure_univ, mul_one]

instance phaseMeasure_probability (Q : Triangle) : IsProbabilityMeasure (phaseMeasure Q) :=
  ⟨phaseMeasure_univ Q⟩

namespace Triangle

/-- Barycentric coordinates for the exact, nondegenerate table. -/
def basis (Q : Triangle) : AffineBasis (Fin 3) ℝ ℂ where
  toFun := Q.vertex
  ind' := Q.nondegenerate
  tot' := Q.nondegenerate.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
    (by simp [Complex.finrank_real_complex])

lemma table_iff_coords (Q : Triangle) (x : ℂ) :
    x ∈ Q.table ↔ ∀ i, 0 < Q.basis.coord i x := by
  change x ∈ interior (convexHull ℝ (range Q.basis)) ↔ _
  rw [Q.basis.interior_convexHull]
  rfl

lemma side_coord_zero_iff (Q : Triangle) {x : ℂ} {i : Fin 3}
    (hx : x ∈ Q.side i) (k : Fin 3) : Q.basis.coord k x = 0 ↔ k = i + 2 := by
  rw [side, openSegment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  change Q.basis.coord k (AffineMap.lineMap (Q.basis i) (Q.basis (i + 1)) t) = 0 ↔ _
  rw [AffineMap.apply_lineMap, Q.basis.coord_apply, Q.basis.coord_apply,
    AffineMap.lineMap_apply_module]
  fin_cases i <;> fin_cases k <;>
    norm_num [ne_of_gt ht.1, ne_of_gt (sub_pos.mpr ht.2)] <;> decide

lemma side_not_table (Q : Triangle) {x : ℂ} {i : Fin 3}
    (hx : x ∈ Q.side i) : x ∉ Q.table := by
  intro h
  have hp := (Q.table_iff_coords x).mp h (i + 2)
  have hz := (Q.side_coord_zero_iff hx (i + 2)).mpr rfl
  linarith

lemma side_index_unique (Q : Triangle) {x : ℂ} {i j : Fin 3}
    (hi : x ∈ Q.side i) (hj : x ∈ Q.side j) : i = j := by
  apply add_right_cancel (b := (2 : Fin 3))
  exact (Q.side_coord_zero_iff hj (i + 2)).mp
    ((Q.side_coord_zero_iff hi (i + 2)).mpr rfl)

end Triangle

/-- The irrational-holonomy scalar for every irrational angle,
with no Diophantine bound. -/
lemma irrational_holonomy_ne_one {α : ℝ} (hα : Irrational (α / Real.pi))
    {j : ℤ} (hj : j ≠ 0) :
    Complex.exp (2 * (j : ℂ) * (α : ℂ) * Complex.I) ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have him := congrArg Complex.im hn
  norm_num [Complex.mul_re, Complex.mul_im] at him
  apply (irrational_iff_ne_rational _).mp hα n j hj
  apply (div_eq_div_iff Real.pi_ne_zero (Int.cast_ne_zero.mpr hj)).mpr
  nlinarith [him]

lemma parallel_mode_zero {α : ℝ} (hα : Irrational (α / Real.pi))
    {j : ℤ} (hj : j ≠ 0) {c : ℂ}
    (hc : Complex.exp (2 * (j : ℂ) * (α : ℂ) * Complex.I) * c = c) : c = 0 := by
  have hz : (Complex.exp (2 * (j : ℂ) * (α : ℂ) * Complex.I) - 1) * c = 0 := by
    rw [sub_mul, hc, one_mul, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (irrational_holonomy_ne_one hα hj))

/-- The reflection is a genuine real-linear Euclidean isometry. -/
def reflectIsometry (e : ℂ) (he : e ≠ 0) : ℂ ≃ₗᵢ[ℝ] ℂ where
  toFun := reflect e
  invFun := reflect e
  left_inv := reflect_involutive he
  right_inv := reflect_involutive he
  map_add' := reflect_add e
  map_smul' := fun r v => reflect_real_smul e v r
  norm_map' := reflect_norm he

lemma exit_time_unique (P : ℝ → Prop) {a b c : ℝ}
    (hab : a < b) (hac : a < c)
    (h₁ : ∀ t, a < t → t < b → P t) (h₂ : ∀ t, a < t → t < c → P t)
    (hb : ¬ P b) (hc : ¬ P c) : b = c := by
  rcases lt_trichotomy b c with h | h | h
  · exact (hb (h₂ b hab h)).elim
  · exact h
  · exact (hc (h₁ c hac h)).elim

lemma entry_time_unique (P : ℝ → Prop) {a b c : ℝ}
    (hac : a < c) (hbc : b < c)
    (h₁ : ∀ t, a < t → t < c → P t) (h₂ : ∀ t, b < t → t < c → P t)
    (ha : ¬ P a) (hb : ¬ P b) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exact (hb (h₁ b h hbc)).elim
  · exact h
  · exact (ha (h₂ a h hac)).elim

end TriangularBilliards
end

end OAI
end
end

section
section
namespace OAI

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
namespace TriangularBilliards

namespace FlightChain

lemma initial_line {Q : Triangle} {z : Phase} (c : FlightChain Q z) (t : ℝ) :
    c.point 0 + (t - c.time 0) • (c.direction 0 : ℂ) = z.1 + t • (z.2 : ℂ) := by
  rw [c.start_point, c.start_direction]
  module

lemma previous_line {Q : Triangle} {z : Phase} (c : FlightChain Q z) (n : ℤ) (t : ℝ) :
    c.point (n - 1) + (t - c.time (n - 1)) • (c.direction (n - 1) : ℂ) =
      c.point n + (t - c.time n) • (c.direction (n - 1) : ℂ) := by
  have h := c.flight (n - 1)
  simp only [sub_add_cancel] at h
  rw [h]
  module

/-- Agreement of the four data fields at a collision; the proof fields
are proposition-valued and need no extra equality assumptions. -/
def Agree {Q : Triangle} {z : Phase} (c d : FlightChain Q z) (n : ℤ) : Prop :=
  c.time n = d.time n ∧ c.point n = d.point n ∧
    c.direction n = d.direction n ∧ c.wall n = d.wall n

lemma agree_zero {Q : Triangle} {z : Phase} (c d : FlightChain Q z) : c.Agree d 0 := by
  have hcinside (t : ℝ) (h₁ : c.time 0 < t) (h₂ : t < 0) :
      z.1 + t • (z.2 : ℂ) ∈ Q.table := by
    rw [← c.initial_line]
    exact c.inside 0 t h₁ (by simpa using h₂.trans c.zero_after)
  have hdinside (t : ℝ) (h₁ : d.time 0 < t) (h₂ : t < 0) :
      z.1 + t • (z.2 : ℂ) ∈ Q.table := by
    rw [← d.initial_line]
    exact d.inside 0 t h₁ (by simpa using h₂.trans d.zero_after)
  have hcentry : ¬ (z.1 + c.time 0 • (z.2 : ℂ) ∈ Q.table) := by
    rw [← c.initial_line]
    simpa only [sub_self, zero_smul, add_zero] using Q.side_not_table (c.on_side 0)
  have hdentry : ¬ (z.1 + d.time 0 • (z.2 : ℂ) ∈ Q.table) := by
    rw [← d.initial_line]
    simpa only [sub_self, zero_smul, add_zero] using Q.side_not_table (d.on_side 0)
  have ht := entry_time_unique (fun t => z.1 + t • (z.2 : ℂ) ∈ Q.table)
    c.zero_before d.zero_before hcinside hdinside hcentry hdentry
  have hp : c.point 0 = d.point 0 := by
    have hc := c.initial_line (c.time 0)
    have hd := d.initial_line (d.time 0)
    simp only [sub_self, zero_smul, add_zero] at hc hd
    rw [hc, hd, ht]
  refine ⟨ht, hp, c.start_direction.symm.trans d.start_direction, ?_⟩
  exact Q.side_index_unique (hp ▸ c.on_side 0) (d.on_side 0)

lemma agree_succ {Q : Triangle} {z : Phase} (c d : FlightChain Q z) (n : ℤ)
    (h : c.Agree d n) : c.Agree d (n + 1) := by
  obtain ⟨ht, hp, hv, _⟩ := h
  let P : ℝ → Prop := fun t => c.point n + (t - c.time n) • (c.direction n : ℂ) ∈ Q.table
  have hcinside : ∀ t, c.time n < t → t < c.time (n + 1) → P t := c.inside n
  have hdinside : ∀ t, c.time n < t → t < d.time (n + 1) → P t := by
    simpa only [P, ht, hp, hv] using d.inside n
  have hcexit : ¬ P (c.time (n + 1)) := by
    change ¬ c.point n + _ • (c.direction n : ℂ) ∈ Q.table
    rw [← c.flight n]
    exact Q.side_not_table (c.on_side (n + 1))
  have hdexit : ¬ P (d.time (n + 1)) := by
    change ¬ c.point n + _ • (c.direction n : ℂ) ∈ Q.table
    rw [ht, hp, hv, ← d.flight n]
    exact Q.side_not_table (d.on_side (n + 1))
  have ht' : c.time (n + 1) = d.time (n + 1) :=
    exit_time_unique P (c.increasing (by omega))
      (ht ▸ d.increasing (by omega)) hcinside hdinside hcexit hdexit
  have hp' : c.point (n + 1) = d.point (n + 1) := by
    rw [c.flight n, d.flight n, ht', ht, hp, hv]
  have hw' : c.wall (n + 1) = d.wall (n + 1) :=
    Q.side_index_unique (hp' ▸ c.on_side (n + 1)) (d.on_side (n + 1))
  refine ⟨ht', hp', ?_, hw'⟩
  apply Subtype.ext
  rw [c.specular, d.specular, hw']
  simp only [add_sub_cancel_right, hv]

lemma agree_pred {Q : Triangle} {z : Phase} (c d : FlightChain Q z) (n : ℤ)
    (h : c.Agree d n) : c.Agree d (n - 1) := by
  obtain ⟨ht, hp, hv, hw⟩ := h
  have hv' : c.direction (n - 1) = d.direction (n - 1) := by
    apply Subtype.ext
    calc
      (c.direction (n - 1) : ℂ) = reflect (Q.tangent (c.wall n)) (c.direction n : ℂ) := by
        rw [c.specular n]
        exact (reflect_involutive (Q.tangent_ne_zero _) _).symm
      _ = reflect (Q.tangent (d.wall n)) (d.direction n : ℂ) := by rw [hw, hv]
      _ = (d.direction (n - 1) : ℂ) := by
        rw [d.specular n]
        exact reflect_involutive (Q.tangent_ne_zero _) _
  let P : ℝ → Prop := fun t =>
    c.point n + (t - c.time n) • (c.direction (n - 1) : ℂ) ∈ Q.table
  have hcinside : ∀ t, c.time (n - 1) < t → t < c.time n → P t := by
    intro t h₁ h₂
    change c.point n + _ • (c.direction (n - 1) : ℂ) ∈ Q.table
    rw [← c.previous_line n t]
    exact c.inside (n - 1) t h₁ (by simpa only [sub_add_cancel] using h₂)
  have hdinside : ∀ t, d.time (n - 1) < t → t < c.time n → P t := by
    intro t h₁ h₂
    change c.point n + _ • (c.direction (n - 1) : ℂ) ∈ Q.table
    rw [ht, hp, hv', ← d.previous_line n t]
    exact d.inside (n - 1) t h₁ (by simpa only [sub_add_cancel, ← ht] using h₂)
  have hcentry : ¬ P (c.time (n - 1)) := by
    change ¬ c.point n + _ • (c.direction (n - 1) : ℂ) ∈ Q.table
    rw [← c.previous_line]
    simpa only [sub_self, zero_smul, add_zero] using Q.side_not_table (c.on_side (n - 1))
  have hdentry : ¬ P (d.time (n - 1)) := by
    change ¬ c.point n + _ • (c.direction (n - 1) : ℂ) ∈ Q.table
    rw [ht, hp, hv', ← d.previous_line]
    simpa only [sub_self, zero_smul, add_zero] using Q.side_not_table (d.on_side (n - 1))
  have ht' : c.time (n - 1) = d.time (n - 1) :=
    entry_time_unique P (c.increasing (by omega))
      (ht ▸ d.increasing (by omega)) hcinside hdinside hcentry hdentry
  have hp' : c.point (n - 1) = d.point (n - 1) := by
    have hc := c.previous_line n (c.time (n - 1))
    have hd := d.previous_line n (d.time (n - 1))
    simp only [sub_self, zero_smul, add_zero] at hc hd
    rw [hc, hd, ht', ht, hp, hv']
  refine ⟨ht', hp', hv', ?_⟩
  exact Q.side_index_unique (hp' ▸ c.on_side (n - 1)) (d.on_side (n - 1))

/-- Determinism of actual complete nonsingular specular trajectories.
Both forward and backward schemes use the same geometric reflection and
never postulate uniqueness as an assumption. -/
theorem unique {Q : Triangle} {z : Phase} (c d : FlightChain Q z) : c = d := by
  have h : ∀ n, c.Agree d n := by
    intro n
    induction n using Int.induction_on with
    | zero => exact c.agree_zero d
    | succ n hn => exact c.agree_succ d n hn
    | pred n hn => exact c.agree_pred d (-n) hn
  have ht : c.time = d.time := funext fun n => (h n).1
  have hp : c.point = d.point := funext fun n => (h n).2.1
  have hv : c.direction = d.direction := funext fun n => (h n).2.2.1
  have hw : c.wall = d.wall := funext fun n => (h n).2.2.2
  cases c
  cases d
  cases ht
  cases hp
  cases hv
  cases hw
  rfl

/-- Rebase a complete chain at a time strictly between its collisions.
The integer relabeling is forced by the designated initial flight. -/
def rebase {Q : Triangle} {z : Phase} (c : FlightChain Q z)
    (t : ℝ) (n : ℤ) (hn : c.time n < t ∧ t < c.time (n + 1)) :
    FlightChain Q (c.at t) where
  time k := c.time (k + n) - t
  point k := c.point (k + n)
  direction k := c.direction (k + n)
  wall k := c.wall (k + n)
  increasing := by
    intro a b hab
    exact sub_lt_sub_right (c.increasing (by omega)) t
  unbounded_below u := by
    obtain ⟨k, hk⟩ := c.unbounded_below (u + t)
    refine ⟨k - n, ?_⟩
    simp only [sub_add_cancel]
    linarith
  unbounded_above u := by
    obtain ⟨k, hk⟩ := c.unbounded_above (u + t)
    refine ⟨k - n, ?_⟩
    simp only [sub_add_cancel]
    linarith
  zero_before := by simpa only [zero_add, sub_lt_zero] using hn.1
  zero_after := by simpa only [add_comm 1 n, sub_pos] using hn.2
  on_side k := c.on_side (k + n)
  flight k := by
    have hi : k + 1 + n = k + n + 1 := by omega
    change c.point (k + 1 + n) = c.point (k + n) +
      ((c.time (k + 1 + n) - t) - (c.time (k + n) - t)) • (c.direction (k + n) : ℂ)
    rw [hi, sub_sub_sub_cancel_right]
    exact c.flight (k + n)
  inside k u h₁ h₂ := by
    have hk : k + 1 + n = k + n + 1 := by ring
    have h := c.inside (k + n) (u + t) (by linarith) (by rw [← hk]; linarith)
    have he : u - (c.time (k + n) - t) = u + t - c.time (k + n) := by ring
    simpa only [he] using h
  start_point := by
    rw [c.at_of_flight ⟨hn.1.le, hn.2⟩]
    simp only [zero_add, neg_sub]
  start_direction := by
    rw [c.at_of_flight ⟨hn.1.le, hn.2⟩]
    simp only [zero_add]
  specular k := by
    rw [show k - 1 + n = k + n - 1 by omega]
    exact c.specular (k + n)

lemma rebase_at {Q : Triangle} {z : Phase} (c : FlightChain Q z)
    (t : ℝ) (n : ℤ) (hn : c.time n < t ∧ t < c.time (n + 1)) (s : ℝ) :
    (c.rebase t n hn).at s = c.at (s + t) := by
  obtain ⟨k, hk⟩ := c.exists_flight (s + t)
  have hleft : (c.rebase t n hn).time (k - n) ≤ s ∧
      s < (c.rebase t n hn).time (k - n + 1) := by
    change c.time (k - n + n) - t ≤ s ∧ s < c.time (k - n + 1 + n) - t
    have hi : k - n + 1 + n = k + 1 := by ring
    rw [sub_add_cancel, hi]
    constructor <;> linarith [hk.1, hk.2]
  rw [at_of_flight _ hleft, c.at_of_flight hk]
  simp only [rebase, sub_add_cancel]
  rw [show s - (c.time k - t) = s + t - c.time k by ring]

end FlightChain

lemma billiardFlow_eq_chain {Q : Triangle} {z : Phase} (c : FlightChain Q z) (t : ℝ) :
    billiardFlow Q t z = c.at t := by
  classical
  have h : Nonempty (FlightChain Q z) := ⟨c⟩
  simp only [billiardFlow, dite_eq_left h]
  rw [FlightChain.unique (Classical.choice h) c]

/-- The exact cocycle identity on every rebased nonsingular trajectory.
Only rebasing at a collision is excluded, since Phase itself uses interior
initial states; the main theorem still needs the fixed-time exceptional
sets to be proved null. -/
lemma billiardFlow_add_of_noncollision {Q : Triangle} {z : Phase}
    (c : FlightChain Q z) (s t : ℝ) (ht : t ∉ range c.time) :
    billiardFlow Q (s + t) z = billiardFlow Q s (billiardFlow Q t z) := by
  obtain ⟨n, hn⟩ := c.exists_flight t
  have hne : c.time n ≠ t := fun h => ht ⟨n, h⟩
  let d := c.rebase t n ⟨lt_of_le_of_ne hn.1 hne, hn.2⟩
  rw [billiardFlow_eq_chain c, billiardFlow_eq_chain c,
    billiardFlow_eq_chain d, FlightChain.rebase_at]

end TriangularBilliards
end

end OAI
end
end

section
section
namespace OAI


open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
namespace TriangularBilliards

/-! Finite unfolding and the actual null vertex-aiming exception. -/

/-- Oriented angular momentum about the origin against a fixed velocity. -/
def crossMap (v : ℂ) : ℂ →ₗ[ℝ] ℝ where
  toFun x := (x * star v).im
  map_add' x y := by simp only [add_mul, Complex.add_im]
  map_smul' r x := by
    rw [smul_mul_assoc]
    exact Complex.imLm.map_smul r (x * star v)

lemma crossMap_unit (v : Circle) : crossMap v (Complex.I * (v : ℂ)) = 1 := by
  change (Complex.I * (v : ℂ) * star (v : ℂ)).im = 1
  rw [mul_assoc, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Circle.norm_coe]
  norm_num

lemma crossMap_ker_ne_top (v : Circle) : LinearMap.ker (crossMap v) ≠ ⊤ := by
  intro h
  have hx : Complex.I * (v : ℂ) ∈ LinearMap.ker (crossMap v) := by rw [h]; trivial
  have hh := LinearMap.mem_ker.mp hx
  rw [crossMap_unit] at hh
  norm_num at hh

/-- States whose straight starting line passes through p, in either direction. -/
def aimingAt (p : ℂ) : Set Phase := {z | crossMap z.2 (z.1 - p) = 0}

lemma isClosed_aimingAt (p : ℂ) : IsClosed (aimingAt p) := by
  change IsClosed {z : Phase | ((z.1 - p) * star (z.2 : ℂ)).im = 0}
  apply isClosed_eq _ continuous_const
  fun_prop

lemma volume_aimingAt_slice (p : ℂ) (v : Circle) :
    volume ((fun x : ℂ => (x, v)) ⁻¹' aimingAt p) = 0 := by
  have hs : ((fun x : ℂ => (x, v)) ⁻¹' aimingAt p) =
      (fun x : ℂ => x + -p) ⁻¹' (LinearMap.ker (crossMap v) : Set ℂ) := by
    ext x
    change crossMap (v : ℂ) (x - p) = 0 ↔ crossMap (v : ℂ) (x + -p) = 0
    rw [sub_eq_add_neg]
  rw [hs, measure_preimage_add_right]
  exact Measure.addHaar_submodule volume _ (crossMap_ker_ne_top v)

lemma phaseMeasure_aimingAt (Q : Triangle) (p : ℂ) : phaseMeasure Q (aimingAt p) = 0 := by
  rw [phaseMeasure, Measure.prod_apply_symm (isClosed_aimingAt p).measurableSet]
  have hz (v : Circle) : ((volume Q.table)⁻¹ • volume.restrict Q.table)
      ((fun x : ℂ => (x, v)) ⁻¹' aimingAt p) = 0 := by
    rw [Measure.smul_apply]
    have hzero : (volume.restrict Q.table) ((fun x : ℂ => (x, v)) ⁻¹' aimingAt p) = 0 := by
      apply le_antisymm _ zero_le
      exact (Measure.le_iff'.mp Measure.restrict_le_self _).trans_eq (volume_aimingAt_slice p v)
    rw [hzero, smul_zero]
  simp only [hz, lintegral_zero]

/-- Reflection of a point in the supporting line of a side. -/
def wallReflection (Q : Triangle) (i : Fin 3) (x : ℂ) : ℂ :=
  Q.vertex i + reflect (Q.tangent i) (x - Q.vertex i)

/-- Finite unfolding places every vertex in the countable reflection orbit. -/
def unfoldedVertex (Q : Triangle) (w : List (Fin 3)) (i : Fin 3) : ℂ :=
  w.foldr (wallReflection Q) (Q.vertex i)

def vertexExceptional (Q : Triangle) : Set Phase :=
  ⋃ w : List (Fin 3), ⋃ i : Fin 3, aimingAt (unfoldedVertex Q w i)

lemma measurableSet_vertexExceptional (Q : Triangle) : MeasurableSet (vertexExceptional Q) := by
  exact MeasurableSet.iUnion fun w => MeasurableSet.iUnion fun i =>
    (isClosed_aimingAt (unfoldedVertex Q w i)).measurableSet

/-- A concrete, unconditional null exceptional set for all finite
unfolding vertex hits, in both time directions and for this exact measure. -/
lemma phaseMeasure_vertexExceptional (Q : Triangle) :
    phaseMeasure Q (vertexExceptional Q) = 0 := by
  apply measure_iUnion_null
  intro w
  apply measure_iUnion_null
  intro i
  exact phaseMeasure_aimingAt Q (unfoldedVertex Q w i)

namespace Triangle

def slope (Q : Triangle) (i : Fin 3) (v : ℂ) : ℝ := (Q.basis.coord i).linear v

lemma coord_shift (Q : Triangle) (i : Fin 3) (x v : ℂ) (t : ℝ) :
    Q.basis.coord i (x + t • v) = Q.basis.coord i x + t * Q.slope i v := by
  have h := (Q.basis.coord i).map_vadd x (t • v)
  simpa only [vadd_eq_add, map_smul, smul_eq_mul, add_comm, slope] using h

lemma sum_slope (Q : Triangle) (v : ℂ) : ∑ i, Q.slope i v = 0 := by
  have h := Q.basis.sum_coord_apply_eq_one v
  have h0 := Q.basis.sum_coord_apply_eq_one (0 : ℂ)
  have he (i : Fin 3) : Q.basis.coord i v = Q.slope i v + Q.basis.coord i 0 := by
    simpa only [vadd_eq_add, add_zero, slope] using (Q.basis.coord i).map_vadd 0 v
  simp only [he, Finset.sum_add_distrib] at h
  linarith

lemma slope_joint_injective (Q : Triangle) {v : ℂ}
    (hv : ∀ i, Q.slope i v = 0) : v = 0 := by
  apply Q.basis.ext_elem
  intro i
  have h := Q.coord_shift i 0 v 1
  simpa only [one_smul, zero_add, hv i, mul_zero, add_zero] using h

lemma exists_slope_neg (Q : Triangle) {v : ℂ} (hv : v ≠ 0) :
    ∃ i, Q.slope i v < 0 := by
  by_contra hn
  push Not at hn
  have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => hn i)).mp
    (Q.sum_slope v)
  exact hv (Q.slope_joint_injective fun i => hs i (Finset.mem_univ i))

end Triangle

/-- Earliest exit for finitely many affine half-planes, including a starting
point on an open side with an inward velocity. This is finite real geometry,
not an assumed exit-time oracle. -/
lemma affine_first_exit {ι : Type uIota} [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hin : ∀ i, a i = 0 → 0 < b i)
    (hb : ∃ i, b i < 0) :
    ∃ T : ℝ, 0 < T ∧ (∀ t, 0 < t → t < T → ∀ i, 0 < a i + t * b i) ∧
      (∀ i, 0 ≤ a i + T * b i) ∧ (∃ i, a i + T * b i = 0 ∧ b i < 0) := by
  classical
  let S := Finset.univ.filter fun i => b i < 0
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := hb
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨i, hi, hmin⟩ := S.exists_min_image (fun i => a i / (-b i)) hS
  have hbi : b i < 0 := (Finset.mem_filter.mp hi).2
  have hai : 0 < a i := by
    by_contra h
    have hz : a i = 0 := le_antisymm (not_lt.mp h) (ha i)
    linarith [hin i hz]
  have hT : 0 < a i / (-b i) := div_pos hai (neg_pos.mpr hbi)
  refine ⟨a i / (-b i), hT, ?_, ?_, i, ?_, hbi⟩
  · intro t ht htT j
    by_cases hbj : b j < 0
    · have htj : t < a j / (-b j) := lt_of_lt_of_le htT
        (hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hbj⟩))
      have hmul := (lt_div_iff₀ (neg_pos.mpr hbj)).mp htj
      nlinarith
    · have hbj' : 0 ≤ b j := le_of_not_gt hbj
      rcases lt_or_eq_of_le (ha j) with haj | haj
      · exact add_pos_of_pos_of_nonneg haj (mul_nonneg ht.le hbj')
      · have hp := hin j haj.symm
        simpa only [← haj, zero_add] using mul_pos ht hp
  · intro j
    by_cases hbj : b j < 0
    · have htj := hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hbj⟩)
      have hmul := (le_div_iff₀ (neg_pos.mpr hbj)).mp htj
      nlinarith
    · exact add_nonneg (ha j) (mul_nonneg hT.le (le_of_not_gt hbj))
  · field_simp [ne_of_lt hbi]
    ring

namespace Triangle

/-- An admissible velocity is strictly inward at every active half-plane. -/
def Inward (Q : Triangle) (x v : ℂ) : Prop :=
  (∀ i, 0 ≤ Q.basis.coord i x) ∧
  (∀ i, Q.basis.coord i x = 0 → 0 < Q.slope i v)

lemma inward_of_table (Q : Triangle) {x v : ℂ} (hx : x ∈ Q.table) : Q.Inward x v := by
  have hp := (Q.table_iff_coords x).mp hx
  exact ⟨fun i => (hp i).le, fun i hi => False.elim ((ne_of_gt (hp i)) hi)⟩

lemma exists_exit (Q : Triangle) {x v : ℂ} (hv : v ≠ 0) (hx : Q.Inward x v) :
    ∃ T : ℝ, 0 < T ∧ (∀ t, 0 < t → t < T → x + t • v ∈ Q.table) ∧
      (∀ i, 0 ≤ Q.basis.coord i (x + T • v)) ∧
      (∃ i, Q.basis.coord i (x + T • v) = 0 ∧ Q.slope i v < 0) := by
  obtain ⟨T, hT, hint, hclosed, i, hi, hs⟩ := affine_first_exit
    (fun i => Q.basis.coord i x) (fun i => Q.slope i v) hx.1 hx.2 (Q.exists_slope_neg hv)
  refine ⟨T, hT, ?_, ?_, i, ?_, hs⟩
  · intro t ht htT
    rw [Q.table_iff_coords]
    intro j
    rw [Q.coord_shift]
    exact hint t ht htT j
  · intro j
    rw [Q.coord_shift]
    exact hclosed j
  · rw [Q.coord_shift]
    exact hi

end Triangle

lemma crossMap_self (v : ℂ) : crossMap v v = 0 := by
  change (v * star v).im = 0
  rw [Complex.star_def, Complex.mul_conj]
  exact Complex.ofReal_im _

lemma crossMap_reflect {e : ℂ} (he : e ≠ 0) (v x : ℂ) :
    crossMap (reflect e v) (reflect e x) = -crossMap v x := by
  have he' : star e ≠ 0 := star_ne_zero.mpr he
  have h : reflect e x * star (reflect e v) = star (x * star v) := by
    simp only [reflect, star_mul', star_div₀, star_star]
    field_simp
  change (reflect e x * star (reflect e v)).im = -(x * star v).im
  rw [h, Complex.star_def, Complex.conj_im]

lemma aimingAt_flight_iff (p x : ℂ) (v : Circle) (t : ℝ) :
    (x + t • (v : ℂ), v) ∈ aimingAt p ↔ (x, v) ∈ aimingAt p := by
  change crossMap (v : ℂ) (x + t • (v : ℂ) - p) = 0 ↔ crossMap (v : ℂ) (x - p) = 0
  rw [show x + t • (v : ℂ) - p = (x - p) + t • (v : ℂ) by abel,
    map_add, map_smul, crossMap_self, smul_zero, add_zero]

lemma vertexExceptional_flight_iff (Q : Triangle) (x : ℂ) (v : Circle) (t : ℝ) :
    (x + t • (v : ℂ), v) ∈ vertexExceptional Q ↔ (x, v) ∈ vertexExceptional Q := by
  simp only [vertexExceptional, mem_iUnion, aimingAt_flight_iff]

/-- Unit outgoing velocity, with exactly the specular law. -/
def reflectedDirection (Q : Triangle) (i : Fin 3) (v : Circle) : Circle :=
  ⟨reflect (Q.tangent i) v, mem_sphere_zero_iff_norm.mpr
    (by rw [reflect_norm (Q.tangent_ne_zero i), Circle.norm_coe])⟩

lemma wallReflection_involutive (Q : Triangle) (i : Fin 3) (x : ℂ) :
    wallReflection Q i (wallReflection Q i x) = x := by
  simp only [wallReflection, add_sub_cancel_left, reflect_involutive (Q.tangent_ne_zero i)]
  abel

lemma wallReflection_sub (Q : Triangle) (i : Fin 3) (x p : ℂ) :
    wallReflection Q i x - wallReflection Q i p = reflect (Q.tangent i) (x - p) := by
  change Q.vertex i + (reflectIsometry (Q.tangent i) (Q.tangent_ne_zero i)) (x - Q.vertex i) -
    (Q.vertex i + (reflectIsometry (Q.tangent i) (Q.tangent_ne_zero i)) (p - Q.vertex i)) = _
  rw [add_sub_add_left_eq_sub, ← map_sub, sub_sub_sub_cancel_right]
  rfl

lemma wallReflection_fixed_side (Q : Triangle) {i : Fin 3} {x : ℂ}
    (hx : x ∈ Q.side i) : wallReflection Q i x = x := by
  rw [Triangle.side, openSegment_eq_image_lineMap] at hx
  obtain ⟨t, _, rfl⟩ := hx
  rw [AffineMap.lineMap_apply_module']
  change Q.vertex i + reflect (Q.tangent i) (t • Q.tangent i + Q.vertex i - Q.vertex i) =
    t • Q.tangent i + Q.vertex i
  rw [add_sub_cancel_right, reflect_real_smul, reflect_tangent (Q.tangent_ne_zero i)]
  exact add_comm _ _

lemma aimingAt_reflection_iff (Q : Triangle) (i : Fin 3) (x p : ℂ) (v : Circle) :
    (wallReflection Q i x, reflectedDirection Q i v) ∈ aimingAt (wallReflection Q i p) ↔
      (x, v) ∈ aimingAt p := by
  change crossMap (reflect (Q.tangent i) v)
    (wallReflection Q i x - wallReflection Q i p) = 0 ↔ crossMap (v : ℂ) (x - p) = 0
  rw [wallReflection_sub, crossMap_reflect (Q.tangent_ne_zero i), neg_eq_zero]

lemma vertexExceptional_reflection_iff (Q : Triangle) (i : Fin 3) (x : ℂ) (v : Circle) :
    (wallReflection Q i x, reflectedDirection Q i v) ∈ vertexExceptional Q ↔
      (x, v) ∈ vertexExceptional Q := by
  constructor
  · intro h
    simp only [vertexExceptional, mem_iUnion] at h ⊢
    obtain ⟨w, k, hk⟩ := h
    refine ⟨i :: w, k, ?_⟩
    have hpi : wallReflection Q i (unfoldedVertex Q (i :: w) k) = unfoldedVertex Q w k := by
      exact wallReflection_involutive Q i _
    apply (aimingAt_reflection_iff Q i x (unfoldedVertex Q (i :: w) k) v).mp
    rwa [hpi]
  · intro h
    simp only [vertexExceptional, mem_iUnion] at h ⊢
    obtain ⟨w, k, hk⟩ := h
    exact ⟨i :: w, k, (aimingAt_reflection_iff Q i x (unfoldedVertex Q w k) v).mpr hk⟩

lemma not_vertex_of_not_exceptional (Q : Triangle) {x : ℂ} {v : Circle}
    (hx : (x, v) ∉ vertexExceptional Q) : ∀ i, x ≠ Q.vertex i := by
  intro i he
  apply hx
  simp only [vertexExceptional, mem_iUnion]
  refine ⟨[], i, ?_⟩
  change crossMap (v : ℂ) (x - Q.vertex i) = 0
  rw [he, sub_self, map_zero]

namespace Triangle

lemma sum_coord_cyclic (Q : Triangle) (x : ℂ) (i : Fin 3) :
    Q.basis.coord i x + Q.basis.coord (i + 1) x + Q.basis.coord (i + 2) x = 1 := by
  have h := Q.basis.sum_coord_apply_eq_one x
  simp only [Fin.sum_univ_three] at h
  fin_cases i
  · exact h
  · change Q.basis.coord 1 x + Q.basis.coord 2 x + Q.basis.coord 0 x = 1
    linarith
  · change Q.basis.coord 2 x + Q.basis.coord 0 x + Q.basis.coord 1 x = 1
    linarith

lemma side_of_coords (Q : Triangle) {x : ℂ} (i : Fin 3)
    (h0 : 0 < Q.basis.coord i x) (h1 : 0 < Q.basis.coord (i + 1) x)
    (h2 : Q.basis.coord (i + 2) x = 0) : x ∈ Q.side i := by
  have hs := Q.sum_coord_cyclic x i
  have ht : Q.basis.coord (i + 1) x < 1 := by linarith
  rw [side, openSegment_eq_image_lineMap]
  refine ⟨Q.basis.coord (i + 1) x, ⟨h1, ht⟩, ?_⟩
  apply Q.basis.ext_elem
  intro k
  change Q.basis.coord k (AffineMap.lineMap (Q.basis i) (Q.basis (i + 1)) _) = _
  rw [AffineMap.apply_lineMap, Q.basis.coord_apply, Q.basis.coord_apply,
    AffineMap.lineMap_apply_module]
  have h01 : i ≠ i + 1 := by fin_cases i <;> decide
  have h20 : i + 2 ≠ i := by fin_cases i <;> decide
  have h21 : i + 2 ≠ i + 1 := by fin_cases i <;> decide
  have hk : k = i ∨ k = i + 1 ∨ k = i + 2 := by fin_cases i <;> fin_cases k <;> decide
  rcases hk with rfl | rfl | rfl
  · simp only [ite_true, ite_eq_right h01, smul_eq_mul, mul_one, mul_zero, add_zero]
    linarith
  · simp only [ite_eq_right h01.symm, ite_true, smul_eq_mul, mul_zero, zero_add, mul_one]
  · simp only [ite_eq_right h20, ite_eq_right h21, smul_eq_mul, mul_zero, add_zero, h2]

lemma eq_vertex_of_two_coords_zero (Q : Triangle) {x : ℂ} (i : Fin 3)
    (h1 : Q.basis.coord (i + 1) x = 0) (h2 : Q.basis.coord (i + 2) x = 0) :
    x = Q.vertex i := by
  have hs := Q.sum_coord_cyclic x i
  apply Q.basis.ext_elem
  intro k
  change Q.basis.coord k x = Q.basis.coord k (Q.basis i)
  rw [Q.basis.coord_apply]
  have h01 : i ≠ i + 1 := by fin_cases i <;> decide
  have h20 : i + 2 ≠ i := by fin_cases i <;> decide
  have hk : k = i ∨ k = i + 1 ∨ k = i + 2 := by fin_cases i <;> fin_cases k <;> decide
  rcases hk with rfl | rfl | rfl
  · simp only [ite_true]
    linarith
  · simpa only [ite_eq_right h01.symm] using h1
  · simpa only [ite_eq_right h20] using h2

lemma boundary_open_side (Q : Triangle) {x : ℂ}
    (hx : ∀ i, 0 ≤ Q.basis.coord i x) (hz : ∃ i, Q.basis.coord i x = 0)
    (hv : ∀ i, x ≠ Q.vertex i) : ∃ i, x ∈ Q.side i := by
  obtain ⟨i, hi⟩ := hz
  have h1 : 0 < Q.basis.coord (i + 1) x := by
    apply lt_of_le_of_ne (hx (i + 1))
    intro he
    apply hv (i + 2)
    apply Q.eq_vertex_of_two_coords_zero
    · convert hi using 1; congr 2; fin_cases i <;> rfl
    · convert he.symm using 1; congr 2; fin_cases i <;> rfl
  have h2 : 0 < Q.basis.coord (i + 2) x := by
    apply lt_of_le_of_ne (hx (i + 2))
    intro he
    apply hv (i + 1)
    apply Q.eq_vertex_of_two_coords_zero
    · convert he.symm using 1; congr 2; fin_cases i <;> rfl
    · convert hi using 1; congr 2; fin_cases i <;> rfl
  refine ⟨i + 1, Q.side_of_coords (i + 1) h1 ?_ ?_⟩
  · convert h2 using 1; congr 2; fin_cases i <;> rfl
  · convert hi using 1; congr 2; fin_cases i <;> rfl

end Triangle

lemma complex_decompose_tangent {e : ℂ} (he : e ≠ 0) (v : ℂ) :
    ∃ a b : ℝ, v = a • e + b • (Complex.I * e) := by
  refine ⟨(v / e).re, (v / e).im, ?_⟩
  rw [Complex.real_smul, Complex.real_smul]
  calc
    v = (v / e) * e := (div_mul_cancel₀ v he).symm
    _ = ((v / e).re + (v / e).im * Complex.I) * e := by rw [Complex.re_add_im]
    _ = _ := by ring

lemma linear_reflect_neg {e : ℂ} (he : e ≠ 0) (l : ℂ →ₗ[ℝ] ℝ) (hl : l e = 0) (v : ℂ) :
    l (reflect e v) = -l v := by
  obtain ⟨a, b, rfl⟩ := complex_decompose_tangent he v
  rw [reflect_add, reflect_real_smul, reflect_real_smul, reflect_tangent he, reflect_normal he]
  simp only [map_add, map_smul, smul_eq_mul, hl, mul_zero, zero_add, map_neg]
  ring

namespace Triangle

lemma slope_tangent_zero (Q : Triangle) (i : Fin 3) : Q.slope (i + 2) (Q.tangent i) = 0 := by
  have h20 : i + 2 ≠ i := by fin_cases i <;> decide
  have h21 : i + 2 ≠ i + 1 := by fin_cases i <;> decide
  have h := (Q.basis.coord (i + 2)).linearMap_vsub (Q.basis (i + 1)) (Q.basis i)
  simp only [vsub_eq_sub, Q.basis.coord_apply, ite_eq_right h20, ite_eq_right h21, sub_zero] at h
  exact h

lemma slope_reflect (Q : Triangle) (i : Fin 3) (v : ℂ) :
    Q.slope (i + 2) (reflect (Q.tangent i) v) = -Q.slope (i + 2) v :=
  linear_reflect_neg (Q.tangent_ne_zero i) (Q.basis.coord (i + 2)).linear
    (Q.slope_tangent_zero i) v

lemma inward_after_reflection (Q : Triangle) {x v : ℂ} {i : Fin 3}
    (hside : x ∈ Q.side i) (hclosed : ∀ j, 0 ≤ Q.basis.coord j x)
    (hneg : Q.slope (i + 2) v < 0) : Q.Inward x (reflect (Q.tangent i) v) := by
  refine ⟨hclosed, ?_⟩
  intro j hj
  have he := (Q.side_coord_zero_iff hside j).mp hj
  rw [he, Q.slope_reflect]
  exact neg_pos.mpr hneg

end Triangle

/-- A finite collision datum whose existence is proved from the actual
half-plane geometry and the countable unfolded-vertex exception. -/
structure NextCollision (Q : Triangle) (x : ℂ) (v : Circle) where
  delay : ℝ
  wall : Fin 3
  positive : 0 < delay
  on_side : x + delay • (v : ℂ) ∈ Q.side wall
  inside : ∀ t : ℝ, 0 < t → t < delay → x + t • (v : ℂ) ∈ Q.table
  inward : Q.Inward (x + delay • (v : ℂ)) (reflectedDirection Q wall v)
  regular : (x + delay • (v : ℂ), reflectedDirection Q wall v) ∉ vertexExceptional Q

lemma exists_next_collision (Q : Triangle) {x : ℂ} {v : Circle}
    (hx : Q.Inward x v) (hreg : (x, v) ∉ vertexExceptional Q) :
    Nonempty (NextCollision Q x v) := by
  obtain ⟨T, hT, hint, hclosed, k, hk, hneg⟩ := Q.exists_exit (Circle.coe_ne_zero v) hx
  have hreg' : (x + T • (v : ℂ), v) ∉ vertexExceptional Q := by
    rwa [vertexExceptional_flight_iff]
  obtain ⟨i, hi⟩ := Q.boundary_open_side hclosed ⟨k, hk⟩
    (not_vertex_of_not_exceptional Q hreg')
  have hki := (Q.side_coord_zero_iff hi k).mp hk
  refine ⟨⟨T, i, hT, hi, hint, ?_, ?_⟩⟩
  · exact Q.inward_after_reflection hi hclosed (hki ▸ hneg)
  · have hiff := vertexExceptional_reflection_iff Q i (x + T • (v : ℂ)) v
    rw [wallReflection_fixed_side Q hi] at hiff
    exact fun h => hreg' (hiff.mp h)

/-- Actual states on a regular recursively extendible ray. Boundary initial
states are allowed only with strict inward velocity. -/
structure Admissible (Q : Triangle) where
  pos : ℂ
  vel : Circle
  inward : Q.Inward pos vel
  regular : (pos, vel) ∉ vertexExceptional Q

namespace Admissible

noncomputable def collision {Q : Triangle} (z : Admissible Q) : NextCollision Q z.pos z.vel :=
  Classical.choice (exists_next_collision Q z.inward z.regular)

noncomputable def next {Q : Triangle} (z : Admissible Q) : Admissible Q where
  pos := z.pos + z.collision.delay • (z.vel : ℂ)
  vel := reflectedDirection Q z.collision.wall z.vel
  inward := z.collision.inward
  regular := z.collision.regular

noncomputable def iterate {Q : Triangle} (z : Admissible Q) : ℕ → Admissible Q
  | 0 => z
  | n + 1 => (z.iterate n).next

noncomputable def time {Q : Triangle} (z : Admissible Q) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (z.iterate k).collision.delay

lemma time_zero {Q : Triangle} (z : Admissible Q) : z.time 0 = 0 := by
  simp [time]

lemma time_succ {Q : Triangle} (z : Admissible Q) (n : ℕ) :
    z.time (n + 1) = z.time n + (z.iterate n).collision.delay := by
  exact Finset.sum_range_succ _ n

lemma time_strictMono {Q : Triangle} (z : Admissible Q) : StrictMono z.time := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [z.time_succ]
  exact lt_add_of_pos_right _ (z.iterate n).collision.positive

lemma iterate_flight {Q : Triangle} (z : Admissible Q) (n : ℕ) :
    (z.iterate (n + 1)).pos = (z.iterate n).pos +
      (z.time (n + 1) - z.time n) • ((z.iterate n).vel : ℂ) := by
  rw [z.time_succ, add_sub_cancel_left]
  rfl

lemma iterate_inside {Q : Triangle} (z : Admissible Q) (n : ℕ) {t : ℝ}
    (h0 : z.time n < t) (h1 : t < z.time (n + 1)) :
    (z.iterate n).pos + (t - z.time n) • ((z.iterate n).vel : ℂ) ∈ Q.table := by
  apply (z.iterate n).collision.inside (t - z.time n) (sub_pos.mpr h0)
  rw [z.time_succ] at h1
  linarith

lemma iterate_on_side {Q : Triangle} (z : Admissible Q) (n : ℕ) :
    (z.iterate (n + 1)).pos ∈ Q.side (z.iterate n).collision.wall :=
  (z.iterate n).collision.on_side

lemma dist_iterate_succ {Q : Triangle} (z : Admissible Q) (n : ℕ) :
    dist (z.iterate n).pos (z.iterate (n + 1)).pos = z.time (n + 1) - z.time n := by
  rw [dist_comm, dist_eq_norm, z.iterate_flight, add_sub_cancel_left, norm_smul,
    Circle.norm_coe, mul_one, Real.norm_eq_abs, abs_of_pos]
  exact sub_pos.mpr (z.time_strictMono (Nat.lt_succ_self n))

lemma dist_iterate_le_time {Q : Triangle} (z : Admissible Q) {m n : ℕ} (hmn : m ≤ n) :
    dist (z.iterate m).pos (z.iterate n).pos ≤ z.time n - z.time m := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    calc
      dist (z.iterate m).pos (z.iterate (n + 1)).pos ≤
          dist (z.iterate m).pos (z.iterate n).pos +
          dist (z.iterate n).pos (z.iterate (n + 1)).pos := dist_triangle _ _ _
      _ ≤ (z.time n - z.time m) + (z.time (n + 1) - z.time n) :=
        add_le_add ih (z.dist_iterate_succ n).le
      _ = z.time (n + 1) - z.time m := by ring

end Admissible

end TriangularBilliards
end

end OAI
end
end

section
section
namespace OAI

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
namespace TriangularBilliards

open Filter
open scoped Topology

lemma crossMap_flight (p x v : ℂ) (t : ℝ) :
    crossMap v (x + t • v - p) = crossMap v (x - p) := by
  rw [show x + t • v - p = (x - p) + t • v by abel,
    map_add, map_smul, crossMap_self, smul_zero, add_zero]

lemma crossMap_abs_le (v : Circle) (x : ℂ) : |crossMap v x| ≤ ‖x‖ := by
  calc
    |crossMap v x| ≤ ‖x * star (v : ℂ)‖ := Complex.abs_im_le_norm _
    _ = ‖x‖ := by rw [norm_mul, norm_star, Circle.norm_coe, mul_one]

lemma wallReflection_fixed_vertex (Q : Triangle) (i k : Fin 3) (hk : k ≠ i + 2) :
    wallReflection Q i (Q.vertex k) = Q.vertex k := by
  have h : k = i ∨ k = i + 1 ∨ k = i + 2 := by fin_cases i <;> fin_cases k <;> decide
  rcases h with rfl | rfl | h
  · simp [wallReflection, reflect]
  · change Q.vertex i + reflect (Q.tangent i) (Q.tangent i) = Q.vertex (i + 1)
    rw [reflect_tangent (Q.tangent_ne_zero i), Triangle.tangent]
    abel
  · exact False.elim (hk h)

namespace Admissible

lemma wall_ne_next {Q : Triangle} (z : Admissible Q) (n : ℕ) :
    (z.iterate n).collision.wall ≠ (z.iterate (n + 1)).collision.wall := by
  intro he
  let i := (z.iterate n).collision.wall
  have h0 : Q.basis.coord (i + 2) (z.iterate (n + 1)).pos = 0 :=
    (Q.side_coord_zero_iff (z.iterate_on_side n) (i + 2)).mpr rfl
  have hp : 0 < Q.slope (i + 2) (z.iterate (n + 1)).vel :=
    (z.iterate (n + 1)).inward.2 (i + 2) h0
  have h1 : Q.basis.coord (i + 2) (z.iterate (n + 2)).pos = 0 := by
    apply (Q.side_coord_zero_iff (z.iterate_on_side (n + 1)) (i + 2)).mpr
    rw [← he]
  change Q.basis.coord (i + 2) ((z.iterate (n + 1)).pos +
    (z.iterate (n + 1)).collision.delay • ((z.iterate (n + 1)).vel : ℂ)) = 0 at h1
  rw [Q.coord_shift, h0, zero_add] at h1
  exact (ne_of_gt (mul_pos (z.iterate (n + 1)).collision.positive hp)) h1

lemma dist_iterate_le_dist_time {Q : Triangle} (z : Admissible Q) (m n : ℕ) :
    dist (z.iterate m).pos (z.iterate n).pos ≤ dist (z.time m) (z.time n) := by
  rcases le_total m n with h | h
  · rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (z.time_strictMono.monotone h))]
    exact z.dist_iterate_le_time h
  · rw [dist_comm (z.iterate m).pos, dist_comm (z.time m), Real.dist_eq, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr (z.time_strictMono.monotone h))]
    exact z.dist_iterate_le_time h

lemma positions_converge_of_bounded_time {Q : Triangle} (z : Admissible Q)
    (hb : BddAbove (range z.time)) :
    ∃ p : ℂ, Tendsto (fun n => (z.iterate n).pos) atTop (𝓝 p) := by
  have ht := tendsto_atTop_ciSup z.time_strictMono.monotone hb
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp ht.cauchySeq ε hε
  exact ⟨N, fun m hm n hn => lt_of_le_of_lt (z.dist_iterate_le_dist_time m n) (hN m hm n hn)⟩

/-- If infinitely many collisions accumulated in finite distance, their
common limit would have to be a vertex, not an arbitrary boundary point. -/
lemma limit_is_vertex {Q : Triangle} (z : Admissible Q) {p : ℂ}
    (hp : Tendsto (fun n => (z.iterate n).pos) atTop (𝓝 p)) : ∃ k, p = Q.vertex k := by
  have hc (i : Fin 3) : Tendsto (fun n => Q.basis.coord i (z.iterate n).pos) atTop
      (𝓝 (Q.basis.coord i p)) :=
    (Q.basis.coord i).continuous_of_finiteDimensional.continuousAt.tendsto.comp hp
  have hnonneg (i : Fin 3) : 0 ≤ Q.basis.coord i p :=
    ge_of_tendsto' (hc i) (fun n => (z.iterate n).inward.1 i)
  have hz : ∃ i, Q.basis.coord i p = 0 := by
    by_contra hn
    push Not at hn
    have hpos (i : Fin 3) : 0 < Q.basis.coord i p := lt_of_le_of_ne (hnonneg i) (hn i).symm
    have he : ∀ᶠ n : ℕ in atTop, ∀ i, 0 < Q.basis.coord i (z.iterate n).pos :=
      eventually_all.mpr fun i => (hc i).eventually (lt_mem_nhds (hpos i))
    obtain ⟨N, hN⟩ := eventually_atTop.mp he
    have hzero := (Q.side_coord_zero_iff (z.iterate_on_side N)
      ((z.iterate N).collision.wall + 2)).mpr rfl
    have hpositive := hN (N + 1) (Nat.le_succ N) ((z.iterate N).collision.wall + 2)
    linarith
  by_contra hn
  push Not at hn
  obtain ⟨i, hi⟩ := Q.boundary_open_side hnonneg hz hn
  have hpos (j : Fin 3) (hj : j ≠ i + 2) : 0 < Q.basis.coord j p := by
    apply lt_of_le_of_ne (hnonneg j)
    intro hj0
    exact hj ((Q.side_coord_zero_iff hi j).mp hj0.symm)
  have he : ∀ᶠ n : ℕ in atTop, ∀ j, j ≠ i + 2 → 0 < Q.basis.coord j (z.iterate n).pos := by
    apply eventually_all.mpr
    intro j
    by_cases hj : j = i + 2
    · exact Eventually.of_forall fun _ h => False.elim (h hj)
    · exact ((hc j).eventually (lt_mem_nhds (hpos j hj))).mono fun _ h _ => h
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  have hw (n : ℕ) (hn : N ≤ n + 1) : (z.iterate n).collision.wall = i := by
    apply add_right_cancel (b := (2 : Fin 3))
    by_contra h
    have hz := (Q.side_coord_zero_iff (z.iterate_on_side n)
      ((z.iterate n).collision.wall + 2)).mpr rfl
    have hp := hN (n + 1) hn ((z.iterate n).collision.wall + 2) h
    linarith
  exact z.wall_ne_next N ((hw N (by omega)).trans (hw (N + 1) (by omega)).symm)

/-- Absolute angular momentum about a fixed point. -/
def momentum {Q : Triangle} (z : Admissible Q) (p : ℂ) : ℝ :=
  |crossMap z.vel (z.pos - p)|

lemma momentum_next {Q : Triangle} (z : Admissible Q) (p : ℂ)
    (hp : wallReflection Q z.collision.wall p = p) : z.next.momentum p = z.momentum p := by
  have hx := wallReflection_fixed_side Q z.collision.on_side
  have h := crossMap_reflect (Q.tangent_ne_zero z.collision.wall) (z.vel : ℂ)
    (z.pos + z.collision.delay • (z.vel : ℂ) - p)
  rw [← wallReflection_sub, hx, hp, crossMap_flight] at h
  change |crossMap (reflect (Q.tangent z.collision.wall) z.vel)
    (z.pos + z.collision.delay • (z.vel : ℂ) - p)| = |crossMap (z.vel : ℂ) (z.pos - p)|
  rw [h, abs_neg]

lemma momentum_tendsto_zero {Q : Triangle} (z : Admissible Q) {p : ℂ}
    (hp : Tendsto (fun n => (z.iterate n).pos) atTop (𝓝 p)) :
    Tendsto (fun n => (z.iterate n).momentum p) atTop (𝓝 0) := by
  have hnorm : Tendsto (fun n => ‖(z.iterate n).pos - p‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hp.sub_const p).norm
  apply squeeze_zero (fun n => abs_nonneg _) (fun n => crossMap_abs_le _ _) hnorm

lemma eventually_wall_fixed_of_vertex_limit {Q : Triangle} (z : Admissible Q) (k : Fin 3)
    (hp : Tendsto (fun n => (z.iterate n).pos) atTop (𝓝 (Q.vertex k))) :
    ∀ᶠ n : ℕ in atTop, wallReflection Q (z.iterate n).collision.wall (Q.vertex k) = Q.vertex k := by
  have hc := (Q.basis.coord k).continuous_of_finiteDimensional.continuousAt.tendsto.comp
    (hp.comp (tendsto_add_atTop_nat 1))
  have hk : Q.basis.coord k (Q.vertex k) = 1 := Q.basis.coord_apply_eq k
  filter_upwards [hc.eventually (lt_mem_nhds (by rw [hk]; norm_num : 0 <
    Q.basis.coord k (Q.vertex k)))] with n hn
  apply wallReflection_fixed_vertex
  intro he
  have hz := (Q.side_coord_zero_iff (z.iterate_on_side n) k).mpr he
  change 0 < Q.basis.coord k (z.iterate (n + 1)).pos at hn
  linarith

/-- Non-Zeno is proved, not added as an admissibility hypothesis: finite
accumulation would approach a vertex, where conservation of absolute
angular momentum forces this regular ray to aim through that vertex. -/
lemma time_not_bddAbove {Q : Triangle} (z : Admissible Q) : ¬ BddAbove (range z.time) := by
  intro hb
  obtain ⟨p, hp⟩ := z.positions_converge_of_bounded_time hb
  obtain ⟨k, rfl⟩ := z.limit_is_vertex hp
  have he := z.eventually_wall_fixed_of_vertex_limit k hp
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  have hconst (n : ℕ) (hn : N ≤ n) :
      (z.iterate n).momentum (Q.vertex k) = (z.iterate N).momentum (Q.vertex k) := by
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      exact ((z.iterate n).momentum_next (Q.vertex k) (hN n hn)).trans ih
  have ht : Tendsto (fun n => (z.iterate n).momentum (Q.vertex k)) atTop
      (𝓝 ((z.iterate N).momentum (Q.vertex k))) :=
    tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨N, fun n hn => (hconst n hn).symm⟩)
  have hm := tendsto_nhds_unique ht (z.momentum_tendsto_zero hp)
  apply (z.iterate N).regular
  simp only [vertexExceptional, mem_iUnion]
  refine ⟨[], k, ?_⟩
  exact abs_eq_zero.mp hm

lemma time_unbounded_above {Q : Triangle} (z : Admissible Q) (t : ℝ) :
    ∃ n : ℕ, t < z.time n := by
  by_contra hn
  push Not at hn
  apply z.time_not_bddAbove
  exact ⟨t, fun _ ⟨n, hn'⟩ => hn' ▸ hn n⟩

end Admissible

lemma reflect_neg (e v : ℂ) : reflect e (-v) = -reflect e v := by
  simp [reflect]

lemma vertexExceptional_neg_iff (Q : Triangle) (x : ℂ) (v : Circle) :
    (x, -v) ∈ vertexExceptional Q ↔ (x, v) ∈ vertexExceptional Q := by
  simp only [vertexExceptional, mem_iUnion, aimingAt, mem_ofPred_eq, Circle.coe_neg]
  have he (p : ℂ) : crossMap (-(v : ℂ)) (x - p) = -crossMap v (x - p) := by
    simp [crossMap]
  simp only [he, neg_eq_zero]

/-- The two genuine recursively generated rays, joined at an interior state. -/
structure TwoRays (Q : Triangle) (z : Phase) where
  interior_pos : z.1 ∈ Q.table
  forward : Admissible Q
  backward : Admissible Q
  forward_pos : forward.pos = z.1
  backward_pos : backward.pos = z.1
  forward_vel : forward.vel = z.2
  backward_vel : backward.vel = -z.2

noncomputable def regularRays (Q : Triangle) (z : Phase) (hx : z.1 ∈ Q.table)
    (hr : z ∉ vertexExceptional Q) : TwoRays Q z where
  interior_pos := hx
  forward := ⟨z.1, z.2, Q.inward_of_table hx, hr⟩
  backward := ⟨z.1, -z.2, Q.inward_of_table hx, by rwa [vertexExceptional_neg_iff]⟩
  forward_pos := rfl
  backward_pos := rfl
  forward_vel := rfl
  backward_vel := rfl

namespace TwoRays

variable {Q : Triangle} {z : Phase} (r : TwoRays Q z)

def time : ℤ → ℝ
  | .ofNat 0 => -r.backward.time 1
  | .ofNat (n + 1) => r.forward.time (n + 1)
  | .negSucc n => -r.backward.time (n + 2)

def point : ℤ → ℂ
  | .ofNat 0 => (r.backward.iterate 1).pos
  | .ofNat (n + 1) => (r.forward.iterate (n + 1)).pos
  | .negSucc n => (r.backward.iterate (n + 2)).pos

def direction : ℤ → Circle
  | .ofNat n => (r.forward.iterate n).vel
  | .negSucc n => -(r.backward.iterate (n + 1)).vel

def wall : ℤ → Fin 3
  | .ofNat 0 => r.backward.collision.wall
  | .ofNat (n + 1) => (r.forward.iterate n).collision.wall
  | .negSucc n => (r.backward.iterate (n + 1)).collision.wall

lemma zero_before : r.time 0 < 0 := by
  change -r.backward.time 1 < 0
  have h := r.backward.time_strictMono (Nat.zero_lt_succ 0)
  rw [r.backward.time_zero] at h
  exact neg_neg_of_pos h

lemma zero_after : 0 < r.time 1 := by
  change 0 < r.forward.time 1
  have h := r.forward.time_strictMono (Nat.zero_lt_succ 0)
  rwa [r.forward.time_zero] at h

lemma increasing : StrictMono r.time := by
  apply strictMono_int_of_lt_succ
  intro n
  cases n with
  | ofNat n =>
    cases n with
    | zero => exact lt_trans r.zero_before r.zero_after
    | succ n => exact r.forward.time_strictMono (Nat.lt_succ_self (n + 1))
  | negSucc n =>
    cases n with
    | zero => exact neg_lt_neg (r.backward.time_strictMono (by omega : 1 < 2))
    | succ n => exact neg_lt_neg (r.backward.time_strictMono (Nat.lt_succ_self (n + 2)))

lemma unbounded_above (t : ℝ) : ∃ n : ℤ, t < r.time n := by
  obtain ⟨n, hn⟩ := r.forward.time_unbounded_above t
  exact ⟨Int.ofNat (n + 1), lt_trans hn (r.forward.time_strictMono (Nat.lt_succ_self n))⟩

lemma unbounded_below (t : ℝ) : ∃ n : ℤ, r.time n < t := by
  obtain ⟨n, hn⟩ := r.backward.time_unbounded_above (-t)
  refine ⟨Int.negSucc n, ?_⟩
  change -r.backward.time (n + 2) < t
  have h := r.backward.time_strictMono (by omega : n < n + 2)
  linarith

lemma on_side (n : ℤ) : r.point n ∈ Q.side (r.wall n) := by
  cases n with
  | ofNat n =>
    cases n with
    | zero => exact r.backward.iterate_on_side 0
    | succ n => exact r.forward.iterate_on_side n
  | negSucc n => exact r.backward.iterate_on_side (n + 1)

lemma middle_point :
    r.point 0 = z.1 - r.backward.time 1 • (z.2 : ℂ) := by
  change (r.backward.iterate 1).pos = _
  rw [r.backward.iterate_flight 0, r.backward.time_zero, sub_zero]
  change r.backward.pos + r.backward.time 1 • (r.backward.vel : ℂ) = _
  rw [r.backward_pos, r.backward_vel, Circle.coe_neg, smul_neg, sub_eq_add_neg]

lemma start_point : z.1 = r.point 0 + (-r.time 0) • (r.direction 0 : ℂ) := by
  rw [r.middle_point]
  change z.1 = z.1 - r.backward.time 1 • (z.2 : ℂ) +
    (- -r.backward.time 1) • (r.forward.vel : ℂ)
  rw [neg_neg, r.forward_vel]
  abel

lemma flight (n : ℤ) : r.point (n + 1) = r.point n +
    (r.time (n + 1) - r.time n) • (r.direction n : ℂ) := by
  cases n with
  | ofNat n =>
    cases n with
    | zero =>
      change r.point 1 = r.point 0 + (r.time 1 - r.time 0) • (r.direction 0 : ℂ)
      rw [r.middle_point]
      change (r.forward.iterate 1).pos = z.1 - r.backward.time 1 • (z.2 : ℂ) +
        (r.forward.time 1 - -r.backward.time 1) • (r.forward.vel : ℂ)
      rw [r.forward.iterate_flight 0, r.forward.time_zero, sub_zero]
      change r.forward.pos + r.forward.time 1 • (r.forward.vel : ℂ) = _
      rw [r.forward_pos, r.forward_vel, sub_neg_eq_add, add_smul]
      abel
    | succ n => exact r.forward.iterate_flight (n + 1)
  | negSucc n =>
    have h := r.backward.iterate_flight (n + 1)
    cases n with
    | zero =>
      change (r.backward.iterate 1).pos = (r.backward.iterate 2).pos +
        (-r.backward.time 1 - -r.backward.time 2) • (-(r.backward.iterate 1).vel : Circle)
      rw [Circle.coe_neg, smul_neg, h]
      rw [show -r.backward.time 1 - -r.backward.time 2 =
        r.backward.time 2 - r.backward.time 1 by ring]
      abel
    | succ n =>
      change (r.backward.iterate (n + 2)).pos = (r.backward.iterate (n + 3)).pos +
        (-r.backward.time (n + 2) - -r.backward.time (n + 3)) •
          (-(r.backward.iterate (n + 2)).vel : Circle)
      rw [Circle.coe_neg, smul_neg, h]
      rw [show -r.backward.time (n + 2) - -r.backward.time (n + 3) =
        r.backward.time (n + 3) - r.backward.time (n + 2) by ring]
      abel

lemma middle_flight (t : ℝ) :
    r.point 0 + (t - r.time 0) • (r.direction 0 : ℂ) = z.1 + t • (z.2 : ℂ) := by
  rw [r.middle_point]
  change z.1 - r.backward.time 1 • (z.2 : ℂ) +
    (t - -r.backward.time 1) • (r.forward.vel : ℂ) = _
  rw [r.forward_vel, sub_neg_eq_add, add_smul]
  abel

lemma inside (n : ℤ) (t : ℝ) (h0 : r.time n < t) (h1 : t < r.time (n + 1)) :
    r.point n + (t - r.time n) • (r.direction n : ℂ) ∈ Q.table := by
  cases n with
  | ofNat n =>
    cases n with
    | zero =>
      change r.point 0 + (t - r.time 0) • (r.direction 0 : ℂ) ∈ Q.table
      rw [r.middle_flight]
      rcases lt_trichotomy t 0 with ht | rfl | ht
      · have h : -t < r.backward.time 1 := by change -r.backward.time 1 < t at h0; linarith
        have hp := r.backward.iterate_inside 0 (t := -t)
          (by rw [r.backward.time_zero]; linarith) h
        change r.backward.pos + (-t - r.backward.time 0) • (r.backward.vel : ℂ) ∈ Q.table at hp
        simpa only [r.backward.time_zero, sub_zero, r.backward_pos, r.backward_vel,
          Circle.coe_neg, smul_neg, neg_smul, neg_neg] using hp
      · simpa only [zero_smul, add_zero] using r.interior_pos
      · have hp := r.forward.iterate_inside 0 (t := t)
          (by rw [r.forward.time_zero]; exact ht) h1
        change r.forward.pos + (t - r.forward.time 0) • (r.forward.vel : ℂ) ∈ Q.table at hp
        simpa only [r.forward.time_zero, sub_zero, r.forward_pos, r.forward_vel] using hp
    | succ n => exact r.forward.iterate_inside (n + 1) h0 h1
  | negSucc n =>
    have ht0 : r.backward.time (n + 1) < -t := by
      cases n with
      | zero => change t < -r.backward.time 1 at h1; linarith
      | succ n => change t < -r.backward.time (n + 2) at h1; linarith
    have ht1 : -t < r.backward.time (n + 2) := by
      change -r.backward.time (n + 2) < t at h0
      linarith
    have hp := r.backward.iterate_inside (n + 1) ht0 ht1
    change (r.backward.iterate (n + 2)).pos + (t - -r.backward.time (n + 2)) •
      (-(r.backward.iterate (n + 1)).vel : Circle) ∈ Q.table
    rw [Circle.coe_neg, smul_neg, r.backward.iterate_flight (n + 1)]
    convert hp using 1
    module

lemma specular (n : ℤ) :
    (r.direction n : ℂ) = reflect (Q.tangent (r.wall n)) (r.direction (n - 1) : ℂ) := by
  cases n with
  | ofNat n =>
    cases n with
    | zero =>
      change (r.forward.vel : ℂ) = reflect (Q.tangent r.backward.collision.wall)
        (-(r.backward.iterate 1).vel : Circle)
      change (r.forward.vel : ℂ) = reflect (Q.tangent r.backward.collision.wall)
        (-reflectedDirection Q r.backward.collision.wall r.backward.vel : Circle)
      rw [Circle.coe_neg, reflect_neg]
      change (r.forward.vel : ℂ) = -reflect (Q.tangent r.backward.collision.wall)
        (reflect (Q.tangent r.backward.collision.wall) r.backward.vel)
      rw [reflect_involutive (Q.tangent_ne_zero _), r.forward_vel, r.backward_vel,
        Circle.coe_neg, neg_neg]
    | succ n =>
      change ((r.forward.iterate n).next.vel : ℂ) = reflect
        (Q.tangent (r.forward.iterate n).collision.wall) (r.direction (Int.ofNat (n + 1) - 1) : ℂ)
      rw [show Int.ofNat (n + 1) - 1 = Int.ofNat n by change (↑(n + 1) : ℤ) - 1 = ↑n; omega]
      rfl
  | negSucc n =>
    change (-(r.backward.iterate (n + 1)).vel : Circle) = reflect
      (Q.tangent (r.backward.iterate (n + 1)).collision.wall)
      (r.direction (Int.negSucc n - 1) : ℂ)
    rw [show Int.negSucc n - 1 = Int.negSucc (n + 1) by omega]
    change (-(r.backward.iterate (n + 1)).vel : Circle) = reflect
      (Q.tangent (r.backward.iterate (n + 1)).collision.wall)
      (-reflectedDirection Q (r.backward.iterate (n + 1)).collision.wall
        (r.backward.iterate (n + 1)).vel : Circle)
    rw [Circle.coe_neg, Circle.coe_neg, reflect_neg]
    change -((r.backward.iterate (n + 1)).vel : ℂ) = -reflect
      (Q.tangent (r.backward.iterate (n + 1)).collision.wall)
      (reflect (Q.tangent (r.backward.iterate (n + 1)).collision.wall)
        (r.backward.iterate (n + 1)).vel)
    rw [reflect_involutive (Q.tangent_ne_zero _)]

/-- The full two-sided, non-Zeno, specular chain, assembled from actual exits. -/
def chain : FlightChain Q z where
  time := r.time
  point := r.point
  direction := r.direction
  wall := r.wall
  increasing := r.increasing
  unbounded_below := r.unbounded_below
  unbounded_above := r.unbounded_above
  zero_before := r.zero_before
  zero_after := r.zero_after
  on_side := r.on_side
  flight := r.flight
  inside := r.inside
  start_point := r.start_point
  start_direction := r.forward_vel.symm
  specular := r.specular

end TwoRays

lemma exists_chain_of_not_exceptional (Q : Triangle) (z : Phase) (hx : z.1 ∈ Q.table)
    (hr : z ∉ vertexExceptional Q) : Nonempty (FlightChain Q z) :=
  ⟨(regularRays Q z hx hr).chain⟩

lemma ae_position_in_table (Q : Triangle) : ∀ᵐ z ∂phaseMeasure Q, z.1 ∈ Q.table := by
  rw [ae_iff]
  rw [show {a : Phase | a.1 ∉ Q.table} = Q.tableᶜ ×ˢ (univ : Set Circle) by
    ext a; simp]
  rw [phaseMeasure, Measure.prod_prod, Measure.smul_apply,
    Measure.restrict_apply Q.measurableSet_table.compl]
  simp only [compl_inter_self, measure_empty, smul_zero, zero_mul]

/-- Complete regular trajectories exist for almost every initial state under
exact normalized area-angular measure; all collisions and both infinite
ends have been constructed above, with no completeness hypothesis. -/
lemma ae_exists_chain (Q : Triangle) :
    ∀ᵐ z ∂phaseMeasure Q, Nonempty (FlightChain Q z) := by
  have hr : ∀ᵐ z ∂phaseMeasure Q, z ∉ vertexExceptional Q := by
    rw [ae_iff]
    convert phaseMeasure_vertexExceptional Q using 2
    ext a; simp
  filter_upwards [ae_position_in_table Q, hr] with z hx hz
  exact exists_chain_of_not_exceptional Q z hx hz

end TriangularBilliards
end

end OAI
end
end

section
section
namespace OAI


open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
namespace TriangularBilliards
open Filter
open scoped Topology

/-! Borel realization of full chains.  Countable collision data, rather than
an uncountable trajectory selector, permit a standard-Borel inverse. -/
namespace Triangle

lemma side_coords_nonneg (Q : Triangle) {x : ℂ} {i : Fin 3}
    (hx : x ∈ Q.side i) (k : Fin 3) : 0 ≤ Q.basis.coord k x := by
  rw [side, openSegment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  change 0 ≤ Q.basis.coord k (AffineMap.lineMap (Q.basis i) (Q.basis (i + 1)) t)
  rw [AffineMap.apply_lineMap, Q.basis.coord_apply, Q.basis.coord_apply,
    AffineMap.lineMap_apply_module]
  split_ifs <;> simp only [smul_eq_mul] <;> nlinarith [ht.1, ht.2]

lemma measurableSet_side (Q : Triangle) (i : Fin 3) : MeasurableSet (Q.side i) := by
  rw [side, openSegment_eq_image_lineMap]
  have hne : Q.vertex i ≠ Q.vertex (i + 1) :=
    Q.nondegenerate.injective.ne (by decide +revert)
  have hc : Continuous (fun t : ℝ => AffineMap.lineMap (Q.vertex i) (Q.vertex (i + 1)) t) := by
    fun_prop
  exact (hc.measurableEmbedding (AffineMap.lineMap_injective ℝ hne)).measurableSet_image.mpr
    measurableSet_Ioo

lemma inside_of_midpoint (Q : Triangle) {x v : ℂ} {a b : ℝ} {i j : Fin 3}
    (ha : x ∈ Q.side i) (hb : x + (b - a) • v ∈ Q.side j)
    (hm : x + ((a + b) / 2 - a) • v ∈ Q.table)
    {t : ℝ} (hat : a < t) (htb : t < b) : x + (t - a) • v ∈ Q.table := by
  rw [Q.table_iff_coords] at hm ⊢
  intro k
  have h0 := Q.side_coords_nonneg ha k
  have h1 := Q.side_coords_nonneg hb k
  have hmid := hm k
  rw [Q.coord_shift] at h1 hmid ⊢
  by_cases hd : 0 ≤ Q.slope k v
  · by_cases hz : Q.slope k v = 0
    · simp only [hz, mul_zero, add_zero] at hmid ⊢
      exact hmid
    · exact add_pos_of_nonneg_of_pos h0 (mul_pos (sub_pos.mpr hat) (lt_of_le_of_ne hd (Ne.symm hz)))
  · have hp : 0 < (b - t) * (-Q.slope k v) :=
      mul_pos (sub_pos.mpr htb) (neg_pos.mpr (lt_of_not_ge hd))
    nlinarith

end Triangle

abbrev ChainData := (ℤ → ℝ) × (ℤ → ℂ) × (ℤ → Circle) × (ℤ → Fin 3)

namespace ChainData

def time (c : ChainData) := c.1
def point (c : ChainData) := c.2.1
def direction (c : ChainData) := c.2.2.1
def wall (c : ChainData) := c.2.2.2

/-- Every predicate is a countable combination of Borel coordinate predicates.
Midpoint membership entails the entire open-flight condition by convexity. -/
def Valid (Q : Triangle) (z : Phase) (c : ChainData) : Prop :=
  (∀ n : ℤ, c.time n < c.time (n + 1)) ∧
  (∀ k : ℤ, ∃ n : ℤ, c.time n < k) ∧
  (∀ k : ℤ, ∃ n : ℤ, (k : ℝ) < c.time n) ∧
  c.time 0 < 0 ∧ 0 < c.time 1 ∧
  (∀ n : ℤ, c.point n ∈ Q.side (c.wall n)) ∧
  (∀ n : ℤ, c.point (n + 1) = c.point n +
    (c.time (n + 1) - c.time n) • (c.direction n : ℂ)) ∧
  (∀ n : ℤ, c.point n + ((c.time n + c.time (n + 1)) / 2 - c.time n) •
    (c.direction n : ℂ) ∈ Q.table) ∧
  z.1 = c.point 0 + (-c.time 0) • (c.direction 0 : ℂ) ∧
  z.2 = c.direction 0 ∧
  (∀ n : ℤ, (c.direction n : ℂ) = reflect (Q.tangent (c.wall n))
    (c.direction (n - 1) : ℂ))

def toChain {Q : Triangle} {z : Phase} {c : ChainData} (h : c.Valid Q z) : FlightChain Q z where
  time := c.time
  point := c.point
  direction := c.direction
  wall := c.wall
  increasing := strictMono_int_of_lt_succ h.1
  unbounded_below := fun t => by
    obtain ⟨k, hk⟩ := exists_int_lt t
    obtain ⟨n, hn⟩ := h.2.1 k
    exact ⟨n, hn.trans hk⟩
  unbounded_above := fun t => by
    obtain ⟨k, hk⟩ := exists_int_gt t
    obtain ⟨n, hn⟩ := h.2.2.1 k
    exact ⟨n, hk.trans hn⟩
  zero_before := h.2.2.2.1
  zero_after := h.2.2.2.2.1
  on_side := h.2.2.2.2.2.1
  flight := h.2.2.2.2.2.2.1
  inside := fun n t ht ht' => by
    apply Q.inside_of_midpoint (j := c.wall (n + 1))
      (h.2.2.2.2.2.1 n) _ (h.2.2.2.2.2.2.2.1 n) ht ht'
    rw [← h.2.2.2.2.2.2.1 n]
    exact h.2.2.2.2.2.1 (n + 1)
  start_point := h.2.2.2.2.2.2.2.2.1
  start_direction := h.2.2.2.2.2.2.2.2.2.1
  specular := h.2.2.2.2.2.2.2.2.2.2

end ChainData

namespace FlightChain

def data {Q : Triangle} {z : Phase} (c : FlightChain Q z) : ChainData :=
  (c.time, c.point, c.direction, c.wall)

lemma data_valid {Q : Triangle} {z : Phase} (c : FlightChain Q z) : c.data.Valid Q z := by
  refine ⟨fun n => c.increasing (by omega), fun k => c.unbounded_below k,
    fun k => c.unbounded_above k, c.zero_before, c.zero_after, c.on_side,
    c.flight, ?_, c.start_point, c.start_direction, c.specular⟩
  intro n
  have h := c.increasing (show n < n + 1 by omega)
  exact c.inside n ((c.time n + c.time (n + 1)) / 2) (by linarith) (by linarith)

end FlightChain

namespace ChainData

@[fun_prop] lemma continuous_time (n : ℤ) : Continuous (fun c : ChainData => c.time n) := by
  unfold time
  fun_prop

@[fun_prop] lemma continuous_point (n : ℤ) : Continuous (fun c : ChainData => c.point n) := by
  unfold point
  fun_prop

@[fun_prop] lemma continuous_direction (n : ℤ) : Continuous (fun c : ChainData => c.direction n) := by
  unfold direction
  fun_prop

@[fun_prop] lemma continuous_wall (n : ℤ) : Continuous (fun c : ChainData => c.wall n) := by
  unfold wall
  fun_prop

lemma measurableSet_side_mem {α : Type uAlpha} [MeasurableSpace α] (Q : Triangle)
    {p : α → ℂ} {w : α → Fin 3} (hp : Measurable p) (hw : Measurable w) :
    MeasurableSet {a | p a ∈ Q.side (w a)} := by
  have he : {a | p a ∈ Q.side (w a)} =
      ⋃ i : Fin 3, {a | w a = i} ∩ p ⁻¹' Q.side i := by
    ext a
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage]
    exact ⟨fun h => ⟨w a, rfl, h⟩, fun ⟨i, hi, hs⟩ => hi ▸ hs⟩
  rw [he]
  exact MeasurableSet.iUnion fun i =>
    (measurableSet_eq_fun hw measurable_const).inter ((Q.measurableSet_side i).preimage hp)

lemma measurableSet_valid (Q : Triangle) :
    MeasurableSet {a : Phase × ChainData | a.2.Valid Q a.1} := by
  have ht (n : ℤ) : Measurable (fun a : Phase × ChainData => a.2.time n) :=
    (continuous_time n).measurable.comp measurable_snd
  have hp (n : ℤ) : Measurable (fun a : Phase × ChainData => a.2.point n) :=
    (continuous_point n).measurable.comp measurable_snd
  have hd (n : ℤ) : Measurable (fun a : Phase × ChainData => a.2.direction n) :=
    (continuous_direction n).measurable.comp measurable_snd
  have hv (n : ℤ) : Measurable (fun a : Phase × ChainData => (a.2.direction n : ℂ)) := by
    exact (show Continuous (fun z : Circle => (z : ℂ)) by fun_prop).measurable.comp (hd n)
  have hw (n : ℤ) : Measurable (fun a : Phase × ChainData => a.2.wall n) :=
    (continuous_wall n).measurable.comp measurable_snd
  simp only [Valid, ofPred_and, ofPred_forall, ofPred_exists]
  refine (MeasurableSet.iInter fun n => measurableSet_lt (ht n) (ht (n + 1))).inter ?_
  refine (MeasurableSet.iInter fun k : ℤ => MeasurableSet.iUnion fun n =>
    measurableSet_lt (ht n) measurable_const).inter ?_
  refine (MeasurableSet.iInter fun k : ℤ => MeasurableSet.iUnion fun n =>
    measurableSet_lt measurable_const (ht n)).inter ?_
  refine (measurableSet_lt (ht 0) measurable_const).inter ?_
  refine (measurableSet_lt measurable_const (ht 1)).inter ?_
  refine (MeasurableSet.iInter fun n => measurableSet_side_mem Q (hp n) (hw n)).inter ?_
  refine (MeasurableSet.iInter fun n => measurableSet_eq_fun (hp (n + 1))
    ((hp n).add (((ht (n + 1)).sub (ht n)).smul (hv n)))).inter ?_
  refine (MeasurableSet.iInter fun n => Q.measurableSet_table.preimage
    ((hp n).add (((((ht n).add (ht (n + 1))).div_const 2).sub (ht n)).smul (hv n)))).inter ?_
  refine (measurableSet_eq_fun (measurable_fst.comp measurable_fst)
    ((hp 0).add ((ht 0).neg.smul (hv 0)))).inter ?_
  refine (measurableSet_eq_fun (measurable_snd.comp measurable_fst) (hd 0)).inter ?_
  apply MeasurableSet.iInter
  intro n
  have he : Measurable (fun a : Phase × ChainData => Q.tangent (a.2.wall n)) :=
    (measurable_of_countable Q.tangent).comp (hw n)
  exact measurableSet_eq_fun (hv n) ((he.div (Complex.continuous_conj.measurable.comp he)).mul
    (Complex.continuous_conj.measurable.comp (hv (n - 1))))

end ChainData

/-- Standard-Borel coding of the exact complete trajectories. -/
abbrev CodedChain (Q : Triangle) := {a : Phase × ChainData // a.2.Valid Q a.1}

namespace CodedChain

instance standardBorel (Q : Triangle) : StandardBorelSpace (CodedChain Q) :=
  (ChainData.measurableSet_valid Q).standardBorel

def initial {Q : Triangle} (c : CodedChain Q) : Phase := c.val.1

def chain {Q : Triangle} (c : CodedChain Q) : FlightChain Q c.initial := ChainData.toChain c.property

instance nonempty (Q : Triangle) : Nonempty (CodedChain Q) := by
  obtain ⟨z, ⟨c⟩⟩ := (ae_exists_chain Q).exists
  exact ⟨⟨(z, c.data), c.data_valid⟩⟩

lemma initial_injective (Q : Triangle) : Function.Injective (initial (Q := Q)) := by
  rintro ⟨⟨z, c⟩, hc⟩ ⟨⟨w, d⟩, hd⟩ h
  change z = w at h
  subst w
  have he := congrArg FlightChain.data (FlightChain.unique (ChainData.toChain hc) (ChainData.toChain hd))
  apply Subtype.ext
  change c = d at he
  exact congrArg (fun x : ChainData => (z, x)) he

lemma initial_embedding (Q : Triangle) : MeasurableEmbedding (initial (Q := Q)) :=
  (measurable_fst.comp measurable_subtype_coe).measurableEmbedding (initial_injective Q)

lemma range_initial (Q : Triangle) :
    range (initial (Q := Q)) = {z | Nonempty (FlightChain Q z)} := by
  ext z
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c.chain⟩
  · rintro ⟨c⟩
    exact ⟨⟨(z, c.data), c.data_valid⟩, rfl⟩

lemma measurableSet_regular (Q : Triangle) : MeasurableSet {z | Nonempty (FlightChain Q z)} := by
  rw [← range_initial]
  exact (initial_embedding Q).measurableSet_range

/-- The inverse is Borel by Lusin--Souslin, not by choice of arbitrary
unmeasurable representatives. It agrees with every exact chain at its initial state. -/
def fromPhase (Q : Triangle) : Phase → CodedChain Q := (initial_embedding Q).invFun

@[fun_prop] lemma measurable_fromPhase (Q : Triangle) : Measurable (fromPhase Q) :=
  (initial_embedding Q).measurable_invFun

lemma fromPhase_initial (Q : Triangle) (c : CodedChain Q) : fromPhase Q c.initial = c :=
  (initial_embedding Q).leftInverse_invFun c

def index {Q : Triangle} (a : CodedChain Q × ℝ) : ℤ :=
  Classical.choose (a.1.chain.exists_flight a.2)

lemma index_spec {Q : Triangle} (a : CodedChain Q × ℝ) :
    a.1.chain.time (index a) ≤ a.2 ∧ a.2 < a.1.chain.time (index a + 1) :=
  Classical.choose_spec (a.1.chain.exists_flight a.2)

lemma index_eq_iff {Q : Triangle} (a : CodedChain Q × ℝ) (n : ℤ) :
    index a = n ↔ a.1.chain.time n ≤ a.2 ∧ a.2 < a.1.chain.time (n + 1) := by
  constructor
  · rintro rfl
    exact index_spec a
  · intro h
    exact a.1.chain.flight_index_unique (index_spec a) h

@[fun_prop] lemma measurable_time (Q : Triangle) (n : ℤ) :
    Measurable (fun c : CodedChain Q => c.chain.time n) :=
  (ChainData.continuous_time n).measurable.comp (measurable_snd.comp measurable_subtype_coe)

@[fun_prop] lemma measurable_point (Q : Triangle) (n : ℤ) :
    Measurable (fun c : CodedChain Q => c.chain.point n) :=
  (ChainData.continuous_point n).measurable.comp (measurable_snd.comp measurable_subtype_coe)

@[fun_prop] lemma measurable_direction (Q : Triangle) (n : ℤ) :
    Measurable (fun c : CodedChain Q => c.chain.direction n) :=
  (ChainData.continuous_direction n).measurable.comp (measurable_snd.comp measurable_subtype_coe)

@[fun_prop] lemma measurable_index (Q : Triangle) : Measurable (index (Q := Q)) := by
  apply measurable_to_countable
  intro a
  have he : index ⁻¹' {index a} =
      {b : CodedChain Q × ℝ | b.1.chain.time (index a) ≤ b.2} ∩
      {b : CodedChain Q × ℝ | b.2 < b.1.chain.time (index a + 1)} := by
    ext b
    exact index_eq_iff b (index a)
  rw [he]
  exact (measurableSet_le ((measurable_time Q _).comp measurable_fst) measurable_snd).inter
    (measurableSet_lt measurable_snd ((measurable_time Q _).comp measurable_fst))

@[fun_prop] lemma measurable_at (Q : Triangle) :
    Measurable (fun a : CodedChain Q × ℝ => a.1.chain.at a.2) := by
  have hf (n : ℤ) : Measurable (fun a : CodedChain Q × ℝ =>
      (a.1.chain.point n + (a.2 - a.1.chain.time n) • (a.1.chain.direction n : ℂ),
        a.1.chain.direction n)) := by
    have hv : Measurable (fun a : CodedChain Q × ℝ => (a.1.chain.direction n : ℂ)) :=
      (show Continuous (fun v : Circle => (v : ℂ)) by fun_prop).measurable.comp
        ((measurable_direction Q n).comp measurable_fst)
    exact (((measurable_point Q n).comp measurable_fst).add
      ((measurable_snd.sub ((measurable_time Q n).comp measurable_fst)).smul hv)).prodMk
        ((measurable_direction Q n).comp measurable_fst)
  have heval : Measurable (fun b : (CodedChain Q × ℝ) × ℤ =>
      (b.1.1.chain.point b.2 + (b.1.2 - b.1.1.chain.time b.2) •
        (b.1.1.chain.direction b.2 : ℂ), b.1.1.chain.direction b.2)) :=
    measurable_from_prod_countable_left hf
  convert heval.comp (measurable_id.prodMk (measurable_index Q)) using 1
  funext a
  exact a.1.chain.at_of_flight (index_spec a)

lemma fromPhase_at {Q : Triangle} {z : Phase} (c : FlightChain Q z) (t : ℝ) :
    (fromPhase Q z).chain.at t = c.at t := by
  let d : CodedChain Q := ⟨(z, c.data), c.data_valid⟩
  have hd : fromPhase Q z = d := fromPhase_initial Q d
  rw [hd]
  have hc : d.chain = c := FlightChain.unique _ _
  exact congrArg (fun e : FlightChain Q z => e.at t) hc

end CodedChain

/-- Joint Borel measurability of the actual chosen billiard flow, obtained
from the unique exact chain, including the singular-set identity convention. -/
lemma measurable_billiardFlow (Q : Triangle) :
    Measurable (fun a : ℝ × Phase => billiardFlow Q a.1 a.2) := by
  classical
  have hm : Measurable (fun a : ℝ × Phase =>
      (CodedChain.fromPhase Q a.2).chain.at a.1) :=
    (CodedChain.measurable_at Q).comp
      (((CodedChain.measurable_fromPhase Q).comp measurable_snd).prodMk measurable_fst)
  have hr : MeasurableSet {a : ℝ × Phase | Nonempty (FlightChain Q a.2)} :=
    (CodedChain.measurableSet_regular Q).preimage measurable_snd
  have he : (fun a : ℝ × Phase => billiardFlow Q a.1 a.2) =
      (fun a : ℝ × Phase => if Nonempty (FlightChain Q a.2) then
        (CodedChain.fromPhase Q a.2).chain.at a.1 else a.2) := by
    funext ⟨t, z⟩
    change billiardFlow Q t z = if Nonempty (FlightChain Q z) then
      (CodedChain.fromPhase Q z).chain.at t else z
    by_cases h : Nonempty (FlightChain Q z)
    · simp only [ite_eq_left h]
      rw [billiardFlow_eq_chain (Classical.choice h), CodedChain.fromPhase_at]
    · simp only [billiardFlow, dite_eq_right h, ite_eq_right h]
  rw [he]
  exact Measurable.ite hr hm measurable_snd

lemma measurable_billiardFlow_time (Q : Triangle) (t : ℝ) : Measurable (billiardFlow Q t) :=
  (measurable_billiardFlow Q).comp (measurable_const.prodMk measurable_id)

end TriangularBilliards

end

end OAI
end
end

section
section
namespace OAI

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section

namespace TriangularBilliards

local instance anglePeriodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Angular Haar probability in additive angle coordinates, used to
verify invariance of the explicit angular measure. -/
def angleMeasure : Measure (AddCircle (2 * Real.pi)) :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume

lemma measurePreserving_toCircle :
    MeasurePreserving (AddCircle.homeomorphCircle' : AddCircle (2 * Real.pi) → Circle) angleMeasure angularMeasure := by
  have hc : Measurable (fun t : ℝ => (t : AddCircle (2 * Real.pi))) :=
    (AddCircle.measurePreserving_mk (2 * Real.pi) 0).measurable
  have he : Measurable (AddCircle.homeomorphCircle' : AddCircle (2 * Real.pi) → Circle) :=
    AddCircle.homeomorphCircle'.continuous.measurable
  refine ⟨he, ?_⟩
  have hvol := ((AddCircle.measurePreserving_mk (2 * Real.pi) 0).smul_measure
    ((ENNReal.ofReal (2 * Real.pi))⁻¹)).map_eq
  simp only [zero_add] at hvol
  rw [angleMeasure, ← hvol, Measure.map_map he hc]
  rw [angularMeasure, Measure.restrict_congr_set Ico_ae_eq_Ioc]
  rfl

lemma measurePreserving_circle_mul (a : Circle) :
    MeasurePreserving (fun v : Circle => a * v) angularMeasure angularMeasure := by
  let θ : AddCircle (2 * Real.pi) := AddCircle.homeomorphCircle'.symm a
  have hθ : AddCircle.homeomorphCircle' θ = a := AddCircle.homeomorphCircle'.apply_symm_apply a
  have ha := (measurePreserving_add_left (volume : Measure (AddCircle (2 * Real.pi))) θ).smul_measure
    ((ENNReal.ofReal (2 * Real.pi))⁻¹)
  change MeasurePreserving (fun x : AddCircle (2 * Real.pi) => θ + x) angleMeasure angleMeasure at ha
  have hh := measurePreserving_toCircle.comp ha
  have hf : AddCircle.homeomorphCircle' ∘ (fun x : AddCircle (2 * Real.pi) => θ + x) =
      (fun v : Circle => a * v) ∘ AddCircle.homeomorphCircle' := by
    funext x
    exact (Real.Angle.toCircle_add θ x).trans
      (congrArg (fun v : Circle => v * Real.Angle.toCircle x) hθ)
  rw [hf] at hh
  have hr := hh.map_of_comp (by fun_prop) measurePreserving_toCircle.measurable
  rwa [measurePreserving_toCircle.map_eq] at hr

lemma measurePreserving_circle_inv :
    MeasurePreserving (fun v : Circle => v⁻¹) angularMeasure angularMeasure := by
  have hn := (Measure.measurePreserving_neg (volume : Measure (AddCircle (2 * Real.pi)))).smul_measure
    ((ENNReal.ofReal (2 * Real.pi))⁻¹)
  change MeasurePreserving (fun x : AddCircle (2 * Real.pi) => -x) angleMeasure angleMeasure at hn
  have hh := measurePreserving_toCircle.comp hn
  have hf : AddCircle.homeomorphCircle' ∘ (fun x : AddCircle (2 * Real.pi) => -x) =
      (fun v : Circle => v⁻¹) ∘ AddCircle.homeomorphCircle' := by
    funext x
    exact Real.Angle.toCircle_neg x
  rw [hf] at hh
  have hr := hh.map_of_comp (by fun_prop) measurePreserving_toCircle.measurable
  rwa [measurePreserving_toCircle.map_eq] at hr

lemma reflectedDirection_eq (Q : Triangle) (i : Fin 3) (v : Circle) :
    reflectedDirection Q i v = reflectedDirection Q i 1 * v⁻¹ := by
  apply Subtype.ext
  simp only [Circle.coe_mul, Circle.coe_inv_eq_conj]
  simp [reflectedDirection, reflect]

lemma measurePreserving_reflectedDirection (Q : Triangle) (i : Fin 3) :
    MeasurePreserving (reflectedDirection Q i) angularMeasure angularMeasure := by
  convert (measurePreserving_circle_mul (reflectedDirection Q i 1)).comp
    measurePreserving_circle_inv using 1
  funext v
  exact reflectedDirection_eq Q i v

lemma measurePreserving_wallReflection (Q : Triangle) (i : Fin 3) :
    MeasurePreserving (wallReflection Q i) volume volume := by
  have hs := measurePreserving_add_right (volume : Measure ℂ) (-Q.vertex i)
  have hr := (reflectIsometry (Q.tangent i) (Q.tangent_ne_zero i)).measurePreserving
  have ha := measurePreserving_add_left (volume : Measure ℂ) (Q.vertex i)
  convert ha.comp (hr.comp hs) using 1
  funext x
  simp only [Function.comp_apply, wallReflection, sub_eq_add_neg]
  rfl

/-- Ambient Liouville measure, before restriction and normalization. -/
def ambientMeasure : Measure Phase := volume.prod angularMeasure

/-- Reflection at a whole supporting line, on the ambient phase space. -/
def wallPhase (Q : Triangle) (i : Fin 3) (z : Phase) : Phase :=
  (wallReflection Q i z.1, reflectedDirection Q i z.2)

lemma measurePreserving_wallPhase (Q : Triangle) (i : Fin 3) :
    MeasurePreserving (wallPhase Q i) ambientMeasure ambientMeasure :=
  (measurePreserving_wallReflection Q i).prod (measurePreserving_reflectedDirection Q i)

/-- The free-flight shear on the whole plane, without any boundary. -/
def freeFlow (t : ℝ) (z : Phase) : Phase := (z.1 + t • (z.2 : ℂ), z.2)

lemma measurePreserving_freeFlow (t : ℝ) :
    MeasurePreserving (freeFlow t) ambientMeasure ambientMeasure := by
  have hs : MeasurePreserving (fun z : Circle × ℂ => (z.1, z.2 + t • (z.1 : ℂ)))
      (angularMeasure.prod volume) (angularMeasure.prod volume) := by
    apply (MeasurePreserving.id angularMeasure).skew_product
      (g := fun (v : Circle) (x : ℂ) => x + t • (v : ℂ))
    · fun_prop
    · exact Filter.Eventually.of_forall fun v =>
        (measurePreserving_add_right (volume : Measure ℂ) (t • (v : ℂ))).map_eq
  exact Measure.measurePreserving_swap.comp (hs.comp Measure.measurePreserving_swap)

end TriangularBilliards

end

end OAI
end
end

section
section
namespace OAI

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section

namespace TriangularBilliards

def phaseWord (Q : Triangle) (w : List (Fin 3)) (z : Phase) : Phase :=
  w.foldr (wallPhase Q) z

lemma measurePreserving_phaseWord (Q : Triangle) (w : List (Fin 3)) :
    MeasurePreserving (phaseWord Q w) ambientMeasure ambientMeasure := by
  induction w with
  | nil => exact MeasurePreserving.id ambientMeasure
  | cons i w hw => exact (measurePreserving_wallPhase Q i).comp hw

lemma wallPhase_involutive (Q : Triangle) (i : Fin 3) (z : Phase) :
    wallPhase Q i (wallPhase Q i z) = z := by
  apply Prod.ext
  · exact wallReflection_involutive Q i z.1
  · apply Subtype.ext
    exact reflect_involutive (Q.tangent_ne_zero i) z.2

namespace FlightChain

def line {Q : Triangle} {z : Phase} (c : FlightChain Q z) (n : ℤ) (t : ℝ) : Phase :=
  (c.point n + (t - c.time n) • (c.direction n : ℂ), c.direction n)

lemma line_zero {Q : Triangle} {z : Phase} (c : FlightChain Q z) (t : ℝ) :
    c.line 0 t = freeFlow t z := by
  apply Prod.ext
  · change c.point 0 + (t - c.time 0) • (c.direction 0 : ℂ) =
      z.1 + t • (z.2 : ℂ)
    rw [c.start_point, c.start_direction, sub_smul, neg_smul]
    abel
  · exact c.start_direction.symm

lemma line_succ {Q : Triangle} {z : Phase} (c : FlightChain Q z) (n : ℤ) (t : ℝ) :
    c.line (n + 1) t = wallPhase Q (c.wall (n + 1)) (c.line n t) := by
  have hv : (c.direction (n + 1) : ℂ) =
      reflect (Q.tangent (c.wall (n + 1))) (c.direction n : ℂ) := by
    simpa using c.specular (n + 1)
  apply Prod.ext
  · have hf := wallReflection_fixed_side Q (c.on_side (n + 1))
    have hd := wallReflection_sub Q (c.wall (n + 1))
      (c.point n + (t - c.time n) • (c.direction n : ℂ)) (c.point (n + 1))
    rw [hf, c.flight n] at hd
    have he : c.point n + (t - c.time n) • (c.direction n : ℂ) -
        (c.point n + (c.time (n + 1) - c.time n) • (c.direction n : ℂ)) =
        (t - c.time (n + 1)) • (c.direction n : ℂ) := by
      simp only [add_sub_add_left_eq_sub, ← sub_smul]
      congr 1
      ring
    rw [he, reflect_real_smul, ← hv] at hd
    change c.point (n + 1) + (t - c.time (n + 1)) • (c.direction (n + 1) : ℂ) = _
    rw [c.flight n]
    exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp hd).symm
  · exact Subtype.ext hv

lemma line_pred {Q : Triangle} {z : Phase} (c : FlightChain Q z) (n : ℤ) (t : ℝ) :
    c.line (n - 1) t = wallPhase Q (c.wall n) (c.line n t) := by
  have hh := c.line_succ (n - 1) t
  simp only [sub_add_cancel] at hh
  rw [hh, wallPhase_involutive]

lemma line_unfold {Q : Triangle} {z : Phase} (c : FlightChain Q z) (n : ℤ) (t : ℝ) :
    ∃ w : List (Fin 3), c.line n t = phaseWord Q w (freeFlow t z) := by
  induction n using Int.induction_on with
  | zero => exact ⟨[], c.line_zero t⟩
  | succ n hn =>
    obtain ⟨w, hw⟩ := hn
    exact ⟨c.wall (n + 1) :: w, (c.line_succ n t).trans (congrArg _ hw)⟩
  | pred n hn =>
    obtain ⟨w, hw⟩ := hn
    exact ⟨c.wall (-n) :: w, (c.line_pred (-n) t).trans (congrArg _ hw)⟩

/-- Every fixed-time endpoint is the value of one of countably many genuine
ambient measure-preserving Euclidean reflection/free-flight maps. -/
lemma at_unfold {Q : Triangle} {z : Phase} (c : FlightChain Q z) (t : ℝ) :
    ∃ w : List (Fin 3), c.at t = phaseWord Q w (freeFlow t z) := by
  obtain ⟨n, hn⟩ := c.exists_flight t
  rw [c.at_of_flight hn]
  exact c.line_unfold n t

end FlightChain

end TriangularBilliards

namespace TriangularBilliards

lemma phaseMeasure_eq_restrict (Q : Triangle) :
    phaseMeasure Q = (volume Q.table)⁻¹ • ambientMeasure.restrict (Q.table ×ˢ univ) := by
  rw [phaseMeasure, Measure.prod_smul_left, Measure.restrict_prod_eq_prod_univ]
  rfl

lemma phaseMeasure_absolutelyContinuous (Q : Triangle) : phaseMeasure Q ≪ ambientMeasure := by
  rw [phaseMeasure_eq_restrict]
  exact Measure.absolutelyContinuous_restrict.smul_left _

lemma side_mem_frontier (Q : Triangle) {i : Fin 3} {x : ℂ} (hx : x ∈ Q.side i) :
    x ∈ frontier (convexHull ℝ (range Q.vertex)) := by
  rw [frontier, mem_sdiff]
  refine ⟨subset_closure ?_, Q.side_not_table hx⟩
  exact (convex_convexHull ℝ _).segment_subset
    (subset_convexHull ℝ _ (mem_range_self i))
    (subset_convexHull ℝ _ (mem_range_self (i + 1))) (openSegment_subset_segment _ _ _ hx)

/-- All boundary-position phases form a measurable ambient-null set. -/
def boundaryPhase (Q : Triangle) : Set Phase :=
  frontier (convexHull ℝ (range Q.vertex)) ×ˢ univ

lemma measurableSet_boundaryPhase (Q : Triangle) : MeasurableSet (boundaryPhase Q) :=
  isClosed_frontier.measurableSet.prod MeasurableSet.univ

lemma ambientMeasure_boundaryPhase (Q : Triangle) : ambientMeasure (boundaryPhase Q) = 0 := by
  rw [ambientMeasure, boundaryPhase, Measure.prod_prod,
    (convex_convexHull ℝ (range Q.vertex)).addHaar_frontier volume, zero_mul]

/-- A countable explicit null superset of all trajectories at a boundary
at a prescribed time; it is defined without making trajectory choices. -/
def collisionExceptional (Q : Triangle) (t : ℝ) : Set Phase :=
  ⋃ w : List (Fin 3), (phaseWord Q w ∘ freeFlow t) ⁻¹' boundaryPhase Q

lemma measurableSet_collisionExceptional (Q : Triangle) (t : ℝ) :
    MeasurableSet (collisionExceptional Q t) :=
  MeasurableSet.iUnion fun w => (measurableSet_boundaryPhase Q).preimage
    ((measurePreserving_phaseWord Q w).comp (measurePreserving_freeFlow t)).measurable

lemma phaseMeasure_collisionExceptional (Q : Triangle) (t : ℝ) :
    phaseMeasure Q (collisionExceptional Q t) = 0 := by
  apply phaseMeasure_absolutelyContinuous Q
  apply measure_iUnion_null
  intro w
  rw [((measurePreserving_phaseWord Q w).comp (measurePreserving_freeFlow t)).measure_preimage
    (measurableSet_boundaryPhase Q).nullMeasurableSet, ambientMeasure_boundaryPhase]

lemma FlightChain.mem_collisionExceptional {Q : Triangle} {z : Phase}
    (c : FlightChain Q z) {t : ℝ} (ht : t ∈ range c.time) :
    z ∈ collisionExceptional Q t := by
  obtain ⟨n, rfl⟩ := ht
  obtain ⟨w, hw⟩ := c.at_unfold (c.time n)
  refine mem_iUnion.mpr ⟨w, ?_⟩
  change phaseWord Q w (freeFlow (c.time n) z) ∈ boundaryPhase Q
  rw [← hw, c.at_of_flight ⟨le_rfl, c.increasing (by omega)⟩]
  simp only [sub_self, zero_smul, add_zero]
  exact ⟨side_mem_frontier Q (c.on_side n), mem_univ _⟩

/-- Remove only the fixed-time collision set from the conull regular states. -/
def regularAt (Q : Triangle) (t : ℝ) : Set Phase :=
  {z | Nonempty (FlightChain Q z)} \ collisionExceptional Q t

lemma measurableSet_regularAt (Q : Triangle) (t : ℝ) : MeasurableSet (regularAt Q t) :=
  (CodedChain.measurableSet_regular Q).diff (measurableSet_collisionExceptional Q t)

lemma ae_regularAt (Q : Triangle) (t : ℝ) : ∀ᵐ z ∂phaseMeasure Q, z ∈ regularAt Q t := by
  filter_upwards [ae_exists_chain Q, (measure_eq_zero_iff_ae_notMem.mp
    (phaseMeasure_collisionExceptional Q t))] with z hz ht
  exact ⟨hz, ht⟩

lemma regularAt_subset_table (Q : Triangle) (t : ℝ) : regularAt Q t ⊆ Q.table ×ˢ univ := by
  rintro z ⟨⟨c⟩, _⟩
  exact ⟨c.initial_inside, mem_univ _⟩

lemma regularAt_noncollision {Q : Triangle} {t : ℝ} {z : Phase} (hz : z ∈ regularAt Q t)
    (c : FlightChain Q z) : t ∉ range c.time :=
  fun ht => hz.2 (c.mem_collisionExceptional ht)

lemma flow_mem_table_of_regularAt {Q : Triangle} {t : ℝ} {z : Phase}
    (hz : z ∈ regularAt Q t) : billiardFlow Q t z ∈ Q.table ×ˢ univ := by
  obtain ⟨c⟩ := hz.1
  obtain ⟨n, hn⟩ := c.exists_flight t
  have hne : c.time n ≠ t := fun h => regularAt_noncollision hz c ⟨n, h⟩
  have ht : c.time n < t ∧ t < c.time (n + 1) := ⟨lt_of_le_of_ne hn.1 hne, hn.2⟩
  rw [billiardFlow_eq_chain c]
  exact ⟨(c.rebase t n ht).initial_inside, mem_univ _⟩

lemma flow_injective_regularAt (Q : Triangle) (t : ℝ) :
    InjOn (billiardFlow Q t) (regularAt Q t) := by
  intro z hz y hy he
  obtain ⟨c⟩ := hz.1
  obtain ⟨d⟩ := hy.1
  have hc := billiardFlow_add_of_noncollision c (-t) t (regularAt_noncollision hz c)
  have hd := billiardFlow_add_of_noncollision d (-t) t (regularAt_noncollision hy d)
  rw [he] at hc
  simpa only [neg_add_cancel, billiardFlow_zero] using hc.trans hd.symm

/-- The flow law for every real pair, outside a proved null set. -/

lemma billiardFlow_cocycle (Q : Triangle) (s t : ℝ) :
    billiardFlow Q (s + t) =ᵐ[phaseMeasure Q] (billiardFlow Q s ∘ billiardFlow Q t) := by
  filter_upwards [ae_regularAt Q t] with z hz
  obtain ⟨c⟩ := hz.1
  exact billiardFlow_add_of_noncollision c s t (regularAt_noncollision hz c)

end TriangularBilliards

end

end OAI
end
end

section
section
namespace OAI


open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section

namespace TriangularBilliards

/-- On a measurable set, an injective measurable map that locally agrees
with one of countably many measure-preserving embeddings preserves the
measure of that set. The pieces need not be open. -/
lemma measure_image_countably_piecewise
    {α : Type uAlpha} [MeasurableSpace α] [MeasurableEq α]
    (μ : Measure α) {f : α → α} (hf : Measurable f) {R : Set α}
    (hR : MeasurableSet R) (hi : InjOn f R) (F : ℕ → α → α)
    (hF : ∀ n, MeasurePreserving (F n) μ μ)
    (hE : ∀ n, MeasurableEmbedding (F n))
    (hcover : ∀ x ∈ R, ∃ n, f x = F n x) : μ (f '' R) = μ R := by
  let S : ℕ → Set α := fun n => R ∩ {x | f x = F n x}
  let D : ℕ → Set α := disjointed S
  have hSm (n : ℕ) : MeasurableSet (S n) :=
    hR.inter (measurableSet_eq_fun hf (hF n).measurable)
  have hDm (n : ℕ) : MeasurableSet (D n) := MeasurableSet.disjointed hSm n
  have hDS (n : ℕ) : D n ⊆ S n := disjointed_subset S n
  have hDR (n : ℕ) : D n ⊆ R := fun _ hx => (hDS n hx).1
  have hDeq : (⋃ n, D n) = R := by
    rw [show (⋃ n, D n) = ⋃ n, S n from iUnion_disjointed]
    ext x
    simp only [mem_iUnion, S, mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun ⟨_, hx, _⟩ => hx, fun hx => by
      obtain ⟨n, hn⟩ := hcover x hx
      exact ⟨n, hx, hn⟩⟩
  have himage (n : ℕ) : f '' D n = F n '' D n := by
    apply image_congr
    intro x hx
    exact (hDS n hx).2
  have hIm (n : ℕ) : MeasurableSet (f '' D n) := by
    rw [himage]
    exact (hE n).measurableSet_image.mpr (hDm n)
  have hId : Pairwise (Function.onFun Disjoint (fun n => f '' D n)) := by
    intro n m hnm
    change Disjoint (f '' D n) (f '' D m)
    rw [disjoint_left]
    rintro y ⟨a, ha, rfl⟩ ⟨b, hb, he⟩
    have hab := hi (hDR m hb) (hDR n ha) he
    subst b
    exact Set.disjoint_left.mp (disjoint_disjointed S hnm) ha hb
  have hmeasure (n : ℕ) : μ (f '' D n) = μ (D n) := by
    rw [himage]
    have hh := (hF n).measure_preimage ((hE n).measurableSet_image.mpr (hDm n)).nullMeasurableSet
    rw [preimage_image_eq _ (hE n).injective] at hh
    exact hh.symm
  calc
    μ (f '' R) = μ (⋃ n, f '' D n) := by rw [← hDeq, image_iUnion]
    _ = ∑' n, μ (f '' D n) := measure_iUnion hId hIm
    _ = ∑' n, μ (D n) := tsum_congr hmeasure
    _ = μ R := by rw [← measure_iUnion (disjoint_disjointed S) hDm, hDeq]

end TriangularBilliards

namespace TriangularBilliards

lemma phaseWord_injective (Q : Triangle) (w : List (Fin 3)) :
    Function.Injective (phaseWord Q w) := by
  induction w with
  | nil => exact Function.injective_id
  | cons i w hw =>
    exact (Function.LeftInverse.injective (wallPhase_involutive Q i)).comp hw

lemma freeFlow_add (s t : ℝ) (z : Phase) : freeFlow s (freeFlow t z) = freeFlow (s + t) z := by
  apply Prod.ext
  · simp only [freeFlow, add_smul]
    abel
  · rfl

lemma freeFlow_zero (z : Phase) : freeFlow 0 z = z := by simp [freeFlow]

lemma freeFlow_injective (t : ℝ) : Function.Injective (freeFlow t) := by
  have h : Function.LeftInverse (freeFlow (-t)) (freeFlow t) := by
    intro z
    rw [freeFlow_add, neg_add_cancel, freeFlow_zero]
  exact h.injective

lemma measurableEmbedding_branch (Q : Triangle) (t : ℝ) (w : List (Fin 3)) :
    MeasurableEmbedding (phaseWord Q w ∘ freeFlow t) :=
  (((measurePreserving_phaseWord Q w).comp (measurePreserving_freeFlow t)).measurable).measurableEmbedding
    ((phaseWord_injective Q w).comp (freeFlow_injective t))

lemma phaseMeasure_eq_regularAt (Q : Triangle) (t : ℝ) :
    phaseMeasure Q = (volume Q.table)⁻¹ • ambientMeasure.restrict (regularAt Q t) := by
  calc
    phaseMeasure Q = (phaseMeasure Q).restrict (regularAt Q t) :=
      (Measure.restrict_eq_self_of_ae_mem (ae_regularAt Q t)).symm
    _ = _ := by rw [phaseMeasure_eq_restrict, Measure.restrict_smul,
      Measure.restrict_restrict_of_subset (regularAt_subset_table Q t)]

/-- Exact Liouville-measure preservation of every actual billiard time map.
The proof uses finite unfolding and injectivity, not an assumed dynamical
invariance or a numerical/recurrence input. -/
lemma measurePreserving_billiardFlow (Q : Triangle) (t : ℝ) :
    MeasurePreserving (billiardFlow Q t) (phaseMeasure Q) (phaseMeasure Q) := by
  refine ⟨measurable_billiardFlow_time Q t, ?_⟩
  apply Measure.eq_of_le_of_measure_univ_eq
  · apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.map_apply (measurable_billiardFlow_time Q t) hA]
    obtain ⟨e, he⟩ := exists_surjective_nat (List (Fin 3))
    let R := (billiardFlow Q t) ⁻¹' A ∩ regularAt Q t
    have hR : MeasurableSet R := (hA.preimage (measurable_billiardFlow_time Q t)).inter
      (measurableSet_regularAt Q t)
    have hsub : R ⊆ regularAt Q t := inter_subset_right
    have hcover : ∀ z ∈ R, ∃ n, billiardFlow Q t z =
        (phaseWord Q (e n) ∘ freeFlow t) z := by
      intro z hz
      obtain ⟨c⟩ := hz.2.1
      obtain ⟨w, hw⟩ := c.at_unfold t
      obtain ⟨n, rfl⟩ := he w
      exact ⟨n, (billiardFlow_eq_chain c t).trans hw⟩
    have hmeasure := measure_image_countably_piecewise ambientMeasure
      (measurable_billiardFlow_time Q t) hR
      ((flow_injective_regularAt Q t).mono hsub)
      (fun n => phaseWord Q (e n) ∘ freeFlow t)
      (fun n => (measurePreserving_phaseWord Q (e n)).comp (measurePreserving_freeFlow t))
      (fun n => measurableEmbedding_branch Q t (e n)) hcover
    have hcontain : billiardFlow Q t '' R ⊆ A ∩ (Q.table ×ˢ univ) := by
      rintro y ⟨z, hz, rfl⟩
      exact ⟨hz.1, flow_mem_table_of_regularAt hz.2⟩
    calc
      phaseMeasure Q ((billiardFlow Q t) ⁻¹' A) =
          (volume Q.table)⁻¹ * ambientMeasure R := by
        rw [phaseMeasure_eq_regularAt Q t, Measure.smul_apply,
          Measure.restrict_apply (hA.preimage (measurable_billiardFlow_time Q t)), smul_eq_mul]
      _ = (volume Q.table)⁻¹ * ambientMeasure (billiardFlow Q t '' R) := by rw [hmeasure]
      _ ≤ (volume Q.table)⁻¹ * ambientMeasure (A ∩ (Q.table ×ˢ univ)) :=
        by gcongr
      _ = phaseMeasure Q A := by
        rw [phaseMeasure_eq_restrict, Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]
  · rw [Measure.map_apply (measurable_billiardFlow_time Q t) MeasurableSet.univ, preimage_univ]

/-- Geometric and nonvacuity conclusions for every nondegenerate triangle.
Only ergodicity requires an irrational angle. -/
theorem geometric_obligations (Q : Triangle) :
    phaseMeasure Q univ = 1 ∧
    (∀ᵐ z ∂phaseMeasure Q, Nonempty (FlightChain Q z)) ∧
    (∀ (z : Phase) (c d : FlightChain Q z), c = d) ∧
    (∀ t : ℝ, MeasurePreserving (billiardFlow Q t) (phaseMeasure Q) (phaseMeasure Q)) ∧
    (∀ s t : ℝ, billiardFlow Q (s + t) =ᵐ[phaseMeasure Q]
      (billiardFlow Q s ∘ billiardFlow Q t)) :=
  ⟨phaseMeasure_univ Q, ae_exists_chain Q, fun _ c d => c.unique d,
    measurePreserving_billiardFlow Q, billiardFlow_cocycle Q⟩

end TriangularBilliards

end

end OAI
end
end

section
section
namespace OAI

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section

/-! Euclidean radial smoothing in local charts, used to construct
the global operator on the triangular double. -/

open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff

noncomputable section

namespace TriangularBilliards.SpatialSmoothing

/-- An explicit smooth radial bump. It is one on the half-unit disk,
positive in the unit disk and zero outside it. -/
def raw (x : ℂ) : ℝ := (ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2 ((2 : ℝ) • x)

lemma raw_nonneg (x : ℂ) : 0 ≤ raw x :=
  ((ContDiffBumpBase.ofInnerProductSpace ℂ).mem_Icc 2 _).1

lemma raw_le_one (x : ℂ) : raw x ≤ 1 :=
  ((ContDiffBumpBase.ofInnerProductSpace ℂ).mem_Icc 2 _).2

lemma raw_radial {x y : ℂ} (h : ‖x‖ = ‖y‖) : raw x = raw y := by
  simp only [raw, ContDiffBumpBase.ofInnerProductSpace, norm_smul, h]

lemma raw_neg (x : ℂ) : raw (-x) = raw x := raw_radial (norm_neg x)

lemma raw_contDiff : ContDiff ℝ ∞ raw := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hs := (ContDiffBumpBase.ofInnerProductSpace ℂ).smooth.contDiffAt
    (x := ((2 : ℝ), (2 : ℝ) • x))
    (prod_mem_nhds (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 2)) univ_mem)
  have hc : ContDiffAt ℝ ∞ (fun y : ℂ => ((2 : ℝ), (2 : ℝ) • y)) x := by fun_prop
  have hh := hs.comp x hc
  exact hh

lemma raw_support : support raw = ball (0 : ℂ) 1 := by
  have hs := (ContDiffBumpBase.ofInnerProductSpace ℂ).support 2 (by norm_num)
  ext x
  change ((2 : ℝ) • x) ∈ support ((ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2) ↔ _
  rw [hs]
  simp only [mem_ball_zero_iff, norm_smul, Real.norm_ofNat]
  constructor <;> intro h <;> linarith

lemma raw_hasCompactSupport : HasCompactSupport raw := by
  rw [HasCompactSupport, tsupport, raw_support, closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
  exact isCompact_closedBall _ _

lemma raw_integrable : Integrable raw volume :=
  raw_contDiff.continuous.integrable_of_hasCompactSupport raw_hasCompactSupport

lemma raw_integral_pos : 0 < ∫ x : ℂ, raw x := by
  apply (integral_pos_iff_support_of_nonneg raw_nonneg raw_integrable).mpr
  rw [raw_support]
  exact measure_ball_pos volume 0 (by norm_num)

/-- The chosen radial mollifier of unit mass. -/
def rho (x : ℂ) : ℝ := raw x / ∫ y : ℂ, raw y

lemma rho_nonneg (x : ℂ) : 0 ≤ rho x := div_nonneg (raw_nonneg x) raw_integral_pos.le

lemma rho_radial {x y : ℂ} (h : ‖x‖ = ‖y‖) : rho x = rho y := by
  rw [rho, rho, raw_radial h]

lemma rho_neg (x : ℂ) : rho (-x) = rho x := rho_radial (norm_neg x)

lemma rho_contDiff : ContDiff ℝ ∞ rho := raw_contDiff.div_const _

lemma rho_support : support rho = ball (0 : ℂ) 1 := by
  change support (fun x => raw x / ∫ y : ℂ, raw y) = _
  rw [support_div, raw_support, support_const raw_integral_pos.ne', inter_univ]

lemma rho_hasCompactSupport : HasCompactSupport rho := by
  rw [HasCompactSupport, tsupport, rho_support, closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
  exact isCompact_closedBall _ _

lemma rho_integrable : Integrable rho volume := raw_integrable.div_const _

lemma rho_integral : ∫ x : ℂ, rho x = 1 := by
  change (∫ x : ℂ, raw x / ∫ y : ℂ, raw y) = 1
  rw [integral_div]
  exact div_self raw_integral_pos.ne'

/-- Exact two-dimensional rescaling `ε⁻² ρ(x/ε)`. -/
def kernel (ε : ℝ) (x : ℂ) : ℝ := (ε ^ 2)⁻¹ * rho (ε⁻¹ • x)

lemma kernel_nonneg (ε : ℝ) (x : ℂ) : 0 ≤ kernel ε x :=
  mul_nonneg (inv_nonneg.mpr (sq_nonneg ε)) (rho_nonneg _)

lemma kernel_radial (ε : ℝ) {x y : ℂ} (h : ‖x‖ = ‖y‖) : kernel ε x = kernel ε y := by
  have hs : ‖ε⁻¹ • x‖ = ‖ε⁻¹ • y‖ := by rw [norm_smul, norm_smul, h]
  rw [kernel, kernel, rho_radial hs]

lemma kernel_neg (ε : ℝ) (x : ℂ) : kernel ε (-x) = kernel ε x :=
  kernel_radial ε (norm_neg x)

lemma kernel_contDiff (ε : ℝ) : ContDiff ℝ ∞ (kernel ε) :=
  contDiff_const.mul (rho_contDiff.comp (by fun_prop :
    ContDiff ℝ ∞ (fun x : ℂ => ε⁻¹ • x)))

lemma kernel_support {ε : ℝ} (hε : 0 < ε) : support (kernel ε) = ball (0 : ℂ) ε := by
  ext x
  rw [mem_support]
  change (ε ^ 2)⁻¹ * rho (ε⁻¹ • x) ≠ 0 ↔ _
  rw [mul_ne_zero_iff]
  have hne : (ε ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hε.ne')
  rw [and_iff_right hne, ← mem_support, rho_support]
  simp only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε,
    ← div_eq_inv_mul]
  rw [div_lt_iff₀ hε, one_mul]

lemma kernel_hasCompactSupport {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (kernel ε) := by
  rw [HasCompactSupport, tsupport, kernel_support hε, closure_ball _ hε.ne']
  exact isCompact_closedBall _ _

lemma kernel_integrable {ε : ℝ} (hε : 0 < ε) : Integrable (kernel ε) volume :=
  (kernel_contDiff ε).continuous.integrable_of_hasCompactSupport (kernel_hasCompactSupport hε)

lemma kernel_integral {ε : ℝ} (hε : 0 < ε) : ∫ x : ℂ, kernel ε x = 1 := by
  change (∫ x : ℂ, (ε ^ 2)⁻¹ * rho (ε⁻¹ • x)) = 1
  rw [integral_const_mul, Measure.integral_comp_smul volume rho ε⁻¹,
    Complex.finrank_real_complex, inv_pow, inv_inv, abs_of_nonneg (sq_nonneg ε),
    smul_eq_mul, rho_integral, mul_one]
  exact inv_mul_cancel₀ (pow_ne_zero _ hε.ne')

/-- The actual first-derivative kernel, with its exact dimensional scaling. -/
lemma kernel_fderiv (ε : ℝ) (x : ℂ) :
    fderiv ℝ (kernel ε) x = (ε ^ 3)⁻¹ • fderiv ℝ rho (ε⁻¹ • x) := by
  have hd := ((rho_contDiff.differentiable (by simp) (ε⁻¹ • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul ε⁻¹)).const_mul ((ε ^ 2)⁻¹)
  have he : (ε ^ 2)⁻¹ •
      ((fderiv ℝ rho (ε⁻¹ • x)).comp (ε⁻¹ • ContinuousLinearMap.id ℝ ℂ)) =
      (ε ^ 3)⁻¹ • fderiv ℝ rho (ε⁻¹ • x) := by
    rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id, smul_smul]
    congr 1
    ring
  rw [← he]
  exact hd.fderiv

lemma rho_fderiv_integrable : Integrable (fderiv ℝ rho) volume :=
  (rho_contDiff.continuous_fderiv (by simp)).integrable_of_hasCompactSupport
    (rho_hasCompactSupport.fderiv ℝ)

lemma kernel_fderiv_integrable {ε : ℝ} (hε : 0 < ε) :
    Integrable (fderiv ℝ (kernel ε)) volume :=
  ((kernel_contDiff ε).continuous_fderiv (by simp)).integrable_of_hasCompactSupport
    ((kernel_hasCompactSupport hε).fderiv ℝ)

def derivativeMass : ℝ := ∫ x : ℂ, ‖fderiv ℝ rho x‖

lemma derivativeMass_nonneg : 0 ≤ derivativeMass := integral_nonneg (fun _ => norm_nonneg _)

lemma kernel_derivative_mass {ε : ℝ} (hε : 0 < ε) :
    (∫ x : ℂ, ‖fderiv ℝ (kernel ε) x‖) = derivativeMass / ε := by
  simp_rw [kernel_fderiv, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos hε 3))]
  rw [integral_const_mul, Measure.integral_comp_smul volume (fun x : ℂ => ‖fderiv ℝ rho x‖) ε⁻¹,
    Complex.finrank_real_complex, inv_pow, inv_inv, abs_of_nonneg (sq_nonneg ε), smul_eq_mul]
  change (ε ^ 3)⁻¹ * (ε ^ 2 * derivativeMass) = derivativeMass / ε
  field_simp

lemma kernel_derivative_lintegral {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ x : ℂ, ENNReal.ofReal ‖fderiv ℝ (kernel ε) x‖ =
      ENNReal.ofReal (derivativeMass / ε) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (kernel_fderiv_integrable hε).norm
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _)), kernel_derivative_mass hε]

end TriangularBilliards.SpatialSmoothing

end
end

end OAI
end
end

section
section
namespace OAI

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section

namespace TriangularBilliards
open SpatialSmoothing

abbrev SmoothPhase := Phase × ZMod 2

/-- The direct Euclidean convolution term on one copy of the table. -/
def directS (Q : Triangle) (ε : ℝ) (f : SmoothPhase → ℂ)
    (b : ZMod 2) (v : Circle) (x : ℂ) : ℂ :=
  ∫ y in Q.table, kernel ε (x - y) • f ((y, v), b)

/-- The opposite-copy contribution after unfolding through wall `i`. -/
def reflectedS (Q : Triangle) (i : Fin 3) (ε : ℝ) (f : SmoothPhase → ℂ)
    (b : ZMod 2) (v : Circle) (x : ℂ) : ℂ :=
  ∫ y in Q.table, kernel ε (x - wallReflection Q i y) •
    f ((y, reflectedDirection Q i v), b + 1)

/-- A bounded global extension of the local disk mollifier. Away from
vertices, at most one reflected term can contribute. This fact is proved
geometrically instead of assuming a chart or an injectivity-radius bound. -/
def reflectedSmoothing (Q : Triangle) (ε : ℝ) (f : SmoothPhase → ℂ) : SmoothPhase → ℂ :=
  fun z => directS Q ε f z.2 z.1.2 z.1.1 +
    ∑ i : Fin 3, reflectedS Q i ε f z.2 z.1.2 z.1.1

lemma reflectedDirection_involutive (Q : Triangle) (i : Fin 3) (v : Circle) :
    reflectedDirection Q i (reflectedDirection Q i v) = v := by
  apply Subtype.ext
  exact reflect_involutive (Q.tangent_ne_zero i) v

lemma wallReflection_isometry (Q : Triangle) (i : Fin 3) : Isometry (wallReflection Q i) := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  rw [dist_eq_norm, wallReflection_sub, reflect_norm (Q.tangent_ne_zero i), dist_eq_norm]

lemma kernel_wall_pair (Q : Triangle) (i : Fin 3) (ε : ℝ) (x y : ℂ) :
    kernel ε (wallReflection Q i x - wallReflection Q i y) = kernel ε (x - y) := by
  rw [wallReflection_sub]
  exact kernel_radial ε (reflect_norm (Q.tangent_ne_zero i) _)

lemma kernel_wall_transfer (Q : Triangle) (i : Fin 3) (ε : ℝ) (x y : ℂ) :
    kernel ε (wallReflection Q i x - y) = kernel ε (x - wallReflection Q i y) := by
  have h := kernel_wall_pair Q i ε x (wallReflection Q i y)
  rwa [wallReflection_involutive] at h

lemma seamS_equivariant (Q : Triangle) (i : Fin 3) (ε : ℝ) (f : SmoothPhase → ℂ)
    (b : ZMod 2) (v : Circle) (x : ℂ) :
    directS Q ε f (b + 1) (reflectedDirection Q i v) (wallReflection Q i x) +
      reflectedS Q i ε f (b + 1) (reflectedDirection Q i v) (wallReflection Q i x) =
    directS Q ε f b v x + reflectedS Q i ε f b v x := by
  simp only [directS, reflectedS, kernel_wall_transfer, wallReflection_involutive,
    reflectedDirection_involutive]
  have hb : (b + 1) + 1 = b := by
    rw [add_assoc, show (1 : ZMod 2) + 1 = 0 by decide, add_zero]
  rw [hb, add_comm]

namespace Triangle

def coordCLM (Q : Triangle) (i : Fin 3) : ℂ →L[ℝ] ℝ :=
  (Q.basis.coord i).linear.toContinuousLinearMap

lemma coord_sub (Q : Triangle) (i : Fin 3) (x y : ℂ) :
    Q.basis.coord i x - Q.basis.coord i y = Q.coordCLM i (x - y) := by
  exact ((Q.basis.coord i).linearMap_vsub x y).symm

def coordinateBound (Q : Triangle) : ℝ := ∑ i, ‖Q.coordCLM i‖

lemma coordinateBound_nonneg (Q : Triangle) : 0 ≤ Q.coordinateBound :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

lemma coord_norm_le (Q : Triangle) (i : Fin 3) (x y : ℂ) :
    |Q.basis.coord i x - Q.basis.coord i y| ≤ Q.coordinateBound * ‖x - y‖ := by
  rw [Q.coord_sub, ← Real.norm_eq_abs]
  apply (Q.coordCLM i).le_opNorm _ |>.trans
  gcongr
  exact Finset.single_le_sum (fun j _ => norm_nonneg (Q.coordCLM j)) (Finset.mem_univ i)

lemma coord_wallReflection (Q : Triangle) (i : Fin 3) (x : ℂ) :
    Q.basis.coord (i + 2) (wallReflection Q i x) = -Q.basis.coord (i + 2) x := by
  have hv : Q.basis.coord (i + 2) (Q.vertex i) = 0 := by
    exact Q.basis.coord_apply (i + 2) i |>.trans (ite_eq_right (by decide +revert))
  have h₁ := Q.coord_shift (i + 2) (Q.vertex i) (reflect (Q.tangent i) (x - Q.vertex i)) 1
  have h₂ := Q.coord_shift (i + 2) (Q.vertex i) (x - Q.vertex i) 1
  rw [one_smul, hv, one_mul, Q.slope_reflect] at h₁
  rw [one_smul, add_sub_cancel, hv, one_mul, zero_add] at h₂
  change Q.basis.coord (i + 2) (Q.vertex i + reflect (Q.tangent i) (x - Q.vertex i)) = _
  linarith

lemma coord_small_of_reflected_near (Q : Triangle) (i : Fin 3) {x y : ℂ} {ε : ℝ}
    (hy : y ∈ Q.table) (hxy : ‖x - wallReflection Q i y‖ ≤ ε) :
    Q.basis.coord (i + 2) x ≤ Q.coordinateBound * ε := by
  have h := Q.coord_norm_le (i + 2) x (wallReflection Q i y)
  rw [Q.coord_wallReflection] at h
  have hp := ((Q.table_iff_coords y).mp hy (i + 2)).le
  have ha := le_abs_self (Q.basis.coord (i + 2) x - -Q.basis.coord (i + 2) y)
  have hm := mul_le_mul_of_nonneg_left hxy Q.coordinateBound_nonneg
  linarith

end Triangle

lemma norm_decompose_sq (e : ℂ) (a b : ℝ) :
    ‖a • e + b • (Complex.I * e)‖ ^ 2 = (a ^ 2 + b ^ 2) * ‖e‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

lemma reflect_distance_le {e : ℂ} (he : e ≠ 0) (l : ℂ →ₗ[ℝ] ℝ)
    (hl : l e = 0) (hlI : l (Complex.I * e) ≠ 0) {x y : ℂ}
    (hxy : 0 ≤ l x * l y) : ‖x - y‖ ≤ ‖x - reflect e y‖ := by
  obtain ⟨a, b, rfl⟩ := complex_decompose_tangent he x
  obtain ⟨c, d, rfl⟩ := complex_decompose_tangent he y
  simp only [map_add, map_smul, smul_eq_mul, hl, mul_zero, zero_add] at hxy
  have hbd : 0 ≤ b * d := by
    nlinarith [sq_pos_of_ne_zero hlI]
  rw [reflect_add, reflect_real_smul, reflect_real_smul, reflect_tangent he, reflect_normal he]
  have hsub : a • e + b • (Complex.I * e) - (c • e + d • (Complex.I * e)) =
      (a - c) • e + (b - d) • (Complex.I * e) := by module
  have href : a • e + b • (Complex.I * e) - (c • e + d • -(Complex.I * e)) =
      (a - c) • e + (b + d) • (Complex.I * e) := by module
  rw [hsub, href]
  have hpos : 0 ≤ ‖e‖ ^ 2 := sq_nonneg ‖e‖
  have hn₁ := norm_decompose_sq e (a - c) (b - d)
  have hn₂ := norm_decompose_sq e (a - c) (b + d)
  nlinarith [norm_nonneg ((a - c) • e + (b - d) • (Complex.I * e)),
    norm_nonneg ((a - c) • e + (b + d) • (Complex.I * e)), mul_nonneg hbd hpos]

namespace Triangle

lemma slope_normal_ne_zero (Q : Triangle) (i : Fin 3) :
    Q.slope (i + 2) (Complex.I * Q.tangent i) ≠ 0 := by
  intro hz
  have hall (v : ℂ) : Q.slope (i + 2) v = 0 := by
    obtain ⟨a, b, rfl⟩ := complex_decompose_tangent (Q.tangent_ne_zero i) v
    change (Q.basis.coord (i + 2)).linear _ = 0
    rw [map_add, map_smul, map_smul]
    change a * Q.slope (i + 2) (Q.tangent i) +
      b * Q.slope (i + 2) (Complex.I * Q.tangent i) = 0
    rw [Q.slope_tangent_zero, hz, mul_zero, mul_zero, add_zero]
  have h := Q.coord_sub (i + 2) (Q.vertex (i + 2)) (Q.vertex i)
  change Q.basis.coord (i + 2) (Q.basis (i + 2)) -
    Q.basis.coord (i + 2) (Q.basis i) = Q.slope (i + 2) _ at h
  simp only [Q.basis.coord_apply, ite_eq_right (show i + 2 ≠ i by fin_cases i <;> decide),
    hall, sub_zero] at h
  exact one_ne_zero h

/-- Reflection through a supporting line can only increase the distance
between two points in the closed table. This also controls tip clearance
without any injectivity-radius assumption. -/
lemma dist_le_reflected_dist (Q : Triangle) (i : Fin 3) {x y : ℂ}
    (hx : x ∈ Q.table) (hy : y ∈ Q.table) :
    ‖x - y‖ ≤ ‖x - wallReflection Q i y‖ := by
  have hv : Q.basis.coord (i + 2) (Q.vertex i) = 0 :=
    Q.basis.coord_apply (i + 2) i |>.trans (ite_eq_right (by decide +revert))
  have he (z : ℂ) : (Q.basis.coord (i + 2)).linear (z - Q.vertex i) =
      Q.basis.coord (i + 2) z := by
    have h := Q.coord_sub (i + 2) z (Q.vertex i)
    rw [hv, sub_zero] at h
    exact h.symm
  have h := reflect_distance_le (Q.tangent_ne_zero i)
    (Q.basis.coord (i + 2)).linear (Q.slope_tangent_zero i) (Q.slope_normal_ne_zero i)
    (x := x - Q.vertex i) (y := y - Q.vertex i) (by
      rw [he, he]
      exact mul_nonneg ((Q.table_iff_coords x).mp hx _).le ((Q.table_iff_coords y).mp hy _).le)
  rw [sub_sub_sub_cancel_right] at h
  have hr : x - Q.vertex i - reflect (Q.tangent i) (y - Q.vertex i) =
      x - wallReflection Q i y := by unfold wallReflection; abel
  rwa [hr] at h

/-- Exact distance to the three cone tips. -/
def clearance (Q : Triangle) (x : ℂ) : ℝ := Metric.infDist x (range Q.vertex)

lemma clearance_nonneg (Q : Triangle) (x : ℂ) : 0 ≤ Q.clearance x :=
  Metric.infDist_nonneg

lemma clearance_lipschitz (Q : Triangle) : LipschitzWith 1 Q.clearance :=
  Metric.lipschitz_infDist_pt (range Q.vertex)

lemma clearance_le_add (Q : Triangle) (x y : ℂ) :
    Q.clearance y ≤ Q.clearance x + ‖x - y‖ := by
  have h := Q.clearance_lipschitz.dist_le_mul y x
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, Real.norm_eq_abs] at h
  rw [norm_sub_rev y x] at h
  have hs := le_abs_self (Q.clearance y - Q.clearance x)
  linarith

end Triangle

def SpatiallyZero (Q : Triangle) (R : ℝ) (f : SmoothPhase → ℂ) : Prop :=
  ∀ y ∈ Q.table, Q.clearance y < R → ∀ v b, f ((y, v), b) = 0

lemma directS_zero_near_tips (Q : Triangle) {ε R : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : SpatiallyZero Q R f) (b : ZMod 2) (v : Circle)
    {x : ℂ} (hx : Q.clearance x + ε ≤ R) : directS Q ε f b v x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem Q.measurableSet_table] with y hy
  by_cases hk : kernel ε (x - y) = 0
  · simp only [hk, zero_smul, Pi.zero_apply]
  · have hd : ‖x - y‖ < ε := by
      have hmem : x - y ∈ support (kernel ε) := hk
      rwa [kernel_support hε, mem_ball_zero_iff] at hmem
    have hr := Q.clearance_le_add x y
    have he := hf y hy (by linarith) v b
    simp only [he, smul_zero, Pi.zero_apply]

lemma reflectedS_zero_near_tips (Q : Triangle) (i : Fin 3) {ε R : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : SpatiallyZero Q R f) (b : ZMod 2) (v : Circle)
    {x : ℂ} (hx : x ∈ Q.table) (hr : Q.clearance x + ε ≤ R) :
    reflectedS Q i ε f b v x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem Q.measurableSet_table] with y hy
  by_cases hk : kernel ε (x - wallReflection Q i y) = 0
  · simp only [hk, zero_smul, Pi.zero_apply]
  · have hd : ‖x - wallReflection Q i y‖ < ε := by
      have hmem : x - wallReflection Q i y ∈ support (kernel ε) := hk
      rwa [kernel_support hε, mem_ball_zero_iff] at hmem
    have hg := Q.dist_le_reflected_dist i hx hy
    have hr' := Q.clearance_le_add x y
    have he := hf y hy (by linarith) (reflectedDirection Q i v) (b + 1)
    simp only [he, smul_zero, Pi.zero_apply]

lemma reflectedSmoothing_zero_near_tips (Q : Triangle) {ε R : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : SpatiallyZero Q R f) {z : SmoothPhase}
    (hx : z.1.1 ∈ Q.table) (hr : Q.clearance z.1.1 + ε ≤ R) :
    reflectedSmoothing Q ε f z = 0 := by
  rw [reflectedSmoothing, directS_zero_near_tips Q hε hf _ _ hr]
  simp only [reflectedS_zero_near_tips Q _ hε hf _ _ hx hr, Finset.sum_const_zero, add_zero]

namespace Triangle

def diameterBound (Q : Triangle) : ℝ := ∑ i : Fin 3, ∑ j : Fin 3, ‖Q.vertex i - Q.vertex j‖

lemma diameterBound_nonneg (Q : Triangle) : 0 ≤ Q.diameterBound :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))

lemma vertex_dist_le_diameterBound (Q : Triangle) (i j : Fin 3) :
    ‖Q.vertex i - Q.vertex j‖ ≤ Q.diameterBound := by
  apply (Finset.single_le_sum (fun k _ => norm_nonneg (Q.vertex i - Q.vertex k))
    (Finset.mem_univ j)).trans
  exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg
    (fun l _ => norm_nonneg (Q.vertex k - Q.vertex l))) (Finset.mem_univ i)

lemma reconstruct_difference (Q : Triangle) (x : ℂ) (k : Fin 3) :
    x - Q.vertex k = ∑ j : Fin 3, Q.basis.coord j x • (Q.vertex j - Q.vertex k) := by
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
    Q.basis.sum_coord_apply_eq_one, one_smul]
  have h := Q.basis.linear_combination_coord_eq_self x
  change ∑ i, Q.basis.coord i x • Q.vertex i = x at h
  rw [h]

lemma clearance_of_coords_small_nonneg (Q : Triangle) {x : ℂ}
    (hx : ∀ j, 0 ≤ Q.basis.coord j x)
    (k : Fin 3) {δ : ℝ} (hδ : 0 ≤ δ)
    (hc : ∀ i, i ≠ k → Q.basis.coord i x ≤ δ) :
    Q.clearance x ≤ 3 * Q.diameterBound * δ := by
  calc
    Q.clearance x ≤ dist x (Q.vertex k) :=
      Metric.infDist_le_dist_of_mem (mem_range_self k)
    _ = ‖∑ j : Fin 3, Q.basis.coord j x • (Q.vertex j - Q.vertex k)‖ := by
      rw [dist_eq_norm, Q.reconstruct_difference]
    _ ≤ ∑ j : Fin 3, ‖Q.basis.coord j x • (Q.vertex j - Q.vertex k)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, δ * Q.diameterBound := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j = k
      · simp only [hj, sub_self, smul_zero, norm_zero]
        exact mul_nonneg hδ Q.diameterBound_nonneg
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hx j)]
        exact mul_le_mul (hc j hj) (Q.vertex_dist_le_diameterBound j k)
          (norm_nonneg _) hδ
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma clearance_of_coords_small (Q : Triangle) {x : ℂ} (hx : x ∈ Q.table)
    (k : Fin 3) {δ : ℝ} (hδ : 0 ≤ δ)
    (hc : ∀ i, i ≠ k → Q.basis.coord i x ≤ δ) :
    Q.clearance x ≤ 3 * Q.diameterBound * δ :=
  Q.clearance_of_coords_small_nonneg (fun j => ((Q.table_iff_coords x).mp hx j).le) k hδ hc

/-- A concrete fixed safety factor depending only on the triangle. -/
def safetyFactor (Q : Triangle) : ℝ := 3 * Q.diameterBound * Q.coordinateBound + 1

lemma safetyFactor_pos (Q : Triangle) : 0 < Q.safetyFactor := by
  unfold safetyFactor
  have h := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) Q.diameterBound_nonneg)
    Q.coordinateBound_nonneg
  linarith

lemma unique_nearby_wall (Q : Triangle) {x : ℂ} (hx : x ∈ Q.table) {ε : ℝ} (hε : 0 < ε)
    (hsafe : Q.safetyFactor * ε < Q.clearance x) {i j : Fin 3}
    (hi : ∃ y ∈ Q.table, ‖x - wallReflection Q i y‖ ≤ ε)
    (hj : ∃ y ∈ Q.table, ‖x - wallReflection Q j y‖ ≤ ε) : i = j := by
  by_contra hij
  obtain ⟨y, hy, hxy⟩ := hi
  obtain ⟨z, hz, hxz⟩ := hj
  have hci := Q.coord_small_of_reflected_near i hy hxy
  have hcj := Q.coord_small_of_reflected_near j hz hxz
  let k : Fin 3 := -((i + 2) + (j + 2))
  have hfin : ∀ i j l : Fin 3, i ≠ j →
      l ≠ -((i + 2) + (j + 2)) → l = i + 2 ∨ l = j + 2 := by decide
  have hcover (l : Fin 3) (hl : l ≠ k) : l = i + 2 ∨ l = j + 2 :=
    hfin i j l hij hl
  have hh := Q.clearance_of_coords_small hx k
    (mul_nonneg Q.coordinateBound_nonneg hε.le) (fun l hl => by
      rcases hcover l hl with h | h
      · rwa [h]
      · rwa [h])
  unfold safetyFactor at hsafe
  nlinarith

end Triangle

/-- Zero extension of a spatial slice; no value at a seam is used. -/
def spatialSlice (Q : Triangle) (f : SmoothPhase → ℂ) (b : ZMod 2) (v : Circle) : ℂ → ℂ :=
  Q.table.indicator (fun y => f ((y, v), b))

def scalarKernelMap : ℂ →L[ℝ] ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.lsmul ℝ ℝ).flip

lemma directS_eq_convolution (Q : Triangle) (ε : ℝ) (f : SmoothPhase → ℂ)
    (b : ZMod 2) (v : Circle) :
    directS Q ε f b v = convolution (spatialSlice Q f b v) (kernel ε)
      scalarKernelMap volume := by
  funext x
  rw [convolution_def]
  change (∫ y in Q.table, kernel ε (x - y) • f ((y, v), b)) =
    ∫ y, kernel ε (x - y) • Q.table.indicator (fun z => f ((z, v), b)) y
  rw [← integral_indicator Q.measurableSet_table]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    by_cases hy : y ∈ Q.table <;> simp [indicator_of_mem, indicator_of_notMem, hy]

lemma directS_contDiff (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} {b : ZMod 2} {v : Circle}
    (hf : IntegrableOn (fun y => f ((y, v), b)) Q.table) :
    ContDiff ℝ ∞ (directS Q ε f b v) := by
  rw [directS_eq_convolution]
  apply (kernel_hasCompactSupport hε).contDiff_convolution_right scalarKernelMap
  · exact ((integrable_indicator_iff Q.measurableSet_table).mpr hf).locallyIntegrable
  · exact kernel_contDiff ε

lemma reflectedS_eq_directS (Q : Triangle) (i : Fin 3) (ε : ℝ)
    (f : SmoothPhase → ℂ) (b : ZMod 2) (v : Circle) :
    reflectedS Q i ε f b v =
      directS Q ε f (b + 1) (reflectedDirection Q i v) ∘ wallReflection Q i := by
  funext x
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by simp only [kernel_wall_transfer]

lemma wallReflection_contDiff (Q : Triangle) (i : Fin 3) :
    ContDiff ℝ ∞ (wallReflection Q i) := by
  change ContDiff ℝ ∞ (fun x => Q.vertex i +
    reflectIsometry (Q.tangent i) (Q.tangent_ne_zero i) (x - Q.vertex i))
  exact contDiff_const.add ((reflectIsometry (Q.tangent i) (Q.tangent_ne_zero i)).contDiff.comp
    (contDiff_id.sub contDiff_const))

lemma reflectedS_contDiff (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} {b : ZMod 2} {v : Circle}
    (hf : IntegrableOn (fun y => f ((y, reflectedDirection Q i v), b + 1)) Q.table) :
    ContDiff ℝ ∞ (reflectedS Q i ε f b v) := by
  rw [reflectedS_eq_directS]
  exact (directS_contDiff Q hε hf).comp (wallReflection_contDiff Q i)

/-- The genuine kernel construction is spatially smooth on every integrable
angular slice. No angular regularization, differentiability or boundedness of
`f` is required. -/
lemma reflectedSmoothing_contDiff (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} {b : ZMod 2} {v : Circle}
    (hf : IntegrableOn (fun y => f ((y, v), b)) Q.table)
    (hfr : ∀ i, IntegrableOn
      (fun y => f ((y, reflectedDirection Q i v), b + 1)) Q.table) :
    ContDiff ℝ ∞ (fun x => reflectedSmoothing Q ε f ((x, v), b)) := by
  exact (directS_contDiff Q hε hf).add
    (ContDiff.sum fun i _ => reflectedS_contDiff Q i hε (hfr i))

lemma reflectedS_zero_of_coord (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    (f : SmoothPhase → ℂ) (b : ZMod 2) (v : Circle) {x : ℂ}
    (hx : Q.coordinateBound * ε < Q.basis.coord (i + 2) x) :
    reflectedS Q i ε f b v x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem Q.measurableSet_table] with y hy
  have hz : kernel ε (x - wallReflection Q i y) = 0 := by
    by_contra hn
    have hd : ‖x - wallReflection Q i y‖ < ε := by
      have hm : x - wallReflection Q i y ∈ support (kernel ε) := hn
      rwa [kernel_support hε, mem_ball_zero_iff] at hm
    exact (not_le_of_gt hx) (Q.coord_small_of_reflected_near i hy hd.le)
  simp only [hz, zero_smul, Pi.zero_apply]

lemma side_other_coord_large (Q : Triangle) {i j : Fin 3} {x : ℂ}
    (hx : x ∈ Q.side i) (hji : j ≠ i) {ε : ℝ} (hε : 0 < ε)
    (hsafe : Q.safetyFactor * ε < Q.clearance x) :
    Q.coordinateBound * ε < Q.basis.coord (j + 2) x := by
  by_contra hn
  have hj := le_of_not_gt hn
  have hi : Q.basis.coord (i + 2) x = 0 := (Q.side_coord_zero_iff hx _).mpr rfl
  let k : Fin 3 := -((i + 2) + (j + 2))
  have hfin : ∀ i j l : Fin 3, i ≠ j →
      l ≠ -((i + 2) + (j + 2)) → l = i + 2 ∨ l = j + 2 := by decide
  have hp := mul_nonneg Q.coordinateBound_nonneg hε.le
  have hb := Q.clearance_of_coords_small_nonneg (Q.side_coords_nonneg hx) k hp (fun l hl => by
    rcases hfin i j l hji.symm hl with he | he
    · rw [he, hi]; exact hp
    · rwa [he])
  unfold Triangle.safetyFactor at hsafe
  nlinarith

/-- Near every safe open seam, the full finite kernel is exactly its
single unfolded two-sheet chart kernel. The assertion holds on a genuine
open neighborhood, so all spatial derivatives also glue. -/
lemma reflectedSmoothing_seam_germ (Q : Triangle) {i : Fin 3} {q : ℂ}
    (hq : q ∈ Q.side i) {ε : ℝ} (hε : 0 < ε)
    (hsafe : Q.safetyFactor * ε < Q.clearance q)
    (f : SmoothPhase → ℂ) (b : ZMod 2) (v : Circle) :
    ∀ᶠ x in nhds q,
      reflectedSmoothing Q ε f ((wallReflection Q i x, reflectedDirection Q i v), b + 1) =
        reflectedSmoothing Q ε f ((x, v), b) := by
  have hc (j : Fin 3) : Continuous (fun x => Q.basis.coord (j + 2) x) :=
    (Q.basis.coord (j + 2)).continuous_of_finiteDimensional
  have he (j : Fin 3) : ∀ᶠ x in nhds q, j ≠ i →
      Q.coordinateBound * ε < Q.basis.coord (j + 2) x ∧
      Q.coordinateBound * ε < Q.basis.coord (j + 2) (wallReflection Q i x) := by
    by_cases hj : j = i
    · exact Filter.Eventually.of_forall fun _ h => (h hj).elim
    · have hh := side_other_coord_large Q hq hj hε hsafe
      have h₁ := (hc j).continuousAt.eventually (Ioi_mem_nhds hh)
      have hh' : Q.coordinateBound * ε < Q.basis.coord (j + 2) (wallReflection Q i q) := by
        rwa [wallReflection_fixed_side Q hq]
      have h₂ := ((hc j).comp (wallReflection_contDiff Q i).continuous).continuousAt
        (x := q) |>.eventually (Ioi_mem_nhds hh')
      filter_upwards [h₁, h₂] with x h₁ h₂ using fun _ => ⟨h₁, h₂⟩
  have hall := (Filter.eventually_all.mpr he)
  filter_upwards [hall] with x hx
  have hsum (b : ZMod 2) (v : Circle) {y : ℂ}
      (hy : ∀ j, j ≠ i → Q.coordinateBound * ε < Q.basis.coord (j + 2) y) :
      (∑ j : Fin 3, reflectedS Q j ε f b v y) = reflectedS Q i ε f b v y := by
    apply Finset.sum_eq_single i
    · intro j _ hj
      exact reflectedS_zero_of_coord Q j hε f b v (hy j hj)
    · simp
  simp only [reflectedSmoothing, hsum b v (fun j hj => (hx j hj).1),
    hsum (b + 1) (reflectedDirection Q i v) (fun j hj => (hx j hj).2)]
  exact seamS_equivariant Q i ε f b v x

lemma directS_fderiv (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} {b : ZMod 2} {v : Circle}
    (hf : IntegrableOn (fun y => f ((y, v), b)) Q.table) (x : ℂ) :
    fderiv ℝ (directS Q ε f b v) x =
      ∫ y in Q.table, (fderiv ℝ (kernel ε) (x - y)).smulRight (f ((y, v), b)) := by
  rw [directS_eq_convolution]
  have hi : LocallyIntegrable (spatialSlice Q f b v) volume :=
    ((integrable_indicator_iff Q.measurableSet_table).mpr hf).locallyIntegrable
  rw [((kernel_hasCompactSupport hε).hasFDerivAt_convolution_right scalarKernelMap hi
    ((kernel_contDiff ε).of_le (by simp)) x).fderiv, convolution_def]
  rw [← integral_indicator Q.measurableSet_table]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    by_cases hy : y ∈ Q.table
    · simp only [spatialSlice, indicator_of_mem hy]
      rfl
    · simp only [spatialSlice, indicator_of_notMem hy, map_zero, zero_apply]

lemma kernel_lintegral {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ x : ℂ, ENNReal.ofReal (kernel ε x) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (kernel_integrable hε)
    (Filter.Eventually.of_forall (kernel_nonneg ε)), kernel_integral hε, ENNReal.ofReal_one]

lemma kernel_row_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    ∫⁻ y in Q.table, ENNReal.ofReal (kernel ε (x - y)) ≤ 1 := by
  calc
    _ ≤ ∫⁻ y : ℂ, ENNReal.ofReal (kernel ε (x - y)) :=
      lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
    _ = 1 := (lintegral_sub_left_eq_self (fun y : ℂ => ENNReal.ofReal (kernel ε y)) x).trans
      (kernel_lintegral hε)

lemma kernel_col_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε) (y : ℂ) :
    ∫⁻ x in Q.table, ENNReal.ofReal (kernel ε (x - y)) ≤ 1 := by
  calc
    _ ≤ ∫⁻ x : ℂ, ENNReal.ofReal (kernel ε (x - y)) :=
      lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
    _ = 1 := (lintegral_sub_right_eq_self (fun x : ℂ => ENNReal.ofReal (kernel ε x)) y).trans
      (kernel_lintegral hε)

lemma reflected_kernel_row_bound (Q : Triangle) (i : Fin 3)
    {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    ∫⁻ y in Q.table, ENNReal.ofReal (kernel ε (x - wallReflection Q i y)) ≤ 1 := by
  simp_rw [← kernel_wall_transfer]
  exact kernel_row_bound Q hε _

lemma reflected_kernel_col_bound (Q : Triangle) (i : Fin 3)
    {ε : ℝ} (hε : 0 < ε) (y : ℂ) :
    ∫⁻ x in Q.table, ENNReal.ofReal (kernel ε (x - wallReflection Q i y)) ≤ 1 :=
  kernel_col_bound Q hε _

end TriangularBilliards

end
end

end OAI
end
end

section
section
namespace OAI

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section

/-! The actual oriented double of the billiard, in its full-measure pair of
interior charts. The second coordinate records the parity of reflections;
it is not an independent randomization of the dynamics. -/
namespace TriangularBilliards

open Function Filter
open scoped Topology

abbrev DoublePhase := Phase × ZMod 2

def parityMeasure : Measure (ZMod 2) := (2 : ℝ≥0∞)⁻¹ • Measure.count

instance parityMeasure_probability : IsProbabilityMeasure parityMeasure := by
  constructor
  simp only [parityMeasure, Measure.smul_apply, smul_eq_mul, Measure.count_univ, ENat.card_eq_coe_fintype_card, ZMod.card, ENat.toENNReal_coe]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

def doubleMeasure (Q : Triangle) : Measure DoublePhase := (phaseMeasure Q).prod parityMeasure

instance doubleMeasure_probability (Q : Triangle) : IsProbabilityMeasure (doubleMeasure Q) := by
  unfold doubleMeasure
  infer_instance

lemma measurePreserving_parity_add (a : ZMod 2) :
    MeasurePreserving (fun b => a + b) parityMeasure parityMeasure := by
  have h : MeasurePreserving (fun b : ZMod 2 => a + b) Measure.count Measure.count := by
    refine ⟨measurable_of_countable _, Measure.eq_of_le_of_measure_univ_eq ?_ ?_⟩
    · exact (add_right_injective a).map_count_le (measurable_of_countable _)
    · rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ, preimage_univ]
  exact h.smul_measure _

def collisionIndex (Q : Triangle) (t : ℝ) (z : Phase) : ℤ := by
  classical
  exact if Nonempty (FlightChain Q z) then CodedChain.index (CodedChain.fromPhase Q z, t) else 0

lemma collisionIndex_spec {Q : Triangle} {z : Phase} (c : FlightChain Q z) (t : ℝ) :
    c.time (collisionIndex Q t z) ≤ t ∧ t < c.time (collisionIndex Q t z + 1) := by
  classical
  let d : CodedChain Q := ⟨(z, c.data), c.data_valid⟩
  have he : CodedChain.fromPhase Q z = d := CodedChain.fromPhase_initial Q d
  have hc : d.chain = c := FlightChain.unique _ _
  simp only [collisionIndex, ite_eq_left (show Nonempty (FlightChain Q z) from ⟨c⟩), he]
  simpa only [hc] using CodedChain.index_spec (d, t)

lemma collisionIndex_eq {Q : Triangle} {z : Phase} (c : FlightChain Q z) {t : ℝ} {n : ℤ}
    (hn : c.time n ≤ t ∧ t < c.time (n + 1)) : collisionIndex Q t z = n :=
  c.flight_index_unique (collisionIndex_spec c t) hn

@[fun_prop] lemma measurable_collisionIndex (Q : Triangle) :
    Measurable (fun a : ℝ × Phase => collisionIndex Q a.1 a.2) := by
  classical
  apply Measurable.ite
  · exact (CodedChain.measurableSet_regular Q).preimage measurable_snd
  · exact (CodedChain.measurable_index Q).comp
      (((CodedChain.measurable_fromPhase Q).comp measurable_snd).prodMk measurable_fst)
  · exact measurable_const

lemma collisionIndex_zero (Q : Triangle) (z : Phase) : collisionIndex Q 0 z = 0 := by
  classical
  by_cases h : Nonempty (FlightChain Q z)
  · exact collisionIndex_eq h.some ⟨h.some.zero_before.le, h.some.zero_after⟩
  · simp [collisionIndex, h]

/-- Unit-speed geodesic flow of the oriented double in the two interior charts. -/
def doubleFlow (Q : Triangle) (t : ℝ) (z : DoublePhase) : DoublePhase :=
  (billiardFlow Q t z.1, (collisionIndex Q t z.1 : ZMod 2) + z.2)

@[fun_prop] lemma measurable_doubleFlow (Q : Triangle) :
    Measurable (fun a : ℝ × DoublePhase => doubleFlow Q a.1 a.2) := by
  have hi : Measurable (fun a : ℝ × DoublePhase => (collisionIndex Q a.1 a.2.1 : ZMod 2)) :=
    (measurable_of_countable (fun n : ℤ => (n : ZMod 2))).comp
      ((measurable_collisionIndex Q).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
  exact ((measurable_billiardFlow Q).comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
    (hi.add (measurable_snd.comp measurable_snd))

@[fun_prop] lemma measurable_doubleFlow_time (Q : Triangle) (t : ℝ) :
    Measurable (doubleFlow Q t) :=
  (measurable_doubleFlow Q).comp (measurable_const.prodMk measurable_id)

lemma measurePreserving_doubleFlow (Q : Triangle) (t : ℝ) :
    MeasurePreserving (doubleFlow Q t) (doubleMeasure Q) (doubleMeasure Q) := by
  apply (measurePreserving_billiardFlow Q t).skew_product
    (g := fun z b => (collisionIndex Q t z : ZMod 2) + b)
  · exact measurable_snd.comp (measurable_doubleFlow_time Q t)
  · exact Eventually.of_forall fun z => (measurePreserving_parity_add _).map_eq

lemma doubleFlow_zero (Q : Triangle) (z : DoublePhase) : doubleFlow Q 0 z = z := by
  simp [doubleFlow, billiardFlow_zero, collisionIndex_zero]

lemma collisionIndex_rebase {Q : Triangle} {z : Phase} (c : FlightChain Q z)
    (t s : ℝ) (hn : c.time (collisionIndex Q t z) < t) :
    collisionIndex Q s (billiardFlow Q t z) + collisionIndex Q t z =
      collisionIndex Q (s + t) z := by
  let n := collisionIndex Q t z
  let m := collisionIndex Q (s + t) z
  have hn' := (collisionIndex_spec c t).2
  let d := c.rebase t n ⟨hn, hn'⟩
  have hm := collisionIndex_spec c (s + t)
  have hd : d.time (m - n) ≤ s ∧ s < d.time (m - n + 1) := by
    change c.time (m - n + n) - t ≤ s ∧ s < c.time (m - n + 1 + n) - t
    rw [sub_add_cancel, show m - n + 1 + n = m + 1 by omega]
    constructor <;> linarith [hm.1, hm.2]
  rw [billiardFlow_eq_chain c t, collisionIndex_eq d hd]
  exact sub_add_cancel _ _

lemma doubleFlow_add_of_noncollision {Q : Triangle} {z : DoublePhase}
    (c : FlightChain Q z.1) (s t : ℝ) (ht : t ∉ range c.time) :
    doubleFlow Q (s + t) z = doubleFlow Q s (doubleFlow Q t z) := by
  have hn : c.time (collisionIndex Q t z.1) < t := lt_of_le_of_ne
    (collisionIndex_spec c t).1 (fun h => ht ⟨_, h⟩)
  apply Prod.ext
  · exact billiardFlow_add_of_noncollision c s t ht
  · change (_ : ZMod 2) + z.2 = _ + (_ + z.2)
    change (collisionIndex Q (s + t) z.1 : ZMod 2) + z.2 =
      (collisionIndex Q s (billiardFlow Q t z.1) : ZMod 2) + ((collisionIndex Q t z.1 : ZMod 2) + z.2)
    rw [← add_assoc, ← Int.cast_add, collisionIndex_rebase c t s hn]

lemma doubleFlow_cocycle (Q : Triangle) (s t : ℝ) :
    doubleFlow Q (s + t) =ᵐ[doubleMeasure Q] (doubleFlow Q s ∘ doubleFlow Q t) := by
  have h : ∀ᵐ z ∂doubleMeasure Q, z.1 ∈ regularAt Q t :=
    Measure.quasiMeasurePreserving_fst.ae (ae_regularAt Q t)
  filter_upwards [h] with z hz
  obtain ⟨c⟩ := hz.1
  exact doubleFlow_add_of_noncollision c s t (regularAt_noncollision hz c)

/-- Rotation in the oriented tangent circle; the negative copy has the
opposite physical rotation, exactly as in a conjugate Euclidean chart. -/
def doubleRotate (a : Circle) (z : DoublePhase) : DoublePhase :=
  ((z.1.1, (if z.2 = 0 then a else a⁻¹) * z.1.2), z.2)

@[fun_prop] lemma measurable_doubleRotate (a : Circle) : Measurable (doubleRotate a) := by
  have h : Measurable (fun b : ZMod 2 => if b = 0 then a else a⁻¹) := measurable_of_countable _
  exact (measurable_fst.fst.prodMk ((h.comp measurable_snd).mul measurable_fst.snd)).prodMk measurable_snd

lemma measurePreserving_doubleRotate (Q : Triangle) (a : Circle) :
    MeasurePreserving (doubleRotate a) (doubleMeasure Q) (doubleMeasure Q) := by
  have h : MeasurePreserving
      (fun z : ZMod 2 × Phase => (z.1, (z.2.1, (if z.1 = 0 then a else a⁻¹) * z.2.2)))
      (parityMeasure.prod (phaseMeasure Q)) (parityMeasure.prod (phaseMeasure Q)) := by
    apply (MeasurePreserving.id parityMeasure).skew_product
      (g := fun (b : ZMod 2) (z : Phase) => (z.1, (if b = 0 then a else a⁻¹) * z.2))
    · have hm : Measurable (fun b : ZMod 2 => if b = 0 then a else a⁻¹) := measurable_of_countable _
      exact measurable_snd.fst.prodMk ((hm.comp measurable_fst).mul measurable_snd.snd)
    · exact Eventually.of_forall fun b =>
        ((MeasurePreserving.id ((volume Q.table)⁻¹ • volume.restrict Q.table)).prod
          (measurePreserving_circle_mul (if b = 0 then a else a⁻¹))).map_eq
  exact Measure.measurePreserving_swap.comp (h.comp Measure.measurePreserving_swap)

lemma doubleRotate_one (z : DoublePhase) : doubleRotate 1 z = z := by
  simp [doubleRotate]

lemma doubleRotate_mul (a b : Circle) (z : DoublePhase) :
    doubleRotate (a * b) z = doubleRotate a (doubleRotate b z) := by
  by_cases hz : z.2 = 0 <;> simp [doubleRotate, hz, mul_assoc, mul_comm b⁻¹ a⁻¹]

lemma doubleFlow_on_flight {Q : Triangle} {z : DoublePhase} (c : FlightChain Q z.1)
    {t : ℝ} {n : ℤ} (ht : c.time n ≤ t ∧ t < c.time (n + 1)) :
    doubleFlow Q t z =
      ((c.point n + (t - c.time n) • (c.direction n : ℂ), c.direction n),
        (n : ZMod 2) + z.2) := by
  simp only [doubleFlow, billiardFlow_eq_chain c t, c.at_of_flight ht, collisionIndex_eq c ht]

lemma continuousAt_doubleFlow_of_noncollision {Q : Triangle} {z : DoublePhase}
    (c : FlightChain Q z.1) {t : ℝ} (ht : t ∉ range c.time) :
    ContinuousAt (fun s => doubleFlow Q s z) t := by
  let n := collisionIndex Q t z.1
  have hn : t ∈ Ioo (c.time n) (c.time (n + 1)) :=
    ⟨lt_of_le_of_ne (collisionIndex_spec c t).1 (fun h => ht ⟨_, h⟩),
      (collisionIndex_spec c t).2⟩
  have he : (fun s => doubleFlow Q s z) =ᶠ[𝓝 t]
      (fun s => ((c.point n + (s - c.time n) • (c.direction n : ℂ), c.direction n),
        (n : ZMod 2) + z.2)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hn] with s hs
    exact doubleFlow_on_flight c ⟨hs.1.le, hs.2⟩
  have hc : ContinuousAt
      (fun s : ℝ => ((c.point n + (s - c.time n) • (c.direction n : ℂ), c.direction n),
        (n : ZMod 2) + z.2)) t := by fun_prop
  exact hc.congr_of_eventuallyEq he

lemma ae_continuousAt_doubleFlow (Q : Triangle) (t : ℝ) :
    ∀ᵐ z ∂doubleMeasure Q, ContinuousAt (fun s => doubleFlow Q s z) t := by
  have h : ∀ᵐ z ∂doubleMeasure Q, z.1 ∈ regularAt Q t :=
    Measure.quasiMeasurePreserving_fst.ae (ae_regularAt Q t)
  filter_upwards [h] with z hz
  obtain ⟨c⟩ := hz.1
  exact continuousAt_doubleFlow_of_noncollision c (regularAt_noncollision hz c)

end TriangularBilliards

end
end

end OAI
end
end

section
section
namespace OAI


open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section

/-! The positive-kernel L² bound for chartwise smoothing, including
the integral inequality and Tonelli. -/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace TriangularBilliards.Analytic

private lemma sqrt_sq (a : ℝ≥0∞) : (a ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = a := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Cauchy–Schwarz against the constant one, including infinite measures. -/
lemma lintegral_sq_le_mass {α : Type uAlpha} [MeasurableSpace α]
    (μ : Measure α) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (∫⁻ x, f x ∂μ) ^ (2 : ℕ) ≤ (∫⁻ x, f x ^ (2 : ℕ) ∂μ) * μ univ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    hf (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    one_mul] at h
  have hr (x : ℝ≥0∞) : x ^ (2 : ℝ) = x ^ (2 : ℕ) := ENNReal.rpow_natCast x 2
  simp only [hr] at h
  calc
    (∫⁻ x, f x ∂μ) ^ (2 : ℕ) ≤
        ((∫⁻ x, f x ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) *
          (μ univ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) := pow_le_pow_left' h 2
    _ = _ := by rw [mul_pow, sqrt_sq, sqrt_sq]

/-- Weighted Cauchy–Schwarz in a form that does not need integrability
assumptions: any infinite expressions remain in ℝ≥0∞. -/
lemma lintegral_kernel_sq {α : Type uAlpha} [MeasurableSpace α]
    (μ : Measure α) {k f : α → ℝ≥0∞} (hk : AEMeasurable k μ)
    (hf : AEMeasurable f μ) :
    (∫⁻ x, k x * f x ∂μ) ^ (2 : ℕ) ≤
      (∫⁻ x, k x ∂μ) * (∫⁻ x, k x * f x ^ (2 : ℕ) ∂μ) := by
  have h := lintegral_sq_le_mass (μ.withDensity k)
    (hf.mono_ac (withDensity_absolutelyContinuous μ k))
  rw [lintegral_withDensity_eq_lintegral_mul₀ hk hf,
    lintegral_withDensity_eq_lintegral_mul₀ hk (hf.pow_const 2),
    withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at h
  simpa only [Pi.mul_apply, mul_comm] using h

/-- Schur's L² bound. Bounds for the absolute kernel integral in each
variable control the squared L² seminorm of its positive majorant. -/
lemma kernel_schur_sq {α : Type uAlpha} {β : Type uBeta} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {K : α → β → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {f : β → ℝ≥0∞} (hf : Measurable f) {A B : ℝ≥0∞}
    (hrow : ∀ x, ∫⁻ y, K x y ∂ν ≤ A)
    (hcol : ∀ y, ∫⁻ x, K x y ∂μ ≤ B) :
    ∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ (2 : ℕ) ∂μ ≤
      A * B * ∫⁻ y, f y ^ (2 : ℕ) ∂ν := by
  have hKx (x : α) : Measurable (K x) := hK.comp (measurable_const.prodMk measurable_id)
  have hKy (y : β) : Measurable (fun x => K x y) :=
    hK.comp (measurable_id.prodMk measurable_const)
  have hprod : Measurable (fun p : α × β => K p.1 p.2 * f p.2 ^ (2 : ℕ)) :=
    hK.mul ((hf.comp measurable_snd).pow_const 2)
  calc
    ∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ (2 : ℕ) ∂μ ≤
        ∫⁻ x, A * ∫⁻ y, K x y * f y ^ (2 : ℕ) ∂ν ∂μ := by
      apply lintegral_mono
      intro x
      apply (lintegral_kernel_sq ν (hKx x).aemeasurable hf.aemeasurable).trans
      exact mul_le_mul_left (hrow x) _
    _ = A * ∫⁻ y, (∫⁻ x, K x y ∂μ) * f y ^ (2 : ℕ) ∂ν := by
      rw [lintegral_const_mul A hprod.lintegral_prod_right,
        lintegral_lintegral_swap hprod.aemeasurable]
      congr 1
      apply lintegral_congr
      intro y
      exact lintegral_mul_const _ (hKy y)
    _ ≤ A * ∫⁻ y, B * f y ^ (2 : ℕ) ∂ν := by
      gcongr with y
      exact hcol y
    _ = _ := by rw [lintegral_const_mul B (hf.pow_const 2), mul_assoc]

/-- The Schur bound for a vector-valued integral with a scalar kernel
majorant. It also covers norm-preserving parallel transports between fibers. -/
lemma kernel_integral_schur_sq {α : Type uAlpha} {β : Type uBeta} {E : Type uE}
    [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {K : α → β → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {f : β → ℝ≥0∞} (hf : Measurable f) {A B : ℝ≥0∞}
    (hrow : ∀ x, ∫⁻ y, K x y ∂ν ≤ A)
    (hcol : ∀ y, ∫⁻ x, K x y ∂μ ≤ B)
    {F : α → β → E} (hF : ∀ x y, ‖F x y‖ₑ ≤ K x y * f y) :
    ∫⁻ x, ‖∫ y, F x y ∂ν‖ₑ ^ (2 : ℕ) ∂μ ≤
      A * B * ∫⁻ y, f y ^ (2 : ℕ) ∂ν := by
  apply le_trans _ (kernel_schur_sq μ ν hK hf hrow hcol)
  apply lintegral_mono
  intro x
  apply pow_le_pow_left'
  exact (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono (hF x))

/-- Fiberwise Schur with the genuine product measure. The kernel acts
only on the spatial variable, while the additional fiber variable is kept
parallel. A measure-preserving fiber substitution can subsequently be used
for unfolded reflected terms. -/
lemma fiber_kernel_integral_schur_sq {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} {E : Type uE}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) (ν : Measure β) (σ : Measure γ)
    [SFinite μ] [SFinite ν] [SFinite σ]
    {K : α → β → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {f : β × γ → ℝ≥0∞} (hf : Measurable f) {A B : ℝ≥0∞}
    (hrow : ∀ x, ∫⁻ y, K x y ∂ν ≤ A)
    (hcol : ∀ y, ∫⁻ x, K x y ∂μ ≤ B)
    {F : (α × γ) → β → E} (hFm : StronglyMeasurable (Function.uncurry F))
    (hF : ∀ x c y, ‖F (x, c) y‖ₑ ≤ K x y * f (y, c)) :
    ∫⁻ p, ‖∫ y, F p y ∂ν‖ₑ ^ (2 : ℕ) ∂μ.prod σ ≤
      A * B * ∫⁻ p, f p ^ (2 : ℕ) ∂ν.prod σ := by
  rw [lintegral_prod_symm _ (hFm.integral_prod_right.enorm.pow_const 2).aemeasurable]
  calc
    _ ≤ ∫⁻ c, A * B * ∫⁻ y, f (y, c) ^ (2 : ℕ) ∂ν ∂σ := by
      apply lintegral_mono
      intro c
      exact kernel_integral_schur_sq μ ν hK
        (hf.comp (measurable_id.prodMk measurable_const)) hrow hcol (fun x y => hF x c y)
    _ = _ := by
      have hm : Measurable (Function.uncurry (fun c y => f (y, c) ^ (2 : ℕ))) :=
        (hf.pow_const 2).comp measurable_swap
      rw [lintegral_const_mul _ hm.lintegral_prod_right,
        ← lintegral_prod_symm _ (hf.pow_const 2).aemeasurable]

/-- In particular, genuine strongly measurable kernel integrals map L²
to L² whenever both Schur constants are finite. -/
lemma memLp_kernel_integral {α : Type uAlpha} {β : Type uBeta} {E : Type uE} {G : Type uG}
    [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {K : α → β → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {f : β → G} (hf : StronglyMeasurable f) (hf₂ : MemLp f 2 ν)
    {A B : ℝ≥0∞} (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (hrow : ∀ x, ∫⁻ y, K x y ∂ν ≤ A)
    (hcol : ∀ y, ∫⁻ x, K x y ∂μ ≤ B)
    {F : α → β → E} (hFm : StronglyMeasurable (Function.uncurry F))
    (hF : ∀ x y, ‖F x y‖ₑ ≤ K x y * ‖f y‖ₑ) :
    MemLp (fun x => ∫ y, F x y ∂ν) 2 μ := by
  refine ⟨hFm.integral_prod_right.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num)
    (by norm_num)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  have hfint : ∫⁻ y, ‖f y‖ₑ ^ (2 : ℕ) ∂ν < ⊤ := by
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hf₂.eLpNorm_lt_top
  exact lt_of_le_of_lt (kernel_integral_schur_sq μ ν hK hf.enorm hrow hcol hF)
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top hA.lt_top hB.lt_top) hfint)

/-- The row integrals used above genuinely exist almost everywhere;
the preceding L² estimate is not exploiting the default value of an
undefined Bochner integral. -/
lemma integrable_kernel_ae {α : Type uAlpha} {β : Type uBeta} {E : Type uE} {G : Type uG}
    [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {K : α → β → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {f : β → G} (hf : StronglyMeasurable f) (hf₂ : MemLp f 2 ν)
    {A B : ℝ≥0∞} (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (hrow : ∀ x, ∫⁻ y, K x y ∂ν ≤ A)
    (hcol : ∀ y, ∫⁻ x, K x y ∂μ ≤ B)
    {F : α → β → E} (hFm : StronglyMeasurable (Function.uncurry F))
    (hF : ∀ x y, ‖F x y‖ₑ ≤ K x y * ‖f y‖ₑ) :
    ∀ᵐ x ∂μ, Integrable (F x) ν := by
  have hfint : ∫⁻ y, ‖f y‖ₑ ^ (2 : ℕ) ∂ν < ⊤ := by
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hf₂.eLpNorm_lt_top
  have hm : Measurable (fun x => (∫⁻ y, K x y * ‖f y‖ₑ ∂ν) ^ (2 : ℕ)) :=
    (hK.mul (hf.enorm.comp measurable_snd)).lintegral_prod_right.pow_const 2
  have hi : ∫⁻ x, (∫⁻ y, K x y * ‖f y‖ₑ ∂ν) ^ (2 : ℕ) ∂μ < ⊤ :=
    lt_of_le_of_lt (kernel_schur_sq μ ν hK hf.enorm hrow hcol)
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top hA.lt_top hB.lt_top) hfint)
  filter_upwards [ae_lt_top hm hi.ne] with x hx
  refine ⟨(hFm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  apply lt_of_le_of_lt (lintegral_mono (hF x))
  by_contra hn
  have ht : (∫⁻ y, K x y * ‖f y‖ₑ ∂ν) = ⊤ := top_unique (not_lt.mp hn)
  simp only [ht, ENNReal.top_pow (by norm_num : (2 : ℕ) ≠ 0), lt_self_iff_false] at hx

end TriangularBilliards.Analytic

end
end
end

end OAI
end
end

section
section
namespace OAI


open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section

namespace TriangularBilliards
open SpatialSmoothing
open Analytic

lemma double_lintegral_assoc (Q : Triangle) (F : DoublePhase → ℝ≥0∞) :
    ∫⁻ z, F z ∂doubleMeasure Q = (volume Q.table)⁻¹ *
      ∫⁻ p : ℂ × (Circle × ZMod 2), F ((p.1, p.2.1), p.2.2)
        ∂(volume.restrict Q.table).prod (angularMeasure.prod parityMeasure) := by
  simp only [doubleMeasure, phaseMeasure, Measure.prod_smul_left,
    lintegral_smul_measure, smul_eq_mul]
  congr 1
  exact (measurePreserving_prodAssoc (volume.restrict Q.table) angularMeasure parityMeasure).lintegral_comp_emb MeasurableEquiv.prodAssoc.measurableEmbedding
      (fun p : ℂ × (Circle × ZMod 2) => F ((p.1, p.2.1), p.2.2))

lemma directS_stronglyMeasurable (Q : Triangle) (ε : ℝ)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun z : SmoothPhase => directS Q ε f z.2 z.1.2 z.1.1) := by
  have h : StronglyMeasurable (Function.uncurry (fun (z : SmoothPhase) (y : ℂ) =>
      kernel ε (z.1.1 - y) • f ((y, z.1.2), z.2))) := by
    exact (((kernel_contDiff ε).continuous.measurable.comp
      (measurable_fst.fst.fst.sub measurable_snd)).stronglyMeasurable).smul
      (hf.comp_measurable
        ((measurable_snd.prodMk measurable_fst.fst.snd).prodMk measurable_fst.snd))
  exact h.integral_prod_right

lemma reflectedS_stronglyMeasurable (Q : Triangle) (i : Fin 3) (ε : ℝ)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun z : SmoothPhase => reflectedS Q i ε f z.2 z.1.2 z.1.1) := by
  have h : StronglyMeasurable (Function.uncurry (fun (z : SmoothPhase) (y : ℂ) =>
      kernel ε (z.1.1 - wallReflection Q i y) •
        f ((y, reflectedDirection Q i z.1.2), z.2 + 1))) := by
    exact (((kernel_contDiff ε).continuous.measurable.comp
      (measurable_fst.fst.fst.sub
        ((wallReflection_contDiff Q i).continuous.measurable.comp measurable_snd))).stronglyMeasurable).smul
      (hf.comp_measurable
        ((measurable_snd.prodMk ((measurePreserving_reflectedDirection Q i).measurable.comp
          measurable_fst.fst.snd)).prodMk (measurable_fst.snd.add_const 1)))
  exact h.integral_prod_right

lemma reflectedSmoothing_stronglyMeasurable (Q : Triangle) (ε : ℝ)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (reflectedSmoothing Q ε f) := by
  apply (directS_stronglyMeasurable Q ε hf).add
  convert (Finset.stronglyMeasurable_sum Finset.univ
    (fun i _ => reflectedS_stronglyMeasurable Q i ε hf)) using 1
  ext z
  simp only [Finset.sum_apply]

lemma directS_l2sq (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    ∫⁻ z : SmoothPhase, ‖directS Q ε f z.2 z.1.2 z.1.1‖ₑ ^ (2 : ℕ) ∂doubleMeasure Q ≤
      ∫⁻ z, ‖f z‖ₑ ^ (2 : ℕ) ∂doubleMeasure Q := by
  rw [double_lintegral_assoc, double_lintegral_assoc]
  apply mul_le_mul_right
  have hK : Measurable (Function.uncurry (fun x y : ℂ => ENNReal.ofReal (kernel ε (x - y)))) :=
    ENNReal.measurable_ofReal.comp ((kernel_contDiff ε).continuous.measurable.comp
      (measurable_fst.sub measurable_snd))
  have hFm : StronglyMeasurable (Function.uncurry
      (fun (p : ℂ × (Circle × ZMod 2)) (y : ℂ) =>
        kernel ε (p.1 - y) • f ((y, p.2.1), p.2.2))) := by
    exact (((kernel_contDiff ε).continuous.measurable.comp
      (measurable_fst.fst.sub measurable_snd)).stronglyMeasurable).smul
      (hf.comp_measurable
        ((measurable_snd.prodMk measurable_fst.snd.fst).prodMk measurable_fst.snd.snd))
  have h := fiber_kernel_integral_schur_sq (volume.restrict Q.table) (volume.restrict Q.table)
    (angularMeasure.prod parityMeasure) hK
    (hf.enorm.comp ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd))
    (kernel_row_bound Q hε) (kernel_col_bound Q hε) hFm (fun x c y => by
      simp only [enorm_smul, Real.enorm_eq_ofReal (kernel_nonneg ε _), Function.comp_apply,
        le_refl])
  simpa only [one_mul, directS, Function.comp_apply] using h

lemma measurePreserving_directionParityReflection (Q : Triangle) (i : Fin 3) :
    MeasurePreserving (fun z : SmoothPhase =>
      ((z.1.1, reflectedDirection Q i z.1.2), z.2 + 1)) (doubleMeasure Q) (doubleMeasure Q) := by
  convert ((MeasurePreserving.id ((volume Q.table)⁻¹ • volume.restrict Q.table)).prod
    (measurePreserving_reflectedDirection Q i)).prod (measurePreserving_parity_add 1) using 1
  · funext ⟨⟨x, v⟩, b⟩
    simp only [Prod.map_apply, id_eq, add_comm]
  · rfl
  · rfl

lemma reflectedS_l2sq (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    ∫⁻ z : SmoothPhase, ‖reflectedS Q i ε f z.2 z.1.2 z.1.1‖ₑ ^ (2 : ℕ) ∂doubleMeasure Q ≤
      ∫⁻ z, ‖f z‖ₑ ^ (2 : ℕ) ∂doubleMeasure Q := by
  let g : SmoothPhase → ℂ := fun z => f ((z.1.1, reflectedDirection Q i z.1.2), z.2 + 1)
  have hg : StronglyMeasurable g := hf.comp_measurable
    (measurePreserving_directionParityReflection Q i).measurable
  have he : (∫⁻ z, ‖g z‖ₑ ^ (2 : ℕ) ∂doubleMeasure Q) =
      ∫⁻ z, ‖f z‖ₑ ^ (2 : ℕ) ∂doubleMeasure Q :=
    (measurePreserving_directionParityReflection Q i).lintegral_comp (hf.enorm.pow_const 2)
  rw [← he, double_lintegral_assoc, double_lintegral_assoc]
  apply mul_le_mul_right
  have hK : Measurable (Function.uncurry (fun x y : ℂ =>
      ENNReal.ofReal (kernel ε (x - wallReflection Q i y)))) :=
    ENNReal.measurable_ofReal.comp ((kernel_contDiff ε).continuous.measurable.comp
      (measurable_fst.sub ((wallReflection_contDiff Q i).continuous.measurable.comp measurable_snd)))
  have hFm : StronglyMeasurable (Function.uncurry
      (fun (p : ℂ × (Circle × ZMod 2)) (y : ℂ) =>
        kernel ε (p.1 - wallReflection Q i y) • g ((y, p.2.1), p.2.2))) := by
    exact (((kernel_contDiff ε).continuous.measurable.comp
      (measurable_fst.fst.sub ((wallReflection_contDiff Q i).continuous.measurable.comp
        measurable_snd))).stronglyMeasurable).smul
      (hg.comp_measurable
        ((measurable_snd.prodMk measurable_fst.snd.fst).prodMk measurable_fst.snd.snd))
  have h := fiber_kernel_integral_schur_sq (volume.restrict Q.table) (volume.restrict Q.table)
    (angularMeasure.prod parityMeasure) hK
    (hg.enorm.comp ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd))
    (reflected_kernel_row_bound Q i hε) (reflected_kernel_col_bound Q i hε) hFm (fun x c y => by
      simp only [enorm_smul, Real.enorm_eq_ofReal (kernel_nonneg ε _), Function.comp_apply,
        le_refl])
  simpa only [one_mul, reflectedS, g, Function.comp_apply] using h

lemma eLpNorm_two_mono_lintegral {α : Type uAlpha} {E : Type uE} {F : Type uF} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedAddCommGroup F] (μ : Measure α)
    {f : α → E} {g : α → F}
    (h : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂μ) ≤ ∫⁻ x, ‖g x‖ₑ ^ (2 : ℕ) ∂μ) :
    eLpNorm' f 2 μ ≤ eLpNorm' g 2 μ := by
  simp only [eLpNorm'_eq_lintegral_enorm, ENNReal.rpow_two]
  exact ENNReal.rpow_le_rpow h (by norm_num)

lemma directS_eLpNorm (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    eLpNorm (fun z : SmoothPhase => directS Q ε f z.2 z.1.2 z.1.1) 2 (doubleMeasure Q) ≤
      eLpNorm f 2 (doubleMeasure Q) := by
  simpa only [eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
    eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), ENNReal.toReal_ofNat]
    using eLpNorm_two_mono_lintegral _ (directS_l2sq Q hε hf)

lemma reflectedS_eLpNorm (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    eLpNorm (fun z : SmoothPhase => reflectedS Q i ε f z.2 z.1.2 z.1.1) 2 (doubleMeasure Q) ≤
      eLpNorm f 2 (doubleMeasure Q) := by
  simpa only [eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
    eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), ENNReal.toReal_ofNat]
    using eLpNorm_two_mono_lintegral _ (reflectedS_l2sq Q i hε hf)

lemma reflectedSmoothing_eLpNorm (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    eLpNorm (reflectedSmoothing Q ε f) 2 (doubleMeasure Q) ≤
      4 * eLpNorm f 2 (doubleMeasure Q) := by
  let d : SmoothPhase → ℂ := fun z => directS Q ε f z.2 z.1.2 z.1.1
  let r : Fin 3 → SmoothPhase → ℂ := fun i z => reflectedS Q i ε f z.2 z.1.2 z.1.1
  have he : reflectedSmoothing Q ε f = d + ∑ i, r i := by
    ext z
    simp only [reflectedSmoothing, Pi.add_apply, Finset.sum_apply, d, r]
  rw [he]
  calc
    _ ≤ eLpNorm d 2 (doubleMeasure Q) + eLpNorm (∑ i, r i) 2 (doubleMeasure Q) :=
      eLpNorm_add_le (directS_stronglyMeasurable Q ε hf).aestronglyMeasurable
        (Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => (reflectedS_stronglyMeasurable Q i ε hf).aestronglyMeasurable)) (by norm_num)
    _ ≤ eLpNorm f 2 (doubleMeasure Q) + ∑ i : Fin 3, eLpNorm (r i) 2 (doubleMeasure Q) :=
      add_le_add (directS_eLpNorm Q hε hf)
        (eLpNorm_sum_le (fun i _ => (reflectedS_stronglyMeasurable Q i ε hf).aestronglyMeasurable) (by norm_num))
    _ ≤ eLpNorm f 2 (doubleMeasure Q) + ∑ _i : Fin 3, eLpNorm f 2 (doubleMeasure Q) :=
      add_le_add le_rfl (Finset.sum_le_sum (fun i _ => reflectedS_eLpNorm Q i hε hf))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma reflectedSmoothing_memLp (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) (hf₂ : MemLp f 2 (doubleMeasure Q)) :
    MemLp (reflectedSmoothing Q ε f) 2 (doubleMeasure Q) := by
  exact ⟨(reflectedSmoothing_stronglyMeasurable Q ε hf).aestronglyMeasurable, (reflectedSmoothing_eLpNorm Q hε hf).trans_lt
    (ENNReal.mul_lt_top (by norm_num) hf₂.eLpNorm_lt_top)⟩

/-- The actual gradient convolution, as a bounded linear differential. -/
def directGradS (Q : Triangle) (ε : ℝ) (f : SmoothPhase → ℂ) : SmoothPhase → (ℂ →L[ℝ] ℂ) :=
  fun z => ∫ y in Q.table, (fderiv ℝ (kernel ε) (z.1.1 - y)).smulRight (f ((y, z.1.2), z.2))

def reflectedGradS (Q : Triangle) (i : Fin 3) (ε : ℝ)
    (f : SmoothPhase → ℂ) : SmoothPhase → (ℂ →L[ℝ] ℂ) :=
  fun z => ∫ y in Q.table, (fderiv ℝ (kernel ε) (z.1.1 - wallReflection Q i y)).smulRight
    (f ((y, reflectedDirection Q i z.1.2), z.2 + 1))

def reflectedSmoothingGradient (Q : Triangle) (ε : ℝ) (f : SmoothPhase → ℂ) :
    SmoothPhase → (ℂ →L[ℝ] ℂ) := directGradS Q ε f + ∑ i, reflectedGradS Q i ε f

lemma derivative_kernel_row_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    ∫⁻ y in Q.table, ENNReal.ofReal ‖fderiv ℝ (kernel ε) (x - y)‖ ≤
      ENNReal.ofReal (derivativeMass / ε) := by
  calc
    _ ≤ ∫⁻ y : ℂ, ENNReal.ofReal ‖fderiv ℝ (kernel ε) (x - y)‖ :=
      lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
    _ = _ := (lintegral_sub_left_eq_self
      (fun y : ℂ => ENNReal.ofReal ‖fderiv ℝ (kernel ε) y‖) x).trans
        (kernel_derivative_lintegral hε)

lemma derivative_kernel_col_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε) (y : ℂ) :
    ∫⁻ x in Q.table, ENNReal.ofReal ‖fderiv ℝ (kernel ε) (x - y)‖ ≤
      ENNReal.ofReal (derivativeMass / ε) := by
  calc
    _ ≤ ∫⁻ x : ℂ, ENNReal.ofReal ‖fderiv ℝ (kernel ε) (x - y)‖ :=
      lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
    _ = _ := (lintegral_sub_right_eq_self
      (fun x : ℂ => ENNReal.ofReal ‖fderiv ℝ (kernel ε) x‖) y).trans
        (kernel_derivative_lintegral hε)

lemma reflected_derivative_kernel_row_bound (Q : Triangle) (i : Fin 3)
    {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    ∫⁻ y in Q.table, ENNReal.ofReal ‖fderiv ℝ (kernel ε) (x - wallReflection Q i y)‖ ≤
      ENNReal.ofReal (derivativeMass / ε) := by
  calc
    _ ≤ ∫⁻ y : ℂ, ENNReal.ofReal ‖fderiv ℝ (kernel ε) (x - wallReflection Q i y)‖ :=
      lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
    _ = ∫⁻ y : ℂ, ENNReal.ofReal ‖fderiv ℝ (kernel ε) (x - y)‖ :=
      (measurePreserving_wallReflection Q i).lintegral_comp
        (ENNReal.measurable_ofReal.comp (((kernel_contDiff ε).continuous_fderiv (by simp)).norm.measurable.comp
          (measurable_const.sub measurable_id)))
    _ = _ := (lintegral_sub_left_eq_self
      (fun y : ℂ => ENNReal.ofReal ‖fderiv ℝ (kernel ε) y‖) x).trans
        (kernel_derivative_lintegral hε)

lemma reflected_derivative_kernel_col_bound (Q : Triangle) (i : Fin 3)
    {ε : ℝ} (hε : 0 < ε) (y : ℂ) :
    ∫⁻ x in Q.table, ENNReal.ofReal ‖fderiv ℝ (kernel ε) (x - wallReflection Q i y)‖ ≤
      ENNReal.ofReal (derivativeMass / ε) := derivative_kernel_col_bound Q hε _

lemma smulRight_stronglyMeasurable {α : Type uAlpha} [MeasurableSpace α]
    {a : α → (ℂ →L[ℝ] ℝ)} {b : α → ℂ} (ha : StronglyMeasurable a) (hb : StronglyMeasurable b) :
    StronglyMeasurable (fun x => (a x).smulRight (b x)) := by
  exact isBoundedBilinearMap_apply.continuous.comp_stronglyMeasurable
    (((ContinuousLinearMap.smulRightL ℝ ℂ ℂ).continuous.comp_stronglyMeasurable ha).prodMk hb)

lemma directGradS_stronglyMeasurable (Q : Triangle) (ε : ℝ)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (directGradS Q ε f) := by
  have h : StronglyMeasurable (Function.uncurry (fun (z : SmoothPhase) (y : ℂ) =>
      (fderiv ℝ (kernel ε) (z.1.1 - y)).smulRight (f ((y, z.1.2), z.2)))) :=
    smulRight_stronglyMeasurable
      ((((kernel_contDiff ε).continuous_fderiv (by simp)).measurable.comp
        (measurable_fst.fst.fst.sub measurable_snd)).stronglyMeasurable)
      (hf.comp_measurable ((measurable_snd.prodMk measurable_fst.fst.snd).prodMk measurable_fst.snd))
  exact h.integral_prod_right

lemma reflectedGradS_stronglyMeasurable (Q : Triangle) (i : Fin 3) (ε : ℝ)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (reflectedGradS Q i ε f) := by
  have h : StronglyMeasurable (Function.uncurry (fun (z : SmoothPhase) (y : ℂ) =>
      (fderiv ℝ (kernel ε) (z.1.1 - wallReflection Q i y)).smulRight
        (f ((y, reflectedDirection Q i z.1.2), z.2 + 1)))) :=
    smulRight_stronglyMeasurable
      ((((kernel_contDiff ε).continuous_fderiv (by simp)).measurable.comp
        (measurable_fst.fst.fst.sub
          ((wallReflection_contDiff Q i).continuous.measurable.comp measurable_snd))).stronglyMeasurable)
      (hf.comp_measurable
        ((measurable_snd.prodMk ((measurePreserving_reflectedDirection Q i).measurable.comp
          measurable_fst.fst.snd)).prodMk (measurable_fst.snd.add_const 1)))
  exact h.integral_prod_right

lemma reflectedSmoothingGradient_stronglyMeasurable (Q : Triangle) (ε : ℝ)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (reflectedSmoothingGradient Q ε f) :=
  (directGradS_stronglyMeasurable Q ε hf).add
    (Finset.stronglyMeasurable_sum _ (fun i _ => reflectedGradS_stronglyMeasurable Q i ε hf))

lemma eLpNorm_two_le_of_lintegral {α : Type uAlpha} {E : Type uE} {F : Type uF} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedAddCommGroup F] (μ : Measure α)
    {f : α → E} {g : α → F} {C : ℝ≥0∞}
    (h : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂μ) ≤ C * C * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℕ) ∂μ) :
    eLpNorm' f 2 μ ≤ C * eLpNorm' g 2 μ := by
  simp only [eLpNorm'_eq_lintegral_enorm, ENNReal.rpow_two]
  calc
    _ ≤ (C * C * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℕ) ∂μ) ^ (1 / (2 : ℝ)) :=
      ENNReal.rpow_le_rpow h (by norm_num)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      congr 1
      rw [← pow_two, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
      norm_num

lemma directGradS_l2sq (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    ∫⁻ z : SmoothPhase, ‖directGradS Q ε f z‖ₑ ^ (2 : ℕ) ∂doubleMeasure Q ≤
      ENNReal.ofReal (derivativeMass / ε) * ENNReal.ofReal (derivativeMass / ε) *
        ∫⁻ z, ‖f z‖ₑ ^ (2 : ℕ) ∂doubleMeasure Q := by
  rw [double_lintegral_assoc, double_lintegral_assoc]
  rw [← mul_assoc _ ((volume Q.table)⁻¹), mul_comm _ ((volume Q.table)⁻¹), mul_assoc]
  apply mul_le_mul_right
  have hK : Measurable (Function.uncurry (fun x y : ℂ =>
      ENNReal.ofReal ‖fderiv ℝ (kernel ε) (x - y)‖)) :=
    ENNReal.measurable_ofReal.comp (((kernel_contDiff ε).continuous_fderiv (by simp)).norm.measurable.comp
      (measurable_fst.sub measurable_snd))
  have hFm : StronglyMeasurable (Function.uncurry
      (fun (p : ℂ × (Circle × ZMod 2)) (y : ℂ) =>
        (fderiv ℝ (kernel ε) (p.1 - y)).smulRight (f ((y, p.2.1), p.2.2)))) :=
    smulRight_stronglyMeasurable
      ((((kernel_contDiff ε).continuous_fderiv (by simp)).measurable.comp
        (measurable_fst.fst.sub measurable_snd)).stronglyMeasurable)
      (hf.comp_measurable
        ((measurable_snd.prodMk measurable_fst.snd.fst).prodMk measurable_fst.snd.snd))
  have h := fiber_kernel_integral_schur_sq (volume.restrict Q.table) (volume.restrict Q.table)
    (angularMeasure.prod parityMeasure) hK
    (hf.enorm.comp ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd))
    (derivative_kernel_row_bound Q hε) (derivative_kernel_col_bound Q hε) hFm (fun x c y => by
      rw [← ofReal_norm, ContinuousLinearMap.norm_smulRight_apply,
        ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
      simp only [ofReal_norm, Function.comp_apply]
      exact le_rfl)
  exact h

lemma reflectedGradS_l2sq (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    ∫⁻ z : SmoothPhase, ‖reflectedGradS Q i ε f z‖ₑ ^ (2 : ℕ) ∂doubleMeasure Q ≤
      ENNReal.ofReal (derivativeMass / ε) * ENNReal.ofReal (derivativeMass / ε) *
        ∫⁻ z, ‖f z‖ₑ ^ (2 : ℕ) ∂doubleMeasure Q := by
  let g : SmoothPhase → ℂ := fun z => f ((z.1.1, reflectedDirection Q i z.1.2), z.2 + 1)
  have hg : StronglyMeasurable g := hf.comp_measurable
    (measurePreserving_directionParityReflection Q i).measurable
  have he : (∫⁻ z, ‖g z‖ₑ ^ (2 : ℕ) ∂doubleMeasure Q) =
      ∫⁻ z, ‖f z‖ₑ ^ (2 : ℕ) ∂doubleMeasure Q :=
    (measurePreserving_directionParityReflection Q i).lintegral_comp (hf.enorm.pow_const 2)
  rw [← he, double_lintegral_assoc, double_lintegral_assoc]
  rw [← mul_assoc _ ((volume Q.table)⁻¹), mul_comm _ ((volume Q.table)⁻¹), mul_assoc]
  apply mul_le_mul_right
  have hK : Measurable (Function.uncurry (fun x y : ℂ =>
      ENNReal.ofReal ‖fderiv ℝ (kernel ε) (x - wallReflection Q i y)‖)) :=
    ENNReal.measurable_ofReal.comp (((kernel_contDiff ε).continuous_fderiv (by simp)).norm.measurable.comp
      (measurable_fst.sub ((wallReflection_contDiff Q i).continuous.measurable.comp measurable_snd)))
  have hFm : StronglyMeasurable (Function.uncurry
      (fun (p : ℂ × (Circle × ZMod 2)) (y : ℂ) =>
        (fderiv ℝ (kernel ε) (p.1 - wallReflection Q i y)).smulRight (g ((y, p.2.1), p.2.2)))) :=
    smulRight_stronglyMeasurable
      ((((kernel_contDiff ε).continuous_fderiv (by simp)).measurable.comp
        (measurable_fst.fst.sub ((wallReflection_contDiff Q i).continuous.measurable.comp
          measurable_snd))).stronglyMeasurable)
      (hg.comp_measurable
        ((measurable_snd.prodMk measurable_fst.snd.fst).prodMk measurable_fst.snd.snd))
  have h := fiber_kernel_integral_schur_sq (volume.restrict Q.table) (volume.restrict Q.table)
    (angularMeasure.prod parityMeasure) hK
    (hg.enorm.comp ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd))
    (reflected_derivative_kernel_row_bound Q i hε) (reflected_derivative_kernel_col_bound Q i hε)
    hFm (fun x c y => by
      rw [← ofReal_norm, ContinuousLinearMap.norm_smulRight_apply,
        ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
      simp only [ofReal_norm, Function.comp_apply]
      exact le_rfl)
  exact h

lemma directGradS_eLpNorm (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    eLpNorm (directGradS Q ε f) 2 (doubleMeasure Q) ≤
      ENNReal.ofReal (derivativeMass / ε) * eLpNorm f 2 (doubleMeasure Q) := by
  simpa only [eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
    eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), ENNReal.toReal_ofNat]
    using eLpNorm_two_le_of_lintegral _ (directGradS_l2sq Q hε hf)

lemma reflectedGradS_eLpNorm (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    eLpNorm (reflectedGradS Q i ε f) 2 (doubleMeasure Q) ≤
      ENNReal.ofReal (derivativeMass / ε) * eLpNorm f 2 (doubleMeasure Q) := by
  simpa only [eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
    eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), ENNReal.toReal_ofNat]
    using eLpNorm_two_le_of_lintegral _ (reflectedGradS_l2sq Q i hε hf)

lemma eLpNorm_add_sum_fin_three_le {α : Type uAlpha} {E : Type uE} [MeasurableSpace α]
    [NormedAddCommGroup E] (μ : Measure α) {d : α → E} {r : Fin 3 → α → E}
    {C : ℝ≥0∞} (hd : AEStronglyMeasurable d μ)
    (hr : ∀ i, AEStronglyMeasurable (r i) μ)
    (hdb : eLpNorm d 2 μ ≤ C) (hrb : ∀ i, eLpNorm (r i) 2 μ ≤ C) :
    eLpNorm (d + ∑ i, r i) 2 μ ≤ 4 * C := by
  have hsum := Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => hr i)
  calc
    _ ≤ eLpNorm d 2 μ + eLpNorm (∑ i, r i) 2 μ := by
      simpa only [eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
        eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
        eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), ENNReal.toReal_ofNat]
        using eLpNorm'_add_le hd hsum (by norm_num : (1 : ℝ) ≤ 2)
    _ ≤ C + ∑ i : Fin 3, eLpNorm (r i) 2 μ :=
      add_le_add hdb (eLpNorm_sum_le (fun i _ => hr i) (by norm_num))
    _ ≤ C + ∑ _i : Fin 3, C := add_le_add le_rfl (Finset.sum_le_sum (fun i _ => hrb i))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma reflectedSmoothingGradient_eLpNorm (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) :
    eLpNorm (reflectedSmoothingGradient Q ε f) 2 (doubleMeasure Q) ≤
      4 * ENNReal.ofReal (derivativeMass / ε) * eLpNorm f 2 (doubleMeasure Q) := by
  have hd : AEStronglyMeasurable (directGradS Q ε f) (doubleMeasure Q) :=
    (directGradS_stronglyMeasurable Q ε hf).aestronglyMeasurable
  have hr (i : Fin 3) : AEStronglyMeasurable (reflectedGradS Q i ε f) (doubleMeasure Q) :=
    (reflectedGradS_stronglyMeasurable Q i ε hf).aestronglyMeasurable
  have h := eLpNorm_add_sum_fin_three_le (doubleMeasure Q) hd hr
    (directGradS_eLpNorm Q hε hf) (fun i => reflectedGradS_eLpNorm Q i hε hf)
  exact h.trans_eq (mul_assoc _ _ _).symm

lemma reflectedSmoothingGradient_memLp (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : StronglyMeasurable f) (hf₂ : MemLp f 2 (doubleMeasure Q)) :
    MemLp (reflectedSmoothingGradient Q ε f) 2 (doubleMeasure Q) := by
  exact ⟨(reflectedSmoothingGradient_stronglyMeasurable Q ε hf).aestronglyMeasurable, (reflectedSmoothingGradient_eLpNorm Q hε hf).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top) hf₂.eLpNorm_lt_top)⟩

end TriangularBilliards

end
end
end

end OAI
end
end

section
section
namespace OAI


open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section

namespace TriangularBilliards.SpatialSmoothing
open Filter
open scoped Topology BoundedContinuousFunction

lemma rho_fderiv_neg (x : ℂ) : fderiv ℝ rho (-x) = -fderiv ℝ rho x := by
  have h := (rho_contDiff.differentiable (by simp) (-x)).hasFDerivAt.comp x
    (hasFDerivAt_id x).neg
  have he : (fun z : ℂ => rho (-z)) = rho := funext rho_neg
  change HasFDerivAt (fun z : ℂ => rho (-z)) _ x at h
  rw [he] at h
  have hh := h.fderiv
  simp only [ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_id] at hh
  rw [hh]
  simp

lemma rho_fderiv_integral : (∫ x : ℂ, fderiv ℝ rho x) = 0 := by
  have h := integral_neg_eq_self (fun x : ℂ => fderiv ℝ rho x) volume
  simp_rw [rho_fderiv_neg] at h
  rw [integral_neg] at h
  ext v
  have hv := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) h
  simp only [neg_apply, zero_apply] at hv ⊢
  linarith

lemma rho_smulRight_integral (c : ℂ) :
    (∫ x : ℂ, (fderiv ℝ rho x).smulRight c) = 0 := by
  have h := ((ContinuousLinearMap.smulRightL ℝ ℂ ℂ).flip c).integral_comp_comm
    rho_fderiv_integrable
  change (∫ x : ℂ, (fderiv ℝ rho x).smulRight c) =
    (∫ x : ℂ, fderiv ℝ rho x).smulRight c at h
  simpa only [rho_fderiv_integral, ContinuousLinearMap.zero_smulRight] using h

lemma rescaled_gradient_continuous (f : ℂ →ᵇ ℂ) (x : ℂ) (ε : ℝ) :
    Continuous (fun y : ℂ => (fderiv ℝ rho y).smulRight (f (x - ε • y))) := by
  let L : (ℂ →L[ℝ] ℝ) →L[ℝ] ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
    ContinuousLinearMap.smulRightL ℝ ℂ ℂ
  have h₁ : Continuous (fun y : ℂ => L (fderiv ℝ rho y)) :=
    L.continuous.comp (rho_contDiff.continuous_fderiv (by simp))
  have h₂ : Continuous (fun y : ℂ => f (x - ε • y)) := by fun_prop
  exact h₁.clm_apply h₂

lemma rescaled_gradient_dominated (f : ℂ →ᵇ ℂ) (x : ℂ) (ε : ℝ) (y : ℂ) :
    ‖(fderiv ℝ rho y).smulRight (f (x - ε • y))‖ ≤ ‖fderiv ℝ rho y‖ * ‖f‖ := by
  rw [ContinuousLinearMap.norm_smulRight_apply]
  exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _)

lemma rescaled_gradient_pointwise (f : ℂ →ᵇ ℂ) (x y : ℂ) :
    Tendsto (fun ε : ℝ => (fderiv ℝ rho y).smulRight (f (x - ε • y)))
      (𝓝 0) (𝓝 ((fderiv ℝ rho y).smulRight (f x))) := by
  let L : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := (ContinuousLinearMap.smulRightL ℝ ℂ ℂ) (fderiv ℝ rho y)
  have h : Continuous (fun ε : ℝ => L (f (x - ε • y))) := by fun_prop
  have hL (c : ℂ) : L c = (fderiv ℝ rho y).smulRight c := by
    ext v
    rfl
  simp_rw [hL] at h
  have hh := h.continuousAt (x := (0 : ℝ))
  simpa only [zero_smul, sub_zero] using hh.tendsto

/-- Rescaled cancellation for a bounded spatially continuous input. This
is the elementary pointwise producer for the small scaled derivative. -/
lemma rescaled_gradient_tendsto (f : ℂ →ᵇ ℂ) (x : ℂ) :
    Tendsto (fun ε : ℝ => ∫ y : ℂ,
      (fderiv ℝ rho y).smulRight (f (x - ε • y))) (𝓝 0) (𝓝 0) := by
  have hi : Integrable (fun y : ℂ => ‖fderiv ℝ rho y‖ * ‖f‖) volume :=
    rho_fderiv_integrable.norm.mul_const ‖f‖
  have hlim : Tendsto (fun ε : ℝ => ∫ y : ℂ,
      (fderiv ℝ rho y).smulRight (f (x - ε • y))) (𝓝 0)
      (𝓝 (∫ y : ℂ, (fderiv ℝ rho y).smulRight (f x))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun y : ℂ => ‖fderiv ℝ rho y‖ * ‖f‖)
    · exact Eventually.of_forall fun ε => (rescaled_gradient_continuous f x ε).aestronglyMeasurable
    · exact Eventually.of_forall fun ε => Eventually.of_forall (rescaled_gradient_dominated f x ε)
    · exact hi
    · exact Eventually.of_forall (rescaled_gradient_pointwise f x)
  simpa only [rho_smulRight_integral] using hlim

/-- Exact substitution relating the rescaled derivative to the actual
first-derivative convolution kernel. -/
lemma scaled_full_gradient (ε : ℝ) (hε : 0 < ε) (f : ℂ → ℂ) (x : ℂ) :
    ε • (∫ y : ℂ, (fderiv ℝ (kernel ε) (x-y)).smulRight (f y)) =
      ∫ y : ℂ, (fderiv ℝ rho y).smulRight (f (x - ε • y)) := by
  rw [← integral_sub_left_eq_self
    (fun y : ℂ => (fderiv ℝ (kernel ε) (x-y)).smulRight (f y)) volume x]
  simp only [sub_sub_cancel]
  have hs := Measure.integral_comp_smul volume
    (fun y : ℂ => (fderiv ℝ (kernel ε) y).smulRight (f (x-y))) ε
  rw [Complex.finrank_real_complex, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg ε))] at hs
  have he : (∫ y : ℂ, (fderiv ℝ (kernel ε) (ε • y)).smulRight (f (x-ε • y))) =
      (ε ^ 3)⁻¹ • (∫ y : ℂ, (fderiv ℝ rho y).smulRight (f (x-ε • y))) := by
    simp_rw [kernel_fderiv, smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
    have hl (y : ℂ) : ((ε ^ 3)⁻¹ • fderiv ℝ rho y).smulRight (f (x - ε • y)) =
        (ε ^ 3)⁻¹ • (fderiv ℝ rho y).smulRight (f (x - ε • y)) := by
      ext v
      simp only [ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul,
        smul_smul]
    simp only [hl, integral_smul]
  rw [he] at hs
  have heq := congrArg (fun u : ℂ →L[ℝ] ℂ => ε ^ 3 • u) hs
  simp only [smul_smul] at heq
  have h₁ : ε ^ 3 * (ε ^ 3)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hε.ne')
  have h₂ : ε ^ 3 * (ε ^ 2)⁻¹ = ε := by field_simp
  simpa only [h₁, h₂, one_smul] using heq.symm

end TriangularBilliards.SpatialSmoothing

namespace TriangularBilliards
open Filter SpatialSmoothing
open scoped Topology BoundedContinuousFunction

lemma kernel_fderiv_eq_zero {ε : ℝ} (hε : 0 < ε) {x : ℂ} (hx : ε < ‖x‖) :
    fderiv ℝ (kernel ε) x = 0 := by
  by_contra hn
  have hm := support_fderiv_subset ℝ (f := kernel ε) hn
  rw [tsupport, kernel_support hε, closure_ball _ hε.ne', mem_closedBall_zero_iff] at hm
  exact (not_le_of_gt hx) hm

lemma directGradS_eq_full (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    (f : SmoothPhase → ℂ) (z : SmoothPhase) (hz : closedBall z.1.1 ε ⊆ Q.table) :
    directGradS Q ε f z = ∫ y : ℂ,
      (fderiv ℝ (kernel ε) (z.1.1 - y)).smulRight (f ((y,z.1.2),z.2)) := by
  rw [directGradS, ← integral_indicator Q.measurableSet_table]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    by_cases hy : y ∈ Q.table
    · rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy]
      have hn : ε < ‖z.1.1 - y‖ := by
        by_contra hh
        exact hy (hz (by rw [mem_closedBall, dist_comm, dist_eq_norm]; exact not_lt.mp hh))
      simp only [kernel_fderiv_eq_zero hε hn, ContinuousLinearMap.zero_smulRight]

lemma reflectedGradS_zero_of_coord (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    (f : SmoothPhase → ℂ) (z : SmoothPhase)
    (hz : Q.coordinateBound * ε < Q.basis.coord (i+2) z.1.1) :
    reflectedGradS Q i ε f z = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem Q.measurableSet_table] with y hy
  have hn : ε < ‖z.1.1 - wallReflection Q i y‖ := by
    by_contra hh
    exact (not_le_of_gt hz) (Q.coord_small_of_reflected_near i hy (not_lt.mp hh))
  simp only [kernel_fderiv_eq_zero hε hn, ContinuousLinearMap.zero_smulRight, Pi.zero_apply]

lemma eventually_interior_gradient (Q : Triangle) (f : SmoothPhase → ℂ)
    (z : SmoothPhase) (hz : z.1.1 ∈ Q.table) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), reflectedSmoothingGradient Q ε f z =
      ∫ y : ℂ, (fderiv ℝ (kernel ε) (z.1.1-y)).smulRight (f ((y,z.1.2),z.2)) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp Q.isOpen_table _ hz
  have hcoords : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i : Fin 3,
      Q.coordinateBound * ε < Q.basis.coord (i+2) z.1.1 := by
    rw [Filter.eventually_all]
    intro i
    have hp := (Q.table_iff_coords z.1.1).mp hz (i+2)
    have hc : Continuous (fun ε : ℝ => Q.coordinateBound * ε) := by fun_prop
    simpa only [mul_zero] using hc.continuousAt.eventually (gt_mem_nhds (by simpa only [mul_zero] using hp))
  filter_upwards [nhdsWithin_le_nhds hcoords,
    nhdsWithin_le_nhds (gt_mem_nhds hr), self_mem_nhdsWithin] with ε hc hεr hε
  have hε' : 0 < ε := hε
  have hfull := directGradS_eq_full Q hε' f z (fun y hy => hball (by
    rw [mem_ball]
    exact (mem_closedBall.mp hy).trans_lt hεr))
  change directGradS Q ε f z + ∑ i : Fin 3, reflectedGradS Q i ε f z = _
  simp only [reflectedGradS_zero_of_coord Q _ hε' f z (hc _), Finset.sum_const_zero, add_zero]
  exact hfull

lemma scaled_gradient_pointwise (Q : Triangle) (f : DoublePhase →ᵇ ℂ)
    (z : DoublePhase) (hz : z.1.1 ∈ Q.table) :
    Tendsto (fun ε : ℝ => ε • reflectedSmoothingGradient Q ε f z)
      (𝓝[>] 0) (𝓝 0) := by
  let g : ℂ →ᵇ ℂ := f.compContinuous ⟨fun y => ((y,z.1.2),z.2), by fun_prop⟩
  have h := (rescaled_gradient_tendsto g z.1.1).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  apply h.congr'
  filter_upwards [eventually_interior_gradient Q f z hz, self_mem_nhdsWithin] with ε hε hp
  rw [hε]
  exact (scaled_full_gradient ε hp (fun y => f ((y,z.1.2),z.2)) z.1.1).symm

end TriangularBilliards

namespace TriangularBilliards
open Filter SpatialSmoothing
open scoped Topology BoundedContinuousFunction

lemma norm_integral_le_kernel_bound {α : Type uAlpha} {E : Type uE} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α}
    (F : α → E) {K : α → ℝ≥0∞} {H C : ℝ} (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hF : ∀ x, ‖F x‖ₑ ≤ K x * ENNReal.ofReal H)
    (hK : ∫⁻ x, K x ∂μ ≤ ENNReal.ofReal C) :
    ‖∫ x, F x ∂μ‖ ≤ C * H := by
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC hH)).mp
  rw [ofReal_norm, ENNReal.ofReal_mul hC]
  calc
    ‖∫ x, F x ∂μ‖ₑ ≤ ∫⁻ x, ‖F x‖ₑ ∂μ := enorm_integral_le_lintegral_enorm F
    _ ≤ ∫⁻ x, K x * ENNReal.ofReal H ∂μ := lintegral_mono hF
    _ = (∫⁻ x, K x ∂μ) * ENNReal.ofReal H := lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by gcongr

lemma directGradS_norm_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} {H : ℝ} (hH : 0 ≤ H) (hf : ∀ z, ‖f z‖ ≤ H)
    (z : DoublePhase) : ‖directGradS Q ε f z‖ ≤ (derivativeMass / ε) * H := by
  apply norm_integral_le_kernel_bound (μ := volume.restrict Q.table)
    (K := fun y => ENNReal.ofReal ‖fderiv ℝ (kernel ε) (z.1.1-y)‖) _ hH
    (div_nonneg derivativeMass_nonneg hε.le)
  · intro y
    rw [← ofReal_norm, ContinuousLinearMap.norm_smulRight_apply,
      ENNReal.ofReal_mul (norm_nonneg _)]
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (hf ((y,z.1.2),z.2))) _
  · exact derivative_kernel_row_bound Q hε z.1.1

lemma reflectedGradS_norm_bound (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} {H : ℝ} (hH : 0 ≤ H) (hf : ∀ z, ‖f z‖ ≤ H)
    (z : DoublePhase) : ‖reflectedGradS Q i ε f z‖ ≤ (derivativeMass / ε) * H := by
  apply norm_integral_le_kernel_bound (μ := volume.restrict Q.table)
    (K := fun y => ENNReal.ofReal ‖fderiv ℝ (kernel ε) (z.1.1 - wallReflection Q i y)‖) _ hH
    (div_nonneg derivativeMass_nonneg hε.le)
  · intro y
    rw [← ofReal_norm, ContinuousLinearMap.norm_smulRight_apply,
      ENNReal.ofReal_mul (norm_nonneg _)]
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (hf ((y,reflectedDirection Q i z.1.2),z.2+1))) _
  · exact reflected_derivative_kernel_row_bound Q i hε z.1.1

lemma scaled_gradient_norm_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} {H : ℝ} (hH : 0 ≤ H) (hf : ∀ z, ‖f z‖ ≤ H)
    (z : DoublePhase) : ‖ε • reflectedSmoothingGradient Q ε f z‖ ≤ 4 * derivativeMass * H := by
  have hb : ‖reflectedSmoothingGradient Q ε f z‖ ≤ 4 * (derivativeMass / ε) * H := by
    change ‖directGradS Q ε f z + ∑ i : Fin 3, reflectedGradS Q i ε f z‖ ≤ _
    calc
      _ ≤ ‖directGradS Q ε f z‖ + ∑ i : Fin 3, ‖reflectedGradS Q i ε f z‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
      _ ≤ (derivativeMass / ε) * H + ∑ _i : Fin 3, (derivativeMass / ε) * H := by
        gcongr
        · exact directGradS_norm_bound Q hε hH hf z
        · exact reflectedGradS_norm_bound Q _ hε hH hf z
      _ = _ := by simp; ring
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  calc
    _ ≤ ε * (4 * (derivativeMass / ε) * H) := mul_le_mul_of_nonneg_left hb hε.le
    _ = _ := by field_simp

lemma ae_double_position_in_table (Q : Triangle) :
    ∀ᵐ z ∂doubleMeasure Q, z.1.1 ∈ Q.table := by
  exact (measurePreserving_fst (μ := phaseMeasure Q) (ν := parityMeasure)).quasiMeasurePreserving.ae
    (ae_position_in_table Q)

/-- The small-scaled-derivative estimate on the dense class of bounded
continuous fields, for the actual reflected convolution kernel. -/
lemma scaled_gradient_integral_tendsto (Q : Triangle) (f : DoublePhase →ᵇ ℂ) :
    Tendsto (fun ε : ℝ => ∫ z, ‖ε • reflectedSmoothingGradient Q ε f z‖ ^ 2 ∂doubleMeasure Q)
      (𝓝[>] 0) (𝓝 0) := by
  have hlim : Tendsto (fun ε : ℝ => ∫ z, ‖ε • reflectedSmoothingGradient Q ε f z‖ ^ 2 ∂doubleMeasure Q)
      (𝓝[>] 0) (𝓝 (∫ _ : DoublePhase, (0 : ℝ) ∂doubleMeasure Q)) := by
    apply tendsto_integral_filter_of_norm_le_const
    · exact Eventually.of_forall fun ε =>
        (((reflectedSmoothingGradient_stronglyMeasurable Q ε f.continuous.stronglyMeasurable).const_smul ε).measurable.norm.pow_const 2).aestronglyMeasurable
    · refine ⟨(4 * derivativeMass * ‖f‖) ^ 2, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (scaled_gradient_norm_bound Q hε (norm_nonneg f) f.norm_coe_le_norm z) 2
    · filter_upwards [ae_double_position_in_table Q] with z hz
      simpa only [norm_zero, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, zero_pow] using
        ((scaled_gradient_pointwise Q f z hz).norm.pow 2)
  simpa only [integral_zero] using hlim

end TriangularBilliards

namespace TriangularBilliards
open Filter SpatialSmoothing
open scoped Topology BoundedContinuousFunction

lemma integrable_slice_ae (Q : Triangle) {f : DoublePhase → ℂ}
    (hf : Integrable f (doubleMeasure Q)) :
    ∀ᵐ z ∂doubleMeasure Q, Integrable (fun y => f ((y,z.1.2),z.2)) (volume.restrict Q.table) := by
  let μ : Measure ℂ := (volume Q.table)⁻¹ • volume.restrict Q.table
  have hμ : IsProbabilityMeasure μ := ⟨Q.normalized_area_univ⟩
  have ha := measurePreserving_prodAssoc μ angularMeasure parityMeasure
  have hfi : Integrable (fun p : ℂ × (Circle × ZMod 2) => f ((p.1,p.2.1),p.2.2))
      (μ.prod (angularMeasure.prod parityMeasure)) := by
    exact (ha.integrable_comp_emb MeasurableEquiv.prodAssoc.measurableEmbedding).mp hf
  have hs : ∀ᵐ c ∂angularMeasure.prod parityMeasure,
      Integrable (fun y => f ((y,c.1),c.2)) (volume.restrict Q.table) := by
    filter_upwards [hfi.prod_left_ae] with c hc
    exact (integrable_smul_measure (by simpa using Q.area_lt_top.ne)
      (by simpa using Q.area_pos.ne')).mp hc
  exact ha.quasiMeasurePreserving.ae
    ((measurePreserving_snd (μ := μ) (ν := angularMeasure.prod parityMeasure)).quasiMeasurePreserving.ae hs)

lemma equal_slice_ae (Q : Triangle) {f g : DoublePhase → ℂ}
    (h : f =ᵐ[doubleMeasure Q] g) :
    ∀ᵐ z ∂doubleMeasure Q, (fun y => f ((y,z.1.2),z.2)) =ᵐ[volume.restrict Q.table]
      (fun y => g ((y,z.1.2),z.2)) := by
  let μ : Measure ℂ := (volume Q.table)⁻¹ • volume.restrict Q.table
  have hμ : IsProbabilityMeasure μ := ⟨Q.normalized_area_univ⟩
  have ha := measurePreserving_prodAssoc μ angularMeasure parityMeasure
  have hi := ha.symm MeasurableEquiv.prodAssoc
  have hc := (Measure.measurePreserving_swap (μ := angularMeasure.prod parityMeasure) (ν := μ)).quasiMeasurePreserving.ae
    (hi.quasiMeasurePreserving.ae h)
  have hs : ∀ᵐ c ∂angularMeasure.prod parityMeasure,
      (fun y => f ((y,c.1),c.2)) =ᵐ[volume.restrict Q.table] (fun y => g ((y,c.1),c.2)) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hc] with c hc
    exact (Measure.ae_ennreal_smul_measure_iff (by simpa using Q.area_lt_top.ne)).mp hc
  exact ha.quasiMeasurePreserving.ae
    ((measurePreserving_snd (μ := μ) (ν := angularMeasure.prod parityMeasure)).quasiMeasurePreserving.ae hs)

lemma directGradS_congr_ae (Q : Triangle) (ε : ℝ) {f g : DoublePhase → ℂ}
    (h : f =ᵐ[doubleMeasure Q] g) : directGradS Q ε f =ᵐ[doubleMeasure Q] directGradS Q ε g := by
  filter_upwards [equal_slice_ae Q h] with z hz
  apply integral_congr_ae
  filter_upwards [hz] with y hy
  rw [hy]

lemma reflectedGradS_congr_ae (Q : Triangle) (i : Fin 3) (ε : ℝ) {f g : DoublePhase → ℂ}
    (h : f =ᵐ[doubleMeasure Q] g) :
    reflectedGradS Q i ε f =ᵐ[doubleMeasure Q] reflectedGradS Q i ε g := by
  filter_upwards [(measurePreserving_directionParityReflection Q i).quasiMeasurePreserving.ae
    (equal_slice_ae Q h)] with z hz
  apply integral_congr_ae
  filter_upwards [hz] with y hy
  rw [hy]

lemma reflectedSmoothingGradient_congr_ae (Q : Triangle) (ε : ℝ) {f g : DoublePhase → ℂ}
    (h : f =ᵐ[doubleMeasure Q] g) :
    reflectedSmoothingGradient Q ε f =ᵐ[doubleMeasure Q] reflectedSmoothingGradient Q ε g := by
  filter_upwards [directGradS_congr_ae Q ε h,
    Filter.eventually_all.mpr (fun i => reflectedGradS_congr_ae Q i ε h)] with z hd hr
  change directGradS Q ε f z + ∑ i, reflectedGradS Q i ε f z =
    directGradS Q ε g z + ∑ i, reflectedGradS Q i ε g z
  rw [hd]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => hr i)

lemma smulRight_sub (k : ℂ →L[ℝ] ℝ) (a b : ℂ) :
    k.smulRight (a-b) = k.smulRight a - k.smulRight b := by
  ext v
  change k v • (a-b) = k v • a - k v • b
  exact smul_sub _ _ _

lemma smulRight_integrable {k : ℂ → (ℂ →L[ℝ] ℝ)} {f : ℂ → ℂ}
    {ν : Measure ℂ} (hk : StronglyMeasurable k) (hf : StronglyMeasurable f)
    (hi : Integrable f ν) {C : ℝ} (hb : ∀ y, ‖k y‖ ≤ C) :
    Integrable (fun y => (k y).smulRight (f y)) ν := by
  apply (hi.norm.const_mul C).mono' (smulRight_stronglyMeasurable hk hf).aestronglyMeasurable
  exact Eventually.of_forall fun y => by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul_of_nonneg_right (hb y) (norm_nonneg _)

lemma directGradS_integrable_ae (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hf : StronglyMeasurable f) (hi : Integrable f (doubleMeasure Q)) :
    ∀ᵐ z ∂doubleMeasure Q, Integrable (fun y => (fderiv ℝ (kernel ε) (z.1.1-y)).smulRight
      (f ((y,z.1.2),z.2))) (volume.restrict Q.table) := by
  obtain ⟨C,hC⟩ := ((kernel_hasCompactSupport hε).fderiv ℝ).exists_bound_of_continuous
    ((kernel_contDiff ε).continuous_fderiv (by simp))
  filter_upwards [integrable_slice_ae Q hi] with z hz
  exact smulRight_integrable
    (((kernel_contDiff ε).continuous_fderiv (by simp)).stronglyMeasurable.comp_measurable
      (measurable_const.sub measurable_id))
    (hf.comp_measurable ((measurable_id.prodMk measurable_const).prodMk measurable_const))
    hz (fun y => hC (z.1.1-y))

lemma reflectedGradS_integrable_ae (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hf : StronglyMeasurable f) (hi : Integrable f (doubleMeasure Q)) :
    ∀ᵐ z ∂doubleMeasure Q, Integrable (fun y =>
      (fderiv ℝ (kernel ε) (z.1.1-wallReflection Q i y)).smulRight
      (f ((y,reflectedDirection Q i z.1.2),z.2+1))) (volume.restrict Q.table) := by
  obtain ⟨C,hC⟩ := ((kernel_hasCompactSupport hε).fderiv ℝ).exists_bound_of_continuous
    ((kernel_contDiff ε).continuous_fderiv (by simp))
  filter_upwards [(measurePreserving_directionParityReflection Q i).quasiMeasurePreserving.ae
    (integrable_slice_ae Q hi)] with z hz
  exact smulRight_integrable
    (((kernel_contDiff ε).continuous_fderiv (by simp)).stronglyMeasurable.comp_measurable
      (measurable_const.sub (wallReflection_contDiff Q i).continuous.measurable))
    (hf.comp_measurable ((measurable_id.prodMk measurable_const).prodMk measurable_const))
    hz (fun y => hC (z.1.1-wallReflection Q i y))

lemma directGradS_sub_ae (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f g : DoublePhase → ℂ} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g)
    (hfi : Integrable f (doubleMeasure Q)) (hgi : Integrable g (doubleMeasure Q)) :
    directGradS Q ε (f-(g : DoublePhase → ℂ)) =ᵐ[doubleMeasure Q] directGradS Q ε f - directGradS Q ε g := by
  filter_upwards [directGradS_integrable_ae Q hε hf hfi,
    directGradS_integrable_ae Q hε hg hgi] with z hz hw
  change (∫ y in Q.table, (fderiv ℝ (kernel ε) (z.1.1-y)).smulRight (f ((y,z.1.2),z.2) - g ((y,z.1.2),z.2))) = _
  simp_rw [smulRight_sub]
  exact integral_sub hz hw

lemma reflectedGradS_sub_ae (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {f g : DoublePhase → ℂ} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g)
    (hfi : Integrable f (doubleMeasure Q)) (hgi : Integrable g (doubleMeasure Q)) :
    reflectedGradS Q i ε (f-(g : DoublePhase → ℂ)) =ᵐ[doubleMeasure Q] reflectedGradS Q i ε f - reflectedGradS Q i ε g := by
  filter_upwards [reflectedGradS_integrable_ae Q i hε hf hfi,
    reflectedGradS_integrable_ae Q i hε hg hgi] with z hz hw
  change (∫ y in Q.table, (fderiv ℝ (kernel ε) (z.1.1-wallReflection Q i y)).smulRight
    (f ((y,reflectedDirection Q i z.1.2),z.2+1) - g ((y,reflectedDirection Q i z.1.2),z.2+1))) = _
  simp_rw [smulRight_sub]
  exact integral_sub hz hw

lemma reflectedSmoothingGradient_sub_ae (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f g : DoublePhase → ℂ} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g)
    (hfi : Integrable f (doubleMeasure Q)) (hgi : Integrable g (doubleMeasure Q)) :
    reflectedSmoothingGradient Q ε (f-(g : DoublePhase → ℂ)) =ᵐ[doubleMeasure Q]
      reflectedSmoothingGradient Q ε f - reflectedSmoothingGradient Q ε g := by
  filter_upwards [directGradS_sub_ae Q hε hf hg hfi hgi,
    Filter.eventually_all.mpr (fun i => reflectedGradS_sub_ae Q i hε hf hg hfi hgi)] with z hd hr
  change directGradS Q ε (f-(g : DoublePhase → ℂ)) z + ∑ i, reflectedGradS Q i ε (f-(g : DoublePhase → ℂ)) z =
    (directGradS Q ε f z + ∑ i, reflectedGradS Q i ε f z) -
      (directGradS Q ε g z + ∑ i, reflectedGradS Q i ε g z)
  simp only [Pi.sub_apply] at hd hr
  rw [hd]
  simp_rw [hr]
  rw [Finset.sum_sub_distrib]
  abel

lemma scaled_gradient_lpNorm_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hf : StronglyMeasurable f) (hf₂ : MemLp f 2 (doubleMeasure Q)) :
    lpNorm (ε • reflectedSmoothingGradient Q ε f) 2 (doubleMeasure Q) ≤
      (4 * derivativeMass) * lpNorm f 2 (doubleMeasure Q) := by
  rw [← toReal_eLpNorm ((reflectedSmoothingGradient_stronglyMeasurable Q ε hf).aestronglyMeasurable.const_smul ε),
    ← toReal_eLpNorm hf.aestronglyMeasurable]
  have hb : eLpNorm (ε • reflectedSmoothingGradient Q ε f) 2 (doubleMeasure Q) ≤
      ENNReal.ofReal (4 * derivativeMass) * eLpNorm f 2 (doubleMeasure Q) := by
    calc
      _ ≤ ‖ε‖ₑ * eLpNorm (reflectedSmoothingGradient Q ε f) 2 (doubleMeasure Q) := eLpNorm_const_smul_le
      _ ≤ ‖ε‖ₑ * (4 * ENNReal.ofReal (derivativeMass / ε) * eLpNorm f 2 (doubleMeasure Q)) := by
        gcongr
        exact reflectedSmoothingGradient_eLpNorm Q hε hf
      _ = _ := by
        rw [Real.enorm_eq_ofReal hε.le, ENNReal.ofReal_div_of_pos hε,
          ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
        have he : ENNReal.ofReal ε ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hε
        rw [div_eq_mul_inv]
        calc
          _ = 4 * ENNReal.ofReal derivativeMass * eLpNorm f 2 (doubleMeasure Q) *
              (ENNReal.ofReal ε * (ENNReal.ofReal ε)⁻¹) := by ac_rfl
          _ = _ := by rw [ENNReal.mul_inv_cancel he ENNReal.ofReal_ne_top, mul_one]; norm_num
  have ht : ENNReal.ofReal (4 * derivativeMass) * eLpNorm f 2 (doubleMeasure Q) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf₂.eLpNorm_ne_top
  have h := ENNReal.toReal_mono ht hb
  have hC : 0 ≤ 4 * derivativeMass := mul_nonneg (by norm_num) derivativeMass_nonneg
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using h

lemma lpNorm_congr_ae_of_strong {α : Type uAlpha} {E : Type uE} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {p : ℝ≥0∞} {f g : α → E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (h : f =ᵐ[μ] g) :
    lpNorm f p μ = lpNorm g p μ := by
  rw [← toReal_eLpNorm hf, ← toReal_eLpNorm hg]
  exact congrArg ENNReal.toReal (eLpNorm_congr_enorm_ae (h.fun_comp enorm))

lemma scaled_gradient_lpNorm_tendsto_bounded (Q : Triangle) (f : DoublePhase →ᵇ ℂ) :
    Tendsto (fun ε : ℝ => lpNorm (ε • reflectedSmoothingGradient Q ε f) 2 (doubleMeasure Q))
      (𝓝[>] 0) (𝓝 0) := by
  have he (ε : ℝ) : lpNorm (ε • reflectedSmoothingGradient Q ε f) 2 (doubleMeasure Q) =
      Real.sqrt (∫ z, ‖ε • reflectedSmoothingGradient Q ε f z‖ ^ 2 ∂doubleMeasure Q) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      ((reflectedSmoothingGradient_stronglyMeasurable Q ε f.continuous.stronglyMeasurable).const_smul ε).aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat, Pi.smul_apply, Real.rpow_two, Real.sqrt_eq_rpow]
    norm_num
  simp_rw [he]
  simpa only [Real.sqrt_zero, Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp
    (scaled_gradient_integral_tendsto Q f)

/-- The small-scaled-derivative estimate for every L² input
and the reflected triangular kernel, not merely a dense test class. -/
lemma scaled_gradient_lpNorm_tendsto (Q : Triangle) {f : DoublePhase → ℂ}
    (hf : StronglyMeasurable f) (hf₂ : MemLp f 2 (doubleMeasure Q)) :
    Tendsto (fun ε : ℝ => lpNorm (ε • reflectedSmoothingGradient Q ε f) 2 (doubleMeasure Q))
      (𝓝[>] 0) (𝓝 0) := by
  let C : ℝ := 4 * derivativeMass
  have hC : 0 ≤ C := mul_nonneg (by norm_num) derivativeMass_nonneg
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  let η : ℝ := δ / (2 * (C+1))
  have hη : 0 < η := div_pos hδ (by positivity)
  obtain ⟨g,hg,hg₂⟩ := hf₂.exists_boundedContinuous_eLpNorm_sub_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (ENNReal.ofReal_ne_zero_iff.mpr hη)
  have hsmall : lpNorm (f - (g : DoublePhase → ℂ)) 2 (doubleMeasure Q) ≤ η := by
    rw [← toReal_eLpNorm (hf.aestronglyMeasurable.sub g.continuous.aestronglyMeasurable)]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hg).trans_eq (ENNReal.toReal_ofReal hη.le)
  have hgsmall := (Metric.tendsto_nhds.mp (scaled_gradient_lpNorm_tendsto_bounded Q g))
    (δ/2) (by positivity)
  filter_upwards [self_mem_nhdsWithin, hgsmall] with ε hε he
  have hgm := (reflectedSmoothingGradient_memLp Q hε g.continuous.stronglyMeasurable hg₂).const_smul ε
  have hfm := (reflectedSmoothingGradient_memLp Q hε hf hf₂).const_smul ε
  have hdiffm := (reflectedSmoothingGradient_memLp Q hε
    (hf.sub g.continuous.stronglyMeasurable) (hf₂.sub hg₂)).const_smul ε
  have hae : (ε • reflectedSmoothingGradient Q ε f - ε • reflectedSmoothingGradient Q ε g) =ᵐ[doubleMeasure Q]
      ε • reflectedSmoothingGradient Q ε (f - (g : DoublePhase → ℂ)) := by
    filter_upwards [reflectedSmoothingGradient_sub_ae Q hε hf g.continuous.stronglyMeasurable
      (hf₂.integrable (by norm_num)) (hg₂.integrable (by norm_num))] with z hz
    simp only [Pi.sub_apply, Pi.smul_apply] at hz ⊢
    rw [hz, smul_sub]
  have hn := lpNorm_le_lpNorm_add_lpNorm_sub' hgm (f := ε • reflectedSmoothingGradient Q ε f)
    (by norm_num : (1:ℝ≥0∞) ≤ 2)
  rw [lpNorm_congr_ae_of_strong (hfm.sub hgm).aestronglyMeasurable
    hdiffm.aestronglyMeasurable hae] at hn
  have hb := scaled_gradient_lpNorm_bound Q hε (hf.sub g.continuous.stronglyMeasurable) (hf₂.sub hg₂)
  have ht : C * η < δ/2 := by
    dsimp [η]
    have hc : (0:ℝ) < C+1 := by linarith
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < 2*(C+1))]
    nlinarith
  have hnonneg : 0 ≤ lpNorm (ε • reflectedSmoothingGradient Q ε g) 2 (doubleMeasure Q) := lpNorm_nonneg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at he
  rw [Real.dist_eq, sub_zero, abs_of_nonneg lpNorm_nonneg]
  have hh : lpNorm (ε • reflectedSmoothingGradient Q ε (f - (g : DoublePhase → ℂ))) 2
      (doubleMeasure Q) ≤ C * η := hb.trans (mul_le_mul_of_nonneg_left hsmall hC)
  linarith

end TriangularBilliards

end
end
end

end OAI
end
end

section
section
namespace OAI


open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section

/-! Hilbert-space analysis of actual measurable measure-preserving flows.
The continuity hypothesis below is only slice-wise almost everywhere and
therefore applies to billiards at each fixed time, despite wall collisions. -/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section

namespace TriangularBilliards.Analysis

variable {A : Type uA} [MeasurableSpace A] {μ : Measure A}

lemma norm_sq_L2 (f : Lp ℂ 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have h := congrArg (RCLike.re (K := ℂ)) (L2.inner_def f f)
  rw [← integral_re] at h
  · simpa only [← norm_sq_eq_re_inner] using h
  · exact L2.integrable_inner f f

variable [TopologicalSpace A] [BorelSpace A]
  [IsFiniteMeasure μ]
  (F : ℝ → A → A) (hm : ∀ t, MeasurePreserving (F t) μ μ)

def koopman (t : ℝ) : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ (F t) (hm t)

omit [TopologicalSpace A] [BorelSpace A] [IsFiniteMeasure μ] in
lemma coe_koopman (t : ℝ) (f : Lp ℂ 2 μ) :
    (koopman F hm t f : A → ℂ) =ᵐ[μ] (fun x => f (F t x)) :=
  Lp.coeFn_compMeasurePreserving f (hm t)

lemma koopman_bounded_continuous (u : A →ᵇ ℂ) (t : ℝ) :
    (koopman F hm t (BoundedContinuousFunction.toLp 2 μ ℂ u) : A → ℂ) =ᵐ[μ]
      (fun x => u (F t x)) := by
  exact (coe_koopman F hm t _).trans
    ((hm t).quasiMeasurePreserving.ae (BoundedContinuousFunction.coeFn_toLp 2 μ ℂ u))

lemma continuous_koopman_bounded (u : A →ᵇ ℂ)
    (hc : ∀ t, ∀ᵐ x ∂μ, ContinuousAt (fun s => F s x) t) :
    Continuous (fun t => koopman F hm t (BoundedContinuousFunction.toLp 2 μ ℂ u)) := by
  rw [continuous_iff_continuousAt]
  intro t
  let f := BoundedContinuousFunction.toLp 2 μ ℂ u
  have he (s : ℝ) : ‖koopman F hm s f - koopman F hm t f‖ ^ 2 =
      ∫ x, ‖u (F s x) - u (F t x)‖ ^ 2 ∂μ := by
    rw [norm_sq_L2]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (koopman F hm s f) (koopman F hm t f),
      koopman_bounded_continuous F hm u s, koopman_bounded_continuous F hm u t] with x hsub hs ht
    simp only [hsub, Pi.sub_apply]
    change ‖(koopman F hm s (BoundedContinuousFunction.toLp 2 μ ℂ u)) x -
      (koopman F hm t (BoundedContinuousFunction.toLp 2 μ ℂ u)) x‖ ^ 2 = _
    rw [hs, ht]
  have hi : Tendsto (fun s : ℝ => ∫ x, ‖u (F s x) - u (F t x)‖ ^ 2 ∂μ)
      (𝓝 t) (𝓝 (∫ x, ‖u (F t x) - u (F t x)‖ ^ 2 ∂μ)) := by
    apply tendsto_integral_filter_of_norm_le_const
    · exact Eventually.of_forall fun s =>
        ((((u.continuous.measurable.comp (hm s).measurable).sub
        (u.continuous.measurable.comp (hm t).measurable)).norm.pow_const 2).aestronglyMeasurable)
    · refine ⟨(2 * ‖u‖) ^ 2, Eventually.of_forall fun s => Eventually.of_forall fun x => ?_⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      calc
        ‖u (F s x) - u (F t x)‖ ≤ ‖u (F s x)‖ + ‖u (F t x)‖ := norm_sub_le _ _
        _ ≤ 2 * ‖u‖ := by linarith [u.norm_coe_le_norm (F s x), u.norm_coe_le_norm (F t x)]
    · filter_upwards [hc t] with x hx
      exact (((u.continuous.continuousAt.comp hx).sub continuousAt_const).norm.pow 2).tendsto
  have hn : Tendsto (fun s => ‖koopman F hm s f - koopman F hm t f‖)
      (𝓝 t) (𝓝 0) := by
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hi
    simpa only [Function.comp_def, ← he, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), sub_self,
      norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero,
      Real.sqrt_zero] using hh
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

variable [NormalSpace A] [μ.WeaklyRegular]

lemma continuous_koopman
    (hc : ∀ t, ∀ᵐ x ∂μ, ContinuousAt (fun s => F s x) t) :
    Continuous (fun tf : ℝ × Lp ℂ 2 μ => koopman F hm tf.1 tf.2) := by
  have h : Continuous (fun ft : Lp ℂ 2 μ × ℝ => koopman F hm ft.2 ft.1) := by
    apply continuous_prod_of_dense_continuous_lipschitzWith _ 1
      (BoundedContinuousFunction.toLp_denseRange (p := 2) ℂ μ ℂ (by norm_num))
    · rintro _ ⟨u, rfl⟩
      exact continuous_koopman_bounded F hm u hc
    · intro t
      exact (koopman F hm t).isometry.lipschitz
  exact h.comp continuous_swap

lemma continuous_koopman_time
    (hc : ∀ t, ∀ᵐ x ∂μ, ContinuousAt (fun s => F s x) t) (f : Lp ℂ 2 μ) :
    Continuous (fun t => koopman F hm t f) :=
  (continuous_koopman F hm hc).comp
    (show Continuous (fun t : ℝ => (t, f)) from continuous_id.prodMk continuous_const)

end TriangularBilliards.Analysis

end
end
end
end

end OAI
end
end

section
section
namespace OAI


open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section

/-! Strongly continuous unitary dynamics and the closed generator graph.
All hypotheses here are structural flow properties; the billiard instance
is constructed from its geometric flow, not postulated. -/

open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section

namespace TriangularBilliards.Analysis

variable (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

structure HilbertFlow where
  act : ℝ → H →ₗᵢ[ℂ] H
  zero : ∀ u, act 0 u = u
  add : ∀ s t u, act (s + t) u = act s (act t u)
  continuous : ∀ u, Continuous (fun t => act t u)

namespace HilbertFlow

variable {H} (W : HilbertFlow H)

@[simp] lemma act_zero (u : H) : W.act 0 u = u := W.zero u

lemma act_neg (t : ℝ) (u : H) : W.act (-t) (W.act t u) = u := by
  rw [← W.add, neg_add_cancel, W.zero]

lemma inner_act (t : ℝ) (u v : H) : inner ℂ (W.act t u) (W.act t v) = inner ℂ u v :=
  (W.act t).inner_map_map u v

lemma continuous_joint : Continuous (fun tu : ℝ × H => W.act tu.1 tu.2) := by
  have h : Continuous (fun ut : H × ℝ => W.act ut.2 ut.1) :=
    continuous_prod_of_continuous_lipschitzWith _ 1 W.continuous
      (fun t => (W.act t).isometry.lipschitz)
  exact h.comp continuous_swap

/-- Conjugating by a second genuine unitary flow preserves all structural
properties. For billiards the second flow is angular rotation. -/
def conjugate (V : HilbertFlow H) (θ : ℝ) : HilbertFlow H where
  act t := (V.act θ).comp ((W.act t).comp (V.act (-θ)))
  zero u := by
    change V.act θ (W.act 0 (V.act (-θ) u)) = u
    rw [W.zero, ← V.add, add_neg_cancel, V.zero]
  add s t u := by
    change V.act θ (W.act (s + t) (V.act (-θ) u)) =
      V.act θ (W.act s (V.act (-θ) (V.act θ (W.act t (V.act (-θ) u)))))
    rw [← V.add, neg_add_cancel, V.zero, W.add]
  continuous u := (V.act θ).continuous.comp (W.continuous (V.act (-θ) u))

lemma conjugate_joint (V : HilbertFlow H) :
    Continuous (fun p : ℝ × ℝ × H => (W.conjugate V p.1).act p.2.1 p.2.2) := by
  change Continuous (fun p : ℝ × ℝ × H => V.act p.1 (W.act p.2.1 (V.act (-p.1) p.2.2)))
  exact V.continuous_joint.comp (continuous_fst.prodMk
    (W.continuous_joint.comp (continuous_snd.fst.prodMk
      (V.continuous_joint.comp (continuous_fst.neg.prodMk continuous_snd.snd)))))

variable [CompleteSpace H]

omit [CompleteSpace H] in
lemma intervalIntegrable (u : H) (a b : ℝ) :
    IntervalIntegrable (fun t => W.act t u) volume a b :=
  (W.continuous u).intervalIntegrable _ _

/-- Integration in time, as a genuine bounded linear operator. No
operator-norm continuity of the unitary group is presupposed. -/
def timeIntegral (a b : ℝ) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun u => ∫ t in a..b, W.act t u
      map_add' := fun u v => by
        simp only [map_add]
        exact intervalIntegral.integral_add (W.intervalIntegrable u a b) (W.intervalIntegrable v a b)
      map_smul' := fun r u => by
        simp only [map_smul, RingHom.id_apply]
        exact intervalIntegral.integral_smul r (fun t => W.act t u) }
    |b - a|
    (fun u => by
      calc
        ‖∫ t in a..b, W.act t u‖ ≤ ‖u‖ * |b - a| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => (W.act t).norm_map u |>.le)
        _ = |b - a| * ‖u‖ := mul_comm _ _)

omit [CompleteSpace H] in
@[simp] lemma timeIntegral_apply (a b : ℝ) (u : H) :
    W.timeIntegral a b u = ∫ t in a..b, W.act t u := rfl

/-- The generator domain encoded by the exact orbit integral identity.
This formulation makes weak closedness an immediate linear-test fact. -/
def HasGenerator (u v : H) : Prop :=
  ∀ t : ℝ, W.act t u - u = W.timeIntegral 0 t v

lemma HasGenerator.hasDerivAt {u v : H} (h : W.HasGenerator u v) (t : ℝ) :
    HasDerivAt (fun s => W.act s u) (W.act t v) t := by
  have hi := W.intervalIntegrable v 0 t
  have hd := intervalIntegral.integral_hasDerivAt_right hi
    (W.continuous v).stronglyMeasurable.stronglyMeasurableAtFilter (W.continuous v).continuousAt
  have he : (fun s => W.act s u) = (fun s => u + ∫ r in 0..s, W.act r v) := by
    funext s
    have hh := h s
    change W.act s u - u = ∫ r in 0..s, W.act r v at hh
    exact eq_add_of_sub_eq' hh
  rw [he]
  exact hd.const_add u

lemma hasGenerator_of_hasDerivAt {u v : H}
    (h : ∀ t, HasDerivAt (fun s => W.act s u) (W.act t v) t) : W.HasGenerator u v := by
  intro t
  rw [timeIntegral_apply, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => h s) (W.intervalIntegrable v 0 t), W.zero]

lemma generator_unique {u v v' : H} (h : W.HasGenerator u v) (h' : W.HasGenerator u v') :
    v = v' := by
  have he := (HasGenerator.hasDerivAt W h 0).unique (HasGenerator.hasDerivAt W h' 0)
  simpa only [W.zero] using he

lemma generator_skew {u v a b : H} (hu : W.HasGenerator u a) (hv : W.HasGenerator v b) :
    inner ℂ u b + inner ℂ a v = 0 := by
  have hd := (HasGenerator.hasDerivAt W hu 0).inner ℂ (HasGenerator.hasDerivAt W hv 0)
  have heq : (fun t => inner ℂ (W.act t u) (W.act t v)) = (fun _ : ℝ => inner ℂ u v) :=
    funext fun t => W.inner_act t u v
  rw [heq] at hd
  simpa only [W.zero] using hd.unique (hasDerivAt_const 0 (inner ℂ u v))

omit [CompleteSpace H] in
lemma generatorGraph_closed : IsClosed {p : H × H | W.HasGenerator p.1 p.2} := by
  have he : {p : H × H | W.HasGenerator p.1 p.2} =
      ⋂ t : ℝ, {p : H × H | W.act t p.1 - p.1 = W.timeIntegral 0 t p.2} := by
    ext p
    simp only [HasGenerator, mem_ofPred_eq, mem_iInter]
  rw [he]
  exact isClosed_iInter fun t => isClosed_eq
    (((W.act t).continuous.comp continuous_fst).sub continuous_fst)
    ((W.timeIntegral 0 t).continuous.comp continuous_snd)

omit [CompleteSpace H] in
lemma generatorGraph_convex : Convex ℝ {p : H × H | W.HasGenerator p.1 p.2} := by
  intro p hp q hq a b _ _ _ t
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    map_add]
  change ((W.act t).toLinearMap (a • p.1) + (W.act t).toLinearMap (b • q.1)) -
    (a • p.1 + b • q.1) = W.timeIntegral 0 t (a • p.2) + W.timeIntegral 0 t (b • q.2)
  rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower,
    ContinuousLinearMap.map_smul_of_tower, ContinuousLinearMap.map_smul_of_tower]
  rw [add_sub_add_comm, ← smul_sub, ← smul_sub]
  change a • (W.act t p.1 - p.1) + b • (W.act t q.1 - q.1) = _
  rw [hp t, hq t]

lemma timeIntegral_translate (a b τ : ℝ) (u : H) :
    W.act τ (W.timeIntegral a b u) = W.timeIntegral (τ + a) (τ + b) u := by
  simp only [timeIntegral_apply]
  rw [← (W.act τ).intervalIntegral_comp_comm]
  have he : (fun t => W.act τ (W.act t u)) = (fun t => W.act (τ + t) u) :=
    funext fun t => (W.add τ t u).symm
  rw [he]
  exact intervalIntegral.integral_comp_add_left (fun t => W.act t u) τ

/-- The finite negative-time average. -/
def negativeAverage (T : ℝ) : H →L[ℂ] H := (T⁻¹ : ℝ) • W.timeIntegral (-T) 0

omit [CompleteSpace H] in
lemma negativeAverage_eq (T : ℝ) (u : H) :
    W.negativeAverage T u = (T⁻¹ : ℝ) • ∫ t in 0..T, W.act (-t) u := by
  change (T⁻¹ : ℝ) • (∫ t in -T..0, W.act t u) =
    (T⁻¹ : ℝ) • ∫ t in 0..T, W.act (-t) u
  rw [intervalIntegral.integral_comp_neg (fun t => W.act t u)]
  simp only [neg_zero]

omit [CompleteSpace H] in
lemma negativeAverage_norm_le {T : ℝ} (hT : 0 < T) (u : H) :
    ‖W.negativeAverage T u‖ ≤ ‖u‖ := by
  rw [negativeAverage_eq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hT)]
  calc
    T⁻¹ * ‖∫ t in 0..T, W.act (-t) u‖ ≤ T⁻¹ * (‖u‖ * T) := by
      gcongr
      simpa only [sub_zero, abs_of_pos hT] using
        intervalIntegral.norm_integral_le_of_norm_le_const
          (f := fun t => W.act (-t) u) (a := 0) (b := T)
          (fun t _ => (W.act (-t)).norm_map u |>.le)
    _ = ‖u‖ := by field_simp

lemma timeIntegral_hasDerivAt_right (u : H) (a t : ℝ) :
    HasDerivAt (fun s => W.timeIntegral a s u) (W.act t u) t := by
  exact intervalIntegral.integral_hasDerivAt_right (W.intervalIntegrable u a t)
    (W.continuous u).stronglyMeasurable.stronglyMeasurableAtFilter (W.continuous u).continuousAt

lemma timeIntegral_hasDerivAt_translate (u : H) (a b t : ℝ) :
    HasDerivAt (fun s => W.timeIntegral (s + a) (s + b) u)
      (W.act (t + b) u - W.act (t + a) u) t := by
  have hb := (W.timeIntegral_hasDerivAt_right u 0 (t + b)).scomp t
    ((hasDerivAt_id t).add_const b)
  have ha := (W.timeIntegral_hasDerivAt_right u 0 (t + a)).scomp t
    ((hasDerivAt_id t).add_const a)
  have he : (fun s => W.timeIntegral (s + a) (s + b) u) =
      (fun s => W.timeIntegral 0 (s + b) u - W.timeIntegral 0 (s + a) u) := by
    funext s
    exact (intervalIntegral.integral_interval_sub_left
      (W.intervalIntegrable u 0 (s + b)) (W.intervalIntegrable u 0 (s + a))).symm
  rw [he]
  convert hb.sub ha using 1 <;> simp only [Function.comp_def, one_smul, id_eq, Pi.sub_def]

lemma negativeAverage_generator (T : ℝ) (u : H) :
    W.HasGenerator (W.negativeAverage T u) ((T⁻¹ : ℝ) • (u - W.act (-T) u)) := by
  apply W.hasGenerator_of_hasDerivAt
  intro t
  have he : (fun s => W.act s (W.negativeAverage T u)) =
      (fun s => (T⁻¹ : ℝ) • W.timeIntegral (s + -T) (s + 0) u) := by
    funext s
    change (W.act s).toLinearMap ((T⁻¹ : ℝ) • W.timeIntegral (-T) 0 u) = _
    rw [LinearMap.map_smul_of_tower]
    change (T⁻¹ : ℝ) • W.act s (W.timeIntegral (-T) 0 u) = _
    rw [W.timeIntegral_translate]
  rw [he]
  have hd := (W.timeIntegral_hasDerivAt_translate u (-T) 0 t).const_smul (T⁻¹ : ℝ)
  have hv : W.act t ((T⁻¹ : ℝ) • (u - W.act (-T) u)) =
      (T⁻¹ : ℝ) • (W.act (t + 0) u - W.act (t + -T) u) := by
    change (W.act t).toLinearMap ((T⁻¹ : ℝ) • (u - W.act (-T) u)) = _
    rw [LinearMap.map_smul_of_tower]
    change (T⁻¹ : ℝ) • W.act t (u - W.act (-T) u) = _
    rw [map_sub, ← W.add, add_zero]
  rw [hv]
  exact hd

omit [CompleteSpace H] in
lemma negativeAverage_generator_norm {T : ℝ} (hT : 0 < T) (u : H) :
    ‖(T⁻¹ : ℝ) • (u - W.act (-T) u)‖ ≤ 2 * ‖u‖ / T := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hT)]
  calc
    T⁻¹ * ‖u - W.act (-T) u‖ ≤ T⁻¹ * (‖u‖ + ‖W.act (-T) u‖) := by
      gcongr
      exact norm_sub_le _ _
    _ = 2 * ‖u‖ / T := by rw [(W.act (-T)).norm_map]; ring

lemma negativeAverage_invariant {u : H} (hu : ∀ t, W.act t u = u) {T : ℝ} (hT : T ≠ 0) :
    W.negativeAverage T u = u := by
  change (T⁻¹ : ℝ) • (∫ t in -T..0, W.act t u) = u
  simp_rw [hu]
  rw [intervalIntegral.integral_const, ← smul_assoc]
  simp only [sub_neg_eq_add, zero_add, smul_eq_mul, inv_mul_cancel₀ hT, one_smul]

lemma negativeAverage_dist_invariant {u : H} (hu : ∀ t, W.act t u = u)
    {T : ℝ} (hT : 0 < T) (a : H) :
    ‖W.negativeAverage T a - u‖ ≤ ‖a - u‖ := by
  calc
    ‖W.negativeAverage T a - u‖ = ‖W.negativeAverage T (a - u)‖ := by
      rw [map_sub, W.negativeAverage_invariant hu hT.ne']
    _ ≤ ‖a - u‖ := by
      exact W.negativeAverage_norm_le hT (a - u)

end HilbertFlow
end TriangularBilliards.Analysis

end
end
end
end
end

end OAI
end
end

section
section
namespace OAI


open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section

namespace TriangularBilliards
open Analysis
open scoped Topology

abbrev DoubleL2 (Q : Triangle) := Lp ℂ 2 (doubleMeasure Q)

/-- The actual unitary geodesic dynamics on the oriented double. -/
def geodesicHilbertFlow (Q : Triangle) : HilbertFlow (DoubleL2 Q) where
  act := koopman (doubleFlow Q) (measurePreserving_doubleFlow Q)
  zero u := by
    apply Lp.ext
    filter_upwards [coe_koopman (doubleFlow Q) (measurePreserving_doubleFlow Q) 0 u] with z hz
    simpa only [doubleFlow_zero] using hz
  add s t u := by
    apply Lp.ext
    have h₁ := coe_koopman (doubleFlow Q) (measurePreserving_doubleFlow Q) (s + t) u
    have h₂ := coe_koopman (doubleFlow Q) (measurePreserving_doubleFlow Q) s
      (koopman (doubleFlow Q) (measurePreserving_doubleFlow Q) t u)
    have h₃ := (measurePreserving_doubleFlow Q s).quasiMeasurePreserving.ae
      (coe_koopman (doubleFlow Q) (measurePreserving_doubleFlow Q) t u)
    have hc := doubleFlow_cocycle Q t s
    rw [add_comm t s] at hc
    filter_upwards [h₁, h₂, h₃, hc] with z h1 h2 h3 h4
    rw [h1, h2, h3, h4]
    rfl
  continuous u :=
    (continuous_koopman (doubleFlow Q) (measurePreserving_doubleFlow Q)
      (ae_continuousAt_doubleFlow Q)).comp (continuous_id.prodMk continuous_const)

lemma geodesic_koopman_ae (Q : Triangle) (t : ℝ) (u : DoubleL2 Q) :
    (geodesicHilbertFlow Q).act t u =ᵐ[doubleMeasure Q] (fun z => u (doubleFlow Q t z)) :=
  coe_koopman (doubleFlow Q) (measurePreserving_doubleFlow Q) t u

/-- Pullback from the billiard phase space preserves L² exactly. -/
def doubleLift (Q : Triangle) : Lp ℂ 2 (phaseMeasure Q) →ₗᵢ[ℂ] DoubleL2 Q :=
  Lp.compMeasurePreservingₗᵢ ℂ Prod.fst
    (by simpa only [doubleMeasure] using
      (measurePreserving_fst (μ := phaseMeasure Q) (ν := parityMeasure)))

lemma doubleLift_ae (Q : Triangle) (f : Lp ℂ 2 (phaseMeasure Q)) :
    (doubleLift Q f : DoublePhase → ℂ) =ᵐ[doubleMeasure Q] (fun z => f z.1) :=
  Lp.coeFn_compMeasurePreserving _ _

lemma doubleLift_invariant (Q : Triangle) (f : Lp ℂ 2 (phaseMeasure Q))
    (hf : ∀ t, (fun z => f (billiardFlow Q t z)) =ᵐ[phaseMeasure Q] f) :
    ∀ t, (geodesicHilbertFlow Q).act t (doubleLift Q f) = doubleLift Q f := by
  intro t
  apply Lp.ext
  have h₁ := geodesic_koopman_ae Q t (doubleLift Q f)
  have h₂ := (measurePreserving_doubleFlow Q t).quasiMeasurePreserving.ae (doubleLift_ae Q f)
  have h₃ : ∀ᵐ z ∂doubleMeasure Q, f (billiardFlow Q t z.1) = f z.1 :=
    Measure.quasiMeasurePreserving_fst.ae (hf t)
  filter_upwards [h₁, h₂, h₃, doubleLift_ae Q f] with z h1 h2 h3 h4
  rw [h1, h2, h4]
  exact h3

end TriangularBilliards

namespace TriangularBilliards
open Analysis
open scoped Topology

lemma continuous_doubleRotate_angle (z : DoublePhase) :
    Continuous (fun θ : ℝ => doubleRotate (Circle.exp θ) z) := by
  by_cases hz : z.2 = 0
  · simp only [doubleRotate, hz, ite_true]
    fun_prop
  · simp only [doubleRotate, hz, ite_false]
    fun_prop

lemma ae_continuousAt_doubleRotate_angle (Q : Triangle) (t : ℝ) :
    ∀ᵐ z ∂doubleMeasure Q, ContinuousAt (fun θ : ℝ => doubleRotate (Circle.exp θ) z) t :=
  Filter.Eventually.of_forall fun z => (continuous_doubleRotate_angle z).continuousAt

lemma continuous_angular_koopman (Q : Triangle) (u : DoubleL2 Q) :
    Continuous (fun θ : ℝ => koopman (fun θ => doubleRotate (Circle.exp θ))
      (fun θ => measurePreserving_doubleRotate Q (Circle.exp θ)) θ u) :=
  continuous_koopman_time (fun θ => doubleRotate (Circle.exp θ))
    (fun θ => measurePreserving_doubleRotate Q (Circle.exp θ))
    (ae_continuousAt_doubleRotate_angle Q) u

/-- Rotation of the oriented tangent fiber, not a rotation of the physical
velocity with the same sign on both copies. -/
def angularHilbertFlow (Q : Triangle) : HilbertFlow (DoubleL2 Q) where
  act := koopman (fun θ => doubleRotate (Circle.exp θ))
    (fun θ => measurePreserving_doubleRotate Q (Circle.exp θ))
  zero u := by
    apply Lp.ext
    filter_upwards [coe_koopman (fun θ => doubleRotate (Circle.exp θ))
      (fun θ => measurePreserving_doubleRotate Q (Circle.exp θ)) 0 u] with z hz
    simpa only [Circle.exp_zero, doubleRotate_one] using hz
  add s t u := by
    apply Lp.ext
    let R := fun θ => doubleRotate (Circle.exp θ)
    let hm := fun θ => measurePreserving_doubleRotate Q (Circle.exp θ)
    have h₁ := coe_koopman R hm (s + t) u
    have h₂ := coe_koopman R hm s (koopman R hm t u)
    have h₃ := (hm s).quasiMeasurePreserving.ae (coe_koopman R hm t u)
    filter_upwards [h₁, h₂, h₃] with z h1 h2 h3
    rw [h1, h2, h3]
    change u (doubleRotate (Circle.exp (s + t)) z) =
      u (doubleRotate (Circle.exp t) (doubleRotate (Circle.exp s) z))
    rw [← doubleRotate_mul, ← Circle.exp_add, add_comm s t]
  continuous := continuous_angular_koopman Q

/-- The transverse geodesic flow is actual geodesic motion after a quarter
turn and restoration of the direction, with no global commutation assumed. -/
def transverseHilbertFlow (Q : Triangle) : HilbertFlow (DoubleL2 Q) :=
  (geodesicHilbertFlow Q).conjugate (angularHilbertFlow Q) (Real.pi / 2)

end TriangularBilliards

namespace TriangularBilliards
open Filter
open scoped Topology ContDiff NNReal

/-- Seam gluing in the two planar sheets: reflection of base and velocity
changes the sheet. This is a local equality, not an assumption of transport
invariance or of an analytic estimate. -/
def SeamCompatible (Q : Triangle) (f : DoublePhase → ℂ) : Prop :=
  ∀ (i : Fin 3) (x : ℂ), x ∈ Q.side i → ∀ (v : Circle) (b : ZMod 2),
    ∀ᶠ y in 𝓝 x, f ((wallReflection Q i y, reflectedDirection Q i v), b + 1) = f ((y, v), b)

/-- Horizontal derivative in the actual unit velocity direction. -/
def xDerivative (f : DoublePhase → ℂ) (z : DoublePhase) : ℂ :=
  fderiv ℝ (fun x => f ((x, z.1.2), z.2)) z.1.1 (z.1.2 : ℂ)

lemma wallReflection_add_smul (Q : Triangle) (i : Fin 3) (x v : ℂ) (t : ℝ) :
    wallReflection Q i (x + t • v) = wallReflection Q i x + t • reflect (Q.tangent i) v := by
  have h := wallReflection_sub Q i (x + t • v) x
  rw [add_sub_cancel_left, reflect_real_smul] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

lemma FlightChain.reflected_direction_previous {Q : Triangle} {z : Phase}
    (c : FlightChain Q z) (n : ℤ) :
    reflectedDirection Q (c.wall n) (c.direction n) = c.direction (n - 1) := by
  apply Subtype.ext
  change reflect (Q.tangent (c.wall n)) (c.direction n : ℂ) = _
  rw [c.specular n, reflect_involutive (Q.tangent_ne_zero _)]

lemma FlightChain.reflected_outgoing_line {Q : Triangle} {z : Phase}
    (c : FlightChain Q z) (n : ℤ) (s : ℝ) :
    wallReflection Q (c.wall n) (c.point n + (s - c.time n) • (c.direction n : ℂ)) =
      c.point (n - 1) + (s - c.time (n - 1)) • (c.direction (n - 1) : ℂ) := by
  rw [wallReflection_add_smul, wallReflection_fixed_side Q (c.on_side n),
    c.specular n, reflect_involutive (Q.tangent_ne_zero _), c.previous_line]

/-- A seam-compatible field has one smooth planar formula through each
collision. Thus no trace at a vertex and no angular regularity is needed
for the ordinary one-variable calculus along a nonsingular orbit. -/
lemma seam_orbit_eventually_line {Q : Triangle} {z : DoublePhase}
    (c : FlightChain Q z.1) {f : DoublePhase → ℂ} (hf : SeamCompatible Q f)
    (t : ℝ) :
    ∃ n : ℤ, c.time n ≤ t ∧ t < c.time (n + 1) ∧
      (fun s => f (doubleFlow Q s z)) =ᶠ[𝓝 t]
        (fun s => f ((c.point n + (s - c.time n) • (c.direction n : ℂ), c.direction n),
          (n : ZMod 2) + z.2)) := by
  let n := collisionIndex Q t z.1
  have hn := collisionIndex_spec c t
  refine ⟨n, hn.1, hn.2, ?_⟩
  by_cases he : c.time n = t
  · let p : ℝ → ℂ := fun s => c.point n + (s - c.time n) • (c.direction n : ℂ)
    have hp : Tendsto p (𝓝 t) (𝓝 (c.point n)) := by
      have hc : Continuous p := by fun_prop
      simpa only [ContinuousAt, p, ← he, sub_self, zero_smul, add_zero] using hc.continuousAt (x := t)
    have hs := hp.eventually (hf (c.wall n) (c.point n) (c.on_side n)
      (c.direction n) ((n : ZMod 2) + z.2))
    have hi : Ioo (c.time (n - 1)) (c.time (n + 1)) ∈ 𝓝 t := by
      rw [← he]
      exact isOpen_Ioo.mem_nhds ⟨c.increasing (by omega), c.increasing (by omega)⟩
    filter_upwards [hs, hi] with s hs hi
    by_cases hsn : c.time n ≤ s
    · rw [doubleFlow_on_flight c ⟨hsn, hi.2⟩]
    · have hprev : c.time (n - 1) ≤ s ∧ s < c.time ((n - 1) + 1) :=
        ⟨hi.1.le, by simpa only [sub_add_cancel] using lt_of_not_ge hsn⟩
      rw [doubleFlow_on_flight c hprev]
      have hb : ((n : ZMod 2) + z.2) + 1 = ((n - 1 : ℤ) : ZMod 2) + z.2 := by
        push_cast
        have h2 : (1 : ZMod 2) + 1 = 0 := by decide
        linear_combination h2
      simpa only [p, c.reflected_outgoing_line, c.reflected_direction_previous, hb] using hs
  · have hi : Ioo (c.time n) (c.time (n + 1)) ∈ 𝓝 t :=
      isOpen_Ioo.mem_nhds ⟨lt_of_le_of_ne hn.1 he, hn.2⟩
    filter_upwards [hi] with s hs
    rw [doubleFlow_on_flight c ⟨hs.1.le, hs.2⟩]

lemma seam_orbit_hasDerivAt {Q : Triangle} {z : DoublePhase}
    (c : FlightChain Q z.1) {f : DoublePhase → ℂ} (hf : SeamCompatible Q f)
    (hd : ∀ v b, Differentiable ℝ (fun x => f ((x, v), b))) (t : ℝ) :
    HasDerivAt (fun s => f (doubleFlow Q s z)) (xDerivative f (doubleFlow Q t z)) t := by
  obtain ⟨n, hn₀, hn₁, he⟩ := seam_orbit_eventually_line c hf t
  have hp : HasDerivAt (fun s => c.point n + (s - c.time n) • (c.direction n : ℂ))
      (c.direction n : ℂ) t := by
    simpa only [one_smul, id_eq] using (((hasDerivAt_id t).sub_const (c.time n)).smul_const
      (c.direction n : ℂ)).const_add (c.point n)
  have h := ((hd (c.direction n) ((n : ZMod 2) + z.2) _).hasFDerivAt).comp_hasDerivAt t hp
  have hx : xDerivative f (doubleFlow Q t z) =
      fderiv ℝ (fun x => f ((x, c.direction n), (n : ZMod 2) + z.2))
        (c.point n + (t - c.time n) • (c.direction n : ℂ)) (c.direction n : ℂ) := by
    rw [doubleFlow_on_flight c ⟨hn₀, hn₁⟩]
    rfl
  rw [hx]
  exact h.congr_of_eventuallyEq he

lemma seam_orbit_norm_deriv_le {Q : Triangle} {z : DoublePhase}
    (c : FlightChain Q z.1) {f : DoublePhase → ℂ} (hf : SeamCompatible Q f)
    (hd : ∀ v b, Differentiable ℝ (fun x => f ((x, v), b)))
    {C : ℝ} (hC : ∀ x v b, ‖fderiv ℝ (fun y => f ((y,v),b)) x‖ ≤ C) (t : ℝ) :
    ‖deriv (fun s => f (doubleFlow Q s z)) t‖ ≤ C := by
  rw [(seam_orbit_hasDerivAt c hf hd t).deriv]
  unfold xDerivative
  apply (ContinuousLinearMap.le_opNorm _ _).trans
  rw [Circle.norm_coe, mul_one]
  exact hC _ _ _

lemma seam_orbit_lipschitz {Q : Triangle} {z : DoublePhase}
    (c : FlightChain Q z.1) {f : DoublePhase → ℂ} (hf : SeamCompatible Q f)
    (hd : ∀ v b, Differentiable ℝ (fun x => f ((x, v), b)))
    {C : ℝ≥0} (hC : ∀ x v b, ‖fderiv ℝ (fun y => f ((y,v),b)) x‖ ≤ C) :
    LipschitzWith C (fun t => f (doubleFlow Q t z)) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (seam_orbit_hasDerivAt c hf hd t).differentiableAt)
  intro t
  exact_mod_cast seam_orbit_norm_deriv_le c hf hd hC t

end TriangularBilliards

namespace TriangularBilliards.Analysis
open Filter
open scoped Topology NNReal

variable {A : Type uA} [MeasurableSpace A] {μ : Measure A} [IsFiniteMeasure μ]

/-- Dominated passage from pointwise orbit derivatives to an actual L²
strong derivative. A uniform Lipschitz bound is supplied by the genuine
seam-glued spatial calculus; no generator identity is assumed. -/
lemma koopman_hasDerivAt_zero
    (F : ℝ → A → A) (hm : ∀ t, MeasurePreserving (F t) μ μ)
    (hzero : ∀ x, F 0 x = x)
    {f g : A → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    {C : ℝ≥0}
    (hd : ∀ᵐ x ∂μ, HasDerivAt (fun t => f (F t x)) (g x) 0)
    (hbound : ∀ᵐ x ∂μ, LipschitzWith C (fun t => f (F t x)))
    (hgC : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) :
    HasDerivAt (fun t => koopman F hm t (hf.toLp f)) (hg.toLp g) 0 := by
  let u := hf.toLp f
  let v := hg.toLp g
  have hu : (u : A → ℂ) =ᵐ[μ] f := hf.coeFn_toLp
  have hv : (v : A → ℂ) =ᵐ[μ] g := hg.coeFn_toLp
  have huf (t : ℝ) : (koopman F hm t u : A → ℂ) =ᵐ[μ] (fun x => f (F t x)) :=
    (coe_koopman F hm t u).trans ((hm t).quasiMeasurePreserving.ae hu)
  have he0 : koopman F hm 0 u = u := by
    apply Lp.ext
    exact (huf 0).trans (by simpa only [hzero] using hu.symm)
  let q : ℝ → A → ℂ := fun t x => t⁻¹ • (f (F t x) - f x) - g x
  have hq (t : ℝ) : AEStronglyMeasurable (q t) μ :=
    (((hf.aestronglyMeasurable.comp_measurePreserving (hm t)).sub hf.aestronglyMeasurable).const_smul
      (t⁻¹ : ℝ)).sub hg.aestronglyMeasurable
  have he (t : ℝ) : ‖t⁻¹ • (koopman F hm t u - u) - v‖ ^ 2 = ∫ x, ‖q t x‖ ^ 2 ∂μ := by
    rw [norm_sq_L2]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((t⁻¹ : ℝ) • (koopman F hm t u - u)) v,
      Lp.coeFn_smul (t⁻¹ : ℝ) (koopman F hm t u - u),
      Lp.coeFn_sub (koopman F hm t u) u, huf t, hu, hv] with x ha hb hc hft hfu hgv
    simp only [ha, hb, hc, Pi.sub_apply, Pi.smul_apply, hft, hfu, hgv, q]
  have hi : Tendsto (fun t : ℝ => ∫ x, ‖q t x‖ ^ 2 ∂μ) (𝓝[≠] 0) (𝓝 0) := by
    have hh : Tendsto (fun t : ℝ => ∫ x, ‖q t x‖ ^ 2 ∂μ) (𝓝[≠] 0)
        (𝓝 (∫ _x : A, (0 : ℝ) ∂μ)) := by
      apply tendsto_integral_filter_of_norm_le_const
      · exact Eventually.of_forall fun t => (hq t).norm.pow 2
      · refine ⟨(2 * (C : ℝ)) ^ 2, Eventually.of_forall fun t => ?_⟩
        filter_upwards [hbound, hgC] with x hx hgx
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        apply pow_le_pow_left₀ (norm_nonneg _) _ 2
        have hdiff : ‖(t⁻¹ : ℝ) • (f (F t x) - f x)‖ ≤ C := by
          by_cases ht : t = 0
          · simp only [ht, inv_zero, zero_smul, norm_zero, NNReal.coe_nonneg]
          rw [norm_smul, norm_inv]
          have hh := hx.norm_sub_le t 0
          rw [hzero, sub_zero] at hh
          calc
            _ ≤ ‖t‖⁻¹ * ((C : ℝ) * ‖t‖) := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (norm_nonneg _))
            _ = C := by field_simp
        calc
          ‖q t x‖ ≤ ‖(t⁻¹ : ℝ) • (f (F t x) - f x)‖ + ‖g x‖ := norm_sub_le _ _
          _ ≤ 2 * (C : ℝ) := by linarith
      · filter_upwards [hd] with x hx
        have hh := hx.tendsto_slope_zero
        simp only [zero_add, hzero] at hh
        have hl := ((hh.sub_const (g x)).norm.pow 2)
        simpa only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, q]
          using hl
    simpa only [integral_zero] using hh
  have hn : Tendsto (fun t => ‖t⁻¹ • (koopman F hm t u - u) - v‖) (𝓝[≠] 0) (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hi
    simpa only [Function.comp_def, ← he, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
      Real.sqrt_zero] using h
  change HasDerivAt (fun t => koopman F hm t u) v 0
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simpa only [zero_add, he0] using tendsto_iff_norm_sub_tendsto_zero.mpr hn

end TriangularBilliards.Analysis

end
end
end
end
end

end OAI
end
end

section
section
namespace OAI


open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section

namespace TriangularBilliards.Analysis.HilbertFlow
open Filter
open scoped Topology
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (W : HilbertFlow H)

/-- A genuine strong derivative at zero determines the entire closed
unitary generator; the group law transports it to every time. -/
lemma hasGenerator_of_hasDerivAt_zero {u v : H}
    (h : HasDerivAt (fun t => W.act t u) v 0) : W.HasGenerator u v := by
  apply W.hasGenerator_of_hasDerivAt
  intro t
  have hs : HasDerivAt (fun s => W.act (s - t) u) v t := by
    have h0 : HasDerivAt (fun s => W.act s u) v (id t - t) := by simpa using h
    have hh := h0.scomp (h := fun s : ℝ => s - t) t ((hasDerivAt_id t).sub_const t)
    simpa only [Function.comp_def, id_eq, sub_self, one_smul] using hh
  have hh := ((W.act t).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hs
  apply hh.congr_of_eventuallyEq
  filter_upwards [] with s
  change W.act s u = W.act t (W.act (s - t) u)
  rw [← W.add, show t + (s - t) = s by ring]

end TriangularBilliards.Analysis.HilbertFlow

namespace TriangularBilliards
open Analysis
open scoped NNReal

/-- The spatial derivative of a smooth seam field is the actual strong
Koopman generator, including trajectories with arbitrarily many reflections.
The asserted generator is proved, not added as a hypothetical analytic input. -/
lemma seam_geodesic_generator {Q : Triangle} {f : DoublePhase → ℂ}
    (hs : SeamCompatible Q f)
    (hd : ∀ v b, Differentiable ℝ (fun x => f ((x, v), b)))
    {C : ℝ≥0} (hC : ∀ x v b, ‖fderiv ℝ (fun y => f ((y,v),b)) x‖ ≤ C)
    (hf : MemLp f 2 (doubleMeasure Q))
    (hxf : MemLp (xDerivative f) 2 (doubleMeasure Q)) :
    (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) (hxf.toLp (xDerivative f)) := by
  apply (geodesicHilbertFlow Q).hasGenerator_of_hasDerivAt_zero
  apply koopman_hasDerivAt_zero (doubleFlow Q) (measurePreserving_doubleFlow Q)
    (doubleFlow_zero Q) hf hxf
  · filter_upwards [(measurePreserving_fst (μ := phaseMeasure Q) (ν := parityMeasure)).quasiMeasurePreserving.ae
      (ae_regularAt Q 0)] with z hz
    obtain ⟨c⟩ := hz.1
    simpa only [doubleFlow_zero] using seam_orbit_hasDerivAt c hs hd 0
  · filter_upwards [(measurePreserving_fst (μ := phaseMeasure Q) (ν := parityMeasure)).quasiMeasurePreserving.ae
      (ae_regularAt Q 0)] with z hz
    obtain ⟨c⟩ := hz.1
    exact seam_orbit_lipschitz c hs hd hC
  · exact Filter.Eventually.of_forall fun z => by
      calc
        ‖xDerivative f z‖ ≤ ‖fderiv ℝ (fun y => f ((y,z.1.2),z.2)) z.1.1‖ * ‖(z.1.2 : ℂ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ C := by rw [Circle.norm_coe, mul_one]; exact hC _ _ _

end TriangularBilliards

namespace TriangularBilliards
open Filter Analysis
open scoped Topology ContDiff

lemma parity_add_one_ne_zero_iff (b : ZMod 2) : b + 1 = 0 ↔ b ≠ 0 := by
  exact (show ∀ c : ZMod 2, c + 1 = 0 ↔ c ≠ 0 by decide) b

lemma reflectedDirection_mul (Q : Triangle) (i : Fin 3) (a v : Circle) :
    reflectedDirection Q i (a * v) = a⁻¹ * reflectedDirection Q i v := by
  apply Subtype.ext
  change reflect (Q.tangent i) ((a : ℂ) * (v : ℂ)) =
    (a⁻¹ : Circle) * reflect (Q.tangent i) (v : ℂ)
  rw [Circle.coe_inv_eq_conj]
  simp only [reflect, star_mul', Complex.star_def]
  ring

lemma doubleRotate_seam (Q : Triangle) (i : Fin 3) (a : Circle)
    (x : ℂ) (v : Circle) (b : ZMod 2) :
    doubleRotate a ((wallReflection Q i x, reflectedDirection Q i v), b + 1) =
      ((wallReflection Q i x, reflectedDirection Q i
        ((if b = 0 then a else a⁻¹) * v)), b + 1) := by
  simp only [doubleRotate, reflectedDirection_mul]
  by_cases hb : b = 0
  · simp [hb]
  · simp [hb, (parity_add_one_ne_zero_iff b).mpr hb]

lemma SeamCompatible.rotate {Q : Triangle} {f : DoublePhase → ℂ}
    (hf : SeamCompatible Q f) (a : Circle) : SeamCompatible Q (f ∘ doubleRotate a) := by
  intro i x hx v b
  filter_upwards [hf i x hx ((if b = 0 then a else a⁻¹) * v) b] with y hy
  change f (doubleRotate a ((wallReflection Q i y, reflectedDirection Q i v), b+1)) =
    f (doubleRotate a ((y,v),b))
  rw [doubleRotate_seam]
  exact hy

lemma wallReflection_hasFDerivAt (Q : Triangle) (i : Fin 3) (x : ℂ) :
    HasFDerivAt (wallReflection Q i)
      (reflectIsometry (Q.tangent i) (Q.tangent_ne_zero i)).toContinuousLinearEquiv.toContinuousLinearMap x := by
  let L : ℂ →L[ℝ] ℂ := (reflectIsometry (Q.tangent i)
    (Q.tangent_ne_zero i)).toContinuousLinearEquiv.toContinuousLinearMap
  have hL : HasFDerivAt (fun y : ℂ => L (y - Q.vertex i)) L x := by
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
      L.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const (Q.vertex i))
  exact hL.const_add (Q.vertex i)

lemma SeamCompatible.xDerivative {Q : Triangle} {f : DoublePhase → ℂ}
    (hf : SeamCompatible Q f)
    (hd : ∀ v b, Differentiable ℝ (fun x => f ((x,v),b))) :
    SeamCompatible Q (xDerivative f) := by
  intro i x hx v b
  have he0 : (fun y => f ((wallReflection Q i y, reflectedDirection Q i v),b+1)) =ᶠ[𝓝 x]
      (fun y => f ((y,v),b)) := hf i x hx v b
  have he := he0.fderiv (𝕜 := ℝ)
  filter_upwards [he] with y hy
  have hchain := ((hd (reflectedDirection Q i v) (b+1) (wallReflection Q i y)).hasFDerivAt).comp y
    (wallReflection_hasFDerivAt Q i y)
  have ht := congrArg (fun L : ℂ →L[ℝ] ℂ => L (v : ℂ)) (hchain.fderiv.symm.trans hy)
  exact ht

/-- Spatial smoothness does not require angular differentiability. -/
lemma xDerivative_contDiff {f : DoublePhase → ℂ}
    (hf : ∀ v b, ContDiff ℝ ∞ (fun x => f ((x,v),b))) (v : Circle) (b : ZMod 2) :
    ContDiff ℝ ∞ (fun x => xDerivative f ((x,v),b)) := by
  change ContDiff ℝ ∞ (fun x => fderiv ℝ (fun y => f ((y,v),b)) x _)
  exact ((hf v b).fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_const (c := (v : ℂ)))

/-- The transverse velocity in the oriented sheet. -/
def transverseVelocity (v : Circle) (b : ZMod 2) : ℂ :=
  (if b = 0 then Complex.I else -Complex.I) * (v : ℂ)

def yDerivative (f : DoublePhase → ℂ) (z : DoublePhase) : ℂ :=
  fderiv ℝ (fun x => f ((x,z.1.2),z.2)) z.1.1 (transverseVelocity z.1.2 z.2)

lemma yDerivative_contDiff {f : DoublePhase → ℂ}
    (hf : ∀ v b, ContDiff ℝ ∞ (fun x => f ((x,v),b))) (v : Circle) (b : ZMod 2) :
    ContDiff ℝ ∞ (fun x => yDerivative f ((x,v),b)) := by
  change ContDiff ℝ ∞ (fun x => fderiv ℝ (fun y => f ((y,v),b)) x (transverseVelocity v b))
  exact ((hf v b).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma reflect_transverseVelocity (Q : Triangle) (i : Fin 3) (v : Circle) (b : ZMod 2) :
    reflect (Q.tangent i) (transverseVelocity v b) =
      transverseVelocity (reflectedDirection Q i v) (b + 1) := by
  have hneg (e u : ℂ) : reflect e (-u) = -reflect e u := by simp [reflect]
  have hI (e u : ℂ) : reflect e (Complex.I * u) = -Complex.I * reflect e u := by
    simp only [reflect, star_mul', Complex.star_def, Complex.conj_I]; ring
  by_cases hb : b = 0
  · simp only [transverseVelocity, hb, ite_eq_left, zero_add]
    simp only [one_ne_zero, ite_false]
    exact hI _ _
  · simp only [transverseVelocity, hb, ite_false, (parity_add_one_ne_zero_iff b).mpr hb, ite_eq_left]
    change reflect (Q.tangent i) (-Complex.I * (v : ℂ)) =
      Complex.I * reflect (Q.tangent i) (v : ℂ)
    rw [neg_mul, hneg, hI, ← neg_mul, neg_neg]

lemma SeamCompatible.yDerivative {Q : Triangle} {f : DoublePhase → ℂ}
    (hf : SeamCompatible Q f)
    (hd : ∀ v b, Differentiable ℝ (fun x => f ((x,v),b))) :
    SeamCompatible Q (yDerivative f) := by
  intro i x hx v b
  have he0 : (fun y => f ((wallReflection Q i y, reflectedDirection Q i v),b+1)) =ᶠ[𝓝 x]
      (fun y => f ((y,v),b)) := hf i x hx v b
  have he := he0.fderiv (𝕜 := ℝ)
  filter_upwards [he] with y hy
  have hchain := ((hd (reflectedDirection Q i v) (b+1) (wallReflection Q i y)).hasFDerivAt).comp y
    (wallReflection_hasFDerivAt Q i y)
  have ht := congrArg (fun L : ℂ →L[ℝ] ℂ => L (transverseVelocity v b)) (hchain.fderiv.symm.trans hy)
  change fderiv ℝ (fun x => f ((x,reflectedDirection Q i v),b+1)) (wallReflection Q i y)
    (reflect (Q.tangent i) (transverseVelocity v b)) = _ at ht
  rw [reflect_transverseVelocity] at ht
  exact ht

lemma x_y_commute {f : DoublePhase → ℂ}
    (hf : ∀ v b, ContDiff ℝ ∞ (fun x => f ((x,v),b))) (z : DoublePhase) :
    xDerivative (yDerivative f) z = yDerivative (xDerivative f) z := by
  have hd := ((hf z.1.2 z.2).fderiv_right (m := ∞) (by simp)).differentiable (by simp) z.1.1
  simp only [xDerivative, yDerivative]
  rw [fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd (differentiableAt_const _)]
  simp
  exact ((hf z.1.2 z.2).contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)).eq _ _

end TriangularBilliards

namespace TriangularBilliards.Analysis.HilbertFlow
open scoped Topology
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma HasGenerator.conjugate {W V : HilbertFlow H} {θ : ℝ} {u v : H}
    (h : W.HasGenerator (V.act (-θ) u) (V.act (-θ) v)) :
    (W.conjugate V θ).HasGenerator u v := by
  apply (W.conjugate V θ).hasGenerator_of_hasDerivAt_zero
  have hd := ((V.act θ).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (HasGenerator.hasDerivAt W h 0)
  change HasDerivAt (fun t => V.act θ (W.act t (V.act (-θ) u)))
    (V.act θ (W.act 0 (V.act (-θ) v))) 0 at hd
  rw [W.zero, ← V.add, add_neg_cancel, V.zero] at hd
  exact hd

lemma commuting_generators_inner {X Y : HilbertFlow H} {u a b c : H}
    (hxu : X.HasGenerator u a) (hyu : Y.HasGenerator u b)
    (hxy : X.HasGenerator b c) (hyx : Y.HasGenerator a c) :
    inner ℂ a b = inner ℂ b a := by
  have hx := X.generator_skew hxu hxy
  have hy := Y.generator_skew hyu hyx
  linear_combination hx - hy

lemma commuting_generators_CR {X Y : HilbertFlow H} {u a b c : H}
    (hxu : X.HasGenerator u a) (hyu : Y.HasGenerator u b)
    (hxy : X.HasGenerator b c) (hyx : Y.HasGenerator a c) :
    ‖a + Complex.I • b‖ = ‖a - Complex.I • b‖ := by
  have hi := congrArg Complex.im (commuting_generators_inner hxu hyu hxy hyx)
  have hs := inner_conj_symm (𝕜 := ℂ) a b
  have hsi := congrArg Complex.im hs
  have him : (inner ℂ a b).im = 0 := by simp only [Complex.conj_im] at hsi; linarith
  have hr : (inner ℂ a (Complex.I • b)).re = 0 := by
    rw [inner_smul_right]
    simp [Complex.mul_re, him]
  have he : ‖a + Complex.I • b‖ ^ 2 = ‖a - Complex.I • b‖ ^ 2 := by
    rw [@norm_add_sq ℂ, @norm_sub_sq ℂ]
    change _ + 2 * (inner ℂ a (Complex.I • b)).re + _ =
      _ - 2 * (inner ℂ a (Complex.I • b)).re + _
    rw [hr]; ring
  nlinarith [norm_nonneg (a + Complex.I • b), norm_nonneg (a - Complex.I • b)]

end TriangularBilliards.Analysis.HilbertFlow

namespace TriangularBilliards
open Analysis
open scoped Topology NNReal

lemma circle_exp_quarter_coe : (Circle.exp (Real.pi / 2) : ℂ) = Complex.I := by
  rw [Circle.coe_exp]
  push_cast
  exact Complex.exp_pi_div_two_mul_I

lemma transverseVelocity_neg_quarter (v : Circle) (b : ZMod 2) :
    transverseVelocity ((doubleRotate (Circle.exp (-(Real.pi / 2))) ((0,v),b)).1.2) b = (v : ℂ) := by
  by_cases hb : b = 0
  · simp only [doubleRotate, hb, ite_eq_left, transverseVelocity, Circle.exp_neg,
      Circle.coe_mul, Circle.coe_inv_eq_conj, circle_exp_quarter_coe, Complex.conj_I]
    ring_nf
    simp
  · simp only [doubleRotate, hb, ite_false, transverseVelocity, Circle.exp_neg,
      inv_inv, Circle.coe_mul, circle_exp_quarter_coe]
    ring_nf
    simp

lemma xDerivative_rotate_neg_quarter (f : DoublePhase → ℂ) (z : DoublePhase) :
    xDerivative (f ∘ doubleRotate (Circle.exp (-(Real.pi / 2)))) z =
      yDerivative f (doubleRotate (Circle.exp (-(Real.pi / 2))) z) := by
  exact congrArg (fun u : ℂ => fderiv ℝ
    (fun x => f ((x, (doubleRotate (Circle.exp (-(Real.pi / 2))) z).1.2), z.2))
      z.1.1 u) (transverseVelocity_neg_quarter z.1.2 z.2).symm

lemma angular_toLp (Q : Triangle) (θ : ℝ) {f : DoublePhase → ℂ}
    (hf : MemLp f 2 (doubleMeasure Q)) :
    (angularHilbertFlow Q).act θ (hf.toLp f) =
      (hf.comp_measurePreserving (measurePreserving_doubleRotate Q (Circle.exp θ))).toLp
        (f ∘ doubleRotate (Circle.exp θ)) := by
  exact Lp.toLp_compMeasurePreserving hf (measurePreserving_doubleRotate Q (Circle.exp θ))

lemma seam_transverse_generator {Q : Triangle} {f : DoublePhase → ℂ}
    (hs : SeamCompatible Q f)
    (hd : ∀ v b, Differentiable ℝ (fun x => f ((x, v), b)))
    {C : ℝ≥0} (hC : ∀ x v b, ‖fderiv ℝ (fun y => f ((y,v),b)) x‖ ≤ C)
    (hf : MemLp f 2 (doubleMeasure Q))
    (hyf : MemLp (yDerivative f) 2 (doubleMeasure Q)) :
    (transverseHilbertFlow Q).HasGenerator (hf.toLp f) (hyf.toLp (yDerivative f)) := by
  apply HilbertFlow.HasGenerator.conjugate
  rw [angular_toLp, angular_toLp]
  let a := Circle.exp (-(Real.pi / 2))
  have he : xDerivative (f ∘ doubleRotate a) = yDerivative f ∘ doubleRotate a :=
    funext (xDerivative_rotate_neg_quarter f)
  have hxy : MemLp (xDerivative (f ∘ doubleRotate a)) 2 (doubleMeasure Q) := by
    rw [he]
    exact hyf.comp_measurePreserving (measurePreserving_doubleRotate Q a)
  convert seam_geodesic_generator (hs.rotate a)
    (fun v b => hd ((if b = 0 then a else a⁻¹) * v) b)
    (fun x v b => hC x ((if b = 0 then a else a⁻¹) * v) b)
    (hf.comp_measurePreserving (measurePreserving_doubleRotate Q a)) hxy using 1
  apply Lp.ext
  filter_upwards [(hyf.comp_measurePreserving (measurePreserving_doubleRotate Q a)).coeFn_toLp,
    hxy.coeFn_toLp] with z hz hzz
  rw [hz, hzz]
  exact congrFun he.symm z

end TriangularBilliards

end
end
end
end
end

end OAI
end
end

section
section
namespace OAI

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section

namespace TriangularBilliards
open Analysis
open scoped NNReal ContDiff

/-- Global equal Cauchy--Riemann norms on the genuine smooth seam core.
The integration-by-parts step is supplied by the actual measure-preserving
geodesic/transverse generators and the proved pointwise Schwarz identity. -/
lemma seam_CR_norms {Q : Triangle} {f : DoublePhase → ℂ}
    (hs : SeamCompatible Q f)
    (hd : ∀ v b, ContDiff ℝ ∞ (fun x => f ((x,v),b)))
    {C Cx Cy : ℝ≥0}
    (hC : ∀ x v b, ‖fderiv ℝ (fun y => f ((y,v),b)) x‖ ≤ C)
    (hCx : ∀ x v b, ‖fderiv ℝ (fun y => xDerivative f ((y,v),b)) x‖ ≤ Cx)
    (hCy : ∀ x v b, ‖fderiv ℝ (fun y => yDerivative f ((y,v),b)) x‖ ≤ Cy)
    (hf : MemLp f 2 (doubleMeasure Q))
    (hxf : MemLp (xDerivative f) 2 (doubleMeasure Q))
    (hyf : MemLp (yDerivative f) 2 (doubleMeasure Q))
    (hxyf : MemLp (xDerivative (yDerivative f)) 2 (doubleMeasure Q)) :
    ‖hxf.toLp (xDerivative f) + Complex.I • hyf.toLp (yDerivative f)‖ =
      ‖hxf.toLp (xDerivative f) - Complex.I • hyf.toLp (yDerivative f)‖ := by
  have hd' := fun v b => (hd v b).differentiable (by simp)
  have he : xDerivative (yDerivative f) = yDerivative (xDerivative f) := funext (x_y_commute hd)
  have hyxf : MemLp (yDerivative (xDerivative f)) 2 (doubleMeasure Q) := by
    rwa [← he]
  have h₁ := seam_geodesic_generator hs hd' hC hf hxf
  have h₂ := seam_transverse_generator hs hd' hC hf hyf
  have h₃ := seam_geodesic_generator (hs.yDerivative hd')
    (fun v b => (yDerivative_contDiff hd v b).differentiable (by simp)) hCy hyf hxyf
  have h₄ := seam_transverse_generator (hs.xDerivative hd')
    (fun v b => (xDerivative_contDiff hd v b).differentiable (by simp)) hCx hxf hyxf
  have heLp : hxyf.toLp (xDerivative (yDerivative f)) = hyxf.toLp (yDerivative (xDerivative f)) :=
    MemLp.toLp_congr hxyf hyxf (Filter.Eventually.of_forall (congrFun he))
  rw [← heLp] at h₄
  exact HilbertFlow.commuting_generators_CR h₁ h₂ h₃ h₄

end TriangularBilliards

namespace TriangularBilliards
open Filter SpatialSmoothing
open scoped Topology ContDiff

lemma raw_eq_one_of_norm_le {x : ℂ} (hx : ‖x‖ ≤ (1/2 : ℝ)) : raw x = 1 := by
  apply (ContDiffBumpBase.ofInnerProductSpace ℂ).eq_one 2 (by norm_num)
  rw [norm_smul, Real.norm_ofNat]
  linarith

lemma raw_eq_zero_of_one_le_norm {x : ℂ} (hx : 1 ≤ ‖x‖) : raw x = 0 := by
  have h : x ∉ Function.support raw := by
    rw [raw_support, mem_ball_zero_iff]
    exact not_lt.mpr hx
  exact Function.notMem_support.mp h

/-- An explicit vertex cutoff, zero up to radius R and one outside radius
2R. Its transition annuli are those used in the localized energy bound. -/
def vertexCutoffFactor (Q : Triangle) (R : ℝ) (i : Fin 3) (x : ℂ) : ℝ :=
  1 - raw ((2 * R)⁻¹ • (x - Q.vertex i))

def vertexCutoff (Q : Triangle) (R : ℝ) (x : ℂ) : ℝ :=
  ∏ i : Fin 3, vertexCutoffFactor Q R i x

lemma vertexCutoffFactor_mem_Icc (Q : Triangle) (R : ℝ) (i : Fin 3) (x : ℂ) :
    vertexCutoffFactor Q R i x ∈ Icc (0 : ℝ) 1 := by
  exact ⟨sub_nonneg.mpr (raw_le_one _), sub_le_self _ (raw_nonneg _)⟩

lemma vertexCutoff_mem_Icc (Q : Triangle) (R : ℝ) (x : ℂ) :
    vertexCutoff Q R x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.prod_nonneg (fun i _ => (vertexCutoffFactor_mem_Icc Q R i x).1)
  · exact Finset.prod_le_one₀ (fun i _ => (vertexCutoffFactor_mem_Icc Q R i x).1)
      (fun i _ => (vertexCutoffFactor_mem_Icc Q R i x).2)

lemma vertexCutoffFactor_zero (Q : Triangle) {R : ℝ} (hR : 0 < R) (i : Fin 3) {x : ℂ}
    (hx : ‖x - Q.vertex i‖ ≤ R) : vertexCutoffFactor Q R i x = 0 := by
  unfold vertexCutoffFactor
  rw [raw_eq_one_of_norm_le, sub_self]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) hR))]
  calc
    (2 * R)⁻¹ * ‖x - Q.vertex i‖ ≤ (2 * R)⁻¹ * R := by gcongr
    _ = 1 / 2 := by field_simp

lemma vertexCutoffFactor_one (Q : Triangle) {R : ℝ} (hR : 0 < R) (i : Fin 3) {x : ℂ}
    (hx : 2 * R ≤ ‖x - Q.vertex i‖) : vertexCutoffFactor Q R i x = 1 := by
  unfold vertexCutoffFactor
  rw [raw_eq_zero_of_one_le_norm, sub_zero]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) hR))]
  calc
    1 = (2 * R)⁻¹ * (2 * R) := (inv_mul_cancel₀ (mul_ne_zero (by norm_num) hR.ne')).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr (mul_nonneg (by norm_num) hR.le))

lemma vertexCutoff_zero (Q : Triangle) {R : ℝ} (hR : 0 < R) {x : ℂ}
    (hx : Q.clearance x ≤ R) : vertexCutoff Q R x = 0 := by
  obtain ⟨v, hv, hd⟩ := (Set.finite_range Q.vertex).isCompact.exists_infDist_eq_dist
    (Set.range_nonempty Q.vertex) x
  obtain ⟨i, rfl⟩ := hv
  have hi : ‖x - Q.vertex i‖ ≤ R := by
    change Metric.infDist x (range Q.vertex) ≤ R at hx
    rw [hd, dist_eq_norm] at hx
    exact hx
  exact Finset.prod_eq_zero (Finset.mem_univ i) (vertexCutoffFactor_zero Q hR i hi)

lemma vertexCutoff_one (Q : Triangle) {R : ℝ} (hR : 0 < R) {x : ℂ}
    (hx : 2 * R ≤ Q.clearance x) : vertexCutoff Q R x = 1 := by
  apply Finset.prod_eq_one
  intro i _
  apply vertexCutoffFactor_one Q hR i
  exact hx.trans (by
    simpa only [Triangle.clearance, dist_eq_norm] using
      Metric.infDist_le_dist_of_mem (x := x) (s := range Q.vertex) (Set.mem_range_self i) : Q.clearance x ≤ ‖x - Q.vertex i‖)

lemma vertexCutoffFactor_contDiff (Q : Triangle) (R : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (vertexCutoffFactor Q R i) := by
  unfold vertexCutoffFactor
  have h : ContDiff ℝ ∞ (fun x : ℂ => (2 * R)⁻¹ • (x - Q.vertex i)) := by fun_prop
  exact contDiff_const.sub (raw_contDiff.comp h)

lemma vertexCutoff_contDiff (Q : Triangle) (R : ℝ) : ContDiff ℝ ∞ (vertexCutoff Q R) := by
  exact contDiff_prod (fun i _ => vertexCutoffFactor_contDiff Q R i)

lemma reflected_vertex_dist (Q : Triangle) (i k : Fin 3) (hk : k = i ∨ k = i+1) (x : ℂ) :
    ‖wallReflection Q i x - Q.vertex k‖ = ‖x - Q.vertex k‖ := by
  have hfix : wallReflection Q i (Q.vertex k) = Q.vertex k := by
    rcases hk with rfl | rfl
    · simp [wallReflection, reflect]
    · unfold wallReflection
      change Q.vertex i + reflect (Q.tangent i) (Q.tangent i) = _
      rw [reflect_tangent (Q.tangent_ne_zero i)]
      simp [Triangle.tangent]
  calc
    _ = ‖wallReflection Q i x - wallReflection Q i (Q.vertex k)‖ := by rw [hfix]
    _ = _ := by rw [wallReflection_sub, reflect_norm (Q.tangent_ne_zero i)]

lemma side_opposite_dist_lower (Q : Triangle) (i : Fin 3) {x : ℂ} (hx : x ∈ Q.side i) :
    1 ≤ Q.coordinateBound * ‖x - Q.vertex (i+2)‖ := by
  have h := Q.coord_norm_le (i+2) x (Q.vertex (i+2))
  have hz : Q.basis.coord (i+2) x = 0 := (Q.side_coord_zero_iff hx _).mpr rfl
  rw [hz] at h
  have h1 : Q.basis.coord (i+2) (Q.vertex (i+2)) = 1 := Q.basis.coord_apply_eq (i+2)
  rw [h1] at h
  simpa only [zero_sub, abs_neg, abs_one] using h

/-- Scale condition only on geometric constants of the fixed nondegenerate
triangle. It imposes no Diophantine angle condition. -/
lemma vertexCutoff_seam_germ (Q : Triangle) {R : ℝ} (hR : 0 < R)
    (hsmall : 2 * R * Q.coordinateBound < 1) (i : Fin 3) {x : ℂ} (hx : x ∈ Q.side i) :
    ∀ᶠ y in 𝓝 x, vertexCutoff Q R (wallReflection Q i y) = vertexCutoff Q R y := by
  have hfar : 2 * R < ‖x - Q.vertex (i+2)‖ := by
    by_contra hn
    have hn := le_of_not_gt hn
    have hb := side_opposite_dist_lower Q i hx
    nlinarith [Q.coordinateBound_nonneg]
  have hc : Continuous (fun y : ℂ => ‖y - Q.vertex (i+2)‖) := by fun_prop
  have hr : Continuous (fun y : ℂ => ‖wallReflection Q i y - Q.vertex (i+2)‖) :=
    hc.comp (wallReflection_contDiff Q i).continuous
  have hfar' : 2 * R < ‖wallReflection Q i x - Q.vertex (i+2)‖ := by
    rwa [wallReflection_fixed_side Q hx]
  filter_upwards [hc.continuousAt.eventually (Ioi_mem_nhds hfar),
    hr.continuousAt.eventually (Ioi_mem_nhds hfar')] with y hy hry
  apply Finset.prod_congr rfl
  intro k _
  by_cases hk : k = i+2
  · subst k
    rw [vertexCutoffFactor_one Q hR _ hry.le, vertexCutoffFactor_one Q hR _ hy.le]
  · have hk' : k = i ∨ k = i+1 := by
      have hfin : ∀ i k : Fin 3, k ≠ i+2 → k = i ∨ k = i+1 := by decide
      exact hfin i k hk
    unfold vertexCutoffFactor
    congr 1
    apply raw_radial
    simp only [norm_smul, reflected_vertex_dist Q i k hk']

end TriangularBilliards

namespace TriangularBilliards
open Filter SpatialSmoothing
open scoped Topology ContDiff

/-- The supported smoothing used for bounded-mode regularity. -/
def supportedSmoothing (Q : Triangle) (ε R : ℝ) (f : DoublePhase → ℂ) : DoublePhase → ℂ :=
  fun z => vertexCutoff Q R z.1.1 • reflectedSmoothing Q ε f z

lemma supportedSmoothing_zero {Q : Triangle} {ε R : ℝ} (hR : 0 < R)
    (f : DoublePhase → ℂ) (z : DoublePhase) (hz : Q.clearance z.1.1 ≤ R) :
    supportedSmoothing Q ε R f z = 0 := by
  simp only [supportedSmoothing, vertexCutoff_zero Q hR hz, zero_smul]

lemma supportedSmoothing_seam (Q : Triangle) {ε R : ℝ} (hε : 0 < ε)
    (hR : Q.safetyFactor * ε < R) (hsmall : 2 * R * Q.coordinateBound < 1)
    (f : DoublePhase → ℂ) : SeamCompatible Q (supportedSmoothing Q ε R f) := by
  have hRp : 0 < R := (mul_pos Q.safetyFactor_pos hε).trans hR
  intro i x hx v b
  by_cases hs : Q.safetyFactor * ε < Q.clearance x
  · filter_upwards [vertexCutoff_seam_germ Q hRp hsmall i hx,
      reflectedSmoothing_seam_germ Q hx hε hs f b v] with y hy hyy
    simp only [supportedSmoothing, hy, hyy]
  · have hxr : Q.clearance x < R := (le_of_not_gt hs).trans_lt hR
    have hc := Q.clearance_lipschitz.continuous
    have hxr' : Q.clearance (wallReflection Q i x) < R := by
      rwa [wallReflection_fixed_side Q hx]
    filter_upwards [hc.continuousAt.eventually (Iio_mem_nhds hxr),
      (hc.comp (wallReflection_contDiff Q i).continuous).continuousAt.eventually
        (Iio_mem_nhds hxr')] with y hy hry
    exact (supportedSmoothing_zero (ε := ε) hRp f
      ((wallReflection Q i y, reflectedDirection Q i v),b+1) hry.le).trans
        (supportedSmoothing_zero (ε := ε) hRp f ((y,v),b) hy.le).symm

lemma bounded_spatialSlice_integrable (Q : Triangle) {f : DoublePhase → ℂ}
    (hm : StronglyMeasurable f) {H : ℝ} (hH : ∀ z, ‖f z‖ ≤ H) (v : Circle) (b : ZMod 2) :
    IntegrableOn (fun x => f ((x,v),b)) Q.table := by
  have : IsFiniteMeasure (volume.restrict Q.table) := ⟨by simpa using Q.area_lt_top⟩
  exact (integrable_const H).mono'
    ((hm.comp_measurable ((measurable_id.prodMk measurable_const).prodMk measurable_const)).aestronglyMeasurable)
    (Eventually.of_forall (fun x => hH ((x,v),b)))

lemma supportedSmoothing_contDiff (Q : Triangle) {ε : ℝ} (hε : 0 < ε) (R : ℝ)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {H : ℝ} (hH : ∀ z, ‖f z‖ ≤ H)
    (v : Circle) (b : ZMod 2) :
    ContDiff ℝ ∞ (fun x => supportedSmoothing Q ε R f ((x,v),b)) :=
  (vertexCutoff_contDiff Q R).smul (reflectedSmoothing_contDiff Q hε
    (bounded_spatialSlice_integrable Q hm hH v b)
    (fun i => bounded_spatialSlice_integrable Q hm hH (reflectedDirection Q i v) (b+1)))

lemma supportedSmoothing_stronglyMeasurable (Q : Triangle) (ε R : ℝ)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) :
    StronglyMeasurable (supportedSmoothing Q ε R f) :=
  (((vertexCutoff_contDiff Q R).continuous.comp (continuous_fst.comp continuous_fst)).stronglyMeasurable).smul
    (reflectedSmoothing_stronglyMeasurable Q ε hm)

lemma directS_norm_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} {H : ℝ} (hH : 0 ≤ H) (hf : ∀ z, ‖f z‖ ≤ H)
    (v : Circle) (b : ZMod 2) (x : ℂ) : ‖directS Q ε f b v x‖ ≤ H := by
  unfold directS
  simpa only [one_mul] using norm_integral_le_kernel_bound
    (μ := volume.restrict Q.table) (fun y => kernel ε (x-y) • f ((y,v),b))
    (K := fun y => ENNReal.ofReal (kernel ε (x-y))) hH (by norm_num : (0 : ℝ) ≤ 1)
    (fun y => by
      rw [← ofReal_norm, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (kernel_nonneg ε _), ENNReal.ofReal_mul (kernel_nonneg ε _)]
      exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (hf ((y,v),b))) _)
    (by simpa only [ENNReal.ofReal_one] using kernel_row_bound Q hε x)

lemma reflectedSmoothing_norm_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} {H : ℝ} (hH : 0 ≤ H) (hf : ∀ z, ‖f z‖ ≤ H)
    (z : DoublePhase) : ‖reflectedSmoothing Q ε f z‖ ≤ 4 * H := by
  unfold reflectedSmoothing
  calc
    _ ≤ ‖directS Q ε f z.2 z.1.2 z.1.1‖ + ∑ i : Fin 3, ‖reflectedS Q i ε f z.2 z.1.2 z.1.1‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ H + ∑ _i : Fin 3, H := by
      gcongr
      · exact directS_norm_bound Q hε hH hf _ _ _
      · rw [reflectedS_eq_directS]
        exact directS_norm_bound Q hε hH hf _ _ _
    _ = 4 * H := by simp; ring

lemma supportedSmoothing_norm_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε) (R : ℝ)
    {f : DoublePhase → ℂ} {H : ℝ} (hH : 0 ≤ H) (hf : ∀ z, ‖f z‖ ≤ H)
    (z : DoublePhase) : ‖supportedSmoothing Q ε R f z‖ ≤ 4 * H := by
  rw [supportedSmoothing, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (vertexCutoff_mem_Icc Q R _).1]
  calc
    _ ≤ 1 * (4 * H) := mul_le_mul (vertexCutoff_mem_Icc Q R _).2
      (reflectedSmoothing_norm_bound Q hε hH hf z) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end TriangularBilliards

end
end
end
end
end

end OAI
end
end

section
section
namespace OAI


open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section

open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section

namespace TriangularBilliards.Analysis

/-- Fubini for a real bounded spatial kernel.  Both input slices are merely
integrable; neither is differentiated. -/
lemma real_kernel_adjoint_slice {A : Type uA} [MeasurableSpace A]
    {μ : Measure A} [SFinite μ] {k l : A → A → ℝ}
    (hk : StronglyMeasurable (Function.uncurry k)) {K : ℝ}
    (hK : ∀ x y, |k x y| ≤ K) (hs : ∀ x y, k x y = l y x)
    {f g : A → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ x, (∫ y, k x y • f y ∂μ) * conj (g x) ∂μ) =
      ∫ y, f y * conj (∫ x, l y x • g x ∂μ) ∂μ := by
  have hgc : Integrable (fun x => conj (g x)) μ :=
    hg.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable hg.1)
      (Eventually.of_forall fun _ => by simp)
  have hi : Integrable (Function.uncurry (fun x y => (k x y • f y) * conj (g x)))
      (μ.prod μ) := by
    have hh := (hgc.mul_prod hf).bdd_mul
      (Complex.continuous_ofReal.comp_stronglyMeasurable hk).aestronglyMeasurable
      (Eventually.of_forall fun p => by simpa only [Complex.norm_real, Real.norm_eq_abs, Function.uncurry] using hK p.1 p.2)
    convert hh using 1
    ext p
    change (k p.1 p.2 • f p.2) * conj (g p.1) =
      (k p.1 p.2 : ℂ) * (conj (g p.1) * f p.2)
    rw [Complex.real_smul]
    ring
  simp_rw [← integral_mul_const]
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← integral_conj, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [hs]
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]
  ring

end TriangularBilliards.Analysis

namespace TriangularBilliards.Analysis

def fiberKernel {A : Type uA} {C : Type uC} [MeasurableSpace A] (μ : Measure A)
    (J : C → C) (k : A → A → C → ℝ) (f : A × C → ℂ) (z : A × C) : ℂ :=
  ∫ y, k z.1 y z.2 • f (y, J z.2) ∂μ

/-- The transport-reversing kernel identity gives the adjoint on a product
space.  This is applicable to both the direct term (J = id) and a wall
reflection, including a derivative kernel with the opposite sign. -/
lemma fiberKernel_adjoint {A : Type uA} {C : Type uC} [MeasurableSpace A] [MeasurableSpace C]
    {μ : Measure A} {ν : Measure C} [SFinite μ] [SFinite ν]
    {J : C → C} (hJ : MeasurePreserving J ν ν) (hJe : MeasurableEmbedding J)
    (hJJ : Function.Involutive J) {k l : A → A → C → ℝ}
    (hk : ∀ c, StronglyMeasurable (Function.uncurry (fun x y => k x y c)))
    (hK : ∀ c, ∃ K : ℝ, ∀ x y, |k x y c| ≤ K)
    (hs : ∀ x y c, k x y c = l y x (J c))
    {f g : A × C → ℂ} (hf : Integrable f (μ.prod ν)) (hg : Integrable g (μ.prod ν))
    (hpair₁ : Integrable (fun z => fiberKernel μ J k f z * conj (g z)) (μ.prod ν))
    (hpair₂ : Integrable (fun z => f z * conj (fiberKernel μ J l g z)) (μ.prod ν)) :
    (∫ z, fiberKernel μ J k f z * conj (g z) ∂μ.prod ν) =
      ∫ z, f z * conj (fiberKernel μ J l g z) ∂μ.prod ν := by
  rw [integral_prod_symm _ hpair₁, integral_prod_symm _ hpair₂]
  calc
    _ = ∫ c, ∫ y, f (y, J c) * conj (fiberKernel μ J l g (y, J c)) ∂μ ∂ν := by
      apply integral_congr_ae
      filter_upwards [hJ.quasiMeasurePreserving.ae hf.prod_left_ae, hg.prod_left_ae] with c hfc hgc
      obtain ⟨K,hKc⟩ := hK c
      have h := real_kernel_adjoint_slice (hk c) hKc (fun x y => hs x y c) hfc hgc
      simpa only [fiberKernel, hJJ c] using h
    _ = _ := hJ.integral_comp hJe (fun c => ∫ y, f (y,c) * conj (fiberKernel μ J l g (y,c)) ∂μ)

end TriangularBilliards.Analysis

namespace TriangularBilliards
open SpatialSmoothing Filter Analysis
open scoped Topology ComplexConjugate

lemma kernel_swap (ε : ℝ) (x y : ℂ) : kernel ε (x-y) = kernel ε (y-x) := by
  exact kernel_radial ε (norm_sub_rev x y)

lemma kernel_wall_swap (Q : Triangle) (i : Fin 3) (ε : ℝ) (x y : ℂ) :
    kernel ε (x-wallReflection Q i y) = kernel ε (y-wallReflection Q i x) := by
  rw [← kernel_wall_transfer, kernel_swap]

lemma kernel_fderiv_neg (ε : ℝ) (x : ℂ) :
    fderiv ℝ (kernel ε) (-x) = -fderiv ℝ (kernel ε) x := by
  simp only [kernel_fderiv, smul_neg, rho_fderiv_neg]

lemma kernel_derivative_swap (ε : ℝ) (x y V : ℂ) :
    fderiv ℝ (kernel ε) (x-y) V = -fderiv ℝ (kernel ε) (y-x) V := by
  rw [← neg_sub x y, kernel_fderiv_neg]
  simp only [_root_.neg_apply, neg_neg]

/-- Reversal of a reflected short segment also reverses its transported
kernel derivative. This is proved from the actual wall unfolding. -/
lemma kernel_wall_derivative_swap (Q : Triangle) (i : Fin 3) (ε : ℝ) (x y V : ℂ) :
    fderiv ℝ (kernel ε) (x-wallReflection Q i y) V =
      -fderiv ℝ (kernel ε) (y-wallReflection Q i x) (reflect (Q.tangent i) V) := by
  have h₁ := ((kernel_contDiff ε).differentiable (by simp) (x-wallReflection Q i y)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const (wallReflection Q i y))
  have h₂ := ((kernel_contDiff ε).differentiable (by simp) (y-wallReflection Q i x)).hasFDerivAt.comp x
    ((wallReflection_hasFDerivAt Q i x).const_sub y)
  have he : (fun x => kernel ε (x-wallReflection Q i y)) =
      (fun x => kernel ε (y-wallReflection Q i x)) := funext (fun x => kernel_wall_swap Q i ε x y)
  change HasFDerivAt (fun x => kernel ε (x-wallReflection Q i y)) _ x at h₁
  change HasFDerivAt (fun x => kernel ε (y-wallReflection Q i x)) _ x at h₂
  rw [he] at h₁
  have hd := h₁.unique h₂
  have ha := congrArg (fun L : ℂ →L[ℝ] ℝ => L V) hd
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    _root_.neg_apply, map_neg] at ha
  exact ha

end TriangularBilliards

namespace TriangularBilliards.Analysis
open Analytic Filter
open scoped ComplexConjugate

lemma fiberKernel_stronglyMeasurable {A : Type uA} {C : Type uC} [MeasurableSpace A] [MeasurableSpace C]
    {μ : Measure A} [SFinite μ] {J : C → C} (hJ : Measurable J)
    {k : A → A → C → ℝ}
    (hk : StronglyMeasurable (fun p : (A × C) × A => k p.1.1 p.2 p.1.2))
    {f : A × C → ℂ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fiberKernel μ J k f) := by
  exact (hk.smul (hf.comp_measurable (measurable_snd.prodMk (hJ.comp measurable_fst.snd)))).integral_prod_right

lemma fiberKernel_memLp {A : Type uA} {C : Type uC} [MeasurableSpace A] [MeasurableSpace C]
    {μ : Measure A} {ν : Measure C} [IsFiniteMeasure μ] [SFinite ν]
    {J : C → C} (hJ : MeasurePreserving J ν ν) {k : A → A → C → ℝ}
    (hk : StronglyMeasurable (fun p : (A × C) × A => k p.1.1 p.2 p.1.2))
    {K : ℝ} (hK : ∀ x y c, |k x y c| ≤ K)
    {f : A × C → ℂ} (hf : StronglyMeasurable f) (hf₂ : MemLp f 2 (μ.prod ν)) :
    MemLp (fiberKernel μ J k f) 2 (μ.prod ν) := by
  let g : A × C → ℂ := fun z => f (z.1,J z.2)
  have hg : StronglyMeasurable g := hf.comp_measurable (measurable_fst.prodMk (hJ.measurable.comp measurable_snd))
  have hg₂ : MemLp g 2 (μ.prod ν) := hf₂.comp_measurePreserving ((MeasurePreserving.id μ).prod hJ)
  have hF := hk.smul (hf.comp_measurable (measurable_snd.prodMk (hJ.measurable.comp measurable_fst.snd)))
  have hb : ∀ x c y, ‖k x y c • f (y,J c)‖ₑ ≤ ENNReal.ofReal K * ‖g (y,c)‖ₑ := by
    intro x c y
    rw [enorm_smul]
    exact mul_le_mul' (by simpa only [Real.enorm_eq_ofReal_abs] using
      ENNReal.ofReal_le_ofReal (hK x y c)) le_rfl
  have hrow (x : A) : ∫⁻ y : A, ENNReal.ofReal K ∂μ ≤ ENNReal.ofReal K * μ Set.univ := by simp
  have hbound := fiber_kernel_integral_schur_sq μ μ ν (K := fun _ _ : A => ENNReal.ofReal K)
    (F := fun z y => k z.1 y z.2 • f (y,J z.2))
    (measurable_const : Measurable (Function.uncurry (fun _ _ : A => ENNReal.ofReal K)))
    hg.enorm hrow hrow hF hb
  refine ⟨(fiberKernel_stronglyMeasurable hJ.measurable hk hf).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num)
    (by norm_num)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  have hfint : ∫⁻ y, ‖g y‖ₑ ^ (2 : ℕ) ∂μ.prod ν < ⊤ := by
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hg₂.eLpNorm_lt_top
  have hA : ENNReal.ofReal K * μ Set.univ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  exact hbound.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top hA hA) hfint)

lemma memLp_conj {A : Type uA} [MeasurableSpace A] {μ : Measure A} {p : ℝ≥0∞}
    {f : A → ℂ} (hf : MemLp f p μ) : MemLp (fun x => conj (f x)) p μ := by
  apply hf.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable)
  exact Eventually.of_forall fun _ => by simp

lemma fiberKernel_L2_adjoint {A : Type uA} {C : Type uC} [MeasurableSpace A] [MeasurableSpace C]
    {μ : Measure A} {ν : Measure C} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {J : C → C} (hJ : MeasurePreserving J ν ν) (hJe : MeasurableEmbedding J)
    (hJJ : Function.Involutive J) {k l : A → A → C → ℝ}
    (hk : StronglyMeasurable (fun p : (A × C) × A => k p.1.1 p.2 p.1.2))
    (hl : StronglyMeasurable (fun p : (A × C) × A => l p.1.1 p.2 p.1.2))
    {K L : ℝ} (hK : ∀ x y c, |k x y c| ≤ K) (hL : ∀ x y c, |l x y c| ≤ L)
    (hs : ∀ x y c, k x y c = l y x (J c))
    {f g : A × C → ℂ} (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hf : MemLp f 2 (μ.prod ν)) (hg : MemLp g 2 (μ.prod ν)) :
    (∫ z, fiberKernel μ J k f z * conj (g z) ∂μ.prod ν) =
      ∫ z, f z * conj (fiberKernel μ J l g z) ∂μ.prod ν := by
  apply fiberKernel_adjoint hJ hJe hJJ
    (fun c => hk.comp_measurable ((measurable_fst.prodMk measurable_const).prodMk measurable_snd))
    (fun c => ⟨K,fun x y => hK x y c⟩) hs (hf.integrable (by norm_num)) (hg.integrable (by norm_num))
  · exact (fiberKernel_memLp hJ hk hK hfm hf).integrable_mul (memLp_conj hg)
  · exact hf.integrable_mul (memLp_conj (fiberKernel_memLp hJ hl hL hgm hg))

end TriangularBilliards.Analysis

namespace TriangularBilliards
open Analysis SpatialSmoothing Filter
open scoped ComplexConjugate

abbrev DirectionParity := Circle × ZMod 2

def associatedField (f : DoublePhase → ℂ) (p : ℂ × DirectionParity) : ℂ :=
  f ((p.1,p.2.1),p.2.2)

lemma associatedField_memLp (Q : Triangle) {f : DoublePhase → ℂ}
    (hf : MemLp f 2 (doubleMeasure Q)) :
    MemLp (associatedField f) 2
      ((volume.restrict Q.table).prod (angularMeasure.prod parityMeasure)) := by
  let μ : Measure ℂ := (volume Q.table)⁻¹ • volume.restrict Q.table
  have hμ : IsProbabilityMeasure μ := ⟨Q.normalized_area_univ⟩
  have ha := measurePreserving_prodAssoc μ angularMeasure parityMeasure
  have hh := hf.comp_measurePreserving (ha.symm MeasurableEquiv.prodAssoc)
  have h := hh.smul_measure Q.area_lt_top.ne
  change MemLp (associatedField f) 2 _ at h
  simpa only [μ, Measure.prod_smul_left, smul_smul,
    ENNReal.mul_inv_cancel Q.area_pos.ne' Q.area_lt_top.ne, one_smul] using h

lemma associatedField_stronglyMeasurable {f : DoublePhase → ℂ}
    (hf : StronglyMeasurable f) : StronglyMeasurable (associatedField f) :=
  hf.comp_measurable ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)

lemma double_integral_assoc (Q : Triangle) (F : DoublePhase → ℂ) :
    ∫ z, F z ∂doubleMeasure Q = ((volume Q.table)⁻¹).toReal •
      ∫ p : ℂ × DirectionParity, F ((p.1,p.2.1),p.2.2)
        ∂(volume.restrict Q.table).prod (angularMeasure.prod parityMeasure) := by
  simp only [doubleMeasure, phaseMeasure, Measure.prod_smul_left, integral_smul_measure]
  congr 1
  exact (measurePreserving_prodAssoc (volume.restrict Q.table) angularMeasure parityMeasure).integral_comp
    MeasurableEquiv.prodAssoc.measurableEmbedding
    (fun p : ℂ × DirectionParity => F ((p.1,p.2.1),p.2.2))

def directionParityReflection (Q : Triangle) (i : Fin 3) (c : DirectionParity) : DirectionParity :=
  (reflectedDirection Q i c.1,c.2+1)

lemma directionParityReflection_involutive (Q : Triangle) (i : Fin 3) :
    Function.Involutive (directionParityReflection Q i) := by
  rintro ⟨v,b⟩
  simp only [directionParityReflection, reflectedDirection_involutive, Prod.mk.injEq, true_and]
  have : (1 : ZMod 2) + 1 = 0 := by decide
  rw [add_assoc, this, add_zero]

lemma measurePreserving_directionParity (Q : Triangle) (i : Fin 3) :
    MeasurePreserving (directionParityReflection Q i) (angularMeasure.prod parityMeasure)
      (angularMeasure.prod parityMeasure) := by
  convert (measurePreserving_reflectedDirection Q i).prod (measurePreserving_parity_add 1) using 1
  funext ⟨v,b⟩
  exact congrArg (fun q => (reflectedDirection Q i v,q)) (add_comm b 1)

lemma measurableEmbedding_directionParity (Q : Triangle) (i : Fin 3) :
    MeasurableEmbedding (directionParityReflection Q i) :=
  (MeasurableEquiv.ofInvolutive (directionParityReflection Q i)
    (directionParityReflection_involutive Q i)
    (measurePreserving_directionParity Q i).measurable).measurableEmbedding

/-- Kernel integration on the two physical triangle copies, with the exact
unnormalized Euclidean spatial integral and normalized phase pairing. -/
def doubleKernel (Q : Triangle) (J : DirectionParity → DirectionParity)
    (k : ℂ → ℂ → DirectionParity → ℝ) (f : DoublePhase → ℂ)
    (z : DoublePhase) : ℂ :=
  fiberKernel (volume.restrict Q.table) J k (associatedField f)
    (z.1.1,(z.1.2,z.2))

lemma doubleKernel_adjoint (Q : Triangle) {J : DirectionParity → DirectionParity}
    (hJ : MeasurePreserving J (angularMeasure.prod parityMeasure) (angularMeasure.prod parityMeasure))
    (hJe : MeasurableEmbedding J) (hJJ : Function.Involutive J)
    {k l : ℂ → ℂ → DirectionParity → ℝ}
    (hk : StronglyMeasurable (fun p : (ℂ × DirectionParity) × ℂ => k p.1.1 p.2 p.1.2))
    (hl : StronglyMeasurable (fun p : (ℂ × DirectionParity) × ℂ => l p.1.1 p.2 p.1.2))
    {K L : ℝ} (hK : ∀ x y c, |k x y c| ≤ K) (hL : ∀ x y c, |l x y c| ≤ L)
    (hs : ∀ x y c, k x y c = l y x (J c))
    {f g : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hf : MemLp f 2 (doubleMeasure Q)) (hg : MemLp g 2 (doubleMeasure Q)) :
    (∫ z, doubleKernel Q J k f z * conj (g z) ∂doubleMeasure Q) =
      ∫ z, f z * conj (doubleKernel Q J l g z) ∂doubleMeasure Q := by
  have : IsFiniteMeasure (volume.restrict Q.table) := ⟨by simpa using Q.area_lt_top⟩
  rw [double_integral_assoc, double_integral_assoc]
  congr 1
  exact fiberKernel_L2_adjoint hJ hJe hJJ hk hl hK hL hs
    (associatedField_stronglyMeasurable hfm) (associatedField_stronglyMeasurable hgm)
    (associatedField_memLp Q hf) (associatedField_memLp Q hg)

lemma doubleKernel_neg (Q : Triangle) (J : DirectionParity → DirectionParity)
    (k : ℂ → ℂ → DirectionParity → ℝ) (f : DoublePhase → ℂ) (z : DoublePhase) :
    doubleKernel Q J (fun x y c => -k x y c) f z = -doubleKernel Q J k f z := by
  simp only [doubleKernel, fiberKernel, neg_smul, integral_neg]

lemma doubleKernel_skew (Q : Triangle) {J : DirectionParity → DirectionParity}
    (hJ : MeasurePreserving J (angularMeasure.prod parityMeasure) (angularMeasure.prod parityMeasure))
    (hJe : MeasurableEmbedding J) (hJJ : Function.Involutive J)
    {k : ℂ → ℂ → DirectionParity → ℝ}
    (hk : StronglyMeasurable (fun p : (ℂ × DirectionParity) × ℂ => k p.1.1 p.2 p.1.2))
    {K : ℝ} (hK : ∀ x y c, |k x y c| ≤ K)
    (hs : ∀ x y c, k x y c = -k y x (J c))
    {f g : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hf : MemLp f 2 (doubleMeasure Q)) (hg : MemLp g 2 (doubleMeasure Q)) :
    (∫ z, doubleKernel Q J k f z * conj (g z) ∂doubleMeasure Q) =
      -(∫ z, f z * conj (doubleKernel Q J k g z) ∂doubleMeasure Q) := by
  have h := doubleKernel_adjoint Q hJ hJe hJJ (l := fun x y c => -k x y c) hk hk.neg hK
    (fun x y c => by simpa only [abs_neg] using hK x y c) hs hfm hgm hf hg
  simpa only [doubleKernel_neg, map_neg, mul_neg, integral_neg] using h

end TriangularBilliards

end
end
end
end
end
end

end OAI
end
end

section
section
namespace OAI


open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section

namespace TriangularBilliards
open Analysis SpatialSmoothing Filter
open scoped ComplexConjugate

lemma directionalKernel_stronglyMeasurable (ε : ℝ) {R : ℂ → ℂ} (hR : Measurable R)
    {V : DirectionParity → ℂ} (hV : StronglyMeasurable V) :
    StronglyMeasurable (fun p : (ℂ × DirectionParity) × ℂ =>
      fderiv ℝ (kernel ε) (p.1.1-R p.2) (V p.1.2)) := by
  exact isBoundedBilinearMap_apply.continuous.comp_stronglyMeasurable
    (((((kernel_contDiff ε).continuous_fderiv (by simp)).measurable.comp
      (measurable_fst.fst.sub (hR.comp measurable_snd))).stronglyMeasurable).prodMk
      (hV.comp_measurable measurable_fst.snd))

lemma directionalKernel_bounded {ε : ℝ} (hε : 0 < ε) (R : ℂ → ℂ)
    {V : DirectionParity → ℂ} (hV : ∀ c, ‖V c‖ ≤ 1) :
    ∃ K : ℝ, ∀ x y c, |fderiv ℝ (kernel ε) (x-R y) (V c)| ≤ K := by
  obtain ⟨K,hK⟩ := ((kernel_hasCompactSupport hε).fderiv ℝ).exists_bound_of_continuous
    ((kernel_contDiff ε).continuous_fderiv (by simp))
  refine ⟨K,fun x y c => ?_⟩
  rw [← Real.norm_eq_abs]
  calc
    _ ≤ ‖fderiv ℝ (kernel ε) (x-R y)‖ * ‖V c‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ (kernel ε) (x-R y)‖ * 1 := mul_le_mul_of_nonneg_left (hV c) (norm_nonneg _)
    _ ≤ K := by simpa only [mul_one] using hK (x-R y)

lemma directDirectional_adjoint (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {V : DirectionParity → ℂ} (hVm : StronglyMeasurable V) (hV : ∀ c, ‖V c‖ ≤ 1)
    {f g : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hf : MemLp f 2 (doubleMeasure Q)) (hg : MemLp g 2 (doubleMeasure Q)) :
    (∫ z, doubleKernel Q id (fun x y c => fderiv ℝ (kernel ε) (x-y) (V c)) f z *
      conj (g z) ∂doubleMeasure Q) =
      -(∫ z, f z * conj (doubleKernel Q id
        (fun x y c => fderiv ℝ (kernel ε) (x-y) (V c)) g z) ∂doubleMeasure Q) := by
  obtain ⟨K,hK⟩ := directionalKernel_bounded hε id hV
  exact doubleKernel_skew Q (MeasurePreserving.id _) MeasurableEmbedding.id (fun _ => rfl)
    (directionalKernel_stronglyMeasurable ε measurable_id hVm) hK
    (fun x y c => kernel_derivative_swap ε x y (V c)) hfm hgm hf hg

lemma reflectedDirectional_adjoint (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {V : DirectionParity → ℂ} (hVm : StronglyMeasurable V) (hV : ∀ c, ‖V c‖ ≤ 1)
    (hVR : ∀ c, reflect (Q.tangent i) (V c) = V (directionParityReflection Q i c))
    {f g : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hf : MemLp f 2 (doubleMeasure Q)) (hg : MemLp g 2 (doubleMeasure Q)) :
    (∫ z, doubleKernel Q (directionParityReflection Q i)
      (fun x y c => fderiv ℝ (kernel ε) (x-wallReflection Q i y) (V c)) f z *
      conj (g z) ∂doubleMeasure Q) =
      -(∫ z, f z * conj (doubleKernel Q (directionParityReflection Q i)
        (fun x y c => fderiv ℝ (kernel ε) (x-wallReflection Q i y) (V c)) g z) ∂doubleMeasure Q) := by
  obtain ⟨K,hK⟩ := directionalKernel_bounded hε (wallReflection Q i) hV
  apply doubleKernel_skew Q (measurePreserving_directionParity Q i)
    (measurableEmbedding_directionParity Q i) (directionParityReflection_involutive Q i)
    (directionalKernel_stronglyMeasurable ε (wallReflection_contDiff Q i).continuous.measurable hVm)
    hK _ hfm hgm hf hg
  intro x y c
  simpa only [hVR] using kernel_wall_derivative_swap Q i ε x y (V c)

lemma directGradS_apply_ae (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    (V : DirectionParity → ℂ) {f : DoublePhase → ℂ}
    (hfm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q)) :
    (fun z => directGradS Q ε f z (V (z.1.2,z.2))) =ᵐ[doubleMeasure Q]
      doubleKernel Q id (fun x y c => fderiv ℝ (kernel ε) (x-y) (V c)) f := by
  filter_upwards [directGradS_integrable_ae Q hε hfm (hf.integrable (by norm_num))] with z hz
  exact ContinuousLinearMap.integral_apply hz (V (z.1.2,z.2))

lemma reflectedGradS_apply_ae (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    (V : DirectionParity → ℂ) {f : DoublePhase → ℂ}
    (hfm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q)) :
    (fun z => reflectedGradS Q i ε f z (V (z.1.2,z.2))) =ᵐ[doubleMeasure Q]
      doubleKernel Q (directionParityReflection Q i)
        (fun x y c => fderiv ℝ (kernel ε) (x-wallReflection Q i y) (V c)) f := by
  filter_upwards [reflectedGradS_integrable_ae Q i hε hfm (hf.integrable (by norm_num))] with z hz
  exact ContinuousLinearMap.integral_apply hz (V (z.1.2,z.2))

end TriangularBilliards

namespace TriangularBilliards.Analysis
open Filter
open scoped ComplexConjugate

lemma gradientApply_memLp {A : Type uA} [MeasurableSpace A] {μ : Measure A}
    {F : A → ℂ →L[ℝ] ℂ} (hF : MemLp F 2 μ)
    {V : A → ℂ} (hV : StronglyMeasurable V) (hVb : ∀ z, ‖V z‖ ≤ 1) :
    MemLp (fun z => F z (V z)) 2 μ := by
  apply hF.norm.mono'
    (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hF.aestronglyMeasurable.prodMk hV.aestronglyMeasurable))
  exact Eventually.of_forall fun z =>
    (ContinuousLinearMap.le_opNorm _ _).trans ((mul_le_mul_of_nonneg_left (hVb z) (norm_nonneg _)).trans_eq (mul_one _))

lemma pairing_add_sum {A : Type uA} [MeasurableSpace A] {μ : Measure A}
    {f g d e : A → ℂ} {r s : Fin 3 → A → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hd : MemLp d 2 μ) (he : MemLp e 2 μ)
    (hr : ∀ i, MemLp (r i) 2 μ) (hs : ∀ i, MemLp (s i) 2 μ)
    (h0 : (∫ z, d z * conj (g z) ∂μ) = -(∫ z, f z * conj (e z) ∂μ))
    (hi : ∀ i, (∫ z, r i z * conj (g z) ∂μ) = -(∫ z, f z * conj (s i z) ∂μ)) :
    (∫ z, (d z + ∑ i, r i z) * conj (g z) ∂μ) =
      -(∫ z, f z * conj (e z + ∑ i, s i z) ∂μ) := by
  have hD : Integrable (fun z => d z * conj (g z)) μ := hd.integrable_mul (memLp_conj hg)
  have hE : Integrable (fun z => f z * conj (e z)) μ := hf.integrable_mul (memLp_conj he)
  have hR (i) : Integrable (fun z => r i z * conj (g z)) μ := (hr i).integrable_mul (memLp_conj hg)
  have hS (i) : Integrable (fun z => f z * conj (s i z)) μ := hf.integrable_mul (memLp_conj (hs i))
  simp only [add_mul, Finset.sum_mul, map_add, map_sum, mul_add, Finset.mul_sum]
  rw [integral_add hD (integrable_finsetSum Finset.univ (fun i _ => hR i)),
    integral_add hE (integrable_finsetSum Finset.univ (fun i _ => hS i)),
    integral_finsetSum Finset.univ (fun i _ => hR i),
    integral_finsetSum Finset.univ (fun i _ => hS i), h0]
  simp only [hi, Finset.sum_neg_distrib, neg_add_rev]
  ring

end TriangularBilliards.Analysis

namespace TriangularBilliards
open Analysis SpatialSmoothing Filter
open scoped ComplexConjugate

lemma directGradS_memLp (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q)) :
    MemLp (directGradS Q ε f) 2 (doubleMeasure Q) :=
  ⟨(directGradS_stronglyMeasurable Q ε hfm).aestronglyMeasurable, (directGradS_eLpNorm Q hε hfm).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top)⟩

lemma reflectedGradS_memLp (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q)) :
    MemLp (reflectedGradS Q i ε f) 2 (doubleMeasure Q) :=
  ⟨(reflectedGradS_stronglyMeasurable Q i ε hfm).aestronglyMeasurable, (reflectedGradS_eLpNorm Q i hε hfm).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top)⟩

/-- Adjoint identity for the actual unfolded gradient kernel on the complete
L² space. It holds in particular after pairing against a supported field,
without taking any derivatives of that field. -/
lemma reflectedSmoothingGradient_adjoint (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {V : DirectionParity → ℂ} (hVm : StronglyMeasurable V) (hV : ∀ c, ‖V c‖ ≤ 1)
    (hVR : ∀ i c, reflect (Q.tangent i) (V c) = V (directionParityReflection Q i c))
    {f g : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hf : MemLp f 2 (doubleMeasure Q)) (hg : MemLp g 2 (doubleMeasure Q)) :
    (∫ z, reflectedSmoothingGradient Q ε f z (V (z.1.2,z.2)) * conj (g z) ∂doubleMeasure Q) =
      -(∫ z, f z * conj (reflectedSmoothingGradient Q ε g z (V (z.1.2,z.2))) ∂doubleMeasure Q) := by
  have hm : StronglyMeasurable (fun z : DoublePhase => V (z.1.2,z.2)) :=
    hVm.comp_measurable (measurable_fst.snd.prodMk measurable_snd)
  have hdF := gradientApply_memLp (directGradS_memLp Q hε hfm hf) hm (fun z => hV (z.1.2,z.2))
  have hdG := gradientApply_memLp (directGradS_memLp Q hε hgm hg) hm (fun z => hV (z.1.2,z.2))
  have hrF (i) := gradientApply_memLp (reflectedGradS_memLp Q i hε hfm hf) hm (fun z => hV (z.1.2,z.2))
  have hrG (i) := gradientApply_memLp (reflectedGradS_memLp Q i hε hgm hg) hm (fun z => hV (z.1.2,z.2))
  have hd : (∫ z, directGradS Q ε f z (V (z.1.2,z.2)) * conj (g z) ∂doubleMeasure Q) =
      -(∫ z, f z * conj (directGradS Q ε g z (V (z.1.2,z.2))) ∂doubleMeasure Q) := by
    have h := directDirectional_adjoint Q hε hVm hV hfm hgm hf hg
    convert h using 1
    · apply integral_congr_ae
      filter_upwards [directGradS_apply_ae Q hε V hfm hf] with z hz
      rw [hz]
    · congr 1
      apply integral_congr_ae
      filter_upwards [directGradS_apply_ae Q hε V hgm hg] with z hz
      rw [hz]
  have hr (i) : (∫ z, reflectedGradS Q i ε f z (V (z.1.2,z.2)) * conj (g z) ∂doubleMeasure Q) =
      -(∫ z, f z * conj (reflectedGradS Q i ε g z (V (z.1.2,z.2))) ∂doubleMeasure Q) := by
    have h := reflectedDirectional_adjoint Q i hε hVm hV (hVR i) hfm hgm hf hg
    convert h using 1
    · apply integral_congr_ae
      filter_upwards [reflectedGradS_apply_ae Q i hε V hfm hf] with z hz
      rw [hz]
    · congr 1
      apply integral_congr_ae
      filter_upwards [reflectedGradS_apply_ae Q i hε V hgm hg] with z hz
      rw [hz]
  have hh := pairing_add_sum hf hg hdF hdG hrF hrG hd hr
  simpa only [reflectedSmoothingGradient, Pi.add_apply, Finset.sum_apply,
    _root_.add_apply, _root_.sum_apply] using hh

end TriangularBilliards

namespace TriangularBilliards
open SpatialSmoothing Filter
open scoped Topology ContDiff

lemma directS_hasFDerivAt (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} {b : ZMod 2} {v : Circle}
    (hf : IntegrableOn (fun y => f ((y,v),b)) Q.table) (x : ℂ) :
    HasFDerivAt (directS Q ε f b v) (directGradS Q ε f ((x,v),b)) x := by
  have h := ((directS_contDiff Q hε hf).differentiable (by simp) x).hasFDerivAt
  rwa [directS_fderiv Q hε hf] at h

lemma kernel_wall_derivative_transfer (Q : Triangle) (i : Fin 3) (ε : ℝ) (x y V : ℂ) :
    fderiv ℝ (kernel ε) (wallReflection Q i x-y) (reflect (Q.tangent i) V) =
      fderiv ℝ (kernel ε) (x-wallReflection Q i y) V := by
  rw [kernel_derivative_swap ε (wallReflection Q i x) y]
  exact (kernel_wall_derivative_swap Q i ε x y V).symm

lemma reflectedS_hasFDerivAt (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {b : ZMod 2} {v : Circle}
    (hf : IntegrableOn (fun y => f ((y,reflectedDirection Q i v),b+1)) Q.table) (x : ℂ) :
    HasFDerivAt (reflectedS Q i ε f b v) (reflectedGradS Q i ε f ((x,v),b)) x := by
  rw [reflectedS_eq_directS]
  have h := (directS_hasFDerivAt Q hε hf (wallReflection Q i x)).comp x
    (wallReflection_hasFDerivAt Q i x)
  have he : reflectedGradS Q i ε f ((x,v),b) =
      (directGradS Q ε f ((wallReflection Q i x,reflectedDirection Q i v),b+1)).comp
        (reflectIsometry (Q.tangent i) (Q.tangent_ne_zero i)).toContinuousLinearEquiv.toContinuousLinearMap := by
    obtain ⟨C,hC⟩ := ((kernel_hasCompactSupport hε).fderiv ℝ).exists_bound_of_continuous
      ((kernel_contDiff ε).continuous_fderiv (by simp))
    have hi (a : ℂ) (J : ℂ → ℂ) (hJ : Measurable J) :
        Integrable (fun y => (fderiv ℝ (kernel ε) (a-J y)).smulRight
          (f ((y,reflectedDirection Q i v),b+1))) (volume.restrict Q.table) :=
      smulRight_integrable
        (((kernel_contDiff ε).continuous_fderiv (by simp)).stronglyMeasurable.comp_measurable
          (measurable_const.sub hJ))
        (hm.comp_measurable ((measurable_id.prodMk measurable_const).prodMk measurable_const))
        hf (fun y => hC _)
    ext V
    change (∫ y in Q.table, (fderiv ℝ (kernel ε) (x-wallReflection Q i y)).smulRight
      (f ((y,reflectedDirection Q i v),b+1))) V =
      (∫ y in Q.table, (fderiv ℝ (kernel ε) (wallReflection Q i x-y)).smulRight
      (f ((y,reflectedDirection Q i v),b+1))) (reflect (Q.tangent i) V)
    have hi' := hi (wallReflection Q i x) id measurable_id
    simp only [id_eq] at hi'
    rw [ContinuousLinearMap.integral_apply (hi x _ (wallReflection_contDiff Q i).continuous.measurable),
      ContinuousLinearMap.integral_apply hi']
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [ContinuousLinearMap.smulRight_apply, kernel_wall_derivative_transfer]
  rw [he]
  exact h

lemma reflectedSmoothing_hasFDerivAt (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {b : ZMod 2} {v : Circle}
    (hf : IntegrableOn (fun y => f ((y,v),b)) Q.table)
    (hfr : ∀ i, IntegrableOn (fun y => f ((y,reflectedDirection Q i v),b+1)) Q.table)
    (x : ℂ) :
    HasFDerivAt (fun y => reflectedSmoothing Q ε f ((y,v),b))
      (reflectedSmoothingGradient Q ε f ((x,v),b)) x := by
  exact (directS_hasFDerivAt Q hε hf x).add
    (HasFDerivAt.fun_sum (fun i _ => reflectedS_hasFDerivAt Q i hε hm (hfr i) x))

end TriangularBilliards

namespace TriangularBilliards
open Analysis SpatialSmoothing Filter
open scoped Topology NNReal ContDiff

lemma vertexCutoffFactor_derivative_bound {C : ℝ}
    (hC : ∀ x, ‖fderiv ℝ raw x‖ ≤ C) (Q : Triangle) {R : ℝ} (hR : 0 < R)
    (i : Fin 3) (x : ℂ) : ‖fderiv ℝ (vertexCutoffFactor Q R i) x‖ ≤ C / (2 * R) := by
  let A : ℂ →L[ℝ] ℂ := (2 * R)⁻¹ • ContinuousLinearMap.id ℝ ℂ
  have hA : HasFDerivAt (fun y : ℂ => (2 * R)⁻¹ • (y-Q.vertex i)) A x :=
    by
      convert ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const (Q.vertex i)).const_smul ((2 * R)⁻¹ : ℝ) using 1 <;> rfl
  have hd := ((raw_contDiff.differentiable (by simp)) _).hasFDerivAt.comp x hA
  have he := hd.const_sub 1
  rw [show fderiv ℝ (vertexCutoffFactor Q R i) x =
    -(fderiv ℝ raw ((2*R)⁻¹ • (x-Q.vertex i))).comp A from he.fderiv, norm_neg]
  calc
    _ ≤ ‖fderiv ℝ raw ((2*R)⁻¹ • (x-Q.vertex i))‖ * ‖A‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ C * (2 * R)⁻¹ := by
      rw [show ‖A‖ = (2 * R)⁻¹ by
        simp only [A, norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_id, mul_one]
        exact abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) hR))]
      exact mul_le_mul_of_nonneg_right (hC _) (inv_nonneg.mpr (mul_nonneg (by norm_num) hR.le))
    _ = _ := (div_eq_mul_inv _ _).symm

lemma vertexCutoff_derivative_bound {C : ℝ}
    (hC : ∀ x, ‖fderiv ℝ raw x‖ ≤ C) (Q : Triangle) {R : ℝ} (hR : 0 < R)
    (x : ℂ) : ‖fderiv ℝ (vertexCutoff Q R) x‖ ≤ 3 * C / (2 * R) := by
  classical
  change ‖fderiv ℝ (fun y => ∏ i : Fin 3, vertexCutoffFactor Q R i y) x‖ ≤ _
  rw [fderiv_finsetProd (fun i _ => (vertexCutoffFactor_contDiff Q R i).differentiable (by simp) x)]
  calc
    _ ≤ ∑ i : Fin 3, ‖(∏ j ∈ Finset.univ.erase i, vertexCutoffFactor Q R j x) •
      fderiv ℝ (vertexCutoffFactor Q R i) x‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, C / (2 * R) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Finset.prod_nonneg (fun j _ => (vertexCutoffFactor_mem_Icc Q R j x).1))]
      calc
        _ ≤ 1 * ‖fderiv ℝ (vertexCutoffFactor Q R i) x‖ :=
          mul_le_mul_of_nonneg_right (Finset.prod_le_one₀
            (fun j _ => (vertexCutoffFactor_mem_Icc Q R j x).1)
            (fun j _ => (vertexCutoffFactor_mem_Icc Q R j x).2)) (norm_nonneg _)
        _ ≤ _ := by simpa using vertexCutoffFactor_derivative_bound hC Q hR i x
    _ = _ := by simp; ring

lemma exists_vertexCutoff_derivative_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (Q : Triangle) (R : ℝ), 0 < R → ∀ x,
      ‖fderiv ℝ (vertexCutoff Q R) x‖ ≤ C / R := by
  obtain ⟨C,hC⟩ := (raw_hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (raw_contDiff.continuous_fderiv (by simp))
  refine ⟨3*C/2, by have := (norm_nonneg _).trans (hC 0); positivity, ?_⟩
  intro Q R hR x
  convert vertexCutoff_derivative_bound hC Q hR x using 1
  ring

def supportedSmoothingGradient (Q : Triangle) (ε R : ℝ) (f : DoublePhase → ℂ)
    (z : DoublePhase) : ℂ →L[ℝ] ℂ :=
  vertexCutoff Q R z.1.1 • reflectedSmoothingGradient Q ε f z +
    (fderiv ℝ (vertexCutoff Q R) z.1.1).smulRight (reflectedSmoothing Q ε f z)

lemma supportedSmoothing_hasFDerivAt (Q : Triangle) {ε : ℝ} (hε : 0 < ε) (R : ℝ)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {H : ℝ} (hH : ∀ z, ‖f z‖ ≤ H)
    (v : Circle) (b : ZMod 2) (x : ℂ) :
    HasFDerivAt (fun y => supportedSmoothing Q ε R f ((y,v),b))
      (supportedSmoothingGradient Q ε R f ((x,v),b)) x := by
  exact ((vertexCutoff_contDiff Q R).differentiable (by simp) x).hasFDerivAt.smul
    (reflectedSmoothing_hasFDerivAt Q hε hm (bounded_spatialSlice_integrable Q hm hH v b)
      (fun i => bounded_spatialSlice_integrable Q hm hH (reflectedDirection Q i v) (b+1)) x)

lemma supportedSmoothingGradient_stronglyMeasurable (Q : Triangle) (ε R : ℝ)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) :
    StronglyMeasurable (supportedSmoothingGradient Q ε R f) := by
  apply StronglyMeasurable.add
  · exact (((vertexCutoff_contDiff Q R).continuous.comp
      (continuous_fst.comp continuous_fst)).stronglyMeasurable).smul
      (reflectedSmoothingGradient_stronglyMeasurable Q ε hm)
  · exact smulRight_stronglyMeasurable
      ((((vertexCutoff_contDiff Q R).continuous_fderiv (by simp)).comp
        (continuous_fst.comp continuous_fst)).stronglyMeasurable)
      (reflectedSmoothing_stronglyMeasurable Q ε hm)

lemma reflectedSmoothingGradient_norm_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} {H : ℝ} (hH : 0 ≤ H) (hf : ∀ z, ‖f z‖ ≤ H)
    (z : DoublePhase) : ‖reflectedSmoothingGradient Q ε f z‖ ≤ 4 * derivativeMass * H / ε := by
  have h := scaled_gradient_norm_bound Q hε hH hf z
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε] at h
  exact (le_div_iff₀ hε).mpr (by nlinarith)

lemma supportedSmoothingGradient_norm_bound (Q : Triangle) {ε R : ℝ}
    (hε : 0 < ε) {f : DoublePhase → ℂ} {H C : ℝ} (hH : 0 ≤ H)
    (hf : ∀ z, ‖f z‖ ≤ H) (hC : ∀ x, ‖fderiv ℝ (vertexCutoff Q R) x‖ ≤ C)
    (z : DoublePhase) : ‖supportedSmoothingGradient Q ε R f z‖ ≤
      4 * derivativeMass * H / ε + C * (4 * H) := by
  unfold supportedSmoothingGradient
  calc
    _ ≤ ‖vertexCutoff Q R z.1.1 • reflectedSmoothingGradient Q ε f z‖ +
      ‖(fderiv ℝ (vertexCutoff Q R) z.1.1).smulRight (reflectedSmoothing Q ε f z)‖ := norm_add_le _ _
    _ ≤ 4 * derivativeMass * H / ε + C * (4 * H) := by
      apply add_le_add
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (vertexCutoff_mem_Icc Q R _).1]
        exact (mul_le_of_le_one_left (norm_nonneg _) (vertexCutoff_mem_Icc Q R _).2).trans
          (reflectedSmoothingGradient_norm_bound Q hε hH hf z)
      · rw [ContinuousLinearMap.norm_smulRight_apply]
        exact mul_le_mul (hC _) (reflectedSmoothing_norm_bound Q hε hH hf z)
          (norm_nonneg _) ((norm_nonneg _).trans (hC z.1.1))

end TriangularBilliards

end
end
end
end
end
end

end OAI
end
end

section
section
namespace OAI


open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section

namespace TriangularBilliards
open Analysis SpatialSmoothing Filter
open scoped NNReal ContDiff

lemma supportedSmoothing_xDerivative (Q : Triangle) {ε : ℝ} (hε : 0 < ε) (R : ℝ)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {H : ℝ} (hH : ∀ z, ‖f z‖ ≤ H)
    (z : DoublePhase) : xDerivative (supportedSmoothing Q ε R f) z =
      supportedSmoothingGradient Q ε R f z (z.1.2 : ℂ) := by
  exact congrArg (fun L : ℂ →L[ℝ] ℂ => L (z.1.2 : ℂ))
    (supportedSmoothing_hasFDerivAt Q hε R hm hH z.1.2 z.2 z.1.1).fderiv

lemma supportedSmoothing_fderiv_bound (Q : Triangle) {ε R : ℝ}
    (hε : 0 < ε) (hR : 0 < R) {f : DoublePhase → ℂ} (hm : StronglyMeasurable f)
    {H : ℝ} (hf : ∀ z, ‖f z‖ ≤ H) :
    ∃ C : ℝ≥0, ∀ x v b, ‖fderiv ℝ (fun y => supportedSmoothing Q ε R f ((y,v),b)) x‖ ≤ C := by
  obtain ⟨D,hD,hDb⟩ := exists_vertexCutoff_derivative_bound
  have hH : 0 ≤ H := (norm_nonneg _).trans (hf ((0,1),0))
  let C := 4 * derivativeMass * H / ε + (D / R) * (4 * H)
  have hC : 0 ≤ C := by
    have := derivativeMass_nonneg
    dsimp [C]
    positivity
  refine ⟨⟨C,hC⟩, fun x v b => ?_⟩
  rw [(supportedSmoothing_hasFDerivAt Q hε R hm hf v b x).fderiv]
  exact supportedSmoothingGradient_norm_bound Q hε hH hf (hDb Q R hR) ((x,v),b)

lemma supportedSmoothing_memLp (Q : Triangle) {ε : ℝ} (hε : 0 < ε) (R : ℝ)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {H : ℝ} (hf : ∀ z, ‖f z‖ ≤ H) :
    MemLp (supportedSmoothing Q ε R f) 2 (doubleMeasure Q) := by
  apply MemLp.of_bound (supportedSmoothing_stronglyMeasurable Q ε R hm).aestronglyMeasurable (4*H)
  exact Filter.Eventually.of_forall (supportedSmoothing_norm_bound Q hε R
    ((norm_nonneg _).trans (hf ((0,1),0))) hf)

lemma supportedSmoothing_xDerivative_memLp (Q : Triangle) {ε R : ℝ}
    (hε : 0 < ε) (hR : 0 < R) {f : DoublePhase → ℂ} (hm : StronglyMeasurable f)
    {H : ℝ} (hf : ∀ z, ‖f z‖ ≤ H) :
    MemLp (xDerivative (supportedSmoothing Q ε R f)) 2 (doubleMeasure Q) := by
  have he : xDerivative (supportedSmoothing Q ε R f) =
      fun z => supportedSmoothingGradient Q ε R f z (z.1.2 : ℂ) :=
    funext (supportedSmoothing_xDerivative Q hε R hm hf)
  obtain ⟨C,hC⟩ := supportedSmoothing_fderiv_bound Q hε hR hm hf
  refine MemLp.of_bound ?_ (C : ℝ) ?_
  · rw [he]
    exact (isBoundedBilinearMap_apply.continuous.comp_stronglyMeasurable
      ((supportedSmoothingGradient_stronglyMeasurable Q ε R hm).prodMk
        ((show Continuous (fun z : DoublePhase => (z.1.2 : ℂ)) from
          continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).stronglyMeasurable))).aestronglyMeasurable
  · filter_upwards [] with z
    exact (ContinuousLinearMap.le_opNorm _ _).trans (by
      rw [Circle.norm_coe, mul_one]
      exact hC z.1.1 z.1.2 z.2)

lemma supportedSmoothing_generator (Q : Triangle) {ε R : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor * ε < R)
    (hsmall : 2 * R * Q.coordinateBound < 1)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {H : ℝ} (hf : ∀ z, ‖f z‖ ≤ H) :
    let hs := supportedSmoothing_memLp Q hε R hm hf
    let hx := supportedSmoothing_xDerivative_memLp Q hε
      ((mul_pos Q.safetyFactor_pos hε).trans hR) hm hf
    (geodesicHilbertFlow Q).HasGenerator (hs.toLp _) (hx.toLp _) := by
  obtain ⟨C,hC⟩ := supportedSmoothing_fderiv_bound Q hε
    ((mul_pos Q.safetyFactor_pos hε).trans hR) hm hf
  apply seam_geodesic_generator (supportedSmoothing_seam Q hε hR hsmall f)
    (fun v b => (supportedSmoothing_contDiff Q hε R hm hf v b).differentiable (by simp)) hC

end TriangularBilliards

namespace TriangularBilliards
open Analysis SpatialSmoothing Filter
open scoped Topology ComplexConjugate

lemma supportedSmoothing_eq_of_supported (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (hA : 2 * R + ε ≤ A)
    {f : DoublePhase → ℂ} (hf : SpatiallyZero Q A f) {z : DoublePhase}
    (hz : z.1.1 ∈ Q.table) :
    supportedSmoothing Q ε R f z = reflectedSmoothing Q ε f z := by
  by_cases hr : 2 * R ≤ Q.clearance z.1.1
  · simp only [supportedSmoothing, vertexCutoff_one Q hR hr, one_smul]
  · have hzero := reflectedSmoothing_zero_near_tips Q hε hf hz (by linarith)
    simp only [supportedSmoothing, hzero, smul_zero]

lemma supportedSmoothing_derivative_eq_of_supported (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (hA : 2 * R + ε ≤ A)
    {f : DoublePhase → ℂ} (hf : SpatiallyZero Q A f) (hm : StronglyMeasurable f)
    {H : ℝ} (hH : ∀ z, ‖f z‖ ≤ H) {z : DoublePhase} (hz : z.1.1 ∈ Q.table) :
    xDerivative (supportedSmoothing Q ε R f) z = reflectedSmoothingGradient Q ε f z (z.1.2 : ℂ) := by
  have he : (fun y => supportedSmoothing Q ε R f ((y,z.1.2),z.2)) =ᶠ[𝓝 z.1.1]
      (fun y => reflectedSmoothing Q ε f ((y,z.1.2),z.2)) := by
    filter_upwards [isOpen_interior.eventually_mem hz] with y hy
    exact supportedSmoothing_eq_of_supported Q hε hR hA hf hy
  change fderiv ℝ (fun y => supportedSmoothing Q ε R f ((y,z.1.2),z.2)) z.1.1 _ = _
  rw [he.fderiv_eq]
  exact congrArg (fun L : ℂ →L[ℝ] ℂ => L (z.1.2 : ℂ))
    (reflectedSmoothing_hasFDerivAt Q hε hm (bounded_spatialSlice_integrable Q hm hH z.1.2 z.2)
      (fun i => bounded_spatialSlice_integrable Q hm hH (reflectedDirection Q i z.1.2) (z.2+1)) z.1.1).fderiv

lemma reflectedSmoothing_direction_memLp (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q)) :
    MemLp (fun z => reflectedSmoothingGradient Q ε f z (z.1.2 : ℂ)) 2 (doubleMeasure Q) :=
  gradientApply_memLp (reflectedSmoothingGradient_memLp Q hε hm hf)
    ((show Continuous (fun z : DoublePhase => (z.1.2 : ℂ)) from
          continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).stronglyMeasurable)
    (fun _z => (Circle.norm_coe _).le)

lemma reflectedSmoothing_supported_generator (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor * ε < R)
    (hsmall : 2 * R * Q.coordinateBound < 1) (hA : 2 * R + ε ≤ A)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {H : ℝ} (hH : ∀ z, ‖f z‖ ≤ H)
    (hf : MemLp f 2 (doubleMeasure Q)) (hs : SpatiallyZero Q A f) :
    (geodesicHilbertFlow Q).HasGenerator
      ((reflectedSmoothing_memLp Q hε hm hf).toLp _)
      ((reflectedSmoothing_direction_memLp Q hε hm hf).toLp _) := by
  have hRp := (mul_pos Q.safetyFactor_pos hε).trans hR
  have h := supportedSmoothing_generator Q hε hR hsmall hm hH
  have h₁ := (supportedSmoothing_memLp Q hε R hm hH).toLp_congr
    (reflectedSmoothing_memLp Q hε hm hf) (by
      filter_upwards [ae_double_position_in_table Q] with z hz
      exact supportedSmoothing_eq_of_supported Q hε hRp hA hs hz)
  have h₂ := (supportedSmoothing_xDerivative_memLp Q hε hRp hm hH).toLp_congr
    (reflectedSmoothing_direction_memLp Q hε hm hf) (by
      filter_upwards [ae_double_position_in_table Q] with z hz
      exact supportedSmoothing_derivative_eq_of_supported Q hε hRp hA hs hm hH hz)
  change (geodesicHilbertFlow Q).HasGenerator
    ((supportedSmoothing_memLp Q hε R hm hH).toLp _) _ at h
  rwa [h₁, h₂] at h

lemma integral_pairing_toLp {A : Type uA} [MeasurableSpace A] {μ : Measure A}
    {f g : A → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ z, f z * conj (g z) ∂μ) = inner ℂ (hg.toLp g) (hf.toLp f) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with z hz hzz
  simp only [hz, hzz, RCLike.inner_apply]

/-- Exact local kernel-transport commutation for a bounded invariant field,
expressed against arbitrary bounded fields with a sufficient vertex margin. -/
lemma invariant_smoothing_direction_pairing_zero (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor * ε < R)
    (hsmall : 2 * R * Q.coordinateBound < 1) (hA : 2 * R + ε ≤ A)
    {f g : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hf : MemLp f 2 (doubleMeasure Q)) (hg : MemLp g 2 (doubleMeasure Q))
    (hfi : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) 0)
    {H : ℝ} (hH : ∀ z, ‖g z‖ ≤ H) (hgs : SpatiallyZero Q A g) :
    (∫ z, reflectedSmoothingGradient Q ε f z (z.1.2 : ℂ) * conj (g z) ∂doubleMeasure Q) = 0 := by
  have h := reflectedSmoothingGradient_adjoint Q hε
    (V := fun c => (c.1 : ℂ)) (show Continuous (fun c : DirectionParity => (c.1 : ℂ)) from
      continuous_subtype_val.comp continuous_fst).stronglyMeasurable
    (fun c => (Circle.norm_coe _).le) (fun i c => rfl) hfm hgm hf hg
  have hgen := reflectedSmoothing_supported_generator Q hε hR hsmall hA hgm hH hg hgs
  have hsk := (geodesicHilbertFlow Q).generator_skew hgen hfi
  simp only [inner_zero_right, zero_add] at hsk
  rw [h, integral_pairing_toLp hf (reflectedSmoothing_direction_memLp Q hε hgm hg), hsk, neg_zero]

end TriangularBilliards

namespace TriangularBilliards
open Analysis SpatialSmoothing Filter
open scoped Topology ComplexConjugate

lemma reflectedSmoothing_direction_norm_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} {H : ℝ} (hH : 0 ≤ H) (hf : ∀ z, ‖f z‖ ≤ H)
    (z : DoublePhase) : ‖reflectedSmoothingGradient Q ε f z (z.1.2 : ℂ)‖ ≤
      4 * derivativeMass * H / ε := by
  calc
    _ ≤ ‖reflectedSmoothingGradient Q ε f z‖ * ‖(z.1.2 : ℂ)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := by rw [Circle.norm_coe, mul_one]; exact reflectedSmoothingGradient_norm_bound Q hε hH hf z

lemma reflectedSmoothing_direction_stronglyMeasurable (Q : Triangle) (ε : ℝ)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) :
    StronglyMeasurable (fun z => reflectedSmoothingGradient Q ε f z (z.1.2 : ℂ)) :=
  isBoundedBilinearMap_apply.continuous.comp_stronglyMeasurable
    ((reflectedSmoothingGradient_stronglyMeasurable Q ε hm).prodMk
      (show Continuous (fun z : DoublePhase => (z.1.2 : ℂ)) from
        continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).stronglyMeasurable)

/-- The actual local X-commutation equation for a bounded invariant field.
No local distributional transport statement is used as an extra hypothesis. -/
lemma invariant_smoothing_direction_zero (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor * ε < R)
    (hsmall : 2 * R * Q.coordinateBound < 1) (hA : 2 * R + ε ≤ A)
    {f : DoublePhase → ℂ} (hfm : StronglyMeasurable f)
    (hf : MemLp f 2 (doubleMeasure Q))
    (hfi : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) 0)
    {H : ℝ} (hH : ∀ z, ‖f z‖ ≤ H) :
    ∀ᵐ z ∂doubleMeasure Q, A ≤ Q.clearance z.1.1 →
      reflectedSmoothingGradient Q ε f z (z.1.2 : ℂ) = 0 := by
  let D : DoublePhase → ℂ := fun z => reflectedSmoothingGradient Q ε f z (z.1.2 : ℂ)
  let E : Set DoublePhase := {z | A ≤ Q.clearance z.1.1}
  let g : DoublePhase → ℂ := E.indicator D
  have hE : MeasurableSet E :=
    measurableSet_le measurable_const
      (Q.clearance_lipschitz.continuous.measurable.comp (measurable_fst.fst))
  have hDm : StronglyMeasurable D := reflectedSmoothing_direction_stronglyMeasurable Q ε hfm
  have hDp : MemLp D 2 (doubleMeasure Q) := reflectedSmoothing_direction_memLp Q hε hfm hf
  have hgm : StronglyMeasurable g := hDm.indicator hE
  have hgp : MemLp g 2 (doubleMeasure Q) := hDp.indicator hE
  have hH₀ : 0 ≤ H := (norm_nonneg _).trans (hH ((0,1),0))
  have hgb : ∀ z, ‖g z‖ ≤ 4 * derivativeMass * H / ε := by
    intro z
    by_cases hz : z ∈ E
    · change ‖E.indicator D z‖ ≤ _
      rw [Set.indicator_of_mem hz]
      exact reflectedSmoothing_direction_norm_bound Q hε hH₀ hH z
    · change ‖E.indicator D z‖ ≤ _
      rw [Set.indicator_of_notMem hz, norm_zero]
      exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) derivativeMass_nonneg) hH₀) hε.le
  have hgs : SpatiallyZero Q A g := by
    intro y _ hy v b
    exact Set.indicator_of_notMem (show ((y,v),b) ∉ E from not_le.mpr hy) D
  have hp := invariant_smoothing_direction_pairing_zero Q hε hR hsmall hA hfm hgm hf hgp hfi hgb hgs
  have he : (∫ z, g z * conj (g z) ∂doubleMeasure Q) = 0 := by
    rw [← hp]
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : z ∈ E
    · simp only [g, Set.indicator_of_mem hz, D]
    · simp only [g, Set.indicator_of_notMem hz, map_zero, mul_zero]
  rw [integral_pairing_toLp hgp hgp, inner_self_eq_zero] at he
  have hgz : g =ᵐ[doubleMeasure Q] 0 := by
    have hh := hgp.coeFn_toLp
    rw [he] at hh
    exact hh.symm.trans (Lp.coeFn_zero _ _ _)
  filter_upwards [hgz] with z hz hza
  change D z = 0
  simpa only [g, Set.indicator_of_mem (show z ∈ E from hza), Pi.zero_apply] using hz

end TriangularBilliards

namespace TriangularBilliards.Analysis
open Filter
open scoped ComplexConjugate

lemma pairing_add_sum_symmetric {A : Type uA} [MeasurableSpace A] {μ : Measure A}
    {f g d e : A → ℂ} {r s : Fin 3 → A → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hd : MemLp d 2 μ) (he : MemLp e 2 μ)
    (hr : ∀ i, MemLp (r i) 2 μ) (hs : ∀ i, MemLp (s i) 2 μ)
    (h0 : (∫ z, d z * conj (g z) ∂μ) = (∫ z, f z * conj (e z) ∂μ))
    (hi : ∀ i, (∫ z, r i z * conj (g z) ∂μ) = (∫ z, f z * conj (s i z) ∂μ)) :
    (∫ z, (d z + ∑ i, r i z) * conj (g z) ∂μ) =
      (∫ z, f z * conj (e z + ∑ i, s i z) ∂μ) := by
  have hD : Integrable (fun z => d z * conj (g z)) μ := hd.integrable_mul (memLp_conj hg)
  have hE : Integrable (fun z => f z * conj (e z)) μ := hf.integrable_mul (memLp_conj he)
  have hR (i) : Integrable (fun z => r i z * conj (g z)) μ := (hr i).integrable_mul (memLp_conj hg)
  have hS (i) : Integrable (fun z => f z * conj (s i z)) μ := hf.integrable_mul (memLp_conj (hs i))
  simp only [add_mul, Finset.sum_mul, map_add, map_sum, mul_add, Finset.mul_sum]
  rw [integral_add hD (integrable_finsetSum Finset.univ (fun i _ => hR i)),
    integral_add hE (integrable_finsetSum Finset.univ (fun i _ => hS i)),
    integral_finsetSum Finset.univ (fun i _ => hR i),
    integral_finsetSum Finset.univ (fun i _ => hS i), h0]
  simp only [hi]

end TriangularBilliards.Analysis

namespace TriangularBilliards
open Analysis SpatialSmoothing Filter
open scoped Topology ComplexConjugate

lemma spatialKernel_stronglyMeasurable (ε : ℝ) {R : ℂ → ℂ} (hR : Measurable R) :
    StronglyMeasurable (fun p : (ℂ × DirectionParity) × ℂ => kernel ε (p.1.1-R p.2)) :=
  ((kernel_contDiff ε).continuous.measurable.comp
    (measurable_fst.fst.sub (hR.comp measurable_snd))).stronglyMeasurable

lemma directS_adjoint (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f g : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hf : MemLp f 2 (doubleMeasure Q)) (hg : MemLp g 2 (doubleMeasure Q)) :
    (∫ z, directS Q ε f z.2 z.1.2 z.1.1 * conj (g z) ∂doubleMeasure Q) =
      (∫ z, f z * conj (directS Q ε g z.2 z.1.2 z.1.1) ∂doubleMeasure Q) := by
  obtain ⟨K,hK⟩ := (kernel_hasCompactSupport hε).exists_bound_of_continuous (kernel_contDiff ε).continuous
  exact doubleKernel_adjoint Q (J := id) (MeasurePreserving.id _) MeasurableEmbedding.id (fun _ => rfl)
    (spatialKernel_stronglyMeasurable ε measurable_id) (spatialKernel_stronglyMeasurable ε measurable_id)
    (fun x y _ => by simpa only [Real.norm_eq_abs] using hK (x-y))
    (fun x y _ => by simpa only [Real.norm_eq_abs] using hK (x-y))
    (fun x y _ => kernel_swap ε x y) hfm hgm hf hg

lemma reflectedS_adjoint (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {f g : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hf : MemLp f 2 (doubleMeasure Q)) (hg : MemLp g 2 (doubleMeasure Q)) :
    (∫ z, reflectedS Q i ε f z.2 z.1.2 z.1.1 * conj (g z) ∂doubleMeasure Q) =
      (∫ z, f z * conj (reflectedS Q i ε g z.2 z.1.2 z.1.1) ∂doubleMeasure Q) := by
  obtain ⟨K,hK⟩ := (kernel_hasCompactSupport hε).exists_bound_of_continuous (kernel_contDiff ε).continuous
  exact doubleKernel_adjoint Q (measurePreserving_directionParity Q i)
    (measurableEmbedding_directionParity Q i) (directionParityReflection_involutive Q i)
    (spatialKernel_stronglyMeasurable ε (wallReflection_contDiff Q i).continuous.measurable)
    (spatialKernel_stronglyMeasurable ε (wallReflection_contDiff Q i).continuous.measurable)
    (fun x y _ => by simpa only [Real.norm_eq_abs] using hK (x-wallReflection Q i y))
    (fun x y _ => by simpa only [Real.norm_eq_abs] using hK (x-wallReflection Q i y))
    (fun x y _ => kernel_wall_swap Q i ε x y) hfm hgm hf hg

lemma directS_memLp (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q)) :
    MemLp (fun z => directS Q ε f z.2 z.1.2 z.1.1) 2 (doubleMeasure Q) :=
  ⟨(directS_stronglyMeasurable Q ε hfm).aestronglyMeasurable, (directS_eLpNorm Q hε hfm).trans_lt hf.eLpNorm_lt_top⟩

lemma reflectedS_memLp (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q)) :
    MemLp (fun z => reflectedS Q i ε f z.2 z.1.2 z.1.1) 2 (doubleMeasure Q) :=
  ⟨(reflectedS_stronglyMeasurable Q i ε hfm).aestronglyMeasurable, (reflectedS_eLpNorm Q i hε hfm).trans_lt hf.eLpNorm_lt_top⟩

lemma reflectedSmoothing_adjoint (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f g : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hf : MemLp f 2 (doubleMeasure Q)) (hg : MemLp g 2 (doubleMeasure Q)) :
    (∫ z, reflectedSmoothing Q ε f z * conj (g z) ∂doubleMeasure Q) =
      (∫ z, f z * conj (reflectedSmoothing Q ε g z) ∂doubleMeasure Q) := by
  exact pairing_add_sum_symmetric hf hg (directS_memLp Q hε hfm hf) (directS_memLp Q hε hgm hg)
    (fun i => reflectedS_memLp Q i hε hfm hf) (fun i => reflectedS_memLp Q i hε hgm hg)
    (directS_adjoint Q hε hfm hgm hf hg) (fun i => reflectedS_adjoint Q i hε hfm hgm hf hg)

end TriangularBilliards

end
end
end
end
end
end

end OAI
end
end

section
section
namespace OAI


open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section

/-! Strongly continuous unitary circle actions and their genuine Fourier
projections. This supplies the angular Hilbert-space calculus, not a new
assumption on a billiard-invariant field. -/
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
namespace TriangularBilliards.Analysis
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {T : ℝ} [Fact (0 < T)]

structure CircleAction (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : ℝ) where
  act : AddCircle T → H →ₗᵢ[ℂ] H
  zero : ∀ u, act 0 u = u
  add : ∀ θ φ u, act (θ + φ) u = act θ (act φ u)
  continuous : ∀ u, Continuous (fun θ => act θ u)

namespace CircleAction
variable (V : CircleAction H T)

omit [Fact (0 < T)] in
lemma act_neg (θ : AddCircle T) (u : H) : V.act (-θ) (V.act θ u) = u := by
  rw [← V.add, neg_add_cancel, V.zero]

omit [Fact (0 < T)] in
lemma adjoint (θ : AddCircle T) (u v : H) :
    inner ℂ (V.act θ u) v = inner ℂ u (V.act (-θ) v) := by
  rw [← (V.act θ).inner_map_map u (V.act (-θ) v), ← V.add, add_neg_cancel, V.zero]

omit [Fact (0 < T)] in
lemma weighted_continuous (j : ℤ) (u : H) :
    Continuous (fun θ : AddCircle T => fourier (-j) θ • V.act θ u) :=
  (fourier (-j)).continuous.smul (V.continuous u)

lemma weighted_integrable (j : ℤ) (u : H) :
    Integrable (fun θ : AddCircle T => fourier (-j) θ • V.act θ u) AddCircle.haarAddCircle :=
  (V.weighted_continuous j u).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [Fact (0 < T)] in
lemma fourier_norm_apply (j : ℤ) (θ : AddCircle T) : ‖fourier j θ‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

lemma coeff_norm_bound (j : ℤ) (u : H) :
    ‖fourierCoeff (fun θ => V.act θ u) j‖ ≤ ‖u‖ := by
  have h := norm_integral_le_of_norm_le_const (μ := AddCircle.haarAddCircle)
    (f := fun θ : AddCircle T => fourier (-j) θ • V.act θ u)
    (Eventually.of_forall fun θ => by
      rw [norm_smul, fourier_norm_apply, (V.act θ).norm_map, one_mul])
  simpa [Measure.real, fourierCoeff] using h

variable [CompleteSpace H]

def projection (j : ℤ) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun u => fourierCoeff (fun θ => V.act θ u) j
      map_add' := fun u v => by
        change (∫ θ, fourier (-j) θ • V.act θ (u+v) ∂AddCircle.haarAddCircle) = _
        simp_rw [map_add, smul_add]
        exact integral_add (V.weighted_integrable j u) (V.weighted_integrable j v)
      map_smul' := fun c u => by
        change (∫ θ, fourier (-j) θ • V.act θ (c • u) ∂AddCircle.haarAddCircle) = _
        simp_rw [map_smul, smul_comm (fourier (-j) _) c]
        exact integral_smul c _ }
    1 (fun u => by simpa using V.coeff_norm_bound j u)

omit [CompleteSpace H] in
lemma projection_apply (j : ℤ) (u : H) :
    V.projection j u = ∫ θ : AddCircle T, fourier (-j) θ • V.act θ u ∂AddCircle.haarAddCircle := rfl

omit [CompleteSpace H] in
lemma projection_norm_le (j : ℤ) (u : H) : ‖V.projection j u‖ ≤ ‖u‖ :=
  V.coeff_norm_bound j u

omit [Fact (0 < T)] in
lemma fourier_arg_add (j : ℤ) (θ φ : AddCircle T) :
    fourier j (θ + φ) = fourier j θ * fourier j φ := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

omit [Fact (0 < T)] in
lemma fourier_arg_neg (j : ℤ) (θ : AddCircle T) :
    fourier j (-θ) = conj (fourier j θ) := by
  simp only [fourier_apply, smul_neg, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]

omit [Fact (0 < T)] in
lemma fourier_neg_mul_self (j : ℤ) (θ : AddCircle T) :
    fourier (-j) θ * fourier j θ = 1 := by
  rw [← fourier_add, neg_add_cancel, fourier_zero]

lemma projection_eigen (j : ℤ) (u : H) (φ : AddCircle T) :
    V.act φ (V.projection j u) = fourier j φ • V.projection j u := by
  rw [projection_apply]
  change (V.act φ).toContinuousLinearMap (∫ θ : AddCircle T, fourier (-j) θ • V.act θ u ∂AddCircle.haarAddCircle) = _
  rw [← (V.act φ).toContinuousLinearMap.integral_comp_comm (V.weighted_integrable j u)]
  change (∫ θ, V.act φ (fourier (-j) θ • V.act θ u) ∂AddCircle.haarAddCircle) = _
  simp_rw [map_smul, ← V.add]
  rw [← integral_add_left_eq_self (μ := AddCircle.haarAddCircle)
    (fun θ => fourier (-j) θ • V.act θ u) φ, ← integral_smul]
  apply integral_congr_ae
  exact Eventually.of_forall fun θ => by
    change fourier (-j) θ • V.act (φ+θ) u = fourier j φ • (fourier (-j) (φ+θ) • V.act (φ+θ) u)
    rw [fourier_arg_add, smul_smul, ← mul_assoc, mul_comm (fourier j φ),
      fourier_neg_mul_self, one_mul]

lemma integral_inner_left {A : Type uA} [MeasurableSpace A] {μ : Measure A}
    {f : A → H} (hf : Integrable f μ) (v : H) :
    (∫ x, inner ℂ (f x) v ∂μ) = inner ℂ (∫ x, f x ∂μ) v := by
  simp_rw [← inner_conj_symm (𝕜 := ℂ) (f _) v]
  rw [integral_conj, integral_inner hf, inner_conj_symm]

lemma projection_adjoint (j : ℤ) (u v : H) :
    inner ℂ (V.projection j u) v = inner ℂ u (V.projection j v) := by
  rw [projection_apply, projection_apply, ← integral_inner_left (V.weighted_integrable j u),
    ← integral_inner (V.weighted_integrable j v)]
  rw [← integral_neg_eq_self (fun θ : AddCircle T =>
    inner ℂ u (fourier (-j) θ • V.act θ v)) AddCircle.haarAddCircle]
  apply integral_congr_ae
  exact Eventually.of_forall fun θ => by
    change inner ℂ ((fourier (-j) θ : ℂ) • V.act θ u) v =
      inner ℂ u ((fourier (-j) (-θ) : ℂ) • V.act (-θ) v)
    rw [inner_smul_left, inner_smul_right, V.adjoint, fourier_arg_neg]

lemma projection_of_eigen {u : H} {k : ℤ}
    (hu : ∀ θ : AddCircle T, V.act θ u = fourier k θ • u) (j : ℤ) :
    V.projection j u = if j = k then u else 0 := by
  rw [projection_apply]
  simp_rw [hu, smul_smul]
  rw [integral_smul_const]
  have he : (∫ θ : AddCircle T, fourier (-j) θ * fourier k θ ∂AddCircle.haarAddCircle) =
      if j = k then (1 : ℂ) else 0 := by
    change fourierCoeff (fourier k) j = _
    rw [fourierCoeff_fourier]
    simp [Pi.single_apply, eq_comm]
  rw [he]
  split_ifs <;> simp

lemma projection_mul (j k : ℤ) (u : H) :
    V.projection j (V.projection k u) = if j = k then V.projection k u else 0 :=
  V.projection_of_eigen (V.projection_eigen k u) j

lemma projection_idem (j : ℤ) (u : H) :
    V.projection j (V.projection j u) = V.projection j u := by
  rw [projection_mul, ite_eq_left rfl]

lemma projection_orthogonal {j k : ℤ} (hjk : j ≠ k) (u v : H) :
    inner ℂ (V.projection j u) (V.projection k v) = 0 := by
  rw [V.projection_adjoint, V.projection_mul, ite_eq_right hjk, inner_zero_right]

/-- The closed Fourier eigenspace, presented as the fixed space of the
proved bounded projection rather than an assumed orthogonal decomposition. -/
def mode (j : ℤ) : Submodule ℂ H :=
  ((V.projection j).toLinearMap - LinearMap.id).ker

omit [CompleteSpace H] in
lemma mem_mode (j : ℤ) (u : H) : u ∈ V.mode j ↔ V.projection j u = u := by
  change V.projection j u - u = 0 ↔ _
  exact sub_eq_zero

lemma projection_mem_mode (j : ℤ) (u : H) : V.projection j u ∈ V.mode j :=
  (V.mem_mode j _).mpr (V.projection_idem j u)

lemma mode_orthogonal : OrthogonalFamily ℂ (fun j => V.mode j)
    (fun j => (V.mode j).subtypeₗᵢ) := by
  intro j k hjk u v
  change inner ℂ (u : H) (v : H) = 0
  rw [← (V.mem_mode j u).mp u.property, ← (V.mem_mode k v).mp v.property]
  exact V.projection_orthogonal hjk u v

lemma projection_norm_sum (u : H) (s : Finset ℤ) :
    ‖∑ j ∈ s, V.projection j u‖ ^ 2 = ∑ j ∈ s, ‖V.projection j u‖ ^ 2 := by
  exact V.mode_orthogonal.norm_sum (fun j => ⟨V.projection j u, V.projection_mem_mode j u⟩) s

lemma projection_inner_self (j : ℤ) (u : H) :
    inner ℂ u (V.projection j u) = (‖V.projection j u‖ ^ 2 : ℝ) := by
  rw [← V.projection_idem j u, ← V.projection_adjoint j u]
  rw [V.projection_idem]
  simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow]

lemma bessel (u : H) (s : Finset ℤ) :
    ∑ j ∈ s, ‖V.projection j u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  have hs := norm_sub_sq (𝕜 := ℂ) u (∑ j ∈ s, V.projection j u)
  rw [V.projection_norm_sum] at hs
  have hi : (inner ℂ u (∑ j ∈ s, V.projection j u)).re =
      ∑ j ∈ s, ‖V.projection j u‖ ^ 2 := by
    rw [inner_sum]
    simp_rw [V.projection_inner_self]
    simp only [Complex.re_sum, Complex.ofReal_re]
  change ‖u - ∑ j ∈ s, V.projection j u‖ ^ 2 =
    ‖u‖ ^ 2 - 2 * (inner ℂ u (∑ j ∈ s, V.projection j u)).re + _ at hs
  rw [hi] at hs
  nlinarith [sq_nonneg ‖u - ∑ j ∈ s, V.projection j u‖]

lemma summable_norm_projection (u : H) : Summable (fun j : ℤ => ‖V.projection j u‖ ^ 2) :=
  summable_of_sum_le (fun _ => sq_nonneg _) (V.bessel u)

lemma summable_projection (u : H) : Summable (fun j : ℤ => V.projection j u) :=
  (V.mode_orthogonal.summable_iff_norm_sq_summable
    (fun j => ⟨V.projection j u, V.projection_mem_mode j u⟩)).mpr (V.summable_norm_projection u)

lemma scalar_coeff (u v : H) (j : ℤ) :
    fourierCoeff (fun θ : AddCircle T => inner ℂ v (V.act θ u)) j =
      inner ℂ v (V.projection j u) := by
  rw [projection_apply, ← integral_inner (V.weighted_integrable j u)]
  unfold fourierCoeff
  apply integral_congr_ae
  exact Eventually.of_forall fun θ => by simp only [inner_smul_right, smul_eq_mul]

lemma eq_zero_of_projections_zero {u : H} (hu : ∀ j, V.projection j u = 0) : u = 0 := by
  let f : AddCircle T → ℂ := fun θ => inner ℂ u (V.act θ u)
  have hc : Continuous f := continuous_const.inner (V.continuous u)
  have hm : MemLp f 2 AddCircle.haarAddCircle := hc.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hz : hm.toLp f = 0 := by
    apply fourierBasis.repr.injective
    ext j
    rw [fourierBasis_repr, congrFun (fourierCoeff_congr_ae hm.coeFn_toLp) j,
      V.scalar_coeff, hu]
    simp
  have hae : f =ᵐ[AddCircle.haarAddCircle] 0 := hm.coeFn_toLp.symm.trans (by rw [hz]; exact Lp.coeFn_zero ℂ 2 AddCircle.haarAddCircle)
  have he : f = 0 := (hc.ae_eq_iff_eq AddCircle.haarAddCircle continuous_const).mp hae
  have hzero := congrFun he 0
  change inner ℂ u (V.act 0 u) = 0 at hzero
  rw [V.zero] at hzero
  exact inner_self_eq_zero.mp hzero

lemma projections_ext {u v : H} (h : ∀ j, V.projection j u = V.projection j v) : u = v := by
  apply sub_eq_zero.mp
  apply V.eq_zero_of_projections_zero
  intro j
  rw [map_sub, h j, sub_self]

lemma tsum_projection (u : H) : ∑' j : ℤ, V.projection j u = u := by
  apply V.projections_ext
  intro j
  rw [(V.projection j).map_tsum (V.summable_projection u)]
  rw [tsum_eq_single j]
  · exact V.projection_idem j u
  · intro k hk
    rw [V.projection_mul, ite_eq_right (Ne.symm hk)]

lemma hasSum_projection (u : H) : HasSum (fun j : ℤ => V.projection j u) u := by
  convert (V.summable_projection u).hasSum using 1
  exact (V.tsum_projection u).symm

/-- An injective sequence of modes escapes every fixed vector strongly. -/
lemma projection_escape {φ : ℕ → ℤ} (hφ : Function.Injective φ) (u : H) :
    Tendsto (fun n => V.projection (φ n) u) atTop (𝓝 0) := by
  exact ((V.summable_projection u).tendsto_cofinite_zero.comp
    hφ.tendsto_cofinite).mono_left atTop_le_cofinite

/-- Uniformly bounded remainder fields of escaping modes converge weakly
in the scalar inner-product sense. No norm convergence of the remainders
is claimed or needed in the endpoint equation. -/
lemma bounded_modes_escape {φ : ℕ → ℤ} (hφ : Function.Injective φ)
    (r : ℕ → H) {C : ℝ} (hC : ∀ n, ‖r n‖ ≤ C)
    (hr : ∀ n, V.projection (φ n) (r n) = r n) (u : H) :
    Tendsto (fun n => inner ℂ u (r n)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n => ‖V.projection (φ n) u‖ * C) atTop (𝓝 0) := by
    simpa using ((V.projection_escape hφ u).norm.mul_const C)
  apply squeeze_zero_norm _ hn
  intro n
  rw [← hr n, ← V.projection_adjoint]
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _))

lemma parity_index_injective (m : ℤ) : Function.Injective (fun n : ℕ => m + 2 * (n : ℤ)) := by
  intro a b h
  change m + 2 * (a : ℤ) = m + 2 * (b : ℤ) at h
  omega

lemma parity_summable (m : ℤ) (u : H) :
    Summable (fun n : ℕ => V.projection (m + 2 * (n : ℤ)) u) :=
  (V.summable_projection u).comp_injective (parity_index_injective m)

/-- The genuine one-sided parity tail of the angular decomposition. -/
def parityTail (m : ℤ) (u : H) : H := ∑' n : ℕ, V.projection (m + 2 * (n : ℤ)) u

lemma parityTail_convergence (m : ℤ) (u : H) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, V.projection (m + 2 * (n : ℤ)) u)
      atTop (𝓝 (V.parityTail m u)) :=
  (V.parity_summable m u).hasSum.tendsto_sum_nat

lemma parityTail_projection_inside (m : ℤ) (u : H) (n : ℕ) :
    V.projection (m + 2 * (n : ℤ)) (V.parityTail m u) =
      V.projection (m + 2 * (n : ℤ)) u := by
  unfold parityTail
  rw [(V.projection _).map_tsum (V.parity_summable m u), tsum_eq_single n]
  · exact V.projection_idem _ u
  · intro k hk
    rw [V.projection_mul, ite_eq_right]
    exact fun h => hk ((parity_index_injective m) h.symm)

lemma parityTail_projection_outside (m : ℤ) (u : H) (j : ℤ)
    (hj : ∀ n : ℕ, j ≠ m + 2 * (n : ℤ)) : V.projection j (V.parityTail m u) = 0 := by
  unfold parityTail
  rw [(V.projection j).map_tsum (V.parity_summable m u)]
  simp only [V.projection_mul, ite_eq_right (hj _), tsum_zero]

end CircleAction
end TriangularBilliards.Analysis

end
end
end
end
end
end
end

end OAI
end
end

section
section
namespace OAI


open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section

namespace TriangularBilliards
open Analysis
open scoped Topology

/-- The actual oriented tangent-circle representation on the double. -/
def angularCircleAction (Q : Triangle) : CircleAction (DoubleL2 Q) (2 * Real.pi) where
  act θ := Lp.compMeasurePreservingₗᵢ ℂ (doubleRotate θ.toCircle)
    (measurePreserving_doubleRotate Q θ.toCircle)
  zero u := by
    apply Lp.ext
    change (Lp.compMeasurePreserving (doubleRotate (AddCircle.toCircle (0 : AddCircle (2 * Real.pi)))) _ u : DoublePhase → ℂ) =ᵐ[doubleMeasure Q] u
    filter_upwards [Lp.coeFn_compMeasurePreserving u
      (measurePreserving_doubleRotate Q (AddCircle.toCircle (0 : AddCircle (2 * Real.pi))))] with z hz
    simpa only [AddCircle.toCircle_zero, doubleRotate_one, Function.comp_apply] using hz
  add θ φ u := by
    apply Lp.ext
    have h₁ := Lp.coeFn_compMeasurePreserving u
      (measurePreserving_doubleRotate Q (θ+φ).toCircle)
    have h₂ := Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving (doubleRotate φ.toCircle)
        (measurePreserving_doubleRotate Q φ.toCircle) u)
      (measurePreserving_doubleRotate Q θ.toCircle)
    have h₃ := (measurePreserving_doubleRotate Q θ.toCircle).quasiMeasurePreserving.ae
      (Lp.coeFn_compMeasurePreserving u (measurePreserving_doubleRotate Q φ.toCircle))
    filter_upwards [h₁, h₂, h₃] with z h1 h2 h3
    change (Lp.compMeasurePreserving (doubleRotate (θ+φ).toCircle) _ u) z =
      (Lp.compMeasurePreserving (doubleRotate θ.toCircle) _ (Lp.compMeasurePreserving (doubleRotate φ.toCircle) _ u)) z
    rw [h1, h2]
    change u (doubleRotate (θ+φ).toCircle z) = (Lp.compMeasurePreserving (doubleRotate φ.toCircle) _ u) (doubleRotate θ.toCircle z)
    rw [h3]
    change u (doubleRotate (θ+φ).toCircle z) = u (doubleRotate φ.toCircle (doubleRotate θ.toCircle z))
    rw [← doubleRotate_mul, AddCircle.toCircle_add, mul_comm]
  continuous u := by
    apply continuous_coinduced_dom.mpr
    change Continuous (fun t : ℝ => Lp.compMeasurePreservingₗᵢ ℂ
      (doubleRotate (AddCircle.toCircle (t : AddCircle (2 * Real.pi)))) _ u)
    have he (t : ℝ) : AddCircle.toCircle (t : AddCircle (2 * Real.pi)) = Circle.exp t := by
      rw [AddCircle.toCircle_apply_mk, div_self (by positivity : 2 * Real.pi ≠ 0), one_mul]
    simp_rw [he]
    exact (angularHilbertFlow Q).continuous u

lemma angularCircleAction_coe (Q : Triangle) (θ : AddCircle (2 * Real.pi)) (u : DoubleL2 Q) :
    ((angularCircleAction Q).act θ u : DoublePhase → ℂ) =ᵐ[doubleMeasure Q]
      u ∘ doubleRotate θ.toCircle :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_doubleRotate Q θ.toCircle)

instance circlePeriodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- These are actual Fourier projections of the double, not externally
specified coefficient operators. -/
def angularProjection (Q : Triangle) (j : ℤ) : DoubleL2 Q →L[ℂ] DoubleL2 Q :=
  (angularCircleAction Q).projection j

lemma angular_projection_complete (Q : Triangle) (u : DoubleL2 Q) :
    HasSum (fun j : ℤ => angularProjection Q j u) u :=
  (angularCircleAction Q).hasSum_projection u

end TriangularBilliards

namespace TriangularBilliards.Analysis.HilbertFlow
open MeasureTheory
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {W : HilbertFlow H}

omit [CompleteSpace H] in
lemma HasGenerator.add {u v a b : H} (h : W.HasGenerator u a) (k : W.HasGenerator v b) :
    W.HasGenerator (u+v) (a+b) := by
  intro t
  rw [map_add, map_add, ← h t, ← k t]
  abel

omit [CompleteSpace H] in
lemma HasGenerator.smul {u a : H} (h : W.HasGenerator u a) (c : ℂ) :
    W.HasGenerator (c • u) (c • a) := by
  intro t
  rw [map_smul, map_smul, ← h t, smul_sub]

lemma HasGenerator.integral {A : Type uA} [MeasurableSpace A] {μ : Measure A}
    {u a : A → H} (hu : Integrable u μ) (ha : Integrable a μ)
    (h : ∀ᵐ x ∂μ, W.HasGenerator (u x) (a x)) :
    W.HasGenerator (∫ x, u x ∂μ) (∫ x, a x ∂μ) := by
  intro t
  change (W.act t).toContinuousLinearMap (∫ x, u x ∂μ) - (∫ x, u x ∂μ) =
    (W.timeIntegral 0 t) (∫ x, a x ∂μ)
  rw [← (W.act t).toContinuousLinearMap.integral_comp_comm hu,
    ← (W.timeIntegral 0 t).integral_comp_comm ha,
    ← integral_sub ((W.act t).toContinuousLinearMap.integrable_comp hu) hu]
  exact integral_congr_ae (h.mono fun x hx => hx t)

end TriangularBilliards.Analysis.HilbertFlow

namespace TriangularBilliards
open Analysis
open scoped Topology

lemma rotated_velocity_decompose (a v : Circle) (b : ZMod 2) :
    (v : ℂ) = (a : ℂ).re • (((if b = 0 then a else a⁻¹) * v : Circle) : ℂ) -
      (a : ℂ).im • transverseVelocity ((if b = 0 then a else a⁻¹) * v) b := by
  have ha := Circle.normSq_coe a
  by_cases hb : b = 0 <;>
    simp only [hb, ite_eq_left, ite_false, transverseVelocity, Circle.coe_mul,
      Circle.coe_inv_eq_conj, Complex.real_smul] <;>
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply] at * <;>
    nlinarith [congrArg (fun t : ℝ => t * (v : ℂ).re) ha,
      congrArg (fun t : ℝ => t * (v : ℂ).im) ha]

lemma rotated_transverse_decompose (a v : Circle) (b : ZMod 2) :
    transverseVelocity v b =
      (a : ℂ).im • (((if b = 0 then a else a⁻¹) * v : Circle) : ℂ) +
      (a : ℂ).re • transverseVelocity ((if b = 0 then a else a⁻¹) * v) b := by
  have ha := Circle.normSq_coe a
  by_cases hb : b = 0 <;>
    simp only [hb, ite_eq_left, ite_false, transverseVelocity, Circle.coe_mul,
      Circle.coe_inv_eq_conj, Complex.real_smul] <;>
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply] at * <;>
    nlinarith [congrArg (fun t : ℝ => t * (v : ℂ).re) ha,
      congrArg (fun t : ℝ => t * (v : ℂ).im) ha]

lemma xDerivative_rotate (a : Circle) (f : DoublePhase → ℂ) (z : DoublePhase) :
    xDerivative (f ∘ doubleRotate a) z =
      (a : ℂ).re • xDerivative f (doubleRotate a z) -
        (a : ℂ).im • yDerivative f (doubleRotate a z) := by
  change fderiv ℝ (fun x => f ((x, _), z.2)) z.1.1 (z.1.2 : ℂ) = _
  rw [rotated_velocity_decompose a z.1.2 z.2, map_sub, map_smul, map_smul]
  rfl

lemma yDerivative_rotate (a : Circle) (f : DoublePhase → ℂ) (z : DoublePhase) :
    yDerivative (f ∘ doubleRotate a) z =
      (a : ℂ).im • xDerivative f (doubleRotate a z) +
        (a : ℂ).re • yDerivative f (doubleRotate a z) := by
  change fderiv ℝ (fun x => f ((x, _), z.2)) z.1.1 (transverseVelocity z.1.2 z.2) = _
  rw [rotated_transverse_decompose a z.1.2 z.2, map_add, map_smul, map_smul]
  rfl

end TriangularBilliards

namespace TriangularBilliards
open Analysis
open scoped Topology NNReal

lemma circleAction_toLp (Q : Triangle) (θ : AddCircle (2 * Real.pi))
    {f : DoublePhase → ℂ} (hf : MemLp f 2 (doubleMeasure Q)) :
    (angularCircleAction Q).act θ (hf.toLp f) =
      (hf.comp_measurePreserving (measurePreserving_doubleRotate Q θ.toCircle)).toLp
        (f ∘ doubleRotate θ.toCircle) :=
  Lp.toLp_compMeasurePreserving hf (measurePreserving_doubleRotate Q θ.toCircle)

lemma rotate_x_memLp (Q : Triangle) (a : Circle) {f : DoublePhase → ℂ}
    (hx : MemLp (xDerivative f) 2 (doubleMeasure Q))
    (hy : MemLp (yDerivative f) 2 (doubleMeasure Q)) :
    MemLp (xDerivative (f ∘ doubleRotate a)) 2 (doubleMeasure Q) := by
  have he : xDerivative (f ∘ doubleRotate a) =
      (a : ℂ).re • (xDerivative f ∘ doubleRotate a) -
        (a : ℂ).im • (yDerivative f ∘ doubleRotate a) := funext (xDerivative_rotate a f)
  rw [he]
  exact ((hx.comp_measurePreserving (measurePreserving_doubleRotate Q a)).const_smul _).sub
    ((hy.comp_measurePreserving (measurePreserving_doubleRotate Q a)).const_smul _)

lemma rotate_y_memLp (Q : Triangle) (a : Circle) {f : DoublePhase → ℂ}
    (hx : MemLp (xDerivative f) 2 (doubleMeasure Q))
    (hy : MemLp (yDerivative f) 2 (doubleMeasure Q)) :
    MemLp (yDerivative (f ∘ doubleRotate a)) 2 (doubleMeasure Q) := by
  have he : yDerivative (f ∘ doubleRotate a) =
      (a : ℂ).im • (xDerivative f ∘ doubleRotate a) +
        (a : ℂ).re • (yDerivative f ∘ doubleRotate a) := funext (yDerivative_rotate a f)
  rw [he]
  exact ((hx.comp_measurePreserving (measurePreserving_doubleRotate Q a)).const_smul _).add
    ((hy.comp_measurePreserving (measurePreserving_doubleRotate Q a)).const_smul _)

lemma seam_rotated_generators {Q : Triangle} {f : DoublePhase → ℂ}
    (hs : SeamCompatible Q f)
    (hd : ∀ v b, Differentiable ℝ (fun x => f ((x,v),b)))
    {C : ℝ≥0} (hC : ∀ x v b, ‖fderiv ℝ (fun y => f ((y,v),b)) x‖ ≤ C)
    (hf : MemLp f 2 (doubleMeasure Q))
    (hx : MemLp (xDerivative f) 2 (doubleMeasure Q))
    (hy : MemLp (yDerivative f) 2 (doubleMeasure Q))
    (θ : AddCircle (2 * Real.pi)) :
    (geodesicHilbertFlow Q).HasGenerator ((angularCircleAction Q).act θ (hf.toLp f))
      ((θ.toCircle : ℂ).re • (angularCircleAction Q).act θ (hx.toLp (xDerivative f)) -
        (θ.toCircle : ℂ).im • (angularCircleAction Q).act θ (hy.toLp (yDerivative f))) ∧
    (transverseHilbertFlow Q).HasGenerator ((angularCircleAction Q).act θ (hf.toLp f))
      ((θ.toCircle : ℂ).im • (angularCircleAction Q).act θ (hx.toLp (xDerivative f)) +
        (θ.toCircle : ℂ).re • (angularCircleAction Q).act θ (hy.toLp (yDerivative f))) := by
  let a := θ.toCircle
  have hxf := rotate_x_memLp Q a hx hy
  have hyf := rotate_y_memLp Q a hx hy
  have h₁ := seam_geodesic_generator (hs.rotate a)
    (fun v b => hd ((if b = 0 then a else a⁻¹) * v) b)
    (fun x v b => hC x ((if b = 0 then a else a⁻¹) * v) b)
    (hf.comp_measurePreserving (measurePreserving_doubleRotate Q a)) hxf
  have h₂ := seam_transverse_generator (hs.rotate a)
    (fun v b => hd ((if b = 0 then a else a⁻¹) * v) b)
    (fun x v b => hC x ((if b = 0 then a else a⁻¹) * v) b)
    (hf.comp_measurePreserving (measurePreserving_doubleRotate Q a)) hyf
  rw [← circleAction_toLp Q θ hf] at h₁ h₂
  have ex : hxf.toLp _ = (a : ℂ).re • (angularCircleAction Q).act θ (hx.toLp _) -
      (a : ℂ).im • (angularCircleAction Q).act θ (hy.toLp _) := by
    apply Lp.ext
    filter_upwards [hxf.coeFn_toLp,
      Lp.coeFn_sub ((a : ℂ).re • (angularCircleAction Q).act θ (hx.toLp _))
        ((a : ℂ).im • (angularCircleAction Q).act θ (hy.toLp _)),
      Lp.coeFn_smul (a : ℂ).re ((angularCircleAction Q).act θ (hx.toLp _)),
      Lp.coeFn_smul (a : ℂ).im ((angularCircleAction Q).act θ (hy.toLp _)),
      angularCircleAction_coe Q θ (hx.toLp _), angularCircleAction_coe Q θ (hy.toLp _),
      (measurePreserving_doubleRotate Q a).quasiMeasurePreserving.ae hx.coeFn_toLp,
      (measurePreserving_doubleRotate Q a).quasiMeasurePreserving.ae hy.coeFn_toLp]
      with z h0 h1 h2 h3 h4 h5 h6 h7
    simp only [Pi.sub_apply, Pi.smul_apply] at h1 h2 h3
    rw [h0, h1, h2, h3, h4, h5]
    change _ = (a : ℂ).re • (hx.toLp _) (doubleRotate a z) -
      (a : ℂ).im • (hy.toLp _) (doubleRotate a z)
    rw [h6, h7, xDerivative_rotate]
  have ey : hyf.toLp _ = (a : ℂ).im • (angularCircleAction Q).act θ (hx.toLp _) +
      (a : ℂ).re • (angularCircleAction Q).act θ (hy.toLp _) := by
    apply Lp.ext
    filter_upwards [hyf.coeFn_toLp,
      Lp.coeFn_add ((a : ℂ).im • (angularCircleAction Q).act θ (hx.toLp _))
        ((a : ℂ).re • (angularCircleAction Q).act θ (hy.toLp _)),
      Lp.coeFn_smul (a : ℂ).im ((angularCircleAction Q).act θ (hx.toLp _)),
      Lp.coeFn_smul (a : ℂ).re ((angularCircleAction Q).act θ (hy.toLp _)),
      angularCircleAction_coe Q θ (hx.toLp _), angularCircleAction_coe Q θ (hy.toLp _),
      (measurePreserving_doubleRotate Q a).quasiMeasurePreserving.ae hx.coeFn_toLp,
      (measurePreserving_doubleRotate Q a).quasiMeasurePreserving.ae hy.coeFn_toLp]
      with z h0 h1 h2 h3 h4 h5 h6 h7
    simp only [Pi.add_apply, Pi.smul_apply] at h1 h2 h3
    rw [h0, h1, h2, h3, h4, h5]
    change _ = (a : ℂ).im • (hx.toLp _) (doubleRotate a z) +
      (a : ℂ).re • (hy.toLp _) (doubleRotate a z)
    rw [h6, h7, yDerivative_rotate]
  exact ⟨by simpa only [ex] using h₁, by simpa only [ey] using h₂⟩

end TriangularBilliards

namespace TriangularBilliards.Analysis
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : ℝ} [Fact (0 < T)]

/-- Covariant first-derivative data, stated as actual generator graphs.
The smooth seam producer below supplies these graphs for billiard fields. -/
def RotationalCR (X Y : HilbertFlow H) (V : CircleAction H T) (u a b : H) : Prop :=
  ∀ θ, X.HasGenerator (V.act θ u)
      (fourier (-1) θ • V.act θ a + fourier 1 θ • V.act θ b) ∧
    Y.HasGenerator (V.act θ u)
      (Complex.I • (fourier (-1) θ • V.act θ a - fourier 1 θ • V.act θ b))

namespace RotationalCR
variable {X Y : HilbertFlow H} {V : CircleAction H T} {u a b : H}

omit [CompleteSpace H] [Fact (0 < T)] in
lemma generators (h : RotationalCR X Y V u a b) :
    X.HasGenerator u (a+b) ∧ Y.HasGenerator u (Complex.I • (a-b)) := by
  simpa only [fourier_apply, smul_zero, AddCircle.toCircle_zero, Circle.coe_one, one_smul,
    V.zero] using h 0

lemma projection (h : RotationalCR X Y V u a b) (j : ℤ) :
    X.HasGenerator (V.projection j u) (V.projection (j+1) a + V.projection (j-1) b) ∧
    Y.HasGenerator (V.projection j u)
      (Complex.I • (V.projection (j+1) a - V.projection (j-1) b)) := by
  have hx (θ : AddCircle T) : X.HasGenerator (fourier (-j) θ • V.act θ u)
      (fourier (-(j+1)) θ • V.act θ a + fourier (-(j-1)) θ • V.act θ b) := by
    have hh := (h θ).1.smul (fourier (-j) θ)
    simpa only [smul_add, smul_smul, ← fourier_add, show -j + -1 = -(j+1) by ring,
      show -j + 1 = -(j-1) by ring] using hh
  have hy (θ : AddCircle T) : Y.HasGenerator (fourier (-j) θ • V.act θ u)
      (Complex.I • (fourier (-(j+1)) θ • V.act θ a - fourier (-(j-1)) θ • V.act θ b)) := by
    have hh := (h θ).2.smul (fourier (-j) θ)
    rw [smul_comm (fourier (-j) θ) Complex.I] at hh
    simpa only [smul_sub, smul_smul, ← fourier_add, show -j + -1 = -(j+1) by ring,
      show -j + 1 = -(j-1) by ring] using hh
  have hxi := HilbertFlow.HasGenerator.integral (V.weighted_integrable j u)
    ((V.weighted_integrable (j+1) a).add (V.weighted_integrable (j-1) b))
    (Filter.Eventually.of_forall hx)
  have hyi := HilbertFlow.HasGenerator.integral (V.weighted_integrable j u)
    (((V.weighted_integrable (j+1) a).sub (V.weighted_integrable (j-1) b)).smul Complex.I)
    (Filter.Eventually.of_forall hy)
  simp only [Pi.add_apply] at hxi
  simp only [Pi.sub_apply, Pi.smul_apply] at hyi
  rw [integral_add (V.weighted_integrable (j+1) a) (V.weighted_integrable (j-1) b)] at hxi
  rw [integral_smul, integral_sub (V.weighted_integrable (j+1) a)
    (V.weighted_integrable (j-1) b)] at hyi
  exact ⟨hxi, hyi⟩

end RotationalCR
end TriangularBilliards.Analysis

end
end
end
end
end
end
end

end OAI
end
end

section
section
namespace OAI


open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section

namespace TriangularBilliards.Analysis
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : ℝ} [Fact (0 < T)]
namespace RotationalCR
variable {X Y : HilbertFlow H} {V : CircleAction H T} {u a b : H}

lemma projection_covariant (h : RotationalCR X Y V u a b) (j : ℤ) :
    RotationalCR X Y V (V.projection j u) (V.projection (j+1) a) (V.projection (j-1) b) := by
  intro θ
  have hx := (h.projection j).1.smul (fourier j θ)
  have hy := (h.projection j).2.smul (fourier j θ)
  simp only [V.projection_eigen]
  have ha : fourier (-1) θ * fourier (j+1) θ = fourier j θ := by
    rw [← fourier_add]; congr 2; ring
  have hb : fourier 1 θ * fourier (j-1) θ = fourier j θ := by
    rw [← fourier_add]; congr 2; ring
  rw [smul_smul, ha, smul_smul, hb]
  constructor
  · simpa only [smul_add] using hx
  · simpa only [smul_comm (fourier j θ) Complex.I, smul_sub] using hy

omit [CompleteSpace H] [Fact (0 < T)] in
lemma add {v c d : H} (h : RotationalCR X Y V u a b) (k : RotationalCR X Y V v c d) :
    RotationalCR X Y V (u+v) (a+c) (b+d) := by
  intro θ
  have hx := (h θ).1.add (k θ).1
  have hy := (h θ).2.add (k θ).2
  simp only [map_add, smul_add]
  constructor
  · convert hx using 1; abel
  · convert hy using 1; module

omit [CompleteSpace H] [Fact (0 < T)] in
lemma smul (h : RotationalCR X Y V u a b) (c : ℂ) :
    RotationalCR X Y V (c • u) (c • a) (c • b) := by
  intro θ
  have hx := (h θ).1.smul c
  have hy := (h θ).2.smul c
  simp only [map_smul]
  constructor
  · convert hx using 1; module
  · convert hy using 1; module

end RotationalCR
end TriangularBilliards.Analysis
namespace TriangularBilliards.Analysis
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : ℝ} [Fact (0 < T)]
namespace RotationalCR
variable {X Y : HilbertFlow H} {V : CircleAction H T} {u a b aa c bb : H}

omit [Fact (0 < T)] in
lemma norm_eq_of_second (h : RotationalCR X Y V u a b)
    (ha : RotationalCR X Y V a aa c) (hb : RotationalCR X Y V b c bb) : ‖a‖ = ‖b‖ := by
  obtain ⟨hxu,hyu⟩ := h.generators
  obtain ⟨hxa,hya⟩ := ha.generators
  obtain ⟨hxb,hyb⟩ := hb.generators
  have hxy : X.HasGenerator (Complex.I • (a-b)) (Complex.I • (aa-bb)) := by
    have hh := (hxa.add (hxb.smul (-1))).smul Complex.I
    convert hh using 1 <;> module
  have hyx : Y.HasGenerator (a+b) (Complex.I • (aa-bb)) := by
    have hh := hya.add hyb
    convert hh using 1
    module
  have hn := HilbertFlow.commuting_generators_CR hxu hyu hxy hyx
  have h₁ : a + b + Complex.I • (Complex.I • (a-b)) = (2 : ℂ) • b := by
    rw [smul_smul, Complex.I_mul_I]; module
  have h₂ : a + b - Complex.I • (Complex.I • (a-b)) = (2 : ℂ) • a := by
    rw [smul_smul, Complex.I_mul_I]; module
  rw [h₁, h₂, norm_smul, norm_smul] at hn
  norm_num at hn
  linarith

lemma projected_norm_eq (h : RotationalCR X Y V u a b)
    (ha : RotationalCR X Y V a aa c) (hb : RotationalCR X Y V b c bb) (j : ℤ) :
    ‖V.projection (j+1) a‖ = ‖V.projection (j-1) b‖ := by
  apply norm_eq_of_second (h.projection_covariant j)
    (c := V.projection j c) (aa := V.projection (j+2) aa) (bb := V.projection (j-2) bb)
  · convert ha.projection_covariant (j+1) using 1 <;> congr 2 <;> ring
  · convert hb.projection_covariant (j-1) using 1 <;> congr 2 <;> ring

end RotationalCR

omit [CompleteSpace H] in
lemma real_parts_CR_algebra (z : ℂ) (x y : H) :
    (z.re : ℂ) • x - (z.im : ℂ) • y =
      conj z • ((1/2 : ℂ) • (x-Complex.I • y)) + z • ((1/2 : ℂ) • (x+Complex.I • y)) := by
  have hr : (z.re : ℂ) = (conj z + z) / 2 := by apply Complex.ext <;> simp
  have hi : (z.im : ℂ) = (z-conj z) / (2*Complex.I) := by
    apply Complex.ext <;> simp [Complex.div_re, Complex.div_im, Complex.normSq_apply]; ring
  rw [hr, hi]
  simp only [div_eq_mul_inv, mul_inv_rev, Complex.inv_I]
  module

omit [CompleteSpace H] in
lemma imag_parts_CR_algebra (z : ℂ) (x y : H) :
    (z.im : ℂ) • x + (z.re : ℂ) • y =
      Complex.I • (conj z • ((1/2 : ℂ) • (x-Complex.I • y)) -
        z • ((1/2 : ℂ) • (x+Complex.I • y))) := by
  have hr : (z.re : ℂ) = (conj z + z) / 2 := by apply Complex.ext <;> simp
  have hi : (z.im : ℂ) = (z-conj z) / (2*Complex.I) := by
    apply Complex.ext <;> simp [Complex.div_re, Complex.div_im, Complex.normSq_apply]; ring
  rw [hr, hi]
  simp only [div_eq_mul_inv, mul_inv_rev, Complex.inv_I]
  match_scalars
  all_goals ring_nf
  all_goals simp only [Complex.I_sq, mul_neg, mul_one]
  all_goals ring

end TriangularBilliards.Analysis

namespace TriangularBilliards.Analysis.CircleAction
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : ℝ} [Fact (0 < T)] (V : CircleAction H T)

lemma projection_commute (L : H →L[ℂ] H)
    (hL : ∀ θ u, L (V.act θ u) = V.act θ (L u)) (j : ℤ) (u : H) :
    L (V.projection j u) = V.projection j (L u) := by
  rw [V.projection_apply, V.projection_apply, ← L.integral_comp_comm (V.weighted_integrable j u)]
  simp only [map_smul, hL]

lemma bessel_reindex {ι : Type uIota} (φ : ι → ℤ) (hφ : Function.Injective φ)
    (u : H) (s : Finset ι) : ∑ i ∈ s, ‖V.projection (φ i) u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  classical
  have hh := V.bessel u (s.image φ)
  rwa [Finset.sum_image (fun i _ k _ hik => hφ hik)] at hh

end TriangularBilliards.Analysis.CircleAction
/-! The real Hilbert formulation applies to the realification of a complex
L² space: real parts of complex inner products are real inner products. -/

open Filter Finset Set
open scoped Topology BigOperators

noncomputable section

namespace TriangularBilliards.Analytic

/-- The finite Cauchy–Schwarz bound used in the localized parity recurrence. -/
lemma sum_products_le {ι : Type uIota} (s : Finset ι) (a b : ι → ℝ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : (∑ i ∈ s, (a i) ^ 2) ≤ A ^ 2)
    (hb : (∑ i ∈ s, (b i) ^ 2) ≤ B ^ 2) :
    (∑ i ∈ s, a i * b i) ≤ A * B := by
  calc
    (∑ i ∈ s, a i * b i) ≤
        Real.sqrt (∑ i ∈ s, (a i) ^ 2) * Real.sqrt (∑ i ∈ s, (b i) ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt s a b
    _ ≤ Real.sqrt (A ^ 2) * Real.sqrt (B ^ 2) :=
      mul_le_mul (Real.sqrt_le_sqrt ha) (Real.sqrt_le_sqrt hb)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = A * B := by rw [Real.sqrt_sq hA, Real.sqrt_sq hB]

/-- Exact finite telescoping plus localization. The sequences `a` and `b`
are the norms of the two factors restricted to the spatial support of Xw. -/
lemma parity_energy_finite (D a b : ℕ → ℝ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrec : ∀ k, D k - D (k + 1) ≤ a k * b k)
    (ha : ∀ n, (∑ k ∈ range n, (a k) ^ 2) ≤ A ^ 2)
    (hb : ∀ n, (∑ k ∈ range n, (b k) ^ 2) ≤ B ^ 2)
    (n : ℕ) : D 0 - D n ≤ A * B := by
  calc
    D 0 - D n = ∑ k ∈ range n, (D k - D (k + 1)) :=
      (sum_range_sub' D n).symm
    _ ≤ ∑ k ∈ range n, a k * b k := sum_le_sum fun k _ => hrec k
    _ ≤ A * B := sum_products_le (range n) a b hA hB (ha n) (hb n)

/-- The infinite-tail passage in the energy estimate.
Only the regularized test field needs its terminal energies to tend to zero;
no decay is required of the invariant field. -/
lemma parity_energy (D a b : ℕ → ℝ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrec : ∀ k, D k - D (k + 1) ≤ a k * b k)
    (ha : ∀ n, (∑ k ∈ range n, (a k) ^ 2) ≤ A ^ 2)
    (hb : ∀ n, (∑ k ∈ range n, (b k) ^ 2) ≤ B ^ 2)
    (hD : Tendsto D atTop (𝓝 0)) : D 0 ≤ A * B := by
  have hlim : Tendsto (fun n => D 0 - D n) atTop (𝓝 (D 0)) := by
    simpa using tendsto_const_nhds.sub hD
  exact le_of_tendsto' hlim (parity_energy_finite D a b hA hB hrec ha hb)

section RealHilbert

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The norm-difference identity for the Cauchy–Riemann recurrence. -/
lemma inner_sum_difference (u v : E) :
    inner ℝ (u + v) (u - v) = ‖u‖ ^ 2 - ‖v‖ ^ 2 := by
  simp only [inner_add_left, inner_sub_right, real_inner_self_eq_norm_sq]
  rw [real_inner_comm v u]
  ring

/-- A version of the energy estimate with the Hilbert-space coefficient
factors still visible. The equality of the two Cauchy–Riemann norms enters
as `hnorm`; it is not asserted for nonsmooth invariant functions here. -/
lemma coefficient_energy (a b : ℕ → E) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hnorm : ∀ k, ‖a k‖ = ‖b k‖)
    (hX : ∀ n, (∑ k ∈ range n, ‖a k + b (k + 1)‖ ^ 2) ≤ A ^ 2)
    (hY : ∀ n, (∑ k ∈ range n, ‖a k - b (k + 1)‖ ^ 2) ≤ B ^ 2)
    (htail : Tendsto (fun n => ‖a n‖ ^ 2) atTop (𝓝 0)) :
    ‖a 0‖ ^ 2 ≤ A * B := by
  apply parity_energy (fun n => ‖a n‖ ^ 2)
    (fun n => ‖a n + b (n + 1)‖) (fun n => ‖a n - b (n + 1)‖)
    hA hB ?_ hX hY htail
  intro k
  rw [hnorm (k + 1), ← inner_sum_difference]
  exact real_inner_le_norm _ _

end RealHilbert

end TriangularBilliards.Analytic

namespace TriangularBilliards.Analysis.CircleAction
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : ℝ} [Fact (0 < T)] (V : CircleAction H T)

omit [CompleteSpace H] in
lemma real_inner_sum_sub (a b : H) :
    (inner ℂ (a+b) (a-b)).re = ‖a‖^2 - ‖b‖^2 := by
  simp only [inner_add_left, inner_sub_right, inner_self_eq_norm_sq_to_K,
    RCLike.ofReal_eq_complex_ofReal, Complex.add_re, Complex.sub_re, ← Complex.ofReal_pow, Complex.ofReal_re]
  have hh := inner_re_symm (𝕜 := ℂ) a b
  change (inner ℂ a b).re = (inner ℂ b a).re at hh
  linarith

/-- The support-localized coefficient estimate. `R` is the spatial
restriction operator; angular commutation and self-adjointness are the
only properties of that operator used. Terminal-mode decay follows from
Bessel and is NOT a hypothesis about an invariant field. -/
lemma localized_CR_energy (a b : H) (j : ℤ) (R : H →L[ℂ] H)
    (hR : ∀ θ u, R (V.act θ u) = V.act θ (R u))
    (hRs : ∀ u v, inner ℂ (R u) v = inner ℂ u (R v))
    (hX : R (a+b) = a+b)
    (hnorm : ∀ k : ℤ, ‖V.projection (k+2) a‖ = ‖V.projection k b‖) :
    ‖V.projection (j+1) a‖ ^ 2 ≤ ‖a+b‖ * ‖R (a-b)‖ := by
  let φ : ℕ → ℤ := fun n => j + 1 + 2 * (n : ℤ)
  have hφ : Function.Injective φ := parity_index_injective (j+1)
  have hn (n : ℕ) : ‖V.projection (φ (n+1)) a‖ = ‖V.projection (φ n) b‖ := by
    have he : φ (n+1) = φ n + 2 := by dsimp [φ]; ring
    rw [he, hnorm]
  have hc (n : ℕ) : R (V.projection (φ n) (a+b)) = V.projection (φ n) (a+b) := by
    rw [V.projection_commute R hR, hX]
  have hrec (n : ℕ) : ‖V.projection (φ n) a‖^2 - ‖V.projection (φ (n+1)) a‖^2 ≤
      ‖V.projection (φ n) (a+b)‖ * ‖V.projection (φ n) (R (a-b))‖ := by
    rw [hn n, ← real_inner_sum_sub]
    rw [← map_add, ← map_sub]
    have he := hRs (V.projection (φ n) (a+b)) (V.projection (φ n) (a-b))
    rw [hc n, V.projection_commute R hR] at he
    rw [he]
    exact re_inner_le_norm (𝕜 := ℂ) _ _
  have hd : Tendsto (fun n => ‖V.projection (φ n) a‖ ^ 2) atTop (𝓝 0) := by
    have hh := ((V.projection_escape hφ a).norm).pow 2
    simpa using hh
  have hh := Analytic.parity_energy
    (fun n => ‖V.projection (φ n) a‖^2)
    (fun n => ‖V.projection (φ n) (a+b)‖)
    (fun n => ‖V.projection (φ n) (R (a-b))‖)
    (norm_nonneg (a+b)) (norm_nonneg (R (a-b))) hrec
    (fun n => V.bessel_reindex φ hφ (a+b) (Finset.range n))
    (fun n => V.bessel_reindex φ hφ (R (a-b)) (Finset.range n)) hd
  simpa only [φ, Nat.cast_zero, mul_zero, add_zero] using hh

end TriangularBilliards.Analysis.CircleAction

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
end

section
section
namespace OAI


open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Finset Set
open scoped Topology BigOperators
noncomputable section

namespace TriangularBilliards
open Analysis
open MeasureTheory Filter
open scoped ComplexConjugate NNReal
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

lemma seam_rotationalCR {Q : Triangle} {f : DoublePhase → ℂ}
    (hs : SeamCompatible Q f)
    (hd : ∀ v b, Differentiable ℝ (fun x => f ((x,v),b)))
    {C : ℝ≥0} (hC : ∀ x v b, ‖fderiv ℝ (fun y => f ((y,v),b)) x‖ ≤ C)
    (hf : MemLp f 2 (doubleMeasure Q))
    (hx : MemLp (xDerivative f) 2 (doubleMeasure Q))
    (hy : MemLp (yDerivative f) 2 (doubleMeasure Q)) :
    RotationalCR (geodesicHilbertFlow Q) (transverseHilbertFlow Q) (angularCircleAction Q)
      (hf.toLp f) ((1/2 : ℂ) • (hx.toLp _ - Complex.I • hy.toLp _))
      ((1/2 : ℂ) • (hx.toLp _ + Complex.I • hy.toLp _)) := by
  intro θ
  obtain ⟨h₁,h₂⟩ := seam_rotated_generators hs hd hC hf hx hy θ
  simp only [fourier_neg, fourier_one,
    map_smul, map_sub, map_add]
  constructor
  · rw [← real_parts_CR_algebra, Complex.coe_smul, Complex.coe_smul]
    exact h₁
  · rw [← imag_parts_CR_algebra, Complex.coe_smul, Complex.coe_smul]
    exact h₂

/-- The second spatial jet on the actual smooth seam core. No spectral
regularity of an invariant is assumed in this lemma. -/
lemma seam_projected_CR_norms {Q : Triangle} {f : DoublePhase → ℂ}
    (hs : SeamCompatible Q f)
    (hd : ∀ v b, ContDiff ℝ ∞ (fun x => f ((x,v),b)))
    {C Cx Cy : ℝ≥0}
    (hC : ∀ x v b, ‖fderiv ℝ (fun y => f ((y,v),b)) x‖ ≤ C)
    (hCx : ∀ x v b, ‖fderiv ℝ (fun y => xDerivative f ((y,v),b)) x‖ ≤ Cx)
    (hCy : ∀ x v b, ‖fderiv ℝ (fun y => yDerivative f ((y,v),b)) x‖ ≤ Cy)
    (hf : MemLp f 2 (doubleMeasure Q))
    (hx : MemLp (xDerivative f) 2 (doubleMeasure Q))
    (hy : MemLp (yDerivative f) 2 (doubleMeasure Q))
    (hxx : MemLp (xDerivative (xDerivative f)) 2 (doubleMeasure Q))
    (hxy : MemLp (xDerivative (yDerivative f)) 2 (doubleMeasure Q))
    (hyy : MemLp (yDerivative (yDerivative f)) 2 (doubleMeasure Q))
    (j : ℤ) :
    ‖(angularCircleAction Q).projection (j+1)
      ((1/2 : ℂ) • (hx.toLp _ - Complex.I • hy.toLp _))‖ =
    ‖(angularCircleAction Q).projection (j-1)
      ((1/2 : ℂ) • (hx.toLp _ + Complex.I • hy.toLp _))‖ := by
  have hd' := fun v b => (hd v b).differentiable (by simp)
  have he : xDerivative (yDerivative f) = yDerivative (xDerivative f) :=
    funext (x_y_commute hd)
  have hyx : MemLp (yDerivative (xDerivative f)) 2 (doubleMeasure Q) := by rwa [← he]
  have heLp : hyx.toLp _ = hxy.toLp _ :=
    MemLp.toLp_congr hyx hxy (Filter.Eventually.of_forall (congrFun he.symm))
  have h := seam_rotationalCR hs hd' hC hf hx hy
  have hₓ := seam_rotationalCR (hs.xDerivative hd')
    (fun v b => (xDerivative_contDiff hd v b).differentiable (by simp)) hCx hx hxx hyx
  have hᵧ := seam_rotationalCR (hs.yDerivative hd')
    (fun v b => (yDerivative_contDiff hd v b).differentiable (by simp)) hCy hy hxy hyy
  rw [heLp] at hₓ
  let aa := (1/4 : ℂ) • (hxx.toLp _ - (2 * Complex.I) • hxy.toLp _ - hyy.toLp _)
  let c := (1/4 : ℂ) • (hxx.toLp _ + hyy.toLp _)
  let bb := (1/4 : ℂ) • (hxx.toLp _ + (2 * Complex.I) • hxy.toLp _ - hyy.toLp _)
  have ha : RotationalCR (geodesicHilbertFlow Q) (transverseHilbertFlow Q)
      (angularCircleAction Q) ((1/2 : ℂ) • (hx.toLp _ - Complex.I • hy.toLp _)) aa c := by
    have hh := (hₓ.add (hᵧ.smul (-Complex.I))).smul (1/2)
    convert hh using 1
    · module
    · dsimp [aa]
      match_scalars
      all_goals ring_nf
      all_goals simp only [Complex.I_sq]
      all_goals ring
    · dsimp [c]
      match_scalars
      all_goals ring_nf
      all_goals simp only [Complex.I_sq]
      all_goals ring
  have hb : RotationalCR (geodesicHilbertFlow Q) (transverseHilbertFlow Q)
      (angularCircleAction Q) ((1/2 : ℂ) • (hx.toLp _ + Complex.I • hy.toLp _)) c bb := by
    have hh := (hₓ.add (hᵧ.smul Complex.I)).smul (1/2)
    convert hh using 1
    · dsimp [c]
      match_scalars
      all_goals ring_nf
      all_goals simp only [Complex.I_sq]
      all_goals ring
    · dsimp [bb]
      match_scalars
      all_goals ring_nf
      all_goals simp only [Complex.I_sq]
      all_goals ring
  exact h.projected_norm_eq ha hb j

end TriangularBilliards

open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal

namespace TriangularBilliards.Analysis

variable {E : Type uE} {F : Type uF} {G : Type uG} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma convolution_uniform_bound (L : E →L[ℝ] F →L[ℝ] G)
    {f : ℂ → E} {g : ℂ → F} (hf : Integrable f) {C : ℝ}
    (hg : ∀ z, ‖g z‖ ≤ C) (x : ℂ) :
    ‖MeasureTheory.convolution (𝕜 := ℝ) f g L volume x‖ ≤ ‖L‖ * (∫ y, ‖f y‖) * C := by
  have hC : 0 ≤ C := (norm_nonneg (g 0)).trans (hg 0)
  unfold MeasureTheory.convolution
  calc
    _ ≤ ∫ y, ‖L (f y) (g (x-y))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ‖L‖ * ‖f y‖ * C := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
        ((hf.norm.const_mul _).mul_const _)
      filter_upwards [] with y
      exact (L.le_opNorm₂ _ _).trans (mul_le_mul_of_nonneg_left (hg _) (by positivity))
    _ = _ := by rw [integral_mul_const, integral_const_mul]

lemma convolution_fderiv_eq (L : E →L[ℝ] F →L[ℝ] G)
    {f : ℂ → E} {g : ℂ → F} (hf : Integrable f)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    fderiv ℝ (MeasureTheory.convolution (𝕜 := ℝ) f g L volume) =
      MeasureTheory.convolution (𝕜 := ℝ) f (fderiv ℝ g) (L.precompR ℂ) volume := by
  funext y
  exact (hgc.hasFDerivAt_convolution_right L hf.locallyIntegrable
    (hg.of_le (by simp)) y).fderiv

lemma convolution_second_formula (L : E →L[ℝ] F →L[ℝ] G)
    {f : ℂ → E} {g : ℂ → F} (hf : Integrable f)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    fderiv ℝ (fderiv ℝ (MeasureTheory.convolution (𝕜 := ℝ) f g L volume)) =
      MeasureTheory.convolution (𝕜 := ℝ) f (fderiv ℝ (fderiv ℝ g)) ((L.precompR ℂ).precompR ℂ) volume := by
  rw [convolution_fderiv_eq L hf hg hgc]
  exact convolution_fderiv_eq (L.precompR ℂ) hf (hg.fderiv_right (by simp)) (hgc.fderiv ℝ)

lemma compact_second_bound {g : ℂ → F} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∃ C : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ C := by
  have hc₁ : HasCompactSupport (fderiv ℝ g) := HasCompactSupport.fderiv (f := g) ℝ hgc
  have hc : HasCompactSupport (fderiv ℝ (fderiv ℝ g)) :=
    HasCompactSupport.fderiv (f := fderiv ℝ g) ℝ hc₁
  have hd : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  have hd' : Continuous (fderiv ℝ (fderiv ℝ g)) := hd.continuous_fderiv (by simp)
  exact HasCompactSupport.exists_bound_of_continuous (f := fderiv ℝ (fderiv ℝ g)) hc hd'

/-- Uniform second jets with an abstract kernel codomain. -/
lemma convolution_second_bound (L : E →L[ℝ] F →L[ℝ] G)
    {g : ℂ → F} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℂ → E), Integrable f → ∀ x,
      ‖fderiv ℝ (fderiv ℝ (MeasureTheory.convolution (𝕜 := ℝ) f g L volume)) x‖ ≤ C * (∫ y, ‖f y‖) := by
  obtain ⟨D,hD⟩ := compact_second_bound hg hgc
  let : NormedAddCommGroup (ℂ →L[ℝ] ℂ →L[ℝ] F) := inferInstance
  let : NormedSpace ℝ (ℂ →L[ℝ] ℂ →L[ℝ] F) := inferInstance
  let : NormedAddCommGroup (ℂ →L[ℝ] ℂ →L[ℝ] G) := inferInstance
  let : NormedSpace ℝ (ℂ →L[ℝ] ℂ →L[ℝ] G) := inferInstance
  let K := (L.precompR ℂ).precompR ℂ
  refine ⟨‖K‖ * D, mul_nonneg (norm_nonneg K)
    ((norm_nonneg (fderiv ℝ (fderiv ℝ g) 0)).trans (hD 0)), ?_⟩
  intro f hf x
  rw [convolution_second_formula L hf hg hgc]
  have hh := convolution_uniform_bound K hf hD x
  convert hh using 1
  exact mul_right_comm _ D _

/-- Joint measurability of a spatial directional derivative requires no
angular differentiability or continuity. -/
lemma measurable_directional_derivative {A : Type uA} [MeasurableSpace A]
    {f : ℂ × A → ℂ} (hf : Measurable f)
    (hd : ∀ a, Differentiable ℝ (fun x => f (x,a)))
    {v : A → ℂ} (hv : Measurable v) :
    Measurable (fun z : ℂ × A => fderiv ℝ (fun x => f (x,z.2)) z.1 (v z.2)) := by
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have ht : Tendsto t atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Filter.Eventually.of_forall ?_⟩
    intro n
    change 1 / ((n : ℝ) + 1) ≠ 0
    positivity
  apply measurable_of_tendsto_metrizable
    (f := fun n z => (t n)⁻¹ • (f (z.1 + t n • v z.2, z.2) - f z))
  · intro n
    exact (measurable_const : Measurable (fun _ : ℂ × A => (t n)⁻¹)).smul ((hf.comp
      ((measurable_fst.add ((measurable_const : Measurable (fun _ : ℂ × A => t n)).smul (hv.comp measurable_snd))).prodMk measurable_snd)).sub hf)
  · apply tendsto_pi_nhds.mpr
    intro z
    have hline : HasDerivAt (fun r : ℝ => z.1 + r • v z.2) (v z.2) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (v z.2)).const_add z.1
    have hf' : HasFDerivAt (fun x => f (x,z.2)) (fderiv ℝ (fun x => f (x,z.2)) z.1)
        (z.1 + (0 : ℝ) • v z.2) := by simpa using (hd z.2 z.1).hasFDerivAt
    have hh := (hf'.comp_hasDerivAt 0 hline).tendsto_slope_zero.comp ht
    simpa only [Function.comp_def, zero_add, zero_smul, add_zero] using hh

lemma second_bound_comp_constant_derivative {f : ℂ → G} {r : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (A : ℂ →L[ℝ] ℂ)
    (hr : ∀ x, HasFDerivAt r A x) {C : ℝ}
    (hC : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C) (x : ℂ) :
    ‖fderiv ℝ (fderiv ℝ (f ∘ r)) x‖ ≤
      ‖(ContinuousLinearMap.compL ℝ ℂ ℂ G).flip A‖ * C * ‖A‖ := by
  let J := (ContinuousLinearMap.compL ℝ ℂ ℂ G).flip A
  have he : fderiv ℝ (f ∘ r) = fun y => J (fderiv ℝ f (r y)) := by
    funext y
    exact (((hf.differentiable (by simp)) (r y)).hasFDerivAt.comp y (hr y)).fderiv
  have hd : HasFDerivAt (fun y => J (fderiv ℝ f (r y)))
      (J.comp ((fderiv ℝ (fderiv ℝ f) (r x)).comp A)) x :=
    J.hasFDerivAt.comp x (((hf.fderiv_right (m := ∞) (by simp)).differentiable
      (by simp) (r x)).hasFDerivAt.comp x (hr x))
  rw [he, hd.fderiv]
  calc
    _ ≤ ‖J‖ * (‖fderiv ℝ (fderiv ℝ f) (r x)‖ * ‖A‖) :=
      (J.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hC (r x)) (norm_nonneg _)) (norm_nonneg A)

lemma norm_second_eq_iterated (f : ℂ → G) (x : ℂ) :
    ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]

lemma second_bound_smul {a : ℂ → ℝ} {f : ℂ → G}
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f)
    {A₀ A₁ A₂ C₀ C₁ C₂ : ℝ}
    (hA₀ : ∀ x, ‖a x‖ ≤ A₀) (hA₁ : ∀ x, ‖fderiv ℝ a x‖ ≤ A₁)
    (hA₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ a) x‖ ≤ A₂)
    (hC₀ : ∀ x, ‖f x‖ ≤ C₀) (hC₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ C₁)
    (hC₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C₂) (x : ℂ) :
    ‖fderiv ℝ (fderiv ℝ (fun y => a y • f y)) x‖ ≤ A₀*C₂ + 2*A₁*C₁ + A₂*C₀ := by
  have hh := norm_iteratedFDeriv_smul_le ha hf x (n := 2) (by norm_cast)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_self, Nat.cast_one,
    Nat.cast_ofNat, Nat.sub_zero, Nat.reduceSub, one_mul,
    norm_iteratedFDeriv_zero, norm_iteratedFDeriv_one,
    ← norm_second_eq_iterated] at hh
  apply hh.trans
  apply add_le_add (add_le_add ?_ ?_) ?_
  · exact mul_le_mul (hA₀ x) (hC₂ x) (norm_nonneg (fderiv ℝ (fderiv ℝ f) x)) ((norm_nonneg (a x)).trans (hA₀ x))
  · exact mul_le_mul (mul_le_mul_of_nonneg_left (hA₁ x) (by norm_num)) (hC₁ x)
      (norm_nonneg _) (by have := (norm_nonneg _).trans (hA₁ x); positivity)
  · exact mul_le_mul (hA₂ x) (hC₀ x) (norm_nonneg (f x)) ((norm_nonneg (fderiv ℝ (fderiv ℝ a) x)).trans (hA₂ x))

lemma second_add {f g : ℂ → G} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : ℂ) :
    fderiv ℝ (fderiv ℝ (fun y => f y + g y)) x =
      fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x := by
  have he : fderiv ℝ (fun y => f y + g y) = fun y => fderiv ℝ f y + fderiv ℝ g y := by
    funext y
    exact fderiv_add (hf.differentiable (by simp) y) (hg.differentiable (by simp) y)
  rw [he]
  exact fderiv_add ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
    ((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)

lemma second_sum {ι : Type uIota} (s : Finset ι) {f : ι → ℂ → G}
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) (x : ℂ) :
    fderiv ℝ (fderiv ℝ (fun y => ∑ i ∈ s, f i y)) x =
      ∑ i ∈ s, fderiv ℝ (fderiv ℝ (f i)) x := by
  have he : fderiv ℝ (fun y => ∑ i ∈ s, f i y) = fun y => ∑ i ∈ s, fderiv ℝ (f i) y := by
    funext y
    exact fderiv_fun_sum (fun i hi => (hf i hi).differentiable (by simp) y)
  rw [he]
  exact fderiv_fun_sum (fun i hi => ((hf i hi).fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)

lemma directional_derivative_bound {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    {C : ℝ} (hC : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C) (v x : ℂ) :
    ‖fderiv ℝ (fun y => fderiv ℝ f y v) x‖ ≤ C * ‖v‖ := by
  have hd := (((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x).hasFDerivAt
  have he : fderiv ℝ (fun y => fderiv ℝ f y v) x = (fderiv ℝ (fderiv ℝ f) x).flip v := by
    simpa using (hd.clm_apply (hasFDerivAt_const v x)).fderiv
  rw [he]
  exact ((by simpa only [ContinuousLinearMap.opNorm_flip] using
      ((fderiv ℝ (fderiv ℝ f) x).flip.le_opNorm v)) : ‖(fderiv ℝ (fderiv ℝ f) x).flip v‖ ≤ ‖fderiv ℝ (fderiv ℝ f) x‖ * ‖v‖).trans
    (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg v))

end TriangularBilliards.Analysis

namespace TriangularBilliards
open Analysis SpatialSmoothing MeasureTheory Filter Set
open scoped Topology ContDiff NNReal

lemma vertexCutoff_sub_one_compact (Q : Triangle) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (fun x => vertexCutoff Q R x - 1) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_iUnion (fun i : Fin 3 => isCompact_closedBall (Q.vertex i) (2*R)))
  intro x hx
  by_contra hn
  have hfar (i : Fin 3) : 2*R ≤ ‖x - Q.vertex i‖ := by
    have hh : x ∉ Metric.closedBall (Q.vertex i) (2*R) := fun hi => hn (mem_iUnion.mpr ⟨i,hi⟩)
    exact (lt_of_not_ge (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hh)).le
  have he : vertexCutoff Q R x = 1 := by
    apply Finset.prod_eq_one
    intro i _
    exact vertexCutoffFactor_one Q hR i (hfar i)
  exact hx (by change vertexCutoff Q R x - 1 = 0; rw [he, sub_self])

lemma vertexCutoff_second_bound (Q : Triangle) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ (vertexCutoff Q R)) x‖ ≤ C := by
  have hc := vertexCutoff_sub_one_compact Q hR
  have hd := (vertexCutoff_contDiff Q R).sub (contDiff_const (c := (1 : ℝ)))
  have he : fderiv ℝ (fun x => vertexCutoff Q R x - 1) = fderiv ℝ (vertexCutoff Q R) := by
    funext x
    exact fderiv_sub_const (x := x) 1
  obtain ⟨C,hC⟩ := compact_second_bound hd hc
  exact ⟨C, by simpa only [he] using hC⟩

lemma spatialSlice_integral_norm_bound (Q : Triangle) {f : DoublePhase → ℂ}
    (hm : StronglyMeasurable f) {H : ℝ} (hf : ∀ z, ‖f z‖ ≤ H)
    (v : Circle) (b : ZMod 2) :
    (∫ x, ‖spatialSlice Q f b v x‖) ≤ (volume Q.table).toReal * H := by
  have hi := bounded_spatialSlice_integrable Q hm hf v b
  let : IsFiniteMeasure (volume.restrict Q.table) := ⟨by simpa using Q.area_lt_top⟩
  rw [spatialSlice]
  simp only [norm_indicator_eq_indicator_norm]
  rw [integral_indicator Q.measurableSet_table]
  calc
    _ ≤ ∫ _x in Q.table, H := integral_mono_ae hi.norm (integrable_const H) (Filter.Eventually.of_forall (fun x => hf ((x,v),b)))
    _ = _ := by simp [Measure.real, smul_eq_mul]

lemma directS_second_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {H : ℝ} (hf : ∀ z, ‖f z‖ ≤ H) :
    ∃ C : ℝ, ∀ x v b, ‖fderiv ℝ (fderiv ℝ (directS Q ε f b v)) x‖ ≤ C := by
  obtain ⟨C,hCp,hC⟩ := convolution_second_bound scalarKernelMap (kernel_contDiff ε) (kernel_hasCompactSupport hε)
  refine ⟨C * ((volume Q.table).toReal * H), fun x v b => ?_⟩
  rw [directS_eq_convolution]
  apply (hC _ ((integrable_indicator_iff Q.measurableSet_table).mpr
    (bounded_spatialSlice_integrable Q hm hf v b)) x).trans
  exact mul_le_mul_of_nonneg_left (spatialSlice_integral_norm_bound Q hm hf v b) hCp

lemma reflectedS_second_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {H : ℝ} (hf : ∀ z, ‖f z‖ ≤ H)
    (i : Fin 3) :
    ∃ C : ℝ, ∀ x v b, ‖fderiv ℝ (fderiv ℝ (reflectedS Q i ε f b v)) x‖ ≤ C := by
  obtain ⟨C,hC⟩ := directS_second_bound Q hε hm hf
  let A := (reflectIsometry (Q.tangent i) (Q.tangent_ne_zero i)).toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨‖(ContinuousLinearMap.compL ℝ ℂ ℂ ℂ).flip A‖ * C * ‖A‖, fun x v b => ?_⟩
  rw [reflectedS_eq_directS]
  exact second_bound_comp_constant_derivative (directS_contDiff Q hε
    (bounded_spatialSlice_integrable Q hm hf (reflectedDirection Q i v) (b+1))) A
    (wallReflection_hasFDerivAt Q i) (fun x => hC x _ _) x

end TriangularBilliards

namespace TriangularBilliards
open Analysis SpatialSmoothing MeasureTheory Filter Set
open scoped Topology ContDiff NNReal

lemma reflectedSmoothing_second_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {H : ℝ} (hf : ∀ z, ‖f z‖ ≤ H) :
    ∃ C : ℝ, ∀ x v b,
      ‖fderiv ℝ (fderiv ℝ (fun y => reflectedSmoothing Q ε f ((y,v),b))) x‖ ≤ C := by
  obtain ⟨C,hC⟩ := directS_second_bound Q hε hm hf
  choose D hD using fun i : Fin 3 => reflectedS_second_bound Q hε hm hf i
  refine ⟨C + ∑ i : Fin 3, D i, fun x v b => ?_⟩
  have hd := directS_contDiff Q hε (bounded_spatialSlice_integrable Q hm hf v b)
  have hr (i : Fin 3) := reflectedS_contDiff Q i hε
    (bounded_spatialSlice_integrable Q hm hf (reflectedDirection Q i v) (b+1))
  change ‖fderiv ℝ (fderiv ℝ (fun y => directS Q ε f b v y + ∑ i : Fin 3, reflectedS Q i ε f b v y)) x‖ ≤ _
  rw [second_add hd (ContDiff.sum (fun i _ => hr i)), second_sum Finset.univ (fun i _ => hr i)]
  have hh : ‖∑ i : Fin 3, fderiv ℝ (fderiv ℝ (reflectedS Q i ε f b v)) x‖ ≤ ∑ i : Fin 3, D i :=
    (norm_sum_le Finset.univ (fun i : Fin 3 => fderiv ℝ (fderiv ℝ (reflectedS Q i ε f b v)) x)).trans
      (Finset.sum_le_sum (fun i _ => hD i x v b))
  apply (norm_add_le (fderiv ℝ (fderiv ℝ (directS Q ε f b v)) x)
    (∑ i : Fin 3, fderiv ℝ (fderiv ℝ (reflectedS Q i ε f b v)) x)).trans
  exact add_le_add (hC x v b) hh

lemma supportedSmoothing_second_bound (Q : Triangle) {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {H : ℝ} (hf : ∀ z, ‖f z‖ ≤ H) :
    ∃ C : ℝ≥0, ∀ x v b,
      ‖fderiv ℝ (fderiv ℝ (fun y => supportedSmoothing Q ε R f ((y,v),b))) x‖ ≤ C := by
  obtain ⟨A,hAp,hA⟩ := exists_vertexCutoff_derivative_bound
  obtain ⟨B,hB⟩ := vertexCutoff_second_bound Q hR
  obtain ⟨C,hC⟩ := reflectedSmoothing_second_bound Q hε hm hf
  have hH : 0 ≤ H := (norm_nonneg (f ((0,1),0))).trans (hf _)
  let M := 1*C + 2*(A/R)*(4*derivativeMass*H/ε) + B*(4*H)
  have hM (x : ℂ) (v : Circle) (b : ZMod 2) :
      ‖fderiv ℝ (fderiv ℝ (fun y => supportedSmoothing Q ε R f ((y,v),b))) x‖ ≤ M := by
    apply second_bound_smul (vertexCutoff_contDiff Q R)
      (reflectedSmoothing_contDiff Q hε (bounded_spatialSlice_integrable Q hm hf v b)
        (fun i => bounded_spatialSlice_integrable Q hm hf (reflectedDirection Q i v) (b+1)))
    · intro y
      rw [Real.norm_eq_abs, abs_of_nonneg (vertexCutoff_mem_Icc Q R y).1]
      exact (vertexCutoff_mem_Icc Q R y).2
    · exact hA Q R hR
    · exact hB
    · intro y
      exact reflectedSmoothing_norm_bound Q hε hH hf ((y,v),b)
    · intro y
      rw [(reflectedSmoothing_hasFDerivAt Q hε hm
        (bounded_spatialSlice_integrable Q hm hf v b)
        (fun i => bounded_spatialSlice_integrable Q hm hf (reflectedDirection Q i v) (b+1)) y).fderiv]
      exact reflectedSmoothingGradient_norm_bound Q hε hH hf ((y,v),b)
    · intro y
      exact hC y v b
  exact ⟨⟨M, (norm_nonneg (fderiv ℝ (fderiv ℝ (fun y => supportedSmoothing Q ε R f ((y,1),0))) 0)).trans (hM 0 1 0)⟩, hM⟩

lemma xDerivative_measurable {f : DoublePhase → ℂ} (hm : Measurable f)
    (hd : ∀ v b, Differentiable ℝ (fun x => f ((x,v),b))) : Measurable (xDerivative f) := by
  have hh := measurable_directional_derivative
    (f := fun z : ℂ × (Circle × ZMod 2) => f ((z.1,z.2.1),z.2.2))
    (hm.comp ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)))
    (fun a => hd a.1 a.2) (v := fun a => (a.1 : ℂ))
    ((show Continuous (fun a : Circle × ZMod 2 => (a.1 : ℂ)) from continuous_subtype_val.comp continuous_fst).measurable)
  exact hh.comp ((measurable_fst.comp measurable_fst).prodMk
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

lemma yDerivative_measurable {f : DoublePhase → ℂ} (hm : Measurable f)
    (hd : ∀ v b, Differentiable ℝ (fun x => f ((x,v),b))) : Measurable (yDerivative f) := by
  have hh := measurable_directional_derivative
    (f := fun z : ℂ × (Circle × ZMod 2) => f ((z.1,z.2.1),z.2.2))
    (hm.comp ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)))
    (fun a => hd a.1 a.2) (v := fun a => transverseVelocity a.1 a.2)
    (by
      unfold transverseVelocity
      exact (Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
        measurable_const measurable_const).mul
        (show Continuous (fun a : Circle × ZMod 2 => (a.1 : ℂ)) from
          continuous_subtype_val.comp continuous_fst).measurable)
  exact hh.comp ((measurable_fst.comp measurable_fst).prodMk
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

end TriangularBilliards

namespace TriangularBilliards
open Analysis MeasureTheory Filter Set
open scoped Topology ContDiff NNReal

lemma norm_transverseVelocity (v : Circle) (b : ZMod 2) : ‖transverseVelocity v b‖ = 1 := by
  unfold transverseVelocity
  split <;> simp [Circle.norm_coe]

lemma xDerivative_fderiv_bound {f : DoublePhase → ℂ}
    (hd : ∀ v b, ContDiff ℝ ∞ (fun x => f ((x,v),b))) {C : ℝ}
    (hC : ∀ x v b, ‖fderiv ℝ (fderiv ℝ (fun y => f ((y,v),b))) x‖ ≤ C)
    (x : ℂ) (v : Circle) (b : ZMod 2) :
    ‖fderiv ℝ (fun y => xDerivative f ((y,v),b)) x‖ ≤ C := by
  simpa only [xDerivative, Circle.norm_coe, mul_one] using
    directional_derivative_bound (hd v b) (fun y => hC y v b) (v : ℂ) x

lemma yDerivative_fderiv_bound {f : DoublePhase → ℂ}
    (hd : ∀ v b, ContDiff ℝ ∞ (fun x => f ((x,v),b))) {C : ℝ}
    (hC : ∀ x v b, ‖fderiv ℝ (fderiv ℝ (fun y => f ((y,v),b))) x‖ ≤ C)
    (x : ℂ) (v : Circle) (b : ZMod 2) :
    ‖fderiv ℝ (fun y => yDerivative f ((y,v),b)) x‖ ≤ C := by
  simpa only [yDerivative, norm_transverseVelocity, mul_one] using
    directional_derivative_bound (hd v b) (fun y => hC y v b) (transverseVelocity v b) x

lemma xDerivative_memLp_of_gradient_bound (Q : Triangle) {f : DoublePhase → ℂ}
    (hm : Measurable f) (hd : ∀ v b, Differentiable ℝ (fun x => f ((x,v),b)))
    {C : ℝ} (hC : ∀ x v b, ‖fderiv ℝ (fun y => f ((y,v),b)) x‖ ≤ C) :
    MemLp (xDerivative f) 2 (doubleMeasure Q) := by
  apply MemLp.of_bound (xDerivative_measurable hm hd).aestronglyMeasurable C
  filter_upwards [] with z
  exact (ContinuousLinearMap.le_opNorm _ _).trans (by
    rw [Circle.norm_coe, mul_one]
    exact hC z.1.1 z.1.2 z.2)

lemma yDerivative_memLp_of_gradient_bound (Q : Triangle) {f : DoublePhase → ℂ}
    (hm : Measurable f) (hd : ∀ v b, Differentiable ℝ (fun x => f ((x,v),b)))
    {C : ℝ} (hC : ∀ x v b, ‖fderiv ℝ (fun y => f ((y,v),b)) x‖ ≤ C) :
    MemLp (yDerivative f) 2 (doubleMeasure Q) := by
  apply MemLp.of_bound (yDerivative_measurable hm hd).aestronglyMeasurable C
  filter_upwards [] with z
  exact (ContinuousLinearMap.le_opNorm _ _).trans (by
    rw [norm_transverseVelocity, mul_one]
    exact hC z.1.1 z.1.2 z.2)

lemma seam_projected_CR_norms_of_bounded_jets {Q : Triangle} {f : DoublePhase → ℂ}
    (hs : SeamCompatible Q f) (hm : Measurable f)
    (hd : ∀ v b, ContDiff ℝ ∞ (fun x => f ((x,v),b)))
    {C D : ℝ≥0}
    (hC : ∀ x v b, ‖fderiv ℝ (fun y => f ((y,v),b)) x‖ ≤ C)
    (hD : ∀ x v b, ‖fderiv ℝ (fderiv ℝ (fun y => f ((y,v),b))) x‖ ≤ D)
    (hf : MemLp f 2 (doubleMeasure Q)) (j : ℤ) :
    let hx := xDerivative_memLp_of_gradient_bound Q hm
      (fun v b => (hd v b).differentiable (by simp)) hC
    let hy := yDerivative_memLp_of_gradient_bound Q hm
      (fun v b => (hd v b).differentiable (by simp)) hC
    ‖(angularCircleAction Q).projection (j+1)
      ((1/2 : ℂ) • (hx.toLp _ - Complex.I • hy.toLp _))‖ =
    ‖(angularCircleAction Q).projection (j-1)
      ((1/2 : ℂ) • (hx.toLp _ + Complex.I • hy.toLp _))‖ := by
  dsimp only
  have hd' := fun v b => (hd v b).differentiable (by simp)
  have hmx := xDerivative_measurable hm hd'
  have hmy := yDerivative_measurable hm hd'
  have hx' := fun v b => (xDerivative_contDiff hd v b).differentiable (by simp)
  have hy' := fun v b => (yDerivative_contDiff hd v b).differentiable (by simp)
  have hX := xDerivative_fderiv_bound hd hD
  have hY := yDerivative_fderiv_bound hd hD
  exact seam_projected_CR_norms hs hd hC hX hY hf _ _
    (xDerivative_memLp_of_gradient_bound Q hmx hx' hX)
    (xDerivative_memLp_of_gradient_bound Q hmy hy' hY)
    (yDerivative_memLp_of_gradient_bound Q hmy hy' hY) j

end TriangularBilliards

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
end

section
section
namespace OAI


open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Finset Set
open scoped Topology BigOperators
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal

open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
namespace TriangularBilliards.Analysis
variable {A : Type uA} [MeasurableSpace A] {μ : Measure A}

def restrictL2 (E : Set A) (hE : MeasurableSet E) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun u => ((Lp.memLp u).indicator hE).toLp (E.indicator u)
      map_add' := fun u v => by
        apply Lp.ext
        filter_upwards [((Lp.memLp (u+v)).indicator hE).coeFn_toLp,
          ((Lp.memLp u).indicator hE).coeFn_toLp,
          ((Lp.memLp v).indicator hE).coeFn_toLp,
          Lp.coeFn_add u v,
          Lp.coeFn_add (((Lp.memLp u).indicator hE).toLp _) (((Lp.memLp v).indicator hE).toLp _)]
          with z h0 h1 h2 h3 h4
        simp only [Pi.add_apply] at h3 h4
        rw [h0, h4, h1, h2]
        by_cases hz : z ∈ E
        · simp only [indicator_of_mem hz]; exact h3
        · simp only [indicator_of_notMem hz, add_zero]
      map_smul' := fun c u => by
        apply Lp.ext
        filter_upwards [((Lp.memLp (c • u)).indicator hE).coeFn_toLp,
          ((Lp.memLp u).indicator hE).coeFn_toLp, Lp.coeFn_smul c u,
          Lp.coeFn_smul c (((Lp.memLp u).indicator hE).toLp _)] with z h0 h1 h2 h3
        simp only [Pi.smul_apply] at h2 h3
        change _ = (c • (((Lp.memLp u).indicator hE).toLp _)) z
        rw [h0, h3, h1]
        by_cases hz : z ∈ E
        · simp only [indicator_of_mem hz]; exact h2
        · simp only [indicator_of_notMem hz, smul_zero] }
    1 (fun u => by
      simp only [one_mul]
      change ‖((Lp.memLp u).indicator hE).toLp _‖ ≤ ‖u‖
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [((Lp.memLp u).indicator hE).coeFn_toLp] with z hz
      rw [hz]
      exact norm_indicator_le_norm_self _ _)

lemma restrictL2_coe (E : Set A) (hE : MeasurableSet E) (u : Lp ℂ 2 μ) :
    (restrictL2 E hE u : A → ℂ) =ᵐ[μ] E.indicator u :=
  ((Lp.memLp u).indicator hE).coeFn_toLp

lemma restrictL2_selfadjoint (E : Set A) (hE : MeasurableSet E) (u v : Lp ℂ 2 μ) :
    inner ℂ (restrictL2 E hE u) v = inner ℂ u (restrictL2 E hE v) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [restrictL2_coe E hE u, restrictL2_coe E hE v] with z hu hv
  rw [hu, hv]
  by_cases hz : z ∈ E
  · simp only [indicator_of_mem hz]
  · simp only [indicator_of_notMem hz, inner_zero_left, inner_zero_right]

lemma restrictL2_fixed (E : Set A) (hE : MeasurableSet E) (u : Lp ℂ 2 μ)
    (hu : ∀ᵐ z ∂μ, z ∉ E → u z = 0) : restrictL2 E hE u = u := by
  apply Lp.ext
  filter_upwards [restrictL2_coe E hE u, hu] with z hz hzz
  rw [hz]
  by_cases hm : z ∈ E
  · exact indicator_of_mem hm _
  · simp only [indicator_of_notMem hm, hzz hm]

lemma restrictL2_commute (E : Set A) (hE : MeasurableSet E)
    (ρ : A → A) (hρ : MeasurePreserving ρ μ μ) (he : ∀ z, ρ z ∈ E ↔ z ∈ E)
    (u : Lp ℂ 2 μ) :
    restrictL2 E hE (Lp.compMeasurePreserving ρ hρ u) =
      Lp.compMeasurePreserving ρ hρ (restrictL2 E hE u) := by
  apply Lp.ext
  filter_upwards [restrictL2_coe E hE (Lp.compMeasurePreserving ρ hρ u),
    Lp.coeFn_compMeasurePreserving u hρ,
    Lp.coeFn_compMeasurePreserving (restrictL2 E hE u) hρ,
    hρ.quasiMeasurePreserving.ae (restrictL2_coe E hE u)] with z h0 h1 h2 h3
  rw [h0, h2]
  change _ = restrictL2 E hE u (ρ z)
  rw [h3]
  by_cases hz : z ∈ E
  · rw [indicator_of_mem hz, indicator_of_mem ((he z).mpr hz)]
    exact h1
  · rw [indicator_of_notMem hz, indicator_of_notMem (fun h => hz ((he z).mp h))]

lemma restrictL2_norm (E : Set A) (hE : MeasurableSet E) (u : Lp ℂ 2 μ) :
    ‖restrictL2 E hE u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [restrictL2_coe E hE u] with z hz
  rw [hz]
  exact norm_indicator_le_norm_self _ _

end TriangularBilliards.Analysis

namespace TriangularBilliards
open Analysis MeasureTheory Filter Set
open scoped ContDiff NNReal
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

lemma spatialRestriction_commute (Q : Triangle) (E : Set ℂ) (hE : MeasurableSet E)
    (θ : AddCircle (2 * Real.pi)) (u : Lp ℂ 2 (doubleMeasure Q)) :
    restrictL2 {z : DoublePhase | z.1.1 ∈ E} (hE.preimage measurable_fst.fst)
        ((angularCircleAction Q).act θ u) =
      (angularCircleAction Q).act θ
        (restrictL2 {z : DoublePhase | z.1.1 ∈ E} (hE.preimage measurable_fst.fst) u) := by
  exact restrictL2_commute _ _ (doubleRotate θ.toCircle)
    (measurePreserving_doubleRotate Q θ.toCircle) (fun _ => Iff.rfl) u

/-- The localized energy bound on the actual smooth core. Every generator
and Fourier projection here is that of the actual billiard double. -/
lemma seam_localized_energy {Q : Triangle} {f : DoublePhase → ℂ}
    (hs : SeamCompatible Q f) (hm : Measurable f)
    (hd : ∀ v b, ContDiff ℝ ∞ (fun x => f ((x,v),b)))
    {C D : ℝ≥0}
    (hC : ∀ x v b, ‖fderiv ℝ (fun y => f ((y,v),b)) x‖ ≤ C)
    (hD : ∀ x v b, ‖fderiv ℝ (fderiv ℝ (fun y => f ((y,v),b))) x‖ ≤ D)
    (hf : MemLp f 2 (doubleMeasure Q))
    (E : Set ℂ) (hE : MeasurableSet E)
    (hX : ∀ᵐ z ∂doubleMeasure Q, z.1.1 ∉ E → xDerivative f z = 0) (j : ℤ) :
    let hx := xDerivative_memLp_of_gradient_bound Q hm
      (fun v b => (hd v b).differentiable (by simp)) hC
    let hy := yDerivative_memLp_of_gradient_bound Q hm
      (fun v b => (hd v b).differentiable (by simp)) hC
    let R := restrictL2 (μ := doubleMeasure Q) {z : DoublePhase | z.1.1 ∈ E} (hE.preimage measurable_fst.fst)
    ∃ dx dy : Lp ℂ 2 (doubleMeasure Q),
      (geodesicHilbertFlow Q).HasGenerator ((angularCircleAction Q).projection j (hf.toLp _)) dx ∧
      (transverseHilbertFlow Q).HasGenerator ((angularCircleAction Q).projection j (hf.toLp _)) dy ∧
      ‖dx‖ ^ 2 ≤ 4 * ‖hx.toLp _‖ * ‖R (hy.toLp _)‖ ∧
      ‖dy‖ ^ 2 ≤ 4 * ‖hx.toLp _‖ * ‖R (hy.toLp _)‖ := by
  dsimp only
  let hx := xDerivative_memLp_of_gradient_bound Q hm
    (fun v b => (hd v b).differentiable (by simp)) hC
  let hy := yDerivative_memLp_of_gradient_bound Q hm
    (fun v b => (hd v b).differentiable (by simp)) hC
  let R := restrictL2 (μ := doubleMeasure Q) {z : DoublePhase | z.1.1 ∈ E} (hE.preimage measurable_fst.fst)
  let a := (1/2 : ℂ) • (hx.toLp _ - Complex.I • hy.toLp _)
  let b := (1/2 : ℂ) • (hx.toLp _ + Complex.I • hy.toLp _)
  have hab : a + b = hx.toLp _ := by dsimp [a,b]; module
  have hsub : a - b = (-Complex.I) • hy.toLp _ := by dsimp [a,b]; module
  have hRx : R (hx.toLp _) = hx.toLp _ := by
    apply restrictL2_fixed
    filter_upwards [hx.coeFn_toLp,hX] with z hz hh
    simpa only [hz, mem_ofPred_eq] using hh
  have hn (k : ℤ) : ‖(angularCircleAction Q).projection (k+2) a‖ =
      ‖(angularCircleAction Q).projection k b‖ := by
    have hh := seam_projected_CR_norms_of_bounded_jets hs hm hd hC hD hf (k+1)
    have hi : k + 1 + 1 = k + 2 := by omega
    simpa only [hi, add_sub_cancel_right] using hh
  have hh := (angularCircleAction Q).localized_CR_energy a b j R
    (spatialRestriction_commute Q E hE) (restrictL2_selfadjoint _ _)
    (by rw [hab]; exact hRx) hn
  have hRsub : ‖R (a-b)‖ = ‖R (hy.toLp _)‖ := by
    rw [hsub, map_smul, norm_smul, norm_neg, Complex.norm_I, one_mul]
  rw [hab, hRsub] at hh
  have hcr := seam_rotationalCR hs (fun v b => (hd v b).differentiable (by simp)) hC hf hx hy
  have hg := hcr.projection j
  have heq : ‖(angularCircleAction Q).projection (j+1) a‖ =
      ‖(angularCircleAction Q).projection (j-1) b‖ :=
    seam_projected_CR_norms_of_bounded_jets hs hm hd hC hD hf j
  let da := (angularCircleAction Q).projection (j+1) a
  let db := (angularCircleAction Q).projection (j-1) b
  refine ⟨da+db, Complex.I • (da-db), hg.1, hg.2, ?_, ?_⟩
  · have hl : ‖da+db‖ ≤ 2 * ‖da‖ := by
      calc _ ≤ ‖da‖ + ‖db‖ := norm_add_le _ _
           _ = _ := by rw [← heq]; ring
    calc
      _ ≤ (2*‖da‖)^2 := by gcongr
      _ = 4*‖da‖^2 := by ring
      _ ≤ _ := by linarith [hh]
  · have hl : ‖Complex.I • (da-db)‖ ≤ 2 * ‖da‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
      calc _ ≤ ‖da‖ + ‖db‖ := norm_sub_le _ _
           _ = _ := by rw [← heq]; ring
    calc
      _ ≤ (2*‖da‖)^2 := by gcongr
      _ = 4*‖da‖^2 := by ring
      _ ≤ _ := by linarith [hh]

end TriangularBilliards

namespace TriangularBilliards
open MeasureTheory Set
namespace Triangle
lemma clearance_sublevel (Q : Triangle) (R : ℝ) :
    {x | Q.clearance x ≤ R} = ⋃ i : Fin 3, Metric.closedBall (Q.vertex i) R := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, ⟨i, rfl⟩, hi⟩ := (finite_range Q.vertex).isCompact.exists_infDist_eq_dist
      (range_nonempty Q.vertex) x
    exact mem_iUnion.mpr ⟨i, by simpa only [Metric.mem_closedBall, ← hi, clearance, mem_ofPred_eq] using hx⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact le_trans (Metric.infDist_le_dist_of_mem (mem_range_self i)) hi

lemma clearance_sublevel_measurable (Q : Triangle) (R : ℝ) :
    MeasurableSet {x | Q.clearance x ≤ R} :=
  measurableSet_le Q.clearance_lipschitz.continuous.measurable measurable_const

lemma clearance_area_bound (Q : Triangle) (R : ℝ) :
    volume {x | Q.clearance x ≤ R} ≤
      3 * (ENNReal.ofReal R) ^ 2 * (NNReal.pi : ℝ≥0∞) := by
  rw [Q.clearance_sublevel]
  calc
    volume (⋃ i : Fin 3, Metric.closedBall (Q.vertex i) R) ≤
      ∑' i : Fin 3, volume (Metric.closedBall (Q.vertex i) R) := measure_iUnion_le _
    _ = 3 * (ENNReal.ofReal R) ^ 2 * (NNReal.pi : ℝ≥0∞) := by
      simp only [Complex.volume_closedBall, tsum_fintype, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end Triangle

/-- The small-tip neighborhood on the actual oriented double. -/
def unsafeSet (Q : Triangle) (R : ℝ) : Set DoublePhase :=
  {z | Q.clearance z.1.1 ≤ R}

lemma unsafeSet_measurable (Q : Triangle) (R : ℝ) : MeasurableSet (unsafeSet Q R) :=
  (Q.clearance_sublevel_measurable R).preimage measurable_fst.fst

lemma unsafeSet_measure_bound (Q : Triangle) (R : ℝ) :
    doubleMeasure Q (unsafeSet Q R) ≤
      (volume Q.table)⁻¹ * (3 * (ENNReal.ofReal R) ^ 2 * (NNReal.pi : ℝ≥0∞)) := by
  have he : unsafeSet Q R = ({x : ℂ | Q.clearance x ≤ R} ×ˢ (univ : Set Circle)) ×ˢ
      (univ : Set (ZMod 2)) := by ext z; simp only [unsafeSet, mem_ofPred_eq, mem_prod,
      mem_univ, and_true]
  rw [he, doubleMeasure, Measure.prod_prod, measure_univ, mul_one,
    phaseMeasure, Measure.prod_prod, measure_univ, mul_one, Measure.smul_apply, smul_eq_mul]
  gcongr
  calc
    volume.restrict Q.table {x | Q.clearance x ≤ R} ≤ volume {x | Q.clearance x ≤ R} :=
      Measure.restrict_apply_le _ _
    _ ≤ _ := Q.clearance_area_bound R

end TriangularBilliards

namespace TriangularBilliards.Analysis
open MeasureTheory Filter Set
variable {A : Type uA} [MeasurableSpace A] {μ : Measure A}
lemma restrictL2_norm_of_bounded (E : Set A) (hE : MeasurableSet E) (hμE : μ E ≠ ⊤)
    {u : Lp ℂ 2 μ} {H : ℝ} (hH : 0 ≤ H) (hu : ∀ᵐ z ∂μ, ‖u z‖ ≤ H) :
    ‖restrictL2 E hE u‖ ≤ H * (μ E).toReal ^ (1/2 : ℝ) := by
  calc
    _ ≤ ‖indicatorConstLp 2 hE hμE (H : ℂ)‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [hu,restrictL2_coe E hE u,
        indicatorConstLp_coeFn (p := 2) (hs := hE) (hμs := hμE) (c := (H : ℂ))] with z hz he hc
      rw [he,hc]
      by_cases h : z ∈ E
      · simpa only [indicator_of_mem h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hH] using hz
      · simp only [indicator_of_notMem h, le_refl]
    _ = _ := by rw [norm_indicatorConstLp (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
                simp [Complex.norm_real, abs_of_nonneg hH, Measure.real]

end TriangularBilliards.Analysis

namespace TriangularBilliards
open Analysis SpatialSmoothing MeasureTheory Filter Set
open scoped Topology ContDiff NNReal
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

lemma vertexCutoff_fderiv_zero_of_large (Q : Triangle) {R : ℝ} (hR : 0 < R) {x : ℂ}
    (hx : 2 * R < Q.clearance x) : fderiv ℝ (vertexCutoff Q R) x = 0 := by
  have he : vertexCutoff Q R =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [((isOpen_lt continuous_const Q.clearance_lipschitz.continuous).mem_nhds hx)] with y hy
    exact vertexCutoff_one Q hR hy.le
  rw [he.fderiv_eq, fderiv_const_apply]

lemma supportedSmoothing_invariant_x_zero (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor * ε < R)
    (hsmall : 2 * R * Q.coordinateBound < 1) (hA : 2 * R + ε ≤ A)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f)
    (hf : MemLp f 2 (doubleMeasure Q))
    (hfi : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) 0)
    {H : ℝ} (hH : ∀ z, ‖f z‖ ≤ H) :
    ∀ᵐ z ∂doubleMeasure Q, z ∉ unsafeSet Q A →
      xDerivative (supportedSmoothing Q ε R f) z = 0 := by
  have hRp : 0 < R := (mul_pos Q.safetyFactor_pos hε).trans hR
  filter_upwards [invariant_smoothing_direction_zero Q hε hR hsmall hA hm hf hfi hH] with z hz hza
  have hb : A < Q.clearance z.1.1 := lt_of_not_ge hza
  have hc : 2 * R < Q.clearance z.1.1 := by linarith
  rw [supportedSmoothing_xDerivative Q hε R hm hH,
    supportedSmoothingGradient, vertexCutoff_fderiv_zero_of_large Q hRp hc,
    vertexCutoff_one Q hRp hc.le, one_smul, ContinuousLinearMap.zero_smulRight, add_zero]
  exact hz hb.le

lemma unsafeSet_real_measure_bound (Q : Triangle) {R : ℝ} (hR : 0 ≤ R) :
    (doubleMeasure Q (unsafeSet Q R)).toReal ≤
      ((volume Q.table).toReal)⁻¹ * (3 * R ^ 2 * Real.pi) := by
  have ht : (volume Q.table)⁻¹ * (3 * (ENNReal.ofReal R)^2 * (NNReal.pi : ℝ≥0∞)) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr Q.area_pos.ne') (by finiteness)
  have hh := ENNReal.toReal_mono ht (unsafeSet_measure_bound Q R)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.toReal_ofReal hR, ENNReal.coe_toReal, NNReal.coe_real_pi] using hh

/-- Generic localized gradient control on an actual smooth seam field, with
its exact tip-neighborhood measure retained. -/
lemma seam_tip_energy {Q : Triangle} {f : DoublePhase → ℂ}
    (hs : SeamCompatible Q f) (hm : Measurable f)
    (hd : ∀ v b, ContDiff ℝ ∞ (fun x => f ((x,v),b)))
    {C D : ℝ≥0}
    (hC : ∀ x v b, ‖fderiv ℝ (fun y => f ((y,v),b)) x‖ ≤ C)
    (hD : ∀ x v b, ‖fderiv ℝ (fderiv ℝ (fun y => f ((y,v),b))) x‖ ≤ D)
    (hf : MemLp f 2 (doubleMeasure Q)) (A : ℝ)
    (hX : ∀ᵐ z ∂doubleMeasure Q, z ∉ unsafeSet Q A → xDerivative f z = 0) (j : ℤ) :
    ∃ dx dy : Lp ℂ 2 (doubleMeasure Q),
      (geodesicHilbertFlow Q).HasGenerator ((angularCircleAction Q).projection j (hf.toLp _)) dx ∧
      (transverseHilbertFlow Q).HasGenerator ((angularCircleAction Q).projection j (hf.toLp _)) dy ∧
      ‖dx‖ ^ 2 ≤ 4 * (C : ℝ)^2 * (doubleMeasure Q (unsafeSet Q A)).toReal ∧
      ‖dy‖ ^ 2 ≤ 4 * (C : ℝ)^2 * (doubleMeasure Q (unsafeSet Q A)).toReal := by
  let hx := xDerivative_memLp_of_gradient_bound Q hm
    (fun v b => (hd v b).differentiable (by simp)) hC
  let hy := yDerivative_memLp_of_gradient_bound Q hm
    (fun v b => (hd v b).differentiable (by simp)) hC
  let R := restrictL2 (μ := doubleMeasure Q) (unsafeSet Q A) (unsafeSet_measurable Q A)
  have hxb : ∀ᵐ z ∂doubleMeasure Q, ‖hx.toLp _ z‖ ≤ (C : ℝ) := by
    filter_upwards [hx.coeFn_toLp] with z hz
    rw [hz]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (by
      rw [Circle.norm_coe, mul_one]; exact hC z.1.1 z.1.2 z.2)
  have hyb : ∀ᵐ z ∂doubleMeasure Q, ‖hy.toLp _ z‖ ≤ (C : ℝ) := by
    filter_upwards [hy.coeFn_toLp] with z hz
    rw [hz]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (by
      rw [norm_transverseVelocity, mul_one]; exact hC z.1.1 z.1.2 z.2)
  have hrx : R (hx.toLp _) = hx.toLp _ := by
    apply restrictL2_fixed
    filter_upwards [hx.coeFn_toLp,hX] with z hz hh
    simpa only [hz] using hh
  have hxn : ‖hx.toLp _‖ ≤ (C : ℝ) * (doubleMeasure Q (unsafeSet Q A)).toReal ^ (1/2 : ℝ) := by
    rw [← hrx]
    exact restrictL2_norm_of_bounded _ _ (measure_ne_top _ _) C.coe_nonneg hxb
  have hyn := restrictL2_norm_of_bounded (unsafeSet Q A) (unsafeSet_measurable Q A)
    (measure_ne_top _ _) C.coe_nonneg hyb
  obtain ⟨dx,dy,hgx,hgy,hbx,hby⟩ := seam_localized_energy hs hm hd hC hD hf
    {x | Q.clearance x ≤ A} (Q.clearance_sublevel_measurable A) hX j
  have hmass : ((doubleMeasure Q (unsafeSet Q A)).toReal ^ (1/2 : ℝ))^2 =
      (doubleMeasure Q (unsafeSet Q A)).toReal := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt ENNReal.toReal_nonneg]
  have hb : 4 * ‖hx.toLp _‖ * ‖R (hy.toLp _)‖ ≤
      4 * (C : ℝ)^2 * (doubleMeasure Q (unsafeSet Q A)).toReal := by
    calc
      _ ≤ 4 * ((C : ℝ) * (doubleMeasure Q (unsafeSet Q A)).toReal ^ (1/2 : ℝ)) *
          ((C : ℝ) * (doubleMeasure Q (unsafeSet Q A)).toReal ^ (1/2 : ℝ)) := by
        gcongr
      _ = _ := by nlinarith [hmass]
  exact ⟨dx,dy,hgx,hgy,hbx.trans hb,hby.trans hb⟩

end TriangularBilliards

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
end

section
section
namespace OAI

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Finset Set
open scoped Topology BigOperators
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section

namespace TriangularBilliards
open Analysis SpatialSmoothing MeasureTheory Filter Set
open scoped Topology ContDiff NNReal
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The uniform per-coefficient estimate for cutoff regularizations of an
actual bounded invariant. The constant depends on the triangle, not the
Fourier index, smoothing scale, or the bounded invariant. -/
lemma bounded_invariant_regularized_modes (Q : Triangle) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {H : ℝ} {f : DoublePhase → ℂ}
      (hm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q))
      (hH : ∀ z, ‖f z‖ ≤ H)
      (_hfi : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) 0)
      {ε : ℝ} (hε : 0 < ε)
      (_hsmall : 2 * ((Q.safetyFactor + 1) * ε) * Q.coordinateBound < 1) (j : ℤ),
      let w := supportedSmoothing Q ε ((Q.safetyFactor + 1) * ε) f
      let hw := supportedSmoothing_memLp Q hε ((Q.safetyFactor + 1) * ε) hm hH
      ∃ dx dy : Lp ℂ 2 (doubleMeasure Q),
        (geodesicHilbertFlow Q).HasGenerator ((angularCircleAction Q).projection j (hw.toLp w)) dx ∧
        (transverseHilbertFlow Q).HasGenerator ((angularCircleAction Q).projection j (hw.toLp w)) dy ∧
        ‖dx‖ ^ 2 ≤ C * H^2 ∧ ‖dy‖ ^ 2 ≤ C * H^2 := by
  obtain ⟨D,hDp,hD⟩ := exists_vertexCutoff_derivative_bound
  let K := Q.safetyFactor + 1
  have hK : 1 < K := by dsimp [K]; linarith [Q.safetyFactor_pos]
  let J := 4 * derivativeMass + 4 * D
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact add_nonneg (mul_nonneg (by norm_num) derivativeMass_nonneg) (mul_nonneg (by norm_num) hDp)
  let B := ((volume Q.table).toReal)⁻¹ * (3 * (2*K+1)^2 * Real.pi)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨4 * J^2 * B, by positivity, ?_⟩
  intro H f hm hf hH hfi ε hε hsmall j
  have hH₀ : 0 ≤ H := (norm_nonneg _).trans (hH ((0,1),0))
  have hR : Q.safetyFactor * ε < K * ε := by dsimp [K]; nlinarith
  have hRp : 0 < K * ε := mul_pos (by linarith) hε
  let Cε : ℝ≥0 := ⟨J*H/ε, by positivity⟩
  have hC (x : ℂ) (v : Circle) (b : ZMod 2) :
      ‖fderiv ℝ (fun y => supportedSmoothing Q ε (K*ε) f ((y,v),b)) x‖ ≤ Cε := by
    rw [(supportedSmoothing_hasFDerivAt Q hε (K*ε) hm hH v b x).fderiv]
    apply (supportedSmoothingGradient_norm_bound Q hε hH₀ hH (hD Q (K*ε) hRp) ((x,v),b)).trans
    change 4*derivativeMass*H/ε + (D/(K*ε))*(4*H) ≤ J*H/ε
    have hh : D / (K*ε) ≤ D / ε :=
      div_le_div_of_nonneg_left hDp hε (by nlinarith)
    calc
      _ ≤ 4*derivativeMass*H/ε + (D/ε)*(4*H) := by gcongr
      _ = _ := by dsimp [J]; ring
  obtain ⟨M,hM⟩ := supportedSmoothing_second_bound Q hε hRp hm hH
  have hm' := (supportedSmoothing_stronglyMeasurable Q ε (K*ε) hm).measurable
  have hw := supportedSmoothing_memLp Q hε (K*ε) hm hH
  have hs := supportedSmoothing_seam Q hε hR hsmall f
  have hd := supportedSmoothing_contDiff Q hε (K*ε) hm hH
  have hA : 2 * (K*ε) + ε ≤ (2*K+1)*ε := by linarith
  obtain ⟨dx,dy,hgx,hgy,hbx,hby⟩ := seam_tip_energy hs hm' hd hC hM hw ((2*K+1)*ε)
    (supportedSmoothing_invariant_x_zero Q hε hR hsmall hA hm hf hfi hH) j
  have hmass : (doubleMeasure Q (unsafeSet Q ((2*K+1)*ε))).toReal ≤ B * ε^2 := by
    apply (unsafeSet_real_measure_bound Q (show 0 ≤ (2*K+1)*ε by positivity)).trans_eq
    dsimp [B]
    ring
  have hb : 4 * (Cε : ℝ)^2 * (doubleMeasure Q (unsafeSet Q ((2*K+1)*ε))).toReal ≤
      (4 * J^2 * B) * H^2 := by
    calc
      _ ≤ 4 * (Cε : ℝ)^2 * (B*ε^2) := by gcongr
      _ = _ := by
        change 4 * (J*H/ε)^2 * (B*ε^2) = _
        field_simp
  exact ⟨dx,dy,hgx,hgy,hbx.trans hb,hby.trans hb⟩

end TriangularBilliards

namespace TriangularBilliards
open Analysis SpatialSmoothing MeasureTheory Filter Set
open scoped Topology ContDiff NNReal BoundedContinuousFunction

lemma kernel_eq_zero_of_large {ε : ℝ} (hε : 0 < ε) {y : ℂ} (hy : ε ≤ ‖y‖) :
    kernel ε y = 0 := by
  by_contra h
  have hx : y ∈ support (kernel ε) := h
  rw [kernel_support hε, mem_ball_zero_iff] at hx
  exact (not_lt_of_ge hy) hx

lemma fullS_tendsto (f : ℂ →ᵇ ℂ) (x : ℂ) :
    Tendsto (fun ε : ℝ => ∫ y : ℂ, kernel ε (x-y) • f y) (𝓝[>] 0) (𝓝 (f x)) := by
  have hs : Tendsto (fun ε : ℝ => support (kernel ε)) (𝓝[>] 0) (𝓝 (0 : ℂ)).smallSets := by
    rw [tendsto_smallSets_iff]
    intro s hs
    obtain ⟨r,hr,hb⟩ := Metric.mem_nhds_iff.mp hs
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds hr)] with ε hp he
    rw [kernel_support hp]
    exact (Metric.ball_subset_ball he.le).trans hb
  have hh := convolution_tendsto_right (μ := (volume : Measure ℂ))
    (g := fun _ : ℝ => (f : ℂ → ℂ)) (k := fun _ : ℝ => x)
    (Eventually.of_forall (fun ε => kernel_nonneg ε))
    (show ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∫ y, kernel ε y = 1 from
      (show ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε from self_mem_nhdsWithin).mono (fun ε hε => kernel_integral hε)) hs
    (Eventually.of_forall fun _ => f.continuous.aestronglyMeasurable)
    (f.continuous.continuousAt.tendsto.comp tendsto_snd) tendsto_const_nhds
  apply hh.congr (fun ε => ?_)
  rw [MeasureTheory.convolution_def]
  rw [← integral_sub_left_eq_self (fun y : ℂ => kernel ε (x-y) • f y) volume x]
  simp only [sub_sub_cancel, ContinuousLinearMap.lsmul_apply]

lemma directS_eq_full (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    (f : DoublePhase → ℂ) (z : DoublePhase) (hz : closedBall z.1.1 ε ⊆ Q.table) :
    directS Q ε f z.2 z.1.2 z.1.1 = ∫ y : ℂ, kernel ε (z.1.1-y) • f ((y,z.1.2),z.2) := by
  rw [directS, ← integral_indicator Q.measurableSet_table]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    by_cases hy : y ∈ Q.table
    · rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy]
      have hn : ε < ‖z.1.1-y‖ := by
        by_contra hh
        exact hy (hz (by rw [mem_closedBall, dist_comm, dist_eq_norm]; exact not_lt.mp hh))
      simp only [kernel_eq_zero_of_large hε hn.le, zero_smul]

lemma reflectedS_zero_of_coord_phase (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    (f : DoublePhase → ℂ) (z : DoublePhase)
    (hz : Q.coordinateBound * ε < Q.basis.coord (i+2) z.1.1) :
    reflectedS Q i ε f z.2 z.1.2 z.1.1 = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem Q.measurableSet_table] with y hy
  have hn : ε < ‖z.1.1 - wallReflection Q i y‖ := by
    by_contra hh
    exact (not_le_of_gt hz) (Q.coord_small_of_reflected_near i hy (not_lt.mp hh))
  simp only [kernel_eq_zero_of_large hε hn.le, zero_smul, Pi.zero_apply]

lemma eventually_interior_smoothing (Q : Triangle) (f : DoublePhase → ℂ)
    (z : DoublePhase) (hz : z.1.1 ∈ Q.table) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), reflectedSmoothing Q ε f z =
      ∫ y : ℂ, kernel ε (z.1.1-y) • f ((y,z.1.2),z.2) := by
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp Q.isOpen_table _ hz
  have hcoords : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i : Fin 3,
      Q.coordinateBound * ε < Q.basis.coord (i+2) z.1.1 := by
    rw [Filter.eventually_all]
    intro i
    have hp := (Q.table_iff_coords z.1.1).mp hz (i+2)
    have hc : Continuous (fun ε : ℝ => Q.coordinateBound * ε) := by fun_prop
    simpa only [mul_zero] using hc.continuousAt.eventually (gt_mem_nhds (by simpa only [mul_zero] using hp))
  filter_upwards [nhdsWithin_le_nhds hcoords,
    nhdsWithin_le_nhds (gt_mem_nhds hr), self_mem_nhdsWithin] with ε hc hεr hε
  have hfull := directS_eq_full Q hε f z (fun y hy => hball (by
    rw [mem_ball]
    exact (mem_closedBall.mp hy).trans_lt hεr))
  change directS Q ε f z.2 z.1.2 z.1.1 + ∑ i, reflectedS Q i ε f z.2 z.1.2 z.1.1 = _
  simp only [reflectedS_zero_of_coord_phase Q _ hε f z (hc _), Finset.sum_const_zero, add_zero]
  exact hfull

lemma smoothing_pointwise (Q : Triangle) (f : DoublePhase →ᵇ ℂ)
    (z : DoublePhase) (hz : z.1.1 ∈ Q.table) :
    Tendsto (fun ε : ℝ => reflectedSmoothing Q ε f z) (𝓝[>] 0) (𝓝 (f z)) := by
  let g : ℂ →ᵇ ℂ := f.compContinuous ⟨fun y => ((y,z.1.2),z.2), by fun_prop⟩
  exact (fullS_tendsto g z.1.1).congr' ((eventually_interior_smoothing Q f z hz).mono (fun _ h => h.symm))

end TriangularBilliards

namespace TriangularBilliards
open Analysis SpatialSmoothing MeasureTheory Filter Set
open scoped Topology ContDiff NNReal BoundedContinuousFunction

lemma Triangle.clearance_pos_of_mem_table (Q : Triangle) {x : ℂ} (hx : x ∈ Q.table) :
    0 < Q.clearance x := by
  apply ((finite_range Q.vertex).isClosed.notMem_iff_infDist_pos (range_nonempty _)).mp
  rintro ⟨i,rfl⟩
  have h := (Q.table_iff_coords _).mp hx (i+2)
  have hv : Q.basis.coord (i+2) (Q.vertex i) = 0 :=
    Q.basis.coord_apply (i+2) i |>.trans (ite_eq_right ((by decide : ∀ i : Fin 3, i+2 ≠ i) i))
  linarith

lemma supported_smoothing_pointwise (Q : Triangle) (K : ℝ) (hK : 0 < K)
    (f : DoublePhase →ᵇ ℂ) (z : DoublePhase) (hz : z.1.1 ∈ Q.table) :
    Tendsto (fun ε : ℝ => supportedSmoothing Q ε (K*ε) f z) (𝓝[>] 0) (𝓝 (f z)) := by
  have hc : ∀ᶠ ε in 𝓝 (0 : ℝ), 2*(K*ε) < Q.clearance z.1.1 := by
    have h : Continuous (fun ε : ℝ => 2*(K*ε)) := by fun_prop
    simpa only [mul_zero] using h.continuousAt.eventually
      (gt_mem_nhds (by simpa only [mul_zero] using Q.clearance_pos_of_mem_table hz))
  apply (smoothing_pointwise Q f z hz).congr'
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hc] with ε hε hh
  simp only [supportedSmoothing, vertexCutoff_one Q (mul_pos hK hε) hh.le, one_smul]

lemma supported_smoothing_lpNorm_tendsto_bounded (Q : Triangle) {K : ℝ} (hK : 0 < K)
    (f : DoublePhase →ᵇ ℂ) :
    Tendsto (fun ε : ℝ => lpNorm (supportedSmoothing Q ε (K*ε) f - (f : DoublePhase → ℂ)) 2 (doubleMeasure Q))
      (𝓝[>] 0) (𝓝 0) := by
  have hi : Tendsto (fun ε : ℝ => ∫ z,
      ‖supportedSmoothing Q ε (K*ε) f z - f z‖^2 ∂doubleMeasure Q)
      (𝓝[>] 0) (𝓝 (∫ _ : DoublePhase, (0 : ℝ) ∂doubleMeasure Q)) := by
    apply tendsto_integral_filter_of_norm_le_const
    · exact Eventually.of_forall fun ε =>
        (((supportedSmoothing_stronglyMeasurable Q ε (K*ε) f.continuous.stronglyMeasurable).sub
          f.continuous.stronglyMeasurable).measurable.norm.pow_const 2).aestronglyMeasurable
    · refine ⟨(5*‖f‖)^2, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        apply pow_le_pow_left₀ (norm_nonneg _)
        exact (norm_sub_le _ _).trans (by
          have h := supportedSmoothing_norm_bound Q hε (K*ε) (norm_nonneg f) f.norm_coe_le_norm z
          linarith [f.norm_coe_le_norm z])
    · filter_upwards [ae_double_position_in_table Q] with z hz
      simpa only [sub_self, norm_zero, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, zero_pow] using
        (((supported_smoothing_pointwise Q K hK f z hz).sub (tendsto_const_nhds (x := f z))).norm.pow 2)
  simp only [integral_zero] at hi
  have he (ε : ℝ) : lpNorm (supportedSmoothing Q ε (K*ε) f - (f : DoublePhase → ℂ)) 2 (doubleMeasure Q) =
      Real.sqrt (∫ z, ‖supportedSmoothing Q ε (K*ε) f z - f z‖^2 ∂doubleMeasure Q) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      ((supportedSmoothing_stronglyMeasurable Q ε (K*ε) f.continuous.stronglyMeasurable).sub
        f.continuous.stronglyMeasurable).aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat, Pi.sub_apply, Real.rpow_two, Real.sqrt_eq_rpow]
    norm_num
  simp_rw [he]
  simpa only [Real.sqrt_zero, Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hi

lemma directS_integrable_ae (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hi : Integrable f (doubleMeasure Q)) :
    ∀ᵐ z ∂doubleMeasure Q, Integrable (fun y => kernel ε (z.1.1-y) •
      f ((y,z.1.2),z.2)) (volume.restrict Q.table) := by
  obtain ⟨C,hC⟩ := (kernel_hasCompactSupport hε).exists_bound_of_continuous
    (kernel_contDiff ε).continuous
  filter_upwards [integrable_slice_ae Q hi] with z hz
  exact hz.bdd_smul C
    (((kernel_contDiff ε).continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall fun y => hC (z.1.1-y))

lemma reflectedS_integrable_ae (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hi : Integrable f (doubleMeasure Q)) :
    ∀ᵐ z ∂doubleMeasure Q, Integrable (fun y => kernel ε (z.1.1-wallReflection Q i y) •
      f ((y,reflectedDirection Q i z.1.2),z.2+1)) (volume.restrict Q.table) := by
  obtain ⟨C,hC⟩ := (kernel_hasCompactSupport hε).exists_bound_of_continuous
    (kernel_contDiff ε).continuous
  filter_upwards [(measurePreserving_directionParityReflection Q i).quasiMeasurePreserving.ae
    (integrable_slice_ae Q hi)] with z hz
  exact hz.bdd_smul C
    (((kernel_contDiff ε).continuous.comp (continuous_const.sub
      (wallReflection_contDiff Q i).continuous)).aestronglyMeasurable)
    (Eventually.of_forall fun y => hC (z.1.1-wallReflection Q i y))

lemma smoothing_sub_ae (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f g : DoublePhase → ℂ} (hfi : Integrable f (doubleMeasure Q)) (hgi : Integrable g (doubleMeasure Q)) :
    reflectedSmoothing Q ε (f-(g : DoublePhase → ℂ)) =ᵐ[doubleMeasure Q]
      reflectedSmoothing Q ε f - reflectedSmoothing Q ε g := by
  filter_upwards [directS_integrable_ae Q hε hfi, directS_integrable_ae Q hε hgi,
    Filter.eventually_all.mpr (fun i => reflectedS_integrable_ae Q i hε hfi),
    Filter.eventually_all.mpr (fun i => reflectedS_integrable_ae Q i hε hgi)] with z hf hg hrf hrg
  have hd : directS Q ε (f-(g : DoublePhase → ℂ)) z.2 z.1.2 z.1.1 = directS Q ε f z.2 z.1.2 z.1.1 - directS Q ε g z.2 z.1.2 z.1.1 := by
    simp only [directS, Pi.sub_apply, smul_sub]
    exact integral_sub hf hg
  have hr (i : Fin 3) : reflectedS Q i ε (f-(g : DoublePhase → ℂ)) z.2 z.1.2 z.1.1 =
      reflectedS Q i ε f z.2 z.1.2 z.1.1 - reflectedS Q i ε g z.2 z.1.2 z.1.1 := by
    simp only [reflectedS, Pi.sub_apply, smul_sub]
    exact integral_sub (hrf i) (hrg i)
  simp only [Pi.sub_apply, reflectedSmoothing, hd, hr, Finset.sum_sub_distrib]
  abel

lemma supported_smoothing_sub_ae (Q : Triangle) {ε : ℝ} (hε : 0 < ε) (R : ℝ)
    {f g : DoublePhase → ℂ} (hfi : Integrable f (doubleMeasure Q)) (hgi : Integrable g (doubleMeasure Q)) :
    supportedSmoothing Q ε R (f-(g : DoublePhase → ℂ)) =ᵐ[doubleMeasure Q]
      supportedSmoothing Q ε R f - supportedSmoothing Q ε R g := by
  filter_upwards [smoothing_sub_ae Q hε hfi hgi] with z hz
  simp only [Pi.sub_apply] at hz ⊢
  simp only [supportedSmoothing, hz, smul_sub]

lemma supportedSmoothing_norm_le (Q : Triangle) (ε R : ℝ) (f : DoublePhase → ℂ) (z : DoublePhase) :
    ‖supportedSmoothing Q ε R f z‖ ≤ ‖reflectedSmoothing Q ε f z‖ := by
  rw [supportedSmoothing, norm_smul, Real.norm_eq_abs, abs_of_nonneg (vertexCutoff_mem_Icc Q R _).1]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (vertexCutoff_mem_Icc Q R _).2 (norm_nonneg _)

lemma supportedSmoothing_memLp_of_memLp (Q : Triangle) {ε : ℝ} (hε : 0 < ε) (R : ℝ)
    {f : DoublePhase → ℂ} (hf : StronglyMeasurable f) (hf₂ : MemLp f 2 (doubleMeasure Q)) :
    MemLp (supportedSmoothing Q ε R f) 2 (doubleMeasure Q) :=
  (reflectedSmoothing_memLp Q hε hf hf₂).norm.mono'
    (supportedSmoothing_stronglyMeasurable Q ε R hf).aestronglyMeasurable
    (Eventually.of_forall (supportedSmoothing_norm_le Q ε R f))

lemma supported_smoothing_lpNorm_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε) (R : ℝ)
    {f : DoublePhase → ℂ} (hf : StronglyMeasurable f) (hf₂ : MemLp f 2 (doubleMeasure Q)) :
    lpNorm (supportedSmoothing Q ε R f) 2 (doubleMeasure Q) ≤ 4 * lpNorm f 2 (doubleMeasure Q) := by
  rw [← toReal_eLpNorm (supportedSmoothing_stronglyMeasurable Q ε R hf).aestronglyMeasurable,
    ← toReal_eLpNorm hf.aestronglyMeasurable]
  have hh : eLpNorm (supportedSmoothing Q ε R f) 2 (doubleMeasure Q) ≤ 4 * eLpNorm f 2 (doubleMeasure Q) :=
    (eLpNorm_mono_ae
      (Eventually.of_forall (supportedSmoothing_norm_le Q ε R f))).trans
      (reflectedSmoothing_eLpNorm Q hε hf)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hf₂.eLpNorm_ne_top) hh

end TriangularBilliards

namespace TriangularBilliards
open Analysis SpatialSmoothing MeasureTheory Filter Set
open scoped Topology ContDiff NNReal BoundedContinuousFunction

/-- Strong L2 approximate identity for the actual supported triangular
mollifier. No smoothness or invariance is required of the input. -/
lemma supported_smoothing_lpNorm_tendsto (Q : Triangle) {K : ℝ} (hK : 0 < K)
    {f : DoublePhase → ℂ} (hf : StronglyMeasurable f) (hf₂ : MemLp f 2 (doubleMeasure Q)) :
    Tendsto (fun ε : ℝ => lpNorm (supportedSmoothing Q ε (K*ε) f - (f : DoublePhase → ℂ)) 2 (doubleMeasure Q))
      (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  let η : ℝ := δ/12
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨g,hg,hg₂⟩ := hf₂.exists_boundedContinuous_eLpNorm_sub_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (ENNReal.ofReal_ne_zero_iff.mpr hη)
  have hsmall : lpNorm (f - (g : DoublePhase → ℂ)) 2 (doubleMeasure Q) ≤ η := by
    rw [← toReal_eLpNorm (hf.aestronglyMeasurable.sub g.continuous.aestronglyMeasurable)]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hg).trans_eq (ENNReal.toReal_ofReal hη.le)
  have hgsmall := (Metric.tendsto_nhds.mp (supported_smoothing_lpNorm_tendsto_bounded Q hK g))
    (δ/2) (by positivity)
  filter_upwards [self_mem_nhdsWithin, hgsmall] with ε hε he
  let Sf := supportedSmoothing Q ε (K*ε) f
  let Sg := supportedSmoothing Q ε (K*ε) g
  have hfm := supportedSmoothing_memLp_of_memLp Q hε (K*ε) hf hf₂
  have hgm := supportedSmoothing_memLp_of_memLp Q hε (K*ε) g.continuous.stronglyMeasurable hg₂
  have hdm := supportedSmoothing_memLp_of_memLp Q hε (K*ε)
    (hf.sub g.continuous.stronglyMeasurable) (hf₂.sub hg₂)
  have hae : Sf - Sg =ᵐ[doubleMeasure Q] supportedSmoothing Q ε (K*ε) (f-(g : DoublePhase → ℂ)) :=
    (supported_smoothing_sub_ae Q hε (K*ε) (hf₂.integrable (by norm_num))
      (hg₂.integrable (by norm_num))).symm
  have hb : lpNorm (Sf-Sg) 2 (doubleMeasure Q) ≤ 4*η := by
    rw [lpNorm_congr_ae_of_strong (hfm.sub hgm).aestronglyMeasurable
      hdm.aestronglyMeasurable hae]
    exact (supported_smoothing_lpNorm_bound Q hε (K*ε)
      (hf.sub g.continuous.stronglyMeasurable) (hf₂.sub hg₂)).trans (by gcongr)
  have hn : lpNorm (Sf-f) 2 (doubleMeasure Q) ≤
      lpNorm (Sf-Sg) 2 (doubleMeasure Q) + lpNorm (Sg-(g : DoublePhase → ℂ)) 2 (doubleMeasure Q) +
        lpNorm (f-(g : DoublePhase → ℂ)) 2 (doubleMeasure Q) := by
    have heq : Sf-f = ((Sf-Sg)+(Sg-(g : DoublePhase → ℂ)))-(f-(g : DoublePhase → ℂ)) := by ext z; simp only [Pi.sub_apply, Pi.add_apply]; abel
    rw [heq]
    apply (lpNorm_sub_le ((hfm.sub hgm).add (hgm.sub hg₂)) (by norm_num)).trans
    exact add_le_add (lpNorm_add_le (hfm.sub hgm) (by norm_num)) le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg lpNorm_nonneg] at he ⊢
  change lpNorm (Sf - f) 2 (doubleMeasure Q) < δ
  change lpNorm (Sg - (g : DoublePhase → ℂ)) 2 (doubleMeasure Q) < δ/2 at he
  dsimp [η] at hsmall hb
  linarith

end TriangularBilliards

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
end

section
section
namespace OAI


open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Finset Set
open scoped Topology BigOperators
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section

open Filter Set
open scoped Topology

noncomputable section

namespace TriangularBilliards.Analytic

section Weak

variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {α : Type uAlpha} {l : Filter α}

/-- Scalar-test characterization of weak convergence over the real field. -/
def WeaklyTendsto (u : α → E) (l : Filter α) (v : E) : Prop :=
  ∀ L : E →L[ℝ] ℝ, Tendsto (fun n => L (u n)) l (𝓝 (L v))

lemma weaklyTendsto_of_tendsto {u : α → E} {v : E}
    (h : Tendsto u l (𝓝 v)) : WeaklyTendsto u l v :=
  fun L => L.continuous.continuousAt.tendsto.comp h

lemma WeaklyTendsto.comp {u : α → E} {v : E} (h : WeaklyTendsto u l v)
    {β : Type uBeta} {m : Filter β} {φ : β → α} (hφ : Tendsto φ m l) :
    WeaklyTendsto (u ∘ φ) m v :=
  fun L => (h L).comp hφ

lemma WeaklyTendsto.prod {u : α → E} {v : α → F} {a : E} {b : F}
    (hu : WeaklyTendsto u l a) (hv : WeaklyTendsto v l b) :
    WeaklyTendsto (fun n => (u n, v n)) l (a, b) := by
  intro L
  have h := (hu (L.comp (ContinuousLinearMap.inl ℝ E F))).add
    (hv (L.comp (ContinuousLinearMap.inr ℝ E F)))
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply, ← map_add, Prod.add_def, add_zero, zero_add] using h

lemma WeaklyTendsto.sub_const {u : α → E} {v : E}
    (h : WeaklyTendsto u l v) (w : E) :
    WeaklyTendsto (fun n => u n - w) l (v - w) := by
  intro L
  simpa only [map_sub] using (h L).sub_const (L w)

/-- Norm-closed convex sets remain closed under weak limits. In particular
this applies to a uniform L∞ bound inside L² and to a closed derivative graph. -/
lemma WeaklyTendsto.mem_of_closed_convex [l.NeBot] {u : α → E} {v : E}
    (h : WeaklyTendsto u l v) {C : Set E} (hc : IsClosed C) (hcv : Convex ℝ C)
    (hu : ∀ᶠ n in l, u n ∈ C) : v ∈ C := by
  by_contra hn
  obtain ⟨L, t, hC, hv⟩ := geometric_hahn_banach_closed_point hcv hc hn
  have hle : L v ≤ t := le_of_tendsto (h L) (hu.mono fun n hn => (hC _ hn).le)
  exact (not_le_of_gt hv) hle

lemma WeaklyTendsto.norm_le [l.NeBot] {u : α → E} {v : E}
    (h : WeaklyTendsto u l v) {r : ℝ} (hu : ∀ᶠ n in l, ‖u n‖ ≤ r) : ‖v‖ ≤ r := by
  have hv := h.mem_of_closed_convex Metric.isClosed_closedBall (convex_closedBall (0 : E) r)
    (hu.mono fun n hn => (mem_closedBall_zero_iff).mpr hn)
  exact mem_closedBall_zero_iff.mp hv

lemma WeaklyTendsto.norm_le_of_bounds [l.NeBot] {u : α → E} {v : E}
    (h : WeaklyTendsto u l v) {r : α → ℝ} {R : ℝ}
    (hr : Tendsto r l (𝓝 R)) (hu : ∀ᶠ n in l, ‖u n‖ ≤ r n) : ‖v‖ ≤ R := by
  apply le_of_forall_pos_le_add
  intro ε hε
  apply h.norm_le
  filter_upwards [hu, hr.eventually (gt_mem_nhds (show R < R + ε by linarith))]
    with n hn hrn
  exact hn.trans hrn.le

end Weak

section Hilbert

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [TopologicalSpace.SeparableSpace E]

/-- Weak sequential compactness of a bounded set in a separable real Hilbert
space, obtained from Banach–Alaoglu and Riesz. -/
lemma exists_weak_subsequence (u : ℕ → E) {R : ℝ} (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ v : E, ‖v‖ ≤ R ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ WeaklyTendsto (u ∘ φ) atTop v := by
  let J := InnerProductSpace.toDual ℝ E
  let w : ℕ → WeakDual ℝ E := fun n => StrongDual.toWeakDual (J (u n))
  have hw : ∀ n, w n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) R := by
    intro n
    change dist (J (u n)) 0 ≤ R
    simpa only [dist_zero_right, LinearIsometryEquiv.norm_map] using hu n
  obtain ⟨a, ha, φ, hφ, hlim⟩ := (WeakDual.isSeqCompact_closedBall ℝ E 0 R) hw
  let v : E := J.symm (WeakDual.toStrongDual a)
  have hv : ‖v‖ ≤ R := by
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, v,
      LinearIsometryEquiv.norm_map] using ha
  refine ⟨v, hv, φ, hφ, ?_⟩
  intro L
  let x : E := J.symm L
  have heq (y : E) : (J y) x = L y := by
    change inner ℝ y (J.symm L) = L y
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have heqa : a x = L v := by
    change (WeakDual.toStrongDual a) x = L v
    have hj : J v = WeakDual.toStrongDual a := J.apply_symm_apply _
    rw [← hj, heq]
  have h := (WeakDual.eval_continuous x).continuousAt.tendsto.comp hlim
  change Tendsto (fun n => (J (u (φ n))) x) atTop (𝓝 (a x)) at h
  simpa only [heq, heqa, Function.comp_apply] using h

end Hilbert

section DerivativeGraph

variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A distributional graph described by test identities. Instantiating it
with weak differentiation requires constructing its actual test functionals. -/
def TestGraph {ι : Type uIota} (A : ι → E →L[ℝ] ℝ) (B : ι → F →L[ℝ] ℝ) : Set (E × F) :=
  {p | ∀ i, A i p.1 = B i p.2}

lemma testGraph_closed {ι : Type uIota} (A : ι → E →L[ℝ] ℝ) (B : ι → F →L[ℝ] ℝ) :
    IsClosed (TestGraph A B) := by
  have h : TestGraph A B = ⋂ i, {p : E × F | A i p.1 = B i p.2} := by
    ext p
    simp only [TestGraph, mem_ofPred_eq, mem_iInter]
  rw [h]
  exact isClosed_iInter fun i => isClosed_eq ((A i).continuous.comp continuous_fst)
    ((B i).continuous.comp continuous_snd)

lemma testGraph_convex {ι : Type uIota} (A : ι → E →L[ℝ] ℝ) (B : ι → F →L[ℝ] ℝ) :
    Convex ℝ (TestGraph A B) := by
  intro p hp q hq a b _ _ _ i
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    map_add, map_smul, hp i, hq i]

/-- Identifying the weak derivative limit uses only test identities, not
an unjustified claim that the entire horizontal derivative lies in L². -/
lemma testGraph_weak_limit {ι : Type uIota} {α : Type uAlpha} (A : ι → E →L[ℝ] ℝ) (B : ι → F →L[ℝ] ℝ)
    {l : Filter α} [l.NeBot] {u : α → E} {d : α → F} {v : E} {e : F}
    (hu : WeaklyTendsto u l v) (hd : WeaklyTendsto d l e)
    (hgraph : ∀ᶠ n in l, (u n, d n) ∈ TestGraph A B) : (v, e) ∈ TestGraph A B :=
  (hu.prod hd).mem_of_closed_convex (testGraph_closed A B) (testGraph_convex A B) hgraph

end DerivativeGraph

section TestGraphLimits

variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F] [TopologicalSpace.SeparableSpace F]

omit [CompleteSpace F] [TopologicalSpace.SeparableSpace F] in
lemma testGraph_unique {ι : Type uIota} (A : ι → E →L[ℝ] ℝ) (B : ι → F →L[ℝ] ℝ)
    (hsep : ∀ v : F, (∀ i, B i v = 0) → v = 0)
    {u : E} {d e : F} (hd : (u, d) ∈ TestGraph A B) (he : (u, e) ∈ TestGraph A B) :
    d = e := by
  apply sub_eq_zero.mp
  apply hsep
  intro i
  rw [map_sub, ← hd i, ← he i, sub_self]

/-- The second-limit step: strong convergence of the functions and a
uniform bound for only the relevant derivatives suffice to pass a fixed
pairing to the limit. There is no bound for the sum of all mode derivatives. -/
lemma testGraph_pairing_of_strong_limit {ι : Type uIota}
    (A : ι → E →L[ℝ] ℝ) (B : ι → F →L[ℝ] ℝ)
    (hsep : ∀ v : F, (∀ i, B i v = 0) → v = 0)
    (u : ℕ → E) (d : ℕ → F) {f : E} {e : F} {R : ℝ}
    (hgraph : ∀ n, (u n, d n) ∈ TestGraph A B)
    (hf : (f, e) ∈ TestGraph A B)
    (hu : Tendsto u atTop (𝓝 f)) (hd : ∀ n, ‖d n‖ ≤ R)
    (L : F →L[ℝ] ℝ) (hL : Tendsto (fun n => L (d n)) atTop (𝓝 0)) : L e = 0 := by
  obtain ⟨e', _, φ, hφ, he'⟩ := exists_weak_subsequence d hd
  have hfu := (weaklyTendsto_of_tendsto hu).comp hφ.tendsto_atTop
  have hfe' : (f, e') ∈ TestGraph A B :=
    testGraph_weak_limit A B hfu he' (Eventually.of_forall fun n => hgraph (φ n))
  have heq := testGraph_unique A B hsep hfe' hf
  have hzero : L e' = 0 := tendsto_nhds_unique (he' L) (hL.comp hφ.tendsto_atTop)
  simpa only [heq] using hzero

end TestGraphLimits

section FirstLimit

variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
  [CompleteSpace F] [TopologicalSpace.SeparableSpace F]

/-- The fixed-clearance-budget weak limit. The derivative bound `M` is
allowed to depend on that fixed budget. An application must supply all
smoothing, support, transport and distributional-graph properties; this
lemma supplies the two subsequence extractions and all limit passages. -/
lemma testGraph_first_limit {ι : Type uIota} {κ : Type uKappa}
    (A : ι → E →L[ℝ] ℝ) (B : ι → F →L[ℝ] ℝ) (X : κ → E →L[ℝ] ℝ)
    (C : Set E) (hCclosed : IsClosed C) (hCconvex : Convex ℝ C)
    (u : ℕ → E) (d : ℕ → F) {f : E} {H M δ : ℝ} (δn : ℕ → ℝ)
    (hu : ∀ n, ‖u n‖ ≤ H) (hd : ∀ n, ‖d n‖ ≤ M)
    (hC : ∀ n, u n ∈ C) (hgraph : ∀ n, (u n, d n) ∈ TestGraph A B)
    (hX : ∀ k, Tendsto (fun n => X k (u n)) atTop (𝓝 0))
    (hδn : Tendsto δn atTop (𝓝 δ)) (hclose : ∀ n, ‖u n - f‖ ≤ δn n)
    (L : F →L[ℝ] ℝ) (hL : Tendsto (fun n => L (d n)) atTop (𝓝 0)) :
    ∃ g : E, ∃ e : F,
      g ∈ C ∧ (∀ k, X k g = 0) ∧ ‖g - f‖ ≤ δ ∧ (g, e) ∈ TestGraph A B ∧ L e = 0 := by
  obtain ⟨g, _, φ, hφ, hg⟩ := exists_weak_subsequence u hu
  obtain ⟨e, _, ψ, hψ, he⟩ := exists_weak_subsequence (d ∘ φ) (fun n => hd (φ n))
  have hw : WeaklyTendsto (u ∘ φ ∘ ψ) atTop g := hg.comp hψ.tendsto_atTop
  have hφψ : Tendsto (φ ∘ ψ) atTop atTop := hφ.tendsto_atTop.comp hψ.tendsto_atTop
  refine ⟨g, e, ?_, ?_, ?_, ?_, ?_⟩
  · exact hw.mem_of_closed_convex hCclosed hCconvex
      (Eventually.of_forall fun n => hC (φ (ψ n)))
  · intro k
    exact tendsto_nhds_unique (hw (X k)) ((hX k).comp hφψ)
  · exact (hw.sub_const f).norm_le_of_bounds (hδn.comp hφψ)
      (Eventually.of_forall fun n => hclose (φ (ψ n)))
  · exact testGraph_weak_limit A B hw he
      (Eventually.of_forall fun n => hgraph (φ (ψ n)))
  · exact tendsto_nhds_unique (he L) (hL.comp hφψ)

end FirstLimit

end TriangularBilliards.Analytic

namespace TriangularBilliards.Analytic

lemma exists_weak_subsequence_unrestricted
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (u : ℕ → E) {R : ℝ} (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ v : E, ‖v‖ ≤ R ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ WeaklyTendsto (u ∘ φ) atTop v := by
  let S := (Submodule.span ℝ (Set.range u)).topologicalClosure
  have hS : TopologicalSpace.IsSeparable (S : Set E) :=
    ((Set.countable_range u).isSeparable.span (R := ℝ)).closure
  let : TopologicalSpace.SeparableSpace S := hS.separableSpace
  let w (n : ℕ) : S := ⟨u n, Submodule.le_topologicalClosure _
    (Submodule.subset_span (Set.mem_range_self n))⟩
  obtain ⟨v,hv,φ,hφ,hw⟩ := exists_weak_subsequence w hu
  refine ⟨v.val,hv,φ,hφ,?_⟩
  intro L
  exact hw (L.comp S.subtypeL)

end TriangularBilliards.Analytic

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
end

section
section
namespace OAI


open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Finset Set
open scoped Topology BigOperators
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Set
open scoped Topology
noncomputable section

namespace TriangularBilliards.Analysis.HilbertFlow
open Analytic
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (W : HilbertFlow H)

omit [CompleteSpace H] in
lemma HasGenerator.weak_limit {α : Type uAlpha} {l : Filter α} [l.NeBot]
    {u a : α → H} {v b : H} (hu : WeaklyTendsto u l v) (ha : WeaklyTendsto a l b)
    (h : ∀ᶠ n in l, W.HasGenerator (u n) (a n)) : W.HasGenerator v b := by
  exact (hu.prod ha).mem_of_closed_convex W.generatorGraph_closed W.generatorGraph_convex h

lemma exists_generator_of_bounded_approx
    {u a : ℕ → H} {v : H} {C : ℝ}
    (hu : Tendsto u atTop (𝓝 v)) (ha : ∀ n, ‖a n‖ ≤ C)
    (h : ∀ n, W.HasGenerator (u n) (a n)) :
    ∃ b : H, W.HasGenerator v b ∧ ‖b‖ ≤ C := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  obtain ⟨b,hb,φ,hφ,hlim⟩ := exists_weak_subsequence_unrestricted a ha
  exact ⟨b, HasGenerator.weak_limit W
    ((weaklyTendsto_of_tendsto hu).comp hφ.tendsto_atTop) hlim
    (Eventually.of_forall fun n => h (φ n)), hb⟩

end TriangularBilliards.Analysis.HilbertFlow

namespace TriangularBilliards
open Analysis

lemma supported_smoothing_toLp_tendsto (Q : Triangle) {K : ℝ} (hK : 0 < K)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q))
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n => (supportedSmoothing_memLp_of_memLp Q (hε n) (K*ε n) hm hf).toLp
      (supportedSmoothing Q (ε n) (K*ε n) f)) atTop (𝓝 (hf.toLp f)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have he : Tendsto ε atTop (𝓝[>] (0 : ℝ)) := tendsto_nhdsWithin_iff.mpr
    ⟨hlim, Eventually.of_forall hε⟩
  convert (supported_smoothing_lpNorm_tendsto Q hK hm hf).comp he using 1
  ext n
  rw [← MemLp.toLp_sub, Lp.norm_toLp,
    toReal_eLpNorm ((supportedSmoothing_stronglyMeasurable Q (ε n) (K*ε n) hm).aestronglyMeasurable.sub hm.aestronglyMeasurable)]
  rfl

/-- Bounded modes for the nonsingular billiard unitary groups.
Only individual Fourier derivatives are bounded; this does not impose
a bound on the sum of all mode derivatives. -/
lemma bounded_invariant_modes (Q : Triangle) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {H : ℝ} {f : DoublePhase → ℂ}
      (_hm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q))
      (_hH : ∀ z, ‖f z‖ ≤ H)
      (_hfi : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) 0) (j : ℤ),
      ∃ dx dy : Lp ℂ 2 (doubleMeasure Q),
        (geodesicHilbertFlow Q).HasGenerator ((angularCircleAction Q).projection j (hf.toLp f)) dx ∧
        (transverseHilbertFlow Q).HasGenerator ((angularCircleAction Q).projection j (hf.toLp f)) dy ∧
        ‖dx‖ ≤ C * H ∧ ‖dy‖ ≤ C * H := by
  obtain ⟨C,hC,hbound⟩ := bounded_invariant_regularized_modes Q
  refine ⟨Real.sqrt C, Real.sqrt_nonneg C, ?_⟩
  intro H f hm hf hH hfi j
  have hH₀ : 0 ≤ H := (norm_nonneg _).trans (hH ((0,1),0))
  let K := Q.safetyFactor + 1
  have hK : 0 < K := by dsimp [K]; linarith [Q.safetyFactor_pos]
  have hnb : ∀ᶠ ε : ℝ in 𝓝 0, 2*(K*ε)*Q.coordinateBound < 1 := by
    have hc : Continuous (fun ε : ℝ => 2*(K*ε)*Q.coordinateBound) := by fun_prop
    simpa only [mul_zero, zero_mul] using hc.continuousAt.eventually
      (gt_mem_nhds (by simp only [mul_zero, zero_mul]; norm_num))
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp hnb
  obtain ⟨ε,_,hε,hlim⟩ := exists_seq_strictAnti_tendsto' hδ
  have hpos (n : ℕ) : 0 < ε n := (hε n).1
  have hsmall (n : ℕ) : 2*(K*ε n)*Q.coordinateBound < 1 :=
    hball (by simpa only [Real.dist_eq, sub_zero, abs_of_pos (hpos n)] using (hε n).2)
  let hw n := supportedSmoothing_memLp Q (hpos n) (K*ε n) hm hH
  let u n := (angularCircleAction Q).projection j
    ((hw n).toLp (supportedSmoothing Q (ε n) (K*ε n) f))
  have hu : Tendsto u atTop (𝓝 ((angularCircleAction Q).projection j (hf.toLp f))) :=
    ((angularCircleAction Q).projection j).continuous.tendsto _ |>.comp
      (supported_smoothing_toLp_tendsto Q hK hm hf hpos hlim)
  have hh (n : ℕ) := hbound hm hf hH hfi (hpos n) (hsmall n) j
  choose dx dy hgx hgy hbx hby using hh
  have hbd {a : ℝ} (ha : a^2 ≤ C*H^2) : a ≤ Real.sqrt C * H := by
    have hs := Real.sq_sqrt hC
    have hs' : (Real.sqrt C * H)^2 = C*H^2 := by rw [mul_pow, hs]
    exact (sq_le_sq₀ (by positivity : 0 ≤ |a|) (by positivity : 0 ≤ Real.sqrt C * H)).mp
      (by simpa only [sq_abs, hs'] using ha) |>.trans' (le_abs_self a)
  obtain ⟨ax,hax,hAx⟩ := (geodesicHilbertFlow Q).exists_generator_of_bounded_approx hu
    (fun n => hbd (hbx n)) hgx
  obtain ⟨ay,hay,hAy⟩ := (transverseHilbertFlow Q).exists_generator_of_bounded_approx hu
    (fun n => hbd (hby n)) hgy
  exact ⟨ax,ay,hax,hay,hAx,hAy⟩

end TriangularBilliards

namespace TriangularBilliards.Analytic
section Map
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {α : Type uAlpha} {l : Filter α}
lemma WeaklyTendsto.map {u : α → E} {v : E} (h : WeaklyTendsto u l v)
    (A : E →L[ℝ] F) : WeaklyTendsto (fun n => A (u n)) l (A v) :=
  fun L => h (L.comp A)
lemma WeaklyTendsto.add {u v : α → E} {a b : E}
    (hu : WeaklyTendsto u l a) (hv : WeaklyTendsto v l b) :
    WeaklyTendsto (fun n => u n + v n) l (a+b) := by
  intro L
  simpa only [map_add] using (hu L).add (hv L)
lemma WeaklyTendsto.sub {u v : α → E} {a b : E}
    (hu : WeaklyTendsto u l a) (hv : WeaklyTendsto v l b) :
    WeaklyTendsto (fun n => u n - v n) l (a-b) := by
  intro L
  simpa only [map_sub] using (hu L).sub (hv L)
end Map
end TriangularBilliards.Analytic

namespace TriangularBilliards.Analysis
open Analytic
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : ℝ} [Fact (0 < T)]
namespace RotationalCR
variable {X Y : HilbertFlow H} {V : CircleAction H T}

omit [CompleteSpace H] [Fact (0 < T)] in
lemma weak_limit {α : Type uAlpha} {l : Filter α} [l.NeBot]
    {u a b : α → H} {v c d : H}
    (hu : WeaklyTendsto u l v) (ha : WeaklyTendsto a l c) (hb : WeaklyTendsto b l d)
    (h : ∀ n, RotationalCR X Y V (u n) (a n) (b n)) : RotationalCR X Y V v c d := by
  intro θ
  let A := ((V.act θ).toContinuousLinearMap).restrictScalars ℝ
  let P : H →L[ℝ] H := (fourier (-1) θ • (V.act θ).toContinuousLinearMap).restrictScalars ℝ
  let M : H →L[ℝ] H := (fourier 1 θ • (V.act θ).toContinuousLinearMap).restrictScalars ℝ
  let I : H →L[ℝ] H := (Complex.I • ContinuousLinearMap.id ℂ H).restrictScalars ℝ
  exact ⟨HilbertFlow.HasGenerator.weak_limit X (hu.map A) ((ha.map P).add (hb.map M))
      (Eventually.of_forall fun n => (h n θ).1),
    HilbertFlow.HasGenerator.weak_limit Y (hu.map A) (((ha.map P).sub (hb.map M)).map I)
      (Eventually.of_forall fun n => (h n θ).2)⟩

omit [Fact (0 < T)] in
lemma exists_of_bounded_approx {u a b : ℕ → H} {v : H} {C : ℝ}
    (hu : Tendsto u atTop (𝓝 v)) (ha : ∀ n, ‖a n‖ ≤ C) (hb : ∀ n, ‖b n‖ ≤ C)
    (h : ∀ n, RotationalCR X Y V (u n) (a n) (b n)) :
    ∃ c d, RotationalCR X Y V v c d ∧ ‖c‖ ≤ C ∧ ‖d‖ ≤ C := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  obtain ⟨c,hc,φ,hφ,hac⟩ := exists_weak_subsequence_unrestricted a ha
  obtain ⟨d,hd,ψ,hψ,hbd⟩ := exists_weak_subsequence_unrestricted (b ∘ φ) (fun n => hb (φ n))
  exact ⟨c,d,weak_limit ((weaklyTendsto_of_tendsto hu).comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop))
    (hac.comp hψ.tendsto_atTop) hbd (fun n => h (φ (ψ n))), hc, hd⟩

/-- In a single Fourier mode, the two CR components are exactly the two
Fourier components of its geodesic generator. -/
lemma components_unique {u a b dx : H} {j : ℤ}
    (h : RotationalCR X Y V u a b)
    (ha : V.projection (j+1) a = a) (hb : V.projection (j-1) b = b)
    (hx : X.HasGenerator u dx) :
    a = V.projection (j+1) dx ∧ b = V.projection (j-1) dx := by
  have he : dx = a+b := X.generator_unique hx h.generators.1
  rw [he, map_add, map_add, ha, hb]
  have hab : V.projection (j+1) b = 0 := by
    rw [← hb, V.projection_mul, ite_eq_right (by omega)]
  have hba : V.projection (j-1) a = 0 := by
    rw [← ha, V.projection_mul, ite_eq_right (by omega)]
  simp only [hab,hba,add_zero,zero_add,and_self]

end RotationalCR
end TriangularBilliards.Analysis

namespace TriangularBilliards
open Analysis
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

lemma supportedSmoothing_rotationalCR (Q : Triangle) {ε R : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor * ε < R)
    (hsmall : 2 * R * Q.coordinateBound < 1)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {H : ℝ} (hf : ∀ z, ‖f z‖ ≤ H) :
    let hw := supportedSmoothing_memLp Q hε R hm hf
    ∃ a b, RotationalCR (geodesicHilbertFlow Q) (transverseHilbertFlow Q) (angularCircleAction Q)
      (hw.toLp _) a b := by
  dsimp only
  obtain ⟨C,hC⟩ := supportedSmoothing_fderiv_bound Q hε
    ((mul_pos Q.safetyFactor_pos hε).trans hR) hm hf
  have hd := fun v b => (supportedSmoothing_contDiff Q hε R hm hf v b).differentiable (by simp)
  have hm' := (supportedSmoothing_stronglyMeasurable Q ε R hm).measurable
  have hx := xDerivative_memLp_of_gradient_bound Q hm' hd hC
  have hy := yDerivative_memLp_of_gradient_bound Q hm' hd hC
  exact ⟨_,_,seam_rotationalCR (supportedSmoothing_seam Q hε hR hsmall f) hd hC
    (supportedSmoothing_memLp Q hε R hm hf) hx hy⟩

lemma bounded_invariant_regularized_CR (Q : Triangle) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {H : ℝ} {f : DoublePhase → ℂ}
      (hm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q))
      (hH : ∀ z, ‖f z‖ ≤ H)
      (_hfi : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) 0)
      {ε : ℝ} (hε : 0 < ε)
      (_hsmall : 2 * ((Q.safetyFactor + 1) * ε) * Q.coordinateBound < 1) (j : ℤ),
      let w := supportedSmoothing Q ε ((Q.safetyFactor + 1) * ε) f
      let hw := supportedSmoothing_memLp Q hε ((Q.safetyFactor + 1) * ε) hm hH
      ∃ a b : Lp ℂ 2 (doubleMeasure Q),
        RotationalCR (geodesicHilbertFlow Q) (transverseHilbertFlow Q) (angularCircleAction Q)
          ((angularCircleAction Q).projection j (hw.toLp w)) a b ∧
        ‖a‖ ^ 2 ≤ C * H^2 ∧ ‖b‖ ^ 2 ≤ C * H^2 := by
  obtain ⟨C,hC,hbound⟩ := bounded_invariant_regularized_modes Q
  refine ⟨C,hC,?_⟩
  intro H f hm hf hH hfi ε hε hsmall j
  obtain ⟨dx,dy,hgx,_,hbx,_⟩ := hbound hm hf hH hfi hε hsmall j
  have hR : Q.safetyFactor * ε < (Q.safetyFactor+1)*ε := by nlinarith
  obtain ⟨a,b,hcr⟩ := supportedSmoothing_rotationalCR Q hε hR hsmall hm hH
  have hc := hcr.projection_covariant j
  have hh := hc.components_unique ((angularCircleAction Q).projection_idem _ a)
    ((angularCircleAction Q).projection_idem _ b) hgx
  refine ⟨_,_,hc,?_,?_⟩
  · exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (hh.1 ▸ (angularCircleAction Q).projection_norm_le (j+1) dx) |>.trans hbx
  · exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (hh.2 ▸ (angularCircleAction Q).projection_norm_le (j-1) dx) |>.trans hbx

end TriangularBilliards

namespace TriangularBilliards
open Analysis
lemma bounded_invariant_CR (Q : Triangle) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {H : ℝ} {f : DoublePhase → ℂ}
      (_hm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q))
      (_hH : ∀ z, ‖f z‖ ≤ H)
      (_hfi : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) 0) (j : ℤ),
      ∃ dx dy : Lp ℂ 2 (doubleMeasure Q),
        RotationalCR (geodesicHilbertFlow Q) (transverseHilbertFlow Q) (angularCircleAction Q)
          ((angularCircleAction Q).projection j (hf.toLp f)) dx dy ∧
        ‖dx‖ ≤ C * H ∧ ‖dy‖ ≤ C * H := by
  obtain ⟨C,hC,hbound⟩ := bounded_invariant_regularized_CR Q
  refine ⟨Real.sqrt C, Real.sqrt_nonneg C, ?_⟩
  intro H f hm hf hH hfi j
  have hH₀ : 0 ≤ H := (norm_nonneg _).trans (hH ((0,1),0))
  let K := Q.safetyFactor + 1
  have hK : 0 < K := by dsimp [K]; linarith [Q.safetyFactor_pos]
  have hnb : ∀ᶠ ε : ℝ in 𝓝 0, 2*(K*ε)*Q.coordinateBound < 1 := by
    have hc : Continuous (fun ε : ℝ => 2*(K*ε)*Q.coordinateBound) := by fun_prop
    simpa only [mul_zero, zero_mul] using hc.continuousAt.eventually
      (gt_mem_nhds (by simp only [mul_zero, zero_mul]; norm_num))
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp hnb
  obtain ⟨ε,_,hε,hlim⟩ := exists_seq_strictAnti_tendsto' hδ
  have hpos (n : ℕ) : 0 < ε n := (hε n).1
  have hsmall (n : ℕ) : 2*(K*ε n)*Q.coordinateBound < 1 :=
    hball (by simpa only [Real.dist_eq, sub_zero, abs_of_pos (hpos n)] using (hε n).2)
  let hw n := supportedSmoothing_memLp Q (hpos n) (K*ε n) hm hH
  let u n := (angularCircleAction Q).projection j
    ((hw n).toLp (supportedSmoothing Q (ε n) (K*ε n) f))
  have hu : Tendsto u atTop (𝓝 ((angularCircleAction Q).projection j (hf.toLp f))) :=
    ((angularCircleAction Q).projection j).continuous.tendsto _ |>.comp
      (supported_smoothing_toLp_tendsto Q hK hm hf hpos hlim)
  have hh (n : ℕ) := hbound hm hf hH hfi (hpos n) (hsmall n) j
  choose dx dy hcr hbx hby using hh
  have hbd {a : ℝ} (ha : a^2 ≤ C*H^2) : a ≤ Real.sqrt C * H := by
    have hs := Real.sq_sqrt hC
    have hs' : (Real.sqrt C * H)^2 = C*H^2 := by rw [mul_pow, hs]
    exact (sq_le_sq₀ (by positivity : 0 ≤ |a|) (by positivity : 0 ≤ Real.sqrt C * H)).mp
      (by simpa only [sq_abs, hs'] using ha) |>.trans' (le_abs_self a)
  exact RotationalCR.exists_of_bounded_approx hu (fun n => hbd (hbx n))
    (fun n => hbd (hby n)) hcr

end TriangularBilliards

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
end

section
section
namespace OAI


open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Finset Set
open scoped Topology BigOperators
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Set
open scoped Topology
noncomputable section

namespace TriangularBilliards.Analysis
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : ℝ} [Fact (0 < T)]

omit [CompleteSpace H] in
lemma CR_components_eq {a b c d : H} (hx : a+b=c+d)
    (hy : Complex.I • (a-b) = Complex.I • (c-d)) : a=c ∧ b=d := by
  have hd : a-b=c-d := smul_right_injective H Complex.I_ne_zero hy
  have haa : (2 : ℂ) • a = (2 : ℂ) • c := by
    calc
      _ = (a+b)+(a-b) := by module
      _ = (c+d)+(c-d) := by rw [hx,hd]
      _ = _ := by module
  have ha := smul_right_injective H (by norm_num : (2 : ℂ) ≠ 0) haa
  exact ⟨ha, add_left_cancel (ha ▸ hx)⟩

namespace RotationalCR
variable {X Y : HilbertFlow H} {V : CircleAction H T}
lemma mode_components {u a b : H} {j : ℤ} (h : RotationalCR X Y V u a b)
    (hu : ∀ θ, V.act θ u = fourier j θ • u) :
    V.projection (j+1) a = a ∧ V.projection (j-1) b = b := by
  have he (θ : AddCircle T) :
      fourier (-1) θ • V.act θ a = fourier j θ • a ∧
      fourier 1 θ • V.act θ b = fourier j θ • b := by
    have hx := (h.generators.1).smul (fourier j θ)
    have hy := (h.generators.2).smul (fourier j θ)
    rw [← hu θ] at hx hy
    exact CR_components_eq
      (by simpa only [smul_add] using X.generator_unique (h θ).1 hx)
      (by simpa only [smul_sub, smul_comm (fourier j θ) Complex.I] using
        Y.generator_unique (h θ).2 hy)
  have ha (θ : AddCircle T) : V.act θ a = fourier (j+1) θ • a := by
    have hc := congrArg (fun x : H => fourier 1 θ • x) (he θ).1
    simpa only [smul_smul, ← fourier_add, show (1 : ℤ)+(-1)=0 by norm_num,
      fourier_zero, Pi.one_apply, one_smul, show (1 : ℤ)+j=j+1 by omega] using hc
  have hb (θ : AddCircle T) : V.act θ b = fourier (j-1) θ • b := by
    have hc := congrArg (fun x : H => fourier (-1) θ • x) (he θ).2
    simpa only [smul_smul, ← fourier_add, show (-1 : ℤ)+1=0 by norm_num,
      fourier_zero, Pi.one_apply, one_smul, show (-1 : ℤ)+j=j-1 by omega] using hc
  exact ⟨by simpa using V.projection_of_eigen ha (j+1),
    by simpa using V.projection_of_eigen hb (j-1)⟩
end RotationalCR
end TriangularBilliards.Analysis

namespace TriangularBilliards.Analysis
open Analytic
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : ℝ} [Fact (0 < T)]
namespace CircleAction
variable (V : CircleAction H T)

lemma inner_of_modes {a b : H} {j k : ℤ} (ha : V.projection j a = a)
    (hb : V.projection k b = b) (hjk : j ≠ k) : inner ℂ a b = 0 := by
  rw [← ha, ← hb]
  exact V.projection_orthogonal hjk a b

lemma mode_inner_right {a b : H} {j : ℤ} (ha : V.projection j a = a) :
    inner ℂ a (V.projection j b) = inner ℂ a b := by
  rw [← V.projection_adjoint, ha]

lemma mode_inner_left {a b : H} {j : ℤ} (hb : V.projection j b = b) :
    inner ℂ (V.projection j a) b = inner ℂ a b := by
  rw [V.projection_adjoint, hb]

end CircleAction

/-- The Fourier recurrence from exact invariance, justified on a dense
regular CR core and then on all L2 tests. It never differentiates an
infinite Fourier series term by term. -/
lemma invariant_CR_recurrence (X Y : HilbertFlow H) (V : CircleAction H T)
    (hD : Dense {v : H | ∃ c d, RotationalCR X Y V v c d})
    {f : H} (hf : X.HasGenerator f 0) (a b : ℤ → H)
    (hg : ∀ j, RotationalCR X Y V (V.projection j f) (a j) (b j)) (m : ℤ) :
    a m + b (m+2) = 0 := by
  have hmodes j := (hg j).mode_components (V.projection_eigen j f)
  have ha := (hmodes m).1
  have hb := (hmodes (m+2)).2
  have hb' : V.projection (m+1) (b (m+2)) = b (m+2) := by
    simpa only [show m+2-1=m+1 by omega] using hb
  have htest (v : H) (hv : ∃ c d, RotationalCR X Y V v c d) :
      inner ℂ (a m+b (m+2)) v = 0 := by
    obtain ⟨c,d,hv⟩ := hv
    have hp := (hv.projection (m+1)).1
    have hpf : X.HasGenerator (V.projection (m+1) v)
        (V.projection (m+2) c + V.projection m d) := by
      simpa only [show m+1+1=m+2 by omega, show m+1-1=m by omega] using hp
    have h0 := X.generator_skew hf hpf
    simp only [inner_zero_left, add_zero] at h0
    have h1 := X.generator_skew (hg m).generators.1 hpf
    have h2 := X.generator_skew (hg (m+2)).generators.1 hpf
    have hmc : inner ℂ (V.projection m f) (V.projection (m+2) c) = 0 :=
      V.projection_orthogonal (by omega) f c
    have hpmd : inner ℂ (V.projection (m+2) f) (V.projection m d) = 0 :=
      V.projection_orthogonal (by omega) f d
    have hmb : inner ℂ (b m) (V.projection (m+1) v) = 0 :=
      V.inner_of_modes (hmodes m).2 (V.projection_idem _ v) (by omega)
    have hpa : inner ℂ (a (m+2)) (V.projection (m+1) v) = 0 :=
      V.inner_of_modes (hmodes (m+2)).1 (V.projection_idem _ v) (by omega)
    simp only [inner_add_left, inner_add_right, hmc, hpmd, hmb, hpa,
      zero_add, add_zero, V.mode_inner_left (V.projection_idem m d),
      V.mode_inner_left (V.projection_idem (m+2) c), V.mode_inner_right ha,
      V.mode_inner_right hb'] at h1 h2
    rw [inner_add_left]
    rw [inner_add_right] at h0
    linear_combination h1 + h2 - h0
  have hall : ∀ v : H, inner ℂ (a m+b (m+2)) v = 0 :=
    hD.induction htest (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
  exact inner_self_eq_zero.mp (hall (a m+b (m+2)))

omit [CompleteSpace H] in
lemma HilbertFlow.HasGenerator.zero (W : HilbertFlow H) : W.HasGenerator 0 0 := by
  intro t
  simp only [map_zero, sub_zero]

omit [CompleteSpace H] in
lemma HilbertFlow.HasGenerator.sum (W : HilbertFlow H) {ι : Type uIota}
    (s : Finset ι) (u a : ι → H) (h : ∀ i ∈ s, W.HasGenerator (u i) (a i)) :
    W.HasGenerator (∑ i ∈ s, u i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using HasGenerator.zero W
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

lemma CircleAction.bounded_modes_weaklyTendsto (V : CircleAction H T)
    {φ : ℕ → ℤ} (hφ : Function.Injective φ) (r : ℕ → H) {C : ℝ}
    (hC : ∀ n, ‖r n‖ ≤ C) (hr : ∀ n, V.projection (φ n) (r n) = r n) :
    WeaklyTendsto r atTop 0 := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  intro L
  let v := (InnerProductSpace.toDual ℝ H).symm L
  have hv (x : H) : inner ℝ v x = L x := InnerProductSpace.toDual_symm_apply
  have he := (Complex.continuous_re.tendsto 0).comp (V.bounded_modes_escape hφ r hC hr v)
  change Tendsto (fun n => (inner ℂ v (r n)).re) atTop (𝓝 (0 : ℝ)) at he
  have heq (x : H) : (inner ℂ v x).re = L x := hv x
  simpa only [heq, map_zero] using he

/-- The one-sided parity tail has the claimed L2 generator. The uniformly
bounded terminal term disappears WEAKLY by escaping angular frequency. -/
lemma parity_tail_endpoint (X Y : HilbertFlow H) (V : CircleAction H T)
    (hD : Dense {v : H | ∃ c d, RotationalCR X Y V v c d})
    {f : H} (hf : X.HasGenerator f 0) (a b : ℤ → H)
    (hg : ∀ j, RotationalCR X Y V (V.projection j f) (a j) (b j))
    {C : ℝ} (ha : ∀ j, ‖a j‖ ≤ C) (m : ℤ) :
    X.HasGenerator (V.parityTail m f) (b m) := by
  have hrec := invariant_CR_recurrence X Y V hD hf a b hg
  let U (N : ℕ) := ∑ n ∈ Finset.range (N+1), V.projection (m+2*(n : ℤ)) f
  let R (N : ℕ) := a (m+2*(N : ℤ))
  have hfinite (N : ℕ) : X.HasGenerator (U N) (b m + R N) := by
    induction N with
    | zero => simpa only [U,R,Nat.zero_add,Finset.sum_range_one,Nat.cast_zero,mul_zero,add_zero,add_comm]
        using (hg m).generators.1
    | succ N ih =>
      have h := ih.add (hg (m+2*((N+1 : ℕ) : ℤ))).generators.1
      have he : b m + R N + (a (m+2*((N+1 : ℕ) : ℤ)) + b (m+2*((N+1 : ℕ) : ℤ))) =
          b m + R (N+1) := by
        have hi : m+2*((N+1 : ℕ) : ℤ)=m+2*(N : ℤ)+2 := by push_cast; ring
        have hr := hrec (m+2*(N : ℤ))
        dsimp only [R]
        rw [hi]
        calc
          _ = b m + a (m+2*(N : ℤ)+2) + (a (m+2*(N : ℤ))+b (m+2*(N : ℤ)+2)) := by abel
          _ = _ := by rw [hr,add_zero]
      simpa only [U,Finset.sum_range_succ,he] using h
  have hu := (V.parityTail_convergence m f).comp (tendsto_add_atTop_nat 1)
  have hm (N : ℕ) : V.projection (m+1+2*(N : ℤ)) (R N) = R N := by
    have hh := ((hg (m+2*(N : ℤ))).mode_components
      (V.projection_eigen (m+2*(N : ℤ)) f)).1
    convert hh using 1
    congr 2
    ring
  have hr := V.bounded_modes_weaklyTendsto (CircleAction.parity_index_injective (m+1)) R
    (fun N => ha _) hm
  have hb : WeaklyTendsto (fun N => b m + R N) atTop (b m) := by
    simpa only [add_zero] using (weaklyTendsto_of_tendsto (tendsto_const_nhds (x := b m))).add hr
  exact HilbertFlow.HasGenerator.weak_limit X (weaklyTendsto_of_tendsto hu) hb
    (Eventually.of_forall hfinite)

end TriangularBilliards.Analysis

namespace TriangularBilliards
open Analysis Filter Set
open scoped Topology BoundedContinuousFunction

lemma dense_rotationalCR_core (Q : Triangle) :
    Dense {v : DoubleL2 Q | ∃ a b, RotationalCR (geodesicHilbertFlow Q)
      (transverseHilbertFlow Q) (angularCircleAction Q) v a b} := by
  let D : Set (DoubleL2 Q) := {v | ∃ a b, RotationalCR (geodesicHilbertFlow Q)
    (transverseHilbertFlow Q) (angularCircleAction Q) v a b}
  have hb (g : DoublePhase →ᵇ ℂ) (hg : MemLp (g : DoublePhase → ℂ) 2 (doubleMeasure Q)) :
      hg.toLp g ∈ closure D := by
    let K := Q.safetyFactor + 1
    have hK : 0 < K := by dsimp [K]; linarith [Q.safetyFactor_pos]
    have hnb : ∀ᶠ ε : ℝ in 𝓝 0, 2*(K*ε)*Q.coordinateBound < 1 := by
      have hc : Continuous (fun ε : ℝ => 2*(K*ε)*Q.coordinateBound) := by fun_prop
      simpa only [mul_zero, zero_mul] using hc.continuousAt.eventually
        (gt_mem_nhds (by simp only [mul_zero, zero_mul]; norm_num))
    obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp hnb
    obtain ⟨ε,_,hε,hlim⟩ := exists_seq_strictAnti_tendsto' hδ
    have hpos (n : ℕ) : 0 < ε n := (hε n).1
    have hsmall (n : ℕ) : 2*(K*ε n)*Q.coordinateBound < 1 :=
      hball (by simpa only [Real.dist_eq, sub_zero, abs_of_pos (hpos n)] using (hε n).2)
    apply isClosed_closure.mem_of_tendsto
      (supported_smoothing_toLp_tendsto Q hK g.continuous.stronglyMeasurable hg hpos hlim)
    apply Eventually.of_forall
    intro n
    apply subset_closure
    exact supportedSmoothing_rotationalCR Q (hpos n)
      (by dsimp only [K]; nlinarith [hpos n]) (hsmall n)
      g.continuous.stronglyMeasurable g.norm_coe_le_norm
  intro u
  rw [← closure_closure (s := D)]
  apply Metric.mem_closure_iff.mpr
  intro δ hδ
  obtain ⟨g,hg,hgp⟩ := (Lp.memLp u).exists_boundedContinuous_eLpNorm_sub_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (ENNReal.ofReal_ne_zero_iff.mpr (by positivity : 0 < δ/2))
  refine ⟨hgp.toLp g,hb g hgp,?_⟩
  rw [dist_eq_norm, ← Lp.toLp_coeFn u (Lp.memLp u), ← MemLp.toLp_sub, Lp.norm_toLp]
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hg
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ δ/2)] at hh
  exact hh.trans_lt (by linarith)

/-- The actual triangular parity-tail endpoint. There is no unproved
smooth-core density assumption remaining in this application. -/
lemma bounded_invariant_tail_endpoint (Q : Triangle) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {H : ℝ} {f : DoublePhase → ℂ}
      (_hm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q))
      (_hH : ∀ z, ‖f z‖ ≤ H)
      (_hfi : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) 0),
      ∃ a b : ℤ → DoubleL2 Q,
        (∀ j, RotationalCR (geodesicHilbertFlow Q) (transverseHilbertFlow Q)
          (angularCircleAction Q) ((angularCircleAction Q).projection j (hf.toLp f)) (a j) (b j)) ∧
        (∀ j, ‖a j‖ ≤ C*H ∧ ‖b j‖ ≤ C*H) ∧
        ∀ m, (geodesicHilbertFlow Q).HasGenerator
          ((angularCircleAction Q).parityTail m (hf.toLp f)) (b m) := by
  obtain ⟨C,hC,hbound⟩ := bounded_invariant_CR Q
  refine ⟨C,hC,?_⟩
  intro H f hm hf hH hfi
  choose a b hg ha hb using fun j => hbound hm hf hH hfi j
  refine ⟨a,b,hg,fun j => ⟨ha j,hb j⟩,?_⟩
  exact fun m => parity_tail_endpoint _ _ _ (dense_rotationalCR_core Q) hfi a b hg ha m

end TriangularBilliards

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
end

section
section
namespace OAI

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Finset Set
open scoped Topology BigOperators
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Set
open scoped Topology
noncomputable section

namespace TriangularBilliards
open Analysis SpatialSmoothing Filter
open scoped Topology ComplexConjugate

/-- Local transport commutation with a nonzero generator, obtained from
unitary skew-adjointness and actual kernel adjoint identities. -/
lemma smoothing_direction_pairing (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor * ε < R)
    (hsmall : 2 * R * Q.coordinateBound < 1) (hA : 2 * R + ε ≤ A)
    {f p g : DoublePhase → ℂ} (hfm : StronglyMeasurable f)
    (hpm : StronglyMeasurable p) (hgm : StronglyMeasurable g)
    (hf : MemLp f 2 (doubleMeasure Q)) (hp : MemLp p 2 (doubleMeasure Q))
    (hg : MemLp g 2 (doubleMeasure Q))
    (hfp : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) (hp.toLp p))
    {H : ℝ} (hH : ∀ z, ‖g z‖ ≤ H) (hgs : SpatiallyZero Q A g) :
    (∫ z, reflectedSmoothingGradient Q ε f z (z.1.2 : ℂ) * conj (g z) ∂doubleMeasure Q) =
      (∫ z, reflectedSmoothing Q ε p z * conj (g z) ∂doubleMeasure Q) := by
  have h := reflectedSmoothingGradient_adjoint Q hε
    (V := fun c => (c.1 : ℂ)) (show Continuous (fun c : DirectionParity => (c.1 : ℂ)) from
      continuous_subtype_val.comp continuous_fst).stronglyMeasurable
    (fun c => (Circle.norm_coe _).le) (fun i c => rfl) hfm hgm hf hg
  have hgen := reflectedSmoothing_supported_generator Q hε hR hsmall hA hgm hH hg hgs
  have hsk := (geodesicHilbertFlow Q).generator_skew hgen hfp
  rw [h, reflectedSmoothing_adjoint Q hε hpm hgm hp hg,
    integral_pairing_toLp hf (reflectedSmoothing_direction_memLp Q hε hgm hg),
    integral_pairing_toLp hp (reflectedSmoothing_memLp Q hε hgm hg)]
  linear_combination -hsk

lemma smoothing_direction_local (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor * ε < R)
    (hsmall : 2 * R * Q.coordinateBound < 1) (hA : 2 * R + ε ≤ A)
    {f p : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hpm : StronglyMeasurable p)
    (hf : MemLp f 2 (doubleMeasure Q)) (hp : MemLp p 2 (doubleMeasure Q))
    (hfp : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) (hp.toLp p))
    {H J : ℝ} (hH : ∀ z, ‖f z‖ ≤ H) (hJ : ∀ z, ‖p z‖ ≤ J) :
    ∀ᵐ z ∂doubleMeasure Q, A ≤ Q.clearance z.1.1 →
      reflectedSmoothingGradient Q ε f z (z.1.2 : ℂ) = reflectedSmoothing Q ε p z := by
  let D : DoublePhase → ℂ := fun z =>
    reflectedSmoothingGradient Q ε f z (z.1.2 : ℂ) - reflectedSmoothing Q ε p z
  let E : Set DoublePhase := {z | A ≤ Q.clearance z.1.1}
  let g : DoublePhase → ℂ := E.indicator D
  have hE : MeasurableSet E := measurableSet_le measurable_const
    (Q.clearance_lipschitz.continuous.measurable.comp (measurable_fst.fst))
  have hDm : StronglyMeasurable D := (reflectedSmoothing_direction_stronglyMeasurable Q ε hfm).sub
    (reflectedSmoothing_stronglyMeasurable Q ε hpm)
  have hDp : MemLp D 2 (doubleMeasure Q) := (reflectedSmoothing_direction_memLp Q hε hfm hf).sub
    (reflectedSmoothing_memLp Q hε hpm hp)
  have hgm : StronglyMeasurable g := hDm.indicator hE
  have hgp : MemLp g 2 (doubleMeasure Q) := hDp.indicator hE
  have hH₀ : 0 ≤ H := (norm_nonneg _).trans (hH ((0,1),0))
  have hJ₀ : 0 ≤ J := (norm_nonneg _).trans (hJ ((0,1),0))
  let C := 4 * derivativeMass * H / ε + 4*J
  have hC : 0 ≤ C := by
    have := derivativeMass_nonneg
    dsimp [C]
    positivity
  have hgb : ∀ z, ‖g z‖ ≤ C := by
    intro z
    by_cases hz : z ∈ E
    · change ‖E.indicator D z‖ ≤ _
      rw [Set.indicator_of_mem hz]
      exact (norm_sub_le _ _).trans (add_le_add
        (reflectedSmoothing_direction_norm_bound Q hε hH₀ hH z)
        (reflectedSmoothing_norm_bound Q hε hJ₀ hJ z))
    · change ‖E.indicator D z‖ ≤ _
      rw [Set.indicator_of_notMem hz, norm_zero]
      exact hC
  have hgs : SpatiallyZero Q A g := by
    intro y _ hy v b
    exact Set.indicator_of_notMem (show ((y,v),b) ∉ E from not_le.mpr hy) D
  have hpair := smoothing_direction_pairing Q hε hR hsmall hA hfm hpm hgm hf hp hgp hfp hgb hgs
  have he : (∫ z, g z * conj (g z) ∂doubleMeasure Q) = 0 := by
    have hDz : (∫ z, D z * conj (g z) ∂doubleMeasure Q) = 0 := by
      simp only [D, sub_mul]
      calc
        _ = (∫ z, reflectedSmoothingGradient Q ε f z (z.1.2 : ℂ) * conj (g z) ∂doubleMeasure Q) -
            (∫ z, reflectedSmoothing Q ε p z * conj (g z) ∂doubleMeasure Q) := by
          convert integral_sub ((reflectedSmoothing_direction_memLp Q hε hfm hf).integrable_mul (memLp_conj hgp))
            ((reflectedSmoothing_memLp Q hε hpm hp).integrable_mul (memLp_conj hgp)) using 1 <;> try rfl
        _ = 0 := sub_eq_zero.mpr hpair
    rw [← hDz]
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : z ∈ E
    · simp only [g, Set.indicator_of_mem hz]
    · simp only [g, Set.indicator_of_notMem hz, map_zero, mul_zero]
  rw [integral_pairing_toLp hgp hgp, inner_self_eq_zero] at he
  have hgz : g =ᵐ[doubleMeasure Q] 0 := by
    have hh := hgp.coeFn_toLp
    rw [he] at hh
    exact hh.symm.trans (Lp.coeFn_zero _ _ _)
  filter_upwards [hgz] with z hz hza
  apply sub_eq_zero.mp
  change D z = 0
  simpa only [g, Set.indicator_of_mem (show z ∈ E from hza), Pi.zero_apply] using hz

end TriangularBilliards

namespace TriangularBilliards
open Analysis SpatialSmoothing Filter
open scoped Topology ComplexConjugate

lemma reflectedSmoothingGradient_zero_near_tips (Q : Triangle) {ε A : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hs : SpatiallyZero Q A f) (hm : StronglyMeasurable f)
    {H : ℝ} (hH : ∀ z, ‖f z‖ ≤ H) {z : DoublePhase}
    (hz : z.1.1 ∈ Q.table) (hA : Q.clearance z.1.1 + ε < A) :
    reflectedSmoothingGradient Q ε f z = 0 := by
  have he : (fun y => reflectedSmoothing Q ε f ((y,z.1.2),z.2)) =ᶠ[𝓝 z.1.1] fun _ => 0 := by
    have hc : Continuous (fun y => Q.clearance y + ε) := Q.clearance_lipschitz.continuous.add continuous_const
    filter_upwards [isOpen_interior.eventually_mem hz,
      hc.continuousAt.eventually (gt_mem_nhds hA)] with y hy hr
    exact reflectedSmoothing_zero_near_tips Q hε hs hy hr.le
  rw [← (reflectedSmoothing_hasFDerivAt Q hε hm
    (bounded_spatialSlice_integrable Q hm hH z.1.2 z.2)
    (fun i => bounded_spatialSlice_integrable Q hm hH (reflectedDirection Q i z.1.2) (z.2+1))
    z.1.1).fderiv]
  rw [he.fderiv_eq, fderiv_const_apply]

/-- Global commutation for inputs and their generators with a genuine
vertex margin. The local identity extends by zero, not by a boundary claim. -/
lemma smoothing_direction_of_supported (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor * ε < R)
    (hsmall : 2 * R * Q.coordinateBound < 1) (hA : 2 * R + 2 * ε ≤ A)
    {f p : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hpm : StronglyMeasurable p)
    (hf : MemLp f 2 (doubleMeasure Q)) (hp : MemLp p 2 (doubleMeasure Q))
    (hfp : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) (hp.toLp p))
    {H J : ℝ} (hH : ∀ z, ‖f z‖ ≤ H) (hJ : ∀ z, ‖p z‖ ≤ J)
    (hfs : SpatiallyZero Q A f) (hps : SpatiallyZero Q A p) :
    (fun z => reflectedSmoothingGradient Q ε f z (z.1.2 : ℂ)) =ᵐ[doubleMeasure Q]
      reflectedSmoothing Q ε p := by
  have hl := smoothing_direction_local Q hε hR hsmall (le_refl (2*R+ε)) hfm hpm hf hp hfp hH hJ
  filter_upwards [hl,ae_double_position_in_table Q] with z hz htable
  by_cases hc : 2*R+ε ≤ Q.clearance z.1.1
  · exact hz hc
  · have hcs : Q.clearance z.1.1 + ε < A := by linarith
    rw [reflectedSmoothingGradient_zero_near_tips Q hε hfs hfm hH htable hcs,
      zero_apply, reflectedSmoothing_zero_near_tips Q hε hps htable hcs.le]

lemma supportedSmoothing_generator_commutes (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor * ε < R)
    (hsmall : 2 * R * Q.coordinateBound < 1) (hA : 2 * R + 2 * ε ≤ A)
    {f p : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hpm : StronglyMeasurable p)
    (hf : MemLp f 2 (doubleMeasure Q)) (hp : MemLp p 2 (doubleMeasure Q))
    (hfp : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) (hp.toLp p))
    {H J : ℝ} (hH : ∀ z, ‖f z‖ ≤ H) (hJ : ∀ z, ‖p z‖ ≤ J)
    (hfs : SpatiallyZero Q A f) (hps : SpatiallyZero Q A p) :
    (geodesicHilbertFlow Q).HasGenerator
      ((supportedSmoothing_memLp Q hε R hfm hH).toLp _)
      ((supportedSmoothing_memLp Q hε R hpm hJ).toLp _) := by
  have hRp := (mul_pos Q.safetyFactor_pos hε).trans hR
  have hA' : 2*R+ε ≤ A := by linarith
  have hgen := supportedSmoothing_generator Q hε hR hsmall hfm hH
  have he := smoothing_direction_of_supported Q hε hR hsmall hA hfm hpm hf hp hfp hH hJ hfs hps
  have hcongr := (supportedSmoothing_xDerivative_memLp Q hε hRp hfm hH).toLp_congr
    (supportedSmoothing_memLp Q hε R hpm hJ) (by
      filter_upwards [ae_double_position_in_table Q,he] with z hz hh
      rw [supportedSmoothing_derivative_eq_of_supported Q hε hRp hA' hfs hfm hH hz,
        hh, supportedSmoothing_eq_of_supported Q hε hRp hA' hps hz])
  dsimp only at hgen
  rwa [hcongr] at hgen

end TriangularBilliards

namespace TriangularBilliards
open Analysis SpatialSmoothing Filter
open scoped Topology ComplexConjugate NNReal ContDiff

lemma transverseVelocity_stronglyMeasurable :
    StronglyMeasurable (fun c : DirectionParity => transverseVelocity c.1 c.2) := by
  unfold transverseVelocity
  have hc : Measurable (fun c : DirectionParity => if c.2 = 0 then (Complex.I : ℂ) else -Complex.I) :=
    measurable_const.ite (measurableSet_eq_fun measurable_snd measurable_const) measurable_const
  have hv : Continuous (fun c : DirectionParity => (c.1 : ℂ)) := by fun_prop
  exact (hc.mul hv.measurable).stronglyMeasurable

def reflectedSmoothingY (Q : Triangle) (ε : ℝ) (f : DoublePhase → ℂ) : DoublePhase → ℂ :=
  fun z => reflectedSmoothingGradient Q ε f z (transverseVelocity z.1.2 z.2)

lemma reflectedSmoothingY_memLp (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q)) :
    MemLp (reflectedSmoothingY Q ε f) 2 (doubleMeasure Q) :=
  gradientApply_memLp (reflectedSmoothingGradient_memLp Q hε hm hf)
    (transverseVelocity_stronglyMeasurable.comp_measurable (measurable_fst.snd.prodMk measurable_snd))
    (fun _z => (norm_transverseVelocity _ _).le)

lemma reflectedSmoothingY_adjoint (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f g : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hf : MemLp f 2 (doubleMeasure Q)) (hg : MemLp g 2 (doubleMeasure Q)) :
    (∫ z, reflectedSmoothingY Q ε f z * conj (g z) ∂doubleMeasure Q) =
      -(∫ z, f z * conj (reflectedSmoothingY Q ε g z) ∂doubleMeasure Q) :=
  reflectedSmoothingGradient_adjoint Q hε transverseVelocity_stronglyMeasurable
    (fun c => (norm_transverseVelocity c.1 c.2).le)
    (fun i c => reflect_transverseVelocity Q i c.1 c.2) hfm hgm hf hg

lemma supportedSmoothing_yDerivative_eq_of_supported (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (hA : 2 * R + ε ≤ A)
    {f : DoublePhase → ℂ} (hf : SpatiallyZero Q A f) (hm : StronglyMeasurable f)
    {H : ℝ} (hH : ∀ z, ‖f z‖ ≤ H) {z : DoublePhase} (hz : z.1.1 ∈ Q.table) :
    yDerivative (supportedSmoothing Q ε R f) z = reflectedSmoothingY Q ε f z := by
  have he : (fun y => supportedSmoothing Q ε R f ((y,z.1.2),z.2)) =ᶠ[𝓝 z.1.1]
      (fun y => reflectedSmoothing Q ε f ((y,z.1.2),z.2)) := by
    filter_upwards [isOpen_interior.eventually_mem hz] with y hy
    exact supportedSmoothing_eq_of_supported Q hε hR hA hf hy
  change fderiv ℝ (fun y => supportedSmoothing Q ε R f ((y,z.1.2),z.2)) z.1.1 _ = _
  rw [he.fderiv_eq]
  exact congrArg (fun L : ℂ →L[ℝ] ℂ => L (transverseVelocity z.1.2 z.2))
    (reflectedSmoothing_hasFDerivAt Q hε hm (bounded_spatialSlice_integrable Q hm hH z.1.2 z.2)
      (fun i => bounded_spatialSlice_integrable Q hm hH (reflectedDirection Q i z.1.2) (z.2+1)) z.1.1).fderiv

lemma supportedSmoothing_transverse_generator (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor * ε < R)
    (hsmall : 2 * R * Q.coordinateBound < 1) (hA : 2 * R + ε ≤ A)
    {f : DoublePhase → ℂ} (hm : StronglyMeasurable f) {H : ℝ} (hH : ∀ z, ‖f z‖ ≤ H)
    (hf : MemLp f 2 (doubleMeasure Q)) (hs : SpatiallyZero Q A f) :
    (transverseHilbertFlow Q).HasGenerator
      ((supportedSmoothing_memLp Q hε R hm hH).toLp _)
      ((reflectedSmoothingY_memLp Q hε hm hf).toLp _) := by
  have hRp := (mul_pos Q.safetyFactor_pos hε).trans hR
  obtain ⟨C,hC⟩ := supportedSmoothing_fderiv_bound Q hε hRp hm hH
  have hd := fun v b => (supportedSmoothing_contDiff Q hε R hm hH v b).differentiable (by simp)
  have hy := yDerivative_memLp_of_gradient_bound Q
    (supportedSmoothing_stronglyMeasurable Q ε R hm).measurable hd hC
  have hgen := seam_transverse_generator (supportedSmoothing_seam Q hε hR hsmall f) hd hC
    (supportedSmoothing_memLp Q hε R hm hH) hy
  have he := hy.toLp_congr (reflectedSmoothingY_memLp Q hε hm hf) (by
    filter_upwards [ae_double_position_in_table Q] with z hz
    exact supportedSmoothing_yDerivative_eq_of_supported Q hε hRp hA hs hm hH hz)
  rwa [he] at hgen

lemma seam_mixed_generators {Q : Triangle} {f : DoublePhase → ℂ}
    (hs : SeamCompatible Q f) (hm : Measurable f)
    (hd : ∀ v b, ContDiff ℝ ∞ (fun x => f ((x,v),b)))
    {D : ℝ≥0}
    (hD : ∀ x v b, ‖fderiv ℝ (fderiv ℝ (fun y => f ((y,v),b))) x‖ ≤ D)
    (hx : MemLp (xDerivative f) 2 (doubleMeasure Q))
    (hy : MemLp (yDerivative f) 2 (doubleMeasure Q)) :
    ∃ c : DoubleL2 Q,
      (geodesicHilbertFlow Q).HasGenerator (hy.toLp _) c ∧
      (transverseHilbertFlow Q).HasGenerator (hx.toLp _) c := by
  have hd' := fun v b => (hd v b).differentiable (by simp)
  have hx' := fun v b => (xDerivative_contDiff hd v b).differentiable (by simp)
  have hy' := fun v b => (yDerivative_contDiff hd v b).differentiable (by simp)
  have hX := xDerivative_fderiv_bound hd hD
  have hY := yDerivative_fderiv_bound hd hD
  have hxy := xDerivative_memLp_of_gradient_bound Q (yDerivative_measurable hm hd') hy' hY
  have hyx := yDerivative_memLp_of_gradient_bound Q (xDerivative_measurable hm hd') hx' hX
  have he := hxy.toLp_congr hyx (Eventually.of_forall (x_y_commute hd))
  refine ⟨hxy.toLp _,seam_geodesic_generator (hs.yDerivative hd') hy' hY hy hxy,?_⟩
  rw [he]
  exact seam_transverse_generator (hs.xDerivative hd') hx' hX hx hyx

end TriangularBilliards

namespace TriangularBilliards
open Analysis SpatialSmoothing Filter
open scoped Topology ComplexConjugate NNReal ContDiff

/-- The segment pairing is obtained on the actual compactly supported
mollifier domain. No commutation on a rough tail is asserted. -/
lemma clearance_smoothing_pairing (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor * ε < R)
    (hsmall : 2 * R * Q.coordinateBound < 1) (hA : 2 * R + 2 * ε ≤ A)
    {f p : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hpm : StronglyMeasurable p)
    (hf : MemLp f 2 (doubleMeasure Q)) (hp : MemLp p 2 (doubleMeasure Q))
    (hfp : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) (hp.toLp p))
    {H J : ℝ} (hH : ∀ z, ‖f z‖ ≤ H) (hJ : ∀ z, ‖p z‖ ≤ J)
    (hfs : SpatiallyZero Q A f) (hps : SpatiallyZero Q A p)
    {U B : DoubleL2 Q} (hUB : (geodesicHilbertFlow Q).HasGenerator U B) :
    inner ℂ B ((reflectedSmoothingY_memLp Q hε hfm hf).toLp _) =
      inner ℂ ((reflectedSmoothingY_memLp Q hε (Lp.stronglyMeasurable U) (Lp.memLp U)).toLp _) (hp.toLp p) := by
  let w := supportedSmoothing Q ε R f
  have hRp := (mul_pos Q.safetyFactor_pos hε).trans hR
  have hA' : 2*R+ε ≤ A := by linarith
  have hd := supportedSmoothing_contDiff Q hε R hfm hH
  obtain ⟨C,hC⟩ := supportedSmoothing_fderiv_bound Q hε hRp hfm hH
  obtain ⟨D,hD⟩ := supportedSmoothing_second_bound Q hε hRp hfm hH
  have hm := (supportedSmoothing_stronglyMeasurable Q ε R hfm).measurable
  have hd' := fun v b => (hd v b).differentiable (by simp)
  have hx := xDerivative_memLp_of_gradient_bound Q hm hd' hC
  have hy := yDerivative_memLp_of_gradient_bound Q hm hd' hC
  have hw := supportedSmoothing_memLp Q hε R hfm hH
  have hpw := supportedSmoothing_memLp Q hε R hpm hJ
  have hs := supportedSmoothing_seam Q hε hR hsmall f
  have hxg := seam_geodesic_generator hs hd' hC hw hx
  have hyg := seam_transverse_generator hs hd' hC hw hy
  have hxg' := supportedSmoothing_generator_commutes Q hε hR hsmall hA
    hfm hpm hf hp hfp hH hJ hfs hps
  have hex := (geodesicHilbertFlow Q).generator_unique hxg hxg'
  have hyg' := supportedSmoothing_transverse_generator Q hε hR hsmall hA'
    hfm hH hf hfs
  have hey := (transverseHilbertFlow Q).generator_unique hyg hyg'
  obtain ⟨c,hcX,hcY⟩ := seam_mixed_generators hs hm hd hD hx hy
  rw [hex] at hcY
  have hpg := supportedSmoothing_transverse_generator Q hε hR hsmall hA'
    hpm hJ hp hps
  have hec := (transverseHilbertFlow Q).generator_unique hcY hpg
  rw [hey,hec] at hcX
  have hskew := (geodesicHilbertFlow Q).generator_skew hUB hcX
  have hadj := reflectedSmoothingY_adjoint Q hε hpm (Lp.stronglyMeasurable U) hp (Lp.memLp U)
  rw [integral_pairing_toLp (reflectedSmoothingY_memLp Q hε hpm hp) (Lp.memLp U),
    integral_pairing_toLp hp (reflectedSmoothingY_memLp Q hε (Lp.stronglyMeasurable U) (Lp.memLp U)),
    Lp.toLp_coeFn U (Lp.memLp U)] at hadj
  rw [hadj] at hskew
  exact eq_of_sub_eq_zero (by linear_combination hskew)

end TriangularBilliards

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
end

section
section
namespace OAI


open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Finset Set
open scoped Topology BigOperators
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Set
open scoped Topology
noncomputable section

namespace TriangularBilliards
open scoped NNReal

namespace FlightChain

lemma dist_point_succ {Q : Triangle} {z : Phase} (c : FlightChain Q z) (n : ℤ) :
    dist (c.point n) (c.point (n + 1)) = c.time (n + 1) - c.time n := by
  rw [dist_comm, dist_eq_norm, c.flight, add_sub_cancel_left,
    norm_smul, Circle.norm_coe, mul_one, Real.norm_eq_abs,
    abs_of_pos (sub_pos.mpr (c.increasing (by omega)))]

lemma dist_point_le {Q : Triangle} {z : Phase} (c : FlightChain Q z)
    {n m : ℤ} (hnm : n ≤ m) : dist (c.point n) (c.point m) ≤ c.time m - c.time n := by
  induction m, hnm using Int.leInduction with
  | base => simp only [dist_self, sub_self, le_refl]
  | succ m hnm ih =>
    calc
      dist (c.point n) (c.point (m + 1)) ≤
        dist (c.point n) (c.point m) + dist (c.point m) (c.point (m + 1)) := dist_triangle _ _ _
      _ ≤ c.time m - c.time n + (c.time (m + 1) - c.time m) :=
        add_le_add ih (c.dist_point_succ m).le
      _ = c.time (m + 1) - c.time n := by ring

lemma position_dist_le {Q : Triangle} {z : Phase} (c : FlightChain Q z) (s t : ℝ) :
    dist (c.at s).1 (c.at t).1 ≤ dist s t := by
  wlog hst : s ≤ t generalizing s t
  · rw [dist_comm, dist_comm s t]
    exact this t s (le_of_not_ge hst)
  obtain ⟨n, hn⟩ := c.exists_flight s
  obtain ⟨m, hm⟩ := c.exists_flight t
  have hnm : n ≤ m := by
    by_contra h
    have hh := c.increasing.monotone (show m + 1 ≤ n by omega)
    linarith [hn.1, hm.2]
  rcases hnm.eq_or_lt with he | hnm
  · subst m
    rw [c.unit_speed_on_flight hn hm]
    exact le_refl _
  · have hsn : dist (c.at s).1 (c.point (n + 1)) = c.time (n + 1) - s := by
      rw [c.at_of_flight hn, c.flight, dist_eq_norm, add_sub_add_left_eq_sub,
        ← sub_smul, norm_smul, Circle.norm_coe, mul_one, Real.norm_eq_abs]
      have hh : (s - c.time n) - (c.time (n + 1) - c.time n) = s - c.time (n + 1) := by ring
      rw [hh, abs_of_neg (sub_neg.mpr hn.2)]
      ring
    have hmt : dist (c.point m) (c.at t).1 = t - c.time m := by
      rw [c.at_of_flight hm, dist_comm, dist_eq_norm, add_sub_cancel_left,
        norm_smul, Circle.norm_coe, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hm.1)]
    calc
      dist (c.at s).1 (c.at t).1 ≤
        dist (c.at s).1 (c.point (n + 1)) + dist (c.point (n + 1)) (c.at t).1 :=
        dist_triangle _ _ _
      _ ≤ dist (c.at s).1 (c.point (n + 1)) +
        (dist (c.point (n + 1)) (c.point m) + dist (c.point m) (c.at t).1) := by
        gcongr
        exact dist_triangle _ _ _
      _ ≤ (c.time (n + 1) - s) +
        ((c.time m - c.time (n + 1)) + (t - c.time m)) := by
        rw [hsn, hmt]
        gcongr
        exact c.dist_point_le (by omega)
      _ = dist s t := by rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst)]; ring

end FlightChain

lemma billiard_position_lipschitz (Q : Triangle) (z : Phase) :
    LipschitzWith 1 (fun t => (billiardFlow Q t z).1) := by
  classical
  rw [lipschitzWith_iff_dist_le_mul]
  intro s t
  by_cases h : Nonempty (FlightChain Q z)
  · simpa only [billiardFlow, dite_eq_left h, NNReal.coe_one, one_mul] using
      (Classical.choice h).position_dist_le s t
  · simp only [billiardFlow, dite_eq_right h, dist_self, NNReal.coe_one, one_mul]
    exact dist_nonneg

namespace Triangle

lemma clearance_flow_lipschitz (Q : Triangle) (z : Phase) :
    LipschitzWith 1 (fun t => Q.clearance (billiardFlow Q t z).1) := by
  simpa only [mul_one, Function.comp_def] using Q.clearance_lipschitz.comp (billiard_position_lipschitz Q z)

end Triangle

end TriangularBilliards

namespace TriangularBilliards
open scoped Topology

/-- A finite measurable subset of the good set. Sampling one
extra endpoint keeps all sample times simple multiples of the mesh width. -/
def goodMesh (Q : Triangle) (L ε T : ℝ) : Set DoublePhase :=
  {z | ∀ k : Fin (Nat.ceil (T / ε) + 1),
    (L + 1) * ε < Q.clearance (doubleFlow Q ((k : ℕ) * ε) z).1.1}

lemma goodMesh_measurable (Q : Triangle) (L ε T : ℝ) :
    MeasurableSet (goodMesh Q L ε T) := by
  simp only [goodMesh, ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  exact measurableSet_lt measurable_const
    (Q.clearance_lipschitz.continuous.measurable.comp
      (measurable_doubleFlow_time Q _).fst.fst)

lemma goodMesh_clearance {Q : Triangle} {L ε T : ℝ} (hε : 0 < ε)
    {z : DoublePhase} (hz : z ∈ goodMesh Q L ε T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    L * ε < Q.clearance (doubleFlow Q t z).1.1 := by
  let k : Fin (Nat.ceil (T / ε) + 1) :=
    ⟨Nat.floor (t / ε), by
      have h := (Nat.floor_mono (div_le_div_of_nonneg_right ht.2 hε.le)).trans
        (Nat.floor_le_ceil (T / ε))
      omega⟩
  have hk0 : (k : ℕ) * ε ≤ t := by
    have h := Nat.floor_le (div_nonneg ht.1 hε.le)
    exact (le_div_iff₀ hε).mp h
  have hk1 : t - (k : ℕ) * ε < ε := by
    have h := (div_lt_iff₀ hε).mp (Nat.lt_floor_add_one (t / ε))
    dsimp [k]
    nlinarith
  have hd := (Q.clearance_flow_lipschitz z.1).dist_le_mul ((k : ℕ) * ε) t
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hd
  rw [abs_of_nonpos (sub_nonpos.mpr hk0)] at hd
  have hh := hz k
  change (L + 1) * ε < Q.clearance (billiardFlow Q ((k : ℕ) * ε) z.1).1 at hh
  change L * ε < Q.clearance (billiardFlow Q t z.1).1
  have he := le_abs_self (Q.clearance (billiardFlow Q ((k : ℕ) * ε) z.1).1 -
    Q.clearance (billiardFlow Q t z.1).1)
  nlinarith

lemma badMesh_measure_bound (Q : Triangle) (L ε T : ℝ) :
    doubleMeasure Q (goodMesh Q L ε T)ᶜ ≤
      (Nat.ceil (T / ε) + 1 : ℕ) * ((volume Q.table)⁻¹ *
        (3 * (ENNReal.ofReal ((L + 1) * ε)) ^ 2 * (NNReal.pi : ℝ≥0∞))) := by
  classical
  have he : (goodMesh Q L ε T)ᶜ =
      ⋃ k : Fin (Nat.ceil (T / ε) + 1),
        doubleFlow Q ((k : ℕ) * ε) ⁻¹' unsafeSet Q ((L + 1) * ε) := by
    ext z
    simp only [goodMesh, mem_compl_iff, mem_ofPred_eq, not_forall, not_lt,
      mem_iUnion, Set.mem_preimage, unsafeSet]
  rw [he]
  calc
    _ ≤ ∑' k : Fin (Nat.ceil (T / ε) + 1),
        doubleMeasure Q (doubleFlow Q ((k : ℕ) * ε) ⁻¹' unsafeSet Q ((L + 1) * ε)) :=
      measure_iUnion_le _
    _ = ∑' _k : Fin (Nat.ceil (T / ε) + 1),
        doubleMeasure Q (unsafeSet Q ((L + 1) * ε)) := by
      congr 1
      funext k
      exact (measurePreserving_doubleFlow Q _).measure_preimage
        (unsafeSet_measurable Q _).nullMeasurableSet
    _ ≤ ∑' _k : Fin (Nat.ceil (T / ε) + 1),
        ((volume Q.table)⁻¹ * (3 * (ENNReal.ofReal ((L + 1) * ε)) ^ 2 *
          (NNReal.pi : ℝ≥0∞))) :=
      ENNReal.tsum_le_tsum (fun _ => unsafeSet_measure_bound Q _)
    _ = _ := by simp only [tsum_fintype, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]

end TriangularBilliards
namespace TriangularBilliards.Analysis.HilbertFlow
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (W : HilbertFlow H)

lemma negativeAverage_mem_convex {C : Set H} (hc : Convex ℝ C) (hclosed : IsClosed C)
    {T : ℝ} (hT : 0 < T) {u : H} (hu : ∀ t ∈ Set.Icc (-T) 0, W.act t u ∈ C) :
    W.negativeAverage T u ∈ C := by
  have hm : ∀ᵐ t ∂volume.restrict (Set.Ioc (-T) 0), W.act t u ∈ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hu t ⟨ht.1.le,ht.2⟩
  have h := hc.set_average_mem hclosed
    (μ := volume) (t := Set.Ioc (-T) 0)
    (by simpa only [Real.volume_Ioc, sub_neg_eq_add, zero_add, ne_eq, ENNReal.ofReal_eq_zero, not_le] using hT)
    (by simp) hm (W.intervalIntegrable u (-T) 0).1
  rw [MeasureTheory.average_eq, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc,
    sub_neg_eq_add, zero_add, ENNReal.toReal_ofReal hT.le] at h
  change (T⁻¹ : ℝ) • W.timeIntegral (-T) 0 u ∈ C
  rwa [timeIntegral_apply, intervalIntegral.integral_of_le (by linarith : -T ≤ 0)]

end TriangularBilliards.Analysis.HilbertFlow

namespace TriangularBilliards.Analysis
open MeasureTheory Set Filter
variable {A : Type uA} [MeasurableSpace A] {μ : Measure A}

/-- Measurable functions with values almost everywhere in prescribed closed
convex fibers form a closed convex subset of the actual L² space. -/
lemma isClosed_ae_mem (C : A → Set ℂ) (hc : ∀ z, IsClosed (C z)) :
    IsClosed {u : Lp ℂ 2 μ | ∀ᵐ z ∂μ, u z ∈ C z} := by
  apply IsSeqClosed.isClosed
  intro u v hu hv
  obtain ⟨φ,_,hφ⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  filter_upwards [ae_all_iff.mpr hu, hφ] with z hz hlim
  exact (hc z).mem_of_tendsto hlim (Filter.Eventually.of_forall fun n => hz (φ n))

lemma convex_ae_mem (C : A → Set ℂ) (hc : ∀ z, Convex ℝ (C z)) :
    Convex ℝ {u : Lp ℂ 2 μ | ∀ᵐ z ∂μ, u z ∈ C z} := by
  intro u hu v hv a b ha hb hab
  filter_upwards [hu,hv,Lp.coeFn_smul a u,Lp.coeFn_smul b v,
    Lp.coeFn_add (a • u) (b • v)] with z h1 h2 h3 h4 h5
  simp only [Pi.add_apply, Pi.smul_apply] at h3 h4 h5
  rw [h5,h3,h4]
  exact hc z h1 h2 ha hb hab

lemma isClosed_ae_bounded (H : ℝ) :
    IsClosed {u : Lp ℂ 2 μ | ∀ᵐ z ∂μ, ‖u z‖ ≤ H} := by
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    isClosed_ae_mem (μ := μ) (fun _ => Metric.closedBall (0 : ℂ) H) (fun _ => Metric.isClosed_closedBall)

lemma convex_ae_bounded (H : ℝ) :
    Convex ℝ {u : Lp ℂ 2 μ | ∀ᵐ z ∂μ, ‖u z‖ ≤ H} := by
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    convex_ae_mem (μ := μ) (fun _ => Metric.closedBall (0 : ℂ) H) (fun _ => convex_closedBall _ _)

lemma isClosed_ae_zero_on (E : Set A) :
    IsClosed {u : Lp ℂ 2 μ | ∀ᵐ z ∂μ, z ∈ E → u z = 0} := by
  classical
  convert isClosed_ae_mem (μ := μ) (fun z => if z ∈ E then {0} else Set.univ)
    (fun z => by split <;> simp) using 1
  ext u
  simp only [mem_ofPred_eq]
  apply eventually_congr
  filter_upwards with z
  by_cases hz : z ∈ E <;> simp [hz]

lemma convex_ae_zero_on (E : Set A) :
    Convex ℝ {u : Lp ℂ 2 μ | ∀ᵐ z ∂μ, z ∈ E → u z = 0} := by
  classical
  convert convex_ae_mem (μ := μ) (fun z => if z ∈ E then {0} else Set.univ)
    (fun z => by split; exact convex_singleton 0; exact convex_univ) using 1
  ext u
  simp only [mem_ofPred_eq]
  apply eventually_congr
  filter_upwards with z
  by_cases hz : z ∈ E <;> simp [hz]

end TriangularBilliards.Analysis

namespace TriangularBilliards.Analysis
open MeasureTheory Filter Set
variable {A : Type uA} [MeasurableSpace A] {μ : Measure A}

lemma restrictL2_ae_bounded {E : Set A} (hE : MeasurableSet E)
    {u : Lp ℂ 2 μ} {H : ℝ} (hH : 0 ≤ H) (hu : ∀ᵐ z ∂μ, ‖u z‖ ≤ H) :
    ∀ᵐ z ∂μ, ‖restrictL2 E hE u z‖ ≤ H := by
  filter_upwards [hu,restrictL2_coe E hE u] with z hz he
  rw [he]
  by_cases h : z ∈ E
  · simpa only [indicator_of_mem h] using hz
  · simpa only [indicator_of_notMem h, norm_zero] using hH

lemma restrictL2_sub_self (E : Set A) (hE : MeasurableSet E) (u : Lp ℂ 2 μ) :
    restrictL2 E hE u - u = -restrictL2 Eᶜ hE.compl u := by
  apply Lp.ext
  filter_upwards [restrictL2_coe E hE u,restrictL2_coe Eᶜ hE.compl u,
    Lp.coeFn_sub (restrictL2 E hE u) u,Lp.coeFn_neg (restrictL2 Eᶜ hE.compl u)] with z h1 h2 h3 h4
  simp only [Pi.sub_apply,Pi.neg_apply] at h3 h4
  rw [h3,h4,h1,h2]
  by_cases hz : z ∈ E <;> simp [hz]
end TriangularBilliards.Analysis

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
end

section
section
namespace OAI

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Finset Set
open scoped Topology BigOperators
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Set
open scoped Topology
noncomputable section

namespace TriangularBilliards
open Analysis Filter

def clearanceAverage (Q : Triangle) (L ε T : ℝ) (u : DoubleL2 Q) : DoubleL2 Q :=
  (geodesicHilbertFlow Q).negativeAverage T
    (restrictL2 (goodMesh Q L ε T) (goodMesh_measurable Q L ε T) u)

lemma clearanceAverage_bounded (Q : Triangle) {L ε T H : ℝ} (hT : 0 < T)
    (hH : 0 ≤ H) {u : DoubleL2 Q} (hu : ∀ᵐ z ∂doubleMeasure Q, ‖u z‖ ≤ H) :
    ∀ᵐ z ∂doubleMeasure Q, ‖clearanceAverage Q L ε T u z‖ ≤ H := by
  apply (geodesicHilbertFlow Q).negativeAverage_mem_convex
    (convex_ae_bounded H) (isClosed_ae_bounded H) hT
  intro t _
  have hb := (measurePreserving_doubleFlow Q t).quasiMeasurePreserving.ae
    (restrictL2_ae_bounded (goodMesh_measurable Q L ε T) hH hu)
  filter_upwards [hb,geodesic_koopman_ae Q t
    (restrictL2 (goodMesh Q L ε T) (goodMesh_measurable Q L ε T) u)] with z hz he
  simpa only [he] using hz

lemma clearanceAverage_zero (Q : Triangle) {L ε T : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (u : DoubleL2 Q) :
    ∀ᵐ z ∂doubleMeasure Q, z ∈ unsafeSet Q (L * ε) → clearanceAverage Q L ε T u z = 0 := by
  apply (geodesicHilbertFlow Q).negativeAverage_mem_convex
    (convex_ae_zero_on _) (isClosed_ae_zero_on _) hT
  intro t ht
  have hc := doubleFlow_cocycle Q (-t) t
  have he := (measurePreserving_doubleFlow Q t).quasiMeasurePreserving.ae
    (restrictL2_coe (goodMesh Q L ε T) (goodMesh_measurable Q L ε T) u)
  filter_upwards [hc,he,geodesic_koopman_ae Q t
    (restrictL2 (goodMesh Q L ε T) (goodMesh_measurable Q L ε T) u)] with z hc he hz
  intro hunsafe
  rw [hz,he]
  apply indicator_of_notMem
  intro hgood
  have hsafe := goodMesh_clearance hε hgood (t := -t) (by constructor <;> linarith [ht.1,ht.2])
  simp only [neg_add_cancel, doubleFlow_zero,Function.comp_apply] at hc
  rw [← hc] at hsafe
  exact (not_lt_of_ge hunsafe) hsafe

lemma clearanceAverage_estimates (Q : Triangle) {L ε T H : ℝ} (hT : 0 < T)
    (hH : 0 ≤ H) {u : DoubleL2 Q} (hu : ∀ᵐ z ∂doubleMeasure Q, ‖u z‖ ≤ H)
    (hinv : ∀ t, (geodesicHilbertFlow Q).act t u = u) :
    ‖clearanceAverage Q L ε T u - u‖ ≤
      H * (doubleMeasure Q (goodMesh Q L ε T)ᶜ).toReal ^ (1/2 : ℝ) ∧
    ∃ a : DoubleL2 Q, (geodesicHilbertFlow Q).HasGenerator (clearanceAverage Q L ε T u) a ∧
      ‖a‖ ≤ 2 * ‖u‖ / T := by
  let v := restrictL2 (goodMesh Q L ε T) (goodMesh_measurable Q L ε T) u
  constructor
  · apply ((geodesicHilbertFlow Q).negativeAverage_dist_invariant hinv hT v).trans
    rw [show v = restrictL2 (goodMesh Q L ε T) (goodMesh_measurable Q L ε T) u from rfl,
      restrictL2_sub_self,norm_neg]
    exact restrictL2_norm_of_bounded _ (goodMesh_measurable Q L ε T).compl (measure_ne_top _ _) hH hu
  · refine ⟨(T⁻¹ : ℝ) • (v - (geodesicHilbertFlow Q).act (-T) v),
      (geodesicHilbertFlow Q).negativeAverage_generator T v, ?_⟩
    apply ((geodesicHilbertFlow Q).negativeAverage_generator_norm hT v).trans
    gcongr
    exact restrictL2_norm _ _ _

end TriangularBilliards
namespace TriangularBilliards
open Analysis Filter Set
open scoped Topology

lemma restricted_clearance_zero_time (Q : Triangle) {L ε T t : ℝ} (hε : 0 < ε)
    (ht : t ∈ Icc (-T) 0) (u : DoubleL2 Q) :
    ∀ᵐ z ∂doubleMeasure Q, z ∈ unsafeSet Q (L * ε) →
      (geodesicHilbertFlow Q).act t
        (restrictL2 (goodMesh Q L ε T) (goodMesh_measurable Q L ε T) u) z = 0 := by
  have hc := doubleFlow_cocycle Q (-t) t
  have he := (measurePreserving_doubleFlow Q t).quasiMeasurePreserving.ae
    (restrictL2_coe (goodMesh Q L ε T) (goodMesh_measurable Q L ε T) u)
  filter_upwards [hc,he,geodesic_koopman_ae Q t
    (restrictL2 (goodMesh Q L ε T) (goodMesh_measurable Q L ε T) u)] with z hc he hz
  intro hunsafe
  rw [hz,he]
  apply indicator_of_notMem
  intro hgood
  have hsafe := goodMesh_clearance hε hgood (t := -t) (by constructor <;> linarith [ht.1,ht.2])
  simp only [neg_add_cancel, doubleFlow_zero,Function.comp_apply] at hc
  rw [← hc] at hsafe
  exact (not_lt_of_ge hunsafe) hsafe

lemma clearanceAverage_generator_supported (Q : Triangle) {L ε T H : ℝ}
    (hε : 0 < ε) (hT : 0 < T) (hH : 0 ≤ H) {u : DoubleL2 Q}
    (hu : ∀ᵐ z ∂doubleMeasure Q, ‖u z‖ ≤ H) :
    ∃ p : DoubleL2 Q,
      (geodesicHilbertFlow Q).HasGenerator (clearanceAverage Q L ε T u) p ∧
      (∀ᵐ z ∂doubleMeasure Q, ‖p z‖ ≤ 2*H/T) ∧
      (∀ᵐ z ∂doubleMeasure Q, z ∈ unsafeSet Q (L*ε) → p z = 0) := by
  let v := restrictL2 (goodMesh Q L ε T) (goodMesh_measurable Q L ε T) u
  let w := (geodesicHilbertFlow Q).act (-T) v
  let p := (T⁻¹ : ℝ) • (v-w)
  refine ⟨p,(geodesicHilbertFlow Q).negativeAverage_generator T v,?_,?_⟩
  · have hv := restrictL2_ae_bounded (goodMesh_measurable Q L ε T) hH hu
    have hw := (measurePreserving_doubleFlow Q (-T)).quasiMeasurePreserving.ae hv
    filter_upwards [hv,hw,geodesic_koopman_ae Q (-T) v,
      Lp.coeFn_sub v w,Lp.coeFn_smul (T⁻¹ : ℝ) (v-w)] with z hv hw hc hd he
    change ‖p z‖ ≤ _
    change ((T⁻¹ : ℝ) • (v-w)) z = _ at he
    rw [he, Pi.smul_apply,hd,Pi.sub_apply,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hT)]
    calc
      _ ≤ T⁻¹ * (‖v z‖+‖w z‖) := mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr hT.le)
      _ ≤ T⁻¹ * (H+H) := by gcongr; simpa only [w,hc] using hw
      _ = _ := by ring
  · have hv := restricted_clearance_zero_time Q (L := L) (T := T) hε (t := 0) (by constructor <;> linarith) u
    have hw := restricted_clearance_zero_time Q (L := L) (T := T) hε (t := -T) (by constructor <;> linarith) u
    simp only [(geodesicHilbertFlow Q).zero] at hv
    filter_upwards [hv,hw,Lp.coeFn_sub v w,Lp.coeFn_smul (T⁻¹ : ℝ) (v-w)] with z hv hw hd he
    intro hz
    change ((T⁻¹ : ℝ) • (v-w)) z = 0
    rw [he,Pi.smul_apply,hd,Pi.sub_apply,hv hz,hw hz,sub_self,smul_zero]

/-- Choose a genuinely measurable everywhere bounded, spatially supported
representative; no pointwise assertion about an arbitrary Lp representative
is used. -/
lemma exists_bounded_supported_representative (Q : Triangle) {u : DoubleL2 Q} {H A : ℝ}
    (hH : 0 ≤ H) (hu : ∀ᵐ z ∂doubleMeasure Q, ‖u z‖ ≤ H)
    (hs : ∀ᵐ z ∂doubleMeasure Q, z ∈ unsafeSet Q A → u z = 0) :
    ∃ f : DoublePhase → ℂ, StronglyMeasurable f ∧
      (∀ z, ‖f z‖ ≤ H) ∧ SpatiallyZero Q A f ∧ f =ᵐ[doubleMeasure Q] u := by
  classical
  let E := {z : DoublePhase | ‖u z‖ ≤ H ∧ A < Q.clearance z.1.1}
  have hE : MeasurableSet E :=
    (measurableSet_le (Lp.stronglyMeasurable u).measurable.norm measurable_const).inter
      (measurableSet_lt measurable_const (Q.clearance_lipschitz.continuous.measurable.comp measurable_fst.fst))
  refine ⟨E.indicator u,(Lp.stronglyMeasurable u).indicator hE,?_,?_,?_⟩
  · intro z
    by_cases hz : z ∈ E
    · simpa only [indicator_of_mem hz] using hz.1
    · simpa only [indicator_of_notMem hz,norm_zero] using hH
  · intro y _ hy v b
    exact indicator_of_notMem (by intro h; exact (not_lt_of_ge hy.le) h.2) _
  · filter_upwards [hu,hs] with z hz hzs
    by_cases hc : A < Q.clearance z.1.1
    · exact indicator_of_mem (show z ∈ E from ⟨hz,hc⟩) _
    · rw [indicator_of_notMem (by intro h; exact hc h.2)]
      exact (hzs (le_of_not_gt hc)).symm

end TriangularBilliards

namespace TriangularBilliards
open Analysis SpatialSmoothing Filter Set
open scoped Topology

lemma doubleL2_norm_le_of_ae_bound (Q : Triangle) {u : DoubleL2 Q} {H : ℝ}
    (hH : 0 ≤ H) (hu : ∀ᵐ z ∂doubleMeasure Q, ‖u z‖ ≤ H) : ‖u‖ ≤ H := by
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hH hu

lemma reflectedSmoothingY_norm_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} {H : ℝ} (hH : 0 ≤ H) (hf : ∀ z, ‖f z‖ ≤ H) (z : DoublePhase) :
    ‖reflectedSmoothingY Q ε f z‖ ≤ 4*derivativeMass*H/ε := by
  exact (ContinuousLinearMap.le_opNorm _ _).trans (by
    rw [norm_transverseVelocity,mul_one]
    exact reflectedSmoothingGradient_norm_bound Q hε hH hf z)

lemma scaled_smoothingY_norm_tendsto (Q : Triangle) (u : DoubleL2 Q)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (he : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ε n * ‖(reflectedSmoothingY_memLp Q (hε n)
      (Lp.stronglyMeasurable u) (Lp.memLp u)).toLp _‖) atTop (𝓝 0) := by
  have he' : Tendsto ε atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨he,Eventually.of_forall hε⟩
  have hlim := (scaled_gradient_lpNorm_tendsto Q (Lp.stronglyMeasurable u) (Lp.memLp u)).comp he'
  apply squeeze_zero (fun n => mul_nonneg (hε n).le (norm_nonneg _)) _ hlim
  intro n
  have hg := (reflectedSmoothingGradient_memLp Q (hε n) (Lp.stronglyMeasurable u) (Lp.memLp u)).const_smul (ε n)
  have hy := (reflectedSmoothingY_memLp Q (hε n) (Lp.stronglyMeasurable u) (Lp.memLp u)).const_smul (ε n)
  have hmono : eLpNorm (ε n • reflectedSmoothingY Q (ε n) u) 2 (doubleMeasure Q) ≤
      eLpNorm (ε n • reflectedSmoothingGradient Q (ε n) u) 2 (doubleMeasure Q) := by
    apply eLpNorm_mono_ae
    filter_upwards [] with z
    simp only [Pi.smul_apply,norm_smul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (ContinuousLinearMap.le_opNorm _ _).trans_eq (by rw [norm_transverseVelocity,mul_one])
  have hb := ENNReal.toReal_mono hg.eLpNorm_ne_top hmono
  rw [toReal_eLpNorm hy.aestronglyMeasurable, toReal_eLpNorm hg.aestronglyMeasurable, lpNorm_const_smul] at hb
  rw [Lp.norm_toLp, toReal_eLpNorm (reflectedSmoothingY_memLp Q (hε n) (Lp.stronglyMeasurable u) (Lp.memLp u)).aestronglyMeasurable]
  simpa only [coe_nnnorm,Real.norm_eq_abs,abs_of_pos (hε n),Function.comp_def] using hb

lemma badMesh_real_bound (Q : Triangle) {L ε T : ℝ}
    (hL : 0 ≤ L+1) (hε : 0 < ε) (hT : 0 ≤ T) :
    (doubleMeasure Q (goodMesh Q L ε T)ᶜ).toReal ≤
      ((volume Q.table).toReal)⁻¹ * (3*(L+1)^2*Real.pi) * (T*ε+2*ε^2) := by
  have hfin : (Nat.ceil (T/ε)+1 : ℕ) * ((volume Q.table)⁻¹ *
      (3*(ENNReal.ofReal ((L+1)*ε))^2 * (NNReal.pi : ℝ≥0∞))) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.mpr Q.area_pos.ne') (by finiteness))
  have hb := ENNReal.toReal_mono hfin (badMesh_measure_bound Q L ε T)
  simp [ENNReal.toReal_mul,ENNReal.toReal_inv,
    ENNReal.toReal_pow,ENNReal.toReal_ofNat,ENNReal.toReal_ofReal (mul_nonneg hL hε.le),
    ENNReal.coe_toReal,NNReal.coe_real_pi,Nat.cast_add,Nat.cast_one] at hb
  have hceil : (Nat.ceil (T/ε) : ℝ)+1 ≤ T/ε+2 := by
    linarith [Nat.ceil_lt_add_one (div_nonneg hT hε.le)]
  apply hb.trans
  calc
    _ ≤ (T/ε+2) * (((volume Q.table).toReal)⁻¹ * (3*((L+1)*ε)^2*Real.pi)) := by
      gcongr
      rw [ENNReal.toReal_add (by simp) (by simp),ENNReal.toReal_natCast,ENNReal.toReal_one]
      exact hceil
    _ = _ := by field_simp

end TriangularBilliards

namespace TriangularBilliards
open Analysis SpatialSmoothing Filter Set
open scoped Topology ContDiff ComplexConjugate
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Quantitative global energy for a supported mollifier with a nonzero
transport source. All graphs are the actual specular generators. -/
lemma supported_source_CR (Q : Triangle) {ε R A T H : ℝ}
    (hε : 0 < ε) (hT : 0 < T) (hH : 0 ≤ H)
    (hR : Q.safetyFactor*ε < R) (hsmall : 2*R*Q.coordinateBound < 1)
    (hA : 2*R+2*ε ≤ A)
    {f p : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hpm : StronglyMeasurable p)
    (hf : MemLp f 2 (doubleMeasure Q)) (hp : MemLp p 2 (doubleMeasure Q))
    (hfp : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) (hp.toLp p))
    (hfb : ∀ z, ‖f z‖ ≤ H) (hpb : ∀ z, ‖p z‖ ≤ 2*H/T)
    (hfs : SpatiallyZero Q A f) (hps : SpatiallyZero Q A p) (j : ℤ)
    {U B : DoubleL2 Q} (hUB : (geodesicHilbertFlow Q).HasGenerator U B)
    (hB : (angularCircleAction Q).projection (j-1) B = B) :
    let hw := supportedSmoothing_memLp Q hε R hfm hfb
    ∃ a b : DoubleL2 Q,
      RotationalCR (geodesicHilbertFlow Q) (transverseHilbertFlow Q) (angularCircleAction Q)
        ((angularCircleAction Q).projection j (hw.toLp _)) a b ∧
      ‖a‖^2 ≤ 32*derivativeMass*H^2/(T*ε) ∧
      ‖b‖^2 ≤ 32*derivativeMass*H^2/(T*ε) ∧
      ‖inner ℂ B b‖ ≤ 4*‖B‖*H/T + H/T *
        ‖(reflectedSmoothingY_memLp Q hε (Lp.stronglyMeasurable U) (Lp.memLp U)).toLp _‖ := by
  dsimp only
  have hDnonneg := derivativeMass_nonneg
  have hRp : 0 < R := (mul_pos Q.safetyFactor_pos hε).trans hR
  have hA' : 2*R+ε ≤ A := by linarith
  let w := supportedSmoothing Q ε R f
  have hd := supportedSmoothing_contDiff Q hε R hfm hfb
  obtain ⟨C,hC⟩ := supportedSmoothing_fderiv_bound Q hε hRp hfm hfb
  obtain ⟨D,hD⟩ := supportedSmoothing_second_bound Q hε hRp hfm hfb
  have hm := (supportedSmoothing_stronglyMeasurable Q ε R hfm).measurable
  have hd' := fun v b => (hd v b).differentiable (by simp)
  let hx := xDerivative_memLp_of_gradient_bound Q hm hd' hC
  let hy := yDerivative_memLp_of_gradient_bound Q hm hd' hC
  let hw := supportedSmoothing_memLp Q hε R hfm hfb
  have hs := supportedSmoothing_seam Q hε hR hsmall f
  let a := (1/2 : ℂ) • (hx.toLp _ - Complex.I • hy.toLp _)
  let b := (1/2 : ℂ) • (hx.toLp _ + Complex.I • hy.toLp _)
  have hab : a+b = hx.toLp _ := by dsimp [a,b]; module
  have hdab : a-b = (-Complex.I) • hy.toLp _ := by dsimp [a,b]; module
  have hcr := seam_rotationalCR hs hd' hC hw hx hy
  have hn (k : ℤ) : ‖(angularCircleAction Q).projection (k+2) a‖ =
      ‖(angularCircleAction Q).projection k b‖ := by
    have hh := seam_projected_CR_norms_of_bounded_jets hs hm hd hC hD hw (k+1)
    simpa only [show k+1+1=k+2 by omega,add_sub_cancel_right] using hh
  have henergy := (angularCircleAction Q).localized_CR_energy a b j
    (ContinuousLinearMap.id ℂ _) (fun _ _ => rfl) (fun _ _ => rfl) rfl hn
  change ‖(angularCircleAction Q).projection (j+1) a‖^2 ≤ ‖a+b‖ * ‖a-b‖ at henergy
  rw [hab,hdab,norm_smul,norm_neg,Complex.norm_I,one_mul] at henergy
  have hxg := seam_geodesic_generator hs hd' hC hw hx
  have hxg' := supportedSmoothing_generator_commutes Q hε hR hsmall hA
    hfm hpm hf hp hfp hfb hpb hfs hps
  have hex := (geodesicHilbertFlow Q).generator_unique hxg hxg'
  have hyg := seam_transverse_generator hs hd' hC hw hy
  have hyg' := supportedSmoothing_transverse_generator Q hε hR hsmall hA' hfm hfb hf hfs
  have hey := (transverseHilbertFlow Q).generator_unique hyg hyg'
  have hxn : ‖hx.toLp _‖ ≤ 8*H/T := by
    rw [hex]
    apply (doubleL2_norm_le_of_ae_bound Q (H := 4*(2*H/T)) (by positivity) _).trans_eq (by ring)
    filter_upwards [(supportedSmoothing_memLp Q hε R hpm hpb).coeFn_toLp] with z hz
    rw [hz]
    exact supportedSmoothing_norm_bound Q hε R (by positivity) hpb z
  have hyn : ‖hy.toLp _‖ ≤ 4*derivativeMass*H/ε := by
    rw [hey]
    apply doubleL2_norm_le_of_ae_bound Q (by positivity)
    filter_upwards [(reflectedSmoothingY_memLp Q hε hfm hf).coeFn_toLp] with z hz
    rw [hz]
    exact reflectedSmoothingY_norm_bound Q hε hH hfb z
  have hbound : ‖(angularCircleAction Q).projection (j+1) a‖^2 ≤
      32*derivativeMass*H^2/(T*ε) := by
    apply henergy.trans
    calc
      _ ≤ (8*H/T)*(4*derivativeMass*H/ε) := mul_le_mul hxn hyn (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have heq := hn (j-1)
  rw [show j-1+2=j+1 by omega] at heq
  refine ⟨_,_,hcr.projection_covariant j,hbound,heq ▸ hbound,?_⟩
  have hyinner := clearance_smoothing_pairing Q hε hR hsmall hA hfm hpm hf hp hfp hfb hpb hfs hps hUB
  have hpbound : ‖hp.toLp p‖ ≤ 2*H/T := by
    apply doubleL2_norm_le_of_ae_bound Q (by positivity)
    filter_upwards [hp.coeFn_toLp] with z hz
    rw [hz]; exact hpb z
  have hyb : ‖inner ℂ B (hy.toLp _)‖ ≤
      ‖(reflectedSmoothingY_memLp Q hε (Lp.stronglyMeasurable U) (Lp.memLp U)).toLp _‖ * (2*H/T) := by
    rw [hey,hyinner]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hpbound (norm_nonneg _))
  rw [← (angularCircleAction Q).projection_adjoint, hB]
  change ‖inner ℂ B ((1/2 : ℂ) • (hx.toLp _ + Complex.I • hy.toLp _))‖ ≤ _
  rw [inner_smul_right,inner_add_right,inner_smul_right,norm_mul]
  have hc : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
  rw [hc]
  calc
    _ ≤ (1/2 : ℝ) * (‖inner ℂ B (hx.toLp _)‖ + ‖Complex.I * inner ℂ B (hy.toLp _)‖) := by gcongr; exact norm_add_le _ _
    _ ≤ (1/2 : ℝ) * (‖B‖*(8*H/T) +
        ‖(reflectedSmoothingY_memLp Q hε (Lp.stronglyMeasurable U) (Lp.memLp U)).toLp _‖ * (2*H/T)) := by
      rw [norm_mul,Complex.norm_I,one_mul]
      gcongr
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hxn (norm_nonneg _))
    _ = _ := by ring

end TriangularBilliards

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
end

section
section
namespace OAI


open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Finset Set
open scoped Topology BigOperators
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Set
open scoped Topology
noncomputable section

namespace TriangularBilliards
open Analysis Analytic SpatialSmoothing MeasureTheory Filter Set
open scoped Topology ContDiff NNReal BoundedContinuousFunction ComplexConjugate
lemma smoothing_lpNorm_tendsto_bounded (Q : Triangle)
    (f : DoublePhase →ᵇ ℂ) :
    Tendsto (fun ε : ℝ => lpNorm (reflectedSmoothing Q ε f - (f : DoublePhase → ℂ)) 2 (doubleMeasure Q))
      (𝓝[>] 0) (𝓝 0) := by
  have hi : Tendsto (fun ε : ℝ => ∫ z,
      ‖reflectedSmoothing Q ε f z - f z‖^2 ∂doubleMeasure Q)
      (𝓝[>] 0) (𝓝 (∫ _ : DoublePhase, (0 : ℝ) ∂doubleMeasure Q)) := by
    apply tendsto_integral_filter_of_norm_le_const
    · exact Eventually.of_forall fun ε =>
        (((reflectedSmoothing_stronglyMeasurable Q ε f.continuous.stronglyMeasurable).sub
          f.continuous.stronglyMeasurable).measurable.norm.pow_const 2).aestronglyMeasurable
    · refine ⟨(5*‖f‖)^2, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        apply pow_le_pow_left₀ (norm_nonneg _)
        exact (norm_sub_le _ _).trans (by
          have h := reflectedSmoothing_norm_bound Q hε (norm_nonneg f) f.norm_coe_le_norm z
          linarith [f.norm_coe_le_norm z])
    · filter_upwards [ae_double_position_in_table Q] with z hz
      simpa only [sub_self, norm_zero, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, zero_pow] using
        (((smoothing_pointwise Q f z hz).sub (tendsto_const_nhds (x := f z))).norm.pow 2)
  simp only [integral_zero] at hi
  have he (ε : ℝ) : lpNorm (reflectedSmoothing Q ε f - (f : DoublePhase → ℂ)) 2 (doubleMeasure Q) =
      Real.sqrt (∫ z, ‖reflectedSmoothing Q ε f z - f z‖^2 ∂doubleMeasure Q) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      ((reflectedSmoothing_stronglyMeasurable Q ε f.continuous.stronglyMeasurable).sub
        f.continuous.stronglyMeasurable).aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat, Pi.sub_apply, Real.rpow_two, Real.sqrt_eq_rpow]
    norm_num
  simp_rw [he]
  simpa only [Real.sqrt_zero, Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hi

lemma smoothing_lpNorm_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hf : StronglyMeasurable f) (hf₂ : MemLp f 2 (doubleMeasure Q)) :
    lpNorm (reflectedSmoothing Q ε f) 2 (doubleMeasure Q) ≤ 4 * lpNorm f 2 (doubleMeasure Q) := by
  rw [← toReal_eLpNorm (reflectedSmoothing_stronglyMeasurable Q ε hf).aestronglyMeasurable,
    ← toReal_eLpNorm hf.aestronglyMeasurable]
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hf₂.eLpNorm_ne_top)
      (reflectedSmoothing_eLpNorm Q hε hf)

lemma smoothing_lpNorm_tendsto (Q : Triangle)
    {f : DoublePhase → ℂ} (hf : StronglyMeasurable f) (hf₂ : MemLp f 2 (doubleMeasure Q)) :
    Tendsto (fun ε : ℝ => lpNorm (reflectedSmoothing Q ε f - (f : DoublePhase → ℂ)) 2 (doubleMeasure Q))
      (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  let η : ℝ := δ/12
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨g,hg,hg₂⟩ := hf₂.exists_boundedContinuous_eLpNorm_sub_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (ENNReal.ofReal_ne_zero_iff.mpr hη)
  have hsmall : lpNorm (f - (g : DoublePhase → ℂ)) 2 (doubleMeasure Q) ≤ η := by
    rw [← toReal_eLpNorm (hf.aestronglyMeasurable.sub g.continuous.aestronglyMeasurable)]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hg).trans_eq (ENNReal.toReal_ofReal hη.le)
  have hgsmall := (Metric.tendsto_nhds.mp (smoothing_lpNorm_tendsto_bounded Q g))
    (δ/2) (by positivity)
  filter_upwards [self_mem_nhdsWithin, hgsmall] with ε hε he
  let Sf := reflectedSmoothing Q ε f
  let Sg := reflectedSmoothing Q ε g
  have hfm := reflectedSmoothing_memLp Q hε hf hf₂
  have hgm := reflectedSmoothing_memLp Q hε g.continuous.stronglyMeasurable hg₂
  have hdm := reflectedSmoothing_memLp Q hε
    (hf.sub g.continuous.stronglyMeasurable) (hf₂.sub hg₂)
  have hae : Sf - Sg =ᵐ[doubleMeasure Q] reflectedSmoothing Q ε (f-(g : DoublePhase → ℂ)) :=
    (smoothing_sub_ae Q hε (hf₂.integrable (by norm_num))
      (hg₂.integrable (by norm_num))).symm
  have hb : lpNorm (Sf-Sg) 2 (doubleMeasure Q) ≤ 4*η := by
    rw [lpNorm_congr_ae_of_strong (hfm.sub hgm).aestronglyMeasurable
      hdm.aestronglyMeasurable hae]
    exact (smoothing_lpNorm_bound Q hε
      (hf.sub g.continuous.stronglyMeasurable) (hf₂.sub hg₂)).trans (by gcongr)
  have hn : lpNorm (Sf-f) 2 (doubleMeasure Q) ≤
      lpNorm (Sf-Sg) 2 (doubleMeasure Q) + lpNorm (Sg-(g : DoublePhase → ℂ)) 2 (doubleMeasure Q) +
        lpNorm (f-(g : DoublePhase → ℂ)) 2 (doubleMeasure Q) := by
    have heq : Sf-f = ((Sf-Sg)+(Sg-(g : DoublePhase → ℂ)))-(f-(g : DoublePhase → ℂ)) := by ext z; simp only [Pi.sub_apply, Pi.add_apply]; abel
    rw [heq]
    apply (lpNorm_sub_le ((hfm.sub hgm).add (hgm.sub hg₂)) (by norm_num)).trans
    exact add_le_add (lpNorm_add_le (hfm.sub hgm) (by norm_num)) le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg lpNorm_nonneg] at he ⊢
  change lpNorm (Sf - f) 2 (doubleMeasure Q) < δ
  change lpNorm (Sg - (g : DoublePhase → ℂ)) 2 (doubleMeasure Q) < δ/2 at he
  dsimp [η] at hsmall hb
  linarith

end TriangularBilliards

namespace TriangularBilliards.Analytic
open Filter
open scoped Topology
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma WeaklyTendsto.inner_right {u : ℕ → E} {v : E}
    (h : WeaklyTendsto u atTop v) (w : E) :
    Tendsto (fun n => inner ℂ w (u n)) atTop (𝓝 (inner ℂ w v)) := by
  have hr := h (Complex.reCLM.comp ((innerSL ℂ w).restrictScalars ℝ))
  have hi := h (Complex.imCLM.comp ((innerSL ℂ w).restrictScalars ℝ))
  have hh := (Complex.continuous_ofReal.tendsto _ |>.comp hr).add
    ((Complex.continuous_ofReal.tendsto _ |>.comp hi).mul_const Complex.I)
  change Tendsto (fun n => ((inner ℂ w (u n)).re : ℂ) + ((inner ℂ w (u n)).im : ℂ)*Complex.I)
    atTop (𝓝 (((inner ℂ w v).re : ℂ) + ((inner ℂ w v).im : ℂ)*Complex.I)) at hh
  simpa only [Complex.re_add_im] using hh

end TriangularBilliards.Analytic

namespace TriangularBilliards
open Analysis Analytic Filter
open scoped Topology ComplexConjugate

noncomputable def smoothingLp (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    (u : DoubleL2 Q) : DoubleL2 Q :=
  (reflectedSmoothing_memLp Q hε (Lp.stronglyMeasurable u) (Lp.memLp u)).toLp _

lemma smoothingLp_adjoint (Q : Triangle) {ε : ℝ} (hε : 0 < ε) (u v : DoubleL2 Q) :
    inner ℂ u (smoothingLp Q hε v) = inner ℂ (smoothingLp Q hε u) v := by
  have h := reflectedSmoothing_adjoint Q hε (Lp.stronglyMeasurable v)
    (Lp.stronglyMeasurable u) (Lp.memLp v) (Lp.memLp u)
  rw [integral_pairing_toLp (reflectedSmoothing_memLp Q hε (Lp.stronglyMeasurable v) (Lp.memLp v)) (Lp.memLp u),
    integral_pairing_toLp (Lp.memLp v) (reflectedSmoothing_memLp Q hε (Lp.stronglyMeasurable u) (Lp.memLp u)),
    Lp.toLp_coeFn u (Lp.memLp u), Lp.toLp_coeFn v (Lp.memLp v)] at h
  exact h

lemma smoothingLp_tendsto (Q : Triangle) {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (he : Tendsto ε atTop (𝓝 0)) (u : DoubleL2 Q) :
    Tendsto (fun n => smoothingLp Q (hε n) u) atTop (𝓝 u) := by
  have he' : Tendsto ε atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨he,Eventually.of_forall hε⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  convert (smoothing_lpNorm_tendsto Q (Lp.stronglyMeasurable u) (Lp.memLp u)).comp he' using 1
  ext n
  have hm := reflectedSmoothing_memLp Q (hε n) (Lp.stronglyMeasurable u) (Lp.memLp u)
  rw [show smoothingLp Q (hε n) u - u = (hm.sub (Lp.memLp u)).toLp
      (reflectedSmoothing Q (ε n) u - (u : DoublePhase → ℂ)) by
    rw [MemLp.toLp_sub _ (Lp.memLp u), Lp.toLp_coeFn]; rfl]
  rw [Lp.norm_toLp, toReal_eLpNorm (hm.sub (Lp.memLp u)).aestronglyMeasurable]
  rfl

lemma smoothing_variable_pairing (Q : Triangle) {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (he : Tendsto ε atTop (𝓝 0))
    {u : ℕ → DoubleL2 Q} {H : ℝ} (hu : ∀ n, ‖u n‖ ≤ H) (v : DoubleL2 Q) :
    Tendsto (fun n => inner ℂ v (smoothingLp Q (hε n) (u n) - u n)) atTop (𝓝 0) := by
  have hv := (smoothingLp_tendsto Q hε he v).sub_const v
  have hb : Tendsto (fun n => ‖smoothingLp Q (hε n) v - v‖ * H) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero,zero_mul] using hv.norm.mul_const H
  apply squeeze_zero_norm _ hb
  intro n
  rw [inner_sub_right,smoothingLp_adjoint,← inner_sub_left]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hu n) (norm_nonneg _))

end TriangularBilliards

namespace TriangularBilliards
open Analysis Analytic SpatialSmoothing Filter Set
open scoped Topology ComplexConjugate
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

lemma smoothing_toLp_eq (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q)) :
    (reflectedSmoothing_memLp Q hε hfm hf).toLp _ = smoothingLp Q hε (hf.toLp f) := by
  apply ext_inner_left ℂ
  intro v
  have hadj := reflectedSmoothing_adjoint Q hε hfm (Lp.stronglyMeasurable v) hf (Lp.memLp v)
  rw [integral_pairing_toLp (reflectedSmoothing_memLp Q hε hfm hf) (Lp.memLp v),
    integral_pairing_toLp hf (reflectedSmoothing_memLp Q hε (Lp.stronglyMeasurable v) (Lp.memLp v)),
    Lp.toLp_coeFn v (Lp.memLp v)] at hadj
  exact hadj.trans (smoothingLp_adjoint Q hε v (hf.toLp f)).symm

/-- One actual long-clearance-segment approximation, with all bounds and
its relevant Fourier derivative pairing. -/
lemma exists_clearance_data (Q : Triangle) {L ε R T H : ℝ}
    (hε : 0 < ε) (hT : 0 < T) (hH : 0 ≤ H)
    (hR : Q.safetyFactor*ε < R) (hsmall : 2*R*Q.coordinateBound < 1)
    (hL : 2*R+2*ε ≤ L*ε)
    {f : DoubleL2 Q} (hf : ∀ᵐ z ∂doubleMeasure Q, ‖f z‖ ≤ H)
    (hinv : ∀ t, (geodesicHilbertFlow Q).act t f = f)
    (j : ℤ) {U B : DoubleL2 Q}
    (hUB : (geodesicHilbertFlow Q).HasGenerator U B)
    (hB : (angularCircleAction Q).projection (j-1) B = B) :
    ∃ g w p a b : DoubleL2 Q,
      (∀ᵐ z ∂doubleMeasure Q, ‖g z‖ ≤ H) ∧
      ‖g-f‖ ≤ H*(doubleMeasure Q (goodMesh Q L ε T)ᶜ).toReal^(1/2:ℝ) ∧
      (geodesicHilbertFlow Q).HasGenerator g p ∧ ‖p‖ ≤ 2*H/T ∧
      w = smoothingLp Q hε g ∧ ‖w‖ ≤ 4*H ∧
      RotationalCR (geodesicHilbertFlow Q) (transverseHilbertFlow Q) (angularCircleAction Q)
        ((angularCircleAction Q).projection j w) a b ∧
      ‖a‖^2 ≤ 32*derivativeMass*H^2/(T*ε) ∧
      ‖b‖^2 ≤ 32*derivativeMass*H^2/(T*ε) ∧
      ‖inner ℂ B b‖ ≤ 4*‖B‖*H/T + H/T *
        ‖(reflectedSmoothingY_memLp Q hε (Lp.stronglyMeasurable U) (Lp.memLp U)).toLp _‖ := by
  let g := clearanceAverage Q L ε T f
  have hgb := clearanceAverage_bounded Q (L:=L) (ε:=ε) hT hH hf
  have hgs := clearanceAverage_zero Q (L:=L) hT hε f
  obtain ⟨p,hgp,hpb,hps⟩ := clearanceAverage_generator_supported Q (L:=L) hε hT hH hf
  obtain ⟨g₀,hgm,hg₀b,hg₀s,hg₀⟩ := exists_bounded_supported_representative Q hH hgb hgs
  obtain ⟨p₀,hpm,hp₀b,hp₀s,hp₀⟩ := exists_bounded_supported_representative Q
    (by positivity : 0 ≤ 2*H/T) hpb hps
  have hgmem := (Lp.memLp g).ae_eq hg₀.symm
  have hpmem := (Lp.memLp p).ae_eq hp₀.symm
  have hgeq : hgmem.toLp g₀ = g := by
    apply Lp.ext
    exact hgmem.coeFn_toLp.trans hg₀
  have hpeq : hpmem.toLp p₀ = p := by
    apply Lp.ext
    exact hpmem.coeFn_toLp.trans hp₀
  have hgp₀ : (geodesicHilbertFlow Q).HasGenerator (hgmem.toLp g₀) (hpmem.toLp p₀) := by
    rw [hgeq,hpeq]; exact hgp
  obtain ⟨a,b,hcr,ha,hb,hpair⟩ := supported_source_CR Q hε hT hH hR hsmall hL
    hgm hpm hgmem hpmem hgp₀ hg₀b hp₀b hg₀s hp₀s j hUB hB
  let hw := supportedSmoothing_memLp Q hε R hgm hg₀b
  let w := hw.toLp (supportedSmoothing Q ε R g₀)
  refine ⟨g,w,p,a,b,hgb,(clearanceAverage_estimates Q hT hH hf hinv).1,hgp,?_,?_,?_,hcr,ha,hb,hpair⟩
  · exact doubleL2_norm_le_of_ae_bound Q (by positivity) hpb
  · have he := hw.toLp_congr (reflectedSmoothing_memLp Q hε hgm hgmem) (by
      filter_upwards [ae_double_position_in_table Q] with z hz
      exact supportedSmoothing_eq_of_supported Q hε
        ((mul_pos Q.safetyFactor_pos hε).trans hR) (by linarith) hg₀s hz)
    change w = _ at he
    rw [he,smoothing_toLp_eq Q hε hgm hgmem,hgeq]
  · apply doubleL2_norm_le_of_ae_bound Q (by positivity)
    filter_upwards [hw.coeFn_toLp] with z hz
    rw [hz]
    exact supportedSmoothing_norm_bound Q hε R hH hg₀b z

end TriangularBilliards

namespace TriangularBilliards.Analytic
open Filter
open scoped Topology
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

lemma weaklyTendsto_of_inner {u : ℕ → E} {v : E}
    (h : ∀ w, Tendsto (fun n => inner ℂ w (u n)) atTop (𝓝 (inner ℂ w v))) :
    WeaklyTendsto u atTop v := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  intro L
  let w := (InnerProductSpace.toDual ℝ E).symm L
  have hw : ∀ x, (inner ℂ w x).re = L x := by
    intro x
    change (InnerProductSpace.toDual ℝ E) w x = L x
    rw [LinearIsometryEquiv.apply_symm_apply]
  simpa only [Function.comp_def,hw] using Complex.continuous_re.tendsto _ |>.comp (h w)

end TriangularBilliards.Analytic

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
end

section
section
namespace OAI


open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Finset Set
open scoped Topology BigOperators
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Set
open scoped Topology
noncomputable section

namespace TriangularBilliards
open Analysis Analytic SpatialSmoothing Filter Set
open scoped Topology ComplexConjugate
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

lemma smoothing_weak_limit (Q : Triangle) {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (he : Tendsto ε atTop (𝓝 0))
    {u : ℕ → DoubleL2 Q} {H : ℝ} (hu : ∀ n, ‖u n‖ ≤ H)
    {g : DoubleL2 Q} (hg : WeaklyTendsto u atTop g) :
    WeaklyTendsto (fun n => smoothingLp Q (hε n) (u n)) atTop g := by
  apply weaklyTendsto_of_inner
  intro v
  have hh := (smoothing_variable_pairing Q hε he hu v).add (hg.inner_right v)
  simpa only [inner_sub_right,sub_add_cancel,zero_add] using hh

noncomputable def clearanceCost (Q : Triangle) : ℝ :=
  ((volume Q.table).toReal)⁻¹ * (3*(2*(Q.safetyFactor+1)+4)^2*Real.pi)

lemma clearanceCost_nonneg (Q : Triangle) : 0 ≤ clearanceCost Q := by
  unfold clearanceCost
  positivity

/-- The genuine fixed-s weak limit. The ε-dependent mode energy is allowed
to grow as s goes to zero; no s-independent bound is used at this stage. -/
lemma clearance_first_limit (Q : Triangle) {H s : ℝ} (hH : 0 ≤ H) (hs : 0 < s)
    {f : DoubleL2 Q} (hf : ∀ᵐ z ∂doubleMeasure Q, ‖f z‖ ≤ H)
    (hinv : ∀ t, (geodesicHilbertFlow Q).act t f = f)
    (j : ℤ) {U B : DoubleL2 Q}
    (hUB : (geodesicHilbertFlow Q).HasGenerator U B)
    (hB : (angularCircleAction Q).projection (j-1) B = B) :
    ∃ g a b : DoubleL2 Q,
      (∀ᵐ z ∂doubleMeasure Q, ‖g z‖ ≤ H) ∧
      (geodesicHilbertFlow Q).HasGenerator g 0 ∧
      ‖g-f‖ ≤ H * (3*clearanceCost Q*s)^(1/2:ℝ) ∧
      RotationalCR (geodesicHilbertFlow Q) (transverseHilbertFlow Q) (angularCircleAction Q)
        ((angularCircleAction Q).projection j g) a b ∧ inner ℂ B b = 0 := by
  let K := Q.safetyFactor+1
  let L := 2*K+3
  have hK : 0 < K := by dsimp [K]; linarith [Q.safetyFactor_pos]
  have hnb : ∀ᶠ ε : ℝ in 𝓝 0, 2*(K*ε)*Q.coordinateBound < 1 ∧ ε^2 < s := by
    have hc : Continuous (fun ε : ℝ => 2*(K*ε)*Q.coordinateBound) := by fun_prop
    have hd : Continuous (fun ε : ℝ => ε^2) := by fun_prop
    have hc₀ : ∀ᶠ ε : ℝ in 𝓝 0, 2*(K*ε)*Q.coordinateBound < 1 := by
      simpa using hc.continuousAt.eventually (gt_mem_nhds (by simp only [mul_zero,zero_mul]; norm_num))
    have hd₀ : ∀ᶠ ε : ℝ in 𝓝 0, ε^2 < s := by
      simpa using hd.continuousAt.eventually (gt_mem_nhds (by simpa using hs))
    exact hc₀.and hd₀
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp hnb
  obtain ⟨ε,_,hε,he⟩ := exists_seq_strictAnti_tendsto' hδ
  have hpos (n : ℕ) : 0 < ε n := (hε n).1
  have hsmall (n : ℕ) : 2*(K*ε n)*Q.coordinateBound < 1 ∧ (ε n)^2 < s := hball
    (by simpa only [Real.dist_eq, sub_zero, abs_of_pos (hpos n)] using (hε n).2)
  have hT (n : ℕ) : 0 < s/ε n := div_pos hs (hpos n)
  have hR (n : ℕ) : Q.safetyFactor*ε n < K*ε n := by dsimp [K]; nlinarith [hpos n]
  have hL (n : ℕ) : 2*(K*ε n)+2*ε n ≤ L*ε n := by dsimp [L]; nlinarith [hpos n]
  have hd (n : ℕ) := exists_clearance_data Q (L:=L) (hpos n) (hT n) hH (hR n)
    (hsmall n).1 (hL n) hf hinv j hUB hB
  choose g w p a b hgb hclose hgp hpb hw hwb hcr hab hbb hpair using hd
  have hgn (n : ℕ) : ‖g n‖ ≤ H := doubleL2_norm_le_of_ae_bound Q hH (hgb n)
  have hpn : Tendsto p atTop (𝓝 0) := by
    apply squeeze_zero_norm _ (show Tendsto (fun n => (2*H/s)*ε n) atTop (𝓝 0) by
      simpa only [mul_zero] using he.const_mul (2*H/s))
    intro n
    exact (hpb n).trans_eq (by field_simp)
  have hcost (n : ℕ) : (doubleMeasure Q (goodMesh Q L (ε n) (s/ε n))ᶜ).toReal ≤
      3*clearanceCost Q*s := by
    have hl : 0 ≤ L+1 := by dsimp [L]; linarith
    have hh := badMesh_real_bound Q hl (hpos n) (hT n).le
    have hC : ((volume Q.table).toReal)⁻¹*(3*(L+1)^2*Real.pi) = clearanceCost Q := by
      dsimp [clearanceCost,L]; congr 3; dsimp [K]; ring
    rw [hC,div_mul_cancel₀ _ (hpos n).ne'] at hh
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left (hsmall n).2.le (clearanceCost_nonneg Q)])
  have hclosen (n : ℕ) : ‖g n-f‖ ≤ H*(3*clearanceCost Q*s)^(1/2:ℝ) := by
    apply (hclose n).trans
    gcongr
    exact hcost n
  let M := Real.sqrt (32*derivativeMass*H^2/s)
  have hM₀ : 0 ≤ 32*derivativeMass*H^2/s := by
    have := derivativeMass_nonneg
    positivity
  have hnorm {x : ℝ} {n : ℕ} (hx : x^2 ≤ 32*derivativeMass*H^2/((s/ε n)*ε n)) : x ≤ M := by
    rw [div_mul_cancel₀ _ (hpos n).ne'] at hx
    have hh := Real.sq_sqrt hM₀
    have hh' := Real.sqrt_nonneg (32*derivativeMass*H^2/s)
    dsimp [M]
    nlinarith
  have han (n : ℕ) : ‖a n‖ ≤ M := hnorm (hab n)
  have hbn (n : ℕ) : ‖b n‖ ≤ M := hnorm (hbb n)
  have hpair0 : Tendsto (fun n => inner ℂ B (b n)) atTop (𝓝 0) := by
    have hy := scaled_smoothingY_norm_tendsto Q U hpos he
    have hlim := (he.const_mul (4*‖B‖*H/s)).add (hy.const_mul (H/s))
    simp only [mul_zero,add_zero] at hlim
    apply squeeze_zero_norm _ hlim
    intro n
    exact (hpair n).trans_eq (by field_simp)
  let : InnerProductSpace ℝ (DoubleL2 Q) := InnerProductSpace.rclikeToReal ℂ _
  obtain ⟨g₀,_,φ,hφ,hg₀⟩ := exists_weak_subsequence_unrestricted g hgn
  obtain ⟨a₀,_,ψ,hψ,ha₀⟩ := exists_weak_subsequence_unrestricted (a ∘ φ) (fun n => han (φ n))
  obtain ⟨b₀,_,χ,hχ,hb₀⟩ := exists_weak_subsequence_unrestricted (b ∘ φ ∘ ψ) (fun n => hbn (φ (ψ n)))
  let κ := φ ∘ ψ ∘ χ
  have hκ : Tendsto κ atTop atTop := hφ.tendsto_atTop.comp (hψ.tendsto_atTop.comp hχ.tendsto_atTop)
  have hgl : WeaklyTendsto (g ∘ κ) atTop g₀ := hg₀.comp (hψ.tendsto_atTop.comp hχ.tendsto_atTop)
  have hal : WeaklyTendsto (a ∘ κ) atTop a₀ := ha₀.comp hχ.tendsto_atTop
  have hbl : WeaklyTendsto (b ∘ κ) atTop b₀ := hb₀
  have hwl : WeaklyTendsto (w ∘ κ) atTop g₀ := by
    have hh := smoothing_weak_limit Q (fun n => hpos (κ n)) (he.comp hκ) (fun n => hgn (κ n)) hgl
    convert hh using 1
    funext n
    exact hw (κ n)
  refine ⟨g₀,a₀,b₀,?_,?_,?_,?_,?_⟩
  · exact hgl.mem_of_closed_convex (isClosed_ae_bounded H) (convex_ae_bounded H)
      (Eventually.of_forall fun n => hgb (κ n))
  · exact HilbertFlow.HasGenerator.weak_limit (geodesicHilbertFlow Q) hgl
      (weaklyTendsto_of_tendsto (hpn.comp hκ)) (Eventually.of_forall fun n => hgp (κ n))
  · exact (hgl.sub_const f).norm_le (Eventually.of_forall fun n => hclosen (κ n))
  · exact RotationalCR.weak_limit (hwl.map (((angularCircleAction Q).projection j).restrictScalars ℝ))
      hal hbl (fun n => hcr (κ n))
  · exact tendsto_nhds_unique (hbl.inner_right B) (hpair0.comp hκ)

end TriangularBilliards

namespace TriangularBilliards.Analysis
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma HilbertFlow.HasGenerator.invariant {W : HilbertFlow E} {u : E}
    (h : W.HasGenerator u 0) (t : ℝ) : W.act t u = u := by
  have hh := h t
  rw [map_zero,sub_eq_zero] at hh
  exact hh

omit [CompleteSpace E] in
lemma HilbertFlow.hasGenerator_zero_iff (W : HilbertFlow E) (u : E) :
    W.HasGenerator u 0 ↔ ∀ t, W.act t u = u := by
  refine ⟨fun h => h.invariant, fun h t => ?_⟩
  rw [h t,sub_self,map_zero]

lemma RotationalCR.unique_pair {T : ℝ} [Fact (0 < T)]
    {X Y : HilbertFlow E} {V : CircleAction E T} {u a b c d : E}
    (h : RotationalCR X Y V u a b) (h' : RotationalCR X Y V u c d) : a=c ∧ b=d :=
  CR_components_eq (X.generator_unique h.generators.1 h'.generators.1)
    (Y.generator_unique h.generators.2 h'.generators.2)

end TriangularBilliards.Analysis

namespace TriangularBilliards
open Analysis Analytic SpatialSmoothing Filter Set
open scoped Topology ComplexConjugate
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

lemma exists_bounded_representative (Q : Triangle) {u : DoubleL2 Q} {H : ℝ}
    (hH : 0 ≤ H) (hu : ∀ᵐ z ∂doubleMeasure Q, ‖u z‖ ≤ H) :
    ∃ f : DoublePhase → ℂ, StronglyMeasurable f ∧
      (∀ z, ‖f z‖ ≤ H) ∧ f =ᵐ[doubleMeasure Q] u := by
  classical
  let E := {z : DoublePhase | ‖u z‖ ≤ H}
  have hE : MeasurableSet E :=
    measurableSet_le (Lp.stronglyMeasurable u).measurable.norm measurable_const
  refine ⟨E.indicator u,(Lp.stronglyMeasurable u).indicator hE,?_,?_⟩
  · intro z
    by_cases hz : z ∈ E
    · simpa only [indicator_of_mem hz] using (show ‖u z‖ ≤ H from hz)
    · simpa only [indicator_of_notMem hz,norm_zero] using hH
  · filter_upwards [hu] with z hz
    exact indicator_of_mem (show z ∈ E from hz) _

lemma bounded_invariant_CR_ae (Q : Triangle) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {H : ℝ} (_hH : 0 ≤ H) {f : DoubleL2 Q}
      (_hf : ∀ᵐ z ∂doubleMeasure Q, ‖f z‖ ≤ H)
      (_hfi : (geodesicHilbertFlow Q).HasGenerator f 0) (j : ℤ),
      ∃ a b : DoubleL2 Q,
        RotationalCR (geodesicHilbertFlow Q) (transverseHilbertFlow Q)
          (angularCircleAction Q) ((angularCircleAction Q).projection j f) a b ∧
        ‖a‖ ≤ C*H ∧ ‖b‖ ≤ C*H := by
  obtain ⟨C,hC,hbound⟩ := bounded_invariant_CR Q
  refine ⟨C,hC,?_⟩
  intro H hH f hf hfi j
  obtain ⟨f₀,hm,hb,he⟩ := exists_bounded_representative Q hH hf
  have hp : MemLp f₀ 2 (doubleMeasure Q) := (Lp.memLp f).ae_eq he.symm
  have hpeq : hp.toLp f₀ = f := Lp.ext (hp.coeFn_toLp.trans he)
  rw [← hpeq] at hfi ⊢
  exact hbound hm hp hb hfi j

/-- The second limit invokes the *exact invariant* uniform mode bound,
not the fixed-s bound used before. -/
lemma clearance_second_limit (Q : Triangle) {H : ℝ} (hH : 0 ≤ H)
    {f : DoubleL2 Q} (hf : ∀ᵐ z ∂doubleMeasure Q, ‖f z‖ ≤ H)
    (hinv : ∀ t, (geodesicHilbertFlow Q).act t f = f)
    (j : ℤ) {a b U : DoubleL2 Q}
    (hcr : RotationalCR (geodesicHilbertFlow Q) (transverseHilbertFlow Q)
      (angularCircleAction Q) ((angularCircleAction Q).projection j f) a b)
    (hUb : (geodesicHilbertFlow Q).HasGenerator U b) : b=0 := by
  obtain ⟨C,hC,hbound⟩ := bounded_invariant_CR_ae Q
  obtain ⟨s,_,hs,he⟩ := exists_seq_strictAnti_tendsto' (by norm_num : (0:ℝ)<1)
  have hpos (n : ℕ) : 0 < s n := (hs n).1
  have hmode := (hcr.mode_components ((angularCircleAction Q).projection_eigen j f)).2
  have hd n := clearance_first_limit Q hH (hpos n) hf hinv j hUb hmode
  choose g a' b' hgb hgi hclose hcr' hpair using hd
  have hbounded (n : ℕ) : ‖a' n‖ ≤ C*H ∧ ‖b' n‖ ≤ C*H := by
    obtain ⟨a₀,b₀,hc,ha,hb⟩ := hbound hH (hgb n) (hgi n) j
    obtain ⟨rfl,rfl⟩ := (hcr' n).unique_pair hc
    exact ⟨ha,hb⟩
  have hgstrong : Tendsto g atTop (𝓝 f) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hzero := (he.const_mul (3*clearanceCost Q)).rpow_const (Or.inr (by norm_num : (0:ℝ) ≤ 1/2))
    have hlim : Tendsto (fun n => H*(3*clearanceCost Q*s n)^(1/2:ℝ)) atTop (𝓝 0) := by
      simpa only [mul_zero,Real.zero_rpow (by norm_num : (1/2:ℝ) ≠ 0)] using hzero.const_mul H
    exact squeeze_zero (fun n => norm_nonneg _) hclose hlim
  let : InnerProductSpace ℝ (DoubleL2 Q) := InnerProductSpace.rclikeToReal ℂ _
  obtain ⟨a₀,_,φ,hφ,ha₀⟩ := exists_weak_subsequence_unrestricted a' (fun n => (hbounded n).1)
  obtain ⟨b₀,_,ψ,hψ,hb₀⟩ := exists_weak_subsequence_unrestricted (b' ∘ φ) (fun n => (hbounded (φ n)).2)
  have hgweak := weaklyTendsto_of_tendsto (hgstrong.comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop))
  have hc := RotationalCR.weak_limit
    (hgweak.map (((angularCircleAction Q).projection j).restrictScalars ℝ))
    (ha₀.comp hψ.tendsto_atTop) hb₀ (fun n => hcr' (φ (ψ n)))
  obtain ⟨_,hh⟩ := hcr.unique_pair hc
  have hp : inner ℂ b b₀ = 0 := tendsto_nhds_unique (hb₀.inner_right b)
    (by simpa only [Function.comp_def,hpair] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℂ)) atTop (𝓝 0)))
  rw [← hh] at hp
  exact inner_self_eq_zero.mp hp

/-- Analytic rigidity, on the actual double of every nondegenerate triangle.
No irrational-angle assumption is needed for this stage. -/
theorem bounded_invariant_rigidity (Q : Triangle) {H : ℝ} (hH : 0 ≤ H)
    {f : DoubleL2 Q} (hf : ∀ᵐ z ∂doubleMeasure Q, ‖f z‖ ≤ H)
    (hinv : ∀ t, (geodesicHilbertFlow Q).act t f = f) (j : ℤ) :
    RotationalCR (geodesicHilbertFlow Q) (transverseHilbertFlow Q)
      (angularCircleAction Q) ((angularCircleAction Q).projection j f) 0 0 := by
  have hfi := ((geodesicHilbertFlow Q).hasGenerator_zero_iff f).mpr hinv
  obtain ⟨f₀,hm,hb,he⟩ := exists_bounded_representative Q hH hf
  have hp : MemLp f₀ 2 (doubleMeasure Q) := (Lp.memLp f).ae_eq he.symm
  have hpeq : hp.toLp f₀ = f := Lp.ext (hp.coeFn_toLp.trans he)
  obtain ⟨_,_,htail⟩ := bounded_invariant_tail_endpoint Q
  obtain ⟨a,b,hcr,_,ht⟩ := htail hm hp hb (hpeq.symm ▸ hfi)
  simp only [hpeq] at hcr ht
  have hz (m : ℤ) : b m = 0 := clearance_second_limit Q hH hf hinv m (hcr m) (ht m)
  have ha : a j = 0 := by
    have hh := invariant_CR_recurrence (geodesicHilbertFlow Q) (transverseHilbertFlow Q)
      (angularCircleAction Q) (dense_rotationalCR_core Q) hfi a b hcr j
    simpa only [hz,add_zero] using hh
  simpa only [ha,hz] using hcr j

end TriangularBilliards

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
end

section
section
namespace OAI

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Finset Set
open scoped Topology BigOperators
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Set
open scoped Topology
noncomputable section

namespace TriangularBilliards
open Analysis Analytic SpatialSmoothing Filter Set
open scoped Topology ComplexConjugate ContDiff
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

lemma bounded_invariant_transverse (Q : Triangle) {H : ℝ} (hH : 0 ≤ H)
    {f : DoubleL2 Q} (hf : ∀ᵐ z ∂doubleMeasure Q, ‖f z‖ ≤ H)
    (hinv : ∀ t, (geodesicHilbertFlow Q).act t f = f) :
    (transverseHilbertFlow Q).HasGenerator f 0 := by
  apply ((transverseHilbertFlow Q).hasGenerator_zero_iff f).mpr
  intro t
  have hj (j : ℤ) : (transverseHilbertFlow Q).act t ((angularCircleAction Q).projection j f) =
      (angularCircleAction Q).projection j f := by
    have hh := (bounded_invariant_rigidity Q hH hf hinv j).generators.2
    simp only [sub_self,smul_zero] at hh
    exact hh.invariant t
  calc
    _ = (transverseHilbertFlow Q).act t (∑' j : ℤ, (angularCircleAction Q).projection j f) := by
      rw [(angularCircleAction Q).tsum_projection]
    _ = ∑' j : ℤ, (transverseHilbertFlow Q).act t ((angularCircleAction Q).projection j f) :=
      ((transverseHilbertFlow Q).act t).toContinuousLinearMap.map_tsum
        ((angularCircleAction Q).summable_projection f)
    _ = _ := by simp only [hj,(angularCircleAction Q).tsum_projection]

lemma transverse_invariant_smoothing_pairing_zero (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor*ε < R)
    (hsmall : 2*R*Q.coordinateBound < 1) (hA : 2*R+ε ≤ A)
    {f g : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hf : MemLp f 2 (doubleMeasure Q)) (hg : MemLp g 2 (doubleMeasure Q))
    (hfi : (transverseHilbertFlow Q).HasGenerator (hf.toLp f) 0)
    {H : ℝ} (hH : ∀ z, ‖g z‖ ≤ H) (hgs : SpatiallyZero Q A g) :
    (∫ z, reflectedSmoothingY Q ε f z * conj (g z) ∂doubleMeasure Q) = 0 := by
  have hgen := supportedSmoothing_transverse_generator Q hε hR hsmall hA hgm hH hg hgs
  have hsk := (transverseHilbertFlow Q).generator_skew hfi hgen
  simp only [inner_zero_left,add_zero] at hsk
  have hh := reflectedSmoothingY_adjoint Q hε hfm hgm hf hg
  rw [hh,integral_pairing_toLp hf (reflectedSmoothingY_memLp Q hε hgm hg)]
  rw [inner_eq_zero_symm.mpr hsk,neg_zero]

lemma transverse_invariant_smoothing_zero (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor*ε < R)
    (hsmall : 2*R*Q.coordinateBound < 1) (hA : 2*R+ε ≤ A)
    {f : DoublePhase → ℂ} (hfm : StronglyMeasurable f)
    (hf : MemLp f 2 (doubleMeasure Q))
    (hfi : (transverseHilbertFlow Q).HasGenerator (hf.toLp f) 0)
    {H : ℝ} (hH : ∀ z, ‖f z‖ ≤ H) :
    ∀ᵐ z ∂doubleMeasure Q, A ≤ Q.clearance z.1.1 → reflectedSmoothingY Q ε f z = 0 := by
  let D := reflectedSmoothingY Q ε f
  let E := {z : DoublePhase | A ≤ Q.clearance z.1.1}
  have hDp := reflectedSmoothingY_memLp Q hε hfm hf
  have hDm := isBoundedBilinearMap_apply.continuous.comp_stronglyMeasurable
    ((reflectedSmoothingGradient_stronglyMeasurable Q ε hfm).prodMk
      (transverseVelocity_stronglyMeasurable.comp_measurable (measurable_fst.snd.prodMk measurable_snd)))
  have hE : MeasurableSet E := measurableSet_le measurable_const
    (Q.clearance_lipschitz.continuous.measurable.comp measurable_fst.fst)
  let g := E.indicator D
  have hgp : MemLp g 2 (doubleMeasure Q) := hDp.indicator hE
  have hgm : StronglyMeasurable g := hDm.indicator hE
  have hH₀ : 0 ≤ H := (norm_nonneg _).trans (hH ((0,1),0))
  have hgb : ∀ z, ‖g z‖ ≤ 4*derivativeMass*H/ε := by
    intro z
    by_cases hz : z ∈ E
    · change ‖E.indicator D z‖ ≤ _
      rw [indicator_of_mem hz]
      exact reflectedSmoothingY_norm_bound Q hε hH₀ hH z
    · change ‖E.indicator D z‖ ≤ _
      rw [indicator_of_notMem hz,norm_zero]
      exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) derivativeMass_nonneg) hH₀) hε.le
  have hgs : SpatiallyZero Q A g := by
    intro y _ hy v b
    exact indicator_of_notMem (show ((y,v),b) ∉ E from not_le.mpr hy) D
  have hp := transverse_invariant_smoothing_pairing_zero Q hε hR hsmall hA hfm hgm hf hgp hfi hgb hgs
  have hi : (∫ z, g z * conj (g z) ∂doubleMeasure Q) = 0 := by
    rw [← hp]
    apply integral_congr_ae
    filter_upwards with z
    by_cases hz : z ∈ E
    · simp only [g,indicator_of_mem hz,D]
    · simp only [g,indicator_of_notMem hz,map_zero,mul_zero]
  rw [integral_pairing_toLp hgp hgp,inner_self_eq_zero] at hi
  have hgzero : g =ᵐ[doubleMeasure Q] 0 := by
    have hh := hgp.coeFn_toLp
    rw [hi] at hh
    exact hh.symm.trans (Lp.coeFn_zero _ _ _)
  filter_upwards [hgzero] with z hz hza
  simpa only [g,indicator_of_mem (show z ∈ E from hza),Pi.zero_apply] using hz

lemma realLinear_zero_of_velocity_transverse (L : ℂ →L[ℝ] ℂ) (v : Circle) (b : ZMod 2)
    (hx : L (v : ℂ)=0) (hy : L (transverseVelocity v b)=0) : L=0 := by
  have hi : L (Complex.I*(v:ℂ))=0 := by
    by_cases hb : b=0
    · simpa only [transverseVelocity,hb,ite_true] using hy
    · simpa only [transverseVelocity,hb,ite_false,neg_mul,map_neg,neg_eq_zero] using hy
  ext z
  have hv : (v:ℂ) ≠ 0 := Circle.coe_ne_zero v
  have hz : z = (z/(v:ℂ)).re • (v:ℂ) + (z/(v:ℂ)).im • (Complex.I*(v:ℂ)) := by
    rw [Complex.real_smul,Complex.real_smul]
    calc
      _ = (z/(v:ℂ))*(v:ℂ) := (div_mul_cancel₀ z hv).symm
      _ = _ := by
        conv_lhs => rw [← Complex.re_add_im (z/(v:ℂ))]
        simp only [div_eq_mul_inv]
        ring
  rw [hz,map_add,map_smul,map_smul,hx,hi,smul_zero,smul_zero,add_zero]
  rfl

lemma invariant_smoothing_gradient_zero (Q : Triangle) {ε R A : ℝ}
    (hε : 0 < ε) (hR : Q.safetyFactor*ε < R)
    (hsmall : 2*R*Q.coordinateBound < 1) (hA : 2*R+ε ≤ A)
    {f : DoublePhase → ℂ} (hfm : StronglyMeasurable f)
    (hf : MemLp f 2 (doubleMeasure Q))
    (hfx : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) 0)
    {H : ℝ} (hH : ∀ z, ‖f z‖ ≤ H) :
    ∀ᵐ z ∂doubleMeasure Q, A ≤ Q.clearance z.1.1 →
      fderiv ℝ (fun y => reflectedSmoothing Q ε f ((y,z.1.2),z.2)) z.1.1 = 0 := by
  have hb : ∀ᵐ z ∂doubleMeasure Q, ‖(hf.toLp f) z‖ ≤ H := by
    filter_upwards [hf.coeFn_toLp] with z hz
    simpa only [hz] using hH z
  have hfy := bounded_invariant_transverse Q ((norm_nonneg _).trans (hH ((0,1),0))) hb hfx.invariant
  filter_upwards [invariant_smoothing_direction_zero Q hε hR hsmall hA hfm hf hfx hH,
    transverse_invariant_smoothing_zero Q hε hR hsmall hA hfm hf hfy hH] with z hx hy ha
  have he := (reflectedSmoothing_hasFDerivAt Q hε hfm
    (bounded_spatialSlice_integrable Q hfm hH z.1.2 z.2)
    (fun i => bounded_spatialSlice_integrable Q hfm hH (reflectedDirection Q i z.1.2) (z.2+1)) z.1.1).fderiv
  rw [he]
  exact realLinear_zero_of_velocity_transverse _ z.1.2 z.2 (hx ha) (hy ha)

end TriangularBilliards

namespace TriangularBilliards
open Analysis Analytic SpatialSmoothing Filter Set
open scoped Topology ContDiff ComplexConjugate

lemma double_ae_slices (Q : Triangle) {p : DoublePhase → Prop}
    (hp : ∀ᵐ z ∂doubleMeasure Q, p z) :
    ∀ᵐ c ∂angularMeasure.prod parityMeasure,
      ∀ᵐ x ∂((volume Q.table)⁻¹ • volume.restrict Q.table), p ((x,c.1),c.2) := by
  let μ : Measure ℂ := (volume Q.table)⁻¹ • volume.restrict Q.table
  have ha := (measurePreserving_prodAssoc μ angularMeasure parityMeasure).symm MeasurableEquiv.prodAssoc
  exact Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap
    (μ := angularMeasure.prod parityMeasure) (ν := μ)).quasiMeasurePreserving.ae
      (ha.quasiMeasurePreserving.ae hp))

lemma double_ae_of_slices (Q : Triangle) {f g : DoublePhase → ℂ}
    (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hp : ∀ᵐ c ∂angularMeasure.prod parityMeasure,
      ∀ᵐ x ∂((volume Q.table)⁻¹ • volume.restrict Q.table), f ((x,c.1),c.2)=g ((x,c.1),c.2)) :
    f =ᵐ[doubleMeasure Q] g := by
  let μ : Measure ℂ := (volume Q.table)⁻¹ • volume.restrict Q.table
  have hm : MeasurableSet {p : DirectionParity × ℂ | f ((p.2,p.1.1),p.1.2)=g ((p.2,p.1.1),p.1.2)} :=
    measurableSet_eq_fun (hfm.measurable.comp ((measurable_snd.prodMk measurable_fst.fst).prodMk measurable_fst.snd))
      (hgm.measurable.comp ((measurable_snd.prodMk measurable_fst.fst).prodMk measurable_fst.snd))
  have hh := (Measure.ae_prod_iff_ae_ae hm).mpr hp
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := angularMeasure.prod parityMeasure)).quasiMeasurePreserving.ae hh
  exact (measurePreserving_prodAssoc μ angularMeasure parityMeasure).quasiMeasurePreserving.ae hs

lemma smoothing_gradient_zero_on_slice (Q : Triangle) {ε A : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} (hfm : StronglyMeasurable f) {H : ℝ} (hb : ∀ z, ‖f z‖ ≤ H)
    (c : DirectionParity)
    (hD : ∀ᵐ x ∂((volume Q.table)⁻¹ • volume.restrict Q.table),
      A ≤ Q.clearance x → fderiv ℝ (fun y => reflectedSmoothing Q ε f ((y,c.1),c.2)) x=0) :
    ∀ x ∈ Q.table, A < Q.clearance x →
      fderiv ℝ (fun y => reflectedSmoothing Q ε f ((y,c.1),c.2)) x=0 := by
  let U := Q.table ∩ {x | A < Q.clearance x}
  have hU : IsOpen U := Q.isOpen_table.inter (isOpen_lt continuous_const Q.clearance_lipschitz.continuous)
  have hd := (Measure.ae_ennreal_smul_measure_iff (by simpa using Q.area_lt_top.ne)).mp hD
  have he : (fun x => fderiv ℝ (fun y => reflectedSmoothing Q ε f ((y,c.1),c.2)) x)
      =ᵐ[volume.restrict U] (fun _ => 0) := by
    filter_upwards [ae_mono (Measure.restrict_mono inter_subset_left le_rfl) hd,
      ae_restrict_mem hU.measurableSet] with x hx hu
    exact hx hu.2.le
  have hsm := reflectedSmoothing_contDiff Q hε (bounded_spatialSlice_integrable Q hfm hb c.1 c.2)
    (fun i => bounded_spatialSlice_integrable Q hfm hb (reflectedDirection Q i c.1) (c.2+1))
  exact fun x hx ha => Measure.eqOn_open_of_ae_eq he hU
    (hsm.continuous_fderiv (by simp)).continuousOn continuousOn_const ⟨hx,ha⟩

end TriangularBilliards
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

lemma eventual_equal_of_vanishing_gradient {U : Set ℂ} (hU : Convex ℝ U)
    {d : ℂ → ℝ} (hd : Continuous d) (hpos : ∀ x ∈ U, 0 < d x)
    {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0))
    {F : ℕ → ℂ → ℂ} (hF : ∀ n, Differentiable ℝ (F n))
    (hD : ∀ n x, x ∈ U → a n < d x → fderiv ℝ (F n) x = 0)
    {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) :
    ∀ᶠ n in atTop, F n x = F n y := by
  have hs : segment ℝ x y ⊆ U := hU.segment_subset hx hy
  have hscompact : IsCompact (segment ℝ x y) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image (by fun_prop)
  obtain ⟨z,hz,hm⟩ := hscompact.exists_isMinOn ⟨x,left_mem_segment ℝ x y⟩ hd.continuousOn
  have hp := hpos z (hs hz)
  filter_upwards [ha.eventually (gt_mem_nhds hp)] with n hn
  have hdz : ∀ w ∈ segment ℝ x y, fderiv ℝ (F n) w=0 := by
    intro w hw
    exact hD n w (hs hw) (hn.trans_le (hm hw))
  have hl := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := F n) (f' := fun _ => (0 : ℂ →L[ℝ] ℂ)) (C := (0:ℝ))
    (fun w hw => (hdz w hw ▸ (hF n w).hasFDerivAt).hasFDerivWithinAt)
    (fun _ _ => by simp) (convex_segment x y) (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  have he : F n y = F n x := sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa only [zero_mul] using hl))
  exact he.symm

lemma ae_constant_of_eventual_equal {μ : Measure ℂ} [IsProbabilityMeasure μ]
    {U : Set ℂ} (hU : ∀ᵐ x ∂μ, x ∈ U) {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hc : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (he : ∀ x ∈ U, ∀ y ∈ U, ∀ᶠ n in atTop, F n x = F n y) :
    f =ᵐ[μ] fun _ => ∫ x, f x ∂μ := by
  obtain ⟨y,hy,hcy⟩ := (hU.and hc).exists
  have hfe : f =ᵐ[μ] fun _ => f y := by
    filter_upwards [hU,hc] with x hx hcx
    apply tendsto_nhds_unique hcx
    apply hcy.congr'
    filter_upwards [he x hx y hy] with n hn
    exact hn.symm
  have hi : (∫ x, f x ∂μ) = f y := by
    simp only [integral_congr_ae hfe,integral_const,probReal_univ,one_smul]
  simpa only [hi] using hfe

namespace TriangularBilliards
open Analysis Analytic SpatialSmoothing Filter Set
open scoped Topology ContDiff ComplexConjugate

/-- The actual bounded invariant is independent of the spatial position on each
of the two triangle sheets, almost everywhere in direction and sheet. -/
theorem bounded_invariant_spatial_constancy (Q : Triangle)
    {f : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q))
    {H : ℝ} (hb : ∀ z, ‖f z‖ ≤ H)
    (hfx : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) 0) :
    ∀ᵐ c ∂angularMeasure.prod parityMeasure,
      (fun x => f ((x,c.1),c.2)) =ᵐ[(volume Q.table)⁻¹ • volume.restrict Q.table]
        (fun _ => ∫ x, f ((x,c.1),c.2) ∂((volume Q.table)⁻¹ • volume.restrict Q.table)) := by
  let K := Q.safetyFactor+1
  have hc : Continuous (fun ε : ℝ => 2*(K*ε)*Q.coordinateBound) := by fun_prop
  have hnb : ∀ᶠ ε : ℝ in 𝓝 0, 2*(K*ε)*Q.coordinateBound < 1 := by
    simpa using hc.continuousAt.eventually (gt_mem_nhds (by simp only [mul_zero,zero_mul]; norm_num))
  obtain ⟨δ,hδ,hδb⟩ := Metric.eventually_nhds_iff.mp hnb
  obtain ⟨ε,_,hε,he⟩ := exists_seq_strictAnti_tendsto' hδ
  have hpos (n : ℕ) : 0 < ε n := (hε n).1
  have hsmall (n : ℕ) : 2*(K*ε n)*Q.coordinateBound < 1 := hδb
    (by simpa only [Real.dist_eq,sub_zero,abs_of_pos (hpos n)] using (hε n).2)
  have hR (n : ℕ) : Q.safetyFactor*ε n < K*ε n := by dsimp [K]; nlinarith [hpos n]
  let A : ℕ → ℝ := fun n => (2*K+1)*ε n
  have hA (n : ℕ) : 2*(K*ε n)+ε n ≤ A n := by dsimp [A]; ring_nf; rfl
  have hder (n : ℕ) := double_ae_slices Q (invariant_smoothing_gradient_zero Q (hpos n)
    (hR n) (hsmall n) (hA n) hfm hf hfx hb)
  have hlim := smoothingLp_tendsto Q hpos he (hf.toLp f)
  obtain ⟨φ,hφ,hpoint⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hpoint' : ∀ᵐ z ∂doubleMeasure Q,
      Tendsto (fun n => reflectedSmoothing Q (ε (φ n)) f z) atTop (𝓝 (f z)) := by
    have hcoe (n : ℕ) : ∀ᵐ z ∂doubleMeasure Q,
        (smoothingLp Q (hpos (φ n)) (hf.toLp f)) z = reflectedSmoothing Q (ε (φ n)) f z := by
      rw [← smoothing_toLp_eq Q (hpos (φ n)) hfm hf]
      exact (reflectedSmoothing_memLp Q (hpos (φ n)) hfm hf).coeFn_toLp
    filter_upwards [hpoint,hf.coeFn_toLp,ae_all_iff.mpr hcoe] with z hz hfz hsz
    simpa only [hfz,hsz] using hz
  let μ : Measure ℂ := (volume Q.table)⁻¹ • volume.restrict Q.table
  have hμ : IsProbabilityMeasure μ := ⟨Q.normalized_area_univ⟩
  have hμU : ∀ᵐ x ∂μ, x ∈ Q.table := Measure.ae_smul_measure (ae_restrict_mem Q.measurableSet_table) _
  filter_upwards [double_ae_slices Q hpoint',ae_all_iff.mpr hder] with c hc hdc
  apply ae_constant_of_eventual_equal hμU hc
  intro x hx y hy
  apply eventual_equal_of_vanishing_gradient (convex_convexHull ℝ (range Q.vertex)).interior
    Q.clearance_lipschitz.continuous (fun z hz => Q.clearance_pos_of_mem_table hz)
    (a := fun n => A (φ n)) (by simpa only [A,mul_zero,Function.comp_def] using (he.comp hφ.tendsto_atTop).const_mul (2*K+1))
    (fun n => (reflectedSmoothing_contDiff Q (hpos (φ n))
      (bounded_spatialSlice_integrable Q hfm hb c.1 c.2)
      (fun i => bounded_spatialSlice_integrable Q hfm hb (reflectedDirection Q i c.1) (c.2+1))).differentiable (by simp))
    (fun n => smoothing_gradient_zero_on_slice Q (hpos (φ n)) hfm hb c (hdc (φ n))) hx hy

end TriangularBilliards

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
end

section
section
namespace OAI


open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Finset Set
open scoped Topology BigOperators
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

namespace TriangularBilliards
open Analysis Analytic SpatialSmoothing Filter Set
open scoped Topology ContDiff ComplexConjugate

def spatialMean (Q : Triangle) (f : DoublePhase → ℂ) (c : DirectionParity) : ℂ :=
  ∫ x, f ((x,c.1),c.2) ∂((volume Q.table)⁻¹ • volume.restrict Q.table)

lemma spatialMean_stronglyMeasurable (Q : Triangle) {f : DoublePhase → ℂ}
    (hf : StronglyMeasurable f) : StronglyMeasurable (spatialMean Q f) := by
  have h : StronglyMeasurable (Function.uncurry (fun c : DirectionParity => fun x : ℂ => f ((x,c.1),c.2))) :=
    hf.comp_measurable ((measurable_snd.prodMk measurable_fst.fst).prodMk measurable_fst.snd)
  exact h.integral_prod_right

lemma Triangle.clearance_pos_of_mem_side (Q : Triangle) {q : ℂ} {i : Fin 3} (hq : q ∈ Q.side i) :
    0 < Q.clearance q := by
  apply ((finite_range Q.vertex).isClosed.notMem_iff_infDist_pos (range_nonempty _)).mp
  rintro ⟨k,rfl⟩
  obtain ⟨j,hjk,hji⟩ := (by decide : ∀ i k : Fin 3, ∃ j : Fin 3, j≠k ∧ j≠i+2) i k
  have hj : Q.basis.coord j (Q.vertex k)=0 := (Q.basis.coord_apply j k).trans (ite_eq_right hjk)
  exact hji ((Q.side_coord_zero_iff hq j).mp hj)

lemma Triangle.side_mem_hull (Q : Triangle) {q : ℂ} {i : Fin 3} (hq : q ∈ Q.side i) :
    q ∈ convexHull ℝ (range Q.vertex) :=
  (convex_convexHull ℝ (range Q.vertex)).segment_subset
    (subset_convexHull ℝ _ (mem_range_self i)) (subset_convexHull ℝ _ (mem_range_self (i+1)))
      (openSegment_subset_segment ℝ _ _ hq)

lemma directS_eq_const_of_slice (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} {v : Circle} {b : ZMod 2} {a : ℂ}
    (hf : (fun y => f ((y,v),b)) =ᵐ[volume.restrict Q.table] (fun _ => a))
    {x : ℂ} (hx : Metric.ball x ε ⊆ Q.table) : directS Q ε f b v x = a := by
  have hi : (∫ y in Q.table, kernel ε (x-y)) = 1 := by
    rw [← integral_indicator Q.measurableSet_table]
    calc
      _ = ∫ y : ℂ, kernel ε (x-y) := by
        apply integral_congr_ae
        filter_upwards with y
        by_cases hy : y∈Q.table
        · exact indicator_of_mem hy _
        · rw [indicator_of_notMem hy]
          symm
          by_contra hn
          have hm : x-y ∈ support (kernel ε) := hn
          rw [kernel_support hε,mem_ball_zero_iff] at hm
          apply hy
          apply hx
          simpa only [Metric.mem_ball,dist_eq_norm,norm_sub_rev] using hm
      _ = 1 := (integral_sub_left_eq_self (fun y : ℂ => kernel ε y) volume x).trans (kernel_integral hε)
  calc
    _ = ∫ y in Q.table, kernel ε (x-y) • a := by
      apply integral_congr_ae
      filter_upwards [hf] with y hy
      rw [hy]
    _ = a := by rw [integral_smul_const,hi,one_smul]

lemma reflectedSmoothing_eq_const_of_slice (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} {v : Circle} {b : ZMod 2} {a : ℂ}
    (hf : (fun y => f ((y,v),b)) =ᵐ[volume.restrict Q.table] (fun _ => a))
    {x : ℂ} (hx : Metric.ball x ε ⊆ Q.table)
    (hcoord : ∀ j : Fin 3, Q.coordinateBound*ε < Q.basis.coord (j+2) x) :
    reflectedSmoothing Q ε f ((x,v),b) = a := by
  rw [reflectedSmoothing,directS_eq_const_of_slice Q hε hf hx]
  have hz : (∑ j : Fin 3, reflectedS Q j ε f b v x)=0 :=
    Finset.sum_eq_zero (fun j _ => reflectedS_zero_of_coord Q j hε f b v (hcoord j))
  rw [hz,add_zero]

end TriangularBilliards
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate ContDiff
noncomputable section
local instance : Fact (Module.finrank ℝ ℂ = 2) := ⟨Complex.finrank_real_complex⟩

lemma equal_of_zero_gradient_openSegment {F : ℂ → ℂ} (hF : ContDiff ℝ ∞ F)
    {x y : ℂ} (hD : ∀ z ∈ openSegment ℝ x y, fderiv ℝ F z=0) : F x=F y := by
  have hcl := closure_minimal hD (isClosed_eq (hF.continuous_fderiv (by simp)) continuous_const)
  rw [closure_openSegment] at hcl
  have hl := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := F) (f' := fun _ => (0 : ℂ →L[ℝ] ℂ)) (C := (0:ℝ))
    (fun w hw => (hcl hw ▸ (hF.differentiable (by simp) w).hasFDerivAt).hasFDerivWithinAt)
    (fun _ _ => by simp) (convex_segment x y) (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  exact (sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa only [zero_mul] using hl))).symm

lemma irrational_arg_of_angle {a b : ℂ} (ha : a≠0) (hb : b≠0)
    (h : Irrational (InnerProductGeometry.angle a b / Real.pi)) :
    Irrational ((conj a*b).arg / Real.pi) := by
  have he : InnerProductGeometry.angle a b = |(conj a*b).arg| := by
    rw [Complex.orientation.angle_eq_abs_oangle_toReal ha hb,Complex.oangle,Complex.arg_coe_angle_toReal_eq_arg]
  rw [he] at h
  rcases le_or_gt 0 (conj a*b).arg with hn|hn
  · simpa only [abs_of_nonneg hn] using h
  · simpa only [abs_of_neg hn,neg_div,irrational_neg_iff] using h

lemma complex_div_conj_eq_exp_double_arg {w : ℂ} (hw : w≠0) :
    w / conj w = Complex.exp (2*(w.arg:ℂ)*Complex.I) := by
  have hn : (‖w‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw)
  have hconj : conj w = (‖w‖:ℂ)*Complex.exp (-(w.arg:ℂ)*Complex.I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I w]
    simp only [map_mul,Complex.conj_ofReal,← Complex.exp_conj,Complex.conj_I]
    congr 2; ring
  rw [hconj]
  conv_lhs => lhs; rw [← Complex.norm_mul_exp_arg_mul_I w]
  rw [mul_div_mul_left _ _ hn,← Complex.exp_sub]
  congr 1
  ring

namespace TriangularBilliards
open Analysis Analytic SpatialSmoothing Filter Set
open scoped Topology ContDiff ComplexConjugate

lemma spatialMean_reflection_invariant (Q : Triangle)
    {f : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hf : MemLp f 2 (doubleMeasure Q))
    {H : ℝ} (hb : ∀ z, ‖f z‖ ≤ H)
    (hfx : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) 0) (i : Fin 3) :
    spatialMean Q f ∘ directionParityReflection Q i =ᵐ[angularMeasure.prod parityMeasure]
      spatialMean Q f := by
  obtain ⟨x,hx⟩ := Q.table_nonempty
  let q := midpoint ℝ (Q.vertex i) (Q.vertex (i+1))
  have hq : q ∈ Q.side i := midpoint_mem_openSegment _ _
  have hopen : openSegment ℝ x q ⊆ Q.table :=
    (convex_convexHull ℝ (range Q.vertex)).openSegment_interior_self_subset_interior hx (Q.side_mem_hull hq)
  have hpos : ∀ y ∈ segment ℝ x q, 0 < Q.clearance y := by
    intro y hy
    rw [← insert_endpoints_openSegment] at hy
    rcases hy with rfl|rfl|hy
    · exact Q.clearance_pos_of_mem_table hx
    · exact Q.clearance_pos_of_mem_side hq
    · exact Q.clearance_pos_of_mem_table (hopen hy)
  have hscompact : IsCompact (segment ℝ x q) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image (by fun_prop)
  obtain ⟨y,hy,hmin⟩ := hscompact.exists_isMinOn ⟨x,left_mem_segment ℝ x q⟩
    Q.clearance_lipschitz.continuous.continuousOn
  obtain ⟨r,hr,hrball⟩ := Metric.mem_nhds_iff.mp (Q.isOpen_table.mem_nhds hx)
  let K := Q.safetyFactor+1
  have hK : 0 < K := by dsimp [K]; linarith [Q.safetyFactor_pos]
  have hev (a d : ℝ) (hd : 0 < d) : ∀ᶠ ε : ℝ in 𝓝 0, a*ε < d := by
    have hc : Continuous (fun ε : ℝ => a*ε) := by fun_prop
    simpa only [mul_zero] using hc.continuousAt.eventually (gt_mem_nhds (by simpa only [mul_zero] using hd))
  have hnb : ∀ᶠ ε : ℝ in 𝓝 0,
      2*(K*ε)*Q.coordinateBound < 1 ∧ (2*K+1)*ε < Q.clearance y ∧ ε<r ∧
        ∀ j : Fin 3, Q.coordinateBound*ε < Q.basis.coord (j+2) x := by
    filter_upwards [hev (2*K*Q.coordinateBound) 1 (by norm_num),
      hev (2*K+1) _ (hpos y hy),hev 1 r hr,
      Filter.eventually_all.mpr (fun j : Fin 3 => hev Q.coordinateBound _ ((Q.table_iff_coords x).mp hx (j+2)))]
      with ε h₁ h₂ h₃ h₄
    exact ⟨by nlinarith,h₂,by simpa using h₃,h₄⟩
  have hnb' : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      0 < ε ∧ 2*(K*ε)*Q.coordinateBound < 1 ∧ (2*K+1)*ε < Q.clearance y ∧ ε<r ∧
        ∀ j : Fin 3, Q.coordinateBound*ε < Q.basis.coord (j+2) x :=
    (show ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε from self_mem_nhdsWithin).and (hnb.filter_mono nhdsWithin_le_nhds)
  obtain ⟨ε,hε,hsmall,hsafe,her,hcoord⟩ := hnb'.exists
  let R := K*ε
  let A := (2*K+1)*ε
  have hR : Q.safetyFactor*ε < R := by dsimp [R,K]; nlinarith
  have hA : 2*R+ε ≤ A := by dsimp [R,A]; ring_nf; rfl
  have hseg : ∀ z∈segment ℝ x q, A < Q.clearance z := fun z hz => hsafe.trans_le (hmin hz)
  have hseam : Q.safetyFactor*ε < Q.clearance q := by
    have hh := hseg q (right_mem_segment ℝ x q)
    dsimp [A,K] at hh
    nlinarith [Q.safetyFactor_pos]
  have hball : Metric.ball x ε ⊆ Q.table := (Metric.ball_subset_ball her.le).trans hrball
  have hconst := bounded_invariant_spatial_constancy Q hfm hf hb hfx
  have hD := double_ae_slices Q (invariant_smoothing_gradient_zero Q hε hR hsmall hA hfm hf hfx hb)
  filter_upwards [hconst,hD,(measurePreserving_directionParity Q i).quasiMeasurePreserving.ae hconst,
    (measurePreserving_directionParity Q i).quasiMeasurePreserving.ae hD] with c hc hd hrc hrd
  have he (c : DirectionParity)
      (hc : (fun z => f ((z,c.1),c.2)) =ᵐ[(volume Q.table)⁻¹ • volume.restrict Q.table]
        (fun _ => spatialMean Q f c))
      (hd : ∀ᵐ z ∂((volume Q.table)⁻¹ • volume.restrict Q.table), A ≤ Q.clearance z →
        fderiv ℝ (fun w => reflectedSmoothing Q ε f ((w,c.1),c.2)) z=0) :
      reflectedSmoothing Q ε f ((q,c.1),c.2) = spatialMean Q f c := by
    have hsm := reflectedSmoothing_contDiff Q hε (bounded_spatialSlice_integrable Q hfm hb c.1 c.2)
      (fun j => bounded_spatialSlice_integrable Q hfm hb (reflectedDirection Q j c.1) (c.2+1))
    have hdx := smoothing_gradient_zero_on_slice Q hε hfm hb c hd
    have hxy := equal_of_zero_gradient_openSegment hsm (fun z hz => hdx z (hopen hz)
      (hseg z (openSegment_subset_segment ℝ x q hz)))
    rw [← hxy]
    exact reflectedSmoothing_eq_const_of_slice Q hε
      ((Measure.ae_ennreal_smul_measure_iff (by simpa using Q.area_lt_top.ne)).mp hc) hball hcoord
  have hs := (reflectedSmoothing_seam_germ Q hq hε hseam f c.2 c.1).self_of_nhds
  rw [wallReflection_fixed_side Q hq] at hs
  change spatialMean Q f (directionParityReflection Q i c) = spatialMean Q f c
  rw [← he _ hrc hrd,← he _ hc hd]
  exact hs

end TriangularBilliards

namespace TriangularBilliards
open scoped ComplexConjugate
lemma reflectedDirection_pair (Q : Triangle) (i : Fin 3) (v : Circle) :
    reflectedDirection Q (i+2) (reflectedDirection Q i v) =
      Circle.exp (2 * (conj (Q.vertex (i+1)-Q.vertex i) * (Q.vertex (i+2)-Q.vertex i)).arg) * v := by
  let a := Q.vertex (i+1)-Q.vertex i
  let b := Q.vertex (i+2)-Q.vertex i
  have ha : a ≠ 0 := Q.tangent_ne_zero i
  have hb : b ≠ 0 := sub_ne_zero.mpr (Q.nondegenerate.injective.ne (by omega))
  have he : Q.tangent (i+2) = -b := by
    dsimp [Triangle.tangent,b]
    rw [show i+2+1=i by omega]
    abel
  have hw : conj a*b ≠ 0 := mul_ne_zero ((map_ne_zero (starRingEnd ℂ)).mpr ha) hb
  apply Subtype.ext
  change reflect (Q.tangent (i+2)) (reflect (Q.tangent i) (v:ℂ)) = _
  rw [he]
  change reflect (-b) (reflect a (v:ℂ)) = _
  simp only [reflect,Complex.star_def,map_mul,map_div₀,map_neg,RingHomCompTriple.comp_apply,
    RingHom.id_apply,Circle.coe_mul,Circle.coe_exp,Complex.ofReal_mul,Complex.ofReal_ofNat]
  rw [← complex_div_conj_eq_exp_double_arg hw]
  simp only [map_mul,Complex.conj_conj]
  field_simp

end TriangularBilliards

namespace TriangularBilliards
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

lemma angle_irrational_ergodic {a : ℝ} (ha : Irrational (a / Real.pi)) :
    Ergodic (fun x : AddCircle (2*Real.pi) => (2*a : ℝ) + x)
      ((ENNReal.ofReal (2*Real.pi))⁻¹ • volume) := by
  let : IsFiniteMeasure (((ENNReal.ofReal (2*Real.pi))⁻¹) • (volume : Measure (AddCircle (2*Real.pi)))) :=
    Measure.smul_finite volume (ENNReal.inv_ne_top.mpr (by positivity))
  apply ergodic_add_left_of_denseRange_zsmul
  apply AddCircle.denseRange_zsmul_coe_iff.mpr
  convert ha using 1
  field_simp

lemma angular_reflections_constant (Q : Triangle) (hQ : Q.HasIrrationalAngle)
    {g : Circle → ℂ} (hg : StronglyMeasurable g)
    (hi : ∀ i : Fin 3, g ∘ reflectedDirection Q i =ᵐ[angularMeasure] g) :
    ∃ a : ℂ, g =ᵐ[angularMeasure] fun _ => a := by
  obtain ⟨i,hiirr⟩ := hQ
  let a := Q.vertex (i+1)-Q.vertex i
  let b := Q.vertex (i+2)-Q.vertex i
  let θ := (conj a*b).arg
  have ha : a≠0 := Q.tangent_ne_zero i
  have hb : b≠0 := sub_ne_zero.mpr (Q.nondegenerate.injective.ne (by omega))
  have hθ : Irrational (θ/Real.pi) := irrational_arg_of_angle ha hb hiirr
  have hinv : (fun v => g (Circle.exp (2*θ)*v)) =ᵐ[angularMeasure] g := by
    filter_upwards [hi i,(measurePreserving_reflectedDirection Q i).quasiMeasurePreserving.ae (hi (i+2))]
      with v hv hrv
    rw [Function.comp_apply,reflectedDirection_pair] at hrv
    exact hrv.trans hv
  let e := AddCircle.homeomorphCircle'
  have hgm : StronglyMeasurable (g ∘ e) := hg.comp_measurable measurePreserving_toCircle.measurable
  have hie : (g ∘ e) ∘ (fun x : AddCircle (2*Real.pi) => (2*θ : ℝ)+x) =ᵐ[angleMeasure] g ∘ e := by
    filter_upwards [measurePreserving_toCircle.quasiMeasurePreserving.ae hinv] with x hx
    have hadd : e (((2*θ : ℝ) : AddCircle (2*Real.pi))+x) =
        Circle.exp (2*θ)*e x :=
      (Real.Angle.toCircle_add (((2*θ : ℝ) : AddCircle (2*Real.pi))) x).trans
        (congrArg (fun z : Circle => z * e x) (Real.Angle.toCircle_coe (2*θ)))
    change g (e (((2*θ : ℝ) : AddCircle (2*Real.pi))+x)) = g (e x)
    rw [hadd]
    exact hx
  obtain ⟨c,hc⟩ := (angle_irrational_ergodic hθ).ae_eq_const_of_ae_eq_comp_ae hgm.aestronglyMeasurable hie
  refine ⟨c,?_⟩
  rw [← measurePreserving_toCircle.map_eq]
  exact (ae_map_iff measurePreserving_toCircle.measurable.aemeasurable
    (measurableSet_eq_fun hg.measurable measurable_const)).mpr hc

end TriangularBilliards

lemma ae_fst_of_ae_prod {α : Type uAlpha} {β : Type uBeta} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] [NeZero ν] {p : α → Prop}
    (h : ∀ᵐ z ∂μ.prod ν, p z.1) : ∀ᵐ x ∂μ, p x := by
  filter_upwards [Measure.ae_ae_of_ae_prod h] with x hx
  obtain ⟨y,hy⟩ := hx.exists
  exact hy

lemma measure_zero_or_one_of_indicator_constant {α : Type uAlpha} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {A : Set α} {c : ℂ}
    (h : A.indicator (fun _ => (1 : ℂ)) =ᵐ[μ] fun _ => c) :
    μ A=0 ∨ μ A=1 := by
  classical
  obtain ⟨x,hx⟩ := h.exists
  by_cases hxA : x∈A
  · have hc : c=1 := by simpa only [indicator_of_mem hxA] using hx.symm
    right
    have he : A =ᵐ[μ] univ := by
      filter_upwards [h] with y hy
      apply propext
      show (y ∈ A) ↔ (y ∈ univ)
      simp only [mem_univ,iff_true]
      by_contra hn
      rw [indicator_of_notMem hn,hc] at hy
      exact zero_ne_one hy
    rw [measure_congr he,measure_univ]
  · have hc : c=0 := by simpa only [indicator_of_notMem hxA] using hx.symm
    left
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [h] with y hy
    intro hym
    rw [indicator_of_mem hym,hc] at hy
    exact one_ne_zero hy

lemma invariant_indicator {α : Type uAlpha} [MeasurableSpace α]
    (μ : Measure α) (T : α → α) (A : Set α) (h : μ ((T ⁻¹' A) ∆ A)=0) :
    (fun x => A.indicator (fun _ => (1:ℂ)) (T x)) =ᵐ[μ] A.indicator (fun _ => (1:ℂ)) := by
  classical
  filter_upwards [measure_symmDiff_eq_zero_iff.mp h] with x hx
  change (T x∈A) = (x∈A) at hx
  by_cases hm : x∈A
  · have ht : T x∈A := by rwa [hx]
    simp only [indicator_of_mem hm,indicator_of_mem ht]
  · have ht : T x∉A := by rwa [hx]
    simp only [indicator_of_notMem hm,indicator_of_notMem ht]

namespace TriangularBilliards
open Analysis Analytic SpatialSmoothing Filter Set
open scoped Topology

/-- Every bounded measurable invariant of the actual billiard is constant.
Spatial rigidity is proved above on the oriented double; side holonomy now
uses the actual irrational angle, with no Diophantine rate assumption. -/
theorem bounded_billiard_invariant_constant (Q : Triangle) (hQ : Q.HasIrrationalAngle)
    {f : Phase → ℂ} (hfm : StronglyMeasurable f) (hf : MemLp f 2 (phaseMeasure Q))
    {H : ℝ} (hb : ∀ z, ‖f z‖ ≤ H)
    (hinv : ∀ t : ℝ, (fun z => f (billiardFlow Q t z)) =ᵐ[phaseMeasure Q] f) :
    ∃ c : ℂ, f =ᵐ[phaseMeasure Q] fun _ => c := by
  let F : DoublePhase → ℂ := fun z => f z.1
  have hFm : StronglyMeasurable F := hfm.comp_measurable measurable_fst
  have mp : MeasurePreserving (Prod.fst : DoublePhase → Phase) (doubleMeasure Q) (phaseMeasure Q) :=
    measurePreserving_fst
  have hF : MemLp F 2 (doubleMeasure Q) := hf.comp_measurePreserving mp
  have hFi : (geodesicHilbertFlow Q).HasGenerator (hF.toLp F) 0 := by
    apply ((geodesicHilbertFlow Q).hasGenerator_zero_iff _).mpr
    intro t
    apply Lp.ext
    filter_upwards [geodesic_koopman_ae Q t (hF.toLp F),hF.coeFn_toLp,
      (measurePreserving_doubleFlow Q t).quasiMeasurePreserving.ae hF.coeFn_toLp,
      mp.quasiMeasurePreserving.ae (hinv t)] with z hz hfz hftz hiz
    rw [hz,hftz,hfz]
    exact hiz
  let g : Circle → ℂ := fun v => spatialMean Q F (v,0)
  have hgm : StronglyMeasurable g := (spatialMean_stronglyMeasurable Q hFm).comp_measurable
    (measurable_id.prodMk measurable_const)
  have hgmean (c : DirectionParity) : spatialMean Q F c = g c.1 := rfl
  have hgi (i : Fin 3) : g ∘ reflectedDirection Q i =ᵐ[angularMeasure] g := by
    apply ae_fst_of_ae_prod (ν := parityMeasure)
    have hh := spatialMean_reflection_invariant Q hFm hF (fun z => hb z.1) hFi i
    filter_upwards [hh] with z hz
    exact hz
  obtain ⟨c,hgc⟩ := angular_reflections_constant Q hQ hgm hgi
  have hs := bounded_invariant_spatial_constancy Q hFm hF (fun z => hb z.1) hFi
  have hs' : ∀ᵐ v ∂angularMeasure,
      (fun x => f (x,v)) =ᵐ[(volume Q.table)⁻¹ • volume.restrict Q.table] fun _ => g v := by
    apply ae_fst_of_ae_prod (ν := parityMeasure)
    exact hs
  have hh : ∀ᵐ v ∂angularMeasure, ∀ᵐ x ∂((volume Q.table)⁻¹ • volume.restrict Q.table), f (x,v)=c := by
    filter_upwards [hs',hgc] with v hv hvc
    filter_upwards [hv] with x hx
    exact hx.trans hvc
  refine ⟨c,?_⟩
  have hm : MeasurableSet {z : ℂ × Circle | f z=c} := measurableSet_eq_fun hfm.measurable measurable_const
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  exact (Measure.ae_ae_comm (p := fun x v => f (x,v)=c) hm).mpr hh

/-- The invariant-set endpoint, for invariance modulo null sets at every real
(time), on the normalized interior phase space of every irrational triangle. -/
theorem irrational_triangle_invariant_set (Q : Triangle) (hQ : Q.HasIrrationalAngle)
    (A : Set Phase) (hA : MeasurableSet A)
    (hAi : ∀ t : ℝ, phaseMeasure Q (((billiardFlow Q t) ⁻¹' A) ∆ A)=0) :
    phaseMeasure Q A=0 ∨ phaseMeasure Q A=1 := by
  classical
  let f : Phase → ℂ := A.indicator (fun _ => 1)
  have hfm : StronglyMeasurable f := stronglyMeasurable_const.indicator hA
  have hf : MemLp f 2 (phaseMeasure Q) := (memLp_const (1:ℂ)).indicator hA
  have hb (z : Phase) : ‖f z‖ ≤ 1 := by
    by_cases hz : z∈A <;> simp [f,hz]
  obtain ⟨c,hc⟩ := bounded_billiard_invariant_constant Q hQ hfm hf hb
    (fun t => invariant_indicator _ _ _ (hAi t))
  exact measure_zero_or_one_of_indicator_constant hc

/-- Full two-sided billiard ergodicity, including complete regular
chains and the geometric and measure-theoretic guarantees. -/
theorem irrational_triangle_billiard_oai (Q : Triangle) (hQ : Q.HasIrrationalAngle) :
    MainConclusion Q := by
  refine ⟨phaseMeasure_univ Q,ae_exists_chain Q,?_,measurePreserving_billiardFlow Q,
    billiardFlow_cocycle Q,irrational_triangle_invariant_set Q hQ⟩
  intro z c d
  exact FlightChain.unique c d

/-- The same conclusion for the completion of the area-angular measure.
Thus "measurable" may also be read in the Lebesgue-completed sense. -/
theorem irrational_triangle_nullMeasurable_set (Q : Triangle) (hQ : Q.HasIrrationalAngle)
    (A : Set Phase) (hA : NullMeasurableSet A (phaseMeasure Q))
    (hAi : ∀ t : ℝ, phaseMeasure Q (((billiardFlow Q t) ⁻¹' A) ∆ A)=0) :
    phaseMeasure Q A=0 ∨ phaseMeasure Q A=1 := by
  have he : toMeasurable (phaseMeasure Q) A =ᵐ[phaseMeasure Q] A := hA.toMeasurable_ae_eq
  rw [← measure_congr he]
  apply irrational_triangle_invariant_set Q hQ _ (measurableSet_toMeasurable _ _)
  intro t
  apply measure_symmDiff_eq_zero_iff.mpr
  have hpre : (billiardFlow Q t ⁻¹' toMeasurable (phaseMeasure Q) A) =ᵐ[phaseMeasure Q]
      (billiardFlow Q t ⁻¹' A) :=
    (measurePreserving_billiardFlow Q t).quasiMeasurePreserving.ae he
  exact hpre.trans ((measure_symmDiff_eq_zero_iff.mp (hAi t)).trans he.symm)

end TriangularBilliards

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
end

theorem solution : type_of% @OAI.TriangularBilliards.irrational_triangle_billiard_oai := @OAI.TriangularBilliards.irrational_triangle_billiard_oai
