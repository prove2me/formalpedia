-- Prove2me | solution 1 for Grunbaum2003.exists_small_apex_from_support_vertex_barycenter
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:45:31.391822+00:00
-- url     : https://prove2.me/submissions/f9284651-a0ed-4c05-8a11-5574a1d28dd0

import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
open scoped Classical BigOperators

private lemma finite_strict_perturbation {d m : ℕ}
    (ψ : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin m → ℝ)
    (w u : Fin d → ℝ) (hw : ∀ i, ψ i w < c i) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ ∀ i, ψ i (w + t • u) < c i := by
  let r : Fin m → ℝ := fun i => |ψ i u| / (c i - ψ i w)
  let B : ℝ := ∑ i, r i
  have hr : ∀ i, 0 ≤ r i := fun i => div_nonneg (abs_nonneg _) (sub_pos.mpr (hw i)).le
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => hr i)
  have hden : 0 < 1 + B := by linarith
  let t : ℝ := 1 / (1 + B)
  have ht : 0 < t := div_pos zero_lt_one hden
  have ht1 : t ≤ 1 := by
    dsimp [t]
    exact (div_le_one hden).2 (by linarith)
  have htden : t * (1 + B) = 1 := by
    dsimp [t]
    exact div_mul_cancel₀ _ (ne_of_gt hden)
  refine ⟨t, ht, ht1, fun i => ?_⟩
  have hri : r i ≤ B := Finset.single_le_sum (fun j _ => hr j) (Finset.mem_univ i)
  have hsmall : t * r i < 1 := by
    calc
      t * r i < t * (1 + B) := mul_lt_mul_of_pos_left (by linarith) ht
      _ = 1 := htden
  have hδ : 0 < c i - ψ i w := sub_pos.mpr (hw i)
  have hratio : t * |ψ i u| / (c i - ψ i w) < 1 := by
    simpa only [r, mul_div_assoc] using hsmall
  have hgap : t * |ψ i u| < c i - ψ i w := (div_lt_one hδ).1 hratio
  have hslope := mul_le_mul_of_nonneg_left (le_abs_self (ψ i u)) ht.le
  rw [map_add, map_smul, smul_eq_mul]
  linarith

/-- A point can move strictly beyond one support plane while remaining strictly
beneath any given finite family of other support planes. -/
private theorem small_apex {d m : ℕ} {P : Set (Fin d → ℝ)}
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (w z : Fin d → ℝ)
    (hbound : ∀ x ∈ P, φ x ≤ φ w) (hz : φ z < φ w)
    (ψ : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hw : ∀ i, ψ i w < c i) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      φ w < φ (w + t • (w - z)) ∧
      w + t • (w - z) ∉ P ∧
      ∀ i, ψ i (w + t • (w - z)) < c i := by
  obtain ⟨t, ht, ht1, hplanes⟩ := finite_strict_perturbation ψ c w (w - z) hw
  have habove : φ w < φ (w + t • (w - z)) := by
    rw [map_add, map_smul, map_sub, smul_eq_mul]
    nlinarith [mul_pos ht (sub_pos.mpr hz)]
  exact ⟨t, ht, ht1, habove, fun h => (not_le_of_gt habove) (hbound _ h), hplanes⟩

/-- The barycenter of the selected support vertices admits an exterior
perturbation beneath every other finite support plane that does not contain
all of those vertices. -/
theorem solution {d m : ℕ} (hd : 0 < d) {P : Set (Fin d → ℝ)}
    (hP : Convex ℝ P) (v : Fin d → Fin d → ℝ) (hvP : ∀ i, v i ∈ P)
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (hbound : ∀ x ∈ P, φ x ≤ a) (hlevel : ∀ i, φ (v i) = a)
    (z : Fin d → ℝ) (hz : φ z < a)
    (ψ : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hother : ∀ j, (∀ i, ψ j (v i) ≤ c j) ∧ ∃ i, ψ j (v i) < c j) :
    let w : Fin d → ℝ := (d : ℝ)⁻¹ • ∑ i, v i
    w ∈ P ∧ φ w = a ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
        a < φ (w + t • (w - z)) ∧
        w + t • (w - z) ∉ P ∧
        ∀ j, ψ j (w + t • (w - z)) < c j := by
  intro w
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  have hwP : w ∈ P := by
    have hmass := hP.centerMass_mem (t := Finset.univ) (w := fun _ : Fin d => (1 : ℝ))
      (z := v) (fun _ _ => zero_le_one) (by simpa using hdpos) (fun i _ => hvP i)
    simpa [Finset.centerMass] using hmass
  have hφw : φ w = a := by
    dsimp [w]
    rw [map_smul, map_sum]
    simp [hlevel, smul_eq_mul, hdne]
  have hplanes : ∀ j, ψ j w < c j := by
    intro j
    have hsum : (∑ i, ψ j (v i)) < (d : ℝ) * c j := by
      calc
        (∑ i, ψ j (v i)) < ∑ _i : Fin d, c j := by
          obtain ⟨i, hi⟩ := (hother j).2
          exact Finset.sum_lt_sum (fun i _ => (hother j).1 i) ⟨i, Finset.mem_univ i, hi⟩
        _ = (d : ℝ) * c j := by simp
    calc
      ψ j w = (d : ℝ)⁻¹ * ∑ i, ψ j (v i) := by
        dsimp [w]
        rw [map_smul, map_sum, smul_eq_mul]
      _ < (d : ℝ)⁻¹ * ((d : ℝ) * c j) :=
        mul_lt_mul_of_pos_left hsum (inv_pos.mpr hdpos)
      _ = c j := by rw [← mul_assoc, inv_mul_cancel₀ hdne, one_mul]
  refine ⟨hwP, hφw, ?_⟩
  have hbound' : ∀ x ∈ P, φ x ≤ φ w := by simpa [hφw] using hbound
  have hz' : φ z < φ w := by simpa [hφw] using hz
  obtain ⟨t, ht, ht1, hφ, hout, hrest⟩ := small_apex φ w z hbound' hz' ψ c hplanes
  exact ⟨t, ht, ht1, hφw ▸ hφ, hout, hrest⟩
