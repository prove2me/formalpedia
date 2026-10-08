-- Prove2me | solution 1 for MonotoneCompStatics.QSMChar.lemma_four_point
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:17:20.353436+00:00
-- url     : https://prove2.me/submissions/55f332d3-6389-4f43-baaf-5875e7871d7e

import Mathlib
import Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn

private theorem bump_strict (K r : ℝ) (hK : 0 ≤ K) :
    StrictMono (fun t : ℝ => t + K * max 0 (t - r)) := by
  intro a b hab
  have hh : max 0 (a - r) ≤ max 0 (b - r) := max_le_max le_rfl (by linarith)
  have := mul_le_mul_of_nonneg_left hh hK
  linarith

private theorem dip_strict (K r : ℝ) (hK : 0 ≤ K) :
    StrictMono (fun t : ℝ => t + K * min 0 (t - r)) := by
  intro a b hab
  have hh : min 0 (a - r) ≤ min 0 (b - r) := min_le_min le_rfl (by linarith)
  have := mul_le_mul_of_nonneg_left hh hK
  linarith

private theorem lift_right (a b c d r : ℝ) (ha : a ≤ r) (hb : b ≤ r) (hc : r < c) :
    ∃ h : ℝ → ℝ, StrictMono h ∧ h a + h b ≤ h c + h d := by
  let V := |a + b - c - d| + 1
  let K := V / (c - r)
  have hV : 0 < V := by dsimp [V]; positivity
  have hK : 0 ≤ K := (div_pos hV (sub_pos.mpr hc)).le
  refine ⟨fun t => t + K * max 0 (t - r), bump_strict K r hK, ?_⟩
  have he : K * (c - r) = V := div_mul_cancel₀ V (sub_ne_zero.mpr hc.ne')
  have hd : 0 ≤ K * max 0 (d - r) := mul_nonneg hK (le_max_left _ _)
  dsimp only
  rw [max_eq_left (by linarith : a - r ≤ 0),
    max_eq_left (by linarith : b - r ≤ 0),
    max_eq_right (by linarith : 0 ≤ c - r), he]
  have := le_abs_self (a + b - c - d)
  dsimp [V] at *
  linarith

private theorem lower_left (a b c d r : ℝ) (ha : a < r) (hc : r ≤ c) (hd : r ≤ d) :
    ∃ h : ℝ → ℝ, StrictMono h ∧ h a + h b ≤ h c + h d := by
  let V := |a + b - c - d| + 1
  let K := V / (r - a)
  have hV : 0 < V := by dsimp [V]; positivity
  have hK : 0 ≤ K := (div_pos hV (sub_pos.mpr ha)).le
  refine ⟨fun t => t + K * min 0 (t - r), dip_strict K r hK, ?_⟩
  have he : K * (a - r) = -V := by
    have hh := div_mul_cancel₀ V (sub_ne_zero.mpr ha.ne')
    change K * (r - a) = V at hh
    nlinarith
  have hb : K * min 0 (b - r) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hK (min_le_left _ _)
  dsimp only
  rw [min_eq_right (by linarith : a - r ≤ 0),
    min_eq_left (by linarith : 0 ≤ c - r),
    min_eq_left (by linarith : 0 ≤ d - r), he]
  have := le_abs_self (a + b - c - d)
  dsimp [V] at *
  linarith

private theorem scalar_ordered (a b c d : ℝ) (hab : a ≤ b)
    (h1 : d ≤ a → b ≤ c) (h2 : d < a → b < c)
    (h3 : d ≤ b → a ≤ c) (h4 : d < b → a < c) :
    ∃ h : ℝ → ℝ, StrictMono h ∧ h a + h b ≤ h c + h d := by
  by_cases hda : d ≤ a
  · by_cases hde : d = a
    · refine ⟨id, strictMono_id, ?_⟩
      simp only [id_eq]
      have := h1 hda
      linarith
    · exact lift_right a b c d b hab le_rfl (h2 (lt_of_le_of_ne hda hde))
  · have had : a < d := lt_of_not_ge hda
    by_cases hbd : b < d
    · obtain ⟨h, hh, he⟩ := lift_right a b d c b hab le_rfl hbd
      exact ⟨h, hh, by linarith⟩
    · have hdb : d ≤ b := le_of_not_gt hbd
      by_cases hde : d = b
      · refine ⟨id, strictMono_id, ?_⟩
        simp only [id_eq]
        have := h3 hdb
        linarith
      · have hac := h4 (lt_of_le_of_ne hdb hde)
        exact lower_left a b c d (min c d) (lt_min hac had) (min_le_left _ _) (min_le_right _ _)

private theorem scalar_transform (a b c d : ℝ)
    (h1 : d ≤ a → b ≤ c) (h2 : d < a → b < c)
    (h3 : d ≤ b → a ≤ c) (h4 : d < b → a < c) :
    ∃ h : ℝ → ℝ, StrictMono h ∧ h a + h b ≤ h c + h d := by
  rcases le_total a b with hab | hba
  · exact scalar_ordered a b c d hab h1 h2 h3 h4
  · obtain ⟨h, hh, he⟩ := scalar_ordered b a c d hba h3 h4 h1 h2
    exact ⟨h, hh, by linarith⟩

namespace MonotoneCompStatics.QSMChar

/-- Lemma (p. 165): a function that is quasisupermodular on the four-point sublattice
`{x, x', x ⊔ x', x ⊓ x'}` becomes supermodular there after some strictly increasing
transformation `h : ℝ → ℝ`. -/
theorem lemma_four_point {X : Type*} [Lattice X] (f : X → ℝ) (x x' : X)
    (hf : MonotoneCompStatics.Monotonicity.QuasiSupermodularOn f {x, x', x ⊔ x', x ⊓ x'}) :
    ∃ h : ℝ → ℝ, StrictMono h ∧
      Supermodularity.Monotonicity.SupermodularOn (h ∘ f) {x, x', x ⊔ x', x ⊓ x'} := by
  have hx : x ∈ ({x, x', x ⊔ x', x ⊓ x'} : Set X) := by simp
  have hx' : x' ∈ ({x, x', x ⊔ x', x ⊓ x'} : Set X) := by simp
  have h1 := hf hx hx'
  have h2 := hf hx' hx
  rw [inf_comm x' x, sup_comm x' x] at h2
  obtain ⟨h, hh, he⟩ := scalar_transform (f x) (f x') (f (x ⊔ x')) (f (x ⊓ x'))
    h1.1 h1.2 h2.1 h2.2
  refine ⟨h, hh, ?_⟩
  have comparable (u v : X) (huv : u ≤ v) :
      h (f u) + h (f v) ≤ h (f (u ⊔ v)) + h (f (u ⊓ v)) := by
    simp [sup_of_le_right huv, inf_of_le_left huv, add_comm]
  have comparable_rev (u v : X) (hvu : v ≤ u) :
      h (f u) + h (f v) ≤ h (f (u ⊔ v)) + h (f (u ⊓ v)) := by
    simp [sup_of_le_left hvu, inf_of_le_right hvu]
  intro u hu v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
  rcases hu with hu | hu | hu | hu <;>
    rcases hv with hv | hv | hv | hv <;>
    subst u <;> subst v <;> simp only [Function.comp_apply] <;>
    first
    | exact he
    | simpa only [sup_comm, inf_comm, add_comm] using he
    | apply comparable; order
    | apply comparable_rev; order


end MonotoneCompStatics.QSMChar

theorem solution {X : Type*} [Lattice X] (f : X → ℝ) (x x' : X)
    (hf : MonotoneCompStatics.Monotonicity.QuasiSupermodularOn f {x, x', x ⊔ x', x ⊓ x'}) :
    ∃ h : ℝ → ℝ, StrictMono h ∧
      Supermodularity.Monotonicity.SupermodularOn (h ∘ f) {x, x', x ⊔ x', x ⊓ x'}  := by
  exact MonotoneCompStatics.QSMChar.lemma_four_point f x x' hf

#print axioms solution
