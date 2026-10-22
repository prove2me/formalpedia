-- Prove2me | solution 2 for ModernConvex.Truss.quadratic_form_minimum
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:32:20.534655+00:00
-- url     : https://prove2.me/submissions/31a0b670-1061-4fd1-9cd8-8a84b6757c0a

import Mathlib
set_option autoImplicit false
open Matrix

theorem solution {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef)
    (b : Fin m → ℝ) :
    let Q : (Fin m → ℝ) → ℝ := fun v => (1 / 2 : ℝ) * (v ⬝ᵥ (A *ᵥ v)) - b ⬝ᵥ v
    (BddBelow (Set.range Q) ↔ ∃ v₀, ∀ v, Q v₀ ≤ Q v) ∧
    ((∃ v₀, ∀ v, Q v₀ ≤ Q v) ↔ ∃ v, A *ᵥ v = b) ∧
    ((∃ v, A *ᵥ v = b) → ∀ v₀, (∀ v, Q v₀ ≤ Q v) ↔ A *ᵥ v₀ = b) ∧
    (∀ v₀, (∀ v, Q v₀ ≤ Q v) → ∀ v, A *ᵥ v = b → Q v₀ = -((1 / 2 : ℝ) * (b ⬝ᵥ v))) := by
  intro Q
  have hT : Aᵀ = A := by
    have := hA.isHermitian.eq
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hsym : ∀ x y : Fin m → ℝ, x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
    intro x y
    rw [Matrix.dotProduct_mulVec]
    conv_lhs => rw [← hT, Matrix.vecMul_transpose]
    rw [dotProduct_comm]
  have hnn : ∀ x : Fin m → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x) := by
    intro x
    simpa using hA.dotProduct_mulVec_nonneg x
  -- difference formula at a solution
  have hdiff : ∀ v w : Fin m → ℝ, A *ᵥ v = b → Q w - Q v = (1/2 : ℝ) * ((w - v) ⬝ᵥ (A *ᵥ (w - v))) := by
    intro v w hv
    have e1 : b ⬝ᵥ w = w ⬝ᵥ (A *ᵥ v) := by rw [hv, dotProduct_comm]
    have e2 : b ⬝ᵥ v = v ⬝ᵥ (A *ᵥ v) := by rw [hv, dotProduct_comm]
    have e3 : (w - v) ⬝ᵥ (A *ᵥ (w - v)) = w ⬝ᵥ (A *ᵥ w) - 2 * (w ⬝ᵥ (A *ᵥ v)) + v ⬝ᵥ (A *ᵥ v) := by
      simp only [mulVec_sub, dotProduct_sub, sub_dotProduct]
      rw [hsym v w]; ring
    simp only [Q]
    rw [e3, e1, e2]; ring
  have hmin_of_sol : ∀ v, A *ᵥ v = b → ∀ w, Q v ≤ Q w := by
    intro v hv w
    have := hdiff v w hv
    have := hnn (w - v)
    linarith
  -- minimizer implies solution
  have hsol_of_min : ∀ v₀, (∀ v, Q v₀ ≤ Q v) → A *ᵥ v₀ = b := by
    intro v₀ hv₀
    set r : Fin m → ℝ := A *ᵥ v₀ - b with hr
    set d : ℝ := r ⬝ᵥ r with hd
    set c : ℝ := r ⬝ᵥ (A *ᵥ r) with hc
    have hc0 : 0 ≤ c := hnn r
    have hexp : ∀ t : ℝ, Q (v₀ + t • r) - Q v₀ = t * d + t ^ 2 * c / 2 := by
      intro t
      have e : (v₀ + t • r) ⬝ᵥ (A *ᵥ (v₀ + t • r)) =
          v₀ ⬝ᵥ (A *ᵥ v₀) + 2 * t * (r ⬝ᵥ (A *ᵥ v₀)) + t ^ 2 * c := by
        simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
          smul_dotProduct, smul_eq_mul]
        rw [hsym v₀ r]; simp only [hc]; ring
      have e' : b ⬝ᵥ (v₀ + t • r) = b ⬝ᵥ v₀ + t * (b ⬝ᵥ r) := by
        simp [dotProduct_add, dotProduct_smul]
      have e'' : d = r ⬝ᵥ (A *ᵥ v₀) - b ⬝ᵥ r := by
        have : d = r ⬝ᵥ (A *ᵥ v₀ - b) := rfl
        rw [this, dotProduct_sub, dotProduct_comm r b]
      simp only [Q]
      rw [e, e']
      rw [e'']
      ring
    by_contra hne
    have hd0 : 0 < d := by
      have : r ≠ 0 := fun h0 => hne (by
        have : A *ᵥ v₀ - b = 0 := h0
        exact sub_eq_zero.mp this)
      have h0 : 0 ≤ r ⬝ᵥ r := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
      rcases lt_or_eq_of_le h0 with h | h
      · exact h
      · exact absurd (dotProduct_self_eq_zero.mp h.symm) this
    have h1 := hv₀ (v₀ + (-d / (c + 1)) • r)
    have h2 := hexp (-d / (c + 1))
    have hc1 : 0 < c + 1 := by linarith
    have : (-d / (c + 1)) * d + (-d / (c + 1)) ^ 2 * c / 2 < 0 := by
      have : (-d / (c + 1)) * d + (-d / (c + 1)) ^ 2 * c / 2 = -(d ^ 2 / (c + 1)) * (1 - c / (2 * (c + 1))) := by
        field_simp; ring
      rw [this]
      have : 0 < d ^ 2 / (c + 1) := by positivity
      have : c / (2 * (c + 1)) < 1 := by rw [div_lt_one (by positivity)]; linarith
      nlinarith
    linarith
  have hunb : (¬ ∃ v, A *ᵥ v = b) → ¬ BddBelow (Set.range Q) := by
    intro hns hbdd
    have hnm : b ∉ LinearMap.range (Matrix.mulVecLin A) := by
      rintro ⟨v, hv⟩
      exact hns ⟨v, by simpa using hv⟩
    obtain ⟨f, hfb, hfp⟩ := Submodule.exists_le_ker_of_notMem hnm
    set w : Fin m → ℝ := fun i => f (Pi.single i 1) with hw
    have hfx : ∀ x, f x = w ⬝ᵥ x := by
      intro x
      rw [LinearMap.pi_apply_eq_sum_univ f x]
      simp only [dotProduct, hw, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : (fun j : Fin m => if i = j then (1:ℝ) else 0) = Pi.single i 1 := by
        ext j; simp [Pi.single_apply, eq_comm]
      rw [this]; ring
    have hfA : ∀ x, w ⬝ᵥ (A *ᵥ x) = 0 := by
      intro x
      have : A *ᵥ x ∈ LinearMap.ker f := hfp ⟨x, by simp⟩
      rw [← hfx]; exact this
    have hAw : A *ᵥ w = 0 := by
      have h0 : (A *ᵥ w) ⬝ᵥ (A *ᵥ w) = 0 := by
        rw [dotProduct_comm, hsym, hfA]
      exact dotProduct_self_eq_zero.mp h0
    have hk : b ⬝ᵥ w ≠ 0 := by
      rw [dotProduct_comm, ← hfx]; exact hfb
    obtain ⟨L, hL⟩ := hbdd
    set k := b ⬝ᵥ w with hkdef
    have hQ : ∀ s : ℝ, Q (s • w) = -(s * k) := by
      intro s
      simp only [Q, mulVec_smul, dotProduct_smul, smul_dotProduct, hAw, dotProduct_zero, smul_eq_mul]
      simp [hkdef]
    have := hL ⟨((|L| + 1) / k) • w, rfl⟩
    rw [hQ] at this
    have e : -((|L| + 1) / k * k) = -(|L| + 1) := by field_simp
    rw [e] at this
    have := neg_abs_le L
    linarith [abs_nonneg L]
  refine ⟨⟨fun hb => ?_, fun ⟨v₀, hv₀⟩ => ⟨Q v₀, by rintro _ ⟨v, rfl⟩; exact hv₀ v⟩⟩,
    ⟨fun ⟨v₀, hv₀⟩ => ⟨v₀, hsol_of_min v₀ hv₀⟩, fun ⟨v, hv⟩ => ⟨v, hmin_of_sol v hv⟩⟩,
    fun _ v₀ => ⟨hsol_of_min v₀, fun h => hmin_of_sol v₀ h⟩, ?_⟩
  · by_contra hne
    have : ∃ v, A *ᵥ v = b := by
      by_contra hns
      exact hunb hns hb
    obtain ⟨v, hv⟩ := this
    exact hne ⟨v, hmin_of_sol v hv⟩
  · intro v₀ hv₀ v hv
    have h1 := hv₀ v
    have h2 := hmin_of_sol v hv v₀
    have : Q v = -((1 / 2 : ℝ) * (b ⬝ᵥ v)) := by
      simp only [Q, hv]
      rw [dotProduct_comm v b]; ring
    linarith
