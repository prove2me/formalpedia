-- Prove2me | solution 1 for MinimaxSLP.ObjSDP.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T01:38:48.573369+00:00
-- url     : https://prove2.me/submissions/bfd418d8-b321-4b09-b271-8776e13be7ee

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjSDP_Model
import Theorems.Thm_MinimaxSLP_ObjSDP_strong_duality
import Theorems.Thm_MinimaxSLP_ObjSDP_dual6_eq_dual8

open MeasureTheory Matrix

namespace MinimaxSLP.ObjSDP.T21Aux

/-- A real `IsGLB` forces nonemptiness. -/
lemma isGLB_nonempty {s : Set ℝ} {a : ℝ} (h : IsGLB s a) : s.Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  subst hne
  have : a + 1 ≤ a := h.2 (by simp)
  linarith

/-- Lower bound from one LMI block: `a μ′w + b ≤ Q · Y + μ′y + y₀`. -/
lemma lmi_lower {d : ℕ} (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (Y : Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ) (y0 a b : ℝ) (w : Fin d → ℝ)
    (hM : (lmiBlock Y y y0 a b w).PosSemidef) :
    a * (μ ⬝ᵥ w) + b ≤ frob Q Y + μ ⬝ᵥ y + y0 := by
  have hY : Y.PosSemidef := by
    have := hM.submatrix (Sum.inl : Fin d → Fin d ⊕ Fin 1)
    have e : (lmiBlock Y y y0 a b w).submatrix Sum.inl Sum.inl = Y := by
      ext i j; simp [lmiBlock, bordered]
    rwa [e] at this
  have h1 := (hA4.posSemidef.hadamard hY).dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))
  have h2 := hM.dotProduct_mulVec_nonneg (Sum.elim μ (fun _ => (1 : ℝ)))
  simp only [star_trivial] at h1 h2
  simp only [dotProduct, mulVec, hadamard, Matrix.sub_apply, vecMulVec_apply, mul_one, one_mul,
    Fintype.sum_sum_type, lmiBlock, bordered, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply, Sum.elim_inl, Sum.elim_inr,
    Finset.univ_unique, Finset.sum_singleton, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h1 h2
  simp only [frob, dotProduct]
  have e1 : ∑ i, ∑ j, (Q i j - μ i * μ j) * Y i j =
      ∑ i, ∑ j, Q i j * Y i j - ∑ i, μ i * ∑ j, Y i j * μ j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have e2 : ∑ i, μ i * (1 / 2 * (y i - a * w i)) =
      (1 / 2) * (∑ i, μ i * y i) - (1 / 2) * a * ∑ i, μ i * w i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have e3 : ∑ j, 1 / 2 * (y j - a * w j) * μ j =
      (1 / 2) * (∑ i, μ i * y i) - (1 / 2) * a * ∑ i, μ i * w i := by
    rw [← e2]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  have e4 : ∑ i, μ i * (∑ j, Y i j * μ j + 1 / 2 * (y i - a * w i)) =
      ∑ i, μ i * ∑ j, Y i j * μ j + ∑ i, μ i * (1 / 2 * (y i - a * w i)) := by
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  rw [e1] at h1
  rw [e4, e2, e3] at h2
  nlinarith [h1, h2]

/-- A linear functional is bounded below on a bounded set. -/
lemma lin_lower {n : ℕ} (S : Set (Fin n → ℝ)) (hS : Bornology.IsBounded S) (g : Fin n → ℝ) :
    ∃ C : ℝ, ∀ x ∈ S, C ≤ g ⬝ᵥ x := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hS
  refine ⟨-∑ i, |g i| * R, fun x hx => ?_⟩
  have hxR := hR x hx
  rw [dotProduct, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hi : |x i| ≤ R := le_trans (by simpa using norm_le_pi_norm x i) hxR
  have := abs_mul (g i) (x i)
  have h3 : |g i * x i| ≤ |g i| * R := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hi (abs_nonneg _)
  linarith [neg_abs_le (g i * x i)]

end MinimaxSLP.ObjSDP.T21Aux

open MinimaxSLP.ObjSDP MinimaxSLP.ObjSDP.T21Aux in
theorem solution {m₁ n r d K : ℕ} [NeZero K]
    (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ) (c : Fin n → ℝ)
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hA1 : (X A b).Nonempty ∧ Bornology.IsBounded (X A b))
    (hrec : ∀ x ∈ X A b, (recourseSet W T h x).Nonempty)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef) :
    IsGLB (firstStageValues A b c W T h α β μ Q) (Z A b c W T h α β μ Q) ∧
    IsGLB (values7 A b c W T h α β μ Q) (ZSDP A b c W T h α β μ Q) ∧
    Z A b c W T h α β μ Q = ZSDP A b c W T h α β μ Q ∧
    ∀ x ∈ X A b, Zx W T h α β μ Q x = ZD8 W T h α β μ Q x := by
  have hSD := fun x (hx : x ∈ X A b) =>
    strong_duality W T h α β hα μ Q hQ hA4 hA3 x (hrec x hx)
  have hD := fun x (hx : x ∈ X A b) => dual6_eq_dual8 W T h α β hα μ Q hA3 x (hrec x hx)
  -- `Z(x)` is the greatest lower bound of the values of (8)
  have hG8 : ∀ x ∈ X A b, IsGLB (dualValues8 W T h α β μ Q x) (Zx W T h α β μ Q x) := by
    intro x hx
    rw [← (hD x hx).1, (hSD x hx).2.2]
    exact (hSD x hx).2.1
  -- the values of (7) are the values `c′x + v`, `x ∈ X`, `v` a value of (8) at `x`
  have hval7 : ∀ t, t ∈ values7 A b c W T h α β μ Q ↔
      ∃ x ∈ X A b, ∃ v ∈ dualValues8 W T h α β μ Q x, t = c ⬝ᵥ x + v := by
    intro t
    constructor
    · rintro ⟨⟨x, Y, y, y0, w⟩, ⟨hk, hAx, hx0⟩, rfl⟩
      refine ⟨x, ⟨hAx, hx0⟩, frob Q Y + μ ⬝ᵥ y + y0, ⟨⟨Y, y, y0, w⟩, hk, rfl⟩, ?_⟩
      simp only; ring
    · rintro ⟨x, ⟨hAx, hx0⟩, v, ⟨⟨Y, y, y0, w⟩, hk, rfl⟩, rfl⟩
      exact ⟨⟨x, Y, y, y0, w⟩, ⟨hk, hAx, hx0⟩, by simp only; ring⟩
  -- uniform lower bound on the values of (7)
  have hbdd7 : BddBelow (values7 A b c W T h α β μ Q) := by
    obtain ⟨π, hπ⟩ := hA3 μ
    set k0 : Fin K := 0
    obtain ⟨C, hC⟩ := lin_lower (X A b) hA1.2 (c - α k0 • (π ᵥ* T))
    refine ⟨C + α k0 * (π ⬝ᵥ h) + β k0, ?_⟩
    rintro t ⟨⟨x, Y, y, y0, w⟩, ⟨hk, hAx, hx0⟩, rfl⟩
    obtain ⟨hM, hWw, hw0⟩ := hk k0
    have hl := lmi_lower μ Q hA4 Y y y0 (α k0) (β k0) (w k0) hM
    have hmw : π ⬝ᵥ h - (π ᵥ* T) ⬝ᵥ x ≤ μ ⬝ᵥ w k0 := by
      have h1 := dotProduct_le_dotProduct_of_nonneg_right hπ hw0
      rw [mulVec_transpose, ← dotProduct_mulVec] at h1
      have hW : W *ᵥ w k0 = h - T *ᵥ x := by rw [← hWw]; abel
      rw [hW, dotProduct_sub, dotProduct_mulVec] at h1
      exact h1
    have hCx := hC x ⟨hAx, hx0⟩
    have hgx : (c - α k0 • (π ᵥ* T)) ⬝ᵥ x = c ⬝ᵥ x - α k0 * ((π ᵥ* T) ⬝ᵥ x) := by
      rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
    have hαμ := mul_le_mul_of_nonneg_left hmw (hα k0)
    simp only
    nlinarith
  -- equality of lower-bound sets
  have hlb : lowerBounds (values7 A b c W T h α β μ Q) =
      lowerBounds (firstStageValues A b c W T h α β μ Q) := by
    ext ℓ
    constructor
    · rintro hℓ t ⟨x, hx, rfl⟩
      have : ℓ - c ⬝ᵥ x ∈ lowerBounds (dualValues8 W T h α β μ Q x) := by
        intro v hv
        have := hℓ ((hval7 _).2 ⟨x, hx, v, hv, rfl⟩)
        linarith
      have := (hG8 x hx).2 this
      linarith
    · intro hℓ t ht
      obtain ⟨x, hx, v, hv, rfl⟩ := (hval7 t).1 ht
      have h1 := (hG8 x hx).1 hv
      have h2 := hℓ ⟨x, hx, rfl⟩
      linarith
  obtain ⟨x0, hx0⟩ := hA1.1
  obtain ⟨v0, hv0⟩ := isGLB_nonempty (hG8 x0 hx0)
  have hne7 : (values7 A b c W T h α β μ Q).Nonempty :=
    ⟨_, (hval7 _).2 ⟨x0, hx0, v0, hv0, rfl⟩⟩
  have hneF : (firstStageValues A b c W T h α β μ Q).Nonempty := ⟨_, x0, hx0, rfl⟩
  have hbddF : BddBelow (firstStageValues A b c W T h α β μ Q) := by
    obtain ⟨L, hL⟩ := hbdd7
    exact ⟨L, hlb ▸ hL⟩
  have hG7 : IsGLB (values7 A b c W T h α β μ Q) (ZSDP A b c W T h α β μ Q) :=
    Real.isGLB_sInf hne7 hbdd7
  have hGF : IsGLB (firstStageValues A b c W T h α β μ Q) (Z A b c W T h α β μ Q) :=
    Real.isGLB_sInf hneF hbddF
  have hGF' : IsGLB (firstStageValues A b c W T h α β μ Q) (ZSDP A b c W T h α β μ Q) := by
    unfold IsGLB; rw [← hlb]; exact hG7
  refine ⟨hGF, hG7, hGF.unique hGF', fun x hx => ?_⟩
  rw [(hSD x hx).2.2, (hD x hx).2]
