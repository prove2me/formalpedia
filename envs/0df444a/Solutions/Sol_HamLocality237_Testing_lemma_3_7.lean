-- Prove2me | solution 1 for HamLocality237.Testing.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T05:14:12.709719+00:00
-- url     : https://prove2.me/submissions/43b4ba8d-6580-4a5d-9f1a-3928188010da

import Definitions.Def_HamLocality237_Testing_Adversary
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace HamLocality237.Testing

lemma sub_form {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : H →L[ℂ] H) (c : ℝ) (a u : H) :
    ‖a + R u‖ ^ 2 - c * ‖u‖ ^ 2 = ‖a‖ ^ 2 + 2 * (inner ℂ (R.adjoint a) u).re
      - (inner ℂ u (((c:ℂ) • 1 - R.adjoint * R) u)).re := by
  have h1 : ‖a + R u‖ ^ 2 = ‖a‖ ^ 2 + 2 * (inner ℂ a (R u)).re + ‖R u‖ ^ 2 := norm_add_sq (𝕜 := ℂ) a (R u)
  have h2 : (inner ℂ a (R u)) = inner ℂ (R.adjoint a) u := by
    rw [ContinuousLinearMap.adjoint_inner_left]
  have h3 : (inner ℂ u (((c:ℂ) • 1 - R.adjoint * R) u)).re = c * ‖u‖ ^ 2 - ‖R u‖ ^ 2 := by
    have : (((c:ℂ) • 1 - R.adjoint * R) u) = (c:ℂ) • u - R.adjoint (R u) := by simp
    rw [this, inner_sub_right, inner_smul_right, ContinuousLinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  rw [h1, h2, h3]; ring

lemma key {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (O : E →L[ℂ] H) (R : H →L[ℂ] H) (c : ℝ) (hc : ‖R‖ ^ 2 ≤ c) (B : H →L[ℂ] H)
    (hPB : ((c:ℂ) • 1 - R.adjoint * R) * B = 1) (r : E) :
    IsGreatest (Set.range (fun u : H => ‖O r + R u‖ ^ 2 - c * ‖u‖ ^ 2))
      (inner ℂ r ((O.adjoint ∘L O + O.adjoint ∘L R ∘L B ∘L R.adjoint ∘L O) r)).re := by
  set a := O r with ha
  set w := R.adjoint a with hw
  set P : H →L[ℂ] H := (c:ℂ) • 1 - R.adjoint * R with hP
  have hval : (inner ℂ r ((O.adjoint ∘L O + O.adjoint ∘L R ∘L B ∘L R.adjoint ∘L O) r)).re
      = ‖a‖ ^ 2 + (inner ℂ w (B w)).re := by
    have e1 : inner ℂ r (O.adjoint (O r)) = inner ℂ a a := by
      rw [ContinuousLinearMap.adjoint_inner_right]
    have e2 : inner ℂ r (O.adjoint (R (B (R.adjoint (O r))))) = inner ℂ w (B w) := by
      rw [ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.adjoint_inner_left]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, inner_add_right]
    rw [e1, e2]
    simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
  have hform : ∀ d : H, (inner ℂ d (P d)).re = c * ‖d‖ ^ 2 - ‖R d‖ ^ 2 := by
    intro d
    have : (P d) = (c:ℂ) • d - R.adjoint (R d) := by simp [hP]
    rw [this, inner_sub_right, inner_smul_right, ContinuousLinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have hnn : ∀ d : H, 0 ≤ (inner ℂ d (P d)).re := by
    intro d
    rw [hform]
    have h0 : ‖R d‖ ≤ ‖R‖ * ‖d‖ := R.le_opNorm d
    have h4 : ‖R d‖ ^ 2 ≤ (‖R‖ * ‖d‖) ^ 2 := by gcongr
    nlinarith [mul_pow ‖R‖ ‖d‖ 2, mul_le_mul_of_nonneg_right hc (sq_nonneg ‖d‖)]
  have hsym : ∀ x y : H, inner ℂ x (P y) = inner ℂ (P x) y := by
    intro x y
    have e1 : P y = (c:ℂ) • y - R.adjoint (R y) := by simp [hP]
    have e2 : P x = (c:ℂ) • x - R.adjoint (R x) := by simp [hP]
    rw [e1, e2, inner_sub_right, inner_sub_left, inner_smul_right, inner_smul_left,
      ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_left]
    simp [Complex.conj_ofReal]
  have hPu : P (B w) = w := by
    have := congrArg (fun T => T w) hPB
    simpa using this
  have hf : ∀ u : H, ‖a + R u‖ ^ 2 - c * ‖u‖ ^ 2
      = ‖a‖ ^ 2 + (inner ℂ w (B w)).re - (inner ℂ (u - B w) (P (u - B w))).re := by
    intro u
    rw [sub_form R c a u]
    have h5 : inner ℂ (B w) (P u) = inner ℂ w u := by
      rw [hsym, hPu]
    have : (inner ℂ (u - B w) (P (u - B w))) = inner ℂ u (P u) - inner ℂ u w
        - inner ℂ (B w) (P u) + inner ℂ (B w) w := by
      rw [map_sub, hPu, inner_sub_left, inner_sub_right, inner_sub_right]
      ring
    rw [this, h5]
    have h6 : (inner ℂ (B w) w).re = (inner ℂ w (B w)).re := by rw [← inner_conj_symm w (B w)]; exact Complex.conj_re _
    have h7 : (inner ℂ u w).re = (inner ℂ w u).re := by rw [← inner_conj_symm u w]; exact Complex.conj_re _
    simp only [Complex.sub_re, Complex.add_re]
    rw [h6, h7]; ring
  rw [hval]
  refine ⟨⟨B w, ?_⟩, ?_⟩
  · simp only
    rw [hf, sub_self, inner_zero_left]; simp
  · rintro _ ⟨u, rfl⟩
    simp only
    rw [hf]
    linarith [hnn (u - B w)]

lemma penalty_inv {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : H →L[ℂ] H) (c : ℝ) (hc : ‖R‖ ^ 2 < c) :
    ∃ B : H →L[ℂ] H, B * ((c:ℂ) • 1 - R.adjoint * R) = 1 ∧
      ((c:ℂ) • 1 - R.adjoint * R) * B = 1 := by
  have hc0 : 0 < c := lt_of_le_of_lt (sq_nonneg _) hc
  set T := R.adjoint * R with hT
  have hTn : ‖T‖ ≤ ‖R‖ ^ 2 := by
    calc ‖T‖ ≤ ‖R.adjoint‖ * ‖R‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖R‖ ^ 2 := by rw [ContinuousLinearMap.adjoint.norm_map]; ring
  have h1 : ‖((c⁻¹ : ℝ) : ℂ) • T‖ < 1 := by
    rw [norm_smul]
    simp only [Complex.norm_real, norm_inv, Real.norm_eq_abs, abs_of_pos hc0]
    rw [inv_mul_lt_iff₀ hc0]
    linarith
  set u := Units.oneSub (((c⁻¹ : ℝ) : ℂ) • T) h1 with hu
  have hcne : (c:ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
  have hP : ((c:ℂ) • 1 - T) = (c:ℂ) • ((u : H →L[ℂ] H)) := by
    simp only [hu, Units.val_oneSub, smul_sub, smul_smul]
    simp [hcne]
  refine ⟨((c⁻¹ : ℝ) : ℂ) • ((u⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H), ?_, ?_⟩
  · rw [hP, smul_mul_smul_comm]
    have : ((c⁻¹ : ℝ) : ℂ) * (c:ℂ) = 1 := by push_cast; field_simp
    rw [this, one_smul]; exact u.inv_mul
  · rw [hP, smul_mul_smul_comm]
    have : (c:ℂ) * ((c⁻¹ : ℝ) : ℂ) = 1 := by push_cast; field_simp
    rw [this, one_smul]; exact u.mul_inv


end HamLocality237.Testing

open HamLocality237.Testing in
theorem solution (r : BandSpace) :
    IsGreatest (Set.range (fun u : HalfLineSpace =>
      ‖observationOperator r + responseOperator u‖ ^ 2 - etaSquared * ‖u‖ ^ 2))
      (inner ℂ r (bandCorrection r)).re := by
  have hlt : ‖responseOperator‖ ^ 2 < etaSquared := by unfold etaSquared; linarith
  obtain ⟨B, hB1, hB2⟩ := penalty_inv responseOperator etaSquared hlt
  have hex : ∃ B : HalfLineSpace →L[ℂ] HalfLineSpace,
      B * penaltyOperator = 1 ∧ penaltyOperator * B = 1 := ⟨B, hB1, hB2⟩
  have hinv : penaltyOperator * penaltyInverse = 1 := by
    unfold penaltyInverse; rw [dif_pos hex]; exact hex.choose_spec.2
  exact key observationOperator responseOperator etaSquared hlt.le penaltyInverse hinv r

