-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOSEnergy.certificate_sq_gap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:01:11.435571+00:00
-- url     : https://prove2.me/submissions/3ca04ba5-bd49-4c8a-8e43-bcb9193b4a72

import Mathlib
import Definitions.Def_OAIQ019N016
import Definitions.Def_OAIQ019N026

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower.SOSEnergy
variable {Γ H : Type*} [Group Γ] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]

theorem energy_nonneg (S : Finset Γ) (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    0 ≤ energy S ρ x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Telescoping a word uses only the unitary relations and the specified generators. -/
theorem word_norm_bound (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (x : H) (r : ℝ)
    (w : List Γ) (hw : ∀ s ∈ w, ‖ρ s x - x‖ ≤ r) :
    ‖ρ w.prod x - x‖ ≤ w.length * r := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have ha := hw a (by simp)
    have ht := ih (fun s hs => hw s (by simp [hs]))
    have he : ρ (a * w.prod) x - x =
        ρ a (ρ w.prod x - x) + (ρ a x - x) := by
      rw [map_mul]
      change ρ a (ρ w.prod x) - x = _
      rw [map_sub]
      abel
    simp only [List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [he]
    calc
      _ ≤ ‖ρ a (ρ w.prod x - x)‖ + ‖ρ a x - x‖ := norm_add_le _ _
      _ = ‖ρ w.prod x - x‖ + ‖ρ a x - x‖ := by rw [(ρ a).norm_map]
      _ ≤ w.length * r + r := add_le_add ht ha
      _ = _ := by ring

/-- A length-at-most-four word has energy bounded by sixteen times the generator energy. -/
theorem word_sq_bound (S : Finset Γ) (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (x : H)
    (w : List Γ) (hw : ∀ s ∈ w, s ∈ S) (hlen : w.length ≤ 4) :
    ‖ρ w.prod x - x‖ ^ 2 ≤ 16 * energy S ρ x := by
  have he := energy_nonneg S ρ x
  have hb : ∀ s ∈ w, ‖ρ s x - x‖ ≤ Real.sqrt (energy S ρ x) := by
    intro s hs
    apply (Real.le_sqrt (norm_nonneg _) he).mpr
    exact Finset.single_le_sum (fun t _ => sq_nonneg ‖ρ t x - x‖) (hw s hs)
  have hn := word_norm_bound ρ x _ w hb
  have h4 : (w.length : ℝ) ≤ 4 := by exact_mod_cast hlen
  have hn' : ‖ρ w.prod x - x‖ ≤ 4 * Real.sqrt (energy S ρ x) :=
    hn.trans (mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg _))
  nlinarith [Real.sq_sqrt he, norm_nonneg (ρ w.prod x - x), Real.sqrt_nonneg (energy S ρ x)]

/-- The exact real quadratic form of a unitary displacement. -/
theorem real_inner_unitary (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (g : Γ) (x : H) :
    (inner ℂ x (ρ g x)).re = ‖x‖ ^ 2 - ‖ρ g x - x‖ ^ 2 / 2 := by
  have h := norm_sub_sq (𝕜 := ℂ) (ρ g x) x
  rw [(ρ g).norm_map, inner_re_symm] at h
  change ‖ρ g x - x‖ ^ 2 = ‖x‖ ^ 2 - 2 * (inner ℂ x (ρ g x)).re + ‖x‖ ^ 2 at h
  linarith

theorem polyVector_real_inner (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (x : H) (p : List (Γ × ℤ)) :
    (inner ℂ x (polyVector ρ x p)).re =
      ((p.map Prod.snd).sum : ℤ) * ‖x‖ ^ 2 -
        (p.map (fun a => (a.2 : ℝ) * ‖ρ a.1 x - x‖ ^ 2)).sum / 2 := by
  induction p with
  | nil => simp [polyVector]
  | cons a p ih =>
    have hz : (inner ℂ x (a.2 • ρ a.1 x)).re =
        (a.2 : ℝ) * (inner ℂ x (ρ a.1 x)).re := by
      change reInnerAdd x (a.2 • ρ a.1 x) = _
      rw [map_zsmul, zsmul_eq_mul]
      rfl
    simp only [polyVector, List.map_cons, List.sum_cons, inner_add_right,
      Complex.add_re] at ih ⊢
    rw [hz, ih, real_inner_unitary]
    push_cast
    ring

/-- An integer coefficient may have either sign; absolute coefficients suffice. -/
theorem weighted_displacement_le (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (x : H)
    (p : List (Γ × ℤ)) (M : ℝ)
    (hb : ∀ a ∈ p, ‖ρ a.1 x - x‖ ^ 2 ≤ M) :
    (p.map (fun a => (a.2 : ℝ) * ‖ρ a.1 x - x‖ ^ 2)).sum ≤
      ((p.map (fun a => |a.2|)).sum : ℤ) * M := by
  induction p with
  | nil => simp
  | cons a p ih =>
    have ht := ih (fun b h => hb b (by simp [h]))
    have h1 : (a.2 : ℝ) * ‖ρ a.1 x - x‖ ^ 2 ≤ |(a.2 : ℝ)| * M :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hb a (by simp)) (abs_nonneg _))
    simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_abs]
    nlinarith

/-- Exact augmentation zero converts a short supported residual into an energy error.
The constant eight here combines the squared word bound 16 with the factor 1/2. -/
theorem residual_lower (S : Finset Γ) (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (x : H)
    (p : List (Γ × ℤ)) (haug : (p.map Prod.snd).sum = 0)
    (hsupp : ∀ a ∈ p, ∃ w : List Γ, w.prod = a.1 ∧ w.length ≤ 4 ∧ ∀ s ∈ w, s ∈ S) :
    -(8 * ((p.map (fun a => |a.2|)).sum : ℤ) * energy S ρ x) ≤
      (inner ℂ x (polyVector ρ x p)).re := by
  have hb := weighted_displacement_le ρ x p (16 * energy S ρ x) (by
    intro a ha
    rcases hsupp a ha with ⟨w, hprod, hlen, hw⟩
    rw [← hprod]
    exact word_sq_bound S ρ x w hw hlen)
  rw [polyVector_real_inner, haug, Int.cast_zero, zero_mul, zero_sub]
  nlinarith

end NuclearUltrapower.SOSEnergy

noncomputable section
open scoped InnerProductSpace ComplexOrder

namespace NuclearUltrapower.SOSEnergy
open scoped ComplexOrder
variable {Γ H : Type*} [Group Γ] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem polyOperator_apply (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (p : List (Γ × ℤ)) (x : H) :
    polyOperator ρ p x = polyVector ρ x p := by
  induction p with
  | nil => simp [polyOperator, polyVector]
  | cons a p ih => simpa only [polyOperator, polyVector, List.map_cons, List.sum_cons,
      add_apply, smul_apply, LinearIsometryEquiv.coe_coe''] using (congrArg (fun y : H => a.2 • ρ a.1 x + y) ih)

/-- The rational certificate's defect absorption, with its exact denominator and
certified l1 size. The support/augmentation premises will be discharged by the
matrix-labelled reflection certificate, never assumed of the main group. -/
theorem certificate_sq_gap_oai (S : Finset Γ) (ρ : Γ →* (H ≃ₗᵢ[ℂ] H))
    (D Q : H →L[ℂ] H) (p : List (Γ × ℤ))
    (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (henergy : ∀ x, (inner ℂ x (D x)).re = energy S ρ x / 2)
    (haug : (p.map Prod.snd).sum = 0)
    (hl1 : (p.map (fun a => |a.2|)).sum = 29562852800)
    (hsupp : ∀ a ∈ p, ∃ w : List Γ, w.prod = a.1 ∧ w.length ≤ 4 ∧ ∀ s ∈ w, s ∈ S)
    (hcert : (10000000000000 : ℝ) • (D*D) - (1000000000000 : ℝ) • D =
      Q + polyOperator ρ p) : (1 / 20 : ℝ) • D ≤ D*D := by
  have hself := IsSelfAdjoint.of_nonneg hD
  have hsq : IsSelfAdjoint (D*D) := by simpa only [pow_two] using hself.pow 2
  have hs : IsSelfAdjoint (D*D - (1/20 : ℝ) • D) :=
    hsq.sub ((IsSelfAdjoint.all (1/20 : ℝ)).smul hself)
  apply (ContinuousLinearMap.le_def _ _).mpr
  refine ⟨hs.isSymmetric, ?_⟩
  intro x
  have hr := residual_lower S ρ x p haug hsupp
  rw [hl1] at hr
  have hq := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hQ).re_inner_nonneg_right x
  have hd := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hD).re_inner_nonneg_right x
  have hc := congrArg (fun T : H →L[ℂ] H => (inner ℂ x (T x)).re) hcert
  simp only [sub_apply, smul_apply, add_apply, inner_sub_right, inner_add_right,
    inner_smul_right_eq_smul, Complex.sub_re, Complex.add_re, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    polyOperator_apply] at hc
  change 0 ≤ (inner ℂ ((D*D - (1/20 : ℝ) • D) x) x).re
  change 0 ≤ RCLike.re (inner ℂ ((D*D - (1/20 : ℝ) • D) x) x)
  rw [inner_re_symm (𝕜 := ℂ)]
  change 0 ≤ (inner ℂ x ((D*D - (1/20 : ℝ) • D) x)).re
  simp only [sub_apply, smul_apply, inner_sub_right, inner_smul_right_eq_smul,
    Complex.sub_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  change 0 ≤ (inner ℂ x (D x)).re at hd
  change 0 ≤ (inner ℂ x (Q x)).re at hq
  rw [henergy] at hc hd ⊢
  norm_num at hr
  nlinarith

end NuclearUltrapower.SOSEnergy
end
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.NuclearUltrapower.SOSEnergy.certificate_sq_gap_oai.{u_1, u_2} := @OAI.NuclearUltrapower.SOSEnergy.certificate_sq_gap_oai.{u_1, u_2}
