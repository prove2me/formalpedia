-- Prove2me | solution 1 for ImpliedAmbiguity.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T14:06:32.77295+00:00
-- url     : https://prove2.me/submissions/cba8e8dc-24bc-447c-9c9a-0e1e47584d46

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Filter.Extr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.FieldSimp
import Definitions.Def_ImpliedAmbiguity_thetaBar
import Definitions.Def_ImpliedAmbiguity_vTheta
import Definitions.Def_ImpliedAmbiguity_etaTheta
import Definitions.Def_ImpliedAmbiguity_sharpe
import Definitions.Def_ImpliedAmbiguity_tangency
import Definitions.Def_ImpliedAmbiguity_excessReturn

set_option autoImplicit false

namespace S13Scalar

/-- The square certificate for the one-variable rational objective. -/
theorem square_certificate (a b d q θ : ℝ)
    (hrel : a * d * (1 - q ^ 2) = b ^ 2) :
    d * (1 + q) *
        ((a - 2 * b * θ + d * θ ^ 2) * (1 - q) -
          2 * q * (b * θ - d * θ ^ 2)) =
      (d * (1 + q) * θ - b) ^ 2 := by
  calc
    _ = a * d * (1 - q ^ 2) - b ^ 2 +
        (d * (1 + q) * θ - b) ^ 2 := by ring
    _ = _ := by rw [hrel]; ring

/-- A positive rational function has one minimizer, determined by a square. -/
theorem minimization_of_q (a b d q : ℝ)
    (hb : 0 < b) (hd : 0 < d) (hq0 : 0 < q) (hq1 : q < 1)
    (hrel : a * d * (1 - q ^ 2) = b ^ 2) :
    let F := fun θ : ℝ => (a - 2 * b * θ + d * θ ^ 2) / (b * θ - d * θ ^ 2)
    let θstar := (b / d) / (1 + q)
    θstar ∈ Set.Ioo 0 (b / d) ∧
    IsMinOn F (Set.Ioo 0 (b / d)) θstar ∧
    (∀ θ ∈ Set.Ioo 0 (b / d), F θ = F θstar → θ = θstar) ∧
    F θstar = 2 * q / (1 - q) := by
  let F := fun θ : ℝ => (a - 2 * b * θ + d * θ ^ 2) / (b * θ - d * θ ^ 2)
  let θstar := (b / d) / (1 + q)
  change θstar ∈ Set.Ioo 0 (b / d) ∧
    IsMinOn F (Set.Ioo 0 (b / d)) θstar ∧
    (∀ θ ∈ Set.Ioo 0 (b / d), F θ = F θstar → θ = θstar) ∧
    F θstar = 2 * q / (1 - q)
  have hp : 0 < 1 + q := by linarith
  have hm : 0 < 1 - q := by linarith
  have hD : 0 < d * (1 + q) := mul_pos hd hp
  have hbar : 0 < b / d := div_pos hb hd
  have hstar0 : 0 < θstar := div_pos hbar hp
  have hstarlt : θstar < b / d := by
    apply (div_lt_iff₀ hp).2
    nlinarith only [mul_pos hbar hq0]
  have hstar : θstar ∈ Set.Ioo 0 (b / d) := ⟨hstar0, hstarlt⟩
  have hstar_eq : d * (1 + q) * θstar = b := by
    dsimp [θstar]
    rw [div_div]
    exact mul_div_cancel₀ b (ne_of_gt hD)
  have hden (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (b / d)) :
      0 < b * θ - d * θ ^ 2 := by
    have hθd : θ * d < b := (lt_div_iff₀ hd).mp hθ.2
    have hres : 0 < b - d * θ := by linarith only [hθd]
    nlinarith only [mul_pos hθ.1 hres]
  have hvalue : F θstar = 2 * q / (1 - q) := by
    apply (div_eq_div_iff (ne_of_gt (hden θstar hstar)) (ne_of_gt hm)).2
    have hc := square_certificate a b d q θstar hrel
    rw [hstar_eq, sub_self, zero_pow (by decide : 2 ≠ 0)] at hc
    have hz := (mul_eq_zero.mp hc).resolve_left (ne_of_gt hD)
    exact sub_eq_zero.mp hz
  have hmin (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (b / d)) :
      2 * q / (1 - q) ≤ F θ := by
    apply (div_le_div_iff₀ hm (hden θ hθ)).2
    have hc := square_certificate a b d q θ hrel
    have hn : 0 ≤ d * (1 + q) *
        ((a - 2 * b * θ + d * θ ^ 2) * (1 - q) -
          2 * q * (b * θ - d * θ ^ 2)) := by
      rw [hc]
      exact sq_nonneg _
    have hdif := nonneg_of_mul_nonneg_right hn hD
    exact sub_nonneg.mp hdif
  refine ⟨hstar, ?_, ?_, hvalue⟩
  · rw [isMinOn_iff]
    intro θ hθ
    rw [hvalue]
    exact hmin θ hθ
  · intro θ hθ heq
    have heq' : F θ = 2 * q / (1 - q) := heq.trans hvalue
    have hcross := (div_eq_div_iff (ne_of_gt (hden θ hθ)) (ne_of_gt hm)).mp heq'
    have hc := square_certificate a b d q θ hrel
    have hz : (a - 2 * b * θ + d * θ ^ 2) * (1 - q) -
        2 * q * (b * θ - d * θ ^ 2) = 0 := sub_eq_zero.mpr hcross
    rw [hz, mul_zero] at hc
    have hlin : d * (1 + q) * θ - b = 0 := sq_eq_zero_iff.mp hc.symm
    apply mul_left_cancel₀ (ne_of_gt hD)
    exact (sub_eq_zero.mp hlin).trans hstar_eq.symm

/-- The scalar form of implied ambiguity, with its square-root normalization. -/
theorem minimization (a b d : ℝ) (hb : 0 < b) (hd : 0 < d)
    (hstrict : b ^ 2 < a * d) :
    let F := fun θ : ℝ => (a - 2 * b * θ + d * θ ^ 2) / (b * θ - d * θ ^ 2)
    let q := Real.sqrt (1 - b ^ 2 / (a * d))
    let θstar := (b / d) / (1 + q)
    θstar ∈ Set.Ioo 0 (b / d) ∧
    IsMinOn F (Set.Ioo 0 (b / d)) θstar ∧
    (∀ θ ∈ Set.Ioo 0 (b / d), F θ = F θstar → θ = θstar) ∧
    F θstar = 2 * q / (1 - q) := by
  have had : 0 < a * d := lt_trans (sq_pos_of_pos hb) hstrict
  have hf0 : 0 < b ^ 2 / (a * d) := div_pos (sq_pos_of_pos hb) had
  have hf1 : b ^ 2 / (a * d) < 1 := (div_lt_one had).2 hstrict
  have hr : 0 < 1 - b ^ 2 / (a * d) := sub_pos.mpr hf1
  have hq0 : 0 < Real.sqrt (1 - b ^ 2 / (a * d)) := Real.sqrt_pos.2 hr
  have hqsq := Real.sq_sqrt hr.le
  have hq1 : Real.sqrt (1 - b ^ 2 / (a * d)) < 1 := by
    nlinarith only [hq0, hqsq, hf0]
  have hrel : a * d * (1 - Real.sqrt (1 - b ^ 2 / (a * d)) ^ 2) = b ^ 2 := by
    rw [hqsq, sub_sub_cancel]
    exact mul_div_cancel₀ _ (ne_of_gt had)
  exact minimization_of_q a b d _ hb hd hq0 hq1 hrel

end S13Scalar

set_option autoImplicit false

open Matrix ImpliedAmbiguity

namespace S13Matrix

variable {N : ℕ}

/-- Positive definiteness makes the published nonsingular inverse an actual inverse. -/
lemma inverse_cancel (S : Matrix (Fin N) (Fin N) ℝ) (hS : S.PosDef)
    (c : Fin N → ℝ) : S *ᵥ (S⁻¹ *ᵥ c) = c := by
  letI := hS.isUnit.invertible
  rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]

/-- Symmetry transfers the covariance matrix across the real dot product. -/
lemma cross_identity (S : Matrix (Fin N) (Fin N) ℝ) (hS : S.PosDef)
    (c x : Fin N → ℝ) : (S⁻¹ *ᵥ c) ⬝ᵥ (S *ᵥ x) = c ⬝ᵥ x := by
  have hs : Sᵀ = S := (Matrix.isHermitian_iff_isSymm.mp hS.isHermitian).eq
  calc
    (S⁻¹ *ᵥ c) ⬝ᵥ (S *ᵥ x) = x ⬝ᵥ (S *ᵥ (S⁻¹ *ᵥ c)) := by
      simpa only [hs] using Matrix.dotProduct_transpose_mulVec S (S⁻¹ *ᵥ c) x
    _ = c ⬝ᵥ x := by rw [inverse_cancel S hS, dotProduct_comm]

/-- Exact expansion of the numerator of the published ambiguity coefficient. -/
lemma quadratic_expansion (S : Matrix (Fin N) (Fin N) ℝ) (hS : S.PosDef)
    (c x : Fin N → ℝ) (θ : ℝ) :
    vTheta S c x θ ⬝ᵥ (S *ᵥ vTheta S c x θ) =
      (c ⬝ᵥ (S⁻¹ *ᵥ c)) / θ ^ 2 - 2 * (c ⬝ᵥ x) / θ + x ⬝ᵥ (S *ᵥ x) := by
  unfold vTheta
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, inverse_cancel S hS,
    sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [cross_identity S hS, dotProduct_comm x c, dotProduct_comm (S⁻¹ *ᵥ c) c]
  ring

lemma cross_expansion (S : Matrix (Fin N) (Fin N) ℝ) (hS : S.PosDef)
    (c x : Fin N → ℝ) (θ : ℝ) :
    x ⬝ᵥ (S *ᵥ vTheta S c x θ) = (c ⬝ᵥ x) / θ - x ⬝ᵥ (S *ᵥ x) := by
  unfold vTheta
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, inverse_cancel S hS,
    dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm x c]
  ring

/-- The complete coefficient is the stated rational function whenever theta is nonzero. -/
lemma eta_expansion (S : Matrix (Fin N) (Fin N) ℝ) (hS : S.PosDef)
    (c x : Fin N → ℝ) (θ : ℝ) (hθ : θ ≠ 0) :
    etaTheta S c x θ =
      ((c ⬝ᵥ (S⁻¹ *ᵥ c)) - 2 * (c ⬝ᵥ x) * θ + (x ⬝ᵥ (S *ᵥ x)) * θ ^ 2) /
      ((c ⬝ᵥ x) * θ - (x ⬝ᵥ (S *ᵥ x)) * θ ^ 2) := by
  unfold etaTheta
  rw [quadratic_expansion S hS, cross_expansion S hS]
  let a := c ⬝ᵥ (S⁻¹ *ᵥ c)
  let b := c ⬝ᵥ x
  let d := x ⬝ᵥ (S *ᵥ x)
  change (a / θ ^ 2 - 2 * b / θ + d) / (b / θ - d) =
    (a - 2 * b * θ + d * θ ^ 2) / (b * θ - d * θ ^ 2)
  have hn : a / θ ^ 2 - 2 * b / θ + d = (a - 2 * b * θ + d * θ ^ 2) / θ ^ 2 := by
    field_simp [hθ]
    <;> ring
  have hd : b / θ - d = (b * θ - d * θ ^ 2) / θ ^ 2 := by
    field_simp [hθ]
    <;> ring
  rw [hn, hd]
  exact div_div_div_cancel_right₀ (pow_ne_zero 2 hθ) _ _

lemma scalar_positivity (S : Matrix (Fin N) (Fin N) ℝ) (hS : S.PosDef)
    (c x : Fin N → ℝ) (hb : 0 < c ⬝ᵥ x) :
    0 < c ⬝ᵥ (S⁻¹ *ᵥ c) ∧ 0 < x ⬝ᵥ (S *ᵥ x) := by
  have hc : c ≠ 0 := by
    intro h
    simpa [h] using hb
  have hx : x ≠ 0 := by
    intro h
    simpa [h] using hb
  constructor
  · simpa using hS.inv.dotProduct_mulVec_pos hc
  · simpa using hS.dotProduct_mulVec_pos hx

/-- The non-tangency hypothesis makes Cauchy--Schwarz strict at the upper endpoint. -/
lemma strict_discriminant (S : Matrix (Fin N) (Fin N) ℝ) (hS : S.PosDef)
    (c x : Fin N → ℝ) (hb : 0 < c ⬝ᵥ x)
    (hv : ∀ θ : ℝ, 0 < θ → vTheta S c x θ ≠ 0) :
    (c ⬝ᵥ x) ^ 2 < (c ⬝ᵥ (S⁻¹ *ᵥ c)) * (x ⬝ᵥ (S *ᵥ x)) := by
  let a := c ⬝ᵥ (S⁻¹ *ᵥ c)
  let b := c ⬝ᵥ x
  let d := x ⬝ᵥ (S *ᵥ x)
  have hb' : 0 < b := hb
  have hd : 0 < d := (scalar_positivity S hS c x hb).2
  have hθ : 0 < b / d := div_pos hb' hd
  have hp : 0 < vTheta S c x (b / d) ⬝ᵥ (S *ᵥ vTheta S c x (b / d)) := by
    simpa using hS.dotProduct_mulVec_pos (hv (b / d) hθ)
  rw [quadratic_expansion S hS] at hp
  change 0 < a / (b / d) ^ 2 - 2 * b / (b / d) + d at hp
  have heq : a / (b / d) ^ 2 - 2 * b / (b / d) + d = d * (a * d - b ^ 2) / b ^ 2 := by
    field_simp [ne_of_gt hb', ne_of_gt hd]
    <;> ring
  rw [heq] at hp
  have hnum := (div_pos_iff_of_pos_right (sq_pos_of_pos hb')).mp hp
  have hgap := (mul_pos_iff_of_pos_left hd).mp hnum
  change b ^ 2 < a * d
  linarith

/-- Squaring the normalized Sharpe ratio removes both positive square roots. -/
lemma sharpe_square (S : Matrix (Fin N) (Fin N) ℝ) (hS : S.PosDef)
    (c x : Fin N → ℝ) (hb : 0 < c ⬝ᵥ x) :
    (sharpe S c x / sharpe S c (tangency S c)) ^ 2 =
      (c ⬝ᵥ x) ^ 2 / ((c ⬝ᵥ (S⁻¹ *ᵥ c)) * (x ⬝ᵥ (S *ᵥ x))) := by
  obtain ⟨ha, hd⟩ := scalar_positivity S hS c x hb
  unfold sharpe tangency
  rw [inverse_cancel S hS, dotProduct_comm (S⁻¹ *ᵥ c) c]
  simp only [div_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hd.le]
  field_simp [ne_of_gt ha, ne_of_gt hd]
  <;> ring

end S13Matrix

set_option autoImplicit false
open Matrix ImpliedAmbiguity

theorem solution {N : ℕ} (SigmaR : Matrix (Fin N) (Fin N) ℝ) (hSigmaR : SigmaR.PosDef)
    (μ : Fin N → ℝ) (Rf : ℝ) (x : Fin N → ℝ)
    (h14 : 0 < excessReturn μ Rf ⬝ᵥ x)
    (hv : ∀ θ : ℝ, 0 < θ → vTheta SigmaR (excessReturn μ Rf) x θ ≠ 0) :
    let c := excessReturn μ Rf
    let θbar := thetaBar SigmaR c x
    let q := Real.sqrt (1 - (sharpe SigmaR c x / sharpe SigmaR c (tangency SigmaR c)) ^ 2)
    let θstar := θbar / (1 + q)
    θstar ∈ Set.Ioo 0 θbar ∧
    IsMinOn (etaTheta SigmaR c x) (Set.Ioo 0 θbar) θstar ∧
    (∀ θ ∈ Set.Ioo 0 θbar, etaTheta SigmaR c x θ = etaTheta SigmaR c x θstar → θ = θstar) ∧
    etaTheta SigmaR c x θstar = 2 * q / (1 - q)  := by
  dsimp only
  rw [S13Matrix.sharpe_square SigmaR hSigmaR (excessReturn μ Rf) x h14]
  let c := excessReturn μ Rf
  let a := c ⬝ᵥ (SigmaR⁻¹ *ᵥ c)
  let b := c ⬝ᵥ x
  let d := x ⬝ᵥ (SigmaR *ᵥ x)
  let q := Real.sqrt (1 - b ^ 2 / (a * d))
  let θstar := (b / d) / (1 + q)
  have hb : 0 < b := h14
  have hd : 0 < d := (S13Matrix.scalar_positivity SigmaR hSigmaR c x hb).2
  have hstrict : b ^ 2 < a * d :=
    S13Matrix.strict_discriminant SigmaR hSigmaR c x hb hv
  have hs := S13Scalar.minimization a b d hb hd hstrict
  change θstar ∈ Set.Ioo 0 (b / d) ∧
    IsMinOn (fun θ : ℝ => (a - 2 * b * θ + d * θ ^ 2) / (b * θ - d * θ ^ 2))
      (Set.Ioo 0 (b / d)) θstar ∧
    (∀ θ ∈ Set.Ioo 0 (b / d),
      (a - 2 * b * θ + d * θ ^ 2) / (b * θ - d * θ ^ 2) =
      (a - 2 * b * θstar + d * θstar ^ 2) / (b * θstar - d * θstar ^ 2) →
      θ = θstar) ∧
    (a - 2 * b * θstar + d * θstar ^ 2) / (b * θstar - d * θstar ^ 2) =
      2 * q / (1 - q) at hs
  obtain ⟨hstar, hmin, huniq, hvalue⟩ := hs
  change θstar ∈ Set.Ioo 0 (b / d) ∧
    IsMinOn (etaTheta SigmaR c x) (Set.Ioo 0 (b / d)) θstar ∧
    (∀ θ ∈ Set.Ioo 0 (b / d),
      etaTheta SigmaR c x θ = etaTheta SigmaR c x θstar → θ = θstar) ∧
    etaTheta SigmaR c x θstar = 2 * q / (1 - q)
  have heta (θ : ℝ) (hθ : θ ≠ 0) : etaTheta SigmaR c x θ =
      (a - 2 * b * θ + d * θ ^ 2) / (b * θ - d * θ ^ 2) :=
    S13Matrix.eta_expansion SigmaR hSigmaR c x θ hθ
  refine ⟨hstar, ?_, ?_, ?_⟩
  · rw [isMinOn_iff]
    intro θ hθ
    rw [heta θstar (ne_of_gt hstar.1), heta θ (ne_of_gt hθ.1)]
    exact (isMinOn_iff.mp hmin) θ hθ
  · intro θ hθ heq
    rw [heta θ (ne_of_gt hθ.1), heta θstar (ne_of_gt hstar.1)] at heq
    exact huniq θ hθ heq
  · rw [heta θstar (ne_of_gt hstar.1)]
    exact hvalue

#print axioms solution
