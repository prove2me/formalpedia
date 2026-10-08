-- Prove2me | solution 1 for MomentDRO.Conf.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T04:14:06.325878+00:00
-- url     : https://prove2.me/submissions/eb444aaa-58dd-4461-aad7-5c682543e850
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Theorems.Thm_MomentDRO_Conf_corollary_1
import Theorems.Thm_MomentDRO_Conf_corollary_2

set_option autoImplicit false

namespace Pbc1243a6

open Matrix MeasureTheory MomentDRO.Conf

lemma dot_mulVec_symm {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.transpose = A)
    (x y : Fin m → ℝ) : y ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (A *ᵥ y) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, dotProduct_comm]

lemma cs {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.transpose = A)
    (hpos : ∀ u : Fin m → ℝ, 0 ≤ u ⬝ᵥ (A *ᵥ u)) (x y : Fin m → ℝ) :
    (x ⬝ᵥ (A *ᵥ y)) ^ 2 ≤ (x ⬝ᵥ (A *ᵥ x)) * (y ⬝ᵥ (A *ᵥ y)) := by
  have key : ∀ t : ℝ, 0 ≤ (y ⬝ᵥ (A *ᵥ y)) * (t * t) + (2 * (x ⬝ᵥ (A *ᵥ y))) * t
      + (x ⬝ᵥ (A *ᵥ x)) := by
    intro t
    have h := hpos (x + t • y)
    have hs := dot_mulVec_symm A hA x y
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul] at h
    rw [hs] at h
    nlinarith [h]
  have hd := discrim_le_zero key
  unfold discrim at hd
  nlinarith [hd]

/-- Copy of the accepted proof of `MomentDRO.Conf.outer_le_of_quadForm_le` (324c4c9e). -/
lemma outer_le {m : ℕ}
    (cov : Matrix (Fin m) (Fin m) ℝ) (hcov : cov.PosDef)
    (d : Fin m → ℝ) (b : ℝ)
    (hd : quadForm cov⁻¹ d ≤ b) :
    LoewnerLE (Matrix.vecMulVec d d) (b • cov) := by
  have hT : cov.transpose = cov := by
    have h1 := hcov.1
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h1
    exact h1
  have hpos : ∀ u : Fin m → ℝ, 0 ≤ u ⬝ᵥ (cov *ᵥ u) := by
    intro u
    have := hcov.posSemidef.dotProduct_mulVec_nonneg u
    simpa using this
  set y := cov⁻¹ *ᵥ d with hy
  have hcy : cov *ᵥ y = d := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hcov.isUnit),
      Matrix.one_mulVec]
  have hqy : y ⬝ᵥ (cov *ᵥ y) = quadForm cov⁻¹ d := by
    rw [hcy, quadForm, dotProduct_comm]
  show (b • cov - Matrix.vecMulVec d d).PosSemidef
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub,
      Matrix.transpose_smul, hT, Matrix.transpose_vecMulVec]
  · intro x
    have hcs := cs cov hT hpos x y
    rw [hqy, hcy] at hcs
    have hx := hpos x
    have hv : Matrix.vecMulVec d d *ᵥ x = (d ⬝ᵥ x) • d := by
      ext i
      simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul,
        Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    have e : star x ⬝ᵥ ((b • cov - Matrix.vecMulVec d d) *ᵥ x)
        = b * (x ⬝ᵥ (cov *ᵥ x)) - (x ⬝ᵥ d) ^ 2 := by
      simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, hv, dotProduct_sub,
        dotProduct_smul, smul_eq_mul]
      rw [dotProduct_comm d x]
      ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hd hx]

/-- Empirical covariance about the sample mean = about `c` minus the outer product of the shift. -/
lemma empCov_eq {m M : ℕ} (hM : 0 < M) (S : Fin M → (Fin m → ℝ)) (c : Fin m → ℝ) :
    empCov S = empCovAbout S c - Matrix.vecMulVec (empMean S - c) (empMean S - c) := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  ext i j
  simp only [empCov, empCovAbout, empMean, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply,
    smul_eq_mul]
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

lemma psd_of_eq {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℝ} (h : A = B) (hB : B.PosSemidef) :
    A.PosSemidef := h ▸ hB

/-- Deterministic part: on the intersection of the two child events the three constraints hold. -/
lemma event_incl {m M : ℕ} (hM : 0 < M) (Sig : Matrix (Fin m) (Fin m) ℝ) (hSig : Sig.PosDef)
    (mu : Fin m → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b < 1)
    (S : Fin M → (Fin m → ℝ))
    (hq : quadForm Sig⁻¹ (empMean S - mu) ≤ b)
    (h1 : LoewnerLE ((1 + a)⁻¹ • empCovAbout S mu) Sig)
    (h2 : LoewnerLE Sig ((1 - a)⁻¹ • empCovAbout S mu)) :
    LoewnerLE Sig ((1 - a - b)⁻¹ • empCov S) ∧ LoewnerLE ((1 + a)⁻¹ • empCov S) Sig := by
  have hout := outer_le Sig hSig _ b hq
  set d := empMean S - mu with hd
  set C := empCovAbout S mu with hC
  have hE : empCov S = C - Matrix.vecMulVec d d := empCov_eq hM S mu
  unfold LoewnerLE at h1 h2 hout ⊢
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have h1ab : (0 : ℝ) < 1 - a - b := by linarith
  have hpa : (0 : ℝ) < 1 + a := by linarith
  have hdd : (Matrix.vecMulVec d d).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star d
  rw [hE]
  constructor
  · refine psd_of_eq (B := (1 - a - b)⁻¹ • ((1 - a) • ((1 - a)⁻¹ • C - Sig)
        + (b • Sig - Matrix.vecMulVec d d))) ?_ ?_
    · rw [smul_sub (1 - a), smul_smul, mul_inv_cancel₀ h1a.ne', one_smul]
      ext i j
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
      field_simp
      ring
    · exact ((h2.smul h1a.le).add hout).smul (inv_nonneg.mpr h1ab.le)
  · refine psd_of_eq (B := (Sig - (1 + a)⁻¹ • C) + (1 + a)⁻¹ • Matrix.vecMulVec d d) ?_ ?_
    · rw [smul_sub]
      abel
    · exact h1.add (hdd.smul (inv_nonneg.mpr hpa.le))

end Pbc1243a6

open MomentDRO.Conf MeasureTheory in
theorem solution {m M : ℕ} (P : Measure (Fin m → ℝ))
    (hP : HasSecondMoments P) (hcov : (covMat P).PosDef)
    (R : ℝ) (hA4 : Assumption4 P R) (hM : 0 < M)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hlarge : alphaC M m R (δ / 4) + betaC M R (δ / 2) < 1) :
    ENNReal.ofReal (1 - δ) ≤ sampleLaw P M
      {S | quadForm (covMat P)⁻¹ (empMean S - meanVec P) ≤ betaC M R (δ / 2) ∧
        LoewnerLE (covMat P)
          ((1 - alphaC M m R (δ / 4) - betaC M R (δ / 2))⁻¹ • empCov S) ∧
        LoewnerLE ((1 + alphaC M m R (δ / 4))⁻¹ • empCov S)
          (covMat P)} := by
  haveI : IsProbabilityMeasure P := hP.1
  have hd2 : 0 < δ / 2 := by linarith
  have hd2' : δ / 2 < 1 := by linarith
  have h44 : δ / 2 / 2 = δ / 4 := by ring
  set a := alphaC M m R (δ / 4) with ha_def
  set b := betaC M R (δ / 2) with hb_def
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hsq : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMpos
  set s := Real.sqrt (1 - (m : ℝ) / R ^ 4) + Real.sqrt (Real.log (1 / (δ / 4))) with hs_def
  have hs0 : 0 ≤ s := by positivity
  have ha0 : 0 ≤ a := by
    rw [ha_def, alphaC]; positivity
  have hb0 : 0 ≤ b := by
    rw [hb_def, betaC]; positivity
  have ha1 : a < 1 := by linarith
  -- size hypothesis of corollary_2 at δ/2
  have hsize : R ^ 4 * (Real.sqrt (1 - (m : ℝ) / R ^ 4) +
      Real.sqrt (Real.log (2 / (δ / 2)))) ^ 2 < (M : ℝ) := by
    have hlog : (2 : ℝ) / (δ / 2) = 1 / (δ / 4) := by field_simp; ring
    rw [hlog, ← hs_def]
    have haeq : a = R ^ 2 / Real.sqrt M * s := by rw [ha_def, alphaC]
    have hRs : R ^ 2 * s < Real.sqrt M := by
      have : R ^ 2 / Real.sqrt M * s < 1 := haeq ▸ ha1
      rw [div_mul_eq_mul_div, div_lt_one hsq] at this
      exact this
    have hR0 : 0 ≤ R ^ 2 * s := by positivity
    have hsqsq : Real.sqrt M ^ 2 = M := Real.sq_sqrt hMpos.le
    nlinarith [mul_self_lt_mul_self hR0 hRs]
  have hc1 := corollary_1 P hP hcov R hA4 hM (δ / 2) hd2 hd2'
  have hc2 := corollary_2 (M := M) P hP hcov R hA4 (δ / 2) hd2 hd2' hsize
  rw [h44] at hc2
  set μ := sampleLaw P M with hμ
  haveI : IsProbabilityMeasure μ := by
    rw [hμ, sampleLaw]; infer_instance
  set A := {S : Fin M → (Fin m → ℝ) | quadForm (covMat P)⁻¹ (empMean S - meanVec P) ≤ b} with hA
  set B := {S : Fin M → (Fin m → ℝ) | LoewnerLE ((1 + a)⁻¹ • empCovAbout S (meanVec P)) (covMat P) ∧
      LoewnerLE (covMat P) ((1 - a)⁻¹ • empCovAbout S (meanVec P))} with hB
  have hAmeas : MeasurableSet A := by
    apply measurableSet_le _ measurable_const
    apply Continuous.measurable
    simp only [quadForm, dotProduct, Matrix.mulVec, empMean]
    fun_prop
  -- union bound
  have hAc : μ Aᶜ ≤ ENNReal.ofReal (δ / 2) := by
    rw [prob_compl_eq_one_sub hAmeas]
    have : (1 : ENNReal) - ENNReal.ofReal (1 - δ / 2) = ENNReal.ofReal (δ / 2) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
      congr 1; ring
    rw [← this]
    exact tsub_le_tsub_left hc1 _
  have hBle : μ B ≤ μ (A ∩ B) + μ Aᶜ := by
    calc μ B ≤ μ ((A ∩ B) ∪ Aᶜ) := by
          apply measure_mono
          intro S hS
          by_cases h : S ∈ A
          · exact Or.inl ⟨h, hS⟩
          · exact Or.inr h
      _ ≤ μ (A ∩ B) + μ Aᶜ := measure_union_le _ _
  have hAB : ENNReal.ofReal (1 - δ) ≤ μ (A ∩ B) := by
    have h3 : ENNReal.ofReal (1 - δ) + ENNReal.ofReal (δ / 2) ≤ μ (A ∩ B) + ENNReal.ofReal (δ / 2) := by
      calc ENNReal.ofReal (1 - δ) + ENNReal.ofReal (δ / 2) = ENNReal.ofReal (1 - δ / 2) := by
            rw [← ENNReal.ofReal_add (by linarith) hd2.le]; congr 1; ring
        _ ≤ μ B := hc2
        _ ≤ μ (A ∩ B) + μ Aᶜ := hBle
        _ ≤ μ (A ∩ B) + ENNReal.ofReal (δ / 2) := by gcongr
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp h3
  refine hAB.trans (measure_mono ?_)
  rintro S ⟨hSA, hSB1, hSB2⟩
  have := Pbc1243a6.event_incl hM (covMat P) hcov (meanVec P) a b ha0 hb0 hlarge S hSA hSB1 hSB2
  exact ⟨hSA, this.1, this.2⟩
