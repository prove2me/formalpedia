-- Prove2me | solution 1 for MinimaxSLP.RhsSDP.strong_duality
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T23:19:01.910668+00:00
-- url     : https://prove2.me/submissions/7391ce46-4e71-45cf-b8d5-f84bd02d1302

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic
import Definitions.Def_MinimaxSLP_RhsSDP_Model

open MeasureTheory Matrix

namespace SDAux

/-- quadratic dual function -/
def quad {r : ℕ} (s : Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ) (h : Fin r → ℝ) : ℝ :=
  h ⬝ᵥ (s.1 *ᵥ h) + s.2.1 ⬝ᵥ h + s.2.2

lemma integrable_coord {r : ℕ} {μ : Fin r → ℝ} {Q : Matrix (Fin r) (Fin r) ℝ}
    {P : Measure (Fin r → ℝ)} (hP : P ∈ MinimaxSLP.ObjSDP.momentClass μ Q) (i : Fin r) :
    Integrable (fun h : Fin r → ℝ => h i) P := by
  have : IsProbabilityMeasure P := hP.1.1
  exact (hP.1.2 i).integrable one_le_two

lemma integrable_coord_mul {r : ℕ} {μ : Fin r → ℝ} {Q : Matrix (Fin r) (Fin r) ℝ}
    {P : Measure (Fin r → ℝ)} (hP : P ∈ MinimaxSLP.ObjSDP.momentClass μ Q) (i j : Fin r) :
    Integrable (fun h : Fin r → ℝ => h i * h j) P := by
  have := (hP.1.2 i).integrable_mul (hP.1.2 j)
  exact this

lemma integral_coord {r : ℕ} {μ : Fin r → ℝ} {Q : Matrix (Fin r) (Fin r) ℝ}
    {P : Measure (Fin r → ℝ)} (hP : P ∈ MinimaxSLP.ObjSDP.momentClass μ Q) (i : Fin r) :
    ∫ h, h i ∂P = μ i := by
  have := congrFun hP.2.1 i
  simpa [MomentDRO.Conf.meanVec] using this

lemma integral_coord_mul {r : ℕ} {μ : Fin r → ℝ} {Q : Matrix (Fin r) (Fin r) ℝ}
    {P : Measure (Fin r → ℝ)} (hP : P ∈ MinimaxSLP.ObjSDP.momentClass μ Q) (i j : Fin r) :
    ∫ h, h i * h j ∂P = Q i j := by
  have := congrFun (congrFun hP.2.2 i) j
  simpa [MomentDRO.Conf.secondMomentAbout] using this

lemma int_dsum {r : ℕ} {μ : Fin r → ℝ} {Q : Matrix (Fin r) (Fin r) ℝ}
    {P : Measure (Fin r → ℝ)} (hP : P ∈ MinimaxSLP.ObjSDP.momentClass μ Q)
    (c : Fin r → Fin r → ℝ) :
    Integrable (fun h : Fin r → ℝ => ∑ i, ∑ j, c i j * (h i * h j)) P ∧
    ∫ h, ∑ i, ∑ j, c i j * (h i * h j) ∂P = ∑ i, ∑ j, c i j * Q i j := by
  refine ⟨integrable_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => (integrable_coord_mul hP i j).const_mul _)), ?_⟩
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => (integrable_coord_mul hP i j).const_mul _))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_finsetSum _ (fun j _ => (integrable_coord_mul hP i j).const_mul _)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [integral_const_mul, integral_coord_mul hP]

lemma int_sum {r : ℕ} {μ : Fin r → ℝ} {Q : Matrix (Fin r) (Fin r) ℝ}
    {P : Measure (Fin r → ℝ)} (hP : P ∈ MinimaxSLP.ObjSDP.momentClass μ Q)
    (y : Fin r → ℝ) :
    Integrable (fun h : Fin r → ℝ => ∑ i, y i * h i) P ∧
    ∫ h, ∑ i, y i * h i ∂P = ∑ i, y i * μ i := by
  refine ⟨integrable_finsetSum _ (fun i _ => (integrable_coord hP i).const_mul _), ?_⟩
  rw [integral_finsetSum _ (fun i _ => (integrable_coord hP i).const_mul _)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_const_mul, integral_coord hP]

lemma integrable_quad {r : ℕ} {μ : Fin r → ℝ} {Q : Matrix (Fin r) (Fin r) ℝ}
    {P : Measure (Fin r → ℝ)} (hP : P ∈ MinimaxSLP.ObjSDP.momentClass μ Q)
    (s : Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ) :
    Integrable (quad s) P ∧ ∫ h, quad s h ∂P = MinimaxSLP.RhsSDP.dualObj μ Q s := by
  have : IsProbabilityMeasure P := hP.1.1
  obtain ⟨Y, y, y0⟩ := s
  have e : quad (Y, y, y0) = fun h => (∑ i, ∑ j, (Y : Fin r → Fin r → ℝ) i j * (h i * h j)) +
      (∑ i, y i * h i) + y0 := by
    funext h
    simp only [quad, dotProduct, mulVec, Finset.mul_sum]
    congr 2
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  obtain ⟨i1, e1⟩ := int_dsum hP (Y : Fin r → Fin r → ℝ)
  obtain ⟨i2, e2⟩ := int_sum hP y
  refine ⟨by rw [e]; exact (i1.add i2).add (integrable_const _), ?_⟩
  rw [e]
  dsimp only
  rw [integral_add (by exact i1.add i2) (integrable_const _), integral_add i1 i2, e1, e2]
  simp only [integral_const, probReal_univ, one_smul]
  unfold MinimaxSLP.RhsSDP.dualObj MinimaxSLP.ObjSDP.frob
  simp only [dotProduct]
  congr 2
  · exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => mul_comm _ _))
  · exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

lemma abs_le_half {t : ℝ} : |t| ≤ (1 + t ^ 2) / 2 := by
  have := sq_nonneg (|t| - 1)
  rw [sub_sq, sq_abs] at this
  nlinarith

/-- integrability of `g` under the moment class -/
lemma integrable_g {r : ℕ} {μ : Fin r → ℝ} {Q : Matrix (Fin r) (Fin r) ℝ}
    {P : Measure (Fin r → ℝ)} (hP : P ∈ MinimaxSLP.ObjSDP.momentClass μ Q)
    (g : (Fin r → ℝ) → ℝ) (hg : Continuous g) (A B : ℝ)
    (hgb : ∀ h, |g h| ≤ A + B * ∑ i, |h i|) : Integrable g P := by
  have : IsProbabilityMeasure P := hP.1.1
  have ib : Integrable (fun h : Fin r → ℝ => A + B * ∑ i, |h i|) P :=
    (integrable_const _).add ((integrable_finsetSum _ (fun i _ => (integrable_coord hP i).abs)).const_mul _)
  refine ib.mono' hg.aestronglyMeasurable (ae_of_all _ (fun h => ?_))
  rw [Real.norm_eq_abs]; exact hgb h

lemma weak_duality {r : ℕ} {μ : Fin r → ℝ} {Q : Matrix (Fin r) (Fin r) ℝ}
    {P : Measure (Fin r → ℝ)} (hP : P ∈ MinimaxSLP.ObjSDP.momentClass μ Q)
    (g : (Fin r → ℝ) → ℝ) (hg : Continuous g) (A B : ℝ)
    (hgb : ∀ h, |g h| ≤ A + B * ∑ i, |h i|)
    (s : Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ) (hs : ∀ h, g h ≤ quad s h) :
    ∫ h, g h ∂P ≤ MinimaxSLP.RhsSDP.dualObj μ Q s := by
  obtain ⟨iq, eq⟩ := integrable_quad hP s
  rw [← eq]
  exact integral_mono (integrable_g hP g hg A B hgb) iq hs

lemma dual_point {r : ℕ} (g : (Fin r → ℝ) → ℝ) (A B : ℝ) (hB : 0 ≤ B)
    (hgb : ∀ h, |g h| ≤ A + B * ∑ i, |h i|) :
    ∀ h, g h ≤ quad ((B / 2) • (1 : Matrix (Fin r) (Fin r) ℝ), 0, A + B * r / 2) h := by
  intro h
  simp only [quad, smul_mulVec, one_mulVec, dotProduct_smul, zero_dotProduct, add_zero,
    smul_eq_mul]
  have h1 : ∑ i, |h i| ≤ ∑ i, (1 + h i ^ 2) / 2 := Finset.sum_le_sum (fun i _ => abs_le_half)
  have h2 : ∑ i : Fin r, (1 + h i ^ 2) / 2 = r / 2 + (h ⬝ᵥ h) / 2 := by
    simp only [dotProduct, add_div, Finset.sum_add_distrib, ← Finset.sum_div]
    simp [sq]
  have := hgb h
  have := le_abs_self (g h)
  nlinarith [mul_le_mul_of_nonneg_left h1 hB]


/-- finitely supported measure from nonnegative weights -/
noncomputable def toMeas {r : ℕ} (w : (Fin r → ℝ) →₀ ℝ) : Measure (Fin r → ℝ) :=
  ∑ p ∈ w.support, ENNReal.ofReal (w p) • Measure.dirac p

lemma integrable_toMeas {r : ℕ} (w : (Fin r → ℝ) →₀ ℝ) (f : (Fin r → ℝ) → ℝ) :
    Integrable f (toMeas w) := by
  unfold toMeas
  refine integrable_finsetSum_measure.2 (fun p _ => ?_)
  exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top

lemma integral_toMeas {r : ℕ} (w : (Fin r → ℝ) →₀ ℝ) (hw : ∀ p, 0 ≤ w p)
    (f : (Fin r → ℝ) → ℝ) :
    ∫ h, f h ∂(toMeas w) = ∑ p ∈ w.support, w p * f p := by
  unfold toMeas
  rw [integral_finsetSum_measure (fun p _ =>
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw p), smul_eq_mul]

lemma toMeas_mem {r : ℕ} (w : (Fin r → ℝ) →₀ ℝ) (hw : ∀ p, 0 ≤ w p)
    (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ)
    (h0 : ∑ p ∈ w.support, w p = 1) (h1 : ∀ i, ∑ p ∈ w.support, w p * p i = μ i)
    (h2 : ∀ i j, ∑ p ∈ w.support, w p * (p i * p j) = Q i j) :
    toMeas w ∈ MinimaxSLP.ObjSDP.momentClass μ Q := by
  have hprob : IsProbabilityMeasure (toMeas w) := by
    constructor
    unfold toMeas
    rw [Measure.coe_finset_sum, Finset.sum_apply]
    simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul,
      mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => hw p), h0, ENNReal.ofReal_one]
  refine ⟨⟨hprob, fun i => ?_⟩, ?_, ?_⟩
  · exact (memLp_two_iff_integrable_sq (continuous_apply i).aestronglyMeasurable).2
      (integrable_toMeas w _)
  · funext i
    simp only [MomentDRO.Conf.meanVec]
    rw [integral_toMeas w hw, h1]
  · funext i j
    simp only [MomentDRO.Conf.secondMomentAbout, Matrix.of_apply, Pi.zero_apply, sub_zero]
    rw [integral_toMeas w hw, h2]


noncomputable def L0 {r : ℕ} : ((Fin r → ℝ) →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun _ => (1 : ℝ))
noncomputable def L1 {r : ℕ} : ((Fin r → ℝ) →₀ ℝ) →ₗ[ℝ] (Fin r → ℝ) :=
  Finsupp.linearCombination ℝ (fun p => p)
noncomputable def L2 {r : ℕ} : ((Fin r → ℝ) →₀ ℝ) →ₗ[ℝ] Matrix (Fin r) (Fin r) ℝ :=
  Finsupp.linearCombination ℝ (fun p => vecMulVec p p)
noncomputable def Lg {r : ℕ} (g : (Fin r → ℝ) → ℝ) : ((Fin r → ℝ) →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ g

lemma L0_eq {r : ℕ} (w : (Fin r → ℝ) →₀ ℝ) : L0 w = ∑ p ∈ w.support, w p := by
  simp [L0, Finsupp.linearCombination_apply, Finsupp.sum]
lemma L1_eq {r : ℕ} (w : (Fin r → ℝ) →₀ ℝ) (i : Fin r) :
    L1 w i = ∑ p ∈ w.support, w p * p i := by
  simp [L1, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply]
lemma L2_eq {r : ℕ} (w : (Fin r → ℝ) →₀ ℝ) (i j : Fin r) :
    L2 w i j = ∑ p ∈ w.support, w p * (p i * p j) := by
  simp [L2, Finsupp.linearCombination_apply, Finsupp.sum, Matrix.sum_apply, vecMulVec_apply]
lemma Lg_eq {r : ℕ} (g : (Fin r → ℝ) → ℝ) (w : (Fin r → ℝ) →₀ ℝ) :
    Lg g w = ∑ p ∈ w.support, w p * g p := by
  simp [Lg, Finsupp.linearCombination_apply, Finsupp.sum]

lemma toMeas_mem' {r : ℕ} (w : (Fin r → ℝ) →₀ ℝ) (hw : ∀ p, 0 ≤ w p)
    (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ) (g : (Fin r → ℝ) → ℝ)
    (h0 : L0 w = 1) (h1 : L1 w = μ) (h2 : L2 w = Q) :
    toMeas w ∈ MinimaxSLP.ObjSDP.momentClass μ Q ∧ ∫ h, g h ∂(toMeas w) = Lg g w := by
  refine ⟨toMeas_mem w hw μ Q (by rw [← L0_eq, h0]) (fun i => by rw [← L1_eq, h1])
    (fun i j => by rw [← L2_eq, h2]), ?_⟩
  rw [integral_toMeas w hw, Lg_eq]

/-- representation of moments by a finitely supported nonnegative weight -/
lemma represent {r : ℕ} (m0 : ℝ) (hm0 : 0 < m0) (a : Fin r → ℝ)
    (B : Matrix (Fin r) (Fin r) ℝ) :
    ∃ w : (Fin r → ℝ) →₀ ℝ, (∀ p, 0 ≤ w p) ∧ L0 w = m0 ∧ L1 w = m0 • a ∧
      L2 w = m0 • (Bᵀ * B + vecMulVec a a) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    refine ⟨Finsupp.single a m0, fun p => ?_, ?_, ?_, ?_⟩
    · rw [Finsupp.single_apply]; split_ifs <;> linarith
    · simp [L0, Finsupp.linearCombination_single]
    · simp [L1, Finsupp.linearCombination_single]
    · ext i; exact i.elim0
  · set c := Real.sqrt r with hc
    have hc2 : c ^ 2 = r := Real.sq_sqrt (Nat.cast_nonneg r)
    have hrR : (r : ℝ) ≠ 0 := by positivity
    let u : Fin r → Fin r → ℝ := fun i j => B i j
    refine ⟨∑ i : Fin r, (m0 / (2 * r)) • (Finsupp.single (a + c • u i) 1 +
      Finsupp.single (a - c • u i) 1), fun p => ?_, ?_, ?_, ?_⟩
    · rw [Finsupp.finset_sum_apply]
      refine Finset.sum_nonneg (fun i _ => ?_)
      simp only [Finsupp.smul_apply, Finsupp.add_apply, Finsupp.single_apply, smul_eq_mul]
      apply mul_nonneg (by positivity)
      split_ifs <;> norm_num
    · simp only [map_sum, map_smul, map_add, L0, Finsupp.linearCombination_single, smul_eq_mul]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
      ring
    · ext j
      simp only [map_sum, map_smul, map_add, L1, Finsupp.linearCombination_single]
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul,
        one_mul]
      have : ∀ i : Fin r, m0 / (2 * r) * ((a j + c * u i j) + (a j - c * u i j)) =
          m0 / r * a j := by
        intro i; field_simp; ring
      simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · ext j k
      simp only [map_sum, map_smul, map_add, L2, Finsupp.linearCombination_single]
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.add_apply, vecMulVec_apply,
        Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, one_mul, Matrix.mul_apply,
        Matrix.transpose_apply]
      have : ∀ i : Fin r, m0 / (2 * r) * ((a j + c * u i j) * (a k + c * u i k) +
          (a j - c * u i j) * (a k - c * u i k)) = m0 / r * (a j * a k) + m0 * (B i j * B i k) := by
        intro i
        have e : c * c = r := by rw [← sq]; exact hc2
        have h' : m0 / (2 * r) * ((a j + c * u i j) * (a k + c * u i k) +
            (a j - c * u i j) * (a k - c * u i k)) =
            m0 / r * (a j * a k) + m0 / r * (c * c) * (B i j * B i k) := by
          simp only [u]; ring
        rw [h', e, div_mul_cancel₀ m0 hrR]
      simp only [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
      field_simp
      ring


lemma pd_coercive {r : ℕ} (S : Matrix (Fin r) (Fin r) ℝ) (hS : S.PosDef) :
    ∃ c > 0, ∀ v : Fin r → ℝ, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (S *ᵥ v) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    exact ⟨1, one_pos, fun v => by simp [dotProduct]⟩
  set K := Metric.sphere (0 : Fin r → ℝ) 1
  have hK : IsCompact K := isCompact_sphere _ _
  have hKne : K.Nonempty := by
    refine ⟨fun _ => 1, ?_⟩
    simp only [K, mem_sphere_iff_norm, sub_zero]
    have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    rw [pi_norm_const, norm_one]
  have hf : Continuous (fun v : Fin r → ℝ => v ⬝ᵥ (S *ᵥ v)) :=
    continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
  obtain ⟨v0, hv0K, hmin⟩ := hK.exists_isMinOn hKne hf.continuousOn
  have hv0 : v0 ≠ 0 := by
    intro h; simp [K, h] at hv0K
  have hc0 : 0 < v0 ⬝ᵥ (S *ᵥ v0) := hS.dotProduct_mulVec_pos hv0 |>.trans_eq (by simp)
  refine ⟨(v0 ⬝ᵥ (S *ᵥ v0)) / r, by positivity, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : ‖v‖⁻¹ • v ∈ K := by
    simp only [K, mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, norm_norm]
    field_simp
  have h1 : v0 ⬝ᵥ (S *ᵥ v0) ≤ (‖v‖⁻¹ • v) ⬝ᵥ (S *ᵥ (‖v‖⁻¹ • v)) := hmin hu
  simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1
  have h2 : v ⬝ᵥ v ≤ r * ‖v‖ ^ 2 := by
    simp only [dotProduct]
    calc ∑ i, v i * v i ≤ ∑ _i : Fin r, ‖v‖ ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have := norm_le_pi_norm v i
          rw [Real.norm_eq_abs] at this
          nlinarith [abs_nonneg (v i), sq_abs (v i)]
      _ = r * ‖v‖ ^ 2 := by simp
  have h3 : v0 ⬝ᵥ (S *ᵥ v0) * ‖v‖ ^ 2 ≤ v ⬝ᵥ (S *ᵥ v) := by
    have e : v0 ⬝ᵥ (S *ᵥ v0) ≤ ‖v‖⁻¹ * (‖v‖⁻¹ * v ⬝ᵥ (S *ᵥ v)) := h1
    have e2 : ‖v‖⁻¹ * (‖v‖⁻¹ * v ⬝ᵥ (S *ᵥ v)) = v ⬝ᵥ (S *ᵥ v) / ‖v‖ ^ 2 := by
      field_simp
    rw [e2, le_div_iff₀ (by positivity)] at e
    exact e
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  calc (v0 ⬝ᵥ (S *ᵥ v0)) / r * (v ⬝ᵥ v) ≤ (v0 ⬝ᵥ (S *ᵥ v0)) / r * (r * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = v0 ⬝ᵥ (S *ᵥ v0) * ‖v‖ ^ 2 := by field_simp
    _ ≤ _ := h3

lemma abs_mul_le_dot {r : ℕ} (v : Fin r → ℝ) (i j : Fin r) : |v i| * |v j| ≤ v ⬝ᵥ v := by
  have hi : v i * v i ≤ v ⬝ᵥ v :=
    Finset.single_le_sum (f := fun k => v k * v k) (fun k _ => mul_self_nonneg (v k))
      (Finset.mem_univ i)
  have hj : v j * v j ≤ v ⬝ᵥ v :=
    Finset.single_le_sum (f := fun k => v k * v k) (fun k _ => mul_self_nonneg (v k))
      (Finset.mem_univ j)
  have := sq_nonneg (|v i| - |v j|)
  have e1 : |v i| * |v i| = v i * v i := abs_mul_abs_self _
  have e2 : |v j| * |v j| = v j * v j := abs_mul_abs_self _
  nlinarith

lemma psd_of_close {r : ℕ} (S S' : Matrix (Fin r) (Fin r) ℝ) (c : ℝ)
    (hc : ∀ v : Fin r → ℝ, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (S *ᵥ v)) (hS' : S'.IsSymm)
    (hclose : ∑ i, ∑ j, |S' i j - S i j| ≤ c) : S'.PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨by show S'ᴴ = S'; rw [conjTranspose_eq_transpose_of_trivial]; exact hS', fun v => ?_⟩
  simp only [star_trivial]
  have hsplit : v ⬝ᵥ (S' *ᵥ v) = v ⬝ᵥ (S *ᵥ v) + ∑ i, ∑ j, v i * (S' i j - S i j) * v j := by
    simp only [dotProduct, mulVec, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  have hlow : -(∑ i, ∑ j, |S' i j - S i j|) * (v ⬝ᵥ v) ≤
      ∑ i, ∑ j, v i * (S' i j - S i j) * v j := by
    rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have h1 := abs_mul_le_dot v i j
    have h2 : |v i * (S' i j - S i j) * v j| = |S' i j - S i j| * (|v i| * |v j|) := by
      rw [abs_mul, abs_mul]; ring
    have h3 := neg_abs_le (v i * (S' i j - S i j) * v j)
    rw [h2] at h3
    nlinarith [abs_nonneg (S' i j - S i j)]
  have hvv : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg (fun k _ => mul_self_nonneg (v k))
  rw [hsplit]
  nlinarith [hc v]

end SDAux


open MeasureTheory Matrix
open scoped MatrixOrder

namespace SDAux

noncomputable def symm {r : ℕ} (M : Matrix (Fin r) (Fin r) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  (1 / 2 : ℝ) • (M + Mᵀ)

lemma symm_apply {r : ℕ} (M : Matrix (Fin r) (Fin r) ℝ) (i j : Fin r) :
    symm M i j = (M i j + M j i) / 2 := by
  simp [symm]; ring

lemma symm_of_isSymm {r : ℕ} (M : Matrix (Fin r) (Fin r) ℝ) (hM : M.IsSymm) : symm M = M := by
  ext i j
  rw [symm_apply, show M j i = M i j from (hM.apply i j)]
  ring

abbrev EE (r : ℕ) := ℝ × (Fin r → ℝ) × Matrix (Fin r) (Fin r) ℝ × ℝ

def HH {r : ℕ} (g : (Fin r → ℝ) → ℝ) : Set (EE r) :=
  {z | ∃ w : (Fin r → ℝ) →₀ ℝ, (∀ p, 0 ≤ w p) ∧ z.1 = L0 w ∧ z.2.1 = L1 w ∧
    symm z.2.2.1 = L2 w ∧ z.2.2.2 ≤ Lg g w}

lemma convex_HH {r : ℕ} (g : (Fin r → ℝ) → ℝ) : Convex ℝ (HH g) := by
  rintro z ⟨w, hw, h0, h1, h2, h3⟩ z' ⟨w', hw', h0', h1', h2', h3'⟩ a b ha hb _
  refine ⟨a • w + b • w', fun p => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hw p)) (mul_nonneg hb (hw' p))
  · simp [map_add, map_smul, h0, h0']
  · simp [map_add, map_smul, h1, h1']
  · rw [map_add, map_smul, map_smul, ← h2, ← h2']
    ext i j
    simp only [Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, symm_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, map_add, map_smul]
    nlinarith

lemma Lg_ge {r : ℕ} (g : (Fin r → ℝ) → ℝ) (A B : ℝ) (hB : 0 ≤ B)
    (hgb : ∀ h, |g h| ≤ A + B * ∑ i, |h i|) (w : (Fin r → ℝ) →₀ ℝ) (hw : ∀ p, 0 ≤ w p) :
    -A * L0 w - B * ∑ i, (L0 w + L2 w i i) / 2 ≤ Lg g w := by
  have hpt : ∀ p : Fin r → ℝ, -A - B * ∑ i, (1 + p i * p i) / 2 ≤ g p := by
    intro p
    have h1 : ∑ i, |p i| ≤ ∑ i, (1 + p i * p i) / 2 :=
      Finset.sum_le_sum (fun i _ => by rw [← sq]; exact abs_le_half)
    have := hgb p
    have := neg_abs_le (g p)
    nlinarith [mul_le_mul_of_nonneg_left h1 hB]
  rw [L0_eq, Lg_eq]
  simp_rw [L2_eq]
  calc -A * ∑ p ∈ w.support, w p - B * ∑ i, (∑ p ∈ w.support, w p +
        ∑ p ∈ w.support, w p * (p i * p i)) / 2
      = ∑ p ∈ w.support, w p * (-A - B * ∑ i, (1 + p i * p i) / 2) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div, mul_sub,
          Finset.sum_sub_distrib]
        rw [Finset.sum_comm (s := Finset.univ)]
        congr 1
        · exact Finset.sum_congr rfl (fun p _ => by ring)
        · refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun i _ => by ring))
    _ ≤ ∑ p ∈ w.support, w p * g p :=
        Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left (hpt p) (hw p))


lemma cat_sum {X ι : Type*} [TopologicalSpace X] (s : Finset ι) (f : ι → X → ℝ) (x : X)
    (h : ∀ i ∈ s, ContinuousAt (f i) x) : ContinuousAt (fun y => ∑ i ∈ s, f i y) x :=
  tendsto_finset_sum s h

noncomputable def Sz {r : ℕ} (z : EE r) : Matrix (Fin r) (Fin r) ℝ :=
  (1 / z.1) • symm z.2.2.1 - vecMulVec ((1 / z.1) • z.2.1) ((1 / z.1) • z.2.1)

lemma Sz_apply {r : ℕ} (z : EE r) (i j : Fin r) :
    Sz z i j = (1 / z.1) * ((z.2.2.1 i j + z.2.2.1 j i) / 2) -
      ((1 / z.1) * z.2.1 i) * ((1 / z.1) * z.2.1 j) := by
  simp [Sz, symm_apply, vecMulVec_apply]
  ring

lemma Sz_isSymm {r : ℕ} (z : EE r) : (Sz z).IsSymm := by
  ext i j
  simp only [transpose_apply, Sz_apply]
  ring

lemma interior_HH {r : ℕ} (g : (Fin r → ℝ) → ℝ) (A B : ℝ) (hB : 0 ≤ B)
    (hgb : ∀ h, |g h| ≤ A + B * ∑ i, |h i|) (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ)
    (hQ : Q.IsSymm) (hA4 : (Q - vecMulVec μ μ).PosDef) :
    ((1 : ℝ), μ, Q, -A - B * ∑ i, (1 + Q i i) / 2 - 1) ∈ interior (HH g) := by
  set x0 : EE r := ((1 : ℝ), μ, Q, -A - B * ∑ i, (1 + Q i i) / 2 - 1) with hx0
  obtain ⟨c, hc, hcS⟩ := pd_coercive _ hA4
  have hcont1 : ContinuousAt (fun z : EE r => z.1) x0 := continuous_fst.continuousAt
  have hinv : ContinuousAt (fun z : EE r => 1 / z.1) x0 :=
    continuousAt_const.div hcont1 (by simp [hx0])
  have hM : Continuous (fun z : EE r => z.2.2.1) :=
    continuous_fst.comp (continuous_snd.comp continuous_snd)
  have hv : Continuous (fun z : EE r => z.2.1) := continuous_fst.comp continuous_snd
  have hentry : ∀ i j, ContinuousAt (fun z : EE r => Sz z i j) x0 := by
    intro i j
    simp only [Sz_apply]
    have e1 : Continuous (fun z : EE r => z.2.2.1 i j) := hM.matrix_elem i j
    have e2 : Continuous (fun z : EE r => z.2.2.1 j i) := hM.matrix_elem j i
    have e3 : Continuous (fun z : EE r => z.2.1 i) := (continuous_apply i).comp hv
    have e4 : Continuous (fun z : EE r => z.2.1 j) := (continuous_apply j).comp hv
    exact (hinv.mul ((e1.add e2).div_const _).continuousAt).sub
      ((hinv.mul e3.continuousAt).mul (hinv.mul e4.continuousAt))
  have hdist : ContinuousAt (fun z : EE r =>
      ∑ i, ∑ j, |Sz z i j - (Q - vecMulVec μ μ) i j|) x0 := by
    have : ∀ i j, ContinuousAt (fun z : EE r => |Sz z i j - (Q - vecMulVec μ μ) i j|) x0 :=
      fun i j => ((hentry i j).sub continuousAt_const).abs
    exact cat_sum _ _ _ (fun i _ => cat_sum _ _ _ (fun j _ => this i j))
  have hSx0 : Sz x0 = Q - vecMulVec μ μ := by
    simp only [Sz, hx0, div_one, one_smul, symm_of_isSymm Q hQ]
  have ev1 : ∀ᶠ z in nhds x0, (0 : ℝ) < z.1 :=
    continuousAt_const.eventually_lt hcont1 (by simp [hx0])
  have ev2 : ∀ᶠ z in nhds x0, ∑ i, ∑ j, |Sz z i j - (Q - vecMulVec μ μ) i j| < c :=
    hdist.eventually_lt continuousAt_const (by simp [hSx0, hc])
  have hlow : ContinuousAt (fun z : EE r => -A * z.1 - B * ∑ i, (z.1 + z.2.2.1 i i) / 2) x0 := by
    have : ∀ i, Continuous (fun z : EE r => (z.1 + z.2.2.1 i i) / 2) :=
      fun i => (continuous_fst.add (hM.matrix_elem i i)).div_const _
    exact ((continuousAt_const.mul hcont1).sub (continuousAt_const.mul
      (continuous_finset_sum _ (fun i _ => this i)).continuousAt))
  have ev3 : ∀ᶠ z in nhds x0, z.2.2.2 < -A * z.1 - B * ∑ i, (z.1 + z.2.2.1 i i) / 2 := by
    have ht : ContinuousAt (fun z : EE r => z.2.2.2) x0 :=
      (continuous_snd.comp (continuous_snd.comp continuous_snd)).continuousAt
    refine ht.eventually_lt hlow ?_
    simp only [hx0]
    have : ∑ i, (1 + Q i i) / 2 = ∑ i, ((1 : ℝ) + Q i i) / 2 := rfl
    linarith
  rw [mem_interior_iff_mem_nhds]
  filter_upwards [ev1, ev2, ev3] with z h1 h2 h3
  have hpsd : (Sz z).PosSemidef := psd_of_close _ _ c hcS (Sz_isSymm z) h2.le
  obtain ⟨B', hB'⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpsd.nonneg
  obtain ⟨w, hw, hw0, hw1, hw2⟩ := represent z.1 h1 ((1 / z.1) • z.2.1) B'
  have hz1 : z.1 ≠ 0 := h1.ne'
  have hL2 : L2 w = symm z.2.2.1 := by
    rw [hw2, show B'ᵀ * B' = Sz z from by rw [hB']; rfl]
    unfold Sz
    rw [sub_add_cancel, smul_smul, mul_one_div_cancel hz1, one_smul]
  refine ⟨w, hw, hw0.symm, ?_, hL2.symm, ?_⟩
  · rw [hw1, smul_smul, mul_one_div_cancel hz1, one_smul]
  · have := Lg_ge g A B hB hgb w hw
    rw [hw0, hL2] at this
    simp only [symm_apply, add_self_div_two] at this
    linarith

end SDAux


open MeasureTheory Matrix
open scoped MatrixOrder

namespace SDAux

lemma decomp {r : ℕ} (f : StrongDual ℝ (EE r)) (z : EE r) :
    f z = z.1 * f (1, 0, 0, 0) + ∑ i, z.2.1 i * f (0, Pi.single i 1, 0, 0) +
      ∑ i, ∑ j, z.2.2.1 i j * f (0, 0, Matrix.single i j 1, 0) + z.2.2.2 * f (0, 0, 0, 1) := by
  have hz : z = z.1 • ((1 : ℝ), (0 : Fin r → ℝ), (0 : Matrix (Fin r) (Fin r) ℝ), (0 : ℝ)) +
      ∑ i, z.2.1 i • ((0 : ℝ), (Pi.single i 1 : Fin r → ℝ), (0 : Matrix (Fin r) (Fin r) ℝ), (0 : ℝ)) +
      ∑ i, ∑ j, z.2.2.1 i j • ((0 : ℝ), (0 : Fin r → ℝ), Matrix.single i j (1 : ℝ), (0 : ℝ)) +
      z.2.2.2 • ((0 : ℝ), (0 : Fin r → ℝ), (0 : Matrix (Fin r) (Fin r) ℝ), (1 : ℝ)) := by
    obtain ⟨z0, z1, Z, t⟩ := z
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · simp [Prod.fst_sum]
    · ext k
      simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    · ext k l
      simp [Prod.fst_sum, Prod.snd_sum, Matrix.sum_apply, Matrix.single_apply, ite_and,
        Finset.sum_ite_eq', Finset.sum_ite_eq]
    · simp [Prod.snd_sum]
  conv_lhs => rw [hz]
  simp only [map_add, map_sum, map_smul, smul_eq_mul]

lemma quad_symm {r : ℕ} (M : Matrix (Fin r) (Fin r) ℝ) (h : Fin r → ℝ) :
    h ⬝ᵥ (symm M *ᵥ h) = ∑ i, ∑ j, M i j * (h i * h j) := by
  simp only [dotProduct, mulVec, symm_apply, Finset.mul_sum]
  have : ∀ i j, h i * ((M i j + M j i) / 2 * h j) =
      (M i j * (h i * h j)) / 2 + (M j i * (h j * h i)) / 2 := by intro i j; ring
  simp only [this, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => M j i * (h j * h i) / 2)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => by ring)

lemma frob_symm {r : ℕ} (Q M : Matrix (Fin r) (Fin r) ℝ) (hQ : Q.IsSymm) :
    MinimaxSLP.ObjSDP.frob Q (symm M) = ∑ i, ∑ j, M i j * Q i j := by
  unfold MinimaxSLP.ObjSDP.frob
  simp only [symm_apply]
  have : ∀ i j, Q i j * ((M i j + M j i) / 2) = (M i j * Q i j) / 2 + (M j i * Q j i) / 2 := by
    intro i j; rw [hQ.apply i j]; ring
  simp only [this, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => M j i * Q j i / 2)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => by ring)

lemma symm_isSymm {r : ℕ} (M : Matrix (Fin r) (Fin r) ℝ) : (symm M).IsSymm := by
  ext i j; simp only [transpose_apply, symm_apply]; ring


/-- the generic moment duality -/
theorem moment_duality {r : ℕ} (g : (Fin r → ℝ) → ℝ) (hg : Continuous g) (A B : ℝ) (hB : 0 ≤ B)
    (hgb : ∀ h, |g h| ≤ A + B * ∑ i, |h i|) (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ)
    (hQ : Q.IsSymm) (hA4 : (Q - vecMulVec μ μ).PosDef) :
    IsLUB ((fun P => ∫ h, g h ∂P) '' MinimaxSLP.ObjSDP.momentClass μ Q)
        (sSup ((fun P => ∫ h, g h ∂P) '' MinimaxSLP.ObjSDP.momentClass μ Q)) ∧
      IsGLB (MinimaxSLP.RhsSDP.dualObj μ Q ''
          {s | s.1.IsSymm ∧ ∀ h, g h ≤ h ⬝ᵥ (s.1 *ᵥ h) + s.2.1 ⬝ᵥ h + s.2.2})
        (sSup ((fun P => ∫ h, g h ∂P) '' MinimaxSLP.ObjSDP.momentClass μ Q)) := by
  set PV := (fun P => ∫ h, g h ∂P) '' MinimaxSLP.ObjSDP.momentClass μ Q with hPV
  set DF := {s : Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ |
    s.1.IsSymm ∧ ∀ h, g h ≤ h ⬝ᵥ (s.1 *ᵥ h) + s.2.1 ⬝ᵥ h + s.2.2} with hDF
  set t0 := -A - B * ∑ i, (1 + Q i i) / 2 - 1 with ht0
  have hx0 := interior_HH g A B hB hgb μ Q hQ hA4
  have hQs : symm Q = Q := symm_of_isSymm Q hQ
  -- primal nonempty
  have hne : PV.Nonempty := by
    obtain ⟨w, hw, h0, h1, h2, -⟩ := interior_subset hx0
    simp only at h0 h1 h2
    rw [hQs] at h2
    obtain ⟨hm, -⟩ := toMeas_mem' w hw μ Q g h0.symm h1.symm h2.symm
    exact ⟨_, _, hm, rfl⟩
  -- weak duality
  have hweak : ∀ v ∈ PV, ∀ s ∈ DF, v ≤ MinimaxSLP.RhsSDP.dualObj μ Q s := by
    rintro v ⟨P, hP, rfl⟩ s hs
    exact weak_duality hP g hg A B hgb s hs.2
  have hs0 : ((B / 2) • (1 : Matrix (Fin r) (Fin r) ℝ), (0 : Fin r → ℝ), A + B * r / 2) ∈ DF :=
    ⟨by ext i j; simp [Matrix.one_apply, eq_comm], dual_point g A B hB hgb⟩
  have hbdd : BddAbove PV := ⟨_, fun v hv => hweak v hv _ hs0⟩
  have hLUB : IsLUB PV (sSup PV) := isLUB_csSup hne hbdd
  set S := sSup PV with hS
  have hlb : ∀ s ∈ DF, S ≤ MinimaxSLP.RhsSDP.dualObj μ Q s :=
    fun s hs => csSup_le hne (fun v hv => hweak v hv s hs)
  -- the separation step
  have hsep : ∀ ε > 0, ∃ s ∈ DF, MinimaxSLP.RhsSDP.dualObj μ Q s ≤ S + ε := by
    intro ε hε
    set xs : EE r := ((1 : ℝ), μ, Q, S + ε) with hxs
    have hxsH : xs ∉ HH g := by
      rintro ⟨w, hw, h0, h1, h2, h3⟩
      simp only [hxs] at h0 h1 h2 h3
      rw [hQs] at h2
      obtain ⟨hm, hint⟩ := toMeas_mem' w hw μ Q g h0.symm h1.symm h2.symm
      have : ∫ h, g h ∂(toMeas w) ≤ S := hLUB.1 ⟨_, hm, rfl⟩
      linarith
    obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point (convex_HH g).interior isOpen_interior
      (fun h => hxsH (interior_subset h))
    have hint_ne : (interior (HH g)).Nonempty := ⟨_, hx0⟩
    have hall : ∀ a ∈ HH g, f a ≤ f xs := by
      intro a ha
      have hcl : a ∈ closure (interior (HH g)) := by
        rw [(convex_HH g).closure_interior_eq_closure_of_nonempty_interior hint_ne]
        exact subset_closure ha
      have hclosed : IsClosed {b : EE r | f b ≤ f xs} := isClosed_le f.continuous continuous_const
      exact closure_minimal (fun b hb => (hf b hb).le) hclosed hcl
    set l0 := f (1, 0, 0, 0) with hl0
    set l1 : Fin r → ℝ := fun i => f (0, Pi.single i 1, 0, 0) with hl1
    set Λ : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun i j => f (0, 0, Matrix.single i j 1, 0)
      with hΛ
    set τ := f (0, 0, 0, 1) with hτ
    have hdec : ∀ z : EE r, f z = z.1 * l0 + ∑ i, z.2.1 i * l1 i +
        ∑ i, ∑ j, z.2.2.1 i j * Λ i j + z.2.2.2 * τ := fun z => decomp f z
    -- tau ≥ 0
    obtain ⟨w0, hw0, h00, h01, h02, h03⟩ := interior_subset hx0
    have hfxs : f xs = 1 * l0 + ∑ i, μ i * l1 i + ∑ i, ∑ j, Q i j * Λ i j + (S + ε) * τ :=
      hdec _
    have hfx0 : f ((1 : ℝ), μ, Q, t0) =
        1 * l0 + ∑ i, μ i * l1 i + ∑ i, ∑ j, Q i j * Λ i j + t0 * τ := hdec _
    have hshift : ∀ sh : ℝ, f ((1 : ℝ), μ, Q, t0 - sh) =
        1 * l0 + ∑ i, μ i * l1 i + ∑ i, ∑ j, Q i j * Λ i j + (t0 - sh) * τ := fun sh => hdec _
    have hlt := hf _ hx0
    have hτ0 : 0 ≤ τ := by
      by_contra hneg
      push Not at hneg
      set sh := (f xs - f ((1 : ℝ), μ, Q, t0) + 1) / (-τ) with hsh
      have hshp : 0 ≤ sh := div_nonneg (by linarith) (by linarith)
      have hmem : ((1 : ℝ), μ, Q, t0 - sh) ∈ HH g := by
        refine ⟨w0, hw0, h00, h01, h02, ?_⟩
        simp only at h03 ⊢
        linarith
      have h1 := hall _ hmem
      have e : sh * τ = -(f xs - f ((1 : ℝ), μ, Q, t0) + 1) := by
        have hτne : τ ≠ 0 := hneg.ne
        rw [hsh, div_mul_eq_mul_div, mul_div_assoc, div_neg, div_self hτne]; ring
      rw [hshift] at h1
      nlinarith
    have hτpos : 0 < τ := by
      rcases hτ0.lt_or_eq with h | h
      · exact h
      · rw [hfx0, hfxs, ← h] at hlt
        simp only [mul_zero, add_zero] at hlt
        exact absurd hlt (lt_irrefl _)
    -- pointwise inequality
    have hK : ∀ p : Fin r → ℝ, l0 + ∑ i, p i * l1 i + ∑ i, ∑ j, (p i * p j) * Λ i j +
        g p * τ ≤ 0 := by
      intro p
      by_contra hpos
      push Not at hpos
      set K := l0 + ∑ i, p i * l1 i + ∑ i, ∑ j, (p i * p j) * Λ i j + g p * τ with hKdef
      set c := (|f xs| + 1) / K with hc
      have hcpos : 0 < c := div_pos (by positivity) hpos
      have hmem : (c, c • p, c • vecMulVec p p, c * g p) ∈ HH g := by
        refine ⟨Finsupp.single p c, fun q => ?_, ?_, ?_, ?_, ?_⟩
        · rw [Finsupp.single_apply]; split_ifs <;> linarith
        · simp [L0, Finsupp.linearCombination_single]
        · simp [L1, Finsupp.linearCombination_single]
        · simp only [L2, Finsupp.linearCombination_single]
          ext i j
          simp [symm_apply, vecMulVec_apply]; ring
        · simp [Lg, Finsupp.linearCombination_single]
      have h1 := hall _ hmem
      rw [hdec] at h1
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, vecMulVec_apply] at h1
      have e : c * l0 + ∑ i, c * p i * l1 i + ∑ i, ∑ j, c * (p i * p j) * Λ i j +
          c * g p * τ = c * K := by
        rw [hKdef]
        simp only [mul_add, Finset.mul_sum]
        congr 1; congr 1; congr 1
        · exact Finset.sum_congr rfl (fun i _ => by ring)
        · exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
        · ring
      rw [e, hc, div_mul_cancel₀ _ hpos.ne'] at h1
      have := le_abs_self (f xs)
      linarith
    -- origin
    have h0mem : (0 : EE r) ∈ HH g := by
      refine ⟨0, fun _ => le_refl _, ?_, ?_, ?_, ?_⟩ <;> simp [symm]
    have hO := hall _ h0mem
    rw [map_zero, hdec xs] at hO
    simp only [hxs] at hO
    -- the dual point
    refine ⟨(-(1 / τ) • symm Λ, -(1 / τ) • l1, -(l0 / τ)), ⟨?_, fun h => ?_⟩, ?_⟩
    · have := symm_isSymm Λ
      ext i j
      simp only [transpose_apply, Matrix.smul_apply]
      rw [this.apply i j]
    · simp only [smul_mulVec, dotProduct_smul, quad_symm, smul_dotProduct, smul_eq_mul]
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
      set X1 := ∑ i, l1 i * h i with hX1
      set X2 := ∑ i, ∑ j, Λ i j * (h i * h j) with hX2
      have eq1 : ∑ i, h i * l1 i = X1 := Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      have eq2 : ∑ i, ∑ j, (h i * h j) * Λ i j = X2 :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => mul_comm _ _))
      have hk : l0 + X1 + X2 + g h * τ ≤ 0 := by linarith [hK h]
      rw [show -(1 / τ) * X2 + -(1 / τ) * X1 + -(l0 / τ) = -(l0 + X1 + X2) / τ by
        field_simp; ring]
      rw [le_div_iff₀ hτpos]
      linarith
    · unfold MinimaxSLP.RhsSDP.dualObj
      simp only
      have ef : MinimaxSLP.ObjSDP.frob Q (-(1 / τ) • symm Λ) =
          -(1 / τ) * MinimaxSLP.ObjSDP.frob Q (symm Λ) := by
        unfold MinimaxSLP.ObjSDP.frob
        simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
      rw [ef, frob_symm Q Λ hQ, dotProduct_smul, smul_eq_mul]
      simp only [dotProduct]
      have e1 : ∑ i, μ i * l1 i = ∑ i, μ i * l1 i := rfl
      have key : -(1 / τ) * ∑ i, ∑ j, Λ i j * Q i j + -(1 / τ) * ∑ i, μ i * l1 i + -(l0 / τ) =
          -(l0 + ∑ i, μ i * l1 i + ∑ i, ∑ j, Q i j * Λ i j) / τ := by
        have : ∑ i, ∑ j, Λ i j * Q i j = ∑ i, ∑ j, Q i j * Λ i j :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => mul_comm _ _))
        rw [this]; field_simp; ring
      rw [key, div_le_iff₀ hτpos]
      linarith
  refine ⟨hLUB, ⟨fun v ⟨s, hs, hv⟩ => hv ▸ hlb s hs, fun L hL => ?_⟩⟩
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨s, hs, hle⟩ := hsep ε hε
  exact (hL ⟨s, hs, rfl⟩).trans hle

end SDAux


open MeasureTheory Matrix

namespace SDAux

lemma Wdot {r d : ℕ} (W : Matrix (Fin r) (Fin d) ℝ) (w : Fin d → ℝ) (π : Fin r → ℝ) :
    (W *ᵥ w) ⬝ᵥ π = w ⬝ᵥ (Wᵀ *ᵥ π) := by
  rw [mulVec_transpose, dotProduct_comm, dotProduct_mulVec, dotProduct_comm]

lemma dual_box {r d : ℕ} (W : Matrix (Fin r) (Fin d) ℝ) (q : Fin d → ℝ)
    (hA2 : ∀ z : Fin r → ℝ, ∃ w : Fin d → ℝ, 0 ≤ w ∧ W *ᵥ w = z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q → ∀ i, |π i| ≤ C := by
  choose wf hwf0 hwf using hA2
  let wp : Fin r → Fin d → ℝ := fun i => wf (Pi.single i 1)
  let wm : Fin r → Fin d → ℝ := fun i => wf (-Pi.single i 1)
  refine ⟨∑ i, (|wp i ⬝ᵥ q| + |wm i ⬝ᵥ q|), Finset.sum_nonneg (fun i _ => by positivity),
    fun π hπ i => ?_⟩
  have h1 : π i ≤ wp i ⬝ᵥ q := by
    have e : π i = (W *ᵥ wp i) ⬝ᵥ π := by simp [wp, hwf]
    rw [e, Wdot]
    exact dotProduct_le_dotProduct_of_nonneg_left hπ (hwf0 _)
  have h2 : -π i ≤ wm i ⬝ᵥ q := by
    have e : -π i = (W *ᵥ wm i) ⬝ᵥ π := by simp [wm, hwf]
    rw [e, Wdot]
    exact dotProduct_le_dotProduct_of_nonneg_left hπ (hwf0 _)
  have h3 : |wp i ⬝ᵥ q| + |wm i ⬝ᵥ q| ≤ ∑ i, (|wp i ⬝ᵥ q| + |wm i ⬝ᵥ q|) :=
    Finset.single_le_sum (f := fun i => |wp i ⬝ᵥ q| + |wm i ⬝ᵥ q|)
      (fun i _ => by positivity) (Finset.mem_univ i)
  rw [abs_le]
  constructor
  · linarith [le_abs_self (wm i ⬝ᵥ q), abs_nonneg (wp i ⬝ᵥ q)]
  · linarith [le_abs_self (wp i ⬝ᵥ q), abs_nonneg (wm i ⬝ᵥ q)]

lemma dot_abs_le {r : ℕ} (C : ℝ) (π u : Fin r → ℝ) (hπ : ∀ i, |π i| ≤ C) :
    |u ⬝ᵥ π| ≤ C * ∑ i, |u i| := by
  unfold dotProduct
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [abs_mul, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hπ i) (abs_nonneg _)

lemma Qval_props {r d n : ℕ} (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ)
    (q : Fin d → ℝ) (hA3 : ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q) (x : Fin n → ℝ)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q → ∀ i, |π i| ≤ C) :
    (∀ h h' : Fin r → ℝ, MinimaxSLP.RhsSDP.Qval W T q h x ≤
        MinimaxSLP.RhsSDP.Qval W T q h' x + C * ∑ i, |h i - h' i|) ∧
    (∀ h : Fin r → ℝ, |MinimaxSLP.RhsSDP.Qval W T q h x| ≤ C * ∑ i, |(h - T *ᵥ x) i|) := by
  obtain ⟨π0, hπ0⟩ := hA3
  have hbdd : ∀ h : Fin r → ℝ, BddAbove ((fun π => (h - T *ᵥ x) ⬝ᵥ π) ''
      {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q}) := by
    intro h
    refine ⟨C * ∑ i, |(h - T *ᵥ x) i|, ?_⟩
    rintro v ⟨π, hπ, rfl⟩
    exact (le_abs_self _).trans (dot_abs_le C π _ (hC π hπ))
  have hne : ∀ h : Fin r → ℝ, ((fun π => (h - T *ᵥ x) ⬝ᵥ π) ''
      {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q}).Nonempty := fun h => ⟨_, π0, hπ0, rfl⟩
  refine ⟨fun h h' => ?_, fun h => ?_⟩
  · unfold MinimaxSLP.RhsSDP.Qval
    refine csSup_le (hne h) ?_
    rintro v ⟨π, hπ, rfl⟩
    have e : (h - T *ᵥ x) ⬝ᵥ π = (h' - T *ᵥ x) ⬝ᵥ π + (h - h') ⬝ᵥ π := by
      rw [← add_dotProduct]; congr 1; abel
    show (h - T *ᵥ x) ⬝ᵥ π ≤ _
    rw [e]
    have h1 : (h' - T *ᵥ x) ⬝ᵥ π ≤ sSup ((fun π => (h' - T *ᵥ x) ⬝ᵥ π) ''
        {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q}) := le_csSup (hbdd h') ⟨π, hπ, rfl⟩
    have h2 := (le_abs_self _).trans (dot_abs_le C π (h - h') (hC π hπ))
    simp only [Pi.sub_apply] at h2
    linarith
  · unfold MinimaxSLP.RhsSDP.Qval
    rw [abs_le]
    constructor
    · have h1 : (h - T *ᵥ x) ⬝ᵥ π0 ≤ sSup ((fun π => (h - T *ᵥ x) ⬝ᵥ π) ''
          {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q}) := le_csSup (hbdd h) ⟨π0, hπ0, rfl⟩
      have h2 := neg_abs_le ((h - T *ᵥ x) ⬝ᵥ π0)
      have h3 := dot_abs_le C π0 (h - T *ᵥ x) (hC π0 hπ0)
      linarith
    · refine csSup_le (hne h) ?_
      rintro v ⟨π, hπ, rfl⟩
      exact (le_abs_self _).trans (dot_abs_le C π _ (hC π hπ))

lemma U_abs {K : ℕ} [NeZero K] (α β : Fin K → ℝ) (t : ℝ) :
    |MinimaxSLP.ObjSDP.disutility α β t| ≤ ∑ k, (|α k| * |t| + |β k|) := by
  have hk : ∀ k, |α k * t + β k| ≤ ∑ k, (|α k| * |t| + |β k|) := by
    intro k
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    exact Finset.single_le_sum (f := fun k => |α k| * |t| + |β k|)
      (fun k _ => by positivity) (Finset.mem_univ k)
  unfold MinimaxSLP.ObjSDP.disutility
  rw [abs_le]
  constructor
  · have := Finset.le_sup' (fun k => α k * t + β k) (Finset.mem_univ (0 : Fin K))
    have h2 := neg_abs_le (α 0 * t + β 0)
    linarith [hk 0]
  · exact Finset.sup'_le _ _ (fun k _ => (le_abs_self _).trans (hk k))

end SDAux

open SDAux in
theorem solution {r d n K : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ)
    (α β : Fin K → ℝ) (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ)
    (hα : ∀ k, 0 ≤ α k)
    (hA2 : ∀ z : Fin r → ℝ, ∃ w : Fin d → ℝ, 0 ≤ w ∧ W *ᵥ w = z)
    (hA3 : ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (x : Fin n → ℝ) :
    IsLUB (MinimaxSLP.RhsSDP.primalValues W T q α β μ Q x) (MinimaxSLP.RhsSDP.Zhat W T q α β μ Q x) ∧
      IsGLB (MinimaxSLP.RhsSDP.dualObj μ Q '' MinimaxSLP.RhsSDP.dualFeasible12 W T q α β x)
        (MinimaxSLP.RhsSDP.Zhat W T q α β μ Q x) ∧
      MinimaxSLP.RhsSDP.Zhat W T q α β μ Q x = MinimaxSLP.RhsSDP.ZhatD W T q α β μ Q x := by
  obtain ⟨C, hC0, hC⟩ := dual_box W q hA2
  obtain ⟨hlip, habs⟩ := Qval_props W T q hA3 x C hC0 hC
  set g : (Fin r → ℝ) → ℝ := fun h =>
    MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x) with hg
  -- continuity
  have hQc : Continuous (fun h : Fin r → ℝ => MinimaxSLP.RhsSDP.Qval W T q h x) := by
    refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (C * r)) (fun h h' => ?_)).continuous
    rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    have hs : ∑ i, |h i - h' i| ≤ r * dist h h' := by
      calc ∑ i, |h i - h' i| ≤ ∑ _i : Fin r, dist h h' := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            rw [← Real.dist_eq]; exact dist_le_pi_dist h h' i
        _ = r * dist h h' := by simp
    rw [abs_le]
    constructor
    · have := hlip h' h
      have e : ∑ i, |h' i - h i| = ∑ i, |h i - h' i| :=
        Finset.sum_congr rfl (fun i _ => abs_sub_comm _ _)
      nlinarith
    · have := hlip h h'
      nlinarith
  have hgc : Continuous g := by
    simp only [hg, MinimaxSLP.ObjSDP.disutility]
    exact Continuous.finset_sup'_apply _ (fun k _ => (continuous_const.mul hQc).add continuous_const)
  -- growth bound
  set Sa := ∑ k, |α k| with hSa
  set Sb := ∑ k, |β k| with hSb
  set D := C * ∑ i, |(T *ᵥ x) i| with hD
  have hgb : ∀ h, |g h| ≤ (Sa * D + Sb) + (Sa * C) * ∑ i, |h i| := by
    intro h
    have h1 := U_abs α β (MinimaxSLP.RhsSDP.Qval W T q h x)
    have h2 := habs h
    have h3 : ∑ i, |(h - T *ᵥ x) i| ≤ ∑ i, |h i| + ∑ i, |(T *ᵥ x) i| := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun i _ => by simp only [Pi.sub_apply]; exact abs_sub _ _)
    have h4 : ∑ k, (|α k| * |MinimaxSLP.RhsSDP.Qval W T q h x| + |β k|) =
        Sa * |MinimaxSLP.RhsSDP.Qval W T q h x| + Sb := by
      rw [Finset.sum_add_distrib, Finset.sum_mul]
    have hSa0 : 0 ≤ Sa := Finset.sum_nonneg (fun k _ => abs_nonneg _)
    rw [h4] at h1
    have h5 : |MinimaxSLP.RhsSDP.Qval W T q h x| ≤ C * ∑ i, |h i| + D := by
      rw [hD]; nlinarith
    show |g h| ≤ _
    nlinarith [mul_le_mul_of_nonneg_left h5 hSa0]
  have hB : 0 ≤ Sa * C := mul_nonneg (Finset.sum_nonneg (fun k _ => abs_nonneg _)) hC0
  obtain ⟨hLUB, hGLB⟩ := moment_duality g hgc _ _ hB hgb μ Q hQ hA4
  have hGLB' : IsGLB (MinimaxSLP.RhsSDP.dualObj μ Q '' MinimaxSLP.RhsSDP.dualFeasible12 W T q α β x)
      (MinimaxSLP.RhsSDP.Zhat W T q α β μ Q x) := hGLB
  refine ⟨hLUB, hGLB', ?_⟩
  unfold MinimaxSLP.RhsSDP.ZhatD
  exact (hGLB'.csInf_eq (by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne] at hGLB'
    have := hGLB'.2 (show MinimaxSLP.RhsSDP.Zhat W T q α β μ Q x + 1 ∈ lowerBounds (∅ : Set ℝ) by
      simp)
    linarith)).symm
