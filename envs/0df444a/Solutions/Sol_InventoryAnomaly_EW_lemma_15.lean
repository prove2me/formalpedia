-- Prove2me | solution 1 for InventoryAnomaly.EW.lemma_15
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T08:33:04.540116+00:00
-- url     : https://prove2.me/submissions/528b6a5d-b86f-475f-ae90-6089b73c78fd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_InventoryAnomaly_EW_Model
import Theorems.Thm_InventoryAnomaly_EW_theorem_2

open MeasureTheory ProbabilityTheory
open scoped NNReal
open InventoryAnomaly.EW

lemma IA15_phi_le_one (k : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    Real.exp (-z) * z ^ k / (Nat.factorial k) ≤ 1 := by
  have h := hasSum_one_poissonMeasure z.toNNReal
  have := le_hasSum h k (fun j _ => by positivity)
  simpa [Real.coe_toNNReal z hz] using this

lemma IA15_phi_lip (k : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x) * x ^ k / (Nat.factorial k) - Real.exp (-y) * y ^ k / (Nat.factorial k)| ≤
      |x - y| := by
  have hder : ∀ z, HasDerivAt (fun z : ℝ => Real.exp (-z) * z ^ k / (Nat.factorial k))
      ((Real.exp (-z) * ((k : ℝ) * z ^ (k - 1)) - Real.exp (-z) * z ^ k) / (Nat.factorial k)) z := by
    intro z
    have h1 : HasDerivAt (fun z : ℝ => Real.exp (-z)) (-Real.exp (-z)) z := by
      simpa using (hasDerivAt_neg z).exp
    have h2 : HasDerivAt (fun z : ℝ => z ^ k) ((k : ℝ) * z ^ (k - 1)) z := hasDerivAt_pow k z
    have := (h1.fun_mul h2).div_const (Nat.factorial k : ℝ)
    refine this.congr_deriv ?_
    ring
  have hbound : ∀ z ∈ Set.Ici (0 : ℝ),
      ‖(Real.exp (-z) * ((k : ℝ) * z ^ (k - 1)) - Real.exp (-z) * z ^ k) / (Nat.factorial k)‖ ≤ 1 := by
    intro z hz
    have hz : 0 ≤ z := hz
    have hb : Real.exp (-z) * z ^ k / (Nat.factorial k) ≤ 1 := IA15_phi_le_one k z hz
    have hb0 : 0 ≤ Real.exp (-z) * z ^ k / (Nat.factorial k) := by positivity
    have ha : Real.exp (-z) * ((k : ℝ) * z ^ (k - 1)) / (Nat.factorial k) ≤ 1 := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · subst h0; norm_num
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have := IA15_phi_le_one j z hz
        calc Real.exp (-z) * (((j + 1 : ℕ) : ℝ) * z ^ (j + 1 - 1)) / (Nat.factorial (j + 1)) =
            Real.exp (-z) * z ^ j / (Nat.factorial j) := by
              rw [Nat.factorial_succ, Nat.add_sub_cancel]; push_cast
              field_simp
          _ ≤ 1 := this
    have ha0 : 0 ≤ Real.exp (-z) * ((k : ℝ) * z ^ (k - 1)) / (Nat.factorial k) := by positivity
    rw [Real.norm_eq_abs, sub_div, abs_le]
    constructor <;> linarith
  have := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (hder z).hasDerivWithinAt) hbound (Set.mem_Ici.2 hy) (Set.mem_Ici.2 hx)
  simpa [Real.norm_eq_abs] using this

lemma IA15_pois_lip (k : ℕ) (M M' : ℝ) : |poisPmf M k - poisPmf M' k| ≤ |M - M'| := by
  unfold poisPmf poissonPMFReal
  rw [Real.coe_toNNReal', Real.coe_toNNReal']
  exact (IA15_phi_lip k _ _ (le_max_right _ _) (le_max_right _ _)).trans
    (abs_max_sub_max_le_abs _ _ _)

lemma IA15_toNNReal_max (M : ℝ) : (max M 0).toNNReal = M.toNNReal := by
  ext; simp [Real.coe_toNNReal']

lemma IA15_anom_lip {d : ℕ} {I : Instance d} {cM cA Csp K L μ : ℝ} (hI : I.Model cM cA Csp K L μ)
    (hK : 0 ≤ K) (α : EuclideanSpace ℝ (Fin d)) (hα : α ∈ I.model.Γ) (k : ℕ) (M M' : ℝ) :
    |I.model.pmf α M k - I.model.pmf α M' k| ≤ K * |M - M'| := by
  have e1 : ∀ N : ℝ, I.model.pmf α N k = I.model.pmf α (max N 0) k := by
    intro N; unfold AnomModel.pmf; rw [IA15_toNNReal_max]
  rw [e1 M, e1 M']
  have := hI.smooth k (α, max M 0) ⟨hα, Set.mem_Ici.2 (le_max_right _ _)⟩ (α, max M' 0)
    ⟨hα, Set.mem_Ici.2 (le_max_right _ _)⟩
  have hd : dist (α, max M 0) (α, max M' 0) = |max M 0 - max M' 0| := by
    simp [Prod.dist_eq, Real.dist_eq]
  rw [hd] at this
  exact this.trans (mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs _ _ _) hK)

lemma IA15_gt_diff {d : ℕ} {I : Instance d} {cM cA Csp K L μ : ℝ} (hI : I.Model cM cA Csp K L μ)
    (hK : 0 ≤ K) (hcA : 0 < cA) (θ : EuclideanSpace ℝ (Fin (d + 1))) (hθ : θ ∈ I.Θ cA)
    (A B : Matrix (Fin I.n) (Fin I.m) ℝ) (D : ℝ) (hD : 0 ≤ D) (hAB : ∀ i j, |A i j - B i j| ≤ D)
    (t : ℕ) : |I.gt θ A t - I.gt θ B t| ≤ (t + 1) * (K + 1) * D := by
  obtain ⟨hα, hp0, hp1⟩ := hθ
  have hn0 : 0 < I.n := by have := hI.two_le_m; have := hI.m_le_n; omega
  have hm0 : 0 < I.m := by have := hI.two_le_m; omega
  set p := pAOf θ
  set α := alphaOf θ
  have hp1' : p ≤ 1 := by linarith
  have hterm : ∀ i j, |(p * I.model.cdf α (A i j) t + (1 - p) * poisCdf (A i j) t) -
      (p * I.model.cdf α (B i j) t + (1 - p) * poisCdf (B i j) t)| ≤ (t + 1) * (K + 1) * D := by
    intro i j
    have hc : |I.model.cdf α (A i j) t - I.model.cdf α (B i j) t| ≤ (t + 1) * (K * D) := by
      unfold AnomModel.cdf
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k ∈ Finset.range (t + 1), |I.model.pmf α (A i j) k - I.model.pmf α (B i j) k|
          ≤ ∑ k ∈ Finset.range (t + 1), K * D := Finset.sum_le_sum fun k _ =>
            (IA15_anom_lip hI hK α hα k _ _).trans (mul_le_mul_of_nonneg_left (hAB i j) hK)
        _ = (t + 1) * (K * D) := by simp
    have hq : |poisCdf (A i j) t - poisCdf (B i j) t| ≤ (t + 1) * D := by
      unfold poisCdf
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k ∈ Finset.range (t + 1), |poisPmf (A i j) k - poisPmf (B i j) k|
          ≤ ∑ k ∈ Finset.range (t + 1), D := Finset.sum_le_sum fun k _ =>
            (IA15_pois_lip k _ _).trans (hAB i j)
        _ = (t + 1) * D := by simp
    have heq : (p * I.model.cdf α (A i j) t + (1 - p) * poisCdf (A i j) t) -
        (p * I.model.cdf α (B i j) t + (1 - p) * poisCdf (B i j) t) =
        p * (I.model.cdf α (A i j) t - I.model.cdf α (B i j) t) +
          (1 - p) * (poisCdf (A i j) t - poisCdf (B i j) t) := by ring
    rw [heq]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hp0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - p)]
    have h1 := mul_le_mul_of_nonneg_left hc hp0
    have h2 := mul_le_mul_of_nonneg_left hq (by linarith : (0 : ℝ) ≤ 1 - p)
    have h3 : p * ((t + 1) * (K * D)) ≤ (t + 1) * (K * D) := by
      have : 0 ≤ (t + 1 : ℝ) * (K * D) := by positivity
      nlinarith
    have h4 : (1 - p) * ((t + 1) * D) ≤ (t + 1) * D := by
      have : 0 ≤ (t + 1 : ℝ) * D := by positivity
      nlinarith
    nlinarith
  unfold Instance.gt
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  have hnm : (0 : ℝ) < I.n * I.m := by positivity
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (I.n * I.m))]
  calc 1 / ((I.n : ℝ) * I.m) * |∑ i, ∑ j, ((p * I.model.cdf α (A i j) t + (1 - p) * poisCdf (A i j) t) -
        (p * I.model.cdf α (B i j) t + (1 - p) * poisCdf (B i j) t))|
      ≤ 1 / ((I.n : ℝ) * I.m) * ∑ _i : Fin I.n, ∑ _j : Fin I.m, (t + 1) * (K + 1) * D := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hterm i j)
    _ = (t + 1) * (K + 1) * D := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

theorem solution (d : ℕ) (cM cA : ℝ) (hcM : 0 < cM) (hcA : 0 < cA) (hcA1 : cA < 1) :
    ∃ Csp C C' : ℝ, 0 < Csp ∧ 0 < C ∧ 0 < C' ∧
      ∀ (I : Instance d) (K L μ : ℝ) (hI : I.Model cM cA Csp K L μ),
        I.SparsityMax hI.r_pos Csp μ L →
        ∀ (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ),
        IsBestRankApprox I.r svdr →
        1 - C' / (I.n * I.m) ≤ I.law.real {ω | ∀ θ ∈ I.Θ cA, ∀ t ≤ d + 1,
          |I.gt θ ((I.model.e I.θstar / I.model.e θ) • I.Mstar) t -
            I.gt θ ((I.model.e θ)⁻¹ • I.Mhat svdr (I.obs ω)) t| ≤
              C * (K + L) * I.δ' hI.r_pos μ L} := by
  obtain ⟨Csp, C2, C2', hCsp, hC2, hC2', H2⟩ := theorem_2 d cM cA hcM hcA hcA1
  refine ⟨Csp, (d + 2) * C2 / cA * (1 + 1 / cM), C2', hCsp, by positivity, hC2', ?_⟩
  intro I K L μ hI hS svdr hsvd
  have E := H2 I K L μ hI hS svdr hsvd
  have hP : IsProbabilityMeasure I.law := by unfold Instance.law; infer_instance
  have hn0 : 0 < I.n := by have := hI.two_le_m; have := hI.m_le_n; omega
  have hm0 : 0 < I.m := by have := hI.two_le_m; omega
  have hL : 0 ≤ L := (abs_nonneg _).trans (hI.max_ub ⟨0, hn0⟩ ⟨0, hm0⟩)
  have hK : 0 ≤ K := by
    have := hI.smooth 0 (I.αstar, 0) ⟨hI.α_mem, Set.mem_Ici.2 le_rfl⟩ (I.αstar, 1)
      ⟨hI.α_mem, Set.mem_Ici.2 zero_le_one⟩
    have hd : dist ((I.αstar, (0 : ℝ))) (I.αstar, (1 : ℝ)) = 1 := by
      simp [Prod.dist_eq, Real.dist_eq]
    rw [hd, mul_one] at this
    exact (abs_nonneg _).trans this
  have hLcM : cM ≤ L := by
    obtain ⟨i, j, h⟩ := hI.max_lb
    exact h.trans ((le_abs_self _).trans (hI.max_ub i j))
  have hμ : 0 ≤ μ := by
    have h := hI.incoh_U ⟨0, hn0⟩
    have h0 : 0 ≤ ∑ k, I.U ⟨0, hn0⟩ k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    by_contra hneg'
    have hneg : μ < 0 := lt_of_not_ge hneg'
    have hr' : (0 : ℝ) < I.r := by exact_mod_cast hI.r_pos
    have hn' : (0 : ℝ) < I.n := by exact_mod_cast hn0
    have : μ * I.r / I.n < 0 := div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg hr') hn'
    linarith
  have hκ0 : 0 ≤ I.κ hI.r_pos := by
    unfold Instance.κ
    exact div_nonneg (hI.σ_pos _).le (hI.σ_pos _).le
  have hδ0 : 0 ≤ I.δ' hI.r_pos μ L := by unfold Instance.δ'; positivity
  refine E.trans (measureReal_mono ?_)
  intro ω hω θ hθ t ht
  have he : cA ≤ I.model.e θ := by
    obtain ⟨hα, hp0, hp1⟩ := hθ
    unfold AnomModel.e
    have := (hI.g_mem (alphaOf θ)).1
    have : 0 ≤ pAOf θ * I.model.g (alphaOf θ) := mul_nonneg hp0 this
    linarith
  have hepos : 0 < I.model.e θ := lt_of_lt_of_le hcA he
  have hAB : ∀ i j, |((I.model.e I.θstar / I.model.e θ) • I.Mstar) i j -
      ((I.model.e θ)⁻¹ • I.Mhat svdr (I.obs ω)) i j| ≤ C2 * I.δ' hI.r_pos μ L / cA := by
    intro i j
    have h := hω i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h ⊢
    have heq : I.model.e I.θstar / I.model.e θ * I.Mstar i j -
        (I.model.e θ)⁻¹ * I.Mhat svdr (I.obs ω) i j =
        -(I.Mhat svdr (I.obs ω) i j - I.model.e I.θstar * I.Mstar i j) / I.model.e θ := by
      field_simp; ring
    rw [heq, abs_div, abs_neg, abs_of_pos hepos]
    calc |I.Mhat svdr (I.obs ω) i j - I.model.e I.θstar * I.Mstar i j| / I.model.e θ
        ≤ C2 * I.δ' hI.r_pos μ L / I.model.e θ := div_le_div_of_nonneg_right h hepos.le
      _ ≤ C2 * I.δ' hI.r_pos μ L / cA :=
          div_le_div_of_nonneg_left (by positivity) hcA he
  have hg := IA15_gt_diff hI hK hcA θ hθ _ _ _ (by positivity) hAB t
  refine hg.trans ?_
  have ht' : (t : ℝ) + 1 ≤ d + 2 := by
    have : (t : ℝ) ≤ d + 1 := by exact_mod_cast ht
    linarith
  have hK1 : K + 1 ≤ (1 + 1 / cM) * (K + L) := by
    have : 1 ≤ L / cM := by rw [le_div_iff₀ hcM]; linarith
    have h2 : (1 + 1 / cM) * (K + L) = K + L + K / cM + L / cM := by ring
    have : 0 ≤ K / cM := by positivity
    linarith
  calc ((t : ℝ) + 1) * (K + 1) * (C2 * I.δ' hI.r_pos μ L / cA)
      ≤ (d + 2) * ((1 + 1 / cM) * (K + L)) * (C2 * I.δ' hI.r_pos μ L / cA) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul ht' hK1 (by linarith) (by positivity)
    _ = (d + 2) * C2 / cA * (1 + 1 / cM) * (K + L) * I.δ' hI.r_pos μ L := by ring
