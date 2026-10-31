-- Prove2me | solution 1 for InventoryAnomaly.EW.lemma_18_spmax
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T08:58:36.460806+00:00
-- url     : https://prove2.me/submissions/df94f656-6b98-4e7a-bbee-28e97306d7d7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_InventoryAnomaly_EW_Model
import Theorems.Thm_InventoryAnomaly_EW_theorem_2
import Theorems.Thm_InventoryAnomaly_EW_lemma_1_spmax

open MeasureTheory ProbabilityTheory
open scoped NNReal Nat
open InventoryAnomaly.EW

lemma IA18_model_mono {d : ℕ} {I : Instance d} {cM cA Csp Csp' K L μ : ℝ}
    (hI : I.Model cM cA Csp K L μ) (hle : Csp' ≤ Csp) : I.Model cM cA Csp' K L μ := by
  have hn0 : 0 < I.n := by have := hI.two_le_m; have := hI.m_le_n; omega
  have hμ : 0 ≤ μ := by
    have h := hI.incoh_U ⟨0, hn0⟩
    have h0 : 0 ≤ ∑ k, I.U ⟨0, hn0⟩ k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    by_contra hneg'
    have hneg : μ < 0 := lt_of_not_ge hneg'
    have hr' : (0 : ℝ) < I.r := by exact_mod_cast hI.r_pos
    have hn' : (0 : ℝ) < I.n := by exact_mod_cast hn0
    have : μ * I.r / I.n < 0 := div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg hr') hn'
    linarith
  refine { hI with sparsity := ?_ }
  have hX : 0 ≤ Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * I.κ hI.r_pos ^ 2 / Real.sqrt I.m := by
    have : 0 ≤ Real.log I.m := Real.log_natCast_nonneg _
    positivity
  have h := hI.sparsity
  calc Csp' * Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * I.κ hI.r_pos ^ 2 / Real.sqrt I.m
      = Csp' * (Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * I.κ hI.r_pos ^ 2 / Real.sqrt I.m) := by ring
    _ ≤ Csp * (Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * I.κ hI.r_pos ^ 2 / Real.sqrt I.m) :=
        mul_le_mul_of_nonneg_right hle hX
    _ = _ := by ring
    _ ≤ _ := h

lemma IA18_spmax_mono {d : ℕ} {I : Instance d} {cM cA Csp Csp' K L μ : ℝ}
    (hI : I.Model cM cA Csp K L μ) (hS : I.SparsityMax hI.r_pos Csp μ L) (hle : Csp' ≤ Csp) :
    I.SparsityMax hI.r_pos Csp' μ L := by
  have hn0 : 0 < I.n := by have := hI.two_le_m; have := hI.m_le_n; omega
  have hm0 : 0 < I.m := by have := hI.two_le_m; omega
  have hL : 0 ≤ L := (abs_nonneg _).trans (hI.max_ub ⟨0, hn0⟩ ⟨0, hm0⟩)
  have hμ : 0 ≤ μ := by
    have h := hI.incoh_U ⟨0, hn0⟩
    have h0 : 0 ≤ ∑ k, I.U ⟨0, hn0⟩ k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    by_contra hneg'
    have hneg : μ < 0 := lt_of_not_ge hneg'
    have hr' : (0 : ℝ) < I.r := by exact_mod_cast hI.r_pos
    have hn' : (0 : ℝ) < I.n := by exact_mod_cast hn0
    have : μ * I.r / I.n < 0 := div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg hr') hn'
    linarith
  intro i₀ j₀ hmax
  have h := hS i₀ j₀ hmax
  have hM0 : 0 ≤ I.Mstar i₀ j₀ := hI.nonneg i₀ j₀
  have hX : 0 ≤ Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * L * I.κ hI.r_pos ^ 2 /
      (I.Mstar i₀ j₀ * Real.sqrt I.m) := by
    have : 0 ≤ Real.log I.m := Real.log_natCast_nonneg _
    positivity
  calc Csp' * Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * L * I.κ hI.r_pos ^ 2 /
        (I.Mstar i₀ j₀ * Real.sqrt I.m)
      = Csp' * (Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * L * I.κ hI.r_pos ^ 2 /
        (I.Mstar i₀ j₀ * Real.sqrt I.m)) := by ring
    _ ≤ Csp * (Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * L * I.κ hI.r_pos ^ 2 /
        (I.Mstar i₀ j₀ * Real.sqrt I.m)) := mul_le_mul_of_nonneg_right hle hX
    _ = _ := by ring
    _ ≤ _ := h

lemma IA18_poisPmf_le_one (M : ℝ) (k : ℕ) : poisPmf M k ≤ 1 := by
  unfold poisPmf
  have h := hasSum_one_poissonMeasure M.toNNReal
  have := le_hasSum h k (fun j _ => by positivity)
  simpa [poissonPMFReal] using this

lemma IA18_poisPmf_nonneg (M : ℝ) (k : ℕ) : 0 ≤ poisPmf M k := by
  unfold poisPmf poissonPMFReal; positivity

lemma IA18_pmf_bounds {d : ℕ} (A : AnomModel d) (α : EuclideanSpace ℝ (Fin d)) (M : ℝ) (k : ℕ) :
    0 ≤ A.pmf α M k ∧ A.pmf α M k ≤ 1 := by
  unfold AnomModel.pmf
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using (A.anom α M.toNNReal).coe_le_one k)

lemma IA18_clamp01 (z : ℝ) : 0 ≤ clamp01 z ∧ clamp01 z ≤ 1 := by
  unfold clamp01
  exact ⟨le_max_right _ _, max_le (min_le_right _ _) zero_le_one⟩


lemma IA18_alpha_star {d : ℕ} (I : Instance d) : alphaOf I.θstar = I.αstar := by
  ext i; simp [alphaOf, Instance.θstar]

lemma IA18_pA_star {d : ℕ} (I : Instance d) : pAOf I.θstar = I.pAstar := by
  simp [pAOf, Instance.θstar]

lemma IA18_coord_le {D : ℕ} (v : EuclideanSpace ℝ (Fin D)) (i : Fin D) : |v i| ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq]
  apply Real.le_sqrt_of_sq_le
  have := Finset.single_le_sum (f := fun k => ‖v k‖ ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  simpa [Real.norm_eq_abs, sq_abs] using this

lemma IA18_alpha_dist {d : ℕ} (θ θ' : EuclideanSpace ℝ (Fin (d + 1))) :
    dist (alphaOf θ) (alphaOf θ') ≤ ‖θ - θ'‖ := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  rw [Fin.sum_univ_castSucc]
  simp only [alphaOf]
  simp
  positivity

lemma IA18_pA_dist {d : ℕ} (θ θ' : EuclideanSpace ℝ (Fin (d + 1))) :
    |pAOf θ - pAOf θ'| ≤ ‖θ - θ'‖ := by
  have := IA18_coord_le (θ - θ') (Fin.last d)
  simpa [pAOf] using this

lemma IA18_clamp_sub (z w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) : |clamp01 z - w| ≤ |z - w| := by
  unfold clamp01
  rcases le_total z 1 with h1 | h1
  · rw [min_eq_left h1]
    rcases le_total z 0 with h0 | h0
    · rw [max_eq_right h0, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
    · rw [max_eq_left h0]
  · rw [min_eq_right h1, max_eq_left zero_le_one, abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]; linarith

lemma IA18_pois_le1 (j : ℕ) (t : ℝ) (ht : 0 ≤ t) : Real.exp (-t) * t ^ j / (j ! : ℝ) ≤ 1 := by
  have h := Real.pow_div_factorial_le_exp t ht j
  rw [mul_div_assoc]
  calc Real.exp (-t) * (t ^ j / j !) ≤ Real.exp (-t) * Real.exp t := by gcongr
    _ = 1 := by rw [← Real.exp_add]; simp

/-- The Poisson weights are `1`-Lipschitz in the mean on `[0, ∞)`. -/
lemma IA18_pois_lip_core (k : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x) * x ^ k / (k ! : ℝ) - Real.exp (-y) * y ^ k / (k ! : ℝ)| ≤ |x - y| := by
  have hge0 : ∀ (j : ℕ) (t : ℝ), 0 ≤ t → 0 ≤ Real.exp (-t) * t ^ j / (j ! : ℝ) := by
    intro j t ht; positivity
  have key : ∀ f' : ℝ → ℝ, (∀ t, HasDerivAt (fun t => Real.exp (-t) * t ^ k / (k ! : ℝ)) (f' t) t) →
      (∀ t, 0 ≤ t → |f' t| ≤ 1) →
      |Real.exp (-x) * x ^ k / (k ! : ℝ) - Real.exp (-y) * y ^ k / (k ! : ℝ)| ≤ |x - y| := by
    intro f' hd hb
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun t => Real.exp (-t) * t ^ k / (k ! : ℝ)) (f' := f') (s := Set.Ici (0 : ℝ))
      (fun t _ => (hd t).hasDerivWithinAt)
      (fun t ht => by rw [Real.norm_eq_abs]; exact hb t ht) (convex_Ici 0) hy hx
    simpa [Real.norm_eq_abs] using this
  have hbase : ∀ t, HasDerivAt (fun t => Real.exp (-t) * t ^ k / (k ! : ℝ))
      ((Real.exp (-t) * -1 * t ^ k + Real.exp (-t) * ((k : ℝ) * t ^ (k - 1))) / (k ! : ℝ)) t := by
    intro t
    exact (((hasDerivAt_neg t).exp).mul (hasDerivAt_pow k t)).div_const _
  rcases k with _ | j
  · refine key (fun t => -Real.exp (-t)) (fun t => (hbase t).congr_deriv (by simp)) ?_
    intro t ht
    rw [abs_neg, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by linarith)
  · refine key (fun t => Real.exp (-t) * t ^ j / (j ! : ℝ) -
        Real.exp (-t) * t ^ (j + 1) / ((j + 1) ! : ℝ)) (fun t => (hbase t).congr_deriv ?_) ?_
    · have : (j ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
      simp only [Nat.add_sub_cancel, Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · intro t ht
      have a1 := IA18_pois_le1 j t ht
      have a2 := IA18_pois_le1 (j + 1) t ht
      have b1 := hge0 j t ht
      have b2 := hge0 (j + 1) t ht
      rw [abs_le]; constructor <;> linarith

lemma IA18_pois_lip (k : ℕ) (a b : ℝ) (hb : 0 ≤ b) : |poisPmf a k - poisPmf b k| ≤ |a - b| := by
  unfold poisPmf poissonPMFReal
  rw [Real.coe_toNNReal', Real.coe_toNNReal', max_eq_left hb]
  refine (IA18_pois_lip_core k (le_max_right a 0) hb).trans ?_
  rcases le_total a 0 with h | h
  · rw [max_eq_right h, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · rw [max_eq_left h]

lemma IA18_pmf_max {d : ℕ} (A : AnomModel d) (α : EuclideanSpace ℝ (Fin d)) (M : ℝ) (k : ℕ) :
    A.pmf α M k = A.pmf α (max M 0) k := by
  unfold AnomModel.pmf
  congr 3
  apply NNReal.eq
  rw [Real.coe_toNNReal', Real.coe_toNNReal', max_eq_left (le_max_right M 0)]

lemma IA18_arith (K L cM cA C1 C2 δ Δ DM : ℝ) (hK : 0 ≤ K) (hcM : 0 < cM) (hL : cM ≤ L)
    (hcA : 0 < cA) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hδ : 0 ≤ δ) (hΔ0 : 0 ≤ Δ) (hDM0 : 0 ≤ DM)
    (hΔ : Δ ≤ C1 * (K + L) * δ) (hDM : DM ≤ (C2 * δ + (K + 2) * Δ * L) / cA) :
    (K + 1) * (Δ + DM) ≤ (1 / cM + 1) * (C1 / cM ^ 2 + C2 / (cA * cM ^ 3) +
      (1 + 2 / cM) * C1 / cA) * (L + K) ^ 2 * L * ((K + L) * δ) := by
  set S := K + L with hS
  have hS0 : cM ≤ S := by rw [hS]; linarith
  have hSpos : 0 < S := by linarith
  have hLpos : 0 < L := by linarith
  set W := S ^ 3 * L * δ with hW
  have hW0 : 0 ≤ W := by positivity
  have ha : K + 1 ≤ (1 / cM + 1) * S := by
    have : 1 ≤ S / cM := by rw [le_div_iff₀ hcM]; linarith
    have : S / cM = 1 / cM * S := by ring
    nlinarith
  have hb : K + 2 ≤ (1 + 2 / cM) * S := by
    have : 1 ≤ S / cM := by rw [le_div_iff₀ hcM]; linarith
    have : (1 + 2 / cM) * S = S + 2 * (S / cM) := by ring
    linarith
  have hSL : cM * cM ≤ S * L := by nlinarith
  have hS2 : S ^ 2 * δ ≤ W / cM ^ 2 := by
    rw [le_div_iff₀ (by positivity), hW]
    have : S ^ 3 * L * δ = (S ^ 2 * δ) * (S * L) := by ring
    rw [this, sq cM]
    exact mul_le_mul_of_nonneg_left hSL (by positivity)
  have hS1 : S * δ ≤ W / cM ^ 3 := by
    rw [le_div_iff₀ (by positivity), hW]
    have h3 : cM ^ 3 ≤ S ^ 2 * L := by
      have : cM ^ 3 = cM * (cM * cM) := by ring
      rw [this, sq]
      have : S * S * L = S * (S * L) := by ring
      rw [this]
      exact mul_le_mul hS0 hSL (by positivity) hSpos.le
    have : S ^ 3 * L * δ = (S * δ) * (S ^ 2 * L) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have hsum : Δ + DM ≤ C1 * S * δ + C2 * δ / cA + (1 + 2 / cM) * C1 / cA * (S ^ 2 * L * δ) := by
    have hKΔ : (K + 2) * Δ * L ≤ ((1 + 2 / cM) * S) * (C1 * S * δ) * L := by
      have : 0 ≤ K + 2 := by linarith
      gcongr
    have : DM ≤ (C2 * δ + ((1 + 2 / cM) * S) * (C1 * S * δ) * L) / cA :=
      hDM.trans (by gcongr)
    have e1 : (C2 * δ + ((1 + 2 / cM) * S) * (C1 * S * δ) * L) / cA =
        C2 * δ / cA + (1 + 2 / cM) * C1 / cA * (S ^ 2 * L * δ) := by ring
    rw [e1] at this
    linarith
  have hsum0 : 0 ≤ Δ + DM := by linarith
  calc (K + 1) * (Δ + DM) ≤ ((1 / cM + 1) * S) *
        (C1 * S * δ + C2 * δ / cA + (1 + 2 / cM) * C1 / cA * (S ^ 2 * L * δ)) :=
        mul_le_mul ha hsum hsum0 (by positivity)
    _ = (1 / cM + 1) * (C1 * (S ^ 2 * δ) + C2 / cA * (S * δ) + (1 + 2 / cM) * C1 / cA * W) := by
        rw [hW]; ring
    _ ≤ (1 / cM + 1) * (C1 * (W / cM ^ 2) + C2 / cA * (W / cM ^ 3) +
          (1 + 2 / cM) * C1 / cA * W) := by
        gcongr
    _ = (1 / cM + 1) * (C1 / cM ^ 2 + C2 / (cA * cM ^ 3) + (1 + 2 / cM) * C1 / cA) * W := by
        field_simp
    _ = _ := by rw [hW, hS]; ring

theorem solution (d : ℕ) (cM cA CRC : ℝ) (hcM : 0 < cM) (hcA : 0 < cA) (hcA1 : cA < 1)
    (hCRC : 0 < CRC) :
    ∃ Csp C C' : ℝ, 0 < Csp ∧ 0 < C ∧ 0 < C' ∧
      ∀ (I : Instance d) (K L μ : ℝ) (hI : I.Model cM cA Csp K L μ),
        I.SparsityMax hI.r_pos Csp μ L →
        I.Regular hI.r_pos cA CRC K L μ →
        ∀ (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ)
          (θhat : I.Obs → EuclideanSpace ℝ (Fin (d + 1))),
        IsBestRankApprox I.r svdr → I.ThetaSel cA svdr θhat →
        1 - C' / (I.n * I.m) ≤ I.law.real {ω | ∀ ij ∈ I.omega (I.obs ω),
          max |I.xhat svdr θhat (I.obs ω) ij.1 ij.2 - I.xstar (I.obs ω) ij.1 ij.2|
              |I.yhat svdr θhat (I.obs ω) ij.1 ij.2 - I.ystar (I.obs ω) ij.1 ij.2| ≤
            C * (L + K) ^ 2 * L * ((K + L) * I.δ' hI.r_pos μ L)} := by
  obtain ⟨Cs1, C1, C1', h1s, h1C, h1C', H1⟩ := lemma_1_spmax d cM cA CRC hcM hcA hcA1 hCRC
  obtain ⟨Cs2, C2, C2', h2s, h2C, h2C', H2⟩ := theorem_2 d cM cA hcM hcA hcA1
  refine ⟨max Cs1 Cs2, (1 / cM + 1) * (C1 / cM ^ 2 + C2 / (cA * cM ^ 3) +
      (1 + 2 / cM) * C1 / cA), C1' + C2', lt_max_of_lt_left h1s, by positivity,
    by positivity, ?_⟩
  intro I K L μ hI hS hReg svdr θhat hsvd hsel
  have E1 := H1 I K L μ (IA18_model_mono hI (le_max_left Cs1 Cs2))
    (IA18_spmax_mono hI hS (le_max_left _ _)) hReg svdr θhat hsvd hsel
  have E2 := H2 I K L μ (IA18_model_mono hI (le_max_right Cs1 Cs2))
    (IA18_spmax_mono hI hS (le_max_right _ _)) svdr hsvd
  -- elementary facts
  have hn0 : 0 < I.n := by have := hI.two_le_m; have := hI.m_le_n; omega
  have hm0 : 0 < I.m := by have := hI.two_le_m; omega
  have hLcM : cM ≤ L := by
    obtain ⟨i, j, h⟩ := hI.max_lb
    exact h.trans ((le_abs_self _).trans (hI.max_ub i j))
  have hL : 0 ≤ L := by linarith
  have hK : 0 ≤ K := by
    have := hI.smooth 0 (I.αstar, 0) ⟨hI.α_mem, Set.mem_Ici.2 le_rfl⟩ (I.αstar, 1)
      ⟨hI.α_mem, Set.mem_Ici.2 zero_le_one⟩
    have hd : dist ((I.αstar, (0 : ℝ))) (I.αstar, (1 : ℝ)) = 1 := by
      simp [Prod.dist_eq, Real.dist_eq]
    rw [hd, mul_one] at this
    exact (abs_nonneg _).trans this
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
  have hpA0 : (0 : ℝ) ≤ I.pAstar := I.pAstar.2
  have hpA1 : (I.pAstar : ℝ) ≤ 1 - cA := hI.pA_le
  have hg := hI.g_mem
  -- `e(θ) ∈ [cA, 1]` on `Θ`
  have he_bd : ∀ θ ∈ I.Θ cA, cA ≤ I.model.e θ ∧ I.model.e θ ≤ 1 := by
    intro θ hθ
    obtain ⟨-, h0, h1⟩ := hθ
    obtain ⟨g0, g1⟩ := hg (alphaOf θ)
    unfold AnomModel.e
    constructor <;> nlinarith
  have hθs : I.θstar ∈ I.Θ cA := by
    refine ⟨?_, ?_, ?_⟩
    · rw [IA18_alpha_star]; exact hI.α_mem
    · rw [IA18_pA_star]; exact hpA0
    · rw [IA18_pA_star]; exact hpA1
  have he_lip : ∀ θ ∈ I.Θ cA, |I.model.e θ - I.model.e I.θstar| ≤ (K + 2) * ‖θ - I.θstar‖ := by
    intro θ hθ
    obtain ⟨-, h0, h1⟩ := hθ
    have hp := IA18_pA_dist θ I.θstar
    have ha := IA18_alpha_dist θ I.θstar
    have hgl := hI.g_lip (alphaOf θ) (alphaOf I.θstar)
    obtain ⟨g0, g1⟩ := hg (alphaOf θ)
    obtain ⟨g0', g1'⟩ := hg (alphaOf I.θstar)
    have hps0 : 0 ≤ pAOf I.θstar := by rw [IA18_pA_star]; exact hpA0
    unfold AnomModel.e
    have eq : pAOf θ * I.model.g (alphaOf θ) + (1 - pAOf θ) -
        (pAOf I.θstar * I.model.g (alphaOf I.θstar) + (1 - pAOf I.θstar)) =
        pAOf θ * (I.model.g (alphaOf θ) - I.model.g (alphaOf I.θstar)) +
          (pAOf θ - pAOf I.θstar) * (I.model.g (alphaOf I.θstar) - 1) := by ring
    rw [eq]
    have t1 : |pAOf θ * (I.model.g (alphaOf θ) - I.model.g (alphaOf I.θstar))| ≤
        K * ‖θ - I.θstar‖ := by
      rw [abs_mul, abs_of_nonneg h0]
      calc pAOf θ * |I.model.g (alphaOf θ) - I.model.g (alphaOf I.θstar)| ≤
          1 * (K * dist (alphaOf θ) (alphaOf I.θstar)) := by
            apply mul_le_mul (by linarith) hgl (abs_nonneg _) zero_le_one
        _ ≤ K * ‖θ - I.θstar‖ := by rw [one_mul]; exact mul_le_mul_of_nonneg_left ha hK
    have t2 : |(pAOf θ - pAOf I.θstar) * (I.model.g (alphaOf I.θstar) - 1)| ≤
        2 * ‖θ - I.θstar‖ := by
      rw [abs_mul]
      have : |I.model.g (alphaOf I.θstar) - 1| ≤ 2 := by rw [abs_le]; constructor <;> linarith
      calc |pAOf θ - pAOf I.θstar| * |I.model.g (alphaOf I.θstar) - 1| ≤
          ‖θ - I.θstar‖ * 2 := mul_le_mul hp this (abs_nonneg _) (norm_nonneg _)
        _ = 2 * ‖θ - I.θstar‖ := by ring
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ K * ‖θ - I.θstar‖ + 2 * ‖θ - I.θstar‖ := add_le_add t1 t2
      _ = _ := by ring
  have hP : IsProbabilityMeasure I.law := by unfold Instance.law; infer_instance
  set A := {ω | ‖θhat (I.obs ω) - I.θstar‖ ≤ C1 * (K + L) * I.δ' hI.r_pos μ L} with hA
  set B := {ω | maxNorm (I.Mhat svdr (I.obs ω) - I.model.e I.θstar • I.Mstar)
      (C2 * I.δ' hI.r_pos μ L)} with hB
  have hsub : A ∩ B ⊆ {ω | ∀ ij ∈ I.omega (I.obs ω),
          max |I.xhat svdr θhat (I.obs ω) ij.1 ij.2 - I.xstar (I.obs ω) ij.1 ij.2|
              |I.yhat svdr θhat (I.obs ω) ij.1 ij.2 - I.ystar (I.obs ω) ij.1 ij.2| ≤
            (1 / cM + 1) * (C1 / cM ^ 2 + C2 / (cA * cM ^ 3) + (1 + 2 / cM) * C1 / cA) *
              (L + K) ^ 2 * L * ((K + L) * I.δ' hI.r_pos μ L)} := by
    rintro ω ⟨hAω, hBω⟩ ij _
    set x := I.obs ω with hx
    set θ := θhat x with hθ
    have hθΘ : θ ∈ I.Θ cA := (hsel x).1
    obtain ⟨hαΓ, hp0, hp1⟩ := hθΘ
    set Δ := ‖θ - I.θstar‖ with hΔ
    have hΔ0 : 0 ≤ Δ := norm_nonneg _
    have hΔb : Δ ≤ C1 * (K + L) * I.δ' hI.r_pos μ L := hAω
    obtain ⟨heA, he1⟩ := he_bd θ ⟨hαΓ, hp0, hp1⟩
    have hepos : 0 < I.model.e θ := lt_of_lt_of_le hcA heA
    set M' := I.Mhat svdr x ij.1 ij.2 / I.model.e θ with hM'
    set Ms := I.Mstar ij.1 ij.2 with hMs
    have hMs0 : 0 ≤ Ms := hI.nonneg _ _
    have hMsL : Ms ≤ L := (le_abs_self _).trans (hI.max_ub _ _)
    set DM := |M' - Ms| with hDM
    have hBij : |I.Mhat svdr x ij.1 ij.2 - I.model.e I.θstar * Ms| ≤
        C2 * I.δ' hI.r_pos μ L := by
      have := hBω ij.1 ij.2
      simpa [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using this
    have hDMb : DM ≤ (C2 * I.δ' hI.r_pos μ L + (K + 2) * Δ * L) / cA := by
      have heq : M' - Ms = ((I.Mhat svdr x ij.1 ij.2 - I.model.e I.θstar * Ms) +
          (I.model.e I.θstar - I.model.e θ) * Ms) / I.model.e θ := by
        rw [hM']; field_simp; ring
      rw [hDM, heq, abs_div, abs_of_pos hepos]
      have hnum : |(I.Mhat svdr x ij.1 ij.2 - I.model.e I.θstar * Ms) +
          (I.model.e I.θstar - I.model.e θ) * Ms| ≤
          C2 * I.δ' hI.r_pos μ L + (K + 2) * Δ * L := by
        refine (abs_add_le _ _).trans (add_le_add hBij ?_)
        rw [abs_mul, abs_of_nonneg hMs0, abs_sub_comm]
        exact mul_le_mul (he_lip θ ⟨hαΓ, hp0, hp1⟩) hMsL hMs0 (by positivity)
      calc _ ≤ (C2 * I.δ' hI.r_pos μ L + (K + 2) * Δ * L) / I.model.e θ :=
            div_le_div_of_nonneg_right hnum hepos.le
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hcA heA
    have hDM0 : 0 ≤ DM := abs_nonneg _
    have hpd : |pAOf θ - I.pAstar| ≤ Δ := by
      have := IA18_pA_dist θ I.θstar; rwa [IA18_pA_star] at this
    have had : dist (alphaOf θ) I.αstar ≤ Δ := by
      have := IA18_alpha_dist θ I.θstar; rwa [IA18_alpha_star] at this
    have hMd : |max M' 0 - Ms| ≤ DM := by
      rw [hDM]
      rcases le_total M' 0 with h | h
      · rw [max_eq_right h, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
      · rw [max_eq_left h]
    have hbd : max |I.xhat svdr θhat x ij.1 ij.2 - I.xstar x ij.1 ij.2|
        |I.yhat svdr θhat x ij.1 ij.2 - I.ystar x ij.1 ij.2| ≤ (K + 1) * (Δ + DM) := by
      set k := (x (ij.1, ij.2)).getD 0 with hk
      obtain ⟨P0, P1⟩ := IA18_pmf_bounds I.model (alphaOf θ) M' k
      obtain ⟨Ps0, Ps1⟩ := IA18_pmf_bounds I.model I.αstar Ms k
      have Q0 := IA18_poisPmf_nonneg M' k
      have Q1 := IA18_poisPmf_le_one M' k
      have Qs0 := IA18_poisPmf_nonneg Ms k
      have Qs1 := IA18_poisPmf_le_one Ms k
      have hPd : |I.model.pmf (alphaOf θ) M' k - I.model.pmf I.αstar Ms k| ≤ K * (Δ + DM) := by
        rw [IA18_pmf_max I.model (alphaOf θ) M' k]
        have hsm := hI.smooth k (alphaOf θ, max M' 0) ⟨hαΓ, Set.mem_Ici.2 (le_max_right _ _)⟩
          (I.αstar, Ms) ⟨hI.α_mem, Set.mem_Ici.2 hMs0⟩
        refine hsm.trans (mul_le_mul_of_nonneg_left ?_ hK)
        rw [Prod.dist_eq, Real.dist_eq]
        exact max_le (by linarith) (by linarith)
      have hQd : |poisPmf M' k - poisPmf Ms k| ≤ DM := IA18_pois_lip k M' Ms hMs0
      apply max_le
      · have hxs0 : 0 ≤ I.xstar x ij.1 ij.2 := mul_nonneg hpA0 Ps0
        have hxs1 : I.xstar x ij.1 ij.2 ≤ 1 := by
          unfold Instance.xstar
          calc (I.pAstar : ℝ) * I.model.pmf I.αstar Ms k ≤ 1 * 1 :=
                mul_le_mul (by linarith) Ps1 Ps0 zero_le_one
            _ = 1 := one_mul 1
        refine (IA18_clamp_sub _ _ hxs0 hxs1).trans ?_
        show |pAOf θ * I.model.pmf (alphaOf θ) (I.Mhat svdr x ij.1 ij.2 / I.model.e θ) k -
          (I.pAstar : ℝ) * I.model.pmf I.αstar Ms k| ≤ _
        rw [← hM']
        have eq : pAOf θ * I.model.pmf (alphaOf θ) M' k - (I.pAstar : ℝ) * I.model.pmf I.αstar Ms k =
            (pAOf θ - I.pAstar) * I.model.pmf (alphaOf θ) M' k +
              (I.pAstar : ℝ) * (I.model.pmf (alphaOf θ) M' k - I.model.pmf I.αstar Ms k) := by ring
        rw [eq]
        calc _ ≤ _ := abs_add_le _ _
          _ ≤ Δ * 1 + 1 * (K * (Δ + DM)) := by
            rw [abs_mul, abs_mul, abs_of_nonneg P0, abs_of_nonneg hpA0]
            exact add_le_add (mul_le_mul hpd P1 P0 hΔ0)
              (mul_le_mul (by linarith) hPd (abs_nonneg _) zero_le_one)
          _ ≤ (K + 1) * (Δ + DM) := by
            have := mul_nonneg hK (add_nonneg hΔ0 hDM0)
            linarith
      · have hys0 : 0 ≤ I.ystar x ij.1 ij.2 := mul_nonneg (by linarith) Qs0
        have hys1 : I.ystar x ij.1 ij.2 ≤ 1 := by
          unfold Instance.ystar
          calc (1 - (I.pAstar : ℝ)) * poisPmf Ms k ≤ 1 * 1 :=
                mul_le_mul (by linarith) Qs1 Qs0 zero_le_one
            _ = 1 := one_mul 1
        refine (IA18_clamp_sub _ _ hys0 hys1).trans ?_
        show |(1 - pAOf θ) * poisPmf (I.Mhat svdr x ij.1 ij.2 / I.model.e θ) k -
          (1 - (I.pAstar : ℝ)) * poisPmf Ms k| ≤ _
        rw [← hM']
        have eq : (1 - pAOf θ) * poisPmf M' k - (1 - (I.pAstar : ℝ)) * poisPmf Ms k =
            (I.pAstar - pAOf θ) * poisPmf M' k +
              (1 - (I.pAstar : ℝ)) * (poisPmf M' k - poisPmf Ms k) := by ring
        rw [eq]
        calc _ ≤ _ := abs_add_le _ _
          _ ≤ Δ * 1 + 1 * DM := by
            rw [abs_mul, abs_mul, abs_of_nonneg Q0, abs_of_nonneg (show (0 : ℝ) ≤ 1 - I.pAstar by linarith),
              abs_sub_comm]
            exact add_le_add (mul_le_mul hpd Q1 Q0 hΔ0)
              (mul_le_mul (by linarith) hQd (abs_nonneg _) zero_le_one)
          _ ≤ (K + 1) * (Δ + DM) := by
            have := mul_nonneg hK (add_nonneg hΔ0 hDM0)
            linarith
    refine hbd.trans ?_
    exact IA18_arith K L cM cA C1 C2 (I.δ' hI.r_pos μ L) Δ DM hK hcM hLcM hcA h1C.le h2C.le hδ0
      hΔ0 hDM0 hΔb hDMb
  have hAm : MeasurableSet A := MeasurableSet.of_discrete
  have hBm : MeasurableSet B := MeasurableSet.of_discrete
  have hunion := measureReal_union_add_inter (μ := I.law) (s := A) hBm
  have hle1 : I.law.real (A ∪ B) ≤ 1 := measureReal_le_one
  calc 1 - (C1' + C2') / (I.n * I.m) = (1 - C1' / (I.n * I.m)) + (1 - C2' / (I.n * I.m)) - 1 := by
        ring
    _ ≤ I.law.real A + I.law.real B - 1 := by linarith
    _ ≤ I.law.real (A ∩ B) := by linarith
    _ ≤ _ := measureReal_mono hsub
