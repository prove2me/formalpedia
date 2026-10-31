-- Prove2me | solution 1 for InventoryAnomaly.EW.lemma_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T08:29:21.418255+00:00
-- url     : https://prove2.me/submissions/6326a255-9503-4cc3-bd17-3ac8b4900d69
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_InventoryAnomaly_EW_Model
import Theorems.Thm_InventoryAnomaly_EW_lemma_15
import Theorems.Thm_InventoryAnomaly_EW_lemma_16

open MeasureTheory ProbabilityTheory
open scoped NNReal
open InventoryAnomaly.EW

lemma IA2_alpha_star {d : ℕ} (I : Instance d) : alphaOf I.θstar = I.αstar := by
  ext i; simp [alphaOf, Instance.θstar]

lemma IA2_pA_star {d : ℕ} (I : Instance d) : pAOf I.θstar = I.pAstar := by
  simp [pAOf, Instance.θstar]

lemma IA2_F_apply {d : ℕ} (I : Instance d) (θ : EuclideanSpace ℝ (Fin (d + 1))) (t : Fin (d + 1)) :
    I.F θ t = I.gt θ ((I.model.e I.θstar / I.model.e θ) • I.Mstar) t := by
  simp [Instance.F]

lemma IA2_norm_le {D : ℕ} (v : EuclideanSpace ℝ (Fin D)) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ t, |v t| ≤ B) : ‖v‖ ≤ Real.sqrt D * B := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq hB, ← Real.sqrt_mul (Nat.cast_nonneg D)]
  apply Real.sqrt_le_sqrt
  calc ∑ t, ‖v t‖ ^ 2 ≤ ∑ _t : Fin D, B ^ 2 := by
        refine Finset.sum_le_sum fun t _ => ?_
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (h t) 2
    _ = D * B ^ 2 := by simp

lemma IA2_model_mono {d : ℕ} {I : Instance d} {cM cA Csp Csp' K L μ : ℝ}
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

lemma IA2_spmax_mono {d : ℕ} {I : Instance d} {cM cA Csp Csp' K L μ : ℝ}
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

theorem solution (d : ℕ) (cM cA : ℝ) (hcM : 0 < cM) (hcA : 0 < cA) (hcA1 : cA < 1) :
    ∃ Csp C C' : ℝ, 0 < Csp ∧ 0 < C ∧ 0 < C' ∧
      ∀ (I : Instance d) (K L μ : ℝ) (hI : I.Model cM cA Csp K L μ),
        I.SparsityMax hI.r_pos Csp μ L →
        ∀ (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ)
          (θhat : I.Obs → EuclideanSpace ℝ (Fin (d + 1))),
        IsBestRankApprox I.r svdr → I.ThetaSel cA svdr θhat →
        1 - C' / (I.n * I.m) ≤ I.law.real {ω |
          ‖I.F (θhat (I.obs ω)) - I.F I.θstar‖ ≤ C * (K + L) * I.δ' hI.r_pos μ L} := by
  obtain ⟨Cs15, C15, C15', h15s, h15C, h15C', H15⟩ := lemma_15 d cM cA hcM hcA hcA1
  obtain ⟨Cs16, C16, C16', h16s, h16C, h16C', H16⟩ := lemma_16 d cM cA hcM hcA hcA1
  refine ⟨max Cs15 Cs16, Real.sqrt (d + 1 : ℕ) * (2 * C15 + 2 * Real.sqrt C16), C15' + C16',
    lt_max_of_lt_left h15s, by positivity, by positivity, ?_⟩
  intro I K L μ hI hS svdr θhat hsvd hsel
  have hI15 := IA2_model_mono hI (le_max_left Cs15 Cs16)
  have hI16 := IA2_model_mono hI (le_max_right Cs15 Cs16)
  have E15 := H15 I K L μ hI15 (IA2_spmax_mono hI hS (le_max_left _ _)) svdr hsvd
  have E16 := H16 I K L μ hI16 (IA2_spmax_mono hI hS (le_max_right _ _)) svdr hsvd
  -- elementary facts
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
  set e := (K + L) * I.δ' hI.r_pos μ L with he
  have he0 : 0 ≤ e := mul_nonneg (by linarith) hδ0
  have hθs : I.θstar ∈ I.Θ cA := by
    refine ⟨?_, ?_, ?_⟩
    · rw [IA2_alpha_star]; exact hI.α_mem
    · rw [IA2_pA_star]; exact I.pAstar.2
    · rw [IA2_pA_star]; exact hI.pA_le
  have hP : IsProbabilityMeasure I.law := by unfold Instance.law; infer_instance
  set A := {ω | ∀ θ ∈ I.Θ cA, ∀ t ≤ d + 1,
          |I.gt θ ((I.model.e I.θstar / I.model.e θ) • I.Mstar) t -
            I.gt θ ((I.model.e θ)⁻¹ • I.Mhat svdr (I.obs ω)) t| ≤
              C15 * (K + L) * I.δ' hI.r_pos μ L} with hA
  set B := {ω | I.hobj (d + 1) svdr (I.obs ω) I.θstar ≤
      C16 * (K + L) ^ 2 * I.δ' hI.r_pos μ L ^ 2} with hB
  have hsub : A ∩ B ⊆ {ω | ‖I.F (θhat (I.obs ω)) - I.F I.θstar‖ ≤
      Real.sqrt (d + 1 : ℕ) * (2 * C15 + 2 * Real.sqrt C16) * (K + L) * I.δ' hI.r_pos μ L} := by
    rintro ω ⟨hAω, hBω⟩
    set x := I.obs ω
    obtain ⟨hθΘ, hh⟩ := hsel x
    -- residual bounds from the objective
    have hres : ∀ θ, I.hobj (d + 1) svdr x θ ≤ C16 * e ^ 2 → ∀ t < d + 1,
        |I.gt θ ((I.model.e θ)⁻¹ • I.Mhat svdr x) t -
          ((I.omega x).filter fun ij => ((x ij).getD 0) ≤ t).card / (I.omega x).card| ≤
          Real.sqrt C16 * e := by
      intro θ hθ t ht
      have hsingle := Finset.single_le_sum (f := fun t => (I.gt θ ((I.model.e θ)⁻¹ • I.Mhat svdr x) t -
          ((I.omega x).filter fun ij => ((x ij).getD 0) ≤ t).card / (I.omega x).card) ^ 2)
        (fun t _ => sq_nonneg _) (Finset.mem_range.2 ht)
      have hsq : (I.gt θ ((I.model.e θ)⁻¹ • I.Mhat svdr x) t -
          ((I.omega x).filter fun ij => ((x ij).getD 0) ≤ t).card / (I.omega x).card) ^ 2 ≤
          (Real.sqrt C16 * e) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt h16C.le]
        exact hsingle.trans hθ
      exact abs_le_of_sq_le_sq' hsq (by positivity) |> fun h => abs_le.2 h
    have hBω' : I.hobj (d + 1) svdr x I.θstar ≤ C16 * e ^ 2 := by
      rw [he, mul_pow, ← mul_assoc]; exact hBω
    have r1 := hres _ (hh.trans hBω')
    have r2 := hres _ hBω'
    have hcoord : ∀ t : Fin (d + 1), |I.F (θhat x) t - I.F I.θstar t| ≤
        (2 * C15 + 2 * Real.sqrt C16) * e := by
      intro t
      rw [IA2_F_apply, IA2_F_apply]
      have a1 := hAω (θhat x) hθΘ t (by omega)
      have a2 := hAω I.θstar hθs t (by omega)
      have b1 := r1 t t.2
      have b2 := r2 t t.2
      rw [mul_assoc C15 (K + L), ← he] at a1 a2
      rw [abs_le] at a1 a2 b1 b2 ⊢
      constructor <;> nlinarith [a1, a2, b1, b2]
    have := IA2_norm_le (I.F (θhat x) - I.F I.θstar) ((2 * C15 + 2 * Real.sqrt C16) * e)
      (by positivity) (fun t => by simpa using hcoord t)
    show ‖I.F (θhat x) - I.F I.θstar‖ ≤ _
    calc _ ≤ _ := this
      _ = _ := by rw [he]; push_cast; ring
  have hAm : MeasurableSet A := MeasurableSet.of_discrete
  have hBm : MeasurableSet B := MeasurableSet.of_discrete
  have hunion := measureReal_union_add_inter (μ := I.law) (s := A) hBm
  have hle1 : I.law.real (A ∪ B) ≤ 1 := measureReal_le_one
  calc 1 - (C15' + C16') / (I.n * I.m) = (1 - C15' / (I.n * I.m)) + (1 - C16' / (I.n * I.m)) - 1 := by
        ring
    _ ≤ I.law.real A + I.law.real B - 1 := by linarith
    _ ≤ I.law.real (A ∩ B) := by linarith
    _ ≤ _ := measureReal_mono hsub
