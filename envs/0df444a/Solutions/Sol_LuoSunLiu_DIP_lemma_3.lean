-- Prove2me | solution 1 for LuoSunLiu.DIP.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T04:25:39.231203+00:00
-- url     : https://prove2.me/submissions/9388aa70-31a2-4434-b4de-1aae33fb7189

import Mathlib
import Definitions.Def_LuoSunLiu_DIP_PLB
import Theorems.Thm_LuoSunLiu_DIP_lemma_S1
import Theorems.Thm_LuoSunLiu_DIP_lemma_S5
import Theorems.Thm_LuoSunLiu_DIP_lemma_2

set_option autoImplicit false

section Helpers

open MeasureTheory ProbabilityTheory Matrix LuoSunLiu.DIP

private lemma vecMulVec_eq_diagonal_of_oneSparse {d : ℕ} {a : Fin d → ℝ} (ha : IsOneSparse a) :
    vecMulVec a a = Matrix.diagonal (fun i => a i ^ 2) := by
  obtain ⟨k, c, _, rfl⟩ := ha
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [vecMulVec_apply, sq]
  · simp only [vecMulVec_apply, Matrix.diagonal_apply, hij, ↓reduceIte]
    by_cases hik : i = k
    · subst hik
      have hjk : j ≠ i := Ne.symm hij
      simp [hjk]
    · simp [Pi.single_apply, hik]

private lemma regDesign_eq_diagonal {d : ℕ} {Ω : Type*} (lam : ℝ) (A : ℕ → Ω → Fin d → ℝ)
    (m : ℕ) (ω : Ω) (hA : ∀ s : ℕ, 1 ≤ s → IsOneSparse (A s ω)) :
    BanditAlgorithm.regularizedDesignMatrix d lam A m ω =
      Matrix.diagonal (fun i => lam + ∑ s ∈ Finset.range m, A (s + 1) ω i ^ 2) := by
  unfold BanditAlgorithm.regularizedDesignMatrix
  have h1 : lam • (1 : Matrix (Fin d) (Fin d) ℝ) = Matrix.diagonal (fun _ => lam) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hsum : (∑ s ∈ Finset.range m, vecMulVec (A (s + 1) ω) (A (s + 1) ω)) =
      ∑ s ∈ Finset.range m, Matrix.diagonal (fun i => A (s + 1) ω i ^ 2) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    exact vecMulVec_eq_diagonal_of_oneSparse (hA (s + 1) (Nat.succ_pos s))
  rw [h1, hsum]
  ext i j
  by_cases hij : i = j <;> simp [hij, Matrix.sum_apply]

private lemma inv_diagonal_pos {d : ℕ} (v : Fin d → ℝ) (hv : ∀ i, 0 < v i) :
    (Matrix.diagonal v)⁻¹ = Matrix.diagonal (fun i => (v i)⁻¹) := by
  rw [Matrix.inv_diagonal]
  let u : (Fin d → ℝ)ˣ :=
    ⟨v, fun i => (v i)⁻¹, funext fun i => mul_inv_cancel₀ (hv i).ne',
      funext fun i => inv_mul_cancel₀ (hv i).ne'⟩
  change Matrix.diagonal (Ring.inverse (u : Fin d → ℝ)) = _
  rw [Ring.inverse_unit]
  rfl

private lemma dot_diag_mulVec {d : ℕ} (v x : Fin d → ℝ) :
    x ⬝ᵥ Matrix.diagonal v *ᵥ x = ∑ i, v i * x i ^ 2 := by
  simp only [dotProduct, Matrix.mulVec_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private lemma self_le_two_mul_log_one_add {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x ≤ 2 * Real.log (1 + x) := by
  have h1x_pos : 0 < 1 + x := by linarith
  have hlog_inv : Real.log ((1 + x)⁻¹) ≤ (1 + x)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (inv_pos.mpr h1x_pos)
  rw [Real.log_inv] at hlog_inv
  have hfrac : x / (1 + x) ≤ Real.log (1 + x) := by
    have hsub : (1 + x)⁻¹ - 1 = -(x / (1 + x)) := by
      field_simp [h1x_pos.ne']
      ring
    linarith
  have hhalf : x / 2 ≤ x / (1 + x) := by
    refine div_le_div_of_nonneg_left hx0 h1x_pos ?_
    linarith
  linarith

private lemma betaTilde_mono {C1 amax lam : ℝ} {d : ℕ} {δ : ℝ}
    (hC1 : 0 ≤ C1) (hlam : 0 < lam) (hd : 1 ≤ d) {t1 t2 : ℕ}
    (ht1 : 1 ≤ t1) (ht12 : t1 ≤ t2) :
    betaTilde C1 amax lam d δ t1 ≤ betaTilde C1 amax lam d δ t2 := by
  unfold betaTilde
  refine max_le_max_left 1 ?_
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hdlam_pos : 0 < (d : ℝ) * lam := mul_pos hd_pos hlam
  have ht1_sub_nonneg : 0 ≤ (t1 : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (t1 : ℝ) := by exact_mod_cast ht1
    linarith
  have ht_le : (t1 : ℝ) - 1 ≤ (t2 : ℝ) - 1 := by
    have : (t1 : ℝ) ≤ (t2 : ℝ) := by exact_mod_cast ht12
    linarith
  have hnum_pos : 0 < (d : ℝ) * lam + ((t1 : ℝ) - 1) * amax ^ 2 :=
    add_pos_of_pos_of_nonneg hdlam_pos (mul_nonneg ht1_sub_nonneg (sq_nonneg amax))
  have hr1_pos : 0 < ((d : ℝ) * lam + ((t1 : ℝ) - 1) * amax ^ 2) / ((d : ℝ) * lam) :=
    div_pos hnum_pos hdlam_pos
  have hr_le : ((d : ℝ) * lam + ((t1 : ℝ) - 1) * amax ^ 2) / ((d : ℝ) * lam) ≤
      ((d : ℝ) * lam + ((t2 : ℝ) - 1) * amax ^ 2) / ((d : ℝ) * lam) := by
    refine div_le_div_of_nonneg_right ?_ (le_of_lt hdlam_pos)
    exact add_le_add_right (mul_le_mul_of_nonneg_right ht_le (sq_nonneg amax)) ((d : ℝ) * lam)
  have hlog_le : Real.log (((d : ℝ) * lam + ((t1 : ℝ) - 1) * amax ^ 2) / ((d : ℝ) * lam)) ≤
      Real.log (((d : ℝ) * lam + ((t2 : ℝ) - 1) * amax ^ 2) / ((d : ℝ) * lam)) :=
    Real.log_le_log hr1_pos hr_le
  have hsqrt_le :
      Real.sqrt (2 * Real.log (1 / δ) +
          (d : ℝ) * Real.log (((d : ℝ) * lam + ((t1 : ℝ) - 1) * amax ^ 2) / ((d : ℝ) * lam))) ≤
        Real.sqrt (2 * Real.log (1 / δ) +
          (d : ℝ) * Real.log (((d : ℝ) * lam + ((t2 : ℝ) - 1) * amax ^ 2) / ((d : ℝ) * lam))) := by
    refine Real.sqrt_le_sqrt ?_
    exact add_le_add_right (mul_le_mul_of_nonneg_left hlog_le (Nat.cast_nonneg d)) _
  have hbase_nonneg : 0 ≤ C1 * Real.sqrt (lam * d) +
      Real.sqrt (2 * Real.log (1 / δ) +
        (d : ℝ) * Real.log (((d : ℝ) * lam + ((t1 : ℝ) - 1) * amax ^ 2) / ((d : ℝ) * lam))) :=
    add_nonneg (mul_nonneg hC1 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hbase_le :
      C1 * Real.sqrt (lam * d) +
          Real.sqrt (2 * Real.log (1 / δ) +
            (d : ℝ) * Real.log (((d : ℝ) * lam + ((t1 : ℝ) - 1) * amax ^ 2) / ((d : ℝ) * lam))) ≤
        C1 * Real.sqrt (lam * d) +
          Real.sqrt (2 * Real.log (1 / δ) +
            (d : ℝ) * Real.log (((d : ℝ) * lam + ((t2 : ℝ) - 1) * amax ^ 2) / ((d : ℝ) * lam))) :=
    add_le_add_right hsqrt_le (C1 * Real.sqrt (lam * d))
  exact sq_le_sq' (by linarith) hbase_le

end Helpers

open MeasureTheory ProbabilityTheory Matrix LuoSunLiu.DIP in
theorem solution {d : ℕ} (hd : 1 ≤ d) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (ξ : ℕ → Ω → Fin d → ℝ) (𝒜 : ℕ → Ω → Finset (Fin d → ℝ)) (A : ℕ → Ω → Fin d → ℝ)
    (Z η : ℕ → Ω → ℝ) (Cp C1 amax lam δ : ℝ)
    (hPLB : IsPLBModel P ℱ ξ 𝒜 A Z η 1) (hCp : HasPerturbation ξ Cp)
    (hCond1 : Condition1 ξ 𝒜) (hCond2 : Condition2 ξ C1) (hCond3 : Condition3 𝒜 amax)
    (hC1 : 0 ≤ C1) (hamax : 0 < amax) (hlam : 0 < lam) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (T0 : ℕ) (hT0 : 1 ≤ T0)
    (hrun : ∀ ω, IsMLinUCBRunAt lam (betaTilde C1 amax lam d δ) 𝒜 A Z T0 ω) :
    ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ P E ∧
      ∀ ω ∈ E, plbRegret ξ 𝒜 A T0 ω ≤
        2 * Real.sqrt (2 * d * T0 * betaTilde C1 amax lam d δ T0 *
          Real.log ((d * lam + T0 * amax ^ 2) / (d * lam))) + 2 * amax * Cp * T0 + 2 * d := by
  obtain ⟨E, hE_meas, hPE, hE_ell⟩ :=
    LuoSunLiu.DIP.lemma_S5 hd P ℱ ξ 𝒜 A Z η C1 amax lam δ
      hPLB hCond2 hCond3 hC1 hamax hlam hδ
  refine ⟨E, hE_meas, hPE, ?_⟩
  intro ω hω
  have hCp_nonneg : 0 ≤ Cp := by
    have h0 := hCp 1 1 le_rfl le_rfl ω ⟨0, by omega⟩
    simpa using h0
  have hA_sparse : ∀ s : ℕ, 1 ≤ s → IsOneSparse (A s ω) := by
    intro s hs
    exact (hCond3 s hs ω (A s ω) ((hPLB s hs).1 ω).1).1
  have hA_norm : ∀ s : ℕ, 1 ≤ s → ∑ i : Fin d, A s ω i ^ 2 ≤ amax ^ 2 := by
    intro s hs
    have hsq_le := (hCond3 s hs ω (A s ω) ((hPLB s hs).1 ω).1).2
    have hsum_nonneg : 0 ≤ ∑ i : Fin d, A s ω i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    calc
      ∑ i : Fin d, A s ω i ^ 2 = (Real.sqrt (∑ i : Fin d, A s ω i ^ 2)) ^ 2 :=
        (Real.sq_sqrt hsum_nonneg).symm
      _ ≤ amax ^ 2 := sq_le_sq' (by linarith [Real.sqrt_nonneg (∑ i : Fin d, A s ω i ^ 2)]) hsq_le
  let vDiag : ℕ → Fin d → ℝ :=
    fun m i => lam + ∑ s ∈ Finset.range m, A (s + 1) ω i ^ 2
  have hv_pos : ∀ (m : ℕ) (i : Fin d), 0 < vDiag m i := by
    intro m i
    exact add_pos_of_pos_of_nonneg hlam (Finset.sum_nonneg fun s _ => sq_nonneg _)
  have hV_eq : ∀ m : ℕ,
      BanditAlgorithm.regularizedDesignMatrix d lam A m ω = Matrix.diagonal (vDiag m) :=
    fun m => regDesign_eq_diagonal lam A m ω hA_sparse
  have hV_inv : ∀ m : ℕ,
      (BanditAlgorithm.regularizedDesignMatrix d lam A m ω)⁻¹ =
        Matrix.diagonal (fun i => (vDiag m i)⁻¹) := by
    intro m
    rw [hV_eq m, inv_diagonal_pos (vDiag m) (hv_pos m)]
  let I : Finset ℕ := Finset.Icc 1 T0
  let r : ℕ → ℝ := fun t => bestValue (𝒜 t ω) (ξ t ω) - ξ t ω ⬝ᵥ A t ω
  have hr_two : ∀ t ∈ I, r t ≤ 2 := by
    intro t ht
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
    have hAt : A t ω ∈ 𝒜 t ω := ((hPLB t ht1).1 ω).1
    have hne : (𝒜 t ω).Nonempty := ⟨A t ω, hAt⟩
    have hbv : bestValue (𝒜 t ω) (ξ t ω) ≤ 1 := by
      simp only [bestValue, hne, ↓reduceDIte]
      refine Finset.sup'_le hne _ fun a ha => ?_
      exact (abs_le.mp (hCond1 t ht1 ω a ha)).2
    have hAt_ge : -1 ≤ ξ t ω ⬝ᵥ A t ω := (abs_le.mp (hCond1 t ht1 ω (A t ω) hAt)).1
    dsimp [r]
    linarith
  let O : Finset ℕ := I.filter (fun t => availIdx (𝒜 t ω) ⊆ pastIdx A t ω)
  let F : Finset ℕ := I.filter (fun t => ¬ availIdx (𝒜 t ω) ⊆ pastIdx A t ω)
  have hregret_split : plbRegret ξ 𝒜 A T0 ω = (∑ t ∈ O, r t) + (∑ t ∈ F, r t) := by
    unfold plbRegret
    exact (Finset.sum_filter_add_sum_filter_not I
      (fun t => availIdx (𝒜 t ω) ⊆ pastIdx A t ω) r).symm
  -- Bound forced-exploration rounds: card F ≤ d, so ∑_{t ∈ F} r_t ≤ 2d.
  have hF_bound : ∑ t ∈ F, r t ≤ 2 * (d : ℝ) := by
    have hsupp_ne : ∀ t ∈ F, (supp (A t ω)).Nonempty := by
      intro t ht
      have ht1 : 1 ≤ t := (Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1).1
      obtain ⟨k, c, hc, hAk⟩ := hA_sparse t ht1
      refine ⟨k, ?_⟩
      simp [supp, hAk, hc]
    let idxChoice : ℕ → Fin d := fun t =>
      if h : (supp (A t ω)).Nonempty then h.choose else ⟨0, by omega⟩
    have hidx_mem : ∀ t ∈ F, idxChoice t ∈ supp (A t ω) := by
      intro t ht
      have hne := hsupp_ne t ht
      simp only [idxChoice, hne, ↓reduceDIte]
      exact hne.choose_spec
    have hinj : Set.InjOn idxChoice (F : Set ℕ) := by
      intro t1 ht1F t2 ht2F heq
      have ht1I : t1 ∈ I := (Finset.mem_filter.mp ht1F).1
      have ht2I : t2 ∈ I := (Finset.mem_filter.mp ht2F).1
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hnot2 : ¬ availIdx (𝒜 t2 ω) ⊆ pastIdx A t2 ω := (Finset.mem_filter.mp ht2F).2
        have hdisj2 : Disjoint (supp (A t2 ω)) (pastIdx A t2 ω) :=
          ((hrun ω t2 ht2I).2.1) hnot2
        have hmem_past : idxChoice t1 ∈ pastIdx A t2 ω := by
          unfold pastIdx
          refine Finset.mem_biUnion.mpr ⟨t1, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ht1I).1, ?_⟩,
            hidx_mem t1 ht1F⟩
          omega
        rw [heq] at hmem_past
        exact Finset.disjoint_left.mp hdisj2 (hidx_mem t2 ht2F) hmem_past
      · have hnot1 : ¬ availIdx (𝒜 t1 ω) ⊆ pastIdx A t1 ω := (Finset.mem_filter.mp ht1F).2
        have hdisj1 : Disjoint (supp (A t1 ω)) (pastIdx A t1 ω) :=
          ((hrun ω t1 ht1I).2.1) hnot1
        have hmem_past : idxChoice t2 ∈ pastIdx A t1 ω := by
          unfold pastIdx
          refine Finset.mem_biUnion.mpr ⟨t2, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ht2I).1, ?_⟩,
            hidx_mem t2 ht2F⟩
          omega
        rw [← heq] at hmem_past
        exact Finset.disjoint_left.mp hdisj1 (hidx_mem t1 ht1F) hmem_past
    have hF_card : F.card ≤ d := by
      calc
        F.card = (F.image idxChoice).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_le_univ _
        _ = d := Fintype.card_fin d
    have hF_card_real : (F.card : ℝ) ≤ (d : ℝ) := by exact_mod_cast hF_card
    calc
      ∑ t ∈ F, r t ≤ ∑ _ ∈ F, (2 : ℝ) :=
        Finset.sum_le_sum fun t ht => hr_two t (Finset.mem_filter.mp ht).1
      _ = (F.card : ℝ) * 2 := by simp
      _ ≤ 2 * (d : ℝ) := by linarith
  -- Bound optimistic rounds using perturbation, shadow ellipsoid membership, and LinUCB optimality.
  let β : ℕ → ℝ := betaTilde C1 amax lam d δ
  have hβ_ge_one : ∀ t : ℕ, 1 ≤ β t := fun t => le_max_left 1 _
  have hβ_nonneg : ∀ t : ℕ, 0 ≤ β t := fun t => le_trans zero_le_one (hβ_ge_one t)
  let w : ℕ → ℝ := fun t =>
    min 1 (mNorm (BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω)⁻¹ (A t ω))
  have hw_nonneg : ∀ t : ℕ, 0 ≤ w t :=
    fun t => le_min zero_le_one (Real.sqrt_nonneg _)
  have hO_term : ∀ t ∈ O, r t ≤ 2 * Real.sqrt (β T0) * w t + 2 * amax * Cp := by
    intro t htO
    have htI : t ∈ I := (Finset.mem_filter.mp htO).1
    have hsub : availIdx (𝒜 t ω) ⊆ pastIdx A t ω := (Finset.mem_filter.mp htO).2
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp htI).1
    have htT0 : t ≤ T0 := (Finset.mem_Icc.mp htI).2
    have hAt : A t ω ∈ 𝒜 t ω := ((hPLB t ht1).1 ω).1
    have hne : (𝒜 t ω).Nonempty := ⟨A t ω, hAt⟩
    -- Show 2 ≤ t since availIdx (𝒜 t ω) is nonempty and contained in pastIdx A t ω.
    have ht2 : 2 ≤ t := by
      obtain ⟨k, c, hc, hAk⟩ := hA_sparse t ht1
      have hk_supp : k ∈ supp (A t ω) := by simp [supp, hAk, hc]
      have hk_avail : k ∈ availIdx (𝒜 t ω) := Finset.mem_biUnion.mpr ⟨A t ω, hAt, hk_supp⟩
      have hk_past : k ∈ pastIdx A t ω := hsub hk_avail
      obtain ⟨s, hsIcc, _⟩ := Finset.mem_biUnion.mp hk_past
      have hs1 := (Finset.mem_Icc.mp hsIcc).1
      have hst := (Finset.mem_Icc.mp hsIcc).2
      omega
    -- Perturbation bound on available actions: |(shadowParam - ξ_t) ⬝ᵥ a| ≤ amax * Cp.
    have hpert_act : ∀ a ∈ 𝒜 t ω, |(shadowParam A ξ t ω - ξ t ω) ⬝ᵥ a| ≤ amax * Cp := by
      intro a ha
      have ha_cond := hCond3 t ht1 ω a ha
      obtain ⟨i, c, hc, rfl⟩ := ha_cond.1
      have hc_abs : |c| ≤ amax := by
        have hsum_c : ∑ j : Fin d, ((Pi.single i c : Fin d → ℝ) j) ^ 2 = c ^ 2 := by
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hji; simp [hji]
          · intro hi; exact absurd (Finset.mem_univ i) hi
        have hsqrt_c : Real.sqrt (∑ j : Fin d, ((Pi.single i c : Fin d → ℝ) j) ^ 2) = |c| := by
          rw [hsum_c, Real.sqrt_sq_eq_abs]
        linarith [ha_cond.2]
      have hi_supp : i ∈ supp (Pi.single i c) := by simp [supp, hc]
      have hi_avail : i ∈ availIdx (𝒜 t ω) :=
        Finset.mem_biUnion.mpr ⟨Pi.single i c, ha, hi_supp⟩
      have hi_past : i ∈ pastIdx A t ω := hsub hi_avail
      obtain ⟨s0, hs0_Icc, hs0_supp⟩ := Finset.mem_biUnion.mp hi_past
      have hs0_ne : A s0 ω i ≠ 0 := by simpa [supp] using hs0_supp
      let S1 : Finset ℕ := (Finset.Icc 1 (t - 1)).filter (fun s => A s ω i ≠ 0)
      have hS1_ne : S1.Nonempty := ⟨s0, Finset.mem_filter.mpr ⟨hs0_Icc, hs0_ne⟩⟩
      let S2 : Set ℕ := {s : ℕ | 1 ≤ s}
      have hS12 : (S1 : Set ℕ) ⊆ S2 := by
        intro s hs
        exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
      have hnum_eq : ∑ s ∈ Finset.Icc 1 (t - 1), A s ω i ^ 2 * ξ s ω i =
          ∑ s ∈ S1, A s ω i ^ 2 * ξ s ω i := by
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (t - 1)) (fun s => A s ω i ≠ 0)]
        have hzero : ∑ s ∈ (Finset.Icc 1 (t - 1)).filter (fun s => ¬ A s ω i ≠ 0),
            A s ω i ^ 2 * ξ s ω i = 0 := by
          refine Finset.sum_eq_zero fun s hs => ?_
          have hs0 : A s ω i = 0 := not_not.mp (Finset.mem_filter.mp hs).2
          simp [hs0]
        rw [hzero, add_zero]
      have hden_eq : ∑ s ∈ Finset.Icc 1 (t - 1), A s ω i ^ 2 = ∑ s ∈ S1, A s ω i ^ 2 := by
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (t - 1)) (fun s => A s ω i ≠ 0)]
        have hzero : ∑ s ∈ (Finset.Icc 1 (t - 1)).filter (fun s => ¬ A s ω i ≠ 0),
            A s ω i ^ 2 = 0 := by
          refine Finset.sum_eq_zero fun s hs => ?_
          have hs0 : A s ω i = 0 := not_not.mp (Finset.mem_filter.mp hs).2
          simp [hs0]
        rw [hzero, add_zero]
      have hcoord_le : |shadowParam A ξ t ω i - ξ t ω i| ≤ Cp := by
        unfold shadowParam
        rw [hnum_eq, hden_eq]
        refine LuoSunLiu.DIP.lemma_S1 S1 S2 hS12 hS1_ne
          (fun s => ξ s ω i) (fun s => A s ω i ^ 2) Cp ?_ ?_ t ht1
        · intro u hu v hv
          exact hCp u v hu hv ω i
        · intro s hs
          exact sq_pos_of_ne_zero (Finset.mem_filter.mp hs).2
      have hdot : (shadowParam A ξ t ω - ξ t ω) ⬝ᵥ Pi.single i c =
          (shadowParam A ξ t ω i - ξ t ω i) * c := by
        simp [dotProduct_single]
      rw [hdot, abs_mul]
      calc
        |shadowParam A ξ t ω i - ξ t ω i| * |c| ≤ Cp * amax :=
          mul_le_mul hcoord_le hc_abs (abs_nonneg c) hCp_nonneg
        _ = amax * Cp := mul_comm Cp amax
    -- Ellipsoid membership of shadowParam A ξ t ω on E.
    have hell_t :
        (shadowParam A ξ t ω - BanditAlgorithm.regularizedLeastSquares d lam A Z (t - 1) ω) ⬝ᵥ
          BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω *ᵥ
            (shadowParam A ξ t ω - BanditAlgorithm.regularizedLeastSquares d lam A Z (t - 1) ω) ≤
          β t := by
      have hnorm_le := hE_ell ω hω t ht2
      let diff := shadowParam A ξ t ω -
        BanditAlgorithm.regularizedLeastSquares d lam A Z (t - 1) ω
      have hq_nonneg : 0 ≤ diff ⬝ᵥ
          BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω *ᵥ diff := by
        rw [hV_eq (t - 1), dot_diag_mulVec]
        exact Finset.sum_nonneg fun i _ =>
          mul_nonneg (le_of_lt (hv_pos (t - 1) i)) (sq_nonneg _)
      have hm_nonneg : 0 ≤
          mNorm (BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω) diff :=
        Real.sqrt_nonneg _
      have hsq_le : diff ⬝ᵥ
          BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω *ᵥ diff ≤
          (C1 * Real.sqrt (lam * d) +
            Real.sqrt (2 * Real.log (1 / δ) +
              (d : ℝ) * Real.log (((d : ℝ) * lam + ((t : ℝ) - 1) * amax ^ 2) / ((d : ℝ) * lam)))) ^ 2 := by
        calc
          diff ⬝ᵥ BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω *ᵥ diff
              = (mNorm (BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω) diff) ^ 2 :=
                (Real.sq_sqrt hq_nonneg).symm
          _ ≤ _ := sq_le_sq' (by linarith) hnorm_le
      exact hsq_le.trans (le_max_right 1 _)
    -- Attain bestValue by some a_star ∈ 𝒜 t ω.
    have hbv_mem : ∃ a_star ∈ 𝒜 t ω, bestValue (𝒜 t ω) (ξ t ω) = ξ t ω ⬝ᵥ a_star := by
      simp only [bestValue, hne, ↓reduceDIte]
      obtain ⟨a_star, ha_star, heq⟩ :=
        Finset.exists_mem_eq_sup' hne (fun a => ξ t ω ⬝ᵥ a)
      exact ⟨a_star, ha_star, heq⟩
    obtain ⟨a_star, ha_star, hbv_eq⟩ := hbv_mem
    have hucb_upper : shadowParam A ξ t ω ⬝ᵥ a_star ≤ linUCB lam (β t) A Z t ω a_star := by
      have hgreat := (LuoSunLiu.DIP.lemma_2.{_, 0}).1 lam (β t) A Z t ω a_star hlam (hβ_nonneg t)
      exact hgreat.2 ⟨shadowParam A ξ t ω, hell_t, rfl⟩
    have hucb_opt : linUCB lam (β t) A Z t ω a_star ≤ linUCB lam (β t) A Z t ω (A t ω) :=
      ((hrun ω t htI).2.2) hsub a_star ha_star
    have hucb_neg : shadowParam A ξ t ω ⬝ᵥ (-A t ω) ≤ linUCB lam (β t) A Z t ω (-A t ω) := by
      have hgreat := (LuoSunLiu.DIP.lemma_2.{_, 0}).1 lam (β t) A Z t ω (-A t ω) hlam (hβ_nonneg t)
      exact hgreat.2 ⟨shadowParam A ξ t ω, hell_t, rfl⟩
    have hmNorm_neg :
        mNorm (BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω)⁻¹ (-A t ω) =
          mNorm (BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω)⁻¹ (A t ω) := by
      unfold mNorm
      simp [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct]
    have hshadow_diff :
        shadowParam A ξ t ω ⬝ᵥ a_star - shadowParam A ξ t ω ⬝ᵥ A t ω ≤
          2 * Real.sqrt (β t) *
            mNorm (BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω)⁻¹ (A t ω) := by
      have h1 : - (shadowParam A ξ t ω ⬝ᵥ A t ω) ≤
          - (BanditAlgorithm.regularizedLeastSquares d lam A Z (t - 1) ω ⬝ᵥ A t ω) +
            Real.sqrt (β t) *
              mNorm (BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω)⁻¹ (A t ω) := by
        simpa [linUCB, dotProduct_neg, hmNorm_neg] using hucb_neg
      have h2 : shadowParam A ξ t ω ⬝ᵥ a_star ≤
          BanditAlgorithm.regularizedLeastSquares d lam A Z (t - 1) ω ⬝ᵥ A t ω +
            Real.sqrt (β t) *
              mNorm (BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω)⁻¹ (A t ω) := by
        simpa [linUCB] using hucb_upper.trans hucb_opt
      linarith
    have hβ_mono : Real.sqrt (β t) ≤ Real.sqrt (β T0) :=
      Real.sqrt_le_sqrt (betaTilde_mono hC1 hlam hd ht1 htT0)
    have hrt_ucb : r t ≤
        2 * Real.sqrt (β T0) *
          mNorm (BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω)⁻¹ (A t ω) +
          2 * amax * Cp := by
      have hp1 : ξ t ω ⬝ᵥ a_star - shadowParam A ξ t ω ⬝ᵥ a_star ≤ amax * Cp := by
        have habs := hpert_act a_star ha_star
        have hsub_dot : (shadowParam A ξ t ω - ξ t ω) ⬝ᵥ a_star =
            shadowParam A ξ t ω ⬝ᵥ a_star - ξ t ω ⬝ᵥ a_star := sub_dotProduct _ _ _
        rw [hsub_dot] at habs
        linarith [(abs_le.mp habs).1]
      have hp2 : shadowParam A ξ t ω ⬝ᵥ A t ω - ξ t ω ⬝ᵥ A t ω ≤ amax * Cp := by
        have habs := hpert_act (A t ω) hAt
        have hsub_dot : (shadowParam A ξ t ω - ξ t ω) ⬝ᵥ A t ω =
            shadowParam A ξ t ω ⬝ᵥ A t ω - ξ t ω ⬝ᵥ A t ω := sub_dotProduct _ _ _
        rw [hsub_dot] at habs
        exact (abs_le.mp habs).2
      have hdecomp_r : r t =
          (ξ t ω ⬝ᵥ a_star - shadowParam A ξ t ω ⬝ᵥ a_star) +
          (shadowParam A ξ t ω ⬝ᵥ A t ω - ξ t ω ⬝ᵥ A t ω) +
          (shadowParam A ξ t ω ⬝ᵥ a_star - shadowParam A ξ t ω ⬝ᵥ A t ω) := by
        dsimp [r]
        rw [hbv_eq]
        ring
      have hnorm_nonneg :
          0 ≤ mNorm (BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω)⁻¹ (A t ω) :=
        Real.sqrt_nonneg _
      have hmul_mono :
          2 * Real.sqrt (β t) *
              mNorm (BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω)⁻¹ (A t ω) ≤
            2 * Real.sqrt (β T0) *
              mNorm (BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω)⁻¹ (A t ω) :=
        mul_le_mul_of_nonneg_right (by linarith) hnorm_nonneg
      linarith
    have hrt_two : r t ≤ 2 * Real.sqrt (β T0) * 1 + 2 * amax * Cp := by
      have hsqrt_ge_one : 1 ≤ Real.sqrt (β T0) := by
        calc
          (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
          _ ≤ Real.sqrt (β T0) := Real.sqrt_le_sqrt (hβ_ge_one T0)
      have hcp_term_nonneg : 0 ≤ 2 * amax * Cp :=
        mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hamax)) hCp_nonneg
      linarith [hr_two t htI]
    by_cases hmin :
        1 ≤ mNorm (BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω)⁻¹ (A t ω)
    · have hw_eq : w t = 1 := min_eq_left hmin
      rw [hw_eq]
      exact hrt_two
    · have hw_eq :
          w t = mNorm (BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω)⁻¹ (A t ω) :=
        min_eq_right (le_of_lt (not_le.mp hmin))
      rw [hw_eq]
      exact hrt_ucb
  -- Sum optimistic bound over O ⊆ I.
  have hO_sum_I : ∑ t ∈ O, r t ≤
      2 * Real.sqrt (β T0) * (∑ t ∈ I, w t) + 2 * amax * Cp * (T0 : ℝ) := by
    have hterm_nonneg : ∀ t : ℕ, 0 ≤ 2 * Real.sqrt (β T0) * w t + 2 * amax * Cp := by
      intro t
      exact add_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (hw_nonneg t))
        (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hamax)) hCp_nonneg)
    have hO_sub_I : O ⊆ I := Finset.filter_subset _ _
    have hI_card : (I.card : ℝ) = (T0 : ℝ) := by
      have : I.card = T0 := by simp [I]
      exact_mod_cast this
    calc
      ∑ t ∈ O, r t ≤ ∑ t ∈ O, (2 * Real.sqrt (β T0) * w t + 2 * amax * Cp) :=
        Finset.sum_le_sum hO_term
      _ ≤ ∑ t ∈ I, (2 * Real.sqrt (β T0) * w t + 2 * amax * Cp) :=
        Finset.sum_le_sum_of_subset_of_nonneg hO_sub_I (fun t _ _ => hterm_nonneg t)
      _ = 2 * Real.sqrt (β T0) * (∑ t ∈ I, w t) + (I.card : ℝ) * (2 * amax * Cp) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      _ = 2 * Real.sqrt (β T0) * (∑ t ∈ I, w t) + 2 * amax * Cp * (T0 : ℝ) := by
        rw [hI_card]; ring
  -- Elliptical potential lemma via diagonal telescoping.
  let q : ℕ → ℝ := fun t =>
    A t ω ⬝ᵥ (BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω)⁻¹ *ᵥ A t ω
  have hq_nonneg : ∀ t : ℕ, 0 ≤ q t := by
    intro t
    dsimp [q]
    rw [hV_inv (t - 1), dot_diag_mulVec]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (inv_nonneg.mpr (le_of_lt (hv_pos (t - 1) i))) (sq_nonneg _)
  have hw_sq : ∀ t : ℕ, w t ^ 2 = min 1 (q t) := by
    intro t
    have hm_eq : mNorm (BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω)⁻¹ (A t ω) =
        Real.sqrt (q t) := rfl
    dsimp [w]
    rw [hm_eq]
    by_cases h1 : 1 ≤ Real.sqrt (q t)
    · have h1q : 1 ≤ q t := by
        calc
          (1 : ℝ) = 1 ^ 2 := by norm_num
          _ ≤ (Real.sqrt (q t)) ^ 2 := sq_le_sq' (by linarith) h1
          _ = q t := Real.sq_sqrt (hq_nonneg t)
      rw [min_eq_left h1, min_eq_left h1q]
      norm_num
    · have hq1 : q t ≤ 1 := by
        have hlt := le_of_lt (not_le.mp h1)
        calc
          q t = (Real.sqrt (q t)) ^ 2 := (Real.sq_sqrt (hq_nonneg t)).symm
          _ ≤ 1 ^ 2 := sq_le_sq' (by linarith [Real.sqrt_nonneg (q t)]) hlt
          _ = 1 := by norm_num
      rw [min_eq_right (le_of_lt (not_le.mp h1)), min_eq_right hq1, Real.sq_sqrt (hq_nonneg t)]
  let gPot : ℕ → ℝ := fun m => ∑ i : Fin d, Real.log (vDiag m i)
  have hlog_step : ∀ m : ℕ, Real.log (1 + q (m + 1)) = gPot (m + 1) - gPot m := by
    intro m
    obtain ⟨k, c, _, hAk⟩ := hA_sparse (m + 1) (Nat.succ_pos m)
    have hq_val : q (m + 1) = (vDiag m k)⁻¹ * c ^ 2 := by
      dsimp [q]
      rw [hV_inv m, dot_diag_mulVec, hAk]
      rw [Finset.sum_eq_single k]
      · simp
      · intro i _ hik; simp [hik]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    have hv_step : ∀ i : Fin d, vDiag (m + 1) i = vDiag m i + A (m + 1) ω i ^ 2 := by
      intro i
      simp only [vDiag, Finset.sum_range_succ]
      ring
    have hg_diff : gPot (m + 1) - gPot m = Real.log (vDiag (m + 1) k / vDiag m k) := by
      dsimp [gPot]
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single k]
      · rw [Real.log_div (hv_pos (m + 1) k).ne' (hv_pos m k).ne']
      · intro i _ hik
        have hAi : A (m + 1) ω i = 0 := by simp [hAk, hik]
        rw [hv_step i, hAi]
        simp
      · intro hk; exact absurd (Finset.mem_univ k) hk
    have hratio : vDiag (m + 1) k / vDiag m k = 1 + q (m + 1) := by
      have hAk_k : A (m + 1) ω k = c := by simp [hAk]
      rw [hv_step k, hAk_k, hq_val]
      have hvk_ne : vDiag m k ≠ 0 := (hv_pos m k).ne'
      field_simp [hvk_ne]
    rw [hg_diff, hratio]
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hdlam_pos : 0 < (d : ℝ) * lam := mul_pos hd_pos hlam
  let M : ℝ := ((d : ℝ) * lam + (T0 : ℝ) * amax ^ 2) / ((d : ℝ) * lam)
  have hM_pos : 0 < M := by
    refine div_pos ?_ hdlam_pos
    exact add_pos_of_pos_of_nonneg hdlam_pos
      (mul_nonneg (Nat.cast_nonneg T0) (sq_nonneg amax))
  have hM_ge_one : 1 ≤ M := by
    dsimp [M]
    rw [le_div_iff₀ hdlam_pos]
    linarith [mul_nonneg (Nat.cast_nonneg T0) (sq_nonneg amax)]
  have hg_tele : gPot T0 - gPot 0 ≤ (d : ℝ) * Real.log M := by
    have hg_eq : gPot T0 - gPot 0 = ∑ i : Fin d, Real.log (vDiag T0 i / lam) := by
      dsimp [gPot]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hv0 : vDiag 0 i = lam := by simp [vDiag]
      rw [hv0, Real.log_div (hv_pos T0 i).ne' hlam.ne']
    rw [hg_eq]
    have hpt : ∀ i : Fin d, Real.log (vDiag T0 i / lam) ≤
        Real.log M + (vDiag T0 i / lam / M - 1) := by
      intro i
      have hxi_pos : 0 < vDiag T0 i / lam := div_pos (hv_pos T0 i) hlam
      have hlog_split : Real.log (vDiag T0 i / lam) =
          Real.log M + Real.log (vDiag T0 i / lam / M) := by
        rw [← Real.log_mul hM_pos.ne' (div_pos hxi_pos hM_pos).ne',
          mul_div_cancel₀ _ hM_pos.ne']
      linarith [Real.log_le_sub_one_of_pos (div_pos hxi_pos hM_pos)]
    have hsum_log : ∑ i : Fin d, Real.log (vDiag T0 i / lam) ≤
        (d : ℝ) * Real.log M + ((∑ i : Fin d, (vDiag T0 i / lam)) / M - (d : ℝ)) := by
      calc
        ∑ i : Fin d, Real.log (vDiag T0 i / lam)
            ≤ ∑ i : Fin d, (Real.log M + (vDiag T0 i / lam / M - 1)) :=
              Finset.sum_le_sum fun i _ => hpt i
        _ = (d : ℝ) * Real.log M + ((∑ i : Fin d, (vDiag T0 i / lam)) / M - (d : ℝ)) := by
              simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div]
    have hsum_v : ∑ i : Fin d, vDiag T0 i ≤ (d : ℝ) * lam + (T0 : ℝ) * amax ^ 2 := by
      have hv_expand : ∑ i : Fin d, vDiag T0 i =
          (d : ℝ) * lam + ∑ s ∈ Finset.range T0, ∑ i : Fin d, A (s + 1) ω i ^ 2 := by
        simp only [vDiag, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        rw [Finset.sum_comm]
      rw [hv_expand]
      have hinner : ∑ s ∈ Finset.range T0, ∑ i : Fin d, A (s + 1) ω i ^ 2 ≤
          ∑ _ ∈ Finset.range T0, amax ^ 2 :=
        Finset.sum_le_sum fun s _ => hA_norm (s + 1) (Nat.succ_pos s)
      simpa using add_le_add_right hinner ((d : ℝ) * lam)
    have hsum_x : ∑ i : Fin d, (vDiag T0 i / lam) ≤ (d : ℝ) * M := by
      rw [← Finset.sum_div]
      have hdM : (d : ℝ) * M = ((d : ℝ) * lam + (T0 : ℝ) * amax ^ 2) / lam := by
        dsimp [M]
        field_simp [hd_pos.ne', hlam.ne']
      rw [hdM]
      exact div_le_div_of_nonneg_right hsum_v (le_of_lt hlam)
    have hdiv_le : (∑ i : Fin d, (vDiag T0 i / lam)) / M ≤ (d : ℝ) :=
      (div_le_iff₀ hM_pos).2 hsum_x
    linarith
  have hw_sq_sum : ∑ t ∈ I, w t ^ 2 ≤ 2 * (d : ℝ) * Real.log M := by
    have hsum_I_eq : ∑ t ∈ I, Real.log (1 + q t) = gPot T0 - gPot 0 := by
      have hI_Ico : I = Finset.Ico 1 (T0 + 1) := rfl
      rw [hI_Ico, Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel]
      have hcongr : ∑ m ∈ Finset.range T0, Real.log (1 + q (1 + m)) =
          ∑ m ∈ Finset.range T0, (gPot (m + 1) - gPot m) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [add_comm 1 m, hlog_step m]
      rw [hcongr, Finset.sum_range_sub]
    calc
      ∑ t ∈ I, w t ^ 2 = ∑ t ∈ I, min 1 (q t) :=
        Finset.sum_congr rfl fun t _ => hw_sq t
      _ ≤ ∑ t ∈ I, 2 * Real.log (1 + q t) := by
        refine Finset.sum_le_sum fun t _ => ?_
        have hmin0 : 0 ≤ min 1 (q t) := le_min zero_le_one (hq_nonneg t)
        have hmin1 : min 1 (q t) ≤ 1 := min_le_left 1 (q t)
        have h1 : min 1 (q t) ≤ 2 * Real.log (1 + min 1 (q t)) :=
          self_le_two_mul_log_one_add hmin0 hmin1
        have h2 : Real.log (1 + min 1 (q t)) ≤ Real.log (1 + q t) :=
          Real.log_le_log (by linarith) (by linarith [min_le_right 1 (q t)])
        linarith
      _ = 2 * ∑ t ∈ I, Real.log (1 + q t) := (Finset.mul_sum _ _ _).symm
      _ = 2 * (gPot T0 - gPot 0) := by rw [hsum_I_eq]
      _ ≤ 2 * (d : ℝ) * Real.log M := by linarith
  -- Cauchy-Schwarz on ∑_{t ∈ I} w_t.
  have hcs_I : (∑ t ∈ I, w t) ^ 2 ≤ (T0 : ℝ) * (∑ t ∈ I, w t ^ 2) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq I (fun _ => (1 : ℝ)) w
    simpa [I] using hcs
  have hell_final :
      Real.sqrt (β T0) * (∑ t ∈ I, w t) ≤
        Real.sqrt (2 * (d : ℝ) * (T0 : ℝ) * β T0 * Real.log M) := by
    have hLHS_nonneg : 0 ≤ Real.sqrt (β T0) * (∑ t ∈ I, w t) :=
      mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun t _ => hw_nonneg t)
    have hsq_bound :
        (Real.sqrt (β T0) * (∑ t ∈ I, w t)) ^ 2 ≤
          2 * (d : ℝ) * (T0 : ℝ) * β T0 * Real.log M := by
      calc
        (Real.sqrt (β T0) * (∑ t ∈ I, w t)) ^ 2
            = β T0 * (∑ t ∈ I, w t) ^ 2 := by
              rw [mul_pow, Real.sq_sqrt (hβ_nonneg T0)]
        _ ≤ β T0 * ((T0 : ℝ) * (∑ t ∈ I, w t ^ 2)) :=
            mul_le_mul_of_nonneg_left hcs_I (hβ_nonneg T0)
        _ ≤ β T0 * ((T0 : ℝ) * (2 * (d : ℝ) * Real.log M)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hw_sq_sum (Nat.cast_nonneg T0)) (hβ_nonneg T0)
        _ = 2 * (d : ℝ) * (T0 : ℝ) * β T0 * Real.log M := by ring
    calc
      Real.sqrt (β T0) * (∑ t ∈ I, w t)
          = Real.sqrt ((Real.sqrt (β T0) * (∑ t ∈ I, w t)) ^ 2) :=
            (Real.sqrt_sq hLHS_nonneg).symm
      _ ≤ Real.sqrt (2 * (d : ℝ) * (T0 : ℝ) * β T0 * Real.log M) :=
            Real.sqrt_le_sqrt hsq_bound
  -- Combine O and F bounds.
  rw [hregret_split]
  dsimp [β, M] at hell_final hO_sum_I
  linarith
