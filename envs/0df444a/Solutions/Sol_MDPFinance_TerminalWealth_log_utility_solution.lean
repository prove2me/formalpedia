-- Prove2me | solution 1 for MDPFinance.TerminalWealth.log_utility_solution
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T00:15:42.329884+00:00
-- url     : https://prove2.me/submissions/87a76a98-fe1d-4364-8849-0ab4e1fd73b4

import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_Market
import Definitions.Def_MDPFinance_TerminalWealth_LogAuxiliary

open MeasureTheory ProbabilityTheory


namespace MDPFinance.TerminalWealth

section Minim
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

def twNullSp (μ : Measure Ω) (R : Ω → Fin d → ℝ) : Submodule ℝ (Fin d → ℝ) where
  carrier := {a | ∀ᵐ ω ∂μ, ∑ k, a k * R ω k = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    filter_upwards [ha, hb] with ω h1 h2
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, h1, h2, add_zero]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    exact Filter.Eventually.of_forall (fun ω => by simp)
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    filter_upwards [ha] with ω h
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, h, mul_zero]

lemma tw_sum_meas (R : Ω → Fin d → ℝ) (hR : Measurable R) (u : Fin d → ℝ) :
    Measurable (fun ω => ∑ k, u k * R ω k) := by
  fun_prop

lemma tw_phi_pos (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → Fin d → ℝ)
    (hR : Measurable R) (hNA : NoArbitrageOnePeriod μ R) (u : Fin d → ℝ)
    (hu : u ∉ twNullSp μ R) :
    0 < ∫ ω, min 1 (max (-(∑ k, u k * R ω k)) 0) ∂μ := by
  have hm := tw_sum_meas R hR u
  have hint : Integrable (fun ω => min 1 (max (-(∑ k, u k * R ω k)) 0)) μ := by
    refine (integrable_const (1 : ℝ)).mono' ?_ ?_
    · exact (measurable_const.min (hm.neg.max measurable_const)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · have := le_max_right (-(∑ k, u k * R ω k)) 0
        have : (0:ℝ) ≤ min 1 (max (-(∑ k, u k * R ω k)) 0) := le_min zero_le_one this
        linarith
      · exact min_le_left _ _
  have hnn : (0 : Ω → ℝ) ≤ fun ω => min 1 (max (-(∑ k, u k * R ω k)) 0) :=
    fun ω => le_min zero_le_one (le_max_right _ _)
  rw [integral_pos_iff_support_of_nonneg hnn hint]
  have hsupp : Function.support (fun ω => min 1 (max (-(∑ k, u k * R ω k)) 0)) =
      {ω | ∑ k, u k * R ω k < 0} := by
    ext ω
    simp only [Function.mem_support, Set.mem_setOf_eq]
    constructor
    · intro h
      by_contra h'
      push_neg at h'
      apply h
      rw [max_eq_right (by linarith), min_eq_right zero_le_one]
    · intro h h0
      rcases min_choice (1:ℝ) (max (-(∑ k, u k * R ω k)) 0) with h1 | h1
      · rw [h1] at h0; norm_num at h0
      · rw [h1, max_eq_left (by linarith)] at h0; linarith
  rw [hsupp]
  by_contra h0
  push_neg at h0
  have h0' : μ {ω | ∑ k, u k * R ω k < 0} = 0 := nonpos_iff_eq_zero.mp h0
  have hge : ∀ᵐ ω ∂μ, 0 ≤ ∑ k, u k * R ω k := by
    rw [ae_iff]; simpa using h0'
  have hpos : μ {ω | 0 < ∑ k, u k * R ω k} = 0 := by
    by_contra hp
    exact hNA ⟨u, hge, pos_iff_ne_zero.mpr hp⟩
  have hle : ∀ᵐ ω ∂μ, ∑ k, u k * R ω k ≤ 0 := by
    rw [ae_iff]; simpa using hpos
  apply hu
  show ∀ᵐ ω ∂μ, ∑ k, u k * R ω k = 0
  filter_upwards [hge, hle] with ω h1 h2
  linarith

lemma tw_phi_cont (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → Fin d → ℝ)
    (hR : Measurable R) :
    Continuous (fun u : Fin d → ℝ => ∫ ω, min 1 (max (-(∑ k, u k * R ω k)) 0) ∂μ) := by
  refine continuous_of_dominated (bound := fun _ => 1) ?_ ?_ (integrable_const _) ?_
  · intro u
    exact (measurable_const.min ((tw_sum_meas R hR u).neg.max measurable_const)).aestronglyMeasurable
  · intro u
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := le_max_right (-(∑ k, u k * R ω k)) 0
      have : (0:ℝ) ≤ min 1 (max (-(∑ k, u k * R ω k)) 0) := le_min zero_le_one this
      linarith
    · exact min_le_left _ _
  · refine Filter.Eventually.of_forall (fun ω => ?_)
    fun_prop

end Minim

section Multi
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

def twW (i : ℕ → ℝ) (π : ℕ → ℝ → (Fin d → ℝ)) : ℕ → ℕ → ℝ → (ℕ → Fin d → ℝ) → ℝ
  | 0, _, x, _ => x
  | (k + 1), n, x, r => twW i π k (n + 1) ((1 + i (n + 1)) * (x + ∑ j, π n x j * r (n + 1) j)) r

lemma tw_tw_eq (M : TerminalWealthMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ)) (k n : ℕ) (x : ℝ)
    (ω : Ω) : M.terminalWealth π k n x ω = twW M.i π k n x (fun j => M.R j ω) := by
  induction k generalizing n x with
  | zero => rfl
  | succ k ih => rw [TerminalWealthMarket.terminalWealth, twW]; exact ih _ _

lemma twW_congr (i : ℕ → ℝ) (π : ℕ → ℝ → (Fin d → ℝ)) (k n : ℕ) (x : ℝ)
    (r r' : ℕ → Fin d → ℝ) (h : ∀ j, n < j → j ≤ n + k → r j = r' j) :
    twW i π k n x r = twW i π k n x r' := by
  induction k generalizing n x with
  | zero => rfl
  | succ k ih =>
    rw [twW, twW, h (n + 1) (by omega) (by omega)]
    exact ih _ _ (fun j h1 h2 => h j (by omega) (by omega))

lemma twW_meas (i : ℕ → ℝ) (π : ℕ → ℝ → (Fin d → ℝ)) (k n : ℕ)
    (hπ : ∀ j, n ≤ j → j < n + k → Measurable (π j)) :
    Measurable (fun p : ℝ × (ℕ → Fin d → ℝ) => twW i π k n p.1 p.2) := by
  induction k generalizing n with
  | zero => exact measurable_fst
  | succ k ih =>
    have hπn : Measurable (π n) := hπ n le_rfl (by omega)
    have hT : Measurable (fun p : ℝ × (ℕ → Fin d → ℝ) =>
        ((1 + i (n + 1)) * (p.1 + ∑ j, π n p.1 j * p.2 (n + 1) j), p.2)) := by
      fun_prop
    exact (ih (n + 1) (fun j h1 h2 => hπ j (by omega) (by omega))).comp hT

lemma tw_lintegral_indep {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (Y : Ω → β) (hX : Measurable X)
    (hY : Measurable Y) (hXY : IndepFun X Y μ) (H : α × β → ENNReal) (hH : Measurable H) :
    ∫⁻ ω, H (X ω, Y ω) ∂μ = ∫⁻ ω, ∫⁻ ω', H (X ω, Y ω') ∂μ ∂μ := by
  have h1 : ∫⁻ ω, H (X ω, Y ω) ∂μ = ∫⁻ p, H p ∂(μ.map (fun ω => (X ω, Y ω))) :=
    (lintegral_map hH (hX.prodMk hY)).symm
  rw [h1, (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hXY,
    lintegral_prod _ hH.aemeasurable, lintegral_map (hH.lintegral_prod_right') hX]
  congr 1
  funext ω
  exact lintegral_map (hH.comp measurable_prodMk_left) hY

lemma tw_toENNReal (t : ℝ) : ((t : EReal) ⊔ 0).toENNReal = ENNReal.ofReal t := by
  rcases le_total t 0 with h | h
  · rw [sup_eq_right.mpr (by exact_mod_cast h), EReal.toENNReal_zero, ENNReal.ofReal_of_nonpos h]
  · rw [sup_eq_left.mpr (by exact_mod_cast h), EReal.toENNReal_of_ne_top (EReal.coe_ne_top t),
      EReal.toReal_coe]


noncomputable def twG (M : TerminalWealthMarket Ω d) (g : ℝ → ENNReal) (π : ℕ → ℝ → (Fin d → ℝ))
    (m : ℕ) (y : ℝ) : ENNReal :=
  ∫⁻ ω, g (M.terminalWealth π (M.N - m) m y ω) ∂M.measIP

lemma twG_decomp (M : TerminalWealthMarket Ω d) (g : ℝ → ENNReal) (hg : Measurable g) (π : ℕ → ℝ → (Fin d → ℝ)) (m : ℕ)
    (hm : m < M.N) (hπ : ∀ j, m ≤ j → j < M.N → Measurable (π j)) (y : ℝ) :
    twG M g π m y = ∫⁻ ω, twG M g π (m + 1)
      ((1 + M.i (m + 1)) * (y + ∑ j, π m y j * M.R (m + 1) ω j)) ∂M.measIP := by
  haveI := M.isProb
  set f : Fin M.N → Ω → (Fin d → ℝ) := fun j => M.R (j.val + 1) with hf
  have hfm : ∀ j, Measurable (f j) := fun j => M.hR_meas _ (by omega) (by omega)
  set S : Finset (Fin M.N) := {⟨m, hm⟩} with hS
  set T : Finset (Fin M.N) := Finset.univ.filter (fun j : Fin M.N => m < j.val) with hT
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [hS, Finset.mem_singleton] at ha
    rw [hT, Finset.mem_filter] at hb
    rw [ha] at hb
    exact lt_irrefl _ hb.2
  have hind := M.hR_indep.indepFun_finset S T hST hfm
  have hmS : (⟨m, hm⟩ : Fin M.N) ∈ S := Finset.mem_singleton_self _
  have hind2 := hind.comp (measurable_pi_apply (⟨⟨m, hm⟩, hmS⟩ : S)) measurable_id
  have hTmem : ∀ j : Fin M.N, m < j.val → j ∈ T := fun j hj => by
    rw [hT, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hj⟩
  let ext : (T → Fin d → ℝ) → (ℕ → Fin d → ℝ) := fun v j =>
    if h : j - 1 < M.N ∧ m < j - 1 then v ⟨⟨j - 1, h.1⟩, hTmem _ h.2⟩ else 0
  have hext_meas : Measurable ext := by
    refine measurable_pi_lambda _ (fun j => ?_)
    by_cases h : j - 1 < M.N ∧ m < j - 1
    · simp only [ext, dif_pos h]; exact measurable_pi_apply _
    · simp only [ext, dif_neg h]; exact measurable_const
  set Y : Ω → (T → Fin d → ℝ) := fun ω (j : T) => f j ω with hY
  have hYm : Measurable Y := measurable_pi_lambda _ (fun j => hfm j)
  have hext : ∀ ω j, m + 1 < j → j ≤ M.N → ext (Y ω) j = M.R j ω := by
    intro ω j h1 h2
    have h : j - 1 < M.N ∧ m < j - 1 := ⟨by omega, by omega⟩
    simp only [ext, dif_pos h, hY, hf]
    congr 1; omega
  have hk : M.N - m = (M.N - (m + 1)) + 1 := by omega
  set k := M.N - (m + 1) with hkdef
  let H : (Fin d → ℝ) × (T → Fin d → ℝ) → ENNReal := fun p =>
    g (twW M.i π k (m + 1)
      ((1 + M.i (m + 1)) * (y + ∑ j, π m y j * p.1 j)) (ext p.2))
  have hHm : Measurable H := by
    have h1 := twW_meas M.i π k (m + 1) (fun j h1 h2 => hπ j (by omega) (by omega))
    have h2 : Measurable (fun p : (Fin d → ℝ) × (T → Fin d → ℝ) =>
        ((1 + M.i (m + 1)) * (y + ∑ j, π m y j * p.1 j), ext p.2)) := by
      refine Measurable.prodMk ?_ (hext_meas.comp measurable_snd)
      fun_prop
    exact hg.comp (h1.comp h2)
  have hX : Measurable (fun ω => (fun ω (i : S) => f i ω) ω ⟨⟨m, hm⟩, hmS⟩) :=
    (measurable_pi_apply _).comp (measurable_pi_lambda _ (fun j => hfm j))
  have key := tw_lintegral_indep M.measIP _ Y hX hYm hind2 H hHm
  unfold twG
  rw [hk]
  have eL : ∀ ω, g (M.terminalWealth π (k + 1) m y ω) =
      H ((fun ω (i : S) => f i ω) ω ⟨⟨m, hm⟩, hmS⟩, Y ω) := by
    intro ω
    simp only [H]
    rw [tw_tw_eq, twW]
    congr 1
    apply twW_congr
    intro j h1 h2
    exact (hext ω j h1 (by omega)).symm
  simp_rw [eL]
  rw [key]
  congr 1
  funext ω
  have hMN : M.N - (m + 1) = k := rfl
  rw [hMN]
  congr 1
  funext ω'
  simp only [H]
  rw [tw_tw_eq]
  congr 1
  apply twW_congr
  intro j h1 h2
  exact hext ω' j h1 (by omega)

end Multi

section PowMin
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

lemma tw_dot_bound (R : Ω → Fin d → ℝ) (α : Fin d → ℝ) (ω : Ω) :
    |∑ k, α k * R ω k| ≤ ‖α‖ * ∑ k, |R ω k| := by
  calc |∑ k, α k * R ω k| ≤ ∑ k, |α k * R ω k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, ‖α‖ * |R ω k| := Finset.sum_le_sum (fun k _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm α k) (abs_nonneg _))
    _ = ‖α‖ * ∑ k, |R ω k| := (Finset.mul_sum _ _ _).symm

lemma tw_minmax_zero (s : ℝ) : min 1 (max (-s) 0) = 0 ↔ 0 ≤ s := by
  constructor
  · intro h
    by_contra hs
    push_neg at hs
    rw [max_eq_left (by linarith)] at h
    rcases min_choice (1:ℝ) (-s) with h1 | h1
    · rw [h1] at h; norm_num at h
    · rw [h1] at h; linarith
  · intro h
    rw [max_eq_right (by linarith), min_eq_right zero_le_one]

lemma tw_afrac_closed (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → Fin d → ℝ)
    (hR : Measurable R) :
    IsClosed {α : Fin d → ℝ | ∀ᵐ ω ∂μ, 0 ≤ 1 + ∑ k, α k * R ω k} := by
  have hmeas : ∀ α : Fin d → ℝ, Measurable (fun ω => min 1 (max (-(1 + ∑ k, α k * R ω k)) 0)) :=
    fun α => measurable_const.min (((tw_sum_meas R hR α).const_add 1).neg.max measurable_const)
  have hbd : ∀ α : Fin d → ℝ, ∀ ω, ‖min 1 (max (-(1 + ∑ k, α k * R ω k)) 0)‖ ≤ 1 := by
    intro α ω
    rw [Real.norm_eq_abs, abs_le]
    have := le_max_right (-(1 + ∑ k, α k * R ω k)) 0
    have : (0:ℝ) ≤ min 1 (max (-(1 + ∑ k, α k * R ω k)) 0) := le_min zero_le_one this
    constructor
    · linarith
    · exact min_le_left _ _
  have hφ : Continuous (fun α : Fin d → ℝ =>
      ∫ ω, min 1 (max (-(1 + ∑ k, α k * R ω k)) 0) ∂μ) := by
    refine continuous_of_dominated (bound := fun _ => 1) (fun α => (hmeas α).aestronglyMeasurable)
      (fun α => Filter.Eventually.of_forall (hbd α)) (integrable_const _) ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    fun_prop
  have heq : {α : Fin d → ℝ | ∀ᵐ ω ∂μ, 0 ≤ 1 + ∑ k, α k * R ω k} =
      (fun α : Fin d → ℝ => ∫ ω, min 1 (max (-(1 + ∑ k, α k * R ω k)) 0) ∂μ) ⁻¹' {0} := by
    ext α
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    have hnn : (0 : Ω → ℝ) ≤ fun ω => min 1 (max (-(1 + ∑ k, α k * R ω k)) 0) :=
      fun ω => le_min zero_le_one (le_max_right _ _)
    have hint : Integrable (fun ω => min 1 (max (-(1 + ∑ k, α k * R ω k)) 0)) μ :=
      (integrable_const (1:ℝ)).mono' (hmeas α).aestronglyMeasurable
        (Filter.Eventually.of_forall (hbd α))
    rw [integral_eq_zero_iff_of_nonneg hnn hint]
    constructor
    · intro h
      filter_upwards [h] with ω hω
      exact (tw_minmax_zero _).mpr hω
    · intro h
      filter_upwards [h] with ω hω
      exact (tw_minmax_zero _).mp hω
  rw [heq]
  exact isClosed_singleton.preimage hφ

lemma tw_pbdd (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → Fin d → ℝ)
    (hR : Measurable R) (hNA : NoArbitrageOnePeriod μ R) (C : Submodule ℝ (Fin d → ℝ))
    (hC : Disjoint (twNullSp μ R) C) :
    ∃ ρ : ℝ, ∀ c ∈ C, (∀ᵐ ω ∂μ, 0 ≤ 1 + ∑ k, c k * R ω k) → ‖c‖ ≤ ρ := by
  set S : Set (Fin d → ℝ) := (C : Set (Fin d → ℝ)) ∩ Metric.sphere 0 1 with hS
  have hSc : IsCompact S := (isCompact_sphere 0 1).inter_left (Submodule.closed_of_finiteDimensional C)
  have hnorm : ∀ c ∈ C, c ≠ 0 → ‖c‖⁻¹ • c ∈ S := by
    intro c hc hc0
    refine ⟨C.smul_mem _ hc, ?_⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hc0)]
  rcases S.eq_empty_or_nonempty with hE | hne
  · refine ⟨0, fun c hc _ => ?_⟩
    by_contra h
    have hc0 : c ≠ 0 := by
      intro h0; rw [h0, norm_zero] at h; exact h le_rfl
    have := hnorm c hc hc0
    rw [hE] at this; exact this
  obtain ⟨u0, hu0S, hu0⟩ := hSc.exists_isMinOn hne (tw_phi_cont μ R hR).continuousOn
  set η := ∫ ω, min 1 (max (-(∑ k, u0 k * R ω k)) 0) ∂μ with hη
  have hηpos : 0 < η := by
    apply tw_phi_pos μ R hR hNA u0
    intro hmem
    have : u0 = 0 := (Submodule.disjoint_def.mp hC) u0 hmem hu0S.1
    have h1 := hu0S.2
    rw [this, mem_sphere_zero_iff_norm, norm_zero] at h1
    norm_num at h1
  refine ⟨1 / η, fun c hc hA => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hlt
    have : 0 < 1 / η := div_pos one_pos hηpos
    linarith
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  set u := ‖c‖⁻¹ • c with hu
  have huS := hnorm c hc hc0
  have hφu : η ≤ ∫ ω, min 1 (max (-(∑ k, u k * R ω k)) 0) ∂μ := hu0 huS
  have hsum : ∀ ω, ∑ k, c k * R ω k = ‖c‖ * ∑ k, u k * R ω k := by
    intro ω
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [hu, Pi.smul_apply, smul_eq_mul]
    field_simp
  have hmu := tw_sum_meas R hR u
  have hint : Integrable (fun ω => ‖c‖ * min 1 (max (-(∑ k, u k * R ω k)) 0)) μ := by
    refine (integrable_const ‖c‖).mono' ?_ ?_
    · exact (measurable_const.mul (measurable_const.min (hmu.neg.max measurable_const))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      have hnn : (0:ℝ) ≤ min 1 (max (-(∑ k, u k * R ω k)) 0) := le_min zero_le_one (le_max_right _ _)
      have hle1 : min 1 (max (-(∑ k, u k * R ω k)) 0) ≤ 1 := min_le_left _ _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hcn.le hnn)]
      nlinarith
  have hle : ∫ ω, ‖c‖ * min 1 (max (-(∑ k, u k * R ω k)) 0) ∂μ ≤ ∫ ω, (1:ℝ) ∂μ := by
    refine integral_mono_ae hint (integrable_const _) ?_
    filter_upwards [hA] with ω hω
    rw [hsum ω] at hω
    have h1 : ‖c‖ * min 1 (max (-(∑ k, u k * R ω k)) 0) ≤ ‖c‖ * max (-(∑ k, u k * R ω k)) 0 :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hcn.le
    have h2 : ‖c‖ * max (-(∑ k, u k * R ω k)) 0 ≤ 1 := by
      rcases le_total (-(∑ k, u k * R ω k)) 0 with h | h
      · rw [max_eq_right h]; simp
      · rw [max_eq_left h]
        have : ‖c‖ * -(∑ k, u k * R ω k) = -(‖c‖ * ∑ k, u k * R ω k) := by ring
        linarith
    linarith
  rw [integral_const_mul] at hle
  have hone : ∫ ω, (1:ℝ) ∂μ = 1 := by simp
  rw [hone] at hle
  have : ‖c‖ * η ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hφu hcn.le) hle
  rw [div_lt_iff₀ hηpos] at hlt
  linarith


end PowMin

section PowMulti
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
lemma tw_meas_omega (M : TerminalWealthMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ)) (m : ℕ)
    (hπ : ∀ j, m ≤ j → j < M.N → Measurable (π j)) (y : ℝ) :
    Measurable (fun ω => M.terminalWealth π (M.N - m) m y ω) := by
  let Rmod : Ω → ℕ → Fin d → ℝ := fun ω j => if 1 ≤ j ∧ j ≤ M.N then M.R j ω else 0
  have hRm : Measurable Rmod := by
    refine measurable_pi_lambda _ (fun j => ?_)
    by_cases h : 1 ≤ j ∧ j ≤ M.N
    · simp only [Rmod, if_pos h]; exact M.hR_meas j h.1 h.2
    · simp only [Rmod, if_neg h]; exact measurable_const
  have heq : (fun ω => M.terminalWealth π (M.N - m) m y ω) =
      fun ω => twW M.i π (M.N - m) m y (Rmod ω) := by
    funext ω
    rw [tw_tw_eq]
    apply twW_congr
    intro j h1 h2
    simp only [Rmod, if_pos (show 1 ≤ j ∧ j ≤ M.N by omega)]
  rw [heq]
  exact (twW_meas M.i π (M.N - m) m (fun j h1 h2 => hπ j h1 (by omega))).comp
    (measurable_const.prodMk hRm)

noncomputable def twgneg : ℝ → ENNReal := fun z => if z < 0 then 1 else 0

lemma twgneg_meas : Measurable twgneg :=
  Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const

noncomputable def twgpow (γ : ℝ) : ℝ → ENNReal := fun z => ENNReal.ofReal (max z 0 ^ γ)

lemma twgpow_meas (γ : ℝ) : Measurable (twgpow γ) :=
  ((measurable_id.max measurable_const).pow_const γ).ennreal_ofReal

lemma tw_lint_const (M : TerminalWealthMarket Ω d) (c : ENNReal) :
    ∫⁻ _ω, c ∂M.measIP = c := by
  haveI := M.isProb
  simp

end PowMulti

end MDPFinance.TerminalWealth

open Filter Topology

namespace MDPFinance.TerminalWealth

section LogMin
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- `b - log t` for `t > 0`, `⊤` otherwise. -/
noncomputable def luH (b t : ℝ) : ENNReal := if 0 < t then ENNReal.ofReal (b - Real.log t) else ⊤

lemma luH_cont (b : ℝ) : Continuous (luH b) := by
  rw [continuous_iff_continuousAt]
  intro t
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have e : (fun _ => (⊤ : ENNReal)) =ᶠ[𝓝 t] luH b := by
      filter_upwards [eventually_lt_nhds ht] with s hs
      simp [luH, not_lt.mpr hs.le]
    exact (continuousAt_const).congr e
  · subst ht
    show Tendsto (luH b) (𝓝 0) (𝓝 (luH b 0))
    have h0 : luH b 0 = ⊤ := by simp [luH]
    rw [h0, ← nhdsLE_sup_nhdsGT, tendsto_sup]
    constructor
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp [luH, not_lt.mpr (show s ≤ 0 from hs)]
    · have h1 : Tendsto (fun s => b - Real.log s) (𝓝[>] 0) atTop :=
        tendsto_atTop_add_const_left _ b (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)
      refine (ENNReal.tendsto_ofReal_atTop.comp h1).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp [luH, show (0:ℝ) < s from hs]
  · have e : (fun s => ENNReal.ofReal (b - Real.log s)) =ᶠ[𝓝 t] luH b := by
      filter_upwards [eventually_gt_nhds ht] with s hs
      simp [luH, hs]
    exact (ENNReal.continuous_ofReal.continuousAt.comp
      (continuousAt_const.sub (Real.continuousAt_log ht.ne'))).congr e

lemma luH_meas : Measurable (fun p : ℝ × ℝ => luH p.1 p.2) := by
  unfold luH
  refine Measurable.ite (measurableSet_lt measurable_const measurable_snd) ?_ measurable_const
  exact (measurable_fst.sub (Real.measurable_log.comp measurable_snd)).ennreal_ofReal

lemma lu_log_le (u : ℝ) (hu : 0 < 1 + u) : Real.log (1 + u) ≤ u := by
  have := Real.log_le_sub_one_of_pos hu; linarith

/-- a.s. positivity and integrability give the `luH` integral explicitly. -/
lemma lu_G_eq (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → Fin d → ℝ) (hR : Measurable R)
    (hint : Integrable (fun ω => ∑ k, |R ω k|) μ) (B : ℝ) (c : Fin d → ℝ) (hcB : ‖c‖ ≤ B)
    (hpos : ∀ᵐ ω ∂μ, 0 < 1 + ∑ k, c k * R ω k)
    (hli : Integrable (fun ω => Real.log (1 + ∑ k, c k * R ω k)) μ) :
    ∫⁻ ω, luH (B * ∑ k, |R ω k|) (1 + ∑ k, c k * R ω k) ∂μ =
      ENNReal.ofReal (B * ∫ ω, ∑ k, |R ω k| ∂μ - ∫ ω, Real.log (1 + ∑ k, c k * R ω k) ∂μ) := by
  have hφi : Integrable (fun ω => B * ∑ k, |R ω k| - Real.log (1 + ∑ k, c k * R ω k)) μ :=
    (hint.const_mul B).sub hli
  have hnn : ∀ᵐ ω ∂μ, 0 ≤ B * ∑ k, |R ω k| - Real.log (1 + ∑ k, c k * R ω k) := by
    filter_upwards [hpos] with ω hω
    have h1 := lu_log_le _ hω
    have h2 := tw_dot_bound R c ω
    have h3 : 0 ≤ ∑ k, |R ω k| := Finset.sum_nonneg (fun k _ => abs_nonneg _)
    have h4 : ‖c‖ * ∑ k, |R ω k| ≤ B * ∑ k, |R ω k| := mul_le_mul_of_nonneg_right hcB h3
    have h5 := le_abs_self (∑ k, c k * R ω k)
    linarith
  have e : (fun ω => luH (B * ∑ k, |R ω k|) (1 + ∑ k, c k * R ω k)) =ᵐ[μ]
      fun ω => ENNReal.ofReal (B * ∑ k, |R ω k| - Real.log (1 + ∑ k, c k * R ω k)) := by
    filter_upwards [hpos] with ω hω
    simp [luH, hω]
  rw [lintegral_congr_ae e, ← ofReal_integral_eq_lintegral_ofReal hφi hnn,
    integral_sub (hint.const_mul B) hli, integral_const_mul]

lemma lu_exists (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → Fin d → ℝ)
    (hR : Measurable R) (hNA : NoArbitrageOnePeriod μ R)
    (hint : Integrable (fun ω => ∑ k, |R ω k|) μ) :
    ∃ α0 : Fin d → ℝ, (∀ᵐ ω ∂μ, 0 < 1 + ∑ k, α0 k * R ω k) ∧
      Integrable (fun ω => Real.log (1 + ∑ k, α0 k * R ω k)) μ ∧
      ∀ α : Fin d → ℝ, (∀ᵐ ω ∂μ, 0 < 1 + ∑ k, α k * R ω k) →
        Integrable (fun ω => Real.log (1 + ∑ k, α k * R ω k)) μ →
        ∫ ω, Real.log (1 + ∑ k, α k * R ω k) ∂μ ≤ ∫ ω, Real.log (1 + ∑ k, α0 k * R ω k) ∂μ := by
  obtain ⟨C, hC⟩ := (twNullSp μ R).exists_isCompl
  obtain ⟨ρ, hρ⟩ := tw_pbdd μ R hR hNA C hC.disjoint
  set B := max ρ 0 with hB
  set A := {α : Fin d → ℝ | ∀ᵐ ω ∂μ, 0 ≤ 1 + ∑ k, α k * R ω k} with hAdef
  set K : Set (Fin d → ℝ) := A ∩ ((C : Set (Fin d → ℝ)) ∩ Metric.closedBall 0 B) with hKdef
  have hK : IsCompact K :=
    ((isCompact_closedBall 0 B).inter_left
      (Submodule.closed_of_finiteDimensional C)).inter_left (tw_afrac_closed μ R hR)
  have h0K : (0 : Fin d → ℝ) ∈ K :=
    ⟨(show ∀ᵐ ω ∂μ, 0 ≤ 1 + ∑ k, (0 : Fin d → ℝ) k * R ω k from
      Filter.Eventually.of_forall (fun ω => by simp)), C.zero_mem, by simp [hB]⟩
  set S : Ω → ℝ := fun ω => ∑ k, |R ω k| with hS
  set G : (Fin d → ℝ) → ENNReal := fun c => ∫⁻ ω, luH (B * S ω) (1 + ∑ k, c k * R ω k) ∂μ
    with hG
  have hψm : ∀ c : Fin d → ℝ, Measurable (fun ω => luH (B * S ω) (1 + ∑ k, c k * R ω k)) := by
    intro c
    refine luH_meas.comp (Measurable.prodMk ?_ ?_)
    · exact measurable_const.mul (by simp only [hS]; fun_prop)
    · exact (tw_sum_meas R hR c).const_add 1
  have hψc : ∀ ω, Continuous (fun c : Fin d → ℝ => luH (B * S ω) (1 + ∑ k, c k * R ω k)) :=
    fun ω => (luH_cont _).comp (by fun_prop)
  have hlsc : LowerSemicontinuousOn G K := by
    intro c hc y hy
    haveI : (𝓝[K] c).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (subset_closure hc)
    have hF : G c ≤ liminf G (𝓝[K] c) := by
      calc G c = ∫⁻ ω, liminf (fun c' => luH (B * S ω) (1 + ∑ k, c' k * R ω k)) (𝓝[K] c) ∂μ := by
            simp only [hG]
            congr 1; funext ω
            exact (((hψc ω).tendsto c).mono_left nhdsWithin_le_nhds).liminf_eq.symm
        _ ≤ liminf G (𝓝[K] c) := lintegral_liminf_le hψm
    exact eventually_lt_of_lt_liminf (lt_of_lt_of_le hy hF)
  obtain ⟨c0, hc0K, hc0⟩ := hlsc.exists_isMinOn ⟨0, h0K⟩ hK
  have hG0 : G 0 = ENNReal.ofReal (B * ∫ ω, S ω ∂μ - ∫ ω, Real.log (1 + ∑ k, (0 : Fin d → ℝ) k * R ω k) ∂μ) :=
    lu_G_eq μ R hR hint B 0 (by simp [hB])
      (Filter.Eventually.of_forall (fun ω => by simp)) (by simp)
  have hGc0 : G c0 ≠ ⊤ := by
    have := hc0 h0K
    refine ne_top_of_le_ne_top ?_ this
    rw [hG0]; exact ENNReal.ofReal_ne_top
  have hlt := ae_lt_top (hψm c0) hGc0
  have hpos0 : ∀ᵐ ω ∂μ, 0 < 1 + ∑ k, c0 k * R ω k := by
    filter_upwards [hlt] with ω hω
    by_contra h
    simp [luH, h] at hω
  have hc0B : ‖c0‖ ≤ B := by
    have := hc0K.2.2; rwa [Metric.mem_closedBall, dist_zero_right] at this
  -- integrability of the log at c0
  have hφnn : ∀ᵐ ω ∂μ, 0 ≤ B * S ω - Real.log (1 + ∑ k, c0 k * R ω k) := by
    filter_upwards [hpos0] with ω hω
    have h1 := lu_log_le _ hω
    have h2 := tw_dot_bound R c0 ω
    have h3 : 0 ≤ ∑ k, |R ω k| := Finset.sum_nonneg (fun k _ => abs_nonneg _)
    have h4 : ‖c0‖ * ∑ k, |R ω k| ≤ B * ∑ k, |R ω k| := mul_le_mul_of_nonneg_right hc0B h3
    have h5 := le_abs_self (∑ k, c0 k * R ω k)
    simp only [hS]; linarith
  have hlogm : Measurable (fun ω => Real.log (1 + ∑ k, c0 k * R ω k)) :=
    Real.measurable_log.comp ((tw_sum_meas R hR c0).const_add 1)
  have hφi : Integrable (fun ω => B * S ω - Real.log (1 + ∑ k, c0 k * R ω k)) μ := by
    refine ⟨((measurable_const.mul (by simp only [hS]; fun_prop)).sub hlogm).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have e : (fun ω => ‖B * S ω - Real.log (1 + ∑ k, c0 k * R ω k)‖ₑ) =ᵐ[μ]
        fun ω => luH (B * S ω) (1 + ∑ k, c0 k * R ω k) := by
      filter_upwards [hpos0, hφnn] with ω hω hn
      simp only [luH, if_pos hω]
      rw [Real.enorm_eq_ofReal hn]
    rw [lintegral_congr_ae e]
    exact lt_top_iff_ne_top.mpr hGc0
  have hli0 : Integrable (fun ω => Real.log (1 + ∑ k, c0 k * R ω k)) μ := by
    have := (hint.const_mul B).sub hφi
    refine this.congr (Filter.Eventually.of_forall (fun ω => ?_))
    simp [hS]
  refine ⟨c0, hpos0, hli0, fun α hα hαi => ?_⟩
  have hmem : α ∈ twNullSp μ R ⊔ C := by rw [hC.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨l, hl, c, hc, hlc⟩ := Submodule.mem_sup.mp hmem
  have hae : ∀ᵐ ω ∂μ, ∑ k, α k * R ω k = ∑ k, c k * R ω k := by
    filter_upwards [hl] with ω hω
    rw [← hlc]
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, hω, zero_add]
  have hcpos : ∀ᵐ ω ∂μ, 0 < 1 + ∑ k, c k * R ω k := by
    filter_upwards [hα, hae] with ω h1 h2
    rw [← h2]; exact h1
  have hcA : c ∈ A := by
    show ∀ᵐ ω ∂μ, _
    filter_upwards [hcpos] with ω h1 using h1.le
  have hcB : ‖c‖ ≤ B := (hρ c hc hcA).trans (le_max_left _ _)
  have hcK : c ∈ K := ⟨hcA, hc, by rw [Metric.mem_closedBall, dist_zero_right]; exact hcB⟩
  have hFeq : ∫ ω, Real.log (1 + ∑ k, α k * R ω k) ∂μ = ∫ ω, Real.log (1 + ∑ k, c k * R ω k) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hae] with ω h
    rw [h]
  have hci : Integrable (fun ω => Real.log (1 + ∑ k, c k * R ω k)) μ := by
    refine hαi.congr ?_
    filter_upwards [hae] with ω h
    rw [h]
  have hle := hc0 hcK
  simp only [Set.mem_setOf_eq] at hle
  have e1 : G c = _ := lu_G_eq μ R hR hint B c hcB hcpos hci
  have e2 : G c0 = _ := lu_G_eq μ R hR hint B c0 hc0B hpos0 hli0
  rw [e1, e2] at hle
  have hnn2 : 0 ≤ B * ∫ ω, S ω ∂μ - ∫ ω, Real.log (1 + ∑ k, c k * R ω k) ∂μ := by
    have h1 : ∫ ω, Real.log (1 + ∑ k, c k * R ω k) ∂μ ≤ ∫ ω, B * S ω ∂μ := by
      refine integral_mono_ae hci (hint.const_mul B) ?_
      filter_upwards [hcpos] with ω hω
      have h1 := lu_log_le _ hω
      have h2 := tw_dot_bound R c ω
      have h3 : 0 ≤ ∑ k, |R ω k| := Finset.sum_nonneg (fun k _ => abs_nonneg _)
      have h4 : ‖c‖ * ∑ k, |R ω k| ≤ B * ∑ k, |R ω k| := mul_le_mul_of_nonneg_right hcB h3
      have h5 := le_abs_self (∑ k, c k * R ω k)
      simp only [hS]; linarith
    rw [integral_const_mul] at h1
    linarith
  rw [ENNReal.ofReal_le_ofReal_iff hnn2] at hle
  rw [hFeq]; linarith

end LogMin

end MDPFinance.TerminalWealth

open Filter Topology

namespace MDPFinance.TerminalWealth

section LogStep
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

lemma lu_coe_fin (x : ENNReal) (hx : x ≠ ⊤) : (x : EReal) = ((x.toReal : ℝ) : EReal) := by
  lift x to NNReal using hx
  rfl

lemma lu_toENNReal_neg (t : ℝ) : (((-(t:EReal)) ⊔ 0).toENNReal) = ENNReal.ofReal (-t) := by
  rw [← EReal.coe_neg]
  rcases le_total (-t) 0 with h | h
  · rw [sup_eq_right.mpr (by exact_mod_cast h), EReal.toENNReal_zero, ENNReal.ofReal_of_nonpos h]
  · rw [sup_eq_left.mpr (by exact_mod_cast h), EReal.toENNReal_of_ne_top (EReal.coe_ne_top _),
      EReal.toReal_coe]

/-- `ofReal w - ofReal (-w) = w`, in the form of an inequality transfer. -/
lemma lu_ofReal_cmp (P Q : ENNReal) (hP : P ≠ ⊤) (hQ : Q ≠ ⊤) (w : ℝ)
    (h : P.toReal - Q.toReal ≤ w) : P + ENNReal.ofReal (-w) ≤ Q + ENNReal.ofReal w := by
  rw [← ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨hP, ENNReal.ofReal_ne_top⟩)
    (ENNReal.add_ne_top.mpr ⟨hQ, ENNReal.ofReal_ne_top⟩),
    ENNReal.toReal_add hP ENNReal.ofReal_ne_top, ENNReal.toReal_add hQ ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
  rcases le_total w 0 with hw | hw
  · rw [max_eq_left (by linarith : (0:ℝ) ≤ -w), max_eq_right hw]; linarith
  · rw [max_eq_right (by linarith : -w ≤ 0), max_eq_left hw]; linarith

/-- The EReal conclusion from the ENNReal inequality. -/
lemma lu_ereal (a b : ENNReal) (H : ℝ) (h : a + ENNReal.ofReal (-H) ≤ b + ENNReal.ofReal H) :
    (a : EReal) + -(b : EReal) ≤ (H : EReal) := by
  by_cases hb : b = ⊤
  · subst hb; simp
  have ha : a ≠ ⊤ := by
    intro ha; subst ha
    have : b + ENNReal.ofReal H = ⊤ := top_le_iff.mp (le_trans (by simp) h)
    exact (ENNReal.add_ne_top.mpr ⟨hb, ENNReal.ofReal_ne_top⟩) this
  rw [lu_coe_fin a ha, lu_coe_fin b hb, ← EReal.coe_neg, ← EReal.coe_add, EReal.coe_le_coe_iff]
  rw [← ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨ha, ENNReal.ofReal_ne_top⟩)
    (ENNReal.add_ne_top.mpr ⟨hb, ENNReal.ofReal_ne_top⟩),
    ENNReal.toReal_add ha ENNReal.ofReal_ne_top, ENNReal.toReal_add hb ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal', ENNReal.toReal_ofReal'] at h
  rcases le_total H 0 with hw | hw
  · rw [max_eq_left (by linarith : (0:ℝ) ≤ -H), max_eq_right hw] at h; linarith
  · rw [max_eq_right (by linarith : -H ≤ 0), max_eq_left hw] at h; linarith

/-- ENNReal chaining with a possibly infinite middle term. -/
lemma lu_chain (a b c q x p : ENNReal) (h1 : a + x ≤ b + p) (h2 : p + c ≤ x + q) (hp : p ≠ ⊤) :
    a + c ≤ b + q := by
  by_cases hx : x = ⊤
  · have : b + p = ⊤ := top_le_iff.mp (le_trans (by simp [hx]) h1)
    have hb : b = ⊤ := by
      rcases ENNReal.add_eq_top.mp this with h | h
      · exact h
      · exact absurd h hp
    simp [hb]
  · have : a + c + x ≤ b + q + x := by
      calc a + c + x = (a + x) + c := by ring
        _ ≤ (b + p) + c := by gcongr
        _ = b + (p + c) := by ring
        _ ≤ b + (x + q) := by gcongr
        _ = b + q + x := by ring
    exact (ENNReal.add_le_add_iff_right hx).mp this

/-- One period: `E[c + log(1+α·R)] ≤ c + v` in ENNReal form, plus finiteness of the positive
part. -/
lemma lu_step (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → Fin d → ℝ) (hR : Measurable R)
    (hint : Integrable (fun ω => ∑ k, |R ω k|) μ) (v : ℝ)
    (hv : ∀ α : Fin d → ℝ, (∀ᵐ ω ∂μ, 0 < 1 + ∑ k, α k * R ω k) →
      Integrable (fun ω => Real.log (1 + ∑ k, α k * R ω k)) μ →
      ∫ ω, Real.log (1 + ∑ k, α k * R ω k) ∂μ ≤ v)
    (α : Fin d → ℝ) (hα : ∀ᵐ ω ∂μ, 0 < 1 + ∑ k, α k * R ω k) (c : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (c + Real.log (1 + ∑ k, α k * R ω k)) ∂μ) ≠ ⊤ ∧
    ∫⁻ ω, ENNReal.ofReal (c + Real.log (1 + ∑ k, α k * R ω k)) ∂μ + ENNReal.ofReal (-(c + v)) ≤
      ∫⁻ ω, ENNReal.ofReal (-(c + Real.log (1 + ∑ k, α k * R ω k))) ∂μ + ENNReal.ofReal (c + v) := by
  set f : Ω → ℝ := fun ω => c + Real.log (1 + ∑ k, α k * R ω k) with hf
  have hfm : Measurable f :=
    measurable_const.add (Real.measurable_log.comp ((tw_sum_meas R hR α).const_add 1))
  -- positive part bound
  have hbd : Integrable (fun ω => |c| + ‖α‖ * ∑ k, |R ω k|) μ :=
    (integrable_const _).add (hint.const_mul _)
  have hPle : ∀ᵐ ω ∂μ, ENNReal.ofReal (f ω) ≤ ENNReal.ofReal (|c| + ‖α‖ * ∑ k, |R ω k|) := by
    filter_upwards [hα] with ω hω
    apply ENNReal.ofReal_le_ofReal
    have h1 := lu_log_le _ hω
    have h2 := tw_dot_bound R α ω
    have h5 := le_abs_self (∑ k, α k * R ω k)
    have h6 := le_abs_self c
    simp only [hf]; linarith
  have hPfin : ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae hPle)
    rw [← ofReal_integral_eq_lintegral_ofReal hbd
      (Filter.Eventually.of_forall (fun ω => add_nonneg (abs_nonneg _)
        (mul_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun k _ => abs_nonneg _)))))]
    exact ENNReal.ofReal_ne_top
  refine ⟨hPfin, ?_⟩
  by_cases hli : Integrable (fun ω => Real.log (1 + ∑ k, α k * R ω k)) μ
  · have hfi : Integrable f μ := (integrable_const c).add hli
    have hQfin : ∫⁻ ω, ENNReal.ofReal (-f ω) ∂μ ≠ ⊤ := by
      have := hfi.neg.lintegral_lt_top
      exact this.ne
    apply lu_ofReal_cmp _ _ hPfin hQfin
    rw [← integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi]
    simp only [hf]
    rw [integral_add (integrable_const c) hli]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    linarith [hv α hα hli]
  · have hQ : ∫⁻ ω, ENNReal.ofReal (-f ω) ∂μ = ⊤ := by
      by_contra hQ
      apply hli
      have hfi : Integrable f μ := by
        refine ⟨hfm.aestronglyMeasurable, ?_⟩
        unfold HasFiniteIntegral
        have e : (fun ω => ‖f ω‖ₑ) = fun ω => ENNReal.ofReal (f ω) + ENNReal.ofReal (-f ω) := by
          funext ω
          rw [Real.enorm_eq_ofReal_abs]
          rcases le_total 0 (f ω) with h | h
          · rw [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (by linarith : -f ω ≤ 0), add_zero]
          · rw [abs_of_nonpos h, ENNReal.ofReal_of_nonpos h, zero_add]
        rw [e, lintegral_add_left hfm.ennreal_ofReal]
        exact lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mpr ⟨hPfin, hQ⟩)
      have := hfi.sub (integrable_const c)
      refine this.congr (Filter.Eventually.of_forall (fun ω => ?_))
      simp [hf]
    rw [hQ]; simp

/-- `vLog` as a maximum. -/
lemma lu_vLog {Ω : Type*} [MeasurableSpace Ω] (M : TerminalWealthMarket Ω d) (n : ℕ)
    (α0 : Fin d → ℝ) (hα0 : ∀ᵐ ω ∂M.measIP, 0 < 1 + ∑ k, α0 k * M.R (n + 1) ω k)
    (hmax : ∀ α : Fin d → ℝ, (∀ᵐ ω ∂M.measIP, 0 < 1 + ∑ k, α k * M.R (n + 1) ω k) →
      Integrable (fun ω => Real.log (1 + ∑ k, α k * M.R (n + 1) ω k)) M.measIP →
      ∫ ω, Real.log (1 + ∑ k, α k * M.R (n + 1) ω k) ∂M.measIP ≤
        ∫ ω, Real.log (1 + ∑ k, α0 k * M.R (n + 1) ω k) ∂M.measIP) :
    M.vLog n = ∫ ω, Real.log (1 + ∑ k, α0 k * M.R (n + 1) ω k) ∂M.measIP := by
  haveI := M.isProb
  set F : (Fin d → ℝ) → ℝ := fun α => ∫ ω, Real.log (1 + ∑ k, α k * M.R (n + 1) ω k) ∂M.measIP
  have h0 : (0 : Fin d → ℝ) ∈ M.AfracLog n := by
    show ∀ᵐ ω ∂M.measIP, _
    exact Filter.Eventually.of_forall (fun ω => by simp)
  have hF0 : F 0 = 0 := by simp [F]
  have hnn : 0 ≤ F α0 := by
    rw [← hF0]
    exact hmax 0 h0 (by simp)
  have hle : ∀ α, (⨆ (_ : α ∈ M.AfracLog n), F α) ≤ F α0 := by
    intro α
    refine Real.iSup_le (fun hα => ?_) hnn
    by_cases hi : Integrable (fun ω => Real.log (1 + ∑ k, α k * M.R (n + 1) ω k)) M.measIP
    · exact hmax α hα hi
    · show ∫ ω, _ ∂M.measIP ≤ _
      rw [integral_undef hi]; exact hnn
  have hbdd : BddAbove (Set.range fun α => ⨆ (_ : α ∈ M.AfracLog n), F α) := by
    refine ⟨F α0, ?_⟩
    rintro _ ⟨α, rfl⟩
    exact hle α
  unfold TerminalWealthMarket.vLog
  apply le_antisymm
  · exact Real.iSup_le hle hnn
  · refine le_ciSup_of_le hbdd α0 ?_
    rw [ciSup_pos (show α0 ∈ M.AfracLog n from hα0)]

end LogStep

end MDPFinance.TerminalWealth

open Filter Topology

namespace MDPFinance.TerminalWealth

section LogMulti
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

noncomputable def lugp : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.log z)
noncomputable def lugm : ℝ → ENNReal := fun z => ENNReal.ofReal (-Real.log z)
noncomputable def lugle : ℝ → ENNReal := fun z => if z ≤ 0 then 1 else 0

lemma lugp_meas : Measurable lugp := Real.measurable_log.ennreal_ofReal
lemma lugm_meas : Measurable lugm := Real.measurable_log.neg.ennreal_ofReal
lemma lugle_meas : Measurable lugle :=
  Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const measurable_const

noncomputable def luD (M : TerminalWealthMarket Ω d) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico m M.N, (Real.log (1 + M.i (k + 1)) + M.vLog k)

lemma luD_succ (M : TerminalWealthMarket Ω d) (m : ℕ) (hm : m < M.N) :
    luD M m = (Real.log (1 + M.i (m + 1)) + M.vLog m) + luD M (m + 1) := by
  unfold luD; rw [Finset.sum_eq_sum_Ico_succ_bot hm]

lemma luD_N (M : TerminalWealthMarket Ω d) : luD M M.N = 0 := by
  unfold luD; simp

lemma twG_N (M : TerminalWealthMarket Ω d) (g : ℝ → ENNReal) (π : ℕ → ℝ → (Fin d → ℝ)) (y : ℝ) :
    twG M g π M.N y = g y := by
  unfold twG
  rw [Nat.sub_self]
  exact tw_lint_const M (g y)

lemma lu_pos_G (M : TerminalWealthMarket Ω d) (hdomU : M.domU = Set.Ioi 0)
    (π : ℕ → ℝ → (Fin d → ℝ)) (n : ℕ) (hπ : M.IsAdmissible n π) :
    ∀ t m, m + t = M.N → n ≤ m → ∀ y, 0 < y → twG M lugle π m y = 0 := by
  intro t
  induction t with
  | zero =>
    intro m hm _ y hy
    simp only [add_zero] at hm
    subst hm
    rw [twG_N]
    simp [lugle, not_le.mpr hy]
  | succ t ih =>
    intro m hm hnm y hy
    have hmN : m < M.N := by omega
    rw [twG_decomp M lugle lugle_meas π m hmN (fun j h1 h2 => (hπ j (by omega) h2).2) y]
    have hD := (hπ m hnm hmN).1 y (by rw [hdomU]; exact hy)
    have : (fun ω => twG M lugle π (m + 1)
        ((1 + M.i (m + 1)) * (y + ∑ j, π m y j * M.R (m + 1) ω j))) =ᵐ[M.measIP] fun _ => 0 := by
      filter_upwards [hD] with ω hω
      rw [hdomU] at hω
      exact ih (m + 1) (by omega) (by omega) _ hω
    rw [lintegral_congr_ae this]
    simp

lemma lu_pos (M : TerminalWealthMarket Ω d) (hdomU : M.domU = Set.Ioi 0)
    (π : ℕ → ℝ → (Fin d → ℝ)) (n : ℕ) (hn : n ≤ M.N) (hπ : M.IsAdmissible n π) (y : ℝ)
    (hy : 0 < y) : ∀ᵐ ω ∂M.measIP, 0 < M.terminalWealth π (M.N - n) n y ω := by
  have h0 := lu_pos_G M hdomU π n hπ (M.N - n) n (by omega) le_rfl y hy
  unfold twG at h0
  have h1 := (lintegral_eq_zero_iff (lugle_meas.comp
    (tw_meas_omega M π n (fun j h1 h2 => (hπ j h1 h2).2) y))).mp h0
  filter_upwards [h1] with ω hω
  simp only [Function.comp_apply, Pi.zero_apply, lugle] at hω
  by_contra h
  push_neg at h
  rw [if_pos h] at hω
  exact one_ne_zero hω

lemma lu_upper (M : TerminalWealthMarket Ω d) (hdomU : M.domU = Set.Ioi 0) (hFM2 : M.FM2)
    (hv : ∀ k, k < M.N → ∀ α : Fin d → ℝ,
      (∀ᵐ ω ∂M.measIP, 0 < 1 + ∑ j, α j * M.R (k + 1) ω j) →
      Integrable (fun ω => Real.log (1 + ∑ j, α j * M.R (k + 1) ω j)) M.measIP →
      ∫ ω, Real.log (1 + ∑ j, α j * M.R (k + 1) ω j) ∂M.measIP ≤ M.vLog k)
    (π : ℕ → ℝ → (Fin d → ℝ)) (n : ℕ) (hπ : M.IsAdmissible n π) :
    ∀ t m, m + t = M.N → n ≤ m → ∀ y, 0 < y →
      twG M lugp π m y + ENNReal.ofReal (-(Real.log y + luD M m)) ≤
        twG M lugm π m y + ENNReal.ofReal (Real.log y + luD M m) := by
  haveI := M.isProb
  intro t
  induction t with
  | zero =>
    intro m hm _ y hy
    simp only [add_zero] at hm
    subst hm
    rw [twG_N, twG_N, luD_N, add_zero]
    simp only [lugp, lugm]
    rw [add_comm]
  | succ t ih =>
    intro m hm hnm y hy
    have hmN : m < M.N := by omega
    have hπm : ∀ j, m ≤ j → j < M.N → Measurable (π j) := fun j h1 h2 => (hπ j (by omega) h2).2
    rw [twG_decomp M lugp lugp_meas π m hmN hπm y, twG_decomp M lugm lugm_meas π m hmN hπm y]
    have hD := (hπ m hnm hmN).1 y (by rw [hdomU]; exact hy)
    have hip := M.hi_pos (m + 1) (by omega) (by omega)
    set Y1 : Ω → ℝ := fun ω => (1 + M.i (m + 1)) * (y + ∑ j, π m y j * M.R (m + 1) ω j) with hY1
    set h : ℝ → ℝ := fun z => Real.log z + luD M (m + 1) with hh
    have hY1m : Measurable Y1 :=
      measurable_const.mul (measurable_const.add
        (tw_sum_meas _ (M.hR_meas (m + 1) (by omega) (by omega)) _))
    have hm1 : Measurable (fun ω => ENNReal.ofReal (-h (Y1 ω))) :=
      ((Real.measurable_log.comp hY1m).add_const _).neg.ennreal_ofReal
    have hm2 : Measurable (fun ω => ENNReal.ofReal (h (Y1 ω))) :=
      ((Real.measurable_log.comp hY1m).add_const _).ennreal_ofReal
    have h1 : ∫⁻ ω, twG M lugp π (m + 1) (Y1 ω) ∂M.measIP + ∫⁻ ω, ENNReal.ofReal (-h (Y1 ω)) ∂M.measIP ≤
        ∫⁻ ω, twG M lugm π (m + 1) (Y1 ω) ∂M.measIP + ∫⁻ ω, ENNReal.ofReal (h (Y1 ω)) ∂M.measIP := by
      rw [← lintegral_add_right _ hm1, ← lintegral_add_right _ hm2]
      refine lintegral_mono_ae ?_
      filter_upwards [hD] with ω hω
      rw [hdomU] at hω
      exact ih (m + 1) (by omega) (by omega) _ hω
    -- one-period step
    set α : Fin d → ℝ := fun k => y⁻¹ * π m y k with hα
    have hpt : ∀ ω, Y1 ω = (1 + M.i (m + 1)) * (y * (1 + ∑ j, α j * M.R (m + 1) ω j)) := by
      intro ω
      simp only [hY1]
      congr 1
      rw [mul_add, mul_one, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [hα]
      field_simp
    have hαA : ∀ᵐ ω ∂M.measIP, 0 < 1 + ∑ j, α j * M.R (m + 1) ω j := by
      filter_upwards [hD] with ω hω
      rw [hdomU, Set.mem_Ioi] at hω
      have : 0 < (1 + M.i (m + 1)) * (y * (1 + ∑ j, α j * M.R (m + 1) ω j)) := by
        rw [← hpt ω]; exact hω
      exact pos_of_mul_pos_right (pos_of_mul_pos_right this hip.le) hy.le
    set c : ℝ := Real.log (1 + M.i (m + 1)) + Real.log y + luD M (m + 1) with hc
    have hlog : ∀ᵐ ω ∂M.measIP, h (Y1 ω) = c + Real.log (1 + ∑ j, α j * M.R (m + 1) ω j) := by
      filter_upwards [hαA] with ω hω
      simp only [hh, hc]
      rw [hpt ω, Real.log_mul hip.ne' (mul_pos hy hω).ne', Real.log_mul hy.ne' hω.ne']
      ring
    obtain ⟨hfin, hstep⟩ := lu_step M.measIP (M.R (m + 1)) (M.hR_meas _ (by omega) (by omega))
      (hFM2 _ (by omega) (by omega)) (M.vLog m) (hv m hmN) α hαA c
    have e2 : ∫⁻ ω, ENNReal.ofReal (h (Y1 ω)) ∂M.measIP =
        ∫⁻ ω, ENNReal.ofReal (c + Real.log (1 + ∑ j, α j * M.R (m + 1) ω j)) ∂M.measIP := by
      refine lintegral_congr_ae ?_
      filter_upwards [hlog] with ω hω; rw [hω]
    have e1 : ∫⁻ ω, ENNReal.ofReal (-h (Y1 ω)) ∂M.measIP =
        ∫⁻ ω, ENNReal.ofReal (-(c + Real.log (1 + ∑ j, α j * M.R (m + 1) ω j))) ∂M.measIP := by
      refine lintegral_congr_ae ?_
      filter_upwards [hlog] with ω hω; rw [hω]
    have hH : Real.log y + luD M m = c + M.vLog m := by
      rw [luD_succ M m hmN, hc]; ring
    rw [hH]
    rw [← e1, ← e2] at hstep
    rw [← e2] at hfin
    exact lu_chain _ _ _ _ _ _ h1 hstep hfin

/-- The value of a policy in terms of the two lintegrals. -/
lemma lu_Vpi (M : TerminalWealthMarket Ω d) (hdomU : M.domU = Set.Ioi 0)
    (hU : ∀ x > (0 : ℝ), M.U x = Real.log x) (π : ℕ → ℝ → (Fin d → ℝ)) (n : ℕ)
    (hn : n ≤ M.N) (hπ : M.IsAdmissible n π) (x : ℝ) (hx : 0 < x) :
    M.Vpi π n x = ((twG M lugp π n x : ENNReal) : EReal) + -((twG M lugm π n x : ENNReal) : EReal) := by
  have hpos := lu_pos M hdomU π n hn hπ x hx
  unfold TerminalWealthMarket.Vpi erealIntegral twG
  have e1 : (fun ω => ((M.U (M.terminalWealth π (M.N - n) n x ω) : EReal) ⊔ 0).toENNReal)
      =ᵐ[M.measIP] fun ω => lugp (M.terminalWealth π (M.N - n) n x ω) := by
    filter_upwards [hpos] with ω h
    rw [tw_toENNReal, hU _ h]
    rfl
  have e2 : (fun ω => (-(M.U (M.terminalWealth π (M.N - n) n x ω) : EReal) ⊔ 0).toENNReal)
      =ᵐ[M.measIP] fun ω => lugm (M.terminalWealth π (M.N - n) n x ω) := by
    filter_upwards [hpos] with ω h
    rw [lu_toENNReal_neg, hU _ h]
    rfl
  rw [lintegral_congr_ae e1, lintegral_congr_ae e2]

end LogMulti

end MDPFinance.TerminalWealth

open Filter Topology

namespace MDPFinance.TerminalWealth

section LogCore
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

lemma lu_prod (M : TerminalWealthMarket Ω d) (αs : ℕ → Fin d → ℝ) (ω : Ω) :
    ∀ k n x, M.terminalWealth (fun k x j => αs k j * x) k n x ω =
      x * ∏ j ∈ Finset.range k,
        ((1 + M.i (n + j + 1)) * (1 + ∑ l, αs (n + j) l * M.R (n + j + 1) ω l)) := by
  intro k
  induction k with
  | zero => intro n x; simp [TerminalWealthMarket.terminalWealth]
  | succ k ih =>
    intro n x
    rw [TerminalWealthMarket.terminalWealth, ih, Finset.prod_range_succ']
    have e : x + ∑ j, αs n j * x * M.R (n + 1) ω j = x * (1 + ∑ l, αs n l * M.R (n + 1) ω l) := by
      rw [mul_add, mul_one, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [e]
    have e2 : ∏ j ∈ Finset.range k, ((1 + M.i (n + 1 + j + 1)) *
        (1 + ∑ l, αs (n + 1 + j) l * M.R (n + 1 + j + 1) ω l)) =
        ∏ j ∈ Finset.range k, ((1 + M.i (n + (j + 1) + 1)) *
        (1 + ∑ l, αs (n + (j + 1)) l * M.R (n + (j + 1) + 1) ω l)) :=
      Finset.prod_congr rfl (fun j _ => by rw [show n + 1 + j = n + (j + 1) by omega])
    rw [e2]
    simp only [add_zero]
    ring

lemma lu_ereal_int (μ : Measure Ω) (f : Ω → ℝ) (hf : Integrable f μ) :
    ((∫⁻ ω, ENNReal.ofReal (f ω) ∂μ : ENNReal) : EReal) + -((∫⁻ ω, ENNReal.ofReal (-f ω) ∂μ : ENNReal) : EReal) =
      ((∫ ω, f ω ∂μ : ℝ) : EReal) := by
  have hP : ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ ≠ ⊤ := hf.lintegral_lt_top.ne
  have hQ : ∫⁻ ω, ENNReal.ofReal (-f ω) ∂μ ≠ ⊤ := hf.neg.lintegral_lt_top.ne
  rw [lu_coe_fin _ hP, lu_coe_fin _ hQ, ← EReal.coe_neg, ← EReal.coe_add,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  rfl

theorem log_core (M : TerminalWealthMarket Ω d) (hFM2 : M.FM2) (hdomU : M.domU = Set.Ioi (0 : ℝ))
    (hU : ∀ x > (0 : ℝ), M.U x = Real.log x) :
    (∀ n ≤ M.N, ∀ x > (0 : ℝ),
        M.V n x = ((Real.log x +
          ∑ k ∈ Finset.Ico n M.N, (Real.log (1 + M.i (k + 1)) + M.vLog k) : ℝ) : EReal)) ∧
      (∃ αstar : ℕ → (Fin d → ℝ), (∀ n < M.N, αstar n ∈ M.AfracLog n ∧
          ∫ ω, Real.log (1 + ∑ k, αstar n k * M.R (n + 1) ω k) ∂M.measIP = M.vLog n) ∧
        ∃ fstar : ℕ → ℝ → (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
          (∀ n < M.N, ∀ x > (0 : ℝ), fstar n x = fun k => αstar n k * x) ∧
          ∀ x > (0 : ℝ), M.Vpi fstar 0 x = M.V 0 x) := by
  haveI := M.isProb
  have hex : ∀ n, n < M.N → ∃ α0 : Fin d → ℝ,
      (∀ᵐ ω ∂M.measIP, 0 < 1 + ∑ k, α0 k * M.R (n + 1) ω k) ∧
      Integrable (fun ω => Real.log (1 + ∑ k, α0 k * M.R (n + 1) ω k)) M.measIP ∧
      ∀ α : Fin d → ℝ, (∀ᵐ ω ∂M.measIP, 0 < 1 + ∑ k, α k * M.R (n + 1) ω k) →
        Integrable (fun ω => Real.log (1 + ∑ k, α k * M.R (n + 1) ω k)) M.measIP →
        ∫ ω, Real.log (1 + ∑ k, α k * M.R (n + 1) ω k) ∂M.measIP ≤
          ∫ ω, Real.log (1 + ∑ k, α0 k * M.R (n + 1) ω k) ∂M.measIP := fun n hn =>
    lu_exists M.measIP (M.R (n + 1)) (M.hR_meas _ (by omega) (by omega))
      (M.hNA _ (by omega) (by omega)) (hFM2 _ (by omega) (by omega))
  choose! αs hαsA hαsI hαsmax using hex
  have hvL : ∀ n, n < M.N → M.vLog n =
      ∫ ω, Real.log (1 + ∑ k, αs n k * M.R (n + 1) ω k) ∂M.measIP :=
    fun n hn => lu_vLog M n (αs n) (hαsA n hn) (hαsmax n hn)
  have hv : ∀ k, k < M.N → ∀ α : Fin d → ℝ,
      (∀ᵐ ω ∂M.measIP, 0 < 1 + ∑ j, α j * M.R (k + 1) ω j) →
      Integrable (fun ω => Real.log (1 + ∑ j, α j * M.R (k + 1) ω j)) M.measIP →
      ∫ ω, Real.log (1 + ∑ j, α j * M.R (k + 1) ω j) ∂M.measIP ≤ M.vLog k := by
    intro k hk α hα hi
    rw [hvL k hk]; exact hαsmax k hk α hα hi
  set fstar : ℕ → ℝ → (Fin d → ℝ) := fun k x j => αs k j * x with hfstar
  have hadm : ∀ n, M.IsAdmissible n fstar := by
    intro n k _ hk
    refine ⟨fun x hx => ?_, (measurable_pi_lambda _ (fun j => measurable_const.mul measurable_id) :
        Measurable (fun x : ℝ => fun j => αs k j * x))⟩
    rw [hdomU, Set.mem_Ioi] at hx
    show ∀ᵐ ω ∂M.measIP, _ ∈ M.domU
    rw [hdomU]
    filter_upwards [hαsA k hk] with ω hω
    rw [Set.mem_Ioi]
    have hip := M.hi_pos (k + 1) (by omega) (by omega)
    have e : x + ∑ j, fstar k x j * M.R (k + 1) ω j = x * (1 + ∑ j, αs k j * M.R (k + 1) ω j) := by
      rw [mul_add, mul_one, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => by simp only [hfstar]; ring)
    rw [e]
    exact mul_pos hip (mul_pos hx hω)
  -- exact value of fstar
  have hfs : ∀ n ≤ M.N, ∀ x, 0 < x →
      M.Vpi fstar n x = ((Real.log x + luD M n : ℝ) : EReal) := by
    intro n hn x hx
    rw [lu_Vpi M hdomU hU fstar n hn (hadm n) x hx]
    unfold twG
    set F : ℕ → Ω → ℝ := fun j ω =>
      (1 + M.i (n + j + 1)) * (1 + ∑ l, αs (n + j) l * M.R (n + j + 1) ω l) with hF
    have hW : ∀ ω, M.terminalWealth fstar (M.N - n) n x ω = x * ∏ j ∈ Finset.range (M.N - n), F j ω :=
      fun ω => lu_prod M αs ω (M.N - n) n x
    have hFpos : ∀ᵐ ω ∂M.measIP, ∀ j ∈ Finset.range (M.N - n), 0 < F j ω := by
      rw [Filter.eventually_all_finset]
      intro j hj
      have hj' : n + j < M.N := by simp at hj; omega
      filter_upwards [hαsA (n + j) hj'] with ω hω
      exact mul_pos (M.hi_pos (n + j + 1) (by omega) (by omega)) hω
    set f : Ω → ℝ := fun ω => Real.log x + ∑ j ∈ Finset.range (M.N - n),
      (Real.log (1 + M.i (n + j + 1)) + Real.log (1 + ∑ l, αs (n + j) l * M.R (n + j + 1) ω l))
      with hf
    have hlogW : ∀ᵐ ω ∂M.measIP, Real.log (M.terminalWealth fstar (M.N - n) n x ω) = f ω := by
      filter_upwards [hFpos] with ω hω
      rw [hW, Real.log_mul hx.ne' (Finset.prod_pos hω).ne',
        Real.log_prod (fun j hj => (hω j hj).ne')]
      simp only [hf]
      congr 1
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hj' : n + j < M.N := by simp at hj; omega
      have hip := M.hi_pos (n + j + 1) (by omega) (by omega)
      have h2 : 0 < 1 + ∑ l, αs (n + j) l * M.R (n + j + 1) ω l := by
        have := hω j hj
        simp only [hF] at this
        exact pos_of_mul_pos_right this hip.le
      simp only [hF]
      rw [Real.log_mul hip.ne' h2.ne']
    have hfi : Integrable f M.measIP := by
      refine (integrable_const _).add (integrable_finset_sum _ (fun j hj => ?_))
      have hj' : n + j < M.N := by simp at hj; omega
      exact (integrable_const _).add (hαsI (n + j) hj')
    have e1 : (fun ω => lugp (M.terminalWealth fstar (M.N - n) n x ω)) =ᵐ[M.measIP]
        fun ω => ENNReal.ofReal (f ω) := by
      filter_upwards [hlogW] with ω h; simp only [lugp, h]
    have e2 : (fun ω => lugm (M.terminalWealth fstar (M.N - n) n x ω)) =ᵐ[M.measIP]
        fun ω => ENNReal.ofReal (-f ω) := by
      filter_upwards [hlogW] with ω h; simp only [lugm, h]
    rw [lintegral_congr_ae e1, lintegral_congr_ae e2, lu_ereal_int M.measIP f hfi]
    congr 1
    simp only [hf]
    rw [integral_add (integrable_const _) (integrable_finset_sum _ (fun j hj => by
      have hj' : n + j < M.N := by simp at hj; omega
      exact (integrable_const _).add (hαsI (n + j) hj'))),
      integral_finset_sum _ (fun j hj => by
      have hj' : n + j < M.N := by simp at hj; omega
      exact (integrable_const _).add (hαsI (n + j) hj'))]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    congr 1
    unfold luD
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' : n + j < M.N := by simp at hj; omega
    rw [integral_add (integrable_const _) (hαsI (n + j) hj'), hvL (n + j) hj']
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hV : ∀ n ≤ M.N, ∀ x, 0 < x → M.V n x = ((Real.log x + luD M n : ℝ) : EReal) := by
    intro n hn x hx
    apply le_antisymm
    · unfold TerminalWealthMarket.V
      refine iSup₂_le (fun π hπ => ?_)
      rw [lu_Vpi M hdomU hU π n hn hπ x hx]
      exact lu_ereal _ _ _ (lu_upper M hdomU hFM2 hv π n hπ (M.N - n) n (by omega) le_rfl x hx)
    · unfold TerminalWealthMarket.V
      rw [← hfs n hn x hx]
      exact le_iSup₂ (f := fun π (_ : π ∈ {π | M.IsAdmissible n π}) => M.Vpi π n x) fstar (hadm n)
  refine ⟨fun n hn x hx => hV n hn x hx, αs,
    fun n hn => ⟨hαsA n hn, (hvL n hn).symm⟩, fstar, hadm 0, fun n _ x _ => rfl,
    fun x hx => by rw [hV 0 (Nat.zero_le _) x hx, hfs 0 (Nat.zero_le _) x hx]⟩

end LogCore

end MDPFinance.TerminalWealth

open MDPFinance.TerminalWealth

theorem solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : TerminalWealthMarket Ω d) (hFM2 : M.FM2) (hdomU : M.domU = Set.Ioi (0 : ℝ))
    (hU : ∀ x > (0 : ℝ), M.U x = Real.log x) :
    (∀ n ≤ M.N, ∀ x > (0 : ℝ),
        M.V n x = ((Real.log x +
          ∑ k ∈ Finset.Ico n M.N, (Real.log (1 + M.i (k + 1)) + M.vLog k) : ℝ) : EReal)) ∧
      (∃ αstar : ℕ → (Fin d → ℝ), (∀ n < M.N, αstar n ∈ M.AfracLog n ∧
          ∫ ω, Real.log (1 + ∑ k, αstar n k * M.R (n + 1) ω k) ∂M.measIP = M.vLog n) ∧
        ∃ fstar : ℕ → ℝ → (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
          (∀ n < M.N, ∀ x > (0 : ℝ), fstar n x = fun k => αstar n k * x) ∧
          ∀ x > (0 : ℝ), M.Vpi fstar 0 x = M.V 0 x) :=
  log_core M hFM2 hdomU hU
