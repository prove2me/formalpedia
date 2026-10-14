-- Prove2me | solution 1 for MDPFinance.TerminalWealth.power_utility_solution
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T04:10:12.161402+00:00
-- url     : https://prove2.me/submissions/a1605e73-add3-4409-bc2e-0008a047c721

import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_Market
import Definitions.Def_MDPFinance_TerminalWealth_PowerAuxiliary

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

lemma tw_rpow_bound (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (t : ℝ) : |t ^ γ| ≤ 1 + |t| := by
  refine (Real.abs_rpow_le_abs_rpow t γ).trans ?_
  rcases le_total |t| 1 with h | h
  · have := Real.rpow_le_one (abs_nonneg t) h hγ0.le
    linarith [abs_nonneg t]
  · have := Real.rpow_le_rpow_of_exponent_le h hγ1.le
    rw [Real.rpow_one] at this; linarith

lemma tw_F_meas (R : Ω → Fin d → ℝ) (hR : Measurable R) (γ : ℝ) (α : Fin d → ℝ) :
    Measurable (fun ω => (1 + ∑ k, α k * R ω k) ^ γ) :=
  ((tw_sum_meas R hR α).const_add 1).pow_const γ

lemma tw_F_bound (R : Ω → Fin d → ℝ) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (α : Fin d → ℝ)
    (ω : Ω) : ‖(1 + ∑ k, α k * R ω k) ^ γ‖ ≤ 2 + ‖α‖ * ∑ k, |R ω k| := by
  rw [Real.norm_eq_abs]
  have h1 := tw_rpow_bound γ hγ0 hγ1 (1 + ∑ k, α k * R ω k)
  have h2 := tw_dot_bound R α ω
  have h3 : |1 + ∑ k, α k * R ω k| ≤ 1 + |∑ k, α k * R ω k| := by
    have := abs_add_le (1:ℝ) (∑ k, α k * R ω k); simpa using this
  linarith

lemma tw_F_int (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → Fin d → ℝ) (hR : Measurable R)
    (hint : Integrable (fun ω => ∑ k, |R ω k|) μ) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (α : Fin d → ℝ) : Integrable (fun ω => (1 + ∑ k, α k * R ω k) ^ γ) μ := by
  refine ((integrable_const (2:ℝ)).add (hint.const_mul ‖α‖)).mono'
    (tw_F_meas R hR γ α).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun ω => ?_)
  simp only [Pi.add_apply]
  exact tw_F_bound R γ hγ0 hγ1 α ω

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

lemma tw_pow_exists (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → Fin d → ℝ)
    (hR : Measurable R) (hNA : NoArbitrageOnePeriod μ R)
    (hint : Integrable (fun ω => ∑ k, |R ω k|) μ) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ α0 : Fin d → ℝ, (∀ᵐ ω ∂μ, 0 ≤ 1 + ∑ k, α0 k * R ω k) ∧
      ∀ α : Fin d → ℝ, (∀ᵐ ω ∂μ, 0 ≤ 1 + ∑ k, α k * R ω k) →
        ∫ ω, (1 + ∑ k, α k * R ω k) ^ γ ∂μ ≤ ∫ ω, (1 + ∑ k, α0 k * R ω k) ^ γ ∂μ := by
  obtain ⟨C, hC⟩ := (twNullSp μ R).exists_isCompl
  obtain ⟨ρ, hρ⟩ := tw_pbdd μ R hR hNA C hC.disjoint
  set A := {α : Fin d → ℝ | ∀ᵐ ω ∂μ, 0 ≤ 1 + ∑ k, α k * R ω k} with hAdef
  set K : Set (Fin d → ℝ) := A ∩ ((C : Set (Fin d → ℝ)) ∩ Metric.closedBall 0 (max ρ 0)) with hKdef
  have hK : IsCompact K :=
    ((isCompact_closedBall 0 (max ρ 0)).inter_left
      (Submodule.closed_of_finiteDimensional C)).inter_left (tw_afrac_closed μ R hR)
  have h0K : (0 : Fin d → ℝ) ∈ K :=
    ⟨(show ∀ᵐ ω ∂μ, 0 ≤ 1 + ∑ k, (0 : Fin d → ℝ) k * R ω k from
      Filter.Eventually.of_forall (fun ω => by simp)), C.zero_mem, by simp⟩
  have hcont : ContinuousOn (fun α : Fin d → ℝ => ∫ ω, (1 + ∑ k, α k * R ω k) ^ γ ∂μ) K := by
    refine continuousOn_of_dominated (bound := fun ω => 2 + max ρ 0 * ∑ k, |R ω k|)
      (fun α _ => (tw_F_meas R hR γ α).aestronglyMeasurable) ?_
      ((integrable_const _).add (hint.const_mul _)) ?_
    · intro α hα
      refine Filter.Eventually.of_forall (fun ω => ?_)
      have h1 := tw_F_bound R γ hγ0 hγ1 α ω
      have h2 : ‖α‖ ≤ max ρ 0 := by
        have := hα.2.2; rwa [Metric.mem_closedBall, dist_zero_right] at this
      have h3 : 0 ≤ ∑ k, |R ω k| := Finset.sum_nonneg (fun k _ => abs_nonneg _)
      nlinarith
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      exact ((Real.continuous_rpow_const hγ0.le).comp (by fun_prop)).continuousOn
  obtain ⟨α0, hα0K, hα0⟩ := hK.exists_isMaxOn ⟨0, h0K⟩ hcont
  refine ⟨α0, hα0K.1, fun α hα => ?_⟩
  have hmem : α ∈ twNullSp μ R ⊔ C := by rw [hC.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨l, hl, c, hc, hlc⟩ := Submodule.mem_sup.mp hmem
  have hae : ∀ᵐ ω ∂μ, ∑ k, α k * R ω k = ∑ k, c k * R ω k := by
    filter_upwards [hl] with ω hω
    rw [← hlc]
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, hω, zero_add]
  have hcA : c ∈ A := by
    show ∀ᵐ ω ∂μ, _
    filter_upwards [hα, hae] with ω h1 h2
    rw [← h2]; exact h1
  have hcK : c ∈ K := ⟨hcA, hc, by
    rw [Metric.mem_closedBall, dist_zero_right]; exact (hρ c hc hcA).trans (le_max_left _ _)⟩
  have hFeq : ∫ ω, (1 + ∑ k, α k * R ω k) ^ γ ∂μ = ∫ ω, (1 + ∑ k, c k * R ω k) ^ γ ∂μ := by
    apply integral_congr_ae
    filter_upwards [hae] with ω h
    rw [h]
  rw [hFeq]
  exact hα0 hcK

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

lemma tw_pow_nonneg_G (M : TerminalWealthMarket Ω d) (hdomU : M.domU = Set.Ici 0)
    (π : ℕ → ℝ → (Fin d → ℝ)) (n : ℕ) (hπ : M.IsAdmissible n π) :
    ∀ t m, m + t = M.N → n ≤ m → ∀ y, 0 ≤ y → twG M twgneg π m y = 0 := by
  intro t
  induction t with
  | zero =>
    intro m hm _ y hy
    simp only [add_zero] at hm
    subst hm
    unfold twG
    rw [Nat.sub_self]
    have e : ∀ ω, twgneg (M.terminalWealth π 0 M.N y ω) = 0 := fun ω => by
      show twgneg y = 0
      simp [twgneg, not_lt.mpr hy]
    simp_rw [e]
    simp
  | succ t ih =>
    intro m hm hnm y hy
    have hmN : m < M.N := by omega
    rw [twG_decomp M twgneg twgneg_meas π m hmN (fun j h1 h2 => (hπ j (by omega) h2).2) y]
    have hD := (hπ m hnm hmN).1 y (by rw [hdomU]; exact hy)
    have : (fun ω => twG M twgneg π (m + 1)
        ((1 + M.i (m + 1)) * (y + ∑ j, π m y j * M.R (m + 1) ω j))) =ᵐ[M.measIP] fun _ => 0 := by
      filter_upwards [hD] with ω hω
      rw [hdomU] at hω
      exact ih (m + 1) (by omega) (by omega) _ hω
    rw [lintegral_congr_ae this]
    simp

lemma tw_pow_nonneg (M : TerminalWealthMarket Ω d) (hdomU : M.domU = Set.Ici 0)
    (π : ℕ → ℝ → (Fin d → ℝ)) (n : ℕ) (hn : n ≤ M.N) (hπ : M.IsAdmissible n π) (y : ℝ)
    (hy : 0 ≤ y) : ∀ᵐ ω ∂M.measIP, 0 ≤ M.terminalWealth π (M.N - n) n y ω := by
  have h0 := tw_pow_nonneg_G M hdomU π n hπ (M.N - n) n (by omega) le_rfl y hy
  unfold twG at h0
  have h1 := (lintegral_eq_zero_iff (twgneg_meas.comp
    (tw_meas_omega M π n (fun j h1 h2 => (hπ j h1 h2).2) y))).mp h0
  filter_upwards [h1] with ω hω
  simp only [Function.comp_apply, Pi.zero_apply, twgneg] at hω
  by_contra h
  push_neg at h
  rw [if_pos h] at hω
  exact one_ne_zero hω

lemma tw_pow_step (μ : Measure Ω) [IsProbabilityMeasure μ] (R1 : Ω → Fin d → ℝ)
    (hR1 : Measurable R1) (hint : Integrable (fun ω => ∑ k, |R1 ω k|) μ) (γ : ℝ) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (ip : ℝ) (hip : 0 < ip) (y : ℝ) (hy : 0 ≤ y) (α : Fin d → ℝ)
    (hα : ∀ᵐ ω ∂μ, 0 ≤ 1 + ∑ k, α k * R1 ω k) (C' : ℝ) (hC' : 0 ≤ C') :
    ∫⁻ ω, ENNReal.ofReal (C' * (ip * (y * (1 + ∑ k, α k * R1 ω k))) ^ γ) ∂μ =
      ENNReal.ofReal (C' * ip ^ γ * y ^ γ * ∫ ω, (1 + ∑ k, α k * R1 ω k) ^ γ ∂μ) := by
  have hA : 0 ≤ C' * ip ^ γ * y ^ γ :=
    mul_nonneg (mul_nonneg hC' (Real.rpow_nonneg hip.le _)) (Real.rpow_nonneg hy _)
  have e : (fun ω => ENNReal.ofReal (C' * (ip * (y * (1 + ∑ k, α k * R1 ω k))) ^ γ)) =ᵐ[μ]
      fun ω => ENNReal.ofReal (C' * ip ^ γ * y ^ γ) *
        ENNReal.ofReal ((1 + ∑ k, α k * R1 ω k) ^ γ) := by
    filter_upwards [hα] with ω hω
    rw [← ENNReal.ofReal_mul hA, Real.mul_rpow hip.le (mul_nonneg hy hω),
      Real.mul_rpow hy hω]
    congr 1; ring
  rw [lintegral_congr_ae e, lintegral_const_mul _ (tw_F_meas R1 hR1 γ α).ennreal_ofReal,
    ← ofReal_integral_eq_lintegral_ofReal (tw_F_int μ R1 hR1 hint γ hγ0 hγ1 α)
      (by filter_upwards [hα] with ω hω; exact Real.rpow_nonneg hω _),
    ← ENNReal.ofReal_mul hA]

end PowMulti

section PowFinal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

noncomputable def twCpow (M : TerminalWealthMarket Ω d) (γ : ℝ) (m : ℕ) : ℝ :=
  ∏ k ∈ Finset.Ico m M.N, ((1 + M.i (k + 1)) ^ γ * M.vPower γ k)

lemma twCpow_nonneg (M : TerminalWealthMarket Ω d) (γ : ℝ)
    (hvge : ∀ k, k < M.N → 1 ≤ M.vPower γ k) (m : ℕ) : 0 ≤ twCpow M γ m := by
  unfold twCpow
  refine Finset.prod_nonneg (fun k hk => ?_)
  rw [Finset.mem_Ico] at hk
  have := hvge k hk.2
  exact mul_nonneg (Real.rpow_nonneg (M.hi_pos (k + 1) (by omega) (by omega)).le _) (by linarith)

lemma twCpow_succ (M : TerminalWealthMarket Ω d) (γ : ℝ) (m : ℕ) (hm : m < M.N) :
    twCpow M γ m = ((1 + M.i (m + 1)) ^ γ * M.vPower γ m) * twCpow M γ (m + 1) := by
  unfold twCpow; rw [Finset.prod_eq_prod_Ico_succ_bot hm]

lemma twCpow_N (M : TerminalWealthMarket Ω d) (γ : ℝ) : twCpow M γ M.N = 1 := by
  unfold twCpow; simp

lemma twG_pow_N (M : TerminalWealthMarket Ω d) (γ : ℝ) (π : ℕ → ℝ → (Fin d → ℝ)) (y : ℝ)
    (hy : 0 ≤ y) : twG M (twgpow γ) π M.N y = ENNReal.ofReal (twCpow M γ M.N * y ^ γ) := by
  unfold twG
  rw [Nat.sub_self, twCpow_N, one_mul]
  have e : ∀ ω, twgpow γ (M.terminalWealth π 0 M.N y ω) = ENNReal.ofReal (y ^ γ) := fun ω => by
    show twgpow γ y = _
    simp [twgpow, max_eq_left hy]
  simp_rw [e]
  exact tw_lint_const M _

lemma tw_pow_upper (M : TerminalWealthMarket Ω d) (hdomU : M.domU = Set.Ici 0) (hFM2 : M.FM2)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hv : ∀ k, k < M.N → ∀ α ∈ M.Afrac k,
      ∫ ω, (1 + ∑ j, α j * M.R (k + 1) ω j) ^ γ ∂M.measIP ≤ M.vPower γ k)
    (hvge : ∀ k, k < M.N → 1 ≤ M.vPower γ k)
    (π : ℕ → ℝ → (Fin d → ℝ)) (n : ℕ) (hπ : M.IsAdmissible n π) :
    ∀ t m, m + t = M.N → n ≤ m → ∀ y, 0 ≤ y →
      twG M (twgpow γ) π m y ≤ ENNReal.ofReal (twCpow M γ m * y ^ γ) := by
  haveI := M.isProb
  intro t
  induction t with
  | zero =>
    intro m hm _ y hy
    simp only [add_zero] at hm
    subst hm
    rw [twG_pow_N M γ π y hy]
  | succ t ih =>
    intro m hm hnm y hy
    have hmN : m < M.N := by omega
    rw [twG_decomp M (twgpow γ) (twgpow_meas γ) π m hmN (fun j h1 h2 => (hπ j (by omega) h2).2) y]
    have hD := (hπ m hnm hmN).1 y (by rw [hdomU]; exact hy)
    have hip := M.hi_pos (m + 1) (by omega) (by omega)
    have hC' := twCpow_nonneg M γ hvge (m + 1)
    have h1 : ∫⁻ ω, twG M (twgpow γ) π (m + 1)
        ((1 + M.i (m + 1)) * (y + ∑ j, π m y j * M.R (m + 1) ω j)) ∂M.measIP ≤
        ∫⁻ ω, ENNReal.ofReal (twCpow M γ (m + 1) *
          ((1 + M.i (m + 1)) * (y + ∑ j, π m y j * M.R (m + 1) ω j)) ^ γ) ∂M.measIP := by
      refine lintegral_mono_ae ?_
      filter_upwards [hD] with ω hω
      rw [hdomU] at hω
      exact ih (m + 1) (by omega) (by omega) _ hω
    refine h1.trans ?_
    rcases hy.eq_or_lt with h0 | hpos
    · subst h0
      have hge : ∀ᵐ ω ∂M.measIP, 0 ≤ ∑ j, π m 0 j * M.R (m + 1) ω j := by
        filter_upwards [hD] with ω hω
        rw [hdomU, Set.mem_Ici, zero_add] at hω
        by_contra hneg
        push_neg at hneg
        have := mul_neg_of_pos_of_neg hip hneg
        linarith
      have hpos0 : M.measIP {ω | 0 < ∑ j, π m 0 j * M.R (m + 1) ω j} = 0 := by
        by_contra hp
        exact M.hNA (m + 1) (by omega) (by omega) ⟨π m 0, hge, pos_iff_ne_zero.mpr hp⟩
      have hle : ∀ᵐ ω ∂M.measIP, ∑ j, π m 0 j * M.R (m + 1) ω j ≤ 0 := by
        rw [ae_iff]; simpa using hpos0
      have hz : (fun ω => ENNReal.ofReal (twCpow M γ (m + 1) *
          ((1 + M.i (m + 1)) * (0 + ∑ j, π m 0 j * M.R (m + 1) ω j)) ^ γ)) =ᵐ[M.measIP]
          fun _ => 0 := by
        filter_upwards [hge, hle] with ω h1 h2
        have : ∑ j, π m 0 j * M.R (m + 1) ω j = 0 := le_antisymm h2 h1
        rw [this, add_zero, mul_zero, Real.zero_rpow hγ0.ne', mul_zero, ENNReal.ofReal_zero]
      rw [lintegral_congr_ae hz]
      simp
    · set α : Fin d → ℝ := fun k => y⁻¹ * π m y k with hα
      have hpt : ∀ ω, (1 + M.i (m + 1)) * (y + ∑ j, π m y j * M.R (m + 1) ω j) =
          (1 + M.i (m + 1)) * (y * (1 + ∑ j, α j * M.R (m + 1) ω j)) := by
        intro ω
        congr 1
        rw [mul_add, mul_one, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl (fun k _ => ?_)
        simp only [hα]
        field_simp
      have hαA : α ∈ M.Afrac m := by
        show ∀ᵐ ω ∂M.measIP, _
        filter_upwards [hD] with ω hω
        rw [hdomU, Set.mem_Ici, hpt ω] at hω
        by_contra hneg
        push_neg at hneg
        have := mul_neg_of_pos_of_neg (mul_pos hip hpos) hneg
        nlinarith
      have e : ∫⁻ ω, ENNReal.ofReal (twCpow M γ (m + 1) *
          ((1 + M.i (m + 1)) * (y + ∑ j, π m y j * M.R (m + 1) ω j)) ^ γ) ∂M.measIP =
          ∫⁻ ω, ENNReal.ofReal (twCpow M γ (m + 1) *
          ((1 + M.i (m + 1)) * (y * (1 + ∑ j, α j * M.R (m + 1) ω j))) ^ γ) ∂M.measIP := by
        congr 1; funext ω; rw [hpt ω]
      rw [e, tw_pow_step M.measIP (M.R (m + 1)) (M.hR_meas _ (by omega) (by omega))
        (hFM2 _ (by omega) (by omega)) γ hγ0 hγ1 _ hip y hy α hαA _ hC']
      apply ENNReal.ofReal_le_ofReal
      have hF := hv m hmN α hαA
      have hA : 0 ≤ twCpow M γ (m + 1) * (1 + M.i (m + 1)) ^ γ * y ^ γ :=
        mul_nonneg (mul_nonneg hC' (Real.rpow_nonneg hip.le _)) (Real.rpow_nonneg hy _)
      rw [twCpow_succ M γ m hmN]
      calc twCpow M γ (m + 1) * (1 + M.i (m + 1)) ^ γ * y ^ γ *
            ∫ ω, (1 + ∑ j, α j * M.R (m + 1) ω j) ^ γ ∂M.measIP
          ≤ twCpow M γ (m + 1) * (1 + M.i (m + 1)) ^ γ * y ^ γ * M.vPower γ m :=
            mul_le_mul_of_nonneg_left hF hA
        _ = _ := by ring

lemma tw_pow_eq (M : TerminalWealthMarket Ω d) (hFM2 : M.FM2)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hvge : ∀ k, k < M.N → 1 ≤ M.vPower γ k)
    (αs : ℕ → Fin d → ℝ)
    (hαs : ∀ k, k < M.N → αs k ∈ M.Afrac k ∧
      ∫ ω, (1 + ∑ j, αs k j * M.R (k + 1) ω j) ^ γ ∂M.measIP = M.vPower γ k) :
    ∀ t m, m + t = M.N → ∀ y, 0 ≤ y →
      twG M (twgpow γ) (fun k x j => αs k j * x) m y =
        ENNReal.ofReal (twCpow M γ m * y ^ γ) := by
  haveI := M.isProb
  intro t
  induction t with
  | zero =>
    intro m hm y hy
    simp only [add_zero] at hm
    subst hm
    rw [twG_pow_N M γ _ y hy]
  | succ t ih =>
    intro m hm y hy
    have hmN : m < M.N := by omega
    rw [twG_decomp M (twgpow γ) (twgpow_meas γ) (fun k x j => αs k j * x) m hmN
      (fun j _ _ => (measurable_pi_lambda _ (fun k => measurable_const.mul measurable_id) :
        Measurable (fun x : ℝ => fun k => αs j k * x))) y]
    have hip := M.hi_pos (m + 1) (by omega) (by omega)
    have hC' := twCpow_nonneg M γ hvge (m + 1)
    have hA := (hαs m hmN).1
    have e : (fun ω => twG M (twgpow γ) (fun k x j => αs k j * x) (m + 1)
        ((1 + M.i (m + 1)) * (y + ∑ j, (fun k x j => αs k j * x) m y j * M.R (m + 1) ω j))) =ᵐ[M.measIP]
        fun ω => ENNReal.ofReal (twCpow M γ (m + 1) *
          ((1 + M.i (m + 1)) * (y * (1 + ∑ j, αs m j * M.R (m + 1) ω j))) ^ γ) := by
      filter_upwards [hA] with ω hω
      have hpt : (1 + M.i (m + 1)) * (y + ∑ j, (fun k x j => αs k j * x) m y j * M.R (m + 1) ω j) =
          (1 + M.i (m + 1)) * (y * (1 + ∑ j, αs m j * M.R (m + 1) ω j)) := by
        congr 1
        rw [mul_add, mul_one, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl (fun k _ => ?_)
        ring
      rw [hpt]
      exact ih (m + 1) (by omega) _ (mul_nonneg hip.le (mul_nonneg hy hω))
    rw [lintegral_congr_ae e, tw_pow_step M.measIP (M.R (m + 1)) (M.hR_meas _ (by omega) (by omega))
        (hFM2 _ (by omega) (by omega)) γ hγ0 hγ1 _ hip y hy (αs m) hA _ hC', (hαs m hmN).2,
      twCpow_succ M γ m hmN]
    congr 1
    ring

lemma tw_pow_Vpi (M : TerminalWealthMarket Ω d) (hdomU : M.domU = Set.Ici 0) (γ : ℝ)
    (hγ0 : 0 < γ) (hU : ∀ x ≥ (0 : ℝ), M.U x = x ^ γ / γ) (π : ℕ → ℝ → (Fin d → ℝ)) (n : ℕ)
    (hn : n ≤ M.N) (hπ : M.IsAdmissible n π) (x : ℝ) (hx : 0 ≤ x) :
    M.Vpi π n x = ((ENNReal.ofReal γ⁻¹ * twG M (twgpow γ) π n x : ENNReal) : EReal) := by
  have hnn := tw_pow_nonneg M hdomU π n hn hπ x hx
  unfold TerminalWealthMarket.Vpi erealIntegral twG
  have e1 : (fun ω => ((M.U (M.terminalWealth π (M.N - n) n x ω) : EReal) ⊔ 0).toENNReal)
      =ᵐ[M.measIP] fun ω => ENNReal.ofReal γ⁻¹ *
        twgpow γ (M.terminalWealth π (M.N - n) n x ω) := by
    filter_upwards [hnn] with ω h
    rw [tw_toENNReal, hU _ h]
    simp only [twgpow, max_eq_left h]
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hγ0.le), div_eq_inv_mul]
  have e2 : (fun ω => (-(M.U (M.terminalWealth π (M.N - n) n x ω) : EReal) ⊔ 0).toENNReal)
      =ᵐ[M.measIP] fun _ => 0 := by
    filter_upwards [hnn] with ω h
    rw [← EReal.coe_neg, tw_toENNReal, hU _ h]
    apply ENNReal.ofReal_of_nonpos
    exact neg_nonpos.mpr (div_nonneg (Real.rpow_nonneg h _) hγ0.le)
  rw [lintegral_congr_ae e1, lintegral_congr_ae e2, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp

end PowFinal

section PowCore
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

theorem pow_core (M : TerminalWealthMarket Ω d) (hFM2 : M.FM2) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hdomU : M.domU = Set.Ici (0 : ℝ)) (hU : ∀ x ≥ (0 : ℝ), M.U x = x ^ γ / γ) :
    (∀ n ≤ M.N, ∀ x ≥ (0 : ℝ),
        M.V n x = ((((1 / γ) * ∏ k ∈ Finset.Ico n M.N, ((1 + M.i (k + 1)) ^ γ * M.vPower γ k)) *
          x ^ γ : ℝ) : EReal)) ∧
      (∃ αstar : ℕ → (Fin d → ℝ), (∀ n < M.N, αstar n ∈ M.Afrac n ∧
          ∫ ω, (1 + ∑ k, αstar n k * M.R (n + 1) ω k) ^ γ ∂M.measIP = M.vPower γ n) ∧
        ∃ fstar : ℕ → ℝ → (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
          (∀ n < M.N, ∀ x ≥ (0 : ℝ), fstar n x = fun k => αstar n k * x) ∧
          ∀ x ≥ (0 : ℝ), M.Vpi fstar 0 x = M.V 0 x) := by
  haveI := M.isProb
  have hex : ∀ n, n < M.N → ∃ α0 : Fin d → ℝ, α0 ∈ M.Afrac n ∧ ∀ α ∈ M.Afrac n,
      ∫ ω, (1 + ∑ j, α j * M.R (n + 1) ω j) ^ γ ∂M.measIP ≤
        ∫ ω, (1 + ∑ j, α0 j * M.R (n + 1) ω j) ^ γ ∂M.measIP := fun n hn =>
    tw_pow_exists M.measIP (M.R (n + 1)) (M.hR_meas _ (by omega) (by omega))
      (M.hNA _ (by omega) (by omega)) (hFM2 _ (by omega) (by omega)) γ hγ0 hγ1
  choose! αs hαsA hαsmax using hex
  have h0A : ∀ n, (0 : Fin d → ℝ) ∈ M.Afrac n := fun n =>
    (show ∀ᵐ ω ∂M.measIP, 0 ≤ 1 + ∑ k, (0 : Fin d → ℝ) k * M.R (n + 1) ω k from
      Filter.Eventually.of_forall (fun ω => by simp))
  have hF0 : ∀ n, n < M.N → 1 ≤ ∫ ω, (1 + ∑ j, αs n j * M.R (n + 1) ω j) ^ γ ∂M.measIP := by
    intro n hn
    have := hαsmax n hn 0 (h0A n)
    simpa using this
  have hvP : ∀ n, n < M.N → M.vPower γ n =
      ∫ ω, (1 + ∑ j, αs n j * M.R (n + 1) ω j) ^ γ ∂M.measIP := by
    intro n hn
    have h1 := hF0 n hn
    unfold TerminalWealthMarket.vPower
    apply le_antisymm
    · exact Real.iSup_le (fun α => Real.iSup_le (fun h => hαsmax n hn α h) (by linarith))
        (by linarith)
    · refine le_ciSup_of_le ⟨∫ ω, (1 + ∑ j, αs n j * M.R (n + 1) ω j) ^ γ ∂M.measIP, ?_⟩
        (αs n) ?_
      · rintro _ ⟨α, rfl⟩
        exact Real.iSup_le (fun h => hαsmax n hn α h) (by linarith)
      · rw [ciSup_pos (hαsA n hn)]
  have hv : ∀ k, k < M.N → ∀ α ∈ M.Afrac k,
      ∫ ω, (1 + ∑ j, α j * M.R (k + 1) ω j) ^ γ ∂M.measIP ≤ M.vPower γ k := by
    intro k hk α hα
    rw [hvP k hk]; exact hαsmax k hk α hα
  have hvge : ∀ k, k < M.N → 1 ≤ M.vPower γ k := fun k hk => by rw [hvP k hk]; exact hF0 k hk
  set fstar : ℕ → ℝ → (Fin d → ℝ) := fun k x j => αs k j * x with hfstar
  have hadm : ∀ n, M.IsAdmissible n fstar := by
    intro n k _ hk
    refine ⟨fun x hx => ?_, (measurable_pi_lambda _ (fun j => measurable_const.mul measurable_id) :
        Measurable (fun x : ℝ => fun j => αs k j * x))⟩
    rw [hdomU, Set.mem_Ici] at hx
    show ∀ᵐ ω ∂M.measIP, _ ∈ M.domU
    rw [hdomU]
    filter_upwards [hαsA k hk] with ω hω
    rw [Set.mem_Ici]
    have hip := M.hi_pos (k + 1) (by omega) (by omega)
    have e : x + ∑ j, fstar k x j * M.R (k + 1) ω j = x * (1 + ∑ j, αs k j * M.R (k + 1) ω j) := by
      rw [mul_add, mul_one, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => by simp only [hfstar]; ring)
    rw [e]
    exact mul_nonneg hip.le (mul_nonneg hx hω)
  have hV : ∀ n ≤ M.N, ∀ x, 0 ≤ x →
      M.V n x = ((ENNReal.ofReal γ⁻¹ * ENNReal.ofReal (twCpow M γ n * x ^ γ) : ENNReal) : EReal) ∧
      M.Vpi fstar n x =
        ((ENNReal.ofReal γ⁻¹ * ENNReal.ofReal (twCpow M γ n * x ^ γ) : ENNReal) : EReal) := by
    intro n hn x hx
    have hfs : M.Vpi fstar n x =
        ((ENNReal.ofReal γ⁻¹ * ENNReal.ofReal (twCpow M γ n * x ^ γ) : ENNReal) : EReal) := by
      rw [tw_pow_Vpi M hdomU γ hγ0 hU fstar n hn (hadm n) x hx,
        tw_pow_eq M hFM2 γ hγ0 hγ1 hvge αs (fun k hk => ⟨hαsA k hk, (hvP k hk).symm⟩)
          (M.N - n) n (by omega) x hx]
    refine ⟨le_antisymm ?_ ?_, hfs⟩
    · unfold TerminalWealthMarket.V
      refine iSup₂_le (fun π hπ => ?_)
      rw [tw_pow_Vpi M hdomU γ hγ0 hU π n hn hπ x hx]
      exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr (mul_le_mul' le_rfl
        (tw_pow_upper M hdomU hFM2 γ hγ0 hγ1 hv hvge π n hπ (M.N - n) n (by omega) le_rfl x hx))
    · unfold TerminalWealthMarket.V
      rw [← hfs]
      exact le_iSup₂ (f := fun π (_ : π ∈ {π | M.IsAdmissible n π}) => M.Vpi π n x) fstar (hadm n)
  have hreal : ∀ n x, 0 ≤ x →
      ((ENNReal.ofReal γ⁻¹ * ENNReal.ofReal (twCpow M γ n * x ^ γ) : ENNReal) : EReal) =
      ((((1 / γ) * ∏ k ∈ Finset.Ico n M.N, ((1 + M.i (k + 1)) ^ γ * M.vPower γ k)) *
          x ^ γ : ℝ) : EReal) := by
    intro n x hx
    have hnn : 0 ≤ γ⁻¹ * (twCpow M γ n * x ^ γ) :=
      mul_nonneg (inv_nonneg.mpr hγ0.le)
        (mul_nonneg (twCpow_nonneg M γ hvge n) (Real.rpow_nonneg hx _))
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hγ0.le), EReal.coe_ennreal_ofReal, max_eq_left hnn]
    congr 1
    unfold twCpow
    ring
  refine ⟨fun n hn x hx => by rw [(hV n hn x hx).1, hreal n x hx], αs,
    fun n hn => ⟨hαsA n hn, (hvP n hn).symm⟩, fstar, hadm 0, fun n _ x _ => rfl,
    fun x hx => by rw [(hV 0 (Nat.zero_le _) x hx).1, (hV 0 (Nat.zero_le _) x hx).2]⟩

end PowCore

end MDPFinance.TerminalWealth

open MDPFinance.TerminalWealth


theorem solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : TerminalWealthMarket Ω d) (hFM2 : M.FM2) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hdomU : M.domU = Set.Ici (0 : ℝ)) (hU : ∀ x ≥ (0 : ℝ), M.U x = x ^ γ / γ) :
    (∀ n ≤ M.N, ∀ x ≥ (0 : ℝ),
        M.V n x = ((((1 / γ) * ∏ k ∈ Finset.Ico n M.N, ((1 + M.i (k + 1)) ^ γ * M.vPower γ k)) *
          x ^ γ : ℝ) : EReal)) ∧
      (∃ αstar : ℕ → (Fin d → ℝ), (∀ n < M.N, αstar n ∈ M.Afrac n ∧
          ∫ ω, (1 + ∑ k, αstar n k * M.R (n + 1) ω k) ^ γ ∂M.measIP = M.vPower γ n) ∧
        ∃ fstar : ℕ → ℝ → (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
          (∀ n < M.N, ∀ x ≥ (0 : ℝ), fstar n x = fun k => αstar n k * x) ∧
          ∀ x ≥ (0 : ℝ), M.Vpi fstar 0 x = M.V 0 x) := by
  exact pow_core M hFM2 γ hγ0 hγ1 hdomU hU
