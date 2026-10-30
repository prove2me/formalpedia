-- Prove2me | solution 1 for LyapDiffMC.RandomHorizon.eq_3_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T11:36:12.795019+00:00
-- url     : https://prove2.me/submissions/627080d4-1a02-4eeb-b153-100540505fd4

import Mathlib
import Definitions.Def_MarkovChainKernel
import Definitions.Def_LyapDiffMC_RandomHorizon_Model

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace LyapDiffMC.RandomHorizon.E38

open BanditAlgorithm LyapDiffMC.RandomHorizon

variable {S : Type*} [MeasurableSpace S]

lemma Qpow_succ' (Q : Kernel S S) (n : ℕ) : Qpow Q (n + 1) = Qpow Q n ∘ₖ Q := by
  induction n with
  | zero => simp [Qpow, Kernel.comp_id, Kernel.id_comp]
  | succ n ih =>
    calc Qpow Q (n + 1 + 1) = Q ∘ₖ Qpow Q (n + 1) := rfl
      _ = Q ∘ₖ (Qpow Q n ∘ₖ Q) := by rw [ih]
      _ = (Q ∘ₖ Qpow Q n) ∘ₖ Q := (Kernel.comp_assoc _ _ _).symm
      _ = Qpow Q (n + 1) ∘ₖ Q := rfl

/-- Last-step (Markov) decomposition along the trajectory kernel. -/
lemma last_step (P : Kernel S S) [IsMarkovKernel P] (j : ℕ)
    (F : (Π _i : Iic j, S) → ℝ≥0∞) (hF : Measurable F) (ψ : S → ℝ≥0∞) (hψ : Measurable ψ)
    (x₀ : Π _i : Iic 0, S) :
    ∫⁻ ω : ℕ → S, F (Preorder.frestrictLe j ω) * ψ (ω (j + 1))
        ∂(Kernel.traj (markovChainStep P) 0 x₀)
      = ∫⁻ ω : ℕ → S, F (Preorder.frestrictLe j ω) * ∫⁻ y, ψ y ∂(P (ω j))
        ∂(Kernel.traj (markovChainStep P) 0 x₀) := by
  have hm1 : Measurable fun ω : ℕ → S => F (Preorder.frestrictLe j ω) * ψ (ω (j + 1)) :=
    (hF.comp (Preorder.measurable_frestrictLe j)).mul (hψ.comp (measurable_pi_apply _))
  have hm2 : Measurable fun ω : ℕ → S => F (Preorder.frestrictLe j ω) * ∫⁻ y, ψ y ∂(P (ω j)) :=
    (hF.comp (Preorder.measurable_frestrictLe j)).mul
      ((hψ.lintegral_kernel).comp (measurable_pi_apply _))
  rw [← Kernel.traj_comp_partialTraj (Nat.zero_le j), Kernel.lintegral_comp _ _ _ hm1,
    Kernel.lintegral_comp _ _ _ hm2]
  congr 1
  funext z
  rw [Kernel.lintegral_traj z hm1, Kernel.lintegral_traj z hm2]
  simp only [Preorder.frestrictLe_updateFinset]
  have h1 : ∀ ω : ℕ → S, Function.updateFinset ω (Iic j) z (j + 1) = ω (j + 1) := by
    intro ω
    simp [Function.updateFinset]
  have h2 : ∀ ω : ℕ → S, Function.updateFinset ω (Iic j) z j = z ⟨j, mem_Iic.2 le_rfl⟩ := by
    intro ω
    simp [Function.updateFinset]
  simp only [h1, h2]
  rw [lintegral_const_mul (F z) (f := fun x : ℕ → S => ψ (x (j + 1))) (hψ.comp (measurable_pi_apply _)), lintegral_const, measure_univ,
    mul_one]
  congr 1
  have e := Kernel.map_traj_succ_self (X := fun _ => S) (κ := markovChainStep P) (a := j)
  have : ∫⁻ x : ℕ → S, ψ (x (j + 1)) ∂(Kernel.traj (markovChainStep P) j z)
      = ∫⁻ y, ψ y ∂(((Kernel.traj (markovChainStep P) j).map (fun x : ℕ → S => x (j + 1))) z) := by
    rw [Kernel.map_apply _ (measurable_pi_apply _), lintegral_map hψ (measurable_pi_apply _)]
  rw [this, e]
  rfl

/-- Last-step decomposition for a functional depending only on the coordinates `≤ j`. -/
lemma last_step' (P : Kernel S S) [IsMarkovKernel P] (j : ℕ)
    (H : (ℕ → S) → ℝ≥0∞) (hH : Measurable H)
    (hdep : ∀ ω ω' : ℕ → S, (∀ k ≤ j, ω k = ω' k) → H ω = H ω')
    (ψ : S → ℝ≥0∞) (hψ : Measurable ψ) (x₀ : Π _i : Iic 0, S) :
    ∫⁻ ω : ℕ → S, H ω * ψ (ω (j + 1)) ∂(Kernel.traj (markovChainStep P) 0 x₀)
      = ∫⁻ ω : ℕ → S, H ω * ∫⁻ y, ψ y ∂(P (ω j)) ∂(Kernel.traj (markovChainStep P) 0 x₀) := by
  classical
  let x' : ℕ → S := fun _ => x₀ ⟨0, mem_Iic.2 le_rfl⟩
  let F : (Π _i : Iic j, S) → ℝ≥0∞ := fun z => H (Function.updateFinset x' (Iic j) z)
  have hF : Measurable F := hH.comp measurable_updateFinset
  have hFH : ∀ ω : ℕ → S, F (Preorder.frestrictLe j ω) = H ω := by
    intro ω
    refine hdep _ _ fun k hk => ?_
    simp [Function.updateFinset, hk]
  have := last_step P j F hF ψ hψ x₀
  simp only [hFH] at this
  exact this

/-- Iterating the last-step decomposition: path functionals of product form are kernel powers. -/
lemma iter (P : Kernel S S) [IsMarkovKernel P] (Q : Kernel S S)
    (φ χ : S → ℝ≥0∞) (hφ : Measurable φ) (hχ : Measurable χ)
    (hQ : ∀ y (ψ : S → ℝ≥0∞), Measurable ψ →
      ∫⁻ z, ψ z ∂(Q y) = φ y * ∫⁻ z, χ z * ψ z ∂(P y))
    (x₀ : Π _i : Iic 0, S) :
    ∀ j (ψ : S → ℝ≥0∞), Measurable ψ →
      ∫⁻ ω : ℕ → S, (∏ k ∈ range j, φ (ω k) * χ (ω (k + 1))) * ψ (ω j)
          ∂(Kernel.traj (markovChainStep P) 0 x₀)
        = ∫⁻ z, ψ z ∂(Qpow Q j (x₀ ⟨0, mem_Iic.2 le_rfl⟩)) := by
  intro j
  induction j with
  | zero =>
    intro ψ hψ
    simp only [range_zero, prod_empty, one_mul]
    rw [Kernel.lintegral_traj (f := fun ω : ℕ → S => ψ (ω 0)) x₀
      (hψ.comp (measurable_pi_apply 0))]
    have : ∀ ω : ℕ → S, Function.updateFinset ω (Iic 0) x₀ 0 = x₀ ⟨0, mem_Iic.2 le_rfl⟩ := by
      intro ω; simp [Function.updateFinset]
    simp only [this, lintegral_const, measure_univ, mul_one]
    rw [Qpow, Kernel.id_apply, lintegral_dirac' _ hψ]
  | succ j ih =>
    intro ψ hψ
    have hprod : ∀ ω : ℕ → S, Measurable fun ω : ℕ → S =>
        ∏ k ∈ range j, φ (ω k) * χ (ω (k + 1)) := by
      intro _
      exact Finset.measurable_prod _ fun k _ =>
        (hφ.comp (measurable_pi_apply _)).mul (hχ.comp (measurable_pi_apply _))
    have e1 : ∀ ω : ℕ → S, (∏ k ∈ range (j + 1), φ (ω k) * χ (ω (k + 1))) * ψ (ω (j + 1))
        = ((∏ k ∈ range j, φ (ω k) * χ (ω (k + 1))) * φ (ω j)) * (χ (ω (j + 1)) * ψ (ω (j + 1))) := by
      intro ω; rw [prod_range_succ]; ring
    simp_rw [e1]
    have hdep : ∀ ω ω' : ℕ → S, (∀ k ≤ j, ω k = ω' k) →
        (∏ k ∈ range j, φ (ω k) * χ (ω (k + 1))) * φ (ω j)
          = (∏ k ∈ range j, φ (ω' k) * χ (ω' (k + 1))) * φ (ω' j) := by
      intro ω ω' h
      rw [h j le_rfl]
      congr 1
      refine prod_congr rfl fun k hk => ?_
      have hk' := mem_range.mp hk
      rw [h k (by omega), h (k + 1) (by omega)]
    have key := last_step' P j (fun ω => (∏ k ∈ range j, φ (ω k) * χ (ω (k + 1))) * φ (ω j))
      ((hprod fun _ => x₀ ⟨0, mem_Iic.2 le_rfl⟩).mul (hφ.comp (measurable_pi_apply _))) hdep
      (fun y => χ y * ψ y) (hχ.mul hψ) x₀
    beta_reduce at key
    rw [key]
    have e2 : ∀ ω : ℕ → S, ((∏ k ∈ range j, φ (ω k) * χ (ω (k + 1))) * φ (ω j))
        * ∫⁻ y, χ y * ψ y ∂(P (ω j))
        = (∏ k ∈ range j, φ (ω k) * χ (ω (k + 1))) * (∫⁻ z, ψ z ∂(Q (ω j))) := by
      intro ω; rw [hQ _ ψ hψ]; ring
    simp_rw [e2]
    rw [ih _ hψ.lintegral_kernel, Qpow, Kernel.lintegral_comp _ _ _ hψ]

section model

variable (M : Setting S) (θ : ℝ)

/-- `χ = 1_C`. -/
noncomputable def χC : S → ℝ≥0∞ := M.C.indicator 1

/-- `φ = e^g`. -/
noncomputable def φg : S → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (M.g y))

lemma χC_meas : Measurable (χC M) := measurable_one.indicator M.C_meas

lemma φg_meas : Measurable (φg M) := M.g_meas.exp.ennreal_ofReal

lemma discKernel_apply' (y : S) :
    discKernel M θ y = φg M y • M.P θ y := by
  rw [discKernel, Kernel.withDensity_apply _
    (show Measurable (Function.uncurry fun x (_ : S) => ENNReal.ofReal (Real.exp (M.g x))) from
      (M.g_meas.exp.ennreal_ofReal).comp measurable_fst)]
  exact withDensity_const _

lemma KC_lint (y : S) (ψ : S → ℝ≥0∞) (_hψ : Measurable ψ) :
    ∫⁻ z, ψ z ∂(KC M θ y) = φg M y * ∫⁻ z, χC M z * ψ z ∂(M.P θ y) := by
  rw [KC, Kernel.restrict_apply, discKernel_apply', Measure.restrict_smul, lintegral_smul_measure,
    smul_eq_mul]
  congr 1
  rw [← lintegral_indicator M.C_meas]
  congr 1; funext z
  by_cases hz : z ∈ M.C <;> simp [χC, hz]

lemma disc_compl_lint (y : S) (ψ : S → ℝ≥0∞) :
    ∫⁻ z in M.Cᶜ, ψ z ∂(discKernel M θ y) = φg M y * ∫⁻ z, M.Cᶜ.indicator ψ z ∂(M.P θ y) := by
  rw [discKernel_apply', Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
    lintegral_indicator M.C_meas.compl]

lemma mck_apply (x : S) :
    markovChainKernel (M.P θ) x = Kernel.traj (markovChainStep (M.P θ)) 0 (fun _ => x) := by
  rw [markovChainKernel, Kernel.comap_apply]

lemma ae_zero (x : S) (hx : x ∈ M.C) :
    ∀ᵐ ω : ℕ → S ∂(Kernel.traj (markovChainStep (M.P θ)) 0 (fun _ : Iic 0 => x)), ω 0 ∈ M.C := by
  have hs : MeasurableSet {z : Π _i : Iic 0, S | z ⟨0, mem_Iic.2 le_rfl⟩ ∉ M.C} :=
    (measurable_pi_apply _ M.C_meas).compl
  have e := Kernel.traj_map_frestrictLe (X := fun _ => S) (κ := markovChainStep (M.P θ)) 0 0
  rw [Kernel.partialTraj_self] at e
  have h2 : (Kernel.traj (markovChainStep (M.P θ)) 0 (fun _ : Iic 0 => x))
      ((Preorder.frestrictLe (π := fun _ : ℕ => S) 0) ⁻¹' {z : Π _i : Iic 0, S | z ⟨0, mem_Iic.2 le_rfl⟩ ∉ M.C}) = 0 := by
    rw [← Measure.map_apply (Preorder.measurable_frestrictLe (X := fun _ : ℕ => S) 0) hs,
      ← Kernel.map_apply _ (Preorder.measurable_frestrictLe (X := fun _ : ℕ => S) 0), e, Kernel.id_apply, Measure.dirac_apply' _ hs]
    simp [hx]
  rw [ae_iff]
  exact h2

lemma le_exitTime_iff (m : ℕ) (ω : ℕ → S) :
    (m : ℕ∞) ≤ exitTime M ω ↔ ∀ k < m, ω k ∈ M.C := by
  unfold exitTime
  rw [le_iInf₂_iff]
  constructor
  · intro h k hk
    by_contra hc
    have := h k hc
    exact absurd (Nat.cast_le.mp this) (by omega)
  · intro h n hn
    by_contra hc
    exact hn (h n (by exact_mod_cast not_le.mp hc))

lemma lt_exitTime_iff (j : ℕ) (ω : ℕ → S) :
    (j : ℕ∞) < exitTime M ω ↔ ∀ k ≤ j, ω k ∈ M.C := by
  rw [← ENat.add_one_le_iff (ENat.coe_ne_top j), show (j : ℕ∞) + 1 = ((j + 1 : ℕ) : ℕ∞) by
    push_cast; rfl, le_exitTime_iff]
  exact ⟨fun h k hk => h k (by omega), fun h k hk => h k (by omega)⟩

lemma disc_meas (j : ℕ) : Measurable fun ω : ℕ → S => discReward M ω j := by
  unfold discReward
  exact ((Finset.measurable_sum _ fun k _ => M.g_meas.comp (measurable_pi_apply k)).exp.mul
    (M.f_meas.comp (measurable_pi_apply j))).ennreal_ofReal

lemma disc_eq (hf : ∀ y, 0 ≤ M.f y) (ω : ℕ → S) (j : ℕ) :
    discReward M ω j = (∏ k ∈ range j, φg M (ω k)) * ENNReal.ofReal (M.f (ω j)) := by
  unfold discReward φg
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le, Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]

lemma χC_of_mem {y : S} (hy : y ∈ M.C) : χC M y = 1 := by simp [χC, hy]
lemma χC_of_not_mem {y : S} (hy : y ∉ M.C) : χC M y = 0 := by simp [χC, hy]

lemma a_repr (j : ℕ) (ω : ℕ → S) :
    (if (j : ℕ∞) < exitTime M ω then discReward M ω j else 0)
      = (∏ k ∈ range (j + 1), χC M (ω k)) * discReward M ω j := by
  split_ifs with h0
  · rw [lt_exitTime_iff] at h0
    rw [prod_eq_one, one_mul]
    intro k hk; exact χC_of_mem M (h0 k (by simpa [Nat.lt_succ_iff] using hk))
  · rw [lt_exitTime_iff] at h0
    obtain ⟨i, hi⟩ := not_forall.mp h0
    simp only [_root_.not_imp] at hi
    rw [prod_eq_zero (i := i), zero_mul]
    · simpa [Nat.lt_succ_iff] using hi.1
    · exact χC_of_not_mem M hi.2

open Classical in
lemma b_repr (j : ℕ) (ω : ℕ → S) :
    (if (j : ℕ∞) ≤ exitTime M ω ∧ ω j ∉ M.C then discReward M ω j else 0)
      = (∏ k ∈ range j, χC M (ω k)) * M.Cᶜ.indicator 1 (ω j) * discReward M ω j := by
  split_ifs with h0
  · rw [le_exitTime_iff] at h0
    rw [prod_eq_one (fun k hk => χC_of_mem M (h0.1 k (mem_range.mp hk))), one_mul]
    simp [h0.2]
  · by_cases h : ∀ k < j, ω k ∈ M.C
    · have hj : ω j ∈ M.C := by
        by_contra hj
        exact h0 ⟨(le_exitTime_iff M j ω).2 h, hj⟩
      simp [hj]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      simp only [_root_.not_imp] at hi
      rw [prod_eq_zero (i := i), zero_mul, zero_mul]
      · exact mem_range.mpr hi.1
      · exact χC_of_not_mem M hi.2

lemma a_meas (j : ℕ) : Measurable fun ω : ℕ → S =>
    (if (j : ℕ∞) < exitTime M ω then discReward M ω j else 0) := by
  simp_rw [a_repr]
  exact (Finset.measurable_prod _ fun k _ => (χC_meas M).comp (measurable_pi_apply k)).mul
    (disc_meas M j)

open Classical in
lemma b_meas (j : ℕ) : Measurable fun ω : ℕ → S =>
    (if (j : ℕ∞) ≤ exitTime M ω ∧ ω j ∉ M.C then discReward M ω j else 0) := by
  simp_rw [b_repr]
  exact ((Finset.measurable_prod _ fun k _ => (χC_meas M).comp (measurable_pi_apply k)).mul
    ((measurable_one.indicator M.C_meas.compl).comp (measurable_pi_apply j))).mul (disc_meas M j)

open Classical in
/-- The reward collected at the exit time equals the sum of the `b`-terms. -/
lemma exit_term (ω : ℕ → S) :
    (if exitTime M ω = ⊤ then 0 else discReward M ω (exitTime M ω).toNat)
      = ∑' j : ℕ, (if (j : ℕ∞) ≤ exitTime M ω ∧ ω j ∉ M.C then discReward M ω j else 0) := by
  by_cases hT : exitTime M ω = ⊤
  · rw [if_pos hT]
    symm
    refine ENNReal.tsum_eq_zero.mpr fun j => if_neg ?_
    rintro ⟨_, hj⟩
    exact hj ((le_exitTime_iff M (j + 1) ω).1 (by rw [hT]; exact le_top) j (by omega))
  · rw [if_neg hT]
    set t := (exitTime M ω).toNat with ht
    have htT : (t : ℕ∞) = exitTime M ω := ENat.coe_toNat hT
    have hlt : ∀ k < t, ω k ∈ M.C := (le_exitTime_iff M t ω).1 htT.le
    have hnot : ω t ∉ M.C := by
      intro hc
      have : ((t + 1 : ℕ) : ℕ∞) ≤ exitTime M ω := by
        rw [le_exitTime_iff]
        intro k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
        · exact hlt k hk
        · rw [hk]; exact hc
      rw [← htT] at this
      exact absurd (Nat.cast_le.mp this) (by omega)
    rw [tsum_eq_single t]
    · rw [if_pos ⟨htT.le, hnot⟩]
    · intro j hj
      refine if_neg ?_
      rintro ⟨hjT, hjC⟩
      rcases lt_or_gt_of_ne hj with h | h
      · exact hjC (hlt j h)
      · exact hnot ((le_exitTime_iff M j ω).1 hjT t h)

lemma dep_prod (j : ℕ) (ω ω' : ℕ → S) (h : ∀ k ≤ j, ω k = ω' k) :
    (∏ k ∈ range j, φg M (ω k) * χC M (ω (k + 1))) * φg M (ω j)
      = (∏ k ∈ range j, φg M (ω' k) * χC M (ω' (k + 1))) * φg M (ω' j) := by
  rw [h j le_rfl]
  congr 1
  refine prod_congr rfl fun k hk => ?_
  have hk' := mem_range.mp hk
  rw [h k (by omega), h (k + 1) (by omega)]

lemma prod_meas (j : ℕ) : Measurable fun ω : ℕ → S =>
    (∏ k ∈ range j, φg M (ω k) * χC M (ω (k + 1))) * φg M (ω j) :=
  (Finset.measurable_prod _ fun k _ =>
    ((φg_meas M).comp (measurable_pi_apply _)).mul ((χC_meas M).comp (measurable_pi_apply _))).mul
    ((φg_meas M).comp (measurable_pi_apply _))

lemma A_term (hf : ∀ y, 0 ≤ M.f y) (x : S) (hx : x ∈ M.C) (j : ℕ) :
    ∫⁻ ω, (if (j : ℕ∞) < exitTime M ω then discReward M ω j else 0)
        ∂(markovChainKernel (M.P θ) x)
      = ∫⁻ y, ENNReal.ofReal (M.f y) ∂(kpow M θ j x) := by
  rw [mck_apply]
  have e : ∀ᵐ ω : ℕ → S ∂(Kernel.traj (markovChainStep (M.P θ)) 0 (fun _ : Iic 0 => x)),
      (if (j : ℕ∞) < exitTime M ω then discReward M ω j else 0)
        = (∏ k ∈ range j, φg M (ω k) * χC M (ω (k + 1))) * ENNReal.ofReal (M.f (ω j)) := by
    filter_upwards [ae_zero M θ x hx] with ω h0
    rw [a_repr, disc_eq M hf, prod_range_succ', χC_of_mem M h0, prod_mul_distrib]
    ring
  rw [lintegral_congr_ae e]
  exact iter (M.P θ) (KC M θ) (φg M) (χC M) (φg_meas M) (χC_meas M) (KC_lint M θ) (fun _ => x) j
    _ M.f_meas.ennreal_ofReal

open Classical in
lemma B_term_zero (x : S) (hx : x ∈ M.C) :
    ∫⁻ ω, (if ((0 : ℕ) : ℕ∞) ≤ exitTime M ω ∧ ω 0 ∉ M.C then discReward M ω 0 else 0)
        ∂(markovChainKernel (M.P θ) x) = 0 := by
  rw [mck_apply]
  have e : ∀ᵐ ω : ℕ → S ∂(Kernel.traj (markovChainStep (M.P θ)) 0 (fun _ : Iic 0 => x)),
      (if ((0 : ℕ) : ℕ∞) ≤ exitTime M ω ∧ ω 0 ∉ M.C then discReward M ω 0 else 0) = 0 := by
    filter_upwards [ae_zero M θ x hx] with ω h0
    exact if_neg fun h => h.2 h0
  rw [lintegral_congr_ae e, lintegral_zero]

open Classical in
lemma B_term_succ (hf : ∀ y, 0 ≤ M.f y) (x : S) (hx : x ∈ M.C) (j : ℕ) :
    ∫⁻ ω, (if ((j + 1 : ℕ) : ℕ∞) ≤ exitTime M ω ∧ ω (j + 1) ∉ M.C then discReward M ω (j + 1)
          else 0) ∂(markovChainKernel (M.P θ) x)
      = ∫⁻ y, (∫⁻ z in M.Cᶜ, ENNReal.ofReal (M.f z) ∂(discKernel M θ y)) ∂(kpow M θ j x) := by
  rw [mck_apply]
  set ψc : S → ℝ≥0∞ := M.Cᶜ.indicator (fun y => ENNReal.ofReal (M.f y)) with hψc
  have hψcm : Measurable ψc := M.f_meas.ennreal_ofReal.indicator M.C_meas.compl
  have e : ∀ᵐ ω : ℕ → S ∂(Kernel.traj (markovChainStep (M.P θ)) 0 (fun _ : Iic 0 => x)),
      (if ((j + 1 : ℕ) : ℕ∞) ≤ exitTime M ω ∧ ω (j + 1) ∉ M.C then discReward M ω (j + 1) else 0)
        = ((∏ k ∈ range j, φg M (ω k) * χC M (ω (k + 1))) * φg M (ω j)) * ψc (ω (j + 1)) := by
    filter_upwards [ae_zero M θ x hx] with ω h0
    rw [b_repr, disc_eq M hf, prod_range_succ' (fun k => χC M (ω k)), χC_of_mem M h0,
      prod_range_succ (fun k => φg M (ω k)), prod_mul_distrib]
    have : M.Cᶜ.indicator 1 (ω (j + 1)) * ENNReal.ofReal (M.f (ω (j + 1))) = ψc (ω (j + 1)) := by
      by_cases hc : ω (j + 1) ∈ M.C <;> simp [hψc, hc]
    rw [← this]
    ring
  rw [lintegral_congr_ae e]
  rw [last_step' (M.P θ) j _ (prod_meas M j) (dep_prod M j) ψc hψcm]
  have e2 : ∀ ω : ℕ → S, ((∏ k ∈ range j, φg M (ω k) * χC M (ω (k + 1))) * φg M (ω j))
        * ∫⁻ y, ψc y ∂(M.P θ (ω j))
      = (∏ k ∈ range j, φg M (ω k) * χC M (ω (k + 1)))
        * (φg M (ω j) * ∫⁻ y, ψc y ∂(M.P θ (ω j))) := by
    intro ω; ring
  simp_rw [e2]
  have key := iter (M.P θ) (KC M θ) (φg M) (χC M) (φg_meas M) (χC_meas M) (KC_lint M θ)
    (fun _ => x) j (fun y => φg M y * ∫⁻ z, ψc z ∂(M.P θ y))
    ((φg_meas M).mul hψcm.lintegral_kernel)
  beta_reduce at key
  rw [key]
  congr 1; funext y
  rw [disc_compl_lint]

end model

open Classical in
theorem eq38 (M : Setting S) (θ : ℝ)
    (hf : ∀ y, 0 ≤ M.f y) (x : S) (hx : x ∈ M.C) :
    ∫⁻ ω, pathReward M ω ∂(BanditAlgorithm.markovChainKernel (M.P θ) x)
        = (∑' j : ℕ, ∫⁻ ω, (if (j : ℕ∞) < exitTime M ω then discReward M ω j else 0)
              ∂(BanditAlgorithm.markovChainKernel (M.P θ) x))
          + (∑' j : ℕ, ∫⁻ ω,
              (if (j : ℕ∞) ≤ exitTime M ω ∧ ω j ∉ M.C then discReward M ω j else 0)
              ∂(BanditAlgorithm.markovChainKernel (M.P θ) x)) ∧
    (∑' j : ℕ, ∫⁻ ω, (if (j : ℕ∞) < exitTime M ω then discReward M ω j else 0)
              ∂(BanditAlgorithm.markovChainKernel (M.P θ) x))
          + (∑' j : ℕ, ∫⁻ ω,
              (if (j : ℕ∞) ≤ exitTime M ω ∧ ω j ∉ M.C then discReward M ω j else 0)
              ∂(BanditAlgorithm.markovChainKernel (M.P θ) x))
        = ∫⁻ y, ftildeE M θ y ∂(greenMeasure M θ x) := by
  constructor
  · unfold pathReward
    simp_rw [exit_term M]
    rw [lintegral_add_left (Measurable.ennreal_tsum fun j => a_meas M j),
      lintegral_tsum (fun j => (a_meas M j).aemeasurable),
      lintegral_tsum (fun j => (b_meas M j).aemeasurable)]
  · have hB : (∑' j : ℕ, ∫⁻ ω,
              (if (j : ℕ∞) ≤ exitTime M ω ∧ ω j ∉ M.C then discReward M ω j else 0)
              ∂(BanditAlgorithm.markovChainKernel (M.P θ) x))
          = ∑' j : ℕ, ∫⁻ y, (∫⁻ z in M.Cᶜ, ENNReal.ofReal (M.f z) ∂(discKernel M θ y))
              ∂(kpow M θ j x) := by
      rw [tsum_eq_zero_add' ENNReal.summable, B_term_zero M θ x hx, zero_add]
      simp_rw [B_term_succ M θ hf x hx]
    rw [hB]
    simp_rw [A_term M θ hf x hx]
    rw [← ENNReal.tsum_add]
    simp_rw [← lintegral_add_left M.f_meas.ennreal_ofReal]
    rw [greenMeasure, lintegral_sum_measure]
    rfl


end LyapDiffMC.RandomHorizon.E38

open Classical LyapDiffMC.RandomHorizon in
theorem solution {S : Type*} [MeasurableSpace S] (M : Setting S) (θ : ℝ)
    (hf : ∀ y, 0 ≤ M.f y) (x : S) (hx : x ∈ M.C) :
    ∫⁻ ω, pathReward M ω ∂(BanditAlgorithm.markovChainKernel (M.P θ) x)
        = (∑' j : ℕ, ∫⁻ ω, (if (j : ℕ∞) < exitTime M ω then discReward M ω j else 0)
              ∂(BanditAlgorithm.markovChainKernel (M.P θ) x))
          + (∑' j : ℕ, ∫⁻ ω,
              (if (j : ℕ∞) ≤ exitTime M ω ∧ ω j ∉ M.C then discReward M ω j else 0)
              ∂(BanditAlgorithm.markovChainKernel (M.P θ) x)) ∧
    (∑' j : ℕ, ∫⁻ ω, (if (j : ℕ∞) < exitTime M ω then discReward M ω j else 0)
              ∂(BanditAlgorithm.markovChainKernel (M.P θ) x))
          + (∑' j : ℕ, ∫⁻ ω,
              (if (j : ℕ∞) ≤ exitTime M ω ∧ ω j ∉ M.C then discReward M ω j else 0)
              ∂(BanditAlgorithm.markovChainKernel (M.P θ) x))
        = ∫⁻ y, ftildeE M θ y ∂(greenMeasure M θ x) :=
  LyapDiffMC.RandomHorizon.E38.eq38 M θ hf x hx
