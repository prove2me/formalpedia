-- Prove2me | solution 1 for OAI.Cotype.exists_walshBilinear_half
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:33:09.023018+00:00
-- url     : https://prove2.me/submissions/6d62e73e-15fc-4147-9b85-ce5ba425e0e8

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality

open OAI OAI.Cotype
open scoped BigOperators
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
theorem t_avg {n : ℕ} (f : Cube n → X) (g : Cube n → Y) :
    average (fun u => ‖f u‖ * ‖g u‖) ≤ cubeL2 X f * cubeL2 Y g := by
  simp only [average, cubeL2, smul_eq_mul]
  have hN : (0 : ℝ) ≤ (Fintype.card (Cube n) : ℝ)⁻¹ := by positivity
  rw [Real.sqrt_mul hN, Real.sqrt_mul hN]
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun u => ‖f u‖) (fun u => ‖g u‖)
  calc (Fintype.card (Cube n) : ℝ)⁻¹ * ∑ u, ‖f u‖ * ‖g u‖
      ≤ (Fintype.card (Cube n) : ℝ)⁻¹ * (√(∑ u, ‖f u‖ ^ 2) * √(∑ u, ‖g u‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left h hN
    _ = _ := by
      rw [show √(Fintype.card (Cube n) : ℝ)⁻¹ * √(∑ u, ‖f u‖ ^ 2) * (√(Fintype.card (Cube n) : ℝ)⁻¹ *
        √(∑ u, ‖g u‖ ^ 2)) = (√(Fintype.card (Cube n) : ℝ)⁻¹ * √(Fintype.card (Cube n) : ℝ)⁻¹) *
        (√(∑ u, ‖f u‖ ^ 2) * √(∑ u, ‖g u‖ ^ 2)) by ring, Real.mul_self_sqrt hN]

theorem h50w_cubeL2_le_of_le {n : ℕ} (f : Cube n → Y) (c : ℝ) (hc : 0 ≤ c) (h : ∀ u, ‖f u‖ ≤ c) :
    cubeL2 Y f ≤ c := by
  unfold cubeL2
  rw [Real.sqrt_le_left hc]
  have hN : (Fintype.card (Cube n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [average, smul_eq_mul]
  calc (Fintype.card (Cube n) : ℝ)⁻¹ * ∑ u, ‖f u‖ ^ 2 ≤ (Fintype.card (Cube n) : ℝ)⁻¹ * ∑ _u : Cube n, c ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum fun u _ => pow_le_pow_left₀ (norm_nonneg _) (h u) 2
    _ = c ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

theorem h50w_cubeL2_map {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X) :
    cubeL2 Y (fun u => T (f u)) ≤ ‖T‖ * cubeL2 X f := by
  unfold cubeL2
  rw [← Real.sqrt_sq (norm_nonneg T), ← Real.sqrt_mul (sq_nonneg _)]
  apply Real.sqrt_le_sqrt
  simp only [average, smul_eq_mul]
  rw [mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm _) 2

theorem h50w_opW_bound {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X) :
    cubeL2 Y (operatorWalsh T f) ≤ ‖T‖ * cubeL2 X f :=
  h50w_cubeL2_le_of_le _ _ (mul_nonneg (norm_nonneg _) (cubeL2_nonneg _)) fun v =>
    (vectorWalsh_bound (fun u => T (f u)) v).trans (h50w_cubeL2_map T f)

theorem h50w_opW_sub {n : ℕ} (A B : X →L[ℝ] Y) (f : Cube n → X) :
    operatorWalsh A f - operatorWalsh B f = operatorWalsh (A - B) f := by
  funext v
  simp only [operatorWalsh, vectorWalsh, average, Pi.sub_apply, ← smul_sub, ← Finset.sum_sub_distrib,
    ContinuousLinearMap.sub_apply]

omit [NormedSpace ℝ Y] in
theorem h50w_cubeL2_sub {n : ℕ} (f g : Cube n → Y) :
    |cubeL2 Y f - cubeL2 Y g| ≤ cubeL2 Y (f - g) := by
  have e : ∀ h : Cube n → Y, cubeL2 Y h = Real.sqrt ((Fintype.card (Cube n) : ℝ)⁻¹) *
      ‖(WithLp.toLp 2 h : PiLp 2 (fun _ : Cube n => Y))‖ := fun h => by
    rw [PiLp.norm_eq_of_L2]
    simp only [cubeL2, average, smul_eq_mul]
    exact Real.sqrt_mul (by positivity) _
  rw [e, e, e, ← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have := abs_norm_sub_norm_le (WithLp.toLp 2 f : PiLp 2 (fun _ : Cube n => Y)) (WithLp.toLp 2 g)
  simpa [← WithLp.toLp_sub] using this

theorem t_opWL {n : ℕ} (A B : X →L[ℝ] Y) (f : Cube n → X) :
    |cubeL2 Y (operatorWalsh A f) - cubeL2 Y (operatorWalsh B f)| ≤ ‖A-B‖ * cubeL2 X f := by
  refine (h50w_cubeL2_sub _ _).trans ?_
  rw [h50w_opW_sub]
  exact h50w_opW_bound _ f

theorem h50w_bdd (n : ℕ) (T : X →L[ℝ] Y) : BddAbove (walshOutputs n T) :=
  ⟨‖T‖, by
    rintro r ⟨f, hf, rfl⟩
    exact (h50w_opW_bound T f).trans (by simpa using mul_le_mul_of_nonneg_left hf (norm_nonneg T))⟩

theorem h50w_ne (n : ℕ) (T : X →L[ℝ] Y) : (walshOutputs n T).Nonempty :=
  ⟨_, 0, by simp [cubeL2, average], rfl⟩

theorem h50w_le (n : ℕ) (A B : X →L[ℝ] Y) : walshNorm n A ≤ walshNorm n B + ‖A - B‖ := by
  apply csSup_le (h50w_ne n A)
  rintro r ⟨f, hf, rfl⟩
  have h1 := t_opWL A B f
  have h2 : cubeL2 Y (operatorWalsh B f) ≤ walshNorm n B := le_csSup (h50w_bdd n B) ⟨f, hf, rfl⟩
  have h3 : ‖A - B‖ * cubeL2 X f ≤ ‖A - B‖ := by
    simpa using mul_le_mul_of_nonneg_left hf (norm_nonneg (A - B))
  linarith [(abs_le.mp h1).2]

theorem t_wnL (n : ℕ) (A B : X →L[ℝ] Y) :
    |walshNorm n A - walshNorm n B| ≤ ‖A-B‖ := by
  rw [abs_le]
  have h1 := h50w_le n A B
  have h2 := h50w_le n B A
  rw [norm_sub_rev] at h2
  constructor <;> linarith

theorem t_dual {n : ℕ} (f : Cube n → X) :
    ∃ g : Cube n → (X →L[ℝ] ℝ), cubeL2 (X →L[ℝ] ℝ) g ≤ 1 ∧
      dualPairing f g = cubeL2 X f := by
  set c := cubeL2 X f with hcdef
  by_cases hc : c = 0
  · refine ⟨0, ?_, ?_⟩
    · simp [cubeL2, average]
    · simp [dualPairing, average, hc]
  have hcpos : 0 < c := lt_of_le_of_ne (cubeL2_nonneg f) (Ne.symm hc)
  choose φ hφ1 hφ2 using fun u => exists_dual_vector'' ℝ (f u)
  have hN : (Fintype.card (Cube n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsq := cubeL2_sq f
  rw [← hcdef] at hsq
  simp only [average, smul_eq_mul] at hsq
  refine ⟨fun u => (‖f u‖ / c) • φ u, ?_, ?_⟩
  · unfold cubeL2
    rw [Real.sqrt_le_one]
    simp only [average, smul_eq_mul]
    calc (Fintype.card (Cube n) : ℝ)⁻¹ * ∑ u, ‖(‖f u‖ / c) • φ u‖ ^ 2
        ≤ (Fintype.card (Cube n) : ℝ)⁻¹ * ∑ u, ‖f u‖ ^ 2 / c ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum
          intro u _
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow]
          calc (‖f u‖ / c) ^ 2 * ‖φ u‖ ^ 2 ≤ (‖f u‖ / c) ^ 2 * 1 := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact pow_le_one₀ (norm_nonneg _) (hφ1 u)
            _ = ‖f u‖ ^ 2 / c ^ 2 := by ring
      _ = 1 := by
          rw [← Finset.sum_div, ← mul_div_assoc, ← hsq]
          field_simp
  · simp only [dualPairing, average, smul_eq_mul, ContinuousLinearMap.smul_apply, hφ2,
      RCLike.ofReal_real_eq_id, id]
    have : ∑ u, ‖f u‖ / c * ‖f u‖ = (∑ u, ‖f u‖ ^ 2) / c := by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun u _ => ?_; ring
    rw [this, mul_div_assoc', ← hsq]
    field_simp

theorem h50w_bil {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X) (g : Cube n → (Y →L[ℝ] ℝ)) :
    walshBilinear T f g = dualPairing (operatorWalsh T f) g := by
  simp only [walshBilinear, dualPairing, operatorWalsh, vectorWalsh, average, smul_eq_mul, map_smul,
    map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem h50w_pos_of_ne {n : ℕ} (h : Cube n → Y) (v : Cube n) (hv : h v ≠ 0) : 0 < cubeL2 Y h := by
  unfold cubeL2
  apply Real.sqrt_pos.mpr
  simp only [average, smul_eq_mul]
  apply mul_pos (by positivity)
  exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun u => ‖h u‖ ^ 2)
    (fun u _ => by positivity) (Finset.mem_univ v))

theorem t_half (n : ℕ) {T : X →L[ℝ] Y} (hT : T ≠ 0) :
    ∃ f : Cube n → X, ∃ g : Cube n → (Y →L[ℝ] ℝ),
      cubeL2 X f ≤ 1 ∧ cubeL2 (Y →L[ℝ] ℝ) g ≤ 1 ∧
      walshNorm n T / 2 < walshBilinear T f g ∧ 0 < walshBilinear T f g := by
  obtain ⟨x, hx⟩ : ∃ x, T x ≠ 0 := by
    by_contra h; push Not at h; exact hT (ContinuousLinearMap.ext h)
  have hx0 : x ≠ 0 := fun h => hx (by rw [h, map_zero])
  set x' := (‖x‖⁻¹) • x
  have hx'n : ‖x'‖ = 1 := by
    simp only [x', norm_smul, norm_inv, norm_norm]; field_simp [norm_ne_zero_iff.mpr hx0]
  have hTx' : T x' ≠ 0 := by
    simp only [x', map_smul]; exact smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hx0)) hx
  let f0 : Cube n → X := fun _ => x'
  have hf0 : cubeL2 X f0 ≤ 1 :=
    h50w_cubeL2_le_of_le f0 1 zero_le_one (fun u => hx'n.le)
  have hv : operatorWalsh T f0 (fun _ => false) = T x' := by
    simp only [operatorWalsh, vectorWalsh, average, f0, character]
    simp only [Bool.false_eq_true, if_false, Finset.prod_const_one, one_smul, Finset.sum_const,
      Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero),
      one_smul]
  have hpos0 : 0 < cubeL2 Y (operatorWalsh T f0) :=
    h50w_pos_of_ne _ (fun _ => false) (by rw [hv]; exact hTx')
  have hW : 0 < walshNorm n T :=
    lt_of_lt_of_le hpos0 (le_csSup (h50w_bdd n T) ⟨f0, hf0, rfl⟩)
  obtain ⟨r, ⟨f, hf, rfl⟩, hr⟩ := exists_lt_of_lt_csSup (h50w_ne n T) (half_lt_self hW)
  obtain ⟨g, hg, hfg⟩ := t_dual (operatorWalsh T f)
  refine ⟨f, g, hf, hg, ?_, ?_⟩
  · rw [h50w_bil, hfg]; exact hr
  · rw [h50w_bil, hfg]; have : walshNorm n T = sSup (walshOutputs n T) := rfl; linarith

theorem solution (n : ℕ) {T : X →L[ℝ] Y} (hT : T ≠ 0) :
    ∃ f : Cube n → X, ∃ g : Cube n → (Y →L[ℝ] ℝ),
      cubeL2 X f ≤ 1 ∧ cubeL2 (Y →L[ℝ] ℝ) g ≤ 1 ∧
      walshNorm n T / 2 < walshBilinear T f g ∧ 0 < walshBilinear T f g := by
  exact t_half n hT

