-- Prove2me | solution 1 for OAI.Cotype.kConvex_iff_coordinate_firstCoefficient_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T22:18:33.509987+00:00
-- url     : https://prove2.me/submissions/a86e3485-174e-4e1c-b9a0-1b66bad62c3e

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
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality
import Definitions.Def_OAI_Analysis_Cotype_Rectangles
import Definitions.Def_OAI_Analysis_Cotype_BinaryRank
import Definitions.Def_OAI_Analysis_Cotype_BiasedFourier
import Definitions.Def_OAI_Analysis_Cotype_Damping
import Definitions.Def_OAI_Analysis_Cotype_WalshExactPairing
import Definitions.Def_OAI_Analysis_Cotype_WalshSymmetry
import Definitions.Def_OAI_Analysis_Cotype_CubeCoordinateProjections
import Definitions.Def_OAI_Analysis_Cotype_CubeFirstChaos

open OAI OAI.Cotype
open scoped BigOperators
open WithLp

section h51
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma h51_xavg_cons {k : ℕ} (G : (Fin (k+1) → Bool) → X) :
    average G = (1/2 : ℝ) • (average (fun ω : Fin k → Bool => G (Fin.cons false ω)) +
      average (fun ω : Fin k → Bool => G (Fin.cons true ω))) := by
  simp only [average]
  rw [← (projectionChoiceCons Bool k).sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, projectionChoiceCons, Equiv.coe_fn_mk]
  have hc : ((Fintype.card (Fin (k+1) → Bool) : ℕ) : ℝ)⁻¹ =
      (1/2 : ℝ) * ((Fintype.card (Fin k → Bool) : ℕ) : ℝ)⁻¹ := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    push_cast; rw [pow_succ]; field_simp
  rw [hc]; simp only [mul_smul, smul_add]; abel

lemma h51_xavg_zero (G : (Fin 0 → Bool) → X) (ω₀ : Fin 0 → Bool) : average G = G ω₀ := by
  simp only [average]
  have : (Finset.univ : Finset (Fin 0 → Bool)) = {ω₀} := by
    ext ω; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]; exact Subsingleton.elim _ _
  rw [this, Finset.sum_singleton]
  simp

lemma h51_prod {n : ℕ} : ∀ (k : ℕ) (c : Fin k → Fin n) (_hc : Function.Injective c) (μ : Fin k → Bool)
    (F : PiLp 2 (fun _ : Cube n => X)) (ε : Cube n),
    projectionProduct (fun j => if μ j then coordinateExpectation (X := X) (c j) else 1) F ε =
    average (fun ω : Fin k → Bool =>
      F (fun t => Bool.xor (decide (∃ j, μ j = true ∧ ω j = true ∧ c j = t)) (ε t))) := by
  intro k
  induction k with
  | zero =>
    intro c _ μ F ε
    rw [h51_xavg_zero _ (fun i => i.elim0)]
    simp [projectionProduct]
  | succ k ih =>
    intro c hc μ F ε
    have hc' : Function.Injective (fun j : Fin k => c j.succ) := fun a b h => Fin.succ_injective _ (hc h)
    have hstep : projectionProduct (fun j => if μ j then coordinateExpectation (X := X) (c j) else 1) F ε =
        ((if μ 0 then coordinateExpectation (X := X) (c 0) else 1)
          (projectionProduct (fun j : Fin k => if μ j.succ then coordinateExpectation (X := X) (c j.succ) else 1) F)) ε := rfl
    rw [hstep, h51_xavg_cons]
    have key0 : ∀ ω : Fin k → Bool, (fun t => Bool.xor (decide (∃ j : Fin (k+1), μ j = true ∧
        (Fin.cons false ω : Fin (k+1) → Bool) j = true ∧ c j = t)) (ε t)) =
        (fun t => Bool.xor (decide (∃ j : Fin k, μ j.succ = true ∧ ω j = true ∧ c j.succ = t)) (ε t)) := by
      intro ω; funext t
      congr 2
      simp [Fin.exists_fin_succ]
    by_cases hμ : μ 0 = true
    · have key1 : ∀ ω : Fin k → Bool, (fun t => Bool.xor (decide (∃ j : Fin (k+1), μ j = true ∧
          (Fin.cons true ω : Fin (k+1) → Bool) j = true ∧ c j = t)) (ε t)) =
          (fun t => Bool.xor (decide (∃ j : Fin k, μ j.succ = true ∧ ω j = true ∧ c j.succ = t))
            (signCubeTwist (unitIndex (c 0)) ε t)) := by
        intro ω; funext t
        simp only [Fin.exists_fin_succ, Fin.cons_zero, Fin.cons_succ, hμ, true_and]
        show _ = Bool.xor _ (Bool.xor (unitIndex (c 0) t) (ε t))
        simp only [unitIndex]
        by_cases h0 : c 0 = t
        · have hn : ¬ ∃ j : Fin k, μ j.succ = true ∧ ω j = true ∧ c j.succ = t := by
            rintro ⟨j, -, -, hj⟩
            exact Fin.succ_ne_zero j (hc (hj.trans h0.symm))
          simp [h0, hn]
        · simp [h0]
      simp only [hμ, if_true, coordinateExpectation_apply]
      rw [ih _ hc' _ F ε, ih _ hc' _ F (signCubeTwist (unitIndex (c 0)) ε)]
      simp_rw [key0, key1]
    · have hμf : μ 0 = false := by simpa using hμ
      simp only [hμf, Bool.false_eq_true, if_false, ContinuousLinearMap.one_apply]
      rw [ih _ hc' _ F ε]
      have key1 : ∀ ω : Fin k → Bool, (fun t => Bool.xor (decide (∃ j : Fin (k+1), μ j = true ∧
          (Fin.cons true ω : Fin (k+1) → Bool) j = true ∧ c j = t)) (ε t)) =
          (fun t => Bool.xor (decide (∃ j : Fin k, μ j.succ = true ∧ ω j = true ∧ c j.succ = t)) (ε t)) := by
        intro ω; funext t
        congr 2
        simp [Fin.exists_fin_succ, hμf]
      simp_rw [key0, key1]
      rw [← two_smul ℝ, smul_smul]; norm_num

lemma h51_xavg_equiv {α : Type*} [Fintype α] (e : α ≃ α) (G : α → X) :
    average (fun a => G (e a)) = average G := by
  simp only [average]; congr 1; exact Equiv.sum_comp e G

lemma h51_xavg_sub {α : Type*} [Fintype α] (G H : α → X) :
    average (fun a => G a - H a) = average G - average H := by
  simp only [average, Finset.sum_sub_distrib, smul_sub]

lemma h51_xavg_add {α : Type*} [Fintype α] (G H : α → X) :
    average (fun a => G a + H a) = average G + average H := by
  simp only [average, Finset.sum_add_distrib, smul_add]

lemma h51_xavg_smul {α : Type*} [Fintype α] (c : ℝ) (G : α → X) :
    average (fun a => c • G a) = c • average G := by
  simp only [average, ← Finset.smul_sum, smul_comm c]

lemma h51_split {n : ℕ} (i : Fin n) (g : Cube n → X) :
    average (fun ω : Cube n => sign (ω i) • g ω) = (1/2 : ℝ) •
      (average (fun ω : Cube n => g (Function.update ω i false)) -
        average (fun ω : Cube n => g (Function.update ω i true))) := by
  let φ : Cube n ≃ Cube n := ⟨fun ω => Function.update ω i (!ω i), fun ω => Function.update ω i (!ω i),
    fun ω => by funext j; by_cases h : j = i <;> simp [Function.update, h],
    fun ω => by funext j; by_cases h : j = i <;> simp [Function.update, h]⟩
  have h1 : average (fun ω : Cube n => sign (ω i) • g ω) =
      average (fun ω : Cube n => (-1 : ℝ) • (sign (ω i) • g (φ ω))) := by
    rw [← h51_xavg_equiv φ]
    congr 1; funext ω
    show sign (Function.update ω i (!ω i) i) • _ = _
    simp [smul_smul]
  have h2 : ∀ ω : Cube n, sign (ω i) • g ω + (-1 : ℝ) • (sign (ω i) • g (φ ω)) =
      g (Function.update ω i false) - g (Function.update ω i true) := by
    intro ω
    show _ + (-1:ℝ) • (sign (ω i) • g (Function.update ω i (!ω i))) = _
    cases hω : ω i
    · have : Function.update ω i false = ω := by rw [← hω, Function.update_eq_self]
      simp [this, sign, sub_eq_add_neg]
    · have : Function.update ω i true = ω := by rw [← hω, Function.update_eq_self]
      simp [this, sign, sub_eq_add_neg, add_comm]
  have h3 : (2:ℝ) • average (fun ω : Cube n => sign (ω i) • g ω) =
      average (fun ω : Cube n => g (Function.update ω i false)) -
        average (fun ω : Cube n => g (Function.update ω i true)) := by
    rw [two_smul]
    conv_lhs => arg 2; rw [h1]
    rw [← h51_xavg_add, ← h51_xavg_sub]
    congr 1; funext ω; exact h2 ω
  rw [← h3, smul_smul]; norm_num

end h51

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
theorem h51_cfr {n : ℕ} (f : Cube n → X) :
    projectionLinearCoefficient (coordinateExpectation (X := X) (n := n)) (toLp 2 f) =
      toLp 2 (radProjection X f) := by
  ext ε
  simp only [projectionLinearCoefficient, ContinuousLinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  simp only [radProjection, rademacherSum, moment]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
  set G := (projectionSubset coordinateExpectation fun j => decide (j ≠ i)) (toLp 2 f) with hGdef
  have hG : ∀ δ : Cube n, G δ = average (fun ω : Cube n =>
      f (fun t => Bool.xor (decide (t ≠ i ∧ ω t = true)) (δ t))) := by
    intro δ
    have := h51_prod n id Function.injective_id (fun j => decide (j ≠ i)) (toLp 2 f) δ
    simp only [id] at this
    rw [hGdef]
    unfold projectionSubset
    rw [this]
    congr 1; funext ω
    congr 1; funext t
    congr 2
    simp
  rw [WithLp.ofLp_sub, Pi.sub_apply, coordinateExpectation_apply]
  change G ε - (1/2 : ℝ) • (G ε + G (signCubeTwist (unitIndex i) ε)) = _
  rw [hG, hG]
  -- RHS as average over ω of sign(ω_i) f(ω ⊕ ε)
  let xe : Cube n ≃ Cube n := ⟨fun ω t => Bool.xor (ω t) (ε t), fun ω t => Bool.xor (ω t) (ε t),
    fun ω => by funext t; simp, fun ω => by funext t; simp⟩
  have hR : sign (ε i) • average (fun δ : Cube n => sign (δ i) • f δ) =
      average (fun ω : Cube n => sign (ω i) • f (fun t => Bool.xor (ω t) (ε t))) := by
    rw [← h51_xavg_smul, ← h51_xavg_equiv xe]
    congr 1; funext ω
    show sign (ε i) • (sign (Bool.xor (ω i) (ε i)) • _) = _
    rw [smul_smul]
    congr 1
    cases ω i <;> cases ε i <;> simp [sign]
  rw [hR, h51_split i (fun ω => f (fun t => Bool.xor (ω t) (ε t)))]
  have e1 : ∀ ω : Cube n, (fun t => Bool.xor (decide (t ≠ i ∧ ω t = true)) (ε t)) =
      (fun t => Bool.xor (Function.update ω i false t) (ε t)) := by
    intro ω; funext t
    by_cases h : t = i
    · subst h; simp
    · simp [h, Function.update_of_ne h]
  have e2 : ∀ ω : Cube n, (fun t => Bool.xor (decide (t ≠ i ∧ ω t = true))
      (signCubeTwist (unitIndex i) ε t)) =
      (fun t => Bool.xor (Function.update ω i true t) (ε t)) := by
    intro ω; funext t
    show _ = Bool.xor _ (ε t)
    change Bool.xor _ (Bool.xor (unitIndex i t) (ε t)) = _
    by_cases h : t = i
    · subst h; simp [unitIndex]
    · simp [h, Function.update_of_ne h, unitIndex, Ne.symm h]
  simp_rw [e1, e2]
  rw [smul_add, smul_sub]
  module

lemma h51_normL2 {n : ℕ} (g : Cube n → X) :
    ‖(toLp 2 g : PiLp 2 (fun _ : Cube n => X))‖ = Real.sqrt (Fintype.card (Cube n)) * cubeL2 X g := by
  rw [PiLp.norm_eq_of_L2]
  simp only [cubeL2, average, smul_eq_mul, PiLp.toLp_apply]
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  have : (Fintype.card (Cube n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem solution :
    KConvex X ↔ ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (f : PiLp 2 (fun _ : Cube n => X)),
      ‖projectionLinearCoefficient (coordinateExpectation (X := X) (n := n)) f‖ ≤ K*‖f‖ := by
  have hpos : ∀ n : ℕ, 0 < Real.sqrt (Fintype.card (Cube n)) := fun n =>
    Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  constructor
  · rintro ⟨K, hK, h⟩
    refine ⟨K, hK, fun n F => ?_⟩
    have hF : F = toLp 2 (ofLp F) := rfl
    rw [hF, h51_cfr, h51_normL2, h51_normL2]
    have := h n (ofLp F)
    calc Real.sqrt (Fintype.card (Cube n)) * cubeL2 X (radProjection X (ofLp F))
        ≤ Real.sqrt (Fintype.card (Cube n)) * (K * cubeL2 X (ofLp F)) :=
          mul_le_mul_of_nonneg_left this (hpos n).le
      _ = K * (Real.sqrt (Fintype.card (Cube n)) * cubeL2 X (ofLp F)) := by ring
  · rintro ⟨K, hK, h⟩
    refine ⟨K, hK, fun n f => ?_⟩
    have := h n (toLp 2 f)
    rw [h51_cfr, h51_normL2, h51_normL2] at this
    have h2 : Real.sqrt (Fintype.card (Cube n)) * cubeL2 X (radProjection X f) ≤
        Real.sqrt (Fintype.card (Cube n)) * (K * cubeL2 X f) := by linarith
    exact le_of_mul_le_mul_left h2 (hpos n)
