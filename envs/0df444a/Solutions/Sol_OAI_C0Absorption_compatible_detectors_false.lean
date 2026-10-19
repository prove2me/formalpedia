-- Prove2me | solution 1 for OAI.C0Absorption.compatible_detectors_false
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:40:06.907976+00:00
-- url     : https://prove2.me/submissions/c1d34c2d-eb1e-469a-a150-819a24704d49

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Definitions.Def_OAI_Analysis_C0Absorption_Duality
import Definitions.Def_OAI_Analysis_C0Absorption_Selection
import Definitions.Def_OAI_Analysis_C0Absorption_Supports
import Definitions.Def_OAI_Analysis_C0Absorption_Operations

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
theorem h41_sign_pair {X : Type*} [AddCommGroup X] [Module ℝ X]
    (q : Seminorm ℝ X) {n : ℕ} (m : Fin n → X) (ε : Fin n → Bool) (i : Fin n) :
    2 * (q (m i)) ^ 2 ≤
      (q (∑ j, realSign (ε j) • m j)) ^ 2 +
      (q (∑ j, realSign (flipSign i ε j) • m j)) ^ 2 := by
  set S1 := ∑ j, realSign (ε j) • m j
  set S2 := ∑ j, realSign (flipSign i ε j) • m j
  have key : S1 - S2 = (2 * realSign (ε i)) • m i := by
    simp only [S1, S2, ← Finset.sum_sub_distrib, ← sub_smul]
    rw [Finset.sum_eq_single i]
    · congr 1
      simp only [flipSign, Equiv.coe_fn_mk, if_true, realSign_not]; ring
    · intro j _ hj
      simp [flipSign, hj]
    · simp
  have hq : q ((2 * realSign (ε i)) • m i) = 2 * q (m i) := by
    rw [map_smul_eq_mul]; simp [abs_mul]
  have h1 : 2 * q (m i) ≤ q S1 + q S2 := by
    rw [← hq, ← key]; exact map_sub_le_add q S1 S2
  have h0 : 0 ≤ q (m i) := apply_nonneg q _
  have hS1 : 0 ≤ q S1 := apply_nonneg q _
  have hS2 : 0 ≤ q S2 := apply_nonneg q _
  nlinarith [sq_nonneg (q S1 - q S2), mul_le_mul h1 h1 (by positivity) (by positivity)]

theorem h41_sign_avg {X : Type*} [AddCommGroup X] [Module ℝ X]
    (q : Seminorm ℝ X) {N : ℕ} (m : Fin N → X) (i : Fin N) :
    (2:ℝ)^N * q (m i) ^ 2 ≤ ∑ ε : Fin N → Bool, q (∑ j, realSign (ε j) • m j) ^ 2 := by
  have h1 : ∑ ε : Fin N → Bool, 2 * q (m i) ^ 2 ≤ ∑ ε : Fin N → Bool,
      ((q (∑ j, realSign (ε j) • m j)) ^ 2 + (q (∑ j, realSign (flipSign i ε j) • m j)) ^ 2) :=
    Finset.sum_le_sum (fun ε _ => h41_sign_pair q m ε i)
  rw [Finset.sum_add_distrib,
    Equiv.sum_comp (flipSign i) (fun ε => (q (∑ j, realSign (ε j) • m j)) ^ 2)] at h1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul] at h1
  push_cast at h1
  linarith

theorem solution {S : Type*} [MetricSpace S]
    (L : ℕ → Set (S → ℝ)) (o : S)
    (m : ℕ → TestSpace L o) (M : ℝ) (hm : SignedBound m M)
    (F : ℕ → S → ℝ) (h : ℕ) (K : ℝ≥0) (hF : ∀ i, F i ∈ L h)
    (hLip : ∀ n (ε : Fin n → ℝ), (∀ i, |ε i|=1) →
      LipschitzWith K (fun s => ∑ i, ε i*F i s))
    {δ : ℝ} (hδ : 0 < δ) (hd : ∀ i, δ ≤ |completedPairing L o (F i) (m i)|) : False := by
  obtain ⟨c, hc⟩ := exists_nat_ge (K:ℝ)
  obtain ⟨n, hn⟩ := triple_surjective (h, c, 0)
  have hpr : (listExponent n).toReal = 2 := by
    simp only [listExponent, hn]; norm_num
  have hKc : K ≤ listConstant n := by
    unfold listConstant; rw [hn, ← NNReal.coe_le_coe]; push_cast; linarith
  have hmem : ∀ i, F i ∈ L (triple n).1 := by rw [hn]; exact hF
  let l : ∀ N : ℕ, AdmissibleList (L (triple n).1) (listConstant n) := fun N =>
    AdmissibleList.mk N (fun i => F i) (fun i => hmem i) (fun ε hε => (hLip N ε hε).weaken hKc)
  have hpre : ∀ N (m : PreSpace L o), ‖(l N).eval (listExponent n) m‖ ≤ (squareWeight n : ℝ)⁻¹ * ‖m‖ :=
    fun N m => (list_le_sigma _ _ _ o (l N) m).trans (sigma_le_preNorm L o n m)
  have hbound : ∀ N (z : TestSpace L o), ‖completedList L o n (l N) z‖ ≤ (squareWeight n : ℝ)⁻¹ * ‖z‖ := by
    intro N z
    refine UniformSpace.Completion.induction_on (p := fun z : UniformSpace.Completion (PreSpace L o) =>
      ‖completedList L o n (l N) z‖ ≤ (squareWeight n : ℝ)⁻¹ * ‖z‖) z ?_ ?_
    · exact isClosed_le (completedList L o n (l N)).continuous.norm (continuous_const.mul continuous_norm)
    · intro m
      have := completedList_coe L o n (l N) m
      change ‖completedList L o n (l N) (toTestSpace L o m)‖ ≤ (squareWeight n : ℝ)⁻¹ * ‖toTestSpace L o m‖
      rw [this, norm_toTestSpace]
      exact hpre N m
  have hcoord : ∀ N (z : TestSpace L o) (i : Fin N),
      (completedList L o n (l N) z) i = completedPairing L o (F i) z := by
    intro N z i
    have hb : ∀ m : PreSpace L o, |pairing S (F i) m| ≤ (squareWeight n)⁻¹ * ‖m‖ := by
      intro m
      have h1 := PiLp.norm_apply_le ((l N).eval (listExponent n) m) i
      rw [Real.norm_eq_abs] at h1
      change |pairing S (F i) m| ≤ _ at h1
      push_cast
      exact h1.trans (hpre N m)
    refine UniformSpace.Completion.induction_on (p := fun z : UniformSpace.Completion (PreSpace L o) =>
      (completedList L o n (l N) z) i = completedPairing L o (F i) z) z ?_ ?_
    · exact isClosed_eq ((PiLp.proj (𝕜 := ℝ) (p := listExponent n) (β := fun _ : Fin N => ℝ) i).comp
        (completedList L o n (l N))).continuous UniformSpace.Completion.continuous_extension
    · intro m
      change (completedList L o n (l N) (toTestSpace L o m)) i = completedPairing L o (F i) (toTestSpace L o m)
      rw [completedList_coe, completedPairing_coe L o (F i) _ hb m]
      rfl
  have hM0 : 0 ≤ M := by
    have := hm 0 Fin.val Fin.val_injective (fun _ => true)
    simpa using this
  set C := (squareWeight n : ℝ)⁻¹ with hC
  have hC0 : 0 ≤ C := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (C^2 * M^2 / δ^2)
  have hNd : C^2 * M^2 < N * δ^2 := by
    rwa [div_lt_iff₀ (by positivity)] at hN
  -- seminorms
  let q : Fin N → Seminorm ℝ (TestSpace L o) := fun i =>
    (normSeminorm ℝ ℝ).comp ((PiLp.projₗ (𝕜 := ℝ) (listExponent n) (fun _ : Fin N => ℝ) i).comp
      (completedList L o n (l N)).toLinearMap)
  have hq : ∀ i z, q i z = |(completedList L o n (l N) z) i| := fun i z => rfl
  let z : (Fin N → Bool) → TestSpace L o := fun ε => ∑ j : Fin N, realSign (ε j) • m j
  have hz : ∀ ε, ‖z ε‖ ≤ M := fun ε => hm N Fin.val Fin.val_injective ε
  have hnorm : ∀ ε, ‖completedList L o n (l N) (z ε)‖ ^ 2 =
      ∑ i : Fin N, |(completedList L o n (l N) (z ε)) i| ^ 2 := by
    intro ε
    have := PiLp.norm_eq_sum (by rw [hpr]; norm_num) (completedList L o n (l N) (z ε))
    rw [hpr] at this
    rw [this]
    have hs : 0 ≤ ∑ i : Fin N, ‖(completedList L o n (l N) (z ε)) i‖ ^ (2:ℝ) :=
      Finset.sum_nonneg (fun i _ => by positivity)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
    norm_num
  have step1 : ∀ i : Fin N, (2:ℝ)^N * δ^2 ≤ ∑ ε : Fin N → Bool, |(completedList L o n (l N) (z ε)) i| ^ 2 := by
    intro i
    have h1 := h41_sign_avg (q i) (fun j => m j) i
    simp only [hq] at h1
    rw [hcoord] at h1
    have h2 : δ^2 ≤ |completedPairing L o (F i) (m i)| ^ 2 := by
      have := hd i
      nlinarith
    have h3 : (0:ℝ) < 2^N := by positivity
    calc (2:ℝ)^N * δ^2 ≤ 2^N * |completedPairing L o (F i) (m i)| ^ 2 :=
          mul_le_mul_of_nonneg_left h2 h3.le
      _ ≤ _ := h1
  have step2 : ∑ i : Fin N, (2:ℝ)^N * δ^2 ≤ ∑ ε : Fin N → Bool, (C * M)^2 := by
    calc ∑ i : Fin N, (2:ℝ)^N * δ^2
        ≤ ∑ i : Fin N, ∑ ε : Fin N → Bool, |(completedList L o n (l N) (z ε)) i| ^ 2 :=
          Finset.sum_le_sum (fun i _ => step1 i)
      _ = ∑ ε : Fin N → Bool, ‖completedList L o n (l N) (z ε)‖ ^ 2 := by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun ε _ => (hnorm ε).symm)
      _ ≤ ∑ ε : Fin N → Bool, (C * M)^2 := by
          refine Finset.sum_le_sum (fun ε _ => ?_)
          have h1 := hbound N (z ε)
          have h2 : C * ‖z ε‖ ≤ C * M := mul_le_mul_of_nonneg_left (hz ε) hC0
          have h3 := norm_nonneg (completedList L o n (l N) (z ε))
          nlinarith
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul] at step2
  push_cast at step2
  have h2N : (0:ℝ) < 2^N := by positivity
  nlinarith

