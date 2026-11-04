-- Prove2me | solution 1 for KellyRSN.PartialBalance.partial_balance_equivalences
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T01:47:30.712054+00:00
-- url     : https://prove2.me/submissions/5546ad4e-b5d9-471e-ade2-dc335bcda7f5

import Mathlib
import Definitions.Def_KellyRSN_PartialBalance_IsKellyRates
import Definitions.Def_KellyRSN_PartialBalance_IsEquilibriumDist
import Definitions.Def_KellyRSN_PartialBalance_IsPartialBalance
import Definitions.Def_KellyRSN_PartialBalance_truncRates
import Definitions.Def_KellyRSN_PartialBalance_condDist
import Definitions.Def_KellyRSN_PartialBalance_scaleInside
import Definitions.Def_KellyRSN_PartialBalance_scaleOutward
import Definitions.Def_KellyRSN_PartialBalance_ReversalTruncationCommute
import Definitions.Def_KellyRSN_PartialBalance_fluxOut
import Definitions.Def_KellyRSN_PartialBalance_SameObservedEquilibrium
import Definitions.Def_KellyRSN_PartialBalance_jumpChainLaw
import Definitions.Def_KellyRSN_PartialBalance_exitKernel
import Definitions.Def_KellyRSN_PartialBalance_entryKernel
import Definitions.Def_KellyRSN_PartialBalance_IsStationaryProb

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

set_option autoImplicit false

open scoped ENNReal NNReal

namespace KPB

open KellyRSN.PartialBalance

theorem split {S : Type*} (A : Set S) (f : S → ℝ≥0∞) :
    ∑' k, f k = ∑' k : A, f k + ∑' k : ↥Aᶜ, f k :=
  (ENNReal.summable.tsum_add_tsum_compl (f := f) ENNReal.summable).symm

/-- Real-linear cancellation behind (iii) and (iv). -/
theorem key (a b a' b' : ℝ≥0∞) (c : ℝ≥0) (hc : c ≠ 1) (hfin : a + b ≠ ⊤)
    (h : a + b = a' + b') : ((c : ℝ≥0∞) * a + b = (c : ℝ≥0∞) * a' + b') ↔ a = a' := by
  have hfin' : a' + b' ≠ ⊤ := h ▸ hfin
  have ha : a ≠ ⊤ := fun h' => hfin (by simp [h'])
  have hb : b ≠ ⊤ := fun h' => hfin (by simp [h'])
  have ha' : a' ≠ ⊤ := fun h' => hfin' (by simp [h'])
  have hb' : b' ≠ ⊤ := fun h' => hfin' (by simp [h'])
  have hcT : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hr : a.toReal + b.toReal = a'.toReal + b'.toReal := by
    rw [← ENNReal.toReal_add ha hb, ← ENNReal.toReal_add ha' hb', h]
  have hcr : (c : ℝ) ≠ 1 := by exact_mod_cast hc
  constructor
  · intro h2
    have h3 : (c : ℝ) * a.toReal + b.toReal = (c : ℝ) * a'.toReal + b'.toReal := by
      have := congrArg ENNReal.toReal h2
      rwa [ENNReal.toReal_add (ENNReal.mul_ne_top hcT ha) hb,
        ENNReal.toReal_add (ENNReal.mul_ne_top hcT ha') hb', ENNReal.toReal_mul,
        ENNReal.toReal_mul, ENNReal.coe_toReal] at this
    have h4 : ((c : ℝ) - 1) * (a.toReal - a'.toReal) = 0 := by linarith
    rcases mul_eq_zero.1 h4 with h5 | h5
    · exact absurd (by linarith) hcr
    · exact (ENNReal.toReal_eq_toReal_iff' ha ha').1 (by linarith)
  · intro h2
    subst h2
    have : b = b' := by
      have := congrArg (fun x => x - a) h
      simpa [ENNReal.add_sub_cancel_left ha] using this
    rw [this]

theorem pi_ne_top {S : Type*} (π : S → ℝ≥0∞) (h1 : ∑' j, π j = 1) (j : S) : π j ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (h1 ▸ ENNReal.le_tsum j)

theorem Z_ne_top {S : Type*} (π : S → ℝ≥0∞) (h1 : ∑' j, π j = 1) (A : Set S) :
    ∑' k : A, π k ≠ ⊤ := by
  have h := split A π
  rw [h1] at h
  exact ne_top_of_le_ne_top ENNReal.one_ne_top (h ▸ le_self_add)

theorem W_ne_top {S : Type*} (π : S → ℝ≥0∞) (h1 : ∑' j, π j = 1) (A : Set S) :
    ∑' k : ↥Aᶜ, π k ≠ ⊤ := by
  have h := split A π
  rw [h1] at h
  exact ne_top_of_le_ne_top ENNReal.one_ne_top (h ▸ le_add_self)

theorem Z_ne_zero {S : Type*} (π : S → ℝ≥0∞) (hpos : ∀ j, 0 < π j) (A : Set S)
    (hA : A.Nonempty) : ∑' k : A, π k ≠ 0 := by
  obtain ⟨a, ha⟩ := hA
  exact ne_of_gt (lt_of_lt_of_le (hpos a) (ENNReal.le_tsum (⟨a, ha⟩ : A)))

/-- The global balance equation at `j`, split along `A`. -/
theorem global_split {S : Type*} (q : S → S → ℝ≥0∞) (π : S → ℝ≥0∞) (A : Set S) (j : S)
    (hb : π j * ∑' k, q j k = ∑' k, π k * q k j) :
    π j * ∑' k : A, q j k + π j * ∑' k : ↥Aᶜ, q j k =
      ∑' k : A, π k * q k j + ∑' k : ↥Aᶜ, π k * q k j := by
  rw [← mul_add, ← split A (fun k => q j k), hb, ← split A (fun k => π k * q k j)]

theorem global_fin {S : Type*} (q : S → S → ℝ≥0∞) (π : S → ℝ≥0∞) (A : Set S) (j : S)
    (hq : ∑' k, q j k ≠ ⊤) (hπ : π j ≠ ⊤) :
    π j * ∑' k : A, q j k + π j * ∑' k : ↥Aᶜ, q j k ≠ ⊤ := by
  rw [← mul_add, ← split A (fun k => q j k)]
  exact ENNReal.mul_ne_top hπ hq

/-! ### (i) ⇔ (ii) -/

theorem part2 {S : Type*} (q : S → S → ℝ≥0∞) (π : S → ℝ≥0∞) (hπ : IsEquilibriumDist q π)
    (A : Set S) (hA : A.Nonempty) :
    IsPartialBalance q π A ↔ IsEquilibriumDist (truncRates q A) (condDist π A) := by
  obtain ⟨hpos, h1, -⟩ := hπ
  set Z := ∑' k : A, π k with hZ
  have hZ0 : Z ≠ 0 := Z_ne_zero π hpos A hA
  have hZT : Z ≠ ⊤ := Z_ne_top π h1 A
  have hiff : ∀ j : A, (π j * ∑' k : A, q j k = ∑' k : A, π k * q k j) ↔
      (condDist π A j * ∑' k : A, truncRates q A j k =
        ∑' k : A, condDist π A k * truncRates q A k j) := by
    intro j
    simp only [condDist, truncRates, div_eq_mul_inv]
    have e1 : π j * Z⁻¹ * ∑' k : A, q j k = Z⁻¹ * (π j * ∑' k : A, q j k) := by ring
    have e2 : ∑' k : A, π k * Z⁻¹ * q k j = Z⁻¹ * ∑' k : A, π k * q k j := by
      rw [← ENNReal.tsum_mul_left]; congr 1; ext k; ring
    rw [← hZ, e1, e2]
    exact (ENNReal.mul_right_inj (ENNReal.inv_ne_zero.2 hZT) (ENNReal.inv_ne_top.2 hZ0)).symm
  constructor
  · intro hPB
    refine ⟨fun j => ENNReal.div_pos (hpos j).ne' hZT, ?_, fun j => (hiff j).1 (hPB j j.2)⟩
    simp only [condDist, div_eq_mul_inv]
    rw [ENNReal.tsum_mul_right, ← hZ]
    exact ENNReal.mul_inv_cancel hZ0 hZT
  · rintro ⟨-, -, hbal⟩ j hj
    exact (hiff ⟨j, hj⟩).2 (hbal ⟨j, hj⟩)

/-! ### (i) ⇔ (iii) -/

open Classical in
theorem part3 {S : Type*} (q : S → S → ℝ≥0∞) (hqf : ∀ j, ∑' k, q j k ≠ ⊤) (π : S → ℝ≥0∞)
    (hπ : IsEquilibriumDist q π) (A : Set S) (c : ℝ≥0) (hc1 : c ≠ 1) :
    IsPartialBalance q π A ↔ IsEquilibriumDist (scaleInside q A c) π := by
  obtain ⟨hpos, h1, hbal⟩ := hπ
  have hin : ∀ j ∈ A, (π j * ∑' k : A, q j k = ∑' k : A, π k * q k j) ↔
      (π j * ∑' k, scaleInside q A c j k = ∑' k, π k * scaleInside q A c k j) := by
    intro j hj
    rw [split A (fun k => scaleInside q A c j k), split A (fun k => π k * scaleInside q A c k j)]
    have e1 : ∑' k : A, scaleInside q A c j k = (c : ℝ≥0∞) * ∑' k : A, q j k := by
      rw [← ENNReal.tsum_mul_left]; congr 1; ext k; simp [scaleInside, hj, k.2]
    have e2 : ∑' k : ↥Aᶜ, scaleInside q A c j k = ∑' k : ↥Aᶜ, q j k := by
      congr 1; ext k; have := k.2; simp only [Set.mem_compl_iff] at this; simp [scaleInside, this]
    have e3 : ∑' k : A, π k * scaleInside q A c k j = (c : ℝ≥0∞) * ∑' k : A, π k * q k j := by
      rw [← ENNReal.tsum_mul_left]; congr 1; ext k; simp [scaleInside, hj, k.2]; ring
    have e4 : ∑' k : ↥Aᶜ, π k * scaleInside q A c k j = ∑' k : ↥Aᶜ, π k * q k j := by
      congr 1; ext k; have := k.2; simp only [Set.mem_compl_iff] at this; simp [scaleInside, this]
    rw [e1, e2, e3, e4, mul_add, mul_left_comm]
    exact (key _ _ _ _ c hc1 (global_fin q π A j (hqf j) (pi_ne_top π h1 j))
      (global_split q π A j (hbal j))).symm
  have hout : ∀ j ∉ A, (π j * ∑' k, scaleInside q A c j k = ∑' k, π k * scaleInside q A c k j) ↔
      (π j * ∑' k, q j k = ∑' k, π k * q k j) := by
    intro j hj
    have e1 : ∀ k, scaleInside q A c j k = q j k := fun k => by simp [scaleInside, hj]
    have e2 : ∀ k, scaleInside q A c k j = q k j := fun k => by simp [scaleInside, hj]
    simp only [e1, e2]
  constructor
  · intro hPB
    refine ⟨hpos, h1, fun j => ?_⟩
    by_cases hj : j ∈ A
    · exact (hin j hj).1 (hPB j hj)
    · exact (hout j hj).2 (hbal j)
  · rintro ⟨-, -, hb⟩ j hj
    exact (hin j hj).2 (hb j)

/-! ### (i) ⇔ (iv) -/

open Classical in
theorem part4 {S : Type*} (q : S → S → ℝ≥0∞) (hqf : ∀ j, ∑' k, q j k ≠ ⊤) (π : S → ℝ≥0∞)
    (hπ : IsEquilibriumDist q π) (A : Set S) (hA : A.Nonempty) (c : ℝ≥0) (hc0 : c ≠ 0)
    (hc1 : c ≠ 1) :
    IsPartialBalance q π A ↔ ∃ B : ℝ≥0∞, IsEquilibriumDist (scaleOutward q A c)
        (fun j => if j ∈ A then B * π j else B * (c : ℝ≥0∞) * π j) := by
  obtain ⟨hpos, h1, hbal⟩ := hπ
  have hcT : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hc0' : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc0
  -- the balance equation of the altered process at `j ∈ A`
  have hin : ∀ B : ℝ≥0∞, ∀ j ∈ A,
      ((fun j => if j ∈ A then B * π j else B * (c : ℝ≥0∞) * π j) j *
          ∑' k, scaleOutward q A c j k =
        ∑' k, (fun j => if j ∈ A then B * π j else B * (c : ℝ≥0∞) * π j) k *
          scaleOutward q A c k j) ↔
      B * ((c : ℝ≥0∞) * (π j * ∑' k : ↥Aᶜ, q j k) + π j * ∑' k : A, q j k) =
        B * ((c : ℝ≥0∞) * ∑' k : ↥Aᶜ, π k * q k j + ∑' k : A, π k * q k j) := by
    intro B j hj
    simp only [hj, if_true]
    rw [split A (fun k => scaleOutward q A c j k),
      split A (fun k => (if k ∈ A then B * π k else B * (c : ℝ≥0∞) * π k) *
        scaleOutward q A c k j)]
    have e1 : ∑' k : A, scaleOutward q A c j k = ∑' k : A, q j k := by
      congr 1; ext k; simp [scaleOutward, k.2]
    have e2 : ∑' k : ↥Aᶜ, scaleOutward q A c j k = (c : ℝ≥0∞) * ∑' k : ↥Aᶜ, q j k := by
      rw [← ENNReal.tsum_mul_left]; congr 1; ext k; have := k.2
      simp only [Set.mem_compl_iff] at this; simp [scaleOutward, hj, this]
    have e3 : ∑' k : A, (if (k : S) ∈ A then B * π k else B * (c : ℝ≥0∞) * π k) *
        scaleOutward q A c k j = B * ∑' k : A, π k * q k j := by
      rw [← ENNReal.tsum_mul_left]; congr 1; ext k; simp [scaleOutward, k.2, hj]; ring
    have e4 : ∑' k : ↥Aᶜ, (if (k : S) ∈ A then B * π k else B * (c : ℝ≥0∞) * π k) *
        scaleOutward q A c k j = B * ((c : ℝ≥0∞) * ∑' k : ↥Aᶜ, π k * q k j) := by
      rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]; congr 1; ext k; have := k.2
      simp only [Set.mem_compl_iff] at this; simp [scaleOutward, this]; ring
    rw [e1, e2, e3, e4]
    constructor <;> intro h <;> convert h using 1 <;> ring
  -- the balance equation of the altered process at `j ∉ A` always holds
  have hout : ∀ B : ℝ≥0∞, ∀ j ∉ A,
      (fun j => if j ∈ A then B * π j else B * (c : ℝ≥0∞) * π j) j *
          ∑' k, scaleOutward q A c j k =
        ∑' k, (fun j => if j ∈ A then B * π j else B * (c : ℝ≥0∞) * π j) k *
          scaleOutward q A c k j := by
    intro B j hj
    simp only [hj, if_false]
    have e1 : ∀ k, scaleOutward q A c j k = q j k := fun k => by simp [scaleOutward, hj]
    have e2 : ∀ k, (if k ∈ A then B * π k else B * (c : ℝ≥0∞) * π k) * scaleOutward q A c k j =
        B * (c : ℝ≥0∞) * (π k * q k j) := fun k => by
      by_cases hk : k ∈ A
      · simp [scaleOutward, hk, hj]; ring
      · simp [scaleOutward, hk]; ring
    simp only [e1, e2]
    rw [ENNReal.tsum_mul_left, ← hbal j]; ring
  have hcancel : ∀ j ∈ A, ((c : ℝ≥0∞) * (π j * ∑' k : ↥Aᶜ, q j k) + π j * ∑' k : A, q j k =
        (c : ℝ≥0∞) * ∑' k : ↥Aᶜ, π k * q k j + ∑' k : A, π k * q k j) ↔
      (π j * ∑' k : A, q j k = ∑' k : A, π k * q k j) := by
    intro j _
    have hs := global_split q π A j (hbal j)
    have hf := global_fin q π A j (hqf j) (pi_ne_top π h1 j)
    rw [key _ _ _ _ c hc1 (by rwa [add_comm]) (by rw [add_comm, hs, add_comm])]
    constructor
    · intro h; have := congrArg (fun x => x - π j * ∑' k : ↥Aᶜ, q j k) hs
      have hb : π j * ∑' k : ↥Aᶜ, q j k ≠ ⊤ := fun h' => hf (by simp [h'])
      rw [ENNReal.add_sub_cancel_right hb, h, ENNReal.add_sub_cancel_right] at this
      · exact this
      · rw [← h]; exact hb
    · intro h; have := congrArg (fun x => x - π j * ∑' k : A, q j k) hs
      have ha : π j * ∑' k : A, q j k ≠ ⊤ := fun h' => hf (by simp [h'])
      rw [ENNReal.add_sub_cancel_left ha, h, ENNReal.add_sub_cancel_left] at this
      · exact this
      · rw [← h]; exact ha
  constructor
  · intro hPB
    obtain ⟨Z, hZ⟩ : ∃ Z, Z = ∑' k : A, π k := ⟨_, rfl⟩
    obtain ⟨W, hW⟩ : ∃ W, W = ∑' k : ↥Aᶜ, π k := ⟨_, rfl⟩
    have hZ0 : Z ≠ 0 := hZ ▸ Z_ne_zero π hpos A hA
    have hD0 : Z + (c : ℝ≥0∞) * W ≠ 0 := fun h => hZ0 (le_antisymm (h ▸ le_self_add) bot_le)
    have hDT : Z + (c : ℝ≥0∞) * W ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨hZ ▸ Z_ne_top π h1 A, ENNReal.mul_ne_top hcT (hW ▸ W_ne_top π h1 A)⟩
    refine ⟨(Z + (c : ℝ≥0∞) * W)⁻¹, fun j => ?_, ?_, fun j => ?_⟩
    · have hB : 0 < (Z + (c : ℝ≥0∞) * W)⁻¹ := ENNReal.inv_pos.2 hDT
      by_cases hj : j ∈ A
      · simp only [hj, if_true]; exact ENNReal.mul_pos hB.ne' (hpos j).ne'
      · simp only [hj, if_false]
        exact ENNReal.mul_pos (ENNReal.mul_pos hB.ne' hc0').ne' (hpos j).ne'
    · rw [split A]
      have e1 : ∑' k : A, (if (k : S) ∈ A then (Z + (c : ℝ≥0∞) * W)⁻¹ * π k
          else (Z + (c : ℝ≥0∞) * W)⁻¹ * (c : ℝ≥0∞) * π k) = (Z + (c : ℝ≥0∞) * W)⁻¹ * Z := by
        rw [hZ, ← ENNReal.tsum_mul_left]; congr 1; ext k; simp [k.2]
      have e2 : ∑' k : ↥Aᶜ, (if (k : S) ∈ A then (Z + (c : ℝ≥0∞) * W)⁻¹ * π k
          else (Z + (c : ℝ≥0∞) * W)⁻¹ * (c : ℝ≥0∞) * π k) =
            (Z + (c : ℝ≥0∞) * W)⁻¹ * ((c : ℝ≥0∞) * W) := by
        rw [hW, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]; congr 1; ext k; have := k.2
        simp only [Set.mem_compl_iff] at this; simp [this]; ring
      rw [e1, e2, ← mul_add]
      exact ENNReal.inv_mul_cancel hD0 hDT
    · by_cases hj : j ∈ A
      · exact (hin _ j hj).2 (congrArg _ ((hcancel j hj).2 (hPB j hj)))
      · exact hout _ j hj
  · rintro ⟨B, hpos', h1', hbal'⟩ j hj
    obtain ⟨a, ha⟩ := hA
    have hBa : 0 < B * π a := by simpa [ha] using hpos' a
    have hB0 : B ≠ 0 := fun h => by simp [h] at hBa
    have hBT : B ≠ ⊤ := by
      intro h
      have := pi_ne_top _ h1' a
      simp only [ha, if_true, h] at this
      exact this (ENNReal.top_mul (hpos a).ne')
    exact (hcancel j hj).1 ((ENNReal.mul_right_inj hB0 hBT).1 ((hin B j hj).1 (hbal' j)))

/-! ### (i) ⇔ (v) -/

theorem part5 {S : Type*} (q : S → S → ℝ≥0∞) (π : S → ℝ≥0∞) (hπ : IsEquilibriumDist q π)
    (A : Set S) (hA : A.Nonempty) :
    IsPartialBalance q π A ↔ ReversalTruncationCommute q π A := by
  have hpos := hπ.1
  have h1 := hπ.2.1
  constructor
  · intro hPB
    refine ⟨condDist π A, (part2 q π hπ A hA).1 hPB, fun j k => ?_⟩
    set Z := ∑' k : A, π k with hZ
    have hZ0 : Z ≠ 0 := Z_ne_zero π hpos A hA
    have hZT : Z ≠ ⊤ := Z_ne_top π h1 A
    simp only [reversedRates, truncRates, condDist, div_eq_mul_inv, ← hZ]
    rw [ENNReal.mul_inv (Or.inl (hpos j).ne') (Or.inl (pi_ne_top π h1 j)), inv_inv]
    calc π k * Z⁻¹ * q k j * ((π j)⁻¹ * Z) = π k * q k j * (π j)⁻¹ * (Z⁻¹ * Z) := by ring
      _ = π k * q k j * (π j)⁻¹ := by rw [ENNReal.inv_mul_cancel hZ0 hZT, mul_one]
  · rintro ⟨μ, ⟨hμpos, hμ1, hμbal⟩, hrev⟩ j hj
    have hμ0 : μ ⟨j, hj⟩ ≠ 0 := (hμpos _).ne'
    have hμT : μ ⟨j, hj⟩ ≠ ⊤ := pi_ne_top μ hμ1 _
    have hπ0 : π j ≠ 0 := (hpos j).ne'
    have hπT : π j ≠ ⊤ := pi_ne_top π h1 j
    have hr : ∀ k : A, π k * q k j = π j * (μ k * q k j / μ ⟨j, hj⟩) := by
      intro k
      have := hrev ⟨j, hj⟩ k
      simp only [reversedRates, truncRates] at this
      rw [this, ENNReal.mul_div_cancel hπ0 hπT]
    have hb := hμbal ⟨j, hj⟩
    simp only [truncRates] at hb
    calc π j * ∑' k : A, q j k
        = π j * ((μ ⟨j, hj⟩ * ∑' k : A, q j k) / μ ⟨j, hj⟩) := by
          rw [mul_comm (μ ⟨j, hj⟩), ENNReal.mul_div_cancel_right hμ0 hμT]
      _ = π j * ∑' k : A, μ k * q k j / μ ⟨j, hj⟩ := by
          rw [hb]; simp_rw [div_eq_mul_inv]; rw [ENNReal.tsum_mul_right]
      _ = ∑' k : A, π k * q k j := by
          rw [← ENNReal.tsum_mul_left]; congr 1; ext k; rw [hr k]

open Classical in
/-- Assembly: (i)⇔(ii)–(v) proved above; (i)⇔(vi) supplied as `hvi`. -/
theorem of_vi {S : Type*} [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (q : S → S → ℝ≥0∞) (hq : IsKellyRates q)
    (π : S → ℝ≥0∞) (hπ : IsEquilibriumDist q π)
    (A : Set S) (hA : A.Nonempty)
    (hvi : fluxOut q π A ≠ ⊤ → (Aᶜ).Nonempty →
      (IsPartialBalance q π A ↔ SameObservedEquilibrium q A)) :
    (IsPartialBalance q π A ↔ IsEquilibriumDist (truncRates q A) (condDist π A)) ∧
    (∀ c : ℝ≥0, c ≠ 0 → c ≠ 1 →
      (IsPartialBalance q π A ↔ IsEquilibriumDist (scaleInside q A c) π)) ∧
    (∀ c : ℝ≥0, c ≠ 0 → c ≠ 1 →
      (IsPartialBalance q π A ↔ ∃ B : ℝ≥0∞, IsEquilibriumDist (scaleOutward q A c)
        (fun j => if j ∈ A then B * π j else B * (c : ℝ≥0∞) * π j))) ∧
    (IsPartialBalance q π A ↔ ReversalTruncationCommute q π A) ∧
    (fluxOut q π A ≠ ⊤ → (Aᶜ).Nonempty →
      (IsPartialBalance q π A ↔ SameObservedEquilibrium q A)) :=
  ⟨part2 q π hπ A hA, fun c _ hc1 => part3 q hq.2.1 π hπ A c hc1,
    fun c hc0 hc1 => part4 q hq.2.1 π hπ A hA c hc0 hc1, part5 q π hπ A hA, hvi⟩

end KPB


open MeasureTheory ProbabilityTheory Finset Preorder Filter Topology
open scoped ENNReal

namespace KPB

open KellyRSN.PartialBalance

variable {S : Type*} [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem jumpKernel_singleton (q : S → S → ℝ≥0∞) (y z : S) :
    jumpKernel q y {z} = jumpProb q y z := by
  show (jumpPMF q y).toMeasure {z} = _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton z)]
  rfl

theorem cyl_meas (n : ℕ) (γ : ℕ → S) :
    MeasurableSet {x : (Π _ : Iic n, S) | ∀ i : Iic n, x i = γ i} := by
  have : {x : (Π _ : Iic n, S) | ∀ i : Iic n, x i = γ i} =
      ⋂ i : Iic n, (fun x : (Π _ : Iic n, S) => x i) ⁻¹' {γ i} := by
    ext x; simp
  rw [this]
  exact MeasurableSet.iInter fun i => measurable_pi_apply i (measurableSet_singleton _)

/-- The jump-chain kernel family used by `jumpChainLaw`. -/
noncomputable abbrev jk (q : S → S → ℝ≥0∞) (n : ℕ) : Kernel (Π _ : Iic n, S) S :=
  (jumpKernel q).comap (fun x : (Π _ : Iic n, S) => x ⟨n, mem_Iic.2 le_rfl⟩)
    (measurable_pi_apply _)

theorem jumpChainLaw_eq (q : S → S → ℝ≥0∞) (j : S) :
    jumpChainLaw q j = Kernel.traj (X := fun _ => S) (jk q) 0 (fun _ => j) := rfl

open Classical in
/-- **Cylinder law of the jump chain.** -/
theorem cylinder (q : S → S → ℝ≥0∞) (j : S) (γ : ℕ → S) : ∀ n : ℕ,
    jumpChainLaw q j {ω | ∀ i ≤ n, ω i = γ i} =
      (if γ 0 = j then 1 else 0) * ∏ i ∈ range n, jumpProb q (γ i) (γ (i + 1))
  | 0 => by
    have hset : {ω : ℕ → S | ∀ i ≤ 0, ω i = γ i} =
        frestrictLe 0 ⁻¹' {x : (Π _ : Iic 0, S) | ∀ i : Iic 0, x i = γ i} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, frestrictLe_apply, Subtype.forall, mem_Iic]
    rw [hset, jumpChainLaw_eq, ← Measure.map_apply (measurable_frestrictLe 0) (cyl_meas 0 γ),
      Kernel.traj_map_frestrictLe_apply, Kernel.partialTraj_self, Kernel.id_apply,
      Measure.dirac_apply' _ (cyl_meas 0 γ)]
    by_cases h : γ 0 = j
    · rw [Set.indicator_of_mem]
      · simp [h]
      · intro i
        have : (i : ℕ) = 0 := Nat.le_zero.1 (mem_Iic.1 i.2)
        simp only
        rw [show γ i = γ 0 from congrArg γ this, h]
    · rw [Set.indicator_of_notMem]
      · simp [h]
      · intro hx
        exact h (hx ⟨0, mem_Iic.2 le_rfl⟩).symm
  | n + 1 => by
    have hset : {ω : ℕ → S | ∀ i ≤ n + 1, ω i = γ i} =
        (fun ω : ℕ → S => (frestrictLe n ω, ω (n + 1))) ⁻¹'
          ({x : (Π _ : Iic n, S) | ∀ i : Iic n, x i = γ i} ×ˢ {γ (n + 1)}) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff,
        frestrictLe_apply, Subtype.forall, mem_Iic]
      constructor
      · intro h
        exact ⟨fun i hi => h i (Nat.le_succ_of_le hi), h (n + 1) le_rfl⟩
      · rintro ⟨h1, h2⟩ i hi
        rcases Nat.le_succ_iff.1 hi with hi | hi
        · exact h1 i hi
        · rw [hi]; exact h2
    have hmeasF : Measurable (fun ω : ℕ → S => (frestrictLe n ω, ω (n + 1))) := by fun_prop
    have hC := cyl_meas n γ
    rw [hset, jumpChainLaw_eq, ← Measure.map_apply hmeasF (hC.prod (measurableSet_singleton _)),
      ← Kernel.partialTraj_compProd_eq_map_traj (Nat.zero_le n),
      Measure.compProd_apply_prod hC (measurableSet_singleton _)]
    have hconst : ∀ x ∈ {x : (Π _ : Iic n, S) | ∀ i : Iic n, x i = γ i},
        jk q n x {γ (n + 1)} = jumpProb q (γ n) (γ (n + 1)) := by
      intro x hx
      rw [Kernel.comap_apply, jumpKernel_singleton, hx ⟨n, mem_Iic.2 le_rfl⟩]
    rw [setLIntegral_congr_fun hC hconst, setLIntegral_const,
      ← Kernel.traj_map_frestrictLe_apply, Measure.map_apply (measurable_frestrictLe n) hC]
    have hset' : frestrictLe n ⁻¹' {x : (Π _ : Iic n, S) | ∀ i : Iic n, x i = γ i} =
        {ω : ℕ → S | ∀ i ≤ n, ω i = γ i} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, frestrictLe_apply, Subtype.forall, mem_Iic]
    rw [hset', ← jumpChainLaw_eq, cylinder q j γ n, prod_range_succ]
    ring



section Mat
variable {T : Type*}

noncomputable def mmul (P Q : T → T → ℝ≥0∞) : T → T → ℝ≥0∞ := fun i j => ∑' k, P i k * Q k j

open Classical in
noncomputable def mone : T → T → ℝ≥0∞ := fun i j => if i = j then 1 else 0

noncomputable def mpow (P : T → T → ℝ≥0∞) : ℕ → T → T → ℝ≥0∞
  | 0 => mone
  | n + 1 => mmul (mpow P n) P

open Classical in
noncomputable def restr (P : T → T → ℝ≥0∞) (R : T → T → Prop) : T → T → ℝ≥0∞ :=
  fun i j => if R i j then P i j else 0

theorem mmul_assoc (P Q R : T → T → ℝ≥0∞) : mmul (mmul P Q) R = mmul P (mmul Q R) := by
  funext i j
  simp only [mmul, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  congr 1; ext k; congr 1; ext l; ring

theorem mone_mmul (P : T → T → ℝ≥0∞) : mmul mone P = P := by
  funext i j
  simp only [mmul, mone, ite_mul, one_mul, zero_mul]
  rw [tsum_eq_single i (fun k hk => by simp [Ne.symm hk])]
  simp

theorem mmul_mone (P : T → T → ℝ≥0∞) : mmul P mone = P := by
  funext i j
  simp only [mmul, mone, mul_ite, mul_one, mul_zero]
  rw [tsum_eq_single j (fun k hk => by simp [hk])]
  simp

theorem mpow_succ' (P : T → T → ℝ≥0∞) : ∀ n, mpow P (n + 1) = mmul P (mpow P n)
  | 0 => by simp only [mpow, mone_mmul, mmul_mone]
  | n + 1 => by
    calc mpow P (n + 1 + 1) = mmul (mpow P (n + 1)) P := rfl
      _ = mmul (mmul P (mpow P n)) P := by rw [mpow_succ' P n]
      _ = mmul P (mmul (mpow P n) P) := mmul_assoc _ _ _
      _ = mmul P (mpow P (n + 1)) := rfl

theorem mpow_rev (m : T → ℝ≥0∞) (P P' : T → T → ℝ≥0∞) (h : ∀ i j, m i * P i j = m j * P' j i) :
    ∀ n i j, m i * mpow P n i j = m j * mpow P' n j i
  | 0, i, j => by
    by_cases hij : i = j
    · subst hij; simp [mpow, mone]
    · simp [mpow, mone, hij, Ne.symm hij]
  | n + 1, i, j => by
    rw [mpow_succ' P' n]
    simp only [mpow, mmul]
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    congr 1; ext k
    calc m i * (mpow P n i k * P k j) = (m i * mpow P n i k) * P k j := by ring
      _ = (m k * mpow P' n k i) * P k j := by rw [mpow_rev m P P' h n i k]
      _ = mpow P' n k i * (m k * P k j) := by ring
      _ = mpow P' n k i * (m j * P' j k) := by rw [h]
      _ = m j * (P' j k * mpow P' n k i) := by ring

theorem restr_rev (m : T → ℝ≥0∞) (P P' : T → T → ℝ≥0∞) (h : ∀ i j, m i * P i j = m j * P' j i)
    (R : T → T → Prop) (i j : T) :
    m i * restr P R i j = m j * restr P' (fun a b => R b a) j i := by
  by_cases hR : R i j
  · simp [restr, hR, h]
  · simp [restr, hR]

theorem green_le (Q : T → T → ℝ≥0∞) (s : T) (v : T → ℝ≥0∞)
    (hv : ∀ y, mone s y + ∑' x, v x * Q x y ≤ v y) :
    ∀ N y, ∑ n ∈ range N, mpow Q n s y ≤ v y
  | 0, y => by simp
  | N + 1, y => by
    rw [sum_range_succ']
    have e : ∑ n ∈ range N, mpow Q (n + 1) s y = ∑' x, (∑ n ∈ range N, mpow Q n s x) * Q x y := by
      simp only [mpow, mmul]
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      congr 1; ext x; rw [Finset.sum_mul]
    calc ∑ n ∈ range N, mpow Q (n + 1) s y + mpow Q 0 s y
        = mone s y + ∑' x, (∑ n ∈ range N, mpow Q n s x) * Q x y := by rw [e, add_comm]; rfl
      _ ≤ mone s y + ∑' x, v x * Q x y :=
          add_le_add le_rfl (ENNReal.tsum_le_tsum fun x =>
            mul_le_mul_of_nonneg_right (green_le Q s v hv N x) (by positivity))
      _ ≤ v y := hv y

theorem avoid_first (P : T → T → ℝ≥0∞) (hrow : ∀ x, ∑' z, P x z = 1) (R : T → T → Prop) (x : T) :
    ∀ N, ∑' z, mpow (restr P R) N x z +
      ∑ n ∈ range N, ∑' y, mpow (restr P R) n x y * ∑' z, restr P (fun a b => ¬ R a b) y z = 1
  | 0 => by
    simp only [mpow, range_zero, sum_empty, add_zero, mone]
    rw [tsum_eq_single x (fun z hz => by simp [Ne.symm hz])]; simp
  | N + 1 => by
    have hsplit : ∀ y, ∑' z, restr P R y z + ∑' z, restr P (fun a b => ¬ R a b) y z = 1 := by
      intro y; rw [← ENNReal.tsum_add, ← hrow y]; congr 1; ext z
      by_cases h : R y z <;> simp [restr, h]
    have hstep : ∑' z, mpow (restr P R) (N + 1) x z +
        ∑' y, mpow (restr P R) N x y * ∑' z, restr P (fun a b => ¬ R a b) y z =
          ∑' z, mpow (restr P R) N x z := by
      simp only [mpow, mmul]
      rw [ENNReal.tsum_comm, ← ENNReal.tsum_add]
      congr 1; ext y
      rw [ENNReal.tsum_mul_left, ← mul_add, hsplit y, mul_one]
    rw [sum_range_succ]
    calc _ = (∑' z, mpow (restr P R) (N + 1) x z +
        ∑' y, mpow (restr P R) N x y * ∑' z, restr P (fun a b => ¬ R a b) y z) +
          ∑ n ∈ range N, ∑' y, mpow (restr P R) n x y *
            ∑' z, restr P (fun a b => ¬ R a b) y z := by ring
      _ = 1 := by rw [hstep, avoid_first P hrow R x N]

theorem first_sum_one (P : T → T → ℝ≥0∞) (hrow : ∀ x, ∑' z, P x z = 1) (R : T → T → Prop) (x : T)
    (h : Tendsto (fun N => ∑' z, mpow (restr P R) N x z) atTop (𝓝 0)) :
    ∑' n, ∑' y, mpow (restr P R) n x y * ∑' z, restr P (fun a b => ¬ R a b) y z = 1 := by
  set f : ℕ → ℝ≥0∞ := fun n => ∑' y, mpow (restr P R) n x y *
    ∑' z, restr P (fun a b => ¬ R a b) y z with hf
  have hS : ∀ N, ∑ n ∈ range N, f n = 1 - ∑' z, mpow (restr P R) N x z := by
    intro N
    have h1 := avoid_first P hrow R x N
    have hne : ∑' z, mpow (restr P R) N x z ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (h1 ▸ le_self_add)
    exact ENNReal.eq_sub_of_add_eq hne (by rw [add_comm]; exact h1)
  have ht1 : Tendsto (fun N => ∑ n ∈ range N, f n) atTop (𝓝 (∑' n, f n)) := ENNReal.tendsto_nat_tsum f
  have ht2 : Tendsto (fun N => ∑ n ∈ range N, f n) atTop (𝓝 (1 - 0)) := by
    simp_rw [hS]
    exact ENNReal.Tendsto.sub tendsto_const_nhds h (Or.inl ENNReal.one_ne_top)
  rw [tsub_zero] at ht2
  exact tendsto_nhds_unique ht1 ht2

/-! ### T2: invariant measures of a recurrent irreducible chain (Norris 1.7.5–1.7.6) -/

theorem inv_pow (P : T → T → ℝ≥0∞) (ρ : T → ℝ≥0∞) (h : ∀ y, ∑' x, ρ x * P x y = ρ y) :
    ∀ n y, ∑' x, ρ x * mpow P n x y = ρ y
  | 0, y => by
    simp only [mpow, mone, mul_ite, mul_one, mul_zero]
    rw [tsum_eq_single y (fun x hx => by simp [hx])]; simp
  | n + 1, y => by
    simp only [mpow, mmul]
    simp_rw [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    simp_rw [← mul_assoc, ENNReal.tsum_mul_right, inv_pow P ρ h n]
    exact h y

theorem inv_zero (P : T → T → ℝ≥0∞) (hirr : ∀ x y, ∃ n, 0 < mpow P n x y) (ρ : T → ℝ≥0∞)
    (hρ : ∀ y, ∑' x, ρ x * P x y = ρ y) (i : T) (h0 : ρ i = 0) (x : T) : ρ x = 0 := by
  obtain ⟨n, hn⟩ := hirr x i
  have := inv_pow P ρ hρ n i
  rw [h0] at this
  have hle : ρ x * mpow P n x i ≤ 0 := le_of_le_of_eq (ENNReal.le_tsum x) this
  rcases mul_eq_zero.1 (nonpos_iff_eq_zero.1 hle) with h | h
  · exact h
  · exact absurd h hn.ne'

/-- expected visits to `y` before returning to `i` (Norris `γ^i`) -/
noncomputable def gam (P : T → T → ℝ≥0∞) (i y : T) : ℝ≥0∞ :=
  ∑' n, mpow (restr P (fun _ b => b ≠ i)) n i y

theorem gam_self (P : T → T → ℝ≥0∞) (i : T) : gam P i i = 1 := by
  unfold gam
  rw [tsum_eq_single 0]
  · simp [mpow, mone]
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simp [mpow, mmul, restr]

theorem gam_off (P : T → T → ℝ≥0∞) (i y : T) (hy : y ≠ i) :
    gam P i y = ∑' x, gam P i x * P x y := by
  unfold gam
  conv_lhs => rw [tsum_eq_zero_add' ENNReal.summable]
  have h0 : mpow (restr P (fun _ b => b ≠ i)) 0 i y = 0 := by simp [mpow, mone, Ne.symm hy]
  rw [h0, zero_add]
  simp only [mpow, mmul]
  rw [ENNReal.tsum_comm]
  congr 1; ext x
  rw [← ENNReal.tsum_mul_right]
  congr 1; ext n
  simp [restr, hy]

theorem gam_inv (P : T → T → ℝ≥0∞) (hrow : ∀ x, ∑' z, P x z = 1) (i : T)
    (hret : Tendsto (fun N => ∑' z, mpow (restr P (fun _ b => b ≠ i)) N i z) atTop (𝓝 0)) :
    ∀ y, ∑' x, gam P i x * P x y = gam P i y := by
  intro y
  by_cases hy : y = i
  · subst hy
    rw [gam_self]
    have h := first_sum_one P hrow _ y hret
    have e : ∀ x, ∑' z, restr P (fun a b => ¬ (fun _ b => b ≠ y) a b) x z = P x y := by
      intro x
      rw [tsum_eq_single y (fun z hz => by simp [restr, hz])]
      simp [restr]
    simp_rw [e] at h
    rw [← h, ENNReal.tsum_comm]
    unfold gam
    congr 1; ext x
    rw [ENNReal.tsum_mul_right]
  · exact (gam_off P i y hy).symm

/-- **T2.** Every finite invariant measure of a recurrent irreducible stochastic matrix is
`λ i • γ^i`. -/
theorem R2 (P : T → T → ℝ≥0∞) (hrow : ∀ x, ∑' z, P x z = 1)
    (hirr : ∀ x y, ∃ n, 0 < mpow P n x y) (i : T)
    (hret : Tendsto (fun N => ∑' z, mpow (restr P (fun _ b => b ≠ i)) N i z) atTop (𝓝 0))
    (lam : T → ℝ≥0∞) (hlam : ∀ y, ∑' x, lam x * P x y = lam y) (hlamT : ∀ y, lam y ≠ ⊤) :
    ∀ y, lam y = lam i * gam P i y := by
  by_cases h0 : lam i = 0
  · intro y; rw [h0, zero_mul]; exact inv_zero P hirr lam hlam i h0 y
  have hle : ∀ y, lam i * gam P i y ≤ lam y := by
    intro y
    have hv : ∀ y, mone i y + ∑' x, ((lam i)⁻¹ * lam x) * restr P (fun _ b => b ≠ i) x y ≤
        (lam i)⁻¹ * lam y := by
      intro y
      by_cases hy : y = i
      · subst hy
        have : ∀ x, restr P (fun _ b => b ≠ y) x y = 0 := fun x => by simp [restr]
        simp only [this, mul_zero, tsum_zero, add_zero, mone, if_true]
        rw [ENNReal.inv_mul_cancel h0 (hlamT _)]
      · have : ∀ x, restr P (fun _ b => b ≠ i) x y = P x y := fun x => by simp [restr, hy]
        simp only [this, mone, Ne.symm hy, if_false, zero_add]
        simp_rw [mul_assoc]
        rw [ENNReal.tsum_mul_left]
        exact le_of_eq (congrArg _ (hlam y))
    have hg : gam P i y ≤ (lam i)⁻¹ * lam y :=
      ENNReal.tsum_le_of_sum_range_le fun N => green_le _ i _ hv N y
    calc lam i * gam P i y ≤ lam i * ((lam i)⁻¹ * lam y) := by gcongr
      _ = lam y := by rw [← mul_assoc, ENNReal.mul_inv_cancel h0 (hlamT i), one_mul]
  set ρ : T → ℝ≥0∞ := fun y => lam y - lam i * gam P i y with hρdef
  have hsum : ∀ y, lam y = lam i * gam P i y + ρ y := fun y => (add_tsub_cancel_of_le (hle y)).symm
  have hgT : ∀ y, lam i * gam P i y ≠ ⊤ := fun y => ne_top_of_le_ne_top (hlamT y) (hle y)
  have hρinv : ∀ y, ∑' x, ρ x * P x y = ρ y := by
    intro y
    have e : lam i * gam P i y + ∑' x, ρ x * P x y = lam i * gam P i y + ρ y := by
      calc lam i * gam P i y + ∑' x, ρ x * P x y
          = ∑' x, (lam i * gam P i x) * P x y + ∑' x, ρ x * P x y := by
            rw [← gam_inv P hrow i hret y]; simp_rw [mul_assoc]; rw [ENNReal.tsum_mul_left]
        _ = ∑' x, (lam i * gam P i x + ρ x) * P x y := by
            rw [← ENNReal.tsum_add]; simp_rw [add_mul]
        _ = ∑' x, lam x * P x y := by simp_rw [← hsum]
        _ = lam y := hlam y
        _ = lam i * gam P i y + ρ y := hsum y
    exact (ENNReal.add_right_inj (hgT y)).1 e
  have hρi : ρ i = 0 := by simp [hρdef, gam_self]
  intro y
  rw [hsum y, inv_zero P hirr ρ hρinv i hρi y, add_zero]

/-! ### T3: reversal turns `λ = λ_i γ^i` into hitting probabilities of the reversed chain -/

theorem rev_hit (m : T → ℝ≥0∞) (hm0 : ∀ x, m x ≠ 0) (hmT : ∀ x, m x ≠ ⊤)
    (P P' : T → T → ℝ≥0∞) (h : ∀ i j, m i * P i j = m j * P' j i)
    (hR2 : ∀ i y, m y = m i * gam P i y) (i y : T) :
    ∑' n, mpow (restr P' (fun a _ => a ≠ i)) n y i = 1 := by
  have e : ∀ n, m i * mpow (restr P (fun _ b => b ≠ i)) n i y =
      m y * mpow (restr P' (fun a _ => a ≠ i)) n y i :=
    fun n => mpow_rev m _ _ (fun a b => restr_rev m P P' h (fun _ b => b ≠ i) a b) n i y
  have := hR2 i y
  rw [gam, ← ENNReal.tsum_mul_left] at this
  simp_rw [e, ENNReal.tsum_mul_left] at this
  exact (ENNReal.mul_right_inj (hm0 y) (hmT y)).1 (this.symm.trans (mul_one _).symm)

/-! ### T4: a chain that hits every state almost surely makes any positive transition -/

/-- row sums of the `N`-th power -/
noncomputable def usum (Q : T → T → ℝ≥0∞) (N : ℕ) (x : T) : ℝ≥0∞ := ∑' z, mpow Q N x z

theorem usum_zero (Q : T → T → ℝ≥0∞) (x : T) : usum Q 0 x = 1 := by
  unfold usum
  simp only [mpow, mone]
  rw [tsum_eq_single x (fun z hz => by simp [Ne.symm hz])]; simp

theorem usum_succ (Q : T → T → ℝ≥0∞) (N : ℕ) (x : T) :
    usum Q (N + 1) x = ∑' z, Q x z * usum Q N z := by
  unfold usum
  rw [mpow_succ']
  simp only [mmul]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]

theorem usum_succ_right (Q : T → T → ℝ≥0∞) (N : ℕ) (x : T) :
    usum Q (N + 1) x = ∑' y, mpow Q N x y * ∑' z, Q y z := by
  unfold usum
  simp only [mpow, mmul]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]

theorem usum_anti (Q : T → T → ℝ≥0∞) (hQ : ∀ y, ∑' z, Q y z ≤ 1) (x : T) :
    Antitone (fun N => usum Q N x) := by
  refine antitone_nat_of_succ_le fun N => ?_
  rw [usum_succ_right]
  exact ENNReal.tsum_le_tsum fun y => mul_le_of_le_one_right (by positivity) (hQ y)

theorem usum_le_one (Q : T → T → ℝ≥0∞) (hQ : ∀ y, ∑' z, Q y z ≤ 1) (N : ℕ) (x : T) :
    usum Q N x ≤ 1 := (usum_zero Q x) ▸ usum_anti Q hQ x (Nat.zero_le N)

theorem restr_le (P : T → T → ℝ≥0∞) (R : T → T → Prop) (x z : T) : restr P R x z ≤ P x z := by
  unfold restr; split_ifs <;> simp

theorem restr_row (P : T → T → ℝ≥0∞) (hrow : ∀ x, ∑' z, P x z = 1) (R : T → T → Prop) (y : T) :
    ∑' z, restr P R y z ≤ 1 := (hrow y) ▸ ENNReal.tsum_le_tsum fun z => restr_le P R y z

open Classical in
/-- source-taboo identity: avoid `a` at times `0..M-1`, or first visit at `t < M`. -/
theorem avoid_src (P : T → T → ℝ≥0∞) (hrow : ∀ x, ∑' z, P x z = 1) (a x : T) :
    ∀ M, usum (restr P (fun y _ => y ≠ a)) M x +
      ∑ t ∈ range M, mpow (restr P (fun y _ => y ≠ a)) t x a = 1
  | 0 => by simp [usum_zero]
  | M + 1 => by
    have hrowA : ∀ y, ∑' z, restr P (fun y _ => y ≠ a) y z = if y = a then 0 else 1 := by
      intro y; by_cases hy : y = a
      · simp [restr, hy]
      · simp [restr, hy, hrow y]
    have hstep : usum (restr P (fun y _ => y ≠ a)) (M + 1) x +
        mpow (restr P (fun y _ => y ≠ a)) M x a = usum (restr P (fun y _ => y ≠ a)) M x := by
      rw [usum_succ_right]
      simp_rw [hrowA]
      have e : ∀ y, mpow (restr P (fun y _ => y ≠ a)) M x y * (if y = a then (0 : ℝ≥0∞) else 1) =
          if y = a then 0 else mpow (restr P (fun y _ => y ≠ a)) M x y := by
        intro y; split_ifs <;> simp
      simp_rw [e]
      unfold usum
      rw [ENNReal.tsum_eq_add_tsum_ite a (f := fun y => mpow (restr P (fun y _ => y ≠ a)) M x y),
        add_comm]
    rw [sum_range_succ]
    calc _ = (usum (restr P (fun y _ => y ≠ a)) (M + 1) x + mpow (restr P (fun y _ => y ≠ a)) M x a) +
          ∑ t ∈ range M, mpow (restr P (fun y _ => y ≠ a)) t x a := by ring
      _ = 1 := by rw [hstep, avoid_src P hrow a x M]

theorem sum_src_le (P : T → T → ℝ≥0∞) (hrow : ∀ x, ∑' z, P x z = 1) (a x : T) (M : ℕ) :
    ∑ t ∈ range M, mpow (restr P (fun y _ => y ≠ a)) t x a ≤ 1 :=
  (avoid_src P hrow a x M) ▸ le_add_self

/-- **Decomposition at the first visit to `a`.** -/
theorem decomp (P : T → T → ℝ≥0∞) (hrow : ∀ x, ∑' z, P x z = 1) (R : T → T → Prop) (a : T) :
    ∀ M N x, usum (restr P R) (N + M) x ≤ usum (restr P (fun y _ => y ≠ a)) M x +
      (∑ t ∈ range M, mpow (restr P (fun y _ => y ≠ a)) t x a) * usum (restr P R) N a
  | 0, N, x => by
    refine le_trans (usum_le_one _ (restr_row P hrow R) N x) ?_
    simp [usum_zero]
  | M + 1, N, x => by
    have IH := decomp P hrow R a M N
    set A := restr P (fun y _ => y ≠ a) with hAdef
    set Q := restr P R with hQdef
    set u := usum Q N a with hudef
    by_cases hx : x = a
    · subst hx
      have h1 : usum Q (N + (M + 1)) x ≤ u :=
        usum_anti _ (restr_row P hrow R) x (by omega)
      refine le_trans h1 (le_trans ?_ le_add_self)
      have h2 : (1 : ℝ≥0∞) ≤ ∑ t ∈ range (M + 1), mpow A t x x := by
        rw [sum_range_succ']
        have : mpow A 0 x x = 1 := by simp [mpow, mone]
        rw [this]; exact le_add_self
      calc u = 1 * u := (one_mul _).symm
        _ ≤ _ := mul_le_mul' h2 le_rfl
    · show usum Q (N + M + 1) x ≤ _
      rw [usum_succ]
      have hA : ∀ z, A x z = P x z := fun z => by simp [hAdef, restr, hx]
      have hpow : ∀ t, mpow A (t + 1) x a = ∑' z, A x z * mpow A t z a := fun t => by
        rw [mpow_succ']; rfl
      calc ∑' z, Q x z * usum Q (N + M) z
          ≤ ∑' z, A x z * (usum A M z + (∑ t ∈ range M, mpow A t z a) * u) := by
            refine ENNReal.tsum_le_tsum fun z => ?_
            rw [hA z]
            exact mul_le_mul' (restr_le P R x z) (IH z)
        _ = usum A (M + 1) x + (∑ t ∈ range M, mpow A (t + 1) x a) * u := by
            rw [usum_succ]
            simp_rw [mul_add]
            rw [ENNReal.tsum_add]
            congr 1
            simp_rw [hpow]
            rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← ENNReal.tsum_mul_right]
            congr 1; ext z
            rw [← Finset.mul_sum, mul_assoc]
        _ ≤ usum A (M + 1) x + (∑ t ∈ range (M + 1), mpow A t x a) * u := by
            refine add_le_add le_rfl (mul_le_mul' ?_ le_rfl)
            rw [sum_range_succ' (fun t => mpow A t x a)]
            exact le_self_add

open Classical in
/-- **T4.** If the chain hits `a` from everywhere and `P a b > 0` with `¬ R a b`, the
probability of making only `R`-transitions for `N` steps tends to `0`. -/
theorem T4 (P : T → T → ℝ≥0∞) (hrow : ∀ x, ∑' z, P x z = 1) (a b : T) (hab : 0 < P a b)
    (hhit : ∀ x, ∑' t, mpow (restr P (fun y _ => y ≠ a)) t x a = 1)
    (R : T → T → Prop) (hR : ¬ R a b) (x : T) :
    Tendsto (fun N => usum (restr P R) N x) atTop (𝓝 0) := by
  set A := restr P (fun y _ => y ≠ a) with hAdef
  set Q := restr P R with hQdef
  have hα : ∀ z, Tendsto (fun M => usum A M z) atTop (𝓝 0) := by
    intro z
    have hS : Tendsto (fun M => ∑ t ∈ range M, mpow A t z a) atTop (𝓝 1) := by
      rw [← hhit z]; exact ENNReal.tendsto_nat_tsum _
    have e : ∀ M, usum A M z = 1 - ∑ t ∈ range M, mpow A t z a := fun M =>
      ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top (sum_src_le P hrow a z M))
        (avoid_src P hrow a z M)
    simp_rw [e]
    have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞))) hS (Or.inl ENNReal.one_ne_top)
    rwa [tsub_self] at this
  have hr : Tendsto (fun M => ∑' z, P a z * usum A M z) atTop (𝓝 0) := by
    set c : ℕ → ℝ≥0∞ := fun t => ∑' z, P a z * mpow A t z a with hcdef
    have hc : ∑' t, c t = 1 := by
      simp only [hcdef]; rw [ENNReal.tsum_comm]
      simp_rw [ENNReal.tsum_mul_left, hhit, mul_one]; exact hrow a
    have hid : ∀ M, ∑' z, P a z * usum A M z + ∑ t ∈ range M, c t = 1 := by
      intro M
      simp only [hcdef]
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← ENNReal.tsum_add]
      simp_rw [← Finset.mul_sum, ← mul_add,
        show ∀ z, usum A M z + ∑ t ∈ range M, mpow A t z a = 1 from fun z => avoid_src P hrow a z M,
        mul_one]
      exact hrow a
    have hS : Tendsto (fun M => ∑ t ∈ range M, c t) atTop (𝓝 1) := by
      rw [← hc]; exact ENNReal.tendsto_nat_tsum _
    have e : ∀ M, ∑' z, P a z * usum A M z = 1 - ∑ t ∈ range M, c t := fun M =>
      ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top ((hid M) ▸ le_add_self))
        (hid M)
    simp_rw [e]
    have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞))) hS (Or.inl ENNReal.one_ne_top)
    rwa [tsub_self] at this
  have hanti : ∀ z, Antitone (fun N => usum Q N z) := fun z => usum_anti Q (restr_row P hrow R) z
  set L := ⨅ N, usum Q N a with hL
  have hLt : Tendsto (fun N => usum Q N a) atTop (𝓝 L) := tendsto_atTop_iInf (hanti a)
  have hc1 : P a b ≤ 1 := (hrow a) ▸ ENNReal.le_tsum b
  have hPab : P a b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hc1
  have hQa : ∑' z, Q a z ≤ 1 - P a b := by
    refine ENNReal.le_sub_of_add_le_right hPab ?_
    rw [← hrow a, ENNReal.tsum_eq_add_tsum_ite b (f := fun z => P a z), add_comm]
    refine add_le_add le_rfl (ENNReal.tsum_le_tsum fun z => ?_)
    by_cases hz : z = b
    · subst hz; simp [hQdef, restr, hR]
    · rw [if_neg hz]; exact restr_le P R a z
  have hkey : ∀ N M, usum Q (N + M + 1) a ≤
      ∑' z, P a z * usum A M z + (1 - P a b) * usum Q N a := by
    intro N M
    rw [usum_succ]
    calc ∑' z, Q a z * usum Q (N + M) z
        ≤ ∑' z, Q a z * (usum A M z + usum Q N a) := by
          refine ENNReal.tsum_le_tsum fun z => mul_le_mul' le_rfl ?_
          refine le_trans (decomp P hrow R a M N z) (add_le_add le_rfl ?_)
          calc (∑ t ∈ range M, mpow A t z a) * usum Q N a ≤ 1 * usum Q N a :=
                mul_le_mul' (sum_src_le P hrow a z M) le_rfl
            _ = usum Q N a := one_mul _
      _ = ∑' z, Q a z * usum A M z + (∑' z, Q a z) * usum Q N a := by
          simp_rw [mul_add]; rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
      _ ≤ _ := add_le_add (ENNReal.tsum_le_tsum fun z => mul_le_mul' (restr_le P R a z) le_rfl)
          (mul_le_mul' hQa le_rfl)
  have hL1 : ∀ N, L ≤ (1 - P a b) * usum Q N a := by
    intro N
    have ht : Tendsto (fun M => ∑' z, P a z * usum A M z + (1 - P a b) * usum Q N a) atTop
        (𝓝 (0 + (1 - P a b) * usum Q N a)) := hr.add tendsto_const_nhds
    rw [zero_add] at ht
    exact ge_of_tendsto' ht fun M => le_trans (iInf_le _ (N + M + 1)) (hkey N M)
  have hL2 : L ≤ (1 - P a b) * L := by
    have ht : Tendsto (fun N => (1 - P a b) * usum Q N a) atTop (𝓝 ((1 - P a b) * L)) :=
      ENNReal.Tendsto.const_mul hLt (Or.inr (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self))
    exact ge_of_tendsto' ht hL1
  have hLT : L ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans (iInf_le _ 0) (le_of_eq (usum_zero Q a)))
  have hL0 : L = 0 := by
    have h1 : L + P a b * L ≤ L + 0 := by
      calc L + P a b * L ≤ (1 - P a b) * L + P a b * L := add_le_add hL2 le_rfl
        _ = L := by rw [← add_mul, tsub_add_cancel_of_le hc1, one_mul]
        _ = L + 0 := (add_zero _).symm
    have h2 := ENNReal.le_of_add_le_add_left hLT h1
    rcases mul_eq_zero.1 (nonpos_iff_eq_zero.1 h2) with h | h
    · exact absurd h hab.ne'
    · exact h
  have hbx : ∀ N M, usum Q (N + M) x ≤ usum A M x + usum Q N a := fun N M =>
    le_trans (decomp P hrow R a M N x) (add_le_add le_rfl
      (le_trans (mul_le_mul' (sum_src_le P hrow a x M) le_rfl) (one_mul _).le))
  have hle : ⨅ K, usum Q K x ≤ L := by
    refine le_iInf fun N => ?_
    have ht : Tendsto (fun M => usum A M x + usum Q N a) atTop (𝓝 (0 + usum Q N a)) :=
      (hα x).add tendsto_const_nhds
    rw [zero_add] at ht
    exact ge_of_tendsto' ht fun M => le_trans (iInf_le _ (N + M)) (hbx N M)
  rw [hL0] at hle
  have := tendsto_atTop_iInf (hanti x)
  rwa [nonpos_iff_eq_zero.1 hle] at this

/-- **T5: cycle representation.** If the reversed chain killed at reversed `D`-transitions
dies out, the invariant measure equals the expected occupation between `D`-transitions. -/
theorem T5 (P P' : T → T → ℝ≥0∞) (m : T → ℝ≥0∞) (hmT : ∀ x, m x ≠ ⊤)
    (h : ∀ i j, m i * P i j = m j * P' j i) (hinv : ∀ y, ∑' x, m x * P x y = m y)
    (D : T → T → Prop)
    (hlim : ∀ y, Tendsto (fun N => usum (restr P' (fun a b => ¬ D b a)) N y) atTop (𝓝 0)) (y : T) :
    ∑' x, (∑' z, m z * restr P D z x) * ∑' n, mpow (restr P (fun a b => ¬ D a b)) n x y = m y := by
  set Q := restr P (fun a b => ¬ D a b) with hQ
  set φ : T → ℝ≥0∞ := fun x => ∑' z, m z * restr P D z x with hφ
  have hsplit : ∀ y, ∑' x, m x * Q x y + φ y = m y := by
    intro y
    rw [hφ, ← ENNReal.tsum_add, ← hinv y]
    congr 1; ext x
    rw [← mul_add]; congr 1
    by_cases hD : D x y <;> simp [hQ, restr, hD]
  have hid : ∀ N y, m y = ∑' x, m x * mpow Q N x y +
      ∑ n ∈ range N, ∑' x, φ x * mpow Q n x y := by
    intro N
    induction N with
    | zero =>
      intro y
      simp only [mpow, mone, mul_ite, mul_one, mul_zero, range_zero, sum_empty, add_zero]
      rw [tsum_eq_single y (fun x hx => by simp [hx])]; simp
    | succ N ih =>
      intro y
      have key : ∑' x, m x * mpow Q N x y =
          ∑' z, m z * mpow Q (N + 1) z y + ∑' x, φ x * mpow Q N x y := by
        calc ∑' x, m x * mpow Q N x y
            = ∑' x, (∑' z, m z * Q z x + φ x) * mpow Q N x y := by
              congr 1; ext x; rw [hsplit x]
          _ = ∑' z, m z * mpow Q (N + 1) z y + ∑' x, φ x * mpow Q N x y := by
              simp_rw [add_mul]
              rw [ENNReal.tsum_add]
              congr 1
              rw [mpow_succ']
              simp only [mmul]
              simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
              rw [ENNReal.tsum_comm]
              congr 1; ext z; congr 1; ext x; ring
      rw [ih y, sum_range_succ, key]; ring
  have hrev : ∀ N, ∑' x, m x * mpow Q N x y =
      m y * usum (restr P' (fun a b => ¬ D b a)) N y := by
    intro N
    unfold usum
    rw [← ENNReal.tsum_mul_left]
    congr 1; ext x
    exact mpow_rev m _ _ (fun a b => restr_rev m P P' h (fun a b => ¬ D a b) a b) N x y
  set f : ℕ → ℝ≥0∞ := fun n => ∑' x, φ x * mpow Q n x y with hf
  have ht : Tendsto (fun N => m y * usum (restr P' (fun a b => ¬ D b a)) N y +
      ∑ n ∈ range N, f n) atTop (𝓝 (m y * 0 + ∑' n, f n)) :=
    (ENNReal.Tendsto.const_mul (hlim y) (Or.inr (hmT y))).add (ENNReal.tendsto_nat_tsum f)
  have hc : (fun N => m y * usum (restr P' (fun a b => ¬ D b a)) N y + ∑ n ∈ range N, f n) =
      fun _ => m y := by
    funext N; rw [← hrev N]; exact (hid N y).symm
  rw [hc, mul_zero, zero_add] at ht
  have e := tendsto_nhds_unique tendsto_const_nhds ht
  rw [e, hf, ENNReal.tsum_comm]
  congr 1; ext x
  rw [ENNReal.tsum_mul_left]


/-! ### T6–T8: lift of a stationary law, uniqueness, exit/entry stationarity, cut balance -/

/-- Green function of a substochastic matrix -/
noncomputable def grn (Q : T → T → ℝ≥0∞) (x y : T) : ℝ≥0∞ := ∑' n, mpow Q n x y

/-- the measure `φ G` -/
noncomputable def lift (Q : T → T → ℝ≥0∞) (φ : T → ℝ≥0∞) (y : T) : ℝ≥0∞ :=
  ∑' x, φ x * grn Q x y

theorem lift_smul (Q : T → T → ℝ≥0∞) (φ : T → ℝ≥0∞) (c : ℝ≥0∞) (y : T) :
    lift Q (fun x => c * φ x) y = c * lift Q φ y := by
  simp only [lift]
  simp_rw [mul_assoc]
  exact ENNReal.tsum_mul_left

theorem sw {ι κ : Type*} (f : ι → ℝ≥0∞) (g : ι → κ → ℝ≥0∞) (h : κ → ℝ≥0∞) :
    ∑' j, f j * ∑' k, g j k * h k = ∑' k, (∑' j, f j * g j k) * h k := by
  simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  congr 1; ext k; congr 1; ext j; ring

theorem grn_id (Q : T → T → ℝ≥0∞) (x w : T) :
    grn Q x w = mone x w + ∑' y, grn Q x y * Q y w := by
  unfold grn
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [mpow, mmul]
  congr 1
  rw [ENNReal.tsum_comm]
  congr 1; ext y
  rw [ENNReal.tsum_mul_right]

theorem lift_inv (P : T → T → ℝ≥0∞) (D : T → T → Prop) (φ : T → ℝ≥0∞)
    (hφ : ∀ w, ∑' y, lift (restr P (fun a b => ¬ D a b)) φ y * restr P D y w = φ w) (w : T) :
    ∑' y, lift (restr P (fun a b => ¬ D a b)) φ y * P y w =
      lift (restr P (fun a b => ¬ D a b)) φ w := by
  set Q := restr P (fun a b => ¬ D a b) with hQ
  have hP : ∀ y, P y w = Q y w + restr P D y w := fun y => by
    by_cases h : D y w <;> simp [hQ, restr, h]
  have h1 : lift Q φ w = φ w + ∑' y, lift Q φ y * Q y w := by
    unfold lift
    simp_rw [grn_id Q _ w, mul_add]
    rw [ENNReal.tsum_add,
      sw φ (fun x y => grn Q x y) (fun y => Q y w)]
    congr 1
    rw [tsum_eq_single w (fun x hx => by simp [mone, hx])]
    simp [mone]
  calc ∑' y, lift Q φ y * P y w = ∑' y, lift Q φ y * Q y w + φ w := by
        simp_rw [hP, mul_add]; rw [ENNReal.tsum_add, hφ w]
    _ = lift Q φ w := by rw [h1, add_comm]

theorem inv_fin (P : T → T → ℝ≥0∞) (hirr : ∀ x y, ∃ n, 0 < mpow P n x y) (ρ : T → ℝ≥0∞)
    (hρ : ∀ y, ∑' x, ρ x * P x y = ρ y) (i : T) (hi : ρ i ≠ ⊤) (x : T) : ρ x ≠ ⊤ := by
  obtain ⟨n, hn⟩ := hirr x i
  have hle : ρ x * mpow P n x i ≤ ρ i :=
    (inv_pow P ρ hρ n i) ▸ ENNReal.le_tsum (f := fun x => ρ x * mpow P n x i) x
  intro hx
  rw [hx, ENNReal.top_mul hn.ne'] at hle
  exact hi (top_le_iff.1 hle)

theorem prop_m (P : T → T → ℝ≥0∞) (hrow : ∀ x, ∑' z, P x z = 1)
    (hirr : ∀ x y, ∃ n, 0 < mpow P n x y) (i : T)
    (hret : Tendsto (fun N => ∑' z, mpow (restr P (fun _ b => b ≠ i)) N i z) atTop (𝓝 0))
    (m : T → ℝ≥0∞) (hm : ∀ y, ∑' x, m x * P x y = m y) (hmT : ∀ y, m y ≠ ⊤) (hm0 : m i ≠ 0)
    (μ : T → ℝ≥0∞) (hμ : ∀ y, ∑' x, μ x * P x y = μ y) (hμT : ∀ y, μ y ≠ ⊤) :
    ∀ y, μ y = μ i / m i * m y := by
  intro y
  rw [R2 P hrow hirr i hret μ hμ hμT y, R2 P hrow hirr i hret m hm hmT y, div_eq_mul_inv,
    mul_assoc, ← mul_assoc (m i)⁻¹, ENNReal.inv_mul_cancel hm0 (hmT i), one_mul]

theorem sub_eq (B : Set T) (f : T → ℝ≥0∞) (hf : ∀ x, x ∉ B → f x = 0) :
    ∑' x : B, f x = ∑' x, f x :=
  tsum_subtype_eq_of_support_subset (fun x hx => by
    by_contra h
    exact hx (hf x h))

open Classical in
/-- extension by zero of a function on `B` -/
noncomputable def extB (B : Set T) (ν : B → ℝ≥0∞) (x : T) : ℝ≥0∞ :=
  if h : x ∈ B then ν ⟨x, h⟩ else 0

theorem sub_ext (B : Set T) (ν : B → ℝ≥0∞) (g : T → ℝ≥0∞) :
    ∑' j : B, ν j * g j = ∑' x, extB B ν x * g x := by
  rw [← sub_eq B (fun x => extB B ν x * g x) (fun x hx => by simp [extB, hx])]
  congr 1; ext j; simp [extB, j.2]

theorem mpow_restr_eq (P : T → T → ℝ≥0∞) (R R1 : T → T → Prop) (C : Set T)
    (hRC : ∀ a b, b ∈ C → (R a b ↔ R1 a b)) (hR1 : ∀ a b, R1 a b → a ∈ C) :
    ∀ n x y, y ∈ C → mpow (restr P R) n x y = mpow (restr P R1) n x y
  | 0, x, y, _ => rfl
  | n + 1, x, y, hy => by
    simp only [mpow, mmul]
    congr 1; ext k
    have e : restr P R k y = restr P R1 k y := by
      classical
      unfold restr; exact if_congr (hRC k y hy) rfl rfl
    rw [e]
    by_cases hk : R1 k y
    · rw [mpow_restr_eq P R R1 C hRC hR1 n x k (hR1 k y hk)]
    · simp [restr, hk]

theorem first_le_one (P : T → T → ℝ≥0∞) (hrow : ∀ x, ∑' z, P x z = 1) (R : T → T → Prop)
    (x : T) :
    ∑' y, grn (restr P R) x y * ∑' z, restr P (fun a b => ¬ R a b) y z ≤ 1 := by
  unfold grn
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine ENNReal.tsum_le_of_sum_range_le (fun N => ?_)
  have := avoid_first P hrow R x N
  exact le_trans le_add_self this.le

/-- **cut inequality**: flux out of `C` ≤ flux into `C` (one direction of `F_in = F_out`). -/
theorem half (P P' : T → T → ℝ≥0∞) (hrow : ∀ x, ∑' z, P x z = 1) (m : T → ℝ≥0∞)
    (hmT : ∀ x, m x ≠ ⊤) (h : ∀ i j, m i * P i j = m j * P' j i)
    (hinv : ∀ y, ∑' x, m x * P x y = m y) (C : Set T) (D E : T → T → Prop)
    (hD : ∀ a b, D a b ↔ (a ∉ C ∧ b ∈ C)) (hE : ∀ a b, E a b ↔ (a ∈ C ∧ b ∉ C))
    (hlim : ∀ y, Tendsto (fun N => usum (restr P' (fun a b => ¬ D b a)) N y) atTop (𝓝 0)) :
    ∑' y, m y * ∑' w, restr P E y w ≤ ∑' x, ∑' z, m z * restr P D z x := by
  have hT5 : ∀ y, ∑' x, (∑' z, m z * restr P D z x) *
      grn (restr P (fun a b => ¬ D a b)) x y = m y :=
    fun y => T5 P P' m hmT h hinv D hlim y
  have hb : ∀ x, ∑' y, grn (restr P (fun a b => ¬ D a b)) x y * ∑' w, restr P E y w ≤ 1 := by
    intro x
    refine le_trans (ENNReal.tsum_le_tsum fun y => ?_)
      (first_le_one P hrow (fun a b => a ∈ C ∧ b ∈ C) x)
    by_cases hy : y ∈ C
    · have e : grn (restr P (fun a b => ¬ D a b)) x y =
          grn (restr P (fun a b => a ∈ C ∧ b ∈ C)) x y := by
        unfold grn; congr 1; ext n
        exact mpow_restr_eq P _ (fun a b => a ∈ C ∧ b ∈ C) C
          (fun a b hb => by simp [hD, hb]) (fun a b hab => hab.1) n x y hy
      rw [e]
      refine mul_le_mul_of_nonneg_left (ENNReal.tsum_le_tsum fun w => ?_) zero_le
      simp only [restr]
      by_cases hw : E y w
      · have hR : ¬ (y ∈ C ∧ w ∈ C) := fun hr => ((hE y w).1 hw).2 hr.2
        simp [hw, hR]
      · simp [hw]
    · have : ∀ w, restr P E y w = 0 := fun w => by
        simp only [restr]; rw [if_neg (fun hw => hy ((hE y w).1 hw).1)]
      simp [this]
  calc ∑' y, m y * ∑' w, restr P E y w
      = ∑' y, (∑' x, (∑' z, m z * restr P D z x) * grn (restr P (fun a b => ¬ D a b)) x y) *
          ∑' w, restr P E y w := by
        congr 1; ext y; rw [hT5 y]
    _ = ∑' x, (∑' z, m z * restr P D z x) *
          ∑' y, grn (restr P (fun a b => ¬ D a b)) x y * ∑' w, restr P E y w :=
        (sw (fun x => ∑' z, m z * restr P D z x)
          (fun x y => grn (restr P (fun a b => ¬ D a b)) x y)
          (fun y => ∑' w, restr P E y w)).symm
    _ ≤ ∑' x, (∑' z, m z * restr P D z x) * 1 :=
        ENNReal.tsum_le_tsum fun x => mul_le_mul_of_nonneg_left (hb x) zero_le
    _ = _ := by simp

/-- generic exit kernel: `E j j' = (Σ_k w j k G(k, j')) · pout j'` -/
noncomputable def exK (P : T → T → ℝ≥0∞) (B : Set T) (w : T → T → ℝ≥0∞) (po : T → ℝ≥0∞)
    (j j' : B) : ℝ≥0∞ :=
  (∑' k, w j k * grn (restr P (fun a b => ¬ (a ∈ B ∧ b ∉ B))) k j') * po j'

/-- generic entry kernel: `N j j' = Σ_y G'(j, y) P(y, j') [y ∉ B]` -/
noncomputable def enK (P : T → T → ℝ≥0∞) (B : Set T) (j j' : B) : ℝ≥0∞ :=
  ∑' y, grn (restr P (fun a b => ¬ (a ∉ B ∧ b ∈ B))) j y *
    restr P (fun a b => a ∉ B ∧ b ∈ B) y j'

theorem exK_sum (P : T → T → ℝ≥0∞) (B : Set T) (w : T → T → ℝ≥0∞) (po : T → ℝ≥0∞)
    (ν : B → ℝ≥0∞) (y : B) :
    ∑' j, ν j * exK P B w po j y =
      lift (restr P (fun a b => ¬ (a ∈ B ∧ b ∉ B))) (fun k => ∑' j, ν j * w j k) y * po y := by
  simp only [exK, lift]
  simp_rw [← mul_assoc]
  rw [ENNReal.tsum_mul_right]
  congr 1
  exact sw ν (fun j k => w j k) (fun k => grn (restr P (fun a b => ¬ (a ∈ B ∧ b ∉ B))) k y)

theorem enK_sum (P : T → T → ℝ≥0∞) (B : Set T) (ν : B → ℝ≥0∞) (y : B) :
    ∑' j, ν j * enK P B j y =
      ∑' x, lift (restr P (fun a b => ¬ (a ∉ B ∧ b ∈ B))) (extB B ν) x *
        restr P (fun a b => a ∉ B ∧ b ∈ B) x y := by
  unfold enK
  exact (sub_ext B ν (fun x => ∑' y', grn (restr P (fun a b => ¬ (a ∉ B ∧ b ∈ B))) x y' *
      restr P (fun a b => a ∉ B ∧ b ∈ B) y' y)).trans
    (sw (extB B ν) (fun x y' => grn (restr P (fun a b => ¬ (a ∉ B ∧ b ∈ B))) x y')
      (fun y' => restr P (fun a b => a ∉ B ∧ b ∈ B) y' y))

/-- **Exit chain**: its stationary laws are exactly `m · pout / F_out`. -/
theorem exit_iff (P P' : T → T → ℝ≥0∞) (hrow : ∀ x, ∑' z, P x z = 1)
    (hirr : ∀ x y, ∃ n, 0 < mpow P n x y)
    (hret : ∀ i, Tendsto (fun N => ∑' z, mpow (restr P (fun _ b => b ≠ i)) N i z) atTop (𝓝 0))
    (m : T → ℝ≥0∞) (hm0 : ∀ x, m x ≠ 0) (hmT : ∀ x, m x ≠ ⊤)
    (h : ∀ i j, m i * P i j = m j * P' j i) (hinv : ∀ y, ∑' x, m x * P x y = m y)
    (B : Set T)
    (hlim : ∀ y, Tendsto (fun N => usum (restr P' (fun a b => ¬ (b ∈ B ∧ a ∉ B))) N y)
      atTop (𝓝 0))
    (po : T → ℝ≥0∞) (hpo : ∀ y, po y = ∑' z, restr P (fun a b => a ∈ B ∧ b ∉ B) y z)
    (w : T → T → ℝ≥0∞) (hw : ∀ y k, restr P (fun a b => a ∈ B ∧ b ∉ B) y k = po y * w y k)
    (hw1 : ∀ y k, w y k ≤ 1) (y0 w0 : T) (hy0 : y0 ∈ B) (hw0 : w0 ∉ B) (hPe : 0 < P y0 w0)
    (hFT : ∑' j : B, m j * po j ≠ ⊤) (ν' : B → ℝ≥0∞) :
    (∑' j, ν' j = 1 ∧ ∀ j', ∑' j, ν' j * exK P B w po j j' = ν' j') ↔
      ν' = fun j : B => m j * po j / ∑' j : B, m j * po j := by
  set Q := restr P (fun a b => ¬ (a ∈ B ∧ b ∉ B)) with hQ
  set F := ∑' j : B, m j * po j with hF
  have hT5 : ∀ y, ∑' x, (∑' z, m z * restr P (fun a b => a ∈ B ∧ b ∉ B) z x) * grn Q x y =
      m y := fun y => T5 P P' m hmT h hinv (fun a b => a ∈ B ∧ b ∉ B) hlim y
  have hF0 : F ≠ 0 := by
    have h1 : m y0 * po y0 ≤ F := ENNReal.le_tsum (f := fun j : B => m j * po j) ⟨y0, hy0⟩
    have h2 : P y0 w0 ≤ po y0 := by
      rw [hpo y0]
      refine le_trans ?_ (ENNReal.le_tsum w0)
      simp [restr, hy0, hw0]
    exact (lt_of_lt_of_le (ENNReal.mul_pos (hm0 y0) (lt_of_lt_of_le hPe h2).ne') h1).ne'
  constructor
  · rintro ⟨hsum, hst⟩
    set φ : T → ℝ≥0∞ := fun k => ∑' j, ν' j * w j k with hφ
    have ha : ∀ y : B, ν' y = lift Q φ y * po y := fun y => by
      rw [← hst y, exK_sum]
    have hb : ∀ w', ∑' y, lift Q φ y * restr P (fun a b => a ∈ B ∧ b ∉ B) y w' = φ w' := by
      intro w'
      rw [← sub_eq B (fun y => lift Q φ y * restr P (fun a b => a ∈ B ∧ b ∉ B) y w')
        (fun y hy => by simp [restr, hy])]
      simp_rw [hw, ← mul_assoc]
      show _ = ∑' j, ν' j * w j w'
      congr 1; ext y; rw [← ha y]
    have hinv' := lift_inv P (fun a b => a ∈ B ∧ b ∉ B) φ hb
    have hφ1 : φ w0 ≤ 1 := by
      calc φ w0 = ∑' j, ν' j * w j w0 := rfl
        _ ≤ ∑' j, ν' j * 1 := ENNReal.tsum_le_tsum fun j => mul_le_mul_of_nonneg_left (hw1 _ _) zero_le
        _ = 1 := by simp [hsum]
    have hfin0 : lift Q φ y0 ≠ ⊤ := by
      intro htop
      have h1 := ENNReal.le_tsum
        (f := fun y => lift Q φ y * restr P (fun a b => a ∈ B ∧ b ∉ B) y w0) y0
      rw [hb w0] at h1
      rw [htop, show restr P (fun a b => a ∈ B ∧ b ∉ B) y0 w0 = P y0 w0 by
        simp [restr, hy0, hw0], ENNReal.top_mul hPe.ne'] at h1
      exact absurd (le_trans h1 hφ1) (by simp)
    have hfin := inv_fin P hirr (lift Q φ) hinv' y0 hfin0
    have hprop := prop_m P hrow hirr y0 (hret y0) m hinv hmT (hm0 y0) (lift Q φ) hinv' hfin
    set c := lift Q φ y0 / m y0 with hc
    have hν : ∀ y : B, ν' y = c * (m y * po y) := fun y => by
      rw [ha y, hprop y, mul_assoc]
    have hcF : c * F = 1 := by
      rw [hF, ← ENNReal.tsum_mul_left, ← hsum]; congr 1; ext y; rw [hν y]
    have hc' : c = F⁻¹ := ENNReal.eq_inv_of_mul_eq_one_left hcF
    funext y
    show ν' y = _ / F
    rw [hν y, hc', div_eq_mul_inv]; ring
  · rintro rfl
    refine ⟨?_, fun j' => ?_⟩
    · simp_rw [div_eq_mul_inv]
      rw [ENNReal.tsum_mul_right, ← hF]
      exact ENNReal.mul_inv_cancel hF0 hFT
    · rw [exK_sum]
      have hφ : ∀ k, ∑' j : B, m j * po j / F * w j k =
          F⁻¹ * ∑' z, m z * restr P (fun a b => a ∈ B ∧ b ∉ B) z k := by
        intro k
        rw [← sub_eq B (fun z => m z * restr P (fun a b => a ∈ B ∧ b ∉ B) z k)
          (fun z hz => by simp [restr, hz]), ← ENNReal.tsum_mul_left]
        congr 1; ext j; rw [hw, div_eq_mul_inv]; ring
      simp only [lift, hφ]
      simp_rw [mul_assoc]
      rw [ENNReal.tsum_mul_left, hT5 j', div_eq_mul_inv]
      ring

/-- **Entry chain**: its stationary laws are exactly `b' / F_in`. -/
theorem entry_iff (P P' : T → T → ℝ≥0∞) (hrow : ∀ x, ∑' z, P x z = 1)
    (hirr : ∀ x y, ∃ n, 0 < mpow P n x y)
    (hret : ∀ i, Tendsto (fun N => ∑' z, mpow (restr P (fun _ b => b ≠ i)) N i z) atTop (𝓝 0))
    (m : T → ℝ≥0∞) (hm0 : ∀ x, m x ≠ 0) (hmT : ∀ x, m x ≠ ⊤)
    (h : ∀ i j, m i * P i j = m j * P' j i) (hinv : ∀ y, ∑' x, m x * P x y = m y)
    (B : Set T)
    (hlim : ∀ y, Tendsto (fun N => usum (restr P' (fun a b => ¬ (b ∉ B ∧ a ∈ B))) N y)
      atTop (𝓝 0))
    (y0 w0 : T) (hy0 : y0 ∉ B) (hw0 : w0 ∈ B) (hPe : 0 < P y0 w0)
    (hFT : ∑' j : B, ∑' z, m z * restr P (fun a b => a ∉ B ∧ b ∈ B) z j ≠ ⊤)
    (ν' : B → ℝ≥0∞) :
    (∑' j, ν' j = 1 ∧ ∀ j', ∑' j, ν' j * enK P B j j' = ν' j') ↔
      ν' = fun j : B => (∑' z, m z * restr P (fun a b => a ∉ B ∧ b ∈ B) z j) /
        ∑' j : B, ∑' z, m z * restr P (fun a b => a ∉ B ∧ b ∈ B) z j := by
  set Q := restr P (fun a b => ¬ (a ∉ B ∧ b ∈ B)) with hQ
  set F := ∑' j : B, ∑' z, m z * restr P (fun a b => a ∉ B ∧ b ∈ B) z j with hF
  have hT5 : ∀ y, ∑' x, (∑' z, m z * restr P (fun a b => a ∉ B ∧ b ∈ B) z x) * grn Q x y =
      m y := fun y => T5 P P' m hmT h hinv (fun a b => a ∉ B ∧ b ∈ B) hlim y
  have hF0 : F ≠ 0 := by
    have h1 : ∑' z, m z * restr P (fun a b => a ∉ B ∧ b ∈ B) z w0 ≤ F :=
      ENNReal.le_tsum (f := fun j : B => ∑' z, m z * restr P (fun a b => a ∉ B ∧ b ∈ B) z j)
        ⟨w0, hw0⟩
    have h2 : m y0 * P y0 w0 ≤ ∑' z, m z * restr P (fun a b => a ∉ B ∧ b ∈ B) z w0 := by
      refine le_trans ?_ (ENNReal.le_tsum y0)
      simp [restr, hy0, hw0]
    exact (lt_of_lt_of_le (ENNReal.mul_pos (hm0 y0) hPe.ne') (h2.trans h1)).ne'
  constructor
  · rintro ⟨hsum, hst⟩
    have hb : ∀ w', ∑' y, lift Q (extB B ν') y * restr P (fun a b => a ∉ B ∧ b ∈ B) y w' =
        extB B ν' w' := by
      intro w'
      by_cases hw' : w' ∈ B
      · rw [show extB B ν' w' = ν' ⟨w', hw'⟩ by simp [extB, hw'], ← hst ⟨w', hw'⟩, enK_sum]
      · rw [show extB B ν' w' = 0 by simp [extB, hw']]
        simp [restr, hw']
    have hinv' := lift_inv P (fun a b => a ∉ B ∧ b ∈ B) (extB B ν') hb
    have hfin0 : lift Q (extB B ν') y0 ≠ ⊤ := by
      intro htop
      have h1 := ENNReal.le_tsum
        (f := fun y => lift Q (extB B ν') y * restr P (fun a b => a ∉ B ∧ b ∈ B) y w0) y0
      rw [hb w0] at h1
      have h2 : extB B ν' w0 ≤ 1 := by
        rw [show extB B ν' w0 = ν' ⟨w0, hw0⟩ by simp [extB, hw0], ← hsum]
        exact ENNReal.le_tsum _
      rw [htop, show restr P (fun a b => a ∉ B ∧ b ∈ B) y0 w0 = P y0 w0 by
        simp [restr, hy0, hw0], ENNReal.top_mul hPe.ne'] at h1
      exact absurd (le_trans h1 h2) (by simp)
    have hfin := inv_fin P hirr _ hinv' y0 hfin0
    have hprop := prop_m P hrow hirr y0 (hret y0) m hinv hmT (hm0 y0) _ hinv' hfin
    set c := lift Q (extB B ν') y0 / m y0 with hc
    have hν : ∀ y : B, ν' y = c * ∑' z, m z * restr P (fun a b => a ∉ B ∧ b ∈ B) z y :=
      fun y => by
        rw [← hst y, enK_sum, ← ENNReal.tsum_mul_left]
        congr 1; ext x; rw [hprop x, mul_assoc]
    have hcF : c * F = 1 := by
      rw [hF, ← ENNReal.tsum_mul_left, ← hsum]; congr 1; ext y; rw [hν y]
    have hc' : c = F⁻¹ := ENNReal.eq_inv_of_mul_eq_one_left hcF
    funext y
    show ν' y = _ / F
    rw [hν y, hc', div_eq_mul_inv]; ring
  · rintro rfl
    refine ⟨?_, fun j' => ?_⟩
    · simp_rw [div_eq_mul_inv]
      rw [ENNReal.tsum_mul_right, ← hF]
      exact ENNReal.mul_inv_cancel hF0 hFT
    · rw [enK_sum]
      have he : extB B (fun j => (∑' z, m z * restr P (fun a b => a ∉ B ∧ b ∈ B) z j) / F) =
          fun x => F⁻¹ * ∑' z, m z * restr P (fun a b => a ∉ B ∧ b ∈ B) z x := by
        funext x
        by_cases hx : x ∈ B
        · simp [extB, hx, div_eq_mul_inv, mul_comm]
        · simp [extB, hx, restr]
      rw [he]
      have hl : ∀ x, lift (restr P (fun a b => ¬ (a ∉ B ∧ b ∈ B))) (fun x => F⁻¹ * ∑' z, m z * restr P (fun a b => a ∉ B ∧ b ∈ B) z x) x
          = F⁻¹ * m x := fun x => by
        rw [lift_smul]; congr 1; exact hT5 x
      simp_rw [hl, mul_assoc]
      rw [ENNReal.tsum_mul_left, div_eq_mul_inv]
      ring

/-- **Cut balance** `F_out = F_in`. -/
theorem cut (P P' : T → T → ℝ≥0∞) (hrow : ∀ x, ∑' z, P x z = 1) (m : T → ℝ≥0∞)
    (hmT : ∀ x, m x ≠ ⊤) (h : ∀ i j, m i * P i j = m j * P' j i)
    (hinv : ∀ y, ∑' x, m x * P x y = m y) (B : Set T)
    (hlimX : ∀ y, Tendsto (fun N => usum (restr P' (fun a b => ¬ (b ∈ B ∧ a ∉ B))) N y)
      atTop (𝓝 0))
    (hlimN : ∀ y, Tendsto (fun N => usum (restr P' (fun a b => ¬ (b ∉ B ∧ a ∈ B))) N y)
      atTop (𝓝 0))
    (po : T → ℝ≥0∞) (hpo : ∀ y, po y = ∑' z, restr P (fun a b => a ∈ B ∧ b ∉ B) y z) :
    ∑' j : B, m j * po j = ∑' j : B, ∑' z, m z * restr P (fun a b => a ∉ B ∧ b ∈ B) z j := by
  have e1 : ∑' j : B, m j * po j =
      ∑' y, m y * ∑' w, restr P (fun a b => a ∈ B ∧ b ∉ B) y w := by
    rw [sub_eq B (fun y => m y * po y) (fun y hy => by rw [hpo y]; simp [restr, hy])]
    congr 1; ext y; rw [hpo y]
  have e2 : ∑' j : B, ∑' z, m z * restr P (fun a b => a ∉ B ∧ b ∈ B) z j =
      ∑' x, ∑' z, m z * restr P (fun a b => a ∉ B ∧ b ∈ B) z x :=
    sub_eq B (fun x => ∑' z, m z * restr P (fun a b => a ∉ B ∧ b ∈ B) z x)
      (fun x hx => by simp [restr, hx])
  rw [e1, e2]
  apply le_antisymm
  · exact half P P' hrow m hmT h hinv B (fun a b => a ∉ B ∧ b ∈ B) (fun a b => a ∈ B ∧ b ∉ B)
      (fun a b => Iff.rfl) (fun a b => Iff.rfl) hlimN
  · have := half P P' hrow m hmT h hinv Bᶜ (fun a b => a ∈ B ∧ b ∉ B)
      (fun a b => a ∉ B ∧ b ∈ B) (fun a b => by simp) (fun a b => by simp) hlimX
    calc ∑' x, ∑' z, m z * restr P (fun a b => a ∉ B ∧ b ∈ B) z x
        = ∑' z, m z * ∑' x, restr P (fun a b => a ∉ B ∧ b ∈ B) z x := by
          rw [ENNReal.tsum_comm]; simp_rw [ENNReal.tsum_mul_left]
      _ ≤ ∑' x, ∑' z, m z * restr P (fun a b => a ∈ B ∧ b ∉ B) z x := this
      _ = ∑' y, m y * ∑' w, restr P (fun a b => a ∈ B ∧ b ∉ B) y w := by
          rw [ENNReal.tsum_comm]; simp_rw [ENNReal.tsum_mul_left]

/-- `T4` packaged: a `D`-edge `b → a` of `P` kills the reversed chain at reversed `D`-steps. -/
theorem hlim_edge (P P' : T → T → ℝ≥0∞) (m : T → ℝ≥0∞) (hm0 : ∀ x, m x ≠ 0)
    (h : ∀ i j, m i * P i j = m j * P' j i) (hrow' : ∀ x, ∑' z, P' x z = 1)
    (hhit : ∀ a x, ∑' t, mpow (restr P' (fun y _ => y ≠ a)) t x a = 1)
    (D : T → T → Prop) (b a : T) (hD : D b a) (hP : 0 < P b a) (y : T) :
    Tendsto (fun N => usum (restr P' (fun a b => ¬ D b a)) N y) atTop (𝓝 0) := by
  have hne : m a * P' a b ≠ 0 := by
    rw [← h b a]; exact (ENNReal.mul_pos (hm0 b) hP.ne').ne'
  exact T4 P' hrow' a b (pos_iff_ne_zero.2 (right_ne_zero_of_mul hne)) (hhit a)
    (fun a b => ¬ D b a) (not_not.2 hD) y

end Mat

/-! ## Bridge: path events of the jump chain ↔ matrix powers -/

theorem det_meas (n : ℕ) (E : Set (ℕ → S))
    (hdet : ∀ ω ω', (∀ i ≤ n, ω i = ω' i) → ω ∈ E → ω' ∈ E) : MeasurableSet E := by
  have hEG : frestrictLe n ⁻¹' (frestrictLe n '' E) = E := by
    ext ω; constructor
    · rintro ⟨ω', h', he⟩
      exact hdet ω' ω (fun i hi => by
        have := congrFun he ⟨i, mem_Iic.2 hi⟩; simpa [frestrictLe_apply] using this) h'
    · intro h; exact ⟨ω, h, rfl⟩
  rw [← hEG]
  exact measurable_frestrictLe n (Set.to_countable _).measurableSet

/-- **Markov property at the last step.** -/
theorem last_step (q : S → S → ℝ≥0∞) (k : S) (n : ℕ) (E : Set (ℕ → S)) (y z : S)
    (hdet : ∀ ω ω', (∀ i ≤ n, ω i = ω' i) → ω ∈ E → ω' ∈ E) (hy : ∀ ω ∈ E, ω n = y) :
    jumpChainLaw q k (E ∩ {ω | ω (n + 1) = z}) = jumpChainLaw q k E * jumpProb q y z := by
  set G : Set (Π _ : Iic n, S) := frestrictLe n '' E with hG
  have hGm : MeasurableSet G := (Set.to_countable G).measurableSet
  have hEG : frestrictLe n ⁻¹' G = E := by
    ext ω; constructor
    · rintro ⟨ω', h', he⟩
      exact hdet ω' ω (fun i hi => by
        have := congrFun he ⟨i, mem_Iic.2 hi⟩; simpa [frestrictLe_apply] using this) h'
    · intro h; exact ⟨ω, h, rfl⟩
  have hset : E ∩ {ω | ω (n + 1) = z} =
      (fun ω : ℕ → S => (frestrictLe n ω, ω (n + 1))) ⁻¹' (G ×ˢ {z}) := by
    ext ω
    have : ω ∈ E ↔ frestrictLe n ω ∈ G := by rw [← Set.mem_preimage, hEG]
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff,
      Set.mem_ofPred_eq, this]
  have hmeasF : Measurable (fun ω : ℕ → S => (frestrictLe n ω, ω (n + 1))) := by fun_prop
  rw [hset, jumpChainLaw_eq, ← Measure.map_apply hmeasF (hGm.prod (measurableSet_singleton _)),
    ← Kernel.partialTraj_compProd_eq_map_traj (Nat.zero_le n),
    Measure.compProd_apply_prod hGm (measurableSet_singleton _)]
  have hconst : ∀ x ∈ G, jk q n x {z} = jumpProb q y z := by
    rintro x ⟨ω, hω, rfl⟩
    rw [Kernel.comap_apply, jumpKernel_singleton]
    simp only [frestrictLe_apply, hy ω hω]
  rw [setLIntegral_congr_fun hGm hconst, setLIntegral_const,
    ← Kernel.traj_map_frestrictLe_apply, Measure.map_apply (measurable_frestrictLe n) hGm, hEG,
    ← jumpChainLaw_eq, mul_comm]

/-- paths whose first `m` steps satisfy `R` and that sit at `y` at time `m` -/
def Ev (R : S → S → Prop) (m : ℕ) (y : S) : Set (ℕ → S) :=
  {ω | (∀ i < m, R (ω i) (ω (i + 1))) ∧ ω m = y}

theorem Ev_det (R : S → S → Prop) (m : ℕ) (y : S) :
    ∀ ω ω', (∀ i ≤ m, ω i = ω' i) → ω ∈ Ev R m y → ω' ∈ Ev R m y := by
  rintro ω ω' h ⟨h1, h2⟩
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [← h i hi.le, ← h (i + 1) hi]; exact h1 i hi
  · rw [← h m le_rfl]; exact h2

theorem Ev_meas (R : S → S → Prop) (m : ℕ) (y : S) : MeasurableSet (Ev R m y) :=
  det_meas m _ (Ev_det R m y)

/-- **Restricted path law = power of the restricted jump matrix.** -/
theorem Ev_law (q : S → S → ℝ≥0∞) (R : S → S → Prop) (k : S) :
    ∀ m y, jumpChainLaw q k (Ev R m y) = mpow (restr (jumpProb q) R) m k y
  | 0, y => by
    have : Ev R 0 y = {ω | ∀ i ≤ 0, ω i = (fun _ => y) i} := by
      ext ω; simp [Ev]
    rw [this, cylinder]
    by_cases h : k = y
    · subst h; simp [mpow, mone]
    · simp [mpow, mone, h, Ne.symm h]
  | m + 1, y' => by
    have hsplit : Ev R (m + 1) y' =
        ⋃ y, ((Ev R m y ∩ {ω | ω (m + 1) = y'}) ∩ {_ω | R y y'}) := by
      ext ω
      simp only [Ev, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨ω m, ⟨⟨fun i hi => h1 i (Nat.lt_succ_of_lt hi), rfl⟩, h2⟩, h2 ▸ h1 m (Nat.lt_succ_self m)⟩
      · rintro ⟨y, ⟨⟨h1, rfl⟩, h2⟩, h3⟩
        refine ⟨fun i hi => ?_, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact h1 i hi
        · rw [h2]; exact h3
    rw [hsplit, measure_iUnion]
    · simp only [mpow, mmul]
      congr 1; ext y
      by_cases hR : R y y'
      · simp only [hR, Set.ofPred_true, Set.inter_univ]
        rw [last_step q k m (Ev R m y) y y' (Ev_det R m y) (fun ω h => h.2), Ev_law q R k m y]
        simp [restr, hR]
      · simp only [hR, Set.ofPred_false, Set.inter_empty, measure_empty]
        simp [restr, hR]
    · intro a b hab
      exact Set.disjoint_left.2 fun ω ha hb => hab (ha.1.1.2.symm.trans hb.1.1.2)
    · intro y
      exact ((Ev_meas R m y).inter (measurable_pi_apply (m + 1) (measurableSet_singleton y'))).inter
        (MeasurableSet.const _)



/-! ## Measure facts for the jump chain -/

theorem jcl_prob (q : S → S → ℝ≥0∞) (j : S) : IsProbabilityMeasure (jumpChainLaw q j) := by
  rw [jumpChainLaw_eq]; infer_instance

attribute [local instance] jcl_prob

theorem avoid_tendsto (q : S → S → ℝ≥0∞) (s : S) (R : S → S → Prop)
    (h0 : jumpChainLaw q s {ω | ∀ n, R (ω n) (ω (n + 1))} = 0) :
    Tendsto (fun N => ∑' z, mpow (restr (jumpProb q) R) N s z) atTop (𝓝 0) := by
  set μ := jumpChainLaw q s
  let pre : ℕ → Set (ℕ → S) := fun N => {ω | ∀ i < N, R (ω i) (ω (i + 1))}
  have hpre : ∀ N, MeasurableSet (pre N) := fun N => det_meas N _ (fun ω ω' h hω i hi => by
    rw [← h i hi.le, ← h (i + 1) hi]; exact hω i hi)
  have e : ∀ N, ∑' z, mpow (restr (jumpProb q) R) N s z = μ (pre N) := by
    intro N
    simp_rw [← Ev_law]
    rw [← measure_iUnion]
    · congr 1; ext ω; simp [Ev, pre]
    · intro a b hab
      exact Set.disjoint_left.2 fun ω ha hb => hab (ha.2.symm.trans hb.2)
    · exact fun z => Ev_meas R N z
  simp_rw [e]
  have hanti : Antitone pre := fun N N' hN ω h i hi => h i (lt_of_lt_of_le hi hN)
  have := tendsto_measure_iInter_atTop (μ := μ) (fun N => (hpre N).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  have hI : (⋂ N, pre N) = {ω | ∀ n, R (ω n) (ω (n + 1))} := by
    ext ω; simp only [pre, Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun h n => h (n + 1) n (Nat.lt_succ_self n), fun h N i _ => h i⟩
  rw [hI, h0] at this
  exact this

/-- **The non-explosion argument**: a supersolution with finite `w`-mass makes the event
"all transitions satisfy `R` forever" null. -/
theorem never_null (q : S → S → ℝ≥0∞) (s : S) (R : S → S → Prop) (w v : S → ℝ≥0∞)
    (hv : ∀ y, mone s y + ∑' x, v x * restr (jumpProb q) R x y ≤ v y)
    (hvw : ∑' y, v y * w y ≠ ⊤)
    (hne : ∀ᵐ ω ∂ jumpChainLaw q s, ∑' n, w (ω n) = ⊤) :
    jumpChainLaw q s {ω | ∀ n, R (ω n) (ω (n + 1))} = 0 := by
  set μ := jumpChainLaw q s
  set N := {ω : ℕ → S | ∀ n, R (ω n) (ω (n + 1))} with hNdef
  have hNm : MeasurableSet N := by
    have : N = ⋂ n, {ω : ℕ → S | R (ω n) (ω (n + 1))} := by ext; simp [N]
    rw [this]
    exact MeasurableSet.iInter fun n => det_meas (n + 1) _ (fun ω ω' h hω => by
      rw [Set.mem_ofPred_eq] at hω ⊢
      rw [← h n (Nat.le_succ n), ← h (n + 1) le_rfl]; exact hω)
  have hind : ∀ n y, Measurable ((Ev R n y).indicator (1 : (ℕ → S) → ℝ≥0∞)) :=
    fun n y => measurable_one.indicator (Ev_meas R n y)
  let W : (ℕ → S) → ℝ≥0∞ := fun ω => ∑' n, ∑' y, w y * (Ev R n y).indicator 1 ω
  have hWm : ∀ n, Measurable (fun ω => ∑' y, w y * (Ev R n y).indicator (1 : (ℕ → S) → ℝ≥0∞) ω) :=
    fun n => Measurable.ennreal_tsum fun y => measurable_const.mul (hind n y)
  have hint : ∫⁻ ω, W ω ∂μ = ∑' n, ∑' y, w y * mpow (restr (jumpProb q) R) n s y := by
    simp only [W]
    rw [lintegral_tsum fun n => (hWm n).aemeasurable]
    congr 1; ext n
    rw [lintegral_tsum (f := fun y ω => w y * (Ev R n y).indicator (1 : (ℕ → S) → ℝ≥0∞) ω)
      fun y => (measurable_const.mul (hind n y)).aemeasurable]
    congr 1; ext y
    rw [lintegral_const_mul _ (hind n y), lintegral_indicator_one (Ev_meas R n y), Ev_law]
  have hfin : ∫⁻ ω, W ω ∂μ ≠ ⊤ := by
    rw [hint, ENNReal.tsum_comm]
    refine ne_top_of_le_ne_top hvw (ENNReal.tsum_le_tsum fun y => ?_)
    rw [ENNReal.tsum_mul_left, mul_comm]
    gcongr; exact ENNReal.tsum_le_of_sum_range_le fun N => green_le _ s v hv N y
  have hlow : ∫⁻ ω, N.indicator (fun _ => ⊤) ω ∂μ ≤ ∫⁻ ω, W ω ∂μ := by
    apply lintegral_mono_ae
    filter_upwards [hne] with ω hω
    by_cases hN : ω ∈ N
    · rw [Set.indicator_of_mem hN]
      have : W ω = ∑' n, w (ω n) := by
        simp only [W]; congr 1; ext n
        rw [tsum_eq_single (ω n)]
        · have hm : ω ∈ Ev R n (ω n) := ⟨fun i _ => hN i, rfl⟩
          simp [Set.indicator_of_mem hm]
        · intro y hy
          have hm : ω ∉ Ev R n y := fun h => hy h.2.symm
          simp [Set.indicator_of_notMem hm]
      rw [this, hω]
    · rw [Set.indicator_of_notMem hN]; simp
  rw [lintegral_indicator_const hNm] at hlow
  by_contra h
  rw [ENNReal.top_mul h] at hlow
  exact hfin (top_le_iff.1 hlow)

/-! ## Kelly setting: invariance of `m = π q` and recurrence (T1) -/

theorem jumpProb_eq (q : S → S → ℝ≥0∞) (j k : S) (h0 : 0 < ∑' k', q j k')
    (hT : ∑' k', q j k' ≠ ⊤) : jumpProb q j k = q j k / ∑' k', q j k' := by
  simp [jumpProb, h0, lt_top_iff_ne_top.2 hT]

theorem m_inv (q : S → S → ℝ≥0∞) (hqpos : ∀ j, 0 < ∑' k, q j k) (hqT : ∀ j, ∑' k, q j k ≠ ⊤)
    (π : S → ℝ≥0∞) (hbal : ∀ j, π j * ∑' k, q j k = ∑' k, π k * q k j) (y : S) :
    ∑' x, π x * (∑' k, q x k) * jumpProb q x y = π y * ∑' k, q y k := by
  rw [hbal y]
  congr 1; ext x
  rw [jumpProb_eq q x y (hqpos x) (hqT x), mul_assoc, ENNReal.mul_div_cancel (hqpos x).ne' (hqT x)]

/-- **T1: the jump chain returns to every state almost surely** (avoid form). -/
theorem return_avoid (q : S → S → ℝ≥0∞) (hqpos : ∀ j, 0 < ∑' k, q j k)
    (hqT : ∀ j, ∑' k, q j k ≠ ⊤) (π : S → ℝ≥0∞) (hπpos : ∀ j, 0 < π j) (hπ1 : ∑' j, π j = 1)
    (hbal : ∀ j, π j * ∑' k, q j k = ∑' k, π k * q k j)
    (hne : ∀ j, ∀ᵐ ω ∂ jumpChainLaw q j, ∑' n, (∑' k, q (ω n) k)⁻¹ = ⊤) (i : S) :
    Tendsto (fun N => ∑' z, mpow (restr (jumpProb q) (fun _ b => b ≠ i)) N i z) atTop (𝓝 0) := by
  apply avoid_tendsto
  have hπT : ∀ j, π j ≠ ⊤ := fun j => ne_top_of_le_ne_top ENNReal.one_ne_top (hπ1 ▸ ENNReal.le_tsum j)
  set m : S → ℝ≥0∞ := fun x => π x * ∑' k, q x k with hm
  have hm0 : m i ≠ 0 := (ENNReal.mul_pos (hπpos i).ne' (hqpos i).ne').ne'
  have hmT : m i ≠ ⊤ := ENNReal.mul_ne_top (hπT i) (hqT i)
  refine never_null q i (fun _ b => b ≠ i) (fun y => (∑' k, q y k)⁻¹) (fun x => (m i)⁻¹ * m x) ?_ ?_ (hne i)
  · intro y
    by_cases hy : y = i
    · subst hy
      have : ∀ x, restr (jumpProb q) (fun _ b => b ≠ y) x y = 0 := fun x => by simp [restr]
      simp only [this, mul_zero, tsum_zero, add_zero, mone, if_true]
      rw [ENNReal.inv_mul_cancel hm0 hmT]
    · have : ∀ x, restr (jumpProb q) (fun _ b => b ≠ i) x y = jumpProb q x y := fun x => by
        simp [restr, hy]
      simp only [this, mone, Ne.symm hy, if_false, zero_add]
      simp_rw [mul_assoc]
      rw [ENNReal.tsum_mul_left]
      exact le_of_eq (congrArg _ (m_inv q hqpos hqT π hbal y))
  · have : ∀ y, (m i)⁻¹ * m y * (∑' k, q y k)⁻¹ = (m i)⁻¹ * π y := by
      intro y; simp only [m]
      rw [mul_assoc, mul_assoc, ENNReal.mul_inv_cancel (hqpos y).ne' (hqT y), mul_one]
    simp_rw [this]
    rw [ENNReal.tsum_mul_left, hπ1, mul_one]
    exact ENNReal.inv_ne_top.2 hm0

/-! ## First-transition events -/

theorem coord_meas (n : ℕ) (y : S) : MeasurableSet {ω : ℕ → S | ω n = y} := by
  have h : MeasurableSet ((fun ω : ℕ → S => ω n) ⁻¹' {y}) :=
    (measurable_pi_apply n) (measurableSet_singleton y)
  exact h

theorem meas_split (μ : Measure (ℕ → S)) (E : Set (ℕ → S)) (hE : MeasurableSet E) (n : ℕ) :
    μ E = ∑' y, μ (E ∩ {ω | ω n = y}) := by
  rw [← measure_iUnion]
  · congr 1; ext ω; simp
  · intro a b hab
    exact Set.disjoint_left.2 fun ω h1 h2 => hab (h1.2.symm.trans h2.2)
  · intro y; exact hE.inter (coord_meas n y)

/-- paths whose first `Term`-transition is at step `m`, all earlier ones satisfying `R` -/
def FirstAt (R Term : S → S → Prop) (m : ℕ) : Set (ℕ → S) :=
  {ω | Term (ω m) (ω (m + 1)) ∧ ∀ i < m, R (ω i) (ω (i + 1))}

theorem FirstAt_meas (R Term : S → S → Prop) (m : ℕ) : MeasurableSet (FirstAt R Term m) :=
  det_meas (m + 1) _ (fun ω ω' h ⟨h1, h2⟩ => by
    refine ⟨?_, fun i hi => ?_⟩
    · rw [← h m (Nat.le_succ m), ← h (m + 1) le_rfl]; exact h1
    · rw [← h i (by omega), ← h (i + 1) (by omega)]; exact h2 i hi)

theorem FirstAt_law (q : S → S → ℝ≥0∞) (R Term : S → S → Prop) (k : S) (m : ℕ) :
    jumpChainLaw q k (FirstAt R Term m) =
      ∑' y, ∑' z, mpow (restr (jumpProb q) R) m k y * restr (jumpProb q) Term y z := by
  rw [meas_split _ _ (FirstAt_meas R Term m) m]
  congr 1; ext y
  rw [meas_split _ _ ((FirstAt_meas R Term m).inter (coord_meas m y)) (m + 1)]
  congr 1; ext z
  have hpc : FirstAt R Term m ∩ {ω | ω m = y} ∩ {ω | ω (m + 1) = z} =
      (Ev R m y ∩ {ω | ω (m + 1) = z}) ∩ {_ω | Term y z} := by
    ext ω
    simp only [FirstAt, Ev, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      refine ⟨⟨⟨h2, h3⟩, h4⟩, ?_⟩; rw [← h3, ← h4]; exact h1
    · rintro ⟨⟨⟨h2, h3⟩, h4⟩, h1⟩
      refine ⟨⟨⟨?_, h2⟩, h3⟩, h4⟩; rw [h3, h4]; exact h1
  rw [hpc]
  by_cases ht : Term y z
  · simp only [ht, Set.ofPred_true, Set.inter_univ]
    rw [last_step q k m (Ev R m y) y z (Ev_det R m y) (fun ω h => h.2), Ev_law q R k m y]
    simp [restr, ht]
  · simp only [ht, Set.ofPred_false, Set.inter_empty, measure_empty]
    simp [restr, ht]

theorem first_law (q : S → S → ℝ≥0∞) (R Term : S → S → Prop) (hT : ∀ a b, Term a b → ¬ R a b)
    (k : S) :
    jumpChainLaw q k {ω | ∃ m, Term (ω m) (ω (m + 1)) ∧ ∀ i < m, R (ω i) (ω (i + 1))} =
      ∑' m, ∑' y, ∑' z, mpow (restr (jumpProb q) R) m k y * restr (jumpProb q) Term y z := by
  have hU : {ω : ℕ → S | ∃ m, Term (ω m) (ω (m + 1)) ∧ ∀ i < m, R (ω i) (ω (i + 1))} =
      ⋃ m, FirstAt R Term m := by
    ext ω; simp [FirstAt]
  rw [hU, measure_iUnion]
  · simp_rw [FirstAt_law]
  · intro a b hab
    refine Set.disjoint_left.2 fun ω ha hb => ?_
    rcases lt_or_gt_of_ne hab with h | h
    · exact hT _ _ ha.1 (hb.2 a h)
    · exact hT _ _ hb.1 (ha.2 b h)
  · exact FirstAt_meas R Term


/-! ## Kelly glue: Theorem 9.5 (i) ⇔ (vi) -/

theorem cross (r : S → S → Prop) (A : Set S) {a b : S} (h : Relation.ReflTransGen r a b)
    (ha : a ∈ A) (hb : b ∉ A) : ∃ x y, x ∈ A ∧ y ∉ A ∧ r x y := by
  revert hb
  induction h with
  | refl => intro hb; exact absurd ha hb
  | @tail c d _ hcd ih =>
    intro hd
    by_cases hc : c ∈ A
    · exact ⟨c, d, hc, hd, hcd⟩
    · exact ih hc

theorem qpos_of (q : S → S → ℝ≥0∞)
    (hirr : ∀ j k, Relation.ReflTransGen (fun a b => 0 < q a b) j k)
    (A : Set S) (hA : A.Nonempty) (hAc : (Aᶜ).Nonempty) (j : S) : 0 < ∑' k, q j k := by
  have : ∃ k, k ≠ j := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hAc
    by_cases hj : j ∈ A
    · exact ⟨b, fun h => hb (h ▸ hj)⟩
    · exact ⟨a, fun h => hj (h ▸ ha)⟩
  obtain ⟨k, hk⟩ := this
  rcases Relation.ReflTransGen.cases_head (hirr j k) with h | ⟨c, hc, -⟩
  · exact absurd h.symm hk
  · exact lt_of_lt_of_le hc (ENNReal.le_tsum c)

theorem hirr_p (q : S → S → ℝ≥0∞) (hqpos : ∀ j, 0 < ∑' k, q j k) (hqT : ∀ j, ∑' k, q j k ≠ ⊤)
    (hirr : ∀ j k, Relation.ReflTransGen (fun a b => 0 < q a b) j k) (x y : S) :
    ∃ n, 0 < mpow (jumpProb q) n x y := by
  have hr := hirr x y
  induction hr with
  | refl => exact ⟨0, by simp [mpow, mone]⟩
  | @tail b c _ hbc ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    have hp : 0 < jumpProb q b c := by
      rw [jumpProb_eq q b c (hqpos b) (hqT b)]
      exact ENNReal.div_pos hbc.ne' (hqT b)
    simp only [mpow, mmul]
    exact lt_of_lt_of_le (ENNReal.mul_pos hn.ne' hp.ne')
      (ENNReal.le_tsum (f := fun k => mpow (jumpProb q) n x k * jumpProb q k c) b)

theorem add_cancel_iff (a b a' b' : ℝ≥0∞) (h : a + b = a' + b') (hfin : a + b ≠ ⊤) :
    a = a' ↔ b = b' := by
  have ha : a ≠ ⊤ := fun h' => hfin (by simp [h'])
  have hb : b ≠ ⊤ := fun h' => hfin (by simp [h'])
  constructor
  · rintro rfl; exact (ENNReal.add_right_inj ha).1 h
  · rintro rfl; exact (ENNReal.add_left_inj hb).1 h

set_option maxHeartbeats 2000000 in
/-- **Kelly Theorem 9.5 (i) ⇔ (vi).** -/
theorem partV (q : S → S → ℝ≥0∞) (hq : IsKellyRates q) (π : S → ℝ≥0∞)
    (hπ : IsEquilibriumDist q π) (A : Set S) (hA : A.Nonempty) (hF : fluxOut q π A ≠ ⊤)
    (hAc : (Aᶜ).Nonempty) :
    IsPartialBalance q π A ↔ SameObservedEquilibrium q A := by
  classical
  obtain ⟨-, hqT, hirr0, hne⟩ := hq
  obtain ⟨hpos, h1, hbal⟩ := hπ
  have hqpos := qpos_of q hirr0 A hA hAc
  have hrow : ∀ x, ∑' z, jumpProb q x z = 1 := tsum_jumpProb q
  have hirr : ∀ x y, ∃ n, 0 < mpow (jumpProb q) n x y := hirr_p q hqpos hqT hirr0
  have hπT : ∀ j, π j ≠ ⊤ := pi_ne_top π h1
  set m : S → ℝ≥0∞ := fun j => π j * ∑' k, q j k with hm
  have hm0 : ∀ x, m x ≠ 0 := fun x => (ENNReal.mul_pos (hpos x).ne' (hqpos x).ne').ne'
  have hmT : ∀ x, m x ≠ ⊤ := fun x => ENNReal.mul_ne_top (hπT x) (hqT x)
  have hinv : ∀ y, ∑' x, m x * jumpProb q x y = m y := m_inv q hqpos hqT π hbal
  set P' : S → S → ℝ≥0∞ := fun i j => m j * jumpProb q j i / m i with hP'
  have h : ∀ i j, m i * jumpProb q i j = m j * P' j i := fun i j => by
    simp only [hP']; exact (ENNReal.mul_div_cancel (hm0 j) (hmT j)).symm
  have hrow' : ∀ x, ∑' z, P' x z = 1 := fun x => by
    simp only [hP']; simp_rw [div_eq_mul_inv]; rw [ENNReal.tsum_mul_right, hinv x]
    exact ENNReal.mul_inv_cancel (hm0 x) (hmT x)
  have hret := return_avoid q hqpos hqT π hpos h1 hbal hne
  have hR2 : ∀ i y, m y = m i * gam (jumpProb q) i y :=
    fun i y => R2 (jumpProb q) hrow hirr i (hret i) m hinv hmT y
  have hhit : ∀ a x, ∑' t, mpow (restr P' (fun y _ => y ≠ a)) t x a = 1 :=
    fun a x => rev_hit m hm0 hmT (jumpProb q) P' h hR2 a x
  -- edges across the cut
  obtain ⟨a0, ha0⟩ := hA
  obtain ⟨b0, hb0⟩ := hAc
  obtain ⟨y0, w0, hy0, hw0, hq0⟩ := cross _ A (hirr0 a0 b0) ha0 hb0
  obtain ⟨y1, w1, hy1, hw1, hq1⟩ := cross _ Aᶜ (hirr0 b0 a0) hb0 (by simpa using ha0)
  have hw1' : w1 ∈ A := by simpa using hw1
  have hpp : ∀ a b, 0 < q a b → 0 < jumpProb q a b := fun a b hab => by
    rw [jumpProb_eq q a b (hqpos a) (hqT a)]; exact ENNReal.div_pos hab.ne' (hqT a)
  have hlimX := hlim_edge (jumpProb q) P' m hm0 h hrow' hhit (fun a b => a ∈ A ∧ b ∉ A) y0 w0
    ⟨hy0, hw0⟩ (hpp _ _ hq0)
  have hlimN := hlim_edge (jumpProb q) P' m hm0 h hrow' hhit (fun a b => a ∉ A ∧ b ∈ A) y1 w1
    ⟨hy1, hw1'⟩ (hpp _ _ hq1)
  -- exit weights
  set po : S → ℝ≥0∞ := fun y => ∑' z, restr (jumpProb q) (fun a b => a ∈ A ∧ b ∉ A) y z
    with hpo
  set w : S → S → ℝ≥0∞ := fun y k => if k ∈ A then 0 else q y k / ∑' k' : ↥Aᶜ, q y k'
    with hwdef
  have hqo : ∀ y, ∑' k' : ↥Aᶜ, q y k' ≤ ∑' k, q y k := fun y =>
    ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
  have hpoA : ∀ y ∈ A, po y = (∑' k : ↥Aᶜ, q y k) / ∑' k, q y k := by
    intro y hy
    simp only [hpo]
    rw [← sub_eq Aᶜ (fun z => restr (jumpProb q) (fun a b => a ∈ A ∧ b ∉ A) y z)
      (fun z hz => by simp [restr, show z ∈ A by simpa using hz]), div_eq_mul_inv,
      ← ENNReal.tsum_mul_right]
    congr 1; ext z
    simp only [restr]
    rw [if_pos ⟨hy, z.2⟩, jumpProb_eq q y z (hqpos y) (hqT y), div_eq_mul_inv]
  have hw : ∀ y k, restr (jumpProb q) (fun a b => a ∈ A ∧ b ∉ A) y k = po y * w y k := by
    intro y k
    by_cases hy : y ∈ A
    · by_cases hk : k ∈ A
      · simp [restr, hk, hwdef]
      · have e1 : restr (jumpProb q) (fun a b => a ∈ A ∧ b ∉ A) y k = q y k / ∑' k, q y k := by
          simp only [restr]
          rw [if_pos ⟨hy, hk⟩]
          exact jumpProb_eq q y k (hqpos y) (hqT y)
        have e2 : w y k = q y k / ∑' k' : ↥Aᶜ, q y k' := by simp [hwdef, hk]
        rw [e1, e2, hpoA y hy]
        by_cases h0 : ∑' k' : ↥Aᶜ, q y k' = 0
        · have : q y k = 0 := le_antisymm
            (h0 ▸ ENNReal.le_tsum (f := fun k' : ↥Aᶜ => q y k') ⟨k, hk⟩) bot_le
          simp [this, h0]
        · have hT' : ∑' k' : ↥Aᶜ, q y k' ≠ ⊤ := ne_top_of_le_ne_top (hqT y) (hqo y)
          rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
          calc q y k * (∑' k, q y k)⁻¹
              = ((∑' k' : ↥Aᶜ, q y k') * (∑' k' : ↥Aᶜ, q y k')⁻¹) * (q y k * (∑' k, q y k)⁻¹) := by
                rw [ENNReal.mul_inv_cancel h0 hT', one_mul]
            _ = _ := by ring
    · have : po y = 0 := by simp [hpo, restr, hy]
      rw [this, zero_mul]; simp [restr, hy]
  have hw1 : ∀ y k, w y k ≤ 1 := by
    intro y k
    simp only [hwdef]
    split_ifs with hk
    · exact zero_le
    · exact ENNReal.div_le_of_le_mul (by
        rw [one_mul]; exact ENNReal.le_tsum (f := fun k' : ↥Aᶜ => q y k') ⟨k, hk⟩)
  -- kernel identifications
  have hEK : exitKernel q A = exK (jumpProb q) A w po := by
    funext j j'
    simp only [exitKernel, exK]
    have hev : ∀ k : S, jumpChainLaw q k
        {ω | ∃ m, ω m = (j' : S) ∧ ω (m + 1) ∉ A ∧ ∀ i < m, ¬ (ω i ∈ A ∧ ω (i + 1) ∉ A)} =
        grn (restr (jumpProb q) (fun a b => ¬ (a ∈ A ∧ b ∉ A))) k j' * po j' := by
      intro k
      have hset : {ω : ℕ → S | ∃ m, ω m = (j' : S) ∧ ω (m + 1) ∉ A ∧
          ∀ i < m, ¬ (ω i ∈ A ∧ ω (i + 1) ∉ A)} =
          {ω | ∃ m, (fun a b => a = (j' : S) ∧ b ∉ A) (ω m) (ω (m + 1)) ∧
            ∀ i < m, (fun a b => ¬ (a ∈ A ∧ b ∉ A)) (ω i) (ω (i + 1))} := by
        ext ω; simp only [Set.mem_setOf_eq, and_assoc]
      rw [hset]
      refine (first_law q (fun a b => ¬ (a ∈ A ∧ b ∉ A)) (fun a b => a = (j' : S) ∧ b ∉ A)
        (fun a b hab hR => hR ⟨hab.1 ▸ j'.2, hab.2⟩) k).trans ?_
      unfold grn
      rw [← ENNReal.tsum_mul_right]
      congr 1; ext n
      rw [tsum_eq_single (j' : S) (fun y hy => by simp [restr, hy])]
      rw [ENNReal.tsum_mul_left]
      congr 1
      simp only [hpo]
      congr 1; ext z
      simp [restr, j'.2]
    simp_rw [hev]
    rw [← ENNReal.tsum_mul_right, ← sub_eq Aᶜ
      (fun k => w j k * grn (restr (jumpProb q) (fun a b => ¬ (a ∈ A ∧ b ∉ A))) k j' * po j')
      (fun k hk => by simp [hwdef, show k ∈ A by simpa using hk])]
    congr 1; ext k
    have hk : (k : S) ∉ A := k.2
    simp only [hwdef, hk, ↓reduceIte]
    ring
  have hNK : entryKernel q A = enK (jumpProb q) A := by
    funext j j'
    simp only [entryKernel, enK]
    have hset : {ω : ℕ → S | ∃ m, ω m ∉ A ∧ ω (m + 1) = (j' : S) ∧
        ∀ i < m, ¬ (ω i ∉ A ∧ ω (i + 1) ∈ A)} =
        {ω | ∃ m, (fun a b => a ∉ A ∧ b = (j' : S)) (ω m) (ω (m + 1)) ∧
          ∀ i < m, (fun a b => ¬ (a ∉ A ∧ b ∈ A)) (ω i) (ω (i + 1))} := by
      ext ω; simp only [Set.mem_setOf_eq, and_assoc]
    rw [hset]
    refine (first_law q (fun a b => ¬ (a ∉ A ∧ b ∈ A)) (fun a b => a ∉ A ∧ b = (j' : S))
      (fun a b hab hR => hR ⟨hab.1, hab.2 ▸ j'.2⟩) j).trans ?_
    unfold grn
    simp_rw [← ENNReal.tsum_mul_right]
    conv_lhs => rw [ENNReal.tsum_comm]
    congr 1; ext y; congr 1; ext n
    rw [tsum_eq_single (j' : S) (fun z hz => by simp [restr, hz])]
    congr 1
    simp [restr, j'.2]
  -- fluxes
  have hmpo : ∀ j : A, m j * po j = π j * ∑' k : ↥Aᶜ, q j k := by
    intro j
    rw [hpoA j j.2]
    simp only [hm]
    rw [div_eq_mul_inv]
    calc π j * (∑' k, q j k) * ((∑' k : ↥Aᶜ, q j k) * (∑' k, q j k)⁻¹)
        = π j * (∑' k : ↥Aᶜ, q j k) * ((∑' k, q j k) * (∑' k, q j k)⁻¹) := by ring
      _ = _ := by rw [ENNReal.mul_inv_cancel (hqpos j).ne' (hqT j), mul_one]
  have hFout : ∑' j : A, m j * po j = fluxOut q π A := by
    unfold fluxOut
    congr 1; ext j
    rw [hmpo j, ENNReal.tsum_mul_left]
  have hb' : ∀ j : A, ∑' z, m z * restr (jumpProb q) (fun a b => a ∉ A ∧ b ∈ A) z j =
      ∑' k : ↥Aᶜ, π k * q k j := by
    intro j
    rw [← sub_eq Aᶜ (fun z => m z * restr (jumpProb q) (fun a b => a ∉ A ∧ b ∈ A) z j)
      (fun z hz => by simp [restr, show z ∈ A by simpa using hz])]
    congr 1; ext z
    have hz : (z : S) ∉ A := z.2
    simp only [restr, hm]
    rw [if_pos ⟨hz, j.2⟩, jumpProb_eq q z j (hqpos z) (hqT z), mul_assoc,
      ENNReal.mul_div_cancel (hqpos z).ne' (hqT z)]
  have hPB : IsPartialBalance q π A ↔ ∀ j : A,
      m j * po j = ∑' z, m z * restr (jumpProb q) (fun a b => a ∉ A ∧ b ∈ A) z j := by
    constructor
    · intro hP j
      rw [hmpo j, hb' j]
      exact (add_cancel_iff _ _ _ _ (global_split q π A j (hbal j))
        (global_fin q π A j (hqT j) (hπT j))).1 (hP j j.2)
    · intro hE j hj
      have := hE ⟨j, hj⟩
      rw [hmpo, hb'] at this
      exact (add_cancel_iff _ _ _ _ (global_split q π A j (hbal j))
        (global_fin q π A j (hqT j) (hπT j))).2 this
  have hFT : ∑' j : A, m j * po j ≠ ⊤ := by rw [hFout]; exact hF
  have hF0 : ∑' j : A, m j * po j ≠ 0 := by
    have h1 : m y0 * po y0 ≤ ∑' j : A, m j * po j :=
      ENNReal.le_tsum (f := fun j : A => m j * po j) ⟨y0, hy0⟩
    have h2 : jumpProb q y0 w0 ≤ po y0 := by
      show _ ≤ ∑' z, restr (jumpProb q) (fun a b => a ∈ A ∧ b ∉ A) y0 z
      refine le_trans ?_ (ENNReal.le_tsum w0)
      simp [restr, hy0, hw0]
    exact (lt_of_lt_of_le (ENNReal.mul_pos (hm0 y0)
      (lt_of_lt_of_le (hpp _ _ hq0) h2).ne') h1).ne'
  have hcut := cut (jumpProb q) P' hrow m hmT h hinv A hlimX hlimN po (fun y => rfl)
  have hE := fun ν' => exit_iff (jumpProb q) P' hrow hirr hret m hm0 hmT h hinv A hlimX po
    (fun y => rfl) w hw hw1 y0 w0 hy0 hw0 (hpp _ _ hq0) hFT ν'
  have hN := fun ν' => entry_iff (jumpProb q) P' hrow hirr hret m hm0 hmT h hinv A hlimN y1 w1
    hy1 hw1' (hpp _ _ hq1) (hcut ▸ hFT) ν'
  rw [hPB]
  unfold SameObservedEquilibrium IsStationaryProb
  rw [hEK, hNK]
  constructor
  · intro hE'
    have heq : (fun j : A => (∑' z, m z * restr (jumpProb q) (fun a b => a ∉ A ∧ b ∈ A) z j) /
        ∑' j : A, ∑' z, m z * restr (jumpProb q) (fun a b => a ∉ A ∧ b ∈ A) z j) =
        (fun j : A => m j * po j / ∑' j : A, m j * po j) := by
      funext j; rw [hE' j, hcut]
    exact ⟨fun j : A => m j * po j / ∑' j : A, m j * po j, hE,
      fun ν' => (hN ν').trans (by rw [heq])⟩
  · rintro ⟨ν, h1', h2'⟩ j
    have eX := (h1' _).1 ((hE _).2 rfl)
    have eN := (h2' _).1 ((hN _).2 rfl)
    have e := congrFun (eX.trans eN.symm) j
    rw [← hcut] at e
    have e2 := congrArg (· * ∑' j : A, m j * po j) e
    simp only [ENNReal.div_mul_cancel hF0 hFT] at e2
    exact e2

end KPB

open Classical ENNReal NNReal KellyRSN.PartialBalance in
theorem solution
    {S : Type*} [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (q : S → S → ℝ≥0∞) (hq : IsKellyRates q)
    (π : S → ℝ≥0∞) (hπ : IsEquilibriumDist q π)
    (A : Set S) (hA : A.Nonempty) :
    (IsPartialBalance q π A ↔ IsEquilibriumDist (truncRates q A) (condDist π A)) ∧
    (∀ c : ℝ≥0, c ≠ 0 → c ≠ 1 →
      (IsPartialBalance q π A ↔ IsEquilibriumDist (scaleInside q A c) π)) ∧
    (∀ c : ℝ≥0, c ≠ 0 → c ≠ 1 →
      (IsPartialBalance q π A ↔ ∃ B : ℝ≥0∞, IsEquilibriumDist (scaleOutward q A c)
        (fun j => if j ∈ A then B * π j else B * (c : ℝ≥0∞) * π j))) ∧
    (IsPartialBalance q π A ↔ ReversalTruncationCommute q π A) ∧
    (fluxOut q π A ≠ ⊤ → (Aᶜ).Nonempty →
      (IsPartialBalance q π A ↔ SameObservedEquilibrium q A)) := by
  exact KPB.of_vi q hq π hπ A hA (fun hF hAc => KPB.partV q hq π hπ A hA hF hAc)
