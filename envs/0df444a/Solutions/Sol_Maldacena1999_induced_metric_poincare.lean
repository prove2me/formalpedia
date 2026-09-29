-- Prove2me | solution 1 for Maldacena1999.induced_metric_poincare
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T15:15:14.131642+00:00
-- url     : https://prove2.me/submissions/1f728525-feef-4f0e-83d3-b2c19ca8d105

import Mathlib
import Definitions.Def_Maldacena1999_Defs

set_option autoImplicit false

open Maldacena1999 Filter Topology in
theorem solution (p : ℕ) (R : ℝ) (hR : 0 < R)
    (U : ℝ) (hU : 0 < U) (x : Fin (p + 1) → ℝ) (δ : ℝ × (Fin (p + 1) → ℝ)) :
    ambientForm p (fderiv ℝ (poincareEmbedding p R) (U, x) δ) =
      U ^ 2 / R ^ 2 * minkowskiForm p δ.2 + R ^ 2 * δ.1 ^ 2 / U ^ 2 := by
  classical
  have hU0 : U ≠ 0 := hU.ne'
  have hR0 : R ≠ 0 := hR.ne'
  -- basic coordinate derivatives
  have h1 : HasFDerivAt (fun y : ℝ × (Fin (p + 1) → ℝ) => y.1)
      (ContinuousLinearMap.fst ℝ ℝ (Fin (p + 1) → ℝ)) (U, x) := hasFDerivAt_fst
  have h2 : ∀ j : Fin (p + 1), HasFDerivAt (fun y : ℝ × (Fin (p + 1) → ℝ) => y.2 j)
      ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ ℝ (Fin (p + 1) → ℝ)))
      (U, x) :=
    fun j => by
      have hs : HasFDerivAt (@Prod.snd ℝ (Fin (p + 1) → ℝ))
          (ContinuousLinearMap.snd ℝ ℝ (Fin (p + 1) → ℝ)) (U, x) := hasFDerivAt_snd
      have := (hasFDerivAt_apply (𝕜 := ℝ) j x).comp (U, x) hs
      exact this
  set dm : ℝ := ∑ a : Fin (p + 1), (if a.val = 0 then (-1 : ℝ) else 1) * (2 * x a * δ.2 a)
    with hdm
  set dV : ℝ := (dm * U + minkowskiForm p x * δ.1) / R ^ 2 - R ^ 2 * δ.1 / U ^ 2 with hdV
  -- the Minkowski form
  obtain ⟨Lm, hLm, hLmδ⟩ : ∃ L : (ℝ × (Fin (p + 1) → ℝ)) →L[ℝ] ℝ,
      HasFDerivAt (fun y : ℝ × (Fin (p + 1) → ℝ) => minkowskiForm p y.2) L (U, x) ∧
        L δ = dm := by
    refine ⟨_, HasFDerivAt.fun_sum (u := Finset.univ) (fun a _ => ((h2 a).pow 2).const_mul
      (if a.val = 0 then (-1 : ℝ) else 1)), ?_⟩
    simp only [hdm]
    simp
    refine Finset.sum_congr rfl (fun a _ => ?_)
    split_ifs <;> simp
  -- R^2 / y.1
  obtain ⟨Li, hLi, hLiδ⟩ : ∃ L : (ℝ × (Fin (p + 1) → ℝ)) →L[ℝ] ℝ,
      HasFDerivAt (fun y : ℝ × (Fin (p + 1) → ℝ) => R ^ 2 / y.1) L (U, x) ∧
        L δ = -(R ^ 2 * δ.1 / U ^ 2) := by
    have hd : HasDerivAt (fun t : ℝ => R ^ 2 / t) ((0 * U - R ^ 2 * 1) / U ^ 2) U :=
      (hasDerivAt_const U (R ^ 2)).div (hasDerivAt_id' U) hU0
    refine ⟨_, hd.comp_hasFDerivAt (U, x) h1, ?_⟩
    simp
    ring
  -- V
  obtain ⟨LV, hLV, hLVδ⟩ : ∃ L : (ℝ × (Fin (p + 1) → ℝ)) →L[ℝ] ℝ,
      HasFDerivAt (fun y : ℝ × (Fin (p + 1) → ℝ) =>
        minkowskiForm p y.2 * y.1 / R ^ 2 + R ^ 2 / y.1) L (U, x) ∧ L δ = dV := by
    have hmul := (hLm.fun_mul h1).mul_const ((R ^ 2)⁻¹)
    have e : (fun y : ℝ × (Fin (p + 1) → ℝ) => minkowskiForm p y.2 * y.1 / R ^ 2) =
        (fun y : ℝ × (Fin (p + 1) → ℝ) => minkowskiForm p y.2 * y.1 * (R ^ 2)⁻¹) := by
      funext y; rw [div_eq_mul_inv]
    rw [← e] at hmul
    refine ⟨_, hmul.add hLi, ?_⟩
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, hLmδ, hLiδ,
      ContinuousLinearMap.coe_fst', smul_eq_mul, hdV]
    field_simp
    ring
  -- the three kinds of component
  obtain ⟨LA, hLA, hLAδ⟩ : ∃ L : (ℝ × (Fin (p + 1) → ℝ)) →L[ℝ] ℝ,
      HasFDerivAt (fun y : ℝ × (Fin (p + 1) → ℝ) =>
        (y.1 + (minkowskiForm p y.2 * y.1 / R ^ 2 + R ^ 2 / y.1)) / 2) L (U, x) ∧
        L δ = (δ.1 + dV) / 2 := by
    have h := (h1.add hLV).mul_const ((2 : ℝ)⁻¹)
    refine ⟨_, h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_), ?_⟩
    · simp only [Pi.add_apply]
      ring
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, hLVδ,
      ContinuousLinearMap.coe_fst', smul_eq_mul]
    ring
  obtain ⟨LC, hLC, hLCδ⟩ : ∃ L : (ℝ × (Fin (p + 1) → ℝ)) →L[ℝ] ℝ,
      HasFDerivAt (fun y : ℝ × (Fin (p + 1) → ℝ) =>
        (y.1 - (minkowskiForm p y.2 * y.1 / R ^ 2 + R ^ 2 / y.1)) / 2) L (U, x) ∧
        L δ = (δ.1 - dV) / 2 := by
    have h := (h1.sub hLV).mul_const ((2 : ℝ)⁻¹)
    refine ⟨_, h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_), ?_⟩
    · simp only [Pi.sub_apply]
      ring
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, hLVδ,
      ContinuousLinearMap.coe_fst', smul_eq_mul]
    ring
  have hB : ∀ j : Fin (p + 1), ∃ L : (ℝ × (Fin (p + 1) → ℝ)) →L[ℝ] ℝ,
      HasFDerivAt (fun y : ℝ × (Fin (p + 1) → ℝ) => y.2 j * y.1 / R) L (U, x) ∧
        L δ = (δ.2 j * U + x j * δ.1) / R := by
    intro j
    have h := ((h2 j).fun_mul h1).mul_const R⁻¹
    have e : (fun y : ℝ × (Fin (p + 1) → ℝ) => y.2 j * y.1 / R) =
        (fun y : ℝ × (Fin (p + 1) → ℝ) => y.2 j * y.1 * R⁻¹) := by
      funext y; rw [div_eq_mul_inv]
    rw [← e] at h
    refine ⟨_, h, ?_⟩
    simp
    ring
  -- componentwise derivatives of the embedding
  have hcomp : ∀ i : Fin (p + 3), ∃ L : (ℝ × (Fin (p + 1) → ℝ)) →L[ℝ] ℝ,
      HasFDerivAt (fun y => poincareEmbedding p R y i) L (U, x) ∧
        L δ = (if i.val = 0 then (δ.1 + dV) / 2
          else if h : i.val ≤ p + 1 then
            (δ.2 ⟨i.val - 1, by omega⟩ * U + x ⟨i.val - 1, by omega⟩ * δ.1) / R
          else (δ.1 - dV) / 2) := by
    intro i
    by_cases h0 : i.val = 0
    · refine ⟨LA, ?_, by simp [h0, hLAδ]⟩
      have e : (fun y => poincareEmbedding p R y i) = (fun y : ℝ × (Fin (p + 1) → ℝ) =>
          (y.1 + (minkowskiForm p y.2 * y.1 / R ^ 2 + R ^ 2 / y.1)) / 2) := by
        funext y; simp [poincareEmbedding, h0]
      rw [e]; exact hLA
    · by_cases hle : i.val ≤ p + 1
      · obtain ⟨L, hL, hLδ⟩ := hB ⟨i.val - 1, by omega⟩
        refine ⟨L, ?_, by simp [h0, hle, hLδ]⟩
        have e : (fun y => poincareEmbedding p R y i) = (fun y : ℝ × (Fin (p + 1) → ℝ) =>
            y.2 ⟨i.val - 1, by omega⟩ * y.1 / R) := by
          funext y; simp [poincareEmbedding, h0, hle]
        rw [e]; exact hL
      · refine ⟨LC, ?_, by simp [h0, hle, hLCδ]⟩
        have e : (fun y => poincareEmbedding p R y i) = (fun y : ℝ × (Fin (p + 1) → ℝ) =>
            (y.1 - (minkowskiForm p y.2 * y.1 / R ^ 2 + R ^ 2 / y.1)) / 2) := by
          funext y; simp [poincareEmbedding, h0, hle]
        rw [e]; exact hLC
  choose L hL hLδ using hcomp
  have hF : HasFDerivAt (poincareEmbedding p R) (ContinuousLinearMap.pi L) (U, x) :=
    hasFDerivAt_pi.2 hL
  rw [hF.fderiv]
  have hv : ∀ i, (ContinuousLinearMap.pi L) δ i = L i δ := fun i => rfl
  have hv0 : L 0 δ = (δ.1 + dV) / 2 := by rw [hLδ]; simp
  have hvk : ∀ k : Fin (p + 1), L k.castSucc.succ δ = (δ.2 k * U + x k * δ.1) / R := by
    intro k
    rw [hLδ]
    have hk : (k.castSucc.succ : Fin (p + 3)).val = k.val + 1 := by simp
    have hne : ¬ ((k.castSucc.succ : Fin (p + 3)).val = 0) := by omega
    have hle : (k.castSucc.succ : Fin (p + 3)).val ≤ p + 1 := by omega
    rw [if_neg hne, dif_pos hle]
    simp
  have hvl : L (Fin.last (p + 1)).succ δ = (δ.1 - dV) / 2 := by
    rw [hLδ]
    have hk : ((Fin.last (p + 1)).succ : Fin (p + 3)).val = p + 2 := by simp
    have hne : ¬ (((Fin.last (p + 1)).succ : Fin (p + 3)).val = 0) := by omega
    have hle : ¬ (((Fin.last (p + 1)).succ : Fin (p + 3)).val ≤ p + 1) := by omega
    rw [if_neg hne, dif_neg hle]
  have hs0 : ambientSign p 0 = -1 := by
    unfold ambientSign
    rw [if_pos]
    simp
  have hsk : ∀ k : Fin (p + 1), ambientSign p k.castSucc.succ = if k.val = 0 then -1 else 1 := by
    intro k
    unfold ambientSign
    have hk : (k.castSucc.succ : Fin (p + 3)).val = k.val + 1 := by simp
    by_cases hk0 : k.val = 0
    · have h2' : (k.castSucc.succ : Fin (p + 3)).val < 2 := by omega
      rw [if_pos h2', if_pos hk0]
    · have h2' : ¬ ((k.castSucc.succ : Fin (p + 3)).val < 2) := by omega
      rw [if_neg h2', if_neg hk0]
  have hsl : ambientSign p (Fin.last (p + 1)).succ = 1 := by
    unfold ambientSign
    have hk : ((Fin.last (p + 1)).succ : Fin (p + 3)).val = p + 2 := by simp
    have h2' : ¬ (((Fin.last (p + 1)).succ : Fin (p + 3)).val < 2) := by omega
    rw [if_neg h2']
  have hmid : ∑ k : Fin (p + 1), (if k.val = 0 then (-1 : ℝ) else 1) *
      ((δ.2 k * U + x k * δ.1) / R) ^ 2 =
      U ^ 2 / R ^ 2 * minkowskiForm p δ.2 + δ.1 * U / R ^ 2 * dm +
        δ.1 ^ 2 / R ^ 2 * minkowskiForm p x := by
    simp only [minkowskiForm, hdm, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  unfold ambientForm
  simp only [hv]
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [hv0, hvk, hvl, hs0, hsk, hsl]
  rw [hmid, hdV]
  field_simp
  ring
