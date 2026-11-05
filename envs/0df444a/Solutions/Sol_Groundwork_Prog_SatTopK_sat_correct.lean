-- Prove2me | solution 1 for Groundwork.Prog.SatTopK.sat_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:57:23.962639+00:00
-- url     : https://prove2.me/submissions/3a5f163d-692d-499d-93a8-583bc4760268

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_StepMachines_Prog_Comb
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Math_SparsifyTree
import Definitions.Def_KSatStatement
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_WidthK_Top_Sat
import Theorems.Thm_Groundwork_Prog_SatTopK_size_fml_le
import Theorems.Thm_Groundwork_Prog_SatTopK_length_enc
import Theorems.Thm_Groundwork_Prog_SatTopK_final_bound
import Theorems.Thm_Groundwork_Decode_length_enc
import Theorems.Thm_Groundwork_Decode_length_toN
import Theorems.Thm_Groundwork_Decode_mem_toN
import Theorems.Thm_Groundwork_Decode_nil_mem_toN
import Theorems.Thm_Groundwork_Decode_satN_toN
import Theorems.Thm_Groundwork_Prog_size_list_le
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_const_runs
import Theorems.Thm_Groundwork_Stepped_ite_runs_false
import Theorems.Thm_Groundwork_Stepped_ite_runs_true
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
import Theorems.Thm_Groundwork_Stepped_mapOut_runs
import Theorems.Thm_Groundwork_Stepped_walk_runs
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit



set_option autoImplicit false
section
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK
open Groundwork.Sparsify (leaves)
namespace Groundwork.Prog.SatTopK
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : 0 ≤ δ')
    {dec : List Bool → ℕ × Fml} {step : Fml → Option (Fml × Fml)} {root : Fml → Fml} {Dd Bl Sk : ℕ}
    (hdec : ∀ (n : ℕ) (φ : Sat3.CNF n), (∀ C ∈ φ, C.length ≤ k) → dec (SatK.enc k φ) = (n, Decode.toN φ))
    (hsp : Sparsifies k (δ / 3) step root Dd Bl Sk) (hδB : δ' * Bl ≤ δ / 3) (M : Stepped Fml ℤ) (A : ℕ)
    (hM : ∀ φ : Fml, (∀ C ∈ φ, C.length ≤ k) →
      ∃ (T : ℕ) (v : ℤ), M.Runs φ T (A * size φ ^ A) v ∧ (0 < v ↔ φ.Sat) ∧
        (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * φ.length)) :
    ∃ c : ℕ, ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF k φ →
      ∃ (T : ℕ) (b : Bool), (satMK dec step root M).Runs (SatK.enc k φ) T (c * ((SatK.enc k φ).length + 1) ^ c) b ∧
        (b = true ↔ Sat3.Satisfiable φ) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n) := by
  classical
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 4 * k + 2 := ⟨_, rfl⟩
  obtain ⟨P₁, hP₁⟩ : ∃ P₁, P₁ = Bl * Q + 1 := ⟨_, rfl⟩
  obtain ⟨P₂, hP₂⟩ : ∃ P₂, P₂ = (Dd + 1) * (Sk * Q + 2) + 1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = cOf P₁ P₂ Q A := ⟨_, rfl⟩
  refine ⟨c, fun n φ h3 => ?_⟩
  obtain ⟨N, hN⟩ : ∃ N, N = (SatK.enc k φ).length + 1 := ⟨_, rfl⟩
  rw [← hN]
  have h1 : 1 ≤ N := by omega
  have hlen := length_enc k φ
  have hn : n ≤ N := by omega
  have hm : φ.length ≤ N := by
    have hB : 0 < k * (Nat.log2 (2 * n) + 1) := Nat.mul_pos hk (by omega)
    have := Nat.le_mul_of_pos_right φ.length hB
    omega
  obtain ⟨hb1, hb2⟩ := final_bound P₁ P₂ Q A N h1
  rw [← hc] at hb1 hb2
  have hdec' : decF dec (SatK.enc k φ) = Decode.toN φ := by rw [decF, hdec n φ h3.1]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Fml, ψ = Decode.toN φ := ⟨_, rfl⟩
  rw [← hψ] at hdec'
  have hψl : ψ.length ≤ N := by rw [hψ, Decode.length_toN]; exact hm
  have hψcl : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n := by
    intro D hD
    obtain ⟨⟨C, hC, hl⟩, h⟩ := Decode.mem_toN (hψ ▸ hD)
    exact ⟨hl ▸ h3.1 C hC, h⟩
  have hq : k * (n + 2 + 1) + 1 + 1 ≤ Q * N := by
    have a1 : k * (n + 2 + 1) ≤ k * (4 * N) := Nat.mul_le_mul_left _ (by omega)
    have a2 : Q * N = k * (4 * N) + 2 * N := by rw [hQ]; ring
    omega
  have hN2 : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ h1
  have hN3 : 1 ≤ N ^ 3 := Nat.one_le_pow _ _ h1
  have hc2 : ((A : ℝ) + 2) ≤ (c : ℝ) := by
    have : A + 2 ≤ c := by rw [hc]; unfold cOf; omega
    exact_mod_cast this
  have hδn : 0 ≤ δ * (n : ℝ) := by positivity
  have hE1 : (1 : ℝ) ≤ (2 : ℝ) ^ (δ * n) := Real.one_le_rpow one_le_two hδn
  have hnilψ : hasNil ψ = true ↔ [] ∈ φ := by
    rw [← Decode.nil_mem_toN, ← hψ]
    simp [hasNil, List.any_eq_true]
  by_cases hnil : [] ∈ φ
  · refine ⟨1, false, ?_, ?_, ?_⟩
    · have r : (Stepped.ite hasNil (Stepped.const false)
          (Stepped.walk step root (Stepped.mapOut M posZ))).Runs (decF dec (SatK.enc k φ)) 1
          (max (size ψ) (size false) + 1 + 1) false := by
        rw [hdec']
        exact Stepped.ite_runs_true (hnilψ.2 hnil) (Stepped.const_runs false ψ)
      refine (Stepped.mapIn_runs r).mono le_rfl ?_
      have hs := size_fml_le hψl hψcl
      have : N * (k * (n + 2 + 1) + 1 + 1) ≤ Q * N ^ 2 := by
        calc N * (k * (n + 2 + 1) + 1 + 1) ≤ N * (Q * N) := Nat.mul_le_mul_left _ hq
          _ = Q * N ^ 2 := by ring
      rw [size_bool]
      omega
    · simp only [Bool.false_eq_true, false_iff]
      rintro ⟨a, ha⟩
      obtain ⟨l, hl, -⟩ := ha [] hnil
      simp at hl
    · have : (1 : ℝ) ≤ (c : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) A]
      push_cast
      nlinarith
  · have hψne : ∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n := by
      intro C hC
      refine ⟨?_, hψcl C hC⟩
      rintro rfl
      exact hnil ((Decode.nil_mem_toN φ).1 (hψ ▸ hC))
    obtain ⟨t1, t2, t3, t4⟩ := hsp n ψ hψne
    obtain ⟨L, hL⟩ : ∃ L, L = leaves step (Dd * n) (root ψ) := ⟨_, rfl⟩
    rw [← hL] at t1 t2 t3
    obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ (δ / 3 * n) := ⟨_, rfl⟩
    have hE0 : 1 ≤ E := by rw [hE]; exact Real.one_le_rpow one_le_two (by positivity)
    have hLE : (L.length : ℝ) ≤ E := by rw [hE]; exact t1
    have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
    have hT : ∀ x ∈ L, (Stepped.mapOut M posZ).Runs x ⌊(A : ℝ) * E⌋₊ (A * (P₁ * N ^ 2) ^ A)
        (decide (Fml.Sat x)) := by
      intro x hx
      obtain ⟨-, hxl, hxc⟩ := t2 x hx
      obtain ⟨T, v, r, hv, hTle⟩ := hM x fun C hC => (hxc C hC).1
      have e : decide (Fml.Sat x) = posZ v := by
        rw [posZ]; exact decide_eq_decide.2 hv.symm
      rw [e]
      refine (Stepped.mapOut_runs r).mono (Nat.le_floor (hTle.trans ?_))
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ A))
      · refine mul_le_mul_of_nonneg_left ?_ hA0
        rw [hE]
        refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
        have hxl' : (x.length : ℝ) ≤ (Bl : ℝ) * n := by exact_mod_cast hxl
        calc δ' * x.length ≤ δ' * ((Bl : ℝ) * n) := mul_le_mul_of_nonneg_left hxl' hδ'
          _ = δ' * Bl * n := by ring
          _ ≤ δ / 3 * n := mul_le_mul_of_nonneg_right hδB (Nat.cast_nonneg n)
      · refine (size_fml_le hxl hxc).trans ?_
        calc Bl * n * (k * (n + 2 + 1) + 1 + 1) + 1
            ≤ Bl * N * (Q * N) + 1 :=
              Nat.succ_le_succ (Nat.mul_le_mul (Nat.mul_le_mul_left _ hn) hq)
          _ = Bl * Q * N ^ 2 + 1 := by ring
          _ ≤ Bl * Q * N ^ 2 + N ^ 2 := Nat.add_le_add_left hN2 _
          _ = P₁ * N ^ 2 := by rw [hP₁]; ring
    have hS : ∀ i, size ((Sparsify.round step)^[i] ([root ψ], [])).1 ≤ P₂ * N ^ 3 := by
      intro i
      obtain ⟨s1, s2⟩ := t4 i
      have hf : ∀ x ∈ ((Sparsify.round step)^[i] ([root ψ], [])).1, size x ≤ (Sk * Q + 1) * N ^ 2 := by
        intro x hx
        refine (size_fml_le (s2 x hx).1 (s2 x hx).2).trans ?_
        calc ψ.length * Sk * (k * (n + 2 + 1) + 1 + 1) + 1
            ≤ N * Sk * (Q * N) + 1 := Nat.succ_le_succ (Nat.mul_le_mul (Nat.mul_le_mul_right _ hψl) hq)
          _ = Sk * Q * N ^ 2 + 1 := by ring
          _ ≤ Sk * Q * N ^ 2 + N ^ 2 := Nat.add_le_add_left hN2 _
          _ = (Sk * Q + 1) * N ^ 2 := by ring
      refine (size_list_le s1 hf).trans ?_
      have hp : Dd * n + 1 ≤ (Dd + 1) * N := by
        have a1 : Dd * n ≤ Dd * N := Nat.mul_le_mul_left _ hn
        have a3 : (Dd + 1) * N = Dd * N + N := by ring
        omega
      have hp2 : (Sk * Q + 1) * N ^ 2 + 1 ≤ (Sk * Q + 2) * N ^ 2 := by
        have a3 : (Sk * Q + 2) * N ^ 2 = (Sk * Q + 1) * N ^ 2 + N ^ 2 := by ring
        omega
      calc (Dd * n + 1) * ((Sk * Q + 1) * N ^ 2 + 1) + 1
          ≤ (Dd + 1) * N * ((Sk * Q + 2) * N ^ 2) + 1 := Nat.succ_le_succ (Nat.mul_le_mul hp hp2)
        _ = (Dd + 1) * (Sk * Q + 2) * N ^ 3 + 1 := by ring
        _ ≤ (Dd + 1) * (Sk * Q + 2) * N ^ 3 + N ^ 3 := Nat.add_le_add_left hN3 _
        _ = P₂ * N ^ 3 := by rw [hP₂]; ring
    have w := Stepped.walk_runs step (root := root) (T := Stepped.mapOut M posZ) (Dd * n) ψ
      (fun x hx => (t2 x (hL ▸ hx)).1) (fun x => decide (Fml.Sat x)) ⌊(A : ℝ) * E⌋₊ (A * (P₁ * N ^ 2) ^ A)
      (P₂ * N ^ 3) (fun x hx => hT x (hL ▸ hx)) hS
    rw [← hL] at w
    refine ⟨L.length * (⌊(A : ℝ) * E⌋₊ + 2), L.any fun x => decide (Fml.Sat x), ?_, ?_, ?_⟩
    · have r : (Stepped.ite hasNil (Stepped.const false)
          (Stepped.walk step root (Stepped.mapOut M posZ))).Runs (decF dec (SatK.enc k φ))
          (L.length * (⌊(A : ℝ) * E⌋₊ + 2))
          (P₂ * N ^ 3 + (1 + (A * (P₁ * N ^ 2) ^ A + 1)) + 1 + 1)
          (L.any fun x => decide (Fml.Sat x)) := by
        rw [hdec']
        exact Stepped.ite_runs_false (by simpa using fun h => hnil (hnilψ.1 h)) w
      exact (Stepped.mapIn_runs r).mono le_rfl (by omega)
    · rw [← Decode.satN_toN, ← hψ]
      simp only [List.any_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨x, hx, a, ha⟩
        exact ⟨a, (t3 fun l => a l.1 = l.2).2 ⟨x, hx, ha⟩⟩
      · rintro ⟨a, ha⟩
        obtain ⟨x, hx, h⟩ := (t3 fun l => a l.1 = l.2).1 ha
        exact ⟨x, hx, a, h⟩
    · have hfl : ((⌊(A : ℝ) * E⌋₊ : ℕ) : ℝ) ≤ (A : ℝ) * E := Nat.floor_le (by positivity)
      have hEE : E * E ≤ (2 : ℝ) ^ (δ * n) := by
        rw [hE, ← Real.rpow_add two_pos]
        refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
        nlinarith
      have hE00 : 0 ≤ E := by linarith
      push_cast
      calc (L.length : ℝ) * (((⌊(A : ℝ) * E⌋₊ : ℕ) : ℝ) + 2)
          ≤ E * ((A : ℝ) * E + 2 * E) :=
            mul_le_mul hLE (by linarith) (by positivity) hE00
        _ = ((A : ℝ) + 2) * (E * E) := by ring
        _ ≤ (c : ℝ) * (2 : ℝ) ^ (δ * n) :=
            mul_le_mul hc2 hEE (by positivity) (Nat.cast_nonneg _)
end Groundwork.Prog.SatTopK
