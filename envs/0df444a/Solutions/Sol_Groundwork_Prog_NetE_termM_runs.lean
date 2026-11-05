-- Prove2me | solution 1 for Groundwork.Prog.NetE.termM_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:01:22.319881+00:00
-- url     : https://prove2.me/submissions/2c198c2e-58cf-4bde-968e-b3509820ddaf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
import Theorems.Thm_Groundwork_Prog_NetE_mem_members
import Theorems.Thm_Groundwork_Prog_NetE_cap_le
import Theorems.Thm_Groundwork_Prog_NetE_cap_symm
import Theorems.Thm_Groundwork_Prog_NetE_valW_runs
import Theorems.Thm_Groundwork_Prog_NetE_valF_runs
import Theorems.Thm_Groundwork_Prog_NetE_psi_natAbs
import Theorems.Thm_Groundwork_Prog_NetE_length_zA
import Theorems.Thm_Groundwork_Prog_NetE_length_labOf
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_const_runs
import Theorems.Thm_Groundwork_Stepped_ite_runs_false
import Theorems.Thm_Groundwork_Stepped_ite_runs_true
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
import Theorems.Thm_Groundwork_Stepped_mul2_runs
import Theorems.Thm_Groundwork_Stepped_sumRange_runs
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
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open Finset Stepped
variable {C : Type} (K g : ℕ) (Np : PNet C)
variable {K g Np} {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {P B t S : ℕ}
variable {x β : ℕ} {G : Fin K} {θ : Fin K → List Bool}
variable [HasSize C]
namespace Groundwork.Prog.NetE
theorem _root_.solution (hN : Np.Presents c N t S) (hS : N.Sized P B) (ht : 1 ≤ t)
    (hβ : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g Np c x G G' ≤ β) (hθ : ∀ G', G' ≠ G → (θ G').length = β)
    (y : ℕ) {i : ℕ} (hi : i < g * g) :
    (termM K g Np).Runs ((((c, x), (G.val, List.ofFn θ)), y), i) (2 ^ P * (2 * t + 2))
      (2 * size ((((c, x), (G.val, List.ofFn θ)), y), i) + 3 * P + 3 * B + S + 12)
      (termVal K g Np N ((((c, x), (G.val, List.ofFn θ)), y), i)) ∧
    (termVal K g Np N ((((c, x), (G.val, List.ofFn θ)), y), i)).natAbs ≤ 2 ^ B := by
  have hg : 0 < g := Nat.pos_of_ne_zero fun h => by simp [h] at hi
  have ha : i / g < g := Nat.div_lt_of_lt_mul hi
  have hb : i % g < g := Nat.mod_lt _ hg
  have h2P : 1 ≤ 2 ^ P := Nat.one_le_two_pow
  have h2B : 1 ≤ 2 ^ B := Nat.one_le_two_pow
  have hst : t ≤ 2 ^ P * (2 * t + 2) := by nlinarith
  cases h1 : isOne K g ((((c, x), (G.val, List.ofFn θ)), y), i) with
  | true =>
    have ev : termVal K g Np N ((((c, x), (G.val, List.ofFn θ)), y), i) = 1 := by
      simp only [termVal, h1, if_true]
    rw [ev]
    refine ⟨(ite_runs_true h1 (const_runs (1 : ℤ) _)).mono (by omega) ?_, by simpa using h2B⟩
    simp only [size_prod, size_nat, size_int]
    have : (1 : ℤ).natAbs.size = 1 := rfl
    omega
  | false =>
    have hcolA : col K x (i / g) = G.val := by
      by_contra hne
      have : isOne K g ((((c, x), (G.val, List.ofFn θ)), y), i) = true := by simp [isOne, hne]
      rw [h1] at this; cases this
    have ham : i / g ∈ members K g x G := (mem_members K g).2 ⟨ha, hcolA⟩
    cases h2 : isW g ((((c, x), (G.val, List.ofFn θ)), y), i) with
    | true =>
      have ev : termVal K g Np N ((((c, x), (G.val, List.ofFn θ)), y), i) = valW N (i / g)
          (zA K g Np (((c, x), (G.val, List.ofFn θ)), y) (i / g)) := by
        simp only [termVal, h1, h2, if_true, if_false, Bool.false_eq_true]
      rw [ev]
      obtain ⟨r1, r2⟩ := valW_runs hN hS ha (length_zA (θs := List.ofFn θ) (y := y) ham)
      exact ⟨(ite_runs_false h1 (ite_runs_true h2 (mapIn_runs r1))).mono hst (by omega), r2⟩
    | false =>
      have hab : i / g ≠ i % g := by
        intro he
        have : isW g ((((c, x), (G.val, List.ofFn θ)), y), i) = true := by simp [isW, he]
        rw [h2] at this; cases this
      cases h3 : isPsi K g ((((c, x), (G.val, List.ofFn θ)), y), i) with
      | false =>
        have hcolB : col K x (i % g) ≠ G.val := by
          intro he
          have : isPsi K g ((((c, x), (G.val, List.ofFn θ)), y), i) = true := by simp [isPsi, he]
          rw [h3] at this; cases this
        have ev : termVal K g Np N ((((c, x), (G.val, List.ofFn θ)), y), i) = valF N (i / g) (i % g)
            (zA K g Np (((c, x), (G.val, List.ofFn θ)), y) (i / g))
            (labOf K g Np ((c, x), (G.val, List.ofFn θ)) (i / g) (i % g)) := by
          simp only [termVal, h1, h2, h3, if_false, Bool.false_eq_true]
        rw [ev]
        obtain ⟨r1, r2⟩ := valF_runs hN hS ha hb hab (length_zA (θs := List.ofFn θ) (y := y) ham)
          (length_labOf hN hS hβ hθ ham hb hcolB)
        exact ⟨(ite_runs_false h1 (ite_runs_false h2 (ite_runs_false h3 (mapIn_runs r1)))).mono hst (by omega), r2⟩
      | true =>
        have hcolB : col K x (i % g) = G.val := by simpa [isPsi] using h3
        have hbm : i % g ∈ members K g x G := (mem_members K g).2 ⟨hb, hcolB⟩
        have hcap : Np.cap c (i / g) (i % g) ≤ P :=
          cap_le hN hS (a := ⟨i / g, ha⟩) (b := ⟨i % g, hb⟩) fun h => hab (congrArg Fin.val h)
        have ev : termVal K g Np N ((((c, x), (G.val, List.ofFn θ)), y), i) = ∑ y' ∈ range (2 ^ Np.cap c (i / g) (i % g)),
            valF N (i / g) (i % g) (zA K g Np (((c, x), (G.val, List.ofFn θ)), y) (i / g))
                (toWord (Np.cap c (i / g) (i % g)) y') *
            valF N (i % g) (i / g) (zA K g Np (((c, x), (G.val, List.ofFn θ)), y) (i % g))
                (toWord (Np.cap c (i / g) (i % g)) y') := by
          simp only [termVal, h1, h2, h3, if_true, if_false, Bool.false_eq_true, nLab]
        rw [ev]
        have hM : ∀ y' < nLab g Np ((((c, x), (G.val, List.ofFn θ)), y), i),
            (mul2 (mapIn (qP1 K g Np) Np.f) (mapIn (qP2 K g Np) Np.f)).Runs (((((c, x), (G.val, List.ofFn θ)), y), i), y')
                (t + 1 + t)
              (size ((((c, x), (G.val, List.ofFn θ)), y), i) + P + B + S + 4)
              (valF N (i / g) (i % g) (zA K g Np (((c, x), (G.val, List.ofFn θ)), y) (i / g))
                  (toWord (Np.cap c (i / g) (i % g)) y') *
               valF N (i % g) (i / g) (zA K g Np (((c, x), (G.val, List.ofFn θ)), y) (i % g))
                   (toWord (Np.cap c (i / g) (i % g)) y')) := by
          intro y' hy'
          obtain ⟨r1, r2⟩ := valF_runs hN hS ha hb hab (length_zA (θs := List.ofFn θ) (y := y) ham)
            (length_toWord (Np.cap c (i / g) (i % g)) y')
          obtain ⟨r3, _⟩ := valF_runs hN hS hb ha hab.symm (length_zA (θs := List.ofFn θ) (y := y) hbm)
            ((length_toWord (Np.cap c (i / g) (i % g)) y').trans (cap_symm hN hS ⟨i / g, ha⟩ ⟨i % g, hb⟩))
          refine (mul2_runs (mapIn_runs (f := qP1 K g Np) (a := (((((c, x), (G.val, List.ofFn θ)), y), i), y')) r1)
            (mapIn_runs (f := qP2 K g Np) (a := (((((c, x), (G.val, List.ofFn θ)), y), i), y')) r3)).mono le_rfl ?_
          have e1 : y'.size ≤ P := (Nat.size_le.2 hy').trans hcap
          have e2 := Nat.size_le_size r2
          rw [Nat.size_pow] at e2
          simp only [size_prod, size_nat, size_int]
          omega
        have hrun := sumRange_runs (N := nLab g Np) (a := ((((c, x), (G.val, List.ofFn θ)), y), i)) (fun _ => t + 1 + t) _
            (2 ^ B * 2 ^ B) _ hM
          (fun y' _ => by
            obtain ⟨_, r2⟩ := valF_runs hN hS ha hb hab (length_zA (θs := List.ofFn θ) (y := y) ham)
              (length_toWord (Np.cap c (i / g) (i % g)) y')
            obtain ⟨_, r4⟩ := valF_runs hN hS hb ha hab.symm (length_zA (θs := List.ofFn θ) (y := y) hbm)
              ((length_toWord (Np.cap c (i / g) (i % g)) y').trans (cap_symm hN hS ⟨i / g, ha⟩ ⟨i % g, hb⟩))
            rw [Int.natAbs_mul]
            exact Nat.mul_le_mul r2 r4)
        refine ⟨(ite_runs_false h1 (ite_runs_false h2 (ite_runs_true h3 hrun))).mono ?_ ?_,
          psi_natAbs hN hS ha hb hab _ _⟩
        · rw [sum_const, card_range, smul_eq_mul]
          exact Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hcap) (by omega)
        · have e : size (nLab g Np ((((c, x), (G.val, List.ofFn θ)), y), i)) = Np.cap c (i / g) (i % g) + 2 := by
            change size (2 ^ Np.cap c (i / g) (i % g)) = _
            simp [Nat.size_pow]
          have e' : size (nLab g Np ((((c, x), (G.val, List.ofFn θ)), y), i) * (2 ^ B * 2 ^ B)) =
              Np.cap c (i / g) (i % g) + (B + B) + 2 := by
            change size (2 ^ Np.cap c (i / g) (i % g) * (2 ^ B * 2 ^ B)) = _
            rw [← pow_add, ← pow_add]
            simp [Nat.size_pow]
          rw [e, e']
          omega
end Groundwork.Prog.NetE
