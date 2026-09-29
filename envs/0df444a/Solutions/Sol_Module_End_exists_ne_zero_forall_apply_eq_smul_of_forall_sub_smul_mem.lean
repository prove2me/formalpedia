-- Prove2me | solution 1 for Module.End.exists_ne_zero_forall_apply_eq_smul_of_forall_sub_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/b48c3ced-ba1b-51d1-a5ec-96c13f473a94

import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Artinian.Module
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_End_exists_ne_zero_forall_apply_eq_smul_of_forall_sub_smul_mem
set_option autoImplicit false

namespace QuotEigenLift

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

private theorem pow_apply_mem {P : Submodule K V} {f : Module.End K V} (hf : ∀ x ∈ P, f x ∈ P) :
    ∀ (k : ℕ) (x : V), x ∈ P → (f ^ k) x ∈ P := by
  intro k
  induction k with
  | zero => intro x hx; simpa using hx
  | succ k ih =>
    intro x hx
    rw [pow_succ', Module.End.mul_apply]
    exact hf _ (ih x hx)

private theorem pow_apply_comm {f g : Module.End K V} (h : ∀ x, f (g x) = g (f x)) :
    ∀ (k : ℕ) (x : V), (f ^ k) (g x) = g ((f ^ k) x) := by
  intro k
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih, h]

private theorem exists_common_ker [FiniteDimensional K V] {ι : Type*} (S : ι → Module.End K V)
    (hS : ∀ (i j : ι) (x : V), S i (S j x) = S j (S i x)) :
    ∀ (n : ℕ) (U : Submodule K V), Module.finrank K U ≤ n → U ≠ ⊥ →
      (∀ i, ∀ x ∈ U, S i x ∈ U) → (∀ i, ∀ x ∈ U, ∃ k : ℕ, (S i ^ k) x = 0) →
      ∃ u ∈ U, u ≠ 0 ∧ ∀ i, S i u = 0 := by
  intro n
  induction n with
  | zero =>
    intro U hU hU0 _ _
    exact absurd (Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hU)) hU0
  | succ n ih =>
    intro U hU hU0 hstab hnil
    by_cases hall : ∀ i, ∀ x ∈ U, S i x = 0
    · obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
      exact ⟨u, huU, hu0, fun i => hall i u huU⟩
    · obtain ⟨i₀, x₀, hx₀U, hx₀⟩ : ∃ (i : ι) (x : V), x ∈ U ∧ ¬ S i x = 0 := by
        simpa only [not_forall, Classical.not_imp, exists_prop] using hall
      have hx₀0 : x₀ ≠ 0 := fun h0 => hx₀ (by rw [h0, map_zero])
      have hlt : U ⊓ LinearMap.ker (S i₀) < U := by
        refine lt_of_le_of_ne inf_le_left fun h => hx₀ ?_
        have hmem : x₀ ∈ U ⊓ LinearMap.ker (S i₀) := by rw [h]; exact hx₀U
        exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hmem).2
      have hrank : Module.finrank K ↥(U ⊓ LinearMap.ker (S i₀)) ≤ n :=
        Nat.lt_succ_iff.mp (lt_of_lt_of_le (Submodule.finrank_lt_finrank_of_lt hlt) hU)
      have hne : U ⊓ LinearMap.ker (S i₀) ≠ ⊥ := by
        intro hbot
        obtain ⟨k, hk⟩ := hnil i₀ x₀ hx₀U
        have key : ∀ m : ℕ, (S i₀ ^ m) x₀ ∈ U ∧ ¬ (S i₀ ^ m) x₀ = 0 := by
          intro m
          induction m with
          | zero => exact ⟨by simpa using hx₀U, by simpa using hx₀0⟩
          | succ m ihm =>
            refine ⟨?_, fun h0 => ihm.2 ?_⟩
            · rw [pow_succ', Module.End.mul_apply]
              exact hstab i₀ _ ihm.1
            · have hmem : (S i₀ ^ m) x₀ ∈ U ⊓ LinearMap.ker (S i₀) := by
                refine Submodule.mem_inf.mpr ⟨ihm.1, ?_⟩
                rw [LinearMap.mem_ker, ← Module.End.mul_apply, ← pow_succ']
                exact h0
              rw [hbot] at hmem
              exact (Submodule.mem_bot K).mp hmem
        exact (key k).2 hk
      have hstab' : ∀ i, ∀ x ∈ U ⊓ LinearMap.ker (S i₀), S i x ∈ U ⊓ LinearMap.ker (S i₀) := by
        intro i x hx
        obtain ⟨hxU, hxk⟩ := Submodule.mem_inf.mp hx
        refine Submodule.mem_inf.mpr ⟨hstab i x hxU, ?_⟩
        rw [LinearMap.mem_ker] at hxk ⊢
        rw [hS i₀ i x, hxk, map_zero]
      have hnil' : ∀ i, ∀ x ∈ U ⊓ LinearMap.ker (S i₀), ∃ k : ℕ, (S i ^ k) x = 0 :=
        fun i x hx => hnil i x (Submodule.mem_inf.mp hx).1
      obtain ⟨u, hu, hu0, hker⟩ := ih _ hrank hne hstab' hnil'
      exact ⟨u, (Submodule.mem_inf.mp hu).1, hu0, hker⟩

end QuotEigenLift

open QuotEigenLift in

theorem solution
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {ι : Type*} (T : ι → Module.End K V) (hT : ∀ i j, Commute (T i) (T j))
    (W : Submodule K V) (hW : ∀ i, ∀ w ∈ W, T i w ∈ W)
    (mu : ι → K) (v : V) (hv : v ∉ W) (heig : ∀ i, T i v - mu i • v ∈ W) :
    ∃ u : V, u ≠ 0 ∧ ∀ i, T i u = mu i • u := by
  classical

  obtain ⟨S, hSx⟩ : ∃ S : ι → Module.End K V, ∀ (i : ι) (x : V), S i x = T i x - mu i • x :=
    ⟨fun i => T i - mu i • 1, fun i x => by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]⟩
  have hTx : ∀ (i j : ι) (x : V), T i (T j x) = T j (T i x) := fun i j x => by
    simpa only [Module.End.mul_apply] using LinearMap.congr_fun (hT i j).eq x
  have hSS : ∀ (i j : ι) (x : V), S i (S j x) = S j (S i x) := by
    intro i j x
    simp only [hSx, map_sub, map_smul, smul_sub, smul_smul, hTx i j x, mul_comm (mu i) (mu j)]
    abel
  have hWS : ∀ i, ∀ w ∈ W, S i w ∈ W := by
    intro i w hw
    rw [hSx]
    exact W.sub_mem (hW i w hw) (W.smul_mem _ hw)
  have hvS : ∀ i, S i v ∈ W := fun i => by rw [hSx]; exact heig i

  have hex : ∃ d : ℕ, ∃ P : Submodule K V, Module.finrank K P = d ∧ (∀ i, ∀ x ∈ P, S i x ∈ P) ∧
      ∃ p ∈ P, p ∉ W ∧ ∀ i, S i p ∈ W :=
    ⟨_, ⊤, rfl, fun i x _ => Submodule.mem_top, v, Submodule.mem_top, hv, hvS⟩
  obtain ⟨P₀, hP₀d, hP₀S, p, hpP, hpW, hpS⟩ := Nat.find_spec hex
  have hmin : ∀ P : Submodule K V, (∀ i, ∀ x ∈ P, S i x ∈ P) →
      (∃ q ∈ P, q ∉ W ∧ ∀ i, S i q ∈ W) → Module.finrank K P₀ ≤ Module.finrank K P := by
    intro P h1 h2
    rw [hP₀d]
    exact Nat.find_min' hex ⟨P, rfl, h1, h2⟩

  have hP₁le : W ⊓ P₀ ⊔ Submodule.span K {p} ≤ P₀ :=
    sup_le inf_le_right ((Submodule.span_singleton_le_iff_mem p P₀).mpr hpP)
  have hP₁S : ∀ i, ∀ x ∈ W ⊓ P₀ ⊔ Submodule.span K {p}, S i x ∈ W ⊓ P₀ := by
    intro i x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    obtain ⟨hyW, hyP⟩ := Submodule.mem_inf.mp hy
    rw [map_add, map_smul]
    exact Submodule.add_mem _ (Submodule.mem_inf.mpr ⟨hWS i y hyW, hP₀S i y hyP⟩)
      (Submodule.smul_mem _ c (Submodule.mem_inf.mpr ⟨hpS i, hP₀S i p hpP⟩))
  have hP₁eq : W ⊓ P₀ ⊔ Submodule.span K {p} = P₀ :=
    Submodule.eq_of_le_of_finrank_le hP₁le (hmin _ (fun i x hx => Submodule.mem_sup_left (hP₁S i x hx))
      ⟨p, Submodule.mem_sup_right (Submodule.mem_span_singleton_self p), hpW, hpS⟩)
  have hSW : ∀ i, ∀ x ∈ P₀, S i x ∈ W := by
    intro i x hx
    have hx' : x ∈ W ⊓ P₀ ⊔ Submodule.span K {p} := by rw [hP₁eq]; exact hx
    exact (Submodule.mem_inf.mp (hP₁S i x hx')).1

  have hnil : ∀ i, ∀ x ∈ P₀, ∃ k : ℕ, (S i ^ k) x = 0 := by
    intro i₀ x₀ hx₀
    by_contra hcon
    simp only [not_exists] at hcon
    obtain ⟨n, hn : ∀ m, n ≤ m → Submodule.map (S i₀ ^ n) P₀ = Submodule.map (S i₀ ^ m) P₀⟩ :=
      IsArtinian.monotone_stabilizes
        (⟨fun m => Submodule.map (S i₀ ^ m) P₀, fun m m' hle x hx => by
          obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
          have hx' : x ∈ Submodule.map (S i₀ ^ (m + k)) P₀ := hx
          obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx'
          show (S i₀ ^ (m + k)) y ∈ Submodule.map (S i₀ ^ m) P₀
          exact Submodule.mem_map.mpr ⟨(S i₀ ^ k) y, pow_apply_mem (hP₀S i₀) k y hy,
            by rw [pow_add, Module.End.mul_apply]⟩⟩ : ℕ →o (Submodule K V)ᵒᵈ)
    have hn1 : Submodule.map (S i₀ ^ (n + 1)) P₀ = Submodule.map (S i₀ ^ (n + 1 + (n + 1))) P₀ := by
      rw [← hn (n + 1) (Nat.le_succ n), ← hn (n + 1 + (n + 1)) (by omega)]
    obtain ⟨y, hyP, hy⟩ : ∃ y ∈ P₀, (S i₀ ^ (n + 1 + (n + 1))) y = (S i₀ ^ (n + 1)) p := by
      have hmem : (S i₀ ^ (n + 1)) p ∈ Submodule.map (S i₀ ^ (n + 1 + (n + 1))) P₀ := by
        rw [← hn1]
        exact Submodule.mem_map_of_mem hpP
      exact Submodule.mem_map.mp hmem
    have hSny : (S i₀ ^ (n + 1)) y ∈ P₀ := pow_apply_mem (hP₀S i₀) _ y hyP
    have hSy : (S i₀ ^ (n + 1)) y ∈ W := by
      rw [pow_succ', Module.End.mul_apply]
      exact hSW i₀ _ (pow_apply_mem (hP₀S i₀) n y hyP)
    have hgood : (∀ i, ∀ x ∈ P₀ ⊓ LinearMap.ker (S i₀ ^ (n + 1)),
        S i x ∈ P₀ ⊓ LinearMap.ker (S i₀ ^ (n + 1))) ∧
        ∃ q ∈ P₀ ⊓ LinearMap.ker (S i₀ ^ (n + 1)), q ∉ W ∧ ∀ i, S i q ∈ W := by
      refine ⟨fun i x hx => ?_, p - (S i₀ ^ (n + 1)) y, ?_, ?_, ?_⟩
      · obtain ⟨hxP, hxk⟩ := Submodule.mem_inf.mp hx
        refine Submodule.mem_inf.mpr ⟨hP₀S i x hxP, ?_⟩
        rw [LinearMap.mem_ker] at hxk ⊢
        rw [pow_apply_comm (hSS i₀ i) (n + 1) x, hxk, map_zero]
      · refine Submodule.mem_inf.mpr ⟨Submodule.sub_mem _ hpP hSny, ?_⟩
        rw [LinearMap.mem_ker, map_sub, ← hy, ← Module.End.mul_apply, ← pow_add, sub_self]
      · intro hmem
        exact hpW (by simpa using W.add_mem hmem hSy)
      · intro i
        rw [map_sub]
        exact W.sub_mem (hpS i) (hSW i _ hSny)
    have hlt : P₀ ⊓ LinearMap.ker (S i₀ ^ (n + 1)) < P₀ := by
      refine lt_of_le_of_ne inf_le_left fun h => hcon (n + 1) ?_
      have hmem : x₀ ∈ P₀ ⊓ LinearMap.ker (S i₀ ^ (n + 1)) := by rw [h]; exact hx₀
      exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hmem).2
    exact absurd (hmin _ hgood.1 hgood.2) (not_le.mpr (Submodule.finrank_lt_finrank_of_lt hlt))

  have hP₀ne : P₀ ≠ ⊥ := by
    intro h
    rw [h] at hpP
    exact hpW (by rw [(Submodule.mem_bot K).mp hpP]; exact W.zero_mem)
  obtain ⟨u, -, hu0, hu⟩ := exists_common_ker S hSS (Module.finrank K P₀) P₀ le_rfl hP₀ne hP₀S hnil
  exact ⟨u, hu0, fun i => sub_eq_zero.mp ((hSx i u).symm.trans (hu i))⟩

end S_Module_End_exists_ne_zero_forall_apply_eq_smul_of_forall_sub_smul_mem
end P2MW
export P2MW.S_Module_End_exists_ne_zero_forall_apply_eq_smul_of_forall_sub_smul_mem (solution)
