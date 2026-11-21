-- Prove2me | solution 1 for MasulloGRH.bounded_stage_of_null_sequence_lifting
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:58:13.164478+00:00
-- url     : https://prove2.me/submissions/fb225a1c-e0ce-4ea6-b006-5b023ea7e4eb

import Mathlib

open Set Filter Bornology Topology
open scoped Pointwise

theorem solution
    (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (P : ℕ → Type*) [∀ n, AddCommGroup (P n)] [∀ n, Module ℂ (P n)]
    [∀ n, TopologicalSpace (P n)] [∀ n, ContinuousSMul ℂ (P n)]
    (j : ∀ n, P n →ₗ[ℂ] E) (hinj : ∀ n, Function.Injective (j n))
    (hseq : ∀ u : ℕ → E, Tendsto u atTop (𝓝 0) →
      ∃ (n : ℕ) (v : ℕ → P n), Tendsto v atTop (𝓝 0) ∧ ∀ k, j n (v k) = u k)
    (B : Set E) (hB : IsVonNBounded ℂ B) :
    ∃ (n : ℕ) (A : Set (P n)), IsVonNBounded ℂ A ∧ B ⊆ j n '' A := by
  classical
  by_contra h
  have bad (n : ℕ) : ∃ W ∈ 𝓝 (0 : P n), Balanced ℂ W ∧
      ∀ c : ℂ, c ≠ 0 → ∃ x ∈ B, x ∉ j n '' (c • W) := by
    by_contra! hn
    have lift (W : Set (P n)) (hW : W ∈ 𝓝 0) (hb : Balanced ℂ W) :
        ∃ c : ℂ, c ≠ 0 ∧ B ⊆ j n '' (c • W) := by
      simpa [Set.subset_def] using hn W hW hb
    obtain ⟨d,hd,hcov⟩ := lift univ univ_mem balanced_univ
    have hcover : B ⊆ j n '' (j n ⁻¹' B) := by
      intro x hx
      obtain ⟨y,hy,he⟩ := hcov hx
      exact ⟨y,show j n y ∈ B from he ▸ hx,he⟩
    apply h ⟨n,j n ⁻¹' B,?_,hcover⟩
    rw [(nhds_basis_balanced ℂ (P n)).isVonNBounded_iff]
    intro W hW
    obtain ⟨c,hc,hcB⟩ := lift W hW.1 hW.2
    apply Absorbs.of_norm
    refine ⟨‖c‖,fun a ha y hy => ?_⟩
    obtain ⟨z,hz,hez⟩ := hcB hy
    exact hW.2.smul_mono ha ((hinj n hez) ▸ hz)
  choose W hW hb hbad using bad
  let c (k : ℕ) : ℂ := ((k+1:ℕ):ℂ)
  have hc (k:ℕ) : c k ≠ 0 := by dsimp [c]; exact_mod_cast Nat.succ_ne_zero k
  choose x hx hxout using fun k : ℕ => hbad k.unpair.1 (c k) (hc k)
  have ht : Tendsto (fun k : ℕ => (c k)⁻¹) atTop (𝓝 0) := by
    have hr : Tendsto (fun k : ℕ => ((k+1:ℕ):ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    simpa [c,Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp hr
  let u (k : ℕ) := (c k)⁻¹ • x k
  have hu : Tendsto u atTop (𝓝 0) := hB.smul_tendsto_zero (Eventually.of_forall hx) ht
  obtain ⟨n,v,hv,hj⟩ := hseq u hu
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hv.eventually_mem (hW n))
  let k := Nat.pair n N
  have hnk : Nat.unpair k = (n,N) := Nat.unpair_pair n N
  have hvk : v k ∈ W n := hN k (Nat.right_le_pair _ _)
  have hmem : x k ∈ j n '' (c k • W n) := by
    refine ⟨c k • v k, ⟨v k,hvk,rfl⟩,?_⟩
    rw [map_smul,hj]
    exact smul_inv_smul₀ (hc k) _
  have hcontra := hxout k
  rw [hnk] at hcontra
  exact hcontra hmem

