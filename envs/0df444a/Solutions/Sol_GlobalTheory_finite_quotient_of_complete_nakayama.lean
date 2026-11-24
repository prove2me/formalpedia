-- Prove2me | solution 1 for GlobalTheory.finite_quotient_of_complete_nakayama
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:50:10.640135+00:00
-- url     : https://prove2.me/submissions/d12f1175-3efc-4ad4-b1e4-94378b3fe654

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteQuotientOfCompleteNakayama

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ {R : Type} [CommRing R] (ϖ : R), (∀ x : ℕ → R, ∃ a : R, ∀ n : ℕ, ∃ b : R, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) → ∀ {T Z : Type} [AddCommGroup T] [Module R T] [AddCommGroup Z] [Module R Z], (∀ x : ℕ → T, ∃ y : T, ∀ n : ℕ, ∃ z : T, y - ∑ j ∈ Finset.range n, ϖ ^ j • x j = ϖ ^ n • z) → (∀ c : Z, (∀ n : ℕ, ∃ z : Z, c = ϖ ^ n • z) → c = 0) → ∀ (d : T →ₗ[R] Z) (N : Submodule R Z), LinearMap.range d ≤ N → ∀ s : Finset Z, (∀ c : Z, ∃ (a : Z → R) (c' : Z) (x : T), c = ∑ i ∈ s, a i • i + ϖ • c' + d x) → Module.Finite R (Z ⧸ N) := by
  intro R _ ϖ hR T Z _ _ _ _ hT hZ d N hdN s hs
  classical
  choose A C X hACX using hs
  choose limR hlimR using hR
  choose limT hlimT using hT
  have key : ∀ c : Z, ∀ n : ℕ, c = ∑ i ∈ s, (∑ j ∈ Finset.range n, ϖ ^ j * A (C^[j] c) i) • i
      + ϖ ^ n • C^[n] c + d (∑ j ∈ Finset.range n, ϖ ^ j • X (C^[j] c)) := by
    intro c n
    induction n with
    | zero => simp
    | succ n ih =>
      refine ih.trans ?_
      rw [Finset.sum_range_succ, Function.iterate_succ_apply']
      simp only [Finset.sum_range_succ]
      set e := C^[n] c with he
      conv_lhs => rw [hACX e]
      simp only [add_smul, Finset.sum_add_distrib, smul_add, map_add, map_smul, Finset.smul_sum,
        mul_smul, pow_succ]
      abel
  have hfin : ∀ c : Z, c - (∑ i ∈ s, limR (fun j => A (C^[j] c) i) • i
      + d (limT (fun j => X (C^[j] c)))) = 0 := by
    intro c
    apply hZ
    intro n
    have hk := key c n
    choose b hb using fun i => hlimR (fun j => A (C^[j] c) i) n
    obtain ⟨z, hz⟩ := hlimT (fun j => X (C^[j] c)) n
    refine ⟨C^[n] c - ∑ i ∈ s, b i • i - d z, ?_⟩
    have hα : ∀ i, limR (fun j => A (C^[j] c) i)
        = (∑ j ∈ Finset.range n, ϖ ^ j * A (C^[j] c) i) + ϖ ^ n * b i :=
      fun i => sub_eq_iff_eq_add'.mp (hb i)
    have hY := sub_eq_iff_eq_add'.mp hz
    simp only [hα, hY]
    rw [sub_eq_iff_eq_add]
    refine hk.trans ?_
    simp only [add_smul, Finset.sum_add_distrib, smul_sub, map_add, map_smul, Finset.smul_sum,
      mul_smul]
    abel
  have h0 : ∀ y : T, N.mkQ (d y) = 0 := by
    intro y
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hdN ⟨y, rfl⟩
  refine ⟨⟨s.image N.mkQ, ?_⟩⟩
  rw [eq_top_iff]
  rintro q -
  obtain ⟨c, rfl⟩ := N.mkQ_surjective q
  have hc := sub_eq_zero.mp (hfin c)
  rw [hc, map_add, h0, add_zero, map_sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hi)))
end GlobalTheory
