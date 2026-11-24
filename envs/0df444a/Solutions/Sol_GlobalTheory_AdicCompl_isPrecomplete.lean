-- Prove2me | solution 1 for GlobalTheory.AdicCompl.isPrecomplete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:26:17.131844+00:00
-- url     : https://prove2.me/submissions/37bbaa87-bd85-49bb-8669-08af55432694

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NumberFieldFinitePlaceCompletionEmbedding
import Theorems.Thm_GlobalTheory_AdicCompl_lt_one_iff_le
import Theorems.Thm_GlobalTheory_AdicCompl_exists_unif
import Theorems.Thm_GlobalTheory_AdicCompl_mem_max_pow_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory
open Formalism.L2.Pj Formalism.L2.PjFree
open IsDedekindDomain NumberField HeightOneSpectrum Filter
open scoped WithZero Topology
open GlobalTheory.AdicCompl
variable {R : Type} [CommRing R] [IsDedekindDomain R] {L : Type} [Field L] [Algebra R L]
  [IsFractionRing R L] (w : HeightOneSpectrum R)
local notation "Lw" => adicCompletion L w
local notation "Ow" => adicCompletionIntegers L w
namespace GlobalTheory.AdicCompl
theorem _root_.solution : IsPrecomplete (IsLocalRing.maximalIdeal Ow) Ow := by
  obtain ⟨π, hπ⟩ := exists_unif (L := L) w
  have hπ1 : Valued.v (π : Lw) < 1 := (lt_one_iff_le _).2 hπ.le
  have hπ0 : (π : Lw) ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  refine ⟨fun f hf => ?_⟩
  simp only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, mem_max_pow_iff w hπ] at hf ⊢
  let g : ℕ → Lw := fun n => (f n : Lw)
  have hc : Cauchy (map g atTop) := by
    rw [Valued.cauchy_iff]
    refine ⟨map_neBot, fun γ => ?_⟩
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hπ1 (Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
      (f := (.ofClass (Valued.v : Valuation Lw ℤᵐ⁰)))) γ)
    refine ⟨g '' Set.Ici n, image_mem_map (Ici_mem_atTop n), ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [Valuation.restrict_lt_iff_lt_embedding]
    refine lt_of_le_of_lt ?_ hn
    have h1 := hf (m := n) (n := a) ha
    have h2 := hf (m := n) (n := b) hb
    have e : g b - g a = ((f n - f a : Ow) : Lw) - ((f n - f b : Ow) : Lw) := by
      simp only [g]; push_cast; ring
    rw [e]
    exact Valuation.map_sub_le _ h1 h2
  obtain ⟨l, hl⟩ := CompleteSpace.complete hc
  have key : ∀ n, Valued.v (g n - l) ≤ Valued.v (π : Lw) ^ n := by
    intro n
    have hU : {y : Lw | (Valued.v : Valuation Lw ℤᵐ⁰).restrict (y - l) <
        (Valued.v : Valuation Lw ℤᵐ⁰).restrict ((π : Lw) ^ n)} ∈ 𝓝 l := by
      rw [Valued.mem_nhds]
      exact ⟨Units.mk0 ((Valued.v : Valuation Lw ℤᵐ⁰).restrict ((π : Lw) ^ n)) (by simp [hπ0]),
        subset_rfl⟩
    have hm := hl hU
    rw [mem_map, mem_atTop_sets] at hm
    obtain ⟨N, hN⟩ := hm
    have h1 : (Valued.v : Valuation Lw ℤᵐ⁰).restrict (g (max N n) - l) <
        (Valued.v : Valuation Lw ℤᵐ⁰).restrict ((π : Lw) ^ n) := hN (max N n) (le_max_left _ _)
    rw [Valuation.restrict_lt_iff, map_pow] at h1
    have h2 := hf (m := n) (n := max N n) (le_max_right N n)
    have e : g n - l = ((f n - f (max N n) : Ow) : Lw) + (g (max N n) - l) := by
      simp only [g]; push_cast; ring
    rw [e]
    exact Valuation.map_add_le _ h2 h1.le
  have hl1 : l ∈ Ow := by
    have e : l = g 0 - (g 0 - l) := by ring
    rw [e]
    exact sub_mem (f 0).2 ((mem_adicCompletionIntegers R L w).2 (by simpa using key 0))
  exact ⟨⟨l, hl1⟩, fun n => key n⟩
end GlobalTheory.AdicCompl
