-- Prove2me | solution 1 for GlobalTheory.Cyc.DiffSmall.exists_moved
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:58:54.950527+00:00
-- url     : https://prove2.me/submissions/21752d71-f9ff-4566-bd43-a74a01377b07

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AvMono
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCycCycChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTraceNormGe
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_norm_gal
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_norm_sub_le_one
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_exists_generator
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_gal_aeval
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_norm_root
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_norm_move_le
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_exists_gal_pow
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_prod_norm_one_sub
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_norm_l_le
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_prod_lift_le
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_exists_lower_bound
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_norm_l_lt_one
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_norm_l_pos
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_mem_Ks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
noncomputable section
open GlobalTheory GlobalTheory.Cyc
open GlobalTheory.Cyc.DiffSmall
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.DiffSmall
theorem _root_.solution (K : FinExt l) {y : Om l} (hy : ‖y‖ ≤ 1) (n : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ < 1) : ∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ (E : IntermediateField ℚ_[l] (Om l))
      [FiniteDimensional ℚ_[l] E], Ks K i ≤ E → y ∈ E → ∀ S : Finset (GQ l), S.card ≤ n →
      (∀ s ∈ S, s ∈ Gj K i) → (∀ h ∈ Gj K i, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ E.fixingSubgroup) →
      ∃ x ∈ E, ‖x‖ ≤ 1 ∧ ∀ σ ∈ Gj K i, σ y ≠ y → δ ≤ ‖x - σ x‖ := by
  have hl : l.Prime := Fact.out
  obtain ⟨c, hc0, hc⟩ := exists_lower_bound hy
  obtain ⟨N₀, hN₀⟩ := exists_pow_lt_of_lt_one (norm_l_pos (l := l)) hδ
  set N := N₀ + n with hN
  have hδN : δ ^ N ≤ ‖(l : Om l)‖ := (pow_le_pow_of_le_one hδ0 hδ.le (by omega)).trans hN₀.le
  obtain ⟨j₀, hj₀⟩ := exists_pow_lt_of_lt_one (pow_pos hc0 N) (norm_l_lt_one (l := l))
  refine ⟨j₀ + 1, fun i hi E _ hKE hyE S hSn hS hu => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  obtain ⟨x, hxE, hx, hgen⟩ := exists_generator E
  refine ⟨x, hxE, hx, fun σ hσ hσy => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  haveI : NeZero (l ^ (j + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ (j + 1))
  have hζ1 : ‖ζ‖ = 1 := norm_root (pow_ne_zero _ hl.ne_zero) hζ.pow_eq_one
  have hζK : ζ ∈ Ks K (j + 1) := mem_Ks K hζ.pow_eq_one
  have hω : IsPrimitiveRoot (ζ ^ l) (l ^ j) := hζ.pow (pow_pos hl.pos _) (by ring)
  have hfixζ : ∀ s ∈ Gj K (j + 1), s ζ = ζ := fun s hs =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs ζ hζK
  have hSne : S.Nonempty := by
    obtain ⟨s, ⟨hs, -⟩, -⟩ := hu 1 (one_mem _)
    exact ⟨s, hs⟩
  have key : ∀ k : ℕ, ∃ g : GQ l, k ∈ Finset.range (l ^ j - 1) →
      g y ≠ y ∧ g ζ = ζ * (ζ ^ l) ^ (k + 1) ∧ ‖x - g x‖ ^ N ≤ ‖1 - (ζ ^ l) ^ (k + 1)‖ := by
    intro k
    by_cases hk : k ∈ Finset.range (l ^ j - 1)
    swap
    · exact ⟨1, fun h => absurd h hk⟩
    rw [Finset.mem_range] at hk
    obtain ⟨τ, hτ, hτζ⟩ := exists_gal_pow K (j + 1) (k + 1) hζ.pow_eq_one
    have hτζ' : τ ζ = ζ * (ζ ^ l) ^ (k + 1) := by rw [hτζ]; ring
    have hnorm : ‖τ ζ - ζ‖ = ‖1 - (ζ ^ l) ^ (k + 1)‖ := by
      rw [hτζ', norm_sub_rev, ← mul_one_sub, norm_mul, hζ1, one_mul]
    have hprod := prod_lift_le (Ks K (j + 1)) E S hS hu hxE hx τ (norm_nonneg _)
      (norm_move_le K hτ (j + 1) (by omega) ζ hζ)
    rw [hnorm] at hprod
    obtain ⟨s, hs, hmin⟩ := Finset.exists_min_image S (fun s => ‖x - τ (s x)‖) hSne
    have hle1 : ‖x - τ (s x)‖ ≤ 1 := norm_sub_le_one hx (by rwa [norm_gal, norm_gal])
    have hA : ‖x - τ (s x)‖ ^ N ≤ ‖1 - (ζ ^ l) ^ (k + 1)‖ := by
      refine (pow_le_pow_of_le_one (norm_nonneg _) hle1 (show S.card ≤ N by omega)).trans ?_
      refine le_trans ?_ hprod
      rw [← Finset.prod_const]
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) hmin
    by_cases hm : τ (s y) = y
    · refine ⟨σ * τ * s, fun _ => ⟨?_, ?_, ?_⟩⟩
      · simpa [hm] using hσy
      · simp only [AlgEquiv.mul_apply]
        rw [hfixζ s (hS s hs), hτζ', map_mul, map_pow, map_pow, hfixζ σ hσ]
      · have hB : ‖x - σ x‖ ^ N ≤ ‖1 - (ζ ^ l) ^ (k + 1)‖ := by
          refine (pow_le_pow_left₀ (norm_nonneg _) hlt.le N).trans (hδN.trans ?_)
          refine norm_l_le j _ ?_ (hω.pow_ne_one_of_pos_of_lt (by omega) (by omega))
          rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
        have hC : ‖x - (σ * τ * s) x‖ ≤ max ‖x - σ x‖ ‖x - τ (s x)‖ := by
          have : x - (σ * τ * s) x = (x - σ x) + σ (x - τ (s x)) := by
            simp only [AlgEquiv.mul_apply, map_sub]; ring
          rw [this, ← norm_gal σ (x - τ (s x))]
          exact IsUltrametricDist.norm_add_le_max _ _
        refine (pow_le_pow_left₀ (norm_nonneg _) hC N).trans ?_
        rcases max_choice ‖x - σ x‖ ‖x - τ (s x)‖ with h | h <;> rw [h]
        exacts [hB, hA]
    · refine ⟨τ * s, fun _ => ⟨hm, ?_, hA⟩⟩
      simp only [AlgEquiv.mul_apply]
      rw [hfixζ s (hS s hs), hτζ']
  choose g hg using key
  obtain ⟨p, hp⟩ := hgen y hyE hy
  obtain ⟨q, hq⟩ := hgen ζ (hKE hζK) hζ1.le
  have hinj : Set.InjOn (fun k => g k x) (Finset.range (l ^ j - 1) : Finset ℕ) := by
    intro a ha b hb hab
    have h1 : g a ζ = g b ζ := by
      rw [← hq, gal_aeval, gal_aeval]
      exact congrArg (fun z => aeval z q) hab
    rw [(hg a ha).2.1, (hg b hb).2.1] at h1
    have h2 := mul_left_cancel₀ (hζ.ne_zero (pow_ne_zero _ hl.ne_zero)) h1
    have ha' := Finset.mem_range.1 ha
    have hb' := Finset.mem_range.1 hb
    have := hω.pow_inj (by omega) (by omega) h2
    omega
  have h1 := hc x p hx hp _ g hinj fun k hk => (hg k hk).1
  have h2 : c ^ N ≤ ‖(l : Om l)‖ ^ j := by
    refine (pow_le_pow_left₀ hc0.le h1 N).trans ?_
    rw [← Finset.prod_pow, ← norm_pow, ← Nat.cast_pow, ← prod_norm_one_sub (pow_pos hl.pos j) hω]
    exact Finset.prod_le_prod (fun _ _ => by positivity) fun k hk => (hg k hk).2.2
  have h3 : ‖(l : Om l)‖ ^ j ≤ ‖(l : Om l)‖ ^ j₀ :=
    pow_le_pow_of_le_one (norm_nonneg _) norm_l_lt_one.le (by omega)
  linarith
end GlobalTheory.Cyc.DiffSmall
