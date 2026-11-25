-- Prove2me | solution 1 for GlobalTheory.Chevalley.exists_le_sup_maximalIdeal_pow_of_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:29:14.384221+00:00
-- url     : https://prove2.me/submissions/58e57716-36e3-421b-b439-47d7de311c02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNoetherianRingAdicCompletionOfNoetherian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLeMaximalIdealPowSmulOfDirected
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChevalleyExistsLeSupMaximalIdealPowOfAntitone
import Theorems.Thm_GlobalTheory_Chevalley_exists_sub_algebraMap_mem_maximalIdeal_pow_adicCompletion
import Theorems.Thm_GlobalTheory_AdicNoeth_isNoetherianRing_adicCompletion
import Theorems.Thm_GlobalTheory_Chevalley_exists_le_maximalIdeal_pow_smul_of_directed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.Chevalley
namespace GlobalTheory.Chevalley
theorem _root_.solution :
    ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (K : ℕ → Ideal A) (J : Ideal A),
      Antitone K → (∀ e, maximalIdeal A ^ e ≤ K e) →
      (∀ (F : AdicCompletion (maximalIdeal A) A) (a : ℕ → A),
        (∀ n, F - algebraMap A (AdicCompletion (maximalIdeal A) A) (a n) ∈
          maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n) →
        (∀ n, a n ∈ K n) → F ∈ J.map (algebraMap A (AdicCompletion (maximalIdeal A) A))) →
      ∀ k : ℕ, ∃ e : ℕ, K e ≤ J ⊔ maximalIdeal A ^ k := by
  intro A _ _ _ K J hK hmK hJ k
  let B := AdicCompletion (maximalIdeal A) A
  haveI : IsNoetherianRing B := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion A _
  haveI : Module.Flat A B := AdicCompletion.flat_of_isNoetherian _
  haveI : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let f := algebraMap A B
  have hmB : ∀ n, maximalIdeal B ^ n = (maximalIdeal A ^ n).map f := fun n ↦ by
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_pow]
  let K' : ℕ → Ideal B := fun e ↦ (K e).map f
  have hK' : Antitone K' := fun i j hij ↦ Ideal.map_mono (hK hij)
  have hmK' : ∀ e, maximalIdeal B ^ e ≤ K' e := fun e ↦ by
    rw [hmB]; exact Ideal.map_mono (hmK e)
  let N : Ideal B := ⨅ e, K' e
  have hNK : ∀ e, N ≤ K' e := fun e ↦ iInf_le _ e
  have hNJ : N ≤ J.map f := by
    intro F hF
    choose a ha using exists_sub_algebraMap_mem_maximalIdeal_pow_adicCompletion A F
    refine hJ F a ha fun n ↦ ?_
    have h1 : f (a n) ∈ K' n := by
      have : f (a n) = F - (F - f (a n)) := by abel
      rw [this]
      exact Submodule.sub_mem _ (hNK n hF) (hmK' n (ha n))
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (K n)]
    exact h1
  let P : ℕ → Submodule B (B ⧸ N) := fun e ↦ Submodule.map (Submodule.mkQ N) (K' e : Submodule B B)
  have hdir : Directed (· ≥ ·) P := fun i j ↦
    ⟨max i j, Submodule.map_mono (hK' (le_max_left i j)), Submodule.map_mono (hK' (le_max_right i j))⟩
  have hbot : (⨅ e, P e) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective N x
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rw [Submodule.mem_iInf] at hx ⊢
    intro e
    have := Submodule.mem_comap.2 (hx e)
    rw [Submodule.comap_map_mkQ, sup_eq_right.2 (hNK e)] at this
    exact this
  obtain ⟨e, he⟩ := exists_le_maximalIdeal_pow_smul_of_directed B (B ⧸ N) ℕ P ⟨0⟩ hdir hbot k
  refine ⟨e, ?_⟩
  have hsm : (maximalIdeal B ^ k • (⊤ : Submodule B (B ⧸ N))) =
      Submodule.map (Submodule.mkQ N) (maximalIdeal B ^ k : Submodule B B) := by
    have hI : (maximalIdeal B ^ k • (⊤ : Submodule B B)) = (maximalIdeal B ^ k : Submodule B B) := by
      rw [smul_eq_mul, Ideal.mul_top]
    rw [← Submodule.range_mkQ N, LinearMap.range_eq_map, ← Submodule.map_smul'', hI]
  have h2 : K' e ≤ maximalIdeal B ^ k ⊔ N := by
    intro y hy
    have h := he (Submodule.mem_map_of_mem (f := Submodule.mkQ N) hy)
    rw [hsm] at h
    have h' : y ∈ Submodule.comap (Submodule.mkQ N)
        (Submodule.map (Submodule.mkQ N) (maximalIdeal B ^ k : Submodule B B)) := h
    rw [Submodule.comap_map_mkQ] at h'
    rw [sup_comm]; exact h'
  have h3 : K' e ≤ (J ⊔ maximalIdeal A ^ k).map f := by
    rw [Ideal.map_sup, ← hmB]
    exact h2.trans (sup_le le_sup_right (hNJ.trans le_sup_left))
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (J ⊔ maximalIdeal A ^ k)]
  exact Ideal.map_le_iff_le_comap.1 h3
end GlobalTheory.Chevalley
