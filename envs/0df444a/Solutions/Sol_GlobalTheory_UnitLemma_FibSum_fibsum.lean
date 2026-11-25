-- Prove2me | solution 1 for GlobalTheory.UnitLemma.FibSum.fibsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:27:14.72544+00:00
-- url     : https://prove2.me/submissions/ac5a6a1e-97dd-4016-9347-bbb0a82595ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardSigmaStableProdLatticeExtSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LieLatticeProdComapInlAndMapSndStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsFullLatticeProdOfComapInlMapSndStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SumStableLatticesProductEqQPowMul
import Theorems.Thm_GlobalTheory_UnitLemma_FibSum_fib_card
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_T_lieLattice_prod_comap_inl_and_map_snd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.FibSum
namespace GlobalTheory.UnitLemma.FibSum
theorem _root_.solution : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.σ B₁.g = B₁.g → B₂.σ B₂.g = B₂.g → (B₁.P * B₂.P).Separable → ∀ (φ₁ : Submodule K.O B₁.A → ℚ) (φ₂ : Submodule K.O B₂.A → ℚ), {M ∈ B₁.Lin | φ₁ M ≠ 0}.Finite → {M ∈ B₂.Lin | φ₂ M ≠ 0}.Finite → {M ∈ (B₁.prod B₂).Lin | φ₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) ≠ 0}.Finite ∧ ∑ᶠ M ∈ (B₁.prod B₂).Lin, φ₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) = (K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P) * ((∑ᶠ M ∈ B₁.Lin, φ₁ M) * ∑ᶠ M ∈ B₂.Lin, φ₂ M) := by
  intro K B₁ B₂ hg₁ hg₂ hsep φ₁ φ₂ hf₁ hf₂
  have hres : resultant B₁.P B₂.P ≠ 0 := resultant_ne_zero _ _ hsep.isCoprime
  set v := val K.O (resultant B₁.P B₂.P) with hv
  set π : Submodule K.O (B₁.prod B₂).A → Submodule K.O B₁.A × Submodule K.O B₂.A := fun M =>
    (M.comap (LinearMap.inl K.O B₁.A B₂.A), M.map (LinearMap.snd K.O B₁.A B₂.A)) with hπ
  suffices key : ∀ F : Submodule K.O (B₁.prod B₂).A → ℚ, (∀ M, F M =
      φ₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ (M.map (LinearMap.snd K.O B₁.A B₂.A))) →
      {M | M ∈ (B₁.prod B₂).Lin ∧ F M ≠ 0}.Finite ∧ ∑ᶠ M ∈ (B₁.prod B₂).Lin, F M =
        (K.q : ℚ) ^ v * ((∑ᶠ M ∈ B₁.Lin, φ₁ M) * ∑ᶠ M ∈ B₂.Lin, φ₂ M) from key _ (fun _ => rfl)
  intro F hF
  set s₁ := hf₁.toFinset
  set s₂ := hf₂.toFinset
  have hs₁ : ∀ M, M ∈ s₁ ↔ M ∈ B₁.Lin ∧ φ₁ M ≠ 0 := fun M => by simp [s₁]
  have hs₂ : ∀ M, M ∈ s₂ ↔ M ∈ B₂.Lin ∧ φ₂ M ≠ 0 := fun M => by simp [s₂]
  have hfibfin : ∀ p ∈ s₁ ×ˢ s₂, {M | M ∈ (B₁.prod B₂).Lin ∧ π M = p}.Finite := by
    intro p hp
    rw [Finset.mem_product, hs₁, hs₂] at hp
    have hc := fib_card K B₁ B₂ hg₁ hg₂ hres p.1 p.2 hp.1.1 hp.2.1
    have hqpos : (0 : ℚ) < K.q := by
      have : 0 < Nat.card (IsLocalRing.ResidueField K.O) := Nat.card_pos
      rw [K.card_res] at this
      exact_mod_cast pos_of_ne_zero (fun h => by simp [h] at this)
    have hne : Nat.card {M : Submodule K.O (B₁.A × B₂.A) // M ∈ (B₁.prod B₂).Lin ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = p.1 ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = p.2} ≠ 0 := by
      intro h0
      rw [h0] at hc
      exact (zpow_pos hqpos v).ne' (by simpa using hc.symm)
    have := Nat.finite_of_card_ne_zero hne
    refine (Set.finite_coe_iff.1 ?_)
    have e : {M | M ∈ (B₁.prod B₂).Lin ∧ π M = p} = {M | M ∈ (B₁.prod B₂).Lin ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = p.1 ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = p.2} := by
      ext M; simp only [Set.mem_setOf_eq, hπ, Prod.ext_iff]
    rw [e]; exact this
  set W := {M | M ∈ (B₁.prod B₂).Lin ∧ π M ∈ s₁ ×ˢ s₂} with hW
  have hWfin : W.Finite := by
    refine (Set.Finite.biUnion (t := fun p => {M | M ∈ (B₁.prod B₂).Lin ∧ π M = p})
      (s₁ ×ˢ s₂).finite_toSet hfibfin).subset ?_
    intro M hM
    exact Set.mem_biUnion (x := π M) hM.2 (show M ∈ {M' | M' ∈ (B₁.prod B₂).Lin ∧ π M' = π M} from ⟨hM.1, rfl⟩)
  have hsupp : ∀ M ∈ (B₁.prod B₂).Lin, F M ≠ 0 → M ∈ W := by
    intro M hM hFM
    have hl := GlobalTheory.T.lieLattice_prod_comap_inl_and_map_snd K B₁ B₂ M hM
    rw [hF M] at hFM
    refine ⟨hM, Finset.mem_product.2 ⟨(hs₁ _).2 ⟨hl.1, left_ne_zero_of_mul hFM⟩,
      (hs₂ _).2 ⟨hl.2, right_ne_zero_of_mul hFM⟩⟩⟩
  refine ⟨hWfin.subset fun M hM => hsupp M hM.1 hM.2, ?_⟩
  have hL : ∑ᶠ M ∈ (B₁.prod B₂).Lin, F M = ∑ M ∈ hWfin.toFinset, F M := by
    have hset : (B₁.prod B₂).Lin ∩ Function.support F = W ∩ Function.support F := by
      ext M
      simp only [Set.mem_inter_iff, Function.mem_support]
      exact ⟨fun h => ⟨hsupp M h.1 h.2, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [← finsum_mem_eq_finite_toFinset_sum _ hWfin, ← finsum_mem_inter_support,
      ← finsum_mem_inter_support (s := W), hset]
  have h1 : ∑ᶠ M ∈ B₁.Lin, φ₁ M = ∑ M ∈ s₁, φ₁ M := by
    have hset : B₁.Lin ∩ Function.support φ₁ = {M | M ∈ B₁.Lin ∧ φ₁ M ≠ 0} ∩ Function.support φ₁ := by
      ext M
      simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨⟨h.1, h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [← finsum_mem_eq_finite_toFinset_sum _ hf₁, ← finsum_mem_inter_support,
      ← finsum_mem_inter_support (s := {M | M ∈ B₁.Lin ∧ φ₁ M ≠ 0}), hset]
  have h2 : ∑ᶠ M ∈ B₂.Lin, φ₂ M = ∑ M ∈ s₂, φ₂ M := by
    have hset : B₂.Lin ∩ Function.support φ₂ = {M | M ∈ B₂.Lin ∧ φ₂ M ≠ 0} ∩ Function.support φ₂ := by
      ext M
      simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨⟨h.1, h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [← finsum_mem_eq_finite_toFinset_sum _ hf₂, ← finsum_mem_inter_support,
      ← finsum_mem_inter_support (s := {M | M ∈ B₂.Lin ∧ φ₂ M ≠ 0}), hset]
  rw [hL, h1, h2, ← Finset.sum_fiberwise_of_maps_to (s := hWfin.toFinset) (t := s₁ ×ˢ s₂) (g := π)
    (fun M hM => ((Set.Finite.mem_toFinset hWfin).1 hM).2), Finset.sum_mul_sum, ← Finset.sum_product', Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hin : ∀ M ∈ hWfin.toFinset.filter (fun M => π M = p), F M = φ₁ p.1 * φ₂ p.2 := by
    intro M hM
    have hM' := (Finset.mem_filter.1 hM).2
    rw [hF, ← hM']
  rw [Finset.sum_congr rfl hin, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hp' := hp
  rw [Finset.mem_product, hs₁, hs₂] at hp'
  rw [← fib_card K B₁ B₂ hg₁ hg₂ hres p.1 p.2 hp'.1.1 hp'.2.1]
  congr 1
  rw [← Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro M
  simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, hW, hπ, Prod.ext_iff]
  constructor
  · rintro ⟨⟨h, _⟩, h'⟩; exact ⟨h, h'⟩
  · rintro ⟨h, h'⟩
    refine ⟨⟨h, ?_⟩, h'⟩
    rw [Finset.mem_product]; rw [h'.1, h'.2]; exact Finset.mem_product.1 hp
end GlobalTheory.UnitLemma.FibSum
