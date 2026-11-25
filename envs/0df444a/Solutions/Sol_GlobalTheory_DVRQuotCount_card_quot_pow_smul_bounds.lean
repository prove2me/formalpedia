-- Prove2me | solution 1 for GlobalTheory.DVRQuotCount.card_quot_pow_smul_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:39:38.004674+00:00
-- url     : https://prove2.me/submissions/d87c74f7-d74b-48a7-a8b6-0acc67c624e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardQuotPowSmulBoundsDvrFgModule
import Theorems.Thm_P2M_GlobalTheory_DVRQuotCount_card_quot_smul_top_of_flat__a97c8dac0493
import Theorems.Thm_GlobalTheory_DVRQuotCount_rank_prod_of_rank_zero
import Theorems.Thm_GlobalTheory_DVRQuotCount_irreducible_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open GlobalTheory GlobalTheory.DVRQuotCount
open scoped TensorProduct DirectSum
namespace GlobalTheory.DVRQuotCount
theorem _root_.solution : ∀ (O M : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O M] [Module.Finite O M] (t : O), t ≠ 0 → ¬ IsUnit t →
    (∀ r : ℕ, Finite (O ⧸ Ideal.span {t ^ r})) → ∃ C : ℕ, 0 < C ∧ ∀ r : ℕ,
      Nat.card (O ⧸ Ideal.span {t ^ r}) ^ finrank O M ≤
        Nat.card (M ⧸ (Ideal.span {t ^ r} • ⊤ : Submodule O M)) ∧
      Nat.card (M ⧸ (Ideal.span {t ^ r} • ⊤ : Submodule O M)) ≤
        C * Nat.card (O ⧸ Ideal.span {t ^ r}) ^ finrank O M := by
  intro O M _ _ _ _ _ _ t ht htu hfin
  obtain ⟨n, ι, _, p, hp, e, ⟨eqv⟩⟩ := Module.equiv_free_prod_directSum O M
  set T := ⨁ i : ι, O ⧸ O ∙ p i ^ e i
  set F := Fin n →₀ O

  have hTi : ∀ i, Finite (O ⧸ O ∙ p i ^ e i) := by
    intro i
    have hle : Ideal.span {t ^ e i} ≤ Ideal.span {p i ^ e i} := by
      rw [Ideal.span_singleton_le_span_singleton]
      exact pow_dvd_pow_of_dvd (irreducible_dvd (hp i) ht htu) _
    haveI := hfin (e i)
    exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)
  haveI : Finite T := Finite.of_equiv _ (DirectSum.linearEquivFunOnFintype O ι _).toEquiv.symm

  have hkill : ∀ x : T, ∃ a : O, a ≠ 0 ∧ a • x = 0 := by
    intro x
    refine ⟨∏ i, p i ^ e i, Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hp i).ne_zero, ?_⟩
    ext i
    rw [DirectSum.smul_apply, DirectSum.zero_apply]
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x i)
    rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
      Submodule.mem_span_singleton]
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun j => p j ^ e j) (Finset.mem_univ i)
    exact ⟨c * y, by rw [hc, smul_eq_mul]; ring⟩
  have hrank : finrank O M = n := by
    rw [eqv.finrank_eq]
    unfold Module.finrank
    rw [rank_prod_of_rank_zero hkill]
    change finrank O F = n
    simp [F]
  refine ⟨Nat.card T, Nat.card_pos, fun r => ?_⟩
  set I : Ideal O := Ideal.span {t ^ r}
  haveI := hfin r
  have hcard : Nat.card (M ⧸ (I • ⊤ : Submodule O M)) =
      Nat.card (O ⧸ I) ^ n * Nat.card (T ⧸ (I • ⊤ : Submodule O T)) := by
    rw [← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul M I).toEquiv,
      Nat.card_congr (TensorProduct.congr (LinearEquiv.refl O (O ⧸ I)) eqv).toEquiv,
      Nat.card_congr (TensorProduct.prodRight O O (O ⧸ I) F T).toEquiv, Nat.card_prod,
      Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul F I).toEquiv,
      Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul T I).toEquiv,
      card_quot_smul_top_of_flat']
    simp [F]
  haveI : Finite (T ⧸ (I • ⊤ : Submodule O T)) := Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have h1 : 1 ≤ Nat.card (T ⧸ (I • ⊤ : Submodule O T)) := Nat.card_pos
  have h2 : Nat.card (T ⧸ (I • ⊤ : Submodule O T)) ≤ Nat.card T :=
    Nat.card_le_card_of_surjective _ (Submodule.mkQ_surjective _)
  rw [hcard, hrank]
  constructor
  · exact Nat.le_mul_of_pos_right _ h1
  · rw [mul_comm]; exact Nat.mul_le_mul_right _ h2
end GlobalTheory.DVRQuotCount
