-- Prove2me | solution 1 for GlobalTheory.KeyKa.exists_pow_span_X_le_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:31:05.845661+00:00
-- url     : https://prove2.me/submissions/12693e13-93bc-4e0d-bb91-13b9032b3af9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsPowSpanXLeOfDense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KeyKa
namespace GlobalTheory.KeyKa
theorem _root_.solution (K : Type) [Field K] (g N : ℕ)
    (I : Ideal (MvPowerSeries (Fin g) K)) (ρ : Fin N → MvPowerSeries (Fin g) K)
    (h : ∀ (r : ℕ) (G : MvPowerSeries (Fin g) K), ∃ v : Fin N → K,
      G - ∑ k, v k • ρ k ∈ I ⊔ Ideal.span (Set.range MvPowerSeries.X) ^ r) :
    ∃ r : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin g → MvPowerSeries (Fin g) K)) ^ r ≤ I := by
  set J : Ideal (MvPowerSeries (Fin g) K) := Ideal.span (Set.range MvPowerSeries.X) with hJ
  let L : (Fin N → K) →ₗ[K] MvPowerSeries (Fin g) K := Fintype.linearCombination K ρ
  have hL : ∀ v, L v = ∑ k, v k • ρ k := fun v => Fintype.linearCombination_apply K ρ v
  let V : ℕ →o (Submodule K (Fin N → K))ᵒᵈ :=
    ⟨fun r => OrderDual.toDual (((I ⊔ J ^ r).restrictScalars K).comap L), by
      intro a b hab
      change ((I ⊔ J ^ b).restrictScalars K).comap L ≤ ((I ⊔ J ^ a).restrictScalars K).comap L
      intro v hv
      exact (sup_le_sup_left (Ideal.pow_le_pow_right hab) I) hv⟩
  obtain ⟨r, hr⟩ := IsArtinian.monotone_stabilizes V
  have hV : ∀ v, L v ∈ I ⊔ J ^ r → L v ∈ I ⊔ J ^ (r + 1) := by
    intro v hv
    have e : ((I ⊔ J ^ r).restrictScalars K).comap L = ((I ⊔ J ^ (r + 1)).restrictScalars K).comap L :=
      hr (r + 1) (Nat.le_succ r)
    have : v ∈ ((I ⊔ J ^ r).restrictScalars K).comap L := hv
    rw [e] at this
    exact this
  have hfg : J.FG := Submodule.fg_span (Set.finite_range _)
  have hjac : J ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, hJ, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  refine ⟨r, Submodule.le_of_le_smul_of_le_jacobson_bot (N' := J ^ r) (N := I) (I := J)
    (Ideal.FG.pow hfg) hjac ?_⟩
  intro G hG
  obtain ⟨v, hv⟩ := h (r + 1) G
  rw [← hL] at hv
  have h1 : L v ∈ I ⊔ J ^ r := by
    have h2 : G - L v ∈ I ⊔ J ^ r :=
      (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.le_succ r)) I) hv
    have h3 : G ∈ I ⊔ J ^ r := Ideal.mem_sup_right hG
    simpa using Ideal.sub_mem _ h3 h2
  have h4 := Ideal.add_mem _ hv (hV v h1)
  rw [sub_add_cancel, pow_succ'] at h4
  exact h4
end GlobalTheory.KeyKa
