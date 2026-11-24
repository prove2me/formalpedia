-- Prove2me | solution 1 for GlobalTheory.FreeQuotient.exists_invariant_dual_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:52:48.580972+00:00
-- url     : https://prove2.me/submissions/4f2a2703-f5d8-4775-907c-d677ff182bd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Theorems.Thm_GlobalTheory_FreeQuotient_averageMap_apply
import Theorems.Thm_GlobalTheory_FreeQuotient_averageMap_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.FreeQuotient
variable {G : Type*} [Group G] [Fintype G] {A : Type*} [CommRing A] [MulSemiringAction G A]
  {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
  {N : Type*} [AddCommGroup N] [Module A N] [DistribMulAction G N] [SMulDistribClass G A N]
namespace GlobalTheory.FreeQuotient
theorem _root_.solution [Module.Finite A M] [Module.Projective A M]
    {c : A} (hc : ∑ g : G, g • c = 1)
    (hM : Submodule.span A {m : M | ∀ g : G, g • m = m} = ⊤) :
    ∃ (n : ℕ) (v : Fin n → M) (f : Fin n → M →ₗ[A] A), (∀ i (g : G), g • v i = v i) ∧
      (∀ i (g : G) m, f i (g • m) = g • f i m) ∧ ∀ m, ∑ i, f i m • v i = m := by
  classical
  obtain ⟨t, ht, ht'⟩ := (Submodule.fg_span_iff_fg_span_finset_subset
    (R := A) {m : M | ∀ g : G, g • m = m}).mp (hM ▸ Module.Finite.fg_top)
  let v : Fin t.card → M := fun i ↦ t.equivFin.symm i
  have hv : ∀ i (g : G), g • v i = v i := fun i ↦ ht (t.equivFin.symm i).2
  have hsurj : Function.Surjective (Fintype.linearCombination A v) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, eq_top_iff, ← hM, ht']
    exact Submodule.span_mono fun x hx ↦ ⟨t.equivFin ⟨x, hx⟩, by simp [v]⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property _ LinearMap.id hsurj
  have hs' : ∀ m, ∑ i, s m i • v i = m := fun m ↦ by
    simpa [Fintype.linearCombination_apply] using LinearMap.congr_fun hs m
  refine ⟨t.card, v, fun i ↦ averageMap G (c • (LinearMap.proj i ∘ₗ s)), hv,
    fun i g m ↦ averageMap_smul _ g m, fun m ↦ ?_⟩
  simp only [averageMap_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  have : ∀ g : G, ∑ i, (g • (c • (LinearMap.proj i ∘ₗ s : M →ₗ[A] A)) (g⁻¹ • m)) • v i =
      (g • c) • m := fun g ↦ by
    conv_rhs => rw [← smul_inv_smul g m, ← smul_distrib_smul, ← hs' (g⁻¹ • m)]
    simp only [Finset.smul_sum, smul_distrib_smul, hv]
    simp [mul_smul]
  simp only [this]
  rw [← Finset.sum_smul, hc, one_smul]
end GlobalTheory.FreeQuotient
