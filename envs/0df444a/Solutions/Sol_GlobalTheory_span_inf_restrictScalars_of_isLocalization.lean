-- Prove2me | solution 1 for GlobalTheory.span_inf_restrictScalars_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:41:03.989279+00:00
-- url     : https://prove2.me/submissions/ce92b0b2-8fdf-4164-845a-0126e093e760

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [Module S M']
  [IsScalarTower R S M']
variable {G : Type*} [Group G]
namespace GlobalTheory
theorem _root_.solution (T : Submonoid R) [IsLocalization T S]
    (L : Submodule R M') (W : Submodule S M') :
    Submodule.span S ((L ⊓ W.restrictScalars R : Submodule R M') : Set M')
      = Submodule.span S (L : Set M') ⊓ W := by
  apply le_antisymm
  · refine le_inf (Submodule.span_mono fun x hx ↦ hx.1) ?_
    rw [Submodule.span_le]; exact fun x hx ↦ hx.2
  · rintro x ⟨hx, hW⟩
    have key : ∀ y ∈ Submodule.span S (L : Set M'), ∃ t : T, (t : R) • y ∈ L := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact ⟨1, by simpa using hy⟩
      | zero => exact ⟨1, by simp⟩
      | add y z _ _ hy hz =>
        obtain ⟨t, ht⟩ := hy
        obtain ⟨u, hu⟩ := hz
        refine ⟨t * u, ?_⟩
        rw [smul_add, Submonoid.coe_mul]
        refine add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact L.smul_mem _ ht
        · rw [mul_smul]; exact L.smul_mem _ hu
      | smul s y _ hy =>
        obtain ⟨t, ht⟩ := hy
        obtain ⟨⟨a, u⟩, hu⟩ := IsLocalization.surj T s
        refine ⟨u * t, ?_⟩
        have : ((u * t : T) : R) • s • y = a • (t : R) • y := by
          rw [← algebraMap_smul S a, ← hu, ← algebraMap_smul S (t : R),
            ← algebraMap_smul S ((u * t : T) : R), smul_smul, smul_smul, Submonoid.coe_mul, map_mul]
          congr 1; ring
        rw [this]; exact L.smul_mem _ ht
    obtain ⟨t, ht⟩ := key x hx
    obtain ⟨v, hv⟩ := IsLocalization.map_units S t
    have : x = (↑v⁻¹ : S) • ((t : R) • x) := by
      rw [← algebraMap_smul S (t : R), ← hv, smul_smul, Units.inv_mul, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨ht, (W.restrictScalars R).smul_mem _ hW⟩)
end GlobalTheory
