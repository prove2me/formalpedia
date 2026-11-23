-- Prove2me | solution 1 for GlobalTheory.LocalFlat.relationsLift_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:00.31289+00:00
-- url     : https://prove2.me/submissions/61cc8d36-cc1e-4b43-822a-5e872d13fc5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open GlobalTheory.LocalFlat
variable {A : Type u} [CommRing A]
variable {M : Type w} [AddCommGroup M] [Module A M]
namespace GlobalTheory.LocalFlat
theorem _root_.solution {I : Ideal A} {C : Type*} [CommRing C] [Algebra A C]
    (hC : Function.Surjective (algebraMap A C)) (hI : RingHom.ker (algebraMap A C) = I)
    {M' : Type*} [AddCommGroup M'] [Module A M'] [Module C M'] [IsScalarTower A C M']
    [Module.Flat C M'] (q : M →ₗ[A] M') (hq : Function.Surjective q)
    (hker : ker q = I • (⊤ : Submodule A M)) : RelationsLift I M := by
  intro F _ _ f x hx
  obtain ⟨k, m, v, rfl⟩ := TensorProduct.exists_sum_tmul_eq x
  rw [← hker, mem_ker] at hx
  have h0 : ∑ i, algebraMap A C (f (v i)) • q (m i) = 0 := by
    simpa [map_sum] using hx
  obtain ⟨l, c, y, hy, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero h0
  choose a ha using fun i j => hC (c i j)
  choose z hz using fun j => hq (y j)
  have hd : ∀ i, m i - ∑ j, a i j • z j ∈ I • (⊤ : Submodule A M) := by
    intro i
    rw [← hker, mem_ker, map_sub, show q (m i) = _ from hy i, map_sum, sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hz, ← ha, algebraMap_smul]
  have hsum : ∑ i, m i ⊗ₜ[A] v i = ∑ i, (m i - ∑ j, a i j • z j) ⊗ₜ[A] v i +
      ∑ j, z j ⊗ₜ[A] (∑ i, a i j • v i) := by
    simp only [sub_tmul, sum_tmul, tmul_sum, smul_tmul, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun j i => z j ⊗ₜ[A] (a i j • v i))]
    abel
  rw [hsum]
  refine add_mem (Submodule.sum_mem _ fun i _ => ?_) (Submodule.sum_mem _ fun j _ => ?_)
  · refine Submodule.smul_induction_on (p := fun d => d ⊗ₜ[A] v i ∈
      range ((Submodule.comap f I).subtype.lTensor M)) (hd i) ?_ ?_
    · intro r hr n _
      refine ⟨n ⊗ₜ ⟨r • v i, ?_⟩, ?_⟩
      · simpa using I.mul_mem_right _ hr
      · simp [smul_tmul]
    · intro d e hd he
      rw [add_tmul]
      exact add_mem hd he
  · refine ⟨z j ⊗ₜ ⟨∑ i, a i j • v i, ?_⟩, by simp⟩
    rw [Submodule.mem_comap, ← hI]
    change algebraMap A C _ = 0
    rw [← hc j]
    simp [map_sum, ha, mul_comm]
end GlobalTheory.LocalFlat
