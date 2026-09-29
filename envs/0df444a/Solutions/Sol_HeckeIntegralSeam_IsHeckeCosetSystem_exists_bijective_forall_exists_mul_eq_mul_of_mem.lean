-- Prove2me | solution 1 for HeckeIntegralSeam.IsHeckeCosetSystem.exists_bijective_forall_exists_mul_eq_mul_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/968fb9d3-872c-5863-aa12-eff3ad8f56ac

import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeIntegralSeam_IsHeckeCosetSystem_exists_bijective_forall_exists_mul_eq_mul_of_mem

set_option autoImplicit false

namespace HeckeIntegralSeam
p2m_export "HeckeIntegralSeam" "IsHeckeCosetSystem"
p2m_open "HeckeIntegralSeam"
namespace IsHeckeCosetSystem
p2m_export "HeckeIntegralSeam.IsHeckeCosetSystem" "mk_injective covers mk mem_doubleCoset"
p2m_open "HeckeIntegralSeam.IsHeckeCosetSystem"
namespace KcPermR1

variable {G : Type*} [Group G] {U : Subgroup G} {g : G} {ι₀ : Type*} {reps : ι₀ → G}

theorem exists_mk_mul_eq_mk (hsys : IsHeckeCosetSystem U g reps) {u : G} (hu : u ∈ U) (i : ι₀) :
    ∃ j, (QuotientGroup.mk (u * reps i) : G ⧸ U) = QuotientGroup.mk (reps j) :=
  hsys.covers _ (HeckePair.mul_mem_doubleCoset (hsys.mem_doubleCoset i) hu)

noncomputable def leftPerm (hsys : IsHeckeCosetSystem U g reps) {u : G} (hu : u ∈ U) : ι₀ → ι₀ :=
  fun i => Classical.choose (exists_mk_mul_eq_mk hsys hu i)

theorem mk_mul_eq_mk_leftPerm (hsys : IsHeckeCosetSystem U g reps) {u : G} (hu : u ∈ U) (i : ι₀) :
    (QuotientGroup.mk (u * reps i) : G ⧸ U) = QuotientGroup.mk (reps (leftPerm hsys hu i)) :=
  Classical.choose_spec (exists_mk_mul_eq_mk hsys hu i)

theorem exists_mul_reps_eq (hsys : IsHeckeCosetSystem U g reps) {u : G} (hu : u ∈ U) (i : ι₀) :
    ∃ u' ∈ U, u * reps i = reps (leftPerm hsys hu i) * u' := by
  have h := mk_mul_eq_mk_leftPerm hsys hu i
  rw [QuotientGroup.eq] at h
  refine ⟨(reps (leftPerm hsys hu i))⁻¹ * (u * reps i), ?_, by group⟩
  have := U.inv_mem h
  simpa [mul_inv_rev] using this

theorem leftPerm_injective (hsys : IsHeckeCosetSystem U g reps) {u : G} (hu : u ∈ U) :
    Function.Injective (leftPerm hsys hu) := by
  intro i j hij
  have hi := mk_mul_eq_mk_leftPerm hsys hu i
  have hj := mk_mul_eq_mk_leftPerm hsys hu j
  rw [hij] at hi
  have hmk : (QuotientGroup.mk (u * reps i) : G ⧸ U) = QuotientGroup.mk (u * reps j) :=
    hi.trans hj.symm
  apply hsys.mk_injective
  change (QuotientGroup.mk (reps i) : G ⧸ U) = QuotientGroup.mk (reps j)
  rw [QuotientGroup.eq] at hmk ⊢
  simpa [mul_inv_rev, mul_assoc] using hmk

theorem leftPerm_surjective (hsys : IsHeckeCosetSystem U g reps) {u : G} (hu : u ∈ U) :
    Function.Surjective (leftPerm hsys hu) := by
  intro j
  obtain ⟨i, hi⟩ := exists_mk_mul_eq_mk hsys (U.inv_mem hu) j
  refine ⟨i, ?_⟩
  apply hsys.mk_injective
  change (QuotientGroup.mk (reps (leftPerm hsys hu i)) : G ⧸ U) = QuotientGroup.mk (reps j)
  rw [← mk_mul_eq_mk_leftPerm hsys hu i]
  rw [QuotientGroup.eq] at hi ⊢
  have := U.inv_mem hi
  simpa [mul_inv_rev, mul_assoc] using this

end KcPermR1
end IsHeckeCosetSystem
end HeckeIntegralSeam

open _root_.HeckeIntegralSeam _root_.P2MW.S_HeckeIntegralSeam_IsHeckeCosetSystem_exists_bijective_forall_exists_mul_eq_mul_of_mem.HeckeIntegralSeam _root_.HeckeIntegralSeam.IsHeckeCosetSystem _root_.P2MW.S_HeckeIntegralSeam_IsHeckeCosetSystem_exists_bijective_forall_exists_mul_eq_mul_of_mem.HeckeIntegralSeam.IsHeckeCosetSystem _root_.P2MW.S_HeckeIntegralSeam_IsHeckeCosetSystem_exists_bijective_forall_exists_mul_eq_mul_of_mem.HeckeIntegralSeam.IsHeckeCosetSystem.KcPermR1 in
theorem solution
    {G : Type*} [Group G] {U : Subgroup G} {g : G} {ι₀ : Type*} {reps : ι₀ → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U g reps) (u : G) (hu : u ∈ U) :
    ∃ π : ι₀ → ι₀, Function.Bijective π ∧
      ∀ i : ι₀, ∃ u' ∈ U, u * reps i = reps (π i) * u' :=
  ⟨leftPerm hsys hu, ⟨leftPerm_injective hsys hu, leftPerm_surjective hsys hu⟩,
    fun i => exists_mul_reps_eq hsys hu i⟩

end S_HeckeIntegralSeam_IsHeckeCosetSystem_exists_bijective_forall_exists_mul_eq_mul_of_mem
end P2MW
export P2MW.S_HeckeIntegralSeam_IsHeckeCosetSystem_exists_bijective_forall_exists_mul_eq_mul_of_mem (solution)
