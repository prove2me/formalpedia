-- Prove2me | solution 1 for GlobalTheory.nakayama_at_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:23:54.585243+00:00
-- url     : https://prove2.me/submissions/8642c09e-104e-4495-a4c1-0588569821e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeSupKerMulOfLeSupMaximalMulSection

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
namespace GlobalTheory
theorem _root_.solution : ∀ (O P : Type) [CommRing O] [IsLocalRing O] [CommRing P] [Algebra O P] (η : P →ₐ[O] O) (J S : Ideal P), J.FG → J ≤ S ⊔ (IsLocalRing.maximalIdeal O).comap η * J → J ≤ S ⊔ RingHom.ker η * J := by
  intro O P _ _ _ _ η J S hJ h
  set S' : Ideal P := S ⊔ RingHom.ker η * J with hS'
  set n : Ideal P := (IsLocalRing.maximalIdeal O).comap η with hn
  have hK : (Submodule.map S'.mkQ J).FG := Submodule.FG.map _ hJ
  have hle : Submodule.map S'.mkQ J ≤ n • Submodule.map S'.mkQ J := by
    rw [← Submodule.map_smul'']
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp (h hj)
    refine Submodule.mem_map.mpr ⟨t, ht, ?_⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    have : t - (s + t) = -s := by ring
    rw [this]
    exact S'.neg_mem (Ideal.mem_sup_left hs)
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul n _ hK hle
  intro j hj
  have h1 : r * j ∈ S' := by
    have := hr _ (Submodule.mem_map_of_mem hj)
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    simpa using this
  have hu : IsUnit (η r) := by
    by_contra hne
    have a : η r ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hne
    have b : η r - 1 ∈ IsLocalRing.maximalIdeal O := by
      have := Ideal.mem_comap.mp hr1
      simpa [map_sub] using this
    have c : (1:O) ∈ IsLocalRing.maximalIdeal O := by
      have := sub_mem a b
      simpa using this
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr c)
  obtain ⟨u, hu'⟩ := hu
  have hk : r - algebraMap O P (η r) ∈ RingHom.ker η := by
    rw [RingHom.mem_ker]
    simp
  have h2 : (r - algebraMap O P (η r)) * j ∈ S' := Ideal.mem_sup_right (Ideal.mul_mem_mul hk hj)
  have h3 : algebraMap O P (η r) * j ∈ S' := by
    have e : algebraMap O P (η r) * j = r * j - (r - algebraMap O P (η r)) * j := by ring
    rw [e]
    exact S'.sub_mem h1 h2
  have h4 : algebraMap O P (↑u⁻¹) * (algebraMap O P (η r) * j) ∈ S' := S'.mul_mem_left _ h3
  rwa [← mul_assoc, ← map_mul, ← hu', Units.inv_mul, map_one, one_mul] at h4
end GlobalTheory
