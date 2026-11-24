-- Prove2me | solution 1 for GlobalTheory.exists_highest_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:41:25.840798+00:00
-- url     : https://prove2.me/submissions/e40fe34a-fe63-40fe-baeb-0bc0052758ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsJointIntEigenvectorOfStable
import Theorems.Thm_GlobalTheory_exists_joint_int_eigenvector_of_stable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K V T : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] [Fintype T] [DecidableEq T] {m : ℕ}
    (e : T → Fin m → Fin m → Module.End K V)
    (he : ∀ t t' i k l, e t i i * e t' k l - e t' k l * e t i i = (if t = t' then ((if i = k then 1 else 0) - (if i = l then 1 else 0) : K) else 0) • e t' k l)
    (hdiag : ⨆ κ : T → Fin m → ℤ, (⨅ t, ⨅ i, Module.End.eigenspace (e t i i) (κ t i : K)) = ⊤)
    (W : Submodule K V) [FiniteDimensional K W] (hW : ∀ t i j, ∀ w ∈ W, e t i j w ∈ W) (hW0 : W ≠ ⊥) :
    ∃ v ∈ W, v ≠ 0 ∧ (∀ t i j, i < j → e t i j v = 0) ∧ ∃ κ : T → Fin m → ℤ, ∀ t i, e t i i v = (κ t i : K) • v := by
  classical

  obtain ⟨κ₀, u₀, hu₀W, hu₀, hκ₀⟩ := exists_joint_int_eigenvector_of_stable
    (fun a : T × Fin m => e a.1 a.2 a.2)
    (by
      intro a b
      have := he a.1 b.1 a.2 b.2 b.2
      rw [sub_self, ite_self, zero_smul] at this
      exact sub_eq_zero.mp this)
    (by
      intro a
      rw [eq_top_iff, ← hdiag]
      refine iSup_le fun κ => ?_
      exact le_trans ((iInf_le _ a.1).trans (iInf_le _ a.2))
        (le_iSup (fun n : ℤ => (e a.1 a.2 a.2).eigenspace (n : K)) (κ a.1 a.2)))
    W (fun a => hW a.1 a.2 a.2) hW0

  let ht : (T → Fin m → ℤ) → ℤ := fun κ => ∑ t, ∑ i : Fin m, (i : ℤ) * κ t i
  let h : Module.End K V := ∑ t, ∑ i : Fin m, ((i : ℕ) : K) • e t i i
  have hhW : ∀ w ∈ W, h w ∈ W := by
    intro w hw
    simp only [h, LinearMap.sum_apply, LinearMap.smul_apply]
    exact W.sum_mem fun t _ => W.sum_mem fun i _ => W.smul_mem _ (hW t i i w hw)
  have hh : ∀ (κ : T → Fin m → ℤ) (v : V), (∀ t i, e t i i v = (κ t i : K) • v) →
      h v = (ht κ : K) • v := by
    intro κ v hv
    simp only [h, ht, LinearMap.sum_apply, LinearMap.smul_apply, hv, smul_smul]
    push_cast
    simp only [Finset.sum_smul]
  let S : Set ℤ := {n | ∃ κ : T → Fin m → ℤ, ht κ = n ∧
    ∃ v ∈ W, v ≠ 0 ∧ ∀ t i, e t i i v = (κ t i : K) • v}
  have hS : S.Finite := by
    have hfin := Module.End.finite_hasEigenvalue (h.restrict hhW)
    refine (hfin.preimage (f := fun n : ℤ => (n : K)) Int.cast_injective.injOn).subset ?_
    rintro n ⟨κ, rfl, v, hvW, hv0, hv⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvW⟩) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact Subtype.ext (hh κ v hv)
    · exact fun h0 => hv0 (congrArg Subtype.val h0)
  have hSne : S.Nonempty :=
    ⟨_, fun t i => κ₀ (t, i), rfl, u₀, hu₀W, hu₀, fun t i => hκ₀ (t, i)⟩
  obtain ⟨n, ⟨κ, rfl, v, hvW, hv0, hv⟩, hmin⟩ := Set.exists_min_image S id hS hSne
  refine ⟨v, hvW, hv0, ?_, κ, hv⟩
  intro t' k l hkl
  by_contra hne
  let δ : T → Fin m → ℤ := fun t i =>
    if t = t' then ((if i = k then 1 else 0) - (if i = l then 1 else 0)) else 0
  have hmem : ht (κ + δ) ∈ S := by
    refine ⟨κ + δ, rfl, e t' k l v, hW _ _ _ v hvW, hne, fun t i => ?_⟩
    have h1 := LinearMap.congr_fun (he t t' i k l) v
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hv,
      map_smul] at h1
    rw [sub_eq_iff_eq_add] at h1
    rw [h1, ← add_smul, add_comm]
    congr 1
    simp only [δ, Pi.add_apply]
    push_cast
    rfl
  have hδ : ht δ = (k : ℤ) - (l : ℤ) := by
    simp only [ht, δ]
    rw [Finset.sum_eq_single t']
    · simp [mul_sub, Finset.sum_sub_distrib]
    · intro b _ hb; simp [hb]
    · simp
  have hadd : ht (κ + δ) = ht κ + ht δ := by
    simp only [ht, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have h2 := hmin _ hmem
  have h3 : (k : ℕ) < l := hkl
  simp only [id] at h2
  omega
end GlobalTheory
