-- Prove2me | solution 1 for GlobalTheory.OnePoint.exists_algHom_ker_eq_nilradical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:29:25.09815+00:00
-- url     : https://prove2.me/submissions/0460f3d6-c22f-4be5-87fa-d6964921fd65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
import Theorems.Thm_GlobalTheory_OnePoint_exists_algHom_ker_eq_of_isMaximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.OnePoint
universe u v w
variable {K : Type u} [Field K]
namespace GlobalTheory.OnePoint
theorem _root_.solution [PerfectField K] {A : Type v} [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] [Nontrivial A] (Ω : Type w) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (h : ∀ a b : A →ₐ[K] Ω, a = b) : ∃ φ : A →ₐ[K] K, RingHom.ker φ = nilradical A := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  have huniq : ∀ n : Ideal A, n.IsMaximal → n = m := fun n hn ↦ by
    obtain ⟨φ, hφ⟩ := exists_algHom_ker_eq_of_isMaximal (K := K) Ω m
    obtain ⟨ψ, hψ⟩ := exists_algHom_ker_eq_of_isMaximal (K := K) Ω n
    rw [← hφ, ← hψ, h φ ψ]
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K)
  have hnil : nilradical A = m := by
    rw [nilradical, Submodule.zero_eq_bot, Ideal.radical_eq_jacobson, Ideal.jacobson]
    refine le_antisymm (sInf_le ⟨bot_le, hm⟩) (le_sInf ?_)
    rintro n ⟨-, hn⟩
    exact (huniq n hn).ge
  let := Ideal.Quotient.field m
  have : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  have hsub : Subsingleton ((A ⧸ m) →ₐ[K] Ω) := ⟨fun a b ↦ Ideal.Quotient.algHom_ext K (h _ _)⟩
  have hcard : Module.finrank K (A ⧸ m) ≤ 1 := by
    rw [← AlgHom.card K (A ⧸ m) Ω]
    exact Fintype.card_le_one_iff_subsingleton.mpr hsub
  have hone : Module.finrank K (A ⧸ m) = 1 := le_antisymm hcard Module.finrank_pos
  have hbij : Function.Bijective (algebraMap K (A ⧸ m)) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hone
  let e : K ≃ₐ[K] (A ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId K _) hbij
  refine ⟨(e.symm : (A ⧸ m) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K m), ?_⟩
  rw [hnil]
  ext a
  simp only [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, map_eq_zero]
  exact Ideal.Quotient.eq_zero_iff_mem
end GlobalTheory.OnePoint
