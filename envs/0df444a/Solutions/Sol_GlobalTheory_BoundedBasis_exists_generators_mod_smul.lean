-- Prove2me | solution 1 for GlobalTheory.BoundedBasis.exists_generators_mod_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:44.544366+00:00
-- url     : https://prove2.me/submissions/f5e8116f-88b4-4d16-8fe1-ff3883f3d9e9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
open GlobalTheory.BoundedBasis
namespace GlobalTheory.BoundedBasis
theorem _root_.solution {R : Type*} [CommRing R] [IsDedekindDomain R] {a : R}
    (ha : a ≠ 0) (r : ℕ) : ∀ (M : Type) [AddCommGroup M] [Module R M]
      (φ : M →ₗ[R] (Fin r → R)), Function.Injective φ →
      ∃ x : Fin r → M, ∀ m : M, ∃ (c : Fin r → R) (m' : M), m = ∑ i, c i • x i + a • m' := by
  induction r with
  | zero =>
    intro M _ _ φ hφ
    refine ⟨fun _ => 0, fun m => ⟨fun _ => 0, 0, ?_⟩⟩
    have : m = 0 := hφ (Subsingleton.elim _ _)
    simp [this]
  | succ r ih =>
    intro M _ _ φ hφ
    let π : M →ₗ[R] R := (LinearMap.proj 0).comp φ
    have hI : ∃ y : M, ∀ m : M, ∃ (c : R) (m' : M), π m = c * π y + a * π m' := by
      by_cases h0 : ∀ m, π m = 0
      · exact ⟨0, fun m => ⟨0, 0, by simp [h0 m]⟩⟩
      · push Not at h0
        obtain ⟨z, hz⟩ := h0
        obtain ⟨y, hy⟩ := IsDedekindDomain.exists_eq_span_pair (I := LinearMap.range π)
          (x := a * π z) ⟨a • z, by simp⟩ (mul_ne_zero ha hz)
        obtain ⟨y', rfl⟩ : y ∈ (LinearMap.range π : Ideal R) := by
          rw [hy]; exact Ideal.subset_span (by simp)
        refine ⟨y', fun m => ?_⟩
        have hm : π m ∈ (LinearMap.range π : Ideal R) := ⟨m, rfl⟩
        rw [hy, Ideal.mem_span_pair] at hm
        obtain ⟨s, t, hst⟩ := hm
        exact ⟨t, s • z, by rw [← hst, map_smul, smul_eq_mul]; ring⟩
    obtain ⟨y, hy⟩ := hI
    let φ' : LinearMap.ker π →ₗ[R] (Fin r → R) :=
      LinearMap.pi fun i => (LinearMap.proj i.succ).comp (φ.comp (LinearMap.ker π).subtype)
    have hφ' : Function.Injective φ' := by
      rw [injective_iff_map_eq_zero]
      intro m hm
      refine Subtype.ext (hφ ?_)
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [Submodule.coe_zero, map_zero]
        exact m.2
      · simpa [φ'] using congrFun hm i
    obtain ⟨x, hx⟩ := ih (LinearMap.ker π) φ' hφ'
    refine ⟨Fin.cons y fun i => (x i : M), fun m => ?_⟩
    obtain ⟨c, m₁, h⟩ := hy m
    obtain ⟨d, m₂, h₂⟩ := hx ⟨m - c • y - a • m₁, by
      rw [LinearMap.mem_ker, map_sub, map_sub, map_smul, map_smul, h]; simp⟩
    refine ⟨Fin.cons c d, m₁ + (m₂ : M), ?_⟩
    have h₃ := congrArg Subtype.val h₂
    simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul] at h₃
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, smul_add]
    rw [sub_sub, sub_eq_iff_eq_add] at h₃
    rw [h₃]
    abel
end GlobalTheory.BoundedBasis
