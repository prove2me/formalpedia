-- Prove2me | solution 1 for GlobalTheory.linearIndependent_of_comm_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:02.375033+00:00
-- url     : https://prove2.me/submissions/ac6ee9c7-39d5-4bdd-a21d-9a74e1ad7c8a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LinearIndependentOfCommSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {K G V : Type} [Field K] [AddCommGroup V] [Module K V]
    [Nontrivial V] (A : G → V →ₗ[K] V) (c : G → G → K) (hA : ∀ x, Function.Injective (A x))
    (h : ∀ x y v, A x (A y v) = c x y • A y (A x v)) (hc : Function.Injective c) :
    LinearIndependent K A := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro g hg i hi
  by_contra hgi

  have htwist : ∀ y, ∑ x ∈ s, (g x * (c x y - c i y)) • A x = 0 := by
    intro y
    ext v
    have h0 := LinearMap.congr_fun hg v
    have h1 := LinearMap.congr_fun hg (A y v)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.zero_apply] at h0 h1 ⊢
    have h2 : A y (∑ x ∈ s, (g x * c x y) • A x v) = 0 := by
      rw [map_sum, ← h1]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_smul, h x y v, smul_smul]
    have h3 : ∑ x ∈ s, (g x * c x y) • A x v = 0 :=
      hA y (by rw [h2, map_zero])
    simp_rw [mul_sub, sub_smul, Finset.sum_sub_distrib, h3, zero_sub, neg_eq_zero]
    have h4 : ∑ x ∈ s, (g x * c i y) • A x v = c i y • ∑ x ∈ s, g x • A x v := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [smul_smul, mul_comm]
    rw [h4, h0, smul_zero]
  have hothers : ∀ x ∈ s, x ≠ i → g x = 0 := by
    intro x hx hxi
    by_contra hgx
    apply hxi
    apply hc
    funext y
    have hrel : ∑ z ∈ s.erase i, (g z * (c z y - c i y)) • A z = 0 := by
      rw [← htwist y, ← Finset.sum_erase_add s _ hi, sub_self, mul_zero, zero_smul, add_zero]
    have := ih (s.erase i) (Finset.erase_ssubset hi) _ hrel x (Finset.mem_erase.2 ⟨hxi, hx⟩)
    rcases mul_eq_zero.1 this with h5 | h5
    · exact absurd h5 hgx
    · exact sub_eq_zero.1 h5
  have hsingle : g i • A i = 0 := by
    rw [← hg, Finset.sum_eq_single_of_mem i hi]
    intro x hx hxi
    rw [hothers x hx hxi, zero_smul]
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  apply hv
  apply hA i
  have := LinearMap.congr_fun hsingle v
  simp only [LinearMap.smul_apply, LinearMap.zero_apply] at this
  rw [map_zero]
  exact (smul_eq_zero.1 this).resolve_left hgi
end _root_.GlobalTheory
end GlobalTheory
