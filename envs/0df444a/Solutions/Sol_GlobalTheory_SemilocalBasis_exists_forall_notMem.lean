-- Prove2me | solution 1 for GlobalTheory.SemilocalBasis.exists_forall_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:44:29.768799+00:00
-- url     : https://prove2.me/submissions/16191235-5aea-4e43-bbce-b5f8c330e6f0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsBasisMemOfSpanEqTopOfSemilocal

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
open GlobalTheory.SemilocalBasis
open scoped Pointwise
namespace GlobalTheory.SemilocalBasis
theorem _root_.solution {A V J : Type*} [CommRing A] [IsLocalRing A]
    [Infinite (IsLocalRing.ResidueField A)] [AddCommGroup V] [Module A V] [Finite J]
    (p : J → Submodule A V) (hp : ∀ i, p i ≠ ⊤)
    (hm : ∀ i, ∀ a ∈ IsLocalRing.maximalIdeal A, ∀ x, a • x ∈ p i) : ∃ x : V, ∀ i, x ∉ p i := by
  classical
  have := Fintype.ofFinite J
  by_contra! h
  have hcov : ⋃ i ∈ (Finset.univ : Finset J),
      (0 : V) +ᵥ ((p i).toAddSubgroup : Set V) = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr fun a => ?_
    obtain ⟨i, hi⟩ := h a
    simp only [zero_vadd, Set.mem_iUnion]
    exact ⟨i, Finset.mem_univ i, hi⟩
  obtain ⟨k, -, hk⟩ := AddSubgroup.exists_finiteIndex_of_leftCoset_cover hcov
  have hfin : Finite (V ⧸ p k) := AddSubgroup.finite_quotient_of_finiteIndex (H := (p k).toAddSubgroup)
  obtain ⟨x, hx⟩ : ∃ x, x ∉ p k := by
    by_contra! h'
    exact hp k (Submodule.eq_top_iff'.mpr h')
  choose s hs using IsLocalRing.residue_surjective (R := A)
  have hinj : Function.Injective
      (fun c : IsLocalRing.ResidueField A => (p k).mkQ (s c • x)) := by
    intro c d hcd
    by_contra hne
    have h1 : (s c - s d) • x ∈ p k := by
      rw [sub_smul]
      exact (Submodule.Quotient.eq _).mp hcd
    have h2 : IsUnit (s c - s d) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub, hs, hs]
      exact sub_ne_zero.mpr hne
    exact hx (((p k).smul_mem_iff_of_isUnit h2).mp h1)
  have := Finite.of_injective _ hinj
  exact not_finite (IsLocalRing.ResidueField A)
end GlobalTheory.SemilocalBasis
