-- Prove2me | solution 1 for GlobalTheory.exists_symplectic_coordinates_adapted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:31:21.728795+00:00
-- url     : https://prove2.me/submissions/8b667ff6-8d5f-452a-9d71-97e33e1ce493

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsSymplecticCoordinatesAdapted
import Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_apply_eq_sum
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_apply_eq_sum
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_mem_orthogonal_iff
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_reindex
import Theorems.Thm_GlobalTheory_exists_isSymplecticBasis_extend
import Theorems.Thm_GlobalTheory_isTorsionFree_quotient_iff
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open Module Function
open GlobalTheory
open Module Function
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ]
    [Module.Finite ℤ Λ] {ω : LinearMap.BilinForm ℤ Λ} (hω : ω.IsAlt) (hp : Bijective ω)
    {I : Submodule ℤ Λ} (hsat : ∀ (k : ℤ) (x : Λ), k ≠ 0 → k • x ∈ I → x ∈ I)
    (hiso : ∀ x ∈ I, ∀ y ∈ I, ω x y = 0) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ∃ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] Λ) (S : Finset (Fin g)),
      (∀ a b, ω (bas a) (bas b) = ε * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd a b) ∧
      I = Submodule.span ℤ ((fun k => bas (Pi.single (Sum.inl k) 1)) '' (S : Set (Fin g))) ∧
      2 * g = finrank ℤ Λ := by
  obtain ⟨r, v⟩ := Submodule.basisOfPid (Module.Free.chooseBasis ℤ Λ) I
  have htf : Module.IsTorsionFree ℤ (Λ ⧸ I) := (_root_.GlobalTheory.isTorsionFree_quotient_iff I).mpr hsat
  have hle : I ≤ ω.orthogonal I := fun x hx =>
    (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun y hy => hiso y hy x hx
  obtain ⟨g, b, hb, hbv⟩ := _root_.GlobalTheory.exists_isSymplecticBasis_extend hω hp htf hle v
  set e : Fin r ⊕ Fin g ≃ Fin (r + g) := finSumFinEquiv
  set b' := b.reindex (e.sumCongr e) with hb'
  have hsymp : _root_.GlobalTheory.IsSymplecticBasis ω b' := hb.reindex e
  have hb'v : ∀ i, b' (Sum.inl (e (Sum.inl i))) = (v i : Λ) := by
    intro i
    rw [hb', Module.Basis.reindex_apply]
    simp [hbv]
  obtain ⟨u, hu⟩ : IsUnit ε := Int.isUnit_iff.mpr hε
  let D : (Fin (r + g) ⊕ Fin (r + g) → ℤ) ≃ₗ[ℤ] (Fin (r + g) ⊕ Fin (r + g) → ℤ) :=
    LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfUnit (Sum.elim (fun _ => 1) (fun _ => u) i)
  have hD : ∀ a i, D a i = Sum.elim (fun _ => (1 : ℤ)) (fun _ => ε) i * a i := by
    intro a i
    rcases i with i | i <;> change (_ : ℤˣ) • a _ = _ <;> simp [Units.smul_def, hu]
  refine ⟨r + g, D.trans b'.equivFun.symm, Finset.univ.image fun i => e (Sum.inl i), ?_, ?_, ?_⟩
  · intro a c
    rw [hsymp.apply_eq_sum hω]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [LinearEquiv.trans_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, hD,
      Sum.elim_inl, Sum.elim_inr]
    ring
  · have hspan : Submodule.span ℤ (Set.range fun i => (v i : Λ)) = I := by
      have h := congrArg (Submodule.map I.subtype) v.span_eq
      rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at h
      exact h
    have hsingle : ∀ k, D (Pi.single (Sum.inl k) 1) = Pi.single (Sum.inl k) 1 := by
      intro k
      funext i
      rw [hD]
      rcases i with i | i <;> simp [Pi.single_apply]
    rw [← hspan]
    congr 1
    ext x
    simp only [Set.mem_image, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range,
      LinearEquiv.trans_apply, hsingle, _root_.Basis.equivFun_symm_single]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e (Sum.inl i), ⟨i, rfl⟩, hb'v i⟩
    · rintro ⟨k, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hb'v i).symm⟩
  · rw [Module.finrank_eq_card_basis b']
    simp
    ring
end _root_.GlobalTheory
end GlobalTheory
