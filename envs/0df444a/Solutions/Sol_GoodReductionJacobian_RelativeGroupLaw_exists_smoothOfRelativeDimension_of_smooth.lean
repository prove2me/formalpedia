-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_smoothOfRelativeDimension_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/a15b2762-ba7d-5fca-812e-9a2efd59b440

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_of_isPullback_of_flat_of_surjective
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_one_comp_eq
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_mem_and_smoothOfRelativeDimension_opensInclusion_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace GroupEquidimGC3

theorem of_isAlgClosed {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of K)} [Smooth g]
    (L : RelativeGroupLaw K g) : ∃ d : ℕ, SmoothOfRelativeDimension d g := by
  classical
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace g

  let e : Spec (CommRingCat.of K) ⟶ X := (L.one (𝟙 _)).1
  obtain ⟨V₀, d, he, hV₀⟩ := AlgebraicGeometry.Smooth.exists_mem_and_smoothOfRelativeDimension_opensInclusion_comp g (e.base (IsLocalRing.closedPoint K))
  refine ⟨d, ?_⟩

  let S : Set X.Opens := {V | SmoothOfRelativeDimension d (V.ι ≫ g)}
  have hcov : (⨆ V : S, (V : X.Opens)) = ⊤ := by
    rw [eq_top_iff]
    rintro z -

    by_contra hz
    have hzW : ∀ z' : X, z ⤳ z' → z' ∉ (⨆ V : S, (V : X.Opens)) := fun z' hzz' hz' =>
      hz (hzz'.mem_open (⨆ V : S, (V : X.Opens)).isOpen hz')
    obtain ⟨c, hccl, hcc⟩ := nonempty_inter_closedPoints (Z := closure {z}) ⟨z, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    rw [mem_closedPoints_iff] at hcc
    apply hzW c (specializes_iff_mem_closure.mpr hccl)
    let a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) g := ⟨pointOfClosedPoint g c hcc, pointOfClosedPoint_comp g c hcc⟩
    obtain ⟨τ, hτg, hτe⟩ := GoodReductionJacobian.RelativeGroupLaw.exists_iso_hom_comp_eq_one_comp_eq L a

    let V₁ : X.Opens := τ.inv ⁻¹ᵁ V₀
    have hτg' : τ.inv ≫ g = g := by rw [← cancel_epi τ.hom, ← Category.assoc, τ.hom_inv_id, Category.id_comp, hτg]
    have hV₁ : SmoothOfRelativeDimension d (V₁.ι ≫ g) := by
      have h1 : V₁.ι ≫ g = (τ.inv ∣_ V₀) ≫ (V₀.ι ≫ g) := by
        show (τ.inv ⁻¹ᵁ V₀).ι ≫ g = _
        rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hτg']
      rw [h1]
      have := hV₀
      have h2 : SmoothOfRelativeDimension (0 + d) ((τ.inv ∣_ V₀) ≫ (V₀.ι ≫ g)) := inferInstance
      simpa using h2
    have hc : c ∈ V₁ := by
      show τ.inv.base c ∈ V₀
      have : τ.inv.base c = e.base (IsLocalRing.closedPoint K) := by
        rw [← pointOfClosedPoint_apply g c hcc (IsLocalRing.closedPoint K)]
        show (a.1 ≫ τ.inv).base _ = _
        rw [← hτe, Category.assoc, τ.hom_inv_id, Category.comp_id]
      rw [this]; exact he
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V₁, hV₁⟩, hc⟩
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) _ hcov fun V => V.2

end GroupEquidimGC3

theorem solution
    {K : Type u} [Field K] {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of K)} [Smooth g]
    (L : RelativeGroupLaw K g) :
    ∃ d : ℕ, SmoothOfRelativeDimension d g := by

  let Kb : Type u := AlgebraicClosure K
  let ι : Spec (CommRingCat.of Kb) ⟶ Spec (CommRingCat.of K) := Spec.map (CommRingCat.ofHom (algebraMap K Kb))
  haveI : Smooth (pullback.snd g ι) := inferInstance
  obtain ⟨d, hd⟩ := GroupEquidimGC3.of_isAlgClosed (L.baseChange ι)
  haveI := hd
  haveI : Flat ι := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  haveI : Surjective ι := ⟨fun p => ⟨IsLocalRing.closedPoint Kb, Subsingleton.elim _ _⟩⟩
  exact ⟨d, SmoothOfRelativeDimension.of_isPullback_of_flat_of_surjective d (IsPullback.of_hasPullback g ι).flip⟩

end S_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth (solution)
