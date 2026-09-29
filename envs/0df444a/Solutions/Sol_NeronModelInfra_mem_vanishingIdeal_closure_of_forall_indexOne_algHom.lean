-- Prove2me | solution 1 for NeronModelInfra.mem_vanishingIdeal_closure_of_forall_indexOne_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c04122de-90dc-5976-8fb2-5a1c17f5dc2d

import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_NeronModelInfra_SmoothnessDefect

import Theorems.Thm_NeronModelInfra_exists_algHom_comap_maximalIdeal_eq_primeIdealOf_of_apply_closedPoint_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_mem_vanishingIdeal_closure_of_forall_indexOne_algHom

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra TensorProduct

universe u

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (S : Set X)
    (hS : ∀ s ∈ S, ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ : Algebra R R')
      (_ : IsLocalHom (algebraMap R R')) (_ : IsIndexOneExtension R R')
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f), x.1 (IsLocalRing.closedPoint R') = s)
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra R Γ(X, U) :=
      ((X.presheaf.map (homOfLE le_top).op).hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
    let J : Ideal Γ(X, U) :=
      PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ closure S})
    ∀ g : Γ(X, U),
      (∀ (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra R R'']
        [IsLocalHom (algebraMap R R'')], IsIndexOneExtension R R'' →
        ∀ c : Γ(X, U) →ₐ[R] R'', J ≤ (IsLocalRing.maximalIdeal R'').comap c →
          g ∈ (IsLocalRing.maximalIdeal R'').comap c) → g ∈ J := by
  letI : Algebra R Γ(X, U) :=
    ((X.presheaf.map (homOfLE le_top).op).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
  intro J g hg
  rw [PrimeSpectrum.mem_vanishingIdeal]
  rintro 𝔭 ⟨y, hy, rfl⟩

  let Z : Set U := {z : U | g ∈ (hU.primeIdealOf z).asIdeal}
  have hZ : IsClosed Z := by
    have : Z = hU.isoSpec.hom.base ⁻¹' PrimeSpectrum.zeroLocus {g} := by
      ext z
      change g ∈ (hU.isoSpec.hom.base z).asIdeal ↔ ({g} : Set Γ(X, U)) ⊆ ((hU.isoSpec.hom.base z).asIdeal : Set Γ(X, U))
      rw [Set.singleton_subset_iff]
      rfl
    rw [this]
    exact (PrimeSpectrum.isClosed_zeroLocus _).preimage hU.isoSpec.hom.base.hom.continuous

  let A : Set U := {s : U | (s : X) ∈ S}
  have hAZ : A ⊆ Z := by
    intro s hs
    obtain ⟨R', _, _, _, _, _, hR', x, hx⟩ := hS s.1 hs
    have hxU : x.1 (IsLocalRing.closedPoint R') ∈ U := by rw [hx]; exact s.2
    obtain ⟨c, hc⟩ :=
      NeronModelInfra.exists_algHom_comap_maximalIdeal_eq_primeIdealOf_of_apply_closedPoint_mem f R' x U hU hxU
    have hs' : (⟨x.1 (IsLocalRing.closedPoint R'), hxU⟩ : U) = s := Subtype.ext hx
    have hJc : J ≤ (IsLocalRing.maximalIdeal R').comap c := by
      rw [hc]
      intro j hj
      rw [PrimeSpectrum.mem_vanishingIdeal] at hj
      exact hj _ ⟨_, by rw [hs']; exact subset_closure hs, rfl⟩
    have := hg R' hR' c hJc
    rw [hc, hs'] at this
    exact this

  have hyA : y ∈ closure A := by
    have hind : Topology.IsInducing ((↑) : U → X) := Topology.IsInducing.subtypeVal
    have key : y ∈ ((↑) : U → X) ⁻¹' closure (((↑) : U → X) '' A) := by
      rw [Set.mem_preimage]
      refine closure_mono ?_ (show (y : X) ∈ closure ((U : Set X) ∩ S) from U.2.inter_closure ⟨y.2, hy⟩)
      rintro _ ⟨hzU, hzS⟩
      exact ⟨⟨_, hzU⟩, hzS, rfl⟩
    exact (hind.closure_eq_preimage_closure_image A).symm ▸ key
  exact hZ.closure_subset_iff.mpr hAZ hyA

end S_NeronModelInfra_mem_vanishingIdeal_closure_of_forall_indexOne_algHom
end P2MW
export P2MW.S_NeronModelInfra_mem_vanishingIdeal_closure_of_forall_indexOne_algHom (solution)
