-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.of_isPullback_of_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/2a030a5d-cb1f-511d-9102-e2698cbbb2b6

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_AlgebraicGeometry_IsProper_descendsAlong_surjective_inf_flat_inf_quasiCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {X A' : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S')}
    (c : A' ⟶ X) (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (hA' : AbelianSchemePropertyBundle S' f') (L : RelativeGroupLaw S f) :
    AbelianSchemePropertyBundle S f := by
  classical
  set ι : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S) := Spec.map (CommRingCat.ofHom (algebraMap S S')) with hι

  have hsurjfun : Function.Surjective ι.base := by
    intro x
    obtain ⟨y, hy⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := S) (B := S') x
    exact ⟨y, hy⟩
  haveI hsurj : Surjective ι := ⟨hsurjfun⟩
  haveI hflat : Flat ι := by
    rw [hι, HasRingHomProperty.Spec_iff (P := @Flat)]
    change (algebraMap S S').Flat
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) ι := ⟨⟨hsurj, hflat⟩, inferInstance⟩
  haveI := AlgebraicGeometry.IsProper.descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
  haveI : Smooth f' := hA'.smooth
  haveI : IsProper f' := hA'.proper
  refine ⟨?_, ?_, ?_, ⟨L⟩⟩
  · exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      hc.flip hQ hA'.smooth
  · exact MorphismProperty.of_isPullback_of_descendsAlong (P := @IsProper) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      hc.flip hQ hA'.proper
  ·
    intro s
    obtain ⟨s', hs'⟩ := hsurjfun s

    have hlift : ∀ x : X, f.base x = s → ∃ x' : A', c.base x' = x ∧ f'.base x' = s' := by
      intro x hx
      obtain ⟨z, hz1, hz2⟩ := AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback (f := f) (g := ι) x s'
        (by rw [hx, hs'])
      refine ⟨hc.isoPullback.inv.base z, ?_, ?_⟩
      · change (hc.isoPullback.inv ≫ c).base z = x
        rw [hc.isoPullback_inv_fst]; exact hz1
      · change (hc.isoPullback.inv ≫ f').base z = s'
        rw [hc.isoPullback_inv_snd]; exact hz2
    have heq : f.base ⁻¹' {s} = c.base '' (f'.base ⁻¹' {s'}) := by
      ext x
      constructor
      · intro hx
        obtain ⟨x', h1, h2⟩ := hlift x hx
        exact ⟨x', h2, h1⟩
      · rintro ⟨x', hx', rfl⟩
        change (c ≫ f).base x' = s
        rw [hc.w]
        change ι.base (f'.base x') = s
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hx'
        rw [hx', hs']
    rw [heq]
    exact (hA'.connectedFibres s').image _ c.base.hom.continuous.continuousOn

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat (solution)
