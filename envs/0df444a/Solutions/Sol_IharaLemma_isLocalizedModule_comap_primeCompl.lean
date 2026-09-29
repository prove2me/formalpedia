-- Prove2me | solution 1 for IharaLemma.isLocalizedModule_comap_primeCompl
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/8d4fda36-9bb6-507a-98ca-7551e3325aef

import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Localization.Defs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IharaLemma_isLocalizedModule_comap_primeCompl

theorem solution {Λ B : Type*} [CommRing Λ] [CommRing B] [Algebra Λ B]
    (hπ : Function.Surjective (algebraMap Λ B))
    (𝔭 : Ideal B) [𝔭.IsPrime]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module B M] [Module B N] [Module Λ M] [Module Λ N]
    [IsScalarTower Λ B M] [IsScalarTower Λ B N]
    (f : M →ₗ[B] N) [IsLocalizedModule 𝔭.primeCompl f] :
    IsLocalizedModule (𝔭.comap (algebraMap Λ B)).primeCompl (f.restrictScalars Λ) := by
  have key : Algebra.algebraMapSubmonoid B (𝔭.comap (algebraMap Λ B)).primeCompl = 𝔭.primeCompl := by
    ext b; constructor
    · rintro ⟨t, ht, rfl⟩; exact ht
    · intro hb; obtain ⟨t, rfl⟩ := hπ b; exact ⟨t, hb, rfl⟩
  haveI : IsLocalizedModule (Algebra.algebraMapSubmonoid B (𝔭.comap (algebraMap Λ B)).primeCompl) f := by
    rw [key]; infer_instance

  constructor
  · intro s
    have h := IsLocalizedModule.map_units f ⟨algebraMap Λ B s,
      Algebra.mem_algebraMapSubmonoid_of_mem s⟩
    have hfun : ⇑(algebraMap B (Module.End B N) (algebraMap Λ B ↑s)) =
        ⇑(algebraMap Λ (Module.End Λ N) ↑s) := by
      funext x; rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, algebraMap_smul]
    rw [Module.End.isUnit_iff] at h ⊢
    rwa [hfun] at h
  · intro y
    obtain ⟨⟨x, ⟨_, s, hs, rfl⟩⟩, e⟩ := IsLocalizedModule.surj
      (Algebra.algebraMapSubmonoid B (𝔭.comap (algebraMap Λ B)).primeCompl) f y
    refine ⟨⟨x, ⟨s, hs⟩⟩, ?_⟩
    simpa [Submonoid.smul_def, algebraMap_smul] using e
  · intro x₁ x₂ e
    obtain ⟨⟨_, s, hs, rfl⟩, hc⟩ := IsLocalizedModule.exists_of_eq
      (S := Algebra.algebraMapSubmonoid B (𝔭.comap (algebraMap Λ B)).primeCompl) (f := f) e
    refine ⟨⟨s, hs⟩, ?_⟩
    simpa [Submonoid.smul_def, algebraMap_smul] using hc

#print axioms solution

end S_IharaLemma_isLocalizedModule_comap_primeCompl
end P2MW
export P2MW.S_IharaLemma_isLocalizedModule_comap_primeCompl (solution)
