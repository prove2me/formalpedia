-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.finprod_eq_finprod_prod_extension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/34d4df49-3725-5dc5-86b8-ddaa64ea3a40

import Mathlib
import Definitions.Def_DedekindDomain_IntegralClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_finprod_eq_finprod_prod_extension

set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem solution
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    {A : Type} [CommMonoid A] (g : HeightOneSpectrum (𝓞 M) → A) (hg : (Function.mulSupport g).Finite) :
    ∏ᶠ w : HeightOneSpectrum (𝓞 M), g w =
      ∏ᶠ v : HeightOneSpectrum (𝓞 E),
        (letI := Extension.fintype (𝓞 E) E M (𝓞 M) v; ∏ w : v.Extension (𝓞 M), g w.1) := by
  classical
  set π : HeightOneSpectrum (𝓞 M) → HeightOneSpectrum (𝓞 E) := fun w => w.under (𝓞 E) with hπ
  set s : Finset (HeightOneSpectrum (𝓞 M)) := hg.toFinset with hs
  have hmem : ∀ w, w ∈ s ↔ g w ≠ 1 := fun w => by simp [hs, Function.mem_mulSupport]
  set t : Finset (HeightOneSpectrum (𝓞 E)) := s.image π with ht
  set G : HeightOneSpectrum (𝓞 E) → A := fun v =>
    (letI := Extension.fintype (𝓞 E) E M (𝓞 M) v; ∏ w : v.Extension (𝓞 M), g w.1) with hG
  have hGv : ∀ v, G v = ∏ w ∈ s.filter (fun w => π w = v), g w := by
    intro v
    letI := Extension.fintype (𝓞 E) E M (𝓞 M) v
    have h1 : G v = ∏ w ∈ (Finset.univ : Finset (v.Extension (𝓞 M))).map ⟨fun w : v.Extension (𝓞 M) => w.1, Subtype.val_injective⟩, g w := by
      rw [Finset.prod_map]
      rfl
    rw [h1]
    symm
    apply Finset.prod_subset
    · intro w hw
      rw [Finset.mem_filter] at hw
      rw [Finset.mem_map]
      exact ⟨⟨w, hw.2⟩, Finset.mem_univ _, rfl⟩
    · intro w hw hw'
      rw [Finset.mem_map] at hw
      obtain ⟨⟨w₀, hw₀⟩, -, rfl⟩ := hw
      by_contra hne
      exact hw' (Finset.mem_filter.mpr ⟨(hmem _).mpr hne, hw₀⟩)
  have hGsupp : Function.mulSupport G ⊆ ↑t := by
    intro v hv
    rw [Function.mem_mulSupport, hGv] at hv
    by_contra hvt
    apply hv
    apply Finset.prod_eq_one
    intro w hw
    rw [Finset.mem_filter] at hw
    exfalso
    exact hvt (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨w, hw.1, hw.2⟩))
  have hL : ∏ᶠ w : HeightOneSpectrum (𝓞 M), g w = ∏ w ∈ s, g w :=
    finprod_eq_prod_of_mulSupport_subset g (by intro w hw; exact Finset.mem_coe.mpr ((hmem w).mpr hw))
  have hR : ∏ᶠ v : HeightOneSpectrum (𝓞 E), G v = ∏ v ∈ t, G v := finprod_eq_prod_of_mulSupport_subset G hGsupp
  change ∏ᶠ w : HeightOneSpectrum (𝓞 M), g w = ∏ᶠ v : HeightOneSpectrum (𝓞 E), G v
  rw [hL, hR]
  simp_rw [hGv]
  exact (Finset.prod_fiberwise_of_maps_to (fun w hw => Finset.mem_image_of_mem π hw) g).symm

end S_IsDedekindDomain_HeightOneSpectrum_finprod_eq_finprod_prod_extension
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_finprod_eq_finprod_prod_extension (solution)
