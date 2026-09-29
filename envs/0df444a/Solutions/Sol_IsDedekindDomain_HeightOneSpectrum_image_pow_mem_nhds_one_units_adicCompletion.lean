-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.image_pow_mem_nhds_one_units_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/68831353-062f-5bc6-be4a-106c6553f786

import Mathlib
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_image_pow_mem_nhds_one_units_adicCompletion

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (hn : 0 < n)
    (V : Set (v.adicCompletion K)ˣ) (hV : V ∈ nhds (1 : (v.adicCompletion K)ˣ)) :
    (fun s : (v.adicCompletion K)ˣ => s ^ n) '' V ∈ nhds (1 : (v.adicCompletion K)ˣ) := by
  letI : NontriviallyNormedField (v.adicCompletion K) :=
    Valued.toNontriviallyNormedField (v.adicCompletion K) (WithZero (Multiplicative ℤ))
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  have hder : HasStrictDerivAt (fun x : v.adicCompletion K => x ^ n)
      ((n : v.adicCompletion K) * (1 : v.adicCompletion K) ^ (n - 1)) 1 := hasStrictDerivAt_pow n 1
  have hne : ((n : v.adicCompletion K) * (1 : v.adicCompletion K) ^ (n - 1)) ≠ 0 := by
    rw [one_pow, mul_one]; exact Nat.cast_ne_zero.2 hn.ne'
  have hmap : Filter.map (fun x : v.adicCompletion K => x ^ n) (nhds 1) = nhds 1 := by
    have h := hder.map_nhds_eq hne
    rwa [one_pow] at h
  have hemb : Topology.IsOpenEmbedding (Units.val : (v.adicCompletion K)ˣ → v.adicCompletion K) :=
    Units.isOpenEmbedding_val
  have h1 : (Units.val '' V) ∈ nhds (((1 : (v.adicCompletion K)ˣ) : (v.adicCompletion K)ˣ) : v.adicCompletion K) := by
    rw [← hemb.map_nhds_eq]; exact Filter.image_mem_map hV
  rw [Units.val_one] at h1
  have h2 : (fun x : v.adicCompletion K => x ^ n) '' (Units.val '' V) ∈ nhds (1 : v.adicCompletion K) := by
    rw [← hmap]; exact Filter.image_mem_map h1
  have h3 : (fun x : v.adicCompletion K => x ^ n) '' (Units.val '' V) =
      Units.val '' ((fun s : (v.adicCompletion K)ˣ => s ^ n) '' V) := by
    rw [Set.image_image, Set.image_image]
    refine Set.image_congr' fun s => ?_
    simp
  rw [h3] at h2
  rw [hemb.nhds_eq_comap, Units.val_one, Filter.mem_comap]
  exact ⟨_, h2, by rw [hemb.injective.preimage_image]⟩

end S_IsDedekindDomain_HeightOneSpectrum_image_pow_mem_nhds_one_units_adicCompletion
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_image_pow_mem_nhds_one_units_adicCompletion (solution)
