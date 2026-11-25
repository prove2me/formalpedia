-- Prove2me | solution 1 for GroundTheory.Global.emultiplicity_relNorm_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:16:27.542838+00:00
-- url     : https://prove2.me/submissions/d2f0392b-8aea-4469-a73e-ff6cb85b2819

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
import Theorems.Thm_GroundTheory_Global_prime_asIdeal
import Theorems.Thm_GroundTheory_Global_emultiplicity_asIdeal_of_isMaximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open IsDedekindDomain NumberField Module
open GroundTheory GroundTheory.Global
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
variable (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Global
theorem _root_.solution (p : Ideal (𝓞 M)) (hp : Prime p) :
    emultiplicity v.asIdeal (Ideal.relNorm (𝓞 K) p) =
      ∑ w : SemiLocal.PlacesOver M v,
        (w.1.asIdeal.inertiaDeg (𝓞 K) : ℕ∞) * emultiplicity w.1.asIdeal p := by
  have hp0 : p ≠ ⊥ := hp.ne_zero
  have hpp : p.IsPrime := (Ideal.prime_iff_isPrime hp0).1 hp
  have hpm : p.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hp0 hpp
  have hqm : (p.under (𝓞 K)).IsMaximal := Ideal.IsMaximal.under (𝓞 K) p
  rw [Ideal.relNorm_eq_pow_of_isMaximal p (p.under (𝓞 K)),
    emultiplicity_pow (prime_asIdeal v), emultiplicity_asIdeal_of_isMaximal]
  simp only [emultiplicity_asIdeal_of_isMaximal, mul_ite, mul_one, mul_zero]
  by_cases hv : v.asIdeal = p.under (𝓞 K)
  · rw [if_pos hv]
    have hlies : p.LiesOver v.asIdeal := ⟨hv⟩
    let w0 : SemiLocal.PlacesOver M v := ⟨⟨p, hpp, hp0⟩, hlies⟩
    rw [Finset.sum_eq_single w0]
    · simp [w0]
    · intro w _ hw
      rw [if_neg]
      intro h
      apply hw
      apply Subtype.ext
      apply HeightOneSpectrum.ext
      exact h
    · simp
  · rw [if_neg hv]
    symm
    apply Finset.sum_eq_zero
    intro w _
    rw [if_neg]
    intro h
    apply hv
    rw [← h]
    exact Ideal.over_def w.1.asIdeal v.asIdeal
end GroundTheory.Global
