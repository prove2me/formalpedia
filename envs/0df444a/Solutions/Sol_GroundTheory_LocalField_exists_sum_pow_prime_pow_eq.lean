-- Prove2me | solution 1 for GroundTheory.LocalField.exists_sum_pow_prime_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:04:36.525805+00:00
-- url     : https://prove2.me/submissions/3bebac30-cec3-4d80-abc2-3ce58f07d413

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
variable {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime)
include hp
namespace GroundTheory.LocalField
theorem _root_.solution {ι : Type*} (s : Finset ι) (b : ι → R) (n : ℕ) :
    ∃ r : R, (∑ i ∈ s, b i) ^ p ^ n = ∑ i ∈ s, b i ^ p ^ n + p * r := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, ?_⟩
    simp [zero_pow (pow_ne_zero n hp.ne_zero)]
  | insert a s ha ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨r', hr'⟩ := exists_add_pow_prime_pow_eq hp (b a) (∑ i ∈ s, b i) n
    refine ⟨r + b a * (∑ i ∈ s, b i) * r', ?_⟩
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hr', hr]
    ring
end GroundTheory.LocalField
