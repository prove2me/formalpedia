-- Prove2me | solution 1 for GlobalTheory.IdealSum.tsum_idealLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:37:17.557838+00:00
-- url     : https://prove2.me/submissions/fde72d9d-336c-4005-b7f5-e4d12d8d0c6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LatticeSumDilateHaarAsymptoticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealSumPeriodicDilate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory GlobalTheory.IdealSum
namespace GlobalTheory.IdealSum
theorem _root_.solution (K : Type) [Field K] [NumberField K] (J : (Ideal (𝓞 K))⁰)
    (F : mixedSpace K → ℂ) :
    ∑' l : idealLattice K (FractionalIdeal.mk0 K J), F l =
      ∑' β : ↥(J.1), F (mixedEmbedding K ((β : 𝓞 K) : K)) := by
  let φ : ↥(J.1) → idealLattice K (FractionalIdeal.mk0 K J) := fun β =>
    ⟨mixedEmbedding K ((β : 𝓞 K) : K), (mem_idealLattice K _).2 ⟨((β : 𝓞 K) : K), by
      rw [FractionalIdeal.coe_mk0]
      exact FractionalIdeal.mem_coeIdeal_of_mem _ β.2, rfl⟩⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b h
      exact Subtype.ext (RingOfIntegers.coe_injective
        (mixedEmbedding_injective K (congrArg Subtype.val h)))
    · rintro ⟨l, hl⟩
      obtain ⟨y, hy, rfl⟩ := (mem_idealLattice K _).1 hl
      rw [FractionalIdeal.coe_mk0] at hy
      obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
      exact ⟨⟨x, hx⟩, rfl⟩
  exact ((Equiv.ofBijective φ hφ).tsum_eq (fun l => F l)).symm
end GlobalTheory.IdealSum
