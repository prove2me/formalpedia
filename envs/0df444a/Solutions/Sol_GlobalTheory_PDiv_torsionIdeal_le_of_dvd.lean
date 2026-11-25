-- Prove2me | solution 1 for GlobalTheory.PDiv.torsionIdeal_le_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:53:38.891065+00:00
-- url     : https://prove2.me/submissions/9e6d65ba-d625-4258-8c3b-f573aee50aa7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Theorems.Thm_GlobalTheory_PDiv_torsionIdeal_le_ker_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv
open GlobalTheory GlobalTheory.PDiv
variable {R A B C D : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
variable [Bialgebra R A] [Bialgebra R B] [Bialgebra R C] [Bialgebra R D]
namespace GlobalTheory.PDiv
theorem _root_.solution [IsCocomm R A] {m n : ℕ} (h : m ∣ n) :
    torsionIdeal R A n ≤ torsionIdeal R A m := by
  obtain ⟨k, rfl⟩ := h
  have h1 := (torsionIdeal_le_ker_iff m (Ideal.Quotient.mkₐ R (torsionIdeal R A m))).1
    fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  have h2 := (torsionIdeal_le_ker_iff (m * k) (Ideal.Quotient.mkₐ R (torsionIdeal R A m))).2
    (by rw [pow_mul, h1, one_pow])
  exact fun a ha => Ideal.Quotient.eq_zero_iff_mem.1 (h2 ha)
end GlobalTheory.PDiv
