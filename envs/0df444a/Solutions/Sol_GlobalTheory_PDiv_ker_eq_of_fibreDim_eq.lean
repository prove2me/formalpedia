-- Prove2me | solution 1 for GlobalTheory.PDiv.ker_eq_of_fibreDim_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:48:44.689617+00:00
-- url     : https://prove2.me/submissions/40889527-7040-41eb-af67-5a10d3459084

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PointsGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpanEqTopOfFinrankFibreEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerCounitAlgHomBaseChangeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankDualAndRangeDualMapBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubsingletonOfResidueFieldFibres
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Theorems.Thm_GlobalTheory_surjective_injective_of_fibre_rank


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module
open GlobalTheory GlobalTheory.PDiv
variable {O : Type} [CommRing O]
variable {A B : Type} [CommRing A] [CommRing B] [HopfAlgebra O A] [HopfAlgebra O B]
  [Module.Finite O A]
variable [Module.Projective O A] [Module.Finite O B] [Module.Projective O B]
namespace GlobalTheory.PDiv
theorem _root_.solution {D E : Type} [CommRing D] [CommRing E] [Algebra O D] [Algebra O E]
    [Module.Finite O D] [Module.Finite O E] [Module.Projective O E] (π : D →ₐ[O] E)
    (hπ : Function.Surjective π) (I : Ideal D) (hI : I ≤ RingHom.ker π)
    (h : ∀ q : PrimeSpectrum O, fibreDim (D ⧸ I) q = fibreDim E q) : RingHom.ker π = I := by
  refine le_antisymm (fun d hd => ?_) hI
  let π' : (D ⧸ I) →ₐ[O] E := Ideal.Quotient.liftₐ I π hI
  have hs : Function.Surjective π' := fun e => by
    obtain ⟨d, rfl⟩ := hπ e
    exact ⟨Ideal.Quotient.mk I d, rfl⟩
  have hi := (GlobalTheory.surjective_injective_of_fibre_rank O _ _ π'.toLinearMap).2 inferInstance inferInstance hs h
  exact Ideal.Quotient.eq_zero_iff_mem.1 (hi (a₁ := Ideal.Quotient.mk I d) (a₂ := 0)
    (by rw [map_zero]; exact hd))
end GlobalTheory.PDiv
