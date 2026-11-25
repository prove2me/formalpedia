-- Prove2me | solution 1 for GlobalTheory.UnramifiedEmbedding.quotientMap_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:34:16.201132+00:00
-- url     : https://prove2.me/submissions/9bf425ac-5d81-4afa-bc47-aa71786e6da7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GaloisOfPrimePowerDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RangeLeRangeOfIsUnramifiedAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IsLocalRing NumberField
open GlobalTheory GlobalTheory.UnramifiedEmbedding
namespace GlobalTheory.UnramifiedEmbedding
theorem _root_.solution {O S : Type*} [CommRing O] [IsLocalRing O] [CommRing S]
    [Algebra O S] [Algebra.IsIntegral O S] [IsAlgClosed (ResidueField O)] (M : Ideal S)
    [M.IsMaximal] (hM : M.comap (algebraMap O S) = maximalIdeal O) :
    Function.Bijective (Ideal.quotientMap M (algebraMap O S) hM.ge) := by
  letI : Field (O ⧸ maximalIdeal O) := Ideal.Quotient.field _
  haveI : IsAlgClosed (O ⧸ maximalIdeal O) := ‹IsAlgClosed (ResidueField O)›
  letI : Field (S ⧸ M) := Ideal.Quotient.field _
  letI := (Ideal.quotientMap M (algebraMap O S) hM.ge).toAlgebra
  refine ⟨RingHom.injective _, fun x => ?_⟩
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hs : IsIntegral (O ⧸ maximalIdeal O) (Ideal.Quotient.mk M s) :=
    (Algebra.IsIntegral.isIntegral (R := O) s).map_of_comp_eq (Ideal.Quotient.mk _)
      (Ideal.Quotient.mk M) (Ideal.quotientMap_comp_mk _)
  exact minpoly.mem_range_of_degree_eq_one _ _
    (IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible hs))
end GlobalTheory.UnramifiedEmbedding
