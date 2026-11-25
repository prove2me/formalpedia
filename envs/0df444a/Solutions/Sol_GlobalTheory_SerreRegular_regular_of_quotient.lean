-- Prove2me | solution 1 for GlobalTheory.SerreRegular.regular_of_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:19:25.073547+00:00
-- url     : https://prove2.me/submissions/2fdebb82-77a2-4114-a82e-7c2c30efc083

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsHasProjectiveDimensionLEOfResidueField
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Theorems.Thm_GlobalTheory_SerreRegular_map_maximalIdeal_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat CategoryTheory TensorProduct
open GlobalTheory
open GlobalTheory.SerreRegular
namespace GlobalTheory.SerreRegular
theorem _root_.solution {A : Type} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] {x : A}
    (hx : IsSMulRegular A x) (hm : x ∈ maximalIdeal A)
    [IsRegularLocalRing (A ⧸ Ideal.span {x})] : IsRegularLocalRing A := by
  classical
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [← ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hx hm,
    ← IsRegularLocalRing.spanFinrank_maximalIdeal]
  obtain ⟨s, hs, hsp⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (IsNoetherian.noetherian (maximalIdeal (A ⧸ Ideal.span {x})))
  choose g hg using Ideal.Quotient.mk_surjective (I := Ideal.span {x})
  have hmap := map_maximalIdeal_eq (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  have h1 : Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) (Ideal.span (g '' s)) =
      maximalIdeal (A ⧸ Ideal.span {x}) := by
    rw [Ideal.map_span, Set.image_image]
    simpa [hg] using hsp
  have h2 : maximalIdeal A = Ideal.span ((insert x (s.image g) : Finset A) : Set A) := by
    have h3 := congrArg (Ideal.comap (Ideal.Quotient.mk (Ideal.span {x}))) (hmap.trans h1.symm)
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hm)] at h3
    rw [h3, Finset.coe_insert, Ideal.span_insert, Finset.coe_image, sup_comm]
  have h4 := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_span_finset_le
    (insert x (s.image g))
  rw [← h2] at h4
  have h5 := Finset.card_insert_le x (s.image g)
  have h6 : (s.image g).card ≤ s.card := Finset.card_image_le
  have h7 : (maximalIdeal A).spanFinrank ≤ (maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank + 1 := by
    omega
  exact_mod_cast h7
end GlobalTheory.SerreRegular
