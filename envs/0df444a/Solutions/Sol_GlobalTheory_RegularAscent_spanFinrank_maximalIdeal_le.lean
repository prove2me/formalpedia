-- Prove2me | solution 1 for GlobalTheory.RegularAscent.spanFinrank_maximalIdeal_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:55:18.811008+00:00
-- url     : https://prove2.me/submissions/710fc89f-9380-48b7-884a-7530c04df1ed

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRegularLocalRingOfRegularQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.RegularAscent
namespace GlobalTheory.RegularAscent
theorem _root_.solution {R : Type} [CommRing R] [IsLocalRing R] (p : Ideal R)
    [p.IsPrime] [IsLocalRing (R ⧸ p)] (r : ℕ) (f : Fin r → R) (hf : p = Ideal.span (Set.range f))
    (hfg : (maximalIdeal (R ⧸ p)).FG) :
    (maximalIdeal R).spanFinrank ≤ r + (maximalIdeal (R ⧸ p)).spanFinrank := by
  classical
  obtain ⟨s, hs, hsp⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  choose g hg using Ideal.Quotient.mk_surjective (I := p)
  have hpm : p ≤ maximalIdeal R := le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
  have hmap : (maximalIdeal R).map (Ideal.Quotient.mk p) = maximalIdeal (R ⧸ p) :=
    map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have h1 : Ideal.map (Ideal.Quotient.mk p) (Ideal.span (g '' s)) = maximalIdeal (R ⧸ p) := by
    rw [Ideal.map_span, Set.image_image]
    simpa [hg] using hsp
  have h2 : maximalIdeal R =
      Ideal.span (((s.image g) ∪ Finset.univ.image f : Finset R) : Set R) := by
    have h3 := congrArg (Ideal.comap (Ideal.Quotient.mk p)) (hmap.trans h1.symm)
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr hpm] at h3
    rw [h3, Finset.coe_union, Ideal.span_union, Finset.coe_image, Finset.coe_image,
      Finset.coe_univ, Set.image_univ, ← hf]
  have h4 := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_span_finset_le
    ((s.image g) ∪ Finset.univ.image f)
  rw [← h2] at h4
  have h5 := Finset.card_union_le (s.image g) (Finset.univ.image f)
  have h6 : (s.image g).card ≤ s.card := Finset.card_image_le
  have h7 : (Finset.univ.image f).card ≤ r := Finset.card_image_le.trans (by simp)
  omega
end GlobalTheory.RegularAscent
