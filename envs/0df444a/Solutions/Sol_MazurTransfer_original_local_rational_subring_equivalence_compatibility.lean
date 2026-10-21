-- Prove2me | solution 1 for MazurTransfer.original_local_rational_subring_equivalence_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T02:06:43.912882+00:00
-- url     : https://prove2.me/submissions/905a0232-a1dc-4b75-86e5-f1d06b954aa5

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
The same rational-subring localization uses the complete official Anthropic FLT input at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2.
Design boundary: the existing localization ring and the original rational-subring ring are related by the original equivalence preserving the same rational and coefficient embeddings.
Named downstream consumer: classification of the same selected actual integral nineteen character quotient.
-/
import Definitions.Def_MazurTransfer_OriginalLocalRationalSubringEquivalenceData20261020
noncomputable section
open MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13LocalRationalSubringEquivalence
attribute [local instance] MazurTransfer.Order13LocalRationalSubringEquivalence.instAtPrimeIntSubtypeRatMemSubringRatLocalizedAtPrimeIdeal_order13LocalRationalSubringEquivalence
namespace MazurTransfer.OriginalLocalRationalSubringEquivalenceBoundary20261020
end MazurTransfer.OriginalLocalRationalSubringEquivalenceBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the EXISTING localization coefficient ring
with the rational-subring coefficient ring in the complete FLT Hopf
classification, proving compatibility with the SAME rational embedding.
Named downstream consumer: actual selected character quotient classification
at nineteen; no definitional identification of base rings is assumed.
-/

noncomputable section
namespace MazurTransfer.OriginalLocalRationalSubringEquivalenceProof20261020
open Order13LocalIntegralCoefficientMaps
variable (q : ℕ) [Fact q.Prime]





theorem rational_embedding_comp_equiv :
    (GaloisRep.ratLocalizedAt q).subtype.comp (localRationalSubringEquiv q).toRingHom =
      algebraMap (LocalRing q) ℚ := by
  apply IsLocalization.ringHom_ext (primeIdeal q).primeCompl
  apply RingHom.ext
  intro z
  change ((localRationalSubringEquiv q) (algebraMap ℤ (LocalRing q) z) : ℚ) =
    algebraMap (LocalRing q) ℚ (algebraMap ℤ (LocalRing q) z)
  rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply ℤ (LocalRing q) ℚ]
  rfl

theorem rational_embedding_equiv_apply (r : LocalRing q) :
    ((localRationalSubringEquiv q r : GaloisRep.ratLocalizedAt q) : ℚ) =
      algebraMap (LocalRing q) ℚ r :=
  RingHom.congr_fun (rational_embedding_comp_equiv q) r

theorem rational_embedding_symm_apply (r : GaloisRep.ratLocalizedAt q) :
    algebraMap (LocalRing q) ℚ ((localRationalSubringEquiv q).symm r) = (r : ℚ) := by
  rw [← rational_embedding_equiv_apply, AlgEquiv.apply_symm_apply]

variable (K : Type) [CommRing K] [Algebra ℚ K]
variable [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K]
variable [Algebra (GaloisRep.ratLocalizedAt q) K]
variable [IsScalarTower (GaloisRep.ratLocalizedAt q) ℚ K]

theorem field_embedding_equiv_apply (r : LocalRing q) :
    algebraMap (GaloisRep.ratLocalizedAt q) K (localRationalSubringEquiv q r) =
      algebraMap (LocalRing q) K r := by
  rw [IsScalarTower.algebraMap_apply (GaloisRep.ratLocalizedAt q) ℚ K,
    IsScalarTower.algebraMap_apply (LocalRing q) ℚ K]
  exact congrArg (algebraMap ℚ K) (rational_embedding_equiv_apply q r)

theorem field_embedding_symm_apply (r : GaloisRep.ratLocalizedAt q) :
    algebraMap (LocalRing q) K ((localRationalSubringEquiv q).symm r) =
      algebraMap (GaloisRep.ratLocalizedAt q) K r := by
  rw [← field_embedding_equiv_apply, AlgEquiv.apply_symm_apply]

end MazurTransfer.OriginalLocalRationalSubringEquivalenceProof20261020


theorem solution : (∀ (q : ℕ) [Fact q.Prime] ,
(GaloisRep.ratLocalizedAt q).subtype.comp (localRationalSubringEquiv q).toRingHom =
      algebraMap (LocalRing q) ℚ) ∧ (∀ (q : ℕ) [Fact q.Prime] (r : LocalRing q),
((localRationalSubringEquiv q r : GaloisRep.ratLocalizedAt q) : ℚ) =
      algebraMap (LocalRing q) ℚ r) ∧ (∀ (q : ℕ) [Fact q.Prime] (r : GaloisRep.ratLocalizedAt q),
algebraMap (LocalRing q) ℚ ((localRationalSubringEquiv q).symm r) = (r : ℚ)) ∧ (∀ (q : ℕ) [Fact q.Prime] (K : Type) [CommRing K] [Algebra ℚ K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K] [Algebra (GaloisRep.ratLocalizedAt q) K] [IsScalarTower (GaloisRep.ratLocalizedAt q) ℚ K] (r : LocalRing q),
algebraMap (GaloisRep.ratLocalizedAt q) K (localRationalSubringEquiv q r) =
      algebraMap (LocalRing q) K r) ∧ (∀ (q : ℕ) [Fact q.Prime] (K : Type) [CommRing K] [Algebra ℚ K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K] [Algebra (GaloisRep.ratLocalizedAt q) K] [IsScalarTower (GaloisRep.ratLocalizedAt q) ℚ K] (r : GaloisRep.ratLocalizedAt q),
algebraMap (LocalRing q) K ((localRationalSubringEquiv q).symm r) =
      algebraMap (GaloisRep.ratLocalizedAt q) K r) := by
  exact ⟨MazurTransfer.OriginalLocalRationalSubringEquivalenceProof20261020.rational_embedding_comp_equiv, MazurTransfer.OriginalLocalRationalSubringEquivalenceProof20261020.rational_embedding_equiv_apply, MazurTransfer.OriginalLocalRationalSubringEquivalenceProof20261020.rational_embedding_symm_apply, MazurTransfer.OriginalLocalRationalSubringEquivalenceProof20261020.field_embedding_equiv_apply, MazurTransfer.OriginalLocalRationalSubringEquivalenceProof20261020.field_embedding_symm_apply⟩
#print axioms solution
