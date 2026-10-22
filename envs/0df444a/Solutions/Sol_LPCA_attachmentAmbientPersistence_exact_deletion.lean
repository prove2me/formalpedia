-- Prove2me | solution 1 for LPCA.attachmentAmbientPersistence_exact_deletion
-- status  : ACCEPTED   (prove)
-- author  : @kaiyue
-- created : 2026-10-22T01:26:07.478977+00:00
-- url     : https://prove2.me/submissions/aca5d693-42d3-46bb-b4e2-0a24cdd8a25c

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.Embedding.Restriction
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finsupp.ToDFinsupp
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Prod
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_redRestrictLin_dLin_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_complex_d_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_dLin_idxCongr_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_BassStatic_signed_restrictLin_dLin_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_dd_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_exists_insert_of_inc_ne_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_hc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_eq_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_sdiff_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_erase_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_gt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_lt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_sdiff_add_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_convex_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_mono_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SrFamily_faceFamily_of_subset_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientCechComplex_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientFieldScalars_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientHochsterRanks_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizationTelescope_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AttachmentRelativeAmbient_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AttachmentRelativeExactSequence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AttachmentRelativePersistence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CanonicalFaceOffset_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechComplex_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradedInclusions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechGradingColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechSquareZero_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTermGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CohomologyGradingInclusions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementFaceNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementLinkIdentities_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulAugmentation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulExt_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulHom_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulResolution_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszulTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinateKoszul_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CoordinatePowerCofinality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomologyLegs_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ExactnessThroughIsomorphisms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceLabelNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceOffsetNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionCoordinates_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionKoszulCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FamilyHochsterPersistence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredColimitHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FilteredHomologyNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFunctor_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FinitePiGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedFaceRestrictionCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedSupportRestriction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterActualComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterCochainComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterCochainNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterCohomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterIncidence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterLinkTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterNonfaceVanishing_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterPersistence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HochsterSigns_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HomLocalizationColumns_Defs
import Definitions.Def_LPCA_Solutions_LPCA_HomLocalizationDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ImagePersistence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulAugmentationNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulExactness_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomDiagram_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulHomTransitions_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulModuleNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_KoszulMultidegree_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LaurentFaceEvaluation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LegacyExtModuleNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LegacyExtNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LinkIdentities_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyCechComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyKoszulComparison_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalCohomologyModuleNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationTelescope_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDegreeSeparation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedGradingSpan_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedGrading_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ModuleDirectSumColimit_Defs
import Definitions.Def_LPCA_Solutions_LPCA_NatRestrictionHomology_Defs
import Definitions.Def_LPCA_Solutions_LPCA_NatRestrictionNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceCochains_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReducedFaceRestriction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_RelativeFaceCochains_Defs
import Definitions.Def_LPCA_Solutions_LPCA_RelativeFaceLabels_Defs
import Definitions.Def_LPCA_Solutions_LPCA_RelativeFaceNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_RelativePersistence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SupportCohomologyPieces_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexAttachmentImage_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexAttachmentNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexCechRestriction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexComplement_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexHochsterPersistence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexPiecePersistence_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

namespace LPCAUploadInline_LPCA_attachmentAmbientPersistence_exact_deletion
open LPCA
set_option autoImplicit false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]



theorem shortComplexIso_exact {A B D A' B' D' : C}
    (f : A ⟶ B) (g : B ⟶ D) (w : f ≫ g = 0)
    (h : (ShortComplex.mk f g w).Exact)
    (eA : A' ≅ A) (eB : B' ≅ B) (eD : D' ≅ D)
    (f' : A' ⟶ B') (g' : B' ⟶ D') (w' : f' ≫ g' = 0)
    (hf : f' ≫ eB.hom = eA.hom ≫ f)
    (hg : g' ≫ eD.hom = eB.hom ≫ g) : (ShortComplex.mk f' g' w').Exact := by
  let e : ShortComplex.mk f' g' w' ≅ ShortComplex.mk f g w :=
    ShortComplex.isoMk eA eB eD hf.symm hg.symm
  exact ShortComplex.exact_of_iso e.symm h

end LPCA

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]























theorem relativeFace_exact_absolute (rank : V ↪ ℕ)
    {K L : Complex V} (h : K.faces ⊆ L.faces) (r : ℤ) :
    (ShortComplex.mk (relativeFaceCohomologyToAbsolute k rank h r)
      (reducedFaceCohomologyRestriction k rank h r)
      (relativeFaceCohomologyToAbsolute_restriction_zero k rank h r)).Exact :=
  (relativeFaceShortExact k rank h).homology_exact₂ r





end LPCA

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

theorem persistenceShortComplex_exact_of_pointwise
    (S : ShortComplex (OrderDual ℝ ⥤ ModuleCat.{u} k))
    (h : ∀ t, (S.map ((evaluation (OrderDual ℝ) (ModuleCat.{u} k)).obj t)).Exact) : S.Exact := by
  rw [S.exact_iff_isZero_homology, Functor.isZero_iff]
  intro t
  exact (S.mapHomologyIso ((evaluation (OrderDual ℝ) (ModuleCat.{u} k)).obj t)).isZero_iff.mp
    (((S.map ((evaluation (OrderDual ℝ) (ModuleCat.{u} k)).obj t)).exact_iff_isZero_homology).mp (h t))

















/-- Exactness at the absolute A persistence module, in the literal
functor category of reversed real-indexed vector-space diagrams. -/
theorem relativePersistence_exact_absolute (rank : V ↪ ℕ)
    (A B : ℝ → Complex V) (hA : Monotone (fun t => (A t).faces))
    (hB : Monotone (fun t => (B t).faces)) (h : ∀ t, (B t).faces ⊆ (A t).faces) (r : ℤ) :
    (ShortComplex.mk (relativeToAbsoluteTransformation k rank A B hA hB h r)
      (pairRestrictionTransformation k rank A B hA hB h r)
      (relativeToAbsolute_pairRestriction_zero k rank A B hA hB h r)).Exact := by
  apply _root_.LPCAUploadInline_LPCA_attachmentAmbientPersistence_exact_deletion.LPCA.persistenceShortComplex_exact_of_pointwise
  intro t
  exact _root_.LPCAUploadInline_LPCA_attachmentAmbientPersistence_exact_deletion.LPCA.relativeFace_exact_absolute k rank (h (OrderDual.ofDual t)) r





end LPCA

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]



























/-- Exactness at the actual deletion Ext piece, literally in the persistence category. -/
theorem attachmentPersistence_exact_deletion (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (b : {v : V // v ≠ i} → ℤ) (q : ℕ) (hb : positiveSupport b = ∅) :
    (ShortComplex.mk (attachmentRelativeToDeletion k rank K f hf i b q hb)
      (vertexAttachmentPieceTransformation k rank K f hf i b q)
      (attachmentRelativeToDeletion_rho_zero k rank K f hf i b q hb)).Exact := by
  apply _root_.LPCAUploadInline_LPCA_attachmentAmbientPersistence_exact_deletion.LPCA.shortComplexIso_exact _ _
    (attachmentReduced_before_zero k rank K f hf i (negativeSupport b)
      ((q : ℤ) - ((negativeSupport b).card : ℤ) - 1))
    (_root_.LPCAUploadInline_LPCA_attachmentAmbientPersistence_exact_deletion.LPCA.relativePersistence_exact_absolute k ((complementEmbedding i).trans rank)
      _ _ _ _ (attachmentLinkPair_subset K f hf i (negativeSupport b)) _)
    (Iso.refl _) (vertexDeletionHochsterPersistenceIso k rank K f hf i b q hb)
    (vertexLinkHochsterPersistenceIso k rank K f hf i b q hb)
  · simp only [attachmentRelativeToDeletion, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.refl_hom, Category.id_comp]
  · exact vertexAttachmentPieceTransformation_hochster k rank K f hf i b q hb





end LPCA

end LPCAUploadInline_LPCA_attachmentAmbientPersistence_exact_deletion
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open LPCA

open CategoryTheory CategoryTheory.Limits

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]
open LPCAUploadInline_LPCA_attachmentAmbientPersistence_exact_deletion.LPCA


theorem solution (rank : V ↪ ℕ)
    (K : Complex V) (f : Finset V → ℝ) (hf : FiltrationMonotone K f) (i : V)
    (b : {v : V // v ≠ i} → ℤ) (q : ℕ) (hb : positiveSupport b = ∅) :
    (ShortComplex.mk (attachmentAmbientRelativeToDeletion k rank K f hf i b q hb)
      (vertexAttachmentPieceTransformation k rank K f hf i b q)
      (attachmentAmbient_before_zero k rank K f hf i b q hb)).Exact := by
  apply _root_.LPCAUploadInline_LPCA_attachmentAmbientPersistence_exact_deletion.LPCA.shortComplexIso_exact _ _
    (attachmentRelativeToDeletion_rho_zero k rank K f hf i b q hb)
    (_root_.LPCAUploadInline_LPCA_attachmentAmbientPersistence_exact_deletion.LPCA.attachmentPersistence_exact_deletion k rank K f hf i b q hb)
    (attachmentRelativeAmbientPersistenceIso k rank K f hf i (negativeSupport b)
      ((q : ℤ) - ((negativeSupport b).card : ℤ) - 1)) (Iso.refl _) (Iso.refl _)
  · simp only [attachmentAmbientRelativeToDeletion, Iso.refl_hom, Category.comp_id]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
