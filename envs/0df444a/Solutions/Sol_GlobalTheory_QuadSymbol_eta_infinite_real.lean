-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.eta_infinite_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:34:11.861082+00:00
-- url     : https://prove2.me/submissions/4cbacd21-d5a0-4be7-9b98-b46ec6358345

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AlmostNormFinDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsApproxModLocalSquares
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsLocalNonnormOfNonsquareAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexSquaresSUnitsNumberField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitValuationEqOfAdm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAdmissibleSupersetFinitePlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSupersetMemSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsQuadraticSqrtExtensionOfNotSquare
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsSupUnitsLocalNormsSqrtNeTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRingHomAdicCompletionUnder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAuxiliaryPlacesSquarePatternsSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsUnionSupLocalSquaresEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfSUnitLocalSquareFiniteRealPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitMemGlobalNormOfMemLocalNorms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasseNormTheoremQuadraticExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsLocalSquaresFiniteRealPlacesLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EvenCardOfNotLone
import Theorems.Thm_GlobalTheory_HilbertRecip_hs_eq_one_iff
import Theorems.Thm_GlobalTheory_HilbertRecip_hs_eq_neg_one_iff
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_QNorm_mem_normSub
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_symm
import Theorems.Thm_GlobalTheory_QuadSymbol_eta_eq_neg_one_iff
import Theorems.Thm_GlobalTheory_QuadSymbol_eta_eq_one_iff
import Theorems.Thm_GlobalTheory_QuadSymbol_mem_normGroup_iff_form
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero


section
open NumberField IsDedekindDomain GlobalTheory.QNorm GlobalTheory.QuadSymbol.NormIndex
noncomputable section
namespace GlobalTheory.HilbertRecip
variable {F : Type} [Field F] [NumberField F]
private lemma ringEquivRealOfIsReal_algebraMap {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}
    (hw : w.IsReal) (x : K) :
    InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap K w.Completion x) =
      InfinitePlace.embedding_of_isReal hw x := by
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply, InfinitePlace.Completion.algebraMap_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
  first
  | rfl
  | simp
  | rw [← WithAbs.equiv_symm_apply, RingEquiv.apply_symm_apply]
end GlobalTheory.HilbertRecip
namespace GlobalTheory.QuadSymbol
open GlobalTheory.HilbertRecip
end GlobalTheory.QuadSymbol
end
end

set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm GlobalTheory.QuadSymbol.NormIndex
noncomputable section
open GlobalTheory GlobalTheory.QuadSymbol
open GlobalTheory.HilbertRecip
namespace GlobalTheory.QuadSymbol
theorem _root_.solution {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    (e : Module.Basis (Fin 2) K L) (h0 : e 0 = 1) {δ : Kˣ} (h1 : e 1 * e 1 = algebraMap K L δ)
    (t : Kˣ) {w : InfinitePlace K} (hw : w.IsReal) :
    eta K L w.Completion (infDiag K t w) =
      hs (.inr (InfinitePlace.embedding_of_isReal hw)) t δ := by
  obtain ⟨f, hf⟩ : ∃ f : w.Completion ≃+* ℝ, ∀ x : K,
      f (algebraMap K w.Completion x) = InfinitePlace.embedding_of_isReal hw x :=
    ⟨_, ringEquivRealOfIsReal_algebraMap hw⟩
  have key : infDiag K t w ∈ normGroup K L w.Completion ↔
      t ∈ nrm (.inr (InfinitePlace.embedding_of_isReal hw)) δ := by
    rw [mem_normGroup_iff_form e h0 h1]
    have ht : ((infDiag K t w : (w.Completion)ˣ) : w.Completion) = algebraMap K w.Completion t := rfl
    rw [ht]
    show _ ↔ t ∈ normSub (InfinitePlace.embedding_of_isReal hw) (δ : K)
    rw [mem_normSub]
    constructor
    · rintro ⟨a, b, hab⟩
      refine ⟨f a, f b, ?_⟩
      have := congrArg f hab
      simp only [map_sub, map_mul, map_pow, hf] at this
      exact this
    · rintro ⟨a, b, hab⟩
      refine ⟨f.symm a, f.symm b, f.injective ?_⟩
      rw [hf, hab]
      simp only [map_sub, map_mul, map_pow, hf, RingEquiv.apply_symm_apply]
  by_cases h : t ∈ nrm (.inr (InfinitePlace.embedding_of_isReal hw)) δ
  · rw [eta_eq_one_iff.2 (key.2 h), hs_eq_one_iff.2 h]
  · rw [eta_eq_neg_one_iff.2 (fun h' => h (key.1 h')), hs_eq_neg_one_iff.2 h]
end GlobalTheory.QuadSymbol
