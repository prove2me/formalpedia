-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.prod_eta_infinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:48:23.654159+00:00
-- url     : https://prove2.me/submissions/351645dc-929e-452f-9c0b-787b77a1bc09

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
import Theorems.Thm_GlobalTheory_QuadSymbol_eta_infinite_real
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_symm
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
end GlobalTheory.HilbertRecip
namespace GlobalTheory.QuadSymbol
open GlobalTheory.HilbertRecip
private lemma eta_infDiag_eq_one_of_isComplex {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    (e : Module.Basis (Fin 2) K L) (h0 : e 0 = 1) {δ : Kˣ} (h1 : e 1 * e 1 = algebraMap K L δ)
    (t : Kˣ) {w : InfinitePlace K} (hw : w.IsComplex) :
    eta K L w.Completion (infDiag K t w) = 1 := by
  rw [eta_eq_one_iff, mem_normGroup_iff_form e h0 h1]
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
      ((infDiag K t w : (w.Completion)ˣ) : w.Completion)) two_pos
  refine ⟨(InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm c, 0, ?_⟩
  have hsq : (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm c ^ 2 =
      ((infDiag K t w : (w.Completion)ˣ) : w.Completion) := by
    rw [← map_pow, hc, RingEquiv.symm_apply_apply]
  rw [hsq]
  simp
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
    (t : Kˣ) [Fintype (K →+* ℝ)] :
    ∏ w : InfinitePlace K, eta K L w.Completion (infDiag K t w) =
      ∏ σ : K →+* ℝ, hs (.inr σ) t δ := by
  classical
  let m : (K →+* ℝ) → InfinitePlace K := fun σ => InfinitePlace.mk (Complex.ofRealHom.comp σ)
  have hr : ∀ σ : K →+* ℝ, ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := fun σ =>
    ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => by
      simp [ComplexEmbedding.conjugate_coe_eq])
  have hm : ∀ σ, (m σ).IsReal := fun σ => InfinitePlace.isReal_mk_iff.2 (hr σ)
  have hemb : ∀ σ, InfinitePlace.embedding_of_isReal (hm σ) = σ := by
    intro σ
    ext x
    have h2 := InfinitePlace.embedding_of_isReal_apply (hm σ) x
    rw [InfinitePlace.embedding_mk_eq_of_isReal (hr σ)] at h2
    exact Complex.ofReal_injective h2
  have hinj : Function.Injective m := by
    intro σ τ h
    have h2 : InfinitePlace.embedding (m σ) = InfinitePlace.embedding (m τ) := by rw [h]
    simp only [m, InfinitePlace.embedding_mk_eq_of_isReal (hr σ),
      InfinitePlace.embedding_mk_eq_of_isReal (hr τ)] at h2
    ext x
    have h3 := RingHom.congr_fun h2 x
    simpa using h3
  have hsurj : ∀ w : InfinitePlace K, w.IsReal → ∃ σ, m σ = w := by
    intro w hw
    refine ⟨InfinitePlace.embedding_of_isReal hw, ?_⟩
    have h2 : Complex.ofRealHom.comp (InfinitePlace.embedding_of_isReal hw) =
        InfinitePlace.embedding w := by
      ext x
      simp
    show InfinitePlace.mk _ = w
    rw [h2, InfinitePlace.mk_embedding]
  calc ∏ w : InfinitePlace K, eta K L w.Completion (infDiag K t w)
      = ∏ w ∈ Finset.univ.image m, eta K L w.Completion (infDiag K t w) := by
        symm
        apply Finset.prod_subset (Finset.subset_univ _)
        intro w _ hw
        have hc : w.IsComplex := by
          rw [← InfinitePlace.not_isReal_iff_isComplex]
          intro hre
          obtain ⟨σ, rfl⟩ := hsurj w hre
          exact hw (Finset.mem_image_of_mem m (Finset.mem_univ σ))
        exact eta_infDiag_eq_one_of_isComplex e h0 h1 t hc
    _ = ∏ σ : K →+* ℝ, eta K L (m σ).Completion (infDiag K t (m σ)) := by
        apply Finset.prod_image
        intro x _ y _ h
        exact hinj h
    _ = ∏ σ : K →+* ℝ, hs (.inr σ) t δ := by
        refine Finset.prod_congr rfl fun σ _ => ?_
        rw [eta_infinite_real e h0 h1 t (hm σ), hemb σ]
end GlobalTheory.QuadSymbol
