-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FD.exists_integral_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:20:13.703874+00:00
-- url     : https://prove2.me/submissions/d6ff553c-e412-4867-899e-dd2e4982c195

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeFundamentalDomainVolume
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FD_card_places

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FD
open scoped Pointwise
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.SW.FD
theorem _root_.solution [DecidableEq (InfinitePlace F)] (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) :
    ∃ B : Module.Basis (InfinitePlace F) ℤ (𝓞 F),
      (Matrix.det (Matrix.of fun i w => ρ w ((B i : 𝓞 F) : F))) ^ 2 = (discr F : ℝ) := by
  classical
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) = Fintype.card (InfinitePlace F) := by
    rw [card_places hF, ← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  let e0 := Fintype.equivOfCardEq hc
  let bq := (integralBasis F).reindex e0
  refine ⟨(RingOfIntegers.basis F).reindex e0, ?_⟩
  have h := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ bq (placeEquiv hF)
  have hd : Algebra.discr ℚ bq = (discr F : ℚ) := by
    rw [coe_discr]
    have h0 := Algebra.discr_reindex ℚ (integralBasis F) e0
    rwa [← Module.Basis.coe_reindex] at h0
  have hM : Algebra.embeddingsMatrixReindex ℚ ℂ bq (placeEquiv hF) =
      (Matrix.of fun i w => ρ w (((RingOfIntegers.basis F).reindex e0 i : 𝓞 F) : F)).map
        Complex.ofRealHom := by
    ext i w
    simp [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, placeEquiv, bq, hρ,
      integralBasis_apply, Module.Basis.reindex_apply]
  rw [hM, hd, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  have h2 : (((discr F : ℝ)) : ℂ) = (((Matrix.det (Matrix.of fun i w =>
      ρ w (((RingOfIntegers.basis F).reindex e0 i : 𝓞 F) : F))) ^ 2 : ℝ) : ℂ) := by
    simpa using h
  exact_mod_cast h2.symm
end GlobalTheory.CompanionTheory.SW.FD
