-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.SmallPair.exists_realBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:33:35.651809+00:00
-- url     : https://prove2.me/submissions/421e188e-b0a4-4d3f-88bf-a1b8d70172a7

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsCuspReductionBound

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.SmallPair
namespace GlobalTheory.CompanionTheory.SW.SmallPair
theorem _root_.solution {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F)
    (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) :
    ∃ (κ : Type) (_ : Fintype κ) (b : Module.Basis κ ℝ (InfinitePlace F → ℝ)),
      ∀ i, ∃ a : 𝓞 F, ∀ w, b i w = ρ w (a : F) := by
  classical
  have hc : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mpr w.2 (hF.isReal w.1)⟩
  let e : mixedEmbedding.mixedSpace F ≃ₗ[ℝ] (InfinitePlace F → ℝ) :=
    { toFun := fun z w => z.1 ⟨w, hF.isReal w⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun v => (fun w => v w.1, fun w => (hc.false w).elim)
      left_inv := fun z => by
        refine Prod.ext rfl ?_
        funext w
        exact (hc.false w).elim
      right_inv := fun v => rfl }
  refine ⟨_, inferInstance, (mixedEmbedding.latticeBasis F).map e, fun i =>
    ⟨RingOfIntegers.basis F i, fun w => ?_⟩⟩
  have h1 : ((mixedEmbedding.latticeBasis F).map e) i w
      = InfinitePlace.embedding_of_isReal (hF.isReal w) (integralBasis F i) := by
    rw [Module.Basis.map_apply, mixedEmbedding.latticeBasis_apply]
    exact mixedEmbedding.mixedEmbedding_apply_isReal F _ ⟨w, hF.isReal w⟩
  rw [h1, integralBasis_apply]
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, hρ]
end GlobalTheory.CompanionTheory.SW.SmallPair
