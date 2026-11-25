-- Prove2me | solution 1 for GlobalTheory.CongIndex.quot_smul_top_span_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:27:49.141271+00:00
-- url     : https://prove2.me/submissions/c9760a29-9b92-4016-905c-b5d61007f0c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexCongruenceSubgroupLeAbsNormPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.CongIndex
open scoped TensorProduct
namespace GlobalTheory.CongIndex
theorem _root_.solution {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    (∃ v : Fin (Module.finrank R N) → N ⧸ (I • ⊤ : Submodule R N), Submodule.span R (Set.range v) = ⊤) ∧
    Nat.card (N ⧸ (I • ⊤ : Submodule R N)) = Nat.card (R ⧸ I) ^ Module.finrank R N := by
  have : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) (Module.finrank R N)
    (fun P => by
      have := P.isMaximal
      let : Field ((R ⧸ I) ⧸ P.asIdeal) := Ideal.Quotient.field _
      rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal)
        ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]
      have h1 := Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥
      rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
      exact h1)
  refine ⟨⟨(TensorProduct.quotTensorEquivQuotSMul N I) ∘ b, ?_⟩, ?_⟩
  · have h1 : Submodule.span R (Set.range b) = ⊤ := by
      rw [← Submodule.restrictScalars_span R (R ⧸ I) Ideal.Quotient.mk_surjective, b.span_eq,
        Submodule.restrictScalars_top]
    have h2 := congrArg (Submodule.map (TensorProduct.quotTensorEquivQuotSMul N I).toLinearMap) h1
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h2
    rw [Set.range_comp]
    exact h2
  · rw [← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul N I).toEquiv,
      Nat.card_congr b.equivFun.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]
end GlobalTheory.CongIndex
