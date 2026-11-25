-- Prove2me | solution 1 for GlobalTheory.DegCnt.Glue.exists_gens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:00:23.906828+00:00
-- url     : https://prove2.me/submissions/f0275841-c8d5-4eb6-8ede-405ccfebe713

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardUnimodularHermGluingsLe
import Theorems.Thm_GlobalTheory_DegCnt_Glue_finrank_baseChange_field
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Glue
open TensorProduct
namespace GlobalTheory.DegCnt.Glue
theorem _root_.solution (R M : Type) [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] (I : Ideal R) [Finite (R ⧸ I)] :
    ∃ t : Fin (Module.finrank R M) → M, ∀ N : Submodule R M, (∀ i, t i ∈ N) → I • (⊤ : Submodule R M) ≤ N →
      N = ⊤ := by
  have : Finite (MaximalSpectrum (R ⧸ I)) := inferInstance
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] M) (Module.finrank R M) (by
    intro P
    have := P.isMaximal
    let _ := Ideal.Quotient.field P.asIdeal
    rw [(AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal) ((R ⧸ I) ⧸ P.asIdeal) M).finrank_eq]
    exact finrank_baseChange_field R M _)
  have hs : Function.Surjective (TensorProduct.mk R (R ⧸ I) M 1) :=
    TensorProduct.mk_surjective R M (R ⧸ I) Ideal.Quotient.mk_surjective
  choose t ht using fun i => hs (b i)
  refine ⟨t, fun N hN hI => eq_top_iff.2 fun m _ => ?_⟩
  choose a ha using fun i => Ideal.Quotient.mk_surjective (b.repr (TensorProduct.mk R (R ⧸ I) M 1 m) i)
  have h0 : TensorProduct.mk R (R ⧸ I) M 1 (m - ∑ i, a i • t i) = 0 := by
    rw [map_sub, map_sum, sub_eq_zero]
    conv_lhs => rw [← b.sum_repr (TensorProduct.mk R (R ⧸ I) M 1 m)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ht, ← ha, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
  have h1 : m - ∑ i, a i • t i ∈ I • (⊤ : Submodule R M) := by
    have := congrArg (TensorProduct.quotTensorEquivQuotSMul M I) h0
    rw [map_zero] at this
    rw [← Submodule.Quotient.mk_eq_zero, ← this]
    simp
  have h2 := N.add_mem (hI h1) (N.sum_mem (t := Finset.univ) fun i _ => N.smul_mem (a i) (hN i))
  simpa using h2
end GlobalTheory.DegCnt.Glue
