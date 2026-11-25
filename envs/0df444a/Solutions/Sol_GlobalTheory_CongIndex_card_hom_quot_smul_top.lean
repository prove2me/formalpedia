-- Prove2me | solution 1 for GlobalTheory.CongIndex.card_hom_quot_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:51:30.352143+00:00
-- url     : https://prove2.me/submissions/e3c041cd-5d7d-41be-9230-b058ebeccd43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexCongruenceSubgroupLeAbsNormPow
import Theorems.Thm_GlobalTheory_CongIndex_quot_smul_top_span_card
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
open GlobalTheory GlobalTheory.CongIndex
namespace GlobalTheory.CongIndex
theorem _root_.solution {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    Finite (N →ₗ[R] N ⧸ (I • ⊤ : Submodule R N)) ∧
    Nat.card (N →ₗ[R] N ⧸ (I • ⊤ : Submodule R N)) ≤ Nat.card (R ⧸ I) ^ (Module.finrank R N ^ 2) := by
  obtain ⟨⟨v, hv⟩, hc⟩ := quot_smul_top_span_card (R := R) (N := N) I
  have : Finite (N ⧸ (I • ⊤ : Submodule R N)) := Submodule.finite_quotient_smul I Module.Finite.fg_top
  have hk : ∀ f : N →ₗ[R] N ⧸ (I • ⊤ : Submodule R N), (I • ⊤ : Submodule R N) ≤ LinearMap.ker f := by
    intro f
    refine Submodule.smul_le.2 fun a ha x _ => ?_
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (f x)
    rw [LinearMap.mem_ker, map_smul, ← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  let Φ : (N →ₗ[R] N ⧸ (I • ⊤ : Submodule R N)) → (Fin (Module.finrank R N) → N ⧸ (I • ⊤ : Submodule R N)) :=
    fun f i => Submodule.liftQ _ f (hk f) (v i)
  have hΦ : Function.Injective Φ := by
    intro f g hfg
    have : Submodule.liftQ _ f (hk f) = Submodule.liftQ _ g (hk g) :=
      LinearMap.ext_on_range hv fun i => congrFun hfg i
    ext x
    simpa using LinearMap.congr_fun this (Submodule.Quotient.mk x)
  refine ⟨Finite.of_injective Φ hΦ, (Nat.card_le_card_of_injective Φ hΦ).trans_eq ?_⟩
  rw [Nat.card_fun, hc, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin, ← pow_mul, sq]
end GlobalTheory.CongIndex
