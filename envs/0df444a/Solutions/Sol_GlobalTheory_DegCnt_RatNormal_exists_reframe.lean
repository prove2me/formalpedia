-- Prove2me | solution 1 for GlobalTheory.DegCnt.RatNormal.exists_reframe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:11:51.924796+00:00
-- url     : https://prove2.me/submissions/9c3dd681-aeba-4cf3-b223-60694de2a0e4

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsInvLower
import Theorems.Thm_GlobalTheory_DegCnt_RatNormal_span_change
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_X_iso
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_le_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_mem_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_finrank_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pairing_isotropicSpan_lastVector
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pairing_lastVector_lastVector
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_z_X
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
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.HermitianLatticeCounting.P
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.RatNormal
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegCnt.RatNormal
theorem _root_.solution (F : FlagD H r) (f : Fin (r + 1) → V) (hf : ∀ a, f a - F.e a ∈ F.Xa a.val) :
    ∃ G : FlagD H r, G.e = f ∧ G.T = F.T ∧ ∀ n, G.Xa n = F.Xa n := by
  have hX : ∀ a : Fin r, f a.castSucc ∈ F.X := fun a => by
    simpa using Submodule.add_mem _ (Xa_le_X F _ (hf a.castSucc)) (e_mem_X F a)
  obtain ⟨x, hx, hz⟩ : ∃ x ∈ F.X, f (Fin.last r) = F.z + x :=
    ⟨_, Xa_le_X F _ (hf (Fin.last r)), by simp [FlagD.z]⟩
  refine ⟨⟨f, F.T, ?_, fun a b => X_iso F (hX a) (hX b), fun a => ?_, ?_, F.hT⟩, rfl, rfl,
    fun n => span_change F f hf n⟩
  · rw [linearIndependent_iff_card_eq_finrank_span]
    have h := span_change F f hf r
    have h2 : {b : Fin r | b.val < r} = Set.univ := Set.eq_univ_of_forall fun b => b.isLt
    rw [h2, Set.image_univ] at h
    rw [Set.finrank, h, Fintype.card_fin]
    exact (finrank_X F).symm
  · rw [hz, map_add, pairing_isotropicSpan_lastVector F (hX a), X_iso F (hX a) hx, add_zero]
  · rw [hz]
    simp only [map_add, LinearMap.add_apply, pairing_lastVector_lastVector, pairing_isotropicSpan_lastVector F hx, z_X F hx, X_iso F hx hx, add_zero]
end GlobalTheory.DegCnt.RatNormal
