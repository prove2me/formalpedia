-- Prove2me | solution 1 for GlobalTheory.DegCnt.RatNormal.exists_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:34:22.056887+00:00
-- url     : https://prove2.me/submissions/13c24930-93c4-4743-9620-7e41534881e4

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsInvLower
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_memOfOrthogonalOrthogonal
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
theorem _root_.solution [FiniteDimensional K V] (G : FlagD H r) (b : Fin r) :
    ∃ y, ∀ a : Fin r, H.B (G.e a.castSucc) y = if a = b then 1 else 0 := by
  have hn : G.e b.castSucc ∉ Submodule.span K ((fun a : Fin r => G.e a.castSucc) '' {b}ᶜ) :=
    G.indep.notMem_span_image (by simp)
  have h := mt (memOfOrthogonalOrthogonal K V H _ (G.e b.castSucc)) hn
  push_neg at h
  obtain ⟨v, hv, hb⟩ := h
  refine ⟨star (H.B (G.e b.castSucc) v)⁻¹ • v, fun a => ?_⟩
  rw [map_smulₛₗ]
  split_ifs with hab
  · subst hab
    rw [starRingEnd_apply, star_star, smul_eq_mul, inv_mul_cancel₀ hb]
  · rw [hv _ (Submodule.subset_span ⟨a, hab, rfl⟩)]; simp
end GlobalTheory.DegCnt.RatNormal
