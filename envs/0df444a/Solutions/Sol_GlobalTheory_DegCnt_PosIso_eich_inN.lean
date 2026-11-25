-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosIso.eich_inN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:30:39.79906+00:00
-- url     : https://prove2.me/submissions/29dca5a0-9f25-4ddb-9af7-8dec6d63fc63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_eich_apply
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_swap0
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_X_iso
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_eich_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_eichlerMapIsometry
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_perp_X
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
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosIso
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V} {r : ℕ}
omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.PosIso
theorem _root_.solution (F : FlagD H r) (x v : V) (c : K) (hx : x ∈ F.X) (hxv : H.B x v = 0)
    (hc : c + star c = -H.B v v) (hlev : ∀ a : Fin r, H.B (F.e a.castSucc) v • x ∈ F.Xa a.val) :
    F.InN (eich H x v c) := by
  obtain ⟨h1, h2, h3⟩ := eichlerMapIsometry K V H x v c (X_iso F hx hx) hxv hc
  refine ⟨h1, ⟨Function.LeftInverse.injective h2, Function.RightInverse.surjective h3⟩, fun a => ?_, fun y hy => ?_⟩
  · simpa [eich_apply, e_X F _ hx] using hlev a
  · have : H.B y x = 0 := B_swap0 H (perp_X F hy x hx)
    simpa [eich_apply, this] using Submodule.smul_mem _ _ hx
end GlobalTheory.DegCnt.PosIso
