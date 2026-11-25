-- Prove2me | solution 1 for GlobalTheory.T.isOpen_subgroup_of_siegel_and_opposite_nhds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:22:31.273665+00:00
-- url     : https://prove2.me/submissions/1db13d99-1412-4a3c-941b-b260f27ec630

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenSubgroupOfSiegelAndOppositeNhds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenSubgroupOfSiegelAndOppositeNhdsStatement
import Theorems.Thm_GlobalTheory_KSp_isOpen_of_sieg_of_opp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (U : Subgroup (UG c (stdJ ν E))), (∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → g ∈ U) → (∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → (weyl c ν)⁻¹ * g * weyl c ν ∈ U) → IsOpen (U : Set (UG c (stdJ ν E))) := by
  first | exact @GlobalTheory.KSp.isOpen_of_sieg_of_opp | exact GlobalTheory.KSp.isOpen_of_sieg_of_opp | (intros; apply GlobalTheory.KSp.isOpen_of_sieg_of_opp <;> assumption)
end _root_.GlobalTheory.T
