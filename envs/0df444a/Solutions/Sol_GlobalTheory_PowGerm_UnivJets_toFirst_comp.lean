-- Prove2me | solution 1 for GlobalTheory.PowGerm.UnivJets.toFirst_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:31:56.821907+00:00
-- url     : https://prove2.me/submissions/ad895dfe-06c3-4c79-88d6-3dc2af08aafe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SaturationChartsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SurjectiveOfKerLeMapSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UniversalStatement
import Theorems.Thm_P2M_GlobalTheory_PowGerm_UnivJets_spMap_id__2f109eb4c8e4
import Theorems.Thm_GlobalTheory_PowGerm_UnivJets_toFirst_succ
import Theorems.Thm_GlobalTheory_PowGerm_UnivJets_toFirst_zero
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_zR_mem_ker


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PowGerm.UnivJets
variable {V : Type} [CommRing V] {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
open Chart (JetR zR jetAug_zR jet_ext ker_jetAug_pow zR_mem_ker jetTruncR dualLift dualLift_zR fstD kerD_sq)
omit [GrpObj G]
namespace GlobalTheory.PowGerm.UnivJets
theorem _root_.solution {κ : Type} (z : ∀ m, Chart.sp (R₀ := V) (JetR V κ m) ⟶ G)
    (htr : ∀ m, Chart.spMap (jetTruncR V κ m) ≫ z (m + 1) = z m) (m : ℕ) :
    Chart.spMap (toFirst κ m) ≫ z (m + 1) = z 1 := by
  induction m with
  | zero =>
    have h : Chart.spMap (AlgHom.id V (JetR V κ 1)) ≫ z 1 = z 1 := by rw [spMap_id', Category.id_comp]
    exact (congrArg (fun f : JetR V κ 1 →ₐ[V] JetR V κ 1 => Chart.spMap f ≫ z 1) (toFirst_zero κ)).trans h
  | succ m ih => rw [toFirst_succ, ← Chart.spMap_comp, Category.assoc, htr, ih]
end GlobalTheory.PowGerm.UnivJets
