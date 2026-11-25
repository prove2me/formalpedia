-- Prove2me | solution 1 for GlobalTheory.PowGerm.UnivJets.ker_aug_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:32:50.398174+00:00
-- url     : https://prove2.me/submissions/6169f38f-ac2f-4cd6-8b75-57c03b0ce70a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SaturationChartsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SurjectiveOfKerLeMapSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UniversalStatement
import Theorems.Thm_GlobalTheory_PowGerm_UnivJets_ker_aug_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetLift_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
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
variable {V : Type} [CommRing V]
open Chart (JetR zR jetAug_zR jet_ext jetLift jetLift_zR ker_jetAug_pow zR_mem_ker)
namespace GlobalTheory.PowGerm.UnivJets
theorem _root_.solution {κ : Type} {m : ℕ} {K : Ideal (JetR V κ m)} (h : ∀ j, zR m j ∈ K) :
    RingHom.ker (Chart.jetAug V κ m) ≤ K := by
  rw [ker_aug_eq, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  exact h j
end GlobalTheory.PowGerm.UnivJets
