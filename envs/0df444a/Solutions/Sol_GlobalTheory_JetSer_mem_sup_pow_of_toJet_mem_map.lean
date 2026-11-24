-- Prove2me | solution 1 for GlobalTheory.JetSer.mem_sup_pow_of_toJet_mem_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:41:26.258339+00:00
-- url     : https://prove2.me/submissions/85c65b82-6803-4e7a-bafd-46d51fd0649e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RepJetAugCompTrunc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniversalThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_LocallyOfFiniteTypePullbackUnit
import Theorems.Thm_GlobalTheory_JetSer_toJet_coe
import Theorems.Thm_GlobalTheory_JetSer_toJet_eq_iff
import Theorems.Thm_GlobalTheory_germIdeal_eq_span
import Theorems.Thm_GlobalTheory_mem_germIdeal_pow_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer
namespace GlobalTheory.JetSer
theorem _root_.solution {R : Type} [CommRing R] {κ : Type} [Finite κ] (m : ℕ)
    (I : Ideal (MvPowerSeries κ R)) (g : MvPowerSeries κ R) (hg : toJet m g ∈ I.map (toJetHom R κ m)) :
    g ∈ I ⊔ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ R)) ^ (m + 1) := by
  have hs : Function.Surjective (toJetHom R κ m) := fun q => by
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨P, toJet_coe m P⟩
  obtain ⟨h, hh, e⟩ := (Ideal.mem_map_iff_of_surjective _ hs).1 hg
  have h2 : g - h ∈ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ R)) ^ (m + 1) := by
    rw [← germIdeal_eq_span, mem_germIdeal_pow_iff]
    intro d hd
    rw [map_sub, (toJet_eq_iff m h g).1 e d hd, sub_self]
  have : g = h + (g - h) := by ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mem_sup_left hh) (Ideal.mem_sup_right h2)
end GlobalTheory.JetSer
