-- Prove2me | solution 1 for GlobalTheory.PowGerm.UnivJets.jet_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:25:52.18288+00:00
-- url     : https://prove2.me/submissions/1d2d37cd-9ca6-42e8-b35d-67e6c19f62cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SaturationChartsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SurjectiveOfKerLeMapSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UniversalStatement
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
theorem _root_.solution (κ : Type) [Finite κ] (m : ℕ) : Module.Finite V (JetR V κ m) := by
  haveI : Algebra.IsIntegral V (JetR V κ m) := ⟨fun w => by
    have hw : w - algebraMap V _ (Chart.jetAug V κ m w) ∈ RingHom.ker (Chart.jetAug V κ m) := by
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes]
      simp
    have h0 : (w - algebraMap V _ (Chart.jetAug V κ m w)) ^ (m + 1) = 0 := by
      have := Ideal.pow_mem_pow hw (m + 1)
      rwa [ker_jetAug_pow, Ideal.mem_bot] at this
    have h1 : IsIntegral V (w - algebraMap V _ (Chart.jetAug V κ m w)) :=
      IsIntegral.of_pow (Nat.succ_pos m) (by rw [h0]; exact isIntegral_zero)
    have := h1.add (isIntegral_algebraMap (x := Chart.jetAug V κ m w))
    rwa [sub_add_cancel] at this⟩
  exact Algebra.IsIntegral.finite
end GlobalTheory.PowGerm.UnivJets
