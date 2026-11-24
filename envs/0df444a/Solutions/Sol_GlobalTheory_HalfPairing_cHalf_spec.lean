-- Prove2me | solution 1 for GlobalTheory.HalfPairing.cHalf_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:12:51.457155+00:00
-- url     : https://prove2.me/submissions/8d1c3bcb-570f-4f37-b497-6b96edf8f8c4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegPFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LiftLaSpec
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HalvesFreeAndAdjoint

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
open GlobalTheory GlobalTheory.HalfPairing
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
namespace GlobalTheory.HalfPairing
theorem _root_.solution (I : Ideal (𝓞 E)) (hI : I ⊔ I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) :
    cHalf H I ∈ I.map (H.bar : 𝓞 E →+* 𝓞 E) ∧ cHalf H I - 1 ∈ I := by
  have h : ∃ c, c ∈ I.map (H.bar : 𝓞 E →+* 𝓞 E) ∧ c - 1 ∈ I := by
    obtain ⟨m, hm, mb, hmb, hsum⟩ := Submodule.mem_sup.1 (hI ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ I ⊔ _)
    refine ⟨mb, hmb, ?_⟩
    have : mb - 1 = -m := by rw [← hsum]; ring
    rw [this]; exact neg_mem hm
  unfold cHalf
  rw [dif_pos h]
  exact h.choose_spec
end GlobalTheory.HalfPairing
