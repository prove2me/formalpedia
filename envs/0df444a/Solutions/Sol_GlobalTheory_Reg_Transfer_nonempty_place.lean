-- Prove2me | solution 1 for GlobalTheory.Reg.Transfer.nonempty_place
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:54:10.879007+00:00
-- url     : https://prove2.me/submissions/8f88eaec-7b1e-4430-8cc8-354cd825f5bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FnTrdegOf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RealPtGeo
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentreChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_TransferLawOfNormalCharts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.Transfer
namespace GlobalTheory.Reg.Transfer
theorem _root_.solution (K : Type) [Field K] [NumberField K] : Nonempty (HeightOneSpectrum (𝓞 K)) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 K)
  exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩⟩
end GlobalTheory.Reg.Transfer
