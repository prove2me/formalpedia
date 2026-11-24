-- Prove2me | solution 1 for GlobalTheory.RootEx.UniformLattices.isOpen_ker_of_cball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:14:33.810799+00:00
-- url     : https://prove2.me/submissions/e27a69d0-ae4e-4ac0-a046-9325330dcd7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PositiveTwistAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OrbitLocallyConstant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenKerOfContinuous
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UniformLattices
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.RootEx.UniformLattices
theorem _root_.solution (μ : kˣ →* ℂˣ) (s : kˣ) (h : ∀ x : kˣ, (x : k) - 1 ∈ cball s → μ x = 1) :
    IsOpen (μ.ker : Set kˣ) := by
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have : (fun x : kˣ => (x : k) - 1) ⁻¹' cball s ∈ 𝓝 (1 : kˣ) :=
    ((isOpen_cball s).preimage (Units.continuous_val.sub continuous_const)).mem_nhds (by simp [cball])
  exact mem_of_superset this h
end GlobalTheory.RootEx.UniformLattices
