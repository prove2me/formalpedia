-- Prove2me | solution 1 for GlobalTheory.RootEx.UniformLattices.perp_mem_nhds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:37:13.565544+00:00
-- url     : https://prove2.me/submissions/cb551f4b-f635-4c0d-a4cb-aaaf127149b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PositiveTwistAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OrbitLocallyConstant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenKerOfContinuous
import Theorems.Thm_GlobalTheory_RootEx_UniformLattices_isCompact_lattice
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_SplitWeil_exists_cball_addChar_eq_one
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
variable {m : Type} [Fintype m]
variable {ψ : AddChar k Circle}
namespace GlobalTheory.RootEx.UniformLattices
theorem _root_.solution (hψ : Continuous ψ) (L : Submodule 𝒪[k] (m → k)) (hL : L.IsLattice k) :
    (perp ψ L : Set (m → k)) ∈ 𝓝 (0 : m → k) := by
  obtain ⟨s, hs⟩ := exists_cball_addChar_eq_one ψ hψ
  refine IsCompact.eventually_forall_of_forall_eventually (isCompact_lattice L hL)
    (P := fun β u => ψ (u ⬝ᵥ β) = 1) fun u _ => ?_
  have hc : Continuous fun q : (m → k) × (m → k) => q.2 ⬝ᵥ q.1 := by fun_prop
  filter_upwards [((isOpen_cball s).preimage hc).mem_nhds (x := (0, u)) (by simp [cball])] with q hq
  exact hs _ hq
end GlobalTheory.RootEx.UniformLattices
