-- Prove2me | solution 1 for GlobalTheory.RootEx.UniformLattices.isCompact_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:26:05.698578+00:00
-- url     : https://prove2.me/submissions/01ec57a6-2db2-488a-9418-a86ead8cb74d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PositiveTwistAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OrbitLocallyConstant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenKerOfContinuous
import Theorems.Thm_GlobalTheory_RootEx_UniformLattices_exists_subset_ballLat
import Theorems.Thm_GlobalTheory_LatPair_isClopen_lattice
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_cball


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UniformLattices
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {m : Type} [Fintype m]
namespace GlobalTheory.RootEx.UniformLattices
theorem _root_.solution (L : Submodule 𝒪[k] (m → k)) (hL : L.IsLattice k) : IsCompact (L : Set (m → k)) := by
  obtain ⟨S, hS⟩ := hL.fg
  obtain ⟨s, hs⟩ := exists_subset_ballLat (K := (S : Set (m → k))) S.finite_toSet.isCompact
  have h1 : L ≤ ballLat m s := hS ▸ Submodule.span_le.2 hs
  have h2 : IsCompact (ballLat m s : Set (m → k)) := by
    have := isCompact_univ_pi fun _ : m => isCompact_cball s
    convert this using 1
    ext x; exact ⟨fun h i _ => h i, fun h i => h i trivial⟩
  exact h2.of_isClosed_subset (LatPair.isClopen_lattice L).1 h1
end GlobalTheory.RootEx.UniformLattices
