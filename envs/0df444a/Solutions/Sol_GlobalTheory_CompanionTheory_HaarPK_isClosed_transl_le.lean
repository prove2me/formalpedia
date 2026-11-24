-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HaarPK.isClosed_transl_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:37:01.730787+00:00
-- url     : https://prove2.me/submissions/6b2be2bc-14ed-476f-b74e-9292bf228210

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_HaarProductClosedCompact
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarProductClosedCompactHolds
import Theorems.Thm_GlobalTheory_CompanionTheory_HaarPK_measurable_transl_fun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HaarPK
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
namespace GlobalTheory.CompanionTheory.HaarPK
theorem _root_.solution (M : Subgroup G) (η : Measure M) [η.Regular] {U : Set G} (hU : IsOpen U) (t : ℝ≥0∞) :
    IsClosed {x | transl M η x U ≤ t} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [mem_compl_iff, mem_setOf_eq, not_le, transl] at hx
  rw [Measure.map_apply (measurable_transl_fun M x) hU.measurableSet] at hx
  have hopen : IsOpen ((fun m : M => x * (m : G)) ⁻¹' U) := hU.preimage (by fun_prop)
  obtain ⟨C, hCU, hC, ht⟩ := hopen.exists_lt_isCompact hx
  have : ∀ᶠ y in 𝓝 x, ∀ m ∈ C, y * (m : G) ∈ U := by
    apply hC.eventually_forall_of_forall_eventually
    intro m hm
    have hcont : Continuous (fun z : G × M => z.1 * (z.2 : G)) := by fun_prop
    exact hcont.continuousAt.eventually_mem (hU.mem_nhds (hCU hm))
  filter_upwards [this] with y hy
  simp only [mem_compl_iff, mem_setOf_eq, not_le, transl]
  rw [Measure.map_apply (measurable_transl_fun M y) hU.measurableSet]
  exact ht.trans_le (measure_mono hy)
end GlobalTheory.CompanionTheory.HaarPK
