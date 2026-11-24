-- Prove2me | solution 1 for GlobalTheory.HeckeSplitAll.Approx.exists_finset_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:15:52.429878+00:00
-- url     : https://prove2.me/submissions/0884bd08-3274-4701-9235-986bdfb71303

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_AddDense
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFinsetNormOne
import Theorems.Thm_GlobalTheory_HeckeSplitAll_Approx_norm_le_one_iff_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Topology Filter
open GlobalTheory GlobalTheory.HeckeSplitAll GlobalTheory.HeckeSplitAll.Approx
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeSplitAll.Approx
theorem _root_.solution (x : F) (hx : x ≠ 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, ‖algebraMap F (v.adicCompletion F) x‖ = 1 := by
  classical
  have h1 := Filter.eventually_cofinite.mp (algebraMap F (FiniteAdeleRing (𝓞 F) F) x).2
  have h2 := Filter.eventually_cofinite.mp (algebraMap F (FiniteAdeleRing (𝓞 F) F) x⁻¹).2
  refine ⟨(h1.union h2).toFinset, fun v hv => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hv
  obtain ⟨ha, hb⟩ := hv
  have ha' : ‖algebraMap F (v.adicCompletion F) x‖ ≤ 1 := (norm_le_one_iff_int v _).2 ha
  have hb' : ‖algebraMap F (v.adicCompletion F) x⁻¹‖ ≤ 1 := (norm_le_one_iff_int v _).2 hb
  rw [map_inv₀, norm_inv] at hb'
  have hpos : 0 < ‖algebraMap F (v.adicCompletion F) x‖ := norm_pos_iff.2 ((map_ne_zero _).2 hx)
  have hm := mul_inv_cancel₀ hpos.ne'
  refine le_antisymm ha' ?_
  nlinarith [mul_nonneg hpos.le (sub_nonneg.2 hb')]
end GlobalTheory.HeckeSplitAll.Approx
