-- Prove2me | solution 1 for GlobalTheory.Published.SvN.exists_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:39:58.353349+00:00
-- url     : https://prove2.me/submissions/59f0085f-f44c-4e8f-9bc8-902546e4b440

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN
open ValuativeRel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.Published.SvN
theorem _root_.solution {p : F → Prop} (hp : ∀ᶠ r in 𝓝 (0 : F), p r) : ∃ r, r ≠ 0 ∧ p r := by
  obtain ⟨γ, hγ, hs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' F).mem_iff.1 hp
  obtain ⟨y, rfl⟩ := ValuativeRel.valuation_surjective γ
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation F)
  refine ⟨y * r, mul_ne_zero (by simpa using hγ) hr, hs ?_⟩
  show valuation F (y * r) < valuation F y
  rw [map_mul]
  exact mul_lt_of_lt_one_right (zero_lt_iff.2 hγ) hr1
end GlobalTheory.Published.SvN
