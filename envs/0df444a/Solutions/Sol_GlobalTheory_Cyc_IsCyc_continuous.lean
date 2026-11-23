-- Prove2me | solution 1 for GlobalTheory.Cyc.IsCyc.continuous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:11.776895+00:00
-- url     : https://prove2.me/submissions/07490b9f-0a81-40f1-b93b-b8afd0ee81f4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Theorems.Thm_GlobalTheory_Cyc_exists_primRoot_pow
import Theorems.Thm_GlobalTheory_Cyc_IsCyc_norm_sub_one_le_of_prim
import Theorems.Thm_GlobalTheory_Cyc_exists_zpow_neg_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc
namespace IsCyc
theorem _root_.solution {χ : GQ l →* ℚ_[l]ˣ} (h : IsCyc χ) :
    Continuous (fun g => (χ g : ℚ_[l])) := by
  change Continuous ((Units.coeHom ℚ_[l]).comp χ)
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_zpow_neg_lt (l := l) hε
  obtain ⟨ζ, hζ⟩ := exists_primRoot_pow (l := l) m
  rw [Filter.Eventually, krullTopology_mem_nhds_one_iff]
  refine ⟨IntermediateField.adjoin ℚ_[l] {ζ},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ), ?_⟩
  intro g hg
  have hg' : g ζ = ζ := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ
    (IntermediateField.mem_adjoin_simple_self _ _)
  have := h.norm_sub_one_le_of_prim g m hζ hg'
  simp only [Set.mem_setOf_eq, map_one, dist_eq_norm]
  exact this.trans_lt hm
end IsCyc
end GlobalTheory.Cyc
