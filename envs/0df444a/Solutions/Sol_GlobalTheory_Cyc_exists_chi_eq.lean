-- Prove2me | solution 1 for GlobalTheory.Cyc.exists_chi_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:53:33.323729+00:00
-- url     : https://prove2.me/submissions/420da098-5a03-4dd5-b301-063a97ba8a13

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjective
import Theorems.Thm_GlobalTheory_Cyc_exists_chi_approx
import Theorems.Thm_GlobalTheory_Cyc_cyc_basic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cyc
open Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
open scoped IntermediateField
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc
theorem _root_.solution (K : FinExt l) (χ : GQ l →* ℚ_[l]ˣ) (hχ : IsCyc χ) (u : ℚ_[l])
    (hu : ‖u‖ = 1) : ∃ g ∈ (K0 K).fixingSubgroup, (χ g : ℚ_[l]) = u := by
  have hlp : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  have hcont := (cyc_basic l χ hχ).2.1
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  have hcl : IsClosed ((K0 K).fixingSubgroup : Set (GQ l)) :=
    IntermediateField.fixingSubgroup_isClosed _
  have hc := (hcl.isCompact.image hcont).isClosed
  have hmem : u ∈ (fun g => (χ g : ℚ_[l])) '' ((K0 K).fixingSubgroup : Set (GQ l)) := by
    rw [← hc.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl1)
    obtain ⟨g, hg, hg'⟩ := exists_chi_approx K χ hχ u hu (n + 1) (by omega)
    refine ⟨_, ⟨g, hg, rfl⟩, ?_⟩
    rw [dist_comm, dist_eq_norm]
    refine hg'.trans_lt (lt_of_le_of_lt ?_ hn)
    rw [inv_pow, ← zpow_natCast, ← zpow_neg]
    exact zpow_le_zpow_right₀ hl1.le (by push_cast; omega)
  exact hmem
end GlobalTheory.Cyc
