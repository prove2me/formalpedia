-- Prove2me | solution 1 for GlobalTheory.Survey.BaseClassMove.latAdm_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:22:17.244578+00:00
-- url     : https://prove2.me/submissions/723a8e0f-51c2-4cc7-aa1a-369b6333d58f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BaseClassMove

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
open GlobalTheory GlobalTheory.Survey GlobalTheory.Survey.BaseClassMove
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
namespace GlobalTheory.Survey.BaseClassMove
theorem _root_.solution (l : Level H) (bad n : ℕ) : LatAdm l bad (unitLat E n) := by
  have ht : ∀ m, (unitLat E n).TrivAt m := fun m => ⟨1, by simp, by simp [unitLat], by simp [unitLat]⟩
  refine ⟨fun v => ⟨fun hv w hw => ?_, fun hv => ?_⟩, ht _, ht _⟩
  · refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ ?_ ?_
    · obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hv j trivial)
      exact ⟨H.bar a, by rw [← ha]; exact H.bar_eq a⟩
    · obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hw j trivial)
      exact ⟨a, ha⟩
  · intro j _
    have h := hv (Pi.single j 1) (fun i _ => by
      by_cases hi : i = j
      · subst hi; simpa using Submodule.one_le.1 le_rfl
      · simp [Pi.single_eq_of_ne hi])
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    obtain ⟨a, ha⟩ := h
    refine Submodule.mem_one.2 ⟨H.bar a, ?_⟩
    have := H.bar_eq a
    change ((H.bar a : 𝓞 E) : E) = v j
    rw [this]
    change IsCMField.complexConj E (algebraMap _ _ a) = _
    rw [ha, IsCMField.complexConj_apply_apply]
end GlobalTheory.Survey.BaseClassMove
