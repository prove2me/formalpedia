-- Prove2me | solution 1 for GlobalTheory.NonGenericLocalCheck.isTermOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:07:26.807796+00:00
-- url     : https://prove2.me/submissions/1bbced5a-1dd9-4a45-ab47-8f74833abb56

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_TransversalityLocal_FramePairFixatorUnitaryAndFixesFrame
import Theorems.Thm_GlobalTheory_NonGenericLocalCheck_img_one
import Theorems.Thm_GlobalTheory_NonGenericLocalCheck_theta_some
import Theorems.Thm_GlobalTheory_NonGenericLocalCheck_lamStd
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
open GlobalTheory GlobalTheory.NonGenericLocalCheck
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E}
variable (M) (m : ℕ)
namespace GlobalTheory.NonGenericLocalCheck
theorem _root_.solution : IsTermOver (pair M m) (datum M m) (term M m) := by
  refine ⟨rfl, rfl, ⟨1, Subgroup.one_mem _, rfl, ?_⟩, ⟨1, Subgroup.one_mem _, rfl, ?_⟩,
    fun g hg => ⟨?_, ?_⟩⟩
  · rw [img_one]
    exact (lamStd M m 0).symm
  · rw [img_one]
    exact (lamStd M m (theta M)).symm
  · intro b
    change vec m (theta M) - vec m (0 : F) ∈ (stdH M m).smulLat (algebraMap F E (g.q : F))
      (Submodule.span M.L.O {v | ∀ i, v i ∈ M.L.O})
    have hv : vec (E := E) m (theta M) - vec m (0 : F) = algebraMap F E (g.q : F) • Pi.single 1 1 := by
      have h01 : (0 : Fin (m + 2)) ≠ 1 := by simp [Fin.ext_iff]
      rw [theta_some M hg]
      funext j
      by_cases h0 : j = 0 <;> by_cases h1 : j = 1 <;> simp [vec, Pi.single_apply, h0, h1, h01, h01.symm]
    rw [hv]
    apply Submodule.subset_span
    refine ⟨Pi.single 1 1, Submodule.subset_span fun j => ?_, rfl⟩
    rw [Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  · ext p
    simp only [datum, Set.mem_setOf_eq]
    constructor
    · intro hp
      exact ⟨g, hg, hp⟩
    · rintro ⟨g', hg', hp⟩
      rw [hg] at hg'
      cases Option.some.inj hg'
      exact hp
end GlobalTheory.NonGenericLocalCheck
