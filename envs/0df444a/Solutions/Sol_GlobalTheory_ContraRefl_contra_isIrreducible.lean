-- Prove2me | solution 1 for GlobalTheory.ContraRefl.contra_isIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:17:06.644925+00:00
-- url     : https://prove2.me/submissions/6b0c44fa-aec9-4afa-b0cf-7e4f6e8f6fa9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_SmoothContragredientIrreducibleAndReflexive
import Theorems.Thm_GlobalTheory_ContraRefl_mem_of_annihilator_eq_bot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.ContraRefl
variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.ContraRefl
theorem _root_.solution
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    {π : Representation ℂ G V} (hπ : IsAdmissible π) (hirr : π.IsIrreducible) :
    (contra π).IsIrreducible := by
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := by
    by_contra h
    push_neg at h
    apply (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)
    apply Subrepresentation.ext
    ext x
    rw [h x]
    exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  obtain ⟨l, hl⟩ := exists_smooth_form_ne hπ.1 hG hv
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => hl ?_⟩, eq_bot_or_eq_top := fun U => ?_ }
  · have : l ∈ (⊥ : Subrepresentation (contra π)).toSubmodule := by
      rw [h]; exact Submodule.mem_top
    rw [(Submodule.mem_bot ℂ).1 this]
    rfl
  · let A : Subrepresentation π :=
      { toSubmodule := ⨅ u ∈ U.toSubmodule, LinearMap.ker (u : Module.Dual ℂ V)
        apply_mem_toSubmodule := fun g v hv => by
          simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hv ⊢
          intro u hu
          have := hv _ (U.apply_mem_toSubmodule g⁻¹ hu)
          rwa [contra_apply, inv_inv] at this }
    have hmemA : ∀ v, v ∈ A.toSubmodule ↔ ∀ u ∈ U.toSubmodule, (u : Module.Dual ℂ V) v = 0 := by
      intro v; simp [A]
    rcases hirr.eq_bot_or_eq_top A with hA | hA
    · right
      apply Subrepresentation.ext
      refine eq_top_iff.2 fun l _ => mem_of_annihilator_eq_bot hG hπ U (fun v hv => ?_) l
      have : v ∈ A.toSubmodule := (hmemA v).2 hv
      rw [hA] at this
      exact (Submodule.mem_bot ℂ).1 this
    · left
      apply Subrepresentation.ext
      refine eq_bot_iff.2 fun u hu => (Submodule.mem_bot ℂ).2 (Subtype.ext (LinearMap.ext fun w => ?_))
      have : w ∈ A.toSubmodule := by rw [hA]; exact Submodule.mem_top
      exact (hmemA w).1 this u hu
end GlobalTheory.ContraRefl
