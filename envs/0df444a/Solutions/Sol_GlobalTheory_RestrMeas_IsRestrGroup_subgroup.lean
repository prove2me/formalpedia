-- Prove2me | solution 1 for GlobalTheory.RestrMeas.IsRestrGroup.subgroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:54.666831+00:00
-- url     : https://prove2.me/submissions/985d9883-0f93-423e-b27f-37ccc6a05478

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ExistsFinsetOfEventually
import Theorems.Thm_GlobalTheory_RestrMeas_exists_extend_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RestrMeas
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal NNReal
variable {X W V : Type} {Ya : W → Type} {Yf : V → Type} [Group X] [∀ w, Group (Ya w)] [∀ v, Group (Yf v)]
  [TopologicalSpace X] [∀ w, TopologicalSpace (Ya w)] [∀ v, TopologicalSpace (Yf v)]
variable {pa : ∀ w, X →* Ya w} {pf : ∀ v, X →* Yf v} {K K' : ∀ v, Subgroup (Yf v)}
namespace GlobalTheory.RestrMeas
namespace IsRestrGroup
theorem _root_.solution [∀ w, T1Space (Ya w)] [∀ v, T1Space (Yf v)] (h : IsRestrGroup pa pf K)
    {W' V' : Type} {i : W' → W} {j : V' → V} (hi : Function.Injective i) (hj : Function.Injective j)
    (H : Subgroup X) (hH : ∀ x, x ∈ H ↔ (∀ w ∉ range i, pa w x = 1) ∧ ∀ v ∉ range j, pf v x = 1) :
    IsRestrGroup (fun w => (pa (i w)).comp H.subtype) (fun v => (pf (j v)).comp H.subtype) fun v => K (j v) := by
  have hl : ∀ x : H, (∀ v, pf (j v) x ∈ K (j v)) ↔ ∀ v, pf v x ∈ K v := fun x => ⟨fun hx v => by
    by_cases hv : v ∈ range j
    · obtain ⟨u, rfl⟩ := hv; exact hx u
    · rw [((hH x).1 x.2).2 v hv]; exact one_mem _, fun hx v => hx _⟩
  refine ⟨fun w => (h.continuous_pa _).comp continuous_subtype_val,
    fun v => (h.continuous_pf _).comp continuous_subtype_val, fun v => h.isOpen_K _, fun v => h.isCompact_K _,
    fun x y ha hf => Subtype.ext (h.ext _ _ (fun w => ?_) fun v => ?_),
    fun x => hj.tendsto_cofinite.eventually (h.eventually_mem x), fun a y hy => ?_, ?_, fun C hC => ?_⟩
  · by_cases hw : w ∈ range i
    · obtain ⟨u, rfl⟩ := hw; exact ha u
    · rw [((hH x).1 x.2).1 w hw, ((hH y).1 y.2).1 w hw]
  · by_cases hv : v ∈ range j
    · obtain ⟨u, rfl⟩ := hv; exact hf u
    · rw [((hH x).1 x.2).2 v hv, ((hH y).1 y.2).2 v hv]
  · obtain ⟨a', ha1, ha2⟩ := exists_extend_one hi a
    obtain ⟨y', hy1, hy2⟩ := exists_extend_one hj y
    obtain ⟨x, hx1, hx2⟩ := h.exists_eq a' y' (((eventually_cofinite.1 hy).image j).subset fun v hv => by
      by_cases hr : v ∈ range j
      · obtain ⟨u, rfl⟩ := hr
        exact ⟨u, fun hu => hv (show y' (j u) ∈ K (j u) by rw [hy1]; exact hu), rfl⟩
      · exact absurd (show y' v ∈ K v by rw [hy2 v hr]; exact one_mem _) hv)
    exact ⟨⟨x, (hH x).2 ⟨fun w hw => (hx1 w).trans (ha2 w hw), fun v hv => (hx2 v).trans (hy2 v hv)⟩⟩,
      fun w => (hx1 _).trans (ha1 w), fun v => (hx2 _).trans (hy1 v)⟩
  · convert h.isOpen_level.preimage (continuous_subtype_val (p := (· ∈ H))) using 1
    exact Set.ext hl
  · have hc : IsClosed (H : Set X) := by
      have : (H : Set X) = (⋂ w ∉ range i, pa w ⁻¹' {1}) ∩ ⋂ v ∉ range j, pf v ⁻¹' {1} :=
        Set.ext fun x => by simpa using hH x
      rw [this]
      exact (isClosed_biInter fun w _ => isClosed_singleton.preimage (h.continuous_pa w)).inter
        (isClosed_biInter fun v _ => isClosed_singleton.preimage (h.continuous_pf v))
    have : ∀ w, ∃ D : Set (Ya w), IsCompact D ∧ (∀ u (e : i u = w), D = e ▸ C u) ∧ (w ∉ range i → D = {1}) :=
      fun w => by
        by_cases hw : w ∈ range i
        · obtain ⟨u, rfl⟩ := hw
          exact ⟨C u, hC u, fun v' e => by obtain rfl := hi e; rfl, fun h => absurd ⟨u, rfl⟩ h⟩
        · exact ⟨{1}, isCompact_singleton, fun v' e => absurd ⟨v', e⟩ hw, fun _ => rfl⟩
    choose D hD h1 h2 using this
    refine (congrArg IsCompact (Set.ext fun x => ?_)).mpr
      (hc.isClosedEmbedding_subtypeVal.isCompact_preimage (h.isCompact_level D hD))
    refine and_congr (Iff.intro (fun hx w => ?_) (fun hx u => ?_) :
      (∀ u, pa (i u) x ∈ C u) ↔ ∀ w, pa w x ∈ D w) (hl x)
    · by_cases hw : w ∈ range i
      · obtain ⟨u, rfl⟩ := hw
        rw [h1 _ u rfl]; exact hx u
      · rw [h2 w hw]; exact ((hH x).1 x.2).1 w hw
    · have := hx (i u)
      rwa [h1 _ u rfl] at this
end IsRestrGroup
end GlobalTheory.RestrMeas
