-- Prove2me | solution 1 for OAI.BoxTransport.Routing.globalFlow_of_bounded_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T13:30:46.945581+00:00
-- url     : https://prove2.me/submissions/f43a12ed-14b4-43d0-9297-90cb3c528072

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BoxTransport/Flow.lean:L464-L537
-- (upload_full_project.md Phase 4): solution for node OAI.BoxTransport.Routing.globalFlow_of_bounded_lipschitz. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow

-- ---- from OAI.Analysis.BoxTransport.Flow ----
namespace OAI

/-! Localized solenoidal moving fields and their unique global flows. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

namespace BoxTransport.Routing
theorem globalFlow_of_bounded_lipschitz {U : Field} {M K : NNReal}
    (hcont : Continuous U) (hbound : ∀ p, ‖U p‖ ≤ M)
    (hlip : ∀ t, LipschitzWith K (fun x => U (t, x))) :
    ∃ Φ, IsGlobalFlow U Φ := by
  have localSolution (x : Space) (r : ℝ) (hr : 0 < r) :
      ∃ α : ℝ → Space, α 0 = x ∧
        ∀ t ∈ Set.Ioo (-r) r, HasDerivAt α (U (t, α t)) t := by
    let t₀ : Set.Icc (-r) r := ⟨0, by constructor <;> linarith⟩
    let a : NNReal := M * ⟨r, hr.le⟩
    have hpl : IsPicardLindelof (fun t x => U (t, x)) t₀ x a 0 M K := by
      constructor
      · intro t ht
        exact (hlip t).lipschitzOnWith
      · intro y hy
        exact (hcont.comp (continuous_id.prodMk continuous_const)).continuousOn
      · intro t ht y hy
        exact hbound (t, y)
      · change (M : ℝ) * max (r - 0) (0 - (-r)) ≤ (M : ℝ) * r - 0
        simp
    obtain ⟨α, hα0, hα⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    exact ⟨α, hα0, fun t ht => (hα t ⟨ht.1.le, ht.2.le⟩).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)⟩
  have trajectories (x : Space) :
      ∃ γ : ℝ → Space, γ 0 = x ∧ ∀ t, HasDerivAt γ (U (t, γ t)) t := by
    let Radius := {r : ℝ // 0 < r}
    have hlocal (r : Radius) := localSolution x r.1 r.2
    choose α hα0 hα using hlocal
    have compatibility (r s : Radius) (t : ℝ)
        (htr : t ∈ Set.Ioo (-r.1) r.1) (hts : t ∈ Set.Ioo (-s.1) s.1) :
        α r t = α s t := by
      have hm : 0 < min r.1 s.1 := lt_min r.2 s.2
      have he : Set.EqOn (α r) (α s) (Set.Ioo (-min r.1 s.1) (min r.1 s.1)) := by
        apply ODE_solution_unique_of_mem_Ioo
          (v := fun t x => U (t, x)) (s := fun _ => Set.univ) (K := K)
          (t₀ := 0)
        · intro t ht
          exact (hlip t).lipschitzOnWith
        · exact ⟨neg_neg_of_pos hm, hm⟩
        · intro t ht
          exact ⟨hα r t ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) ht.1,
            lt_of_lt_of_le ht.2 (min_le_left _ _)⟩, Set.mem_univ _⟩
        · intro t ht
          exact ⟨hα s t ⟨lt_of_le_of_lt (neg_le_neg (min_le_right _ _)) ht.1,
            lt_of_lt_of_le ht.2 (min_le_right _ _)⟩, Set.mem_univ _⟩
        · rw [hα0, hα0]
      apply he
      constructor
      · rw [← max_neg_neg]
        exact max_lt htr.1 hts.1
      · exact lt_min htr.2 hts.2
    let ρ : ℝ → Radius := fun t => ⟨|t| + 1, by positivity⟩
    have hin (t : ℝ) : t ∈ Set.Ioo (-(ρ t).1) (ρ t).1 := by
      have hp := le_abs_self t
      have hn := neg_abs_le t
      change -(|t| + 1) < t ∧ t < |t| + 1
      constructor <;> linarith
    let γ : ℝ → Space := fun t => α (ρ t) t
    have heq (r : Radius) (t : ℝ) (ht : t ∈ Set.Ioo (-r.1) r.1) : γ t = α r t :=
      compatibility (ρ t) r t (hin t) ht
    refine ⟨γ, hα0 (ρ 0), ?_⟩
    intro t
    have hev : γ =ᶠ[nhds t] α (ρ t) := by
      filter_upwards [isOpen_Ioo.mem_nhds (hin t)] with s hs
      exact heq (ρ t) s hs
    exact (hα (ρ t) t (hin t)).congr_of_eventuallyEq hev
  choose γ hγ0 hγ using trajectories
  refine ⟨fun t x => γ x t, (fun x => hγ0 x), (fun t x => hγ x t), ?_⟩
  intro x ν hν0 hν t
  have he : ν = γ x := ODE_solution_unique_univ
    (v := fun t x => U (t, x)) (s := fun _ => Set.univ) (K := K) (t₀ := 0)
    (fun t => (hlip t).lipschitzOnWith)
    (fun t => ⟨hν t, Set.mem_univ _⟩)
    (fun t => ⟨hγ x t, Set.mem_univ _⟩) (hν0.trans (hγ0 x).symm)
  exact congrFun he t

end BoxTransport.Routing

end

end OAI

-- ---- platform node ----
open OAI OAI.BoxTransport OAI.BoxTransport.Routing
open scoped Topology
open scoped BigOperators ContDiff


theorem solution : type_of% @_root_.OAI.BoxTransport.Routing.globalFlow_of_bounded_lipschitz := @_root_.OAI.BoxTransport.Routing.globalFlow_of_bounded_lipschitz
