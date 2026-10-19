-- Prove2me | solution 1 for OAI.ArnoldCounterexample.Descent.critical_level_cover
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:07:18.601397+00:00
-- url     : https://prove2.me/submissions/3f07073a-245c-403f-8b31-3f9dc83c67eb

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Descent.lean:L168-L244
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.Descent.critical_level_cover. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates
import Definitions.Def_OAI_Geometry_Arnold_Extension
import Theorems.Thm_OAI_ArnoldCounterexample_Descent_thicken_sublevel
import Theorems.Thm_OAI_ArnoldCounterexample_Descent_uniform_drop

-- ---- from OAI.Geometry.Arnold.Descent ----
namespace OAI

universe uE uX

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology

open Set
open scoped ContDiff

namespace ArnoldCounterexample.Descent

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

end ArnoldCounterexample.Descent

open Set Function

namespace ArnoldCounterexample.Descent

variable {X : Type uX} [TopologicalSpace X] [CompactSpace X]

/-- The finite critical-value LS cover, expressed without manifold jargon.
Every cover member is the inverse image of the same nonvanishing-coordinate
chart under an iterate of a single strict Lyapunov descent. -/
theorem critical_level_cover {D : X → X} {f : X → ℝ} {ℓ : X → ℂ}
    (hD : Continuous D) (hf : Continuous f) (hℓ : Continuous ℓ)
    (hdec : ∀ x, f (D x) ≤ f x)
    (hchart : ∀ x, ℓ x = 0 → f (D x) < f x)
    (s : Finset ℝ) (a : ℝ)
    (hstationary : ∀ x, f x ≤ a → f (D x) = f x → f x ∈ s) :
    ∃ T : Finset ℕ, T.card ≤ s.card ∧
      ∀ x, f x ≤ a → ∃ n ∈ T, ℓ (D^[n] x) ≠ 0 := by
  classical
  induction s using Finset.strongInductionOn generalizing a with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · let c := s.max' hs
      have hc : c ∈ s := Finset.max'_mem s hs
      have herase : s.erase c ⊂ s := Finset.erase_ssubset hc
      by_cases hca : c ≤ a
      · let K : Set X := {x | f x ≤ c ∧ ℓ x = 0}
        have hK : IsCompact K := ((isClosed_le hf continuous_const).inter
          (isClosed_eq hℓ continuous_const)).isCompact
        have hd : ∃ d : ℝ, d < c ∧ ∀ x ∈ K, f (D x) ≤ d := by
          by_cases hne : K.Nonempty
          · obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne (hf.comp hD).continuousOn
            exact ⟨f (D z), (hchart z hz.2).trans_le hz.1, fun x hx ↦ hmax hx⟩
          · exact ⟨c - 1, by linarith, fun x hx ↦ False.elim (hne ⟨x, hx⟩)⟩
        obtain ⟨d, hdc, hd⟩ := hd
        let b := (d + c) / 2
        have hdb : d < b := by dsimp [b]; linarith
        have hbc : b < c := by dsimp [b]; linarith
        obtain ⟨T, hTcard, hT⟩ := ih (s.erase c) herase b (by
          intro x hx heq
          refine Finset.mem_erase.mpr ⟨?_, hstationary x (hx.trans (hbc.le.trans hca)) heq⟩
          exact ne_of_lt (hx.trans_lt hbc))
        obtain ⟨ε, hε, hdrop⟩ := thicken_sublevel hf (hf.comp hD) hℓ c b (by
          intro x hx hz
          exact (hd x ⟨hx, hz⟩).trans_lt hdb)
        obtain ⟨N, hN⟩ := uniform_drop hD hf hdec (c + ε) a (by
          intro x hx hxa
          refine lt_of_le_of_ne (hdec x) ?_
          intro heq
          have hsx := hstationary x hxa heq
          have hxc : f x ≤ c := Finset.le_max' s (f x) hsx
          linarith)
        let T' := insert 0 (T.image Nat.succ)
        refine ⟨T'.image (fun n ↦ n + N), ?_, ?_⟩
        · calc
            (T'.image (fun n ↦ n + N)).card ≤ T'.card := Finset.card_image_le
            _ ≤ T.card + 1 := by
              exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_image_le 1)
            _ ≤ s.card := by
              have herasecard := Finset.card_erase_add_one hc
              omega
        · intro x hx
          have hy : f (D^[N] x) < c + ε := hN x hx
          by_cases hzero : ℓ (D^[N] x) = 0
          · have hb : f (D (D^[N] x)) < b := hdrop _ hy.le hzero
            obtain ⟨n, hn, hnonzero⟩ := hT _ hb.le
            refine ⟨n.succ + N, Finset.mem_image.mpr ⟨n.succ, ?_, rfl⟩, ?_⟩
            · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨n, hn, rfl⟩)
            · simpa only [Function.iterate_add_apply, Function.iterate_succ_apply] using hnonzero
          · exact ⟨0 + N, Finset.mem_image.mpr ⟨0, Finset.mem_insert_self _ _, rfl⟩,
              by simpa using hzero⟩
      · have hac : a < c := lt_of_not_ge hca
        obtain ⟨T, hTcard, hT⟩ := ih (s.erase c) herase a (by
          intro x hx heq
          exact Finset.mem_erase.mpr ⟨ne_of_lt (hx.trans_lt hac), hstationary x hx heq⟩)
        exact ⟨T, hTcard.trans (Finset.card_le_card (Finset.erase_subset _ _)), hT⟩
    · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      refine ⟨∅, by simp, fun x hx ↦ ?_⟩
      have hK : IsCompact {x | f x ≤ a} := (isClosed_le hf continuous_const).isCompact
      obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn ⟨x, hx⟩ hf.continuousOn
      have hDz : f (D z) ≤ a := (hdec z).trans hz
      have heq : f (D z) = f z := le_antisymm (hdec z) (hmin hDz)
      have hm := hstationary z hz heq
      simp [hempty] at hm

end ArnoldCounterexample.Descent

end

end OAI

-- ---- platform node ----
open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.Descent
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Set
open scoped ContDiff
open Set Function


theorem solution.{uX} : type_of% @_root_.OAI.ArnoldCounterexample.Descent.critical_level_cover.{uX} := @_root_.OAI.ArnoldCounterexample.Descent.critical_level_cover.{uX}
