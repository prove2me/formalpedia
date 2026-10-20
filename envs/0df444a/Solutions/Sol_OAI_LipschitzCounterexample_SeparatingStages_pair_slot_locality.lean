-- Prove2me | solution 1 for OAI.LipschitzCounterexample.SeparatingStages.pair_slot_locality
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:16:51.736819+00:00
-- url     : https://prove2.me/submissions/53737190-f213-475f-9b04-0655e0d29822

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/LocalOrthogonality.lean:L114-L162
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.SeparatingStages.pair_slot_locality. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparatingCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlowAngles
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RotatingStages
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBijection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalOrthogonality
import Theorems.Thm_OAI_LipschitzCounterexample_SeparatingStages_stage_coord_zero
import Theorems.Thm_OAI_LipschitzCounterexample_SeparatingStages_support_disjoint

-- ---- from OAI.Analysis.LipschitzEquivalence.SlotRadii ----
namespace OAI

universe uE

noncomputable section
namespace LipschitzCounterexample

namespace HilbertSlots
open scoped ENNReal NNReal
open Filter Topology
variable {E : ℕ → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]

theorem radius_tendsto (x : SlotDomain E) : Tendsto (fun N => radius N x) atTop (𝓝 0) := by
  have h := ((tendsto_const_nhds (x := radiusSeq x)).sub (prefix_tendsto (radiusSeq x))).norm
  simpa [radius, radiusCLM] using h

end HilbertSlots

end LipschitzCounterexample
end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.SeparatingCoordinates ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uIndex uOtherIndex

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal

namespace LipschitzCounterexample.SeparatingStages

end LipschitzCounterexample.SeparatingStages

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal

theorem scalarCoordinate_separate {x y : M} (h : ∀ j, scalarCoordinate j x = scalarCoordinate j y) : x = y := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply lp.ext
    funext n
    apply PiLp.ext
    intro a
    exact h (.inl ⟨n,a⟩)
  · apply lp.ext
    funext n
    exact h (.inr n)

theorem p_separate {x y : M} (h : ∀ j, p j x = p j y) : x = y := by
  apply scalarCoordinate_separate
  intro a
  obtain ⟨j,rfl⟩ := enumerate.surjective a
  exact Real.tanh_injective (h j)

end LipschitzCounterexample.SeparatingStages

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal

section Embed
variable {ι : Type uIndex} {κ : Type uOtherIndex} [Fintype ι] [Fintype κ]
open Classical

end Embed
end LipschitzCounterexample.SeparatingStages

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal

end LipschitzCounterexample.SeparatingStages

end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.LocalOrthogonality ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe uI

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal InnerProductSpace Topology
open HilbertSlots RadialBudget SlowAngles RotatingStages Filter Set

theorem path_coord_zero (n N : ℕ) (α : ℕ → M → ℝ) (x : M) (a : BlockLabel n)
    (h : ∀ j ≤ N, stage n j x a = 0) : path (stage n) α N x a = 0 := by
  induction N with
  | zero => exact h 0 (le_refl _)
  | succ N ih =>
    change Real.cos (α N x) * path (stage n) α N x a +
      Real.sin (α N x) * stage n (N+1) x a = 0
    rw [ih (fun j hj => h j (by omega)), h (N+1) (le_refl _)]
    ring

theorem path_coord_after_zero (n K N : ℕ) (hKN : K ≤ N) (α : ℕ → M → ℝ)
    (x : M) (a : BlockLabel n) (hK : path (stage n) α K x a = 0)
    (h : ∀ j, K < j → j ≤ N → stage n j x a = 0) : path (stage n) α N x a = 0 := by
  induction N, hKN using Nat.le_induction with
  | base => exact hK
  | succ N hKN ih =>
    change Real.cos (α N x) * path (stage n) α N x a +
      Real.sin (α N x) * stage n (N+1) x a = 0
    rw [ih (fun j hj hj' => h j hj (by omega)), h (N+1) (by omega) (le_refl _)]
    ring

theorem slot_low_coord_zero (n K : ℕ) (hKn : K ≤ n) (x : M)
    (hr : radius n x ≤ lower bounds bounds_nonneg K) (a : BlockLabel n)
    (ha : stageIndex a ≤ K) : slot n x a = 0 := by
  apply path_coord_after_zero n (K+1) (n+1) (by omega)
  · have hp := (path_small_eventually (stage n) bounds bounds_nonneg (radius n)
      (radius_lipschitz n).continuous K x hr).eq_of_nhds
    rw [hp]
    exact stage_coord_zero n (K+1) x a (by omega)
  · intro j hj hj'
    exact stage_coord_zero n j x a (by omega)

theorem slot_stage_coord_zero (n : ℕ) (k : Fin (n+1)) (x : M) (a : Label (k.val+1))
    (ha : normalized (k.val+1) (pVector (k.val+1) x) a = 0) :
    slot n x (.inr ⟨k,a⟩) = 0 := by
  apply path_coord_zero
  intro j hj
  by_cases he : j = k.val+1
  · subst j
    simpa only [stage,dite_eq_left k.isLt,W_on] using ha
  · exact stage_coord_zero n j x (.inr ⟨k,a⟩) he

theorem slot_disjoint_of_separated (n K j : ℕ) (hKn : K ≤ n) (hjK : j < K+1)
    (x y : M) (hx : radius n x ≤ lower bounds bounds_nonneg K)
    (_hy : radius n y ≤ lower bounds bounds_nonneg K)
    (hxy : 2/((K+1 : ℕ) : ℝ) < |p j x-p j y|) (a : BlockLabel n) :
    slot n x a = 0 ∨ slot n y a = 0 := by
  cases a with
  | inl u =>
    left
    exact slot_low_coord_zero n K hKn x hx (.inl u) (Nat.zero_le _)
  | inr a =>
    rcases a with ⟨k,a⟩
    by_cases hk : k.val < K
    · left
      exact slot_low_coord_zero n K hKn x hx (.inr ⟨k,a⟩) (by exact_mod_cast hk)
    have hKk : K ≤ k.val := by omega
    have hjk : j < k.val+1 := by omega
    have hxy' : 2/((k.val+1 : ℕ) : ℝ) < |p j x-p j y| := by
      apply lt_of_le_of_lt _ hxy
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hKk 1)
    rcases support_disjoint (Nat.zero_lt_succ k.val) (s := pVector (k.val+1) x)
      (t := pVector (k.val+1) y) ⟨j,hjk⟩ hxy' a with hx' | hy'
    · exact Or.inl (slot_stage_coord_zero n k x a hx')
    · exact Or.inr (slot_stage_coord_zero n k y a hy')

end LipschitzCounterexample.SeparatingStages

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal InnerProductSpace Topology
open HilbertSlots RadialBudget SlowAngles RotatingStages Filter Set

theorem pair_slot_locality {x y : M} (hxy : x ≠ y) :
    ∃ r : ℝ, 0 < r ∧ ∃ l : ℕ, ∀ n ≥ l, ∀ s ∈ Metric.ball x r,
      ∀ t ∈ Metric.ball y r, ∀ a : BlockLabel n, slot n s a = 0 ∨ slot n t a = 0 := by
  classical
  have hp : ∃ j, p j x ≠ p j y := by
    by_contra h
    push Not at h
    exact hxy (p_separate h)
  obtain ⟨j,hj⟩ := hp
  let δ := |p j x-p j y|
  have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hj)
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt (show 0 < δ/4 by positivity)
  let K := max j k
  have hjK : j < K+1 := by dsimp [K]; omega
  have hscale : 2/((K+1 : ℕ) : ℝ) < δ/2 := by
    have hmono : 1/((K+1 : ℕ) : ℝ) ≤ 1/((k+1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by exact_mod_cast Nat.add_le_add_right (le_max_right j k) 1)
    have hk' : 1/((k+1 : ℕ) : ℝ) < δ/4 := by simpa using hk
    calc
      2/((K+1 : ℕ) : ℝ) = 2*(1/((K+1 : ℕ) : ℝ)) := by ring
      _ < δ/2 := by linarith
  have hlx := (radius_tendsto x).eventually (gt_mem_nhds (lower_pos bounds bounds_nonneg K))
  have hly := (radius_tendsto y).eventually (gt_mem_nhds (lower_pos bounds bounds_nonneg K))
  obtain ⟨l,hlx,hly,hKl⟩ := (hlx.and (hly.and (eventually_ge_atTop K))).exists
  let O : Set M := {s | |p j s-p j x| < δ/4 ∧ radius l s < lower bounds bounds_nonneg K}
  let P : Set M := {t | |p j t-p j y| < δ/4 ∧ radius l t < lower bounds bounds_nonneg K}
  have hO : IsOpen O :=
    (isOpen_lt (((p_contDiff (n := 1) j).continuous.sub continuous_const).abs) continuous_const).inter
      (isOpen_lt (radius_lipschitz l).continuous continuous_const)
  have hP : IsOpen P :=
    (isOpen_lt (((p_contDiff (n := 1) j).continuous.sub continuous_const).abs) continuous_const).inter
      (isOpen_lt (radius_lipschitz l).continuous continuous_const)
  have hxO : x ∈ O := ⟨by simpa using (show 0 < δ/4 by positivity),hlx⟩
  have hyP : y ∈ P := ⟨by simpa using (show 0 < δ/4 by positivity),hly⟩
  obtain ⟨r,hr,hrO⟩ := Metric.isOpen_iff.mp hO x hxO
  obtain ⟨q,hq,hqP⟩ := Metric.isOpen_iff.mp hP y hyP
  refine ⟨min r q,lt_min hr hq,l,?_⟩
  intro n hln s hs t ht a
  have hsO := hrO ((Metric.ball_subset_ball (min_le_left r q)) hs)
  have htP := hqP ((Metric.ball_subset_ball (min_le_right r q)) ht)
  have hsep : δ/2 < |p j s-p j t| := by
    have h₁ := abs_sub_le (p j x) (p j s) (p j y)
    have h₂ := abs_sub_le (p j s) (p j t) (p j y)
    rw [abs_sub_comm (p j x) (p j s)] at h₁
    change δ ≤ _ at h₁
    linarith [hsO.1,htP.1]
  exact slot_disjoint_of_separated n K j (hKl.trans hln) hjK s t
    ((radius_antitone s hln).trans hsO.2.le)
    ((radius_antitone t hln).trans htP.2.le) (hscale.trans hsep) a

end LipschitzCounterexample.SeparatingStages

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal InnerProductSpace Topology
open HilbertSlots RadialBudget SlowAngles RotatingStages Filter Set

end LipschitzCounterexample.SeparatingStages

end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.SeparatingStages
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped ENNReal NNReal InnerProductSpace Topology
open HilbertSlots RadialBudget SlowAngles RotatingStages Filter Set


theorem solution : type_of% @_root_.OAI.LipschitzCounterexample.SeparatingStages.pair_slot_locality := @_root_.OAI.LipschitzCounterexample.SeparatingStages.pair_slot_locality
