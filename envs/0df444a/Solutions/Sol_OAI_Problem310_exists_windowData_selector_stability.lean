-- Prove2me | solution 1 for OAI.Problem310.exists_windowData_selector_stability
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:28:12.062569+00:00
-- url     : https://prove2.me/submissions/f161944d-10e5-4324-b628-29e46ede2cfb

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/WindowDataStability.lean:L12-L43
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.exists_windowData_selector_stability. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RandomSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefaultSelection
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteLocalPredicate
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowData
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_StableRoutingBridge
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowExceptionalTransfer
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteWindowAtom
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicEnvelope
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GlobalFromPeriodic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridGeometry
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridMeasure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridStability
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowPlacement
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowRecursion
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PackedWindowSpan
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TreePreorder
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TreePreorderRank
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PreorderIndex
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowSpanSum
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TreeSpanBridge
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowDataExistence
import Theorems.Thm_OAI_Problem310_dyadicGridKey_eq_of_stable
import Theorems.Thm_OAI_Problem310_exists_dyadic_gap_budget
import Theorems.Thm_OAI_Problem310_gridBadCenters_add_one
import Theorems.Thm_OAI_Problem310_volume_iUnion_gridBadCenters_period_le

-- ---- from OAI.MeasureTheory.DyadicAvoidance.GridGeometry ----
namespace OAI

noncomputable section
namespace Problem310

/-- Fine dyadic grid labels determine all coarser labels by integer division. -/
theorem dyadicGridKey_nested {b B : ℕ} (hb : b ≤ B) (x : ℝ) :
    dyadicGridKey B x / (2 : ℤ) ^ (B - b) = dyadicGridKey b x := by
  have hp : (2 : ℝ) ^ (B + 2) = ((2 : ℕ) ^ (B - b) : ℝ) * (2 : ℝ) ^ (b + 2) := by
    push_cast
    rw [← pow_add]
    congr 1
    omega
  unfold dyadicGridKey periodicGridKey
  rw [hp, mul_assoc]
  have h := Int.natCast_mul_floor_div_cancel (R := ℝ)
    (n := (2 : ℕ) ^ (B - b)) (by positivity) ((2 : ℝ) ^ (b + 2) * Int.fract x)
  simpa using h

end Problem310

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.GridMeasure ----
namespace OAI

universe u_ι

noncomputable section
namespace Problem310
open MeasureTheory Set

theorem mem_gridBadCenters_iff (q : ℕ) (δ x : ℝ) :
    x ∈ gridBadCenters q δ ↔ ∃ k : ℤ, (k : ℝ) / q ∈ Ioc x (x + δ) := by
  simp only [gridBadCenters, mem_iUnion, mem_Ico, mem_Ioc]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith [hk.1], by linarith [hk.2]⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith [hk.2], by linarith [hk.1]⟩

theorem measurableSet_gridBadCenters (q : ℕ) (δ : ℝ) :
    MeasurableSet (gridBadCenters q δ) := by
  apply MeasurableSet.iUnion
  intro k
  exact measurableSet_Ico

end Problem310

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.GridStability ----
namespace OAI

universe u_ι

noncomputable section
namespace Problem310
open MeasureTheory Set

theorem measurableSet_gridStableCenters {ι : Type u_ι} [Countable ι] (a b : ι → ℕ) :
    MeasurableSet (gridStableCenters a b) := by
  apply MeasurableSet.compl
  apply MeasurableSet.iUnion
  intro i
  exact measurableSet_gridBadCenters _ _

theorem gridStableCenters_add_one {ι : Type u_ι} (a b : ι → ℕ) (x : ℝ) :
    x + 1 ∈ gridStableCenters a b ↔ x ∈ gridStableCenters a b := by
  simp only [gridStableCenters, mem_compl_iff, mem_iUnion, not_exists]
  apply forall_congr'
  intro i
  exact not_congr (gridBadCenters_add_one _ (by positivity) _ _)

/-- Stability at a grid also preserves every coarser grid at a later-window trial. -/
theorem gridStableCenters_preserves {ι : Type u_ι} {a b : ι → ℕ} {x t : ℝ}
    (hx : x ∈ gridStableCenters a b) (i : ι) {c n : ℕ}
    (hc : c ≤ b i) (hn : a i ≤ n) (ht : t ∈ Icc (1 : ℝ) 2) :
    dyadicGridKey c (x + t * ((2 : ℝ)⁻¹) ^ n) = dyadicGridKey c x := by
  have hxnot : x ∉ gridBadCenters ((2 : ℕ) ^ (b i + 2))
      (2 * ((2 : ℝ)⁻¹) ^ (a i)) := by
    intro hi
    exact hx (mem_iUnion.mpr ⟨i, hi⟩)
  have hkey := dyadicGridKey_eq_of_stable hn ht (fun k hk ↦ by
    apply hxnot
    apply (mem_gridBadCenters_iff _ _ _).mpr
    exact ⟨k, by simpa using hk⟩)
  rw [← dyadicGridKey_nested hc, ← dyadicGridKey_nested hc, hkey]

private theorem grid_window_width_le {a b : ℕ} (hgap : b + 3 ≤ a) :
    2 * ((2 : ℝ)⁻¹) ^ a ≤ (((2 : ℕ) ^ (b + 2) : ℕ) : ℝ)⁻¹ := by
  have h := pow_right_anti₀ (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    (by norm_num : (2 : ℝ)⁻¹ ≤ 1) hgap
  change (2 : ℝ)⁻¹ ^ a ≤ (2 : ℝ)⁻¹ ^ (b + 3) at h
  have hp : ((2 : ℝ)⁻¹) ^ (b + 3) = ((2 : ℝ)⁻¹) ^ (b + 2) * 2⁻¹ := by
    rw [show b + 3 = (b + 2) + 1 by omega, pow_succ]
  rw [hp] at h
  have h2 : 2 * ((2 : ℝ)⁻¹) ^ a ≤ ((2 : ℝ)⁻¹) ^ (b + 2) := by
    norm_num at h ⊢
    linarith
  simpa only [Nat.cast_pow, Nat.cast_ofNat, inv_pow] using h2

/-- A quantitative simultaneous stability estimate, with no tree assumptions. -/
theorem volume_gridStableCenters_compl_period_le {ι : Type u_ι} [Fintype ι]
    (a b : ι → ℕ) (hgap : ∀ i, b i + 3 ≤ a i) :
    volume ((gridStableCenters a b)ᶜ ∩ Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (∑ i, (2 : ℝ) ^ (b i + 2) * (2 * ((2 : ℝ)⁻¹) ^ (a i))) := by
  simp only [gridStableCenters, compl_compl]
  simpa using volume_iUnion_gridBadCenters_period_le
    (fun i ↦ (2 : ℕ) ^ (b i + 2)) (fun i ↦ 2 * ((2 : ℝ)⁻¹) ^ (a i))
    (fun i ↦ by positivity) (fun i ↦ by positivity)
    (fun i ↦ grid_window_width_le (hgap i))

/-- The density cost of a gap depends only on its length, not on the grid resolution. -/
theorem dyadic_grid_gap_budget (b g : ℕ) :
    (2 : ℝ) ^ (b + 2) * (2 * ((2 : ℝ)⁻¹) ^ (b + g + 1)) =
      4 * ((2 : ℝ)⁻¹) ^ g := by
  have hcancel : (2 : ℝ) ^ b * ((2 : ℝ)⁻¹) ^ b = 1 := by
    rw [inv_pow]
    exact mul_inv_cancel₀ (by positivity)
  calc
    (2 : ℝ) ^ (b + 2) * (2 * ((2 : ℝ)⁻¹) ^ (b + g + 1))
      = 4 * ((2 : ℝ) ^ b * ((2 : ℝ)⁻¹) ^ b) * ((2 : ℝ)⁻¹) ^ g := by
        simp only [pow_add, pow_one]
        norm_num
        ring
    _ = 4 * ((2 : ℝ)⁻¹) ^ g := by rw [hcancel]; ring

theorem volume_gridStableCenters_compl_gap_le {ι : Type u_ι} [Fintype ι]
    (a b : ι → ℕ) (g : ℕ) (hg : 2 ≤ g)
    (ha : ∀ i, a i = b i + g + 1) :
    volume ((gridStableCenters a b)ᶜ ∩ Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) * (4 * ((2 : ℝ)⁻¹) ^ g)) := by
  have h := volume_gridStableCenters_compl_period_le a b (fun i ↦ by rw [ha i]; omega)
  have heq : (∑ i, (2 : ℝ) ^ (b i + 2) * (2 * ((2 : ℝ)⁻¹) ^ (a i))) =
      (Fintype.card ι : ℝ) * (4 * ((2 : ℝ)⁻¹) ^ g) := by
    simp only [ha, dyadic_grid_gap_budget, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rwa [heq] at h

end Problem310

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.GridStabilityFin ----
namespace OAI

universe u_ι

noncomputable section
namespace Problem310

/-- Bridge from quantitative stability to the canonical finite selector addresses. -/
theorem gridStableCenters_preserves_fin {ι : Type u_ι} {a b : ι → ℕ} {x t : ℝ}
    (hx : x ∈ gridStableCenters a b) (i : ι) {c n : ℕ}
    (hc : c ≤ b i) (hn : a i ≤ n) (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    GridSeparation.dyadicKey c (x + t * ((2 : ℝ)⁻¹) ^ n) =
      GridSeparation.dyadicKey c x := by
  apply (GridSeparation.dyadicKey_eq_iff c _ _).mpr
  exact gridStableCenters_preserves hx i hc hn ht

/-- Choose the gap using only the finite number of grids, before their resolutions
are assigned. Every subsequent assignment has a periodic measurable stable set
with the same prescribed exceptional-density budget. -/
theorem exists_uniform_grid_stability {ι : Type u_ι} [Fintype ι]
    (p : ℝ) (hp : 0 < p) :
    ∃ g : ℕ, 2 ≤ g ∧ ∀ b : ι → ℕ, ∃ G : Set ℝ,
      MeasurableSet G ∧ (∀ x : ℝ, x + 1 ∈ G ↔ x ∈ G) ∧
      MeasureTheory.volume (Gᶜ ∩ Set.Icc (0 : ℝ) 1) ≤ ENNReal.ofReal p ∧
      ∀ x ∈ G, ∀ i : ι, ∀ n : ℕ, b i + g + 1 ≤ n →
        ∀ t ∈ Set.Icc (1 : ℝ) 2,
          GridSeparation.dyadicKey (b i) (x + t * ((2 : ℝ)⁻¹) ^ n) =
            GridSeparation.dyadicKey (b i) x := by
  obtain ⟨g, hg, hbudget⟩ := exists_dyadic_gap_budget (Fintype.card ι) hp
  refine ⟨g, hg, fun b ↦ ?_⟩
  let a : ι → ℕ := fun i ↦ b i + g + 1
  refine ⟨gridStableCenters a b, measurableSet_gridStableCenters a b,
    gridStableCenters_add_one a b, ?_, ?_⟩
  · exact (volume_gridStableCenters_compl_gap_le a b g hg (fun i ↦ rfl)).trans
      (ENNReal.ofReal_le_ofReal hbudget.le)
  · intro x hx i n hn t ht
    exact gridStableCenters_preserves_fin hx i le_rfl hn ht

end Problem310

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.WindowDataStability ----
namespace OAI

noncomputable section
namespace Problem310

open FiniteTableModel

/-- Actual selector stability for arbitrary canonical window data. The gap is
chosen before the window recursion and all its resolutions. Prefix and sibling
gap fields of `W` may be applied directly to the displayed strict cutoff. -/
theorem exists_windowData_selector_stability (M d : ℕ) (p : ℝ) (hp : 0 < p) :
    ∃ g : ℕ, 2 ≤ g ∧ ∀ r₀ : ℕ, ∀ W : WindowData (M + 1) d g r₀,
      ∃ G : Set ℝ, MeasurableSet G ∧
        (∀ x : ℝ, x + 1 ∈ G ↔ x ∈ G) ∧
        MeasureTheory.volume (Gᶜ ∩ Set.Icc (0 : ℝ) 1) ≤ ENNReal.ofReal p ∧
        ∀ x ∈ G, ∀ P : Node M d, ∀ i : Fin M, ∀ n : ℕ,
          W.b (P.val ++ [i.castSucc]) + g < n →
          ∀ t ∈ Set.Icc (1 : ℝ) 2,
          ∀ ω : SelectorTable (fun P : Node M d => fun i : Fin M =>
            W.b (P.val ++ [i.castSucc])),
          selectorValue (fun P : Node M d => fun i : Fin M =>
            W.b (P.val ++ [i.castSucc])) ω P.val i (x + t * ((2 : ℝ)⁻¹) ^ n) =
          selectorValue (fun P : Node M d => fun i : Fin M =>
            W.b (P.val ++ [i.castSucc])) ω P.val i x := by
  obtain ⟨g, hg, hgeometry⟩ :=
    exists_uniform_grid_stability (ι := Node M d × Fin M) p hp
  refine ⟨g, hg, fun r₀ W ↦ ?_⟩
  let bS : Node M d → Fin M → ℕ := fun P i => W.b (P.val ++ [i.castSucc])
  obtain ⟨G, hGm, hGp, hGbudget, hGkey⟩ := hgeometry (fun e => bS e.1 e.2)
  refine ⟨G, hGm, hGp, hGbudget, ?_⟩
  intro x hx P i n hn t ht ω
  have hk := hGkey x hx (P, i) n (by dsimp [bS]; omega) t ht
  have ha : selectorAddress bS P i (x + t * ((2 : ℝ)⁻¹) ^ n) =
      selectorAddress bS P i x := by
    unfold selectorAddress
    rw [hk]
  change selectorValue bS ω P.val i (x + t * ((2 : ℝ)⁻¹) ^ n) =
    selectorValue bS ω P.val i x
  rw [selectorValue_valid, selectorValue_valid, ha]

end Problem310

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310
open FiniteTableModel


theorem solution : type_of% @_root_.OAI.Problem310.exists_windowData_selector_stability := @_root_.OAI.Problem310.exists_windowData_selector_stability
