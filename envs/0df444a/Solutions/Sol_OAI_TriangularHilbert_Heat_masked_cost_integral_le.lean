-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.masked_cost_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:50:46.212561+00:00
-- url     : https://prove2.me/submissions/511e583b-0fe0-496d-b142-ec1572602257

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/MaskedActual.lean:L52-L78
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.masked_cost_integral_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteLineMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_JumpScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_Switch
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SortedWindows
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedActual
import Theorems.Thm_OAI_TriangularHilbert_Heat_finite_masked_dissipation
import Theorems.Thm_OAI_TriangularHilbert_Heat_planeTime_intervalIntegrable
import Theorems.Thm_OAI_TriangularHilbert_sum_windowMask_variation

-- ---- from OAI.Analysis.TriangularHilbert.PlaneDissipation ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma strictRate_pos (i w : Three) : 0 < strictRate i w := by
  unfold strictRate; split_ifs <;> norm_num

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.Switch ----
namespace OAI

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

lemma windowMask_norm_le (a b s : ℝ) (A : ℂ) : ‖windowMask a b s A‖ ≤ ‖A‖ := by
  unfold windowMask
  split_ifs <;> simp

end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.SortedWindows ----
namespace OAI

section
namespace TriangularHilbert
open MeasureTheory
open scoped BigOperators
noncomputable section

lemma sortedTimes_monotone (S : Finset ℝ) (hS : S.Nonempty) : Monotone (sortedTimes S hS) := by
  intro k l hkl
  apply (S.orderEmbOfFin rfl).monotone
  exact min_le_min_right _ hkl

lemma sortedTimes_mem (S : Finset ℝ) (hS : S.Nonempty) (k : ℕ) : sortedTimes S hS k ∈ S :=
  Finset.orderEmbOfFin_mem _ _ _

lemma sortedTimes_zero (S : Finset ℝ) (hS : S.Nonempty) : sortedTimes S hS 0 = S.min' hS := by
  exact Finset.orderEmbOfFin_zero rfl (Finset.card_pos.mpr hS)

lemma sortedTimes_last (S : Finset ℝ) (hS : S.Nonempty) : sortedTimes S hS (S.card-1) = S.max' hS := by
  simp only [sortedTimes,min_self]
  exact Finset.orderEmbOfFin_last rfl (Finset.card_pos.mpr hS)

lemma sortedTimes_no_between (S : Finset ℝ) (hS : S.Nonempty) (k : ℕ) {e : ℝ}
    (he : e ∈ S) : ¬ (sortedTimes S hS k < e ∧ e < sortedTimes S hS (k+1)) := by
  have he' : e ∈ Set.range (S.orderEmbOfFin rfl) := by simpa using he
  obtain ⟨j,rfl⟩ := he'
  intro ⟨h1,h2⟩
  have h1' := (S.orderEmbOfFin rfl).lt_iff_lt.mp h1
  have h2' := (S.orderEmbOfFin rfl).lt_iff_lt.mp h2
  change min k (S.card-1) < j.val at h1'
  change j.val < min (k+1) (S.card-1) at h2'
  omega

lemma sortedTimes_le_iff (S : Finset ℝ) (hS : S.Nonempty) (k : ℕ) {e s : ℝ}
    (he : e ∈ S) (hs : s ∈ Set.Ico (sortedTimes S hS k) (sortedTimes S hS (k+1))) :
    e ≤ s ↔ e ≤ sortedTimes S hS k := by
  constructor
  · intro hes
    by_contra h
    exact sortedTimes_no_between S hS k he ⟨lt_of_not_ge h,hes.trans_lt hs.2⟩
  · exact fun h => h.trans hs.1

lemma sortedTimes_mask_const (S : Finset ℝ) (hS : S.Nonempty) (k : ℕ) {a b s : ℝ}
    (ha : a ∈ S) (hb : b ∈ S)
    (hs : s ∈ Set.Ico (sortedTimes S hS k) (sortedTimes S hS (k+1))) (A : ℂ) :
    windowMask a b s A = windowMask a b (sortedTimes S hS k) A := by
  have h1 := sortedTimes_le_iff S hS k ha hs
  have h2 := not_congr (sortedTimes_le_iff S hS k hb hs)
  simp only [not_le] at h2
  simp only [windowMask,h1,h2]

lemma intervalIntegrable_of_Ico_eq {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (he : ∀ s ∈ Set.Ico a b, f s=g s) :
    IntervalIntegrable f volume a b := by
  apply hg.congr_ae
  rw [Set.uIoc_of_le hab]
  apply (ae_restrict_iff' measurableSet_Ioc).2
  filter_upwards [volume.ae_ne b] with s hsb hs
  exact (he s ⟨hs.1.le,lt_of_le_of_ne hs.2 hsb⟩).symm

end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.MaskedActual ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma maskedArray_const (A : Three → Matrix ι ι ℂ) (a b : Matrix ι ι ℝ)
    (S : Finset ℝ) (hS : S.Nonempty) (ha : ∀ i j, a i j ∈ S) (hb : ∀ i j, b i j ∈ S)
    (k : ℕ) {s : ℝ} (hs : s ∈ Set.Ico (sortedTimes S hS k) (sortedTimes S hS (k+1))) :
    maskedArray A a b s = maskedArray A a b (sortedTimes S hS k) := by
  unfold maskedArray
  congr 1
  funext i j
  exact sortedTimes_mask_const S hS k (ha i j) (hb i j) hs _

lemma planeSumCost_intervalIntegrable (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) (r : Three) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun s => ∑ v, planeIntegral (fun p => heatCost A h u p (fun z => strictRate r z*s) v v) d) volume a b := by
  have hi : IntervalIntegrable (∑ v : Three, fun s => planeIntegral (fun p => heatCost A h u p (fun z => strictRate r z*s) v v) d) volume a b :=
    IntervalIntegrable.sum Finset.univ (fun v _ => (planeTime_intervalIntegrable A hh u d (strictRate r) (strictRate_pos r) ha hab).2 v v)
  convert hi using 1
  ext s
  simp

lemma maskedCost_interval_piece (A : Three → Matrix ι ι ℂ) (a b : Matrix ι ι ℝ)
    (S : Finset ℝ) (hS : S.Nonempty) (ha : ∀ i j, a i j ∈ S) (hb : ∀ i j, b i j ∈ S)
    {h : ℝ} (hh : 0 < h) (u : ι → ℝ) (ht0 : 0 < sortedTimes S hS 0) (r : Three) (k : ℕ) :
    IntervalIntegrable (maskedCost A a b h u r) volume (sortedTimes S hS k) (sortedTimes S hS (k+1)) := by
  have ht := sortedTimes_monotone S hS
  apply intervalIntegrable_of_Ico_eq (ht (Nat.le_succ k))
    (planeSumCost_intervalIntegrable (maskedArray A a b (sortedTimes S hS k)) hh u 0 r
      (ht0.trans_le (ht (Nat.zero_le k))) (ht (Nat.le_succ k)))
  intro s hs
  unfold maskedCost
  rw [maskedArray_const A a b S hS ha hb k hs]

lemma masked_cost_integral_le (D : Finset ℤ) (A : Three → Matrix D D ℂ) (a b : Matrix D D ℝ)
    (hab : ∀ i j, a i j ≤ b i j) (S : Finset ℝ) (hS : S.Nonempty)
    (ha : ∀ i j, a i j ∈ S) (hb : ∀ i j, b i j ∈ S)
    {h : ℝ} (hh : 0 < h) (hl : ∀ s ∈ S, h^2 ≤ s) (r : Three) :
    strictConstant*(∫ s in S.min' hS..S.max' hS, maskedCost A a b h (fun m => h*(m:ℤ)) r s) ≤
      maskedConstant*arrayCubic A h := by
  let t := sortedTimes S hS
  have ht : Monotone t := sortedTimes_monotone S hS
  have ht0 : h^2 ≤ t 0 := hl _ (sortedTimes_mem S hS 0)
  let B : ℕ → Matrix D D ℂ := fun k i j => windowMask (a i j) (b i j) (t k) (A 0 i j)
  have hB (k : ℕ) (i j : D) : ‖B k i j‖ ≤ ‖A 0 i j‖ := windowMask_norm_le _ _ _ _
  have hv (i j : D) : (∑ k ∈ Finset.range (S.card-1), ‖B (k+1) i j-B k i j‖) ≤ 2*‖A 0 i j‖ :=
    sum_windowMask_variation t ht _ _ (hab i j) _ _
  have hin := finite_masked_dissipation D A B hB (S.card-1) hv hh t ht ht0 r
  have he (k : ℕ) : (∫ s in t k..t (k+1), ∑ v, planeIntegral (fun p => heatCost (replaceZero A (B k)) h
      (fun m => h*(m:ℤ)) p (fun z => strictRate r z*s) v v) 0) =
      ∫ s in t k..t (k+1), maskedCost A a b h (fun m => h*(m:ℤ)) r s := by
    apply intervalIntegral.integral_congr_Ioo_of_le (ht (Nat.le_succ k))
    intro s hs
    unfold maskedCost
    rw [maskedArray_const A a b S hS ha hb k ⟨hs.1.le,hs.2⟩]
    rfl
  simp_rw [he] at hin
  rw [intervalIntegral.sum_integral_adjacent_intervals] at hin
  · simpa only [t,sortedTimes_zero,sortedTimes_last] using hin
  · intro k _
    exact maskedCost_interval_piece A a b S hS ha hb hh _ ((sq_pos_of_pos hh).trans_le ht0) r k
end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TriangularHilbert.Heat.masked_cost_integral_le := @_root_.OAI.TriangularHilbert.Heat.masked_cost_integral_le
