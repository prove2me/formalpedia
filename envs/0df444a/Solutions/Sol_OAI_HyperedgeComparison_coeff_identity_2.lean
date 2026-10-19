-- Prove2me | solution 2 for OAI.HyperedgeComparison.coeff_identity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:05:50.874772+00:00
-- url     : https://prove2.me/submissions/158b2cfe-90b0-4d39-b7dd-3a606a256405

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean:L1127-L1142
-- (upload_full_project.md Phase 4): solution for node OAI.HyperedgeComparison.coeff_identity. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Theorems.Thm_OAI_HyperedgeComparison_cluster_delete_clusters
import Theorems.Thm_OAI_HyperedgeComparison_column_conditional_expectation
import Theorems.Thm_OAI_HyperedgeComparison_column_residual
import Theorems.Thm_OAI_HyperedgeComparison_conditioning_weight
import Theorems.Thm_OAI_HyperedgeComparison_exists_unique_firstRoot

-- ---- from OAI.Probability.CriticalZ3.HyperedgeComparison ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
namespace OAI

universe uE uI uV

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace HyperedgeComparison

variable {V : Type uV} {E : Type uE}

theorem adj_symm {H : Hypergraph V E} {ω : E → Bool} {D : Set V} {x y : V}
    (h : Adj H ω D x y) : Adj H ω D y x := by
  obtain ⟨e, he, hd, hx, hy⟩ := h
  exact ⟨e, he, hd, hy, hx⟩

theorem connected_symm {H : Hypergraph V E} {ω : E → Bool} {D : Set V} {x y : V}
    (h : Connected H ω D x y) : Connected H ω D y x := by
  induction h with
  | refl => exact .refl
  | tail _ hxy ih => exact ih.head (adj_symm hxy)

theorem connected_trans {H : Hypergraph V E} {ω : E → Bool} {D : Set V} {x y z : V}
    (hxy : Connected H ω D x y) (hyz : Connected H ω D y z) :
    Connected H ω D x z := hxy.trans hyz

theorem adj_mono_delete {H : Hypergraph V E} {ω : E → Bool} {D D' : Set V}
    (hDD : D ⊆ D') {x y : V} (h : Adj H ω D' x y) : Adj H ω D x y := by
  obtain ⟨e, he, hd, hx, hy⟩ := h
  exact ⟨e, he, hd.mono_right hDD, hx, hy⟩

theorem cluster_mono_delete {H : Hypergraph V E} {ω : E → Bool} {D D' : Set V}
    (hDD : D ⊆ D') (x : V) : cluster H ω D' x ⊆ cluster H ω D x :=
  Relation.ReflTransGen.mono (fun _ _ => adj_mono_delete hDD) x

theorem clusters_mono_delete {H : Hypergraph V E} {ω : E → Bool} {D D' S : Set V}
    (hDD : D ⊆ D') : clusters H ω D' S ⊆ clusters H ω D S := by
  rintro y ⟨x, hx, hy⟩
  exact ⟨x, hx, cluster_mono_delete hDD x hy⟩

/-- Disjointness of a full cluster from a tested set is also disjointness from its
entire union of clusters, the fact used in the first-listed-node partition. -/
theorem cluster_disjoint_clusters_iff {H : Hypergraph V E} {ω : E → Bool}
    {D S : Set V} {x : V} :
    Disjoint (cluster H ω D x) (clusters H ω D S) ↔
      Disjoint (cluster H ω D x) S := by
  constructor
  · exact fun h => h.mono_right (clusters_contains H ω D S)
  · intro h
    apply Set.disjoint_left.mpr
    rintro y hy ⟨s, hs, hsy⟩
    exact Set.disjoint_left.mp h (connected_trans hy (connected_symm hsy)) hs

/-- Bits on deleted hyperedges are irrelevant to the surviving clusters. -/
theorem cluster_eq_of_agree_disjoint {H : Hypergraph V E} {ω ω' : E → Bool}
    {D : Set V} (hagree : ∀ e, Disjoint (H e) D → ω' e = ω e) (s : V) :
    cluster H ω' D s = cluster H ω D s := by
  have hrel : Adj H ω' D = Adj H ω D := by
    funext x y
    apply propext
    constructor <;> rintro ⟨e, he, hd, hx, hy⟩
    · exact ⟨e, (hagree e hd) ▸ he, hd, hx, hy⟩
    · exact ⟨e, (hagree e hd).trans he, hd, hx, hy⟩
  unfold cluster Connected
  rw [hrel]

theorem clusters_eq_of_agree_disjoint {H : Hypergraph V E} {ω ω' : E → Bool}
    {D S : Set V} (hagree : ∀ e, Disjoint (H e) D → ω' e = ω e) :
    clusters H ω' D S = clusters H ω D S := by
  unfold clusters
  simp only [cluster_eq_of_agree_disjoint hagree]

theorem clusters_singleton (H : Hypergraph V E) (ω : E → Bool) (D : Set V) (s : V) :
    clusters H ω D {s} = cluster H ω D s := by
  ext y
  simp [clusters]

/-- Deleting a cluster does not change the union of any disjoint clusters. -/
theorem clusters_delete_cluster {H : Hypergraph V E} {ω : E → Bool}
    {D S : Set V} {s : V} (h : Disjoint (cluster H ω D s) S) :
    clusters H ω (D ∪ cluster H ω D s) S = clusters H ω D S := by
  ext y
  constructor
  · exact fun hy => clusters_mono_delete Set.subset_union_left hy
  · rintro ⟨x, hx, hy⟩
    refine ⟨x, hx, ?_⟩
    have heq := cluster_delete_clusters (H := H) (ω := ω) (D := D) (S := {s})
      (x := x) (by simpa only [clusters_singleton] using (fun hxs => Set.disjoint_left.mp h hxs hx))
    rw [clusters_singleton] at heq
    rwa [heq]

section FiniteLaw
variable [Fintype E]

theorem column_resample [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k i : Fin n) (F : Set V → ℝ) :
    column H p x k (resample H p (x k) (earlier x k) F) i =
      ∫ ω, if firstRoot H x ω ∅ k i then
        meanAfterDelete H p (x k) (clusters H ω ∅ (earlier x k)) F else 0 ∂law p := by
  classical
  have h := column_conditional_expectation H p x k i
    (fun ω U => meanAfterDelete H p (x k) (clusters H ω U (earlier x k)) F)
    (by intro U ω ω' hagree; rw [clusters_eq_of_agree_disjoint hagree])
  change _ = column H p x k (resample H p (x k) (earlier x k) F) i at h
  rw [← h]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  by_cases hf : firstRoot H x ω ∅ k i
  · have heq := clusters_delete_cluster hf.1
    simp only [Set.empty_union] at heq
    simp [hf, heq]
  · simp [hf]

/-- An earlier list segment is included in every later segment. -/
theorem earlier_mono {n : ℕ} (x : Fin n → V) {k j : Fin n} (hkj : k ≤ j) :
    earlier x k ⊆ earlier x j := by
  rintro y ⟨l, hl, hly⟩
  exact ⟨l, lt_of_lt_of_le hl hkj, hly⟩

omit [Fintype E] in
/-- Separation from a union of full clusters is exactly avoidance by the root. -/
theorem disjoint_cluster_iff_root_notin {H : Hypergraph V E} {ω : E → Bool}
    {D S : Set V} {s : V} :
    Disjoint (cluster H ω D s) S ↔ s ∉ clusters H ω D S := by
  constructor
  · rintro hd ⟨t, ht, hts⟩
    exact Set.disjoint_left.mp hd (connected_symm hts) ht
  · intro hs
    apply Set.disjoint_left.mpr
    intro t hst ht
    exact hs ⟨t, ht, connected_symm hst⟩

omit [Fintype E] in
theorem firstRoot_notin_earlier_clusters {n : ℕ} {H : Hypergraph V E}
    {x : Fin n → V} {ω : E → Bool} {D : Set V} {j i k : Fin n}
    (hf : firstRoot H x ω D j i) (hkj : k ≤ j) :
    x i ∉ clusters H ω D (earlier x k) := by
  have hd := (cluster_disjoint_clusters_iff.mpr hf.1).mono_right
    (show clusters H ω D (earlier x k) ⊆ clusters H ω D (earlier x j) from by
      rintro y ⟨z, hz, hzy⟩
      exact ⟨z, earlier_mono x hkj hz, hzy⟩)
  exact fun hi => Set.disjoint_left.mp hd hf.2 hi

omit [Fintype E] in

theorem firstListed_partition {n : ℕ} (H : Hypergraph V E) (x : Fin n → V)
    (ω : E → Bool) (k i : Fin n) (a : ℝ) :
    (if x k ∉ clusters H ω ∅ (earlier x k) ∧ x i ∉ clusters H ω ∅ (earlier x k)
      then a else 0) =
      (if firstRoot H x ω ∅ k i then a else 0) +
        ∑ j, if k < j ∧ firstRoot H x ω ∅ j i ∧ x k ∉ clusters H ω ∅ (earlier x k)
          then a else 0 := by
  classical
  obtain ⟨j, hj, huniq⟩ := exists_unique_firstRoot H x ω ∅ i
  have hsum : (∑ l, if k < l ∧ firstRoot H x ω ∅ l i ∧
      x k ∉ clusters H ω ∅ (earlier x k) then a else 0) =
      if k < j ∧ x k ∉ clusters H ω ∅ (earlier x k) then a else 0 := by
    rw [Finset.sum_eq_single j]
    · simp only [hj, true_and]
    · intro l _ hlj
      have hlf : ¬firstRoot H x ω ∅ l i := fun h => hlj (huniq l h)
      simp [hlf]
    · simp
  rw [hsum]
  rcases lt_trichotomy j k with hjk | rfl | hkj
  · have hi : x i ∈ clusters H ω ∅ (earlier x k) := ⟨x j, ⟨j, hjk,rfl⟩, hj.2⟩
    have hk : ¬firstRoot H x ω ∅ k i := fun h => (ne_of_lt hjk) (huniq k h).symm
    simp [hi, hk, not_lt_of_gt hjk]
  · have hs := disjoint_cluster_iff_root_notin.mp hj.1
    have hi := firstRoot_notin_earlier_clusters hj le_rfl
    simp [hj, hs, hi]
  · have hi := firstRoot_notin_earlier_clusters hj hkj.le
    have hk : ¬firstRoot H x ω ∅ k i := fun h => (ne_of_lt hkj) (huniq k h)
    simp [hi, hk, hkj]

/-- Integrated form of the first-listed-node partition. -/
theorem integral_firstListed_partition {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k i : Fin n)
    (g : (E → Bool) → ℝ) :
    (∫ ω, if x k ∉ clusters H ω ∅ (earlier x k) ∧ x i ∉ clusters H ω ∅ (earlier x k)
      then g ω else 0 ∂law p) =
      (∫ ω, if firstRoot H x ω ∅ k i then g ω else 0 ∂law p) +
        ∑ j, ∫ ω, if k < j ∧ firstRoot H x ω ∅ j i ∧ x k ∉ clusters H ω ∅ (earlier x k)
          then g ω else 0 ∂law p := by
  simp_rw [firstListed_partition H x _ k i]
  rw [integral_add (Integrable.of_finite) (Integrable.of_finite),
    integral_finsetSum _ (fun _ _ => Integrable.of_finite)]

/-- Subtraction under a finite expectation with the same event indicator. -/
theorem integral_indicator_sub (p : E → Set.Icc (0 : ℝ) 1)
    (P : (E → Bool) → Prop) [DecidablePred P] (f g : (E → Bool) → ℝ) :
    (∫ ω, if P ω then f ω - g ω else 0 ∂law p) =
      (∫ ω, if P ω then f ω else 0 ∂law p) -
        ∫ ω, if P ω then g ω else 0 ∂law p := by
  have h : (fun ω => if P ω then f ω-g ω else 0) =
      (fun ω => (if P ω then f ω else 0) - (if P ω then g ω else 0)) := by
    funext ω
    by_cases h : P ω <;> simp [h]
  rw [h, integral_sub (Integrable.of_finite) (Integrable.of_finite)]

theorem column_identity [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k i : Fin n) (F : Set V → ℝ) :
    column H p x k F i = column H p x k (resample H p (x k) (earlier x k) F) i +
      ∑ j, if k < j then column H p x j (residualMean H p (x k) (earlier x k) · F) i
        else 0 := by
  classical
  let c : (E → Bool) → ℝ := fun ω =>
    meanAfterDelete H p (x k) (clusters H ω ∅ (earlier x k)) F
  let f : (E → Bool) → ℝ := fun ω => F (cluster H ω ∅ (x k))
  let P : Fin n → (E → Bool) → Prop := fun j ω =>
    k < j ∧ firstRoot H x ω ∅ j i ∧ x k ∉ clusters H ω ∅ (earlier x k)
  have hcond := conditioning_weight H p (x k) ∅ (earlier x k)
    (fun U => if x k ∉ U ∧ x i ∉ U then 1 else 0) F (by intro U h; simp [h])
  simp only [ite_mul, one_mul, zero_mul, Set.empty_union] at hcond
  rw [integral_firstListed_partition H p x k i,
    integral_firstListed_partition H p x k i] at hcond
  change column H p x k F i + (∑ j, ∫ ω, if P j ω then f ω else 0 ∂law p) =
    (∫ ω, if firstRoot H x ω ∅ k i then c ω else 0 ∂law p) +
      (∑ j, ∫ ω, if P j ω then c ω else 0 ∂law p) at hcond
  have hbase : column H p x k (resample H p (x k) (earlier x k) F) i =
      ∫ ω, if firstRoot H x ω ∅ k i then c ω else 0 ∂law p :=
    column_resample H p x k i F
  have hres (j : Fin n) :
      (if k < j then column H p x j (residualMean H p (x k) (earlier x k) · F) i else 0) =
        (∫ ω, if P j ω then c ω else 0 ∂law p) -
          ∫ ω, if P j ω then f ω else 0 ∂law p := by
    by_cases hkj : k < j
    · rw [ite_eq_left hkj, column_residual H p x k j i hkj F]
      rw [← integral_indicator_sub p (P j) c f]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ω
      by_cases h : firstRoot H x ω ∅ j i ∧ x k ∉ clusters H ω ∅ (earlier x k)
      · simp [P, hkj, h, c, f]
      · simp [P, hkj, h]
    · simp [P, hkj]
  have hsum : (∑ j, if k < j then
      column H p x j (residualMean H p (x k) (earlier x k) · F) i else 0) =
      (∑ j, ∫ ω, if P j ω then c ω else 0 ∂law p) -
        (∑ j, ∫ ω, if P j ω then f ω else 0 ∂law p) := by
    simp_rw [hres]
    rw [Finset.sum_sub_distrib]
  rw [hsum, hbase]
  linarith

/-- Inverse-basis coordinates obey the same column identity. -/
theorem coeff_identity [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k : Fin n) (F : Set V → ℝ) :
    coeff H p x k F = coeff H p x k (resample H p (x k) (earlier x k) F) +
      ∑ j, if k < j then coeff H p x j (residualMean H p (x k) (earlier x k) · F) else 0 := by
  have hc : column H p x k F = column H p x k (resample H p (x k) (earlier x k) F) +
      ∑ j, if k < j then column H p x j (residualMean H p (x k) (earlier x k) · F) else 0 := by
    funext i
    simpa only [Pi.add_apply, Finset.sum_apply, ite_apply, Pi.zero_apply] using
      column_identity H p x k i F
  unfold coeff
  rw [hc, Matrix.mulVec_add, Matrix.mulVec_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : k < j <;> simp [h]

end FiniteLaw
namespace Site
variable (G : SimpleGraph V)

end Site

end HyperedgeComparison

end OAI

-- ---- platform node ----
open OAI OAI.HyperedgeComparison
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix


theorem solution.{uE,uV} : type_of% @_root_.OAI.HyperedgeComparison.coeff_identity.{uE,uV} := @_root_.OAI.HyperedgeComparison.coeff_identity.{uE,uV}
