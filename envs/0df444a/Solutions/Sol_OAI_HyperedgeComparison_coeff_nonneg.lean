-- Prove2me | solution 1 for OAI.HyperedgeComparison.coeff_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:07:27.383615+00:00
-- url     : https://prove2.me/submissions/f8b227b2-b2e6-495b-9276-2b6c114f6023

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean:L1154-L1220
-- (upload_full_project.md Phase 4): solution for node OAI.HyperedgeComparison.coeff_nonneg. The node keeps its source
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
import Theorems.Thm_OAI_HyperedgeComparison_baseMatrix_diag_pos
import Theorems.Thm_OAI_HyperedgeComparison_cluster_delete_clusters
import Theorems.Thm_OAI_HyperedgeComparison_coeff_identity
import Theorems.Thm_OAI_HyperedgeComparison_resample_tendsto_constant
import Theorems.Thm_OAI_HyperedgeComparison_residualMean_eq_integral

-- ---- from OAI.Probability.CriticalZ3.HyperedgeComparison ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uE uI uV

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace HyperedgeComparison

variable {V : Type uV} {E : Type uE}

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

theorem residual_cluster_mem_domain {H : Hypergraph V E} {ω : E → Bool}
    {s : V} {S U : Set V} (hs : s ∉ clusters H ω U S) :
    cluster H ω (clusters H ω U S) s ∈ ClusterDomain s S := by
  refine ⟨.refl, (cluster_avoids_deleted hs).mono_right ?_⟩
  exact clusters_contains H ω U S

theorem residual_cluster_union_mem_domain {H : Hypergraph V E} {ω : E → Bool}
    {s : V} {S U : Set V} (hs : s ∉ clusters H ω U S) (hsU : s ∉ U) :
    cluster H ω (clusters H ω U S ∪ U) s ∈ ClusterDomain s S := by
  refine ⟨.refl, (cluster_avoids_deleted (fun h => h.elim hs hsU)).mono_right ?_⟩
  exact (clusters_contains H ω U S).trans Set.subset_union_left

theorem residualSample_nonneg {H : Hypergraph V E} {ω : E → Bool}
    {s : V} {S U : Set V} {F : Set V → ℝ} (hsU : s ∉ U)
    (hF : MonotoneOn F (ClusterDomain s S)) :
    0 ≤ residualSample H ω s S U F := by
  classical
  unfold residualSample
  split_ifs with hs
  · exact le_rfl
  · exact sub_nonneg.mpr (hF (residual_cluster_union_mem_domain hs hsU)
      (residual_cluster_mem_domain hs) (cluster_mono_delete Set.subset_union_left s))

theorem residualSample_mono {H : Hypergraph V E} {ω : E → Bool}
    {s : V} {S U U' : Set V} {F : Set V → ℝ}
    (hUU : U ⊆ U') (hsU' : s ∉ U') (hF : MonotoneOn F (ClusterDomain s S)) :
    residualSample H ω s S U F ≤ residualSample H ω s S U' F := by
  classical
  have hsU : s ∉ U := fun hs => hsU' (hUU hs)
  by_cases hs : s ∈ clusters H ω U S
  · rw [residualSample, ite_eq_left hs]
    exact residualSample_nonneg hsU' hF
  · have hs' : s ∉ clusters H ω U' S :=
      fun h => hs (clusters_mono_delete hUU h)
    have hfirst : F (cluster H ω (clusters H ω U S) s) ≤
        F (cluster H ω (clusters H ω U' S) s) :=
      hF (residual_cluster_mem_domain hs) (residual_cluster_mem_domain hs')
        (cluster_mono_delete (clusters_mono_delete hUU) s)
    have heq : cluster H ω (clusters H ω U S ∪ U) s = cluster H ω U s := by
      rw [Set.union_comm]
      exact cluster_delete_clusters hs
    have heq' : cluster H ω (clusters H ω U' S ∪ U') s = cluster H ω U' s := by
      rw [Set.union_comm]
      exact cluster_delete_clusters hs'
    have hsecond : F (cluster H ω (clusters H ω U' S ∪ U') s) ≤
        F (cluster H ω (clusters H ω U S ∪ U) s) := by
      apply hF (residual_cluster_union_mem_domain hs' hsU')
        (residual_cluster_union_mem_domain hs hsU)
      rw [heq, heq']
      exact cluster_mono_delete hUU s
    simp only [residualSample, ite_eq_right hs, ite_eq_right hs']
    exact sub_le_sub hfirst hsecond

section FiniteLaw
variable [Fintype E]

theorem residualMean_nonneg [Fintype V] {H : Hypergraph V E}
    {p : E → Set.Icc (0 : ℝ) 1} {s : V} {S U : Set V} {F : Set V → ℝ}
    (hsU : s ∉ U) (hF : MonotoneOn F (ClusterDomain s S)) :
    0 ≤ residualMean H p s S U F := by
  rw [residualMean_eq_integral]
  exact integral_nonneg (fun _ => residualSample_nonneg hsU hF)

theorem residualMean_mono [Fintype V] {H : Hypergraph V E}
    {p : E → Set.Icc (0 : ℝ) 1} {s : V} {S U U' : Set V} {F : Set V → ℝ}
    (hUU : U ⊆ U') (hsU' : s ∉ U') (hF : MonotoneOn F (ClusterDomain s S)) :
    residualMean H p s S U F ≤ residualMean H p s S U' F := by
  rw [residualMean_eq_integral, residualMean_eq_integral]
  exact integral_mono (Integrable.of_finite) (Integrable.of_finite)
    (fun _ => residualSample_mono hUU hsU' hF)

theorem meanAfterDelete_antitone {H : Hypergraph V E}
    {p : E → Set.Icc (0 : ℝ) 1} {s : V} {S W W' : Set V} {F : Set V → ℝ}
    (hWW : W ⊆ W') (hSW : S ⊆ W) (hs : s ∉ W')
    (hF : MonotoneOn F (ClusterDomain s S)) :
    meanAfterDelete H p s W' F ≤ meanAfterDelete H p s W F := by
  apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
  intro ω
  apply hF
  · exact ⟨.refl, (cluster_avoids_deleted hs).mono_right (hSW.trans hWW)⟩
  · exact ⟨.refl, (cluster_avoids_deleted (fun h => hs (hWW h))).mono_right hSW⟩
  · exact cluster_mono_delete hWW s

theorem resample_monotone {H : Hypergraph V E}
    {p : E → Set.Icc (0 : ℝ) 1} {s : V} {S : Set V} {F : Set V → ℝ}
    (hF : MonotoneOn F (ClusterDomain s S)) :
    MonotoneOn (resample H p s S F) (ClusterDomain s S) := by
  intro U hU U' hU' hUU
  apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
  intro ω
  apply meanAfterDelete_antitone (clusters_mono_delete hUU) (clusters_contains H ω U' S)
  · exact fun hs => Set.disjoint_left.mp (clusters_avoids_deleted hU.2.symm) hs hU.1
  · exact hF

theorem resample_nonneg {H : Hypergraph V E}
    {p : E → Set.Icc (0 : ℝ) 1} {s : V} {S U : Set V} {F : Set V → ℝ}
    (hF : ∀ U ∈ ClusterDomain s S, 0 ≤ F U) (hU : U ∈ ClusterDomain s S) :
    0 ≤ resample H p s S F U := by
  apply integral_nonneg
  intro ω
  apply integral_nonneg
  intro ω'
  apply hF
  exact ⟨.refl, (cluster_avoids_deleted (fun hs =>
    Set.disjoint_left.mp (clusters_avoids_deleted hU.2.symm) hs hU.1)).mono_right
      (clusters_contains H ω U S)⟩

/-- Pointwise convergence exchanges with any expectation on a finite bit space. -/
theorem tendsto_integral_finite (p : E → Set.Icc (0 : ℝ) 1)
    (f : ℕ → (E → Bool) → ℝ) (g : (E → Bool) → ℝ)
    (h : ∀ ω, Tendsto (fun n => f n ω) atTop (nhds (g ω))) :
    Tendsto (fun n => ∫ ω, f n ω ∂law p) atTop (nhds (∫ ω, g ω ∂law p)) := by
  simp_rw [integral_fintype (Integrable.of_finite)]
  exact tendsto_finsetSum _ (fun ω _ => tendsto_const_nhds.smul (h ω))

/-- Column convergence only needs convergence on its specified cluster domain. -/
theorem column_tendsto {n : ℕ} (H : Hypergraph V E) (p : E → Set.Icc (0 : ℝ) 1)
    (x : Fin n → V) (k i : Fin n) (F : ℕ → Set V → ℝ) (c : ℝ)
    (h : ∀ U ∈ ClusterDomain (x k) (earlier x k),
      Tendsto (fun t => F t U) atTop (nhds c)) :
    Tendsto (fun t => column H p x k (F t) i) atTop
      (nhds (column H p x k (fun _ => c) i)) := by
  unfold column
  apply tendsto_integral_finite
  intro ω
  by_cases hf : firstRoot H x ω ∅ k i
  · simp only [hf, ite_true]
    exact h _ ⟨.refl, hf.1⟩
  · simp only [hf, ite_false]
    exact tendsto_const_nhds

omit [Fintype E] in
theorem root_notin_earlier {n : ℕ} {x : Fin n → V} (hx : Function.Injective x) (k : Fin n) :
    x k ∉ earlier x k := by
  rintro ⟨j, hj, heq⟩
  exact (ne_of_lt hj) (hx heq)

theorem baseMatrix_lowerTriangular {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) : (baseMatrix H p x).IsLowerTriangular := by
  intro i j hij
  have hf (ω : E → Bool) : ¬firstRoot H x ω ∅ j i := by
    intro hf
    exact Set.disjoint_left.mp hf.1 hf.2 ⟨i, hij, rfl⟩
  simp [baseMatrix, column, hf]

theorem baseMatrix_det_ne_zero {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) :
    (baseMatrix H p x).det ≠ 0 := by
  rw [Matrix.det_of_isLowerTriangular _ (baseMatrix_lowerTriangular H p x)]
  exact Finset.prod_ne_zero_iff.mpr (fun k _ => ne_of_gt (baseMatrix_diag_pos H p hp x hx k))

theorem column_const {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k : Fin n) (c : ℝ) :
    column H p x k (fun _ => c) = c • column H p x k (fun _ => 1) := by
  funext i
  unfold column
  change (∫ ω, if firstRoot H x ω ∅ k i then c else 0 ∂law p) =
    c * ∫ ω, if firstRoot H x ω ∅ k i then 1 else 0 ∂law p
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  by_cases hf : firstRoot H x ω ∅ k i <;> simp [hf]

theorem coeff_const {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) (k i : Fin n) (c : ℝ) :
    coeff H p x k (fun _ => c) i = if i = k then c else 0 := by
  have hdet : IsUnit (baseMatrix H p x).det := isUnit_iff_ne_zero.mpr
    (baseMatrix_det_ne_zero H p hp x hx)
  have hinv : coeff H p x k (fun _ => 1) i = if i = k then 1 else 0 := by
    change ((baseMatrix H p x)⁻¹ * baseMatrix H p x) i k = _
    rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_apply]
  unfold coeff
  rw [column_const, Matrix.mulVec_smul]
  change c * coeff H p x k (fun _ => 1) i = _
  rw [hinv]
  split_ifs <;> simp

/-- Convergence passes to inverse-basis coordinates by finite linearity. -/
theorem coeff_tendsto {n : ℕ} (H : Hypergraph V E) (p : E → Set.Icc (0 : ℝ) 1)
    (x : Fin n → V) (k i : Fin n) (F : ℕ → Set V → ℝ) (c : ℝ)
    (h : ∀ U ∈ ClusterDomain (x k) (earlier x k),
      Tendsto (fun t => F t U) atTop (nhds c)) :
    Tendsto (fun t => coeff H p x k (F t) i) atTop
      (nhds (coeff H p x k (fun _ => c) i)) := by
  unfold coeff Matrix.mulVec dotProduct
  exact tendsto_finsetSum _ (fun j _ => tendsto_const_nhds.mul (column_tendsto H p x k j F c h))

theorem coeff_nonneg [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) (k : Fin n) (F : Set V → ℝ)
    (hF0 : ∀ U ∈ ClusterDomain (x k) (earlier x k), 0 ≤ F U)
    (hFm : MonotoneOn F (ClusterDomain (x k) (earlier x k))) (i : Fin n) :
    0 ≤ coeff H p x k F i := by
  suffices aux : ∀ m : ℕ, ∀ k : Fin n, n - k.val = m → ∀ F : Set V → ℝ,
      (∀ U ∈ ClusterDomain (x k) (earlier x k), 0 ≤ F U) →
      MonotoneOn F (ClusterDomain (x k) (earlier x k)) →
      ∀ i, 0 ≤ coeff H p x k F i by
    exact aux (n - k.val) k rfl F hF0 hFm i
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro k hkm F hF0 hFm i
    let G : ℕ → Set V → ℝ := fun t => (resample H p (x k) (earlier x k))^[t] F
    have hG0 (t : ℕ) : ∀ U ∈ ClusterDomain (x k) (earlier x k), 0 ≤ G t U := by
      induction t with
      | zero => exact hF0
      | succ t ht =>
        intro U hU
        simpa only [G, Function.iterate_succ_apply'] using
          (resample_nonneg (H := H) (p := p) ht hU)
    have hGm (t : ℕ) : MonotoneOn (G t) (ClusterDomain (x k) (earlier x k)) := by
      induction t with
      | zero => exact hFm
      | succ t ht =>
        simpa only [G, Function.iterate_succ_apply'] using
          (resample_monotone (H := H) (p := p) ht)
    have hstep (t : ℕ) : coeff H p x k (G (t + 1)) i ≤ coeff H p x k (G t) i := by
      have hid := congrFun (coeff_identity H p x k (G t)) i
      simp only [Pi.add_apply, Finset.sum_apply, ite_apply, Pi.zero_apply] at hid
      have hr : 0 ≤ ∑ j : Fin n, if k < j then
          coeff H p x j (residualMean H p (x k) (earlier x k) · (G t)) i else 0 := by
        apply Finset.sum_nonneg
        intro j _
        split_ifs with hkj
        · have hmj : n - j.val < m := by
            have hjn := j.isLt
            have hkn := k.isLt
            have hkjv : k.val < j.val := hkj
            omega
          apply ih (n - j.val) hmj j rfl _
          · intro U hU
            apply residualMean_nonneg _ (hGm t)
            intro hu
            exact Set.disjoint_left.mp hU.2 hu ⟨k, hkj, rfl⟩
          · intro U hU U' hU' hUU
            apply residualMean_mono hUU _ (hGm t)
            intro hu
            exact Set.disjoint_left.mp hU'.2 hu ⟨k, hkj, rfl⟩
        · exact le_rfl
      have heq : G (t + 1) = resample H p (x k) (earlier x k) (G t) :=
        Function.iterate_succ_apply' _ _ _
      rw [heq]
      linarith
    have hant : Antitone (fun t => coeff H p x k (G t) i) :=
      antitone_nat_of_succ_le hstep
    obtain ⟨c, hc, hlim⟩ := resample_tendsto_constant H p hp (x k) (earlier x k)
      (root_notin_earlier hx k) F hF0
    have hl := coeff_tendsto H p x k i G c hlim
    have hle : coeff H p x k (fun _ => c) i ≤ coeff H p x k F i := by
      apply le_of_tendsto hl
      exact Filter.Eventually.of_forall (fun t => hant (Nat.zero_le t))
    apply le_trans _ hle
    rw [coeff_const H p hp x hx]
    split_ifs <;> positivity

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


theorem solution.{uE,uV} : type_of% @_root_.OAI.HyperedgeComparison.coeff_nonneg.{uE,uV} := @_root_.OAI.HyperedgeComparison.coeff_nonneg.{uE,uV}
