-- Prove2me | solution 1 for MonoSkew.Main.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-23T11:52:38.336989+00:00
-- url     : https://prove2.me/submissions/45411e1c-d4c8-4a9b-a1cd-dae7a2e14807

import Mathlib
import Definitions.Def_MonoSkew_Main_Basic
import Theorems.Thm_QuasiFejerOpial_exists_weak_subsequence


/-!
# Deterministic quasi-Fejer convergence with summable errors

Source: Benar F. Svaiter, *Fejer-convergent algorithms which accept summable
errors, approximated resolvents and the Hybrid Proximal-Extragradient method*,
Definition 2.1 and Proposition 2.2 (2)-(3), printed pp. 2-3.
https://webdoc.sub.gwdg.de/ebook/serien/e/IMPA_A/715.pdf

These are formalizations of standard published results, not new mathematical
claims. The scalar proof uses Mathlib's monotone convergence and convergence of
partial sums. The metric result needs neither completeness nor compactness:
the required convergent subsequence is an explicit hypothesis.
-/

open Filter Topology
open scoped BigOperators

namespace ShorNonsmooth.QuasiFejer

/-- A nonnegative real sequence whose upward increments are bounded by a
nonnegative summable error sequence has a finite limit. This is the scalar
core of Svaiter's Proposition 2.2 (2). -/
theorem scalar_converges_of_summable_error (a e : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (he : ∀ n, 0 ≤ e n) (hsum : Summable e)
    (hstep : ∀ n, a (n + 1) ≤ a n + e n) :
    ∃ L : ℝ, Tendsto a atTop (𝓝 L) := by
  let b : ℕ → ℝ := fun n => a n - ∑ i ∈ Finset.range n, e i
  have hb : Antitone b := by
    apply antitone_nat_of_succ_le
    intro n
    dsimp [b]
    rw [Finset.sum_range_succ]
    linarith [hstep n]
  have hbounded : BddBelow (Set.range b) := by
    refine ⟨-(∑' i, e i), ?_⟩
    rintro _ ⟨n, rfl⟩
    have hs := hsum.sum_le_tsum (Finset.range n) (fun i _ => he i)
    dsimp [b]
    linarith [ha n]
  refine ⟨(⨅ n, b n) + ∑' i, e i, ?_⟩
  have hlim := (tendsto_atTop_ciInf hb hbounded).add hsum.hasSum.tendsto_sum_nat
  simpa only [b, sub_add_cancel] using hlim

end ShorNonsmooth.QuasiFejer


/-!
Uniqueness component of the quasi-Fejer / Opial argument.
The exact platform WeakTendsto definition is imported. The local
IsSeqWeakClusterPt predicate below is definitionally the same existential as
MonoSkew.Main.IsSeqWeakClusterPt from Def_MonoSkew_Main_Basic.lean, as checked by the bridge lemma in the final assembly.
Source: Svaiter, Proposition 2.4, using the standard squared-distance identity.
This section proves uniqueness; existence and full weak convergence are supplied
by the later assembly. Completeness is unnecessary for the uniqueness helpers.
-/

open Filter Topology
open ThreeOpSplitting.Convergence

namespace ShorNonsmooth.QuasiFejer

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The same subsequence-based semantics as MonoSkew.Main.IsSeqWeakClusterPt. -/
def IsSeqWeakClusterPt (x : ℕ → H) (p : H) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ WeakTendsto (x ∘ φ) p

/-- Explicit semantic expansion matching the platform cluster predicate. -/
theorem isSeqWeakClusterPt_iff (x : ℕ → H) (p : H) :
    IsSeqWeakClusterPt x p ↔
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ y : H, Tendsto (fun k => inner ℝ (x (φ k)) y) atTop (𝓝 (inner ℝ p y)) :=
  Iff.rfl

/-- Two weak subsequential limits coincide if the squared distances to both
points converge along the whole sequence. -/
theorem weak_cluster_unique_of_sq_dist_limits (x : ℕ → H) (p q : H)
    (hp : ∃ L : ℝ, Tendsto (fun k => ‖x k - p‖ ^ 2) atTop (𝓝 L))
    (hq : ∃ L : ℝ, Tendsto (fun k => ‖x k - q‖ ^ 2) atTop (𝓝 L))
    (hcp : IsSeqWeakClusterPt x p) (hcq : IsSeqWeakClusterPt x q) : p = q := by
  obtain ⟨Lp, hLp⟩ := hp
  obtain ⟨Lq, hLq⟩ := hq
  obtain ⟨φ, hφ, hφlim⟩ := hcp
  obtain ⟨ψ, hψ, hψlim⟩ := hcq
  have hid (z : H) : ‖z - p‖ ^ 2 - ‖z - q‖ ^ 2 =
      ‖p‖ ^ 2 - ‖q‖ ^ 2 - 2 * inner ℝ z (p - q) := by
    rw [norm_sub_sq_real, norm_sub_sq_real, inner_sub_right]
    ring
  have hdiff := hLp.sub hLq
  have hlp : Lp - Lq = ‖p‖ ^ 2 - ‖q‖ ^ 2 - 2 * inner ℝ p (p - q) := by
    have hw := ((hφlim (p - q)).const_mul 2).const_sub (‖p‖ ^ 2 - ‖q‖ ^ 2)
    have hs := hdiff.comp hφ.tendsto_atTop
    simp only [Function.comp_def, hid] at hs
    exact tendsto_nhds_unique hs hw
  have hlq : Lp - Lq = ‖p‖ ^ 2 - ‖q‖ ^ 2 - 2 * inner ℝ q (p - q) := by
    have hw := ((hψlim (p - q)).const_mul 2).const_sub (‖p‖ ^ 2 - ‖q‖ ^ 2)
    have hs := hdiff.comp hψ.tendsto_atTop
    simp only [Function.comp_def, hid] at hs
    exact tendsto_nhds_unique hs hw
  have hi : inner ℝ (p - q) (p - q) = 0 := by
    rw [inner_sub_left]
    linarith
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hi)

/-- Uniqueness within a target set; no nonemptiness or closedness is needed. -/
theorem weak_cluster_unique_in_set (x : ℕ → H) (C : Set H)
    (hlim : ∀ y ∈ C, ∃ L : ℝ, Tendsto (fun k => ‖x k - y‖ ^ 2) atTop (𝓝 L))
    (p q : H) (hp : p ∈ C) (hq : q ∈ C)
    (hcp : IsSeqWeakClusterPt x p) (hcq : IsSeqWeakClusterPt x q) : p = q :=
  weak_cluster_unique_of_sq_dist_limits x p q (hlim p hp) (hlim q hq) hcp hcq

/-- Summable errors may depend on the target point. This proves only uniqueness
of weak cluster points in C, not existence or convergence of the full sequence. -/
theorem weak_cluster_unique_of_quasiFejer_sq (x : ℕ → H) (C : Set H)
    (hquasi : ∀ y ∈ C, ∃ e : ℕ → ℝ, (∀ k, 0 ≤ e k) ∧ Summable e ∧
      ∀ k, ‖x (k + 1) - y‖ ^ 2 ≤ ‖x k - y‖ ^ 2 + e k)
    (p q : H) (hp : p ∈ C) (hq : q ∈ C)
    (hcp : IsSeqWeakClusterPt x p) (hcq : IsSeqWeakClusterPt x q) : p = q := by
  apply weak_cluster_unique_in_set x C _ p q hp hq hcp hcq
  intro y hy
  obtain ⟨e, he, hs, hstep⟩ := hquasi y hy
  exact scalar_converges_of_summable_error (fun k => ‖x k - y‖ ^ 2) e
    (fun k => sq_nonneg _) he hs hstep

end ShorNonsmooth.QuasiFejer


/-!
Conditional assembly of the Opial / quasi-Fejer argument.
Weak subsequence extraction is an explicit assumption of these intermediate
helpers. The final solution discharges it using the imported proved Hilbert theorem.
We test weak convergence against each fixed vector and apply the scalar filter
subsequence criterion. No first-countability assertion about a weak topology is
used. All cluster predicates have the platform semantics documented in
WeakClusterUniqueness.lean.
-/

open Filter Topology
open ThreeOpSplitting.Convergence

namespace ShorNonsmooth.QuasiFejer

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- If every subsequence admits a weakly convergent further subsequence, and all
weak cluster points are in C, the squared-distance limits force weak convergence.
The extraction property is assumed, not derived from boundedness here. -/
theorem weakTendsto_of_sq_dist_limits_of_subseq_extraction
    (x : ℕ → H) (C : Set H)
    (hlim : ∀ y ∈ C, ∃ L : ℝ, Tendsto (fun k => ‖x k - y‖ ^ 2) atTop (𝓝 L))
    (hclus : ∀ w, IsSeqWeakClusterPt x w → w ∈ C)
    (hextract : ∀ φ : ℕ → ℕ, StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ w : H,
        WeakTendsto (fun k => x (φ (ψ k))) w) :
    ∃ c ∈ C, WeakTendsto x c := by
  obtain ⟨φ, hφ, c, hc⟩ := hextract id strictMono_id
  have hcc : IsSeqWeakClusterPt x c := ⟨φ, hφ, hc⟩
  have hcC : c ∈ C := hclus c hcc
  refine ⟨c, hcC, ?_⟩
  intro y
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨η, hη, hnsη⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨ψ, hψ, w, hw⟩ := hextract (ns ∘ η) hnsη
  have hwc : IsSeqWeakClusterPt x w :=
    ⟨(ns ∘ η) ∘ ψ, hnsη.comp hψ, hw⟩
  have heq : w = c := weak_cluster_unique_in_set x C hlim w c
    (hclus w hwc) hcC hwc hcc
  refine ⟨η ∘ ψ, ?_⟩
  simpa only [heq, Function.comp_def] using hw y

/-- Conditional Opial assembly for target-dependent summable squared-distance
errors. Weak subsequence extraction remains an explicit hypothesis. -/
theorem weakTendsto_of_quasiFejer_sq_of_subseq_extraction
    (x : ℕ → H) (C : Set H)
    (hquasi : ∀ y ∈ C, ∃ e : ℕ → ℝ, (∀ k, 0 ≤ e k) ∧ Summable e ∧
      ∀ k, ‖x (k + 1) - y‖ ^ 2 ≤ ‖x k - y‖ ^ 2 + e k)
    (hclus : ∀ w, IsSeqWeakClusterPt x w → w ∈ C)
    (hextract : ∀ φ : ℕ → ℕ, StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ w : H,
        WeakTendsto (fun k => x (φ (ψ k))) w) :
    ∃ c ∈ C, WeakTendsto x c := by
  apply weakTendsto_of_sq_dist_limits_of_subseq_extraction x C _ hclus hextract
  intro y hy
  obtain ⟨e, he, hs, hstep⟩ := hquasi y hy
  exact scalar_converges_of_summable_error (fun k => ‖x k - y‖ ^ 2) e
    (fun k => sq_nonneg _) he hs hstep

end ShorNonsmooth.QuasiFejer


/-!
Complete assembly of the public MonoSkew.Main.lemma_2_2 statement.
The target-set error sequence may depend on the point. Boundedness follows
from a scalar squared-distance limit; weak subsequence extraction is proved
separately for general Hilbert spaces, not assumed in this theorem.
Source: Briceno-Arias and Combettes, A Monotone+Skew Splitting Model for Composite
Monotone Inclusions in Duality, arXiv:1011.5517v1, Lemma 2.2 (p. 4).
-/

open Filter Topology
open ThreeOpSplitting.Convergence

open MonoSkew.Main

/-- The local lightweight cluster predicate is exactly the platform definition. -/
theorem isSeqWeakClusterPt_iff_local {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : ℕ → E) (w : E) :
    IsSeqWeakClusterPt x w ↔ ShorNonsmooth.QuasiFejer.IsSeqWeakClusterPt x w := Iff.rfl

/-- Full quasi-Fejer version of Opial's lemma, with no extraction hypothesis. -/
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : Set E) (hC : C.Nonempty) (x : ℕ → E)
    (hfej : ∀ c ∈ C, ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ Summable ε ∧
      ∀ n, ‖x (n + 1) - c‖ ^ 2 ≤ ‖x n - c‖ ^ 2 + ε n)
    (hclus : ∀ w, IsSeqWeakClusterPt x w → w ∈ C) :
    ∃ c ∈ C, WeakTendsto x c := by
  obtain ⟨c₀, hc₀⟩ := hC
  obtain ⟨ε, hε, hsum, hstep⟩ := hfej c₀ hc₀
  obtain ⟨L, hL⟩ := ShorNonsmooth.QuasiFejer.scalar_converges_of_summable_error
    (fun n => ‖x n - c₀‖ ^ 2) ε (fun n => sq_nonneg _) hε hsum hstep
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _ hL).exists_norm_le
  have hsq (n : ℕ) : ‖x n - c₀‖ ^ 2 ≤ B := by
    have hb := hB (‖x n - c₀‖ ^ 2) ⟨n, rfl⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x n - c₀‖)] using hb
  have hB0 : 0 ≤ B := (sq_nonneg _).trans (hsq 0)
  have hnorm : ∀ n, ‖x n‖ ≤ B + 1 + ‖c₀‖ := by
    intro n
    have hd : ‖x n - c₀‖ ≤ B + 1 := by
      have := hsq n
      nlinarith [sq_nonneg (‖x n - c₀‖ - 1)]
    calc
      ‖x n‖ = ‖(x n - c₀) + c₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖x n - c₀‖ + ‖c₀‖ := norm_add_le _ _
      _ ≤ B + 1 + ‖c₀‖ := add_le_add hd le_rfl
  apply ShorNonsmooth.QuasiFejer.weakTendsto_of_quasiFejer_sq_of_subseq_extraction
    x C hfej (fun w hw => hclus w ((isSeqWeakClusterPt_iff_local x w).mpr hw))
  intro φ hφ
  obtain ⟨ψ, hψ, w, hw⟩ := QuasiFejerOpial.exists_weak_subsequence (x ∘ φ)
    (B + 1 + ‖c₀‖) (fun n => hnorm (φ n))
  exact ⟨ψ, hψ, w, hw⟩



