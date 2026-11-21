-- Prove2me | solution 1 for MasulloGRH.nuclear_finite_rank_approximation
-- status  : ACCEPTED   (prove)
-- author  : @ghseeli
-- created : 2026-11-21T00:36:26.721721+00:00
-- url     : https://prove2.me/submissions/8ecaba64-79f3-42c4-ae19-e43279c53b27

import Theorems.Thm_MasulloGRH_nuclear_dual_domination
import Theorems.Thm_MasulloGRH_nuclear_expansion_of_dual_domination
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MasulloGRH Filter Topology Set
open scoped BigOperators

private theorem sum_bound {E : Type*} [AddCommGroup E] [Module ℂ E]
    (q : Seminorm ℂ E) (y : ℕ → E) (g : ℕ → ℂ) (c : ℕ → ℝ)
    (R : ℝ) (_hR : 0 ≤ R) (hc : ∀ n, 0 ≤ c n) (hy : ∀ n, q (y n) ≤ 1)
    (hg : ∀ n, ‖g n‖ ≤ R) (s : Finset ℕ) :
    q (∑ n ∈ s, ((c n : ℂ) * g n) • y n) ≤ (∑ n ∈ s, c n) * R := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
    simp only [Finset.sum_insert hn]
    apply (map_add_le_add q _ _).trans
    have hterm : q (((c n : ℂ) * g n) • y n) ≤ c n * R := by
      rw [map_smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc n)]
      calc c n * ‖g n‖ * q (y n) ≤ c n * ‖g n‖ * 1 :=
          mul_le_mul_of_nonneg_left (hy n) (mul_nonneg (hc n) (norm_nonneg _))
        _ ≤ c n * R := by simpa using mul_le_mul_of_nonneg_left (hg n) (hc n)
    nlinarith

private theorem identity_approx (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsNuclear E) (B : Set E) (hB : Bornology.IsVonNBounded ℂ B)
    (q : Seminorm ℂ E) (hq : Continuous q) (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (φ : Fin N → StrongDual ℂ E) (y : Fin N → E),
      ∀ x ∈ B, q (x - ∑ i, φ i x • y i) < ε := by
  classical
  obtain ⟨⟨ι, hι, p, hp⟩, hT⟩ := hE.1
  let : IsTopologicalAddGroup E := hp.topologicalAddGroup
  let : ContinuousSMul ℂ E := hp.continuousSMul
  let : PolynormableSpace ℂ E := hp.toPolynormableSpace
  obtain ⟨r, y, g, c, hr, hc0, hc, hy, hg, hconv⟩ :=
    MasulloGRH.nuclear_expansion_of_dual_domination E hE.1
      (MasulloGRH.nuclear_dual_domination E hE) q hq
  obtain ⟨R, hR, hRB⟩ := (PolynormableSpace.withSeminorms ℂ E).isVonNBounded_iff_seminorm_bounded.mp
    hB ⟨r, hr⟩
  let S : ℕ → E → E := fun N x => ∑ n ∈ Finset.range N, ((c n : ℂ) * g n x) • y n
  let tail : ℕ → ℝ := fun N => (∑' n, c n) - ∑ n ∈ Finset.range N, c n
  have htpos (N : ℕ) : 0 ≤ tail N := sub_nonneg.mpr
    (hc.sum_le_tsum (Finset.range N) (fun n _ => hc0 n))
  have herror (N : ℕ) (x : E) : q (x - S N x) ≤ tail N * r x := by
    have hlim : Tendsto (fun M : ℕ => q (x - S M x) +
        ((∑ n ∈ Finset.range M, c n) - ∑ n ∈ Finset.range N, c n) * r x)
        atTop (𝓝 (tail N * r x)) := by
      simpa [S, tail] using (hconv x).add
        ((hc.hasSum.tendsto_sum_nat.sub_const (∑ n ∈ Finset.range N, c n)).mul_const (r x))
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop N] with M hNM
    have hdiff : q (S M x - S N x) ≤
        ((∑ n ∈ Finset.range M, c n) - ∑ n ∈ Finset.range N, c n) * r x := by
      have hh := sum_bound q y (fun n => g n x) c (r x) (apply_nonneg r x)
        hc0 hy (fun n => hg n x) (Finset.Ico N M)
      simpa only [Finset.sum_Ico_eq_sub _ hNM, S] using hh
    calc
      q (x - S N x) = q ((x - S M x) + (S M x - S N x)) := by congr 1; abel
      _ ≤ q (x - S M x) + q (S M x - S N x) := map_add_le_add q _ _
      _ ≤ _ := add_le_add le_rfl hdiff
  have ht : Tendsto (fun N => tail N * R) atTop (𝓝 0) := by
    have ht0 : Tendsto (fun _ : ℕ => ∑' n, c n) atTop (𝓝 (∑' n, c n)) := tendsto_const_nhds
    simpa [tail] using (ht0.sub hc.hasSum.tendsto_sum_nat).mul_const R
  obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨N, fun i => (c i : ℂ) • g i, fun i => y i, ?_⟩
  intro x hx
  have he : q (x - S N x) < ε :=
    lt_of_le_of_lt ((herror N x).trans
      (mul_le_mul_of_nonneg_left (hRB x hx).le (htpos N))) hN
  simpa [S, ← Fin.sum_univ_eq_sum_range, smul_eq_mul] using he


theorem solution (E F : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (hE : IsNuclear E) (T : E →L[ℂ] F) (B : Set E)
    (hB : Bornology.IsVonNBounded ℂ B) (q : Seminorm ℂ F) (hq : Continuous q)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (φ : Fin N → StrongDual ℂ E) (y : Fin N → F),
      ∀ x ∈ B, q (T x - ∑ i, φ i x • y i) < ε := by
  have hcomp : Continuous (q.comp T.toLinearMap) := hq.comp T.continuous
  obtain ⟨N, φ, y, ha⟩ := identity_approx E hE B hB (q.comp T.toLinearMap) hcomp ε hε
  refine ⟨N, φ, fun i => T (y i), ?_⟩
  intro x hx
  simpa only [Seminorm.comp_apply, ContinuousLinearMap.coe_coe, map_sub, map_sum,
    map_smul] using ha x hx
