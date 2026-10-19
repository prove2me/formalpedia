-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_forward_residual_entropy_of_closure_sequence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/6403051e-72a6-4947-b654-7761bb4452cf

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_compactified_residual_of_closure_sequence
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactified_entropy_limit_eq_residual_sub_logb

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r : ℕ} {s R : ℝ}
    (u : ℕ → ℝ)
    (a : ℕ → Fin (r + 1) → ℝ)
    (b : ℕ → Fin r → ℝ)
    (hu : Tendsto u atTop (nhds s))
    (hinter : ∀ n, Interlacing (a n) (b n))
    (hgap : ∀ n, u n < 2 * Gamma (a n) (b n))
    (hPhi : ∀ n, Phi (a n) (b n) ≤ R + 1 / ((n : ℝ) + 1)) :
    ∃ (L : ℝ) (A : Fin (r + 1) → ℝ) (B : Fin r → ℝ)
      (d : Fin r → ℝ) (φ : ℕ → ℕ)
      (k j : ℕ) (hkj : k + j = r)
      (q : ℕ) (a₀ : Fin (q + 1) → ℝ) (b₀ : Fin q → ℝ)
      (c : ℝ),
      StrictMono φ ∧
      0 ≤ L ∧ L ≤ R ∧
      (∀ i, A i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, B i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, Tendsto
        (fun n => compactifiedHierarchyCoordinate (a (φ n) i))
        atTop (nhds (A i))) ∧
      (∀ i, Tendsto
        (fun n => compactifiedHierarchyCoordinate (b (φ n) i))
        atTop (nhds (B i))) ∧
      Tendsto (fun n => u (φ n)) atTop (nhds s) ∧
      (∀ n, u (φ n) < 2 * Gamma (a (φ n)) (b (φ n))) ∧
      Tendsto (fun n => Phi (a (φ n)) (b (φ n))) atTop (nhds L) ∧
      (∀ i, d i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, Tendsto
        (fun n => b (φ n) i / a (φ n) i.castSucc)
        atTop (nhds (d i))) ∧
      (∀ i : Fin r, A i.castSucc = 0 ↔ B i = 0) ∧
      (∀ i : Fin r, A i.castSucc = 0 →
        0 < d i ∧
        Tendsto
          (fun n => quadraticCoordinate (b (φ n) i) /
            quadraticCoordinate (a (φ n) i.castSucc))
          atTop (nhds (d i ^ 2))) ∧
      q ≤ j ∧ Interlacing a₀ b₀ ∧
      (∀ i : Fin r, i.val < k → A i.castSucc = 0 ∧ B i = 0) ∧
      (∀ i : Fin r, A i.castSucc = 0 ↔ i.val < k) ∧
      (∀ i, compactifiedAmbientSuffix hkj A i ∈ Set.Ioc (0 : ℝ) 1) ∧
      (∀ i, compactifiedStabilizerSuffix hkj B i ∈ Set.Ioc (0 : ℝ) 1) ∧
      (∀ i : Fin j,
        compactifiedAmbientSuffix hkj A i.castSucc ≤
          compactifiedStabilizerSuffix hkj B i ∧
        compactifiedStabilizerSuffix hkj B i ≤
          compactifiedAmbientSuffix hkj A i.succ) ∧
      Phi a₀ b₀ =
        Phi (fun i => (compactifiedAmbientSuffix hkj A i)⁻¹ - 1)
          (fun i => (compactifiedStabilizerSuffix hkj B i)⁻¹ - 1) ∧
      (∀ t : ℝ, 0 < t →
        hierarchyStieltjesRatio
          (fun i => (compactifiedAmbientSuffix hkj A i)⁻¹ - 1)
          (fun i => (compactifiedStabilizerSuffix hkj B i)⁻¹ - 1) t =
            hierarchyStieltjesRatio a₀ b₀ t) ∧
      c = ∏ i ∈ Finset.univ.filter (fun i : Fin r => i.val < k), d i ∧
      0 < c ∧ c ≤ 1 ∧ (c < 1 → q < r) ∧
      L = Phi a₀ b₀ - Real.logb 2 c := by
  obtain ⟨L, A, B, d, φ, k, j, hkj, q, a₀, b₀, c,
      hφ, hLnonneg, hLR, hA, hB, hAlim, hBlim, hulim, hgaplim,
      hLlim, hd, hratio, hpaired, hescape, hq, hresidual,
      hprefix, hzero, hpositiveA, hpositiveB, hweakSuffix,
      hresidualPhi, hstieltjes, hc, hcpos, hcle, hdrop⟩ :=
    exists_compactified_residual_of_closure_sequence
      u a b hu hinter hgap hPhi
  have hbound : ∀ n, Phi (a n) (b n) ≤ R + 1 := by
    intro n
    refine (hPhi n).trans ?_
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hden : 0 < (n : ℝ) + 1 := by linarith
    have hfrac : 1 / ((n : ℝ) + 1) ≤ (1 : ℝ) :=
      (div_le_one hden).2 (by linarith)
    linarith
  have hlast : 0 < A (Fin.last r) := by
    have h := (hpositiveA (Fin.last j)).1
    have hindex :
        compactifiedAmbientSuffix hkj A (Fin.last j) = A (Fin.last r) := by
      unfold compactifiedAmbientSuffix
      congr 1
      apply Fin.ext
      simp only [Fin.val_last]
      exact hkj
    rw [hindex] at h
    exact h
  have hdprefix : ∀ i : Fin r, i.val < k → 0 < d i := by
    intro i hi
    exact (hescape i ((hzero i).mpr hi)).1
  have hentropy : L = Phi a₀ b₀ - Real.logb 2 c :=
    compactified_entropy_limit_eq_residual_sub_logb hkj a₀ b₀
      hinter hbound hAlim hBlim (fun i => (hA i).1)
      (fun i => (hB i).1) hlast hratio hzero hdprefix
      hLlim hresidualPhi hc
  exact ⟨L, A, B, d, φ, k, j, hkj, q, a₀, b₀, c,
    hφ, hLnonneg, hLR, hA, hB, hAlim, hBlim, hulim, hgaplim,
    hLlim, hd, hratio, hpaired, hescape, hq, hresidual,
    hprefix, hzero, hpositiveA, hpositiveB, hweakSuffix,
    hresidualPhi, hstieltjes, hc, hcpos, hcle, hdrop, hentropy⟩
end MetricCodes.Spherical.HigherHierarchy
