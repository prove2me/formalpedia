-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_compactified_residual_of_closure_sequence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/689dbeea-acbd-40c1-a545-c54696eff958

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_atTop_of_compactifiedHierarchyCoordinate_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_compactified_bounded_hierarchy_subsequence
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_WeakInterlacing_ambient_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_strict_residual_of_weak_interlacing
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_paired_infinity_iff
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactifiedAmbient_monotone_of_weak_interlacing
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_positive_compactified_suffix
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactified_finite_suffix_weak_interlacing
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_compactified_paired_ratio_subsequence

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
open Set Filter Topology
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
      0 < c ∧ c ≤ 1 ∧ (c < 1 → q < r) := by
  have hbound : ∀ n, Phi (a n) (b n) ≤ R + 1 := by
    intro n
    refine (hPhi n).trans ?_
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hden : 0 < (n : ℝ) + 1 := by linarith
    have hfrac : 1 / ((n : ℝ) + 1) ≤ (1 : ℝ) :=
      (div_le_one hden).2 (by linarith)
    linarith
  obtain ⟨L, A, B, ψ, hψ, hL, hA, hB, hAψ, hBψ,
      hweak, hlast, hLψ⟩ :=
    exists_compactified_bounded_hierarchy_subsequence a b hinter hbound
  let aψ : ℕ → Fin (r + 1) → ℝ := fun n => a (ψ n)
  let bψ : ℕ → Fin r → ℝ := fun n => b (ψ n)
  obtain ⟨d, χ, hχ, hd, hdχ, hdpos, hdquadratic⟩ :=
    exists_compactified_paired_ratio_subsequence aψ bψ
      (fun n => hinter (ψ n)) (fun n => hbound (ψ n))
  let φ : ℕ → ℕ := ψ ∘ χ
  have hφ : StrictMono φ := hψ.comp hχ
  have hAφ : ∀ i, Tendsto
      (fun n => compactifiedHierarchyCoordinate (a (φ n) i))
      atTop (nhds (A i)) := by
    intro i
    exact (hAψ i).comp hχ.tendsto_atTop
  have hBφ : ∀ i, Tendsto
      (fun n => compactifiedHierarchyCoordinate (b (φ n) i))
      atTop (nhds (B i)) := by
    intro i
    exact (hBψ i).comp hχ.tendsto_atTop
  have hLφ : Tendsto (fun n => Phi (a (φ n)) (b (φ n)))
      atTop (nhds L) := by
    exact hLψ.comp hχ.tendsto_atTop
  have hpaired : ∀ i : Fin r, A i.castSucc = 0 ↔ B i = 0 :=
    paired_infinity_iff hinter hbound hAφ hBφ
      (fun i => (hA i).1) (fun i => (hB i).1)
  obtain ⟨k, j, hkj, hprefix, hpositiveA, hpositiveB, hweakSuffix⟩ :=
    exists_positive_compactified_suffix
      A B hA hB hweak hpaired hlast
  obtain ⟨q, a₀, b₀, hq, hresidual, hresidualPhi, hstieltjes⟩ :=
    exists_strict_residual_of_weak_interlacing
      (compactified_finite_suffix_weak_interlacing
        hkj A B hpositiveA hpositiveB hweakSuffix)
  have hzero : ∀ i : Fin r, A i.castSucc = 0 ↔ i.val < k := by
    intro i
    constructor
    · intro hi
      by_contra hnot
      have hki : k ≤ i.val := Nat.le_of_not_gt hnot
      let i₀ : Fin (r + 1) := ⟨k, by omega⟩
      have hpositive : 0 < A i₀ := by
        simpa [compactifiedAmbientSuffix, i₀] using
          (hpositiveA (0 : Fin (j + 1))).1
      have hle : i₀ ≤ i.castSucc := Fin.mk_le_mk.mpr hki
      exact (ne_of_gt
        (hpositive.trans_le
          (compactifiedAmbient_monotone_of_weak_interlacing hweak hle))) hi
    · intro hi
      exact (hprefix i hi).1
  have hratio : ∀ i, Tendsto
      (fun n => b (φ n) i / a (φ n) i.castSucc)
      atTop (nhds (d i)) := by
    intro i
    simpa [φ, aψ, bψ, Function.comp_apply] using hdχ i
  have hescape : ∀ i : Fin r, A i.castSucc = 0 →
      0 < d i ∧
        Tendsto (fun n => quadraticCoordinate (b (φ n) i) /
          quadraticCoordinate (a (φ n) i.castSucc))
          atTop (nhds (d i ^ 2)) := by
    intro i hi
    have hatop : Tendsto (fun n => a (φ n) i.castSucc)
        atTop atTop :=
      tendsto_atTop_of_compactifiedHierarchyCoordinate_zero
        (fun n => (hinter (φ n)).ambient_nonneg i.castSucc)
        (hi ▸ hAφ i.castSucc)
    have hatop' : Tendsto (fun n => aψ (χ n) i.castSucc)
        atTop atTop := by
      simpa [aψ, φ, Function.comp_apply] using hatop
    exact ⟨hdpos i hatop', by
      simpa [aψ, bψ, φ, Function.comp_apply] using
        hdquadratic i hatop'⟩
  let c : ℝ := ∏ i ∈ Finset.univ.filter
    (fun i : Fin r => i.val < k), d i
  have hcpos : 0 < c := by
    dsimp [c]
    apply Finset.prod_pos
    intro i hi
    exact (hescape i (hprefix i (Finset.mem_filter.mp hi).2).1).1
  have hcle : c ≤ 1 := by
    dsimp [c]
    apply Finset.prod_le_one
    · intro i _
      exact (hd i).1
    · intro i _
      exact (hd i).2
  have hdrop : c < 1 → q < r := by
    intro hc
    have hk : 0 < k := by
      by_contra hnot
      have hkzero : k = 0 := Nat.eq_zero_of_not_pos hnot
      have hcunit : c = 1 := by
        simp [c, hkzero]
      linarith
    omega
  have herror : Tendsto
      (fun n : ℕ => R + 1 / ((n : ℝ) + 1)) atTop (nhds R) := by
    simpa using
      (tendsto_const_nhds (x := R)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have herrorsub : Tendsto
      (fun n : ℕ => R + 1 / (((φ n : ℕ) : ℝ) + 1))
      atTop (nhds R) := by
    exact herror.comp hφ.tendsto_atTop
  have hdiff : Tendsto
      (fun n : ℕ =>
        Phi (a (φ n)) (b (φ n)) -
          (R + 1 / (((φ n : ℕ) : ℝ) + 1)))
      atTop (nhds (L - R)) := hLφ.sub herrorsub
  have hLR : L ≤ R := by
    have hle : L - R ≤ 0 := le_of_tendsto hdiff
      (Filter.Eventually.of_forall fun n => sub_nonpos.mpr (hPhi (φ n)))
    linarith
  refine ⟨L, A, B, d, φ, k, j, hkj, q, a₀, b₀, c,
    hφ, hL.1, hLR, hA, hB, hAφ, hBφ, ?_, ?_, hLφ,
    hd, hratio, hpaired, hescape, hq, hresidual,
    hprefix, hzero, hpositiveA, hpositiveB, hweakSuffix,
    hresidualPhi, hstieltjes, rfl, hcpos, hcle, hdrop⟩
  · exact hu.comp hφ.tendsto_atTop
  · intro n
    exact hgap (φ n)
end MetricCodes.Spherical.HigherHierarchy
