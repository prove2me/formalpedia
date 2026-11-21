-- Prove2me | solution 5 for MasulloRH.spectral_trace_hasSum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:44:57.500659+00:00
-- url     : https://prove2.me/submissions/7268c7e3-11ff-4d80-a075-86f1aa552b36
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_regularized_mellin_limit
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_MasulloRH_regularized_spectral_domination_any_window
import Theorems.Thm_MasulloRH_trace_window_comparison
import Theorems.Thm_MasulloRH_regularized_test_admissible
import Theorems.Thm_MasulloRH_single_resolvent_test
import Mathlib.Analysis.Normed.Group.Tannery
import Theorems.Thm_MasulloRH_regular_width_one_sided_trace
import Theorems.Thm_MasulloRH_window_trace_boundary_limits
import Theorems.Thm_MasulloRH_trace_formula_rational_full_strip
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Topology.Algebra.Module.Cardinality

open MasulloRH MeasureTheory Filter Set Topology

noncomputable section

private abbrev Z := ZetaZerosInTraceStrip (1/2)
private def distLine (ρ : Z) : ℝ := |(ρ:ℂ).re - 1/2|

private def windowEquiv (α : ℝ) :
    {ρ : Z // distLine ρ < α} ≃ ZetaZerosInTraceStrip α where
  toFun x := ⟨x.val.val,x.val.property.1,x.val.property.2.1,x.val.property.2.2.1,x.property⟩
  invFun x := ⟨⟨x.val,x.property.1,x.property.2.1,x.property.2.2.1,
    abs_lt.mpr ⟨by linarith [x.property.2.1],by linarith [x.property.2.2.1]⟩⟩,x.property.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem window_tsum (α : ℝ) (φ : ℝ → ℂ) :
    (∑' ρ : Z, if distLine ρ < α then zetaTraceTerm φ (1/2) ρ else 0) =
      ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by
  let S := {ρ : Z | distLine ρ < α}
  change (∑' ρ : Z, S.indicator (zetaTraceTerm φ (1/2)) ρ) = _
  rw [←tsum_subtype]
  exact (windowEquiv α).tsum_eq (zetaTraceTerm φ α)


private theorem regular_widths {α : ℝ} (hα : 0 < α) :
    ∃ b : ℕ → ℝ, (∀ n, 0 < b n) ∧ (∀ n, b n < α) ∧
      (∀ n ρ, distLine ρ ≠ b n) ∧ Tendsto b atTop (𝓝 α) := by
  have : DiscreteTopology riemannZetaZeros := isDiscrete_iff_discreteTopology.mp isDiscrete_riemannZetaZeros
  have : Countable riemannZetaZeros := countable_of_Lindelof_of_discrete
  have : Countable Z := Function.Injective.countable (f := fun z : Z => (⟨z.val,z.prop.1⟩ : riemannZetaZeros))
    (fun _ _ h => Subtype.ext (congrArg (Subtype.val : riemannZetaZeros → ℂ) h))
  have hd := Set.Countable.dense_compl ℝ (Set.countable_range distLine)
  have hw (n : ℕ) := hd.exists_mem_open (isOpen_Ioo (a := max (α/2) (α - 1/(n+1:ℝ))) (b := α))
    (Set.nonempty_Ioo.mpr (by apply max_lt <;> first | linarith | exact sub_lt_self _ (by positivity)))
  choose b hreg hbound using hw
  refine ⟨b, fun n => (show 0 < α/2 by linarith).trans_le ((le_max_left _ _).trans (hbound n).1.le),
    fun n => (hbound n).2,fun n ρ h => hreg n ⟨ρ,h⟩,?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (h := fun _ : ℕ => α) (g := fun n : ℕ => α - 1/(n+1:ℝ))
  · simpa using (tendsto_const_nhds (x := α)).sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · exact tendsto_const_nhds
  · exact fun n => (le_max_right _ _).trans (hbound n).1.le
  · exact fun n => (hbound n).2.le

-- The cutoff limit is adapted from the accepted full-strip proof and the cutoff
-- arguments of davidloeffler (see the submission explanation for attribution).
/-- Uniform summable domination allows passage through the full zero sum. -/
private theorem spectralLimit (α : ℝ) (hα : 0 < α)
    (s : ℂ) (hs : (3 / 2 : ℝ) < s.re) :
    Tendsto (fun n : ℕ => cutoffSpectral α n s) atTop
      (𝓝 (regularizedSpectral α s)) := by
  obtain ⟨C, hC, hbound⟩ := regularized_spectral_domination_any_window α s hs
  apply tendsto_tsum_of_dominated_convergence
    ((weighted_zero_summability α hα).mul_left C)
  · intro ρ
    have hr : (ρ : ℂ).re < 1 := ρ.property.2.2.1
    have hwr : ((ρ : ℂ) - 1 / 2).re = (ρ : ℂ).re - 1 / 2 := by simp
    have hm := regularized_mellin_limit s ((ρ : ℂ) - 1 / 2)
      (by rw [hwr]; linarith) (by rw [hwr]; linarith)
    convert hm.const_mul (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) using 1 <;>
      simp only [zetaTraceTerm, zeroResolventTerm] <;> (congr 3; try ring) <;> congr 1 <;> ring
  · exact .of_forall hbound

private theorem cutoff_above (n : ℕ) (s : ℂ) :
    tsupport (regularizedTraceTest n s) ⊆ Ioi 1 := by
  let a := Real.exp (1/(n+1:ℝ))
  have ha : 1 < a := Real.one_lt_exp_iff.mpr (by positivity)
  have hsup : Function.support (regularizedTraceTest n s) ⊆ Ici a := by
    intro x hx
    by_contra! h
    have hxa : x < a := lt_of_not_ge h
    apply hx
    by_cases h1 : 1 < x
    · have hl : Real.log x < 1/(n+1:ℝ) := (Real.log_lt_iff_lt_exp (by linarith)).mpr hxa
      have h0 : (n+1:ℝ)*Real.log x-1 ≤ 0 := by
        have hmul := (lt_div_iff₀ (by positivity : 0 < (n+1:ℝ))).mp hl
        linarith
      simp [regularizedTraceTest,traceLogCutoff,h1,Real.smoothTransition.zero_of_nonpos h0]
    · simp [regularizedTraceTest,h1]
  exact (closure_minimal hsup isClosed_Ici).trans (fun x hx => lt_of_lt_of_le ha hx)

private theorem one_sided_eq (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ)
    (hφ : IsRationalTraceTest φ) (hp : tsupport φ ⊆ Ioi 1) :
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) + (∑' i, primePowerTraceTerm φ i) =
    mellin φ (1/2) + mellin φ (-1/2) - ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by
  obtain ⟨b,hpos,hbelow,hreg,hlim⟩ := regular_widths hα
  have hleft := (window_trace_boundary_limits α b hlim (fun _ => 0) φ hφ).1 hbelow
  let P := mellin φ (1/2) + mellin φ (-1/2)
  let G := (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) + (∑' i, primePowerTraceTerm φ i)
  have hval (n : ℕ) : (∑' ρ : Z, if distLine ρ < b n then zetaTraceTerm φ (1/2) ρ else 0) = P-G := by
    rw [window_tsum]
    have hh := regular_width_one_sided_trace (b n) (hpos n) (hreg n) φ hφ hp
    change G = P - _ at hh
    linear_combination hh
  have hc : Tendsto (fun n : ℕ => ∑' ρ : Z, if distLine ρ < b n then zetaTraceTerm φ (1/2) ρ else 0)
      atTop (𝓝 (P-G)) := tendsto_const_nhds.congr fun n => (hval n).symm
  have hs : Tendsto (fun n : ℕ => ∑' ρ : Z, if distLine ρ < b n then zetaTraceTerm φ (1/2) ρ else 0)
      atTop (𝓝 (∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ)) := by
    apply hleft.congr
    intro n
    apply tsum_congr
    intro ρ
    by_cases hl : |ρ.val.re - 1/2| < b n
    · simp only [hl, if_true, distLine]
    · simp [distLine, hl, hreg n ρ]
  have hh := tendsto_nhds_unique hs hc
  change G = P - _
  linear_combination hh

theorem solution (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    HasSum (zetaTraceTerm φ α) ((mellin φ (1/2) + mellin φ (-1/2)) -
      ((∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) + ∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i)) := by
  have hcut (n : ℕ) : cutoffSpectral α n 3 = cutoffSpectral (1/2) n 3 := by
    let f := regularizedTraceTest n 3
    have hf := regularized_test_admissible n 3
    have hA := one_sided_eq α hα f hf (cutoff_above n 3)
    have hB := (trace_formula_rational_full_strip f hf).2.2.2
    change (∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm f α ρ) = ∑' ρ : Z, zetaTraceTerm f (1/2) ρ
    linear_combination hA - hB
  have hres := tendsto_nhds_unique (spectralLimit α hα 3 (by norm_num))
    ((spectralLimit (1/2) (by norm_num) 3 (by norm_num)).congr (fun n => (hcut n).symm))
  have hz := (single_resolvent_test α).mp (by simp [regularizedTraceRHS,hres])
  have hsum : (∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ) = ∑' ρ : Z, zetaTraceTerm φ (1/2) ρ := by
    rw [←window_tsum]
    exact tsum_congr fun ρ => if_pos (hz ρ)
  have hf := (trace_formula_rational_full_strip φ hφ).2.2.2
  have he := (trace_window_comparison α φ hφ).2.2.1.hasSum
  convert he using 1
  linear_combination -hf - hsum
