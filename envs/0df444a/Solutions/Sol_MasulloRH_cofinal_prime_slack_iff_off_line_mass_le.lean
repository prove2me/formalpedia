-- Prove2me | solution 1 for MasulloRH.cofinal_prime_slack_iff_off_line_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:26:51.256184+00:00
-- url     : https://prove2.me/submissions/1eba5465-41fc-4879-9f1f-114d3c7dd83f

-- New tolerance-by-tolerance relation between finite prime certificates and the off-line trace.
import Theorems.Thm_MasulloRH_off_line_mass_is_glb_of_finite_critical_line_deficits
import Theorems.Thm_MasulloRH_regularized_reference_mass_prime_series
import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
open MasulloRH ArithmeticFunction Set Filter Topology

theorem solution (τ : ℝ) :
    let f := fun j : ℕ => vonMangoldt j/(j:ℝ)^(5/2:ℝ) - vonMangoldt j/(j:ℝ)^(3:ℝ)
    let C := Real.log 2/2 + Real.pi/4 - 37/30
    let Z := {z : ZetaZerosInTraceStrip (1/2) // z.val.re = 1/2}
    let M := fun F : Finset Z => ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val.val:ℝ) *
      ((z.val.val.im^2-5)/(2*(z.val.val.im^2+25/4)*(z.val.val.im^2+4)))
    let D := ∑' z : {z : ZetaZerosInTraceStrip (1/2) // z.val.re ≠ 1/2},
      (zeroResolventTerm (1/2) 3 z.val).re
    D ≤ τ ↔ ∀ k : ℕ, ∃ N ≥ k, ∃ F : Finset Z,
      C + (∑ j ∈ Finset.range N,f j) ≤ M F + τ + 1/((k:ℝ)+1) := by
  classical
  let f := fun j : ℕ => vonMangoldt j/(j:ℝ)^(5/2:ℝ) - vonMangoldt j/(j:ℝ)^(3:ℝ)
  let C := Real.log 2/2 + Real.pi/4 - 37/30
  let Z := {z : ZetaZerosInTraceStrip (1/2) // z.val.re = 1/2}
  let M := fun F : Finset Z => ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val.val:ℝ) *
      ((z.val.val.im^2-5)/(2*(z.val.val.im^2+25/4)*(z.val.val.im^2+4)))
  let D := ∑' z : {z : ZetaZerosInTraceStrip (1/2) // z.val.re ≠ 1/2},
      (zeroResolventTerm (1/2) 3 z.val).re
  let P := C+∑' j,f j
  have hglb : IsGLB (Set.range (fun F => P-M F)) D := off_line_mass_is_glb_of_finite_critical_line_deficits
  have hs : Summable f := regularized_reference_mass_prime_series.summable
  have hf (j : ℕ) : 0 ≤ f j := by
    rcases eq_or_ne j 0 with rfl | hj
    · simp [f]
    have h1 : 1 ≤ (j:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
    apply sub_nonneg.mpr
    exact div_le_div_of_nonneg_left vonMangoldt_nonneg (Real.rpow_pos_of_pos (by linarith) _)
      (Real.rpow_le_rpow_of_exponent_le h1 (by norm_num))
  change D ≤ τ ↔ ∀ k : ℕ, ∃ N ≥ k, ∃ F : Finset Z,
      C + (∑ j ∈ Finset.range N,f j) ≤ M F + τ + 1/((k:ℝ)+1)
  constructor
  · intro h k
    have hm : ∃ F : Finset Z, P-M F < τ+1/((k:ℝ)+1) := by
      by_contra! hbad
      have hh : τ+1/((k:ℝ)+1) ≤ D := hglb.2 (by rintro _ ⟨F,rfl⟩; exact hbad F)
      linarith [show (0:ℝ) < 1/((k:ℝ)+1) by positivity]
    obtain ⟨F,hF⟩ := hm
    refine ⟨k,le_rfl,F,?_⟩
    have hp := hs.sum_le_tsum (Finset.range k) (fun j _ => hf j)
    dsimp only [P] at hF
    linarith
  · intro hall
    choose N hN F hF using hall
    have ht : Tendsto N atTop atTop := tendsto_atTop_mono hN tendsto_id
    have hpartial := hs.hasSum.tendsto_sum_nat.comp ht
    have hz : Tendsto (fun k : ℕ => 1/((k:ℝ)+1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim : Tendsto (fun k : ℕ =>
        τ + 1/((k:ℝ)+1) + ((∑' j,f j)-(∑ j ∈ Finset.range (N k),f j))) atTop (𝓝 τ) := by
      simpa using ((tendsto_const_nhds (x:=τ)).add hz).add
        ((tendsto_const_nhds (x:=∑' j,f j)).sub hpartial)
    apply ge_of_tendsto' hlim
    intro k
    have hd := hglb.1 (Set.mem_range_self (F k))
    change D ≤ C + (∑' j,f j) - M (F k) at hd
    linarith only [hd,hF k]
