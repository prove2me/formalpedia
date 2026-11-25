-- Prove2me | solution 1 for GlobalTheory.DeformedSum.Series.series_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:52:54.332942+00:00
-- url     : https://prove2.me/submissions/4d18b7ef-3c1a-48a1-a54f-e6178e5e7a00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemIntegersOfMemHatO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DeformedProductDerivativeTermNormLeUniformStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasFDerivAtDeformedProductDerivativeTermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SeriesDifferentiable
import Theorems.Thm_GlobalTheory_CMVal_Conv_summable_norm_rpow
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_CMVal_out_mem_lattice
import Theorems.Thm_GlobalTheory_T_deformedProductDerivativeTerm_norm_le_uniform
import Theorems.Thm_GlobalTheory_T_hasFDerivAt_deformedProductDerivativeTerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
open GlobalTheory GlobalTheory.DeformedSum GlobalTheory.DeformedSum.Series
namespace GlobalTheory.DeformedSum.Series
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ), IsCMType φ → ∀ s : ℕ, 2 ≤ s → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ (m : I → ℕ) (z : I → ℂ), z ∈ polydisc I → Summable (fun q : modUnits (lattice c y) => dTerm φ (2 * s) m z q.1.out) ∧ DifferentiableAt ℂ (fun w : I → ℂ => ∑' q : modUnits (lattice c y), dTerm φ (2 * s) m w q.1.out) z ∧ ∀ i : I, HasLineDerivAt ℂ (fun w : I → ℂ => ∑' q : modUnits (lattice c y), dTerm φ (2 * s) m w q.1.out) (∑' q : modUnits (lattice c y), dTerm φ (2 * s) (m + Pi.single i 1) z q.1.out) z (Pi.single i 1) := by
  intro E _ _ _ I _ _ φ hφ s hs c y hc m z hz

  have hz1 : ‖z‖ < 1 := by
    rcases isEmpty_or_nonempty I with hI | hI
    · simp [Subsingleton.elim z 0]
    · exact (pi_norm_lt_iff one_pos).2 hz
  set r : ℝ := (‖z‖ + 1) / 2 with hr
  have hr1 : r < 1 := by rw [hr]; linarith
  have hzr : ‖z‖ < r := by rw [hr]; linarith
  set U : Set (I → ℂ) := Metric.ball 0 r with hU
  have hUo : IsOpen U := Metric.isOpen_ball
  have hUc : IsPreconnected U := (convex_ball (0 : I → ℂ) r).isPreconnected
  have hzU : z ∈ U := by simpa [hU] using hzr
  have hUle : ∀ w ∈ U, ∀ i, ‖w i‖ ≤ r := fun w hw i =>
    (norm_le_pi_norm w i).trans (show ‖w‖ < r by simpa [hU] using hw).le
  have hUpd : ∀ w ∈ U, w ∈ polydisc I := fun w hw i => lt_of_le_of_lt (hUle w hw i) hr1

  set N : modUnits (lattice c y) → ℝ := fun q => |(Algebra.norm ℚ (q.1.out : E) : ℝ)| ^ (-(s : ℝ)) with hN
  have hNs : Summable N := GlobalTheory.CMVal.Conv.summable_norm_rpow E c y (s : ℝ) hc (by exact_mod_cast (by omega : 1 < s))
  have hne : ∀ q : modUnits (lattice c y), q.1.out ≠ 0 := fun q => (out_mem_lattice q).2
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.deformedProductDerivativeTerm_norm_le_uniform E I φ hφ s m r hr1
  have hsum : ∀ w ∈ U, Summable (fun q : modUnits (lattice c y) => dTerm φ (2 * s) m w q.1.out) := fun w hw =>
    Summable.of_norm_bounded (hNs.mul_left C0) fun q => hC0 w (hUle w hw) _ (hne q)
  choose C hC using fun j : I => GlobalTheory.T.deformedProductDerivativeTerm_norm_le_uniform E I φ hφ s (m + Pi.single j 1) r hr1
  set f' : modUnits (lattice c y) → (I → ℂ) → ((I → ℂ) →L[ℂ] ℂ) := fun q w =>
    ∑ j, dTerm φ (2 * s) (m + Pi.single j 1) w q.1.out • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) j) with hf'
  set u : modUnits (lattice c y) → ℝ := fun q => ∑ j, C j * N q * ‖ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) j‖ with hu
  have hus : Summable u := summable_sum fun j _ => ((hNs.mul_left (C j)).mul_right _)
  have hder : ∀ q w, w ∈ U → HasFDerivAt (fun w : I → ℂ => dTerm φ (2 * s) m w q.1.out) (f' q w) w :=
    fun q w hw => GlobalTheory.T.hasFDerivAt_deformedProductDerivativeTerm E I φ (2 * s) m q.1.out (hne q) w (hUpd w hw)
  have hbd : ∀ q w, w ∈ U → ‖f' q w‖ ≤ u q := by
    intro q w hw
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hC j w (hUle w hw) _ (hne q)) (norm_nonneg _)
  have hF : HasFDerivAt (fun w : I → ℂ => ∑' q : modUnits (lattice c y), dTerm φ (2 * s) m w q.1.out)
      (∑' q, f' q z) z :=
    hasFDerivAt_tsum_of_isPreconnected hus hUo hUc hder hbd hzU (hsum z hzU) hzU
  refine ⟨hsum z hzU, hF.differentiableAt, fun i => ?_⟩
  have hL := hF.hasLineDerivAt (Pi.single i 1)
  have hcs : Summable (fun q => f' q z) := Summable.of_norm_bounded hus fun q => hbd q z hzU
  have hev : (∑' q, f' q z) (Pi.single i 1) = ∑' q : modUnits (lattice c y), dTerm φ (2 * s) (m + Pi.single i 1) z q.1.out := by
    have hm := (ContinuousLinearMap.apply ℂ ℂ (Pi.single i (1 : ℂ) : I → ℂ)).map_tsum hcs
    simp only [ContinuousLinearMap.apply_apply] at hm
    rw [hm]
    refine tsum_congr fun q => ?_
    simp [hf', ContinuousLinearMap.sum_apply, Pi.single_apply]
  rwa [hev] at hL
end GlobalTheory.DeformedSum.Series
