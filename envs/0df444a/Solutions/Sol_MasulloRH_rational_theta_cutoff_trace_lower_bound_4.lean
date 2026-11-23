-- Prove2me | solution 4 for MasulloRH.rational_theta_cutoff_trace_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:33:53.094322+00:00
-- url     : https://prove2.me/submissions/0d6fc287-38e0-4335-b382-f1d9fd5fa776
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_MasulloRH_riemannHypothesis_iff_cofinal_approximate_prime_mass_certificates
import Theorems.Thm_MasulloRH_theta_cutoff_tolerance_iff_finite_prime_certificates

-- Step 1: `mathlib_riemannHypothesis` implies `MasulloRH.cofinal_approximate_prime_mass_certificates` (accepted reduction of `MasulloRH.cofinal_approximate_prime_mass_certificates`).
section

open ArithmeticFunction MasulloRH Finset

theorem MasulloRH.cofinal_approximate_prime_mass_certificates :
    let P := fun N : ℕ => Real.log 2/2 + Real.pi/4 - 37/30 +
      ∑ j ∈ Finset.range N, (vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ))
    let M := fun F : Finset (ZetaZerosInTraceStrip (1/2)) =>
      ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
        ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4)))
    ∀ k : ℕ, ∃ N ≥ k, ∃ F : Finset (ZetaZerosInTraceStrip (1/2)), (∀ z ∈ F, z.val.re = 1/2) ∧ P N ≤ M F + 1/((k:ℝ)+1) :=
  Iff.mp MasulloRH.riemannHypothesis_iff_cofinal_approximate_prime_mass_certificates
    mathlib_riemannHypothesis

end

-- Step 2: `MasulloRH.cofinal_approximate_prime_mass_certificates` implies `MasulloRH.rational_theta_cutoff_trace_lower_bound` (accepted reduction of `MasulloRH.rational_theta_cutoff_trace_lower_bound`).
section

-- New frontier proof-sketch. The cofinal approximate prime witnesses remain open.


open MasulloRH MasulloGRH ArithmeticFunction

theorem solution :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ T : rationalThetaAnnihilator ((n:ℝ)+1) →L[ℂ] rationalThetaAnnihilator ((n:ℝ)+1),
        IsRationalThetaConvolution ((n:ℝ)+1) (regularizedTraceTest n 3) T →
          (cutoffPolar n 3 - (cutoffArch n 3 + cutoffPrime n 3)).re ≤
            (operatorTrace T).re + ε := by
  classical
  apply (theta_cutoff_tolerance_iff_finite_prime_certificates 0).mpr
  intro k
  obtain ⟨N,hN,F,hF,h⟩ := cofinal_approximate_prime_mass_certificates k
  let Z := ZetaZerosInTraceStrip (1/2)
  let line := {z : Z // z.val.re = 1/2}
  let e : {z : Z // z ∈ F} ↪ line :=
    ⟨fun z => ⟨z.val,hF z.val z.property⟩,fun x y h => Subtype.ext (congrArg (fun z : line => z.val) h)⟩
  let K (z : Z) := (analyticOrderNatAt riemannZeta z.val:ℝ) *
        ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4)))
  refine ⟨N,hN,F.attach.map e,?_⟩
  change _ ≤ (∑ z ∈ F.attach.map e,K z.val) + 0 + _
  rw [add_zero,Finset.sum_map]
  change _ ≤ (∑ z ∈ F.attach,K z.val) + _
  rw [Finset.sum_attach]
  exact h

end
