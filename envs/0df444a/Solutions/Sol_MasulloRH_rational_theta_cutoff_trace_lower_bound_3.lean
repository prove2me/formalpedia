-- Prove2me | solution 3 for MasulloRH.rational_theta_cutoff_trace_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:29:18.919352+00:00
-- url     : https://prove2.me/submissions/543c142b-d121-4845-99ad-1fe00bb8d7bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- New frontier proof-sketch. The cofinal approximate prime witnesses remain open.
import Theorems.Thm_MasulloRH_theta_cutoff_tolerance_iff_finite_prime_certificates
import Theorems.Thm_MasulloRH_cofinal_approximate_prime_mass_certificates
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
