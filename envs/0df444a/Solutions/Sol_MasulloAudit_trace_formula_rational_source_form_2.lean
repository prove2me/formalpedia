-- Prove2me | solution 2 for MasulloAudit.trace_formula_rational_source_form
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:20:44.789876+00:00
-- url     : https://prove2.me/submissions/560b3302-065a-4b52-8209-56686b10009e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloRH_RationalTrace
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_MasulloRH_trace_formula_rational_iff_RH
import Theorems.Thm_MasulloAudit_geometric_side_eq_formal_lhs

set_option autoImplicit false
open MeasureTheory Set
open scoped Topology

namespace MasulloAudit
end MasulloAudit
open MasulloAudit

open MasulloRH

/-- Each `p : Nat.Primes` gives the `Fact` needed to form `ℚ_[p]`. -/
local instance factPrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- Masullo, Theorem 12.5.1.1 (ζ case, `K = ℚ`), in its source form (12.5.1.1)–(12.5.1.3).
For every window `α > 0`, every norm-invariant test `φ(g) = ϕ(|g|_v)` with `ϕ` an admissible
rational trace test, and every family of Borel measurable structures and additive Haar measures
`μ_p` on the `ℚ_[p]`, with local multiplicative measures `μ_∞ = dx/|x|` on `ℝ^×` and
`μ_p = dμ_p/|g|_p` on `ℚ_p^×` (so `μ_p^×(ℤ_p^×) = μ_p {‖g‖ = 1}`):
the real-place and every `p`-adic local integral converge absolutely, the family of prime-place
terms is summable, the spectral family `zetaTraceTerm ϕ α` is summable, and

`½ ∫_{ℝ^×} φ |g|^{1/2}/|1-g| d^×g + Σ_p (log p / μ_p^×(ℤ_p^×)) ∫_{ℚ_p^×} φ |g|_p^{1/2}/|1-g|_p d^×g
  = M ϕ(1/2) + M ϕ(-1/2) - Σ_{ρ, |Re ρ - 1/2| < α} ord_ρ ζ · M ϕ(ρ - 1/2)`,

with the zero-sum convention of `MasulloRH.trace_formula_rational`. -/
theorem solution (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ)
    (hφ : IsRationalTraceTest φ)
    (inst : ∀ p : Nat.Primes, MeasurableSpace ℚ_[p])
    [hB : ∀ p : Nat.Primes, BorelSpace ℚ_[p]]
    (μ : ∀ p : Nat.Primes, Measure ℚ_[p]) [hμ : ∀ p : Nat.Primes, (μ p).IsAddHaarMeasure] :
    IntegrableOn (fun x : ℝ => φ |x| * ((|x| ^ (1/2 : ℝ) / |1 - x| * (1 / |x|) : ℝ) : ℂ))
        {x : ℝ | x ≠ 0} ∧
    (∀ p : Nat.Primes,
      IntegrableOn (fun g : ℚ_[p] => φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ))
        {g : ℚ_[p] | g ≠ 0} (μ p)) ∧
    Summable (fun p : Nat.Primes =>
      ((Real.log p / (μ p).real {g : ℚ_[p] | ‖g‖ = 1} : ℝ) : ℂ) *
        ∫ g in {g : ℚ_[p] | g ≠ 0},
          φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ) ∂(μ p)) ∧
    Summable (zetaTraceTerm φ α) ∧
    (1/2 : ℂ) * (∫ x in {x : ℝ | x ≠ 0},
        φ |x| * ((|x| ^ (1/2 : ℝ) / |1 - x| * (1 / |x|) : ℝ) : ℂ)) +
      ∑' p : Nat.Primes,
        ((Real.log p / (μ p).real {g : ℚ_[p] | ‖g‖ = 1} : ℝ) : ℂ) *
          ∫ g in {g : ℚ_[p] | g ≠ 0},
            φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ) ∂(μ p) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ :=
  by
  obtain ⟨hReal, hPadic, _, hPrime, _, hGeom⟩ :=
    MasulloAudit.geometric_side_eq_formal_lhs φ hφ inst μ
  obtain ⟨_, _, hSpectral, hTrace⟩ :=
    MasulloRH.trace_formula_rational_iff_RH.mpr mathlib_riemannHypothesis α hα φ hφ
  exact ⟨hReal, hPadic, hPrime, hSpectral, hGeom.trans hTrace⟩
