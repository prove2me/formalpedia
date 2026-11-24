-- Prove2me | solution 1 for GlobalTheory.SW.HermLat.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:27:20.545804+00:00
-- url     : https://prove2.me/submissions/19e5985b-d5e5-4a4b-8612-4677319c4fc9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsIntegralBasisHermitianMatricesDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HermLat
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [IsCMField E]
namespace GlobalTheory.SW.HermLat
theorem _root_.solution {ι : Type} [Fintype ι] {N : ℕ} (X : ι → Matrix (Fin N) (Fin N) E) :
    ∃ c : ℕ, 0 < c ∧ ∀ i, IntM ((c : E) • X i) := by
  have h : ∀ p : ι × Fin N × Fin N, ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * X p.1 p.2.1 p.2.2) := by
    intro p
    have ha : IsAlgebraic ℤ (X p.1 p.2.1 p.2.2) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic _)
    obtain ⟨d, hd, hi⟩ := ha.exists_integral_multiple
    refine ⟨d.natAbs, Int.natAbs_pos.2 hd, ?_⟩
    rw [zsmul_eq_mul] at hi
    rcases Int.natAbs_eq d with e | e
    · rw [e] at hi; simpa using hi
    · rw [e] at hi; simpa using hi.neg
  choose d hd hi using h
  refine ⟨∏ p, d p, Finset.prod_pos fun p _ => hd p, fun i a b => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (i, a, b)), Matrix.smul_apply, smul_eq_mul,
    Nat.cast_mul, mul_assoc]
  refine IsIntegral.mul ?_ (hi (i, a, b))
  simpa using isIntegral_algebraMap (R := ℤ) (A := E)
    (x := ((∏ p ∈ Finset.univ.erase (i, a, b), d p : ℕ) : ℤ))
end GlobalTheory.SW.HermLat
