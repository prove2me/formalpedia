-- Prove2me | solution 1 for GlobalTheory.FiniteCoverGrowth.exists_map_eq_of_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:07:53.614892+00:00
-- url     : https://prove2.me/submissions/f0734ada-6247-4330-a3f8-220cd99a739e

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IntegralAndRationalOfPolynomialGrowth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.FiniteCoverGrowth
namespace GlobalTheory.FiniteCoverGrowth
theorem _root_.solution {d N : ℕ} (U : Set (Fin d → ℂ)) (S : (Fin d → ℂ) → Polynomial ℂ)
    (hdeg : ∀ x ∈ U, (S x).degree < N)
    (hev : ∀ t : ℂ, ∃ g : MvPolynomial (Fin d) ℂ, ∀ x ∈ U, (S x).eval t = MvPolynomial.eval x g) :
    ∃ s : Polynomial (MvPolynomial (Fin d) ℂ), s.degree < N ∧
      ∀ x ∈ U, s.map (MvPolynomial.eval x) = S x := by
  classical
  choose g hg using hev
  have hinj : Set.InjOn (fun i : ℕ => (i : ℂ)) (Finset.range N) :=
    fun a _ b _ h => Nat.cast_injective (R := ℂ) h
  refine ⟨∑ i ∈ Finset.range N, Polynomial.C (g i) *
    (Lagrange.basis (Finset.range N) (fun i : ℕ => (i : ℂ)) i).map MvPolynomial.C, ?_, ?_⟩
  · refine (Polynomial.degree_sum_le _ _).trans_lt ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro i hi
    rw [← Polynomial.smul_eq_C_mul]
    refine (Polynomial.degree_smul_le _ _).trans_lt (Polynomial.degree_map_le.trans_lt ?_)
    rw [Lagrange.degree_basis hinj hi, Finset.card_range]
    have := Finset.mem_range.1 hi
    exact_mod_cast (by omega : N - 1 < N)
  · intro x hx
    rw [Lagrange.eq_interpolate (f := S x) hinj (by simpa using hdeg x hx),
      Lagrange.interpolate_apply, Polynomial.map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map, hg _ x hx]
    congr 1
    have : (MvPolynomial.eval x).comp (MvPolynomial.C : ℂ →+* MvPolynomial (Fin d) ℂ) =
        RingHom.id ℂ := by ext; simp
    rw [this, Polynomial.map_id]
end GlobalTheory.FiniteCoverGrowth
