-- Prove2me | solution 1 for GlobalTheory.EndDivisible.mem_range_of_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:26:25.106487+00:00
-- url     : https://prove2.me/submissions/87785985-9b24-42e4-bd8e-68d7314bff51

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfLocalOnBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeOfSumEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.EndDivisible
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic TopologicalSpace
namespace GlobalTheory.EndDivisible
theorem _root_.solution {K R : Type} [Field K] [IsAlgClosed K] [CommRing R] [IsDomain R]
    (κ : K →+* R) {n : ℕ} (c : Fin n → K) (hc : c ≠ 0) (x : R) (h : ∑ k, κ (c k) * x ^ (k : ℕ) = 0) :
    x ∈ κ.range := by
  let p : Polynomial K := ∑ k : Fin n, Polynomial.monomial (k : ℕ) (c k)
  have hp : p ≠ 0 := fun h0 => hc (funext fun k => by
    have := congrArg (fun q => Polynomial.coeff q k) h0
    simp only [p, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Fin.val_inj,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Polynomial.coeff_zero] at this
    exact this)
  refine (IsAlgClosed.splits p).mem_range_of_isRoot hp ?_
  rw [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_finset_sum]
  simpa [Polynomial.eval₂_monomial] using h
end GlobalTheory.EndDivisible
