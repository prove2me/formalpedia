-- Prove2me | solution 1 for GlobalTheory.HtVal.val_eq_zero_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:37:24.192824+00:00
-- url     : https://prove2.me/submissions/6747c97b-621f-454e-add9-620b1d7213c7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_MemRangeOfForallHeightOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocalizationAtPrimeIsDiscreteValuationRingOfHeig
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHeightOneValuationsControlSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HtVal
namespace GlobalTheory.HtVal
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] (P : Ideal R) [hP : P.IsPrime]
    (w : (FractionRing R)ˣ →* Multiplicative ℤ)
    (hw : ∀ x : (FractionRing R)ˣ, 0 ≤ Multiplicative.toAdd (w x) ↔
      ∃ s ∉ P, algebraMap R (FractionRing R) s * x ∈ (algebraMap R (FractionRing R)).range)
    (u : (FractionRing R)ˣ) (a : R) (ha : (u : FractionRing R) = algebraMap R _ a) (haP : a ∉ P) :
    Multiplicative.toAdd (w u) = 0 := by
  have h1 : (1 : R) ∉ P := fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hp : 0 ≤ Multiplicative.toAdd (w u) := (hw u).2 ⟨1, h1, a, by rw [map_one, one_mul, ha]⟩
  have hn : 0 ≤ Multiplicative.toAdd (w u⁻¹) := (hw u⁻¹).2 ⟨a, haP, 1, by
    rw [map_one, ← ha, Units.mul_inv]⟩
  rw [map_inv, toAdd_inv] at hn
  omega
end GlobalTheory.HtVal
