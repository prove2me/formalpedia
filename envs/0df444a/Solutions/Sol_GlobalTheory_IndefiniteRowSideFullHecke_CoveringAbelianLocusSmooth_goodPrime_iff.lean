-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CoveringAbelianLocusSmooth.goodPrime_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:16.676459+00:00
-- url     : https://prove2.me/submissions/64941260-6601-4f43-b823-dec69f400f6f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoveringAbelianLocusSmooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CoveringAbelianLocusSmooth
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.IndefiniteRowSideFullHecke.CoveringAbelianLocusSmooth
theorem _root_.solution (l : Level H) {p : ℕ} (hp : p.Prime) :
    GoodPrime l p ↔ ¬ (p : ℤ) ∣ discr E ∧ ¬ p ∣ l.M' := by
  unfold GoodPrime
  rw [NumberField.not_dvd_discr_iff_isUnramifiedIn E (𝓞 E) (Nat.prime_iff_prime_int.mp hp)]
end GlobalTheory.IndefiniteRowSideFullHecke.CoveringAbelianLocusSmooth
