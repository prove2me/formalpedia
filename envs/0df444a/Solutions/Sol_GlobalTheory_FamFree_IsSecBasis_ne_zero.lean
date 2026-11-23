-- Prove2me | solution 1 for GlobalTheory.FamFree.IsSecBasis.ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:57:15.014854+00:00
-- url     : https://prove2.me/submissions/6dea9e77-9ce6-4900-b462-759a18c3aec4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FamFree
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.FamFree
namespace IsSecBasis
theorem _root_.solution {S : Scheme.{0}} {A T : Over S} [Nontrivial Γ(T.left, ⊤)] {N : LB (T ⊗ A).left} {m : ℕ}
    {b : Fin m → LB.Sec N} (hb : IsSecBasis N b) (i : Fin m) : ¬ ∀ j, (b i).f j = 0 := by
  classical
  intro h
  obtain ⟨r, -, hr⟩ := hb SecOps.secZero
  have h0 := hr 0 (fun j => by
    show (0 : Γ((T ⊗ A).left, N.U j)) = _
    simp only [Pi.zero_apply, map_zero, MulZeroClass.zero_mul, Finset.sum_const_zero])
  have h1 := hr (Pi.single i 1) (fun j => by
    show (0 : Γ((T ⊗ A).left, N.U j)) = _
    refine (Finset.sum_eq_zero fun i' _ => ?_).symm
    by_cases e : i' = i
    · rw [e, h j, mul_zero]
    · rw [Pi.single_eq_of_ne e, map_zero, map_zero, MulZeroClass.zero_mul])
  have := congrFun (h1.trans h0.symm) i
  rw [Pi.single_eq_same] at this
  exact one_ne_zero this
end IsSecBasis
end GlobalTheory.FamFree
