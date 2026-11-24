-- Prove2me | solution 1 for GlobalTheory.SymOfZeroDivisor.sym_of_regular_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:54:08.949799+00:00
-- url     : https://prove2.me/submissions/bff44303-b763-4ee9-bb64-647bb1917775

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsoLineBundleOfRegularPullbacksSameZeroSchemeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SymmetricLineBundleOfRegularSection
import Theorems.Thm_GlobalTheory_SymOfZeroDivisor_appLE_mem_nonZeroDivisors
import Theorems.Thm_GlobalTheory_SymOfZeroDivisor_inv_eq_zero_iff
import Theorems.Thm_GlobalTheory_T_isoLineBundle_of_regularPullbacks_sameZeroScheme


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SymOfZeroDivisor
namespace GlobalTheory.SymOfZeroDivisor
theorem _root_.solution : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left) (θ : L.Sec), L.IsLB → (∀ (i : L.ι) (V : Scheme.Opens A.left) (h : V ≤ L.U i), resG A.left h (θ.f i) ∈ nonZeroDivisors Γ(A.left, V)) → (∀ (T : Scheme.{0}) (t : T ⟶ A.left) (i : L.ι) (h : ⊤ ≤ t ⁻¹ᵁ L.U i), (t.appLE (L.U i) ⊤ h).hom (θ.f i) = 0 ↔ t = t ≫ A.hom ≫ eSec A) → Out.Sym A L := by
  intro S A _ L θ hL hreg hz s
  refine ⟨⊤, trivial, ?_⟩
  haveI : IsIso (GrpObj.inv : A ⟶ A).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (GrpObj.inv : A ⟶ A)))
  refine GlobalTheory.T.isoLineBundle_of_regularPullbacks_sameZeroScheme A.left _ L θ _ _ hL
    (fun i V h => appLE_mem_nonZeroDivisors _ _ _ (hreg i) V h)
    (fun i V h => appLE_mem_nonZeroDivisors _ _ _ (hreg i) V h) ?_
  intro T t i j h h'
  rw [hz, hz, ← Category.assoc t]
  exact inv_eq_zero_iff A _
end GlobalTheory.SymOfZeroDivisor
