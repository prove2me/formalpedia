-- Prove2me | solution 1 for GlobalTheory.T.symmetric_lineBundle_of_regular_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:04:51.347802+00:00
-- url     : https://prove2.me/submissions/6d894346-ec6c-43b7-9ecf-e4c0df398dd7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SymmetricLineBundleOfRegularSection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SymmetricLineBundleOfRegularSectionStatement
import Theorems.Thm_GlobalTheory_SymOfZeroDivisor_sym_of_regular_section


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
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left) (θ : L.Sec), L.IsLB → (∀ (i : L.ι) (V : Scheme.Opens A.left) (h : V ≤ L.U i), resG A.left h (θ.f i) ∈ nonZeroDivisors Γ(A.left, V)) → (∀ (T : Scheme.{0}) (t : T ⟶ A.left) (i : L.ι) (h : ⊤ ≤ t ⁻¹ᵁ L.U i), (t.appLE (L.U i) ⊤ h).hom (θ.f i) = 0 ↔ t = t ≫ A.hom ≫ eSec A) → Out.Sym A L := by
  first | exact @GlobalTheory.SymOfZeroDivisor.sym_of_regular_section | exact GlobalTheory.SymOfZeroDivisor.sym_of_regular_section | (intros; apply GlobalTheory.SymOfZeroDivisor.sym_of_regular_section <;> assumption)
end _root_.GlobalTheory.T
