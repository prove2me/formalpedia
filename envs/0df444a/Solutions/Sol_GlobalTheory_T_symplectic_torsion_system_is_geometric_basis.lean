-- Prove2me | solution 1 for GlobalTheory.T.symplectic_torsion_system_is_geometric_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:33:29.721492+00:00
-- url     : https://prove2.me/submissions/b724b323-9051-493b-9522-f652b6f269ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SymplecticTorsionSystemIsGeometricBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SymplecticTorsionSystemIsGeometricBasisStatement
import Theorems.Thm_GlobalTheory_symplectic_system_torsion_basis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
namespace _root_.GlobalTheory.T
theorem _root_.solution : Out.Laws → ∀ (K₀ : Type) [Field K₀] (P : Out.PolAV (Sp K₀)) (k : ℕ) (ze : K₀ˣ) (pt : Fin (2 * P.g) → (Out.baseOver (Sp K₀) ⟶ P.A)), (k : K₀) ≠ 0 → IsPrimitiveRoot ze k → (∀ i, pt i ^ k = 1) → (∀ i j, Out.WeilIs P.A P.L k (pt i) (pt j) (unitOn ze ^ Out.stdSymp P.g i j)) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp K₀) (y : Over.mk x ⟶ P.A), y ^ k = 1 → ∃! c : Fin (2 * P.g) → ZMod k, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp K₀)) ≫ pt i) (fun i => (c i).val) = y := by
  first | exact @GlobalTheory.symplectic_system_torsion_basis | exact GlobalTheory.symplectic_system_torsion_basis | (intros; apply GlobalTheory.symplectic_system_torsion_basis <;> assumption)
end _root_.GlobalTheory.T
