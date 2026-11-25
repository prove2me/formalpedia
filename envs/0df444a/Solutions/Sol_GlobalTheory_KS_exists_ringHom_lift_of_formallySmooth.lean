-- Prove2me | solution 1 for GlobalTheory.KS.exists_ringHom_lift_of_formallySmooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:57:46.94281+00:00
-- url     : https://prove2.me/submissions/ee06f845-8b07-4d38-ba88-d47cadb967cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDerivationExtendOfFormallySmooth

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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS
namespace GlobalTheory.KS
theorem _root_.solution (R B E C : Type) [CommRing R] [CommRing B]
    [CommRing E] [CommRing C] [Algebra R B] [Algebra.FormallySmooth R B]
    (φ : B →+* C) (ψ : R →+* E) (π : E →+* C) (hπ : Function.Surjective π)
    (hn : IsNilpotent (RingHom.ker π)) (hc : ∀ r, π (ψ r) = φ (algebraMap R B r)) :
    ∃ l : B →+* E, (∀ b, π (l b) = φ b) ∧ ∀ r, l (algebraMap R B r) = ψ r := by
  letI : Algebra R E := ψ.toAlgebra
  letI : Algebra R C := (φ.comp (algebraMap R B)).toAlgebra
  let f : B →ₐ[R] C := { φ with commutes' := fun _ => rfl }
  let g : E →ₐ[R] C := { π with commutes' := fun r => hc r }
  refine ⟨(Algebra.FormallySmooth.liftOfSurjective f g hπ hn).toRingHom, fun b => ?_, fun r => ?_⟩
  · exact Algebra.FormallySmooth.liftOfSurjective_apply f g hπ hn b
  · exact (Algebra.FormallySmooth.liftOfSurjective f g hπ hn).commutes r
end GlobalTheory.KS
