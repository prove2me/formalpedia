-- Prove2me | solution 1 for GlobalTheory.T.exists_twist_basis_off_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:32:56.396093+00:00
-- url     : https://prove2.me/submissions/c09273f7-e802-4589-9fef-69ae82e2f8dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrimeStatement
import Theorems.Thm_GlobalTheory_TwistLoc_exists_basis_off_prime


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace _root_.GlobalTheory.T
theorem _root_.solution : PolBaseChangeSt → GlobalFnsSt → DVR.TwistBaseChangeStatement → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R), (∃ W : (Spec (CommRingCat.of R)).Opens, genericPoint (Spec (CommRingCat.of R)) ∈ W ∧ Nonempty (PsiOn D W)) → ∀ (p : Ideal R) [p.IsPrime] (k : ℕ), 1 ≤ k → ∀ α : D.X, ∃ b : Fin (k ^ D.P.g) → D.SecB k α, ∀ (R' : Type) [CommRing R'] (f : R →+* R'), (∀ s ∉ p, IsUnit (f s)) → ∀ b' : Fin (k ^ D.P.g) → LB.Sec (LB.LinComb D.P.L (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left ≫ DegPre.famφB D α i) (DegPre.famε k)), (∀ i, IsPullSecLC D.P.L (DegPre.famφB D α) (DegPre.famε k) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left (b i) (b' i)) → IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.P.A) _ b' := by
  first | exact @GlobalTheory.TwistLoc.exists_basis_off_prime | exact GlobalTheory.TwistLoc.exists_basis_off_prime | (intros; apply GlobalTheory.TwistLoc.exists_basis_off_prime <;> assumption)
end _root_.GlobalTheory.T
