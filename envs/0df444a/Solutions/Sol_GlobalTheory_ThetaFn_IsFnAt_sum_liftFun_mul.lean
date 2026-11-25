-- Prove2me | solution 1 for GlobalTheory.ThetaFn.IsFnAt.sum_liftFun_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:46:03.725811+00:00
-- url     : https://prove2.me/submissions/5249dca2-b99b-43eb-8307-178c38cf6599

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Theorems.Thm_P2M_GlobalTheory_ThetaFn_valAt__sum_a41dbec43369

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
variable {u p}
namespace GlobalTheory.ThetaFn
namespace IsFnAt
theorem _root_.solution {k : ℤ} {I : Type*} (F : Finset I) {s : I → LB.Sec (LPow A L k T)}
    {t : LB.Sec (LPow A L k T)} {θ : I → (Fin g → ℂ) → ℂ} (h : ∀ i ∈ F, IsFnAt u p k (s i) (θ i))
    (r : I → Γ(T.left, ⊤)) (ht : ∀ j, t.f j = ∑ i ∈ F, liftFun A _ (r i) * (s i).f j) :
    IsFnAt u p k t (∑ i ∈ F, valAt' p.left ⊤ (r i) • θ i) := fun j z hj => by
  rw [ht j, valAt'_sum _ hj, Finset.sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [valAt'_mul _ hj, valAt'_liftFun u p hj, h i hi j z hj, Pi.smul_apply, smul_eq_mul,
    _root_.mul_assoc]
end IsFnAt
end GlobalTheory.ThetaFn
