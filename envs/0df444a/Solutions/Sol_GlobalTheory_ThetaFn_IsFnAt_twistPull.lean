-- Prove2me | solution 1 for GlobalTheory.ThetaFn.IsFnAt.twistPull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:29:57.404132+00:00
-- url     : https://prove2.me/submissions/4248b9a9-b992-4ddc-86c6-cba02aa07e97

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Theorems.Thm_P2M_GlobalTheory_ThetaFn_valAt__appLE__46c54dbc5e3c

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
variable (u p)
variable {u p}
namespace GlobalTheory.ThetaFn
namespace IsFnAt
theorem _root_.solution {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
    {s : LB.Sec (LPow A L b T)} {s' : LB.Sec (LPow A L a T)} {θ θ' : (Fin g → ℂ) → ℂ}
    (h : IsFnAt u p b s θ) (h' : IsFnAt u p a s' θ') (ht : IsTwistPull A L ψ m hm a b α s s')
    {z w : Fin g → ℂ} (hw : exAt u p z ≫ ψ.left = exAt u p w) (j : Fin 2 → L.ι)
    (hj : ⊤ ≤ exAt u p z ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j) :
    θ' z * u.fr (j 0) z ^ a =
      valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, m.left] j) (α.s j).val *
        (θ w * u.fr (j 1) w ^ b) := by
  have h0 : ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L a T).U (fun _ => j 0) :=
    fun _ hy => chart_le_zero A L m j (hj hy)
  have h1 : ⊤ ≤ exAt u p w ⁻¹ᵁ (LPow A L b T).U (fun _ => j 1) := by
    rw [← hw]
    exact fun _ hy => chart_le_pull A L ψ m hm j (hj hy)
  refine (h' _ z h0).symm.trans ((valAt'_res _ (chart_le_zero A L m j) hj _).symm.trans ?_)
  refine (congrArg _ (ht j)).trans ((valAt'_mul _ hj _ _).trans (congrArg (_ * ·) ?_))
  refine (valAt'_appLE' _ ψ.left (chart_le_pull A L ψ m hm j) hj _).trans ?_
  rw [hw]
  exact h _ w h1
end IsFnAt
end GlobalTheory.ThetaFn
