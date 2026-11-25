-- Prove2me | solution 1 for GlobalTheory.ThetaFn.isFnAt_iff_isFnPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:45:45.355993+00:00
-- url     : https://prove2.me/submissions/2d5a8d4b-d595-4857-8cac-07ee0b40dfd8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Theorems.Thm_P2M_GlobalTheory_ThetaFn_valAt__pullPow_0a8ce325415d
import Theorems.Thm_GlobalTheory_ThetaFn_ex_fibreIncl

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
namespace GlobalTheory.ThetaFn
theorem _root_.solution (n : ℕ) (s : LB.Sec (LPow A L n T)) (θ : (Fin g → ℂ) → ℂ) :
    IsFnAt u p n s θ ↔ u.IsFnPow n (toFibre L p n s) θ := by
  have hm : ∀ (i : L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U (fun _ => i) ↔
      ⊤ ≤ exAt u p z ⁻¹ᵁ (LPow A L n T).U (fun _ => i) := fun i z =>
    (le_wchart_unique L (K := PUnit) (u.ex z).left (𝟙 _) (fun _ => i)).trans
      (exAt_mem_chart_iff u p n (fun _ => i) z).symm
  have hv : ∀ (i : L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U (fun _ => i) →
      valAt' (u.ex z).left ((lbPow L n).U fun _ => i) ((toFibre L p n s).f fun _ => i) =
        valAt' (exAt u p z) ((LPow A L n T).U fun _ => i) (s.f fun _ => i) := fun i z hz => by
    rw [← ex_fibreIncl]
    exact valAt'_pullPow L _ _ _ s _ (fun _ : PUnit => i) hz
  constructor
  · intro h j z hj
    exact (hv (j PUnit.unit) z hj).trans
      ((h (fun _ => j PUnit.unit) z ((hm _ z).1 hj)).trans (by rw [zpow_natCast]))
  · intro h j z hj
    obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i :=
      ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    have hj' := (hm i z).2 hj
    exact (hv i z hj').symm.trans ((h _ z hj').trans (by rw [zpow_natCast]))
end GlobalTheory.ThetaFn
