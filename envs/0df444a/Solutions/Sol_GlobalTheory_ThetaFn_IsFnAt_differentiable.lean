-- Prove2me | solution 1 for GlobalTheory.ThetaFn.IsFnAt.differentiable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:39:28.542404+00:00
-- url     : https://prove2.me/submissions/42a5c642-218b-4144-9d9e-8f8fd4d43ce5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_hol

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
theorem _root_.solution (hL : L.IsLB) {k : ℤ} {s : LB.Sec (LPow A L k T)}
    {θ : (Fin g → ℂ) → ℂ} (h : IsFnAt u p k s θ) : Differentiable ℂ θ := by
  intro z
  obtain ⟨j, hj⟩ := exists_chart_exAt u p hL k z
  obtain ⟨ho, hd⟩ := exAt_hol u p _ (s.f j)
  have hn := ho.mem_nhds hj
  have hd2 : DifferentiableOn ℂ (u.fr (j 0)) {w | ⊤ ≤ exAt u p w ⁻¹ᵁ (LPow A L k T).U j} :=
    (u.fr_hol _).mono fun w hw => (exAt_mem_chart_iff u p k j w).1 hw
  have hq := (hd.differentiableAt hn).mul ((hd2.differentiableAt hn).zpow (m := -k)
    (Or.inl (u.fr_ne _ z ((exAt_mem_chart_iff u p k j z).1 hj))))
  refine hq.congr_of_eventuallyEq ?_
  filter_upwards [hn] with w hw
  rw [h.eq_div hw, div_eq_mul_inv, ← zpow_neg]
  rfl
end IsFnAt
end GlobalTheory.ThetaFn
