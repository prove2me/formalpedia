-- Prove2me | solution 1 for GlobalTheory.ThetaFn.exists_unif_isFnT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:26:07.669067+00:00
-- url     : https://prove2.me/submissions/35c64096-dd02-41b0-8879-0792c716a85d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Theorems.Thm_GlobalTheory_ThetaFn_isFnT_iff_isFnPow
import Theorems.Thm_GlobalTheory_ThetaFn_existsUnique_sec_isFnT

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
namespace GlobalTheory.ThetaFn
theorem _root_.solution (h : ThetaUnifAV) (P : PolAV (Sp ℂ))
    (rig : LB.Gen (P.L.pull (eSec P.A))) (hrig : rig.IsGen) :
    ∃ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ),
      u.IsAH Hm χ ∧ u.IsRig rig ∧ ∀ n : ℕ,
        (∀ s : LB.Sec (LPow P.A P.L n (baseOver (Sp ℂ))),
          ∃! θ, u.IsThetaFn Hm χ n θ ∧ IsFnT u n s θ) ∧
        ∀ θ, u.IsThetaFn Hm χ n θ →
          ∃! s : LB.Sec (LPow P.A P.L n (baseOver (Sp ℂ))), IsFnT u n s θ := by
  obtain ⟨u, Hm, χ, -, hAH, hr, -, -, -, hsec, -⟩ := h P rig hrig
  refine ⟨u, Hm, χ, hAH, hr, fun n => ⟨fun s => ?_, fun θ hθ =>
    existsUnique_sec_isFnT u (hsec n).2 hθ⟩⟩
  simpa only [isFnT_iff_isFnPow] using (hsec n).1 (fibreEquiv P.L basePt n s)
end GlobalTheory.ThetaFn
