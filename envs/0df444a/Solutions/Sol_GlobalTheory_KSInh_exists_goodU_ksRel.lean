-- Prove2me | solution 1 for GlobalTheory.KSInh.exists_goodU_ksRel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:40:35.615863+00:00
-- url     : https://prove2.me/submissions/f2647b1b-757d-4960-b21b-3c3a4fd3f68d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGoodUniformisationKodairaSpencer
import Theorems.Thm_GlobalTheory_KSInh_ksRel_const

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
noncomputable section
open GlobalTheory GlobalTheory.KSInh
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g)
namespace GlobalTheory.KSInh
theorem _root_.solution : ThetaUnifAV → ∀ P₀ : Out.PolAV (Sp ℂ), ∃ (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ ∧ ∀ w : Fin P₀.g → ℂ, KSRel u P₀.A.hom (𝟙 _) (fun _ => 0) 0 (fun z W f => fderiv ℂ (fn u (𝟙 _) W f) z w) := by
  intro hT P₀
  obtain ⟨rig, hrig⟩ : ∃ rig : LB.Gen (P₀.L.pull (eSec P₀.A)), rig.IsGen := P₀.rigid
  obtain ⟨u, Hm, χ, _, hAH, -, ht₁, ht₂, hend, hth, -⟩ := hT P₀ rig hrig
  exact ⟨u, Hm, χ, ⟨hAH, ht₁, ht₂, hend, fun n θ hθ => ((hth n).2 θ hθ).exists⟩, fun w => ksRel_const u w⟩
end GlobalTheory.KSInh
