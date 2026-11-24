-- Prove2me | solution 1 for GlobalTheory.PushInv.exists_nhds_of_gs_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:54:53.831867+00:00
-- url     : https://prove2.me/submissions/3fd9287e-264e-4c19-a6da-af7e54ea89c6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsProperRestrictPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PushInvertibleOfDensePart
import Theorems.Thm_GlobalTheory_PushInv_gs_id

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.PushInv
open GlobalTheory.AbLocusPull
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.PushInv
theorem _root_.solution {U₁ U₂ U₃ : X.Opens} {x : X} (h₁ : x ∈ U₁) (h₂ : x ∈ U₂) (h₃ : x ∈ U₃)
    (f₁ : Γ(X, U₁)) (f₂ : Γ(X, U₂)) (f₃ : Γ(X, U₃))
    (e : gs (𝟙 X) x U₁ f₁ = gs (𝟙 X) x U₂ f₂ * gs (𝟙 X) x U₃ f₃) :
    ∃ N : X.Opens, x ∈ N ∧ N ≤ U₁ ⊓ U₂ ⊓ U₃ ∧
      ∀ z ∈ N, gs (𝟙 X) z U₁ f₁ = gs (𝟙 X) z U₂ f₂ * gs (𝟙 X) z U₃ f₃ := by
  have h₂₃ : x ∈ U₂ ⊓ U₃ := ⟨h₂, h₃⟩
  have m : ∀ z ∈ U₂ ⊓ U₃, gs (𝟙 X) z (U₂ ⊓ U₃) (resG X inf_le_left f₂ * resG X inf_le_right f₃) =
      gs (𝟙 X) z U₂ f₂ * gs (𝟙 X) z U₃ f₃ := fun z hz => by
    rw [gs_mul _ z _ hz, gs_res _ z _ hz, gs_res _ z _ hz]
  rw [← m x h₂₃, gs_id x _ h₁, gs_id x _ h₂₃] at e
  obtain ⟨N, hN, i₁, i₂, e⟩ := X.presheaf.germ_eq x h₁ h₂₃ _ _ e
  refine ⟨N, hN, le_inf (le_inf i₁.le (i₂.le.trans inf_le_left)) (i₂.le.trans inf_le_right), fun z hz => ?_⟩
  rw [← m z (i₂.le hz), ← gs_res (𝟙 X) z i₁.le hz, ← gs_res (𝟙 X) z i₂.le hz]
  exact congrArg (gs (𝟙 X) z N) e
end GlobalTheory.PushInv
