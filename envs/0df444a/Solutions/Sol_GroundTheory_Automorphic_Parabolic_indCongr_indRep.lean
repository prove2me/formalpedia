-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.indCongr_indRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:30:48.234367+00:00
-- url     : https://prove2.me/submissions/91efb2cb-d360-488d-bb0a-be63296da803

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCharacters
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_coe_indCongr_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H : Subgroup G}
  {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  {ρ₁ : Representation ℂ H V₁} {ρ₂ : Representation ℂ H V₂}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (e : V₁ ≃ₗ[ℂ] V₂) (he : ∀ h v, e (ρ₁ h v) = ρ₂ h (e v)) (g : G)
    (φ : indSpace H ρ₁) :
    indCongr e he (indRep H ρ₁ g φ) = indRep H ρ₂ g (indCongr e he φ) :=
  Subtype.ext (funext fun x => by rw [coe_indCongr_apply, coe_indRep_apply, coe_indRep_apply,
    coe_indCongr_apply])
end GroundTheory.Automorphic.Parabolic
