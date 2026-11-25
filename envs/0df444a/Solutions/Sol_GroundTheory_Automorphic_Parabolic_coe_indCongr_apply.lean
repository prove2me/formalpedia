-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.coe_indCongr_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:58:51.227027+00:00
-- url     : https://prove2.me/submissions/99a3bd2e-e0fe-4374-95b9-66e0fed33cc5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCharacters

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
theorem _root_.solution (e : V₁ ≃ₗ[ℂ] V₂) (he : ∀ h v, e (ρ₁ h v) = ρ₂ h (e v))
    (φ : indSpace H ρ₁) (g : G) : ((indCongr e he φ : indSpace H ρ₂) : G → V₂) g = e ((φ : G → V₁) g) :=
  rfl
end GroundTheory.Automorphic.Parabolic
