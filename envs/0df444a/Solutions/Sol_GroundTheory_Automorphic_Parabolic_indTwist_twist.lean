-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.indTwist_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:54.929794+00:00
-- url     : https://prove2.me/submissions/6e056d83-9631-405f-8b96-1a006506ad67

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCharacters
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_coe_indTwist_apply

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ H V}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (χ : G →* ℂ) (hχ : ∀ g, χ g ≠ 0)
    (hχo : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, χ u = 1) (g : G) (φ : indSpace H ρ) :
    indTwist χ hχ hχo (twist χ (indRep H ρ) g φ) =
      indRep H (twist (χ.comp H.subtype) ρ) g (indTwist χ hχ hχo φ) :=
  Subtype.ext (funext fun x => by
    rw [coe_indTwist_apply, coe_indRep_apply, coe_indTwist_apply, twist_apply,
      Submodule.coe_smul, Pi.smul_apply, coe_indRep_apply, smul_smul, map_mul])
end GroundTheory.Automorphic.Parabolic
