-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.coe_indTwist_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:06:44.520951+00:00
-- url     : https://prove2.me/submissions/f9cddeff-5afb-4142-bf1c-1767959af0b1

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ H V}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (χ : G →* ℂ) (hχ : ∀ g, χ g ≠ 0)
    (hχo : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, χ u = 1) (φ : indSpace H ρ) (g : G) :
    ((indTwist χ hχ hχo φ : indSpace H (twist (χ.comp H.subtype) ρ)) : G → V) g =
      χ g • (φ : G → V) g := rfl
end GroundTheory.Automorphic.Parabolic
