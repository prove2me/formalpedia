-- Prove2me | solution 1 for GroundTheory.Automorphic.TorusE.ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:17:40.265655+00:00
-- url     : https://prove2.me/submissions/f78a61b7-b513-4d78-9754-c0749e9f1140

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus
import Theorems.Thm_GroundTheory_Automorphic_TorusE_val_mk
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj


attribute [local simp] GroundTheory.Automorphic.TorusE.val_mk

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type*} [AddCommGroup V] [Module E V]
variable [FiniteDimensional E V]
open GroundTheory.Automorphic.TorusE
variable {γ : V ≃ₗ[E] V}
omit [FiniteDimensional E V]
namespace GroundTheory.Automorphic.TorusE
theorem _root_.solution {a b : TorusE γ} (hab : a.val = b.val) : a = b :=
  Subtype.ext (p := (· ∈ torusE γ)) hab
end GroundTheory.Automorphic.TorusE
