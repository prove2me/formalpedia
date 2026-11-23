-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.toSesq_self_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:27.634934+00:00
-- url     : https://prove2.me/submissions/150e677f-b91f-46ab-8112-5cad5040b8af

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Theorems.Thm_GroundTheory_Automorphic_conj_eq_self_iff
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_conj_toSesq_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V' V'' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
  [AddCommGroup V''] [Module E V'']
open GroundTheory.Automorphic.HermitianForm
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution [Algebra.IsSeparable F E] (h : HermitianForm F E V) (x : V) :
    h.toSesq x x ∈ Set.range (algebraMap F E) :=
  conj_eq_self_iff.1 (h.conj_toSesq_self x)
end GroundTheory.Automorphic.HermitianForm
