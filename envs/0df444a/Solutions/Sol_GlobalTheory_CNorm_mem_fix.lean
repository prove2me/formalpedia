-- Prove2me | solution 1 for GlobalTheory.CNorm.mem_fix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:07.234817+00:00
-- url     : https://prove2.me/submissions/b0fd70ae-3d37-4f04-b61b-86b997340da1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CNorm
open NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
namespace GlobalTheory.CNorm
namespace _root_.GlobalTheory.CNorm
theorem _root_.solution {A : Type} [CommGroup A] (σ : A →* A) (a : A) :
    a ∈ _root_.GlobalTheory.CNorm.fix σ ↔ σ a = a := Iff.rfl
end _root_.GlobalTheory.CNorm
end GlobalTheory.CNorm
