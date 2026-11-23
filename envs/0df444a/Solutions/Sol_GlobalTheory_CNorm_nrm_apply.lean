-- Prove2me | solution 1 for GlobalTheory.CNorm.nrm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:01:13.073427+00:00
-- url     : https://prove2.me/submissions/909de1e5-a5cd-4fa7-ab81-f6854ff0d6c4

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
namespace GlobalTheory.CNorm
theorem _root_.solution {A : Type} [CommGroup A] (σ : A →* A) (n : ℕ) (a : A) :
    nrm σ n a = ∏ i ∈ Finset.range n, σ^[i] a := rfl
end GlobalTheory.CNorm
