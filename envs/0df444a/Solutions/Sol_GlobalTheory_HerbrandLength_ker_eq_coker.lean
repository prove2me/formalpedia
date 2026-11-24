-- Prove2me | solution 1 for GlobalTheory.HerbrandLength.ker_eq_coker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:27:45.280322+00:00
-- url     : https://prove2.me/submissions/52fb6294-2d8b-49a9-977e-9cd4d21729ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthEqKerAddRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HerbrandLength
open IsLocalRing
variable {A : Type} [CommRing A]
namespace GlobalTheory.HerbrandLength
theorem _root_.solution {M : Type} [AddCommGroup M] [Module A M] (φ : M →ₗ[A] M)
    (h : Module.length A M ≠ ⊤) :
    Module.length A (M ⧸ LinearMap.range φ) = Module.length A (LinearMap.ker φ) := by
  have h1 := Module.length_eq_add_of_exact (LinearMap.ker φ).subtype (LinearMap.ker φ).mkQ
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have h2 := Module.length_eq_add_of_exact (LinearMap.range φ).subtype (LinearMap.range φ).mkQ
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  rw [φ.quotKerEquivRange.length_eq] at h1
  have hR : Module.length A (LinearMap.range φ) ≠ ⊤ :=
    ne_top_of_le_ne_top h (le_self_add.trans_eq h2.symm)
  exact WithTop.add_left_cancel hR (h2.symm.trans (h1.trans (add_comm _ _)))
end GlobalTheory.HerbrandLength
