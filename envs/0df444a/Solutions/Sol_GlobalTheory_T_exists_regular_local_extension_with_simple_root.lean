-- Prove2me | solution 1 for GlobalTheory.T.exists_regular_local_extension_with_simple_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:16:17.890878+00:00
-- url     : https://prove2.me/submissions/a7f18aa7-62fa-4b08-8a1a-cfd3b9650ffc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularLocalExtensionWithSimpleRoot
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularLocalExtensionWithSimpleRootStatement
import Theorems.Thm_GlobalTheory_MonicRootExtension_exists_extension


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A Ω : Type) [CommRing A] [IsRegularLocalRing A] [Field Ω] (u : A →+* Ω) (p : Polynomial A) (α : Ω), RingHom.ker u = maximalIdeal A → IsAdicComplete (maximalIdeal A) A → p.Monic → (p.map u).eval α = 0 → (p.map u).derivative.eval α ≠ 0 → ∃ (E : Type) (_ : CommRing E) (_ : IsRegularLocalRing E) (a : A →+* E) (v : E →+* Ω), a.Flat ∧ (maximalIdeal A).map a = maximalIdeal E ∧ IsAdicComplete (maximalIdeal E) E ∧ RingHom.ker v = maximalIdeal E ∧ v.comp a = u ∧ α ∈ v.range := by
  first | exact @GlobalTheory.MonicRootExtension.exists_extension | exact GlobalTheory.MonicRootExtension.exists_extension | (intros; apply GlobalTheory.MonicRootExtension.exists_extension <;> assumption)
end _root_.GlobalTheory.T
