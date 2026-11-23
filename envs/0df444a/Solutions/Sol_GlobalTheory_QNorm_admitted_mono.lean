-- Prove2me | solution 1 for GlobalTheory.QNorm.admitted.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:07.319709+00:00
-- url     : https://prove2.me/submissions/cf0dfba3-3f21-424b-9f8f-d4c5342891bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped WithZero
noncomputable section
open GlobalTheory GlobalTheory.QNorm
variable (F : Type) [Field F] [NumberField F]
namespace GlobalTheory.QNorm
namespace admitted
theorem _root_.solution {F : Type} [Field F] [NumberField F] {S T : Finset (HeightOneSpectrum (𝓞 F))}
    (h : admitted F S) (hST : S ⊆ T) : admitted F T := by
  intro v hv
  obtain ⟨h2, π, hπ, hw⟩ := h v (fun a => hv (hST a))
  exact ⟨h2, π, hπ, fun w hwT hne => hw w (fun a => hwT (hST a)) hne⟩
end admitted
end GlobalTheory.QNorm
