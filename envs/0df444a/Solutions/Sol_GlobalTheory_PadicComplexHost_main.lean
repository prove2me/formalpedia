-- Prove2me | solution 1 for GlobalTheory.PadicComplexHost.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:57:24.7959+00:00
-- url     : https://prove2.me/submissions/7da63df2-1ad8-4f64-95ef-5096412c4c76

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsPrimitiveRoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
import Theorems.Thm_GlobalTheory_PadicComplexHost_not_isUnit_p
import Theorems.Thm_GlobalTheory_PadicComplexHost_isAdicComplete
import Theorems.Thm_ReciprocityTheory_PGsh_exists_eps


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Ideal
open GlobalTheory GlobalTheory.PadicComplexHost
variable (p : ℕ) [hp : Fact p.Prime]
namespace GlobalTheory.PadicComplexHost
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime], ∃ (_ : Fact ¬IsUnit ((p : ℕ) : 𝓞_ℂ_[p])) (_ : IsAdicComplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p])
    (ε : PreTilt 𝓞_ℂ_[p] p), (Valued.v : Valuation ℂ_[p] NNReal).Integers 𝓞_ℂ_[p] ∧
      IsPrimitiveRoot (((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm ε).untilt) p := by
  intro p _
  have h1 : Fact ¬IsUnit ((p : ℕ) : 𝓞_ℂ_[p]) := ⟨not_isUnit_p p⟩
  have h2 := isAdicComplete p
  obtain ⟨ε, hε⟩ := ReciprocityTheory.PGsh.exists_eps (p := p) ℂ_[p] Valued.v 𝓞_ℂ_[p]
    (PadicComplexInt.integers p)
  exact ⟨h1, h2, ε, PadicComplexInt.integers p, hε⟩
end GlobalTheory.PadicComplexHost
