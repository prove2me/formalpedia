-- Prove2me | solution 1 for GlobalTheory.T.exists_global_element_near_idempotent_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:51:28.97231+00:00
-- url     : https://prove2.me/submissions/0ad4bc6c-7d2e-468f-afdb-291d6516ce1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGlobalElementNearIdempotentAdicCompletion
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGlobalElementNearIdempotentAdicCompletionStatement
import Theorems.Thm_GlobalTheory_exists_global_near_idempotent


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [Algebra E E'] [FiniteDimensional E E'] (w : HeightOneSpectrum (𝓞 E)) {ι : Type} [Fintype ι] (b : Module.Basis ι E E') (ψ : w.adicCompletion E ⊗[E] E' →ₐ[w.adicCompletion E] w.adicCompletion E) (e : w.adicCompletion E ⊗[E] E'), e * e = e → ψ e = 1 → ∀ (p q : w.adicCompletion E ⊗[E] E') (n : ℕ), ∃ ε : E', (∀ i, w.valuation E (b.repr (ε * ε - ε) i) ≤ 1) ∧ Valued.v (ψ ((1 : w.adicCompletion E) ⊗ₜ ε) - 1) ≤ WithZero.exp (-(n : ℤ)) ∧ Valued.v (Algebra.norm (w.adicCompletion E) (p + q * ((1 : w.adicCompletion E) ⊗ₜ ε - e)) - Algebra.norm (w.adicCompletion E) p) ≤ WithZero.exp (-(n : ℤ)) := by
  first | exact @GlobalTheory.exists_global_near_idempotent | exact GlobalTheory.exists_global_near_idempotent | (intros; apply GlobalTheory.exists_global_near_idempotent <;> assumption)
end _root_.GlobalTheory.T
