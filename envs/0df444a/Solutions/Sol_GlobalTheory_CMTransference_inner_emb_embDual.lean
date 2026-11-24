-- Prove2me | solution 1 for GlobalTheory.CMTransference.inner_emb_embDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:03:53.326881+00:00
-- url     : https://prove2.me/submissions/6be6dac5-fecb-4922-8213-4f45893144ed

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoveringRadiusStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BabaiCovering
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_CmApproximationTransference
import Theorems.Thm_GlobalTheory_CMTransference_trace_eq_two_mul_sum_re
import Theorems.Thm_GlobalTheory_CMTransference_traceForm_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CMTransference
open NumberField Matrix Module Submodule ReciprocityTheory.MultiplicativeHeights ComplexConjugate
variable {K : Type} [Field K] [NumberField K] {r : ℕ} {ι : Type} [Fintype ι]
variable (p : ℕ) (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ)
variable {p σ Q}
namespace GlobalTheory.CMTransference
theorem _root_.solution {S : HermForm K r} (hσ : Function.Injective σ)
    (hcm : ∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ)
    (hQ : ∀ i x y, σ i (S.h x y) = jForm p (Q i *ᵥ embVec (σ i) x) (Q i *ᵥ embVec (σ i) y))
    (x y : Fin r → K) :
    inner ℝ (emb σ Q y) (embDual p σ Q x) = (traceForm S x y : ℝ) := by
  rw [traceForm_apply, trace_eq_two_mul_sum_re hσ hcm, PiLp.inner_apply, Fintype.sum_prod_type,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hQ, jForm, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.inner]
  change (2 * sgn p k * (Q i *ᵥ embVec (σ i) x) k * conj ((Q i *ᵥ embVec (σ i) y) k)).re = _
  unfold sgn
  split_ifs <;> simp <;> ring
end GlobalTheory.CMTransference
