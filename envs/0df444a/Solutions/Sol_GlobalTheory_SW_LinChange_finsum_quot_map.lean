-- Prove2me | solution 1 for GlobalTheory.SW.LinChange.finsum_quot_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:27:20.629262+00:00
-- url     : https://prove2.me/submissions/a9f6ee1d-6acd-4251-ad17-79f571f3c0b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.LinChange
namespace GlobalTheory.SW.LinChange
theorem _root_.solution {V : Type} [AddCommGroup V] (S : AddSubgroup V) (T : V ≃+ V)
    (φ : V → ℂ) (hφ : ∀ x, ∀ y ∈ S.map T.toAddMonoidHom, φ (x + y) = φ x) :
    ∑ᶠ q : V ⧸ S, φ (T q.out) = ∑ᶠ q : V ⧸ S.map T.toAddMonoidHom, φ q.out := by
  rw [← finsum_comp_equiv (QuotientAddGroup.congr S (S.map T.toAddMonoidHom) T rfl).toEquiv]
  refine finsum_congr fun q => ?_
  have h1 : (QuotientAddGroup.congr S (S.map T.toAddMonoidHom) T rfl).toEquiv q
      = (T q.out : V ⧸ S.map T.toAddMonoidHom) := by
    conv_lhs => rw [← q.out_eq']
    rfl
  obtain ⟨y, hy⟩ := QuotientAddGroup.mk_out_eq_mul (S.map T.toAddMonoidHom) (T q.out)
  rw [h1, hy, hφ _ _ y.2]
end GlobalTheory.SW.LinChange
