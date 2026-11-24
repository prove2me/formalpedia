-- Prove2me | solution 1 for GlobalTheory.SW.LinChange.finsum_quot_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:44:25.216812+00:00
-- url     : https://prove2.me/submissions/0636fc94-a4e2-489e-82e2-e23bbb2e76e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMul
import Theorems.Thm_GlobalTheory_SW_LinChange_finsum_prod_fst

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
theorem _root_.solution {V : Type} [AddCommGroup V] (S P : AddSubgroup V) (hle : S ≤ P)
    (hi : S.relIndex P ≠ 0) (φ : V → ℂ) (hφ : ∀ x, ∀ y ∈ P, φ (x + y) = φ x) :
    ∑ᶠ q : V ⧸ S, φ q.out = (S.relIndex P : ℂ) * ∑ᶠ q : V ⧸ P, φ q.out := by
  have : Finite (P ⧸ S.addSubgroupOf P) := Nat.finite_of_card_ne_zero hi
  have h := finsum_prod_fst (B := P ⧸ S.addSubgroupOf P) (fun q : V ⧸ P => φ q.out)
  rw [← finsum_comp_equiv (AddSubgroup.quotientEquivProdOfLE hle)] at h
  refine Eq.trans (finsum_congr fun q => ?_) h
  have h1 : (AddSubgroup.quotientEquivProdOfLE hle q).1 = (q.out : V ⧸ P) := by
    conv_lhs => rw [← q.out_eq']
    rfl
  obtain ⟨y, hy⟩ := QuotientAddGroup.mk_out_eq_mul P q.out
  rw [h1, hy, hφ _ _ y.2]
end GlobalTheory.SW.LinChange
