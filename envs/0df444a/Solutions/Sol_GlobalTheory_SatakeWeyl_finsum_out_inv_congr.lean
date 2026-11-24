-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.finsum_out_inv_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:32:55.5808+00:00
-- url     : https://prove2.me/submissions/17f16d64-17c0-4d6c-8815-a466f3b44245

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContractingAutChainCosetSumScalingOfUnimodularit
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl
namespace GlobalTheory.SatakeWeyl
theorem _root_.solution {A : Type} [Group A] (U V : Subgroup A) (e : MulAut A) (f : A → ℂ)
    (he : ∀ a, a ∈ U ↔ e a ∈ V) (hV : ∀ v ∈ V, ∀ a, f (v * a) = f a) :
    ∑ᶠ y : A ⧸ U, f (e y.out)⁻¹ = ∑ᶠ y : A ⧸ V, f y.out⁻¹ := by
  let E : A ⧸ U ≃ A ⧸ V := Quotient.congr e.toEquiv (fun a b => by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, he, map_mul, map_inv]
    rfl)
  have hE : ∀ a : A, E (QuotientGroup.mk a) = QuotientGroup.mk (e a) := fun a => rfl
  rw [← finsum_comp_equiv E]
  refine finsum_congr fun y => ?_
  have h1 : E y = QuotientGroup.mk (e y.out) := by
    rw [← hE, QuotientGroup.out_eq']
  obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul V (e y.out)
  rw [h1, hv, mul_inv_rev, hV _ (V.inv_mem v.2)]
end GlobalTheory.SatakeWeyl
