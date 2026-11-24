-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.intIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:52:04.260483+00:00
-- url     : https://prove2.me/submissions/de0c41de-c569-4183-af5a-b978b3de0429

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardIntegersModUniformizerEqQSq
import Theorems.Thm_GlobalTheory_SatakeWeyl_lt_one_iff_le_exp_neg_one
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
theorem _root_.solution : GlobalTheory.SatakeWeyl.IntIndex := by
  intro L _ _ ϖ σ q hU
  obtain ⟨-, -, -, hϖ, -, -, hcard⟩ := hU
  set v : Valuation L (WithZero (Multiplicative ℤ)) := Valued.v with hv
  set A := v.valuationSubring
  set O := (intL L).toAddSubgroup
  let e : O →+ A :=
    { toFun := fun x => ⟨x.1, x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let f : O →+ A ⧸ IsLocalRing.maximalIdeal A :=
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)).toAddMonoidHom.comp e
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨⟨a.1, a.2⟩, rfl⟩
  have hϖ1 : v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ1
    exact WithZero.exp_ne_zero hϖ1.symm
  have hker : (O.map (AddMonoidHom.mulLeft ϖ)).addSubgroupOf O = f.ker := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker]
    change _ ↔ Ideal.Quotient.mk _ (e x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Valuation.mem_maximalIdeal_iff]
    change _ ↔ v x.1 < 1
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hy1 : v y ≤ 1 := hy
      rw [← hxy, AddMonoidHom.coe_mulLeft, map_mul, hϖ1]
      calc WithZero.exp (-1 : ℤ) * v y ≤ WithZero.exp (-1 : ℤ) * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact (lt_one_iff_le_exp_neg_one _).2 le_rfl
    · intro hx
      refine ⟨ϖ⁻¹ * x.1, ?_, ?_⟩
      · show v (ϖ⁻¹ * x.1) ≤ 1
        rw [map_mul, map_inv₀, hϖ1, ← WithZero.exp_neg, neg_neg]
        calc WithZero.exp (1 : ℤ) * v x.1 ≤ WithZero.exp (1 : ℤ) * WithZero.exp (-1 : ℤ) :=
              by gcongr; exact (lt_one_iff_le_exp_neg_one _).1 hx
          _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
      · rw [AddMonoidHom.coe_mulLeft]
        show ϖ * (ϖ⁻¹ * x.1) = x.1
        rw [← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]
  rw [AddSubgroup.relIndex, hker, AddSubgroup.index_eq_card,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  exact hcard
end GlobalTheory.SatakeWeyl
