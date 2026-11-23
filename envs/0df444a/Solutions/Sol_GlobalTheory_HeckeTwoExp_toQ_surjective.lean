-- Prove2me | solution 1 for GlobalTheory.HeckeTwoExp.toQ_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:13:45.562981+00:00
-- url     : https://prove2.me/submissions/c9db9d94-c7ce-4001-84e7-b2925306884d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormEqProd
import Theorems.Thm_GlobalTheory_HeckeTwoExp_emb_nonempty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoExp
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeTwoExp
theorem _root_.solution [IsTotallyReal F] (𝔞 𝔟 : Frac F) : Function.Surjective (toQ 𝔞 𝔟) := by
  intro q
  induction q using Quotient.inductionOn with
  | h p => ?_
  obtain ⟨⟨ν, b⟩, hν, hb, hpos⟩ := p
  obtain ⟨τ₀⟩ := emb_nonempty (F := F)
  have hνb : ν * b ≠ 0 := by
    intro h0; have := hpos τ₀; rw [h0, map_zero] at this; exact lt_irrefl _ this
  have hb0 : b ≠ 0 := right_ne_zero_of_mul hνb
  have hν0 : ν ≠ 0 := left_ne_zero_of_mul hνb
  set c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) := Quotient.mk _ ⟨b, hb, hb0⟩ with hcdef
  obtain ⟨ε, hε⟩ := Quotient.exact (Quotient.out_eq c : Quotient.mk _ c.out = Quotient.mk _ ⟨b, hb, hb0⟩)
  dsimp only at hε
  have hmem : ((ε : 𝓞 F) : F) * ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := by
    have := Submodule.smul_mem (𝔞 : FractionalIdeal (𝓞 F)⁰ F).coeToSubmodule (ε : 𝓞 F) hν
    rw [Algebra.smul_def] at this
    exact this
  have hne : ((ε : 𝓞 F) : F) * ν ≠ 0 := by
    refine mul_ne_zero ?_ hν0
    intro h0
    have := unit_inv_mul ε; rw [h0, mul_zero] at this; exact zero_ne_one this
  have hprod : ((ε : 𝓞 F) : F) * ν * c.out.1 = ν * b := by rw [hε]; ring
  refine ⟨⟨c, ⟨⟨((ε : 𝓞 F) : F) * ν, hmem, hne⟩, fun τ => by rw [hprod]; exact hpos τ⟩⟩, ?_⟩
  apply Quotient.sound
  refine ⟨ε, ?_, hε⟩
  show ν = _ * (((ε : 𝓞 F) : F) * ν)
  rw [← mul_assoc, unit_inv_mul, one_mul]
end GlobalTheory.HeckeTwoExp
