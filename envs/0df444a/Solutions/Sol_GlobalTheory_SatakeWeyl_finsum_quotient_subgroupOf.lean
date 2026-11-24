-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.finsum_quotient_subgroupOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:32:57.352696+00:00
-- url     : https://prove2.me/submissions/43f25160-6496-48fc-a3b8-c0d6e2782e41

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexCosetSumUnimodularityOfFiniteIndex
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl
namespace GlobalTheory.SatakeWeyl
theorem _root_.solution {A : Type} [Group A] (Γ W : Subgroup A) (F : A → ℂ)
    (hΓ : ∀ a, F a ≠ 0 → a ∈ Γ) (hF : ∀ w ∈ W, ∀ a, F (a * w) = F a) :
    ∑ᶠ y : A ⧸ W, F y.out = ∑ᶠ y : Γ ⧸ W.subgroupOf Γ, F (y.out : Γ) := by
  have hout : ∀ a : A, F (QuotientGroup.mk a : A ⧸ W).out = F a := by
    intro a
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul W a
    rw [hw, hF w w.2]
  let e : Γ ⧸ W.subgroupOf Γ → A ⧸ W := fun y => QuotientGroup.mk ((y.out : Γ) : A)
  have hinj : Function.Injective e := by
    intro y z h
    have h1 : ((y.out : Γ) : A)⁻¹ * ((z.out : Γ) : A) ∈ W := QuotientGroup.eq.1 h
    have h2 : (QuotientGroup.mk y.out : Γ ⧸ W.subgroupOf Γ) = QuotientGroup.mk z.out :=
      QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 (by simpa using h1))
    simpa using h2
  have hsupp : (Function.support fun y : A ⧸ W => F y.out) ⊆ Set.range e := by
    intro y hy
    have hm : y.out ∈ Γ := hΓ _ hy
    refine ⟨QuotientGroup.mk ⟨y.out, hm⟩, ?_⟩
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (W.subgroupOf Γ) ⟨y.out, hm⟩
    have hw' : ((w : Γ) : A) ∈ W := Subgroup.mem_subgroupOf.1 w.2
    show (QuotientGroup.mk _ : A ⧸ W) = y
    rw [hw, Subgroup.coe_mul, QuotientGroup.mk_mul_of_mem _ hw']
    exact QuotientGroup.out_eq' y
  calc ∑ᶠ y : A ⧸ W, F y.out = ∑ᶠ y ∈ Set.range e, F y.out := by
        rw [← finsum_mem_univ]
        apply finsum_mem_inter_support_eq
        rw [Set.univ_inter, Set.inter_eq_right.2 hsupp]
    _ = ∑ᶠ y, F (e y).out := finsum_mem_range hinj
    _ = _ := finsum_congr fun y => hout _
end GlobalTheory.SatakeWeyl
