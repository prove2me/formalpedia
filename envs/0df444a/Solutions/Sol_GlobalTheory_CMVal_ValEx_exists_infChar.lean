-- Prove2me | solution 1 for GlobalTheory.CMVal.ValEx.exists_infChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:21:34.923008+00:00
-- url     : https://prove2.me/submissions/41f0fc8b-d2b0-44c8-81b4-415f8f1e2192

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Theorems.Thm_GlobalTheory_CMVal_ValEx_exists_infExt
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.ValEx
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.ValEx
theorem _root_.solution {I : Type} [Fintype I] (φ : I → E →+* ℂ) (m : I → ℤ) :
    ∃ ψ : (InfiniteAdeleRing E)ˣ →* ℂˣ, Continuous ψ ∧ (∀ x, ‖((ψ x : ℂˣ) : ℂ)‖ = 1) ∧
      (∀ k : Eˣ, ((ψ (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k) : ℂˣ) : ℂ) =
        ∏ i, (φ i (k : E) / starRingEnd ℂ (φ i (k : E))) ^ m i) ∧
      ∀ k : E, k ∈ maximalRealSubfield E → ∀ x : (InfiniteAdeleRing E)ˣ,
        (∀ w, x.1 w = (1 : InfiniteAdeleRing E) w ∨ x.1 w = algebraMap E (InfiniteAdeleRing E) k w) → ψ x = 1 := by
  choose e he he' he2 using fun i => exists_infExt (φ i)
  let ψ : (InfiniteAdeleRing E)ˣ →* ℂˣ :=
    ∏ i, (Units.map (e i).toMonoidHom / Units.map ((starRingEnd ℂ).comp (e i)).toMonoidHom) ^ m i
  have h0 : ∀ x, ψ x = ∏ i, (Units.map (e i).toMonoidHom x / Units.map ((starRingEnd ℂ).comp (e i)).toMonoidHom x) ^ m i :=
    fun x => by simp only [ψ, MonoidHom.finsetProd_apply]; rfl
  have h1 : ∀ x, (ψ x : ℂ) = ∏ i, (e i x / starRingEnd ℂ (e i x)) ^ m i := fun x => by
    rw [h0]; simp
  refine ⟨ψ, ?_, fun x => ?_, fun k => ?_, fun k hk x hx => Units.ext ?_⟩
  · rw [show (ψ : _ → _) = _ from funext h0]
    exact continuous_finsetProd _ fun i _ =>
      ((Continuous.units_map _ (he i)).div' (Continuous.units_map _ (Complex.continuous_conj.comp (he i)))).zpow _
  · rw [h1, norm_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    have : e i x ≠ 0 := (x.isUnit.map (e i)).ne_zero
    rw [norm_zpow, norm_div, Complex.norm_conj, div_self (by simpa using this), one_zpow]
  · rw [h1]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← he']; rfl
  · rw [h1]
    refine Finset.prod_eq_one fun i _ => ?_
    have h2 : e i x ≠ 0 := (x.isUnit.map (e i)).ne_zero
    have h3 : starRingEnd ℂ (e i x) = e i x := by
      rcases hx (InfinitePlace.mk (φ i)) with h | h
      · rw [he2 i _ _ h, map_one, map_one]
      · rw [he2 i _ _ h, he']; exact hk (φ i)
    rw [h3, div_self h2, one_zpow]
end GlobalTheory.CMVal.ValEx
