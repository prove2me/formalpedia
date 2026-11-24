-- Prove2me | solution 1 for GlobalTheory.CMVal.ValEx.exists_locMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:21:35.807811+00:00
-- url     : https://prove2.me/submissions/6eeafa27-c3ae-495d-bb9d-e2fe4fc542a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Theorems.Thm_GlobalTheory_CMVal_ValEx_continuous_of_val
import Theorems.Thm_GlobalTheory_CMVal_ValEx_continuous_val
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
open WithZeroTopology
namespace GlobalTheory.CMVal.ValEx
theorem _root_.solution (σ : E ≃+* E) (w w' : HeightOneSpectrum (𝓞 E)) (h : ∀ y, w'.valuation E y = w.valuation E (σ y)) :
    ∃ c : w'.adicCompletion E →+* w.adicCompletion E, Continuous c ∧
      (∀ y, c (algebraMap E _ y) = algebraMap E _ (σ y)) ∧ ∀ x, Valued.v (c x) = Valued.v x := by
  have hc : Continuous (WithVal.map (w'.valuation E) (w.valuation E) σ.toRingHom) :=
    continuous_of_val (fun γ => by
      obtain ⟨y, hy⟩ := w'.valuation_surjective E γ
      exact ⟨WithVal.toVal _ y, hy⟩) _ (fun x => (h x.ofVal).symm)
  let c : w'.adicCompletion E →+* w.adicCompletion E :=
    ((HeightOneSpectrum.adicCompletion.equiv E w).symm.toRingHom.comp
      (UniformSpace.Completion.mapRingHom _ hc)).comp (HeightOneSpectrum.adicCompletion.equiv E w').toRingHom
  have hcc : Continuous c := (HeightOneSpectrum.adicCompletion.continuous_ofCompletion E w).comp
    (UniformSpace.Completion.continuous_map.comp (HeightOneSpectrum.adicCompletion.continuous_toCompletion E w'))
  have ha : ∀ y, c (algebraMap E _ y) = algebraMap E _ (σ y) := fun y => by
    apply HeightOneSpectrum.adicCompletion.ext
    exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ y)
  refine ⟨c, hcc, ha, fun x => ?_⟩
  refine congrFun ((w'.denseRange_algebraMap E).equalizer ((continuous_val w).comp hcc) (continuous_val w') ?_) x
  funext y
  simp only [Function.comp_apply, ha]
  exact (w.valuedAdicCompletion_eq_valuation' (σ y)).trans ((h y).symm.trans (w'.valuedAdicCompletion_eq_valuation' y).symm)
end GlobalTheory.CMVal.ValEx
