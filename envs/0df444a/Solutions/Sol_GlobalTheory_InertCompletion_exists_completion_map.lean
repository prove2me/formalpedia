-- Prove2me | solution 1 for GlobalTheory.InertCompletion.exists_completion_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:41:52.63199+00:00
-- url     : https://prove2.me/submissions/83bf07ef-e716-4260-8cb0-b71c929a91c5

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsFieldAdicCompletionTensorOfInert
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsRingEquivTensorInertAdicCompletion
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.InertCompletion
open scoped WithZeroTopology
namespace GlobalTheory.InertCompletion
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (h : IsInertAt F E v P) :
    ∃ φ : v.adicCompletion F →+* P.adicCompletion E, Continuous φ ∧
      (∀ x : F, φ (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)) ∧
      ∀ x, Valued.v (φ x) = Valued.v x := by
  have h' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal := h
  have : P.asIdeal.LiesOver v.asIdeal := ⟨v.isMaximal.eq_of_le
    (Ideal.comap_ne_top _ P.isPrime.ne_top) (h' ▸ Ideal.le_comap_map)⟩
  have he : Ideal.ramificationIdx' v.asIdeal P.asIdeal = 1 := by
    by_contra hne
    have := (Ideal.ramificationIdx'_ne_one_iff h'.le).1 hne
    rw [h'] at this
    exact absurd this (not_le_of_gt (Ideal.pow_lt_self _ P.ne_bot P.isPrime.ne_top 2 le_rfl))
  have hc := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver F E v P).continuous
  let φ : v.adicCompletion F →+* P.adicCompletion E :=
    ((HeightOneSpectrum.adicCompletion.equiv E P).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation F)) (WithVal (P.valuation E))) hc)).comp
      (HeightOneSpectrum.adicCompletion.equiv F v).toRingHom
  have hφ : ∀ x : F, φ (algebraMap F _ x) = algebraMap E _ (algebraMap F E x) := fun x => by
    apply HeightOneSpectrum.adicCompletion.ext
    exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)
  have hcont : Continuous φ :=
    (HeightOneSpectrum.adicCompletion.continuous_ofCompletion E P).comp
      ((UniformSpace.Completion.continuous_map
        (f := algebraMap (WithVal (v.valuation F)) (WithVal (P.valuation E)))).comp
        (HeightOneSpectrum.adicCompletion.continuous_toCompletion F v))
  refine ⟨φ, hcont, hφ, fun x => ?_⟩
  refine (HeightOneSpectrum.denseRange_algebraMap F v).induction_on
    (p := fun x => Valued.v (φ x) = Valued.v x) x
    (isClosed_eq
      ((Valued.continuous_valuation_of_surjective (P.valuedAdicCompletion_surjective E)).comp hcont)
      (Valued.continuous_valuation_of_surjective (v.valuedAdicCompletion_surjective F))) fun k => ?_
  rw [hφ, Idele.valued_algebraMap, Idele.valued_algebraMap,
    ← HeightOneSpectrum.valuation_liesOver E v P, he, pow_one]
end GlobalTheory.InertCompletion
