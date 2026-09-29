-- Prove2me | solution 1 for LanglandsTunnell.P2.Artin.unitIdeles_le_range_idelicNorm_of_isAdmissibleModulusOfDegree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/a01cf57f-4390-534d-a2b7-53b4e7f2faac

import Mathlib
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Theorems.Thm_M4aHerbrand_unitIdele_mem_idelicNorm_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_P2_Artin_unitIdeles_le_range_idelicNorm_of_isAdmissibleModulusOfDegree
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin Deep.NTSupply
open scoped IsMulCommutative

theorem solution
    (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (𝔣 : Ideal (𝓞 E)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣) :
    unitIdeles E 𝔣 ≤ ((genuineBaseChange E F).idelicNorm).range := by
  classical
  intro u hu
  refine M4aHerbrand.unitIdele_mem_idelicNorm_range E F (genuineBaseChange E F) u
    (fun v => hu.1 v) ?_ ?_
  ·
    intro v hv
    have hdvd : v.asIdeal ^ NumberField.NormIndex.admissibleExpOfDegree E (Module.finrank E F) v ∣ 𝔣 := hadm.2 v hv
    have hane : NumberField.NormIndex.admissibleExpOfDegree E (Module.finrank E F) v ≠ 0 := by
      unfold NumberField.NormIndex.admissibleExpOfDegree; omega
    have hv𝔣 : v.asIdeal ∣ 𝔣 := (dvd_pow_self v.asIdeal hane).trans hdvd
    refine le_trans (hu.2.1 v hv𝔣) ?_
    rw [WithZero.exp_le_exp, neg_le_neg_iff]
    have hcount : NumberField.NormIndex.admissibleExpOfDegree E (Module.finrank E F) v
        ≤ (Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors := by
      rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hadm.1) (Associates.irreducible_mk.mpr v.irreducible),
        ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd]
      exact hdvd
    unfold NumberField.NormIndex.admissibleExpOfDegree at hcount
    exact_mod_cast hcount
  ·
    intro w hw _
    have key : ∀ (τ : E →+* ℝ) (w' : InfinitePlace E) (hw' : w'.IsReal), placeOf E τ = w' →
        0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw'
          (((u : AdeleRing (𝓞 E) E).1 : InfiniteAdeleRing E) w') := by
      rintro τ w' hw' rfl
      exact hu.2.2 τ
    refine key (InfinitePlace.embedding_of_isReal hw) w hw ?_
    show InfinitePlace.mk _ = w
    conv_rhs => rw [← InfinitePlace.mk_embedding w]
    congr 1
    ext x
    exact InfinitePlace.embedding_of_isReal_apply hw x

end S_LanglandsTunnell_P2_Artin_unitIdeles_le_range_idelicNorm_of_isAdmissibleModulusOfDegree
end P2MW
export P2MW.S_LanglandsTunnell_P2_Artin_unitIdeles_le_range_idelicNorm_of_isAdmissibleModulusOfDegree (solution)
