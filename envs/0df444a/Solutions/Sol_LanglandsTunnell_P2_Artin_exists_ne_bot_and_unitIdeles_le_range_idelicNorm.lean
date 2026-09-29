-- Prove2me | solution 1 for LanglandsTunnell.P2.Artin.exists_ne_bot_and_unitIdeles_le_range_idelicNorm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/1a2b938c-80a6-54d3-bc5f-7ff9a7fa1bba

import Mathlib
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_AdeleBaseChange
import Theorems.Thm_M4aHerbrand_unitIdele_mem_idelicNorm_range
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_ne_bot_forall_inertia_primeAbove_ne_bot_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_P2_Artin_exists_ne_bot_and_unitIdeles_le_range_idelicNorm
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open NumberField IsDedekindDomain M4aHerbrand.GenuineDescent Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped IsMulCommutative

namespace DeepModulusAux

variable (F : Type*) [Field F] [NumberField F]

omit [NumberField F] in

theorem placeOf_embedding_of_isReal (w : InfinitePlace F) (hw : w.IsReal) :
    placeOf F (InfinitePlace.embedding_of_isReal hw) = w := by
  have h : Complex.ofRealHom.comp (InfinitePlace.embedding_of_isReal hw) = w.embedding := by
    ext x
    exact InfinitePlace.embedding_of_isReal_apply hw x
  unfold placeOf
  rw [h, InfinitePlace.mk_embedding]

theorem extensionEmbeddingOfIsReal_pos_of_mem_unitIdeles {𝔪 : Ideal (𝓞 F)} {u : (AdeleRing (𝓞 F) F)ˣ}
    (hu : u ∈ unitIdeles F 𝔪) (w : InfinitePlace F) (hw : w.IsReal) :
    0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (((u : AdeleRing (𝓞 F) F).1 : InfiniteAdeleRing F) w) := by
  have key : ∀ (w' : InfinitePlace F) (hw' : w'.IsReal), w' = placeOf F (InfinitePlace.embedding_of_isReal hw) →
      0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw' (((u : AdeleRing (𝓞 F) F).1 : InfiniteAdeleRing F) w') := by
    rintro w' hw' rfl
    have h := hu.2.2 (InfinitePlace.embedding_of_isReal hw)
    unfold archSign archRealProjTau at h
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply] at h
    exact h
  exact key w hw (placeOf_embedding_of_isReal F w hw).symm

end DeepModulusAux

open DeepModulusAux in
theorem solution
    (F N : Type*) [Field F] [NumberField F] [Field N] [NumberField N] [Algebra F N] [IsGalois F N]
    [IsMulCommutative (N ≃ₐ[F] N)] :
    ∃ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ ∧
      (∀ w : HeightOneSpectrum (𝓞 F), (primeAbove F N w).inertia (N ≃ₐ[F] N) ≠ ⊥ → w.asIdeal ∣ 𝔪) ∧
      unitIdeles F 𝔪 ≤ (genuineBaseChange F N).idelicNorm.range := by
  classical

  let D : HeightOneSpectrum (𝓞 F) → ℕ := fun v =>
    1 + ∑ p ∈ (Module.finrank F N).primeFactors,
      ((Module.finrank F N).factorization p + 1) * Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) v.asIdeal
  have hD : ∀ v, D v ≠ 0 := fun v => by simp only [D]; omega

  obtain ⟨𝔯, h𝔯0, h𝔯⟩ := LanglandsTunnell.P2.Artin.exists_ne_bot_forall_inertia_primeAbove_ne_bot_dvd F N
  have h𝔯0' : 𝔯 ≠ 0 := by rwa [Ne, Submodule.zero_eq_bot]
  set R : Finset (HeightOneSpectrum (𝓞 F)) := (Ideal.finite_factors h𝔯0').toFinset with hR
  have hmemR : ∀ w, w ∈ R ↔ w.asIdeal ∣ 𝔯 := fun w => by rw [hR, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  set 𝔪 : Ideal (𝓞 F) := ∏ w ∈ R, w.asIdeal ^ D w with h𝔪
  have h𝔪0' : 𝔪 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ =>
    pow_ne_zero _ (by rw [Ne, Submodule.zero_eq_bot]; exact w.ne_bot)
  have h𝔪0 : 𝔪 ≠ ⊥ := by rwa [Ne, ← Submodule.zero_eq_bot]
  have hpow : ∀ w ∈ R, w.asIdeal ^ D w ∣ 𝔪 := fun w hw => Finset.dvd_prod_of_mem _ hw
  refine ⟨𝔪, h𝔪0, fun w hw => ?_, fun u hu => ?_⟩
  · exact dvd_trans (dvd_pow_self _ (hD w)) (hpow w ((hmemR w).mpr (h𝔯 w hw)))
  · refine M4aHerbrand.unitIdele_mem_idelicNorm_range F N (genuineBaseChange F N) u (fun v => hu.1 v)
      (fun v hv => ?_) (fun w hw _ => extensionEmbeddingOfIsReal_pos_of_mem_unitIdeles F hu w hw)
    have hvR : v ∈ R := (hmemR v).mpr (h𝔯 v hv)
    have hv𝔪 : v.asIdeal ∣ 𝔪 := dvd_trans (dvd_pow_self _ (hD v)) (hpow v hvR)
    refine le_trans (hu.2.1 v hv𝔪) ?_
    rw [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]
    have h := (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr h𝔪0') v.associates_irreducible).mp
      (by rw [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd]; exact hpow v hvR)
    exact h

end S_LanglandsTunnell_P2_Artin_exists_ne_bot_and_unitIdeles_le_range_idelicNorm
end P2MW
export P2MW.S_LanglandsTunnell_P2_Artin_exists_ne_bot_and_unitIdeles_le_range_idelicNorm (solution)
