-- Prove2me | solution 1 for NumberField.AdeleRing.exists_isOpen_inter_principalIdeles_eq_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/ba3c9f8c-2bad-54fa-b9d4-a7d0f36da52c

import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdeleRing_exists_isOpen_inter_principalIdeles_eq_singleton

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_AdeleRing_exists_isOpen_inter_principalIdeles_eq_singleton.NumberField"

section Fold_PrincipalIdelesDiscrete

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_AdeleRing_exists_isOpen_inter_principalIdeles_eq_singleton.NumberField IsDedekindDomain"

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing AdeleRing.algebraMap_snd_apply AdeleRing.algebraMap_injective place InfiniteAdeleRing.coe_norm_eq_abs_norm AdeleRing InfiniteAdeleRing.norm_def InfiniteAdeleRing.norm_eq_zero_of_not_isUnit"
namespace FujisakiVocab
p2m_open "NumberField"

variable (F : Type) [Field F] [NumberField F]

theorem continuous_infiniteAdeleNorm :
    Continuous (fun y : InfiniteAdeleRing F => ‖y‖) := by
  simp only [InfiniteAdeleRing.norm_def]
  exact continuous_finsetProd _ fun w _ =>
    (continuous_apply w).norm.pow _

theorem isOpen_finiteIntegralAdeles :
    IsOpen {b : FiniteAdeleRing (𝓞 F) F |
      ∀ v : HeightOneSpectrum (𝓞 F), b v ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem (fun _ => Valued.isOpen_valuationSubring _)

def adelicZeroNbhd : Set (AdeleRing (𝓞 F) F) :=
  {a | ‖a.1‖ < 1} ∩
    Prod.snd ⁻¹' {b : FiniteAdeleRing (𝓞 F) F |
      ∀ v : HeightOneSpectrum (𝓞 F), b v ∈ v.adicCompletionIntegers F}

theorem isOpen_adelicZeroNbhd : IsOpen (adelicZeroNbhd F) := by
  refine IsOpen.inter ?_ ?_
  · exact isOpen_lt ((continuous_infiniteAdeleNorm F).comp continuous_fst) continuous_const
  · exact IsOpen.preimage continuous_snd (isOpen_finiteIntegralAdeles F)

theorem zero_mem_adelicZeroNbhd : (0 : AdeleRing (𝓞 F) F) ∈ adelicZeroNbhd F := by
  refine ⟨?_, fun v => ?_⟩
  · show ‖(0 : InfiniteAdeleRing F)‖ < 1
    rw [InfiniteAdeleRing.norm_eq_zero_of_not_isUnit not_isUnit_zero]
    exact zero_lt_one
  · show (0 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F
    exact zero_mem _

theorem adelicZeroNbhd_inter_principal :
    adelicZeroNbhd F ∩ (algebraMap F (AdeleRing (𝓞 F) F)).range = {0} := by
  ext a
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨harch, hfin⟩, x, rfl⟩
    simp only [Set.mem_setOf_eq, Set.mem_preimage] at harch hfin
    have hxint : x ∈ (algebraMap (𝓞 F) F).range := by
      refine HeightOneSpectrum.mem_integers_of_valuation_le_one F x fun v => ?_
      have hv := hfin v
      rw [AdeleRing.algebraMap_snd_apply] at hv
      rwa [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x,
        ← HeightOneSpectrum.mem_adicCompletionIntegers]
    obtain ⟨r, rfl⟩ := hxint
    have harch' : ‖algebraMap F (InfiniteAdeleRing F) (algebraMap (𝓞 F) F r)‖ < 1 := harch
    rw [InfiniteAdeleRing.coe_norm_eq_abs_norm, ← Algebra.coe_norm_int] at harch'
    have hN : |Algebra.norm ℤ r| < 1 := by exact_mod_cast harch'
    simp [Algebra.norm_eq_zero_iff.mp (Int.abs_lt_one_iff.mp hN)]
  · rintro rfl
    exact ⟨zero_mem_adelicZeroNbhd F, 0, map_zero _⟩

end NumberField.FujisakiVocab

end

end Fold_PrincipalIdelesDiscrete

theorem solution
    (F : Type) [Field F] [NumberField F] :
    ∃ V : Set (AdeleRing (𝓞 F) F)ˣ, IsOpen V ∧
      V ∩ (M4aHerbrand.principalIdeles (𝓞 F) F : Set (AdeleRing (𝓞 F) F)ˣ) = {1} := by
  set W : Set (AdeleRing (𝓞 F) F) := (· - 1) ⁻¹' NumberField.FujisakiVocab.adelicZeroNbhd F with hWdef
  have hWopen : IsOpen W :=
    IsOpen.preimage (continuous_sub_right 1) (NumberField.FujisakiVocab.isOpen_adelicZeroNbhd F)
  set V : Set (AdeleRing (𝓞 F) F)ˣ :=
    (Units.val : (AdeleRing (𝓞 F) F)ˣ → AdeleRing (𝓞 F) F) ⁻¹' W with hVdef
  have hVopen : IsOpen V := IsOpen.preimage Units.continuous_val hWopen
  have hV1 : (1 : (AdeleRing (𝓞 F) F)ˣ) ∈ V := by
    show ((1 : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) - 1 ∈ NumberField.FujisakiVocab.adelicZeroNbhd F
    rw [Units.val_one, sub_self]
    exact NumberField.FujisakiVocab.zero_mem_adelicZeroNbhd F
  have hVP : ∀ p ∈ M4aHerbrand.principalIdeles (𝓞 F) F, p ∈ V → p = 1 := by
    intro p hp hpV
    obtain ⟨a, ha⟩ := hp
    have hav : ((p : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) =
        algebraMap F (AdeleRing (𝓞 F) F) (a : F) := by
      rw [← ha]; rfl
    have hm : algebraMap F (AdeleRing (𝓞 F) F) ((a : F) - 1) ∈
        NumberField.FujisakiVocab.adelicZeroNbhd F ∩ (algebraMap F (AdeleRing (𝓞 F) F)).range := by
      refine ⟨?_, (a : F) - 1, rfl⟩
      have hpW : ((p : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) - 1 ∈
          NumberField.FujisakiVocab.adelicZeroNbhd F := hpV
      rw [hav] at hpW
      simpa only [map_sub, map_one] using hpW
    rw [NumberField.FujisakiVocab.adelicZeroNbhd_inter_principal, Set.mem_singleton_iff,
      map_eq_zero_iff _ (AdeleRing.algebraMap_injective (𝓞 F) F), sub_eq_zero] at hm
    apply Units.ext
    rw [hav, hm, map_one, Units.val_one]
  refine ⟨V, hVopen, ?_⟩
  ext p
  simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hpV, hp⟩
    exact hVP p hp hpV
  · rintro rfl
    exact ⟨hV1, one_mem _⟩

end S_NumberField_AdeleRing_exists_isOpen_inter_principalIdeles_eq_singleton
end P2MW
export P2MW.S_NumberField_AdeleRing_exists_isOpen_inter_principalIdeles_eq_singleton (solution)
