-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.Window.exists_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:02.505443+00:00
-- url     : https://prove2.me/submissions/522b325e-e435-4919-a237-ff91620809fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlternatingDifferenceTermWindow
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_al_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology Classical
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc GlobalTheory.UnitLemma.Desc.Window
variable {K : UQ} (B : InvAlg K) {ι : Type}
namespace GlobalTheory.UnitLemma.Desc.Window
theorem _root_.solution {a : K.O} (ha : K.Small a) {t : K.E} (ht : t ≠ 0) :
    ∃ C : ℕ, ∀ m : ℤ, al K a ^ m * t ∈ (algebraMap K.O K.E).range → -(C : ℤ) ≤ m := by
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := K.O) t
  have hd0 : algebraMap K.O K.E d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  have hn0 : n ≠ 0 := by rintro rfl; simp at ht
  have hnu : ¬ IsUnit a := fun hu => (IsLocalRing.mem_maximalIdeal a).1 ha.2.1 hu
  obtain ⟨C, hC⟩ := FiniteMultiplicity.of_not_isUnit hnu hn0
  refine ⟨C, fun m hm => ?_⟩
  by_contra hlt
  push_neg at hlt
  obtain ⟨b, hb⟩ := hm
  obtain ⟨j, hj⟩ : ∃ j : ℕ, m = -(j : ℤ) := ⟨(-m).toNat, by omega⟩
  apply hC
  have hjC : C + 1 ≤ j := by omega
  refine (pow_dvd_pow a hjC).trans ⟨d * b, ?_⟩
  apply IsFractionRing.injective K.O K.E
  have hα := al_ne_zero ha
  rw [hj, zpow_neg, zpow_natCast] at hb
  rw [map_mul, map_mul, map_pow, hb]
  field_simp
end GlobalTheory.UnitLemma.Desc.Window
