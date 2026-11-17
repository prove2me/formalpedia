-- Prove2me | solution 1 for NumberField.finrank_dvd_classNumber_of_unramified_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:55:59.1937+00:00
-- url     : https://prove2.me/submissions/c373ffce-0125-43e4-936f-e17e3c364f91

import Theorems.Thm_M4aHerbrand_exists_adeleBaseChange_normCoset_index_ne_zero_and_finrank_dvd
import Theorems.Thm_M4aHerbrand_unitIdele_mem_idelicNorm_range
import Theorems.Thm_NumberField_TateGlobal_index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber

set_option autoImplicit false

open NumberField IsDedekindDomain M4aHerbrand

namespace NumberField

/-- An everywhere unramified cyclic extension has degree dividing the class
number. The proof uses the idelic norm index and the ordinary class-group index. -/
theorem _root_.solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (hfinite : ∀ v : HeightOneSpectrum (𝓞 K),
      (LanglandsTunnell.P2.Artin.primeAbove K L v).inertia (L ≃ₐ[K] L) = ⊥)
    (hinfinite : ∀ w : InfinitePlace K, w.IsUnramifiedIn L) :
    Module.finrank K L ∣ classNumber K := by
  obtain ⟨B, _, hdegree⟩ :=
    exists_adeleBaseChange_normCoset_index_ne_zero_and_finrank_dvd K L
  have hunits : AdeleRing.unitIdelesOutside (𝓞 K) K ∅ ≤ B.idelicNorm.range := by
    intro u hu
    apply unitIdele_mem_idelicNorm_range K L B u
    · intro v
      have hp := hu v (by simp)
      change Valued.v (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) ≤ 1 ∧
        Valued.v ((((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 :
          FiniteAdeleRing (𝓞 K) K) v) ≤ 1 at hp
      apply le_antisymm hp.1
      have hm := congrArg
        (fun z : AdeleRing (𝓞 K) K => (z.2 : FiniteAdeleRing (𝓞 K) K) v) u.val_inv
      have hv := congrArg (fun z => Valued.v z) hm
      change Valued.v
        ((((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) *
          ((((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 :
            FiniteAdeleRing (𝓞 K) K) v)) = Valued.v (1 : v.adicCompletion K) at hv
      rw [map_mul, map_one] at hv
      calc
        1 = _ := hv.symm
        _ ≤ _ * 1 := by gcongr; exact hp.2
        _ = _ := mul_one _
    · intro v hv
      exact (hv (hfinite v)).elim
    · intro w _ hw
      exact (hw (hinfinite w)).elim
  have hle : AdeleRing.unitIdelesOutside (𝓞 K) K ∅ ⊔ principalIdeles (𝓞 K) K ≤
      principalIdeles (𝓞 K) K ⊔ B.idelicNorm.range :=
    sup_le (le_trans hunits le_sup_right) le_sup_left
  have hindex := Subgroup.index_dvd_of_le hle
  have hclass :
      (AdeleRing.unitIdelesOutside (𝓞 K) K ∅ ⊔ principalIdeles (𝓞 K) K).index =
        classNumber K :=
    TateGlobal.index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber K
  rw [hclass] at hindex
  exact dvd_trans hdegree hindex

end NumberField
