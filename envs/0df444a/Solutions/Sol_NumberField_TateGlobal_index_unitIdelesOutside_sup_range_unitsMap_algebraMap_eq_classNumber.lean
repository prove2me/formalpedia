-- Prove2me | solution 1 for NumberField.TateGlobal.index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/6743edb3-978d-583a-a523-f43e52de4474

import Theorems.Thm_IsDedekindDomain_FiniteAdeleRing_nonempty_classGroup_mulEquiv_units_quotient_unitIdeles_sup_range
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber.NumberField IsDedekindDomain"

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing place AdeleRing classNumber AdeleRing.unitIdelesOutside"
namespace TateGlobal
namespace IdeleClassNumber
p2m_open "NumberField.TateGlobal NumberField"

variable (K : Type) [Field K] [NumberField K]

abbrev proj : (AdeleRing (𝓞 K) K)ˣ →* (FiniteAdeleRing (𝓞 K) K)ˣ :=
  Units.map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).toMonoidHom

def lift (y : (FiniteAdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K)ˣ where
  val := ((1 : InfiniteAdeleRing K), (y : FiniteAdeleRing (𝓞 K) K))
  inv := ((1 : InfiniteAdeleRing K), ((y⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K))
  val_inv := Prod.ext (mul_one _) y.mul_inv
  inv_val := Prod.ext (mul_one _) y.inv_mul

theorem proj_lift (y : (FiniteAdeleRing (𝓞 K) K)ˣ) : proj K (lift K y) = y := Units.ext rfl

theorem proj_surjective : Function.Surjective (proj K) := fun y => ⟨lift K y, proj_lift K y⟩

theorem proj_unitsMap (k : Kˣ) :
    proj K (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k) =
      Units.map (algebraMap K (FiniteAdeleRing (𝓞 K) K) : K →* FiniteAdeleRing (𝓞 K) K) k :=
  Units.ext rfl

theorem sup_eq_comap :
    NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (∅ : Set (HeightOneSpectrum (𝓞 K))) ⊔
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range =
    (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 K) K ⊔
      (Units.map (algebraMap K (FiniteAdeleRing (𝓞 K) K) : K →* FiniteAdeleRing (𝓞 K) K)).range).comap
      (proj K) := by
  have hU : NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (∅ : Set (HeightOneSpectrum (𝓞 K))) =
      (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 K) K).comap (proj K) := by
    rw [← IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside_empty]
    rfl
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rw [hU]
      exact Subgroup.comap_mono le_sup_left
    · rintro _ ⟨k, rfl⟩
      rw [Subgroup.mem_comap, proj_unitsMap]
      exact Subgroup.mem_sup_right ⟨k, rfl⟩
  · intro x hx
    rw [Subgroup.mem_comap] at hx
    obtain ⟨u, hu, _, ⟨k, rfl⟩, huk⟩ := Subgroup.mem_sup.1 hx
    have hxk : x * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k)⁻¹ ∈
        NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (∅ : Set (HeightOneSpectrum (𝓞 K))) := by
      rw [hU, Subgroup.mem_comap, map_mul, map_inv, proj_unitsMap, ← huk, mul_inv_cancel_right]
      exact hu
    have : x = x * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k)⁻¹ *
        Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k := by
      rw [inv_mul_cancel_right]
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left hxk) (Subgroup.mem_sup_right ⟨k, rfl⟩)

end NumberField.TateGlobal.IdeleClassNumber

end

open NumberField.TateGlobal.IdeleClassNumber in
theorem solution
    (K : Type) [Field K] [NumberField K] :
    (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (∅ : Set (HeightOneSpectrum (𝓞 K))) ⊔
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range).index =
      NumberField.classNumber K := by
  obtain ⟨e⟩ :=
    IsDedekindDomain.FiniteAdeleRing.nonempty_classGroup_mulEquiv_units_quotient_unitIdeles_sup_range (𝓞 K) K
  rw [sup_eq_comap, Subgroup.index_comap_of_surjective _ (proj_surjective K), Subgroup.index_eq_card,
    ← Nat.card_congr e.toEquiv, NumberField.classNumber, Nat.card_eq_fintype_card]

end S_NumberField_TateGlobal_index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber
end P2MW
export P2MW.S_NumberField_TateGlobal_index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber (solution)
