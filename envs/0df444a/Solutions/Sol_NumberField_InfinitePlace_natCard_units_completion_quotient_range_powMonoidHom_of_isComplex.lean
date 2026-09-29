-- Prove2me | solution 1 for NumberField.InfinitePlace.natCard_units_completion_quotient_range_powMonoidHom_of_isComplex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/1ca0bc21-01c7-57fe-b871-7a33bc5377de

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_InfinitePlace_natCard_units_completion_quotient_range_powMonoidHom_of_isComplex

set_option autoImplicit false

theorem P2mS26ArchPowC.index_range_powMonoidHom_congr {G H : Type*} [CommGroup G] [CommGroup H] (φ : G ≃* H) (n : ℕ) :
    (powMonoidHom n : G →* G).range.index = (powMonoidHom n : H →* H).range.index := by
  rw [← Subgroup.index_map_of_bijective (f := φ.toMonoidHom) φ.bijective, ← MonoidHom.range_comp]
  have hc : φ.toMonoidHom.comp (powMonoidHom n) = (powMonoidHom n).comp φ.toMonoidHom := by
    ext x; simp
  rw [hc, MonoidHom.range_comp, MonoidHom.range_eq_top.2 φ.surjective, ← MonoidHom.range_eq_map]

theorem P2mS26ArchPowC.range_powMonoidHom_units_eq_top_of_isAlgClosed (F : Type*) [Field F] [IsAlgClosed F]
    {n : ℕ} (hn : 0 < n) : (powMonoidHom n : Fˣ →* Fˣ).range = ⊤ := by
  rw [eq_top_iff]
  rintro u -
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : F) hn
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hz
    exact u.ne_zero hz.symm
  refine ⟨Units.mk0 z hz0, ?_⟩
  ext
  simp [hz]

theorem solution {K : Type*} [Field K]
    (w : NumberField.InfinitePlace K) (hw : w.IsComplex) {n : ℕ} (hn : 0 < n) :
    Nat.card ((w.Completion)ˣ ⧸ (powMonoidHom n : (w.Completion)ˣ →* (w.Completion)ˣ).range) = 1 := by
  rw [← Subgroup.index_eq_card,
    P2mS26ArchPowC.index_range_powMonoidHom_congr
      (Units.mapEquiv (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).toMulEquiv) n,
    P2mS26ArchPowC.range_powMonoidHom_units_eq_top_of_isAlgClosed ℂ hn, Subgroup.index_top]

end S_NumberField_InfinitePlace_natCard_units_completion_quotient_range_powMonoidHom_of_isComplex
end P2MW
export P2MW.S_NumberField_InfinitePlace_natCard_units_completion_quotient_range_powMonoidHom_of_isComplex (solution)
