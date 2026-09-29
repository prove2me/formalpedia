-- Prove2me | solution 1 for M4aLocalCFT.fieldUnitsDecomp_card_tateH0_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/cc975b70-ab78-5cf2-8187-68ded5e0def3

import Definitions.Def_M4aLocalCFT_VocabDefs
import Theorems.Thm_M4aLocalCFT_fieldUnitsDecomp_herbrandQuotient_eq_card
import Theorems.Thm_M4aLocalCFT_fieldUnitsDecomp_norm_ker_le_derive_range
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aLocalCFT_fieldUnitsDecomp_card_tateH0_eq_card

set_option Elab.async false
set_option autoImplicit false

open M4aLocalCFT in
theorem solution {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal (A : Type _)) A]
    [Finite (IsLocalRing.ResidueField A)]
    [Finite (A.decompositionSubgroup K)]
    (g : A.decompositionSubgroup K) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card ((M4aLocalCFT.fieldUnitsDerive A g).ker ⧸
      ((M4aLocalCFT.fieldUnitsNorm (K := K) A).range.subgroupOf (M4aLocalCFT.fieldUnitsDerive A g).ker)) =
    Nat.card (A.decompositionSubgroup K) := by

  haveI : IsCyclic (A.decompositionSubgroup K) := ⟨g, hg⟩

  obtain ⟨heq, hne⟩ := fieldUnitsDecomp_herbrandQuotient_eq_card K A g hg

  have hker := M4aLocalCFT.fieldUnitsDecomp_norm_ker_le_derive_range A g hg

  have hsub : ((fieldUnitsDerive A g).range.subgroupOf
      (fieldUnitsNorm (K := K) A).ker) = ⊤ := by
    rw [Subgroup.subgroupOf_eq_top]; exact hker

  have hcard1 : Nat.card ((fieldUnitsNorm (K := K) A).ker ⧸
      ((fieldUnitsDerive A g).range.subgroupOf (fieldUnitsNorm (K := K) A).ker)) = 1 := by
    rw [hsub]
    have : Subsingleton ((fieldUnitsNorm (K := K) A).ker ⧸
        (⊤ : Subgroup (fieldUnitsNorm (K := K) A).ker)) :=
      QuotientGroup.subsingleton_quotient_top
    exact Nat.card_eq_one_iff_unique.mpr ⟨this, ⟨1⟩⟩

  rw [hcard1, mul_one] at heq
  exact heq

#check @solution
#print axioms solution

end S_M4aLocalCFT_fieldUnitsDecomp_card_tateH0_eq_card
end P2MW
export P2MW.S_M4aLocalCFT_fieldUnitsDecomp_card_tateH0_eq_card (solution)
