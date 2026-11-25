-- Prove2me | solution 1 for GlobalTheory.CharacterColumns.constantCoeff_dmonOf_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:54:13.170313+00:00
-- url     : https://prove2.me/submissions/309f4fa1-b3e7-4bc1-8f27-895f93a15053

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfSubMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NabValColumnsCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ConstantCoeffDmonOfEigen
import Theorems.Thm_GlobalTheory_CharacterColumns_dof_zero_dir
import Theorems.Thm_GlobalTheory_constantCoeff_dmonOf_sub_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.CharacterColumns
namespace GlobalTheory.CharacterColumns
theorem _root_.solution {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) {ι : Type}
    [Fintype ι] (u : ι → Fin d → R) (S : Set ι) (χ : PS R 1 d) (y : ι → R)
    (h1 : constantCoeff χ = 1) (hχ : ∀ l ∈ S, Dof F (u l) χ = C (y l) * χ) (mo : ι →₀ ℕ)
    (hmo : ∀ l, mo l ≠ 0 → l ∈ S) :
    constantCoeff (DmonOf F (S.indicator u) mo χ) = ∏ l, y l ^ mo l := by
  have key := constantCoeff_dmonOf_sub_mem R d F ⊥ ι (S.indicator u) (S.indicator y) χ (by
    intro l mo'
    by_cases hl : l ∈ S
    · rw [Set.indicator_of_mem hl, Set.indicator_of_mem hl, hχ l hl, sub_self, map_zero]
      exact Ideal.zero_mem _
    · rw [Set.indicator_of_notMem hl, Set.indicator_of_notMem hl, dof_zero_dir, map_zero, zero_mul,
        sub_self, map_zero]
      exact Ideal.zero_mem _) mo
  rw [Ideal.mem_bot, sub_eq_zero, h1, mul_one] at key
  rw [key]
  refine Finset.prod_congr rfl fun l _ => ?_
  by_cases hl : mo l = 0
  · rw [hl, pow_zero, pow_zero]
  · rw [Set.indicator_of_mem (hmo l hl)]
end GlobalTheory.CharacterColumns
