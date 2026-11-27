-- Prove2me | solution 1 for GroundTheory.Global.cosetAverage_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:46:04.13374+00:00
-- url     : https://prove2.me/submissions/3a162b5b-014f-4f84-b491-e6220c8cbe6a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
import Definitions.Def_GroundTheory_GlobalFields_Artin_InflationTower
import Theorems.Thm_GroundTheory_Global_card_mul_sum_comp_of_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField
open scoped Pointwise
open GroundTheory GroundTheory.Global
variable {G H : Type*} [Group G] [Group H]
namespace GroundTheory.Global
theorem _root_.solution (I : Subgroup G) [Finite I] (π : G →* H) (f : H → ℂ) (g : G) :
    cosetAverage I (f ∘ π) g = cosetAverage (I.map π) f (π g) := by
  classical
  have : Finite (I.map π) := Finite.of_surjective _ (π.subgroupMap_surjective I)
  have : Fintype I := Fintype.ofFinite _
  have : Fintype (I.map π) := Fintype.ofFinite _
  have key := card_mul_sum_comp_of_surjective (π.subgroupMap I) (π.subgroupMap_surjective I)
    (fun j => f (π g * j))
  have hI : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hJ : (Fintype.card (I.map π) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold cosetAverage
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, inv_mul_eq_div, inv_mul_eq_div, div_eq_div_iff hI hJ]
  simp only [Function.comp_apply, map_mul]
  have hsub : ∀ i : I, π (i : G) = ((π.subgroupMap I i : I.map π) : H) := fun _ => rfl
  simp only [hsub]
  linear_combination key
end GroundTheory.Global
