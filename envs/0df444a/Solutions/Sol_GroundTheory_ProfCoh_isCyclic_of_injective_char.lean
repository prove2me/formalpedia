-- Prove2me | solution 1 for GroundTheory.ProfCoh.isCyclic_of_injective_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:48:56.96637+00:00
-- url     : https://prove2.me/submissions/236775a3-af42-4007-a6dc-49b56429eadc

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CyclicCup
import Definitions.Def_GroundTheory_TateCohomology_InfRes
import Definitions.Def_GroundTheory_ProfiniteCohomology_CyclicCupInflation
import Theorems.Thm_GroundTheory_GroupCoh_cupCochainsTensor_tmul
import Theorems.Thm_P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.cupCochainsTensor_tmul
attribute [local simp] P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory Limits MonoidalCategory groupCohomology GroundTheory.GroupCoh
variable {G : Type} [Group G]
namespace GroundTheory.ProfCoh
theorem _root_.solution [Finite G] (χ : Additive G →+ AddCircle (1 : ℚ))
    (hχ : Function.Injective χ) : IsCyclic G := by
  classical
  have := Fintype.ofFinite G
  set m := Fintype.card G with hmdef
  rcases Nat.lt_or_ge m 2 with hm | hm
  · have : Subsingleton G := Fintype.card_le_one_iff_subsingleton.1 (by omega)
    infer_instance
  have hk : ∀ x : G, ∃ k : ℕ, k < m ∧
      ((((k : ℚ) / m : ℚ)) : AddCircle (1 : ℚ)) = χ (Additive.ofMul x) := by
    intro x
    have hy01 := reprIco_mem (χ (Additive.ofMul x))
    have h0 : (((m : ℚ) * reprIco (χ (Additive.ofMul x)) : ℚ) : AddCircle (1 : ℚ)) = 0 := by
      rw [← nsmul_eq_mul, AddCircle.coe_nsmul, coe_reprIco, ← map_nsmul, ← ofMul_pow,
        pow_card_eq_one, ofMul_one, map_zero]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 h0
    rw [zsmul_one] at hn
    simp only [Set.mem_Ico] at hy01
    have hmpos : (0 : ℚ) < m := by exact_mod_cast (by omega : 0 < m)
    have hn0 : 0 ≤ n := by
      have : (0 : ℚ) ≤ n := by rw [hn]; exact mul_nonneg hmpos.le hy01.1
      exact_mod_cast this
    have hnm : n < m := by
      have : (n : ℚ) < m := by rw [hn]; nlinarith
      exact_mod_cast this
    refine ⟨n.toNat, by omega, ?_⟩
    rw [← coe_reprIco (χ (Additive.ofMul x))]
    congr 1
    rw [show ((n.toNat : ℕ) : ℚ) = (n : ℚ) by exact_mod_cast Int.toNat_of_nonneg hn0, hn]
    field_simp
  choose k hkm hkeq using hk
  have hkinj : Function.Injective k := by
    intro x x' h
    apply Additive.ofMul.injective
    apply hχ
    rw [← hkeq x, ← hkeq x', h]
  have himage : Finset.univ.image k = Finset.range m := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hi
      exact Finset.mem_range.2 (hkm x)
    · rw [Finset.card_range, Finset.card_image_of_injective _ hkinj, Finset.card_univ]
  have h1 : 1 ∈ Finset.univ.image k := by
    rw [himage]
    exact Finset.mem_range.2 (by omega)
  obtain ⟨g, -, hg⟩ := Finset.mem_image.1 h1
  have hχg := hkeq g
  rw [hg, Nat.cast_one] at hχg
  have hord : orderOf g = m := by
    rw [← addOrderOf_ofMul_eq_orderOf, ← addOrderOf_injective χ hχ, ← hχg]
    exact AddCircle.addOrderOf_period_div (p := (1 : ℚ)) (n := m) (by omega)
  exact isCyclic_of_orderOf_eq_card g (by rw [hord, Nat.card_eq_fintype_card])
end GroundTheory.ProfCoh
