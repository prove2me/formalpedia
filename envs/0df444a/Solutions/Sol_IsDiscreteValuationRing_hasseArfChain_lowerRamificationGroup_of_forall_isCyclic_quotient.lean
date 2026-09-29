-- Prove2me | solution 1 for IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_forall_isCyclic_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/a8327902-4306-5c5a-ae51-556644db970f

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Definitions.Def_RamificationChain_Wild
import Theorems.Thm_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq
import Theorems.Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_forall_isCyclic_quotient
p2m_attr_erase "simp" "IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf"

set_option autoImplicit false

namespace HasseArfRed

open IsLocalRing

section upper
variable {R : Type*} [CommRing R] [IsLocalRing R] {G : Type*} [Group G] [Finite G] [MulSemiringAction G R]

theorem upperRamificationGroup_le_succ_of_lt {i : ℕ} {w : ℚ} (hw : herbrandPhi R G i < w) :
    upperRamificationGroup R G w ≤ lowerRamificationGroup R G (i + 1) := by
  apply lowerRamificationGroup_antitone

  by_contra h
  push_neg at h
  have h1 : (upperRamificationIndex R G w : ℕ) ≤ i := Nat.lt_succ_iff.mp h
  have h2 := le_herbrandPhi_upperRamificationIndex (R := R) (G := G) w
  have h3 : herbrandPhi R G (upperRamificationIndex R G w : ℕ) ≤ herbrandPhi R G i :=
    herbrandPhi_monotone (by exact_mod_cast h1)
  exact absurd (h2.trans h3) (not_le.mpr hw)

theorem exists_jump_of_upper {v : ℚ} (hv : upperRamificationGroup R G v ≠ ⊥)
    (hw : ∀ w : ℚ, v < w → upperRamificationGroup R G w = ⊥) :
    ∃ c : ℕ, lowerRamificationGroup R G c ≠ lowerRamificationGroup R G (c + 1) ∧ herbrandPhi R G c = v := by
  refine ⟨upperRamificationIndex R G v, ?_, ?_⟩
  ·
    intro h
    have e1 : upperRamificationGroup R G v = lowerRamificationGroup R G (upperRamificationIndex R G v) := rfl
    have hlt : v < herbrandPhi R G ((upperRamificationIndex R G v + 1 : ℕ) : ℚ) := by
      refine lt_of_le_of_lt (le_herbrandPhi_upperRamificationIndex v) (herbrandPhi_strictMono ?_)
      exact_mod_cast Nat.lt_succ_self _
    have e2 := hw _ hlt
    rw [upperRamificationGroup_herbrandPhi_natCast] at e2
    exact hv (by rw [e1, h]; exact_mod_cast e2)
  ·
    rcases (le_herbrandPhi_upperRamificationIndex (R := R) (G := G) v).lt_or_eq with hlt | heq
    · have e2 := hw _ hlt
      rw [upperRamificationGroup_herbrandPhi_natCast] at e2
      exact absurd e2 hv
    · exact heq.symm

theorem exists_herbrandPhi_eq_natCast (hHA : RamificationChain.HasseArfChain (lowerRamificationGroup R G)) {c : ℕ}
    (hc : lowerRamificationGroup R G c ≠ lowerRamificationGroup R G (c + 1)) : ∃ m : ℕ, herbrandPhi R G c = m := by
  obtain ⟨k, hk⟩ := hHA c hc
  refine ⟨k, ?_⟩
  rw [herbrandPhi_natCast]
  have h0 : (lowerRamificationCard R G 0 : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (lowerRamificationCard_pos (R := R) (G := G) 0).ne'
  rw [div_eq_iff h0]
  have : (∑ i ∈ Finset.Icc 1 c, (lowerRamificationCard R G i : ℚ)) = ((∑ j ∈ Finset.Icc 1 c, Nat.card ↥(lowerRamificationGroup R G j) : ℕ) : ℚ) := by
    rw [Nat.cast_sum]; rfl
  rw [this, hk, Nat.cast_mul, mul_comm]
  rfl

theorem dvd_of_herbrandPhi_eq_natCast {c : ℕ} {m : ℕ} (h : herbrandPhi R G c = m) :
    Nat.card ↥(lowerRamificationGroup R G 0) ∣ ∑ j ∈ Finset.Icc 1 c, Nat.card ↥(lowerRamificationGroup R G j) := by
  refine ⟨m, ?_⟩
  have h0 : (lowerRamificationCard R G 0 : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (lowerRamificationCard_pos (R := R) (G := G) 0).ne'
  rw [herbrandPhi_natCast, div_eq_iff h0] at h
  have e : ((∑ j ∈ Finset.Icc 1 c, Nat.card ↥(lowerRamificationGroup R G j) : ℕ) : ℚ) = ((Nat.card ↥(lowerRamificationGroup R G 0) * m : ℕ) : ℚ) := by
    rw [Nat.cast_sum, Nat.cast_mul, mul_comm]
    exact h
  exact_mod_cast e

end upper

section cyclicQuotient
variable {G : Type*} [Group G] [Finite G] [IsMulCommutative G]

open scoped IsMulCommutative in

theorem exists_normal_isCyclic_quotient (N : Subgroup G) (g : G) (hg : g ∉ N) :
    ∃ H : Subgroup G, N ≤ H ∧ g ∉ H ∧ IsCyclic (G ⧸ H) := by
  haveI : N.Normal := Subgroup.normal_of_isMulCommutative N
  have hne : (QuotientGroup.mk g : G ⧸ N) ≠ 1 := by
    rwa [Ne, QuotientGroup.eq_one_iff]
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (G ⧸ N) ℂ hne
  let ψ : G →* ℂˣ := φ.comp (QuotientGroup.mk' N)
  refine ⟨ψ.ker, fun n hn => ?_, fun h => hφ ?_, ?_⟩
  · rw [MonoidHom.mem_ker]
    change φ (QuotientGroup.mk n) = 1
    rw [(QuotientGroup.eq_one_iff n).2 hn, map_one]
  · rwa [MonoidHom.mem_ker] at h
  · haveI : Finite ψ.range := Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
    haveI : IsCyclic ψ.range := isCyclic_subgroup_units ψ.range
    exact isCyclic_of_surjective (QuotientGroup.quotientKerEquivRange ψ).symm.toMonoidHom
      (QuotientGroup.quotientKerEquivRange ψ).symm.surjective

end cyclicQuotient

end HasseArfRed

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [IsMulCommutative G]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    [PerfectField (IsLocalRing.ResidueField R)]
    (hcyc : ∀ (H : Subgroup G) [H.Normal], IsCyclic (G ⧸ H) →
      RamificationChain.HasseArfChain
        (IsLocalRing.lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H))) :
    RamificationChain.HasseArfChain (IsLocalRing.lowerRamificationGroup R G) := by
  classical
  intro i hi

  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · simp

  have hlt : IsLocalRing.lowerRamificationGroup R G (i + 1) < IsLocalRing.lowerRamificationGroup R G i :=
    lt_of_le_of_ne (IsLocalRing.lowerRamificationGroup_antitone (Nat.le_succ i)) (Ne.symm hi)
  obtain ⟨g, hgi, hgi'⟩ := SetLike.exists_of_lt hlt

  obtain ⟨H, hNH, hgH, hcycH⟩ := HasseArfRed.exists_normal_isCyclic_quotient (IsLocalRing.lowerRamificationGroup R G (i + 1)) g hgi'
  haveI hHn : H.Normal := Subgroup.normal_of_isMulCommutative H

  have hcompat : IsLocalRing.UpperRamificationQuotientCompat R G (FixedPoints.subring R H) H :=
    IsLocalRing.upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq
      (fun n => IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField (R := R) (G := G) (H := H) n)

  set v : ℚ := IsLocalRing.herbrandPhi R G i with hvdef
  have hv0 : 0 ≤ v := IsLocalRing.herbrandPhi_nonneg (by exact_mod_cast Nat.zero_le i)
  have hQv : IsLocalRing.upperRamificationGroup (FixedPoints.subring R H) (G ⧸ H) v ≠ ⊥ := by
    rw [← hcompat v hv0, IsLocalRing.upperRamificationGroup_herbrandPhi_natCast]
    intro h
    have : QuotientGroup.mk' H g ∈ (IsLocalRing.lowerRamificationGroup R G i).map (QuotientGroup.mk' H) := Subgroup.mem_map_of_mem _ hgi
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact hgH this
  have hQw : ∀ w : ℚ, v < w → IsLocalRing.upperRamificationGroup (FixedPoints.subring R H) (G ⧸ H) w = ⊥ := by
    intro w hw
    rw [← hcompat w (hv0.trans hw.le), eq_bot_iff]
    refine (Subgroup.map_mono (HasseArfRed.upperRamificationGroup_le_succ_of_lt hw)).trans ?_
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hNH hx
  obtain ⟨c, hc, hφc⟩ := HasseArfRed.exists_jump_of_upper hQv hQw

  obtain ⟨m, hm⟩ := HasseArfRed.exists_herbrandPhi_eq_natCast (hcyc H hcycH) hc
  exact HasseArfRed.dvd_of_herbrandPhi_eq_natCast (R := R) (G := G) (m := m) (by rw [← hvdef, ← hφc, hm])

end S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_forall_isCyclic_quotient
end P2MW
export P2MW.S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_forall_isCyclic_quotient (solution)
