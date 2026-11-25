-- Prove2me | solution 1 for GroundTheory.LocalField.minpoly_isEisensteinAt_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:49:26.028477+00:00
-- url     : https://prove2.me/submissions/8b19bd47-6358-4557-8ca0-4ede6a949827

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
import Theorems.Thm_GroundTheory_LocalField_eq_zero_of_addVal_lt_of_sum_eq_zero
import Theorems.Thm_GroundTheory_LocalField_addVal_algebraMap_integer
import Theorems.Thm_GroundTheory_LocalField_addVal_eq_one_of_mem_of_notMem_sq
import Theorems.Thm_GroundTheory_LocalField_aeval_integer_eq_zero
import Theorems.Thm_GroundTheory_LocalField_addVal_term_of_totallyRamified
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped _root_.IntermediateField
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  (h : ramificationIndex K L = Module.finrank K L) {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include h hϖ
namespace GroundTheory.LocalField
theorem _root_.solution :
    (minpoly 𝒪[K] (ϖ : L)).IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]) ∧
      (minpoly 𝒪[K] (ϖ : L)).natDegree = Module.finrank K L := by
  set g := minpoly 𝒪[K] (ϖ : L) with hg_def
  set n := Module.finrank K L with hn_def
  have hint : IsIntegral 𝒪[K] (ϖ : L) := (isIntegral_iff K L _).mpr ϖ.2
  have hmon : g.Monic := minpoly.monic hint
  set d := g.natDegree with hd_def
  have hd0 : 0 < d := minpoly.natDegree_pos hint
  have hmap : minpoly K (ϖ : L) = g.map (algebraMap 𝒪[K] K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' K hint
  have hdn : d ≤ n := by
    have := minpoly.natDegree_le (A := K) (ϖ : L)
    rwa [hmap, hmon.natDegree_map] at this
  have hn0 : 0 < n := Module.finrank_pos
  have hroot : aeval ϖ g = 0 := by
    have := aeval_integer_eq_zero (f := g) ϖ.2 (minpoly.aeval 𝒪[K] (ϖ : L))
    simpa using this
  set t : ℕ → 𝒪[L] := fun i => algebraMap 𝒪[K] 𝒪[L] (g.coeff i) * ϖ ^ i with ht
  have hsum : ∑ i ∈ Finset.range (d + 1), t i = 0 := by
    rw [← hroot, aeval_eq_sum_range]
    simp [t, Algebra.smul_def, d]
  have hterm := addVal_term_of_totallyRamified h hϖ g
  have hne : ∀ i, IsUnit (g.coeff i) → t i ≠ 0 := by
    intro i hu h0
    have := (hterm i).2 hu
    simp only [t] at h0
    rw [h0, addVal_zero] at this
    exact ENat.top_ne_natCast _ this
  have hlow : ∀ i, ((i : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (t i) := by
    intro i
    have := (hterm i).1 0 (by simp)
    rw [mul_zero, zero_add] at this
    exact this

  have hmem : ∀ i < d, g.coeff i ∈ IsLocalRing.maximalIdeal 𝒪[K] := by
    by_contra hcon
    push Not at hcon
    have hex : ∃ j, j < d ∧ g.coeff j ∉ IsLocalRing.maximalIdeal 𝒪[K] := hcon
    classical
    let j := Nat.find hex
    have hj : j < d ∧ g.coeff j ∉ IsLocalRing.maximalIdeal 𝒪[K] := Nat.find_spec hex
    have hu : IsUnit (g.coeff j) := IsLocalRing.notMem_maximalIdeal.mp hj.2
    refine hne j hu (eq_zero_of_addVal_lt_of_sum_eq_zero hsum
      (Finset.mem_range.mpr (by omega)) fun i hi hij => ?_)
    rw [(hterm j).2 hu]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hi' : g.coeff i ∈ IsLocalRing.maximalIdeal 𝒪[K] := by
        by_contra hc
        exact Nat.find_min hex hlt ⟨by omega, hc⟩
      have := (hterm i).1 1 (by rwa [pow_one])
      refine lt_of_lt_of_le ?_ this
      exact_mod_cast (by omega : j < n * 1 + i)
    · exact lt_of_lt_of_le (by exact_mod_cast hgt) (hlow i)
  have htop : t d = ϖ ^ d := by
    simp only [t]
    rw [show g.coeff d = 1 from hmon]
    simp
  have htop_val : addVal 𝒪[L] (t d) = d := by rw [htop, hϖ.addVal_pow]
  have htop_ne : t d ≠ 0 := by
    rw [htop]
    exact pow_ne_zero _ hϖ.ne_zero

  have hmid : ∀ i, 0 < i → i < d → ((n + 1 : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (t i) := by
    intro i hi0 hid
    have := (hterm i).1 1 (by rw [pow_one]; exact hmem i hid)
    refine le_trans ?_ this
    exact_mod_cast (by omega : n + 1 ≤ n * 1 + i)

  have hsq : g.coeff 0 ∉ IsLocalRing.maximalIdeal 𝒪[K] ^ 2 := by
    intro hc
    refine htop_ne (eq_zero_of_addVal_lt_of_sum_eq_zero hsum (Finset.self_mem_range_succ d)
      fun i hi hid => ?_)
    have hid' : i < d := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hid
    rw [htop_val]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · refine lt_of_lt_of_le ?_ ((hterm 0).1 2 hc)
      exact_mod_cast (by omega : d < n * 2 + 0)
    · exact lt_of_lt_of_le (by exact_mod_cast (by omega : d < n + 1)) (hmid i hi0 hid')
  have Heisenberg₂ : g.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]) :=
    { leading := by
        rw [hmon.leadingCoeff]
        exact fun h1 => (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).ne_top
          ((Ideal.eq_top_iff_one _).mpr h1)
      mem := fun hi => hmem _ hi
      notMem := hsq }
  refine ⟨Heisenberg₂, le_antisymm hdn ?_⟩

  by_contra hlt
  rw [not_le] at hlt
  have h0val : addVal 𝒪[L] (t 0) = n := by
    simp only [t]
    rw [addVal_mul, addVal_algebraMap_integer, h,
      addVal_eq_one_of_mem_of_notMem_sq (hmem 0 hd0) hsq]
    simp
  refine htop_ne (eq_zero_of_addVal_lt_of_sum_eq_zero hsum (Finset.self_mem_range_succ d)
    fun i hi hid => ?_)
  have hid' : i < d := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hid
  rw [htop_val]
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [h0val]
    exact_mod_cast hlt
  · exact lt_of_lt_of_le (by exact_mod_cast (by omega : d < n + 1)) (hmid i hi0 hid')
end GroundTheory.LocalField
