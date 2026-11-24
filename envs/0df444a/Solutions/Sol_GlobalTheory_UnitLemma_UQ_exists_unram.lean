-- Prove2me | solution 1 for GlobalTheory.UnitLemma.UQ.exists_unram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:24:44.964738+00:00
-- url     : https://prove2.me/submissions/ae87c7a5-b13f-4d60-8de7-75a04416ac53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LocallyCompactOfComplete
import Theorems.Thm_GlobalTheory_UnitLemma_Bridge_unram_of_involution
import Theorems.Thm_GlobalTheory_UnitLemma_Bridge_locallyCompact_of_complete
import Theorems.Thm_GlobalTheory_UnitLemma_Bridge_val_conj
import Theorems.Thm_GlobalTheory_UnitLemma_Bridge_exists_fixed_val
import Theorems.Thm_GlobalTheory_UnitLemma_Bridge_absOfVal_le_iff
import Theorems.Thm_GlobalTheory_UnitLemma_Bridge_absOfVal_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma
open Bridge
namespace GlobalTheory.UnitLemma
namespace UQ
theorem _root_.solution : ∀ K : UQ, ∃ (F : Type) (_ : NontriviallyNormedField F) (nE : NontriviallyNormedField K.E) (hE : nE.toField = K.fE) (_ : @NormedAlgebra F K.E _ nE.toNormedField.toNormedCommRing.toSeminormedCommRing.toSeminormedRing) (st : @StarRing K.E nE.toNormedField.toNormedCommRing.toRing.toNonAssocRing.toNonUnitalNonAssocRing.toNonUnitalNonAssocSemiring), @GlobalTheory.JR.Unram F K.E _ nE _ st ∧ (∀ y, st.star y = K.c y) ∧ ∀ y : K.E, nE.norm y ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range := by
  intro K
  let v := (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E
  obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal K.O).valuation_exists_uniformizer K.E
  have hint : ∀ y : K.E, v y ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range := by
    intro y
    refine ⟨fun h => IsDiscreteValuationRing.exists_lift_of_le_one h, ?_⟩
    rintro ⟨a, rfl⟩
    exact (IsDiscreteValuationRing.maximalIdeal K.O).valuation_le_one a
  have hle : ∀ y, v y ≤ 1 → v (K.c y) ≤ 1 := by
    intro y hy
    obtain ⟨a, rfl⟩ := (hint y).1 hy
    obtain ⟨b, hb⟩ := K.c_int a
    exact (hint _).2 ⟨b, hb.symm⟩
  have hv := val_conj v π hπ K.c K.c_c hle
  obtain ⟨a, b, hab, hm⟩ := K.c_res
  have hd : v (algebraMap K.O K.E a - K.c (algebraMap K.O K.E a)) = 1 := by
    rw [hab, ← map_sub]
    refine le_antisymm ((hint _).2 ⟨_, rfl⟩) (not_lt.1 fun h => hm ?_)
    exact ((IsDiscreteValuationRing.maximalIdeal K.O).valuation_lt_one_iff_mem _).1 h
  have hu := exists_fixed_val v π hπ K.c K.c_c hv _ ((hint _).2 ⟨a, rfl⟩) hd
  have hne : ∃ y, K.c y ≠ y := by
    refine ⟨algebraMap K.O K.E a, fun h => ?_⟩
    rw [h, sub_self, map_zero] at hd
    exact zero_ne_one hd
  have hball : ∀ y : K.E, absOfVal v y ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range := by
    intro y
    rw [← hint, ← (absOfVal v).map_one, absOfVal_le_iff, map_one]
  letI nE : NontriviallyNormedField K.E :=
    { (absOfVal v).toNormedField with
      non_trivial := by
        refine ⟨π⁻¹, not_le.1 fun h => ?_⟩
        have h1 : absOfVal v π⁻¹ ≤ 1 := h
        rw [hball, ← hint, map_inv₀] at h1
        rw [show v π = WithZero.exp (-1) from hπ, ← WithZero.exp_neg, ← WithZero.exp_zero,
          WithZero.exp_le_exp] at h1
        omega }
  haveI : IsUltrametricDist K.E := IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
    fun x y => by
      change absOfVal v (x + y) ≤ max (absOfVal v x) (absOfVal v y)
      rw [le_max_iff, absOfVal_le_iff, absOfVal_le_iff, ← le_max_iff]
      exact v.map_add x y
  haveI : LocallyCompactSpace K.E :=
    locallyCompact_of_complete (O := K.O) (IsFractionRing.injective K.O K.E) hball
  obtain ⟨F, nF, nA, st, h1, h2⟩ := unram_of_involution (nE := nE) K.c K.c_c hne
    (fun y => absOfVal_congr v (hv y))
    (fun y => (hu y).imp fun x hx => ⟨hx.1, absOfVal_congr v hx.2⟩)
  exact ⟨F, nF, nE, rfl, nA, st, h1, h2, hball⟩
end UQ
end GlobalTheory.UnitLemma
