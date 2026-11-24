-- Prove2me | solution 1 for GlobalTheory.UnitPairNorm.exists_unit_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:03:12.787327+00:00
-- url     : https://prove2.me/submissions/e775fb43-ce67-49e7-9c2c-4242da158ccc

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitPairNorm
open Module
variable {O E : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E]
  [Algebra O E] [IsFractionRing O E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
namespace GlobalTheory.UnitPairNorm
theorem _root_.solution (h : V → V → E)
    (hsmul : ∀ (s : E) (x z : V), h (s • x) z = s * h x z)
    (W : Submodule E V) (L : Submodule O V) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set V) = W)
    (hdual : ∀ y ∈ W, (y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap O E).range))
    (hne : L ≠ ⊥) :
    ∃ x ∈ L, ∃ y ∈ L, ∃ a : Oˣ, h x y = algebraMap O E a := by
  by_contra hcon
  push_neg at hcon
  apply hne
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hϖ0 : algebraMap O E ϖ ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective O E)]; exact hϖ.ne_zero
  refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal O) L hfg ?_
    (IsLocalRing.maximalIdeal_le_jacobson _)
  intro x hx
  have hxW : x ∈ W := hsp ▸ Submodule.subset_span hx
  have hx'L : (algebraMap O E ϖ)⁻¹ • x ∈ L := by
    rw [hdual _ (W.smul_mem _ hxW)]
    intro z hz
    obtain ⟨o, ho⟩ := (hdual x hxW).mp hx z hz
    have hou : ¬ IsUnit o := fun hu => hcon x hx z hz hu.unit (by rw [IsUnit.unit_spec]; exact ho.symm)
    have hom : o ∈ Ideal.span {ϖ} := by
      rw [← hmax]; exact (IsLocalRing.mem_maximalIdeal o).mpr hou
    obtain ⟨o', rfl⟩ := Ideal.mem_span_singleton'.mp hom
    refine ⟨o', ?_⟩
    rw [hsmul, ← ho, map_mul]
    field_simp
  have hxe : x = ϖ • ((algebraMap O E ϖ)⁻¹ • x) := by
    rw [← algebraMap_smul E ϖ, smul_smul, mul_inv_cancel₀ hϖ0, one_smul]
  rw [hxe]
  exact Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit) hx'L
end GlobalTheory.UnitPairNorm
