-- Prove2me | solution 1 for OAI.FiniteAlgebraicEnvelopes.lemma_2_1_construction_v2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-12T19:42:43.724226+00:00
-- url     : https://prove2.me/submissions/a5a4c250-37ca-4fca-a545-3f56ed29863a

import Mathlib
import Mathlib.GroupTheory.HNNExtension
import Definitions.Def_lemma_2_1_data

open Monoid Coprod Multiplicative Subgroup Function
open OAI.FiniteAlgebraicEnvelopes

universe u

section Gens

variable {H : Type u} [Group H] (A B : Subgroup H) (φ : A ≃* B)

/-- `HNNExtension.of`'s range together with the stable letter `t` generate the whole
`HNNExtension`: both are images, under the defining quotient map, of the generators
`range inl ∪ range inr` of the free product `H ∗ ℤ` (multiplicatively), which generate
the whole free product. -/
theorem hnn_gens_top :
    Subgroup.closure (Set.range (HNNExtension.of : H →* HNNExtension H A B φ) ∪
      {HNNExtension.t (A := A) (B := B) (φ := φ)}) = ⊤ := by
  have hsurj : Function.Surjective (HNNExtension.con H A B φ).mk' := Con.mk'_surjective
  have h1 : Subgroup.closure (Set.range (Coprod.inl : H →* Coprod H (Multiplicative ℤ)) ∪
      Set.range (Coprod.inr : Multiplicative ℤ →* Coprod H (Multiplicative ℤ))) = ⊤ :=
    Coprod.closure_range_inl_union_inr
  have h2 : Subgroup.closure (((HNNExtension.con H A B φ).mk' :
      Coprod H (Multiplicative ℤ) →* HNNExtension H A B φ) ''
      (Set.range (Coprod.inl : H →* Coprod H (Multiplicative ℤ)) ∪
      Set.range (Coprod.inr : Multiplicative ℤ →* Coprod H (Multiplicative ℤ)))) = ⊤ := by
    rw [← MonoidHom.map_closure, h1, Subgroup.map_top_of_surjective _ hsurj]
  rw [Set.image_union] at h2
  have heq1 : ((HNNExtension.con H A B φ).mk' ''
      Set.range (Coprod.inl : H →* Coprod H (Multiplicative ℤ))) =
      Set.range (HNNExtension.of : H →* HNNExtension H A B φ) := by
    rw [← Set.range_comp]; congr 1
  have hsub2 : ((HNNExtension.con H A B φ).mk' ''
      Set.range (Coprod.inr : Multiplicative ℤ →* Coprod H (Multiplicative ℤ))) ⊆
      (Subgroup.zpowers (HNNExtension.t (A := A) (B := B) (φ := φ)) : Set (HNNExtension H A B φ)) := by
    rintro x ⟨y, ⟨n, rfl⟩, rfl⟩
    set k := Multiplicative.toAdd n with hk
    refine ⟨k, ?_⟩
    have hn : n = Multiplicative.ofAdd (1 : ℤ) ^ k := by
      rw [hk, ← Int.ofAdd_mul, one_mul]; rfl
    show (HNNExtension.t (A := A) (B := B) (φ := φ)) ^ k =
        (HNNExtension.con H A B φ).mk' (Coprod.inr n)
    rw [hn, map_zpow, map_zpow]
    rfl
  rw [heq1] at h2
  have hle : Subgroup.closure (Set.range (HNNExtension.of : H →* HNNExtension H A B φ) ∪
      ((HNNExtension.con H A B φ).mk' ''
        Set.range (Coprod.inr : Multiplicative ℤ →* Coprod H (Multiplicative ℤ))))
      ≤ Subgroup.closure (Set.range (HNNExtension.of : H →* HNNExtension H A B φ) ∪
          {HNNExtension.t (A := A) (B := B) (φ := φ)}) := by
    rw [Subgroup.closure_le]
    apply Set.union_subset
    · exact Set.subset_union_left.trans Subgroup.subset_closure
    · refine hsub2.trans ?_
      rw [Subgroup.zpowers_eq_closure]
      exact SetLike.coe_subset_coe.mpr (Subgroup.closure_mono Set.subset_union_right)
  exact le_antisymm le_top (h2 ▸ hle)

/-- Consequently, `HNNExtension H A B φ` is finitely generated whenever `H` is: take a finite
generating set for `H`, push it through `of`, and add `t`. -/
theorem hnn_fg [Group.FG H] (A B : Subgroup H) (φ : A ≃* B) :
    Group.FG (HNNExtension H A B φ) := by
  classical
  obtain ⟨S, hSclosure, hSfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG H)
  rw [Group.fg_iff]
  refine ⟨(HNNExtension.of '' S) ∪ {HNNExtension.t (A := A) (B := B) (φ := φ)}, ?_,
    (hSfin.image _).union (Set.finite_singleton _)⟩
  have h1 : Subgroup.closure (Set.range (HNNExtension.of : H →* HNNExtension H A B φ) ∪
      {HNNExtension.t (A := A) (B := B) (φ := φ)}) = ⊤ := hnn_gens_top A B φ
  have hofS : Subgroup.closure (HNNExtension.of '' S) =
      (HNNExtension.of : H →* HNNExtension H A B φ).range := by
    rw [← MonoidHom.map_closure, hSclosure, MonoidHom.range_eq_map]
  have hofS' : (↑(Subgroup.closure ((HNNExtension.of (A := A) (B := B) (φ := φ)) '' S)) :
        Set (HNNExtension H A B φ)) =
      Set.range (HNNExtension.of (A := A) (B := B) (φ := φ)) := by
    rw [hofS, MonoidHom.coe_range]
  apply le_antisymm le_top
  rw [← h1, Subgroup.closure_le]
  apply Set.union_subset
  · rw [← hofS']
    exact SetLike.coe_subset_coe.mpr (Subgroup.closure_mono Set.subset_union_left)
  · exact Set.subset_union_right.trans Subgroup.subset_closure

end Gens

theorem solution {H : Type u} [Group H] [Group.FG H] :
    Group.FG (HNNExtension (H × H) (diagonalSubgroup H) (secondFactorSubgroup H)
        (diagonalEquivSecondFactor H)) ∧
    Function.Injective
      (HNNExtension.of : H × H →*
        HNNExtension (H × H) (diagonalSubgroup H) (secondFactorSubgroup H)
          (diagonalEquivSecondFactor H)) ∧
    ∀ g : H, (HNNExtension.of ((g, g) : H × H) :
          HNNExtension (H × H) (diagonalSubgroup H) (secondFactorSubgroup H)
            (diagonalEquivSecondFactor H)) *
        HNNExtension.t * (HNNExtension.of ((g, g) : H × H))⁻¹ * HNNExtension.t⁻¹
        = HNNExtension.of ((g, 1) : H × H) := by
  classical
  set A := diagonalSubgroup H
  set B := secondFactorSubgroup H
  set φ := diagonalEquivSecondFactor H
  have hHH_fg : Group.FG (H × H) := inferInstance
  refine ⟨hnn_fg A B φ, HNNExtension.of_injective (A := A) (B := B) (φ := φ), ?_⟩
  intro g
  have hainv : ((g⁻¹, g⁻¹) : H × H) ∈ A := rfl
  have key := HNNExtension.equiv_eq_conj (A := A) (B := B) (φ := φ) (⟨(g⁻¹, g⁻¹), hainv⟩ : A)
  have hval : (φ (⟨(g⁻¹, g⁻¹), hainv⟩ : A) : H × H) = (1, g⁻¹) :=
    diagonalEquivSecondFactor_apply H g⁻¹
  rw [hval] at key
  have hofinv : (HNNExtension.of ((g⁻¹, g⁻¹) : H × H) : HNNExtension (H × H) A B φ)
      = (HNNExtension.of ((g, g) : H × H))⁻¹ := by
    rw [show ((g⁻¹, g⁻¹) : H × H) = ((g, g) : H × H)⁻¹ from rfl, map_inv]
  rw [hofinv] at key
  calc HNNExtension.of ((g, g) : H × H) * HNNExtension.t *
        (HNNExtension.of ((g, g) : H × H))⁻¹ * HNNExtension.t⁻¹
      = HNNExtension.of ((g, g) : H × H) *
          (HNNExtension.t * (HNNExtension.of ((g, g) : H × H))⁻¹ * HNNExtension.t⁻¹) := by
        group
    _ = HNNExtension.of ((g, g) : H × H) * HNNExtension.of ((1, g⁻¹) : H × H) := by rw [← key]
    _ = HNNExtension.of (((g, g) : H × H) * ((1, g⁻¹) : H × H)) := (map_mul _ _ _).symm
    _ = HNNExtension.of ((g, 1) : H × H) := by congr 1; ext <;> simp
