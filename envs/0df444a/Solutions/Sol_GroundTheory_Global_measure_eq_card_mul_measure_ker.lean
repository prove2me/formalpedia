-- Prove2me | solution 1 for GroundTheory.Global.measure_eq_card_mul_measure_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:28:04.681267+00:00
-- url     : https://prove2.me/submissions/b9312783-27c4-4244-8a15-828ede37ee43

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise
noncomputable section
namespace GroundTheory.Global
theorem _root_.solution {A Q : Type*} [AddGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A] (μ : Measure A)
    [μ.IsAddLeftInvariant] (L : AddSubgroup A) [AddGroup Q] [Finite Q] (φ : L →+ Q)
    (hφ : Function.Surjective φ) (hker : IsOpen ((φ.ker.map L.subtype : AddSubgroup A) : Set A)) :
    μ L = Nat.card Q * μ (φ.ker.map L.subtype) := by
  classical
  have := Fintype.ofFinite Q
  set N : Set A := ((φ.ker.map L.subtype : AddSubgroup A) : Set A) with hN
  have hmemN : ∀ y : A, y ∈ N ↔ ∃ h : y ∈ L, φ ⟨y, h⟩ = 0 := by
    intro y
    simp only [hN, AddSubgroup.coe_map, AddSubgroup.coe_subtype, Set.mem_image, SetLike.mem_coe,
      AddMonoidHom.mem_ker]
    constructor
    · rintro ⟨⟨z, hz⟩, h0, rfl⟩
      exact ⟨hz, h0⟩
    · rintro ⟨h, h0⟩
      exact ⟨⟨y, h⟩, h0, rfl⟩
  let t : Q → L := Function.surjInv hφ
  have ht : ∀ q, φ (t q) = q := Function.surjInv_eq hφ
  have hU : (L : Set A) = ⋃ q, ((t q : L) : A) +ᵥ N := by
    ext y
    simp only [SetLike.mem_coe, Set.mem_iUnion, Set.mem_vadd_set, vadd_eq_add]
    constructor
    · intro hy
      refine ⟨φ ⟨y, hy⟩, -(t (φ ⟨y, hy⟩) : A) + y, (hmemN _).2 ⟨L.add_mem (L.neg_mem (t _).2) hy, ?_⟩,
        add_neg_cancel_left _ _⟩
      have : (⟨-(t (φ ⟨y, hy⟩) : A) + y, L.add_mem (L.neg_mem (t _).2) hy⟩ : L) =
          -t (φ ⟨y, hy⟩) + ⟨y, hy⟩ := rfl
      rw [this, map_add, map_neg, ht, neg_add_cancel]
    · rintro ⟨q, n, hn, rfl⟩
      obtain ⟨hnL, -⟩ := (hmemN n).1 hn
      exact L.add_mem (t q).2 hnL
  have hdisj : Pairwise (Function.onFun Disjoint fun q ↦ ((t q : L) : A) +ᵥ N) := by
    intro q q' hqq'
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨n, hn, rfl⟩ ⟨n', hn', h⟩
    obtain ⟨hnL, hn0⟩ := (hmemN n).1 hn
    obtain ⟨hnL', hn0'⟩ := (hmemN n').1 hn'
    apply hqq'
    have h' : (t q' : L) + ⟨n', hnL'⟩ = t q + ⟨n, hnL⟩ := Subtype.ext h
    have := congrArg φ h'
    rwa [map_add, map_add, hn0, hn0', add_zero, add_zero, ht, ht, eq_comm] at this
  have hmeas : MeasurableSet N := hker.measurableSet
  rw [hU, measure_iUnion hdisj fun q ↦ (hker.vadd _).measurableSet, tsum_fintype]
  simp only [measure_vadd, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
end GroundTheory.Global
