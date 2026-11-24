-- Prove2me | solution 1 for GlobalTheory.UnitLemma.SgnProd.lattice_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:10:30.879803+00:00
-- url     : https://prove2.me/submissions/5baddafe-94cd-4bca-a2a0-3b8b7e5e7f04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyLeftMulBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatSpanBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatProdEqEtaResultantMul
import Theorems.Thm_GlobalTheory_UnitLemma_SgnProd_exists_basis_lat
import Theorems.Thm_GlobalTheory_UnitLemma_SgnProd_exists_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.SgnProd
open Module
namespace GlobalTheory.UnitLemma.SgnProd
theorem _root_.solution (K : UQ) (V₁ V₂ : Type) [AddCommGroup V₁] [Module K.E V₁] [Module K.O V₁]
    [IsScalarTower K.O K.E V₁] [Module.Finite K.E V₁] [AddCommGroup V₂] [Module K.E V₂] [Module K.O V₂]
    [IsScalarTower K.O K.E V₂] [Module.Finite K.E V₂] (M : Submodule K.O (V₁ × V₂)) (hfg : M.FG)
    (hsp : Submodule.span K.E (M : Set (V₁ × V₂)) = ⊤) :
    ∃ (e₁ : Basis (Fin (finrank K.E V₁)) K.E V₁) (e₂ : Basis (Fin (finrank K.E V₂)) K.E V₂)
      (x : Fin (finrank K.E V₂) → V₁ × V₂),
      Submodule.span K.O (Set.range e₁) = M.comap (LinearMap.inl K.O V₁ V₂) ∧
      Submodule.span K.O (Set.range e₂) = M.map (LinearMap.snd K.O V₁ V₂) ∧
      (∀ j, (x j).2 = e₂ j) ∧
      Submodule.span K.O (Set.range (Fin.addCases (fun i => ((e₁ i, 0) : V₁ × V₂)) x)) = M := by
  set M₁ := M.comap (LinearMap.inl K.O V₁ V₂) with hM₁
  set M₂ := M.map (LinearMap.snd K.O V₁ V₂) with hM₂
  have hfg₁ : M₁.FG := by
    haveI : IsNoetherian K.O M := isNoetherian_of_fg_of_noetherian M hfg
    refine Submodule.fg_of_fg_map_injective (LinearMap.inl K.O V₁ V₂) LinearMap.inl_injective ?_
    exact Submodule.FG.of_le_of_isNoetherian (T := M) (Submodule.map_comap_le _ _)
  have hsp₁ : Submodule.span K.E (M₁ : Set V₁) = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨s, hs0, hs⟩ := exists_smul_mem K M hfg hsp ((y, 0) : V₁ × V₂)
    have hsy : s • y ∈ M₁ := by
      show LinearMap.inl K.O V₁ V₂ (s • y) ∈ M
      simpa [LinearMap.inl_apply, Prod.smul_mk] using hs
    have hs' : algebraMap K.O K.E s ≠ 0 := by
      rwa [ne_eq, (IsFractionRing.injective K.O K.E).eq_iff' (map_zero _)]
    have : y = (algebraMap K.O K.E s)⁻¹ • (s • y) := by
      rw [← algebraMap_smul K.E s y, smul_smul, inv_mul_cancel₀ hs', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hsy)
  have hfg₂ : M₂.FG := hfg.map _
  have hsp₂ : Submodule.span K.E (M₂ : Set V₂) = ⊤ := by
    have h1 : (M₂ : Set V₂) = (LinearMap.snd K.E V₁ V₂) '' (M : Set (V₁ × V₂)) := by
      rw [hM₂, Submodule.map_coe]; rfl
    rw [h1, Submodule.span_image, hsp, Submodule.map_top, LinearMap.range_eq_top.2 LinearMap.snd_surjective]
  obtain ⟨e₁, he₁⟩ := exists_basis_lat K M₁ hfg₁ hsp₁
  obtain ⟨e₂, he₂⟩ := exists_basis_lat K M₂ hfg₂ hsp₂
  have hlift : ∀ j, ∃ x ∈ M, x.2 = e₂ j := fun j => by
    have : e₂ j ∈ M₂ := he₂ ▸ Submodule.subset_span ⟨j, rfl⟩
    obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 this
    exact ⟨x, hx, hxe⟩
  choose x hxM hx2 using hlift
  refine ⟨e₁, e₂, x, he₁, he₂, hx2, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    induction l using Fin.addCases with
    | left i =>
      simp only [Fin.addCases_left, SetLike.mem_coe]
      have : e₁ i ∈ M₁ := he₁ ▸ Submodule.subset_span ⟨i, rfl⟩
      exact this
    | right j => simp only [Fin.addCases_right, SetLike.mem_coe]; exact hxM j
  · intro y hy
    have hy2 : y.2 ∈ M₂ := Submodule.mem_map_of_mem hy
    rw [← he₂, Submodule.mem_span_range_iff_exists_fun] at hy2
    obtain ⟨c, hc⟩ := hy2
    set z := y - ∑ j, c j • x j with hz
    have hzM : z ∈ M := M.sub_mem hy (M.sum_mem fun j _ => M.smul_mem _ (hxM j))
    have hz2 : z.2 = 0 := by
      simp only [hz, Prod.snd_sub, Prod.snd_sum, Prod.smul_snd, hx2, hc, sub_self]
    have hz1 : z.1 ∈ M₁ := by
      show LinearMap.inl K.O V₁ V₂ z.1 ∈ M
      have : LinearMap.inl K.O V₁ V₂ z.1 = z := Prod.ext rfl hz2.symm
      rw [this]; exact hzM
    rw [← he₁, Submodule.mem_span_range_iff_exists_fun] at hz1
    obtain ⟨d, hd⟩ := hz1
    have hyz : y = ∑ i, d i • ((e₁ i, 0) : V₁ × V₂) + ∑ j, c j • x j := by
      have : ∑ i, d i • ((e₁ i, 0) : V₁ × V₂) = z := by
        refine Prod.ext ?_ ?_
        · simp [Prod.fst_sum, hd]
        · simp [Prod.snd_sum, hz2]
      rw [this, hz, sub_add_cancel]
    rw [hyz]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
      (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
    · exact Submodule.subset_span ⟨Fin.castAdd _ i, Fin.addCases_left _⟩
    · exact Submodule.subset_span ⟨Fin.natAdd _ j, Fin.addCases_right _⟩
end GlobalTheory.UnitLemma.SgnProd
