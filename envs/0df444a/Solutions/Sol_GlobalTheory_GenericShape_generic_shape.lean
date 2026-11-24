-- Prove2me | solution 1 for GlobalTheory.GenericShape.generic_shape
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:13:25.12087+00:00
-- url     : https://prove2.me/submissions/c4f3bbc2-a656-4eec-b191-11ee5df33def

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GenericLevelOfFrameBlockAndCharacter
import Theorems.Thm_GlobalTheory_RootEx_Radical_embX_val
import Theorems.Thm_GlobalTheory_RootEx_Radical_mem_N_iff
import Theorems.Thm_P2M_GlobalTheory_RootEx_Radical_toBlocks___of_mem_fe0d9551bf6c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
namespace GlobalTheory.GenericShape
open MeasureTheory ValuativeRel Matrix Topology in
private lemma map_residue_apply {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {a : Type} [Fintype a] [DecidableEq a] (M : GL a 𝒪[k]) (i j : a) :
    ((GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) M : GL a 𝓀[k]) : Matrix a a 𝓀[k]) i j =
      IsLocalRing.residue 𝒪[k] ((M : Matrix a a 𝒪[k]) i j) := by
  simp
open MeasureTheory ValuativeRel Matrix Topology in
private lemma reduces_of_corner_lemma {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {κ l : ℕ} {g : GL (Fin κ ⊕ Fin l) k} {γ : GL (Fin κ) k}
    {g₀ : GL (Fin κ ⊕ Fin l) 𝒪[k]} (hg : GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₀ = g)
    (hγ : (g : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k).toBlocks₁₁ = γ)
    (hres : ∀ r s : Fin κ, s ≤ r → IsLocalRing.residue 𝒪[k]
      ((g₀ : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) 𝒪[k]) (Sum.inl r) (Sum.inl s)) =
        (1 : Matrix (Fin κ) (Fin κ) 𝓀[k]) r s) :
    ∃ gb, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.Reduces γ gb ∧
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUpperUnip Fin.val (gb : Matrix (Fin κ) (Fin κ) 𝓀[k]) := by
  subst hg
  set A : Matrix (Fin κ) (Fin κ) 𝒪[k] :=
    (g₀ : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) 𝒪[k]).toBlocks₁₁ with hA
  have hB : ∀ r s, s ≤ r → IsLocalRing.residue 𝒪[k] (A r s) = (1 : Matrix (Fin κ) (Fin κ) 𝓀[k]) r s :=
    hres
  have hdet : IsUnit A.det := by
    apply IsLocalRing.notMem_maximalIdeal.1
    intro hm
    rw [← IsLocalRing.residue_eq_zero_iff, RingHom.map_det, Matrix.det_of_upperTriangular] at hm
    · have hp : ∏ i, (IsLocalRing.residue 𝒪[k]).mapMatrix A i i = 1 :=
        Finset.prod_eq_one fun i _ => by simp [RingHom.mapMatrix_apply, hB i i le_rfl]
      rw [hp] at hm
      exact one_ne_zero hm
    · intro i j hij
      have hij' : j < i := hij
      simp [RingHom.mapMatrix_apply, hB i j hij'.le, Matrix.one_apply_ne (ne_of_lt hij').symm]
  let γ₀ : GL (Fin κ) 𝒪[k] := A.nonsingInvUnit hdet
  refine ⟨GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) γ₀, ⟨γ₀, ?_, rfl⟩, ?_⟩
  · ext i j
    rw [← hγ]
    rfl
  · intro r s hsr
    rw [map_residue_apply]
    exact hres r s hsr
open MeasureTheory ValuativeRel Matrix Topology in
private lemma toBlocks₁₁_mul_embX_of_mem_N {k : Type*} [Field k] {κ l p : ℕ}
    {u : GL (Fin κ ⊕ Fin l) k} (hu : u ∈ _root_.GlobalTheory.RootEx.N k (Fin κ) l p)
    (γ : GL (Fin κ) k) :
    ((u * _root_.GlobalTheory.RootEx.embX l γ : GL (Fin κ ⊕ Fin l) k) :
      Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k).toBlocks₁₁ = γ := by
  rw [Units.val_mul, _root_.GlobalTheory.StepData.mul_toBlocks₁₁, _root_.GlobalTheory.RootEx.Radical.toBlocks₁₁_of_mem hu,
    _root_.GlobalTheory.RootEx.Radical.embX_val]
  simp
open MeasureTheory ValuativeRel Matrix Topology in
private lemma one_apply_inl_inl {F a b : Type*} [Zero F] [One F] [DecidableEq a] [DecidableEq b]
    (r s : a) : (1 : Matrix (a ⊕ b) (a ⊕ b) F) (Sum.inl r) (Sum.inl s) = (1 : Matrix a a F) r s := by
  by_cases h : r = s <;> simp [Matrix.one_apply, h]
open MeasureTheory ValuativeRel Matrix Topology in
private lemma reduces_embX_of_reduces {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {κ l : ℕ} {γ : GL (Fin κ) k}
    {gb : GL (Fin κ) 𝓀[k]} (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.Reduces γ gb) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.Reduces (_root_.GlobalTheory.RootEx.embX l γ)
      (_root_.GlobalTheory.RootEx.embX l gb) := by
  obtain ⟨γ₀, h₁, h₂⟩ := h
  subst h₁ h₂
  let g₀ : GL (Fin κ ⊕ Fin l) 𝒪[k] :=
    ⟨fromBlocks (γ₀ : Matrix (Fin κ) (Fin κ) 𝒪[k]) 0 0 1,
      fromBlocks ((γ₀⁻¹ : GL (Fin κ) 𝒪[k]) : Matrix (Fin κ) (Fin κ) 𝒪[k]) 0 0 1,
      by rw [fromBlocks_multiply]; simp, by rw [fromBlocks_multiply]; simp⟩
  refine ⟨g₀, ?_, ?_⟩ <;> ext i j <;> rcases i with i | i <;> rcases j with j | j <;>
    simp [g₀, _root_.GlobalTheory.RootEx.Radical.embX_val, Matrix.one_apply, apply_ite]
open MeasureTheory ValuativeRel Matrix Topology in
private lemma one_apply_inr_inr {F a b : Type*} [Zero F] [One F] [DecidableEq a] [DecidableEq b]
    (r s : b) : (1 : Matrix (a ⊕ b) (a ⊕ b) F) (Sum.inr r) (Sum.inr s) = (1 : Matrix b b F) r s := by
  by_cases h : r = s <;> simp [Matrix.one_apply, h]
open MeasureTheory ValuativeRel Matrix Topology in
private lemma superSum_framePos_embX {k : Type} [Field k] {κ l : ℕ} (γ : GL (Fin κ) k) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ l)
        ((_root_.GlobalTheory.RootEx.embX l γ : GL (Fin κ ⊕ Fin l) k) :
          Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum Fin.val (γ : Matrix (Fin κ) (Fin κ) k) := by
  have hl : ∀ i : Fin κ, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ l (Sum.inl i) = i := fun i => by
    simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos]
  have hr : ∀ i : Fin l, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ l (Sum.inr i) = κ + i := fun i => by
    simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos]
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum
  simp only [Fintype.sum_sum_type, _root_.GlobalTheory.RootEx.Radical.embX_val, hl, hr,
    fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply,
    ite_self, Finset.sum_const_zero, add_zero, zero_add]
  have h : ∑ i : Fin l, ∑ j : Fin l,
      (if κ + (j : ℕ) = κ + i + 1 then (1 : Matrix (Fin l) (Fin l) k) i j else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hij
    · exact Matrix.one_apply_ne fun h => by subst h; omega
    · rfl
  linear_combination h
open MeasureTheory ValuativeRel Matrix Topology in
private lemma superSum_framePos_eq_simpleSum_of_mem_N {k : Type} [Field k] {κ l : ℕ}
    {u : GL (Fin κ ⊕ Fin l) k} (hu : u ∈ _root_.GlobalTheory.RootEx.N k (Fin κ) l 1) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ l)
        (u : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) =
      _root_.GlobalTheory.RootEx.simpleSum u := by
  rw [_root_.GlobalTheory.RootEx.Model.mem_N_iff] at hu
  unfold _root_.GlobalTheory.RootEx.InN at hu
  have hl : ∀ i : Fin κ, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ l (Sum.inl i) = i := fun i => by
    simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos]
  have hr : ∀ i : Fin l, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ l (Sum.inr i) = κ + i := fun i => by
    simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos]
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum _root_.GlobalTheory.RootEx.simpleSum
  simp only [Fintype.sum_sum_type, hl, hr]
  have h₁ : ∑ i : Fin κ, ∑ j : Fin κ, (if (j : ℕ) = i + 1 then
      (u : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) (Sum.inl i) (Sum.inl j) else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hij
    · rw [hu _ _ (by simp [_root_.GlobalTheory.RootEx.lev])]
      exact Matrix.one_apply_ne fun h => by
        have := congrArg (fun x : Fin κ ⊕ Fin l => Sum.elim (fun a : Fin κ => (a : ℕ)) (fun _ => 0) x) h
        simp at this
        omega
    · rfl
  have h₂ : ∑ i : Fin κ, ∑ j : Fin l, (if κ + (j : ℕ) = i + 1 then
      (u : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) (Sum.inl i) (Sum.inr j) else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hij
    · rw [hu _ _ (by simp [_root_.GlobalTheory.RootEx.lev]; omega)]
      simp
    · rfl
  have h₃ : ∑ i : Fin l, ∑ j : Fin κ, (if (j : ℕ) = κ + i + 1 then
      (u : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) (Sum.inr i) (Sum.inl j) else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg (by omega)]
  have h₄ : ∀ i j : Fin l, (κ + (j : ℕ) = κ + i + 1) ↔ ((j : ℕ) = i + 1) := fun i j => by omega
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [h₄]
  linear_combination h₁ + h₂ + h₃
end GlobalTheory.GenericShape
end

set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.GenericShape
open MeasureTheory ValuativeRel Matrix Topology
namespace GlobalTheory.GenericShape
namespace _root_.GlobalTheory.GenericShape
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (ϖ : kˣ) (κ l : ℕ) (P : _root_.GlobalTheory.StepData.TypeDatum k (Fin κ ⊕ Fin l)), _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsGenericLevel ψ ϖ P → ((∀ u ∈ _root_.GlobalTheory.RootEx.N k (Fin κ) l 1, ∀ γ : GL (Fin κ) k, u * _root_.GlobalTheory.RootEx.embX l γ ∈ P.J → ∃ gb, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.Reduces γ gb ∧ _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUpperUnip Fin.val gb.val) ∧ (∀ (γ : GL (Fin κ) k) (gb : GL (Fin κ) 𝓀[k]), _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.Reduces γ gb → _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUpperUnip Fin.val gb.val → ∃ hm : _root_.GlobalTheory.RootEx.embX l γ ∈ P.J, (P.lam ⟨_, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum Fin.val γ.val)) ∧ ∀ u ∈ _root_.GlobalTheory.RootEx.N k (Fin κ) l 1, ∀ hm : u ∈ P.J, (P.lam ⟨u, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * _root_.GlobalTheory.RootEx.simpleSum u)) := by
  intro k _ _ _ _ ψ ϖ κ l P h
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsGenericLevel at h
  obtain ⟨hJ, hlam⟩ := h
  refine ⟨fun u hu γ hm => ?_, fun γ gb hred hup => ?_, fun u hu hm => ?_⟩
  · obtain ⟨gb', ⟨g₀, hg₀, hres₀⟩, hup'⟩ := (hJ _).1 hm
    refine reduces_of_corner_lemma hg₀ (toBlocks₁₁_mul_embX_of_mem_N hu γ) fun r s hsr => ?_
    rw [← map_residue_apply, hres₀]
    exact (hup' (Sum.inl r) (Sum.inl s) (by simpa [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos] using hsr)).trans
      (one_apply_inl_inl r s)
  · have hm : _root_.GlobalTheory.RootEx.embX l γ ∈ P.J := by
      refine (hJ _).2 ⟨_root_.GlobalTheory.RootEx.embX l gb, reduces_embX_of_reduces hred, ?_⟩
      intro r s hrs
      rcases r with r | r <;> rcases s with s | s
      · have h' : (s : ℕ) ≤ r := by simpa [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos] using hrs
        rw [_root_.GlobalTheory.RootEx.Radical.embX_val, fromBlocks_apply₁₁]
        exact (hup r s h').trans (one_apply_inl_inl r s).symm
      · have h' : κ + (s : ℕ) ≤ r := by simpa [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos] using hrs
        omega
      · rw [_root_.GlobalTheory.RootEx.Radical.embX_val, fromBlocks_apply₂₁]
        simp [Matrix.one_apply]
      · rw [_root_.GlobalTheory.RootEx.Radical.embX_val, fromBlocks_apply₂₂]
        exact (one_apply_inr_inr r s).symm
    refine ⟨hm, ?_⟩
    rw [hlam ⟨_, hm⟩]
    simp only [superSum_framePos_embX]
  · rw [hlam ⟨u, hm⟩, superSum_framePos_eq_simpleSum_of_mem_N hu]
end _root_.GlobalTheory.GenericShape
end GlobalTheory.GenericShape
