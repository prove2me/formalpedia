-- Prove2me | solution 1 for GlobalTheory.SplitJump.jump_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:21:15.814747+00:00
-- url     : https://prove2.me/submissions/5615d02e-8c54-441e-8cdb-1a6f60efcb37

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PeriodDataComparison
import Theorems.Thm_GlobalTheory_SplitJump_fil_mono
import Theorems.Thm_GlobalTheory_SplitJump_eq_zero_of_mem_fil_one
import Theorems.Thm_GlobalTheory_SplitJump_mem_filV
import Theorems.Thm_GlobalTheory_SplitJump_exists_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory GlobalTheory.SplitJump
open Module TensorProduct
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) {n : ℕ} (e : Basis (Fin n) Qp V)
open Module TensorProduct
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) {n : ℕ} (e : Basis (Fin n) Qp V)
namespace GlobalTheory.SplitJump
namespace _root_.GlobalTheory.SplitJump
theorem _root_.solution (W W' : Matrix (Fin n) (Fin n) BdR)
    (hWW : W * W' = 1)
    (hW : ∀ i j, W i j ∈ PD.Fil 0) (hW' : ∀ i j, W' i j ∈ PD.Fil 0)
    (hg : ∀ g, (Matrix.of fun i j => algebraMap Qp BdR (e.repr (ρ g (e j)) i)) *
      W.map (PD.actdR g) = W)
    (τ : K →ₐ[Qp] LL) (a : ℤ) (h : _root_.Formalism.WeaklyAdmissibleFiltrations.IsJumpV PD ρ τ a) : a = 0 := by
  have hK0 : ∀ c : K, algebraMap K BdR c ∈ PD.Fil 0 := fun c => by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (PD.Fil 0).smul_mem c PD.one_mem
  have hrec : ∀ y ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ, ∃ k : Fin n → K,
      _root_.GlobalTheory.SplitJump.coord e BdR y = W.mulVec (fun i => algebraMap K BdR (k i)) ∧
      (fun i => algebraMap K BdR (k i)) = W'.mulVec (_root_.GlobalTheory.SplitJump.coord e BdR y) := by
    intro y hy
    obtain ⟨k, hk⟩ := _root_.GlobalTheory.SplitJump.exists_coord PD ρ e W W' hWW hg y hy
    refine ⟨k, ?_, hk⟩
    rw [hk, Matrix.mulVec_mulVec, hWW, Matrix.one_mulVec]
  have hlow : ∀ y ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ, ∀ b : ℤ, b ≤ 0 → y ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) b := by
    intro y hy b hb
    obtain ⟨k, hc, -⟩ := hrec y hy
    rw [_root_.GlobalTheory.SplitJump.mem_filV PD e]
    intro i
    apply _root_.GlobalTheory.SplitJump.fil_mono PD hb
    rw [hc]
    simp only [Matrix.mulVec, dotProduct]
    refine Submodule.sum_mem _ fun j _ => ?_
    simpa using PD.Fil_mul 0 0 _ _ (hW i j) (hK0 (k j))
  have hhigh : ∀ y ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ, ∀ b : ℤ, 1 ≤ b →
      y ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) b → y = 0 := by
    intro y hy b hb hyb
    obtain ⟨k, hc, hk⟩ := hrec y hy
    rw [_root_.GlobalTheory.SplitJump.mem_filV PD e] at hyb
    have hk0 : k = 0 := by
      funext i
      apply _root_.GlobalTheory.SplitJump.eq_zero_of_mem_fil_one PD
      have := congrFun hk i
      rw [this]
      simp only [Matrix.mulVec, dotProduct]
      refine Submodule.sum_mem _ fun j _ => ?_
      simpa using PD.Fil_mul 0 1 _ _ (hW' i j) (_root_.GlobalTheory.SplitJump.fil_mono PD hb (hyb j))
    apply (_root_.GlobalTheory.SplitJump.coord e BdR).injective
    rw [hc, hk0, map_zero]
    funext i
    simp [Matrix.mulVec, dotProduct]
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.IsJumpV _root_.Formalism.WeaklyAdmissibleFiltrations.FildR at h
  have hL : _root_.Formalism.WeaklyAdmissibleFiltrations.DdRE PD ρ τ ≤ _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ := by
    unfold _root_.Formalism.WeaklyAdmissibleFiltrations.DdRE
    exact inf_le_left
  by_contra ha
  apply h
  rcases lt_or_gt_of_ne ha with ha | ha
  · rw [inf_eq_left.2 fun y hy => hlow y (hL hy) _ (by omega),
      inf_eq_left.2 fun y hy => hlow y (hL hy) _ (by omega)]
  · have hbot : ∀ b : ℤ, 1 ≤ b →
        _root_.Formalism.WeaklyAdmissibleFiltrations.DdRE PD ρ τ ⊓ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) b = ⊥ := by
      intro b hb
      rw [eq_bot_iff]
      intro y hy
      exact (Submodule.mem_bot _).2 (hhigh y (hL hy.1) b hb hy.2)
    rw [hbot _ (by omega), hbot _ (by omega)]
end _root_.GlobalTheory.SplitJump
end GlobalTheory.SplitJump
