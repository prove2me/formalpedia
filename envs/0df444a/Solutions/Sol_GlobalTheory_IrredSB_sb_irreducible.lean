-- Prove2me | solution 1 for GlobalTheory.IrredSB.sb_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:07:16.18301+00:00
-- url     : https://prove2.me/submissions/1bd1a3ed-b29e-4652-a465-1189a8d95ade

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegersModNatFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreduc
import Theorems.Thm_GlobalTheory_IrredSB_ind_mem
import Theorems.Thm_GlobalTheory_IrredSB_mem_of_cosets
import Theorems.Thm_GlobalTheory_IrredSB_pair_add_right
import Theorems.Thm_GlobalTheory_IrredSB_sep
import Theorems.Thm_GlobalTheory_IrredSB_cover
import Theorems.Thm_GlobalTheory_IrredSB_trans_mem_SB
import Theorems.Thm_GlobalTheory_IrredSB_modul_mem_SB
import Theorems.Thm_GlobalTheory_SBUnif_sb_lattice_bounds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.IrredSB
namespace GlobalTheory.IrredSB
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (ψk : AddChar k Circle), Continuous ψk → ψk ≠ 1 → ∀ W : Submodule ℂ (Matrix Y Y' k → ℂ), W ≤ SB (Matrix Y Y' k) → (∀ Φ ∈ W, ∀ x : Matrix Y Y' k, (fun t => Φ (t + x)) ∈ SB (Matrix Y Y' k) → (fun t => Φ (t + x)) ∈ W) → (∀ Φ ∈ W, ∀ b : Matrix Y Y' k, (fun t => (ψk (∑ r, ∑ q, b r q * t r q) : ℂ) * Φ t) ∈ SB (Matrix Y Y' k) → (fun t => (ψk (∑ r, ∑ q, b r q * t r q) : ℂ) * Φ t) ∈ W) → ∀ Φ₀ ∈ W, Φ₀ ≠ 0 → W = SB (Matrix Y Y' k) := by
  intro k _ _ _ _ _ Y Y' _ _ _ _ ψk hψ hψ1 W hW hTc hMc Φ₀ h0 hne
  have hT : ∀ Φ ∈ W, ∀ x, (fun t => Φ (t + x)) ∈ W := fun Φ h x => hTc Φ h x (trans_mem_SB (hW h) x)
  have hM : ∀ Φ ∈ W, ∀ b, (fun t => (ψk (pair b t) : ℂ) * Φ t) ∈ W :=
    fun Φ h b => hMc Φ h b (modul_mem_SB ψk hψ (hW h) b)
  have he : ∀ b t u : Matrix Y Y' k, (ψk (pair b (t + u)) : ℂ) = (ψk (pair b t) : ℂ) * ψk (pair b u) :=
    fun b t u => by rw [pair_add_right, AddChar.map_add_eq_mul, Circle.coe_mul]
  refine le_antisymm hW fun Φ hΦ => ?_
  obtain ⟨a, ha⟩ : ∃ a, Φ₀ a ≠ 0 := Function.ne_iff.1 hne
  have hf : ((Φ₀ a)⁻¹ • fun t => Φ₀ (t + a)) ∈ W := W.smul_mem _ (hT _ h0 a)
  have hf0 : ((Φ₀ a)⁻¹ • fun t => Φ₀ (t + a)) 0 = 1 := by simp [ha]
  generalize ((Φ₀ a)⁻¹ • fun t => Φ₀ (t + a)) = f at hf hf0
  obtain ⟨n, hn, hinv, hsupp⟩ := GlobalTheory.SBUnif.sb_lattice_bounds k Y Y' f (hW hf)
  obtain ⟨m, hm, hinv', hsupp'⟩ := GlobalTheory.SBUnif.sb_lattice_bounds k Y Y' Φ hΦ
  have hnm : 0 < n * m := Nat.mul_pos hn hm
  have hn1 : ind (lat k Y Y' n) ∈ W := by
    obtain ⟨P, hP⟩ := cover (k := k) (Y := Y) (Y' := Y') hn hn
    refine ind_mem (fun b t => (ψk (pair b t) : ℂ)) he W hM _ (sep ψk hψ hψ1 hn) hf ?_ P
      fun t ht => hP t (hsupp t ht)
    rintro _ ⟨u, hu, rfl⟩
    have := hinv u hu 0
    rw [zero_add, hf0] at this
    exact this
  have hn2 : ind (lat k Y Y' (n * m)) ∈ W := by
    obtain ⟨P, hP⟩ := cover (k := k) (Y := Y) (Y' := Y') one_pos hnm
    refine ind_mem (fun b t => (ψk (pair b t) : ℂ)) he W hM _ (sep ψk hψ hψ1 hnm) hn1 ?_ P
      fun t ht => hP t ?_
    · rintro _ ⟨u, hu, rfl⟩
      have : nsmulAddMonoidHom (n * m) u ∈ lat k Y Y' n :=
        ⟨m • u, nsmul_mem hu m, (mul_smul n m u).symm⟩
      rw [ind, if_pos this]
    · have : t ∈ lat k Y Y' n := by
        by_contra h
        exact ht (by rw [ind, if_neg h])
      obtain ⟨u, hu, rfl⟩ := this
      rw [one_smul]
      exact (nsmul_mem hu n : n • u ∈ intMat k Y Y')
  obtain ⟨P, hP⟩ := cover (k := k) (Y := Y) (Y' := Y') hm hnm
  refine mem_of_cosets W hT hn2 P Φ ?_ fun t ht => hP t (hsupp' t ht)
  rintro _ ⟨u, hu, rfl⟩ t
  have := hinv' (n • u) (nsmul_mem hu n : n • u ∈ intMat k Y Y') t
  rw [← mul_smul, mul_comm] at this
  exact this
end GlobalTheory.IrredSB
