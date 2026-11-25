-- Prove2me | solution 1 for GlobalTheory.LatClass.bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:52:42.472626+00:00
-- url     : https://prove2.me/submissions/0eb742d8-2972-49ff-b387-bf969c0d874b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ZpowMulMemPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LatticeBounds
import Theorems.Thm_GlobalTheory_LatClass_aff_row
import Theorems.Thm_GlobalTheory_LatClass_aff_diag
import Theorems.Thm_GlobalTheory_LatClass_exists_supp
import Theorems.Thm_GlobalTheory_LatClass_col_mem_nf
import Theorems.Thm_GlobalTheory_LatClass_mem_nf
import Theorems.Thm_GlobalTheory_LatClass_mem_pow_zero
import Theorems.Thm_GlobalTheory_LatClass_smul_mem_lat
import Theorems.Thm_GlobalTheory_LatClass_zpow_mem_pow
import Theorems.Thm_GlobalTheory_LatClass_zpow_mul_mem_pow
import Theorems.Thm_GlobalTheory_RootEx_Unram_mem_of_psi
import Theorems.Thm_GlobalTheory_RootEx_Unram_psi_ch_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.LatClass
variable {k : Type} [Field k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
  {ϖ : kˣ} {ψ : AddChar k Circle} {ν : Measure k}
namespace GlobalTheory.LatClass
theorem _root_.solution (hϖ : valuation k (ϖ : k) = uniformizer k) (hψ : HasConductor ψ 1) [ν.IsAddHaarMeasure]
    {g' : GL n' k} {e' : Fin (c + 1 + 1) → ℤ} {z' : n' → k} {h : GL (n ⊕ Fin (c + 1)) k}
    {Ψ : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k → ℂ}
    (hs : ∀ x, Ψ x ≠ 0 → MapsLat x (latOf (nfBasis ϖ g' e' z')) (latOf h))
    (hp : ∀ x y, MapsLat y (latOf (nfBasis ϖ g' e' z')) (latOf h) → Ψ (x + (ϖ : k) • y) = Ψ x)
    {x₀ : Matrix n n' k} (h0 : opE ψ ν 1 Ψ x₀ ≠ 0) (i : Fin (c + 1)) {a : ℤ}
    (ha : topCoord (latOf h) i = powInt ϖ a) : e' i.succ - 1 ≤ a ∧ a ≤ e' i.castSucc := by
  constructor
  · obtain ⟨v, hv, hv0, hvi⟩ : (ϖ : k) ^ a ∈ topCoord (latOf h) i := ha ▸ (zpow_mem_pow hϖ).2 le_rfl
    have key : -((ϖ : k) * ((ϖ : k) ^ (-e' i.succ) * (ϖ : k) ^ a)) ∈ 𝒪[k] := by
      refine Unram.mem_of_psi hψ fun t ht => ?_
      let y : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k :=
        Matrix.of fun r s => if s = .inr i.succ then t * (ϖ : k) ^ (-e' i.succ) * v r else 0
      have hy : MapsLat y (latOf (nfBasis ϖ g' e' z')) (latOf h) := fun w hw => by
        have : y *ᵥ w = (t * ((ϖ : k) ^ (-e' i.succ) * w (.inr i.succ))) • v := by
          ext r; simp [y, mulVec, dotProduct]; ring
        rw [this]
        refine smul_mem_lat (mul_mem ht ?_) hv
        rw [← mem_pow_zero (ϖ := ϖ), zpow_mul_mem_pow]
        simpa using (mem_nf.1 hw).2 i.succ
      have := Unram.psi_ch_eq_one ψ ν Ψ x₀ h0 ((ϖ : k) • y) (fun r s hf => ?_) fun x => hp x y hy
      · convert this using 2
        simp [ch, y, hvi]; ring
      · simp only [y, Matrix.smul_apply, Matrix.of_apply]
        split_ifs with e
        · subst e
          rcases r with r | r
          · simp [Free] at hf
          · rw [hv0 r (by simp only [Free, Fin.val_succ] at hf; rw [Fin.lt_def]; omega)]; simp
        · simp
    rw [neg_mem_iff, ← mem_pow_zero (ϖ := ϖ), ← zpow_add₀ ϖ.ne_zero, ← zpow_one_add₀ ϖ.ne_zero,
      zpow_mem_pow hϖ] at key
    omega
  · obtain ⟨y, hy⟩ := exists_supp h0
    have := hs _ hy _ (col_mem_nf i.castSucc ((zpow_mem_pow hϖ).2 le_rfl))
    rw [← zpow_mem_pow hϖ, ← ha]
    refine ⟨_, this, fun l hl => ?_, ?_⟩
    · rw [aff_row, aff_diag _ _ _ _ hl.le, if_neg hl.ne', zero_mul]
    · rw [aff_row, aff_diag _ _ _ _ le_rfl, if_pos rfl, one_mul]
end GlobalTheory.LatClass
