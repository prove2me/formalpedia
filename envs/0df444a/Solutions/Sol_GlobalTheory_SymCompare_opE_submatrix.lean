-- Prove2me | solution 1 for GlobalTheory.SymCompare.opE_submatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:13:17.209982+00:00
-- url     : https://prove2.me/submissions/bd75e197-9c64-4e54-bd84-9f553a171fb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_SymmetricPatternGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsReindexIff
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.SymCompare
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n m n' m' : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] {c : ℕ}
omit [DecidableEq n] [DecidableEq m] [DecidableEq n'] [DecidableEq m']
namespace GlobalTheory.SymCompare
theorem _root_.solution [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
    (p : ℕ) (e : n ≃ m) (e' : n' ≃ m') (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix m m' k) :
    opE ψ ν p (fun x => Φ (x.submatrix (sE e c) (sE e' (c + 1)))) x₀ = opE ψ ν p Φ (x₀.submatrix e e') := by
  classical
  have := secondCountable k
  have := t2Space k
  have hf : ∀ r s, Free p (r, s) ↔ Free p (sE e c r, sE e' (c + 1) s) := by
    rintro (r | r) (s | s) <;> exact Iff.rfl
  let σ : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} ≃ {rs : (m ⊕ Fin c) × (m' ⊕ Fin (c + 1)) // Free p rs} :=
    ((sE e c).prodCongr (sE e' (c + 1))).subtypeEquiv fun rs => hf rs.1 rs.2
  have h1 : ∀ f, (affPt p x₀ f).submatrix (sE e c) (sE e' (c + 1)) =
      affPt p (x₀.submatrix e e') (MeasurableEquiv.piCongrLeft (fun _ => k) σ.symm f) := fun f => by
    have h2 : ∀ a, MeasurableEquiv.piCongrLeft (fun _ => k) σ.symm f a = f (σ a) := fun a => by
      obtain ⟨a, rfl⟩ := σ.symm.surjective a
      rw [MeasurableEquiv.piCongrLeft_apply_apply, Equiv.apply_symm_apply]
    ext r s
    have hb : basePt c x₀ (sE e c r) (sE e' (c + 1) s) = basePt c (x₀.submatrix e e') r s := by
      rcases r with r | r <;> rcases s with s | s <;> rfl
    simp only [affPt, submatrix_apply, Matrix.add_apply, hb, of_apply, h2]
    by_cases h : Free p (r, s)
    · rw [dif_pos h, dif_pos ((hf r s).1 h)]; rfl
    · rw [dif_neg h, dif_neg fun H => h ((hf r s).2 H)]
  unfold opE
  rw [← (measurePreserving_piCongrLeft (fun _ => ν) σ.symm).integral_comp']
  simp only [← h1]
  rfl
end GlobalTheory.SymCompare
