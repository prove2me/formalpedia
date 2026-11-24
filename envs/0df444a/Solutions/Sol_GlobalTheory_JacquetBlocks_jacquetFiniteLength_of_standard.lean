-- Prove2me | solution 1 for GlobalTheory.JacquetBlocks.jacquetFiniteLength_of_standard
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:37:32.056414+00:00
-- url     : https://prove2.me/submissions/aa0d647b-f068-4ae4-a725-12c0c63cdcca

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InductionFiniteLength
import Theorems.Thm_GlobalTheory_JacquetBlocks_hasFiniteLength_twist_iff
import Theorems.Thm_GlobalTheory_JacquetBlocks_hasFiniteLength_jacU_reindex
import Theorems.Thm_GlobalTheory_JacquetBlocks_hasFiniteLength_jacU_relabel
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_hasFiniteLength_comp_iff
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.JacquetBlocks
namespace GlobalTheory.JacquetBlocks
theorem _root_.solution :
    GlobalTheory.Published.StandardFunctorsFiniteLength → ∀ (k : Type) [Field k] [ValuativeRel k]
      [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.JacquetFiniteLength k := by
  intro hP k _ _ _ _ α n m _ _ _ _ _ _ e V _ _ π hπ hl
  classical
  let α' := {a : α // Nonempty (m a)}
  let o : Fin (Fintype.card α') ≃o α' := monoEquivOfFin α' rfl
  let d : Fin (Fintype.card α') → ℕ := fun i => Fintype.card (m (o i).1)
  have hd : ∀ i, 0 < d i := fun i => Fintype.card_pos_iff.2 (o i).2
  let T : (Σ a' : α', m a'.1) ≃ (Σ a, m a) :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun x => ⟨⟨x.1, ⟨x.2⟩⟩, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let s : (Σ i, Fin (d i)) ≃ (Σ a, m a) :=
    ((Equiv.sigmaCongrRight fun i => (Fintype.equivFin (m (o i).1)).symm).trans
      (Equiv.sigmaCongrLeft (β := fun a' : α' => m a'.1) o.toEquiv)).trans T
  have hs : ∀ x, (s x).1 = (fun i => (o i).1) x.1 := by
    rintro ⟨i, j⟩
    rfl
  have hf : StrictMono (fun i => (o i).1) := fun i j h => o.strictMono h
  let e₁ := s.trans e
  let ψ : Fin (∑ i, d i) ≃ n := finSigmaFinEquiv.symm.trans e₁
  let Φ : GL (Fin (∑ i, d i)) k →* GL n k :=
    (Units.mapEquiv (Matrix.reindexAlgEquiv k k ψ).toMulEquiv).toMonoidHom
  have hΦs : Function.Surjective Φ := (Units.mapEquiv _).surjective
  have hΦc : Continuous Φ := by
    refine Units.continuous_iff.2 ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
    · exact Units.continuous_val.matrix_elem (ψ.symm i) (ψ.symm j)
    · exact Units.continuous_coe_inv.matrix_elem (ψ.symm i) (ψ.symm j)
  have h1 := (hP k _ d hd).1 V (π.comp Φ) (isSmooth_comp hπ Φ hΦc)
    ((hasFiniteLength_comp_iff π Φ hΦs).2 hl)
  have h2 : HasFiniteLength (jacU (finSigmaFinEquiv.trans ψ) π) :=
    hasFiniteLength_jacU_reindex _ ψ π
      ((hasFiniteLength_twist_iff (jacU finSigmaFinEquiv (π.comp Φ)) _).1 h1)
  have he : finSigmaFinEquiv.trans ψ = e₁ := by
    ext x
    simp [ψ]
  rw [he] at h2
  exact (hasFiniteLength_twist_iff (jacU e π) (deltaHalf k m)⁻¹).2
    (hasFiniteLength_jacU_relabel e s _ hf hs π h2)
end GlobalTheory.JacquetBlocks
