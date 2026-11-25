-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.QIndex.ConjLe.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:36:19.596258+00:00
-- url     : https://prove2.me/submissions/c7ca3d6a-9d11-4ab0-b0fc-f08e8595b758

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDet
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DiagonalConjugateCongruenceBox
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_ConjLe_diag_inv
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_ConjLe_conj_entry
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_ConjLe_mem_congGL_of_lvl
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_mem_conjSub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex GlobalTheory.CompanionTheory.QL.QIndex.ConjLe
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
namespace GlobalTheory.CompanionTheory.QL.QIndex.ConjLe
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (n : ℕ) (β : Fin n → ℕ) (Q : Subgroup (GL (Fin n) F)), (∀ g, g ∈ Q ↔ (g : Matrix (Fin n) (Fin n) F).BlockTriangular β) → ∀ T : ℕ, 1 ≤ T → ∀ d : Q, ((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag → (∀ a b, ϖ ^ T * (((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a a * (((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) b b)⁻¹) ∈ O) → conjSub ((congGL O (ϖ ^ (2 * T)) n).subgroupOf Q) d ≤ (congGL O (ϖ ^ T) n).subgroupOf Q ∧ ∀ p ∈ (congGL O (ϖ ^ T) n).subgroupOf Q, (p ∈ conjSub ((congGL O (ϖ ^ (2 * T)) n).subgroupOf Q) d ↔ ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 ∈ boxAdd O β (lev ϖ T fun a => ((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a a)) := by
  intro F _ _ _ _ O ϖ nrm q hLF n β Q hQ T hT d hdiag hd
  have hD : ((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal fun a => ((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a a :=
    hdiag.diagonal_diag.symm
  obtain ⟨hne, -⟩ := diag_inv (d : GL (Fin n) F) hD
  have hent := fun (p : GL (Fin n) F) => conj_entry (d : GL (Fin n) F) p hD
  have hconj : ∀ p : Q, ((d * p * d⁻¹ : Q) : GL (Fin n) F) =
      (d : GL (Fin n) F) * (p : GL (Fin n) F) * (d : GL (Fin n) F)⁻¹ := fun p => rfl
  have h2T : 1 ≤ 2 * T := by omega
  refine ⟨fun p hp => ?_, fun p _ => ?_⟩
  · rw [mem_conjSub, Subgroup.mem_subgroupOf, hconj] at hp
    rw [Subgroup.mem_subgroupOf]
    refine mem_congGL_of_lvl hLF hT _ fun a b => ?_
    obtain ⟨o, ho, e⟩ := hp.2 a b
    rw [hent] at e
    refine ⟨o * (ϖ ^ T * (((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) b b *
      (((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a a)⁻¹)), O.mul_mem ho (hd b a), ?_⟩
    have hna := hne a
    have hnb := hne b
    field_simp at e ⊢
    linear_combination e
  · rw [mem_conjSub, Subgroup.mem_subgroupOf, hconj]
    constructor
    · intro hp
      refine ⟨((hQ _).1 p.2).sub (blockTriangular_one), fun a b => ?_⟩
      obtain ⟨o, ho, e⟩ := hp.2 a b
      rw [hent] at e
      refine ⟨o, ho, ?_⟩
      have hna := hne a
      have hnb := hne b
      simp only [lev]
      field_simp at e ⊢
      linear_combination e
    · rintro ⟨-, hx⟩
      refine mem_congGL_of_lvl hLF h2T _ fun a b => ?_
      obtain ⟨o, ho, e⟩ := hx a b
      refine ⟨o, ho, ?_⟩
      rw [hent, e]
      have hna := hne a
      have hnb := hne b
      simp only [lev]
      field_simp
end GlobalTheory.CompanionTheory.QL.QIndex.ConjLe
