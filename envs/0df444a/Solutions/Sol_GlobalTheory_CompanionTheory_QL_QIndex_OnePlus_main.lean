-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.QIndex.OnePlus.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:36:24.682889+00:00
-- url     : https://prove2.me/submissions/c9cf1dda-3ae5-496c-a807-6e0778c50904

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDet
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemBoxLatticeIffCongruence
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_OnePlus_nrm_det_one_add
import Theorems.Thm_GlobalTheory_CompanionTheory_QLDet_mem_GLint_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_main


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex GlobalTheory.CompanionTheory.QL.QIndex.OnePlus
namespace GlobalTheory.CompanionTheory.QL.QIndex.OnePlus
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (n : ℕ) (β : Fin n → ℕ) (Q : Subgroup (GL (Fin n) F)), (∀ g, g ∈ Q ↔ (g : Matrix (Fin n) (Fin n) F).BlockTriangular β) → ∀ T : ℕ, 1 ≤ T → ∀ x : Matrix (Fin n) (Fin n) F, x ∈ boxAdd O β (fun _ _ => ϖ ^ T) ↔ ∃ p ∈ (congGL O (ϖ ^ T) n).subgroupOf Q, ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + x := by
  intro F _ _ _ _ O ϖ nrm q hLF n β Q hQ T hT x
  obtain ⟨-, hϖ, -, -, -, -, -⟩ := GlobalTheory.CompanionTheory.QL.NormalisedValue.main hLF
  constructor
  · rintro ⟨hbt, hent⟩
    have hx' : ∀ a b, ∃ o ∈ O, x a b = ϖ * o := fun a b => by
      obtain ⟨o, ho, e⟩ := hent a b
      have e' : x a b = ϖ ^ T * o := e
      have hTT : ϖ ^ T = ϖ * ϖ ^ (T - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hT]
      refine ⟨ϖ ^ (T - 1) * o, O.mul_mem (O.pow_mem hϖ _) ho, ?_⟩
      rw [e', hTT, mul_assoc]
    have hdet := nrm_det_one_add hLF hx'
    have hne : (1 + x).det ≠ 0 := fun e => by
      rw [e] at hdet
      simp at hdet
    let g : GL (Fin n) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + x) hne
    have hg : (g : Matrix (Fin n) (Fin n) F) = 1 + x := rfl
    have hint : IsInt O (g : Matrix (Fin n) (Fin n) F) := fun a b => by
      rw [hg, Matrix.add_apply]
      obtain ⟨o, ho, e⟩ := hx' a b
      refine O.add_mem ?_ (e ▸ O.mul_mem hϖ ho)
      by_cases hab : a = b
      · rw [hab, Matrix.one_apply_eq]
        exact O.one_mem
      · rw [Matrix.one_apply_ne hab]
        exact O.zero_mem
    have hgQ : g ∈ Q := by
      rw [hQ, hg]
      intro i j hij
      have hne' : i ≠ j := fun e => by
        subst e
        exact lt_irrefl _ hij
      simp [hbt hij, hne']
    refine ⟨⟨g, hgQ⟩, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    refine ⟨(GlobalTheory.CompanionTheory.QLDet.mem_GLint_iff hLF n g).2 ⟨hint, hdet⟩, fun a b => ?_⟩
    obtain ⟨o, ho, e⟩ := hent a b
    refine ⟨o, ho, ?_⟩
    simpa [hg] using e
  · rintro ⟨p, hp, e⟩
    rw [Subgroup.mem_subgroupOf] at hp
    obtain ⟨-, hl⟩ := hp
    have hx : x = ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 := by
      rw [e]
      simp
    refine ⟨fun i j hij => ?_, fun a b => ?_⟩
    · have h0 := (hQ _).1 p.2 hij
      have hne' : i ≠ j := fun e => by
        subst e
        exact lt_irrefl _ hij
      simp [hx, h0, hne']
    · rw [hx]
      exact hl a b
end GlobalTheory.CompanionTheory.QL.QIndex.OnePlus
