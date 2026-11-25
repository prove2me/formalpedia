-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.modularCharacter_leviPar_of_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:44:26.456451+00:00
-- url     : https://prove2.me/submissions/f3aa7285-6042-4e5c-b712-120ddce9edef

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaModular
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_modularCharacter_leviPar
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_apply_self_ne_zero_of_diagonal
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_inv_apply_of_diagonal
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_det_adLeviPar_of_diagonal
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Measures_modulus_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_Measures_modulus_units
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa MeasureTheory Measure Topology Set ValuativeRel Measures
open scoped NNReal
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α α' : Type*} [LinearOrder α] [LinearOrder α'] {γ : Fin n → α} {δ : Fin n → α'}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (l : leviPar F n γ δ)
    (hl : ∀ i j, i ≠ j → ((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0) :
    modularCharacter l = ∏ s : {ij : Fin n × Fin n // γ ij.1 = γ ij.2 ∧ δ ij.1 < δ ij.2},
      modulus (((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.1) /
        modulus (((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.2 s.1.2) := by
  classical
  rw [modularCharacter_leviPar, ← modulus_units, det_adLeviPar_of_diagonal l hl, map_prod]
  set f : Fin n → ℝ≥0 := fun i => modulus (((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i)
  have hf : ∀ i, f i ≠ 0 := fun i => modulus_ne_zero (apply_self_ne_zero_of_diagonal hl i)
  have hfac : ∀ s : LeviParIndex n γ δ,
      modulus (((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.1 *
        (((l : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.2 s.1.2) =
      f s.1.1 / f s.1.2 := by
    intro s
    rw [map_mul, inv_apply_of_diagonal hl, if_pos rfl, map_inv₀, div_eq_mul_inv]
  rw [Finset.prod_congr rfl fun s _ => hfac s]
  change ∏ s : LeviParIndex n γ δ, f s.1.1 / f s.1.2 =
    ∏ s : {ij : Fin n × Fin n // γ ij.1 = γ ij.2 ∧ δ ij.1 < δ ij.2}, f s.1.1 / f s.1.2
  let g : Fin n × Fin n → ℝ≥0 := fun ij => f ij.1 / f ij.2
  rw [← Finset.prod_subtype (Finset.univ.filter fun ij : Fin n × Fin n =>
        γ ij.1 = γ ij.2 ∧ ¬ δ ij.2 < δ ij.1) (by simp) g,
    ← Finset.prod_subtype (Finset.univ.filter fun ij : Fin n × Fin n =>
        γ ij.1 = γ ij.2 ∧ δ ij.1 < δ ij.2) (by simp) g]
  have hsplit : (Finset.univ.filter fun ij : Fin n × Fin n => γ ij.1 = γ ij.2 ∧ ¬ δ ij.2 < δ ij.1) =
      (Finset.univ.filter fun ij : Fin n × Fin n => γ ij.1 = γ ij.2 ∧ δ ij.1 < δ ij.2) ∪
        (Finset.univ.filter fun ij : Fin n × Fin n => γ ij.1 = γ ij.2 ∧ δ ij.1 = δ ij.2) := by
    ext ij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, not_lt]
    constructor
    · rintro ⟨h1, h2⟩
      rcases h2.lt_or_eq with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨h1, h⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, h2.le⟩
      · exact ⟨h1, h2.le⟩
  have hdisj : Disjoint
      (Finset.univ.filter fun ij : Fin n × Fin n => γ ij.1 = γ ij.2 ∧ δ ij.1 < δ ij.2)
      (Finset.univ.filter fun ij : Fin n × Fin n => γ ij.1 = γ ij.2 ∧ δ ij.1 = δ ij.2) := by
    rw [Finset.disjoint_filter]
    intro ij _ h1 h2
    exact h1.2.ne h2.2
  rw [hsplit, Finset.prod_union hdisj]
  set S := Finset.univ.filter fun ij : Fin n × Fin n => γ ij.1 = γ ij.2 ∧ δ ij.1 = δ ij.2
  have hswap : ∏ ij ∈ S, f ij.2 = ∏ ij ∈ S, f ij.1 := by
    refine Finset.prod_nbij' Prod.swap Prod.swap (fun ij hij => ?_) (fun ij hij => ?_)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap,
        Prod.snd_swap] at hij ⊢
      exact ⟨hij.1.symm, hij.2.symm⟩
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap,
        Prod.snd_swap] at hij ⊢
      exact ⟨hij.1.symm, hij.2.symm⟩
  have hone : ∏ ij ∈ S, g ij = 1 := by
    rw [Finset.prod_div_distrib, hswap, div_self]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hf _
  rw [hone, mul_one]
end GroundTheory.Automorphic.Parabolic
