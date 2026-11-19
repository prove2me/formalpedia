-- Prove2me | solution 1 for OAI.Saxl.even_rows_shortPair_support
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:36:26.892364+00:00
-- url     : https://prove2.me/submissions/b85abb05-142d-4a11-929f-5526df276d40

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US023
import Theorems.Thm_OAI_Saxl_even_rows_symmetricPairs_support

section
-- module Solutions.OAIQ259_US.Saxl_CyclicSector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY uZ uV

namespace Saxl

theorem cyclic_projection_support {G : Type uG} {X : Type uX} {Y : Type uY} {Z : Type uZ} [Group G] [Finite G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y} {τ : Representation ℂ G Z}
    (F : Representation.IntertwiningMap ρ σ) (v : X)
    (f : Representation.IntertwiningMap τ (cyclic σ (F v)).toRepresentation) (hf : f ≠ 0) :
    ∃ g : Representation.IntertwiningMap τ (cyclic ρ v).toRepresentation, g ≠ 0 := by
  obtain ⟨g,hg⟩ := intertwining_lift_surjective (cyclicMap F v) (cyclicMap_surjective F v) f
  refine ⟨g, ?_⟩
  intro hz
  apply hf
  rw [← hg,hz]
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact map_zero (cyclicMap F v)



lemma cyclic_smul_eq {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) (c : ℂ) (hc : c ≠ 0) :
    cyclic ρ (c • v) = cyclic ρ v := by
  apply le_antisymm
  · apply (cyclic_le _ _ _).mpr
    exact Submodule.smul_mem _ _ (mem_cyclic ρ v)
  · apply (cyclic_le _ _ _).mpr
    have hh := Submodule.smul_mem (cyclic ρ (c • v)).toSubmodule c⁻¹ (mem_cyclic ρ (c • v))
    change v ∈ (cyclic ρ (c • v)).toSubmodule
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hh

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_PairForms
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Forms. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma pairFormTensor_one {n m d : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m) :
    pairFormTensor e (1 : Matrix (Fin d) (Fin d) ℂ) = symmetricPairs e d := by
  classical
  funext w
  change (∏ i, if leftWord e w i = rightWord e w i then (1 : ℂ) else 0) = _
  by_cases hw : leftWord e w = rightWord e w
  · simp [hw, symmetricPairs]
  · have hi : ∃ i, leftWord e w i ≠ rightWord e w i := by
      exact not_forall.mp (fun he => hw (funext he))
    obtain ⟨i, hi⟩ := hi
    rw [symmetricPairs, ite_eq_right hw]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma pairFormTensor_smul {n m d : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m)
    (c : ℂ) (B : Matrix (Fin d) (Fin d) ℂ) :
    pairFormTensor e (c • B) = c^m • pairFormTensor e B := by
  funext w
  simp [pairFormTensor, Finset.prod_mul_distrib]

lemma wordMap_pairFormTensor {n m a b : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m)
    (L : Fin a → Fin b → ℂ) (B : Matrix (Fin a) (Fin a) ℂ) :
    wordMap L (pairFormTensor e B) = pairFormTensor e
      (fun j k => ∑ p : Fin a × Fin a, B p.1 p.2 * L p.1 j * L p.2 k) := by
  classical
  funext w
  change (∑ c, pairFormTensor e B c * ∏ i, L (c i) (w i)) = _
  calc
    _ = ∑ c : Fin m → Fin a × Fin a,
        ∏ i, B (c i).1 (c i).2 * L (c i).1 (leftWord e w i) *
          L (c i).2 (rightWord e w i) := by
      apply Fintype.sum_equiv (pairWordsEquiv e)
      intro c
      simp only [pairWordsEquiv_apply, pairFormTensor, Finset.prod_mul_distrib]
      have he : (∏ i, L (c i) (w i)) =
          (∏ i, L (leftWord e c i) (leftWord e w i)) *
            ∏ i, L (rightWord e c i) (rightWord e w i) := by
        calc
          _ = ∏ x : Fin m ⊕ Fin m, L (c (e.symm x)) (w (e.symm x)) :=
            (Equiv.prod_comp e.symm (fun i => L (c i) (w i))).symm
          _ = _ := by
            rw [Fintype.prod_sum_type]
            rfl
      rw [he, mul_assoc]
    _ = _ := by
      change (∑ c : Fin m → Fin a × Fin a,
        ∏ i, B (c i).1 (c i).2 * L (c i).1 (leftWord e w i) *
          L (c i).2 (rightWord e w i)) =
        ∏ i, ∑ p : Fin a × Fin a,
          B p.1 p.2 * L p.1 (leftWord e w i) * L p.2 (rightWord e w i)
      exact (Fintype.prod_sum (fun (i : Fin m) (p : Fin a × Fin a) =>
        B p.1 p.2 * L p.1 (leftWord e w i) * L p.2 (rightWord e w i))).symm

theorem even_rows_pairFormTensor_support {n m a d : ℕ}
    (e : Fin n ≃ Fin m ⊕ Fin m) (B : Matrix (Fin a) (Fin a) ℂ)
    (L : Fin a → Fin d → ℂ) (c : ℂ) (hc : c ≠ 0)
    (hL : (fun j k => ∑ p : Fin a × Fin a, B p.1 p.2 * L p.1 j * L p.2 k) =
      c • (1 : Matrix (Fin d) (Fin d) ℂ))
    (μ : YoungDiagram) (t : Tableau n μ)
    (he : ∀ i, Even (μ.rowLen i)) (hd : μ.colLen 0 ≤ d) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n a) (pairFormTensor e B)).toRepresentation, F ≠ 0 := by
  have hmap : wordMap L (pairFormTensor e B) = c^m • symmetricPairs e d := by
    rw [wordMap_pairFormTensor, hL, pairFormTensor_smul, pairFormTensor_one]
  have hs := even_rows_symmetricPairs_support e μ t he hd
  have hcyc : cyclic (wordRep n d) (wordMap L (pairFormTensor e B)) =
      cyclic (wordRep n d) (symmetricPairs e d) := by
    rw [hmap, cyclic_smul_eq _ _ _ (pow_ne_zero m hc)]
  rw [← hcyc] at hs
  obtain ⟨F,hF⟩ := hs
  exact cyclic_projection_support (wordMap L) (pairFormTensor e B) F hF

lemma shortPairCongruence_gram :
    (fun j k => ∑ p : Fin 4 × Fin 4,
      shortPairForm p.1 p.2 * shortPairCongruence p.1 j * shortPairCongruence p.2 k) =
      (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    (first | (simp [Fintype.sum_prod_type, Fin.sum_univ_succ, shortPairForm, shortPairCongruence, Matrix.one_apply]; all_goals first | (norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, shortPairForm, shortPairCongruence, Matrix.one_apply]; done) | rfl | decide) | (norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, shortPairForm, shortPairCongruence, Matrix.one_apply]; done) | norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, shortPairForm, shortPairCongruence, Matrix.one_apply])

theorem even_rows_shortPair_support_oai {n m : ℕ}
    (e : Fin n ≃ Fin m ⊕ Fin m) (μ : YoungDiagram) (t : Tableau n μ)
    (he : ∀ i, Even (μ.rowLen i)) (hd : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n 4) (pairFormTensor e shortPairForm)).toRepresentation, F ≠ 0 :=
  even_rows_pairFormTensor_support e shortPairForm shortPairCongruence 2 (by norm_num)
    shortPairCongruence_gram μ t he hd

end Saxl
end
end

end OAI
end

theorem solution : type_of% @OAI.Saxl.even_rows_shortPair_support_oai := @OAI.Saxl.even_rows_shortPair_support_oai
