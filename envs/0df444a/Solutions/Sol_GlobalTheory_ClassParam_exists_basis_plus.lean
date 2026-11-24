-- Prove2me | solution 1 for GlobalTheory.ClassParam.exists_basis_plus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:12:44.947186+00:00
-- url     : https://prove2.me/submissions/747a8abb-fb49-4bfe-98b1-1b788ebc4fd7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PlusPolynomialInclusion_starL_of
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PlusPolynomialInclusion_starL_starL


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix Formalism.UG
open GlobalTheory GlobalTheory.ClassParam
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
attribute [local instance] algLk
variable {F E : Type} [Field F] [Field E] [Algebra F E] {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}
  (k : Type) [Field k] [Algebra F k]
namespace GlobalTheory.ClassParam
theorem _root_.solution [CharZero E] (hP : IsPPol c r P) (hc : ∀ e, c (c e) = e) (hc1 : c ≠ 1)
    (hF : ∀ e, c e = e → ∃ a, algebraMap F E a = e) {ι : Type} [Fintype ι]
    (b : Module.Basis ι F (Lplus hP)) :
    ∃ b' : Module.Basis ι E (AdjoinRoot P), ∀ i, b' i = b i := by
  obtain ⟨e₀, he₀⟩ : ∃ e, c e ≠ e := by
    by_contra h
    push Not at h
    exact hc1 (AlgEquiv.ext h)
  set δ := e₀ - c e₀ with hδ
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 he₀.symm
  have hcδ : c δ = -δ := by rw [hδ, map_sub, hc, neg_sub]
  have hsm : ∀ (e : E) (l : AdjoinRoot P), starL hP (e • l) = c e • starL hP l := fun e l => by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    exact congrArg (· * _) (starL_of hP e)
  have hfix : ∀ i, starL hP (b i) = b i := fun i => (b i).2
  refine ⟨Module.Basis.mk (v := fun i => (b i : AdjoinRoot P)) ?_ ?_,
    fun i => Module.Basis.mk_apply _ _ _⟩
  · have key : ∀ g : ι → E, ∑ i, g i • (b i : AdjoinRoot P) = 0 → ∀ j, g j + c (g j) = 0 := by
      intro g hg j
      have h1 := congrArg (starL hP) hg
      simp only [map_sum, hsm, hfix, map_zero] at h1
      choose a ha using fun i => hF (g i + c (g i)) (by rw [map_add, hc, add_comm])
      have h2 : ∑ i, a i • b i = 0 := by
        apply Subtype.val_injective
        have : ∑ i, a i • (b i : AdjoinRoot P) = 0 := by
          simp only [← IsScalarTower.algebraMap_smul E (a _), ha, add_smul,
            Finset.sum_add_distrib, hg, h1, add_zero]
        simpa using this
      rw [← ha, Fintype.linearIndependent_iff.1 b.linearIndependent a h2 j, map_zero]
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h1 := key g hg j
    have h2 := key (fun i => δ * g i) (by
      simp only [mul_smul, ← Finset.smul_sum, hg, smul_zero]) j
    rw [map_mul, hcδ] at h2
    have : (2 * δ) * g j = 0 := by linear_combination δ * h1 + h2
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero hδ0)
  · have key : ∀ l, starL hP l = l →
        l ∈ Submodule.span E (Set.range fun i => (b i : AdjoinRoot P)) := by
      intro l hl
      have h := congrArg Subtype.val (b.sum_repr ⟨l, hl⟩)
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at h
      rw [← h]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    rintro l -
    have h1 := key (l + starL hP l) (by rw [map_add, starL_starL hP hc, add_comm])
    have h2 := key (δ • (l - starL hP l)) (by
      rw [hsm, hcδ, map_sub, starL_starL hP hc, neg_smul, ← smul_neg, neg_sub])
    have : l = (2 : E)⁻¹ • ((l + starL hP l) + δ⁻¹ • δ • (l - starL hP l)) := by
      rw [inv_smul_smul₀ hδ0, add_add_sub_cancel, ← two_smul E l, inv_smul_smul₀ two_ne_zero]
    rw [this]
    exact Submodule.smul_mem _ _ (add_mem h1 (Submodule.smul_mem _ _ h2))
end GlobalTheory.ClassParam
