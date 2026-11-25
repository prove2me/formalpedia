-- Prove2me | solution 1 for GlobalTheory.existsUnique_ringHom_OmS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:43:07.083247+00:00
-- url     : https://prove2.me/submissions/03a45c73-a681-43de-8767-3b03e2e46499

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussIndepOfLeTrdeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_AlgebraicIndependentFreeVar
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_card_le_trdeg_add
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_indep_of_le_trdeg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
open MvPolynomial
open NumberField
open scoped TensorProduct
open MvPolynomial
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (K Ω L : Type) [Field K] [Field Ω] [Algebra K Ω] [Field L] [Algebra K L] (D N : ℕ)
      (j₀ : Fin (N + 1)) (x : Fin N → Ω) (τ : _root_.ReciprocityTheory.ChartRestriction.G.T0.TVar D N → L) (φ : Ω →ₐ[K] L),
      Algebra.trdeg K Ω = D → AlgebraicIndependent K τ →
      (∀ i : Fin D, τ (i.succ, j₀) + ∑ k, τ (i.succ, j₀.succAbove k) * φ (x k) = 0) →
      ∃! P : _root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N →+* L, (∀ a : Ω, P (algebraMap Ω (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N) a) = φ a) ∧
        ∀ p, P (_root_.ReciprocityTheory.ChartRestriction.G.T0.sImg j₀ x p) = τ p := by
  intro K Ω L _ _ _ _ _ D N j₀ x τ φ hD hτ hrel
  letI : Algebra Ω L := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K Ω L := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  have hΩ : ∀ a : Ω, algebraMap Ω L a = φ a := fun _ => rfl

  let g : _root_.ReciprocityTheory.ChartRestriction.G.T0.SVar D N → L := fun v => τ (_root_.GlobalTheory.SectionPoint.freeVarIndex j₀ v)
  have hg0 : g (Sum.inl ()) = τ (0, j₀) := rfl
  have hg1 : ∀ i k, g (Sum.inr (i, k)) = τ (i, j₀.succAbove k) := fun _ _ => rfl
  have hsub : ∀ p, τ p ∈ Algebra.adjoin Ω (Set.range g) := by
    rintro ⟨i, j⟩
    rcases Fin.eq_self_or_eq_succAbove j₀ j with rfl | ⟨k, rfl⟩
    · cases i using Fin.cases with
      | zero => exact Algebra.subset_adjoin ⟨Sum.inl (), hg0⟩
      | succ i =>
        rw [eq_neg_of_add_eq_zero_left (hrel i)]
        refine Subalgebra.neg_mem _ (Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ ?_ ?_)
        · exact Algebra.subset_adjoin ⟨Sum.inr (i.succ, k), hg1 _ _⟩
        · rw [← hΩ]
          exact Subalgebra.algebraMap_mem _ _
    · exact Algebra.subset_adjoin ⟨Sum.inr (i, k), hg1 _ _⟩
  have hcard := _root_.ReciprocityTheory.MultiplicativeHeights.gauss_card_le_trdeg_add (F := K) (E := Ω) (C := L) g τ hτ hsub
  rw [hD] at hcard
  have hind : AlgebraicIndependent Ω g := by
    apply _root_.ReciprocityTheory.MultiplicativeHeights.gauss_indep_of_le_trdeg
    change Cardinal.mk (Unit ⊕ Fin (D + 1) × Fin N) ≤ _
    change Cardinal.mk (Fin (D + 1) × Fin (N + 1)) ≤ _ at hcard
    simp only [Cardinal.mk_fintype, Fintype.card_sum, Fintype.card_prod, Fintype.card_unit,
      Fintype.card_fin] at hcard ⊢
    rcases lt_or_ge (Algebra.trdeg Ω (Algebra.adjoin Ω (Set.range g))) Cardinal.aleph0 with ht | ht
    · obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.1 ht
      rw [hm] at hcard ⊢
      norm_cast at hcard ⊢
      nlinarith
    · exact le_trans (Cardinal.nat_lt_aleph0 _).le ht
  have hinj : Function.Injective (MvPolynomial.aeval (R := Ω) g).toRingHom :=
    algebraicIndependent_iff_injective_aeval.1 hind
  let P : _root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N →+* L := IsFractionRing.lift (K := _root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N) hinj
  have hP : ∀ f, P (algebraMap (MvPolynomial (_root_.ReciprocityTheory.ChartRestriction.G.T0.SVar D N) Ω) (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N) f) =
      MvPolynomial.aeval g f := fun f => IsFractionRing.lift_algebraMap hinj f
  have hC : ∀ a : Ω, algebraMap Ω (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N) a =
      algebraMap (MvPolynomial (_root_.ReciprocityTheory.ChartRestriction.G.T0.SVar D N) Ω) (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N) (C a) := fun a =>
    IsScalarTower.algebraMap_apply Ω (MvPolynomial (_root_.ReciprocityTheory.ChartRestriction.G.T0.SVar D N) Ω) (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N) a
  have hfree : ∀ v, _root_.ReciprocityTheory.ChartRestriction.G.T0.sImg j₀ x (_root_.GlobalTheory.SectionPoint.freeVarIndex j₀ v) =
      algebraMap (MvPolynomial (_root_.ReciprocityTheory.ChartRestriction.G.T0.SVar D N) Ω) (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N) (X v) := by
    rintro (⟨⟩ | ⟨i, k⟩)
    · simp [_root_.ReciprocityTheory.ChartRestriction.G.T0.sImg, _root_.GlobalTheory.SectionPoint.freeVarIndex]
    · simp [_root_.ReciprocityTheory.ChartRestriction.G.T0.sImg, _root_.GlobalTheory.SectionPoint.freeVarIndex]
  have hPΩ : ∀ a : Ω, P (algebraMap Ω (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N) a) = φ a := fun a => by
    rw [hC, hP, MvPolynomial.aeval_C, hΩ]
  have hPτ : ∀ p, P (_root_.ReciprocityTheory.ChartRestriction.G.T0.sImg j₀ x p) = τ p := by
    rintro ⟨i, j⟩
    rcases Fin.eq_self_or_eq_succAbove j₀ j with rfl | ⟨k, rfl⟩
    · cases i using Fin.cases with
      | zero => exact (congrArg P (hfree (Sum.inl ()))).trans ((hP _).trans (aeval_X _ _))
      | succ i =>
        have h := eq_neg_of_add_eq_zero_left (hrel i)
        simp [_root_.ReciprocityTheory.ChartRestriction.G.T0.sImg, hP, hg1, hΩ, Fin.succ_ne_zero]
        exact h.symm
    · exact (congrArg P (hfree (Sum.inr (i, k)))).trans ((hP _).trans (aeval_X _ _))
  refine ⟨P, ⟨hPΩ, hPτ⟩, fun Q ⟨hQΩ, hQτ⟩ => ?_⟩
  refine IsFractionRing.ringHom_ext (A := MvPolynomial (_root_.ReciprocityTheory.ChartRestriction.G.T0.SVar D N) Ω) ?_
  intro f
  refine RingHom.congr_fun (MvPolynomial.ringHom_ext
    (f := Q.comp (algebraMap (MvPolynomial (_root_.ReciprocityTheory.ChartRestriction.G.T0.SVar D N) Ω) (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N)))
    (g := P.comp (algebraMap (MvPolynomial (_root_.ReciprocityTheory.ChartRestriction.G.T0.SVar D N) Ω) (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N)))
    (fun a => ?_) (fun v => ?_)) f
  · simp only [RingHom.comp_apply, ← hC, hQΩ, hPΩ]
  · simp only [RingHom.comp_apply, ← hfree, hQτ, hPτ]
end _root_.GlobalTheory
end GlobalTheory
