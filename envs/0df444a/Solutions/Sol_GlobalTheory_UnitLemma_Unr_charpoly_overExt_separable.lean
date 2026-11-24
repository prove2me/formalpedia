-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.charpoly_overExt_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:21:06.813233+00:00
-- url     : https://prove2.me/submissions/0ba7c91f-8d90-44ab-b410-3adaee48a387

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SeparableCharpolyInvAlgBaseChangeUnramified
import Theorems.Thm_GlobalTheory_UnitLemma_exists_basis_pow_of_separable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ →
    ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e)
      (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)), B.P.Separable → (overExt φ B ψ hψ hσ).P.Separable := by
  intro K K' d φ _ B ψ hψ hσ hsep

  obtain ⟨e, he⟩ := exists_basis_pow_of_separable K B hsep

  have hP : aeval B.g B.P = 0 := by
    have h1 := LinearMap.aeval_self_charpoly (LinearMap.mulLeft K.E B.g)
    have h2 : aeval (LinearMap.mulLeft K.E B.g) B.P = Algebra.lmul K.E B.A (aeval B.g B.P) := by
      rw [← Polynomial.aeval_algHom_apply]; rfl
    have h3 := congrArg (fun f : Module.End K.E B.A => f 1) (h2.symm.trans h1)
    simpa using h3
  set B' := overExt φ B ψ hψ hσ with hB'
  have hg : B'.g = B.g := rfl
  have hmap : ∀ x : K'.E, algebraMap K'.E B'.A x = ψ x := fun x => rfl
  have hint : IsIntegral K'.E B'.g := Algebra.IsIntegral.isIntegral _

  have htop : Algebra.adjoin K'.E {B'.g} = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have hy : (y : B.A) = ∑ i, (e.repr y i) • e i := (e.sum_repr y).symm
    change (y : B'.A) ∈ Algebra.adjoin K'.E {B'.g}
    have : (y : B'.A) = ∑ i, algebraMap K'.E B'.A (φ (e.repr y i)) * B'.g ^ (i : ℕ) := by
      refine hy.trans (Finset.sum_congr rfl fun i _ => ?_)
      rw [hmap, hψ, he, Algebra.smul_def]; rfl
    rw [this]
    exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) _)
  let pb := PowerBasis.ofAdjoinEqTop hint htop
  have hchar : B'.P = minpoly K'.E B'.g := by
    have h1 := charpoly_leftMulMatrix pb
    rw [PowerBasis.ofAdjoinEqTop_gen] at h1
    rw [← h1, Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]
    rfl
  have hdvd : minpoly K'.E B'.g ∣ B.P.map φ := by
    refine minpoly.dvd _ _ ?_
    rw [aeval_def, eval₂_map]
    have : (algebraMap K'.E B'.A).comp φ = algebraMap K.E B.A := RingHom.ext fun x => hψ x
    rw [this]
    exact hP
  rw [hchar]
  exact (hsep.map).of_dvd hdvd
end GlobalTheory.UnitLemma.Unr
