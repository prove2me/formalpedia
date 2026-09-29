-- Prove2me | solution 1 for HopfAlgebra.blockPieces_torsor_core_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/b20d3ff6-9fdf-53de-a83f-26b2ea0d3505

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_TorsorGrading
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_blockPieces_torsor_core_of_isAlgClosed

set_option autoImplicit false

set_option maxHeartbeats 1600000

open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace S17
namespace TorsorCoreGen
open HopfAlgebra.TorsorGrading

open TensorProduct

variable (A : Type) [AddCommGroup A] [DecidableEq A]
variable {R H : Type} [CommRing R] [CommRing H] [Bialgebra R H]
variable (π : H →ₐc[R] MonoidAlgebra R (Multiplicative A))

section MAHelpers

variable (N : Type) [AddCommGroup N] [Module R N]

def maScalarLeft : MonoidAlgebra R (Multiplicative A) ⊗[R] N ≃ₗ[R] (Multiplicative A →₀ N) :=
  ((MonoidAlgebra.coeffLinearEquiv R).rTensor N) ≪≫ₗ
    TensorProduct.finsuppScalarLeft R N (Multiplicative A)

theorem maScalarLeft_tmul (p : MonoidAlgebra R (Multiplicative A)) (n : N) :
    maScalarLeft A N (p ⊗ₜ[R] n) = p.coeff.sum fun i m => Finsupp.single i (m • n) := by
  rw [maScalarLeft, LinearEquiv.trans_apply, LinearEquiv.rTensor_tmul,
    MonoidAlgebra.coeffLinearEquiv_apply, TensorProduct.finsuppScalarLeft_apply_tmul]

theorem maScalarLeft_single_tmul (g : Multiplicative A) (r : R) (n : N) :
    maScalarLeft A N (MonoidAlgebra.single g r ⊗ₜ[R] n) = Finsupp.single g (r • n) := by
  rw [maScalarLeft_tmul, MonoidAlgebra.coeff_single,
    Finsupp.sum_single_index (by rw [zero_smul, Finsupp.single_zero])]

theorem maScalarLeft_symm_single (g : Multiplicative A) (n : N) :
    (maScalarLeft A N).symm (Finsupp.single g n)
      = MonoidAlgebra.single g (1 : R) ⊗ₜ[R] n := by
  rw [LinearEquiv.symm_apply_eq, maScalarLeft_single_tmul, one_smul]

theorem gradingComponents_eq_maScalarLeft (t : H) :
    gradingComponents A π t = maScalarLeft A H (gradingCoaction A π t) := rfl

end MAHelpers


theorem gradingCoaction_eq_of_mem {j : A} {t : H} (ht : t ∈ gradedPiece A π j) :
    gradingCoaction A π t
      = MonoidAlgebra.single (Multiplicative.ofAdd j) (1 : R) ⊗ₜ[R] t := by
  have ht' : gradingComponents A π t = Finsupp.single (Multiplicative.ofAdd j) t := ht
  rw [gradingComponents_eq_maScalarLeft, ← LinearEquiv.eq_symm_apply] at ht'
  rw [ht', maScalarLeft_symm_single]

omit [AddCommGroup A] [DecidableEq A] in

theorem comul_monoidAlgebra_single_one (g : Multiplicative A) :
    (Coalgebra.comul (R := R))
        (MonoidAlgebra.single g (1 : R)
          : MonoidAlgebra R (Multiplicative A))
      = MonoidAlgebra.single g (1 : R) ⊗ₜ[R] MonoidAlgebra.single g (1 : R) := by
  rw [MonoidAlgebra.comul_single]
  rw [show (Coalgebra.comul (R := R)) (1 : R) = (1 : R) ⊗ₜ[R] (1 : R) from by
    rw [Bialgebra.comul_one, Algebra.TensorProduct.one_def]]
  rw [TensorProduct.map_tmul]
  rfl

theorem gradingCoaction_eq_sum_components (t : H) :
    gradingCoaction A π t
      = (gradingComponents A π t).sum
          (fun g m => MonoidAlgebra.single g (1 : R) ⊗ₜ[R] m) := by
  have h := (maScalarLeft A H).symm_apply_apply (gradingCoaction A π t)
  rw [← gradingComponents_eq_maScalarLeft] at h
  rw [← h]
  conv_lhs => rw [show gradingComponents A π t
      = (gradingComponents A π t).sum (fun g m => Finsupp.single g m) from
    (Finsupp.sum_single _).symm]
  rw [Finsupp.sum]
  rw [map_sum]
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  exact maScalarLeft_symm_single A H g _

omit [DecidableEq A] in

theorem assoc_naturality_pi :
    (TensorProduct.map π.toLinearMap
        (LinearMap.rTensor H π.toLinearMap)) ∘ₗ
      (TensorProduct.assoc R H H H).toLinearMap
    = (TensorProduct.assoc R _ _ H).toLinearMap ∘ₗ
        (LinearMap.rTensor H
          (TensorProduct.map π.toLinearMap π.toLinearMap)) := by
  apply TensorProduct.ext_threefold
  intro x y z
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.assoc_tmul, TensorProduct.map_tmul, LinearMap.rTensor_tmul]

omit [DecidableEq A] in

theorem gradingCoaction_coassoc :
    (LinearMap.lTensor (MonoidAlgebra R (Multiplicative A))
        (gradingCoaction A π)) ∘ₗ gradingCoaction A π
    = (TensorProduct.assoc R _ _ H).toLinearMap ∘ₗ
        (LinearMap.rTensor H (Coalgebra.comul (R := R))) ∘ₗ
          gradingCoaction A π := by

  have hA : (LinearMap.lTensor (MonoidAlgebra R (Multiplicative A))
        (gradingCoaction A π)) ∘ₗ gradingCoaction A π
      = (TensorProduct.map π.toLinearMap
          (LinearMap.rTensor H π.toLinearMap)) ∘ₗ
        (LinearMap.lTensor H (Coalgebra.comul (R := R))) ∘ₗ
          Coalgebra.comul := by
    unfold gradingCoaction
    ext t
    simp only [LinearMap.coe_comp, Function.comp_apply]

    induction (Coalgebra.comul (R := R) t) with
    | zero => simp only [map_zero]
    | tmul a b =>
      simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        TensorProduct.map_tmul, LinearMap.coe_comp, Function.comp_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hB : (TensorProduct.assoc R _ _ H).toLinearMap ∘ₗ
        (LinearMap.rTensor H (Coalgebra.comul (R := R))) ∘ₗ
          gradingCoaction A π
      = (TensorProduct.assoc R _ _ H).toLinearMap ∘ₗ
          (LinearMap.rTensor H
            (TensorProduct.map π.toLinearMap π.toLinearMap)) ∘ₗ
            (LinearMap.rTensor H (Coalgebra.comul (R := R))) ∘ₗ
              Coalgebra.comul := by
    have hcoalg : (Coalgebra.comul (R := R)) ∘ₗ π.toLinearMap
        = (TensorProduct.map π.toLinearMap π.toLinearMap)
            ∘ₗ (Coalgebra.comul (R := R)) :=
      (CoalgHomClass.map_comp_comul π).symm
    have hfuse : (LinearMap.rTensor H (Coalgebra.comul (R := R))) ∘ₗ
          (LinearMap.rTensor H π.toLinearMap)
        = (LinearMap.rTensor H
            (TensorProduct.map π.toLinearMap π.toLinearMap)) ∘ₗ
            (LinearMap.rTensor H (Coalgebra.comul (R := R))) := by
      rw [← LinearMap.rTensor_comp H, hcoalg, LinearMap.rTensor_comp H]
    unfold gradingCoaction
    ext t
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    congr 1
    simpa using DFunLike.congr_fun hfuse ((Coalgebra.comul (R := R)) t)
  rw [hA, hB]
  calc (TensorProduct.map π.toLinearMap (LinearMap.rTensor H π.toLinearMap)) ∘ₗ
        (LinearMap.lTensor H (Coalgebra.comul (R := R))) ∘ₗ Coalgebra.comul
      = (TensorProduct.map π.toLinearMap (LinearMap.rTensor H π.toLinearMap)) ∘ₗ
          (TensorProduct.assoc R H H H).toLinearMap ∘ₗ
            (LinearMap.rTensor H (Coalgebra.comul (R := R))) ∘ₗ Coalgebra.comul := by
        rw [Coalgebra.coassoc]
    _ = ((TensorProduct.map π.toLinearMap (LinearMap.rTensor H π.toLinearMap)) ∘ₗ
          (TensorProduct.assoc R H H H).toLinearMap) ∘ₗ
            (LinearMap.rTensor H (Coalgebra.comul (R := R))) ∘ₗ Coalgebra.comul := by
        rw [LinearMap.comp_assoc]
    _ = ((TensorProduct.assoc R _ _ H).toLinearMap ∘ₗ
          (LinearMap.rTensor H
            (TensorProduct.map π.toLinearMap π.toLinearMap))) ∘ₗ
            (LinearMap.rTensor H (Coalgebra.comul (R := R))) ∘ₗ Coalgebra.comul := by
        rw [assoc_naturality_pi A π]
    _ = (TensorProduct.assoc R _ _ H).toLinearMap ∘ₗ
          (LinearMap.rTensor H
            (TensorProduct.map π.toLinearMap π.toLinearMap)) ∘ₗ
            (LinearMap.rTensor H (Coalgebra.comul (R := R))) ∘ₗ Coalgebra.comul := by
        rw [LinearMap.comp_assoc]

theorem gradingCoaction_componentProj (t : H) (g : Multiplicative A) :
    gradingCoaction A π ((gradingComponents A π t) g)
      = MonoidAlgebra.single g (1 : R) ⊗ₜ[R] ((gradingComponents A π t) g) := by
  classical
  by_cases hg : g ∈ (gradingComponents A π t).support
  case neg =>
    have hz : (gradingComponents A π t) g = 0 := by
      rwa [Finsupp.mem_support_iff, not_not] at hg
    rw [hz, map_zero, TensorProduct.tmul_zero]
  case pos =>

    have hco := DFunLike.congr_fun (gradingCoaction_coassoc A π) t
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at hco
    rw [gradingCoaction_eq_sum_components A π t, Finsupp.sum] at hco
    rw [map_sum, map_sum, map_sum] at hco

    have hL : ∀ g' ∈ (gradingComponents A π t).support,
        (LinearMap.lTensor (MonoidAlgebra R (Multiplicative A))
            (gradingCoaction A π))
          ((MonoidAlgebra.single g' (1 : R)
              : MonoidAlgebra R (Multiplicative A))
            ⊗ₜ[R] (gradingComponents A π t) g')
        = (MonoidAlgebra.single g' (1 : R)
            : MonoidAlgebra R (Multiplicative A))
            ⊗ₜ[R] gradingCoaction A π ((gradingComponents A π t) g') :=
      fun g' _ => LinearMap.lTensor_tmul _ _ _ _
    have hR : ∀ g' ∈ (gradingComponents A π t).support,
        (TensorProduct.assoc R (MonoidAlgebra R (Multiplicative A))
            (MonoidAlgebra R (Multiplicative A)) H)
          ((LinearMap.rTensor H (Coalgebra.comul (R := R)))
            ((MonoidAlgebra.single g' (1 : R)
                : MonoidAlgebra R (Multiplicative A))
              ⊗ₜ[R] (gradingComponents A π t) g'))
        = (MonoidAlgebra.single g' (1 : R)
            : MonoidAlgebra R (Multiplicative A))
            ⊗ₜ[R] ((MonoidAlgebra.single g' (1 : R)
                : MonoidAlgebra R (Multiplicative A))
              ⊗ₜ[R] (gradingComponents A π t) g') := by
      intro g' _
      rw [LinearMap.rTensor_tmul, comul_monoidAlgebra_single_one A]
      exact TensorProduct.assoc_tmul _ _ _
    rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR] at hco

    have hterm : ∀ (g' : Multiplicative A)
        (x : MonoidAlgebra R (Multiplicative A) ⊗[R] H),
        (maScalarLeft A (MonoidAlgebra R (Multiplicative A) ⊗[R] H))
          ((MonoidAlgebra.single g' (1 : R)
              : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] x) g
        = if g' = g then x else 0 := by
      intro g' x
      rw [maScalarLeft_single_tmul, one_smul, Finsupp.single_apply]

    have key : ∀ (s : Finset (Multiplicative A))
        (f : Multiplicative A →
          MonoidAlgebra R (Multiplicative A) ⊗[R] H),
        (maScalarLeft A (MonoidAlgebra R (Multiplicative A) ⊗[R] H))
          (∑ x ∈ s, (MonoidAlgebra.single x (1 : R)
              : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] f x) g
          = ∑ x ∈ s, if x = g then f x else 0 := by
      intro s f
      induction s using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        have hz : (maScalarLeft A (MonoidAlgebra R (Multiplicative A) ⊗[R] H))
            (0 : MonoidAlgebra R (Multiplicative A) ⊗[R]
              (MonoidAlgebra R (Multiplicative A) ⊗[R] H)) = 0 := map_zero _
        exact (DFunLike.congr_fun hz g).trans Finsupp.zero_apply
      | insert a s' ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        have hadd := map_add (maScalarLeft A (MonoidAlgebra R (Multiplicative A) ⊗[R] H))
          ((MonoidAlgebra.single a (1 : R)
              : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] f a)
          (∑ x ∈ s', (MonoidAlgebra.single x (1 : R)
              : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] f x)
        refine (DFunLike.congr_fun hadd g).trans ?_
        rw [Finsupp.add_apply]
        exact congrArg₂ (· + ·) (hterm a (f a)) ih

    have h1 : (maScalarLeft A (MonoidAlgebra R (Multiplicative A) ⊗[R] H))
        (∑ x ∈ ((gradingComponents A π) t).support,
          (MonoidAlgebra.single x (1 : R)
              : MonoidAlgebra R (Multiplicative A))
            ⊗ₜ[R] gradingCoaction A π ((gradingComponents A π t) x)) g
        = gradingCoaction A π ((gradingComponents A π t) g) := by
      rw [key ((gradingComponents A π) t).support
        (fun x => gradingCoaction A π ((gradingComponents A π t) x))]
      rw [Finset.sum_ite_eq' ((gradingComponents A π) t).support g
        (fun x => gradingCoaction A π ((gradingComponents A π t) x))]
      rw [if_pos hg]
    have h2 : (maScalarLeft A (MonoidAlgebra R (Multiplicative A) ⊗[R] H))
        (∑ x ∈ ((gradingComponents A π) t).support,
          (MonoidAlgebra.single x (1 : R)
              : MonoidAlgebra R (Multiplicative A))
            ⊗ₜ[R] ((MonoidAlgebra.single x (1 : R)
                : MonoidAlgebra R (Multiplicative A))
              ⊗ₜ[R] (gradingComponents A π t) x)) g
        = (MonoidAlgebra.single g (1 : R)
            : MonoidAlgebra R (Multiplicative A))
            ⊗ₜ[R] (gradingComponents A π t) g := by
      rw [key ((gradingComponents A π) t).support
        (fun x => (MonoidAlgebra.single x (1 : R)
            : MonoidAlgebra R (Multiplicative A))
          ⊗ₜ[R] (gradingComponents A π t) x)]
      rw [Finset.sum_ite_eq' ((gradingComponents A π) t).support g
        (fun x => (MonoidAlgebra.single x (1 : R)
            : MonoidAlgebra R (Multiplicative A))
          ⊗ₜ[R] (gradingComponents A π t) x)]
      rw [if_pos hg]
    exact h1.symm.trans ((congrArg (fun z =>
      (maScalarLeft A (MonoidAlgebra R (Multiplicative A) ⊗[R] H)) z g) hco).trans h2)

theorem componentProj_mem_gradedPiece (t : H) (j : A) :
    componentProj A π j t ∈ gradedPiece A π j := by
  have h := gradingCoaction_componentProj A π t (Multiplicative.ofAdd j)
  show gradingComponents A π (componentProj A π j t)
    = Finsupp.single (Multiplicative.ofAdd j) (componentProj A π j t)
  have hc : componentProj A π j t
      = (gradingComponents A π t) (Multiplicative.ofAdd j) := rfl
  rw [gradingComponents_eq_maScalarLeft, hc, h, maScalarLeft_single_tmul, one_smul]

theorem componentProj_eq_of_mem {j : A} {t : H} (ht : t ∈ gradedPiece A π j) :
    componentProj A π j t = t := by
  have ht' : gradingComponents A π t = Finsupp.single (Multiplicative.ofAdd j) t := ht
  show (gradingComponents A π t) (Multiplicative.ofAdd j) = t
  rw [ht', Finsupp.single_eq_same]

theorem componentProj_eq_zero_of_mem {j j' : A} (hne : j' ≠ j) {t : H}
    (ht : t ∈ gradedPiece A π j) : componentProj A π j' t = 0 := by
  have ht' : gradingComponents A π t = Finsupp.single (Multiplicative.ofAdd j) t := ht
  show (gradingComponents A π t) (Multiplicative.ofAdd j') = 0
  rw [ht']
  exact Finsupp.single_eq_of_ne (fun h => hne (Multiplicative.ofAdd.injective h.symm).symm)

theorem coalgHom_apply_mem_single_line {j : A} {t : H}
    (ht : t ∈ gradedPiece A π j) :
    π t = MonoidAlgebra.single (Multiplicative.ofAdd j)
      (Coalgebra.counit (R := R) (π t)) := by

  have hmem := gradingCoaction_eq_of_mem A π ht

  have hl : (LinearMap.lTensor (MonoidAlgebra R (Multiplicative A))
        π.toLinearMap) (gradingCoaction A π t)
      = (Coalgebra.comul (R := R)) (π t) := by
    rw [gradingCoaction_apply]
    have : (LinearMap.lTensor (MonoidAlgebra R (Multiplicative A)) π.toLinearMap)
          ((LinearMap.rTensor H π.toLinearMap) ((Coalgebra.comul (R := R)) t))
        = (TensorProduct.map π.toLinearMap π.toLinearMap)
            ((Coalgebra.comul (R := R)) t) := by
      induction (Coalgebra.comul (R := R) t) with
      | zero => simp only [map_zero]
      | tmul a b => simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
          TensorProduct.map_tmul]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [this]
    exact DFunLike.congr_fun (CoalgHomClass.map_comp_comul π) t
  rw [hmem] at hl

  have hc : (Coalgebra.comul (R := R)) (π t)
      = (MonoidAlgebra.single (Multiplicative.ofAdd j) (1 : R)
          : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] π t :=
    hl.symm.trans (LinearMap.lTensor_tmul
      (MonoidAlgebra R (Multiplicative A)) π.toLinearMap _ t)

  have hcounit := DFunLike.congr_fun
    (Coalgebra.lTensor_counit_comp_comul (R := R)
      (A := MonoidAlgebra R (Multiplicative A))) (π t)
  simp only [LinearMap.coe_comp, Function.comp_apply] at hcounit
  rw [hc] at hcounit
  have hexp : (LinearMap.lTensor (MonoidAlgebra R (Multiplicative A))
        (Coalgebra.counit (R := R)))
      ((MonoidAlgebra.single (Multiplicative.ofAdd j) (1 : R)
          : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] π t)
      = (MonoidAlgebra.single (Multiplicative.ofAdd j) (1 : R)
          : MonoidAlgebra R (Multiplicative A))
          ⊗ₜ[R] (Coalgebra.counit (R := R) (π t)) :=
    LinearMap.lTensor_tmul _ _ _ _
  rw [hexp] at hcounit

  have hrid := congrArg
    (TensorProduct.rid R (MonoidAlgebra R (Multiplicative A))) hcounit
  rw [TensorProduct.rid_tmul] at hrid
  have hflip : (TensorProduct.rid R (MonoidAlgebra R (Multiplicative A)))
      ((TensorProduct.mk R (MonoidAlgebra R (Multiplicative A)) R).flip 1 (π t))
      = π t := by
    rw [show (TensorProduct.mk R (MonoidAlgebra R (Multiplicative A)) R).flip 1 (π t)
        = π t ⊗ₜ[R] (1 : R) from rfl]
    rw [TensorProduct.rid_tmul, one_smul]
  rw [hflip] at hrid

  have hsmul : (Coalgebra.counit (R := R) (π t))
        • (MonoidAlgebra.single (Multiplicative.ofAdd j) (1 : R)
            : MonoidAlgebra R (Multiplicative A))
      = MonoidAlgebra.single (Multiplicative.ofAdd j)
          (Coalgebra.counit (R := R) (π t)) := by
    rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  exact hrid.symm.trans hsmul

def translationByPoint (ψ : H →ₐ[R] R) : H →ₗ[R] H :=
  (TensorProduct.rid R H).toLinearMap
    ∘ₗ LinearMap.lTensor H ψ.toLinearMap
    ∘ₗ (Coalgebra.comul (R := R) (A := H))

theorem translationByPoint_apply (ψ : H →ₐ[R] R) (t : H) :
    translationByPoint (R := R) ψ t
      = (TensorProduct.rid R H)
          ((LinearMap.lTensor H ψ.toLinearMap)
            ((Coalgebra.comul (R := R)) t)) := rfl

theorem translationByPoint_counit (t : H) :
    translationByPoint (R := R) (Bialgebra.counitAlgHom R H) t = t := by
  have hlaw := DFunLike.congr_fun
    (Coalgebra.lTensor_counit_comp_comul (R := R) (A := H)) t
  simp only [LinearMap.coe_comp, Function.comp_apply] at hlaw
  have h1 : translationByPoint (R := R) (Bialgebra.counitAlgHom R H) t
      = (TensorProduct.rid R H)
          ((LinearMap.lTensor H (Coalgebra.counit (R := R)))
            ((Coalgebra.comul (R := R)) t)) := rfl
  rw [h1, hlaw]
  have h2 : (TensorProduct.mk R H R).flip 1 t = t ⊗ₜ[R] (1 : R) := rfl
  rw [h2, TensorProduct.rid_tmul, one_smul]

omit [DecidableEq A] in

theorem gradingCoaction_translationByPoint (ψ : H →ₐ[R] R) :
    gradingCoaction A π ∘ₗ translationByPoint (R := R) ψ
      = LinearMap.lTensor (MonoidAlgebra R (Multiplicative A))
          (translationByPoint (R := R) ψ) ∘ₗ gradingCoaction A π := by

  have hA : (Coalgebra.comul (R := R) (A := H)) ∘ₗ translationByPoint (R := R) ψ
      = LinearMap.lTensor H (translationByPoint (R := R) ψ)
          ∘ₗ (Coalgebra.comul (R := R)) := by

    have hA1 : (Coalgebra.comul (R := R) (A := H)) ∘ₗ (TensorProduct.rid R H).toLinearMap
        = (TensorProduct.rid R (H ⊗[R] H)).toLinearMap
            ∘ₗ LinearMap.rTensor R (Coalgebra.comul (R := R)) := by
      ext h
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
        LinearMap.coe_restrictScalars]
      rw [TensorProduct.rid_tmul, one_smul, LinearMap.rTensor_tmul,
        TensorProduct.rid_tmul, one_smul]

    have hA2 : LinearMap.rTensor R (Coalgebra.comul (R := R) (A := H))
          ∘ₗ LinearMap.lTensor H ψ.toLinearMap
        = LinearMap.lTensor (H ⊗[R] H) ψ.toLinearMap
            ∘ₗ LinearMap.rTensor H (Coalgebra.comul (R := R)) :=
      (LinearMap.rTensor_comp_lTensor _ _ _).trans
        (LinearMap.lTensor_comp_rTensor _ _ _).symm

    have hA3 : LinearMap.rTensor H (Coalgebra.comul (R := R) (A := H))
          ∘ₗ (Coalgebra.comul (R := R))
        = (TensorProduct.assoc R H H H).symm.toLinearMap
            ∘ₗ LinearMap.lTensor H (Coalgebra.comul (R := R))
            ∘ₗ (Coalgebra.comul (R := R)) := by
      have h := Coalgebra.coassoc (R := R) (A := H)

      have h' := congrArg (fun F =>
        (TensorProduct.assoc R H H H).symm.toLinearMap ∘ₗ F) h
      beta_reduce at h'
      rw [← h']
      ext t
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
      rw [LinearEquiv.symm_apply_apply]

    have hA4pre : (TensorProduct.rid R (H ⊗[R] H)).toLinearMap
          ∘ₗ LinearMap.lTensor (H ⊗[R] H) ψ.toLinearMap
        = (LinearMap.lTensor H ((TensorProduct.rid R H).toLinearMap
            ∘ₗ LinearMap.lTensor H ψ.toLinearMap))
            ∘ₗ (TensorProduct.assoc R H H H).toLinearMap := by
      apply TensorProduct.ext_threefold
      intro x y z
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
      rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
      rw [TensorProduct.assoc_tmul]
      rw [LinearMap.lTensor_tmul]
      rw [LinearMap.comp_apply]
      rw [LinearMap.lTensor_tmul]
      rw [LinearEquiv.coe_coe]
      rw [TensorProduct.rid_tmul]
      rw [TensorProduct.tmul_smul]

    have hidA : (TensorProduct.assoc R H H H).toLinearMap
          ∘ₗ (TensorProduct.assoc R H H H).symm.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro t
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearMap.id_apply]
      exact (TensorProduct.assoc R H H H).apply_symm_apply t

    have hA4 : (TensorProduct.rid R (H ⊗[R] H)).toLinearMap
          ∘ₗ LinearMap.lTensor (H ⊗[R] H) ψ.toLinearMap
          ∘ₗ (TensorProduct.assoc R H H H).symm.toLinearMap
        = LinearMap.lTensor H ((TensorProduct.rid R H).toLinearMap
            ∘ₗ LinearMap.lTensor H ψ.toLinearMap) := by
      rw [← LinearMap.comp_assoc, hA4pre, LinearMap.comp_assoc, hidA, LinearMap.comp_id]

    show (Coalgebra.comul (R := R))
        ∘ₗ ((TensorProduct.rid R H).toLinearMap
          ∘ₗ LinearMap.lTensor H ψ.toLinearMap
          ∘ₗ (Coalgebra.comul (R := R)))
      = LinearMap.lTensor H (translationByPoint (R := R) ψ)
          ∘ₗ (Coalgebra.comul (R := R))
    calc (Coalgebra.comul (R := R))
          ∘ₗ ((TensorProduct.rid R H).toLinearMap
            ∘ₗ LinearMap.lTensor H ψ.toLinearMap
            ∘ₗ (Coalgebra.comul (R := R)))
        = ((Coalgebra.comul (R := R))
            ∘ₗ (TensorProduct.rid R H).toLinearMap)
            ∘ₗ LinearMap.lTensor H ψ.toLinearMap
            ∘ₗ (Coalgebra.comul (R := R)) := by
          rw [LinearMap.comp_assoc]
      _ = ((TensorProduct.rid R (H ⊗[R] H)).toLinearMap
            ∘ₗ LinearMap.rTensor R (Coalgebra.comul (R := R)))
            ∘ₗ LinearMap.lTensor H ψ.toLinearMap
            ∘ₗ (Coalgebra.comul (R := R)) := by rw [hA1]
      _ = (TensorProduct.rid R (H ⊗[R] H)).toLinearMap
            ∘ₗ (LinearMap.rTensor R (Coalgebra.comul (R := R))
              ∘ₗ LinearMap.lTensor H ψ.toLinearMap)
            ∘ₗ (Coalgebra.comul (R := R)) := by
          rw [LinearMap.comp_assoc, LinearMap.comp_assoc]
      _ = (TensorProduct.rid R (H ⊗[R] H)).toLinearMap
            ∘ₗ (LinearMap.lTensor (H ⊗[R] H) ψ.toLinearMap
              ∘ₗ LinearMap.rTensor H (Coalgebra.comul (R := R)))
            ∘ₗ (Coalgebra.comul (R := R)) := by rw [hA2]
      _ = (TensorProduct.rid R (H ⊗[R] H)).toLinearMap
            ∘ₗ LinearMap.lTensor (H ⊗[R] H) ψ.toLinearMap
            ∘ₗ (LinearMap.rTensor H (Coalgebra.comul (R := R))
              ∘ₗ (Coalgebra.comul (R := R))) := by
          rw [LinearMap.comp_assoc]
      _ = (TensorProduct.rid R (H ⊗[R] H)).toLinearMap
            ∘ₗ LinearMap.lTensor (H ⊗[R] H) ψ.toLinearMap
            ∘ₗ (TensorProduct.assoc R H H H).symm.toLinearMap
            ∘ₗ LinearMap.lTensor H (Coalgebra.comul (R := R))
            ∘ₗ (Coalgebra.comul (R := R)) := by rw [hA3]
      _ = ((TensorProduct.rid R (H ⊗[R] H)).toLinearMap
            ∘ₗ LinearMap.lTensor (H ⊗[R] H) ψ.toLinearMap
            ∘ₗ (TensorProduct.assoc R H H H).symm.toLinearMap)
            ∘ₗ LinearMap.lTensor H (Coalgebra.comul (R := R))
            ∘ₗ (Coalgebra.comul (R := R)) := by
          rw [LinearMap.comp_assoc, LinearMap.comp_assoc]
      _ = LinearMap.lTensor H ((TensorProduct.rid R H).toLinearMap
            ∘ₗ LinearMap.lTensor H ψ.toLinearMap)
            ∘ₗ LinearMap.lTensor H (Coalgebra.comul (R := R))
            ∘ₗ (Coalgebra.comul (R := R)) := by rw [hA4]
      _ = LinearMap.lTensor H (translationByPoint (R := R) ψ)
            ∘ₗ (Coalgebra.comul (R := R)) := by
          rw [← LinearMap.comp_assoc, ← LinearMap.lTensor_comp]
          rfl

  have hB : LinearMap.rTensor H π.toLinearMap
        ∘ₗ LinearMap.lTensor H (translationByPoint (R := R) ψ)
      = LinearMap.lTensor (MonoidAlgebra R (Multiplicative A))
          (translationByPoint (R := R) ψ)
        ∘ₗ LinearMap.rTensor H π.toLinearMap :=
    (LinearMap.rTensor_comp_lTensor _ _ _).trans
      (LinearMap.lTensor_comp_rTensor _ _ _).symm

  show (LinearMap.rTensor H π.toLinearMap ∘ₗ (Coalgebra.comul (R := R)))
      ∘ₗ translationByPoint (R := R) ψ
    = LinearMap.lTensor (MonoidAlgebra R (Multiplicative A))
        (translationByPoint (R := R) ψ)
      ∘ₗ LinearMap.rTensor H π.toLinearMap ∘ₗ (Coalgebra.comul (R := R))
  calc (LinearMap.rTensor H π.toLinearMap ∘ₗ (Coalgebra.comul (R := R)))
        ∘ₗ translationByPoint (R := R) ψ
      = LinearMap.rTensor H π.toLinearMap
          ∘ₗ ((Coalgebra.comul (R := R)) ∘ₗ translationByPoint (R := R) ψ) := by
        rw [LinearMap.comp_assoc]
    _ = LinearMap.rTensor H π.toLinearMap
          ∘ₗ LinearMap.lTensor H (translationByPoint (R := R) ψ)
          ∘ₗ (Coalgebra.comul (R := R)) := by rw [hA]
    _ = (LinearMap.rTensor H π.toLinearMap
          ∘ₗ LinearMap.lTensor H (translationByPoint (R := R) ψ))
          ∘ₗ (Coalgebra.comul (R := R)) := by rw [LinearMap.comp_assoc]
    _ = (LinearMap.lTensor (MonoidAlgebra R (Multiplicative A))
          (translationByPoint (R := R) ψ)
          ∘ₗ LinearMap.rTensor H π.toLinearMap)
          ∘ₗ (Coalgebra.comul (R := R)) := by rw [hB]
    _ = LinearMap.lTensor (MonoidAlgebra R (Multiplicative A))
          (translationByPoint (R := R) ψ)
          ∘ₗ LinearMap.rTensor H π.toLinearMap ∘ₗ (Coalgebra.comul (R := R)) := by
        rw [LinearMap.comp_assoc]

theorem mem_gradedPiece_of_gradingCoaction {j : A} {t : H}
    (h : gradingCoaction A π t
      = (MonoidAlgebra.single (Multiplicative.ofAdd j) (1 : R)
          : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] t) :
    t ∈ gradedPiece A π j := by
  show gradingComponents A π t
    = Finsupp.single (Multiplicative.ofAdd j) t
  rw [gradingComponents_eq_maScalarLeft, h, maScalarLeft_single_tmul, one_smul]

theorem translationByPoint_mem_gradedPiece (ψ : H →ₐ[R] R) {j : A} {t : H}
    (ht : t ∈ gradedPiece A π j) :
    translationByPoint (R := R) ψ t ∈ gradedPiece A π j := by
  have hmem : gradingCoaction A π t
      = (MonoidAlgebra.single (Multiplicative.ofAdd j) (1 : R)
          : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] t :=
    gradingCoaction_eq_of_mem A π ht
  have hcomm := DFunLike.congr_fun (gradingCoaction_translationByPoint A π ψ) t
  simp only [LinearMap.coe_comp, Function.comp_apply] at hcomm
  rw [hmem] at hcomm
  have hpush : (LinearMap.lTensor (MonoidAlgebra R (Multiplicative A))
        (translationByPoint (R := R) ψ))
      ((MonoidAlgebra.single (Multiplicative.ofAdd j) (1 : R)
          : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] t)
      = (MonoidAlgebra.single (Multiplicative.ofAdd j) (1 : R)
          : MonoidAlgebra R (Multiplicative A))
          ⊗ₜ[R] translationByPoint (R := R) ψ t :=
    LinearMap.lTensor_tmul _ _ _ _
  rw [hpush] at hcomm
  exact mem_gradedPiece_of_gradingCoaction A π hcomm

def translationOfIndexPoint (ψ : MonoidAlgebra R (Multiplicative A) →ₐ[R] R) :
    H →ₗ[R] H :=
  (TensorProduct.lid R H).toLinearMap
    ∘ₗ LinearMap.rTensor H ψ.toLinearMap
    ∘ₗ gradingCoaction A π

theorem translationOfIndexPoint_eq_smul_of_mem
    (ψ : MonoidAlgebra R (Multiplicative A) →ₐ[R] R) {j : A} {t : H}
    (ht : t ∈ gradedPiece A π j) :
    translationOfIndexPoint A π ψ t
      = ψ (MonoidAlgebra.single (Multiplicative.ofAdd j) (1 : R)) • t := by
  show (TensorProduct.lid R H).toLinearMap
      (LinearMap.rTensor H ψ.toLinearMap (gradingCoaction A π t))
    = ψ (MonoidAlgebra.single (Multiplicative.ofAdd j) (1 : R)) • t
  rw [gradingCoaction_eq_of_mem A π ht]
  exact (congrArg (⇑(TensorProduct.lid R H))
    (LinearMap.rTensor_tmul _ _ _ _)).trans (TensorProduct.lid_tmul t _)

theorem eq_zero_of_mem_gradedPiece_of_mem_gradedPiece
    (ψ : MonoidAlgebra R (Multiplicative A) →ₐ[R] R) {i j : A} {t : H}
    (hi : t ∈ gradedPiece A π i) (hj : t ∈ gradedPiece A π j)
    (hsep : IsUnit (ψ (MonoidAlgebra.single (Multiplicative.ofAdd i) (1 : R))
      - ψ (MonoidAlgebra.single (Multiplicative.ofAdd j) (1 : R)))) :
    t = 0 := by
  have h1 := translationOfIndexPoint_eq_smul_of_mem A π ψ hi
  have h2 := translationOfIndexPoint_eq_smul_of_mem A π ψ hj
  have hdiff : (ψ (MonoidAlgebra.single (Multiplicative.ofAdd i) (1 : R))
      - ψ (MonoidAlgebra.single (Multiplicative.ofAdd j) (1 : R))) • t = 0 := by
    rw [sub_smul, h1.symm.trans h2, sub_self]
  obtain ⟨u, hu⟩ := hsep
  have hz : ((u⁻¹ : Rˣ) : R) • ((u : R) • t) = 0 := by rw [hu, hdiff, smul_zero]
  rwa [smul_smul, Units.inv_mul, one_smul] at hz

theorem eq_zero_of_sum_eq_zero_of_mem_gradedPiece (s : Finset A) (f : A → H)
    (hf : ∀ j ∈ s, f j ∈ gradedPiece A π j) (hsum : ∑ j ∈ s, f j = 0)
    {j : A} (hj : j ∈ s) : f j = 0 := by
  have hproj := congrArg (componentProj A π j) hsum
  rw [map_sum, map_zero] at hproj
  rw [Finset.sum_eq_single j
    (fun i hi hne => componentProj_eq_zero_of_mem A π (Ne.symm hne) (hf i hi))
    (fun h => absurd hj h)] at hproj
  rw [componentProj_eq_of_mem A π (hf j hj)] at hproj
  exact hproj

omit [DecidableEq A] in

theorem gradingCoaction_mul (x y : H) :
    gradingCoaction A π (x * y) = gradingCoaction A π x * gradingCoaction A π y := by
  have hkey : LinearMap.rTensor H π.toLinearMap
      = (Algebra.TensorProduct.map π.toAlgHom (AlgHom.id R H)).toLinearMap := rfl
  unfold gradingCoaction
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [Bialgebra.comul_mul, hkey]
  exact map_mul (Algebra.TensorProduct.map π.toAlgHom (AlgHom.id R H)) _ _

omit [DecidableEq A] in
theorem gradingCoaction_one :
    gradingCoaction A π (1 : H)
      = (1 : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] (1 : H) := by
  unfold gradingCoaction
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [Bialgebra.comul_one, Algebra.TensorProduct.one_def, LinearMap.rTensor_tmul]
  rw [show π.toLinearMap (1 : H) = 1 from map_one π]

theorem one_mem_gradedPiece_zero : (1 : H) ∈ gradedPiece A π 0 := by
  show gradingComponents A π 1 = Finsupp.single (Multiplicative.ofAdd (0 : A)) 1
  rw [gradingComponents_eq_maScalarLeft, gradingCoaction_one, MonoidAlgebra.one_def,
    maScalarLeft_single_tmul, one_smul, ofAdd_zero]

theorem gradingCoaction_mul_of_mem {i j : A} {x y : H}
    (hx : x ∈ gradedPiece A π i) (hy : y ∈ gradedPiece A π j) :
    gradingCoaction A π (x * y)
      = MonoidAlgebra.single (Multiplicative.ofAdd (i + j)) (1 : R) ⊗ₜ[R] (x * y) := by
  rw [gradingCoaction_mul A π x y, gradingCoaction_eq_of_mem A π hx,
    gradingCoaction_eq_of_mem A π hy]
  refine (Algebra.TensorProduct.tmul_mul_tmul _ _ _ _).trans ?_
  congr 1
  refine (MonoidAlgebra.single_mul_single _ _ _ _).trans ?_
  rw [one_mul, ← ofAdd_add]

theorem gradedPiece_mul_mem (i j : A) (x y : H)
    (hx : x ∈ gradedPiece A π i) (hy : y ∈ gradedPiece A π j) :
    x * y ∈ gradedPiece A π (i + j) := by
  show gradingComponents A π (x * y)
    = Finsupp.single (Multiplicative.ofAdd (i + j)) (x * y)
  rw [gradingComponents_eq_maScalarLeft, gradingCoaction_mul_of_mem A π hx hy,
    maScalarLeft_single_tmul, one_smul]

theorem sum_finsuppScalarLeft_eq
    (z : MonoidAlgebra R (Multiplicative A) ⊗[R] H) :
    ((maScalarLeft A H) z).sum (fun _ x => x)
      = (TensorProduct.lid R H)
          ((LinearMap.rTensor H
            (Coalgebra.counit (R := R) (A := MonoidAlgebra R (Multiplicative A)))) z) := by
  induction z with
  | zero =>
    rw [show (maScalarLeft A H)
        (0 : MonoidAlgebra R (Multiplicative A) ⊗[R] H) = 0 from map_zero _,
      Finsupp.sum_zero_index, map_zero, map_zero]
  | tmul p n =>
    have hcount : ∀ p' : MonoidAlgebra R (Multiplicative A),
        (p'.coeff.sum fun _ m => m • n)
          = (Coalgebra.counit (R := R)
              (A := MonoidAlgebra R (Multiplicative A)) p') • n := by
      intro p'
      induction p' using MonoidAlgebra.induction_linear with
      | zero =>
        rw [MonoidAlgebra.coeff_zero, Finsupp.sum_zero_index]
        have hz : (Coalgebra.counit (R := R)
            (A := MonoidAlgebra R (Multiplicative A)))
              (0 : MonoidAlgebra R (Multiplicative A)) = 0 := map_zero _
        erw [hz, zero_smul]
      | add f g hf hg =>
        rw [MonoidAlgebra.coeff_add,
          Finsupp.sum_add_index' (fun _ => zero_smul R n) (fun _ b c => add_smul b c n), hf, hg]
        have ha : (Coalgebra.counit (R := R)
            (A := MonoidAlgebra R (Multiplicative A))) (f + g)
            = Coalgebra.counit (R := R)
                (A := MonoidAlgebra R (Multiplicative A)) f
              + Coalgebra.counit (R := R)
                  (A := MonoidAlgebra R (Multiplicative A)) g := map_add _ f g
        erw [ha, add_smul]
      | single g r =>
        rw [MonoidAlgebra.coeff_single, Finsupp.sum_single_index (zero_smul R n)]
        congr 1
        erw [MonoidAlgebra.counit_single]
        rfl
    rw [maScalarLeft_tmul]
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
    rw [Finsupp.sum_sum_index (fun _ => rfl) (fun _ _ _ => rfl)]
    have hinner : (p.coeff.sum fun i m => ((Finsupp.single i (m • n)).sum fun _ x => x))
        = p.coeff.sum fun _ m => m • n :=
      Finsupp.sum_congr fun i _ => Finsupp.sum_single_index rfl
    rw [hinner]
    exact hcount p
  | add a b ha hb =>
    have hsplit : (maScalarLeft A H) (a + b)
        = (maScalarLeft A H) a
          + (maScalarLeft A H) b :=
      map_add _ a b
    rw [hsplit, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), ha, hb,
      map_add, map_add]

theorem sum_componentProj_eq (t : H) :
    (gradingComponents A π t).sum (fun _ x => x) = t := by
  rw [gradingComponents_eq_maScalarLeft, sum_finsuppScalarLeft_eq]
  have hcomp : LinearMap.rTensor H
      (Coalgebra.counit (R := R) (A := MonoidAlgebra R (Multiplicative A))) ∘ₗ
        LinearMap.rTensor H π.toLinearMap
      = LinearMap.rTensor H (Coalgebra.counit (R := R) (A := H)) := by
    rw [← LinearMap.rTensor_comp]
    congr 1
    exact CoalgHomClass.counit_comp π
  have h3 : (LinearMap.rTensor H (Coalgebra.counit (R := R) (A := H)))
      ((Coalgebra.comul (R := R)) t) = (1 : R) ⊗ₜ[R] t := by
    have hlaw := Coalgebra.rTensor_counit_comp_comul (R := R) (A := H)
    have h' := congrArg (fun (F : H →ₗ[R] R ⊗[R] H) => F t) hlaw
    simp only [LinearMap.coe_comp, Function.comp_apply] at h'
    rw [h']
    rfl
  have h2 : (LinearMap.rTensor H
      (Coalgebra.counit (R := R) (A := MonoidAlgebra R (Multiplicative A))))
        (gradingCoaction A π t) = (1 : R) ⊗ₜ[R] t := by
    rw [gradingCoaction_apply]
    calc (LinearMap.rTensor H
          (Coalgebra.counit (R := R) (A := MonoidAlgebra R (Multiplicative A))))
            ((LinearMap.rTensor H π.toLinearMap) ((Coalgebra.comul (R := R)) t))
        = ((LinearMap.rTensor H
            (Coalgebra.counit (R := R) (A := MonoidAlgebra R (Multiplicative A)))) ∘ₗ
              (LinearMap.rTensor H π.toLinearMap)) ((Coalgebra.comul (R := R)) t) := rfl
      _ = (LinearMap.rTensor H (Coalgebra.counit (R := R) (A := H)))
            ((Coalgebra.comul (R := R)) t) := by rw [hcomp]
      _ = (1 : R) ⊗ₜ[R] t := h3
  rw [h2, TensorProduct.lid_tmul, one_smul]

theorem finsuppScalarLeft_mul_one_tmul (z : MonoidAlgebra R (Multiplicative A) ⊗[R] H)
    (e : H) (g : Multiplicative A) :
    (maScalarLeft A H)
        (z * ((1 : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] e)) g
      = (maScalarLeft A H) z g * e := by
  induction z with
  | zero =>
    have h0 : (maScalarLeft A H)
        (0 : MonoidAlgebra R (Multiplicative A) ⊗[R] H) = 0 := map_zero _
    rw [zero_mul, h0]
    exact (zero_mul e).symm
  | tmul f t =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [maScalarLeft_tmul, maScalarLeft_tmul]
    rw [Finsupp.sum_apply, Finsupp.sum_apply, Finsupp.sum, Finsupp.sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finsupp.single_apply, Finsupp.single_apply]
    by_cases hh : h = g
    · simp only [hh, if_true]
      rw [smul_mul_assoc]
    · simp only [hh, if_false, zero_mul]
  | add z₁ z₂ h₁ h₂ =>
    rw [add_mul]
    have hL : (maScalarLeft A H)
        (z₁ * ((1 : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] e)
          + z₂ * ((1 : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] e))
        = (maScalarLeft A H)
            (z₁ * ((1 : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] e))
          + (maScalarLeft A H)
              (z₂ * ((1 : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] e)) := map_add _ _ _
    have hR : (maScalarLeft A H) (z₁ + z₂)
        = (maScalarLeft A H) z₁
          + (maScalarLeft A H) z₂ := map_add _ _ _
    rw [hL, Finsupp.add_apply, h₁, h₂, hR, Finsupp.add_apply, add_mul]

theorem gradingComponents_mul_of_mem_zero {e : H} (he : e ∈ gradedPiece A π 0)
    (x : H) (g : Multiplicative A) :
    gradingComponents A π (x * e) g = gradingComponents A π x g * e := by
  have hρe : gradingCoaction A π e
      = ((1 : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] e) := by
    rw [gradingCoaction_eq_of_mem A π he]
    exact congrArg (fun m => m ⊗ₜ[R] e) MonoidAlgebra.one_def.symm
  rw [gradingComponents_eq_maScalarLeft, gradingCoaction_mul A π x e, hρe,
    finsuppScalarLeft_mul_one_tmul, gradingComponents_eq_maScalarLeft]

theorem eq_zero_of_mul_self_mul_self_of_pow_le {S B : Type} [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] [CommRing B] [Algebra S B] [Module.Finite S B]
    {q : ℕ} (hqS : ¬ IsUnit ((q : ℕ) : S)) {J : Ideal B} {n : ℕ}
    (hJ : J ^ n ≤ Ideal.span {((q : ℕ) : B)}) {d : B} (hd3 : d * (d * d) = d) (hdJ : d ∈ J) :
    d = 0 := by
  have hk : ∀ k : ℕ, d = d * (d * d) ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, mul_one]
    | succ k ih =>
      calc d = d * (d * d) ^ k := ih
        _ = (d * (d * d)) * (d * d) ^ k := by rw [hd3]
        _ = d * (d * d) ^ (k + 1) := by ring
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hJ (Ideal.pow_mem_pow hdJ n))
  have hdq : d = ((q : ℕ) : S) • (d ^ (n + 1) * c) := by
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
    calc d = d * (d * d) ^ n := hk n
      _ = d ^ (n + 1) * d ^ n := by ring
      _ = d ^ (n + 1) * (c * ((q : ℕ) : B)) := by rw [hc]
      _ = ((q : ℕ) : B) * (d ^ (n + 1) * c) := by ring
  have hNfg : ((Ideal.span {d}).restrictScalars S).FG := IsNoetherian.noetherian _
  have hle : (Ideal.span {d}).restrictScalars S
      ≤ Ideal.span {((q : ℕ) : S)} • (Ideal.span {d}).restrictScalars S := by
    intro z hz
    have hz' : z ∈ Ideal.span {d} := hz
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hz'
    have hmem : b * (d ^ (n + 1) * c) ∈ (Ideal.span {d}).restrictScalars S := by
      show b * (d ^ (n + 1) * c) ∈ Ideal.span {d}
      exact Ideal.mem_span_singleton'.mpr ⟨b * (d ^ n * c), by ring⟩
    have hbd : b * d = ((q : ℕ) : S) • (b * (d ^ (n + 1) * c)) := by
      conv_lhs => rw [hdq]
      rw [mul_smul_comm]
    rw [hbd]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hmem
  have hjac : Ideal.span {((q : ℕ) : S)} ≤ (⊥ : Ideal S).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_singleton_le_iff_mem]
    exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hqS)
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hNfg hle hjac
  have hdN : d ∈ (Ideal.span {d}).restrictScalars S := Ideal.mem_span_singleton_self d
  rw [hbot] at hdN
  exact (Submodule.mem_bot S).mp hdN

theorem card_nsmul_eq_zero_of_fintype {B : Type} [AddCommGroup B] [Fintype B] (a : B) :
    Fintype.card B • a = 0 := by
  rw [← Nat.card_eq_fintype_card]
  exact card_nsmul_eq_zero'

theorem exists_add_one_pow_prime_pow_eq {T : Type} [CommRing T] {q : ℕ} (hq : q.Prime) (x : T) (k : ℕ) :
    ∃ r : T, (x + 1) ^ (q ^ k) = x ^ (q ^ k) + 1 + (q : T) * r := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨r₁, hr₁⟩ := exists_add_pow_prime_eq hq (x ^ (q ^ k) + 1) ((q : T) * r)
    obtain ⟨r₂, hr₂⟩ := exists_add_pow_prime_eq hq (x ^ (q ^ k)) (1 : T)
    have hqq : ((q : T) * r) ^ q = (q : T) * ((q : T) ^ (q - 1) * r ^ q) := by
      rw [mul_pow, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hq.one_lt.le]
    refine ⟨x ^ (q ^ k) * r₂ + x ^ (q ^ k) * (q : T) * r * r₁ + (q : T) ^ (q - 1) * r ^ q + (q : T) * r * r₁, ?_⟩
    rw [pow_succ, pow_mul, hr, hr₁, hqq, hr₂, one_pow, ← pow_mul]
    ring

omit [DecidableEq A] in

theorem single_sub_one_pow_mem {q : ℕ} (hq : q.Prime) {k : ℕ} (hqA : ∀ a : A, q ^ k • a = 0)
    (g : Multiplicative A) :
    ((MonoidAlgebra.single g (1 : R) : MonoidAlgebra R (Multiplicative A)) - 1) ^ (q ^ k)
      ∈ Ideal.span {((q : ℕ) : MonoidAlgebra R (Multiplicative A))} := by
  have hgq : g ^ (q ^ k) = 1 := by
    have h1 : Multiplicative.ofAdd (q ^ k • Multiplicative.toAdd g) = g ^ (q ^ k) := by
      rw [ofAdd_nsmul, ofAdd_toAdd]
    rw [← h1, hqA, ofAdd_zero]
  have hpow : ((MonoidAlgebra.single g (1 : R) : MonoidAlgebra R (Multiplicative A)) - 1 + 1) ^ (q ^ k)
      = 1 := by
    rw [sub_add_cancel, MonoidAlgebra.single_pow, hgq, one_pow]
    exact MonoidAlgebra.one_def.symm
  obtain ⟨r, hr⟩ := exists_add_one_pow_prime_pow_eq hq
    ((MonoidAlgebra.single g (1 : R) : MonoidAlgebra R (Multiplicative A)) - 1) k
  rw [hpow] at hr
  refine Ideal.mem_span_singleton'.mpr ⟨-r, ?_⟩
  linear_combination hr

def augIdeal : Ideal (MonoidAlgebra R (Multiplicative A) ⊗[R] H) :=
  Ideal.span (Set.range fun g : Multiplicative A =>
    ((MonoidAlgebra.single g (1 : R) : MonoidAlgebra R (Multiplicative A)) - 1) ⊗ₜ[R] (1 : H))

omit [DecidableEq A] in

theorem exists_augIdeal_pow_le [Finite A] {q : ℕ} (hq : q.Prime) {k : ℕ} (hqA : ∀ a : A, q ^ k • a = 0) :
    ∃ n : ℕ, augIdeal (R := R) (H := H) A ^ n
      ≤ Ideal.span {((q : ℕ) : MonoidAlgebra R (Multiplicative A) ⊗[R] H)} := by
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (Submodule.fg_span (Set.finite_range _))
  rw [augIdeal, Ideal.span_le]
  rintro _ ⟨g, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_radical_iff]
  refine ⟨q ^ k, ?_⟩
  show (((MonoidAlgebra.single g (1 : R) : MonoidAlgebra R (Multiplicative A)) - 1)
      ⊗ₜ[R] (1 : H)) ^ (q ^ k) ∈ _
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp (single_sub_one_pow_mem (R := R) A hq hqA g)
  have hqB : (((q : ℕ) : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] (1 : H))
      = ((q : ℕ) : MonoidAlgebra R (Multiplicative A) ⊗[R] H) :=
    map_natCast (Algebra.TensorProduct.includeLeft :
      MonoidAlgebra R (Multiplicative A) →ₐ[R] MonoidAlgebra R (Multiplicative A) ⊗[R] H) q
  rw [Algebra.TensorProduct.tmul_pow, one_pow, ← hz]
  have hsplit : ((z * ((q : ℕ) : MonoidAlgebra R (Multiplicative A))) ⊗ₜ[R] (1 : H))
      = (z ⊗ₜ[R] (1 : H))
        * (((q : ℕ) : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] (1 : H)) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [hsplit, hqB]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem gradingCoaction_sub_one_tmul_mem_augIdeal (e : H) :
    gradingCoaction A π e - (1 : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] e
      ∈ augIdeal (R := R) (H := H) A := by
  have hsume : (1 : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] e
      = ∑ g ∈ (gradingComponents A π e).support,
          (1 : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] ((gradingComponents A π e) g) := by
    conv_lhs => rw [← sum_componentProj_eq A π e]
    rw [Finsupp.sum, TensorProduct.tmul_sum]
  rw [gradingCoaction_eq_sum_components A π e, hsume, Finsupp.sum, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun g _ => ?_
  show (MonoidAlgebra.single g (1 : R) : MonoidAlgebra R (Multiplicative A))
        ⊗ₜ[R] ((gradingComponents A π e) g)
      - (1 : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] ((gradingComponents A π e) g)
      ∈ augIdeal (R := R) (H := H) A
  rw [← TensorProduct.sub_tmul]
  have hfac : ((MonoidAlgebra.single g (1 : R) : MonoidAlgebra R (Multiplicative A)) - 1)
        ⊗ₜ[R] ((gradingComponents A π e) g)
      = (((MonoidAlgebra.single g (1 : R) : MonoidAlgebra R (Multiplicative A)) - 1)
          ⊗ₜ[R] (1 : H))
        * ((1 : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] ((gradingComponents A π e) g)) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [hfac]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨g, rfl⟩)

theorem isIdempotentElem_mem_gradedPiece_zero [Finite A] [IsLocalRing R] [IsNoetherianRing R]
    [Module.Finite R H] {q : ℕ} (hq : q.Prime) (hqR : ¬ IsUnit ((q : ℕ) : R))
    {k : ℕ} (hqA : ∀ a : A, q ^ k • a = 0) {e : H} (he : IsIdempotentElem e) :
    e ∈ gradedPiece A π 0 := by
  suffices hρ : gradingCoaction A π e = (1 : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] e by
    apply mem_gradedPiece_of_gradingCoaction A π
    rw [hρ, ofAdd_zero]
    exact congrArg (fun m : MonoidAlgebra R (Multiplicative A) => m ⊗ₜ[R] e)
      MonoidAlgebra.one_def
  have h₁ : gradingCoaction A π e * gradingCoaction A π e = gradingCoaction A π e := by
    rw [← gradingCoaction_mul A π e e, he.eq]
  have h₂ : ((1 : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] e)
        * ((1 : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] e)
      = (1 : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] e := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, he.eq]
  have hdJ := gradingCoaction_sub_one_tmul_mem_augIdeal A π e
  obtain ⟨n, hJn⟩ := exists_augIdeal_pow_le (R := R) (H := H) A hq hqA
  rw [← sub_eq_zero]
  generalize gradingCoaction A π e = x at h₁ hdJ ⊢
  generalize (1 : MonoidAlgebra R (Multiplicative A)) ⊗ₜ[R] e = y at h₂ hdJ ⊢
  have hd3 : (x - y) * ((x - y) * (x - y)) = x - y := by
    linear_combination (x + 1 - 3 * y) * h₁ + (3 * x - y - 1) * h₂
  exact eq_zero_of_mul_self_mul_self_of_pow_le hqR hJn hd3 hdJ

omit [DecidableEq A] in

theorem lift_comp_apply {L : Type} [CommRing L] [Algebra R L]
    (s : MonoidAlgebra R (Multiplicative A) →ₐ[R] L) (ψ : H →ₐ[R] L) (z : H ⊗[R] H) :
    Algebra.TensorProduct.lift (s.comp (π : H →ₐ[R] MonoidAlgebra R (Multiplicative A))) ψ
        (fun _ _ => Commute.all _ _) z
      = Algebra.TensorProduct.lift s ψ (fun _ _ => Commute.all _ _)
          (LinearMap.rTensor H π.toLinearMap z) := by
  induction z with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul u v =>
    rw [LinearMap.rTensor_tmul, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
    rfl
  | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]

theorem toConv_comp_convMul_apply_of_mem {L : Type} [CommRing L] [Algebra R L]
    (s : MonoidAlgebra R (Multiplicative A) →ₐ[R] L) (ψ : WithConv (H →ₐ[R] L))
    {j : A} {t : H} (ht : t ∈ gradedPiece A π j) :
    (WithConv.toConv (s.comp (π : H →ₐ[R] MonoidAlgebra R (Multiplicative A))) * ψ) t
      = s (MonoidAlgebra.single (Multiplicative.ofAdd j) (1 : R)) * ψ t := by
  rw [AlgHom.convMul_apply, WithConv.ofConv_toConv, lift_comp_apply A π, ← gradingCoaction_apply,
    gradingCoaction_eq_of_mem A π ht]
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

omit [DecidableEq A] in

theorem single_ofAdd_zero_one_eq_one :
    MonoidAlgebra.single (Multiplicative.ofAdd (0 : A)) (1 : R) = (1 : MonoidAlgebra R (Multiplicative A)) := by
  rw [ofAdd_zero]
  exact MonoidAlgebra.one_def.symm

omit [DecidableEq A] in

theorem assoc_naturality_left :
    (TensorProduct.assoc R (MonoidAlgebra R (Multiplicative A)) H H).toLinearMap ∘ₗ
        LinearMap.rTensor H (LinearMap.rTensor H π.toLinearMap)
      = TensorProduct.map π.toLinearMap (LinearMap.id : H ⊗[R] H →ₗ[R] H ⊗[R] H) ∘ₗ
          (TensorProduct.assoc R H H H).toLinearMap := by
  apply TensorProduct.ext_threefold
  intro x y z
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.assoc_tmul, TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.id_apply]

omit [DecidableEq A] in

theorem map_comp_lTensor_comul :
    TensorProduct.map π.toLinearMap (LinearMap.id : H ⊗[R] H →ₗ[R] H ⊗[R] H) ∘ₗ
        LinearMap.lTensor H (Coalgebra.comul (R := R))
      = LinearMap.lTensor (MonoidAlgebra R (Multiplicative A)) (Coalgebra.comul (R := R)) ∘ₗ
          LinearMap.rTensor H π.toLinearMap := by
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.lTensor_tmul,
    LinearMap.rTensor_tmul, TensorProduct.map_tmul, LinearMap.id_apply]

theorem rTensor_gradingCoaction_comul_of_mem {j : A} {t : H} (ht : t ∈ gradedPiece A π j) :
    LinearMap.rTensor H (gradingCoaction A π) ((Coalgebra.comul (R := R)) t)
      = (TensorProduct.assoc R (MonoidAlgebra R (Multiplicative A)) H H).symm
          ((MonoidAlgebra.single (Multiplicative.ofAdd j) (1 : R) : MonoidAlgebra R (Multiplicative A))
            ⊗ₜ[R] (Coalgebra.comul (R := R)) t) := by
  rw [LinearEquiv.eq_symm_apply]
  have h1 : LinearMap.rTensor H (gradingCoaction A π)
      = LinearMap.rTensor H (LinearMap.rTensor H π.toLinearMap) ∘ₗ
          LinearMap.rTensor H (Coalgebra.comul (R := R)) := by
    unfold gradingCoaction
    rw [LinearMap.rTensor_comp]
  have h2 := DFunLike.congr_fun (assoc_naturality_left A π)
    (LinearMap.rTensor H (Coalgebra.comul (R := R)) ((Coalgebra.comul (R := R)) t))
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at h2
  have h3 := DFunLike.congr_fun (map_comp_lTensor_comul A π) ((Coalgebra.comul (R := R)) t)
  simp only [LinearMap.coe_comp, Function.comp_apply] at h3
  rw [h1, LinearMap.comp_apply, h2, Coalgebra.coassoc_apply, h3, ← gradingCoaction_apply,
    gradingCoaction_eq_of_mem A π ht]
  exact LinearMap.lTensor_tmul _ _ _ _

theorem finsuppScalarLeft_single_one_tmul_apply_same (j : A) (u : H) :
    (maScalarLeft A H)
        ((MonoidAlgebra.single (Multiplicative.ofAdd j) (1 : R) : MonoidAlgebra R (Multiplicative A))
          ⊗ₜ[R] u) (Multiplicative.ofAdd j) = u := by
  rw [maScalarLeft_single_tmul, one_smul, Finsupp.single_eq_same]

theorem rTensor_lapply_rTensor_finsuppScalarLeft_assoc_symm (j : A) (z : H ⊗[R] H) :
    LinearMap.rTensor H (Finsupp.lapply (Multiplicative.ofAdd j) : (Multiplicative A →₀ H) →ₗ[R] H)
        (LinearMap.rTensor H (maScalarLeft A H).toLinearMap
          ((TensorProduct.assoc R (MonoidAlgebra R (Multiplicative A)) H H).symm
            (MonoidAlgebra.single (Multiplicative.ofAdd j) (1 : R) ⊗ₜ[R] z)))
      = z := by
  induction z with
  | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero, map_zero]
  | tmul u v =>
    rw [TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
    exact congrArg (fun w : H => w ⊗ₜ[R] v) (finsuppScalarLeft_single_one_tmul_apply_same A j u)
  | add z₁ z₂ h₁ h₂ => rw [TensorProduct.tmul_add, map_add, map_add, map_add, h₁, h₂]

theorem rTensor_componentProj_comul_of_mem {j : A} {t : H} (ht : t ∈ gradedPiece A π j) :
    LinearMap.rTensor H (componentProj A π j) ((Coalgebra.comul (R := R)) t)
      = (Coalgebra.comul (R := R)) t := by
  have e1 : LinearMap.rTensor H (componentProj A π j)
      = LinearMap.rTensor H
          (Finsupp.lapply (Multiplicative.ofAdd j) : (Multiplicative A →₀ H) →ₗ[R] H) ∘ₗ
          LinearMap.rTensor H (gradingComponents A π) := by
    unfold componentProj
    rw [LinearMap.rTensor_comp]
  have e2 : LinearMap.rTensor H (gradingComponents A π)
      = LinearMap.rTensor H (maScalarLeft A H).toLinearMap ∘ₗ
          LinearMap.rTensor H (gradingCoaction A π) := by
    rw [← LinearMap.rTensor_comp]
    rfl
  rw [e1, LinearMap.comp_apply, e2, LinearMap.comp_apply,
    rTensor_gradingCoaction_comul_of_mem A π ht]
  exact rTensor_lapply_rTensor_finsuppScalarLeft_assoc_symm A j _

omit [AddCommGroup A] in

theorem finsetSum_single_apply (g₀ : Multiplicative A) (s : Finset (Multiplicative A))
    (c : Multiplicative A → R) :
    (∑ g ∈ s, Finsupp.single g (c g) : Multiplicative A →₀ R) g₀
      = if g₀ ∈ s then c g₀ else 0 := by
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply, Finset.sum_ite_eq']

theorem exists_mem_gradedPiece_counit_eq_one (hsurj : Function.Surjective π) (j : A) :
    ∃ h ∈ gradedPiece A π j, Coalgebra.counit (R := R) h = 1 := by
  obtain ⟨h', hh'⟩ := hsurj (MonoidAlgebra.single (Multiplicative.ofAdd j) (1 : R))
  refine ⟨componentProj A π j h', componentProj_mem_gradedPiece A π h' j, ?_⟩
  have h1 : π h' = ∑ g ∈ (gradingComponents A π h').support,
      (MonoidAlgebra.single g (Coalgebra.counit (R := R) ((gradingComponents A π h') g))
        : MonoidAlgebra R (Multiplicative A)) := by
    conv_lhs => rw [← sum_componentProj_eq A π h']
    rw [Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    have hmem : (gradingComponents A π h') g ∈ gradedPiece A π (Multiplicative.toAdd g) :=
      componentProj_mem_gradedPiece A π h' (Multiplicative.toAdd g)
    exact (coalgHom_apply_mem_single_line A π hmem).trans
      (congrArg (MonoidAlgebra.single (Multiplicative.ofAdd (Multiplicative.toAdd g)))
        (CoalgHomClass.counit_comp_apply π _))
  have hexp : (Finsupp.single (Multiplicative.ofAdd j) (1 : R) : Multiplicative A →₀ R)
      = ∑ g ∈ (gradingComponents A π h').support,
          Finsupp.single g (Coalgebra.counit (R := R) ((gradingComponents A π h') g)) := by
    have := congrArg (MonoidAlgebra.coeffLinearEquiv R) (hh'.symm.trans h1)
    simpa only [map_sum, MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.coeff_single] using this
  have hc := DFunLike.congr_fun hexp (Multiplicative.ofAdd j)
  rw [Finsupp.single_eq_same, finsetSum_single_apply] at hc
  split_ifs at hc with hs
  · exact hc.symm
  · exact eq_of_zero_eq_one hc.symm _ _

end S17.TorsorCoreGen

end

noncomputable section

namespace S17
namespace TorsorCoreGen
open HopfAlgebra.TorsorGrading

open TensorProduct

section Bridge

variable {q : ℕ} [Fact q.Prime] {Λ : Type} [AddCommGroup Λ] [DecidableEq Λ] {L : Type} [Field L] [IsAlgClosed L] [CharZero L] {O : Type} [CommRing O] [IsDomain O] [Algebra O L] [FaithfulSMul O L]
  {HO : Type} [CommRing HO] [Bialgebra O HO]
  (p₀ : HO →ₐc[O] MonoidAlgebra O (Multiplicative Λ))

theorem mul_mem_blockPiece_of_mem {e : HO} (hidem : IsIdempotentElem e)
    (he0 : e ∈ gradedPiece Λ p₀ 0) {j : Λ} {t : HO}
    (ht : t ∈ gradedPiece Λ p₀ j) : t * e ∈ blockPiece Λ p₀ e j := by
  refine (mem_blockPiece_iff Λ p₀ e j _).mpr ⟨?_, by rw [mul_assoc, hidem.eq]⟩
  have h := gradedPiece_mul_mem Λ p₀ j 0 t e ht he0
  rwa [add_zero] at h

theorem blockPiece_mul_mem {e : HO} (i j : Λ)
    {x y : HO} (hx : x ∈ blockPiece Λ p₀ e i) (hy : y ∈ blockPiece Λ p₀ e j) :
    x * y ∈ blockPiece Λ p₀ e (i + j) := by
  obtain ⟨hx1, _⟩ := (mem_blockPiece_iff Λ p₀ e i x).mp hx
  obtain ⟨hy1, hy2⟩ := (mem_blockPiece_iff Λ p₀ e j y).mp hy
  exact (mem_blockPiece_iff Λ p₀ e (i + j) _).mpr
    ⟨gradedPiece_mul_mem Λ p₀ i j x y hx1 hy1, by rw [mul_assoc, hy2]⟩

theorem mem_iSup_blockPiece_of_mul_eq {e : HO} (he0 : e ∈ gradedPiece Λ p₀ 0)
    (x : HO) (hx : x * e = x) : x ∈ ⨆ j : Λ, blockPiece Λ p₀ e j := by
  rw [← sum_componentProj_eq Λ p₀ x, Finsupp.sum]
  refine Submodule.sum_mem _ fun g _ => ?_
  refine Submodule.mem_iSup_of_mem (Multiplicative.toAdd g) ?_
  refine (mem_blockPiece_iff Λ p₀ e _ _).mpr
    ⟨componentProj_mem_gradedPiece Λ p₀ x (Multiplicative.toAdd g), ?_⟩
  have h := gradingComponents_mul_of_mem_zero Λ p₀ he0 x g
  rw [hx] at h
  exact h.symm

end Bridge

section Arithmetic

theorem isUnit_of_mul_mem_eq_one (q : ℕ) {L : Type} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    (hA : A.LiesOverPrime q) (O : Type) [CommRing O] [IsDomain O] [Algebra O L] [FaithfulSMul O L]
    (hOA : ∀ x : O, algebraMap O L x ∈ A)
    (hOdvr : IsDiscreteValuationRing O) (hOirr : Irreducible ((q : ℕ) : O))
    (c : O) {β : L} (hβ : β ∈ A) (h : algebraMap O L c * β = 1) :
    IsUnit c := by
  haveI := hOdvr
  by_contra hc
  have hcm : c ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal c).mpr (mem_nonunits_iff.mpr hc)
  rw [hOirr.maximalIdeal_eq] at hcm
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp hcm
  have h2 : ((q : ℕ) : L) * ((algebraMap O L (c' : O)) * β) = 1 := by
    rw [← h, ← hc']
    push_cast
    ring
  have hq : A.valuation ((q : ℕ) : L) < 1 := (A.mem_nonunits_iff).mp hA
  have hmem : (algebraMap O L (c' : O)) * β ∈ A := mul_mem (hOA c') hβ
  have hv : A.valuation ((algebraMap O L (c' : O)) * β) ≤ 1 :=
    (A.valuation_le_one_iff _).mpr hmem
  have hval := congrArg A.valuation h2
  rw [Valuation.map_mul, Valuation.map_one] at hval
  have hlt : A.valuation ((q : ℕ) : L)
      * A.valuation ((algebraMap O L (c' : O)) * β) < 1 := by
    calc A.valuation ((q : ℕ) : L)
          * A.valuation ((algebraMap O L (c' : O)) * β)
        ≤ A.valuation ((q : ℕ) : L) * 1 := mul_le_mul_right hv _
      _ = A.valuation ((q : ℕ) : L) := mul_one _
      _ < 1 := hq
  rw [hval] at hlt
  exact lt_irrefl _ hlt

end Arithmetic

section Furniture

theorem apply_mem_valuationSubring_of_moduleFinite
    {L : Type} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L) (O : Type) [CommRing O] [IsDomain O] [Algebra O L] [FaithfulSMul O L]
    (hOA : ∀ x : O, algebraMap O L x ∈ A)
    (H₁ : Type) [CommRing H₁] [Algebra O H₁] [Module.Finite O H₁]
    (f : H₁ →ₐ[O] L) (h : H₁) : f h ∈ A := by
  classical
  have hint : IsIntegral O (f h) := (Algebra.IsIntegral.isIntegral (R := O) h).map f
  obtain ⟨p, hpm, hpev⟩ := hint
  rw [← A.valuation_le_one_iff]
  by_contra hgt
  rw [not_le] at hgt
  have hy0 : A.valuation (f h) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hgt)
  have hsum : ∑ i ∈ Finset.range (p.natDegree + 1),
      algebraMap O L (p.coeff i) * f h ^ i = 0 := by
    rw [← Polynomial.eval₂_eq_sum_range]
    exact hpev
  rw [Finset.sum_range_succ, hpm.coeff_natDegree, map_one, one_mul] at hsum
  have hyd : f h ^ p.natDegree
      = -∑ i ∈ Finset.range p.natDegree,
          algebraMap O L (p.coeff i) * f h ^ i :=
    eq_neg_of_add_eq_zero_right hsum
  have hlt : A.valuation (∑ i ∈ Finset.range p.natDegree,
      algebraMap O L (p.coeff i) * f h ^ i)
        < A.valuation (f h) ^ p.natDegree := by
    apply Valuation.map_sum_lt _ (pow_ne_zero _ hy0)
    intro i hi
    have hi' : i < p.natDegree := Finset.mem_range.mp hi
    rw [Valuation.map_mul, Valuation.map_pow]
    calc A.valuation (algebraMap O L (p.coeff i)) * A.valuation (f h) ^ i
        ≤ 1 * A.valuation (f h) ^ i := by
          apply mul_le_mul_left
          exact (A.valuation_le_one_iff _).mpr (hOA (p.coeff i))
      _ = A.valuation (f h) ^ i := one_mul _
      _ < A.valuation (f h) ^ p.natDegree := pow_lt_pow_right₀ hgt hi'
  have hcontra : A.valuation (f h ^ p.natDegree) < A.valuation (f h) ^ p.natDegree := by
    rw [hyd, Valuation.map_neg]
    exact hlt
  rw [Valuation.map_pow] at hcontra
  exact lt_irrefl _ hcontra

theorem exists_convMul_eq_one_of_comm {R H L : Type} [CommRing R] [CommRing H] [HopfAlgebra R H]
    [CommRing L] [Algebra R L]
    (f : WithConv (H →ₐ[R] L)) : ∃ g : WithConv (H →ₐ[R] L), g * f = 1 := by
  let S : H →ₐ[R] H :=
    { toFun := fun h => HopfAlgebra.antipode R h
      map_one' := HopfAlgebra.antipode_one
      map_mul' := fun x y => by rw [HopfAlgebra.antipode_mul, mul_comm]
      map_zero' := map_zero _
      map_add' := fun x y => map_add _ x y
      commutes' := fun r => by
        rw [Algebra.algebraMap_eq_smul_one, map_smul, HopfAlgebra.antipode_one] }
  have hS : ∀ h, S h = HopfAlgebra.antipode R h := fun _ => rfl
  refine ⟨WithConv.toConv ((WithConv.ofConv f).comp S), ?_⟩
  apply WithConv.ext
  apply AlgHom.ext
  intro h
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply, WithConv.ofConv_toConv]
  have key : ∀ t : TensorProduct R H H,
      Algebra.TensorProduct.lift ((WithConv.ofConv f).comp S) (WithConv.ofConv f)
          (fun _ _ => Commute.all _ _) t
        = (WithConv.ofConv f) (LinearMap.mul' R H ((HopfAlgebra.antipode R).rTensor H t)) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
        rw [Algebra.TensorProduct.lift_tmul, LinearMap.rTensor_tmul, LinearMap.mul'_apply, map_mul,
          AlgHom.comp_apply, hS]
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add, map_add]
  rw [key, HopfAlgebra.mul_antipode_rTensor_comul_apply, AlgHom.commutes]

end Furniture

section Orbit

variable {q : ℕ} [Fact q.Prime] {Λ : Type} [AddCommGroup Λ] [DecidableEq Λ] [Fintype Λ] {L : Type} [Field L] [IsAlgClosed L] [CharZero L] {O : Type} [CommRing O] [IsDomain O] [Algebra O L] [FaithfulSMul O L]
  {HO : Type} [CommRing HO] [HopfAlgebra O HO] [Coalgebra.IsCocomm O HO]
  (p₀ : HO →ₐc[O] MonoidAlgebra O (Multiplicative Λ))

omit [DecidableEq Λ] in

theorem natCard_algHom_monoidAlgebra_eq :
    Nat.card (MonoidAlgebra O (Multiplicative Λ) →ₐ[O] L) = Fintype.card Λ := by
  rw [HopfAlgebra.natCard_algHom_eq_finrank_of_charZero]
  rw [(MonoidAlgebra.coeffLinearEquiv O).finrank_eq, Module.finrank_finsupp_self,
    Fintype.card_multiplicative]

theorem exists_eq_toConv_comp_convMul (hsurj : Function.Surjective ⇑p₀)
    {e : HO} (he0 : e ∈ gradedPiece Λ p₀ 0)
    (hcard : Nat.card {ψ : WithConv (HO →ₐ[O] L) // ψ e = 1} = Fintype.card Λ)
    (ψ₁ : WithConv (HO →ₐ[O] L)) (hψ₁ : ψ₁ e = 1)
    (φ : WithConv (HO →ₐ[O] L)) (hφ : φ e = 1) :
    ∃ s : MonoidAlgebra O (Multiplicative Λ) →ₐ[O] L,
      φ = WithConv.toConv
            (s.comp (p₀ : HO →ₐ[O] MonoidAlgebra O (Multiplicative Λ))) * ψ₁ := by
  have hstable : ∀ s : MonoidAlgebra O (Multiplicative Λ) →ₐ[O] L,
      (WithConv.toConv
        (s.comp (p₀ : HO →ₐ[O] MonoidAlgebra O (Multiplicative Λ))) * ψ₁) e = 1 := by
    intro s
    rw [toConv_comp_convMul_apply_of_mem Λ p₀ s ψ₁ he0, single_ofAdd_zero_one_eq_one,
      map_one, hψ₁, one_mul]
  let Φ : (MonoidAlgebra O (Multiplicative Λ) →ₐ[O] L) →
      {ψ : WithConv (HO →ₐ[O] L) // ψ e = 1} :=
    fun s => ⟨WithConv.toConv
      (s.comp (p₀ : HO →ₐ[O] MonoidAlgebra O (Multiplicative Λ))) * ψ₁, hstable s⟩
  have hinj : Function.Injective Φ := by
    intro s s' hss'
    have h1 : WithConv.toConv
          (s.comp (p₀ : HO →ₐ[O] MonoidAlgebra O (Multiplicative Λ))) * ψ₁
        = WithConv.toConv
          (s'.comp (p₀ : HO →ₐ[O] MonoidAlgebra O (Multiplicative Λ))) * ψ₁ :=
      congrArg Subtype.val hss'
    obtain ⟨g, hg⟩ := exists_convMul_eq_one_of_comm ψ₁
    have hg' : ψ₁ * g = 1 := by rw [mul_comm]; exact hg
    have h2 : WithConv.toConv
          (s.comp (p₀ : HO →ₐ[O] MonoidAlgebra O (Multiplicative Λ)))
        = WithConv.toConv
          (s'.comp (p₀ : HO →ₐ[O] MonoidAlgebra O (Multiplicative Λ))) := by
      have h1' := congrArg (fun x => x * g) h1
      simp only [mul_assoc, hg', mul_one] at h1'
      exact h1'
    have h3 := WithConv.toConv_injective h2
    refine AlgHom.ext fun m => ?_
    obtain ⟨h, rfl⟩ := hsurj m
    exact DFunLike.congr_fun h3 h
  haveI : Finite {ψ : WithConv (HO →ₐ[O] L) // ψ e = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Fintype.card_ne_zero)
  have hbij : Function.Bijective Φ :=
    hinj.bijective_of_nat_card_le (le_of_eq (by rw [hcard, natCard_algHom_monoidAlgebra_eq]))
  obtain ⟨s, hs⟩ := hbij.2 ⟨φ, hφ⟩
  exact ⟨s, (congrArg Subtype.val hs).symm⟩

theorem exists_forall_apply_eq_mul_of_point (hsurj : Function.Surjective ⇑p₀)
    {e : HO} (hidem : IsIdempotentElem e) (he0 : e ∈ gradedPiece Λ p₀ 0)
    (hcard : Nat.card {ψ : WithConv (HO →ₐ[O] L) // ψ e = 1} = Fintype.card Λ)
    (ψ₁ : WithConv (HO →ₐ[O] L)) (hψ₁ : ψ₁ e = 1) (j : Λ)
    (φ : WithConv (HO →ₐ[O] L)) :
    ∃ lam : L, ∀ t ∈ blockPiece Λ p₀ e j, φ t = lam * ψ₁ t := by
  have hφe : IsIdempotentElem (φ e) := by
    show φ e * φ e = φ e
    rw [← map_mul, hidem.eq]
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hφe with h0 | h1
  · refine ⟨0, fun t ht => ?_⟩
    obtain ⟨_, hte⟩ := (mem_blockPiece_iff Λ p₀ e j t).mp ht
    calc φ t = φ (t * e) := by rw [hte]
      _ = φ t * φ e := map_mul _ _ _
      _ = 0 * ψ₁ t := by rw [h0, mul_zero, zero_mul]
  · obtain ⟨s, rfl⟩ := exists_eq_toConv_comp_convMul p₀ hsurj he0 hcard ψ₁ hψ₁ φ h1
    refine ⟨s (MonoidAlgebra.single (Multiplicative.ofAdd j) (1 : O)), fun t ht => ?_⟩
    obtain ⟨htj, _⟩ := (mem_blockPiece_iff Λ p₀ e j t).mp ht
    exact toConv_comp_convMul_apply_of_mem Λ p₀ s ψ₁ htj

end Orbit

section Span

variable {L : Type} [Field L] [IsAlgClosed L] [CharZero L] {O : Type} [CommRing O] [IsDomain O] [Algebra O L] [FaithfulSMul O L] {HO : Type} [CommRing HO] [HopfAlgebra O HO]
  [Module.Finite O HO] [Module.Flat O HO]

theorem span_range_toLinearMap_eq_top (hOdvr : IsDiscreteValuationRing O) [Nontrivial HO] :
    Submodule.span L
        (Set.range fun ψ : HO →ₐ[O] L => ψ.toLinearMap) = ⊤ := by
  classical
  haveI := hOdvr
  haveI : Module.Free O HO := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis O HO
  let cb : (Module.Free.ChooseBasisIndex O HO → L)
      ≃ₗ[L] (HO →ₗ[O] L) := b.constr L
  haveI : FiniteDimensional L (HO →ₗ[O] L) :=
    LinearEquiv.finiteDimensional cb
  have hrank : Module.finrank L (HO →ₗ[O] L)
      = Module.finrank O HO := by
    rw [← cb.finrank_eq, Module.finrank_fintype_fun_eq_card, Module.finrank_eq_card_basis b]
  have hcardpts : Nat.card (HO →ₐ[O] L) = Module.finrank O HO :=
    HopfAlgebra.natCard_algHom_eq_finrank_of_charZero O HO L
  haveI : Finite (HO →ₐ[O] L) :=
    Nat.finite_of_card_ne_zero (by rw [hcardpts]; exact Module.finrank_pos.ne')
  letI : Fintype (HO →ₐ[O] L) := Fintype.ofFinite _
  have hli : LinearIndependent L
      (fun ψ : HO →ₐ[O] L => ψ.toLinearMap) := by
    let toFn : (HO →ₗ[O] L) →ₗ[L] (HO → L) :=
      { toFun := fun f => ⇑f
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine LinearIndependent.of_comp toFn ?_
    exact (linearIndependent_monoidHom HO L).comp
      (fun ψ : HO →ₐ[O] L => (ψ : HO →* L))
      (fun _ _ hψ => AlgHom.ext fun x => DFunLike.congr_fun hψ x)
  have hcount : Fintype.card (HO →ₐ[O] L)
      = Module.finrank L (HO →ₗ[O] L) := by
    rw [hrank, ← hcardpts, Nat.card_eq_fintype_card]
  exact hli.span_eq_top_of_card_eq_finrank' hcount

end Span

section Cyclic

variable {q : ℕ} [Fact q.Prime] {Λ : Type} [AddCommGroup Λ] [DecidableEq Λ] [Fintype Λ] {L : Type} [Field L] [IsAlgClosed L] [CharZero L] {O : Type} [CommRing O] [IsDomain O] [Algebra O L] [FaithfulSMul O L]
  {HO : Type} [CommRing HO] [HopfAlgebra O HO]
  [Module.Finite O HO] [Module.Flat O HO] [Coalgebra.IsCocomm O HO]
  (p₀ : HO →ₐc[O] MonoidAlgebra O (Multiplicative Λ))

theorem exists_forall_apply_eq_mul_of_linearMap (hOdvr : IsDiscreteValuationRing O)
    (hsurj : Function.Surjective ⇑p₀)
    {e : HO} (hidem : IsIdempotentElem e) (he0 : e ∈ gradedPiece Λ p₀ 0)
    (hcard : Nat.card {ψ : WithConv (HO →ₐ[O] L) // ψ e = 1} = Fintype.card Λ)
    (ψ₁ : WithConv (HO →ₐ[O] L)) (hψ₁ : ψ₁ e = 1) (j : Λ)
    (G : HO →ₗ[O] L) :
    ∃ lam : L, ∀ t ∈ blockPiece Λ p₀ e j, G t = lam * ψ₁ t := by
  haveI : Nontrivial HO := (WithConv.ofConv ψ₁).toRingHom.domain_nontrivial
  have hG : G ∈ Submodule.span L
      (Set.range fun ψ : HO →ₐ[O] L => ψ.toLinearMap) := by
    rw [span_range_toLinearMap_eq_top hOdvr]
    exact Submodule.mem_top
  induction hG using Submodule.span_induction with
  | mem G' hG' =>
    obtain ⟨ψ, rfl⟩ := hG'
    obtain ⟨lam, hlam⟩ := exists_forall_apply_eq_mul_of_point p₀ hsurj hidem he0 hcard ψ₁ hψ₁ j
      (WithConv.toConv ψ)
    exact ⟨lam, fun t ht => hlam t ht⟩
  | zero => exact ⟨0, fun t _ => by rw [LinearMap.zero_apply, zero_mul]⟩
  | add G₁ G₂ _ _ ih₁ ih₂ =>
    obtain ⟨l₁, hl₁⟩ := ih₁
    obtain ⟨l₂, hl₂⟩ := ih₂
    exact ⟨l₁ + l₂, fun t ht => by rw [LinearMap.add_apply, hl₁ t ht, hl₂ t ht, add_mul]⟩
  | smul c G' _ ih =>
    obtain ⟨l, hl⟩ := ih
    exact ⟨c * l, fun t ht => by rw [LinearMap.smul_apply, hl t ht, smul_eq_mul, mul_assoc]⟩

theorem exists_blockPiece_eq_span (hOdvr : IsDiscreteValuationRing O)
    (hsurj : Function.Surjective ⇑p₀)
    {e : HO} (hidem : IsIdempotentElem e) (he0 : e ∈ gradedPiece Λ p₀ 0)
    (hcard : Nat.card {ψ : WithConv (HO →ₐ[O] L) // ψ e = 1} = Fintype.card Λ)
    (ψ₁ : WithConv (HO →ₐ[O] L)) (hψ₁ : ψ₁ e = 1) (j : Λ) :
    ∃ t : HO, blockPiece Λ p₀ e j = Submodule.span O {t} := by
  classical
  haveI := hOdvr
  haveI : Module.Free O HO := Module.free_of_flat_of_isLocalRing
  obtain ⟨n, bN⟩ := Submodule.basisOfPid (Module.Free.chooseBasis O HO) (blockPiece Λ p₀ e j)
  rcases n with _ | _ | n
  · refine ⟨0, ?_⟩
    rw [Submodule.span_zero_singleton, eq_bot_iff]
    intro x hx
    have hy : (⟨x, hx⟩ : blockPiece Λ p₀ e j) = 0 :=
      bN.repr.injective (Finsupp.ext fun i => Fin.elim0 i)
    exact (Submodule.mem_bot O).mpr (by simpa using congrArg Subtype.val hy)
  · refine ⟨(bN 0 : HO), le_antisymm ?_ ?_⟩
    · intro x hx
      have h := bN.sum_repr ⟨x, hx⟩
      rw [Fin.sum_univ_one] at h
      rw [Submodule.mem_span_singleton]
      exact ⟨bN.repr ⟨x, hx⟩ 0, by rw [← Submodule.coe_smul, h]⟩
    · rw [Submodule.span_singleton_le_iff_mem]
      exact (bN 0).2
  · exfalso

    let r : HO →ₗ[O] blockPiece Λ p₀ e j :=
      (LinearMap.mulRight O e ∘ₗ componentProj Λ p₀ j).codRestrict (blockPiece Λ p₀ e j)
        (fun x => mul_mem_blockPiece_of_mem p₀ hidem he0
          (componentProj_mem_gradedPiece Λ p₀ x j))
    have hr : ∀ y : blockPiece Λ p₀ e j, r (y : HO) = y := by
      intro y
      obtain ⟨hy1, hy2⟩ := (mem_blockPiece_iff Λ p₀ e j (y : HO)).mp y.2
      apply Subtype.ext
      show componentProj Λ p₀ j (y : HO) * e = (y : HO)
      rw [componentProj_eq_of_mem Λ p₀ hy1, hy2]

    let G : Fin (n + 2) → (HO →ₗ[O] L) := fun i =>
      Algebra.linearMap O L ∘ₗ bN.coord i ∘ₗ r
    have hG : ∀ (i : Fin (n + 2)) (y : blockPiece Λ p₀ e j),
        G i (y : HO) = algebraMap O L (bN.repr y i) := by
      intro i y
      show algebraMap O L (bN.coord i (r (y : HO))) = _
      rw [hr y, bN.coord_apply]
    have key : ∀ i : Fin (n + 2), ∃ lam : L, ∀ y : blockPiece Λ p₀ e j,
        algebraMap O L (bN.repr y i) = lam * ψ₁ (y : HO) := by
      intro i
      obtain ⟨lam, hlam⟩ :=
        exists_forall_apply_eq_mul_of_linearMap p₀ hOdvr hsurj hidem he0 hcard ψ₁ hψ₁ j (G i)
      exact ⟨lam, fun y => by rw [← hG i y]; exact hlam (y : HO) y.2⟩
    obtain ⟨i₀, hi₀⟩ : ∃ i : Fin (n + 2), (i : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
    obtain ⟨i₁, hi₁⟩ : ∃ i : Fin (n + 2), (i : ℕ) = 1 := ⟨⟨1, by omega⟩, rfl⟩
    have hne : i₀ ≠ i₁ := by
      intro h
      rw [h] at hi₀
      omega
    obtain ⟨l₀, hl₀⟩ := key i₀
    obtain ⟨l₁, hl₁⟩ := key i₁
    have h00 := hl₀ (bN i₀)
    have h01 := hl₀ (bN i₁)
    have h11 := hl₁ (bN i₁)
    rw [bN.repr_self, Finsupp.single_eq_same, map_one] at h00
    rw [bN.repr_self, Finsupp.single_apply, if_neg hne.symm, map_zero] at h01
    rw [bN.repr_self, Finsupp.single_eq_same, map_one] at h11
    have hl₀ne : l₀ ≠ 0 := by
      intro h
      rw [h, zero_mul] at h00
      exact one_ne_zero h00
    have hv : ψ₁ ((bN i₁ : blockPiece Λ p₀ e j) : HO) = 0 :=
      (mul_eq_zero.mp h01.symm).resolve_left hl₀ne
    rw [hv, mul_zero] at h11
    exact one_ne_zero h11

end Cyclic

section Units

variable {q : ℕ} [Fact q.Prime] {Λ : Type} [AddCommGroup Λ] [DecidableEq Λ] [Fintype Λ] {L : Type} [Field L] [IsAlgClosed L] [CharZero L] {O : Type} [CommRing O] [IsDomain O] [Algebra O L] [FaithfulSMul O L]
  {HO : Type} [CommRing HO] [HopfAlgebra O HO]
  [Module.Finite O HO] [Coalgebra.IsCocomm O HO]
  (p₀ : HO →ₐc[O] MonoidAlgebra O (Multiplicative Λ))

omit [Fintype Λ] in

theorem exists_mem_mul_apply_eq_one (A : ValuationSubring L)
    (hOA : ∀ x : O, algebraMap O L x ∈ A) (hsurj : Function.Surjective ⇑p₀)
    {e : HO} (hidem : IsIdempotentElem e) (he0 : e ∈ gradedPiece Λ p₀ 0)
    (ψ₁ : WithConv (HO →ₐ[O] L)) (hψ₁ : ψ₁ e = 1) (j : Λ)
    {t : HO} (hspan : blockPiece Λ p₀ e j = Submodule.span O {t}) :
    ∃ α ∈ A, ψ₁ t * α = 1 := by
  obtain ⟨h, hhj, hh1⟩ := exists_mem_gradedPiece_counit_eq_one Λ p₀ hsurj j
  obtain ⟨g, hg⟩ := exists_convMul_eq_one_of_comm ψ₁
  have h1 : (ψ₁ * g) h = 1 := by
    rw [mul_comm, hg, AlgHom.convOne_apply, hh1, map_one]
  rw [AlgHom.convMul_apply, ← rTensor_componentProj_comul_of_mem Λ p₀ hhj] at h1
  have key : ∀ z : HO ⊗[O] HO, ∃ α ∈ A,
      Algebra.TensorProduct.lift (WithConv.ofConv ψ₁) (WithConv.ofConv g)
          (fun _ _ => Commute.all _ _) (LinearMap.rTensor HO (componentProj Λ p₀ j) z)
        = ψ₁ t * α := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, zero_mem A, by rw [map_zero, map_zero, mul_zero]⟩
    | tmul x y =>
      have hmem := mul_mem_blockPiece_of_mem p₀ hidem he0
        (componentProj_mem_gradedPiece Λ p₀ x j)
      rw [hspan, Submodule.mem_span_singleton] at hmem
      obtain ⟨c, hc⟩ := hmem
      refine ⟨algebraMap O L c * g y,
        mul_mem (hOA c) (apply_mem_valuationSubring_of_moduleFinite A O hOA HO
          (WithConv.ofConv g) y), ?_⟩
      rw [LinearMap.rTensor_tmul, Algebra.TensorProduct.lift_tmul]
      have hx : ψ₁ (componentProj Λ p₀ j x)
          = ψ₁ t * algebraMap O L c := by
        calc ψ₁ (componentProj Λ p₀ j x)
            = ψ₁ (componentProj Λ p₀ j x * e) := by rw [map_mul, hψ₁, mul_one]
          _ = ψ₁ (c • t) := by rw [hc]
          _ = ψ₁ t * algebraMap O L c := by
            rw [map_smul, Algebra.smul_def, mul_comm]
      rw [hx]
      ring
    | add z₁ z₂ ih₁ ih₂ =>
      obtain ⟨α₁, hα₁, e₁⟩ := ih₁
      obtain ⟨α₂, hα₂, e₂⟩ := ih₂
      exact ⟨α₁ + α₂, add_mem hα₁ hα₂, by rw [map_add, map_add, e₁, e₂, mul_add]⟩
  obtain ⟨α, hα, hαeq⟩ := key (Coalgebra.comul h)
  refine ⟨α, hα, ?_⟩
  rw [← hαeq]
  exact h1

end Units

theorem blockPieces_torsor_core
    (q : ℕ) [Fact q.Prime] (k : ℕ) (Λ : Type) [AddCommGroup Λ] [DecidableEq Λ] [Fintype Λ] (hΛq : ∀ g : Λ, (q ^ k) • g = 0)
    {L : Type} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L) (hA : A.LiesOverPrime q)
    (O : Type) [CommRing O] [IsDomain O] [Algebra O L] [FaithfulSMul O L]
    (hOA : ∀ x : O, algebraMap O L x ∈ A)
    (hOdvr : IsDiscreteValuationRing O) (hOirr : Irreducible ((q : ℕ) : O))
    (HO : Type) [CommRing HO] [HopfAlgebra O HO]
    [Module.Finite O HO] [Module.Flat O HO] [Coalgebra.IsCocomm O HO]
    (p₀ : HO →ₐc[O] MonoidAlgebra O (Multiplicative Λ))
    (hsurj : Function.Surjective ⇑p₀)
    (e : HO) (hidem : IsIdempotentElem e)
    (hcard : Nat.card {ψ : WithConv (HO →ₐ[O] L) // ψ e = 1} = Fintype.card Λ) :
    (blockPiece Λ p₀ e 0 = Submodule.span O {e}) ∧
    (∀ j : Λ, ∃ t : HO, blockPiece Λ p₀ e j = Submodule.span O {t}) ∧
    (∀ i j : Λ, blockPiece Λ p₀ e (i + j) ≤
      Submodule.span O
        {z : HO | ∃ x ∈ blockPiece Λ p₀ e i, ∃ y ∈ blockPiece Λ p₀ e j, z = x * y}) ∧
    (∀ i j : Λ, ∀ x ∈ blockPiece Λ p₀ e i, ∀ y ∈ blockPiece Λ p₀ e j,
      x * y ∈ blockPiece Λ p₀ e (i + j)) ∧
    (∀ x : HO, x * e = x → x ∈ ⨆ j : Λ, blockPiece Λ p₀ e j) := by
  haveI := hOdvr
  have hq : q.Prime := Fact.out
  haveI : NeZero q := ⟨hq.ne_zero⟩

  have hqR : ¬ IsUnit ((q : ℕ) : O) := hOirr.not_isUnit
  have he0 : e ∈ gradedPiece Λ p₀ 0 :=
    isIdempotentElem_mem_gradedPiece_zero Λ p₀ hq hqR hΛq hidem

  have hne : Nat.card {ψ : WithConv (HO →ₐ[O] L) // ψ e = 1} ≠ 0 := by
    rw [hcard]
    exact Fintype.card_ne_zero
  obtain ⟨⟨ψ₁, hψ₁⟩⟩ := (Nat.card_ne_zero.mp hne).1

  have hcyc : ∀ j : Λ, ∃ t : HO, blockPiece Λ p₀ e j = Submodule.span O {t} :=
    fun j => exists_blockPiece_eq_span p₀ hOdvr hsurj hidem he0 hcard ψ₁ hψ₁ j
  have hunit : ∀ (j : Λ) (t : HO), blockPiece Λ p₀ e j = Submodule.span O {t} →
      ∃ α ∈ A, ψ₁ t * α = 1 :=
    fun j t hspan => exists_mem_mul_apply_eq_one p₀ A hOA hsurj hidem he0 ψ₁ hψ₁ j hspan
  have hint : ∀ x : HO, ψ₁ x ∈ A :=
    fun x => apply_mem_valuationSubring_of_moduleFinite A O hOA HO (WithConv.ofConv ψ₁) x

  have hunit_of : ∀ (c : O) (t u : HO), c • t = u → (∃ β ∈ A, ψ₁ u * β = 1) → IsUnit c := by
    intro c t u hcu ⟨β, hβ, hβ1⟩
    refine isUnit_of_mul_mem_eq_one q A hA O hOA hOdvr hOirr c (β := ψ₁ t * β)
      (mul_mem (hint t) hβ) ?_
    have hval : ψ₁ u = algebraMap O L c * ψ₁ t := by
      rw [← hcu, map_smul, Algebra.smul_def]
    rw [← hβ1, hval]
    ring
  refine ⟨?_, hcyc, ?_, fun i j x hx y hy => blockPiece_mul_mem p₀ i j hx hy,
    fun x hx => mem_iSup_blockPiece_of_mul_eq p₀ he0 x hx⟩
  ·
    obtain ⟨t₀, ht₀⟩ := hcyc 0
    have hemem : e ∈ blockPiece Λ p₀ e 0 :=
      (mem_blockPiece_iff Λ p₀ e 0 e).mpr ⟨he0, hidem.eq⟩
    refine le_antisymm ?_ ?_
    · rw [ht₀] at hemem ⊢
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hemem
      have hcu : IsUnit c := hunit_of c t₀ e hc ⟨1, one_mem A, by rw [hψ₁, mul_one]⟩
      obtain ⟨u, rfl⟩ := hcu
      rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      refine ⟨((u⁻¹ : (O)ˣ) : O), ?_⟩
      rw [← hc, smul_smul, Units.inv_mul, one_smul]
    · rw [Submodule.span_singleton_le_iff_mem]
      exact hemem
  ·
    intro i j
    obtain ⟨tᵢ, htᵢ⟩ := hcyc i
    obtain ⟨tⱼ, htⱼ⟩ := hcyc j
    obtain ⟨tₖ, htₖ⟩ := hcyc (i + j)
    have hprod : tᵢ * tⱼ ∈ blockPiece Λ p₀ e (i + j) :=
      blockPiece_mul_mem p₀ i j
        (by rw [htᵢ]; exact Submodule.mem_span_singleton_self tᵢ)
        (by rw [htⱼ]; exact Submodule.mem_span_singleton_self tⱼ)
    rw [htₖ] at hprod ⊢
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hprod
    obtain ⟨αᵢ, hαᵢ, hαᵢ1⟩ := hunit i tᵢ htᵢ
    obtain ⟨αⱼ, hαⱼ, hαⱼ1⟩ := hunit j tⱼ htⱼ
    have hcu : IsUnit c := hunit_of c tₖ (tᵢ * tⱼ) hc ⟨αᵢ * αⱼ, mul_mem hαᵢ hαⱼ, by
      rw [map_mul]
      calc ψ₁ tᵢ * ψ₁ tⱼ * (αᵢ * αⱼ) = (ψ₁ tᵢ * αᵢ) * (ψ₁ tⱼ * αⱼ) := by ring
        _ = 1 := by rw [hαᵢ1, hαⱼ1, one_mul]⟩
    obtain ⟨u, rfl⟩ := hcu
    rw [Submodule.span_singleton_le_iff_mem]
    have hmem : tᵢ * tⱼ ∈ Submodule.span O
        {z : HO | ∃ x ∈ blockPiece Λ p₀ e i, ∃ y ∈ blockPiece Λ p₀ e j, z = x * y} :=
      Submodule.subset_span ⟨tᵢ, by rw [htᵢ]; exact Submodule.mem_span_singleton_self tᵢ,
        tⱼ, by rw [htⱼ]; exact Submodule.mem_span_singleton_self tⱼ, rfl⟩
    have htₖeq : tₖ = ((u⁻¹ : (O)ˣ) : O) • (tᵢ * tⱼ) := by
      rw [← hc, smul_smul, Units.inv_mul, one_smul]
    rw [htₖeq]
    exact Submodule.smul_mem _ _ hmem

end S17.TorsorCoreGen

end

theorem solution
    (q : ℕ) [Fact q.Prime] (k : ℕ) (Λ : Type) [AddCommGroup Λ] [DecidableEq Λ] [Fintype Λ] (hΛq : ∀ g : Λ, (q ^ k) • g = 0)
    {L : Type} [Field L] [IsAlgClosed L] [CharZero L]
    (A : ValuationSubring L) (hA : A.LiesOverPrime q)
    (O : Type) [CommRing O] [IsDomain O] [Algebra O L] [FaithfulSMul O L]
    (hOA : ∀ x : O, algebraMap O L x ∈ A)
    (hOdvr : IsDiscreteValuationRing O) (hOirr : Irreducible ((q : ℕ) : O))
    (HO : Type) [CommRing HO] [HopfAlgebra O HO]
    [Module.Finite O HO] [Module.Flat O HO] [Coalgebra.IsCocomm O HO]
    (p₀ : HO →ₐc[O] MonoidAlgebra O (Multiplicative Λ))
    (hsurj : Function.Surjective ⇑p₀)
    (e : HO) (hidem : IsIdempotentElem e)
    (hcard : Nat.card {ψ : WithConv (HO →ₐ[O] L) // ψ e = 1} = Fintype.card Λ) :
    (HopfAlgebra.TorsorGrading.blockPiece Λ p₀ e 0 = Submodule.span O {e}) ∧
    (∀ j : Λ, ∃ t : HO, HopfAlgebra.TorsorGrading.blockPiece Λ p₀ e j = Submodule.span O {t}) ∧
    (∀ i j : Λ, HopfAlgebra.TorsorGrading.blockPiece Λ p₀ e (i + j) ≤
      Submodule.span O
        {z : HO | ∃ x ∈ HopfAlgebra.TorsorGrading.blockPiece Λ p₀ e i, ∃ y ∈ HopfAlgebra.TorsorGrading.blockPiece Λ p₀ e j, z = x * y}) ∧
    (∀ i j : Λ, ∀ x ∈ HopfAlgebra.TorsorGrading.blockPiece Λ p₀ e i, ∀ y ∈ HopfAlgebra.TorsorGrading.blockPiece Λ p₀ e j,
      x * y ∈ HopfAlgebra.TorsorGrading.blockPiece Λ p₀ e (i + j)) ∧
    (∀ x : HO, x * e = x → x ∈ ⨆ j : Λ, HopfAlgebra.TorsorGrading.blockPiece Λ p₀ e j) :=
  S17.TorsorCoreGen.blockPieces_torsor_core q k Λ hΛq A hA O hOA hOdvr hOirr HO p₀ hsurj e hidem hcard

end S_HopfAlgebra_blockPieces_torsor_core_of_isAlgClosed
end P2MW
export P2MW.S_HopfAlgebra_blockPieces_torsor_core_of_isAlgClosed (solution)
