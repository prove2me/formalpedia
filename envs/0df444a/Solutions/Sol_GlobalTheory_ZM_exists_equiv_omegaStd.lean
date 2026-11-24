-- Prove2me | solution 1 for GlobalTheory.ZM.exists_equiv_omegaStd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:19:14.175811+00:00
-- url     : https://prove2.me/submissions/c22461ac-8551-4be4-aaa7-78cedeb57223

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsEquivStdSymp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsEquivOmegaStd
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk


section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory.ZM
private theorem omegaStd_single_single_eq_stdSymp {g : ℕ} (a b : Fin g ⊕ Fin g) :
    omegaStd (Pi.single a (1 : ℤ)) (Pi.single b 1) =
      Out.stdSymp g (finCongr (two_mul g).symm (finSumFinEquiv a))
        (finCongr (two_mul g).symm (finSumFinEquiv b)) := by
  unfold Out.stdSymp omegaStd
  rcases a with i | i <;> rcases b with j | j <;>
    simp only [Pi.single_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, mul_zero, zero_mul,
      sub_zero, zero_sub, mul_ite, ite_mul, mul_one, one_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.sum_const_zero, Finset.sum_neg_distrib] <;>
    simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, finCongr_apply, Fin.coe_cast,
      Fin.coe_castAdd, Fin.coe_natAdd, Fin.ext_iff] <;>
    split_ifs <;> omega
end GlobalTheory.ZM
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM
namespace GlobalTheory.ZM
theorem _root_.solution {M : Type} [AddCommGroup M] (B : LinearMap.BilinForm ℤ M) {g : ℕ}
    (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] M)
    (h : ∀ i j, B (bas (Pi.single i 1)) (bas (Pi.single j 1)) = Out.stdSymp g i j) :
    ∃ bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] M, ∀ x y, B (bas' x) (bas' y) = omegaStd x y := by
  set e : Fin g ⊕ Fin g ≃ Fin (2 * g) := finSumFinEquiv.trans (finCongr (two_mul g).symm) with he
  refine ⟨(LinearEquiv.funCongrLeft ℤ ℤ e.symm).trans bas, ?_⟩
  have hs : ∀ a, (LinearEquiv.funCongrLeft ℤ ℤ e.symm) (Pi.single a (1 : ℤ)) = Pi.single (e a) 1 := by
    intro a
    funext k
    simp [LinearEquiv.funCongrLeft_apply, Pi.single_apply, Equiv.symm_apply_eq]
  let Ω : LinearMap.BilinForm ℤ (Fin g ⊕ Fin g → ℤ) :=
    LinearMap.mk₂ ℤ omegaStd
      (fun a a' b => by simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; ext; ring)
      (fun c a b => by simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; ext; ring)
      (fun a b b' => by simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; ext; ring)
      (fun c a b => by simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; ext; ring)
  have hB : B.compl₁₂ ((LinearEquiv.funCongrLeft ℤ ℤ e.symm).trans bas).toLinearMap
      ((LinearEquiv.funCongrLeft ℤ ℤ e.symm).trans bas).toLinearMap = Ω := by
    refine LinearMap.ext_basis (Pi.basisFun ℤ _) (Pi.basisFun ℤ _) fun a b => ?_
    simp only [Pi.basisFun_apply, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply, hs, h,
      Ω, LinearMap.mk₂_apply]
    exact (omegaStd_single_single_eq_stdSymp a b).symm
  intro x y
  exact LinearMap.congr_fun₂ hB x y
end GlobalTheory.ZM
