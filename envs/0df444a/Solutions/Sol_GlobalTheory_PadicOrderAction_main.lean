-- Prove2me | solution 1 for GlobalTheory.PadicOrderAction.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:17:04.014217+00:00
-- url     : https://prove2.me/submissions/aa75227a-58f6-4f47-9b85-51b48d942337

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PadicEndApply
import Theorems.Thm_GlobalTheory_PadicOrderAction_complEnd_tmul
import Theorems.Thm_GlobalTheory_PadicOrderAction_complMat_tmul
import Theorems.Thm_GlobalTheory_PadicOrderAction_padic_mul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.PadicOrderAction
variable {R₀ : Type} [CommRing R₀]
namespace GlobalTheory.PadicOrderAction
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} (B : BX R₀) (O : LAlg R₀) (gb : Module.Basis (Fin g) R₀ B.gg) (O₀ : Type) [CommRing O₀] (f : O₀ → OEnd B O) (p : ℕ) [Fact p.Prime] [Algebra ℤ_[p] (O : Type)] (dL : O₀ →+* Matrix (Fin g) (Fin g) (O : Type)),
    Function.Surjective (algebraMap R₀ (O : Type)) → (∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R), (f 1).f s x = x ∧ ∀ a b, (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧
      (f (a * b)).f s x = (f a).f s ((f b).f s x)) →
    (∀ a {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker),
      (∀ k, (m k : (R : Type)) = s.1 (dL a k l) * i) →
      (f a).f s (B.tg π hπ (gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] m k)) →
    ∃ (A : OAct B O p (ℤ_[p] ⊗[ℤ] O₀)) (ρL : ℤ_[p] ⊗[ℤ] O₀ →+* Matrix (Fin g) (Fin g) (O : Type)),
      (∀ c a, ρL (c ⊗ₜ[ℤ] a) = algebraMap ℤ_[p] (O : Type) c • dL a) ∧
      (∀ a k l, ρL a k l = algebraMap R₀ (O : Type) (gb.repr (A.actL a (gb l)) k)) ∧
      ∀ c a (S : LAlg R₀) (s : LHom O S) (x : torP B p S), (A.act (c ⊗ₜ[ℤ] a) S s x : B.G S) = (PadicInt.toZMod c).val • (f a).f s x) := by
  intro R₀ _ g B O gb O₀ _ f p _ _ dL hs hf htg
  choose pre hpre using hs
  let L : ℤ_[p] ⊗[ℤ] O₀ → B.gg →ₗ[R₀] B.gg := fun a =>
    gb.constr R₀ fun l => ∑ k, pre (complMat p dL a k l) • gb k
  have hL : ∀ a l, L a (gb l) = ∑ k, pre (complMat p dL a k l) • gb k := fun a l =>
    gb.constr_basis R₀ _ l
  have key : ∀ a {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g)
      (i : π.ker) (hi : p • i = 0),
      (complEnd f p s (hf s) a ⟨B.tg π hπ (gb l ⊗ₜ i), tg_torP B p π hπ _ i hi⟩ : B.G R) =
        B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] kerMul π (s.1 (complMat p dL a k l)) i) := by
    intro a R S s π hπ l i hi
    induction a using TensorProduct.induction_on with
    | zero =>
      have : ∀ k, kerMul π (s.1 (complMat p dL 0 k l)) i = 0 := fun k =>
        Subtype.ext (by simp [kerMul])
      simp only [this]
      simp only [TensorProduct.tmul_zero, Finset.sum_const_zero, map_zero]
      rfl
    | tmul c a =>
      rw [complEnd_tmul]
      change _ • (f a).f s (B.tg π hπ (gb l ⊗ₜ i)) = _
      rw [htg a s π hπ l i (fun k => kerMul π (s.1 (dL a k l)) i) (fun k => rfl), ← map_nsmul,
        Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      refine (map_nsmul (TensorProduct.mk R₀ B.gg π.ker (gb k)) _ _).symm.trans ?_
      change gb k ⊗ₜ[R₀] _ = _
      congr 1
      apply Subtype.ext
      have hi' : p • (i : (R : Type)) = 0 := congrArg Subtype.val hi
      have h2 := padic_mul_eq (s.1.toRingHom.comp (algebraMap ℤ_[p] (O : Type))) c
        (s.1 (dL a k l) * i) (by rw [← mul_smul_comm, hi', mul_zero])
      change (PadicInt.toZMod c).val • (s.1 (dL a k l) * i) = s.1 (complMat p dL (c ⊗ₜ a) k l) * i
      rw [← h2, complMat_tmul, Matrix.smul_apply, smul_eq_mul, map_mul, _root_.mul_assoc]
      rfl
    | add a b ha hb =>
      have : ∀ k, kerMul π (s.1 (complMat p dL (a + b) k l)) i =
          kerMul π (s.1 (complMat p dL a k l)) i + kerMul π (s.1 (complMat p dL b k l)) i :=
        fun k => Subtype.ext (by simp [kerMul, add_mul])
      simp only [this, TensorProduct.tmul_add, Finset.sum_add_distrib]
      rw [map_add (B.tg π hπ), ← ha, ← hb, map_add]
      rfl
  have key2 : ∀ a {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g)
      (i : π.ker) (hi : p • i = 0),
      (complEnd f p s (hf s) a ⟨B.tg π hπ (gb l ⊗ₜ i), tg_torP B p π hπ _ i hi⟩ : B.G R) =
        B.tg π hπ (L a (gb l) ⊗ₜ[R₀] i) := by
    intro a R S s π hπ l i hi
    rw [key a s π hπ l i hi, hL, TensorProduct.sum_tmul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.smul_tmul]
    congr 1
    apply Subtype.ext
    change s.1 (complMat p dL a k l) * i = pre (complMat p dL a k l) • (i : (R : Type))
    rw [Algebra.smul_def, ← s.1.commutes, hpre]
  refine ⟨{ act := fun a S s => complEnd f p s (hf s) a
            act_one := fun S s x => by rw [map_one]; rfl
            act_mul := fun a b S s x => by rw [map_mul]; rfl
            act_add := fun a b S s x => by rw [map_add]; rfl
            act_nat := ?_
            actL := L
            act_tg := ?_ }, complMat p dL, complMat_tmul p dL, ?_,
            fun c a S s x => complEnd_tmul f p s (hf s) c a x⟩
  · intro a S S' s s' φ hφ x
    subst hφ
    change B.map φ (complEnd f p s (hf s) a x : B.G S) =
      (complEnd f p (φ.comp s) (hf _) a ⟨B.map φ x, map_torP B p φ x⟩ : B.G S')
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul c a => rw [complEnd_tmul, complEnd_tmul, map_nsmul, (f a).nat]
    | add a b ha hb =>
      rw [map_add, map_add]
      change B.map φ ((complEnd f p s (hf s) a x : B.G S) + (complEnd f p s (hf s) b x : B.G S)) = _
      rw [map_add, ha, hb]
      rfl
  · intro a R S s π hπ w i hi
    have hr : ∀ l, p • (gb.repr w l • i) = 0 := fun l => by rw [smul_comm, hi, smul_zero]
    have h1 : (⟨B.tg π hπ (w ⊗ₜ i), tg_torP B p π hπ w i hi⟩ : torP B p R) =
        ∑ l, ⟨B.tg π hπ (gb l ⊗ₜ (gb.repr w l • i)), tg_torP B p π hπ _ _ (hr l)⟩ := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finset_sum]
      change B.tg π hπ (w ⊗ₜ i) = ∑ l, B.tg π hπ (gb l ⊗ₜ (gb.repr w l • i))
      rw [← map_sum]
      congr 1
      conv_lhs => rw [← gb.sum_repr w, TensorProduct.sum_tmul]
      exact Finset.sum_congr rfl fun l _ => TensorProduct.smul_tmul _ _ _
    change (complEnd f p s (hf s) a ⟨B.tg π hπ (w ⊗ₜ i), tg_torP B p π hπ w i hi⟩ : B.G R) = _
    rw [h1, map_sum, AddSubmonoidClass.coe_finset_sum,
      Finset.sum_congr rfl fun l _ => key2 a s π hπ l _ (hr l), ← map_sum]
    congr 1
    conv_rhs => rw [← gb.sum_repr w, map_sum, TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl fun l _ => by rw [map_smul, TensorProduct.smul_tmul]
  · intro a k l
    change complMat p dL a k l = algebraMap R₀ (O : Type) (gb.repr (L a (gb l)) k)
    rw [hL, gb.repr_sum_self, hpre]
end GlobalTheory.PadicOrderAction
