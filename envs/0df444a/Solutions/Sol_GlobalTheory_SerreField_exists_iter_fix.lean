-- Prove2me | solution 1 for GlobalTheory.SerreField.exists_iter_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:45:41.899855+00:00
-- url     : https://prove2.me/submissions/f00dc302-1456-4919-a9f1-309bd1044d03

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulPullOfCubeOfSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsOddNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SerreField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.MulPull
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]
variable {A}
namespace GlobalTheory.SerreField
theorem _root_.solution (σ : A ≅ A) [IsMonHom σ.hom] (T : Over S) (n : ℕ)
    [Finite {x : T ⟶ A // x ^ n = 1}] :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ x : T ⟶ A, x ^ n = 1 → x ≫ (iter σ m).hom = x := by
  let f : {x : T ⟶ A // x ^ n = 1} → {x : T ⟶ A // x ^ n = 1} := fun x =>
    ⟨x.1 ≫ σ.hom, by rw [← MonObj.pow_comp, x.2, MonObj.one_comp]⟩
  have hf : Function.Injective f := fun x y h =>
    Subtype.ext ((cancel_mono σ.hom).1 (congrArg Subtype.val h))
  let e : Equiv.Perm {x : T ⟶ A // x ^ n = 1} := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
  have he : ∀ (m : ℕ) x, ((e ^ m) x).1 = x.1 ≫ (iter σ m).hom := by
    intro m
    induction m with
    | zero => intro x; simp [iter]
    | succ m ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply]
      change ((e ^ m) x).1 ≫ σ.hom = _
      rw [ih, iter, Iso.trans_hom, Category.assoc]
  refine ⟨orderOf e, (orderOf_pos e).ne', fun x hx => ?_⟩
  have := he (orderOf e) ⟨x, hx⟩
  rw [pow_orderOf_eq_one] at this
  exact this.symm
end GlobalTheory.SerreField
