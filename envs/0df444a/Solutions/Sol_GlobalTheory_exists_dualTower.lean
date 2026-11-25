-- Prove2me | solution 1 for GlobalTheory.exists_dualTower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:00:39.685673+00:00
-- url     : https://prove2.me/submissions/d65a0dba-6674-4220-a419-7b849a9bd932

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_IsFibreSq
import Definitions.Def_ReciprocityTheory_DualLattices_DualPairInh
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DualTowerMapExists
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair_____9b8197f73975

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace GlobalTheory
section Helpers
open ReciprocityTheory.PGsh
private lemma dualTowerRing_C {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) (r : (Λ : Type)) :
    dualTowerRing Dq ψ (Ideal.Quotient.mk _ (Polynomial.C r)) = Dq.σ.1 (ψ.1 r) := by
  rw [dualTowerRing, Ideal.Quotient.lift_mk, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  rfl
private lemma dualTowerRing_X {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) : dualTowerRing Dq ψ (DualNum.eta Λ) = Dq.η := by
  rw [dualTowerRing, DualNum.eta, Ideal.Quotient.lift_mk, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X]
private lemma dualTowerRing_π {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) (x : DualNum.DN Λ) :
    Dq.π.1 (dualTowerRing Dq ψ x) = ψ.1 (DualNum.ev Λ x) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction f using Polynomial.induction_on with
  | C a => rw [dualTowerRing_C, Dq.sect, DualNum.ev_mk, Polynomial.eval_C]
  | add f g hf hg => simp only [map_add, hf, hg]
  | monomial n a _ =>
    have h := dualTowerRing_X Dq ψ
    rw [DualNum.eta] at h
    rw [DualNum.ev_mk, pow_succ Polynomial.X n, ← mul_assoc, map_mul, map_mul, h, map_mul, Dq.π_η]
    simp
private lemma dualTower_map_exists {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) :
    ∃ f : LHom (DualNum.dualPair Λ).D Dq.D,
      (∀ x, Dq.π.1 (f.1 x) = ψ.1 ((DualNum.dualPair Λ).π.1 x)) ∧
      (∀ x, f.1 ((DualNum.dualPair Λ).σ.1 x) = Dq.σ.1 (ψ.1 x)) ∧
      f.1 (DualNum.dualPair Λ).η = Dq.η := by
  let fA : DualNum.DN Λ →ₐ[R₀] (Dq.D : Type) :=
    { dualTowerRing Dq ψ with
      commutes' := fun r => by
        show dualTowerRing Dq ψ (algebraMap R₀ (DualNum.DN Λ) r) = _
        rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_apply, dualTowerRing_C,
          AlgHom.commutes, AlgHom.commutes] }
  refine ⟨mkLHom (R := (DualNum.dualPair Λ).D) fA fun a ha => ?_, fun x => dualTowerRing_π Dq ψ x,
    fun x => ?_, dualTowerRing_X Dq ψ⟩
  · refine (DualNum.dualPair Λ).isUnit_of_π ?_
    have h1 : IsUnit (Dq.π.1 (dualTowerRing Dq ψ a)) := ha.map Dq.π.1
    exact ψ.2.map_nonunit _ ((dualTowerRing_π Dq ψ a) ▸ h1)
  · show dualTowerRing Dq ψ (algebraMap (Λ : Type) (DualNum.DN Λ) x) = _
    rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_apply, dualTowerRing_C]
    rfl
private lemma dualTower_nonempty {R₀ : Type} [CommRing R₀] {p : ℕ} (Tw : ATowerL R₀ p) :
    Nonempty (DualTower Tw) := by
  choose d h₁ h₂ h₃ using fun n => dualTower_map_exists (DualNum.dualPair (Tw.R n)) (Tw.r n)
  exact ⟨⟨fun n => DualNum.dualPair (Tw.R n), d, h₁, h₂, h₃⟩⟩
end Helpers
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
end GlobalTheory
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} (Tw : ATowerL R₀ p), Nonempty (DualTower Tw)) :=
  fun Tw => dualTower_nonempty Tw
end GlobalTheory
