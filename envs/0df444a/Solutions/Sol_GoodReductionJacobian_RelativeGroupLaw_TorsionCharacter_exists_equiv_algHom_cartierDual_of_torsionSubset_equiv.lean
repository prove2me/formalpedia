-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.TorsionCharacter.exists_equiv_algHom_cartierDual_of_torsionSubset_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/2ca2708d-0086-56ef-9717-67732de9a636

import Mathlib
import Definitions.Def_AlgebraicGeometry_TorsionCharacter
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_TorsionCharacter_exists_equiv_algHom_cartierDual_of_torsionSubset_equiv

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

open TensorProduct

namespace CharYonedaAux

variable (R : Type u) [CommRing R] (H : Type u) [CommRing H] [HopfAlgebra R H]
  [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H]
  (R' : Type u) [CommRing R'] [Algebra R R']

noncomputable def evalC : H ≃ₗ[R] Module.Dual R (CartierDual R H) :=
  (Module.evalEquiv R H).trans (CartierDual.toDual R H).dualMap

@[scoped simp] theorem evalC_apply (h : H) (δ : CartierDual R H) : evalC R H h δ = δ h := rfl

noncomputable def Φ : R' ⊗[R] H ≃ₗ[R] (CartierDual R H →ₗ[R] R') :=
  (TensorProduct.comm R R' H).trans
    ((TensorProduct.congr (evalC R H) (LinearEquiv.refl R R')).trans (dualTensorHomEquiv R (CartierDual R H) R'))

@[scoped simp] theorem Φ_tmul (r' : R') (h : H) (δ : CartierDual R H) : Φ R H R' (r' ⊗ₜ[R] h) δ = δ h • r' := by
  simp [Φ, dualTensorHomEquiv, dualTensorHom_apply]

noncomputable def pair₂ (δ₁ δ₂ : CartierDual R H) : R' ⊗[R] (H ⊗[R] H) →ₗ[R] R' :=
  (TensorProduct.rid R R').toLinearMap ∘ₗ
    LinearMap.lTensor R' (TensorProduct.lift (LinearMap.mk₂ R (fun a b => δ₁ a * δ₂ b)
      (fun a a' b => by simp [add_mul]) (fun c a b => by simp [mul_assoc])
      (fun a b b' => by simp [mul_add]) (fun c a b => by simp [mul_left_comm])))

@[scoped simp] theorem pair₂_tmul (δ₁ δ₂ : CartierDual R H) (r' : R') (a b : H) :
    pair₂ R H R' δ₁ δ₂ (r' ⊗ₜ[R] (a ⊗ₜ[R] b)) = (δ₁ a * δ₂ b) • r' := by
  simp [pair₂, TensorProduct.rid_tmul]

def IsGrouplike (u : R' ⊗[R] H) : Prop :=
  LinearMap.lTensor R' (Coalgebra.comul (R := R) (A := H)) u =
      Algebra.TensorProduct.map (AlgHom.id R R') (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H) u *
        Algebra.TensorProduct.map (AlgHom.id R R') (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H) u ∧
    LinearMap.lTensor R' (Coalgebra.counit (R := R) (A := H)) u = (1 : R') ⊗ₜ[R] (1 : R)

theorem Φ_mul (u : R' ⊗[R] H) (δ₁ δ₂ : CartierDual R H) :
    Φ R H R' u (δ₁ * δ₂) = pair₂ R H R' δ₁ δ₂ (LinearMap.lTensor R' (Coalgebra.comul (R := R) (A := H)) u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul r' h =>
    rw [Φ_tmul, LinearMap.lTensor_tmul, CartierDual.mul_apply]

    induction (Coalgebra.comul (R := R) h) using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [TensorProduct.dualDistrib_apply]
    | add x y hx hy => simp only [map_add, tmul_add, add_smul] at hx hy ⊢; rw [hx, hy]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

theorem pair₂_mul_includes (u : R' ⊗[R] H) (δ₁ δ₂ : CartierDual R H) :
    pair₂ R H R' δ₁ δ₂
      (Algebra.TensorProduct.map (AlgHom.id R R') (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H) u *
        Algebra.TensorProduct.map (AlgHom.id R R') (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H) u) =
      Φ R H R' u δ₁ * Φ R H R' u δ₂ := by

  suffices h : ∀ v w : R' ⊗[R] H, pair₂ R H R' δ₁ δ₂
      (Algebra.TensorProduct.map (AlgHom.id R R') (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H) v *
        Algebra.TensorProduct.map (AlgHom.id R R') (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H) w) =
      Φ R H R' v δ₁ * Φ R H R' w δ₂ from h u u
  intro v w
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul s b =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
        pair₂_tmul, Φ_tmul]
      simp only [Algebra.smul_def, map_mul]
      ring
    | add x y hx hy => simp only [map_add, mul_add, LinearMap.add_apply, hx, hy]
  | add x y hx hy => simp only [map_add, add_mul, LinearMap.add_apply, hx, hy]

theorem Φ_one (u : R' ⊗[R] H) :
    Φ R H R' u 1 = TensorProduct.rid R R' (LinearMap.lTensor R' (Coalgebra.counit (R := R) (A := H)) u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul r' h => simp [CartierDual.one_apply]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

noncomputable def algHomOfGrouplike (u : R' ⊗[R] H) (hu : IsGrouplike R H R' u) : CartierDual R H →ₐ[R] R' :=
  AlgHom.ofLinearMap (Φ R H R' u)
    ((Φ_one R H R' u).trans (by rw [hu.2]; simp))
    (fun δ₁ δ₂ => (Φ_mul R H R' u δ₁ δ₂).trans (by rw [hu.1]; exact pair₂_mul_includes R H R' u δ₁ δ₂))

section Generic

variable (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M]

noncomputable def ΦM : R' ⊗[R] M ≃ₗ[R] (Module.Dual R M →ₗ[R] R') :=
  (TensorProduct.comm R R' M).trans
    ((TensorProduct.congr (Module.evalEquiv R M) (LinearEquiv.refl R R')).trans (dualTensorHomEquiv R (Module.Dual R M) R'))

@[scoped simp] theorem ΦM_tmul (r' : R') (m : M) (θ : Module.Dual R M) : ΦM R R' M (r' ⊗ₜ[R] m) θ = θ m • r' := by
  simp [ΦM, dualTensorHomEquiv, dualTensorHom_apply]

theorem eq_zero_of_forall_ΦM_eq_zero (w : R' ⊗[R] M) (h : ∀ θ : Module.Dual R M, ΦM R R' M w θ = 0) : w = 0 := by
  have : ΦM R R' M w = 0 := LinearMap.ext h
  simpa using this

end Generic

theorem pair₂_eq_ΦM (δ₁ δ₂ : CartierDual R H) (w : R' ⊗[R] (H ⊗[R] H)) :
    pair₂ R H R' δ₁ δ₂ w =
      ΦM R R' (H ⊗[R] H) w (TensorProduct.dualDistrib R H H (CartierDual.toDual R H δ₁ ⊗ₜ[R] CartierDual.toDual R H δ₂)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul r' x =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [TensorProduct.dualDistrib_apply]
    | add x y hx hy => simp only [tmul_add, map_add, LinearMap.add_apply] at hx hy ⊢; rw [hx, hy]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

theorem eq_zero_of_forall_pair₂_eq_zero (w : R' ⊗[R] (H ⊗[R] H)) (h : ∀ δ₁ δ₂ : CartierDual R H, pair₂ R H R' δ₁ δ₂ w = 0) :
    w = 0 := by
  apply eq_zero_of_forall_ΦM_eq_zero R R' (H ⊗[R] H)
  intro θ

  obtain ⟨t, rfl⟩ := (TensorProduct.dualDistribEquiv R H H).surjective θ
  induction t using TensorProduct.induction_on with
  | zero => rw [LinearEquiv.map_zero, LinearMap.map_zero]
  | tmul f g =>
    have := h (CartierDual.ofDual R H f) (CartierDual.ofDual R H g)
    rw [pair₂_eq_ΦM] at this
    simp [TensorProduct.dualDistribEquiv] at this
    exact this
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

theorem isGrouplike_symm_of_algHom (ψ : CartierDual R H →ₐ[R] R') :
    IsGrouplike R H R' ((Φ R H R').symm ψ.toLinearMap) := by
  set u := (Φ R H R').symm ψ.toLinearMap with hu
  have hΦu : Φ R H R' u = ψ.toLinearMap := (Φ R H R').apply_symm_apply _
  constructor
  ·
    rw [← sub_eq_zero]
    apply eq_zero_of_forall_pair₂_eq_zero
    intro δ₁ δ₂
    rw [map_sub, sub_eq_zero, ← Φ_mul, pair₂_mul_includes, hΦu]
    exact congrArg (fun x => x) (map_mul ψ δ₁ δ₂)
  ·
    have h1 : Φ R H R' u 1 = 1 := by rw [hΦu]; exact map_one ψ
    rw [Φ_one] at h1
    apply (TensorProduct.rid R R').injective
    rw [h1, TensorProduct.rid_tmul, one_smul]

noncomputable def grouplikeEquiv : {u : R' ⊗[R] H // IsGrouplike R H R' u} ≃ (CartierDual R H →ₐ[R] R') where
  toFun u := algHomOfGrouplike R H R' u.1 u.2
  invFun ψ := ⟨(Φ R H R').symm ψ.toLinearMap, isGrouplike_symm_of_algHom R H R' ψ⟩
  left_inv u := by
    apply Subtype.ext
    show (Φ R H R').symm (algHomOfGrouplike R H R' u.1 u.2).toLinearMap = u.1
    have : (algHomOfGrouplike R H R' u.1 u.2).toLinearMap = Φ R H R' u.1 := rfl
    rw [this, LinearEquiv.symm_apply_apply]
  right_inv ψ := by
    apply AlgHom.toLinearMap_injective
    show Φ R H R' ((Φ R H R').symm ψ.toLinearMap) = ψ.toLinearMap
    exact (Φ R H R').apply_symm_apply _

theorem grouplikeEquiv_apply (u : {u : R' ⊗[R] H // IsGrouplike R H R' u}) (δ : CartierDual R H) :
    grouplikeEquiv R H R' u δ = Φ R H R' u.1 δ := rfl

theorem Φ_map {R'' : Type u} [CommRing R''] [Algebra R R''] (g : R' →ₐ[R] R'') (u : R' ⊗[R] H) (δ : CartierDual R H) :
    Φ R H R'' (Algebra.TensorProduct.map g (AlgHom.id R H) u) δ = g (Φ R H R' u δ) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul r' h => simp [Algebra.smul_def]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

theorem cd_add_apply (α β : CartierDual R H) (h : H) : (α + β) h = α h + β h := by
  show CartierDual.toDual R H (α + β) h = _
  rw [map_add]; rfl

theorem cd_smul_apply (c : R) (α : CartierDual R H) (h : H) : (c • α) h = c * α h := by
  show CartierDual.toDual R H (c • α) h = _
  rw [map_smul]; rfl

noncomputable def evPair (h k : H) : CartierDual R H ⊗[R] CartierDual R H →ₗ[R] R :=
  TensorProduct.lift (LinearMap.mk₂ R (fun α β : CartierDual R H => α h * β k)
    (fun _ _ _ => by simp only [cd_add_apply, add_mul]) (fun _ _ _ => by simp only [cd_smul_apply, smul_eq_mul, mul_assoc])
    (fun _ _ _ => by simp only [cd_add_apply, mul_add]) (fun _ _ _ => by simp only [cd_smul_apply, smul_eq_mul, mul_left_comm]))

@[scoped simp] theorem evPair_tmul (h k : H) (α β : CartierDual R H) : evPair R H h k (α ⊗ₜ[R] β) = α h * β k := by
  simp [evPair]

theorem evPair_eq_dualDistrib (h k : H) (w : CartierDual R H ⊗[R] CartierDual R H) :
    evPair R H h k w =
      TensorProduct.dualDistrib R H H
        (TensorProduct.map (CartierDual.toDual R H).toLinearMap (CartierDual.toDual R H).toLinearMap w) (h ⊗ₜ[R] k) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul α β => simp [TensorProduct.dualDistrib_apply]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

theorem evPair_comul (h k : H) (δ : CartierDual R H) :
    evPair R H h k (Coalgebra.comul (R := R) δ) = δ (h * k) := by
  rw [evPair_eq_dualDistrib]
  exact CartierDual.comul_pairing δ h k

theorem Φ_ringMul (u v : R' ⊗[R] H) (δ : CartierDual R H) :
    Φ R H R' (u * v) δ =
      LinearMap.mul' R R' (TensorProduct.map (Φ R H R' u) (Φ R H R' v) (Coalgebra.comul (R := R) δ)) := by

  have key : ∀ (r s : R') (h k : H) (w : CartierDual R H ⊗[R] CartierDual R H),
      LinearMap.mul' R R' (TensorProduct.map (Φ R H R' (r ⊗ₜ[R] h)) (Φ R H R' (s ⊗ₜ[R] k)) w) =
        evPair R H h k w • (r * s) := by
    intro r s h k w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul α β =>
      simp only [TensorProduct.map_tmul, Φ_tmul, LinearMap.mul'_apply, evPair_tmul]
      simp only [Algebra.smul_def, map_mul]; ring
    | add x y hx hy => simp only [map_add, hx, hy, add_smul]
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul r h =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul s k =>
      rw [key, evPair_comul, Algebra.TensorProduct.tmul_mul_tmul, Φ_tmul]
    | add x y hx hy => rw [mul_add, map_add, LinearMap.add_apply, hx, hy, map_add, TensorProduct.map_add_right, LinearMap.add_apply, map_add]
  | add x y hx hy => rw [add_mul, map_add, LinearMap.add_apply, hx, hy, map_add, TensorProduct.map_add_left, LinearMap.add_apply, map_add]

section LayerU

variable {T : Type u} [CommRing T] [Algebra R T]

noncomputable def eval₂ (a : R' →ₐ[R] T) (φ₁ φ₂ : H →ₐ[R] T) : R' ⊗[R] (H ⊗[R] H) →ₐ[R] T :=
  Algebra.TensorProduct.lift a (Algebra.TensorProduct.lift φ₁ φ₂ (fun _ _ => Commute.all _ _)) (fun _ _ => Commute.all _ _)

theorem eval₂_comp_map_includeLeft (a : R' →ₐ[R] T) (φ₁ φ₂ : H →ₐ[R] T) :
    (eval₂ R H R' a φ₁ φ₂).comp
        (Algebra.TensorProduct.map (AlgHom.id R R') (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H)) =
      Algebra.TensorProduct.lift a φ₁ (fun _ _ => Commute.all _ _) := by
  ext r <;> simp [eval₂]

theorem eval₂_comp_map_includeRight (a : R' →ₐ[R] T) (φ₁ φ₂ : H →ₐ[R] T) :
    (eval₂ R H R' a φ₁ φ₂).comp
        (Algebra.TensorProduct.map (AlgHom.id R R') (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H)) =
      Algebra.TensorProduct.lift a φ₂ (fun _ _ => Commute.all _ _) := by
  ext r <;> simp [eval₂]

theorem eval₂_lTensor_comul (a : R' →ₐ[R] T) (φ₁ φ₂ : H →ₐ[R] T) (u : R' ⊗[R] H) :
    eval₂ R H R' a φ₁ φ₂ (LinearMap.lTensor R' (Coalgebra.comul (R := R) (A := H)) u) =
      Algebra.TensorProduct.lift a (WithConv.toConv φ₁ * WithConv.toConv φ₂).ofConv (fun _ _ => Commute.all _ _) u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul r h =>
    rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.lift_tmul]
    simp only [eval₂, Algebra.TensorProduct.lift_tmul]
    congr 1

    rw [AlgHom.convMul_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem eval_mul_of_isGrouplike (u : R' ⊗[R] H) (hu : IsGrouplike R H R' u) (a : R' →ₐ[R] T) (φ₁ φ₂ : H →ₐ[R] T) :
    Algebra.TensorProduct.lift a (WithConv.toConv φ₁ * WithConv.toConv φ₂).ofConv (fun _ _ => Commute.all _ _) u =
      Algebra.TensorProduct.lift a φ₁ (fun _ _ => Commute.all _ _) u *
        Algebra.TensorProduct.lift a φ₂ (fun _ _ => Commute.all _ _) u := by
  rw [← eval₂_lTensor_comul, hu.1, map_mul, ← AlgHom.comp_apply, eval₂_comp_map_includeLeft, ← AlgHom.comp_apply,
    eval₂_comp_map_includeRight]

theorem eval_one_of_isGrouplike (u : R' ⊗[R] H) (hu : IsGrouplike R H R' u) (a : R' →ₐ[R] T) :
    Algebra.TensorProduct.lift a (1 : WithConv (H →ₐ[R] T)).ofConv (fun _ _ => Commute.all _ _) u = 1 := by

  have key : ∀ v : R' ⊗[R] H, Algebra.TensorProduct.lift a (1 : WithConv (H →ₐ[R] T)).ofConv (fun _ _ => Commute.all _ _) v =
      Algebra.TensorProduct.lift a (Algebra.ofId R T) (fun _ _ => Commute.all _ _)
        (LinearMap.lTensor R' (Coalgebra.counit (R := R) (A := H)) v) := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul r h =>
      rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
      congr 1
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [key, hu.2, Algebra.TensorProduct.lift_tmul, map_one, map_one, mul_one]

end LayerU

end CharYonedaAux
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_TorsionCharacter_exists_equiv_algHom_cartierDual_of_torsionSubset_equiv.CharYonedaAux"

namespace CharYonedaY

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}

def castPt {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of S)} (h : t = t') (x : SchemeHomOver t f) :
    SchemeHomOver t' f := ⟨x.1, x.2.trans (by rw [h])⟩

@[scoped simp] theorem castPt_val {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of S)} (h : t = t') (x : SchemeHomOver t f) :
    (castPt h x).1 = x.1 := rfl

theorem castPt_eq_rec {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of S)} (h : t = t') (x : SchemeHomOver t f) :
    castPt h x = h ▸ x := by cases h; rfl

theorem isTorsionPoint_castPt (L : RelativeGroupLaw S f) (n : ℕ) {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of S)}
    (h : t = t') (x : SchemeHomOver t f) : L.IsTorsionPoint t' n (castPt h x) ↔ L.IsTorsionPoint t n x := by
  cases h; rfl

theorem mul_castPt (L : RelativeGroupLaw S f) {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of S)}
    (h : t = t') (x y : SchemeHomOver t f) : L.mul t' (castPt h x) (castPt h y) = castPt h (L.mul t x y) := by
  cases h; rfl

theorem base_eq {R : Type u} [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (R' : Type u) [CommRing R'] [Algebra R R'] (T : Type u) [CommRing T] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T] :
    Spec.map (CommRingCat.ofHom (algebraMap R T)) ≫ ι =
      Spec.map (CommRingCat.ofHom (algebraMap R' T)) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι) := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq R R' T]

section Main

variable (L : RelativeGroupLaw S f) (n : ℕ) {R : Type u} [CommRing R]
  (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
  (H : Type u) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H]
  (e : ∀ (T : Type u) [CommRing T] [Algebra R T],
    WithConv (H →ₐ[R] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T)) ≫ ι) n)
  (R' : Type u) [CommRing R'] [Algebra R R']

noncomputable def pt (T : Type u) [CommRing T] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T] (φ : H →ₐ[R] T) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R' T)) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) f :=
  castPt (base_eq ι R' T) (e T (WithConv.toConv φ)).val

theorem pt_fst (T : Type u) [CommRing T] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T] (φ : H →ₐ[R] T) :
    (pt L n ι H e R' T φ).1 = (e T (WithConv.toConv φ)).val.1 := rfl

theorem pt_tors (T : Type u) [CommRing T] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T] (φ : H →ₐ[R] T) :
    L.IsTorsionPoint _ n (pt L n ι H e R' T φ) :=
  (isTorsionPoint_castPt L n (base_eq ι R' T) _).mpr (e T (WithConv.toConv φ)).property

noncomputable def valAt (χ : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι))
    (T : Type u) [CommRing T] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T] (φ : H →ₐ[R] T) : Tˣ :=
  χ.val T (Spec.map (CommRingCat.ofHom (algebraMap R' T))) (pt L n ι H e R' T φ) (pt_tors L n ι H e R' T φ)

theorem valAt_map
    (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
        (g : T →ₐ[R] T') (φ : WithConv (H →ₐ[R] T)),
      ((e T' (.toConv (g.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (e T φ).val.1)
    (χ : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι))
    (T T' : Type u) [CommRing T] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T]
    [CommRing T'] [Algebra R T'] [Algebra R' T'] [IsScalarTower R R' T']
    (g : T →ₐ[R] T') (hg : g.toRingHom.comp (algebraMap R' T) = algebraMap R' T') (φ : H →ₐ[R] T) :
    valAt L n ι H e R' χ T' (g.comp φ) = Units.map (g : T →* T') (valAt L n ι H e R' χ T φ) := by
  unfold valAt
  refine χ.val_natural T T' _ _ g.toRingHom ?_ _ _ _ _ ?_
  · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hg]
  · rw [pt_fst, pt_fst]
    exact he_nat T T' g (WithConv.toConv φ)

variable
  (he_mul : ∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (H →ₐ[R] T)),
    ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val)
  (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
      (g : T →ₐ[R] T') (φ : WithConv (H →ₐ[R] T)),
    ((e T' (.toConv (g.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (e T φ).val.1)

include he_mul in

theorem pt_convMul (T : Type u) [CommRing T] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T] (φ ψ : H →ₐ[R] T) :
    pt L n ι H e R' T (WithConv.toConv φ * WithConv.toConv ψ).ofConv =
      L.mul _ (pt L n ι H e R' T φ) (pt L n ι H e R' T ψ) := by
  unfold pt
  rw [mul_castPt, WithConv.toConv_ofConv, he_mul]

omit [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H] in
theorem val_congr (χ : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι))
    (T : Type u) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R'))
    {x y : SchemeHomOver (κ ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) f} (h : x = y)
    (hx : L.IsTorsionPoint _ n x) (hy : L.IsTorsionPoint _ n y) : χ.val T κ x hx = χ.val T κ y hy := by
  subst h; rfl

omit [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H] in
theorem isTorsionPoint_congr {T : Type u} [CommRing T] {κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R')}
    {x y : SchemeHomOver (κ ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) f} (h : x = y)
    (hx : L.IsTorsionPoint _ n x) : L.IsTorsionPoint _ n y := by
  subst h; exact hx

include he_mul in

theorem valAt_convMul (χ : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι))
    (T : Type u) [CommRing T] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T] (φ ψ : H →ₐ[R] T) :
    valAt L n ι H e R' χ T (WithConv.toConv φ * WithConv.toConv ψ).ofConv =
      valAt L n ι H e R' χ T φ * valAt L n ι H e R' χ T ψ := by
  have hpt := pt_convMul L n ι H e R' he_mul T φ ψ
  have htors : L.IsTorsionPoint _ n (L.mul _ (pt L n ι H e R' T φ) (pt L n ι H e R' T ψ)) :=
    isTorsionPoint_congr L n ι R' hpt (pt_tors L n ι H e R' T _)
  exact (val_congr L n ι R' χ T _ hpt (pt_tors L n ι H e R' T _) htors).trans (χ.val_mul T _ _ _ _ _ htors)

include he_mul in

theorem valAt_convOne (χ : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι))
    (T : Type u) [CommRing T] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T] :
    valAt L n ι H e R' χ T (1 : WithConv (H →ₐ[R] T)).ofConv = 1 := by
  have h := valAt_convMul L n ι H e R' he_mul χ T (1 : WithConv (H →ₐ[R] T)).ofConv (1 : WithConv (H →ₐ[R] T)).ofConv
  rw [WithConv.toConv_ofConv, mul_one] at h
  exact mul_left_cancel (h.symm.trans (mul_one _).symm) |>.symm |> fun h' => h'.symm

noncomputable def liftPt (T : Type u) [CommRing T] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T] (φ : H →ₐ[R] T) :
    R' ⊗[R] H →ₐ[R] T :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R R' T) φ (fun _ _ => Commute.all _ _)

omit [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H] in
theorem liftPt_comp_algebraMap (T : Type u) [CommRing T] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T]
    (φ : H →ₐ[R] T) : (liftPt H R' T φ).toRingHom.comp (algebraMap R' (R' ⊗[R] H)) = algebraMap R' T := by
  ext r
  show liftPt H R' T φ (r ⊗ₜ[R] 1) = algebraMap R' T r
  simp [liftPt]

omit [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H] in
theorem liftPt_comp_includeRight (T : Type u) [CommRing T] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T]
    (φ : H →ₐ[R] T) : (liftPt H R' T φ).comp Algebra.TensorProduct.includeRight = φ := by
  ext h
  simp [liftPt]

noncomputable def uOf (χ : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) : R' ⊗[R] H :=
  (valAt L n ι H e R' χ (R' ⊗[R] H) Algebra.TensorProduct.includeRight).val

include he_nat in

theorem valAt_eq_liftPt (χ : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι))
    (T : Type u) [CommRing T] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T] (φ : H →ₐ[R] T) :
    (valAt L n ι H e R' χ T φ).val = liftPt H R' T φ (uOf L n ι H e R' χ) := by
  have h := valAt_map L n ι H e R' he_nat χ (R' ⊗[R] H) T (liftPt H R' T φ) (liftPt_comp_algebraMap H R' T φ)
    Algebra.TensorProduct.includeRight
  rw [liftPt_comp_includeRight] at h
  rw [h]
  rfl

omit [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H] in
theorem liftPt_coord₁ :
    liftPt H R' (R' ⊗[R] (H ⊗[R] H))
        ((Algebra.TensorProduct.includeRight : H ⊗[R] H →ₐ[R] R' ⊗[R] (H ⊗[R] H)).comp
          (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H)) =
      Algebra.TensorProduct.map (AlgHom.id R R') (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H) := by
  ext x
  · simp [liftPt, Algebra.TensorProduct.one_def]
  · simp [liftPt]

omit [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H] in
theorem liftPt_coord₂ :
    liftPt H R' (R' ⊗[R] (H ⊗[R] H))
        ((Algebra.TensorProduct.includeRight : H ⊗[R] H →ₐ[R] R' ⊗[R] (H ⊗[R] H)).comp
          (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H)) =
      Algebra.TensorProduct.map (AlgHom.id R R') (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H) := by
  ext x
  · simp [liftPt, Algebra.TensorProduct.one_def]
  · simp [liftPt]

omit [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H] in
theorem eval₂_coord :
    CharYonedaAux.eval₂ R H R' (T := R' ⊗[R] (H ⊗[R] H)) (IsScalarTower.toAlgHom R R' (R' ⊗[R] (H ⊗[R] H)))
        ((Algebra.TensorProduct.includeRight : H ⊗[R] H →ₐ[R] R' ⊗[R] (H ⊗[R] H)).comp
          (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H))
        ((Algebra.TensorProduct.includeRight : H ⊗[R] H →ₐ[R] R' ⊗[R] (H ⊗[R] H)).comp
          (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H)) =
      AlgHom.id R (R' ⊗[R] (H ⊗[R] H)) := by
  ext x
  · simp [CharYonedaAux.eval₂, Algebra.TensorProduct.one_def]
  · simp [CharYonedaAux.eval₂]
  · simp [CharYonedaAux.eval₂]

omit [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H] in

theorem liftPt_convOne_apply (v : R' ⊗[R] H) :
    liftPt H R' R' (1 : WithConv (H →ₐ[R] R')).ofConv v =
      Algebra.TensorProduct.rid R R' R' (LinearMap.lTensor R' (Coalgebra.counit (R := R) (A := H)) v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul r h =>
    rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.rid_tmul]
    simp [liftPt, AlgHom.convOne_apply, Algebra.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

include he_mul he_nat in

theorem isGrouplike_uOf (χ : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) :
    CharYonedaAux.IsGrouplike R H R' (uOf L n ι H e R' χ) := by
  constructor
  ·
    have h := congrArg Units.val (valAt_convMul L n ι H e R' he_mul χ (R' ⊗[R] (H ⊗[R] H))
      ((Algebra.TensorProduct.includeRight : H ⊗[R] H →ₐ[R] R' ⊗[R] (H ⊗[R] H)).comp Algebra.TensorProduct.includeLeft)
      ((Algebra.TensorProduct.includeRight : H ⊗[R] H →ₐ[R] R' ⊗[R] (H ⊗[R] H)).comp Algebra.TensorProduct.includeRight))
    rw [Units.val_mul, valAt_eq_liftPt L n ι H e R' he_nat, valAt_eq_liftPt L n ι H e R' he_nat,
      valAt_eq_liftPt L n ι H e R' he_nat, liftPt_coord₁, liftPt_coord₂] at h
    rw [← h]

    have := CharYonedaAux.eval₂_lTensor_comul R H R' (T := R' ⊗[R] (H ⊗[R] H)) (IsScalarTower.toAlgHom R R' (R' ⊗[R] (H ⊗[R] H)))
      ((Algebra.TensorProduct.includeRight : H ⊗[R] H →ₐ[R] R' ⊗[R] (H ⊗[R] H)).comp Algebra.TensorProduct.includeLeft)
      ((Algebra.TensorProduct.includeRight : H ⊗[R] H →ₐ[R] R' ⊗[R] (H ⊗[R] H)).comp Algebra.TensorProduct.includeRight)
      (uOf L n ι H e R' χ)
    rw [eval₂_coord, AlgHom.id_apply] at this
    exact this
  ·
    have h := congrArg Units.val (valAt_convOne L n ι H e R' he_mul χ R')
    rw [valAt_eq_liftPt L n ι H e R' he_nat, liftPt_convOne_apply, Units.val_one] at h
    apply (Algebra.TensorProduct.rid R R' R').injective
    rw [h, Algebra.TensorProduct.rid_tmul, one_smul]

section InvPt
variable {T : Type u} [CommRing T] [Algebra R T]

omit [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H] in

noncomputable def invPt (φ : H →ₐ[R] T) : H →ₐ[R] T :=
  AlgHom.ofLinearMap (φ.toLinearMap ∘ₗ HopfAlgebra.antipode R)
    (by simp [HopfAlgebra.antipode_one])
    (fun a b => by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, HopfAlgebra.antipode_mul, map_mul]
      exact mul_comm _ _)

omit [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H] in
theorem invPt_apply (φ : H →ₐ[R] T) (h : H) : invPt H φ h = φ (HopfAlgebra.antipode R h) := rfl

omit [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H] in
theorem convMul_invPt (φ : H →ₐ[R] T) : WithConv.toConv φ * WithConv.toConv (invPt H φ) = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro h
  let ℛ := Coalgebra.Repr.arbitrary R h
  show (WithConv.toConv φ * WithConv.toConv (invPt H φ)) h = (1 : WithConv (H →ₐ[R] T)) h
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply, ← ℛ.eq, map_sum]
  simp only [Algebra.TensorProduct.lift_tmul, invPt_apply, ← map_mul, ← map_sum,
    HopfAlgebra.sum_mul_antipode_eq_smul ℛ, map_smul, map_one, Algebra.smul_def, mul_one, AlgHom.commutes]

end InvPt
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_TorsionCharacter_exists_equiv_algHom_cartierDual_of_torsionSubset_equiv.CharYonedaAux"

theorem isUnit_liftPt_of_isGrouplike (u : R' ⊗[R] H) (hu : CharYonedaAux.IsGrouplike R H R' u)
    (T : Type u) [CommRing T] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T] (φ : H →ₐ[R] T) :
    IsUnit (liftPt H R' T φ u) := by
  refine IsUnit.of_mul_eq_one (liftPt H R' T (invPt H φ) u) ?_
  have h1 := CharYonedaAux.eval_mul_of_isGrouplike R H R' u hu (IsScalarTower.toAlgHom R R' T) φ (invPt H φ)
  have h2 := CharYonedaAux.eval_one_of_isGrouplike R H R' u hu (IsScalarTower.toAlgHom R R' T)
  rw [convMul_invPt] at h1
  unfold liftPt
  rw [← h1, h2]

omit [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H] in
theorem base_eq' (T : Type u) [CommRing T] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T]
    (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R')) (hκ : κ = Spec.map (CommRingCat.ofHom (algebraMap R' T))) :
    κ ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι) = Spec.map (CommRingCat.ofHom (algebraMap R T)) ≫ ι := by
  rw [hκ, base_eq ι R' T]

noncomputable def hpt (T : Type u) [CommRing T] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T]
    (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R')) (hκ : κ = Spec.map (CommRingCat.ofHom (algebraMap R' T)))
    (x : SchemeHomOver (κ ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) f) (hx : L.IsTorsionPoint _ n x) :
    H →ₐ[R] T :=
  ((e T).symm ⟨castPt (base_eq' ι R' T κ hκ) x, (isTorsionPoint_castPt L n _ x).mpr hx⟩).ofConv

theorem e_hpt (T : Type u) [CommRing T] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T]
    (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R')) (hκ : κ = Spec.map (CommRingCat.ofHom (algebraMap R' T)))
    (x : SchemeHomOver (κ ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) f) (hx : L.IsTorsionPoint _ n x) :
    (e T (WithConv.toConv (hpt L n ι H e R' T κ hκ x hx))).val.1 = x.1 := by
  unfold hpt
  rw [WithConv.toConv_ofConv, Equiv.apply_symm_apply]
  rfl

theorem pt_hpt_fst (T : Type u) [CommRing T] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T]
    (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R')) (hκ : κ = Spec.map (CommRingCat.ofHom (algebraMap R' T)))
    (x : SchemeHomOver (κ ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) f) (hx : L.IsTorsionPoint _ n x) :
    (pt L n ι H e R' T (hpt L n ι H e R' T κ hκ x hx)).1 = x.1 := by
  rw [pt_fst, e_hpt]

include he_nat in

theorem val_eq_liftPt_hpt (χ : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι))
    (T : Type u) [CommRing T] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T]
    (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R')) (hκ : κ = Spec.map (CommRingCat.ofHom (algebraMap R' T)))
    (x : SchemeHomOver (κ ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) f) (hx : L.IsTorsionPoint _ n x) :
    (χ.val T κ x hx).val = liftPt H R' T (hpt L n ι H e R' T κ hκ x hx) (uOf L n ι H e R' χ) := by
  rw [← valAt_eq_liftPt L n ι H e R' he_nat]

  subst hκ
  unfold valAt
  congr 1
  symm
  have h := χ.val_natural T T _ _ (RingHom.id T) (by simp) (pt L n ι H e R' T (hpt L n ι H e R' T _ rfl x hx))
    (pt_tors L n ι H e R' T _) x hx (by rw [pt_hpt_fst]; simp)
  rw [h]
  ext
  simp

omit [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H] in
theorem kappa_eq_of_preimage (T : Type u) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R')) :
    κ = Spec.map (CommRingCat.ofHom (Spec.preimage κ).hom) := by
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

include he_mul in

theorem hpt_mul (T : Type u) [CommRing T] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T]
    (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R')) (hκ : κ = Spec.map (CommRingCat.ofHom (algebraMap R' T)))
    (x y : SchemeHomOver (κ ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) f)
    (hx : L.IsTorsionPoint _ n x) (hy : L.IsTorsionPoint _ n y) (hxy : L.IsTorsionPoint _ n (L.mul _ x y)) :
    WithConv.toConv (hpt L n ι H e R' T κ hκ (L.mul _ x y) hxy) =
      WithConv.toConv (hpt L n ι H e R' T κ hκ x hx) * WithConv.toConv (hpt L n ι H e R' T κ hκ y hy) := by
  apply (e T).injective
  apply Subtype.ext
  rw [he_mul]
  unfold hpt
  rw [WithConv.toConv_ofConv, WithConv.toConv_ofConv, WithConv.toConv_ofConv, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact (mul_castPt L (base_eq' ι R' T κ hκ) x y).symm

include he_nat in

theorem hpt_map (T T' : Type u) [CommRing T] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T]
    [CommRing T'] [Algebra R T'] [Algebra R' T'] [IsScalarTower R R' T']
    (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R')) (hκ : κ = Spec.map (CommRingCat.ofHom (algebraMap R' T)))
    (κ' : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of R')) (hκ' : κ' = Spec.map (CommRingCat.ofHom (algebraMap R' T')))
    (g : T →ₐ[R] T')
    (x : SchemeHomOver (κ ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) f) (hx : L.IsTorsionPoint _ n x)
    (x' : SchemeHomOver (κ' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) f) (hx' : L.IsTorsionPoint _ n x')
    (hxx' : x'.1 = Spec.map (CommRingCat.ofHom g.toRingHom) ≫ x.1) :
    hpt L n ι H e R' T' κ' hκ' x' hx' = g.comp (hpt L n ι H e R' T κ hκ x hx) := by
  apply WithConv.toConv_injective
  apply (e T').injective
  apply Subtype.ext
  apply Subtype.ext

  have h1 := e_hpt L n ι H e R' T' κ' hκ' x' hx'
  have h2 := he_nat T T' g (WithConv.toConv (hpt L n ι H e R' T κ hκ x hx))
  rw [WithConv.ofConv_toConv, e_hpt] at h2
  rw [h1, h2, hxx']

omit [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H] in

theorem liftPt_comp (T T' : Type u) [CommRing T] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T]
    [CommRing T'] [Algebra R T'] [Algebra R' T'] [IsScalarTower R R' T']
    (g : T →ₐ[R] T') (hg : g.toRingHom.comp (algebraMap R' T) = algebraMap R' T') (φ : H →ₐ[R] T) :
    liftPt H R' T' (g.comp φ) = g.comp (liftPt H R' T φ) := by
  apply Algebra.TensorProduct.ext
  · ext r
    show liftPt H R' T' (g.comp φ) (r ⊗ₜ[R] 1) = g (liftPt H R' T φ (r ⊗ₜ[R] 1))
    simp only [liftPt, Algebra.TensorProduct.lift_tmul, map_one, mul_one, map_mul]
    exact (RingHom.congr_fun hg r).symm
  · ext h
    simp [liftPt]

noncomputable def charOf (u : R' ⊗[R] H) (hu : CharYonedaAux.IsGrouplike R H R' u) :
    L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι) where
  val T _ κ x hx :=
    letI : Algebra R' T := (Spec.preimage κ).hom.toAlgebra
    letI : Algebra R T := ((Spec.preimage κ).hom.comp (algebraMap R R')).toAlgebra
    haveI : IsScalarTower R R' T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    (isUnit_liftPt_of_isGrouplike H R' u hu T
      (hpt L n ι H e R' T κ (kappa_eq_of_preimage R' T κ) x hx)).unit
  val_mul T _ κ x y hx hy hxy := by
    letI : Algebra R' T := (Spec.preimage κ).hom.toAlgebra
    letI : Algebra R T := ((Spec.preimage κ).hom.comp (algebraMap R R')).toAlgebra
    haveI : IsScalarTower R R' T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    ext
    simp only [Units.val_mul, IsUnit.unit_spec]
    have h := hpt_mul L n ι H e R' he_mul T κ (kappa_eq_of_preimage R' T κ) x y hx hy hxy
    have h' : hpt L n ι H e R' T κ (kappa_eq_of_preimage R' T κ) (L.mul _ x y) hxy =
        (WithConv.toConv (hpt L n ι H e R' T κ (kappa_eq_of_preimage R' T κ) x hx) *
          WithConv.toConv (hpt L n ι H e R' T κ (kappa_eq_of_preimage R' T κ) y hy)).ofConv := by
      rw [← h, WithConv.ofConv_toConv]
    rw [h']
    exact CharYonedaAux.eval_mul_of_isGrouplike R H R' u hu (IsScalarTower.toAlgHom R R' T) _ _
  val_natural T T' _ _ κ κ' φr hφ x hx x' hx' hxx' := by
    letI iT : Algebra R' T := (Spec.preimage κ).hom.toAlgebra
    letI jT : Algebra R T := ((Spec.preimage κ).hom.comp (algebraMap R R')).toAlgebra
    haveI : IsScalarTower R R' T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI iT' : Algebra R' T' := (Spec.preimage κ').hom.toAlgebra
    letI jT' : Algebra R T' := ((Spec.preimage κ').hom.comp (algebraMap R R')).toAlgebra
    haveI : IsScalarTower R R' T' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

    have hpre : (Spec.preimage κ').hom = φr.comp (Spec.preimage κ).hom := by
      have : Spec.preimage κ' = Spec.preimage κ ≫ CommRingCat.ofHom φr := by
        apply Spec.map_injective
        rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage, hφ]
      rw [this]; rfl
    have hcomm : ∀ r : R, φr (algebraMap R T r) = algebraMap R T' r := by
      intro r
      show φr ((Spec.preimage κ).hom (algebraMap R R' r)) = (Spec.preimage κ').hom (algebraMap R R' r)
      rw [hpre]; rfl
    let g : T →ₐ[R] T' := ⟨φr, hcomm⟩
    have hg : g.toRingHom.comp (algebraMap R' T) = algebraMap R' T' := by
      show φr.comp (Spec.preimage κ).hom = (Spec.preimage κ').hom
      rw [hpre]
    ext
    simp only [IsUnit.unit_spec, Units.coe_map, MonoidHom.coe_coe]
    rw [hpt_map L n ι H e R' he_nat T T' κ (kappa_eq_of_preimage R' T κ) κ' (kappa_eq_of_preimage R' T' κ') g x hx x' hx'
      hxx', liftPt_comp H R' T T' g hg]
    rfl

theorem hpt_pt (T : Type u) [CommRing T] [Algebra R T] [Algebra R' T] [IsScalarTower R R' T] (φ : H →ₐ[R] T) :
    hpt L n ι H e R' T (Spec.map (CommRingCat.ofHom (algebraMap R' T))) rfl (pt L n ι H e R' T φ)
      (pt_tors L n ι H e R' T φ) = φ := by
  apply WithConv.toConv_injective
  apply (e T).injective
  apply Subtype.ext
  apply Subtype.ext
  rw [e_hpt, pt_fst]

omit [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H] in
theorem liftPt_includeRight : liftPt H R' (R' ⊗[R] H) Algebra.TensorProduct.includeRight = AlgHom.id R _ := by
  apply Algebra.TensorProduct.ext
  · ext r
    show liftPt H R' (R' ⊗[R] H) Algebra.TensorProduct.includeRight (r ⊗ₜ[R] 1) = r ⊗ₜ[R] 1
    simp [liftPt]
  · ext h
    simp [liftPt]

include he_nat in

theorem charOf_uOf (χ : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) :
    charOf L n ι H e R' he_mul he_nat (uOf L n ι H e R' χ) (isGrouplike_uOf L n ι H e R' he_mul he_nat χ) = χ := by
  apply GoodReductionJacobian.RelativeGroupLaw.TorsionCharacter.ext
  funext T _ κ x hx
  letI : Algebra R' T := (Spec.preimage κ).hom.toAlgebra
  letI : Algebra R T := ((Spec.preimage κ).hom.comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  ext
  rw [val_eq_liftPt_hpt L n ι H e R' he_nat χ T κ (kappa_eq_of_preimage R' T κ) x hx]
  exact IsUnit.unit_spec _

theorem liftPt_hpt_univ (u : R' ⊗[R] H)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] H))) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) f)
    (hx : L.IsTorsionPoint _ n x)
    (hxe : x.1 = (e (R' ⊗[R] H) (WithConv.toConv Algebra.TensorProduct.includeRight)).val.1)
    (j : Algebra R (R' ⊗[R] H)) (j' : Algebra R' (R' ⊗[R] H))
    (hst : @IsScalarTower R R' (R' ⊗[R] H) _ j'.toSMul j.toSMul)
    (hj : ∀ r : R, @algebraMap R (R' ⊗[R] H) _ _ j r = @algebraMap R (R' ⊗[R] H) _ _ Algebra.TensorProduct.instAlgebra r)
    (hj' : ∀ r : R', @algebraMap R' (R' ⊗[R] H) _ _ j' r =
      @algebraMap R' (R' ⊗[R] H) _ _ Algebra.TensorProduct.leftAlgebra r)
    (hκ : Spec.map (CommRingCat.ofHom (@algebraMap R' (R' ⊗[R] H) _ _ Algebra.TensorProduct.leftAlgebra)) =
      Spec.map (CommRingCat.ofHom (@algebraMap R' (R' ⊗[R] H) _ _ j'))) :
    @liftPt R _ H _ _ R' _ _ (R' ⊗[R] H) _ j j' hst
      (@hpt S _ A f L n R _ ι H _ _ e R' _ _ (R' ⊗[R] H) _ j j' hst
        (Spec.map (CommRingCat.ofHom (@algebraMap R' (R' ⊗[R] H) _ _ Algebra.TensorProduct.leftAlgebra))) hκ x hx) u = u := by
  obtain rfl : j = Algebra.TensorProduct.instAlgebra := Algebra.algebra_ext _ _ hj
  obtain rfl : j' = Algebra.TensorProduct.leftAlgebra := Algebra.algebra_ext _ _ hj'
  have : @hpt S _ A f L n R _ ι H _ _ e R' _ _ (R' ⊗[R] H) _ _ _ hst
        (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] H)))) hκ x hx = Algebra.TensorProduct.includeRight := by
    apply WithConv.toConv_injective
    apply (e (R' ⊗[R] H)).injective
    apply Subtype.ext
    apply Subtype.ext
    rw [e_hpt]
    exact hxe
  rw [this, liftPt_includeRight]
  rfl

include he_mul he_nat in

theorem uOf_charOf (u : R' ⊗[R] H) (hu : CharYonedaAux.IsGrouplike R H R' u) :
    uOf L n ι H e R' (charOf L n ι H e R' he_mul he_nat u hu) = u := by
  have hpre : (Spec.preimage (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] H))))).hom =
      algebraMap R' (R' ⊗[R] H) := by
    rw [Spec.preimage_map, CommRingCat.hom_ofHom]
  unfold uOf valAt
  dsimp only [charOf]
  rw [IsUnit.unit_spec]
  refine liftPt_hpt_univ L n ι H e R' u _ _ (pt_fst L n ι H e R' _ _) _ _ _ (fun r => ?_) (fun r => ?_) _
  · show (Spec.preimage (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] H))))).hom (algebraMap R R' r) = _
    rw [hpre, ← IsScalarTower.algebraMap_apply]
  · show (Spec.preimage (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] H))))).hom r = _
    rw [hpre]

noncomputable def Ψ : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι) ≃ (CartierDual R H →ₐ[R] R') where
  toFun χ := CharYonedaAux.grouplikeEquiv R H R' ⟨uOf L n ι H e R' χ, isGrouplike_uOf L n ι H e R' he_mul he_nat χ⟩
  invFun ψ := charOf L n ι H e R' he_mul he_nat ((CharYonedaAux.grouplikeEquiv R H R').symm ψ).1
    ((CharYonedaAux.grouplikeEquiv R H R').symm ψ).2
  left_inv χ := by
    show charOf L n ι H e R' he_mul he_nat _ _ = χ
    rw [Equiv.symm_apply_apply]
    exact charOf_uOf L n ι H e R' he_mul he_nat χ
  right_inv ψ := by
    show CharYonedaAux.grouplikeEquiv R H R' _ = ψ
    have h1 : (⟨uOf L n ι H e R' (charOf L n ι H e R' he_mul he_nat ((CharYonedaAux.grouplikeEquiv R H R').symm ψ).1
        ((CharYonedaAux.grouplikeEquiv R H R').symm ψ).2),
        isGrouplike_uOf L n ι H e R' he_mul he_nat (charOf L n ι H e R' he_mul he_nat
          ((CharYonedaAux.grouplikeEquiv R H R').symm ψ).1 ((CharYonedaAux.grouplikeEquiv R H R').symm ψ).2)⟩ :
          {u : R' ⊗[R] H // CharYonedaAux.IsGrouplike R H R' u}) = (CharYonedaAux.grouplikeEquiv R H R').symm ψ :=
      Subtype.ext (uOf_charOf L n ι H e R' he_mul he_nat ((CharYonedaAux.grouplikeEquiv R H R').symm ψ).1
        ((CharYonedaAux.grouplikeEquiv R H R').symm ψ).2)
    exact (congrArg (CharYonedaAux.grouplikeEquiv R H R') h1).trans (Equiv.apply_symm_apply _ ψ)

theorem Ψ_apply (χ : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) (δ : CartierDual R H) :
    Ψ L n ι H e R' he_mul he_nat χ δ = CharYonedaAux.Φ R H R' (uOf L n ι H e R' χ) δ := rfl

theorem Ψ_mul (χ₁ χ₂ χ₃ : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι))
    (h : ∀ (T : Type u) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R'))
        (x : SchemeHomOver (κ ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) f)
        (hx : L.IsTorsionPoint _ n x),
        χ₃.val T κ x hx = χ₁.val T κ x hx * χ₂.val T κ x hx) :
    Ψ L n ι H e R' he_mul he_nat χ₃ =
      (WithConv.toConv (Ψ L n ι H e R' he_mul he_nat χ₁) * WithConv.toConv (Ψ L n ι H e R' he_mul he_nat χ₂)).ofConv := by
  have hu : uOf L n ι H e R' χ₃ = uOf L n ι H e R' χ₁ * uOf L n ι H e R' χ₂ := by
    unfold uOf valAt
    rw [h, Units.val_mul]
  apply AlgHom.ext
  intro δ
  rw [Ψ_apply, hu, CharYonedaAux.Φ_ringMul]
  rfl

theorem Ψ_one (χ : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι))
    (h : ∀ (T : Type u) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R'))
        (x : SchemeHomOver (κ ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) f)
        (hx : L.IsTorsionPoint _ n x), χ.val T κ x hx = 1) :
    Ψ L n ι H e R' he_mul he_nat χ = (1 : WithConv (CartierDual R H →ₐ[R] R')).ofConv := by
  have hu : uOf L n ι H e R' χ = 1 := by
    unfold uOf valAt
    rw [h, Units.val_one]
  apply AlgHom.ext
  intro δ
  rw [Ψ_apply, hu, AlgHom.convOne_apply]
  have h1 : CharYonedaAux.Φ R H R' (1 : R' ⊗[R] H) δ = algebraMap R R' (δ 1) := by
    rw [Algebra.TensorProduct.one_def, CharYonedaAux.Φ_tmul, Algebra.algebraMap_eq_smul_one]
  exact h1.trans (congrArg (algebraMap R R') (CartierDual.counit_apply δ)).symm

include he_mul he_nat in
theorem Ψ_natural (R'' : Type u) [CommRing R''] [Algebra R R''] (g : R' →ₐ[R] R'')
    (χ' : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι))
    (χ'' : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R'')) ≫ ι))
    (hrel : ∀ (T : Type u) [CommRing T] (κ'' : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R''))
        (x'' : SchemeHomOver (κ'' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R'')) ≫ ι)) f)
        (hx'' : L.IsTorsionPoint _ n x'')
        (x' : SchemeHomOver ((κ'' ≫ Spec.map (CommRingCat.ofHom g.toRingHom)) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) f)
        (hx' : L.IsTorsionPoint _ n x'),
        x''.1 = x'.1 →
          χ''.val T κ'' x'' hx'' = χ'.val T (κ'' ≫ Spec.map (CommRingCat.ofHom g.toRingHom)) x' hx') :
    Ψ L n ι H e R'' he_mul he_nat χ'' = g.comp (Ψ L n ι H e R' he_mul he_nat χ') := by

  letI jR' : Algebra R' (R'' ⊗[R] H) := ((algebraMap R'' (R'' ⊗[R] H)).comp g.toRingHom).toAlgebra
  haveI hst : IsScalarTower R R' (R'' ⊗[R] H) := IsScalarTower.of_algebraMap_eq (fun r => by
    show algebraMap R (R'' ⊗[R] H) r = algebraMap R'' (R'' ⊗[R] H) (g (algebraMap R R' r))
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply])
  have hgalg : g.toRingHom.comp (algebraMap R R') = algebraMap R R'' := g.comp_algebraMap
  have hb : Spec.map (CommRingCat.ofHom (algebraMap R'' (R'' ⊗[R] H))) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R R'')) ≫ ι) =
      (Spec.map (CommRingCat.ofHom (algebraMap R'' (R'' ⊗[R] H))) ≫ Spec.map (CommRingCat.ofHom g.toRingHom)) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι) := by
    simp only [← hgalg, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have hκ : Spec.map (CommRingCat.ofHom (algebraMap R'' (R'' ⊗[R] H))) ≫ Spec.map (CommRingCat.ofHom g.toRingHom) =
      Spec.map (CommRingCat.ofHom (algebraMap R' (R'' ⊗[R] H))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

  have hu : uOf L n ι H e R'' χ'' = Algebra.TensorProduct.map g (AlgHom.id R H) (uOf L n ι H e R' χ') := by
    have hx'v : (castPt hb (pt L n ι H e R'' (R'' ⊗[R] H) Algebra.TensorProduct.includeRight)).1 =
        (pt L n ι H e R'' (R'' ⊗[R] H) Algebra.TensorProduct.includeRight).1 := castPt_val hb _
    have htx' : L.IsTorsionPoint _ n (castPt hb (pt L n ι H e R'' (R'' ⊗[R] H) Algebra.TensorProduct.includeRight)) :=
      (isTorsionPoint_castPt L n hb _).mpr (pt_tors L n ι H e R'' (R'' ⊗[R] H) _)
    have h1 := hrel (R'' ⊗[R] H) (Spec.map (CommRingCat.ofHom (algebraMap R'' (R'' ⊗[R] H))))
      (pt L n ι H e R'' (R'' ⊗[R] H) Algebra.TensorProduct.includeRight)
      (pt_tors L n ι H e R'' (R'' ⊗[R] H) _) _ htx' hx'v.symm
    show (valAt L n ι H e R'' χ'' (R'' ⊗[R] H) Algebra.TensorProduct.includeRight).val = _
    unfold valAt
    rw [h1, val_eq_liftPt_hpt L n ι H e R' he_nat χ' (R'' ⊗[R] H) _ hκ]

    have h2 : hpt L n ι H e R' (R'' ⊗[R] H) _ hκ
        (castPt hb (pt L n ι H e R'' (R'' ⊗[R] H) Algebra.TensorProduct.includeRight))
        ((isTorsionPoint_castPt L n hb _).mpr (pt_tors L n ι H e R'' (R'' ⊗[R] H) _)) =
        Algebra.TensorProduct.includeRight := by
      apply WithConv.toConv_injective
      apply (e (R'' ⊗[R] H)).injective
      apply Subtype.ext
      apply Subtype.ext
      rw [e_hpt, castPt_val, pt_fst]
    rw [h2]

    have h3 : liftPt H R' (R'' ⊗[R] H) Algebra.TensorProduct.includeRight = Algebra.TensorProduct.map g (AlgHom.id R H) := by
      apply Algebra.TensorProduct.ext
      · ext r
        show liftPt H R' (R'' ⊗[R] H) Algebra.TensorProduct.includeRight (r ⊗ₜ[R] 1) =
          Algebra.TensorProduct.map g (AlgHom.id R H) (r ⊗ₜ[R] 1)
        simp only [liftPt, Algebra.TensorProduct.lift_tmul, map_one, mul_one, Algebra.TensorProduct.map_tmul,
          AlgHom.id_apply, IsScalarTower.toAlgHom_apply]
        rfl
      · ext h
        simp [liftPt]
    rw [h3]
  apply AlgHom.ext
  intro δ
  rw [Ψ_apply, AlgHom.comp_apply, Ψ_apply, hu, CharYonedaAux.Φ_map]

end Main
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_TorsionCharacter_exists_equiv_algHom_cartierDual_of_torsionSubset_equiv.CharYonedaAux"

end CharYonedaY
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_TorsionCharacter_exists_equiv_algHom_cartierDual_of_torsionSubset_equiv.CharYonedaAux P2MW.S_GoodReductionJacobian_RelativeGroupLaw_TorsionCharacter_exists_equiv_algHom_cartierDual_of_torsionSubset_equiv.CharYonedaY"

theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (n : ℕ)
    {R : Type u} [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (H : Type u) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H]
    (e : ∀ (T : Type u) [CommRing T] [Algebra R T],
      WithConv (H →ₐ[R] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T)) ≫ ι) n)
    (he_mul : ∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (H →ₐ[R] T)),
      ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val)
    (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
        (g : T →ₐ[R] T') (φ : WithConv (H →ₐ[R] T)),
      ((e T' (.toConv (g.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (e T φ).val.1) :
    ∃ Ψ : ∀ (R' : Type u) [CommRing R'] [Algebra R R'],
        L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι) ≃ (CartierDual R H →ₐ[R] R'),

      (∀ (R' R'' : Type u) [CommRing R'] [Algebra R R'] [CommRing R''] [Algebra R R''] (g : R' →ₐ[R] R'')
          (χ' : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι))
          (χ'' : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R'')) ≫ ι)),
          (∀ (T : Type u) [CommRing T] (κ'' : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R''))
              (x'' : SchemeHomOver (κ'' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R'')) ≫ ι)) f)
              (hx'' : L.IsTorsionPoint _ n x'')
              (x' : SchemeHomOver ((κ'' ≫ Spec.map (CommRingCat.ofHom g.toRingHom)) ≫
                (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) f)
              (hx' : L.IsTorsionPoint _ n x'),
              x''.1 = x'.1 →
                χ''.val T κ'' x'' hx'' = χ'.val T (κ'' ≫ Spec.map (CommRingCat.ofHom g.toRingHom)) x' hx') →
          Ψ R'' χ'' = g.comp (Ψ R' χ')) ∧

      (∀ (R' : Type u) [CommRing R'] [Algebra R R']
          (χ₁ χ₂ χ₃ : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)),
          (∀ (T : Type u) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R'))
              (x : SchemeHomOver (κ ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) f)
              (hx : L.IsTorsionPoint _ n x),
              χ₃.val T κ x hx = χ₁.val T κ x hx * χ₂.val T κ x hx) →
          Ψ R' χ₃ = (WithConv.toConv (Ψ R' χ₁) * WithConv.toConv (Ψ R' χ₂)).ofConv) ∧
      (∀ (R' : Type u) [CommRing R'] [Algebra R R']
          (χ : L.TorsionCharacter n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)),
          (∀ (T : Type u) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R'))
              (x : SchemeHomOver (κ ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ ι)) f)
              (hx : L.IsTorsionPoint _ n x), χ.val T κ x hx = 1) →
          Ψ R' χ = (1 : WithConv (CartierDual R H →ₐ[R] R')).ofConv) := by
  refine ⟨fun R' _ _ => CharYonedaY.Ψ L n ι H e R' he_mul he_nat, ?_, ?_, ?_⟩
  · intro R' R'' _ _ _ _ g χ' χ'' hrel
    exact CharYonedaY.Ψ_natural L n ι H e R' he_mul he_nat R'' g χ' χ'' hrel
  · intro R' _ _ χ₁ χ₂ χ₃ h
    exact CharYonedaY.Ψ_mul L n ι H e R' he_mul he_nat χ₁ χ₂ χ₃ h
  · intro R' _ _ χ h
    exact CharYonedaY.Ψ_one L n ι H e R' he_mul he_nat χ h

end S_GoodReductionJacobian_RelativeGroupLaw_TorsionCharacter_exists_equiv_algHom_cartierDual_of_torsionSubset_equiv
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_TorsionCharacter_exists_equiv_algHom_cartierDual_of_torsionSubset_equiv (solution)
