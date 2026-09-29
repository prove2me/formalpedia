-- Prove2me | solution 1 for HopfAlgebra.exists_hopfAlgebra_surjective_injective_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c74d5801-daa3-5408-914e-632a3219cfe9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace HopfAlgebra
p2m_export "HopfAlgebra" "sum_mul_antipode_eq_algebraMap_counit mk antipode_one ofAlgHom mul_antipode_lTensor_comul_apply antipode_mul sum_antipode_mul_eq_algebraMap_counit mul_antipode_rTensor_comul mul_antipode_lTensor_comul mul_antipode_rTensor_comul_apply"
namespace ImageFactor
p2m_open "HopfAlgebra"

variable {R : Type u} [CommRing R]
variable {H : Type v} [CommRing H] [HopfAlgebra R H]
variable {H' : Type v} [CommRing H'] [HopfAlgebra R H']
variable (φ : H →ₐc[R] H')

private abbrev _root_.HopfAlgebra.ImageFactor.ker : Ideal H := RingHom.ker (φ : H →ₐ[R] H')

p2m_export "HopfAlgebra.ImageFactor" "ker"

abbrev Q : Type v := H ⧸ ker φ

def π : H →ₐ[R] Q φ := Ideal.Quotient.mkₐ R (ker φ)

def ι : Q φ →ₐ[R] H' := Ideal.Quotient.liftₐ (ker φ) (φ : H →ₐ[R] H') fun _ ha => ha

theorem π_surjective : Function.Surjective (π φ) := Ideal.Quotient.mkₐ_surjective R _

theorem ι_injective : Function.Injective (ι φ) :=
  RingHom.lift_injective_of_ker_le_ideal _ (fun _ ha => ha) le_rfl

@[scoped simp] theorem ι_π (x : H) : ι φ (π φ x) = φ x := rfl

theorem ι_comp_π : (ι φ).comp (π φ) = (φ : H →ₐ[R] H') := AlgHom.ext fun _ => rfl

scoped instance moduleFinite [Module.Finite R H] : Module.Finite R (Q φ) :=
  Module.Finite.of_surjective (π φ).toLinearMap (π_surjective φ)

private theorem _root_.HopfAlgebra.ImageFactor.isTorsionFree [Module.Flat R H'] : Module.IsTorsionFree R (Q φ) := by
  haveI : Module.IsTorsionFree R H' := Module.Flat.isTorsionFree
  exact Function.Injective.moduleIsTorsionFree (ι φ) (ι_injective φ) (map_smul (ι φ))

p2m_export "HopfAlgebra.ImageFactor" "isTorsionFree"
scoped instance free [IsDomain R] [IsPrincipalIdealRing R] [Module.Finite R H] [Module.Flat R H'] :
    Module.Free R (Q φ) := by
  haveI := isTorsionFree φ
  exact Module.free_of_finite_type_torsion_free'

scoped instance flat [IsDomain R] [IsPrincipalIdealRing R] [Module.Finite R H] [Module.Flat R H'] :
    Module.Flat R (Q φ) := by
  haveI := free φ
  infer_instance

section Descend

variable [IsDomain R] [IsPrincipalIdealRing R] [Module.Finite R H] [Module.Flat R H']

theorem map_ι_ι_injective : Function.Injective (Algebra.TensorProduct.map (ι φ) (ι φ)) := by
  have h1 : Function.Injective ((ι φ).toLinearMap.lTensor (Q φ)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (ι_injective φ)
  have h2 : Function.Injective ((ι φ).toLinearMap.rTensor H') :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (ι_injective φ)
  have h3 : ∀ z, Algebra.TensorProduct.map (ι φ) (ι φ) z =
      ((ι φ).toLinearMap.rTensor H') (((ι φ).toLinearMap.lTensor (Q φ)) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp [map_add, hx, hy]
  intro z w hzw
  rw [h3, h3] at hzw
  exact h1 (h2 hzw)

def comulQ : Q φ →ₐ[R] Q φ ⊗[R] Q φ :=
  Ideal.Quotient.liftₐ (ker φ)
    ((Algebra.TensorProduct.map (π φ) (π φ)).comp (Bialgebra.comulAlgHom R H)) (by
      intro a ha
      apply map_ι_ι_injective φ
      rw [map_zero, AlgHom.comp_apply, ← AlgHom.comp_apply (Algebra.TensorProduct.map (ι φ) (ι φ)),
        ← Algebra.TensorProduct.map_comp, ι_comp_π]
      have ha' : (φ : H →ₐ[R] H') a = 0 := ha
      have e1 : (Algebra.TensorProduct.map (φ : H →ₐ[R] H') (φ : H →ₐ[R] H'))
          (Bialgebra.comulAlgHom R H a) = Bialgebra.comulAlgHom R H' ((φ : H →ₐ[R] H') a) := by
        have h := congrArg (fun f : H →ₐ[R] H' ⊗[R] H' => f a) (BialgHomClass.map_comp_comulAlgHom φ)
        simp only [AlgHom.comp_apply] at h
        exact h
      rw [e1, ha', map_zero])

def counitQ : Q φ →ₐ[R] R :=
  Ideal.Quotient.liftₐ (ker φ) (Bialgebra.counitAlgHom R H) (by
      intro a ha
      have h := congrArg (fun f : H →ₗ[R] R => f a) (CoalgHomClass.counit_comp φ)
      simp only [LinearMap.comp_apply] at h
      have ha' : (φ : H →ₐ[R] H') a = 0 := ha
      show Coalgebra.counit a = 0
      rw [← h]
      show Coalgebra.counit ((φ : H →ₐ[R] H') a) = 0
      rw [ha', map_zero])

@[scoped simp] theorem comulQ_π (x : H) :
    comulQ φ (π φ x) = TensorProduct.map (π φ).toLinearMap (π φ).toLinearMap (Coalgebra.comul x) := rfl

theorem amap_apply (t : H ⊗[R] H) :
    Algebra.TensorProduct.map (π φ) (π φ) t = TensorProduct.map (π φ).toLinearMap (π φ).toLinearMap t := rfl

@[scoped simp] theorem counitQ_π (x : H) : counitQ φ (π φ x) = Coalgebra.counit x := rfl

theorem comulQ_comp_π :
    (comulQ φ).comp (π φ) = (Algebra.TensorProduct.map (π φ) (π φ)).comp (Bialgebra.comulAlgHom R H) :=
  AlgHom.ext fun _ => rfl

theorem counitQ_comp_π : (counitQ φ).comp (π φ) = Bialgebra.counitAlgHom R H :=
  AlgHom.ext fun _ => rfl

end Descend

end HopfAlgebra.ImageFactor
p2m_reactivate "P2MW.S_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq.HopfAlgebra P2MW.S_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq.HopfAlgebra.ImageFactor"
p2m_reactivate "P2MW.S_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq.HopfAlgebra"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "sum_mul_antipode_eq_algebraMap_counit mk antipode_one ofAlgHom mul_antipode_lTensor_comul_apply antipode_mul sum_antipode_mul_eq_algebraMap_counit mul_antipode_rTensor_comul mul_antipode_lTensor_comul mul_antipode_rTensor_comul_apply"
namespace ImageFactor
p2m_open "HopfAlgebra"

open TensorProduct in

theorem assoc_nat {R : Type u} [CommRing R]
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (p : M →ₗ[R] N) (s : (M ⊗[R] M) ⊗[R] M) :
    TensorProduct.assoc R N N N (TensorProduct.map (TensorProduct.map p p) p s) =
      TensorProduct.map p (TensorProduct.map p p) (TensorProduct.assoc R M M M s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul t c =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

variable {R : Type u} [CommRing R]
variable {H : Type v} [CommRing H] [HopfAlgebra R H]
variable {H' : Type v} [CommRing H'] [HopfAlgebra R H']
variable (φ : H →ₐc[R] H')
variable [IsDomain R] [IsPrincipalIdealRing R] [Module.Finite R H] [Module.Flat R H']

theorem comulQ_p (x : H) : comulQ φ (π φ x) = TensorProduct.map (π φ).toLinearMap (π φ).toLinearMap (Coalgebra.comul (R := R) x) := rfl

open TensorProduct in
theorem coassocQ :
    ((Algebra.TensorProduct.assoc R R R (Q φ) (Q φ) (Q φ) :
        (Q φ ⊗[R] Q φ) ⊗[R] Q φ →ₐ[R] Q φ ⊗[R] (Q φ ⊗[R] Q φ))).comp
        ((Algebra.TensorProduct.map (comulQ φ) (AlgHom.id R (Q φ))).comp (comulQ φ)) =
      (Algebra.TensorProduct.map (AlgHom.id R (Q φ)) (comulQ φ)).comp (comulQ φ) := by
  apply Ideal.Quotient.algHom_ext R (I := ker φ)
  apply AlgHom.ext
  intro x
  change (Algebra.TensorProduct.assoc R R R (Q φ) (Q φ) (Q φ))
      ((Algebra.TensorProduct.map (comulQ φ) (AlgHom.id R (Q φ))) (comulQ φ (π φ x))) =
    (Algebra.TensorProduct.map (AlgHom.id R (Q φ)) (comulQ φ)) (comulQ φ (π φ x))

  have E1 : ∀ t : H ⊗[R] H,
      (Algebra.TensorProduct.map (comulQ φ) (AlgHom.id R (Q φ))) (TensorProduct.map (π φ).toLinearMap (π φ).toLinearMap t) =
        TensorProduct.map (TensorProduct.map (π φ).toLinearMap (π φ).toLinearMap) (π φ).toLinearMap
          (LinearMap.rTensor H Coalgebra.comul t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [comulQ_p, amap_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  have E2 : ∀ t : H ⊗[R] H,
      (Algebra.TensorProduct.map (AlgHom.id R (Q φ)) (comulQ φ)) (TensorProduct.map (π φ).toLinearMap (π φ).toLinearMap t) =
        TensorProduct.map (π φ).toLinearMap (TensorProduct.map (π φ).toLinearMap (π φ).toLinearMap)
          (LinearMap.lTensor H Coalgebra.comul t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [comulQ_p, amap_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hco := congrArg (fun f : H →ₗ[R] H ⊗[R] (H ⊗[R] H) => f x) (Coalgebra.coassoc (R := R) (A := H))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hco
  rw [comulQ_p, E1, E2, ← hco]
  exact assoc_nat (π φ).toLinearMap _

open TensorProduct in
theorem rTensor_counitQ :
    (Algebra.TensorProduct.map (counitQ φ) (AlgHom.id R (Q φ))).comp (comulQ φ) =
      ↑(Algebra.TensorProduct.lid R (Q φ)).symm := by
  apply Ideal.Quotient.algHom_ext R (I := ker φ)
  apply AlgHom.ext
  intro x
  change (Algebra.TensorProduct.map (counitQ φ) (AlgHom.id R (Q φ))) (comulQ φ (π φ x)) =
    (Algebra.TensorProduct.lid R (Q φ)).symm (π φ x)
  have E : ∀ t : H ⊗[R] H,
      (Algebra.TensorProduct.map (counitQ φ) (AlgHom.id R (Q φ))) (TensorProduct.map (π φ).toLinearMap (π φ).toLinearMap t) =
        TensorProduct.map LinearMap.id (π φ).toLinearMap (LinearMap.rTensor H Coalgebra.counit t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have hc := congrArg (fun f : H →ₗ[R] R ⊗[R] H => f x) (Coalgebra.rTensor_counit_comp_comul (R := R) (A := H))
  simp only [LinearMap.comp_apply] at hc
  rw [comulQ_p, E, hc]
  simp

open TensorProduct in
theorem lTensor_counitQ :
    (Algebra.TensorProduct.map (AlgHom.id R (Q φ)) (counitQ φ)).comp (comulQ φ) =
      ↑(Algebra.TensorProduct.rid R R (Q φ)).symm := by
  apply Ideal.Quotient.algHom_ext R (I := ker φ)
  apply AlgHom.ext
  intro x
  change (Algebra.TensorProduct.map (AlgHom.id R (Q φ)) (counitQ φ)) (comulQ φ (π φ x)) =
    (Algebra.TensorProduct.rid R R (Q φ)).symm (π φ x)
  have E : ∀ t : H ⊗[R] H,
      (Algebra.TensorProduct.map (AlgHom.id R (Q φ)) (counitQ φ)) (TensorProduct.map (π φ).toLinearMap (π φ).toLinearMap t) =
        TensorProduct.map (π φ).toLinearMap LinearMap.id (LinearMap.lTensor H Coalgebra.counit t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have hc := congrArg (fun f : H →ₗ[R] H ⊗[R] R => f x) (Coalgebra.lTensor_counit_comp_comul (R := R) (A := H))
  simp only [LinearMap.comp_apply] at hc
  rw [comulQ_p, E, hc]
  simp

noncomputable scoped instance bialgebraQ : Bialgebra R (Q φ) :=
  Bialgebra.ofAlgHom (comulQ φ) (counitQ φ) (coassocQ φ) (rTensor_counitQ φ) (lTensor_counitQ φ)

theorem comul_def : (Coalgebra.comul : Q φ →ₗ[R] Q φ ⊗[R] Q φ) = (comulQ φ).toLinearMap := rfl
theorem counit_def : (Coalgebra.counit : Q φ →ₗ[R] R) = (counitQ φ).toLinearMap := rfl

end HopfAlgebra.ImageFactor
p2m_reactivate "P2MW.S_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq.HopfAlgebra P2MW.S_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq.HopfAlgebra.ImageFactor"
p2m_reactivate "P2MW.S_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq.HopfAlgebra P2MW.S_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq.HopfAlgebra.ImageFactor"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "sum_mul_antipode_eq_algebraMap_counit mk antipode_one ofAlgHom mul_antipode_lTensor_comul_apply antipode_mul sum_antipode_mul_eq_algebraMap_counit mul_antipode_rTensor_comul mul_antipode_lTensor_comul mul_antipode_rTensor_comul_apply"
namespace ImageFactor
p2m_open "HopfAlgebra"

section AntipodeCompat

variable {R : Type u} [CommRing R]
variable {H : Type v} [CommRing H] [HopfAlgebra R H]
variable {H' : Type v} [CommRing H'] [HopfAlgebra R H']

open TensorProduct in

theorem map_antipode (φ : H →ₐc[R] H') (x : H) :
    φ (HopfAlgebra.antipode R x) = HopfAlgebra.antipode R (φ x) := by
  classical
  let φL : H →ₗ[R] H' := (φ : H →ₐc[R] H').toLinearMap
  let Φ : WithConv (H →ₗ[R] H') := WithConv.toConv φL
  let L : WithConv (H →ₗ[R] H') := WithConv.toConv (φL ∘ₗ HopfAlgebra.antipode R)
  let Rt : WithConv (H →ₗ[R] H') := WithConv.toConv (HopfAlgebra.antipode R ∘ₗ φL)
  have hL : L * Φ = 1 := by
    refine WithConv.ext (LinearMap.ext fun c => ?_)
    rw [LinearMap.convMul_apply]
    change LinearMap.mul' R H' (TensorProduct.map (φL ∘ₗ HopfAlgebra.antipode R) φL (Coalgebra.comul c)) =
      algebraMap R H' (Coalgebra.counit c)
    let ρ := Coalgebra.Repr.arbitrary R c
    have hs := HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit ρ
    rw [← ρ.eq, map_sum, map_sum]
    simp only [TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.comp_apply]
    calc ∑ i ∈ ρ.index, φL (HopfAlgebra.antipode R (ρ.left i)) * φL (ρ.right i)
        = φ (∑ i ∈ ρ.index, HopfAlgebra.antipode R (ρ.left i) * ρ.right i) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul]
          rfl
      _ = algebraMap R H' (Coalgebra.counit c) := by
          rw [hs]
          exact AlgHomClass.commutes φ _
  have hR : Φ * Rt = 1 := by
    refine WithConv.ext (LinearMap.ext fun c => ?_)
    rw [LinearMap.convMul_apply]
    change LinearMap.mul' R H' (TensorProduct.map φL (HopfAlgebra.antipode R ∘ₗ φL) (Coalgebra.comul c)) =
      algebraMap R H' (Coalgebra.counit c)
    let ρ := Coalgebra.Repr.arbitrary R c

    have hmap := congrArg (fun f : H →ₗ[R] H' ⊗[R] H' => f c) (CoalgHomClass.map_comp_comul φ)
    simp only [LinearMap.comp_apply] at hmap
    have heq : ∑ i ∈ ρ.index, φ (ρ.left i) ⊗ₜ[R] φ (ρ.right i) = Coalgebra.comul (φ c) := by
      rw [← ρ.eq, map_sum] at hmap
      simp only [TensorProduct.map_tmul] at hmap
      exact hmap
    let ρ' : Coalgebra.Repr R (φ c) _ :=
      Coalgebra.Repr.mk ρ.index (fun i => φ (ρ.left i)) (fun i => φ (ρ.right i)) heq
    have hs := HopfAlgebra.sum_mul_antipode_eq_algebraMap_counit ρ'
    have hcu : Coalgebra.counit (φ c) = Coalgebra.counit (R := R) c := by
      have h := congrArg (fun f : H →ₗ[R] R => f c) (CoalgHomClass.counit_comp φ)
      simpa using h
    rw [← ρ.eq, map_sum, map_sum]
    simp only [TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.comp_apply]
    rw [← hcu, ← hs]
    rfl
  have hLR : L = Rt := left_inv_eq_right_inv hL hR
  have h := congrArg (fun f : WithConv (H →ₗ[R] H') => f.ofConv x) hLR
  exact h

end AntipodeCompat
p2m_reactivate "P2MW.S_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq.HopfAlgebra P2MW.S_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq.HopfAlgebra.ImageFactor"

variable {R : Type u} [CommRing R]
variable {H : Type v} [CommRing H] [HopfAlgebra R H]
variable {H' : Type v} [CommRing H'] [HopfAlgebra R H']
variable (φ : H →ₐc[R] H')
variable [IsDomain R] [IsPrincipalIdealRing R] [Module.Finite R H] [Module.Flat R H']

noncomputable def antipodeAlgHomH : H →ₐ[R] H :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode R) (HopfAlgebra.antipode_one (R := R) (A := H))
    (fun a b => by rw [HopfAlgebra.antipode_mul, mul_comm])

omit [IsDomain R] [IsPrincipalIdealRing R] [Module.Finite R H] [Module.Flat R H'] in
@[scoped simp] theorem antipodeAlgHomH_apply (x : H) :
    antipodeAlgHomH (R := R) (H := H) x = HopfAlgebra.antipode R x := rfl

noncomputable def antipodeQ : Q φ →ₐ[R] Q φ :=
  Ideal.Quotient.liftₐ (ker φ) ((π φ).comp (antipodeAlgHomH (R := R) (H := H))) (by
    intro a ha
    have ha' : (φ : H →ₐ[R] H') a = 0 := ha
    show π φ (HopfAlgebra.antipode R a) = 0
    apply ι_injective φ
    rw [map_zero, ι_π]
    show (φ : H →ₐc[R] H') (HopfAlgebra.antipode R a) = 0
    rw [map_antipode]
    have : (φ : H →ₐc[R] H') a = 0 := ha'
    rw [this, map_zero])

@[scoped simp] theorem antipodeQ_π (x : H) : antipodeQ φ (π φ x) = π φ (HopfAlgebra.antipode R x) := rfl

noncomputable scoped instance hopfStructQ : HopfAlgebraStruct R (Q φ) where
  antipode := (antipodeQ φ).toLinearMap

theorem antipode_def : (HopfAlgebra.antipode R : Q φ →ₗ[R] Q φ) = (antipodeQ φ).toLinearMap := rfl

open TensorProduct in
noncomputable scoped instance hopfQ : HopfAlgebra R (Q φ) where
  mul_antipode_rTensor_comul := by
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := π_surjective φ y
    change LinearMap.mul' R (Q φ)
        (LinearMap.rTensor (Q φ) (antipodeQ φ).toLinearMap (comulQ φ (π φ x))) =
      algebraMap R (Q φ) (counitQ φ (π φ x))
    rw [comulQ_π, counitQ_π]
    have E : ∀ t : H ⊗[R] H,
        LinearMap.mul' R (Q φ) (LinearMap.rTensor (Q φ) (antipodeQ φ).toLinearMap
          (TensorProduct.map (π φ).toLinearMap (π φ).toLinearMap t)) =
        π φ (LinearMap.mul' R H (LinearMap.rTensor H (HopfAlgebra.antipode R) t)) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [map_mul]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [E, HopfAlgebra.mul_antipode_rTensor_comul_apply]
    exact (π φ).commutes _
  mul_antipode_lTensor_comul := by
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := π_surjective φ y
    change LinearMap.mul' R (Q φ)
        (LinearMap.lTensor (Q φ) (antipodeQ φ).toLinearMap (comulQ φ (π φ x))) =
      algebraMap R (Q φ) (counitQ φ (π φ x))
    rw [comulQ_π, counitQ_π]
    have E : ∀ t : H ⊗[R] H,
        LinearMap.mul' R (Q φ) (LinearMap.lTensor (Q φ) (antipodeQ φ).toLinearMap
          (TensorProduct.map (π φ).toLinearMap (π φ).toLinearMap t)) =
        π φ (LinearMap.mul' R H (LinearMap.lTensor H (HopfAlgebra.antipode R) t)) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [map_mul]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [E, HopfAlgebra.mul_antipode_lTensor_comul_apply]
    exact (π φ).commutes _

noncomputable def πb : H →ₐc[R] Q φ :=
  BialgHom.ofAlgHom (π φ) (counitQ_comp_π φ) (comulQ_comp_π φ).symm

theorem ι_counit : (Bialgebra.counitAlgHom R H').comp (ι φ) = Bialgebra.counitAlgHom R (Q φ) := by
  apply Ideal.Quotient.algHom_ext R (I := ker φ)
  apply AlgHom.ext
  intro x
  change Coalgebra.counit ((φ : H →ₐc[R] H') x) = Coalgebra.counit (R := R) x
  have h := congrArg (fun f : H →ₗ[R] R => f x) (CoalgHomClass.counit_comp φ)
  simpa using h

open TensorProduct in
theorem ι_comul :
    (Algebra.TensorProduct.map (ι φ) (ι φ)).comp (Bialgebra.comulAlgHom R (Q φ)) =
      (Bialgebra.comulAlgHom R H').comp (ι φ) := by
  apply Ideal.Quotient.algHom_ext R (I := ker φ)
  apply AlgHom.ext
  intro x
  change Algebra.TensorProduct.map (ι φ) (ι φ) (comulQ φ (π φ x)) =
    Coalgebra.comul ((φ : H →ₐc[R] H') x)
  rw [comulQ_π]
  have E : ∀ t : H ⊗[R] H,
      Algebra.TensorProduct.map (ι φ) (ι φ) (TensorProduct.map (π φ).toLinearMap (π φ).toLinearMap t) =
        TensorProduct.map (φ : H →ₐc[R] H').toLinearMap (φ : H →ₐc[R] H').toLinearMap t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [ι_π]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [E]
  have hmap := congrArg (fun f : H →ₗ[R] H' ⊗[R] H' => f x) (CoalgHomClass.map_comp_comul φ)
  simp only [LinearMap.comp_apply] at hmap
  exact hmap

noncomputable def ιb : Q φ →ₐc[R] H' :=
  BialgHom.ofAlgHom (ι φ) (ι_counit φ) (ι_comul φ)

@[scoped simp] theorem πb_apply (x : H) : πb φ x = π φ x := rfl
@[scoped simp] theorem ιb_apply (y : Q φ) : ιb φ y = ι φ y := rfl

end HopfAlgebra.ImageFactor
p2m_reactivate "P2MW.S_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq.HopfAlgebra P2MW.S_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq.HopfAlgebra.ImageFactor"
p2m_reactivate "P2MW.S_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq.HopfAlgebra P2MW.S_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq.HopfAlgebra.ImageFactor"

open HopfAlgebra.ImageFactor in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H]
    {H' : Type v} [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (φ : H →ₐc[R] H') :
    ∃ (Q : Type v) (_ : CommRing Q) (_ : HopfAlgebra R Q) (_ : Module.Finite R Q) (_ : Module.Flat R Q)
      (π : H →ₐc[R] Q) (ι : Q →ₐc[R] H'),
      Function.Surjective π ∧ Function.Injective ι ∧ ι.comp π = φ :=
  ⟨Q φ, inferInstance, hopfQ φ, moduleFinite φ, flat φ, πb φ, ιb φ,
    π_surjective φ, ι_injective φ, DFunLike.ext _ _ fun x => rfl⟩

end S_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq
end P2MW
export P2MW.S_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq (solution)
