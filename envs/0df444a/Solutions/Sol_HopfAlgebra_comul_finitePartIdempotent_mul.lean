-- Prove2me | solution 1 for HopfAlgebra.comul_finitePartIdempotent_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/98a15952-cc44-52de-913c-2d0b94f0cc7e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_comul_finitePartIdempotent_mul
set_option maxHeartbeats 1600000

open scoped TensorProduct

open IsLocalRing

namespace FinitePart

section Away
variable {H : Type*} [CommRing H]

theorem algebraMap_eq_one_of_isIdempotentElem {e : H} (he : IsIdempotentElem e)
    (L : Type*) [CommRing L] [Algebra H L] [IsLocalization.Away e L] : algebraMap H L e = 1 := by
  have hu : IsUnit (algebraMap H L e) := IsLocalization.Away.algebraMap_isUnit e
  apply hu.mul_left_cancel
  rw [← map_mul, he.eq, mul_one]

theorem algebraMap_surjective_of_isIdempotentElem {e : H} (he : IsIdempotentElem e)
    (L : Type*) [CommRing L] [Algebra H L] [IsLocalization.Away e L] : Function.Surjective (algebraMap H L) := by
  intro x
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers e) x
  refine ⟨r, ?_⟩
  obtain ⟨n, hn⟩ := s.2
  symm
  rw [IsLocalization.mk'_eq_iff_eq_mul, ← hn, map_pow, algebraMap_eq_one_of_isIdempotentElem he L, one_pow, mul_one]

theorem eq_zero_of_subsingleton_away {g : H} (hg : IsIdempotentElem g)
    (L : Type*) [CommRing L] [Algebra H L] [IsLocalization.Away g L] [Subsingleton L] : g = 0 := by
  have h : algebraMap H L 1 = algebraMap H L 0 := Subsingleton.elim _ _
  obtain ⟨⟨c, n, rfl⟩, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers g) L).1 h
  simp only [mul_one, mul_zero] at hc

  rcases n with _ | n
  · rw [pow_zero] at hc
    rw [← mul_one g, hc, mul_zero]
  · rw [← hg.pow_succ_eq n, hc]

end Away

section Local
variable {R : Type*} [CommRing R] [IsLocalRing R] {H : Type*} [CommRing H] [Algebra R H]

theorem mul_eq_zero_of_finite_away_of_map_maximalIdeal_eq_top {e f : H}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hfin : Module.Finite R (Localization.Away e))
    (hgen : Ideal.map (algebraMap R (Localization.Away f)) (maximalIdeal R) = ⊤) : e * f = 0 := by
  have hg : IsIdempotentElem (e * f) := he.mul hf
  let L := Localization.Away (e * f)

  have hue : IsUnit (algebraMap H L e) := by
    have h := IsLocalization.Away.algebraMap_isUnit (S := L) (e * f)
    rw [map_mul] at h
    exact isUnit_of_mul_isUnit_left h
  have huf : IsUnit (algebraMap H L f) := by
    have h := IsLocalization.Away.algebraMap_isUnit (S := L) (e * f)
    rw [map_mul] at h
    exact isUnit_of_mul_isUnit_right h

  let φe : Localization.Away e →+* L := IsLocalization.Away.lift e hue
  let φf : Localization.Away f →+* L := IsLocalization.Away.lift f huf
  have hφe : ∀ h : H, φe (algebraMap H _ h) = algebraMap H L h := fun h => IsLocalization.Away.lift_eq e hue h
  have hφf : ∀ h : H, φf (algebraMap H _ h) = algebraMap H L h := fun h => IsLocalization.Away.lift_eq f huf h
  have hφeR : ∀ r : R, φe (algebraMap R _ r) = algebraMap R L r := fun r => by
    rw [IsScalarTower.algebraMap_apply R H (Localization.Away e), hφe, ← IsScalarTower.algebraMap_apply]
  have hφfR : ∀ r : R, φf (algebraMap R _ r) = algebraMap R L r := fun r => by
    rw [IsScalarTower.algebraMap_apply R H (Localization.Away f), hφf, ← IsScalarTower.algebraMap_apply]

  let ψ : Localization.Away e →ₗ[R] L :=
    { toFun := φe
      map_add' := fun x y => map_add φe x y
      map_smul' := fun r x => by
        simp only [Algebra.smul_def, map_mul, hφeR, RingHom.id_apply] }
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨h, rfl⟩ := algebraMap_surjective_of_isIdempotentElem hg L x
    exact ⟨algebraMap H _ h, hφe h⟩
  haveI : Module.Finite R L := Module.Finite.of_surjective ψ hψ

  have hgenL : Ideal.map (algebraMap R L) (maximalIdeal R) = ⊤ := by
    have h1 : Ideal.map φf (Ideal.map (algebraMap R (Localization.Away f)) (maximalIdeal R)) = ⊤ := by
      rw [hgen, Ideal.map_top]
    rw [Ideal.map_map] at h1
    have h2 : φf.comp (algebraMap R (Localization.Away f)) = algebraMap R L := RingHom.ext hφfR
    rwa [h2] at h1
  have htop : (⊤ : Submodule R L) ≤ maximalIdeal R • (⊤ : Submodule R L) := by
    rw [Ideal.smul_top_eq_map, hgenL]
    intro x _
    trivial

  have hbot : (⊤ : Submodule R L) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) ⊤ Module.Finite.fg_top htop
      (maximalIdeal_le_jacobson ⊥)
  haveI : Subsingleton L := by
    refine ⟨fun x y => ?_⟩
    have hx : x ∈ (⊤ : Submodule R L) := trivial
    have hy : y ∈ (⊤ : Submodule R L) := trivial
    rw [hbot, Submodule.mem_bot] at hx hy
    rw [hx, hy]
  exact eq_zero_of_subsingleton_away hg L

theorem finitePartIdempotent_unique (e e' : H) (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (hfin : Module.Finite R (Localization.Away e)) (hfin' : Module.Finite R (Localization.Away e'))
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (maximalIdeal R) = ⊤)
    (hgen' : Ideal.map (algebraMap R (Localization.Away (1 - e'))) (maximalIdeal R) = ⊤) :
    e = e' := by
  have h1 : e * (1 - e') = 0 :=
    mul_eq_zero_of_finite_away_of_map_maximalIdeal_eq_top he he'.one_sub hfin hgen'
  have h2 : e' * (1 - e) = 0 :=
    mul_eq_zero_of_finite_away_of_map_maximalIdeal_eq_top he' he.one_sub hfin' hgen
  have h1' : e = e * e' := by
    have := h1; rw [mul_sub, mul_one, sub_eq_zero] at this; exact this
  have h2' : e' = e' * e := by
    have := h2; rw [mul_sub, mul_one, sub_eq_zero] at this; exact this
  rw [h1', mul_comm, ← h2']

end Local

end FinitePart

section Counit
open IsLocalRing
variable {R : Type*} [CommRing R] [IsLocalRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]

theorem FinitePart.counit_eq_one {e : H} (he : IsIdempotentElem e)
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (maximalIdeal R) = ⊤) :
    Coalgebra.counit (R := R) e = 1 := by

  set c : R := Coalgebra.counit (R := R) e with hc
  have hcid : IsIdempotentElem c := by
    change c * c = c
    rw [hc, ← Bialgebra.counitAlgHom_apply, ← map_mul, he.eq]
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with hu | hu
  ·
    exact hu.mul_left_cancel (by rw [hcid.eq, mul_one])
  ·
    exfalso
    have hc0 : c = 0 := by
      have h := hu.mul_left_cancel (show (1 - c) * c = (1 - c) * 0 by
        rw [mul_zero, sub_mul, one_mul, hcid.eq, sub_self])
      exact h

    have hunit : IsUnit (Bialgebra.counitAlgHom R H (1 - e)) := by
      rw [map_sub, map_one, Bialgebra.counitAlgHom_apply, ← hc, hc0, sub_zero]
      exact isUnit_one
    let ε' : Localization.Away (1 - e) →+* R :=
      IsLocalization.Away.lift (1 - e) (g := (Bialgebra.counitAlgHom R H : H →+* R)) hunit
    have hε' : ∀ r : R, ε' (algebraMap R (Localization.Away (1 - e)) r) = r := fun r => by
      rw [IsScalarTower.algebraMap_apply R H (Localization.Away (1 - e)), IsLocalization.Away.lift_eq]
      exact (Bialgebra.counitAlgHom R H).commutes r
    have h1 : Ideal.map ε' (Ideal.map (algebraMap R (Localization.Away (1 - e))) (maximalIdeal R)) = ⊤ := by
      rw [hgen, Ideal.map_top]
    rw [Ideal.map_map, show ε'.comp (algebraMap R (Localization.Away (1 - e))) = RingHom.id R from RingHom.ext hε',
      Ideal.map_id] at h1
    exact (maximalIdeal.isMaximal R).ne_top h1

end Counit

section MapAlong
open IsLocalRing
variable {R : Type*} [CommRing R] {H H' : Type*} [CommRing H] [CommRing H'] [Algebra R H] [Algebra R H']

noncomputable def FinitePart.awayMapAlong (φ : H →ₐ[R] H') (g : H) :
    Localization.Away g →+* Localization.Away (φ g) :=
  IsLocalization.Away.lift g
    (g := ((algebraMap H' (Localization.Away (φ g))).comp (φ : H →+* H')))
    (by
      rw [RingHom.comp_apply]
      exact IsLocalization.Away.algebraMap_isUnit (φ g))

theorem FinitePart.awayMapAlong_algebraMap (φ : H →ₐ[R] H') (g : H) (h : H) :
    FinitePart.awayMapAlong φ g (algebraMap H _ h) = algebraMap H' _ (φ h) :=
  IsLocalization.Away.lift_eq g _ h

theorem FinitePart.awayMapAlong_algebraMap_base (φ : H →ₐ[R] H') (g : H) (r : R) :
    FinitePart.awayMapAlong φ g (algebraMap R _ r) = algebraMap R _ r := by
  rw [IsScalarTower.algebraMap_apply R H (Localization.Away g), FinitePart.awayMapAlong_algebraMap, AlgHom.commutes,
    ← IsScalarTower.algebraMap_apply]

theorem FinitePart.finite_away_map (φ : H →ₐ[R] H') (hφ : Function.Surjective φ) {g : H}
    (hg : IsIdempotentElem g) (hfin : Module.Finite R (Localization.Away g)) :
    Module.Finite R (Localization.Away (φ g)) := by
  let ψ : Localization.Away g →ₗ[R] Localization.Away (φ g) :=
    { toFun := FinitePart.awayMapAlong φ g
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => by
        simp only [Algebra.smul_def, map_mul, FinitePart.awayMapAlong_algebraMap_base, RingHom.id_apply] }
  refine Module.Finite.of_surjective ψ fun x => ?_
  obtain ⟨h', rfl⟩ := FinitePart.algebraMap_surjective_of_isIdempotentElem (hg.map φ) (Localization.Away (φ g)) x
  obtain ⟨h, rfl⟩ := hφ h'
  exact ⟨algebraMap H _ h, FinitePart.awayMapAlong_algebraMap φ g h⟩

theorem FinitePart.map_maximalIdeal_away_map [IsLocalRing R] (φ : H →ₐ[R] H') (g : H)
    (hgen : Ideal.map (algebraMap R (Localization.Away g)) (maximalIdeal R) = ⊤) :
    Ideal.map (algebraMap R (Localization.Away (φ g))) (maximalIdeal R) = ⊤ := by
  have h1 : Ideal.map (FinitePart.awayMapAlong φ g) (Ideal.map (algebraMap R (Localization.Away g)) (maximalIdeal R)) = ⊤ := by
    rw [hgen, Ideal.map_top]
  rwa [Ideal.map_map, show (FinitePart.awayMapAlong φ g).comp (algebraMap R (Localization.Away g))
      = algebraMap R (Localization.Away (φ g)) from RingHom.ext (FinitePart.awayMapAlong_algebraMap_base φ g)] at h1

end MapAlong

section Antipode
open IsLocalRing HopfAlgebra

variable {R : Type*} [CommRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]

noncomputable def FinitePart.antipodeAlgHom : H →ₐ[R] H :=
  AlgHom.ofLinearMap (HopfAlgebraStruct.antipode R) antipode_one (fun a b => by rw [antipode_mul, mul_comm])

@[scoped simp] theorem FinitePart.antipodeAlgHom_apply (a : H) :
    FinitePart.antipodeAlgHom (R := R) a = HopfAlgebraStruct.antipode R a := rfl

p2m_reactivate "P2MW.S_HopfAlgebra_comul_finitePartIdempotent_mul.FinitePart"

theorem FinitePart.lift_eq_mul'_map (f g : H →ₐ[R] H) (z : H ⊗[R] H) :
    Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) z
      = LinearMap.mul' R H (TensorProduct.map f.toLinearMap g.toLinearMap z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => rw [Algebra.TensorProduct.lift_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply]; rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem FinitePart.toConv_id_mul_toConv_antipode :
    WithConv.toConv (AlgHom.id R H) * WithConv.toConv (FinitePart.antipodeAlgHom (R := R) (H := H)) = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro a
  rw [AlgHom.convMul_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv, AlgHom.convOne_apply,
    FinitePart.lift_eq_mul'_map]
  have : TensorProduct.map (AlgHom.id R H).toLinearMap (FinitePart.antipodeAlgHom (R := R) (H := H)).toLinearMap
      = LinearMap.lTensor H (HopfAlgebraStruct.antipode R) := by
    apply TensorProduct.ext'
    intro x y
    rfl
  rw [this]
  exact HopfAlgebra.mul_antipode_lTensor_comul_apply (R := R) a

theorem FinitePart.toConv_antipode_mul_toConv_antipode_comp :
    WithConv.toConv (FinitePart.antipodeAlgHom (R := R) (H := H))
      * WithConv.toConv ((FinitePart.antipodeAlgHom (R := R) (H := H)).comp FinitePart.antipodeAlgHom) = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro a
  rw [AlgHom.convMul_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv, AlgHom.convOne_apply]
  have key : ∀ z : H ⊗[R] H,
      Algebra.TensorProduct.lift (FinitePart.antipodeAlgHom (R := R) (H := H))
          ((FinitePart.antipodeAlgHom (R := R) (H := H)).comp FinitePart.antipodeAlgHom) (fun _ _ => Commute.all _ _) z
        = FinitePart.antipodeAlgHom (R := R)
          (Algebra.TensorProduct.lift (AlgHom.id R H) FinitePart.antipodeAlgHom (fun _ _ => Commute.all _ _) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y => rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul, map_mul]; rfl
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  rw [key]
  have h1 := FinitePart.toConv_id_mul_toConv_antipode (R := R) (H := H)
  have h1a := congrArg (fun ψ : WithConv (H →ₐ[R] H) => ψ.ofConv a) h1
  rw [AlgHom.convMul_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv, AlgHom.convOne_apply] at h1a
  rw [h1a, AlgHom.commutes]

theorem FinitePart.antipode_antipode (a : H) :
    HopfAlgebraStruct.antipode R (HopfAlgebraStruct.antipode R a) = a := by
  have h1 := FinitePart.toConv_id_mul_toConv_antipode (R := R) (H := H)
  have h2 := FinitePart.toConv_antipode_mul_toConv_antipode_comp (R := R) (H := H)
  have h3 : WithConv.toConv ((FinitePart.antipodeAlgHom (R := R) (H := H)).comp FinitePart.antipodeAlgHom)
      = WithConv.toConv (AlgHom.id R H) := by
    calc WithConv.toConv ((FinitePart.antipodeAlgHom (R := R) (H := H)).comp FinitePart.antipodeAlgHom)
        = (WithConv.toConv (AlgHom.id R H) * WithConv.toConv (FinitePart.antipodeAlgHom (R := R) (H := H)))
            * WithConv.toConv ((FinitePart.antipodeAlgHom (R := R) (H := H)).comp FinitePart.antipodeAlgHom) := by
          rw [h1, one_mul]
      _ = WithConv.toConv (AlgHom.id R H) := by rw [mul_assoc, h2, mul_one]
  have h4 := congrArg (fun ψ : WithConv (H →ₐ[R] H) => ψ.ofConv a) h3
  simpa using h4

theorem FinitePart.antipode_surjective : Function.Surjective (HopfAlgebraStruct.antipode R (A := H)) :=
  fun a => ⟨HopfAlgebraStruct.antipode R a, FinitePart.antipode_antipode a⟩

variable [IsLocalRing R]

theorem FinitePart.antipode_eq_self {e : H} (he : IsIdempotentElem e)
    (hfin : Module.Finite R (Localization.Away e))
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (maximalIdeal R) = ⊤) :
    HopfAlgebraStruct.antipode R e = e := by
  let S : H →ₐ[R] H := FinitePart.antipodeAlgHom
  have hS : Function.Surjective S := FinitePart.antipode_surjective
  have h1 : Module.Finite R (Localization.Away (S e)) := FinitePart.finite_away_map S hS he hfin
  have h2 : Ideal.map (algebraMap R (Localization.Away (1 - S e))) (maximalIdeal R) = ⊤ := by
    have := FinitePart.map_maximalIdeal_away_map S (1 - e) hgen
    rwa [map_sub, map_one] at this
  exact FinitePart.finitePartIdempotent_unique _ _ (he.map S) he h1 hfin h2 hgen

end Antipode
p2m_reactivate "P2MW.S_HopfAlgebra_comul_finitePartIdempotent_mul.FinitePart"

section Galois
open HopfAlgebra

variable {R : Type*} [CommRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]

namespace FinitePart

theorem comp_convMul_ofConv {C A B : Type*} [CommRing C] [Bialgebra R C] [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (ψ : A →ₐ[R] B) (f g : WithConv (C →ₐ[R] A)) :
    ψ.comp (f * g).ofConv = (WithConv.toConv (ψ.comp f.ofConv) * WithConv.toConv (ψ.comp g.ofConv)).ofConv := by
  apply AlgHom.ext
  intro c
  rw [AlgHom.comp_apply, AlgHom.convMul_apply, AlgHom.convMul_apply, WithConv.ofConv_toConv,
    WithConv.ofConv_toConv]
  generalize CoalgebraStruct.comul (R := R) c = z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => simp only [Algebra.TensorProduct.lift_tmul, map_mul, AlgHom.comp_apply]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem comp_convOne_ofConv {C A B : Type*} [CommRing C] [Bialgebra R C] [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (ψ : A →ₐ[R] B) :
    ψ.comp (1 : WithConv (C →ₐ[R] A)).ofConv = (1 : WithConv (C →ₐ[R] B)).ofConv := by
  apply AlgHom.ext
  intro c
  rw [AlgHom.comp_apply, AlgHom.convOne_apply, AlgHom.convOne_apply, AlgHom.commutes]

theorem toConv_antipode_mul_toConv_id :
    WithConv.toConv (FinitePart.antipodeAlgHom (R := R) (H := H)) * WithConv.toConv (AlgHom.id R H) = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro a
  rw [AlgHom.convMul_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv, AlgHom.convOne_apply,
    FinitePart.lift_eq_mul'_map]
  have : TensorProduct.map (FinitePart.antipodeAlgHom (R := R) (H := H)).toLinearMap (AlgHom.id R H).toLinearMap
      = LinearMap.rTensor H (HopfAlgebraStruct.antipode R) := by
    apply TensorProduct.ext'
    intro x y
    rfl
  rw [this]
  exact HopfAlgebra.mul_antipode_rTensor_comul_apply (R := R) a

local notation "L" => (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H)
local notation "Rg" => (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H)
local notation "Sₐ" => (FinitePart.antipodeAlgHom (R := R) (H := H))

theorem toConv_comulAlgHom_eq :
    WithConv.toConv (Bialgebra.comulAlgHom R H) = WithConv.toConv L * WithConv.toConv Rg := by
  apply WithConv.ext
  apply AlgHom.ext
  intro a
  rw [WithConv.ofConv_toConv, AlgHom.convMul_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv,
    Bialgebra.comulAlgHom_apply]
  generalize CoalgebraStruct.comul (R := R) a = z
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero]
  | tmul x y =>
      rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add a b ha hb => rw [map_add, ← ha, ← hb]

theorem toConv_includeLeft_comp_antipode_mul :
    WithConv.toConv ((L).comp Sₐ) * WithConv.toConv L = 1 := by
  have h := congrArg (fun φ : WithConv (H →ₐ[R] H) => WithConv.toConv ((L).comp φ.ofConv))
    (toConv_antipode_mul_toConv_id (R := R) (H := H))
  rw [comp_convMul_ofConv, WithConv.toConv_ofConv, WithConv.ofConv_toConv, WithConv.ofConv_toConv,
    comp_convOne_ofConv, WithConv.toConv_ofConv] at h
  simpa using h

theorem toConv_includeRight_mul_comp_antipode :
    WithConv.toConv Rg * WithConv.toConv ((Rg).comp Sₐ) = 1 := by
  have h := congrArg (fun φ : WithConv (H →ₐ[R] H) => WithConv.toConv ((Rg).comp φ.ofConv))
    (FinitePart.toConv_id_mul_toConv_antipode (R := R) (H := H))
  rw [comp_convMul_ofConv, WithConv.toConv_ofConv, WithConv.ofConv_toConv, WithConv.ofConv_toConv,
    comp_convOne_ofConv, WithConv.toConv_ofConv] at h
  simpa using h

noncomputable def gal₁ : H ⊗[R] H →ₐ[R] H ⊗[R] H :=
  Algebra.TensorProduct.lift L (Bialgebra.comulAlgHom R H) (fun _ _ => Commute.all _ _)

noncomputable def gal₂ : H ⊗[R] H →ₐ[R] H ⊗[R] H :=
  Algebra.TensorProduct.lift (Bialgebra.comulAlgHom R H) Rg (fun _ _ => Commute.all _ _)

theorem gal₁_tmul (a b : H) : gal₁ (R := R) (a ⊗ₜ[R] b) = (a ⊗ₜ[R] 1) * CoalgebraStruct.comul (R := R) b :=
  Algebra.TensorProduct.lift_tmul _ _ _ a b

theorem gal₂_tmul (a b : H) : gal₂ (R := R) (a ⊗ₜ[R] b) = CoalgebraStruct.comul (R := R) a * (1 ⊗ₜ[R] b) :=
  Algebra.TensorProduct.lift_tmul _ _ _ a b

theorem gal₁_map_antipode_comul (b : H) :
    gal₁ (R := R) (TensorProduct.map (Sₐ).toLinearMap LinearMap.id (CoalgebraStruct.comul (R := R) b)) = 1 ⊗ₜ[R] b := by
  have key : ∀ z : H ⊗[R] H, gal₁ (R := R) (TensorProduct.map (Sₐ).toLinearMap LinearMap.id z)
      = Algebra.TensorProduct.lift ((L).comp Sₐ) (Bialgebra.comulAlgHom R H) (fun _ _ => Commute.all _ _) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y => rw [TensorProduct.map_tmul, gal₁, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [key]
  have h : WithConv.toConv ((L).comp Sₐ) * WithConv.toConv (Bialgebra.comulAlgHom R H) = WithConv.toConv Rg := by
    rw [toConv_comulAlgHom_eq, ← mul_assoc, toConv_includeLeft_comp_antipode_mul, one_mul]
  have h' := congrArg (fun φ : WithConv (H →ₐ[R] H ⊗[R] H) => φ.ofConv b) h
  dsimp only at h'
  rw [AlgHom.convMul_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv] at h'
  rw [h', Algebra.TensorProduct.includeRight_apply]

theorem gal₂_map_comul_antipode (a : H) :
    gal₂ (R := R) (TensorProduct.map LinearMap.id (Sₐ).toLinearMap (CoalgebraStruct.comul (R := R) a)) = a ⊗ₜ[R] 1 := by
  have key : ∀ z : H ⊗[R] H, gal₂ (R := R) (TensorProduct.map LinearMap.id (Sₐ).toLinearMap z)
      = Algebra.TensorProduct.lift (Bialgebra.comulAlgHom R H) ((Rg).comp Sₐ) (fun _ _ => Commute.all _ _) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y => rw [TensorProduct.map_tmul, gal₂, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [key]
  have h : WithConv.toConv (Bialgebra.comulAlgHom R H) * WithConv.toConv ((Rg).comp Sₐ) = WithConv.toConv L := by
    rw [toConv_comulAlgHom_eq, mul_assoc, toConv_includeRight_mul_comp_antipode, mul_one]
  have h' := congrArg (fun φ : WithConv (H →ₐ[R] H ⊗[R] H) => φ.ofConv a) h
  dsimp only at h'
  rw [AlgHom.convMul_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv] at h'
  rw [h', Algebra.TensorProduct.includeLeft_apply]

theorem gal₁_surjective : Function.Surjective (gal₁ (R := R) (H := H)) := by
  have h1 : ∀ a : H, a ⊗ₜ[R] (1 : H) ∈ (gal₁ (R := R) (H := H)).range := fun a =>
    ⟨a ⊗ₜ[R] 1, show gal₁ (a ⊗ₜ[R] 1) = a ⊗ₜ[R] 1 by
      rw [gal₁_tmul, Bialgebra.comul_one, mul_one]⟩
  have h2 : ∀ b : H, (1 : H) ⊗ₜ[R] b ∈ (gal₁ (R := R) (H := H)).range := fun b =>
    ⟨_, show gal₁ _ = _ from gal₁_map_antipode_comul b⟩
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a b =>
      have : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : H)) * ((1 : H) ⊗ₜ[R] b) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this]
      exact Subalgebra.mul_mem _ (h1 a) (h2 b)
  | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', show _ = _ from map_add _ _ _⟩

theorem gal₂_surjective : Function.Surjective (gal₂ (R := R) (H := H)) := by
  have h1 : ∀ a : H, a ⊗ₜ[R] (1 : H) ∈ (gal₂ (R := R) (H := H)).range := fun a =>
    ⟨_, show gal₂ _ = _ from gal₂_map_comul_antipode a⟩
  have h2 : ∀ b : H, (1 : H) ⊗ₜ[R] b ∈ (gal₂ (R := R) (H := H)).range := fun b =>
    ⟨1 ⊗ₜ[R] b, show gal₂ ((1 : H) ⊗ₜ[R] b) = 1 ⊗ₜ[R] b by
      rw [gal₂_tmul, Bialgebra.comul_one, one_mul]⟩
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a b =>
      have : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : H)) * ((1 : H) ⊗ₜ[R] b) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this]
      exact Subalgebra.mul_mem _ (h1 a) (h2 b)
  | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', show _ = _ from map_add _ _ _⟩

end FinitePart
p2m_reactivate "P2MW.S_HopfAlgebra_comul_finitePartIdempotent_mul.FinitePart"
end Galois
p2m_reactivate "P2MW.S_HopfAlgebra_comul_finitePartIdempotent_mul.FinitePart"

section DeltaMain
open IsLocalRing HopfAlgebra

namespace FinitePart

variable {R : Type*} [CommRing R]

theorem map_maximalIdeal_eq_top_of_ringHom [IsLocalRing R] {L₁ L₂ : Type*} [CommRing L₁] [CommRing L₂]
    [Algebra R L₁] [Algebra R L₂] (φ : L₁ →+* L₂) (hφ : ∀ r, φ (algebraMap R L₁ r) = algebraMap R L₂ r)
    (h : Ideal.map (algebraMap R L₁) (maximalIdeal R) = ⊤) : Ideal.map (algebraMap R L₂) (maximalIdeal R) = ⊤ := by
  have h1 : Ideal.map φ (Ideal.map (algebraMap R L₁) (maximalIdeal R)) = ⊤ := by rw [h, Ideal.map_top]
  rwa [Ideal.map_map, show φ.comp (algebraMap R L₁) = algebraMap R L₂ from RingHom.ext hφ] at h1

variable {H : Type*} [CommRing H]

theorem map_maximalIdeal_away_of_dvd [IsLocalRing R] [Algebra R H] {A : Type*} [CommRing A] [Algebra R A]
    (ψ : H →ₐ[R] A) (g : H) (F : A) (hdiv : ψ g ∣ F)
    (hgen : Ideal.map (algebraMap R (Localization.Away g)) (maximalIdeal R) = ⊤) :
    Ideal.map (algebraMap R (Localization.Away F)) (maximalIdeal R) = ⊤ := by
  have hunit : IsUnit ((algebraMap A (Localization.Away F)).comp (ψ : H →+* A) g) := by
    rw [RingHom.comp_apply]
    obtain ⟨c, hc⟩ := hdiv
    have hF : IsUnit (algebraMap A (Localization.Away F) F) := IsLocalization.Away.algebraMap_isUnit F
    have hsplit : algebraMap A (Localization.Away F) F
        = algebraMap A (Localization.Away F) (ψ g) * algebraMap A (Localization.Away F) c := by
      rw [← map_mul, ← hc]
    rw [hsplit] at hF
    exact isUnit_of_mul_isUnit_left hF
  refine map_maximalIdeal_eq_top_of_ringHom (IsLocalization.Away.lift g hunit) (fun r => ?_) hgen
  rw [IsScalarTower.algebraMap_apply R H (Localization.Away g), IsLocalization.Away.lift_eq, RingHom.comp_apply,
    AlgHom.coe_toRingHom, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

theorem finite_away_tmul [Algebra R H] {e : H} (he : IsIdempotentElem e)
    (hfin : Module.Finite R (Localization.Away e)) :
    Module.Finite R (Localization.Away (e ⊗ₜ[R] e : H ⊗[R] H)) := by
  let A := H ⊗[R] H
  let T := Localization.Away (e ⊗ₜ[R] e : H ⊗[R] H)
  have hee : IsIdempotentElem (e ⊗ₜ[R] e : H ⊗[R] H) := by
    change (e ⊗ₜ[R] e) * (e ⊗ₜ[R] e) = e ⊗ₜ[R] e
    rw [Algebra.TensorProduct.tmul_mul_tmul, he.eq]
  have hU : IsUnit (algebraMap A T (e ⊗ₜ[R] e)) := IsLocalization.Away.algebraMap_isUnit _
  have hsplit : algebraMap A T (e ⊗ₜ[R] e) = algebraMap A T (e ⊗ₜ[R] (1 : H)) * algebraMap A T ((1 : H) ⊗ₜ[R] e) := by
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have huL : IsUnit ((algebraMap A T).comp (Algebra.TensorProduct.includeLeft : H →ₐ[R] A).toRingHom e) := by
    rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.includeLeft_apply]
    rw [hsplit] at hU
    exact isUnit_of_mul_isUnit_left hU
  have huR : IsUnit ((algebraMap A T).comp (Algebra.TensorProduct.includeRight : H →ₐ[R] A).toRingHom e) := by
    rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.includeRight_apply]
    rw [hsplit] at hU
    exact isUnit_of_mul_isUnit_right hU

  let θL' : Localization.Away e →+* T := IsLocalization.Away.lift e huL
  let θR' : Localization.Away e →+* T := IsLocalization.Away.lift e huR
  have hθL : ∀ h : H, θL' (algebraMap H _ h) = algebraMap A T (h ⊗ₜ[R] 1) := fun h => IsLocalization.Away.lift_eq e huL h
  have hθR : ∀ h : H, θR' (algebraMap H _ h) = algebraMap A T (1 ⊗ₜ[R] h) := fun h => IsLocalization.Away.lift_eq e huR h
  have hθLR : ∀ r : R, θL' (algebraMap R _ r) = algebraMap R T r := fun r => by
    rw [IsScalarTower.algebraMap_apply R H (Localization.Away e), hθL, ← Algebra.TensorProduct.includeLeft_apply (S := R),
      AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  have hθRR : ∀ r : R, θR' (algebraMap R _ r) = algebraMap R T r := fun r => by
    rw [IsScalarTower.algebraMap_apply R H (Localization.Away e), hθR,
      ← Algebra.TensorProduct.includeRight_apply, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  let θL : Localization.Away e →ₐ[R] T := { toRingHom := θL', commutes' := hθLR }
  let θR : Localization.Away e →ₐ[R] T := { toRingHom := θR', commutes' := hθRR }
  let θ : Localization.Away e ⊗[R] Localization.Away e →ₐ[R] T :=
    Algebra.TensorProduct.lift θL θR (fun _ _ => Commute.all _ _)

  have hθ : ∀ z : A, θ (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R H (Localization.Away e))
      (IsScalarTower.toAlgHom R H (Localization.Away e)) z) = algebraMap A T z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b =>
        rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul]
        change θL' (algebraMap H _ a) * θR' (algebraMap H _ b) = _
        rw [hθL, hθR, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine Module.Finite.of_surjective θ.toLinearMap fun t => ?_
  obtain ⟨z, rfl⟩ := FinitePart.algebraMap_surjective_of_isIdempotentElem hee T t
  exact ⟨_, hθ z⟩

end FinitePart
p2m_reactivate "P2MW.S_HopfAlgebra_comul_finitePartIdempotent_mul.FinitePart"
end DeltaMain
p2m_reactivate "P2MW.S_HopfAlgebra_comul_finitePartIdempotent_mul.FinitePart"

section DeltaCard
open IsLocalRing HopfAlgebra

namespace FinitePart
variable {R : Type*} [CommRing R] [IsLocalRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]

local notation "L" => (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H)
local notation "Rg" => (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H)

omit [IsLocalRing R] in
theorem isIdempotentElem_tmul {a b : H} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) :
    IsIdempotentElem (a ⊗ₜ[R] b : H ⊗[R] H) := by
  change (a ⊗ₜ[R] b) * (a ⊗ₜ[R] b) = a ⊗ₜ[R] b
  rw [Algebra.TensorProduct.tmul_mul_tmul, ha.eq, hb.eq]

set_option maxHeartbeats 3200000 in
theorem comul_mul_tmul_of_finitePart {e : H} (he : IsIdempotentElem e)
    (hfin : Module.Finite R (Localization.Away e))
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (maximalIdeal R) = ⊤) :
    CoalgebraStruct.comul (R := R) e * (e ⊗ₜ[R] 1) = e ⊗ₜ[R] e ∧
      CoalgebraStruct.comul (R := R) e * (1 ⊗ₜ[R] e) = e ⊗ₜ[R] e := by
  set Δe := CoalgebraStruct.comul (R := R) e with hΔe_def
  have h1e : IsIdempotentElem (1 - e) := he.one_sub
  have hee : IsIdempotentElem (e ⊗ₜ[R] e : H ⊗[R] H) := isIdempotentElem_tmul he he
  have hΔe : IsIdempotentElem Δe := he.map (Bialgebra.comulAlgHom R H)

  have hfin2 : Module.Finite R (Localization.Away (e ⊗ₜ[R] e : H ⊗[R] H)) := finite_away_tmul he hfin
  have hg1 : gal₁ (R := R) (e ⊗ₜ[R] e) = Δe * (e ⊗ₜ[R] 1) := by rw [gal₁_tmul, mul_comm]
  have hg2 : gal₂ (R := R) (e ⊗ₜ[R] e) = Δe * (1 ⊗ₜ[R] e) := gal₂_tmul e e
  have hfinG1 : Module.Finite R (Localization.Away (Δe * (e ⊗ₜ[R] 1))) := by
    rw [← hg1]; exact finite_away_map (gal₁ (R := R) (H := H)) gal₁_surjective hee hfin2
  have hfinG2 : Module.Finite R (Localization.Away (Δe * (1 ⊗ₜ[R] e))) := by
    rw [← hg2]; exact finite_away_map (gal₂ (R := R) (H := H)) gal₂_surjective hee hfin2
  have hidG1 : IsIdempotentElem (Δe * (e ⊗ₜ[R] 1)) := by rw [← hg1]; exact hee.map (gal₁ (R := R) (H := H))
  have hidG2 : IsIdempotentElem (Δe * (1 ⊗ₜ[R] e)) := by rw [← hg2]; exact hee.map (gal₂ (R := R) (H := H))

  have hgen1 : Ideal.map (algebraMap R (Localization.Away (e ⊗ₜ[R] (1 - e) : H ⊗[R] H))) (maximalIdeal R) = ⊤ :=
    map_maximalIdeal_away_of_dvd Rg (1 - e) _ ⟨e ⊗ₜ[R] 1, by
      rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]⟩ hgen
  have hgen2 : Ideal.map (algebraMap R (Localization.Away ((1 - e) ⊗ₜ[R] e : H ⊗[R] H))) (maximalIdeal R) = ⊤ :=
    map_maximalIdeal_away_of_dvd L (1 - e) _ ⟨1 ⊗ₜ[R] e, by
      rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]⟩ hgen
  have hgen3 : Ideal.map (algebraMap R (Localization.Away (CoalgebraStruct.comul (R := R) (1 - e))))
      (maximalIdeal R) = ⊤ := by
    have := map_maximalIdeal_away_map (Bialgebra.comulAlgHom R H) (1 - e) hgen
    rwa [Bialgebra.comulAlgHom_apply] at this

  have hA : (Δe * (e ⊗ₜ[R] 1)) * (e ⊗ₜ[R] (1 - e)) = 0 :=
    mul_eq_zero_of_finite_away_of_map_maximalIdeal_eq_top hidG1 (isIdempotentElem_tmul he h1e) hfinG1 hgen1
  have hB : (Δe * (1 ⊗ₜ[R] e)) * ((1 - e) ⊗ₜ[R] e) = 0 :=
    mul_eq_zero_of_finite_away_of_map_maximalIdeal_eq_top hidG2 (isIdempotentElem_tmul h1e he) hfinG2 hgen2
  have hC : (e ⊗ₜ[R] e : H ⊗[R] H) * CoalgebraStruct.comul (R := R) (1 - e) = 0 :=
    mul_eq_zero_of_finite_away_of_map_maximalIdeal_eq_top hee (h1e.map (Bialgebra.comulAlgHom R H)) hfin2 hgen3

  have hA' : Δe * (e ⊗ₜ[R] (1 - e)) = 0 := by
    rw [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, he.eq, one_mul] at hA
    exact hA
  have hB' : Δe * ((1 - e) ⊗ₜ[R] e) = 0 := by
    rw [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, he.eq, one_mul] at hB
    exact hB
  have hC' : (e ⊗ₜ[R] e : H ⊗[R] H) = Δe * (e ⊗ₜ[R] e) := by
    rw [map_sub, Bialgebra.comul_one, mul_sub, mul_one, sub_eq_zero, mul_comm] at hC
    exact hC
  have hsplit1 : (e ⊗ₜ[R] (1 : H)) = e ⊗ₜ[R] e + e ⊗ₜ[R] (1 - e) := by
    rw [← TensorProduct.tmul_add, add_sub_cancel]
  have hsplit2 : ((1 : H) ⊗ₜ[R] e) = e ⊗ₜ[R] e + (1 - e) ⊗ₜ[R] e := by
    rw [← TensorProduct.add_tmul, add_sub_cancel]
  constructor
  · rw [hsplit1, mul_add, hA', add_zero, ← hC']
  · rw [hsplit2, mul_add, hB', add_zero, ← hC']

end FinitePart
p2m_reactivate "P2MW.S_HopfAlgebra_comul_finitePartIdempotent_mul.FinitePart"
end DeltaCard
p2m_reactivate "P2MW.S_HopfAlgebra_comul_finitePartIdempotent_mul.FinitePart"

theorem solution
    (R : Type*) [CommRing R] [IsLocalRing R] (H : Type*) [CommRing H] [HopfAlgebra R H]
    (e : H) (he : IsIdempotentElem e)
    (hfin : Module.Finite R (Localization.Away e))
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (IsLocalRing.maximalIdeal R) = ⊤) :
    Coalgebra.comul (R := R) e * (e ⊗ₜ[R] 1) = e ⊗ₜ[R] e ∧ Coalgebra.comul (R := R) e * (1 ⊗ₜ[R] e) = e ⊗ₜ[R] e :=
  FinitePart.comul_mul_tmul_of_finitePart he hfin hgen

end S_HopfAlgebra_comul_finitePartIdempotent_mul
end P2MW
export P2MW.S_HopfAlgebra_comul_finitePartIdempotent_mul (solution)
