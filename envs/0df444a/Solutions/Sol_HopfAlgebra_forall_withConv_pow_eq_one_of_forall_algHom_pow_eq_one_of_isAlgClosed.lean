-- Prove2me | solution 1 for HopfAlgebra.forall_withConv_pow_eq_one_of_forall_algHom_pow_eq_one_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/b1c3c94e-ab14-57f8-8819-6daf38a7b8fc

import Mathlib
import Theorems.Thm_HopfAlgebra_forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one
import Theorems.Thm_HopfAlgebra_algebra_etale_of_module_finite_of_charZero
import Theorems.Thm_Algebra_Etale_natCard_algHom_eq_finrank_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_forall_withConv_pow_eq_one_of_forall_algHom_pow_eq_one_of_isAlgClosed

set_option autoImplicit false

open scoped TensorProduct

namespace S17PointsKilled

theorem comp_convOne {R : Type} [CommRing R] {H : Type} [CommRing H] [HopfAlgebra R H]
    {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (h : A →ₐ[R] B) :
    h.comp (1 : WithConv (H →ₐ[R] A)).ofConv = (1 : WithConv (H →ₐ[R] B)).ofConv := by
  apply AlgHom.ext
  intro x
  rw [AlgHom.comp_apply]
  change h ((1 : WithConv (H →ₐ[R] A)) x) = (1 : WithConv (H →ₐ[R] B)) x
  rw [AlgHom.convOne_apply, AlgHom.convOne_apply, AlgHom.commutes]

theorem comp_convPow {R : Type} [CommRing R] {H : Type} [CommRing H] [HopfAlgebra R H]
    {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (h : A →ₐ[R] B)
    (f : WithConv (H →ₐ[R] A)) (n : ℕ) :
    h.comp (f ^ n).ofConv = ((WithConv.toConv (h.comp f.ofConv)) ^ n).ofConv := by
  induction n with
  | zero => rw [pow_zero, pow_zero, comp_convOne]
  | succ n ih =>
      rw [pow_succ, pow_succ, AlgHom.comp_convMul_distrib, ih, WithConv.toConv_ofConv]

theorem eq_zero_of_forall_algHom_eq_zero
    (L : Type) [Field L] [IsAlgClosed L] (A : Type) [CommRing A] [Algebra L A]
    [Module.Finite L A] [Algebra.Etale L A] [Nontrivial A]
    (a : A) (ha : ∀ χ : A →ₐ[L] L, χ a = 0) : a = 0 := by
  classical
  have hcount : Nat.card (A →ₐ[L] L) = Module.finrank L A :=
    Algebra.Etale.natCard_algHom_eq_finrank_of_isAlgClosed L A
  haveI : Finite (A →ₐ[L] L) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcount]
    exact Module.finrank_pos.ne'
  haveI : Fintype (A →ₐ[L] L) := Fintype.ofFinite _

  let ev : A →ₗ[L] ((A →ₐ[L] L) → L) := LinearMap.pi fun χ => (χ : A →ₐ[L] L).toLinearMap
  have ev_apply : ∀ (x : A) (χ : A →ₐ[L] L), ev x χ = χ x := fun _ _ => rfl

  have hli : LinearIndependent L (fun χ : A →ₐ[L] L => ((χ : A →ₐ[L] L) : A → L)) := by
    let c : (A →ₐ[L] L) → (A →* L) := fun χ => (χ : A →ₐ[L] L).toMonoidHom
    have hc : Function.Injective c := by
      intro φ ψ h
      apply AlgHom.ext
      intro x
      exact congrArg (fun f : A →* L => f x) h
    exact (linearIndependent_monoidHom A L).comp c hc
  have hsurj : Function.Surjective ev := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨f, hf0, hfr⟩ :=
      Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
    have hker : ∀ x, f (ev x) = 0 := by
      intro x
      have : f (ev x) ∈ Submodule.map f (LinearMap.range ev) := Submodule.mem_map_of_mem ⟨x, rfl⟩
      rw [hfr] at this
      exact (Submodule.mem_bot L).mp this
    set w : (A →ₐ[L] L) → L := fun χ => f (Pi.single χ 1) with hw
    have hexp : ∀ v : (A →ₐ[L] L) → L, f v = ∑ χ, v χ * w χ := by
      intro v
      conv_lhs => rw [← Finset.univ_sum_single v]
      rw [map_sum]
      refine Finset.sum_congr rfl fun χ _ => ?_
      have : (Pi.single χ (v χ) : (A →ₐ[L] L) → L) = v χ • (Pi.single χ (1 : L) : (A →ₐ[L] L) → L) := by
        ext ψ; simp [Pi.single_apply]
      rw [this, map_smul, smul_eq_mul]
    have hrel : ∑ χ, w χ • ((χ : A →ₐ[L] L) : A → L) = 0 := by
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have := hker x
      rw [hexp] at this
      rw [← this]
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [ev_apply, mul_comm]
    have hw0 : ∀ χ, w χ = 0 := Fintype.linearIndependent_iff.mp hli w hrel
    apply hf0
    apply LinearMap.ext
    intro v
    rw [hexp v, LinearMap.zero_apply]
    exact Finset.sum_eq_zero fun χ _ => by rw [hw0 χ, mul_zero]
  have hdim : Module.finrank L A = Module.finrank L ((A →ₐ[L] L) → L) := by
    rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card, hcount]
  have hinj : Function.Injective ev :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  apply hinj
  rw [map_zero]
  funext χ
  rw [ev_apply, ha χ]
  rfl

end S17PointsKilled

open S17PointsKilled in

theorem solution
    (R : Type) [CommRing R] [IsDomain R] (H : Type) [CommRing H] [HopfAlgebra R H]
    [Module.Finite R H] [Module.Flat R H]
    (L : Type) [Field L] [IsAlgClosed L] [CharZero L] [Algebra R L]
    (hRL : Function.Injective (algebraMap R L))
    (m : ℕ) (hL : ∀ f : WithConv (H →ₐ[R] L), f ^ m = 1)
    (T : Type) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)) : f ^ m = 1 := by
  classical
  suffices hid : (WithConv.toConv (AlgHom.id R H)) ^ m = 1 from
    (HopfAlgebra.forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one m).mpr hid T f

  haveI : Nontrivial H := by
    refine ⟨⟨1, 0, fun h10 => ?_⟩⟩
    have h := Bialgebra.counit_one (R := R) (A := H)
    have : (Coalgebra.counit (R := R) (A := H)) 1 = (Coalgebra.counit (R := R) (A := H)) 0 := by rw [h10]
    rw [h, map_zero] at this
    exact one_ne_zero this

  let ι : H →ₐ[R] L ⊗[R] H := Algebra.TensorProduct.includeRight
  have hι : Function.Injective ι := Algebra.TensorProduct.includeRight_injective hRL
  haveI : Nontrivial (L ⊗[R] H) := hι.nontrivial
  haveI : Module.Finite L (L ⊗[R] H) := inferInstance
  haveI : Algebra.Etale L (L ⊗[R] H) :=
    HopfAlgebra.algebra_etale_of_module_finite_of_charZero L (L ⊗[R] H)

  have hu : (WithConv.toConv ι) ^ m = 1 := by
    apply WithConv.ext
    apply AlgHom.ext
    intro x
    rw [← sub_eq_zero]
    apply eq_zero_of_forall_algHom_eq_zero L (L ⊗[R] H)
    intro χ
    rw [map_sub, sub_eq_zero]
    have h1 : χ (((WithConv.toConv ι) ^ m).ofConv x) =
        ((χ.restrictScalars R).comp ((WithConv.toConv ι) ^ m).ofConv) x := rfl
    have h2 : χ ((1 : WithConv (H →ₐ[R] L ⊗[R] H)).ofConv x) =
        ((χ.restrictScalars R).comp (1 : WithConv (H →ₐ[R] L ⊗[R] H)).ofConv) x := rfl
    rw [h1, h2, comp_convPow, comp_convOne, WithConv.ofConv_toConv, hL]

  have key : ι.comp ((WithConv.toConv (AlgHom.id R H)) ^ m).ofConv =
      ι.comp (1 : WithConv (H →ₐ[R] H)).ofConv := by
    rw [comp_convPow, comp_convOne, WithConv.ofConv_toConv, AlgHom.comp_id, hu]
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  apply hι
  exact congrArg (fun g : H →ₐ[R] L ⊗[R] H => g x) key

#print axioms solution

end S_HopfAlgebra_forall_withConv_pow_eq_one_of_forall_algHom_pow_eq_one_of_isAlgClosed
end P2MW
export P2MW.S_HopfAlgebra_forall_withConv_pow_eq_one_of_forall_algHom_pow_eq_one_of_isAlgClosed (solution)
