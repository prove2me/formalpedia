-- Prove2me | solution 1 for ModularCurve.JZeroNeronPrimaryTorsionFFModels.exists_natCard_withConv_hffBarQ_algHom_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/b9688ab0-9437-5632-a324-a9ec91d4f277

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFFModels_exists_natCard_withConv_hffBarQ_algHom_eq_pow

p2m_open "ModularCurve P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFFModels_exists_natCard_withConv_hffBarQ_algHom_eq_pow.ModularCurve"

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open scoped TensorProduct
open Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "eisensteinPrimaryTorsionBar JZeroNeronPrimaryTorsionCore JZeroNeronPrimaryTorsionFFModels JZero"
p2m_open "ModularCurve"
namespace JZeroNeronPrimaryTorsionFFModelsAlpha

section SEP

variable {R : Type*} [CommRing R] [IsDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (Ω : Type*) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω] [Algebra K Ω]
  [IsScalarTower R K Ω] {H : Type*} [CommRing H] [Algebra R H]

theorem eq_zero_of_algebraMap_mul_eq_zero [Module.Flat R H]
    (s : R) (hs : s ≠ 0) (y : H) (hy : algebraMap R H s * y = 0) : y = 0 := by
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := H)
    (mem_nonZeroDivisors_of_ne_zero hs)
  refine hreg ?_
  change s • y = s • (0 : H)
  rw [smul_zero, Algebra.smul_def, hy]

attribute [local instance] MvPolynomial.algebraMvPolynomial

include K in

theorem isNilpotent_of_forall_algHom_apply_eq_zero [hft : Algebra.FiniteType R H]
    (htf : ∀ s : R, s ≠ 0 → ∀ y : H, algebraMap R H s * y = 0 → y = 0)
    (x : H) (hvan : ∀ g : H →ₐ[R] Ω, g x = 0) : IsNilpotent x := by
  classical
  obtain ⟨n, F, hF⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hft
  obtain ⟨P, hP⟩ := hF x
  set J : Ideal (MvPolynomial (Fin n) R) := RingHom.ker F with hJdef
  set ι : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) K :=
    algebraMap (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) K) with hιdef
  set I : Ideal (MvPolynomial (Fin n) K) := J.map ι with hIdef
  have hev : ∀ (v : Fin n → Ω) (a : MvPolynomial (Fin n) R),
      MvPolynomial.aeval v (ι a) = MvPolynomial.aeval (R := R) v a := by
    intro v a
    rw [hιdef, MvPolynomial.algebraMap_def]
    exact MvPolynomial.aeval_map_algebraMap K v a
  have hA : ι P ∈ MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus Ω I) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro v hv
    rw [MvPolynomial.mem_zeroLocus_iff] at hv
    have hJ : ∀ a ∈ J, MvPolynomial.aeval (R := R) v a = 0 := fun a ha => by
      rw [← hev]; exact hv (ι a) (Ideal.mem_map_of_mem ι ha)
    set e := Ideal.quotientKerAlgEquivOfSurjective hF with hedef
    set gv : H →ₐ[R] Ω :=
      (Ideal.Quotient.liftₐ J (MvPolynomial.aeval v) hJ).comp (e.symm : H →ₐ[R] _) with hgvdef
    have hgv : ∀ a, gv (F a) = MvPolynomial.aeval (R := R) v a := by
      intro a
      have he : e.symm (F a) = Ideal.Quotient.mk J a := by
        apply e.injective
        rw [AlgEquiv.apply_symm_apply, hedef, Ideal.quotientKerAlgEquivOfSurjective_apply]
        exact (RingHom.kerLift_mk _ _).symm
      rw [hgvdef, AlgHom.comp_apply, AlgEquiv.coe_algHom, he, Ideal.Quotient.liftₐ_apply,
        Ideal.Quotient.lift_mk]
      rfl
    calc MvPolynomial.aeval v (ι P) = MvPolynomial.aeval (R := R) v P := hev v P
      _ = gv (F P) := (hgv P).symm
      _ = gv x := by rw [hP]
      _ = 0 := hvan gv
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hA
  obtain ⟨k, hk⟩ := hA
  rw [← map_pow] at hk
  obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, has⟩ := (IsLocalization.mem_map_algebraMap_iff
    ((nonZeroDivisors R).map (MvPolynomial.C : R →+* MvPolynomial (Fin n) R))
    (MvPolynomial (Fin n) K)).1 hk
  obtain ⟨s0, hs0, rfl⟩ := Submonoid.mem_map.1 hs
  have hinj : Function.Injective ι := by
    rw [hιdef, MvPolynomial.algebraMap_def]
    exact MvPolynomial.map_injective _ (IsFractionRing.injective R K)
  have hPk : P ^ k * MvPolynomial.C s0 = a := by
    apply hinj
    rw [map_mul]
    exact has
  have hJmem : P ^ k * MvPolynomial.C s0 ∈ J := hPk ▸ ha
  have h0 : F (P ^ k * MvPolynomial.C s0) = 0 := hJmem
  have hC : F (MvPolynomial.C s0) = algebraMap R H s0 := by
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  rw [map_mul, map_pow, hP, hC, mul_comm] at h0
  exact ⟨k, htf s0 (nonZeroDivisors.ne_zero hs0) _ h0⟩

end SEP

section Engine

variable (R : Type*) [CommRing R] (H : Type*) [CommRing H] [Bialgebra R H]

def Dmap (n : ℕ) : H →ₐ[R] H :=
  ((WithConv.toConv (AlgHom.id R H)) ^ n).ofConv

variable {R H}

theorem comp_convOne {L : Type*} [CommRing L] [Algebra R L] (φ : H →ₐ[R] L) :
    φ.comp ((1 : WithConv (H →ₐ[R] H)).ofConv) = (1 : WithConv (H →ₐ[R] L)).ofConv := by
  rw [AlgHom.convOne_def, AlgHom.convOne_def, WithConv.ofConv_toConv, WithConv.ofConv_toConv,
    ← AlgHom.comp_assoc]
  congr 1
  ext

theorem toConv_pow_eq {L : Type*} [CommRing L] [Algebra R L] (φ : H →ₐ[R] L) (n : ℕ) :
    (WithConv.toConv φ) ^ n = WithConv.toConv (φ.comp (Dmap R H n)) := by
  induction n with
  | zero =>
      simp only [Dmap, pow_zero]
      rw [comp_convOne φ, WithConv.toConv_ofConv]
  | succ n ih =>
      simp only [Dmap] at ih ⊢
      rw [pow_succ, pow_succ, ih]
      rw [AlgHom.comp_convMul_distrib φ
        ((WithConv.toConv (AlgHom.id R H)) ^ n) (WithConv.toConv (AlgHom.id R H))]
      rw [WithConv.toConv_ofConv, WithConv.ofConv_toConv, AlgHom.comp_id]

theorem dmap_sub_counit_nilpotent {Ω : Type*} [CommRing Ω] [Algebra R Ω] {n : ℕ}
    (hsep : ∀ x : H, (∀ g : H →ₐ[R] Ω, g x = 0) → IsNilpotent x)
    (hΩ : ∀ φ : WithConv (H →ₐ[R] Ω), φ ^ n = 1) (x : H) :
    IsNilpotent (Dmap R H n x - algebraMap R H (Bialgebra.counitAlgHom R H x)) := by
  classical
  apply hsep
  intro φ
  have hφ : WithConv.toConv (φ.comp (Dmap R H n)) = (1 : WithConv (H →ₐ[R] Ω)) := by
    rw [← toConv_pow_eq φ n]
    exact hΩ (WithConv.toConv φ)
  have hφ' : φ.comp (Dmap R H n) = (1 : WithConv (H →ₐ[R] Ω)).ofConv := by
    rw [← hφ, WithConv.ofConv_toConv]
  have hpt : φ (Dmap R H n x) = algebraMap R Ω (Bialgebra.counitAlgHom R H x) := by
    have h := congrArg (fun f : H →ₐ[R] Ω => f x) hφ'
    simp only [AlgHom.comp_apply] at h
    rw [h, AlgHom.convOne_def, WithConv.ofConv_toConv, AlgHom.comp_apply, Algebra.ofId_apply]
  rw [map_sub, hpt, AlgHom.commutes, sub_self]

theorem withConv_pow_eq_one_of_nilpotent {L : Type*} [Field L] [Algebra R L] {n : ℕ}
    (hnil : ∀ x : H, IsNilpotent (Dmap R H n x - algebraMap R H (Bialgebra.counitAlgHom R H x)))
    (ψ : WithConv (H →ₐ[R] L)) : ψ ^ n = 1 := by
  classical
  have hψpt : ∀ x : H, ψ.ofConv (Dmap R H n x)
      = algebraMap R L (Bialgebra.counitAlgHom R H x) := by
    intro x
    have h0 : ψ.ofConv (Dmap R H n x - algebraMap R H (Bialgebra.counitAlgHom R H x)) = 0 :=
      ((hnil x).map (ψ.ofConv : H →+* L)).eq_zero
    rw [map_sub, sub_eq_zero] at h0
    rw [h0]
    exact ψ.ofConv.commutes (Bialgebra.counitAlgHom R H x)
  have hcomp : ψ.ofConv.comp (Dmap R H n) = (1 : WithConv (H →ₐ[R] L)).ofConv := by
    apply AlgHom.ext
    intro x
    rw [AlgHom.comp_apply, hψpt x, AlgHom.convOne_def, WithConv.ofConv_toConv,
      AlgHom.comp_apply, Algebra.ofId_apply]
  calc ψ ^ n = (WithConv.toConv ψ.ofConv) ^ n := by rw [WithConv.toConv_ofConv]
    _ = WithConv.toConv (ψ.ofConv.comp (Dmap R H n)) := toConv_pow_eq ψ.ofConv n
    _ = WithConv.toConv ((1 : WithConv (H →ₐ[R] L)).ofConv) := by rw [hcomp]
    _ = 1 := WithConv.toConv_ofConv _

end Engine

section Count

theorem finite_algHom_of_module_finite (R : Type*) [CommRing R] (H : Type*) [CommRing H]
    [Algebra R H] [Module.Finite R H] (L : Type*) [Field L] [Algebra R L] :
    Finite (H →ₐ[R] L) := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType R H).out
  have hint : ∀ y : H, ∃ Q : R[X], Q.Monic ∧ aeval y Q = 0 := fun y =>
    Algebra.IsIntegral.isIntegral (R := R) y
  choose Q hQm hQy using hint
  let ev : (H →ₐ[R] L) → (∀ y : ↥s, ↥((Q y.1).rootSet L)) :=
    fun ψ y => ⟨ψ y.1, by
      rw [Polynomial.mem_rootSet']
      exact ⟨((hQm y.1).map (algebraMap R L)).ne_zero,
        by rw [Polynomial.aeval_algHom_apply, hQy, map_zero]⟩⟩
  refine Finite.of_injective ev ?_
  intro ψ₁ ψ₂ h
  apply AlgHom.ext_of_adjoin_eq_top hs
  intro y hy
  exact congrArg
    (fun g : (∀ y : ↥s, ↥((Q y.1).rootSet L)) => ((g ⟨y, hy⟩ : ↥((Q y).rootSet L)) : L)) h

theorem card_pow_of_exponent (R : Type*) [CommRing R] (H : Type*) [CommRing H] [Bialgebra R H]
    (L : Type*) [Field L] [Algebra R L] (q : ℕ) [hq : Fact q.Prime] (m : ℕ)
    (hT : ∀ ψ : WithConv (H →ₐ[R] L), ψ ^ (q ^ m) = 1) (hF : Finite (H →ₐ[R] L)) :
    ∃ a : ℕ, Nat.card (H →ₐ[R] L) = q ^ a := by
  classical
  haveI hfW : Finite (WithConv (H →ₐ[R] L)) :=
    Finite.of_equiv _ (WithConv.equiv (H →ₐ[R] L)).symm
  have hcard : Nat.card (H →ₐ[R] L) = Nat.card (WithConv (H →ₐ[R] L)) :=
    (Nat.card_congr (WithConv.equiv (H →ₐ[R] L))).symm
  letI : Group (WithConv (H →ₐ[R] L)) :=
    { (inferInstance : Monoid (WithConv (H →ₐ[R] L))) with
      inv := fun x => x ^ (q ^ m - 1)
      inv_mul_cancel := fun x => by
        show x ^ (q ^ m - 1) * x = 1
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hq.out.pos)]
        exact hT x }
  have hpg : IsPGroup q (WithConv (H →ₐ[R] L)) := fun g => ⟨m, hT g⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
  exact ⟨n, hcard.trans hn⟩

end Count

section Main

open GaloisRep

variable {p q : ℕ} [Fact p.Prime] [hq : Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
    {C : JZeroNeronPrimaryTorsionCore p q A hA} (F : JZeroNeronPrimaryTorsionFFModels p q A hA C)
    (m : ℕ) (hqp : q ≠ p)

local notation "ℚbar" => AlgebraicClosure ℚ
local notation "𝔽bar" => AlgebraicClosure (ZMod q)
local notation "Rq" => GaloisRep.ratLocalizedAt q

omit hq in

theorem pow_nsmul_eq_zero (x : JZero p) (hx : x ∈ eisensteinPrimaryTorsionBar p q m) :
    (q ^ m) • x = 0 := by
  have h1 : ((q : ℤ) ^ m) • x = 0 := hx.1
  rw [← natCast_zsmul, Nat.cast_pow]
  exact h1

theorem qbar_point_pow_eq_one
    (φ : WithConv (F.Hff m q hq.out hqp →ₐ[Rq] ℚbar)) : φ ^ (q ^ m) = 1 := by
  classical
  set E := F.ffPoints m q hq.out hqp with hEdef
  have hadd : ∀ f g, E (f * g) = E f + E g := F.ffConv m q hq.out hqp
  have h1 : E 1 = 0 := by
    have h := hadd 1 1
    rw [one_mul] at h
    have h' : E 1 + 0 = E 1 + E 1 := by rw [add_zero]; exact h
    exact (add_left_cancel h').symm
  have hpow : ∀ (n : ℕ) (ψ : WithConv (F.Hff m q hq.out hqp →ₐ[Rq] ℚbar)),
      E (ψ ^ n) = n • E ψ := by
    intro n ψ
    induction n with
    | zero => rw [pow_zero, h1, zero_nsmul]
    | succ n ih => rw [pow_succ, hadd, ih, succ_nsmul]
  have htor : (q ^ m) • E φ = 0 := by
    have hc : ((q ^ m) • ((E φ : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)) = 0 :=
      pow_nsmul_eq_zero m ((E φ : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p) (E φ).2
    apply Subtype.ext
    push_cast
    exact hc
  have : E (φ ^ (q ^ m)) = E 1 := by rw [hpow, htor, h1]
  exact E.injective this

theorem dmap_sub_counit_nilpotent_hff (x : F.Hff m q hq.out hqp) :
    IsNilpotent (Dmap Rq (F.Hff m q hq.out hqp) (q ^ m) x
      - algebraMap Rq (F.Hff m q hq.out hqp)
          (Bialgebra.counitAlgHom Rq (F.Hff m q hq.out hqp) x)) := by
  haveI : IsFractionRing Rq ℚ := GaloisRep.isFractionRing_ratLocalizedAt q
  refine dmap_sub_counit_nilpotent (Ω := ℚbar) ?_ (qbar_point_pow_eq_one F m hqp) x
  intro y hy
  exact isNilpotent_of_forall_algHom_apply_eq_zero ℚ ℚbar
    (eq_zero_of_algebraMap_mul_eq_zero (R := Rq) (H := F.Hff m q hq.out hqp)) y hy

theorem point_pow_eq_one {L : Type*} [Field L] [Algebra Rq L]
    (ψ : WithConv (F.Hff m q hq.out hqp →ₐ[Rq] L)) : ψ ^ (q ^ m) = 1 :=
  withConv_pow_eq_one_of_nilpotent (dmap_sub_counit_nilpotent_hff F m hqp) ψ

theorem exists_natCard_hff_algHom_eq_pow :
    ∃ n : ℕ, Nat.card (F.Hff m q hq.out hqp →ₐ[Rq] 𝔽bar) = q ^ n :=
  card_pow_of_exponent Rq (F.Hff m q hq.out hqp) 𝔽bar q m (point_pow_eq_one F m hqp)
    (finite_algHom_of_module_finite Rq _ 𝔽bar)

theorem natCard_hffBarQ_eq :
    Nat.card (WithConv (F.HffBarQ m hqp →ₐ[ZMod q] 𝔽bar))
      = Nat.card (F.Hff m q hq.out hqp →ₐ[Rq] 𝔽bar) := by
  rw [Nat.card_congr (WithConv.equiv _)]
  refine Nat.card_congr ?_
  haveI hloc : IsLocalization.AtPrime Rq (Ideal.span {(q : ℤ)}) :=
    GaloisRep.isLocalization_ratLocalizedAt (p := q) hq.out
  let red : F.Hff m q hq.out hqp →+* F.HffBarQ m hqp := F.ffBarQ_red m hqp
  have hred_surj : Function.Surjective red := F.ffBarQ_red_surjective m hqp
  have hred_ker : RingHom.ker red = Ideal.span {((q : ℤ) : F.Hff m q hq.out hqp)} :=
    F.ffBarQ_red_ker m hqp
  haveI : IsScalarTower ℤ Rq (ZMod q) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    exact (RingHom.ext_int _ _).symm
  exact
  { toFun := fun f =>
      { toRingHom := f.toRingHom.comp red
        commutes' := fun r => by
          have key : red.comp (algebraMap Rq (F.Hff m q hq.out hqp))
              = (algebraMap (ZMod q) (F.HffBarQ m hqp)).comp (algebraMap Rq (ZMod q)) :=
            IsLocalization.ringHom_ext (M := (Ideal.span {(q:ℤ)}).primeCompl) (RingHom.ext_int _ _)
          show (f.toRingHom.comp red) (algebraMap _ _ r) = algebraMap _ _ r
          rw [← RingHom.comp_apply (f.toRingHom.comp red), RingHom.comp_assoc, key,
            ← RingHom.comp_assoc,
            show f.toRingHom.comp (algebraMap (ZMod q) (F.HffBarQ m hqp))
              = algebraMap (ZMod q) 𝔽bar from RingHom.ext fun s => f.commutes s,
            RingHom.comp_apply,
            ← IsScalarTower.algebraMap_apply Rq (ZMod q) 𝔽bar] }
    invFun := fun g =>
      let hker : RingHom.ker red ≤ RingHom.ker g.toRingHom := by
        rw [hred_ker, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
        show g ((q:ℤ) : F.Hff m q hq.out hqp) = 0
        rw [map_intCast, ← map_intCast (algebraMap (ZMod q) 𝔽bar),
          show ((q:ℤ) : ZMod q) = 0 from by exact_mod_cast ZMod.natCast_self q, map_zero]
      let ψ : F.HffBarQ m hqp →+* 𝔽bar :=
        (red.liftOfSurjective hred_surj) ⟨g.toRingHom, hker⟩
      { toRingHom := ψ
        commutes' := fun r => by
          show ψ (algebraMap (ZMod q) (F.HffBarQ m hqp) r) = algebraMap (ZMod q) _ r
          obtain ⟨n, rfl⟩ := ZMod.intCast_surjective r
          simp only [map_intCast] }
    left_inv := fun f => by
      apply AlgHom.ext
      intro b
      obtain ⟨h, rfl⟩ := hred_surj b
      exact red.liftOfSurjective_comp_apply hred_surj _ h
    right_inv := fun g => by
      apply AlgHom.ext
      intro x
      exact DFunLike.congr_fun (red.liftOfSurjective_comp hred_surj _) x }

theorem exists_natCard_withConv_hffBarQ_algHom_eq_pow' :
    ∃ n : ℕ, Nat.card (WithConv (F.HffBarQ m hqp →ₐ[ZMod q] 𝔽bar)) = q ^ n := by
  rw [natCard_hffBarQ_eq F m hqp]
  exact exists_natCard_hff_algHom_eq_pow F m hqp

end Main

end JZeroNeronPrimaryTorsionFFModelsAlpha
end ModularCurve

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFFModels_exists_natCard_withConv_hffBarQ_algHom_eq_pow.ModularCurve in
theorem solution
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (F : JZeroNeronPrimaryTorsionFFModels p q A hA C)
    (m : ℕ) (hqp : q ≠ p) :
    ∃ n : ℕ, Nat.card (WithConv (F.HffBarQ m hqp →ₐ[ZMod q] AlgebraicClosure (ZMod q))) = q ^ n :=
  JZeroNeronPrimaryTorsionFFModelsAlpha.exists_natCard_withConv_hffBarQ_algHom_eq_pow' F m hqp

end S_ModularCurve_JZeroNeronPrimaryTorsionFFModels_exists_natCard_withConv_hffBarQ_algHom_eq_pow
end P2MW
export P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFFModels_exists_natCard_withConv_hffBarQ_algHom_eq_pow (solution)
