-- Prove2me | solution 1 for HopfAlgebra.natCard_algHom_mul_natCard_algHom_cartierDual_eq_finrank_of_map_eq_conv_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/66140d5e-6155-5cc7-a085-45afa77c3466

import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq
import Theorems.Thm_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_natCard_algHom_mul_natCard_algHom_cartierDual_eq_finrank_of_map_eq_conv_frobenius

set_option autoImplicit false

open scoped TensorProduct

universe u v w x

noncomputable section

open Module

namespace OrdConnEb2Pts

variable (q : ℕ) [Fact q.Prime]

section Reduced

variable (A : Type) [CommRing A] [Algebra (ZMod q) A] [Module.Finite (ZMod q) A]
variable (L : Type) [Field L] [Algebra (ZMod q) L]

private def kerPt (f : A →ₐ[ZMod q] L) : MaximalSpectrum A :=
  ⟨RingHom.ker f, by
    haveI : IsArtinianRing A := IsArtinianRing.of_finite (ZMod q) A
    haveI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
    exact IsArtinianRing.isMaximal_of_isPrime (RingHom.ker f)⟩

private theorem kerPt_asIdeal (f : A →ₐ[ZMod q] L) :
    (kerPt q A L f).asIdeal = RingHom.ker f := rfl

private def fibreEquiv (I : MaximalSpectrum A) :
    {f : A →ₐ[ZMod q] L // kerPt q A L f = I} ≃ ((A ⧸ I.asIdeal) →ₐ[ZMod q] L) where
  toFun f := Ideal.Quotient.liftₐ I.asIdeal f.1 (fun a ha => by
    have h : RingHom.ker (f.1 : A →+* L) = I.asIdeal := congrArg MaximalSpectrum.asIdeal f.2
    have ha' : a ∈ RingHom.ker (f.1 : A →+* L) := h ▸ ha
    exact (RingHom.mem_ker).mp ha')
  invFun g := ⟨g.comp (Ideal.Quotient.mkₐ (ZMod q) I.asIdeal), by
    letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    apply MaximalSpectrum.ext
    rw [kerPt_asIdeal]
    ext x
    rw [RingHom.mem_ker]
    change g (Ideal.Quotient.mk I.asIdeal x) = 0 ↔ x ∈ I.asIdeal
    rw [map_eq_zero_iff g (RingHom.injective (g : A ⧸ I.asIdeal →+* L)),
      Ideal.Quotient.eq_zero_iff_mem]⟩
  left_inv f := by
    apply Subtype.ext
    apply AlgHom.ext
    intro x
    simp [Ideal.Quotient.mkₐ_eq_mk]
  right_inv g := by
    apply Ideal.Quotient.algHom_ext
    apply AlgHom.ext
    intro x
    simp [Ideal.Quotient.mkₐ_eq_mk]

private scoped instance finite_fibre (I : MaximalSpectrum A) :
    Finite {f : A →ₐ[ZMod q] L // kerPt q A L f = I} := by
  letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
  exact Finite.of_equiv _ (fibreEquiv q A L I).symm

private theorem finite_pts : Finite (A →ₐ[ZMod q] L) := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite (ZMod q) A
  exact Finite.of_equiv _ (Equiv.sigmaFiberEquiv (kerPt q A L))

private theorem exists_kerPt_eq [IsAlgClosed L] (I : MaximalSpectrum A) :
    ∃ f : A →ₐ[ZMod q] L, kerPt q A L f = I := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI : PerfectField (ZMod q) := PerfectField.ofFinite
  letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
  have hpos : 0 < Fintype.card ((A ⧸ I.asIdeal) →ₐ[ZMod q] L) := by
    rw [AlgHom.card (ZMod q) (A ⧸ I.asIdeal) L]; exact finrank_pos
  obtain ⟨g⟩ := Fintype.card_pos_iff.mp hpos
  exact ⟨((fibreEquiv q A L I).symm g).1, ((fibreEquiv q A L I).symm g).2⟩

private theorem natCard_algHom_eq_finrank_of_isReduced [IsReduced A] [IsAlgClosed L] :
    Nat.card (A →ₐ[ZMod q] L) = finrank (ZMod q) A := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite (ZMod q) A
  haveI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI : PerfectField (ZMod q) := PerfectField.ofFinite
  calc Nat.card (A →ₐ[ZMod q] L)
      = Nat.card (Σ I : MaximalSpectrum A, {f : A →ₐ[ZMod q] L // kerPt q A L f = I}) :=
        Nat.card_congr (Equiv.sigmaFiberEquiv (kerPt q A L)).symm
    _ = ∑ I : MaximalSpectrum A, Nat.card {f : A →ₐ[ZMod q] L // kerPt q A L f = I} :=
        Nat.card_sigma
    _ = ∑ I : MaximalSpectrum A, Nat.card ((A ⧸ I.asIdeal) →ₐ[ZMod q] L) := by
        refine Finset.sum_congr rfl fun I _ => Nat.card_congr (fibreEquiv q A L I)
    _ = ∑ I : MaximalSpectrum A, finrank (ZMod q) (A ⧸ I.asIdeal) := by
        refine Finset.sum_congr rfl fun I _ => ?_
        letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
        rw [Nat.card_eq_fintype_card]
        convert AlgHom.card (ZMod q) (A ⧸ I.asIdeal) L
    _ = finrank (ZMod q) (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) :=
        (Module.finrank_pi_fintype (ZMod q)).symm
    _ = finrank (ZMod q) A :=
        (((IsArtinianRing.equivPi A).toLinearEquiv.restrictScalars (ZMod q)).finrank_eq).symm

private theorem eq_zero_of_forall_algHom [IsReduced A] [IsAlgClosed L] (z : A)
    (h : ∀ f : A →ₐ[ZMod q] L, f z = 0) : z = 0 := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite (ZMod q) A
  have hz : z ∈ nilradical A := by
    rw [nilradical_eq_sInf, Ideal.mem_sInf]
    intro J hJ
    haveI : J.IsPrime := hJ
    obtain ⟨f, hf⟩ := exists_kerPt_eq q A L ⟨J, IsArtinianRing.isMaximal_of_isPrime J⟩
    have hker : RingHom.ker (f : A →+* L) = J := congrArg MaximalSpectrum.asIdeal hf
    rw [← hker, RingHom.mem_ker]
    exact h f
  exact (mem_nilradical.mp hz).eq_zero

end Reduced

section Stable

variable (A : Type) [CommRing A] [Algebra (ZMod q) A] [Module.Finite (ZMod q) A]
variable (f : A →ₗ[ZMod q] A) (hf : ∀ x, f x = x ^ q)

private def Phi (hf : ∀ x, f x = x ^ q) : A →ₐ[ZMod q] A :=
  AlgHom.ofLinearMap f (by rw [hf, one_pow]) (fun x y => by rw [hf, hf, hf, mul_pow])

include hf

omit [Module.Finite (ZMod q) A] in
private theorem Phi_apply (x : A) : Phi q A f hf x = x ^ q := by
  change f x = x ^ q
  exact hf x

omit [Module.Finite (ZMod q) A] in
private theorem Phi_pow_apply (n : ℕ) (x : A) : (Phi q A f hf ^ n) x = x ^ q ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', AlgHom.mul_apply, ih, Phi_apply, ← pow_mul, ← pow_succ]

omit [Module.Finite (ZMod q) A] in
private theorem _root_.OrdConnEb2Pts.pow_apply (n : ℕ) (x : A) : (f ^ n) x = x ^ q ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, hf, ← pow_mul, ← pow_succ]

p2m_export "OrdConnEb2Pts" "pow_apply"
omit [Module.Finite (ZMod q) A] in
private theorem range_toSubmodule (n : ℕ) :
    Subalgebra.toSubmodule (Phi q A f hf ^ n).range = LinearMap.range (f ^ n) := by
  ext x
  simp only [Subalgebra.mem_toSubmodule, AlgHom.mem_range, LinearMap.mem_range, Phi_pow_apply,
    pow_apply q A f hf]

omit hf in
private theorem ker_pow_eq (n : ℕ) (hn : finrank (ZMod q) A ≤ n) :
    LinearMap.ker (f ^ n) = LinearMap.ker (f ^ finrank (ZMod q) A) :=
  Module.End.ker_pow_eq_ker_pow_finrank_of_le hn

omit hf in

private theorem finrank_range_pow_eq (n : ℕ) (hn : finrank (ZMod q) A ≤ n) :
    finrank (ZMod q) ↥(LinearMap.range (f ^ n)) =
      finrank (ZMod q) ↥(LinearMap.range (f ^ finrank (ZMod q) A)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (f ^ n)
  have h2 := LinearMap.finrank_range_add_finrank_ker (f ^ finrank (ZMod q) A)
  rw [ker_pow_eq q A f n hn] at h1
  omega

omit [Module.Finite (ZMod q) A] hf in
private theorem range_pow_le (n : ℕ) (hn : finrank (ZMod q) A ≤ n) :
    LinearMap.range (f ^ n) ≤ LinearMap.range (f ^ finrank (ZMod q) A) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [pow_add, Module.End.mul_eq_comp]
  exact LinearMap.range_comp_le_range _ _

private theorem range_succ :
    (Phi q A f hf ^ (finrank (ZMod q) A + 1)).range = (Phi q A f hf ^ finrank (ZMod q) A).range := by
  apply Subalgebra.toSubmodule_injective
  rw [range_toSubmodule, range_toSubmodule]
  apply Submodule.eq_of_le_of_finrank_eq (range_pow_le q A f _ (Nat.le_succ _))
  exact finrank_range_pow_eq q A f _ (Nat.le_succ _)

private abbrev St : Subalgebra (ZMod q) A := (Phi q A f hf ^ finrank (ZMod q) A).range

omit [Module.Finite (ZMod q) A] in
private theorem finite_St [Module.Finite (ZMod q) A] : Module.Finite (ZMod q) (St q A f hf) :=
  Module.Finite.of_injective (St q A f hf).val.toLinearMap Subtype.val_injective

omit [Module.Finite (ZMod q) A] in
private theorem finrank_St :
    finrank (ZMod q) (St q A f hf) = finrank (ZMod q) ↥(LinearMap.range (f ^ finrank (ZMod q) A)) := by
  rw [← Subalgebra.finrank_toSubmodule, range_toSubmodule]

omit [Module.Finite (ZMod q) A] in
private theorem mem_St_of_mem_range (n : ℕ) (hn : finrank (ZMod q) A ≤ n) (x : A)
    (hx : x ∈ LinearMap.range (f ^ n)) : x ∈ St q A f hf := by
  have hx' := range_pow_le q A f n hn hx
  rw [← range_toSubmodule q A f hf] at hx'
  exact hx'

private theorem apply_mem (y : A) (hy : y ∈ St q A f hf) : Phi q A f hf y ∈ St q A f hf := by
  obtain ⟨x, hx⟩ := (AlgHom.mem_range _).mp hy
  have : (Phi q A f hf ^ (finrank (ZMod q) A + 1)) x ∈ (Phi q A f hf ^ (finrank (ZMod q) A + 1)).range :=
    AlgHom.mem_range_self _ _
  rw [range_succ] at this
  rwa [pow_succ', AlgHom.mul_apply, hx] at this

private def PhiSt : St q A f hf →ₐ[ZMod q] St q A f hf :=
  ((Phi q A f hf).comp (St q A f hf).val).codRestrict (St q A f hf) fun y => apply_mem q A f hf y.1 y.2

private theorem coe_PhiSt (y : St q A f hf) : (PhiSt q A f hf y : A) = (y : A) ^ q := Phi_apply q A f hf y

private theorem coe_PhiSt_pow (n : ℕ) (y : St q A f hf) :
    ((PhiSt q A f hf ^ n) y : A) = (y : A) ^ q ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', AlgHom.mul_apply, coe_PhiSt, ih, ← pow_mul, ← pow_succ]

private theorem PhiSt_surjective : Function.Surjective (PhiSt q A f hf) := by
  rintro ⟨y, hy⟩
  have hy' : y ∈ (Phi q A f hf ^ (finrank (ZMod q) A + 1)).range := by rwa [range_succ]
  obtain ⟨x, hx⟩ := (AlgHom.mem_range _).mp hy'
  refine ⟨⟨(Phi q A f hf ^ finrank (ZMod q) A) x, AlgHom.mem_range_self _ _⟩, Subtype.ext ?_⟩
  change Phi q A f hf ((Phi q A f hf ^ finrank (ZMod q) A) x) = y
  rw [← hx, pow_succ', AlgHom.mul_apply]

private theorem PhiSt_bijective : Function.Bijective (PhiSt q A f hf) := by
  haveI := finite_St q A f hf
  refine ⟨?_, PhiSt_surjective q A f hf⟩
  have h : Function.Surjective (PhiSt q A f hf).toLinearMap := PhiSt_surjective q A f hf
  exact LinearMap.injective_iff_surjective.mpr h

private theorem isReduced_St : IsReduced (St q A f hf) := by
  refine ⟨fun y ⟨n, hn⟩ => ?_⟩
  have hq : 1 < q := (Fact.out : q.Prime).one_lt
  have hyq : y ^ q ^ n = 0 := pow_eq_zero_of_le (Nat.lt_pow_self hq).le hn
  have hinj : Function.Injective (PhiSt q A f hf ^ n) := by
    rw [AlgHom.coe_pow]; exact (PhiSt_bijective q A f hf).1.iterate n
  apply hinj
  rw [map_zero]
  apply Subtype.ext
  calc ((PhiSt q A f hf ^ n) y : A) = (y : A) ^ q ^ n := coe_PhiSt_pow q A f hf n y
    _ = ((y ^ q ^ n : St q A f hf) : A) := (SubmonoidClass.coe_pow y (q ^ n)).symm
    _ = ((0 : St q A f hf) : A) := by rw [hyq]

variable (L : Type) [Field L] [Algebra (ZMod q) L]

private def res (g : A →ₐ[ZMod q] L) : St q A f hf →ₐ[ZMod q] L := g.comp (St q A f hf).val

private def ext' (g : St q A f hf →ₐ[ZMod q] L) : A →ₐ[ZMod q] L :=
  g.comp (Phi q A f hf ^ finrank (ZMod q) A).rangeRestrict

omit [Module.Finite (ZMod q) A] in
private theorem res_injective : Function.Injective (res q A f hf L) := by
  intro g₁ g₂ h
  haveI : CharP L q := charP_of_injective_algebraMap (algebraMap (ZMod q) L).injective q
  haveI : ExpChar L q := ExpChar.prime (Fact.out : q.Prime)
  apply AlgHom.ext
  intro x
  apply iterateFrobenius_inj L q (finrank (ZMod q) A)
  rw [iterateFrobenius_def, iterateFrobenius_def, ← map_pow, ← map_pow,
    ← Phi_pow_apply q A f hf]
  exact AlgHom.congr_fun h ⟨(Phi q A f hf ^ finrank (ZMod q) A) x, AlgHom.mem_range_self _ _⟩

private theorem res_ext'_apply (g : St q A f hf →ₐ[ZMod q] L) (y : St q A f hf) :
    res q A f hf L (ext' q A f hf L g) y = g ((PhiSt q A f hf ^ finrank (ZMod q) A) y) := by
  have h1 : ((Phi q A f hf ^ finrank (ZMod q) A).rangeRestrict (y : A) : A) =
      (y : A) ^ q ^ finrank (ZMod q) A :=
    Phi_pow_apply q A f hf _ _
  have h2 : ((PhiSt q A f hf ^ finrank (ZMod q) A) y : A) = (y : A) ^ q ^ finrank (ZMod q) A :=
    coe_PhiSt_pow q A f hf _ _
  have h3 : (Phi q A f hf ^ finrank (ZMod q) A).rangeRestrict (y : A) =
      (PhiSt q A f hf ^ finrank (ZMod q) A) y :=
    Subtype.ext (h1.trans h2.symm)
  change g ((Phi q A f hf ^ finrank (ZMod q) A).rangeRestrict (y : A)) = _
  rw [h3]

private theorem ext'_injective : Function.Injective (ext' q A f hf L) := by
  intro g₁ g₂ h
  have hsurj : Function.Surjective (PhiSt q A f hf ^ finrank (ZMod q) A) := by
    rw [AlgHom.coe_pow]; exact (PhiSt_bijective q A f hf).2.iterate _
  apply AlgHom.ext
  intro y
  obtain ⟨z, rfl⟩ := hsurj y
  rw [← res_ext'_apply q A f hf L, ← res_ext'_apply q A f hf L, h]

private theorem natCard_algHom_eq_finrank_St [IsAlgClosed L] :
    Nat.card (A →ₐ[ZMod q] L) = finrank (ZMod q) (St q A f hf) := by
  haveI := isReduced_St q A f hf
  haveI := finite_St q A f hf
  haveI : Finite (St q A f hf →ₐ[ZMod q] L) := finite_pts q (St q A f hf) L
  haveI : Finite (A →ₐ[ZMod q] L) := Finite.of_injective _ (res_injective q A f hf L)
  rw [← natCard_algHom_eq_finrank_of_isReduced q (St q A f hf) L]
  exact le_antisymm (Nat.card_le_card_of_injective _ (res_injective q A f hf L))
    (Nat.card_le_card_of_injective _ (ext'_injective q A f hf L))

private theorem res_surjective [IsAlgClosed L] : Function.Surjective (res q A f hf L) := by
  haveI := isReduced_St q A f hf
  haveI := finite_St q A f hf
  haveI : Finite (St q A f hf →ₐ[ZMod q] L) := finite_pts q (St q A f hf) L
  haveI : Finite (A →ₐ[ZMod q] L) := Finite.of_injective _ (res_injective q A f hf L)
  haveI : Fintype (St q A f hf →ₐ[ZMod q] L) := Fintype.ofFinite _
  haveI : Fintype (A →ₐ[ZMod q] L) := Fintype.ofFinite _
  have hcard : Fintype.card (A →ₐ[ZMod q] L) = Fintype.card (St q A f hf →ₐ[ZMod q] L) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      natCard_algHom_eq_finrank_St q A f hf L, natCard_algHom_eq_finrank_of_isReduced q (St q A f hf) L]
  exact ((Fintype.bijective_iff_injective_and_card _).mpr ⟨res_injective q A f hf L, hcard⟩).2

private theorem natCard_algHom_eq_finrank_range_lin [IsAlgClosed L]
    (n : ℕ) (hn : Module.finrank (ZMod q) A ≤ n) :
    Nat.card (A →ₐ[ZMod q] L) = Module.finrank (ZMod q) ↥(LinearMap.range (f ^ n)) := by
  rw [finrank_range_pow_eq q A f n hn, ← finrank_St q A f hf, natCard_algHom_eq_finrank_St q A f hf L]

private theorem forall_algHom_apply_eq_imp_eq_lin [IsAlgClosed L]
    (n : ℕ) (hn : Module.finrank (ZMod q) A ≤ n) (x y : A)
    (hx : x ∈ LinearMap.range (f ^ n)) (hy : y ∈ LinearMap.range (f ^ n))
    (h : ∀ χ : A →ₐ[ZMod q] L, χ x = χ y) : x = y := by
  haveI := isReduced_St q A f hf
  haveI := finite_St q A f hf
  have hx' := mem_St_of_mem_range q A f hf n hn x hx
  have hy' := mem_St_of_mem_range q A f hf n hn y hy
  suffices hz : (⟨x, hx'⟩ - ⟨y, hy'⟩ : St q A f hf) = 0 by
    have := congrArg Subtype.val hz
    simpa [sub_eq_zero] using this
  apply eq_zero_of_forall_algHom q (St q A f hf) L
  intro g
  obtain ⟨g', rfl⟩ := res_surjective q A f hf L g
  rw [map_sub, sub_eq_zero]
  exact h g'

end Stable

section Exports

variable (A : Type) [CommRing A] [Algebra (ZMod q) A] [Module.Finite (ZMod q) A]
variable (Φ : A →ₐ[ZMod q] A) (hΦ : ∀ x, Φ x = x ^ q)
include hΦ

private theorem natCard_algHom_eq_finrank_range (n : ℕ) (hn : Module.finrank (ZMod q) A ≤ n) :
    Nat.card (A →ₐ[ZMod q] AlgebraicClosure (ZMod q)) =
      Module.finrank (ZMod q) ↥(LinearMap.range (Φ.toLinearMap ^ n)) :=
  natCard_algHom_eq_finrank_range_lin q A Φ.toLinearMap (fun x => hΦ x)
    (AlgebraicClosure (ZMod q)) n hn

private theorem forall_algHom_apply_eq_imp_eq (n : ℕ) (hn : Module.finrank (ZMod q) A ≤ n) (x y : A)
    (hx : x ∈ LinearMap.range (Φ.toLinearMap ^ n))
    (hy : y ∈ LinearMap.range (Φ.toLinearMap ^ n))
    (h : ∀ χ : A →ₐ[ZMod q] AlgebraicClosure (ZMod q), χ x = χ y) : x = y :=
  forall_algHom_apply_eq_imp_eq_lin q A Φ.toLinearMap (fun x => hΦ x)
    (AlgebraicClosure (ZMod q)) n hn x y hx hy h

end Exports

end OrdConnEb2Pts
p2m_reactivate "P2MW.S_HopfAlgebra_natCard_algHom_mul_natCard_algHom_cartierDual_eq_finrank_of_map_eq_conv_frobenius.OrdConnEb2Pts"

end
p2m_reactivate "P2MW.S_HopfAlgebra_natCard_algHom_mul_natCard_algHom_cartierDual_eq_finrank_of_map_eq_conv_frobenius.OrdConnEb2Pts"

namespace OrdConnEb2Dual

open scoped TensorProduct

section Preliminaries

private theorem nontrivial_of_bialgebra (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B]
    [Bialgebra (ZMod q) B] : Nontrivial B :=
  (Bialgebra.counitAlgHom (ZMod q) B).toRingHom.domain_nontrivial

private theorem eq_of_forall_dual_apply_eq (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B]
    [Bialgebra (ZMod q) B] {x y : B} (h : ∀ ψ : CartierDual (ZMod q) B, ψ x = ψ y) : x = y := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff (ZMod q)]
  intro φ
  rw [map_sub, sub_eq_zero]
  exact h (CartierDual.ofDual (ZMod q) B φ)

private theorem tensor_eq_of_forall_pairing_eq (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B]
    [Bialgebra (ZMod q) B] [Module.Finite (ZMod q) B] {s t : B ⊗[ZMod q] B}
    (h : ∀ ψ φ : CartierDual (ZMod q) B,
      TensorProduct.dualDistrib (ZMod q) B B
          (CartierDual.toDual (ZMod q) B ψ ⊗ₜ[ZMod q] CartierDual.toDual (ZMod q) B φ) s =
        TensorProduct.dualDistrib (ZMod q) B B
          (CartierDual.toDual (ZMod q) B ψ ⊗ₜ[ZMod q] CartierDual.toDual (ZMod q) B φ) t) :
    s = t := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff (ZMod q)]
  intro F
  obtain ⟨w, rfl⟩ := (TensorProduct.dualDistribEquiv (ZMod q) B B).surjective F
  rw [CartierDual.dualDistribEquiv_apply_eq]
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, LinearMap.zero_apply]
  | tmul ψ φ =>
    rw [map_sub, sub_eq_zero]
    exact h (CartierDual.ofDual (ZMod q) B ψ) (CartierDual.ofDual (ZMod q) B φ)
  | add u v hu hv => rw [map_add, LinearMap.add_apply, hu, hv, add_zero]

private noncomputable def verLin (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] (g : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) :
    B →ₗ[ZMod q] B :=
  (Module.evalEquiv (ZMod q) B).symm.toLinearMap ∘ₗ
    ((CartierDual.toDual (ZMod q) B).toLinearMap ∘ₗ g ∘ₗ (CartierDual.ofDual (ZMod q) B).toLinearMap).dualMap ∘ₗ
      Module.Dual.eval (ZMod q) B

private theorem apply_verLin (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] (g : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B)
    (ψ : CartierDual (ZMod q) B) (b : B) : ψ (verLin q B g b) = g ψ b := by
  have h : verLin q B g b = (Module.evalEquiv (ZMod q) B).symm
      (((CartierDual.toDual (ZMod q) B).toLinearMap ∘ₗ g ∘ₗ (CartierDual.ofDual (ZMod q) B).toLinearMap).dualMap
        (Module.Dual.eval (ZMod q) B b)) := rfl
  rw [h]
  exact Module.apply_evalEquiv_symm_apply (ZMod q) B (CartierDual.toDual (ZMod q) B ψ) _

private theorem finrank_range_verLin (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] (g : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) :
    Module.finrank (ZMod q) ↥(LinearMap.range (verLin q B g)) = Module.finrank (ZMod q) ↥(LinearMap.range g) := by
  unfold verLin
  rw [LinearMap.range_comp, LinearEquiv.finrank_map_eq,
    LinearMap.range_comp_of_range_eq_top _ (Module.erange_coe (ZMod q) B),
    LinearMap.finrank_range_dualMap_eq_finrank_range, LinearMap.range_comp, LinearEquiv.finrank_map_eq,
    LinearMap.range_comp_of_range_eq_top _ (CartierDual.ofDual (ZMod q) B).range]

private theorem eq_verLin_of_forall_apply (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] (W : B →ₗ[ZMod q] B) (g : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B)
    (h : ∀ (ψ : CartierDual (ZMod q) B) (b : B), ψ (W b) = g ψ b) : W = verLin q B g := by
  apply LinearMap.ext
  intro b
  apply eq_of_forall_dual_apply_eq q B
  intro ψ
  rw [h, apply_verLin]

private theorem apply_pow_of_forall_apply (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    (W : B →ₗ[ZMod q] B) (g : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B)
    (h : ∀ (ψ : CartierDual (ZMod q) B) (b : B), ψ (W b) = g ψ b) (n : ℕ) :
    ∀ (ψ : CartierDual (ZMod q) B) (b : B), ψ ((W ^ n) b) = (g ^ n) ψ b := by
  induction n with
  | zero => intro ψ b; rw [pow_zero, pow_zero, Module.End.one_apply, Module.End.one_apply]
  | succ n ih =>
    intro ψ b
    rw [pow_succ, Module.End.mul_apply, ih, h, pow_succ', Module.End.mul_apply]

private theorem finrank_range_pow_eq (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] (W : B →ₗ[ZMod q] B) (g : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B)
    (h : ∀ (ψ : CartierDual (ZMod q) B) (b : B), ψ (W b) = g ψ b) (n : ℕ) :
    Module.finrank (ZMod q) ↥(LinearMap.range (W ^ n)) = Module.finrank (ZMod q) ↥(LinearMap.range (g ^ n)) := by
  rw [eq_verLin_of_forall_apply q B (W ^ n) (g ^ n) (apply_pow_of_forall_apply q B W g h n), finrank_range_verLin]

private theorem coeLin_apply (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (ψ : CartierDual (ZMod q) B) :
    (FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) ψ = FD ψ := rfl

private theorem map_frobDual_eq_pow (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B]
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q)
    (hD : ∀ a c : CartierDual (ZMod q) B, a * c = c * a) :
    ∀ w : @TensorProduct (ZMod q) _ (CartierDual (ZMod q) B) (CartierDual (ZMod q) B) _ _
      Algebra.toModule Algebra.toModule, Algebra.TensorProduct.map FD FD w = w ^ q := by
  haveI : Nontrivial (@TensorProduct (ZMod q) _ (CartierDual (ZMod q) B) (CartierDual (ZMod q) B) _ _
      Algebra.toModule Algebra.toModule) :=
    (Algebra.TensorProduct.lift (Bialgebra.counitAlgHom (ZMod q) (CartierDual (ZMod q) B))
      (Bialgebra.counitAlgHom (ZMod q) (CartierDual (ZMod q) B))
      (fun _ _ => Commute.all _ _)).toRingHom.domain_nontrivial
  haveI : CharP (@TensorProduct (ZMod q) _ (CartierDual (ZMod q) B) (CartierDual (ZMod q) B) _ _
      Algebra.toModule Algebra.toModule) q :=
    ((algebraMap (ZMod q) (@TensorProduct (ZMod q) _ (CartierDual (ZMod q) B) (CartierDual (ZMod q) B) _ _
      Algebra.toModule Algebra.toModule)).charP_iff_charP q).mp inferInstance
  have hcomm : ∀ s t : @TensorProduct (ZMod q) _ (CartierDual (ZMod q) B) (CartierDual (ZMod q) B) _ _
      Algebra.toModule Algebra.toModule, s * t = t * s := by
    intro s t
    induction s using TensorProduct.induction_on with
    | zero => rw [zero_mul, mul_zero]
    | tmul a c =>
      induction t using TensorProduct.induction_on with
      | zero => rw [zero_mul, mul_zero]
      | tmul a' c' =>
        refine Eq.trans (Algebra.TensorProduct.tmul_mul_tmul a a' c c') ?_
        refine Eq.trans ?_ (Eq.symm (Algebra.TensorProduct.tmul_mul_tmul a' a c' c))
        congr 1
        · exact hD a a'
        · exact hD c c'
      | add u v hu hv => rw [mul_add, add_mul, hu, hv]
    | add u v hu hv => rw [add_mul, mul_add, hu, hv]
  intro w
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, zero_pow (Fact.out : q.Prime).ne_zero]
  | tmul a c => rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_pow, hFD, hFD]
  | add s t hs ht => rw [map_add, add_pow_char_of_commute q (hcomm s t), hs, ht]

private theorem comul_frobDual_alg (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q)
    (ψ : CartierDual (ZMod q) B) :
    Coalgebra.comul (R := ZMod q) (FD ψ) =
      Algebra.TensorProduct.map FD FD (Coalgebra.comul (R := ZMod q) ψ) := by
  rw [hFD]
  exact (Bialgebra.comul_pow ψ q).trans (map_frobDual_eq_pow q B FD hFD (fun a c => mul_comm a c) _).symm

private theorem algMap_eq_linMap (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B]
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) :
    ∀ w : @TensorProduct (ZMod q) _ (CartierDual (ZMod q) B) (CartierDual (ZMod q) B) _ _
      Algebra.toModule Algebra.toModule,
      Algebra.TensorProduct.map FD FD w =
        TensorProduct.map (FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B)
          (FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) w := by
  intro w
  induction w using TensorProduct.induction_on with
  | zero =>
    exact (map_zero (Algebra.TensorProduct.map FD FD)).trans
      (map_zero (TensorProduct.map (FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B)
        (FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B))).symm
  | tmul a c => rfl
  | add s t hs ht =>
    refine (map_add (Algebra.TensorProduct.map FD FD) s t).trans ?_
    rw [hs, ht]
    exact (map_add (TensorProduct.map (FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B)
      (FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B)) s t).symm

private theorem comul_frobDual (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q)
    (ψ : CartierDual (ZMod q) B) :
    Coalgebra.comul (R := ZMod q) (FD ψ) =
      TensorProduct.map (FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B)
        (FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) (Coalgebra.comul (R := ZMod q) ψ) :=
  (comul_frobDual_alg q B FD hFD ψ).trans (algMap_eq_linMap q B FD _)

private theorem pairing_verLin (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B]
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (x y : B)
    (w : CartierDual (ZMod q) B ⊗[ZMod q] CartierDual (ZMod q) B) :
    TensorProduct.dualDistrib (ZMod q) B B
        (TensorProduct.map (CartierDual.toDual (ZMod q) B).toLinearMap (CartierDual.toDual (ZMod q) B).toLinearMap w)
        (verLin q B (FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) x ⊗ₜ[ZMod q]
          verLin q B (FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) y) =
      TensorProduct.dualDistrib (ZMod q) B B
        (TensorProduct.map (CartierDual.toDual (ZMod q) B).toLinearMap (CartierDual.toDual (ZMod q) B).toLinearMap
          (TensorProduct.map (FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B)
            (FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) w))
        (x ⊗ₜ[ZMod q] y) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul a c =>
    simp only [TensorProduct.map_tmul, LinearEquiv.coe_coe, TensorProduct.dualDistrib_apply, CartierDual.toDual_apply,
      apply_verLin]
  | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]

private theorem verLin_mul (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q) (x y : B) :
    verLin q B (FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) (x * y) =
      verLin q B (FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) x *
        verLin q B (FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) y := by
  apply eq_of_forall_dual_apply_eq q B
  intro ψ
  rw [apply_verLin, coeLin_apply, ← CartierDual.comul_pairing (FD ψ) x y, comul_frobDual q B FD hFD,
    ← CartierDual.comul_pairing ψ, pairing_verLin]

private theorem verLin_one (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B]
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q) :
    verLin q B (FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) 1 = 1 := by
  apply eq_of_forall_dual_apply_eq q B
  intro ψ
  have h : Coalgebra.counit (R := ZMod q) (ψ ^ q) = Coalgebra.counit (R := ZMod q) ψ ^ q := Bialgebra.counit_pow ψ q
  rw [apply_verLin, coeLin_apply, ← CartierDual.counit_apply (FD ψ), ← CartierDual.counit_apply ψ, hFD, h,
    ZMod.pow_card]

private noncomputable def verAlg (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q) : B →ₐ[ZMod q] B :=
  AlgHom.ofLinearMap (verLin q B (FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B))
    (verLin_one q B FD hFD) (verLin_mul q B FD hFD)

private theorem verAlg_apply (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q) (b : B) :
    verAlg q B FD hFD b = verLin q B (FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) b := rfl

private theorem apply_verAlg (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q)
    (ψ : CartierDual (ZMod q) B) (b : B) : ψ (verAlg q B FD hFD b) = FD ψ b := by
  rw [verAlg_apply, apply_verLin, coeLin_apply]

private theorem counit_comp_verAlg (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q) :
    (Bialgebra.counitAlgHom (ZMod q) B).comp (verAlg q B FD hFD) = Bialgebra.counitAlgHom (ZMod q) B := by
  apply AlgHom.ext
  intro b
  rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply]
  have h := apply_verAlg q B FD hFD 1 b
  rw [map_one, CartierDual.one_apply, CartierDual.one_apply] at h
  exact h

private theorem pairing_map_verAlg (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q)
    (ψ φ : CartierDual (ZMod q) B) (t : B ⊗[ZMod q] B) :
    TensorProduct.dualDistrib (ZMod q) B B
        (CartierDual.toDual (ZMod q) B ψ ⊗ₜ[ZMod q] CartierDual.toDual (ZMod q) B φ)
        (Algebra.TensorProduct.map (verAlg q B FD hFD) (verAlg q B FD hFD) t) =
      TensorProduct.dualDistrib (ZMod q) B B
        (CartierDual.toDual (ZMod q) B (FD ψ) ⊗ₜ[ZMod q] CartierDual.toDual (ZMod q) B (FD φ)) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    simp only [Algebra.TensorProduct.map_tmul, TensorProduct.dualDistrib_apply, CartierDual.toDual_apply, apply_verAlg]
  | add s u hs hu => simp only [map_add, hs, hu]

private theorem map_comp_comul_verAlg (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q) :
    (Algebra.TensorProduct.map (verAlg q B FD hFD) (verAlg q B FD hFD)).comp (Bialgebra.comulAlgHom (ZMod q) B) =
      (Bialgebra.comulAlgHom (ZMod q) B).comp (verAlg q B FD hFD) := by
  apply AlgHom.ext
  intro b
  rw [AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, Bialgebra.comulAlgHom_apply]
  apply tensor_eq_of_forall_pairing_eq q B
  intro ψ φ
  rw [pairing_map_verAlg, ← CartierDual.mul_apply, ← CartierDual.mul_apply, ← map_mul, apply_verAlg]

private noncomputable def ver (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q) : B →ₐc[ZMod q] B :=
  BialgHom.ofAlgHom (verAlg q B FD hFD) (counit_comp_verAlg q B FD hFD) (map_comp_comul_verAlg q B FD hFD)

private theorem ver_apply (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q) (b : B) :
    ver q B FD hFD b = verLin q B (FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) b := rfl

private theorem apply_ver (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q)
    (ψ : CartierDual (ZMod q) B) (b : B) : ψ (ver q B FD hFD b) = FD ψ b := by
  rw [ver_apply, apply_verLin, coeLin_apply]

private theorem ver_comm_frob (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]
    (Fk : B →ₐc[ZMod q] B) (hFk : ∀ x, Fk x = x ^ q)
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q) (b : B) :
    ver q B FD hFD (Fk b) = Fk (ver q B FD hFD b) := by
  rw [hFk, hFk, map_pow]

private theorem ver_comm_bialgHom (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]
    (T : B →ₐc[ZMod q] B)
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q) (b : B) :
    ver q B FD hFD (T b) = T (ver q B FD hFD b) := by
  apply eq_of_forall_dual_apply_eq q B
  intro ψ
  have h : ψ (T (ver q B FD hFD b)) = CartierDual.map T ψ (ver q B FD hFD b) := rfl
  rw [apply_ver, h, apply_ver, hFD, hFD, ← map_pow (CartierDual.map T)]
  rfl

private theorem zero_apply' (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B] (b : B) :
    (0 : CartierDual (ZMod q) B) b = 0 := rfl

private theorem add_apply' (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    (φ χ : CartierDual (ZMod q) B) (b : B) : (φ + χ) b = φ b + χ b := rfl

private theorem coeBialg_apply (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    (f : B →ₐc[ZMod q] B) (x : B) : (f : B →ₗ[ZMod q] B) x = f x := rfl

private theorem pairing_comul_eq_apply_mul' (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] (ψ : CartierDual (ZMod q) B) (t : B ⊗[ZMod q] B) :
    TensorProduct.dualDistrib (ZMod q) B B
        (TensorProduct.map (CartierDual.toDual (ZMod q) B).toLinearMap (CartierDual.toDual (ZMod q) B).toLinearMap
          (Coalgebra.comul (R := ZMod q) ψ)) t =
      ψ (LinearMap.mul' (ZMod q) B t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a c =>
    rw [LinearMap.mul'_apply]
    exact CartierDual.comul_pairing ψ a c
  | add u v hu hv => simp only [map_add, hu, hv]

private theorem pairing_map_frob_frobDual (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B] (Fk : B →ₐc[ZMod q] B)
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q)
    (α β : CartierDual (ZMod q) B) (t : B ⊗[ZMod q] B) :
    TensorProduct.dualDistrib (ZMod q) B B
        (CartierDual.toDual (ZMod q) B
            ((CartierDual.map Fk : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) α) ⊗ₜ[ZMod q]
          CartierDual.toDual (ZMod q) B ((FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) β)) t =
      TensorProduct.dualDistrib (ZMod q) B B
        (CartierDual.toDual (ZMod q) B α ⊗ₜ[ZMod q] CartierDual.toDual (ZMod q) B β)
        (TensorProduct.map (Fk : B →ₗ[ZMod q] B) (ver q B FD hFD : B →ₗ[ZMod q] B) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    simp only [TensorProduct.map_tmul, TensorProduct.dualDistrib_apply, CartierDual.toDual_apply, coeLin_apply,
      CartierDual.map_apply, coeBialg_apply, apply_ver]
  | add u v hu hv => simp only [map_add, hu, hv]

private theorem mul'_map_apply (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B] (Fk : B →ₐc[ZMod q] B)
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q) (b : B)
    (w : CartierDual (ZMod q) B ⊗[ZMod q] CartierDual (ZMod q) B) :
    LinearMap.mul' (ZMod q) (CartierDual (ZMod q) B)
        (TensorProduct.map (CartierDual.map Fk : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B)
          (FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) w) b =
      TensorProduct.dualDistrib (ZMod q) B B
        (TensorProduct.map (CartierDual.toDual (ZMod q) B).toLinearMap (CartierDual.toDual (ZMod q) B).toLinearMap w)
        (TensorProduct.map (Fk : B →ₗ[ZMod q] B) (ver q B FD hFD : B →ₗ[ZMod q] B)
          (Coalgebra.comul (R := ZMod q) b)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, zero_apply', LinearMap.zero_apply]
  | tmul α β =>
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply, CartierDual.mul_apply, TensorProduct.map_tmul]
    exact pairing_map_frob_frobDual q B Fk FD hFD α β _
  | add u v hu hv => simp only [map_add, add_apply', LinearMap.add_apply, hu, hv]

private theorem conv_eq (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]
    (T : B →ₐc[ZMod q] B) (Fk : B →ₐc[ZMod q] B)
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q)
    (hFV : (CartierDual.map T : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) =
      (WithConv.toConv
          (CartierDual.map Fk : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) *
        WithConv.toConv
          (FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B)).ofConv) :
    WithConv.toConv (T : B →ₗ[ZMod q] B) =
      WithConv.toConv (Fk : B →ₗ[ZMod q] B) * WithConv.toConv (ver q B FD hFD : B →ₗ[ZMod q] B) := by
  apply WithConv.ofConv_injective
  rw [LinearMap.convMul_def]
  apply LinearMap.ext
  intro b
  rw [LinearMap.comp_apply, LinearMap.comp_apply, coeBialg_apply]
  apply eq_of_forall_dual_apply_eq q B
  intro ψ
  have h1 : ψ (T b) =
      (CartierDual.map T : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) ψ b := rfl
  rw [h1, hFV, LinearMap.convMul_def]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, mul'_map_apply, pairing_comul_eq_apply_mul']

private theorem charP_conv (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Coalgebra.IsCocomm (ZMod q) B] :
    CharP (WithConv (B →ₗ[ZMod q] AlgebraicClosure (ZMod q))) q := by
  haveI : Nontrivial (WithConv (B →ₗ[ZMod q] AlgebraicClosure (ZMod q))) := by
    refine nontrivial_of_ne (1 : WithConv (B →ₗ[ZMod q] AlgebraicClosure (ZMod q))) 0 fun h => ?_
    have h1 := congrArg (fun f : WithConv (B →ₗ[ZMod q] AlgebraicClosure (ZMod q)) => f.ofConv (1 : B)) h
    simp only [LinearMap.convOne_def, WithConv.ofConv_toConv, LinearMap.comp_apply, Bialgebra.counit_one,
      Algebra.linearMap_apply, map_one, WithConv.ofConv_zero, LinearMap.zero_apply] at h1
    exact one_ne_zero h1
  refine (CharP.charP_iff_prime_eq_zero Fact.out).2 ?_
  rw [← nsmul_one]
  apply WithConv.ofConv_injective
  rw [← WithConv.addEquiv_apply, map_nsmul, WithConv.addEquiv_apply, WithConv.ofConv_zero,
    ← Nat.cast_smul_eq_nsmul (ZMod q), ZMod.natCast_self, zero_smul]

private theorem smul_convMul (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    (a : AlgebraicClosure (ZMod q)) (f g : WithConv (B →ₗ[ZMod q] AlgebraicClosure (ZMod q))) :
    (a • f) * g = a • (f * g) := by
  apply WithConv.ofConv_injective
  apply LinearMap.ext
  intro b
  change ((a • f) * g) b = (a • (f * g)).ofConv b
  simp only [LinearMap.convMul_apply, WithConv.ofConv_smul, LinearMap.smul_apply]
  generalize Coalgebra.comul (R := ZMod q) b = t
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul x y => simp only [TensorProduct.map_tmul, LinearMap.smul_apply, LinearMap.mul'_apply, smul_mul_assoc]
  | add s t hs ht => simp only [map_add, hs, ht, smul_add]

private theorem smul_convPow (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Coalgebra.IsCocomm (ZMod q) B]
    (a : AlgebraicClosure (ZMod q)) (f : WithConv (B →ₗ[ZMod q] AlgebraicClosure (ZMod q))) (n : ℕ) :
    (a • f) ^ n = a ^ n • f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_zero, one_smul]
  | succ n ih =>
    rw [pow_succ, ih, mul_comm, smul_convMul, mul_comm, smul_convMul, smul_smul, ← pow_succ', ← pow_succ]

private noncomputable def _root_.OrdConnEb2Dual.ext (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    (ψ : CartierDual (ZMod q) B) : B →ₗ[ZMod q] AlgebraicClosure (ZMod q) :=
  (Algebra.ofId (ZMod q) (AlgebraicClosure (ZMod q))).toLinearMap ∘ₗ CartierDual.toDual (ZMod q) B ψ

p2m_export "OrdConnEb2Dual" "ext"
private theorem ext_apply (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    (ψ : CartierDual (ZMod q) B) (b : B) :
    ext q B ψ b = algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) (ψ b) := rfl

private theorem toConv_ext_pow (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    (ψ : CartierDual (ZMod q) B) (m : ℕ) :
    WithConv.toConv (ext q B ψ) ^ m = WithConv.toConv (ext q B (ψ ^ m)) := by
  induction m with
  | zero =>
    rw [pow_zero, pow_zero, LinearMap.convOne_def]
    rfl
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    apply WithConv.ofConv_injective
    rw [WithConv.ofConv_toConv]
    unfold ext
    rw [CartierDual.toDual_mul, LinearMap.algHom_comp_convMul_distrib, WithConv.ofConv_toConv, WithConv.ofConv_toConv]

private theorem ext_ver_pow (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q)
    (ψ : CartierDual (ZMod q) B) (b : B) :
    ext q B ψ (ver q B FD hFD b) ^ q = (WithConv.toConv (ext q B ψ) ^ q).ofConv b := by
  rw [toConv_ext_pow, WithConv.ofConv_toConv, ext_apply, ext_apply, ← map_pow, ZMod.pow_card, apply_ver, hFD]

private theorem apply_eq_sum (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] (θ : B →ₗ[ZMod q] AlgebraicClosure (ZMod q)) (x : B) :
    θ x = ∑ j, θ (Module.finBasis (ZMod q) B j) *
      ext q B (CartierDual.ofDual (ZMod q) B ((Module.finBasis (ZMod q) B).coord j)) x := by
  conv_lhs => rw [← (Module.finBasis (ZMod q) B).sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, ext_apply, CartierDual.ofDual_apply, Module.Basis.coord_apply, Algebra.smul_def, mul_comm]

private theorem toConv_eq_sum (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] (θ : B →ₗ[ZMod q] AlgebraicClosure (ZMod q)) :
    WithConv.toConv θ = ∑ j, θ (Module.finBasis (ZMod q) B j) •
      WithConv.toConv (ext q B (CartierDual.ofDual (ZMod q) B ((Module.finBasis (ZMod q) B).coord j))) := by
  apply WithConv.ofConv_injective
  apply LinearMap.ext
  intro x
  rw [WithConv.ofConv_toConv, WithConv.ofConv_sum, LinearMap.sum_apply, apply_eq_sum q B θ x]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [WithConv.ofConv_smul, LinearMap.smul_apply, WithConv.ofConv_toConv, smul_eq_mul]

private theorem apply_ver_pow (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q)
    (θ : B →ₗ[ZMod q] AlgebraicClosure (ZMod q)) (b : B) :
    θ (ver q B FD hFD b) ^ q = (WithConv.toConv θ ^ q).ofConv b := by
  haveI := charP_conv q B
  rw [apply_eq_sum q B θ, sum_pow_char, toConv_eq_sum q B θ, sum_pow_char, WithConv.ofConv_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_pow, ext_ver_pow, smul_convPow, WithConv.ofConv_smul, LinearMap.smul_apply, smul_eq_mul]

private theorem apply_ver_iterate_pow (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q) (n : ℕ) :
    ∀ (θ : B →ₗ[ZMod q] AlgebraicClosure (ZMod q)) (b : B),
      θ ((⇑(ver q B FD hFD))^[n] b) ^ (q ^ n) = (WithConv.toConv θ ^ (q ^ n)).ofConv b := by
  induction n with
  | zero => intro θ b; rw [Function.iterate_zero, id, pow_zero, pow_one, pow_one, WithConv.ofConv_toConv]
  | succ n ih =>
    intro θ b
    rw [Function.iterate_succ_apply, pow_succ]
    simp only [pow_mul]
    rw [ih θ (ver q B FD hFD b), apply_ver_pow, WithConv.toConv_ofConv]

private theorem toConv_algHom_pow (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    (θ : B →ₐ[ZMod q] AlgebraicClosure (ZMod q)) (m : ℕ) :
    WithConv.toConv θ.toLinearMap ^ m =
      WithConv.toConv (θ.toLinearMap ∘ₗ (WithConv.toConv (LinearMap.id : B →ₗ[ZMod q] B) ^ m).ofConv) := by
  induction m with
  | zero =>
    rw [pow_zero, pow_zero, LinearMap.convOne_def, LinearMap.convOne_def, WithConv.ofConv_toConv]
    congr 1
    apply LinearMap.ext
    intro b
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply, AlgHom.toLinearMap_apply, AlgHom.commutes]
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    apply WithConv.ofConv_injective
    rw [WithConv.ofConv_toConv, LinearMap.algHom_comp_convMul_distrib]
    simp only [LinearMap.comp_id]

private theorem algHom_ver_iterate (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]
    (N : ℕ) (hN : WithConv.toConv (LinearMap.id : B →ₗ[ZMod q] B) ^ (q ^ N) = 1)
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q)
    (θ : B →ₐ[ZMod q] AlgebraicClosure (ZMod q)) (b : B) :
    θ ((⇑(ver q B FD hFD))^[N] b) = algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) (Coalgebra.counit b) := by
  apply iterateFrobenius_inj (AlgebraicClosure (ZMod q)) q N
  rw [iterateFrobenius_def, iterateFrobenius_def, ← map_pow (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))),
    ZMod.pow_card_pow]
  have h := apply_ver_iterate_pow q B FD hFD N θ.toLinearMap b
  rw [AlgHom.toLinearMap_apply, toConv_algHom_pow, hN, WithConv.ofConv_toConv, LinearMap.comp_apply,
    LinearMap.convOne_apply, AlgHom.toLinearMap_apply, AlgHom.commutes] at h
  exact h

private theorem counit_ver (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q) (b : B) :
    Coalgebra.counit (R := ZMod q) (ver q B FD hFD b) = Coalgebra.counit (R := ZMod q) b := by
  have h := apply_ver q B FD hFD 1 b
  rw [map_one, CartierDual.one_apply, CartierDual.one_apply] at h
  exact h

private theorem counit_ver_iterate (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q) (k : ℕ) (b : B) :
    Coalgebra.counit (R := ZMod q) ((⇑(ver q B FD hFD))^[k] b) = Coalgebra.counit (R := ZMod q) b := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', counit_ver, ih]

private theorem algHom_ver_iterate_of_le (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]
    (N : ℕ) (hN : WithConv.toConv (LinearMap.id : B →ₗ[ZMod q] B) ^ (q ^ N) = 1)
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q)
    (θ : B →ₐ[ZMod q] AlgebraicClosure (ZMod q)) (n : ℕ) (hn : N ≤ n) (b : B) :
    θ ((⇑(ver q B FD hFD))^[n] b) = algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) (Coalgebra.counit b) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Function.iterate_add_apply, algHom_ver_iterate q B N hN FD hFD, counit_ver_iterate]

end Preliminaries
p2m_reactivate "P2MW.S_HopfAlgebra_natCard_algHom_mul_natCard_algHom_cartierDual_eq_finrank_of_map_eq_conv_frobenius.OrdConnEb2Pts"

private theorem exists_verschiebung
    (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [HopfAlgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]
    (N : ℕ) (hN : WithConv.toConv (LinearMap.id : B →ₗ[ZMod q] B) ^ (q ^ N) = 1)
    (T : B →ₐc[ZMod q] B)
    (Fk : B →ₐc[ZMod q] B) (hFk : ∀ x, Fk x = x ^ q)
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q)
    (hFV : (CartierDual.map T : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) =
      (WithConv.toConv
          (CartierDual.map Fk : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) *
        WithConv.toConv
          (FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B)).ofConv) :
    ∃ V : B →ₐc[ZMod q] B,
      (∀ (ψ : CartierDual (ZMod q) B) (b : B), ψ (V b) = FD ψ b) ∧
      (∀ b, V (Fk b) = Fk (V b)) ∧
      (∀ b, V (T b) = T (V b)) ∧
      (WithConv.toConv (T : B →ₗ[ZMod q] B) =
        WithConv.toConv (Fk : B →ₗ[ZMod q] B) * WithConv.toConv (V : B →ₗ[ZMod q] B)) ∧
      (∀ (θ : B →ₐ[ZMod q] AlgebraicClosure (ZMod q)) (n : ℕ), N ≤ n → ∀ b : B,
        θ ((⇑V)^[n] b) = algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) (Coalgebra.counit b)) ∧
      (∀ n : ℕ, Module.finrank (ZMod q) ↥(LinearMap.range ((V : B →ₗ[ZMod q] B) ^ n)) =
        Module.finrank (ZMod q) ↥(LinearMap.range (FD.toLinearMap ^ n))) := by
  refine ⟨ver q B FD hFD, fun ψ b => apply_ver q B FD hFD ψ b, fun b => ver_comm_frob q B Fk hFk FD hFD b,
    fun b => ver_comm_bialgHom q B T FD hFD b, ?_, ?_, ?_⟩
  · exact conv_eq q B T Fk FD hFD hFV
  · exact fun θ n hn b => algHom_ver_iterate_of_le q B N hN FD hFD θ n hn b
  · intro n
    exact finrank_range_pow_eq q B (ver q B FD hFD : B →ₗ[ZMod q] B) FD.toLinearMap
      (fun ψ b => apply_ver q B FD hFD ψ b) n

end OrdConnEb2Dual
p2m_reactivate "P2MW.S_HopfAlgebra_natCard_algHom_mul_natCard_algHom_cartierDual_eq_finrank_of_map_eq_conv_frobenius.OrdConnEb2Pts"

namespace OrdConnEb2Split

open WithConv

section Generic

variable {F : Type u} [Field F] {H : Type v} [CommRing H] [HopfAlgebra F H]

private theorem bialgHom_pow_apply (g : H →ₐc[F] H) : ∀ (j : ℕ) (b : H), (g ^ j) b = (⇑g)^[j] b
  | 0, b => by rw [pow_zero, BialgHom.one_apply, Function.iterate_zero_apply]
  | j + 1, b => by rw [pow_succ, BialgHom.mul_apply, bialgHom_pow_apply g j (g b), Function.iterate_succ_apply]

private theorem comm_pow {f g : H →ₐc[F] H} (h : ∀ b, g (f b) = f (g b)) :
    ∀ (j : ℕ) (b : H), g ((f ^ j) b) = (f ^ j) (g b)
  | 0, b => by rw [pow_zero, BialgHom.one_apply, BialgHom.one_apply]
  | j + 1, b => by rw [pow_succ, BialgHom.mul_apply, BialgHom.mul_apply, comm_pow h j (f b), h b]

private theorem apply_eq_algebraMap_counit_of_mem_hopfKer {H' : Type w} [CommRing H'] [HopfAlgebra F H']
    (π : H →ₐc[F] H') {y : H} (hy : y ∈ HopfAlgebra.hopfKer π) :
    π y = algebraMap F H' (Coalgebra.counit (R := F) y) := by
  classical
  have h1 : ∑ i ∈ (Coalgebra.Repr.arbitrary F y).index,
      (Coalgebra.Repr.arbitrary F y).left i ⊗ₜ[F] π ((Coalgebra.Repr.arbitrary F y).right i) = y ⊗ₜ[F] (1 : H') :=
    (HopfAlgebra.HopfKerHopf.coaction_repr π (Coalgebra.Repr.arbitrary F y)).symm.trans
      (HopfAlgebra.coaction_eq_of_mem π hy)
  have h2 := congrArg (TensorProduct.lift ((LinearMap.lsmul F H').comp (Coalgebra.counit (R := F) (A := H)))) h1
  simp only [map_sum, TensorProduct.lift.tmul, LinearMap.comp_apply, LinearMap.lsmul_apply] at h2
  calc π y = π (∑ i ∈ (Coalgebra.Repr.arbitrary F y).index,
          Coalgebra.counit (R := F) ((Coalgebra.Repr.arbitrary F y).left i) •
            (Coalgebra.Repr.arbitrary F y).right i) := by
        rw [Coalgebra.sum_counit_smul]
    _ = ∑ i ∈ (Coalgebra.Repr.arbitrary F y).index,
          Coalgebra.counit (R := F) ((Coalgebra.Repr.arbitrary F y).left i) •
            π ((Coalgebra.Repr.arbitrary F y).right i) := by
        simp only [map_sum, map_smul]
    _ = Coalgebra.counit (R := F) y • (1 : H') := h2
    _ = algebraMap F H' (Coalgebra.counit (R := F) y) := (Algebra.algebraMap_eq_smul_one _).symm

private theorem apply_mem_hopfKer_of_comm (π g : H →ₐc[F] H) (hcomm : ∀ b, π (g b) = g (π b)) {y : H}
    (hy : y ∈ HopfAlgebra.hopfKer π) : g y ∈ HopfAlgebra.hopfKer π := by
  classical
  rw [HopfAlgebra.mem_hopfKer_iff] at hy ⊢
  rw [HopfAlgebra.HopfKerHopf.coaction_repr π (Coalgebra.Repr.arbitrary F y)] at hy
  rw [HopfAlgebra.HopfKerHopf.coaction_repr π (HopfAlgebra.HopfKerHopf.reprMap g (Coalgebra.Repr.arbitrary F y))]
  simp only [HopfAlgebra.HopfKerHopf.reprMap, hcomm]
  have h3 := congrArg (TensorProduct.map (g : H →ₐc[F] H).toLinearMap (g : H →ₐc[F] H).toLinearMap) hy
  simp only [map_sum, TensorProduct.map_tmul, HopfAlgebra.HopfKerHopf.toLinearMap_apply', map_one] at h3
  exact h3

private theorem apply_mem_hopfKer_of_comp_eq {H' : Type w} [CommRing H'] [HopfAlgebra F H'] (π : H →ₐc[F] H')
    (g : H →ₐc[F] H) (hg : ∀ c, π (g c) = algebraMap F H' (Coalgebra.counit (R := F) c)) (b : H) :
    g b ∈ HopfAlgebra.hopfKer π := by
  classical
  rw [HopfAlgebra.mem_hopfKer_iff,
    HopfAlgebra.HopfKerHopf.coaction_repr π (HopfAlgebra.HopfKerHopf.reprMap g (Coalgebra.Repr.arbitrary F b))]
  simp only [HopfAlgebra.HopfKerHopf.reprMap, hg]
  have h := congrArg (LinearMap.lTensor H (Algebra.linearMap F H'))
    (Coalgebra.sum_map_tmul_counit_eq (R := F) g b (repr := Coalgebra.Repr.arbitrary F b))
  simp only [map_sum, LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one] at h
  exact h

private theorem hopfKer_comp_eq_of_injective {Q : Type w} [CommRing Q] [HopfAlgebra F Q]
    {H' : Type x} [CommRing H'] [HopfAlgebra F H'] (ρ : H →ₐc[F] Q) (ι : Q →ₐc[F] H') (hι : Function.Injective ι) :
    HopfAlgebra.hopfKer (ι.comp ρ) = HopfAlgebra.hopfKer ρ := by
  have hinj : Function.Injective ((ι : Q →ₐc[F] H').toLinearMap.lTensor H) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hι
  have key : ∀ z : H, HopfAlgebra.coaction (ι.comp ρ) z =
      (ι : Q →ₐc[F] H').toLinearMap.lTensor H (HopfAlgebra.coaction ρ z) := by
    intro z
    rw [HopfAlgebra.HopfKerHopf.coaction_eq_map, HopfAlgebra.HopfKerHopf.coaction_eq_map]
    induction Coalgebra.comul (R := F) z with
    | zero => simp only [map_zero]
    | tmul a b =>
      simp only [TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.id_apply,
        HopfAlgebra.HopfKerHopf.toLinearMap_apply', BialgHom.coe_comp, Function.comp_apply]
    | add s t hs ht => simp only [map_add, hs, ht]
  ext a
  simp only [HopfAlgebra.mem_hopfKer_iff, key]
  constructor
  · intro h
    apply hinj
    rw [h, LinearMap.lTensor_tmul, HopfAlgebra.HopfKerHopf.toLinearMap_apply', map_one]
  · intro h
    rw [h, LinearMap.lTensor_tmul, HopfAlgebra.HopfKerHopf.toLinearMap_apply', map_one]

private theorem finrank_hopfKer_mul_finrank_range [Module.Finite F H] (φ : H →ₐc[F] H) :
    Module.finrank F ↥(HopfAlgebra.hopfKer φ) * Module.finrank F ↥(LinearMap.range φ.toLinearMap) =
      Module.finrank F H := by
  obtain ⟨Q, _, _, _, _, ρ, ι, hρ, hι, hcomp⟩ :=
    HopfAlgebra.exists_hopfAlgebra_surjective_injective_comp_eq (R := F) (H := H) (H' := H) φ
  obtain ⟨-, -, -, h4⟩ := HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective (R := F) ρ hρ
  have h6 : Module.finrank F ↥(HopfAlgebra.hopfKer ρ) * Module.finrank F Q = Module.finrank F H := by
    simpa using h4 ⟨⊥, Ideal.isPrime_bot⟩
  have hker : HopfAlgebra.hopfKer φ = HopfAlgebra.hopfKer ρ := by
    rw [← hcomp]; exact hopfKer_comp_eq_of_injective ρ ι hι
  have hQ : Module.finrank F ↥(LinearMap.range φ.toLinearMap) = Module.finrank F Q := by
    have h1 : φ.toLinearMap = (ι : Q →ₐc[F] H).toLinearMap ∘ₗ (ρ : H →ₐc[F] Q).toLinearMap := by
      rw [← hcomp]; exact LinearMap.ext fun b => rfl
    have h2 : LinearMap.range (ρ : H →ₐc[F] Q).toLinearMap = ⊤ := LinearMap.range_eq_top.mpr fun z => hρ z
    rw [h1, LinearMap.range_comp, h2, Submodule.map_top]
    exact LinearMap.finrank_range_of_inj (f := (ι : Q →ₐc[F] H).toLinearMap) fun a b hab => hι hab
  rw [hker, hQ]
  exact h6

private theorem prod_toConv_comp {C : Type*} [AddCommMonoid C] [Module F C] [Coalgebra F C] [Coalgebra.IsCocomm F C]
    {A₁ : Type*} [CommRing A₁] [Algebra F A₁] {A₂ : Type*} [CommRing A₂] [Algebra F A₂]
    (h : A₁ →ₐ[F] A₂) (g : ℕ → (C →ₗ[F] A₁)) :
    ∀ j : ℕ, (∏ i ∈ Finset.range j, toConv (h.toLinearMap ∘ₗ g i)) =
      toConv (h.toLinearMap ∘ₗ (∏ i ∈ Finset.range j, toConv (g i)).ofConv)
  | 0 => by
    rw [Finset.prod_range_zero, Finset.prod_range_zero]
    refine WithConv.ext (LinearMap.ext fun c => ?_)
    simp only [LinearMap.convOne_def, WithConv.ofConv_toConv, LinearMap.comp_apply, Algebra.linearMap_apply,
      AlgHom.toLinearMap_apply, AlgHom.commutes]
  | j + 1 => by
    rw [Finset.prod_range_succ, Finset.prod_range_succ, prod_toConv_comp h g j, LinearMap.algHom_comp_convMul_distrib]

private theorem exists_mem_hopfKer_apply_eq [Coalgebra.IsCocomm F H] {H' : Type w} [CommRing H'] [HopfAlgebra F H']
    (π : H →ₐc[F] H') (n : H →ₐc[F] H) (ρ : H →ₐ[F] H) (M : ℕ)
    (hn : ∀ y ∈ HopfAlgebra.hopfKer π, n y ∈ HopfAlgebra.hopfKer π)
    (hnil : ∀ y ∈ HopfAlgebra.hopfKer π, (n ^ M) y = algebraMap F H (Coalgebra.counit (R := F) y))
    (hρn : toConv ρ.toLinearMap * toConv (n : H →ₐc[F] H).toLinearMap = toConv (LinearMap.id : H →ₗ[F] H)) :
    ∀ y ∈ HopfAlgebra.hopfKer π, ∃ x ∈ HopfAlgebra.hopfKer π, ρ x = y := by
  classical
  intro y hy
  have hmem : ∀ (i : ℕ) (s : ↥(HopfAlgebra.hopfKer π)), (n ^ i) (s : H) ∈ HopfAlgebra.hopfKer π := by
    intro i
    induction i with
    | zero => intro s; rw [pow_zero, BialgHom.one_apply]; exact s.2
    | succ i ih => intro s; rw [pow_succ', BialgHom.mul_apply]; exact hn _ (ih s)

  obtain ⟨c, hc⟩ : ∃ c : ℕ → (↥(HopfAlgebra.hopfKer π) →ₗc[F] H),
      ∀ (i : ℕ) (s : ↥(HopfAlgebra.hopfKer π)), (c i).toLinearMap s = (n ^ i) (s : H) :=
    ⟨fun i => ((n ^ i).comp (HopfAlgebra.hopfKerVal π)).toCoalgHom, fun _ _ => rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ → (↥(HopfAlgebra.hopfKer π) →ₗ[F] ↥(HopfAlgebra.hopfKer π)),
      ∀ (i : ℕ) (s : ↥(HopfAlgebra.hopfKer π)), ((d i s : ↥(HopfAlgebra.hopfKer π)) : H) = (n ^ i) (s : H) :=
    ⟨fun i => ((((n ^ i : H →ₐc[F] H) : H →ₐ[F] H).comp (HopfAlgebra.hopfKer π).val).codRestrict
        (HopfAlgebra.hopfKer π) (fun s => hmem i s)).toLinearMap, fun _ _ => rfl⟩
  have hcd : ∀ i, (c i).toLinearMap = (HopfAlgebra.hopfKer π).val.toLinearMap ∘ₗ d i :=
    fun i => LinearMap.ext fun s => (hc i s).trans (hd i s).symm
  have hn' : ∀ i, (n : H →ₐc[F] H).toLinearMap ∘ₗ (c i).toLinearMap = (c (i + 1)).toLinearMap := by
    intro i
    refine LinearMap.ext fun s => ?_
    rw [LinearMap.comp_apply, hc i s, hc (i + 1) s, pow_succ', BialgHom.mul_apply,
      HopfAlgebra.HopfKerHopf.toLinearMap_apply']

  have hstep : ∀ i, toConv (ρ.toLinearMap ∘ₗ (c i).toLinearMap) * toConv (c (i + 1)).toLinearMap =
      toConv (c i).toLinearMap := by
    intro i
    have e := LinearMap.convMul_comp_coalgHom_distrib (toConv ρ.toLinearMap)
      (toConv (n : H →ₐc[F] H).toLinearMap) (c i)
    rw [hρn] at e
    simp only [LinearMap.id_comp] at e
    rw [← hn' i]
    exact WithConv.ext e.symm
  have hJ : ∀ j : ℕ, (∏ i ∈ Finset.range j, toConv (ρ.toLinearMap ∘ₗ (c i).toLinearMap)) * toConv (c j).toLinearMap =
      toConv (c 0).toLinearMap := by
    intro j
    induction j with
    | zero => rw [Finset.prod_range_zero, one_mul]
    | succ j ih => rw [Finset.prod_range_succ, mul_assoc, hstep j, ih]

  have hVM : toConv (c M).toLinearMap = (1 : WithConv (↥(HopfAlgebra.hopfKer π) →ₗ[F] H)) := by
    refine WithConv.ext (LinearMap.ext fun s => ?_)
    rw [LinearMap.convOne_def]
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply]
    rw [hc M s]
    exact hnil (s : H) s.2
  have hP : (∏ i ∈ Finset.range M, toConv (ρ.toLinearMap ∘ₗ (c i).toLinearMap)) = toConv (c 0).toLinearMap := by
    have h := hJ M
    rwa [hVM, mul_one] at h
  have hP1 : (∏ i ∈ Finset.range M, toConv (ρ.toLinearMap ∘ₗ (c i).toLinearMap)) =
      toConv (ρ.toLinearMap ∘ₗ (∏ i ∈ Finset.range M, toConv (c i).toLinearMap).ofConv) :=
    prod_toConv_comp ρ (fun i => (c i).toLinearMap) M
  have hP2 : (∏ i ∈ Finset.range M, toConv ((HopfAlgebra.hopfKer π).val.toLinearMap ∘ₗ d i)) =
      toConv ((HopfAlgebra.hopfKer π).val.toLinearMap ∘ₗ (∏ i ∈ Finset.range M, toConv (d i)).ofConv) :=
    prod_toConv_comp (HopfAlgebra.hopfKer π).val d M
  rw [hP1] at hP
  simp only [hcd] at hP
  rw [hP2] at hP
  have hP4 := LinearMap.congr_fun (congrArg WithConv.ofConv hP) (⟨y, hy⟩ : ↥(HopfAlgebra.hopfKer π))
  have hP5 : ρ (((∏ i ∈ Finset.range M, toConv (d i)).ofConv (⟨y, hy⟩ : ↥(HopfAlgebra.hopfKer π)) :
      ↥(HopfAlgebra.hopfKer π)) : H) = ((d 0 ⟨y, hy⟩ : ↥(HopfAlgebra.hopfKer π)) : H) := hP4
  rw [hd 0 ⟨y, hy⟩, pow_zero, BialgHom.one_apply] at hP5
  exact ⟨_, ((∏ i ∈ Finset.range M, toConv (d i)).ofConv (⟨y, hy⟩ : ↥(HopfAlgebra.hopfKer π))).2, hP5⟩

end Generic
p2m_reactivate "P2MW.S_HopfAlgebra_natCard_algHom_mul_natCard_algHom_cartierDual_eq_finrank_of_map_eq_conv_frobenius.OrdConnEb2Pts"

section Main

variable (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [HopfAlgebra (ZMod q) B]
  [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]

private theorem finrank_range_mul_finrank_range_eq
    (T : B →ₐc[ZMod q] B) (hT : Function.Bijective T)
    (Fk : B →ₐc[ZMod q] B) (hFk : ∀ x, Fk x = x ^ q)
    (V : B →ₐc[ZMod q] B) (hVF : ∀ b, V (Fk b) = Fk (V b)) (hVT : ∀ b, V (T b) = T (V b))
    (hTFV : WithConv.toConv (T : B →ₗ[ZMod q] B) =
      WithConv.toConv (Fk : B →ₗ[ZMod q] B) * WithConv.toConv (V : B →ₗ[ZMod q] B))
    (N : ℕ)
    (hVpt : ∀ (θ : B →ₐ[ZMod q] AlgebraicClosure (ZMod q)) (n : ℕ), N ≤ n →
      ∀ b, θ ((⇑V)^[n] b) = algebraMap (ZMod q) _ (Coalgebra.counit b))
    (hsep : ∀ (n : ℕ), Module.finrank (ZMod q) B ≤ n → ∀ x y : B,
      x ∈ LinearMap.range ((Fk : B →ₗ[ZMod q] B) ^ n) → y ∈ LinearMap.range ((Fk : B →ₗ[ZMod q] B) ^ n) →
      (∀ χ : B →ₐ[ZMod q] AlgebraicClosure (ZMod q), χ x = χ y) → x = y)
    (M : ℕ) (hM : Module.finrank (ZMod q) B ≤ M) (hMN : N ≤ M) :
    Module.finrank (ZMod q) ↥(LinearMap.range ((Fk : B →ₗ[ZMod q] B) ^ M)) *
        Module.finrank (ZMod q) ↥(LinearMap.range ((V : B →ₗ[ZMod q] B) ^ M)) =
      Module.finrank (ZMod q) B := by
  classical
  have _ := hVF
  have _ := hVT

  have hFkL : ((Fk : B →ₗ[ZMod q] B) ^ M) = (Fk ^ M).toLinearMap :=
    LinearMap.ext fun b => (Module.End.pow_apply (Fk : B →ₗ[ZMod q] B) M b).trans
      ((bialgHom_pow_apply Fk M b).symm.trans (HopfAlgebra.HopfKerHopf.toLinearMap_apply' (Fk ^ M) b).symm)
  have hVL : ((V : B →ₗ[ZMod q] B) ^ M) = (V ^ M).toLinearMap :=
    LinearMap.ext fun b => (Module.End.pow_apply (V : B →ₗ[ZMod q] B) M b).trans
      ((bialgHom_pow_apply V M b).symm.trans (HopfAlgebra.HopfKerHopf.toLinearMap_apply' (V ^ M) b).symm)

  have hVK : ∀ b : B, (V ^ M) b ∈ HopfAlgebra.hopfKer (Fk ^ M) := by
    refine apply_mem_hopfKer_of_comp_eq (Fk ^ M) (V ^ M) (fun c => ?_)
    have hx : (Fk ^ M) ((V ^ M) c) ∈ LinearMap.range ((Fk : B →ₗ[ZMod q] B) ^ M) := by
      rw [hFkL]; exact LinearMap.mem_range.mpr ⟨(V ^ M) c, rfl⟩
    have hy : algebraMap (ZMod q) B (Coalgebra.counit (R := ZMod q) c) ∈
        LinearMap.range ((Fk : B →ₗ[ZMod q] B) ^ M) := by
      rw [hFkL]
      exact LinearMap.mem_range.mpr ⟨algebraMap (ZMod q) B (Coalgebra.counit (R := ZMod q) c),
        AlgHomClass.commutes (Fk ^ M) (Coalgebra.counit (R := ZMod q) c)⟩
    refine hsep M hM _ _ hx hy fun χ => ?_
    rw [AlgHomClass.commutes χ]
    have h := hVpt (χ.comp ((Fk ^ M : B →ₐc[ZMod q] B) : B →ₐ[ZMod q] B)) M hMN c
    rwa [AlgHom.comp_apply, ← bialgHom_pow_apply] at h

  set e : B ≃ₐc[ZMod q] B := BialgEquiv.ofBijective T hT with he
  set σ : B →ₐc[ZMod q] B := (e.symm : B →ₐc[ZMod q] B) with hσ
  have hσT : ∀ b, σ (T b) = b := fun b => e.symm_apply_apply b
  have hTσ : ∀ b, T (σ b) = b := fun b => e.apply_symm_apply b
  have hσF : ∀ b, σ (Fk b) = Fk (σ b) := by
    intro b; rw [hFk, hFk, map_pow]
  have hcommF : ∀ b, (Fk ^ M) (Fk b) = Fk ((Fk ^ M) b) := by
    intro b; rw [← BialgHom.mul_apply (Fk ^ M) Fk b, ← pow_succ, pow_succ', BialgHom.mul_apply]
  have hcommσ : ∀ b, (Fk ^ M) (σ b) = σ ((Fk ^ M) b) := fun b => (comm_pow hσF M b).symm
  have hσFk : Commute σ Fk := BialgHom.ext fun b => by rw [BialgHom.mul_apply, BialgHom.mul_apply, hσF]
  have hn : ∀ y ∈ HopfAlgebra.hopfKer (Fk ^ M), (σ * Fk) y ∈ HopfAlgebra.hopfKer (Fk ^ M) := by
    intro y hy
    rw [BialgHom.mul_apply]
    exact apply_mem_hopfKer_of_comm (Fk ^ M) σ hcommσ (apply_mem_hopfKer_of_comm (Fk ^ M) Fk hcommF hy)
  have hnil : ∀ y ∈ HopfAlgebra.hopfKer (Fk ^ M),
      ((σ * Fk) ^ M) y = algebraMap (ZMod q) B (Coalgebra.counit (R := ZMod q) y) := by
    intro y hy
    rw [hσFk.mul_pow, BialgHom.mul_apply, apply_eq_algebraMap_counit_of_mem_hopfKer (Fk ^ M) hy]
    exact AlgHomClass.commutes (σ ^ M) _
  have hρn : toConv ((σ : B →ₐ[ZMod q] B).comp (V : B →ₐ[ZMod q] B)).toLinearMap *
      toConv (σ * Fk : B →ₐc[ZMod q] B).toLinearMap = toConv (LinearMap.id : B →ₗ[ZMod q] B) := by
    have e1 := LinearMap.algHom_comp_convMul_distrib (σ : B →ₐ[ZMod q] B)
      (WithConv.toConv (Fk : B →ₗ[ZMod q] B)) (WithConv.toConv (V : B →ₗ[ZMod q] B))
    rw [← hTFV] at e1
    simp only at e1
    have hid : (σ : B →ₐ[ZMod q] B).toLinearMap ∘ₗ (T : B →ₗ[ZMod q] B) = LinearMap.id :=
      LinearMap.ext fun b => hσT b
    rw [hid] at e1
    have e2 : toConv ((σ : B →ₐ[ZMod q] B).toLinearMap ∘ₗ (Fk : B →ₗ[ZMod q] B)) *
        toConv ((σ : B →ₐ[ZMod q] B).toLinearMap ∘ₗ (V : B →ₗ[ZMod q] B)) = toConv (LinearMap.id : B →ₗ[ZMod q] B) :=
      WithConv.ext e1.symm
    have hρL : ((σ : B →ₐ[ZMod q] B).comp (V : B →ₐ[ZMod q] B)).toLinearMap =
        (σ : B →ₐ[ZMod q] B).toLinearMap ∘ₗ (V : B →ₗ[ZMod q] B) := LinearMap.ext fun b => rfl
    have hnL : (σ * Fk : B →ₐc[ZMod q] B).toLinearMap =
        (σ : B →ₐ[ZMod q] B).toLinearMap ∘ₗ (Fk : B →ₗ[ZMod q] B) := LinearMap.ext fun b => rfl
    rw [hρL, hnL, mul_comm]
    exact e2
  have hsurj : ∀ y ∈ HopfAlgebra.hopfKer (Fk ^ M), ∃ x ∈ HopfAlgebra.hopfKer (Fk ^ M), V x = y := by
    intro y hy
    obtain ⟨x, hx, hρx⟩ := exists_mem_hopfKer_apply_eq (Fk ^ M) (σ * Fk)
      ((σ : B →ₐ[ZMod q] B).comp (V : B →ₐ[ZMod q] B))
      M hn hnil hρn (σ y) (apply_mem_hopfKer_of_comm (Fk ^ M) σ hcommσ hy)
    refine ⟨x, hx, ?_⟩
    have h1 : σ (V x) = σ y := hρx
    have h2 := congrArg T h1
    rwa [hTσ, hTσ] at h2
  have hiter : ∀ (j : ℕ), ∀ y ∈ HopfAlgebra.hopfKer (Fk ^ M), ∃ x ∈ HopfAlgebra.hopfKer (Fk ^ M), (⇑V)^[j] x = y := by
    intro j
    induction j with
    | zero => intro y hy; exact ⟨y, hy, rfl⟩
    | succ j ih =>
      intro y hy
      obtain ⟨x₁, hx₁, hVx₁⟩ := hsurj y hy
      obtain ⟨x, hx, hjx⟩ := ih x₁ hx₁
      exact ⟨x, hx, by rw [Function.iterate_succ_apply', hjx, hVx₁]⟩

  have hrange : LinearMap.range ((V : B →ₗ[ZMod q] B) ^ M) =
      Subalgebra.toSubmodule (HopfAlgebra.hopfKer (Fk ^ M)) := by
    rw [hVL]
    refine le_antisymm ?_ ?_
    · rintro _ ⟨b, rfl⟩
      exact hVK b
    · intro y hy
      obtain ⟨x, -, hx⟩ := hiter M y hy
      exact LinearMap.mem_range.mpr
        ⟨x, (HopfAlgebra.HopfKerHopf.toLinearMap_apply' (V ^ M) x).trans ((bialgHom_pow_apply V M x).trans hx)⟩
  rw [hrange, Subalgebra.finrank_toSubmodule, hFkL, mul_comm]
  exact finrank_hopfKer_mul_finrank_range (Fk ^ M)

end Main
p2m_reactivate "P2MW.S_HopfAlgebra_natCard_algHom_mul_natCard_algHom_cartierDual_eq_finrank_of_map_eq_conv_frobenius.OrdConnEb2Pts"

end OrdConnEb2Split
p2m_reactivate "P2MW.S_HopfAlgebra_natCard_algHom_mul_natCard_algHom_cartierDual_eq_finrank_of_map_eq_conv_frobenius.OrdConnEb2Pts"

theorem solution
    (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [HopfAlgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]
    (N : ℕ) (hN : WithConv.toConv (LinearMap.id : B →ₗ[ZMod q] B) ^ (q ^ N) = 1)
    (T : B →ₐc[ZMod q] B) (hT : Function.Bijective T)
    (Fk : B →ₐc[ZMod q] B) (hFk : ∀ x, Fk x = x ^ q)
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q)
    (hFV : (CartierDual.map T : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) =
      (WithConv.toConv
          (CartierDual.map Fk : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) *
        WithConv.toConv
          (FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B)).ofConv) :
    Nat.card (B →ₐ[ZMod q] AlgebraicClosure (ZMod q)) *
        Nat.card (CartierDual (ZMod q) B →ₐ[ZMod q] AlgebraicClosure (ZMod q)) =
      Module.finrank (ZMod q) B := by
  obtain ⟨V, _hV1, hVF', hVT', hTFV, hVpt, hVrank⟩ :=
    OrdConnEb2Dual.exists_verschiebung q B N hN T Fk hFk FD hFD hFV
  obtain ⟨M, hM, hMN, hMD⟩ : ∃ M : ℕ, Module.finrank (ZMod q) B ≤ M ∧ N ≤ M ∧
      Module.finrank (ZMod q) (CartierDual (ZMod q) B) ≤ M :=
    ⟨N + Module.finrank (ZMod q) B + Module.finrank (ZMod q) (CartierDual (ZMod q) B),
      by omega, by omega, by omega⟩
  have hsplit := OrdConnEb2Split.finrank_range_mul_finrank_range_eq q B T hT Fk hFk V hVF' hVT' hTFV N hVpt
    (fun n hn x y hx hy h => OrdConnEb2Pts.forall_algHom_apply_eq_imp_eq_lin q B (Fk : B →ₗ[ZMod q] B)
      (fun b => hFk b) (AlgebraicClosure (ZMod q)) n hn x y hx hy h) M hM hMN
  have hB : Nat.card (B →ₐ[ZMod q] AlgebraicClosure (ZMod q)) =
      Module.finrank (ZMod q) ↥(LinearMap.range ((Fk : B →ₗ[ZMod q] B) ^ M)) :=
    OrdConnEb2Pts.natCard_algHom_eq_finrank_range_lin q B (Fk : B →ₗ[ZMod q] B) (fun b => hFk b)
      (AlgebraicClosure (ZMod q)) M hM
  have hD : Nat.card (CartierDual (ZMod q) B →ₐ[ZMod q] AlgebraicClosure (ZMod q)) =
      Module.finrank (ZMod q) ↥(LinearMap.range (FD.toLinearMap ^ M)) :=
    OrdConnEb2Pts.natCard_algHom_eq_finrank_range_lin q (CartierDual (ZMod q) B) FD.toLinearMap
      (fun ψ => hFD ψ) (AlgebraicClosure (ZMod q)) M hMD
  rw [hB, hD, ← hVrank M]
  exact hsplit

#print axioms solution

end S_HopfAlgebra_natCard_algHom_mul_natCard_algHom_cartierDual_eq_finrank_of_map_eq_conv_frobenius
end P2MW
export P2MW.S_HopfAlgebra_natCard_algHom_mul_natCard_algHom_cartierDual_eq_finrank_of_map_eq_conv_frobenius (solution)
