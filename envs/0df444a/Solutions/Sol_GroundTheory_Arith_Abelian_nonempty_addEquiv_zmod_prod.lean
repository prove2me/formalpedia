-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.nonempty_addEquiv_zmod_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:52:33.624951+00:00
-- url     : https://prove2.me/submissions/8ca19d05-5a8a-446a-b1f7-2b230e7c2551

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Torsion
import Theorems.Thm_GroundTheory_Arith_Abelian_exists_addOrderOf_eq_of_card
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some


section
namespace GroundTheory.Arith.Abelian
open AddSubgroup
section Group
variable {A : Type*} [AddCommGroup A]
private theorem zmodHom_apply {n : ℕ} [NeZero n] (P : A) (hP : n • P = 0) (a : ZMod n) :
    zmodHom n P hP a = a.val • P := by
  have h : ((a.val : ℤ) : ZMod n) = a := by simp
  conv_lhs => rw [← h]
  rw [zmodHom, ZMod.lift_coe]
  simp only [zmultiplesHom_apply, natCast_zsmul]
end Group
section Curve
variable {F : Type*} [Field F] [IsSepClosed F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
end Curve
end GroundTheory.Arith.Abelian
end

set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open AddSubgroup
variable {A : Type*} [AddCommGroup A]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {n : ℕ} (hn : 0 < n) (hA : ∀ a : A, n • a = 0)
    (hcard : Nat.card A = n ^ 2)
    (hker : ∀ m, m ∣ n → Nat.card {a : A // m • a = 0} ≤ m ^ 2) :
    Nonempty (A ≃+ ZMod n × ZMod n) := by
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨P, hP⟩ := exists_addOrderOf_eq_of_card hn hA hcard hker
  set C := AddSubgroup.zmultiples P with hCdef
  have hC : Nat.card C = n := by rw [Nat.card_zmultiples, hP]
  have hB : Nat.card (A ⧸ C) = n := by
    have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup C
    rw [hcard, hC] at h
    have : n * n = Nat.card (A ⧸ C) * n := by rw [← h]; ring
    exact (Nat.eq_of_mul_eq_mul_right hn this).symm
  have hBn : ∀ b : A ⧸ C, n • b = 0 := by
    intro b
    induction b using QuotientAddGroup.induction_on with
    | H a => rw [← QuotientAddGroup.mk_nsmul, hA, QuotientAddGroup.mk_zero]

  obtain ⟨Qb, hQb⟩ : ∃ Qb : A ⧸ C, addOrderOf Qb = n := by
    have hexB : AddMonoid.ExponentExists (A ⧸ C) := ⟨n, hn, hBn⟩
    obtain ⟨Qb, hQ⟩ := AddMonoid.exists_addOrderOf_eq_exponent hexB
    refine ⟨Qb, hQ.trans ?_⟩
    set m := AddMonoid.exponent (A ⧸ C) with hmdef
    have hm : m ∣ n := AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero hBn
    have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hm hn
    obtain ⟨d, hd⟩ := hm
    have hdpos : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hd; omega)
    let φ : A →+ A :=
      { toFun := fun a => m • a
        map_zero' := nsmul_zero m
        map_add' := fun a b => nsmul_add a b m }
    have hφ : ∀ a, φ a = m • a := fun a => rfl

    have hkerφ : Nat.card φ.ker ≤ m ^ 2 := by
      have : Nat.card φ.ker = Nat.card {a : A // m • a = 0} :=
        Nat.card_congr (Equiv.subtypeEquivRight fun a => by rw [AddMonoidHom.mem_ker, hφ])
      rw [this]
      exact hker m ⟨d, hd⟩

    have hrange : Nat.card φ.range ≤ d := by
      have hmem : ∀ x : φ.range, (x : A) ∈ C := by
        rintro ⟨_, a, rfl⟩
        show φ a ∈ C
        rw [← QuotientAddGroup.eq_zero_iff, hφ, QuotientAddGroup.mk_nsmul]
        exact AddMonoid.exponent_nsmul_eq_zero _
      have hd' : ∀ x : φ.range, d • (x : A) = 0 := by
        rintro ⟨_, a, rfl⟩
        show d • φ a = 0
        rw [hφ, ← mul_nsmul', mul_comm, ← hd, hA]
      let ι : φ.range → {c : C // d • c = 0} := fun x =>
        ⟨⟨x, hmem x⟩, by
          apply Subtype.ext
          simp only [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]
          exact hd' x⟩
      have hι : Function.Injective ι := by
        intro x y h
        have := congrArg (fun z => ((z.1 : C) : A)) h
        exact Subtype.ext this
      have hle := Nat.card_le_card_of_injective ι hι
      classical
      have : Fintype C := Fintype.ofFinite C
      have hcyc := IsAddCyclic.card_nsmul_eq_zero_le (α := C) hdpos
      rw [Nat.card_eq_fintype_card (α := {c : C // d • c = 0}), Fintype.card_subtype] at hle
      exact hle.trans (by convert hcyc)
    have htot : Nat.card A = Nat.card φ.ker * Nat.card φ.range := by
      rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker,
        Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv, mul_comm]
    rw [hcard, hd] at htot
    have h1 : (m * d) ^ 2 ≤ m ^ 2 * d := by
      rw [htot]; exact Nat.mul_le_mul hkerφ hrange
    have hd1 : d ≤ 1 := by
      by_contra h
      push Not at h
      have : m ^ 2 * d < (m * d) ^ 2 := by
        rw [mul_pow]
        have : d < d ^ 2 := by nlinarith
        exact Nat.mul_lt_mul_of_pos_left this (by positivity)
      omega
    have : d = 1 := by omega
    rw [hd, this, mul_one]
  obtain ⟨Q, rfl⟩ := QuotientAddGroup.mk_surjective Qb
  have hQn : n • Q = 0 := hA Q
  let f : ZMod n × ZMod n →+ A := (zmodHom n P (hA P)).coprod (zmodHom n Q hQn)
  have hf : ∀ x : ZMod n × ZMod n, f x = x.1.val • P + x.2.val • Q := by
    intro x
    simp [f, AddMonoidHom.coprod_apply, zmodHom_apply]
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ hab
    rw [hf] at hab
    have hPC : (P : A ⧸ C) = 0 := (QuotientAddGroup.eq_zero_iff P).mpr (AddSubgroup.mem_zmultiples P)
    have hb : b.val • (Q : A ⧸ C) = 0 := by
      have := congrArg (QuotientAddGroup.mk (s := C)) hab
      simpa [QuotientAddGroup.mk_add, QuotientAddGroup.mk_nsmul, hPC] using this
    rw [← addOrderOf_dvd_iff_nsmul_eq_zero, hQb] at hb
    have hb0 : b = 0 := by
      rw [← ZMod.val_eq_zero]
      exact Nat.eq_zero_of_dvd_of_lt hb (ZMod.val_lt b)
    subst hb0
    simp only [ZMod.val_zero, zero_smul, add_zero] at hab
    rw [← addOrderOf_dvd_iff_nsmul_eq_zero, hP] at hab
    have ha0 : a = 0 := by
      rw [← ZMod.val_eq_zero]
      exact Nat.eq_zero_of_dvd_of_lt hab (ZMod.val_lt a)
    simp [ha0]
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_prod, Nat.card_zmod, sq])
  exact ⟨(AddEquiv.ofBijective f hbij).symm⟩
end GroundTheory.Arith.Abelian
