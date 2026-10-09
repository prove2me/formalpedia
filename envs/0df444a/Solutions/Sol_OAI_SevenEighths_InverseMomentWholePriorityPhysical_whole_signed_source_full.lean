-- Prove2me | solution 1 for OAI.SevenEighths.InverseMomentWholePriorityPhysical.whole_signed_source_full
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:33:58.87484+00:00
-- url     : https://prove2.me/submissions/edafb4fd-e6d1-4063-854f-c9ce95872fe7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B019

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.FiniteFourier
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap

open Finset Complex

namespace ActualEisensteinCubic

theorem cubicGauss_cube {E : Type*} [Field E] (ι : O →+* E)
    (hι : Function.Injective ι) (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1)
    (ψ : AddChar (O ⧸ P) E) (hψ : ψ.IsPrimitive) :
    gaussSum ((cubicChar P hgood).ringHomComp ι) ψ ^ 3 =
      -(ι p) * (Nat.card (O ⧸ P) : E) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ := cubicChar P hgood
  let ξ := χ.ringHomComp ι
  have hχ3 : χ ^ 3 = 1 := cubicChar_pow_three P hgood
  have hχne : χ ≠ 1 := cubicChar_ne_one P hgood
  have hχ2 : χ * χ ≠ 1 := by
    intro h
    have hd : orderOf χ ∣ 2 := by
      rw [← pow_two] at h
      exact orderOf_dvd_of_pow_eq_one h
    rw [cubicChar_order P hgood] at hd
    norm_num at hd
  have hξne : ξ ≠ 1 := (MulChar.ringHomComp_ne_one_iff hι).mpr hχne
  have hξ2 : ξ * ξ ≠ 1 := by
    rw [show ξ * ξ = (χ * χ).ringHomComp ι by
      exact (MulChar.ringHomComp_mul χ χ ι).symm]
    exact (MulChar.ringHomComp_ne_one_iff hι).mpr hχ2
  have hχinv : χ⁻¹ = χ ^ 2 := by
    apply inv_eq_iff_mul_eq_one.mpr
    simpa only [pow_succ, mul_comm] using hχ3
  have hξinv : ξ⁻¹ = ξ ^ 2 := by
    change (χ.ringHomComp ι)⁻¹ = (χ.ringHomComp ι) ^ 2
    rw [MulChar.ringHomComp_inv, MulChar.ringHomComp_pow, hχinv]
  have hξmul : ξ * ξ = ξ⁻¹ := by rw [hξinv, pow_two]
  have hχneg : χ (-1) = 1 :=
    MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd 3) hχ3
  have hξneg : ξ (-1) = 1 := by
    change ι (χ (-1)) = 1
    rw [hχneg, map_one]
  have hξinvneg : ξ⁻¹ (-1) = 1 := by
    rw [MulChar.inv_apply_eq_inv', hξneg, inv_one]
  have hgs : gaussSum ξ ψ * gaussSum ξ⁻¹ ψ = (Nat.card (O ⧸ P) : E) := by
    have h := gaussSum_mul_gaussSum_eq_card hξne hψ
    have hshift := mul_gaussSum_inv_eq_gaussSum ξ⁻¹ ψ
    rw [hξinvneg, one_mul] at hshift
    rw [hshift] at h
    simpa only [Nat.card_eq_fintype_card] using h
  have hJ : jacobiSum ξ ξ = -(ι p) := by
    change jacobiSum (χ.ringHomComp ι) (χ.ringHomComp ι) = -(ι p)
    rw [jacobiSum_ringHomComp]
    rw [cubicJacobi_eq_neg_primary_generator_of_principal P hgood p hP hprimary,
      map_neg]
  have hgj : gaussSum ξ⁻¹ ψ * jacobiSum ξ ξ = gaussSum ξ ψ * gaussSum ξ ψ := by
    simpa only [hξmul] using jacobiSum_mul_nontrivial hξ2 ψ
  calc
    gaussSum ξ ψ ^ 3 = (gaussSum ξ ψ * gaussSum ξ ψ) * gaussSum ξ ψ := by ring
    _ = (gaussSum ξ⁻¹ ψ * jacobiSum ξ ξ) * gaussSum ξ ψ := by rw [hgj]
    _ = (gaussSum ξ ψ * gaussSum ξ⁻¹ ψ) * jacobiSum ξ ξ := by ring
    _ = -(ι p) * (Nat.card (O ⧸ P) : E) := by rw [hgs, hJ]; ring

theorem primary_generator_mul_conj_eq_card (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1) :
    p * conjO p = (Nat.card (O ⧸ P) : O) := by
  have h := cubicJacobi_mul_conj P hgood
  rw [cubicJacobi_eq_neg_primary_generator_of_principal P hgood p hP hprimary,
    map_neg] at h
  simpa only [neg_mul_neg] using h

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Arithmetic.EisensteinEmbedding
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical

namespace ActualEisensteinCubic

theorem eisEmbedding_conjO (x : O) :
    ConcreteTraceCRT.eisEmbedding (conjO x) =
      star (ConcreteTraceCRT.eisEmbedding x) := by
  let ι := ConcreteTraceCRT.eisEmbedding
  let z := ι omega
  have hz3 : z ^ 3 = 1 := by
    change ι omega ^ 3 = 1
    rw [← map_pow, omega_primitive.pow_eq_one, map_one]
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hz3
    exact zero_ne_one hz3
  have hznorm : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz3 (by decide)
  have hzstar : star z = z ^ 2 := by
    apply mul_left_cancel₀ hz0
    calc
      z * star z = 1 := by rw [← starRingEnd_apply, Complex.mul_conj', hznorm]; norm_num
      _ = z * z ^ 2 := by rw [← pow_succ', hz3]
  have hhom : ι.comp conjO.toRingHom = (starRingEnd ℂ).comp ι := by
    apply RingHom.toIntAlgHom_injective
    apply (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis.algHom_ext
    rw [(IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis_gen]
    change ι (conjO omega) = star (ι omega)
    rw [conjO_omega, map_pow]
    exact hzstar.symm
  have hx := congrArg (fun f : O →+* ℂ => f x) hhom
  exact hx

theorem cubicGauss_normalized_cube_eis (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive) :
    (gaussSum ((cubicChar P hgood).ringHomComp ConcreteTraceCRT.eisEmbedding) ψ /
      (‖ConcreteTraceCRT.eisEmbedding p‖ : ℂ)) ^ 3 =
      -(ConcreteTraceCRT.eisEmbedding p) /
        (‖ConcreteTraceCRT.eisEmbedding p‖ : ℂ) := by
  let z := ConcreteTraceCRT.eisEmbedding p
  let g := gaussSum ((cubicChar P hgood).ringHomComp
    ConcreteTraceCRT.eisEmbedding) ψ
  have hnormO := primary_generator_mul_conj_eq_card P hgood p hP hprimary
  have hnormC := congrArg ConcreteTraceCRT.eisEmbedding hnormO
  rw [map_mul, eisEmbedding_conjO, map_natCast] at hnormC
  have hq : (Nat.card (O ⧸ P) : ℂ) = (‖z‖ : ℂ) ^ 2 := by
    simpa only [z, ← starRingEnd_apply, Complex.mul_conj'] using hnormC.symm
  have hqne : (Nat.card (O ⧸ P) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hn0 : (‖z‖ : ℂ) ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hq
    exact hqne hq
  have hg : g ^ 3 = -z * (Nat.card (O ⧸ P) : ℂ) :=
    cubicGauss_cube ConcreteTraceCRT.eisEmbedding
      ConcreteTraceCRT.eisEmbedding_injective P hgood p hP hprimary ψ hψ
  change (g / (‖z‖ : ℂ)) ^ 3 = -z / (‖z‖ : ℂ)
  rw [div_pow, hg, hq]
  field_simp

open AddChar MulChar

open AddChar MulChar

end ActualEisensteinCubic

namespace PrimitiveTrace

open Complex
open scoped ComplexConjugate
open EisensteinEmbedding ConcreteTraceCRT

private theorem complex_exp_trace_integer {t : ℂ}
    (ht : Complex.exp (2 * Real.pi * Complex.I * t) = 1) :
    ∃ n : ℤ, t = n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp ht
  refine ⟨n, ?_⟩
  have hnonzero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero) Complex.I_ne_zero
  apply mul_left_cancel₀ hnonzero
  calc
    (2 * Real.pi * Complex.I : ℂ) * t = n * (2 * Real.pi * Complex.I) := by
      simpa only [mul_assoc] using hn
    _ = (2 * Real.pi * Complex.I : ℂ) * n := by ring

private theorem phase_integer {z : ℂ}
    (hz : ShortDraftTrace.breveE (z / eisLam) = 1) :
    ∃ n : ℤ, z / eisLam + conj (z / eisLam) = n := by
  apply complex_exp_trace_integer
  exact hz

private theorem omega_conj : conj omega3 = omega3 ^ 2 := by
  have hs : omega3 ^ 2 = -omega3 - 1 := by
    linear_combination omega3_sq
  rw [hs]
  unfold omega3
  simp only [map_div₀, map_add, map_neg, map_one, map_mul,
    Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

private theorem reconstruction (z : ℂ) :
    z = (z / eisLam + conj (z / eisLam)) +
      (omega3 * z / eisLam + conj (omega3 * z / eisLam)) +
      (z / eisLam + conj (z / eisLam)) * omega3 := by
  have hquad := omega3_sq
  have hl : eisLam ≠ 0 := eisLam_ne_zero
  have hcl : conj eisLam = -eisLam := by
    simp only [eisLam, map_add, map_one, map_mul, map_ofNat, omega_conj]
    linear_combination 2 * hquad
  simp only [map_div₀, map_mul, omega_conj, hcl, div_neg]
  dsimp [eisLam] at *
  field_simp
  linear_combination (conj z) * hquad

private theorem in_coordinate_lattice_of_two_phases (z : ℂ)
    (hz : ShortDraftTrace.breveE (z / eisLam) = 1)
    (hwz : ShortDraftTrace.breveE (omega3 * z / eisLam) = 1) :
    z ∈ coordinateSubring := by
  obtain ⟨b, hb⟩ := phase_integer hz
  obtain ⟨c, hc⟩ := phase_integer hwz
  change ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * omega3
  refine ⟨b + c, b, ?_⟩
  calc
    z = (z / eisLam + conj (z / eisLam)) +
      (omega3 * z / eisLam + conj (omega3 * z / eisLam)) +
      (z / eisLam + conj (z / eisLam)) * omega3 := reconstruction z
    _ = ((b + c : ℤ) : ℂ) + (b : ℂ) * omega3 := by
      rw [hb, hc]
      push_cast
      ring

theorem eisTraceModChar_breveE_ne_one
    (P : Ideal O) [P.IsMaximal] (p : O)
    (hP : P = Ideal.span {p}) (hp : p ≠ 0) :
    eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp ≠ 1 := by
  intro hψ
  let ι := eisEmbedding
  let z : ℂ := (ι p)⁻¹
  have hpι : ι p ≠ 0 := eisEmbedding_ne_zero hp
  have hbase1 : ∀ x : O,
      ShortDraftTrace.breveE (ι x / (ι p * eisLam)) = 1 := by
    intro x
    have hpoint := congrArg
      (fun f : AddChar (O ⧸ Ideal.span {p}) ℂ =>
        f (Ideal.Quotient.mk (Ideal.span {p}) x)) hψ
    simpa only [eisTraceModChar, IdealGaussCRT.traceModChar_mk,
      AddChar.one_apply] using hpoint
  have h1 : ShortDraftTrace.breveE (z / eisLam) = 1 := by
    convert (preTransparency := .instances) hbase1 1 using 1 ; dsimp [z, ι] ; simp ; field_simp
  have hw : ShortDraftTrace.breveE (omega3 * z / eisLam) = 1 := by
    convert (preTransparency := .instances) hbase1 pb.gen using 1
    · rw [show ι pb.gen = omega3 from embedding_gen omega3 omega3_sq]
      dsimp [z]
      field_simp
  have hz := in_coordinate_lattice_of_two_phases z h1 hw
  obtain ⟨q, hq⟩ := toCoordinateSubring_surjective ⟨z, hz⟩
  have hιq : ι q = z := congrArg Subtype.val hq
  have hpq : p * q = 1 := by
    apply eisEmbedding_injective
    rw [map_mul, map_one, hιq]
    dsimp [z]
    exact mul_inv_cancel₀ hpι
  have hunit : IsUnit p := isUnit_iff_dvd_one.mpr ⟨q, hpq.symm⟩
  have htop : P = ⊤ := by
    rw [hP]
    exact Ideal.span_singleton_eq_top.mpr hunit
  exact (inferInstance : P.IsMaximal).ne_top htop

theorem eisTraceModChar_breveE_primitive
    (P : Ideal O) [P.IsMaximal] (p : O)
    (hP : P = Ideal.span {p}) (hp : p ≠ 0) :
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp).IsPrimitive := by
  have : (Ideal.span {p}).IsMaximal := hP ▸ inferInstance
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  exact AddChar.IsPrimitive.of_ne_one
    (eisTraceModChar_breveE_ne_one P p hP hp)

end PrimitiveTrace

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Cusp.MatrixPhases
namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section

namespace ActualEisensteinCoordinates

theorem eval_congr_mod_four {a b c d : ℤ}
    (ha : (a : ZMod 4) = c) (hb : (b : ZMod 4) = d) :
    ∃ z : O, eval a b - eval c d = 4 * z := by
  have ha4 : (4 : ℤ) ∣ a-c := (ZMod.intCast_eq_intCast_iff_dvd_sub c a 4).mp ha.symm
  have hb4 : (4 : ℤ) ∣ b-d := (ZMod.intCast_eq_intCast_iff_dvd_sub d b 4).mp hb.symm
  obtain ⟨u, hu⟩ := ha4
  obtain ⟨v, hv⟩ := hb4
  refine ⟨(u : O) + (v : O) * omega, ?_⟩
  dsimp [eval]
  rw [show a = c + 4*u by omega, show b = d + 4*v by omega]
  push_cast
  ring

theorem congr_mod_four_of_residue_eq {x y : O}
    (h : residue x = residue y) : ∃ z : O, x-y = 4*z := by
  rw [←eval_coords x, ←eval_coords y]
  apply eval_congr_mod_four
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

theorem residue_lift (v : EisensteinEPrimaryPhase.Coord) :
    residue (lift v) = v := by
  simp [lift, residue_eval]

end ActualEisensteinCoordinates

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.CubicNormalization
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical

namespace ActualEisensteinCubic

section

open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace

theorem cubicGauss_normalized_cube_breveE
    (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) (hprimary : lambda ^ 2 ∣ p - 1) :
    (gaussSum ((cubicChar P hgood).ringHomComp eisEmbedding)
      (hP.symm ▸ eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates p hp) /
      (‖eisEmbedding p‖ : ℂ)) ^ 3 =
      -(eisEmbedding p) / (‖eisEmbedding p‖ : ℂ) := by
  subst P
  exact cubicGauss_normalized_cube_eis (Ideal.span {p}) hgood p rfl hprimary
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp)
    (eisTraceModChar_breveE_primitive (Ideal.span {p}) p rfl hp)

end

open EisensteinEmbedding ConcreteTraceCRT

theorem breveGamma2_cube (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) (hprimary : lambda ^ 2 ∣ p - 1) :
    (breveGamma2 P hgood p hP hp) ^ 3 =
      -(eisEmbedding p) / (‖eisEmbedding p‖ : ℂ) := by
  unfold breveGamma2
  rw [canonicalSextic_pow_two]
  exact cubicGauss_normalized_cube_breveE P hgood p hP hp hprimary

end ActualEisensteinCubic

namespace JacobiQuadratic

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem square_fiber (χ : MulChar F ℂ)
    (hchar : ringChar F ≠ 2) :
    (∑ t : F, χ (1 - t ^ 2)) =
      ∑ y : F, ((quadraticChar F y : ℂ) + 1) * χ (1 - y) := by
  classical
  have hfiber : (∑ t : F, χ (1 - t ^ 2)) =
      ∑ y : F, (#{t : F | t ^ 2 = y}.toFinset : ℂ) * χ (1 - y) := by
    rw [← Finset.sum_fiberwise (s := Finset.univ)
      (g := fun t : F => t ^ 2) (f := fun t : F => χ (1 - t ^ 2))]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_congr rfl (fun t ht => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      rw [ht])]
    simp
  rw [hfiber]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  exact_mod_cast quadraticChar_card_sqrts hchar y

theorem jacobi_quadratic (χ : MulChar F ℂ)
    (hchar : ringChar F ≠ 2) (hχ : χ ≠ 1) :
    jacobiSum χ ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) =
      χ (4 : F) * jacobiSum χ χ := by
  classical
  let q : MulChar F ℂ := (quadraticChar F).ringHomComp (Int.castRingHom ℂ)
  have hsum0 : (∑ y : F, χ (1 - y)) = 0 := by
    have ht := (Equiv.sum_comp (oneSub (F := F)) χ)
    change (∑ y : F, χ ((oneSub (F := F)) y)) = 0
    exact ht.trans (MulChar.sum_eq_zero_of_ne_one hχ)
  have hfiber := square_fiber χ hchar
  have hsq : (∑ t : F, χ (1 - t ^ 2)) = jacobiSum χ q := by
    rw [hfiber]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    simp only [one_mul, hsum0, add_zero]
    exact jacobiSum_comm q χ
  have hchange : (∑ t : F, χ (1 - t ^ 2)) =
      ∑ x : F, χ (4 * x * (1 - x)) := by
    have ht := Equiv.sum_comp (affineDouble (F := F) hchar)
      (fun t : F => χ (1 - t ^ 2))
    convert (preTransparency := .instances) ht.symm using 1
    · apply Finset.sum_congr rfl
      intro x _
      congr 1
      change 4 * x * (1 - x) = 1 - (2 * x - 1) ^ 2
      ring
  calc
    jacobiSum χ q = ∑ x : F, χ (4 * x * (1 - x)) := hsq.symm.trans hchange
    _ = χ (4 : F) * jacobiSum χ χ := by
      rw [jacobiSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp only [ map_mul]
      ring

theorem gauss_sextic_relation (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hchar : ringChar F ≠ 2) (hψ : ψ.IsPrimitive)
    (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1) (hχ4 : χ ^ 4 ≠ 1)
    (hχ3 : χ ^ 3 = (quadraticChar F).ringHomComp (Int.castRingHom ℂ))
    (hχ6 : χ ^ 6 = 1) :
    χ (4 : F) * gaussSum χ ψ * (Fintype.card F : ℂ) =
      gaussSum (χ ^ 3) ψ * gaussSum (χ ^ 2) ψ ^ 2 := by

  let g1 := gaussSum χ ψ
  let g2 := gaussSum (χ ^ 2) ψ
  let g3 := gaussSum (χ ^ 3) ψ
  let g4 := gaussSum (χ ^ 4) ψ
  let J11 := jacobiSum χ χ
  let J13 := jacobiSum χ (χ ^ 3)
  have hprod2 : χ * χ = χ ^ 2 := (pow_two χ).symm
  have hprod4 : χ * χ ^ 3 = χ ^ 4 := by group
  have hJ12 : g2 * J11 = g1 * g1 := by
    have h := jacobiSum_mul_nontrivial (by rw [hprod2]; exact hχ2) ψ
      (χ := χ) (φ := χ)
    rw [hprod2] at h
    exact h
  have hJ13 : g4 * J13 = g1 * g3 := by
    have h := jacobiSum_mul_nontrivial (by rw [hprod4]; exact hχ4) ψ
      (χ := χ) (φ := χ ^ 3)
    rw [hprod4] at h
    exact h
  have hJquad : J13 = χ (4 : F) * J11 := by
    simpa only [J13, J11, hχ3] using jacobi_quadratic χ hchar hχ1
  have hg1ne : g1 ≠ 0 := by
    apply gaussSum_ne_zero_of_nontrivial
    · exact_mod_cast Fintype.card_pos.ne'
    · exact hχ1
    · exact hψ
  have h4inv : χ ^ 4 = (χ ^ 2)⁻¹ := by
    apply (inv_eq_of_mul_eq_one_right ?_).symm
    calc
      χ ^ 2 * χ ^ 4 = χ ^ 6 := by group
      _ = 1 := hχ6
  have h4minus : (χ ^ 4) (-1 : F) = 1 := by
    rw [χ.pow_apply' (by decide : (4 : ℕ) ≠ 0), ← map_pow,
      show (-1 : F) ^ 4 = 1 by ring, map_one]
  have hG4inv : gaussSum (χ ^ 4) ψ⁻¹ = g4 := by
    have h := mul_gaussSum_inv_eq_gaussSum (χ ^ 4) ψ
    rw [h4minus, one_mul] at h
    exact h
  have hG24 : g2 * g4 = (Fintype.card F : ℂ) := by
    have h := gaussSum_mul_gaussSum_eq_card hχ2 hψ
    rw [← h4inv, hG4inv] at h
    exact h
  have hbasic : g1 * g3 * g2 = χ (4 : F) * g4 * g1 ^ 2 := by
    calc
      g1 * g3 * g2 = (g4 * J13) * g2 := by rw [hJ13]
      _ = χ (4 : F) * g4 * (g2 * J11) := by rw [hJquad]; ring
      _ = χ (4 : F) * g4 * g1 ^ 2 := by rw [hJ12]; ring
  have hbasic' : g3 * g2 = χ (4 : F) * g4 * g1 := by
    apply mul_left_cancel₀ hg1ne
    calc
      g1 * (g3 * g2) = g1 * g3 * g2 := by ring
      _ = χ (4 : F) * g4 * g1 ^ 2 := hbasic
      _ = g1 * (χ (4 : F) * g4 * g1) := by ring
  calc
    χ (4 : F) * g1 * (Fintype.card F : ℂ) =
        χ (4 : F) * g1 * (g2 * g4) := by rw [hG24]
    _ = (χ (4 : F) * g4 * g1) * g2 := by ring
    _ = g3 * g2 ^ 2 := by rw [← hbasic']; ring

theorem normalized_gauss_sextic_relation (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hchar : ringChar F ≠ 2) (hψ : ψ.IsPrimitive)
    (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1) (hχ4 : χ ^ 4 ≠ 1)
    (hχ3 : χ ^ 3 = (quadraticChar F).ringHomComp (Int.castRingHom ℂ))
    (hχ6 : χ ^ 6 = 1)
    (s : ℂ) (hs : s ^ 2 = (Fintype.card F : ℂ)) (hs0 : s ≠ 0) :
    χ (4 : F) * (gaussSum χ ψ / s) * (gaussSum (χ ^ 2) ψ / s) =
      (gaussSum (χ ^ 3) ψ / s) * (gaussSum (χ ^ 2) ψ / s) ^ 3 := by
  have hraw := gauss_sextic_relation χ ψ hchar hψ hχ1 hχ2 hχ4 hχ3 hχ6
  rw [← hs] at hraw
  field_simp
  linear_combination (gaussSum (χ ^ 2) ψ) * hraw

end JacobiQuadratic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SexticNormalization
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical

namespace ActualEisensteinCubic

section

open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace

theorem breveGamma1_gamma2_relation (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0)
    (hprimary : lambda ^ 2 ∣ p - 1) :
    breveGamma1 P hgood p hP hp * breveGamma2 P hgood p hP hp =
      (canonicalSextic P hgood
        (Ideal.Quotient.mk P (4 : O)))⁻¹ *
      breveGamma3 P hgood p hP hp *
        (breveGamma2 P hgood p hP hp) ^ 3 := by
  subst P
  let χ := canonicalSextic (Ideal.span {p}) hgood
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates p hp
  let s : ℂ := ‖eisEmbedding p‖
  have hψ : ψ.IsPrimitive :=
    eisTraceModChar_breveE_primitive (Ideal.span {p}) p rfl hp
  have hχ1 : χ ≠ 1 := by
    simpa only [pow_one] using
      (canonicalSextic_pow_ne_one (Ideal.span {p}) hgood hchar
        (by decide : (1 : ℕ) ≠ 0) (by decide : (1 : ℕ) < 6))
  have hχ2 : χ ^ 2 ≠ 1 := canonicalSextic_pow_ne_one (Ideal.span {p}) hgood hchar
    (by decide : (2 : ℕ) ≠ 0) (by decide : (2 : ℕ) < 6)
  have hχ4 : χ ^ 4 ≠ 1 := canonicalSextic_pow_ne_one (Ideal.span {p}) hgood hchar
    (by decide : (4 : ℕ) ≠ 0) (by decide : (4 : ℕ) < 6)
  have hχ3 : χ ^ 3 = (quadraticChar (O ⧸ Ideal.span {p})).ringHomComp
      (Int.castRingHom ℂ) := canonicalSextic_pow_three_quadratic (Ideal.span {p}) hgood
  have hχ6 : χ ^ 6 = 1 := canonicalSextic_pow_six (Ideal.span {p}) hgood
  have hs : s ^ 2 = (Fintype.card (O ⧸ Ideal.span {p}) : ℂ) := by
    have hnormO := primary_generator_mul_conj_eq_card
      (Ideal.span {p}) hgood p rfl hprimary
    have hnormC := congrArg eisEmbedding hnormO
    rw [map_mul, eisEmbedding_conjO, map_natCast] at hnormC
    simpa only [s, ← starRingEnd_apply, Complex.mul_conj',
      Nat.card_eq_fintype_card] using hnormC
  have hs0 : s ≠ 0 := by
    dsimp [s]
    exact_mod_cast (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp))
  have hmul := JacobiQuadratic.normalized_gauss_sextic_relation
    χ ψ hchar hψ hχ1 hχ2 hχ4 hχ3 hχ6 s hs hs0
  have hfour : (4 : O ⧸ Ideal.span {p}) ≠ 0 := by
    have htwo : (2 : O ⧸ Ideal.span {p}) ≠ 0 := Ring.two_ne_zero hchar
    convert (preTransparency := .instances) pow_ne_zero 2 htwo using 1 ; norm_num
  have hχfour : χ (4 : O ⧸ Ideal.span {p}) ≠ 0 :=
    χ.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr hfour)
  change χ 4 * breveGamma1 (Ideal.span {p}) hgood p rfl hp *
    breveGamma2 (Ideal.span {p}) hgood p rfl hp =
    breveGamma3 (Ideal.span {p}) hgood p rfl hp *
      breveGamma2 (Ideal.span {p}) hgood p rfl hp ^ 3 at hmul
  change breveGamma1 (Ideal.span {p}) hgood p rfl hp *
    breveGamma2 (Ideal.span {p}) hgood p rfl hp =
    (χ 4)⁻¹ * breveGamma3 (Ideal.span {p}) hgood p rfl hp *
      breveGamma2 (Ideal.span {p}) hgood p rfl hp ^ 3
  calc
    breveGamma1 (Ideal.span {p}) hgood p rfl hp *
        breveGamma2 (Ideal.span {p}) hgood p rfl hp =
      (χ 4)⁻¹ * (χ 4 * breveGamma1 (Ideal.span {p}) hgood p rfl hp *
        breveGamma2 (Ideal.span {p}) hgood p rfl hp) := by field_simp
    _ = (χ 4)⁻¹ * (breveGamma3 (Ideal.span {p}) hgood p rfl hp *
        breveGamma2 (Ideal.span {p}) hgood p rfl hp ^ 3) := by rw [hmul]
    _ = _ := by ring

end

section

open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace

theorem breveGamma1_gamma2_eq_neg_alpha_G (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0)
    (hprimary : lambda ^ 2 ∣ p - 1) :
    breveGamma1 P hgood p hP hp * breveGamma2 P hgood p hP hp =
      (-(eisEmbedding p) / (‖eisEmbedding p‖ : ℂ)) *
        breveLocalG P hgood p hP hp := by
  rw [breveGamma1_gamma2_relation P hgood hchar p hP hp hprimary,
    breveGamma2_cube P hgood p hP hp hprimary]
  unfold breveLocalG
  ring

end

open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE

end ActualEisensteinCubic

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace

private theorem canonicalSextic_order_six (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    orderOf (canonicalSextic P hgood) = 6 := by
  let Φ : MulChar (O ⧸ P) O →* MulChar (O ⧸ P) ℂ :=
    MulChar.ringHomCompHom eisEmbedding
  have hΦ : Function.Injective Φ := by
    intro x y h
    apply MulChar.ext
    intro t
    apply eisEmbedding_injective
    exact congrArg (fun f : MulChar (O ⧸ P) ℂ => f t) h
  change orderOf (Φ (sexticChar P hgood)) = 6
  rw [orderOf_injective Φ hΦ, sexticChar_order P hgood hchar]

theorem breveGamma1_gammaMinus1 (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0)
    (hprimary : lambda ^ 2 ∣ p - 1) :
    breveGamma1 P hgood p hP hp * breveGammaMinus1 P hgood p hP hp =
      canonicalSextic P hgood (Ideal.Quotient.mk P (-1 : O)) := by
  subst P
  let χ := canonicalSextic (Ideal.span {p}) hgood
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates p hp
  let s : ℂ := ‖eisEmbedding p‖
  have hψ : ψ.IsPrimitive :=
    eisTraceModChar_breveE_primitive (Ideal.span {p}) p rfl hp
  have hχ1 : χ ≠ 1 := by
    simpa only [pow_one] using
      (canonicalSextic_pow_ne_one (Ideal.span {p}) hgood hchar
        (by decide : (1 : ℕ) ≠ 0) (by decide : (1 : ℕ) < 6))
  have hχ6 : χ ^ 6 = 1 := canonicalSextic_pow_six (Ideal.span {p}) hgood
  have horder : orderOf χ = 6 :=
    canonicalSextic_order_six (Ideal.span {p}) hgood hchar
  have hχ5 : χ ^ 5 = χ⁻¹ := by
    apply (inv_eq_of_mul_eq_one_right ?_).symm
    calc
      χ * χ ^ 5 = χ ^ 6 := by group
      _ = 1 := hχ6
  have hprod := gaussSum_mul_gaussSum_pow_orderOf_sub_one hχ1 hψ
  rw [horder, show 6 - 1 = 5 by decide, hχ5] at hprod
  have hs : s ^ 2 = (Fintype.card (O ⧸ Ideal.span {p}) : ℂ) := by
    have hnormO := primary_generator_mul_conj_eq_card
      (Ideal.span {p}) hgood p rfl hprimary
    have hnormC := congrArg eisEmbedding hnormO
    rw [map_mul, eisEmbedding_conjO, map_natCast] at hnormC
    simpa only [s, ← starRingEnd_apply, Complex.mul_conj',
      Nat.card_eq_fintype_card] using hnormC
  have hs0 : s ≠ 0 := by
    dsimp [s]
    exact_mod_cast (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp))
  change (gaussSum χ ψ / s) * (gaussSum χ⁻¹ ψ / s) = χ (-1)
  field_simp
  rw [hs]
  simpa only [mul_comm] using hprod

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.LocalProductAssembly
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical

namespace ActualEisensteinCubic

open ConcreteTraceCRT
open scoped ComplexConjugate

theorem canonicalSextic_inverse_eq_conj_on_units (P : Ideal O)
    [P.IsMaximal] (hgood : lambda ∉ P) (u : (O ⧸ P)ˣ) :
    (canonicalSextic P hgood (u : O ⧸ P))⁻¹ =
      star (canonicalSextic P hgood (u : O ⧸ P)) := by
  let χ := canonicalSextic P hgood
  have hχ6 : χ ^ 6 = 1 := canonicalSextic_pow_six P hgood
  have hval : χ (u : O ⧸ P) ^ 6 = 1 := by
    rw [← χ.pow_apply_coe 6 u, hχ6, MulChar.one_apply_coe]
  exact Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hval (by decide))

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.RamifiedTracePhase
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical

namespace ActualEisensteinCubic

theorem finiteSquarefreeRow_sixth_power
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (a : O) :
    finiteSquarefreeRow P hgood S (a ^ 6) =
      if ∃ i ∈ S, a ∈ P i then 0 else 1 := by
  classical
  simp only [finiteSquarefreeRow]
  by_cases hex : ∃ i ∈ S, a ∈ P i
  · obtain ⟨i, hi, hai⟩ := hex
    rw [if_pos ⟨i, hi, hai⟩]
    apply Finset.prod_eq_zero hi
    rw [canonicalSextic_sixth_power_mask]
    simp [hai]
  · rw [if_neg hex]
    apply Finset.prod_eq_one
    intro i hi
    rw [canonicalSextic_sixth_power_mask]
    simp [show a ∉ P i by intro hai; exact hex ⟨i, hi, hai⟩]

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Mellin.LocalNonvanishing
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar

open Filter Asymptotics

open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter

private theorem pairing_algebra
    (g1 g2 gm G alpha eps t : ℂ)
    (halpha : alpha * star alpha = 1)
    (hg1 : g1 * star g1 = 1)
    (hprod : g1 * g2 = -alpha * G)
    (hpair : g1 * gm = eps) :
    (-star g1) * G * t = (star alpha * g2) * t ∧
    (-gm) * G * t = eps * (star alpha * g2) * t ∧
    (-g1) * star G * t⁻¹ = (alpha * star g2) * t⁻¹ ∧
    (-star gm) * star G * t⁻¹ = star eps * (alpha * star g2) * t⁻¹ := by
  have h2 : g2 = -(star g1) * alpha * G := by
    calc
      g2 = (g1 * star g1) * g2 := by rw [hg1]; ring
      _ = star g1 * (g1 * g2) := by ring
      _ = star g1 * (-alpha * G) := by rw [hprod]
      _ = _ := by ring
  have hA : star alpha * g2 = (-star g1) * G := by
    rw [h2]
    calc
      star alpha * (-(star g1) * alpha * G) =
          (alpha * star alpha) * ((-star g1) * G) := by ring
      _ = (-star g1) * G := by rw [halpha]; ring
  have hm : gm = eps * star g1 := by
    calc
      gm = (g1 * star g1) * gm := by rw [hg1]; ring
      _ = star g1 * (g1 * gm) := by ring
      _ = eps * star g1 := by rw [hpair]; ring
  have hB : (-gm) * G = eps * (star alpha * g2) := by
    rw [hm, hA]
    ring
  have hC : (-g1) * star G = alpha * star g2 := by
    have h := congrArg (fun z : ℂ => star z) hA
    simp only [star_mul, star_neg, star_star] at h
    calc
      (-g1) * star G = star G * (-g1) := by ring
      _ = star g2 * alpha := h.symm
      _ = alpha * star g2 := by ring
  have hD : (-star gm) * star G = star eps * (alpha * star g2) := by
    have h := congrArg (fun z : ℂ => star z) hB
    simpa only [star_mul, star_neg, star_star, mul_comm, mul_left_comm, mul_assoc] using h
  exact ⟨by rw [hA], by rw [hB], by rw [hC], by rw [hD]⟩

namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace
open scoped ComplexConjugate

private theorem breveGamma1_mul_star_one (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0)
    (hprimary : lambda ^ 2 ∣ p - 1) :
    breveGamma1 P hgood p hP hp * star (breveGamma1 P hgood p hP hp) = 1 := by
  subst P
  let χ := canonicalSextic (Ideal.span {p}) hgood
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates p hp
  let s : ℝ := ‖eisEmbedding p‖
  have hψ : ψ.IsPrimitive :=
    eisTraceModChar_breveE_primitive (Ideal.span {p}) p rfl hp
  have hχ1 : χ ≠ 1 := by
    simpa only [pow_one] using
      (canonicalSextic_pow_ne_one (Ideal.span {p}) hgood hchar
        (by decide : (1 : ℕ) ≠ 0) (by decide : (1 : ℕ) < 6))
  have hnormO := primary_generator_mul_conj_eq_card
    (Ideal.span {p}) hgood p rfl hprimary
  have hnormC := congrArg eisEmbedding hnormO
  rw [map_mul, eisEmbedding_conjO, map_natCast] at hnormC
  have hs : (s : ℂ) ^ 2 = (Fintype.card (O ⧸ Ideal.span {p}) : ℂ) := by
    simpa only [s, ← starRingEnd_apply, Complex.mul_conj',
      Nat.card_eq_fintype_card] using hnormC
  have hsreal : s ^ 2 = (Fintype.card (O ⧸ Ideal.span {p}) : ℝ) := by
    exact Complex.ofReal_injective (by exact_mod_cast hs)
  have hcard : 0 < (Fintype.card (O ⧸ Ideal.span {p}) : ℝ) := by positivity
  have hsroot : s = Real.sqrt (Fintype.card (O ⧸ Ideal.span {p})) := by
    nlinarith [Real.sq_sqrt hcard.le, Real.sqrt_nonneg
      (Fintype.card (O ⧸ Ideal.span {p})), norm_nonneg (eisEmbedding p)]
  have hs0 : s ≠ 0 := by
    dsimp [s]
    exact (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp))
  have hnorm : ‖breveGamma1 (Ideal.span {p}) hgood p rfl hp‖ = 1 := by
    change ‖gaussSum χ ψ / (s : ℂ)‖ = 1
    rw [norm_div, ShortDraftGauss.norm_gaussSum_eq_sqrt_card χ ψ hχ1 hψ]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (eisEmbedding p))]
    rw [← hsroot]
    exact div_self hs0
  rw [← starRingEnd_apply, Complex.mul_conj', hnorm]
  norm_num

theorem first_poisson_prime_sign_pairing
    (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) :
    let alpha : ℂ := eisEmbedding p / (‖eisEmbedding p‖ : ℂ)
    let g1 := breveGamma1 P hgood p hP hp
    let g2 := breveGamma2 P hgood p hP hp
    let gm := breveGammaMinus1 P hgood p hP hp
    let G := breveLocalG P hgood p hP hp
    let t := canonicalSextic P hgood (Ideal.Quotient.mk P h)
    let eps := canonicalSextic P hgood (Ideal.Quotient.mk P (-1 : O))
    (-star g1) * G * t = (star alpha * g2) * t ∧
    (-gm) * G * t = eps * (star alpha * g2) * t ∧
    (-g1) * star G * t⁻¹ = (alpha * star g2) * t⁻¹ ∧
    (-star gm) * star G * t⁻¹ = star eps * (alpha * star g2) * t⁻¹ := by
  have hz : eisEmbedding p ≠ 0 := eisEmbedding_ne_zero hp
  have hs : (‖eisEmbedding p‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hz)
  have hanorm : ‖eisEmbedding p / (‖eisEmbedding p‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg (eisEmbedding p))]
    exact div_self (norm_ne_zero_iff.mpr hz)
  have ha : (eisEmbedding p / (‖eisEmbedding p‖ : ℂ)) *
      star (eisEmbedding p / (‖eisEmbedding p‖ : ℂ)) = 1 := by
    rw [← starRingEnd_apply, Complex.mul_conj', hanorm]
    norm_num
  have hg1 := breveGamma1_mul_star_one P hgood hchar p hP hp hprimary
  have hprod := breveGamma1_gamma2_eq_neg_alpha_G
    P hgood hchar p hP hp hprimary
  have hprod' :
      breveGamma1 P hgood p hP hp * breveGamma2 P hgood p hP hp =
        -(eisEmbedding p / (‖eisEmbedding p‖ : ℂ)) *
          breveLocalG P hgood p hP hp := by
    simpa only [neg_div] using hprod
  have hpair := breveGamma1_gammaMinus1
    P hgood hchar p hP hp hprimary
  dsimp only
  exact pairing_algebra
    (breveGamma1 P hgood p hP hp)
    (breveGamma2 P hgood p hP hp)
    (breveGammaMinus1 P hgood p hP hp)
    (breveLocalG P hgood p hP hp)
    (eisEmbedding p / (‖eisEmbedding p‖ : ℂ))
    (canonicalSextic P hgood (Ideal.Quotient.mk P (-1 : O)))
    (canonicalSextic P hgood (Ideal.Quotient.mk P h))
    ha hg1 hprod' hpair

end ActualEisensteinCubic

open MulChar AddChar

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SecondPoissonScale
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap

namespace ActualEisensteinCubic

section

open scoped ComplexConjugate

theorem canonicalSextic_conj_as_row_label
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P) (e : O) :
    star (canonicalSextic P hgood (Ideal.Quotient.mk P e)) =
      canonicalSextic P hgood (Ideal.Quotient.mk P e) *
        (canonicalSextic P hgood (Ideal.Quotient.mk P e)) ^ 4 := by
  let χ := canonicalSextic P hgood
  let x : O ⧸ P := Ideal.Quotient.mk P e
  have hconj : star (χ x) = (χ x)⁻¹ := by
    by_cases hx : IsUnit x
    · let u : (O ⧸ P)ˣ := hx.unit
      have hu : (u : O ⧸ P) = x := hx.unit_spec
      rw [← hu]
      exact (canonicalSextic_inverse_eq_conj_on_units P hgood u).symm
    · have hzero : χ x = 0 := MulChar.map_nonunit χ hx
      simp [hzero]
  rw [hconj]
  by_cases hx : IsUnit x
  · have h6 : (χ x) ^ 6 = 1 := by
      rw [← MulChar.pow_apply' χ (by decide : 6 ≠ 0),
        canonicalSextic_pow_six P hgood]
      exact MulChar.one_apply hx
    apply inv_eq_of_mul_eq_one_right
    calc
      χ x * (χ x * (χ x) ^ 4) = (χ x) ^ 6 := by ring
      _ = 1 := h6
  · have hzero : χ x = 0 := MulChar.map_nonunit χ hx
    change (χ x)⁻¹ = χ x * (χ x) ^ 4
    simp [hzero]

theorem finiteSquarefreeRow_conj_as_row_label
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (e : O) :
    star (finiteSquarefreeRow P hgood S e) =
      finiteSquarefreeRow P hgood S e *
        (finiteSquarefreeRow P hgood S e) ^ 4 := by
  classical
  simp only [finiteSquarefreeRow, star_prod]
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact canonicalSextic_conj_as_row_label (P i) (hgood i) e

theorem finiteSquarefreeRow_second_child
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι)
    (d e k J C v : O) :
    star (finiteSquarefreeRow P hgood S e) *
      finiteSquarefreeRow P hgood S d *
      finiteSquarefreeRow P hgood S k *
      (finiteSquarefreeRow P hgood S (J * C)) ^ 4 *
      (finiteSquarefreeRow P hgood S v) ^ 4 =
    finiteSquarefreeRow P hgood S (d * e * k) *
      (finiteSquarefreeRow P hgood S (J * C * e * v)) ^ 4 := by
  rw [finiteSquarefreeRow_conj_as_row_label P hgood S e]
  simp only [finiteSquarefreeRow_mul]
  ring

end

theorem finiteSquarefreeRow_pair_kernel
    {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger - 1 ∉ P i)
    (S T : Finset ι) (u : O) :
    star (finiteSquarefreeRow P hgood S u) * finiteSquarefreeRow P hgood T u =
      rowCoprimeMask P (S ∩ T) u *
        star (finiteSquarefreeRow P hgood (S \ T) u) *
        finiteSquarefreeRow P hgood (T \ S) u := by
  have hsplit (A B : Finset ι) :
      finiteSquarefreeRow P hgood A u =
        finiteSquarefreeRow P hgood (A ∩ B) u *
        finiteSquarefreeRow P hgood (A \ B) u := by
    exact (Finset.prod_inter_mul_prod_sdiff A B _).symm
  rw [hsplit S T, hsplit T S, Finset.inter_comm T S, star_mul]
  calc
    _ = (star (finiteSquarefreeRow P hgood (S ∩ T) u) *
          finiteSquarefreeRow P hgood (S ∩ T) u) *
        star (finiteSquarefreeRow P hgood (S \ T) u) *
        finiteSquarefreeRow P hgood (T \ S) u := by ring
    _ = _ := by rw [finiteSquarefreeRow_self_pair]

private theorem mask_powerset {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (p : ι → Prop) [DecidablePred p] :
    (if ∃ i ∈ S, p i then (0 : ℂ) else 1) =
      ∑ E ∈ S.powerset, (-1 : ℂ) ^ E.card *
        if ∀ i ∈ E, p i then 1 else 0 := by
  have hprod : (if ∃ i ∈ S, p i then (0 : ℂ) else 1) =
      ∏ i ∈ S, (1 - if p i then (1 : ℂ) else 0) := by
    by_cases h : ∃ i ∈ S, p i
    · rw [if_pos h]
      obtain ⟨i, hi, hp⟩ := h
      symm
      apply Finset.prod_eq_zero hi
      simp [hp]
    · rw [if_neg h]
      symm
      apply Finset.prod_eq_one
      intro i hi
      simp [show ¬p i from fun hp => h ⟨i, hi, hp⟩]
  rw [hprod, Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro E hE
  simp only [Finset.prod_const_one, mul_one]
  congr 1
  by_cases h : ∀ i ∈ E, p i
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    simp [h i hi]
  · rw [if_neg h]
    push Not at h
    obtain ⟨i, hi, hp⟩ := h
    apply Finset.prod_eq_zero hi
    simp [hp]

theorem rowCoprimeMask_subsets
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S : Finset ι) (u : O) :
    rowCoprimeMask P S u =
      ∑ E ∈ S.powerset, (-1 : ℂ) ^ E.card *
        if ∀ i ∈ E, u ∈ P i then 1 else 0 := by
  classical
  exact mask_powerset S (fun i => u ∈ P i)

theorem prime_product_moebius
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (hprime : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (S : Finset ι) :
    (UniqueFactorizationMonoid.moebius (∏ i ∈ S, P i) : ℂ) =
      (-1 : ℂ) ^ S.card := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, UniqueFactorizationMonoid.moebius_one, Int.cast_one, Finset.card_empty, pow_zero]
  | @insert i S hi ih =>
    have hcop : IsCoprime (P i) (∏ j ∈ S, P j) := by
      apply IsCoprime.prod_right
      intro j hj
      apply Ideal.isCoprime_of_isMaximal
      exact hinj.ne (by intro h; subst j; exact hi hj)
    rw [Finset.prod_insert hi, hcop.isRelPrime.moebius_mul,
      (hprime i).irreducible.moebius_eq, Int.cast_mul, Int.cast_neg,
      Int.cast_one, ih, Finset.card_insert_of_notMem hi, pow_succ]
    ring

theorem mem_prime_product_iff
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (u : O) :
    u ∈ (∏ i ∈ S, P i) ↔ ∀ i ∈ S, u ∈ P i := by
  rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime]
  · simp
  · intro i hi j hj hij
    exact Ideal.isCoprime_of_isMaximal (hinj.ne hij)

end ActualEisensteinCubic

namespace EisensteinSchwartzPoisson
open MeasureTheory Filter LineDeriv
open scoped FourierTransform SchwartzMap Real RealInnerProductSpace

theorem fourier_prod_eq_iterated (f : LogPlane → ℂ) (hf : Integrable f) (ξ η : ℝ) :
    𝓕 f (WithLp.toLp 2 (ξ, η)) =
      𝓕 (fun x : ℝ => 𝓕 (fun y : ℝ => f (WithLp.toLp 2 (x, y))) η) ξ := by
  let w : LogPlane := WithLp.toLp 2 (ξ, η)
  let G : LogPlane → ℂ := fun z => Real.fourierChar (-⟪z, w⟫) • f z
  have hG : Integrable G := (Real.fourierIntegral_convergent_iff w).mpr hf
  have hGp : Integrable (fun z : ℝ × ℝ => G (WithLp.toLp 2 z)) :=
    (WithLp.volume_preserving_toLp ℝ ℝ).integrable_comp_of_integrable hG
  calc
    𝓕 f (WithLp.toLp 2 (ξ, η)) = ∫ z : LogPlane, G z := rfl
    _ = ∫ z : ℝ × ℝ, G (WithLp.toLp 2 z) :=
      ((WithLp.volume_preserving_toLp ℝ ℝ).integral_comp
        (MeasurableEquiv.toLp 2 (ℝ × ℝ)).measurableEmbedding G).symm
    _ = ∫ x : ℝ, ∫ y : ℝ, G (WithLp.toLp 2 (x, y)) := integral_prod _ hGp
    _ = 𝓕 (fun x : ℝ => 𝓕 (fun y : ℝ => f (WithLp.toLp 2 (x, y))) η) ξ := by
      simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by
          simp only [G, w, WithLp.prod_inner_apply,
            neg_add, Real.fourierChar.map_add_eq_mul, Circle.smul_def, smul_eq_mul,
            Circle.coe_mul, mul_assoc]

theorem verticalMajorant_integrable (f : SchwartzMap ℂ ℂ) : Integrable (verticalMajorant f) :=
  integrable_inv_one_add_sq.const_mul _

theorem norm_le_verticalMajorant (f : SchwartzMap ℂ ℂ) (x y : ℝ) :
    ‖f (complexPoint x y)‖ ≤ verticalMajorant f y := by
  have h0 := SchwartzMap.norm_le_seminorm ℝ f (complexPoint x y)
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ f 2 (complexPoint x y)
  have hy : y ^ 2 ≤ ‖complexPoint x y‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, complexPoint]
    nlinarith [sq_nonneg x]
  have hym := mul_le_mul_of_nonneg_right hy (norm_nonneg (f (complexPoint x y)))
  have hden : 0 < 1 + y ^ 2 := by positivity
  rw [verticalMajorant, ← div_eq_mul_inv]
  apply (le_div_iff₀ hden).mpr
  nlinarith

theorem partialFourier_continuous (f : SchwartzMap ℂ ℂ) (η : ℝ) :
    Continuous (partialFourier f η) := by
  change Continuous (fun x : ℝ => ∫ y : ℝ,
    Real.fourierChar (-inner ℝ y η) • f (complexPoint x y))
  apply continuous_of_dominated
    (bound := verticalMajorant f)
  · intro x
    have hline : Continuous (fun y : ℝ => complexPoint x y) :=
      Complex.equivRealProdCLM.symm.continuous.comp (continuous_const.prodMk continuous_id)
    exact ((by fun_prop : Continuous (fun y : ℝ => Real.fourierChar (-inner ℝ y η))).smul
      (f.continuous.comp hline)).aestronglyMeasurable
  · intro x
    exact Eventually.of_forall fun y => by
      simpa only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul] using
        norm_le_verticalMajorant f x y
  · exact verticalMajorant_integrable f
  · exact Eventually.of_forall fun y => by
      have hf : Continuous (fun x : ℝ => f (complexPoint x y)) :=
        f.continuous.comp (horizontal_isometry y).continuous
      exact continuous_const.smul hf

theorem partialFourier_integrable (f : SchwartzMap ℂ ℂ) (η : ℝ) :
    Integrable (partialFourier f η) := by
  let G : ℂ → ℂ := fun z => Real.fourierChar (-inner ℝ z.im η) • f z
  have hG : Integrable G := f.integrable.norm.mono'
    (by fun_prop : Continuous G).aestronglyMeasurable
    (Eventually.of_forall fun z => by
      simp only [G, Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
      exact le_rfl)
  have hGp : Integrable (fun z : ℝ × ℝ => G (Complex.measurableEquivRealProd.symm z)) :=
    Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_of_integrable hG
  change Integrable (fun x : ℝ => ∫ y : ℝ,
    Real.fourierChar (-inner ℝ y η) • f (complexPoint x y))
  simpa only [G, Complex.measurableEquivRealProd_symm_apply, complexPoint]
    using hGp.integral_prod_left

theorem fourier_partialFourier (f : SchwartzMap ℂ ℂ) (ξ η : ℝ) :
    𝓕 (partialFourier f η) ξ = 𝓕 (f : ℂ → ℂ) (complexPoint ξ η) := by
  let fp : SchwartzMap LogPlane ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ planeComplexIso.toContinuousLinearEquiv f
  have hprod := fourier_prod_eq_iterated (fp : LogPlane → ℂ) fp.integrable ξ η
  have hcoe : (fp : LogPlane → ℂ) = (f : ℂ → ℂ) ∘ planeComplexIso := rfl
  rw [hcoe, Real.fourier_comp_linearIsometry] at hprod
  change 𝓕 (fun x : ℝ => 𝓕 (fun y : ℝ => f (complexPoint x y)) η) ξ = _
  simpa only [Function.comp_apply, planeComplexIso_apply] using hprod.symm

theorem partialFourierSchwartz_apply (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    partialFourierSchwartz f η x = partialFourier f η x := by
  have heq : 𝓕 (partialFourier f η) =
      (horizontalSlice (𝓕 f) η : ℝ → ℂ) := by
    funext ξ
    rw [fourier_partialFourier, horizontalSlice_apply]
    exact (congrFun (SchwartzMap.fourier_coe f) (complexPoint ξ η)).symm
  have hi : Integrable (𝓕 (partialFourier f η)) := by
    rw [heq]
    exact (horizontalSlice (𝓕 f) η).integrable
  change (𝓕⁻ (horizontalSlice (𝓕 f) η)) x = _
  rw [congrFun (SchwartzMap.fourierInv_coe (horizontalSlice (𝓕 f) η)) x, ← heq]
  exact (partialFourier_integrable f η).fourierInv_fourier_eq hi
    (partialFourier_continuous f η).continuousAt

theorem partialFourierSchwartz_coe (f : SchwartzMap ℂ ℂ) (η : ℝ) :
    (partialFourierSchwartz f η : ℝ → ℂ) = partialFourier f η :=
  funext (partialFourierSchwartz_apply f η)

theorem horizontal_hasFDerivAt (η x : ℝ) :
    HasFDerivAt (fun y : ℝ => complexPoint y η) Complex.ofRealCLM x := by
  have heq : (fun y : ℝ => complexPoint y η) =
      (fun y : ℝ => Complex.ofRealCLM y + Complex.I * (η : ℂ)) := by
    funext y
    exact complexPoint_eq y η
  rw [heq]
  exact Complex.ofRealCLM.hasFDerivAt.add_const _

theorem horizontalSlice_lineDerivOp (F : SchwartzMap ℂ ℂ) (η : ℝ) :
    ∂_{(1 : ℝ)} (horizontalSlice F η) = horizontalSlice (∂_{(1 : ℂ)} F) η := by
  apply SchwartzMap.ext
  intro x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, horizontalSlice_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hcomp := (F.hasFDerivAt (complexPoint x η)).comp x (horizontal_hasFDerivAt η x)
  change fderiv ℝ (fun y : ℝ => F (complexPoint y η)) x (1 : ℝ) = _
  change fderiv ℝ ((F : ℂ → ℂ) ∘ (fun y => complexPoint y η)) x (1 : ℝ) = _
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.ofReal_one]

theorem horizontalSlice_lineDerivOp_twice (F : SchwartzMap ℂ ℂ) (η : ℝ) :
    ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (horizontalSlice F η)) =
      horizontalSlice (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F)) η := by
  rw [horizontalSlice_lineDerivOp, horizontalSlice_lineDerivOp]

theorem summable_norm_of_cauchy_product (F : ℤ × ℤ → ℂ) (C : ℝ)
    (hF : ∀ p, ‖F p‖ ≤ C *
      ((1 + (p.1 : ℝ) ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2)⁻¹)) :
    Summable (fun p => ‖F p‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hF
    (summable_int_cauchy_product.mul_left C)

theorem plane_schwartz_product_decay (F : SchwartzMap ℂ ℂ) (ξ η : ℝ) :
    ((1 + ξ ^ 2) * (1 + η ^ 2)) * ‖F (complexPoint ξ η)‖ ≤
      planeDecayConstant F := by
  let z := complexPoint ξ η
  have hz : ‖z‖ ^ 2 = ξ ^ 2 + η ^ 2 := by
    rw [Complex.sq_norm]
    simp [z, Complex.normSq_apply, complexPoint, sq]
  have h0 := SchwartzMap.norm_le_seminorm ℝ F z
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ F 2 z
  have h4 := SchwartzMap.norm_pow_mul_le_seminorm ℝ F 4 z
  have hz4 : ‖z‖ ^ 4 = (ξ ^ 2 + η ^ 2) ^ 2 := by
    calc
      ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 := by ring
      _ = (ξ ^ 2 + η ^ 2) ^ 2 := congrArg (fun t : ℝ => t ^ 2) hz
  have hxy : ξ ^ 2 * η ^ 2 ≤ ‖z‖ ^ 4 := by
    rw [hz4]
    nlinarith [sq_nonneg (ξ ^ 2), sq_nonneg (η ^ 2),
      mul_nonneg (sq_nonneg ξ) (sq_nonneg η)]
  have hm := mul_le_mul_of_nonneg_right hxy (norm_nonneg (F z))
  rw [hz] at h2
  change ((1 + ξ ^ 2) * (1 + η ^ 2)) * ‖F z‖ ≤ _
  unfold planeDecayConstant
  nlinarith

theorem norm_horizontalSlice_le (F : SchwartzMap ℂ ℂ) (η ξ : ℝ) :
    ‖horizontalSlice F η ξ‖ ≤
      (planeDecayConstant F / (1 + η ^ 2)) * (1 + ξ ^ 2)⁻¹ := by
  rw [horizontalSlice_apply, ← div_eq_mul_inv, div_div]
  apply (le_div_iff₀ (by positivity : 0 < (1 + η ^ 2) * (1 + ξ ^ 2))).mpr
  nlinarith [plane_schwartz_product_decay F ξ η]

theorem norm_inverse_horizontalSlice_le (F : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ‖(𝓕⁻ (horizontalSlice F η)) x‖ ≤
      (planeDecayConstant F / (1 + η ^ 2)) * Real.pi := by
  rw [congrFun (SchwartzMap.fourierInv_coe (horizontalSlice F η)) x,
    Real.fourierInv_eq]
  have hb : Integrable (fun ξ : ℝ =>
      (planeDecayConstant F / (1 + η ^ 2)) * (1 + ξ ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have h := norm_integral_le_of_norm_le
    (f := fun ξ : ℝ => Real.fourierChar (inner ℝ ξ x) • horizontalSlice F η ξ) hb (Eventually.of_forall fun ξ => by
    simpa only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul] using
      norm_horizontalSlice_le F η ξ)
  simpa only [integral_const_mul, integral_univ_inv_one_add_sq] using h

theorem norm_inverse_lineDeriv (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖(𝓕⁻ (∂_{(1 : ℝ)} g)) x‖ =
      (2 * Real.pi) * |x| * ‖(𝓕⁻ g) x‖ := by
  have ht : (fun u : ℝ => inner ℝ u (1 : ℝ)).HasTemperateGrowth := by fun_prop
  have hc : ‖(-(2 * Real.pi * Complex.I) : ℂ)‖ = 2 * Real.pi := by
    simp [ Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [SchwartzMap.fourierInv_lineDerivOp_eq]
  simp only [_root_.smul_apply, SchwartzMap.smulLeftCLM_apply_apply ht,
    norm_smul, hc]
  simp [RCLike.inner_apply, Real.norm_eq_abs, mul_assoc]

theorem sq_mul_norm_inverse_le_second (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    x ^ 2 * ‖(𝓕⁻ g) x‖ ≤ ‖(𝓕⁻ (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} g))) x‖ := by
  rw [norm_inverse_lineDeriv, norm_inverse_lineDeriv]
  have hp : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  calc
    x ^ 2 * ‖(𝓕⁻ g) x‖ ≤ ((2 * Real.pi) ^ 2 * x ^ 2) * ‖(𝓕⁻ g) x‖ :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (sq_nonneg x) hp) (norm_nonneg _)
    _ = ((2 * Real.pi) ^ 2 * |x| ^ 2) * ‖(𝓕⁻ g) x‖ := by rw [sq_abs]
    _ = _ := by ring

theorem inverse_horizontalSlice_product_decay (F : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ((1 + x ^ 2) * (1 + η ^ 2)) * ‖(𝓕⁻ (horizontalSlice F η)) x‖ ≤
      Real.pi * (planeDecayConstant F +
        planeDecayConstant (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F))) := by
  have h0 := norm_inverse_horizontalSlice_le F η x
  have h2a := sq_mul_norm_inverse_le_second (horizontalSlice F η) x
  rw [horizontalSlice_lineDerivOp_twice] at h2a
  have h2 := h2a.trans
    (norm_inverse_horizontalSlice_le (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F)) η x)
  have hden : 0 < 1 + η ^ 2 := by positivity
  have h0' : ‖(𝓕⁻ (horizontalSlice F η)) x‖ * (1 + η ^ 2) ≤
      planeDecayConstant F * Real.pi := by
    apply (le_div_iff₀ hden).mp
    simpa only [div_mul_eq_mul_div] using h0
  have h2' : (x ^ 2 * ‖(𝓕⁻ (horizontalSlice F η)) x‖) * (1 + η ^ 2) ≤
      planeDecayConstant (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F)) * Real.pi := by
    apply (le_div_iff₀ hden).mp
    simpa only [div_mul_eq_mul_div] using h2
  nlinarith

theorem partialFourier_product_decay (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ((1 + x ^ 2) * (1 + η ^ 2)) * ‖partialFourier f η x‖ ≤
      partialFourierDecayConstant f := by
  rw [← partialFourierSchwartz_apply]
  exact inverse_horizontalSlice_product_decay (𝓕 f) η x

theorem norm_partialFourier_le (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ‖partialFourier f η x‖ ≤
      partialFourierDecayConstant f * ((1 + x ^ 2)⁻¹ * (1 + η ^ 2)⁻¹) := by
  rw [← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < (1 + x ^ 2) * (1 + η ^ 2))).mpr
  nlinarith [partialFourier_product_decay f η x]

theorem partialFourier_gaussian_summable_norm (f : SchwartzMap ℂ ℂ) :
    Summable (fun p : ℤ × ℤ =>
      ‖partialFourier f (p.2 : ℝ) (p.1 : ℝ)‖) := by
  apply summable_norm_of_cauchy_product
    (fun p : ℤ × ℤ => partialFourier f (p.2 : ℝ) (p.1 : ℝ))
    (partialFourierDecayConstant f)
  intro p
  exact norm_partialFourier_le f (p.2 : ℝ) (p.1 : ℝ)

theorem partialFourier_gaussian_summable (f : SchwartzMap ℂ ℂ) :
    Summable (fun p : ℤ × ℤ => partialFourier f (p.2 : ℝ) (p.1 : ℝ)) :=
  (partialFourier_gaussian_summable_norm f).of_norm

theorem plane_lattice_summable_norm (f : 𝓢(ℂ, ℂ)) :
    Summable (fun p : ℤ × ℤ => ‖f (complexPoint (p.1 : ℝ) (p.2 : ℝ))‖) := by
  apply summable_norm_of_cauchy_product _ (planeDecayConstant f)
  intro p
  rw [← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity :
    0 < (1 + (p.1 : ℝ) ^ 2) * (1 + (p.2 : ℝ) ^ 2))).mpr
  nlinarith [plane_schwartz_product_decay f (p.1 : ℝ) (p.2 : ℝ)]

theorem plane_lattice_summable (f : 𝓢(ℂ, ℂ)) :
    Summable (fun p : ℤ × ℤ => f (complexPoint (p.1 : ℝ) (p.2 : ℝ))) :=
  (plane_lattice_summable_norm f).of_norm

theorem schwartz_poisson_zero (g : 𝓢(ℝ, ℂ)) :
    (∑' n : ℤ, g (n : ℝ)) = ∑' n : ℤ, 𝓕 (g : ℝ → ℂ) (n : ℝ) := by
  simpa [fourier_eval_zero, SchwartzMap.fourier_coe] using g.tsum_eq_tsum_fourier 0

theorem vertical_poisson (f : 𝓢(ℂ, ℂ)) (x : ℝ) :
    (∑' n : ℤ, f (complexPoint x (n : ℝ))) =
      ∑' n : ℤ, partialFourier f (n : ℝ) x := by
  exact schwartz_poisson_zero (verticalSlice f x)

private theorem horizontal_poisson (f : 𝓢(ℂ, ℂ)) (n : ℤ) :
    (∑' m : ℤ, partialFourier f (n : ℝ) (m : ℝ)) =
      ∑' k : ℤ, (𝓕 f) (complexPoint (k : ℝ) (n : ℝ)) := by
  have h := schwartz_poisson_zero (partialFourierSchwartz f n)
  simpa only [partialFourierSchwartz_apply, partialFourierSchwartz_coe,
    fourier_partialFourier, SchwartzMap.fourier_coe] using h

private theorem iterated_poisson_pair_sum
    (f g h : ℤ → ℤ → ℂ)
    (hf : Summable (Function.uncurry f))
    (hg : Summable (Function.uncurry g))
    (hh : Summable (Function.uncurry h))
    (hvertical : ∀ m, (∑' n, f m n) = ∑' n, h m n)
    (hhorizontal : ∀ n, (∑' m, h m n) = ∑' m, g m n) :
    (∑' p : ℤ × ℤ, f p.1 p.2) = ∑' p : ℤ × ℤ, g p.1 p.2 := by
  calc
    (∑' p : ℤ × ℤ, f p.1 p.2) = ∑' m, ∑' n, f m n := hf.tsum_prod
    _ = ∑' m, ∑' n, h m n := tsum_congr hvertical
    _ = ∑' n, ∑' m, h m n := hh.tsum_comm.symm
    _ = ∑' n, ∑' m, g m n := tsum_congr hhorizontal
    _ = ∑' m, ∑' n, g m n := hg.tsum_comm
    _ = ∑' p : ℤ × ℤ, g p.1 p.2 := hg.tsum_prod.symm

theorem integer_pair_poisson (f : 𝓢(ℂ, ℂ)) :
    (∑' p : ℤ × ℤ, f (complexPoint (p.1 : ℝ) (p.2 : ℝ))) =
      ∑' p : ℤ × ℤ, (𝓕 f) (complexPoint (p.1 : ℝ) (p.2 : ℝ)) := by
  exact iterated_poisson_pair_sum
    (fun m n => f (complexPoint (m : ℝ) (n : ℝ)))
    (fun m n : ℤ => (𝓕 f : 𝓢(ℂ, ℂ)) (complexPoint (m : ℝ) (n : ℝ)))
    (fun m n => partialFourier f (n : ℝ) (m : ℝ))
    (plane_lattice_summable f) (plane_lattice_summable (𝓕 f))
    (partialFourier_gaussian_summable f)
    (fun m => vertical_poisson f m) (horizontal_poisson f)

end EisensteinSchwartzPoisson

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Poisson.EisensteinLattice
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical

namespace EisensteinSchwartzPoisson

section
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem integral_comp_linearEquiv (A : ℂ ≃L[ℝ] ℂ) (f : ℂ → ℂ) :
    (∫ x : ℂ, f (A x)) = inverseJacobian A • ∫ x : ℂ, f x := by
  have h := integral_map_equiv («μ» := (volume : Measure ℂ))
    A.toHomeomorph.toMeasurableEquiv f
  have hm : Measure.map A (volume : Measure ℂ) =
      ENNReal.ofReal (inverseJacobian A) • volume := by
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume
      A.toLinearEquiv.isUnit_det'.ne_zero
  change (∫ y : ℂ, f y ∂Measure.map A volume) = (∫ x : ℂ, f (A x)) at h
  rw [hm, integral_smul_measure, ENNReal.toReal_ofReal (show 0 ≤ inverseJacobian A from abs_nonneg _)] at h
  exact h.symm

theorem inner_linear_dual (A : ℂ ≃L[ℝ] ℂ) (x y : ℂ) :
    inner ℝ (A x) (dualMap A y) = inner ℝ x y := by
  rw [dualMap, ContinuousLinearMap.adjoint_inner_right]
  simp

theorem fourier_comp_linearEquiv (A : ℂ ≃L[ℝ] ℂ) (f : ℂ → ℂ) (w : ℂ) :
    𝓕 (f ∘ A) w = inverseJacobian A • 𝓕 f (dualMap A w) := by
  let H : ℂ → ℂ := fun z => Real.fourierChar (-inner ℝ z (dualMap A w)) • f z
  calc
    𝓕 (f ∘ A) w = ∫ x : ℂ, H (A x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [H, inner_linear_dual, Function.comp_apply]
        rfl
    _ = inverseJacobian A • ∫ z : ℂ, H z := integral_comp_linearEquiv A H
    _ = inverseJacobian A • 𝓕 f (dualMap A w) := rfl

theorem fourier_translate (f : ℂ → ℂ) (b w : ℂ) :
    𝓕 (fun z => f (z + b)) w =
      Real.fourierChar (inner ℝ b w) • 𝓕 f w := by
  exact congrFun
    (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
      (volume : Measure ℂ) (innerₗ ℂ) f b) w

theorem fourier_affinePullback (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b w : ℂ) :
    (𝓕 (affinePullback f A b)) w =
      inverseJacobian A •
        (Real.fourierChar (inner ℝ b (dualMap A w)) • (𝓕 f) (dualMap A w)) := by
  rw [congrFun (SchwartzMap.fourier_coe _) w]
  change 𝓕 ((fun z => f (z + b)) ∘ A) w = _
  rw [fourier_comp_linearEquiv, fourier_translate]
  rw [congrFun (SchwartzMap.fourier_coe f) (dualMap A w)]

theorem affine_lattice_poisson (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) :
    (∑' p : ℤ × ℤ, f (A (complexPoint (p.1 : ℝ) (p.2 : ℝ)) + b)) =
      inverseJacobian A • ∑' p : ℤ × ℤ,
        Real.fourierChar (inner ℝ b (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) •
          (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))) := by
  have h := integer_pair_poisson (affinePullback f A b)
  simp only [affinePullback_apply, fourier_affinePullback] at h
  rw [tsum_const_smul''] at h
  exact h

end

section
open MeasureTheory EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem eisensteinLatticeMap_point (c : ℂ) (hc : c ≠ 0) (p : ℤ × ℤ) :
    eisensteinLatticeMap c hc (complexPoint (p.1 : ℝ) (p.2 : ℝ)) =
      c * eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) := by
  simp [eisensteinLatticeMap, complexPoint, eisEmbedding_eval, mul_comm]

theorem actual_eisenstein_coset_poisson (f : 𝓢(ℂ, ℂ)) (b c : O) (hc : c ≠ 0) :
    (∑' z : O, f (eisEmbedding (b + c * z))) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖ ^ 2)) • ∑' p : ℤ × ℤ,
        Real.fourierChar (inner ℝ (eisEmbedding b)
          (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) •
        (𝓕 f) (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p) := by
  let A := eisensteinLatticeMap (eisEmbedding c) (eisEmbedding_ne_zero hc)
  have h := affine_lattice_poisson f A (eisEmbedding b)
  rw [eisenstein_inverseJacobian] at h
  calc
    (∑' z : O, f (eisEmbedding (b + c * z))) =
        ∑' p : ℤ × ℤ, f (eisEmbedding (b + c * latticeCoordEquiv.symm p)) :=
      (latticeCoordEquiv.symm.tsum_eq _).symm
    _ = ∑' p : ℤ × ℤ,
        f (A (complexPoint (p.1 : ℝ) (p.2 : ℝ)) + eisEmbedding b) := by
      apply tsum_congr
      intro p
      congr 1
      rw [map_add, map_mul]
      change eisEmbedding b + eisEmbedding c *
          eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) = _
      rw [← eisensteinLatticeMap_point]
      exact add_comm _ _
    _ = _ := h

theorem actual_eisenstein_coset_summable_norm (f : 𝓢(ℂ, ℂ)) (b c : O) (hc : c ≠ 0) :
    Summable (fun z : O => ‖f (eisEmbedding (b + c * z))‖) := by
  let A := eisensteinLatticeMap (eisEmbedding c) (eisEmbedding_ne_zero hc)
  have hp := plane_lattice_summable_norm (affinePullback f A (eisEmbedding b))
  have hpair : Summable (fun p : ℤ × ℤ =>
      ‖f (eisEmbedding (b + c * latticeCoordEquiv.symm p))‖) := by
    convert (preTransparency := .instances) hp using 1
    funext p
    rw [affinePullback_apply]
    apply congrArg norm
    apply congrArg f
    rw [map_add, map_mul]
    change eisEmbedding b + eisEmbedding c *
        eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) = _
    rw [← eisensteinLatticeMap_point]
    exact add_comm _ _
  exact (latticeCoordEquiv.symm.summable_iff).mp hpair

theorem actual_eisenstein_summable_norm (f : 𝓢(ℂ, ℂ)) :
    Summable (fun z : O => ‖f (eisEmbedding z)‖) := by
  simpa using actual_eisenstein_coset_summable_norm f 0 1 one_ne_zero

theorem actual_eisenstein_periodic_summable (f : 𝓢(ℂ, ℂ))
    {R : Type*} [Fintype R] (q : O → R) (P : R → ℂ) :
    Summable (fun z : O => P (q z) * f (eisEmbedding z)) := by
  classical
  let C : ℝ := ∑ r : R, ‖P r‖
  have hP (r : R) : ‖P r‖ ≤ C :=
    Finset.single_le_sum (fun a _ => norm_nonneg (P a)) (Finset.mem_univ r)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _
    ((actual_eisenstein_summable_norm f).mul_left C)
  intro z
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hP (q z)) (norm_nonneg _)

theorem actual_eisenstein_periodic_poisson (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      ∑ r : O ⧸ Ideal.span {c}, P r *
        ((2 / (Real.sqrt 3 * ‖eisEmbedding c‖ ^ 2)) • ∑' p : ℤ × ℤ,
          Real.fourierChar (inner ℝ
            (eisEmbedding (GaussianShiftedPartition.representative c r))
            (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) •
          (𝓕 f) (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [GaussianAbelPartition.tsum_periodic_weighted_partition
    (Ideal.Quotient.mk (Ideal.span {c})) P (fun z => f (eisEmbedding z))
    (actual_eisenstein_periodic_summable f _ P)]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  exact (GaussianFiberEquiv.fiber_tsum c hc r
    (GaussianShiftedPartition.representative c r)
    (GaussianShiftedPartition.representative_spec c r)
    (fun z => f (eisEmbedding z))).trans
      (actual_eisenstein_coset_poisson f _ c hc)

theorem inverseJacobian_pos (A : ℂ ≃L[ℝ] ℂ) : 0 < inverseJacobian A :=
  abs_pos.mpr (inv_ne_zero A.toLinearEquiv.isUnit_det'.ne_zero)

theorem dual_lattice_summable_norm (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) :
    Summable (fun p : ℤ × ℤ =>
      ‖(𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))‖) := by
  have hJ := inverseJacobian_pos A
  have hp := plane_lattice_summable_norm (𝓕 (affinePullback f A 0))
  have hn (p : ℤ × ℤ) :
      ‖(𝓕 (affinePullback f A 0)) (complexPoint (p.1 : ℝ) (p.2 : ℝ))‖ =
      inverseJacobian A * ‖(𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))‖ := by
    rw [fourier_affinePullback]
    simp [ abs_of_pos hJ]
  simp_rw [hn] at hp
  have hi := hp.mul_left (inverseJacobian A)⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ hJ.ne', one_mul] using hi

theorem finite_phase_sum {R : Type*} [Fintype R]
    (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b : R → ℂ) (P : R → ℂ) :
    (∑ r : R, P r * (inverseJacobian A • ∑' p : ℤ × ℤ,
      Real.fourierChar (inner ℝ (b r) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) •
        (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))))) =
    inverseJacobian A • ∑' p : ℤ × ℤ,
      (∑ r : R, P r * (Real.fourierChar (inner ℝ (b r)
        (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) : ℂ)) *
        (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))) := by
  classical
  have hs (r : R) : Summable (fun p : ℤ × ℤ =>
      P r * (Real.fourierChar (inner ℝ (b r)
        (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) •
        (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))))) := by
    apply Summable.mul_left
    apply Summable.of_norm
    simpa only [Circle.norm_smul] using dual_lattice_summable_norm f A
  simp_rw [mul_smul_comm, ← tsum_mul_left]
  rw [← Finset.smul_sum, ← Summable.tsum_finsetSum (fun r _ => hs r)]
  congr 1
  apply tsum_congr
  intro p
  simp only [Circle.smul_def, smul_eq_mul, Finset.sum_mul, mul_assoc]

theorem actual_eisenstein_periodic_fourier (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖ ^ 2)) • ∑' p : ℤ × ℤ,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          (Real.fourierChar (inner ℝ
            (eisEmbedding (GaussianShiftedPartition.representative c r))
            (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) : ℂ)) *
          (𝓕 f) (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [actual_eisenstein_periodic_poisson f c hc P]
  have h := finite_phase_sum f
    (eisensteinLatticeMap (eisEmbedding c) (eisEmbedding_ne_zero hc))
    (fun r => eisEmbedding (GaussianShiftedPartition.representative c r)) P
  rw [eisenstein_inverseJacobian] at h
  exact h

end

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem dualMap_trans (A B : ℂ ≃L[ℝ] ℂ) (z : ℂ) :
    dualMap (A.trans B) z = dualMap B (dualMap A z) := by
  change (ContinuousLinearMap.adjoint
    (A.symm.toContinuousLinearMap.comp B.symm.toContinuousLinearMap)) z = _
  rw [ContinuousLinearMap.adjoint_comp]
  rfl

theorem dual_basis_apply (w : ℂ) (hw : w.im ≠ 0) (z : ℂ) :
    dualMap (basisEquiv w hw) z =
      complexPoint z.re ((z.im - w.re * z.re) / w.im) := by
  apply ext_inner_left ℝ
  intro v
  rw [dualMap, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ ((basisEquiv w hw).symm v) z = _
  simp only [basisEquiv_symm_apply, Complex.inner, complexPoint,
    Complex.mul_re,  Complex.conj_re, Complex.conj_im]
  field_simp [hw]
  ring

theorem dual_mul_apply (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    dualMap (complexMulEquiv c hc) z = (starRingEnd ℂ c)⁻¹ * z := by
  apply ext_inner_left ℝ
  intro v
  rw [dualMap, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (c⁻¹ * v) z = _
  simp only [Complex.inner, map_mul, map_inv₀]
  congr 1
  ring

theorem eisensteinDualFrequency_explicit (c : ℂ) (hc : c ≠ 0) (p : ℤ × ℤ) :
    eisensteinDualFrequency c hc p =
      complexPoint (p.1 : ℝ) (((p.1 : ℝ) + 2 * (p.2 : ℝ)) / Real.sqrt 3) /
        starRingEnd ℂ c := by
  unfold eisensteinDualFrequency eisensteinLatticeMap scaledBasisEquiv
  rw [dualMap_trans, dual_basis_apply, dual_mul_apply]
  have he : complexPoint (complexPoint (p.1 : ℝ) (p.2 : ℝ)).re
      (((complexPoint (p.1 : ℝ) (p.2 : ℝ)).im - omega3.re *
        (complexPoint (p.1 : ℝ) (p.2 : ℝ)).re) / omega3.im) =
      complexPoint (p.1 : ℝ) (((p.1 : ℝ) + 2 * (p.2 : ℝ)) / Real.sqrt 3) := by
    apply Complex.ext
    · rfl
    · simp only [complexPoint, omega3_im]
      have hr : omega3.re = -(1 / 2 : ℝ) := by norm_num [omega3]
      rw [hr]
      ring
  rw [he]
  ring

theorem actual_eisenstein_poisson_explicit (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖ ^ 2)) • ∑' p : ℤ × ℤ,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          (Real.fourierChar (inner ℝ
            (eisEmbedding (GaussianShiftedPartition.representative c r))
            (explicitDualFrequency (eisEmbedding c) p)) : ℂ)) *
          (𝓕 f) (explicitDualFrequency (eisEmbedding c) p) := by
  simpa only [eisensteinDualFrequency_explicit, explicitDualFrequency] using
    actual_eisenstein_periodic_fourier f c hc P

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

end EisensteinSchwartzPoisson

open scoped BigOperators Classical

namespace IdealGaussCRT

theorem gauss_transform_finite_crt_scalar {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, Field (R i)]
    [Fintype T] [∀ i, Fintype (R i)]
    (e : T ≃+* ∀ i, R i)
    (χ : ∀ i, MulChar (R i) ℂ) (ψ : AddChar T ℂ)
    (hχ : ∀ i, χ i ≠ 1) (h : T) :
    (∑ x : T, (∏ i, χ i (e x i)) * ψ (h * x)) =
      (∏ i, χ i (e h i))⁻¹ *
        ∑ x : T, (∏ i, χ i (e x i)) * ψ x := by
  classical
  have hbase := gauss_transform_finite_crt R e χ ψ hχ (1 : T)
  simp only [one_mul, map_one, Pi.one_apply, one_ne_zero, ↓reduceIte,
    inv_one, one_mul] at hbase
  rw [gauss_transform_finite_crt R e χ ψ hχ h, hbase]
  have hlocal (i : ι) :
      (if e h i = 0 then 0 else
        (χ i (e h i))⁻¹ * gaussSum (χ i) (coordinateAddChar R e ψ i)) =
      (χ i (e h i))⁻¹ * gaussSum (χ i) (coordinateAddChar R e ψ i) := by
    split_ifs with hi
    · simp [hi]
    · rfl
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]

end IdealGaussCRT

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical

namespace ActualEisensteinCubic

theorem canonical_finite_prime_gauss_transform_scalar
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) (h : O ⧸ ∏ i, P i) :
    (∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ (h * x)) =
      (finiteSexticQuotientRow P hc hgood j h)⁻¹ *
        ∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ x := by
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
  exact IdealGaussCRT.gauss_transform_finite_crt_scalar (fun i => O ⧸ P i)
    (IdealGaussCRT.quotientProdEquivPi P hc)
    (fun i => canonicalSextic (P i) (hgood i) ^ j i) ψ
    (fun i => canonicalSextic_pow_ne_one (P i) (hgood i) (hchar i) (hj0 i) (hj6 i)) h

theorem finiteSexticQuotientRow_inv_eq_star
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (h : O ⧸ ∏ i, P i) :
    (finiteSexticQuotientRow P hc hgood j h)⁻¹ =
      star (finiteSexticQuotientRow P hc hgood j h) := by
  classical
  simp only [finiteSexticQuotientRow, star_prod]
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [MulChar.star_apply', MulChar.inv_apply_eq_inv']

theorem canonical_finite_prime_gauss_transform_conj
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) (h : O ⧸ ∏ i, P i) :
    (∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ (h * x)) =
      star (finiteSexticQuotientRow P hc hgood j h) *
        ∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ x := by
  rw [canonical_finite_prime_gauss_transform_scalar P hc hgood hchar j hj0 hj6 ψ,
    finiteSexticQuotientRow_inv_eq_star]

end ActualEisensteinCubic

namespace EisensteinSchwartzPoisson

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem explicitDualFrequency_eq_paperFrequency (c : ℂ) (p : ℤ × ℤ) :
    explicitDualFrequency c p = paperFrequency (eisEmbedding (dualFrequencyEquiv p) / c) := by
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hnum : complexPoint (p.1 : ℝ)
      (((p.1 : ℝ) + 2 * (p.2 : ℝ)) / Real.sqrt 3) =
      (2 * Complex.I / (Real.sqrt 3 : ℂ)) *
        starRingEnd ℂ (eisEmbedding (dualFrequencyEquiv p)) := by
    rw [dualFrequencyEquiv_coordinates]
    apply Complex.ext <;>
      norm_num [complexPoint, Complex.div_re, Complex.div_im] <;>
      field_simp <;>
      simp only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  unfold explicitDualFrequency paperFrequency
  rw [map_div₀, hnum]
  ring

theorem explicitDualFrequency_phase (r c : ℂ) (p : ℤ × ℤ) :
    (Real.fourierChar (inner ℝ r (explicitDualFrequency c p)) : ℂ) =
      paperE (r * eisEmbedding (dualFrequencyEquiv p) / c) := by
  rw [explicitDualFrequency_eq_paperFrequency, fourierChar_paperFrequency]
  congr 1
  ring

theorem actual_eisenstein_paper_poisson (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (1 / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          paperE (eisEmbedding (GaussianShiftedPartition.representative c r) *
            eisEmbedding h / eisEmbedding c)) *
          paperFourier f (eisEmbedding h / eisEmbedding c) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let A : O → ℂ := fun h => ∑ r : O ⧸ Ideal.span {c}, P r *
    paperE (eisEmbedding (GaussianShiftedPartition.representative c r) *
      eisEmbedding h / eisEmbedding c)
  have ht : (∑' h : O, A h * paperFourier f (eisEmbedding h / eisEmbedding c)) =
      (2 / Real.sqrt 3 : ℝ) • ∑' p : ℤ × ℤ,
        A (dualFrequencyEquiv p) *
          (𝓕 f) (explicitDualFrequency (eisEmbedding c) p) := by
    calc
      _ = ∑' p : ℤ × ℤ, A (dualFrequencyEquiv p) *
          paperFourier f (eisEmbedding (dualFrequencyEquiv p) / eisEmbedding c) :=
        (dualFrequencyEquiv.tsum_eq _).symm
      _ = ∑' p : ℤ × ℤ, (2 / Real.sqrt 3 : ℝ) •
          (A (dualFrequencyEquiv p) *
            (𝓕 f) (explicitDualFrequency (eisEmbedding c) p)) := by
        apply tsum_congr
        intro p
        rw [paperFourier_eq_standard, ← explicitDualFrequency_eq_paperFrequency]
        change A (dualFrequencyEquiv p) *
          ((2 / Real.sqrt 3 : ℝ) • (𝓕 f) (explicitDualFrequency (eisEmbedding c) p)) = _
        simp only [Algebra.smul_def]
        ring
      _ = _ := tsum_const_smul'' _
    rfl
  have hp := actual_eisenstein_poisson_explicit f c hc P
  simp_rw [explicitDualFrequency_phase] at hp
  change _ = (1 / ‖eisEmbedding c‖ ^ 2 : ℝ) •
    ∑' h : O, A h * paperFourier f (eisEmbedding h / eisEmbedding c)
  rw [ht, smul_smul]
  convert (preTransparency := .instances) hp using 1
  congr 1
  ring

theorem actual_eisenstein_paper_poisson_trace (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (1 / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          paperFourier f (eisEmbedding h / eisEmbedding c) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  simpa only [eisTraceModChar_frequency] using actual_eisenstein_paper_poisson f c hc P

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

theorem paperFourier_comp_mul (f : ℂ → ℂ) (a : ℂ) (ha : a ≠ 0) (u : ℂ) :
    paperFourier (fun z => f (a * z)) u =
      (1 / ‖a‖ ^ 2 : ℝ) • paperFourier f (u / a) := by
  have hd : dualMap (complexMulEquiv a ha) (paperFrequency u) =
      paperFrequency (u / a) := by
    rw [dual_mul_apply]
    unfold paperFrequency
    rw [map_div₀]
    ring
  have hj : inverseJacobian (complexMulEquiv a ha) = 1 / ‖a‖ ^ 2 := by
    rw [inverseJacobian, complexMulEquiv_det, abs_inv,
      abs_of_nonneg (Complex.normSq_nonneg a), Complex.sq_norm]
    ring
  rw [paperFourier_eq_standard, paperFourier_eq_standard]
  have hF := fourier_comp_linearEquiv (complexMulEquiv a ha) f (paperFrequency u)
  simp only [Function.comp_def, complexMulEquiv_apply] at hF
  rw [hF, hd, hj, smul_smul, smul_smul]
  congr 1
  ring

theorem paperFourier_radial (W : ℝ → ℂ) (u : ℂ) :
    paperFourier (fun z => W (‖z‖ ^ 2)) u =
      paperRadialFourier W (‖u‖ ^ 2) := by
  unfold paperRadialFourier
  rw [Real.sqrt_sq (norm_nonneg u)]
  by_cases hu : u = 0
  · simp [hu]
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hnC : (‖u‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  let a : ℂ := u / (‖u‖ : ℂ)
  have ha : a ≠ 0 := div_ne_zero hu hnC
  have hna : ‖a‖ = 1 := by
    simp [a, Complex.norm_real, hn]
  have hq : u / a = (‖u‖ : ℂ) := by
    dsimp [a]
    field_simp
  have hfun : (fun z : ℂ => W (‖a * z‖ ^ 2)) = fun z : ℂ => W (‖z‖ ^ 2) := by
    funext z
    rw [norm_mul, hna, one_mul]
  have hF := paperFourier_comp_mul (fun z => W (‖z‖ ^ 2)) a ha u
  rw [hfun, hna, hq] at hF
  simpa using hF

theorem inverseSqrt_norm_sq (K : ℝ) (hK : 0 < K) :
    ‖(Real.sqrt K : ℂ)⁻¹‖ ^ 2 = 1 / K := by
  rw [norm_inv, inv_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg K), Real.sq_sqrt hK.le, one_div]

theorem paperFourier_radial_scaled (W : ℝ → ℂ) (K : ℝ) (hK : 0 < K) (u : ℂ) :
    paperFourier (fun z => W (‖z‖ ^ 2 / K)) u =
      K • paperRadialFourier W (K * ‖u‖ ^ 2) := by
  let a : ℂ := (Real.sqrt K : ℂ)⁻¹
  have ha : a ≠ 0 := inverseSqrt_ne_zero K hK
  have hna : ‖a‖ ^ 2 = 1 / K := inverseSqrt_norm_sq K hK
  have hfun : (fun z : ℂ => W (‖a * z‖ ^ 2)) =
      fun z : ℂ => W (‖z‖ ^ 2 / K) := by
    funext z
    rw [norm_mul, mul_pow, hna]
    congr 1
    ring
  have hnorm : ‖u / a‖ ^ 2 = K * ‖u‖ ^ 2 := by
    rw [norm_div, div_pow, hna]
    field_simp
  have hF := paperFourier_comp_mul (fun z => W (‖z‖ ^ 2)) a ha u
  rw [hfun, hna, one_div_one_div, paperFourier_radial, hnorm] at hF
  exact hF

@[simp] theorem scaledRadialTest_apply (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (z : ℂ) :
    scaledRadialTest W K hK z = W (‖z‖ ^ 2 / K) := by
  simp only [scaledRadialTest, affinePullback_apply, complexMulEquiv_apply,
    add_zero, radialTest_apply, norm_mul, mul_pow, inverseSqrt_norm_sq K hK]
  congr 1
  ring

theorem paperFourier_scaledRadialTest (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (u : ℂ) :
    paperFourier (scaledRadialTest W K hK) u =
      K • paperRadialFourier W (K * ‖u‖ ^ 2) := by
  change paperFourier (fun z => scaledRadialTest W K hK z) u = _
  simp only [scaledRadialTest_apply]
  exact paperFourier_radial_scaled W K hK u

theorem actual_radial_paper_poisson_trace (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K)
    (c : O) (hc : c ≠ 0) (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * W (‖eisEmbedding z‖ ^ 2 / K)) =
      (K / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc
  let A : O → ℂ := fun h => ∑ r : O ⧸ Ideal.span {c}, P r *
    ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)
  have ht : (∑' h : O, A h *
      paperFourier (scaledRadialTest W K hK) (eisEmbedding h / eisEmbedding c)) =
      K • ∑' h : O, A h *
        paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
    calc
      _ = ∑' h : O, K • (A h *
          paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)) := by
        apply tsum_congr
        intro h
        rw [paperFourier_scaledRadialTest, norm_div, div_pow]
        have hr : K * (‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) =
            K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2 := by ring
        rw [hr]
        simp only [Algebra.smul_def]
        ring
      _ = _ := tsum_const_smul'' _
  have hp := actual_eisenstein_paper_poisson_trace (scaledRadialTest W K hK) c hc P
  change (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) *
    scaledRadialTest W K hK (eisEmbedding z)) =
    (1 / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O, A h *
      paperFourier (scaledRadialTest W K hK) (eisEmbedding h / eisEmbedding c) at hp
  rw [ht, smul_smul] at hp
  simpa only [scaledRadialTest_apply, one_div_mul_eq_div] using hp

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap ContDiff

namespace ActualEisensteinCubic
open ConcreteTraceCRT EisensteinSchwartzPoisson

theorem canonical_principal_gauss_transform {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (c : O) (hc : Ideal.span {c} = ∏ i, P i)
    [Fintype (O ⧸ Ideal.span {c})]
    (ψ : AddChar (O ⧸ Ideal.span {c}) ℂ) (h : O ⧸ Ideal.span {c}) :
    (∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r * ψ (h * r)) =
      star (principalSexticRow P hcop hgood j c hc h) *
        ∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r * ψ r := by
  let e := Ideal.quotEquivOfEq hc
  let row := finiteSexticQuotientRow P hcop hgood j
  let φ : AddChar (O ⧸ ∏ i, P i) ℂ := ψ.compAddMonoidHom e.symm.toAddMonoidHom
  have hleft :
      (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ (h * r)) =
        ∑ x : O ⧸ ∏ i, P i, row x * φ (e h * x) := by
    rw [← Equiv.sum_comp e.toEquiv (fun x => row x * φ (e h * x))]
    apply Finset.sum_congr rfl
    intro r _
    change row (e r) * ψ (h * r) = row (e r) * ψ (e.symm (e h * e r))
    rw [← map_mul, e.symm_apply_apply]
  have hbase :
      (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ r) =
        ∑ x : O ⧸ ∏ i, P i, row x * φ x := by
    rw [← Equiv.sum_comp e.toEquiv (fun x => row x * φ x)]
    apply Finset.sum_congr rfl
    intro r _
    change row (e r) * ψ r = row (e r) * ψ (e.symm (e r))
    rw [e.symm_apply_apply]
  change (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ (h * r)) =
    star (row (e h)) * ∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ r
  rw [hleft, hbase]
  exact canonical_finite_prime_gauss_transform_conj P hcop hgood hchar j hj0 hj6 φ (e h)

theorem canonical_radial_poisson {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let c := finitePrimeModulus P
    let hc0 := finitePrimeModulus_ne_zero P
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let row := principalSexticRow P hcop hgood j c (span_finitePrimeModulus P)
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc0
    (∑' z : O, finiteSexticRow P hgood j z * W (‖eisEmbedding z‖ ^ 2 / scale)) =
      (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (star (finiteSexticRow P hgood j h) * (∑ r, row r * ψ r)) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  classical
  let c := finitePrimeModulus P
  have hc0 : c ≠ 0 := finitePrimeModulus_ne_zero P
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (span_finitePrimeModulus P)
  let : Fintype (O ⧸ ∏ i, P i) := Fintype.ofEquiv (O ⧸ Ideal.span {c}) e.toEquiv
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let row := principalSexticRow P hcop hgood j c (span_finitePrimeModulus P)
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc0
  have ht (h : O) :
      (∑ r : O ⧸ Ideal.span {c}, row r * ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) =
        star (finiteSexticRow P hgood j h) * (∑ r, row r * ψ r) := by
    rw [canonical_principal_gauss_transform P hcop hgood hchar j hj0 hj6 c
      (span_finitePrimeModulus P) ψ, principalSexticRow_mk]
  have hp := actual_radial_paper_poisson_trace W scale hscale c hc0 row
  change (∑' z : O, row (Ideal.Quotient.mk (Ideal.span {c}) z) *
    W (‖eisEmbedding z‖ ^ 2 / scale)) =
      (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, row r *
          ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) at hp
  simp_rw [ht] at hp
  simpa only [row, principalSexticRow_mk] using hp

theorem canonical_radial_poisson_normalized {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let c := finitePrimeModulus P
    (∑' z : O, finiteSexticRow P hgood j z * W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * canonicalNormalizedGauss P hcop hgood j / (‖eisEmbedding c‖ : ℂ)) *
        ∑' h : O, star (finiteSexticRow P hgood j h) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  classical
  let c := finitePrimeModulus P
  let G := canonicalGaussSum P hcop hgood j
  let F : O → ℂ := fun h => star (finiteSexticRow P hgood j h) *
    paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)
  have hp := canonical_radial_poisson P hcop hgood hchar j hj0 hj6 W scale hscale
  change (∑' z : O, finiteSexticRow P hgood j z * W (‖eisEmbedding z‖ ^ 2 / scale)) =
    (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
      (star (finiteSexticRow P hgood j h) * G) *
        paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) at hp
  have hsum : (∑' h : O, (star (finiteSexticRow P hgood j h) * G) *
      paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)) =
      G * ∑' h : O, F h := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro h
    dsimp [F]
    ring
  rw [hsum] at hp
  rw [hp]
  change ((scale / ‖eisEmbedding c‖ ^ 2 : ℝ) : ℂ) * (G * ∑' h : O, F h) =
    ((scale : ℂ) * (G / (‖eisEmbedding c‖ : ℂ)) / (‖eisEmbedding c‖ : ℂ)) *
      ∑' h : O, F h
  have hn : (‖eisEmbedding c‖ : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr
      (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero P)))
  push_cast
  field_simp

theorem finiteSexticRow_eq_zero_iff {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) (a : O) :
    finiteSexticRow P hgood j a = 0 ↔ ∃ i, a ∈ P i := by
  classical
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
  simp only [finiteSexticRow, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and,
    MulChar.apply_eq_zero_iff, isUnit_iff_ne_zero, not_not, Ideal.Quotient.eq_zero_iff_mem]

theorem finiteSexticRow_zero {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) :
    finiteSexticRow P hgood j 0 = 0 := by
  rw [finiteSexticRow_eq_zero_iff]
  exact ⟨Classical.arbitrary ι, Ideal.zero_mem _⟩

theorem finiteSexticRow_radial_summable {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    Summable (fun z : O => finiteSexticRow P hgood j z *
      W (‖eisEmbedding z‖ ^ 2 / scale)) := by
  let c := finitePrimeModulus P
  have hc0 : c ≠ 0 := finitePrimeModulus_ne_zero P
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  have hs := actual_eisenstein_periodic_summable (scaledRadialTest W scale hscale)
    (Ideal.Quotient.mk (Ideal.span {c}))
    (principalSexticRow P hcop hgood j c (span_finitePrimeModulus P))
  simpa only [principalSexticRow_mk, scaledRadialTest_apply] using hs

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Poisson.RadialFourier
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff

namespace EisensteinSchwartzPoisson

open ConcreteTraceCRT ActualEisensteinCubic
open scoped SchwartzMap

theorem polynomial_tail_majorant (A : ℕ) (K T q B f : ℝ)
    (hK : 0 < K) (hT : 0 ≤ T) (hq : 0 ≤ q) (hf : 0 ≤ f)
    (htail : T ≤ K * q) (hbound : (1 + K * q) ^ (A + 2) * f ≤ B) :
    f ≤ (B / ((min 1 K) ^ 2 * (1 + T) ^ A)) * ((1 + q) ^ 2)⁻¹ := by
  have hm : 0 < min 1 K := lt_min (by norm_num) hK
  have hm1 : min 1 K ≤ 1 := min_le_left _ _
  have hmK : min 1 K ≤ K := min_le_right _ _
  have hbase : min 1 K * (1 + q) ≤ 1 + K * q := by
    nlinarith [mul_le_mul_of_nonneg_right hmK hq]
  have htwo : (min 1 K) ^ 2 * (1 + q) ^ 2 ≤ (1 + K * q) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hpow : (1 + T) ^ A ≤ (1 + K * q) ^ A :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hden : ((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2 ≤
      (1 + K * q) ^ (A + 2) := by
    have hh := mul_le_mul hpow htwo (by positivity) (by positivity)
    rw [pow_add]
    nlinarith
  have hprod : f * (((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2) ≤ B := by
    calc
      _ = (((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2) * f := mul_comm _ _
      _ ≤ (1 + K * q) ^ (A + 2) * f := mul_le_mul_of_nonneg_right hden hf
      _ ≤ B := hbound
  have hraw := (le_div_iff₀ (show 0 < ((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2
      by positivity)).mpr hprod
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using hraw

theorem paperRadialFourier_lattice_summable_norm (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun h : O => ‖paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)‖) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound 2
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let D := (min 1 K) ^ 2 * (1 + (0 : ℝ)) ^ (0 : ℕ)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (eisenstein_cauchy_summable.mul_left (B / D))
  intro h
  exact polynomial_tail_majorant 0 K 0 _ B _ hK (by norm_num)
    (sq_nonneg _) (norm_nonneg _) (by positivity) (hb W _ (by positivity))

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap ContDiff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.IdealGenerators
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical

open scoped BigOperators Classical

namespace ConcretePrimeRowBridge

theorem tsum_ideal_eq_tsum_generator (J : Ideal O) (hJ : J ≠ ⊥)
    (f : O → ℂ) :
    (∑' u : O, if u ∈ J then f u else 0) =
      ∑' z : O, f (idealGenerator J * z) := by
  let d := idealGenerator J
  have hd : d ≠ 0 := idealGenerator_ne_zero J hJ
  let F : O → ℂ := fun u => if u ∈ J then f u else 0
  have hrange : Function.support F ⊆ Set.range (fun z : O => d * z) := by
    intro u hu
    have huJ : u ∈ J := by
      by_contra hn
      exact hu (by simp [F, hn])
    rw [← span_idealGenerator J, Ideal.mem_span_singleton] at huJ
    obtain ⟨z, hz⟩ := huJ
    exact ⟨z, hz.symm⟩
  have ht := (mul_right_injective₀ hd).tsum_eq hrange
  calc
    (∑' u : O, if u ∈ J then f u else 0) = ∑' z : O, F (d * z) := ht.symm
    _ = ∑' z : O, f (d * z) := by
      apply tsum_congr
      intro z
      have hz : d * z ∈ J := by
        rw [← span_idealGenerator J, Ideal.mem_span_singleton]
        exact ⟨z, rfl⟩
      simp only [F, if_pos hz]

end ConcretePrimeRowBridge

namespace ActualEisensteinCubic

theorem tsum_rowCoprimeMask_subsets
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S : Finset ι)
    (f : O → ℂ) (hf : Summable f) :
    (∑' u : O, rowCoprimeMask P S u * f u) =
      ∑ E ∈ S.powerset, (-1 : ℂ) ^ E.card *
        ∑' u : O, if ∀ i ∈ E, u ∈ P i then f u else 0 := by
  have hterm (u : O) : rowCoprimeMask P S u * f u =
      ∑ E ∈ S.powerset, (-1 : ℂ) ^ E.card *
        (if ∀ i ∈ E, u ∈ P i then f u else 0) := by
    rw [rowCoprimeMask_subsets, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro E hE
    by_cases h : ∀ i ∈ E, u ∈ P i <;> simp [h]
  have hsum (E : Finset ι) :
      Summable (fun u : O => (-1 : ℂ) ^ E.card *
        (if ∀ i ∈ E, u ∈ P i then f u else 0)) := by
    have hi := hf.indicator {u : O | ∀ i ∈ E, u ∈ P i}
    simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using hi.mul_left ((-1 : ℂ) ^ E.card)
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum (fun E _ => hsum E)]
  apply Finset.sum_congr rfl
  intro E hE
  exact tsum_mul_left

theorem primeSubsetGenerator_ne_zero {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (E : Finset ι) :
    primeSubsetGenerator P E ≠ 0 := by
  apply ConcretePrimeRowBridge.idealGenerator_ne_zero
  change (∏ i ∈ E, P i) ≠ 0
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i))

theorem tsum_rowCoprimeMask_dilations
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (f : O → ℂ) (hf : Summable f) :
    (∑' u : O, rowCoprimeMask P S u * f u) =
      ∑ E ∈ S.powerset,
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
          ∑' z : O, f (primeSubsetGenerator P E * z) := by
  rw [tsum_rowCoprimeMask_subsets P S f hf]
  have hprime (i : ι) : Prime (P i) :=
    Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
  apply Finset.sum_congr rfl
  intro E hE
  rw [prime_product_moebius P hprime hinj E]
  congr 1
  have hJ : (∏ i ∈ E, P i) ≠ ⊥ := by
    change (∏ i ∈ E, P i) ≠ 0
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i))
  calc
    _ = ∑' u : O, if u ∈ (∏ i ∈ E, P i) then f u else 0 := by
      apply tsum_congr
      intro u
      rw [mem_prime_product_iff P hinj E u]
      by_cases h : ∀ i ∈ E, u ∈ P i <;> simp [h]
    _ = _ := ConcretePrimeRowBridge.tsum_ideal_eq_tsum_generator _ hJ f

open ConcreteTraceCRT

theorem tsum_masked_radial_dilations
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (hinj : Function.Injective P) (S : Finset ι)
    (r : O → ℂ) (hr : ∀ a b, r (a * b) = r a * r b)
    (W : ℝ → ℂ) (scale : ℝ)
    (hsum : Summable (fun u : O => r u * W (‖eisEmbedding u‖ ^ 2 / scale))) :
    (∑' u : O, rowCoprimeMask P S u * r u * W (‖eisEmbedding u‖ ^ 2 / scale)) =
      ∑ E ∈ S.powerset,
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
          r (primeSubsetGenerator P E) *
          ∑' z : O, r z *
            W (‖eisEmbedding z‖ ^ 2 / (scale / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2)) := by
  calc
    _ = ∑' u : O, rowCoprimeMask P S u *
        (r u * W (‖eisEmbedding u‖ ^ 2 / scale)) := by
      apply tsum_congr
      intro u
      ring
    _ = _ := by
      rw [tsum_rowCoprimeMask_dilations P hinj S _ hsum]
      apply Finset.sum_congr rfl
      intro E hE
      rw [mul_assoc]
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr
      intro z
      rw [hr, map_mul, norm_mul, mul_pow, div_div_eq_mul_div]
      ring_nf

open ConcreteTraceCRT EisensteinSchwartzPoisson

theorem primeSubset_reducedScale_pos {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (E : Finset α)
    {scale : ℝ} (hscale : 0 < scale) :
    0 < scale / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 := by
  exact div_pos hscale (sq_pos_of_pos (norm_pos_iff.mpr
    (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E))))

theorem canonical_masked_radial_dilations
    {α ι : Type*} [DecidableEq α] [Fintype ι]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (S : Finset α)
    (Q : ι → Ideal O) [∀ i, (Q i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime Q))
    (hgood : ∀ i, lambda ∉ Q i) (j : ι → ℕ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' u : O, rowCoprimeMask P S u * finiteSexticRow Q hgood j u *
      W (‖eisEmbedding u‖ ^ 2 / scale)) =
      ∑ E ∈ S.powerset,
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
          finiteSexticRow Q hgood j (primeSubsetGenerator P E) *
          ∑' z : O, finiteSexticRow Q hgood j z *
            W (‖eisEmbedding z‖ ^ 2 /
              (scale / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2)) := by
  exact tsum_masked_radial_dilations P hinj S (finiteSexticRow Q hgood j)
    (finiteSexticRow_mul Q hgood j) W scale
    (finiteSexticRow_radial_summable Q hcop hgood j W scale hscale)

theorem canonical_masked_radial_poisson
    {α ι : Type*} [DecidableEq α] [Fintype ι]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (S : Finset α)
    (Q : ι → Ideal O) [∀ i, (Q i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime Q))
    (hgood : ∀ i, lambda ∉ Q i)
    (hchar : ∀ i, ringChar (O ⧸ Q i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let c := finitePrimeModulus Q
    (∑' u : O, rowCoprimeMask P S u * finiteSexticRow Q hgood j u *
      W (‖eisEmbedding u‖ ^ 2 / scale)) =
      ∑ E ∈ S.powerset,
        let d := primeSubsetGenerator P E
        let reducedScale := scale / ‖eisEmbedding d‖ ^ 2
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
          finiteSexticRow Q hgood j d *
          ((reducedScale : ℂ) * canonicalNormalizedGauss Q hcop hgood j /
            (‖eisEmbedding c‖ : ℂ)) *
          ∑' h : O, star (finiteSexticRow Q hgood j h) *
            paperRadialFourier W
              (reducedScale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  dsimp only
  rw [canonical_masked_radial_dilations P hinj S Q hcop hgood j W scale hscale]
  apply Finset.sum_congr rfl
  intro E hE
  rw [canonical_radial_poisson_normalized Q hcop hgood hchar j hj0 hj6 W
    (scale / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2)
    (primeSubset_reducedScale_pos P E hscale)]
  ring

theorem canonical_masked_radial_poisson_collected
    {α ι : Type*} [DecidableEq α] [Fintype ι]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (S : Finset α)
    (Q : ι → Ideal O) [∀ i, (Q i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime Q))
    (hgood : ∀ i, lambda ∉ Q i)
    (hchar : ∀ i, ringChar (O ⧸ Q i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let c := finitePrimeModulus Q
    (∑' u : O, rowCoprimeMask P S u * finiteSexticRow Q hgood j u *
      W (‖eisEmbedding u‖ ^ 2 / scale)) =
      ((scale : ℂ) * canonicalNormalizedGauss Q hcop hgood j / (‖eisEmbedding c‖ : ℂ)) *
        ∑ E ∈ S.powerset,
          let d := primeSubsetGenerator P E
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
            finiteSexticRow Q hgood j d / (‖eisEmbedding d‖ ^ 2 : ℝ)) *
            ∑' h : O, star (finiteSexticRow Q hgood j h) *
              paperRadialFourier W
                (scale * ‖eisEmbedding h‖ ^ 2 /
                  (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding c‖ ^ 2)) := by
  dsimp only
  rw [canonical_masked_radial_poisson P hinj S Q hcop hgood hchar j hj0 hj6 W scale hscale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only
  have harg (h : O) :
      scale / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 * ‖eisEmbedding h‖ ^ 2 /
          ‖eisEmbedding (finitePrimeModulus Q)‖ ^ 2 =
      scale * ‖eisEmbedding h‖ ^ 2 /
        (‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 *
          ‖eisEmbedding (finitePrimeModulus Q)‖ ^ 2) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  simp_rw [harg]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end ActualEisensteinCubic

namespace ActualEisensteinCubic
open ConcreteTraceCRT EisensteinSchwartzPoisson

theorem finiteSquarefreeRow_pair_radial_summable
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S T : Finset ι)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    Summable (fun u : O =>
      (star (finiteSquarefreeRow P hgood S u) * finiteSquarefreeRow P hgood T u) *
        W (‖eisEmbedding u‖ ^ 2 / scale)) := by
  have hW : Summable (fun u : O => ‖W (‖eisEmbedding u‖ ^ 2 / scale)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W scale hscale)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun u => norm_nonneg _) _ hW
  intro u
  simp only [norm_mul, norm_star]
  calc
    ‖finiteSquarefreeRow P hgood S u‖ * ‖finiteSquarefreeRow P hgood T u‖ *
        ‖W (‖eisEmbedding u‖ ^ 2 / scale)‖ ≤
      1 * 1 * ‖W (‖eisEmbedding u‖ ^ 2 / scale)‖ := by
        gcongr
        · exact finiteSquarefreeRow_norm_le_one P hgood S u
        · exact finiteSquarefreeRow_norm_le_one P hgood T u
    _ = _ := by ring

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.ActiveGaussFactorization
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical
namespace ActualEisensteinCubic

theorem activeExponent_ne_zero {α : Type*} [DecidableEq α]
    (S T : Finset α) (i : activeSupport S T) : activeExponent S T i ≠ 0 := by
  unfold activeExponent
  split_ifs <;> decide

theorem activeExponent_lt_six {α : Type*} [DecidableEq α]
    (S T : Finset α) (i : activeSupport S T) : activeExponent S T i < 6 := by
  unfold activeExponent
  split_ifs <;> decide

theorem finiteSexticRow_activeSupport {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S T : Finset α) (u : O) :
    finiteSexticRow (activePrimes P S T) (fun i => hgood i.val) (activeExponent S T) u =
      star (finiteSquarefreeRow P hgood (S \ T) u) *
        finiteSquarefreeRow P hgood (T \ S) u := by
  classical
  have hd : Disjoint (S \ T) (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  have hpow5 (i : α) :
      (canonicalSextic (P i) (hgood i) ^ 5) (Ideal.Quotient.mk (P i) u) =
        star (canonicalSextic (P i) (hgood i) (Ideal.Quotient.mk (P i) u)) := by
    rw [MulChar.pow_apply' _ (by decide : (5 : ℕ) ≠ 0)]
    rw [canonicalSextic_conj_as_row_label]
    ring
  unfold finiteSexticRow activePrimes activeExponent
  let f : α → ℂ := fun i =>
    (canonicalSextic (P i) (hgood i) ^ (if i ∈ S \ T then 5 else 1))
      (Ideal.Quotient.mk (P i) u)
  change (∏ i : activeSupport S T, f i.val) = _
  rw [Finset.prod_coe_sort (s := activeSupport S T) (f := f)]
  change (∏ i ∈ (S \ T) ∪ (T \ S),
    (canonicalSextic (P i) (hgood i) ^ (if i ∈ S \ T then 5 else 1))
      (Ideal.Quotient.mk (P i) u)) = _
  rw [Finset.prod_union hd]
  simp only [finiteSquarefreeRow, star_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    rw [if_pos hi, hpow5]
  · apply Finset.prod_congr rfl
    intro i hi
    have hnot : i ∉ S \ T := fun h => Finset.disjoint_left.mp hd h hi
    rw [if_neg hnot, pow_one]

theorem finiteSquarefreeRow_pair_activeSupport {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S T : Finset α) (u : O) :
    star (finiteSquarefreeRow P hgood S u) * finiteSquarefreeRow P hgood T u =
      rowCoprimeMask P (S ∩ T) u *
        finiteSexticRow (activePrimes P S T) (fun i => hgood i.val)
          (activeExponent S T) u := by
  rw [finiteSexticRow_activeSupport P hgood S T u]
  have hk := finiteSquarefreeRow_pair_kernel P hgood S T u
  simpa only [mul_assoc] using hk

open ConcreteTraceCRT EisensteinSchwartzPoisson

end ActualEisensteinCubic

open scoped BigOperators Classical

namespace FiniteGaussPhase

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem canonicalProductGauss_constant_power {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ℕ) (hj : j ≠ 0) :
    canonicalProductGauss p hp hcop hgood (fun _ => j) =
      (∏ i, ∏ k ∈ Finset.univ.erase i,
        canonicalSextic (Ideal.span {p i}) (hgood i)
          (Ideal.Quotient.mk (Ideal.span {p i}) (p k))) ^ j *
        ∏ i, ConcreteBreveE.normalizedTraceGauss (p i) (hp i)
          (canonicalSextic (Ideal.span {p i}) (hgood i) ^ j) := by
  rw [canonicalProductGauss_cross_factors]
  simp only [MulChar.pow_apply' _ hj, Finset.prod_pow]

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem angularFactor_prod {ι : Type*} [Fintype ι] (p : ι → O) :
    angularFactor (∏ i, p i) = ∏ i, angularFactor (p i) := by
  unfold angularFactor
  rw [map_prod, norm_prod, Complex.ofReal_prod, Finset.prod_div_distrib]

theorem canonicalCrossFactor_pow_six {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) :
    canonicalCrossFactor p hgood ^ 6 = 1 := by
  unfold canonicalCrossFactor
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i _
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro k hk
  have hnot := prime_generator_not_mem_other p hcop i k
    (Ne.symm (Finset.mem_erase.mp hk).1)
  simpa only [map_pow, if_neg hnot] using
    (canonicalSextic_sixth_power_mask (Ideal.span {p i}) (hgood i) (p k))

theorem canonicalProductCoefficient_crt {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) :
    canonicalProductCoefficient p hp hcop hgood =
      canonicalCrossFactor p hgood ^ 2 *
        ∏ i, star (angularFactor (p i)) *
          ConcreteBreveE.normalizedTraceGauss (p i) (hp i)
            (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 2) := by
  rw [canonicalProductCoefficient, canonicalProductGauss_constant_power p hp hcop hgood 2
    (by decide), angularFactor_prod, star_prod, Finset.prod_mul_distrib]
  unfold canonicalCrossFactor
  ring

theorem product_moebius_eq_sign {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) :
    (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) =
      (-1 : ℂ) ^ Fintype.card ι := by
  have hinj : Function.Injective (fun i => Ideal.span {p i}) := by
    intro i k h
    by_contra hik
    have ht := (hcop hik).sup_eq
    rw [h, sup_idem] at ht
    exact (inferInstance : (Ideal.span {p k}).IsMaximal).ne_top ht
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  rw [span_finset_prod]
  simpa only [Finset.card_univ] using
    prime_product_moebius (fun i => Ideal.span {p i}) hprime hinj Finset.univ

theorem norm_angularFactor (a : O) (ha : a ≠ 0) : ‖angularFactor a‖ = 1 := by
  rw [angularFactor, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero ha))

end FiniteGaussPhase

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.CubicTrace
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

namespace GaussGeneratorTransport

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase

theorem canonicalNormalizedGauss_eq_principal {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) :
    canonicalNormalizedGauss P hcop hgood j =
      principalNormalizedGauss P hcop hgood j (finitePrimeModulus P)
        (span_finitePrimeModulus P) (finitePrimeModulus_ne_zero P) := rfl

theorem principalNormalizedGauss_eq_product {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) :
    principalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j (∏ i, p i)
      (span_finset_prod Finset.univ p) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) =
      canonicalProductGauss p hp hcop hgood j := rfl

theorem modulusUnit_spec {ι : Type*} [Fintype ι] (p : ι → O) :
    finitePrimeModulus (fun i => Ideal.span {p i}) = (modulusUnit p : O) * ∏ i, p i :=
  Classical.choose_spec (exists_modulus_unit p)

theorem canonicalNormalizedGauss_eq_product {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) :
    canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j =
      finiteSexticRow (fun i => Ideal.span {p i}) hgood j (modulusUnit p : O) *
        canonicalProductGauss p hp hcop hgood j := by
  rw [canonicalNormalizedGauss_eq_principal,
    principalNormalizedGauss_unit_change (fun i => Ideal.span {p i}) hcop hgood j
      (finitePrimeModulus (fun i => Ideal.span {p i})) (∏ i, p i)
      (span_finitePrimeModulus _) (span_finset_prod Finset.univ p)
      (finitePrimeModulus_ne_zero _) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
      (modulusUnit p) (modulusUnit_spec p), principalNormalizedGauss_eq_product]

theorem canonicalNormalizedGauss_frequency_transport {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (h : O) :
    canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
      star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j ((modulusUnit p : O) * h)) =
      canonicalProductGauss p hp hcop hgood j *
        star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) := by
  rw [canonicalNormalizedGauss_eq_product p hp hcop hgood j,
    finiteSexticRow_mul, star_mul]
  calc
    _ = (finiteSexticRow (fun i => Ideal.span {p i}) hgood j (modulusUnit p : O) *
          star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j (modulusUnit p : O))) *
        (canonicalProductGauss p hp hcop hgood j *
          star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h)) := by ring
    _ = _ := by rw [finiteSexticRow_unit_mul_star, one_mul]

theorem gauss_weighted_radial_sum_transport {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (F : ℝ → ℂ) :
    canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
      (∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
        F (‖eisEmbedding h‖ ^ 2)) =
      canonicalProductGauss p hp hcop hgood j *
        (∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
          F (‖eisEmbedding h‖ ^ 2)) := by
  rw [← tsum_mul_left, ← tsum_mul_left]
  calc
    _ = ∑' h : O, canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
        (star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j
          ((modulusUnit p : O) * h)) * F (‖eisEmbedding ((modulusUnit p : O) * h)‖ ^ 2)) :=
      ((modulusUnit p).mulLeft.tsum_eq _).symm
    _ = _ := by
      apply tsum_congr
      intro h
      rw [norm_eisEmbedding_unit_mul, ← mul_assoc,
        canonicalNormalizedGauss_frequency_transport p hp hcop hgood j, mul_assoc]

theorem gauss_weighted_finite_radial_sum_transport {ι κ : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ)
    (D : Finset κ) (a : κ → ℂ) (F : κ → ℝ → ℂ) :
    canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
      (∑ k ∈ D, a k * ∑' h : O,
        star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
          F k (‖eisEmbedding h‖ ^ 2)) =
      canonicalProductGauss p hp hcop hgood j *
        (∑ k ∈ D, a k * ∑' h : O,
          star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
            F k (‖eisEmbedding h‖ ^ 2)) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = a k * (canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
        ∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) *
          F k (‖eisEmbedding h‖ ^ 2)) := by ring
    _ = _ := by rw [gauss_weighted_radial_sum_transport p hp hcop hgood j]; ring

theorem finitePrimeModulus_norm_eq_product {ι : Type*} [Fintype ι] (p : ι → O) :
    ‖eisEmbedding (finitePrimeModulus (fun i => Ideal.span {p i}))‖ =
      ‖eisEmbedding (∏ i, p i)‖ := by
  rw [modulusUnit_spec p, norm_eisEmbedding_unit_mul]

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase

end GaussGeneratorTransport

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.MixedConversion
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical

open scoped BigOperators Classical

namespace MixedGaussConversion
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase

theorem norm_localGauss (p : O) (hp : p ≠ 0) [ (Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (j : ℕ) (hj0 : j ≠ 0) (hj6 : j < 6) : ‖localGauss p hp hg j‖ = 1 := by
  let q : Unit → O := fun _ => p
  have hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {q i})) := by
    intro i k hik
    exact (hik (Subsingleton.elim i k)).elim
  have h := norm_canonicalProductGauss q (fun _ => hp) hcop (fun _ => hg)
    (fun _ => hchar) (fun _ => j) (fun _ => hj0) (fun _ => hj6)
  rw [canonicalProductGauss_constant_power q (fun _ => hp) hcop (fun _ => hg) j hj0] at h
  simpa only [q, Fintype.prod_unique, Finset.univ_unique, Finset.erase_singleton,
    Finset.prod_empty, Finset.prod_singleton, one_pow, one_mul, localGauss] using h

theorem canonicalSextic_fifth_eq_inverse (p : O) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) :
    canonicalSextic (Ideal.span {p}) hg ^ 5 = (canonicalSextic (Ideal.span {p}) hg)⁻¹ := by
  apply DFunLike.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [MulChar.pow_apply' _ (by decide : (5 : ℕ) ≠ 0), ← MulChar.star_apply',
    canonicalSextic_conj_as_row_label]
  ring

theorem localGauss_five_eq (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) :
    localGauss p hp hg 5 = breveGammaMinus1 (Ideal.span {p}) hg p rfl hp := by
  rw [localGauss, canonicalSextic_fifth_eq_inverse]
  rfl

theorem local_sign_conversion (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hprimary : lambda ^ 2 ∣ p - 1) :
    (-localGauss p hp hg 1) * star (localG p hp hg) = star (localCoefficient p hp hg) ∧
    (-localGauss p hp hg 5) * localG p hp hg =
      canonicalSextic (Ideal.span {p}) hg (Ideal.Quotient.mk (Ideal.span {p}) (-1 : O)) *
        localCoefficient p hp hg := by
  have h := first_poisson_prime_sign_pairing (Ideal.span {p}) hg hchar p rfl hp hprimary 1
  dsimp only at h
  simp only [map_one, mul_one, inv_one] at h
  constructor
  · simpa only [localGauss, localG, localCoefficient, angularFactor, pow_one,
      ConcreteBreveE.normalizedTraceGauss, breveGamma1, breveGamma2, star_mul, star_star,
      mul_comm] using h.2.2.1
  · rw [localGauss_five_eq]
    exact h.2.1

theorem norm_localG (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hprimary : lambda ^ 2 ∣ p - 1) : ‖localG p hp hg‖ = 1 := by
  have h := congrArg norm (local_sign_conversion p hp hg hchar hprimary).1
  simp only [norm_mul, norm_neg, norm_star, localCoefficient] at h
  rw [norm_localGauss p hp hg hchar 1 (by decide) (by decide), one_mul,
    norm_angularFactor p hp,
    norm_localGauss p hp hg hchar 2 (by decide) (by decide), one_mul] at h
  exact h

theorem neg_localGauss_eq_converted (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hprimary : lambda ^ 2 ∣ p - 1) (inverse : Bool) :
    -localGauss p hp hg (if inverse then 5 else 1) = convertedLocal p hp hg inverse := by
  have hG : localG p hp hg ≠ 0 := by
    intro hz
    have hn := norm_localG p hp hg hchar hprimary
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  cases inverse
  · exact (eq_div_iff (star_ne_zero.mpr hG)).mpr
      (local_sign_conversion p hp hg hchar hprimary).1
  · exact (eq_div_iff hG).mpr (local_sign_conversion p hp hg hchar hprimary).2

theorem moebius_mixed_gauss_conversion {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) (inverse : ι → Bool) :
    (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
      canonicalProductGauss p hp hcop hgood (fun i => if inverse i then 5 else 1) =
      (∏ i, ∏ k ∈ Finset.univ.erase i,
        (canonicalSextic (Ideal.span {p i}) (hgood i) ^ (if inverse i then 5 else 1))
          (Ideal.Quotient.mk (Ideal.span {p i}) (p k))) *
        ∏ i, convertedLocal (p i) (hp i) (hgood i) (inverse i) := by
  rw [product_moebius_eq_sign p hcop, canonicalProductGauss_cross_factors]
  have hprod : (-1 : ℂ) ^ Fintype.card ι *
      (∏ i, localGauss (p i) (hp i) (hgood i) (if inverse i then 5 else 1)) =
      ∏ i, convertedLocal (p i) (hp i) (hgood i) (inverse i) := by
    rw [← Finset.card_univ, ← Finset.prod_neg]
    apply Finset.prod_congr rfl
    intro i _
    exact neg_localGauss_eq_converted (p i) (hp i) (hgood i) (hchar i) (hprimary i) (inverse i)
  calc
    _ = (∏ i, ∏ k ∈ Finset.univ.erase i,
          (canonicalSextic (Ideal.span {p i}) (hgood i) ^ (if inverse i then 5 else 1))
            (Ideal.Quotient.mk (Ideal.span {p i}) (p k))) *
        ((-1 : ℂ) ^ Fintype.card ι *
          ∏ i, localGauss (p i) (hp i) (hgood i) (if inverse i then 5 else 1)) := by
      unfold localGauss
      ring
    _ = _ := by rw [hprod]

end MixedGaussConversion

open scoped BigOperators Classical SchwartzMap ContDiff

namespace GaussGeneratorTransport
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase
open MixedGaussConversion

theorem pair_moebius_eq_active
    {ι : Type*} [DecidableEq ι] (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (S T : Finset ι) :
    (UniqueFactorizationMonoid.moebius (∏ i ∈ S, Ideal.span {p i}) : ℂ) *
      (UniqueFactorizationMonoid.moebius (∏ i ∈ T, Ideal.span {p i}) : ℂ) =
      (UniqueFactorizationMonoid.moebius
        (Ideal.span {∏ i : activeSupport S T, p i.val}) : ℂ) := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have hcop := activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T
  rw [prime_product_moebius (fun i => Ideal.span {p i}) hprime hinj S,
    prime_product_moebius (fun i => Ideal.span {p i}) hprime hinj T,
    product_moebius_eq_sign (fun i : activeSupport S T => p i.val) hcop, ← pow_add]
  have hd : Disjoint (S \ T) (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  have ha : Fintype.card (activeSupport S T) = (S \ T).card + (T \ S).card := by
    rw [Fintype.card_coe, activeSupport, Finset.card_union_of_disjoint hd]
  have hs := Finset.card_sdiff_add_card_inter S T
  have ht := Finset.card_sdiff_add_card_inter T S
  rw [Finset.inter_comm T S] at ht
  have hcard : S.card + T.card = Fintype.card (activeSupport S T) + 2 * (S ∩ T).card := by omega
  rw [hcard, pow_add, pow_mul]
  norm_num

end GaussGeneratorTransport

open scoped BigOperators Classical SchwartzMap ContDiff

open MeasureTheory Set
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SquarePhaseFactorization
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators

namespace ActualEisensteinCubic

theorem canonicalSextic_sq_reciprocity_primary
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    (canonicalSextic P hPgood (Ideal.Quotient.mk P q)) ^ 2 =
      (canonicalSextic Q hQgood (Ideal.Quotient.mk Q p)) ^ 2 := by
  have hP2 : (canonicalSextic P hPgood (Ideal.Quotient.mk P q)) ^ 2 =
      ConcreteTraceCRT.eisEmbedding (cubicChar P hPgood (Ideal.Quotient.mk P q)) := by
    rw [← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), canonicalSextic_pow_two]
    rfl
  have hQ2 : (canonicalSextic Q hQgood (Ideal.Quotient.mk Q p)) ^ 2 =
      ConcreteTraceCRT.eisEmbedding (cubicChar Q hQgood (Ideal.Quotient.mk Q p)) := by
    rw [← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), canonicalSextic_pow_two]
    rfl
  rw [hP2, hQ2, cubic_reciprocity_primary P Q hPgood hQgood p q hP hQ hpprimary hqprimary]

theorem canonicalSextic_four_prod_eq_fixed_two
    {ι : Type*} (s : Finset ι) (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (p : ι → O)
    (hP : ∀ i ∈ s, P i = Ideal.span {p i})
    (hprimary : ∀ i ∈ s, lambda ^ 2 ∣ p i - 1) :
    (∏ i ∈ s, canonicalSextic (P i) (hgood i) (Ideal.Quotient.mk (P i) (4 : O))) =
      ConcreteTraceCRT.eisEmbedding (cubicChar cubicTwoIdeal cubicTwoIdeal_good
        (Ideal.Quotient.mk cubicTwoIdeal (∏ i ∈ s, p i))) := by
  simp only [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact canonicalSextic_four_eq_fixed_two (P i) (hgood i) (p i) (hP i hi) (hprimary i hi)

end ActualEisensteinCubic

open scoped BigOperators Classical

namespace QuadraticGaussRay

open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates

open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates

theorem fixed_two_mk_eq_residue_lift (c : O) :
    Ideal.Quotient.mk cubicTwoIdeal c =
      Ideal.Quotient.mk cubicTwoIdeal (lift (residue c)) := by
  obtain ⟨z, hz⟩ := congr_mod_four_of_residue_eq (residue_lift (residue c)).symm
  apply Ideal.Quotient.eq.mpr
  rw [cubicTwoIdeal, Ideal.mem_span_singleton]
  refine ⟨(-2 : O) * z, ?_⟩
  calc
    c - lift (residue c) = 4 * z := hz
    _ = (-2 : O) * (-2 * z) := by ring

theorem canonicalProductG_eq_fixedGValue
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductG p hp hcop hgood = fixedGValue (residue (∏ i, p i)) := by
  rw [canonicalProductG,
    canonicalSextic_four_prod_eq_fixed_two Finset.univ (fun i => Ideal.span {p i}) hgood p
      (fun i _ => rfl) (fun i _ => hprimary i),
    canonicalProductGauss_three_eq_rayValue p hp hcop hgood hchar,
    fixed_two_mk_eq_residue_lift]
  rfl

theorem canonicalProductG_eq_fixed_quotient
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductG p hp hcop hgood =
      fixedGQuotientValue (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i, p i)) :=
  canonicalProductG_eq_fixedGValue p hp hcop hgood hchar hprimary

end QuadraticGaussRay

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.CrossSeparation
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators

open scoped BigOperators Classical

namespace MixedCrossSeparation

open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion

private theorem ordered_cross_partition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ι → ℂ) (l : ι → ℂ) (A B : Finset ι)
    (hd : Disjoint A B) (hu : A ∪ B = Finset.univ) :
    (∏ i, ((∏ k ∈ Finset.univ.erase i, x i k ^ (if i ∈ A then 5 else 1)) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ 5) * l i) *
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k) * l i) *
      (∏ i ∈ A, ∏ k ∈ B, x i k ^ 5 * x k i) := by
  have hA (i : ι) (hi : i ∈ A) :
      (∏ k ∈ Finset.univ.erase i, x i k ^ (if i ∈ A then 5 else 1)) =
        (∏ k ∈ A.erase i, x i k ^ 5) * (∏ k ∈ B, x i k ^ 5) := by
    have hn : i ∉ B := fun hb => Finset.disjoint_left.mp hd hi hb
    have he : Finset.univ.erase i = A.erase i ∪ B := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk]
    rw [he, if_pos hi, Finset.prod_union (hd.mono_left (Finset.erase_subset _ _))]
  have hB (i : ι) (hi : i ∈ B) :
      (∏ k ∈ Finset.univ.erase i, x i k ^ (if i ∈ A then 5 else 1)) =
        (∏ k ∈ B.erase i, x i k) * (∏ k ∈ A, x i k) := by
    have hn : i ∉ A := fun ha => Finset.disjoint_left.mp hd ha hi
    have he : Finset.univ.erase i = B.erase i ∪ A := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk, or_comm]
    rw [he, if_neg hn, Finset.prod_union (hd.symm.mono_left (Finset.erase_subset _ _))]
    simp only [pow_one]
  have hpA : (∏ i ∈ A, ((∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ A then 5 else 1)) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ 5) * l i) *
        (∏ i ∈ A, ∏ k ∈ B, x i k ^ 5) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hA i hi]
    ring
  have hpB : (∏ i ∈ B, ((∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ A then 5 else 1)) * l i)) =
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k) * l i) *
        (∏ i ∈ B, ∏ k ∈ A, x i k) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hB i hi]
    ring
  calc
    _ = (∏ i ∈ A, ((∏ k ∈ Finset.univ.erase i,
            x i k ^ (if i ∈ A then 5 else 1)) * l i)) *
        (∏ i ∈ B, ((∏ k ∈ Finset.univ.erase i,
            x i k ^ (if i ∈ A then 5 else 1)) * l i)) := by
      rw [← Finset.prod_union hd, hu]
    _ = _ := by
      rw [hpA, hpB]
      rw [Finset.prod_comm (s := B) (t := A)]
      simp only [Finset.prod_mul_distrib]
      ring

theorem mixed_cross_eq_quadratic {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (i k : ι)
    (hpi : lambda ^ 2 ∣ p i - 1) (hpk : lambda ^ 2 ∣ p k - 1) :
    crossSymbol p hg i k ^ 5 * crossSymbol p hg k i =
      crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3 := by
  have hs : crossSymbol p hg i k ^ 2 = crossSymbol p hg k i ^ 2 :=
    canonicalSextic_sq_reciprocity_primary
      (Ideal.span {p i}) (Ideal.span {p k}) (hg i) (hg k)
      (p i) (p k) rfl rfl hpi hpk
  calc
    _ = crossSymbol p hg i k ^ 3 * crossSymbol p hg i k ^ 2 * crossSymbol p hg k i := by ring
    _ = _ := by rw [hs]; ring

theorem mixed_converted_gauss_separation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (inverse : ι → Bool)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    (∏ i, ∏ k ∈ Finset.univ.erase i,
      (canonicalSextic (Ideal.span {p i}) (hg i) ^ (if inverse i then 5 else 1))
        (Ideal.Quotient.mk (Ideal.span {p i}) (p k))) *
      (∏ i, convertedLocal (p i) (hp i) (hg i) (inverse i)) =
    convertedColumnBlock p hp hg (Finset.univ.filter fun i => inverse i = true) true *
      convertedColumnBlock p hp hg (Finset.univ.filter fun i => inverse i = false) false *
      quadraticCrossPhase p hg (Finset.univ.filter fun i => inverse i = true)
        (Finset.univ.filter fun i => inverse i = false) := by
  let A := Finset.univ.filter (fun i => inverse i = true)
  let B := Finset.univ.filter (fun i => inverse i = false)
  have hA (i : ι) : i ∈ A ↔ inverse i = true := by simp [A]
  have hB (i : ι) : i ∈ B ↔ inverse i = false := by simp [B]
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have ht := (hA i).mp hi
    have hf := (hB i).mp hj
    rw [ht] at hf
    contradiction
  have hu : A ∪ B = Finset.univ := by
    ext i
    simp only [Finset.mem_union, hA, hB, Finset.mem_univ, iff_true]
    cases inverse i <;> simp
  have hpow (i k : ι) :
      (canonicalSextic (Ideal.span {p i}) (hg i) ^ (if inverse i then 5 else 1))
        (Ideal.Quotient.mk (Ideal.span {p i}) (p k)) =
      crossSymbol p hg i k ^ (if i ∈ A then 5 else 1) := by
    rw [MulChar.pow_apply' _ (by cases inverse i <;> decide)]
    simp only [hA,  crossSymbol]
  simp_rw [hpow]
  rw [← Finset.prod_mul_distrib,
    ordered_cross_partition (crossSymbol p hg)
      (fun i => convertedLocal (p i) (hp i) (hg i) (inverse i)) A B hd hu]
  have hn : (∏ i ∈ A, (∏ k ∈ A.erase i, crossSymbol p hg i k ^ 5) *
      convertedLocal (p i) (hp i) (hg i) (inverse i)) = convertedColumnBlock p hp hg A true := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [(hA i).mp hi,   ↓reduceIte]
  have hp' : (∏ i ∈ B, (∏ k ∈ B.erase i, crossSymbol p hg i k) *
      convertedLocal (p i) (hp i) (hg i) (inverse i)) = convertedColumnBlock p hp hg B false := by
    unfold convertedColumnBlock
    simp only [Bool.false_eq_true, ↓reduceIte, pow_one]
    apply Finset.prod_congr rfl
    intro i hi
    rw [(hB i).mp hi]
  have hc : (∏ i ∈ A, ∏ k ∈ B, crossSymbol p hg i k ^ 5 * crossSymbol p hg k i) =
      quadraticCrossPhase p hg A B := by
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro k hk
    exact mixed_cross_eq_quadratic p hg i k (hprimary i) (hprimary k)
  rw [hn, hp', hc]

theorem activeConvertedGauss_separated
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) :
    let q : activeSupport S T → O := fun i => p i.val
    let hq : ∀ i, q i ≠ 0 := fun i => hp i.val
    let hgood : ∀ i, lambda ∉ Ideal.span {q i} := fun i => hg i.val
    let A : Finset (activeSupport S T) := Finset.univ.filter fun i => i.val ∈ S \ T
    let B : Finset (activeSupport S T) := Finset.univ.filter fun i => i.val ∉ S \ T
    GaussGeneratorTransport.activeConvertedGauss p hp hg S T =
      convertedColumnBlock q hq hgood A true * convertedColumnBlock q hq hgood B false *
        quadraticCrossPhase q hgood A B := by
  dsimp only
  have h := mixed_converted_gauss_separation (fun i : activeSupport S T => p i.val)
    (fun i => hp i.val) (fun i => hg i.val) (fun i => decide (i.val ∈ S \ T))
    (fun i => hprimary i.val)
  simp only [GaussGeneratorTransport.activeConvertedGauss, activeExponent,
    decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢
  convert (preTransparency := .instances) h using 1 ; congr 2
  funext i
  apply Finset.prod_congr
  · ext k; simp
  · intro k hk; rfl

open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion
open QuadraticGaussRay ActualEisensteinCoordinates

end MixedCrossSeparation

open scoped BigOperators Classical

namespace CoprimeMobiusExtension

theorem double_sum_disjoint_expansion {ι : Type*} [DecidableEq ι]
    (B : Finset ι) (Z : Finset ι → Finset ι → ℂ) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset, if Disjoint S T then Z S T else 0) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        ∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
          if D ⊆ S ∧ D ⊆ T then Z S T else 0 := by
  have hp (S T : Finset ι) (hS : S ∈ B.powerset) (hT : T ∈ B.powerset) :
      (if Disjoint S T then Z S T else 0) =
        ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
          if D ⊆ S ∧ D ⊆ T then Z S T else 0 := by
    calc
      _ = (if Disjoint S T then (1 : ℂ) else 0) * Z S T := by split_ifs <;> simp
      _ = (∑ D ∈ B.powerset,
          if D ⊆ S ∧ D ⊆ T then (-1 : ℂ) ^ D.card else 0) * Z S T := by
        rw [disjoint_indicator_expansion B S T (Finset.mem_powerset.mp hS)
          (Finset.mem_powerset.mp hT)]
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro D hD
        split_ifs <;> simp
  calc
    _ = ∑ S ∈ B.powerset, ∑ T ∈ B.powerset, ∑ D ∈ B.powerset,
        (-1 : ℂ) ^ D.card * if D ⊆ S ∧ D ⊆ T then Z S T else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      exact Finset.sum_congr rfl (fun T hT => hp S T hS hT)
    _ = _ := by
      simp_rw [Finset.mul_sum]
      calc
        _ = ∑ S ∈ B.powerset, ∑ D ∈ B.powerset, ∑ T ∈ B.powerset,
            (-1 : ℂ) ^ D.card * if D ⊆ S ∧ D ⊆ T then Z S T else 0 := by
          apply Finset.sum_congr rfl
          intro S hS
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

theorem sum_supersets {ι : Type*} [DecidableEq ι]
    (B D : Finset ι) (hD : D ⊆ B) (f : Finset ι → ℂ) :
    (∑ S ∈ B.powerset, if D ⊆ S then f S else 0) =
      ∑ U ∈ (B \ D).powerset, f (D ∪ U) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun S _ => S \ D) ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
    exact Finset.sdiff_subset_sdiff hS.1 (Finset.Subset.refl _)
  · intro S hS T hT heq
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS hT
    have he := congrArg (fun U => D ∪ U) heq
    simpa [Finset.union_sdiff_of_subset hS.2, Finset.union_sdiff_of_subset hT.2] using he
  · intro U hU
    have hUB : U ⊆ B \ D := Finset.mem_powerset.mp hU
    refine ⟨D ∪ U, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.union_subset hD (hUB.trans Finset.sdiff_subset), Finset.subset_union_left⟩
    · apply Finset.union_sdiff_cancel_left
      exact (Finset.disjoint_of_subset_right hUB disjoint_sdiff_self_right)
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS
    rw [Finset.union_sdiff_of_subset hS.2]

theorem double_sum_disjoint_reindexed {ι : Type*} [DecidableEq ι]
    (B : Finset ι) (Z : Finset ι → Finset ι → ℂ) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset, if Disjoint S T then Z S T else 0) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        ∑ U ∈ (B \ D).powerset, ∑ V ∈ (B \ D).powerset, Z (D ∪ U) (D ∪ V) := by
  rw [double_sum_disjoint_expansion]
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  have hDB := Finset.mem_powerset.mp hD
  calc
    _ = ∑ S ∈ B.powerset, if D ⊆ S then
          (∑ T ∈ B.powerset, if D ⊆ T then Z S T else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      by_cases hh : D ⊆ S <;> simp [hh]
    _ = _ := by
      rw [sum_supersets B D hDB]
      apply Finset.sum_congr rfl
      intro U hU
      exact sum_supersets B D hDB (Z (D ∪ U))

open ActualEisensteinCubic

end CoprimeMobiusExtension

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.CompletedExpansion
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical

namespace FiniteRayExpansion

variable {R : Type*} [CommRing R] [Fintype R]

attribute [local instance] OAI.FiniteRayExpansion.instFintypeMulCharComplex_definitions
theorem zeroExtendUnits_fourier (f : Rˣ → ℂ) (r : R) :
    zeroExtendUnits f r = ∑ χ : MulChar R ℂ, unitFourierCoeff f χ * χ r := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    rw [zeroExtendUnits_unit]
    exact (unit_fourier_inversion f u).symm
  · rw [zeroExtendUnits_nonunit f r hr]
    simp only [MulChar.map_nonunit _ hr, mul_zero, Finset.sum_const_zero]

end FiniteRayExpansion

open scoped BigOperators Classical

namespace RayFourExpansion
open ActualEisensteinCubic ConcreteTraceCRT ActualEisensteinCoordinates QuadraticGaussRay
open FiniteRayExpansion

theorem phase_expansion (f : RayRing → ℂ) (a : O) :
    rayMask a * f (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a) =
      ∑ χ : RayCharacter, phaseCoeff f χ * rayCharacter χ a := by
  rw [rayMask, ← zeroExtendUnits_restrict]
  exact zeroExtendUnits_fourier _ _

theorem fixedG_character_expansion (a : O) :
    rayMask a * fixedGQuotientValue (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a) =
      ∑ χ : RayCharacter, gCoeff χ * rayCharacter χ a := phase_expansion _ a

end RayFourExpansion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.RayCharacters
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical

namespace RayFourExpansion
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase QuadraticGaussRay
open ActualEisensteinCoordinates MixedCrossSeparation

theorem canonicalProductG_character_expansion
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductG p hp hcop hgood =
      ∑ χ : RayCharacter, gCoeff χ * rayCharacter χ (∏ i, p i) := by
  rw [canonicalProductG_eq_fixed_quotient p hp hcop hgood hchar hprimary]
  have h := fixedG_character_expansion (∏ i, p i)
  rw [rayMask_prime_product p hchar Finset.univ, one_mul] at h
  exact h

theorem quadraticCrossPhase_character_expansion
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (A B : Finset ι) (hd : Disjoint A B) :
    quadraticCrossPhase p hg A B =
      ∑ χ : RayCharacter, ∑ η : RayCharacter,
        crossCoeff χ η * rayCharacter χ (∏ i ∈ A, p i) *
          rayCharacter η (∏ i ∈ B, p i) := by
  rw [quadraticCrossPhase_eq_rayPair p hp hcop hg hchar A B hd]
  have h := quadraticRayPair_character_expansion (∏ i ∈ A, p i) (∏ i ∈ B, p i)
  rw [rayMask_prime_product p hchar A, rayMask_prime_product p hchar B, one_mul, one_mul] at h
  exact h

end RayFourExpansion

namespace MixedCrossSeparation
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion
open QuadraticGaussRay ActualEisensteinCoordinates GaussGeneratorTransport

theorem convertedColumnBlock_image
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (e : κ → ι) (he : Function.Injective e)
    (A : Finset κ) (inverse : Bool) :
    convertedColumnBlock (fun i => p (e i)) (fun i => hp (e i)) (fun i => hg (e i)) A inverse =
      convertedColumnBlock p hp hg (A.image e) inverse := by
  unfold convertedColumnBlock
  rw [Finset.prod_image (fun a ha b hb hab => he hab)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.image_erase he A i, Finset.prod_image (fun a ha b hb hab => he hab)]
  rfl

theorem quadraticCrossPhase_image
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (e : κ → ι) (he : Function.Injective e)
    (A B : Finset κ) :
    quadraticCrossPhase (fun i => p (e i)) (fun i => hg (e i)) A B =
      quadraticCrossPhase p hg (A.image e) (B.image e) := by
  unfold quadraticCrossPhase
  rw [Finset.prod_image (fun a ha b hb hab => he hab)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.prod_image (fun a ha b hb hab => he hab)]
  rfl

private theorem negative_active_image {ι : Type*} [DecidableEq ι] (S T : Finset ι) :
    (Finset.univ.filter (fun i : activeSupport S T => i.val ∈ S \ T)).image Subtype.val = S \ T := by
  ext i
  constructor
  · intro hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp ha).2
  · intro hi
    exact Finset.mem_image.mpr ⟨⟨i, Finset.mem_union_left _ hi⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩

private theorem positive_active_image {ι : Type*} [DecidableEq ι] (S T : Finset ι) :
    (Finset.univ.filter (fun i : activeSupport S T => i.val ∉ S \ T)).image Subtype.val = T \ S := by
  ext i
  constructor
  · intro hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    have hm := a.property
    rcases Finset.mem_union.mp hm with hleft | hright
    · exact ((Finset.mem_filter.mp ha).2 hleft).elim
    · exact hright
  · intro hi
    have hn : i ∉ S \ T := fun h => (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp h).1
    exact Finset.mem_image.mpr ⟨⟨i, Finset.mem_union_right _ hi⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩, rfl⟩

theorem activeConvertedGauss_eq_columnBlocks
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) :
    activeConvertedGauss p hp hg S T =
      convertedColumnBlock p hp hg (S \ T) true *
        convertedColumnBlock p hp hg (T \ S) false *
          quadraticCrossPhase p hg (S \ T) (T \ S) := by
  rw [activeConvertedGauss_separated p hp hg hprimary S T]
  rw [convertedColumnBlock_image p hp hg Subtype.val Subtype.val_injective,
    convertedColumnBlock_image p hp hg Subtype.val Subtype.val_injective,
    quadraticCrossPhase_image p hg Subtype.val Subtype.val_injective,
    negative_active_image, positive_active_image]

end MixedCrossSeparation

namespace FirstCauchyArithmetic

section
open ActualEisensteinCubic CoprimeMobiusExtension

theorem supportMobius_sq {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P) (S : Finset ι) :
    supportMobius P S * supportMobius P S = 1 := by
  rw [supportMobius, prime_product_moebius P hprime hinj, ← mul_pow]
  norm_num

theorem star_supportMobius {ι : Type*} (P : ι → Ideal O) (S : Finset ι) :
    star (supportMobius P S) = supportMobius P S := by
  simp [supportMobius]

end

open ActualEisensteinCubic ConcretePrimeRowBridge

theorem family_prime_dvd_product_iff {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (S : Finset ι) (i : ι) :
    P i ∣ ∏ j ∈ S, P j ↔ i ∈ S := by
  constructor
  · intro h
    obtain ⟨j, hj, hd⟩ := ((family_prime P i).dvd_finsetProd_iff P).mp h
    have he : P i = P j := associated_iff_eq.mp
      ((family_prime P i).associated_of_dvd (family_prime P j) hd)
    exact hinj he ▸ hj
  · exact fun hi => Finset.dvd_prod_of_mem P hi

theorem family_product_injective {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) : Function.Injective (fun S : Finset ι => ∏ i ∈ S, P i) := by
  intro S T h
  change (∏ i ∈ S, P i) = (∏ i ∈ T, P i) at h
  ext i
  rw [← family_prime_dvd_product_iff P hinj S i, h, family_prime_dvd_product_iff P hinj T i]

end FirstCauchyArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.CoefficientCancellation
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical

namespace MixedCrossSeparation
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion

theorem norm_localCoefficient (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    ‖localCoefficient p hp hg‖ = 1 := by
  rw [localCoefficient, norm_mul, norm_star, norm_angularFactor p hp,
    norm_localGauss p hp hg hc 2 (by decide) (by decide), one_mul]

theorem local_coefficient_cancel (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hpr : lambda ^ 2 ∣ p - 1) :
    localCoefficient p hp hg * convertedLocal p hp hg false = localG p hp hg ∧
      star (localCoefficient p hp hg) * convertedLocal p hp hg true =
        canonicalSextic (Ideal.span {p}) hg (Ideal.Quotient.mk (Ideal.span {p}) (-1 : O)) *
          star (localG p hp hg) := by
  have hA : localCoefficient p hp hg * star (localCoefficient p hp hg) = 1 := by
    rw [← starRingEnd_apply, Complex.mul_conj', norm_localCoefficient p hp hg hc]
    norm_num
  have hG : localG p hp hg * star (localG p hp hg) = 1 := by
    rw [← starRingEnd_apply, Complex.mul_conj', norm_localG p hp hg hc hpr]
    norm_num
  have hGn : localG p hp hg ≠ 0 := by
    intro h
    simp [h] at hG
  have hGsn := star_ne_zero.mpr hGn
  constructor
  · simp only [convertedLocal, Bool.false_eq_true, ↓reduceIte]
    rw [← mul_div_assoc]
    apply (div_eq_iff hGsn).mpr
    rw [hA, hG]
  · simp only [convertedLocal, ↓reduceIte]
    rw [← mul_div_assoc]
    apply (div_eq_iff hGn).mpr
    calc
      _ = canonicalSextic (Ideal.span {p}) hg (Ideal.Quotient.mk (Ideal.span {p}) (-1 : O)) *
          (localCoefficient p hp hg * star (localCoefficient p hp hg)) := by ring
      _ = _ := by
        rw [hA]
        calc
          _ = canonicalSextic (Ideal.span {p}) hg (Ideal.Quotient.mk (Ideal.span {p}) (-1 : O)) *
              (localG p hp hg * star (localG p hp hg)) := by rw [hG]
          _ = _ := by ring

theorem canonicalProductG_crt {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) :
    canonicalProductG p hp hcop hg = canonicalCrossFactor p hg ^ 3 *
      ∏ i, localG (p i) (hp i) (hg i) := by
  rw [canonicalProductG, canonicalProductGauss_constant_power p hp hcop hg 3 (by decide)]
  change (∏ i, canonicalSextic (Ideal.span {p i}) (hg i)
      (Ideal.Quotient.mk (Ideal.span {p i}) (4 : O)))⁻¹ *
      (canonicalCrossFactor p hg ^ 3 * ∏ i, localGauss (p i) (hp i) (hg i) 3) = _
  simp only [localG, breveLocalG, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  change (∏ i, canonicalSextic (Ideal.span {p i}) (hg i)
      (Ideal.Quotient.mk (Ideal.span {p i}) (4 : O)))⁻¹ *
      (canonicalCrossFactor p hg ^ 3 * ∏ i, localGauss (p i) (hp i) (hg i) 3) =
    canonicalCrossFactor p hg ^ 3 *
      ((∏ i, canonicalSextic (Ideal.span {p i}) (hg i)
        (Ideal.Quotient.mk (Ideal.span {p i}) (4 : O)))⁻¹ *
        ∏ i, localGauss (p i) (hp i) (hg i) 3)
  ring

theorem convertedColumnBlock_univ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (b : Bool) :
    convertedColumnBlock p hp hg Finset.univ b =
      canonicalCrossFactor p hg ^ (if b then 5 else 1) *
        ∏ i, convertedLocal (p i) (hp i) (hg i) b := by
  simp only [convertedColumnBlock, Finset.prod_mul_distrib, ← Finset.prod_pow,
    canonicalCrossFactor, crossSymbol]
  congr 2
  funext i
  congr 1
  ext k
  simp

theorem coefficient_cancel_univ_false {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductCoefficient p hp hcop hg * convertedColumnBlock p hp hg Finset.univ false =
      canonicalProductG p hp hcop hg := by
  rw [canonicalProductCoefficient_crt, convertedColumnBlock_univ, canonicalProductG_crt]
  change (canonicalCrossFactor p hg ^ 2 * ∏ i, localCoefficient (p i) (hp i) (hg i)) *
      (canonicalCrossFactor p hg ^ 1 * ∏ i, convertedLocal (p i) (hp i) (hg i) false) = _
  calc
    _ = canonicalCrossFactor p hg ^ 3 * ∏ i,
        localCoefficient (p i) (hp i) (hg i) * convertedLocal (p i) (hp i) (hg i) false := by
      rw [Finset.prod_mul_distrib]
      ring
    _ = _ := by
      congr 1
      exact Finset.prod_congr rfl (fun i _ => (local_coefficient_cancel (p i) (hp i) (hg i) (hc i) (hpr i)).1)

theorem coefficient_cancel_univ_true {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) :
    star (canonicalProductCoefficient p hp hcop hg) * convertedColumnBlock p hp hg Finset.univ true =
      (∏ i, canonicalSextic (Ideal.span {p i}) (hg i)
        (Ideal.Quotient.mk (Ideal.span {p i}) (-1 : O))) * star (canonicalProductG p hp hcop hg) := by
  let C := canonicalCrossFactor p hg
  have hC6 : C ^ 6 = 1 := canonicalCrossFactor_pow_six p hcop hg
  have hCn : ‖C‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hC6 (by decide)
  have hCC : C * star C = 1 := by
    rw [← starRingEnd_apply, Complex.mul_conj', hCn]
    norm_num
  have hC3 : star C ^ 3 = C ^ 3 := by
    have hh : (C ^ 3) ^ 2 = 1 := by simpa only [← pow_mul] using hC6
    rw [← star_pow]
    rcases (sq_eq_one_iff).mp hh with h | h <;> simp [h]
  rw [canonicalProductCoefficient_crt, convertedColumnBlock_univ, canonicalProductG_crt]
  change star (C ^ 2 * ∏ i, localCoefficient (p i) (hp i) (hg i)) *
      (C ^ 5 * ∏ i, convertedLocal (p i) (hp i) (hg i) true) =
        _ * star (C ^ 3 * ∏ i, localG (p i) (hp i) (hg i))
  simp only [star_mul, star_pow, star_prod, hC3]
  calc
    _ = (C * star C) ^ 2 * C ^ 3 * ∏ i,
        star (localCoefficient (p i) (hp i) (hg i)) * convertedLocal (p i) (hp i) (hg i) true := by
      rw [Finset.prod_mul_distrib]
      ring
    _ = C ^ 3 * ∏ i,
        canonicalSextic (Ideal.span {p i}) (hg i)
          (Ideal.Quotient.mk (Ideal.span {p i}) (-1 : O)) * star (localG (p i) (hp i) (hg i)) := by
      rw [hCC, one_pow, one_mul]
      congr 1
      exact Finset.prod_congr rfl (fun i _ => (local_coefficient_cancel (p i) (hp i) (hg i) (hc i) (hpr i)).2)
    _ = _ := by rw [Finset.prod_mul_distrib]; ring

theorem convertedColumnBlock_subtype {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (b : Bool) :
    convertedColumnBlock (fun i : S => p i.val) (fun i => hp i.val)
      (fun i => hg i.val) Finset.univ b = convertedColumnBlock p hp hg S b := by
  have h := convertedColumnBlock_image p hp hg (Subtype.val : S → ι)
    Subtype.val_injective Finset.univ b
  have he : (Finset.univ : Finset S).image Subtype.val = S := by ext; simp
  simpa only [he] using h

theorem columnCoefficient_cancel_false {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S : Finset ι) :
    columnCoefficient p hp hcop hg S * convertedColumnBlock p hp hg S false =
      columnG p hp hcop hg S := by
  have h := coefficient_cancel_univ_false (fun i : S => p i.val) (fun i => hp i.val)
    (columnPrimeCoprime p hcop S) (fun i => hg i.val) (fun i => hc i.val) (fun i => hpr i.val)
  rw [convertedColumnBlock_subtype] at h
  exact h

theorem columnCoefficient_cancel_true {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S : Finset ι) :
    star (columnCoefficient p hp hcop hg S) * convertedColumnBlock p hp hg S true =
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1) *
        star (columnG p hp hcop hg S) := by
  have h := coefficient_cancel_univ_true (fun i : S => p i.val) (fun i => hp i.val)
    (columnPrimeCoprime p hcop S) (fun i => hg i.val) (fun i => hc i.val) (fun i => hpr i.val)
  have hprod : (∏ i : S, canonicalSextic (Ideal.span {p i.val}) (hg i.val)
      (Ideal.Quotient.mk (Ideal.span {p i.val}) (-1 : O))) =
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1) := by
    simpa only [finiteSquarefreeRow] using
      (Finset.prod_coe_sort S (fun i => canonicalSextic (Ideal.span {p i}) (hg i)
        (Ideal.Quotient.mk (Ideal.span {p i}) (-1 : O))))
  rw [convertedColumnBlock_subtype, hprod] at h
  exact h

end MixedCrossSeparation

open scoped BigOperators Classical SchwartzMap ContDiff
namespace FirstCauchyArithmetic
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion
open MixedCrossSeparation GaussGeneratorTransport ConcretePrimeRowBridge EisensteinSchwartzPoisson

theorem active_productGauss_eq_mobius_converted
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) :
    let q : activeSupport S T → O := fun i => p i.val
    canonicalProductGauss q (fun i => hp i.val)
      (activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T)
      (fun i => hg i.val) (activeExponent S T) =
    supportMobius (fun i => Ideal.span {p i}) S *
      supportMobius (fun i => Ideal.span {p i}) T * activeConvertedGauss p hp hg S T := by
  dsimp only
  let : DecidableEq (activeSupport S T) := fun a b => Classical.propDecidable (a = b)
  let q : activeSupport S T → O := fun i => p i.val
  let hq := activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T
  have he : activeExponent S T =
      (fun i : activeSupport S T => if decide (i.val ∈ S \ T) then 5 else 1) := by
    funext i
    simp only [activeExponent, decide_eq_true_eq]
  have h' : (supportMobius (fun i => Ideal.span {p i}) S *
      supportMobius (fun i => Ideal.span {p i}) T) *
      canonicalProductGauss q (fun i => hp i.val) hq (fun i => hg i.val)
        (activeExponent S T) = activeConvertedGauss p hp hg S T := by
    rw [supportMobius, supportMobius, pair_moebius_eq_active p hinj S T]
    unfold activeConvertedGauss
    rw [he]
    exact moebius_mixed_gauss_conversion q (fun i => hp i.val) hq (fun i => hg i.val)
      (fun i => hc i.val) (fun i => hpr i.val) (fun i => decide (i.val ∈ S \ T))
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have hs := supportMobius_sq (fun i => Ideal.span {p i}) hprime hinj S
  have ht := supportMobius_sq (fun i => Ideal.span {p i}) hprime hinj T
  calc
    _ = (supportMobius (fun i => Ideal.span {p i}) S * supportMobius (fun i => Ideal.span {p i}) S) *
      (supportMobius (fun i => Ideal.span {p i}) T * supportMobius (fun i => Ideal.span {p i}) T) *
      canonicalProductGauss q (fun i => hp i.val) hq (fun i => hg i.val) (activeExponent S T) := by
        rw [hs, ht]; ring
    _ = _ := by rw [← h']; ring

end FirstCauchyArithmetic

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Arithmetic.SquarefreeDivisors
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical
namespace FirstPassCubeLabels
open ActualEisensteinCubic

section Rows
variable {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i) (S : Finset ι)

theorem row_pow (a : O) (m : ℕ) :
    finiteSquarefreeRow P hg S (a ^ m) = finiteSquarefreeRow P hg S a ^ m := by
  simp only [finiteSquarefreeRow, map_pow, Finset.prod_pow]

theorem row_prod {κ : Type*} (B : Finset κ) (a : κ → O) :
    finiteSquarefreeRow P hg S (∏ j ∈ B, a j) =
      ∏ j ∈ B, finiteSquarefreeRow P hg S (a j) := by
  classical
  induction B using Finset.induction_on with
  | empty => simp [finiteSquarefreeRow]
  | @insert j B hj ih =>
    simp only [Finset.prod_insert hj, finiteSquarefreeRow_mul, ih]

theorem row_sixth (a : O) :
    finiteSquarefreeRow P hg S a ^ 6 = rowCoprimeMask P S a := by
  rw [← row_pow, finiteSquarefreeRow_sixth_power]
  rfl

include hg

theorem mask_mul (a b : O) :
    rowCoprimeMask P S (a * b) = rowCoprimeMask P S a * rowCoprimeMask P S b := by
  simp only [← row_sixth P hg S, finiteSquarefreeRow_mul, mul_pow]

theorem mask_prod {κ : Type*} (B : Finset κ) (a : κ → O) :
    rowCoprimeMask P S (∏ j ∈ B, a j) = ∏ j ∈ B, rowCoprimeMask P S (a j) := by
  rw [← row_sixth P hg S, row_prod, ← Finset.prod_pow]
  simp only [row_sixth]

theorem row_zero_of_mask_zero (a : O) (h : rowCoprimeMask P S a = 0) :
    finiteSquarefreeRow P hg S a = 0 := by
  have hq := row_sixth P hg S a
  rw [h] at hq
  exact (pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp hq

theorem row_power_mul_mask_power (a : O) (k m : ℕ) (hk : 0 < k) :
    finiteSquarefreeRow P hg S a ^ k * rowCoprimeMask P S a ^ m =
      finiteSquarefreeRow P hg S a ^ k := by
  by_cases h : ∃ i ∈ S, a ∈ P i
  · have hm : rowCoprimeMask P S a = 0 := by simp [rowCoprimeMask, h]
    rw [row_zero_of_mask_zero P hg S a hm]
    simp [Nat.ne_of_gt hk]
  · simp [rowCoprimeMask, h]

end Rows

end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Mellin.UniformKernelBounds
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open MixedCrossSeparation (crossSymbol quadraticCrossPhase columnPrimeCoprime)
open FiniteGaussPhase (canonicalProductGauss canonicalProductGauss_cross_factors)
open MixedGaussConversion (localGauss)

theorem canonicalProductGauss_eq_gaussBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e : ι → ℕ)
    (he : ∀ i ∈ S, e i ≠ 0) :
    canonicalProductGauss (fun i : S => p i.val) (fun i => hp i.val)
      (columnPrimeCoprime p hcop S) (fun i => hg i.val) (fun i => e i.val) =
      gaussBlock p hp hg S e := by
  let : DecidableEq S := fun a b => Classical.propDecidable (a = b)
  rw [canonicalProductGauss_cross_factors, ← Finset.prod_mul_distrib]
  have hin (i : S) :
      (∏ k ∈ (Finset.univ : Finset S).erase i,
        (canonicalSextic (Ideal.span {p i.val}) (hg i.val) ^ e i.val)
          (Ideal.Quotient.mk (Ideal.span {p i.val}) (p k.val))) =
      ∏ k ∈ S.erase i.val, crossSymbol p hg i.val k ^ e i.val := by
    apply Finset.prod_bij (fun k _ => k.val)
    · intro k hk
      exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hk).1 (Subtype.ext h), k.property⟩
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro k hk
      refine ⟨⟨k, (Finset.mem_erase.mp hk).2⟩, ?_, rfl⟩
      exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hk).1 (congrArg Subtype.val h),
        Finset.mem_univ _⟩
    · intro k hk
      exact MulChar.pow_apply' _ (he i.val i.property) _
  calc
    _ = ∏ i : S, (∏ k ∈ S.erase i.val, crossSymbol p hg i.val k ^ e i.val) *
        localGauss (p i.val) (hp i.val) (hg i.val) (e i.val) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [hin i]
      rfl
    _ = _ := Finset.prod_coe_sort S (fun i =>
      (∏ k ∈ S.erase i, crossSymbol p hg i k ^ e i) * localGauss (p i) (hp i) (hg i) (e i))

theorem gaussBlock_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S T : Finset ι) (hd : Disjoint S T)
    (e : ι → ℕ) :
    gaussBlock p hp hg (S ∪ T) e =
      gaussBlock p hp hg S e * gaussBlock p hp hg T e * blockCross p hg S T e := by
  have hS (i : ι) (hi : i ∈ S) :
      (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) =
      (∏ k ∈ S.erase i, crossSymbol p hg i k ^ e i) *
        ∏ k ∈ T, crossSymbol p hg i k ^ e i := by
    have hn : i ∉ T := fun h => Finset.disjoint_left.mp hd hi h
    rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hn,
      Finset.prod_union (hd.mono_left (Finset.erase_subset _ _))]
  have hT (i : ι) (hi : i ∈ T) :
      (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) =
      (∏ k ∈ T.erase i, crossSymbol p hg i k ^ e i) *
        ∏ k ∈ S, crossSymbol p hg i k ^ e i := by
    have hn : i ∉ S := fun h => Finset.disjoint_left.mp hd h hi
    rw [Finset.union_comm S T, Finset.erase_union_distrib, Finset.erase_eq_of_notMem hn,
      Finset.prod_union (hd.symm.mono_left (Finset.erase_subset _ _))]
  have hpS : (∏ i ∈ S, (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) *
      localGauss (p i) (hp i) (hg i) (e i)) =
      gaussBlock p hp hg S e * (∏ i ∈ S, ∏ k ∈ T, crossSymbol p hg i k ^ e i) := by
    rw [gaussBlock, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hS i hi]
    ring
  have hpT : (∏ i ∈ T, (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) *
      localGauss (p i) (hp i) (hg i) (e i)) =
      gaussBlock p hp hg T e * (∏ i ∈ T, ∏ k ∈ S, crossSymbol p hg i k ^ e i) := by
    rw [gaussBlock, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hT i hi]
    ring
  rw [gaussBlock, Finset.prod_union hd, hpS, hpT,
    Finset.prod_comm (s := T) (t := S)]
  simp only [blockCross, Finset.prod_mul_distrib]
  ring

theorem columnCoefficient_eq_gaussBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) :
    MixedCrossSeparation.columnCoefficient p hp hcop hg S =
      star (FiniteGaussPhase.angularFactor (∏ i ∈ S, p i)) *
        gaussBlock p hp hg S (fun _ => 2) := by
  unfold MixedCrossSeparation.columnCoefficient FiniteGaussPhase.canonicalProductCoefficient
  rw [Finset.prod_coe_sort]
  rw [canonicalProductGauss_eq_gaussBlock p hp hcop hg S (fun _ => 2) (fun _ _ => by decide)]

theorem blockCross_two_eq_row_four {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) :
    blockCross p hg S T (fun _ => 2) =
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (∏ k ∈ T, p k) ^ 4 := by
  simp only [blockCross, finiteSquarefreeRow, map_prod, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro k hk
  have hr : crossSymbol p hg i k ^ 2 = crossSymbol p hg k i ^ 2 :=
    canonicalSextic_sq_reciprocity_primary (Ideal.span {p i}) (Ideal.span {p k})
      (hg i) (hg k) (p i) (p k) rfl rfl (hpr i) (hpr k)
  change crossSymbol p hg i k ^ 2 * crossSymbol p hg k i ^ 2 = crossSymbol p hg i k ^ 4
  rw [← hr]
  ring

theorem columnCoefficient_union_row_four {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) (hd : Disjoint S T) :
    MixedCrossSeparation.columnCoefficient p hp hcop hg (S ∪ T) =
      MixedCrossSeparation.columnCoefficient p hp hcop hg S *
        MixedCrossSeparation.columnCoefficient p hp hcop hg T *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (∏ k ∈ T, p k) ^ 4 := by
  have ha : FiniteGaussPhase.angularFactor (∏ i ∈ S ∪ T, p i) =
      FiniteGaussPhase.angularFactor (∏ i ∈ S, p i) *
        FiniteGaussPhase.angularFactor (∏ i ∈ T, p i) := by
    rw [Finset.prod_union hd]
    simp only [FiniteGaussPhase.angularFactor, map_mul, norm_mul, Complex.ofReal_mul,
      div_eq_mul_inv, mul_inv_rev]
    ring
  rw [columnCoefficient_eq_gaussBlock, columnCoefficient_eq_gaussBlock,
    columnCoefficient_eq_gaussBlock, ha, star_mul, gaussBlock_union p hp hg S T hd,
    blockCross_two_eq_row_four p hg hpr S T]
  ring

theorem gaussBlock_norm_one {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (S : Finset ι) (e : ι → ℕ) (he : ∀ i ∈ S, e i ≠ 0) (he6 : ∀ i ∈ S, e i < 6) :
    ‖gaussBlock p hp hg S e‖ = 1 := by
  rw [← canonicalProductGauss_eq_gaussBlock p hp hcop hg S e he]
  exact FiniteGaussPhase.norm_canonicalProductGauss
    (fun i : S => p i.val) (fun i => hp i.val) (columnPrimeCoprime p hcop S)
    (fun i => hg i.val) (fun i => hc i.val) (fun i => e i.val)
    (fun i => he i.val i.property) (fun i => he6 i.val i.property)

end FirstPassCubeLabels

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.RayExpansion
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical
namespace FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)

theorem primeProductNorm_pos {ι : Type*} (p : ι → O) (hp : ∀ i, p i ≠ 0) (S : Finset ι) :
    0 < primeProductNorm p S :=
  pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)))) 2

theorem primeProductNorm_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) (S T : Finset ι) (hd : Disjoint S T) :
    primeProductNorm p (S ∪ T) = primeProductNorm p S * primeProductNorm p T := by
  simp only [primeProductNorm, Finset.prod_union hd, map_mul, norm_mul, mul_pow]

end FirstPassCubeLabels

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.KernelEnergy
namespace OAI

noncomputable section

namespace FirstPassCubeLabels

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius supportRay supportConjugateSum)
open RayFourExpansion (RayCharacter)

section Local
variable {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i)

theorem row_union (S T : Finset ι) (hd : Disjoint S T) (a : O) :
    finiteSquarefreeRow P hg (S ∪ T) a =
      finiteSquarefreeRow P hg S a * finiteSquarefreeRow P hg T a := by
  exact Finset.prod_union hd

include hg in
theorem mask_union (S T : Finset ι) (hd : Disjoint S T) (a : O) :
    rowCoprimeMask P (S ∪ T) a = rowCoprimeMask P S a * rowCoprimeMask P T a := by
  simp only [← row_sixth P hg, row_union P hg S T hd, mul_pow]

end Local

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)

end

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FourierBridge (logPhase)

end FirstPassCubeLabels

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.FirstPassage
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open MixedCrossSeparation (columnCoefficient columnG convertedColumnBlock quadraticCrossPhase
  columnPrimeCoprime columnCoefficient_cancel_false columnCoefficient_cancel_true)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)

theorem columnCoefficient_norm_one {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (S : Finset ι) :
    ‖columnCoefficient p hp hcop hg S‖ = 1 := by
  rw [FirstPassCubeLabels.columnCoefficient_eq_gaussBlock, norm_mul, norm_star,
    FiniteGaussPhase.norm_angularFactor _
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)),
    FirstPassCubeLabels.gaussBlock_norm_one p hp hcop hg hc S (fun _ => 2)
      (fun _ _ => by decide) (fun _ _ => by decide), one_mul]

theorem columnCoefficient_mul_star {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (S : Finset ι) :
    columnCoefficient p hp hcop hg S * star (columnCoefficient p hp hcop hg S) = 1 := by
  rw [← starRingEnd_apply, Complex.mul_conj', columnCoefficient_norm_one p hp hcop hg hc S]
  norm_num

theorem convertedColumnBlock_restore {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S : Finset ι) :
    convertedColumnBlock p hp hg S false =
      star (columnCoefficient p hp hcop hg S) * columnG p hp hcop hg S ∧
    convertedColumnBlock p hp hg S true =
      columnCoefficient p hp hcop hg S * finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1) *
        star (columnG p hp hcop hg S) := by
  have ha := columnCoefficient_mul_star p hp hcop hg hc S
  constructor
  · have h := congrArg (fun z => star (columnCoefficient p hp hcop hg S) * z)
      (columnCoefficient_cancel_false p hp hcop hg hc hpr S)
    calc
      _ = (columnCoefficient p hp hcop hg S * star (columnCoefficient p hp hcop hg S)) *
          convertedColumnBlock p hp hg S false := by rw [ha, one_mul]
      _ = _ := by convert (preTransparency := .instances) h using 1 ; ring
  · have h := congrArg (fun z => columnCoefficient p hp hcop hg S * z)
      (columnCoefficient_cancel_true p hp hcop hg hc hpr S)
    calc
      _ = (columnCoefficient p hp hcop hg S * star (columnCoefficient p hp hcop hg S)) *
          convertedColumnBlock p hp hg S true := by rw [ha, one_mul]
      _ = _ := by convert (preTransparency := .instances) h using 1 <;> ring

theorem mobius_second_gauss_restore {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) (hd : Disjoint S T)
    (C₁ C₂ : Finset ι → ℂ) (e k : O) :
    star (supportMobius (fun i => Ideal.span {p i}) S * C₁ S) *
      (supportMobius (fun i => Ideal.span {p i}) T * C₂ T) *
      activeGaussRowFactor p hp hinj hg T S e k =
    quadraticCrossPhase p hg T S * star (secondColumnMinus p hp hcop hg C₁ e k S) *
      secondColumnPlus p hp hcop hg C₂ e k T := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have hmS := FirstCauchyArithmetic.supportMobius_sq _ hprime hinj S
  have hmT := FirstCauchyArithmetic.supportMobius_sq _ hprime hinj T
  have hr (u : O) :
      finiteSexticRow (activePrimes (fun i => Ideal.span {p i}) T S)
        (fun i => hg i.val) (activeExponent T S) u =
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T u) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S u := by
    have hh := finiteSquarefreeRow_pair_activeSupport (fun i => Ideal.span {p i}) hg T S u
    simpa [Finset.disjoint_iff_inter_eq_empty.mp hd.symm, rowCoprimeMask] using hh.symm
  unfold activeGaussRowFactor
  dsimp only
  rw [FirstCauchyArithmetic.active_productGauss_eq_mobius_converted p hp hinj hg hc hpr,
    MixedCrossSeparation.activeConvertedGauss_eq_columnBlocks p hp hg hpr T S,
    Finset.sdiff_eq_self_of_disjoint hd.symm, Finset.sdiff_eq_self_of_disjoint hd,
    (convertedColumnBlock_restore p hp hcop hg hc hpr S).1,
    (convertedColumnBlock_restore p hp hcop hg hc hpr T).2, hr e, hr k]
  simp only [secondColumnMinus, secondColumnPlus, star_mul, star_star,
    FirstCauchyArithmetic.star_supportMobius]
  calc
    _ = (supportMobius (fun i => Ideal.span {p i}) S * supportMobius (fun i => Ideal.span {p i}) S) *
      (supportMobius (fun i => Ideal.span {p i}) T * supportMobius (fun i => Ideal.span {p i}) T) *
      (quadraticCrossPhase p hg T S *
        (star (columnCoefficient p hp hcop hg S) * columnG p hp hcop hg S * star (C₁ S) *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S e *
          star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S k)) *
        (columnCoefficient p hp hcop hg T * finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T (-1) *
          star (columnG p hp hcop hg T) * C₂ T * star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T e) *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T k)) := by ring
    _ = _ := by rw [hmS, hmT]; ring

end
section

open ActualEisensteinCubic
open MixedCrossSeparation (columnCoefficient)
open FirstPassCubeLabels (row_union mask_union mask_mul)

section Masks
variable {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i) (S : Finset ι)

theorem mask_star_row (e : O) :
    rowCoprimeMask P S e * star (finiteSquarefreeRow P hg S e) =
      star (finiteSquarefreeRow P hg S e) := by
  by_cases h : ∃ i ∈ S, e ∈ P i
  · have hm : rowCoprimeMask P S e = 0 := by simp [rowCoprimeMask, h]
    rw [FirstPassCubeLabels.row_zero_of_mask_zero P hg S e hm]
    simp
  · simp [rowCoprimeMask, h]

theorem second_child_masked (m r c d e k v : O) :
    rowCoprimeMask P S (m * (e * r)) *
      star (finiteSquarefreeRow P hg S e) *
      finiteSquarefreeRow P hg S d * finiteSquarefreeRow P hg S k *
      finiteSquarefreeRow P hg S c ^ 4 * finiteSquarefreeRow P hg S v ^ 4 =
    rowCoprimeMask P S (m * r) *
      finiteSquarefreeRow P hg S (d * e * k) *
      finiteSquarefreeRow P hg S (c * e * v) ^ 4 := by
  have hr := finiteSquarefreeRow_second_child P hg S d e k c 1 v
  simp only [mul_one] at hr
  rw [mask_mul P hg S m (e * r), mask_mul P hg S e r,
    mask_mul P hg S m r]
  calc
    _ = (rowCoprimeMask P S m * rowCoprimeMask P S r) *
      (rowCoprimeMask P S e * star (finiteSquarefreeRow P hg S e)) *
      finiteSquarefreeRow P hg S d * finiteSquarefreeRow P hg S k *
      finiteSquarefreeRow P hg S c ^ 4 * finiteSquarefreeRow P hg S v ^ 4 := by ring
    _ = _ := by
      rw [mask_star_row]
      have hh := congrArg (fun z : ℂ => (rowCoprimeMask P S m * rowCoprimeMask P S r) * z) hr
      convert (preTransparency := .instances) hh using 1 <;> ring
end Masks

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondPreColumn_union
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (Ψ : O →* ℂ) (m r c d e k : O) (H : Finset ι → ℂ)
    (V N : Finset ι) (hd : Disjoint V N) :
    secondPreColumn p hp hcop hg Ψ (m * (e * r)) c d e k H (V ∪ N) =
      secondPreColumn p hp hcop hg Ψ (m * (e * r)) c d e k (fun _ => 1) V *
      secondChildColumn p hp hcop hg Ψ (m * r) (c * e * ∏ i ∈ V, p i) (d * e * k)
        (fun U => H (V ∪ U)) N := by
  have hA := FirstPassCubeLabels.columnCoefficient_union_row_four
    p hp hcop hg hpr N V hd.symm
  rw [Finset.union_comm N V] at hA
  have hrow := second_child_masked (fun i => Ideal.span {p i}) hg N m r c d e k (∏ i ∈ V, p i)
  simp only [secondPreColumn, secondChildColumn, hA, Finset.prod_union hd,
    map_mul, row_union _ hg V N hd, mask_union _ hg V N hd,
    mul_pow, star_mul, mul_one]
  calc
    _ = (columnCoefficient p hp hcop hg V * Ψ (∏ i ∈ V, p i) *
      rowCoprimeMask (fun i => Ideal.span {p i}) V (m * (e * r)) *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V c ^ 4 *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V d *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V e) *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V k) *
      (columnCoefficient p hp hcop hg N * Ψ (∏ i ∈ N, p i) *
        (rowCoprimeMask (fun i => Ideal.span {p i}) N (m * (e * r)) *
          star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N e) *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N d *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N k *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N c ^ 4 *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N (∏ i ∈ V, p i) ^ 4) *
        H (V ∪ N)) := by ring
    _ = _ := by rw [hrow]; ring

end

open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.RayCoefficients
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open MixedCrossSeparation (columnG columnPrimeCoprime quadraticCrossPhase)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open RayFourExpansion (RayCharacter rayCharacter gCoeff crossCoeff)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem columnG_eq_ray_sum
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S : Finset ι) :
    columnG p hp hcop hg S = ∑ χ : RayCharacter, gCoeff χ * rayCharacter χ (∏ i ∈ S, p i) := by
  have h := RayFourExpansion.canonicalProductG_character_expansion
    (fun i : S => p i.val) (fun i => hp i.val) (columnPrimeCoprime p hcop S)
    (fun i => hg i.val) (fun i => hc i.val) (fun i => hpr i.val)
  simpa only [columnG, Finset.prod_coe_sort] using h

theorem secondColumnMinus_ray_expansion
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (Ψ : O →* ℂ) (m c d e k : O) (H : Finset ι → ℂ) (S : Finset ι) :
    secondColumnMinus p hp hcop hg (secondInputCoefficient p hg Ψ m c d H) e k S =
      ∑ χ : RayCharacter, star (gCoeff χ) *
        secondPreColumn p hp hcop hg (conjugateRayMonoid χ * Ψ) m c d e k H S := by
  simp only [secondColumnMinus, columnG_eq_ray_sum p hp hcop hg hc hpr,
    star_sum, star_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro χ hχ
  simp only [secondPreColumn, secondInputCoefficient, MonoidHom.mul_apply, conjugateRayMonoid_apply]
  ring

theorem secondColumnPlus_ray_expansion
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (Ψ : O →* ℂ) (m c d e k : O) (H : Finset ι → ℂ) (S : Finset ι) :
    secondColumnPlus p hp hcop hg (secondInputCoefficient p hg Ψ m c d H) e k S =
      ∑ χ : RayCharacter, star (gCoeff χ) *
        secondPreColumn p hp hcop hg (conjugateRayMonoid χ * Ψ) m c d e (-k) H S := by
  have hk : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-k) =
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S k := by
    simpa only [neg_one_mul] using finiteSquarefreeRow_mul (fun i => Ideal.span {p i}) hg S (-1) k
  simp only [secondColumnPlus, columnG_eq_ray_sum p hp hcop hg hc hpr,
    star_sum, star_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro χ hχ
  simp only [secondPreColumn, secondInputCoefficient, MonoidHom.mul_apply, conjugateRayMonoid_apply, hk]
  ring

theorem second_gauss_ray_expansion
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d e k : O) (H₁ H₂ : Finset ι → ℂ)
    (S T : Finset ι) (hd : Disjoint S T) :
    star (supportMobius (fun i => Ideal.span {p i}) S * secondInputCoefficient p hg Ψ₁ m c d H₁ S) *
      (supportMobius (fun i => Ideal.span {p i}) T * secondInputCoefficient p hg Ψ₂ m c d H₂ T) *
      activeGaussRowFactor p hp hinj hg T S e k =
    ∑ b : RayCharacter, ∑ a : RayCharacter, ∑ χ : RayCharacter, ∑ η : RayCharacter,
      (crossCoeff χ η * gCoeff a * star (gCoeff b)) *
        star (secondPreColumn p hp hcop hg
          (conjugateRayMonoid η * (conjugateRayMonoid a * Ψ₁)) m c d e k H₁ S) *
        secondPreColumn p hp hcop hg
          (rayMonoid χ * (conjugateRayMonoid b * Ψ₂)) m c d e (-k) H₂ T := by
  rw [mobius_second_gauss_restore p hp hinj hcop hg hc hpr S T hd,
    secondColumnMinus_ray_expansion p hp hcop hg hc hpr,
    secondColumnPlus_ray_expansion p hp hcop hg hc hpr,
    RayFourExpansion.quadraticCrossPhase_character_expansion p hp hcop hg hc T S hd.symm]
  simp only [star_sum, star_mul, star_star, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro η hη
  simp only [secondPreColumn, MonoidHom.mul_apply, conjugateRayMonoid_apply,
    rayMonoid_apply, star_mul, star_star]
  ring

end

open ActualEisensteinCubic

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

open scoped BigOperators Classical MatrixGroups

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.SecondPoisson
namespace OAI

noncomputable section

namespace SecondPassArithmetic

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

section

open scoped BigOperators Classical SchwartzMap ContDiff
section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstCauchyArithmetic (activeGaussRowFactor)

theorem masked_pair_second_poisson {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (M S T : Finset ι) (hd : Disjoint S T)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    let n := ∏ i : activeSupport T S, p i.val
    (∑' z : O, rowCoprimeMask (fun i => Ideal.span {p i}) M z *
      (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S z) *
      W (‖eisEmbedding z‖ ^ 2 / Y)) =
    ((Y : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
      ∑ E ∈ M.powerset,
        let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
          (‖eisEmbedding e‖ ^ 2 : ℝ)) *
          ∑' k : O, paperRadialFourier W
            (Y * ‖eisEmbedding k‖ ^ 2 / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) *
              activeGaussRowFactor p hp hinj hg T S e k := by
  dsimp only
  let P : ι → Ideal O := fun i => Ideal.span {p i}
  let Q := activePrimes P T S
  let q : activeSupport T S → O := fun i => p i.val
  let hQ := activePrimes_pairwise_isCoprime P hinj T S
  let j := activeExponent T S
  let row := finiteSexticRow Q (fun i => hg i.val) j
  let n := ∏ i, q i
  have hr (z : O) : star (finiteSquarefreeRow P hg T z) * finiteSquarefreeRow P hg S z = row z := by
    rw [finiteSquarefreeRow_pair_activeSupport]
    simp [Finset.disjoint_iff_inter_eq_empty.mp hd.symm, rowCoprimeMask, row, Q, j]
  have h := canonical_masked_radial_poisson_collected P hinj M Q hQ
    (fun i => hg i.val) (fun i => hc i.val) j
    (activeExponent_ne_zero T S) (activeExponent_lt_six T S) W Y hY
  have hn : ‖eisEmbedding (finitePrimeModulus Q)‖ = ‖eisEmbedding n‖ :=
    GaussGeneratorTransport.finitePrimeModulus_norm_eq_product q
  dsimp only at h
  rw [hn] at h
  have ht := GaussGeneratorTransport.gauss_weighted_finite_radial_sum_transport
    q (fun i => hp i.val) hQ (fun i => hg i.val) j M.powerset
    (fun E => let e := primeSubsetGenerator P E
      (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) * row e /
        (‖eisEmbedding e‖ ^ 2 : ℝ))
    (fun E t => let e := primeSubsetGenerator P E
      paperRadialFourier W (Y * t / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)))
  calc
    _ = ∑' z : O, rowCoprimeMask P M z * row z * W (‖eisEmbedding z‖ ^ 2 / Y) := by
      apply tsum_congr
      intro z
      rw [hr]
    _ = ((Y : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
        (canonicalNormalizedGauss Q hQ (fun i => hg i.val) j *
          ∑ E ∈ M.powerset,
            ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) * row (primeSubsetGenerator P E) /
              (‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 : ℝ)) *
            ∑' k : O, star (row k) * paperRadialFourier W
              (Y * ‖eisEmbedding k‖ ^ 2 /
                (‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))) := by
      rw [h]
      ring
    _ = _ := by
      rw [ht]
      simp only [Finset.mul_sum, ← tsum_mul_left]
      apply Finset.sum_congr rfl
      intro E hE
      apply tsum_congr
      intro k
      dsimp only [activeGaussRowFactor]
      ring

end

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open FirstPassCubeLabels (columnLog primeProductNorm )
open FourierBridge (logPhase)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end

open scoped BigOperators Classical
open ActualEisensteinCubic
open ConcretePrimeRowBridge (idealGenerator span_idealGenerator)
open SecondPassFiber (OldTuple Valid)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Poisson.PrincipalTruncation
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators
namespace FiniteOverlapDecomposition
variable {ι : Type*} [DecidableEq ι]

lemma join_split (ST : Finset ι × Finset ι) : join (split ST) = ST := by
  apply Prod.ext
  · ext i
    simp only [join, split, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  · ext i
    simp only [join, split, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto

lemma split_mem {F : Finset ι} {ST : Finset ι × Finset ι}
    (hST : ST ∈ F.powerset ×ˢ F.powerset) : split ST ∈ triples F := by
  rcases Finset.mem_product.mp hST with ⟨hS, hT⟩
  have hSF := Finset.mem_powerset.mp hS
  have hTF := Finset.mem_powerset.mp hT
  simp only [triples, split, Finset.mem_sigma, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
  refine ⟨Finset.inter_subset_left.trans hSF, ⟨?_, ?_⟩, ?_⟩
  · intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hi ⊢
    exact ⟨hSF hi.1, by tauto⟩
  · intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hi ⊢
    exact ⟨hTF hi.1, by tauto⟩
  · apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1

lemma join_mem {F : Finset ι} {GUV : Triple ι} (h : GUV ∈ triples F) :
    join GUV ∈ F.powerset ×ˢ F.powerset := by
  rcases (by simpa only [triples, Finset.mem_sigma, Finset.mem_filter,
    Finset.mem_product, Finset.mem_powerset] using h) with ⟨hG, ⟨hU, hV⟩, _⟩
  apply Finset.mem_product.mpr
  constructor <;> apply Finset.mem_powerset.mpr
  · exact Finset.union_subset hG (hU.trans Finset.sdiff_subset)
  · exact Finset.union_subset hG (hV.trans Finset.sdiff_subset)

lemma split_join {F : Finset ι} {GUV : Triple ι} (h : GUV ∈ triples F) :
    split (join GUV) = GUV := by
  rcases GUV with ⟨G, U, V⟩
  have hh : G ⊆ F ∧ (U ⊆ F \ G ∧ V ⊆ F \ G) ∧ Disjoint U V := by
    simpa only [triples, Finset.mem_sigma, Finset.mem_filter,
      Finset.mem_product, Finset.mem_powerset] using h
  rcases hh with ⟨_, ⟨hU, hV⟩, hd⟩
  have hUG : Disjoint U G := Finset.disjoint_left.mpr (fun i hi hg => (Finset.mem_sdiff.mp (hU hi)).2 hg)
  have hVG : Disjoint V G := Finset.disjoint_left.mpr (fun i hi hg => (Finset.mem_sdiff.mp (hV hi)).2 hg)
  have h₀ : (G ∪ U) ∩ (G ∪ V) = G := by
    ext i
    have hi : i ∈ U → i ∈ V → False := fun hi hj => Finset.disjoint_left.mp hd hi hj
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto
  have h₁ : (G ∪ U) \ (G ∪ V) = U := by
    ext i
    have hi : i ∈ U → i ∈ V → False := fun hi hj => Finset.disjoint_left.mp hd hi hj
    have hj : i ∈ U → i ∈ G → False := fun hi hj => Finset.disjoint_left.mp hUG hi hj
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  have h₂ : (G ∪ V) \ (G ∪ U) = V := by
    ext i
    have hi : i ∈ V → i ∈ U → False := fun hi hj => Finset.disjoint_left.mp hd.symm hi hj
    have hj : i ∈ V → i ∈ G → False := fun hi hj => Finset.disjoint_left.mp hVG hi hj
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  simp only [split, join, h₀, h₁, h₂]

theorem sum_pair_eq_overlap {β : Type*} [AddCommMonoid β]
    (F : Finset ι) (C : Finset ι → Finset ι → β) :
    (∑ S ∈ F.powerset, ∑ T ∈ F.powerset, C S T) =
      ∑ G ∈ F.powerset, ∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
        if Disjoint U V then C (G ∪ U) (G ∪ V) else 0 := by
  classical
  have hs : (∑ ST ∈ F.powerset ×ˢ F.powerset, C ST.1 ST.2) =
      ∑ GUV ∈ triples F, C (join GUV).1 (join GUV).2 := by
    apply Finset.sum_bij (fun ST _ => split ST)
    · intro ST hST
      exact split_mem hST
    · intro ST hST SU hSU heq
      have hh := congrArg join heq
      simpa only [join_split] using hh
    · intro GUV hGUV
      exact ⟨join GUV, join_mem hGUV, split_join hGUV⟩
    · intro ST hST
      rw [join_split]
  simpa only [triples, Finset.sum_sigma, Finset.sum_filter, Finset.sum_product, join] using hs

end FiniteOverlapDecomposition

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.ChildTransfer
namespace OAI

noncomputable section

namespace SecondPassArithmetic

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

section

open scoped BigOperators Classical

section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius supportConjugateSum)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondInputCoefficient_union (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (G U : Finset ι) (hd : Disjoint G U) :
    secondInputCoefficient p hg Ψ m c d H (G ∪ U) =
      secondInputCoefficient p hg Ψ m c d (fun _ => 1) G *
        secondInputCoefficient p hg Ψ m c d (fun V => H (G ∪ V)) U := by
  simp only [secondInputCoefficient, Finset.prod_union hd, map_mul,
    FirstPassCubeLabels.mask_union _ hg G U hd,
    FirstPassCubeLabels.row_union _ hg G U hd, mul_pow, mul_one]
  ring

theorem supportMobius_disjoint_mul
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (G U : Finset ι) (hd : Disjoint G U) :
    supportMobius (fun i => Ideal.span {p i}) (G ∪ U) =
      supportMobius (fun i => Ideal.span {p i}) G * supportMobius (fun i => Ideal.span {p i}) U := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  simp only [supportMobius, prime_product_moebius _ hprime hinj,
    Finset.card_union_of_disjoint hd, pow_add]

theorem inputConjugateRow_sq_overlap
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ) (z : O) :
    (↑(‖inputConjugateRow p hg F Ψ m c d H z‖ ^ 2) : ℂ) =
      ∑ G ∈ F.powerset, ∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
        if Disjoint U V then
          (↑(‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2) : ℂ) *
          rowCoprimeMask (fun i => Ideal.span {p i}) G z *
          (star (supportMobius (fun i => Ideal.span {p i}) U *
            secondInputCoefficient p hg Ψ m c d (fun S => H (G ∪ S)) U) *
            (supportMobius (fun i => Ideal.span {p i}) V *
              secondInputCoefficient p hg Ψ m c d (fun S => H (G ∪ S)) V) *
            (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U z *
              star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V z))) else 0 := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have hnorm (a : ℂ) : (↑(‖a‖ ^ 2) : ℂ) = star a * a := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    rfl
  rw [hnorm]
  unfold inputConjugateRow supportConjugateSum
  rw [star_sum, Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [FiniteOverlapDecomposition.sum_pair_eq_overlap]
  apply Finset.sum_congr rfl
  intro G hG
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  by_cases hd : Disjoint U V
  · rw [if_pos hd, if_pos hd]
    have hGU : Disjoint G U := Finset.disjoint_left.mpr (fun i hi hu =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hU) hu)).2 hi)
    have hGV : Disjoint G V := Finset.disjoint_left.mpr (fun i hi hv =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hV) hv)).2 hi)
    rw [supportMobius_disjoint_mul p hinj G U hGU, supportMobius_disjoint_mul p hinj G V hGV,
      secondInputCoefficient_union p hg Ψ m c d H G U hGU,
      secondInputCoefficient_union p hg Ψ m c d H G V hGV,
      FirstPassCubeLabels.row_union _ hg G U hGU,
      FirstPassCubeLabels.row_union _ hg G V hGV]
    simp only [star_mul, star_star, FirstCauchyArithmetic.star_supportMobius]
    have hmu := FirstCauchyArithmetic.supportMobius_sq _ hprime hinj G
    have hrow := finiteSquarefreeRow_self_pair (fun i => Ideal.span {p i}) hg G z
    rw [hnorm]
    calc
      _ = (supportMobius (fun i => Ideal.span {p i}) G * supportMobius (fun i => Ideal.span {p i}) G) *
        (star (secondInputCoefficient p hg Ψ m c d (fun _ => 1) G) *
          secondInputCoefficient p hg Ψ m c d (fun _ => 1) G) *
        (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg G z) *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg G z) *
        (star (supportMobius (fun i => Ideal.span {p i}) U *
            secondInputCoefficient p hg Ψ m c d (fun S => H (G ∪ S)) U) *
          (supportMobius (fun i => Ideal.span {p i}) V *
            secondInputCoefficient p hg Ψ m c d (fun S => H (G ∪ S)) V) *
          (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U z *
            star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V z))) := by
          simp only [star_mul, FirstCauchyArithmetic.star_supportMobius]
          ring
      _ = _ := by
        rw [hmu, hrow]
        simp only [star_mul, FirstCauchyArithmetic.star_supportMobius]
        ring
  · simp [hd]

end

section
open ActualEisensteinCubic

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
include hg

theorem commonProduct_mask
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (U G : Finset ι) :
    rowCoprimeMask (fun i => Ideal.span {p i}) U (∏ i ∈ G, p i) =
      if Disjoint U G then 1 else 0 := by
  by_cases hd : Disjoint U G
  · rw [if_pos hd, FirstPassCubeLabels.mask_prod _ hg U G p]
    apply Finset.prod_eq_one
    intro j hj
    have hh : ¬ ∃ i ∈ U, p j ∈ Ideal.span {p i} := by
      rintro ⟨i, hi, hpi⟩
      have hij : i ≠ j := fun he => Finset.disjoint_left.mp hd hi (he ▸ hj)
      exact (prime_generator_not_mem_of_ne (Ideal.span {p i}) (Ideal.span {p j})
        (fun he => hij (hinj he)) (p j) rfl) hpi
    simp [rowCoprimeMask, hh]
  · rw [if_neg hd]
    obtain ⟨i, hiU, hiG⟩ := Finset.not_disjoint_iff.mp hd
    have hh : ∃ j ∈ U, (∏ i ∈ G, p i) ∈ Ideal.span {p j} :=
      ⟨i, hiU, Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem p hiG)⟩
    simp [rowCoprimeMask, hh]

theorem sum_remove_common_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G : Finset ι) (A : Finset ι → ℂ) :
    (∑ U ∈ (F \ G).powerset, A U) =
      ∑ U ∈ F.powerset, rowCoprimeMask (fun i => Ideal.span {p i}) U (∏ i ∈ G, p i) * A U := by
  have hsub : (F \ G).powerset ⊆ F.powerset := Finset.powerset_mono.mpr Finset.sdiff_subset
  calc
    _ = ∑ U ∈ (F \ G).powerset,
        rowCoprimeMask (fun i => Ideal.span {p i}) U (∏ i ∈ G, p i) * A U := by
      apply Finset.sum_congr rfl
      intro U hU
      have hd : Disjoint U G := Finset.disjoint_left.mpr (fun i hi hG =>
        (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hU) hi)).2 hG)
      rw [commonProduct_mask p hg hinj U G, if_pos hd, one_mul]
    _ = _ := by
      apply Finset.sum_subset hsub
      intro U hUF hUG
      have hd : ¬ Disjoint U G := by
        intro hd
        apply hUG
        apply Finset.mem_powerset.mpr
        intro i hi
        exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hUF) hi,
          fun hG => Finset.disjoint_left.mp hd hi hG⟩
      rw [commonProduct_mask p hg hinj U G, if_neg hd, zero_mul]

omit [DecidableEq ι] in
theorem secondInputCoefficient_fixed_mask (Ψ : O →* ℂ) (m g c d : O)
    (H : Finset ι → ℂ) (U : Finset ι) :
    secondInputCoefficient p hg Ψ (m*g) c d H U =
      rowCoprimeMask (fun i => Ideal.span {p i}) U g * secondInputCoefficient p hg Ψ m c d H U := by
  rw [secondInputCoefficient, FirstPassCubeLabels.mask_mul _ hg U m g]
  unfold secondInputCoefficient
  ring

theorem inputConjugateRow_fixed_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ) (z : O) :
    inputConjugateRow p hg (F \ G) Ψ m c d H z =
      inputConjugateRow p hg F Ψ (m * ∏ i ∈ G, p i) c d H z := by
  unfold inputConjugateRow FirstCauchyArithmetic.supportConjugateSum
  rw [sum_remove_common_pool p hg hinj F G]
  apply Finset.sum_congr rfl
  intro U hU
  rw [secondInputCoefficient_fixed_mask]
  ring

end

section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
include hg

theorem sum_pair_remove_common_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G : Finset ι) (A : Finset ι → Finset ι → ℂ) :
    (∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset, A U V) =
      ∑ U ∈ F.powerset, ∑ V ∈ F.powerset,
        rowCoprimeMask (fun i => Ideal.span {p i}) U (∏ i ∈ G, p i) *
        rowCoprimeMask (fun i => Ideal.span {p i}) V (∏ i ∈ G, p i) * A U V := by
  rw [sum_remove_common_pool p hg hinj F G]
  apply Finset.sum_congr rfl
  intro U hU
  rw [sum_remove_common_pool p hg hinj F G, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro V hV
  ring

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] hg in
lemma star_mask (P : ι → Ideal O) (S : Finset ι) (a : O) :
    star (rowCoprimeMask P S a) = rowCoprimeMask P S a := by
  unfold rowCoprimeMask
  split_ifs <;> simp

theorem input_pair_fixed_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O)
    (H₁ H₂ : Finset ι → ℂ) (K : Finset ι → Finset ι → ℂ) :
    (∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
      if Disjoint U V then
        star (supportMobius (fun i => Ideal.span {p i}) U * secondInputCoefficient p hg Ψ₁ m c d H₁ U) *
        (supportMobius (fun i => Ideal.span {p i}) V * secondInputCoefficient p hg Ψ₂ m c d H₂ V) * K U V
      else 0) =
    ∑ U ∈ F.powerset, ∑ V ∈ F.powerset,
      if Disjoint U V then
        star (supportMobius (fun i => Ideal.span {p i}) U *
          secondInputCoefficient p hg Ψ₁ (m * ∏ i ∈ G, p i) c d H₁ U) *
        (supportMobius (fun i => Ideal.span {p i}) V *
          secondInputCoefficient p hg Ψ₂ (m * ∏ i ∈ G, p i) c d H₂ V) * K U V
      else 0 := by
  rw [sum_pair_remove_common_pool p hg hinj F G]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  by_cases hd : Disjoint U V
  · rw [if_pos hd, if_pos hd, secondInputCoefficient_fixed_mask,
      secondInputCoefficient_fixed_mask]
    simp only [star_mul, star_mask]
    ring
  · simp [hd]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] hg in
theorem secondMaskQuotient_spec (E G : Finset ι) (hEG : E ⊆ G) :
    (∏ i ∈ G, p i) = primeSubsetGenerator (fun i => Ideal.span {p i}) E *
      secondMaskQuotient p E G hEG :=
  Classical.choose_spec (poisson_mask_generator_dvd p E G hEG)

end

open ActualEisensteinCubic

end

section

open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstCauchyArithmetic (supportMobius)
open EisensteinSchwartzPoisson (paperRadialFourier)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] in
theorem maskedSecondSource_summable (G U V : Finset ι) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun z : O => rowCoprimeMask (fun i => Ideal.span {p i}) G z *
      (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V z) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U z) * W (‖eisEmbedding z‖ ^ 2 / Y)) := by
  have h := finiteSquarefreeRow_pair_radial_summable (fun i => Ideal.span {p i}) hg V U W Y hY
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _ h.norm
  intro z
  have hm : ‖rowCoprimeMask (fun i => Ideal.span {p i}) G z‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> norm_num
  simpa only [norm_mul, one_mul, mul_assoc] using
    mul_le_mul_of_nonneg_right hm
      (norm_nonneg ((star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V z) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U z) * W (‖eisEmbedding z‖ ^ 2 / Y)))

theorem inputConjugateRow_smoothed_overlap
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖inputConjugateRow p hg F Ψ m c d H z‖ ^ 2) : ℂ)) =
      ∑ G ∈ F.powerset, ∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
        if Disjoint U V then overlapPairWeight p hg Ψ m c d H G U V *
          maskedSecondSource p hg G U V W Y else 0 := by
  let f := fun (G U V : Finset ι) (z : O) => if Disjoint U V then
    overlapPairWeight p hg Ψ m c d H G U V *
      (rowCoprimeMask (fun i => Ideal.span {p i}) G z *
        (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V z) *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U z) * W (‖eisEmbedding z‖ ^ 2 / Y))
    else 0
  have hf (G U V : Finset ι) : Summable (f G U V) := by
    by_cases hd : Disjoint U V
    · simpa only [f, if_pos hd] using
        (maskedSecondSource_summable p hg G U V W Y hY).mul_left (overlapPairWeight p hg Ψ m c d H G U V)
    · simp only [f, if_neg hd]
      exact summable_zero
  have he (z : O) : W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖inputConjugateRow p hg F Ψ m c d H z‖ ^ 2) : ℂ) =
      ∑ G ∈ F.powerset, ∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset, f G U V z := by
    rw [inputConjugateRow_sq_overlap p hg hinj]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro G hG
    apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro V hV
    by_cases hd : Disjoint U V
    · simp only [f, if_pos hd, overlapPairWeight]
      ring
    · simp [f, hd]
  rw [tsum_congr he]
  rw [Summable.tsum_finsetSum (fun G _ => summable_sum (fun U _ => summable_sum (fun V _ => hf G U V)))]
  apply Finset.sum_congr rfl
  intro G hG
  rw [Summable.tsum_finsetSum (fun U _ => summable_sum (fun V _ => hf G U V))]
  apply Finset.sum_congr rfl
  intro U hU
  rw [Summable.tsum_finsetSum (fun V _ => hf G U V)]
  apply Finset.sum_congr rfl
  intro V hV
  by_cases hd : Disjoint U V
  · simp only [f, if_pos hd, maskedSecondSource]
    exact tsum_mul_left
  · simp [f, hd]

theorem inputConjugateRow_smoothed_second_poisson (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖inputConjugateRow p hg F Ψ m c d H z‖ ^ 2) : ℂ)) =
      ∑ G ∈ F.powerset, ∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
        if Disjoint U V then overlapPairWeight p hg Ψ m c d H G U V *
          maskedSecondDual p hg hp hinj G U V W Y else 0 := by
  rw [inputConjugateRow_smoothed_overlap p hg hinj F Ψ m c d H W Y hY]
  apply Finset.sum_congr rfl
  intro G hG
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  by_cases hd : Disjoint U V
  · rw [if_pos hd, if_pos hd]
    congr 1
    exact masked_pair_second_poisson p hp hinj hg hc G U V hd W Y hY
  · simp [hd]

end

open scoped BigOperators Classical
open ActualEisensteinCubic
open FirstPassCubeLabels (cubeCoreCoefficient cubeOddSupport coreRayCoefficient coreRayTwist
  coreRayCharacter dilatedCoreRow dilatedRayColumn afterDilationLabel b0Label jLabel)
open FirstCauchyArithmetic (supportMobius supportRay supportConjugateSum)
open RayFourExpansion (RayCharacter)
open FourierBridge (logPhase)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.IntegratedTransfer
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

namespace SecondPassArithmetic

open ActualEisensteinCubic
open FirstPassCubeLabels (b0Label jLabel)
open RayFourExpansion (RayCharacter)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem firstCoreInputRow_smoothed_sign
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) : ℂ)) =
    ∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖inputConjugateRow p hg (F \ D) (firstCoreTwist negative χ Ψ r)
        (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
        (firstCoreTest H V y negative t D) z‖ ^ 2) : ℂ) := by
  cases negative
  · rfl
  · simpa only [firstCoreInputRow, Bool.true_eq, ite_true, Equiv.neg_apply, map_neg, norm_neg] using
      (Equiv.neg O).tsum_eq (fun z : O => W (‖eisEmbedding z‖ ^ 2 / Y) *
        (↑(‖inputConjugateRow p hg (F \ D) (firstCoreTwist true χ Ψ r)
          (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
          (firstCoreTest H V y true t D) z‖ ^ 2) : ℂ))

theorem firstCoreInputRow_smoothed_second_poisson
    (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) : ℂ)) =
    ∑ G ∈ (F \ D).powerset, ∑ U ∈ ((F \ D) \ G).powerset, ∑ V' ∈ ((F \ D) \ G).powerset,
      if Disjoint U V' then
        overlapPairWeight p hg (firstCoreTwist negative χ Ψ r)
          (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
          (firstCoreTest H V y negative t D) G U V' *
          maskedSecondDual p hg hp hinj G U V' W Y
      else 0 := by
  rw [firstCoreInputRow_smoothed_sign]
  exact inputConjugateRow_smoothed_second_poisson p hg hp hinj hc (F \ D)
    (firstCoreTwist negative χ Ψ r) (m * b0Label p B v ε₁ ε₂)
    (c * jLabel p B v ε₁ ε₂) d (firstCoreTest H V y negative t D) W Y hY

end SecondPassArithmetic

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.RowMajorants
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondPreKernelPair_eq_children
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k₁ k₂ : O)
    (K : Finset ι → Finset ι → ℂ) :
    secondPreKernelPair p hp hcop hg F Ψ₁ Ψ₂ m r c d e k₁ k₂ K =
      ∑ V ∈ F.powerset, secondCommonWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k₁ k₂ V *
        secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ K := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  unfold secondPreKernelPair
  rw [CoprimeMobiusExtension.double_sum_disjoint_reindexed]
  apply Finset.sum_congr rfl
  intro V hV
  rw [secondCommonWeight, supportMobius, prime_product_moebius _ hprime hinj]
  simp only [secondChildKernelPair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  have hdN : Disjoint V N := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hN) disjoint_sdiff_self_right
  have hdM : Disjoint V M := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hM) disjoint_sdiff_self_right
  rw [secondPreColumn_union p hp hcop hg hpr Ψ₁ m r c d e k₁ (fun _ => 1) V N hdN,
    secondPreColumn_union p hp hcop hg hpr Ψ₂ m r c d e k₂ (fun _ => 1) V M hdM, star_mul]
  ring

theorem secondKernelPair_eq_pre
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (K : Finset ι → Finset ι → ℂ) :
    secondKernelPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k K =
      ∑ z : SecondRayIndex, secondRayCoefficient z *
        secondPreKernelPair p hp hcop hg F (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
          m r c d e k (-k) K := by
  have hterm (S T : Finset ι) :
      (if Disjoint S T then secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k
        (fun _ => 1) (fun _ => 1) S T * K S T else 0) =
      ∑ z : SecondRayIndex, secondRayCoefficient z * (if Disjoint S T then
        star (secondPreColumn p hp hcop hg (secondRayMinus Ψ₁ z) (m * (e * r)) c d e k (fun _ => 1) S) *
        secondPreColumn p hp hcop hg (secondRayPlus Ψ₂ z) (m * (e * r)) c d e (-k) (fun _ => 1) T * K S T else 0) := by
    by_cases hd : Disjoint S T
    · simp only [if_pos hd, secondGaussTerm]
      have h := congrArg (fun a : ℂ => a * K S T)
        (second_gauss_ray_expansion p hp hcop hg hinj hc hpr Ψ₁ Ψ₂
          (m * (e * r)) c d e k (fun _ => 1) (fun _ => 1) S T hd)
      simpa only [Fintype.sum_prod_type, secondRayCoefficient, secondRayMinus,
        secondRayPlus, Finset.sum_mul, mul_assoc] using h
    · simp [hd]
  unfold secondKernelPair
  simp_rw [hterm]
  calc
    _ = ∑ S ∈ F.powerset, ∑ z : SecondRayIndex, ∑ T ∈ F.powerset,
        secondRayCoefficient z * (if Disjoint S T then
        star (secondPreColumn p hp hcop hg (secondRayMinus Ψ₁ z) (m * (e * r)) c d e k (fun _ => 1) S) *
        secondPreColumn p hp hcop hg (secondRayPlus Ψ₂ z) (m * (e * r)) c d e (-k) (fun _ => 1) T * K S T else 0) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [secondPreKernelPair, Finset.mul_sum]

theorem secondKernelPair_eq_children
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (K : Finset ι → Finset ι → ℂ) :
    secondKernelPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k K =
      ∑ z : SecondRayIndex, ∑ V ∈ F.powerset,
        secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z,V) *
          secondChildKernelPair p hp hcop hg F V (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
            m r c d e k (-k) K := by
  rw [secondKernelPair_eq_pre p hp hcop hg hinj hc hpr]
  simp only [secondPreKernelPair_eq_children p hp hcop hg hinj hpr,
    secondTotalWeight, Finset.mul_sum, mul_assoc]

end SecondPassArithmetic

open MeasureTheory Set Module
open scoped BigOperators Classical ENNReal

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.PrimePools
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

private theorem active_row_norm_le_one (S T : Finset ι) (a : O) :
    ‖finiteSexticRow (activePrimes (fun i => Ideal.span {p i}) S T)
      (fun i => hg i.val) (activeExponent S T) a‖ ≤ 1 := by
  rw [finiteSexticRow_activeSupport, norm_mul, norm_star]
  exact (mul_le_mul (finiteSquarefreeRow_norm_le_one _ hg _ _)
    (finiteSquarefreeRow_norm_le_one _ hg _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem secondPairRadialMode_summable (S T : Finset ι) (e : O) (he : e ≠ 0)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun k : O => secondPairRadialMode p hp hg hinj S T e k W Y) := by
  let n := ∏ i : activeSupport T S, p i.val
  let G := FiniteGaussPhase.canonicalProductGauss (fun i : activeSupport T S => p i.val)
    (fun i => hp i.val) (activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj T S)
    (fun i => hg i.val) (activeExponent T S)
  have hn : n ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i hi => hp i.val)
  have hK : 0 < Y / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2) :=
    div_pos hY (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero he)))
      (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hn))))
  have hs := EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W _ hK
  have hgk (k : O) : ‖activeGaussRowFactor p hp hinj hg T S e k‖ ≤ ‖G‖ := by
    simp only [activeGaussRowFactor, norm_mul, norm_star]
    change ‖G‖ * (_ * _) ≤ ‖G‖
    have hb : ‖finiteSexticRow (activePrimes (fun i => Ideal.span {p i}) T S)
        (fun i => hg i.val) (activeExponent T S) e‖ *
        ‖finiteSexticRow (activePrimes (fun i => Ideal.span {p i}) T S)
        (fun i => hg i.val) (activeExponent T S) k‖ ≤ 1 := by
      simpa only [one_mul] using mul_le_mul (active_row_norm_le_one p hg T S e)
        (active_row_norm_le_one p hg T S k) (norm_nonneg _) zero_le_one
    exact mul_le_of_le_one_right (norm_nonneg _) hb
  have harg (k : O) : Y * ‖eisEmbedding k‖ ^ 2 / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2) =
      (Y / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) * ‖eisEmbedding k‖ ^ 2 := by ring
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((hs.mul_left ‖(Y : ℂ) / (‖eisEmbedding n‖ : ℂ)‖).mul_right ‖G‖)
  intro k
  simp only [secondPairRadialMode, norm_mul]
  rw [show (∏ i : activeSupport T S, p i.val) = n from rfl, harg]
  exact mul_le_mul_of_nonneg_left (hgk k) (by positivity)

theorem maskedSecondDual_eq_modes (G S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    maskedSecondDual p hg hp hinj G S T W Y =
      ∑ E ∈ G.powerset,
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
          (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ)) *
        ∑' k : O, secondPairRadialMode p hp hg hinj S T
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E) k W Y := by
  simp only [maskedSecondDual, secondPairRadialMode, mul_assoc, tsum_mul_left, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E hE
  ring

theorem residualSecondMode_summable (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O)
    (H₁ H₂ : Finset ι → ℂ) (e : O) (he : e ≠ 0) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun k : O => residualSecondMode p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂ e k W Y) := by
  apply summable_sum
  intro S hS
  apply summable_sum
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [if_pos hd]
    exact (secondPairRadialMode_summable p hp hg hinj S T e he W Y hY).mul_left _
  · simp only [if_neg hd]
    exact summable_zero

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open FirstPassCubeLabels (primeProductNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem residualSecondMode_tsum (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O)
    (H₁ H₂ : Finset ι → ℂ) (e : O) (he : e ≠ 0) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' k : O, residualSecondMode p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂ e k W Y) =
      ∑ S ∈ (F \ G).powerset, ∑ T ∈ (F \ G).powerset,
        ∑' k : O, if Disjoint S T then
          star (supportMobius (fun i => Ideal.span {p i}) S * secondInputCoefficient p hg Ψ₁ m c d H₁ S) *
          (supportMobius (fun i => Ideal.span {p i}) T * secondInputCoefficient p hg Ψ₂ m c d H₂ T) *
          secondPairRadialMode p hp hg hinj S T e k W Y
        else 0 := by
  have hs (S T : Finset ι) : Summable (fun k : O => if Disjoint S T then
      star (supportMobius (fun i => Ideal.span {p i}) S * secondInputCoefficient p hg Ψ₁ m c d H₁ S) *
      (supportMobius (fun i => Ideal.span {p i}) T * secondInputCoefficient p hg Ψ₂ m c d H₂ T) *
      secondPairRadialMode p hp hg hinj S T e k W Y else 0) := by
    by_cases hd : Disjoint S T
    · simp only [if_pos hd]
      exact (secondPairRadialMode_summable p hp hg hinj S T e he W Y hY).mul_left _
    · simp only [if_neg hd]
      exact summable_zero
  unfold residualSecondMode
  rw [Summable.tsum_finsetSum (fun S _ => summable_sum (fun T _ => hs S T))]
  apply Finset.sum_congr rfl
  intro S hS
  exact Summable.tsum_finsetSum (fun T _ => hs S T)

theorem secondOverlapBlock_eq_modes (F G : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    secondOverlapBlock p hp hg hinj F G Ψ m c d H W Y =
      (↑(‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2) : ℂ) *
        ∑ E ∈ G.powerset,
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
            (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ)) *
          ∑' k : O, residualSecondMode p hp hg hinj F G Ψ Ψ m c d
            (fun U => H (G ∪ U)) (fun U => H (G ∪ U))
            (primeSubsetGenerator (fun i => Ideal.span {p i}) E) k W Y := by
  let a := (↑(‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2) : ℂ)
  let w := fun E : Finset ι =>
    (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
      (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ)
  let f := fun (E S T : Finset ι) (k : O) => if Disjoint S T then
    star (supportMobius (fun i => Ideal.span {p i}) S *
      secondInputCoefficient p hg Ψ m c d (fun U => H (G ∪ U)) S) *
    (supportMobius (fun i => Ideal.span {p i}) T *
      secondInputCoefficient p hg Ψ m c d (fun U => H (G ∪ U)) T) *
    secondPairRadialMode p hp hg hinj S T (primeSubsetGenerator (fun i => Ideal.span {p i}) E) k W Y
    else 0
  have hterm (S T : Finset ι) :
      (if Disjoint S T then overlapPairWeight p hg Ψ m c d H G S T *
        maskedSecondDual p hg hp hinj G S T W Y else 0) =
      a * ∑ E ∈ G.powerset, w E * ∑' k : O, f E S T k := by
    by_cases hd : Disjoint S T
    · simp only [if_pos hd, maskedSecondDual_eq_modes p hp hg hinj,
        overlapPairWeight, f, Finset.mul_sum, tsum_mul_left]
      apply Finset.sum_congr rfl
      intro E hE
      dsimp only [a, w]
      ring
    · simp [hd, f]
  calc
    _ = a * ∑ S ∈ (F \ G).powerset, ∑ T ∈ (F \ G).powerset,
        ∑ E ∈ G.powerset, w E * ∑' k : O, f E S T k := by
      simp only [secondOverlapBlock, hterm, Finset.mul_sum]
    _ = a * ∑ S ∈ (F \ G).powerset, ∑ E ∈ G.powerset,
        ∑ T ∈ (F \ G).powerset, w E * ∑' k : O, f E S T k := by
      congr 1
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.sum_comm]
    _ = a * ∑ E ∈ G.powerset, ∑ S ∈ (F \ G).powerset,
        ∑ T ∈ (F \ G).powerset, w E * ∑' k : O, f E S T k := by
      congr 1
      rw [Finset.sum_comm]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro E hE
      rw [residualSecondMode_tsum p hp hg hinj F G Ψ Ψ m c d
        (fun U => H (G ∪ U)) (fun U => H (G ∪ U))
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E)
        (primeSubsetGenerator_ne_zero _ E) W Y hY]
      simp only [Finset.mul_sum]
      rfl

theorem residualSecondMode_eq_frequencyKernel (F G E : Finset ι) (hEG : E ⊆ G)
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O) (H₁ H₂ : Finset ι → ℂ)
    (k : O) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    residualSecondMode p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E) k W Y =
    secondFrequencyKernel p hp hg hinj F Ψ₁ Ψ₂ m (secondMaskQuotient p E G hEG) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E) k H₁ H₂ W Y := by
  unfold residualSecondMode
  rw [input_pair_fixed_pool p hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂]
  unfold secondFrequencyKernel
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd : Disjoint S T
  · rw [if_pos hd, if_pos hd]
    have hn : (∏ i : activeSupport T S, p i.val) = ∏ i ∈ S ∪ T, p i := by
      rw [Finset.prod_coe_sort]
      simp only [activeSupport, Finset.sdiff_eq_self_of_disjoint hd,
        Finset.sdiff_eq_self_of_disjoint hd.symm, Finset.union_comm T S]
    simp only [secondPairRadialMode, secondGaussTerm, hn, primeProductNorm,
      ← secondMaskQuotient_spec p E G hEG]
    ring
  · simp [hd]

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.FrequencyBlocks
namespace OAI

noncomputable section

namespace SecondPassArithmetic

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

section

open scoped BigOperators Classical SchwartzMap

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem inputConjugateRow_smoothed_frequency_blocks
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖inputConjugateRow p hg F Ψ m c d H z‖ ^ 2) : ℂ)) =
    ∑ G ∈ F.powerset,
      (↑(‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2) : ℂ) *
      ∑ E : G.powerset,
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E.val, Ideal.span {p i}) : ℂ) /
          (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖ ^ 2 : ℝ)) *
        ∑' k : O,
          secondFrequencyKernel p hp hg hinj F Ψ Ψ m
            (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
            (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
            (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y := by
  rw [inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F Ψ m c d H W Y hY]
  apply Finset.sum_congr rfl
  intro G hG
  change secondOverlapBlock p hp hg hinj F G Ψ m c d H W Y = _
  rw [secondOverlapBlock_eq_modes p hp hg hinj F G Ψ m c d H W Y hY]
  congr 1
  rw [← Finset.sum_coe_sort (s := G.powerset)]
  apply Finset.sum_congr rfl
  intro E hE
  congr 1
  apply tsum_congr
  intro k
  exact residualSecondMode_eq_frequencyKernel p hp hg hinj F G E.val
    (Finset.mem_powerset.mp E.property) Ψ Ψ m c d
    (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) k W Y

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstCauchyArithmetic (supportConjugateSum supportMobius)
open RayFourExpansion (RayCharacter)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open ActualEisensteinCubic
open JointLogSeparation
open FirstPassCubeLabels (b0Label)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.FixedProfiles
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem secondGaussTerm_test_factors (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) (S T : Finset ι) :
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k H₁ H₂ S T =
      star (H₁ S) * H₂ T *
        secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k (fun _ => 1) (fun _ => 1) S T := by
  simp only [secondGaussTerm, secondInputCoefficient, star_mul, mul_one]
  ring

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap ContDiff

namespace SecondPassArithmetic

open ActualEisensteinCubic
open FiniteGaussPhase (canonicalProductGauss_cross_factors)
open FirstCauchyArithmetic (activeGaussRowFactor supportMobius)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem activeGaussRowFactor_zero_of_ne (S T : Finset ι) (hne : S ≠ T) (e : O) :
    activeGaussRowFactor p hp hinj hg S T e 0 = 0 := by
  have hs : (activeSupport S T).Nonempty := by
    by_contra hn
    apply hne
    have he : activeSupport S T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [activeSupport, Finset.union_eq_empty, Finset.sdiff_eq_empty_iff_subset] at he
    exact Finset.Subset.antisymm he.1 he.2
  let : Nonempty (activeSupport S T) := hs.to_subtype
  unfold activeGaussRowFactor
  simp only [finiteSexticRow_zero, star_zero, mul_zero]

theorem activeGaussRowFactor_empty (e k : O) :
    activeGaussRowFactor p hp hinj hg ∅ ∅ e k = 1 := by
  have hempty : activeSupport (∅ : Finset ι) ∅ = ∅ := by simp [activeSupport]
  let : IsEmpty (activeSupport (∅ : Finset ι) ∅) := ⟨fun x => by simpa [hempty] using x.property⟩
  simp only [activeGaussRowFactor, finiteSexticRow, star_one, mul_one,
    canonicalProductGauss_cross_factors, Fintype.prod_empty]

theorem secondGaussTerm_empty (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) :
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k H₁ H₂ ∅ ∅ =
      star (H₁ ∅) * H₂ ∅ := by
  have hm : supportMobius (fun i => Ideal.span {p i}) ∅ = 1 := by
    change (UniqueFactorizationMonoid.moebius (1 : Ideal O) : ℂ) = 1
    exact_mod_cast UniqueFactorizationMonoid.moebius_one
  simp only [secondGaussTerm, hm, one_mul, secondInputCoefficient, Finset.prod_empty,
    map_one, activeGaussRowFactor_empty, mul_one]
  simp [rowCoprimeMask, finiteSquarefreeRow]

theorem secondFrequencyKernel_zero (F : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e : O) (H₁ H₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    secondFrequencyKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e 0 H₁ H₂ W Y =
      (Y : ℂ) * EisensteinSchwartzPoisson.paperRadialFourier W 0 * star (H₁ ∅) * H₂ ∅ := by
  have hz (S T : Finset ι) (hne : S ≠ T) :
      secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e 0 H₁ H₂ S T = 0 := by
    unfold secondGaussTerm
    rw [activeGaussRowFactor_zero_of_ne p hp hg hinj T S (Ne.symm hne) e, mul_zero]
  unfold secondFrequencyKernel
  rw [Finset.sum_eq_single ∅]
  · rw [Finset.sum_eq_single ∅]
    · simp [secondGaussTerm_empty, mul_assoc]
    · intro T hT hne
      rw [hz ∅ T (Ne.symm hne)]
      simp
    · simp
  · intro S hS hne
    apply Finset.sum_eq_zero
    intro T hT
    by_cases hd : Disjoint S T
    · have hneq : S ≠ T := by
        intro heq
        subst T
        exact hne ((show S = ∅ by simpa using Finset.disjoint_iff_inter_eq_empty.mp hd))
      rw [hz S T hneq]
      simp
    · simp [hd]
  · simp

end SecondPassArithmetic

open MeasureTheory Set Filter
open scoped BigOperators Classical

open MeasureTheory Set Filter
open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.ResidualSectors
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstPassCubeLabels (primeProductNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem secondFrequencyKernel_eq_kernelPair (F : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    secondFrequencyKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e k H₁ H₂ W Y =
      (Y : ℂ) * secondKernelPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k
        (secondSourcePairKernel p e k H₁ H₂ W Y) := by
  unfold secondFrequencyKernel secondKernelPair
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [if_pos hd, secondSourcePairKernel]
    rw [secondGaussTerm_test_factors, Finset.prod_union hd, map_mul, norm_mul,
      Complex.ofReal_mul, FirstPassCubeLabels.primeProductNorm_union p S T hd]
    ring
  · simp [hd]

theorem secondFrequencyKernel_eq_child_sectors
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    secondFrequencyKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e k H₁ H₂ W Y =
      (Y : ℂ) * ∑ z : SecondRayIndex, ∑ V ∈ F.powerset,
        secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z,V) *
          secondChildKernelPair p hp hcop hg F V (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
            m r c d e k (-k) (secondSourcePairKernel p e k H₁ H₂ W Y) := by
  rw [secondFrequencyKernel_eq_kernelPair,
    secondKernelPair_eq_children p hp hcop hg hinj hc hpr]

theorem inputConjugateRow_eq_truncated_add_tail
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) (K : Finset ι → Finset ι → Finset O) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖inputConjugateRow p hg F Ψ m c d H z‖ ^ 2) : ℂ)) =
      truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K +
        secondSourceTail p hp hg hinj F Ψ m c d H W Y K := by
  rw [inputConjugateRow_smoothed_frequency_blocks p hp hg hinj hc F Ψ m c d H W Y hY]
  unfold truncatedSecondSource secondSourceTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro G hG
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  have hs : Summable (fun k : O => secondFrequencyKernel p hp hg hinj F Ψ Ψ m
      (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
      (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y) := by
    simp_rw [← residualSecondMode_eq_frequencyKernel p hp hg hinj F G E.val
      (Finset.mem_powerset.mp E.property) Ψ Ψ m c d (fun U => H (G ∪ U)) (fun U => H (G ∪ U))]
    exact residualSecondMode_summable p hp hg hinj F G Ψ Ψ m c d
      (fun U => H (G ∪ U)) (fun U => H (G ∪ U))
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)
      (primeSubsetGenerator_ne_zero _ _) W Y hY
  rw [← hs.sum_add_tsum_subtype_compl (K G E.val)]
  simp only [secondSourceCommonCoefficient, mul_add, Finset.mul_sum]
  ring_nf

theorem truncatedSecondSource_eq_child_sectors
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) :
    truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K =
      ∑ G ∈ F.powerset, ∑ E : G.powerset,
        ∑ z : SecondRayIndex, ∑ V ∈ F.powerset, ∑ k ∈ K G E.val,
          ((Y : ℂ) * secondSourceCommonCoefficient p hg Ψ m c d G E.val *
            secondTotalWeight p hp hcop hg Ψ Ψ m
              (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
              (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k (z,V)) *
          secondChildKernelPair p hp hcop hg F V (secondRayMinus Ψ z) (secondRayPlus Ψ z)
            m (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
            (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k (-k)
            (secondSourcePairKernel p (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
              (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y) := by
  unfold truncatedSecondSource
  apply Finset.sum_congr rfl
  intro G hG
  apply Finset.sum_congr rfl
  intro E hE
  simp_rw [secondFrequencyKernel_eq_child_sectors p hp hg hinj hcop hc hpr]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro V hV
  apply Finset.sum_congr rfl
  intro k hk
  ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

theorem rowCoprimeMask_eq_of_span_eq {ι : Type*} (P : ι → Ideal O)
    (S : Finset ι) {a b : O} (hab : Ideal.span {a} = Ideal.span {b}) :
    rowCoprimeMask P S a = rowCoprimeMask P S b := by
  have hm (i : ι) : a ∈ P i ↔ b ∈ P i := by
    rw [← Ideal.span_singleton_le_iff_mem, ← Ideal.span_singleton_le_iff_mem, hab]
  simp only [rowCoprimeMask, hm]

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.ConjugateProfiles
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj

theorem secondPreColumn_zero_of_common_overlap
    (Ψ : O →* ℂ) (m c d e k : O) (H : Finset ι → ℂ) (G S : Finset ι)
    (hSG : ¬ Disjoint S G) :
    secondPreColumn p hp hcop hg Ψ (m * ∏ i ∈ G, p i) c d e k H S = 0 := by
  have hm : rowCoprimeMask (fun i => Ideal.span {p i}) S (m * ∏ i ∈ G, p i) = 0 := by
    rw [FirstPassCubeLabels.mask_mul _ hg S,
      commonProduct_mask p hg hinj S G, if_neg hSG, mul_zero]
  simp only [secondPreColumn, hm, mul_zero, zero_mul]

theorem weighted_secondChildKernelPair_congr_off_common
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (G E : Finset ι) (hEG : E ⊆ G) (F V : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d k₁ k₂ : O)
    (K lengthScale : Finset ι → Finset ι → ℂ)
    (hKL : ∀ S T, Disjoint G S → Disjoint G T → K S T = lengthScale S T) :
    let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    let r := secondMaskQuotient p E G hEG
    secondCommonWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k₁ k₂ V *
      secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ K =
    secondCommonWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k₁ k₂ V *
      secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ lengthScale := by
  dsimp only
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
  let r := secondMaskQuotient p E G hEG
  let w := secondCommonWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k₁ k₂ V
  unfold secondChildKernelPair
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  have hVN : Disjoint V N := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hN) disjoint_sdiff_self_right
  have hVM : Disjoint V M := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hM) disjoint_sdiff_self_right
  have hcoeff :
      w * (star (secondChildColumn p hp hcop hg Ψ₁ (m*r) (c*e*∏ i ∈ V, p i)
          (d*e*k₁) (fun _ => 1) N) *
        secondChildColumn p hp hcop hg Ψ₂ (m*r) (c*e*∏ i ∈ V, p i)
          (d*e*k₂) (fun _ => 1) M) =
      supportMobius (fun i => Ideal.span {p i}) V *
        star (secondPreColumn p hp hcop hg Ψ₁ (m*(e*r)) c d e k₁ (fun _ => 1) (V∪N)) *
        secondPreColumn p hp hcop hg Ψ₂ (m*(e*r)) c d e k₂ (fun _ => 1) (V∪M) := by
    rw [secondPreColumn_union p hp hcop hg hpr Ψ₁ m r c d e k₁ (fun _ => 1) V N hVN,
      secondPreColumn_union p hp hcop hg hpr Ψ₂ m r c d e k₂ (fun _ => 1) V M hVM]
    simp only [w, secondCommonWeight, star_mul]
    ring
  change w * (_ * K (V∪N) (V∪M)) = w * (_ * lengthScale (V∪N) (V∪M))
  conv_lhs => rw [← mul_assoc w, hcoeff]
  conv_rhs => rw [← mul_assoc w, hcoeff]
  by_cases hGN : Disjoint G (V∪N)
  · by_cases hGM : Disjoint G (V∪M)
    · rw [hKL _ _ hGN hGM]
    · have hz := secondPreColumn_zero_of_common_overlap p hp hcop hg hinj Ψ₂ m c d e k₂
        (fun _ => 1) G (V∪M) (fun h => hGM h.symm)
      rw [secondMaskQuotient_spec p E G hEG] at hz
      change secondPreColumn p hp hcop hg Ψ₂ (m*(e*r)) c d e k₂ (fun _ => 1) (V∪M) = 0 at hz
      rw [hz]
      ring
  · have hz := secondPreColumn_zero_of_common_overlap p hp hcop hg hinj Ψ₁ m c d e k₁
      (fun _ => 1) G (V∪N) (fun h => hGN h.symm)
    rw [secondMaskQuotient_spec p E G hEG] at hz
    change secondPreColumn p hp hcop hg Ψ₁ (m*(e*r)) c d e k₁ (fun _ => 1) (V∪N) = 0 at hz
    rw [hz, star_zero]
    ring

theorem weighted_secondRayChild_congr_off_common
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (G E : Finset ι) (hEG : E ⊆ G) (F V : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d k : O) (z : SecondRayIndex)
    (K lengthScale : Finset ι → Finset ι → ℂ)
    (hKL : ∀ S T, Disjoint G S → Disjoint G T → K S T = lengthScale S T) :
    let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    let r := secondMaskQuotient p E G hEG
    secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z,V) *
      secondChildKernelPair p hp hcop hg F V (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
        m r c d e k (-k) K =
    secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z,V) *
      secondChildKernelPair p hp hcop hg F V (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
        m r c d e k (-k) lengthScale := by
  dsimp only
  simp only [secondTotalWeight, mul_assoc]
  congr 1
  exact weighted_secondChildKernelPair_congr_off_common p hp hcop hg hinj hpr G E hEG F V
    (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z) m c d k (-k) K lengthScale hKL

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

end SecondPassArithmetic

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.PrincipalTruncation
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section

open ActualEisensteinCubic

theorem mem_secondExpansionPool {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (K : Finset ι → Finset ι → Finset O) (x : SecondExpansionData ι) :
    x ∈ secondExpansionPool F K ↔
      x.sourceCommon ⊆ F ∧ x.divisor ⊆ x.sourceCommon ∧ x.overlap ⊆ F ∧
        x.frequency ∈ K x.sourceCommon x.divisor := by
  simp only [secondExpansionPool, Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
  constructor
  · rintro ⟨G,hG,E,hE,V,hV,k,hk,hx⟩
    subst x
    exact ⟨hG,hE,hV,hk⟩
  · rintro ⟨hG,hE,hV,hk⟩
    exact ⟨x.sourceCommon,hG,x.divisor,hE,x.overlap,hV,x.frequency,hk,rfl⟩

theorem sum_secondExpansionPool {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (K : Finset ι → Finset ι → Finset O) (H : SecondExpansionData ι → ℂ) :
    (∑ x ∈ secondExpansionPool F K, H x) =
      ∑ G ∈ F.powerset, ∑ E ∈ G.powerset, ∑ V ∈ F.powerset, ∑ k ∈ K G E, H ⟨G,E,V,k⟩ := by
  unfold secondExpansionPool
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro G hG
    rw [Finset.sum_biUnion]
    · apply Finset.sum_congr rfl
      intro E hE
      rw [Finset.sum_biUnion]
      · apply Finset.sum_congr rfl
        intro V hV
        rw [Finset.sum_image]
        intro k hk k' hk' heq
        exact congrArg SecondExpansionData.frequency heq
      · intro V hV V' hV' hne
        apply Finset.disjoint_left.mpr
        intro x hx hx'
        obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨k',hk',heq⟩ := Finset.mem_image.mp hx'
        exact hne (congrArg SecondExpansionData.overlap heq).symm
    · intro E hE E' hE' hne
      apply Finset.disjoint_left.mpr
      intro x hx hx'
      obtain ⟨V,hV,hx⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨V',hV',hx'⟩ := Finset.mem_biUnion.mp hx'
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨k',hk',heq⟩ := Finset.mem_image.mp hx'
      exact hne (congrArg SecondExpansionData.divisor heq).symm
  · intro G hG G' hG' hne
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨E,hE,V,hV,hx⟩ := (by simpa only [Finset.mem_biUnion] using hx)
    obtain ⟨E',hE',V',hV',hx'⟩ := (by simpa only [Finset.mem_biUnion] using hx')
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k',hk',heq⟩ := Finset.mem_image.mp hx'
    exact hne (congrArg SecondExpansionData.sourceCommon heq).symm

theorem sum_secondExpansionSector {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (K : Finset ι → Finset ι → Finset O) (H : SecondExpansionData ι → ℂ) :
    (∑ R ∈ F.powerset, ∑ x ∈ secondExpansionSector F K R, H x) =
      ∑ x ∈ secondExpansionPool F K, H x := by
  simp only [secondExpansionSector, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  have hR : x.sourceCommon \ x.divisor ∈ F.powerset :=
    Finset.mem_powerset.mpr ((Finset.sdiff_subset).trans ((mem_secondExpansionPool F K x).mp hx).1)
  rw [Finset.sum_eq_single_of_mem (x.sourceCommon \ x.divisor) hR]
  · simp
  · intro R hR hne
    simp [Ne.symm hne]

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem truncatedSecondSource_eq_expansionPool
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) :
    truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K =
      ∑ z : SecondRayIndex, secondExpansionSource p hp hcop hg F Ψ m c d z
        (secondExpansionPool F K) H H W Y := by
  rw [truncatedSecondSource_eq_child_sectors p hp hg hinj hcop hc hpr]
  simp only [secondExpansionSource, sum_secondExpansionPool]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro G hG
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Finset.sum_coe_sort (s := G.powerset)]
  apply Finset.sum_congr rfl
  intro E hE
  apply Finset.sum_congr rfl
  intro V hV
  apply Finset.sum_congr rfl
  intro k hk
  have hs : (⟨G,E.val,V,k⟩ : SecondExpansionData ι).divisor ⊆
      (⟨G,E.val,V,k⟩ : SecondExpansionData ι).sourceCommon := Finset.mem_powerset.mp E.property
  simp only [secondExpansionQuotient_of_subset p _ hs]
  simp only [mul_assoc]

theorem truncatedSecondSource_eq_fixed_sectors
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) :
    truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K =
      ∑ z : SecondRayIndex, ∑ R ∈ F.powerset,
        secondExpansionSource p hp hcop hg F Ψ m c d z
          (secondExpansionSector F K R) H H W Y := by
  rw [truncatedSecondSource_eq_expansionPool p hp hcop hg hinj hc hpr]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [secondExpansionSource, sum_secondExpansionSector]

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
  (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)

include hc

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.FrequencyCutoffs
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem truncatedSecondSource_eq_nonzero_add_zero
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) :
    truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K =
      truncatedSecondSource p hp hg hinj F Ψ m c d H W Y (fun G E => (K G E).erase 0) +
        truncatedSecondZero p hg F Ψ m c d H W Y K := by
  unfold truncatedSecondSource truncatedSecondZero
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro G hG
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  by_cases h0 : 0 ∈ K G E.val
  · rw [← Finset.sum_erase_add _ _ h0]
    congr 1
    simp only [if_pos h0, secondFrequencyKernel_zero, Finset.union_empty,
      secondSourceCommonCoefficient]
    ring
  · simp only [Finset.erase_eq_of_notMem h0, if_neg h0, mul_zero, add_zero]

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (columnLog jLabel b0Label )
open JointLogSeparation (tripleCoefficient)

end SecondPassArithmetic

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.TruncatedSecondTransfer
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap

namespace SecondPassArithmetic

section

open ActualEisensteinCubic

theorem sum_secondDyadicSector {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype κ]
    (F : Finset ι) (K : Finset ι → Finset ι → Finset O) (R : Finset ι)
    (label : Finset ι → SecondExpansionData ι → κ) (H : SecondExpansionData ι → ℂ) :
    (∑ j : κ, ∑ x ∈ secondDyadicSector F K R label j, H x) =
      ∑ x ∈ secondExpansionSector F (fun G E => (K G E).erase 0) R, H x := by
  simp only [secondDyadicSector, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype κ]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem truncatedSecondSource_eq_zero_add_dyadic
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O)
    (label : Finset ι → SecondExpansionData ι → κ) :
    truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K =
      truncatedSecondZero p hg F Ψ m c d H W Y K +
      ∑ z : SecondRayIndex, ∑ R ∈ F.powerset, ∑ j : κ,
        secondExpansionSource p hp hcop hg F Ψ m c d z
          (secondDyadicSector F K R label j) H H W Y := by
  rw [truncatedSecondSource_eq_nonzero_add_zero, add_comm,
    truncatedSecondSource_eq_fixed_sectors p hp hcop hg hinj hc hpr]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro R hR
  simp only [secondExpansionSource, sum_secondDyadicSector]

end

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory
open ActualEisensteinCubic
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstToSecond
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem firstFreshSecondPoisson_fixed_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (H : Finset ι → ℂ) (ω : ℝ → ℂ) (X : ℝ) (c d : Eis)
    (r : FirstCoreIndex) (t Y : ℝ) (hY : 0 < Y) :
    firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m H ω X c d r t Y =
    ∑ G∈F.powerset,∑ U∈(F\G).powerset,∑ V∈(F\G).powerset,
      if Disjoint U V then overlapPairWeight p hg (firstCoreTwist negative χ Ψ r)
        ((m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i) (c*jLabel p B v ε₁ ε₂) d
        (firstCoreTest H (fun u => ω (Real.exp u))
          (columnLog p (primeProductNorm p D*X)) negative (-t) D) G U V *
        maskedSecondDual p hg hp hinj G U V rowMajorant Y else 0 := by
  unfold firstFreshSecondPoisson
  rw [← firstCoreInputRow_smoothed_second_poisson p hg hp hinj hc F D B v ε₁ ε₂ negative χ Ψ m
    H (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d r (-t) rowMajorant Y hY]
  rw [firstCoreInputRow_smoothed_sign p hg F D B v ε₁ ε₂ negative χ Ψ m H
    (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d r (-t) rowMajorant Y]
  simp_rw [inputConjugateRow_fixed_pool p hg hinj F D]
  exact inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F
    (firstCoreTwist negative χ Ψ r) ((m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i)
    (c*jLabel p B v ε₁ ε₂) d
    (firstCoreTest H (fun u => ω (Real.exp u))
      (columnLog p (primeProductNorm p D*X)) negative (-t) D) rowMajorant Y hY

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialArithmetic
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open MixedCrossSeparation (columnCoefficient)
open SevenEighths.InverseMoment SevenEighths.InverseInitialFibers
open CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → O) (hp : ∀ i, p i≠0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, λ₀∉Ideal.span {p i})

theorem sourceIdeal_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) :
    Function.Injective (sourceIdeal p) := by
  intro S T he
  simp only [sourceIdeal,FiniteGaussPhase.span_finset_prod] at he
  exact FirstCauchyArithmetic.family_product_injective _ hinj he

end SevenEighths.InverseInitialArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondSourceProfile
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem secondExpansionSource_marked_profile
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (F : Finset ι) (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex)
    (source : Finset (SecondExpansionData ι))
    (hE : ∀ x ∈ source, x.divisor ⊆ x.sourceCommon)
    (A₁ A₂ : Finset ι) (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) :
    secondExpansionSource p hp hcop hg F Ψ m c d z source
      (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ U) * W₁ (primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ U) * W₂ (primeProductNorm p U/X)) Φ Y =
    ∑ x ∈ source, expansionProfileWeight p hp hcop hg Ψ m c d z Y x *
      actualSecondProfileRow p hp hcop hg F (expansionProfileData p Ψ m c d z A₁ A₂ x)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X := by
  unfold secondExpansionSource
  apply Finset.sum_congr rfl
  intro x hx
  have he := hE x hx
  have hc := weighted_secondRayChild_congr_off_common p hp hcop hg hinj hpr
    x.sourceCommon x.divisor he F x.overlap Ψ Ψ m c d x.frequency z
    (secondSourcePairKernel p (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency
      (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ (x.sourceCommon ∪ U)) *
        W₁ (primeProductNorm p (x.sourceCommon ∪ U)/X))
      (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ (x.sourceCommon ∪ U)) *
        W₂ (primeProductNorm p (x.sourceCommon ∪ U)/X)) Φ Y)
    (secondSourcePairKernel p (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency
      (fun U => primeMark slots₁ lists₁ a₁ ((A₁ ∪ x.sourceCommon) ∪ U) *
        W₁ (primeProductNorm p x.sourceCommon * primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ ((A₂ ∪ x.sourceCommon) ∪ U) *
        W₂ (primeProductNorm p x.sourceCommon * primeProductNorm p U/X)) Φ Y)
    (by
      intro S T hGS hGT
      simp only [secondSourcePairKernel,primeProductNorm_union p x.sourceCommon S hGS,
        primeProductNorm_union p x.sourceCommon T hGT,Finset.union_assoc])
  dsimp only at hc
  rw [← secondExpansionQuotient_of_subset p x he] at hc
  rw [hc]
  simp only [expansionProfileWeight,actualSecondProfileRow,expansionProfileData,
    secondSourceCommonCoefficient,Complex.ofReal_pow]
  ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SlotAssignments
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

theorem primeMark_supported_assignments (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) :
    primeMark I L a A = ∑ q ∈ I.pi (fun i => L i ∩ A), slotAssignmentWeight I a q := by
  simp only [primeMark,primeSlot,Finset.sum_ite_mem,slotAssignmentWeight]
  exact Finset.prod_sum I (fun i => L i ∩ A) a

omit [DecidableEq σ] [DecidableEq ι] in
theorem indexedSlotAssignment_injective (I : Finset σ) :
    Function.Injective (indexedSlotAssignment (ι:=ι) I) := by
  intro q r h
  funext i hi
  have he := congrFun h (I.equivFin ⟨i,hi⟩)
  simpa [indexedSlotAssignment] using he

theorem indexedSlotAssignment_support (I : Finset σ) (L : σ → Finset ι)
    (A : Finset ι) (q : ∀ i ∈ I, ι) (hq : q ∈ I.pi (fun i => L i ∩ A))
    (j : Fin I.card) :
    indexedSlotAssignment I q j ∈ L ((I.equivFin).symm j).val ∩ A :=
  Finset.mem_pi.mp hq _ _

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondAssignedSource
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

omit [DecidableEq ι] [DecidableEq σ] in
theorem pairedSlotAssignment_injective (J₁ J₂ : Finset σ) :
    Function.Injective (pairedSlotAssignment (ι:=ι) J₁ J₂) := by
  intro q r h
  apply Prod.ext
  · apply indexedSlotAssignment_injective J₁
    funext j
    simpa only [pairedSlotAssignment,Fin.addCases_left] using congrFun h (Fin.castAdd J₂.card j)
  · apply indexedSlotAssignment_injective J₂
    funext j
    simpa only [pairedSlotAssignment,Fin.addCases_right] using congrFun h (Fin.natAdd J₁.card j)

theorem paired_primeMark_assignments (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ) (A : Finset ι) :
    star (primeMark J₁ L₁ a₁ A)*primeMark J₂ L₂ a₂ A =
      ∑ q ∈ (J₁.pi (fun i => L₁ i∩A)) ×ˢ (J₂.pi (fun i => L₂ i∩A)),
        pairedSlotWeight J₁ J₂ a₁ a₂ q := by
  rw [primeMark_supported_assignments,primeMark_supported_assignments]
  simp only [star_sum,Finset.sum_product,pairedSlotWeight,Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_comm

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondAssignedSum
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

omit [DecidableEq ι] [DecidableEq σ] in
lemma indexedSlotAssignment_apply (I : Finset σ) (q : ∀ i ∈ I,ι) (i : σ) (hi : i ∈ I) :
    indexedSlotAssignment I q (I.equivFin ⟨i,hi⟩) = q i hi := by
  exact congrArg (fun j : I => q j.val j.property) ((I.equivFin).symm_apply_apply ⟨i,hi⟩)

omit [DecidableEq ι] [DecidableEq σ] in
@[simp] theorem assignedSecondCoefficient_attach {Jo : ℕ}
    (J₁ J₂ : Finset σ) (a₁ a₂ : σ → ι → ℂ)
    (x : MarkedSecondSource ι Jo 0) (q : (∀ i ∈ J₁,ι) × (∀ i ∈ J₂,ι)) :
    assignedSecondCoefficient J₁ J₂ a₁ a₂ (attachPairedSlots J₁ J₂ (x,q)) =
      pairedSlotWeight J₁ J₂ a₁ a₂ q := by
  simp only [assignedSecondCoefficient,attachPairedSlots,attachSecondSlots,
    pairedSlotAssignment,Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply,pairedSlotWeight]

theorem paired_assignment_filter (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) (A : Finset ι) :
    ((J₁.pi L₁) ×ˢ (J₂.pi L₂)).filter (fun q => ∀ j, pairedSlotAssignment J₁ J₂ q j ∈ A) =
      (J₁.pi (fun i => L₁ i∩A)) ×ˢ (J₂.pi (fun i => L₂ i∩A)) := by
  ext q
  constructor
  · intro hq
    obtain ⟨hmem,hs⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq₁,hq₂⟩ := Finset.mem_product.mp hmem
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_pi.mpr
      intro i hi
      refine Finset.mem_inter.mpr ⟨Finset.mem_pi.mp hq₁ i hi,?_⟩
      simpa only [pairedSlotAssignment,Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply] using hs (Fin.castAdd J₂.card (J₁.equivFin ⟨i,hi⟩))
    · apply Finset.mem_pi.mpr
      intro i hi
      refine Finset.mem_inter.mpr ⟨Finset.mem_pi.mp hq₂ i hi,?_⟩
      simpa only [pairedSlotAssignment,Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply] using hs (Fin.natAdd J₁.card (J₂.equivFin ⟨i,hi⟩))
  · intro hq
    obtain ⟨hq₁,hq₂⟩ := Finset.mem_product.mp hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
    · exact Finset.mem_pi.mpr (fun i hi => (Finset.mem_inter.mp (Finset.mem_pi.mp hq₁ i hi)).1)
    · exact Finset.mem_pi.mpr (fun i hi => (Finset.mem_inter.mp (Finset.mem_pi.mp hq₂ i hi)).1)
    · intro j
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simpa only [pairedSlotAssignment,Fin.addCases_left] using
          (Finset.mem_inter.mp (indexedSlotAssignment_support J₁ L₁ _ q.1 hq₁ k)).2
      · simpa only [pairedSlotAssignment,Fin.addCases_right] using
          (Finset.mem_inter.mp (indexedSlotAssignment_support J₂ L₂ _ q.2 hq₂ k)).2

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondWeights
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem expansionProfileWeight_eq_signed (Ψ : Eis →* ℂ) (m c d : Eis)
    (z : SecondRayIndex) (Y : ℝ) (x : SecondExpansionData ι) :
    expansionProfileWeight p hp hcop hg Ψ m c d z Y x =
      (Y : ℂ)*secondRayCoefficient z*secondSignedSourceWeight p hp hcop hg Ψ m c d z x := by
  simp only [expansionProfileWeight,secondSignedSourceWeight,secondTotalWeight]
  ring

theorem secondExpansionSource_signed_profile
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (F : Finset ι) (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex)
    (source : Finset (SecondExpansionData ι)) (hE : ∀ x ∈ source, x.divisor ⊆ x.sourceCommon)
    (A₁ A₂ : Finset ι) (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) :
    secondExpansionSource p hp hcop hg F Ψ m c d z source
      (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ U) * W₁ (primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ U) * W₂ (primeProductNorm p U/X)) Φ Y =
    (Y : ℂ)*secondRayCoefficient z *
      ∑ x ∈ source, secondSignedSourceWeight p hp hcop hg Ψ m c d z x *
        actualSecondProfileRow p hp hcop hg F (expansionProfileData p Ψ m c d z A₁ A₂ x)
          slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X := by
  rw [secondExpansionSource_marked_profile p hp hcop hg hinj hpr (hE := hE)]
  simp only [expansionProfileWeight_eq_signed,Finset.mul_sum,mul_assoc]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondSourceAttachment
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

omit [DecidableEq ι] in
theorem attachSecondExpansion_injective {Jo : ℕ} (parent : SecondParentSource ι Jo) :
    Function.Injective (attachSecondExpansion parent) := by
  intro x y h
  exact congrArg MarkedSecondSource.second h

variable (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem attached_inherited_profile {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (x : SecondExpansionData ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex) :
    secondInheritedProfile p (attachSecondExpansion parent x) Ψ m z =
      expansionProfileData p Ψ (secondParentPuncture p m parent)
        (secondParentLabel p parent) (secondParentDivisor p parent) z ∅ ∅ x := rfl

theorem attached_signed_weight {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (x : SecondExpansionData ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex) :
    actualSecondSignedWeight p hp hcop hg Ψ
      (m*ConcretePrimeRowBridge.idealGenerator (attachSecondExpansion parent x).quotient) z
      (attachSecondExpansion parent x) =
    secondSignedSourceWeight p hp hcop hg Ψ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) z x := rfl

theorem secondExpansionSource_attached
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (source : Finset (SecondExpansionData ι)) (hE : ∀ x∈source,x.divisor ⊆ x.sourceCommon)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) :
    secondExpansionSource p hp hcop hg pool Ψ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) z source
      (fun U => primeMark slots₁ lists₁ a₁ U*W₁ (primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ U*W₂ (primeProductNorm p U/X)) Φ Y =
    (Y : ℂ)*secondRayCoefficient z *
      ∑ x∈source.image (attachSecondExpansion parent),
        actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X := by
  have he := secondExpansionSource_signed_profile p hp hcop hg hinj hpr pool Ψ
    (secondParentPuncture p m parent) (secondParentLabel p parent) (secondParentDivisor p parent)
    z source hE ∅ ∅ slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ X Y
  simp only [Finset.empty_union] at he
  rw [he]
  congr 1
  rw [Finset.sum_image (fun x hx y hy h => attachSecondExpansion_injective parent h)]
  apply Finset.sum_congr rfl
  intro x hx
  rw [attached_inherited_profile,attached_signed_weight]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondVariableCutoff
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem second_variable_original_support {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (pool residual : Finset ι) (R : Finset ι → Finset ι → ℝ)
    (label : Finset ι → SecondExpansionData ι → κ) (j : κ)
    (x : SecondExpansionData ι)
    (hx : x∈secondDyadicSector pool (secondVariableCutoff p parent R) residual label j) :
    x.sourceCommon ⊆ pool ∧ x.divisor ⊆ x.sourceCommon ∧ x.overlap ⊆ pool ∧
    x.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p (attachSecondExpansion parent x)) (R x.sourceCommon x.divisor) := by
  obtain ⟨hx,hlabel⟩ := Finset.mem_filter.mp hx
  obtain ⟨hx,hresidual⟩ := Finset.mem_filter.mp hx
  exact (mem_secondExpansionPool _ _ _).mp hx

theorem truncated_second_attached_variable [Fintype κ]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) (R : Finset ι → Finset ι → ℝ)
    (label : Finset ι → SecondExpansionData ι → κ) :
    truncatedSecondSource p hp hg hinj pool Ψ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent)
      (fun U => primeMark slots lists a U*W (primeProductNorm p U/X)) Φ Y
      (secondVariableCutoff p parent R) =
    truncatedSecondZero p hg pool Ψ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent)
      (fun U => primeMark slots lists a U*W (primeProductNorm p U/X)) Φ Y
      (secondVariableCutoff p parent R) +
    ∑ z : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y : ℂ)*secondRayCoefficient z *
        ∑ x∈(secondDyadicSector pool (secondVariableCutoff p parent R) residual label j).image
          (attachSecondExpansion parent),
          actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x *
            actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
              slots slots lists lists a a W W Φ Y X := by
  rw [truncatedSecondSource_eq_zero_add_dyadic p hp hcop hg hinj hc hpr
    pool Ψ (secondParentPuncture p m parent) (secondParentLabel p parent) (secondParentDivisor p parent)
    (fun U => primeMark slots lists a U*W (primeProductNorm p U/X)) Φ Y (secondVariableCutoff p parent R) label]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro residual hresidual
  apply Finset.sum_congr rfl
  intro j hj
  exact secondExpansionSource_attached p hp hcop hg hinj hpr parent _
    (fun x hx => (second_variable_original_support p parent pool residual R label j x hx).2.1)
    pool Ψ m z slots slots lists lists a a W W Φ X Y

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.SecondPrincipalCaller
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseSecondPrincipalCaller
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FourierBridge
open SecondPassIntegration CompletedHeight
open InverseMoment InversePrincipalEnergy RayFourExpansion
local notation "Eis" => ActualEisensteinCubic.O

section Arithmetic
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→Eis) (hp : ∀ i,p i≠0)

include hp in

theorem whole_columnLog (D U : Finset ι) (hDU : Disjoint D U) (X : ℝ) :
    columnLog p (primeProductNorm p D*X) (D∪U)=Real.log (primeProductNorm p U/X) := by
  unfold columnLog
  rw [primeProductNorm_union p D U hDU,
    mul_div_mul_left _ _ (primeProductNorm_pos p hp D).ne']

omit [DecidableEq σ] in

theorem primeMark_union_of_lists_disjoint (slots : Finset σ) (lists : σ→Finset ι)
    (coeff : σ→ι→ℂ) (D U : Finset ι)
    (hD : ∀ i∈slots,Disjoint (lists i) D) :
    primeMark slots lists coeff (D∪U)=primeMark slots lists coeff U := by
  unfold primeMark
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  have hh := Finset.disjoint_left.mp (hD i hi) hk
  simp only [Finset.mem_union,hh,false_or]

include hp in

theorem firstCoreTest_markedRadial (slots : Finset σ) (lists : σ→Finset ι)
    (coeff : σ→ι→ℂ) (D U : Finset ι) (hDU : Disjoint D U)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (negative : Bool) (X t : ℝ) (hX : 0<X) :
    firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
      (columnLog p (primeProductNorm p D*X)) negative (-t) D U =
    markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X U := by
  have ht : ∀ y : ℝ,logPhase (-t) (-y)=logPhase t y := by
    intro y
    unfold logPhase
    congr 1
    push_cast
    ring
  simp only [firstCoreTest,primeMark_union_of_lists_disjoint slots lists coeff D U hD,
    whole_columnLog p hp D U hDU X,ht,
    Real.exp_log (div_pos (primeProductNorm_pos p hp U) hX),
    markedRadial,Finset.empty_union,principalWindow]
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true,
    conjugateProfile_apply,uniformTwistedSchwartz_apply,normTwistedSource,star_mul] <;> ring

variable [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem secondInputCoefficient_overlap_zero
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Ψ : Eis→*ℂ) (m c d : Eis) (H : Finset ι→ℂ) (D U : Finset ι)
    (hDU : ¬Disjoint D U) :
    secondInputCoefficient p hg Ψ (m*∏ i∈D,p i) c d H U=0 := by
  rw [secondInputCoefficient_fixed_mask (p := p) (hg := hg),commonProduct_mask p hg hinj]
  split_ifs with h
  · exact (hDU h.symm).elim
  · exact zero_mul _

include hp in

theorem firstCoreTest_coefficient (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ) (D U : Finset ι)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (negative : Bool) (X t : ℝ) (hX : 0<X) (Ψ : Eis→*ℂ) (m c d : Eis) :
    secondInputCoefficient p hg Ψ (m*∏ i∈D,p i) c d
      (firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
        (columnLog p (primeProductNorm p D*X)) negative (-t) D) U =
    secondInputCoefficient p hg Ψ (m*∏ i∈D,p i) c d
      (markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X) U := by
  by_cases hd : Disjoint D U
  · unfold secondInputCoefficient
    rw [firstCoreTest_markedRadial p hp slots lists coeff D U hd hD om a b ha hs negative X t hX]
  · rw [secondInputCoefficient_overlap_zero p hg hinj Ψ m c d _ D U hd,
      secondInputCoefficient_overlap_zero p hg hinj Ψ m c d _ D U hd]

end Arithmetic

end SevenEighths.InverseSecondPrincipalCaller

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondParentInput
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers RayFourExpansion
open InverseInitialArithmetic (sourceIdeal)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [DecidableEq ι] in
theorem secondInputCoefficient_old_divisor_mask (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (S : Finset ι) :
    secondInputCoefficient p hg Ψ (m*d) c d H S = secondInputCoefficient p hg Ψ m c d H S := by
  rw [secondInputCoefficient_fixed_mask p hg Ψ m d c d H S]
  have hd := row_power_mul_mask_power (fun i => Ideal.span {p i}) hg S d 1 1 (by decide)
  simp only [pow_one] at hd
  unfold secondInputCoefficient
  calc
    _ = Ψ (∏ i∈S,p i)*rowCoprimeMask (fun i => Ideal.span {p i}) S m*
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S c^4*
      (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S d*
        rowCoprimeMask (fun i => Ideal.span {p i}) S d)*H S := by ring
    _ = _ := by rw [hd]

theorem inputConjugateRow_old_divisor_mask (F : Finset ι) (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (k : Eis) :
    inputConjugateRow p hg F Ψ (m*d) c d H k = inputConjugateRow p hg F Ψ m c d H k := by
  simp only [inputConjugateRow,FirstCauchyArithmetic.supportConjugateSum,secondInputCoefficient_old_divisor_mask]

theorem inputConjugateRow_puncture_span (F : Finset ι) (Ψ : Eis →* ℂ) (m₁ m₂ c d : Eis)
    (hspan : Ideal.span {m₁} = (Ideal.span {m₂} : Ideal Eis)) (H : Finset ι → ℂ) (k : Eis) :
    inputConjugateRow p hg F Ψ m₁ c d H k = inputConjugateRow p hg F Ψ m₂ c d H k := by
  simp only [inputConjugateRow,FirstCauchyArithmetic.supportConjugateSum,secondInputCoefficient,
    rowCoprimeMask_eq_of_span_eq (fun i => Ideal.span {p i}) _ hspan]

theorem fresh_input_parent_mask {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (F D : Finset ι) (hq : parent.quotient = sourceIdeal p D)
    (Ψ : Eis →* ℂ) (m : Eis) (H : Finset ι → ℂ) (k : Eis) :
    inputConjugateRow p hg F Ψ
      ((m*b0Label p parent.cube.support (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
        parent.cube.leftBit parent.cube.rightBit)*∏ i∈D,p i)
      (secondParentLabel p parent) (secondParentDivisor p parent) H k =
    inputConjugateRow p hg F Ψ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H k := by
  rw [←inputConjugateRow_old_divisor_mask]
  apply inputConjugateRow_puncture_span
  let b := b0Label p parent.cube.support (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
    parent.cube.leftBit parent.cube.rightBit
  let d := secondParentDivisor p parent
  change Ideal.span {((m*b)*(∏ i∈D,p i))*d} =
    (Ideal.span {(m*ConcretePrimeRowBridge.idealGenerator parent.quotient)*b*d} : Ideal Eis)
  rw [show ((m*b)*(∏ i∈D,p i))*d = (m*b*d)*(∏ i∈D,p i) by ring,
    show (m*ConcretePrimeRowBridge.idealGenerator parent.quotient)*b*d =
      (m*b*d)*ConcretePrimeRowBridge.idealGenerator parent.quotient by ring]
  simp only [←Ideal.span_singleton_mul_span_singleton,
    ConcretePrimeRowBridge.span_idealGenerator,hq,sourceIdeal]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondParentRadial
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers RayFourExpansion
open InverseInitialArithmetic (sourceIdeal)
open InversePrincipalEnergy InverseSecondPrincipalCaller
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem first_fresh_parent_radial_truncated
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (parent : SecondParentSource ι Jo) (F D : Finset ι)
    (hq : parent.quotient = sourceIdeal p D)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (core : FirstCoreIndex)
    (K : Finset ι → Finset ι → Finset Eis) :
    let Ψ₀ := firstCoreTwist negative χ Ψ core
    let H₀ := markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X
    firstFreshSecondPoisson p hp hg hinj F D parent.cube.support
      (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
      parent.cube.leftBit parent.cube.rightBit negative χ Ψ m (primeMark slots lists coeff) om X
      (∏ i∈parent.firstCommon,p i) (secondParentDivisor p parent) core t Y =
    truncatedSecondSource p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K +
    secondSourceTail p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K := by
  intro Ψ₀ H₀
  let H := firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
    (columnLog p (primeProductNorm p D*X)) negative (-t) D
  let m₀ := (m*b0Label p parent.cube.support
    (fun i=>parent.cube.leftExponent i+parent.cube.rightExponent i)
    parent.cube.leftBit parent.cube.rightBit)*∏ i∈D,p i
  have he (k : Eis) : inputConjugateRow p hg F Ψ₀ m₀
      (secondParentLabel p parent) (secondParentDivisor p parent) H k =
    inputConjugateRow p hg F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ k := by
    calc
      _ = inputConjugateRow p hg F Ψ₀ m₀ (secondParentLabel p parent)
          (secondParentDivisor p parent) H₀ k := by
        unfold inputConjugateRow FirstCauchyArithmetic.supportConjugateSum
        apply Finset.sum_congr rfl
        intro U hU
        rw [firstCoreTest_coefficient p hp hg hinj slots lists coeff D U hD om a b ha hs negative X t hX]
      _ = _ := fresh_input_parent_mask p hg parent F D hq Ψ₀ m H₀ k
  rw [firstFreshSecondPoisson_fixed_pool p hp hg hinj hc (hY:=hY)]
  rw [←inputConjugateRow_smoothed_second_poisson p hg hp hinj hc _ _ _ _ _ _ _ _ hY]
  change (∑' k : Eis,rowMajorant (‖ConcreteTraceCRT.eisEmbedding k‖^2/Y)*
    (‖inputConjugateRow p hg F Ψ₀ m₀ (secondParentLabel p parent)
      (secondParentDivisor p parent) H k‖^2 : ℝ)) = _
  simp_rw [he]
  exact inputConjugateRow_eq_truncated_add_tail p hp hg hinj hc F Ψ₀ (secondParentPuncture p m parent)
    (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y hY K

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondFullSource
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers RayFourExpansion
open InverseInitialArithmetic (sourceIdeal)
open InversePrincipalEnergy InverseSecondPrincipalCaller
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ] [Fintype κ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem first_parent_full_second_source
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (parent : SecondParentSource ι Jo) (F D : Finset ι)
    (hq : parent.quotient = sourceIdeal p D)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (X height Y : ℝ) (hX : 0<X) (hY : 0<Y) (core : FirstCoreIndex)
    (R : Finset ι → Finset ι → ℝ) (label : Finset ι → SecondExpansionData ι → κ) :
    let Ψ₀ := firstCoreTwist negative χ Ψ core
    let V := principalWindow om a b ha hs negative height
    let H₀ := markedRadial p slots lists coeff ∅ V X
    let K := secondVariableCutoff p parent R
    firstFreshSecondPoisson p hp hg hinj F D parent.cube.support
      (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
      parent.cube.leftBit parent.cube.rightBit negative χ Ψ m (primeMark slots lists coeff) om X
      (∏ i∈parent.firstCommon,p i) (secondParentDivisor p parent) core height Y =
    truncatedSecondZero p hg F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K +
    (∑ ray : SecondRayIndex,∑ residual∈F.powerset,∑ j : κ,
      (Y : ℂ)*secondRayCoefficient ray *
        ∑ x∈(secondDyadicSector F K residual label j).image (attachSecondExpansion parent),
          actualSecondSignedWeight p hp hcop hg Ψ₀ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x *
            actualSecondProfileRow p hp hcop hg F (secondInheritedProfile p x Ψ₀ m ray)
              slots slots lists lists coeff coeff V V rowMajorant Y X) +
    secondSourceTail p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K := by
  intro Ψ₀ V H₀ K
  have htest : H₀=(fun U=>primeMark slots lists coeff U*V (primeProductNorm p U/X)) := by
    funext U
    simp only [H₀,markedRadial,Finset.empty_union]
  have hret := truncated_second_attached_variable p hp hcop hg hinj hc hpr parent F Ψ₀ m
    slots lists coeff V rowMajorant X Y R label
  rw [←htest] at hret
  calc
    _ = truncatedSecondSource p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
        (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K +
        secondSourceTail p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
          (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K :=
      first_fresh_parent_radial_truncated p hp hg hinj hc parent F D hq negative χ Ψ m
        slots lists coeff hD om a b ha hs X height Y hX hY core K
    _ = _ := congrArg (fun v=>v + secondSourceTail p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
        (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K) hret

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.FirstPriorityParents
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseFirstPriorityParents
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic
local notation "O" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}

variable (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

theorem parent_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) :
    Function.Injective (parent p (Jo:=Jo)) := by
  intro x y h
  apply Source.ext
  · exact congrArg SecondParentSource.cube h
  · exact congrArg SecondParentSource.firstCommon h
  · exact congrArg SecondParentSource.firstDivisor h
  · exact sourceIdeal_injective p hinj (congrArg SecondParentSource.quotient h)
  · exact congrArg SecondParentSource.oldAssigned h

omit [DecidableEq ι] in
theorem appendParent_injective {Jn : ℕ} :
    Function.Injective (fun q : SecondParentSource ι Jo × (Fin Jn→SmoothMobiusCorrection.PrimeIdeal)=>
      appendParent q.1 q.2) := by
  intro q r h
  apply Prod.ext
  · simpa only [forget_append] using congrArg forgetAppended h
  · funext i
    simpa only [appendParent,Fin.addCases_right] using
      congrArg (fun x : SecondParentSource ι (Jo+Jn)=>x.oldAssigned (Fin.natAdd Jo i)) h

omit [DecidableEq σ] in
theorem attach_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) (J : Finset σ) :
    Function.Injective (attach p (Jo:=Jo) J) := by
  intro q r h
  have he := @appendParent_injective ι Jo (J.card+J.card)
    (parent p q.1,fun i=>sourcePrime p (pairedSlotAssignment J J q.2 i))
    (parent p r.1,fun i=>sourcePrime p (pairedSlotAssignment J J r.2 i)) h
  apply Prod.ext
  · exact parent_injective p hinj (congrArg Prod.fst he)
  · apply pairedSlotAssignment_injective J J
    funext i
    exact hinj (congrArg (fun q : SecondParentSource ι Jo ×
      (Fin (J.card+J.card)→SmoothMobiusCorrection.PrimeIdeal)=>(q.2 i).val) he)

omit [DecidableEq σ] in
theorem coefficient_attach (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (J : Finset σ) (a : σ→ι→ℂ) (w : Source ι Jo→ℂ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    coefficient p J a w (attach p J q)=w q.1*pairedSlotWeight J J a a q.2 :=
  (attach_injective p hinj J).extend_apply _ _ _

variable (hp : ∀ i,p i≠0) (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end SevenEighths.InverseFirstPriorityParents

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.WholePriorityParents
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMomentWholePriorityParents
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}

variable (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

theorem sum_wholeAssignmentSource (extra : Source ι Jo→Finset ι) {A : Type*} [AddCommMonoid A]
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (H : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))→A) :
    ∑ q∈wholeAssignmentSource extra source negative J lists,H q =
      ∑ x∈source,∑ q∈(J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))×ˢ
        (J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x)),H (x,q) := by
  rw [wholeAssignmentSource,Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x hx
  rw [←Finset.sum_filter]
  dsimp only
  rw [paired_assignment_filter]

theorem sum_wholeAssignedParents (extra : Source ι Jo→Finset ι) (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    {A : Type*} [AddCommMonoid A] (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (H : SecondParentSource ι (Jo+(J.card+J.card))→A) :
    ∑ y∈wholeAssignedParents p extra source negative J lists,H y =
      ∑ x∈source,∑ q∈(J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))×ˢ
        (J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x)),H (attach p J (x,q)) := by
  rw [wholeAssignedParents,Finset.sum_image (fun _ _ _ _ h=>attach_injective p hinj J h)]
  exact sum_wholeAssignmentSource extra source negative J lists _

theorem wholePaired_parent_sum (extra : Source ι Jo→Finset ι) (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (H : SecondParentSource ι Jo→ℂ) :
    (∑ x∈source,w x*(star (primeMark J lists a (wholeExtractedSupport extra negative x))*
      primeMark J lists a (wholeExtractedSupport extra negative x))*H (parent p x)) =
    ∑ y∈wholeAssignedParents p extra source negative J lists,
      coefficient p J a w y*H (forgetAppended y) := by
  rw [sum_wholeAssignedParents p extra hinj]
  apply Finset.sum_congr rfl
  intro x hx
  rw [paired_primeMark_assignments]
  simp only [Finset.mul_sum,Finset.sum_mul,coefficient_attach p hinj,forget_attach]

theorem wholePaired_parent_sq_sum (extra : Source ι Jo→Finset ι) (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (H : SecondParentSource ι Jo→ℂ) :
    (∑ x∈source,w x*(‖primeMark J lists a (wholeExtractedSupport extra negative x)‖^2 : ℝ)*H (parent p x)) =
    ∑ y∈wholeAssignedParents p extra source negative J lists,
      coefficient p J a w y*H (forgetAppended y) := by
  simpa only [Complex.sq_norm,Complex.normSq_eq_conj_mul_self,starRingEnd_apply] using
    wholePaired_parent_sum p extra hinj source negative J lists a w H

lemma mem_wholeAssignmentSource (extra : Source ι Jo→Finset ι) (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι)
    (x : Source ι Jo) (q : (∀ i∈J,ι)×(∀ i∈J,ι)) :
    (x,q)∈wholeAssignmentSource extra source negative J lists ↔ x∈source ∧
      q∈(J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))×ˢ
        (J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x)) := by
  rw [←paired_assignment_filter]
  simp only [wholeAssignmentSource,Finset.mem_filter,Finset.mem_product]
  tauto

theorem mem_wholeAssignedParents (extra : Source ι Jo→Finset ι) (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (y : SecondParentSource ι (Jo+(J.card+J.card))) :
    y∈wholeAssignedParents p extra source negative J lists ↔
      ∃ x∈source,∃ q∈(J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))×ˢ
        (J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x)),attach p J (x,q)=y := by
  simp only [wholeAssignedParents,Finset.mem_image]
  constructor
  · rintro ⟨⟨x,q⟩,hq,he⟩
    exact ⟨x,(mem_wholeAssignmentSource extra source negative J lists x q).mp hq |>.1,
      q,(mem_wholeAssignmentSource extra source negative J lists x q).mp hq |>.2,he⟩
  · rintro ⟨x,hx,q,hq,he⟩
    exact ⟨(x,q),(mem_wholeAssignmentSource extra source negative J lists x q).mpr ⟨hx,hq⟩,he⟩

end SevenEighths.InverseMomentWholePriorityParents

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.PrioritySecondSource
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InversePrioritySecondSource
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents
open InversePrincipalEnergy InverseSecondPrincipalCaller RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable {Jo : ℕ} (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

theorem quotientSupport_parent (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (x : Source ι Jo) : quotientSupport p (parent p x)=x.quotientSupport :=
  (sourceIdeal_injective p hinj).extend_apply _ _ _

omit [DecidableEq σ] in
theorem quotientSupport_attach (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (J : Finset σ) (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    quotientSupport p (attach p J q)=q.1.quotientSupport :=
  quotientSupport_parent p hinj q.1

omit [DecidableEq σ] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem residualLists_disjoint (negative : Bool) (lists : σ→Finset ι)
    (y : SecondParentSource ι Jo) (i : σ) :
    Disjoint (residualLists p negative lists y i) (quotientSupport p y) := by
  apply Finset.disjoint_left.mpr
  intro q hq hd
  exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_union_right _ hd)

variable (hp : ∀ i,p i≠0)
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem parentPoisson_full [Fintype κ]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (y : SecondParentSource ι Jo) (pool : Finset ι)
    (hq : y.quotient=sourceIdeal p (quotientSupport p y))
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ) :
    let Ψ₀ := firstCoreTwist negative (if negative then r.1 else r.2) Ψ core
    let V := principalWindow om lo hi hlo hs negative t
    let H := markedRadial p (slots\J) (residualLists p negative lists y) a ∅ V X
    let K := secondVariableCutoff p y R
    parentPoisson p hp hg hinj pool negative Ψ m slots J lists a om X t Y r core y =
      truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
        (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K +
      (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
        (Y:ℂ)*secondRayCoefficient ray *
          ∑ x∈(secondDyadicSector pool K residual label j).image (attachSecondExpansion y),
            retainedRow p hp hcop hg pool negative Ψ₀ m slots J lists a V X Y ray x) +
      secondSourceTail p hp hg hinj pool Ψ₀ (secondParentPuncture p m y)
        (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K := by
  intro Ψ₀ V H K
  have hsum : (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈(secondDyadicSector pool K residual label j).image (attachSecondExpansion y),
          actualSecondSignedWeight p hp hcop hg Ψ₀
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ₀ m ray)
            (slots\J) (slots\J) (residualLists p negative lists y) (residualLists p negative lists y)
            a a V V rowMajorant Y X) =
    ∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈(secondDyadicSector pool K residual label j).image (attachSecondExpansion y),
          retainedRow p hp hcop hg pool negative Ψ₀ m slots J lists a V X Y ray x := by
    apply Finset.sum_congr rfl
    intro ray hray
    apply Finset.sum_congr rfl
    intro residual hresidual
    apply Finset.sum_congr rfl
    intro j hj
    apply congrArg ((Y:ℂ)*secondRayCoefficient ray * ·)
    apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    rfl
  have he := first_parent_full_second_source p hp hcop hg hinj hc hpr y pool (quotientSupport p y) hq
    negative (if negative then r.1 else r.2) Ψ m (slots\J) (residualLists p negative lists y) a
    (fun i _=>residualLists_disjoint p negative lists y i) om lo hi hlo hs X t Y hX hY core R label
  exact he.trans (congrArg (fun z : ℂ=>truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K + z +
    secondSourceTail p hp hg hinj pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K) hsum)

end SevenEighths.InversePrioritySecondSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.WholePriorityPhysical
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMomentWholePriorityPhysical
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents
open InverseMomentWholePriorityParents InversePrioritySecondSource
open InversePrincipalEnergy InverseSecondPrincipalCaller RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ] [Fintype κ]
variable {Jo : ℕ} (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem whole_parent_full
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ)
    (y : SecondParentSource ι Jo) (hq : y.quotient=sourceIdeal p (quotientSupport p y)) :
    parentPoisson p hp hg hinj pool negative Ψ m slots J
      (fun i=>lists i\extra y.cube) a om X t Y r core y =
    fullPhysical p hp hcop hg hinj extra pool negative Ψ m slots J lists a
      (principalWindow om lo hi hlo hs negative t) X Y r core R label y :=
  parentPoisson_full p hp hcop hg hinj hc hpr y pool hq negative Ψ m slots J
    (fun i=>lists i\extra y.cube) a om lo hi hlo hs X t Y hX hY r core R label

theorem whole_signed_source_full_oai
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (source : Finset (Source ι Jo)) (w : Source ι Jo→ℂ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ) :
    (∑ x∈source,w x*(‖primeMark J lists a
      (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots J
        (fun i=>lists i\extra x.cube) a om X t Y r core (parent p x)) =
    ∑ y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
      coefficient p J a w y *
        fullPhysical p hp hcop hg hinj extra pool negative Ψ m slots J lists a
          (principalWindow om lo hi hlo hs negative t) X Y r core R label y := by
  have he := wholePaired_parent_sq_sum p (fun x=>extra x.cube) hinj source negative J lists a w
    (fun y=>parentPoisson p hp hg hinj pool negative Ψ m slots J
      (fun i=>lists i\extra y.cube) a om X t Y r core y)
  refine he.trans ?_
  apply Finset.sum_congr rfl
  intro y hy
  obtain ⟨x,hx,q,hq,rfl⟩ :=
    (mem_wholeAssignedParents p (fun x=>extra x.cube) source negative J lists y).mp hy
  rw [forget_attach]
  apply congrArg (coefficient p J a w (attach p J (x,q))* ·)
  have hquot : (attach p J (x,q)).quotient=sourceIdeal p (quotientSupport p (attach p J (x,q))) := by
    rw [quotientSupport_attach p hinj];rfl
  exact whole_parent_full p hp hcop hg hinj hc hpr extra pool negative Ψ m slots J lists a
    om lo hi hlo hs X t Y hX hY r core R label (attach p J (x,q)) hquot

end SevenEighths.InverseMomentWholePriorityPhysical

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.SevenEighths.InverseMomentWholePriorityPhysical.whole_signed_source_full_oai.{u_1, u_2, u_3} := @OAI.SevenEighths.InverseMomentWholePriorityPhysical.whole_signed_source_full_oai.{u_1, u_2, u_3}
