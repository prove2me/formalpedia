-- Prove2me | solution 1 for OAI.SevenEighths.ProbePhysical.idealMarkedLocalFactor_eq_source
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:28:10.279869+00:00
-- url     : https://prove2.me/submissions/114e01b0-d4bd-4a6f-9f4f-5fc99f736091

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027
import Theorems.Thm_OAI_SevenEighths_ProbePrimePower_actualSextic_neg_one_sq
import Theorems.Thm_OAI_SevenEighths_ProbePrimePower_localGamma_norm_one

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

open scoped BigOperators Classical

namespace FiniteGaussPhase

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem norm_angularFactor (a : O) (ha : a ≠ 0) : ‖angularFactor a‖ = 1 := by
  rw [angularFactor, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero ha))

theorem angularFactor_mul_star (a : O) (ha : a ≠ 0) :
    angularFactor a * star (angularFactor a) = 1 := by
  rw [← starRingEnd_apply, Complex.mul_conj', norm_angularFactor a ha]
  norm_num

end FiniteGaussPhase

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

end QuadraticGaussRay

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

namespace CompletedGauss

open ActualEisensteinCubic

open ActualEisensteinCubic ConcreteTraceCRT

theorem product_primary {ι : Type*} [Fintype ι] (p : ι → O)
    (hp : ∀ i, lambda ^ 2 ∣ p i - 1) : lambda ^ 2 ∣ (∏ i, p i) - 1 := by
  apply primary_multiset_prod (Finset.univ.val.map p)
  intro r hr
  obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hr
  exact hp i

theorem cubicRow_product_mk {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hI : primaryGenerator (Ideal.span {∏ i, p i}) ≠ 0) (a : O) :
    cubicRow (Ideal.span {∏ i, p i}) hI (Ideal.Quotient.mk (Ideal.span {∏ i, p i}) a) =
      ∏ i, (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 2)
        (Ideal.Quotient.mk (Ideal.span {p i}) a) := by
  rw [cubicRow_mk]
  symm
  exact (productPrimeIndexEquiv p hcop).prod_comp (fun P =>
    (canonicalSextic P.val (primeIndex_good _ hI P) ^ 2) (Ideal.Quotient.mk P.val a))

theorem gaussTwo_eq_canonicalProductGauss {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (hI : primaryGenerator (Ideal.span {∏ i, p i}) ≠ 0) :
    gaussTwo (Ideal.span {∏ i, p i}) hI =
      FiniteGaussPhase.canonicalProductGauss p hp hcop hgood (fun _ => 2) := by
  have hpall : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hgen := primaryGenerator_span (∏ i, p i) hpall (product_primary p hprimary)
  let : Finite (O ⧸ Ideal.span {∏ i, p i}) := finite_quotient_span hpall
  let : Fintype (O ⧸ Ideal.span {∏ i, p i}) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {primaryGenerator (Ideal.span {∏ i, p i})}) := finite_quotient_span hI
  let : Fintype (O ⧸ Ideal.span {primaryGenerator (Ideal.span {∏ i, p i})}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (primaryGenerator_spec (Ideal.span {∏ i, p i}) hI).1
  have hsum :
      (∑ x : O ⧸ Ideal.span {primaryGenerator (Ideal.span {∏ i, p i})},
        cubicRow (Ideal.span {∏ i, p i}) hI (e x) *
          eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
            (primaryGenerator (Ideal.span {∏ i, p i})) hI x) =
      (∑ x : O ⧸ Ideal.span {∏ i, p i},
        (∏ i, (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 2)
          (FiniteGaussPhase.productElementCRT p hcop x i)) *
          eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
            (∏ i, p i) hpall x) := by
    apply Fintype.sum_equiv e.toEquiv
    intro x
    change cubicRow (Ideal.span {∏ i, p i}) hI (e x) *
        eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
          (primaryGenerator (Ideal.span {∏ i, p i})) hI x =
      (∏ i, (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 2)
        (FiniteGaussPhase.productElementCRT p hcop (e x) i)) *
        eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
          (∏ i, p i) hpall (e x)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [e, Ideal.quotEquivOfEq_mk, cubicRow_product_mk p hcop hgood hI,
      FiniteGaussPhase.productElementCRT_mk, eisTraceModChar, IdealGaussCRT.traceModChar_mk, hgen]
  change _ / _ = _ / _
  rw [hsum, hgen]

end CompletedGauss

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.CrossFactorization
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

namespace QuadraticGaussRay
open EisensteinEPrimaryPhase ActualEisensteinCoordinates ActualEisensteinCubic

theorem quadraticRayValue_square (r : Coord) (hr : odd r) :
    quadraticRayValue (mul r r) = 1 := by
  have hi : (Complex.I : ℂ)⁻¹ = -Complex.I := by
    apply inv_eq_of_mul_eq_one_right
    norm_num
  have h : mul r r = (1, 0) ∨ mul r r = (3, 3) ∨ mul r r = (0, 1) := by
    decide +revert
  rcases h with h | h | h
  · rw [h]
    change breveGaussianFourTerms 1 0 = 1
    rw [breveGaussianFourTerms_formula]
    norm_num [hi]
  · rw [h]
    change breveGaussianFourTerms 3 3 = 1
    rw [breveGaussianFourTerms_formula]
    norm_num [hi]
  · rw [h]
    change breveGaussianFourTerms 0 1 = 1
    rw [breveGaussianFourTerms_formula]
    norm_num [hi]
    ring

end QuadraticGaussRay

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.ConjugateLevelAction
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators
namespace QuadraticAllOddCRT
open ActualEisensteinCubic
open QuadraticGaussRay hiding O
open ActualEisensteinCoordinates hiding O omega
open EisensteinEPrimaryPhase (Coord odd)

lemma quadraticRaySign_sq (r s : Coord) (hr : odd r) (hs : odd s) :
    quadraticRaySign r s^2=1 := by
  unfold quadraticRaySign
  rw [if_pos ⟨hr,hs⟩]
  split_ifs <;> norm_num

end QuadraticAllOddCRT

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Gauss
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma gaussTwo_eq_gaussSum (I : Ideal O) (hI : Admissible I) :
    let : Finite (O ⧸ Ideal.span {primaryGenerator I}) := finite_quotient_span hI.2
    let : Fintype (O ⧸ Ideal.span {primaryGenerator I}) := Fintype.ofFinite _
    gaussTwo I hI.2 = gaussSum (principalCubicCharacter I hI)
      (eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
        (primaryGenerator I) hI.2) / (‖eisEmbedding (primaryGenerator I)‖ : ℂ) := by
  dsimp only [gaussTwo, gaussSum, principalCubicCharacter, quotientCharacterTransport, cubicQuotientCharacter]
  congr 1

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Phase
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates QuadraticGaussRay ConcreteTraceCRT
open QuadraticAllOddCRT
local notation "O" => ActualEisensteinCubic.O

theorem G_mul (a b : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hb : EisensteinEPrimaryPhase.odd (residue b)) :
    G (a * b) = G a * G b * reciprocitySign a b := by
  change fixedGValue (residue (a * b)) = fixedGValue (residue a) * fixedGValue (residue b) * reciprocitySign a b
  simp only [fixedGValue, ← fixed_two_mk_eq_residue_lift]
  simp only [map_mul, mul_inv_rev, residue_mul]
  rw [quadraticRayValue_mul _ _ ha hb]
  unfold reciprocitySign
  ring

theorem reciprocitySign_mul_right (a b c : O) :
    reciprocitySign a (b * c) = reciprocitySign a b * reciprocitySign a c := by
  simp only [reciprocitySign, residue_mul, quadraticRaySign_mul_right, Int.cast_mul]

theorem reciprocitySign_sq (a b : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hb : EisensteinEPrimaryPhase.odd (residue b)) :
    reciprocitySign a b ^ 2 = 1 := by
  unfold reciprocitySign
  exact_mod_cast quadraticRaySign_sq (residue a) (residue b) ha hb

theorem reciprocitySign_cube_right (a b : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hb : EisensteinEPrimaryPhase.odd (residue b)) :
    reciprocitySign a (b ^ 3) = reciprocitySign a b := by
  rw [show b ^ 3 = b ^ 2 * b by ring, reciprocitySign_mul_right,
    pow_two, reciprocitySign_mul_right]
  have hs := reciprocitySign_sq a b ha hb
  calc
    _ = reciprocitySign a b ^ 2 * reciprocitySign a b := by ring
    _ = reciprocitySign a b := by rw [hs, one_mul]

theorem quadraticRayValue_cube (r : EisensteinEPrimaryPhase.Coord)
    (hr : EisensteinEPrimaryPhase.odd r) :
    quadraticRayValue (EisensteinEPrimaryPhase.mul
      (EisensteinEPrimaryPhase.mul r r) r) = quadraticRayValue r := by
  have he : ∀ r : EisensteinEPrimaryPhase.Coord, EisensteinEPrimaryPhase.odd r →
      quadraticRayExponent (EisensteinEPrimaryPhase.mul
        (EisensteinEPrimaryPhase.mul r r) r) = quadraticRayExponent r := by decide
  rw [quadraticRayValue_eq_fourthRoot _ (odd_mul _ _ (odd_mul _ _ hr hr) hr),
    he r hr, ← quadraticRayValue_eq_fourthRoot r hr]

theorem G_cube (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hu : IsUnit (Ideal.Quotient.mk cubicTwoIdeal a)) :
    G (a ^ 3) = quadraticRayValue (residue a) := by
  have hχ := congrArg
    (fun η : MulChar (O ⧸ cubicTwoIdeal) O => η (Ideal.Quotient.mk cubicTwoIdeal a))
    (cubicChar_pow_three cubicTwoIdeal cubicTwoIdeal_good)
  simp only [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), MulChar.one_apply hu] at hχ
  have hc := congrArg eisEmbedding hχ
  simp only [map_pow, map_one] at hc
  change fixedGValue (residue (a ^ 3)) = quadraticRayValue (residue a)
  simp only [fixedGValue, ← fixed_two_mk_eq_residue_lift]
  simp only [map_pow, hc, inv_one, one_mul]
  rw [show a ^ 3 = (a * a) * a by ring, residue_mul, residue_mul]
  exact quadraticRayValue_cube (residue a) ha

end SevenEighths.ProbePhase
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Physical
namespace OAI

noncomputable section

open scoped BigOperators Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open CubicEisenstein ProbeCompleted ProbeRow

local notation "O" => ActualEisensteinCubic.O

theorem sexticGauss_coefficient_mk (s : O) (a : O) :
    idealRowHom (GaussianShiftedPartition.representative s
      (Ideal.Quotient.mk (Ideal.span {s}) a)) (Ideal.span {s}) =
      idealRowHom a (Ideal.span {s}) := by
  apply idealRowHom_congr_mod
  apply Ideal.Quotient.eq.mp
  exact GaussianShiftedPartition.representative_spec _ _

attribute [local irreducible] markedPhysicalProbe

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Gauss
namespace OAI

namespace SevenEighths.ProbeGauss
open scoped BigOperators Classical
noncomputable section

theorem gauss_inverse_pair {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum χ⁻¹ ψ = χ (-1) * (Fintype.card F : ℂ) := by
  rw [← mul_gaussSum_inv_eq_gaussSum χ⁻¹, mul_left_comm,
    gaussSum_mul_gaussSum_eq_card hχ hψ, MulChar.inv_apply', inv_neg_one]

theorem normalizedGauss_inverse_pair {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    normalizedGauss χ ψ * normalizedGauss χ⁻¹ ψ = χ (-1) := by
  have hq : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : (Real.sqrt (Fintype.card F) : ℂ) ^ 2 = (Fintype.card F : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card F) : (0 : ℝ) ≤ _)
  unfold normalizedGauss
  rw [div_mul_div_comm, ← pow_two, hs, gauss_inverse_pair χ ψ hχ hψ]
  exact mul_div_cancel_right₀ _ hq

end
end SevenEighths.ProbeGauss

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Canonical
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentCanonical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCorrelation

theorem actualSextic_order_six (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    orderOf (actualSextic P hg) = 6 := by
  let Φ : MulChar (O ⧸ P) O →* MulChar (O ⧸ P) ℂ :=
    MulChar.ringHomCompHom eisEmbedding
  have hΦ : Function.Injective Φ := by
    intro x y h
    apply MulChar.ext
    intro t
    apply eisEmbedding_injective
    exact congrArg (fun f : MulChar (O ⧸ P) ℂ => f t) h
  exact (orderOf_injective Φ hΦ _).trans (sexticChar_order P hg hchar)

end SevenEighths.CenteredMomentCanonical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Sextic
namespace OAI

noncomputable section
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem actualSextic_pow_eq_one_iff (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2) (n : ℕ) :
    actualSextic P hg ^ n = 1 ↔ 6 ∣ n := by
  rw [← orderOf_dvd_iff_pow_eq_one, CenteredMomentCanonical.actualSextic_order_six P hg hc]

end SevenEighths.ProbePrimePower
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CongruenceScalar
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition
local notation "O" => ActualEisensteinCubic.O

lemma exactQuotient_spec (a b : O) (h : b ∣ a) : a = b * exactQuotient a b h :=
  Classical.choose_spec h

end SevenEighths.ProbePrimePower
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LiftedFourier
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition
local notation "O" => ActualEisensteinCubic.O

lemma quotientTrace_split_frequency (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (H d v : O) :
    quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ ((H-b*d)*v)) =
      quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ (H*v)) *
        quotientTrace a ha (Ideal.Quotient.mk _ ((-v)*d)) := by
  have hs := quotientTrace_conductor_scale a b ((-v)*d) ha hb 1
  simp only [mul_one, map_one] at hs
  rw [show (H-b*d)*v = H*v+b*((-v)*d) by ring, map_add, AddChar.map_add_eq_mul, hs]

lemma quotientFourier_congr (p a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (H : O) (he : a=b) :
    quotientFourier p a ha χ H = quotientFourier p b hb χ H := by
  subst b
  rfl

lemma primePowerGauss_eq_quotientFourier (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (H : O) :
    primePowerGauss p hp χ n H =
      quotientFourier p (p*p^n) (mul_ne_zero hp (pow_ne_zero _ hp)) χ H := by
  unfold primePowerGauss conductorFourier quotientFourier
  apply tsum_congr
  intro d
  have hr : conductorReduction p (p^n) d =
      Ideal.Quotient.mk (Ideal.span {p}) (representative (p*p^n) d) := by
    conv_lhs => rw [← representative_spec (p*p^n) d]
    rfl
  have hm : Ideal.Quotient.mk (Ideal.span {p*p^n}) (H*representative (p*p^n) d) =
      Ideal.Quotient.mk _ H*d := by rw [map_mul, representative_spec]
  rw [hr, hm]

end SevenEighths.ProbePrimePower
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PhysicalFourier
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein GaussianShiftedPartition ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

theorem rawFourier_exactQuotient (a s : O) (ha : a≠0) (hs : s≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (H : O) :
    conductorFourier a s ha hs F H =
      (Ideal.absNorm (Ideal.span {s}):ℂ) *
        (if h : s∣H then rawFourier a ha F (exactQuotient H s h) else 0) := by
  by_cases h : s∣H
  · rw [dif_pos h]
    conv_lhs => rw [exactQuotient_spec H s h]
    exact conductorFourier_lift a s ha hs F _
  · rw [dif_neg h, mul_zero]
    by_contra hn
    exact h (conductorFourier_support a s ha hs F H hn)

lemma trace_split_product (a s : O) (ha : a≠0) (hs : s≠0) (H m d : O) :
    quotientTrace (a*s) (mul_ne_zero ha hs) (Ideal.Quotient.mk _ (H*m)) *
      quotientTrace s hs (Ideal.Quotient.mk _ ((-m)*d)) =
    quotientTrace (a*s) (mul_ne_zero ha hs) (Ideal.Quotient.mk _ ((H-a*d)*m)) := by
  have he := quotientTrace_split_frequency s a hs ha H d m
  simp only [quotientTrace_mk] at he ⊢
  simpa only [mul_comm s a] using he.symm

theorem fullFourier_eq_congruence (a s : O) (ha : a≠0) (hs : s≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (χ : (O ⧸ Ideal.span {s}) → ℂ) (H : O) :
    fullFourier a s ha hs F χ H =
      (Ideal.absNorm (Ideal.span {s}):ℂ) * congruenceCoefficient a s ha F χ H := by
  let : Finite (O ⧸ Ideal.span {a*s}) := finite_quotient_span (mul_ne_zero ha hs)
  let : Finite (O ⧸ Ideal.span {s}) := finite_quotient_span hs
  let : Fintype (O ⧸ Ideal.span {a*s}) := Fintype.ofFinite _
  let : Fintype (O ⧸ Ideal.span {s}) := Fintype.ofFinite _
  unfold fullFourier rawFourier
  simp_rw [tsum_fintype, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold congruenceCoefficient
  rw [tsum_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  calc
    _ = χ d * conductorFourier a s ha hs F (H-a*representative s d) := by
      rw [conductorFourier, tsum_fintype, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have ht := trace_split_product a s ha hs H (representative (a*s) m) (representative s d)
      simp only [map_mul, representative_spec] at ht
      rw [← ht]
      ring
    _ = _ := by rw [rawFourier_exactQuotient]; ring

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PhysicalCoefficient
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O

lemma rawFourier_outer (s : O) (hs : s≠0) (h : O) :
    rawFourier s hs (outerQuotient s) h = sexticGauss s hs h := rfl

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.FrequencySupport
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition CanonicalRowCompletion
open CenteredMomentCommonSupport CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

lemma elementFourier_congr (c d : O) (hc : c≠0) (hd : d≠0) (f : O → ℂ) (H : O)
    (he : c=d) : elementFourier c hc f H = elementFourier d hd f H := by
  subst d
  rfl

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CalibrationRemoval
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition CanonicalRowCompletion
open CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

lemma barePhysicalFourier_eq (A s : O) (hA : A≠0) (hs : s≠0) (H : O) :
    barePhysicalFourier A s hA hs H =
      (Ideal.absNorm (Ideal.span {s}):ℂ)*bareCongruenceCoefficient A s hA H := by
  unfold bareCongruenceCoefficient
  rw [← fullFourier_eq_congruence A s hA hs]
  unfold barePhysicalFourier elementFourier fullFourier
  apply tsum_congr
  intro m
  rw [rawFourier_outer]
  have he : conductorReduction A s m = Ideal.Quotient.mk (Ideal.span {A}) (representative (A*s) m) := by
    conv_lhs => rw [← representative_spec (A*s) m]
    rfl
  rw [he]
  unfold outerQuotient
  rw [sexticGauss_coefficient_mk]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PhaseCancellation
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates QuadraticGaussRay ConcreteTraceCRT
open QuadraticAllOddCRT CanonicalRowCompletion CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem quadraticRayValue_norm_one (r : EisensteinEPrimaryPhase.Coord)
    (hr : EisensteinEPrimaryPhase.odd r) : ‖quadraticRayValue r‖ = 1 := by
  rw [quadraticRayValue_eq_fourthRoot r hr]
  simp [fourthRoot]

theorem G_norm_one (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hu : IsUnit (Ideal.Quotient.mk cubicTwoIdeal a)) : ‖G a‖ = 1 := by
  have hχ := congrArg
    (fun η : MulChar (O ⧸ cubicTwoIdeal) O => η (Ideal.Quotient.mk cubicTwoIdeal a))
    (cubicChar_pow_three cubicTwoIdeal cubicTwoIdeal_good)
  simp only [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), MulChar.one_apply hu] at hχ
  have hc := congrArg eisEmbedding hχ
  simp only [map_pow, map_one] at hc
  have hn := Complex.norm_eq_one_of_pow_eq_one hc (by decide : (3 : ℕ) ≠ 0)
  change ‖fixedGValue (residue a)‖ = 1
  simp only [fixedGValue, ← fixed_two_mk_eq_residue_lift, norm_mul, norm_inv,
    hn, inv_one, one_mul]
  exact quadraticRayValue_norm_one _ ha

theorem cubicTwo_isUnit_of_odd (a : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a)) :
    IsUnit (Ideal.Quotient.mk cubicTwoIdeal a) := by
  let : Field (O ⧸ cubicTwoIdeal) := Ideal.Quotient.field _
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hd : (2 : O) ∣ a := by
    simpa only [cubicTwoIdeal, Ideal.mem_span_singleton, neg_dvd] using hm
  exact ((odd_residue_iff_not_two_dvd a).mp ha) hd

theorem G_conjugate_cancel (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hu : IsUnit (Ideal.Quotient.mk cubicTwoIdeal a)) : star (G a) * G a = 1 := by
  have hn := G_norm_one a ha hu
  have hs : star (G a) = (G a)⁻¹ := (Complex.inv_eq_conj hn).symm
  rw [hs]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mp (by rw [hn]; norm_num))

end SevenEighths.ProbePhase
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PrimePhase
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates CompletedGauss
open ConcreteTraceCRT ConcretePrimeRowBridge QuadraticGaussRay FiniteGaussPhase CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem normalizedTraceGauss_eq_normalizedGauss (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) :
    letI : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
    letI : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
    ConcreteBreveE.normalizedTraceGauss p hp χ =
      ProbeGauss.normalizedGauss χ (quotientTrace p hp) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hn : Real.sqrt (Nat.card (O ⧸ Ideal.span {p}) : ℝ) = ‖eisEmbedding p‖ := by
    change Real.sqrt (Ideal.absNorm (Ideal.span {p}) : ℝ) = _
    rw [← eisEmbedding_norm_sq_eq_absNorm_span, Real.sqrt_sq (norm_nonneg _)]
  simp only [ConcreteBreveE.normalizedTraceGauss, ProbeGauss.normalizedGauss,
    quotientTrace, ← Nat.card_eq_fintype_card, hn]

theorem quadraticRayValue_eq_normalizedTraceGauss (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    quadraticRayValue (residue p) =
      ConcreteBreveE.normalizedTraceGauss p hp (actualSextic (Ideal.span {p}) hg ^ 3) := by
  let pp : Unit → O := fun _ => p
  have hpp : ∀ i, pp i ≠ 0 := fun _ => hp
  have hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {pp i})) := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have he := canonicalProductGauss_three_eq_rayValue pp hpp hcop (fun _ => hg) (fun _ => hc)
  rw [canonicalProductGauss_cross_factors pp hpp hcop (fun _ => hg) (fun _ => 3)] at he
  simpa [pp] using he.symm

theorem G_cube_eq_normalizedTraceGauss (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (ho : EisensteinEPrimaryPhase.odd (residue p)) :
    G (p ^ 3) =
      ConcreteBreveE.normalizedTraceGauss p hp (actualSextic (Ideal.span {p}) hg ^ 3) := by
  rw [G_cube p ho (cubicTwo_isUnit_of_odd p ho)]
  exact quadraticRayValue_eq_normalizedTraceGauss p hp hg hc

theorem normalizedTraceGauss_three_sq (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    ConcreteBreveE.normalizedTraceGauss p hp (actualSextic (Ideal.span {p}) hg ^ 3) ^ 2 =
      actualSextic (Ideal.span {p}) hg (-1) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  let χ := actualSextic (Ideal.span {p}) hg
  have h6 : χ ^ 6 = 1 := (ProbePrimePower.actualSextic_pow_eq_one_iff _ hg hc 6).mpr (by decide)
  have h3 : χ ^ 3 ≠ 1 := fun h => (by decide : ¬6 ∣ 3)
    ((ProbePrimePower.actualSextic_pow_eq_one_iff _ hg hc 3).mp h)
  have hi : (χ ^ 3)⁻¹ = χ ^ 3 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add]
    exact h6
  have hψ : (quotientTrace p hp).IsPrimitive :=
    GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp
  have he := ProbeGauss.normalizedGauss_inverse_pair (χ ^ 3) (quotientTrace p hp) h3 hψ
  rw [hi, ← pow_two] at he
  rw [normalizedTraceGauss_eq_normalizedGauss]
  rw [he]
  simp only [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), ← map_pow]
  norm_num
  rfl

theorem reciprocitySign_self_eq_sextic_neg_one (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (ho : EisensteinEPrimaryPhase.odd (residue p)) :
    reciprocitySign p p = actualSextic (Ideal.span {p}) hg (-1) := by
  have hq := QuadraticAllOddCRT.quadraticRayValue_mul (residue p) (residue p) ho ho
  rw [quadraticRayValue_square _ ho] at hq
  have hprod : reciprocitySign p p * quadraticRayValue (residue p) ^ 2 = 1 := by
    simpa only [reciprocitySign, pow_two, mul_assoc] using hq.symm
  have he := normalizedTraceGauss_three_sq p hp hg hc
  rw [← quadraticRayValue_eq_normalizedTraceGauss p hp hg hc] at he
  rw [he] at hprod
  calc
    reciprocitySign p p = reciprocitySign p p * 1 := (mul_one _).symm
    _ = reciprocitySign p p * (reciprocitySign p p * actualSextic (Ideal.span {p}) hg (-1)) := by rw [hprod]
    _ = reciprocitySign p p ^ 2 * actualSextic (Ideal.span {p}) hg (-1) := by ring
    _ = _ := by rw [reciprocitySign_sq p p ho ho, one_mul]

end SevenEighths.ProbePhase
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PhasePowers
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates QuadraticGaussRay QuadraticAllOddCRT
local notation "O" => ActualEisensteinCubic.O

lemma residue_one_mod_four : residue (1 : O) = (1, 0) := by
  have he : (1 : O) = eval 1 0 := by simp [eval]
  rw [he, residue_eval]
  norm_num

lemma odd_residue_one : EisensteinEPrimaryPhase.odd (residue (1 : O)) := by
  rw [residue_one_mod_four]
  decide

lemma odd_residue_pow (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a)) (n : ℕ) :
    EisensteinEPrimaryPhase.odd (residue (a ^ n)) := by
  induction n with
  | zero => simpa only [pow_zero] using odd_residue_one
  | succ n ih =>
    rw [pow_succ, residue_mul]
    exact odd_mul _ _ ih ha

lemma reciprocitySign_symm (a b : O) : reciprocitySign a b = reciprocitySign b a := by
  simp only [reciprocitySign, quadraticRaySign_symm]

lemma reciprocitySign_one_left (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a)) :
    reciprocitySign 1 a = 1 := by
  have ht : ∀ r : EisensteinEPrimaryPhase.Coord, EisensteinEPrimaryPhase.odd r →
      quadraticRaySign (1, 0) r = 1 := by decide
  unfold reciprocitySign
  rw [residue_one_mod_four]
  exact_mod_cast ht (residue a) ha

lemma reciprocitySign_mul_left (a b c : O) :
    reciprocitySign (a * b) c = reciprocitySign a c * reciprocitySign b c := by
  simp only [reciprocitySign, residue_mul, quadraticRaySign_mul_left, Int.cast_mul]

lemma reciprocitySign_pow_left (a b : O)
    (hb : EisensteinEPrimaryPhase.odd (residue b)) (n : ℕ) :
    reciprocitySign (a ^ n) b = reciprocitySign a b ^ n := by
  induction n with
  | zero => simp only [pow_zero, reciprocitySign_one_left b hb]
  | succ n ih => rw [pow_succ, reciprocitySign_mul_left, ih, pow_succ]

lemma reciprocitySign_pow_right (a b : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a)) (n : ℕ) :
    reciprocitySign a (b ^ n) = reciprocitySign a b ^ n := by
  rw [reciprocitySign_symm, reciprocitySign_pow_left b a ha n, reciprocitySign_symm b a]

lemma G_one : G (1 : O) = 1 := by
  have hq : quadraticRayValue (residue (1 : O)) = 1 := by
    rw [residue_one_mod_four]
    change breveGaussianFourTerms 1 0 = 1
    rw [breveGaussianFourTerms_formula]
    norm_num
  have he := G_cube (1 : O) odd_residue_one (cubicTwo_isUnit_of_odd 1 odd_residue_one)
  simpa only [one_pow, hq] using he

theorem G_pow (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a)) (n : ℕ) :
    G (a ^ n) = G a ^ n * reciprocitySign a a ^ (n.choose 2) := by
  induction n with
  | zero => simp [G_one]
  | succ n ih =>
    rw [pow_succ, G_mul (a ^ n) a (odd_residue_pow a ha n) ha, ih,
      reciprocitySign_pow_left a a ha n, Nat.choose_succ_succ, Nat.choose_one_right,
      pow_add, pow_succ]
    ring

theorem reciprocitySign_cube_self (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a)) :
    reciprocitySign (a ^ 3) (a ^ 3) = reciprocitySign a a := by
  rw [reciprocitySign_cube_right (a ^ 3) a (odd_residue_pow a ha 3) ha,
    reciprocitySign_symm, reciprocitySign_cube_right a a ha ha]

theorem G_cube_power (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a)) (l : ℕ) :
    G (a ^ (3 * l)) = G (a ^ 3) ^ l * reciprocitySign a a ^ (l.choose 2) := by
  rw [pow_mul, G_pow (a ^ 3) (odd_residue_pow a ha 3), reciprocitySign_cube_self a ha]

theorem G_completed_prime_power (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a))
    (e l : ℕ) (he : e ≤ 1) :
    G (a ^ (e + 3 * l)) =
      G a ^ e * G (a ^ 3) ^ l * reciprocitySign a a ^ (e * l + l.choose 2) := by
  have hc : e = 0 ∨ e = 1 := by omega
  rcases hc with rfl | rfl
  · simpa only [zero_add, zero_mul, pow_zero, one_mul] using G_cube_power a ha l
  · rw [pow_add, pow_one, G_mul a (a ^ (3 * l)) ha (odd_residue_pow a ha _),
      G_cube_power a ha l, pow_mul, reciprocitySign_pow_right a (a ^ 3) ha l,
      reciprocitySign_cube_right a a ha ha]
    simp only [pow_one, one_mul, pow_add]
    ring

end SevenEighths.ProbePhase
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CompletedCRTPhase
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates CompletedGauss CubicEisenstein
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

lemma reciprocitySign_star (a b : O) : star (reciprocitySign a b)=reciprocitySign a b := by
  simp only [reciprocitySign, star_intCast]

end SevenEighths.ProbePhase
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CubicGaussCRT
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open CompletedGauss ConcreteTraceCRT CubicEisenstein GaussianShiftedPartition
open CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

lemma gaussTwo_eq_elementFourier (I : Ideal O) (hI : CubicSieve.Admissible I) :
    gaussTwo I hI.2 =
      elementFourier (primaryGenerator I) hI.2 (CubicSieve.cubicRow I) 1 /
        (‖eisEmbedding (primaryGenerator I)‖:ℂ) := by
  let := finite_quotient_span hI.2
  let : Fintype (Residue (primaryGenerator I)) := Fintype.ofFinite _
  rw [CubicSieve.gaussTwo_eq_gaussSum I hI]
  unfold gaussSum elementFourier
  rw [tsum_fintype]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  have hc := CubicSieve.principalCubicCharacter_mk I hI (representative (primaryGenerator I) x)
  rw [representative_spec] at hc
  rw [hc]
  simp only [map_one, one_mul]
  rfl

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LocalPhysical
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalRowCompletion
open CubicEisenstein GaussianShiftedPartition ProbePrimePower ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma outerQuotient_prime_power (p : O) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (k : ℕ) (hk : k≠0) (d : O ⧸ Ideal.span {p^k}) :
    outerQuotient (p^k) d =
      (actualSextic (Ideal.span {p}) hg ^ k)
        (Ideal.Quotient.mk _ (representative (p^k) d)) := by
  unfold outerQuotient
  rw [← Ideal.span_singleton_pow, map_pow, idealRowHom_prime _ _ hg, MulChar.pow_apply' _ hk]

lemma sexticGauss_prime_power (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (n : ℕ) (H : O) :
    sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) H =
      primePowerGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg^(n+1)) n H := by
  have he : sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) H =
      quotientFourier p (p^(n+1)) (pow_ne_zero _ hp.ne_zero)
        (actualSextic (Ideal.span {p}) hg^(n+1)) H := by
    unfold sexticGauss quotientFourier
    apply tsum_congr
    intro d
    have hc := outerQuotient_prime_power p hg (n+1) (by omega) d
    change idealRowHom (representative (p^(n+1)) d) (Ideal.span {p^(n+1)}) = _ at hc
    rw [hc]
    rw [(Ideal.Quotient.mk (Ideal.span {p^(n+1)})).map_mul, representative_spec]
  rw [he, primePowerGauss_eq_quotientFourier]
  apply quotientFourier_congr
  exact pow_succ' p n

theorem bareCongruenceCoefficient_prime_power_pos (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (n k j : ℕ) (hk : k≠0) :
    bareCongruenceCoefficient (p^(n+1)) (p^k) (pow_ne_zero _ hp.ne_zero) (p^j) =
      positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j := by
  unfold bareCongruenceCoefficient congruenceCoefficient
  rw [positiveScalar, if_neg hk]
  apply tsum_congr
  intro d
  rw [outerQuotient_prime_power p hg k hk]
  split_ifs with hd
  · rw [rawFourier_outer, sexticGauss_prime_power p hp hg]
  · ring

lemma sexticGauss_one (H : O) : sexticGauss 1 one_ne_zero H=1 := by
  let : Subsingleton (O ⧸ Ideal.span {(1:O)}) := by
    rw [Ideal.span_singleton_one]
    infer_instance
  let : Unique (O ⧸ Ideal.span {(1:O)}) := uniqueOfSubsingleton 0
  let : Fintype (O ⧸ Ideal.span {(1:O)}) := Fintype.ofFinite _
  unfold sexticGauss
  have hrow (d : O ⧸ Ideal.span {(1:O)}) :
      idealRowHom (representative 1 d) (Ideal.span {(1:O)})=1 := by
    rw [Ideal.span_singleton_one, ← Ideal.one_eq_top, map_one]
  simp only [hrow, one_mul]
  have ht (d : O ⧸ Ideal.span {(1:O)}) :
      quotientTrace 1 one_ne_zero (Ideal.Quotient.mk _ H*d)=1 := by
    rw [Subsingleton.elim (Ideal.Quotient.mk _ H*d) 0, AddChar.map_zero_eq_one]
  simp only [ht, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_unique, one_smul]

lemma barePhysicalFourier_outer_one (A : O) (hA : A≠0) (H : O) :
    barePhysicalFourier A 1 hA one_ne_zero H = sexticGauss A hA H := by
  unfold barePhysicalFourier
  rw [elementFourier_congr (A*1) A (mul_ne_zero hA one_ne_zero) hA _ H (mul_one A)]
  simp only [sexticGauss_one, mul_one]
  rfl

lemma bareCongruenceCoefficient_outer_one (A : O) (hA : A≠0) (H : O) :
    bareCongruenceCoefficient A 1 hA H=sexticGauss A hA H := by
  have he := barePhysicalFourier_eq A 1 hA one_ne_zero H
  rw [barePhysicalFourier_outer_one] at he
  simpa only [Ideal.span_singleton_one, ← Ideal.one_eq_top, map_one, Nat.cast_one, one_mul] using he.symm

theorem bareCongruenceCoefficient_prime_power (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p}) (n k j : ℕ) :
    bareCongruenceCoefficient (p^(n+1)) (p^k) (pow_ne_zero _ hp.ne_zero) (p^j) =
      positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j := by
  by_cases hk : k=0
  · subst k
    rw [pow_zero, bareCongruenceCoefficient_outer_one, sexticGauss_prime_power p hp hg,
      positiveScalar_kzero]
  · exact bareCongruenceCoefficient_prime_power_pos p hp hg n k j hk

theorem bareCongruenceCoefficient_inner_one (s : O) (hs : s≠0) (H : O) :
    bareCongruenceCoefficient 1 s one_ne_zero H = outerQuotient s (Ideal.Quotient.mk _ H) := by
  let := finite_quotient_span hs
  let : Fintype (O ⧸ Ideal.span {s}) := Fintype.ofFinite _
  have htest (d : O ⧸ Ideal.span {s}) :
      s∣H-1*representative s d ↔ d=Ideal.Quotient.mk _ H := by
    rw [one_mul, ← Ideal.mem_span_singleton, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem,
      representative_spec, eq_comm]
  have hraw (k : O) : rawFourier 1 one_ne_zero (outerQuotient 1) k=1 := by
    rw [rawFourier_outer, sexticGauss_one]
  unfold bareCongruenceCoefficient congruenceCoefficient
  simp_rw [hraw]
  simp only [tsum_fintype]
  rw [Finset.sum_eq_single (Ideal.Quotient.mk _ H)]
  · rw [dif_pos ((htest _).mpr rfl), mul_one]
  · intro d hd hne
    rw [dif_neg ((htest d).not.mpr hne), mul_zero]
  · simp

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PrimeConstants
namespace OAI

noncomputable section
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem localGamma_one_two_signal (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hprimary : goodLambda^2 ∣ p-1) :
    localGamma p hp hg 1 * localGamma p hp hg 2 =
      -FiniteGaussPhase.angularFactor p * MixedGaussConversion.localG p hp hg := by
  have he := breveGamma1_gamma2_eq_neg_alpha_G (Ideal.span {p}) hg hc p rfl hp hprimary
  simpa only [localGamma, ConcreteBreveE.normalizedTraceGauss, pow_one,
    breveGamma1, breveGamma2, MixedGaussConversion.localG, FiniteGaussPhase.angularFactor,
    neg_div] using he

end SevenEighths.ProbePrimePower
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.SpectralWeights
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma signed_diagonal_phase (omega : ℂ) (ho : omega^2=1) (e l k : ℕ) :
    omega^(((e+3*l)*k:ℕ):ℤ) * omega^(-((e*l+l.choose 2:ℕ):ℤ)) =
      omega^((e+3*l)*k+e*l+l.choose 2) := by
  have hn : omega≠0 := by intro h; simp [h] at ho
  have hi : omega⁻¹=omega := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using ho
  rw [zpow_neg, zpow_natCast, zpow_natCast, ← inv_pow, hi, ← pow_add]
  congr 1
  omega

lemma source_signed_phase (C omega : ℂ) (ho : omega^2=1) (e l k : ℕ) :
    C ^l * omega^((((e+3*l)*k:ℕ):ℤ)-(e*l+l.choose 2:ℕ)) =
      localCubePhase C omega e l k := by
  have hn : omega≠0 := by intro h; simp [h] at ho
  rw [sub_eq_add_neg, zpow_add₀ hn, signed_diagonal_phase omega ho]
  rfl

lemma spectral_power_split (Q : ℝ) (hQ : 0<Q) (x w z : ℂ) (e l k m : ℕ) :
    (Q:ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) =
      ((Q:ℂ)^(-x)/(Q:ℂ)^(1/2:ℂ))^e *
      (((Q:ℂ)^(-x))^3/(Q:ℂ))^l * ((Q:ℂ)^(-w))^k * ((Q:ℂ)^(-6*z))^m := by
  have hn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  have h1 : (Q:ℂ)^(-x)/(Q:ℂ)^(1/2:ℂ) = (Q:ℂ)^(-x-(1/2:ℂ)) :=
    (Complex.cpow_sub _ _ hn).symm
  have h3 : ((Q:ℂ)^(-x))^3/(Q:ℂ) = (Q:ℂ)^(-1-3*x) := by
    rw [← Complex.cpow_nat_mul (Q:ℂ) 3 (-x)]
    calc
      _ = (Q:ℂ)^(3*(-x)) / (Q:ℂ)^(1:ℂ) := by rw [Complex.cpow_one]; norm_num
      _ = (Q:ℂ)^(3*(-x)-1) := (Complex.cpow_sub _ _ hn).symm
      _ = _ := by congr 1; ring
  rw [h1, h3, ← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat,
    ← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat,
    ← Complex.cpow_add _ _ hn, ← Complex.cpow_add _ _ hn, ← Complex.cpow_add _ _ hn]
  congr 1
  ring

lemma cpow_half_eq_sqrt (Q : ℝ) (hQ : 0≤Q) :
    (Q:ℂ)^(1/2:ℂ) = (Real.sqrt Q:ℂ) := by
  rw [Real.sqrt_eq_rpow]
  simpa using (Complex.ofReal_cpow hQ (1/2:ℝ)).symm

theorem sourceWeightedScalar_eq (Q : ℝ) (hQ : 0<Q)
    (eta a gamma1 G1 C omega x w z scalar : ℂ) (hG : G1=gamma1*(Real.sqrt Q:ℂ))
    (ho : omega^2=1) (e l k m : ℕ) :
    sourceWeightedScalar Q eta a gamma1 C omega x w z scalar e l k m =
      weightedScalar Q eta a G1 C omega ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w))
        ((Q:ℂ)^(-6*z)) scalar e l k m := by
  unfold sourceWeightedScalar weightedScalar
  rw [spectral_power_split Q hQ, cpow_half_eq_sqrt Q hQ.le]
  rw [zpow_neg, zpow_natCast]
  have hphase := source_signed_phase 1 omega ho e l k
  simp only [localCubePhase, one_pow, one_mul] at hphase
  unfold localCubePhase
  rw [hphase, mul_pow a C, hG]
  simp only [mul_pow, div_pow]

  ring

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma firstGauss_eq_gamma_sqrt (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hg : goodLambda ∉ Ideal.span {p}) :
    primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 =
      localGamma p hp.ne_zero hg 1 *
        (Real.sqrt (Ideal.absNorm (Ideal.span {p})):ℂ) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hQ : 0 < (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hs : (Real.sqrt (Ideal.absNorm (Ideal.span {p})):ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hQ).ne'
  unfold localGamma
  rw [pow_one, ProbePhase.normalizedTraceGauss_eq_normalizedGauss]
  simp only [ProbeGauss.normalizedGauss, ← Nat.card_eq_fintype_card]
  change _ = (gaussSum _ _ / (Real.sqrt (Ideal.absNorm (Ideal.span {p})):ℂ)) * _
  rw [div_mul_cancel₀ _ hs]
  simp only [primeGauss, map_one, one_mul, tsum_fintype, gaussSum]

theorem sourceWeightedScalar_actual (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hg : goodLambda ∉ Ideal.span {p})
    (eta a x w z scalar : ℂ) (e l k m : ℕ) :
    sourceWeightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
      (localGamma p hp.ne_zero hg 1) (star (localGamma p hp.ne_zero hg 3))
      (actualSextic (Ideal.span {p}) hg (-1)) x w z scalar e l k m =
    weightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
      (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1)
      (star (localGamma p hp.ne_zero hg 3)) (actualSextic (Ideal.span {p}) hg (-1))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-6*z)) scalar e l k m := by
  have hQ : 0 < (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  simpa only [Complex.ofReal_natCast] using
    sourceWeightedScalar_eq _ hQ eta a (localGamma p hp.ne_zero hg 1) _
      (star (localGamma p hp.ne_zero hg 3)) (actualSextic (Ideal.span {p}) hg (-1))
      x w z scalar (firstGauss_eq_gamma_sqrt p hp hg)
      (actualSextic_neg_one_sq _ hg) e l k m

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.SourceLocal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

lemma sourcePrincipalTerm_pos (eta a x w z : ℂ) (e l k m : ℕ) (ht : e+3*l≠0) :
    sourcePrincipalTerm p hp hg eta a x w z e l k m =
      principalMarkedTerm p hp hg eta a
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
        (coordV (Ideal.absNorm (Ideal.span {p})) z) e l k m := by
  unfold sourcePrincipalTerm
  rw [sourceWeightedScalar_actual p hp hg]
  simp only [sourceScalar, ht, ite_false, principalMarkedTerm, coordV, Complex.ofReal_natCast]

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PhysicalLocalEuler
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalRowCompletion
open CubicEisenstein GaussianShiftedPartition ProbePrimePower ProbeEuler ProbeLocal
local notation "O" => ActualEisensteinCubic.O

lemma outerQuotient_mk (s H : O) :
    outerQuotient s (Ideal.Quotient.mk _ H)=idealRowHom H (Ideal.span {s}) := by
  unfold outerQuotient
  apply idealRowHom_congr_mod
  exact Ideal.Quotient.eq.mp (representative_spec _ _)

theorem bareCongruenceCoefficient_all_prime_powers (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p}) (t k j : ℕ) :
    bareCongruenceCoefficient (p^t) (p^k) (pow_ne_zero _ hp.ne_zero) (p^j) =
      sourceScalar p hp hg t k j := by
  cases t with
  | zero =>
    simp only [pow_zero]
    rw [bareCongruenceCoefficient_inner_one _ (pow_ne_zero _ hp.ne_zero), outerQuotient_mk]
    unfold sourceScalar
    rw [if_pos rfl]
    by_cases hk : k=0
    · subst k
      simp only [pow_zero, Ideal.span_singleton_one, ← Ideal.one_eq_top, map_one, ite_true]
    · rw [if_neg hk, ← Ideal.span_singleton_pow, map_pow, idealRowHom_prime _ _ hg,
        MulChar.pow_apply' _ hk]
  | succ n =>
    rw [bareCongruenceCoefficient_prime_power p hp hg n k j]
    simp only [sourceScalar, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
      Nat.add_sub_cancel]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.SourcePrime
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ActualEisensteinCoordinates CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge CubicEisenstein ConcreteTraceCRT
open ProbePhase ProbeEuler ProbePrimePower FiniteGaussPhase QuadraticGaussRay
local notation "O" => ActualEisensteinCubic.O

theorem gaussTwo_prime_localGamma (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hprimary : goodLambda^2∣p-1) (hI : primaryGenerator (Ideal.span {p})≠0) :
    gaussTwo (Ideal.span {p}) hI=localGamma p hp.ne_zero hg 2 := by
  let pp : Unit→O := fun _=>p
  have hpp : ∀i,pp i≠0 := fun _=>hp.ne_zero
  have hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {pp i})) := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have hi : primaryGenerator (Ideal.span {∏i,pp i})≠0 := by simpa [pp] using hI
  have he := gaussTwo_eq_canonicalProductGauss pp hpp hcop (fun _=>hg) (fun _=>hprimary) hi
  rw [canonicalProductGauss_cross_factors pp hpp hcop (fun _ => hg) (fun _ => 2)] at he
  simpa [pp,localGamma,ConcreteBreveE.normalizedTraceGauss] using he

theorem G_prime_localG (p : O) (hp : p≠0)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1) :
    G p=MixedGaussConversion.localG p hp hg := by
  let pp : Unit→O := fun _=>p
  have hpp : ∀i,pp i≠0 := fun _=>hp
  have hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {pp i})) := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have he := canonicalProductG_eq_fixedGValue pp hpp hcop (fun _=>hg)
    (fun _=>hchar) (fun _=>hprimary)
  unfold canonicalProductG at he
  rw [canonicalProductGauss_cross_factors pp hpp hcop (fun _ => hg) (fun _ => 3)] at he
  simpa [pp,G,fixedGQuotientValue,MixedGaussConversion.localG,breveLocalG,breveGamma3,
    ConcreteBreveE.normalizedTraceGauss] using he.symm

theorem localGamma_one_two_full_signal (p : O) (hp : p≠0)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1) :
    localGamma p hp hg 1 * localGamma p hp hg 2 =
      -FiniteGaussPhase.angularFactor p * G p := by
  rw [G_prime_localG p hp hg hchar hprimary]
  exact localGamma_one_two_signal p hp hg hchar hprimary

lemma angularFactor_pow (p : O) (n : ℕ) : angularFactor (p^n)=angularFactor p^n := by
  simp only [angularFactor,map_pow,norm_pow,Complex.ofReal_pow,div_pow]

lemma gaussTwo_one : gaussTwo (1:Ideal O) (by rw [primaryGenerator_one]; exact one_ne_zero)=1 := by
  have hI : CubicSieve.Admissible (1:Ideal O) := ⟨squarefree_one,by rw [primaryGenerator_one]; exact one_ne_zero⟩
  rw [gaussTwo_eq_elementFourier (1:Ideal O) hI]
  simp only [primaryGenerator_one,map_one,norm_one,Complex.ofReal_one,div_one]
  have hrow (a : O) : CubicSieve.cubicRow (1:Ideal O) a=1 := by
    rw [CubicSieve.cubicRow,←idealRowHom_square,map_one,one_pow]
  rw [show CubicSieve.cubicRow (1:Ideal O)=(fun _=>1) from funext hrow]
  have he : elementFourier 1 one_ne_zero (fun _=>1) 1=sexticGauss 1 one_ne_zero 1 := by
    unfold elementFourier sexticGauss
    apply tsum_congr
    intro x
    simp only [Ideal.span_singleton_one,←Ideal.one_eq_top,map_one,one_mul]
  rw [he,sexticGauss_one]

lemma gaussTwo_prime_power_small (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hprimary : goodLambda^2∣p-1) (e : ℕ) (he : e≤1)
    (hI : primaryGenerator (Ideal.span {p^e})≠0) :
    gaussTwo (Ideal.span {p^e}) hI=localGamma p hp.ne_zero hg 2^e := by
  have hcases : e=0 ∨ e=1 := by omega
  rcases hcases with rfl|rfl
  · simpa only [pow_zero,Ideal.span_singleton_one,←Ideal.one_eq_top] using gaussTwo_one
  · have hi : primaryGenerator (Ideal.span {p})≠0 := by simpa only [pow_one] using hI
    simpa only [pow_one] using gaussTwo_prime_localGamma p hp hg hprimary hi

lemma corrected_prime_cubic_signal (p : O) (hp : p≠0)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) :
    localGamma p hp hg 2 * star (angularFactor p) * star (G p) = -(localGamma p hp hg 1)⁻¹ := by
  have hsig := localGamma_one_two_full_signal p hp hg hchar hprimary
  have hn := localGamma_norm_one p hp hg hchar 1 (by decide) (by decide)
  have hne : localGamma p hp hg 1≠0 := by intro h; rw [h,norm_zero] at hn; norm_num at hn
  have hG : G p*star (G p)=1 := by
    rw [mul_comm]
    exact G_conjugate_cancel p (supported_residue_odd p hs)
      (cubicTwo_isUnit_of_odd p (supported_residue_odd p hs))
  apply mul_left_cancel₀ hne
  calc
    _ = (localGamma p hp hg 1*localGamma p hp hg 2)*star (angularFactor p)*star (G p) := by ring
    _ = -1 := by
      rw [hsig]
      calc
        _ = -(angularFactor p*star (angularFactor p))*(G p*star (G p)) := by ring
        _ = _ := by rw [angularFactor_mul_star p hp,hG]; ring
    _ = _ := by rw [mul_neg,mul_inv_cancel₀ hne]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.SourcePrimeFactor
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein ProbePhase ProbeEuler ProbePrimePower ProbeRow
local notation "O" => ActualEisensteinCubic.O

theorem bareSourceCoefficient_prime_formula (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (e l k j : ℕ) (he : e≤1)
    (hI : primaryGenerator (Ideal.span {p^e})≠0) :
    bareSourceCoefficient η (Ideal.span {p^e}) hI (p^(e+3*l)) (p^k)
      (pow_ne_zero _ hp.ne_zero) (p^j) =
    (-1:ℂ)^e * ((localGamma p hp.ne_zero hg 1)⁻¹)^e * (targetMonoid η p)^e *
      (star (FiniteGaussPhase.angularFactor p)^3 * (targetMonoid η p)^3 *
        star (localGamma p hp.ne_zero hg 3))^l *
      (actualSextic (Ideal.span {p}) hg (-1))^((e+3*l)*k+e*l+l.choose 2) *
      sourceScalar p hp hg (e+3*l) k j := by
  have ho := supported_residue_odd p hs
  have hself := reciprocitySign_self_eq_sextic_neg_one p hp.ne_zero hg hchar ho
  have hstar : star (actualSextic (Ideal.span {p}) hg (-1))=
      actualSextic (Ideal.span {p}) hg (-1) := by
    rw [←hself,reciprocitySign_star]
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [gaussTwo_prime_power_small p hp hg hprimary e he hI,
    bareCongruenceCoefficient_all_prime_powers p hp hg,
    angularFactor_pow,map_pow,
    G_completed_prime_power p ho e l he,
    G_cube_eq_normalizedTraceGauss p hp.ne_zero hg hchar ho,
    reciprocitySign_pow_left p _ (odd_residue_pow p ho k),reciprocitySign_pow_right p p ho,
    hself]
  change _ = _
  simp only [star_mul,star_pow,hstar]
  change (targetMonoid η p)^(e+3*l) * star (FiniteGaussPhase.angularFactor p)^(e+3*l) *
    (localGamma p hp.ne_zero hg 2^e *
      ((actualSextic (Ideal.span {p}) hg (-1))^(e*l+l.choose 2) *
        (star (localGamma p hp.ne_zero hg 3)^l * star (G p)^e)) *
      (((actualSextic (Ideal.span {p}) hg (-1))^k)^(e+3*l) *
        sourceScalar p hp hg (e+3*l) k j)) = _
  calc
    _ = (localGamma p hp.ne_zero hg 2 * star (FiniteGaussPhase.angularFactor p) * star (G p))^e *
      (targetMonoid η p)^e *
      (star (FiniteGaussPhase.angularFactor p)^3*(targetMonoid η p)^3*
        star (localGamma p hp.ne_zero hg 3))^l *
      (actualSextic (Ideal.span {p}) hg (-1))^((e+3*l)*k+e*l+l.choose 2) *
      sourceScalar p hp hg (e+3*l) k j := by
        simp only [pow_add,pow_mul,mul_pow]
        ring
    _ = _ := by
      rw [corrected_prime_cubic_signal p hp.ne_zero hg hchar hprimary hs]
      rw [neg_eq_neg_one_mul ((localGamma p hp.ne_zero hg 1)⁻¹),mul_pow]

theorem bareSourceCoefficient_weighted_prime (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (e l k m : ℕ) (he : e≤1)
    (hI : primaryGenerator (Ideal.span {p^e})≠0) (x w z : ℂ) :
    bareSourceCoefficient η (Ideal.span {p^e}) hI (p^(e+3*l)) (p^k)
      (pow_ne_zero _ hp.ne_zero) (p^(6*m)) *
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) =
    sourcePrincipalTerm p hp hg (targetMonoid η p) (actualACube η p) x w z e l k m := by
  rw [bareSourceCoefficient_prime_formula η p hp hg hchar hprimary hs e l k (6*m) he hI]
  unfold sourcePrincipalTerm sourceWeightedScalar
  simp only [zpow_neg,zpow_natCast,←inv_pow,Complex.ofReal_natCast]
  have hpdiag := source_signed_phase
    (actualACube η p*star (localGamma p hp.ne_zero hg 3))
    (actualSextic (Ideal.span {p}) hg (-1)) (actualSextic_neg_one_sq _ hg) e l k
  simp only [localCubePhase] at hpdiag
  have ha : actualACube η p=
      star (FiniteGaussPhase.angularFactor p)^3*(targetMonoid η p)^3 := rfl
  rw [ha] at hpdiag ⊢
  calc
    _ = ((-1:ℂ)^e*((localGamma p hp.ne_zero hg 1)⁻¹)^e*(targetMonoid η p)^e) *
      ((star (FiniteGaussPhase.angularFactor p)^3*(targetMonoid η p)^3*
        star (localGamma p hp.ne_zero hg 3))^l *
        (actualSextic (Ideal.span {p}) hg (-1))^((e+3*l)*k+e*l+l.choose 2)) *
      sourceScalar p hp hg (e+3*l) k (6*m) *
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) := by ring
    _ = _ := by rw [←hpdiag]; ring

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.IdealLocalEuler
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein ProbePhase ProbeEuler ProbePrimePower ProbeRow
local notation "O" => ActualEisensteinCubic.O

lemma prime_power_small_squarefree (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (e : ℕ) (he : e≤1) :
    Squarefree ((Ideal.span {p})^e) := by
  have hP : Prime (Ideal.span {p}:Ideal O) :=
    Ideal.prime_of_isPrime (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero) inferInstance
  have hcases : e=0 ∨ e=1 := by omega
  rcases hcases with rfl|rfl
  · simpa only [pow_zero] using (squarefree_one : Squarefree (1:Ideal O))
  · simpa only [pow_one] using hP.squarefree

theorem bareIdealHighCoefficient_at_prime (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (e l k m : ℕ) (he : e≤1) :
    bareIdealHighCoefficient η 1 ((Ideal.span {p})^e) ((Ideal.span {p})^l)
      ((Ideal.span {p})^k) ((Ideal.span {p})^m) =
    bareSourceCoefficient η (Ideal.span {p^e})
      (by rw [← Ideal.span_singleton_pow,primaryGenerator_prime_power p hp.ne_zero hprimary e];
          exact pow_ne_zero _ hp.ne_zero)
      (p^(e+3*l)) (p^k) (pow_ne_zero _ hp.ne_zero) (p^(6*m)) := by
  have hguard : Squarefree ((Ideal.span {p})^e) ∧ Supported ((Ideal.span {p})^e) ∧
      Supported ((Ideal.span {p})^l) ∧ Supported ((Ideal.span {p})^k) ∧ Supported ((Ideal.span {p})^m) :=
    ⟨prime_power_small_squarefree p hp e he,supported_pow hs e,supported_pow hs l,supported_pow hs k,supported_pow hs m⟩
  unfold bareIdealHighCoefficient
  rw [dif_pos hguard]
  simp only [primaryGenerator_prime_power p hp.ne_zero hprimary,one_mul]
  have hA : p^e*(p^l)^3=p^(e+3*l) := by rw [←pow_mul,Nat.mul_comm l 3,←pow_add]
  have hH : (p^m)^6=p^(6*m) := by rw [←pow_mul,Nat.mul_comm m 6]
  simp only [hA,hH,Ideal.span_singleton_pow]

lemma fullIdealWeight_power (s : ℂ) (I : Ideal O) (n : ℕ) :
    fullIdealWeight s (I ^n)=fullIdealWeight s I ^n := (IdealEuler.normWeight s).map_pow I n

lemma prime_spectral_weights (p : O) (hp : p≠0) (e l k m : ℕ) (x w z : ℂ) :
    fullIdealWeight (x+1/2) ((Ideal.span {p})^e) *
      fullIdealWeight (1+3*x) ((Ideal.span {p})^l) *
      fullIdealWeight w ((Ideal.span {p})^k) * fullIdealWeight (6*z) ((Ideal.span {p})^m) =
    (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) := by
  have hI : (Ideal.span {p}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr hp
  have hQ : (Ideal.absNorm (Ideal.span {p}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hI
  simp only [fullIdealWeight_power]
  simp only [fullIdealWeight,if_neg hI]
  rw [←Complex.cpow_mul_nat,←Complex.cpow_mul_nat,←Complex.cpow_mul_nat,←Complex.cpow_mul_nat,
    ←Complex.cpow_add _ _ hQ,←Complex.cpow_add _ _ hQ,←Complex.cpow_add _ _ hQ]
  congr 1
  ring

theorem bareIdealHighSummand_at_prime (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (e l k m : ℕ) (he : e≤1) (x w z : ℂ) :
    bareIdealHighSummand η 1 x w z ((Ideal.span {p})^e) ((Ideal.span {p})^l)
      ((Ideal.span {p})^k) ((Ideal.span {p})^m) =
    sourcePrincipalTerm p hp hg (targetMonoid η p) (actualACube η p) x w z e l k m := by
  unfold bareIdealHighSummand
  rw [bareIdealHighCoefficient_at_prime η p hp hprimary hs e l k m he]
  have hw := prime_spectral_weights p hp.ne_zero e l k m x w z
  simp only [mul_assoc] at hw ⊢
  rw [hw]
  simpa only [mul_assoc] using
    bareSourceCoefficient_weighted_prime η p hp hg hchar hprimary hs e l k m he _ x w z

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.MarkedLocal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ProbeEuler ProbeRow ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma idealMarkedLocalFactor_eq_source_oai (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    let p := primaryGenerator P.val
    let hp := supported_primeGenerator_prime P hs
    letI : (Ideal.span {p}:Id).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    let hg := (supported_prime_data p hp ((span_primaryGenerator_of_supported P.val hs).symm ▸ hs)).1
    idealMarkedLocalFactor η P x w z=
      principalMarkedSeries p hp hg (targetMonoid η p) (actualACube η p)
        ((Ideal.absNorm P.val:ℂ)^(-x)) ((Ideal.absNorm P.val:ℂ)^(-w))
        (coordV (Ideal.absNorm P.val) z) := by
  dsimp only
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Id).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hprimary := (primaryGenerator_spec P.val (supported_primaryGenerator_ne_zero P.val hs)).2
  unfold idealMarkedLocalFactor principalMarkedSeries principalInner
  apply Finset.sum_congr rfl
  intro e he
  apply tsum_congr
  intro l
  apply tsum_congr
  intro k
  apply tsum_congr
  intro m
  change completedValuationMark P ((e.val,l),(k,m))*bareIdealHighSummand η 1 x w z
    (P.val^e.val) (P.val^l) (P.val^k) (P.val^m)=_
  have hterm := bareIdealHighSummand_at_prime η p hp hg.1 hg.2 hprimary hsp e.val l k m (by omega) x w z
  conv_lhs at hterm => rw [hspan]
  rw [hterm]
  by_cases ht : e.val+3*l=0
  · have he0 : e.val=0 := by omega
    have hl0 : l=0 := by omega
    simp only [completedValuationMark,ht,ne_eq,not_true_eq_false,ite_false,zero_mul]
    rw [he0,hl0]
    simpa only [hspan] using (markedTerm_zero_index p hp hg.1 (targetMonoid η p)
      (actualACube η p) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) k m).symm
  · simp only [completedValuationMark,ht,ne_eq,not_false_eq_true,ite_true,one_mul]
    simpa only [hspan] using sourcePrincipalTerm_pos p hp hg.1 (targetMonoid η p) (actualACube η p) x w z e.val l k m ht

end SevenEighths.ProbePhysical
end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.ProbePhysical.idealMarkedLocalFactor_eq_source_oai := @OAI.SevenEighths.ProbePhysical.idealMarkedLocalFactor_eq_source_oai
