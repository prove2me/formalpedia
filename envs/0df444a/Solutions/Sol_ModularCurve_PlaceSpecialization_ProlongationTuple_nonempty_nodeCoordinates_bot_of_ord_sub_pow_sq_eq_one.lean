-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.nonempty_nodeCoordinates_bot_of_ord_sub_pow_sq_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ce74bbd0-9620-5be7-9357-3baa27bd5320

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Theorems.Thm_ModularCurve_pow_char_eq_qExpand_of_coeff_fixed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_nonempty_nodeCoordinates_bot_of_ord_sub_pow_sq_eq_one
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace TwoCoordinateFormula

private theorem coeffEmb_qExpand (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n]
    (x : LaurentSeries ℚ) : coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x) :=
  coeffMap_qExpand _ n x

private theorem coe_atkinLehnerInvolutionFull_of_mem {N q : ℕ} [NeZero N] [NeZero q]
    (hAL : IsAtkinLehnerAutFull N q (atkinLehnerInvolutionFull N q))
    (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull N) :
    ((atkinLehnerInvolutionFull N q
        ⟨g, full_degeneracy_le (dvd_mul_right N q) hg⟩ : ↥(modularFunctionFieldFull (N * q)))
      : LaurentSeries ℚ) = qExpand ℚ q g := by
  induction hg using IntermediateField.adjoin_induction with
  | mem x hx =>
      obtain ⟨d, hd0, hdN, rfl⟩ := hx
      have h := (hAL d hd0 hdN).1
      have hmem :
          (⟨qExpand ℚ d jq, full_degeneracy_le (dvd_mul_right N q) (jqd_mem_full N hdN)⟩ :
            ↥(modularFunctionFieldFull (N * q)))
            = ⟨qExpand ℚ d jq, jqd_mem_full (N * q) (Dvd.dvd.mul_right hdN q)⟩ := rfl
      rw [hmem, h]
      have h2 : qExpand ℚ q (qExpand ℚ d jq) = qExpand ℚ (q * d) jq := qExpand_qExpand d q jq
      rw [h2]
      exact qExpand_congr (Nat.mul_comm d q) jq
  | algebraMap r =>
      have h1 : (⟨algebraMap ℚ (LaurentSeries ℚ) r, full_degeneracy_le (dvd_mul_right N q)
            ((modularFunctionFieldFull N).algebraMap_mem r)⟩ :
            ↥(modularFunctionFieldFull (N * q)))
          = algebraMap ℚ ↥(modularFunctionFieldFull (N * q)) r := Subtype.ext (by simp)
      rw [h1, AlgEquiv.commutes]
      simp
  | add x y hx hy ihx ihy =>
      have hsplit :
          (⟨x + y, full_degeneracy_le (dvd_mul_right N q) (add_mem hx hy)⟩ :
            ↥(modularFunctionFieldFull (N * q)))
          = ⟨x, full_degeneracy_le (dvd_mul_right N q) hx⟩
            + ⟨y, full_degeneracy_le (dvd_mul_right N q) hy⟩ := rfl
      rw [hsplit, map_add]
      push_cast
      rw [ihx, ihy, map_add]
  | inv x hx ihx =>
      have hsplit :
          (⟨x⁻¹, full_degeneracy_le (dvd_mul_right N q) (inv_mem hx)⟩ :
            ↥(modularFunctionFieldFull (N * q)))
          = (⟨x, full_degeneracy_le (dvd_mul_right N q) hx⟩ :
            ↥(modularFunctionFieldFull (N * q)))⁻¹ := rfl
      rw [hsplit, map_inv₀]
      push_cast
      rw [ihx, map_inv₀]
  | mul x y hx hy ihx ihy =>
      have hsplit :
          (⟨x * y, full_degeneracy_le (dvd_mul_right N q) (mul_mem hx hy)⟩ :
            ↥(modularFunctionFieldFull (N * q)))
          = ⟨x, full_degeneracy_le (dvd_mul_right N q) hx⟩
            * ⟨y, full_degeneracy_le (dvd_mul_right N q) hy⟩ := rfl
      rw [hsplit, map_mul]
      push_cast
      rw [ihx, ihy, map_mul]

private theorem atkinLehnerBar_heckeAlphaBar_eq_heckeBetaBar {N q : ℕ} [NeZero N] [NeZero q]
    (hAL : IsAtkinLehnerAutFull N q (atkinLehnerInvolutionFull N q))
    (f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) :
    atkinLehnerBar N q (heckeAlphaBar (AlgebraicClosure ℚ) N q f)
      = heckeBetaBar (AlgebraicClosure ℚ) N q f := by
  obtain ⟨x, hx⟩ := f
  apply Subtype.ext
  induction hx using IntermediateField.adjoin_induction with
  | mem z hz =>
      obtain ⟨g₀, hg₀, rfl⟩ := hz
      have hα : heckeAlphaBar (AlgebraicClosure ℚ) N q
            ⟨coeffEmb (AlgebraicClosure ℚ) g₀, IntermediateField.subset_adjoin _ _ ⟨g₀, hg₀, rfl⟩⟩
          = ⟨coeffEmb (AlgebraicClosure ℚ) g₀,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (full_degeneracy_le (dvd_mul_right N q) hg₀)⟩ :=
        Subtype.ext (coe_heckeAlphaBar _ _ _)
      rw [hα]
      have hAL1 : atkinLehnerBar N q
            ⟨coeffEmb (AlgebraicClosure ℚ) g₀,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (full_degeneracy_le (dvd_mul_right N q) hg₀)⟩
          = ⟨coeffEmb (AlgebraicClosure ℚ)
                ((atkinLehnerInvolutionFull N q
                  ⟨g₀, full_degeneracy_le (dvd_mul_right N q) hg₀⟩ : ↥(modularFunctionFieldFull (N * q)))),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (atkinLehnerInvolutionFull N q
                  ⟨g₀, full_degeneracy_le (dvd_mul_right N q) hg₀⟩).2⟩ :=
        geomAut_coeffEmb (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q))
          (atkinLehnerInvolutionFull N q) ⟨g₀, full_degeneracy_le (dvd_mul_right N q) hg₀⟩
      rw [hAL1]
      show coeffEmb (AlgebraicClosure ℚ)
          ((atkinLehnerInvolutionFull N q ⟨g₀, full_degeneracy_le (dvd_mul_right N q) hg₀⟩ :
            ↥(modularFunctionFieldFull (N * q))) : LaurentSeries ℚ)
          = ((heckeBetaBar (AlgebraicClosure ℚ) N q ⟨coeffEmb (AlgebraicClosure ℚ) g₀, _⟩ :
              ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)))) :
            LaurentSeries (AlgebraicClosure ℚ))
      rw [coe_atkinLehnerInvolutionFull_of_mem hAL g₀ hg₀]
      rw [show ((heckeBetaBar (AlgebraicClosure ℚ) N q ⟨coeffEmb (AlgebraicClosure ℚ) g₀, _⟩ :
              ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)))) :
            LaurentSeries (AlgebraicClosure ℚ))
          = qExpand (AlgebraicClosure ℚ) q (coeffEmb (AlgebraicClosure ℚ) g₀) from
        coe_heckeBetaBarRingHom _ _ _]
      exact coeffEmb_qExpand (AlgebraicClosure ℚ) q g₀
  | algebraMap r =>
      rw [show (⟨algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) r, _⟩ :
            ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
          = algebraMap (AlgebraicClosure ℚ)
              ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) r from
          Subtype.ext rfl,
        AlgHom.commutes, AlgHom.commutes, AlgEquiv.commutes]
  | add a b ha hb iha ihb =>
      rw [show (⟨a + b, add_mem ha hb⟩ :
            ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
          = ⟨a, ha⟩ + ⟨b, hb⟩ from rfl, map_add, map_add, map_add]
      push_cast
      rw [iha, ihb]
  | inv a ha iha =>
      rw [show (⟨a⁻¹, inv_mem ha⟩ :
            ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
          = (⟨a, ha⟩ :
            ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))⁻¹ from rfl,
        map_inv₀, map_inv₀, map_inv₀]
      push_cast
      rw [iha]
  | mul a b ha hb iha ihb =>
      rw [show (⟨a * b, mul_mem ha hb⟩ :
            ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
          = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, map_mul, map_mul, map_mul]
      push_cast
      rw [iha, ihb]

private theorem red_pow_char_eq_of_coe_eq_algebraMap
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (a : A) (r : ℚ)
    (h : (a : AlgebraicClosure ℚ) = algebraMap ℚ (AlgebraicClosure ℚ) r) :
    red a ^ q = red a := by
  have hq : q.Prime := Fact.out

  have hQ : (a : AlgebraicClosure ℚ) * (r.den : AlgebraicClosure ℚ) = (r.num : AlgebraicClosure ℚ) := by
    rw [h, ← map_natCast (algebraMap ℚ (AlgebraicClosure ℚ)) r.den,
      ← map_intCast (algebraMap ℚ (AlgebraicClosure ℚ)) r.num, ← map_mul, Rat.mul_den_eq_num]
  have hA : a * (r.den : A) = (r.num : A) := by
    apply Subtype.ext
    simpa using hQ
  have hk : red a * (r.den : k) = (r.num : k) := by
    simpa [map_mul, map_natCast, map_intCast] using congrArg red hA

  have hden0 : (r.den : k) ≠ 0 := by
    intro h0
    have hnum0 : ((r.num : ℤ) : k) = 0 := by rw [← hk, h0, mul_zero]
    have hqden : q ∣ r.den := (CharP.cast_eq_zero_iff k q r.den).mp h0
    have hqnum : (q : ℤ) ∣ r.num := (CharP.intCast_eq_zero_iff k q r.num).mp hnum0
    have hqnum' : q ∣ r.num.natAbs := by
      simpa using Int.natAbs_dvd_natAbs.mpr hqnum
    have hone : q ∣ Nat.gcd r.num.natAbs r.den := Nat.dvd_gcd hqnum' hqden
    rw [Nat.Coprime.gcd_eq_one r.reduced] at hone
    exact hq.one_lt.ne' (Nat.dvd_one.mp hone)

  have hfrob : frobenius k q (red a) * (r.den : k) = red a * (r.den : k) := by
    have := congrArg (frobenius k q) hk
    rw [map_mul, map_natCast, map_intCast] at this
    rw [this, hk]
  exact mul_right_cancel₀ hden0 hfrob

private theorem red_coeff_pow_char_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (y : LaurentSeries ↥A) (g₀ : LaurentSeries ℚ)
    (hy : coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) g₀) (n : ℤ) :
    red (y.coeff n) ^ q = red (y.coeff n) :=
  red_pow_char_eq_of_coe_eq_algebraMap red (y.coeff n) (g₀.coeff n) (by
    have := congrArg (fun s : LaurentSeries (AlgebraicClosure ℚ) => s.coeff n) hy
    simpa [coeffMap_coeff, coeffEmb_coeff] using this)

private theorem coeffMap_pow_char_eq_qExpand
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (y : LaurentSeries ↥A) (g₀ : LaurentSeries ℚ)
    (hy : coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) g₀) :
    coeffMap red y ^ q = qExpand k q (coeffMap red y) :=
  ModularCurve.pow_char_eq_qExpand_of_coeff_fixed q (coeffMap red y) fun n => by
    rw [coeffMap_coeff]
    exact red_coeff_pow_char_eq red y g₀ hy n

private theorem mem_restrictAlong_iff {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring :=
  Iff.rfl

private theorem coe_atkinLehnerInvolutionFull_of_mem_qExpand {N q : ℕ} [NeZero N] [NeZero q]
    (hAL : IsAtkinLehnerAutFull N q (atkinLehnerInvolutionFull N q))
    (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull N) :
    ((atkinLehnerInvolutionFull N q
        ⟨qExpand ℚ q g, full_degeneracy_map_le (N := N) q ⟨g, hg, rfl⟩⟩ : ↥(modularFunctionFieldFull (N * q)))
      : LaurentSeries ℚ) = g := by
  induction hg using IntermediateField.adjoin_induction with
  | mem x hx =>
      obtain ⟨d, hd0, hdN, rfl⟩ := hx
      have h := (hAL d hd0 hdN).2
      have hmem :
          (⟨qExpand ℚ q (qExpand ℚ d jq),
              full_degeneracy_map_le (N := N) q ⟨qExpand ℚ d jq, jqd_mem_full N hdN, rfl⟩⟩ :
            ↥(modularFunctionFieldFull (N * q)))
            = ⟨qExpand ℚ (d * q) jq, jqd_mem_full (N * q) (Nat.mul_dvd_mul_right hdN q)⟩ := by
        apply Subtype.ext
        show qExpand ℚ q (qExpand ℚ d jq) = qExpand ℚ (d * q) jq
        rw [qExpand_qExpand d q jq]
        exact qExpand_congr (Nat.mul_comm q d) jq
      rw [hmem, h]
  | algebraMap r =>
      have h1 : (⟨qExpand ℚ q (algebraMap ℚ (LaurentSeries ℚ) r),
            full_degeneracy_map_le (N := N) q
              ⟨algebraMap ℚ (LaurentSeries ℚ) r, (modularFunctionFieldFull N).algebraMap_mem r, rfl⟩⟩ :
            ↥(modularFunctionFieldFull (N * q)))
          = algebraMap ℚ ↥(modularFunctionFieldFull (N * q)) r := by
        apply Subtype.ext
        show qExpand ℚ q (algebraMap ℚ (LaurentSeries ℚ) r) = _
        rw [show qExpand ℚ q (algebraMap ℚ (LaurentSeries ℚ) r) = algebraMap ℚ (LaurentSeries ℚ) r from
          (qExpandₐ q).commutes r]
        simp
      rw [h1, AlgEquiv.commutes]
      simp
  | add x y hx hy ihx ihy =>
      have hsplit :
          (⟨qExpand ℚ q (x + y), full_degeneracy_map_le (N := N) q ⟨x + y, add_mem hx hy, rfl⟩⟩ :
            ↥(modularFunctionFieldFull (N * q)))
          = ⟨qExpand ℚ q x, full_degeneracy_map_le (N := N) q ⟨x, hx, rfl⟩⟩
            + ⟨qExpand ℚ q y, full_degeneracy_map_le (N := N) q ⟨y, hy, rfl⟩⟩ :=
        Subtype.ext (map_add (qExpand ℚ q) x y)
      rw [hsplit, map_add]
      push_cast
      rw [ihx, ihy]
  | inv x hx ihx =>
      have hsplit :
          (⟨qExpand ℚ q x⁻¹, full_degeneracy_map_le (N := N) q
              ⟨x⁻¹, (inv_mem hx : x⁻¹ ∈ modularFunctionFieldFull N), rfl⟩⟩ :
            ↥(modularFunctionFieldFull (N * q)))
          = (⟨qExpand ℚ q x, full_degeneracy_map_le (N := N) q ⟨x, hx, rfl⟩⟩ :
            ↥(modularFunctionFieldFull (N * q)))⁻¹ :=
        Subtype.ext (map_inv₀ (qExpand ℚ q) x)
      rw [hsplit, map_inv₀]
      push_cast
      rw [ihx]
  | mul x y hx hy ihx ihy =>
      have hsplit :
          (⟨qExpand ℚ q (x * y), full_degeneracy_map_le (N := N) q ⟨x * y, mul_mem hx hy, rfl⟩⟩ :
            ↥(modularFunctionFieldFull (N * q)))
          = ⟨qExpand ℚ q x, full_degeneracy_map_le (N := N) q ⟨x, hx, rfl⟩⟩
            * ⟨qExpand ℚ q y, full_degeneracy_map_le (N := N) q ⟨y, hy, rfl⟩⟩ :=
        Subtype.ext (map_mul (qExpand ℚ q) x y)
      rw [hsplit, map_mul]
      push_cast
      rw [ihx, ihy]

private theorem atkinLehnerBar_heckeBetaBar_eq_heckeAlphaBar {N q : ℕ} [NeZero N] [NeZero q]
    (hAL : IsAtkinLehnerAutFull N q (atkinLehnerInvolutionFull N q))
    (f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) :
    atkinLehnerBar N q (heckeBetaBar (AlgebraicClosure ℚ) N q f)
      = heckeAlphaBar (AlgebraicClosure ℚ) N q f := by
  obtain ⟨x, hx⟩ := f
  apply Subtype.ext
  induction hx using IntermediateField.adjoin_induction with
  | mem z hz =>
      obtain ⟨g₀, hg₀, rfl⟩ := hz
      have hmap : qExpand ℚ q g₀ ∈ modularFunctionFieldFull (N * q) :=
        full_degeneracy_map_le (N := N) q ⟨g₀, hg₀, rfl⟩
      have hβ : heckeBetaBar (AlgebraicClosure ℚ) N q
            ⟨coeffEmb (AlgebraicClosure ℚ) g₀, IntermediateField.subset_adjoin _ _ ⟨g₀, hg₀, rfl⟩⟩
          = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q g₀),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmap⟩ := by
        apply Subtype.ext
        rw [coe_heckeBetaBar]
        exact (coeffEmb_qExpand (AlgebraicClosure ℚ) q g₀).symm
      rw [hβ]
      have hAL1 : atkinLehnerBar N q
            ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q g₀), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmap⟩
          = ⟨coeffEmb (AlgebraicClosure ℚ)
                ((atkinLehnerInvolutionFull N q ⟨qExpand ℚ q g₀, hmap⟩ : ↥(modularFunctionFieldFull (N * q)))),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (atkinLehnerInvolutionFull N q ⟨qExpand ℚ q g₀, hmap⟩).2⟩ :=
        geomAut_coeffEmb (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q))
          (atkinLehnerInvolutionFull N q) ⟨qExpand ℚ q g₀, hmap⟩
      rw [hAL1]
      show coeffEmb (AlgebraicClosure ℚ)
          ((atkinLehnerInvolutionFull N q ⟨qExpand ℚ q g₀, hmap⟩ : ↥(modularFunctionFieldFull (N * q))) :
            LaurentSeries ℚ)
          = ((heckeAlphaBar (AlgebraicClosure ℚ) N q ⟨coeffEmb (AlgebraicClosure ℚ) g₀, _⟩ :
              ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)))) :
            LaurentSeries (AlgebraicClosure ℚ))
      rw [coe_atkinLehnerInvolutionFull_of_mem_qExpand hAL g₀ hg₀, coe_heckeAlphaBar]
  | algebraMap r =>
      rw [show (⟨algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) r, _⟩ :
            ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
          = algebraMap (AlgebraicClosure ℚ)
              ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) r from
          Subtype.ext rfl,
        AlgHom.commutes, AlgHom.commutes, AlgEquiv.commutes]
  | add a b ha hb iha ihb =>
      rw [show (⟨a + b, add_mem ha hb⟩ : ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
          = ⟨a, ha⟩ + ⟨b, hb⟩ from rfl, map_add, map_add, map_add]
      push_cast
      rw [iha, ihb]
  | inv a ha iha =>
      rw [show (⟨a⁻¹, inv_mem ha⟩ : ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
          = (⟨a, ha⟩ : ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))⁻¹ from rfl,
        map_inv₀, map_inv₀, map_inv₀]
      push_cast
      rw [iha]
  | mul a b ha hb iha ihb =>
      rw [show (⟨a * b, mul_mem ha hb⟩ : ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
          = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, map_mul, map_mul, map_mul]
      push_cast
      rw [iha, ihb]

private theorem coeffEmb_mem_fieldOver_bot {M : ℕ} [NeZero M] (hGEN : FunctionFieldGeneration M)
    {s : LaurentSeries ℚ} (hs : s ∈ modularFunctionFieldFull M) :
    coeffEmb (AlgebraicClosure ℚ) s ∈ NodeLocalized.fieldOver M (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)) := by
  have hle : modularFunctionFieldFull M ≤ IntermediateField.adjoin ℚ {jq, qExpand ℚ M jq} := by
    rw [modularFunctionFieldFull, IntermediateField.adjoin_le_iff]
    rintro x ⟨d, hne, hdvd, rfl⟩
    exact hGEN d hdvd hne
  have hs' : s ∈ IntermediateField.adjoin ℚ {jq, qExpand ℚ M jq} := hle hs
  clear hs
  induction hs' using IntermediateField.adjoin_induction with
  | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · have hj : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
          rw [← jqModC_rat]
          exact coeffMap_jqModC _
        rw [hj]
        exact Subfield.subset_closure (Or.inr (Set.mem_insert _ _))
      · have hjM : coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M jq) = jqNModC (AlgebraicClosure ℚ) M := by
          rw [show qExpand ℚ M jq = jqNModC ℚ M from rfl]
          exact coeffMap_jqNModC _ M
        rw [hjM]
        exact Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))
  | algebraMap r =>
      have hc : coeffEmb (AlgebraicClosure ℚ) (algebraMap ℚ (LaurentSeries ℚ) r)
          = CharPReduction.constSeries (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)).toSubalgebra.toSubring
              ⟨algebraMap ℚ (AlgebraicClosure ℚ) r, IntermediateField.mem_bot.mpr ⟨r, rfl⟩⟩ := by
        show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (algebraMap ℚ (LaurentSeries ℚ) r)
          = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (algebraMap ℚ (AlgebraicClosure ℚ) r)
        simp only [algebraMap_laurentSeries_eq_single, coeffMap_single]
      rw [hc]
      exact Subfield.subset_closure (Or.inl ⟨_, rfl⟩)
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact add_mem ihx ihy
  | inv x hx ihx =>
      rw [map_inv₀]
      exact inv_mem ihx
  | mul x y hx hy ihx ihy =>
      rw [map_mul]
      exact mul_mem ihx ihy

end TwoCoordinateFormula

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k]
    (hAL : IsAtkinLehnerAutFull N q (atkinLehnerInvolutionFull N q)) (hGEN : FunctionFieldGeneration (N * q))
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (g₀ : LaurentSeries ℚ) (y : LaurentSeries ↥A) (g : ↥(modularFunctionFieldBar N))
    (gbar : ↥(modularFunctionFieldC k N))
    (h₀ : g₀ ∈ modularFunctionFieldFull N)
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) g₀)
    (hy : coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) g₀)
    (hgbar : (gbar : LaurentSeries k) = coeffMap red y)
    (hordw : w.ord (gbar - gbar ^ (q ^ 2)) = 1)
    (hordφ : (arithFrobC q k N • w).ord (gbar - gbar ^ (q ^ 2)) = 1)
    (hpole : ∀ U : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
      (P.sp U = w ∨ frobOnPlacesGeomLevel k N data hKr (P.sp U) = w ∨
          P.sp U = frobOnPlacesGeomLevel k N data hKr w) →
        g ∈ U.toValuationSubring) :
    Nonempty (R.NodeCoordinates (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)) w) := by
  have _ := hw

  have hgy : (g : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype y := hg.trans hy.symm
  have hfrob : coeffMap red y ^ q = qExpand k q (coeffMap red y) :=
    TwoCoordinateFormula.coeffMap_pow_char_eq_qExpand red y g₀ hy
  have hcomp : R.redBar.comp (IsLocalRing.residue ↥A) = red := RingHom.ext R.redBar_residue
  have hAB : atkinLehnerBar N q (heckeAlphaBar (AlgebraicClosure ℚ) N q g) = heckeBetaBar (AlgebraicClosure ℚ) N q g :=
    TwoCoordinateFormula.atkinLehnerBar_heckeAlphaBar_eq_heckeBetaBar hAL g
  have hBA : atkinLehnerBar N q (heckeBetaBar (AlgebraicClosure ℚ) N q g) = heckeAlphaBar (AlgebraicClosure ℚ) N q g :=
    TwoCoordinateFormula.atkinLehnerBar_heckeBetaBar_eq_heckeAlphaBar hAL g

  obtain ⟨xBar, hxdef⟩ : ∃ xBar : ↥(modularFunctionFieldBar (N * q)),
      xBar = heckeBetaBar (AlgebraicClosure ℚ) N q g - heckeAlphaBar (AlgebraicClosure ℚ) N q g ^ q := ⟨_, rfl⟩
  obtain ⟨yBar, hydef⟩ : ∃ yBar : ↥(modularFunctionFieldBar (N * q)),
      yBar = heckeAlphaBar (AlgebraicClosure ℚ) N q g - heckeBetaBar (AlgebraicClosure ℚ) N q g ^ q := ⟨_, rfl⟩
  have hxcoe : (xBar : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype (qExpand ↥A q y - y ^ q) := by
    rw [hxdef, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, coe_heckeBetaBar, coe_heckeAlphaBar, hgy,
      map_sub, map_pow, coeffMap_qExpand]
  have hycoe : (yBar : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype (y - qExpand ↥A q y ^ q) := by
    rw [hydef, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, coe_heckeBetaBar, coe_heckeAlphaBar, hgy,
      map_sub, map_pow, coeffMap_qExpand]
  have hALx : atkinLehnerBar N q xBar = yBar := by
    rw [hxdef, hydef, map_sub, map_pow, hBA, hAB]
  have hALy : atkinLehnerBar N q yBar = xBar := by
    rw [hxdef, hydef, map_sub, map_pow, hAB, hBA]

  have hxmem : coeffMap A.subtype (qExpand ↥A q y - y ^ q) ∈ modularFunctionFieldBar (N * q) := hxcoe ▸ xBar.2
  have hymem : coeffMap A.subtype (y - qExpand ↥A q y ^ q) ∈ modularFunctionFieldBar (N * q) := hycoe ▸ yBar.2
  obtain ⟨hx₁', hxres'⟩ := R.residue₁_coeffMap (qExpand ↥A q y - y ^ q) hxmem
  obtain ⟨hy₁', hyres'⟩ := R.residue₁_coeffMap (y - qExpand ↥A q y ^ q) hymem
  have hxeq : xBar = ⟨coeffMap A.subtype (qExpand ↥A q y - y ^ q), hxmem⟩ := Subtype.ext hxcoe
  have hyeq : yBar = ⟨coeffMap A.subtype (y - qExpand ↥A q y ^ q), hymem⟩ := Subtype.ext hycoe
  have hx₁ : xBar ∈ R.R₁.integers := by rw [hxeq]; exact hx₁'
  have hy₁ : yBar ∈ R.R₁.integers := by rw [hyeq]; exact hy₁'
  have hxres : ((R.ι (R.R₁.residue ⟨xBar, hx₁⟩) : ↥(modularFunctionFieldC k N)) : LaurentSeries k) = 0 := by
    have h1 : (⟨xBar, hx₁⟩ : ↥(R.R₁.integers))
        = ⟨⟨coeffMap A.subtype (qExpand ↥A q y - y ^ q), hxmem⟩, hx₁'⟩ := Subtype.ext hxeq
    rw [h1, R.ι_coe, hxres', coeffMap_coeffMap, hcomp, map_sub, map_pow, coeffMap_qExpand, ← hfrob, sub_self]
  have hyres : ((R.ι (R.R₁.residue ⟨yBar, hy₁⟩) : ↥(modularFunctionFieldC k N)) : LaurentSeries k)
      = (gbar : LaurentSeries k) - (gbar : LaurentSeries k) ^ (q ^ 2) := by
    have h1 : (⟨yBar, hy₁⟩ : ↥(R.R₁.integers))
        = ⟨⟨coeffMap A.subtype (y - qExpand ↥A q y ^ q), hymem⟩, hy₁'⟩ := Subtype.ext hyeq
    rw [h1, R.ι_coe, hyres', coeffMap_coeffMap, hcomp, map_sub, map_pow, coeffMap_qExpand, ← hfrob, ← pow_mul,
      ← pow_two, hgbar]

  have hx₂ : xBar ∈ R.R₂.integers := (R.mem_integers₂_iff xBar).mpr (by rw [hALx]; exact hy₁)
  have hy₂ : yBar ∈ R.R₂.integers := (R.mem_integers₂_iff yBar).mpr (by rw [hALy]; exact hx₁)
  have hsubx : ∀ h, R.R₁.residue ⟨atkinLehnerBar N q xBar, h⟩ = R.R₁.residue ⟨yBar, hy₁⟩ :=
    fun h => congrArg R.R₁.residue (Subtype.ext hALx)
  have hsuby : ∀ h, R.R₁.residue ⟨atkinLehnerBar N q yBar, h⟩ = R.R₁.residue ⟨xBar, hx₁⟩ :=
    fun h => congrArg R.R₁.residue (Subtype.ext hALy)
  have hxres2 : ((R.ι (R.R₂.residue ⟨xBar, hx₂⟩) : ↥(modularFunctionFieldC k N)) : LaurentSeries k)
      = (gbar : LaurentSeries k) - (gbar : LaurentSeries k) ^ (q ^ 2) := by
    rw [R.residue₂_eq xBar hx₂, hsubx]
    exact hyres
  have hyres2 : ((R.ι (R.R₂.residue ⟨yBar, hy₂⟩) : ↥(modularFunctionFieldC k N)) : LaurentSeries k) = 0 := by
    rw [R.residue₂_eq yBar hy₂, hsuby]
    exact hxres

  have exres₁ : R.residue₁ ⟨xBar, hx₁⟩ = 0 :=
    Subtype.ext (by rw [residue₁_apply, ZeroMemClass.coe_zero]; exact hxres)
  have eyres₁ : R.residue₁ ⟨yBar, hy₁⟩ = gbar - gbar ^ (q ^ 2) :=
    Subtype.ext (by rw [residue₁_apply, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow]; exact hyres)
  have exres₂ : R.residue₂ ⟨xBar, hx₂⟩ = gbar - gbar ^ (q ^ 2) :=
    Subtype.ext (by rw [residue₂_apply, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow]; exact hxres2)
  have eyres₂ : R.residue₂ ⟨yBar, hy₂⟩ = 0 :=
    Subtype.ext (by rw [residue₂_apply, ZeroMemClass.coe_zero]; exact hyres2)

  have hαβV : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      heckeAlphaBar (AlgebraicClosure ℚ) N q g ∈ V.toValuationSubring ∧
        heckeBetaBar (AlgebraicClosure ℚ) N q g ∈ V.toValuationSubring := by
    intro V hV
    change P.sp (V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) = w at hV
    refine ⟨(TwoCoordinateFormula.mem_restrictAlong_iff (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V g).mp
        (hpole _ (Or.inl hV)), (TwoCoordinateFormula.mem_restrictAlong_iff (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ V g).mp
        (hpole _ ?_)⟩
    rcases P.d1 V with h | h
    · rw [hV] at h
      exact Or.inr (Or.inl h.symm)
    · rw [hV] at h
      exact Or.inr (Or.inr h.symm)
  have hxV : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      xBar ∈ V.toValuationSubring := fun V hV => by
    rw [hxdef]
    exact sub_mem (hαβV V hV).2 (pow_mem (hαβV V hV).1 q)
  have hyV : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      yBar ∈ V.toValuationSubring := fun V hV => by
    rw [hydef]
    exact sub_mem (hαβV V hV).1 (pow_mem (hαβV V hV).2 q)

  have hqg₀ : qExpand ℚ q g₀ ∈ modularFunctionFieldFull (N * q) := full_degeneracy_map_le (N := N) q ⟨g₀, h₀, rfl⟩
  have hg₀' : g₀ ∈ modularFunctionFieldFull (N * q) := full_degeneracy_le (dvd_mul_right N q) h₀
  have hxK : ((xBar : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ NodeLocalized.fieldOver (N * q) (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)) := by
    have : (xBar : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q g₀ - g₀ ^ q) := by
      rw [hxdef, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, coe_heckeBetaBar, coe_heckeAlphaBar, hg, map_sub,
        map_pow, TwoCoordinateFormula.coeffEmb_qExpand]
    rw [this]
    exact TwoCoordinateFormula.coeffEmb_mem_fieldOver_bot hGEN (sub_mem hqg₀ (pow_mem hg₀' q))
  have hyK : ((yBar : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ NodeLocalized.fieldOver (N * q) (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)) := by
    have : (yBar : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (g₀ - qExpand ℚ q g₀ ^ q) := by
      rw [hydef, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, coe_heckeBetaBar, coe_heckeAlphaBar, hg, map_sub,
        map_pow, TwoCoordinateFormula.coeffEmb_qExpand]
    rw [this]
    exact TwoCoordinateFormula.coeffEmb_mem_fieldOver_bot hGEN (sub_mem hg₀' (pow_mem hqg₀ q))

  refine ⟨{ x := ⟨xBar, ⟨hx₁, hx₂, hxV⟩, hxK⟩, y := ⟨yBar, ⟨hy₁, hy₂, hyV⟩, hyK⟩,
            x_fst := ?_, x_snd := ?_, y_snd := ?_, y_fst := ?_ }⟩
  · change R.residue₁ ⟨xBar, hx₁⟩ = 0
    exact exres₁
  · change (arithFrobC q k N • w).ord (R.residue₂ ⟨xBar, hx₂⟩) = 1
    rw [exres₂]
    exact hordφ
  · change R.residue₂ ⟨yBar, hy₂⟩ = 0
    exact eyres₂
  · change w.ord (R.residue₁ ⟨yBar, hy₁⟩) = 1
    rw [eyres₁]
    exact hordw

end

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_nonempty_nodeCoordinates_bot_of_ord_sub_pow_sq_eq_one
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_nonempty_nodeCoordinates_bot_of_ord_sub_pow_sq_eq_one (solution)
