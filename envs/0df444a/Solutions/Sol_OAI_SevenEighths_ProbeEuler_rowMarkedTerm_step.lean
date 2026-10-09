-- Prove2me | solution 1 for OAI.SevenEighths.ProbeEuler.rowMarkedTerm_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T01:45:23.029449+00:00
-- url     : https://prove2.me/submissions/09271fcf-a011-406d-a410-92443198f7ca

import Mathlib
import Definitions.Def_OAIHecke78B017
import Theorems.Thm_OAI_SevenEighths_ProbePrimePower_actualSextic_neg_one_sq

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Gauss
namespace OAI

namespace SevenEighths.ProbeGauss
open scoped BigOperators Classical
noncomputable section

theorem frequencyGauss_nonzero {F : Type*} [Field F] [Fintype F]
    (ξ : MulChar F ℂ) (ψ : AddChar F ℂ) {h : F} (hh : h ≠ 0) :
    frequencyGauss ξ ψ h = ξ⁻¹ h * gaussSum ξ ψ := by
  exact gaussSum_mulShift_eq ξ ψ (Units.mk0 h hh)

theorem frequencyGauss_principal {F : Type*} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (h : F) :
    frequencyGauss 1 ψ h = if h = 0 then (Nat.card Fˣ : ℂ) else -1 := by
  classical
  by_cases hh : h = 0
  · subst h
    simpa [frequencyGauss, Nat.card_eq_fintype_card] using
      (MulChar.sum_one_eq_card_units (R := F) (R' := ℂ))
  · rw [if_neg hh, frequencyGauss_nonzero _ ψ hh, inv_one,
      MulChar.one_apply (isUnit_iff_ne_zero.mpr hh), one_mul]
    exact gaussSum_one_left hψ

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

theorem finite_gauss_convolution {F : Type*} [Field F] [Fintype F]
    (χ ξ : MulChar F ℂ) (ψ : AddChar F ℂ) (h : F) :
    (∑ d : F, χ d * frequencyGauss ξ ψ (h - d)) =
      χ⁻¹ (-1) * gaussSum χ ψ * frequencyGauss (ξ * χ⁻¹) ψ h := by
  classical
  have hfreq (v : F) :
      ξ v * (∑ d : F, χ d * ψ (-(v * d))) =
        χ⁻¹ (-1) * gaussSum χ ψ * (ξ v * χ⁻¹ v) := by
    by_cases hv : v = 0
    · subst v
      simp [MulChar.map_zero]
    · have hn : -v ≠ 0 := neg_ne_zero.mpr hv
      have he := gaussSum_mulShift_eq χ ψ (Units.mk0 (-v) hn)
      simp only [gaussSum, AddChar.mulShift_apply, Units.val_mk0] at he
      have hinv : χ⁻¹ (-v) = χ⁻¹ (-1) * χ⁻¹ v := by rw [← map_mul]; congr 1; ring
      rw [hinv] at he
      have he' : (∑ d : F, χ d * ψ (-(v * d))) =
          (χ⁻¹ (-1) * χ⁻¹ v) * gaussSum χ ψ := by
        simpa only [neg_mul, gaussSum] using he
      rw [he']
      ring
  unfold frequencyGauss
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ v : F, ∑ d : F, χ d * (ξ v * ψ ((h - d) * v))) =
        ∑ v : F, ψ (h * v) * (ξ v * ∑ d : F, χ d * ψ (-(v * d))) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [show (h - d) * v = h * v + -(v * d) by ring, ψ.map_add_eq_mul]
      ring
    _ = ∑ v : F, ψ (h * v) *
        (χ⁻¹ (-1) * gaussSum χ ψ * (ξ v * χ⁻¹ v)) := by simp_rw [hfreq]
    _ = ∑ v : F, χ⁻¹ (-1) * gaussSum χ ψ * ((ξ * χ⁻¹) v * ψ (h * v)) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [MulChar.mul_apply]
      ring

end
end SevenEighths.ProbeGauss

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PrimePower
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein

local notation "O" => ActualEisensteinCubic.O

theorem primePowerGauss_support (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O)
    (hG : primePowerGauss p hp χ n h ≠ 0) : p ^ n ∣ h :=
  conductorFourier_support p (p ^ n) hp (pow_ne_zero _ hp) χ h hG

theorem primePowerGauss_zero_off_support (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O)
    (hdiv : ¬p ^ n ∣ h) : primePowerGauss p hp χ n h = 0 := by
  by_contra hG
  exact hdiv (primePowerGauss_support p hp χ n h hG)

theorem primePowerGauss_lift (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O) :
    primePowerGauss p hp χ n (p ^ n * h) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n * primeGauss p hp χ h := by
  unfold primePowerGauss primeGauss
  rw [conductorFourier_lift]
  have hn : Ideal.absNorm (Ideal.span {p ^ n}) = Ideal.absNorm (Ideal.span {p}) ^ n := by
    rw [← Ideal.span_singleton_pow, map_pow]
  rw [hn, Nat.cast_pow]

theorem primePowerGauss_nonprincipal_extra_divisibility (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (hχ : χ ≠ 1) (n : ℕ) (h : O)
    (hph : p ∣ h) : primePowerGauss p hp χ n (p ^ n * h) = 0 := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := ConcreteTraceCRT.finite_quotient_span hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  rw [primePowerGauss_lift]
  have hz : Ideal.Quotient.mk (Ideal.span {p}) h = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hph)
  have hzero : primeGauss p hp χ h = 0 := by
    rw [primeGauss, tsum_fintype]
    simp only [hz, zero_mul, AddChar.map_zero_eq_one, mul_one]
    exact MulChar.sum_eq_zero_of_ne_one hχ
  rw [hzero, mul_zero]

theorem primePowerGauss_principal (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hψ : quotientTrace p hp ≠ 1) (n : ℕ) (h : O) :
    primePowerGauss p hp 1 n (p ^ n * h) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n *
        (if p ∣ h then (Nat.card (O ⧸ Ideal.span {p})ˣ : ℂ) else -1) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := ConcreteTraceCRT.finite_quotient_span hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  rw [primePowerGauss_lift]
  congr 1
  have hdiv : Ideal.Quotient.mk (Ideal.span {p}) h = 0 ↔ p ∣ h := by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  simpa only [primeGauss, tsum_fintype, ProbeGauss.frequencyGauss, hdiv] using
    ProbeGauss.frequencyGauss_principal (quotientTrace p hp) hψ
      (Ideal.Quotient.mk (Ideal.span {p}) h)

theorem higher_outer_lift_annihilated (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ ξ : MulChar (O ⧸ Ideal.span {p}) ℂ) {n : ℕ} (hn : 0 < n) (m : O) :
    ξ (Ideal.Quotient.mk (Ideal.span {p}) m) * primePowerGauss p hp χ n (-m) = 0 := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  by_cases hG : primePowerGauss p hp χ n (-m) = 0
  · rw [hG, mul_zero]
  · have hdneg := primePowerGauss_support p hp χ n (-m) hG
    have hdpow : p ∣ p ^ n := dvd_pow_self p (Nat.ne_of_gt hn)
    have hdm : p ∣ m := dvd_neg.mp (hdpow.trans hdneg)
    have hz : Ideal.Quotient.mk (Ideal.span {p}) m = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdm)
    rw [hz, MulChar.map_zero, zero_mul]

theorem scalarKOne_eq (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ ξ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O) :
    scalarKOne p hp χ ξ n h =
      χ⁻¹ (-1) * primeGauss p hp χ 1 * primePowerGauss p hp (ξ * χ⁻¹) n h := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := ConcreteTraceCRT.finite_quotient_span hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  by_cases hdiv : p ^ n ∣ h
  · obtain ⟨k, rfl⟩ := hdiv
    have hmk (d : O ⧸ Ideal.span {p}) :
        Ideal.Quotient.mk (Ideal.span {p})
          (k - GaussianShiftedPartition.representative p d) =
          Ideal.Quotient.mk (Ideal.span {p}) k - d := by
      rw [map_sub, GaussianShiftedPartition.representative_spec]
    have hscalar : scalarKOne p hp χ ξ n (p ^ n * k) =
        (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n *
          ∑ d : O ⧸ Ideal.span {p}, χ d * ProbeGauss.frequencyGauss ξ
            (quotientTrace p hp) (Ideal.Quotient.mk _ k - d) := by
      unfold scalarKOne
      rw [tsum_fintype, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [← mul_sub, primePowerGauss_lift]
      have he : primeGauss p hp ξ (k - GaussianShiftedPartition.representative p d) =
          ProbeGauss.frequencyGauss ξ (quotientTrace p hp) (Ideal.Quotient.mk _ k - d) := by
        rw [primeGauss, tsum_fintype]
        simp only [hmk, ProbeGauss.frequencyGauss]
      rw [he]
      ring
    rw [hscalar, ProbeGauss.finite_gauss_convolution, primePowerGauss_lift]
    have hG : primeGauss p hp χ 1 = gaussSum χ (quotientTrace p hp) := by
      simp [primeGauss, tsum_fintype, gaussSum]
    have hF : primeGauss p hp (ξ * χ⁻¹) k =
        ProbeGauss.frequencyGauss (ξ * χ⁻¹) (quotientTrace p hp) (Ideal.Quotient.mk _ k) := by
      simp only [primeGauss, tsum_fintype, ProbeGauss.frequencyGauss]
    rw [hG, hF]
    ring
  · rw [primePowerGauss_zero_off_support p hp (ξ * χ⁻¹) n h hdiv, mul_zero]
    unfold scalarKOne
    rw [tsum_fintype]
    apply Finset.sum_eq_zero
    intro d _
    have hndiv : ¬p ^ n ∣ h - p ^ n * GaussianShiftedPartition.representative p d := by
      intro hd
      apply hdiv
      have ha := dvd_add hd (dvd_mul_right (p ^ n)
        (GaussianShiftedPartition.representative p d))
      simpa only [sub_add_cancel] using ha
    rw [primePowerGauss_zero_off_support p hp ξ n _ hndiv, mul_zero]

end SevenEighths.ProbePrimePower
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GaussValuation
namespace OAI

noncomputable section
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem primePowerGauss_at_pow_nonprincipal (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (hχ : χ ≠ 1) (n j : ℕ) :
    primePowerGauss p hp.ne_zero χ n (p ^ j) =
      if j = n then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n * primeGauss p hp.ne_zero χ 1
      else 0 := by
  by_cases he : j = n
  · subst j
    rw [if_pos rfl]
    simpa only [mul_one] using primePowerGauss_lift p hp.ne_zero χ n 1
  rw [if_neg he]
  rcases lt_or_gt_of_ne he with hjn | hnj
  · apply primePowerGauss_zero_off_support
    rw [pow_dvd_pow_iff hp.ne_zero hp.not_isUnit]
    omega
  · have hle : n ≤ j := Nat.le_of_lt hnj
    have heq : p ^ j = p ^ n * p ^ (j - n) := by rw [← pow_add, Nat.add_sub_of_le hle]
    rw [heq]
    apply primePowerGauss_nonprincipal_extra_divisibility p hp.ne_zero χ hχ
    exact dvd_pow_self p (by omega)

theorem primePowerGauss_at_pow_principal (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hψ : quotientTrace p hp.ne_zero ≠ 1) (n j : ℕ) :
    primePowerGauss p hp.ne_zero 1 n (p ^ j) =
      (if n + 1 ≤ j then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (n + 1) else 0) -
      (if n ≤ j then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n else 0) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := ConcreteTraceCRT.finite_quotient_span hp.ne_zero
  have hcard : (Nat.card (O ⧸ Ideal.span {p})ˣ : ℂ) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) - 1 := by
    rw [Nat.card_units, Nat.cast_sub (Nat.card_pos : 0 < Nat.card (O ⧸ Ideal.span {p})),
      Nat.cast_one]
    rfl
  rcases lt_trichotomy j n with hjn | he | hnj
  · rw [if_neg (by omega), if_neg (by omega), sub_self]
    apply primePowerGauss_zero_off_support
    rw [pow_dvd_pow_iff hp.ne_zero hp.not_isUnit]
    omega
  · subst j
    have hnot : ¬p ∣ (1 : O) := by simpa only [isUnit_iff_dvd_one] using hp.not_isUnit
    simpa only [mul_one, if_neg hnot, if_neg (Nat.not_succ_le_self n),
      if_pos (le_refl n), zero_sub, mul_neg_one] using
      primePowerGauss_principal p hp.ne_zero hψ n 1
  · have hle : n ≤ j := by omega
    have heq : p ^ j = p ^ n * p ^ (j - n) := by rw [← pow_add, Nat.add_sub_of_le hle]
    have hd : p ∣ p ^ (j - n) := dvd_pow_self p (by omega)
    rw [heq, primePowerGauss_principal, if_pos hd, if_pos (by omega : n + 1 ≤ j),
      if_pos hle, hcard, pow_succ]
    ring
    exact hψ

end SevenEighths.ProbePrimePower
end

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

theorem actualSextic_primePowerGauss_at_pow (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (r n j : ℕ) :
    primePowerGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg ^ r) n (p ^ j) =
      if 6 ∣ r then
        (if n + 1 ≤ j then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (n + 1) else 0) -
        (if n ≤ j then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n else 0)
      else if j = n then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n *
        primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg ^ r) 1 else 0 := by
  by_cases hr : 6 ∣ r
  · rw [if_pos hr, (actualSextic_pow_eq_one_iff _ hg hc r).mpr hr]
    apply primePowerGauss_at_pow_principal p hp
    have hprim : (quotientTrace p hp.ne_zero).IsPrimitive :=
      GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp.ne_zero
    simpa using hprim (a := 1) one_ne_zero
  · rw [if_neg hr]
    exact primePowerGauss_at_pow_nonprincipal p hp _
      (fun h => hr ((actualSextic_pow_eq_one_iff _ hg hc r).mp h)) n j

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

lemma exactQuotient_eq (a b c : O) (h : b ∣ a) (hb : b ≠ 0) (he : a = b*c) :
    exactQuotient a b h = c := by
  apply mul_left_cancel₀ hb
  exact (exactQuotient_spec a b h).symm.trans he

theorem positiveScalar_kone_jzero (p : O) (hp : Prime p)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) :
    positiveScalar p hp.ne_zero χ n 1 0 = 0 := by
  simp only [positiveScalar, Nat.one_ne_zero, ite_false]
  rw [pow_one]
  simp only [pow_zero, pow_one]
  refine (tsum_congr (g := fun _ => (0:ℂ)) ?_).trans tsum_zero
  intro d
  rw [dif_neg]
  intro hd
  have hd2 : p ∣ p^(n+1)*representative p d :=
    (dvd_pow_self p (by omega : n+1 ≠ 0)).mul_right _
  have hunit : p ∣ (1:O) := by
    have := dvd_add hd hd2
    simpa only [sub_add_cancel] using this
  exact hp.not_isUnit (isUnit_iff_dvd_one.mpr hunit)

theorem positiveScalar_kone_convolution (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n j : ℕ) :
    positiveScalar p hp χ n 1 (j+1) = scalarKOne p hp χ (χ^(n+1)) n (p^j) := by
  simp only [positiveScalar, Nat.one_ne_zero, ite_false, scalarKOne]
  rw [pow_one]
  simp only [pow_one]
  apply tsum_congr
  intro d
  have he : p^(j+1)-p^(n+1)*representative p d = p*(p^j-p^n*representative p d) := by
    simp only [pow_succ]
    ring
  have hd : p ∣ p^(j+1)-p^(n+1)*representative p d := ⟨_,he⟩
  rw [dif_pos hd, exactQuotient_eq _ _ _ hd hp he, representative_spec]

theorem positiveScalar_kone (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n j : ℕ) :
    positiveScalar p hp χ n 1 (j+1) =
      χ⁻¹ (-1) * primeGauss p hp χ 1 * primePowerGauss p hp (χ^n) n (p^j) := by
  rw [positiveScalar_kone_convolution, scalarKOne_eq]
  have he : χ^(n+1)*χ⁻¹ = χ^n := by rw [pow_succ, mul_assoc, mul_inv_cancel, mul_one]
  rw [he]

end SevenEighths.ProbePrimePower
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

end SevenEighths.ProbePhase
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

lemma actualSextic_six (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2) : actualSextic P hg ^ 6 = 1 :=
  (actualSextic_pow_eq_one_iff P hg hc 6).mpr (by decide)

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

theorem primePowerGauss_lift_add (p : O) (hp : Prime p)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n k : ℕ) (h : O) :
    primePowerGauss p hp.ne_zero χ (n+k) (p^k*h) =
      (Ideal.absNorm (Ideal.span {p}):ℂ)^k * primePowerGauss p hp.ne_zero χ n h := by
  by_cases hd : p^n ∣ h
  · obtain ⟨a, rfl⟩ := hd
    have he : p^k*(p^n*a) = p^(n+k)*a := by rw [pow_add]; ring
    rw [he, primePowerGauss_lift, primePowerGauss_lift, pow_add]
    ring
  · have hbig : ¬p^(n+k) ∣ p^k*h := by
      rw [pow_add, mul_comm (p^n) (p^k), mul_dvd_mul_iff_left (pow_ne_zero _ hp.ne_zero)]
      exact hd
    rw [primePowerGauss_zero_off_support _ _ _ _ _ hbig,
      primePowerGauss_zero_off_support _ _ _ _ _ hd, mul_zero]

theorem gauss_exactQuotient_lift (p : O) (hp : Prime p)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n k : ℕ) (h : O) :
    (if hd : p^k ∣ h then primePowerGauss p hp.ne_zero χ n (exactQuotient h (p^k) hd) else 0) =
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^k)⁻¹ * primePowerGauss p hp.ne_zero χ (n+k) h := by
  have hq : (Ideal.absNorm (Ideal.span {p}):ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  by_cases hd : p^k ∣ h
  · rw [dif_pos hd]
    conv_rhs => rw [exactQuotient_spec h (p^k) hd]
    rw [primePowerGauss_lift_add p hp, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq), one_mul]
  · rw [dif_neg hd]
    have hnd : ¬p^(n+k) ∣ h := by
      intro he
      exact hd ((show p^k ∣ p^(n+k) from ⟨p^n, by rw [pow_add]; ring⟩).trans he)
    rw [primePowerGauss_zero_off_support _ _ _ _ _ hnd, mul_zero]

theorem positiveScalar_full_lift (p : O) (hp : Prime p)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n k j : ℕ) (hk : k ≠ 0) :
    positiveScalar p hp.ne_zero χ n k j =
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^k)⁻¹ *
        ∑' d : O ⧸ Ideal.span {p^k},
          (χ^k) (Ideal.Quotient.mk _ (representative (p^k) d)) *
            primePowerGauss p hp.ne_zero (χ^(n+1)) (n+k)
              (p^j-p^(n+1)*representative (p^k) d) := by
  rw [positiveScalar, if_neg hk, ← tsum_mul_left]
  apply tsum_congr
  intro d
  have he := gauss_exactQuotient_lift p hp (χ^(n+1)) n k
    (p^j-p^(n+1)*representative (p^k) d)
  by_cases hd : p^k ∣ p^j-p^(n+1)*representative (p^k) d
  · rw [dif_pos hd] at he ⊢
    rw [he]
    ring
  · rw [dif_neg hd] at he ⊢
    linear_combination (χ^k) (Ideal.Quotient.mk _ (representative (p^k) d)) * he

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.ScalarVanishing
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition
local notation "O" => ActualEisensteinCubic.O

theorem higher_convolution_zero (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ ξ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n m : ℕ) (H : O) :
    (∑' d : O ⧸ Ideal.span {p^(m+2)},
      χ (Ideal.Quotient.mk _ (representative (p^(m+2)) d)) *
        primePowerGauss p hp.ne_zero ξ (n+(m+2))
          (H-p^(n+1)*representative (p^(m+2)) d)) = 0 := by
  let : Finite (O ⧸ Ideal.span {p^(m+2)}) :=
    ConcreteTraceCRT.finite_quotient_span (pow_ne_zero _ hp.ne_zero)
  let : Fintype (O ⧸ Ideal.span {p^(m+2)}) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {p*p^(n+(m+2))}) :=
    ConcreteTraceCRT.finite_quotient_span (mul_ne_zero hp.ne_zero (pow_ne_zero _ hp.ne_zero))
  let : Fintype (O ⧸ Ideal.span {p*p^(n+(m+2))}) := Fintype.ofFinite _
  have hmod : p*p^(n+(m+2)) = p^(m+2)*p^(n+1) := by
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  have hinner (V : O) : (∑' d : O ⧸ Ideal.span {p^(m+2)},
      χ (Ideal.Quotient.mk _ (representative (p^(m+2)) d)) *
        quotientTrace (p^(m+2)) (pow_ne_zero _ hp.ne_zero)
          (Ideal.Quotient.mk _ ((-V)*representative (p^(m+2)) d))) =
      primePowerGauss p hp.ne_zero χ (m+1) (-V) := by
    change quotientFourier p (p^(m+2)) (pow_ne_zero _ hp.ne_zero) χ (-V) = _
    rw [primePowerGauss_eq_quotientFourier]
    apply quotientFourier_congr
    rw [← pow_succ']
  unfold primePowerGauss conductorFourier
  simp_rw [tsum_fintype, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro y hy
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
  change (∑ d : O ⧸ Ideal.span {p^(m+2)},
    χ (Ideal.Quotient.mk _ (representative (p^(m+2)) d)) *
      (ξ (Ideal.Quotient.mk _ v) *
        quotientTrace (p*p^(n+(m+2))) _
          (Ideal.Quotient.mk _ (H-p^(n+1)*representative (p^(m+2)) d)*Ideal.Quotient.mk _ v))) = 0
  have ht (d : O ⧸ Ideal.span {p^(m+2)}) :
      quotientTrace (p*p^(n+(m+2))) (mul_ne_zero hp.ne_zero (pow_ne_zero _ hp.ne_zero))
        (Ideal.Quotient.mk _ ((H-p^(n+1)*representative (p^(m+2)) d)*v)) =
      quotientTrace (p*p^(n+(m+2))) (mul_ne_zero hp.ne_zero (pow_ne_zero _ hp.ne_zero))
        (Ideal.Quotient.mk _ (H*v)) *
      quotientTrace (p^(m+2)) (pow_ne_zero _ hp.ne_zero)
        (Ideal.Quotient.mk _ ((-v)*representative (p^(m+2)) d)) := by
    have ht := quotientTrace_split_frequency (p^(m+2)) (p^(n+1))
      (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hp.ne_zero) H
      (representative (p^(m+2)) d) v
    simp only [quotientTrace_mk] at ht ⊢
    simpa only [← hmod] using ht
  simp_rw [← map_mul, ht]
  calc
    _ = ξ (Ideal.Quotient.mk _ v) *
        quotientTrace (p*p^(n+(m+2))) (mul_ne_zero hp.ne_zero (pow_ne_zero _ hp.ne_zero))
          (Ideal.Quotient.mk _ (H*v)) *
        ∑ d : O ⧸ Ideal.span {p^(m+2)},
          χ (Ideal.Quotient.mk _ (representative (p^(m+2)) d)) *
            quotientTrace (p^(m+2)) (pow_ne_zero _ hp.ne_zero)
              (Ideal.Quotient.mk _ ((-v)*representative (p^(m+2)) d)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = quotientTrace (p*p^(n+(m+2))) (mul_ne_zero hp.ne_zero (pow_ne_zero _ hp.ne_zero))
          (Ideal.Quotient.mk _ (H*v)) *
        (ξ (Ideal.Quotient.mk _ v) * primePowerGauss p hp.ne_zero χ (m+1) (-v)) := by
      have hi := hinner v
      rw [tsum_fintype] at hi
      rw [hi]
      ring
    _ = 0 := by rw [higher_outer_lift_annihilated p hp.ne_zero χ ξ (by omega : 0 < m+1) v, mul_zero]

theorem positiveScalar_kge_two (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n m j : ℕ) :
    positiveScalar p hp.ne_zero χ n (m+2) j = 0 := by
  rw [positiveScalar_full_lift p hp χ n (m+2) j (by omega),
    higher_convolution_zero p hp (χ^(m+2)) (χ^(n+1)) n m (p^j), mul_zero]

end SevenEighths.ProbePrimePower
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.ScalarTable
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

theorem actualSextic_gaussValuationTable (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (r n j : ℕ) :
    primePowerGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg ^ r) n (p^j) =
      gaussValuationTable (Ideal.absNorm (Ideal.span {p}))
        (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg ^ r) 1) r n j :=
  actualSextic_primePowerGauss_at_pow p hp hg hc r n j

theorem positiveScalar_actual_table (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (n k j : ℕ) :
    let χ := actualSextic (Ideal.span {p}) hg
    let Q : ℂ := Ideal.absNorm (Ideal.span {p})
    positiveScalar p hp.ne_zero χ n k j =
      if k=0 then gaussValuationTable Q (primeGauss p hp.ne_zero (χ^(n+1)) 1) (n+1) n j
      else if k=1 ∧ 1 ≤ j then
        (χ (-1))⁻¹ * primeGauss p hp.ne_zero χ 1 *
          gaussValuationTable Q (primeGauss p hp.ne_zero (χ^n) 1) n n (j-1)
      else 0 := by
  dsimp only
  rcases k with _ | k
  · rw [if_pos rfl, positiveScalar_kzero, actualSextic_gaussValuationTable p hp hg hc]
  rcases k with _ | k
  · rcases j with _ | j
    · simp only [ zero_add, Nat.one_ne_zero, ite_false,
          show ¬(1:ℕ) ≤ 0 by omega, and_false]
      exact positiveScalar_kone_jzero p hp _ n
    · rw [if_neg (by omega : (1:ℕ) ≠ 0), if_pos ⟨rfl, by omega⟩,
        positiveScalar_kone p hp.ne_zero, MulChar.inv_apply_eq_inv',
        actualSextic_gaussValuationTable p hp hg hc]
      simp
  · rw [if_neg (by omega), if_neg (by omega), positiveScalar_kge_two p hp]

end SevenEighths.ProbePrimePower
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsRecurrence
namespace OAI

noncomputable section
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

lemma gaussValuationTable_step_six (Q G : ℂ) (r n j : ℕ) :
    gaussValuationTable Q G (r+6) (n+6) (j+6)=Q^6*gaussValuationTable Q G r n j := by
  have hd : 6∣r+6 ↔ 6∣r := by omega
  have hle : n+6+1≤j+6 ↔ n+1≤j := by omega
  have hle' : n+6≤j+6 ↔ n≤j := by omega
  have he : j+6=n+6 ↔ j=n := by omega
  simp only [gaussValuationTable,hd,hle,hle',he]
  split_ifs <;> simp [pow_add] <;> ring

theorem positiveScalar_step_six (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (n k j : ℕ) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (n+6) k (j+6)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^6*
        positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j := by
  rw [positiveScalar_actual_table p hp hg hc,positiveScalar_actual_table p hp hg hc]
  have hp6 (a : ℕ) : actualSextic (Ideal.span {p}) hg^(a+6)=
      actualSextic (Ideal.span {p}) hg^a := by
    rw [pow_add,actualSextic_six _ hg hc,mul_one]
  by_cases hk : k=0
  · simp only [hk,ite_true]
    rw [show n+6+1=(n+1)+6 by omega,hp6,gaussValuationTable_step_six]
  · simp only [if_neg hk]
    by_cases hk1 : k=1
    · subst k
      by_cases hj : 1≤j
      · rw [if_pos ⟨rfl,by omega⟩,if_pos ⟨rfl,hj⟩,hp6,
          show j+6-1=(j-1)+6 by omega,gaussValuationTable_step_six]
        ring
      · have hz : j=0 := by omega
        subst j
        simp only [show (1:ℕ)≤0+6 by omega,show ¬(1:ℕ)≤0 by omega,
          and_true,and_false,ite_true,ite_false,mul_zero]
        simp only [gaussValuationTable]
        split_ifs <;> simp_all ; omega
    · rw [if_neg (by omega),if_neg (by omega),mul_zero]

end SevenEighths.ProbePrimePower
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsWeights
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma localCubePhase_step_two (C omega : ℂ) (hC : C ^2=omega) (ho : omega^2=1)
    (e l k : ℕ) : localCubePhase C omega e (l+2) k=localCubePhase C omega e l k := by
  have hchoose : (l+2).choose 2=l.choose 2+2*l+1 := by
    rw [show l+2=(l+1)+1 by omega,Nat.choose_succ_succ,Nat.choose_one_right,
      Nat.choose_succ_succ,Nat.choose_one_right]
    change l+1+(l+l.choose 2)=l.choose 2+2*l+1
    omega
  unfold localCubePhase
  rw [pow_add C l 2,hC,hchoose]
  have he : (e+3*(l+2))*k+e*(l+2)+(l.choose 2+2*l+1)=
      ((e+3*l)*k+e*l+l.choose 2)+(2*(3*k+e+l)+1) := by ring
  have ht : omega^(2*(3*k+e+l)+1)=omega := by
    rw [pow_add,pow_mul omega 2,ho,one_pow,pow_one,one_mul]
  rw [he,pow_add omega _ (2*(3*k+e+l)+1),ht]
  calc
    _ = C ^l*omega^((e+3*l)*k+e*l+l.choose 2)*omega^2 := by ring
    _ = _ := by rw [ho,mul_one]

theorem weightedScalar_step_two (Q eta a G1 C omega X W V scalar : ℂ)
    (hQ : Q≠0) (hC : C ^2=omega) (ho : omega^2=1) (e l k m : ℕ) :
    weightedScalar Q eta a G1 C omega X W V (Q^6*scalar) e (l+2) k (m+1)=
      evenRatio Q a X V*weightedScalar Q eta a G1 C omega X W V scalar e l k m := by
  unfold weightedScalar evenRatio
  rw [localCubePhase_step_two C omega hC ho]
  rw [pow_add (a*X^3/Q) l 2,pow_succ V m]
  have hbase : (a*X^3/Q)^2*Q^6=a^2*Q^4*X^6 := by
    field_simp
  linear_combination (-eta*X/G1)^e*(a*X^3/Q)^l*localCubePhase C omega e l k*scalar*W^k*V^m*V*hbase

theorem rowWeightedScalar_parameters (Q eta a G1 C omega X W V rho scalar : ℂ)
    (e l k m : ℕ) :
    rowWeightedScalar Q eta a G1 C omega X W V rho scalar e l k m=
      weightedScalar Q (eta/rho) (a/rho^3) G1 C omega X (rho*W) V scalar e l k m := by
  unfold rowWeightedScalar weightedScalar
  simp only [pow_add,pow_mul,mul_pow,div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring

theorem evenRatio_unit (Q a X V rho : ℂ) (hρ : rho^6=1) :
    evenRatio Q (a/rho^3) X V=evenRatio Q a X V := by
  unfold evenRatio
  rw [div_pow,←pow_mul,show 3*2=6 by decide,hρ,div_one]

theorem rowWeightedScalar_step_two (Q eta a G1 C omega X W V rho scalar : ℂ)
    (hQ : Q≠0) (hC : C ^2=omega) (ho : omega^2=1) (hρ : rho^6=1) (e l k m : ℕ) :
    rowWeightedScalar Q eta a G1 C omega X W V rho (Q^6*scalar) e (l+2) k (m+1)=
      evenRatio Q a X V*rowWeightedScalar Q eta a G1 C omega X W V rho scalar e l k m := by
  rw [rowWeightedScalar_parameters,rowWeightedScalar_parameters,
    weightedScalar_step_two Q (eta/rho) (a/rho^3) G1 C omega X (rho*W) V scalar hQ hC ho,
    evenRatio_unit Q a X V rho hρ]

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LocalSeries
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

include hc in
lemma localGamma_conjugate_three_sq :
    (star (localGamma p hp.ne_zero hg 3))^2 = actualSextic (Ideal.span {p}) hg (-1) := by
  have hg3 : localGamma p hp.ne_zero hg 3 ^ 2 = actualSextic (Ideal.span {p}) hg (-1) :=
    ProbePhase.normalizedTraceGauss_three_sq p hp.ne_zero hg hc
  rw [← star_pow, hg3]
  have hω := actualSextic_neg_one_sq (Ideal.span {p}) hg
  rcases (sq_eq_one_iff).mp hω with h | h
  · simp [h]
  · simp [h]

omit [(Ideal.span {p}).IsMaximal] in
include hp in
lemma primeNorm_ne_zero : (Ideal.absNorm (Ideal.span {p}):ℂ) ≠ 0 := by
  exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)

include hc

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsSeries
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

include hc in
theorem rowMarkedTerm_step_oai (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (j e l k m : ℕ) (ht : 0<e+3*l) :
    rowMarkedTerm p hp hg eta a X W V rho j e (l+2) k (m+1)=
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V *
        rowMarkedTerm p hp hg eta a X W V rho j e l k m := by
  unfold rowMarkedTerm
  rw [if_neg (by omega),if_neg (by omega),
    show e+3*(l+2)-1=(e+3*l-1)+6 by omega,
    show j+6*(m+1)=(j+6*m)+6 by omega,
    positiveScalar_step_six p hp hg hc]
  exact rowWeightedScalar_step_two _ _ _ _ _ _ _ _ _ _ _ (primeNorm_ne_zero p hp)
    (localGamma_conjugate_three_sq p hp hg hc) (actualSextic_neg_one_sq _ hg) hρ e l k m

end SevenEighths.ProbeEuler
end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.ProbeEuler.rowMarkedTerm_step_oai := @OAI.SevenEighths.ProbeEuler.rowMarkedTerm_step_oai
