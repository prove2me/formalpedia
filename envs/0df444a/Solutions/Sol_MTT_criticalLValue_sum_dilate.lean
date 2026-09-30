-- Prove2me | solution 1 for MTT.criticalLValue_sum_dilate
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T16:46:59.891239+00:00
-- url     : https://prove2.me/submissions/61d18291-194e-4da0-b080-af0c724a2116

import Definitions.Def_MTT_Arithmetic
import Mathlib.NumberTheory.ModularForms.LFunction
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
noncomputable section

namespace MTT

/-- Cusp forms for `Γ₁(M)` extend through `ofComplex` as one-periodic functions. -/
theorem cuspForm_periodic_comp_ofComplex {M k : ℕ} (_hM : 0 < M)
    (g : CuspForm (GammaOne M) (k : ℤ)) :
    Function.Periodic (g ∘ UpperHalfPlane.ofComplex) 1 := by
  have hperiod : (1 : ℝ) ∈ (GammaOne M).strictPeriods := by
    change (1 : ℝ) ∈
      (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods
    simp
  simpa using SlashInvariantFormClass.periodic_comp_ofComplex g hperiod

end MTT

open scoped BigOperators

namespace MTT

/-- The finite-translate inverse twist commutes with finite linear combinations. -/
theorem inverseTwist_sum_mul {α : Type*} [Fintype α] (ι : Qbar →+* ℂ)
    (f : α → UpperHalfPlane → ℂ) (c : α → ℂ) (m : ℕ) [NeZero m]
    (χ : DirichletCharacter Qbar m) (z : UpperHalfPlane) :
    inverseTwist ι (fun w ↦ ∑ i, c i * f i w) m χ z =
      ∑ i, c i * inverseTwist ι (f i) m χ z := by
  simp only [inverseTwist, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  ext i
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Integer dilation of the translates can be reduced modulo the twist modulus. -/
theorem periodic_dilate_translate (f : UpperHalfPlane → ℂ)
    (hf : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1)
    {m : ℕ} [NeZero m] (d : ℕ) (z : ℂ) (a : ZMod m) :
    f (UpperHalfPlane.ofComplex ((d : ℂ) * (z + (a.val : ℂ) / m))) =
      f (UpperHalfPlane.ofComplex ((d : ℂ) * z + (((d : ZMod m) * a).val : ℂ) / m)) := by
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hval : ((d : ZMod m) * a).val = (d * a.val) % m := by
    calc
      _ = ((d * a.val : ℕ) : ZMod m).val := by
        simp only [Nat.cast_mul, ZMod.natCast_zmod_val]
      _ = _ := ZMod.val_natCast _ _
  have hdecomp : (d : ℂ) * (a.val : ℂ) =
      (((d : ZMod m) * a).val : ℂ) + (m : ℂ) * ((d * a.val / m : ℕ) : ℂ) := by
    rw [hval]
    exact_mod_cast (Nat.mod_add_div (d * a.val) m).symm
  have heq : (d : ℂ) * (z + (a.val : ℂ) / m) =
      (d : ℂ) * z + (((d : ZMod m) * a).val : ℂ) / m + (d * a.val / m : ℕ) := by
    field_simp
    linear_combination hdecomp
  rw [heq]
  simpa only [Function.comp_apply, mul_one] using
    hf.nat_mul (d * a.val / m)
      ((d : ℂ) * z + (((d : ZMod m) * a).val : ℂ) / m)

/-- Dilation prime to the modulus acts on the inverse twist by the inverse character. -/
theorem inverseTwist_dilate_of_periodic (ι : Qbar →+* ℂ)
    (f : UpperHalfPlane → ℂ)
    (hf : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1)
    {m : ℕ} [NeZero m] (χ : DirichletCharacter Qbar m)
    (d : ℕ) (hd : 0 < d) (hcop : Nat.Coprime d m) (z : UpperHalfPlane) :
    inverseTwist ι (fun w ↦ f (UpperHalfPlane.ofComplex ((d : ℂ) * (w : ℂ)))) m χ z =
      (ι (χ d))⁻¹ * inverseTwist ι f m χ
        (UpperHalfPlane.ofComplex ((d : ℂ) * (z : ℂ))) := by
  have hχ : ι (χ d) ≠ 0 :=
    ((ZMod.isUnit_iff_coprime d m).2 hcop |>.map χ.toMonoidHom |>.map ι.toMonoidHom).ne_zero
  have him (a : ZMod m) : 0 < ((z : ℂ) + (a.val : ℂ) / m).im := by
    simpa only [Complex.add_im, Complex.div_natCast_im, Complex.natCast_im, zero_div,
      add_zero, UpperHalfPlane.coe_im] using z.im_pos
  have hdim : 0 < ((d : ℂ) * (z : ℂ)).im := by
    simpa using mul_pos (show (0 : ℝ) < d by exact_mod_cast hd) z.im_pos
  simp only [inverseTwist, UpperHalfPlane.ofComplex_apply_of_im_pos hdim,
    UpperHalfPlane.coe_mk]
  simp_rw [UpperHalfPlane.ofComplex_apply_of_im_pos (him _),
    periodic_dilate_translate f hf d]
  let u := ZMod.unitOfCoprime d hcop
  have hsum := Equiv.sum_comp u.mulLeft
    (fun a : ZMod m ↦ ι (χ a) *
      f (UpperHalfPlane.ofComplex ((d : ℂ) * (z : ℂ) + (a.val : ℂ) / m)))
  simp only [Units.mulLeft_apply, u, ZMod.coe_unitOfCoprime, map_mul, mul_assoc,
    ← Finset.mul_sum] at hsum
  rw [← hsum]
  field_simp

end MTT

open scoped BigOperators MatrixGroups Pointwise ModularForm
open UpperHalfPlane MeasureTheory Matrix ConjAct

namespace MTT

private def translationSL (r : ℚ) : SL(2, ℚ) :=
  ⟨!![1, r; 0, 1], by simp [Matrix.det_fin_two]⟩

private def translationGL (r : ℚ) : GL (Fin 2) ℝ :=
  ((translationSL r : GL (Fin 2) ℚ).map (Rat.castHom ℝ))

private lemma translationGL_eq (r : ℚ) :
    translationGL r = Matrix.SpecialLinearGroup.mapGL ℝ (translationSL r) := by
  ext i j
  rfl

private lemma translationGL_apply (r : ℚ) (i j : Fin 2) :
    translationGL r i j = (!![1, (r : ℝ); 0, 1]) i j := by
  change (((!![1, r; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ) i j : ℚ) : ℝ) = _
  fin_cases i <;> fin_cases j <;> norm_num

private lemma translationGL_slash (r : ℚ) (k : ℤ) (f : UpperHalfPlane → ℂ)
    (z : UpperHalfPlane) :
    (f ∣[k] translationGL r) z = f (UpperHalfPlane.ofComplex ((z : ℂ) + r)) := by
  have hdet : (translationGL r).det = 1 := by simp [translationGL_eq]
  have hact : translationGL r • z = ofComplex ((z : ℂ) + r) := by
    ext
    rw [coe_smul_of_det_pos (by simp [hdet]),
      ofComplex_apply_of_im_pos (by simpa using z.im_pos)]
    simp [num, denom, translationGL_apply]
  rw [ModularForm.slash_apply, hact]
  simp [σ, hdet, denom, translationGL_apply]

lemma integrableOn_cuspForm_vertical_pow {M k : ℕ} (hM : 0 < M) (hk : 2 ≤ k)
    (g : CuspForm (GammaOne M) (k : ℤ)) (r : ℚ) (j : ℕ) :
    IntegrableOn (fun t : ℝ ↦ g (ofComplex (Complex.I * t + (r : ℂ))) * (t : ℂ) ^ j)
      (Set.Ioi 0) := by
  have : NeZero M := ⟨hM.ne'⟩
  have : (toConjAct (translationGL r)⁻¹ • GammaOne M).IsArithmetic := by
    convert Subgroup.IsArithmetic.conj (GammaOne M) (translationSL r : GL (Fin 2) ℚ)⁻¹
      using 1
    simp [translationGL]
  have hk' : (0 : ℤ) < k := by omega
  have hint := ((CuspForm.isStrongFEPair hk' (CuspForm.translate g (translationGL r))).hasMellin
    ((j : ℂ) + 1)).1
  have hfun (t : ℝ) (ht : 0 < t) :
      CuspForm.translate g (translationGL r) (ofComplex (Complex.I * t)) =
        g (ofComplex (Complex.I * t + (r : ℂ))) := by
    change ((g : UpperHalfPlane → ℂ) ∣[(k : ℤ)] translationGL r)
      (ofComplex (Complex.I * t)) = _
    rw [translationGL_slash]
    rw [ofComplex_apply_of_im_pos (z := Complex.I * t) (by simpa)]
  apply hint.congr_fun _ measurableSet_Ioi
  intro t ht
  change (t : ℂ) ^ ((j : ℂ) + 1 - 1) •
    CuspForm.translate g (translationGL r) (ofComplex (Complex.I * t)) = g _ * _
  rw [hfun t ht]
  simp [mul_comm]

lemma integrableOn_cuspForm_vertical_mul_pow {M k : ℕ} (hM : 0 < M) (hk : 2 ≤ k)
    (g : CuspForm (GammaOne M) (k : ℤ)) (r : ℚ) (j : ℕ) {d : ℝ} (hd : 0 < d) :
    IntegrableOn (fun t : ℝ ↦
      g (ofComplex (Complex.I * (d * t) + (r : ℂ))) * (t : ℂ) ^ j) (Set.Ioi 0) := by
  have hint : MellinConvergent (fun t : ℝ ↦ g (ofComplex (Complex.I * t + (r : ℂ))))
      ((j : ℂ) + 1) := by
    simpa [MellinConvergent, mul_comm] using integrableOn_cuspForm_vertical_pow hM hk g r j
  have hscaled := (MellinConvergent.comp_mul_left hd).mpr hint
  simpa [MellinConvergent, mul_comm] using hscaled

lemma integrableOn_inverseTwist_vertical_pow {M k m : ℕ} [NeZero m]
    (hM : 0 < M) (hk : 2 ≤ k) (ι : Qbar →+* ℂ)
    (g : CuspForm (GammaOne M) (k : ℤ)) (χ : DirichletCharacter Qbar m) (j : ℕ) :
    IntegrableOn (fun t : ℝ ↦ inverseTwist ι g m χ (ofComplex (Complex.I * t)) *
      (t : ℂ) ^ j) (Set.Ioi 0) := by
  have hi (a : ZMod m) : IntegrableOn (fun t : ℝ ↦
      ι (χ a) * (g (ofComplex (Complex.I * t + ((a.val : ℚ) / m : ℚ))) *
        (t : ℂ) ^ j)) (Set.Ioi 0) :=
    (integrableOn_cuspForm_vertical_pow hM hk g ((a.val : ℚ) / m) j).const_mul _
  have hsum := (integrable_finsetSum Finset.univ (fun a _ ↦ hi a)).const_mul
    (gaussSum ι m χ)⁻¹
  apply IntegrableOn.congr_fun hsum _ measurableSet_Ioi
  intro t ht
  simp only [inverseTwist, ofComplex_apply_of_im_pos (z := Complex.I * t) (by simpa using ht),
    Rat.cast_div, Rat.cast_natCast, Finset.sum_mul, mul_assoc]

end MTT

open MeasureTheory
open scoped BigOperators

namespace MTT

/-- Weighted integrability is preserved by a positive dilation. -/
lemma integrableOn_dilate_mul_pow {F : ℝ → ℂ} (j : ℕ) {d : ℝ} (hd : 0 < d)
    (hF : IntegrableOn (fun t : ℝ ↦ F t * (t : ℂ) ^ j) (Set.Ioi 0)) :
    IntegrableOn (fun t : ℝ ↦ F (d * t) * (t : ℂ) ^ j) (Set.Ioi 0) := by
  have hd0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  have hcomp : IntegrableOn (fun t : ℝ ↦ F (d * t) * ((d * t : ℝ) : ℂ) ^ j)
      (Set.Ioi 0) := by
    simpa only [mul_zero] using
      (integrableOn_Ioi_comp_mul_left_iff (fun t : ℝ ↦ F t * (t : ℂ) ^ j) 0 hd).mpr
        (by simpa only [mul_zero] using hF)
  have heq : (fun t : ℝ ↦ F (d * t) * (t : ℂ) ^ j) =
      fun t : ℝ ↦ ((d : ℂ) ^ j)⁻¹ * (F (d * t) * ((d * t : ℝ) : ℂ) ^ j) := by
    ext t
    simp only [Complex.ofReal_mul, mul_pow]
    field_simp
  rw [heq]
  exact hcomp.const_mul _

/-- Positive dilation in the polynomially weighted Mellin integral. -/
lemma integral_Ioi_dilate_mul_pow (F : ℝ → ℂ) (j : ℕ) {d : ℝ} (hd : 0 < d) :
    (∫ t in Set.Ioi (0 : ℝ), F (d * t) * (t : ℂ) ^ j) =
      (∫ t in Set.Ioi (0 : ℝ), F t * (t : ℂ) ^ j) / (d : ℂ) ^ (j + 1) := by
  have hd0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  have hfun : (fun t : ℝ ↦ F (d * t) * ((d * t : ℝ) : ℂ) ^ j) =
      fun t : ℝ ↦ (d : ℂ) ^ j * (F (d * t) * (t : ℂ) ^ j) := by
    funext t
    simp only [Complex.ofReal_mul, mul_pow]
    ring
  have h := integral_comp_mul_left_Ioi (fun t : ℝ ↦ F t * (t : ℂ) ^ j) 0 hd
  rw [hfun, integral_const_mul] at h
  simp only [mul_zero, Complex.real_smul, Complex.ofReal_inv] at h
  apply (eq_div_iff (pow_ne_zero _ hd0)).mpr
  calc
    _ = (d : ℂ) * ((d : ℂ) ^ j *
        ∫ t in Set.Ioi (0 : ℝ), F (d * t) * (t : ℂ) ^ j) := by ring
    _ = (d : ℂ) * ((d : ℂ)⁻¹ *
        ∫ t in Set.Ioi (0 : ℝ), F t * (t : ℂ) ^ j) := by rw [h]
    _ = _ := mul_inv_cancel_left₀ hd0 _

/-- Weighted inverse-twist integrability follows from a pointwise dilation identity. -/
lemma integrableOn_of_inverseTwist_dilate
    {m d : ℕ} [NeZero m] (hd : 0 < d) (ι : Qbar →+* ℂ)
    (F g : UpperHalfPlane → ℂ) (χ : DirichletCharacter Qbar m) (j : ℕ) (b : ℂ)
    (hF : ∀ z, inverseTwist ι F m χ z =
      b * inverseTwist ι g m χ (UpperHalfPlane.ofComplex ((d : ℂ) * (z : ℂ))))
    (hg : IntegrableOn (fun t : ℝ ↦
      inverseTwist ι g m χ (UpperHalfPlane.ofComplex (Complex.I * t)) * (t : ℂ) ^ j)
        (Set.Ioi 0)) :
    IntegrableOn (fun t : ℝ ↦
      inverseTwist ι F m χ (UpperHalfPlane.ofComplex (Complex.I * t)) * (t : ℂ) ^ j)
        (Set.Ioi 0) := by
  have hi := (integrableOn_dilate_mul_pow j
    (show 0 < (d : ℝ) by exact_mod_cast hd) hg).const_mul b
  apply IntegrableOn.congr_fun hi _ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [hF, mul_assoc]
  congr 4
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (z := Complex.I * (t : ℂ))
    (by simpa using ht)]
  push_cast
  ring

/-- A pointwise dilation identity for inverse twists gives the corresponding Mellin identity. -/
lemma criticalLValue_eq_mul_of_inverseTwist_dilate
    {m d : ℕ} [NeZero m] (hd : 0 < d) (ι : Qbar →+* ℂ)
    (F g : UpperHalfPlane → ℂ) (χ : DirichletCharacter Qbar m) (j : ℕ) (b : ℂ)
    (hF : ∀ z, inverseTwist ι F m χ z =
      b * inverseTwist ι g m χ (UpperHalfPlane.ofComplex ((d : ℂ) * (z : ℂ)))) :
    criticalLValue ι F m χ j =
      (b / (d : ℂ) ^ (j + 1)) * criticalLValue ι g m χ j := by
  have hpoint (t : ℝ) (ht : 0 < t) :
      inverseTwist ι F m χ (UpperHalfPlane.ofComplex (Complex.I * t)) * (t : ℂ) ^ j =
        b * (inverseTwist ι g m χ
          (UpperHalfPlane.ofComplex (Complex.I * (((d : ℝ) * t : ℝ) : ℂ))) *
            (t : ℂ) ^ j) := by
    rw [hF, mul_assoc]
    congr 4
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (z := Complex.I * (t : ℂ))
      (by simpa using ht)]
    push_cast
    ring
  unfold criticalLValue
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_const_mul]
  rw [integral_Ioi_dilate_mul_pow
    (fun t ↦ inverseTwist ι g m χ (UpperHalfPlane.ofComplex (Complex.I * t))) j
    (show 0 < (d : ℝ) by exact_mod_cast hd)]
  push_cast
  ring

end MTT

open MeasureTheory
open scoped BigOperators

namespace MTT

/-- Finite linearity of critical values when every weighted inverse twist is integrable. -/
theorem criticalLValue_sum_mul_of_integrable
    {α : Type*} [Fintype α] {m : ℕ} [NeZero m] (ι : Qbar →+* ℂ)
    (f : α → UpperHalfPlane → ℂ) (c : α → ℂ)
    (χ : DirichletCharacter Qbar m) (j : ℕ)
    (hf : ∀ i, IntegrableOn (fun t : ℝ ↦
      inverseTwist ι (f i) m χ (UpperHalfPlane.ofComplex (Complex.I * t)) * (t : ℂ) ^ j)
        (Set.Ioi 0)) :
    criticalLValue ι (fun z ↦ ∑ i, c i * f i z) m χ j =
      ∑ i, c i * criticalLValue ι (f i) m χ j := by
  simp only [criticalLValue, inverseTwist_sum_mul, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun i _ ↦ (hf i).const_mul (c i))]
  simp_rw [integral_const_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end MTT

open MeasureTheory
open scoped BigOperators

theorem solution
    {M k m : ℕ} [NeZero m] (hM : 0 < M) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (g : CuspForm (MTT.GammaOne M) (k : ℤ))
    (χ : DirichletCharacter MTT.Qbar m) (j : ℕ)
    {α : Type} [Fintype α] (d : α → ℕ) (c : α → ℂ)
    (hd : ∀ i, 0 < d i ∧ Nat.Coprime (d i) m) :
    MTT.criticalLValue ι
        (fun z ↦ ∑ i, c i * g (UpperHalfPlane.ofComplex ((d i : ℂ) * (z : ℂ)))) m χ j =
      (∑ i, c i * (ι (χ (d i)))⁻¹ / (d i : ℂ) ^ (j + 1)) *
        MTT.criticalLValue ι g m χ j := by
  have hperiod := MTT.cuspForm_periodic_comp_ofComplex hM g
  have htwist (i : α) :=
    MTT.inverseTwist_dilate_of_periodic ι g hperiod χ (d i) (hd i).1 (hd i).2
  have hg := MTT.integrableOn_inverseTwist_vertical_pow hM hk ι g χ j
  have hint (i : α) := MTT.integrableOn_of_inverseTwist_dilate (hd i).1 ι
    (fun z ↦ g (UpperHalfPlane.ofComplex ((d i : ℂ) * (z : ℂ)))) g χ j
      (ι (χ (d i)))⁻¹ (htwist i) hg
  rw [MTT.criticalLValue_sum_mul_of_integrable ι _ c χ j hint]
  simp_rw [MTT.criticalLValue_eq_mul_of_inverseTwist_dilate (hd _).1 ι _ g χ j
    (ι (χ (d _)))⁻¹ (htwist _)]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring
