-- Prove2me | solution 1 for MTT.interpolation_positive_conductor_of_moments
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T05:07:45.77279+00:00
-- url     : https://prove2.me/submissions/f225f54b-50b1-49f8-bebe-ab319a62b7b8

/-
The analytic expansion and binomial-collapse lemmas below are adapted from
allychan327's accepted Prove2Me distribution proof fb1d1260-8329-4338-b082-f7177d36d846.
The direct modular-symbol/vertical-moment identity is adapted from davidloeffler's
accepted Birch–Mellin proof c299c88e-54ce-422f-83a0-af34e766a04f.
The character-sum and Gauss-sum transformations also adapt that Birch–Mellin proof.
The new argument proves primitive-character fiber cancellation, identifies the
critical signed algebraic sum, reconstructs the measure integral, and closes
the positive-conductor interpolation theorem.
-/
import Definitions.Def_MTT_Measures
import Mathlib.NumberTheory.ModularForms.LFunction
import Mathlib.NumberTheory.ModularForms.Identities
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Ring.Periodic
import Theorems.Thm_MTT_birch_mellin_formula
import Theorems.Thm_MTT_character_integral_of_disk_moments

set_option autoImplicit false
set_option maxRecDepth 4000
noncomputable section
open scoped BigOperators ModularForm
open MeasureTheory Complex UpperHalfPlane MTT ModularForm ConjAct Pointwise

namespace MTTComparisonProof

/-- `∫_0^∞ f(r + iy) y^j dy`. -/
def verticalMoment (f : UpperHalfPlane → ℂ) (r : ℚ) (j : ℕ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), f (ofComplex ((r : ℂ) + Complex.I * t)) * (t : ℂ) ^ j

theorem rational_translate_integrable {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (f : CuspForm (GammaOne N) (k : ℤ)) (r : ℚ) (j : ℕ) :
    IntegrableOn (fun t : ℝ =>
      f (ofComplex ((r : ℂ) + Complex.I * t)) * (t : ℂ) ^ j) (Set.Ioi 0) := by
  let : NeZero N := ⟨by omega⟩
  let g : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.upperRightHom r
  let gr : GL (Fin 2) ℝ := g.map (Rat.castHom ℝ)
  have hr : gr = Matrix.GeneralLinearGroup.upperRightHom (r : ℝ) := by
    ext i l
    fin_cases i <;> fin_cases l <;> simp [gr, g]
  let : (GammaOne N).IsArithmetic := by dsimp [GammaOne]; infer_instance
  let : (toConjAct gr⁻¹ • GammaOne N).IsArithmetic := by
    have hh := Subgroup.IsArithmetic.conj (GammaOne N) g⁻¹
    simpa [gr] using hh
  let F := CuspForm.translate f gr
  have hconv := ((CuspForm.isStrongFEPair (by omega : (0 : ℤ) < k) F).hasMellin
    ((j : ℂ) + 1)).1
  unfold MellinConvergent at hconv
  have hval (t : ℝ) (ht : 0 < t) :
      F (ofComplex (Complex.I * t)) = f (ofComplex ((r : ℂ) + Complex.I * t)) := by
    change (⇑f ∣[(k : ℤ)] gr) _ = _
    rw [slash_def, hr]
    simp only [Matrix.GeneralLinearGroup.val_det_apply]
    simp [σ, denom, Matrix.GeneralLinearGroup.upperRightHom]
    congr 1
    ext
    simp [coe_smul, σ, num, denom, ofComplex_apply_of_im_pos, ht]
    ring
  apply hconv.congr_fun _ measurableSet_Ioi
  intro t ht
  simp only [ModularForm.weakFEPair, add_sub_cancel_right, Complex.cpow_natCast,
    smul_eq_mul, hval t ht]
  ring

section Expansion

variable {N k : ℕ}

theorem vm_periodic (f : CuspForm (GammaOne N) (k : ℤ)) (r : ℚ) (j : ℕ) :
    verticalMoment f (r + 1) j = verticalMoment f r j := by
  have hp := SlashInvariantFormClass.periodic_comp_ofComplex f
    (show (1 : ℝ) ∈ (GammaOne N).strictPeriods by
      simp [GammaOne, CongruenceSubgroup.strictPeriods_Gamma1])
  unfold verticalMoment
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t _
  apply congrArg (fun z : ℂ => z * (t : ℂ) ^ j)
  simpa [Function.comp_def, add_assoc, add_comm, add_left_comm] using
    hp ((r : ℂ) + Complex.I * t)

theorem modularIntegral_pow (hN : 0 < N) (hk : 2 ≤ k)
    (f : CuspForm (GammaOne N) (k : ℤ)) (r : ℚ) (t : ℕ) :
    modularIntegral f (Polynomial.X ^ t) r
      = 2 * (Real.pi : ℂ) * ∑ l ∈ Finset.range (t + 1),
          (Complex.I ^ l * (r : ℂ) ^ (t - l) * (t.choose l : ℂ)) * verticalMoment f r l := by
  set g : ℕ → ℝ → ℂ := fun l x =>
      (Complex.I ^ l * (r : ℂ) ^ (t - l) * (t.choose l : ℂ)) *
        (f (ofComplex ((r : ℂ) + Complex.I * x)) * (x : ℂ) ^ l) with hg
  have hgint : ∀ l ∈ Finset.range (t + 1), IntegrableOn (g l) (Set.Ioi 0) := by
    intro l _
    exact (rational_translate_integrable hN hk f r l).const_mul _
  have hpt : ∀ x : ℝ,
      f (ofComplex ((r : ℂ) + Complex.I * x)) *
          (Polynomial.X ^ t : Polynomial ℂ).eval ((r : ℂ) + Complex.I * x)
      = ∑ l ∈ Finset.range (t + 1), g l x := by
    intro x
    simp only [hg, Polynomial.eval_pow, Polynomial.eval_X]
    rw [add_comm ((r : ℂ)) (Complex.I * x), add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_pow]
    ring
  unfold modularIntegral
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x _ => hpt x),
    MeasureTheory.integral_finsetSum (Finset.range (t + 1)) hgint]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [hg]
  rw [MeasureTheory.integral_const_mul]
  simp only [verticalMoment]

end Expansion

section Collapse

variable {N k : ℕ}

/-- Binomial inversion: recentring the shifted moments at `a` recovers `m ^ j * V j`. -/
theorem centered_collapse {R : Type*} [CommRing R] (V : ℕ → R) (m a : R) (j : ℕ) :
    (∑ t ∈ Finset.range (j + 1), (j.choose t : R) * (-a) ^ (j - t) *
      (∑ u ∈ Finset.range (t + 1), (t.choose u : R) * m ^ u * a ^ (t - u) * V u))
      = m ^ j * V j := by
  have step1 : ∀ t ∈ Finset.range (j + 1),
      (j.choose t : R) * (-a) ^ (j - t) *
        (∑ u ∈ Finset.range (t + 1), (t.choose u : R) * m ^ u * a ^ (t - u) * V u)
      = ∑ u ∈ Finset.range (t + 1),
          ((j.choose t : R) * (t.choose u : R)) *
            ((-a) ^ (j - t) * a ^ (t - u) * m ^ u * V u) := by
    intro t _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring
  rw [Finset.sum_congr rfl step1]
  rw [Finset.sum_comm' (t' := Finset.range (j + 1)) (s' := fun u => Finset.Ico u (j + 1))
      (h := by intro x y; simp only [Finset.mem_range, Finset.mem_Ico]; omega)]
  have inner : ∀ u ∈ Finset.range (j + 1),
      (∑ t ∈ Finset.Ico u (j + 1),
        ((j.choose t : R) * (t.choose u : R)) *
          ((-a) ^ (j - t) * a ^ (t - u) * m ^ u * V u))
      = (j.choose u : R) * m ^ u * V u * (0 : R) ^ (j - u) := by
    intro u hu
    rw [Finset.mem_range] at hu
    have hu' : u ≤ j := Nat.lt_succ_iff.mp hu
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : j + 1 - u = (j - u) + 1 := by omega
    rw [hlen]
    have key : ∀ v ∈ Finset.range ((j - u) + 1),
        ((j.choose (u + v) : R) * ((u + v).choose u : R)) *
          ((-a) ^ (j - (u + v)) * a ^ ((u + v) - u) * m ^ u * V u)
        = ((j.choose u : R) * m ^ u * V u) *
            (a ^ v * (-a) ^ ((j - u) - v) * ((j - u).choose v : R)) := by
      intro v hv
      rw [Finset.mem_range] at hv
      have hv' : v ≤ j - u := Nat.lt_succ_iff.mp hv
      have hch : j.choose (u + v) * (u + v).choose u = j.choose u * (j - u).choose v := by
        have := Nat.choose_mul (n := j) (k := u + v) (s := u) (Nat.le_add_right u v)
        simpa using this
      have h1 : j - (u + v) = (j - u) - v := by omega
      have h2 : (u + v) - u = v := by omega
      rw [h1, h2]
      have hcast : ((j.choose (u + v) : R) * ((u + v).choose u : R))
          = ((j.choose u : R) * ((j - u).choose v : R)) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → R) hch
      rw [hcast]; ring
    rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
    have hbin : (∑ v ∈ Finset.range ((j - u) + 1),
        a ^ v * (-a) ^ ((j - u) - v) * ((j - u).choose v : R)) = (0 : R) ^ (j - u) := by
      rw [← add_pow]; simp
    rw [hbin]
  rw [Finset.sum_congr rfl inner, Finset.sum_eq_single j]
  · simp
  · intro u hu hne
    rw [Finset.mem_range] at hu
    have : j - u ≠ 0 := by omega
    simp [zero_pow this]
  · intro h
    exact absurd (Finset.self_mem_range_succ j) h

theorem collapse_MI (hN : 0 < N) (hk : 2 ≤ k) (f : CuspForm (GammaOne N) (k : ℤ))
    (j : ℕ) (a m : ℚ) (c : ℂ) (r : ℚ)
    (hr : ∀ t l : ℕ, l ≤ t →
      (m : ℂ) ^ t * c ^ t * ((r : ℂ) ^ (t - l) * Complex.I ^ l)
        = (-(a : ℂ)) ^ (t - l) * (c * Complex.I * (m : ℂ)) ^ l) :
    (∑ t ∈ Finset.range (j + 1),
      (j.choose t : ℂ) * (m : ℂ) ^ t * (a : ℂ) ^ (j - t) *
        (c ^ t * modularIntegral f (Polynomial.X ^ t) r))
      = 2 * (Real.pi : ℂ) * (c * Complex.I * (m : ℂ)) ^ j * verticalMoment f r j := by
  have hL : (∑ t ∈ Finset.range (j + 1),
      (j.choose t : ℂ) * (m : ℂ) ^ t * (a : ℂ) ^ (j - t) *
        (c ^ t * modularIntegral f (Polynomial.X ^ t) r))
      = 2 * (Real.pi : ℂ) * ∑ t ∈ Finset.range (j + 1),
          (j.choose t : ℂ) * (-(-(a : ℂ))) ^ (j - t) *
            (∑ l ∈ Finset.range (t + 1), (t.choose l : ℂ) *
              (c * Complex.I * (m : ℂ)) ^ l * (-(a : ℂ)) ^ (t - l) *
                verticalMoment f r l) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [modularIntegral_pow hN hk f r t]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hlt : l ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    linear_combination ((j.choose t : ℂ) * (a : ℂ) ^ (j - t) * (2 * (Real.pi : ℂ)) *
      (t.choose l : ℂ) * verticalMoment f r l) * hr t l hlt
  rw [hL, centered_collapse (fun l => verticalMoment f r l) (c * Complex.I * (m : ℂ))
    (-(a : ℂ)) j]
  ring

end Collapse

section SymbolClosed

variable {N k : ℕ} {ι : Qbar →+* ℂ}

theorem symbol_closed (hN : 0 < N) (hk : 2 ≤ k) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (s : Bool) (j : ℕ) (hj : j ≤ k - 2)
    (a m : ℚ) (hm : m ≠ 0) :
    P.omega s * ι (algebraicSymbol P s j a m)
      = (Real.pi : ℂ) * (Complex.I * (m : ℂ)) ^ j *
          (verticalMoment f.form (-a / m) j +
            (MTT.sign s : ℂ) * (-1 : ℂ) ^ j * verticalMoment f.form (a / m) j) := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hom := P.omega_ne s
  have hneg : -(-a / m : ℚ) = a / m := by field_simp
  have h1 : P.omega s * ι (algebraicSymbol P s j a m)
      = ∑ t ∈ Finset.range (j + 1), (j.choose t : ℂ) * (m : ℂ) ^ t * (a : ℂ) ^ (j - t) *
          signedIntegral f.form s t (-a / m) := by
    simp only [algebraicSymbol, map_sum, map_mul, map_pow, map_natCast, map_ratCast,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' : t ≤ k - 2 := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)) hj
    rw [P.comparison s t (-a / m) ht']
    field_simp
  have h2 : ∀ t : ℕ, signedIntegral f.form s t (-a / m)
      = (modularIntegral f.form (Polynomial.X ^ t) (-a / m)
          + (MTT.sign s : ℂ) * (-1 : ℂ) ^ t *
              modularIntegral f.form (Polynomial.X ^ t) (a / m)) / 2 := by
    intro t
    rw [signedIntegral, hneg]
  have hcol1 := collapse_MI hN hk f.form j a m 1 (-a / m) (by
    intro t l hlt
    have hml : (m : ℂ) ^ t = (m : ℂ) ^ l * (m : ℂ) ^ (t - l) := by
      rw [← pow_add]; congr 1; omega
    push_cast
    rw [div_pow, hml]
    field_simp
    ring)
  have hcol2 := collapse_MI hN hk f.form j a m (-1) (a / m) (by
    intro t l hlt
    have hml : (m : ℂ) ^ t = (m : ℂ) ^ l * (m : ℂ) ^ (t - l) := by
      rw [← pow_add]; congr 1; omega
    have hsl : (-1 : ℂ) ^ t = (-1 : ℂ) ^ l * (-1 : ℂ) ^ (t - l) := by
      rw [← pow_add]; congr 1; omega
    push_cast
    rw [div_pow, hml, hsl]
    field_simp
    ring)
  have hsum_eq : (∑ t ∈ Finset.range (j + 1), (j.choose t : ℂ) * (m : ℂ) ^ t * (a : ℂ) ^ (j - t) *
      signedIntegral f.form s t (-a / m))
      = (∑ t ∈ Finset.range (j + 1), (j.choose t : ℂ) * (m : ℂ) ^ t * (a : ℂ) ^ (j - t) *
          ((1 : ℂ) ^ t * modularIntegral f.form (Polynomial.X ^ t) (-a / m))) / 2
        + (MTT.sign s : ℂ) *
          ((∑ t ∈ Finset.range (j + 1), (j.choose t : ℂ) * (m : ℂ) ^ t * (a : ℂ) ^ (j - t) *
            (((-1) : ℂ) ^ t * modularIntegral f.form (Polynomial.X ^ t) (a / m))) / 2) := by
    rw [Finset.sum_div, Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [h2 t]
    ring
  rw [h1, hsum_eq, hcol1, hcol2]
  ring

end SymbolClosed

private lemma symbol_vertical (f : UpperHalfPlane → ℂ) (a m : ℚ) (hm : m ≠ 0) (j : ℕ) :
    modularSymbol f j a m = (2*Real.pi : ℂ) * ((m : ℂ)*Complex.I)^j *
      verticalMoment f (-a/m) j := by
  unfold modularSymbol modularIntegral verticalMoment
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have heq (t : ℝ) :
      ((((m : ℂ) • Polynomial.X + Polynomial.C (a : ℂ))^j).eval
        (((-a/m : ℚ) : ℂ) + Complex.I*t)) =
      ((m : ℂ)*Complex.I)^j * (t : ℂ)^j := by
    simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_smul,
      Polynomial.eval_X, Polynomial.eval_C, smul_eq_mul, Rat.cast_div, Rat.cast_neg]
    rw [← mul_pow]
    congr 1
    field_simp
    ring
  simp_rw [heq]
  rw [show (fun t : ℝ => f (ofComplex (((-a/m : ℚ) : ℂ) + Complex.I*t)) *
      (((m : ℂ)*Complex.I)^j * (t : ℂ)^j)) =
    (fun t : ℝ => ((m : ℂ)*Complex.I)^j *
      (f (ofComplex (((-a/m : ℚ) : ℂ) + Complex.I*t)) * (t : ℂ)^j)) by
        funext t; ring, integral_const_mul]
  ring


end MTTComparisonProof

open MTTComparisonProof in
private theorem algebraic_symbol_comparison {N k : ℕ} {ι : Qbar →+* ℂ}
    (hN : 0 < N) (hk : 2 ≤ k) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (s : Bool) (j : ℕ) (hj : j ≤ k - 2)
    (a m : ℚ) (hm : m ≠ 0) :
    2 * P.omega s * ι (algebraicSymbol P s j a m) =
      modularSymbol f.form j a m + (MTT.sign s : ℂ) * (-1 : ℂ) ^ j *
        modularSymbol f.form j (-a) m := by
  have h := symbol_closed hN hk f P s j hj a m hm
  rw [symbol_vertical f.form a m hm j, symbol_vertical f.form (-a) m hm j]
  simp only [neg_neg]
  simp only [mul_comm (m : ℂ) Complex.I]
  linear_combination 2 * h

open MTTComparisonProof
namespace MTTPositiveProof

private lemma weighted_moment_neg {N k m : ℕ} [NeZero m]
    (ι : Qbar →+* ℂ) (f : CuspForm (GammaOne N) (k : ℤ))
    (χ : DirichletCharacter Qbar m) (j : ℕ) :
    (∑ a : ZMod m, ι (χ a) * verticalMoment f (-(a.val : ℚ)/m) j) =
      ι (χ (-1)) * ∑ a : ZMod m, ι (χ a) * verticalMoment f ((a.val : ℚ)/m) j := by
  have hn (a : ZMod m) : verticalMoment f (-((-a).val : ℚ)/m) j =
      verticalMoment f ((a.val : ℚ)/m) j := by
    by_cases ha : a = 0
    · simp [ha]
    · rw [ZMod.neg_val, if_neg ha]
      have hval : a.val ≤ m := (ZMod.val_lt a).le
      push_cast [Nat.cast_sub hval]
      have hm : (m : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne m
      have he : -((m : ℚ)-a.val)/m = (a.val : ℚ)/m - 1 := by field_simp; ring
      rw [he]
      simpa using (vm_periodic f ((a.val : ℚ)/m-1) j).symm
  calc
    _ = ∑ a : ZMod m, ι (χ (-a)) * verticalMoment f (-((-a).val : ℚ)/m) j :=
      (Equiv.sum_comp (Equiv.neg (ZMod m)) _).symm
    _ = ∑ a : ZMod m, ι (χ (-1)) *
        (ι (χ a) * verticalMoment f ((a.val : ℚ)/m) j) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hn, show -a = (-1 : ZMod m)*a by ring, map_mul, map_mul]
      ring
    _ = _ := (Finset.mul_sum ..).symm

private lemma primitive_comp {m : ℕ} [NeZero m] (ι : Qbar →+* ℂ)
    (χ : DirichletCharacter Qbar m) (hχ : χ.IsPrimitive) :
    DirichletCharacter.IsPrimitive (χ.ringHomComp ι) := by
  let ψ : DirichletCharacter ℂ m := χ.ringHomComp ι
  have hc := ψ.factorsThrough_conductor
  have hh : χ.FactorsThrough ψ.conductor := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hc.dvd]
    intro u hu
    have h := (DirichletCharacter.factorsThrough_iff_ker_unitsMap hc.dvd).mp hc hu
    rw [MonoidHom.mem_ker, Units.ext_iff] at h
    change ι (χ u) = 1 at h
    rw [MonoidHom.mem_ker, Units.ext_iff]
    change χ u = 1
    apply ι.injective
    simpa using h
  change ψ.conductor = m
  apply Nat.le_antisymm (Nat.le_of_dvd (NeZero.pos m) ψ.conductor_dvd_level)
  calc
    m = χ.conductor := hχ.symm
    _ ≤ ψ.conductor := Nat.sInf_le hh

private lemma gauss_bridge {m : ℕ} [NeZero m] (ι : Qbar →+* ℂ)
    (χ : DirichletCharacter Qbar m) :
    MTT.gaussSum ι m χ = _root_.gaussSum (χ.ringHomComp ι) ZMod.stdAddChar := by
  unfold MTT.gaussSum _root_.gaussSum
  apply Finset.sum_congr rfl
  intro a _
  simp [ZMod.stdAddChar_apply, ZMod.toCircle_apply]

private lemma gauss_product {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m)
    (hχ : χ.IsPrimitive) :
    _root_.gaussSum χ ZMod.stdAddChar * _root_.gaussSum χ⁻¹ ZMod.stdAddChar =
      χ (-1) * (m : ℂ) := by
  have heq : ZMod.dft (⇑χ) = _root_.gaussSum χ ZMod.stdAddChar •
      (fun a => χ⁻¹ (-a)) := by
    ext a
    simpa [mul_comm] using hχ.fourierTransform_eq_inv_mul_gaussSum a
  have h := congrFun (ZMod.dft_dft (⇑χ)) (1 : ZMod m)
  rw [heq, map_smul, ZMod.dft_comp_neg] at h
  simp only [Pi.smul_apply, smul_eq_mul] at h
  have ht : ZMod.dft (⇑χ⁻¹) (-1) = _root_.gaussSum χ⁻¹ ZMod.stdAddChar := by
    simp [ZMod.dft_apply, _root_.gaussSum, mul_comm]
  rw [ht] at h
  simpa [mul_comm] using h


private lemma weighted_signed_comparison {N k m : ℕ} [NeZero m]
    {ι : Qbar →+* ℂ} (hN : 0 < N) (hk : 2 ≤ k) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (s : Bool) (χ : DirichletCharacter Qbar m)
    (j : ℕ) (hj : j ≤ k - 2) :
    2 * P.omega s * ι (∑ a : ZMod m, χ a * algebraicSymbol P s j a.val m) =
      (1 + (MTT.sign s : ℂ) * (-1 : ℂ)^j * ι (χ (-1))) *
        ∑ a : ZMod m, ι (χ a) * modularSymbol f.form j a.val m := by
  have hm : (m : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hc : ι (χ (-1)) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow]
    norm_num
  let W := ∑ a : ZMod m, ι (χ a) * verticalMoment f.form ((a.val : ℚ)/m) j
  have hA : P.omega s * ι (∑ a : ZMod m, χ a * algebraicSymbol P s j a.val m) =
      (Real.pi : ℂ) * (Complex.I * (m : ℂ))^j *
        ((ι (χ (-1)) + (MTT.sign s : ℂ) * (-1 : ℂ)^j) * W) := by
    calc
      _ = (Real.pi : ℂ) * (Complex.I * (m : ℂ))^j *
          ((∑ a : ZMod m, ι (χ a) * verticalMoment f.form (-(a.val : ℚ)/m) j) +
            (MTT.sign s : ℂ) * (-1 : ℂ)^j * W) := by
        simp only [map_sum,map_mul,Finset.mul_sum,W,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        have h := symbol_closed hN hk f P s j hj a.val m hm
        push_cast at h
        linear_combination ι (χ a) * h
      _ = _ := by rw [weighted_moment_neg]; dsimp [W]; ring
  have hS : (∑ a : ZMod m, ι (χ a) * modularSymbol f.form j a.val m) =
      2 * (Real.pi : ℂ) * (Complex.I * (m : ℂ))^j * (ι (χ (-1)) * W) := by
    calc
      _ = 2 * (Real.pi : ℂ) * (Complex.I * (m : ℂ))^j *
          ∑ a : ZMod m, ι (χ a) * verticalMoment f.form (-(a.val : ℚ)/m) j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [symbol_vertical f.form a.val m hm j]
        push_cast
        ring
      _ = _ := by rw [weighted_moment_neg]
  calc
    _ = 2 * (P.omega s * ι (∑ a : ZMod m, χ a * algebraicSymbol P s j a.val m)) := by ring
    _ = _ := by
      rw [hA,hS]
      linear_combination -(2 * (Real.pi : ℂ) * (Complex.I * (m : ℂ))^j *
        (MTT.sign s : ℂ) * (-1 : ℂ)^j * W) * hc


private lemma signed_sum_period {N k m : ℕ} [NeZero m]
    {ι : Qbar →+* ℂ} (hN : 0 < N) (hk : 2 ≤ k) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (χ : DirichletCharacter Qbar m)
    (j : ℕ) (hj : j ≤ k - 2) :
    ι (∑ a : ZMod m, χ a *
      (algebraicSymbol P true j a.val m + algebraicSymbol P false j a.val m)) =
      (∑ a : ZMod m, ι (χ a) * modularSymbol f.form j a.val m) /
        P.omega (criticalSign χ j) := by
  let A (s : Bool) := ∑ a : ZMod m, χ a * algebraicSymbol P s j a.val m
  let B := ∑ a : ZMod m, ι (χ a) * modularSymbol f.form j a.val m
  have hp := weighted_signed_comparison hN hk f P true χ j hj
  have hm := weighted_signed_comparison hN hk f P false χ j hj
  have heq : χ (-1) * (-1 : Qbar)^j = 1 ∨ χ (-1) * (-1 : Qbar)^j = -1 := by
    apply sq_eq_one_iff.mp
    have hx : χ (-1)^2 = 1 := by rw [← map_pow]; norm_num
    have hy : ((-1 : Qbar)^j)^2 = 1 := by rw [pow_right_comm]; norm_num
    rw [mul_pow,hx,hy,mul_one]
  have hsum : ι (∑ a : ZMod m, χ a *
      (algebraicSymbol P true j a.val m + algebraicSymbol P false j a.val m)) =
      ι (A true) + ι (A false) := by
    simp only [A,map_sum,map_mul,map_add,mul_add,Finset.sum_add_distrib]
  rw [hsum]
  rcases heq with heq | heq
  · have heC : (-1 : ℂ)^j * ι (χ (-1)) = 1 := by
      simpa only [map_mul,map_pow,map_neg,map_one,mul_comm] using congrArg ι heq
    have hp' : 2 * P.omega true * ι (A true) = 2 * B := by
      simpa [A,B,MTT.sign,mul_assoc,heC,one_add_one_eq_two] using hp
    have hm' : 2 * P.omega false * ι (A false) = 0 := by
      simpa [A,B,MTT.sign,mul_assoc,heC,one_add_one_eq_two] using hm
    have hpA : ι (A true) = B / P.omega true := by
      apply (eq_div_iff (P.omega_ne true)).mpr
      linear_combination (1/2 : ℂ) * hp'
    have hmA : ι (A false) = 0 := by
      apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (P.omega_ne false))
      simpa only [mul_zero] using hm'
    simp [hpA,hmA,criticalSign,heq,B]
  · have heC : (-1 : ℂ)^j * ι (χ (-1)) = -1 := by
      simpa only [map_mul,map_pow,map_neg,map_one,mul_comm] using congrArg ι heq
    have hp' : 2 * P.omega true * ι (A true) = 0 := by
      simpa [A,B,MTT.sign,mul_assoc,heC,one_add_one_eq_two] using hp
    have hm' : 2 * P.omega false * ι (A false) = 2 * B := by
      simpa [A,B,MTT.sign,mul_assoc,heC,one_add_one_eq_two] using hm
    have hpA : ι (A true) = 0 := by
      apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (P.omega_ne true))
      simpa only [mul_zero] using hp'
    have hmA : ι (A false) = B / P.omega false := by
      apply (eq_div_iff (P.omega_ne false)).mpr
      linear_combination (1/2 : ℂ) * hm'
    have hne : χ (-1) * (-1 : Qbar)^j ≠ 1 := by rw [heq]; norm_num
    simp [hpA,hmA,criticalSign,hne,B]

private lemma gauss_ne_zero {m : ℕ} [NeZero m] (ι : Qbar →+* ℂ)
    (χ : DirichletCharacter Qbar m) (hχ : χ.IsPrimitive) :
    MTT.gaussSum ι m χ⁻¹ ≠ 0 := by
  have hg := gauss_product (χ.ringHomComp ι) (primitive_comp ι χ hχ)
  have hc : ι (χ (-1)) ^ 2 = 1 := by rw [← map_pow,← map_pow]; norm_num
  have hcne : ι (χ (-1)) ≠ 0 := by intro h; simp [h] at hc
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  intro h
  have h' : _root_.gaussSum (χ.ringHomComp ι)⁻¹ ZMod.stdAddChar = 0 := by
    simpa [gauss_bridge,MulChar.ringHomComp_inv] using h
  rw [h',mul_zero] at hg
  exact (mul_ne_zero hcne hm) hg.symm

private lemma complex_interpolation_sum {p N k : ℕ} [Fact p.Prime]
    {ι : Qbar →+* ℂ} (hN : 0 < N) (hk : 2 ≤ k) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (n : ℕ) (χ : DirichletCharacter Qbar (p^n))
    (hχ : χ.IsPrimitive) (j : ℕ) (hj : j ≤ k - 2) :
    ι (∑ a : ZMod (p^n), χ a *
      (algebraicSymbol P true j a.val (p^n) + algebraicSymbol P false j a.val (p^n))) =
      normalizedCriticalValue f P.omega n χ j := by
  simp only [← Nat.cast_pow]
  rw [signed_sum_period hN hk f P χ j hj,normalizedCriticalValue,
    MTT.birch_mellin_formula hN hk ι f χ hχ j hj]
  have hm : ((p^n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne (p^n))
  have hfac : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hg := gauss_ne_zero ι χ hχ
  field_simp

private theorem primitive_character_fiber_cancellation {R : Type*} [Field R] {m d : ℕ} [NeZero m]
    (hd : d ∣ m) (hdm : d < m) (χ : DirichletCharacter R m)
    (hχ : χ.IsPrimitive) (F : (ZMod d)ˣ → R) :
    (∑ a : (ZMod m)ˣ, χ a * F (ZMod.unitsMap hd a)) = 0 := by
  classical
  have hnf : ¬ χ.FactorsThrough d := by
    intro hf
    have hle : χ.conductor ≤ d := Nat.sInf_le hf
    rw [hχ] at hle
    omega
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd] at hnf
  change ¬ (∀ u, ZMod.unitsMap hd u = 1 → χ.toUnitHom u = 1) at hnf
  push Not at hnf
  obtain ⟨u,hu,hcu⟩ := hnf
  have hcu' : χ u ≠ 1 := by
    intro h
    apply hcu
    apply Units.ext
    exact h
  apply eq_zero_of_mul_eq_self_left hcu'
  calc
    _ = ∑ a : (ZMod m)ˣ, χ (u * a) * F (ZMod.unitsMap hd (u * a)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      simp only [map_mul,hu,one_mul]
      ring
    _ = _ := by
      simpa only [Equiv.coe_mulLeft, Units.val_mul] using Equiv.sum_comp (Equiv.mulLeft u)
        (fun a : (ZMod m)ˣ => χ a * F (ZMod.unitsMap hd a))


private lemma algebraic_symbol_periodic {N k : ℕ} {ι : Qbar →+* ℂ}
    (hN : 0 < N) (hk : 2 ≤ k) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (s : Bool) (j : ℕ) (hj : j ≤ k - 2)
    (m : ℚ) (hm : m ≠ 0) :
    Function.Periodic (fun a : ℚ => algebraicSymbol P s j a m) m := by
  have hv : Function.Periodic (fun r : ℚ => verticalMoment f.form r j) 1 :=
    fun r => vm_periodic f.form r j
  intro a
  apply ι.injective
  apply mul_left_cancel₀ (P.omega_ne s)
  rw [symbol_closed hN hk f P s j hj _ m hm,symbol_closed hN hk f P s j hj _ m hm]
  have e1 : -(a+m)/m = -a/m-1 := by field_simp; ring
  have e2 : (a+m)/m = a/m+1 := by field_simp
  rw [e1,e2,hv.sub_eq,vm_periodic]

private lemma periodic_rat_congr_int {B : Type*} {m : ℕ} (F : ℚ → B)
    (hF : Function.Periodic F (m : ℚ)) {a b : ℤ}
    (h : (a : ZMod m) = (b : ZMod m)) : F (a : ℚ) = F (b : ℚ) := by
  obtain ⟨c,hc⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub a b m).mp h
  have hcQ : (b : ℚ) = (a : ℚ) + (c : ℚ) * (m : ℚ) := by
    have hcast : (b : ℚ) - (a : ℚ) = (m : ℚ) * (c : ℚ) := by exact_mod_cast hc
    linear_combination hcast
  rw [hcQ]
  exact (hF.int_mul c (a : ℚ)).symm

private lemma sum_units_eq_sum {R : Type*} [Field R] {m : ℕ} [NeZero m]
    (χ : DirichletCharacter R m) (F : ZMod m → R) :
    (∑ a : (ZMod m)ˣ, χ a * F a) = ∑ a : ZMod m, χ a * F a := by
  classical
  apply Fintype.sum_of_injective Units.val Units.val_injective
  · intro a ha
    have hnu : ¬ IsUnit a := by
      intro hu
      exact ha ⟨hu.unit,hu.unit_spec⟩
    rw [χ.map_nonunit hnu,zero_mul]
  · intro a
    rfl

private lemma correction_sum_zero {p N k : ℕ} [Fact p.Prime]
    {ι : Qbar →+* ℂ} (hN : 0 < N) (hk : 2 ≤ k) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (s : Bool) (n : ℕ) (hn : 0 < n)
    (χ : DirichletCharacter Qbar (p^n)) (hχ : χ.IsPrimitive)
    (j : ℕ) (hj : j ≤ k - 2) :
    (∑ a : (ZMod (p^n))ˣ, χ a *
      algebraicSymbol P s j (a : ZMod (p^n)).val ((p^(n-1) : ℕ) : ℚ)) = 0 := by
  let d := p^(n-1)
  have hd : d ∣ p^n := pow_dvd_pow p (Nat.sub_le n 1)
  have hdm : d < p^n := pow_lt_pow_right₀ (Fact.out : p.Prime).one_lt (by omega)
  let F : (ZMod d)ˣ → Qbar := fun a => algebraicSymbol P s j (a : ZMod d).val d
  have hdp : (d : ℚ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  have hper := algebraic_symbol_periodic hN hk f P s j hj (d : ℚ) hdp
  have heq (a : (ZMod (p^n))ˣ) :
      algebraicSymbol P s j (a : ZMod (p^n)).val (d : ℚ) = F (ZMod.unitsMap hd a) := by
    have hval : (((a : ZMod (p^n)).val : ℤ) : ZMod d) =
        ((((ZMod.unitsMap hd a : (ZMod d)ˣ) : ZMod d).val : ℤ) : ZMod d) := by
      push_cast
      rw [ZMod.natCast_zmod_val,ZMod.unitsMap_val,ZMod.natCast_val]
    exact periodic_rat_congr_int (fun a => algebraicSymbol P s j a (d : ℚ)) hper hval
  rw [show (∑ a : (ZMod (p^n))ˣ, χ a *
      algebraicSymbol P s j (a : ZMod (p^n)).val (d : ℚ)) =
      ∑ a : (ZMod (p^n))ˣ, χ a * F (ZMod.unitsMap hd a) from
        Finset.sum_congr rfl (fun a _ => congrArg (fun z => χ a * z) (heq a))]
  exact primitive_character_fiber_cancellation hd hdm χ hχ F

private lemma character_disk_sum {p N k : ℕ} [Fact p.Prime]
    {ι : Qbar →+* ℂ} (hN : 0 < N) (hk : 2 ≤ k)
    (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (α : ℂ_[p]) (s : Bool)
    (n : ℕ) (hn : 0 < n) (χ : DirichletCharacter Qbar (p^n))
    (hχ : χ.IsPrimitive) (j : ℕ) (hj : j ≤ k - 2) :
    (∑ a : (ZMod (p^n))ˣ, ιp (χ a) *
      diskMoment f ιp P α s j n ((a : ZMod (p^n)).val : ℤ)) =
    (α^n)⁻¹ * ιp (∑ a : (ZMod (p^n))ˣ, χ a *
      algebraicSymbol P s j (a : ZMod (p^n)).val (p^n)) := by
  classical
  have hc := correction_sum_zero hN hk f P s n hn χ hχ j hj
  have hc' : (∑ a : (ZMod (p^n))ˣ, ιp (χ a) *
      ιp (algebraicSymbol P s j (a : ZMod (p^n)).val (p^(n-1)))) = 0 := by
    simpa only [map_sum,map_mul,map_zero,Nat.cast_pow] using congrArg ιp hc
  simp only [diskMoment,Int.cast_natCast,map_sum,map_mul,Finset.mul_sum]
  calc
    _ = (∑ a : (ZMod (p^n))ˣ, (α^n)⁻¹ * (ιp (χ a) *
          ιp (algebraicSymbol P s j (a : ZMod (p^n)).val (p^n)))) -
        (ιp (f.epsilon p) * (p : ℂ_[p])^(k-2) / α^(n+1)) *
          (∑ a : (ZMod (p^n))ˣ, ιp (χ a) *
            ιp (algebraicSymbol P s j (a : ZMod (p^n)).val (p^(n-1)))) := by
      rw [Finset.mul_sum,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by rw [hc',mul_zero,sub_zero]

private lemma euler_positive {p N k : ℕ} [Fact p.Prime]
    {ι : Qbar →+* ℂ} (f : Eigenform N k ι) (ιp : Qbar →+* ℂ_[p])
    (α : ℂ_[p]) (n : ℕ) (hn : 0 < n)
    (χ : DirichletCharacter Qbar (p^n)) (j : ℕ) :
    eulerMultiplier f ιp α n χ j = (α^n)⁻¹ := by
  have hpnu : ¬ IsUnit (p : ZMod (p^n)) := by
    rw [ZMod.isUnit_iff_coprime,Nat.coprime_pow_right_iff hn]
    simpa using (Fact.out : p.Prime).ne_one
  simp [eulerMultiplier,χ.map_nonunit hpnu,(χ⁻¹).map_nonunit hpnu]

end MTTPositiveProof

open MTTPositiveProof in
theorem solution {p N k : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (α : ℂ_[p]) (_hα : IsOrdinaryRoot f ιp α)
    (μ : Bool → UnitMeasure p)
    (hμ : ∀ s, RealizesMoments f ιp P α s (μ s))
    (n : ℕ) (hn : 0 < n) (χ : DirichletCharacter Qbar (p ^ n))
    (hχ : χ.IsPrimitive) (j : ℕ) (hj : j ≤ k - 2) :
    ∃ (g : C((ℤ_[p])ˣ, ℂ_[p])) (v : Qbar),
      (∀ x, g x = specialFunction ιp n χ j x) ∧
      ι v = normalizedCriticalValue f P.omega n χ j ∧
      (μ true + μ false) g = eulerMultiplier f ιp α n χ j * ιp v := by
  classical
  let V (s : Bool) := ∑ a : (ZMod (p^n))ˣ, χ a *
    algebraicSymbol P s j (a : ZMod (p^n)).val (p^n)
  let v := V true + V false
  obtain ⟨g,hg,hgt⟩ := MTT.character_integral_of_disk_moments ιp f P α true
    (μ true) (hμ true) n hn χ j hj
  obtain ⟨g',hg',hgf⟩ := MTT.character_integral_of_disk_moments ιp f P α false
    (μ false) (hμ false) n hn χ j hj
  have hgg : g' = g := ContinuousMap.ext (fun x => (hg' x).trans (hg x).symm)
  subst g'
  refine ⟨g,v,hg,?_,?_⟩
  · have hv : v = ∑ a : ZMod (p^n), χ a *
        (algebraicSymbol P true j a.val (p^n) +
          algebraicSymbol P false j a.val (p^n)) := by
      dsimp [v,V]
      rw [← Finset.sum_add_distrib]
      simp_rw [← mul_add]
      exact sum_units_eq_sum χ (fun a =>
        algebraicSymbol P true j a.val (p^n) + algebraicSymbol P false j a.val (p^n))
    rw [hv]
    exact complex_interpolation_sum hN hk f P n χ hχ j hj
  · change μ true g + μ false g = _
    rw [hgt,hgf,character_disk_sum hN hk ιp f P α true n hn χ hχ j hj,
      character_disk_sum hN hk ιp f P α false n hn χ hχ j hj,
      euler_positive f ιp α n hn χ j]
    simp only [v,map_add,V,mul_add]
