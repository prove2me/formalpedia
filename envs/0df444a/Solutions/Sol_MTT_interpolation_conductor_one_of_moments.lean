-- Prove2me | solution 1 for MTT.interpolation_conductor_one_of_moments
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T05:19:53.830304+00:00
-- url     : https://prove2.me/submissions/924bbc6d-c963-4c73-83e1-fb6581276a08

/-
The analytic expansion and binomial-collapse lemmas below are adapted from
allychan327's accepted Prove2Me distribution proof fb1d1260-8329-4338-b082-f7177d36d846.
The direct modular-symbol/vertical-moment identity is adapted from davidloeffler's
accepted Birch–Mellin proof c299c88e-54ce-422f-83a0-af34e766a04f.
The character-sum and Gauss-sum transformations also adapt that Birch–Mellin proof.
The new argument proves the conductor-one interpolation theorem. The depth-one
Hecke sum excludes the zero residue, and the ordinary-root equation supplies
both Euler factors. The Hecke moment calculation and reflection of its residue
sum are also adapted from the credited distribution proof.
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

open MTTComparisonProof
namespace MTTConductorOneProof

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

section Scaling

variable (f : UpperHalfPlane → ℂ)

theorem vm_shrink_pt (r : ℚ) (j : ℕ) {c : ℕ} (hc : 0 < c) (u : ℝ) :
    f (ofComplex (((r : ℂ) + Complex.I * u) / (c : ℂ))) * (u : ℂ) ^ j
      = (c : ℂ) ^ j *
          (f (ofComplex (((r / c : ℚ) : ℂ) + Complex.I * (((c : ℝ)⁻¹ * u : ℝ) : ℂ))) *
            (((c : ℝ)⁻¹ * u : ℝ) : ℂ) ^ j) := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have harg : ((r : ℂ) + Complex.I * u) / (c : ℂ)
      = ((r / c : ℚ) : ℂ) + Complex.I * (((c : ℝ)⁻¹ * u : ℝ) : ℂ) := by
    push_cast; field_simp
  have hsc : ((u : ℝ) : ℂ) ^ j
      = (c : ℂ) ^ j * (((c : ℝ)⁻¹ * u : ℝ) : ℂ) ^ j := by
    push_cast
    rw [mul_pow, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hcC, one_pow, one_mul]
  rw [harg, hsc]; ring

theorem vm_stretch_pt (r : ℚ) (j : ℕ) {c : ℕ} (hc : 0 < c) (u : ℝ) :
    f (ofComplex ((c : ℂ) * ((r : ℂ) + Complex.I * u))) * (u : ℂ) ^ j
      = ((c : ℂ) ^ j)⁻¹ *
          (f (ofComplex (((c * r : ℚ) : ℂ) + Complex.I * (((c : ℝ) * u : ℝ) : ℂ))) *
            (((c : ℝ) * u : ℝ) : ℂ) ^ j) := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have harg : (c : ℂ) * ((r : ℂ) + Complex.I * u)
      = ((c * r : ℚ) : ℂ) + Complex.I * (((c : ℝ) * u : ℝ) : ℂ) := by push_cast; ring
  have hsc : ((u : ℝ) : ℂ) ^ j
      = ((c : ℂ) ^ j)⁻¹ * (((c : ℝ) * u : ℝ) : ℂ) ^ j := by
    push_cast
    rw [mul_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero j hcC), one_mul]
  rw [harg, hsc]; ring

theorem vm_shrink (r : ℚ) (j : ℕ) {c : ℕ} (hc : 0 < c) :
    (c : ℂ) ^ (j + 1) * verticalMoment f (r / c) j
      = ∫ u in Set.Ioi (0 : ℝ),
          f (ofComplex (((r : ℂ) + Complex.I * u) / (c : ℂ))) * (u : ℂ) ^ j := by
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  simp only [vm_shrink_pt f r j hc]
  rw [MeasureTheory.integral_const_mul,
    integral_comp_mul_left_Ioi
      (fun y : ℝ => f (ofComplex (((r / c : ℚ) : ℂ) + Complex.I * y)) * (y : ℂ) ^ j) 0
      (inv_pos.mpr hcR)]
  simp only [mul_zero, inv_inv]
  rw [Complex.real_smul]
  simp only [verticalMoment]
  push_cast
  ring

theorem vm_stretch (r : ℚ) (j : ℕ) {c : ℕ} (hc : 0 < c) :
    (c : ℂ) ^ (j + 1) *
        (∫ u in Set.Ioi (0 : ℝ),
          f (ofComplex ((c : ℂ) * ((r : ℂ) + Complex.I * u))) * (u : ℂ) ^ j)
      = verticalMoment f (c * r) j := by
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  simp only [vm_stretch_pt f r j hc]
  rw [MeasureTheory.integral_const_mul,
    integral_comp_mul_left_Ioi
      (fun y : ℝ => f (ofComplex (((c * r : ℚ) : ℂ) + Complex.I * y)) * (y : ℂ) ^ j) 0 hcR]
  simp only [mul_zero]
  rw [Complex.real_smul]
  simp only [verticalMoment]
  push_cast
  field_simp
  ring

end Scaling

section Integrability

variable {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (f : CuspForm (GammaOne N) (k : ℤ))

include hN hk in
theorem vm_shrink_integrable (r : ℚ) (j : ℕ) {c : ℕ} (hc : 0 < c) :
    IntegrableOn (fun u : ℝ =>
      f (ofComplex (((r : ℂ) + Complex.I * u) / (c : ℂ))) * (u : ℂ) ^ j) (Set.Ioi 0) := by
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hbase := rational_translate_integrable hN hk f (r / c) j
  have hcomp : IntegrableOn (fun u : ℝ =>
      f (ofComplex (((r / c : ℚ) : ℂ) + Complex.I * (((c : ℝ)⁻¹ * u : ℝ) : ℂ))) *
        (((c : ℝ)⁻¹ * u : ℝ) : ℂ) ^ j) (Set.Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff
      (fun y : ℝ => f (ofComplex (((r / c : ℚ) : ℂ) + Complex.I * y)) * (y : ℂ) ^ j) 0
      (inv_pos.mpr hcR)).2 (by simpa using hbase)
    exact this
  show Integrable _ (volume.restrict (Set.Ioi 0))
  simpa only [← vm_shrink_pt f r j hc] using hcomp.const_mul ((c : ℂ) ^ j)

include hN hk in
theorem vm_stretch_integrable (r : ℚ) (j : ℕ) {c : ℕ} (hc : 0 < c) :
    IntegrableOn (fun u : ℝ =>
      f (ofComplex ((c : ℂ) * ((r : ℂ) + Complex.I * u))) * (u : ℂ) ^ j) (Set.Ioi 0) := by
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hbase := rational_translate_integrable hN hk f (c * r) j
  have hcomp : IntegrableOn (fun u : ℝ =>
      f (ofComplex (((c * r : ℚ) : ℂ) + Complex.I * (((c : ℝ) * u : ℝ) : ℂ))) *
        (((c : ℝ) * u : ℝ) : ℂ) ^ j) (Set.Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff
      (fun y : ℝ => f (ofComplex (((c * r : ℚ) : ℂ) + Complex.I * y)) * (y : ℂ) ^ j) 0
      hcR).2 (by simpa using hbase)
    exact this
  show Integrable _ (volume.restrict (Set.Ioi 0))
  simpa only [← vm_stretch_pt f r j hc] using hcomp.const_mul (((c : ℂ) ^ j)⁻¹)

end Integrability

section Hecke

variable {N k : ℕ} {ι : Qbar →+* ℂ}

theorem hecke_pointwise (_hN : 0 < N) (hk : 2 ≤ k) (f : Eigenform N k ι)
    {p : ℕ} (hp : p.Prime) (j : ℕ) (r : ℚ) {u : ℝ} (hu : 0 < u) :
    (∑ b ∈ Finset.range p,
        f.form (ofComplex (((r : ℂ) + (b : ℂ) + Complex.I * u) / (p : ℂ))) * (u : ℂ) ^ j)
      = (p : ℂ) * ι (f.coeff p) *
          (f.form (ofComplex ((r : ℂ) + Complex.I * u)) * (u : ℂ) ^ j)
        - (p : ℂ) ^ k * ι (f.epsilon (p : ZMod N)) *
          (f.form (ofComplex ((p : ℂ) * ((r : ℂ) + Complex.I * u))) * (u : ℂ) ^ j) := by
  have hp0 : 0 < p := hp.pos
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have him : 0 < ((r : ℂ) + Complex.I * u).im := by simpa using hu
  set z : UpperHalfPlane := ofComplex ((r : ℂ) + Complex.I * u) with hzdef
  have hz : (z : ℂ) = (r : ℂ) + Complex.I * u := by
    rw [hzdef, ofComplex_apply_of_im_pos him]
  have hpk : (p : ℂ) * (p : ℂ) ^ (k - 1) = (p : ℂ) ^ k := by
    rw [← pow_succ']
    congr 1
    omega
  have heig := f.eigen p hp z
  rw [heckePrime] at heig
  have heig' := congrArg (fun x : ℂ => (p : ℂ) * x) heig
  simp only [mul_add] at heig'
  rw [← mul_assoc, mul_inv_cancel₀ hpC, one_mul] at heig'
  have hkey : (∑ b : Fin p, f.form (ofComplex (((z : ℂ) + (b.val : ℂ)) / (p : ℂ))))
      = (p : ℂ) * ι (f.coeff p) * f.form z
        - (p : ℂ) ^ k * ι (f.epsilon (p : ZMod N)) *
            f.form (ofComplex ((p : ℂ) * (z : ℂ))) := by
    linear_combination heig' -
      ι (f.epsilon (p : ZMod N)) * f.form (ofComplex ((p : ℂ) * (z : ℂ))) * hpk
  have harg : ∀ b : Fin p,
      f.form (ofComplex (((r : ℂ) + (b.val : ℂ) + Complex.I * u) / (p : ℂ)))
        = f.form (ofComplex (((z : ℂ) + (b.val : ℂ)) / (p : ℂ))) := by
    intro b
    rw [hz]
    ring_nf
  have hsum : (∑ b : Fin p,
      f.form (ofComplex (((r : ℂ) + (b.val : ℂ) + Complex.I * u) / (p : ℂ))))
      = (p : ℂ) * ι (f.coeff p) * f.form z
        - (p : ℂ) ^ k * ι (f.epsilon (p : ZMod N)) *
            f.form (ofComplex ((p : ℂ) * (z : ℂ))) := by
    rw [← hkey]
    exact Finset.sum_congr rfl fun b _ => harg b
  rw [← Fin.sum_univ_eq_sum_range
      (fun b : ℕ =>
        f.form (ofComplex (((r : ℂ) + (b : ℂ) + Complex.I * u) / (p : ℂ))) * (u : ℂ) ^ j) p,
    ← Finset.sum_mul, hsum, hz]
  ring

theorem hecke_vm (hN : 0 < N) (hk : 2 ≤ k) (f : Eigenform N k ι)
    {p : ℕ} (hp : p.Prime) (j : ℕ) (hjk : j + 1 ≤ k) (r : ℚ) :
    (p : ℂ) ^ (j + 1) * ∑ b ∈ Finset.range p, verticalMoment f.form ((r + b) / p) j
      = (p : ℂ) * ι (f.coeff p) * verticalMoment f.form r j
        - (p : ℂ) ^ (k - j - 1) * ι (f.epsilon (p : ZMod N)) *
            verticalMoment f.form ((p : ℚ) * r) j := by
  have hp0 : 0 < p := hp.pos
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hcast : ∀ b : ℕ, ((r + (b : ℚ) : ℚ) : ℂ) = (r : ℂ) + (b : ℂ) := by
    intro b; push_cast; ring
  have hshr : ∀ b : ℕ, (p : ℂ) ^ (j + 1) * verticalMoment f.form ((r + b) / p) j
      = ∫ u in Set.Ioi (0 : ℝ),
          f.form (ofComplex (((r : ℂ) + (b : ℂ) + Complex.I * u) / (p : ℂ))) * (u : ℂ) ^ j := by
    intro b
    rw [vm_shrink f.form (r + b) j hp0]
    simp only [hcast b]
  have hint : ∀ b ∈ Finset.range p, IntegrableOn (fun u : ℝ =>
      f.form (ofComplex (((r : ℂ) + (b : ℂ) + Complex.I * u) / (p : ℂ))) * (u : ℂ) ^ j)
      (Set.Ioi 0) := by
    intro b _
    have := vm_shrink_integrable hN hk f.form (r + b) j hp0
    simpa only [hcast b] using this
  have hA := rational_translate_integrable hN hk f.form r j
  have hB := vm_stretch_integrable hN hk f.form r j hp0
  rw [Finset.mul_sum, Finset.sum_congr rfl (fun b hb => hshr b),
    ← MeasureTheory.integral_finsetSum _ hint,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun u hu => hecke_pointwise hN hk f hp j r hu),
    MeasureTheory.integral_sub (hA.const_mul _) (hB.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hexp : (p : ℂ) ^ k = (p : ℂ) ^ (k - j - 1) * (p : ℂ) ^ (j + 1) := by
    rw [← pow_add]; congr 1; omega
  have hst := vm_stretch f.form r j hp0
  simp only [verticalMoment] at hst ⊢
  rw [hexp]
  linear_combination (-((p : ℂ) ^ (k - j - 1)) * ι (f.epsilon (p : ZMod N))) * hst

end Hecke


variable {N k : ℕ}

theorem sum_reflect (f : CuspForm (GammaOne N) (k : ℤ)) (j : ℕ) {p : ℕ} (hp : 0 < p) (r : ℚ) :
    (∑ b ∈ Finset.range p, verticalMoment f ((r - b) / p) j)
      = ∑ b ∈ Finset.range p, verticalMoment f ((r + b) / p) j := by
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  refine Finset.sum_nbij' (i := fun b => (p - b) % p) (j := fun b => (p - b) % p)
    (fun a _ => Finset.mem_range.mpr (Nat.mod_lt _ hp))
    (fun a _ => Finset.mem_range.mpr (Nat.mod_lt _ hp)) ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_range] at ha
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h; simp
    · have h1 : (p - a) % p = p - a := Nat.mod_eq_of_lt (by omega)
      have h2 : p - (p - a) = a := by omega
      rw [h1, h2, Nat.mod_eq_of_lt ha]
  · intro a ha
    rw [Finset.mem_range] at ha
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h; simp
    · have h1 : (p - a) % p = p - a := Nat.mod_eq_of_lt (by omega)
      have h2 : p - (p - a) = a := by omega
      rw [h1, h2, Nat.mod_eq_of_lt ha]
  · intro a ha
    rw [Finset.mem_range] at ha
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h; simp
    · have hle : a ≤ p := by omega
      have h1 : (p - a) % p = p - a := Nat.mod_eq_of_lt (by omega)
      have hc : (((p - a : ℕ)) : ℚ) = (p : ℚ) - (a : ℚ) := by
        rw [Nat.cast_sub hle]
      have hshift : (r + (((p - a : ℕ)) : ℚ)) / p = (r - (a : ℚ)) / p + 1 := by
        rw [hc]; field_simp; ring
      rw [h1, hshift]
      exact (vm_periodic f ((r - (a : ℚ)) / p) j).symm


private lemma symbol_boundary_sum {p N k : ℕ} [Fact p.Prime]
    {ι : Qbar →+* ℂ} (hN : 0 < N) (hk : 2 ≤ k) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (s : Bool) (j : ℕ) (hj : j ≤ k - 2) :
    (∑ b ∈ Finset.range p, algebraicSymbol P s j b p) =
      (f.coeff p - f.epsilon p * (p : Qbar)^(k-2-j)) *
        algebraicSymbol P s j 0 1 := by
  have hp : p.Prime := Fact.out
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  let W := ∑ b ∈ Finset.range p, verticalMoment f.form ((b : ℚ)/p) j
  let V := verticalMoment f.form 0 j
  let u := (MTT.sign s : ℂ) * (-1 : ℂ)^j
  have hr : (∑ b ∈ Finset.range p, verticalMoment f.form (-(b : ℚ)/p) j) = W := by
    simpa only [zero_sub,zero_add,W] using sum_reflect f.form j hp.pos 0
  have hs : P.omega s * ι (∑ b ∈ Finset.range p, algebraicSymbol P s j b p) =
      (Real.pi : ℂ) * Complex.I^j * (p : ℂ)^j * (1+u) * W := by
    rw [map_sum,Finset.mul_sum]
    simp_rw [symbol_closed hN hk f P s j hj _ p hpQ]
    push_cast
    simp only [mul_pow]
    rw [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.mul_sum,hr]
    dsimp [u,W]
    ring
  have h0 : P.omega s * ι (algebraicSymbol P s j 0 1) =
      (Real.pi : ℂ) * Complex.I^j * (1+u) * V := by
    rw [symbol_closed hN hk f P s j hj 0 1 (by norm_num)]
    simp only [Rat.cast_one,mul_one,neg_zero,zero_div]
    dsimp [u,V]
    ring
  have hH : (p : ℂ)^(j+1)*W =
      (p : ℂ)*ι (f.coeff p)*V - (p : ℂ)^(k-j-1)*ι (f.epsilon p)*V := by
    simpa only [zero_add,mul_zero,W,V] using hecke_vm hN hk f hp j (by omega) 0
  have hpow : (p : ℂ)^(k-j-1) = (p : ℂ)^(k-2-j) * p := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpow,pow_succ] at hH
  apply ι.injective
  apply mul_left_cancel₀ (P.omega_ne s)
  simp only [map_mul,map_sub,map_pow,map_natCast]
  calc
    _ = (Real.pi : ℂ)*Complex.I^j*(p : ℂ)^j*(1+u)*W := hs
    _ = (ι (f.coeff p) - ι (f.epsilon p)*(p : ℂ)^(k-2-j)) *
        ((Real.pi : ℂ)*Complex.I^j*(1+u)*V) := by
      apply mul_left_cancel₀ hpC
      linear_combination ((Real.pi : ℂ)*Complex.I^j*(1+u)) * hH
    _ = _ := by rw [← h0]; ring

private lemma symbol_zero_scale {N k : ℕ} {ι : Qbar →+* ℂ}
    (hN : 0 < N) (hk : 2 ≤ k) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (s : Bool) (j : ℕ) (hj : j ≤ k - 2)
    (m : ℚ) (hm : m ≠ 0) :
    algebraicSymbol P s j 0 m = (m : Qbar)^j * algebraicSymbol P s j 0 1 := by
  apply ι.injective
  apply mul_left_cancel₀ (P.omega_ne s)
  simp only [map_mul,map_pow,map_ratCast]
  rw [mul_left_comm (P.omega s),symbol_closed hN hk f P s j hj 0 1 (by norm_num),
    symbol_closed hN hk f P s j hj 0 m hm]
  simp only [Rat.cast_one,mul_one,neg_zero,zero_div,mul_pow]
  ring

private lemma symbol_integral_one {N k : ℕ} {ι : Qbar →+* ℂ}
    (hN : 0 < N) (hk : 2 ≤ k) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (s : Bool) (j : ℕ) (hj : j ≤ k - 2) (a : ℕ) :
    algebraicSymbol P s j a 1 = algebraicSymbol P s j 0 1 := by
  have hper := algebraic_symbol_periodic hN hk f P s j hj 1 (by norm_num)
  simpa using hper.nat_mul a 0

private lemma sum_units_add_zero {p : ℕ} [Fact p.Prime] (F : ZMod p → Qbar) :
    (∑ a : (ZMod p)ˣ, F a) + F 0 = ∑ a : ZMod p, F a := by
  classical
  have h := Fintype.sum_subtype_add_sum_subtype (fun a : ZMod p => a ≠ 0) F
  have he : (∑ a : (ZMod p)ˣ, F a) = ∑ a : {a : ZMod p // a ≠ 0}, F a := by
    exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun a => rfl)
  let : Unique {a : ZMod p // ¬ a ≠ 0} :=
    ⟨⟨0,by simp⟩,fun a => Subtype.ext (not_not.mp a.property)⟩
  have hz : ((default : {a : ZMod p // ¬ a ≠ 0}) : ZMod p) = 0 :=
    not_not.mp (default : {a : ZMod p // ¬ a ≠ 0}).property
  rw [he]
  simpa only [Fintype.sum_unique,hz] using h

private lemma sum_zmod_eq_range {p : ℕ} [NeZero p] (F : ℕ → Qbar) :
    (∑ a : ZMod p, F a.val) = ∑ a ∈ Finset.range p, F a := by
  rw [← Fin.sum_univ_eq_sum_range]
  symm
  apply Fintype.sum_equiv (ZMod.finEquiv p).toEquiv
  intro a
  congr 1
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

private lemma symbol_unit_boundary_sum {p N k : ℕ} [Fact p.Prime]
    {ι : Qbar →+* ℂ} (hN : 0 < N) (hk : 2 ≤ k) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (s : Bool) (j : ℕ) (hj : j ≤ k - 2) :
    (∑ a : (ZMod p)ˣ, algebraicSymbol P s j (a : ZMod p).val p) =
      (f.coeff p - f.epsilon p * (p : Qbar)^(k-2-j) - (p : Qbar)^j) *
        algebraicSymbol P s j 0 1 := by
  have h := sum_units_add_zero (fun a : ZMod p => algebraicSymbol P s j a.val p)
  rw [sum_zmod_eq_range (fun a => algebraicSymbol P s j a p),
    symbol_boundary_sum hN hk f P s j hj] at h
  simp only [ZMod.val_zero,Nat.cast_zero] at h
  rw [symbol_zero_scale hN hk f P s j hj p (by exact_mod_cast (Fact.out : p.Prime).ne_zero)] at h
  push_cast at h
  linear_combination h

private lemma conductor_one_character_value {p : ℕ}
    (χ : DirichletCharacter Qbar (p^0)) (a : ZMod (p^0)) : χ a = 1 := by
  let : Subsingleton (ZMod (p^0)) := by rw [pow_zero]; infer_instance
  rw [Subsingleton.elim a 1,map_one]

private lemma disk_sum_one {p N k : ℕ} [Fact p.Prime]
    {ι : Qbar →+* ℂ} (hN : 0 < N) (hk : 2 ≤ k)
    (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (α : ℂ_[p]) (hα : IsOrdinaryRoot f ιp α)
    (s : Bool) (χ : DirichletCharacter Qbar (p^0))
    (j : ℕ) (hj : j ≤ k - 2) :
    (∑ a : (ZMod p)ˣ, diskMoment f ιp P α s j 1 ((a : ZMod p).val : ℤ)) =
      eulerMultiplier f ιp α 0 χ j * ιp (algebraicSymbol P s j 0 1) := by
  classical
  have hα0 : α ≠ 0 := by
    intro he
    have H := hα.1
    simp [he] at H
  have ha := congrArg ιp (symbol_unit_boundary_sum (p := p) hN hk f P s j hj)
  simp only [map_sum,map_mul,map_sub,map_pow,map_natCast] at ha
  have hc : (∑ a : (ZMod p)ˣ, ιp (algebraicSymbol P s j (a : ZMod p).val 1)) =
      ((p : ℂ_[p])-1) * ιp (algebraicSymbol P s j 0 1) := by
    simp_rw [symbol_integral_one hN hk f P s j hj]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_units,ZMod.card]
    rw [Nat.cast_sub (Fact.out : p.Prime).one_le,Nat.cast_one]
  have hsum : (∑ a : (ZMod p)ˣ, diskMoment f ιp P α s j 1 ((a : ZMod p).val : ℤ)) =
      (α⁻¹ * (ιp (f.coeff p) - ιp (f.epsilon p)*(p : ℂ_[p])^(k-2-j) - (p : ℂ_[p])^j) -
        (ιp (f.epsilon p)*(p : ℂ_[p])^(k-2) / α^2)*((p : ℂ_[p])-1)) *
          ιp (algebraicSymbol P s j 0 1) := by
    simp only [diskMoment,pow_one,Nat.sub_self,pow_zero,Int.cast_natCast,
      Finset.sum_sub_distrib,← Finset.mul_sum]
    rw [ha,hc]
    ring
  rw [hsum]
  congr 1
  simp only [eulerMultiplier,pow_zero,inv_one,one_mul,conductor_one_character_value,
    map_one]
  have hpow : (p : ℂ_[p])^(k-2-j) * (p : ℂ_[p])^j = (p : ℂ_[p])^(k-2) := by
    rw [← pow_add,Nat.sub_add_cancel hj]
  have hpow' : (p : ℂ_[p])^(k-1) = (p : ℂ_[p])^(k-2) * p := by
    rw [← pow_succ]
    congr 1
    omega
  have hr := hα.2
  rw [hpow'] at hr
  field_simp
  linear_combination -hr - ιp (f.epsilon p) * hpow

private lemma monomial_integral_depth_one {p N k : ℕ} [Fact p.Prime]
    {ι : Qbar →+* ℂ} (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (α : ℂ_[p]) (s : Bool) (μ : UnitMeasure p)
    (hμ : RealizesMoments f ιp P α s μ) (j : ℕ) (hj : j ≤ k - 2) :
    ∃ g : C((ℤ_[p])ˣ,ℂ_[p]), (∀ x, g x = coordinate x ^ j) ∧
      μ g = ∑ a : (ZMod p)ˣ, diskMoment f ιp P α s j 1 ((a : ZMod p).val : ℤ) := by
  obtain ⟨g,hg,hmg⟩ := MTT.character_integral_of_disk_moments ιp f P α s μ hμ
    1 (by omega) 1 j hj
  refine ⟨g,?_,?_⟩
  · intro x
    rw [hg,specialFunction,MulChar.one_apply (x.isUnit.map (PadicInt.toZModPow 1)),
      map_one,one_mul]
  · simp only [MulChar.one_apply_coe,map_one,one_mul] at hmg
    rw [hmg]
    apply Fintype.sum_equiv (Units.mapEquiv (ZMod.ringEquivCongr (pow_one p)).toMulEquiv).toEquiv
    intro a
    exact congrArg (fun z : ℕ => diskMoment f ιp P α s j 1 (z : ℤ))
      (ZMod.ringEquivCongr_val (pow_one p) (a : ZMod (p^1))).symm

end MTTConductorOneProof

open MTTConductorOneProof in
theorem solution {p N k : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (α : ℂ_[p]) (hα : IsOrdinaryRoot f ιp α)
    (μ : Bool → UnitMeasure p)
    (hμ : ∀ s, RealizesMoments f ιp P α s (μ s))
    (χ : DirichletCharacter Qbar (p ^ 0)) (hχ : χ.IsPrimitive)
    (j : ℕ) (hj : j ≤ k - 2) :
    ∃ (g : C((ℤ_[p])ˣ, ℂ_[p])) (v : Qbar),
      (∀ x, g x = specialFunction ιp 0 χ j x) ∧
      ι v = normalizedCriticalValue f P.omega 0 χ j ∧
      (μ true + μ false) g = eulerMultiplier f ιp α 0 χ j * ιp v := by
  classical
  let v := algebraicSymbol P true j 0 1 + algebraicSymbol P false j 0 1
  obtain ⟨g,hg,hgt⟩ := monomial_integral_depth_one ιp f P α true (μ true) (hμ true) j hj
  obtain ⟨g',hg',hgf⟩ := monomial_integral_depth_one ιp f P α false (μ false) (hμ false) j hj
  have hgg : g' = g := ContinuousMap.ext (fun x => (hg' x).trans (hg x).symm)
  subst g'
  refine ⟨g,v,?_,?_,?_⟩
  · intro x
    simp only [hg,specialFunction,conductor_one_character_value,map_one,one_mul]
  · have h := complex_interpolation_sum hN hk f P 0 χ hχ j hj
    have hv : (∑ a : ZMod (p^0), χ a *
        (algebraicSymbol P true j a.val (p^0) + algebraicSymbol P false j a.val (p^0))) = v := by
      simp only [conductor_one_character_value,one_mul]
      have hval (a : ZMod (p^0)) : a.val = 0 := by
        have ha := ZMod.val_lt a
        simpa only [pow_zero,Nat.lt_one_iff] using ha
      simp only [hval,Nat.cast_zero,pow_zero,Finset.sum_const,Finset.card_univ,
        ZMod.card,nsmul_eq_mul,Nat.cast_one,one_mul,v]
    rw [hv] at h
    exact h
  · change μ true g + μ false g = _
    rw [hgt,hgf,disk_sum_one hN hk ιp f P α hα true χ j hj,
      disk_sum_one hN hk ιp f P α hα false χ j hj]
    simp only [v,map_add,mul_add]
