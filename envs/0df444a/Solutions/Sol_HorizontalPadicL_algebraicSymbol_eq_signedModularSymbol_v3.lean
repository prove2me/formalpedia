-- Prove2me | solution 1 for HorizontalPadicL.algebraicSymbol_eq_signedModularSymbol_v3
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T11:42:15.241328+00:00
-- url     : https://prove2.me/submissions/adfe7f9c-1994-48d6-b298-e60e5da91719

import Definitions.Def_MTT_Measures
import Definitions.Def_KN_SeededThetaConstructionV2B
import Mathlib.NumberTheory.ModularForms.LFunction
import Mathlib.NumberTheory.ModularForms.Identities
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 4000
noncomputable section
open scoped BigOperators ModularForm
open MeasureTheory Complex UpperHalfPlane MTT ModularForm ConjAct Pointwise

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

theorem hecke_pointwise (hN : 0 < N) (hk : 2 ≤ k) (f : Eigenform N k ι)
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
open HorizontalPadicL

private lemma symbol_vertical_local (f : UpperHalfPlane → ℂ) (a m : ℚ)
    (hm : m ≠ 0) (j : ℕ) :
    modularSymbol f j a m = (2 * Real.pi : ℂ) * ((m : ℂ) * Complex.I) ^ j *
      verticalMoment f (-a / m) j := by
  unfold modularSymbol modularIntegral verticalMoment
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have heq (t : ℝ) :
      ((((m : ℂ) • Polynomial.X + Polynomial.C (a : ℂ)) ^ j).eval
        (((-a / m : ℚ) : ℂ) + Complex.I * t)) =
      ((m : ℂ) * Complex.I) ^ j * (t : ℂ) ^ j := by
    simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_smul,
      Polynomial.eval_X, Polynomial.eval_C, smul_eq_mul, Rat.cast_div, Rat.cast_neg]
    rw [← mul_pow]
    congr 1
    field_simp
    ring
  simp_rw [heq]
  rw [show (fun t : ℝ => f (ofComplex (((-a / m : ℚ) : ℂ) + Complex.I * t)) *
      (((m : ℂ) * Complex.I) ^ j * (t : ℂ) ^ j)) =
    (fun t : ℝ => ((m : ℂ) * Complex.I) ^ j *
      (f (ofComplex (((-a / m : ℚ) : ℂ) + Complex.I * t)) * (t : ℂ) ^ j)) by
        funext t; ring, integral_const_mul]
  ring

theorem solution
    {N k : ℕ} {ι : MTT.Qbar →+* ℂ}
    (hN : 0 < N) (hk : 2 ≤ k) (f : MTT.Eigenform N k ι)
    (P : MTT.Periods k ι f.form) (s : Bool) (j : ℕ) (a m : ℚ)
    (hj : j ≤ k - 2) (hm : m ≠ 0) :
    ι (MTT.algebraicSymbol P s j a m) * P.omega s =
      signedModularSymbol f.form s j a m := by
  have hclosed := symbol_closed hN hk f P s j hj a m hm
  have hcomparison :
      2 * P.omega s * ι (algebraicSymbol P s j a m) =
        modularSymbol f.form j a m +
          (MTT.sign s : ℂ) * (-1 : ℂ) ^ j *
            modularSymbol f.form j (-a) m := by
    rw [symbol_vertical_local f.form a m hm j,
      symbol_vertical_local f.form (-a) m hm j]
    simp only [neg_neg]
    simp only [mul_comm (m : ℂ) Complex.I]
    linear_combination 2 * hclosed
  unfold signedModularSymbol
  linear_combination (1 / 2 : ℂ) * hcomparison
