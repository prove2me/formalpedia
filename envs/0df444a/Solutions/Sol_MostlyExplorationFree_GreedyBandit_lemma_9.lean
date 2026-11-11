-- Prove2me | solution 1 for MostlyExplorationFree.GreedyBandit.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T05:29:32.684397+00:00
-- url     : https://prove2.me/submissions/65435702-e41c-428c-a4d7-4a4a78830905

import Mathlib
import Definitions.Def_TroppMatrixConcentration_probability
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Matrix
import Theorems.Thm_TroppMatrixConcentration_ch3_probabilistic_lieb

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace P09c104e7

open TroppMatrixConcentration

/-- The exact statement of the Proved platform theorem 712d622b
(TroppMatrixConcentration.ch3_probabilistic_lieb), specialised to a `Type` sample space. -/
def ProbLieb : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (H : Matrix (Fin d) (Fin d) ℂ) (_hH : H.IsHermitian)
    (X : Ω → Matrix (Fin d) (Fin d) ℂ)
    (_hMeas : Measurable X) (_hHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    (_hExp : Integrable (fun ω => matrixExp (X ω)) μ),
    (∫ ω, traceExp (H + X ω) ∂μ) ≤
      traceExp (H + matrixLog (∫ ω, matrixExp (X ω) ∂μ))

lemma exp_matrixLog {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosDef) :
    matrixExp (matrixLog A) = A := by
  have h := CFC.exp_log A hA.isStrictlyPositive
  simpa [matrixExp, matrixLog, CFC.log] using h

lemma matrixLog_isHermitian {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    (matrixLog A).IsHermitian := by
  have : IsSelfAdjoint (cfc Real.log A) := IsSelfAdjoint.cfc
  exact this

/-- Lieb concavity (two-point form) from the probabilistic Lieb theorem, via a Bernoulli measure. -/
lemma lieb_two_point (hL : ProbLieb) {d : ℕ} [NeZero d]
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    {A B : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * traceExp (H + matrixLog A) + (1 - t) * traceExp (H + matrixLog B) ≤
      traceExp (H + matrixLog ((t : ℂ) • A + ((1 - t : ℝ) : ℂ) • B)) := by
  classical
  let μ : Measure Bool :=
    ENNReal.ofReal t • Measure.dirac true + ENNReal.ofReal (1 - t) • Measure.dirac false
  have : IsProbabilityMeasure μ := by
    constructor
    simp only [μ, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem,
      Set.mem_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add ht0 (by linarith)]
    simp
  let X : Bool → Matrix (Fin d) (Fin d) ℂ := fun b => if b then matrixLog A else matrixLog B
  have hmeas : Measurable X := measurable_of_finite X
  have hherm : ∀ᵐ ω ∂μ, (X ω).IsHermitian :=
    Filter.Eventually.of_forall fun b => by
      cases b <;> simp [X, matrixLog_isHermitian]
  have hint : Integrable (fun ω => matrixExp (X ω)) μ := Integrable.of_finite
  have key := hL μ H hH X hmeas hherm hint
  have e1 : (∫ ω, traceExp (H + X ω) ∂μ) =
      t * traceExp (H + matrixLog A) + (1 - t) * traceExp (H + matrixLog B) := by
    have hi : ∀ f : Bool → ℝ, Integrable f μ := fun f => Integrable.of_finite
    simp only [μ]
    rw [integral_add_measure (hi _ |>.mono_measure (by
          exact Measure.le_add_right le_rfl)) (hi _ |>.mono_measure (by
          exact Measure.le_add_left le_rfl))]
    rw [integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
    simp [X, ENNReal.toReal_ofReal ht0, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 1 - t)]
  have e2 : (∫ ω, matrixExp (X ω) ∂μ) = (t : ℂ) • A + ((1 - t : ℝ) : ℂ) • B := by
    have hi : ∀ f : Bool → Matrix (Fin d) (Fin d) ℂ, Integrable f μ := fun f => Integrable.of_finite
    simp only [μ]
    rw [integral_add_measure (hi _ |>.mono_measure (by
          exact Measure.le_add_right le_rfl)) (hi _ |>.mono_measure (by
          exact Measure.le_add_left le_rfl))]
    rw [integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
    simp only [X, if_true, Bool.false_eq_true, if_false, exp_matrixLog hA, exp_matrixLog hB,
      ENNReal.toReal_ofReal ht0, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 1 - t)]
    try (rw [← Complex.coe_smul, ← Complex.coe_smul])
    try rfl
  rw [e1, e2] at key
  exact key

lemma traceExp_add_algebraMap {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (c : ℝ) :
    traceExp (A + algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) c) = Real.exp c * traceExp A := by
  have hc : Commute A (algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) c) := (Algebra.commutes c A).symm
  have hsa : IsSelfAdjoint (algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) c) := by
    first
      | exact IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all c)
      | simp [IsSelfAdjoint, Algebra.algebraMap_eq_smul_one]
  have h1 : matrixExp (A + algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) c) =
      Real.exp c • matrixExp A := by
    rw [matrixExp, matrixExp, Matrix.exp_add_of_commute _ _ hc,
      ← CFC.real_exp_eq_normedSpace_exp hsa,
      cfc_algebraMap, ← Algebra.commutes, ← Algebra.smul_def]
  rw [traceExp, traceExp, h1, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

lemma traceExp_nonneg {d : ℕ} {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) :
    0 ≤ traceExp M := by
  have h0 : (0 : Matrix (Fin d) (Fin d) ℂ) ≤ NormedSpace.exp M :=
    IsSelfAdjoint.exp_nonneg (show IsSelfAdjoint M from hM)
  have hpsd : (NormedSpace.exp M).PosSemidef := Matrix.nonneg_iff_posSemidef.1 h0
  have h := hpsd.trace_nonneg
  have := (Complex.le_def.1 h).1
  simpa [traceExp, matrixExp] using this

lemma traceExp_log_smul {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) {Y : Matrix (Fin d) (Fin d) ℂ}
    (hY : Y.PosDef) {t : ℝ} (ht : 0 < t) :
    traceExp (H + matrixLog (t • Y)) = t * traceExp (H + matrixLog Y) := by
  have h := CFC.log_smul' (A := Matrix (Fin d) (Fin d) ℂ) Y ht hY.isStrictlyPositive
  have h' : matrixLog (t • Y) = algebraMap ℝ _ (Real.log t) + matrixLog Y := by
    simpa [matrixLog, CFC.log] using h
  have e : H + (algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) (Real.log t) + matrixLog Y) =
      (H + matrixLog Y) + algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) (Real.log t) := by abel
  rw [h', e, traceExp_add_algebraMap, Real.exp_log ht]

lemma lieb_superadd (hL : ProbLieb) {d : ℕ} [NeZero d]
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    {A B : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    traceExp (H + matrixLog A) + traceExp (H + matrixLog B) ≤
      traceExp (H + matrixLog (A + B)) := by
  have h := lieb_two_point hL H hH hA hB (t := 1/2) (by norm_num) (by norm_num)
  have e : ((1/2 : ℝ) : ℂ) • A + ((1 - 1/2 : ℝ) : ℂ) • B = (1/2 : ℝ) • (A + B) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    push_cast; ring
  rw [e, traceExp_log_smul H (hA.add hB) (by norm_num)] at h
  linarith

lemma one_le_matrixExp {d : ℕ} {D : Matrix (Fin d) (Fin d) ℂ} (hD : 0 ≤ D) :
    (1 : Matrix (Fin d) (Fin d) ℂ) ≤ matrixExp D := by
  have hsa : IsSelfAdjoint D := IsSelfAdjoint.of_nonneg hD
  rw [matrixExp, ← CFC.real_exp_eq_normedSpace_exp hsa]
  calc (1 : Matrix (Fin d) (Fin d) ℂ) = cfc (fun _ : ℝ => (1:ℝ)) D := (cfc_const_one ℝ D).symm
    _ ≤ cfc Real.exp D :=
        cfc_mono (fun x hx => Real.one_le_exp (spectrum_nonneg_of_nonneg hD hx))

/-- Trace-exponential is monotone along nonnegative increments (derived from Lieb concavity
via homogeneity and superadditivity; no eigenvalue interlacing needed). -/
lemma traceExp_le_add (hL : ProbLieb) {d : ℕ} [NeZero d]
    {H D : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian) (hD : 0 ≤ D) :
    traceExp H ≤ traceExp (H + D) := by
  have hsa : IsSelfAdjoint D := IsSelfAdjoint.of_nonneg hD
  have hY1 : (1 : Matrix (Fin d) (Fin d) ℂ) ≤ matrixExp D := one_le_matrixExp hD
  have hlogY : matrixLog (matrixExp D) = D := by
    simpa [matrixLog, matrixExp, CFC.log] using CFC.log_exp D hsa
  have hlog1 : matrixLog (1 : Matrix (Fin d) (Fin d) ℂ) = 0 := by
    simpa [matrixLog, CFC.log] using (CFC.log_one (A := Matrix (Fin d) (Fin d) ℂ))
  have key : ∀ δ : ℝ, 0 < δ → δ < 1 → (1 - δ) * traceExp H ≤ traceExp (H + D) := by
    intro δ hδ0 hδ1
    have hP1 : ((1 - δ) • (1 : Matrix (Fin d) (Fin d) ℂ)).PosDef :=
      Matrix.PosDef.one.smul (by linarith)
    have hP2 : (matrixExp D - (1 - δ) • (1 : Matrix (Fin d) (Fin d) ℂ)).PosDef := by
      have hpsd : (matrixExp D - 1).PosSemidef :=
        Matrix.nonneg_iff_posSemidef.1 (sub_nonneg.2 hY1)
      have hpd : (δ • (1 : Matrix (Fin d) (Fin d) ℂ)).PosDef := Matrix.PosDef.one.smul hδ0
      have e : matrixExp D - (1 - δ) • (1 : Matrix (Fin d) (Fin d) ℂ) =
          (matrixExp D - 1) + δ • 1 := by rw [sub_smul, one_smul]; abel
      rw [e, add_comm]; exact hpd.add_posSemidef hpsd
    have h := lieb_superadd hL H hH hP1 hP2
    have hsum : (1 - δ) • (1 : Matrix (Fin d) (Fin d) ℂ) +
        (matrixExp D - (1 - δ) • (1 : Matrix (Fin d) (Fin d) ℂ)) = matrixExp D := by abel
    rw [hsum, hlogY, traceExp_log_smul H Matrix.PosDef.one (by linarith), hlog1, add_zero] at h
    have h0 := traceExp_nonneg (hH.add (matrixLog_isHermitian
      (matrixExp D - (1 - δ) • (1 : Matrix (Fin d) (Fin d) ℂ))))
    linarith
  by_contra hcon
  push Not at hcon
  have hb : 0 ≤ traceExp (H + D) := traceExp_nonneg (hH.add hsa)
  have ha : 0 < traceExp H := lt_of_le_of_lt hb hcon
  have h := key ((traceExp H - traceExp (H + D)) / (2 * traceExp H))
    (div_pos (by linarith) (by linarith)) (by rw [div_lt_one (by linarith)]; linarith)
  have e : (1 - (traceExp H - traceExp (H + D)) / (2 * traceExp H)) * traceExp H =
      (traceExp H + traceExp (H + D)) / 2 := by field_simp; ring
  rw [e] at h
  linarith

/-! ### Step 1: scalar chord bound and its CFC lift -/

lemma exp_neg_le_chord {θ R x : ℝ} (hR : 0 < R) (hx0 : 0 ≤ x) (hxR : x ≤ R) :
    Real.exp (-θ * x) ≤ 1 - (1 - Real.exp (-θ * R)) / R * x := by
  have ha : 0 ≤ 1 - x / R := by rw [sub_nonneg, div_le_one hR]; exact hxR
  have hb : 0 ≤ x / R := div_nonneg hx0 hR.le
  have h := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (-θ * R)) ha hb (by ring)
  have e : (1 - x / R) • (0:ℝ) + (x / R) • (-θ * R) = -θ * x := by
    simp only [smul_eq_mul]; field_simp; ring
  rw [e] at h
  simp only [smul_eq_mul, Real.exp_zero] at h
  calc Real.exp (-θ * x) ≤ (1 - x / R) * 1 + x / R * Real.exp (-θ * R) := h
    _ = 1 - (1 - Real.exp (-θ * R)) / R * x := by field_simp; ring

lemma cfc_one_sub_mul {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : IsSelfAdjoint A) (g : ℝ) :
    cfc (fun x : ℝ => 1 - g * x) A = 1 - g • A := by
  rw [cfc_sub (fun _ : ℝ => (1:ℝ)) (fun x : ℝ => g * x) A, cfc_const_one ℝ A,
    cfc_const_mul_id g A]

lemma matrixLog_one_sub {d : ℕ} {W : Matrix (Fin d) (Fin d) ℂ} {g : ℝ} (hW : IsSelfAdjoint W)
    (hpos : ∀ x ∈ spectrum ℝ W, 0 < 1 - g * x) :
    matrixLog (1 - g • W) = cfc (fun x => Real.log (1 - g * x)) W := by
  have h := cfc_comp' Real.log (fun x => 1 - g * x) W
    (Real.continuousOn_log.mono (by rintro _ ⟨x, hx, rfl⟩; exact (hpos x hx).ne'))
    (by fun_prop) hW
  rw [h, cfc_one_sub_mul W hW g]
  first | rfl | simp [matrixLog, CFC.log]

lemma spectrum_mem_Icc {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} {R : ℝ} (hA : 0 ≤ A)
    (hAR : A ≤ algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) R) :
    ∀ x ∈ spectrum ℝ A, 0 ≤ x ∧ x ≤ R := fun x hx =>
  ⟨spectrum_nonneg_of_nonneg hA hx,
    (le_algebraMap_iff_spectrum_le (IsSelfAdjoint.of_nonneg hA)).1 hAR x hx⟩

lemma one_sub_pos_of_Icc {R θ x : ℝ} (hR : 0 < R) (hx : 0 ≤ x ∧ x ≤ R) :
    0 < 1 - (1 - Real.exp (-θ * R)) / R * x :=
  lt_of_lt_of_le (Real.exp_pos _) (exp_neg_le_chord hR hx.1 hx.2)

/-- `-θ A ≤ log (1 - g A)` for `0 ≤ A ≤ R`, with `g = (1 - e^{-θR})/R`. -/
lemma neg_smul_le_log_one_sub {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} {R θ : ℝ} (hR : 0 < R)
    (hA : 0 ≤ A) (hAR : A ≤ algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) R) :
    (-θ) • A ≤ matrixLog (1 - ((1 - Real.exp (-θ * R)) / R) • A) := by
  have hsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  have hspec := spectrum_mem_Icc hA hAR
  have hpos : ∀ x ∈ spectrum ℝ A, 0 < 1 - (1 - Real.exp (-θ * R)) / R * x := fun x hx =>
    one_sub_pos_of_Icc hR (hspec x hx)
  rw [matrixLog_one_sub hsa hpos, ← cfc_const_mul_id (-θ) A hsa]
  have hcont : ContinuousOn (fun x => Real.log (1 - (1 - Real.exp (-θ * R)) / R * x))
      (spectrum ℝ A) :=
    ContinuousOn.log (by fun_prop) (fun x hx => (hpos x hx).ne')
  refine cfc_mono (fun x hx => ?_) (hg := hcont)
  rw [Real.le_log_iff_exp_le (hpos x hx)]
  exact exp_neg_le_chord hR (hspec x hx).1 (hspec x hx).2

/-- `log (1 - g W) ≤ -g W` whenever `1 - g W` is positive definite. -/
lemma log_one_sub_le {d : ℕ} {W : Matrix (Fin d) (Fin d) ℂ} {g : ℝ} (hW : IsSelfAdjoint W)
    (hpos : ∀ x ∈ spectrum ℝ W, 0 < 1 - g * x) :
    matrixLog (1 - g • W) ≤ (-g) • W := by
  rw [matrixLog_one_sub hW hpos, ← cfc_const_mul_id (-g) W hW]
  have hcont : ContinuousOn (fun x => Real.log (1 - g * x)) (spectrum ℝ W) :=
    ContinuousOn.log (by fun_prop) (fun x hx => (hpos x hx).ne')
  refine cfc_mono (fun x hx => ?_) (hf := hcont)
  have := Real.log_le_sub_one_of_pos (hpos x hx)
  linarith

/-! ### Step 2: fixed-`H` conditional Jensen on real coefficient arrays -/

/-- Complexification of a real coefficient array. -/
noncomputable def cx {d : ℕ} (Z : Fin d → Fin d → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  (Matrix.of Z).map Complex.ofReal

lemma continuous_cx {d : ℕ} : Continuous (cx (d := d)) :=
  continuous_pi fun i => continuous_pi fun j =>
    Complex.continuous_ofReal.comp ((continuous_apply j).comp (continuous_apply i))

lemma cx_add_smul {d : ℕ} (Z1 Z2 : Fin d → Fin d → ℝ) (a b : ℝ) :
    cx (a • Z1 + b • Z2) = a • cx Z1 + b • cx Z2 := by
  ext i j
  simp [cx]

/-- The closed convex domain `c ≤ Z ≤ 1` (Loewner order, complexified). -/
def sSet {d : ℕ} (c : ℝ) : Set (Fin d → Fin d → ℝ) :=
  {Z | IsSelfAdjoint (cx Z) ∧ algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) c ≤ cx Z ∧ cx Z ≤ 1}

lemma isClosed_sSet {d : ℕ} (c : ℝ) : IsClosed (sSet (d := d) c) := by
  refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
  · exact isClosed_eq (continuous_star.comp continuous_cx) continuous_cx
  · exact isClosed_le continuous_const continuous_cx
  · exact isClosed_le continuous_cx continuous_const

lemma smul_le_smul_real {d : ℕ} {M N : Matrix (Fin d) (Fin d) ℂ} (h : M ≤ N) {a : ℝ}
    (ha : 0 ≤ a) : a • M ≤ a • N := by
  first
  | exact smul_le_smul_of_nonneg_left h ha
  | (have h' := Matrix.nonneg_iff_posSemidef.1 (sub_nonneg.2 h)
     have h'' : ((a : ℂ) • (N - M)).PosSemidef := h'.smul (by exact_mod_cast ha)
     rw [Complex.coe_smul, smul_sub] at h''
     exact sub_nonneg.1 (Matrix.nonneg_iff_posSemidef.2 h''))

lemma convex_sSet {d : ℕ} (c : ℝ) : Convex ℝ (sSet (d := d) c) := by
  intro Z1 h1 Z2 h2 a b ha hb hab
  refine ⟨?_, ?_, ?_⟩ <;> rw [cx_add_smul]
  · exact ((IsSelfAdjoint.all a).smul h1.1).add ((IsSelfAdjoint.all b).smul h2.1)
  · have e : algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) c =
        a • algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) c + b • algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) c := by
      rw [← add_smul, hab, one_smul]
    rw [e]
    exact add_le_add (smul_le_smul_real h1.2.1 ha) (smul_le_smul_real h2.2.1 hb)
  · have e : (1 : Matrix (Fin d) (Fin d) ℂ) = a • 1 + b • 1 := by
      rw [← add_smul, hab, one_smul]
    rw [e]
    exact add_le_add (smul_le_smul_real h1.2.2 ha) (smul_le_smul_real h2.2.2 hb)

lemma posDef_of_sSet {d : ℕ} {c : ℝ} (hc : 0 < c) {Z : Fin d → Fin d → ℝ}
    (hZ : Z ∈ sSet (d := d) c) : (cx Z).PosDef := by
  have hpsd : (cx Z - algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) c).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.1 (sub_nonneg.2 hZ.2.1)
  have hpd : (algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) c).PosDef := by
    rw [Algebra.algebraMap_eq_smul_one]; exact Matrix.PosDef.one.smul hc
  have e : cx Z = algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) c +
      (cx Z - algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) c) := by abel
  rw [e]; exact hpd.add_posSemidef hpsd

/-- The Lieb functional with fixed `H`. -/
noncomputable def φL {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (Z : Fin d → Fin d → ℝ) : ℝ :=
  traceExp (H + matrixLog (cx Z))

lemma concaveOn_φL (hL : ProbLieb) {d : ℕ} [NeZero d] {H : Matrix (Fin d) (Fin d) ℂ}
    (hH : H.IsHermitian) {c : ℝ} (hc : 0 < c) : ConcaveOn ℝ (sSet (d := d) c) (φL H) := by
  refine ⟨convex_sSet c, fun Z1 h1 Z2 h2 a b ha hb hab => ?_⟩
  obtain rfl : b = 1 - a := by linarith
  have e : cx (a • Z1 + (1 - a) • Z2) = (a : ℂ) • cx Z1 + ((1 - a : ℝ) : ℂ) • cx Z2 := by
    rw [cx_add_smul, Complex.coe_smul, Complex.coe_smul]
  have h := lieb_two_point hL H hH (posDef_of_sSet hc h1) (posDef_of_sSet hc h2) ha (by linarith)
  simp only [φL, smul_eq_mul]
  rw [e]; exact h

lemma continuous_traceExp {d : ℕ} : Continuous (fun M : Matrix (Fin d) (Fin d) ℂ => traceExp M) := by
  have hexp : Continuous (NormedSpace.exp : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ) := by
    rw [← continuousOn_univ, ← Metric.eball_top_eq_univ (0 : Matrix (Fin d) (Fin d) ℂ),
      ← NormedSpace.expSeries_radius_eq_top ℂ (Matrix (Fin d) (Fin d) ℂ)]
    exact NormedSpace.continuousOn_exp (𝕂 := ℂ)
  unfold traceExp matrixExp
  exact Complex.continuous_re.comp (Continuous.matrix_trace hexp)

lemma continuousOn_φL {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) {c : ℝ} (hc : 0 < c) :
    ContinuousOn (φL H) (sSet (d := d) c) := by
  have hlog : ContinuousOn (fun Z => matrixLog (cx Z)) (sSet (d := d) c) :=
    CFC.continuousOn_log.comp continuous_cx.continuousOn (fun Z hZ =>
      ⟨hZ.1, (posDef_of_sSet hc hZ).isStrictlyPositive.isUnit⟩)
  exact continuous_traceExp.comp_continuousOn (continuousOn_const.add hlog)

lemma matrixLog_nonpos {d : ℕ} {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.PosDef) (h1 : M ≤ 1) :
    matrixLog M ≤ 0 := by
  have hsa : IsSelfAdjoint M := hM.isHermitian
  have hsp := hM.isStrictlyPositive
  have h0 : 0 ≤ M := hsp.nonneg
  have h1' : M ≤ algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) 1 := by rwa [map_one]
  have hcont : ContinuousOn Real.log (spectrum ℝ M) :=
    Real.continuousOn_log.mono (fun x hx => by
      rintro rfl; exact spectrum.zero_notMem ℝ hsp.isUnit hx)
  rw [matrixLog, ← cfc_zero ℝ M]
  exact cfc_mono (fun x hx => Real.log_nonpos (spectrum_nonneg_of_nonneg h0 hx)
    ((le_algebraMap_iff_spectrum_le hsa).1 h1' x hx)) (hf := hcont)

lemma φL_nonneg {d : ℕ} {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    (Z : Fin d → Fin d → ℝ) : 0 ≤ φL H Z :=
  traceExp_nonneg (hH.add (matrixLog_isHermitian _))

lemma φL_le (hL : ProbLieb) {d : ℕ} [NeZero d] {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    {c : ℝ} (hc : 0 < c) {Z : Fin d → Fin d → ℝ} (hZ : Z ∈ sSet (d := d) c) :
    φL H Z ≤ traceExp H := by
  have hl0 := matrixLog_nonpos (posDef_of_sSet hc hZ) hZ.2.2
  have h := traceExp_le_add hL (H := H + matrixLog (cx Z)) (D := -matrixLog (cx Z))
    (hH.add (matrixLog_isHermitian _)) (neg_nonneg.2 hl0)
  simpa [φL] using h

/-- Conditional Jensen for the Lieb functional with a deterministic `H`. -/
lemma jensen_fixed (hL : ProbLieb) {d : ℕ} [NeZero d] {H : Matrix (Fin d) (Fin d) ℂ}
    (hH : H.IsHermitian) {c : ℝ} (hc : 0 < c) {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] (hm : m ≤ mΩ) (Z : Ω → (Fin d → Fin d → ℝ))
    (hZi : Integrable Z μ) (hZs : ∀ᵐ ω ∂μ, Z ω ∈ sSet (d := d) c)
    (hφi : Integrable (φL H ∘ Z) μ) :
    μ[φL H ∘ Z | m] ≤ᵐ[μ] φL H ∘ μ[Z | m] :=
  (concaveOn_φL hL hH hc).condExp_map_le hm (continuousOn_φL H hc).upperSemicontinuousOn hZs
    (isClosed_sSet c) hZi hφi

lemma aesm_φL_comp {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) {c : ℝ} (hc : 0 < c) {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → (Fin d → Fin d → ℝ)}
    (hf : AEMeasurable f μ) (hfs : ∀ᵐ ω ∂μ, f ω ∈ sSet (d := d) c) :
    AEStronglyMeasurable (φL H ∘ f) μ := by
  have hs : MeasurableSet (sSet (d := d) c) := (isClosed_sSet c).measurableSet
  have hν : (μ.map f).restrict (sSet (d := d) c) = μ.map f := by
    apply Measure.restrict_eq_self_of_ae_mem
    exact (ae_map_iff (p := fun x => x ∈ sSet (d := d) c) hf hs).2 hfs
  have h1 : AEStronglyMeasurable (φL H) ((μ.map f).restrict (sSet (d := d) c)) :=
    (continuousOn_φL H hc).aestronglyMeasurable hs
  rw [hν] at h1
  exact h1.comp_aemeasurable hf

lemma integrable_φL_comp (hL : ProbLieb) {d : ℕ} [NeZero d] {H : Matrix (Fin d) (Fin d) ℂ}
    (hH : H.IsHermitian) {c : ℝ} (hc : 0 < c) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → (Fin d → Fin d → ℝ)}
    (hf : AEMeasurable f μ) (hfs : ∀ᵐ ω ∂μ, f ω ∈ sSet (d := d) c) :
    Integrable (φL H ∘ f) μ :=
  Integrable.of_bound (aesm_φL_comp H hc hf hfs) (traceExp H) (hfs.mono fun ω h => by
    show ‖φL H (f ω)‖ ≤ traceExp H
    rw [Real.norm_of_nonneg (φL_nonneg hH _)]; exact φL_le hL hH hc h)

/-- Set-integral form of the fixed-`H` Jensen inequality on `m`-measurable sets. -/
lemma setIntegral_jensen (hL : ProbLieb) {d : ℕ} [NeZero d] {H : Matrix (Fin d) (Fin d) ℂ}
    (hH : H.IsHermitian) {c : ℝ} (hc : 0 < c) {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] (hm : m ≤ mΩ) (Z : Ω → (Fin d → Fin d → ℝ))
    (hZi : Integrable Z μ) (hZs : ∀ᵐ ω ∂μ, Z ω ∈ sSet (d := d) c) {A : Set Ω}
    (hA : MeasurableSet[m] A) :
    ∫ ω in A, φL H (Z ω) ∂μ ≤ ∫ ω in A, φL H (μ[Z | m] ω) ∂μ := by
  have hφi : Integrable (φL H ∘ Z) μ := integrable_φL_comp hL hH hc hZi.aemeasurable hZs
  have hCs : ∀ᵐ ω ∂μ, μ[Z | m] ω ∈ sSet (d := d) c :=
    (convex_sSet c).condExp_mem hm hZi (isClosed_sSet c) hZs
  have hCm : AEMeasurable (μ[Z | m]) μ :=
    (stronglyMeasurable_condExp.mono hm).measurable.aemeasurable
  have hCi : Integrable (φL H ∘ μ[Z | m]) μ := integrable_φL_comp hL hH hc hCm hCs
  have e := setIntegral_condExp hm hφi hA
  calc ∫ ω in A, φL H (Z ω) ∂μ = ∫ ω in A, (μ[φL H ∘ Z | m]) ω ∂μ := e.symm
    _ ≤ ∫ ω in A, φL H (μ[Z | m] ω) ∂μ :=
        setIntegral_mono_ae integrable_condExp.integrableOn hCi.integrableOn
          (jensen_fixed hL hH hc hm Z hZi hZs hφi)

/-! ### Step 3: random `m`-measurable `H` (simple approximation + dominated convergence) -/

/-- Admissible random `H` values: complexified real arrays, self-adjoint, `≤ K`. -/
def tset {d : ℕ} (K : ℝ) : Set (Fin d → Fin d → ℝ) :=
  {h | IsSelfAdjoint (cx h) ∧ cx h ≤ algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) K}

lemma cx_zero {d : ℕ} : cx (0 : Fin d → Fin d → ℝ) = 0 := by
  ext i j; simp [cx]

lemma zero_mem_tset {d : ℕ} {K : ℝ} (hK : 0 ≤ K) : (0 : Fin d → Fin d → ℝ) ∈ tset (d := d) K := by
  refine ⟨by rw [cx_zero]; exact IsSelfAdjoint.zero _, ?_⟩
  rw [cx_zero, Algebra.algebraMap_eq_smul_one]
  exact Matrix.nonneg_iff_posSemidef.2 (Matrix.PosSemidef.one.smul hK)

lemma traceExp_le_of_le (hL : ProbLieb) {d : ℕ} [NeZero d] {h : Matrix (Fin d) (Fin d) ℂ}
    (hh : IsSelfAdjoint h) {K : ℝ} (hK : h ≤ algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) K) :
    traceExp h ≤ Real.exp K * traceExp (0 : Matrix (Fin d) (Fin d) ℂ) := by
  have h1 := traceExp_le_add hL (H := h) (D := algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) K - h) hh
    (sub_nonneg.2 hK)
  have e : h + (algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) K - h) =
      0 + algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) K := by abel
  rw [e, traceExp_add_algebraMap] at h1
  exact h1

/-- The Lieb functional as a function of the pair `(H, Z)` of real arrays. -/
noncomputable def ψL {d : ℕ} (p : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)) : ℝ :=
  traceExp (cx p.1 + matrixLog (cx p.2))

lemma continuousOn_ψL {d : ℕ} {c : ℝ} (hc : 0 < c) :
    ContinuousOn (ψL (d := d)) (Set.univ ×ˢ sSet c) := by
  have hlog : ContinuousOn
      (fun p : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ) => matrixLog (cx p.2))
      (Set.univ ×ˢ sSet c) :=
    CFC.continuousOn_log.comp (continuous_cx.comp continuous_snd).continuousOn (fun p hp =>
      ⟨hp.2.1, (posDef_of_sSet hc hp.2).isStrictlyPositive.isUnit⟩)
  exact continuous_traceExp.comp_continuousOn
    ((continuous_cx.comp continuous_fst).continuousOn.add hlog)

lemma aesm_ψL_comp {d : ℕ} {c : ℝ} (hc : 0 < c) {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {f : Ω → (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)}
    (hf : AEMeasurable f μ) (hfs : ∀ᵐ ω ∂μ, (f ω).2 ∈ sSet (d := d) c) :
    AEStronglyMeasurable (ψL ∘ f) μ := by
  have hs : MeasurableSet ((Set.univ : Set (Fin d → Fin d → ℝ)) ×ˢ sSet (d := d) c) :=
    MeasurableSet.univ.prod (isClosed_sSet c).measurableSet
  have hν : (μ.map f).restrict ((Set.univ : Set (Fin d → Fin d → ℝ)) ×ˢ sSet (d := d) c) = μ.map f := by
    apply Measure.restrict_eq_self_of_ae_mem
    exact (ae_map_iff (p := fun x => x ∈ (Set.univ : Set (Fin d → Fin d → ℝ)) ×ˢ sSet (d := d) c) hf hs).2
      (hfs.mono fun ω h => ⟨Set.mem_univ _, h⟩)
  have h1 : AEStronglyMeasurable ψL ((μ.map f).restrict ((Set.univ : Set (Fin d → Fin d → ℝ)) ×ˢ sSet (d := d) c)) :=
    (continuousOn_ψL hc).aestronglyMeasurable hs
  rw [hν] at h1
  exact h1.comp_aemeasurable hf

lemma ψL_bound (hL : ProbLieb) {d : ℕ} [NeZero d] {c K : ℝ} (hc : 0 < c)
    {h z : Fin d → Fin d → ℝ} (hh : h ∈ tset (d := d) K) (hz : z ∈ sSet (d := d) c) :
    ‖ψL (h, z)‖ ≤ Real.exp K * traceExp (0 : Matrix (Fin d) (Fin d) ℂ) := by
  have h0 : 0 ≤ ψL (h, z) := φL_nonneg (H := cx h) hh.1 z
  rw [Real.norm_of_nonneg h0]
  exact (φL_le hL hh.1 hc hz).trans (traceExp_le_of_le hL hh.1 hh.2)

/-- Jensen for an `m`-simple random `H` (finite range, `m`-measurable fibres). -/
lemma integral_simple_le (hL : ProbLieb) {d : ℕ} [NeZero d] {c K : ℝ} (hc : 0 < c)
    {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] (hm : m ≤ mΩ) (Z : Ω → (Fin d → Fin d → ℝ))
    (hZi : Integrable Z μ) (hZs : ∀ᵐ ω ∂μ, Z ω ∈ sSet (d := d) c)
    (s : Ω → (Fin d → Fin d → ℝ)) (T : Finset (Fin d → Fin d → ℝ))
    (hsT : ∀ ω, s ω ∈ T) (hT : ∀ y ∈ T, y ∈ tset (d := d) K)
    (hfib : ∀ y, MeasurableSet[m] (s ⁻¹' {y})) :
    ∫ ω, ψL (s ω, Z ω) ∂μ ≤ ∫ ω, ψL (s ω, μ[Z | m] ω) ∂μ := by
  classical
  have hCs : ∀ᵐ ω ∂μ, μ[Z | m] ω ∈ sSet (d := d) c :=
    (convex_sSet c).condExp_mem hm hZi (isClosed_sSet c) hZs
  have hCm : AEMeasurable (μ[Z | m]) μ :=
    (stronglyMeasurable_condExp.mono hm).measurable.aemeasurable
  have dec : ∀ F : Ω → (Fin d → Fin d → ℝ),
      (∀ y ∈ T, Integrable (fun ω => ψL (y, F ω)) μ) →
      ∫ ω, ψL (s ω, F ω) ∂μ = ∑ y ∈ T, ∫ ω in s ⁻¹' {y}, ψL (y, F ω) ∂μ := by
    intro F hF
    have e : (fun ω => ψL (s ω, F ω)) = fun ω =>
        ∑ y ∈ T, (s ⁻¹' {y}).indicator (fun ω => ψL (y, F ω)) ω := by
      funext ω
      rw [Finset.sum_eq_single (s ω)]
      · rw [Set.indicator_of_mem (show ω ∈ s ⁻¹' {s ω} from rfl)]
      · intro y _ hy
        have hn : ω ∉ s ⁻¹' {y} := fun h => hy (Set.mem_singleton_iff.1 h).symm
        first
          | exact Set.indicator_of_notMem hn _
          | exact Set.indicator_of_not_mem hn _
      · intro h; exact absurd (hsT ω) h
    rw [e, integral_finsetSum _ (fun y hy => (hF y hy).indicator (hm _ (hfib y)))]
    refine Finset.sum_congr rfl fun y _ => ?_
    exact integral_indicator (hm _ (hfib y))
  have hint : ∀ F : Ω → (Fin d → Fin d → ℝ), AEMeasurable F μ →
      (∀ᵐ ω ∂μ, F ω ∈ sSet (d := d) c) →
      ∀ y ∈ T, Integrable (fun ω => ψL (y, F ω)) μ := fun F hF hFs y hy =>
    integrable_φL_comp hL (hT y hy).1 hc hF hFs
  rw [dec Z (hint Z hZi.aemeasurable hZs), dec _ (hint _ hCm hCs)]
  exact Finset.sum_le_sum fun y hy =>
    setIntegral_jensen hL (hT y hy).1 hc hm Z hZi hZs (hfib y)

lemma exists_approx {Ω : Type*} [m : MeasurableSpace Ω] {d : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (Hr : Ω → (Fin d → Fin d → ℝ)) (hHm : Measurable Hr) (hHs : ∀ ω, Hr ω ∈ tset (d := d) K) :
    ∃ s : ℕ → Ω → (Fin d → Fin d → ℝ), (∀ n ω, s n ω ∈ tset (d := d) K) ∧
      (∀ ω, Filter.Tendsto (fun n => s n ω) Filter.atTop (nhds (Hr ω))) ∧
      (∀ n, Measurable (s n)) ∧
      (∀ n, ∃ T : Finset (Fin d → Fin d → ℝ), (∀ ω, s n ω ∈ T) ∧ ∀ y ∈ T, y ∈ tset (d := d) K) ∧
      ∀ n y, MeasurableSet (s n ⁻¹' {y}) := by
  classical
  let A : ℕ → SimpleFunc Ω (Fin d → Fin d → ℝ) := fun n =>
    SimpleFunc.approxOn Hr hHm (tset K) 0 (zero_mem_tset hK) n
  have hmem : ∀ n ω, A n ω ∈ tset (d := d) K := fun n ω =>
    SimpleFunc.approxOn_mem hHm _ n ω
  refine ⟨fun n => A n, hmem,
    fun ω => SimpleFunc.tendsto_approxOn hHm _ (subset_closure (hHs ω)),
    fun n => (A n).measurable, fun n => ⟨(A n).range, fun ω => (A n).mem_range_self ω, ?_⟩,
    fun n y => (A n).measurableSet_fiber y⟩
  intro y hy
  obtain ⟨ω0, rfl⟩ := SimpleFunc.mem_range.1 hy
  exact hmem n ω0

/-- Conditional Jensen for the Lieb functional with a random `m`-measurable `H`
(in expectation). -/
lemma jensen_random (hL : ProbLieb) {d : ℕ} [NeZero d] {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K)
    {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] (hm : m ≤ mΩ) (Z : Ω → (Fin d → Fin d → ℝ))
    (hZi : Integrable Z μ) (hZs : ∀ᵐ ω ∂μ, Z ω ∈ sSet (d := d) c)
    (Hr : Ω → (Fin d → Fin d → ℝ)) (hHm : @Measurable Ω _ m _ Hr)
    (hHs : ∀ ω, Hr ω ∈ tset (d := d) K) :
    ∫ ω, ψL (Hr ω, Z ω) ∂μ ≤ ∫ ω, ψL (Hr ω, μ[Z | m] ω) ∂μ := by
  obtain ⟨s, hmem, htend, hsmeas, hfin, hfib⟩ := exists_approx (m := m) hK Hr hHm hHs
  have hCs : ∀ᵐ ω ∂μ, μ[Z | m] ω ∈ sSet (d := d) c :=
    (convex_sSet c).condExp_mem hm hZi (isClosed_sSet c) hZs
  have hCm : AEMeasurable (μ[Z | m]) μ :=
    (stronglyMeasurable_condExp.mono hm).measurable.aemeasurable
  have hsm : ∀ n, AEMeasurable (fun ω => s n ω) μ := fun n =>
    ((hsmeas n).mono hm le_rfl).aemeasurable
  have key : ∀ F : Ω → (Fin d → Fin d → ℝ), AEMeasurable F μ →
      (∀ᵐ ω ∂μ, F ω ∈ sSet (d := d) c) →
      Filter.Tendsto (fun n => ∫ ω, ψL (s n ω, F ω) ∂μ) Filter.atTop
        (nhds (∫ ω, ψL (Hr ω, F ω) ∂μ)) := by
    intro F hF hFs
    refine tendsto_integral_of_dominated_convergence (fun _ => Real.exp K * traceExp (0 : Matrix (Fin d) (Fin d) ℂ))
      (fun n => ?_) (integrable_const _)
      (fun n => hFs.mono fun ω h => ψL_bound hL hc (hmem n ω) h)
      (Filter.Eventually.of_forall fun ω => ?_)
    · have hp : AEMeasurable (fun ω => (s n ω, F ω)) μ := by
        first
          | exact (hsm n).prodMk hF
          | exact (hsm n).prod_mk hF
      exact aesm_ψL_comp hc hp hFs
    · have hcont : Continuous (fun h : Fin d → Fin d → ℝ => ψL (h, F ω)) :=
        show Continuous (fun h : Fin d → Fin d → ℝ => traceExp (cx h + matrixLog (cx (F ω)))) from
          continuous_traceExp.comp (continuous_cx.add continuous_const)
      exact (hcont.tendsto _).comp (htend ω)
  exact le_of_tendsto_of_tendsto' (key Z hZi.aemeasurable hZs) (key _ hCm hCs)
    fun n => (hfin n).elim fun T hT => integral_simple_le hL hc hm Z hZi hZs (s n) T hT.1 hT.2 (hfib n)

/-! ### Step 4a: one supermartingale step -/

/-- The identity as a real array. -/
def I0 {d : ℕ} : Fin d → Fin d → ℝ := fun i j => if i = j then 1 else 0

lemma cx_I0_sub {d : ℕ} (g : ℝ) (X : Fin d → Fin d → ℝ) :
    cx (I0 - g • X) = 1 - g • cx X := by
  ext i j
  by_cases h : i = j <;> simp [cx, I0, Matrix.one_apply, h, Complex.real_smul]

lemma sa_one {d : ℕ} : IsSelfAdjoint (1 : Matrix (Fin d) (Fin d) ℂ) := by
  first
    | exact isSelfAdjoint_one _
    | exact IsSelfAdjoint.one
    | simp [IsSelfAdjoint]

lemma matrixLog_le_sub_one {d : ℕ} {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.PosDef) :
    matrixLog M ≤ M - 1 := by
  have hsp := hM.isStrictlyPositive
  have h0 : 0 ≤ M := hsp.nonneg
  have hpos : ∀ x ∈ spectrum ℝ M, 0 < x := fun x hx =>
    lt_of_le_of_ne (spectrum_nonneg_of_nonneg h0 hx) (by
      rintro rfl; exact spectrum.zero_notMem ℝ hsp.isUnit hx)
  have hcont : ContinuousOn Real.log (spectrum ℝ M) :=
    Real.continuousOn_log.mono (fun x hx => (hpos x hx).ne')
  have e : cfc (fun x : ℝ => x - 1) M = M - 1 := by
    rw [cfc_sub (fun x : ℝ => x) (fun _ : ℝ => (1:ℝ)) M, cfc_id' ℝ M, cfc_const_one ℝ M]
  rw [← e, matrixLog]
  exact cfc_mono (fun x hx => Real.log_le_sub_one_of_pos (hpos x hx)) (hf := hcont)

lemma isClosed_tset {d : ℕ} (K : ℝ) : IsClosed (tset (d := d) K) :=
  IsClosed.inter (isClosed_eq (continuous_star.comp continuous_cx) continuous_cx)
    (isClosed_le continuous_cx continuous_const)

lemma exists_trunc {Ω : Type*} [m : MeasurableSpace Ω] {d : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (H : Ω → (Fin d → Fin d → ℝ)) (hH : Measurable H) :
    ∃ H' : Ω → (Fin d → Fin d → ℝ), Measurable H' ∧ (∀ ω, H' ω ∈ tset (d := d) K) ∧
      ∀ ω, H ω ∈ tset (d := d) K → H' ω = H ω := by
  classical
  refine ⟨fun ω => if H ω ∈ tset (d := d) K then H ω else 0,
    Measurable.ite (hH (isClosed_tset K).measurableSet) hH measurable_const,
    fun ω => ?_, fun ω h => if_pos h⟩
  by_cases h : H ω ∈ tset (d := d) K
  · dsimp only; rw [if_pos h]; exact h
  · dsimp only; rw [if_neg h]; exact zero_mem_tset hK

/-- One step of the trace-exponential supermartingale (in expectation). -/
lemma step_le (hL : ProbLieb) {d : ℕ} [NeZero d] {θ R K c g : ℝ} (hR : 0 < R) (hθ : 0 ≤ θ)
    (hK : 0 ≤ K) (hc : c = Real.exp (-θ * R)) (hg : g = (1 - c) / R)
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    (X : Ω → (Fin d → Fin d → ℝ)) (hXi : Integrable X μ)
    (hX : ∀ᵐ ω ∂μ, 0 ≤ cx (X ω) ∧ cx (X ω) ≤ algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) R)
    (H : Ω → (Fin d → Fin d → ℝ)) (hHm : @Measurable Ω _ m _ H)
    (hHK : ∀ᵐ ω ∂μ, H ω ∈ tset (d := d) K) :
    ∫ ω, traceExp (cx (H ω) + (-θ) • cx (X ω)) ∂μ ≤
      ∫ ω, traceExp (cx (H ω) + (-g) • cx (μ[X | m] ω)) ∂μ := by
  have hc0 : 0 < c := hc ▸ Real.exp_pos _
  have hg0 : 0 ≤ g := by
    rw [hg]
    refine div_nonneg ?_ hR.le
    rw [hc, sub_nonneg]
    exact Real.exp_le_one_iff.2 (by nlinarith)
  have hgR : g * R = 1 - c := by rw [hg]; field_simp
  obtain ⟨Z, hZdef⟩ : ∃ Z : Ω → (Fin d → Fin d → ℝ), Z = (fun _ => I0) - g • X := ⟨_, rfl⟩
  have hZω : ∀ ω, cx (Z ω) = 1 - g • cx (X ω) := fun ω => by
    rw [hZdef]; exact cx_I0_sub g (X ω)
  have hZi : Integrable Z μ := by rw [hZdef]; exact (integrable_const I0).sub (hXi.smul g)
  have hZs : ∀ᵐ ω ∂μ, Z ω ∈ sSet (d := d) c := by
    filter_upwards [hX] with ω h
    obtain ⟨h0, hXR⟩ := h
    have hsa : IsSelfAdjoint (cx (X ω)) := IsSelfAdjoint.of_nonneg h0
    refine ⟨?_, ?_, ?_⟩ <;> rw [hZω]
    · exact sa_one.sub ((IsSelfAdjoint.all g).smul hsa)
    · have h1 := smul_le_smul_real hXR hg0
      rw [Algebra.algebraMap_eq_smul_one, smul_smul, hgR, sub_smul, one_smul] at h1
      rw [Algebra.algebraMap_eq_smul_one]
      exact le_sub_comm.1 h1
    · have h1 := smul_le_smul_real h0 hg0
      rw [smul_zero] at h1
      exact sub_le_self _ h1
  have hZm : AEMeasurable Z μ := hZi.aemeasurable
  have hHae : AEMeasurable H μ := (hHm.mono hm le_rfl).aemeasurable
  have hCs : ∀ᵐ ω ∂μ, μ[Z | m] ω ∈ sSet (d := d) c :=
    (convex_sSet c).condExp_mem hm hZi (isClosed_sSet c) hZs
  have hXC : AEMeasurable (μ[X | m]) μ :=
    (stronglyMeasurable_condExp.mono hm).measurable.aemeasurable
  have hCX : ∀ᵐ ω ∂μ, μ[Z | m] ω = I0 - g • μ[X | m] ω := by
    rw [hZdef]
    filter_upwards [condExp_sub (integrable_const I0) (hXi.smul g) m,
      condExp_smul g X m] with ω h1 h2
    rw [h1, Pi.sub_apply, condExp_const hm, h2]
    rfl
  have hE1 : ∀ᵐ ω ∂μ, cx (μ[Z | m] ω) - 1 = (-g) • cx (μ[X | m] ω) := by
    filter_upwards [hCX] with ω hx
    rw [hx, cx_I0_sub, neg_smul]; abel
  -- (a) chord step
  have hA : ∀ᵐ ω ∂μ, traceExp (cx (H ω) + (-θ) • cx (X ω)) ≤ ψL (H ω, Z ω) := by
    filter_upwards [hX, hHK] with ω hXω hHω
    have hlog := neg_smul_le_log_one_sub (θ := θ) hR hXω.1 hXω.2
    rw [← hc, ← hg, ← hZω ω] at hlog
    have hsa : IsSelfAdjoint (cx (H ω) + (-θ) • cx (X ω)) :=
      hHω.1.add ((IsSelfAdjoint.all _).smul (IsSelfAdjoint.of_nonneg hXω.1))
    have h := traceExp_le_add hL hsa (sub_nonneg.2 hlog)
    have e : cx (H ω) + (-θ) • cx (X ω) + (matrixLog (cx (Z ω)) - (-θ) • cx (X ω)) =
        cx (H ω) + matrixLog (cx (Z ω)) := by abel
    rw [e] at h
    exact h
  -- (c) log step
  have hC : ∀ᵐ ω ∂μ, ψL (H ω, μ[Z | m] ω) ≤ traceExp (cx (H ω) + (-g) • cx (μ[X | m] ω)) := by
    filter_upwards [hCs, hE1, hHK] with ω hs he hHω
    have hlog := matrixLog_le_sub_one (posDef_of_sSet hc0 hs)
    rw [he] at hlog
    have hsa : IsSelfAdjoint (cx (H ω) + matrixLog (cx (μ[Z | m] ω))) :=
      hHω.1.add (matrixLog_isHermitian _)
    have h := traceExp_le_add hL hsa (sub_nonneg.2 hlog)
    have e : cx (H ω) + matrixLog (cx (μ[Z | m] ω)) +
        ((-g) • cx (μ[X | m] ω) - matrixLog (cx (μ[Z | m] ω))) =
        cx (H ω) + (-g) • cx (μ[X | m] ω) := by abel
    rw [e] at h
    exact h
  -- integrability
  have hp1 : AEMeasurable (fun ω => (H ω, Z ω)) μ := by
    first
      | exact hHae.prodMk hZm
      | exact hHae.prod_mk hZm
  have hψZ : Integrable (fun ω => ψL (H ω, Z ω)) μ :=
    Integrable.of_bound (aesm_ψL_comp hc0 hp1 hZs)
      (Real.exp K * traceExp (0 : Matrix (Fin d) (Fin d) ℂ))
      (by filter_upwards [hHK, hZs] with ω h1 h2; exact ψL_bound hL hc0 h1 h2)
  have hcont3 : Continuous (fun p : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ) =>
      traceExp (cx p.1 + (-g) • cx p.2)) :=
    continuous_traceExp.comp ((continuous_cx.comp continuous_fst).add
      ((continuous_cx.comp continuous_snd).const_smul (-g)))
  have hp3 : AEMeasurable (fun ω => (H ω, μ[X | m] ω)) μ := by
    first
      | exact hHae.prodMk hXC
      | exact hHae.prod_mk hXC
  have hI3 : Integrable (fun ω => traceExp (cx (H ω) + (-g) • cx (μ[X | m] ω))) μ := by
    refine Integrable.of_bound (hcont3.measurable.comp_aemeasurable hp3).aestronglyMeasurable
      (Real.exp K * traceExp (0 : Matrix (Fin d) (Fin d) ℂ)) ?_
    filter_upwards [hCs, hE1, hCX, hHK] with ω hs he hx hHω
    have hsaC : IsSelfAdjoint ((-g) • cx (μ[X | m] ω)) := by
      rw [← he]; exact hs.1.sub sa_one
    have hsa : IsSelfAdjoint (cx (H ω) + (-g) • cx (μ[X | m] ω)) := hHω.1.add hsaC
    have h1 := hs.2.2
    rw [hx, cx_I0_sub, sub_le_self_iff] at h1
    have h2 : (-g) • cx (μ[X | m] ω) ≤ 0 := by rw [neg_smul]; exact neg_nonpos.2 h1
    rw [Real.norm_of_nonneg (traceExp_nonneg hsa)]
    exact traceExp_le_of_le hL hsa (add_le_of_le_of_nonpos hHω.2 h2)
  -- (b) Jensen with a truncated `H`
  obtain ⟨H', hH'm, hH'mem, hH'eq⟩ := exists_trunc (m := m) hK H hHm
  have hHH' : ∀ᵐ ω ∂μ, H' ω = H ω := hHK.mono fun ω h => hH'eq ω h
  have hJ := jensen_random hL hc0 hK hm Z hZi hZs H' hH'm hH'mem
  have hJ' : ∫ ω, ψL (H ω, Z ω) ∂μ ≤ ∫ ω, ψL (H ω, μ[Z | m] ω) ∂μ := by
    have e1 : ∫ ω, ψL (H' ω, Z ω) ∂μ = ∫ ω, ψL (H ω, Z ω) ∂μ :=
      integral_congr_ae (hHH'.mono fun ω h => by simp only [h])
    have e2 : ∫ ω, ψL (H' ω, μ[Z | m] ω) ∂μ = ∫ ω, ψL (H ω, μ[Z | m] ω) ∂μ :=
      integral_congr_ae (hHH'.mono fun ω h => by simp only [h])
    rw [← e1, ← e2]; exact hJ
  calc ∫ ω, traceExp (cx (H ω) + (-θ) • cx (X ω)) ∂μ ≤ ∫ ω, ψL (H ω, Z ω) ∂μ :=
        integral_mono_of_nonneg (by
          filter_upwards [hX, hHK] with ω h1 h2
          exact traceExp_nonneg (h2.1.add ((IsSelfAdjoint.all _).smul
            (IsSelfAdjoint.of_nonneg h1.1)))) hψZ hA
    _ ≤ ∫ ω, ψL (H ω, μ[Z | m] ω) ∂μ := hJ'
    _ ≤ _ := integral_mono_of_nonneg (by
          filter_upwards [hHK] with ω h
          exact φL_nonneg h.1 _) hI3 hC

/-! ### Step 4b glue: Rayleigh quotients, `lambdaMin`, and `log traceExp` -/

lemma le_log_traceExp {d : ℕ} {M : Matrix (Fin d) (Fin d) ℂ} (hM : IsSelfAdjoint M) :
    M ≤ algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) (Real.log (traceExp M)) := by
  rw [le_algebraMap_iff_spectrum_le hM]
  intro x hx
  have h0 : (0 : Matrix (Fin d) (Fin d) ℂ) ≤ NormedSpace.exp M := IsSelfAdjoint.exp_nonneg hM
  have hpsd : (NormedSpace.exp M).PosSemidef := Matrix.nonneg_iff_posSemidef.1 h0
  have hxA : Real.exp x ∈ spectrum ℝ (NormedSpace.exp M) := by
    rw [← CFC.real_exp_eq_normedSpace_exp hM, cfc_map_spectrum Real.exp M]
    exact ⟨x, hx, rfl⟩
  rw [hpsd.1.spectrum_real_eq_range_eigenvalues] at hxA
  obtain ⟨j, hj⟩ := hxA
  have htr : traceExp M = ∑ i, hpsd.1.eigenvalues i := by
    unfold traceExp matrixExp
    rw [hpsd.1.trace_eq_sum_eigenvalues, Complex.re_sum]
    simp
  have hle : Real.exp x ≤ traceExp M := by
    rw [htr, ← hj]
    exact Finset.single_le_sum (fun i _ => hpsd.eigenvalues_nonneg i) (Finset.mem_univ j)
  rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos x) hle)]
  exact hle

lemma rayleigh_le_log_traceExp {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : IsSelfAdjoint (cx A)) (v : Fin d → ℝ) (hv : v ⬝ᵥ v = 1) :
    v ⬝ᵥ (A.mulVec v) ≤ Real.log (traceExp (cx A)) := by
  set s := Real.log (traceExp (cx A))
  have hP : (algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) s - cx A).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.1 (sub_nonneg.2 (le_log_traceExp hA))
  have h2 := hP.dotProduct_mulVec_nonneg (fun i => (v i : ℂ))
  have e : star (fun i => (v i : ℂ)) ⬝ᵥ
      Matrix.mulVec (algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) s - cx A) (fun i => (v i : ℂ)) =
      ((s * (v ⬝ᵥ v) - v ⬝ᵥ (A.mulVec v) : ℝ) : ℂ) := by
    have hof : ∀ i j, (Matrix.of A : Matrix (Fin d) (Fin d) ℝ) i j = A i j := fun _ _ => rfl
    simp [dotProduct, Matrix.mulVec, cx, Matrix.sub_apply, Algebra.algebraMap_eq_smul_one,
      Matrix.one_apply, Finset.mul_sum, Finset.sum_sub_distrib, sub_mul, mul_sub,
      Complex.ofReal_sum, Complex.ofReal_mul, Complex.real_smul, mul_comm, mul_left_comm,
      mul_assoc, hof]
    try (refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
         simp only [hof]; ring)
  rw [e] at h2
  have h3 := (Complex.le_def.1 h2).1
  simp only [Complex.zero_re, Complex.ofReal_re] at h3
  rw [hv, mul_one] at h3
  linarith

lemma abs_rayleigh_le {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ)
    (hv : v ⬝ᵥ v = 1) : |v ⬝ᵥ (A.mulVec v)| ≤ ∑ i, ∑ j, |A i j| := by
  have hvi : ∀ i, |v i| ≤ 1 := by
    intro i
    have h : v i * v i ≤ v ⬝ᵥ v :=
      Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg _)
        (Finset.mem_univ i)
    rw [hv] at h
    exact abs_le_one_iff_mul_self_le_one.2 h
  simp only [dotProduct, Matrix.mulVec]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  calc |v i| * |∑ j, A i j * v j| ≤ 1 * ∑ j, |A i j| := by
        refine mul_le_mul (hvi i) ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j _ => ?_)) (abs_nonneg _) zero_le_one
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hvi j)
    _ = ∑ j, |A i j| := one_mul _

open MostlyExplorationFree.GreedyBandit in
lemma lambdaMin_le_rayleigh {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ)
    (hv : v ⬝ᵥ v = 1) : lambdaMin A ≤ v ⬝ᵥ (A.mulVec v) := by
  have hb : BddBelow (Set.range fun w : {w : Fin d → ℝ // w ⬝ᵥ w = 1} => w.1 ⬝ᵥ (A.mulVec w.1)) :=
    ⟨-(∑ i, ∑ j, |A i j|), by
      rintro _ ⟨w, rfl⟩
      exact neg_le_of_abs_le (abs_rayleigh_le A w.1 w.2)⟩
  exact ciInf_le hb ⟨v, hv⟩

open MostlyExplorationFree.GreedyBandit in
lemma exists_rayleigh_lt {d : ℕ} (hd : 1 ≤ d) (A : Matrix (Fin d) (Fin d) ℝ) {t : ℝ}
    (ht : lambdaMin A < t) : ∃ v : Fin d → ℝ, v ⬝ᵥ v = 1 ∧ v ⬝ᵥ (A.mulVec v) < t := by
  have : Nonempty {w : Fin d → ℝ // w ⬝ᵥ w = 1} :=
    ⟨⟨Pi.single ⟨0, hd⟩ 1, by simp [dotProduct, Pi.single_apply]⟩⟩
  obtain ⟨w, hw⟩ := exists_lt_of_ciInf_lt ht
  exact ⟨w.1, w.2, hw⟩



/-! ### Step 4c: real/complex glue, conditional expectations, assembly -/

open scoped Matrix

lemma cx_add {d : ℕ} (Z1 Z2 : Fin d → Fin d → ℝ) : cx (Z1 + Z2) = cx Z1 + cx Z2 := by
  ext i j; simp [cx]

lemma cx_smul {d : ℕ} (a : ℝ) (Z : Fin d → Fin d → ℝ) : cx (a • Z) = a • cx Z := by
  ext i j; simp [cx]

lemma cx_sum {d : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin d → Fin d → ℝ) :
    cx (∑ j ∈ s, f j) = ∑ j ∈ s, cx (f j) := by
  ext i k; simp [cx, Finset.sum_apply, Matrix.sum_apply]

/-- The closed convex set `0 ≤ Z ≤ R` (Loewner order, complexified). -/
def bSet {d : ℕ} (R : ℝ) : Set (Fin d → Fin d → ℝ) :=
  {Z | 0 ≤ cx Z ∧ cx Z ≤ algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) R}

lemma isClosed_bSet {d : ℕ} (R : ℝ) : IsClosed (bSet (d := d) R) :=
  (isClosed_le continuous_const continuous_cx).inter (isClosed_le continuous_cx continuous_const)

lemma convex_bSet {d : ℕ} (R : ℝ) : Convex ℝ (bSet (d := d) R) := by
  intro Z1 h1 Z2 h2 a b ha hb hab
  refine ⟨?_, ?_⟩ <;> rw [cx_add_smul]
  · have := add_le_add (smul_le_smul_real h1.1 ha) (smul_le_smul_real h2.1 hb)
    simpa using this
  · have e : algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) R =
        a • algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) R +
          b • algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) R := by
      rw [← add_smul, hab, one_smul]
    rw [e]
    exact add_le_add (smul_le_smul_real h1.2 ha) (smul_le_smul_real h2.2 hb)

lemma quad_add {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (x y : Fin d → ℝ) :
    (x + y) ⬝ᵥ (A *ᵥ (x + y)) =
      x ⬝ᵥ (A *ᵥ x) + x ⬝ᵥ (A *ᵥ y) + y ⬝ᵥ (A *ᵥ x) + y ⬝ᵥ (A *ᵥ y) := by
  simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct]; ring

lemma quad_sub {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (x y : Fin d → ℝ) :
    (x - y) ⬝ᵥ (A *ᵥ (x - y)) =
      x ⬝ᵥ (A *ᵥ x) - x ⬝ᵥ (A *ᵥ y) - y ⬝ᵥ (A *ᵥ x) + y ⬝ᵥ (A *ᵥ y) := by
  simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]; ring

lemma single_quad {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (a b : Fin d) :
    Pi.single a (1 : ℝ) ⬝ᵥ (A *ᵥ Pi.single b 1) = A a b := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

lemma entry_abs_le {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hs : ∀ i j, A j i = A i j) {R : ℝ}
    (h0 : ∀ v, 0 ≤ v ⬝ᵥ (A *ᵥ v)) (hdiag : ∀ i, A i i ≤ R) (a b : Fin d) : |A a b| ≤ R := by
  have h1 := h0 (Pi.single a 1 + Pi.single b 1)
  have h2 := h0 (Pi.single a 1 - Pi.single b 1)
  rw [quad_add] at h1
  rw [quad_sub] at h2
  simp only [single_quad] at h1 h2
  rw [hs a b] at h1 h2
  have ha := hdiag a
  have hb := hdiag b
  rw [abs_le]; constructor <;> linarith

open MostlyExplorationFree.GreedyBandit in
lemma rayleigh_le_lambdaMax {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ)
    (hv : v ⬝ᵥ v = 1) : v ⬝ᵥ (A.mulVec v) ≤ lambdaMax A := by
  have hb : BddAbove (Set.range fun w : {w : Fin d → ℝ // w ⬝ᵥ w = 1} => w.1 ⬝ᵥ (A.mulVec w.1)) :=
    ⟨∑ i, ∑ j, |A i j|, by
      rintro _ ⟨w, rfl⟩
      exact le_of_abs_le (abs_rayleigh_le A w.1 w.2)⟩
  exact le_ciSup hb ⟨v, hv⟩

open MostlyExplorationFree.GreedyBandit in
lemma quad_le {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) {R : ℝ}
    (hR : lambdaMax A ≤ R) (v : Fin d → ℝ) : v ⬝ᵥ (A *ᵥ v) ≤ R * (v ⬝ᵥ v) := by
  have hnn : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  rcases hnn.eq_or_lt with h | h
  · have : v = 0 := dotProduct_self_eq_zero.1 h.symm
    subst this; simp
  · obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (v ⬝ᵥ v) := ⟨_, rfl⟩
    have hs0 : 0 < s := hs ▸ Real.sqrt_pos.2 h
    have hss : s * s = v ⬝ᵥ v := hs ▸ Real.mul_self_sqrt hnn
    have hu : (s⁻¹ • v) ⬝ᵥ (s⁻¹ • v) = 1 := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hss]; field_simp
    have h1 := (rayleigh_le_lambdaMax A _ hu).trans hR
    rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h1
    rw [← hss]
    have e : s⁻¹ * (s⁻¹ * (v ⬝ᵥ (A *ᵥ v))) = (v ⬝ᵥ (A *ᵥ v)) / (s * s) := by
      rw [div_eq_mul_inv, mul_inv]; ring
    rw [e, div_le_iff₀ (by positivity)] at h1
    exact h1

lemma cx_nonneg {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hs : ∀ i j, A j i = A i j)
    (h0 : ∀ v : Fin d → ℝ, 0 ≤ v ⬝ᵥ (A *ᵥ v)) : 0 ≤ cx A := by
  rw [Matrix.nonneg_iff_posSemidef]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun w => ?_
  · ext i j; simp [cx, Matrix.conjTranspose_apply]; exact hs i j
  · have hre : (star w ⬝ᵥ (cx A *ᵥ w)).re = (fun i => (w i).re) ⬝ᵥ (A *ᵥ fun i => (w i).re) +
        (fun i => (w i).im) ⬝ᵥ (A *ᵥ fun i => (w i).im) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.re_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp [cx, Complex.mul_re, Complex.mul_im] <;> (try rw [show (Matrix.of A) i j = A i j from rfl]) <;> ring
    have him : (star w ⬝ᵥ (cx A *ᵥ w)).im =
        ∑ i, ∑ j, ((w i).re * (A i j * (w j).im) - (w i).im * (A i j * (w j).re)) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.im_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp [cx, Complex.mul_re, Complex.mul_im] <;> (try rw [show (Matrix.of A) i j = A i j from rfl]) <;> ring
    have key : ∑ i, ∑ j, (w i).im * (A i j * (w j).re) =
        ∑ i, ∑ j, (w i).re * (A i j * (w j).im) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hs]; ring
    rw [Complex.le_def]
    refine ⟨?_, ?_⟩
    · rw [hre, Complex.zero_re]; exact add_nonneg (h0 _) (h0 _)
    · rw [him, Complex.zero_im]
      simp only [Finset.sum_sub_distrib, key, sub_self]

open MostlyExplorationFree.GreedyBandit in
lemma mem_bSet {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosSemidef) {R : ℝ}
    (hR : lambdaMax A ≤ R) : (A : Fin d → Fin d → ℝ) ∈ bSet (d := d) R ∧ ∀ a b, |A a b| ≤ R := by
  have hs : ∀ i j, A j i = A i j := fun i j => by
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hA.1 i) j
  have h0 : ∀ v, 0 ≤ v ⬝ᵥ (A *ᵥ v) := fun v => by simpa using hA.dotProduct_mulVec_nonneg v
  refine ⟨⟨cx_nonneg A hs h0, ?_⟩, entry_abs_le A hs h0 (fun i => ?_)⟩
  · rw [← sub_nonneg]
    have e : algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) R - cx A =
        cx ((R • 1 - A : Matrix (Fin d) (Fin d) ℝ)) := by
      ext i j
      rw [Matrix.sub_apply, show cx A i j = (A i j : ℂ) from rfl,
        show cx ((R • 1 - A : Matrix (Fin d) (Fin d) ℝ)) i j =
          ((R • 1 - A : Matrix (Fin d) (Fin d) ℝ) i j : ℂ) from rfl]
      by_cases h : i = j <;> simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply, h]
    rw [e]
    refine cx_nonneg _ (fun i j => ?_) (fun v => ?_)
    · by_cases h : i = j
      · subst h; rfl
      · simp [Matrix.sub_apply, Matrix.one_apply, h, Ne.symm h, hs i j]
    · have := quad_le A hR v
      have e2 : v ⬝ᵥ ((R • 1 - A : Matrix (Fin d) (Fin d) ℝ) *ᵥ v) =
          R * (v ⬝ᵥ v) - v ⬝ᵥ (A *ᵥ v) := by
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
          dotProduct_smul, smul_eq_mul]
      rw [e2]; linarith
  · have := quad_le A hR (Pi.single i 1)
    rw [single_quad] at this
    simpa [dotProduct, Pi.single_apply] using this

lemma alg_le_alg {d : ℕ} {a b : ℝ} (h : a ≤ b) :
    algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) a ≤ algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) b := by
  rw [← sub_nonneg, ← map_sub, Algebra.algebraMap_eq_smul_one]
  exact Matrix.nonneg_iff_posSemidef.2 (Matrix.PosSemidef.one.smul (sub_nonneg.2 h))

lemma sum_bSet {d : ℕ} {R : ℝ} (s : Finset ℕ) (f : ℕ → Fin d → Fin d → ℝ)
    (hf : ∀ j ∈ s, f j ∈ bSet (d := d) R) :
    0 ≤ cx (∑ j ∈ s, f j) ∧
      cx (∑ j ∈ s, f j) ≤ algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) (s.card * R) := by
  rw [cx_sum]
  refine ⟨Finset.sum_nonneg fun j hj => (hf j hj).1, ?_⟩
  calc ∑ j ∈ s, cx (f j) ≤ ∑ j ∈ s, algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) R :=
        Finset.sum_le_sum fun j hj => (hf j hj).2
    _ = _ := by rw [Finset.sum_const, ← map_nsmul, nsmul_eq_mul]

lemma mem_tset_of {d : ℕ} {θ g R : ℝ} (hθ : 0 ≤ θ) (hg : 0 ≤ g) {Y W : Fin d → Fin d → ℝ}
    {m n : ℕ} (hY : 0 ≤ cx Y) (hW0 : 0 ≤ cx W)
    (hW : cx W ≤ algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) (m * R)) (hmn : m ≤ n) (hR : 0 ≤ R) :
    (-θ) • Y + g • W ∈ tset (d := d) (g * (n * R)) := by
  have e : cx ((-θ) • Y + g • W) = g • cx W - θ • cx Y := by
    rw [cx_add_smul, neg_smul]; abel
  refine ⟨?_, ?_⟩ <;> rw [e]
  · exact ((IsSelfAdjoint.all g).smul (IsSelfAdjoint.of_nonneg hW0)).sub
      ((IsSelfAdjoint.all θ).smul (IsSelfAdjoint.of_nonneg hY))
  · have h1 : 0 ≤ θ • cx Y := by simpa using smul_le_smul_real hY hθ
    have h2 := smul_le_smul_real hW hg
    have h3 : g • algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) (m * R) ≤
        algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) (g * (n * R)) := by
      rw [Algebra.smul_def, ← map_mul]
      exact alg_le_alg (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hmn) hR) hg)
    calc g • cx W - θ • cx Y ≤ g • cx W := sub_le_self _ h1
      _ ≤ _ := h2.trans h3

noncomputable def Ysum {Ω : Type*} {d : ℕ} (Xp : ℕ → Ω → (Fin d → Fin d → ℝ)) (k : ℕ)
    (ω : Ω) : Fin d → Fin d → ℝ :=
  ∑ j ∈ Finset.Icc 1 k, Xp j ω

noncomputable def Wsum {Ω : Type*} {mΩ : MeasurableSpace Ω} {d : ℕ} (ℱ : Filtration ℕ mΩ)
    (P : Measure Ω) (Xp : ℕ → Ω → (Fin d → Fin d → ℝ)) (k : ℕ) (ω : Ω) : Fin d → Fin d → ℝ :=
  ∑ j ∈ Finset.Icc 1 k, P[Xp j | ℱ (j - 1)] ω

lemma good_ae {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (ℱ : Filtration ℕ mΩ) (n : ℕ) (Xp : ℕ → Ω → (Fin d → Fin d → ℝ)) {R : ℝ}
    (hXi : ∀ k ∈ Finset.Icc 1 n, Integrable (Xp k) P)
    (hXb : ∀ k ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, Xp k ω ∈ bSet (d := d) R) :
    ∀ᵐ ω ∂P, ∀ k ∈ Finset.Icc 1 n,
      Xp k ω ∈ bSet (d := d) R ∧ P[Xp k | ℱ (k - 1)] ω ∈ bSet (d := d) R := by
  have h : ∀ k : ℕ, ∀ᵐ ω ∂P, k ∈ Finset.Icc 1 n →
      (Xp k ω ∈ bSet (d := d) R ∧ P[Xp k | ℱ (k - 1)] ω ∈ bSet (d := d) R) := by
    intro k
    by_cases hk : k ∈ Finset.Icc 1 n
    · filter_upwards [hXb k hk, (convex_bSet R).condExp_mem (ℱ.le (k - 1)) (hXi k hk)
        (isClosed_bSet R) (hXb k hk)] with ω h1 h2 _
      exact ⟨h1, h2⟩
    · exact Filter.Eventually.of_forall fun ω h => absurd h hk
  filter_upwards [ae_all_iff.2 h] with ω hω k hk using hω k hk

lemma good_tset {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {d : ℕ}
    (ℱ : Filtration ℕ mΩ) {n : ℕ} {Xp : ℕ → Ω → (Fin d → Fin d → ℝ)} {R θ g : ℝ}
    (hR : 0 ≤ R) (hθ : 0 ≤ θ) (hg : 0 ≤ g) {ω : Ω}
    (hω : ∀ k ∈ Finset.Icc 1 n,
      Xp k ω ∈ bSet (d := d) R ∧ P[Xp k | ℱ (k - 1)] ω ∈ bSet (d := d) R)
    {k k' : ℕ} (hk : k ≤ n) (hk' : k' ≤ n) :
    (-θ) • Ysum Xp k ω + g • Wsum ℱ P Xp k' ω ∈ tset (d := d) (g * (n * R)) := by
  have hY := sum_bSet (Finset.Icc 1 k) (fun j => Xp j ω)
    fun j hj => (hω j (Finset.Icc_subset_Icc_right hk hj)).1
  have hW := sum_bSet (Finset.Icc 1 k') (fun j => P[Xp j | ℱ (j - 1)] ω)
    fun j hj => (hω j (Finset.Icc_subset_Icc_right hk' hj)).2
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hW
  exact mem_tset_of hθ hg hY.1 hW.1 hW.2 hk' hR

lemma traceExp_zero' {d : ℕ} : traceExp (0 : Matrix (Fin d) (Fin d) ℂ) = d := by
  simp [traceExp, matrixExp]

lemma chain_le (hL : ProbLieb) {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {d : ℕ} [NeZero d] (ℱ : Filtration ℕ mΩ) (n : ℕ)
    (Xp : ℕ → Ω → (Fin d → Fin d → ℝ)) {R θ g : ℝ} (hR : 0 < R) (hθ : 0 ≤ θ)
    (hg : g = (1 - Real.exp (-θ * R)) / R)
    (hXm : ∀ k ∈ Finset.Icc 1 n, Measurable[ℱ k] (Xp k))
    (hXi : ∀ k ∈ Finset.Icc 1 n, Integrable (Xp k) P)
    (hXb : ∀ k ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, Xp k ω ∈ bSet (d := d) R) :
    ∀ k ≤ n, ∫ ω, traceExp (cx ((-θ) • Ysum Xp k ω + g • Wsum ℱ P Xp k ω)) ∂P ≤ d := by
  have hg0 : 0 ≤ g := by
    rw [hg]
    exact div_nonneg (sub_nonneg.2 (Real.exp_le_one_iff.2 (by nlinarith))) hR.le
  have hgood := good_ae ℱ n Xp hXi hXb
  intro k
  induction k with
  | zero =>
    intro _
    have hI : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
    have e0 : ∀ ω, (-θ) • Ysum Xp 0 ω + g • Wsum ℱ P Xp 0 ω = 0 := fun ω => by
      simp [Ysum, Wsum, hI]
    simp only [e0, cx_zero, traceExp_zero']
    simp
  | succ k ih =>
    intro hk
    have hk1 : k + 1 ∈ Finset.Icc 1 n := Finset.mem_Icc.2 ⟨by omega, hk⟩
    refine le_trans ?_ (ih (by omega))
    have hYs : ∀ ω, Ysum Xp (k + 1) ω = Ysum Xp k ω + Xp (k + 1) ω := fun ω => by
      simp only [Ysum]; exact Finset.sum_Icc_succ_top (by omega) _
    have hWs : ∀ ω, Wsum ℱ P Xp (k + 1) ω = Wsum ℱ P Xp k ω + P[Xp (k + 1) | ℱ k] ω :=
      fun ω => by
        simp only [Wsum]; rw [Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]
    have hY : Measurable[ℱ k] (fun ω => Ysum Xp k ω) := by
      simp only [Ysum]
      refine Finset.measurable_sum _ fun j hj => ?_
      have hj' := Finset.mem_Icc.1 hj
      exact (hXm j (Finset.mem_Icc.2 ⟨hj'.1, by omega⟩)).mono (ℱ.mono hj'.2) le_rfl
    have hWm : Measurable[ℱ k] (fun ω => Wsum ℱ P Xp (k + 1) ω) := by
      simp only [Wsum]
      refine Finset.measurable_sum _ fun j hj => ?_
      have hj' := Finset.mem_Icc.1 hj
      exact stronglyMeasurable_condExp.measurable.mono (ℱ.mono (by omega)) le_rfl
    have hHm : Measurable[ℱ k]
        (fun ω => (-θ) • Ysum Xp k ω + g • Wsum ℱ P Xp (k + 1) ω) :=
      (hY.const_smul (-θ)).add (hWm.const_smul g)
    have hHK : ∀ᵐ ω ∂P, (-θ) • Ysum Xp k ω + g • Wsum ℱ P Xp (k + 1) ω ∈
        tset (d := d) (g * (n * R)) := by
      filter_upwards [hgood] with ω hω using good_tset ℱ hR.le hθ hg0 hω (by omega) hk
    have key := step_le hL hR hθ (K := g * (n * R)) (c := Real.exp (-θ * R)) (g := g)
      (by positivity) rfl hg (ℱ.le k) (Xp (k + 1)) (hXi _ hk1) (hXb _ hk1)
      (fun ω => (-θ) • Ysum Xp k ω + g • Wsum ℱ P Xp (k + 1) ω) hHm hHK
    beta_reduce at key
    have e1 : ∀ ω, cx ((-θ) • Ysum Xp (k + 1) ω + g • Wsum ℱ P Xp (k + 1) ω) =
        cx ((-θ) • Ysum Xp k ω + g • Wsum ℱ P Xp (k + 1) ω) + (-θ) • cx (Xp (k + 1) ω) := by
      intro ω; rw [← cx_smul, ← cx_add]; congr 1; rw [hYs ω, smul_add]; abel
    have e2 : ∀ ω, cx ((-θ) • Ysum Xp k ω + g • Wsum ℱ P Xp k ω) =
        cx ((-θ) • Ysum Xp k ω + g • Wsum ℱ P Xp (k + 1) ω) +
          (-g) • cx (P[Xp (k + 1) | ℱ k] ω) := by
      intro ω; rw [← cx_smul, ← cx_add]; congr 1; rw [hWs ω]; simp only [smul_add, neg_smul]; abel
    simp only [e1, e2]
    exact key

lemma exp_le_traceExp {d : ℕ} {M : Matrix (Fin d) (Fin d) ℂ} (hM : IsSelfAdjoint M) {x : ℝ}
    (hx : x ∈ spectrum ℝ M) : Real.exp x ≤ traceExp M := by
  have h0 : (0 : Matrix (Fin d) (Fin d) ℂ) ≤ NormedSpace.exp M := IsSelfAdjoint.exp_nonneg hM
  have hpsd : (NormedSpace.exp M).PosSemidef := Matrix.nonneg_iff_posSemidef.1 h0
  have hxA : Real.exp x ∈ spectrum ℝ (NormedSpace.exp M) := by
    rw [← CFC.real_exp_eq_normedSpace_exp hM, cfc_map_spectrum Real.exp M]
    exact ⟨x, hx, rfl⟩
  rw [hpsd.1.spectrum_real_eq_range_eigenvalues] at hxA
  obtain ⟨j, hj⟩ := hxA
  have htr : traceExp M = ∑ i, hpsd.1.eigenvalues i := by
    unfold traceExp matrixExp
    rw [hpsd.1.trace_eq_sum_eigenvalues, Complex.re_sum]
    simp
  rw [htr, ← hj]
  exact Finset.single_le_sum (fun i _ => hpsd.eigenvalues_nonneg i) (Finset.mem_univ j)

lemma traceExp_pos {d : ℕ} [NeZero d] {M : Matrix (Fin d) (Fin d) ℂ} (hM : IsSelfAdjoint M) :
    0 < traceExp M :=
  (Real.exp_pos _).trans_le
    (exp_le_traceExp hM ((show M.IsHermitian from hM).eigenvalues_mem_spectrum_real 0))

open MostlyExplorationFree.GreedyBandit in
lemma final_bound {d : ℕ} (hd : 1 ≤ d) {θ g mu γ ε : ℝ} (hθ : 0 < θ) (hg : 0 ≤ g) (hε : 0 < ε)
    (Y W : Fin d → Fin d → ℝ) (hsa : IsSelfAdjoint (cx ((-θ) • Y + g • W)))
    (hY : lambdaMin (Matrix.of Y) ≤ (1 - γ) * mu) (hW : mu ≤ lambdaMin (Matrix.of W)) :
    -θ * ((1 - γ) * mu) + g * mu ≤ Real.log (traceExp (cx ((-θ) • Y + g • W))) + ε := by
  obtain ⟨v, hv, hvY⟩ := exists_rayleigh_lt hd (Matrix.of Y) (t := (1 - γ) * mu + ε / θ)
    (by linarith [div_pos hε hθ])
  have hvW := hW.trans (lambdaMin_le_rayleigh (Matrix.of W) v hv)
  have hR : v ⬝ᵥ ((Matrix.of ((-θ) • Y + g • W)).mulVec v) ≤
      Real.log (traceExp (cx ((-θ) • Y + g • W))) := rayleigh_le_log_traceExp hsa v hv
  have e : v ⬝ᵥ ((Matrix.of ((-θ) • Y + g • W)).mulVec v) =
      -θ * (v ⬝ᵥ ((Matrix.of Y).mulVec v)) + g * (v ⬝ᵥ ((Matrix.of W).mulVec v)) := by
    rw [← Matrix.of_add_of, ← Matrix.smul_of, ← Matrix.smul_of, Matrix.add_mulVec,
      Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, dotProduct_smul,
      smul_eq_mul, smul_eq_mul]
  rw [e] at hR
  have h1 := mul_le_mul_of_nonneg_left hvY.le hθ.le
  have h2 : θ * (ε / θ) = ε := by field_simp
  rw [mul_add, h2] at h1
  have h3 := mul_le_mul_of_nonneg_left hvW hg
  nlinarith

lemma condExp_entry {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω} {d : ℕ}
    (X : Ω → (Fin d → Fin d → ℝ)) (hX : Integrable X P) (a b : Fin d) :
    ∀ᵐ ω ∂P, P[X | m] ω a b = P[fun ω => X ω a b | m] ω := by
  let T : (Fin d → Fin d → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj b).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => Fin d → ℝ) a)
  have h := T.comp_condExp_comm (m := m) hX
  have e : (⇑T ∘ X) = fun ω => X ω a b := rfl
  rw [e] at h
  filter_upwards [h] with ω hω
  exact hω

open MostlyExplorationFree.GreedyBandit in
theorem main (hL : ProbLieb) {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℕ} (hd : 1 ≤ d) (ℱ : Filtration ℕ mΩ) (n : ℕ)
    (Xp : ℕ → Ω → (Fin d → Fin d → ℝ)) (R : ℝ) (hR : 0 < R)
    (hadapted : ∀ k ∈ Finset.Icc 1 n, ∀ a b, StronglyMeasurable[ℱ k] (fun ω => Xp k ω a b))
    (hpsd : ∀ k ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, Matrix.PosSemidef (Xp k ω))
    (hmax : ∀ k ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, lambdaMax (Xp k ω) ≤ R)
    (mu γ : ℝ) (hmu : 0 ≤ mu) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    (P {ω | lambdaMin (∑ k ∈ Finset.Icc 1 n, Xp k ω) ≤ (1 - γ) * mu ∧
        mu ≤ lambdaMin (∑ k ∈ Finset.Icc 1 n, condExpMatrix (ℱ (k - 1)) P (Xp k) ω)}).toReal
      ≤ d * (Real.exp (-γ) / (1 - γ) ^ (1 - γ)) ^ (mu / R) := by
  haveI : NeZero d := ⟨by omega⟩
  rcases hγ0.eq_or_lt with hγ | hγ
  · subst hγ
    simp only [neg_zero, Real.exp_zero, sub_zero, Real.one_rpow, div_one, mul_one]
    refine le_trans (ENNReal.toReal_le_of_le_ofReal zero_le_one ?_) (by exact_mod_cast hd)
    rw [ENNReal.ofReal_one]; exact prob_le_one
  have h1γ : 0 < 1 - γ := by linarith
  have hlog : Real.log (1 - γ) < 0 := Real.log_neg h1γ (by linarith)
  obtain ⟨θ, hθdef⟩ : ∃ θ, θ = -Real.log (1 - γ) / R := ⟨_, rfl⟩
  have hθ : 0 < θ := hθdef ▸ div_pos (by linarith) hR
  have hc : Real.exp (-θ * R) = 1 - γ := by
    rw [hθdef, show -(-Real.log (1 - γ) / R) * R = Real.log (1 - γ) by field_simp]
    exact Real.exp_log h1γ
  obtain ⟨g, hgdef⟩ : ∃ g, g = (1 - Real.exp (-θ * R)) / R := ⟨_, rfl⟩
  have hg : g = γ / R := by rw [hgdef, hc]; ring
  have hg0 : 0 ≤ g := hg ▸ div_nonneg hγ.le hR.le
  have hB : ∀ k ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, Xp k ω ∈ bSet (d := d) R ∧ ∀ a b, |Xp k ω a b| ≤ R :=
    fun k hk => by
      filter_upwards [hpsd k hk, hmax k hk] with ω h1 h2 using mem_bSet h1 h2
  have hXb : ∀ k ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, Xp k ω ∈ bSet (d := d) R := fun k hk => by
    filter_upwards [hB k hk] with ω h using h.1
  have hXm : ∀ k ∈ Finset.Icc 1 n, Measurable[ℱ k] (Xp k) := fun k hk => by
    letI : MeasurableSpace Ω := ℱ k
    exact measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => (hadapted k hk a b).measurable
  have hXi : ∀ k ∈ Finset.Icc 1 n, Integrable (Xp k) P := fun k hk => by
    refine integrable_pi_iff.2 fun a => integrable_pi_iff.2 fun b => ?_
    refine Integrable.of_bound ((hadapted k hk a b).mono (ℱ.le k)).aestronglyMeasurable R ?_
    filter_upwards [hB k hk] with ω h
    simpa [Real.norm_eq_abs] using h.2 a b
  have hgood := good_ae ℱ n Xp hXi hXb
  have hSn := chain_le hL ℱ n Xp hR hθ.le hgdef hXm hXi hXb n le_rfl
  obtain ⟨S, hSdef⟩ : ∃ S : Ω → ℝ,
      S = fun ω => traceExp (cx ((-θ) • Ysum Xp n ω + g • Wsum ℱ P Xp n ω)) := ⟨_, rfl⟩
  have hSn' : ∫ ω, S ω ∂P ≤ d := by rw [hSdef]; exact hSn
  have hFm : Measurable (fun ω => (-θ) • Ysum Xp n ω + g • Wsum ℱ P Xp n ω) := by
    have hY : Measurable (fun ω => Ysum Xp n ω) := by
      simp only [Ysum]
      exact Finset.measurable_sum _ fun j hj => (hXm j hj).mono (ℱ.le j) le_rfl
    have hW : Measurable (fun ω => Wsum ℱ P Xp n ω) := by
      simp only [Wsum]
      exact Finset.measurable_sum _ fun j hj =>
        stronglyMeasurable_condExp.measurable.mono (ℱ.le _) le_rfl
    exact (hY.const_smul (-θ)).add (hW.const_smul g)
  have hS0 : 0 ≤ᵐ[P] S := by
    filter_upwards [hgood] with ω hω
    rw [hSdef]
    exact traceExp_nonneg (good_tset ℱ hR.le hθ.le hg0 hω (le_refl n) (le_refl n)).1
  have hSi : Integrable S P := by
    rw [hSdef]
    refine Integrable.of_bound ((continuous_traceExp.comp continuous_cx).measurable.comp
      hFm).aestronglyMeasurable (Real.exp (g * (n * R)) * d) ?_
    filter_upwards [hgood] with ω hω
    have hT := good_tset ℱ hR.le hθ.le hg0 hω (le_refl n) (le_refl n)
    show ‖traceExp (cx ((-θ) • Ysum Xp n ω + g • Wsum ℱ P Xp n ω))‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (traceExp_nonneg hT.1)]
    have := traceExp_le_of_le hL hT.1 hT.2
    rwa [traceExp_zero'] at this
  have hWeq : ∀ᵐ ω ∂P, Matrix.of (Wsum ℱ P Xp n ω) =
      ∑ k ∈ Finset.Icc 1 n, condExpMatrix (ℱ (k - 1)) P (Xp k) ω := by
    have h : ∀ k, ∀ᵐ ω ∂P, k ∈ Finset.Icc 1 n → ∀ a b,
        P[Xp k | ℱ (k - 1)] ω a b = P[fun ω => Xp k ω a b | ℱ (k - 1)] ω := by
      intro k
      by_cases hk : k ∈ Finset.Icc 1 n
      · filter_upwards [ae_all_iff.2 fun a => ae_all_iff.2 fun b =>
          condExp_entry (m := ℱ (k - 1)) (Xp k) (hXi k hk) a b] with ω hω _ using hω
      · exact Filter.Eventually.of_forall fun ω h => absurd h hk
    filter_upwards [ae_all_iff.2 h] with ω hω
    ext a b
    simp only [Wsum, Matrix.of_apply, Matrix.sum_apply, Finset.sum_apply, condExpMatrix]
    exact Finset.sum_congr rfl fun k hk => hω k hk a b
  obtain ⟨t, htdef⟩ : ∃ t, t = -θ * ((1 - γ) * mu) + g * mu := ⟨_, rfl⟩
  have hM := mul_meas_ge_le_integral_of_nonneg hS0 hSi (Real.exp t)
  try simp only [measureReal_def] at hM
  have hF : (P {x | Real.exp t ≤ S x}).toReal ≤ d * Real.exp (-t) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos t)]
    linarith [hM, hSn']
  have hbase : 0 < Real.exp (-γ) / (1 - γ) ^ (1 - γ) :=
    div_pos (Real.exp_pos _) (Real.rpow_pos_of_pos h1γ _)
  have hexp : Real.exp (-t) = (Real.exp (-γ) / (1 - γ) ^ (1 - γ)) ^ (mu / R) := by
    rw [Real.rpow_def_of_pos hbase, Real.log_div (Real.exp_pos _).ne'
      (Real.rpow_pos_of_pos h1γ _).ne', Real.log_exp, Real.log_rpow h1γ]
    congr 1
    rw [htdef, hθdef, hg]
    field_simp
    ring
  rw [← hexp]
  refine le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)) hF
  filter_upwards [hgood, hWeq] with ω hω hWω hE
  obtain ⟨hE1, hE2⟩ := hE
  have hT := good_tset ℱ hR.le hθ.le hg0 hω (le_refl n) (le_refl n)
  have hpos : 0 < S ω := by rw [hSdef]; exact traceExp_pos hT.1
  show Real.exp t ≤ S ω
  rw [← Real.le_log_iff_exp_le hpos]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hW2 := hE2
  rw [← hWω] at hW2
  have := final_bound hd hθ hg0 hε (Ysum Xp n ω) (Wsum ℱ P Xp n ω) hT.1 hE1 hW2
  rw [hSdef, htdef]
  exact this

end P09c104e7

theorem P09c104e7.probLieb_holds : P09c104e7.ProbLieb := by
  intro Ω _ μ _ d _ H hH X hMeas hHerm hExp
  exact TroppMatrixConcentration.ch3_probabilistic_lieb μ H hH X hMeas hHerm hExp

open MostlyExplorationFree.GreedyBandit Matrix MeasureTheory ProbabilityTheory in
theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (hd : 1 ≤ d) (ℱ : Filtration ℕ mΩ) (n : ℕ)
    (Xk : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (R : ℝ) (hR : 0 < R)
    (hadapted : ∀ k ∈ Finset.Icc 1 n, ∀ a b, StronglyMeasurable[ℱ k] (fun ω => Xk k ω a b))
    (hpsd : ∀ k ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, (Xk k ω).PosSemidef)
    (hmax : ∀ k ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, lambdaMax (Xk k ω) ≤ R)
    (mu γ : ℝ) (hmu : 0 ≤ mu) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    (P {ω | lambdaMin (∑ k ∈ Finset.Icc 1 n, Xk k ω) ≤ (1 - γ) * mu ∧
        mu ≤ lambdaMin (∑ k ∈ Finset.Icc 1 n, condExpMatrix (ℱ (k - 1)) P (Xk k) ω)}).toReal
      ≤ d * (Real.exp (-γ) / (1 - γ) ^ (1 - γ)) ^ (mu / R) := by
  exact P09c104e7.main P09c104e7.probLieb_holds P hd ℱ n Xk R hR hadapted hpsd hmax mu γ hmu hγ0 hγ1
