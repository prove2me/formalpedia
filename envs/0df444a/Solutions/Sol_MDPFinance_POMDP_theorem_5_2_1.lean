-- Prove2me | solution 1 for MDPFinance.POMDP.theorem_5_2_1
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-02T16:20:43.868274+00:00
-- url     : https://prove2.me/submissions/7ce46310-5240-44ba-b967-2787b2fb94bd

import Mathlib
import Definitions.Def_MDPFinance_POMDP_Model
import Definitions.Def_MDPFinance_POMDP_Policy
import Definitions.Def_MDPFinance_POMDP_Objective
import Definitions.Def_MDPFinance_POMDP_FilterData

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MDPFinance.POMDP

variable {EX EY A : Type*} [MeasurableSpace EX] [MeasurableSpace EY] [MeasurableSpace A]

namespace Sol521

/-- The kernel reading off a (measurable) probability-measure-valued map. -/
noncomputable def pmKernel {X : Type*} [MeasurableSpace X] (g : X → ProbabilityMeasure EY)
    (hg : Measurable g) : Kernel X EY where
  toFun x := (g x : Measure EY)
  measurable' := measurable_subtype_coe.comp hg

instance {X : Type*} [MeasurableSpace X] (g : X → ProbabilityMeasure EY) (hg : Measurable g) :
    IsMarkovKernel (pmKernel g hg) :=
  ⟨fun x => (g x).2⟩

lemma measurable_update_pair {P X : Type*} [MeasurableSpace P] [MeasurableSpace X] (i : ℕ)
    {f : P → ℕ → X} {g : P → X} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun p => Function.update (f p) i (g p) :=
  measurable_update'.comp (hf.prodMk hg)


variable (M : PartiallyObservableMDM EX EY A) (Fd : FilterData M)

noncomputable def Nd (x : EX) (ρ : ProbabilityMeasure EY) (a : A) (x' : EX) (y' : EY) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (Fd.q x y a x' y') ∂(ρ : Measure EY)

/-- The normalising constant. -/
noncomputable def Nn (x : EX) (ρ : ProbabilityMeasure EY) (a : A) (x' : EX) : ℝ≥0∞ :=
  ∫⁻ y', Nd M Fd x ρ a x' y' ∂Fd.nu

lemma measurable_qq (x : EX) (a : A) :
    Measurable fun p : EY × EX × EY => ENNReal.ofReal (Fd.q x p.1 a p.2.1 p.2.2) :=
  ENNReal.measurable_ofReal.comp (Fd.hq_meas.comp
    ((measurable_const.prodMk (measurable_fst.prodMk measurable_const)).prodMk
      measurable_snd))

lemma measurable_Nd (x : EX) (ρ : ProbabilityMeasure EY) (a : A) :
    Measurable fun p : EX × EY => Nd M Fd x ρ a p.1 p.2 := by
  have := (measurable_qq M Fd x a).comp (f := fun q : (EX × EY) × EY => (q.2, q.1.1, q.1.2))
    (measurable_snd.prodMk (measurable_fst.comp measurable_fst |>.prodMk
      (measurable_snd.comp measurable_fst)))
  exact this.lintegral_prod_right'

lemma measurable_Nn (x : EX) (ρ : ProbabilityMeasure EY) (a : A) :
    Measurable fun x' => Nn M Fd x ρ a x' := by
  have := Fd.hnu_sigmaFinite
  exact (measurable_Nd M Fd x ρ a).lintegral_prod_right'

lemma lintegral_Q_eq (x : EX) (ρ : ProbabilityMeasure EY) (a : A) (F : EX × EY → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ y, ∫⁻ p, F p ∂(M.Q ((x, y), a)) ∂(ρ : Measure EY) =
      ∫⁻ x', ∫⁻ y', Nd M Fd x ρ a x' y' * F (x', y') ∂Fd.nu ∂Fd.lam := by
  have := Fd.hlam_sigmaFinite
  have := Fd.hnu_sigmaFinite
  have hq := measurable_qq M Fd x a
  have hjoint : Measurable fun p : EY × EX × EY =>
      ENNReal.ofReal (Fd.q x p.1 a p.2.1 p.2.2) * F (p.2.1, p.2.2) :=
    hq.mul (hF.comp measurable_snd)
  calc ∫⁻ y, ∫⁻ p, F p ∂(M.Q ((x, y), a)) ∂(ρ : Measure EY)
      = ∫⁻ y, ∫⁻ x', ∫⁻ y', ENNReal.ofReal (Fd.q x y a x' y') * F (x', y') ∂Fd.nu ∂Fd.lam
          ∂(ρ : Measure EY) := by
        refine lintegral_congr fun y => ?_
        have hd : Measurable fun p : EX × EY => ENNReal.ofReal (Fd.q x y a p.1 p.2) :=
          hq.comp (measurable_const.prodMk measurable_id)
        rw [Fd.hQ_density, lintegral_withDensity_eq_lintegral_mul _ hd hF,
          lintegral_prod _ (hd.mul hF).aemeasurable]
        rfl
    _ = ∫⁻ x', ∫⁻ y, ∫⁻ y', ENNReal.ofReal (Fd.q x y a x' y') * F (x', y') ∂Fd.nu
          ∂(ρ : Measure EY) ∂Fd.lam := by
        refine lintegral_lintegral_swap ?_
        have := hjoint.comp (f := fun q : (EY × EX) × EY => (q.1.1, q.1.2, q.2))
          ((measurable_fst.comp measurable_fst).prodMk
            ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
        exact this.lintegral_prod_right'.aemeasurable
    _ = ∫⁻ x', ∫⁻ y', ∫⁻ y, ENNReal.ofReal (Fd.q x y a x' y') * F (x', y')
          ∂(ρ : Measure EY) ∂Fd.nu ∂Fd.lam := by
        refine lintegral_congr fun x' => lintegral_lintegral_swap ?_
        have := hjoint.comp (f := fun q : EY × EY => (q.1, x', q.2))
          (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
        exact this.aemeasurable
    _ = ∫⁻ x', ∫⁻ y', Nd M Fd x ρ a x' y' * F (x', y') ∂Fd.nu ∂Fd.lam := by
        refine lintegral_congr fun x' => lintegral_congr fun y' => ?_
        have hm : Measurable fun y => ENNReal.ofReal (Fd.q x y a x' y') :=
          hq.comp (measurable_id.prodMk (measurable_const : Measurable fun _ : EY => (x', y')))
        rw [Nd, lintegral_mul_const _ hm]


/-- The marginal law of the next observable state, `Q^X(dx'|x,ρ,a)`, as a density w.r.t. `λ`. -/
noncomputable def QX (x : EX) (ρ : ProbabilityMeasure EY) (a : A) : Measure EX :=
  Fd.lam.withDensity (Nn M Fd x ρ a)

lemma isProb_QX (x : EX) (ρ : ProbabilityMeasure EY) (a : A) :
    IsProbabilityMeasure (QX M Fd x ρ a) := by
  have := M.isMarkovQ
  constructor
  rw [QX, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h := lintegral_Q_eq M Fd x ρ a (fun _ => 1) measurable_const
  simp only [mul_one] at h
  show ∫⁻ x', ∫⁻ y', Nd M Fd x ρ a x' y' ∂Fd.nu ∂Fd.lam = 1
  rw [← h]
  simp

lemma bayes (x : EX) (ρ : ProbabilityMeasure EY) (a : A) (F : EX × EY → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ y, ∫⁻ p, F p ∂(M.Q ((x, y), a)) ∂(ρ : Measure EY) =
      ∫⁻ x', ∫⁻ y', F (x', y') ∂(Fd.Phi x ρ a x' : Measure EY) ∂(QX M Fd x ρ a) := by
  have := Fd.hlam_sigmaFinite
  have := Fd.hnu_sigmaFinite
  have hPhim : Measurable fun x' : EX => Fd.Phi x ρ a x' :=
    Fd.hPhi_meas.comp ((measurable_const : Measurable fun _ : EX => (x, ρ)).prodMk
      ((measurable_const : Measurable fun _ : EX => a).prodMk measurable_id))
  have hG : Measurable fun x' => ∫⁻ y', F (x', y') ∂(Fd.Phi x ρ a x' : Measure EY) := by
    have := Measurable.lintegral_kernel_prod_right' (κ := pmKernel (fun x' => Fd.Phi x ρ a x')
      hPhim) hF
    exact this
  rw [lintegral_Q_eq M Fd x ρ a F hF, QX,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_Nn M Fd x ρ a) hG]
  have hint : ∫⁻ x', Nn M Fd x ρ a x' ∂Fd.lam ≠ ∞ := by
    have h := isProb_QX M Fd x ρ a
    rw [QX] at h
    have := h.measure_univ
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
    rw [this]; exact ENNReal.one_ne_top
  refine lintegral_congr_ae ((ae_lt_top (measurable_Nn M Fd x ρ a) hint).mono fun x' hx' => ?_)
  simp only [Pi.mul_apply]
  have hNdm : Measurable fun y' => Nd M Fd x ρ a x' y' :=
    (measurable_Nd M Fd x ρ a).comp (measurable_const.prodMk measurable_id)
  rcases eq_or_ne (Nn M Fd x ρ a x') 0 with h0 | h0
  · rw [h0, zero_mul]
    have hz : (fun y' => Nd M Fd x ρ a x' y') =ᵐ[Fd.nu] 0 :=
      (lintegral_eq_zero_iff hNdm).mp h0
    calc ∫⁻ y', Nd M Fd x ρ a x' y' * F (x', y') ∂Fd.nu = ∫⁻ y', 0 ∂Fd.nu :=
          lintegral_congr_ae (hz.mono fun y' hy' => by simp only [Pi.zero_apply] at hy'; simp [hy'])
      _ = 0 := lintegral_zero
  · have hPhi_eq : (Fd.Phi x ρ a x' : Measure EY) =
        (Nn M Fd x ρ a x')⁻¹ • Fd.nu.withDensity (fun y' => Nd M Fd x ρ a x' y') := by
      ext C hC
      rw [Fd.hPhi x ρ a x' (pos_iff_ne_zero.mpr h0) hx' C hC, Measure.smul_apply,
        withDensity_apply _ hC, smul_eq_mul, div_eq_mul_inv, mul_comm]
      rfl
    have hFm : Measurable fun y' => F (x', y') :=
      hF.comp ((measurable_const : Measurable fun _ : EY => x').prodMk measurable_id)
    rw [hPhi_eq, lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hNdm hFm,
      smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel h0 hx'.ne, one_mul]
    rfl

/-! ### Measurability of the original-model values -/

/-- Iterated Bochner integrals of a bounded measurable function through a Markov kernel, split
into positive and negative parts. -/
lemma iter_eq {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z] (μ : Measure X)
    [IsProbabilityMeasure μ] (κ : Kernel X Z) [IsMarkovKernel κ] (G : X × Z → ℝ)
    (hG : Measurable G) (C : ℝ) (hC : ∀ p, |G p| ≤ C) :
    ∫ x, ∫ z, G (x, z) ∂κ x ∂μ =
      (∫⁻ x, ∫⁻ z, ENNReal.ofReal (G (x, z)) ∂κ x ∂μ).toReal -
        (∫⁻ x, ∫⁻ z, ENNReal.ofReal (-G (x, z)) ∂κ x ∂μ).toReal := by
  have hsec : ∀ x, Measurable fun z => G (x, z) := fun x =>
    hG.comp (measurable_const.prodMk measurable_id)
  have hint : ∀ x, Integrable (fun z => G (x, z)) (κ x) := fun x =>
    Integrable.of_bound (hsec x).aestronglyMeasurable C
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC _)
  have hP : Measurable fun x => ∫⁻ z, ENNReal.ofReal (G (x, z)) ∂κ x :=
    (ENNReal.measurable_ofReal.comp hG).lintegral_kernel_prod_right'
  have hN : Measurable fun x => ∫⁻ z, ENNReal.ofReal (-G (x, z)) ∂κ x :=
    (ENNReal.measurable_ofReal.comp hG.neg).lintegral_kernel_prod_right'
  have hbdP : ∀ x, ∫⁻ z, ENNReal.ofReal (G (x, z)) ∂κ x ≤ ENNReal.ofReal C := by
    intro x
    calc ∫⁻ z, ENNReal.ofReal (G (x, z)) ∂κ x ≤ ∫⁻ _, ENNReal.ofReal C ∂κ x :=
          lintegral_mono fun z => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hC _))
      _ = ENNReal.ofReal C := by simp
  have hbdN : ∀ x, ∫⁻ z, ENNReal.ofReal (-G (x, z)) ∂κ x ≤ ENNReal.ofReal C := by
    intro x
    calc ∫⁻ z, ENNReal.ofReal (-G (x, z)) ∂κ x ≤ ∫⁻ _, ENNReal.ofReal C ∂κ x :=
          lintegral_mono fun z => ENNReal.ofReal_le_ofReal ((neg_le_abs _).trans (hC _))
      _ = ENNReal.ofReal C := by simp
  have hfinP : ∀ x, ∫⁻ z, ENNReal.ofReal (G (x, z)) ∂κ x < ∞ := fun x =>
    (hbdP x).trans_lt ENNReal.ofReal_lt_top
  have hfinN : ∀ x, ∫⁻ z, ENNReal.ofReal (-G (x, z)) ∂κ x < ∞ := fun x =>
    (hbdN x).trans_lt ENNReal.ofReal_lt_top
  have hiP : Integrable (fun x => (∫⁻ z, ENNReal.ofReal (G (x, z)) ∂κ x).toReal) μ :=
    Integrable.of_bound hP.ennreal_toReal.aestronglyMeasurable (ENNReal.ofReal C).toReal
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        exact ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbdP x))
  have hiN : Integrable (fun x => (∫⁻ z, ENNReal.ofReal (-G (x, z)) ∂κ x).toReal) μ :=
    Integrable.of_bound hN.ennreal_toReal.aestronglyMeasurable (ENNReal.ofReal C).toReal
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        exact ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbdN x))
  calc ∫ x, ∫ z, G (x, z) ∂κ x ∂μ
      = ∫ x, ((∫⁻ z, ENNReal.ofReal (G (x, z)) ∂κ x).toReal -
          (∫⁻ z, ENNReal.ofReal (-G (x, z)) ∂κ x).toReal) ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hint x)
    _ = _ := by
        rw [integral_sub hiP hiN, integral_toReal hP.aemeasurable (ae_of_all _ hfinP),
          integral_toReal hN.aemeasurable (ae_of_all _ hfinN)]

/-- Bayes' formula for bounded real test functions. -/
lemma bayes_real (x : EX) (ρ : ProbabilityMeasure EY) (a : A) (G : EX × EY → ℝ)
    (hG : Measurable G) (C : ℝ) (hC : ∀ p, |G p| ≤ C) :
    ∫ y, ∫ p, G p ∂(M.Q ((x, y), a)) ∂(ρ : Measure EY) =
      ∫ x', ∫ y', G (x', y') ∂(Fd.Phi x ρ a x' : Measure EY) ∂(QX M Fd x ρ a) := by
  have := M.isMarkovQ
  have := isProb_QX M Fd x ρ a
  have hf : Measurable fun y : EY => ((x, y), a) :=
    (measurable_const.prodMk measurable_id).prodMk measurable_const
  have hPhim : Measurable fun x' : EX => Fd.Phi x ρ a x' :=
    Fd.hPhi_meas.comp ((measurable_const : Measurable fun _ : EX => (x, ρ)).prodMk
      ((measurable_const : Measurable fun _ : EX => a).prodMk measurable_id))
  have h1 := iter_eq (ρ : Measure EY) (M.Q.comap _ hf) (fun q : EY × (EX × EY) => G q.2)
    (hG.comp measurable_snd) C (fun q => hC _)
  have h2 := iter_eq (QX M Fd x ρ a) (pmKernel (fun x' => Fd.Phi x ρ a x') hPhim)
    (fun q : EX × EY => G q) hG C hC
  have hb1 := bayes M Fd x ρ a (fun p => ENNReal.ofReal (G p)) (ENNReal.measurable_ofReal.comp hG)
  have hb2 := bayes M Fd x ρ a (fun p => ENNReal.ofReal (-G p))
    (ENNReal.measurable_ofReal.comp hG.neg)
  calc ∫ y, ∫ p, G p ∂(M.Q ((x, y), a)) ∂(ρ : Measure EY)
      = (∫⁻ y, ∫⁻ p, ENNReal.ofReal (G p) ∂(M.Q ((x, y), a)) ∂(ρ : Measure EY)).toReal -
        (∫⁻ y, ∫⁻ p, ENNReal.ofReal (-G p) ∂(M.Q ((x, y), a)) ∂(ρ : Measure EY)).toReal := h1
    _ = (∫⁻ x', ∫⁻ y', ENNReal.ofReal (G (x', y')) ∂(Fd.Phi x ρ a x' : Measure EY)
            ∂(QX M Fd x ρ a)).toReal -
          (∫⁻ x', ∫⁻ y', ENNReal.ofReal (-G (x', y')) ∂(Fd.Phi x ρ a x' : Measure EY)
            ∂(QX M Fd x ρ a)).toReal := by rw [hb1, hb2]
    _ = _ := h2.symm

/-! ### The filter started at an arbitrary time -/

/-- The filter started at time `m` from the prior `ρ`: `filt m ρ 0 = ρ`,
`filt m ρ (i+1) = Φ(x_{m+i}, filt m ρ i, a_{m+i}, x_{m+i+1})`. -/
noncomputable def filt (m : ℕ) (ρ : ProbabilityMeasure EY) :
    ℕ → (ℕ → EX) → (ℕ → A) → ProbabilityMeasure EY
  | 0, _, _ => ρ
  | (i + 1), xs, as => Fd.Phi (xs (m + i)) (filt m ρ i xs as) (as (m + i)) (xs (m + i + 1))

lemma mu_eq_filt : ∀ n xs as, Fd.mu M n xs as = filt M Fd 0 ⟨M.Q0, M.isProbQ0⟩ n xs as := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro xs as
    simp only [FilterData.mu, filt, ih, zero_add]

lemma filt_shift : ∀ i m (ρ : ProbabilityMeasure EY) (xs : ℕ → EX) (as : ℕ → A),
    filt M Fd m ρ (i + 1) xs as = filt M Fd (m + 1) (Fd.Phi (xs m) ρ (as m) (xs (m + 1))) i xs as := by
  intro i
  induction i with
  | zero => intro m ρ xs as; simp [filt]
  | succ i ih =>
    intro m ρ xs as
    rw [filt.eq_2, ih, filt.eq_2]
    have e : m + (i + 1) = m + 1 + i := by omega
    rw [e]

lemma measurable_filt (m : ℕ) (ρ : ProbabilityMeasure EY) :
    ∀ i, Measurable fun p : (ℕ → EX) × (ℕ → A) => filt M Fd m ρ i p.1 p.2 := by
  intro i
  induction i with
  | zero => exact measurable_const
  | succ i ih =>
    exact Fd.hPhi_meas.comp ((((measurable_pi_apply (m + i)).comp measurable_fst).prodMk ih).prodMk
      (((measurable_pi_apply (m + i)).comp measurable_snd).prodMk
        ((measurable_pi_apply (m + i + 1)).comp measurable_fst)))

/-- The test function integrated against the filter: `(xs,as) ↦ ∫ F(xs,as,y) filt m ρ k (dy)`. -/
noncomputable def Fpost (m : ℕ) (ρ : ProbabilityMeasure EY) (k : ℕ)
    (F : (ℕ → EX) → (ℕ → A) → EY → ℝ) : (ℕ → EX) → (ℕ → A) → EY → ℝ :=
  fun xs as _ => ∫ yn, F xs as yn ∂(filt M Fd m ρ k xs as : Measure EY)

lemma measurable_Fpost (m : ℕ) (ρ : ProbabilityMeasure EY) (k : ℕ)
    (F : (ℕ → EX) → (ℕ → A) → EY → ℝ)
    (hF : Measurable fun p : (ℕ → EX) × (ℕ → A) × EY => F p.1 p.2.1 p.2.2) :
    Measurable fun p : (ℕ → EX) × (ℕ → A) × EY => Fpost M Fd m ρ k F p.1 p.2.1 p.2.2 := by
  have hF' : Measurable fun q : ((ℕ → EX) × (ℕ → A)) × EY => F q.1.1 q.1.2 q.2 :=
    hF.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have := (hF'.stronglyMeasurable.integral_kernel_prod_right'
    (κ := pmKernel (fun p : (ℕ → EX) × (ℕ → A) => filt M Fd m ρ k p.1 p.2)
      (measurable_filt M Fd m ρ k))).measurable
  exact this.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))

lemma abs_Fpost_le (m : ℕ) (ρ : ProbabilityMeasure EY) (k : ℕ)
    (F : (ℕ → EX) → (ℕ → A) → EY → ℝ) (C : ℝ) (hC : ∀ xs as y, |F xs as y| ≤ C) :
    ∀ xs as y, |Fpost M Fd m ρ k F xs as y| ≤ C := by
  intro xs as y
  simp only [Fpost]
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := C) (ae_of_all _ fun p => ?_)).trans (by simp)
  rw [Real.norm_eq_abs]; exact hC _ _ _

/-! ### Properties of the expectation operator `Ex` -/

lemma measurable_Ex (π : Policy EX A) (F : (ℕ → EX) → (ℕ → A) → EY → ℝ)
    (hF : Measurable fun p : (ℕ → EX) × (ℕ → A) × EY => F p.1 p.2.1 p.2.2) :
    ∀ k n, (∀ j, n ≤ j → j < n + k →
      Measurable fun p : (ℕ → EX) × (ℕ → A) => π j p.1 p.2) →
      Measurable fun p : (ℕ → EX) × (ℕ → A) × EY => M.Ex π k n p.1 p.2.1 p.2.2 F := by
  intro k
  induction k with
  | zero => intro n _; exact hF
  | succ k ih =>
    intro n hπ
    have hπn : Measurable fun p : (ℕ → EX) × (ℕ → A) × EY => π n p.1 p.2.1 :=
      (hπ n le_rfl (by omega)).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have hg : Measurable fun p : (ℕ → EX) × (ℕ → A) × EY => ((p.1 n, p.2.2), π n p.1 p.2.1) :=
      (((measurable_pi_apply n).comp measurable_fst).prodMk
        (measurable_snd.comp measurable_snd)).prodMk hπn
    have hH : Measurable fun q : ((ℕ → EX) × (ℕ → A) × EY) × (EX × EY) =>
        M.Ex π k (n + 1) (Function.update q.1.1 (n + 1) q.2.1)
          (Function.update q.1.2.1 n (π n q.1.1 q.1.2.1)) q.2.2 F :=
      (ih (n + 1) (fun j h1 h2 => hπ j (by omega) (by omega))).comp
        ((measurable_update_pair (n + 1) (measurable_fst.comp measurable_fst)
          (measurable_fst.comp measurable_snd)).prodMk
        ((measurable_update_pair n (measurable_fst.comp (measurable_snd.comp measurable_fst))
          (hπn.comp measurable_fst)).prodMk (measurable_snd.comp measurable_snd)))
    have := M.isMarkovQ
    exact (hH.stronglyMeasurable.integral_kernel_prod_right' (κ := M.Q.comap _ hg)).measurable

lemma abs_Ex_le (π : Policy EX A) (F : (ℕ → EX) → (ℕ → A) → EY → ℝ) (C : ℝ)
    (hC : ∀ xs as y, |F xs as y| ≤ C) :
    ∀ k n xs as y, |M.Ex π k n xs as y F| ≤ C := by
  intro k
  induction k with
  | zero => intro n xs as y; exact hC _ _ _
  | succ k ih =>
    intro n xs as y
    have := M.isMarkovQ
    simp only [PartiallyObservableMDM.Ex]
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := C) (ae_of_all _ fun p => ?_)).trans (by simp)
    rw [Real.norm_eq_abs]; exact ih _ _ _ _

lemma Ex_congr (π : Policy EX A) :
    ∀ k n xs as y (F F' : (ℕ → EX) → (ℕ → A) → EY → ℝ),
      (∀ xs' as', (∀ i ≤ n, xs' i = xs i) → (∀ i < n, as' i = as i) →
        ∀ y', F xs' as' y' = F' xs' as' y') →
      M.Ex π k n xs as y F = M.Ex π k n xs as y F' := by
  intro k
  induction k with
  | zero => intro n xs as y F F' h; exact h xs as (fun _ _ => rfl) (fun _ _ => rfl) y
  | succ k ih =>
    intro n xs as y F F' h
    simp only [PartiallyObservableMDM.Ex]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    dsimp only
    apply ih
    intro xs' as' hx ha y'
    refine h xs' as' (fun i hi => ?_) (fun i hi => ?_) y'
    · rw [hx i (by omega), Function.update_of_ne (by omega)]
    · rw [ha i (by omega), Function.update_of_ne (by omega)]

/-! ### The main induction -/

lemma main (π : Policy EX A) (F : (ℕ → EX) → (ℕ → A) → EY → ℝ)
    (hF : Measurable fun p : (ℕ → EX) × (ℕ → A) × EY => F p.1 p.2.1 p.2.2) (C : ℝ)
    (hC : ∀ xs as y, |F xs as y| ≤ C) :
    ∀ k m, (∀ j, m ≤ j → j < m + k →
      Measurable fun p : (ℕ → EX) × (ℕ → A) => π j p.1 p.2) →
      ∀ (ρ : ProbabilityMeasure EY) (xs : ℕ → EX) (as : ℕ → A),
      ∫ y, M.Ex π k m xs as y F ∂(ρ : Measure EY) =
        ∫ y, M.Ex π k m xs as y (Fpost M Fd m ρ k F) ∂(ρ : Measure EY) := by
  intro k
  induction k with
  | zero =>
    intro m _ ρ xs as
    simp only [PartiallyObservableMDM.Ex, Fpost, filt]
    simp
  | succ k ih =>
    intro m hπ ρ xs as
    have hupd : Measurable fun p : EX × EY =>
        (Function.update xs (m + 1) p.1, Function.update as m (π m xs as), p.2) :=
      (measurable_update_pair (m + 1) measurable_const measurable_fst).prodMk
        (measurable_const.prodMk measurable_snd)
    have hπ' : ∀ j, m + 1 ≤ j → j < m + 1 + k →
        Measurable fun p : (ℕ → EX) × (ℕ → A) => π j p.1 p.2 :=
      fun j h1 h2 => hπ j (by omega) (by omega)
    have hL := bayes_real M Fd (xs m) ρ (π m xs as)
      (fun p => M.Ex π k (m + 1) (Function.update xs (m + 1) p.1)
        (Function.update as m (π m xs as)) p.2 F)
      ((measurable_Ex M π F hF k (m + 1) hπ').comp hupd) C
      (fun p => abs_Ex_le M π F C hC _ _ _ _ _)
    have hR := bayes_real M Fd (xs m) ρ (π m xs as)
      (fun p => M.Ex π k (m + 1) (Function.update xs (m + 1) p.1)
        (Function.update as m (π m xs as)) p.2 (Fpost M Fd m ρ (k + 1) F))
      ((measurable_Ex M π _ (measurable_Fpost M Fd m ρ (k + 1) F hF) k (m + 1) hπ').comp hupd) C
      (fun p => abs_Ex_le M π _ C (abs_Fpost_le M Fd m ρ (k + 1) F C hC) _ _ _ _ _)
    simp only [PartiallyObservableMDM.Ex]
    rw [hL, hR]
    refine integral_congr_ae (ae_of_all _ fun x' => ?_)
    dsimp only
    rw [ih (m + 1) hπ' (Fd.Phi (xs m) ρ (π m xs as) x') (Function.update xs (m + 1) x')
      (Function.update as m (π m xs as))]
    refine integral_congr_ae (ae_of_all _ fun y' => ?_)
    dsimp only
    apply Ex_congr
    intro xs' as' hx ha y''
    simp only [Fpost]
    rw [filt_shift, hx m (by omega), hx (m + 1) le_rfl, ha m (by omega)]
    simp

end Sol521

end MDPFinance.POMDP

open MDPFinance.POMDP in
theorem solution {EX EY A : Type*} [MeasurableSpace EX] [MeasurableSpace EY]
    [MeasurableSpace A] [Nonempty A] (M : PartiallyObservableMDM EX EY A) (Fd : FilterData M)
    (N : ℕ) (π : Policy EX A) (hπ : M.IsPolicy N π) (x0 : EX) (n : ℕ) (hn : n ≤ N)
    (v : (ℕ → EX) → (ℕ → A) → EY → ℝ)
    (hv_meas : Measurable fun p : (ℕ → EX) × (ℕ → A) × EY => v p.1 p.2.1 p.2.2)
    (hv_bdd : ∃ C : ℝ, ∀ xs as y, |v xs as y| ≤ C) :
    ∫ y0 : EY, M.Ex π n 0 (fun _ => x0) (fun _ => Classical.arbitrary A) y0
        (fun xs as y => v xs as y) ∂M.Q0 =
      ∫ y0 : EY, M.Ex π n 0 (fun _ => x0) (fun _ => Classical.arbitrary A) y0
        (fun xs as _ => ∫ yn, v xs as yn ∂(Fd.mu M n xs as).toMeasure) ∂M.Q0 := by
  obtain ⟨C, hC⟩ := hv_bdd
  have hπm : ∀ j, 0 ≤ j → j < 0 + n →
      Measurable fun p : (ℕ → EX) × (ℕ → A) => π j p.1 p.2 :=
    fun j _ hj => (hπ j (by omega)).1
  have h := Sol521.main M Fd π v hv_meas C hC n 0 hπm ⟨M.Q0, M.isProbQ0⟩ (fun _ => x0)
    (fun _ => Classical.arbitrary A)
  have hfun : (fun xs as (_ : EY) => ∫ yn, v xs as yn ∂(Fd.mu M n xs as).toMeasure) =
      Sol521.Fpost M Fd 0 ⟨M.Q0, M.isProbQ0⟩ n v := by
    funext xs as y
    simp only [Sol521.Fpost, Sol521.mu_eq_filt]
  rw [hfun]
  exact h
