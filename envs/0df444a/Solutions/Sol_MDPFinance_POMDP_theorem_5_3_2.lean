-- Prove2me | solution 1 for MDPFinance.POMDP.theorem_5_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-02T16:07:26.655984+00:00
-- url     : https://prove2.me/submissions/5dfc7ade-352e-4314-b8c2-56997a675f78

import Mathlib
import Definitions.Def_MDPFinance_POMDP_Model
import Definitions.Def_MDPFinance_POMDP_Policy
import Definitions.Def_MDPFinance_POMDP_Objective
import Definitions.Def_MDPFinance_POMDP_FilterData
import Definitions.Def_MDPFinance_POMDP_FilteredModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MDPFinance.POMDP

variable {EX EY A : Type*} [MeasurableSpace EX] [MeasurableSpace EY] [MeasurableSpace A]

namespace Sol532

/-! ### Generalities on `erealIntegral` -/

lemma erealIntegral_mono {E : Type*} [MeasurableSpace E] (μ : Measure E) {v w : E → EReal}
    (h : ∀ x, v x ≤ w x) : erealIntegral μ v ≤ erealIntegral μ w := by
  unfold erealIntegral
  refine add_le_add ?_ ?_
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (lintegral_mono fun x => EReal.toENNReal_le_toENNReal (sup_le_sup_right (h x) _))
  · refine EReal.neg_le_neg_iff.mpr ?_
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (lintegral_mono fun x => EReal.toENNReal_le_toENNReal
        (sup_le_sup_right (EReal.neg_le_neg_iff.mpr (h x)) _))

lemma erealIntegral_map {E F : Type*} [MeasurableSpace E] [MeasurableSpace F] (μ : Measure E)
    {h : E → F} (hh : Measurable h) {v : F → EReal} (hv : Measurable v) :
    erealIntegral (μ.map h) v = erealIntegral μ (v ∘ h) := by
  unfold erealIntegral
  rw [lintegral_map (f := fun x => (v x ⊔ 0).toENNReal)
      ((hv.max measurable_const).ereal_toENNReal) hh,
    lintegral_map (f := fun x => ((-v x) ⊔ 0).toENNReal)
      ((hv.neg.max measurable_const).ereal_toENNReal) hh]
  rfl

lemma measurable_erealIntegral_kernel {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (κ : Kernel X Y) [IsSFiniteKernel κ] {f : X → Y → EReal}
    (hf : Measurable fun p : X × Y => f p.1 p.2) :
    Measurable fun x => erealIntegral (κ x) (f x) := by
  unfold erealIntegral
  have h1 : Measurable fun x => ∫⁻ y, (f x y ⊔ 0).toENNReal ∂κ x :=
    (hf.max measurable_const).ereal_toENNReal.lintegral_kernel_prod_right'
  have h2 : Measurable fun x => ∫⁻ y, ((-f x y) ⊔ 0).toENNReal ∂κ x :=
    (hf.neg.max measurable_const).ereal_toENNReal.lintegral_kernel_prod_right'
  exact (measurable_coe_ennreal_ereal.comp h1).add (measurable_coe_ennreal_ereal.comp h2).neg

/-- The kernel `p ↦ ρ` reading off the probability-measure coordinate. -/
noncomputable def pmKernel {X : Type*} [MeasurableSpace X] (g : X → ProbabilityMeasure EY)
    (hg : Measurable g) : Kernel X EY where
  toFun x := (g x : Measure EY)
  measurable' := measurable_subtype_coe.comp hg

instance {X : Type*} [MeasurableSpace X] (g : X → ProbabilityMeasure EY) (hg : Measurable g) :
    IsMarkovKernel (pmKernel g hg) :=
  ⟨fun x => (g x).2⟩

variable (M : PartiallyObservableMDM EX EY A) (Fd : FilterData M) (M' : FilteredModel M Fd)

lemma measurable_rprime :
    Measurable fun p : (EX × ProbabilityMeasure EY) × A => FilteredModel.rprime M p.1 p.2 := by
  have := measurable_erealIntegral_kernel (pmKernel (fun p : (EX × ProbabilityMeasure EY) × A =>
      p.1.2) (measurable_snd.comp measurable_fst))
    (f := fun p y => (M.r (p.1.1, y, p.2) : EReal))
    (measurable_coe_real_ereal.comp (M.hr_meas.comp
      ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))))
  exact this

lemma measurable_gprime :
    Measurable fun e : EX × ProbabilityMeasure EY => FilteredModel.gprime M e := by
  have := measurable_erealIntegral_kernel (pmKernel (fun e : EX × ProbabilityMeasure EY =>
      e.2) measurable_snd)
    (f := fun e y => (M.g (e.1, y) : EReal))
    (measurable_coe_real_ereal.comp (M.hg_meas.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
  exact this

/-- The graph map `x' ↦ (x', Φ(x,ρ,a,x'))`. -/
lemma measurable_graph (x : EX) (ρ : ProbabilityMeasure EY) (a : A) :
    Measurable fun x' : EX => (x', Fd.Phi x ρ a x') := by
  have : Measurable fun x' : EX => Fd.Phi x ρ a x' :=
    Fd.hPhi_meas.comp ((measurable_const : Measurable fun _ : EX => (x, ρ)).prodMk
      ((measurable_const : Measurable fun _ : EX => a).prodMk measurable_id))
  exact measurable_id.prodMk this

lemma isProb_QXprime (x : EX) (ρ : ProbabilityMeasure EY) (a : A) :
    IsProbabilityMeasure (Fd.QXprime M x ρ a) := by
  have := M.isMarkovQ
  have hk : Measurable fun y : EY => (M.Q ((x, y), a)).map Prod.fst :=
    (Measure.measurable_map _ measurable_fst).comp
      (M.Q.measurable.comp ((measurable_const.prodMk measurable_id).prodMk measurable_const))
  constructor
  rw [FilterData.QXprime, Measure.bind_apply MeasurableSet.univ hk.aemeasurable]
  simp [Measure.map_apply measurable_fst MeasurableSet.univ]

instance isMarkov_Qprime : IsMarkovKernel M'.Qprime := by
  constructor
  rintro ⟨⟨x, ρ⟩, a⟩
  rw [M'.hQprime]
  have := isProb_QXprime M Fd x ρ a
  exact Measure.isProbabilityMeasure_map (measurable_graph M Fd x ρ a).aemeasurable


lemma measurable_update_pair {P X : Type*} [MeasurableSpace P] [MeasurableSpace X] (i : ℕ)
    {f : P → ℕ → X} {g : P → X} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun p => Function.update (f p) i (g p) :=
  measurable_update'.comp (hf.prodMk hg)

lemma measurable_ExPrime [Nonempty A] (π : Policy EX A) (n : ℕ)
    (hπ : ∀ j < n, Measurable fun p : (ℕ → EX) × (ℕ → A) => π j p.1 p.2) :
    ∀ k j, j + k ≤ n → Measurable fun p : ((ℕ → EX) × (ℕ → A)) × ProbabilityMeasure EY =>
      FilteredModel.ExPrime M Fd M' π k j p.1.1 p.1.2 p.2 := by
  intro k
  induction k with
  | zero =>
    intro j _
    exact (measurable_gprime M).comp
      (((measurable_pi_apply j).comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
  | succ k ih =>
    intro j hj
    simp only [FilteredModel.ExPrime]
    have hg : Measurable fun p : ((ℕ → EX) × (ℕ → A)) × ProbabilityMeasure EY =>
        ((p.1.1 j, p.2), π j p.1.1 p.1.2) :=
      (((measurable_pi_apply j).comp (measurable_fst.comp measurable_fst)).prodMk
        measurable_snd).prodMk ((hπ j (by omega)).comp measurable_fst)
    refine ((measurable_rprime M).comp hg).add (Measurable.const_mul ?_ _)
    have := measurable_erealIntegral_kernel (M'.Qprime.comap _ hg)
      (f := fun p e' => FilteredModel.ExPrime M Fd M' π k (j + 1)
        (Function.update p.1.1 (j + 1) e'.1) (Function.update p.1.2 j (π j p.1.1 p.1.2)) e'.2)
      ((ih (j + 1) (by omega)).comp ((((measurable_update_pair (j + 1)
          (measurable_fst.comp (measurable_fst.comp measurable_fst))
          (measurable_fst.comp measurable_snd))).prodMk
        (measurable_update_pair j (measurable_snd.comp (measurable_fst.comp measurable_fst))
          ((hπ j (by omega)).comp (measurable_fst.comp measurable_fst)))).prodMk
        (measurable_snd.comp measurable_snd)))
    exact this



/-! ### Extended-real arithmetic -/

lemma toENNReal_max_zero (x : EReal) : (x ⊔ 0).toENNReal = x.toENNReal := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, EReal.toENNReal_of_nonpos h, EReal.toENNReal_zero]

/-- Lift an extended nonnegative real that is finite to a real. -/
lemma coe_ennreal_eq_coe_real {a : ℝ≥0∞} (ha : a ≠ ∞) : (a : EReal) = ((a.toReal : ℝ) : EReal) := by
  lift a to NNReal using ha
  rfl

/-- The core identity behind `erealIntegral_sub`. -/
lemma ereal_sub_aux (P Q a b : ℝ≥0∞) (hP : P ≠ ∞) (ha : a ≠ ∞) (h : P + b = Q + a) :
    (P : EReal) + -(Q : EReal) = (a : EReal) - (b : EReal) := by
  by_cases hb : b = ∞
  · have hQ : Q = ∞ := by
      subst hb
      by_contra hQ
      rw [add_top] at h
      exact (ENNReal.add_ne_top.mpr ⟨hQ, ha⟩) h.symm
    subst hb; subst hQ
    rw [EReal.coe_ennreal_top, EReal.neg_top, coe_ennreal_eq_coe_real hP, EReal.add_bot,
      sub_eq_add_neg, EReal.neg_top, coe_ennreal_eq_coe_real ha, EReal.add_bot]
  · have hQ : Q ≠ ∞ := by
      intro hQ; rw [hQ, top_add] at h; exact (ENNReal.add_ne_top.mpr ⟨hP, hb⟩) h
    rw [coe_ennreal_eq_coe_real hP, coe_ennreal_eq_coe_real hQ, coe_ennreal_eq_coe_real ha,
      coe_ennreal_eq_coe_real hb, ← EReal.coe_neg, ← EReal.coe_add, ← EReal.coe_sub]
    congr 1
    have := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_add hP hb, ENNReal.toReal_add hQ ha] at this
    linarith

/-- `∫ (A - B) = ∫ A - ∫ B` for `[0,∞]`-valued `A, B` with `∫ A < ∞`. -/
lemma erealIntegral_sub {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {A B : Ω → ℝ≥0∞}
    (hA : Measurable A) (hB : Measurable B) (hfin : ∫⁻ ω, A ω ∂μ ≠ ∞) :
    erealIntegral μ (fun ω => (A ω : EReal) - (B ω : EReal)) =
      ((∫⁻ ω, A ω ∂μ : ℝ≥0∞) : EReal) - ((∫⁻ ω, B ω ∂μ : ℝ≥0∞) : EReal) := by
  have hAe : ∀ᵐ ω ∂μ, A ω ≠ ∞ := (ae_lt_top hA hfin).mono fun _ h => h.ne
  have h1 : ∫⁻ ω, ((((A ω : EReal) - (B ω : EReal)) ⊔ 0).toENNReal) ∂μ =
      ∫⁻ ω, (A ω - B ω) ∂μ := by
    refine lintegral_congr fun ω => ?_
    rw [toENNReal_max_zero, EReal.toENNReal_sub (EReal.coe_ennreal_nonneg _),
      EReal.toENNReal_coe, EReal.toENNReal_coe]
  have h2 : ∫⁻ ω, (((-((A ω : EReal) - (B ω : EReal))) ⊔ 0).toENNReal) ∂μ =
      ∫⁻ ω, (B ω - A ω) ∂μ := by
    refine lintegral_congr_ae (hAe.mono fun ω hω => ?_)
    dsimp only
    rw [toENNReal_max_zero, coe_ennreal_eq_coe_real hω, EReal.neg_sub (Or.inr (by simp))
      (Or.inl (by simp)), add_comm, ← sub_eq_add_neg, EReal.toENNReal_sub (EReal.coe_nonneg.mpr ENNReal.toReal_nonneg),
      EReal.toENNReal_coe, ← coe_ennreal_eq_coe_real hω, EReal.toENNReal_coe]
  unfold erealIntegral
  rw [h1, h2]
  refine ereal_sub_aux _ _ _ _ ?_ hfin ?_
  · exact ne_top_of_le_ne_top hfin (lintegral_mono fun ω => tsub_le_self)
  · rw [← lintegral_add_right _ hB, ← lintegral_add_right _ hA]
    refine lintegral_congr fun ω => ?_
    rw [tsub_add_eq_max, tsub_add_eq_max, max_comm]

lemma ereal_split (r β : ℝ) (hβ : 0 < β) (A B : ℝ≥0∞) :
    (r : EReal) + (β : EReal) * ((A : EReal) - (B : EReal)) =
      ((ENNReal.ofReal r + ENNReal.ofReal β * A : ℝ≥0∞) : EReal) -
        ((ENNReal.ofReal (-r) + ENNReal.ofReal β * B : ℝ≥0∞) : EReal) := by
  have hβ' : ENNReal.ofReal β ≠ 0 := by simpa using hβ
  by_cases hB : B = ∞
  · subst hB
    rw [EReal.coe_ennreal_top, EReal.sub_top, EReal.coe_mul_bot_of_pos hβ, EReal.add_bot,
      ENNReal.mul_top hβ', add_top, EReal.coe_ennreal_top, EReal.sub_top]
  by_cases hA : A = ∞
  · subst hA
    rw [EReal.coe_ennreal_top, coe_ennreal_eq_coe_real hB, EReal.top_sub_coe,
      EReal.coe_mul_top_of_pos hβ, EReal.coe_add_top, ENNReal.mul_top hβ', add_top,
      EReal.coe_ennreal_top]
    have : ENNReal.ofReal (-r) + ENNReal.ofReal β * B ≠ ∞ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB⟩
    rw [coe_ennreal_eq_coe_real this, EReal.top_sub_coe]
  have h1 : ENNReal.ofReal r + ENNReal.ofReal β * A ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA⟩
  have h2 : ENNReal.ofReal (-r) + ENNReal.ofReal β * B ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB⟩
  rw [coe_ennreal_eq_coe_real hA, coe_ennreal_eq_coe_real hB, coe_ennreal_eq_coe_real h1,
    coe_ennreal_eq_coe_real h2, ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_add,
    ← EReal.coe_sub]
  congr 1
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA),
    ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hβ.le,
    ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
  rcases le_total 0 r with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

lemma ereal_recombine (β : ℝ) (hβ : 0 < β) (a1 a2 b1 b2 : ℝ≥0∞) (ha1 : a1 ≠ ∞) (ha2 : a2 ≠ ∞) :
    ((a1 + ENNReal.ofReal β * a2 : ℝ≥0∞) : EReal) - ((b1 + ENNReal.ofReal β * b2 : ℝ≥0∞) : EReal) =
      ((a1 : EReal) - (b1 : EReal)) + (β : EReal) * ((a2 : EReal) - (b2 : EReal)) := by
  have hβ' : ENNReal.ofReal β ≠ 0 := by simpa using hβ
  have hl : a1 + ENNReal.ofReal β * a2 ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨ha1, ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha2⟩
  by_cases hb1 : b1 = ∞
  · subst hb1
    rw [top_add, EReal.coe_ennreal_top, EReal.sub_top, EReal.sub_top, EReal.bot_add]
  by_cases hb2 : b2 = ∞
  · subst hb2
    rw [ENNReal.mul_top hβ', add_top, EReal.coe_ennreal_top, EReal.sub_top,
      EReal.sub_top, EReal.coe_mul_bot_of_pos hβ, EReal.add_bot]
  have hr : b1 + ENNReal.ofReal β * b2 ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hb1, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb2⟩
  rw [coe_ennreal_eq_coe_real hl, coe_ennreal_eq_coe_real hr, coe_ennreal_eq_coe_real ha1,
    coe_ennreal_eq_coe_real ha2, coe_ennreal_eq_coe_real hb1, coe_ennreal_eq_coe_real hb2,
    ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_add]
  congr 1
  rw [ENNReal.toReal_add ha1 (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha2),
    ENNReal.toReal_add hb1 (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb2),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hβ.le]
  ring


lemma erealIntegral_eq_sub {E : Type*} [MeasurableSpace E] (μ : Measure E) (v : E → EReal) :
    erealIntegral μ v = ((∫⁻ x, (v x).toENNReal ∂μ : ℝ≥0∞) : EReal) -
      ((∫⁻ x, (-v x).toENNReal ∂μ : ℝ≥0∞) : EReal) := by
  unfold erealIntegral
  simp only [toENNReal_max_zero]
  rfl

lemma erealIntegral_congr_ae {E : Type*} [MeasurableSpace E] (μ : Measure E) {v w : E → EReal}
    (h : v =ᵐ[μ] w) : erealIntegral μ v = erealIntegral μ w := by
  unfold erealIntegral
  have h1 : (fun x => (v x ⊔ 0).toENNReal) =ᵐ[μ] fun x => (w x ⊔ 0).toENNReal :=
    h.mono fun x hx => by simp only [hx]
  have h2 : (fun x => ((-v x) ⊔ 0).toENNReal) =ᵐ[μ] fun x => ((-w x) ⊔ 0).toENNReal :=
    h.mono fun x hx => by simp only [hx]
  rw [lintegral_congr_ae h1, lintegral_congr_ae h2]


/-! ### The Bayes formula for nonnegative integrands -/

/-- The unnormalised posterior density `∫ q(x'|y') ρ(dy)`. -/
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

lemma QXprime_eq (x : EX) (ρ : ProbabilityMeasure EY) (a : A) :
    Fd.QXprime M x ρ a = Fd.lam.withDensity (Nn M Fd x ρ a) := by
  have := Fd.hnu_sigmaFinite
  have := M.isMarkovQ
  ext B hB
  have hk : Measurable fun y : EY => (M.Q ((x, y), a)).map Prod.fst :=
    (Measure.measurable_map _ measurable_fst).comp
      (M.Q.measurable.comp ((measurable_const.prodMk measurable_id).prodMk measurable_const))
  rw [FilterData.QXprime, Measure.bind_apply hB hk.aemeasurable, withDensity_apply _ hB]
  have h1 : ∀ y, (M.Q ((x, y), a)).map Prod.fst B =
      ∫⁻ p, (Prod.fst ⁻¹' B).indicator 1 p ∂(M.Q ((x, y), a)) := by
    intro y
    rw [Measure.map_apply measurable_fst hB, lintegral_indicator_one (measurable_fst hB)]
  simp_rw [h1]
  rw [lintegral_Q_eq M Fd x ρ a _ ((measurable_one.indicator (measurable_fst hB)))]
  rw [← lintegral_indicator hB]
  refine lintegral_congr fun x' => ?_
  by_cases hx : x' ∈ B
  · simp only [Set.indicator, Set.mem_preimage, hx, if_true, Pi.one_apply, mul_one]
    rfl
  · simp [Set.indicator, hx]

lemma bayes (x : EX) (ρ : ProbabilityMeasure EY) (a : A) (F : EX × EY → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ y, ∫⁻ p, F p ∂(M.Q ((x, y), a)) ∂(ρ : Measure EY) =
      ∫⁻ x', ∫⁻ y', F (x', y') ∂(Fd.Phi x ρ a x' : Measure EY) ∂(Fd.QXprime M x ρ a) := by
  have := Fd.hlam_sigmaFinite
  have := Fd.hnu_sigmaFinite
  have hPhim : Measurable fun x' : EX => Fd.Phi x ρ a x' :=
    Fd.hPhi_meas.comp ((measurable_const : Measurable fun _ : EX => (x, ρ)).prodMk
      ((measurable_const : Measurable fun _ : EX => a).prodMk measurable_id))
  have hG : Measurable fun x' => ∫⁻ y', F (x', y') ∂(Fd.Phi x ρ a x' : Measure EY) := by
    have := Measurable.lintegral_kernel_prod_right' (κ := pmKernel (fun x' => Fd.Phi x ρ a x')
      hPhim) hF
    exact this
  rw [lintegral_Q_eq M Fd x ρ a F hF, QXprime_eq M Fd x ρ a,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_Nn M Fd x ρ a) hG]
  have hint : ∫⁻ x', Nn M Fd x ρ a x' ∂Fd.lam ≠ ∞ := by
    have h := isProb_QXprime M Fd x ρ a
    rw [QXprime_eq M Fd x ρ a] at h
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

lemma measurable_Vpi [Nonempty A] (π : Policy EX A) (n : ℕ)
    (hπ : ∀ j < n, Measurable fun p : (ℕ → EX) × (ℕ → A) => π j p.1 p.2) :
    ∀ k j, j + k ≤ n → Measurable fun p : ((ℕ → EX) × (ℕ → A)) × EY =>
      M.Vpi π k j p.1.1 p.1.2 p.2 := by
  have := M.isMarkovQ
  intro k
  induction k with
  | zero =>
    intro j _
    exact measurable_coe_real_ereal.comp (M.hg_meas.comp
      (((measurable_pi_apply j).comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd))
  | succ k ih =>
    intro j hj
    simp only [PartiallyObservableMDM.Vpi]
    have hg : Measurable fun p : ((ℕ → EX) × (ℕ → A)) × EY =>
        ((p.1.1 j, p.2), π j p.1.1 p.1.2) :=
      (((measurable_pi_apply j).comp (measurable_fst.comp measurable_fst)).prodMk
        measurable_snd).prodMk ((hπ j (by omega)).comp measurable_fst)
    have hr : Measurable fun p : ((ℕ → EX) × (ℕ → A)) × EY =>
        ((M.r (p.1.1 j, p.2, π j p.1.1 p.1.2) : ℝ) : EReal) :=
      measurable_coe_real_ereal.comp (M.hr_meas.comp
        (((measurable_pi_apply j).comp (measurable_fst.comp measurable_fst)).prodMk
          (measurable_snd.prodMk ((hπ j (by omega)).comp measurable_fst))))
    refine hr.add (Measurable.const_mul ?_ _)
    have := measurable_erealIntegral_kernel (M.Q.comap _ hg)
      (f := fun p q => M.Vpi π k (j + 1)
        (Function.update p.1.1 (j + 1) q.1) (Function.update p.1.2 j (π j p.1.1 p.1.2)) q.2)
      ((ih (j + 1) (by omega)).comp ((((measurable_update_pair (j + 1)
          (measurable_fst.comp (measurable_fst.comp measurable_fst))
          (measurable_fst.comp measurable_snd))).prodMk
        (measurable_update_pair j (measurable_snd.comp (measurable_fst.comp measurable_fst))
          ((hπ j (by omega)).comp (measurable_fst.comp measurable_fst)))).prodMk
        (measurable_snd.comp measurable_snd)))
    exact this

lemma measurable_VposPi [Nonempty A] (π : Policy EX A) (n : ℕ)
    (hπ : ∀ j < n, Measurable fun p : (ℕ → EX) × (ℕ → A) => π j p.1 p.2) :
    ∀ k j, j + k ≤ n → Measurable fun p : ((ℕ → EX) × (ℕ → A)) × EY =>
      M.VposPi π k j p.1.1 p.1.2 p.2 := by
  have := M.isMarkovQ
  intro k
  induction k with
  | zero =>
    intro j _
    exact ENNReal.measurable_ofReal.comp (M.hg_meas.comp
      (((measurable_pi_apply j).comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd))
  | succ k ih =>
    intro j hj
    simp only [PartiallyObservableMDM.VposPi]
    have hg : Measurable fun p : ((ℕ → EX) × (ℕ → A)) × EY =>
        ((p.1.1 j, p.2), π j p.1.1 p.1.2) :=
      (((measurable_pi_apply j).comp (measurable_fst.comp measurable_fst)).prodMk
        measurable_snd).prodMk ((hπ j (by omega)).comp measurable_fst)
    have hr : Measurable fun p : ((ℕ → EX) × (ℕ → A)) × EY =>
        ENNReal.ofReal (M.r (p.1.1 j, p.2, π j p.1.1 p.1.2)) :=
      ENNReal.measurable_ofReal.comp (M.hr_meas.comp
        (((measurable_pi_apply j).comp (measurable_fst.comp measurable_fst)).prodMk
          (measurable_snd.prodMk ((hπ j (by omega)).comp measurable_fst))))
    refine hr.add (Measurable.const_mul ?_ _)
    have := Measurable.lintegral_kernel_prod_right' (κ := M.Q.comap _ hg)
      (f := fun q : (((ℕ → EX) × (ℕ → A)) × EY) × (EX × EY) => M.VposPi π k (j + 1)
        (Function.update q.1.1.1 (j + 1) q.2.1)
        (Function.update q.1.1.2 j (π j q.1.1.1 q.1.1.2)) q.2.2)
      ((ih (j + 1) (by omega)).comp ((((measurable_update_pair (j + 1)
          (measurable_fst.comp (measurable_fst.comp measurable_fst))
          (measurable_fst.comp measurable_snd))).prodMk
        (measurable_update_pair j (measurable_snd.comp (measurable_fst.comp measurable_fst))
          ((hπ j (by omega)).comp (measurable_fst.comp measurable_fst)))).prodMk
        (measurable_snd.comp measurable_snd)))
    exact this

lemma toENNReal_coe_real (r : ℝ) : ((r : EReal)).toENNReal = ENNReal.ofReal r := by
  rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top r), EReal.toReal_coe]

lemma toENNReal_erealIntegral_le {E : Type*} [MeasurableSpace E] (μ : Measure E) (v : E → EReal) :
    (erealIntegral μ v).toENNReal ≤ ∫⁻ x, (v x).toENNReal ∂μ := by
  unfold erealIntegral
  have : (↑(∫⁻ x, (v x ⊔ 0).toENNReal ∂μ) : EReal) +
      -↑(∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂μ) ≤ ↑(∫⁻ x, (v x ⊔ 0).toENNReal ∂μ) := by
    have h0 : -(↑(∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂μ) : EReal) ≤ 0 := by
      have := EReal.neg_le_neg_iff.mpr (EReal.coe_ennreal_nonneg (∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂μ))
      simpa using this
    simpa using add_le_add_right h0 (↑(∫⁻ x, (v x ⊔ 0).toENNReal ∂μ) : EReal)
  refine (EReal.toENNReal_le_toENNReal this).trans ?_
  rw [EReal.toENNReal_coe]
  simp only [toENNReal_max_zero, le_refl]

lemma Vpi_pos_le [Nonempty A] (π : Policy EX A) :
    ∀ k j xs as y, (M.Vpi π k j xs as y).toENNReal ≤ M.VposPi π k j xs as y := by
  intro k
  induction k with
  | zero => intro j xs as y; exact le_of_eq (toENNReal_coe_real _)
  | succ k ih =>
    intro j xs as y
    simp only [PartiallyObservableMDM.Vpi, PartiallyObservableMDM.VposPi]
    refine EReal.toENNReal_add_le.trans (add_le_add (le_of_eq (toENNReal_coe_real _)) ?_)
    rw [EReal.toENNReal_mul (EReal.coe_nonneg.mpr M.hβ0.le), toENNReal_coe_real]
    exact mul_le_mul_of_nonneg_left ((toENNReal_erealIntegral_le _ _).trans
      (lintegral_mono fun p => ih _ _ _ _)) bot_le

/-! ### The main induction -/

lemma main_induction [Nonempty A] (π : Policy EX A) (n : ℕ)
    (hπ : ∀ j < n, Measurable fun p : (ℕ → EX) × (ℕ → A) => π j p.1 p.2) :
    ∀ k j, j + k ≤ n → ∀ xs as (ρ : ProbabilityMeasure EY),
      ∫⁻ y, M.VposPi π k j xs as y ∂(ρ : Measure EY) ≠ ∞ →
        erealIntegral (ρ : Measure EY) (M.Vpi π k j xs as) =
          FilteredModel.ExPrime M Fd M' π k j xs as ρ := by
  have := M.isMarkovQ
  have hβ := M.hβ0
  have hβ' : ENNReal.ofReal M.β ≠ 0 := by simpa using hβ
  intro k
  induction k with
  | zero => intro j _ xs as ρ _; rfl
  | succ k ih =>
    intro j hj xs as ρ hfin
    -- the integrand of the next stage, as a function of `(x', y')`
    have hupd : Measurable fun p : EX × EY =>
        ((Function.update xs (j + 1) p.1, Function.update as j (π j xs as)), p.2) :=
      ((measurable_update_pair (j + 1) measurable_const measurable_fst).prodMk
        measurable_const).prodMk measurable_snd
    have hVk : Measurable fun p : EX × EY => M.Vpi π k (j + 1)
        (Function.update xs (j + 1) p.1) (Function.update as j (π j xs as)) p.2 :=
      (measurable_Vpi M π n hπ k (j + 1) (by omega)).comp hupd
    have hPk : Measurable fun p : EX × EY => M.VposPi π k (j + 1)
        (Function.update xs (j + 1) p.1) (Function.update as j (π j xs as)) p.2 :=
      (measurable_VposPi M π n hπ k (j + 1) (by omega)).comp hupd
    have hVp : Measurable fun p : EX × EY => (M.Vpi π k (j + 1)
        (Function.update xs (j + 1) p.1) (Function.update as j (π j xs as)) p.2).toENNReal :=
      hVk.ereal_toENNReal
    have hVm : Measurable fun p : EX × EY => (-M.Vpi π k (j + 1)
        (Function.update xs (j + 1) p.1) (Function.update as j (π j xs as)) p.2).toENNReal :=
      hVk.neg.ereal_toENNReal
    have hyk : Measurable fun y : EY => ((xs j, y), π j xs as) :=
      (measurable_const.prodMk measurable_id).prodMk measurable_const
    have hint_y : ∀ {F : EX × EY → ℝ≥0∞}, Measurable F →
        Measurable fun y => ∫⁻ p, F p ∂(M.Q ((xs j, y), π j xs as)) := fun hF =>
      Measurable.lintegral_kernel_prod_right' (κ := M.Q.comap _ hyk) (hF.comp measurable_snd)
    have hPhim : Measurable fun x' : EX => Fd.Phi (xs j) ρ (π j xs as) x' :=
      Fd.hPhi_meas.comp ((measurable_const : Measurable fun _ : EX => (xs j, ρ)).prodMk
        ((measurable_const : Measurable fun _ : EX => π j xs as).prodMk measurable_id))
    have hint_x : ∀ {F : EX × EY → ℝ≥0∞}, Measurable F →
        Measurable fun x' => ∫⁻ y', F (x', y') ∂(Fd.Phi (xs j) ρ (π j xs as) x' : Measure EY) :=
      fun hF => Measurable.lintegral_kernel_prod_right' (κ := pmKernel _ hPhim) hF
    have hrm : Measurable fun y => ENNReal.ofReal (M.r (xs j, y, π j xs as)) :=
      ENNReal.measurable_ofReal.comp (M.hr_meas.comp
        (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
    have hrm' : Measurable fun y => ENNReal.ofReal (-M.r (xs j, y, π j xs as)) :=
      ENNReal.measurable_ofReal.comp (M.hr_meas.comp
        (measurable_const.prodMk (measurable_id.prodMk measurable_const))).neg
    -- finiteness
    have hfin' : ∫⁻ y, ENNReal.ofReal (M.r (xs j, y, π j xs as)) ∂(ρ : Measure EY) +
        ENNReal.ofReal M.β * ∫⁻ y, ∫⁻ p, M.VposPi π k (j + 1)
          (Function.update xs (j + 1) p.1) (Function.update as j (π j xs as)) p.2
          ∂(M.Q ((xs j, y), π j xs as)) ∂(ρ : Measure EY) ≠ ∞ := by
      rw [← lintegral_const_mul _ (hint_y hPk), ← lintegral_add_left hrm]
      exact hfin
    have hr_fin := (ENNReal.add_ne_top.mp hfin').1
    have hPP_fin : ∫⁻ y, ∫⁻ p, M.VposPi π k (j + 1)
          (Function.update xs (j + 1) p.1) (Function.update as j (π j xs as)) p.2
          ∂(M.Q ((xs j, y), π j xs as)) ∂(ρ : Measure EY) ≠ ∞ := by
      intro h
      have := (ENNReal.add_ne_top.mp hfin').2
      rw [h, ENNReal.mul_top hβ'] at this
      exact this rfl
    have hA_fin : ∫⁻ y, ∫⁻ p, (M.Vpi π k (j + 1)
          (Function.update xs (j + 1) p.1) (Function.update as j (π j xs as)) p.2).toENNReal
          ∂(M.Q ((xs j, y), π j xs as)) ∂(ρ : Measure EY) ≠ ∞ :=
      ne_top_of_le_ne_top hPP_fin (lintegral_mono fun y => lintegral_mono fun p =>
        Vpi_pos_le M π k (j + 1) _ _ p.2)
    -- left-hand side
    have hL : erealIntegral (ρ : Measure EY) (M.Vpi π (k + 1) j xs as) =
        ((∫⁻ y, ENNReal.ofReal (M.r (xs j, y, π j xs as)) ∂(ρ : Measure EY) +
          ENNReal.ofReal M.β * ∫⁻ y, ∫⁻ p, (M.Vpi π k (j + 1)
            (Function.update xs (j + 1) p.1) (Function.update as j (π j xs as)) p.2).toENNReal
            ∂(M.Q ((xs j, y), π j xs as)) ∂(ρ : Measure EY) : ℝ≥0∞) : EReal) -
        ((∫⁻ y, ENNReal.ofReal (-M.r (xs j, y, π j xs as)) ∂(ρ : Measure EY) +
          ENNReal.ofReal M.β * ∫⁻ y, ∫⁻ p, (-M.Vpi π k (j + 1)
            (Function.update xs (j + 1) p.1) (Function.update as j (π j xs as)) p.2).toENNReal
            ∂(M.Q ((xs j, y), π j xs as)) ∂(ρ : Measure EY) : ℝ≥0∞) : EReal) := by
      have hpt : M.Vpi π (k + 1) j xs as = fun y =>
          ((ENNReal.ofReal (M.r (xs j, y, π j xs as)) + ENNReal.ofReal M.β *
            ∫⁻ p, (M.Vpi π k (j + 1) (Function.update xs (j + 1) p.1)
              (Function.update as j (π j xs as)) p.2).toENNReal
            ∂(M.Q ((xs j, y), π j xs as)) : ℝ≥0∞) : EReal) -
          ((ENNReal.ofReal (-M.r (xs j, y, π j xs as)) + ENNReal.ofReal M.β *
            ∫⁻ p, (-M.Vpi π k (j + 1) (Function.update xs (j + 1) p.1)
              (Function.update as j (π j xs as)) p.2).toENNReal
            ∂(M.Q ((xs j, y), π j xs as)) : ℝ≥0∞) : EReal) := by
        funext y
        show (M.r (xs j, y, π j xs as) : EReal) + (M.β : EReal) *
          erealIntegral (M.Q ((xs j, y), π j xs as)) (fun p => M.Vpi π k (j + 1)
            (Function.update xs (j + 1) p.1) (Function.update as j (π j xs as)) p.2) = _
        rw [erealIntegral_eq_sub, ereal_split _ _ hβ]
      have hAy : Measurable fun y => ∫⁻ p, (M.Vpi π k (j + 1) (Function.update xs (j + 1) p.1)
          (Function.update as j (π j xs as)) p.2).toENNReal ∂(M.Q ((xs j, y), π j xs as)) :=
        hint_y hVp
      have hBy : Measurable fun y => ∫⁻ p, (-M.Vpi π k (j + 1) (Function.update xs (j + 1) p.1)
          (Function.update as j (π j xs as)) p.2).toENNReal ∂(M.Q ((xs j, y), π j xs as)) :=
        hint_y hVm
      have hA' : Measurable fun y => ENNReal.ofReal (M.r (xs j, y, π j xs as)) +
          ENNReal.ofReal M.β * ∫⁻ p, (M.Vpi π k (j + 1) (Function.update xs (j + 1) p.1)
          (Function.update as j (π j xs as)) p.2).toENNReal ∂(M.Q ((xs j, y), π j xs as)) :=
        hrm.add (hAy.const_mul _)
      have hB' : Measurable fun y => ENNReal.ofReal (-M.r (xs j, y, π j xs as)) +
          ENNReal.ofReal M.β * ∫⁻ p, (-M.Vpi π k (j + 1) (Function.update xs (j + 1) p.1)
          (Function.update as j (π j xs as)) p.2).toENNReal ∂(M.Q ((xs j, y), π j xs as)) :=
        hrm'.add (hBy.const_mul _)
      rw [hpt, erealIntegral_sub _ hA' hB', lintegral_add_left hrm,
        lintegral_const_mul _ hAy, lintegral_add_left hrm',
        lintegral_const_mul _ hBy]
      rw [lintegral_add_left hrm, lintegral_const_mul _ hAy]
      exact ENNReal.add_ne_top.mpr ⟨hr_fin, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA_fin⟩
    -- right-hand side, reward part
    have hR1 : FilteredModel.rprime M (xs j, ρ) (π j xs as) =
        ((∫⁻ y, ENNReal.ofReal (M.r (xs j, y, π j xs as)) ∂(ρ : Measure EY) : ℝ≥0∞) : EReal) -
        ((∫⁻ y, ENNReal.ofReal (-M.r (xs j, y, π j xs as)) ∂(ρ : Measure EY) : ℝ≥0∞) : EReal) := by
      rw [FilteredModel.rprime, erealIntegral_eq_sub]
      simp only [← EReal.coe_neg, toENNReal_coe_real]
    -- right-hand side, continuation part
    have hW : Measurable fun e' : EX × ProbabilityMeasure EY =>
        FilteredModel.ExPrime M Fd M' π k (j + 1) (Function.update xs (j + 1) e'.1)
          (Function.update as j (π j xs as)) e'.2 :=
      (measurable_ExPrime M Fd M' π n hπ k (j + 1) (by omega)).comp
        (((measurable_update_pair (j + 1) measurable_const measurable_fst).prodMk
          measurable_const).prodMk measurable_snd)
    have hbP := bayes M Fd (xs j) ρ (π j xs as) _ hPk
    have hbVp := bayes M Fd (xs j) ρ (π j xs as) _ hVp
    have hbVm := bayes M Fd (xs j) ρ (π j xs as) _ hVm
    simp only at hbP hbVp hbVm
    have hR2 : erealIntegral (M'.Qprime ((xs j, ρ), π j xs as)) (fun e' =>
        FilteredModel.ExPrime M Fd M' π k (j + 1) (Function.update xs (j + 1) e'.1)
          (Function.update as j (π j xs as)) e'.2) =
        ((∫⁻ y, ∫⁻ p, (M.Vpi π k (j + 1)
            (Function.update xs (j + 1) p.1) (Function.update as j (π j xs as)) p.2).toENNReal
            ∂(M.Q ((xs j, y), π j xs as)) ∂(ρ : Measure EY) : ℝ≥0∞) : EReal) -
        ((∫⁻ y, ∫⁻ p, (-M.Vpi π k (j + 1)
            (Function.update xs (j + 1) p.1) (Function.update as j (π j xs as)) p.2).toENNReal
            ∂(M.Q ((xs j, y), π j xs as)) ∂(ρ : Measure EY) : ℝ≥0∞) : EReal) := by
      rw [M'.hQprime, erealIntegral_map _ (measurable_graph M Fd _ _ _) hW]
      have hae : ∀ᵐ x' ∂(Fd.QXprime M (xs j) ρ (π j xs as)),
          ∫⁻ y', M.VposPi π k (j + 1) (Function.update xs (j + 1) x')
            (Function.update as j (π j xs as)) y'
            ∂(Fd.Phi (xs j) ρ (π j xs as) x' : Measure EY) < ∞ := by
        refine ae_lt_top (hint_x hPk) ?_
        rw [← hbP]; exact hPP_fin
      have hcongr : ((fun e' : EX × ProbabilityMeasure EY =>
          FilteredModel.ExPrime M Fd M' π k (j + 1) (Function.update xs (j + 1) e'.1)
            (Function.update as j (π j xs as)) e'.2) ∘
            fun x' => (x', Fd.Phi (xs j) ρ (π j xs as) x')) =ᵐ[Fd.QXprime M (xs j) ρ (π j xs as)]
          fun x' => ((∫⁻ y', (M.Vpi π k (j + 1) (Function.update xs (j + 1) x')
              (Function.update as j (π j xs as)) y').toENNReal
              ∂(Fd.Phi (xs j) ρ (π j xs as) x' : Measure EY) : ℝ≥0∞) : EReal) -
            ((∫⁻ y', (-M.Vpi π k (j + 1) (Function.update xs (j + 1) x')
              (Function.update as j (π j xs as)) y').toENNReal
              ∂(Fd.Phi (xs j) ρ (π j xs as) x' : Measure EY) : ℝ≥0∞) : EReal) := by
        filter_upwards [hae] with x' hx'
        have := ih (j + 1) (by omega) (Function.update xs (j + 1) x')
          (Function.update as j (π j xs as)) (Fd.Phi (xs j) ρ (π j xs as) x') hx'.ne
        rw [Function.comp_apply, ← this, erealIntegral_eq_sub]
      rw [erealIntegral_congr_ae _ hcongr, erealIntegral_sub _ (hint_x hVp) (hint_x hVm),
        ← hbVp, ← hbVm]
      rw [← hbVp]; exact hA_fin
    rw [hL]
    simp only [FilteredModel.ExPrime]
    rw [hR1, hR2, ereal_recombine _ hβ _ _ _ _ hr_fin hA_fin]

end Sol532

end MDPFinance.POMDP

open MDPFinance.POMDP in
theorem solution {EX EY A : Type*} [MeasurableSpace EX] [MeasurableSpace EY]
    [MeasurableSpace A] [Nonempty A] (M : PartiallyObservableMDM EX EY A) (Fd : FilterData M)
    (M' : FilteredModel M Fd) (N : ℕ) (hInt : M.IntegrabilityAssumption N)
    (π : Policy EX A) (hπ : M.IsPolicy N π) (x : EX) :
    M.JNpi π N x = FilteredModel.JprimeNpi M Fd M' π N x ⟨M.Q0, M.isProbQ0⟩ ∧
      M.JN N x = FilteredModel.Jprime M Fd M' N x ⟨M.Q0, M.isProbQ0⟩ := by
  have key : ∀ π' : Policy EX A, M.IsPolicy N π' →
      M.JNpi π' N x = FilteredModel.JprimeNpi M Fd M' π' N x ⟨M.Q0, M.isProbQ0⟩ := by
    intro π' hπ'
    have hfin : ∫⁻ y0, M.VposPi π' N 0 (fun _ => x) (fun _ => Classical.arbitrary A) y0 ∂M.Q0
        ≠ ∞ := by
      refine ne_top_of_le_ne_top (hInt x).ne ?_
      exact le_iSup₂_of_le (f := fun π (_ : π ∈ {π : Policy EX A | M.IsPolicy N π}) =>
        ∫⁻ y0 : EY, M.VposPi π N 0 (fun _ => x) (fun _ => Classical.arbitrary A) y0 ∂M.Q0)
        π' hπ' le_rfl
    exact Sol532.main_induction M Fd M' π' N (fun j hj => (hπ' j hj).1) N 0 (by omega) _ _
      ⟨M.Q0, M.isProbQ0⟩ hfin
  refine ⟨key π hπ, ?_⟩
  unfold PartiallyObservableMDM.JN FilteredModel.Jprime
  exact iSup_congr fun π' => iSup_congr fun hπ' => key π' hπ'
