-- Prove2me | solution 1 for LearnStability.ERMLOO.theorem31
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T19:43:38.362982+00:00
-- url     : https://prove2.me/submissions/59c0912f-7a14-4745-a85c-24cd30f831f2

import Mathlib
import Definitions.Def_LearnStability_ERMLOO_Setting
import Definitions.Def_LearnStability_ERMLOO_RuleProperties

/-! e1a6c9b8 LearnStability.ERMLOO.theorem31 (Shalev-Shwartz, Shamir, Srebro, Sridharan 2010, Thm 31).
Write `G_n = E F(A_n(S))`, `e_m = E F_S(A_m(S)) = E min_h F_S(h)`, `F* = inf F`.
* `c_n = G_n - F* >= 0` (consistency gap), `δ_m = F* - e_m >= 0` (ERM optimism).
* For an exact ERM, `f(A(S^{\i}); z_i) >= f(A(S); z_i)` pointwise, so the absolute value in LOO
  stability disappears and `LOO_{n+1} = c_n + δ_{n+1}`; the on-average gap is `c_m + δ_m`.
* Universal consistency bounds `δ_m` (empirical-distribution trick + exchangeability), and a
  second-moment bound controls the negative part of the gap.  -/

set_option autoImplicit false

namespace LearnStability.ERMLOO.T31Proof

open MeasureTheory Filter Topology LearnStability.ERMLOO

variable {H Z : Type*} [MeasurableSpace Z]

/-! ### Elementary bounds -/

lemma abs_empRisk_le {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) {m : ℕ} (hm : 1 ≤ m)
    (S : Fin m → Z) (h : H) : |empRisk f S h| ≤ B := by
  unfold empRisk
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  rw [abs_div, abs_of_pos hm', div_le_iff₀ hm']
  calc |∑ i, f h (S i)| ≤ ∑ i, |f h (S i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, B := Finset.sum_le_sum fun i _ => hP.bounded h (S i)
    _ = B * m := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]

lemma bddBelow_empRisk {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) {m : ℕ}
    (hm : 1 ≤ m) (S : Fin m → Z) : BddBelow (Set.range fun h => empRisk f S h) :=
  ⟨-B, by rintro _ ⟨h, rfl⟩; exact (abs_le.mp (abs_empRisk_le hP hm S h)).1⟩

lemma ermValue_le {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) {m : ℕ} (hm : 1 ≤ m)
    (S : Fin m → Z) (h : H) : ermValue f S ≤ empRisk f S h :=
  ciInf_le (bddBelow_empRisk hP hm S) h

lemma neg_le_ermValue [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    {m : ℕ} (hm : 1 ≤ m) (S : Fin m → Z) : -B ≤ ermValue f S :=
  le_ciInf fun h => (abs_le.mp (abs_empRisk_le hP hm S h)).1

lemma integrable_of_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {g : α → ℝ} (hg : Measurable g) (C : ℝ) (hC : ∀ x, |g x| ≤ C) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable C
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)

lemma abs_risk_le {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) (D : Measure Z)
    [IsProbabilityMeasure D] (h : H) : |risk f D h| ≤ B := by
  unfold risk
  have := norm_integral_le_of_norm_le_const (μ := D) (f := f h) (C := B)
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hP.bounded h z)
  rw [Real.norm_eq_abs] at this
  simpa using this

lemma measurable_empRisk_rule {f : H → Z → ℝ} {A : Rule H Z} (hA : MeasurableRule f A)
    {m k : ℕ} {φ : (Fin m → Z) → (Fin k → Z)} (hφ : Measurable φ) :
    Measurable (fun S : Fin m → Z => empRisk f S (A k (φ S))) := by
  unfold empRisk
  refine Measurable.div_const ?_ _
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (hA k).comp (hφ.prodMk (measurable_pi_apply i))

lemma measurable_risk_rule {f : H → Z → ℝ} {A : Rule H Z} (hA : MeasurableRule f A)
    (D : Measure Z) [SFinite D] (m : ℕ) : Measurable (fun S : Fin m → Z => risk f D (A m S)) :=
  ((hA m).stronglyMeasurable.integral_prod_right' (ν := D)).measurable

lemma measurable_ermValue {f : H → Z → ℝ} {A : Rule H Z} (hA : MeasurableRule f A)
    (hERM : IsERMRule f A) {m : ℕ} (hm : 1 ≤ m) :
    Measurable (fun S : Fin m → Z => ermValue f S) := by
  have h := measurable_empRisk_rule hA (m := m) (k := m) (φ := id) measurable_id
  have e : (fun S : Fin m → Z => ermValue f S) = fun S => empRisk f S (A m (id S)) :=
    funext fun S => (hERM m hm S).symm
  rw [e]
  exact h

lemma integral_empRisk {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) (D : Measure Z)
    [IsProbabilityMeasure D] {m : ℕ} (hm : 1 ≤ m) (h : H) :
    ∫ S, empRisk f S h ∂(Measure.pi fun _ : Fin m => D) = risk f D h := by
  have hm' : (m:ℝ) ≠ 0 := by
    have : (0:ℝ) < m := by exact_mod_cast hm
    exact this.ne'
  have hi : ∀ i : Fin m, Integrable (fun S : Fin m → Z => f h (S i))
      (Measure.pi fun _ : Fin m => D) := fun i =>
    integrable_of_abs_le ((hP.measurable h).comp (measurable_pi_apply i)) B
      fun S => hP.bounded _ _
  have h1 : ∀ i : Fin m, ∫ S, f h (S i) ∂(Measure.pi fun _ : Fin m => D) = risk f D h :=
    fun i => integral_comp_eval (hP.measurable h).aestronglyMeasurable
  have hsum : ∫ S, ∑ i, f h (S i) ∂(Measure.pi fun _ : Fin m => D)
      = ∑ i, ∫ S, f h (S i) ∂(Measure.pi fun _ : Fin m => D) :=
    integral_finsetSum _ fun i _ => hi i
  unfold empRisk
  rw [integral_div, hsum, Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_cancel_left₀ _ hm']

lemma measurable_empRisk_const {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) (m : ℕ)
    (h : H) : Measurable (fun S : Fin m → Z => empRisk f S h) := by
  unfold empRisk
  exact Measurable.div_const
    (Finset.measurable_sum _ fun i _ => (hP.measurable h).comp (measurable_pi_apply i)) _

lemma abs_integral_le_of_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {g : α → ℝ} {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    |∫ x, g x ∂μ| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := g) (C := C)
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC z)
  rw [Real.norm_eq_abs] at this
  simpa using this

lemma B_nonneg [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    (D : Measure Z) [IsProbabilityMeasure D] : 0 ≤ B := by
  have hZ : Nonempty Z := by
    by_contra hZ
    rw [not_nonempty_iff] at hZ
    have h1 := measure_univ (μ := D)
    rw [Measure.eq_zero_of_isEmpty D] at h1
    simp at h1
  exact (abs_nonneg _).trans (hP.bounded (Classical.arbitrary H) (Classical.arbitrary Z))

/-! ### Marginals of the product measure -/

lemma comp_inj_mp {ι κ : Type*} [Fintype ι] [Fintype κ] (D : Measure Z) [IsProbabilityMeasure D]
    (g : κ → ι) (hg : Function.Injective g) :
    MeasurePreserving (fun S : ι → Z => fun a => S (g a)) (Measure.pi fun _ : ι => D)
      (Measure.pi fun _ : κ => D) := by
  have hm : Measurable (fun S : ι → Z => fun a => S (g a)) :=
    measurable_pi_lambda _ fun a => measurable_pi_apply (g a)
  refine ⟨hm, ?_⟩
  have hind : ProbabilityTheory.iIndepFun (fun (i : ι) (ω : ι → Z) => (id : Z → Z) (ω i))
      (Measure.pi fun _ : ι => D) :=
    ProbabilityTheory.iIndepFun_pi (μ := fun _ : ι => D) (X := fun _ => (id : Z → Z)) (fun _ => aemeasurable_id)
  have h2 : ProbabilityTheory.iIndepFun (fun (a : κ) (ω : ι → Z) => ω (g a)) (Measure.pi fun _ : ι => D) :=
    hind.precomp hg
  have h3 := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map (μ := Measure.pi fun _ : ι => D)
    (f := fun (a : κ) (ω : ι → Z) => ω (g a))
    (fun a => (measurable_pi_apply (g a)).aemeasurable)).mp h2
  rw [h3]
  congr 1
  funext a
  exact (measurePreserving_eval (fun _ : ι => D) (g a)).map_eq

lemma prefix_term {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) {A : Rule H Z}
    (hA : MeasurableRule f A) (D : Measure Z) [IsProbabilityMeasure D] {m k : ℕ} (hkm : k ≤ m)
    (j : Fin m) (hj : k ≤ j.val) :
    ∫ S, f (A k (fun a => S (Fin.castLE hkm a))) (S j) ∂(Measure.pi fun _ : Fin m => D)
      = ∫ T, risk f D (A k T) ∂(Measure.pi fun _ : Fin k => D) := by
  classical
  let g : Option (Fin k) → Fin m := fun o => o.elim j (Fin.castLE hkm)
  have hg : Function.Injective g := by
    rintro (_ | a) (_ | b) hab
    · rfl
    · exfalso
      have h1 : j.val = b.val := congrArg Fin.val hab
      have := b.isLt
      omega
    · exfalso
      have h1 : a.val = j.val := congrArg Fin.val hab
      have := a.isLt
      omega
    · have := Fin.castLE_injective hkm hab
      rw [this]
  set J := MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin k) => Z) with hJdef
  have hJs : MeasurePreserving J.symm ((Measure.pi fun _ : Fin k => D).prod D)
      (Measure.pi fun _ : Option (Fin k) => D) :=
    ⟨J.symm.measurable, Measure.pi_map_piOptionEquivProd (fun _ : Option (Fin k) => D)⟩
  have hJ : MeasurePreserving J (Measure.pi fun _ : Option (Fin k) => D)
      ((Measure.pi fun _ : Fin k => D).prod D) := MeasurePreserving.symm J.symm hJs
  have hc := hJ.comp (comp_inj_mp D g hg)
  have hφ : Measurable (fun p : (Fin k → Z) × Z => f (A k p.1) p.2) := hA k
  have hI : Integrable (fun p : (Fin k → Z) × Z => f (A k p.1) p.2)
      ((Measure.pi fun _ : Fin k => D).prod D) :=
    integrable_of_abs_le hφ B fun p => hP.bounded _ _
  have h1 : ∫ p, f (A k p.1) p.2 ∂((Measure.pi fun _ : Fin k => D).prod D)
      = ∫ S, f (A k (fun a => S (Fin.castLE hkm a))) (S j) ∂(Measure.pi fun _ : Fin m => D) := by
    have := integral_map (μ := Measure.pi fun _ : Fin m => D) hc.measurable.aemeasurable
      (f := fun p : (Fin k → Z) × Z => f (A k p.1) p.2)
      (by rw [hc.map_eq]; exact hI.aestronglyMeasurable)
    rw [hc.map_eq] at this
    exact this
  rw [← h1, integral_prod _ hI]
  rfl

lemma prefix_lower [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    {A : Rule H Z} (hA : MeasurableRule f A) (D : Measure Z) [IsProbabilityMeasure D]
    {m k : ℕ} (hm : 1 ≤ m) (hkm : k ≤ m) :
    (∫ T, risk f D (A k T) ∂(Measure.pi fun _ : Fin k => D)) - 2 * B * k / m ≤
      ∫ S, empRisk f S (A k (fun a => S (Fin.castLE hkm a)))
        ∂(Measure.pi fun _ : Fin m => D) := by
  classical
  have hB := B_nonneg hP D
  set G := ∫ T, risk f D (A k T) ∂(Measure.pi fun _ : Fin k => D) with hG
  have hGB : G ≤ B :=
    (abs_le.mp (abs_integral_le_of_bound (fun T => abs_risk_le hP D (A k T)))).2
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  set μ := Measure.pi fun _ : Fin m => D with hμ
  have hint : ∀ j : Fin m,
      Integrable (fun S : Fin m → Z => f (A k (fun a => S (Fin.castLE hkm a))) (S j)) μ := by
    intro j
    have hpair : Measurable (fun S : Fin m → Z => ((fun a => S (Fin.castLE hkm a), S j) :
        (Fin k → Z) × Z)) :=
      (measurable_pi_lambda _ fun a => measurable_pi_apply _).prodMk (measurable_pi_apply j)
    have hm : Measurable (fun S : Fin m → Z => f (A k (fun a => S (Fin.castLE hkm a))) (S j)) :=
      (hA k).comp hpair
    exact integrable_of_abs_le hm B fun S => hP.bounded _ _
  have hterm : ∀ j : Fin m, G - (if j.val < k then 2 * B else 0) ≤
      ∫ S, f (A k (fun a => S (Fin.castLE hkm a))) (S j) ∂μ := by
    intro j
    by_cases hj : j.val < k
    · rw [if_pos hj]
      have := (abs_le.mp (abs_integral_le_of_bound (μ := μ)
        (g := fun S : Fin m → Z => f (A k (fun a => S (Fin.castLE hkm a))) (S j)) (C := B)
        fun S => hP.bounded _ _)).1
      linarith
    · rw [if_neg hj, prefix_term hP hA D hkm j (not_lt.mp hj)]
      linarith
  have hsum : ∫ S, empRisk f S (A k (fun a => S (Fin.castLE hkm a))) ∂μ =
      (∑ j, ∫ S, f (A k (fun a => S (Fin.castLE hkm a))) (S j) ∂μ) / m := by
    unfold empRisk
    rw [integral_div, integral_finsetSum _ fun j _ => hint j]
  have hcount : ((Finset.univ.filter fun j : Fin m => j.val < k).card : ℝ) ≤ k := by
    have : (Finset.univ.filter fun j : Fin m => j.val < k).card ≤ (Finset.range k).card :=
      Finset.card_le_card_of_injOn (fun j => j.val) (fun j hj => by simpa using hj)
        (fun a _ b _ h => Fin.ext h)
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hcs : ∑ j : Fin m, (if j.val < k then 2 * B else 0) =
      2 * B * (Finset.univ.filter fun j : Fin m => j.val < k).card := by
    rw [← Finset.sum_filter]
    simp [Finset.sum_const, mul_comm]
  have hlow : (m:ℝ) * G - 2 * B * k ≤
      ∑ j, ∫ S, f (A k (fun a => S (Fin.castLE hkm a))) (S j) ∂μ := by
    have h1 := Finset.sum_le_sum (fun (j : Fin m) (_ : j ∈ Finset.univ) => hterm j)
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hcs] at h1
    have h2 := mul_le_mul_of_nonneg_left hcount (by positivity : (0:ℝ) ≤ 2 * B)
    linarith
  rw [hsum]
  have e : G - 2 * B * k / m = ((m:ℝ) * G - 2 * B * k) / m := by
    field_simp
  rw [e]
  exact div_le_div_of_nonneg_right hlow hmpos.le


/-! ### Exchangeability (ported) -/

omit [MeasurableSpace Z] in
lemma empRisk_comp_perm (f : H → Z → ℝ) {m : ℕ} (S : Fin m → Z) (π : Equiv.Perm (Fin m))
    (h : H) : empRisk f (fun i => S (π i)) h = empRisk f S h := by
  unfold empRisk
  congr 1
  exact Equiv.sum_comp π (fun i => f h (S i))

omit [MeasurableSpace Z] in
lemma ermValue_comp_perm (f : H → Z → ℝ) {m : ℕ} (S : Fin m → Z) (π : Equiv.Perm (Fin m)) :
    ermValue f (fun i => S (π i)) = ermValue f S := by
  unfold ermValue
  exact congrArg iInf (funext fun h => empRisk_comp_perm f S π h)

lemma perm_mp {ι : Type*} [Fintype ι] (D : Measure Z) [SigmaFinite D] (π : Equiv.Perm ι) :
    MeasurePreserving (fun x : ι → Z => fun i => x (π i)) (Measure.pi fun _ => D)
      (Measure.pi fun _ => D) := by
  have hmeas : Measurable (fun x : ι → Z => fun i => x (π i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (π i)
  refine ⟨hmeas, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have : (fun x : ι → Z => fun i => x (π i)) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i => s (π.symm i)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h i
      have := h (π.symm i)
      simpa using this
    · intro h i
      have := h (π i)
      simpa using this
  rw [this, Measure.pi_pi]
  exact Equiv.prod_comp π.symm (fun i => D (s i))

lemma integral_comp_perm {ι : Type*} [Fintype ι] (D : Measure Z) [SigmaFinite D]
    (π : Equiv.Perm ι) {g : (ι → Z) → ℝ} (hg : Measurable g) :
    ∫ x, g (fun i => x (π i)) ∂(Measure.pi fun _ => D) = ∫ x, g x ∂(Measure.pi fun _ => D) := by
  have hmp := perm_mp D π
  have h := integral_map (μ := Measure.pi fun _ : ι => D) hmp.measurable.aemeasurable
    (f := g) (by rw [hmp.map_eq]; exact hg.aestronglyMeasurable)
  rw [hmp.map_eq] at h
  exact h.symm

lemma exists_perm_ext {k m : ℕ} (ι : Fin k → Fin m) (hι : Function.Injective ι)
    (σ : Fin k ↪ Fin m) : ∃ π : Equiv.Perm (Fin m), ∀ j, π (ι j) = σ j := by
  classical
  let e : {x // x ∈ Set.range ι} ≃ {x // x ∈ Set.range σ} :=
    (Equiv.ofInjective ι hι).symm.trans (Equiv.ofInjective σ σ.injective)
  refine ⟨e.extendSubtype, fun j => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem e (ι j) ⟨j, rfl⟩]
  simp [e, Equiv.ofInjective_symm_apply]

/-! ### Part 3: stability + AERM ⟹ consistency -/

lemma kk_le (m : ℕ) : Nat.sqrt (Nat.sqrt m) ≤ m := (Nat.sqrt_le_self _).trans (Nat.sqrt_le_self _)

/-- The gap between the empirical risk of `A` run on the resampled sample `S ∘ τ` and the
minimal empirical risk. -/
noncomputable def gap (f : H → Z → ℝ) (A : Rule H Z) {m k : ℕ} (S : Fin m → Z)
    (τ : Fin k → Fin m) : ℝ :=
  empRisk f S (A k (fun j => S (τ j))) - ermValue f S

omit [MeasurableSpace Z] in
lemma gap_perm (f : H → Z → ℝ) (A : Rule H Z) {m k : ℕ} (S : Fin m → Z)
    (π : Equiv.Perm (Fin m)) (ι σ : Fin k → Fin m) (hπ : ∀ j, π (ι j) = σ j) :
    gap f A (fun i => S (π i)) ι = gap f A S σ := by
  simp only [gap, empRisk_comp_perm, ermValue_comp_perm, hπ]

lemma measurable_gap {f : H → Z → ℝ} {A : Rule H Z}
    (hA : MeasurableRule f A) (hERM : IsERMRule f A) {m k : ℕ} (hm : 1 ≤ m) (τ : Fin k → Fin m) :
    Measurable (fun S : Fin m → Z => gap f A S τ) :=
  (measurable_empRisk_rule hA (measurable_pi_lambda _ fun j => measurable_pi_apply (τ j))).sub
    (measurable_ermValue hA hERM hm)

lemma gap_nonneg {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) {A : Rule H Z}
    {m k : ℕ} (hm : 1 ≤ m) (S : Fin m → Z) (τ : Fin k → Fin m) : 0 ≤ gap f A S τ :=
  sub_nonneg.mpr (ermValue_le hP hm S _)

lemma gap_le [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    {A : Rule H Z} {m k : ℕ} (hm : 1 ≤ m) (S : Fin m → Z) (τ : Fin k → Fin m) :
    gap f A S τ ≤ 2 * B := by
  have h1 := (abs_le.mp (abs_empRisk_le hP hm S (A k (fun j => S (τ j))))).2
  have h2 := neg_le_ermValue hP hm S
  unfold gap
  linarith

lemma unif_real_singleton {m : ℕ} [Nonempty (Fin m)] (i : Fin m) :
    (PMF.uniformOfFintype (Fin m)).toMeasure.real {i} = (m:ℝ)⁻¹ := by
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i),
    PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv, ENNReal.toReal_natCast]

lemma pi_unif_real_singleton {m k : ℕ} [Nonempty (Fin m)] (τ : Fin k → Fin m) :
    (Measure.pi fun _ : Fin k => (PMF.uniformOfFintype (Fin m)).toMeasure).real {τ}
      = ((m:ℝ)⁻¹) ^ k := by
  have : ({τ} : Set (Fin k → Fin m)) = Set.univ.pi (fun j => {τ j}) := by
    ext x
    simp [funext_iff]
  rw [measureReal_def, this, Measure.pi_pi, ENNReal.toReal_prod]
  have h1 : ∀ j : Fin k, ((PMF.uniformOfFintype (Fin m)).toMeasure {τ j}).toReal = (m:ℝ)⁻¹ :=
    fun j => unif_real_singleton (τ j)
  simp only [h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma risk_empMeasure (f : H → Z → ℝ) (hf : ∀ h, Measurable (f h)) {m : ℕ} [Nonempty (Fin m)]
    (S : Fin m → Z) (h : H) :
    risk f ((PMF.uniformOfFintype (Fin m)).toMeasure.map S) h = empRisk f S h := by
  unfold risk empRisk
  rw [integral_map (measurable_of_countable S).aemeasurable (hf h).aestronglyMeasurable,
    integral_fintype (Integrable.of_finite (μ := (PMF.uniformOfFintype (Fin m)).toMeasure))]
  simp only [unif_real_singleton, smul_eq_mul]
  rw [← Finset.mul_sum, inv_mul_eq_div]

/-- Consistency of `A` under the empirical distribution of `S`. -/
lemma empirical_consistency [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    {A : Rule H Z} (hA : MeasurableRule f A) {εc : ℕ → ℝ} (hc : UniversallyConsistent f A εc)
    {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (S : Fin m → Z) :
    ∑ τ : Fin k → Fin m, gap f A S τ ≤ (m:ℝ) ^ k * εc k := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hSm : Measurable S := measurable_of_countable S
  have : IsProbabilityMeasure ((PMF.uniformOfFintype (Fin m)).toMeasure.map S) :=
    Measure.isProbabilityMeasure_map hSm.aemeasurable
  have hrisk : ∀ h : H, risk f ((PMF.uniformOfFintype (Fin m)).toMeasure.map S) h
      = empRisk f S h := fun h => risk_empMeasure f hP.measurable S h
  have hopt : optRisk f ((PMF.uniformOfFintype (Fin m)).toMeasure.map S) = ermValue f S := by
    unfold optRisk ermValue
    exact congrArg iInf (funext hrisk)
  have hcons := hc ((PMF.uniformOfFintype (Fin m)).toMeasure.map S) inferInstance k hk
  unfold sampleLaw at hcons
  simp only [hrisk, hopt] at hcons
  have hpi : (Measure.pi fun _ : Fin k => (PMF.uniformOfFintype (Fin m)).toMeasure.map S) =
      (Measure.pi fun _ : Fin k => (PMF.uniformOfFintype (Fin m)).toMeasure).map
        (fun τ j => S (τ j)) :=
    (Measure.pi_map_pi (fun _ => hSm.aemeasurable)).symm
  have hmeasT : Measurable (fun T : Fin k → Z => empRisk f S (A k T) - ermValue f S) := by
    refine Measurable.sub_const ?_ _
    unfold empRisk
    refine Measurable.div_const ?_ _
    exact Finset.measurable_sum _ fun i _ => (hA k).comp (measurable_id.prodMk measurable_const)
  rw [hpi, integral_map (measurable_of_countable (fun τ : Fin k → Fin m => fun j => S (τ j))).aemeasurable
    hmeasT.aestronglyMeasurable] at hcons
  rw [integral_fintype (Integrable.of_finite
    (μ := Measure.pi fun _ : Fin k => (PMF.uniformOfFintype (Fin m)).toMeasure))] at hcons
  simp only [pi_unif_real_singleton, smul_eq_mul] at hcons
  rw [← Finset.mul_sum] at hcons
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  have e : ∑ τ : Fin k → Fin m, gap f A S τ =
      (m:ℝ) ^ k * ((m:ℝ)⁻¹ ^ k * ∑ τ : Fin k → Fin m, gap f A S τ) := by
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hmpos.ne', one_pow, one_mul]
  rw [e]
  exact mul_le_mul_of_nonneg_left hcons (by positivity)

lemma two_k_bound {k m : ℕ} (h : k * k * (k * k) ≤ m) : 2 * (k * (k - 1)) ≤ m := by
  rcases k with _ | _ | k
  · simp
  · simp
  · have e : k + 1 + 1 - 1 = k + 1 := rfl
    rw [e]
    nlinarith

lemma card_bound {m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) (h4 : 2 * (k * (k - 1)) ≤ m) :
    (m:ℝ) ^ k ≤ 2 * (m.descFactorial k : ℝ) := by
  have hm : (0:ℝ) < m := by exact_mod_cast (lt_of_lt_of_le hk hkm)
  have h1 : ((m + 1 - k : ℕ) : ℝ) ^ k ≤ m.descFactorial k := by
    exact_mod_cast Nat.pow_sub_le_descFactorial m k
  have hcast : ((m + 1 - k : ℕ) : ℝ) = m * (1 + (-(((k:ℝ) - 1) / m))) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    field_simp
    ring
  have hkm' : (k:ℝ) ≤ m := by exact_mod_cast hkm
  have hx : (-2:ℝ) ≤ -(((k:ℝ) - 1) / m) := by
    have : ((k:ℝ) - 1) / m ≤ 1 := by
      rw [div_le_one hm]
      linarith
    linarith
  have hb := one_add_mul_le_pow hx k
  have h4' : (2:ℝ) * (k * ((k:ℝ) - 1)) ≤ m := by
    have := (Nat.cast_le (α := ℝ)).mpr h4
    push_cast [Nat.cast_sub hk] at this
    linarith
  have hhalf : (1:ℝ) / 2 ≤ 1 + k * (-(((k:ℝ) - 1) / m)) := by
    have : (k:ℝ) * (((k:ℝ) - 1) / m) ≤ 1 / 2 := by
      rw [← mul_div_assoc, div_le_iff₀ hm]
      linarith
    linarith
  calc (m:ℝ) ^ k = m ^ k * 1 := by ring
    _ ≤ m ^ k * (2 * (1 + (-(((k:ℝ) - 1) / m))) ^ k) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [hb, hhalf]
    _ = 2 * ((m + 1 - k : ℕ) : ℝ) ^ k := by rw [hcast, mul_pow]; ring
    _ ≤ 2 * m.descFactorial k := by linarith [h1]

lemma aerm_core [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    (A : Rule H Z) (εc : ℕ → ℝ) (hA : MeasurableRule f A) (hERM : IsERMRule f A)
    (hc : UniversallyConsistent f A εc)
    (D : Measure Z) [IsProbabilityMeasure D] {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (hkm : k ≤ m)
    (hcard : (m:ℝ) ^ k ≤ 2 * (m.descFactorial k : ℝ)) (hεk : 0 ≤ εc k) :
    ∫ S, (empRisk f S (A k (fun j => S (Fin.castLE hkm j))) - ermValue f S)
      ∂(Measure.pi fun _ : Fin m => D) ≤ 2 * εc k := by
  classical
  have hGi : ∀ τ : Fin k → Fin m,
      Integrable (fun S : Fin m → Z => gap f A S τ) (Measure.pi fun _ : Fin m => D) :=
    fun τ => integrable_of_abs_le (measurable_gap hA hERM hm τ) (2 * B) fun S => by
      rw [abs_of_nonneg (gap_nonneg hP hm S τ)]
      exact gap_le hP hm S τ
  have hexch : ∀ σ : Fin k ↪ Fin m, ∫ S, gap f A S σ ∂(Measure.pi fun _ : Fin m => D) =
      ∫ S, gap f A S (Fin.castLE hkm) ∂(Measure.pi fun _ : Fin m => D) := by
    intro σ
    obtain ⟨π, hπ⟩ := exists_perm_ext (Fin.castLE hkm) (Fin.castLE_injective hkm) σ
    calc ∫ S, gap f A S σ ∂(Measure.pi fun _ : Fin m => D)
        = ∫ S, gap f A (fun i => S (π i)) (Fin.castLE hkm) ∂(Measure.pi fun _ : Fin m => D) := by
          congr 1
          funext S
          exact (gap_perm f A S π _ _ hπ).symm
      _ = ∫ S, gap f A S (Fin.castLE hkm) ∂(Measure.pi fun _ : Fin m => D) :=
          integral_comp_perm D π (measurable_gap hA hERM hm _)
  have hsum_emb : ∀ S : Fin m → Z,
      ∑ σ : Fin k ↪ Fin m, gap f A S σ ≤ ∑ τ : Fin k → Fin m, gap f A S τ := by
    intro S
    calc ∑ σ : Fin k ↪ Fin m, gap f A S σ
        = ∑ τ ∈ Finset.univ.map (⟨fun σ : Fin k ↪ Fin m => (σ : Fin k → Fin m),
            DFunLike.coe_injective⟩ : (Fin k ↪ Fin m) ↪ (Fin k → Fin m)), gap f A S τ :=
          (Finset.sum_map Finset.univ (⟨fun σ : Fin k ↪ Fin m => (σ : Fin k → Fin m),
            DFunLike.coe_injective⟩ : (Fin k ↪ Fin m) ↪ (Fin k → Fin m))
            (fun τ => gap f A S τ)).symm
      _ ≤ ∑ τ : Fin k → Fin m, gap f A S τ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun τ _ _ => gap_nonneg hP hm S τ
  have hI : (0:ℝ) < Fintype.card (Fin k ↪ Fin m) := by
    have : 0 < Fintype.card (Fin k ↪ Fin m) :=
      Fintype.card_pos_iff.mpr ⟨⟨Fin.castLE hkm, Fin.castLE_injective hkm⟩⟩
    exact_mod_cast this
  have hcardI : (Fintype.card (Fin k ↪ Fin m) : ℝ) = (m.descFactorial k : ℝ) := by
    rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
  have hmain : (Fintype.card (Fin k ↪ Fin m) : ℝ) *
        ∫ S, gap f A S (Fin.castLE hkm) ∂(Measure.pi fun _ : Fin m => D)
      ≤ (m:ℝ) ^ k * εc k := by
    calc (Fintype.card (Fin k ↪ Fin m) : ℝ) *
          ∫ S, gap f A S (Fin.castLE hkm) ∂(Measure.pi fun _ : Fin m => D)
        = ∑ σ : Fin k ↪ Fin m, ∫ S, gap f A S σ ∂(Measure.pi fun _ : Fin m => D) := by
          rw [Finset.sum_congr rfl fun σ _ => hexch σ, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul]
      _ = ∫ S, ∑ σ : Fin k ↪ Fin m, gap f A S σ ∂(Measure.pi fun _ : Fin m => D) :=
          (integral_finsetSum _ fun (σ : Fin k ↪ Fin m) _ => hGi σ).symm
      _ ≤ ∫ S, ∑ τ : Fin k → Fin m, gap f A S τ ∂(Measure.pi fun _ : Fin m => D) :=
          integral_mono (integrable_finsetSum _ fun (σ : Fin k ↪ Fin m) _ => hGi σ)
            (integrable_finsetSum _ fun τ _ => hGi τ) hsum_emb
      _ ≤ ∫ _S, (m:ℝ) ^ k * εc k ∂(Measure.pi fun _ : Fin m => D) :=
          integral_mono (integrable_finsetSum _ fun τ _ => hGi τ) (integrable_const _)
            fun S => empirical_consistency hP hA hc hm hk S
      _ = (m:ℝ) ^ k * εc k := by simp
  have h2 : (m:ℝ) ^ k * εc k ≤ (Fintype.card (Fin k ↪ Fin m) : ℝ) * (2 * εc k) := by
    rw [hcardI]
    calc (m:ℝ) ^ k * εc k ≤ (2 * (m.descFactorial k : ℝ)) * εc k :=
          mul_le_mul_of_nonneg_right hcard hεk
      _ = (m.descFactorial k : ℝ) * (2 * εc k) := by ring
  exact le_of_mul_le_mul_left (hmain.trans h2) hI


lemma rate_nonneg {ε : ℕ → ℝ} (hε : IsRate ε) {k : ℕ} (hk : 1 ≤ k) : 0 ≤ ε k :=
  le_of_tendsto hε.2 (eventually_atTop.mpr ⟨k, fun n hn => hε.1 k n hk hn⟩)


/-! ### The leave-one-out identity -/

omit [MeasurableSpace Z] in
lemma empRisk_succ {f : H → Z → ℝ} {n : ℕ} (hn : 1 ≤ n) (S : Fin (n + 1) → Z) (i : Fin (n + 1))
    (h : H) :
    ((n:ℝ) + 1) * empRisk f S h = f h (S i) + n * empRisk f (Fin.removeNth i S) h := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  unfold empRisk
  rw [Fin.sum_univ_succAbove _ i]
  push_cast
  field_simp
  simp [Fin.removeNth]

lemma loo_pointwise {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) {A : Rule H Z}
    (hERM : IsERMRule f A) {n : ℕ} (hn : 1 ≤ n) (S : Fin (n + 1) → Z) (i : Fin (n + 1)) :
    f (A (n + 1) S) (S i) ≤ f (A n (Fin.removeNth i S)) (S i) := by
  have h1 := empRisk_succ (f := f) hn S i (A (n + 1) S)
  have h2 := empRisk_succ (f := f) hn S i (A n (Fin.removeNth i S))
  have e1 := hERM (n + 1) (by omega) S
  have e2 := hERM n hn (Fin.removeNth i S)
  have l1 := ermValue_le hP hn (Fin.removeNth i S) (A (n + 1) S)
  have l2 := ermValue_le hP (by omega : 1 ≤ n + 1) S (A n (Fin.removeNth i S))
  have l1' := mul_le_mul_of_nonneg_left l1 (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  have l2' := mul_le_mul_of_nonneg_left l2 (by positivity : (0:ℝ) ≤ (n:ℝ) + 1)
  rw [e1] at h1
  rw [e2] at h2
  linarith

lemma loo_term {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) {A : Rule H Z}
    (hA : MeasurableRule f A) (D : Measure Z) [IsProbabilityMeasure D] {n : ℕ} (i : Fin (n + 1)) :
    ∫ S, f (A n (Fin.removeNth i S)) (S i) ∂(Measure.pi fun _ : Fin (n + 1) => D)
      = ∫ T, risk f D (A n T) ∂(Measure.pi fun _ : Fin n => D) := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => D) i
  have hg : Measurable (fun p : Z × (Fin n → Z) => f (A n p.2) p.1) :=
    (hA n).comp measurable_swap
  have hI : Integrable (fun p : Z × (Fin n → Z) => f (A n p.2) p.1)
      (D.prod (Measure.pi fun _ : Fin n => D)) :=
    integrable_of_abs_le hg B fun p => hP.bounded _ _
  have h : ∫ S : Fin (n + 1) → Z, f (A n (Fin.removeNth i S)) (S i)
        ∂(Measure.pi fun _ : Fin (n + 1) => D)
      = ∫ y : Z × (Fin n → Z), f (A n y.2) y.1 ∂(D.prod (Measure.pi fun _ : Fin n => D)) :=
    hmp.integral_comp' (g := fun p : Z × (Fin n → Z) => f (A n p.2) p.1)
  rw [h, integral_prod_symm _ hI]
  rfl

lemma integrable_rule_apply {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    {A : Rule H Z} (hA : MeasurableRule f A) (D : Measure Z) [IsProbabilityMeasure D] {m : ℕ}
    (i : Fin m) :
    Integrable (fun S : Fin m → Z => f (A m S) (S i)) (Measure.pi fun _ : Fin m => D) :=
  integrable_of_abs_le ((hA m).comp (measurable_id.prodMk (measurable_pi_apply i))) B
    fun _ => hP.bounded _ _

lemma sum_integral_rule {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    {A : Rule H Z} (hA : MeasurableRule f A) (D : Measure Z) [IsProbabilityMeasure D] {m : ℕ}
    (hm : 1 ≤ m) :
    ∑ i : Fin m, ∫ S, f (A m S) (S i) ∂(Measure.pi fun _ : Fin m => D)
      = m * ∫ S, empRisk f S (A m S) ∂(Measure.pi fun _ : Fin m => D) := by
  have hm' : (m:ℝ) ≠ 0 := by
    have : (0:ℝ) < m := by exact_mod_cast hm
    exact this.ne'
  unfold empRisk
  rw [integral_div, integral_finsetSum _ fun i _ => integrable_rule_apply hP hA D i]
  field_simp

/-- Expected risk of `A` on `m` points. -/
noncomputable def Gv (f : H → Z → ℝ) (A : Rule H Z) (D : Measure Z) (m : ℕ) : ℝ :=
  ∫ T, risk f D (A m T) ∂(Measure.pi fun _ : Fin m => D)

/-- Expected minimal empirical risk on `m` points. -/
noncomputable def Ev (f : H → Z → ℝ) (A : Rule H Z) (D : Measure Z) (m : ℕ) : ℝ :=
  ∫ S, empRisk f S (A m S) ∂(Measure.pi fun _ : Fin m => D)

lemma loo_eq {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) {A : Rule H Z}
    (hA : MeasurableRule f A) (hERM : IsERMRule f A) (D : Measure Z) [IsProbabilityMeasure D]
    {n : ℕ} (hn : 1 ≤ n) :
    (∑ i : Fin (n + 1),
        ∫ S, |f (A n (Fin.removeNth i S)) (S i) - f (A (n + 1) S) (S i)|
          ∂(sampleLaw D (n + 1))) / (n + 1) = Gv f A D n - Ev f A D (n + 1) := by
  unfold sampleLaw
  have hint1 : ∀ i : Fin (n + 1), Integrable
      (fun S : Fin (n + 1) → Z => f (A n (Fin.removeNth i S)) (S i))
      (Measure.pi fun _ : Fin (n + 1) => D) := by
    intro i
    have hpair : Measurable (fun S : Fin (n + 1) → Z =>
        ((Fin.removeNth i S, S i) : (Fin n → Z) × Z)) :=
      (measurable_pi_lambda _ fun j => measurable_pi_apply _).prodMk (measurable_pi_apply i)
    exact integrable_of_abs_le ((hA n).comp hpair) B fun S => hP.bounded _ _
  have hterm : ∀ i : Fin (n + 1),
      ∫ S, |f (A n (Fin.removeNth i S)) (S i) - f (A (n + 1) S) (S i)|
          ∂(Measure.pi fun _ : Fin (n + 1) => D)
      = Gv f A D n - ∫ S, f (A (n + 1) S) (S i) ∂(Measure.pi fun _ : Fin (n + 1) => D) := by
    intro i
    have : (fun S : Fin (n + 1) → Z =>
        |f (A n (Fin.removeNth i S)) (S i) - f (A (n + 1) S) (S i)|) =
        fun S => f (A n (Fin.removeNth i S)) (S i) - f (A (n + 1) S) (S i) :=
      funext fun S => abs_of_nonneg (sub_nonneg.mpr (loo_pointwise hP hERM hn S i))
    rw [this, integral_sub (hint1 i) (integrable_rule_apply hP hA D i), loo_term hP hA D i]
    rfl
  have hn1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have hsum := sum_integral_rule hP hA D (m := n + 1) (by omega)
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum]
  unfold Ev
  push_cast
  field_simp

/-! ### Relations between the expected quantities -/

lemma opt_le_risk {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) (D : Measure Z)
    [IsProbabilityMeasure D] (h : H) : optRisk f D ≤ risk f D h :=
  ciInf_le ⟨-B, by rintro _ ⟨g, rfl⟩; exact (abs_le.mp (abs_risk_le hP D g)).1⟩ h

lemma integrable_risk_rule {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    {A : Rule H Z} (hA : MeasurableRule f A) (D : Measure Z) [IsProbabilityMeasure D] (m : ℕ) :
    Integrable (fun T : Fin m → Z => risk f D (A m T)) (Measure.pi fun _ : Fin m => D) :=
  integrable_of_abs_le (measurable_risk_rule hA D m) B fun _ => abs_risk_le hP D _

lemma integrable_empRisk_rule {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    {A : Rule H Z} (hA : MeasurableRule f A) (D : Measure Z) [IsProbabilityMeasure D] {m : ℕ}
    (hm : 1 ≤ m) :
    Integrable (fun S : Fin m → Z => empRisk f S (A m S)) (Measure.pi fun _ : Fin m => D) :=
  integrable_of_abs_le (measurable_empRisk_rule hA (m := m) (k := m) (φ := id) measurable_id) B
    fun S => abs_empRisk_le hP hm S _

lemma opt_le_Gv {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) {A : Rule H Z}
    (hA : MeasurableRule f A) (D : Measure Z) [IsProbabilityMeasure D] (m : ℕ) :
    optRisk f D ≤ Gv f A D m := by
  unfold Gv
  have := integral_mono (integrable_const (optRisk f D)) (integrable_risk_rule hP hA D m)
    (fun T => opt_le_risk hP D (A m T))
  simpa using this

lemma Ev_le_opt [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    {A : Rule H Z} (hA : MeasurableRule f A) (hERM : IsERMRule f A) (D : Measure Z)
    [IsProbabilityMeasure D] {m : ℕ} (hm : 1 ≤ m) : Ev f A D m ≤ optRisk f D := by
  unfold optRisk
  refine le_ciInf fun h => ?_
  rw [← integral_empRisk hP D hm h]
  unfold Ev
  exact integral_mono (integrable_empRisk_rule hP hA D hm)
    (integrable_of_abs_le (measurable_empRisk_const hP m h) B fun S => abs_empRisk_le hP hm S h)
    fun S => by rw [hERM m hm S]; exact ermValue_le hP hm S h

lemma integral_ermValue {f : H → Z → ℝ} (A : Rule H Z) (hERM : IsERMRule f A) (D : Measure Z)
    {m : ℕ} (hm : 1 ≤ m) :
    ∫ S, ermValue f S ∂(Measure.pi fun _ : Fin m => D) = Ev f A D m := by
  unfold Ev
  congr 1
  funext S
  exact (hERM m hm S).symm

lemma consistent_integral {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) {A : Rule H Z}
    (hA : MeasurableRule f A) (D : Measure Z) [IsProbabilityMeasure D] (m : ℕ) :
    ∫ S, (risk f D (A m S) - optRisk f D) ∂(sampleLaw D m) = Gv f A D m - optRisk f D := by
  unfold sampleLaw Gv
  rw [integral_sub (integrable_risk_rule hP hA D m) (integrable_const _)]
  simp

/-! ### Bound on the optimism of the ERM -/

lemma delta_bound_k [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    {A : Rule H Z} (hA : MeasurableRule f A) (hERM : IsERMRule f A) {ε : ℕ → ℝ}
    (hc : UniversallyConsistent f A ε) (D : Measure Z) [IsProbabilityMeasure D] {m k : ℕ}
    (hm : 1 ≤ m) (hk1 : 1 ≤ k) (hkm : k ≤ m) (hcard : (m:ℝ) ^ k ≤ 2 * (m.descFactorial k : ℝ))
    (hεk : 0 ≤ ε k) (hkk : k * k ≤ m) :
    optRisk f D - Ev f A D m ≤ 2 * ε k + 2 * B / Real.sqrt m := by
  have hB := B_nonneg hP D
  have key := aerm_core hP A ε hA hERM hc D hm hk1 hkm hcard hεk
  have pl := prefix_lower hP hA D hm hkm
  have hopt := opt_le_Gv hP hA D k
  unfold Gv at hopt
  have hi1 : Integrable
      (fun S : Fin m → Z => empRisk f S (A k (fun j => S (Fin.castLE hkm j))))
      (Measure.pi fun _ : Fin m => D) :=
    integrable_of_abs_le (measurable_empRisk_rule hA
      (measurable_pi_lambda _ fun j => measurable_pi_apply _)) B fun S => abs_empRisk_le hP hm S _
  have hi2 : Integrable (fun S : Fin m → Z => ermValue f S) (Measure.pi fun _ : Fin m => D) := by
    have e : (fun S : Fin m → Z => ermValue f S) = fun S => empRisk f S (A m S) :=
      funext fun S => (hERM m hm S).symm
    rw [e]
    exact integrable_empRisk_rule hP hA D hm
  rw [integral_sub hi1 hi2, integral_ermValue A hERM D hm] at key
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  have hsq : (0:ℝ) < Real.sqrt m := Real.sqrt_pos.mpr hmpos
  have hkR : (k:ℝ) * k ≤ m := by exact_mod_cast hkk
  have hkm' : (k:ℝ) / m ≤ 1 / Real.sqrt m := by
    rw [div_le_div_iff₀ hmpos hsq]
    have hs : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hmpos.le
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have hks : (k:ℝ) ≤ Real.sqrt m := by
      apply Real.le_sqrt_of_sq_le
      nlinarith
    nlinarith
  have h2 : 2 * B * k / m ≤ 2 * B / Real.sqrt m := by
    have := mul_le_mul_of_nonneg_left hkm' (by positivity : (0:ℝ) ≤ 2 * B)
    calc 2 * B * k / m = 2 * B * (k / m) := by ring
      _ ≤ 2 * B * (1 / Real.sqrt m) := this
      _ = 2 * B / Real.sqrt m := by ring
  linarith

lemma delta_bound [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    {A : Rule H Z} (hA : MeasurableRule f A) (hERM : IsERMRule f A) {ε : ℕ → ℝ} (hε : IsRate ε)
    (hc : UniversallyConsistent f A ε) (D : Measure Z) [IsProbabilityMeasure D] {m : ℕ}
    (hm : 1 ≤ m) :
    optRisk f D - Ev f A D m ≤ 2 * ε (Nat.sqrt (Nat.sqrt m)) + 2 * B / Real.sqrt m := by
  have hk1 : 1 ≤ Nat.sqrt (Nat.sqrt m) := Nat.sqrt_pos.mpr (Nat.sqrt_pos.mpr hm)
  have hεk : 0 ≤ ε (Nat.sqrt (Nat.sqrt m)) := rate_nonneg hε hk1
  have h4 : Nat.sqrt (Nat.sqrt m) * Nat.sqrt (Nat.sqrt m) *
      (Nat.sqrt (Nat.sqrt m) * Nat.sqrt (Nat.sqrt m)) ≤ m :=
    (Nat.mul_le_mul (Nat.sqrt_le _) (Nat.sqrt_le _)).trans (Nat.sqrt_le _)
  refine delta_bound_k hP hA hERM hc D hm hk1 (kk_le m)
    (card_bound hk1 (kk_le m) (two_k_bound h4)) hεk ?_
  calc Nat.sqrt (Nat.sqrt m) * Nat.sqrt (Nat.sqrt m)
      ≤ Nat.sqrt (Nat.sqrt m) * Nat.sqrt (Nat.sqrt m) *
        (Nat.sqrt (Nat.sqrt m) * Nat.sqrt (Nat.sqrt m)) :=
        Nat.le_mul_of_pos_right _ (Nat.mul_pos hk1 hk1)
    _ ≤ m := h4

/-! ### Concentration of the empirical risk -/

lemma sq_integral_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {g : α → ℝ} (hg : Measurable g) (C : ℝ) (hC : ∀ x, |g x| ≤ C) :
    (∫ x, |g x| ∂μ) ^ 2 ≤ ∫ x, (g x) ^ 2 ∂μ := by
  have hi1 : Integrable (fun x => |g x|) μ :=
    integrable_of_abs_le hg.abs C fun x => by rw [abs_abs]; exact hC x
  have hi2 : Integrable (fun x => (g x) ^ 2) μ :=
    integrable_of_abs_le (hg.pow_const 2) (C ^ 2) fun x => by
      have h1 := hC x
      have h0 := abs_nonneg (g x)
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      nlinarith
  set a := ∫ x, |g x| ∂μ with ha
  have h0 : 0 ≤ ∫ x, (|g x| - a) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have e : (fun x => (|g x| - a) ^ 2) = fun x => (g x) ^ 2 - (2 * a) * |g x| + a ^ 2 := by
    funext x
    rw [sub_sq, sq_abs]
    ring
  have hi3 : Integrable (fun x => (g x) ^ 2 - (2 * a) * |g x|) μ := hi2.sub (hi1.const_mul _)
  rw [e, integral_add hi3 (integrable_const _),
    integral_sub hi2 (hi1.const_mul _), integral_const_mul, integral_const] at h0
  have hu : μ.real Set.univ = 1 := by simp
  rw [hu, one_smul, ← ha] at h0
  nlinarith

lemma second_moment {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) (D : Measure Z)
    [IsProbabilityMeasure D] {m : ℕ} (hm : 1 ≤ m) (h : H) :
    ∫ S, (empRisk f S h - risk f D h) ^ 2 ∂(Measure.pi fun _ : Fin m => D) ≤ 4 * B ^ 2 / m := by
  classical
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hYm : ∀ i : Fin m, Measurable (fun S : Fin m → Z => f h (S i) - risk f D h) := fun i =>
    ((hP.measurable h).comp (measurable_pi_apply i)).sub_const _
  have hYb : ∀ (i : Fin m) (S : Fin m → Z), |f h (S i) - risk f D h| ≤ 2 * B := by
    intro i S
    calc |f h (S i) - risk f D h| ≤ |f h (S i)| + |risk f D h| := abs_sub _ _
      _ ≤ B + B := add_le_add (hP.bounded _ _) (abs_risk_le hP D h)
      _ = 2 * B := by ring
  have hB0 : ∀ (i : Fin m) (S : Fin m → Z), 0 ≤ 2 * B := fun i S =>
    (abs_nonneg _).trans (hYb i S)
  have hind := ProbabilityTheory.iIndepFun_pi (μ := fun _ : Fin m => D)
    (X := fun _ : Fin m => fun z : Z => f h z - risk f D h)
    (fun _ => ((hP.measurable h).sub_const _).aemeasurable)
  have h0 : ∀ i : Fin m, ∫ S : Fin m → Z, (f h (S i) - risk f D h)
      ∂(Measure.pi fun _ : Fin m => D) = 0 := by
    intro i
    have hi : Integrable (fun S : Fin m → Z => f h (S i)) (Measure.pi fun _ : Fin m => D) :=
      integrable_of_abs_le ((hP.measurable h).comp (measurable_pi_apply i)) B
        fun S => hP.bounded _ _
    rw [integral_sub hi (integrable_const _),
      integral_comp_eval (hP.measurable h).aestronglyMeasurable]
    simp [risk]
  have hoff : ∀ i j : Fin m, i ≠ j → ∫ S : Fin m → Z,
      (f h (S i) - risk f D h) * (f h (S j) - risk f D h)
        ∂(Measure.pi fun _ : Fin m => D) = 0 := by
    intro i j hij
    have hI := hind.indepFun hij
    have := hI.integral_mul_eq_mul_integral (hYm i).aestronglyMeasurable
      (hYm j).aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, h0 i, zero_mul]
  have hI2 : ∀ i j : Fin m, Integrable (fun S : Fin m → Z =>
      (f h (S i) - risk f D h) * (f h (S j) - risk f D h)) (Measure.pi fun _ : Fin m => D) :=
    fun i j => integrable_of_abs_le ((hYm i).mul (hYm j)) ((2 * B) * (2 * B)) fun S => by
      rw [abs_mul]
      exact mul_le_mul (hYb i S) (hYb j S) (abs_nonneg _) (hB0 i S)
  have hexp : ∀ S : Fin m → Z, (empRisk f S h - risk f D h) ^ 2 =
      (∑ i, ∑ j, (f h (S i) - risk f D h) * (f h (S j) - risk f D h)) / (m:ℝ) ^ 2 := by
    intro S
    have e1 : empRisk f S h - risk f D h = (∑ i, (f h (S i) - risk f D h)) / m := by
      unfold empRisk
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp
    rw [e1, div_pow, sq (∑ i, _), Finset.sum_mul_sum]
  calc ∫ S, (empRisk f S h - risk f D h) ^ 2 ∂(Measure.pi fun _ : Fin m => D)
      = ∫ S, (∑ i, ∑ j, (f h (S i) - risk f D h) * (f h (S j) - risk f D h)) / (m:ℝ) ^ 2
          ∂(Measure.pi fun _ : Fin m => D) := by
        congr 1
        funext S
        exact hexp S
    _ = (∑ i, ∑ j, ∫ S : Fin m → Z, (f h (S i) - risk f D h) * (f h (S j) - risk f D h)
          ∂(Measure.pi fun _ : Fin m => D)) / (m:ℝ) ^ 2 := by
        rw [integral_div, integral_finsetSum _ (fun i _ => integrable_finsetSum _
          fun j _ => hI2 i j)]
        congr 1
        exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hI2 i j
    _ ≤ (∑ i : Fin m, ∑ j : Fin m, if i = j then 4 * B ^ 2 else 0) / (m:ℝ) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        by_cases hij : i = j
        · subst hij
          rw [if_pos rfl]
          have := integral_mono (hI2 i i) (integrable_const (4 * B ^ 2))
            (μ := Measure.pi fun _ : Fin m => D) (fun S => by
              have h1 := abs_le.mp (hYb i S)
              nlinarith)
          simpa using this
        · rw [if_neg hij, hoff i j hij]
    _ = 4 * B ^ 2 / m := by
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

lemma abs_moment {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) (D : Measure Z)
    [IsProbabilityMeasure D] {m : ℕ} (hm : 1 ≤ m) (h : H) :
    ∫ S, |empRisk f S h - risk f D h| ∂(Measure.pi fun _ : Fin m => D) ≤
      2 * B / Real.sqrt m := by
  have : Nonempty H := ⟨h⟩
  have hB := B_nonneg hP D
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hsq : (0:ℝ) < Real.sqrt m := Real.sqrt_pos.mpr hm'
  have h1 := sq_integral_abs_le (μ := Measure.pi fun _ : Fin m => D)
    (g := fun S : Fin m → Z => empRisk f S h - risk f D h)
    ((measurable_empRisk_const hP m h).sub_const _) (2 * B) (fun S => by
      have a1 := abs_empRisk_le hP hm S h
      have a2 := abs_risk_le hP D h
      calc |empRisk f S h - risk f D h| ≤ |empRisk f S h| + |risk f D h| := abs_sub _ _
        _ ≤ B + B := add_le_add a1 a2
        _ = 2 * B := by ring)
  have h2 := second_moment hP D hm h
  have h3 : (2 * B / Real.sqrt m) ^ 2 = 4 * B ^ 2 / m := by
    rw [div_pow, Real.sq_sqrt hm'.le]
    ring
  have h4 : 0 ≤ 2 * B / Real.sqrt m := by positivity
  have h5 : (∫ S, |empRisk f S h - risk f D h| ∂(Measure.pi fun _ : Fin m => D)) ^ 2
      ≤ (2 * B / Real.sqrt m) ^ 2 := by
    rw [h3]
    exact h1.trans h2
  exact (sq_le_sq₀ (integral_nonneg fun S => abs_nonneg _) h4).mp h5

/-! ### Bound on the absolute generalisation gap -/

lemma gen_bound [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    {A : Rule H Z} (hA : MeasurableRule f A) (hERM : IsERMRule f A) (D : Measure Z)
    [IsProbabilityMeasure D] {m : ℕ} (hm : 1 ≤ m) :
    ∫ S, |risk f D (A m S) - empRisk f S (A m S)| ∂(Measure.pi fun _ : Fin m => D)
      ≤ (Gv f A D m - Ev f A D m) + 4 * B / Real.sqrt m := by
  have hX : Integrable (fun S : Fin m → Z => risk f D (A m S) - empRisk f S (A m S))
      (Measure.pi fun _ : Fin m => D) :=
    (integrable_risk_rule hP hA D m).sub (integrable_empRisk_rule hP hA D hm)
  have hEx : ∫ S, (risk f D (A m S) - empRisk f S (A m S)) ∂(Measure.pi fun _ : Fin m => D)
      = Gv f A D m - Ev f A D m := by
    unfold Gv Ev
    exact integral_sub (integrable_risk_rule hP hA D m) (integrable_empRisk_rule hP hA D hm)
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨h, hh⟩ : ∃ h, risk f D h < optRisk f D + η / 2 :=
    exists_lt_of_ciInf_lt (f := fun h => risk f D h) (a := optRisk f D + η / 2)
      (show optRisk f D < optRisk f D + η / 2 by linarith)
  have hpt : ∀ S : Fin m → Z, |risk f D (A m S) - empRisk f S (A m S)| ≤
      (risk f D (A m S) - empRisk f S (A m S)) +
        2 * (|empRisk f S h - risk f D h| + η / 2) := by
    intro S
    have e1 := hERM m hm S
    have l1 := ermValue_le hP hm S h
    have l2 := opt_le_risk hP D (A m S)
    have l3 := le_abs_self (empRisk f S h - risk f D h)
    have l4 := abs_nonneg (empRisk f S h - risk f D h)
    rw [e1]
    rcases abs_cases (risk f D (A m S) - ermValue f S) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  have hWa : Integrable (fun S : Fin m → Z => |empRisk f S h - risk f D h|)
      (Measure.pi fun _ : Fin m => D) :=
    ((integrable_of_abs_le (measurable_empRisk_const hP m h) B
      fun S => abs_empRisk_le hP hm S h).sub (integrable_const _)).abs
  have hW : Integrable (fun S : Fin m → Z => |empRisk f S h - risk f D h| + η / 2)
      (Measure.pi fun _ : Fin m => D) := hWa.add (integrable_const _)
  have hint : ∫ S, |risk f D (A m S) - empRisk f S (A m S)| ∂(Measure.pi fun _ : Fin m => D) ≤
      ∫ S, ((risk f D (A m S) - empRisk f S (A m S)) +
        2 * (|empRisk f S h - risk f D h| + η / 2)) ∂(Measure.pi fun _ : Fin m => D) :=
    integral_mono hX.abs (hX.add (hW.const_mul 2)) hpt
  rw [integral_add hX (hW.const_mul 2), integral_const_mul, integral_add hWa (integrable_const _),
    integral_const, hEx] at hint
  have hu : (Measure.pi fun _ : Fin m => D).real Set.univ = 1 := by simp
  rw [hu, one_smul] at hint
  have hm2 := abs_moment hP D hm h
  have e : 4 * B / Real.sqrt m = 2 * (2 * B / Real.sqrt m) := by ring
  rw [e]
  linarith

/-! ### Rates -/

lemma isRate_add {ε₁ ε₂ : ℕ → ℝ} (h₁ : IsRate ε₁) (h₂ : IsRate ε₂) :
    IsRate (fun m => ε₁ m + ε₂ m) :=
  ⟨fun m n hm hmn => add_le_add (h₁.1 m n hm hmn) (h₂.1 m n hm hmn), by
    simpa using h₁.2.add h₂.2⟩

lemma isRate_div_sqrt {c : ℝ} (hc : 0 ≤ c) : IsRate (fun m => c / Real.sqrt m) := by
  refine ⟨fun m n hm hmn => ?_, ?_⟩
  · have hm' : (0:ℝ) < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
    exact div_le_div_of_nonneg_left hc hm' (Real.sqrt_le_sqrt (by exact_mod_cast hmn))
  · exact tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

lemma tendsto_nat_sqrt : Tendsto Nat.sqrt atTop atTop :=
  tendsto_atTop_atTop.mpr fun b => ⟨b * b, fun _ hn => Nat.le_sqrt.mpr hn⟩

lemma isRate_cons {ε : ℕ → ℝ} (hε : IsRate ε) {c : ℝ} (hc : 0 ≤ c) :
    IsRate (fun m => 3 * ε (Nat.sqrt (Nat.sqrt m)) + c / Real.sqrt m) := by
  refine isRate_add ⟨fun m n hm hmn => ?_, ?_⟩ (isRate_div_sqrt hc)
  · have h1 : 1 ≤ Nat.sqrt (Nat.sqrt m) := Nat.sqrt_pos.mpr (Nat.sqrt_pos.mpr hm)
    have h2 : Nat.sqrt (Nat.sqrt m) ≤ Nat.sqrt (Nat.sqrt n) :=
      Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt hmn)
    have := hε.1 _ _ h1 h2
    linarith
  · have := (hε.2.comp (tendsto_nat_sqrt.comp tendsto_nat_sqrt)).const_mul 3
    simpa using this

lemma isRate_succ {ε : ℕ → ℝ} (hε : IsRate ε) : IsRate (fun m => ε (m + 1)) :=
  ⟨fun m n hm hmn => hε.1 (m + 1) (n + 1) (by omega) (by omega),
    hε.2.comp (tendsto_add_atTop_nat 1)⟩

lemma kk_le_pred {n : ℕ} (hn : 1 ≤ n) : Nat.sqrt (Nat.sqrt (n + 1)) ≤ n :=
  (Nat.sqrt_le_self _).trans (Nat.lt_succ_iff.mp (Nat.sqrt_lt_self (by omega)))

/-! ### The four implications -/

lemma loo_to_cons [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    {A : Rule H Z} (hA : MeasurableRule f A) (hERM : IsERMRule f A) {ε : ℕ → ℝ}
    (hL : UniversallyLOOStable f A ε) : UniversallyConsistent f A (fun m => ε (m + 1)) := by
  intro D hD m hm
  have := hD
  have h1 := hL D hD m hm
  rw [loo_eq hP hA hERM D hm] at h1
  have h2 := Ev_le_opt hP hA hERM D (by omega : 1 ≤ m + 1)
  show ∫ S, (risk f D (A m S) - optRisk f D) ∂(sampleLaw D m) ≤ ε (m + 1)
  rw [consistent_integral hP hA D m]
  linarith

lemma cons_to_loo [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    {A : Rule H Z} (hA : MeasurableRule f A) (hERM : IsERMRule f A) {ε : ℕ → ℝ} (hε : IsRate ε)
    (hc : UniversallyConsistent f A ε) :
    UniversallyLOOStable f A
      (fun m => 3 * ε (Nat.sqrt (Nat.sqrt m)) + 6 * |B| / Real.sqrt m) := by
  intro D hD n hn
  have := hD
  have hB := B_nonneg hP D
  have h1 := hc D hD n hn
  rw [consistent_integral hP hA D n] at h1
  have h2 := delta_bound hP hA hERM hε hc D (by omega : 1 ≤ n + 1)
  have h3 : ε n ≤ ε (Nat.sqrt (Nat.sqrt (n + 1))) :=
    hε.1 _ _ (Nat.sqrt_pos.mpr (Nat.sqrt_pos.mpr (by omega))) (kk_le_pred hn)
  have hsq : (0:ℝ) < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have h4 : 2 * B / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ 6 * |B| / Real.sqrt ((n + 1 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right (by rw [abs_of_nonneg hB]; linarith) hsq.le
  show (∑ i : Fin (n + 1), ∫ S, |f (A n (Fin.removeNth i S)) (S i) - f (A (n + 1) S) (S i)|
      ∂(sampleLaw D (n + 1))) / ((n:ℝ) + 1) ≤
    3 * ε (Nat.sqrt (Nat.sqrt (n + 1))) + 6 * |B| / Real.sqrt ((n + 1 : ℕ) : ℝ)
  rw [loo_eq hP hA hERM D hn]
  linarith

lemma cons_to_gen [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    {A : Rule H Z} (hA : MeasurableRule f A) (hERM : IsERMRule f A) {ε : ℕ → ℝ} (hε : IsRate ε)
    (hc : UniversallyConsistent f A ε) :
    UniversallyGeneralizes f A
      (fun m => 3 * ε (Nat.sqrt (Nat.sqrt m)) + 6 * |B| / Real.sqrt m) := by
  intro D hD m hm
  have := hD
  have hB := B_nonneg hP D
  have h1 := hc D hD m hm
  rw [consistent_integral hP hA D m] at h1
  have h2 := delta_bound hP hA hERM hε hc D hm
  have h3 : ε m ≤ ε (Nat.sqrt (Nat.sqrt m)) :=
    hε.1 _ _ (Nat.sqrt_pos.mpr (Nat.sqrt_pos.mpr hm)) (kk_le m)
  have hsq : (0:ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  have h4 : 2 * B / Real.sqrt (m : ℝ) ≤ 2 * |B| / Real.sqrt (m : ℝ) :=
    div_le_div_of_nonneg_right (by rw [abs_of_nonneg hB]) hsq.le
  have h5 : 4 * B / Real.sqrt (m : ℝ) ≤ 4 * |B| / Real.sqrt (m : ℝ) :=
    div_le_div_of_nonneg_right (by rw [abs_of_nonneg hB]) hsq.le
  have h6 := gen_bound hP hA hERM D hm
  show ∫ S, |risk f D (A m S) - empRisk f S (A m S)| ∂(Measure.pi fun _ : Fin m => D) ≤
    3 * ε (Nat.sqrt (Nat.sqrt m)) + 6 * |B| / Real.sqrt (m : ℝ)
  have e : 6 * |B| / Real.sqrt (m : ℝ) = 2 * |B| / Real.sqrt (m : ℝ) +
      4 * |B| / Real.sqrt (m : ℝ) := by ring
  rw [e]
  linarith

lemma gen_to_cons [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    {A : Rule H Z} (hA : MeasurableRule f A) (hERM : IsERMRule f A) {ε : ℕ → ℝ}
    (hg : UniversallyGeneralizes f A ε) : UniversallyConsistent f A ε := by
  intro D hD m hm
  have := hD
  have h1 := hg D hD m hm
  have h2 := Ev_le_opt hP hA hERM D hm
  have hX : Integrable (fun S : Fin m → Z => risk f D (A m S) - empRisk f S (A m S))
      (Measure.pi fun _ : Fin m => D) :=
    (integrable_risk_rule hP hA D m).sub (integrable_empRisk_rule hP hA D hm)
  have hEx : ∫ S, (risk f D (A m S) - empRisk f S (A m S)) ∂(Measure.pi fun _ : Fin m => D)
      = Gv f A D m - Ev f A D m := by
    unfold Gv Ev
    exact integral_sub (integrable_risk_rule hP hA D m) (integrable_empRisk_rule hP hA D hm)
  have h3 := integral_mono hX hX.abs (fun S => le_abs_self
    (risk f D (A m S) - empRisk f S (A m S)))
  rw [hEx] at h3
  have h4 : ∫ S, |risk f D (A m S) - empRisk f S (A m S)| ∂(Measure.pi fun _ : Fin m => D)
      ≤ ε m := h1
  rw [consistent_integral hP hA D m]
  linarith

end LearnStability.ERMLOO.T31Proof

open LearnStability.ERMLOO MeasureTheory in
theorem solution {H Z : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (B : ℝ) (hf : StandingAssumptions f B)
    (A : Rule H Z) (hA : MeasurableRule f A) (hERM : IsERMRule f A) :
    ((∃ ε, IsRate ε ∧ UniversallyLOOStable f A ε) ↔ (∃ ε, IsRate ε ∧ UniversallyConsistent f A ε)) ∧
    ((∃ ε, IsRate ε ∧ UniversallyConsistent f A ε) ↔
      (∃ ε, IsRate ε ∧ UniversallyGeneralizes f A ε)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨ε, hε, hL⟩
    exact ⟨_, T31Proof.isRate_succ hε, T31Proof.loo_to_cons hf hA hERM hL⟩
  · rintro ⟨ε, hε, hc⟩
    exact ⟨_, T31Proof.isRate_cons hε (by positivity : (0:ℝ) ≤ 6 * |B|),
      T31Proof.cons_to_loo hf hA hERM hε hc⟩
  · rintro ⟨ε, hε, hc⟩
    exact ⟨_, T31Proof.isRate_cons hε (by positivity : (0:ℝ) ≤ 6 * |B|),
      T31Proof.cons_to_gen hf hA hERM hε hc⟩
  · rintro ⟨ε, hε, hg⟩
    exact ⟨ε, hε, T31Proof.gen_to_cons hf hA hERM hg⟩
