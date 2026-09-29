-- Prove2me | solution 1 for LearnStability.Characterization.theorem7_learnable_iff_stable_aerm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T07:50:51.219587+00:00
-- url     : https://prove2.me/submissions/0a885dc7-3ca2-409e-91c0-457781f4cd70

import Mathlib
import Definitions.Def_LearnStability_Characterization_Setting
import Definitions.Def_LearnStability_Characterization_RuleProperties
import Definitions.Def_LearnStability_Characterization_Stability

/-! be2ab818 LearnStability.Characterization.theorem7_learnable_iff_stable_aerm
(Shalev-Shwartz, Shamir, Srebro, Sridharan 2010, Theorem 7).
Part 3: uniform-RO stability (with replacement vector constant = test point) plus the
coordinate-swap exchangeability of `D^m ⊗ D` gives on-average generalization; together with
`E[min_h F_S(h)] ≤ F*` and the AERM bound this gives consistency.
Part 2: `A'(S) = A(first ⌊m^{1/4}⌋ points)`. Stability: only `k ≤ √m` coordinates matter.
AERM: consistency of `A` under the empirical distribution of `S` bounds the average over all
`τ : Fin k → Fin m` of the gap; exchangeability (permutation invariance of `D^m`) makes every
injective `τ` give the same expected gap as the prefix; `m^k ≤ 2·m^{(k)}` (Bernoulli).
Part 1 follows from parts 2 and 3. -/

set_option autoImplicit false

namespace LearnStability.Characterization.T7Proof

open MeasureTheory Filter Topology LearnStability.Characterization

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

/-! ### Exchangeability of product measures -/

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

lemma swap_mp {m : ℕ} (D : Measure Z) [IsProbabilityMeasure D] (i : Fin m) :
    MeasurePreserving (fun p : (Fin m → Z) × Z => (Function.update p.1 i p.2, p.1 i))
      ((Measure.pi fun _ : Fin m => D).prod D) ((Measure.pi fun _ : Fin m => D).prod D) := by
  set J := MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin m) => Z) with hJdef
  have hJs : MeasurePreserving J.symm ((Measure.pi fun _ : Fin m => D).prod D)
      (Measure.pi fun _ : Option (Fin m) => D) :=
    ⟨J.symm.measurable, Measure.pi_map_piOptionEquivProd (fun _ : Option (Fin m) => D)⟩
  have hJ : MeasurePreserving J (Measure.pi fun _ : Option (Fin m) => D)
      ((Measure.pi fun _ : Fin m => D).prod D) :=
    MeasurePreserving.symm J.symm hJs
  have hσ := perm_mp D (Equiv.swap (none : Option (Fin m)) (some i))
  have hc := hJ.comp (hσ.comp hJs)
  convert hc using 1
  funext p
  obtain ⟨x, rfl⟩ := J.surjective p
  simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply]
  refine Prod.ext ?_ ?_
  · show Function.update (fun j => x (some j)) i (x none) =
      fun j => x (Equiv.swap none (some i) (some j))
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Equiv.swap_apply_def, hj]
  · show x (some i) = x (Equiv.swap none (some i) none)
    simp

lemma exists_perm_ext {k m : ℕ} (ι : Fin k → Fin m) (hι : Function.Injective ι)
    (σ : Fin k ↪ Fin m) : ∃ π : Equiv.Perm (Fin m), ∀ j, π (ι j) = σ j := by
  classical
  let e : {x // x ∈ Set.range ι} ≃ {x // x ∈ Set.range σ} :=
    (Equiv.ofInjective ι hι).symm.trans (Equiv.ofInjective σ σ.injective)
  refine ⟨e.extendSubtype, fun j => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem e (ι j) ⟨j, rfl⟩]
  simp [e, Equiv.ofInjective_symm_apply]

/-! ### Part 3: stability + AERM ⟹ consistency -/

theorem part3 [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    (A : Rule H Z) (εs εe : ℕ → ℝ) (hA : MeasurableRule f A) (hs : UniformROStable f A εs)
    (he : UniversalAERM f A εe) : UniversallyConsistent f A (fun m => εs m + εe m) := by
  intro D hD m hm
  have hAE := he D hD m hm
  show ∫ S, (risk f D (A m S) - optRisk f D) ∂(sampleLaw D m) ≤ εs m + εe m
  unfold sampleLaw at hAE ⊢
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hR : Measurable (fun S : Fin m → Z => risk f D (A m S)) := measurable_risk_rule hA D m
  have hE : Measurable (fun S : Fin m → Z => empRisk f S (A m S)) :=
    measurable_empRisk_rule hA measurable_id
  have hV : Measurable (fun S : Fin m → Z => ermValue f S) := hP.measurable_ermValue m
  have hRi : Integrable (fun S : Fin m → Z => risk f D (A m S)) (Measure.pi fun _ : Fin m => D) :=
    integrable_of_abs_le hR B fun S => abs_risk_le hP D _
  have hEi : Integrable (fun S : Fin m → Z => empRisk f S (A m S))
      (Measure.pi fun _ : Fin m => D) :=
    integrable_of_abs_le hE B fun S => abs_empRisk_le hP hm S _
  have hVi : Integrable (fun S : Fin m → Z => ermValue f S) (Measure.pi fun _ : Fin m => D) :=
    integrable_of_abs_le hV B fun S => by
      rw [abs_le]
      exact ⟨neg_le_ermValue hP hm S, (ermValue_le hP hm S (Classical.arbitrary H)).trans
        (abs_le.mp (abs_empRisk_le hP hm S _)).2⟩
  -- K1: on-average generalization from uniform-RO stability
  have K1 : ∫ S, risk f D (A m S) ∂(Measure.pi fun _ : Fin m => D) -
      ∫ S, empRisk f S (A m S) ∂(Measure.pi fun _ : Fin m => D) ≤ εs m := by
    have hW : Measurable (fun p : (Fin m → Z) × Z => f (A m p.1) p.2) := hA m
    have hWi : Integrable (fun p : (Fin m → Z) × Z => f (A m p.1) p.2)
        ((Measure.pi fun _ : Fin m => D).prod D) :=
      integrable_of_abs_le hW B fun p => hP.bounded _ _
    have hG : ∀ i : Fin m,
        Measurable (fun p : (Fin m → Z) × Z => f (A m (Function.update p.1 i p.2)) p.2) :=
      fun i => (hA m).comp (measurable_update'.prodMk measurable_snd)
    have hGi : ∀ i : Fin m,
        Integrable (fun p : (Fin m → Z) × Z => f (A m (Function.update p.1 i p.2)) p.2)
          ((Measure.pi fun _ : Fin m => D).prod D) :=
      fun i => integrable_of_abs_le (hG i) B fun p => hP.bounded _ _
    have hF : ∀ i : Fin m, Measurable (fun S : Fin m → Z => f (A m S) (S i)) :=
      fun i => (hA m).comp (measurable_id.prodMk (measurable_pi_apply i))
    have hFi : ∀ i : Fin m,
        Integrable (fun S : Fin m → Z => f (A m S) (S i)) (Measure.pi fun _ : Fin m => D) :=
      fun i => integrable_of_abs_le (hF i) B fun S => hP.bounded _ _
    have hswap : ∀ i : Fin m,
        ∫ p, f (A m (Function.update p.1 i p.2)) p.2 ∂((Measure.pi fun _ : Fin m => D).prod D)
          = ∫ S, f (A m S) (S i) ∂(Measure.pi fun _ : Fin m => D) := by
      intro i
      have hmp := swap_mp D i
      have hF' : Measurable (fun p : (Fin m → Z) × Z => f (A m p.1) (p.1 i)) :=
        (hF i).comp measurable_fst
      have h := integral_map (μ := (Measure.pi fun _ : Fin m => D).prod D)
        hmp.measurable.aemeasurable (f := fun p : (Fin m → Z) × Z => f (A m p.1) (p.1 i))
        (by rw [hmp.map_eq]; exact hF'.aestronglyMeasurable)
      rw [hmp.map_eq] at h
      have h2 : ∫ p, f (A m p.1) (p.1 i) ∂((Measure.pi fun _ : Fin m => D).prod D)
          = ∫ S, f (A m S) (S i) ∂(Measure.pi fun _ : Fin m => D) := by
        have := integral_fun_fst (μ := Measure.pi fun _ : Fin m => D) (ν := D)
          (fun S : Fin m → Z => f (A m S) (S i))
        simpa using this
      rw [← h2, h]
      congr 1
      funext p
      simp
    have hRQ : ∫ p, f (A m p.1) p.2 ∂((Measure.pi fun _ : Fin m => D).prod D)
        = ∫ S, risk f D (A m S) ∂(Measure.pi fun _ : Fin m => D) := by
      rw [integral_prod _ hWi]
      rfl
    have hsumP : ∫ S, ∑ i, f (A m S) (S i) ∂(Measure.pi fun _ : Fin m => D)
        = ∑ i, ∫ S, f (A m S) (S i) ∂(Measure.pi fun _ : Fin m => D) :=
      integral_finsetSum _ fun i _ => hFi i
    have hEP : ∫ S, empRisk f S (A m S) ∂(Measure.pi fun _ : Fin m => D)
        = (∑ i, ∫ S, f (A m S) (S i) ∂(Measure.pi fun _ : Fin m => D)) / m := by
      unfold empRisk
      rw [integral_div, hsumP]
    have hsum0 : ∫ p, ∑ i, (f (A m p.1) p.2 - f (A m (Function.update p.1 i p.2)) p.2)
          ∂((Measure.pi fun _ : Fin m => D).prod D)
        = ∑ i, ∫ p, (f (A m p.1) p.2 - f (A m (Function.update p.1 i p.2)) p.2)
          ∂((Measure.pi fun _ : Fin m => D).prod D) :=
      integral_finsetSum _ fun i _ => hWi.sub (hGi i)
    have hgi : Integrable (fun p : (Fin m → Z) × Z =>
        (∑ i, (f (A m p.1) p.2 - f (A m (Function.update p.1 i p.2)) p.2)) / m)
        ((Measure.pi fun _ : Fin m => D).prod D) :=
      (integrable_finsetSum _ fun i _ => hWi.sub (hGi i)).div_const _
    have hgint : ∫ p, (∑ i, (f (A m p.1) p.2 - f (A m (Function.update p.1 i p.2)) p.2)) / m
          ∂((Measure.pi fun _ : Fin m => D).prod D)
        = ∫ S, risk f D (A m S) ∂(Measure.pi fun _ : Fin m => D) -
          ∫ S, empRisk f S (A m S) ∂(Measure.pi fun _ : Fin m => D) := by
      rw [integral_div, hsum0, Finset.sum_congr rfl fun i _ => integral_sub hWi (hGi i),
        Finset.sum_sub_distrib, hRQ, hEP, Finset.sum_congr rfl fun i _ => hswap i,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sub_div,
        mul_div_cancel_left₀ _ hm'.ne']
    have hpt : ∀ p : (Fin m → Z) × Z,
        (∑ i, (f (A m p.1) p.2 - f (A m (Function.update p.1 i p.2)) p.2)) / m ≤ εs m := by
      intro p
      refine le_trans ?_ (hs m hm p.1 (fun _ => p.2) p.2)
      gcongr with i hi
      rw [abs_sub_comm]
      exact le_abs_self _
    have hle := integral_mono hgi (integrable_const (εs m)) hpt
    rw [hgint] at hle
    simpa using hle
  -- K3: E[min empirical risk] ≤ optimal risk
  have K3 : ∫ S, ermValue f S ∂(Measure.pi fun _ : Fin m => D) ≤ optRisk f D := by
    refine le_ciInf fun h => ?_
    have hEh : Integrable (fun S : Fin m → Z => empRisk f S h) (Measure.pi fun _ : Fin m => D) :=
      integrable_of_abs_le (by
          unfold empRisk
          exact (Finset.measurable_sum _ fun i _ =>
            (hP.measurable h).comp (measurable_pi_apply i)).div_const _) B
        fun S => abs_empRisk_le hP hm S h
    calc ∫ S, ermValue f S ∂(Measure.pi fun _ : Fin m => D)
        ≤ ∫ S, empRisk f S h ∂(Measure.pi fun _ : Fin m => D) :=
          integral_mono hVi hEh fun S => ermValue_le hP hm S h
      _ = risk f D h := integral_empRisk hP D hm h
  have e1 : ∫ S, (risk f D (A m S) - optRisk f D) ∂(Measure.pi fun _ : Fin m => D) =
      ∫ S, risk f D (A m S) ∂(Measure.pi fun _ : Fin m => D) - optRisk f D := by
    rw [integral_sub hRi (integrable_const _)]
    simp
  have e2 : ∫ S, (empRisk f S (A m S) - ermValue f S) ∂(Measure.pi fun _ : Fin m => D) =
      ∫ S, empRisk f S (A m S) ∂(Measure.pi fun _ : Fin m => D) -
        ∫ S, ermValue f S ∂(Measure.pi fun _ : Fin m => D) :=
    integral_sub hEi hVi
  rw [e2] at hAE
  rw [e1]
  linarith

/-! ### Part 2: a stable AERM from a consistent rule -/

lemma kk_le (m : ℕ) : Nat.sqrt (Nat.sqrt m) ≤ m := (Nat.sqrt_le_self _).trans (Nat.sqrt_le_self _)

/-- Run `A` on the first `⌊m^{1/4}⌋` points of the sample. -/
def subRule (A : Rule H Z) : Rule H Z :=
  fun m S => A (Nat.sqrt (Nat.sqrt m)) (fun j => S (Fin.castLE (kk_le m) j))

lemma subRule_measurable {f : H → Z → ℝ} {A : Rule H Z} (hA : MeasurableRule f A) :
    MeasurableRule f (subRule A) := by
  intro m
  have hφ : Measurable (fun p : (Fin m → Z) × Z =>
      ((fun j => p.1 (Fin.castLE (kk_le m) j)), p.2)) :=
    (measurable_pi_lambda _ fun j => (measurable_pi_apply _).comp measurable_fst).prodMk
      measurable_snd
  exact (hA _).comp hφ

lemma subRule_stable [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    (A : Rule H Z) : UniformROStable f (subRule A) (fun m => 2 * B / Real.sqrt m) := by
  intro m hm S S' z'
  show _ ≤ 2 * B / Real.sqrt m
  have hB : 0 ≤ B := (abs_nonneg _).trans (hP.bounded (Classical.arbitrary H) z')
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hι : Function.Injective (Fin.castLE (kk_le m)) := Fin.castLE_injective _
  have hsum : ∑ i, |f (subRule A m (Function.update S i (S' i))) z' - f (subRule A m S) z'| =
      ∑ j : Fin (Nat.sqrt (Nat.sqrt m)), |f (subRule A m (Function.update S (Fin.castLE (kk_le m) j)
        (S' (Fin.castLE (kk_le m) j)))) z' - f (subRule A m S) z'| := by
    symm
    refine Fintype.sum_of_injective (Fin.castLE (kk_le m)) hι _ _ ?_ (fun j => rfl)
    intro i hi
    have : (fun j => Function.update S i (S' i) (Fin.castLE (kk_le m) j)) =
        fun j => S (Fin.castLE (kk_le m) j) := by
      funext j
      apply Function.update_of_ne
      intro hji
      exact hi ⟨j, hji⟩
    simp only [subRule, this, sub_self, abs_zero]
  have hterm : ∀ j : Fin (Nat.sqrt (Nat.sqrt m)),
      |f (subRule A m (Function.update S (Fin.castLE (kk_le m) j)
        (S' (Fin.castLE (kk_le m) j)))) z' - f (subRule A m S) z'| ≤ 2 * B := by
    intro j
    have ha := abs_le.mp (hP.bounded (subRule A m (Function.update S (Fin.castLE (kk_le m) j)
        (S' (Fin.castLE (kk_le m) j)))) z')
    have hb := abs_le.mp (hP.bounded (subRule A m S) z')
    rw [abs_le]
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  have hsum_le : ∑ j : Fin (Nat.sqrt (Nat.sqrt m)), |f (subRule A m (Function.update S
        (Fin.castLE (kk_le m) j) (S' (Fin.castLE (kk_le m) j)))) z' - f (subRule A m S) z'|
      ≤ ((Nat.sqrt (Nat.sqrt m) : ℕ) : ℝ) * (2 * B) := by
    calc _ ≤ ∑ _j : Fin (Nat.sqrt (Nat.sqrt m)), 2 * B := Finset.sum_le_sum fun j _ => hterm j
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hk : ((Nat.sqrt (Nat.sqrt m) : ℕ) : ℝ) ≤ Real.sqrt m :=
    (Nat.cast_le.mpr (Nat.sqrt_le_self _)).trans Real.nat_sqrt_le_real_sqrt
  have hsq : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt (Nat.cast_nonneg m)
  have hsqpos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm'
  rw [hsum, div_le_div_iff₀ hm' hsqpos]
  calc _ ≤ (((Nat.sqrt (Nat.sqrt m) : ℕ) : ℝ) * (2 * B)) * Real.sqrt m :=
        mul_le_mul_of_nonneg_right hsum_le hsqpos.le
    _ ≤ (Real.sqrt m * (2 * B)) * Real.sqrt m := by gcongr
    _ = 2 * B * (Real.sqrt m * Real.sqrt m) := by ring
    _ = 2 * B * m := by rw [hsq]

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

lemma measurable_gap {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) {A : Rule H Z}
    (hA : MeasurableRule f A) {m k : ℕ} (τ : Fin k → Fin m) :
    Measurable (fun S : Fin m → Z => gap f A S τ) :=
  (measurable_empRisk_rule hA (measurable_pi_lambda _ fun j => measurable_pi_apply (τ j))).sub
    (hP.measurable_ermValue m)

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
    (A : Rule H Z) (εc : ℕ → ℝ) (hA : MeasurableRule f A) (hc : UniversallyConsistent f A εc)
    (D : Measure Z) [IsProbabilityMeasure D] {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (hkm : k ≤ m)
    (hcard : (m:ℝ) ^ k ≤ 2 * (m.descFactorial k : ℝ)) (hεk : 0 ≤ εc k) :
    ∫ S, (empRisk f S (A k (fun j => S (Fin.castLE hkm j))) - ermValue f S)
      ∂(Measure.pi fun _ : Fin m => D) ≤ 2 * εc k := by
  classical
  have hGi : ∀ τ : Fin k → Fin m,
      Integrable (fun S : Fin m → Z => gap f A S τ) (Measure.pi fun _ : Fin m => D) :=
    fun τ => integrable_of_abs_le (measurable_gap hP hA τ) (2 * B) fun S => by
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
          integral_comp_perm D π (measurable_gap hP hA _)
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

lemma subRule_aerm [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    (A : Rule H Z) (εc : ℕ → ℝ) (hA : MeasurableRule f A) (hε : IsRate εc)
    (hc : UniversallyConsistent f A εc) :
    UniversalAERM f (subRule A)
      (fun m => 3 * εc (Nat.sqrt (Nat.sqrt m)) + 8 * B / Real.sqrt m) := by
  intro D hD m hm
  have hZ : Nonempty Z := by
    by_contra hZ
    rw [not_nonempty_iff] at hZ
    have h1 := measure_univ (μ := D)
    rw [Measure.eq_zero_of_isEmpty D] at h1
    simp at h1
  have hB : 0 ≤ B :=
    (abs_nonneg _).trans (hP.bounded (Classical.arbitrary H) (Classical.arbitrary Z))
  have hk1 : 1 ≤ Nat.sqrt (Nat.sqrt m) := Nat.sqrt_pos.mpr (Nat.sqrt_pos.mpr hm)
  have hεk : 0 ≤ εc (Nat.sqrt (Nat.sqrt m)) := rate_nonneg hε hk1
  have h4 : Nat.sqrt (Nat.sqrt m) * Nat.sqrt (Nat.sqrt m) *
      (Nat.sqrt (Nat.sqrt m) * Nat.sqrt (Nat.sqrt m)) ≤ m :=
    (Nat.mul_le_mul (Nat.sqrt_le _) (Nat.sqrt_le _)).trans (Nat.sqrt_le _)
  have key := aerm_core hP A εc hA hc D hm hk1 (kk_le m)
    (card_bound hk1 (kk_le m) (two_k_bound h4)) hεk
  have h8 : 0 ≤ 8 * B / Real.sqrt m := by positivity
  show ∫ S, (empRisk f S (subRule A m S) - ermValue f S) ∂(sampleLaw D m) ≤
    3 * εc (Nat.sqrt (Nat.sqrt m)) + 8 * B / Real.sqrt m
  exact le_trans key (by linarith)

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

lemma part1_mp [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    (hL : Learnable f) :
    ∃ A : Rule H Z, MeasurableRule f A ∧ ∃ εstable εerm : ℕ → ℝ,
        IsRate εstable ∧ IsRate εerm ∧
        UniformROStable f A εstable ∧ UniversalAERM f A εerm := by
  obtain ⟨A, hA, ε, hε, hc⟩ := hL
  refine ⟨subRule A, subRule_measurable hA, fun m => 2 * |B| / Real.sqrt m,
    fun m => 3 * ε (Nat.sqrt (Nat.sqrt m)) + 8 * |B| / Real.sqrt m,
    isRate_div_sqrt (by positivity), isRate_cons hε (by positivity), ?_, ?_⟩
  · intro m hm S S' z'
    refine (subRule_stable hP A m hm S S' z').trans ?_
    show 2 * B / Real.sqrt m ≤ 2 * |B| / Real.sqrt m
    gcongr
    exact le_abs_self B
  · intro D hD m hm
    refine (subRule_aerm hP A ε hA hε hc D hD m hm).trans ?_
    show 3 * ε (Nat.sqrt (Nat.sqrt m)) + 8 * B / Real.sqrt m ≤
      3 * ε (Nat.sqrt (Nat.sqrt m)) + 8 * |B| / Real.sqrt m
    gcongr
    exact le_abs_self B

end LearnStability.Characterization.T7Proof

open LearnStability.Characterization MeasureTheory in
theorem solution {H Z : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B) :
    (Learnable f ↔
      ∃ A : Rule H Z, MeasurableRule f A ∧ ∃ εstable εerm : ℕ → ℝ,
        IsRate εstable ∧ IsRate εerm ∧
        UniformROStable f A εstable ∧ UniversalAERM f A εerm) ∧
    (∀ (A : Rule H Z) (εcons : ℕ → ℝ), MeasurableRule f A → IsRate εcons →
      UniversallyConsistent f A εcons →
      ∃ A' : Rule H Z, MeasurableRule f A' ∧
        UniformROStable f A' (fun m => 2 * B / Real.sqrt m) ∧
        UniversalAERM f A'
          (fun m => 3 * εcons (Nat.sqrt (Nat.sqrt m)) + 8 * B / Real.sqrt m)) ∧
    (∀ (A : Rule H Z) (εstable εerm : ℕ → ℝ), MeasurableRule f A →
      UniformROStable f A εstable → UniversalAERM f A εerm →
      UniversallyConsistent f A (fun m => εstable m + εerm m)) := by
  refine ⟨⟨T7Proof.part1_mp hP, ?_⟩, fun A ε hA hε hc => ⟨T7Proof.subRule A,
    T7Proof.subRule_measurable hA, T7Proof.subRule_stable hP A,
    T7Proof.subRule_aerm hP A ε hA hε hc⟩,
    fun A εs εe hA hs he => T7Proof.part3 hP A εs εe hA hs he⟩
  rintro ⟨A, hA, εs, εe, hs', he', hs, he⟩
  exact ⟨A, hA, _, T7Proof.isRate_add hs' he', T7Proof.part3 hP A εs εe hA hs he⟩
