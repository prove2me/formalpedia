-- Prove2me | solution 1 for OAI.PiExponent.eventualTransverseJetSurjectiveForSpatialVolume_spatial_volume_bound_retry9
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T17:51:31.387888+00:00
-- url     : https://prove2.me/submissions/236d6ab9-bf5d-4111-9727-f88c48f6b169

import Definitions.Def_eventualTransverseJetSurjectiveForSpatialVolume_360483bd
import Mathlib

section

open MeasureTheory Set

namespace PiSimplex

noncomputable section

/-- the simplex `{x ≥ 0, ∑ x ≤ c}` -/
def S (n : ℕ) (c : ℝ) : Set (Fin n → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ c}

lemma S_closed (n : ℕ) (c : ℝ) : IsClosed (S n c) := by
  unfold S
  refine IsClosed.inter ?_ ?_
  · have := isClosed_iInter fun i : Fin n =>
      isClosed_le (continuous_const (y := (0 : ℝ))) (continuous_apply (A := fun _ : Fin n => ℝ) i)
    rw [Set.iInter_setOf] at this
    exact this
  · exact isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const

lemma S_meas (n : ℕ) (c : ℝ) : MeasurableSet (S n c) := (S_closed n c).measurableSet

lemma S_neg (n : ℕ) {c : ℝ} (hc : c < 0) : S n c = ∅ := by
  ext x
  simp only [S, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_le]
  intro h
  exact lt_of_lt_of_le hc (Finset.sum_nonneg fun i _ => h i)

lemma slice (n : ℕ) (c t : ℝ) :
    {y : Fin n → ℝ | (Fin.cons t y : Fin (n + 1) → ℝ) ∈ S (n + 1) c} =
      if 0 ≤ t then S n (c - t) else ∅ := by
  ext y
  simp only [S, mem_setOf_eq, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.sum_univ_succ]
  split_ifs with h
  · simp only [h, true_and, mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  · simp [h]

/-- the value of the volume -/
def F (n : ℕ) (c : ℝ) : ENNReal := if 0 ≤ c then ENNReal.ofReal (c ^ n / n.factorial) else 0

lemma integral_pow_sub (n : ℕ) (c : ℝ) :
    ∫ t in (0 : ℝ)..c, (c - t) ^ n / n.factorial = c ^ (n + 1) / (n + 1).factorial := by
  rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_left (fun t => t ^ n)]
  simp only [sub_self, sub_zero, integral_pow]
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

lemma vol_succ (n : ℕ) (c : ℝ) :
    volume (S (n + 1) c) = ∫⁻ t, (if 0 ≤ t then volume (S n (c - t)) else 0) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  rw [← h.measure_preimage_equiv (S (n + 1) c)]
  rw [show (volume : Measure (Fin (n + 1) → ℝ)) = Measure.pi (fun _ => volume) from rfl] at h
  rw [Measure.volume_eq_prod, Measure.prod_apply]
  · congr 1
    ext t
    have : Prod.mk t ⁻¹' ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm ⁻¹'
        S (n + 1) c) = {y : Fin n → ℝ | (Fin.cons t y : Fin (n + 1) → ℝ) ∈ S (n + 1) c} := by
      ext y
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply]; rfl
    rw [this, slice]
    split_ifs <;> simp
  · exact (MeasurableEquiv.measurable _) (S_meas _ _)

theorem vol_S (n : ℕ) (c : ℝ) : volume (S n c) = F n c := by
  induction n generalizing c with
  | zero =>
    unfold F
    split_ifs with hc
    · have : S 0 c = univ := by
        ext x; simp [S, hc]
      rw [this, volume_pi, Measure.pi_univ]; simp
    · rw [S_neg 0 (lt_of_not_ge hc)]; simp
  | succ n ih =>
    rw [vol_succ]
    simp_rw [ih]
    unfold F
    split_ifs with hc
    · have : (fun t : ℝ => if 0 ≤ t then (if 0 ≤ c - t then ENNReal.ofReal ((c - t) ^ n / n.factorial)
          else 0) else 0) = (Icc 0 c).indicator (fun t => ENNReal.ofReal ((c - t) ^ n / n.factorial)) := by
        ext t
        simp only [indicator, mem_Icc, sub_nonneg]
        split_ifs <;> first | rfl | (exfalso; tauto)
      rw [this, lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal,
        integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hc, integral_pow_sub]
      · exact (Continuous.integrableOn_Icc (by fun_prop))
      · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun t ht => ?_)
        have : 0 ≤ c - t := by linarith [ht.2]
        positivity
    · have : (fun t : ℝ => if 0 ≤ t then (if 0 ≤ c - t then ENNReal.ofReal ((c - t) ^ n / n.factorial)
          else 0) else 0) = fun _ => 0 := by
        ext t
        split_ifs with h1 h2 <;> first | rfl | (exfalso; linarith)
      rw [this]; simp

theorem vol_S_of_nonneg (n : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    volume (S n c) = ENNReal.ofReal (c ^ n / n.factorial) := by
  rw [vol_S, F, if_pos hc]

end

end PiSimplex

end

section

open MeasureTheory Set PiSimplex

namespace PiL2

lemma diag_apply {m : ℕ} (w : Fin m → ℝ) (x : Fin m → ℝ) :
    (Matrix.diagonal w).toLin' x = fun i => w i * x i := by
  ext i; simp [Matrix.mulVec_diagonal]

lemma vol_diag {m : ℕ} (w : Fin m → ℝ) (s : Set (Fin m → ℝ)) :
    volume ((fun x : Fin m → ℝ => fun i => w i * x i) '' s) =
      ENNReal.ofReal |∏ i, w i| * volume s := by
  have := Measure.addHaar_image_linearMap (volume : Measure (Fin m → ℝ)) (Matrix.diagonal w).toLin' s
  have hf : ⇑(Matrix.diagonal w).toLin' = fun x i => w i * x i := funext (diag_apply w)
  rw [LinearMap.det_toLin', Matrix.det_diagonal, hf] at this
  exact this

theorem diag_toReal {m : Nat} (w : Fin m → Real) (hw : ∀ i, w i ≠ 0) (s : Set (Fin m → Real)) (hs : MeasurableSet s) :
    (MeasureTheory.volume ((fun x : Fin m → Real => fun i => w i * x i) '' s)).toReal =
      |(∏ i : Fin m, w i)| * (MeasureTheory.volume s).toReal := by
  rw [vol_diag, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]

lemma weighted_image {m : ℕ} (w : Fin m → ℝ) (hw : ∀ i, 0 < w i) (H : ℝ) :
    (fun x : Fin m → ℝ => fun i => w i * x i) '' {x | (∀ i, 0 ≤ x i) ∧ ∑ i, w i * x i ≤ H} = S m H := by
  ext y
  simp only [mem_image, mem_setOf_eq, S]
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨fun i => mul_nonneg (hw i).le (h1 i), h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => y i / w i, ⟨fun i => div_nonneg (h1 i) (hw i).le, ?_⟩, ?_⟩
    · convert h2 using 2 with i; field_simp [(hw i).ne']
    · ext i; field_simp [(hw i).ne']

theorem weighted_div {m : Nat} (w : Fin m → Real) (H : Real) (hw : ∀ i, 0 < w i) (hH : 0 < H) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, w i * x i ≤ H}).toReal =
      (MeasureTheory.volume {y : Fin m → Real | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ H}).toReal / ∏ i : Fin m, w i := by
  have hp : 0 < ∏ i, w i := Finset.prod_pos fun i _ => hw i
  have := vol_diag w {x | (∀ i, 0 ≤ x i) ∧ ∑ i, w i * x i ≤ H}
  rw [weighted_image w hw] at this
  change _ = (volume (S m H)).toReal / _
  rw [this, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos hp]
  field_simp

theorem weighted_formula {m : Nat} (w : Fin m → Real) (B : Real) (hw : ∀ i, 0 < w i) (hB : 0 < B) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ B + ∑ i : Fin m, w i}).toReal =
      (B + ∑ i : Fin m, w i) ^ m /
        ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i := by
  have h0 : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ => (hw i).le
  rw [weighted_div w _ hw (by linarith)]
  change (volume (S m _)).toReal / _ = _
  rw [vol_S_of_nonneg _ (by linarith), ENNReal.toReal_ofReal (by positivity)]

end PiL2

end

section

open MeasureTheory Set

namespace PiL20

noncomputable def rws {m : ℕ} (w : Fin m → ℝ) (R : ℝ) : Finset (Fin m → ℕ) := by
  classical
  exact (Fintype.piFinset (fun i => Finset.range (⌊R / w i⌋₊ + 1))).filter
    (fun a => ∑ i, w i * (a i : ℝ) ≤ R)

noncomputable def srws {m : ℕ} (w : Fin m → ℝ) (R : ℝ) : Finset (Fin m → ℕ) := by
  classical
  exact (rws w R).filter (fun a => ∑ i, w i * (a i : ℝ) < R)

lemma mem_rws {m : ℕ} {w : Fin m → ℝ} {R : ℝ} {a : Fin m → ℕ} :
    a ∈ rws w R ↔ (∀ i, a i < ⌊R / w i⌋₊ + 1) ∧ ∑ i, w i * (a i : ℝ) ≤ R := by
  classical
  simp [rws, Fintype.mem_piFinset]

lemma mem_rws' {m : ℕ} {w : Fin m → ℝ} (hw : ∀ i, 0 < w i) {R : ℝ} {a : Fin m → ℕ} :
    a ∈ rws w R ↔ ∑ i, w i * (a i : ℝ) ≤ R := by
  rw [mem_rws]
  refine ⟨fun h => h.2, fun h => ⟨fun i => ?_, h⟩⟩
  apply Nat.lt_succ_of_le
  apply Nat.le_floor
  rw [le_div_iff₀ (hw i), mul_comm]
  have := Finset.single_le_sum (f := fun j => w j * (a j : ℝ))
    (fun j _ => mul_nonneg (hw j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)
  linarith

lemma mem_srws {m : ℕ} {w : Fin m → ℝ} (hw : ∀ i, 0 < w i) {R : ℝ} {a : Fin m → ℕ} :
    a ∈ srws w R ↔ ∑ i, w i * (a i : ℝ) < R := by
  classical
  simp only [srws, Finset.mem_filter, mem_rws' hw]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

def box {m : ℕ} (n : Fin m → ℕ) : Set (Fin m → ℝ) := {x | ∀ i, (n i : ℝ) ≤ x i ∧ x i < (n i : ℝ) + 1}

lemma box_eq {m : ℕ} (n : Fin m → ℕ) : box n = Set.pi univ fun i => Ico (n i : ℝ) (n i + 1) := by
  ext x; simp [box]

lemma vol_box {m : ℕ} (n : Fin m → ℕ) : volume (box n) = 1 := by
  rw [box_eq, Real.volume_pi_Ico]; simp

lemma box_meas {m : ℕ} (n : Fin m → ℕ) : MeasurableSet (box n) := by
  rw [box_eq]; exact MeasurableSet.univ_pi fun i => measurableSet_Ico

lemma union_eq {m : ℕ} (S : Finset (Fin m → ℕ)) : volume (⋃ n ∈ S, box n) = S.card := by
  rw [measure_biUnion_finset]
  · simp [vol_box]
  · intro a _ b _ hab
    rw [Function.onFun, Set.disjoint_left]
    intro x hxa hxb
    apply hab
    funext i
    obtain ⟨h1, h2⟩ := hxa i
    obtain ⟨h3, h4⟩ := hxb i
    have e1 : (a i : ℝ) < b i + 1 := lt_of_le_of_lt h1 h4
    have e2 : (b i : ℝ) < a i + 1 := lt_of_le_of_lt h3 h2
    have e1' : a i < b i + 1 := by exact_mod_cast e1
    have e2' : b i < a i + 1 := by exact_mod_cast e2
    omega
  · intro a _; exact box_meas a

lemma region_lt_top {m : ℕ} (w : Fin m → ℝ) (hw : ∀ i, 0 < w i) (C : ℝ) :
    volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ C} < ⊤ := by
  refine lt_of_le_of_lt (measure_mono (t := Set.pi univ fun i => Icc (0:ℝ) (|C| / w i)) ?_) ?_
  · rintro x ⟨hx0, hxs⟩ i _
    refine ⟨hx0 i, ?_⟩
    have := Finset.single_le_sum (f := fun j => w j * x j) (fun j _ => mul_nonneg (hw j).le (hx0 j))
      (Finset.mem_univ i)
    rw [le_div_iff₀ (hw i), mul_comm]
    linarith [le_abs_self C]
  · rw [volume_pi_pi]; simp [Real.volume_Icc, ENNReal.prod_lt_top]

theorem card_upper {m : Nat} (w : Fin m → Real) (B : Real) (hw : ∀ i, 0 < w i) (hB : 0 < B) :
    ((rws w B).card : Real) ≤ (B + ∑ i : Fin m, w i) ^ m / ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i := by
  rw [← PiL2.weighted_formula w B hw hB]
  have h1 := union_eq (rws w B)
  have h2 : (⋃ n ∈ rws w B, box n) ⊆
      {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ B + ∑ i : Fin m, w i} := by
    intro x hx
    simp only [mem_iUnion, exists_prop] at hx
    obtain ⟨a, ha, hxa⟩ := hx
    have hs := (mem_rws.1 ha).2
    refine ⟨fun i => le_trans (Nat.cast_nonneg _) (hxa i).1, ?_⟩
    calc ∑ i, w i * x i ≤ ∑ i, (w i * (a i : ℝ) + w i) := Finset.sum_le_sum fun i _ => by
            nlinarith [(hxa i).2, hw i]
      _ = ∑ i, w i * (a i : ℝ) + ∑ i, w i := Finset.sum_add_distrib
      _ ≤ _ := by linarith
  have := ENNReal.toReal_mono (region_lt_top w hw _).ne (measure_mono h2)
  rw [h1] at this
  simpa using this

theorem card_lower {m : Nat} (w : Fin m → Real) (B R : Real) (hw : ∀ i, 0 < w i) (hB : 0 < B)
    (hR : B + ∑ i : Fin m, w i < R) :
    (B + ∑ i : Fin m, w i) ^ m / ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i ≤
      ((srws w R).card : Real) := by
  rw [← PiL2.weighted_formula w B hw hB]
  have h0 : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ => (hw i).le
  have hsub : {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ B + ∑ i : Fin m, w i} ⊆
      ⋃ n ∈ srws w R, box n := by
    rintro x ⟨hx0, hxs⟩
    simp only [mem_iUnion, exists_prop]
    refine ⟨fun i => ⌊x i⌋₊, (mem_srws hw).2 ?_, fun i => ⟨Nat.floor_le (hx0 i), Nat.lt_floor_add_one _⟩⟩
    calc ∑ i, w i * (⌊x i⌋₊ : ℝ) ≤ ∑ i, w i * x i :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (Nat.floor_le (hx0 i)) (hw i).le
      _ < R := by linarith
  have hfin : volume (⋃ n ∈ srws w R, box n) ≠ ⊤ := by
    rw [union_eq]; simp
  have := ENNReal.toReal_mono hfin (measure_mono hsub)
  rw [union_eq] at this
  simpa using this

/-- dimension count: surjectivity of the translated-coefficient map -/
theorem dim_count (m K : Nat) (alpha : Rat) (w : Fin m → Nat) (halpha : 0 < alpha) (hw : ∀ i, 0 < w i)
    (c : Fin K → Fin m → Complex) (H : Nat)
    (hsurj : ∀ J : Fin K → (Fin m →₀ Nat) → Complex,
        ∃ Q : MvPolynomial (Fin m) Complex,
          (∀ e ∈ Q.support,
            (∑ i : Fin m, (w i : Real) * (e i : Real)) ≤ (H : Real)) ∧
          ∀ (j : Fin K) (e : Fin m →₀ Nat),
            (∑ i : Fin m, ((w i : Real) / (alpha : Real)) * (e i : Real)) < (H : Real) →
              MvPolynomial.coeff e
                (MvPolynomial.aeval
                  (fun i => MvPolynomial.C (c j i) + MvPolynomial.X i) Q) = J j e) :
    K * (srws (fun i => (w i : Real) / (alpha : Real)) H).card ≤
      (rws (fun i => (w i : Real)) H).card := by
  classical
  set S := rws (fun i => (w i : Real)) H
  set T := srws (fun i => (w i : Real) / (alpha : Real)) H
  have hα : (0 : ℝ) < alpha := by exact_mod_cast halpha
  have hw' : ∀ i, (0 : ℝ) < (w i : ℝ) := fun i => by exact_mod_cast hw i
  have hw'' : ∀ i, (0 : ℝ) < (w i : ℝ) / alpha := fun i => div_pos (hw' i) hα
  let mon : (Fin m → ℕ) → MvPolynomial (Fin m) ℂ := fun s => MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm s) 1
  let P : (S → ℂ) →ₗ[ℂ] MvPolynomial (Fin m) ℂ :=
    { toFun := fun f => ∑ s : S, f s • mon s
      map_add' := fun f g => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a f => by simp [Finset.smul_sum, smul_smul] }
  let Φ : (S → ℂ) →ₗ[ℂ] (Fin K × T → ℂ) :=
    { toFun := fun f p => MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (p.2 : Fin m → ℕ))
          (MvPolynomial.aeval (fun i => MvPolynomial.C (c p.1 i) + MvPolynomial.X i) (P f))
      map_add' := fun f g => by funext p; simp [map_add]
      map_smul' := fun a f => by funext p; simp [map_smul] }
  have hs : Function.Surjective Φ := by
    intro g
    obtain ⟨Q, hQs, hQc⟩ := hsurj fun j e =>
      if h : (e : Fin m → ℕ) ∈ T then g (j, ⟨_, h⟩) else 0
    refine ⟨fun s => MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (s : Fin m → ℕ)) Q, ?_⟩
    have hPQ : P (fun s => MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (s : Fin m → ℕ)) Q) = Q := by
      change ∑ s : S, _ = Q
      conv_rhs => rw [Q.as_sum]
      rw [Finset.sum_coe_sort S (fun s => MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm s) Q • mon s)]
      symm
      refine Finset.sum_bij_ne_zero (fun e _ _ => (e : Fin m → ℕ)) ?_ ?_ ?_ ?_
      · intro e he _
        exact (mem_rws' hw').2 (hQs e he)
      · intro a _ _ b _ _ h
        exact Finsupp.equivFunOnFinite.injective h
      · intro s hs hne
        refine ⟨Finsupp.equivFunOnFinite.symm s, ?_, ?_, ?_⟩
        · rw [MvPolynomial.mem_support_iff]
          intro h0; apply hne; simp [h0]
        · intro h0; apply hne
          simp only [mon, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
          rw [h0]
        · simp
      · intro e _ _
        simp [mon, MvPolynomial.smul_monomial]
    funext p
    change MvPolynomial.coeff _ (MvPolynomial.aeval _ (P _)) = g p
    rw [hPQ]
    have hT := (mem_srws hw'').1 p.2.2
    rw [hQc p.1 _ (by simpa using hT)]
    obtain ⟨j, e, he⟩ := p
    simp [Finsupp.coe_equivFunOnFinite_symm, he]
  have hle := LinearMap.finrank_range_le Φ
  rw [LinearMap.range_eq_top.2 hs, finrank_top] at hle
  simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_prod] using hle


open Filter Topology in
theorem main_bound (m K : Nat) (alpha : Rat) (w : Fin m → Nat)
    (hm : 0 < m) (hK : 0 < K) (halpha : 0 < alpha)
    (hw : ∀ i, 0 < w i)
    (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (htrans : OAI.PiExponent.eventualTransverseJetSurjectiveForSpatialVolume_360483bd m K alpha w c) :
    (K : Rat) * alpha ^ m ≤ 1 := by
  obtain ⟨D, hD, H0, h⟩ := htrans
  have hα : (0 : ℝ) < alpha := by exact_mod_cast halpha
  set u : Fin m → ℝ := fun i => (w i : ℝ)
  set u' : Fin m → ℝ := fun i => (w i : ℝ) / (alpha : ℝ)
  have hu : ∀ i, 0 < u i := fun i => by simp only [u]; exact_mod_cast hw i
  have hu' : ∀ i, 0 < u' i := fun i => div_pos (hu i) hα
  set a := ∑ i, u' i
  set b := ∑ i, u i
  have hb : 0 ≤ b := Finset.sum_nonneg fun i _ => (hu i).le
  have ha : 0 < a := Finset.sum_pos (fun i _ => hu' i) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hP : 0 < ∏ i, u i := Finset.prod_pos fun i _ => hu i
  have hP' : ∏ i, u' i = (∏ i, u i) / (alpha : ℝ) ^ m := by
    simp only [u', u, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hfact : (0 : ℝ) < ((Nat.factorial m : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
  let x : ℕ → ℝ := fun n => ((D * (n + H0 + 1) : ℕ) : ℝ)
  have hx : Tendsto x atTop atTop := by
    refine tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (fun n => ?_) tendsto_id)
    simp only [id]; nlinarith
  -- key inequality for large n
  have key : ∀ᶠ n in atTop, (K : ℝ) * (alpha : ℝ) ^ m * (1 - a * (x n)⁻¹) ^ m ≤ (1 + b * (x n)⁻¹) ^ m := by
    filter_upwards [hx.eventually_gt_atTop (2 * a)] with n hn
    have hxpos : 0 < x n := by
      have : 0 ≤ a := Finset.sum_nonneg fun i _ => (hu' i).le
      linarith
    have hH : H0 ≤ D * (n + H0 + 1) := by nlinarith
    have hcnt := dim_count m K alpha w halpha hw c _ (h _ hH (Dvd.intro _ rfl))
    have hcnt' : (K : ℝ) * ((srws u' (x n)).card : ℝ) ≤ ((rws u (x n)).card : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).2 hcnt
      rwa [Nat.cast_mul] at this
    have hup := card_upper u (x n) hu hxpos
    have hlow := card_lower u' (x n - 2 * a) (x n) hu' (by linarith) (by linarith)
    rw [hP'] at hlow
    have e1 : (x n - 2 * a + ∑ i, u' i) ^ m = (x n) ^ m * (1 - a * (x n)⁻¹) ^ m := by
      rw [← mul_pow]; congr 1; change _ = x n * (1 - a * (x n)⁻¹); field_simp; ring
    have e2 : (x n + b) ^ m = (x n) ^ m * (1 + b * (x n)⁻¹) ^ m := by
      rw [← mul_pow]; congr 1; field_simp
    rw [e1] at hlow
    rw [e2] at hup
    have hxm : 0 < (x n) ^ m := pow_pos hxpos m
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    have hαm : 0 < (alpha : ℝ) ^ m := pow_pos hα m
    have h3 : (K : ℝ) * ((x n) ^ m * (1 - a * (x n)⁻¹) ^ m / ((Nat.factorial m : ℕ) : ℝ) /
        ((∏ i, u i) / (alpha : ℝ) ^ m)) ≤ (x n) ^ m * (1 + b * (x n)⁻¹) ^ m / ((Nat.factorial m : ℕ) : ℝ) / ∏ i, u i :=
      le_trans (mul_le_mul_of_nonneg_left hlow hK0) (le_trans hcnt' hup)
    have h4 : (K : ℝ) * ((x n) ^ m * (1 - a * (x n)⁻¹) ^ m / ((Nat.factorial m : ℕ) : ℝ) /
        ((∏ i, u i) / (alpha : ℝ) ^ m)) = ((x n) ^ m / ((Nat.factorial m : ℕ) : ℝ) / ∏ i, u i) *
          ((K : ℝ) * (alpha : ℝ) ^ m * (1 - a * (x n)⁻¹) ^ m) := by
      field_simp
    have h5 : (x n) ^ m * (1 + b * (x n)⁻¹) ^ m / ((Nat.factorial m : ℕ) : ℝ) / ∏ i, u i =
        ((x n) ^ m / ((Nat.factorial m : ℕ) : ℝ) / ∏ i, u i) * (1 + b * (x n)⁻¹) ^ m := by
      field_simp
    rw [h4, h5] at h3
    exact le_of_mul_le_mul_left h3 (by positivity)
  have hinv : Tendsto (fun n => (x n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hx
  have hl : Tendsto (fun n => (K : ℝ) * (alpha : ℝ) ^ m * (1 - a * (x n)⁻¹) ^ m) atTop
      (𝓝 ((K : ℝ) * (alpha : ℝ) ^ m * (1 - a * 0) ^ m)) :=
    ((tendsto_const_nhds.sub (hinv.const_mul a)).pow m).const_mul _
  have hr : Tendsto (fun n => (1 + b * (x n)⁻¹) ^ m) atTop (𝓝 ((1 + b * 0) ^ m)) :=
    (tendsto_const_nhds.add (hinv.const_mul b)).pow m
  have := le_of_tendsto_of_tendsto hl hr key
  simp at this
  exact_mod_cast this

end PiL20

end

open OAI OAI.PiExponent
open scoped BigOperators

theorem solution
    (m K : Nat) (alpha : Rat) (w : Fin m → Nat)
    (hm : 0 < m) (hK : 0 < K) (halpha : 0 < alpha)
    (hw : ∀ i, 0 < w i)
    (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (htrans : OAI.PiExponent.eventualTransverseJetSurjectiveForSpatialVolume_360483bd m K alpha w c) :
    (K : Rat) * alpha ^ m ≤ 1 := by
  apply PiL20.main_bound <;> assumption
