-- Prove2me | solution 1 for LindleyQueue.Stability.lindley_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T06:03:41.264642+00:00
-- url     : https://prove2.me/submissions/6f59ba64-f6e6-4f2d-8210-e046b4b63147

import Mathlib
import Definitions.Def_LindleyQueue_Stability_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology

namespace LindleyAux

open LindleyQueue.Stability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- event: all partial sums up to `r` are `≤ x`. -/
def A (Q : Input Ω P) (r : ℕ) (x : ℝ) : Set Ω := {ω | ∀ n ≤ r, Q.U n ω ≤ x}

lemma measurable_u (Q : Input Ω P) (r : ℕ) : Measurable (Q.u r) :=
  (Q.measurable_s r).sub (Q.measurable_t r)

lemma measurable_U (Q : Input Ω P) (n : ℕ) : Measurable (Q.U n) := by
  unfold Input.U
  exact Finset.measurable_sum _ (fun i _ => measurable_u Q i)

lemma measurableSet_A (Q : Input Ω P) (r : ℕ) (x : ℝ) : MeasurableSet (A Q r x) := by
  have : A Q r x = ⋂ n ∈ Finset.range (r + 1), {ω | Q.U n ω ≤ x} := by
    ext ω; simp [A]
  rw [this]
  exact Finset.measurableSet_biInter _ (fun n _ => measurableSet_le (measurable_U Q n) measurable_const)

/-! ### pair space and path functionals -/

/-- the pair space of (service, interarrival) sequences -/
abbrev Pt := (ℕ → ℝ) × (ℕ → ℝ)

/-- reindexed input sequences -/
def Sg (Q : Input Ω P) (g : ℕ → ℕ) (ω : Ω) : Pt :=
  (fun i => Q.s (g i) ω, fun i => Q.t (g i) ω)

lemma measurable_Sg (Q : Input Ω P) (g : ℕ → ℕ) : Measurable (Sg Q g) :=
  (measurable_pi_lambda _ fun i => Q.measurable_s (g i)).prodMk
    (measurable_pi_lambda _ fun i => Q.measurable_t (g i))

lemma identDistrib_Sg [IsProbabilityMeasure P] (Q : Input Ω P) {g : ℕ → ℕ} (hg : g.Injective) :
    IdentDistrib (Sg Q g) (Sg Q id) P P := by
  have hφ : Measurable (fun (f : ℕ → ℝ) (i : ℕ) => f (g i)) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply (g i))
  exact IdentDistrib.prodMk
    (IdentDistrib.pi (X := fun i ω => Q.s (g i) ω) (Y := fun i ω => Q.s i ω)
      (fun i => (Q.identDistrib_s (g i)).trans (Q.identDistrib_s i).symm)
      (Q.iIndepFun_s.precomp hg) Q.iIndepFun_s)
    (IdentDistrib.pi (X := fun i ω => Q.t (g i) ω) (Y := fun i ω => Q.t i ω)
      (fun i => (Q.identDistrib_t (g i)).trans (Q.identDistrib_t i).symm)
      (Q.iIndepFun_t.precomp hg) Q.iIndepFun_t)
    (Q.indepFun_s_t.comp hφ hφ) Q.indepFun_s_t

/-- partial sums on pair space -/
def Us (p : Pt) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, (p.1 i - p.2 i)

lemma measurable_Us (n : ℕ) : Measurable (fun p : Pt => Us p n) := by
  unfold Us
  exact Finset.measurable_sum _ (fun i _ =>
    ((measurable_pi_apply i).comp measurable_fst).sub ((measurable_pi_apply i).comp measurable_snd))

lemma U_eq (Q : Input Ω P) (n : ℕ) (ω : Ω) : Q.U n ω = Us (Sg Q id ω) n := rfl

lemma u_eq (Q : Input Ω P) (i : ℕ) : Q.u i = (fun p : Pt => p.1 0 - p.2 0) ∘ Sg Q (Equiv.swap 0 i) := by
  funext ω; simp [Sg, Input.u]

lemma identDistrib_u [IsProbabilityMeasure P] (Q : Input Ω P) (i : ℕ) :
    IdentDistrib (Q.u i) (Q.u 0) P P := by
  have hm : Measurable (fun p : Pt => p.1 0 - p.2 0) :=
    ((measurable_pi_apply 0).comp measurable_fst).sub ((measurable_pi_apply 0).comp measurable_snd)
  have h := (identDistrib_Sg Q (Equiv.swap 0 i).injective).comp hm
  rw [← u_eq] at h
  have h0 : (fun p : Pt => p.1 0 - p.2 0) ∘ Sg Q id = Q.u 0 := by funext ω; simp [Sg, Input.u]
  rwa [h0] at h

/-! ### duality -/

lemma w_le_iff (Q : Input Ω P) (ω : Ω) : ∀ (r : ℕ) (x : ℝ),
    Q.w r ω ≤ x ↔ ∀ k ≤ r, ∑ i ∈ Finset.range k, Q.u (r - 1 - i) ω ≤ x
  | 0, x => by
    simp only [Input.w, nonpos_iff_eq_zero, forall_eq, Finset.range_zero, Finset.sum_empty]
  | r + 1, x => by
    have ih := w_le_iff Q ω r (x - Q.u r ω)
    have hsum : ∀ j, ∑ i ∈ Finset.range (j + 1), Q.u (r + 1 - 1 - i) ω
        = (∑ i ∈ Finset.range j, Q.u (r - 1 - i) ω) + Q.u r ω := by
      intro j
      rw [Finset.sum_range_succ']
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        rw [show r + 1 - 1 - (i + 1) = r - 1 - i by omega]
    simp only [Input.w]
    rw [max_le_iff]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      cases k with
      | zero => simpa using h2
      | succ j =>
        rw [hsum]
        have := (ih.mp (by linarith)) j (by omega)
        linarith
    · intro h
      refine ⟨?_, by simpa using h 0 (Nat.zero_le _)⟩
      have : Q.w r ω ≤ x - Q.u r ω := ih.mpr (fun k hk => by
        have := h (k + 1) (by omega)
        rw [hsum] at this
        linarith)
      linarith

/-- reversal of `[0, r)` -/
def rho (r : ℕ) (i : ℕ) : ℕ := if i < r then r - 1 - i else i

lemma rho_injective (r : ℕ) : (rho r).Injective := by
  intro a b h
  simp only [rho] at h
  split_ifs at h <;> omega

lemma F_eq [IsProbabilityMeasure P] (Q : Input Ω P) (r : ℕ) (x : ℝ) :
    Q.F r x = P.real (A Q r x) := by
  set B : Set Pt := {p | ∀ k ≤ r, Us p k ≤ x} with hB
  have hBm : MeasurableSet B := by
    have : B = ⋂ k ∈ Finset.range (r + 1), {p | Us p k ≤ x} := by
      ext p; simp [hB]
    rw [this]
    exact Finset.measurableSet_biInter _ (fun k _ => measurableSet_le (measurable_Us k) measurable_const)
  have h1 : {ω | Q.w r ω ≤ x} = Sg Q (rho r) ⁻¹' B := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hB, w_le_iff Q ω r x]
    apply forall_congr'; intro k; apply imp_congr_right; intro hk
    unfold Us Sg
    rw [iff_eq_eq]; congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < r := lt_of_lt_of_le (Finset.mem_range.mp hi) hk
    simp [rho, hi', Input.u]
  have h2 : A Q r x = Sg Q id ⁻¹' B := by
    ext ω; simp [A, hB, U_eq]
  unfold Input.F
  rw [h1, h2]
  simp only [Measure.real]
  rw [(identDistrib_Sg Q (rho_injective r)).measure_mem_eq hBm]

/-! ### strong law -/

lemma integral_u [IsProbabilityMeasure P] (Q : Input Ω P) :
    ∫ ω, Q.u 0 ω ∂P = ∫ ω, Q.s 0 ω ∂P - ∫ ω, Q.t 0 ω ∂P := by
  simp only [Input.u]
  exact integral_sub Q.integrable_s Q.integrable_t

lemma slln_U [IsProbabilityMeasure P] (Q : Input Ω P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => Q.U n ω / n) atTop (𝓝 (∫ ω, Q.u 0 ω ∂P)) := by
  have hs := strong_law_ae_real Q.s Q.integrable_s (fun i j hij => Q.iIndepFun_s.indepFun hij)
    Q.identDistrib_s
  have ht := strong_law_ae_real Q.t Q.integrable_t (fun i j hij => Q.iIndepFun_t.indepFun hij)
    Q.identDistrib_t
  filter_upwards [hs, ht] with ω h1 h2
  rw [integral_u]
  refine (h1.sub h2).congr (fun n => ?_)
  simp only [Input.U, Input.u, Finset.sum_sub_distrib, sub_div]

lemma bdd_of_neg [IsProbabilityMeasure P] (Q : Input Ω P) (hneg : ∫ ω, Q.u 0 ω ∂P < 0) :
    ∀ᵐ ω ∂P, BddAbove (Set.range fun n => Q.U n ω) := by
  filter_upwards [slln_U Q] with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hω.eventually (gt_mem_nhds hneg))
  refine ⟨∑ n ∈ Finset.range (N + 1), |Q.U n ω|, ?_⟩
  rintro _ ⟨n, rfl⟩
  by_cases hn : n ≤ N
  · exact (le_abs_self _).trans (Finset.single_le_sum (f := fun n => |Q.U n ω|)
      (fun i _ => abs_nonneg _) (Finset.mem_range.mpr (by omega)))
  · have h1 := hN n (by omega)
    have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have h2 := mul_neg_of_neg_of_pos h1 hpos
    rw [div_mul_cancel₀ _ hpos.ne'] at h2
    exact h2.le.trans (Finset.sum_nonneg (fun i _ => abs_nonneg _))

lemma bdd_of_zero [IsProbabilityMeasure P] (Q : Input Ω P) (hz : Q.u 0 =ᵐ[P] 0) :
    ∀ᵐ ω ∂P, BddAbove (Set.range fun n => Q.U n ω) := by
  have hall : ∀ i, Q.u i =ᵐ[P] 0 := by
    intro i
    exact (identDistrib_u Q i).symm.ae_snd (p := fun y => y = 0) (measurableSet_eq_fun measurable_id measurable_const) hz
  have hall' : ∀ᵐ ω ∂P, ∀ i, Q.u i ω = 0 := ae_all_iff.mpr hall
  filter_upwards [hall'] with ω hω
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  simp [Input.U, hω]

lemma bdd_of [IsProbabilityMeasure P] (Q : Input Ω P)
    (h : ∫ ω, Q.u 0 ω ∂P < 0 ∨ Q.u 0 =ᵐ[P] 0) :
    ∀ᵐ ω ∂P, BddAbove (Set.range fun n => Q.U n ω) := by
  rcases h with h | h
  · exact bdd_of_neg Q h
  · exact bdd_of_zero Q h

lemma unbdd_pos [IsProbabilityMeasure P] (Q : Input Ω P) (hpos : 0 < ∫ ω, Q.u 0 ω ∂P) :
    ∀ᵐ ω ∂P, ¬ BddAbove (Set.range fun n => Q.U n ω) := by
  filter_upwards [slln_U Q] with ω hω
  rintro ⟨B, hB⟩
  have ht : Tendsto (fun n : ℕ => Q.U n ω / n * n) atTop atTop :=
    hω.pos_mul_atTop hpos tendsto_natCast_atTop_atTop
  obtain ⟨n, hn⟩ := ((ht.eventually (eventually_gt_atTop B)).and (eventually_ge_atTop 1)).exists
  have hpos' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h3 : Q.U n ω / n * n = Q.U n ω := div_mul_cancel₀ _ hpos'.ne'
  have h4 := hB ⟨n, rfl⟩
  simp only at h4
  linarith [hn.1]

/-! ### running maximum on pair space -/

/-- running maximum `max_{k ≤ n} Us p k` -/
def Mx (p : Pt) : ℕ → ℝ
  | 0 => 0
  | n + 1 => max (Mx p n) (Us p (n + 1))

def shift (p : Pt) : Pt := (fun i => p.1 (i + 1), fun i => p.2 (i + 1))

lemma Us_zero (p : Pt) : Us p 0 = 0 := by simp [Us]

lemma Us_succ (p : Pt) (k : ℕ) : Us p (k + 1) = (p.1 0 - p.2 0) + Us (shift p) k := by
  unfold Us shift
  rw [Finset.sum_range_succ']
  ring

lemma Mx_succ (p : Pt) : ∀ n, Mx p (n + 1) = max 0 ((p.1 0 - p.2 0) + Mx (shift p) n)
  | 0 => by simp [Mx, Us_succ, Us_zero]
  | n + 1 => by
    rw [Mx, Mx_succ p n, Us_succ, Mx, max_assoc, max_add_add_left]

lemma Mx_nonneg (p : Pt) : ∀ n, 0 ≤ Mx p n
  | 0 => le_rfl
  | n + 1 => le_max_of_le_left (Mx_nonneg p n)

lemma Mx_mono (p : Pt) : Monotone (Mx p) :=
  monotone_nat_of_le_succ (fun n => le_max_left _ _)

lemma Us_le_Mx (p : Pt) : ∀ n k, k ≤ n → Us p k ≤ Mx p n
  | 0, k, hk => by
    rw [Nat.le_zero.mp hk, Us_zero]; exact le_rfl
  | n + 1, k, hk => by
    rcases Nat.lt_or_ge k (n + 1) with h | h
    · exact (Us_le_Mx p n k (by omega)).trans (le_max_left _ _)
    · rw [show k = n + 1 by omega]; exact le_max_right _ _

lemma Mx_le (p : Pt) (c : ℝ) (hc0 : 0 ≤ c) : ∀ n, (∀ k ≤ n, Us p k ≤ c) → Mx p n ≤ c
  | 0, _ => hc0
  | n + 1, h => max_le (Mx_le p c hc0 n (fun k hk => h k (by omega))) (h (n + 1) le_rfl)

lemma measurable_Mx : ∀ n, Measurable (fun p : Pt => Mx p n)
  | 0 => measurable_const
  | n + 1 => (measurable_Mx n).max (measurable_Us (n + 1))

lemma Mx_le_sum (p : Pt) (h1 : ∀ i, 0 ≤ p.1 i) (h2 : ∀ i, 0 ≤ p.2 i) (n : ℕ) :
    Mx p n ≤ ∑ i ∈ Finset.range n, p.1 i := by
  apply Mx_le p _ (Finset.sum_nonneg (fun i _ => h1 i)) n
  intro k hk
  calc Us p k ≤ ∑ i ∈ Finset.range k, p.1 i :=
        Finset.sum_le_sum (fun i _ => sub_le_self _ (h2 i))
    _ ≤ ∑ i ∈ Finset.range n, p.1 i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hk)
          (fun i _ _ => h1 i)

lemma bdd_Mx_of_bdd_Us (p : Pt) (h : BddAbove (Set.range (Us p))) : BddAbove (Set.range (Mx p)) := by
  obtain ⟨B, hB⟩ := h
  refine ⟨max B 0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact Mx_le p _ (le_max_right _ _) n (fun k _ => (hB ⟨k, rfl⟩).trans (le_max_left _ _))

/-! ### the Laplace functional -/

noncomputable def Psi (p : Pt) : ℝ := ⨅ n, Real.exp (-(Mx p n))

lemma Psi_anti (p : Pt) : Antitone (fun n => Real.exp (-(Mx p n))) :=
  fun _ _ hab => Real.exp_le_exp.mpr (neg_le_neg (Mx_mono p hab))

lemma Psi_bddBelow (p : Pt) : BddBelow (Set.range (fun n => Real.exp (-(Mx p n)))) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; exact (Real.exp_pos _).le⟩

lemma tendsto_Psi (p : Pt) : Tendsto (fun n => Real.exp (-(Mx p n))) atTop (𝓝 (Psi p)) :=
  tendsto_atTop_ciInf (Psi_anti p) (Psi_bddBelow p)

lemma Psi_le (p : Pt) (n : ℕ) : Psi p ≤ Real.exp (-(Mx p n)) := ciInf_le (Psi_bddBelow p) n

lemma Psi_nonneg (p : Pt) : 0 ≤ Psi p :=
  le_ciInf (fun n => (Real.exp_pos _).le)

lemma Psi_le_one (p : Pt) : Psi p ≤ 1 := by
  have := Psi_le p 0
  simpa [Mx] using this

lemma measurable_Psi : Measurable Psi :=
  Measurable.iInf (fun n => Real.measurable_exp.comp (measurable_Mx n).neg)

lemma Psi_pos_of_bdd (p : Pt) (h : BddAbove (Set.range (Mx p))) : 0 < Psi p := by
  obtain ⟨B, hB⟩ := h
  have : Real.exp (-B) ≤ Psi p :=
    le_ciInf (fun n => Real.exp_le_exp.mpr (neg_le_neg (hB ⟨n, rfl⟩)))
  exact lt_of_lt_of_le (Real.exp_pos _) this

lemma Psi_rec (p : Pt)
    (H : ∀ c : ℝ, (∀ n, Mx (shift p) n ≤ c) → 0 ≤ (p.1 0 - p.2 0) + c) :
    Psi p = Real.exp (-(p.1 0 - p.2 0)) * Psi (shift p) := by
  set d := p.1 0 - p.2 0 with hd
  have h1 : Tendsto (fun n => Real.exp (-(Mx p (n + 1)))) atTop (𝓝 (Psi p)) :=
    (tendsto_Psi p).comp (tendsto_add_atTop_nat 1)
  have h2 : ∀ n, Real.exp (-(Mx p (n + 1)))
      = min 1 (Real.exp (-d) * Real.exp (-(Mx (shift p) n))) := by
    intro n
    rw [Mx_succ, ← Real.exp_add, ← hd]
    rcases le_total 0 (d + Mx (shift p) n) with h | h
    · rw [max_eq_right h, min_eq_right]
      · ring_nf
      · rw [Real.exp_le_one_iff]; linarith
    · rw [max_eq_left h, min_eq_left]
      · simp
      · rw [Real.one_le_exp_iff]; linarith
  have h3 : Tendsto (fun n => min 1 (Real.exp (-d) * Real.exp (-(Mx (shift p) n)))) atTop
      (𝓝 (min 1 (Real.exp (-d) * Psi (shift p)))) :=
    tendsto_const_nhds.min ((tendsto_Psi (shift p)).const_mul _)
  have hPsi : Psi p = min 1 (Real.exp (-d) * Psi (shift p)) :=
    tendsto_nhds_unique (h1.congr h2) h3
  rw [hPsi, min_eq_right]
  by_contra hgt
  push_neg at hgt
  have hpos : 0 < Psi (shift p) := by
    rcases (Psi_nonneg (shift p)).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hgt; linarith
  have hc : ∀ n, Mx (shift p) n ≤ -Real.log (Psi (shift p)) := by
    intro n
    have := Real.log_le_log hpos (Psi_le (shift p) n)
    rw [Real.log_exp] at this
    linarith
  have hH := H _ hc
  have he : Real.exp (-d) * Psi (shift p) = Real.exp (-d + Real.log (Psi (shift p))) := by
    rw [Real.exp_add, Real.exp_log hpos]
  rw [he, ← Real.exp_zero] at hgt
  have := Real.exp_lt_exp.mp hgt
  linarith

/-! ### independence of the head from the tail -/

lemma iIndepFun_bool [IsProbabilityMeasure P] (Q : Input Ω P) :
    iIndepFun (fun (b : Bool) (ω : Ω) => (fun j => cond b (Q.s j ω) (Q.t j ω))) P := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  set A : Set (ℕ → ℝ) := if true ∈ S then sets true else Set.univ with hA
  set B : Set (ℕ → ℝ) := if false ∈ S then sets false else Set.univ with hB
  have hAm : MeasurableSet A := by
    rw [hA]; split_ifs with h
    · exact hsets true h
    · exact MeasurableSet.univ
  have hBm : MeasurableSet B := by
    rw [hB]; split_ifs with h
    · exact hsets false h
    · exact MeasurableSet.univ
  have key := Q.indepFun_s_t.measure_inter_preimage_eq_mul A B hAm hBm
  have e1 : (⋂ i ∈ S, (fun ω => (fun j => cond i (Q.s j ω) (Q.t j ω))) ⁻¹' sets i)
      = (fun ω r => Q.s r ω) ⁻¹' A ∩ (fun ω r => Q.t r ω) ⁻¹' B := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, hA, hB]
    constructor
    · intro h
      constructor
      · split_ifs with hm
        · exact h true hm
        · trivial
      · split_ifs with hm
        · exact h false hm
        · trivial
    · rintro ⟨ha, hb⟩ i hi
      cases i
      · rw [if_pos hi] at hb; exact hb
      · rw [if_pos hi] at ha; exact ha
  have e2 : ∀ i, i ∈ S → P ((fun ω => (fun j => cond i (Q.s j ω) (Q.t j ω))) ⁻¹' sets i)
      = P ((fun ω => (fun j => cond i (Q.s j ω) (Q.t j ω))) ⁻¹'
          (if i ∈ S then sets i else Set.univ)) := by
    intro i hi; rw [if_pos hi]
  rw [e1, key, Finset.prod_congr rfl e2]
  rw [Finset.prod_subset (Finset.subset_univ S) (fun i _ hi => by rw [if_neg hi]; simp)]
  rw [Fintype.prod_bool]
  simp only [cond_true, cond_false, hA, hB]

lemma indep_head_tail [IsProbabilityMeasure P] (Q : Input Ω P) :
    IndepFun (fun ω => (Q.s 0 ω, Q.t 0 ω)) (Sg Q (· + 1)) P := by
  set X : Bool → ℕ → Ω → ℝ := fun b j ω => cond b (Q.s j ω) (Q.t j ω) with hX
  have mX : ∀ b j, Measurable (X b j) := by
    intro b j; cases b
    · exact Q.measurable_t j
    · exact Q.measurable_s j
  have h2 : ∀ b, iIndepFun (X b) P := by
    intro b; cases b
    · exact Q.iIndepFun_t
    · exact Q.iIndepFun_s
  have hZ := iIndepFun_uncurry' mX (iIndepFun_bool Q) h2
  set m : Bool × ℕ → MeasurableSpace Ω :=
    fun p => MeasurableSpace.comap (fun ω => X p.1 p.2 ω) inferInstance with hm
  have hZ' : iIndep m P := hZ
  have h_le : ∀ p, m p ≤ (inferInstance : MeasurableSpace Ω) :=
    fun p => (mX p.1 p.2).comap_le
  have hInd := indep_iSup_of_disjoint h_le hZ'
    (S := {p : Bool × ℕ | p.2 = 0}) (T := {p : Bool × ℕ | p.2 ≠ 0})
    (Set.disjoint_left.mpr (fun p h1 h2 => h2 h1))
  rw [IndepFun_iff_Indep]
  have hmeasX : ∀ p : Bool × ℕ, Measurable[m p] (X p.1 p.2) := fun p => comap_measurable _
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hInd ?_) ?_
  · apply Measurable.comap_le
    have hs : Measurable[⨆ p ∈ {p : Bool × ℕ | p.2 = 0}, m p] (Q.s 0) :=
      (hmeasX (true, 0)).mono (le_iSup₂ (f := fun p _ => m p) (true, 0) rfl) le_rfl
    have ht : Measurable[⨆ p ∈ {p : Bool × ℕ | p.2 = 0}, m p] (Q.t 0) :=
      (hmeasX (false, 0)).mono (le_iSup₂ (f := fun p _ => m p) (false, 0) rfl) le_rfl
    exact hs.prodMk ht
  · apply Measurable.comap_le
    have hs : ∀ j, Measurable[⨆ p ∈ {p : Bool × ℕ | p.2 ≠ 0}, m p] (Q.s (j + 1)) := fun j =>
      (hmeasX (true, j + 1)).mono
        (le_iSup₂ (f := fun p _ => m p) (true, j + 1) (Nat.succ_ne_zero j)) le_rfl
    have ht : ∀ j, Measurable[⨆ p ∈ {p : Bool × ℕ | p.2 ≠ 0}, m p] (Q.t (j + 1)) := fun j =>
      (hmeasX (false, j + 1)).mono
        (le_iSup₂ (f := fun p _ => m p) (false, j + 1) (Nat.succ_ne_zero j)) le_rfl
    exact Measurable.prodMk (m := ⨆ p ∈ {p : Bool × ℕ | p.2 ≠ 0}, m p)
      (@measurable_pi_lambda Ω ℕ (fun _ => ℝ) (⨆ p ∈ {p : Bool × ℕ | p.2 ≠ 0}, m p) _ _ hs)
      (@measurable_pi_lambda Ω ℕ (fun _ => ℝ) (⨆ p ∈ {p : Bool × ℕ | p.2 ≠ 0}, m p) _ _ ht)

/-! ### `E (max_{k ≤ n} U_k) = o(n)` for a mean-zero walk -/

lemma Mx_div_tendsto (p : Pt) (h : Tendsto (fun n : ℕ => Us p n / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Mx p n / n) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h (ε / 2) (by linarith)
  have hU : ∀ n ≥ N + 1, Us p n ≤ ε / 2 * n := by
    intro n hn
    have h1 := hN n (by omega)
    rw [Real.dist_eq, sub_zero] at h1
    have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have := (abs_lt.mp h1).2
    rw [div_lt_iff₀ hpos] at this
    linarith
  have hM : ∀ n ≥ N + 1, Mx p n ≤ max (Mx p (N + 1)) (ε / 2 * n) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact le_max_left _ _
    | succ n hn ih =>
      show max (Mx p n) (Us p (n + 1)) ≤ _
      apply max_le
      · refine ih.trans (max_le_max le_rfl ?_)
        have : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
        nlinarith
      · exact (hU (n + 1) (by omega)).trans (le_max_right _ _)
  obtain ⟨K, hK⟩ := exists_nat_gt (Mx p (N + 1) / (ε / 2))
  refine ⟨max (N + 1) (K + 1), fun n hn => ?_⟩
  have hn1 : N + 1 ≤ n := le_of_max_le_left hn
  have hn2 : K + 1 ≤ n := le_of_max_le_right hn
  have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (Mx_nonneg p n) hpos.le),
    div_lt_iff₀ hpos]
  have hKn : (K : ℝ) + 1 ≤ n := by exact_mod_cast hn2
  have hMN : Mx p (N + 1) < ε / 2 * n := by
    rw [div_lt_iff₀ (by linarith)] at hK
    nlinarith
  calc Mx p n ≤ max (Mx p (N + 1)) (ε / 2 * n) := hM n hn1
    _ ≤ ε / 2 * n := max_le hMN.le le_rfl
    _ < ε * n := by nlinarith

lemma integrable_Mx [IsProbabilityMeasure P] (Q : Input Ω P) (g : ℕ → ℕ) (n : ℕ) :
    Integrable (fun ω => Mx (Sg Q g ω) n) P := by
  have hint : Integrable (fun ω => ∑ i ∈ Finset.range n, Q.s (g i) ω) P :=
    integrable_finset_sum _ (fun i _ => (Q.identDistrib_s (g i)).integrable_iff.mpr Q.integrable_s)
  refine hint.mono' ((measurable_Mx n).comp (measurable_Sg Q g)).aestronglyMeasurable
    (Eventually.of_forall (fun ω => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (Mx_nonneg _ n)]
  exact Mx_le_sum (Sg Q g ω) (fun i => Q.nonneg_s _ ω) (fun i => Q.nonneg_t _ ω) n

lemma small_mean [IsProbabilityMeasure P] (Q : Input Ω P) (h0 : ∫ ω, Q.u 0 ω ∂P = 0)
    (ε : ℝ) (hε : 0 < ε) : ∃ n : ℕ, 1 ≤ n ∧ (∫ ω, Mx (Sg Q id ω) n ∂P) / n < ε := by
  by_contra hcon
  push_neg at hcon
  set c := ∫ ω, Q.s 0 ω ∂P with hc
  set f : ℕ → Ω → ℝ := fun n ω => Mx (Sg Q id ω) n / n with hfdef
  set g : ℕ → Ω → ℝ := fun n ω => (∑ i ∈ Finset.range n, Q.s i ω) / n with hgdef
  have hsint : ∀ i, Integrable (Q.s i) P := fun i =>
    (Q.identDistrib_s i).integrable_iff.mpr Q.integrable_s
  have hfg : ∀ n ω, f n ω ≤ g n ω := fun n ω =>
    div_le_div_of_nonneg_right
      (Mx_le_sum (Sg Q id ω) (fun i => Q.nonneg_s _ ω) (fun i => Q.nonneg_t _ ω) n)
      (Nat.cast_nonneg n)
  have hfi : ∀ n, Integrable (f n) P := fun n => (integrable_Mx Q id n).div_const _
  have hgi : ∀ n, Integrable (g n) P := fun n =>
    (integrable_finset_sum _ (fun i _ => hsint i)).div_const _
  have hgint : ∀ n, 1 ≤ n → ∫ ω, g n ω ∂P = c := by
    intro n hn
    simp only [hgdef]
    rw [integral_div, integral_finset_sum _ (fun i _ => hsint i)]
    have : ∀ i ∈ Finset.range n, ∫ ω, Q.s i ω ∂P = c := fun i _ =>
      (Q.identDistrib_s i).integral_eq
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hpos : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    field_simp
  have hfint : ∀ n, ∫ ω, f n ω ∂P = (∫ ω, Mx (Sg Q id ω) n ∂P) / n := fun n => by
    simp only [hfdef]; rw [integral_div]
  have hcε : ε ≤ c := by
    have h1 := hcon 1 le_rfl
    rw [← hfint] at h1
    have := integral_mono (hfi 1) (hgi 1) (hfg 1)
    rw [hgint 1 le_rfl] at this
    linarith
  have hs := strong_law_ae_real Q.s Q.integrable_s (fun i j hij => Q.iIndepFun_s.indepFun hij)
    Q.identDistrib_s
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => ENNReal.ofReal (g n ω - f n ω)) atTop
      (𝓝 (ENNReal.ofReal c)) := by
    filter_upwards [hs, slln_U Q] with ω h1 h2
    rw [h0] at h2
    have hf := Mx_div_tendsto (Sg Q id ω) h2
    have := h1.sub hf
    rw [sub_zero] at this
    exact (ENNReal.continuous_ofReal.tendsto _).comp this
  have hfatou := lintegral_liminf_le' (μ := P) (u := atTop)
    (f := fun n ω => ENNReal.ofReal (g n ω - f n ω))
    (fun n => (((hgi n).sub (hfi n)).aemeasurable).ennreal_ofReal)
  have hlhs : ∫⁻ ω, liminf (fun n => ENNReal.ofReal (g n ω - f n ω)) atTop ∂P
      = ENNReal.ofReal c := by
    rw [lintegral_congr_ae (hlim.mono (fun ω h => h.liminf_eq))]
    simp
  have hrhs : ∀ n, 1 ≤ n →
      ∫⁻ ω, ENNReal.ofReal (g n ω - f n ω) ∂P ≤ ENNReal.ofReal (c - ε) := by
    intro n hn
    have e := ofReal_integral_eq_lintegral_ofReal ((hgi n).sub (hfi n))
      (Eventually.of_forall (fun ω => sub_nonneg.mpr (hfg n ω)))
    simp only [Pi.sub_apply] at e
    rw [← e]
    apply ENNReal.ofReal_le_ofReal
    have e2 := integral_sub (hgi n) (hfi n)
    rw [e2, hgint n hn, hfint n]
    linarith [hcon n hn]
  have hli : liminf (fun n => ∫⁻ ω, ENNReal.ofReal (g n ω - f n ω) ∂P) atTop
      ≤ ENNReal.ofReal (c - ε) :=
    liminf_le_of_frequently_le' (eventually_atTop.mpr ⟨1, hrhs⟩).frequently
  have hfin := hlhs ▸ hfatou.trans hli
  rw [ENNReal.ofReal_le_ofReal_iff (by linarith)] at hfin
  linarith

/-! ### the mean-zero case -/

lemma unbdd_zero [IsProbabilityMeasure P] (Q : Input Ω P) (h0 : ∫ ω, Q.u 0 ω ∂P = 0)
    (h1 : ¬ (Q.u 0 =ᵐ[P] 0)) :
    ∀ᵐ ω ∂P, ¬ BddAbove (Set.range fun n => Q.U n ω) := by
  have hinj : Function.Injective (fun i : ℕ => i + 1) := fun a b h => by simpa using h
  have hid := identDistrib_Sg Q hinj
  set m : ℕ → Ω → ℝ := fun n ω => Mx (Sg Q id ω) n with hm
  set m' : ℕ → Ω → ℝ := fun n ω => Mx (Sg Q (· + 1) ω) n with hm'
  have hshift : ∀ ω, shift (Sg Q id ω) = Sg Q (· + 1) ω := fun ω => rfl
  have hd : ∀ ω, (Sg Q id ω).1 0 - (Sg Q id ω).2 0 = Q.u 0 ω := fun ω => rfl
  have hrec : ∀ n ω, m (n + 1) ω = max 0 (Q.u 0 ω + m' n ω) := by
    intro n ω; simp only [hm, hm']; rw [Mx_succ, hshift, hd]
  have hmi : ∀ n, Integrable (m n) P := integrable_Mx Q id
  have hm'i : ∀ n, Integrable (m' n) P := integrable_Mx Q (· + 1)
  have hu0i : Integrable (Q.u 0) P := Q.integrable_s.sub Q.integrable_t
  have hE1 : ∀ n, ∫ ω, m' n ω ∂P = ∫ ω, m n ω ∂P := fun n =>
    (hid.comp (measurable_Mx n)).integral_eq
  set D : ℕ → Ω → ℝ := fun n ω => max 0 (-(Q.u 0 ω + m' n ω)) with hD
  have hDeq : ∀ n ω, D n ω = m (n + 1) ω - Q.u 0 ω - m' n ω := by
    intro n ω; rw [hrec]; simp only [hD]
    rcases le_total 0 (Q.u 0 ω + m' n ω) with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have hDi : ∀ n, Integrable (D n) P := fun n => by
    have : D n = fun ω => m (n + 1) ω - Q.u 0 ω - m' n ω := funext (hDeq n)
    rw [this]; exact ((hmi (n + 1)).sub hu0i).sub (hm'i n)
  have hDint : ∀ n, ∫ ω, D n ω ∂P = ∫ ω, m (n + 1) ω ∂P - ∫ ω, m n ω ∂P := by
    intro n
    have e := integral_sub ((hmi (n + 1)).sub hu0i) (hm'i n)
    have e2 := integral_sub (hmi (n + 1)) hu0i
    simp only [Pi.sub_apply] at e e2
    rw [integral_congr_ae (Eventually.of_forall (hDeq n)), e, e2, h0, hE1]
    ring
  have hD0 : ∀ n ω, 0 ≤ D n ω := fun n ω => le_max_left _ _
  set L : Ω → ℝ := fun ω => ⨅ n, D n ω with hL
  have hLbdd : ∀ ω, BddBelow (Set.range fun n => D n ω) := fun ω =>
    ⟨0, by rintro _ ⟨n, rfl⟩; exact hD0 n ω⟩
  have hLle : ∀ n ω, L ω ≤ D n ω := fun n ω => ciInf_le (hLbdd ω) n
  have hL0 : ∀ ω, 0 ≤ L ω := fun ω => le_ciInf (fun n => hD0 n ω)
  have hLm : Measurable L := by
    apply Measurable.iInf
    intro n
    have hu : Measurable (Q.u 0) := measurable_u Q 0
    have hm'm : Measurable (m' n) := (measurable_Mx n).comp (measurable_Sg Q _)
    exact measurable_const.max ((hu.add hm'm).neg)
  have hLi : Integrable L P := (hDi 0).mono' hLm.aestronglyMeasurable
    (Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hL0 ω)]; exact hLle 0 ω))
  have hm0 : ∫ ω, m 0 ω ∂P = 0 := by simp [hm, Mx]
  have hsum : ∀ n : ℕ, (n : ℝ) * ∫ ω, L ω ∂P ≤ ∫ ω, m n ω ∂P := by
    intro n
    induction n with
    | zero => simp [hm0]
    | succ n ih =>
      have := integral_mono hLi (hDi n) (hLle n)
      rw [hDint] at this
      push_cast
      linarith
  have hLint : ∫ ω, L ω ∂P ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    obtain ⟨n, hn, hlt⟩ := small_mean Q h0 _ hpos
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have := hsum n
    rw [div_lt_iff₀ hnpos] at hlt
    linarith
  have hLae : L =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg hL0 hLi).mp (le_antisymm hLint (integral_nonneg hL0))
  have hH : ∀ᵐ ω ∂P, ∀ c : ℝ, (∀ n, Mx (shift (Sg Q id ω)) n ≤ c) →
      0 ≤ ((Sg Q id ω).1 0 - (Sg Q id ω).2 0) + c := by
    filter_upwards [hLae] with ω hω c hc
    rw [hshift] at hc
    rw [hd]
    have hle : max 0 (-(Q.u 0 ω + c)) ≤ L ω := le_ciInf (fun n => by
      simp only [hD]
      apply max_le_max le_rfl
      have := hc n
      simp only [hm']
      linarith)
    rw [hω] at hle
    simp only [Pi.zero_apply] at hle
    have := (le_max_right 0 (-(Q.u 0 ω + c))).trans hle
    linarith
  have hrecPsi : ∀ᵐ ω ∂P,
      Psi (Sg Q id ω) = Real.exp (-(Q.u 0 ω)) * Psi (Sg Q (· + 1) ω) := by
    filter_upwards [hH] with ω hω
    rw [Psi_rec _ hω, hd, hshift]
  -- Laplace argument
  by_contra hcon
  have hpos_set : P {ω | BddAbove (Set.range fun n => Q.U n ω)} ≠ 0 := by
    intro h
    apply hcon
    rw [ae_iff]
    simpa using h
  set c := ∫⁻ ω, ENNReal.ofReal (Psi (Sg Q id ω)) ∂P with hcdef
  have hPsim : Measurable (fun ω => ENNReal.ofReal (Psi (Sg Q id ω))) :=
    ENNReal.measurable_ofReal.comp (measurable_Psi.comp (measurable_Sg Q id))
  have hc0 : c ≠ 0 := by
    intro h
    rw [hcdef, lintegral_eq_zero_iff hPsim] at h
    apply hpos_set
    apply measure_mono_null _ (ae_iff.mp h)
    intro ω hω
    simp only [Set.mem_setOf_eq, Pi.zero_apply, ENNReal.ofReal_eq_zero, not_le]
    exact Psi_pos_of_bdd _ (bdd_Mx_of_bdd_Us _ hω)
  have hctop : c ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := ∫⁻ _, 1 ∂P) (by simp)
    apply lintegral_mono
    intro ω
    exact ENNReal.ofReal_le_one.mpr (Psi_le_one _)
  have hc' : ∫⁻ ω, ENNReal.ofReal (Psi (Sg Q (· + 1) ω)) ∂P = c :=
    (hid.comp (ENNReal.measurable_ofReal.comp measurable_Psi)).lintegral_eq
  have hφ : Measurable (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(q.1 - q.2)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_fst.sub measurable_snd).neg)
  have hψ : Measurable (fun p : Pt => ENNReal.ofReal (Psi p)) :=
    ENNReal.measurable_ofReal.comp measurable_Psi
  have hindep : IndepFun (fun ω => ENNReal.ofReal (Real.exp (-(Q.u 0 ω))))
      (fun ω => ENNReal.ofReal (Psi (Sg Q (· + 1) ω))) P :=
    (indep_head_tail Q).comp hφ hψ
  have hu0m : Measurable (Q.u 0) := measurable_u Q 0
  have hE : c = (∫⁻ ω, ENNReal.ofReal (Real.exp (-(Q.u 0 ω))) ∂P) * c := by
    conv_lhs => rw [hcdef]
    rw [lintegral_congr_ae (hrecPsi.mono (fun ω h => by
      rw [h, ENNReal.ofReal_mul (Real.exp_pos _).le]))]
    rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
      (f := fun ω => ENNReal.ofReal (Real.exp (-(Q.u 0 ω))))
      (g := fun ω => ENNReal.ofReal (Psi (Sg Q (· + 1) ω)))
      (Measurable.aemeasurable (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hu0m.neg)))
      (Measurable.aemeasurable (hψ.comp (measurable_Sg Q _))) hindep, hc']
  have hI : ∫⁻ ω, ENNReal.ofReal (Real.exp (-(Q.u 0 ω))) ∂P = 1 := by
    have : 1 * c = (∫⁻ ω, ENNReal.ofReal (Real.exp (-(Q.u 0 ω))) ∂P) * c := by
      rw [one_mul]; exact hE
    exact ((ENNReal.mul_left_inj hc0 hctop).mp this).symm
  have hexpnn : 0 ≤ᵐ[P] fun ω => Real.exp (-(Q.u 0 ω)) :=
    Eventually.of_forall (fun ω => (Real.exp_pos _).le)
  have hexpi : Integrable (fun ω => Real.exp (-(Q.u 0 ω))) P := by
    refine ⟨(Real.measurable_exp.comp hu0m.neg).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hexpnn, hI]
    exact ENNReal.one_lt_top
  have hexpint : ∫ ω, Real.exp (-(Q.u 0 ω)) ∂P = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae hexpnn hexpi.aestronglyMeasurable, hI]
    simp
  set G : Ω → ℝ := fun ω => Real.exp (-(Q.u 0 ω)) - 1 + Q.u 0 ω with hG
  have hG0 : 0 ≤ G := fun ω => by
    have := Real.add_one_le_exp (-(Q.u 0 ω))
    simp only [hG, Pi.zero_apply]
    linarith
  have hGi : Integrable G P := (hexpi.sub (integrable_const 1)).add hu0i
  have hGint : ∫ ω, G ω ∂P = 0 := by
    simp only [hG]
    have e := integral_add (hexpi.sub (integrable_const 1)) hu0i
    have e2 := integral_sub hexpi (integrable_const (1 : ℝ))
    simp only [Pi.sub_apply] at e e2
    rw [e, e2, hexpint, h0]
    simp
  have hGae := (integral_eq_zero_iff_of_nonneg hG0 hGi).mp hGint
  apply h1
  filter_upwards [hGae] with ω hω
  simp only [hG, Pi.zero_apply] at hω
  simp only [Pi.zero_apply]
  by_contra hne
  have := Real.add_one_lt_exp (x := -(Q.u 0 ω)) (by simpa using hne)
  linarith

lemma unbdd_of [IsProbabilityMeasure P] (Q : Input Ω P)
    (h0 : 0 ≤ ∫ ω, Q.u 0 ω ∂P) (h1 : ¬ (Q.u 0 =ᵐ[P] 0)) :
    ∀ᵐ ω ∂P, ¬ BddAbove (Set.range fun n => Q.U n ω) := by
  rcases h0.lt_or_eq with h | h
  · exact unbdd_pos Q h
  · exact unbdd_zero Q h.symm h1

lemma tendsto_A [IsProbabilityMeasure P] (Q : Input Ω P) (x : ℝ) :
    Tendsto (fun r => P.real (A Q r x)) atTop (𝓝 (P.real {ω | ∀ n, Q.U n ω ≤ x})) := by
  have hanti : Antitone (fun r => A Q r x) := by
    intro a b hab ω hω n hn; exact hω n (le_trans hn hab)
  have hinter : (⋂ r, A Q r x) = {ω | ∀ n, Q.U n ω ≤ x} := by
    ext ω; simp only [A, Set.mem_iInter, Set.mem_setOf_eq]
    exact ⟨fun h n => h n n le_rfl, fun h r n _ => h n⟩
  have h := tendsto_measure_iInter_atTop (μ := P) (fun r => (measurableSet_A Q r x).nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter] at h
  have := (ENNReal.tendsto_toReal (measure_ne_top P _)).comp h
  simpa [Function.comp_def, Measure.real] using this

lemma part2 [IsProbabilityMeasure P] (Q : Input Ω P)
    (h0 : 0 ≤ ∫ ω, Q.u 0 ω ∂P) (h1 : ¬ (Q.u 0 =ᵐ[P] 0)) (x : ℝ) :
    Tendsto (fun r => Q.F r x) atTop (𝓝 0) := by
  have hF : (fun r => Q.F r x) = fun r => P.real (A Q r x) := funext (F_eq Q · x)
  rw [hF]
  have hz : P.real {ω | ∀ n, Q.U n ω ≤ x} = 0 := by
    have hae := unbdd_of Q h0 h1
    rw [ae_iff] at hae
    rw [measureReal_eq_zero_iff]
    apply measure_mono_null _ hae
    intro ω hω
    simp only [Set.mem_setOf_eq, not_not]
    exact ⟨x, by rintro _ ⟨n, rfl⟩; exact hω n⟩
  rw [← hz]; exact tendsto_A Q x

lemma part1_mpr [IsProbabilityMeasure P] (Q : Input Ω P)
    (h : ∫ ω, Q.u 0 ω ∂P < 0 ∨ Q.u 0 =ᵐ[P] 0) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
        ∀ x : ℝ, ν {x} = 0 → Tendsto (fun r => Q.F r x) atTop (𝓝 (ν.real (Set.Iic x))) := by
  set M : Ω → ℝ := fun ω => ⨆ n, Q.U n ω with hMdef
  have hM : Measurable M := Measurable.iSup (fun n => measurable_U Q n)
  refine ⟨P.map M, Measure.isProbabilityMeasure_map hM.aemeasurable, fun x _ => ?_⟩
  have hF : (fun r => Q.F r x) = fun r => P.real (A Q r x) := funext (F_eq Q · x)
  rw [hF]
  have heq : (P.map M).real (Set.Iic x) = P.real {ω | ∀ n, Q.U n ω ≤ x} := by
    rw [map_measureReal_apply hM measurableSet_Iic]
    apply measureReal_congr
    filter_upwards [bdd_of Q h] with ω hω
    change (M ω ≤ x) = (∀ n, Q.U n ω ≤ x)
    simp only [hMdef]
    exact propext (ciSup_le_iff hω)
  rw [heq]; exact tendsto_A Q x

lemma part1_mp [IsProbabilityMeasure P] (Q : Input Ω P)
    (hν : ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
        ∀ x : ℝ, ν {x} = 0 → Tendsto (fun r => Q.F r x) atTop (𝓝 (ν.real (Set.Iic x)))) :
    ∫ ω, Q.u 0 ω ∂P < 0 ∨ Q.u 0 =ᵐ[P] 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h0, h1⟩ := hcon
  obtain ⟨ν, hνp, hlim⟩ := hν
  -- every non-atom `x` has `ν (Iic x) = 0`
  have hzero : ∀ x : ℝ, ν {x} = 0 → ν.real (Set.Iic x) = 0 := fun x hx =>
    tendsto_nhds_unique (hlim x hx) (part2 Q h0 h1 x)
  have hcount : Set.Countable {t : ℝ | 0 < ν {a : ℝ | a = t}} :=
    Measure.countable_meas_level_set_pos measurable_id
  -- pick non-atoms `x n ≥ n`
  have hex : ∀ n : ℕ, ∃ x : ℝ, (n : ℝ) ≤ x ∧ ν {x} = 0 := by
    intro n
    by_contra hne
    push_neg at hne
    have hsub : Set.Ici (n : ℝ) ⊆ {t : ℝ | 0 < ν {a : ℝ | a = t}} := by
      intro t ht
      simp only [Set.mem_setOf_eq, Set.setOf_eq_eq_singleton]
      exact pos_iff_ne_zero.mpr (hne t ht)
    have hc : (Set.Ici (n : ℝ)).Countable := hcount.mono hsub
    have := hc.measure_zero (volume : Measure ℝ)
    rw [Real.volume_Ici] at this
    exact ENNReal.top_ne_zero this
  have hIic : ∀ n : ℕ, ν (Set.Iic (n : ℝ)) = 0 := by
    intro n
    obtain ⟨x, hnx, hx⟩ := hex n
    have h1 : ν (Set.Iic x) = 0 := by
      have := hzero x hx
      rwa [measureReal_eq_zero_iff] at this
    exact measure_mono_null (Set.Iic_subset_Iic.mpr hnx) h1
  have huniv : (Set.univ : Set ℝ) = ⋃ n : ℕ, Set.Iic (n : ℝ) := by
    ext y; simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_Iic, true_iff]
    obtain ⟨n, hn⟩ := exists_nat_ge y; exact ⟨n, hn⟩
  have : ν Set.univ = 0 := by rw [huniv]; exact measure_iUnion_null hIic
  simp at this

end LindleyAux

open MeasureTheory ProbabilityTheory Filter Topology LindleyQueue.Stability in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Q : Input Ω P) :
    ((∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
        ∀ x : ℝ, ν {x} = 0 → Tendsto (fun r => Q.F r x) atTop (𝓝 (ν.real (Set.Iic x))))
      ↔ (∫ ω, Q.u 0 ω ∂P < 0 ∨ Q.u 0 =ᵐ[P] 0)) ∧
    (0 ≤ ∫ ω, Q.u 0 ω ∂P → ¬ (Q.u 0 =ᵐ[P] 0) →
      ∀ x : ℝ, Tendsto (fun r => Q.F r x) atTop (𝓝 0)) := by
  exact ⟨⟨LindleyAux.part1_mp Q, LindleyAux.part1_mpr Q⟩, fun h0 h1 x => LindleyAux.part2 Q h0 h1 x⟩
