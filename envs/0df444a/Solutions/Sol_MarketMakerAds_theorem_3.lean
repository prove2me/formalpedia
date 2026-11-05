-- Prove2me | solution 1 for MarketMakerAds.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-11-04T15:34:02.018459+00:00
-- url     : https://prove2.me/submissions/1c5d948b-f6a1-4c41-abb0-67b09f455882

import Definitions.Def_MarketMakerAds_Market

set_option autoImplicit false

open MeasureTheory

namespace MarketMakerAds

namespace MMA3

lemma sortDesc_pw (l : List ℝ) : (sortDesc l).Pairwise (fun a b => b ≤ a) :=
  List.pairwise_insertionSort _ _

lemma sortDesc_perm (l : List ℝ) : (sortDesc l).Perm l := List.perm_insertionSort _ _

lemma sortDesc_eq_of {s l : List ℝ} (hs : s.Pairwise (fun a b => b ≤ a)) (hp : s.Perm l) :
    sortDesc l = s :=
  List.Perm.eq_of_pairwise' (sortDesc_pw l) hs ((sortDesc_perm l).trans hp.symm)

/-- the order statistic on tuples -/
noncomputable def F (n I : ℕ) (x : Fin n → ℝ) : ℝ := (sortDesc (List.ofFn x)).getD I 0

lemma F_eq (n I : ℕ) (x : Fin n → ℝ) :
    F n I x = if h : I < n then x (Tuple.sort (fun i => -x i) ⟨I, h⟩) else 0 := by
  set σ := Tuple.sort (fun i => -x i)
  have hmono := Tuple.monotone_sort (fun i => -x i)
  have hanti : Antitone (x ∘ σ) := by
    intro a b hab
    have := hmono hab
    simp only [Function.comp_apply, neg_le_neg_iff] at this
    exact this
  have hpw : (List.ofFn (x ∘ σ)).Pairwise (fun a b => b ≤ a) :=
    (List.sortedGE_ofFn_iff.2 hanti).pairwise
  have hs : sortDesc (List.ofFn x) = List.ofFn (x ∘ σ) :=
    sortDesc_eq_of hpw (Equiv.Perm.ofFn_comp_perm σ x)
  unfold F
  rw [hs, List.getD_eq_getElem?_getD]
  split_ifs with h
  · simp [h]
  · simp [h]

lemma measSet_sort (n : ℕ) (τ : Equiv.Perm (Fin n)) :
    MeasurableSet {x : Fin n → ℝ | τ = Tuple.sort (fun i => -x i)} := by
  simp only [Tuple.eq_sort_iff]
  refine measurableSet_setOfPred.2 (Measurable.and ?_ ?_)
  · unfold Monotone
    refine Measurable.forall fun a => Measurable.forall fun b => Measurable.imp measurable_const ?_
    exact measurableSet_setOfPred.1
      (measurableSet_le (measurable_pi_apply _).neg (measurable_pi_apply _).neg)
  · refine Measurable.forall fun a => Measurable.forall fun b => Measurable.imp measurable_const ?_
    refine Measurable.imp ?_ measurable_const
    exact measurableSet_setOfPred.1
      (measurableSet_eq_fun (measurable_pi_apply _).neg (measurable_pi_apply _).neg)

lemma F_meas (n I : ℕ) : Measurable (F n I) := by
  classical
  by_cases h : I < n
  · have : F n I = fun x => ∑ τ : Equiv.Perm (Fin n),
        (if τ = Tuple.sort (fun i => -x i) then x (τ ⟨I, h⟩) else 0) := by
      funext x
      rw [F_eq]
      simp [h]
    rw [this]
    refine Finset.measurable_sum _ fun τ _ => ?_
    exact Measurable.ite (measSet_sort n τ) (measurable_pi_apply _) measurable_const
  · have : F n I = fun _ => 0 := by
      funext x; rw [F_eq]; simp [h]
    rw [this]; exact measurable_const

lemma c_meas {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) : Measurable M.c := by
  intro B hB
  have : M.c ⁻¹' B = ⋃ n : ℕ, {ω | M.N ω = n} ∩
      (fun ω => F n M.I (fun j : Fin n => M.V ω j)) ⁻¹' B := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro h; exact ⟨M.N ω, rfl, h⟩
    · rintro ⟨n, hn, h⟩
      subst hn; exact h
  rw [this]
  refine MeasurableSet.iUnion fun n => (M.measurable_N (measurableSet_singleton n)).inter ?_
  exact (F_meas n M.I).comp (measurable_pi_lambda _ fun j => M.measurable_V j) hB

lemma units_nonneg {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (ω : Ω) :
    ∀ v ∈ M.units ω, 0 ≤ v := by
  intro v hv
  simp only [Market.units, List.mem_ofFn] at hv
  obtain ⟨j, rfl⟩ := hv
  exact M.nonneg_V ω j

lemma c_nonneg {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (ω : Ω) : 0 ≤ M.c ω := by
  unfold Market.c
  rw [List.getD_eq_getElem?_getD]
  cases h : (sortDesc (M.units ω))[M.I]? with
  | none => simp
  | some x =>
    simp only [Option.getD_some]
    have hx : x ∈ sortDesc (M.units ω) := List.mem_of_getElem? h
    exact units_nonneg M ω x ((sortDesc_perm _).mem_iff.1 hx)

/-! list lemmas for part 2 -/

lemma split_filter (q : ℝ → Bool) (hq : ∀ v w, w ≤ v → q w = true → q v = true) :
    ∀ s : List ℝ, s.Pairwise (fun a b => b ≤ a) →
      s.filter q ++ s.filter (fun v => !q v) = s
  | [], _ => rfl
  | a :: t, hs => by
    rw [List.pairwise_cons] at hs
    by_cases hqa : q a = true
    · simp [hqa, split_filter q hq t hs.2]
    · have h1 : t.filter q = [] := List.filter_eq_nil_iff.2 fun b hb hqb =>
        hqa (hq a b (hs.1 b hb) hqb)
      have h2 : t.filter (fun v => !q v) = t := List.filter_eq_self.2 fun b hb => by
        have : ¬ q b = true := fun hqb => hqa (hq a b (hs.1 b hb) hqb)
        simpa using this
      simp only [List.filter_cons, hqa, h1, h2]
      simp

lemma part2_list (l : List ℝ) (I : ℕ) (T : ℝ) (q : ℝ → Bool) (hq : ∀ v, q v = true ↔ T ≤ v)
    (hc : (sortDesc l).getD I 0 < T) :
    (l.filter q).length ≤ I ∧
      (sortDesc (l.filter (fun v => !q v))).getD (I - (l.filter q).length) 0
        = (sortDesc l).getD I 0 ∧
      (l.filter q).sum + ((sortDesc (l.filter fun v => !q v)).take
        (I - (l.filter q).length)).sum = ((sortDesc l).take I).sum := by
  set s := sortDesc l with hsdef
  have hs : s.Pairwise (fun a b => b ≤ a) := sortDesc_pw l
  have hperm : s.Perm l := sortDesc_perm l
  have hup : ∀ v w, w ≤ v → q w = true → q v = true := fun v w hwv hw =>
    (hq v).2 (((hq w).1 hw).trans hwv)
  set A := s.filter q
  set B := s.filter (fun v => !q v)
  have hAB : A ++ B = s := split_filter q hup s hs
  have hA : (l.filter q).Perm A := (hperm.filter q).symm
  have hB : sortDesc (l.filter (fun v => !q v)) = B :=
    sortDesc_eq_of (hs.filter _) (hperm.filter _)
  have hlen : (l.filter q).length = A.length := hA.length_eq
  rw [hB, hlen]
  have hle : A.length ≤ I := by
    by_contra hlt
    push Not at hlt
    have h1 : s.getD I 0 = A[I] := by
      rw [← hAB, List.getD_append _ _ _ _ hlt, List.getD_eq_getElem _ _ hlt]
    have h2 : A[I] ∈ A := List.getElem_mem hlt
    have h3 : q A[I] = true := (List.mem_filter.1 h2).2
    have := (hq _).1 h3
    rw [← h1] at this
    linarith
  refine ⟨hle, ?_, ?_⟩
  · rw [← hAB, List.getD_append_right _ _ _ _ hle]
  · rw [hA.sum_eq, ← hAB, List.take_append, List.take_of_length_le hle, List.sum_append]
lemma take_succ_le (a : ℝ) (ha : 0 ≤ a) (s : List ℝ) (hs : ∀ v ∈ s, v ≤ a) (k : ℕ) :
    (s.take (k + 1)).sum ≤ a + (s.take k).sum := by
  rw [List.take_add, List.sum_append]
  cases h : s.drop k with
  | nil => simp; linarith
  | cons x t =>
    have hx : x ∈ s := List.mem_of_mem_drop (h ▸ List.mem_cons_self)
    simp only [List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil, add_zero]
    linarith [hs x hx]

-- uses sortDesc_perm from A
lemma sum_le_take {t s : List ℝ} (h : t.Sublist s) (hs : s.Pairwise (fun a b => b ≤ a))
    (hnn : ∀ v ∈ s, 0 ≤ v) : ∀ k, t.length ≤ k → t.sum ≤ (s.take k).sum := by
  induction h with
  | slnil => intro k _; simp
  | @cons l₁ l₂ a h' ih =>
    rw [List.pairwise_cons] at hs
    have ih' := ih hs.2 (fun v hv => hnn v (List.mem_cons_of_mem _ hv))
    intro k hk
    cases k with
    | zero =>
      have : l₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp [this]
    | succ k =>
      have h1 := ih' (k + 1) hk
      have h2 := take_succ_le a (hnn a List.mem_cons_self) l₂ hs.1 k
      simp only [List.take_succ_cons, List.sum_cons]
      linarith
  | @cons_cons l₁ l₂ a h' ih =>
    rw [List.pairwise_cons] at hs
    have ih' := ih hs.2 (fun v hv => hnn v (List.mem_cons_of_mem _ hv))
    intro k hk
    cases k with
    | zero => simp at hk
    | succ k =>
      simp only [List.length_cons] at hk
      simp only [List.take_succ_cons, List.sum_cons]
      linarith [ih' k (by omega)]

lemma opt_list (l s' : List ℝ) (hnn : ∀ v ∈ l, 0 ≤ v) (I : ℕ) (h : s'.Sublist l)
    (hlen : s'.length ≤ I) : s'.sum ≤ ((sortDesc l).take I).sum := by
  have hsp : s'.Subperm (sortDesc l) := h.subperm.trans (sortDesc_perm l).symm.subperm
  obtain ⟨t, htp, hts⟩ := hsp
  rw [← htp.sum_eq]
  exact sum_le_take hts (List.pairwise_insertionSort _ _)
    (fun v hv => hnn v ((sortDesc_perm l).mem_iff.1 hv)) I (htp.length_eq ▸ hlen)
section G
variable (g : Measure ℝ) [IsProbabilityMeasure g] (pmax : ℝ)
  (hsupp : ∀ᵐ p ∂g, 0 ≤ p ∧ p < pmax) (htop : ∀ v < pmax, 0 < g (Set.Ioi v))
include hsupp

lemma intC (f : ℝ → ℝ) (hf : Continuous f) : Integrable f g := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := 0) (b := pmax)).exists_bound_of_continuousOn
    hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (hsupp.mono fun p hp => hC p ⟨hp.1, hp.2.le⟩)

lemma strict_lt (f h : ℝ → ℝ) (hf : Continuous f) (hh : Continuous h) (hle : ∀ p, f p ≤ h p)
    (hpos : 0 < g {p | f p < h p}) : ∫ p, f p ∂g < ∫ p, h p ∂g := by
  have hi : Integrable (fun p => h p - f p) g := intC g pmax hsupp _ (hh.sub hf)
  have h0 : 0 < ∫ p, (h p - f p) ∂g := by
    rw [integral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall
      fun p => sub_nonneg.2 (hle p)) hi]
    refine lt_of_lt_of_le hpos (measure_mono fun p hp => ?_)
    simp only [Set.mem_ofPred_eq] at hp
    simp only [Function.mem_support]; linarith
  rw [integral_sub (intC g pmax hsupp _ hh) (intC g pmax hsupp _ hf)] at h0
  linarith

omit hsupp in
lemma int_const_eq (a : ℝ) : ∫ _p, a ∂g = a := by simp

lemma var_le (X : ℝ → ℝ) (hX : Continuous X) (a : ℝ) :
    ∫ p, (X p - ∫ q, X q ∂g) ^ 2 ∂g ≤ ∫ p, (X p - a) ^ 2 ∂g := by
  set E := ∫ q, X q ∂g
  have hd : ∫ p, (X p - a) ^ 2 ∂g - ∫ p, (X p - E) ^ 2 ∂g = (E - a) ^ 2 := by
    rw [← integral_sub (intC g pmax hsupp _ (by fun_prop)) (intC g pmax hsupp _ (by fun_prop))]
    have : (fun p => (X p - a) ^ 2 - (X p - E) ^ 2) =
        fun p => (E - a) * (2 * X p) - (E - a) * (a + E) := by funext p; ring
    rw [this, integral_sub (intC g pmax hsupp _ (by fun_prop)) (integrable_const _),
      integral_const_mul, integral_const_mul, int_const_eq]
    ring
  nlinarith [sq_nonneg (E - a)]

omit hsupp in
include htop in
lemma not_const (hsupp' : ∀ᵐ p ∂g, 0 ≤ p ∧ p < pmax) (k : ℝ) : ¬ ∀ᵐ p ∂g, p = k := by
  intro hk
  obtain ⟨p, hp1, hp2⟩ := (hk.and hsupp').exists
  have hk' : k < pmax := hp1 ▸ hp2.2
  have h0 : g {p | ¬ p = k} = 0 := ae_iff.1 hk
  have : g (Set.Ioi k) ≤ g {p | ¬ p = k} := measure_mono fun p hp => ne_of_gt hp
  have := htop k hk'
  simp_all

include htop

omit htop in
lemma UA_eq (m : RiskModel) (hm : m.IsAdmissible) (v : ℝ) (hv : pmax ≤ v) :
    UA m g v = Ubuy m v (pStar m g) := by
  have hae : ∀ᵐ p ∂g, max (v - p) 0 = v - p :=
    hsupp.mono fun p hp => max_eq_left (by linarith [hp.2])
  cases m with
  | meanVariance β =>
    simp only [UA, riskUtility, Ubuy, pStar]
    have h1 : ∫ p, max (v - p) 0 ∂g = v - ∫ p, p ∂g := by
      rw [integral_congr_ae hae, integral_sub (integrable_const _)
        (intC g pmax hsupp (fun p => p) continuous_id), int_const_eq]
    rw [h1]
    have h2 : ∫ p, (max (v - p) 0 - (v - ∫ q, q ∂g)) ^ 2 ∂g = ∫ p, (p - ∫ q, q ∂g) ^ 2 ∂g := by
      refine integral_congr_ae (hae.mono fun p hp => ?_)
      simp only [hp]; ring
    rw [h2]; ring
  | cara α =>
    simp only [RiskModel.IsAdmissible] at hm
    simp only [UA, riskUtility, Ubuy, pStar]
    set Z := ∫ p, Real.exp (α * p) ∂g
    have hZ : 0 < Z := integral_exp_pos (intC g pmax hsupp _ (by fun_prop))
    have h1 : ∫ p, (1 - Real.exp (-(α * max (v - p) 0))) ∂g =
        ∫ p, (1 - Real.exp (-(α * v)) * Real.exp (α * p)) ∂g := by
      refine integral_congr_ae (hae.mono fun p hp => ?_)
      simp only [hp]; rw [← Real.exp_add]; ring_nf
    rw [h1, integral_sub (integrable_const _) ((intC g pmax hsupp _ (by fun_prop)).const_mul _),
      integral_const_mul, int_const_eq]
    have : -(α * (v - 1 / α * Real.log Z)) = -(α * v) + Real.log Z := by
      field_simp; ring
    rw [this, Real.exp_add, Real.exp_log hZ]

lemma UA_gt (m : RiskModel) (hm : m.IsAdmissible) (v : ℝ) (hv : v < pmax) :
    Ubuy m v (pStar m g) < UA m g v := by
  have hIoi := htop v hv
  cases m with
  | meanVariance β =>
    simp only [RiskModel.IsAdmissible] at hm
    simp only [UA, riskUtility, Ubuy, pStar]
    have h1 : v - ∫ p, p ∂g < ∫ p, max (v - p) 0 ∂g := by
      have := strict_lt g pmax hsupp (fun p => v - p) (fun p => max (v - p) 0) (by fun_prop)
        (by fun_prop) (fun p => le_max_left _ _)
        (lt_of_lt_of_le hIoi (measure_mono fun p hp => by
          simp only [Set.mem_Ioi] at hp
          simp only [Set.mem_ofPred_eq]
          rw [max_eq_right (by linarith)]; linarith))
      rwa [integral_sub (integrable_const _) (intC g pmax hsupp (fun p => p) continuous_id),
        int_const_eq] at this
    have h2 := var_le g pmax hsupp (fun p => max (v - p) 0) (by fun_prop)
      (max (v - ∫ q, q ∂g) 0)
    have h3 : ∫ p, (max (v - p) 0 - max (v - ∫ q, q ∂g) 0) ^ 2 ∂g ≤
        ∫ p, (p - ∫ q, q ∂g) ^ 2 ∂g := by
      refine integral_mono (intC g pmax hsupp _ (by fun_prop))
        (intC g pmax hsupp _ (by fun_prop)) fun p => ?_
      have := abs_max_sub_max_le_abs (v - p) (v - ∫ q, q ∂g) 0
      have h' : |v - p - (v - ∫ q, q ∂g)| = |p - ∫ q, q ∂g| := by
        rw [abs_sub_comm]; congr 1; ring
      rw [h'] at this
      simp only
      rw [← sq_abs, ← sq_abs (p - _)]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    nlinarith [mul_le_mul_of_nonneg_left (h2.trans h3) hm]
  | cara α =>
    simp only [RiskModel.IsAdmissible] at hm
    simp only [UA, riskUtility, Ubuy, pStar]
    set Z := ∫ p, Real.exp (α * p) ∂g
    have hZ : 0 < Z := integral_exp_pos (intC g pmax hsupp _ (by fun_prop))
    have hlt : ∫ p, Real.exp (-(α * max (v - p) 0)) ∂g <
        ∫ p, Real.exp (-(α * v)) * Real.exp (α * p) ∂g := by
      refine strict_lt g pmax hsupp _ _ (by fun_prop) (by fun_prop) (fun p => ?_) ?_
      · rw [← Real.exp_add]; apply Real.exp_le_exp.2
        nlinarith [le_max_left (v - p) 0]
      · refine lt_of_lt_of_le hIoi (measure_mono fun p hp => ?_)
        simp only [Set.mem_Ioi] at hp
        simp only [Set.mem_ofPred_eq]
        rw [← Real.exp_add, max_eq_right (by linarith)]; apply Real.exp_lt_exp.2
        nlinarith
    rw [integral_sub (integrable_const _) (intC g pmax hsupp _ (by fun_prop)), int_const_eq,
      integral_const_mul] at *
    have : -(α * (v - 1 / α * Real.log Z)) = -(α * v) + Real.log Z := by
      field_simp; ring
    rw [this, Real.exp_add, Real.exp_log hZ]
    linarith

lemma mean_lt (m : RiskModel) (hpos : m.IsPositive) : ∫ p, p ∂g < pStar m g := by
  have hnc := not_const g pmax htop hsupp
  cases m with
  | meanVariance β =>
    simp only [RiskModel.IsPositive] at hpos
    simp only [pStar]
    have hint := intC g pmax hsupp (fun p => (p - ∫ q, q ∂g) ^ 2) (by fun_prop)
    have hnn : 0 ≤ ∫ p, (p - ∫ q, q ∂g) ^ 2 ∂g := integral_nonneg fun p => sq_nonneg _
    have hne : ∫ p, (p - ∫ q, q ∂g) ^ 2 ∂g ≠ 0 := by
      intro h0
      rw [integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall
        fun p => sq_nonneg _) hint] at h0
      exact hnc (∫ q, q ∂g) (h0.mono fun p hp => by
        simp only [Pi.zero_apply] at hp
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hp
        linarith)
    have := lt_of_le_of_ne hnn (Ne.symm hne)
    nlinarith [mul_pos hpos this]
  | cara α =>
    simp only [RiskModel.IsPositive] at hpos
    simp only [pStar]
    set μ := ∫ p, p ∂g
    set Z := ∫ p, Real.exp (α * p) ∂g
    have hZ : 0 < Z := integral_exp_pos (intC g pmax hsupp _ (by fun_prop))
    have hne : g {p | ¬ p = μ} ≠ 0 := fun h => hnc μ (ae_iff.2 h)
    have hlt : ∫ p, Real.exp (α * μ) * (α * (p - μ) + 1) ∂g < Z := by
      refine strict_lt g pmax hsupp _ _ (by fun_prop) (by fun_prop) (fun p => ?_) ?_
      · have := Real.add_one_le_exp (α * (p - μ))
        have h2 : Real.exp (α * p) = Real.exp (α * μ) * Real.exp (α * (p - μ)) := by
          rw [← Real.exp_add]; ring_nf
        rw [h2]; exact mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
      · refine lt_of_lt_of_le (pos_iff_ne_zero.2 hne) (measure_mono fun p hp => ?_)
        simp only [Set.mem_ofPred_eq] at hp ⊢
        have hx : α * (p - μ) ≠ 0 := mul_ne_zero hpos.ne' (sub_ne_zero.2 hp)
        have := Real.add_one_lt_exp hx
        have h2 : Real.exp (α * p) = Real.exp (α * μ) * Real.exp (α * (p - μ)) := by
          rw [← Real.exp_add]; ring_nf
        rw [h2]; exact mul_lt_mul_of_pos_left this (Real.exp_pos _)
    have hval : ∫ p, Real.exp (α * μ) * (α * (p - μ) + 1) ∂g = Real.exp (α * μ) := by
      rw [integral_const_mul]
      have : (fun p => α * (p - μ) + 1) = fun p => α * p - (α * μ - 1) := by funext p; ring
      rw [this, integral_sub ((intC g pmax hsupp (fun p => p) continuous_id).const_mul _)
        (integrable_const _), integral_const_mul, int_const_eq]
      ring
    rw [hval] at hlt
    have := (Real.lt_log_iff_exp_lt hZ).2 hlt
    calc μ = 1 / α * (α * μ) := by field_simp
      _ < 1 / α * Real.log Z := mul_lt_mul_of_pos_left this (by positivity)

end G

end MMA3

theorem theorem_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : Market Ω) (m : RiskModel) (hm : m.IsAdmissible) (pmax : ℝ)
    (h_le : ∀ᵐ ω ∂P, M.c ω ≤ pmax) (h_top : ∀ v < pmax, 0 < P {ω | v < M.c ω})
    (h_atom : P {ω | M.c ω = pmax} = 0) :
    -- 1. each buyer's utility remains the same
    ((∀ v : ℝ, buysMM m (M.priceLaw P) (M.mmPrice m P) v →
        Ubuy m v (M.mmPrice m P) = UA m (M.priceLaw P) v) ∧
      (∀ v : ℝ, buysMM m (M.priceLaw P) (M.mmPrice m P) v ↔ max pmax (M.mmPrice m P) ≤ v) ∧
      (∀ ω, M.util1 m P ω = M.util0 m P ω)) ∧
    -- 2. efficiency remains optimal
    (∀ᵐ ω ∂P, M.nMM m P ω ≤ M.I ∧ M.c1 m P ω = M.c ω ∧ M.eff1 m P ω = M.eff0 ω ∧
      ∀ s : List ℝ, s.Sublist (M.units ω) → s.length ≤ M.I → s.sum ≤ M.eff0 ω) ∧
    -- 3. revenue strictly increases
    (m.IsPositive → 0 < ∫ ω, (M.nMM m P ω : ℝ) ∂P →
      ∫ ω, (M.nMM m P ω : ℝ) * M.c ω ∂P ≤ (∫ ω, (M.nMM m P ω : ℝ) ∂P) * ∫ ω, M.c ω ∂P →
      ∫ ω, M.rev0 ω ∂P < ∫ ω, M.rev1 m P ω ∂P) ∧
    -- 4. welfare strictly increases
    (m.IsPositive → 0 < ∫ ω, (M.nMM m P ω : ℝ) ∂P →
      ∫ ω, (M.nMM m P ω : ℝ) * M.c ω ∂P ≤ (∫ ω, (M.nMM m P ω : ℝ) ∂P) * ∫ ω, M.c ω ∂P →
      Integrable (M.util0 m P) P →
      ∫ ω, M.welfare0 m P ω ∂P < ∫ ω, M.welfare1 m P ω ∂P) := by
  classical
  have hc := MMA3.c_meas M
  have hgdef : M.priceLaw P = P.map M.c := rfl
  have hgP : IsProbabilityMeasure (M.priceLaw P) := Measure.isProbabilityMeasure_map hc.aemeasurable
  have hlt : ∀ᵐ ω ∂P, M.c ω < pmax := by
    have h2 : ∀ᵐ ω ∂P, M.c ω ≠ pmax := ae_iff.2 (by simpa using h_atom)
    filter_upwards [h_le, h2] with ω h1 h2 using lt_of_le_of_ne h1 h2
  have hsupp : ∀ᵐ p ∂(M.priceLaw P), 0 ≤ p ∧ p < pmax := by
    have hms : MeasurableSet {p : ℝ | 0 ≤ p ∧ p < pmax} := measurableSet_Ico
    rw [hgdef, ae_map_iff hc.aemeasurable hms]
    exact hlt.mono fun ω h => ⟨MMA3.c_nonneg M ω, h⟩
  have htop' : ∀ v < pmax, 0 < (M.priceLaw P) (Set.Ioi v) := fun v hv => by
    rw [hgdef, Measure.map_apply hc measurableSet_Ioi]; exact h_top v hv
  have hpS' : M.mmPrice m P = pStar m (M.priceLaw P) := rfl
  have key1 : ∀ v, buysMM m (M.priceLaw P) (M.mmPrice m P) v ↔ max pmax (M.mmPrice m P) ≤ v := by
    intro v; constructor
    · intro hb
      refine max_le ?_ hb.1
      by_contra hv; push Not at hv
      have := MMA3.UA_gt (M.priceLaw P) pmax hsupp htop' m hm v hv
      rw [← hpS'] at this; linarith [hb.2]
    · intro hv
      refine ⟨le_of_max_le_right hv, ?_⟩
      rw [MMA3.UA_eq (M.priceLaw P) pmax hsupp m hm v (le_of_max_le_left hv), hpS']
  have key2 : ∀ v, buysMM m (M.priceLaw P) (M.mmPrice m P) v →
      Ubuy m v (M.mmPrice m P) = UA m (M.priceLaw P) v := fun v hb => by
    rw [MMA3.UA_eq (M.priceLaw P) pmax hsupp m hm v (le_of_max_le_left ((key1 v).1 hb)), hpS']
  have hutil : ∀ ω, M.util1 m P ω = M.util0 m P ω := by
    intro ω
    unfold Market.util1 Market.util0
    congr 1
    refine List.map_congr_left fun v _ => ?_
    split_ifs with hb
    · exact key2 v hb
    · rfl
  have hpart2 : ∀ᵐ ω ∂P, M.nMM m P ω ≤ M.I ∧ M.c1 m P ω = M.c ω ∧ M.eff1 m P ω = M.eff0 ω ∧
      ∀ s : List ℝ, s.Sublist (M.units ω) → s.length ≤ M.I → s.sum ≤ M.eff0 ω := by
    filter_upwards [hlt] with ω hω
    have hq : ∀ v, decide (buysMM m (M.priceLaw P) (M.mmPrice m P) v) = true ↔
        max pmax (M.mmPrice m P) ≤ v := fun v => by
      rw [decide_eq_true_iff]; exact key1 v
    obtain ⟨h1, h2, h3⟩ := MMA3.part2_list (M.units ω) M.I (max pmax (M.mmPrice m P)) _ hq
      (lt_of_lt_of_le hω (le_max_left _ _))
    exact ⟨h1, h2, h3, fun s hs hl => MMA3.opt_list _ s (MMA3.units_nonneg M ω) M.I hs hl⟩
  have hbd : ∀ᵐ ω ∂P, ‖M.c ω‖ ≤ pmax := h_le.mono fun ω h => by
    rw [Real.norm_eq_abs, abs_of_nonneg (MMA3.c_nonneg M ω)]; exact h
  have hcint : Integrable M.c P := Integrable.of_bound hc.aestronglyMeasurable pmax hbd
  have hEc : ∫ ω, M.c ω ∂P = ∫ p, p ∂(M.priceLaw P) := by
    rw [hgdef, integral_map hc.aemeasurable (f := fun p : ℝ => p) aestronglyMeasurable_id]
  have hr0int : Integrable (M.rev0) P := hcint.const_mul (M.I : ℝ)
  have hpart3 : m.IsPositive → 0 < ∫ ω, (M.nMM m P ω : ℝ) ∂P →
      ∫ ω, (M.nMM m P ω : ℝ) * M.c ω ∂P ≤ (∫ ω, (M.nMM m P ω : ℝ) ∂P) * ∫ ω, M.c ω ∂P →
      Integrable (M.rev1 m P) P ∧ ∫ ω, M.rev0 ω ∂P < ∫ ω, M.rev1 m P ω ∂P := by
    intro hpos hl hcov
    have hlint : Integrable (fun ω => (M.nMM m P ω : ℝ)) P :=
      Integrable.of_integral_ne_zero hl.ne'
    have hlc : Integrable (fun ω => (M.nMM m P ω : ℝ) * M.c ω) P :=
      hlint.mul_bdd hc.aestronglyMeasurable hbd
    have hae : M.rev1 m P =ᵐ[P] fun ω => (M.nMM m P ω : ℝ) * M.mmPrice m P +
        ((M.I : ℝ) * M.c ω - (M.nMM m P ω : ℝ) * M.c ω) := by
      filter_upwards [hpart2] with ω h
      unfold Market.rev1
      rw [h.2.1, Nat.cast_sub h.1]; ring
    have hi : Integrable (fun ω => (M.nMM m P ω : ℝ) * M.mmPrice m P +
        ((M.I : ℝ) * M.c ω - (M.nMM m P ω : ℝ) * M.c ω)) P :=
      (hlint.mul_const _).add ((hcint.const_mul _).sub hlc)
    refine ⟨hi.congr hae.symm, ?_⟩
    have hE1 : ∫ ω, M.rev1 m P ω ∂P = (∫ ω, (M.nMM m P ω : ℝ) ∂P) * M.mmPrice m P +
        ((M.I : ℝ) * ∫ ω, M.c ω ∂P - ∫ ω, (M.nMM m P ω : ℝ) * M.c ω ∂P) := by
      rw [integral_congr_ae hae]
      have a1 := integral_add (hlint.mul_const (M.mmPrice m P)) ((hcint.const_mul (M.I : ℝ)).sub hlc)
      have a2 := integral_sub (hcint.const_mul (M.I : ℝ)) hlc
      have a3 := integral_mul_const (μ := P) (M.mmPrice m P) (fun ω => (M.nMM m P ω : ℝ))
      have a4 := integral_const_mul (μ := P) (M.I : ℝ) M.c
      simp only [Pi.sub_apply] at a1
      rw [a1, a2, a3, a4]
    have hr0 : ∫ ω, M.rev0 ω ∂P = M.I * ∫ ω, M.c ω ∂P := integral_const_mul _ _
    rw [hr0, hE1]
    have hm := MMA3.mean_lt (M.priceLaw P) pmax hsupp htop' m hpos
    rw [← hEc, ← hpS'] at hm
    nlinarith [mul_lt_mul_of_pos_left hm hl]
  refine ⟨⟨fun v hb => key2 v hb, key1, hutil⟩, hpart2, fun a b c' => (hpart3 a b c').2, ?_⟩
  intro hpos hl hcov hu
  obtain ⟨hr1, hlt3⟩ := hpart3 hpos hl hcov
  have e0 : ∫ ω, M.welfare0 m P ω ∂P = ∫ ω, M.util0 m P ω ∂P + ∫ ω, M.rev0 ω ∂P :=
    integral_add hu hr0int
  have e1 : ∫ ω, M.welfare1 m P ω ∂P = ∫ ω, M.util0 m P ω ∂P + ∫ ω, M.rev1 m P ω ∂P := by
    have : M.welfare1 m P = fun ω => M.util0 m P ω + M.rev1 m P ω :=
      funext fun ω => by unfold Market.welfare1; rw [hutil]
    rw [this, integral_add hu hr1]
  linarith

end MarketMakerAds


-- Platform entry point: restates the target verbatim.
namespace MarketMakerAds

/-- **Theorem 3 (Market-Maker Pareto Improvement), p.18 (corrected: β > 0, Cov(ℓ, c) ≤ 0,
E[ℓ] > 0).**
Cohen, Désir, Korula, Sivan, *Best of Both Worlds Ad Contracts*, SSRN 3088600, Theorem 3, p.18
(proof pp.18–19): "When offering the Market-Maker contract at price p*_M, both the seller's revenue
and the welfare strictly increase. Moreover, the efficiency remains optimal and each buyer's
utility remains the same."

The seller sells `I` units; the market outcome `ω` is a random list of nonnegative unit values
(`Market`), `c` is the `(I+1)`-th highest unit value with law `g`, and every buyer evaluates the
auction with `g`. The contract is offered at `p = p*_M = pStar m g`. Assume `β ≥ 0`, resp. `α > 0`,
and that `p_max` is the top of the support of `c` (`c ≤ p_max` a.s., `P(c > v) > 0` for all
`v < p_max`) with no atom at `p_max`. Then:
1. **each buyer's utility remains the same**: a unit that buys the contract gets
   `U_buy(v, p) = U_A(v)`, the buyers are exactly those with `v ≥ max(p_max, p)`, and the sum of the
   buyers' utilities is unchanged in every outcome;
2. **efficiency remains optimal**, almost surely: at most `I` units buy the contract, the auction
   clearing price is unchanged, the allocated value is unchanged, and no `I` units have a larger
   total value;
3. **revenue strictly increases**, `E[R₀] < E[R₁]`, if `β > 0` (resp. `α > 0`), `E[ℓ] > 0` and
   `E[ℓ c] ≤ E[ℓ] E[c]`, where `ℓ` is the number of contract units;
4. **welfare strictly increases**, `E[W₀] < E[W₁]`, under the hypotheses of 3 and integrability of
   the buyers' utility sum.

**Formalization Note** Corrections: with `β = 0`, `p*_M = µ_A` and revenue does not strictly
increase; with `E[ℓ] = 0` nobody buys; with `ℓ` positively correlated with `c` revenue can fall
(the model allows correlated values and a random number of buyers). Independence of `ℓ` and `c` is
a special case of `E[ℓ c] ≤ E[ℓ] E[c]`. The paper's density for `c` is replaced by "no atom at
`p_max`". -/
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : Market Ω) (m : RiskModel) (hm : m.IsAdmissible) (pmax : ℝ)
    (h_le : ∀ᵐ ω ∂P, M.c ω ≤ pmax) (h_top : ∀ v < pmax, 0 < P {ω | v < M.c ω})
    (h_atom : P {ω | M.c ω = pmax} = 0) :
    -- 1. each buyer's utility remains the same
    ((∀ v : ℝ, buysMM m (M.priceLaw P) (M.mmPrice m P) v →
        Ubuy m v (M.mmPrice m P) = UA m (M.priceLaw P) v) ∧
      (∀ v : ℝ, buysMM m (M.priceLaw P) (M.mmPrice m P) v ↔ max pmax (M.mmPrice m P) ≤ v) ∧
      (∀ ω, M.util1 m P ω = M.util0 m P ω)) ∧
    -- 2. efficiency remains optimal
    (∀ᵐ ω ∂P, M.nMM m P ω ≤ M.I ∧ M.c1 m P ω = M.c ω ∧ M.eff1 m P ω = M.eff0 ω ∧
      ∀ s : List ℝ, s.Sublist (M.units ω) → s.length ≤ M.I → s.sum ≤ M.eff0 ω) ∧
    -- 3. revenue strictly increases
    (m.IsPositive → 0 < ∫ ω, (M.nMM m P ω : ℝ) ∂P →
      ∫ ω, (M.nMM m P ω : ℝ) * M.c ω ∂P ≤ (∫ ω, (M.nMM m P ω : ℝ) ∂P) * ∫ ω, M.c ω ∂P →
      ∫ ω, M.rev0 ω ∂P < ∫ ω, M.rev1 m P ω ∂P) ∧
    -- 4. welfare strictly increases
    (m.IsPositive → 0 < ∫ ω, (M.nMM m P ω : ℝ) ∂P →
      ∫ ω, (M.nMM m P ω : ℝ) * M.c ω ∂P ≤ (∫ ω, (M.nMM m P ω : ℝ) ∂P) * ∫ ω, M.c ω ∂P →
      Integrable (M.util0 m P) P →
      ∫ ω, M.welfare0 m P ω ∂P < ∫ ω, M.welfare1 m P ω ∂P) := by
  apply @MarketMakerAds.theorem_3 <;> assumption

end MarketMakerAds
