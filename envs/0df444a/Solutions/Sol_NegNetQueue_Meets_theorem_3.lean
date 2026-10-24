-- Prove2me | solution 1 for NegNetQueue.Meets.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T00:02:55.496128+00:00
-- url     : https://prove2.me/submissions/278564f9-2412-409c-8198-55122f700abd

import Mathlib
import Definitions.Def_NegNetQueue_Meets_EventSeq
import Definitions.Def_NegNetQueue_Meets_Model

set_option autoImplicit false



namespace T3E

def A (p h m : ℕ) : ℤ := ((p+m).choose p : ℤ) - ((p+m).choose (h+p+1) : ℤ)
def B (p h d : ℕ) : ℤ := ((p+d).choose (h+p) : ℤ) - ((p+d).choose (h+p+1) : ℤ)
def cnt (p h u v : ℕ) : ℤ := if v = 0 then A p h u else if v ≤ u then B p h (u - v) else 0

def c : ℕ → ℕ → ℕ → ℕ → ℤ
  | 0, _, u, v => if u = 0 ∧ v = 0 then 1 else 0
  | p+1, 0, u, v => c p 1 u v
  | p+1, h+1, u, v => cnt p h u v

lemma pas (N k : ℕ) : ((N+1).choose (k+1) : ℤ) = (N.choose k : ℤ) + (N.choose (k+1) : ℤ) := by
  rw [Nat.choose_succ_succ']; push_cast; ring

lemma R0 (p h v : ℕ) : c (p+1) (h+1) 0 v = c p (h+2) 0 v := by
  rcases p with _ | p
  · rcases v with _ | v <;> simp [c, cnt, A, B, Nat.choose_eq_zero_of_lt]
  · rcases v with _ | v <;> simp [c, cnt, A, B, Nat.choose_eq_zero_of_lt]

lemma R1 (p u v : ℕ) (hu : u ≤ p) :
    c (p+1) 1 (u+1) v = c p 2 (u+1) v + (if v = 0 then 0 else c p 1 u (v-1)) := by
  rcases p with _ | p
  · have hu0 : u = 0 := by omega
    subst hu0
    rcases v with _ | _ | v <;> simp [c, cnt, A, B]
  · rcases v with _ | v
    · simp only [c, cnt, A, if_true]
      have e1 := pas (p+u+1) p
      have e2 := pas (p+u+1) (p+1)
      simp only [if_true, add_zero]
      ring_nf at e1 e2 ⊢; linarith
    · rcases v with _ | w
      · simp [c, cnt, A, B]
        have e1 := pas (p+u) p
        have e2 := pas (p+u) (p+1)
        ring_nf at e1 e2 ⊢; linarith
      · by_cases hw : w + 2 ≤ u + 1
        · obtain ⟨d, rfl⟩ : ∃ d, u = w + 1 + d := ⟨u - (w+1), by omega⟩
          simp only [c, cnt, B]
          have h2 : w + 1 + 1 ≤ w + 1 + d + 1 := by omega
          have h4 : w + 1 ≤ w + 1 + d := by omega
          simp only [h2, h4, if_true, Nat.add_sub_cancel, add_eq_zero, one_ne_zero, and_false,
            if_false]
          rw [show w + 1 + d + 1 - (w + 1 + 1) = d by omega, show w + 1 + d - (w + 1) = d by omega]
          have e1 := pas (p+d) p
          have e2 := pas (p+d) (p+1)
          ring_nf at e1 e2 ⊢; linarith
        · simp only [c, cnt]
          have h2 : ¬ (w + 1 + 1 ≤ u + 1) := by omega
          have h4 : ¬ (w + 1 ≤ u) := by omega
          simp [h2, h4]

lemma z0 {N k : ℕ} (h : N < k) : ((N.choose k : ℕ) : ℤ) = 0 := by
  rw [Nat.choose_eq_zero_of_lt h]; simp

lemma R2 (p h u v : ℕ) (hu : u + 1 ≤ h + p + 2) :
    c (p+1) (h+2) (u+1) v = c p (h+3) (u+1) v + c (p+1) (h+1) u v := by
  rcases p with _ | p
  · rcases v with _ | w
    · simp [c, cnt, A]
      have e1 := pas u (h+1)
      have z := z0 (N := u) (k := h+2) (by omega)
      ring_nf at e1 z ⊢; linarith
    · by_cases hw : w ≤ u
      · obtain ⟨d, rfl⟩ : ∃ d, u = w + d := ⟨u - w, by omega⟩
        rcases d with _ | e
        · simp [c, cnt, B]
        · have h1 : w + 1 ≤ w + (e+1) + 1 := by omega
          have h2 : w + 1 ≤ w + (e+1) := by omega
          simp only [c, cnt, B, h1, h2, if_true, add_eq_zero, one_ne_zero, and_false, if_false]
          rw [show w + (e+1) + 1 - (w + 1) = e + 1 by omega, show w + (e+1) - (w + 1) = e by omega]
          have e1 := pas e h
          have e2 := pas e (h+1)
          have z1 := z0 (N := e) (k := h+1) (by omega)
          have z2 := z0 (N := e) (k := h+2) (by omega)
          simp
          ring_nf at e1 e2 z1 z2 ⊢; linarith
      · have h1 : ¬ (w + 1 ≤ u + 1) := by omega
        have h2 : ¬ (w + 1 ≤ u) := by omega
        simp [c, cnt, h1, h2]
  · rcases v with _ | w
    · simp [c, cnt, A]
      have e1 := pas (p+u+1) p
      have e2 := pas (p+u+1) (h+p+2)
      ring_nf at e1 e2 ⊢; linarith
    · by_cases hw : w ≤ u
      · obtain ⟨d, rfl⟩ : ∃ d, u = w + d := ⟨u - w, by omega⟩
        rcases d with _ | e
        · have h1 : w + 1 ≤ w + 0 + 1 := by omega
          have h2 : ¬ (w + 1 ≤ w + 0) := by omega
          simp only [c, cnt, B, h1, h2, if_true, add_eq_zero, one_ne_zero, and_false, if_false]
          rw [show w + 0 + 1 - (w + 1) = 0 by omega]
          have z1 := z0 (N := p+1+0) (k := h+1+(p+1)) (by omega)
          have z2 := z0 (N := p+1+0) (k := h+1+(p+1)+1) (by omega)
          have z3 := z0 (N := p+0) (k := h+2+p) (by omega)
          have z4 := z0 (N := p+0) (k := h+2+p+1) (by omega)
          rw [z1, z2, z3, z4]; simp
        · have h1 : w + 1 ≤ w + (e+1) + 1 := by omega
          have h2 : w + 1 ≤ w + (e+1) := by omega
          simp only [c, cnt, B, h1, h2, if_true, add_eq_zero, one_ne_zero, and_false, if_false]
          rw [show w + (e+1) + 1 - (w + 1) = e + 1 by omega, show w + (e+1) - (w + 1) = e by omega]
          have e1 := pas (p+e+1) (h+p+1)
          have e2 := pas (p+e+1) (h+p+2)
          ring_nf at e1 e2 ⊢; linarith
      · have h1 : ¬ (w + 1 ≤ u + 1) := by omega
        have h2 : ¬ (w + 1 ≤ u) := by omega
        simp [c, cnt, h1, h2]

end T3E

namespace NegNetQueue.Meets.T3

open MeasureTheory ProbabilityTheory Finset Filter Topology

lemma run_succ_left (n : ℕ) (s : TagState) (e : ℕ → Bool) (N : ℕ) :
    run n s e (N+1) = run n (step n s (e 0)) (fun t => e (t+1)) N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    show step n (run n s e (N+1)) (e (N+1)) =
      step n (run n (step n s (e 0)) (fun t => e (t+1)) N) (e (N+1))
    rw [ih]

lemma run_congr (n : ℕ) (s : TagState) (e e' : ℕ → Bool) (N : ℕ) (h : ∀ i < N, e i = e' i) :
    run n s e N = run n s e' N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    show step n (run n s e N) (e N) = step n (run n s e' N) (e' N)
    rw [ih (fun i hi => h i (by omega)), h N (by omega)]

def ext {N : ℕ} (b : Fin N → Bool) : ℕ → Bool := fun i => if h : i < N then b ⟨i, h⟩ else false

noncomputable def g (n : ℕ) (q : ℝ) (Q : TagState → Prop) [DecidablePred Q] : ℕ → TagState → ℝ
  | 0, s => if Q s then 1 else 0
  | N+1, s => q * g n q Q N (step n s true) + (1 - q) * g n q Q N (step n s false)

def wt (q : ℝ) (b : Bool) : ℝ := if b then q else 1 - q

lemma run_cons (n : ℕ) (s : TagState) (N : ℕ) (a : Bool) (f : Fin N → Bool) :
    run n s (ext (Fin.cons a f : Fin (N+1) → Bool)) (N+1) = run n (step n s a) (ext f) N := by
  rw [run_succ_left]
  have h0 : ext (Fin.cons a f : Fin (N+1) → Bool) 0 = a := by simp [ext]
  rw [h0]
  apply run_congr
  intro i hi
  simp only [ext, dif_pos hi, dif_pos (show i + 1 < N + 1 by omega)]
  exact Fin.cons_succ (α := fun _ => Bool) a f ⟨i, hi⟩

lemma sum_eq_g (n : ℕ) (q : ℝ) (Q : TagState → Prop) [DecidablePred Q] (N : ℕ) (s : TagState) :
    ∑ b : Fin N → Bool, (if Q (run n s (ext b) N) then ∏ i, wt q (b i) else 0) = g n q Q N s := by
  induction N generalizing s with
  | zero => simp [g, run]
  | succ N ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (N+1) => Bool)).sum_comp]
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    have key : ∀ (a : Bool), (∑ f : Fin N → Bool,
        (if Q (run n s (ext ((Fin.consEquiv (fun _ : Fin (N+1) => Bool)) (a, f))) (N+1)) then
          ∏ i, wt q ((Fin.consEquiv (fun _ : Fin (N+1) => Bool)) (a, f) i) else 0))
        = wt q a * g n q Q N (step n s a) := by
      intro a
      rw [← ih, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun f _ => ?_)
      have e1 : (Fin.consEquiv (fun _ : Fin (N+1) => Bool)) (a, f) = Fin.cons a f := rfl
      rw [e1, run_cons, Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      split_ifs <;> simp
    rw [key true, key false]
    simp [g, wt]

lemma wt_nonneg (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (b : Bool) : 0 ≤ wt q b := by
  cases b <;> simp [wt] <;> linarith

section prob
variable {Ω : Type*} [MeasurableSpace Ω]

lemma prob_atom (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → Bool)
    (hm : ∀ t, Measurable (ε t)) (q : ℝ) (hq0 : 0 ≤ q)
    (hlaw : ∀ t, P {ω | ε t ω = true} = ENNReal.ofReal q) (i : ℕ) (b : Bool) :
    P (ε i ⁻¹' {b}) = ENNReal.ofReal (wt q b) := by
  cases b
  · have : ε i ⁻¹' {false} = {ω | ε i ω = true}ᶜ := by ext ω; simp
    rw [this, prob_compl_eq_one_sub (by exact hm i (measurableSet_singleton true)), hlaw, wt]
    simp only [Bool.false_eq_true, if_false]
    rw [ENNReal.ofReal_sub 1 hq0, ENNReal.ofReal_one]
  · show P {ω | ε i ω = true} = _
    rw [hlaw i]; simp [wt]

lemma prob_cyl (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → Bool)
    (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε P) (q : ℝ) (hq0 : 0 ≤ q)
    (hlaw : ∀ t, P {ω | ε t ω = true} = ENNReal.ofReal q) {N : ℕ} (b : Fin N → Bool) :
    P {ω | ∀ i : Fin N, ε i ω = b i} = ∏ i : Fin N, ENNReal.ofReal (wt q (b i)) := by
  have hset : {ω | ∀ i : Fin N, ε i ω = b i} = ⋂ i ∈ Finset.range N, ε i ⁻¹' {ext b i} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff,
      Finset.mem_range]
    constructor
    · intro h i hi; simp [ext, hi, h ⟨i, hi⟩]
    · intro h i; have := h i i.2; simpa [ext, i.2] using this
  rw [hset, hind.measure_inter_preimage_eq_mul (Finset.range N)
    (fun i _ => measurableSet_singleton _)]
  rw [← Fin.prod_univ_eq_prod_range (fun i => P (ε i ⁻¹' {ext b i}))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [prob_atom P ε hm q hq0 hlaw]
  simp [ext, i.2]

lemma prob_eq_g (n : ℕ) (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → Bool)
    (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε P) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hlaw : ∀ t, P {ω | ε t ω = true} = ENNReal.ofReal q)
    (Q : TagState → Prop) [DecidablePred Q] (N : ℕ) (s : TagState) :
    MeasurableSet {ω | Q (run n s (fun t => ε t ω) N)} ∧
    (P {ω | Q (run n s (fun t => ε t ω) N)}).toReal = g n q Q N s := by
  have hS : {ω | Q (run n s (fun t => ε t ω) N)} =
      ⋃ b ∈ (Finset.univ.filter (fun b : Fin N → Bool => Q (run n s (ext b) N))),
        {ω | ∀ i : Fin N, ε i ω = b i} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      exists_prop]
    constructor
    · intro h
      refine ⟨fun i => ε i ω, ?_, fun i => rfl⟩
      rwa [run_congr n s (ext fun i : Fin N => ε i ω) (fun t => ε t ω) N
        (fun i hi => by simp [ext, hi])]
    · rintro ⟨b, hb, hω⟩
      rwa [run_congr n s (fun t => ε t ω) (ext b) N (fun i hi => by simp [ext, hi, hω ⟨i, hi⟩])]
  have hmeas : ∀ b : Fin N → Bool, MeasurableSet {ω | ∀ i : Fin N, ε i ω = b i} := by
    intro b
    have : {ω | ∀ i : Fin N, ε i ω = b i} = ⋂ i : Fin N, ε i ⁻¹' {b i} := by ext ω; simp
    rw [this]; exact MeasurableSet.iInter (fun i => hm i (measurableSet_singleton _))
  refine ⟨?_, ?_⟩
  · rw [hS]; exact Finset.measurableSet_biUnion _ (fun b _ => hmeas b)
  · rw [hS, measure_biUnion_finset]
    · rw [ENNReal.toReal_sum (fun b _ => measure_ne_top _ _), ← sum_eq_g, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      split_ifs
      · rw [prob_cyl P ε hm hind q hq0 hlaw, ENNReal.toReal_prod]
        exact Finset.prod_congr rfl (fun i _ => ENNReal.toReal_ofReal (wt_nonneg q hq0 hq1 _))
      · rfl
    · intro b _ b' _ hbb'
      rw [Function.onFun, Set.disjoint_left]
      intro ω h1 h2; apply hbb'; funext i; exact (h1 i).symm.trans (h2 i)
    · intro b _; exact hmeas b

end prob

lemma g_frozen (n : ℕ) (q : ℝ) (Q : TagState → Prop) [DecidablePred Q] (s : TagState)
    (hp : s.pos = 0) (N : ℕ) : g n q Q N s = if Q s then 1 else 0 := by
  have hs : ∀ b, step n s b = s := by intro b; simp [step, hp]
  induction N with
  | zero => rfl
  | succ N ih => simp only [g, hs, ih]; ring

lemma lim_rec (n : ℕ) (q : ℝ) (Q : TagState → Prop) [DecidablePred Q] (L : TagState → ℝ)
    (hL : ∀ s, Tendsto (fun N => g n q Q N s) atTop (𝓝 (L s))) (s : TagState) :
    L s = q * L (step n s true) + (1 - q) * L (step n s false) := by
  have h1 := (hL s).comp (tendsto_add_atTop_nat 1)
  have h2 := ((hL (step n s true)).const_mul q).add ((hL (step n s false)).const_mul (1 - q))
  exact tendsto_nhds_unique h1 (h2.congr (fun N => by simp [g]))

def Inv (n : ℕ) (s : TagState) : Prop :=
  s.len = s.pos + s.met ∧ s.fill ≤ s.met ∧ s.len ≤ n ∧ (s.pos = 0 → s.len < n)

lemma inv_step (n : ℕ) (s : TagState) (b : Bool) (h : Inv n s) : Inv n (step n s b) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold step Inv
  split_ifs <;> (try dsimp only) <;> (try split_ifs) <;> omega

lemma wf_eq (n : ℕ) (q : ℝ) (hq : 0 < q) (G V : TagState → ℝ) (Q : TagState → Prop)
    [DecidablePred Q]
    (hG0 : ∀ s, s.pos = 0 → G s = if Q s then 1 else 0)
    (hGrec : ∀ s, G s = q * G (step n s true) + (1-q) * G (step n s false))
    (hV0 : ∀ s, Inv n s → s.pos = 0 → V s = if Q s then 1 else 0)
    (hV1 : ∀ s, Inv n s → s.pos ≠ 0 → s.len < n →
      V s = q * V (step n s true) + (1-q) * V (step n s false))
    (hV2 : ∀ s, Inv n s → s.pos ≠ 0 → ¬ s.len < n → V s = V (step n s true)) :
    ∀ s, Inv n s → G s = V s := by
  intro s
  induction' hm : s.pos * (n+1) + (n - s.len) using Nat.strong_induction_on with m ih generalizing s
  intro hs
  by_cases hp : s.pos = 0
  · rw [hG0 s hp, hV0 s hs hp]
  · have hst : (step n s true).pos * (n+1) + (n - (step n s true).len) < m := by
      obtain ⟨h1, h2, h3, h4⟩ := hs
      simp only [step, hp, if_false, if_true]
      rw [← hm]
      have : (s.pos - 1) * (n+1) + (n+1) = s.pos * (n+1) := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.pos_of_ne_zero hp)]
      omega
    by_cases hl : s.len < n
    · have hsf : (step n s false).pos * (n+1) + (n - (step n s false).len) < m := by
        simp only [step, hp, hl, if_false, if_true, Bool.false_eq_true]
        omega
      rw [hGrec s, hV1 s hs hp hl, ih _ hst _ rfl (inv_step n s true hs),
        ih _ hsf _ rfl (inv_step n s false hs)]
    · have hsf : step n s false = s := by simp [step, hp, hl]
      have h := hGrec s
      rw [hsf] at h
      have : G s = G (step n s true) := by
        have : q * G s = q * G (step n s true) := by linarith
        exact mul_left_cancel₀ hq.ne' this
      rw [this, hV2 s hs hp hl, ih _ hst _ rfl (inv_step n s true hs)]

lemma met_le_step (n : ℕ) (s : TagState) (b : Bool) :
    s.met ≤ (step n s b).met ∧ s.fill ≤ (step n s b).fill := by
  unfold step
  split_ifs <;> (try dsimp only) <;> omega

lemma pos_step (n : ℕ) (s : TagState) (b : Bool) (h : s.pos = 0) : step n s b = s := by
  simp [step, h]

lemma frozen (n : ℕ) (s : TagState) (e : ℕ → Bool) (N : ℕ) (h : (run n s e N).pos = 0) (M : ℕ) :
    run n s e (N + M) = run n s e N := by
  induction M with
  | zero => rfl
  | succ M ih =>
    show step n (run n s e (N + M)) (e (N + M)) = _
    rw [ih, pos_step n _ _ h]

lemma iSup_eventually (f : ℕ → ℕ) (hf : Monotone f) (N : ℕ) (hN : ∀ M, f (N + M) = f N) :
    (⨆ t, (f t : ℕ∞)) = f N := by
  refine le_antisymm (iSup_le fun t => ?_) (le_iSup (fun t => (f t : ℕ∞)) N)
  rcases le_total t N with h | h
  · exact_mod_cast hf h
  · obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [hN M]

lemma sup_at (n : ℕ) (s : TagState) (e : ℕ → Bool) (N : ℕ) (h : (run n s e N).pos = 0) :
    (⨆ t, ((run n s e t).met : ℕ∞)) = (run n s e N).met ∧
    (⨆ t, ((run n s e t).fill : ℕ∞)) = (run n s e N).fill := by
  constructor
  · exact iSup_eventually (fun t => (run n s e t).met)
      (monotone_nat_of_le_succ fun t => (met_le_step n _ (e t)).1) N
      (fun M => by rw [frozen n s e N h M])
  · exact iSup_eventually (fun t => (run n s e t).fill)
      (monotone_nat_of_le_succ fun t => (met_le_step n _ (e t)).2) N
      (fun M => by rw [frozen n s e N h M])

section limits
variable {Ω : Type*} [MeasurableSpace Ω]

lemma tendsto_g (n : ℕ) (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → Bool)
    (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε P) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hlaw : ∀ t, P {ω | ε t ω = true} = ENNReal.ofReal q)
    (Q : TagState → Prop) [DecidablePred Q] (hQ : ∀ s b, Q s → Q (step n s b)) (s : TagState) :
    Tendsto (fun N => g n q Q N s) atTop
      (𝓝 (P (⋃ N, {ω | Q (run n s (fun t => ε t ω) N)})).toReal) := by
  have hmono : Monotone (fun N => {ω | Q (run n s (fun t => ε t ω) N)}) := by
    apply monotone_nat_of_le_succ; intro N ω h; exact hQ _ _ h
  have h1 := tendsto_measure_iUnion_atTop (μ := P) hmono
  have h2 := (ENNReal.tendsto_toReal (measure_ne_top P _)).comp h1
  refine h2.congr (fun N => ?_)
  simp only [Function.comp]
  exact (prob_eq_g n P ε hm hind q hq0 hq1 hlaw Q N s).2

lemma prob_union_eq (n : ℕ) (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → Bool)
    (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε P) (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hlaw : ∀ t, P {ω | ε t ω = true} = ENNReal.ofReal q)
    (Q : TagState → Prop) [DecidablePred Q] (hQ : ∀ s b, Q s → Q (step n s b))
    (V : TagState → ℝ)
    (hV0 : ∀ s, Inv n s → s.pos = 0 → V s = if Q s then 1 else 0)
    (hV1 : ∀ s, Inv n s → s.pos ≠ 0 → s.len < n →
      V s = q * V (step n s true) + (1-q) * V (step n s false))
    (hV2 : ∀ s, Inv n s → s.pos ≠ 0 → ¬ s.len < n → V s = V (step n s true))
    (s : TagState) (hs : Inv n s) :
    (P (⋃ N, {ω | Q (run n s (fun t => ε t ω) N)})).toReal = V s := by
  have hT := tendsto_g n P ε hm hind q hq0.le hq1 hlaw Q hQ
  refine wf_eq n q hq0 (fun s => (P (⋃ N, {ω | Q (run n s (fun t => ε t ω) N)})).toReal) V Q
    ?_ ?_ hV0 hV1 hV2 s hs
  · intro s hp
    refine tendsto_nhds_unique (hT s) ?_
    simp only [g_frozen n q Q s hp]
    exact tendsto_const_nhds
  · exact lim_rec n q Q _ hT

noncomputable def XS (n : ℕ) (s : TagState) (ε : ℕ → Ω → Bool) (ω : Ω) : ℕ∞ :=
  ⨆ t, ((run n s (fun t => ε t ω) t).met : ℕ∞)
noncomputable def YS (n : ℕ) (s : TagState) (ε : ℕ → Ω → Bool) (ω : Ω) : ℕ∞ :=
  ⨆ t, ((run n s (fun t => ε t ω) t).fill : ℕ∞)

lemma absorbed (n : ℕ) (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → Bool)
    (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε P) (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hlaw : ∀ t, P {ω | ε t ω = true} = ENNReal.ofReal q) (s : TagState) (hs : Inv n s) :
    P (⋃ N, {ω | (run n s (fun t => ε t ω) N).pos = 0})ᶜ = 0 := by
  have h := prob_union_eq n P ε hm hind q hq0 hq1 hlaw (fun st => st.pos = 0)
    (fun s b h => by rw [pos_step n s b h]; exact h) (fun _ => 1)
    (fun s _ hp => by simp [hp]) (fun s _ _ _ => by ring) (fun _ _ _ _ => rfl) s hs
  have hmeas : MeasurableSet (⋃ N, {ω | (run n s (fun t => ε t ω) N).pos = 0}) :=
    MeasurableSet.iUnion fun N =>
      (prob_eq_g n P ε hm hind q hq0.le hq1 hlaw (fun st => st.pos = 0) N s).1
  rw [prob_compl_eq_zero_iff hmeas]
  have h1 : P (⋃ N, {ω | (run n s (fun t => ε t ω) N).pos = 0}) ≠ ⊤ := measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal h1, h, ENNReal.ofReal_one]

lemma prob_event (n : ℕ) (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → Bool)
    (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε P) (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hlaw : ∀ t, P {ω | ε t ω = true} = ENNReal.ofReal q)
    (R : ℕ∞ → ℕ∞ → Prop) [∀ a b, Decidable (R a b)] (V : TagState → ℝ)
    (hV0 : ∀ s, Inv n s → s.pos = 0 → V s = if R s.met s.fill then 1 else 0)
    (hV1 : ∀ s, Inv n s → s.pos ≠ 0 → s.len < n →
      V s = q * V (step n s true) + (1-q) * V (step n s false))
    (hV2 : ∀ s, Inv n s → s.pos ≠ 0 → ¬ s.len < n → V s = V (step n s true))
    (s : TagState) (hs : Inv n s) :
    (P {ω | R (XS n s ε ω) (YS n s ε ω)}).toReal = V s := by
  have hQ : ∀ st b, (st.pos = 0 ∧ R st.met st.fill) →
      ((step n st b).pos = 0 ∧ R (step n st b).met (step n st b).fill) := by
    intro st b h; rw [pos_step n st b h.1]; exact h
  have key := prob_union_eq n P ε hm hind q hq0 hq1 hlaw
    (fun st => st.pos = 0 ∧ R st.met st.fill) hQ V
    (fun s hs hp => by rw [hV0 s hs hp]; simp [hp]) hV1 hV2 s hs
  rw [← key, ← measure_inter_conull (absorbed n P ε hm hind q hq0 hq1 hlaw s hs)]
  congr 2
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨hR, N, hN⟩
    obtain ⟨h1, h2⟩ := sup_at n s (fun t => ε t ω) N hN
    refine ⟨N, hN, ?_⟩
    unfold XS YS at hR
    rw [h1, h2] at hR; exact hR
  · rintro ⟨N, hN, hR⟩
    obtain ⟨h1, h2⟩ := sup_at n s (fun t => ε t ω) N hN
    refine ⟨?_, N, hN⟩
    unfold XS YS
    rw [h1, h2]; exact hR

end limits

end NegNetQueue.Meets.T3

namespace NegNetQueue.Meets.T3

noncomputable def Wt (q : ℝ) (p h u v : ℕ) : ℝ :=
  (1-q)^u * q^(if h = 0 then p - 1 else p) / q^v * (T3E.c p h u v : ℝ)

noncomputable def Vt (n x y : ℕ) (q : ℝ) (s : TagState) : ℝ :=
  if s.met ≤ x ∧ s.fill ≤ y then Wt q s.pos (n - s.len) (x - s.met) (y - s.fill) else 0

lemma Vt0 (n x y : ℕ) (q : ℝ) (s : TagState) (hp : s.pos = 0) :
    Vt n x y q s = if s.met = x ∧ s.fill = y then 1 else 0 := by
  obtain ⟨P, L, m, f⟩ := s
  simp only at hp; subst hp
  unfold Vt Wt
  dsimp only
  by_cases h1 : m = x ∧ f = y
  · obtain ⟨rfl, rfl⟩ := h1
    simp [T3E.c]
  · rw [if_neg h1]
    by_cases h2 : m ≤ x ∧ f ≤ y
    · rw [if_pos h2]
      have : ¬ (x - m = 0 ∧ y - f = 0) := by omega
      simp [T3E.c, this]
    · rw [if_neg h2]

lemma Wa (q : ℝ) (hq : q ≠ 0) (p h v : ℕ) :
    Wt q (p+1) (h+1) 0 v = q * Wt q p (h+2) 0 v := by
  simp only [Wt]
  rw [T3E.R0]
  simp
  field_simp
  ring

lemma Wb (q : ℝ) (hq : q ≠ 0) (p u : ℕ) (hu : u ≤ p) :
    Wt q (p+1) 1 (u+1) 0 = q * Wt q p 2 (u+1) 0 := by
  simp only [Wt]
  rw [T3E.R1 p u 0 hu]
  simp
  field_simp
  ring

lemma Wc (q : ℝ) (hq : q ≠ 0) (p u v : ℕ) (hu : u ≤ p) :
    Wt q (p+1) 1 (u+1) (v+1) = q * Wt q p 2 (u+1) (v+1) + (1-q) * Wt q (p+1) 0 u v := by
  simp only [Wt]
  rw [T3E.R1 p u (v+1) hu, show T3E.c (p+1) 0 u v = T3E.c p 1 u v by simp only [T3E.c]]
  simp
  field_simp
  ring

lemma Wd (q : ℝ) (hq : q ≠ 0) (p h u v : ℕ) (hu : u + 1 ≤ h + p + 2) :
    Wt q (p+1) (h+2) (u+1) v = q * Wt q p (h+3) (u+1) v + (1-q) * Wt q (p+1) (h+1) u v := by
  simp only [Wt]
  rw [T3E.R2 p h u v hu]
  simp
  field_simp
  ring

lemma Vt_of (n x y : ℕ) (q : ℝ) (P L m f u v h : ℕ) (hx : x = m + u) (hy : y = f + v)
    (hh : n - L = h) : Vt n x y q ⟨P, L, m, f⟩ = Wt q P h u v := by
  unfold Vt
  dsimp only
  rw [if_pos (by omega)]
  subst hx hy hh
  rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]

lemma Vt_zero (n x y : ℕ) (q : ℝ) (P L m f : ℕ) (h : ¬ (m ≤ x ∧ f ≤ y)) :
    Vt n x y q ⟨P, L, m, f⟩ = 0 := by
  unfold Vt
  dsimp only
  rw [if_neg h]

lemma V1 (n x y : ℕ) (hx : x < n) (q : ℝ) (hq : 0 < q) (p L m f : ℕ) (hL : L = p + 1 + m)
    (hLn : L < n) :
    Vt n x y q ⟨p+1, L, m, f⟩ = q * Vt n x y q ⟨p, L - 1, m, f⟩ +
      (1-q) * Vt n x y q ⟨p+1, L+1, m+1, f + if L + 1 = n then 1 else 0⟩ := by
  have hq' : q ≠ 0 := hq.ne'
  obtain ⟨h', rfl⟩ : ∃ h', n = L + 1 + h' := ⟨n - L - 1, by omega⟩
  by_cases hA : m ≤ x ∧ f ≤ y
  · obtain ⟨u, rfl⟩ : ∃ u, x = m + u := ⟨x - m, by omega⟩
    obtain ⟨v, rfl⟩ : ∃ v, y = f + v := ⟨y - f, by omega⟩
    rw [Vt_of _ _ _ q _ _ _ _ u v (h'+1) rfl rfl (by omega),
      Vt_of _ _ _ q _ _ _ _ u v (h'+2) rfl rfl (by omega)]
    rcases u with _ | u
    · rw [Vt_zero _ _ _ q _ _ _ _ (by omega), Wa q hq' p h' v]
      ring
    · rcases h' with _ | h''
      · rw [if_pos (by omega)]
        rcases v with _ | v
        · rw [Vt_zero _ _ _ q _ _ _ _ (by omega), Wb q hq' p u (by omega)]
          ring
        · rw [Vt_of _ _ _ q _ _ _ _ u v 0 (by omega) (by omega) (by omega),
            Wc q hq' p u v (by omega)]
      · rw [if_neg (by omega), Vt_of _ _ _ q _ _ _ _ u v (h''+1) (by omega) (by omega) (by omega),
          Wd q hq' p h'' u v (by omega)]
  · rw [Vt_zero _ _ _ q _ _ _ _ hA, Vt_zero _ _ _ q _ _ _ _ hA,
      Vt_zero _ _ _ q _ _ _ _ (by split_ifs <;> omega)]
    ring

lemma V2 (n x y : ℕ) (q : ℝ) (p m f : ℕ) (hL : n = p + 1 + m) :
    Vt n x y q ⟨p+1, n, m, f⟩ = Vt n x y q ⟨p, n - 1, m, f⟩ := by
  unfold Vt
  dsimp only
  split_ifs with hA
  · rw [show n - n = 0 by omega, show n - (n - 1) = 1 by omega]
    simp [Wt, T3E.c]
  · rfl

end NegNetQueue.Meets.T3

namespace NegNetQueue.Meets.T3

open MeasureTheory ProbabilityTheory Finset Filter Topology

lemma Vt_hV0 (n x y : ℕ) (q : ℝ) : ∀ s, Inv n s → s.pos = 0 →
    Vt n x y q s = if (s.met : ℕ∞) = (x : ℕ∞) ∧ (s.fill : ℕ∞) = (y : ℕ∞) then 1 else 0 := by
  intro s _ hp
  rw [Vt0 n x y q s hp]
  simp only [Nat.cast_inj]

lemma Vt_hV1 (n x y : ℕ) (hx : x < n) (q : ℝ) (hq : 0 < q) : ∀ s, Inv n s → s.pos ≠ 0 →
    s.len < n → Vt n x y q s = q * Vt n x y q (step n s true) + (1-q) * Vt n x y q (step n s false) := by
  rintro ⟨P, L, m, f⟩ ⟨h1, h2, h3, h4⟩ hp hl
  simp only at h1 h2 h3 h4 hp hl
  obtain ⟨p, rfl⟩ : ∃ p, P = p + 1 := ⟨P - 1, by omega⟩
  have e1 : step n ⟨p+1, L, m, f⟩ true = ⟨p, L - 1, m, f⟩ := by simp [step]
  have e2 : step n ⟨p+1, L, m, f⟩ false =
      ⟨p+1, L+1, m+1, f + if L + 1 = n then 1 else 0⟩ := by simp [step, hl]
  rw [e1, e2]
  exact V1 n x y hx q hq p L m f (by omega) hl

lemma Vt_hV2 (n x y : ℕ) (q : ℝ) : ∀ s, Inv n s → s.pos ≠ 0 →
    ¬ s.len < n → Vt n x y q s = Vt n x y q (step n s true) := by
  rintro ⟨P, L, m, f⟩ ⟨h1, h2, h3, h4⟩ hp hl
  simp only at h1 h2 h3 h4 hp hl
  obtain ⟨p, rfl⟩ : ∃ p, P = p + 1 := ⟨P - 1, by omega⟩
  obtain rfl : L = n := by omega
  have e1 : step L ⟨p+1, L, m, f⟩ true = ⟨p, L - 1, m, f⟩ := by simp [step]
  rw [e1]
  exact V2 L x y q p m f (by omega)

lemma rq (lam mu : ℝ) (c : ℕ) (hlam : 0 < lam) (hmu : 0 < mu) (hc : 1 ≤ c) :
    qComp lam mu c = 1 / (1 + rho lam mu c) ∧ 0 < rho lam mu c := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hcm : 0 < (c : ℝ) * mu := mul_pos hc' hmu
  refine ⟨?_, div_pos hlam hcm⟩
  unfold qComp rho
  field_simp
  ring

lemma eval3 (r : ℝ) (hr : 0 < r) (n j x y : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n - 1) (hx : x < n) :
    Vt n x y (1 / (1 + r)) ⟨j, j, 0, 0⟩ =
      if y = 0 ∧ x < n then
          ((Nat.choose (j + x - 1) (j - 1) : ℝ) - (Nat.choose (j + x - 1) (n - 1) : ℝ)) *
            r ^ x / (1 + r) ^ (j + x)
        else if 0 < y ∧ y ≤ x ∧ x < n then
          ((Nat.choose (j + (x - y) - 1) (n - 2) : ℝ) - (Nat.choose (j + (x - y) - 1) (n - 1) : ℝ)) *
            r ^ x / (1 + r) ^ (j + (x - y))
        else 0 := by
  obtain ⟨p, rfl⟩ : ∃ p, j = p + 1 := ⟨j - 1, by omega⟩
  obtain ⟨h, rfl⟩ : ∃ h, n = p + 1 + h + 1 := ⟨n - p - 2, by omega⟩
  have hr1 : (1 + r) ≠ 0 := by positivity
  have hq1 : 1 - 1 / (1 + r) = r / (1 + r) := by field_simp; ring
  rw [Vt_of _ _ _ _ _ _ _ _ x y (h+1) (by omega) (by omega) (by omega)]
  simp only [Wt, Nat.add_one_ne_zero, if_false, hq1,
    show T3E.c (p+1) (h+1) x y = T3E.cnt p h x y by simp only [T3E.c]]
  rcases y with _ | v
  · simp only [T3E.cnt, T3E.A, if_true, true_and, if_pos hx]
    rw [show p + 1 + x - 1 = p + x by omega, show p + 1 - 1 = p by omega,
      show p + 1 + h + 1 - 1 = h + p + 1 by omega]
    push_cast
    simp only [div_pow, one_div, inv_pow, pow_add, pow_zero]
    field_simp
  · by_cases hv : v + 1 ≤ x
    · obtain ⟨d, rfl⟩ : ∃ d, x = v + 1 + d := ⟨x - v - 1, by omega⟩
      have hv0 : v + 1 ≠ 0 := by omega
      simp only [T3E.cnt, T3E.B, hv0, if_false, hv, if_true, false_and]
      rw [if_pos ⟨by omega, by simp, hx⟩]
      rw [show v + 1 + d - (v + 1) = d by omega, show p + 1 + d - 1 = p + d by omega,
        show p + 1 + h + 1 - 2 = h + p by omega,
        show p + 1 + h + 1 - 1 = h + p + 1 by omega]
      push_cast
      simp only [div_pow, one_div, inv_pow, pow_add, pow_zero]
      field_simp
    · have hv0 : v + 1 ≠ 0 := by omega
      simp only [T3E.cnt, hv0, if_false, hv, false_and, and_false]
      simp
end NegNetQueue.Meets.T3

namespace NegNetQueue.Meets.T3

open MeasureTheory ProbabilityTheory Finset Filter Topology

noncomputable def F3 (r : ℝ) (n j x y : ℕ) : ℝ :=
  if y = 0 ∧ x < n then
      ((Nat.choose (j + x - 1) (j - 1) : ℝ) - (Nat.choose (j + x - 1) (n - 1) : ℝ)) *
        r ^ x / (1 + r) ^ (j + x)
    else if 0 < y ∧ y ≤ x ∧ x < n then
      ((Nat.choose (j + (x - y) - 1) (n - 2) : ℝ) - (Nat.choose (j + (x - y) - 1) (n - 1) : ℝ)) *
        r ^ x / (1 + r) ^ (j + (x - y))
    else 0

lemma eval3F (r : ℝ) (hr : 0 < r) (n j x y : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n - 1) (hx : x < n) :
    Vt n x y (1 / (1 + r)) ⟨j, j, 0, 0⟩ = F3 r n j x y :=
  eval3 r hr n j x y hj1 hjn hx

lemma sum_ite_lt (g : ℕ → ℝ) (x m : ℕ) (hxm : x ≤ m) :
    ∑ y ∈ range m, (if y < x then g y else 0) = ∑ y ∈ range x, g y := by
  induction m, hxm using Nat.le_induction with
  | base => exact Finset.sum_congr rfl (fun y hy => if_pos (Finset.mem_range.1 hy))
  | succ m hm ih => rw [Finset.sum_range_succ, ih, if_neg (by omega), add_zero]

lemma F3_row (r : ℝ) (n j x : ℕ) (hx : x < n) :
    ∑ y ∈ range n, F3 r n j x y =
      ((Nat.choose (j + x - 1) (j - 1) : ℝ) - (Nat.choose (j + x - 1) (n - 1) : ℝ)) *
        r ^ x / (1 + r) ^ (j + x) +
      ∑ d ∈ range x, ((Nat.choose (j + d - 1) (n - 2) : ℝ) - (Nat.choose (j + d - 1) (n - 1) : ℝ)) *
        r ^ x / (1 + r) ^ (j + d) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  · unfold F3
    rw [if_pos ⟨rfl, hx⟩]
  · have h1 : ∀ y, F3 r (m+1) j x (y+1) = if y < x then
        ((Nat.choose (j + (x - 1 - y) - 1) (m + 1 - 2) : ℝ) -
          (Nat.choose (j + (x - 1 - y) - 1) (m + 1 - 1) : ℝ)) *
          r ^ x / (1 + r) ^ (j + (x - 1 - y)) else 0 := by
      intro y
      unfold F3
      have c1 : ¬ (y + 1 = 0 ∧ x < m + 1) := by omega
      by_cases hy : y < x
      · have c2 : (0 < y + 1 ∧ y + 1 ≤ x ∧ x < m + 1) := ⟨by omega, by omega, hx⟩
        rw [if_neg c1, if_pos c2, if_pos hy, show x - (y + 1) = x - 1 - y by omega]
      · have c2 : ¬ (0 < y + 1 ∧ y + 1 ≤ x ∧ x < m + 1) := by omega
        rw [if_neg c1, if_neg c2, if_neg hy]
    simp only [h1]
    rw [sum_ite_lt _ x m (by omega)]
    exact Finset.sum_range_reflect (fun d => ((Nat.choose (j + d - 1) (m + 1 - 2) : ℝ) -
      (Nat.choose (j + d - 1) (m + 1 - 1) : ℝ)) * r ^ x / (1 + r) ^ (j + d)) x

lemma alg4 (r : ℝ) (hr : 0 < r) (n j : ℕ) (ψ : ℕ → ℝ) :
    ∑ x ∈ range n, (∑ y ∈ range n, F3 r n j x y) * ψ x =
      (1 / (1 + r)) ^ j *
          (∑ x ∈ Finset.range n,
              ((Nat.choose (j + x - 1) (j - 1) : ℝ) - (Nat.choose (j + x - 1) (n - 1) : ℝ)) *
                (r / (1 + r)) ^ x * ψ x +
            ∑ d ∈ Finset.range (n - 1),
              ((Nat.choose (j + d - 1) (n - 2) : ℝ) - (Nat.choose (j + d - 1) (n - 1) : ℝ)) *
                (1 / (1 + r)) ^ d *
                ∑ x ∈ Finset.Ico (d + 1) n, r ^ x * ψ x) := by
  have hr1 : (1 + r) ≠ 0 := by positivity
  have hrow : ∀ x ∈ range n, (∑ y ∈ range n, F3 r n j x y) * ψ x =
      (((Nat.choose (j + x - 1) (j - 1) : ℝ) - (Nat.choose (j + x - 1) (n - 1) : ℝ)) *
        r ^ x / (1 + r) ^ (j + x) +
      ∑ d ∈ range x, ((Nat.choose (j + d - 1) (n - 2) : ℝ) - (Nat.choose (j + d - 1) (n - 1) : ℝ)) *
        r ^ x / (1 + r) ^ (j + d)) * ψ x :=
    fun x hx => by rw [F3_row r n j x (Finset.mem_range.1 hx)]
  rw [Finset.sum_congr rfl hrow]
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm' (t' := range (n - 1)) (s' := fun d => Ico (d + 1) n)
    (fun x d => by
      simp only [Finset.mem_range, Finset.mem_Ico]
      constructor <;> intro h <;> omega)]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun x _ => ?_)
    simp only [one_div, inv_pow, div_pow, pow_add]
    field_simp
    try ring
  · refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp only [one_div, inv_pow, div_pow, pow_add]
    field_simp
    try ring

section final
variable {Ω : Type*} [MeasurableSpace Ω]

lemma event_eq_union (n : ℕ) (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → Bool)
    (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε P) (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hlaw : ∀ t, P {ω | ε t ω = true} = ENNReal.ofReal q)
    (R : ℕ∞ → ℕ∞ → Prop) (s : TagState) (hs : Inv n s) :
    P {ω | R (XS n s ε ω) (YS n s ε ω)} =
      P (⋃ N, {ω | (run n s (fun t => ε t ω) N).pos = 0 ∧
        R (run n s (fun t => ε t ω) N).met (run n s (fun t => ε t ω) N).fill}) := by
  rw [← measure_inter_conull (absorbed n P ε hm hind q hq0 hq1 hlaw s hs)]
  congr 1
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨hR, N, hN⟩
    obtain ⟨h1, h2⟩ := sup_at n s (fun t => ε t ω) N hN
    refine ⟨N, hN, ?_⟩
    unfold XS YS at hR
    rw [h1, h2] at hR; exact hR
  · rintro ⟨N, hN, hR⟩
    obtain ⟨h1, h2⟩ := sup_at n s (fun t => ε t ω) N hN
    refine ⟨?_, N, hN⟩
    unfold XS YS
    rw [h1, h2]; exact hR

lemma part2 (n : ℕ) (hn : 2 ≤ n) (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → Bool)
    (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε P) (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hlaw : ∀ t, P {ω | ε t ω = true} = ENNReal.ofReal q) (x : ℕ∞) :
    P {ω | Xmet n n ε ω = x} = P {ω | Xmet n (n - 1) ε ω = x} := by
  classical
  have hs0 : Inv n ⟨n, n, 0, 0⟩ := by
    unfold Inv; dsimp only; exact ⟨by omega, le_refl _, le_refl _, fun h => by omega⟩
  have hs1 : Inv n ⟨n - 1, n - 1, 0, 0⟩ := by
    unfold Inv; dsimp only; exact ⟨by omega, le_refl _, by omega, fun _ => by omega⟩
  have e0 : {ω | Xmet n n ε ω = x} = {ω | (fun a (_ : ℕ∞) => a = x)
      (XS n ⟨n, n, 0, 0⟩ ε ω) (YS n ⟨n, n, 0, 0⟩ ε ω)} := rfl
  have e1 : {ω | Xmet n (n - 1) ε ω = x} = {ω | (fun a (_ : ℕ∞) => a = x)
      (XS n ⟨n - 1, n - 1, 0, 0⟩ ε ω) (YS n ⟨n - 1, n - 1, 0, 0⟩ ε ω)} := rfl
  rw [e0, e1, event_eq_union n P ε hm hind q hq0 hq1 hlaw (fun a (_ : ℕ∞) => a = x) _ hs0,
    event_eq_union n P ε hm hind q hq0 hq1 hlaw (fun a (_ : ℕ∞) => a = x) _ hs1]
  let Q : TagState → Prop := fun st => st.pos = 0 ∧ (st.met : ℕ∞) = x
  have hQ : ∀ st b, Q st → Q (step n st b) := fun st b h => by rw [pos_step n st b h.1]; exact h
  have hT := tendsto_g n P ε hm hind q hq0.le hq1 hlaw Q hQ
  have hrec := lim_rec n q Q _ hT ⟨n, n, 0, 0⟩
  have e_t : step n ⟨n, n, 0, 0⟩ true = ⟨n - 1, n - 1, 0, 0⟩ := by
    simp [step, show n ≠ 0 by omega]
  have e_f : step n ⟨n, n, 0, 0⟩ false = ⟨n, n, 0, 0⟩ := by simp [step]
  rw [e_t, e_f] at hrec
  beta_reduce at hrec
  have heq : (P (⋃ N, {ω | Q (run n ⟨n, n, 0, 0⟩ (fun t => ε t ω) N)})).toReal =
      (P (⋃ N, {ω | Q (run n ⟨n - 1, n - 1, 0, 0⟩ (fun t => ε t ω) N)})).toReal := by
    have h2 : q * (P (⋃ N, {ω | Q (run n ⟨n, n, 0, 0⟩ (fun t => ε t ω) N)})).toReal =
        q * (P (⋃ N, {ω | Q (run n ⟨n - 1, n - 1, 0, 0⟩ (fun t => ε t ω) N)})).toReal := by
      linarith
    exact mul_left_cancel₀ hq0.ne' h2
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 heq

lemma part3 (n : ℕ) (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → Bool)
    (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε P) (r : ℝ) (hr : 0 < r)
    (hlaw : ∀ t, P {ω | ε t ω = true} = ENNReal.ofReal (1 / (1 + r)))
    (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n - 1) (x y : ℕ) :
    (P {ω | Xmet n j ε ω = (x : ℕ∞) ∧ Yfill n j ε ω = (y : ℕ∞)}).toReal = F3 r n j x y := by
  have hq0 : (0 : ℝ) < 1 / (1 + r) := by positivity
  have hq1 : 1 / (1 + r) ≤ (1 : ℝ) := by rw [div_le_one (by positivity)]; linarith
  have hs : Inv n ⟨j, j, 0, 0⟩ := by
    unfold Inv; dsimp only; exact ⟨by omega, le_refl _, by omega, fun _ => by omega⟩
  have e0 : {ω | Xmet n j ε ω = (x : ℕ∞) ∧ Yfill n j ε ω = (y : ℕ∞)} =
      {ω | (fun a b : ℕ∞ => a = x ∧ b = y) (XS n ⟨j, j, 0, 0⟩ ε ω) (YS n ⟨j, j, 0, 0⟩ ε ω)} := rfl
  rw [e0]
  by_cases hx : x < n
  · rw [prob_event n P ε hm hind _ hq0 hq1 hlaw (fun a b : ℕ∞ => a = x ∧ b = y)
      (Vt n x y (1 / (1 + r))) (Vt_hV0 n x y _) (Vt_hV1 n x y hx _ hq0) (Vt_hV2 n x y _) _ hs]
    exact eval3F r hr n j x y hj1 hjn hx
  · rw [prob_event n P ε hm hind _ hq0 hq1 hlaw (fun a b : ℕ∞ => a = x ∧ b = y)
      (fun _ => 0) ?_ (fun _ _ _ _ => by ring) (fun _ _ _ _ => rfl) _ hs]
    · simp [F3, hx]
    · intro s hs' hp
      obtain ⟨h1, h2, h3, h4⟩ := hs'
      have hlt : s.met < x := by have := h4 hp; omega
      rw [if_neg]
      rintro ⟨hx', _⟩
      have := Nat.cast_inj.1 hx'
      omega

lemma inv_run (n : ℕ) (s : TagState) (hs : Inv n s) (e : ℕ → Bool) (N : ℕ) :
    Inv n (run n s e N) := by
  induction N with
  | zero => exact hs
  | succ N ih => exact inv_step n _ _ ih

lemma met_lt (n : ℕ) (st : TagState) (hs : Inv n st) : st.met < n := by
  obtain ⟨h1, h2, h3, h4⟩ := hs
  by_cases hp : st.pos = 0
  · have := h4 hp; omega
  · omega

lemma probX (n : ℕ) (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → Bool)
    (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε P) (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hlaw : ∀ t, P {ω | ε t ω = true} = ENNReal.ofReal q) (x : ℕ) (hx : x < n)
    (s : TagState) (hs : Inv n s) :
    (P (⋃ N, {ω | (run n s (fun t => ε t ω) N).pos = 0 ∧
        (run n s (fun t => ε t ω) N).met = x})).toReal = ∑ y ∈ range n, Vt n x y q s := by
  classical
  refine prob_union_eq n P ε hm hind q hq0 hq1 hlaw (fun st => st.pos = 0 ∧ st.met = x)
    (fun st b h => by rw [pos_step n st b h.1]; exact h)
    (fun st => ∑ y ∈ range n, Vt n x y q st) ?_ ?_ ?_ s hs
  · intro st hst hp
    have hf : st.fill < n := lt_of_le_of_lt hst.2.1 (met_lt n st hst)
    simp only [Vt0 n x _ q st hp, hp, true_and]
    by_cases hmx : st.met = x
    · simp [hmx, hf]
    · simp [hmx]
  · intro st hst hp hl
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun y _ => Vt_hV1 n x y hx q hq0 st hst hp hl)
  · intro st hst hp hl
    exact Finset.sum_congr rfl (fun y _ => Vt_hV2 n x y q st hst hp hl)

lemma integral_formula (n : ℕ) (P : Measure Ω) [IsProbabilityMeasure P] (ε : ℕ → Ω → Bool)
    (hm : ∀ t, Measurable (ε t)) (hind : iIndepFun ε P) (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hlaw : ∀ t, P {ω | ε t ω = true} = ENNReal.ofReal q) (j : ℕ) (hs : Inv n ⟨j, j, 0, 0⟩)
    (ψ : ℕ → ℝ) :
    ∫ ω, ψ (Xmet n j ε ω).toNat ∂P =
      ∑ x ∈ range n, (∑ y ∈ range n, Vt n x y q ⟨j, j, 0, 0⟩) * ψ x := by
  classical
  let E : ℕ → Set Ω := fun x => ⋃ N, {ω | (run n ⟨j, j, 0, 0⟩ (fun t => ε t ω) N).pos = 0 ∧
    (run n ⟨j, j, 0, 0⟩ (fun t => ε t ω) N).met = x}
  have hae : ∀ᵐ ω ∂P, ω ∈ ⋃ N, {ω | (run n ⟨j, j, 0, 0⟩ (fun t => ε t ω) N).pos = 0} := by
    rw [ae_iff]; exact absorbed n P ε hm hind q hq0 hq1 hlaw _ hs
  have hfun : (fun ω => ψ (Xmet n j ε ω).toNat) =ᵐ[P]
      fun ω => ∑ x ∈ range n, (E x).indicator (fun _ => ψ x) ω := by
    filter_upwards [hae] with ω hω
    obtain ⟨N, hN⟩ := Set.mem_iUnion.1 hω
    have hsup := (sup_at n ⟨j, j, 0, 0⟩ (fun t => ε t ω) N hN).1
    have hX : Xmet n j ε ω = ((run n ⟨j, j, 0, 0⟩ (fun t => ε t ω) N).met : ℕ∞) := hsup
    have hlt := met_lt n _ (inv_run n _ hs (fun t => ε t ω) N)
    rw [hX, ENat.toNat_coe, Finset.sum_eq_single ((run n ⟨j, j, 0, 0⟩ (fun t => ε t ω) N).met)]
    · rw [Set.indicator_of_mem]
      exact Set.mem_iUnion.2 ⟨N, hN, rfl⟩
    · intro x _ hx
      rw [Set.indicator_of_notMem]
      intro hmem
      obtain ⟨N', hN', hx'⟩ := Set.mem_iUnion.1 hmem
      have h2 := (sup_at n ⟨j, j, 0, 0⟩ (fun t => ε t ω) N' hN').1
      apply hx
      rw [← hx']
      exact_mod_cast (h2.symm.trans hsup)
    · intro h; exact absurd (Finset.mem_range.2 hlt) h
  have hEm : ∀ x, MeasurableSet (E x) := fun x => MeasurableSet.iUnion fun N =>
    (prob_eq_g n P ε hm hind q hq0.le hq1 hlaw (fun st => st.pos = 0 ∧ st.met = x) N _).1
  rw [integral_congr_ae hfun, integral_finset_sum]
  · refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [integral_indicator_const _ (hEm x), smul_eq_mul, measureReal_def,
      probX n P ε hm hind q hq0 hq1 hlaw x (Finset.mem_range.1 hx) _ hs]
  · intro x _
    exact (integrable_const (ψ x)).indicator (hEm x)

end final

end NegNetQueue.Meets.T3

open NegNetQueue.Meets MeasureTheory ProbabilityTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (lam mu : ℝ) (c : ℕ)
    (hlam : 0 < lam) (hmu : 0 < mu) (hc : 1 ≤ c) (ε : ℕ → Ω → Bool)
    (hε : IsEventSeq P lam mu c ε) (n : ℕ) (hn : 2 ≤ n) :
    (∀ j : ℕ, 1 ≤ j → j ≤ n - 1 → ∀ x y : ℕ,
      (P {ω | Xmet n j ε ω = (x : ℕ∞) ∧ Yfill n j ε ω = (y : ℕ∞)}).toReal =
        if y = 0 ∧ x < n then
          ((Nat.choose (j + x - 1) (j - 1) : ℝ) - (Nat.choose (j + x - 1) (n - 1) : ℝ)) *
            rho lam mu c ^ x / (1 + rho lam mu c) ^ (j + x)
        else if 0 < y ∧ y ≤ x ∧ x < n then
          ((Nat.choose (j + (x - y) - 1) (n - 2) : ℝ) - (Nat.choose (j + (x - y) - 1) (n - 1) : ℝ)) *
            rho lam mu c ^ x / (1 + rho lam mu c) ^ (j + (x - y))
        else 0) ∧
    (∀ x : ℕ∞, P {ω | Xmet n n ε ω = x} = P {ω | Xmet n (n - 1) ε ω = x}) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ n - 1 → ∀ ψ : ℕ → ℝ,
      ∫ ω, ψ (Xmet n j ε ω).toNat ∂P =
        (1 / (1 + rho lam mu c)) ^ j *
          (∑ x ∈ Finset.range n,
              ((Nat.choose (j + x - 1) (j - 1) : ℝ) - (Nat.choose (j + x - 1) (n - 1) : ℝ)) *
                (rho lam mu c / (1 + rho lam mu c)) ^ x * ψ x +
            ∑ d ∈ Finset.range (n - 1),
              ((Nat.choose (j + d - 1) (n - 2) : ℝ) - (Nat.choose (j + d - 1) (n - 1) : ℝ)) *
                (1 / (1 + rho lam mu c)) ^ d *
                ∑ x ∈ Finset.Ico (d + 1) n, rho lam mu c ^ x * ψ x)) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ n - 1 → ∀ s : ℝ, s * rho lam mu c ≠ 1 →
      ∫ ω, s ^ (Xmet n j ε ω).toNat ∂P =
        (1 / (1 + rho lam mu c)) ^ j *
          (∑ x ∈ Finset.range n,
              ((Nat.choose (j + x - 1) (j - 1) : ℝ) - (Nat.choose (j + x - 1) (n - 1) : ℝ)) *
                (rho lam mu c * s / (1 + rho lam mu c)) ^ x +
            ∑ d ∈ Finset.range (n - 1),
              ((Nat.choose (j + d - 1) (n - 2) : ℝ) - (Nat.choose (j + d - 1) (n - 1) : ℝ)) *
                (1 / (1 + rho lam mu c)) ^ d *
                (((s * rho lam mu c) ^ n - (s * rho lam mu c) ^ (d + 1)) /
                  (s * rho lam mu c - 1)))) := by
  have := hε.isProb
  obtain ⟨hq, hr⟩ := T3.rq lam mu c hlam hmu hc
  have hlaw : ∀ t, P {ω | ε t ω = true} = ENNReal.ofReal (1 / (1 + rho lam mu c)) :=
    fun t => by rw [hε.law, hq]
  have hq0 : (0 : ℝ) < 1 / (1 + rho lam mu c) := by positivity
  have hq1 : 1 / (1 + rho lam mu c) ≤ (1 : ℝ) := by rw [div_le_one (by positivity)]; linarith
  have h4 : ∀ j : ℕ, 1 ≤ j → j ≤ n - 1 → ∀ ψ : ℕ → ℝ,
      ∫ ω, ψ (Xmet n j ε ω).toNat ∂P =
        (1 / (1 + rho lam mu c)) ^ j *
          (∑ x ∈ Finset.range n,
              ((Nat.choose (j + x - 1) (j - 1) : ℝ) - (Nat.choose (j + x - 1) (n - 1) : ℝ)) *
                (rho lam mu c / (1 + rho lam mu c)) ^ x * ψ x +
            ∑ d ∈ Finset.range (n - 1),
              ((Nat.choose (j + d - 1) (n - 2) : ℝ) - (Nat.choose (j + d - 1) (n - 1) : ℝ)) *
                (1 / (1 + rho lam mu c)) ^ d *
                ∑ x ∈ Finset.Ico (d + 1) n, rho lam mu c ^ x * ψ x) := by
    intro j hj1 hjn ψ
    have hs : T3.Inv n ⟨j, j, 0, 0⟩ := by
      unfold T3.Inv; dsimp only; exact ⟨by omega, le_refl _, by omega, fun _ => by omega⟩
    rw [T3.integral_formula n P ε hε.meas hε.indep _ hq0 hq1 hlaw j hs ψ]
    have hV : ∀ x ∈ Finset.range n,
        (∑ y ∈ Finset.range n, T3.Vt n x y (1 / (1 + rho lam mu c)) ⟨j, j, 0, 0⟩) * ψ x =
          (∑ y ∈ Finset.range n, T3.F3 (rho lam mu c) n j x y) * ψ x := fun x hx => by
      rw [Finset.sum_congr rfl (fun y _ => T3.eval3F _ hr n j x y hj1 hjn (Finset.mem_range.1 hx))]
    rw [Finset.sum_congr rfl hV]
    exact T3.alg4 _ hr n j ψ
  refine ⟨fun j hj1 hjn x y => T3.part3 n P ε hε.meas hε.indep _ hr hlaw j hj1 hjn x y,
    fun x => T3.part2 n hn P ε hε.meas hε.indep _ hq0 hq1 hlaw x, h4, ?_⟩
  intro j hj1 hjn s hs
  rw [h4 j hj1 hjn (fun x => s ^ x)]
  beta_reduce
  congr 2
  · refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [mul_assoc, ← mul_pow, div_mul_eq_mul_div]
  · refine Finset.sum_congr rfl (fun d hd => ?_)
    have hd' : d + 1 ≤ n := by have := Finset.mem_range.1 hd; omega
    rw [← geom_sum_Ico hs hd']
    congr 1
    refine Finset.sum_congr rfl (fun x _ => ?_)
    ring
