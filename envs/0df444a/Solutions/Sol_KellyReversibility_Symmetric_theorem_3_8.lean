-- Prove2me | solution 1 for KellyReversibility.Symmetric.theorem_3_8
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:30:29.372672+00:00
-- url     : https://prove2.me/submissions/1ee28ea4-3ca8-4d3e-bbd6-995cec8747e4

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Symmetric_SymmetricQueue
import Definitions.Def_KellyReversibility_Symmetric_Equilibrium
import Theorems.Thm_KellyReversibility_Symmetric_eq_3_18_equilibrium

set_option autoImplicit false

namespace P2M0cff

open KellyReversibility.Symmetric

lemma prod_phi (φ : ℕ → ℝ) : ∀ n : ℕ, ∏ i : Fin n, φ ((i : ℕ) + 1) = ∏ l ∈ Finset.Icc 1 n, φ l
  | 0 => by simp
  | n + 1 => by
    simp only [Fin.prod_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    rw [prod_phi φ n, Finset.prod_Icc_succ_top (by omega)]

lemma prod_get {α : Type*} (f : α → ℝ) : ∀ l : List α, ∏ i : Fin l.length, f (l.get i) = (l.map f).prod
  | [] => by simp
  | h :: t => by
    show ∏ i : Fin (t.length + 1), f ((h :: t).get i) = _
    rw [Fin.prod_univ_succ, List.map_cons, List.prod_cons, ← prod_get f t]
    rfl

lemma prod_map_div {K : Type*} (f : K → ℝ) (a : ℝ) :
    ∀ cs : List K, (cs.map fun c => f c / a).prod = (cs.map f).prod / a ^ cs.length
  | [] => by simp
  | c :: cs => by
    rw [List.map_cons, List.prod_cons, prod_map_div f a cs, List.map_cons, List.prod_cons,
      List.length_cons, pow_succ', div_mul_div_comm]

lemma hasSum_lists {V : Type*} (G : V → ℝ) (A : ℝ) (hG : HasSum G A) (hG0 : ∀ v, 0 ≤ G v)
    (n : ℕ) : HasSum (fun l : List V => if l.length = n then (l.map G).prod else 0) (A ^ n) := by
  induction n with
  | zero =>
    have h : HasSum (fun l : List V => if l.length = 0 then (l.map G).prod else 0)
        ((fun l : List V => if l.length = 0 then (l.map G).prod else 0) []) := by
      apply hasSum_single
      intro l hl
      cases l with
      | nil => exact absurd rfl hl
      | cons h t => simp
    simpa using h
  | succ n ih =>
    have hinj : Function.Injective (fun p : V × List V => p.1 :: p.2) := by
      intro p q h
      simp only [List.cons.injEq] at h
      exact Prod.ext h.1 h.2
    have hcond : ∀ l, l ∉ Set.range (fun p : V × List V => p.1 :: p.2) →
        (fun l : List V => if l.length = n + 1 then (l.map G).prod else 0) l = 0 := by
      intro l hl
      cases l with
      | nil => simp
      | cons h t => exact absurd ⟨(h, t), rfl⟩ hl
    rw [← hinj.hasSum_iff hcond]
    have heq : ((fun l : List V => if l.length = n + 1 then (l.map G).prod else 0) ∘
        fun p : V × List V => p.1 :: p.2) =
        fun p => G p.1 * (fun l : List V => if l.length = n then (l.map G).prod else 0) p.2 := by
      funext p
      simp only [Function.comp_apply, List.length_cons, List.map_cons, List.prod_cons,
        Nat.add_right_cancel_iff]
      split_ifs <;> simp
    rw [heq, pow_succ']
    have h0 : 0 ≤ (fun l : List V => if l.length = n then (l.map G).prod else 0) := by
      intro l
      dsimp only
      split_ifs
      · apply List.prod_nonneg
        intro a ha
        obtain ⟨v, -, rfl⟩ := List.mem_map.mp ha
        exact hG0 v
      · exact le_rfl
    exact HasSum.mul (f := G)
      (g := fun l : List V => if l.length = n then (l.map G).prod else 0) hG ih
      (hG.summable.mul_of_nonneg ih.summable (fun v => hG0 v) h0)

lemma hasSum_lists_map {V K : Type*} [DecidableEq K] (f : V → K) (G : V → ℝ) (A : K → ℝ)
    (hA : ∀ k, HasSum (fun v => if f v = k then G v else 0) (A k)) (hG0 : ∀ v, 0 ≤ G v) :
    ∀ cs : List K, HasSum (fun l : List V => if l.map f = cs then (l.map G).prod else 0)
      (cs.map A).prod := by
  intro cs
  induction cs with
  | nil =>
    have h : HasSum (fun l : List V => if l.map f = [] then (l.map G).prod else 0)
        ((fun l : List V => if l.map f = [] then (l.map G).prod else 0) []) := by
      apply hasSum_single
      intro l hl
      cases l with
      | nil => exact absurd rfl hl
      | cons h t => simp
    simpa using h
  | cons k cs ih =>
    have hinj : Function.Injective (fun p : V × List V => p.1 :: p.2) := by
      intro p q h
      simp only [List.cons.injEq] at h
      exact Prod.ext h.1 h.2
    have hcond : ∀ l, l ∉ Set.range (fun p : V × List V => p.1 :: p.2) →
        (fun l : List V => if l.map f = k :: cs then (l.map G).prod else 0) l = 0 := by
      intro l hl
      cases l with
      | nil => simp
      | cons h t => exact absurd ⟨(h, t), rfl⟩ hl
    rw [← hinj.hasSum_iff hcond]
    have heq : ((fun l : List V => if l.map f = k :: cs then (l.map G).prod else 0) ∘
        fun p : V × List V => p.1 :: p.2) =
        fun p => (fun v => if f v = k then G v else 0) p.1 *
          (fun l : List V => if l.map f = cs then (l.map G).prod else 0) p.2 := by
      funext p
      simp only [Function.comp_apply, List.map_cons, List.prod_cons, List.cons.injEq]
      by_cases h1 : f p.1 = k <;> by_cases h2 : p.2.map f = cs <;> simp [h1, h2]
    rw [heq, List.map_cons, List.prod_cons]
    have h0a : 0 ≤ (fun v => if f v = k then G v else 0) := by
      intro v
      dsimp only
      split_ifs
      · exact hG0 v
      · exact le_rfl
    have h0 : 0 ≤ (fun l : List V => if l.map f = cs then (l.map G).prod else 0) := by
      intro l
      dsimp only
      split_ifs
      · apply List.prod_nonneg
        intro a ha
        obtain ⟨v, -, rfl⟩ := List.mem_map.mp ha
        exact hG0 v
      · exact le_rfl
    exact HasSum.mul (f := fun v => if f v = k then G v else 0)
      (g := fun l : List V => if l.map f = cs then (l.map G).prod else 0) (hA k) ih
      ((hA k).summable.mul_of_nonneg ih.summable h0a h0)

variable {C Z : Type*}

/-- weight of a (class, refined class, stage) triple -/
noncomputable def F (Q : SymmetricQueue C Z) (s : Σ _ : C, Σ _ : Z, ℕ) : ℝ :=
  if 1 ≤ s.2.2 ∧ s.2.2 ≤ Q.w s.1 s.2.1 then Q.ν s.1 * Q.p s.1 s.2.1 * Q.d s.1 s.2.1 else 0

lemma F_nonneg (Q : SymmetricQueue C Z) (hQ : Q.IsValid) (s : Σ _ : C, Σ _ : Z, ℕ) :
    0 ≤ F Q s := by
  unfold F
  split_ifs
  · exact mul_nonneg (mul_nonneg (hQ.ν_nonneg _) (hQ.p_nonneg _ _)) (hQ.d_pos _ _).le
  · exact le_rfl

lemma meanReq_nonneg (Q : SymmetricQueue C Z) (hQ : Q.IsValid) (c : C) : 0 ≤ Q.meanReq c :=
  tsum_nonneg fun z =>
    mul_nonneg (mul_nonneg (hQ.p_nonneg c z) (Nat.cast_nonneg _)) (hQ.d_pos c z).le

lemma hasSum_F_fiber (Q : SymmetricQueue C Z) (hQ : Q.IsValid)
    (hmean : ∀ c, Summable (fun z => Q.p c z * (Q.w c z : ℝ) * Q.d c z)) (c : C) :
    HasSum (fun s : Σ _ : Z, ℕ => F Q ⟨c, s⟩) (Q.ν c * Q.meanReq c) := by
  have hz : ∀ z, HasSum (fun u : ℕ => F Q ⟨c, z, u⟩)
      (Q.ν c * (Q.p c z * (Q.w c z : ℝ) * Q.d c z)) := by
    intro z
    have : HasSum (fun u : ℕ => F Q ⟨c, z, u⟩) (∑ u ∈ Finset.Icc 1 (Q.w c z), F Q ⟨c, z, u⟩) :=
      hasSum_sum_of_ne_finset_zero (by
        intro u hu
        simp only [Finset.mem_Icc] at hu
        simp only [F]
        rw [if_neg hu])
    convert this using 1
    rw [Finset.sum_congr rfl (g := fun _ => Q.ν c * Q.p c z * Q.d c z) (by
      intro u hu
      simp only [Finset.mem_Icc] at hu
      simp only [F]
      rw [if_pos hu])]
    simp [Finset.sum_const, Nat.card_Icc]
    ring
  have htot : HasSum (fun z => Q.ν c * (Q.p c z * (Q.w c z : ℝ) * Q.d c z))
      (Q.ν c * Q.meanReq c) := (hmean c).hasSum.mul_left (Q.ν c)
  have hsum : Summable (fun s : Σ _ : Z, ℕ => F Q ⟨c, s⟩) := by
    rw [summable_sigma_of_nonneg (fun s => F_nonneg Q hQ _)]
    exact ⟨fun z => (hz z).summable, htot.summable.congr (fun z => ((hz z).tsum_eq).symm)⟩
  exact HasSum.sigma_of_hasSum htot hz hsum

lemma hasSum_F (Q : SymmetricQueue C Z) (hQ : Q.IsValid)
    (hmean : ∀ c, Summable (fun z => Q.p c z * (Q.w c z : ℝ) * Q.d c z))
    (hload : Summable (fun c => Q.ν c * Q.meanReq c)) :
    HasSum (F Q) Q.load := by
  have hf := hasSum_F_fiber Q hQ hmean
  have hsum : Summable (F Q) := by
    rw [summable_sigma_of_nonneg (fun s => F_nonneg Q hQ _)]
    exact ⟨fun c => (hf c).summable, hload.congr (fun c => ((hf c).tsum_eq).symm)⟩
  exact HasSum.sigma_of_hasSum hload.hasSum hf hsum

open Classical in
lemma hasSum_F_cls (Q : SymmetricQueue C Z) (hQ : Q.IsValid)
    (hmean : ∀ c, Summable (fun z => Q.p c z * (Q.w c z : ℝ) * Q.d c z))
    (hload : Summable (fun c => Q.ν c * Q.meanReq c)) (c : C) :
    HasSum (fun s : Σ _ : C, Σ _ : Z, ℕ => if s.1 = c then F Q s else 0)
      (Q.ν c * Q.meanReq c) := by
  have hsum : Summable (fun s : Σ _ : C, Σ _ : Z, ℕ => if s.1 = c then F Q s else 0) := by
    refine (hasSum_F Q hQ hmean hload).summable.of_nonneg_of_le (fun s => ?_) (fun s => ?_)
    · split_ifs
      · exact F_nonneg Q hQ s
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact F_nonneg Q hQ s
  refine HasSum.sigma_of_hasSum (hasSum_ite_eq c (Q.ν c * Q.meanReq c)) (fun c' => ?_) hsum
  by_cases h : c' = c
  · subst h
    simpa using hasSum_F_fiber Q hQ hmean c'
  · simpa [h] using (hasSum_zero : HasSum (fun _ : Σ _ : Z, ℕ => (0 : ℝ)) 0)

lemma hasSum_valid_of (Q : SymmetricQueue C Z) (hQ : Q.IsValid) (P : C → Prop)
    [DecidablePred P] (A : ℝ)
    (h : HasSum (fun s : Σ _ : C, Σ _ : Z, ℕ => if P s.1 then F Q s else 0) A) :
    HasSum (fun v : {e : Customer C Z // Q.ValidCustomer e} =>
      if P v.1.cls then Q.ν v.1.cls * Q.p v.1.cls v.1.ref * Q.d v.1.cls v.1.ref else 0) A := by
  let j : {e : Customer C Z // Q.ValidCustomer e} → (Σ _ : C, Σ _ : Z, ℕ) :=
    fun v => ⟨v.1.cls, v.1.ref, v.1.stage⟩
  have hj : Function.Injective j := by
    rintro ⟨⟨c1, r1, u1⟩, h1⟩ ⟨⟨c2, r2, u2⟩, h2⟩ h
    simp only [j, Sigma.mk.inj_iff, heq_eq_eq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  have hcond : ∀ s, s ∉ Set.range j →
      (fun s : Σ _ : C, Σ _ : Z, ℕ => if P s.1 then F Q s else 0) s = 0 := by
    rintro ⟨c, z, u⟩ hs
    simp only [F]
    split_ifs with hP hu
    · rcases (mul_nonneg (hQ.ν_nonneg c) (hQ.p_nonneg c z)).lt_or_eq with h' | h'
      · exact absurd ⟨⟨⟨c, z, u⟩, ⟨h', hu.1, hu.2⟩⟩, rfl⟩ hs
      · rw [← h', zero_mul]
    · rfl
    · rfl
  have key := (hj.hasSum_iff hcond).mpr h
  convert key using 1
  funext v
  have hv : 1 ≤ v.1.stage ∧ v.1.stage ≤ Q.w v.1.cls v.1.ref := ⟨v.2.2.1, v.2.2.2⟩
  simp only [Function.comp_apply, j, F]
  rw [if_pos hv]

lemma hasSum_states_of (Q : SymmetricQueue C Z) (P : List (Customer C Z) → Prop)
    [DecidablePred P] (G : Customer C Z → ℝ) (A : ℝ)
    (h : HasSum (fun l : List {e : Customer C Z // Q.ValidCustomer e} =>
      if P (l.map Subtype.val) then (l.map fun v => G v.1).prod else 0) A) :
    HasSum (fun x : Q.State => if P x.1 then (x.1.map G).prod else 0) A := by
  let ι : List {e : Customer C Z // Q.ValidCustomer e} → Q.State :=
    fun l => Subtype.mk (p := fun x : List (Customer C Z) => ∀ e ∈ x, Q.ValidCustomer e)
      (l.map Subtype.val) (by
        intro e he
        obtain ⟨v, -, rfl⟩ := List.mem_map.mp he
        exact v.2)
  have hι : Function.Injective ι := by
    intro l1 l2 h
    have : l1.map Subtype.val = l2.map Subtype.val := congrArg Subtype.val h
    exact (List.map_injective_iff.mpr Subtype.val_injective) this
  have hcond : ∀ x, x ∉ Set.range ι →
      (fun x : Q.State => if P x.1 then (x.1.map G).prod else 0) x = 0 := by
    intro x hx
    exact absurd ⟨x.1.attach.map (fun e => ⟨e.1, x.2 e.1 e.2⟩), Subtype.ext (by simp [ι])⟩ hx
  rw [← (hι.hasSum_iff hcond)]
  convert h using 1
  funext l
  show (if P (l.map Subtype.val) then ((l.map Subtype.val).map G).prod else 0) = _
  rw [List.map_map]
  rfl

lemma eqWeight_eq (Q : SymmetricQueue C Z) (l : List (Customer C Z)) :
    Q.eqWeight l = (l.map fun e => Q.ν e.cls * Q.p e.cls e.ref * Q.d e.cls e.ref).prod /
      ∏ k ∈ Finset.Icc 1 l.length, Q.φ k := by
  unfold SymmetricQueue.eqWeight
  rw [Finset.prod_div_distrib, prod_phi Q.φ l.length,
    ← prod_get (fun e => Q.ν e.cls * Q.p e.cls e.ref * Q.d e.cls e.ref) l]

open Classical in
theorem class_sequence_marginal {C Z : Type*} [Countable C] [Countable Z]
    (Q : SymmetricQueue C Z) (hQ : Q.IsValid)
    (hmean : ∀ c, Summable (fun z => Q.p c z * (Q.w c z : ℝ) * Q.d c z))
    (hload : Summable (fun c => Q.ν c * Q.meanReq c)) (b : ℝ) (cs : List C) :
    HasSum (fun x : Q.State => if x.1.map Customer.cls = cs then b * Q.eqWeight x.1 else 0)
      (b * Q.normTerm Q.load cs.length *
        (cs.map fun c => Q.ν c * Q.meanReq c / Q.load).prod) := by
  set g : Customer C Z → ℝ := fun e => Q.ν e.cls * Q.p e.cls e.ref * Q.d e.cls e.ref with hg
  have hA : ∀ c, HasSum (fun v : {e : Customer C Z // Q.ValidCustomer e} =>
      if (fun v : {e : Customer C Z // Q.ValidCustomer e} => v.1.cls) v = c then g v.1 else 0)
      (Q.ν c * Q.meanReq c) := fun c =>
    hasSum_valid_of Q hQ (fun c' => c' = c) _ (hasSum_F_cls Q hQ hmean hload c)
  have hL := hasSum_lists_map (fun v : {e : Customer C Z // Q.ValidCustomer e} => v.1.cls)
    (fun v => g v.1) (fun c => Q.ν c * Q.meanReq c) hA
    (fun v => mul_nonneg (mul_nonneg (hQ.ν_nonneg _) (hQ.p_nonneg _ _)) (hQ.d_pos _ _).le) cs
  have hS : HasSum (fun x : Q.State =>
      if x.1.map Customer.cls = cs then (x.1.map g).prod else 0)
      (cs.map fun c => Q.ν c * Q.meanReq c).prod := by
    refine hasSum_states_of Q (fun l => l.map Customer.cls = cs) g _ ?_
    convert hL using 1
    funext l
    simp only [List.map_map]
    rfl
  have := hS.mul_left (b / ∏ k ∈ Finset.Icc 1 cs.length, Q.φ k)
  have hf : (fun x : Q.State => if x.1.map Customer.cls = cs then b * Q.eqWeight x.1 else 0) =
      fun x => (b / ∏ k ∈ Finset.Icc 1 cs.length, Q.φ k) *
        (if x.1.map Customer.cls = cs then (x.1.map g).prod else 0) := by
    funext x
    split_ifs with h
    · rw [eqWeight_eq, ← h, List.length_map]
      ring
    · simp
  have hv : b * Q.normTerm Q.load cs.length *
      (cs.map fun c => Q.ν c * Q.meanReq c / Q.load).prod =
      (b / ∏ k ∈ Finset.Icc 1 cs.length, Q.φ k) * (cs.map fun c => Q.ν c * Q.meanReq c).prod := by
    simp only [SymmetricQueue.normTerm]
    rw [prod_map_div]
    by_cases hl : Q.load = 0
    · cases cs with
      | nil => simp
      | cons c cs =>
        have h0 : HasSum (fun c => Q.ν c * Q.meanReq c) 0 := by
          have := hload.hasSum
          rwa [show (∑' c, Q.ν c * Q.meanReq c) = Q.load from rfl, hl] at this
        have hz := (hasSum_zero_iff_of_nonneg (fun c =>
          mul_nonneg (hQ.ν_nonneg c) (meanReq_nonneg Q hQ c))).mp h0
        have hc : Q.ν c * Q.meanReq c = 0 := congrFun hz c
        simp [hl, hc]
    · have hp : Q.load ^ cs.length ≠ 0 := pow_ne_zero _ hl
      field_simp
  rw [hf, hv]
  exact this

theorem length_marginal {C Z : Type*} [Countable C] [Countable Z]
    (Q : SymmetricQueue C Z) (hQ : Q.IsValid)
    (hmean : ∀ c, Summable (fun z => Q.p c z * (Q.w c z : ℝ) * Q.d c z))
    (hload : Summable (fun c => Q.ν c * Q.meanReq c)) (b : ℝ) (n : ℕ) :
    HasSum (fun x : Q.State => if x.1.length = n then b * Q.eqWeight x.1 else 0)
      (b * Q.normTerm Q.load n) := by
  set g : Customer C Z → ℝ := fun e => Q.ν e.cls * Q.p e.cls e.ref * Q.d e.cls e.ref with hg
  have hT : HasSum (fun v : {e : Customer C Z // Q.ValidCustomer e} => g v.1) Q.load := by
    have := hasSum_valid_of Q hQ (fun _ => True) Q.load (by simpa using hasSum_F Q hQ hmean hload)
    simpa using this
  have hL := hasSum_lists (fun v : {e : Customer C Z // Q.ValidCustomer e} => g v.1) Q.load hT
    (fun v => mul_nonneg (mul_nonneg (hQ.ν_nonneg _) (hQ.p_nonneg _ _)) (hQ.d_pos _ _).le) n
  have hS : HasSum (fun x : Q.State => if x.1.length = n then (x.1.map g).prod else 0)
      (Q.load ^ n) := by
    refine hasSum_states_of Q (fun l => l.length = n) g _ ?_
    convert hL using 1
    funext l
    simp only [List.length_map]
  have := hS.mul_left (b / ∏ k ∈ Finset.Icc 1 n, Q.φ k)
  have hf : (fun x : Q.State => if x.1.length = n then b * Q.eqWeight x.1 else 0) =
      fun x => (b / ∏ k ∈ Finset.Icc 1 n, Q.φ k) *
        (if x.1.length = n then (x.1.map g).prod else 0) := by
    funext x
    split_ifs with h
    · rw [eqWeight_eq, h]
      ring
    · simp
  have hv : b * Q.normTerm Q.load n = (b / ∏ k ∈ Finset.Icc 1 n, Q.φ k) * Q.load ^ n := by
    simp only [SymmetricQueue.normTerm]
    ring
  rw [hf, hv]
  exact this

end P2M0cff

namespace P2M0cffQR

open KellyReversibility.Symmetric

lemma prod_phi (φ : ℕ → ℝ) : ∀ n : ℕ, ∏ i : Fin n, φ ((i : ℕ) + 1) = ∏ l ∈ Finset.Icc 1 n, φ l
  | 0 => by simp
  | n + 1 => by
    simp only [Fin.prod_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    rw [prod_phi φ n, Finset.prod_Icc_succ_top (by omega)]

lemma prod_get {α : Type*} (f : α → ℝ) : ∀ l : List α, ∏ i : Fin l.length, f (l.get i) = (l.map f).prod
  | [] => by simp
  | h :: t => by
    show ∏ i : Fin (t.length + 1), f ((h :: t).get i) = _
    rw [Fin.prod_univ_succ, List.map_cons, List.prod_cons, ← prod_get f t]
    rfl

variable {C Z : Type*}

/-- the weight factor `ν p d` of one customer -/
noncomputable def g (Q : SymmetricQueue C Z) (e : Customer C Z) : ℝ :=
  Q.ν e.cls * Q.p e.cls e.ref * Q.d e.cls e.ref

lemma eqWeight_eq (Q : SymmetricQueue C Z) (l : List (Customer C Z)) :
    Q.eqWeight l = (l.map (g Q)).prod / ∏ k ∈ Finset.Icc 1 l.length, Q.φ k := by
  unfold SymmetricQueue.eqWeight
  rw [Finset.prod_div_distrib, prod_phi Q.φ l.length, ← prod_get (g Q) l]
  rfl

lemma eqWeight_pos (Q : SymmetricQueue C Z) (hQ : Q.IsValid) (x : Q.State) :
    0 < Q.eqWeight x.1 := by
  rw [eqWeight_eq]
  apply div_pos
  · apply List.prod_pos
    intro a ha
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    exact mul_pos (x.2 e he).1 (hQ.d_pos _ _)
  · apply Finset.prod_pos
    intro l hl
    exact hQ.φ_pos l (by simp only [Finset.mem_Icc] at hl; omega)

lemma eqWeight_insert (Q : SymmetricQueue C Z) (l : List (Customer C Z)) (i : ℕ)
    (hi : i ≤ l.length) (e : Customer C Z) :
    Q.eqWeight (l.insertIdx i e) = Q.eqWeight l * g Q e / Q.φ (l.length + 1) := by
  rw [eqWeight_eq, eqWeight_eq, List.length_insertIdx_of_le_length hi,
    ((List.perm_insertIdx e l hi).map (g Q)).prod_eq, List.map_cons, List.prod_cons,
    Finset.prod_Icc_succ_top (by omega)]
  ring

/-- count of customers whose key is `k` -/
def cnt {K : Type*} [DecidableEq K] (κ : C → Z → K) (l : List (Customer C Z)) (k : K) : ℕ :=
  l.countP (fun e => decide (κ e.cls e.ref = k))

lemma cnt_insert {K : Type*} [DecidableEq K] (κ : C → Z → K) (l : List (Customer C Z)) (i : ℕ)
    (hi : i ≤ l.length) (e : Customer C Z) (k : K) :
    cnt κ (l.insertIdx i e) k = cnt κ l k + if κ e.cls e.ref = k then 1 else 0 := by
  unfold cnt
  rw [(List.perm_insertIdx e l hi).countP_eq, List.countP_cons]
  simp

lemma cnt_set {K : Type*} [DecidableEq K] (κ : C → Z → K) (l : List (Customer C Z)) (i : ℕ)
    (hi : i < l.length) (e : Customer C Z) (he : κ e.cls e.ref = κ l[i].cls l[i].ref) (k : K) :
    cnt κ (l.set i e) k = cnt κ l k := by
  unfold cnt
  rw [List.countP_set hi]
  by_cases h : κ l[i].cls l[i].ref = k
  · have hpos : 0 < l.countP (fun e => decide (κ e.cls e.ref = k)) :=
      List.countP_pos_iff.mpr ⟨l[i], List.getElem_mem hi, by simp [h]⟩
    simp only [he, h, decide_true, if_true]
    omega
  · simp [he, h]

lemma cnt_erase_le {K : Type*} [DecidableEq K] (κ : C → Z → K) (l : List (Customer C Z))
    (i : ℕ) (k : K) : cnt κ (l.eraseIdx i) k ≤ cnt κ l k :=
  (List.eraseIdx_sublist l i).countP_le

lemma cnt_le_insert {K : Type*} [DecidableEq K] (κ : C → Z → K) (l : List (Customer C Z))
    (i : ℕ) (e : Customer C Z) (k : K) : cnt κ l k ≤ cnt κ (l.insertIdx i e) k :=
  (List.sublist_insertIdx l i e).countP_le

lemma gamma_sum (Q : SymmetricQueue C Z) (hQ : Q.IsValid) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), Q.γ (j + 1) (n + 1) = 1 := by
  rw [← hQ.γ_sum (n + 1) (Nat.succ_pos n), Finset.range_eq_Ico,
    Finset.sum_Ico_add' (fun l => Q.γ l (n + 1)) 0 (n + 1) 1]
  congr 1

section generic

variable (Q : SymmetricQueue C Z) (hQ : Q.IsValid) {K : Type*} [DecidableEq K]
  (κ : C → Z → K) (count : Q.State → K → ℕ) (hcount : ∀ x k, count x k = cnt κ x.1 k)

include hcount in
lemma one_more_of_ins (x x' : Q.State) (j : ℕ) (hj : j ≤ x.1.length) (e : Customer C Z)
    (hins : x.1.insertIdx j e = x'.1) (k : K) (hk : κ e.cls e.ref = k) :
    OneMoreOf count x' x k := by
  unfold OneMoreOf
  refine ⟨?_, fun k' hk' => ?_⟩
  · rw [hcount, hcount, ← hins, cnt_insert κ _ j hj, if_pos hk]
  · rw [hcount, hcount, ← hins, cnt_insert κ _ j hj,
      if_neg (fun h => hk' (h.symm.trans hk)), add_zero]

include hcount in
lemma kappa_of_one_more (x x' : Q.State) (j : ℕ) (hj : j ≤ x.1.length) (e : Customer C Z)
    (hins : x.1.insertIdx j e = x'.1) (k : K) (hO : OneMoreOf count x' x k) :
    κ e.cls e.ref = k := by
  by_contra hne
  unfold OneMoreOf at hO
  have h1 := hO.1
  rw [hcount, hcount, ← hins, cnt_insert κ _ j hj, if_neg hne] at h1
  omega

open Classical in
/-- arrival term `j` of the forward sum, restricted to arrivals of key `k` -/
noncomputable def A (x : Q.State) (k : K) (j : ℕ) (x' : Q.State) : ℝ :=
  match x'.1[j]? with
  | some e =>
      if e.stage = 1 ∧ x.1.insertIdx j e = x'.1 ∧ κ e.cls e.ref = k then
        Q.ν e.cls * Q.p e.cls e.ref * Q.γ (j + 1) (x.1.length + 1)
      else 0
  | none => 0

open Classical in
/-- departure term `i` of the reversed sum -/
noncomputable def B (x : Q.State) (k : K) (i : ℕ) (x' : Q.State) : ℝ :=
  match x'.1[i]? with
  | some e =>
      if e.stage = Q.w e.cls e.ref ∧ x'.1.eraseIdx i = x.1 ∧ κ e.cls e.ref = k then
        Q.ν e.cls * Q.p e.cls e.ref * Q.γ (i + 1) (x.1.length + 1)
      else 0
  | none => 0

/-- the new customer's admissible refined classes -/
def E (k : K) : Type _ := {cz : C × Z // 0 < Q.ν cz.1 * Q.p cz.1 cz.2 ∧ κ cz.1 cz.2 = k}

include hQ in
lemma valid_mk (k : K) (cz : E Q κ k) (u : ℕ) (hu1 : 1 ≤ u) (hu2 : u ≤ Q.w cz.1.1 cz.1.2) :
    Q.ValidCustomer ⟨cz.1.1, cz.1.2, u⟩ := ⟨cz.2.1, hu1, hu2⟩

/-- insert a valid customer into a state -/
def ins (x : Q.State) (i : ℕ) (hi : i ≤ x.1.length) (e : Customer C Z)
    (he : Q.ValidCustomer e) : Q.State :=
  Subtype.mk (p := fun l : List (Customer C Z) => ∀ e ∈ l, Q.ValidCustomer e)
    (x.1.insertIdx i e) (by
      intro e' he'
      rcases List.mem_cons.mp ((List.perm_insertIdx e x.1 hi).mem_iff.mp he') with h | h
      · rw [h]; exact he
      · exact x.2 e' h)

lemma ins_inj (x : Q.State) (i : ℕ) (hi : i ≤ x.1.length) (e1 e2 : Customer C Z)
    (h1 : Q.ValidCustomer e1) (h2 : Q.ValidCustomer e2)
    (h : ins Q x i hi e1 h1 = ins Q x i hi e2 h2) : e1 = e2 := by
  have h' : x.1.insertIdx i e1 = x.1.insertIdx i e2 := congrArg Subtype.val h
  have := congrArg (fun l => l[i]?) h'
  simp only [List.getElem?_insertIdx_self, if_pos hi, Option.some.injEq] at this
  exact this

include hQ hcount in
lemma hasSum_A (α : K → ℝ)
    (hα : ∀ k, HasSum (fun cz : E Q κ k => Q.ν cz.1.1 * Q.p cz.1.1 cz.1.2) (α k))
    (x : Q.State) (k : K) (j : ℕ) (hj : j ≤ x.1.length) :
    HasSum (A Q κ x k j) (α k * Q.γ (j + 1) (x.1.length + 1)) := by
  let ι : E Q κ k → Q.State := fun cz =>
    ins Q x j hj ⟨cz.1.1, cz.1.2, 1⟩ (valid_mk Q hQ κ k cz 1 le_rfl (hQ.w_pos _ _))
  have hι : Function.Injective ι := by
    intro a b h
    have := ins_inj Q x j hj _ _ _ _ h
    simp only [Customer.mk.injEq, and_true] at this
    exact Subtype.ext (Prod.ext this.1 this.2)
  have hcond : ∀ x' : Q.State, x' ∉ Set.range ι → A Q κ x k j x' = 0 := by
    intro x' hx'
    unfold A
    cases h : x'.1[j]? with
    | none => rfl
    | some e =>
      dsimp only
      rw [if_neg]
      rintro ⟨hs, hins, hk⟩
      have he : Q.ValidCustomer e := x'.2 e (List.mem_of_getElem? h)
      refine hx' ⟨⟨(e.cls, e.ref), he.1, hk⟩, Subtype.ext ?_⟩
      show x.1.insertIdx j ⟨e.cls, e.ref, 1⟩ = x'.1
      rw [← hins, ← hs]
  rw [← hι.hasSum_iff hcond]
  have key := (hα k).mul_right (Q.γ (j + 1) (x.1.length + 1))
  have hf : (A Q κ x k j ∘ ι) = fun cz : E Q κ k =>
      Q.ν cz.1.1 * Q.p cz.1.1 cz.1.2 * Q.γ (j + 1) (x.1.length + 1) := by
    funext cz
    show A Q κ x k j (ins Q x j hj _ _) = _
    unfold A ins
    simp only [List.getElem?_insertIdx_self, if_pos hj]
    rw [if_pos (by simp [cz.2.2])]
  rw [hf]
  exact key

include hQ hcount in
lemma hasSum_B (α : K → ℝ)
    (hα : ∀ k, HasSum (fun cz : E Q κ k => Q.ν cz.1.1 * Q.p cz.1.1 cz.1.2) (α k))
    (x : Q.State) (k : K) (i : ℕ) (hi : i ≤ x.1.length) :
    HasSum (B Q κ x k i) (α k * Q.γ (i + 1) (x.1.length + 1)) := by
  let ι : E Q κ k → Q.State := fun cz =>
    ins Q x i hi ⟨cz.1.1, cz.1.2, Q.w cz.1.1 cz.1.2⟩
      (valid_mk Q hQ κ k cz _ (hQ.w_pos _ _) le_rfl)
  have hι : Function.Injective ι := by
    intro a b h
    have := ins_inj Q x i hi _ _ _ _ h
    simp only [Customer.mk.injEq] at this
    exact Subtype.ext (Prod.ext this.1 this.2.1)
  have hcond : ∀ x' : Q.State, x' ∉ Set.range ι → B Q κ x k i x' = 0 := by
    intro x' hx'
    unfold B
    cases h : x'.1[i]? with
    | none => rfl
    | some e =>
      dsimp only
      rw [if_neg]
      rintro ⟨hs, herase, hk⟩
      have he : Q.ValidCustomer e := x'.2 e (List.mem_of_getElem? h)
      obtain ⟨hi', he'⟩ := List.getElem?_eq_some_iff.mp h
      refine hx' ⟨⟨(e.cls, e.ref), he.1, hk⟩, Subtype.ext ?_⟩
      show x.1.insertIdx i ⟨e.cls, e.ref, Q.w e.cls e.ref⟩ = x'.1
      rw [← herase, ← hs]
      have : (⟨e.cls, e.ref, e.stage⟩ : Customer C Z) = x'.1[i] := he'.symm
      rw [this]
      exact List.insertIdx_eraseIdx_getElem hi'
  rw [← hι.hasSum_iff hcond]
  have key := (hα k).mul_right (Q.γ (i + 1) (x.1.length + 1))
  have hf : (B Q κ x k i ∘ ι) = fun cz : E Q κ k =>
      Q.ν cz.1.1 * Q.p cz.1.1 cz.1.2 * Q.γ (i + 1) (x.1.length + 1) := by
    funext cz
    show B Q κ x k i (ins Q x i hi _ _) = _
    unfold B ins
    simp only [List.getElem?_insertIdx_self, if_pos hi]
    rw [if_pos (by simp [cz.2.2, List.eraseIdx_insertIdx_self])]
  rw [hf]
  exact key

include hcount in
open Classical in
lemma fwd_point (x x' : Q.State) (k : K) :
    (if OneMoreOf count x' x k then Q.rate x x' else 0) =
      ∑ j ∈ Finset.range (x.1.length + 1), A Q κ x k j x' := by
  by_cases hO : OneMoreOf count x' x k
  · rw [if_pos hO]
    have h1 : count x' k = count x k + 1 := by unfold OneMoreOf at hO; exact hO.1
    rw [hcount, hcount] at h1
    have hserv : Q.serviceRate x.1 x'.1 = 0 := by
      unfold SymmetricQueue.serviceRate
      apply Finset.sum_eq_zero
      intro i _
      cases h : x.1[i]? with
      | none => rfl
      | some e =>
        obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.mp h
        dsimp only
        rw [if_neg]
        rintro (⟨-, hset⟩ | ⟨-, herase⟩)
        · have := cnt_set κ x.1 i hi'
            { cls := x.1[i].cls, ref := x.1[i].ref, stage := x.1[i].stage + 1 } rfl k
          rw [← hset, this] at h1
          omega
        · have := cnt_erase_le κ x.1 i k
          rw [← herase] at h1
          omega
    unfold SymmetricQueue.rate
    rw [hserv, add_zero]
    unfold SymmetricQueue.arrivalRate
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ x.1.length := by simp only [Finset.mem_range] at hj; omega
    unfold A
    cases h : x'.1[j]? with
    | none => rfl
    | some e =>
      dsimp only
      by_cases hc : e.stage = 1 ∧ x.1.insertIdx j e = x'.1
      · have hk := kappa_of_one_more Q κ count hcount x x' j hj' e hc.2 k hO
        rw [if_pos hc, if_pos ⟨hc.1, hc.2, hk⟩]
      · rw [if_neg hc, if_neg (fun h' => hc ⟨h'.1, h'.2.1⟩)]
  · rw [if_neg hO]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    have hj' : j ≤ x.1.length := by simp only [Finset.mem_range] at hj; omega
    unfold A
    cases h : x'.1[j]? with
    | none => rfl
    | some e =>
      dsimp only
      rw [if_neg]
      rintro ⟨-, hins, hk⟩
      exact hO (one_more_of_ins Q κ count hcount x x' j hj' e hins k hk)

include hQ hcount in
open Classical in
lemma rev_point (b : ℝ) (hb : 0 < b) (x x' : Q.State) (k : K) :
    (if OneMoreOf count x' x k then
      KellyStochasticNetworks.reversedRates (fun x : Q.State => b * Q.eqWeight x.1) Q.rate x x'
      else 0) =
      ∑ i ∈ Finset.range (x.1.length + 1), B Q κ x k i x' := by
  by_cases hO : OneMoreOf count x' x k
  · rw [if_pos hO]
    have h1 : count x' k = count x k + 1 := by unfold OneMoreOf at hO; exact hO.1
    rw [hcount, hcount] at h1
    have harr : Q.arrivalRate x'.1 x.1 = 0 := by
      unfold SymmetricQueue.arrivalRate
      apply Finset.sum_eq_zero
      intro j _
      cases h : x.1[j]? with
      | none => rfl
      | some e =>
        dsimp only
        rw [if_neg]
        rintro ⟨-, hins⟩
        have := cnt_le_insert κ x'.1 j e k
        rw [hins] at this
        omega
    have hset : ∀ (i : ℕ) (hi : i < x'.1.length) (u : ℕ),
        x'.1.set i { cls := x'.1[i].cls, ref := x'.1[i].ref, stage := u } ≠ x.1 := by
      intro i hi u hs
      have := cnt_set κ x'.1 i hi { cls := x'.1[i].cls, ref := x'.1[i].ref, stage := u } rfl k
      rw [hs] at this
      omega
    have hπ : 0 < Q.eqWeight x.1 := eqWeight_pos Q hQ x
    unfold KellyStochasticNetworks.reversedRates SymmetricQueue.rate
    beta_reduce
    rw [harr, zero_add]
    by_cases hlen : x'.1.length = x.1.length + 1
    · unfold SymmetricQueue.serviceRate
      rw [hlen, Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      have hi1 : i < x.1.length + 1 := Finset.mem_range.mp hi
      unfold B
      cases h : x'.1[i]? with
      | none => simp
      | some e =>
        obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.mp h
        dsimp only
        by_cases hc : x'.1[i].stage = Q.w x'.1[i].cls x'.1[i].ref ∧ x'.1.eraseIdx i = x.1
        · have hins : x.1.insertIdx i x'.1[i] = x'.1 := by
            rw [← hc.2]; exact List.insertIdx_eraseIdx_getElem hi'
          have hk := kappa_of_one_more Q κ count hcount x x' i (by omega) _ hins k hO
          rw [if_pos (Or.inr hc), if_pos ⟨hc.1, hc.2, hk⟩]
          have hW := eqWeight_insert Q x.1 i (by omega) x'.1[i]
          rw [hins] at hW
          rw [hW]
          have hφ : Q.φ (x.1.length + 1) ≠ 0 := (hQ.φ_pos _ (Nat.succ_pos _)).ne'
          have hd : Q.d x'.1[i].cls x'.1[i].ref ≠ 0 := (hQ.d_pos _ _).ne'
          have hb' : b ≠ 0 := hb.ne'
          have hπ' : Q.eqWeight x.1 ≠ 0 := hπ.ne'
          unfold g
          field_simp
        · rw [if_neg, if_neg (fun h' => hc ⟨h'.1, h'.2.1⟩), mul_zero, zero_div]
          rintro (⟨-, hs⟩ | hc')
          · exact hset i hi' _ hs
          · exact hc hc'
    · have hserv : Q.serviceRate x'.1 x.1 = 0 := by
        unfold SymmetricQueue.serviceRate
        apply Finset.sum_eq_zero
        intro i _
        cases h : x'.1[i]? with
        | none => rfl
        | some e =>
          obtain ⟨hi'', rfl⟩ := List.getElem?_eq_some_iff.mp h
          dsimp only
          rw [if_neg]
          rintro (⟨-, hs⟩ | ⟨-, herase⟩)
          · exact hset i hi'' _ hs
          · have := congrArg List.length herase
            rw [List.length_eraseIdx, if_pos hi''] at this
            omega
      rw [hserv, mul_zero, zero_div]
      symm
      apply Finset.sum_eq_zero
      intro i _
      unfold B
      cases h : x'.1[i]? with
      | none => rfl
      | some e =>
        obtain ⟨hi'', rfl⟩ := List.getElem?_eq_some_iff.mp h
        dsimp only
        rw [if_neg]
        rintro ⟨-, herase, -⟩
        have := congrArg List.length herase
        rw [List.length_eraseIdx, if_pos hi''] at this
        omega
  · rw [if_neg hO]
    symm
    apply Finset.sum_eq_zero
    intro i _
    unfold B
    cases h : x'.1[i]? with
    | none => rfl
    | some e =>
      obtain ⟨hi'', rfl⟩ := List.getElem?_eq_some_iff.mp h
      dsimp only
      rw [if_neg]
      rintro ⟨-, herase, hk⟩
      have hlen := congrArg List.length herase
      rw [List.length_eraseIdx, if_pos hi''] at hlen
      have hins : x.1.insertIdx i x'.1[i] = x'.1 := by
        rw [← herase]; exact List.insertIdx_eraseIdx_getElem hi''
      exact hO (one_more_of_ins Q κ count hcount x x' i (by omega) _ hins k hk)

include hQ hcount in
theorem qr_generic (b : ℝ) (hb : 0 < b) (α : K → ℝ)
    (hα : ∀ k, HasSum (fun cz : E Q κ k => Q.ν cz.1.1 * Q.p cz.1.1 cz.1.2) (α k)) :
    QuasiReversibleRates (fun x : Q.State => b * Q.eqWeight x.1) Q.rate count := by
  unfold QuasiReversibleRates
  refine ⟨α, fun k x => ⟨?_, ?_⟩⟩
  · have hS := hasSum_sum (s := Finset.range (x.1.length + 1))
      (fun j hj => hasSum_A Q hQ κ count hcount α hα x k j
        (by simp only [Finset.mem_range] at hj; omega))
    rw [← Finset.mul_sum, gamma_sum Q hQ, mul_one] at hS
    have hf := funext fun x' => fwd_point Q κ count hcount x x' k
    rw [hf]
    exact hS
  · have hS := hasSum_sum (s := Finset.range (x.1.length + 1))
      (fun i hi => hasSum_B Q hQ κ count hcount α hα x k i
        (by simp only [Finset.mem_range] at hi; omega))
    rw [← Finset.mul_sum, gamma_sum Q hQ, mul_one] at hS
    have hf := funext fun x' => rev_point Q hQ κ count hcount b hb x x' k
    rw [hf]
    exact hS

end generic

theorem quasiReversible_class {C Z : Type*} [Countable C] [Countable Z]
    (Q : SymmetricQueue C Z) (hQ : Q.IsValid) (b : ℝ) (hb : 0 < b) :
    QuasiReversibleRates (fun x : Q.State => b * Q.eqWeight x.1) Q.rate
      (fun x c => classCount x.1 c) := by
  classical
  refine qr_generic Q hQ (fun c _ => c) (fun x c => classCount x.1 c) (fun x c => ?_) b hb Q.ν
    (fun c => ?_)
  · unfold classCount cnt
    rfl
  · let φ' : E Q (fun c _ => c) c → Z := fun cz => cz.1.2
    have hφ : Function.Injective φ' := by
      intro a b h
      apply Subtype.ext
      have ha : a.1.1 = c := a.2.2
      have hb : b.1.1 = c := b.2.2
      exact Prod.ext (ha.trans hb.symm) h
    have hcond : ∀ z, z ∉ Set.range φ' → (fun z => Q.ν c * Q.p c z) z = 0 := by
      intro z hz
      rcases (mul_nonneg (hQ.ν_nonneg c) (hQ.p_nonneg c z)).lt_or_eq with h | h
      · exact absurd ⟨⟨(c, z), h, rfl⟩, rfl⟩ hz
      · exact h.symm
    have h0 := (hQ.p_hasSum c).mul_left (Q.ν c)
    rw [mul_one] at h0
    have key := (hφ.hasSum_iff (f := fun z => Q.ν c * Q.p c z) hcond).mpr h0
    have hf : (fun cz : E Q (fun c _ => c) c => Q.ν cz.1.1 * Q.p cz.1.1 cz.1.2) =
        (fun z => Q.ν c * Q.p c z) ∘ φ' := by
      funext cz
      have h : cz.1.1 = c := cz.2.2
      simp only [Function.comp_apply, φ', h]
    rw [hf]
    exact key

theorem quasiReversible_refined {C Z : Type*} [Countable C] [Countable Z]
    (Q : SymmetricQueue C Z) (hQ : Q.IsValid) (b : ℝ) (hb : 0 < b) :
    QuasiReversibleRates (fun x : Q.State => b * Q.eqWeight x.1) Q.rate
      (fun x k => refinedCount x.1 k) := by
  classical
  refine qr_generic Q hQ (fun c z => (c, z)) (fun x k => refinedCount x.1 k) (fun x k => ?_) b hb
    (fun k => Q.ν k.1 * Q.p k.1 k.2) (fun k => ?_)
  · unfold refinedCount cnt
    apply List.countP_congr
    intro e _
    simp [Prod.ext_iff]
  · by_cases hpos : 0 < Q.ν k.1 * Q.p k.1 k.2
    · let a : E Q (fun c z => (c, z)) k := ⟨k, hpos, rfl⟩
      exact hasSum_single (f := fun cz : E Q (fun c z => (c, z)) k =>
        Q.ν cz.1.1 * Q.p cz.1.1 cz.1.2) a (fun b' hb' =>
          absurd (Subtype.ext (show b'.1 = k from b'.2.2)) hb')
    · have hz : Q.ν k.1 * Q.p k.1 k.2 = 0 :=
        le_antisymm (not_lt.mp hpos) (mul_nonneg (hQ.ν_nonneg _) (hQ.p_nonneg _ _))
      have : IsEmpty (E Q (fun c z => (c, z)) k) := ⟨fun cz => hpos (by
        have h : cz.1 = k := cz.2.2
        rw [← h]
        exact cz.2.1)⟩
      rw [hz]
      exact hasSum_empty

end P2M0cffQR

open KellyReversibility.Symmetric in
open Classical in
theorem solution {C Z : Type*} [Countable C] [Countable Z]
    (Q : SymmetricQueue C Z) (hQ : Q.IsValid)
    (hmean : ∀ c, Summable (fun z => Q.p c z * (Q.w c z : ℝ) * Q.d c z))
    (hload : Summable (fun c => Q.ν c * Q.meanReq c))
    (b : ℝ) (hb : HasSum (fun n : ℕ => Q.normTerm Q.load n) b⁻¹) :
    let π : Q.State → ℝ := fun x => b * Q.eqWeight x.1
    IsEquilibriumDistribution π Q.rate ∧
    (∀ n : ℕ, HasSum (fun x : Q.State => if x.1.length = n then π x else 0)
        (b * Q.normTerm Q.load n)) ∧
    (∀ cs : List C, HasSum (fun x : Q.State => if x.1.map Customer.cls = cs then π x else 0)
        (b * Q.normTerm Q.load cs.length *
          (cs.map fun c => Q.ν c * Q.meanReq c / Q.load).prod)) ∧
    QuasiReversibleRates π Q.rate (fun x c => classCount x.1 c) ∧
    QuasiReversibleRates π Q.rate (fun x k => refinedCount x.1 k) := by
  intro π
  have hnn : ∀ n, 0 ≤ Q.normTerm Q.load n := by
    intro n
    have hl : 0 ≤ Q.load := tsum_nonneg fun c =>
      mul_nonneg (hQ.ν_nonneg c) (tsum_nonneg fun z =>
        mul_nonneg (mul_nonneg (hQ.p_nonneg c z) (Nat.cast_nonneg _)) (hQ.d_pos c z).le)
    exact div_nonneg (pow_nonneg hl n)
      (Finset.prod_nonneg fun l hl' => (hQ.φ_pos l (by simp at hl'; omega)).le)
  have hb0 : 0 < b := by
    have h1 : Q.normTerm Q.load 0 ≤ b⁻¹ :=
      le_hasSum hb 0 (fun n _ => hnn n)
    have h0 : Q.normTerm Q.load 0 = 1 := by simp [SymmetricQueue.normTerm]
    rw [h0] at h1
    exact inv_pos.mp (lt_of_lt_of_le one_pos h1)
  exact ⟨eq_3_18_equilibrium Q hQ hmean hload b hb,
    fun n => P2M0cff.length_marginal Q hQ hmean hload b n,
    fun cs => P2M0cff.class_sequence_marginal Q hQ hmean hload b cs,
    P2M0cffQR.quasiReversible_class Q hQ b hb0,
    P2M0cffQR.quasiReversible_refined Q hQ b hb0⟩
