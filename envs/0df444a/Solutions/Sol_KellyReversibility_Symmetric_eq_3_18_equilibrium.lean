-- Prove2me | solution 1 for KellyReversibility.Symmetric.eq_3_18_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:03:03.415989+00:00
-- url     : https://prove2.me/submissions/fd59c6f0-1e3f-497a-bb74-189ff2269209

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Symmetric_SymmetricQueue
import Definitions.Def_KellyReversibility_Symmetric_Equilibrium

set_option autoImplicit false

namespace P2M35b

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

lemma eqWeight_eq0 (Q : SymmetricQueue C Z) (l : List (Customer C Z)) :
    Q.eqWeight l = (l.map fun e => Q.ν e.cls * Q.p e.cls e.ref * Q.d e.cls e.ref).prod /
      ∏ k ∈ Finset.Icc 1 l.length, Q.φ k := by
  unfold SymmetricQueue.eqWeight
  rw [Finset.prod_div_distrib, prod_phi Q.φ l.length,
    ← prod_get (fun e => Q.ν e.cls * Q.p e.cls e.ref * Q.d e.cls e.ref) l]

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
    · rw [eqWeight_eq0, h]
      ring
    · simp
  have hv : b * Q.normTerm Q.load n = (b / ∏ k ∈ Finset.Icc 1 n, Q.φ k) * Q.load ^ n := by
    simp only [SymmetricQueue.normTerm]
    ring
  rw [hf, hv]
  exact this


/-- the weight factor `ν p d` of one customer -/
noncomputable def gw (Q : SymmetricQueue C Z) (e : Customer C Z) : ℝ :=
  Q.ν e.cls * Q.p e.cls e.ref * Q.d e.cls e.ref

lemma eqWeight_eq (Q : SymmetricQueue C Z) (l : List (Customer C Z)) :
    Q.eqWeight l = (l.map (gw Q)).prod / ∏ k ∈ Finset.Icc 1 l.length, Q.φ k := by
  unfold SymmetricQueue.eqWeight
  rw [Finset.prod_div_distrib, prod_phi Q.φ l.length, ← prod_get (gw Q) l]
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
    Q.eqWeight (l.insertIdx i e) = Q.eqWeight l * gw Q e / Q.φ (l.length + 1) := by
  rw [eqWeight_eq, eqWeight_eq, List.length_insertIdx_of_le_length hi,
    ((List.perm_insertIdx e l hi).map (gw Q)).prod_eq, List.map_cons, List.prod_cons,
    Finset.prod_Icc_succ_top (by omega)]
  ring

lemma eqWeight_set (Q : SymmetricQueue C Z) (l : List (Customer C Z)) (i : ℕ)
    (hi : i < l.length) (e : Customer C Z) (he : gw Q e = gw Q l[i]) :
    Q.eqWeight (l.set i e) = Q.eqWeight l := by
  rw [eqWeight_eq, eqWeight_eq, List.length_set, List.map_set, he]
  have h2 : i < (l.map (gw Q)).length := by simpa using hi
  have : gw Q l[i] = (l.map (gw Q))[i] := (List.getElem_map (gw Q)).symm
  rw [this, List.set_getElem_self h2]

lemma gamma_sum (Q : SymmetricQueue C Z) (hQ : Q.IsValid) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), Q.γ (j + 1) (n + 1) = 1 := by
  rw [← hQ.γ_sum (n + 1) (Nat.succ_pos n), Finset.range_eq_Ico,
    Finset.sum_Ico_add' (fun l => Q.γ l (n + 1)) 0 (n + 1) 1]
  congr 1

/-- admissible refined classes -/
def E (Q : SymmetricQueue C Z) : Type _ := {cz : C × Z // 0 < Q.ν cz.1 * Q.p cz.1 cz.2}

/-- insert a valid customer into a state -/
def ins (Q : SymmetricQueue C Z) (x : Q.State) (i : ℕ) (hi : i ≤ x.1.length) (e : Customer C Z)
    (he : Q.ValidCustomer e) : Q.State :=
  Subtype.mk (p := fun l : List (Customer C Z) => ∀ e ∈ l, Q.ValidCustomer e)
    (x.1.insertIdx i e) (by
      intro e' he'
      rcases List.mem_cons.mp ((List.perm_insertIdx e x.1 hi).mem_iff.mp he') with h | h
      · rw [h]; exact he
      · exact x.2 e' h)

lemma ins_inj (Q : SymmetricQueue C Z) (x : Q.State) (i : ℕ) (hi : i ≤ x.1.length)
    (e1 e2 : Customer C Z)
    (h1 : Q.ValidCustomer e1) (h2 : Q.ValidCustomer e2)
    (h : ins Q x i hi e1 h1 = ins Q x i hi e2 h2) : e1 = e2 := by
  have h' : x.1.insertIdx i e1 = x.1.insertIdx i e2 := congrArg Subtype.val h
  have := congrArg (fun l => l[i]?) h'
  simp only [List.getElem?_insertIdx_self, if_pos hi, Option.some.injEq] at this
  exact this

lemma hasSum_Lam (Q : SymmetricQueue C Z) (hQ : Q.IsValid) :
    HasSum (fun cz : E Q => Q.ν cz.1.1 * Q.p cz.1.1 cz.1.2) (∑' c, Q.ν c) := by
  let f : (Σ _ : C, Z) → ℝ := fun s => Q.ν s.1 * Q.p s.1 s.2
  have hfib : ∀ c, HasSum (fun z => f ⟨c, z⟩) (Q.ν c) := by
    intro c
    have h0 := (hQ.p_hasSum c).mul_left (Q.ν c)
    rw [mul_one] at h0
    exact h0
  have hf0 : ∀ s, 0 ≤ f s := fun s => mul_nonneg (hQ.ν_nonneg _) (hQ.p_nonneg _ _)
  have hsum : Summable f := by
    rw [summable_sigma_of_nonneg hf0]
    exact ⟨fun c => (hfib c).summable,
      hQ.ν_summable.congr (fun c => ((hfib c).tsum_eq).symm)⟩
  have htot : HasSum f (∑' c, Q.ν c) :=
    HasSum.sigma_of_hasSum hQ.ν_summable.hasSum hfib hsum
  let j : E Q → (Σ _ : C, Z) := fun cz => ⟨cz.1.1, cz.1.2⟩
  have hj : Function.Injective j := by
    rintro ⟨⟨c1, z1⟩, h1⟩ ⟨⟨c2, z2⟩, h2⟩ h
    simp only [j, Sigma.mk.inj_iff, heq_eq_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  have hcond : ∀ s, s ∉ Set.range j → f s = 0 := by
    rintro ⟨c, z⟩ hs
    rcases (hf0 ⟨c, z⟩).lt_or_eq with h' | h'
    · exact absurd ⟨⟨(c, z), h'⟩, rfl⟩ hs
    · exact h'.symm
  exact (hj.hasSum_iff hcond).mpr htot

open Classical in
/-- arrival term `j` of `arrivalRate x y` -/
noncomputable def A (Q : SymmetricQueue C Z) (x : Q.State) (j : ℕ) (y : Q.State) : ℝ :=
  match y.1[j]? with
  | some e =>
      if e.stage = 1 ∧ x.1.insertIdx j e = y.1 then
        Q.ν e.cls * Q.p e.cls e.ref * Q.γ (j + 1) (x.1.length + 1)
      else 0
  | none => 0

lemma arrivalRate_eq (Q : SymmetricQueue C Z) (x y : Q.State) :
    Q.arrivalRate x.1 y.1 = ∑ j ∈ Finset.range (x.1.length + 1), A Q x j y := rfl

open Classical in
/-- departure term `i` (used through the reversed flow) -/
noncomputable def B (Q : SymmetricQueue C Z) (x : Q.State) (i : ℕ) (y : Q.State) : ℝ :=
  match y.1[i]? with
  | some e =>
      if e.stage = Q.w e.cls e.ref ∧ y.1.eraseIdx i = x.1 then
        Q.ν e.cls * Q.p e.cls e.ref * Q.γ (i + 1) (x.1.length + 1)
      else 0
  | none => 0

open Classical in
/-- service term `i` of `serviceRate x y` -/
noncomputable def S (Q : SymmetricQueue C Z) (x : Q.State) (i : ℕ) (y : Q.State) : ℝ :=
  match x.1[i]? with
  | some e =>
      if (e.stage < Q.w e.cls e.ref ∧
            x.1.set i { cls := e.cls, ref := e.ref, stage := e.stage + 1 } = y.1) ∨
          (e.stage = Q.w e.cls e.ref ∧ x.1.eraseIdx i = y.1) then
        Q.φ x.1.length * Q.γ (i + 1) x.1.length / Q.d e.cls e.ref
      else 0
  | none => 0

lemma serviceRate_eq (Q : SymmetricQueue C Z) (x y : Q.State) :
    Q.serviceRate x.1 y.1 = ∑ i ∈ Finset.range x.1.length, S Q x i y := rfl

open Classical in
noncomputable def SU (Q : SymmetricQueue C Z) (x : Q.State) (i : ℕ) (y : Q.State) : ℝ :=
  match x.1[i]? with
  | some e =>
      if e.stage < Q.w e.cls e.ref ∧
            x.1.set i { cls := e.cls, ref := e.ref, stage := e.stage + 1 } = y.1 then
        Q.φ x.1.length * Q.γ (i + 1) x.1.length / Q.d e.cls e.ref
      else 0
  | none => 0

open Classical in
noncomputable def SV (Q : SymmetricQueue C Z) (x : Q.State) (i : ℕ) (y : Q.State) : ℝ :=
  match x.1[i]? with
  | some e =>
      if e.stage = Q.w e.cls e.ref ∧ x.1.eraseIdx i = y.1 then
        Q.φ x.1.length * Q.γ (i + 1) x.1.length / Q.d e.cls e.ref
      else 0
  | none => 0

lemma S_split (Q : SymmetricQueue C Z) (x : Q.State) (i : ℕ) (y : Q.State) :
    S Q x i y = SU Q x i y + SV Q x i y := by
  unfold S SU SV
  cases h : x.1[i]? with
  | none => simp
  | some e =>
    dsimp only
    by_cases h1 : e.stage < Q.w e.cls e.ref ∧
        x.1.set i { cls := e.cls, ref := e.ref, stage := e.stage + 1 } = y.1
    · have h2 : ¬ (e.stage = Q.w e.cls e.ref ∧ x.1.eraseIdx i = y.1) := by
        rintro ⟨h2, -⟩
        have := h1.1
        omega
      rw [if_pos (Or.inl h1), if_pos h1, if_neg h2, add_zero]
    · by_cases h2 : e.stage = Q.w e.cls e.ref ∧ x.1.eraseIdx i = y.1
      · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2, zero_add]
      · rw [if_neg (by tauto), if_neg h1, if_neg h2, add_zero]

/-- the service-completion rate of position `i` of `x` -/
noncomputable def sv (Q : SymmetricQueue C Z) (x : Q.State) (i : ℕ) : ℝ :=
  match x.1[i]? with
  | some e => Q.φ x.1.length * Q.γ (i + 1) x.1.length / Q.d e.cls e.ref
  | none => 0

lemma hasSum_A (Q : SymmetricQueue C Z) (hQ : Q.IsValid) (Λ : ℝ)
    (hΛ : HasSum (fun cz : E Q => Q.ν cz.1.1 * Q.p cz.1.1 cz.1.2) Λ)
    (x : Q.State) (j : ℕ) (hj : j ≤ x.1.length) :
    HasSum (A Q x j) (Λ * Q.γ (j + 1) (x.1.length + 1)) := by
  let ι : E Q → Q.State := fun cz =>
    ins Q x j hj ⟨cz.1.1, cz.1.2, 1⟩ ⟨cz.2, le_rfl, hQ.w_pos _ _⟩
  have hι : Function.Injective ι := by
    intro a b h
    have := ins_inj Q x j hj _ _ _ _ h
    simp only [Customer.mk.injEq, and_true] at this
    exact Subtype.ext (Prod.ext this.1 this.2)
  have hcond : ∀ y : Q.State, y ∉ Set.range ι → A Q x j y = 0 := by
    intro y hy
    unfold A
    cases h : y.1[j]? with
    | none => rfl
    | some e =>
      dsimp only
      rw [if_neg]
      rintro ⟨hs, hins⟩
      have he : Q.ValidCustomer e := y.2 e (List.mem_of_getElem? h)
      refine hy ⟨⟨(e.cls, e.ref), he.1⟩, Subtype.ext ?_⟩
      show x.1.insertIdx j ⟨e.cls, e.ref, 1⟩ = y.1
      rw [← hins, ← hs]
  rw [← hι.hasSum_iff hcond]
  have key := hΛ.mul_right (Q.γ (j + 1) (x.1.length + 1))
  have hf : (A Q x j ∘ ι) = fun cz : E Q =>
      Q.ν cz.1.1 * Q.p cz.1.1 cz.1.2 * Q.γ (j + 1) (x.1.length + 1) := by
    funext cz
    show A Q x j (ins Q x j hj _ _) = _
    unfold A ins
    simp only [List.getElem?_insertIdx_self, if_pos hj]
    rw [if_pos (by simp)]
  rw [hf]
  exact key

lemma hasSum_B (Q : SymmetricQueue C Z) (hQ : Q.IsValid) (Λ : ℝ)
    (hΛ : HasSum (fun cz : E Q => Q.ν cz.1.1 * Q.p cz.1.1 cz.1.2) Λ)
    (x : Q.State) (i : ℕ) (hi : i ≤ x.1.length) :
    HasSum (B Q x i) (Λ * Q.γ (i + 1) (x.1.length + 1)) := by
  let ι : E Q → Q.State := fun cz =>
    ins Q x i hi ⟨cz.1.1, cz.1.2, Q.w cz.1.1 cz.1.2⟩ ⟨cz.2, hQ.w_pos _ _, le_rfl⟩
  have hι : Function.Injective ι := by
    intro a b h
    have := ins_inj Q x i hi _ _ _ _ h
    simp only [Customer.mk.injEq] at this
    exact Subtype.ext (Prod.ext this.1 this.2.1)
  have hcond : ∀ y : Q.State, y ∉ Set.range ι → B Q x i y = 0 := by
    intro y hy
    unfold B
    cases h : y.1[i]? with
    | none => rfl
    | some e =>
      dsimp only
      rw [if_neg]
      rintro ⟨hs, herase⟩
      have he : Q.ValidCustomer e := y.2 e (List.mem_of_getElem? h)
      obtain ⟨hi', he'⟩ := List.getElem?_eq_some_iff.mp h
      refine hy ⟨⟨(e.cls, e.ref), he.1⟩, Subtype.ext ?_⟩
      show x.1.insertIdx i ⟨e.cls, e.ref, Q.w e.cls e.ref⟩ = y.1
      rw [← herase, ← hs]
      have : (⟨e.cls, e.ref, e.stage⟩ : Customer C Z) = y.1[i] := he'.symm
      rw [this]
      exact List.insertIdx_eraseIdx_getElem hi'
  rw [← hι.hasSum_iff hcond]
  have key := hΛ.mul_right (Q.γ (i + 1) (x.1.length + 1))
  have hf : (B Q x i ∘ ι) = fun cz : E Q =>
      Q.ν cz.1.1 * Q.p cz.1.1 cz.1.2 * Q.γ (i + 1) (x.1.length + 1) := by
    funext cz
    show B Q x i (ins Q x i hi _ _) = _
    unfold B ins
    simp only [List.getElem?_insertIdx_self, if_pos hi]
    rw [if_pos (by simp [List.eraseIdx_insertIdx_self])]
  rw [hf]
  exact key

lemma hasSum_S (Q : SymmetricQueue C Z) (x : Q.State) (i : ℕ) (hi : i < x.1.length) :
    HasSum (S Q x i) (sv Q x i) := by
  have he : Q.ValidCustomer x.1[i] := x.2 _ (List.getElem_mem hi)
  have hsv : sv Q x i = Q.φ x.1.length * Q.γ (i + 1) x.1.length / Q.d x.1[i].cls x.1[i].ref := by
    simp only [sv, List.getElem?_eq_getElem hi]
  by_cases hlt : x.1[i].stage < Q.w x.1[i].cls x.1[i].ref
  · let y0 : Q.State := Subtype.mk (p := fun l : List (Customer C Z) => ∀ e ∈ l, Q.ValidCustomer e)
      (x.1.set i { cls := x.1[i].cls, ref := x.1[i].ref, stage := x.1[i].stage + 1 }) (by
        intro e' he'
        rcases List.mem_or_eq_of_mem_set he' with h | h
        · exact x.2 e' h
        · rw [h]
          refine ⟨he.1, ?_, ?_⟩
          · show 1 ≤ x.1[i].stage + 1
            omega
          · show x.1[i].stage + 1 ≤ Q.w x.1[i].cls x.1[i].ref
            omega)
    have h0 : ∀ y, y ≠ y0 → S Q x i y = 0 := by
      intro y hy
      simp only [S, List.getElem?_eq_getElem hi]
      rw [if_neg]
      rintro (⟨-, h⟩ | ⟨h1, -⟩)
      · exact hy (Subtype.ext h.symm)
      · omega
    have := hasSum_single y0 h0
    convert this using 1
    rw [hsv]
    simp only [S, List.getElem?_eq_getElem hi]
    rw [if_pos (Or.inl ⟨hlt, rfl⟩)]
  · have heq : x.1[i].stage = Q.w x.1[i].cls x.1[i].ref := by have := he.2.2; omega
    let y0 : Q.State := Subtype.mk (p := fun l : List (Customer C Z) => ∀ e ∈ l, Q.ValidCustomer e)
      (x.1.eraseIdx i) (fun e' he' => x.2 e' ((List.eraseIdx_sublist _ _).subset he'))
    have h0 : ∀ y, y ≠ y0 → S Q x i y = 0 := by
      intro y hy
      simp only [S, List.getElem?_eq_getElem hi]
      rw [if_neg]
      rintro (⟨h1, -⟩ | ⟨-, h⟩)
      · exact hlt h1
      · exact hy (Subtype.ext h.symm)
    have := hasSum_single y0 h0
    convert this using 1
    rw [hsv]
    simp only [S, List.getElem?_eq_getElem hi]
    rw [if_pos (Or.inr ⟨heq, rfl⟩)]

lemma hasSum_out (Q : SymmetricQueue C Z) (hQ : Q.IsValid) (Λ : ℝ)
    (hΛ : HasSum (fun cz : E Q => Q.ν cz.1.1 * Q.p cz.1.1 cz.1.2) Λ) (x : Q.State) :
    HasSum (Q.rate x) (Λ + ∑ i ∈ Finset.range x.1.length, sv Q x i) := by
  have h1 := hasSum_sum (s := Finset.range (x.1.length + 1))
    (fun j hj => hasSum_A Q hQ Λ hΛ x j (by simp only [Finset.mem_range] at hj; omega))
  rw [← Finset.mul_sum, gamma_sum Q hQ, mul_one] at h1
  have h2 := hasSum_sum (s := Finset.range x.1.length)
    (fun i hi => hasSum_S Q x i (Finset.mem_range.mp hi))
  have h3 := h1.add h2
  have hf : Q.rate x = fun y => (∑ j ∈ Finset.range (x.1.length + 1), A Q x j y) +
      ∑ i ∈ Finset.range x.1.length, S Q x i y := by
    funext y
    rfl
  rw [hf]
  exact h3

/-- sums over two ranges agree when the summand vanishes unless the ranges agree -/
lemma range_swap (f : ℕ → ℝ) (m k : ℕ) (h : m ≠ k → ∀ j, f j = 0) :
    ∑ j ∈ Finset.range m, f j = ∑ j ∈ Finset.range k, f j := by
  by_cases hmk : m = k
  · rw [hmk]
  · rw [Finset.sum_eq_zero (fun j _ => h hmk j), Finset.sum_eq_zero (fun j _ => h hmk j)]

lemma A_zero (Q : SymmetricQueue C Z) (x y : Q.State) (h : y.1.length + 1 ≠ x.1.length)
    (j : ℕ) : A Q y j x = 0 := by
  unfold A
  cases hx : x.1[j]? with
  | none => rfl
  | some e =>
    dsimp only
    rw [if_neg]
    rintro ⟨-, hins⟩
    obtain ⟨hj, -⟩ := List.getElem?_eq_some_iff.mp hx
    have hl := congrArg List.length hins
    rw [List.length_insertIdx] at hl
    split_ifs at hl <;> omega

lemma SU_zero (Q : SymmetricQueue C Z) (x y : Q.State) (h : y.1.length ≠ x.1.length)
    (i : ℕ) : SU Q y i x = 0 := by
  unfold SU
  cases hy : y.1[i]? with
  | none => rfl
  | some e =>
    dsimp only
    rw [if_neg]
    rintro ⟨-, hs⟩
    have hl := congrArg List.length hs
    rw [List.length_set] at hl
    exact h hl

lemma SV_zero (Q : SymmetricQueue C Z) (x y : Q.State) (h : y.1.length ≠ x.1.length + 1)
    (i : ℕ) : SV Q y i x = 0 := by
  unfold SV
  cases hy : y.1[i]? with
  | none => rfl
  | some e =>
    dsimp only
    rw [if_neg]
    rintro ⟨-, hs⟩
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp hy
    have hl := congrArg List.length hs
    rw [List.length_eraseIdx, if_pos hi] at hl
    omega

lemma SV_eq_B (Q : SymmetricQueue C Z) (hQ : Q.IsValid) (b : ℝ) (x y : Q.State) (i : ℕ) :
    b * Q.eqWeight y.1 * SV Q y i x = b * Q.eqWeight x.1 * B Q x i y := by
  unfold SV B
  cases h : y.1[i]? with
  | none => simp
  | some e =>
    obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.mp h
    dsimp only
    by_cases hc : y.1[i].stage = Q.w y.1[i].cls y.1[i].ref ∧ y.1.eraseIdx i = x.1
    · rw [if_pos hc, if_pos hc]
      have hins : x.1.insertIdx i y.1[i] = y.1 := by
        rw [← hc.2]; exact List.insertIdx_eraseIdx_getElem hi'
      have hlx := congrArg List.length hc.2
      rw [List.length_eraseIdx, if_pos hi'] at hlx
      have hW := eqWeight_insert Q x.1 i (by omega) y.1[i]
      rw [hins] at hW
      have hly : y.1.length = x.1.length + 1 := by omega
      rw [hW, hly]
      have hφ : Q.φ (x.1.length + 1) ≠ 0 := (hQ.φ_pos _ (Nat.succ_pos _)).ne'
      have hd : Q.d y.1[i].cls y.1[i].ref ≠ 0 := (hQ.d_pos _ _).ne'
      unfold gw
      field_simp
    · rw [if_neg hc, if_neg hc]
      simp

lemma getElem?_set_eq {α : Type*} (l : List α) (i : ℕ) (hi : i < l.length) (a : α) :
    (l.set i a)[i]? = some a := List.getElem?_set_self hi

lemma hasSum_partial (Q : SymmetricQueue C Z) (hQ : Q.IsValid) (b : ℝ) (x : Q.State) (j : ℕ)
    (hj : j < x.1.length) :
    HasSum (fun y : Q.State => b * Q.eqWeight y.1 * A Q y j x + b * Q.eqWeight y.1 * SU Q y j x)
      (b * Q.eqWeight x.1 * sv Q x j) := by
  have he : Q.ValidCustomer x.1[j] := x.2 _ (List.getElem_mem hj)
  have hxj : x.1[j]? = some x.1[j] := List.getElem?_eq_getElem hj
  have hsv : sv Q x j = Q.φ x.1.length * Q.γ (j + 1) x.1.length / Q.d x.1[j].cls x.1[j].ref := by
    simp only [sv, hxj]
  -- if `y.set j e'+ = x` then `x[j]` is `e'` with its stage advanced
  have hstep : ∀ (y : Q.State) (e' : Customer C Z), y.1[j]? = some e' →
      y.1.set j { cls := e'.cls, ref := e'.ref, stage := e'.stage + 1 } = x.1 →
      x.1[j] = { cls := e'.cls, ref := e'.ref, stage := e'.stage + 1 } := by
    intro y e' hy hs
    obtain ⟨hj', -⟩ := List.getElem?_eq_some_iff.mp hy
    have h1 : x.1[j]? = some { cls := e'.cls, ref := e'.ref, stage := e'.stage + 1 } := by
      rw [← hs]; exact getElem?_set_eq _ _ hj' _
    rw [hxj] at h1
    exact Option.some.inj h1
  by_cases hs1 : x.1[j].stage = 1
  · have hSU : ∀ y, SU Q y j x = 0 := by
      intro y
      unfold SU
      cases hy : y.1[j]? with
      | none => rfl
      | some e' =>
        dsimp only
        rw [if_neg]
        rintro ⟨-, hs⟩
        have hv : Q.ValidCustomer e' := y.2 e' (List.mem_of_getElem? hy)
        have := hstep y e' hy hs
        rw [this] at hs1
        have := hv.2.1
        simp only at hs1
        omega
    let y0 : Q.State := Subtype.mk (p := fun l : List (Customer C Z) => ∀ e ∈ l, Q.ValidCustomer e)
      (x.1.eraseIdx j) (fun e' he' => x.2 e' ((List.eraseIdx_sublist _ _).subset he'))
    have hl0 : y0.1.length + 1 = x.1.length := by
      show (x.1.eraseIdx j).length + 1 = _
      rw [List.length_eraseIdx, if_pos hj]
      omega
    have h0 : ∀ y, y ≠ y0 →
        b * Q.eqWeight y.1 * A Q y j x + b * Q.eqWeight y.1 * SU Q y j x = 0 := by
      intro y hy
      rw [hSU y, mul_zero, add_zero]
      simp only [A, hxj]
      rw [if_neg, mul_zero]
      rintro ⟨-, hins⟩
      apply hy
      apply Subtype.ext
      show y.1 = x.1.eraseIdx j
      rw [← hins, List.eraseIdx_insertIdx_self]
    have := hasSum_single y0 h0
    convert this using 1
    rw [hSU y0, mul_zero, add_zero, hsv]
    simp only [A, hxj]
    have hins : (x.1.eraseIdx j).insertIdx j x.1[j] = x.1 := List.insertIdx_eraseIdx_getElem hj
    rw [if_pos ⟨hs1, hins⟩]
    have hW := eqWeight_insert Q (x.1.eraseIdx j) j (by
      rw [List.length_eraseIdx, if_pos hj]; omega) x.1[j]
    rw [hins] at hW
    have hl0' : (x.1.eraseIdx j).length + 1 = x.1.length := hl0
    rw [hl0'] at hW
    show b * Q.eqWeight x.1 * _ = b * Q.eqWeight (x.1.eraseIdx j) * _
    rw [hW, hl0']
    have hφ : Q.φ x.1.length ≠ 0 := (hQ.φ_pos _ (by omega)).ne'
    have hd : Q.d x.1[j].cls x.1[j].ref ≠ 0 := (hQ.d_pos _ _).ne'
    unfold gw
    field_simp
  · have hs2 : 2 ≤ x.1[j].stage := by have := he.2.1; omega
    have hA : ∀ y, A Q y j x = 0 := by
      intro y
      simp only [A, hxj]
      rw [if_neg]
      rintro ⟨h, -⟩
      exact hs1 h
    let em : Customer C Z := { cls := x.1[j].cls, ref := x.1[j].ref, stage := x.1[j].stage - 1 }
    let y0 : Q.State := Subtype.mk (p := fun l : List (Customer C Z) => ∀ e ∈ l, Q.ValidCustomer e)
      (x.1.set j em) (by
        intro e' he'
        rcases List.mem_or_eq_of_mem_set he' with h | h
        · exact x.2 e' h
        · rw [h]; exact ⟨he.1, by show 1 ≤ x.1[j].stage - 1; omega,
            by show x.1[j].stage - 1 ≤ Q.w x.1[j].cls x.1[j].ref; have := he.2.2; omega⟩)
    have hem : { cls := em.cls, ref := em.ref, stage := em.stage + 1 } = x.1[j] := by
      show ({ cls := x.1[j].cls, ref := x.1[j].ref, stage := x.1[j].stage - 1 + 1 } : Customer C Z)
        = x.1[j]
      rw [Nat.sub_add_cancel (by omega : 1 ≤ x.1[j].stage)]
    have h0 : ∀ y, y ≠ y0 →
        b * Q.eqWeight y.1 * A Q y j x + b * Q.eqWeight y.1 * SU Q y j x = 0 := by
      intro y hy
      rw [hA y, mul_zero, zero_add]
      unfold SU
      cases hy' : y.1[j]? with
      | none => simp
      | some e' =>
        dsimp only
        rw [if_neg, mul_zero]
        rintro ⟨-, hs⟩
        apply hy
        apply Subtype.ext
        have hx := hstep y e' hy' hs
        obtain ⟨hj', he'⟩ := List.getElem?_eq_some_iff.mp hy'
        have hee : em = e' := by
          show ({ cls := x.1[j].cls, ref := x.1[j].ref, stage := x.1[j].stage - 1 } : Customer C Z)
            = e'
          rw [hx]
          simp
        show y.1 = x.1.set j em
        rw [hee, ← hs, List.set_set, ← he', List.set_getElem_self hj']
    have := hasSum_single y0 h0
    convert this using 1
    rw [hA y0, mul_zero, zero_add, hsv]
    have hlen : y0.1.length = x.1.length := List.length_set
    have hy0 : y0.1[j]? = some em := getElem?_set_eq _ _ hj _
    simp only [SU, hy0]
    have hcond : em.stage < Q.w em.cls em.ref ∧
        y0.1.set j { cls := em.cls, ref := em.ref, stage := em.stage + 1 } = x.1 := by
      refine ⟨?_, ?_⟩
      · show x.1[j].stage - 1 < Q.w x.1[j].cls x.1[j].ref
        have := he.2.2
        omega
      · show (x.1.set j em).set j _ = x.1
        rw [List.set_set, hem, List.set_getElem_self hj]
    rw [if_pos hcond, hlen]
    have hW : Q.eqWeight y0.1 = Q.eqWeight x.1 := eqWeight_set Q x.1 j hj em (by
      simp only [gw, em])
    rw [hW]

lemma hasSum_in (Q : SymmetricQueue C Z) (hQ : Q.IsValid) (Λ : ℝ)
    (hΛ : HasSum (fun cz : E Q => Q.ν cz.1.1 * Q.p cz.1.1 cz.1.2) Λ) (b : ℝ) (x : Q.State) :
    HasSum (fun y : Q.State => b * Q.eqWeight y.1 * Q.rate y x)
      (b * Q.eqWeight x.1 * (Λ + ∑ i ∈ Finset.range x.1.length, sv Q x i)) := by
  have h1 := hasSum_sum (s := Finset.range x.1.length)
    (fun j hj => hasSum_partial Q hQ b x j (Finset.mem_range.mp hj))
  have h2 := hasSum_sum (s := Finset.range (x.1.length + 1))
    (fun i hi => (hasSum_B Q hQ Λ hΛ x i
      (by simp only [Finset.mem_range] at hi; omega)).mul_left (b * Q.eqWeight x.1))
  rw [← Finset.mul_sum, ← Finset.mul_sum, gamma_sum Q hQ, mul_one] at h2
  rw [← Finset.mul_sum] at h1
  have h3 := h1.add h2
  have hv : b * Q.eqWeight x.1 * (Λ + ∑ i ∈ Finset.range x.1.length, sv Q x i) =
      b * Q.eqWeight x.1 * ∑ i ∈ Finset.range x.1.length, sv Q x i + b * Q.eqWeight x.1 * Λ := by
    ring
  have hf : (fun y : Q.State => b * Q.eqWeight y.1 * Q.rate y x) = fun y =>
      (∑ j ∈ Finset.range x.1.length,
        (b * Q.eqWeight y.1 * A Q y j x + b * Q.eqWeight y.1 * SU Q y j x)) +
      ∑ i ∈ Finset.range (x.1.length + 1), b * Q.eqWeight x.1 * B Q x i y := by
    funext y
    have ha : Q.arrivalRate y.1 x.1 = ∑ j ∈ Finset.range x.1.length, A Q y j x := by
      rw [arrivalRate_eq]
      exact range_swap _ _ _ (fun h j => A_zero Q x y h j)
    have hs : Q.serviceRate y.1 x.1 = ∑ i ∈ Finset.range x.1.length, SU Q y i x +
        ∑ i ∈ Finset.range (x.1.length + 1), SV Q y i x := by
      rw [serviceRate_eq, Finset.sum_congr rfl (fun i _ => S_split Q y i x),
        Finset.sum_add_distrib]
      rw [range_swap (fun i => SU Q y i x) _ x.1.length (fun h j => SU_zero Q x y h j),
        range_swap (fun i => SV Q y i x) _ (x.1.length + 1) (fun h j => SV_zero Q x y h j)]
    show b * Q.eqWeight y.1 * (Q.arrivalRate y.1 x.1 + Q.serviceRate y.1 x.1) = _
    rw [ha, hs, Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun i _ => (SV_eq_B Q hQ b x y i).symm)]
    rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    ring
  rw [hf, hv]
  exact h3

lemma b_pos (Q : SymmetricQueue C Z) (hQ : Q.IsValid) (b : ℝ)
    (hb : HasSum (fun n : ℕ => Q.normTerm Q.load n) b⁻¹) : 0 < b := by
  have hload : 0 ≤ Q.load :=
    tsum_nonneg fun c => mul_nonneg (hQ.ν_nonneg c) (meanReq_nonneg Q hQ c)
  have hnn : ∀ n, 0 ≤ Q.normTerm Q.load n := by
    intro n
    unfold SymmetricQueue.normTerm
    apply div_nonneg (pow_nonneg hload n)
    apply Finset.prod_nonneg
    intro l hl
    exact (hQ.φ_pos l (by simp only [Finset.mem_Icc] at hl; omega)).le
  have h0 : Q.normTerm Q.load 0 ≤ b⁻¹ := le_hasSum hb 0 (fun n _ => hnn n)
  have h1 : Q.normTerm Q.load 0 = 1 := by simp [SymmetricQueue.normTerm]
  rw [h1] at h0
  exact inv_pos.mp (lt_of_lt_of_le one_pos h0)

lemma hasSum_total {C Z : Type*} [Countable C] [Countable Z]
    (Q : SymmetricQueue C Z) (hQ : Q.IsValid)
    (hmean : ∀ c, Summable (fun z => Q.p c z * (Q.w c z : ℝ) * Q.d c z))
    (hload : Summable (fun c => Q.ν c * Q.meanReq c))
    (b : ℝ) (hb : HasSum (fun n : ℕ => Q.normTerm Q.load n) b⁻¹) :
    HasSum (fun x : Q.State => b * Q.eqWeight x.1) 1 := by
  have hbpos := b_pos Q hQ b hb
  let f : Q.State → ℝ := fun x => b * Q.eqWeight x.1
  have hf0 : ∀ x, 0 ≤ f x := fun x => (mul_pos hbpos (eqWeight_pos Q hQ x)).le
  let e := Equiv.sigmaFiberEquiv (fun x : Q.State => x.1.length)
  have hfib : ∀ n : ℕ, HasSum (fun y : {x : Q.State // x.1.length = n} => (f ∘ e) ⟨n, y⟩)
      (b * Q.normTerm Q.load n) := by
    intro n
    have hm := length_marginal Q hQ hmean hload b n
    have hi : (fun x : Q.State => if x.1.length = n then b * Q.eqWeight x.1 else 0) =
        Set.indicator {x : Q.State | x.1.length = n} f := by
      funext x
      simp only [Set.indicator_apply, Set.mem_setOf_eq, f]
    rw [hi, ← hasSum_subtype_iff_indicator] at hm
    exact hm
  have ha : HasSum (fun n : ℕ => b * Q.normTerm Q.load n) 1 := by
    have := hb.mul_left b
    rwa [mul_inv_cancel₀ hbpos.ne'] at this
  have hsum : Summable (f ∘ e) :=
    (summable_sigma_of_nonneg (f := f ∘ e) (fun s => hf0 _)).mpr
      ⟨fun n => (hfib n).summable, ha.summable.congr (fun n => ((hfib n).tsum_eq).symm)⟩
  have := HasSum.sigma_of_hasSum ha hfib hsum
  exact (e.hasSum_iff).mp this

end P2M35b

open KellyReversibility.Symmetric in
theorem solution {C Z : Type*} [Countable C] [Countable Z]
    (Q : SymmetricQueue C Z) (hQ : Q.IsValid)
    (hmean : ∀ c, Summable (fun z => Q.p c z * (Q.w c z : ℝ) * Q.d c z))
    (hload : Summable (fun c => Q.ν c * Q.meanReq c))
    (b : ℝ) (hb : HasSum (fun n : ℕ => Q.normTerm Q.load n) b⁻¹) :
    IsEquilibriumDistribution (fun x : Q.State => b * Q.eqWeight x.1) Q.rate := by
  have hbpos := P2M35b.b_pos Q hQ b hb
  have hΛ := P2M35b.hasSum_Lam Q hQ
  refine ⟨fun x => mul_pos hbpos (P2M35b.eqWeight_pos Q hQ x),
    P2M35b.hasSum_total Q hQ hmean hload b hb,
    fun x => (P2M35b.hasSum_out Q hQ _ hΛ x).summable,
    fun x => (P2M35b.hasSum_in Q hQ _ hΛ b x).summable, ?_⟩
  intro x
  beta_reduce
  rw [(P2M35b.hasSum_out Q hQ _ hΛ x).tsum_eq, (P2M35b.hasSum_in Q hQ _ hΛ b x).tsum_eq]
