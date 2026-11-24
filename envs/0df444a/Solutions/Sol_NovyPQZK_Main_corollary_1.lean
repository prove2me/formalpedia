-- Prove2me | solution 1 for NovyPQZK.Main.corollary_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T14:38:46.615252+00:00
-- url     : https://prove2.me/submissions/d0d92c59-1c79-477e-aabd-822fe562fcef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NovyPQZK_Main_Novy
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Theorems.Thm_NovyPQZK_Main_lemma_4
import Theorems.Thm_NovyPQZK_Main_lemma_5

/-! Boolean-stack simulation of a TM2 machine (copied from the accepted proof of
`QuantumMaxCutEnergy.tm2_to_boolean_stacks`), used to run `π` inside composed programs. -/
open scoped BigOperators

namespace QMCBoolSim
open Turing Function OAI.MetricKMedian.Binary

section Sim
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- Boolean statements over the extended state. -/
abbrev St (K Λ σ : Type) := TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)

/-- Push the first `n` bits of `g v`, so that bit `0` ends on top. -/
def pushAt (k : K) (g : σ × Option Bool → List Bool) : ℕ → St K Λ σ → St K Λ σ
  | 0, q => q
  | n + 1, q => .push k (fun v => (g v).getD n false) (pushAt k g n q)

theorem pushAt_spec (k : K) (g : σ × Option Bool → List Bool) (n : ℕ) (q : St K Λ σ)
    (v : σ × Option Bool) (s : K → List Bool) (hn : n ≤ (g v).length) :
    TM2.stepAux (pushAt k g n q) v s = TM2.stepAux q v (update s k ((g v).take n ++ s k)) := by
  induction n generalizing s with
  | zero => simp [pushAt]
  | succ n ih =>
      simp only [pushAt, TM2.stepAux]
      rw [ih _ (by omega)]
      have hlt : n < (g v).length := by omega
      simp only [update_self, update_idem]
      congr 2
      rw [List.getD_eq_getElem _ _ hlt, List.take_succ_eq_append_getElem hlt]
      simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- Read `n` bits from `k`, remembering them in the control flow. -/
def readTree (k : K) : ℕ → (List Bool → St K Λ σ) → St K Λ σ → St K Λ σ
  | 0, cont, _ => cont []
  | n + 1, cont, e =>
      .pop k (fun v x => (v.1, x))
        (.branch (fun v => v.2.isSome)
          (.branch (fun v => v.2 == some true)
            (readTree k n (fun l => cont (true :: l)) e)
            (readTree k n (fun l => cont (false :: l)) e))
          e)

theorem readTree_spec (k : K) (l : List Bool) (cont : List Bool → St K Λ σ) (e : St K Λ σ)
    (v : σ) (b : Option Bool) (s : K → List Bool) (rest : List Bool) (hs : s k = l ++ rest) :
    ∃ b', TM2.stepAux (readTree k l.length cont e) (v, b) s
      = TM2.stepAux (cont l) (v, b') (update s k rest) := by
  induction l generalizing cont b s with
  | nil =>
      refine ⟨b, ?_⟩
      have : update s k rest = s := by
        have : rest = s k := by simpa using hs.symm
        rw [this]; simp
      rw [this]; rfl
  | cons x l ih =>
      have hs' : s k = x :: (l ++ rest) := by simpa using hs
      cases x with
      | true =>
          obtain ⟨b', hb⟩ := ih (fun l => cont (true :: l)) (some true)
            (update s k (l ++ rest)) (by simp)
          refine ⟨b', ?_⟩
          simp only [update_idem] at hb
          simpa [List.length_cons, readTree, TM2.stepAux, hs'] using hb
      | false =>
          obtain ⟨b', hb⟩ := ih (fun l => cont (false :: l)) (some false)
            (update s k (l ++ rest)) (by simp)
          refine ⟨b', ?_⟩
          simp only [update_idem] at hb
          simpa [List.length_cons, readTree, TM2.stepAux, hs'] using hb

theorem readTree_empty (k : K) (n : ℕ) (cont : List Bool → St K Λ σ) (e : St K Λ σ)
    (v : σ) (b : Option Bool) (s : K → List Bool) (hs : s k = []) :
    TM2.stepAux (readTree k (n + 1) cont e) (v, b) s = TM2.stepAux e (v, none) s := by
  have : update s k [] = s := by rw [← hs]; simp
  simp [readTree, TM2.stepAux, hs, this]

/-- The symbols pushed by a statement. -/
def syms : TM2.Stmt Γ Λ σ → Set (Σ k, Γ k)
  | .push k f q => Set.range (fun v => (⟨k, f v⟩ : Σ k, Γ k)) ∪ syms q
  | .peek _ _ q => syms q
  | .pop _ _ q => syms q
  | .load _ q => syms q
  | .branch _ q r => syms q ∪ syms r
  | .goto _ => ∅
  | .halt => ∅

theorem syms_finite [Finite σ] (q : TM2.Stmt Γ Λ σ) : (syms q).Finite := by
  induction q with
  | push k f q ih => exact (Set.finite_range _).union ih
  | peek k f q ih => exact ih
  | pop k f q ih => exact ih
  | load f q ih => exact ih
  | branch f q r ihq ihr => exact ihq.union ihr
  | goto f => exact Set.finite_empty
  | halt => exact Set.finite_empty

variable (w : K → ℕ) (c : ∀ k, Γ k → List Bool) (d : ∀ k, List Bool → Option (Γ k))

/-- Translate a statement to Boolean stacks. -/
def tr : TM2.Stmt Γ Λ σ → St K Λ σ
  | .push k f q => pushAt k (fun v => c k (f v.1)) (w k) (tr q)
  | .peek k f q =>
      readTree k (w k)
        (fun l => pushAt k (fun _ => l) (w k) (.load (fun v => (f v.1 (d k l), none)) (tr q)))
        (.load (fun v => (f v.1 none, none)) (tr q))
  | .pop k f q =>
      readTree k (w k)
        (fun l => .load (fun v => (f v.1 (d k l), none)) (tr q))
        (.load (fun v => (f v.1 none, none)) (tr q))
  | .load f q => .load (fun v => (f v.1, none)) (tr q)
  | .branch f q r => .branch (fun v => f v.1) (tr q) (tr r)
  | .goto f => .goto (fun v => f v.1)
  | .halt => .halt

/-- Encode the stacks. -/
def enc (s : ∀ k, List (Γ k)) : K → List Bool := fun k => (s k).flatMap (c k)

/-- Encode a configuration. -/
def ecfg (a : TM2.Cfg Γ Λ σ) : TM2.Cfg (fun _ : K => Bool) Λ (σ × Option Bool) :=
  ⟨a.l, (a.var, none), enc c a.stk⟩

theorem enc_update (s : ∀ k, List (Γ k)) (k : K) (t : List (Γ k)) :
    enc c (update s k t) = update (enc c s) k (t.flatMap (c k)) := by
  funext j
  by_cases h : j = k
  · subst h; simp [enc]
  · simp [enc, update_of_ne h]

variable (T : Set (Σ k, Γ k))

theorem inv_update {s : ∀ k, List (Γ k)} (hs : ∀ k x, x ∈ s k → (⟨k, x⟩ : Σ k, Γ k) ∈ T)
    {k : K} {t : List (Γ k)} (ht : ∀ x ∈ t, (⟨k, x⟩ : Σ k, Γ k) ∈ T) :
    ∀ j x, x ∈ update s k t j → (⟨j, x⟩ : Σ k, Γ k) ∈ T := by
  intro j x hx
  by_cases h : j = k
  · subst h
    simp only [update_self] at hx
    exact ht x hx
  · rw [update_of_ne h] at hx
    exact hs j x hx

variable (hw : ∀ k, 0 < w k)
  (hlen : ∀ k x, (⟨k, x⟩ : Σ k, Γ k) ∈ T → (c k x).length = w k)
  (hd : ∀ k x, (⟨k, x⟩ : Σ k, Γ k) ∈ T → d k (c k x) = some x)

include hw hlen hd in
theorem tr_spec (q : TM2.Stmt Γ Λ σ) (hq : syms q ⊆ T) (v : σ) (s : ∀ k, List (Γ k))
    (hs : ∀ k x, x ∈ s k → (⟨k, x⟩ : Σ k, Γ k) ∈ T) :
    TM2.stepAux (tr w c d q) (v, none) (enc c s) = ecfg c (TM2.stepAux q v s) ∧
      (∀ k x, x ∈ (TM2.stepAux q v s).stk k → (⟨k, x⟩ : Σ k, Γ k) ∈ T) := by
  induction q generalizing v s with
  | push k f q ih =>
      have hfv : (⟨k, f v⟩ : Σ k, Γ k) ∈ T := hq (Or.inl ⟨v, rfl⟩)
      have hs' := inv_update T hs (k := k) (t := f v :: s k) (by
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hfv
        · exact hs k x hx)
      have ih' := ih (fun _ hx => hq (Or.inr hx)) v _ hs'
      simp only [tr, TM2.stepAux]
      refine ⟨?_, ih'.2⟩
      rw [pushAt_spec _ _ _ _ _ _ (by simp [hlen k _ hfv]), ← ih'.1, enc_update]
      congr 2
      rw [List.take_of_length_le (by simp [hlen k _ hfv])]
      simp [enc]
  | peek k f q ih =>
      have hq' : syms q ⊆ T := hq
      simp only [tr, TM2.stepAux]
      cases hsk : s k with
      | nil =>
          have ih' := ih hq' (f v none) s hs
          refine ⟨?_, ih'.2⟩
          obtain ⟨n, hn⟩ : ∃ n, w k = n + 1 := Nat.exists_eq_succ_of_ne_zero (hw k).ne'
          rw [hn, readTree_empty _ _ _ _ _ _ _ (by simp [enc, hsk])]
          simpa [TM2.stepAux] using ih'.1
      | cons x t =>
          have hx : (⟨k, x⟩ : Σ k, Γ k) ∈ T := hs k x (by simp [hsk])
          have ih' := ih hq' (f v (some x)) s hs
          refine ⟨?_, ih'.2⟩
          obtain ⟨b', hb⟩ := readTree_spec (Λ := Λ) k (c k x)
            (fun l => pushAt k (fun _ => l) (w k) (.load (fun v => (f v.1 (d k l), none))
              (tr w c d q)))
            (.load (fun v => (f v.1 none, none)) (tr w c d q)) v none (enc c s)
            (t.flatMap (c k)) (by simp [enc, hsk])
          rw [hlen k x hx] at hb
          simp only [List.head?_cons]
          rw [hb]
          rw [pushAt_spec _ _ _ _ _ _ (by simp [hlen k _ hx]),
            List.take_of_length_le (by simp [hlen k _ hx])]
          simp only [TM2.stepAux, hd k x hx, update_idem, update_self]
          have : update (enc c s) k (c k x ++ t.flatMap (c k)) = enc c s := by
            have : c k x ++ t.flatMap (c k) = enc c s k := by simp [enc, hsk]
            rw [this]; simp
          rw [this]
          exact ih'.1
  | pop k f q ih =>
      have hq' : syms q ⊆ T := hq
      simp only [tr, TM2.stepAux]
      cases hsk : s k with
      | nil =>
          have hup : update s k [] = s := by rw [← hsk]; simp
          have ih' := ih hq' (f v none) s hs
          simp only [List.tail_nil, List.head?_nil, hup]
          refine ⟨?_, ih'.2⟩
          obtain ⟨n, hn⟩ : ∃ n, w k = n + 1 := Nat.exists_eq_succ_of_ne_zero (hw k).ne'
          rw [hn, readTree_empty _ _ _ _ _ _ _ (by simp [enc, hsk])]
          simpa [TM2.stepAux] using ih'.1
      | cons x t =>
          have hx : (⟨k, x⟩ : Σ k, Γ k) ∈ T := hs k x (by simp [hsk])
          have hs' := inv_update T hs (k := k) (t := t) (by
            intro y hy
            exact hs k y (by simp [hsk, hy]))
          have ih' := ih hq' (f v (some x)) _ hs'
          simp only [List.tail_cons, List.head?_cons]
          refine ⟨?_, ih'.2⟩
          obtain ⟨b', hb⟩ := readTree_spec (Λ := Λ) k (c k x)
            (fun l => .load (fun v => (f v.1 (d k l), none)) (tr w c d q))
            (.load (fun v => (f v.1 none, none)) (tr w c d q)) v none (enc c s)
            (t.flatMap (c k)) (by simp [enc, hsk])
          rw [hlen k x hx] at hb
          rw [hb]
          simp only [TM2.stepAux, hd k x hx]
          rw [← enc_update]
          exact ih'.1
  | load f q ih =>
      have ih' := ih hq (f v) s hs
      simp only [tr, TM2.stepAux]
      exact ih'
  | branch f q r ihq ihr =>
      have hq' : syms q ⊆ T := fun _ hx => hq (Or.inl hx)
      have hr' : syms r ⊆ T := fun _ hx => hq (Or.inr hx)
      simp only [tr, TM2.stepAux]
      cases hf : f v with
      | false => simpa using ihr hr' v s hs
      | true => simpa using ihq hq' v s hs
  | goto f =>
      exact ⟨rfl, hs⟩
  | halt =>
      exact ⟨rfl, hs⟩

include hw hlen hd in
theorem sim_trace (m : Λ → TM2.Stmt Γ Λ σ) (hm : ∀ l, syms (m l) ⊆ T)
    {n : ℕ} {a b : TM2.Cfg Γ Λ σ} (h : Trace (TM2.step m) n a b)
    (ha : ∀ k x, x ∈ a.stk k → (⟨k, x⟩ : Σ k, Γ k) ∈ T) :
    Trace (TM2.step (fun l => tr w c d (m l))) n (ecfg c a) (ecfg c b) := by
  induction h with
  | refl => exact Trace.refl _
  | @cons n a b e hab _ ih =>
      rcases a with ⟨l, v, s⟩
      cases l with
      | none => cases hab
      | some l =>
          have hb : b = TM2.stepAux (m l) v s := (Option.some.inj hab).symm
          subst b
          have hspec := tr_spec w c d T hw hlen hd (m l) (hm l) v s ha
          refine Trace.cons ?_ (ih hspec.2)
          exact congrArg some hspec.1

end Sim

theorem exists_block (A : Type) (S : Set A) (hS : S.Finite) :
    ∃ (w : ℕ) (c : A → List Bool), 0 < w ∧ (∀ x ∈ S, (c x).length = w) ∧ Set.InjOn c S := by
  classical
  haveI : Finite S := hS
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin S
  let i : A → ℕ := fun x => if h : x ∈ S then (e ⟨x, h⟩).val else 0
  refine ⟨n + 1, fun x => List.ofFn (fun j : Fin (n + 1) => decide (j.val = i x)),
    Nat.succ_pos _, fun x _ => by simp, ?_⟩
  intro x hx y hy hxy
  have hxy' := List.ofFn_injective hxy
  have hix : i x < n + 1 := by
    have : i x = (e ⟨x, hx⟩).val := by simp [i, hx]
    have := (e ⟨x, hx⟩).isLt
    omega
  have h1 := congrFun hxy' ⟨i x, hix⟩
  simp only [decide_true] at h1
  have h2 : i x = i y := by simpa using h1.symm
  have h3 : e ⟨x, hx⟩ = e ⟨y, hy⟩ := by
    apply Fin.ext
    simpa [i, hx, hy] using h2
  simpa using e.injective h3

/-- The Boolean machine simulating a bundled machine. -/
abbrev simMachine (tm : FinTM2) (w : tm.K → ℕ) (c : ∀ k, tm.Γ k → List Bool)
    (d : ∀ k, List Bool → Option (tm.Γ k)) : Machine :=
  letI := tm.kDecidableEq
  letI := tm.kFin
  letI := tm.ΛFin
  letI := tm.σFin
  { K := tm.K
    input := tm.k₀
    output := tm.k₁
    Label := tm.Λ
    main := tm.main
    State := tm.σ × Option Bool
    initial := (tm.initialState, none)
    code := fun l => tr w c d (tm.m l) }

theorem simulate (tm : FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) :
    ∃ (M : Machine) (τ : Bool ≃ Bool), ∀ (s t : List Bool) (n : ℕ),
      TM2OutputsInTime tm (s.map e₀.symm) (some (t.map e₁.symm)) n →
        Nonempty (TM2OutputsInTime M.tm s (some (t.map τ)) n) := by
  classical
  letI := tm.kDecidableEq
  letI := tm.kFin
  letI := tm.ΛFin
  letI := tm.σFin
  let T : Set (Σ k, tm.Γ k) :=
    (⋃ l, syms (tm.m l)) ∪ Set.range (fun x : tm.Γ tm.k₀ => (⟨tm.k₀, x⟩ : Σ k, tm.Γ k))
  haveI : Finite (tm.Γ tm.k₀) := Finite.of_equiv Bool e₀.symm
  have hT : T.Finite :=
    (Set.finite_iUnion fun l => syms_finite (tm.m l)).union (Set.finite_range _)
  have key : ∀ k, ∃ (w : ℕ) (c : tm.Γ k → List Bool), 0 < w ∧
      (∀ x, (⟨k, x⟩ : Σ k, tm.Γ k) ∈ T → (c x).length = w) ∧
      (∀ x y, (⟨k, x⟩ : Σ k, tm.Γ k) ∈ T → (⟨k, y⟩ : Σ k, tm.Γ k) ∈ T → c x = c y → x = y) ∧
      (∀ h : k = tm.k₀, ∀ x, c x = [e₀ (h ▸ x)]) ∧
      (k ≠ tm.k₀ → ∀ h : k = tm.k₁, ∀ x, c x = [e₁ (h ▸ x)]) := by
    intro k
    by_cases h0 : k = tm.k₀
    · subst h0
      refine ⟨1, fun x => [e₀ x], one_pos, fun _ _ => rfl, ?_, fun _ _ => rfl, fun h => absurd rfl h⟩
      intro x y _ _ hxy
      exact e₀.injective (by simpa using hxy)
    · by_cases h1 : k = tm.k₁
      · subst h1
        refine ⟨1, fun x => [e₁ x], one_pos, fun _ _ => rfl, ?_, fun h => absurd h h0,
          fun _ _ _ => rfl⟩
        intro x y _ _ hxy
        exact e₁.injective (by simpa using hxy)
      · have hS : {x : tm.Γ k | (⟨k, x⟩ : Σ k, tm.Γ k) ∈ T}.Finite :=
          hT.preimage (f := fun x : tm.Γ k => (⟨k, x⟩ : Σ k, tm.Γ k))
            (sigma_mk_injective.injOn)
        obtain ⟨w, c, hw, hl, hi⟩ := exists_block _ _ hS
        exact ⟨w, c, hw, hl, fun x y hx hy h => hi hx hy h, fun h => absurd h h0,
          fun _ h => absurd h h1⟩
  choose w c hw hlen hinj hc0 hc1 using key
  let d : ∀ k, List Bool → Option (tm.Γ k) := fun k l =>
    if h : ∃ x, (⟨k, x⟩ : Σ k, tm.Γ k) ∈ T ∧ c k x = l then some h.choose else none
  have hd : ∀ k x, (⟨k, x⟩ : Σ k, tm.Γ k) ∈ T → d k (c k x) = some x := by
    intro k x hx
    have h : ∃ y, (⟨k, y⟩ : Σ k, tm.Γ k) ∈ T ∧ c k y = c k x := ⟨x, hx, rfl⟩
    have hspec := h.choose_spec
    simp only [d, dif_pos h]
    exact congrArg some (hinj k _ _ hspec.1 hx hspec.2)
  have hc0' : ∀ x, c tm.k₀ x = [e₀ x] := fun x => hc0 tm.k₀ rfl x
  obtain ⟨τ, hτ⟩ : ∃ τ : Bool ≃ Bool, ∀ x, c tm.k₁ x = [τ (e₁ x)] := by
    by_cases h : tm.k₁ = tm.k₀
    · have aux : ∀ k (_ : k = tm.k₀) (e : tm.Γ k ≃ Bool),
          ∃ τ : Bool ≃ Bool, ∀ x, c k x = [τ (e x)] := by
        intro k hk e
        subst hk
        exact ⟨e.symm.trans e₀, fun x => by simp [hc0']⟩
      exact aux _ h e₁
    · exact ⟨Equiv.refl _, fun x => hc1 tm.k₁ h rfl x⟩
  have hin : ∀ s : List Bool, (s.map e₀.symm).flatMap (c tm.k₀) = s := by
    intro s
    induction s with
    | nil => rfl
    | cons b s ih => simpa [hc0'] using ih
  have hout : ∀ t : List Bool, (t.map e₁.symm).flatMap (c tm.k₁) = t.map τ := by
    intro t
    induction t with
    | nil => rfl
    | cons b t ih => simpa [hτ] using ih
  refine ⟨simMachine tm w c d, τ, ?_⟩
  intro s t n h
  have htr : Trace (TM2.step tm.m) h.steps _ _ := Trace.of_iterate (f := tm.step) h.evals_in_steps
  have hsim := sim_trace w c d T hw hlen hd tm.m
    (fun l x hx => Or.inl (Set.mem_iUnion.2 ⟨l, hx⟩)) htr (by
      intro k x hx
      by_cases hk : k = tm.k₀
      · subst hk
        exact Or.inr ⟨_, rfl⟩
      · simp [initList, hk] at hx)
  have hinit : ecfg c (initList tm (s.map e₀.symm)) = (simMachine tm w c d).initialCfg s := by
    refine congrArg (TM2.Cfg.mk _ _) ?_
    funext k
    by_cases hk : k = tm.k₀
    · subst hk
      simpa [enc, initList, Machine.initialCfg] using hin s
    · simp [enc, initList, Machine.initialCfg, hk]
  have hhalt : ecfg c (haltList tm (t.map e₁.symm)) = (simMachine tm w c d).finalCfg (t.map τ) := by
    refine congrArg (TM2.Cfg.mk _ _) ?_
    funext k
    by_cases hk : k = tm.k₁
    · subst hk
      simpa [enc, haltList, Machine.finalCfg] using hout t
    · simp [enc, haltList, Machine.finalCfg, hk]
  rw [hinit, hhalt] at hsim
  exact ⟨⟨⟨_, hsim.iterate_eq⟩, h.steps_le_m⟩⟩

/-- A letterwise transducer. -/
def mapT (τ : Bool → Bool) : Transducer where
  Q := Unit
  initial := ()
  next _ b := ((), [τ b])
  finish _ := []

theorem mapT_run (τ : Bool → Bool) (xs : List Bool) : (mapT τ).run () xs = xs.map τ := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change τ b :: (mapT τ).run () xs = τ b :: xs.map τ; rw [ih]

end QMCBoolSim


namespace NovyPQZK.Main.PT

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem polyTimeFn_of_poly {f : Bits → Bits} (h : Poly f) : PolyTimeFn f :=
  ⟨(((BooleanLists.packProgram.comp h.program).comp BooleanLists.unpackProgram).congr f
    (fun _ => rfl)).stock⟩

theorem poly_of_polyTimeFn {f : Bits → Bits} (h : PolyTimeFn f) : Poly f := by
  obtain ⟨H⟩ := h
  obtain ⟨M, τ, hM⟩ := QMCBoolSim.simulate H.tm H.inputAlphabet H.outputAlphabet
  have hin : ∀ s : Bits, s.map H.inputAlphabet.symm = (id s).map H.inputAlphabet.symm := fun _ => rfl
  let P : PolyProgram id (fun b : Bits => b.map τ) f :=
    ⟨M, H.time, fun a => (hM _ _ _ (H.outputsFun a)).some⟩
  let Q : PolyProgram (fun b : Bits => b.map τ) id id :=
    (QMCBoolSim.mapT τ.symm).program.recode (fun b : Bits => b.map τ) (fun _ => rfl) (fun b => by
        change (QMCBoolSim.mapT τ.symm).run () _ = _
        rw [QMCBoolSim.mapT_run]
        simp)
  exact ⟨((BooleanLists.unpackProgram.comp (P.comp Q)).comp BooleanLists.packProgram).congr f
    (fun _ => rfl)⟩

section
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

theorem poly_foldl [Inhabited β] (op : γ × β → γ) (hop : Poly op) (C : ℕ)
    (hC : ∀ g b, (enc (op (g, b))).length ≤ (enc g).length + C * (2 * (enc b).length + 1))
    {xs : α → List β} {i : α → γ} (hx : Poly xs) (hi : Poly i) :
    Poly (fun x => (xs x).foldl (fun g b => op (g, b)) (i x)) :=
  Poly.comp (f := fun y : List β × γ => y.1.foldl (fun g b => op (g, b)) y.2)
    ⟨hop.program.listFoldLinear default C hC⟩ (Poly.pair hx hi)

@[fun_prop] theorem poly_reverse [Inhabited β] {xs : α → List β} (hx : Poly xs) :
    Poly (fun x => (xs x).reverse) :=
  Poly.comp (f := List.reverse) ⟨PolyProgram.listReverse enc default⟩ hx

@[fun_prop] theorem poly_range_length [Inhabited β] {xs : α → List β} (hx : Poly xs) :
    Poly (fun x => List.range (xs x).length) :=
  Poly.comp (f := fun l : List β => List.range l.length) Poly.list_indices hx

@[fun_prop] theorem poly_getD (a0 : β) {xs : α → List β} {i : α → ℕ} (hx : Poly xs) (hi : Poly i) :
    Poly (fun x => (xs x).getD (i x) a0) := by
  simp only [List.getD_eq_getElem?_getD]; fun_prop

@[fun_prop] theorem poly_all [Inhabited α] [Inhabited β] {p : α → β → Bool} {xs : α → List β}
    (hp : Poly (fun y : α × β => p y.1 y.2)) (hx : Poly xs) :
    Poly (fun x => (xs x).all (p x)) := by
  have e : ∀ x, (xs x).all (p x) = ((xs x).filter (fun b => !p x b)).isEmpty := by
    intro x; induction xs x with
    | nil => rfl
    | cons a l ih => by_cases h : p x a <;> simp [h, ih]
  simp only [e]
  have h2 : Poly (fun y : α × β => !p y.1 y.2) :=
    Poly.comp (f := fun b : Bool => !b) Poly.bool_not hp
  exact Poly.comp (f := List.isEmpty) Poly.list_empty (Poly.list_filter (f := fun x b => !p x b) h2 hx)

theorem poly_bool_xor : Poly (fun y : Bool × Bool => xor y.1 y.2) := by
  have e : ∀ y : Bool × Bool, xor y.1 y.2 = (if y.1 then !y.2 else y.2) := by
    intro y; cases y.1 <;> cases y.2 <;> rfl
  simp only [e]; fun_prop

@[fun_prop] theorem poly_bool_eq {a b : α → Bool} (ha : Poly a) (hb : Poly b) :
    Poly (fun x => decide (a x = b x)) := by
  have e : ∀ x, decide (a x = b x) = (if a x then b x else !b x) := by
    intro x; cases a x <;> cases b x <;> rfl
  simp only [e]; fun_prop

@[fun_prop] theorem poly_xor {a b : α → Bool} (ha : Poly a) (hb : Poly b) :
    Poly (fun x => xor (a x) (b x)) :=
  Poly.comp (f := fun y : Bool × Bool => xor y.1 y.2) poly_bool_xor (Poly.pair ha hb)

@[fun_prop] theorem poly_bits_eq [Inhabited α] {a b : α → Bits} (ha : Poly a) (hb : Poly b) :
    Poly (fun x => decide (a x = b x)) := by
  have e : ∀ x, decide (a x = b x) = (decide ((a x).length = (b x).length) &&
      (List.range (a x).length).all (fun i => decide ((a x).getD i false = (b x).getD i false))) := by
    intro x
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.and_eq_true, List.all_eq_true, List.mem_range]
    constructor
    · intro h; rw [h]; simp
    · rintro ⟨hl, h⟩
      apply List.ext_getElem hl
      intro i h1 h2
      have := h i h1
      simpa [List.getD_eq_getElem?_getD, h1, h2] using this
  simp only [e]
  fun_prop

end

theorem bitsToNat_eq_value (l : Bits) : bitsToNat l = Word.value l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have e : bitsToNat (b :: l) = 2 * bitsToNat l + cond b 1 0 := rfl
    rw [e, ih, Word.value_cons]; cases b <;> simp <;> ring

@[fun_prop] theorem poly_bitsToNat {α : Type} [Coding α] {a : α → Bits} (ha : Poly a) :
    Poly (fun x => bitsToNat (a x)) := by
  simp only [bitsToNat_eq_value]
  exact Poly.comp (f := Word.value) ⟨BooleanLists.valueProgram⟩ ha

theorem poly_ip_core : Poly (fun y : Bits × Bits => ip y.1 y.2) := by
  have h := poly_foldl (fun y : Bool × Bool => xor y.1 y.2) poly_bool_xor 0
    (fun g b => by simp [enc, Coding.encode, encodeBool]) (xs := fun y : Bits × Bits => (y.1.zip y.2).map fun p => p.1 && p.2)
    (i := fun _ => false) (by fun_prop) (by fun_prop)
  exact h

@[fun_prop] theorem poly_ip {α : Type} [Coding α] {a b : α → Bits} (ha : Poly a) (hb : Poly b) :
    Poly (fun x => ip (a x) (b x)) := Poly.comp (f := fun y : Bits × Bits => ip y.1 y.2) poly_ip_core (Poly.pair ha hb)

@[fun_prop] theorem poly_pack {α : Type} [Coding α] {a : α → List Bits} (ha : Poly a) :
    Poly (fun x => pack (a x)) := by
  unfold pack packOne; fun_prop

/-- one step of the streaming parser for `unpack`: the head of the list is the current item,
reversed; the flag records a pending `true`. -/
def upStep (y : List Bits × Bool) (b : Bool) : List Bits × Bool :=
  if y.2 then ((b :: y.1.head?.getD []) :: y.1.tail, false)
  else if b then (y.1, true) else ([] :: y.1, false)

theorem upStep_fold (x cur : Bits) (D : List Bits) :
    (((x.foldl upStep (cur :: D, false)).1.tail.map List.reverse).reverse) =
      (D.map List.reverse).reverse ++ unpackAux x cur := by
  induction x, cur using unpackAux.induct generalizing D with
  | case1 cur => simp [unpackAux]
  | case2 rest cur ih =>
    simp only [List.foldl_cons, upStep, unpackAux, Bool.false_eq_true, ite_false]
    rw [ih]; simp
  | case3 b rest cur ih =>
    simp only [List.foldl_cons, upStep, unpackAux, ite_true, Bool.false_eq_true, ite_false,
      List.head?_cons, Option.getD_some, List.tail_cons]
    rw [ih]
  | case4 cur => simp [unpackAux, upStep]

theorem unpack_eq_fold (x : Bits) :
    unpack x = ((x.foldl upStep ([[]], false)).1.tail.map List.reverse).reverse := by
  rw [upStep_fold x [] []]; simp [unpack]

theorem poly_upStep : Poly (fun y : (List Bits × Bool) × Bool => upStep y.1 y.2) := by
  unfold upStep; fun_prop

theorem enc_len_bits (l : Bits) : (enc l).length = 3 * l.length := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have h3 : (enc (b :: l)).length = 2 * (enc b).length + 1 + (enc l).length :=
      EncodedList.cons_length _ b l
    rw [h3, ih]; simp [enc, Coding.encode, encodeBool]; ring

theorem enc_len_listBits (L : List Bits) :
    (enc L).length = (L.map fun l => 6 * l.length + 1).sum := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    have h1 : (enc (l :: L)).length = 2 * (enc l).length + 1 + (enc L).length :=
      EncodedList.cons_length _ l L
    rw [h1, enc_len_bits, ih]; simp; ring

theorem enc_len_state (y : List Bits × Bool) :
    (enc y).length = 2 * (y.1.map fun l => 6 * l.length + 1).sum + 2 := by
  have : (enc y).length = 2 * (enc y.1).length + 1 + (enc y.2).length :=
    encodePair_length _ _ y
  rw [this, enc_len_listBits]; simp [enc, Coding.encode, encodeBool]

@[fun_prop] theorem poly_unpack {α : Type} [Coding α] {a : α → Bits} (ha : Poly a) :
    Poly (fun x => unpack (a x)) := by
  simp only [unpack_eq_fold]
  have h := poly_foldl (fun y : (List Bits × Bool) × Bool => upStep y.1 y.2) poly_upStep 5
    (fun g b => by
      rw [enc_len_state, enc_len_state]
      obtain ⟨L, p⟩ := g
      unfold upStep
      cases p <;> cases b <;> cases L <;> simp [enc, Coding.encode, encodeBool] <;> ring_nf <;> omega)
    (xs := a) (i := fun _ => ([[]], false)) ha (by fun_prop)
  have h2 : Poly (fun x => (((a x).foldl upStep ([[]], false)).1.tail.map List.reverse).reverse) := by
    fun_prop
  exact h2

end NovyPQZK.Main.PT


namespace NovyPQZK.Main.PT

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem hid_length_msbStr (n v : ℕ) : (msbStr n v).length = n := by simp [msbStr]

theorem hid_msbStr_succ (n v : ℕ) : msbStr (n + 1) v = v.testBit n :: msbStr n v := by
  simp only [msbStr, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  simp only [List.map_inj_left, List.mem_range, Function.comp_apply]
  intro a ha
  congr 1
  omega

theorem hid_getElem_msbStr (n v i : ℕ) (hi : i < (msbStr n v).length) :
    (msbStr n v)[i] = v.testBit (n - 1 - i) := by simp [msbStr]

theorem hid_msbStr_inj (n v w : ℕ) (hv : v < 2 ^ n) (hw : w < 2 ^ n)
    (h : msbStr n v = msbStr n w) : v = w := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have h1 : n - 1 - i < (msbStr n v).length := by rw [hid_length_msbStr]; omega
    have h2 : n - 1 - i < (msbStr n w).length := by rw [hid_length_msbStr]; omega
    have := hid_getElem_msbStr n v (n - 1 - i) h1
    have h' := hid_getElem_msbStr n w (n - 1 - i) h2
    have e : n - 1 - (n - 1 - i) = i := by omega
    rw [e] at this h'
    rw [← this, ← h']
    simp only [h]
  · have : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem hid_msbStr_surj (n : ℕ) (w : Bits) (hw : w.length = n) :
    ∃ v < 2 ^ n, msbStr n v = w := by
  induction n generalizing w with
  | zero => exact ⟨0, by norm_num, by simp [msbStr]; exact (List.length_eq_zero_iff.mp hw)⟩
  | succ n ih =>
    obtain _ | ⟨b, w'⟩ := w
    · simp at hw
    · simp only [List.length_cons, Nat.add_right_cancel_iff] at hw
      obtain ⟨v', hv', hm⟩ := ih w' hw
      refine ⟨(if b then 2 ^ n else 0) + v', ?_, ?_⟩
      · rw [pow_succ]; split_ifs <;> omega
      · rw [hid_msbStr_succ]
        congr 1
        · cases b
          · simp [Nat.testBit_lt_two_pow hv']
          · simp [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hv']
        · rw [← hm]
          apply List.ext_getElem (by simp [hid_length_msbStr])
          intro i h1 h2
          rw [hid_getElem_msbStr, hid_getElem_msbStr]
          rw [hid_length_msbStr] at h1
          cases b
          · simp
          · simp only [if_true]
            rw [Nat.testBit_two_pow_add_gt (by omega)]

/-- all strings of length `n`, in the order used by `consistentList`. -/
theorem hid_mem_enum (n : ℕ) (w : Bits) :
    w ∈ (List.range (2 ^ n)).map (msbStr n) ↔ w.length = n := by
  constructor
  · intro h
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp h
    exact hid_length_msbStr n v
  · intro h
    obtain ⟨v, hv, rfl⟩ := hid_msbStr_surj n w h
    exact List.mem_map.mpr ⟨v, List.mem_range.mpr hv, rfl⟩

theorem hid_nodup_enum (n : ℕ) : ((List.range (2 ^ n)).map (msbStr n)).Nodup := by
  apply List.Nodup.map_on _ List.nodup_range
  intro v hv w hw h
  exact hid_msbStr_inj n v w (List.mem_range.mp hv) (List.mem_range.mp hw) h


theorem hid_foldl_xor (l : List Bool) (acc : Bool) :
    l.foldl xor acc = xor acc (l.foldl xor false) := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih => simp only [List.foldl_cons]; rw [ih, ih (xor false a)]; simp [Bool.xor_assoc]

theorem hid_ip_cons (a b : Bool) (h w : Bits) : ip (a :: h) (b :: w) = xor (a && b) (ip h w) := by
  unfold ip
  simp only [List.zip_cons_cons, List.map_cons, List.foldl_cons]
  rw [hid_foldl_xor]
  simp

/-- the equations `⟨h_i, w⟩ = z_i`. -/
def eqsOK (hs : List Bits) (zs : List Bool) (w : Bits) : Bool :=
  (hs.zip zs).all fun p => ip p.1 w == p.2

theorem hid_consistentList_eq (n : ℕ) (hs : List Bits) (zs : List Bool) :
    consistentList n hs zs = ((List.range (2 ^ n)).map (msbStr n)).filter (eqsOK hs zs) := rfl

theorem hid_eqsOK_cons_false (gs : List Bits) (zs : List Bool) (w0 : Bool) (w : Bits) :
    eqsOK (gs.map (List.cons false)) zs (w0 :: w) = eqsOK gs zs w := by
  induction gs generalizing zs with
  | nil => simp [eqsOK]
  | cons g gs ih =>
    cases zs with
    | nil => simp [eqsOK]
    | cons z zs =>
      have := ih zs
      simp only [eqsOK, List.map_cons, List.zip_cons_cons, List.all_cons] at this ⊢
      rw [this, hid_ip_cons]
      simp

/-- `hs` is a list of legitimate challenges for rounds `1, 2, …`. -/
def WFs (N : ℕ) (hs : List Bits) : Prop :=
  ∀ i < hs.length, wellFormedH N (i + 1) (hs.getD i []) = true

theorem hid_wf_one (M : ℕ) (h : Bits) (hw : wellFormedH (M + 2) 1 h = true) :
    ∃ r, h = true :: r ∧ r.length = M + 1 := by
  obtain _ | ⟨a, r⟩ := h
  · simp [wellFormedH] at hw
  · simp [wellFormedH] at hw
    exact ⟨r, by rw [hw.2], hw.1⟩

theorem hid_wf_succ (M i : ℕ) (h : Bits) (hw : wellFormedH (M + 2) (i + 2) h = true) :
    h = false :: h.tail ∧ wellFormedH (M + 1) (i + 1) h.tail = true := by
  obtain _ | ⟨a, r⟩ := h
  · simp [wellFormedH] at hw
  · have e : i + 2 - 1 = i + 1 := by omega
    have e' : i + 1 - 1 = i := by omega
    simp only [wellFormedH, e, e', List.take_succ_cons, List.all_cons, List.getD_cons_succ,
      List.length_cons, Bool.and_eq_true, decide_eq_true_eq, List.tail_cons] at hw ⊢
    obtain ⟨⟨hl, ha, ht⟩, hg⟩ := hw
    refine ⟨by cases a <;> simp_all, ⟨decide_eq_true (by omega), ht⟩, hg⟩

/-- `N − 1` legitimate challenges leave exactly two consistent strings. -/
theorem hid_two_solutions (M : ℕ) (hs : List Bits) (zs : List Bool) (hl : hs.length = M)
    (hz : zs.length = M) (hwf : WFs (M + 1) hs) :
    ∃ s0 s1 : Bits, s0 ≠ s1 ∧ ∀ w, (w.length = M + 1 ∧ eqsOK hs zs w = true) ↔ (w = s0 ∨ w = s1) := by
  induction M generalizing hs zs with
  | zero =>
    rw [List.length_eq_zero_iff] at hl hz
    subst hl hz
    refine ⟨[false], [true], by simp, fun w => ?_⟩
    simp only [eqsOK, List.zip_nil_left, List.all_nil, and_true]
    constructor
    · intro h
      obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp h
      cases b <;> simp
    · rintro (rfl | rfl) <;> rfl
  | succ M ih =>
    obtain _ | ⟨h1, hs'⟩ := hs
    · simp at hl
    obtain _ | ⟨z1, zs'⟩ := zs
    · simp at hz
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl hz
    obtain ⟨r1, rfl, hr1⟩ := hid_wf_one M h1 (by simpa using hwf 0 (by simp))
    have hsuc : ∀ i < hs'.length, wellFormedH (M + 2) (i + 2) (hs'.getD i []) = true := by
      intro i hi
      simpa using hwf (i + 1) (by simp; omega)
    set gs := hs'.map List.tail
    have hhs : hs' = gs.map (List.cons false) := by
      simp only [gs, List.map_map]
      conv_lhs => rw [← List.map_id hs']
      apply List.ext_getElem (by simp)
      intro i h1 h2
      simp only [List.getElem_map, id, Function.comp_apply]
      have := (hid_wf_succ M i _ (hsuc i (by simpa using h1))).1
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1),
        Option.getD_some] at this
      exact this
    have hgwf : WFs (M + 1) gs := by
      intro i hi
      have hi' : i < hs'.length := by simpa [gs] using hi
      have := (hid_wf_succ M i _ (hsuc i hi')).2
      simpa [gs, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi'] using this
    obtain ⟨s0, s1, hne, hiff⟩ := ih gs zs' (by simp [gs, hl]) hz hgwf
    refine ⟨xor z1 (ip r1 s0) :: s0, xor z1 (ip r1 s1) :: s1, by simp [hne], fun w => ?_⟩
    have key : ∀ w0 w', eqsOK ((true :: r1) :: hs') (z1 :: zs') (w0 :: w') =
        ((xor w0 (ip r1 w') == z1) && eqsOK gs zs' w') := by
      intro w0 w'
      rw [hhs]
      simp only [eqsOK, List.zip_cons_cons, List.all_cons]
      rw [← eqsOK, hid_eqsOK_cons_false, hid_ip_cons]
      simp only [Bool.true_and]
      rfl
    obtain _ | ⟨w0, w'⟩ := w
    · simp
    rw [key]
    simp only [List.length_cons, Nat.add_right_cancel_iff, Bool.and_eq_true, beq_iff_eq,
      List.cons.injEq]
    constructor
    · rintro ⟨hl', h1', h2'⟩
      have hw0 : w0 = xor z1 (ip r1 w') := by rw [← h1']; cases w0 <;> simp
      rcases (hiff w').mp ⟨hl', h2'⟩ with rfl | rfl
      · exact Or.inl ⟨hw0, rfl⟩
      · exact Or.inr ⟨hw0, rfl⟩
    · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
      · subst w0; subst w'
        have := (hiff s0).mpr (Or.inl rfl)
        exact ⟨this.1, by simp, this.2⟩
      · subst w0; subst w'
        have := (hiff s1).mpr (Or.inr rfl)
        exact ⟨this.1, by simp, this.2⟩


theorem hid_eqsOK_map (hs : List Bits) (f : Bits → Bool) (w : Bits) :
    eqsOK hs (hs.map f) w = true ↔ ∀ h ∈ hs, ip h w = f h := by
  induction hs with
  | nil => simp [eqsOK]
  | cons h hs ih =>
    have e : eqsOK (h :: hs) ((h :: hs).map f) w = ((ip h w == f h) && eqsOK hs (hs.map f) w) := rfl
    rw [e, Bool.and_eq_true, ih]
    simp

theorem hid_cl_mem (n : ℕ) (hs : List Bits) (zs : List Bool) (w : Bits) :
    w ∈ consistentList n hs zs ↔ w.length = n ∧ eqsOK hs zs w = true := by
  rw [hid_consistentList_eq, List.mem_filter, hid_mem_enum]

theorem hid_cl_pair (N : ℕ) (hN : 1 ≤ N) (hs : List Bits) (zs : List Bool) (hl : hs.length = N - 1)
    (hz : zs.length = N - 1) (hwf : WFs N hs) :
    ∃ a b, a ≠ b ∧ consistentList N hs zs = [a, b] := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hl hz
  obtain ⟨s0, s1, hne, hiff⟩ := hid_two_solutions M hs zs hl hz hwf
  have hnd : (consistentList (M + 1) hs zs).Nodup := by
    rw [hid_consistentList_eq]; exact (hid_nodup_enum _).filter _
  have hp : (consistentList (M + 1) hs zs).Perm [s0, s1] := by
    rw [List.perm_ext_iff_of_nodup hnd (by simp [hne])]
    intro w
    rw [hid_cl_mem, hiff]
    simp
  have hlen := hp.length_eq
  match h : consistentList (M + 1) hs zs, hnd with
  | [a, b], hnd' => exact ⟨a, b, by simpa using hnd', rfl⟩
  | [], _ => simp [h] at hlen
  | [_], _ => simp [h] at hlen
  | _ :: _ :: _ :: _, _ => simp [h] at hlen

/-- the other string consistent with the hashing transcript. -/
def partner (N : ℕ) (hs : List Bits) (y : Bits) : Bits :=
  let ys := consistentList N hs (hs.map fun h => ip h y)
  if y = ys.getD 0 [] then ys.getD 1 [] else ys.getD 0 []


def wfB (N : ℕ) (hs : List Bits) : Bool :=
  (List.range hs.length).all fun i => wellFormedH N (i + 1) (hs.getD i [])

theorem hid_WFs_of_wfB (N : ℕ) (hs : List Bits) (h : wfB N hs = true) : WFs N hs := by
  intro i hi
  simp only [wfB, List.all_eq_true, List.mem_range] at h
  exact h i hi

theorem testBit_bitsToNat (l : Bits) (i : ℕ) : (bitsToNat l).testBit i = l.getD i false := by
  induction l generalizing i with
  | nil => simp [bitsToNat]
  | cons b l ih =>
    have e : bitsToNat (b :: l) = Nat.bit b (bitsToNat l) := by
      show 2 * bitsToNat l + cond b 1 0 = _
      cases b <;> simp [Nat.bit] <;> ring
    rw [e]
    cases i with
    | zero => simp [Nat.testBit_bit_zero]
    | succ i => rw [Nat.testBit_bit_succ, ih]; simp

theorem msbStr_bitsToNat (k : ℕ) (c : Bits) :
    msbStr k (bitsToNat c) = (List.range k).map fun i => c.getD (k - 1 - i) false := by
  simp [msbStr, testBit_bitsToNat]

theorem valRev_msbStr (n v : ℕ) : bitsToNat (msbStr n v).reverse = v % 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_bitsToNat, Nat.testBit_mod_two_pow]
  by_cases hi : i < n
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hid_length_msbStr]; omega)]
    simp only [List.getElem_reverse, Option.getD_some, hi, decide_true, Bool.true_and]
    rw [hid_getElem_msbStr]
    simp [hid_length_msbStr]
    congr 1; omega
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [hid_length_msbStr]; omega)]
    simp [hi]

theorem cl_pairwise (n : ℕ) (hs : List Bits) (zs : List Bool) :
    (consistentList n hs zs).Pairwise
      (fun a b => bitsToNat a.reverse < bitsToNat b.reverse) := by
  rw [hid_consistentList_eq]
  apply List.Pairwise.filter
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ List.pairwise_lt_range
  intro a b ha hb hab
  rw [valRev_msbStr, valRev_msbStr, Nat.mod_eq_of_lt (List.mem_range.mp ha),
    Nat.mod_eq_of_lt (List.mem_range.mp hb)]
  exact hab

/-- one back-substitution step. -/
def bstep (p : Bits × Bool) (s : Bits) : Bits := xor p.2 (ip p.1.reverse s.reverse) :: s

/-- the solution of the triangular system with last bit `c`. -/
def bsol (hs : List Bits) (zs : List Bool) (c : Bool) : Bits := (hs.zip zs).foldr bstep [c]

/-- the two strings ordered as in `consistentList`. -/
def sp (a b : Bits) : List Bits :=
  if bitsToNat a.reverse < bitsToNat b.reverse then [a, b] else [b, a]

def ysG (n : ℕ) (hs : List Bits) (zs : List Bool) : List Bits :=
  if n = 0 then [] else sp (bsol hs zs false) (bsol hs zs true)

theorem zip_append_left (a b w : Bits) (h : w.length ≤ a.length) :
    (a ++ b).zip w = a.zip w := by
  induction a generalizing w with
  | nil => simp at h; simp [h]
  | cons x a ih =>
    cases w with
    | nil => simp
    | cons y w => simp [ih w (by simpa using h)]

theorem ip_append_left (a b w : Bits) (h : w.length ≤ a.length) : ip (a ++ b) w = ip a w := by
  unfold ip; rw [zip_append_left a b w h]

theorem ip_reverse (a w : Bits) (h : a.length = w.length) : ip a.reverse w.reverse = ip a w := by
  induction a generalizing w with
  | nil => simp [ip]
  | cons x a ih =>
    cases w with
    | nil => simp at h
    | cons y w =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rw [hid_ip_cons, ← ih w h]
      simp only [List.reverse_cons, ip]
      rw [List.zip_append (by simpa using h)]
      simp only [List.map_append, List.foldl_append, List.zip_cons_cons, List.zip_nil_left,
        List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      rw [Bool.xor_comm]

theorem bsol_cons (h : Bits) (z : Bool) (hs : List Bits) (zs : List Bool) (c : Bool) :
    bsol (h :: hs) (z :: zs) c = bstep (h, z) (bsol hs zs c) := rfl

theorem bsol_length (hs : List Bits) (zs : List Bool) (c : Bool) :
    (bsol hs zs c).length = min hs.length zs.length + 1 := by
  induction hs generalizing zs with
  | nil => simp [bsol]
  | cons h hs ih =>
    cases zs with
    | nil => simp [bsol]
    | cons z zs => rw [bsol_cons]; simp [bstep, ih] <;> omega

theorem bsol_getLast (hs : List Bits) (zs : List Bool) (c : Bool) :
    (bsol hs zs c).getLast? = some c := by
  induction hs generalizing zs with
  | nil => simp [bsol]
  | cons h hs ih =>
    cases zs with
    | nil => simp [bsol]
    | cons z zs =>
      rw [bsol_cons, bstep, List.getLast?_cons, ih]; rfl

theorem bsol_map_false (gs : List Bits) (zs : List Bool) (c : Bool)
    (h : ∀ g ∈ gs, gs.length ≤ g.length) :
    bsol (gs.map (List.cons false)) zs c = bsol gs zs c := by
  induction gs generalizing zs with
  | nil => rfl
  | cons g gs ih =>
    cases zs with
    | nil => rfl
    | cons z zs =>
      simp only [List.map_cons, bsol_cons]
      rw [ih zs (fun g' hg' => by
        have := h g' (by simp [hg']); simp at this; omega)]
      have hs : (bsol gs zs c).length ≤ g.length := by
        rw [bsol_length]; have := h g (by simp); simp at this; omega
      simp only [bstep, List.reverse_cons]
      rw [ip_append_left _ _ _ (by simpa using hs)]

theorem wf_length (n i : ℕ) (h : Bits) (hw : wellFormedH n i h = true) : h.length = n := by
  simp only [wellFormedH, Bool.and_eq_true, decide_eq_true_eq] at hw
  exact hw.1.1

theorem bsol_spec (M : ℕ) (hs : List Bits) (zs : List Bool) (hl : hs.length = M)
    (hz : zs.length = M) (hwf : WFs (M + 1) hs) (c : Bool) :
    eqsOK hs zs (bsol hs zs c) = true := by
  induction M generalizing hs zs with
  | zero =>
    rw [List.length_eq_zero_iff] at hl hz
    subst hl hz; rfl
  | succ M ih =>
    obtain _ | ⟨h1, hs'⟩ := hs
    · simp at hl
    obtain _ | ⟨z1, zs'⟩ := zs
    · simp at hz
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl hz
    obtain ⟨r1, rfl, hr1⟩ := hid_wf_one M h1 (by simpa using hwf 0 (by simp))
    have hsuc : ∀ i < hs'.length, wellFormedH (M + 2) (i + 2) (hs'.getD i []) = true := by
      intro i hi
      simpa using hwf (i + 1) (by simp; omega)
    set gs := hs'.map List.tail
    have hhs : hs' = gs.map (List.cons false) := by
      simp only [gs, List.map_map]
      conv_lhs => rw [← List.map_id hs']
      apply List.ext_getElem (by simp)
      intro i h1 h2
      simp only [List.getElem_map, id, Function.comp_apply]
      have := (hid_wf_succ M i _ (hsuc i (by simpa using h1))).1
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1),
        Option.getD_some] at this
      exact this
    have hgwf : WFs (M + 1) gs := by
      intro i hi
      have hi' : i < hs'.length := by simpa [gs] using hi
      have := (hid_wf_succ M i _ (hsuc i hi')).2
      simpa [gs, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi'] using this
    have hgl : gs.length = M := by simp [gs, hl]
    have hglen : ∀ g ∈ gs, gs.length ≤ g.length := by
      intro g hg
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      have := wf_length _ _ _ (hgwf i hi)
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
      omega
    have IH := ih gs zs' hgl hz hgwf
    have key : ∀ w0 w', eqsOK ((true :: r1) :: hs') (z1 :: zs') (w0 :: w') =
        ((xor w0 (ip r1 w') == z1) && eqsOK gs zs' w') := by
      intro w0 w'
      rw [hhs]
      simp only [eqsOK, List.zip_cons_cons, List.all_cons]
      rw [← eqsOK, hid_eqsOK_cons_false, hid_ip_cons]
      simp only [Bool.true_and]
      rfl
    have hlen : (bsol gs zs' c).length = M + 1 := by rw [bsol_length]; omega
    rw [bsol_cons, hhs, bsol_map_false gs zs' c hglen, ← hhs]
    simp only [bstep, List.reverse_cons]
    rw [key, ip_append_left _ _ _ (by simp [hlen, hr1]),
      ip_reverse _ _ (by rw [hlen, hr1]), IH]
    simp

theorem bsol_ne (hs : List Bits) (zs : List Bool) : bsol hs zs false ≠ bsol hs zs true := by
  intro h
  have := congrArg List.getLast? h
  rw [bsol_getLast, bsol_getLast] at this
  simp at this

theorem cl_eq_sp (n : ℕ) (hn : 1 ≤ n) (hs : List Bits) (zs : List Bool) (hl : hs.length = n - 1)
    (hz : zs.length = n - 1) (hwf : WFs n hs) :
    consistentList n hs zs = sp (bsol hs zs false) (bsol hs zs true) := by
  obtain ⟨a, b, hab, hys⟩ := hid_cl_pair n hn hs zs hl hz hwf
  have hpw := cl_pairwise n hs zs
  rw [hys] at hpw
  have hlt : bitsToNat a.reverse < bitsToNat b.reverse := by simpa using hpw
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 1 := ⟨n - 1, by omega⟩
  have hmem : ∀ c, bsol hs zs c ∈ [a, b] := by
    intro c
    rw [← hys, hid_cl_mem]
    refine ⟨?_, bsol_spec M hs zs (by simpa using hl) (by simpa using hz) hwf c⟩
    rw [bsol_length]; simp at hl hz; omega
  have hne := bsol_ne hs zs
  have h0 := hmem false
  have h1 := hmem true
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h0 h1
  rw [hys]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exact absurd (h0.trans h1.symm) hne
  · rw [h0, h1, sp, if_pos hlt]
  · rw [h0, h1, sp, if_neg (by omega)]
  · exact absurd (h0.trans h1.symm) hne

theorem cl_getD_ysG (n : ℕ) (hs : List Bits) (zs : List Bool) (hl : hs.length = n - 1)
    (hz : zs.length = n - 1) (hwf : WFs n hs) (k : ℕ) :
    (consistentList n hs zs).getD k [] = (ysG n hs zs).getD k [] := by
  by_cases hn : n = 0
  · subst hn
    simp at hl hz
    subst hl hz
    have : consistentList 0 [] [] = [[]] := rfl
    rw [this, ysG, if_pos rfl]
    cases k <;> simp
  · rw [ysG, if_neg hn, cl_eq_sp n (by omega) hs zs hl hz hwf]

theorem poly_bstep : Poly (fun y : Bits × (Bits × Bool) => bstep y.2 y.1) := by
  unfold bstep; fun_prop

@[fun_prop] theorem poly_bsol {α : Type} [Coding α] [Inhabited α] {hs : α → List Bits}
    {zs : α → List Bool} {c : α → Bool} (hh : Poly hs) (hz : Poly zs) (hc : Poly c) :
    Poly (fun x => bsol (hs x) (zs x) (c x)) := by
  have e : ∀ x, bsol (hs x) (zs x) (c x) =
      ((hs x).zip (zs x)).reverse.foldl (fun s p => bstep p s) [c x] := by
    intro x; rw [List.foldl_reverse]; rfl
  simp only [e]
  exact poly_foldl (fun y : Bits × (Bits × Bool) => bstep y.2 y.1) poly_bstep 1
    (fun g b => by
      have h1 : (enc (bstep b g)).length = (enc g).length + 3 := by
        rw [enc_len_bits, enc_len_bits]; simp [bstep]; ring
      have h2 : (enc b).length = 2 * (enc b.1).length + 1 + (enc b.2).length :=
        encodePair_length _ _ b
      simp only at h1 ⊢
      rw [h1]; omega)
    (xs := fun x => ((hs x).zip (zs x)).reverse) (i := fun x => [c x]) (by fun_prop) (by fun_prop)

@[fun_prop] theorem poly_ysG {α : Type} [Coding α] [Inhabited α] {n : α → ℕ} {hs : α → List Bits}
    {zs : α → List Bool} (hn : Poly n) (hh : Poly hs) (hz : Poly zs) :
    Poly (fun x => ysG (n x) (hs x) (zs x)) := by
  unfold ysG sp; fun_prop

end NovyPQZK.Main.PT


namespace NovyPQZK.Main.PT

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

/-- `take` written with the available list primitives. -/
def takeG {β : Type} (d : β) (k : ℕ) (l : List β) : List β :=
  ((List.range l.length).filter (fun i => decide (i < k))).map (fun i => l.getD i d)

theorem range_filter_lt (n k : ℕ) :
    (List.range n).filter (fun i => decide (i < k)) = List.range (min n k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, ih]
    by_cases h : n < k
    · rw [show min (n + 1) k = min n k + 1 by omega, show min n k = n by omega, List.range_succ]
      simp [h]
    · rw [show min (n + 1) k = min n k by omega]; simp [h]

theorem takeG_eq {β : Type} (d : β) (k : ℕ) (l : List β) : takeG d k l = l.take k := by
  unfold takeG
  rw [range_filter_lt]
  apply List.ext_getElem (by simp [Nat.min_comm])
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_take]
  simp at h1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl

@[fun_prop] theorem poly_takeG {α β : Type} [Coding α] [Coding β] [Inhabited α] [Inhabited β]
    (d : β) {k : α → ℕ} {l : α → List β} (hk : Poly k) (hl : Poly l) :
    Poly (fun x => takeG d (k x) (l x)) := by
  unfold takeG; fun_prop

theorem wf_eq (n i : ℕ) (h : Bits) : wellFormedH n i h =
    (decide (h.length = n) && (takeG false (i - 1) h).all (fun b => !b) && h.getD (i - 1) false) := by
  rw [takeG_eq]; rfl

@[fun_prop] theorem poly_wf {α : Type} [Coding α] [Inhabited α] {n i : α → ℕ} {h : α → Bits}
    (hn : Poly n) (hi : Poly i) (hh : Poly h) : Poly (fun x => wellFormedH (n x) (i x) (h x)) := by
  simp only [wf_eq]; fun_prop

theorem natToBits_two_pow (k : ℕ) : natToBits (2 ^ k) = List.replicate k false ++ [true] := by
  have hv : Word.value (List.replicate k false ++ [true]) = 2 ^ k := by
    rw [Word.value_append, (Word.value_zero _).mpr (fun b hb => (List.mem_replicate.mp hb).2)]
    simp
  unfold natToBits
  rw [← hv, Word.bits_value]
  simp

theorem filter_range_ge (n k : ℕ) :
    ((List.range n).filter fun i => decide (k ≤ i)).length = n - k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    by_cases h : k ≤ n
    · simp [h]; omega
    · simp [h]; omega

theorem getD_map_bitsToNat (l : List Bits) (j : ℕ) :
    (l.map bitsToNat).getD j 0 = bitsToNat (l.getD j []) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[j]? <;> rfl

/-- `novyX` with the available primitives. -/
def novyXg (pub cenc : Bits) : Bits :=
  (List.range pub.length).map fun i => ((unpack cenc).getD 0 []).getD (pub.length - 1 - i) false

theorem novyX_eq (pub cenc : Bits) : novyX pub.length cenc = novyXg pub cenc := by
  unfold novyX novyXg
  rw [getD_map_bitsToNat, msbStr_bitsToNat]

@[fun_prop] theorem poly_novyXg {α : Type} [Coding α] [Inhabited α] {p c : α → Bits}
    (hp : Poly p) (hc : Poly c) : Poly (fun x => novyXg (p x) (c x)) := by
  unfold novyXg; fun_prop

/-! ### setup and rounds -/

def gSetup (s : Bits) : Bits := if s.isEmpty then [true] else s.map (fun _ => true)

theorem setup_eq (s : Bits) : unary (max s.length 1) = gSetup s := by
  cases s with
  | nil => rfl
  | cons b s => simp [gSetup, unary, List.map_const', List.replicate_succ]

theorem poly_gSetup : Poly gSetup := by unfold gSetup; fun_prop

/-! ### Sam's coins -/

def gSCoins (s : Bits) : Bits :=
  if (unpack s).length = 2 then pack [((unpack s).getD 1 []).map (fun _ => false) ++ [true]]
  else pack []

theorem scoins_eq (π : PermFamily) (s : Bits) :
    pack (((novy π).sender.coins s).map natToBits) = gSCoins s := by
  show pack ((match unpack s with
    | [_, pub] => [2 ^ pub.length]
    | _ => []).map natToBits) = _
  unfold gSCoins
  rcases unpack s with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;>
    simp [natToBits_two_pow, List.map_const']

theorem poly_gSCoins : Poly gSCoins := by unfold gSCoins; fun_prop

/-! ### Rachel's coins -/

def gRCoins (pub : Bits) : Bits :=
  pack ((List.range pub.tail.length).map fun j =>
    ((List.range pub.length).filter (fun i => decide (j + 1 ≤ i))).map (fun _ => false) ++ [true])

theorem rcoins_eq (π : PermFamily) (pub : Bits) :
    pack (((novy π).receiver.coins pub).map natToBits) = gRCoins pub := by
  show pack ((((List.range (pub.length - 1)).map fun j => 2 ^ (pub.length - (j + 1)))).map
    natToBits) = _
  unfold gRCoins
  congr 1
  rw [List.length_tail, List.map_map]
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply, natToBits_two_pow, List.map_const', filter_range_ge]

theorem poly_gRCoins : Poly gRCoins := by unfold gRCoins; fun_prop

/-! ### Rachel's messages -/

def gRNext (view : Bits) : Bits :=
  if 2 ≤ (unpack view).length then
    let inp := (unpack view).getD 0 []
    let cenc := (unpack view).getD 1 []
    let msgs := (unpack view).tail.tail
    if msgs.length < inp.length - 1 then
      msgs.map (fun _ => false) ++ [true] ++
        ((List.range inp.length).filter (fun i => decide (i < inp.length - (msgs.length + 1)))).map
          (fun i => ((unpack cenc).getD msgs.length []).getD
            (inp.length - (msgs.length + 1) - 1 - i) false)
    else []
  else []

theorem rnext_eq (π : PermFamily) (view : Bits) : (novy π).receiver.next view = gRNext view := by
  show novyReceiver.next view = _
  unfold novyReceiver gRNext
  simp only
  rcases unpack view with _ | ⟨inp, _ | ⟨cenc, msgs⟩⟩
  · simp
  · simp
  · simp only [List.length_cons, le_add_iff_nonneg_left, zero_le, if_true, List.getD_cons_zero,
      List.getD_cons_succ, List.tail_cons]
    split_ifs with h
    · rw [getD_map_bitsToNat, msbStr_bitsToNat, range_filter_lt,
        show min inp.length (inp.length - (msgs.length + 1)) = inp.length - (msgs.length + 1)
          by omega, List.map_const']
    · rfl

theorem poly_gRNext : Poly gRNext := by unfold gRNext; fun_prop

end NovyPQZK.Main.PT


namespace NovyPQZK.Main.PT

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem getLastD_eq (l : List Bits) : l.getLastD [] = l.getD (l.length - 1) [] := by
  rcases l.eq_nil_or_concat with rfl | ⟨L, b, rfl⟩
  · rfl
  · simp [List.getLastD_eq_getLast?, List.getD_eq_getElem?_getD]

/-! ### Sam's messages -/

def sBody (π : PermFamily) (m pub cenc : Bits) (msgs : List Bits) : Bits :=
  if ((List.range (takeG [] (pub.length - 1) msgs).length).all fun i =>
      wellFormedH pub.length (i + 1) ((takeG [] (pub.length - 1) msgs).getD i [])) then
    if msgs.length = 0 then []
    else if msgs.length ≤ pub.length - 1 then
      [ip (msgs.getD (msgs.length - 1) []) (π.applyStr (novyXg pub cenc))]
    else if msgs.length = (pub.length - 1) + 1 then
      [xor (m.head?.getD false) (!(decide (π.applyStr (novyXg pub cenc) =
        (ysG pub.length (takeG [] (pub.length - 1) msgs)
          ((takeG [] (pub.length - 1) msgs).map fun h => ip h (π.applyStr (novyXg pub cenc)))).getD 0 [])))]
    else []
  else []

def gSNext (π : PermFamily) (view : Bits) : Bits :=
  if 2 ≤ (unpack view).length then
    if (unpack ((unpack view).getD 0 [])).length = 2 then
      sBody π ((unpack ((unpack view).getD 0 [])).getD 0 [])
        ((unpack ((unpack view).getD 0 [])).getD 1 []) ((unpack view).getD 1 [])
        (unpack view).tail.tail
    else []
  else []

theorem snext_eq (π : PermFamily) (view : Bits) : (novy π).sender.next view = gSNext π view := by
  show (novySender π).next view = _
  unfold novySender gSNext
  simp only
  rcases unpack view with _ | ⟨inp, _ | ⟨cenc, msgs⟩⟩
  · simp
  · simp
  simp only [List.length_cons, le_add_iff_nonneg_left, zero_le, if_true, List.getD_cons_zero,
    List.getD_cons_succ, List.tail_cons]
  rcases unpack inp with _ | ⟨m, _ | ⟨pub, _ | ⟨w, t⟩⟩⟩
  · simp
  · simp
  swap
  · simp
  simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, if_true,
    List.getD_cons_zero, List.getD_cons_succ]
  unfold sBody
  rw [← novyX_eq, takeG_eq, getLastD_eq]
  split_ifs with h1 h2 h3 h4 <;> try rfl
  have hl : (msgs.take (pub.length - 1)).length = pub.length - 1 := by simp; omega
  rw [cl_getD_ysG pub.length _ _ hl (by simp; omega) (hid_WFs_of_wfB _ _ h1) 0, List.headD_eq_head?_getD]

theorem poly_sBody (π : PermFamily) (hP : Poly π.applyStr) :
    Poly (fun x : ((Bits × Bits) × Bits) × List Bits => sBody π x.1.1.1 x.1.1.2 x.1.2 x.2) := by
  unfold sBody; fun_prop

theorem poly_gSNext (π : PermFamily) (hP : Poly π.applyStr) : Poly (gSNext π) := by
  have h := poly_sBody π hP
  unfold gSNext
  refine Poly.ite_prop (by fun_prop) (Poly.ite_prop (by fun_prop) ?_ (by fun_prop)) (by fun_prop)
  exact Poly.comp (f := fun x : ((Bits × Bits) × Bits) × List Bits => sBody π x.1.1.1 x.1.1.2 x.1.2 x.2)
    (g := fun view => ((((unpack ((unpack view).getD 0 [])).getD 0 [],
        (unpack ((unpack view).getD 0 [])).getD 1 []), (unpack view).getD 1 []),
        (unpack view).tail.tail)) h (by fun_prop)

/-! ### Sam's opening -/

def gSOpen (π : PermFamily) (s : Bits) : Bits :=
  if 2 ≤ (unpack s).length then
    if (unpack ((unpack s).getD 0 [])).length = 2 then
      pack [(unpack ((unpack s).getD 0 [])).getD 0 [],
        pack [novyXg ((unpack ((unpack s).getD 0 [])).getD 1 []) ((unpack s).getD 1 []),
          π.applyStr (novyXg ((unpack ((unpack s).getD 0 [])).getD 1 []) ((unpack s).getD 1 []))]]
    else pack [[], []]
  else pack [[], []]

theorem sopen_eq (π : PermFamily) (s : Bits) :
    pack [((novy π).sopen s).1, ((novy π).sopen s).2] = gSOpen π s := by
  show pack [(novySopen π s).1, (novySopen π s).2] = _
  unfold novySopen gSOpen
  rcases unpack s with _ | ⟨inp, _ | ⟨cenc, msgs⟩⟩
  · simp
  · simp
  simp only [List.length_cons, le_add_iff_nonneg_left, zero_le, if_true, List.getD_cons_zero,
    List.getD_cons_succ]
  rcases unpack inp with _ | ⟨m, _ | ⟨pub, _ | ⟨w, t⟩⟩⟩
  · simp
  · simp
  swap
  · simp
  simp [novyX_eq]

theorem poly_gSOpen (π : PermFamily) (hP : Poly π.applyStr) : Poly (gSOpen π) := by
  unfold gSOpen; fun_prop

/-! ### Rachel's verdict -/

def ropenG (π : PermFamily) (m u : Bits) (comm : List Bits) (pub : Bits) : Bool :=
  if (unpack u).length = 2 then
    decide (comm.length = (pub.length - 1) + 1 + ((pub.length - 1) + 1)) &&
      ((List.range pub.tail.length).all fun i => wellFormedH pub.length (i + 1)
        (((List.range pub.tail.length).map fun i => comm.getD (i + i) []).getD i [])) &&
      ((List.range pub.tail.length).map fun i => comm.getD (i + i + 1) []).all
        (fun z => decide (z.length = 1)) &&
      decide ((comm.getD ((pub.length - 1) + (pub.length - 1) + 1) []).length = 1) &&
      decide (m.length = 1) && decide (u = pack [(unpack u).getD 0 [], (unpack u).getD 1 []]) &&
      decide (((unpack u).getD 0 []).length = pub.length) &&
      decide (((unpack u).getD 1 []).length = pub.length) &&
      ((decide ((unpack u).getD 1 [] = (ysG pub.length
            ((List.range pub.tail.length).map fun i => comm.getD (i + i) [])
            (((List.range pub.tail.length).map fun i => comm.getD (i + i + 1) []).map
              fun z => z.head?.getD false)).getD 0 []) &&
          decide (π.applyStr ((unpack u).getD 0 []) = (unpack u).getD 1 []) &&
          decide (m.head?.getD false =
            xor ((comm.getD ((pub.length - 1) + (pub.length - 1) + 1) []).head?.getD false) false)) ||
        (decide ((unpack u).getD 1 [] = (ysG pub.length
            ((List.range pub.tail.length).map fun i => comm.getD (i + i) [])
            (((List.range pub.tail.length).map fun i => comm.getD (i + i + 1) []).map
              fun z => z.head?.getD false)).getD 1 []) &&
          decide (π.applyStr ((unpack u).getD 0 []) = (unpack u).getD 1 []) &&
          decide (m.head?.getD false =
            xor ((comm.getD ((pub.length - 1) + (pub.length - 1) + 1) []).head?.getD false) true)))
  else false

theorem ropen_eq (π : PermFamily) (m u : Bits) (comm : List Bits) (privR pub : Bits) :
    novyRopen π m u comm privR pub = ropenG π m u comm pub := by
  unfold novyRopen ropenG
  simp only [List.length_tail, two_mul]
  rcases unpack u with _ | ⟨x, _ | ⟨y, _ | ⟨w, t⟩⟩⟩
  · simp
  · simp
  swap
  · simp
  simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, if_true,
    List.getD_cons_zero, List.getD_cons_succ, List.any_cons, List.any_nil, Bool.toNat_false,
    Bool.toNat_true, Bool.or_false, List.headD_eq_head?_getD]
  by_cases hw : ((List.range (pub.length - 1)).all fun i => wellFormedH pub.length (i + 1)
      (((List.range (pub.length - 1)).map fun i => comm.getD (i + i) []).getD i [])) = true
  · have hl : ((List.range (pub.length - 1)).map fun i => comm.getD (i + i) []).length =
        pub.length - 1 := by simp
    have hwf := hid_WFs_of_wfB pub.length _ (by unfold wfB; rw [hl]; exact hw)
    have hz : (((List.range (pub.length - 1)).map fun i => comm.getD (i + i + 1) []).map
        fun z => z.head?.getD false).length = pub.length - 1 := by simp
    simp only [cl_getD_ysG pub.length _ _ hl hz hwf 0, cl_getD_ysG pub.length _ _ hl hz hwf 1]
  · simp only [Bool.not_eq_true] at hw
    simp only [hw, Bool.and_false, Bool.false_and]

theorem poly_ropenG (π : PermFamily) (hP : Poly π.applyStr) :
    Poly (fun x : ((Bits × Bits) × List Bits) × Bits => ropenG π x.1.1.1 x.1.1.2 x.1.2 x.2) := by
  unfold ropenG; fun_prop

def gROpen (π : PermFamily) (s : Bits) : Bits :=
  if 4 ≤ (unpack s).length then
    [ropenG π ((unpack s).getD 0 []) ((unpack s).getD 1 []) (unpack s).tail.tail.tail.tail
      ((unpack s).getD 2 [])]
  else [false]

theorem gropen_eq (π : PermFamily) (s : Bits) :
    (match unpack s with
      | m :: u :: pub :: privR :: comm => [(novy π).ropen m u comm privR pub]
      | _ => [false]) = gROpen π s := by
  unfold gROpen
  rcases unpack s with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, t⟩⟩⟩⟩
  · simp
  · simp
  · simp
  · simp
  · simp only [List.length_cons]
    rw [if_pos (by omega)]
    simp only [List.getD_cons_zero, List.getD_cons_succ, List.tail_cons]
    exact congrArg (fun b => [b]) (ropen_eq π a b t d c)

theorem poly_gROpen (π : PermFamily) (hP : Poly π.applyStr) : Poly (gROpen π) := by
  have h := poly_ropenG π hP
  unfold gROpen
  refine Poly.ite_prop (by fun_prop) ?_ (by fun_prop)
  have h2 := Poly.comp (f := fun x : ((Bits × Bits) × List Bits) × Bits => ropenG π x.1.1.1 x.1.1.2 x.1.2 x.2)
    (g := fun s => ((((unpack s).getD 0 [], (unpack s).getD 1 []), (unpack s).tail.tail.tail.tail),
        (unpack s).getD 2 [])) h (by fun_prop)
  exact Poly.comp (f := fun b : Bool => [b]) (by fun_prop) h2

end NovyPQZK.Main.PT


namespace NovyPQZK.Main.PT

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem polyTime_parts (π : PermFamily) (hπ : π.IsPolyTime) :
    PolyTimeFn (fun s => (novy π).setup s.length) ∧ PolyTimeNat (fun s => (novy π).rounds s.length) ∧
    PolyTimeFn (fun s => pack (((novy π).sender.coins s).map natToBits)) ∧
    PolyTimeFn (novy π).sender.next ∧
    PolyTimeFn (fun s => pack (((novy π).receiver.coins s).map natToBits)) ∧
    PolyTimeFn (novy π).receiver.next ∧
    PolyTimeFn (fun s => pack [((novy π).sopen s).1, ((novy π).sopen s).2]) ∧
    PolyTimeFn (fun s => match unpack s with
      | m :: u :: pub :: privR :: comm => [(novy π).ropen m u comm privR pub]
      | _ => [false]) := by
  have hP : Poly π.applyStr := poly_of_polyTimeFn hπ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : (fun s : Bits => (novy π).setup s.length) = gSetup := funext setup_eq
    rw [e]; exact polyTimeFn_of_poly poly_gSetup
  · have e : (fun s : Bits => unary ((novy π).rounds s.length)) = gSetup := by
      funext s; rw [← setup_eq]; congr 1; show max s.length 1 - 1 + 1 = _; omega
    unfold PolyTimeNat; rw [e]; exact polyTimeFn_of_poly poly_gSetup
  · have e : (fun s => pack (((novy π).sender.coins s).map natToBits)) = gSCoins :=
      funext (scoins_eq π)
    rw [e]; exact polyTimeFn_of_poly poly_gSCoins
  · have e : (novy π).sender.next = gSNext π := funext (snext_eq π)
    rw [e]; exact polyTimeFn_of_poly (poly_gSNext π hP)
  · have e : (fun s => pack (((novy π).receiver.coins s).map natToBits)) = gRCoins :=
      funext (rcoins_eq π)
    rw [e]; exact polyTimeFn_of_poly poly_gRCoins
  · have e : (novy π).receiver.next = gRNext := funext (rnext_eq π)
    rw [e]; exact polyTimeFn_of_poly poly_gRNext
  · have e : (fun s => pack [((novy π).sopen s).1, ((novy π).sopen s).2]) = gSOpen π :=
      funext (sopen_eq π)
    rw [e]; exact polyTimeFn_of_poly (poly_gSOpen π hP)
  · have e : (fun s => match unpack s with
        | m :: u :: pub :: privR :: comm => [(novy π).ropen m u comm privR pub]
        | _ => [false]) = gROpen π := funext (gropen_eq π)
    rw [e]; exact polyTimeFn_of_poly (poly_gROpen π hP)

end NovyPQZK.Main.PT


namespace NovyPQZK.Main

theorem novy_isBit (π : PermFamily) : (novy π).IsBit := fun _ => rfl

open QAlgorithms
open scoped Matrix

/-! ## Generic algebra of `embedOp`, permutation matrices, and fresh ancillas -/

/-- The permutation matrix of `φ` on basis states. -/
def permOf {N : ℕ} (φ : Qubits N → Qubits N) : Matrix (Qubits N) (Qubits N) ℂ :=
  Matrix.of fun y z => if y = φ z then 1 else 0

theorem permOf_mul {N : ℕ} (φ ψ : Qubits N → Qubits N) :
    permOf φ * permOf ψ = permOf (φ ∘ ψ) := by
  ext y z
  simp only [permOf, Matrix.mul_apply, Matrix.of_apply, Function.comp_apply, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (ψ z)]
  simp

theorem permOf_id {N : ℕ} : permOf (N := N) id = 1 := by
  ext y z
  simp [permOf, Matrix.one_apply]

theorem permOf_conjTranspose {N : ℕ} (φ : Qubits N → Qubits N) (hφ : ∀ z, φ (φ z) = z) :
    (permOf φ)ᴴ = permOf φ := by
  ext y z
  simp only [permOf, Matrix.conjTranspose_apply, Matrix.of_apply]
  have : (z = φ y) ↔ (y = φ z) := ⟨fun h => by rw [h, hφ], fun h => by rw [h, hφ]⟩
  by_cases h : y = φ z
  · rw [if_pos (this.2 h), if_pos h]; simp
  · rw [if_neg (fun h' => h (this.1 h')), if_neg h]; simp

theorem permOf_conj_apply {N : ℕ} (φ : Qubits N → Qubits N) (hφ : ∀ z, φ (φ z) = z)
    (M : Matrix (Qubits N) (Qubits N) ℂ) (y z : Qubits N) :
    (permOf φ * M * (permOf φ)ᴴ) y z = M (φ y) (φ z) := by
  rw [permOf_conjTranspose φ hφ, Matrix.mul_apply]
  have h1 : ∀ x, (permOf φ * M) y x = M (φ y) x := by
    intro x
    rw [Matrix.mul_apply]
    have : ∀ w, permOf φ y w * M w x = if w = φ y then M (φ y) x else 0 := by
      intro w
      simp only [permOf, Matrix.of_apply]
      by_cases hw : w = φ y
      · subst hw; rw [if_pos (hφ y).symm, if_pos rfl, one_mul]
      · rw [if_neg hw, if_neg (fun h => hw (by rw [h, hφ])), zero_mul]
    simp_rw [this]
    simp
  simp_rw [h1]
  simp only [permOf, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  simp

theorem permOf_unitary {N : ℕ} (φ : Qubits N → Qubits N) (hφ : ∀ z, φ (φ z) = z) :
    permOf φ ∈ Matrix.unitaryGroup (Qubits N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, permOf_conjTranspose φ hφ,
    permOf_mul]
  have : φ ∘ φ = id := funext hφ
  rw [this, permOf_id]

theorem embedOp_mul {m n : ℕ} (A B : Matrix (Qubits m) (Qubits m) ℂ)
    (w : Fin m ↪ Fin n) :
    embedOp (A * B) w = embedOp A w * embedOp B w := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.mul_apply]
  by_cases hyz : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · rw [if_pos hyz]
    have hsum : (∑ x : Qubits n,
        (if ∀ a : Fin n, a ∉ Set.range w → y a = x a then A (y ∘ w) (x ∘ w) else 0) *
          (if ∀ a : Fin n, a ∉ Set.range w → x a = z a then B (x ∘ w) (z ∘ w) else 0)) =
        ∑ x : Qubits n,
          if ∀ a : Fin n, a ∉ Set.range w → y a = x a then
            A (y ∘ w) (x ∘ w) * B (x ∘ w) (z ∘ w) else 0 := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases hyx : ∀ a : Fin n, a ∉ Set.range w → y a = x a
      · have hxz : ∀ a : Fin n, a ∉ Set.range w → x a = z a := fun a ha =>
          (hyx a ha).symm.trans (hyz a ha)
        rw [if_pos hyx, if_pos hxz, if_pos hyx]
      · rw [if_neg hyx, zero_mul, if_neg hyx]
    rw [hsum, ← Finset.sum_filter]
    symm
    refine Finset.sum_bij (fun x _ => x ∘ w)
      (fun _ _ => Finset.mem_univ _)
      (fun x₁ hx₁ x₂ hx₂ h => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
        funext a
        by_cases ha : a ∈ Set.range w
        · rcases ha with ⟨b, rfl⟩
          exact congrFun h b
        · exact (hx₁ a ha).symm.trans (hx₂ a ha))
      (fun x' _ => by
        refine ⟨fun a => if h : ∃ b : Fin m, w b = a then x' (Classical.choose h) else y a, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro a ha
          have hnot : ¬ ∃ b : Fin m, w b = a := by simpa [Set.mem_range] using ha
          simp [hnot]
        · funext b
          have h : ∃ b' : Fin m, w b' = w b := ⟨b, rfl⟩
          simp only [Function.comp_apply, h, ↓reduceDIte]
          exact congrArg x' (w.injective (Classical.choose_spec h)))
      (fun _ _ => rfl)
  · rw [if_neg hyz]
    symm
    refine Finset.sum_eq_zero (fun x _ => ?_)
    by_cases hyx : ∀ a : Fin n, a ∉ Set.range w → y a = x a
    · have hxz : ¬ ∀ a : Fin n, a ∉ Set.range w → x a = z a := fun hxz =>
        hyz (fun a ha => (hyx a ha).trans (hxz a ha))
      rw [if_neg hxz, mul_zero]
    · rw [if_neg hyx, zero_mul]

theorem embedOp_trans {k m n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (u : Fin k ↪ Fin m) (w : Fin m ↪ Fin n) :
    embedOp (embedOp M u) w = embedOp M (u.trans w) := by
  ext y z
  simp only [embedOp, Matrix.of_apply]
  by_cases hR : ∀ a : Fin n, a ∉ Set.range (u.trans w) → y a = z a
  · rw [if_pos hR]
    have hw : ∀ a : Fin n, a ∉ Set.range w → y a = z a := by
      intro a ha
      apply hR a
      rintro ⟨c, hc⟩
      exact ha ⟨u c, hc⟩
    have hu : ∀ b : Fin m, b ∉ Set.range u → y (w b) = z (w b) := by
      intro b hb
      apply hR (w b)
      rintro ⟨c, hc⟩
      exact hb ⟨c, w.injective hc⟩
    rw [if_pos hw]
    change (if ∀ b : Fin m, b ∉ Set.range u → y (w b) = z (w b)
      then M (y ∘ u.trans w) (z ∘ u.trans w) else 0) = _
    rw [if_pos hu]
  · rw [if_neg hR]
    simp only [not_forall] at hR
    rcases hR with ⟨a, ha, hne⟩
    by_cases haw : a ∈ Set.range w
    · rcases haw with ⟨b, rfl⟩
      have hbu : b ∉ Set.range u := by
        rintro ⟨c, rfl⟩
        exact ha ⟨c, rfl⟩
      by_cases hw : ∀ a : Fin n, a ∉ Set.range w → y a = z a
      · rw [if_pos hw]
        change (if ∀ b : Fin m, b ∉ Set.range u → y (w b) = z (w b)
          then M (y ∘ u.trans w) (z ∘ u.trans w) else 0) = 0
        rw [if_neg (fun hu => hne (hu b hbu))]
      · rw [if_neg hw]
    · rw [if_neg (fun hw => hne (hw a haw))]

theorem embedOp_conjTranspose {k n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    (embedOp M w)ᴴ = embedOp Mᴴ w := by
  ext y z
  simp only [embedOp, Matrix.conjTranspose_apply, Matrix.of_apply]
  have : (∀ a : Fin n, a ∉ Set.range w → z a = y a) ↔ (∀ a : Fin n, a ∉ Set.range w → y a = z a) :=
    ⟨fun h a ha => (h a ha).symm, fun h a ha => (h a ha).symm⟩
  by_cases h : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · rw [if_pos (this.2 h), if_pos h]
  · rw [if_neg (fun h' => h (this.1 h')), if_neg h, star_zero]

theorem circuit_unitary_cons {N : ℕ} (g : GateApp allSmallGates N) (c : QCircuit N) :
    Circuit.unitary (g :: c) = Circuit.unitary c * embedOp g.gate.mat g.wires := by
  simp [Circuit.unitary, List.reverse_cons, List.prod_append]

theorem circuit_unitary_append {N : ℕ} (c₁ c₂ : QCircuit N) :
    Circuit.unitary (c₁ ++ c₂) = Circuit.unitary c₂ * Circuit.unitary c₁ := by
  simp [Circuit.unitary, List.reverse_append, List.prod_append]

theorem circuit_unitary_nil {N : ℕ} : Circuit.unitary ([] : QCircuit N) = 1 := by
  simp [Circuit.unitary]

/-! ### The register with `m` fresh wires appended -/

section Lift
variable {N m N' : ℕ}

/-- The old wires inside the enlarged register. -/
def eL (h : N + m = N') : Fin N ↪ Fin N' :=
  ⟨fun i => ⟨i.val, by omega⟩, fun a b hab => by simpa [Fin.ext_iff] using hab⟩

/-- The fresh wires. -/
def fL (h : N + m = N') (j : Fin m) : Fin N' := ⟨N + j.val, by omega⟩

theorem eL_val (h : N + m = N') (i : Fin N) : (eL h i).val = i.val := rfl
theorem fL_val (h : N + m = N') (j : Fin m) : (fL h j).val = N + j.val := rfl

theorem eL_ne_fL (h : N + m = N') (i : Fin N) (j : Fin m) : eL h i ≠ fL h j := by
  intro hh; have := congrArg Fin.val hh; simp [eL_val, fL_val] at this; omega

/-- Splitting a basis state of the enlarged register. -/
def splitQ (h : N + m = N') : Qubits N' ≃ Qubits N × Qubits m where
  toFun z := (z ∘ eL h, z ∘ fL h)
  invFun p a := if ha : a.val < N then p.1 ⟨a.val, ha⟩ else p.2 ⟨a.val - N, by omega⟩
  left_inv z := by
    funext a
    by_cases ha : a.val < N
    · simp only [ha, ↓reduceDIte, Function.comp_apply]
      congr 1
    · simp only [ha, ↓reduceDIte, Function.comp_apply]
      congr 1; apply Fin.ext; simp [fL_val]; omega
  right_inv p := by
    obtain ⟨p, q⟩ := p
    ext i
    · simp [eL_val, i.isLt]
    · simp [fL_val]

theorem splitQ_apply (h : N + m = N') (z : Qubits N') : splitQ h z = (z ∘ eL h, z ∘ fL h) := rfl

theorem eq_iff_split (h : N + m = N') (y z : Qubits N') :
    y = z ↔ y ∘ eL h = z ∘ eL h ∧ y ∘ fL h = z ∘ fL h := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    apply (splitQ h).injective
    rw [splitQ_apply, splitQ_apply, h1, h2]

theorem offRange_iff (h : N + m = N') (y z : Qubits N') :
    (∀ a : Fin N', a ∉ Set.range (eL h) → y a = z a) ↔ y ∘ fL h = z ∘ fL h := by
  constructor
  · intro H; funext j
    apply H
    rintro ⟨i, hi⟩; exact eL_ne_fL h i j hi
  · intro H a ha
    have hN : ¬ a.val < N := fun hlt => ha ⟨⟨a.val, hlt⟩, Fin.ext rfl⟩
    have := congrFun H ⟨a.val - N, by omega⟩
    simp only [Function.comp_apply] at this
    have e : fL h ⟨a.val - N, by omega⟩ = a := by apply Fin.ext; simp [fL_val]; omega
    rwa [e] at this

/-- `ρ ⊗ σ`, `ρ` on the old wires and `σ` on the fresh ones. -/
def tens (h : N + m = N') (ρ : Matrix (Qubits N) (Qubits N) ℂ) (σ : Matrix (Qubits m) (Qubits m) ℂ) :
    Matrix (Qubits N') (Qubits N') ℂ :=
  Matrix.of fun y z => ρ (y ∘ eL h) (z ∘ eL h) * σ (y ∘ fL h) (z ∘ fL h)

theorem sum_split {M : Type*} [AddCommMonoid M] (h : N + m = N') (F : Qubits N' → M) :
    ∑ z, F z = ∑ p : Qubits N, ∑ q : Qubits m, F ((splitQ h).symm (p, q)) := by
  rw [← Fintype.sum_prod_type', ← (splitQ h).symm.sum_comp]

theorem split_symm_e (h : N + m = N') (p : Qubits N) (q : Qubits m) :
    (splitQ h).symm (p, q) ∘ eL h = p := by
  exact congrArg Prod.fst ((splitQ h).apply_symm_apply (p, q))

theorem split_symm_f (h : N + m = N') (p : Qubits N) (q : Qubits m) :
    (splitQ h).symm (p, q) ∘ fL h = q := by
  exact congrArg Prod.snd ((splitQ h).apply_symm_apply (p, q))

theorem embedOp_mul_tens (h : N + m = N') (A ρ : Matrix (Qubits N) (Qubits N) ℂ)
    (σ : Matrix (Qubits m) (Qubits m) ℂ) :
    embedOp A (eL h) * tens h ρ σ = tens h (A * ρ) σ := by
  ext y z
  rw [Matrix.mul_apply, sum_split h]
  simp only [embedOp, tens, Matrix.of_apply, offRange_iff, split_symm_e, split_symm_f,
    Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_eq_single (y ∘ fL h)]
  · simp only [if_true]; ring
  · intro q _ hq; rw [if_neg (Ne.symm hq)]; ring
  · simp

theorem tens_mul_embedOp (h : N + m = N') (ρ B : Matrix (Qubits N) (Qubits N) ℂ)
    (σ : Matrix (Qubits m) (Qubits m) ℂ) :
    tens h ρ σ * embedOp B (eL h) = tens h (ρ * B) σ := by
  ext y z
  rw [Matrix.mul_apply, sum_split h]
  simp only [embedOp, tens, Matrix.of_apply, offRange_iff, split_symm_e, split_symm_f,
    Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_eq_single (z ∘ fL h)]
  · simp only [if_true]; ring
  · intro q _ hq; rw [if_neg hq]; ring
  · simp

theorem trace_tens (h : N + m = N') (ρ : Matrix (Qubits N) (Qubits N) ℂ)
    (σ : Matrix (Qubits m) (Qubits m) ℂ) :
    (tens h ρ σ).trace = ρ.trace * σ.trace := by
  simp only [Matrix.trace, Matrix.diag, tens, Matrix.of_apply]
  rw [sum_split h, Finset.sum_mul_sum]
  simp only [split_symm_e, split_symm_f]

/-- A gate application moved to the enlarged register. -/
def liftGA (h : N + m = N') (g : GateApp allSmallGates N) : GateApp allSmallGates N' :=
  ⟨g.gate, g.mem, g.wires.trans (eL h)⟩

/-- A circuit moved to the enlarged register. -/
def liftCirc (h : N + m = N') (c : QCircuit N) : QCircuit N' := c.map (liftGA h)

theorem liftCirc_unitary (h : N + m = N') (c : QCircuit N) :
    (liftCirc h c).unitary = embedOp c.unitary (eL h) := by
  induction c with
  | nil => simp [liftCirc, circuit_unitary_nil, embedOp_one]
  | cons g c ih =>
    have : liftCirc h (g :: c) = liftGA h g :: liftCirc h c := rfl
    rw [this, circuit_unitary_cons, circuit_unitary_cons, ih, embedOp_mul, embedOp_trans]
    rfl

theorem flipMask_map_e (h : N + m = N') (w : List (Fin N)) (x : Bits) (i : Fin N) :
    flipMask (w.map (eL h)) x (eL h i) = flipMask w x i := by
  simp only [flipMask, List.zip_map_left, List.any_map]
  congr 1; funext p
  simp [(eL h).injective.eq_iff]

theorem flipMask_map_off (h : N + m = N') (w : List (Fin N)) (x : Bits) (a : Fin N')
    (ha : a ∉ Set.range (eL h)) : flipMask (w.map (eL h)) x a = false := by
  simp only [flipMask, List.zip_map_left, List.any_map, List.any_eq_false]
  intro p _
  have : eL h p.1 ≠ a := fun hh => ha ⟨p.1, hh⟩
  simp [this]

theorem loadX_map (h : N + m = N') (w : List (Fin N)) (x : Bits) :
    loadX (w.map (eL h)) x = embedOp (loadX w x) (eL h) := by
  ext y z
  simp only [loadX, embedOp, Matrix.of_apply]
  have key : (y = fun a => xor (z a) (flipMask (w.map (eL h)) x a)) ↔
      ((∀ a : Fin N', a ∉ Set.range (eL h) → y a = z a) ∧
        (y ∘ eL h = fun a => xor ((z ∘ eL h) a) (flipMask w x a))) := by
    constructor
    · intro hy
      refine ⟨fun a ha => ?_, ?_⟩
      · rw [hy]; simp [flipMask_map_off h w x a ha]
      · funext i; rw [hy]; simp [flipMask_map_e]
    · rintro ⟨h1, h2⟩
      funext a
      by_cases ha : a ∈ Set.range (eL h)
      · obtain ⟨i, rfl⟩ := ha
        have := congrFun h2 i
        simp only [Function.comp_apply] at this
        rw [this, flipMask_map_e]
      · rw [h1 a ha, flipMask_map_off h w x a ha]; simp
  by_cases H : y = fun a => xor (z a) (flipMask (w.map (eL h)) x a)
  · rw [if_pos H, if_pos (key.1 H).1, if_pos (key.1 H).2]
  · rw [if_neg H]
    by_cases H1 : ∀ a : Fin N', a ∉ Set.range (eL h) → y a = z a
    · rw [if_pos H1, if_neg (fun H2 => H (key.2 ⟨H1, H2⟩))]
    · rw [if_neg H1]

theorem outcomeProj_map (h : N + m = N') (w : List (Fin N)) (c : Bits) :
    outcomeProj (w.map (eL h)) c = embedOp (outcomeProj w c) (eL h) := by
  ext y z
  simp only [outcomeProj, diagProj, embedOp, Matrix.of_apply, Matrix.diagonal_apply, readWires,
    List.map_map, offRange_iff]
  by_cases hyz : y = z
  · subst hyz; simp only [if_true]; split_ifs <;> simp_all
  · rw [if_neg hyz]
    rw [eq_iff_split h] at hyz
    by_cases h2 : y ∘ fL h = z ∘ fL h
    · rw [if_pos h2, if_neg (fun h1 => hyz ⟨h1, h2⟩)]
    · rw [if_neg h2]

theorem loadX_nil' {N : ℕ} (w : List (Fin N)) : loadX w [] = 1 := by
  ext y z
  simp [loadX, flipMask, Matrix.one_apply]

/-- A step moved to the enlarged register. -/
def liftStep (h : N + m = N') (s : RoundStep N) : RoundStep N' :=
  ⟨s.inW.map (eL h), liftCirc h s.circ, s.outW.map (eL h)⟩

theorem liftStep_op (h : N + m = N') (s : RoundStep N) (x : Bits) :
    (liftStep h s).op x = embedOp (s.op x) (eL h) := by
  simp only [RoundStep.op, liftStep, liftCirc_unitary, loadX_map, embedOp_mul]

theorem stepDM_lift (h : N + m = N') (s : RoundStep N) (x o : Bits)
    (ρ : Matrix (Qubits N) (Qubits N) ℂ) (σ : Matrix (Qubits m) (Qubits m) ℂ) :
    stepDM (liftStep h s) x o (tens h ρ σ) = tens h (stepDM s x o ρ) σ := by
  simp only [stepDM, liftStep_op, embedOp_conjTranspose]
  have hP : outcomeProj (liftStep h s).outW o = embedOp (outcomeProj s.outW o) (eL h) :=
    outcomeProj_map h s.outW o
  rw [hP, ← embedOp_mul, embedOp_mul_tens, tens_mul_embedOp, tens_mul_embedOp]

end Lift
/-! ### CNOT copies of measured wires onto fresh ancillas -/

section Copy
variable {N N' : ℕ}

def cnotFun {n : ℕ} (a t : Fin n) (x : Qubits n) : Qubits n :=
  fun k => if k = t then xor (x t) (x a) else x k

theorem cnot_mat_eq :
    ((Gate.ofMatrix2 cnot).mat : Matrix (Qubits 2) (Qubits 2) ℂ) = permOf (N := 2) (cnotFun 0 1) := by
  show cnot.submatrix (fun b : Qubits 2 => (b 0, b 1)) (fun b => (b 0, b 1)) = permOf (cnotFun 0 1)
  ext y z
  simp only [cnot, permOf, Matrix.submatrix_apply, Matrix.of_apply]
  have key : (y 0 = z 0 ∧ y 1 = xor (z 1) (z 0)) ↔ y = cnotFun 0 1 z := by
    constructor
    · rintro ⟨h0, h1⟩; funext k; fin_cases k <;> simp [cnotFun, h0, h1]
    · intro hh; rw [hh]; simp [cnotFun]
  by_cases H : y = cnotFun 0 1 z
  · rw [if_pos H, if_pos (key.2 H)]
  · rw [if_neg H, if_neg (fun hh => H (key.1 hh))]

theorem cnotFun_invol {n : ℕ} (a t : Fin n) (hat : a ≠ t) (x : Qubits n) :
    cnotFun a t (cnotFun a t x) = x := by
  funext k
  by_cases hkt : k = t
  · subst hkt; simp [cnotFun, hat]
  · simp [cnotFun, hkt]

theorem cnot_mem : Gate.ofMatrix2 cnot ∈ allSmallGates := by
  refine ⟨le_refl _, ?_⟩
  show (Gate.ofMatrix2 cnot).mat ∈ _
  rw [cnot_mat_eq]
  exact permOf_unitary (N := 2) _ (cnotFun_invol (0 : Fin 2) 1 (by decide))

def cnotWires {n : ℕ} (a t : Fin n) (hat : a ≠ t) : Fin 2 ↪ Fin n :=
  ⟨![a, t], by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij hat
    · exact absurd hij.symm hat
    · rfl⟩

def cnotGA {n : ℕ} (a t : Fin n) (hat : a ≠ t) : GateApp allSmallGates n :=
  ⟨Gate.ofMatrix2 cnot, cnot_mem, cnotWires a t hat⟩

theorem embedOp_cnot2 {n : ℕ} (a t : Fin n) (hat : a ≠ t) :
    embedOp (permOf (N := 2) (cnotFun 0 1)) (cnotWires a t hat) = permOf (cnotFun a t) := by
  ext y z
  simp only [embedOp, permOf, Matrix.of_apply]
  have hw0 : cnotWires a t hat 0 = a := rfl
  have hw1 : cnotWires a t hat 1 = t := rfl
  have hc : ((∀ k : Fin n, k ∉ Set.range (cnotWires a t hat) → y k = z k) ∧
      (y ∘ cnotWires a t hat = cnotFun 0 1 (z ∘ cnotWires a t hat))) ↔ y = cnotFun a t z := by
    constructor
    · rintro ⟨hk, h2⟩
      have ha := congrFun h2 0
      have ht := congrFun h2 1
      simp only [Function.comp_apply, cnotFun, hw0, hw1] at ha ht
      simp at ha ht
      funext k
      by_cases hkt : k = t
      · subst hkt; simp [cnotFun, ht]
      · by_cases hka : k = a
        · subst hka; simp [cnotFun, hat, ha]
        · have hnot : k ∉ Set.range (cnotWires a t hat) := by
            rintro ⟨i, hi⟩
            fin_cases i
            · exact hka hi.symm
            · exact hkt hi.symm
          simp [cnotFun, hkt, hk k hnot]
    · intro hz
      subst hz
      refine ⟨?_, ?_⟩
      · intro k hk
        have hkt : k ≠ t := fun hh => hk ⟨1, by rw [hw1, hh]⟩
        simp [cnotFun, hkt]
      · funext i
        fin_cases i
        · simp [cnotFun, hw0, hw1, hat]
        · simp [cnotFun, hw0, hw1]
  by_cases H : y = cnotFun a t z
  · rw [if_pos (hc.2 H).1, if_pos (hc.2 H).2, if_pos H]
  · rw [if_neg H]
    by_cases H1 : ∀ k : Fin n, k ∉ Set.range (cnotWires a t hat) → y k = z k
    · rw [if_pos H1, if_neg (fun H2 => H (hc.1 ⟨H1, H2⟩))]
    · rw [if_neg H1]

theorem embedOp_cnotGA {n : ℕ} (a t : Fin n) (hat : a ≠ t) :
    embedOp (cnotGA a t hat).gate.mat (cnotGA a t hat).wires = permOf (cnotFun a t) :=
  (congrArg (fun M : Matrix (Qubits 2) (Qubits 2) ℂ => embedOp M (cnotWires a t hat)) cnot_mat_eq).trans
    (embedOp_cnot2 a t hat)


/-- The CNOT from old wire `dW[j]` to fresh wire `j`. -/
def copyGA {dW : List (Fin N)} (h : N + dW.length = N') (j : Fin dW.length) :
    GateApp allSmallGates N' :=
  cnotGA (eL h (dW.get j)) (fL h j) (eL_ne_fL h _ _)

def copyFun {dW : List (Fin N)} (h : N + dW.length = N') :
    List (Fin dW.length) → Qubits N' → Qubits N'
  | [] => id
  | j :: l => copyFun h l ∘ cnotFun (eL h (dW.get j)) (fL h j)

theorem copy_unitary {dW : List (Fin N)} (h : N + dW.length = N') (l : List (Fin dW.length)) :
    Circuit.unitary (l.map (copyGA h)) = permOf (copyFun h l) := by
  induction l with
  | nil => simp [circuit_unitary_nil, copyFun, permOf_id]
  | cons j l ih =>
    rw [List.map_cons, circuit_unitary_cons, ih, copyGA, embedOp_cnotGA, permOf_mul]
    rfl

theorem copyFun_e {dW : List (Fin N)} (h : N + dW.length = N') (l : List (Fin dW.length))
    (z : Qubits N') (i : Fin N) : copyFun h l z (eL h i) = z (eL h i) := by
  induction l generalizing z with
  | nil => rfl
  | cons j l ih =>
    show copyFun h l (cnotFun _ _ z) (eL h i) = _
    rw [ih]
    simp [cnotFun, eL_ne_fL]

theorem copyFun_f {dW : List (Fin N)} (h : N + dW.length = N') (l : List (Fin dW.length))
    (hl : l.Nodup) (z : Qubits N') (j : Fin dW.length) :
    copyFun h l z (fL h j) =
      if j ∈ l then xor (z (fL h j)) (z (eL h (dW.get j))) else z (fL h j) := by
  induction l generalizing z with
  | nil => simp [copyFun]
  | cons k l ih =>
    rw [List.nodup_cons] at hl
    show copyFun h l (cnotFun _ _ z) (fL h j) = _
    rw [ih hl.2]
    have hf : ∀ a b : Fin dW.length, fL h a = fL h b ↔ a = b := by
      intro a b; constructor
      · intro hh; have := congrArg Fin.val hh; simp [fL_val] at this; exact Fin.ext this
      · rintro rfl; rfl
    by_cases hjk : j = k
    · subst hjk
      simp [hl.1, cnotFun, eL_ne_fL]
    · have hjk' : fL h j ≠ fL h k := fun hh => hjk ((hf j k).1 hh)
      by_cases hjl : j ∈ l
      · simp [hjl, cnotFun, hjk', eL_ne_fL]
      · simp [hjl, hjk, cnotFun, hjk']

/-- The full copy circuit. -/
def copyCirc {dW : List (Fin N)} (h : N + dW.length = N') : QCircuit N' :=
  (List.finRange dW.length).map (copyGA h)

/-- What the copy circuit does on basis states. -/
def copyAll {dW : List (Fin N)} (h : N + dW.length = N') : Qubits N' → Qubits N' :=
  copyFun h (List.finRange dW.length)

theorem copyAll_e {dW : List (Fin N)} (h : N + dW.length = N') (z : Qubits N') :
    copyAll h z ∘ eL h = z ∘ eL h := funext fun i => copyFun_e h _ z i

theorem copyAll_f {dW : List (Fin N)} (h : N + dW.length = N') (z : Qubits N') :
    copyAll h z ∘ fL h = fun j => xor (z (fL h j)) (z (eL h (dW.get j))) := by
  funext j
  simp only [Function.comp_apply, copyAll]
  rw [copyFun_f h _ (List.nodup_finRange _)]
  simp

theorem copyAll_invol {dW : List (Fin N)} (h : N + dW.length = N') (z : Qubits N') :
    copyAll h (copyAll h z) = z := by
  rw [eq_iff_split h]
  refine ⟨by rw [copyAll_e, copyAll_e], ?_⟩
  rw [copyAll_f]
  funext j
  have h1 := congrFun (copyAll_f h z) j
  have h2 := congrFun (copyAll_e h z) (dW.get j)
  simp only [Function.comp_apply] at h1 h2
  show xor (copyAll h z (fL h j)) (copyAll h z (eL h (dW.get j))) = z (fL h j)
  rw [h1, h2]; simp

theorem copyCirc_unitary {dW : List (Fin N)} (h : N + dW.length = N') :
    (copyCirc h).unitary = permOf (copyAll h) := copy_unitary h _

theorem readWires_eq_ofFn_iff (dW : List (Fin N)) (p : Qubits N) (d : Qubits dW.length) :
    readWires dW p = List.ofFn d ↔ (fun j => p (dW.get j)) = d := by
  have : readWires dW p = List.ofFn (fun j => p (dW.get j)) := by
    simp only [readWires]
    conv_lhs => rw [← List.ofFn_get dW]
    rw [List.map_ofFn]; rfl
  rw [this, List.ofFn_inj]

theorem trace_diag_sandwich {n : ℕ} (a : Qubits n → ℂ) (X M : Matrix (Qubits n) (Qubits n) ℂ) :
    (Matrix.diagonal a * X * Matrix.diagonal a * M).trace =
      ∑ p, ∑ p', a p * X p p' * a p' * M p' p := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun p' _ => ?_))
  rw [Finset.sum_mul, Finset.sum_eq_single p']
  · simp [Matrix.diagonal_apply]
  · intro b _ hb; simp [Matrix.diagonal_apply, hb]
  · simp

/-- Deferred measurement: copying the wires `dW` onto fresh ancillas in `|0⟩` and tracing them out
equals measuring `dW` and summing over the outcomes. -/
theorem deferred_trace {dW : List (Fin N)} (h : N + dW.length = N')
    (X A B : Matrix (Qubits N) (Qubits N) ℂ) :
    (embedOp A (eL h) * ((copyCirc h).unitary * tens h X (zeroDM dW.length) * ((copyCirc h).unitary)ᴴ)
        * embedOp B (eL h)).trace =
      ∑ d : Qubits dW.length,
        (A * outcomeProj dW (List.ofFn d) * X * outcomeProj dW (List.ofFn d) * B).trace := by
  set r : Qubits N → Qubits dW.length := fun p j => p (dW.get j) with hr
  -- entries of the copied state
  have hT : ∀ y z, ((copyCirc h).unitary * tens h X (zeroDM dW.length) * ((copyCirc h).unitary)ᴴ) y z
      = X (y ∘ eL h) (z ∘ eL h) * (if y ∘ fL h = r (y ∘ eL h) then 1 else 0) *
        (if z ∘ fL h = r (z ∘ eL h) then 1 else 0) := by
    intro y z
    rw [copyCirc_unitary, permOf_conj_apply _ (copyAll_invol h)]
    simp only [tens, Matrix.of_apply, copyAll_e, zeroDM, copyAll_f]
    have e1 : ∀ w : Qubits N', ((fun j => xor (w (fL h j)) (w (eL h (dW.get j)))) = fun _ => false)
        ↔ w ∘ fL h = r (w ∘ eL h) := by
      intro w
      constructor
      · intro hh; funext j; have := congrFun hh j; simp only [Function.comp_apply, hr]
        simpa using this
      · intro hh; funext j; have := congrFun hh j; simp only [Function.comp_apply, hr] at this
        simp [this]
    by_cases hy : y ∘ fL h = r (y ∘ eL h)
    · by_cases hz : z ∘ fL h = r (z ∘ eL h)
      · rw [if_pos ⟨(e1 y).2 hy, (e1 z).2 hz⟩, if_pos hy, if_pos hz]; ring
      · rw [if_neg (fun hh => hz ((e1 z).1 hh.2)), if_neg hz]; ring
    · rw [if_neg (fun hh => hy ((e1 y).1 hh.1)), if_neg hy]; ring
  -- left side
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← embedOp_mul]
  have lhs : ∀ (T : Matrix (Qubits N') (Qubits N') ℂ) (M : Matrix (Qubits N) (Qubits N) ℂ),
      (T * embedOp M (eL h)).trace = ∑ y, ∑ z, T y z * embedOp M (eL h) z y := by
    intro T M; simp [Matrix.trace, Matrix.mul_apply]
  rw [lhs]
  simp_rw [hT]
  rw [sum_split h]
  simp_rw [sum_split h (fun z => _ * embedOp _ _ z _)]
  simp only [split_symm_e, split_symm_f, embedOp, Matrix.of_apply, offRange_iff]
  calc _ = ∑ p, ∑ p', X p p' * (B * A) p' p * (if r p' = r p then 1 else 0) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun p' _ => ?_)
        rw [Finset.sum_eq_single (r p)]
        · rw [Finset.sum_eq_single (r p')]
          · by_cases hpp : r p' = r p <;> simp [hpp]
          · intro q _ hq; simp [hq]
          · simp
        · intro q _ hq; simp [hq]
        · simp
    _ = _ := by
        have rhs : ∀ d : Qubits dW.length,
            (A * outcomeProj dW (List.ofFn d) * X * outcomeProj dW (List.ofFn d) * B).trace =
              ∑ p : Qubits N, ∑ p' : Qubits N, (if r p = d then (1 : ℂ) else 0) * X p p' *
                (if r p' = d then 1 else 0) * (B * A) p' p := by
          intro d
          have e : A * outcomeProj dW (List.ofFn d) * X * outcomeProj dW (List.ofFn d) * B =
              A * (outcomeProj dW (List.ofFn d) * X * outcomeProj dW (List.ofFn d) * B) := by
            simp only [Matrix.mul_assoc]
          rw [e, Matrix.trace_mul_comm]
          have e2 : outcomeProj dW (List.ofFn d) * X * outcomeProj dW (List.ofFn d) * B * A =
              outcomeProj dW (List.ofFn d) * X * outcomeProj dW (List.ofFn d) * (B * A) := by
            simp only [Matrix.mul_assoc]
          rw [e2]
          simp only [outcomeProj, diagProj]
          rw [trace_diag_sandwich]
          simp only [readWires_eq_ofFn_iff]
          rfl
        simp_rw [rhs]
        symm
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun p' _ => ?_)
        rw [Finset.sum_eq_single (r p)]
        · by_cases hpp : r p' = r p <;> simp [hpp]
        · intro d _ hd; simp [Ne.symm hd]
        · simp

end Copy

/-! ### Runs -/

theorem runFrom_append (S : QStrategy) (msg : List Bits → Bits) (l₁ l₂ done : List Bits)
    (ρ : Matrix (Qubits S.N) (Qubits S.N) ℂ) :
    S.runFrom msg done (l₁ ++ l₂) ρ = S.runFrom msg (done ++ l₁) l₂ (S.runFrom msg done l₁ ρ) := by
  induction l₁ generalizing done ρ with
  | nil => simp [QStrategy.runFrom]
  | cons o l ih =>
    simp only [List.cons_append, QStrategy.runFrom]
    rw [ih]; simp

theorem runFrom_lift {m : ℕ} (S S' : QStrategy) (h : S.N + m = S'.N) (K : ℕ)
    (hstep : ∀ j < K, S'.stepAt j = liftStep h (S.stepAt j)) (msg msg' : List Bits → Bits)
    (hmsg : ∀ d : List Bits, d.length < K → msg' d = msg d)
    (σ : Matrix (Qubits m) (Qubits m) ℂ) :
    ∀ (os done : List Bits) (ρ : Matrix (Qubits S.N) (Qubits S.N) ℂ), done.length + os.length ≤ K →
      S'.runFrom msg' done os (tens h ρ σ) = tens h (S.runFrom msg done os ρ) σ := by
  intro os
  induction os with
  | nil => intro done ρ _; simp [QStrategy.runFrom]
  | cons o rest ih =>
    intro done ρ hl
    simp only [List.length_cons] at hl
    simp only [QStrategy.runFrom]
    rw [hstep _ (by omega), hmsg _ (by omega), stepDM_lift]
    exact ih _ _ (by simp; omega)

section PSD
open scoped ComplexOrder

theorem initDM_zero_psd (S : QStrategy) : (S.initDM (zeroDM S.inQ)).PosSemidef := by
  have : S.initDM (zeroDM S.inQ) = Matrix.vecMulVec
      (fun y => (if fstPart y = (fun _ => false) then 1 else 0) * S.advice (sndPart y))
      (star fun y => (if fstPart y = (fun _ => false) then 1 else 0) * S.advice (sndPart y)) := by
    ext y z
    simp only [QStrategy.initDM, zeroDM, Matrix.of_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      star_mul']
    by_cases hy : fstPart y = (fun _ => false)
    · by_cases hz : fstPart z = (fun _ => false)
      · simp [hy, hz]
        try ring
      · simp [hy, hz]
    · simp [hy]
  rw [this]
  exact Matrix.posSemidef_vecMulVec_self_star _

theorem outcomeProj_conjTranspose {N : ℕ} (w : List (Fin N)) (c : Bits) :
    (outcomeProj w c)ᴴ = outcomeProj w c := by
  simp only [outcomeProj, diagProj, Matrix.diagonal_conjTranspose]
  congr 1; funext z; simp only [Pi.star_apply]; split_ifs <;> simp

theorem stepDM_psd {N : ℕ} (s : RoundStep N) (x o : Bits) {ρ : Matrix (Qubits N) (Qubits N) ℂ}
    (hρ : ρ.PosSemidef) : (stepDM s x o ρ).PosSemidef := by
  have : stepDM s x o ρ = (outcomeProj s.outW o * s.op x) * ρ * (outcomeProj s.outW o * s.op x)ᴴ := by
    simp only [stepDM, Matrix.conjTranspose_mul, outcomeProj_conjTranspose, Matrix.mul_assoc]
  rw [this]
  exact hρ.mul_mul_conjTranspose_same _

theorem runFrom_psd (S : QStrategy) (msg : List Bits → Bits) :
    ∀ (os done : List Bits) {ρ : Matrix (Qubits S.N) (Qubits S.N) ℂ}, ρ.PosSemidef →
      (S.runFrom msg done os ρ).PosSemidef := by
  intro os
  induction os with
  | nil => intro done ρ hρ; simpa [QStrategy.runFrom] using hρ
  | cons o rest ih =>
    intro done ρ hρ
    simp only [QStrategy.runFrom]
    exact ih _ (stepDM_psd _ _ _ hρ)

theorem run_trace_nonneg (S : QStrategy) (msg : List Bits → Bits) (os : List Bits) :
    0 ≤ (S.run msg (zeroDM S.inQ) os).trace.re := by
  have := (runFrom_psd S msg os [] (initDM_zero_psd S)).trace_nonneg
  exact (Complex.nonneg_iff.1 this).1

end PSD



/-! ## Sums over measurement outcomes as sums over strings of given lengths -/

/-- `∑` over lists of strings with prescribed lengths. -/
noncomputable def lensSum : List ℕ → (List Bits → ℝ) → ℝ
  | [], F => F []
  | a :: l, F => ∑ x : Qubits a, lensSum l (fun t => F (List.ofFn x :: t))

theorem sum_outs_eq (r : ℕ) : ∀ (g : ℕ → ℕ) (F : List Bits → ℝ),
    ∑ o : ((j : Fin r) → Qubits (g j)), F (List.ofFn fun j => List.ofFn (o j)) =
      lensSum ((List.range r).map g) F := by
  induction r with
  | zero => intro g F; simp [lensSum]
  | succ r ih =>
    intro g F
    rw [← (Fin.consEquiv (fun j : Fin (r + 1) => Qubits (g j))).sum_comp, Fintype.sum_prod_type]
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [lensSum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have := ih (fun k => g (k + 1)) (fun t => F (List.ofFn x :: t))
    simp only [List.ofFn_succ, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
    convert this using 2
    all_goals rfl

theorem sum_outs_eq' (S : QStrategy) (r : ℕ) (F : List Bits → ℝ) :
    ∑ o : S.Outs r, F (QStrategy.outList o) =
      lensSum ((List.range r).map fun j => (S.stepAt j).outW.length) F :=
  sum_outs_eq r (fun j => (S.stepAt j).outW.length) F

theorem lensSum_append (l₁ l₂ : List ℕ) : ∀ F : List Bits → ℝ,
    lensSum (l₁ ++ l₂) F = lensSum l₁ (fun p => lensSum l₂ (fun q => F (p ++ q))) := by
  induction l₁ with
  | nil => intro F; simp [lensSum]
  | cons a l ih => intro F; simp only [List.cons_append, lensSum, ih]

theorem lensSum_mono (l : List ℕ) : ∀ F G : List Bits → ℝ,
    (∀ p : List Bits, p.length = l.length → F p ≤ G p) → lensSum l F ≤ lensSum l G := by
  induction l with
  | nil => intro F G h; exact h [] rfl
  | cons a l ih =>
    intro F G h
    simp only [lensSum]
    refine Finset.sum_le_sum (fun x _ => ih _ _ (fun p hp => h _ (by simp [hp])))

theorem lensSum_add (l : List ℕ) : ∀ F G : List Bits → ℝ,
    lensSum l (fun p => F p + G p) = lensSum l F + lensSum l G := by
  induction l with
  | nil => intro F G; rfl
  | cons a l ih =>
    intro F G
    simp only [lensSum]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => ih _ _)

theorem lensSum_congr (l : List ℕ) : ∀ F G : List Bits → ℝ,
    (∀ p : List Bits, p.length = l.length → F p = G p) → lensSum l F = lensSum l G := by
  intro F G h
  exact le_antisymm (lensSum_mono l F G (fun p hp => (h p hp).le))
    (lensSum_mono l G F (fun p hp => (h p hp).ge))

theorem lensSum_single (a : ℕ) (F : List Bits → ℝ) :
    lensSum [a] F = ∑ x : Qubits a, F [List.ofFn x] := rfl

/-! ## Structure of packed strings -/

theorem packOne_nil : packOne [] = [false] := rfl

theorem packOne_cons (b : Bool) (u : Bits) : packOne (b :: u) = true :: b :: packOne u := by
  simp [packOne]

theorem packOne_length (u : Bits) : (packOne u).length = 2 * u.length + 1 := by
  induction u with
  | nil => rfl
  | cons b u ih => rw [packOne_cons]; simp [ih]; ring

theorem unpackAux_cons_spec : ∀ (s cur u : Bits) (rest : List Bits), unpackAux s cur = u :: rest →
    ∃ v s', u = cur.reverse ++ v ∧ s = packOne v ++ s' ∧ unpackAux s' [] = rest := by
  intro s cur
  induction s, cur using unpackAux.induct with
  | case1 cur => intro u rest h; simp [unpackAux] at h
  | case2 rest' cur =>
    intro u rest h
    simp only [unpackAux, List.cons.injEq] at h
    exact ⟨[], rest', by simp [h.1], by simp [packOne_nil], h.2⟩
  | case3 b rest' cur ih =>
    intro u rest h
    simp only [unpackAux] at h
    obtain ⟨v, s', hu, hs, hr⟩ := ih u rest h
    refine ⟨b :: v, s', by simp [hu], by rw [hs, packOne_cons]; rfl, hr⟩
  | case4 cur => intro u rest h; simp [unpackAux] at h

theorem pack_two_ne_nil (x y : Bits) : pack [x, y] ≠ [] := by
  simp [pack, packOne]

/-- If the first two items of `unpack s` are nonempty, `s` begins with their encodings. -/
theorem unpack_two_prefix (s u0 u1 : Bits) (h0 : (unpack s).getD 0 [] = u0)
    (h1 : (unpack s).getD 1 [] = u1) (hu0 : u0 ≠ []) (hu1 : u1 ≠ []) :
    ∃ t, s = packOne u0 ++ packOne u1 ++ t := by
  unfold unpack at h0 h1
  rcases hs : unpackAux s [] with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · rw [hs] at h0; simp at h0; exact absurd h0 hu0
  · rw [hs] at h1; simp at h1; exact absurd h1 hu1
  · rw [hs] at h0 h1
    simp at h0 h1
    subst h0; subst h1
    obtain ⟨v, s', hv, hs', hr⟩ := unpackAux_cons_spec s [] a (b :: rest) hs
    obtain ⟨v', t, hv', ht, _⟩ := unpackAux_cons_spec s' [] b rest hr
    simp at hv hv'
    subst hv; subst hv'
    exact ⟨t, by rw [hs', ht, List.append_assoc]⟩

theorem packOne_getD_even (u t : Bits) : ∀ j, j < u.length →
    (packOne u ++ t).getD (2 * j) false = true := by
  induction u with
  | nil => intro j hj; simp at hj
  | cons b u ih =>
    intro j hj
    rw [packOne_cons]
    rcases j with _ | j
    · rfl
    · have e : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
      rw [e]
      simp only [List.cons_append, List.getD_cons_succ]
      exact ih j (by simp at hj; omega)

theorem packOne_getD_odd (u t : Bits) : ∀ j, j < u.length →
    (packOne u ++ t).getD (2 * j + 1) false = u.getD j false := by
  induction u with
  | nil => intro j hj; simp at hj
  | cons b u ih =>
    intro j hj
    rw [packOne_cons]
    rcases j with _ | j
    · rfl
    · have e : 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 := by ring
      rw [e]
      simp only [List.cons_append, List.getD_cons_succ]
      exact ih j (by simp at hj; omega)

theorem packOne_getD_end (u t : Bits) : (packOne u ++ t).getD (2 * u.length) false = false := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    rw [packOne_cons]
    have e : 2 * (b :: u).length = 2 * u.length + 1 + 1 := by simp; ring
    rw [e]
    simp only [List.cons_append, List.getD_cons_succ]
    exact ih

theorem getD_append_len (u t : Bits) (k : ℕ) : (u ++ t).getD (u.length + k) false = t.getD k false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

/-! ## Selecting the bits of `x` from `pack [pack [x, y], …]` -/

/-- Positions of `packOne x` inside `packOne (pack [x, y]) ++ …` (offset `o`): separators at
`o + 4i`, bits at `o + 4i + 3`, terminator at `o + 4|x| + 1`. -/
def bpos (o : ℕ) : ℕ → List ℕ
  | 0 => [o + 1]
  | k + 1 => o :: (o + 3) :: bpos (o + 4) k

theorem bpos_bounds : ∀ (k o p : ℕ), p ∈ bpos o k → o ≤ p ∧ p ≤ o + 4 * k + 1 := by
  intro k
  induction k with
  | zero => intro o p hp; simp [bpos] at hp; omega
  | succ k ih =>
    intro o p hp
    simp only [bpos, List.mem_cons] at hp
    rcases hp with rfl | rfl | hp
    · omega
    · omega
    · have := ih (o + 4) p hp; omega

theorem bpos_nodup : ∀ (k o : ℕ), (bpos o k).Nodup := by
  intro k
  induction k with
  | zero => intro o; simp [bpos]
  | succ k ih =>
    intro o
    simp only [bpos, List.nodup_cons, List.mem_cons]
    refine ⟨?_, ?_, ih _⟩
    · rintro (h | h)
      · omega
      · have := bpos_bounds k (o + 4) o h; omega
    · intro h; have := bpos_bounds k (o + 4) (o + 3) h; omega

theorem bpos_map (s : Bits) : ∀ (x : Bits) (o : ℕ),
    (∀ i, i < x.length → s.getD (o + 4 * i) false = true ∧ s.getD (o + 4 * i + 3) false = x.getD i false) →
    s.getD (o + 4 * x.length + 1) false = false →
    (bpos o x.length).map (fun p => s.getD p false) = packOne x := by
  intro x
  induction x with
  | nil =>
    intro o _ h
    simp only [List.length_nil, mul_zero, add_zero] at h
    simp only [List.length_nil, bpos, List.map_cons, List.map_nil, packOne_nil, h]
  | cons b x ih =>
    intro o h1 h2
    simp only [List.length_cons, bpos, List.map_cons, packOne_cons]
    have h0 := h1 0 (by simp)
    simp only [mul_zero, add_zero, List.getD_cons_zero] at h0
    rw [h0.1, h0.2]
    congr 2
    apply ih (o + 4)
    · intro i hi
      have := h1 (i + 1) (by simp; omega)
      have e1 : o + 4 * (i + 1) = o + 4 + 4 * i := by ring
      have e2 : o + 4 * (i + 1) + 3 = o + 4 + 4 * i + 3 := by ring
      rw [e1] at this
      simpa using this
    · have e : o + 4 * (x.length + 1) + 1 = o + 4 + 4 * x.length + 1 := by ring
      simp only [List.length_cons] at h2
      rw [e] at h2; exact h2

/-- Facts on `packOne (packOne x ++ packOne y) ++ t` at the positions of `bpos 0 |x|`. -/
theorem block_facts (x y t : Bits) :
    ∀ i, i < x.length →
      (packOne (packOne x ++ packOne y) ++ t).getD (0 + 4 * i) false = true ∧
      (packOne (packOne x ++ packOne y) ++ t).getD (0 + 4 * i + 3) false = x.getD i false := by
  intro i hi
  have hl : (packOne x ++ packOne y).length = 2 * x.length + 1 + (2 * y.length + 1) := by
    simp [packOne_length]
  constructor
  · have e : 0 + 4 * i = 2 * (2 * i) := by ring
    rw [e]; exact packOne_getD_even _ _ _ (by rw [hl]; omega)
  · have e : 0 + 4 * i + 3 = 2 * (2 * i + 1) + 1 := by ring
    rw [e, packOne_getD_odd _ _ _ (by rw [hl]; omega)]
    have := packOne_getD_odd x (packOne y) i hi
    exact this

theorem block_end (x y t : Bits) :
    (packOne (packOne x ++ packOne y) ++ t).getD (0 + 4 * x.length + 1) false = false := by
  have hl : (packOne x ++ packOne y).length = 2 * x.length + 1 + (2 * y.length + 1) := by
    simp [packOne_length]
  have e : 0 + 4 * x.length + 1 = 2 * (2 * x.length) + 1 := by ring
  rw [e, packOne_getD_odd _ _ _ (by rw [hl]; omega)]
  exact packOne_getD_end x (packOne y)

theorem block0_map (x y t : Bits) :
    (bpos 0 x.length).map (fun p => (packOne (packOne x ++ packOne y) ++ t).getD p false) = packOne x :=
  bpos_map _ x 0 (block_facts x y t) (block_end x y t)

theorem block_shift_map (pre s : Bits) (P : List ℕ) :
    (P.map (fun p => pre.length + p)).map (fun p => (pre ++ s).getD p false) =
      P.map (fun p => s.getD p false) := by
  simp only [List.map_map, Function.comp_def, getD_append_len]

/-- The positions selected, for the order `a` (`false`: `x₀` first). -/
def selPos (n : ℕ) (a : Bool) : List ℕ :=
  if a then (bpos 0 n).map (fun p => (8 * n + 5) + p) ++ bpos 0 n
  else bpos 0 n ++ (bpos 0 n).map (fun p => (8 * n + 5) + p)

theorem selPos_length (n : ℕ) (a : Bool) : (selPos n a).length = 4 * n + 2 := by
  have : ∀ k o, (bpos o k).length = 2 * k + 1 := by
    intro k; induction k with
    | zero => intro o; rfl
    | succ k ih => intro o; simp [bpos, ih]; ring
  cases a <;> simp [selPos, this] <;> ring

theorem selPos_bound (n : ℕ) (a : Bool) : ∀ p ∈ selPos n a, p < 16 * n + 10 := by
  intro p hp
  cases a
  · simp only [selPos, Bool.false_eq_true, if_false, List.mem_append, List.mem_map] at hp
    rcases hp with hp | ⟨q, hq, rfl⟩
    · have := bpos_bounds n 0 p hp; omega
    · have := bpos_bounds n 0 q hq; omega
  · simp only [selPos, if_true, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | hp
    · have := bpos_bounds n 0 q hq; omega
    · have := bpos_bounds n 0 p hp; omega

theorem selPos_nodup (n : ℕ) (a : Bool) : (selPos n a).Nodup := by
  have h1 := bpos_nodup n 0
  have h2 : ((bpos 0 n).map (fun p => (8 * n + 5) + p)).Nodup :=
    h1.map (fun a b hab => by simpa using hab)
  have hd : ∀ p ∈ bpos 0 n, ∀ q ∈ (bpos 0 n).map (fun p => (8 * n + 5) + p), p ≠ q := by
    intro p hp q hq
    simp only [List.mem_map] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    have := bpos_bounds n 0 p hp
    omega
  cases a
  · simp only [selPos, Bool.false_eq_true, if_false]
    exact List.nodup_append.2 ⟨h1, h2, fun p hp q hq => hd p hp q hq⟩
  · simp only [selPos, if_true]
    exact List.nodup_append.2 ⟨h2, h1, fun p hp q hq => (hd q hq p hp).symm⟩

/-- The selection from `pack [pack [x₀, y₀], pack [x₁, y₁]] ++ t` is `pack [x₀, x₁]` or
`pack [x₁, x₀]`. -/
theorem selPos_map (n : ℕ) (x0 y0 x1 y1 t : Bits) (hx0 : x0.length = n) (hy0 : y0.length = n)
    (hx1 : x1.length = n) (a : Bool) :
    (selPos n a).map (fun p => (packOne (pack [x0, y0]) ++ packOne (pack [x1, y1]) ++ t).getD p false) =
      if a then pack [x1, x0] else pack [x0, x1] := by
  have hlen : (packOne (pack [x0, y0])).length = 8 * n + 5 := by
    simp [packOne_length, pack, hx0, hy0]; ring
  have hp0 : pack [x0, y0] = packOne x0 ++ packOne y0 := by simp [pack]
  have hp1 : pack [x1, y1] = packOne x1 ++ packOne y1 := by simp [pack]
  have B0 : (bpos 0 n).map (fun p => (packOne (pack [x0, y0]) ++ packOne (pack [x1, y1]) ++ t).getD p false)
      = packOne x0 := by
    rw [List.append_assoc, hp0, ← hx0]; exact block0_map x0 y0 _
  have B1 : ((bpos 0 n).map (fun p => (8 * n + 5) + p)).map
      (fun p => (packOne (pack [x0, y0]) ++ packOne (pack [x1, y1]) ++ t).getD p false) = packOne x1 := by
    rw [← hlen, List.append_assoc, block_shift_map, hp1, ← hx1]; exact block0_map x1 y1 t
  cases a
  · simp only [selPos, Bool.false_eq_true, if_false, List.map_append, B0, B1]; simp [pack]
  · simp only [selPos, if_true, List.map_append, B0, B1]; simp [pack]

/-- Selecting measured wires by positions. -/
theorem filterMap_wires_read {α : Type*} (W : List α) (z : α → Bool) :
    ∀ P : List ℕ, (∀ p ∈ P, p < W.length) →
      (P.filterMap (fun p => W[p]?)).map z = P.map (fun p => (W.map z).getD p false) := by
  intro P
  induction P with
  | nil => intro _; rfl
  | cons p P ih =>
    intro hP
    have hp : p < W.length := hP p (by simp)
    simp only [List.filterMap_cons, List.getElem?_eq_getElem hp, List.map_cons]
    rw [ih (fun q hq => hP q (by simp [hq]))]
    congr 1
    simp [List.getD_eq_getElem?_getD, hp]

theorem filterMap_wires_nodup {α : Type*} (W : List α) (hW : W.Nodup) (P : List ℕ) (hP : P.Nodup) :
    (P.filterMap (fun p => W[p]?)).Nodup := by
  refine hP.filterMap ?_
  intro a a' b ha ha'
  simp only [Option.mem_def, List.getElem?_eq_some_iff] at ha ha'
  obtain ⟨h1, rfl⟩ := ha
  obtain ⟨h2, h3⟩ := ha'
  exact ((List.Nodup.getElem_inj_iff hW).1 h3).symm


/-! ## From partial -/

theorem unpackAux_packOne (x rest cur : Bits) :
    unpackAux (packOne x ++ rest) cur = (cur.reverse ++ x) :: unpackAux rest [] := by
  induction x generalizing cur with
  | nil => simp [packOne, unpackAux]
  | cons b x ih =>
    have : packOne (b :: x) ++ rest = true :: b :: (packOne x ++ rest) := by simp [packOne]
    rw [this, unpackAux, ih]; simp

theorem unpack_pack (l : List Bits) : unpack (pack l) = l := by
  induction l with
  | nil => simp [pack, unpack, unpackAux]
  | cons a l ih =>
    unfold unpack at ih ⊢
    have : pack (a :: l) = packOne a ++ pack l := by simp [pack]
    rw [this, unpackAux_packOne, ih]; simp

theorem unpackAux_sum_le (x cur : Bits) :
    ((unpackAux x cur).map List.length).sum ≤ x.length + cur.length := by
  induction x, cur using unpackAux.induct with
  | case1 cur => simp [unpackAux]
  | case2 rest cur ih => simp [unpackAux] at ih ⊢; omega
  | case3 b rest cur ih => simp [unpackAux] at ih ⊢; omega
  | case4 cur => simp [unpackAux]

theorem unpack_two_le {s m p : Bits} (h : unpack s = [m, p]) : m.length + p.length ≤ s.length := by
  have := unpackAux_sum_le s []
  unfold unpack at h; rw [h] at this; simpa using this

theorem msbStr_length (n v : ℕ) : (msbStr n v).length = n := by simp [msbStr]

theorem applyStr_length (π : PermFamily) (s : Bits) : (π.applyStr s).length = s.length := by
  simp [PermFamily.applyStr]

theorem pack_two_length (a b : Bits) : (pack [a, b]).length = 2 * a.length + 2 * b.length + 2 := by
  simp [pack, packOne]; ring

theorem applyStr_inj (π : PermFamily) {x x' : Bits} (hl : x.length = x'.length)
    (h : π.applyStr x = π.applyStr x') : x = x' := by
  have key : ∀ (a b : ℕ) (f : Fin a → Bool) (g : Fin b → Bool), a = b →
      List.ofFn (π a f) = List.ofFn (π b g) → List.ofFn f = List.ofFn g := by
    intro a b f g hab hfg
    subst hab
    have := List.ofFn_injective hfg
    rw [(π a).injective this]
  have := key _ _ _ _ hl h
  simpa [List.ofFn_get] using this

theorem novy_ropen_spec (π : PermFamily) (comm : List Bits) (privR pub : Bits) (b : Bool) (u : Bits)
    (h : novyRopen π [b] u comm privR pub = true) :
    ∃ x y, u = pack [x, y] ∧ x.length = pub.length ∧ π.applyStr x = y ∧
      y = (consistentList pub.length ((List.range (pub.length - 1)).map fun i => comm.getD (2 * i) [])
            (((List.range (pub.length - 1)).map fun i => comm.getD (2 * i + 1) []).map fun z => z.headD false)).getD
          (xor b ((comm.getD (2 * (pub.length - 1) + 1) []).headD false)).toNat [] := by
  unfold novyRopen at h
  split at h
  · rename_i x y hu
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_true, List.headD_cons] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, hu'⟩, hx⟩, _⟩, hβ⟩ := h
    refine ⟨x, y, hu', hx, ?_⟩
    rcases hβ with ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩
    · refine ⟨h2, ?_⟩
      rw [h1, of_decide_eq_true h3]; cases ((comm.getD (2 * (pub.length - 1) + 1) []).headD false) <;> rfl
    · refine ⟨h2, ?_⟩
      rw [h1, of_decide_eq_true h3]; cases ((comm.getD (2 * (pub.length - 1) + 1) []).headD false) <;> rfl
  · simp at h

/-! ## Novy-specific classical facts -/

example (π : PermFamily) (k : ℕ) : (novy π).setup (k + 2) = unary (k + 2) := rfl
example (π : PermFamily) (k : ℕ) : (novy π).rounds (k + 2) = k + 2 := rfl

theorem interleave_getD : ∀ (A B : List Bits), A.length = B.length → ∀ i, i < A.length →
    (interleave A B).getD (2 * i) [] = A.getD i [] ∧
      (interleave A B).getD (2 * i + 1) [] = B.getD i [] := by
  intro A
  induction A with
  | nil => intro B _ i hi; simp at hi
  | cons a A ih =>
    intro B hAB i hi
    rcases B with _ | ⟨b, B⟩
    · simp at hAB
    · simp only [interleave]
      rcases i with _ | i
      · simp
      · have e1 : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
        have e2 : 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 := by ring
        rw [e1]
        simp only [List.getD_cons_succ]
        exact ih B (by simpa using hAB) i (by simpa using hi)

theorem range_map_getD (p : List Bits) : (List.range p.length).map (fun i => p.getD i []) = p := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

theorem msbStr_inj (n v w : ℕ) (hv : v < 2 ^ n) (hw : w < 2 ^ n) (h : msbStr n v = msbStr n w) :
    v = w := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have hj : n - 1 - i < n := by omega
    have := congrArg (fun l : Bits => l[n - 1 - i]?) h
    simp only [msbStr, List.getElem?_map, List.getElem?_range hj, Option.map_some,
      Option.some.injEq] at this
    have e : n - 1 - (n - 1 - i) = i := by omega
    rwa [e] at this
  · have h2 : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hv h2),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hw h2)]

theorem consistentList_nodup (n : ℕ) (hs : List Bits) (zs : List Bool) :
    (consistentList n hs zs).Nodup := by
  unfold consistentList
  refine List.Nodup.filter _ ?_
  refine List.Nodup.map_on ?_ List.nodup_range
  intro v hv w hw h
  exact msbStr_inj n v w (List.mem_range.1 hv) (List.mem_range.1 hw) h

/-- The opening check, with `π_n(x) = y` kept. -/
theorem novy_openBoth_classical' (π : PermFamily) (comm : List Bits) (privR pub u0 u1 : Bits)
    (h : ∀ b : Bool, novyRopen π [b] u0 comm privR pub = true ∨ novyRopen π [b] u1 comm privR pub = true)
    (β : Bool) :
    ∃ u ∈ [u0, u1], ∃ x y, u = pack [x, y] ∧ x.length = pub.length ∧ π.applyStr x = y ∧
      y = (consistentList pub.length ((List.range (pub.length - 1)).map fun i => comm.getD (2 * i) [])
            (((List.range (pub.length - 1)).map fun i => comm.getD (2 * i + 1) []).map fun z => z.headD false)).getD
          β.toNat [] := by
  have hb : xor (xor β ((comm.getD (2 * (pub.length - 1) + 1) []).headD false))
      ((comm.getD (2 * (pub.length - 1) + 1) []).headD false) = β := by simp
  rcases h (xor β ((comm.getD (2 * (pub.length - 1) + 1) []).headD false)) with h | h
  · obtain ⟨x, y, hu, hx, hxy, hy⟩ := novy_ropen_spec π comm privR pub _ u0 h
    rw [hb] at hy
    exact ⟨u0, by simp, x, y, hu, hx, hxy, hy⟩
  · obtain ⟨x, y, hu, hx, hxy, hy⟩ := novy_ropen_spec π comm privR pub _ u1 h
    rw [hb] at hy
    exact ⟨u1, by simp, x, y, hu, hx, hxy, hy⟩

theorem pack_two_inj {x y x' y' : Bits} (h : pack [x, y] = pack [x', y']) : x = x' ∧ y = y' := by
  have := congrArg unpack h
  rw [unpack_pack, unpack_pack] at this
  simpa using this

/-- The selected positions of a successful opening of both bits give `π`-binding preimages. -/
theorem select_success (π : PermFamily) (n : ℕ) (hn : 1 ≤ n) (YS : List Bits) (hYS : YS.Nodup)
    (Sx : Bits)
    (hA : ∃ u ∈ [(unpack Sx).getD 0 [], (unpack Sx).getD 1 []], ∃ x y, u = pack [x, y] ∧
      x.length = n ∧ π.applyStr x = y ∧ y = YS.getD 0 [])
    (hB : ∃ u ∈ [(unpack Sx).getD 0 [], (unpack Sx).getD 1 []], ∃ x y, u = pack [x, y] ∧
      x.length = n ∧ π.applyStr x = y ∧ y = YS.getD 1 []) :
    16 * n + 10 ≤ Sx.length ∧ ∃ a : Bool,
      ((unpack ((selPos n a).map fun p => Sx.getD p false)).getD 0 []).length = n ∧
      ((unpack ((selPos n a).map fun p => Sx.getD p false)).getD 1 []).length = n ∧
      π.applyStr ((unpack ((selPos n a).map fun p => Sx.getD p false)).getD 0 []) = YS.getD 0 [] ∧
      π.applyStr ((unpack ((selPos n a).map fun p => Sx.getD p false)).getD 1 []) = YS.getD 1 [] := by
  obtain ⟨uA, huA, xA, yA, hA1, hA2, hA3, hA4⟩ := hA
  obtain ⟨uB, huB, xB, yB, hB1, hB2, hB3, hB4⟩ := hB
  have hyB : yB.length = n := by rw [← hB3, applyStr_length, hB2]
  have hyA : yA.length = n := by rw [← hA3, applyStr_length, hA2]
  -- the two targets differ
  have hne : YS.getD 0 [] ≠ YS.getD 1 [] := by
    have hlen : 2 ≤ YS.length := by
      by_contra hc
      have : YS.getD 1 [] = [] := List.getD_eq_default _ _ (by omega)
      rw [this] at hB4; rw [hB4] at hyB; simp at hyB; omega
    intro heq
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 0 < YS.length by omega),
      List.getElem?_eq_getElem (show 1 < YS.length by omega), Option.getD_some] at heq
    have := (List.Nodup.getElem_inj_iff hYS).1 heq
    omega
  have hAB : uA ≠ uB := by
    intro heq
    rw [hA1, hB1] at heq
    obtain ⟨hx, _⟩ := pack_two_inj heq
    apply hne
    rw [← hA4, ← hB4, ← hA3, ← hB3, hx]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at huA huB
  -- both items are well formed
  have key : ∀ (x0 y0 x1 y1 : Bits), (unpack Sx).getD 0 [] = pack [x0, y0] →
      (unpack Sx).getD 1 [] = pack [x1, y1] → x0.length = n → y0.length = n → x1.length = n →
      y1.length = n →
      16 * n + 10 ≤ Sx.length ∧ ∀ a, (selPos n a).map (fun p => Sx.getD p false) =
        if a then pack [x1, x0] else pack [x0, x1] := by
    intro x0 y0 x1 y1 h0 h1 hx0 hy0 hx1 hy1
    obtain ⟨t, ht⟩ := unpack_two_prefix Sx _ _ h0 h1 (pack_two_ne_nil _ _) (pack_two_ne_nil _ _)
    refine ⟨?_, fun a => ?_⟩
    · rw [ht]; simp only [List.length_append, packOne_length, pack_two_length, hx0, hy0, hx1, hy1]
      omega
    · rw [ht]; exact selPos_map n x0 y0 x1 y1 t hx0 hy0 hx1 a
  rcases huA with hA0 | hA0 <;> rcases huB with hB0 | hB0
  · exact absurd (hA0.trans hB0.symm) hAB
  · obtain ⟨hL, hsel⟩ := key xA yA xB yB (hA0 ▸ hA1) (hB0 ▸ hB1) hA2 hyA hB2 hyB
    refine ⟨hL, false, ?_⟩
    rw [hsel false]; simp only [Bool.false_eq_true, if_false, unpack_pack]
    simp [hA2, hB2, hA3, hB3, hA4, hB4]
  · obtain ⟨hL, hsel⟩ := key xB yB xA yA (hB0 ▸ hB1) (hA0 ▸ hA1) hB2 hyB hA2 hyA
    refine ⟨hL, true, ?_⟩
    rw [hsel true]; simp only [if_true, unpack_pack]
    simp [hA2, hB2, hA3, hB3, hA4, hB4]
  · exact absurd (hA0.trans hB0.symm) hAB

/-! ## The `π`-binding adversary built from an open-both adversary -/

abbrev mK (S : QStrategy) (k : ℕ) : ℕ := (S.stepAt (k + 1)).outW.length

theorem hK (S : QStrategy) (k : ℕ) :
    S.N + (S.stepAt (k + 1)).outW.length = S.inQ + (S.wkQ + mK S k) := Nat.add_assoc _ _ _

/-- The advice with the fresh ancillas in `|0⟩`. -/
def advLift (S : QStrategy) (m : ℕ) : Qubits (S.wkQ + m) → ℂ := fun w =>
  S.advice (fun i => w (Fin.castAdd m i)) *
    (if (fun j => w (Fin.natAdd S.wkQ j)) = (fun _ => false) then 1 else 0)

/-- The wires of the opening step selected to read `pack [x, x']`. -/
def selW0 (S : QStrategy) (k : ℕ) (a : Bool) : List (Fin S.N) :=
  (selPos (k + 2) a).filterMap (fun p => (S.stepAt (k + 2)).outW[p]?)

/-- Steps `k + 1` (announcing `d`) and `k + 2` (the opening) merged, `d` copied to ancillas. -/
def mergedStep (S : QStrategy) (k : ℕ) (a : Bool) : RoundStep (S.inQ + (S.wkQ + mK S k)) :=
  ⟨[], liftCirc (hK S k) (S.stepAt (k + 1)).circ ++
      (copyCirc (hK S k) ++ liftCirc (hK S k) (S.stepAt (k + 2)).circ),
    (selW0 S k a).map (eL (hK S k))⟩

/-- The `π`-binding adversary at `n = k + 2`. -/
def advPi (S : QStrategy) (k : ℕ) (a : Bool) : QStrategy where
  inQ := S.inQ
  wkQ := S.wkQ + mK S k
  advice := advLift S (mK S k)
  steps := (List.range (k + 1)).map (fun j => liftStep (hK S k) (S.stepAt j)) ++ [mergedStep S k a]

theorem advPi_stepAt_lt (S : QStrategy) (k : ℕ) (a : Bool) (j : ℕ) (hj : j < k + 1) :
    (advPi S k a).stepAt j = liftStep (hK S k) (S.stepAt j) := by
  simp only [QStrategy.stepAt, advPi, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simpa using hj)]
  simp [List.getElem?_range hj]

theorem advPi_stepAt_K (S : QStrategy) (k : ℕ) (a : Bool) :
    (advPi S k a).stepAt (k + 1) = mergedStep S k a := by
  simp only [QStrategy.stepAt, advPi, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp)]
  simp

theorem advPi_initDM (S : QStrategy) (k : ℕ) (a : Bool) :
    (advPi S k a).initDM (zeroDM (advPi S k a).inQ) =
      tens (N' := (advPi S k a).N) (hK S k) (S.initDM (zeroDM S.inQ)) (zeroDM (mK S k)) := by
  refine Matrix.ext (fun (y z : Qubits (S.inQ + (S.wkQ + mK S k))) => ?_)
  have hf : ∀ y : Qubits (S.inQ + (S.wkQ + mK S k)),
      fstPart (a := S.inQ) (b := S.wkQ) (y ∘ eL (hK S k)) = fstPart y := fun y => rfl
  have hs : ∀ y : Qubits (S.inQ + (S.wkQ + mK S k)),
      (fun i => sndPart (a := S.inQ) (b := S.wkQ + mK S k) y (Fin.castAdd (mK S k) i)) =
        sndPart (a := S.inQ) (b := S.wkQ) (y ∘ eL (hK S k)) := fun y => rfl
  have hz : ∀ y : Qubits (S.inQ + (S.wkQ + mK S k)),
      (fun j => sndPart (a := S.inQ) (b := S.wkQ + mK S k) y (Fin.natAdd S.wkQ j)) =
        y ∘ fL (hK S k) := by
    intro y; funext j
    simp only [sndPart, Function.comp_apply]
    congr 1; apply Fin.ext; simp [fL_val, QStrategy.N]; omega
  show (zeroDM S.inQ) (fstPart y) (fstPart z) * advLift S (mK S k) (sndPart y) *
      star (advLift S (mK S k) (sndPart z)) =
    (zeroDM S.inQ) (fstPart (y ∘ eL (hK S k))) (fstPart (z ∘ eL (hK S k))) *
      S.advice (sndPart (y ∘ eL (hK S k))) * star (S.advice (sndPart (z ∘ eL (hK S k)))) *
      zeroDM (mK S k) (y ∘ fL (hK S k)) (z ∘ fL (hK S k))
  simp only [advLift]
  rw [hs y, hs z, hz y, hz z, hf y, hf z]
  simp only [zeroDM, Matrix.of_apply]
  by_cases hy : y ∘ fL (hK S k) = (fun _ => false)
  · by_cases hzz : z ∘ fL (hK S k) = (fun _ => false)
    · simp only [hy, hzz, and_self, if_true, mul_one, star_one]
    · simp only [hzz, if_false, mul_zero, star_zero, and_false]
  · simp only [hy, if_false, zero_mul, mul_zero, false_and]

/-! ### The merged step on `ρ ⊗ |0⟩⟨0|` -/

theorem op_nil {N : ℕ} (s : RoundStep N) : s.op [] = s.circ.unitary := by
  simp [RoundStep.op, loadX_nil']

theorem trace_diag_sandwich' {n : ℕ} (a : Qubits n → ℂ) (Y : Matrix (Qubits n) (Qubits n) ℂ) :
    (Matrix.diagonal a * Y * Matrix.diagonal a).trace = ∑ z, a z * Y z z * a z := by
  simp [Matrix.trace, Matrix.diagonal_mul, Matrix.mul_diagonal]

/-- Measuring selected wires of `oW` is coarse-graining the measurement of `oW`. -/
theorem proj_split {N : ℕ} (oW : List (Fin N)) (P : List ℕ) (hP : ∀ p ∈ P, p < oW.length)
    (s' : Bits) (Y : Matrix (Qubits N) (Qubits N) ℂ) :
    (outcomeProj (P.filterMap (fun p => oW[p]?)) s' * Y * outcomeProj (P.filterMap (fun p => oW[p]?)) s').trace =
      ∑ s : Qubits oW.length, if P.map (fun p => (List.ofFn s).getD p false) = s' then
        (outcomeProj oW (List.ofFn s) * Y * outcomeProj oW (List.ofFn s)).trace else 0 := by
  simp only [outcomeProj, diagProj]
  rw [trace_diag_sandwich']
  simp_rw [trace_diag_sandwich']
  have hread : ∀ z : Qubits N, readWires (P.filterMap (fun p => oW[p]?)) z =
      P.map (fun p => (readWires oW z).getD p false) := fun z => filterMap_wires_read oW z P hP
  simp_rw [hread]
  have hite : ∀ (c : Prop) [Decidable c] (f : Qubits N → ℂ),
      (if c then ∑ z, f z else 0) = ∑ z, if c then f z else 0 := by
    intro c _ f; split_ifs <;> simp
  simp only [hite]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.sum_eq_single (fun j => z (oW.get j))]
  · have e : readWires oW z = List.ofFn (fun j => z (oW.get j)) :=
      (readWires_eq_ofFn_iff oW z _).2 rfl
    rw [if_pos e]
    by_cases hc : P.map (fun p => (readWires oW z).getD p false) = s'
    · rw [if_pos hc, if_pos (by rw [← e]; exact hc)]
    · rw [if_neg hc, if_neg (by rw [← e]; exact hc)]; simp
  · intro s _ hs
    have : ¬ readWires oW z = List.ofFn s := fun h => hs (((readWires_eq_ofFn_iff oW z s).1 h).symm)
    split_ifs <;> simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The trace of the merged step: a sum over the outcomes `d` of step `k + 1` and the outcomes of
step `k + 2` whose selection is `s'`. -/
theorem merged_trace (S : QStrategy) (k : ℕ) (a : Bool) (R : Matrix (Qubits S.N) (Qubits S.N) ℂ)
    (hL : 16 * (k + 2) + 10 ≤ (S.stepAt (k + 2)).outW.length) (s' : Bits) :
    (stepDM (mergedStep S k a) [] s' (tens (hK S k) R (zeroDM (mK S k)))).trace =
      ∑ d : Qubits (mK S k), ∑ s : Qubits (S.stepAt (k + 2)).outW.length,
        if (selPos (k + 2) a).map (fun p => (List.ofFn s).getD p false) = s' then
          (stepDM (S.stepAt (k + 2)) [] (List.ofFn s)
            (stepDM (S.stepAt (k + 1)) [] (List.ofFn d) R)).trace else 0 := by
  set h := hK S k
  set U0 := (S.stepAt (k + 1)).circ.unitary
  set U1 := (S.stepAt (k + 2)).circ.unitary
  set C := (copyCirc h).unitary
  set Q := outcomeProj (selW0 S k a) s'
  have hU : (mergedStep S k a).op [] = embedOp U1 (eL h) * C * embedOp U0 (eL h) := by
    rw [op_nil]
    simp only [mergedStep, circuit_unitary_append, liftCirc_unitary]
    rfl
  have hQ : outcomeProj (mergedStep S k a).outW s' = embedOp Q (eL h) := outcomeProj_map h _ _
  have hT : embedOp U0 (eL h) * tens h R (zeroDM (mK S k)) * embedOp U0ᴴ (eL h) =
      tens h (U0 * R * U0ᴴ) (zeroDM (mK S k)) := by
    rw [embedOp_mul_tens, tens_mul_embedOp]
  have hstep : stepDM (mergedStep S k a) [] s' (tens h R (zeroDM (mK S k))) =
      embedOp (Q * U1) (eL h) * (C * tens h (U0 * R * U0ᴴ) (zeroDM (mK S k)) * Cᴴ) *
        embedOp (U1ᴴ * Q) (eL h) := by
    simp only [stepDM]
    rw [hU, hQ, ← hT]
    simp only [Matrix.conjTranspose_mul, embedOp_conjTranspose, embedOp_mul, Matrix.mul_assoc]
  rw [hstep, deferred_trace]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  have hsel : ∀ p ∈ selPos (k + 2) a, p < (S.stepAt (k + 2)).outW.length :=
    fun p hp => lt_of_lt_of_le (selPos_bound _ a p hp) hL
  have e1 : Q * U1 * outcomeProj (S.stepAt (k + 1)).outW (List.ofFn d) * (U0 * R * U0ᴴ) *
      outcomeProj (S.stepAt (k + 1)).outW (List.ofFn d) * (U1ᴴ * Q) =
      Q * (U1 * stepDM (S.stepAt (k + 1)) [] (List.ofFn d) R * U1ᴴ) * Q := by
    simp only [stepDM, op_nil, Matrix.mul_assoc]; rfl
  rw [e1]
  show (outcomeProj (selW0 S k a) s' * _ * outcomeProj (selW0 S k a) s').trace = _
  rw [selW0, proj_split _ _ hsel]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  split_ifs
  · simp only [stepDM, op_nil, Matrix.mul_assoc]; rfl
  · rfl

/-! ### The probabilities -/

/-- The summand of `openBothProb`. -/
noncomputable def obG (Cm : CommitmentScheme) (S : QStrategy) (n : ℕ)
    (c : CoinSpace (Cm.receiver.coins (Cm.setup n))) (os : List Bits) : ℝ :=
  let comm := commTranscript Cm n c (os.take (Cm.rounds n))
  let s := os.getD (Cm.rounds n) []
  let u0 := (unpack s).getD 0 []
  let u1 := (unpack s).getD 1 []
  let ok : Bool → Bool := fun b =>
    Cm.ropen [b] u0 comm (encCoins c) (Cm.setup n) || Cm.ropen [b] u1 comm (encCoins c) (Cm.setup n)
  if (ok false && ok true) = true then
    (S.run (expMsg Cm n c (fun _ => [])) (zeroDM S.inQ) os).trace.re
  else 0

theorem openBothProb_eq (Cm : CommitmentScheme) (S : QStrategy) (n : ℕ) :
    openBothProb Cm S n = avgOver (CoinSpace (Cm.receiver.coins (Cm.setup n))) fun c =>
      ∑ o : S.Outs (Cm.rounds n + 1), obG Cm S n c (QStrategy.outList o) := rfl

/-- The summand of `piBindProb`. -/
noncomputable def pbG (π : PermFamily) (S : QStrategy) (n : ℕ)
    (c : CoinSpace (novyReceiver.coins (unary n))) (os : List Bits) : ℝ :=
  let pub := unary n
  let K := n - 1
  let hs := (List.range K).map fun j => novyReceiver.msg pub c (os.take j)
  let ys := consistentList n hs ((os.take K).map fun z => z.headD false)
  let s := os.getD K []
  let x0 := (unpack s).getD 0 []
  let x1 := (unpack s).getD 1 []
  let msg : List Bits → Bits := fun done =>
    if done.length < K then msgFor pub (novyReceiver.msg pub c) done else []
  if x0.length = n ∧ x1.length = n ∧ π.applyStr x0 = ys.getD 0 [] ∧ π.applyStr x1 = ys.getD 1 []
  then (S.run msg (zeroDM S.inQ) os).trace.re
  else 0

theorem piBindProb_eq (π : PermFamily) (S : QStrategy) (n : ℕ) :
    piBindProb π S n = avgOver (CoinSpace (novyReceiver.coins (unary n))) fun c =>
      ∑ o : S.Outs (n - 1 + 1), pbG π S n c (QStrategy.outList o) := rfl

theorem novyReceiver_msg_last (k : ℕ) (c : CoinSpace (novyReceiver.coins (unary (k + 2))))
    (p : List Bits) (hp : p.length = k + 1) : novyReceiver.msg (unary (k + 2)) c p = [] := by
  simp only [Party.msg, Party.view, novyReceiver, unpack_pack]
  simp [unary, hp]

theorem pbG_nonneg (π : PermFamily) (S : QStrategy) (n : ℕ) (c) (os : List Bits) :
    0 ≤ pbG π S n c os := by
  unfold pbG
  dsimp only
  split_ifs
  · exact run_trace_nonneg _ _ _
  · exact le_refl _

theorem stepDM2_nonneg (S : QStrategy) (msg : List Bits → Bits) (p : List Bits) (s0 s1 : RoundStep S.N)
    (x0 x1 o0 o1 : Bits) :
    0 ≤ (stepDM s1 x1 o1 (stepDM s0 x0 o0 (S.runFrom msg [] p (S.initDM (zeroDM S.inQ))))).trace.re := by
  open scoped ComplexOrder in
  have := (stepDM_psd s1 x1 o1 (stepDM_psd s0 x0 o0 (runFrom_psd S msg p [] (initDM_zero_psd S)))).trace_nonneg
  exact (Complex.nonneg_iff.1 this).1

theorem sum_ofFn_eq (len : ℕ) (t : Bits) (ht : t.length = len) (F : Bits → ℝ) :
    (∑ s' : Qubits len, if t = List.ofFn s' then F (List.ofFn s') else 0) = F t := by
  subst ht
  rw [Finset.sum_eq_single (fun i => t.get i)]
  · rw [if_pos (List.ofFn_get t).symm, List.ofFn_get]
  · intro b _ hb
    rw [if_neg]
    intro h
    apply hb
    have : List.ofFn b = List.ofFn (fun i => t.get i) := by rw [← h, List.ofFn_get]
    exact List.ofFn_injective this
  · simp

/-! ### One coin, one prefix -/

def msgO (π : PermFamily) (k : ℕ) (c : CoinSpace (novyReceiver.coins (unary (k + 2)))) :
    List Bits → Bits :=
  expMsg (novy π) (k + 2) c (fun _ => [])

noncomputable def Rst (π : PermFamily) (S : QStrategy) (k : ℕ)
    (c : CoinSpace (novyReceiver.coins (unary (k + 2)))) (p : List Bits) :
    Matrix (Qubits S.N) (Qubits S.N) ℂ :=
  S.runFrom (msgO π k c) [] p (S.initDM (zeroDM S.inQ))

noncomputable def tt (π : PermFamily) (S : QStrategy) (k : ℕ)
    (c : CoinSpace (novyReceiver.coins (unary (k + 2)))) (p : List Bits)
    (d : Qubits (mK S k)) (s : Qubits (S.stepAt (k + 2)).outW.length) : ℝ :=
  (stepDM (S.stepAt (k + 2)) [] (List.ofFn s)
    (stepDM (S.stepAt (k + 1)) [] (List.ofFn d) (Rst π S k c p))).trace.re

abbrev OBc (π : PermFamily) (k : ℕ) (c : CoinSpace (novyReceiver.coins (unary (k + 2))))
    (p : List Bits) (D Sx : Bits) : Prop :=
  let comm := commTranscript (novy π) (k + 2) c (p ++ [D])
  let u0 := (unpack Sx).getD 0 []
  let u1 := (unpack Sx).getD 1 []
  let ok : Bool → Bool := fun b =>
    (novy π).ropen [b] u0 comm (encCoins c) ((novy π).setup (k + 2)) ||
      (novy π).ropen [b] u1 comm (encCoins c) ((novy π).setup (k + 2))
  (ok false && ok true) = true

def YSp (k : ℕ) (c : CoinSpace (novyReceiver.coins (unary (k + 2)))) (p : List Bits) : List Bits :=
  consistentList (k + 2) ((List.range (k + 1)).map fun j => novyReceiver.msg (unary (k + 2)) c (p.take j))
    (p.map fun z => z.headD false)

abbrev PBc (π : PermFamily) (k : ℕ) (c : CoinSpace (novyReceiver.coins (unary (k + 2))))
    (p : List Bits) (s'' : Bits) : Prop :=
  ((unpack s'').getD 0 []).length = k + 2 ∧ ((unpack s'').getD 1 []).length = k + 2 ∧
    π.applyStr ((unpack s'').getD 0 []) = (YSp k c p).getD 0 [] ∧
    π.applyStr ((unpack s'').getD 1 []) = (YSp k c p).getD 1 []

def pick (n : ℕ) (a : Bool) (Sx : Bits) : Bits := (selPos n a).map fun q => Sx.getD q false

theorem msgO_last (π : PermFamily) (k : ℕ) (c : CoinSpace (novyReceiver.coins (unary (k + 2))))
    (p : List Bits) (hp : p.length = k + 1) : msgO π k c p = [] := by
  unfold msgO expMsg msgFor
  rw [if_pos (show p.length < (novy π).rounds (k + 2) from by show p.length < k + 2; omega)]
  rw [if_neg (by intro h; rw [h] at hp; simp at hp)]
  exact novyReceiver_msg_last k c p hp

theorem msgO_after (π : PermFamily) (k : ℕ) (c : CoinSpace (novyReceiver.coins (unary (k + 2))))
    (p : List Bits) (hp : p.length = k + 1) (D : Bits) : msgO π k c (p ++ [D]) = [] := by
  unfold msgO expMsg
  rw [if_neg (show ¬ (p ++ [D]).length < (novy π).rounds (k + 2) from by
    show ¬ (p ++ [D]).length < k + 2; simp [hp])]

theorem obG_eq (π : PermFamily) (S : QStrategy) (k : ℕ)
    (c : CoinSpace (novyReceiver.coins (unary (k + 2)))) (p : List Bits) (hp : p.length = k + 1)
    (d : Qubits (mK S k)) (s : Qubits (S.stepAt (k + 2)).outW.length) :
    obG (novy π) S (k + 2) c (p ++ [List.ofFn d, List.ofFn s]) =
      if OBc π k c p (List.ofFn d) (List.ofFn s) then tt π S k c p d s else 0 := by
  have hr : (novy π).rounds (k + 2) = k + 2 := rfl
  have e1 : (p ++ [List.ofFn d, List.ofFn s]).take (k + 2) = p ++ [List.ofFn d] := by
    rw [show p ++ [List.ofFn d, List.ofFn s] = (p ++ [List.ofFn d]) ++ [List.ofFn s] by simp]
    exact List.take_left' (by simp [hp])
  have e2 : (p ++ [List.ofFn d, List.ofFn s]).getD (k + 2) [] = List.ofFn s := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hp]
    simp
  have e3 : S.run (expMsg (novy π) (k + 2) c (fun _ => [])) (zeroDM S.inQ)
      (p ++ [List.ofFn d, List.ofFn s]) =
      stepDM (S.stepAt (k + 2)) [] (List.ofFn s)
        (stepDM (S.stepAt (k + 1)) [] (List.ofFn d) (Rst π S k c p)) := by
    have h1 := msgO_last π k c p hp
    have h2 := msgO_after π k c p hp (List.ofFn d)
    unfold msgO at h1 h2
    unfold QStrategy.run Rst msgO
    rw [runFrom_append]
    simp only [QStrategy.runFrom, List.nil_append, List.length_append, List.length_singleton, hp, h1, h2]
  unfold obG
  dsimp only
  rw [hr, e1, e2, e3]
  rfl

theorem pbG_eq (π : PermFamily) (S : QStrategy) (k : ℕ) (a : Bool)
    (c : CoinSpace (novyReceiver.coins (unary (k + 2)))) (p : List Bits) (hp : p.length = k + 1)
    (s' : Bits) :
    pbG π (advPi S k a) (k + 2) c (p ++ [s']) =
      if PBc π k c p s' then
        (stepDM (mergedStep S k a) [] s' (tens (hK S k) (Rst π S k c p) (zeroDM (mK S k)))).trace.re
      else 0 := by
  have hk : k + 2 - 1 = k + 1 := rfl
  have e0 : ∀ j, j < k + 1 → (p ++ [s']).take j = p.take j := by
    intro j hj; rw [List.take_append_of_le_length (by omega)]
  have e1 : (p ++ [s']).take (k + 1) = p := by
    rw [← hp]; simp
  have e2 : (p ++ [s']).getD (k + 1) [] = s' := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hp]; simp
  have hrange : ((List.range (k + 1)).map fun j => novyReceiver.msg (unary (k + 2)) c ((p ++ [s']).take j)) =
      (List.range (k + 1)).map fun j => novyReceiver.msg (unary (k + 2)) c (p.take j) :=
    List.map_congr_left (fun j hj => by rw [e0 j (List.mem_range.1 hj)])
  have hmsg : ∀ d : List Bits, d.length < k + 1 →
      (fun done : List Bits => if done.length < k + 1 then
        msgFor (unary (k + 2)) (novyReceiver.msg (unary (k + 2)) c) done else []) d = msgO π k c d := by
    intro d hd
    simp only [msgO, expMsg]
    rw [if_pos hd, if_pos (show d.length < (novy π).rounds (k + 2) from by show d.length < k + 2; omega)]
    rfl
  have e3 : (advPi S k a).run (fun done : List Bits => if done.length < k + 1 then
        msgFor (unary (k + 2)) (novyReceiver.msg (unary (k + 2)) c) done else [])
        (zeroDM (advPi S k a).inQ) (p ++ [s']) =
      stepDM (mergedStep S k a) [] s' (tens (hK S k) (Rst π S k c p) (zeroDM (mK S k))) := by
    unfold QStrategy.run
    rw [runFrom_append, advPi_initDM,
      runFrom_lift S (advPi S k a) (hK S k) (k + 1) (advPi_stepAt_lt S k a) _ _ hmsg _ p [] _
        (by simp [hp])]
    simp only [QStrategy.runFrom, List.nil_append, hp]
    rw [advPi_stepAt_K, if_neg (lt_irrefl _)]
    rfl
  unfold pbG
  dsimp only
  simp only [hk, e1, e2, hrange, e3]
  rfl

theorem ob_select (π : PermFamily) (k : ℕ) (c : CoinSpace (novyReceiver.coins (unary (k + 2))))
    (p : List Bits) (hp : p.length = k + 1) (D Sx : Bits) (h : OBc π k c p D Sx) :
    16 * (k + 2) + 10 ≤ Sx.length ∧ ∃ a : Bool, PBc π k c p (pick (k + 2) a Sx) := by
  have hok : ∀ b : Bool, novyRopen π [b] ((unpack Sx).getD 0 []) (commTranscript (novy π) (k + 2) c (p ++ [D]))
      (encCoins c) (unary (k + 2)) = true ∨ novyRopen π [b] ((unpack Sx).getD 1 [])
      (commTranscript (novy π) (k + 2) c (p ++ [D])) (encCoins c) (unary (k + 2)) = true := by
    simp only [OBc, Bool.and_eq_true, Bool.or_eq_true] at h
    intro b; cases b
    · exact h.1
    · exact h.2
  have hpub : (unary (k + 2)).length = k + 2 := by simp [unary]
  -- the hashing transcript inside `comm`
  set comm := commTranscript (novy π) (k + 2) c (p ++ [D]) with hcomm
  have hA : ((List.range ((novy π).rounds (k + 2))).map fun j =>
      (novy π).receiver.msg ((novy π).setup (k + 2)) c ((p ++ [D]).take j)).length = (p ++ [D]).length := by
    simp [hp]; rfl
  have hI : ∀ i, i < k + 1 → comm.getD (2 * i) [] = novyReceiver.msg (unary (k + 2)) c (p.take i) ∧
      comm.getD (2 * i + 1) [] = p.getD i [] := by
    intro i hi
    have := interleave_getD _ _ hA i
      (by simp only [List.length_map, List.length_range]; show i < k + 2; omega)
    refine ⟨?_, ?_⟩
    · rw [hcomm]; unfold commTranscript; rw [this.1]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (show i < (novy π).rounds (k + 2) from by show i < k + 2; omega),
        Option.map_some, Option.getD_some]
      rw [List.take_append_of_le_length (by omega)]
      rfl
    · rw [hcomm]; unfold commTranscript; rw [this.2]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
  have hhs : ((List.range ((unary (k + 2)).length - 1)).map fun i => comm.getD (2 * i) []) =
      (List.range (k + 1)).map fun j => novyReceiver.msg (unary (k + 2)) c (p.take j) := by
    rw [hpub]
    exact List.map_congr_left (fun i hi => (hI i (List.mem_range.1 hi)).1)
  have hzs : (((List.range ((unary (k + 2)).length - 1)).map fun i => comm.getD (2 * i + 1) []).map
      fun z => z.headD false) = p.map fun z => z.headD false := by
    rw [hpub]
    have : ((List.range (k + 1)).map fun i => comm.getD (2 * i + 1) []) = p := by
      rw [← range_map_getD p, hp]
      exact List.map_congr_left (fun i hi => (hI i (List.mem_range.1 hi)).2)
    rw [show k + 2 - 1 = k + 1 from rfl, this]
  have hβ := fun β => novy_openBoth_classical' π comm (encCoins c) (unary (k + 2)) _ _ hok β
  rw [hhs, hzs, hpub] at hβ
  obtain ⟨hL, a, ha⟩ := select_success π (k + 2) (by omega) (YSp k c p) (consistentList_nodup _ _ _) Sx
    (hβ false) (hβ true)
  exact ⟨hL, a, ha⟩

/-- One coin `c` and one prefix `p` of the first `k + 1` outcomes. -/
theorem per_prefix (π : PermFamily) (S : QStrategy) (k : ℕ)
    (c : CoinSpace (novyReceiver.coins (unary (k + 2)))) (p : List Bits) (hp : p.length = k + 1) :
    (∑ d : Qubits (mK S k), ∑ s : Qubits (S.stepAt (k + 2)).outW.length,
        obG (novy π) S (k + 2) c (p ++ [List.ofFn d, List.ofFn s])) ≤
      (∑ s' : Qubits ((advPi S k false).stepAt (k + 1)).outW.length,
          pbG π (advPi S k false) (k + 2) c (p ++ [List.ofFn s'])) +
      (∑ s' : Qubits ((advPi S k true).stepAt (k + 1)).outW.length,
          pbG π (advPi S k true) (k + 2) c (p ++ [List.ofFn s'])) := by
  have ht : ∀ d s, 0 ≤ tt π S k c p d s := fun d s => stepDM2_nonneg S (msgO π k c) p _ _ _ _ _ _
  simp_rw [obG_eq π S k c p hp]
  by_cases hL : 16 * (k + 2) + 10 ≤ (S.stepAt (k + 2)).outW.length
  · have hsel : ∀ a, ∀ q ∈ selPos (k + 2) a, q < (S.stepAt (k + 2)).outW.length :=
      fun a q hq => lt_of_lt_of_le (selPos_bound _ a q hq) hL
    have hlen : ∀ a, ((advPi S k a).stepAt (k + 1)).outW.length = (selPos (k + 2) a).length := by
      intro a
      rw [advPi_stepAt_K]
      simp only [mergedStep, List.length_map, selW0]
      have hh := congrArg List.length (filterMap_wires_read (S.stepAt (k + 2)).outW (fun _ => false)
        (selPos (k + 2) a) (hsel a))
      simp only [List.length_map] at hh
      show ((selW0 S k a).map (eL (hK S k))).length = _
      rw [List.length_map]
      exact hh
    have hRHS : ∀ a : Bool,
        (∑ s' : Qubits ((advPi S k a).stepAt (k + 1)).outW.length,
          pbG π (advPi S k a) (k + 2) c (p ++ [List.ofFn s'])) =
        ∑ d : Qubits (mK S k), ∑ s : Qubits (S.stepAt (k + 2)).outW.length,
          if PBc π k c p (pick (k + 2) a (List.ofFn s)) then tt π S k c p d s else 0 := by
      intro a
      calc _ = ∑ s' : Qubits ((advPi S k a).stepAt (k + 1)).outW.length,
            ∑ d : Qubits (mK S k), ∑ s : Qubits (S.stepAt (k + 2)).outW.length,
              if pick (k + 2) a (List.ofFn s) = List.ofFn s' then
                (if PBc π k c p (List.ofFn s') then tt π S k c p d s else 0) else 0 := by
            refine Finset.sum_congr rfl (fun s' _ => ?_)
            rw [pbG_eq π S k a c p hp, merged_trace S k a _ hL]
            by_cases hc : PBc π k c p (List.ofFn s')
            · rw [if_pos hc, Complex.re_sum]
              refine Finset.sum_congr rfl (fun d _ => ?_)
              rw [Complex.re_sum]
              refine Finset.sum_congr rfl (fun s _ => ?_)
              rw [if_pos hc]
              simp only [pick]
              split_ifs <;> simp_all [tt]
            · rw [if_neg hc]
              symm
              refine Finset.sum_eq_zero (fun d _ => Finset.sum_eq_zero (fun s _ => ?_))
              rw [if_neg hc]; split_ifs <;> simp
        _ = ∑ d : Qubits (mK S k), ∑ s : Qubits (S.stepAt (k + 2)).outW.length,
            ∑ s' : Qubits ((advPi S k a).stepAt (k + 1)).outW.length,
              if pick (k + 2) a (List.ofFn s) = List.ofFn s' then
                (if PBc π k c p (List.ofFn s') then tt π S k c p d s else 0) else 0 := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun d _ => ?_)
            rw [Finset.sum_comm]
        _ = _ := by
            refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun s _ => ?_))
            exact sum_ofFn_eq _ (pick (k + 2) a (List.ofFn s))
              (by rw [hlen a]; simp [pick]) (fun x => if PBc π k c p x then tt π S k c p d s else 0)
    rw [hRHS false, hRHS true, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun d _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun s _ => ?_)
    by_cases hob : OBc π k c p (List.ofFn d) (List.ofFn s)
    · rw [if_pos hob]
      obtain ⟨_, a, ha⟩ := ob_select π k c p hp _ _ hob
      cases a
      · rw [if_pos ha]
        have : 0 ≤ (if PBc π k c p (pick (k + 2) true (List.ofFn s)) then tt π S k c p d s else 0) := by
          split_ifs
          · exact ht d s
          · exact le_refl _
        linarith
      · rw [if_pos ha]
        have : 0 ≤ (if PBc π k c p (pick (k + 2) false (List.ofFn s)) then tt π S k c p d s else 0) := by
          split_ifs
          · exact ht d s
          · exact le_refl _
        linarith
    · rw [if_neg hob]
      apply add_nonneg <;> (split_ifs; exacts [ht d s, le_refl _])
  · have : (∑ d : Qubits (mK S k), ∑ s : Qubits (S.stepAt (k + 2)).outW.length,
        if OBc π k c p (List.ofFn d) (List.ofFn s) then tt π S k c p d s else 0) = 0 := by
      refine Finset.sum_eq_zero (fun d _ => Finset.sum_eq_zero (fun s _ => ?_))
      rw [if_neg]
      intro hob
      have := (ob_select π k c p hp _ _ hob).1
      simp at this
      exact hL this
    rw [this]
    exact add_nonneg (Finset.sum_nonneg (fun _ _ => pbG_nonneg _ _ _ _ _))
      (Finset.sum_nonneg (fun _ _ => pbG_nonneg _ _ _ _ _))

/-! ### The whole probabilities -/

theorem openBoth_le (π : PermFamily) (S : QStrategy) (k : ℕ) :
    openBothProb (novy π) S (k + 2) ≤
      piBindProb π (advPi S k false) (k + 2) + piBindProb π (advPi S k true) (k + 2) := by
  rw [openBothProb_eq, piBindProb_eq, piBindProb_eq]
  unfold avgOver
  rw [← smul_add, ← Finset.sum_add_distrib]
  refine smul_le_smul_of_nonneg_left (Finset.sum_le_sum (fun c _ => ?_)) (by positivity)
  rw [sum_outs_eq', sum_outs_eq', sum_outs_eq']
  have hr1 : (novy π).rounds (k + 2) + 1 = k + 1 + 1 + 1 := rfl
  have hr2 : k + 2 - 1 + 1 = k + 1 + 1 := rfl
  rw [hr1, hr2]
  have L1 : ((List.range (k + 1 + 1 + 1)).map fun j => (S.stepAt j).outW.length) =
      ((List.range (k + 1)).map fun j => (S.stepAt j).outW.length) ++
        [(S.stepAt (k + 1)).outW.length, (S.stepAt (k + 2)).outW.length] := by
    simp [List.range_succ]
  have L2 : ∀ a, ((List.range (k + 1 + 1)).map fun j => ((advPi S k a).stepAt j).outW.length) =
      ((List.range (k + 1)).map fun j => ((advPi S k a).stepAt j).outW.length) ++
        [((advPi S k a).stepAt (k + 1)).outW.length] := by
    intro a; simp [List.range_succ]
  rw [L1, L2 false, L2 true]
  have hpre : ∀ a, ((List.range (k + 1)).map fun j => ((advPi S k a).stepAt j).outW.length) =
      (List.range (k + 1)).map fun j => (S.stepAt j).outW.length := by
    intro a
    refine List.map_congr_left (fun j hj => ?_)
    rw [advPi_stepAt_lt S k a j (List.mem_range.1 hj)]
    exact List.length_map _
  rw [hpre false, hpre true, lensSum_append, lensSum_append, lensSum_append, ← lensSum_add]
  refine lensSum_mono _ _ _ (fun p hp => ?_)
  simp only [List.length_map, List.length_range] at hp
  simp only [lensSum]
  exact per_prefix π S k c p hp

/-! ### The new adversary is QPT -/

theorem stepAt_nodup (S : QStrategy) (hS : S.Valid) (j : ℕ) :
    (S.stepAt j).inW.Nodup ∧ (S.stepAt j).outW.Nodup := by
  unfold QStrategy.stepAt
  rw [List.getD_eq_getElem?_getD]
  rcases h : S.steps[j]? with _ | s
  · simp; exact ⟨List.nodup_nil, List.nodup_nil⟩
  · simp only [Option.getD_some]
    obtain ⟨hj, hs⟩ := List.getElem?_eq_some_iff.1 h
    exact hS.2 s (hs ▸ List.getElem_mem hj)

theorem advPi_valid (S : QStrategy) (hS : S.Valid) (k : ℕ) (a : Bool) : (advPi S k a).Valid := by
  refine ⟨?_, ?_⟩
  · show ∑ w : Qubits (S.wkQ + mK S k), ‖advLift S (mK S k) w‖ ^ 2 = 1
    rw [sum_split (N := S.wkQ) (m := mK S k) rfl]
    rw [← hS.1]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.sum_eq_single (fun _ => false)]
    · have e1 := split_symm_e (rfl : S.wkQ + mK S k = S.wkQ + mK S k) q (fun _ => false)
      have e2 := split_symm_f (rfl : S.wkQ + mK S k = S.wkQ + mK S k) q (fun _ => false)
      simp only [advLift]
      rw [show (fun i => (splitQ rfl).symm (q, fun _ => false) (Fin.castAdd (mK S k) i)) = q from e1,
        show (fun j => (splitQ rfl).symm (q, fun _ => false) (Fin.natAdd S.wkQ j)) = (fun _ => false)
          from e2]
      simp
    · intro r _ hr
      have e1 := split_symm_e (rfl : S.wkQ + mK S k = S.wkQ + mK S k) q r
      have e2 := split_symm_f (rfl : S.wkQ + mK S k = S.wkQ + mK S k) q r
      simp only [advLift]
      rw [show (fun i => (splitQ rfl).symm (q, r) (Fin.castAdd (mK S k) i)) = q from e1,
        show (fun j => (splitQ rfl).symm (q, r) (Fin.natAdd S.wkQ j)) = r from e2]
      simp [hr]
    · simp
  · intro s hs
    have hs' : s ∈ (List.range (k + 1)).map (fun j => liftStep (hK S k) (S.stepAt j)) ++
        [mergedStep S k a] := hs
    rcases List.mem_append.1 hs' with hs'' | hs''
    · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hs''
      obtain ⟨h1, h2⟩ := stepAt_nodup S hS j
      exact ⟨h1.map (eL (hK S k)).injective, h2.map (eL (hK S k)).injective⟩
    · rw [List.mem_singleton.1 hs'']
      refine ⟨List.nodup_nil, ?_⟩
      refine List.Nodup.map (eL (hK S k)).injective ?_
      exact filterMap_wires_nodup _ (stepAt_nodup S hS (k + 2)).2 _ (selPos_nodup _ _)

theorem stepAt_size_le (S : QStrategy) (j : ℕ) :
    (S.stepAt j).size ≤ (S.steps.map RoundStep.size).sum := by
  unfold QStrategy.stepAt
  rw [List.getD_eq_getElem?_getD]
  rcases h : S.steps[j]? with _ | s
  · simp [RoundStep.size, default, Circuit.size]
  · simp only [Option.getD_some]
    obtain ⟨hj, hs⟩ := List.getElem?_eq_some_iff.1 h
    exact List.le_sum_of_mem (List.mem_map.2 ⟨s, hs ▸ List.getElem_mem hj, rfl⟩)

theorem sum_range_getD_le {N : ℕ} (l : List (RoundStep N)) : ∀ r,
    ((List.range r).map fun j => (l.getD j default).size).sum ≤ (l.map RoundStep.size).sum := by
  have h0 : (default : RoundStep N).size = 0 := rfl
  induction l with
  | nil =>
    intro r
    simp [h0]
  | cons x l ih =>
    intro r
    rcases r with _ | r
    · simp
    · calc ((List.range (r + 1)).map fun j => ((x :: l).getD j default).size).sum
          = x.size + ((List.range r).map fun j => (l.getD j default).size).sum := by
            rw [List.range_succ_eq_map]; simp [Function.comp_def]
        _ ≤ x.size + (l.map RoundStep.size).sum := by have := ih r; omega
        _ = _ := by simp

theorem liftStep_size {N m N' : ℕ} (h : N + m = N') (s : RoundStep N) :
    (liftStep h s).size = s.size := by
  simp [RoundStep.size, liftStep, liftCirc, Circuit.size]

theorem advPi_size (S : QStrategy) (k : ℕ) (a : Bool) :
    (advPi S k a).size ≤ 6 * S.size + 5 * (k + 2) + 2 := by
  have hT : (S.steps.map RoundStep.size).sum ≤ S.size := by unfold QStrategy.size; omega
  have hsum := sum_range_getD_le S.steps (k + 1)
  have hm : mK S k ≤ (S.steps.map RoundStep.size).sum :=
    le_trans (by simp only [RoundStep.size, mK]; omega) (stepAt_size_le S (k + 1))
  have hc1 : (S.stepAt (k + 1)).circ.length ≤ (S.steps.map RoundStep.size).sum :=
    le_trans (by simp only [RoundStep.size, Circuit.size]; omega) (stepAt_size_le S (k + 1))
  have hc2 : (S.stepAt (k + 2)).circ.length ≤ (S.steps.map RoundStep.size).sum :=
    le_trans (by simp only [RoundStep.size, Circuit.size]; omega) (stepAt_size_le S (k + 2))
  have hsel : (selW0 S k a).length ≤ 4 * (k + 2) + 2 := by
    rw [← selPos_length (k + 2) a]; exact List.length_filterMap_le _ _
  have hmerged : (mergedStep S k a).size ≤ (S.stepAt (k + 1)).circ.length + mK S k +
      (S.stepAt (k + 2)).circ.length + (4 * (k + 2) + 2) := by
    simp only [RoundStep.size, mergedStep, Circuit.size, List.length_append, List.length_nil,
      List.length_map, liftCirc, copyCirc, List.length_finRange, mK]
    omega
  have hlift : ((List.range (k + 1)).map fun j => (liftStep (hK S k) (S.stepAt j)).size).sum =
      ((List.range (k + 1)).map fun j => (S.steps.getD j default).size).sum := by
    congr 1
    exact List.map_congr_left (fun j _ => by rw [liftStep_size]; rfl)
  have hsz : (advPi S k a).size = S.inQ + (S.wkQ + mK S k) + (k + 2) +
      (((List.range (k + 1)).map fun j => (liftStep (hK S k) (S.stepAt j)).size).sum +
        (mergedStep S k a).size) := by
    simp only [QStrategy.size, advPi, List.length_append, List.length_map, List.length_range,
      List.length_singleton, List.map_append, List.sum_append, List.map_map, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rfl
  have hS : S.inQ + S.wkQ ≤ S.size := by unfold QStrategy.size; omega
  rw [hsz, hlift]
  omega

/-! ### Negligibility -/

theorem negl_combo (f g e : ℕ → ℝ) (hf : CompNonlocal.Negligible f) (hg : CompNonlocal.Negligible g)
    (he : ∀ n, 2 ≤ n → e n = 0) : CompNonlocal.Negligible (fun n => |f n| + |g n| + e n) := by
  intro P
  have h1 := hf P
  have h2 := hg P
  have : Filter.Tendsto (fun n : ℕ => |f n| * P.eval (n : ℝ) + |g n| * P.eval (n : ℝ))
      Filter.atTop (nhds 0) := by simpa using h1.add h2
  refine this.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  rw [he n hn, add_zero, abs_of_nonneg (add_nonneg (abs_nonneg (f n)) (abs_nonneg (g n)))]
  ring

/-- The `π`-binding adversaries built from `S`. -/
def advFam (S : ℕ → QStrategy) (a : Bool) : ℕ → QStrategy
  | 0 => S 0
  | 1 => S 1
  | k + 2 => advPi (S (k + 2)) k a

theorem advFam_qpt (S : ℕ → QStrategy) (hS : IsQPT S) (a : Bool) : IsQPT (advFam S a) := by
  obtain ⟨hV, p, hp⟩ := hS
  refine ⟨fun n => ?_, Polynomial.C 6 * p + Polynomial.C 5 * Polynomial.X + Polynomial.C 2, fun n => ?_⟩
  · match n with
    | 0 => exact hV 0
    | 1 => exact hV 1
    | k + 2 => exact advPi_valid _ (hV _) k a
  · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    match n with
    | 0 => have := hp 0; show (S 0).size ≤ _; omega
    | 1 => have := hp 1; show (S 1).size ≤ _; omega
    | k + 2 =>
      have := hp (k + 2)
      have := advPi_size (S (k + 2)) k a
      show (advPi (S (k + 2)) k a).size ≤ _
      push_cast
      omega

theorem novy_openOnce' (π : PermFamily) (hbind : IsPiBinding π) : (novy π).IsOpenOnceBinding := by
  intro S hS
  obtain ⟨μ0, hμ0, hb0⟩ := hbind (advFam S false) (advFam_qpt S hS false)
  obtain ⟨μ1, hμ1, hb1⟩ := hbind (advFam S true) (advFam_qpt S hS true)
  refine ⟨fun n => |μ0 n| + |μ1 n| + (if n < 2 then |openBothProb (novy π) (S n) n| else 0),
    negl_combo μ0 μ1 _ hμ0 hμ1 (fun n hn => by simp; omega), fun n => ?_⟩
  match n with
  | 0 =>
    simp only [show (0 : ℕ) < 2 by norm_num, if_true]
    have := le_abs_self (openBothProb (novy π) (S 0) 0)
    have := abs_nonneg (μ0 0); have := abs_nonneg (μ1 0)
    linarith
  | 1 =>
    simp only [show (1 : ℕ) < 2 by norm_num, if_true]
    have := le_abs_self (openBothProb (novy π) (S 1) 1)
    have := abs_nonneg (μ0 1); have := abs_nonneg (μ1 1)
    linarith
  | k + 2 =>
    simp only [show ¬ (k + 2 < 2) by omega, if_false, add_zero]
    have h := openBoth_le π (S (k + 2)) k
    have h0 : piBindProb π (advPi (S (k + 2)) k false) (k + 2) ≤ μ0 (k + 2) := hb0 (k + 2)
    have h1 : piBindProb π (advPi (S (k + 2)) k true) (k + 2) ≤ μ1 (k + 2) := hb1 (k + 2)
    have := le_abs_self (μ0 (k + 2)); have := le_abs_self (μ1 (k + 2))
    linarith


/-! ## Assembly -/

/-- OPEN: the machine-model part of `IsPPT` for novy. -/
theorem novy_polyTime_parts (π : PermFamily) (hπ : π.IsPolyTime) :
    PolyTimeFn (fun s => (novy π).setup s.length) ∧ PolyTimeNat (fun s => (novy π).rounds s.length) ∧
    PolyTimeFn (fun s => pack (((novy π).sender.coins s).map natToBits)) ∧
    PolyTimeFn (novy π).sender.next ∧
    PolyTimeFn (fun s => pack (((novy π).receiver.coins s).map natToBits)) ∧
    PolyTimeFn (novy π).receiver.next ∧
    PolyTimeFn (fun s => pack [((novy π).sopen s).1, ((novy π).sopen s).2]) ∧
    PolyTimeFn (fun s => match unpack s with
      | m :: u :: pub :: privR :: comm => [(novy π).ropen m u comm privR pub]
      | _ => [false]) :=
  PT.polyTime_parts π hπ

theorem novy_isPPT (π : PermFamily) (hπ : π.IsPolyTime) : (novy π).IsPPT := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := novy_polyTime_parts π hπ
  refine ⟨h1, h2, ⟨h3, h4, ?_, ?_⟩, ⟨h5, h6, ?_, ?_⟩, h7, ?_, h8⟩
  · intro s m hm
    simp only [novy, novySender] at hm
    split at hm
    · simp at hm; subst hm; positivity
    · simp at hm
  · refine ⟨Polynomial.C 1, fun inp c msgs => ?_⟩
    simp only [Polynomial.eval_C, Party.msg, novy, novySender]
    split
    · split
      · split_ifs <;> simp
      · simp
    · simp
  · intro s m hm
    simp only [novy, novyReceiver, List.mem_map, List.mem_range] at hm
    obtain ⟨j, _, rfl⟩ := hm; positivity
  · refine ⟨Polynomial.X, fun inp c msgs => ?_⟩
    simp only [Polynomial.eval_X, Party.msg, Party.view, novy, novyReceiver, unpack_pack]
    split_ifs with hj
    · simp [msbStr_length]; omega
    · simp
  · refine ⟨Polynomial.C 2 + 5 * Polynomial.X, fun inp c msgs => ?_⟩
    simp only [Party.view, novy, novySopen, unpack_pack]
    split
    · rename_i m pub hmp
      have := unpack_two_le hmp
      simp only [pack_two_length, applyStr_length, novyX, msbStr_length, Polynomial.eval_add,
        Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      omega
    · simp


theorem novy_uniqueOpenings (π : PermFamily) : (novy π).HasUniqueOpenings := by
  intro comm privR pub b u u' h h'
  obtain ⟨x, y, hu, hx, hxy, hy⟩ := novy_ropen_spec π comm privR pub b u h
  obtain ⟨x', y', hu', hx', hxy', hy'⟩ := novy_ropen_spec π comm privR pub b u' h'
  have hyy : y = y' := hy.trans hy'.symm
  have hxx : x = x' := applyStr_inj π (hx.trans hx'.symm) (by rw [hxy, hxy', hyy])
  rw [hu, hu', hxx, hyy]


/-- Classical core of the open-once reduction: if `u₀` or `u₁` opens each bit, then for each
`β` one of them is `pack [x, y]` with `|x| = n` and `π_n(x) = y_β`. -/
theorem novy_openBoth_classical (π : PermFamily) (comm : List Bits) (privR pub u0 u1 : Bits)
    (h : ∀ b : Bool, novyRopen π [b] u0 comm privR pub = true ∨ novyRopen π [b] u1 comm privR pub = true)
    (β : Bool) :
    ∃ u ∈ [u0, u1], ∃ x y, u = pack [x, y] ∧ x.length = pub.length ∧
      π.applyStr x = (consistentList pub.length ((List.range (pub.length - 1)).map fun i => comm.getD (2 * i) [])
            (((List.range (pub.length - 1)).map fun i => comm.getD (2 * i + 1) []).map fun z => z.headD false)).getD
          β.toNat [] := by
  have hb : xor (xor β ((comm.getD (2 * (pub.length - 1) + 1) []).headD false))
      ((comm.getD (2 * (pub.length - 1) + 1) []).headD false) = β := by simp
  rcases h (xor β ((comm.getD (2 * (pub.length - 1) + 1) []).headD false)) with h | h
  · obtain ⟨x, y, hu, hx, hxy, hy⟩ := novy_ropen_spec π comm privR pub _ u0 h
    rw [hb] at hy
    exact ⟨u0, by simp, x, y, hu, hx, hxy.trans hy⟩
  · obtain ⟨x, y, hu, hx, hxy, hy⟩ := novy_ropen_spec π comm privR pub _ u1 h
    rw [hb] at hy
    exact ⟨u1, by simp, x, y, hu, hx, hxy.trans hy⟩

/-- An open-both adversary yields two `π`-binding adversaries (one per order of the two openings);
proved above as `novy_openOnce'`. -/
theorem novy_openOnce (π : PermFamily) (hbind : IsPiBinding π) : (novy π).IsOpenOnceBinding :=
  novy_openOnce' π hbind

theorem corollary_1_proof (π : PermFamily) (hπ : π.IsPolyTime) (hbind : IsPiBinding π) :
    (novy π).IsSumBinding ∧ (novy π).IsCollapseBinding :=
  ⟨lemma_4 (novy π) (novy_isPPT π hπ) (novy_isBit π) (novy_uniqueOpenings π) (novy_openOnce π hbind),
   lemma_5 (novy π) (novy_isPPT π hπ) (novy_isBit π) (novy_uniqueOpenings π) (novy_openOnce π hbind)⟩

end NovyPQZK.Main

theorem solution (π : NovyPQZK.Main.PermFamily) (hπ : π.IsPolyTime) (hbind : NovyPQZK.Main.IsPiBinding π) :
    (NovyPQZK.Main.novy π).IsSumBinding ∧ (NovyPQZK.Main.novy π).IsCollapseBinding :=
  NovyPQZK.Main.corollary_1_proof π hπ hbind
