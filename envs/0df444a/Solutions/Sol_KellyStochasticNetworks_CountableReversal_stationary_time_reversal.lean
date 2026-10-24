-- Prove2me | solution 1 for KellyStochasticNetworks.CountableReversal.stationary_time_reversal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T09:06:09.148842+00:00
-- url     : https://prove2.me/submissions/cf59157f-c781-483e-9a62-1697f29f391e

import Mathlib

open MeasureTheory Filter Set
open scoped BigOperators Topology

set_option linter.unusedSectionVars false

namespace X5RV

variable {Ω S : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ → Ω → S)

def cyl {n : ℕ} (t : Fin n → ℝ) (x : Fin n → S) : Set Ω := {ω | ∀ i, X (t i) ω = x i}

noncomputable def T (a b : ℝ) (i j : S) : ℝ :=
  (P ({ω | X b ω = j} ∩ {ω | X a ω = i})).toReal / (P {ω | X a ω = i}).toReal

/-- Markov hypothesis in product form (no positivity needed). -/
lemma mk_mul
    (hmk : ∀ (n : ℕ) (t : Fin n → ℝ) (x : Fin n → S) (s u : ℝ) (j k : S),
        StrictMono t → (∀ i, t i < s) → s < u →
        0 < (P (cyl X t x ∩ {ω | X s ω = j})).toReal →
        (P ({ω | X u ω = k} ∩ (cyl X t x ∩ {ω | X s ω = j}))).toReal /
            (P (cyl X t x ∩ {ω | X s ω = j})).toReal =
          (P ({ω | X u ω = k} ∩ {ω | X s ω = j})).toReal / (P {ω | X s ω = j}).toReal)
    {n : ℕ} (t : Fin n → ℝ) (x : Fin n → S) (s u : ℝ) (j k : S)
    (ht : StrictMono t) (hts : ∀ i, t i < s) (hsu : s < u) :
    (P ({ω | X u ω = k} ∩ (cyl X t x ∩ {ω | X s ω = j}))).toReal =
      (P (cyl X t x ∩ {ω | X s ω = j})).toReal * T P X s u j k := by
  by_cases h : 0 < (P (cyl X t x ∩ {ω | X s ω = j})).toReal
  · have := hmk n t x s u j k ht hts hsu h
    rw [T, ← this]; field_simp
  · have h0 : (P (cyl X t x ∩ {ω | X s ω = j})).toReal = 0 :=
      le_antisymm (not_lt.1 h) ENNReal.toReal_nonneg
    have h0' : P (cyl X t x ∩ {ω | X s ω = j}) = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).1 h0 with h1 | h1
      · exact h1
      · exact absurd h1 (measure_ne_top _ _)
    rw [h0, zero_mul, measure_mono_null Set.inter_subset_right h0', ENNReal.toReal_zero]

lemma cyl_snoc {n : ℕ} (τ : Fin (n + 1) → ℝ) (ξ : Fin (n + 1) → S) :
    cyl X τ ξ = cyl X (Fin.init τ) (Fin.init ξ) ∩ {ω | X (τ (Fin.last n)) ω = ξ (Fin.last n)} := by
  ext ω
  simp only [cyl, Set.mem_inter_iff, Set.mem_setOf_eq, Fin.forall_fin_succ', Fin.init]

lemma cyl_cons {n : ℕ} (w : ℝ) (y : S) (τ : Fin n → ℝ) (ξ : Fin n → S) :
    cyl X (Fin.cons w τ : Fin (n + 1) → ℝ) (Fin.cons y ξ : Fin (n + 1) → S) =
      {ω | X w ω = y} ∩ cyl X τ ξ := by
  ext ω
  simp only [cyl, Set.mem_inter_iff, Set.mem_setOf_eq, Fin.forall_fin_succ, Fin.cons_zero,
    Fin.cons_succ]

variable {P X}

lemma M2
    (hmk : ∀ (n : ℕ) (t : Fin n → ℝ) (x : Fin n → S) (s u : ℝ) (j k : S),
        StrictMono t → (∀ i, t i < s) → s < u →
        0 < (P (cyl X t x ∩ {ω | X s ω = j})).toReal →
        (P ({ω | X u ω = k} ∩ (cyl X t x ∩ {ω | X s ω = j}))).toReal /
            (P (cyl X t x ∩ {ω | X s ω = j})).toReal =
          (P ({ω | X u ω = k} ∩ {ω | X s ω = j})).toReal / (P {ω | X s ω = j}).toReal)
    {m : ℕ} (τ : Fin (m + 1) → ℝ) (ξ : Fin (m + 1) → S) (hτ : StrictMono τ) (u : ℝ) (k : S)
    (hu : τ (Fin.last m) < u) :
    (P ({ω | X u ω = k} ∩ cyl X τ ξ)).toReal =
      (P (cyl X τ ξ)).toReal * T P X (τ (Fin.last m)) u (ξ (Fin.last m)) k := by
  rw [cyl_snoc]
  exact mk_mul P X hmk _ _ _ _ _ _ (hτ.comp (Fin.strictMono_castSucc))
    (fun i => hτ (Fin.castSucc_lt_last i)) hu

lemma prepend
    (hmk : ∀ (n : ℕ) (t : Fin n → ℝ) (x : Fin n → S) (s u : ℝ) (j k : S),
        StrictMono t → (∀ i, t i < s) → s < u →
        0 < (P (cyl X t x ∩ {ω | X s ω = j})).toReal →
        (P ({ω | X u ω = k} ∩ (cyl X t x ∩ {ω | X s ω = j}))).toReal /
            (P (cyl X t x ∩ {ω | X s ω = j})).toReal =
          (P ({ω | X u ω = k} ∩ {ω | X s ω = j})).toReal / (P {ω | X s ω = j}).toReal)
    (w : ℝ) (y : S) :
    ∀ (n : ℕ) (τ : Fin (n + 1) → ℝ) (ξ : Fin (n + 1) → S), StrictMono τ → w < τ 0 →
      (P ({ω | X w ω = y} ∩ cyl X τ ξ)).toReal * (P {ω | X (τ 0) ω = ξ 0}).toReal =
        (P ({ω | X w ω = y} ∩ {ω | X (τ 0) ω = ξ 0})).toReal * (P (cyl X τ ξ)).toReal := by
  intro n
  induction n with
  | zero =>
    intro τ ξ _ _
    have : cyl X τ ξ = {ω | X (τ 0) ω = ξ 0} := by
      ext ω
      simp only [cyl, Set.mem_setOf_eq]
      refine ⟨fun h => h 0, fun h i => ?_⟩
      obtain rfl : i = 0 := Fin.fin_one_eq_zero i
      exact h
    rw [this]
  | succ n ih =>
    intro τ ξ hτ hw
    have hτ' : StrictMono (Fin.init τ) := hτ.comp Fin.strictMono_castSucc
    have h0 : Fin.init τ 0 = τ 0 := rfl
    have h0' : Fin.init ξ 0 = ξ 0 := rfl
    have hc : StrictMono (Fin.cons w (Fin.init τ) : Fin (n + 2) → ℝ) := by
      rw [Fin.strictMono_cons]
      exact ⟨fun j => lt_of_lt_of_le hw (hτ.monotone (Fin.zero_le _)), hτ'⟩
    have hlast : (Fin.cons w (Fin.init τ) : Fin (n + 2) → ℝ) (Fin.last (n + 1)) =
        Fin.init τ (Fin.last n) := by
      rw [← Fin.succ_last, Fin.cons_succ]
    have hlastx : (Fin.cons y (Fin.init ξ) : Fin (n + 2) → S) (Fin.last (n + 1)) =
        Fin.init ξ (Fin.last n) := by
      rw [← Fin.succ_last, Fin.cons_succ]
    have hlt : Fin.init τ (Fin.last n) < τ (Fin.last (n + 1)) := hτ (Fin.castSucc_lt_last _)
    -- step for the cylinder with w prepended
    have e1 := M2 hmk _ (Fin.cons y (Fin.init ξ)) hc (τ (Fin.last (n + 1))) (ξ (Fin.last (n + 1)))
      (by rw [hlast]; exact hlt)
    rw [hlast, hlastx, cyl_cons] at e1
    -- step for the cylinder itself
    have e2 := M2 hmk (Fin.init τ) (Fin.init ξ) hτ' (τ (Fin.last (n + 1))) (ξ (Fin.last (n + 1))) hlt
    have s1 : {ω | X w ω = y} ∩ cyl X τ ξ =
        {ω | X (τ (Fin.last (n + 1))) ω = ξ (Fin.last (n + 1))} ∩
          ({ω | X w ω = y} ∩ cyl X (Fin.init τ) (Fin.init ξ)) := by
      rw [cyl_snoc]; ext ω; simp only [Set.mem_inter_iff]; tauto
    have s2 : cyl X τ ξ = {ω | X (τ (Fin.last (n + 1))) ω = ξ (Fin.last (n + 1))} ∩
        cyl X (Fin.init τ) (Fin.init ξ) := by
      rw [cyl_snoc, Set.inter_comm]
    have ih' := ih (Fin.init τ) (Fin.init ξ) hτ' (by rw [h0]; exact hw)
    rw [h0, h0'] at ih'
    rw [s1, e1, s2, e2]
    calc (P ({ω | X w ω = y} ∩ cyl X (Fin.init τ) (Fin.init ξ))).toReal * _ * (P {ω | X (τ 0) ω = ξ 0}).toReal
        = ((P ({ω | X w ω = y} ∩ cyl X (Fin.init τ) (Fin.init ξ))).toReal *
            (P {ω | X (τ 0) ω = ξ 0}).toReal) * T P X (Fin.init τ (Fin.last n))
              (τ (Fin.last (n + 1))) (Fin.init ξ (Fin.last n)) (ξ (Fin.last (n + 1))) := by ring
      _ = _ := by rw [ih']; ring

end X5RV



theorem solution {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S] [Nonempty S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → S) (q : S → S → ℝ) (π : S → ℝ) :
    let cp := fun (A B : Set Ω) => (P (A ∩ B)).toReal / (P B).toReal
    let cylinder := fun (Z : ℝ → Ω → S) (n : ℕ)
      (t : Fin n → ℝ) (x : Fin n → S) => {ω | ∀ i, Z (t i) ω = x i}
    let markov := fun (Z : ℝ → Ω → S) =>
      ∀ (n : ℕ) (t : Fin n → ℝ) (x : Fin n → S) (s u : ℝ) (j k : S),
        StrictMono t → (∀ i, t i < s) → s < u →
        0 < (P (cylinder Z n t x ∩ {ω | Z s ω = j})).toReal →
        cp {ω | Z u ω = k} (cylinder Z n t x ∩ {ω | Z s ω = j}) =
          cp {ω | Z u ω = k} {ω | Z s ω = j}
    let stationary := fun (Z : ℝ → Ω → S) =>
      ∀ (n : ℕ) (t : Fin n → ℝ) (x : Fin n → S) (h : ℝ),
        P (cylinder Z n (fun i => t i + h) x) = P (cylinder Z n t x)
    let regular := fun (Z : ℝ → Ω → S) =>
      ∀ᵐ ω ∂P,
        (∀ a b : ℝ, ∃ D : Finset ℝ,
          ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
            (∀ u ∈ D, u ∉ Icc s t) → Z s ω = Z t ω) ∧
        (∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∃ l r : S,
          (∀ s ∈ Ioo (t - ε) t, Z s ω = l) ∧
          (∀ s ∈ Ioo t (t + ε), Z s ω = r) ∧
          (Z t ω = l ∨ Z t ω = r))
    let rateData := fun (Q : S → S → ℝ) =>
      (∀ j k, 0 ≤ Q j k) ∧ (∀ j, Q j j = 0) ∧
      (∀ j, Summable (Q j)) ∧ (∀ j, 0 < ∑' k, Q j k) ∧
      (∀ j k, Relation.ReflTransGen (fun a b => 0 < Q a b) j k)
    let equilibrium := fun (Q : S → S → ℝ) =>
      (∀ j, 0 < π j) ∧ HasSum π 1 ∧
        (∀ j, HasSum (fun k => π k * Q k j) (π j * ∑' k, Q j k))
    let rates := fun (Z : ℝ → Ω → S) (Q : S → S → ℝ) =>
      ∀ (t : ℝ) (j k : S), j ≠ k →
        Tendsto (fun h : ℝ => cp {ω | Z (t + h) ω = k} {ω | Z t ω = j} / h)
          (𝓝[>] (0 : ℝ)) (𝓝 (Q j k))
    let Y := fun t ω => X (-t) ω
    let q' := fun j k => π k * q k j / π j
    (∀ t, Measurable (X t)) → regular X → markov X → stationary X →
      rateData q → equilibrium q →
      (∀ t j, (P {ω | X t ω = j}).toReal = π j) → rates X q →
    (∀ t, Measurable (Y t)) ∧ regular Y ∧ markov Y ∧ stationary Y ∧
      rateData q' ∧ equilibrium q' ∧
      (∀ t j, (P {ω | Y t ω = j}).toReal = π j) ∧ rates Y q' := by
  intro cp cylinder markov stationary regular rateData equilibrium rates Y q'
  intro hmeas hreg hmk hst hrd heq hlaw hrates
  obtain ⟨hq0, hqd, hqs, hqp, hqirr⟩ := hrd
  obtain ⟨hπpos, hπ1, hbal⟩ := heq
  have hmk' : ∀ (n : ℕ) (t : Fin n → ℝ) (x : Fin n → S) (s u : ℝ) (j k : S),
      StrictMono t → (∀ i, t i < s) → s < u →
      0 < (P (X5RV.cyl X t x ∩ {ω | X s ω = j})).toReal →
      (P ({ω | X u ω = k} ∩ (X5RV.cyl X t x ∩ {ω | X s ω = j}))).toReal /
          (P (X5RV.cyl X t x ∩ {ω | X s ω = j})).toReal =
        (P ({ω | X u ω = k} ∩ {ω | X s ω = j})).toReal / (P {ω | X s ω = j}).toReal :=
    fun n t x s u j k ht hts hsu hpos => hmk n t x s u j k ht hts hsu hpos
  have hsum : ∀ j, ∑' k, q' j k = ∑' k, q j k := by
    intro j
    show ∑' k, π k * q k j / π j = _
    rw [tsum_div_const, (hbal j).tsum_eq]
    field_simp [(hπpos j).ne']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t; exact hmeas (-t)
  · filter_upwards [hreg] with ω hω
    obtain ⟨h1, h2⟩ := hω
    refine ⟨fun a b => ?_, fun t => ?_⟩
    · obtain ⟨D, hD⟩ := h1 (-b) (-a)
      refine ⟨D.image (fun u => -u), fun s hs t ht hst hno => ?_⟩
      have := hD (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ (-s)
        ⟨by linarith [hs.2], by linarith [hs.1]⟩ (by linarith)
        (fun u hu hmem => hno (-u) (Finset.mem_image_of_mem _ hu)
          ⟨by linarith [hmem.2], by linarith [hmem.1]⟩)
      exact this.symm
    · obtain ⟨ε, hε, l, r, hl, hr, hlr⟩ := h2 (-t)
      exact ⟨ε, hε, r, l, fun s hs => hr (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩,
        fun s hs => hl (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩, hlr.symm⟩
  · intro n t x s u j k ht hts hsu hpos
    set τ : Fin (n + 1) → ℝ := Fin.cons (-s) (fun i => -(t (Fin.rev i))) with hτdef
    set ξ : Fin (n + 1) → S := Fin.cons j (fun i => x (Fin.rev i)) with hξdef
    have hτ : StrictMono τ := Fin.strictMono_cons.2
      ⟨fun i => by linarith [hts (Fin.rev i)],
        fun a b hab => neg_lt_neg (ht (Fin.rev_lt_rev.2 hab))⟩
    have hset : cylinder Y n t x ∩ {ω | Y s ω = j} = X5RV.cyl X τ ξ := by
      rw [hτdef, hξdef, X5RV.cyl_cons]
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, X5RV.cyl, cylinder, Y]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h2, fun i => h1 (Fin.rev i)⟩
      · rintro ⟨h2, h1⟩
        refine ⟨fun i => ?_, h2⟩
        have := h1 (Fin.rev i); rwa [Fin.rev_rev] at this
    have hpre := X5RV.prepend hmk' (-u) k n τ ξ hτ (by
      show -u < -s; linarith)
    have hYs : (P {ω | Y s ω = j}).toReal = π j := hlaw (-s) j
    show (P ({ω | Y u ω = k} ∩ (cylinder Y n t x ∩ {ω | Y s ω = j}))).toReal /
        (P (cylinder Y n t x ∩ {ω | Y s ω = j})).toReal =
      (P ({ω | Y u ω = k} ∩ {ω | Y s ω = j})).toReal / (P {ω | Y s ω = j}).toReal
    rw [hset] at hpos ⊢
    rw [div_eq_div_iff hpos.ne' (by rw [hYs]; exact (hπpos j).ne')]
    exact hpre
  · intro n t x h
    have := hst n (fun i => -(t i)) x (-h)
    have e : ∀ i, -(t i + h) = -(t i) + -h := fun i => by ring
    show P {ω | ∀ i, X (-(t i + h)) ω = x i} = P {ω | ∀ i, X (-(t i)) ω = x i}
    simp only [e]
    exact this
  · refine ⟨fun j k => div_nonneg (mul_nonneg (hπpos k).le (hq0 k j)) (hπpos j).le,
      fun j => ?_, fun j => ?_, fun j => ?_, fun j k => ?_⟩
    · show π j * q j j / π j = 0
      rw [hqd, mul_zero, zero_div]
    · exact (hbal j).summable.div_const _
    · rw [hsum]; exact hqp j
    · have h1 := hqirr k j
      have h2 : Relation.ReflTransGen (Function.swap (fun a b => 0 < q a b)) j k :=
        Relation.ReflTransGen.swap (r := fun a b => 0 < q a b) j k h1
      exact Relation.ReflTransGen.mono
        (fun a b hab => div_pos (mul_pos (hπpos b) hab) (hπpos a)) j k h2
  · refine ⟨hπpos, hπ1, fun j => ?_⟩
    rw [hsum j]
    have : (fun k => π k * q' k j) = fun k => π j * q j k := by
      funext k
      show π k * (π j * q j k / π k) = _
      field_simp [(hπpos k).ne']
    rw [this]
    exact (hqs j).hasSum.mul_left (π j)
  · intro t j; exact hlaw (-t) j
  · intro t j k hjk
    have hX := hrates (-t) k j (Ne.symm hjk)
    have hfun : (fun h : ℝ => cp {ω | Y (t + h) ω = k} {ω | Y t ω = j} / h) =
        fun h => (π k / π j) * (cp {ω | X (-t + h) ω = j} {ω | X (-t) ω = k} / h) := by
      funext h
      show (P ({ω | X (-(t + h)) ω = k} ∩ {ω | X (-t) ω = j})).toReal /
          (P {ω | X (-t) ω = j}).toReal / h =
        π k / π j * ((P ({ω | X (-t + h) ω = j} ∩ {ω | X (-t) ω = k})).toReal /
          (P {ω | X (-t) ω = k}).toReal / h)
      have e := hst 2 ![-(t + h), -t] ![k, j] h
      have s1 : cylinder X 2 (fun i => ![-(t + h), -t] i + h) ![k, j] =
          {ω | X (-t + h) ω = j} ∩ {ω | X (-t) ω = k} := by
        ext ω
        simp only [cylinder, Set.mem_setOf_eq, Set.mem_inter_iff, Fin.forall_fin_two,
          Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [show -(t + h) + h = -t by ring]
        tauto
      have s2 : cylinder X 2 ![-(t + h), -t] ![k, j] =
          {ω | X (-(t + h)) ω = k} ∩ {ω | X (-t) ω = j} := by
        ext ω
        simp only [cylinder, Set.mem_setOf_eq, Set.mem_inter_iff, Fin.forall_fin_two,
          Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [s1, s2] at e
      rw [← e, hlaw (-t) j, hlaw (-t) k]
      field_simp [(hπpos j).ne', (hπpos k).ne']
    rw [hfun]
    have := hX.const_mul (π k / π j)
    convert this using 2
    show π k * q k j / π j = π k / π j * q k j
    ring

