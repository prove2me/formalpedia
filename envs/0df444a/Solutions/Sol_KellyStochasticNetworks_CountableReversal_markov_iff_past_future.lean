-- Prove2me | solution 1 for KellyStochasticNetworks.CountableReversal.markov_iff_past_future
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T16:51:23.540181+00:00
-- url     : https://prove2.me/submissions/4eba743c-7af0-45e3-bdce-6d7c5644a057

import Mathlib

open MeasureTheory

section
variable {Ω S : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ → Ω → S)

def g81m_cyl (L : List (ℝ × S)) : Set Ω := {ω | ∀ p ∈ L, X p.1 ω = p.2}

theorem g81m_cyl_append (L M : List (ℝ × S)) :
    g81m_cyl X (L ++ M) = g81m_cyl X L ∩ g81m_cyl X M := by
  ext ω; simp [g81m_cyl, or_imp, forall_and]

theorem g81m_cyl_single (p : ℝ × S) : g81m_cyl X [p] = {ω | X p.1 ω = p.2} := by
  ext ω; simp [g81m_cyl]

theorem g81m_cyl_cons (p : ℝ × S) (L : List (ℝ × S)) :
    g81m_cyl X (p :: L) = {ω | X p.1 ω = p.2} ∩ g81m_cyl X L := by
  rw [show p :: L = [p] ++ L from rfl, g81m_cyl_append, g81m_cyl_single]

/-- Markov property in list form, multiplicative. -/
def g81m_ML : Prop :=
  ∀ (L : List (ℝ × S)) (s u : ℝ) (j k : S), L.Pairwise (fun p q => p.1 < q.1) →
    (∀ p ∈ L, p.1 < s) → s < u →
    P.real ({ω | X u ω = k} ∩ (g81m_cyl X L ∩ {ω | X s ω = j})) * P.real {ω | X s ω = j} =
      P.real (g81m_cyl X L ∩ {ω | X s ω = j}) * P.real ({ω | X u ω = k} ∩ {ω | X s ω = j})

theorem g81m_M2 [IsFiniteMeasure P] (hML : g81m_ML P X) (Q : List (ℝ × S)) (r u : ℝ) (q k : S)
    (hQ : (Q ++ [(r, q)]).Pairwise (fun p q => p.1 < q.1)) (hu : r < u) :
    P.real ({ω | X u ω = k} ∩ g81m_cyl X (Q ++ [(r, q)])) * P.real {ω | X r ω = q} =
      P.real (g81m_cyl X (Q ++ [(r, q)])) * P.real ({ω | X u ω = k} ∩ {ω | X r ω = q}) := by
  rw [List.pairwise_append] at hQ
  have h := hML Q r u q k hQ.1 (fun p hp => hQ.2.2 p hp (r, q) (by simp)) hu
  rw [g81m_cyl_append, g81m_cyl_single]
  exact h
theorem g81m_CI [IsFiniteMeasure P] (hML : g81m_ML P X) (F : List (ℝ × S)) :
    ∀ (A : List (ℝ × S)) (s : ℝ) (j : S), A.Pairwise (fun p q => p.1 < q.1) →
      F.Pairwise (fun p q => p.1 < q.1) → (∀ p ∈ A, p.1 < s) → (∀ p ∈ F, s < p.1) →
      P.real (g81m_cyl X A ∩ g81m_cyl X F ∩ {ω | X s ω = j}) * P.real {ω | X s ω = j} =
        P.real (g81m_cyl X F ∩ {ω | X s ω = j}) * P.real (g81m_cyl X A ∩ {ω | X s ω = j}) := by
  induction F using List.reverseRecOn with
  | nil =>
    intro A s j _ _ _ _
    have : g81m_cyl X ([] : List (ℝ × S)) = Set.univ := by ext; simp [g81m_cyl]
    rw [this, Set.inter_univ, Set.univ_inter]; ring
  | append_singleton F' uk ih =>
    intro A s j hA hF hAs hFs
    obtain ⟨u, k⟩ := uk
    rw [List.pairwise_append] at hF
    have hF' := hF.1
    have hlt : ∀ p ∈ F', p.1 < u := fun p hp => hF.2.2 p hp (u, k) (by simp)
    have hsu : s < u := hFs (u, k) (by simp)
    have hIH := ih A s j hA hF' hAs (fun p hp => hFs p (by simp [hp]))
    set Q' : List (ℝ × S) := (s, j) :: F' with hQ'
    have hne : Q' ≠ [] := by simp [hQ']
    set r := (Q'.getLast hne).1
    set q := (Q'.getLast hne).2
    have hsplit : Q' = Q'.dropLast ++ [(r, q)] := by
      simp only [r, q, Prod.mk.eta]; exact (List.dropLast_append_getLast hne).symm
    have hrmem : (r, q) ∈ Q' := by simp only [r, q, Prod.mk.eta]; exact List.getLast_mem hne
    have hru : r < u := by
      rw [hQ'] at hrmem
      rcases List.mem_cons.1 hrmem with h | h
      · rw [show r = s from congrArg Prod.fst h]; exact hsu
      · exact hlt _ h
    have hQ'pw : Q'.Pairwise (fun p q => p.1 < q.1) := by
      rw [hQ', List.pairwise_cons]
      exact ⟨fun p hp => hFs p (by simp [hp]), hF'⟩
    have hQpw : (A ++ Q').Pairwise (fun p q => p.1 < q.1) := by
      rw [List.pairwise_append]
      refine ⟨hA, hQ'pw, fun p hp p' hp' => ?_⟩
      rw [hQ'] at hp'
      rcases List.mem_cons.1 hp' with h | h
      · rw [h]; exact hAs p hp
      · exact (hAs p hp).trans (hFs p' (by simp [h]))
    have M1 := g81m_M2 P X hML (A ++ Q'.dropLast) r u q k
      (by rw [List.append_assoc, ← hsplit]; exact hQpw) hru
    have M2 := g81m_M2 P X hML Q'.dropLast r u q k (by rw [← hsplit]; exact hQ'pw) hru
    rw [List.append_assoc, ← hsplit] at M1
    rw [← hsplit] at M2
    have cQ : g81m_cyl X (A ++ Q') = g81m_cyl X A ∩ g81m_cyl X F' ∩ {ω | X s ω = j} := by
      rw [g81m_cyl_append, hQ', g81m_cyl_cons]; ext ω; simp only [Set.mem_inter_iff]; tauto
    have cQ' : g81m_cyl X Q' = g81m_cyl X F' ∩ {ω | X s ω = j} := by
      rw [hQ', g81m_cyl_cons, Set.inter_comm]
    have cF : g81m_cyl X (F' ++ [(u, k)]) = g81m_cyl X F' ∩ {ω | X u ω = k} := by
      rw [g81m_cyl_append, g81m_cyl_single]
    have e1 : g81m_cyl X A ∩ g81m_cyl X (F' ++ [(u, k)]) ∩ {ω | X s ω = j} =
        {ω | X u ω = k} ∩ g81m_cyl X (A ++ Q') := by
      rw [cF, cQ]; ext ω; simp only [Set.mem_inter_iff]; tauto
    have e2 : g81m_cyl X (F' ++ [(u, k)]) ∩ {ω | X s ω = j} =
        {ω | X u ω = k} ∩ g81m_cyl X Q' := by
      rw [cF, cQ']; ext ω; simp only [Set.mem_inter_iff]; tauto
    rw [e1, e2]
    rw [← cQ, ← cQ'] at hIH
    by_cases he : P.real {ω | X r ω = q} = 0
    · -- the last state is null: everything vanishes
      have hsub' : g81m_cyl X Q' ⊆ {ω | X r ω = q} := by
        intro ω hω; exact hω (r, q) hrmem
      have hsub : g81m_cyl X (A ++ Q') ⊆ {ω | X r ω = q} := by
        intro ω hω; exact hω (r, q) (List.mem_append_right _ hrmem)
      have z1 : P.real ({ω | X u ω = k} ∩ g81m_cyl X (A ++ Q')) = 0 :=
        le_antisymm ((measureReal_mono (Set.inter_subset_right.trans hsub)).trans he.le)
          measureReal_nonneg
      have z2 : P.real ({ω | X u ω = k} ∩ g81m_cyl X Q') = 0 :=
        le_antisymm ((measureReal_mono (Set.inter_subset_right.trans hsub')).trans he.le)
          measureReal_nonneg
      rw [z1, z2]; ring
    · apply mul_right_cancel₀ he
      calc P.real ({ω | X u ω = k} ∩ g81m_cyl X (A ++ Q')) * P.real {ω | X s ω = j} *
            P.real {ω | X r ω = q}
          = P.real (g81m_cyl X (A ++ Q')) * P.real {ω | X s ω = j} *
              P.real ({ω | X u ω = k} ∩ {ω | X r ω = q}) := by
            rw [mul_right_comm, M1]; ring
        _ = P.real (g81m_cyl X Q') * P.real (g81m_cyl X A ∩ {ω | X s ω = j}) *
              P.real ({ω | X u ω = k} ∩ {ω | X r ω = q}) := by rw [hIH]
        _ = _ := by
            have := M2
            linear_combination (-(P.real (g81m_cyl X A ∩ {ω | X s ω = j}))) * this
end


theorem g81m_cylC {Ω S : Type*} (X : ℝ → Ω → S) (n : ℕ) (t : Fin n → ℝ) (x : Fin n → S) :
    {ω | ∀ i, X (t i) ω = x i} = g81m_cyl X (List.ofFn (fun i => (t i, x i))) := by
  ext ω; simp [g81m_cyl, List.mem_ofFn]

theorem g81m_pw {S : Type*} {n : ℕ} {t : Fin n → ℝ} (x : Fin n → S) (ht : StrictMono t) :
    (List.ofFn (fun i => (t i, x i))).Pairwise (fun p q => p.1 < q.1) :=
  List.pairwise_ofFn.2 fun _ _ hij => ht hij

theorem g81m_memlt {S : Type*} {n : ℕ} {t : Fin n → ℝ} (x : Fin n → S) {s : ℝ}
    (hts : ∀ i, t i < s) : ∀ p ∈ List.ofFn (fun i => (t i, x i)), p.1 < s := by
  intro p hp; obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp; exact hts i

theorem g81m_memgt {S : Type*} {n : ℕ} {t : Fin n → ℝ} (x : Fin n → S) {s : ℝ}
    (hts : ∀ i, s < t i) : ∀ p ∈ List.ofFn (fun i => (t i, x i)), s < p.1 := by
  intro p hp; obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp; exact hts i

theorem solution {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → S) (hX : ∀ t, Measurable (X t)) :
    let E := fun (t : ℝ) (j : S) =>
      (⟨{ω | X t ω = j}, hX t (measurableSet_singleton j)⟩ :
        {A : Set Ω // MeasurableSet A})
    let C := fun (n : ℕ) (t : Fin n → ℝ) (x : Fin n → S) =>
      (⟨{ω | ∀ i, X (t i) ω = x i}, by
        simpa only [Set.ofPred_forall, Set.preimage, Set.mem_singleton_iff] using
          MeasurableSet.iInter (fun i => hX (t i) (measurableSet_singleton (x i)))⟩ :
        {A : Set Ω // MeasurableSet A})
    let inter := fun (A B : {A : Set Ω // MeasurableSet A}) =>
      (⟨A.1 ∩ B.1, A.2.inter B.2⟩ : {A : Set Ω // MeasurableSet A})
    let cp := fun (A B : {A : Set Ω // MeasurableSet A}) =>
      (P (A.1 ∩ B.1)).toReal / (P B.1).toReal
    (∀ (n : ℕ) (t : Fin n → ℝ) (x : Fin n → S) (s u : ℝ) (j k : S),
      StrictMono t → (∀ i, t i < s) → s < u →
      0 < (P (inter (C n t x) (E s j)).1).toReal →
      cp (E u k) (inter (C n t x) (E s j)) = cp (E u k) (E s j)) ↔
    (∀ (m n : ℕ) (a : Fin m → ℝ) (b : Fin n → ℝ)
      (x : Fin m → S) (y : Fin n → S) (s : ℝ) (j : S),
      StrictMono a → StrictMono b → (∀ i, a i < s) → (∀ i, s < b i) →
      0 < (P (E s j).1).toReal →
      cp (inter (C m a x) (C n b y)) (E s j) =
        cp (C n b y) (E s j) * cp (C m a x) (E s j)) := by
  intro E C inter cp
  simp only [E, C, inter, cp]
  simp only [← measureReal_def]
  constructor
  · intro hM
    have hML : g81m_ML P X := by
      intro L s u j k hL hLs hsu
      by_cases h0 : P.real (g81m_cyl X L ∩ {ω | X s ω = j}) = 0
      · have : P.real ({ω | X u ω = k} ∩ (g81m_cyl X L ∩ {ω | X s ω = j})) = 0 :=
          le_antisymm ((measureReal_mono Set.inter_subset_right).trans h0.le) measureReal_nonneg
        rw [this, h0]; ring
      have hpos : 0 < P.real (g81m_cyl X L ∩ {ω | X s ω = j}) :=
        lt_of_le_of_ne measureReal_nonneg (Ne.symm h0)
      have hE : 0 < P.real {ω | X s ω = j} :=
        lt_of_lt_of_le hpos (measureReal_mono Set.inter_subset_right)
      have hLeq : L = List.ofFn (fun i : Fin L.length => ((L.get i).1, (L.get i).2)) := by
        simp
      have ht : StrictMono (fun i : Fin L.length => (L.get i).1) := by
        intro i i' hii'
        exact List.pairwise_iff_get.1 hL i i' hii'
      have key := hM L.length (fun i => (L.get i).1) (fun i => (L.get i).2) s u j k ht
        (fun i => hLs _ (List.get_mem L i)) hsu
      rw [g81m_cylC, ← hLeq] at key
      have key := key hpos
      field_simp at key
      linarith
    intro m n a b x y s j ha hb has hbs hE
    have hCI := g81m_CI P X hML (List.ofFn (fun i => (b i, y i))) (List.ofFn (fun i => (a i, x i)))
      s j (g81m_pw x ha) (g81m_pw y hb) (g81m_memlt x has) (g81m_memgt y hbs)
    rw [g81m_cylC X m a x, g81m_cylC X n b y]
    field_simp
    linarith
  · intro hCI n t x s u j k ht hts hsu hpos
    have hE : 0 < P.real {ω | X s ω = j} :=
      lt_of_lt_of_le hpos (measureReal_mono Set.inter_subset_right)
    have key := hCI n 1 t (fun _ => u) x (fun _ => k) s j ht
      (fun i i' h => absurd h (by simp [Subsingleton.elim i i'])) hts (fun _ => hsu) hE
    have hb : {ω | ∀ i : Fin 1, X u ω = k} = {ω | X u ω = k} := by ext ω; simp
    rw [hb] at key
    have e : {ω | X u ω = k} ∩ ({ω | ∀ i, X (t i) ω = x i} ∩ {ω | X s ω = j}) =
        {ω | ∀ i, X (t i) ω = x i} ∩ {ω | X u ω = k} ∩ {ω | X s ω = j} := by
      ext ω; simp only [Set.mem_inter_iff]; tauto
    rw [e]
    field_simp at key ⊢
    nlinarith [key]
