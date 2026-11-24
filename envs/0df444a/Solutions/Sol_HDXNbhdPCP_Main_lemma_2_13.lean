-- Prove2me | solution 1 for HDXNbhdPCP.Main.lemma_2_13
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T19:46:41.97082+00:00
-- url     : https://prove2.me/submissions/45511f8b-1128-48b9-a0c8-dbf8fc6f3e25

import Mathlib
import Definitions.Def_HDXNbhdPCP_Main_Complex

namespace HDXNbhdPCP.Main
open Classical
noncomputable section

namespace FinDist
variable {α β : Type}

theorem expect_map (D : FinDist α) (g : α → β) (h : β → ℝ) :
    (D.map g).expect h = D.expect (fun a => h (g a)) := by
  unfold expect map
  simp only
  rw [← Finset.sum_fiberwise_of_maps_to (s := D.supp) (t := D.supp.image g) (g := g)
    (fun a ha => Finset.mem_image_of_mem g ha)]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [(Finset.mem_filter.1 ha).2]

theorem prob_eq (D : FinDist α) (E : α → Prop) :
    D.prob E = D.expect (fun x => if E x then 1 else 0) := by
  unfold prob expect
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  by_cases hE : E a <;> simp [hE]

theorem expect_cond (D : FinDist α) (E : α → Prop) (h : α → ℝ) :
    (D.cond E).expect h = D.expect (fun x => if E x then h x else 0) / D.prob E := by
  unfold expect cond
  simp only
  rw [Finset.sum_div, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  split_ifs <;> simp [div_mul_eq_mul_div]

theorem expect_add (D : FinDist α) (f g : α → ℝ) :
    D.expect (fun a => f a + g a) = D.expect f + D.expect g := by
  unfold expect; rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun a _ => by ring)

theorem expect_sub (D : FinDist α) (f g : α → ℝ) :
    D.expect (fun a => f a - g a) = D.expect f - D.expect g := by
  unfold expect; rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun a _ => by ring)

theorem expect_mul (D : FinDist α) (c : ℝ) (f : α → ℝ) :
    D.expect (fun a => c * f a) = c * D.expect f := by
  unfold expect; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun a _ => by ring)

theorem expect_const (D : FinDist α) (c : ℝ) :
    D.expect (fun _ => c) = c * D.expect (fun _ => 1) := by
  rw [← expect_mul]; simp

theorem expect_zero (D : FinDist α) : D.expect (fun _ => (0:ℝ)) = 0 := by
  simp [expect]

theorem expect_congr (D : FinDist α) {f g : α → ℝ} (h : ∀ a ∈ D.supp, f a = g a) :
    D.expect f = D.expect g := by
  unfold expect
  exact Finset.sum_congr rfl (fun a ha => by rw [h a ha])

/-- weights nonnegative on the support -/
def Nonneg (D : FinDist α) : Prop := ∀ a ∈ D.supp, 0 ≤ D.w a

theorem expect_mono {D : FinDist α} (hD : D.Nonneg) {f g : α → ℝ}
    (h : ∀ a ∈ D.supp, f a ≤ g a) : D.expect f ≤ D.expect g := by
  unfold expect
  exact Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (h a ha) (hD a ha))

theorem expect_nonneg {D : FinDist α} (hD : D.Nonneg) {f : α → ℝ}
    (h : ∀ a, 0 ≤ f a) : 0 ≤ D.expect f := by
  have := expect_mono hD (f := fun _ => 0) (g := f) (fun a _ => h a)
  simpa [expect_zero] using this

theorem expect_eq_sum_wt (D : FinDist α) (s : Finset α) (hs : D.supp ⊆ s) (h : α → ℝ) :
    D.expect h = ∑ a ∈ s, D.wt a * h a := by
  unfold expect
  rw [← Finset.sum_subset hs (f := fun a => D.wt a * h a) ?_]
  · exact Finset.sum_congr rfl (fun a ha => by simp [wt, ha])
  · intro a _ ha; simp [wt, ha]

theorem expect_mixUniform {ι : Type} (s : Finset ι) (Ds : ι → FinDist α) (h : α → ℝ) :
    (mixUniform s Ds).expect h = (1 / (s.card : ℝ)) * ∑ i ∈ s, (Ds i).expect h := by
  have h1 : ∀ i ∈ s, (Ds i).expect h =
      ∑ a ∈ s.biUnion (fun i => (Ds i).supp), (Ds i).wt a * h a := fun i hi =>
    expect_eq_sum_wt _ _ (Finset.subset_biUnion_of_mem (fun i => (Ds i).supp) hi) h
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.mul_sum]
  unfold expect mixUniform
  simp only
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => by ring)

end FinDist

namespace ColoredComplex
variable {I : Type} {V : I → Type}

theorem merge_expect (K : ColoredComplex I V) (a b : I)
    (h : ((m : MColor I a b) → MV V a b m) → ℝ) :
    (K.merge a b).expect h = 1 / 2 * (K.expect (fun x => h (mergeFacet a b x true)) +
      K.expect (fun x => h (mergeFacet a b x false))) := by
  unfold merge
  rw [FinDist.expect_mixUniform]
  simp [FinDist.expect_map]

end ColoredComplex

namespace FinDist
variable {α : Type}
theorem expect_sq_decomp (D : FinDist α) (hm : D.expect (fun _ => (1:ℝ)) = 1) (k : α → ℝ) :
    D.expect (fun a => k a ^ 2) = D.expect (fun a => (k a - D.expect k) ^ 2) + D.expect k ^ 2 := by
  have h1 : (fun a => (k a - D.expect k) ^ 2) =
      fun a => (k a ^ 2 - 2 * D.expect k * k a) + D.expect k ^ 2 := by funext a; ring
  rw [h1, expect_add, expect_sub, expect_mul, expect_const, hm]
  ring
end FinDist

namespace BipGraph
variable {L R : Type}

theorem left_expect (G : BipGraph L R) (f : L → ℝ) :
    G.left.expect f = G.expect (fun e => f e.1) := FinDist.expect_map G Prod.fst f

theorem right_expect (G : BipGraph L R) (f : R → ℝ) :
    G.right.expect f = G.expect (fun e => f e.2) := FinDist.expect_map G Prod.snd f

theorem right_w (G : BipGraph L R) (r : R) :
    G.right.w r = G.expect (fun e => if e.2 = r then 1 else 0) := by
  unfold right FinDist.map FinDist.expect
  simp only
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  by_cases h : e.2 = r <;> simp [h]

theorem right_wt (G : BipGraph L R) (r : R) :
    G.right.wt r = G.expect (fun e => if e.2 = r then 1 else 0) := by
  by_cases hr : r ∈ G.right.supp
  · simp [FinDist.wt, hr, right_w]
  · have h0 : G.right.wt r = 0 := by simp [FinDist.wt, hr]
    rw [h0]
    unfold FinDist.expect
    symm
    apply Finset.sum_eq_zero
    intro e he
    have : e.2 ≠ r := fun h' => hr (by
      unfold right FinDist.map; simp only [Finset.mem_image]; exact ⟨e, he, h'⟩)
    simp [this]

theorem avg_eq (G : BipGraph L R) (f : L → ℝ) (r : R) :
    G.avg f r = G.expect (fun e => if e.2 = r then f e.1 else 0) /
      G.expect (fun e => if e.2 = r then 1 else 0) := by
  unfold avg
  rw [right_w]
  congr 1
  unfold FinDist.expect
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  by_cases h : e.2 = r <;> simp [h]

theorem expander_congr {G G' : BipGraph L R} (h : ∀ k, G.expect k = G'.expect k) {lam : ℝ}
    (H : G.IsExpander lam) : G'.IsExpander lam := by
  intro f hf
  have := H f
  simp only [left_expect, right_expect, avg_eq] at this hf ⊢
  simp only [h] at this
  exact this hf

theorem avg_sub_const (D : BipGraph L R) (f : L → ℝ) (c : ℝ) (r : R)
    (hρ : D.expect (fun e => if e.2 = r then (1:ℝ) else 0) ≠ 0) :
    D.avg (fun u => f u - c) r = D.avg f r - c := by
  rw [avg_eq, avg_eq]
  have : (fun e : L × R => if e.2 = r then f e.1 - c else 0) =
      fun e => (if e.2 = r then f e.1 else 0) - c * (if e.2 = r then (1:ℝ) else 0) := by
    funext e; split_ifs <;> simp
  rw [this, FinDist.expect_sub, FinDist.expect_mul]
  field_simp

theorem expander_iff_sq (G : BipGraph L R) {ε : ℝ} (hε : 0 ≤ ε)
    (hY : ∀ f : L → ℝ, 0 ≤ G.expect (fun e => f e.1 ^ 2)) :
    G.IsExpander ε ↔ ∀ f : L → ℝ, G.expect (fun e => f e.1) = 0 →
      G.expect (fun e => (G.avg f e.2) ^ 2) ≤ ε ^ 2 * G.expect (fun e => f e.1 ^ 2) := by
  unfold IsExpander
  simp only [left_expect, right_expect]
  constructor
  · intro H f hf
    have := (Real.sqrt_le_iff.1 (H f hf)).2
    rwa [mul_pow, Real.sq_sqrt (hY f)] at this
  · intro H f hf
    rw [Real.sqrt_le_iff]
    refine ⟨mul_nonneg hε (Real.sqrt_nonneg _), ?_⟩
    rw [mul_pow, Real.sq_sqrt (hY f)]
    exact H f hf

theorem expect_snd_eq {A B R : Type} (Ga : BipGraph A R) (Gb : BipGraph B R)
    (hρ : ∀ r, Ga.expect (fun e => if e.2 = r then (1:ℝ) else 0) =
      Gb.expect (fun e => if e.2 = r then (1:ℝ) else 0)) (k : R → ℝ) :
    Ga.expect (fun e => k e.2) = Gb.expect (fun e => k e.2) := by
  rw [← right_expect Ga k, ← right_expect Gb k]
  rw [FinDist.expect_eq_sum_wt Ga.right (Ga.right.supp ∪ Gb.right.supp) Finset.subset_union_left,
    FinDist.expect_eq_sum_wt Gb.right (Ga.right.supp ∪ Gb.right.supp) Finset.subset_union_right]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [right_wt, right_wt, hρ r]

theorem mix_left {A B R : Type} (G : BipGraph (A ⊕ B) R) (Ga : BipGraph A R) (Gb : BipGraph B R)
    {ε : ℝ} (hε : 0 ≤ ε) (hnA : Ga.Nonneg) (hnB : Gb.Nonneg)
    (hmA : Ga.expect (fun _ => (1:ℝ)) = 1) (hmB : Gb.expect (fun _ => (1:ℝ)) = 1)
    (hE : ∀ h : (A ⊕ B) × R → ℝ, G.expect h = 1 / 2 *
      (Ga.expect (fun e => h (Sum.inl e.1, e.2)) + Gb.expect (fun e => h (Sum.inr e.1, e.2))))
    (hρ : ∀ r, Ga.expect (fun e => if e.2 = r then (1:ℝ) else 0) =
      Gb.expect (fun e => if e.2 = r then (1:ℝ) else 0))
    (hA : Ga.IsExpander ε) (hB : Gb.IsExpander ε) : G.IsExpander ε := by
  have hYA : ∀ f : A → ℝ, 0 ≤ Ga.expect (fun e => f e.1 ^ 2) :=
    fun f => FinDist.expect_nonneg hnA (fun e => sq_nonneg _)
  have hYB : ∀ f : B → ℝ, 0 ≤ Gb.expect (fun e => f e.1 ^ 2) :=
    fun f => FinDist.expect_nonneg hnB (fun e => sq_nonneg _)
  have hYG : ∀ f : A ⊕ B → ℝ, 0 ≤ G.expect (fun e => f e.1 ^ 2) := by
    intro f
    have h1 := hE (fun e => f e.1 ^ 2)
    simp only at h1
    rw [h1]
    have := hYA (fun u => f (Sum.inl u))
    have := hYB (fun u => f (Sum.inr u))
    linarith
  rw [expander_iff_sq G hε hYG]
  have sqA := (expander_iff_sq Ga hε hYA).1 hA
  have sqB := (expander_iff_sq Gb hε hYB).1 hB
  intro f hf
  have hf_eq : f = Sum.elim (fun u => f (Sum.inl u)) (fun v => f (Sum.inr v)) := by
    funext x; cases x <;> rfl
  generalize (fun u => f (Sum.inl u)) = fa at hf_eq
  generalize (fun u => f (Sum.inr u)) = fb at hf_eq
  subst hf_eq
  have hsum0 := hE (fun e => Sum.elim fa fb e.1)
  simp only [Sum.elim_inl, Sum.elim_inr] at hsum0
  rw [hf] at hsum0
  obtain ⟨ma, hma⟩ : ∃ m, Ga.expect (fun e => fa e.1) = m := ⟨_, rfl⟩
  obtain ⟨mb, hmb⟩ : ∃ m, Gb.expect (fun e => fb e.1) = m := ⟨_, rfl⟩
  have hsum : ma + mb = 0 := by rw [hma, hmb] at hsum0; linarith
  have havg : ∀ r, G.avg (Sum.elim fa fb) r = 1 / 2 * (Ga.avg fa r + Gb.avg fb r) := by
    intro r
    simp only [avg_eq]
    have hN := hE (fun e => if e.2 = r then Sum.elim fa fb e.1 else 0)
    have hD := hE (fun e => if e.2 = r then (1:ℝ) else 0)
    simp only [Sum.elim_inl, Sum.elim_inr] at hN hD
    rw [hN, hD, ← hρ r]
    by_cases h0 : Ga.expect (fun e => if e.2 = r then (1:ℝ) else 0) = 0
    · simp [h0]
    · field_simp
      ring
  have hgm : Ga.expect (fun e => fa e.1 - ma) = 0 := by
    have := FinDist.expect_sub Ga (fun e => fa e.1) (fun _ => ma)
    rw [this, hma, FinDist.expect_const, hmA]; ring
  have hgm' : Gb.expect (fun e => fb e.1 - mb) = 0 := by
    have := FinDist.expect_sub Gb (fun e => fb e.1) (fun _ => mb)
    rw [this, hmb, FinDist.expect_const, hmB]; ring
  have sqA' := sqA (fun u => fa u - ma) hgm
  have sqB' := sqB (fun u => fb u - mb) hgm'
  have hx : ∀ r, G.avg (Sum.elim fa fb) r =
      1 / 2 * (Ga.avg (fun u => fa u - ma) r + Gb.avg (fun v => fb v - mb) r) := by
    intro r
    rw [havg]
    by_cases h0 : Ga.expect (fun e => if e.2 = r then (1:ℝ) else 0) = 0
    · have h0' : Gb.expect (fun e => if e.2 = r then (1:ℝ) else 0) = 0 := by rw [← hρ r]; exact h0
      simp only [avg_eq, h0, h0', div_zero]
    · rw [avg_sub_const Ga fa ma r h0, avg_sub_const Gb fb mb r (by rwa [← hρ r])]
      linarith
  have hsnd := expect_snd_eq Ga Gb hρ
  have hptw : ∀ r, (G.avg (Sum.elim fa fb) r) ^ 2 ≤ 1 / 2 * ((Ga.avg (fun u => fa u - ma) r) ^ 2 +
      (Gb.avg (fun v => fb v - mb) r) ^ 2) := by
    intro r
    rw [hx r]
    nlinarith [sq_nonneg (Ga.avg (fun u => fa u - ma) r - Gb.avg (fun v => fb v - mb) r)]
  have hXG := hE (fun e => (G.avg (Sum.elim fa fb) e.2) ^ 2)
  simp only at hXG
  have hA1 : Ga.expect (fun e => (G.avg (Sum.elim fa fb) e.2) ^ 2) ≤
      1 / 2 * (Ga.expect (fun e => (Ga.avg (fun u => fa u - ma) e.2) ^ 2) +
        Ga.expect (fun e => (Gb.avg (fun v => fb v - mb) e.2) ^ 2)) := by
    have := FinDist.expect_mono hnA (f := fun e => (G.avg (Sum.elim fa fb) e.2) ^ 2)
      (g := fun e => 1 / 2 * ((Ga.avg (fun u => fa u - ma) e.2) ^ 2 +
        (Gb.avg (fun v => fb v - mb) e.2) ^ 2)) (fun e _ => hptw e.2)
    rw [FinDist.expect_mul, FinDist.expect_add] at this
    exact this
  have hB1 : Gb.expect (fun e => (G.avg (Sum.elim fa fb) e.2) ^ 2) ≤
      1 / 2 * (Ga.expect (fun e => (Ga.avg (fun u => fa u - ma) e.2) ^ 2) +
        Gb.expect (fun e => (Gb.avg (fun v => fb v - mb) e.2) ^ 2)) := by
    have := FinDist.expect_mono hnB (f := fun e => (G.avg (Sum.elim fa fb) e.2) ^ 2)
      (g := fun e => 1 / 2 * ((Ga.avg (fun u => fa u - ma) e.2) ^ 2 +
        (Gb.avg (fun v => fb v - mb) e.2) ^ 2)) (fun e _ => hptw e.2)
    rw [FinDist.expect_mul, FinDist.expect_add] at this
    have hu : Gb.expect (fun e => (Ga.avg (fun u => fa u - ma) e.2) ^ 2) =
        Ga.expect (fun e => (Ga.avg (fun u => fa u - ma) e.2) ^ 2) :=
      (hsnd (fun r => (Ga.avg (fun u => fa u - ma) r) ^ 2)).symm
    rw [hu] at this
    exact this
  have hYa := FinDist.expect_sq_decomp Ga hmA (fun e => fa e.1)
  have hYb := FinDist.expect_sq_decomp Gb hmB (fun e => fb e.1)
  rw [hma] at hYa
  rw [hmb] at hYb
  have hYG' := hE (fun e => (Sum.elim fa fb e.1) ^ 2)
  simp only [Sum.elim_inl, Sum.elim_inr] at hYG'
  rw [hXG, hYG', hYa, hYb]
  have hbb : Ga.expect (fun e => (Gb.avg (fun v => fb v - mb) e.2) ^ 2) =
      Gb.expect (fun e => (Gb.avg (fun v => fb v - mb) e.2) ^ 2) :=
    hsnd (fun r => (Gb.avg (fun v => fb v - mb) r) ^ 2)
  rw [hbb] at hA1
  nlinarith [mul_nonneg (sq_nonneg ε) (sq_nonneg ma), mul_nonneg (sq_nonneg ε) (sq_nonneg mb)]

theorem mix_right {A B R : Type} (G : BipGraph R (A ⊕ B)) (Ga : BipGraph R A) (Gb : BipGraph R B)
    {ε : ℝ} (hε : 0 ≤ ε) (hnA : Ga.Nonneg) (hnB : Gb.Nonneg)
    (hE : ∀ h : R × (A ⊕ B) → ℝ, G.expect h = 1 / 2 *
      (Ga.expect (fun e => h (e.1, Sum.inl e.2)) + Gb.expect (fun e => h (e.1, Sum.inr e.2))))
    (hL : ∀ k : R → ℝ, Ga.expect (fun e => k e.1) = Gb.expect (fun e => k e.1))
    (hA : Ga.IsExpander ε) (hB : Gb.IsExpander ε) : G.IsExpander ε := by
  have hYA : ∀ f : R → ℝ, 0 ≤ Ga.expect (fun e => f e.1 ^ 2) :=
    fun f => FinDist.expect_nonneg hnA (fun e => sq_nonneg _)
  have hYB : ∀ f : R → ℝ, 0 ≤ Gb.expect (fun e => f e.1 ^ 2) :=
    fun f => FinDist.expect_nonneg hnB (fun e => sq_nonneg _)
  have hYG' : ∀ f : R → ℝ, G.expect (fun e => f e.1 ^ 2) = Ga.expect (fun e => f e.1 ^ 2) := by
    intro f
    have h1 := hE (fun e => f e.1 ^ 2)
    simp only at h1
    rw [h1, ← hL (fun r => f r ^ 2)]; ring
  have hYG : ∀ f : R → ℝ, 0 ≤ G.expect (fun e => f e.1 ^ 2) := by
    intro f; rw [hYG' f]; exact hYA f
  rw [expander_iff_sq G hε hYG]
  have sqA := (expander_iff_sq Ga hε hYA).1 hA
  have sqB := (expander_iff_sq Gb hε hYB).1 hB
  intro f hf
  have hf1 : Ga.expect (fun e => f e.1) = 0 := by
    have := hE (fun e => f e.1)
    simp only at this
    rw [hf, ← hL f] at this
    linarith
  have hf2 : Gb.expect (fun e => f e.1) = 0 := by rw [← hL f]; exact hf1
  have sqA' := sqA f hf1
  have sqB' := sqB f hf2
  have havl : ∀ u : A, G.avg f (Sum.inl u) = Ga.avg f u := by
    intro u
    simp only [avg_eq]
    have hN : G.expect (fun e => @ite ℝ (e.2 = Sum.inl u) (Classical.propDecidable _) (f e.1) 0) =
        1 / 2 * Ga.expect (fun e => if e.2 = u then f e.1 else 0) := by
      rw [hE]; simp [FinDist.expect_zero]
    have hD : G.expect (fun e => @ite ℝ (e.2 = Sum.inl u) (Classical.propDecidable _) ((1:ℝ)) 0) =
        1 / 2 * Ga.expect (fun e => if e.2 = u then (1:ℝ) else 0) := by
      rw [hE]; simp [FinDist.expect_zero]
    rw [hN, hD]
    by_cases h0 : Ga.expect (fun e => if e.2 = u then (1:ℝ) else 0) = 0
    · simp [h0]
    · field_simp
  have havr : ∀ v : B, G.avg f (Sum.inr v) = Gb.avg f v := by
    intro v
    simp only [avg_eq]
    have hN : G.expect (fun e => @ite ℝ (e.2 = Sum.inr v) (Classical.propDecidable _) (f e.1) 0) =
        1 / 2 * Gb.expect (fun e => if e.2 = v then f e.1 else 0) := by
      rw [hE]; simp [FinDist.expect_zero]
    have hD : G.expect (fun e => @ite ℝ (e.2 = Sum.inr v) (Classical.propDecidable _) ((1:ℝ)) 0) =
        1 / 2 * Gb.expect (fun e => if e.2 = v then (1:ℝ) else 0) := by
      rw [hE]; simp [FinDist.expect_zero]
    rw [hN, hD]
    by_cases h0 : Gb.expect (fun e => if e.2 = v then (1:ℝ) else 0) = 0
    · simp [h0]
    · field_simp
  have hX := hE (fun e => (G.avg f e.2) ^ 2)
  simp only [havl, havr] at hX
  have hLf : Ga.expect (fun e => f e.1 ^ 2) = Gb.expect (fun e => f e.1 ^ 2) :=
    hL (fun r => f r ^ 2)
  rw [hX, hYG' f]
  nlinarith [sq_nonneg ε]

end BipGraph

namespace ColoredComplex
variable {I : Type} {V : I → Type}

theorem pg_expect (K : ColoredComplex I V) (E : ((i : I) → V i) → Prop) (i j : I)
    (h : V i × V j → ℝ) :
    (pairGraph (K.cond E) i j).expect h =
      K.expect (fun x => if E x then h (x i, x j) else 0) / K.prob E := by
  unfold pairGraph
  rw [FinDist.expect_map, FinDist.expect_cond]

theorem merge_pg_expect (K : ColoredComplex I V) (a b : I)
    (E : ((m : MColor I a b) → MV V a b m) → Prop) (i j : MColor I a b)
    (h : MV V a b i × MV V a b j → ℝ) :
    (pairGraph ((K.merge a b).cond E) i j).expect h =
      (K.expect (fun x => if E (mergeFacet a b x true)
          then h (mergeFacet a b x true i, mergeFacet a b x true j) else 0) +
        K.expect (fun x => if E (mergeFacet a b x false)
          then h (mergeFacet a b x false i, mergeFacet a b x false j) else 0)) /
      (K.expect (fun x => if E (mergeFacet a b x true) then 1 else 0) +
        K.expect (fun x => if E (mergeFacet a b x false) then 1 else 0)) := by
  rw [pg_expect, FinDist.prob_eq, merge_expect K a b, merge_expect K a b]
  rw [mul_div_mul_left _ _ (by norm_num : (1 / 2 : ℝ) ≠ 0)]

theorem prob_pos_of (K : ColoredComplex I V) (hK : FinDist.IsProb K) (E : ((i : I) → V i) → Prop)
    (x₀ : (i : I) → V i) (hx : x₀ ∈ K.supp) (hE : E x₀) : 0 < K.prob E := by
  unfold FinDist.prob
  apply Finset.sum_pos'
  · intro x hx'; exact (hK.1 x (Finset.mem_filter.1 hx').1).le
  · exact ⟨x₀, Finset.mem_filter.2 ⟨hx, hE⟩, hK.1 x₀ hx⟩

theorem pg_nonneg (K : ColoredComplex I V) (hK : FinDist.IsProb K)
    (E : ((i : I) → V i) → Prop) (i j : I) : (pairGraph (K.cond E) i j).Nonneg := by
  intro e he
  unfold pairGraph FinDist.map FinDist.cond
  simp only
  apply Finset.sum_nonneg
  intro x hx
  have hp : 0 ≤ K.prob E := by
    unfold FinDist.prob
    exact Finset.sum_nonneg (fun x hx' => (hK.1 x (Finset.mem_filter.1 hx').1).le)
  have hx2 := (Finset.mem_filter.1 hx).1
  exact div_nonneg (hK.1 x (Finset.mem_filter.1 hx2).1).le hp

theorem pg_mass (K : ColoredComplex I V) (hK : FinDist.IsProb K) (E : ((i : I) → V i) → Prop)
    (x₀ : (i : I) → V i) (hx : x₀ ∈ K.supp) (hE : E x₀) (i j : I) :
    (pairGraph (K.cond E) i j).expect (fun _ => (1:ℝ)) = 1 := by
  rw [pg_expect]
  have hp := prob_pos_of K hK E x₀ hx hE
  rw [FinDist.prob_eq] at hp ⊢
  exact div_self hp.ne'

theorem mergeFacet_none_iff (a b : I) (x x₀ : (i : I) → V i) (coin c : Bool) :
    mergeFacet a b x coin none = mergeFacet a b x₀ c none ↔
      coin = c ∧ x (if c then a else b) = x₀ (if c then a else b) := by
  cases coin <;> cases c <;> simp [mergeFacet] <;>
    first
    | exact ⟨fun h => Sum.inl.inj h, fun h => by rw [h]⟩
    | exact ⟨fun h => Sum.inr.inj h, fun h => by rw [h]⟩

theorem merge_isProduct (K : ColoredComplex I V) [Fintype I]
    (hK : FinDist.IsProb K) (ε : ℝ) (hε₀ : 0 ≤ ε) (hprod : K.IsProduct ε)
    (a b : I) : (K.merge a b).IsProduct ε := by
  intro J y hy i j hi hj hij
  have hy' : ∃ x₀ ∈ K.supp, ∃ c : Bool, mergeFacet a b x₀ c = y := by
    unfold merge FinDist.mixUniform at hy
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, FinDist.map,
      Finset.mem_image] at hy
    obtain ⟨c, x₀, hx₀, h⟩ := hy
    exact ⟨x₀, hx₀, c, h⟩
  obtain ⟨x₀, hx₀, c, rfl⟩ := hy'
  obtain ⟨JR, hJR⟩ : ∃ JR : Finset I, ∀ k, k ∈ JR ↔
      ∃ h : k ≠ a ∧ k ≠ b, (some ⟨k, h⟩ : MColor I a b) ∈ J :=
    ⟨Finset.univ.filter (fun k => ∃ h : k ≠ a ∧ k ≠ b, (some ⟨k, h⟩ : MColor I a b) ∈ J),
      fun k => by simp⟩
  have hcond : (K.merge a b).condFace J (mergeFacet a b x₀ c) =
      FinDist.cond (K.merge a b) (fun z => ∀ m ∈ J, z m = mergeFacet a b x₀ c m) := rfl
  rw [hcond]
  by_cases hnone : (none : MColor I a b) ∈ J
  · -- the new colour is in the face
    cases i with
    | none => exact absurd hnone hi
    | some i' =>
    cases j with
    | none => exact absurd hnone hj
    | some j' =>
    have hT : ∀ (x : (i : I) → V i) (coin : Bool),
        (∀ m ∈ J, mergeFacet a b x coin m = mergeFacet a b x₀ c m) ↔
          (coin = c ∧ ∀ k ∈ insert (if c then a else b) JR, x k = x₀ k) := by
      intro x coin
      constructor
      · intro H
        have h1 := (mergeFacet_none_iff a b x x₀ coin c).1 (H none hnone)
        refine ⟨h1.1, ?_⟩
        intro k hk
        rcases Finset.mem_insert.1 hk with rfl | hk
        · exact h1.2
        · obtain ⟨hh, hm⟩ := (hJR k).1 hk
          exact H _ hm
      · rintro ⟨rfl, H⟩ m hm
        cases m with
        | none =>
          exact (mergeFacet_none_iff a b x x₀ coin coin).2 ⟨rfl, H _ (Finset.mem_insert_self _ _)⟩
        | some m' =>
          exact H m'.1 (Finset.mem_insert_of_mem ((hJR m'.1).2 ⟨m'.2, hm⟩))
    have hi' : i'.1 ∉ insert (if c then a else b) JR := by
      intro h
      rcases Finset.mem_insert.1 h with h | h
      · split_ifs at h
        · exact i'.2.1 h
        · exact i'.2.2 h
      · obtain ⟨hh, hm⟩ := (hJR _).1 h
        exact hi hm
    have hj' : j'.1 ∉ insert (if c then a else b) JR := by
      intro h
      rcases Finset.mem_insert.1 h with h | h
      · split_ifs at h
        · exact j'.2.1 h
        · exact j'.2.2 h
      · obtain ⟨hh, hm⟩ := (hJR _).1 h
        exact hj hm
    have hne : i'.1 ≠ j'.1 := fun h => hij (by rw [Subtype.ext h])
    have hex := hprod (insert (if c then a else b) JR) x₀ hx₀ i'.1 j'.1 hi' hj' hne
    refine BipGraph.expander_congr (G := pairGraph (K.cond (fun x => ∀ k ∈ insert (if c then a else b) JR,
      x k = x₀ k)) i'.1 j'.1) ?_ hex
    intro h
    refine Eq.trans ?_ (merge_pg_expect K a b _ (some i') (some j') h).symm
    rw [pg_expect, FinDist.prob_eq]
    simp only [hT]
    cases c <;> simp [mergeFacet, FinDist.expect_zero] <;> congr 1 <;> congr 1 <;> funext x <;> congr
  · have hT : ∀ (x : (i : I) → V i) (coin : Bool),
        (∀ m ∈ J, mergeFacet a b x coin m = mergeFacet a b x₀ c m) ↔ ∀ k ∈ JR, x k = x₀ k := by
      intro x coin
      constructor
      · intro H k hk
        obtain ⟨hh, hm⟩ := (hJR k).1 hk
        exact H _ hm
      · intro H m hm
        cases m with
        | none => exact absurd hm hnone
        | some m' => exact H m'.1 ((hJR m'.1).2 ⟨m'.2, hm⟩)
    have hJa : a ∉ JR := fun h => by obtain ⟨hh, _⟩ := (hJR a).1 h; exact hh.1 rfl
    have hJb : b ∉ JR := fun h => by obtain ⟨hh, _⟩ := (hJR b).1 h; exact hh.2 rfl
    have hJ' : ∀ m' : {i // i ≠ a ∧ i ≠ b}, some m' ∉ J → m'.1 ∉ JR :=
      fun m' hm h => by obtain ⟨hh, hm'⟩ := (hJR _).1 h; exact hm hm'
    have hmixeq : ∀ A B P P₂ A' B' P' : ℝ, A = A' → B = B' → P = P' → P₂ = P' →
        (A + B) / (P + P₂) = 1 / 2 * (A' / P' + B' / P') := by
      intro A B P P₂ A' B' P' h1 h2 h3 h4; subst h1 h2 h3 h4; ring
    have hdupeq : ∀ A A₂ P P₂ A' P' : ℝ, A = A' → A₂ = A' → P = P' → P₂ = P' →
        (A + A₂) / (P + P₂) = A' / P' := by
      intro A A₂ P P₂ A' P' h1 h2 h3 h4; subst h1 h2 h3 h4; rw [← two_mul, ← two_mul, mul_div_mul_left _ _ two_ne_zero]
    have hx0 : (fun x : (i : I) → V i => ∀ k ∈ JR, x k = x₀ k) x₀ := fun k _ => rfl
    cases i with
    | none =>
      cases j with
      | none => exact absurd rfl hij
      | some j' =>
        have hA := hprod JR x₀ hx₀ a j'.1 hJa (hJ' j' hj) (fun h => j'.2.1 h.symm)
        have hB := hprod JR x₀ hx₀ b j'.1 hJb (hJ' j' hj) (fun h => j'.2.2 h.symm)
        refine BipGraph.mix_left _ (pairGraph (K.cond (fun x => ∀ k ∈ JR, x k = x₀ k)) a j'.1)
          (pairGraph (K.cond (fun x => ∀ k ∈ JR, x k = x₀ k)) b j'.1) hε₀
          (pg_nonneg K hK _ _ _) (pg_nonneg K hK _ _ _)
          (pg_mass K hK _ x₀ hx₀ hx0 _ _) (pg_mass K hK _ x₀ hx₀ hx0 _ _) ?_ ?_ hA hB
        · intro h
          refine (merge_pg_expect K a b _ none (some j') h).trans ?_
          rw [pg_expect, pg_expect]
          simp only [FinDist.prob_eq, hT]
          simp only [mergeFacet, if_true, if_false, Bool.false_eq_true]
          refine hmixeq _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ <;> first | rfl | (congr 1; funext x; congr)
        · intro r
          rw [pg_expect, pg_expect]
    | some i' =>
      cases j with
      | none =>
        have hA := hprod JR x₀ hx₀ i'.1 a (hJ' i' hi) hJa (fun h => i'.2.1 h)
        have hB := hprod JR x₀ hx₀ i'.1 b (hJ' i' hi) hJb (fun h => i'.2.2 h)
        refine BipGraph.mix_right _ (pairGraph (K.cond (fun x => ∀ k ∈ JR, x k = x₀ k)) i'.1 a)
          (pairGraph (K.cond (fun x => ∀ k ∈ JR, x k = x₀ k)) i'.1 b) hε₀
          (pg_nonneg K hK _ _ _) (pg_nonneg K hK _ _ _) ?_ ?_ hA hB
        · intro h
          refine (merge_pg_expect K a b _ (some i') none h).trans ?_
          rw [pg_expect, pg_expect]
          simp only [FinDist.prob_eq, hT]
          simp only [mergeFacet, if_true, if_false, Bool.false_eq_true]
          refine hmixeq _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ <;> first | rfl | (congr 1; funext x; congr)
        · intro k
          rw [pg_expect, pg_expect]
      | some j' =>
        have hne : i'.1 ≠ j'.1 := fun h => hij (by rw [Subtype.ext h])
        have hex := hprod JR x₀ hx₀ i'.1 j'.1 (hJ' i' hi) (hJ' j' hj) hne
        refine BipGraph.expander_congr (G := pairGraph (K.cond (fun x => ∀ k ∈ JR,
          x k = x₀ k)) i'.1 j'.1) ?_ hex
        intro h
        refine Eq.trans ?_ (merge_pg_expect K a b _ (some i') (some j') h).symm
        rw [pg_expect, FinDist.prob_eq]
        simp only [hT]
        simp only [mergeFacet]
        refine (hdupeq _ _ _ _ _ _ ?_ ?_ ?_ ?_).symm <;> first | rfl | (congr 1; funext x; congr)

end ColoredComplex
end
end HDXNbhdPCP.Main

theorem solution {I : Type} [Fintype I] {V : I → Type}
    (K : HDXNbhdPCP.Main.ColoredComplex I V)
    (hK : HDXNbhdPCP.Main.FinDist.IsProb K) (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (hprod : K.IsProduct ε) (a b : I) (hab : a ≠ b) : (K.merge a b).IsProduct ε :=
  HDXNbhdPCP.Main.ColoredComplex.merge_isProduct K hK ε hε₀ hprod a b
