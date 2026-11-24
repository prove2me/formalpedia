-- Prove2me | solution 1 for MulticlassDS.Compress.lemma29_expDim_le
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T01:14:00.453796+00:00
-- url     : https://prove2.me/submissions/58148b08-ad91-40ed-bfc3-d40b6d90c0c4

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Dimensions
import Definitions.Def_MulticlassDS_Compress_Shifting

open MulticlassDS.Compress

namespace L29Aux

open scoped Classical in
/-- Words on the first k coordinates extending in G by both labels a and b. -/
noncomputable def Gab {k p : ℕ} (G : Finset (Fin (k + 1) → Fin p)) (a b : Fin p) :
    Finset (Fin k → Fin p) :=
  Finset.univ.filter fun v =>
    (Fin.snoc v a : Fin (k + 1) → Fin p) ∈ G ∧ (Fin.snoc v b : Fin (k + 1) → Fin p) ∈ G

open scoped Classical in
/-- Labels extending v inside G. -/
noncomputable def fib {k p : ℕ} (G : Finset (Fin (k + 1) → Fin p)) (v : Fin k → Fin p) :
    Finset (Fin p) :=
  Finset.univ.filter fun y => (Fin.snoc v y : Fin (k + 1) → Fin p) ∈ G

def pairs (p : ℕ) : Finset (Fin p × Fin p) := Finset.univ.filter fun ab => ab.1 < ab.2

noncomputable def Phi {k p : ℕ} (G : Finset (Fin (k + 1) → Fin p)) (u : Fin (k + 1) → Fin p) :
    Option (Fin p × Fin p) × (Fin k → Fin p) :=
  if h : (fib G (Fin.init u)).Nonempty then
    (if u (Fin.last k) = (fib G (Fin.init u)).min' h then none
      else some ((fib G (Fin.init u)).min' h, u (Fin.last k)), Fin.init u)
  else (none, Fin.init u)

lemma Phi_snd {k p : ℕ} (G : Finset (Fin (k + 1) → Fin p)) (u : Fin (k + 1) → Fin p) :
    (Phi G u).2 = Fin.init u := by
  unfold Phi
  split_ifs <;> rfl

lemma fib_nonempty {k p : ℕ} (G : Finset (Fin (k + 1) → Fin p)) (u : Fin (k + 1) → Fin p)
    (hu : u ∈ G) : (fib G (Fin.init u)).Nonempty := by
  refine ⟨u (Fin.last k), ?_⟩
  unfold fib
  rw [Finset.mem_filter, Fin.snoc_init_self]
  exact ⟨Finset.mem_univ _, hu⟩

lemma Phi_fst {k p : ℕ} (G : Finset (Fin (k + 1) → Fin p)) (u : Fin (k + 1) → Fin p)
    (hu : u ∈ G) :
    ((Phi G u).1 = none → (fib G (Fin.init u)).min = ((u (Fin.last k) : Fin p) : WithTop (Fin p))) ∧
      ∀ ab, (Phi G u).1 = some ab → ab.2 = u (Fin.last k) := by
  have hne := fib_nonempty G u hu
  unfold Phi
  rw [dif_pos hne]
  by_cases hm : u (Fin.last k) = (fib G (Fin.init u)).min' hne
  · rw [if_pos hm]
    refine ⟨fun _ => ?_, fun ab h => ?_⟩
    · rw [← Finset.coe_min' hne, ← hm]
    · exact absurd h (by simp)
  · rw [if_neg hm]
    refine ⟨fun h => ?_, fun ab h => ?_⟩
    · exact absurd h (by simp)
    · have h' := Option.some.inj h
      rw [← h']

lemma two_pairs (p : ℕ) : 2 * (pairs p).card ≤ p ^ 2 := by
  have himg : ((pairs p).image Prod.swap).card = (pairs p).card :=
    Finset.card_image_of_injective _ Prod.swap_injective
  have hdisj : Disjoint (pairs p) ((pairs p).image Prod.swap) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx'
    have h1 : y.swap.1 < y.swap.2 := (Finset.mem_filter.mp hx).2
    have h2 : y.1 < y.2 := (Finset.mem_filter.mp hy).2
    exact lt_asymm h1 h2
  have hle : (pairs p ∪ (pairs p).image Prod.swap).card ≤
      (Finset.univ : Finset (Fin p × Fin p)).card := Finset.card_le_card (Finset.subset_univ _)
  rw [Finset.card_union_of_disjoint hdisj, himg, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin] at hle
  nlinarith

lemma count_step {k p : ℕ} (G : Finset (Fin (k + 1) → Fin p)) :
    G.card ≤ (G.image Fin.init).card + ∑ ab ∈ pairs p, (Gab G ab.1 ab.2).card := by
  classical
  let T : Finset (Option (Fin p × Fin p) × (Fin k → Fin p)) :=
    (G.image Fin.init).image (fun v => (none, v)) ∪
      (pairs p).biUnion (fun ab => (Gab G ab.1 ab.2).image (fun v => (some ab, v)))
  have hT : T.card ≤ (G.image Fin.init).card + ∑ ab ∈ pairs p, (Gab G ab.1 ab.2).card :=
    (Finset.card_union_le _ _).trans (add_le_add Finset.card_image_le
      (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_image_le)))
  refine le_trans (Finset.card_le_card_of_injOn (Phi G) ?_ ?_) hT
  · intro u hu
    have hu' : u ∈ G := hu
    have hne := fib_nonempty G u hu'
    show Phi G u ∈ T
    unfold Phi
    rw [dif_pos hne]
    by_cases hm : u (Fin.last k) = (fib G (Fin.init u)).min' hne
    · rw [if_pos hm]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨Fin.init u, Finset.mem_image_of_mem _ hu', rfl⟩)
    · rw [if_neg hm]
      have hmem := Finset.min'_mem _ hne
      have hmem' : (Fin.snoc (Fin.init u) ((fib G (Fin.init u)).min' hne) :
          Fin (k + 1) → Fin p) ∈ G := by
        unfold fib at hmem
        exact (Finset.mem_filter.mp hmem).2
      have hlast : u (Fin.last k) ∈ fib G (Fin.init u) := by
        unfold fib
        rw [Finset.mem_filter, Fin.snoc_init_self]
        exact ⟨Finset.mem_univ _, hu'⟩
      have hlt : (fib G (Fin.init u)).min' hne < u (Fin.last k) :=
        lt_of_le_of_ne (Finset.min'_le _ _ hlast) (Ne.symm hm)
      refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨((fib G (Fin.init u)).min' hne, u (Fin.last k)), ?_, Finset.mem_image.mpr
          ⟨Fin.init u, ?_, rfl⟩⟩)
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
      · unfold Gab
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem', ?_⟩
        show (Fin.snoc (Fin.init u) (u (Fin.last k)) : Fin (k + 1) → Fin p) ∈ G
        rw [Fin.snoc_init_self]
        exact hu'
  · intro u1 hu1 u2 hu2 h
    have hu1' : u1 ∈ G := hu1
    have hu2' : u2 ∈ G := hu2
    have hinit : Fin.init u1 = Fin.init u2 := by
      rw [← Phi_snd G u1, ← Phi_snd G u2, h]
    have h1 := Phi_fst G u1 hu1'
    have h2 := Phi_fst G u2 hu2'
    have hlast : u1 (Fin.last k) = u2 (Fin.last k) := by
      rcases ho : (Phi G u1).1 with _ | ab
      · have e1 := h1.1 ho
        have e2 := h2.1 (by rw [← h]; exact ho)
        rw [hinit] at e1
        exact WithTop.coe_injective (e1.symm.trans e2)
      · have e1 := h1.2 ab ho
        have e2 := h2.2 ab (by rw [← h]; exact ho)
        exact e1.symm.trans e2
    rw [← Fin.snoc_init_self u1, ← Fin.snoc_init_self u2, hinit, hlast]

lemma shatter_init {k p m : ℕ} (G : Finset (Fin (k + 1) → Fin p)) (S : Fin m → Fin k)
    (h : NShatters (↑(G.image Fin.init) : Set (Fin k → Fin p)) S) :
    NShatters (↑G : Set (Fin (k + 1) → Fin p)) (Fin.castSucc ∘ S) := by
  classical
  obtain ⟨f, g, hfg, hc⟩ := h
  refine ⟨f, g, hfg, fun c => ?_⟩
  obtain ⟨w, hw, e⟩ := hc c
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hw)
  exact ⟨u, Finset.mem_coe.mpr hu, e⟩

lemma shatter_snoc {k p m : ℕ} (G : Finset (Fin (k + 1) → Fin p)) (a b : Fin p) (hab : a ≠ b)
    (S : Fin m → Fin k) (h : NShatters (↑(Gab G a b) : Set (Fin k → Fin p)) S) :
    NShatters (↑G : Set (Fin (k + 1) → Fin p))
      (Fin.snoc (Fin.castSucc ∘ S) (Fin.last k) : Fin (m + 1) → Fin (k + 1)) := by
  obtain ⟨f, g, hfg, hc⟩ := h
  refine ⟨(Fin.snoc f a : Fin (m + 1) → Fin p), (Fin.snoc g b : Fin (m + 1) → Fin p), ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hab
    · simpa using hfg j
  · intro c
    obtain ⟨v, hv, e⟩ := hc (fun i => c i.castSucc)
    have hv' : (Fin.snoc v a : Fin (k + 1) → Fin p) ∈ G ∧
        (Fin.snoc v b : Fin (k + 1) → Fin p) ∈ G := by
      have := Finset.mem_coe.mp hv
      unfold Gab at this
      exact (Finset.mem_filter.mp this).2
    refine ⟨(Fin.snoc v (if c (Fin.last m) then a else b) : Fin (k + 1) → Fin p), ?_, ?_⟩
    · by_cases hcl : c (Fin.last m) = true
      · rw [if_pos hcl]
        exact Finset.mem_coe.mpr hv'.1
      · rw [if_neg hcl]
        exact Finset.mem_coe.mpr hv'.2
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · have ej := congrFun e j
        simp only [Function.comp_apply] at ej
        simp [ej]

lemma bound : ∀ (k : ℕ) {p : ℕ} (d : ℕ) (G : Finset (Fin k → Fin p)), 2 ≤ p →
    (∀ (m : ℕ) (S : Fin m → Fin k), NShatters (↑G : Set (Fin k → Fin p)) S → m ≤ d) →
    2 ^ k * G.card ≤ p ^ (2 * d) * 3 ^ k := by
  intro k
  induction k with
  | zero =>
    intro p d G hp _
    have h1 : G.card ≤ 1 := Finset.card_le_one_of_subsingleton G
    have h2 : 1 ≤ p ^ (2 * d) := Nat.one_le_pow _ _ (by omega)
    simpa using h1.trans h2
  | succ k ih =>
    intro p d G hp hd
    classical
    have hA : 2 ^ k * (G.image Fin.init).card ≤ p ^ (2 * d) * 3 ^ k :=
      ih d (G.image Fin.init) hp (fun m S hS => hd m _ (shatter_init G S hS))
    have hB : ∀ ab ∈ pairs p, 2 ^ k * (Gab G ab.1 ab.2).card * p ^ 2 ≤ p ^ (2 * d) * 3 ^ k := by
      intro ab hab
      have hne : ab.1 ≠ ab.2 := ne_of_lt (Finset.mem_filter.mp hab).2
      have hd' : ∀ (m : ℕ) (S : Fin m → Fin k),
          NShatters (↑(Gab G ab.1 ab.2) : Set (Fin k → Fin p)) S → m + 1 ≤ d :=
        fun m S hS => hd (m + 1) _ (shatter_snoc G ab.1 ab.2 hne S hS)
      rcases Finset.eq_empty_or_nonempty (Gab G ab.1 ab.2) with he | ⟨v, hv⟩
      · rw [he]
        simp
      · have h0 : NShatters (↑(Gab G ab.1 ab.2) : Set (Fin k → Fin p))
            (Fin.elim0 : Fin 0 → Fin k) :=
          ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun c =>
            ⟨v, Finset.mem_coe.mpr hv, funext fun i => i.elim0⟩⟩
        have hd1 : 1 ≤ d := hd' 0 _ h0
        obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
        have hih := ih d' (Gab G ab.1 ab.2) hp (fun m S hS => by have := hd' m S hS; omega)
        calc 2 ^ k * (Gab G ab.1 ab.2).card * p ^ 2
            ≤ p ^ (2 * d') * 3 ^ k * p ^ 2 := Nat.mul_le_mul_right _ hih
          _ = p ^ (2 * (d' + 1)) * 3 ^ k := by ring
    have hsum : 2 ^ k * (∑ ab ∈ pairs p, (Gab G ab.1 ab.2).card) * p ^ 2 ≤
        (pairs p).card * (p ^ (2 * d) * 3 ^ k) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      calc ∑ ab ∈ pairs p, 2 ^ k * (Gab G ab.1 ab.2).card * p ^ 2
          ≤ ∑ _ab ∈ pairs p, p ^ (2 * d) * 3 ^ k := Finset.sum_le_sum hB
        _ = (pairs p).card * (p ^ (2 * d) * 3 ^ k) := by
          rw [Finset.sum_const, smul_eq_mul]
    have hpairs := two_pairs p
    have hsum2 : 2 * (2 ^ k * (∑ ab ∈ pairs p, (Gab G ab.1 ab.2).card)) ≤ p ^ (2 * d) * 3 ^ k := by
      have hp2 : 0 < p ^ 2 := by positivity
      refine Nat.le_of_mul_le_mul_right ?_ hp2
      calc 2 * (2 ^ k * (∑ ab ∈ pairs p, (Gab G ab.1 ab.2).card)) * p ^ 2
          = 2 * (2 ^ k * (∑ ab ∈ pairs p, (Gab G ab.1 ab.2).card) * p ^ 2) := by ring
        _ ≤ 2 * ((pairs p).card * (p ^ (2 * d) * 3 ^ k)) := Nat.mul_le_mul_left _ hsum
        _ = (2 * (pairs p).card) * (p ^ (2 * d) * 3 ^ k) := by ring
        _ ≤ p ^ 2 * (p ^ (2 * d) * 3 ^ k) := Nat.mul_le_mul_right _ hpairs
        _ = p ^ (2 * d) * 3 ^ k * p ^ 2 := by ring
    have hc := count_step G
    calc 2 ^ (k + 1) * G.card
        ≤ 2 ^ (k + 1) * ((G.image Fin.init).card + ∑ ab ∈ pairs p, (Gab G ab.1 ab.2).card) :=
          Nat.mul_le_mul_left _ hc
      _ = 2 * (2 ^ k * (G.image Fin.init).card) +
            2 * (2 ^ k * (∑ ab ∈ pairs p, (Gab G ab.1 ab.2).card)) := by ring
      _ ≤ 2 * (p ^ (2 * d) * 3 ^ k) + p ^ (2 * d) * 3 ^ k :=
          add_le_add (Nat.mul_le_mul_left _ hA) hsum2
      _ = p ^ (2 * d) * 3 ^ (k + 1) := by ring

lemma shatter_proj {n p k m : ℕ} (H : Set (Fin n → Fin p)) (S : Fin k → Fin n)
    (T : Fin m → Fin k) (h : NShatters (proj H S) T) : NShatters H (S ∘ T) := by
  obtain ⟨f, g, hfg, hc⟩ := h
  refine ⟨f, g, hfg, fun c => ?_⟩
  obtain ⟨w, ⟨h0, hh, rfl⟩, e⟩ := hc c
  exact ⟨h0, hh, e⟩

lemma final_ineq (k d p : ℕ) (h : 4 ^ k ≤ p ^ (2 * d) * 3 ^ k) :
    (k : ℝ) ≤ 5 * d * Real.logb 2 p := by
  have h1 : 4 ^ k * 3 ^ (5 * k) ≤ 4 ^ (5 * k) := by
    have : (4 * 3 ^ 5) ^ k ≤ (4 ^ 5) ^ k := Nat.pow_le_pow_left (by norm_num) k
    calc 4 ^ k * 3 ^ (5 * k) = (4 * 3 ^ 5) ^ k := by rw [mul_pow, ← pow_mul]
      _ ≤ (4 ^ 5) ^ k := this
      _ = 4 ^ (5 * k) := by rw [← pow_mul]
  have h2 : 4 ^ (5 * k) ≤ p ^ (10 * d) * 3 ^ (5 * k) := by
    calc 4 ^ (5 * k) = (4 ^ k) ^ 5 := by rw [← pow_mul, mul_comm]
      _ ≤ (p ^ (2 * d) * 3 ^ k) ^ 5 := Nat.pow_le_pow_left h 5
      _ = p ^ (10 * d) * 3 ^ (5 * k) := by ring
  have h3 : 4 ^ k ≤ p ^ (10 * d) :=
    Nat.le_of_mul_le_mul_right (h1.trans h2) (by positivity)
  have h4 : (2 : ℝ) ^ (2 * k) ≤ (p : ℝ) ^ (10 * d) := by
    have : (2 : ℕ) ^ (2 * k) ≤ p ^ (10 * d) := by
      rw [pow_mul]
      exact h3
    exact_mod_cast this
  have h5 := Real.logb_le_logb_of_le (one_lt_two) (by positivity) h4
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one one_lt_two] at h5
  push_cast at h5
  linarith

end L29Aux

open L29Aux

theorem solution {n p : ℕ} (H : Set (Fin n → Fin p)) (dN dE : ℕ)
    (hN : natarajanDim H = dN) (hE : expDim H = dE) :
    (dE : ℝ) ≤ 5 * dN * Real.logb 2 p := by
  classical
  have hB0 : 0 ≤ 5 * (dN : ℝ) * Real.logb 2 p := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · subst h0
      simp
    · have : 0 ≤ Real.logb 2 (p : ℝ) :=
        Real.logb_nonneg one_lt_two (by exact_mod_cast h0)
      positivity
  have hall : ∀ (k : ℕ) (S : Fin k → Fin n), (2 : ℕ∞) ^ k ≤ (proj H S).encard →
      (k : ℝ) ≤ 5 * dN * Real.logb 2 p := by
    intro k S hk
    have hfin : (proj H S).Finite := Set.toFinite _
    have hcard : 2 ^ k ≤ hfin.toFinset.card := by
      rw [hfin.encard_eq_coe_toFinset_card] at hk
      exact_mod_cast hk
    rcases Nat.lt_or_ge p 2 with hp | hp
    · have hsub : Subsingleton (Fin k → Fin p) := by
        have : Subsingleton (Fin p) := Fin.subsingleton_iff_le_one.mpr (by omega)
        infer_instance
      have h1 : hfin.toFinset.card ≤ 1 := Finset.card_le_one_of_subsingleton _
      have hk0 : k = 0 := by
        by_contra hne
        have : 2 ≤ 2 ^ k := Nat.le_self_pow hne 2
        omega
      rw [hk0]
      simpa using hB0
    · have hd : ∀ (m : ℕ) (T : Fin m → Fin k),
          NShatters (↑hfin.toFinset : Set (Fin k → Fin p)) T → m ≤ dN := by
        intro m T hT
        rw [Set.Finite.coe_toFinset] at hT
        have hs := shatter_proj H S T hT
        have hle : (m : ℕ∞) ≤ natarajanDim H :=
          le_iSup_of_le m (le_iSup_of_le (S ∘ T) (le_iSup_of_le hs le_rfl))
        rw [hN] at hle
        exact_mod_cast hle
      have hb := bound k dN hfin.toFinset hp hd
      have h4 : 4 ^ k ≤ p ^ (2 * dN) * 3 ^ k := by
        calc 4 ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
          _ ≤ 2 ^ k * hfin.toFinset.card := Nat.mul_le_mul_left _ hcard
          _ ≤ p ^ (2 * dN) * 3 ^ k := hb
      exact final_ineq k dN p h4
  have hfl : (dE : ℕ∞) ≤ ((⌊5 * (dN : ℝ) * Real.logb 2 p⌋₊ : ℕ) : ℕ∞) := by
    rw [← hE]
    unfold expDim
    refine iSup_le fun k => iSup_le fun S => iSup_le fun hk => ?_
    exact_mod_cast Nat.le_floor (hall k S hk)
  have hfl' : dE ≤ ⌊5 * (dN : ℝ) * Real.logb 2 p⌋₊ := by exact_mod_cast hfl
  exact le_trans (by exact_mod_cast hfl') (Nat.floor_le hB0)
