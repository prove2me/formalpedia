-- Prove2me | solution 1 for GreedyColoringLCA969.LowerBound.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:56:51.214207+00:00
-- url     : https://prove2.me/submissions/dbe20c5a-8d02-4dda-9c53-f1b074467b03

import Definitions.Def_GreedyColoringLCA969_LowerBound_GraphBasics

namespace HGC

/-- A cyclic injective tuple of length `m + 3` in `H`. -/
def IsCyc {V : Type*} (H : SimpleGraph V) {m : ℕ} (u : Fin (m + 3) → V) : Prop :=
  Function.Injective u ∧ ∀ i : Fin (m + 3), H.Adj (u i) (u (i + 1))

lemma exists_cyc_of_isCycle {V : Type*} {H : SimpleGraph V} {a : V} {w : H.Walk a a}
    (hw : w.IsCycle) :
    ∃ (m : ℕ) (u : Fin (m + 3) → V), w.length = m + 3 ∧ IsCyc H u := by
  obtain ⟨m, hm⟩ : ∃ m, w.length = m + 3 := ⟨w.length - 3, by have := hw.three_le_length; omega⟩
  refine ⟨m, fun i => w.getVert i.val, hm, ?_, ?_⟩
  · intro i j hij
    have hinj := hw.getVert_injOn'
    have := hinj (by simp only [Set.mem_ofPred_eq]; have := i.2; omega)
      (by simp only [Set.mem_ofPred_eq]; have := j.2; omega) hij
    exact Fin.ext this
  · intro i
    by_cases hi : i.val < m + 2
    · have hval : (i + 1 : Fin (m + 3)).val = i.val + 1 := Fin.val_add_one_of_lt (by
        rw [Fin.lt_def]; simp; omega)
      show H.Adj (w.getVert i.val) (w.getVert (i + 1 : Fin (m + 3)).val)
      rw [hval]
      exact w.adj_getVert_succ (by omega)
    · have hi' : i.val = m + 2 := by have := i.2; omega
      have hval : (i + 1 : Fin (m + 3)) = 0 := by
        apply Fin.ext
        simp [Fin.val_add, hi']
      show H.Adj (w.getVert i.val) (w.getVert (i + 1 : Fin (m + 3)).val)
      rw [hval, hi']
      have h1 := w.adj_getVert_succ (i := m + 2) (by omega)
      have h2 : w.getVert (m + 2 + 1) = a := by
        have := w.getVert_length
        rwa [hm] at this
      simpa [h2, Fin.val_zero, SimpleGraph.Walk.getVert_zero] using h1

end HGC

namespace HGC

open Finset

section weights

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Weight of an edge-flag pattern `x` under independent flags with probability `p`. -/
noncomputable def wt (p : ℝ) (x : ι → Bool) : ℝ := ∏ e, if x e then p else 1 - p

lemma wt_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (x : ι → Bool) : 0 ≤ wt p x :=
  Finset.prod_nonneg fun e _ => by split_ifs <;> linarith

lemma sum_wt_piFinset (p : ℝ) (t : ι → Finset Bool) :
    ∑ x ∈ Fintype.piFinset t, wt p x = ∏ e, ∑ b ∈ t e, (if b then p else 1 - p) := by
  rw [Finset.prod_univ_sum (fun e => t e) (fun _ b => if b then p else 1 - p)]
  rfl

lemma sum_wt_univ (p : ℝ) : ∑ x : ι → Bool, wt p x = 1 := by
  have h := sum_wt_piFinset (ι := ι) p (fun _ => Finset.univ)
  rw [Fintype.piFinset_univ] at h
  rw [h]
  simp [Fintype.sum_bool]

/-- The weight of the event "all flags in `F₀` equal `b`". -/
lemma sum_wt_event (p : ℝ) (F₀ : Finset ι) (b : Bool) :
    ∑ x ∈ Finset.univ.filter (fun x : ι → Bool => ∀ e ∈ F₀, x e = b), wt p x =
      (if b then p else 1 - p) ^ F₀.card := by
  have hset : Finset.univ.filter (fun x : ι → Bool => ∀ e ∈ F₀, x e = b) =
      Fintype.piFinset (fun e => if e ∈ F₀ then {b} else Finset.univ) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h e
      by_cases he : e ∈ F₀
      · simp [he, h e he]
      · simp [he]
    · intro h e he
      have := h e
      simpa [he] using this
  rw [hset, sum_wt_piFinset]
  have : ∀ e : ι, (∑ c ∈ (if e ∈ F₀ then ({b} : Finset Bool) else Finset.univ),
      (if c then p else 1 - p)) = if e ∈ F₀ then (if b then p else 1 - p) else 1 := by
    intro e
    by_cases he : e ∈ F₀
    · simp [he]
    · simp [he, Fintype.sum_bool]
  simp_rw [this]
  rw [Finset.prod_ite_mem Finset.univ F₀ (fun _ => (if b then p else 1 - p))]
  simp

end weights

end HGC

namespace HGC

open Finset
open scoped Classical

/-- The graph on `Fin n` whose edges are the flagged pairs. -/
def gr {n : ℕ} (x : Sym2 (Fin n) → Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e | x e = true}

lemma gr_adj {n : ℕ} (x : Sym2 (Fin n) → Bool) (u v : Fin n) :
    (gr x).Adj u v ↔ x s(u, v) = true ∧ u ≠ v := by
  simp [gr, SimpleGraph.fromEdgeSet_adj]

/-- All cyclic edges of the tuple `u` are flagged. -/
def Pres {n m : ℕ} (x : Sym2 (Fin n) → Bool) (u : Fin (m + 3) → Fin n) : Prop :=
  ∀ i, x s(u i, u (i + 1)) = true

/-- The set of cyclic edges of a tuple. -/
noncomputable def edgesOf {V : Type*} {m : ℕ} (u : Fin (m + 3) → V) : Finset (Sym2 V) :=
  Finset.univ.image fun i => s(u i, u (i + 1))

lemma pres_iff {n m : ℕ} (x : Sym2 (Fin n) → Bool) (u : Fin (m + 3) → Fin n) :
    Pres x u ↔ ∀ e ∈ edgesOf u, x e = true := by
  simp [Pres, edgesOf]

lemma fin_succ_ne {m : ℕ} (i : Fin (m + 3)) : i + 1 ≠ i := by
  intro h
  have : (1 : Fin (m + 3)) = 0 := by simpa using h
  exact absurd (congrArg Fin.val this) (by simp)

lemma fin_two_ne {m : ℕ} (j : Fin (m + 3)) : j + 1 + 1 ≠ j := by
  intro h
  have h2 : (1 + 1 : Fin (m + 3)) = 0 := by
    have : j + (1 + 1) = j + 0 := by rw [← add_assoc, add_zero]; exact h
    exact add_left_cancel this
  have h3 : (((1 + 1 : Fin (m + 3)) : ℕ)) = 2 := by
    rw [Fin.val_add]
    simp
  rw [h2] at h3
  simp at h3

lemma edge_inj {V : Type*} {m : ℕ} {u : Fin (m + 3) → V} (hu : Function.Injective u) :
    Function.Injective fun i : Fin (m + 3) => s(u i, u (i + 1)) := by
  intro i j hij
  simp only [Sym2.eq_iff] at hij
  rcases hij with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact hu h1
  · have hi : i = j + 1 := hu h1
    have hj : i + 1 = j := hu h2
    rw [hi] at hj
    exact absurd hj (fin_two_ne j)

lemma card_edgesOf {V : Type*} {m : ℕ} {u : Fin (m + 3) → V}
    (hu : Function.Injective u) : (edgesOf u).card = m + 3 := by
  unfold edgesOf
  rw [Finset.card_image_of_injective _ (edge_inj hu)]
  simp

lemma isCyc_gr_iff {n m : ℕ} (x : Sym2 (Fin n) → Bool) (u : Fin (m + 3) → Fin n) :
    IsCyc (gr x) u ↔ Function.Injective u ∧ Pres x u := by
  unfold IsCyc Pres
  constructor
  · rintro ⟨hu, h⟩
    exact ⟨hu, fun i => ((gr_adj x _ _).1 (h i)).1⟩
  · rintro ⟨hu, h⟩
    refine ⟨hu, fun i => (gr_adj x _ _).2 ⟨h i, fun heq => fin_succ_ne i (hu heq).symm⟩⟩

/-- Number of short cyclic tuples present in `x`. -/
noncomputable def Xc (n g : ℕ) (x : Sym2 (Fin n) → Bool) : ℕ :=
  ∑ m ∈ range (g - 2),
    (Finset.univ.filter (fun u : Fin (m + 3) → Fin n => Function.Injective u ∧ Pres x u)).card

/-- Number of independent `a`-sets in `x`. -/
noncomputable def Yc (n a : ℕ) (x : Sym2 (Fin n) → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin n)).powersetCard a |>.filter
    (fun S => ∀ u ∈ S, ∀ v ∈ S, u ≠ v → x s(u, v) = false)).card

/-- General first-moment identity. -/
lemma sum_wt_mul_card_filter {ι κ : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) (b : Bool)
    (𝒯 : Finset κ) (F : κ → Finset ι) :
    ∑ x : ι → Bool, wt p x * ((𝒯.filter (fun τ => ∀ e ∈ F τ, x e = b)).card : ℝ) =
      ∑ τ ∈ 𝒯, (if b then p else 1 - p) ^ (F τ).card := by
  have h1 : ∀ x : ι → Bool, wt p x * ((𝒯.filter (fun τ => ∀ e ∈ F τ, x e = b)).card : ℝ) =
      ∑ τ ∈ 𝒯, if (∀ e ∈ F τ, x e = b) then wt p x else 0 := by
    intro x
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    split_ifs <;> simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← sum_wt_event p (F τ) b, Finset.sum_filter]


/-- Expected number of short cyclic tuples. -/
lemma sum_wt_Xc {n g : ℕ} {p : ℝ} (hp : 0 ≤ p) :
    ∑ x : Sym2 (Fin n) → Bool, wt p x * (Xc n g x : ℝ) ≤
      ∑ m ∈ range (g - 2), ((n : ℝ) * p) ^ (m + 3) := by
  have key : ∀ m : ℕ, ∑ x : Sym2 (Fin n) → Bool, wt p x *
      ((Finset.univ.filter (fun u : Fin (m + 3) → Fin n =>
        Function.Injective u ∧ Pres x u)).card : ℝ) ≤ ((n : ℝ) * p) ^ (m + 3) := by
    intro m
    have hcard : ∀ x : Sym2 (Fin n) → Bool,
        (Finset.univ.filter (fun u : Fin (m + 3) → Fin n => Function.Injective u ∧ Pres x u)) =
        ((Finset.univ.filter (fun u : Fin (m + 3) → Fin n => Function.Injective u)).filter
          (fun u => ∀ e ∈ edgesOf u, x e = true)) := by
      intro x
      rw [Finset.filter_filter]
      refine Finset.filter_congr fun u _ => ?_
      rw [pres_iff]
    simp_rw [hcard]
    rw [sum_wt_mul_card_filter p true]
    simp only [if_true]
    have : ∀ u ∈ (Finset.univ.filter (fun u : Fin (m + 3) → Fin n => Function.Injective u)),
        p ^ (edgesOf u).card = p ^ (m + 3) := by
      intro u hu
      rw [card_edgesOf (Finset.mem_filter.1 hu).2]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
    have hle : ((Finset.univ.filter (fun u : Fin (m + 3) → Fin n => Function.Injective u)).card : ℝ)
        ≤ (n : ℝ) ^ (m + 3) := by
      have : (Finset.univ.filter (fun u : Fin (m + 3) → Fin n => Function.Injective u)).card ≤
          n ^ (m + 3) := by
        calc _ ≤ (Finset.univ : Finset (Fin (m + 3) → Fin n)).card := Finset.card_filter_le _ _
          _ = n ^ (m + 3) := by simp
      exact_mod_cast this
    calc _ ≤ (n : ℝ) ^ (m + 3) * p ^ (m + 3) := by gcongr
      _ = ((n : ℝ) * p) ^ (m + 3) := (mul_pow _ _ _).symm
  unfold Xc
  simp_rw [Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun m _ => key m

lemma indep_iff_forall_edges {n : ℕ} (x : Sym2 (Fin n) → Bool) (S : Finset (Fin n)) :
    (∀ u ∈ S, ∀ v ∈ S, u ≠ v → x s(u, v) = false) ↔
      ∀ e ∈ S.offDiag.image Sym2.mk.uncurry, x e = false := by
  constructor
  · intro h e he
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.1 he
    rw [Finset.mem_offDiag] at huv
    exact h u huv.1 v huv.2.1 huv.2.2
  · intro h u hu v hv huv
    exact h _ (Finset.mem_image.2 ⟨(u, v), Finset.mem_offDiag.2 ⟨hu, hv, huv⟩, rfl⟩)

/-- Expected number of independent `a`-sets. -/
lemma sum_wt_Yc (n a : ℕ) (p : ℝ) :
    ∑ x : Sym2 (Fin n) → Bool, wt p x * (Yc n a x : ℝ) =
      (n.choose a : ℝ) * (1 - p) ^ (a.choose 2) := by
  have hY : ∀ x : Sym2 (Fin n) → Bool, Yc n a x =
      (((Finset.univ : Finset (Fin n)).powersetCard a).filter
        (fun S => ∀ e ∈ S.offDiag.image Sym2.mk.uncurry, x e = false)).card := by
    intro x
    unfold Yc
    congr 1
    exact Finset.filter_congr fun S _ => indep_iff_forall_edges x S
  simp_rw [hY]
  rw [sum_wt_mul_card_filter p false]
  simp only [Bool.false_eq_true, if_false]
  have : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard a,
      (1 - p) ^ (S.offDiag.image Sym2.mk.uncurry).card = (1 - p) ^ (a.choose 2) := by
    intro S hS
    rw [Sym2.card_image_offDiag, (Finset.mem_powersetCard.1 hS).2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  simp


end HGC

namespace HGC
open Finset
open scoped Classical

noncomputable def Zc (n k : ℕ) (x : Sym2 (Fin n) → Bool) : ℕ :=
  ∑ v : Fin n, ((Finset.univ : Finset (Fin n)).powersetCard k |>.filter
    (fun S => ∀ w ∈ S, x s(v, w) = true)).card

lemma sum_wt_Zc (n k : ℕ) (p : ℝ) :
    ∑ x : Sym2 (Fin n) → Bool, wt p x * (Zc n k x : ℝ) =
      n * (n.choose k : ℝ) * p ^ k := by
  have hZ : ∀ x : Sym2 (Fin n) → Bool, Zc n k x =
      ∑ v : Fin n, ((Finset.univ : Finset (Fin n)).powersetCard k |>.filter
        (fun S => ∀ e ∈ S.image (fun w => s(v,w)), x e = true)).card := by
    intro x
    unfold Zc
    apply Finset.sum_congr rfl
    intro v _
    congr 1
    ext S
    simp
  simp_rw [hZ, Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner (v : Fin n) : ∑ x : Sym2 (Fin n) → Bool, wt p x *
      (((Finset.univ : Finset (Fin n)).powersetCard k |>.filter
        (fun S => ∀ e ∈ S.image (fun w => s(v,w)), x e = true)).card : ℝ) = (n.choose k : ℝ) * p ^ k := by
    rw [sum_wt_mul_card_filter p true]
    have hinj : Function.Injective (fun w : Fin n => s(v,w)) := by
      intro a b hab
      simp only [Sym2.eq_iff, Prod.mk.injEq] at hab
      rcases hab with ⟨_, hab⟩ | ⟨h1, h2⟩
      · exact hab
      · exact h2.trans h1
    have hcard : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        (S.image (fun w => s(v,w))).card = k := by
      intro S hS
      rw [Finset.card_image_of_injective _ hinj, (Finset.mem_powersetCard.mp hS).2]
    simp only [if_true]
    simp_rw [Finset.sum_congr rfl (fun S hS => congrArg (p ^ ·) (hcard S hS))]
    simp
  simp_rw [hinner]
  simp [mul_assoc]

lemma choose_le_exp_pow (n a : ℕ) (ha : 0 < a) :
    (n.choose a : ℝ) ≤ (Real.exp 1 * n / a) ^ a := by
  have hap : (0 : ℝ) < a := by exact_mod_cast ha
  have hfact := Real.pow_div_factorial_le_exp (a : ℝ) (Nat.cast_nonneg a) a
  have hfacpos : (0 : ℝ) < a.factorial := by positivity
  have hbound : (a : ℝ) ^ a / Real.exp (a : ℝ) ≤ a.factorial := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    simpa [mul_comm] using (div_le_iff₀ hfacpos).mp hfact
  have hchoose : (n.choose a : ℝ) ≤ (n : ℝ) ^ a / a.factorial := Nat.choose_le_pow_div a n
  calc
    _ ≤ (n : ℝ) ^ a / a.factorial := hchoose
    _ ≤ (n : ℝ) ^ a / ((a : ℝ) ^ a / Real.exp (a : ℝ)) := by gcongr
    _ = (Real.exp 1 * n / a) ^ a := by
      rw [div_pow, mul_pow, ← Real.exp_nat_mul]
      push_cast
      field_simp

lemma bound_Y_dense {n q d a m : ℕ} (hq : 2 ≤ q) (hd : 1 ≤ d)
    (hn : n = q * d) (ha : a = q * m)
    (hm : (8 : ℝ) * (1 + Real.log d) ≤ m) :
    (n.choose a : ℝ) * (1 - 1 / (q : ℝ)) ^ (a.choose 2) < 1 / 2 := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hq)
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  have hm8 : (8 : ℝ) ≤ m := by linarith
  have hmp : (0 : ℝ) < m := by linarith
  have hap : 0 < a := by rw [ha]; exact Nat.mul_pos (by omega) (by exact_mod_cast hmp)
  have hA : (a : ℝ) = q * m := by rw [ha]; push_cast; rfl
  have hN : (n : ℝ) = q * d := by rw [hn]; push_cast; rfl
  have hA8 : (8 : ℝ) ≤ a := by rw [hA]; nlinarith [show (2 : ℝ) ≤ q by exact_mod_cast hq]
  have hchoose : (n.choose a : ℝ) ≤ Real.exp ((a : ℝ) * (1 + Real.log d)) := by
    calc
      _ ≤ (Real.exp 1 * n / a) ^ a := choose_le_exp_pow n a hap
      _ ≤ (Real.exp 1 * d) ^ a := by
        gcongr
        apply (div_le_iff₀ (by exact_mod_cast hap : (0 : ℝ) < a)).mpr
        rw [hN, hA]
        calc
          Real.exp 1 * (q * d) ≤ Real.exp 1 * (q * d) * m :=
            le_mul_of_one_le_right (by positivity) (by linarith)
          _ = Real.exp 1 * d * (q * m) := by ring
      _ = Real.exp ((a : ℝ) * (1 + Real.log d)) := by
        rw [show Real.exp 1 * (d : ℝ) = Real.exp (1 + Real.log d) by rw [Real.exp_add, Real.exp_log hdp],
          ← Real.exp_nat_mul]
  have hbase : 0 ≤ 1 - 1 / (q : ℝ) := by
    have : 1 / (q : ℝ) ≤ 1 := (div_le_one hqp).mpr (by exact_mod_cast (show 1 ≤ q by omega))
    linarith
  have h2 : (1 - 1 / (q : ℝ)) ^ (a.choose 2) ≤ Real.exp ((a.choose 2 : ℕ) * (-(1 / (q : ℝ)))) := by
    calc
      _ ≤ (Real.exp (-(1 / (q : ℝ)))) ^ (a.choose 2) := by
        gcongr
        have := Real.add_one_le_exp (-(1 / (q : ℝ)))
        linarith
      _ = _ := (Real.exp_nat_mul _ _).symm
  have hC : ((a.choose 2 : ℕ) : ℝ) * (1 / (q : ℝ)) = (m : ℝ) * (a - 1) / 2 := by
    rw [Nat.cast_choose_two, hA]
    field_simp
  have hprod : (n.choose a : ℝ) * (1 - 1 / (q : ℝ)) ^ (a.choose 2) ≤
      Real.exp (a * (1 + Real.log d) - (m : ℝ) * (a - 1) / 2) := by
    calc
      _ ≤ Real.exp (a * (1 + Real.log d)) * Real.exp ((a.choose 2 : ℕ) * (-(1 / (q : ℝ)))) :=
        mul_le_mul hchoose h2 (pow_nonneg hbase _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; nlinarith [hC]
  have hexp : (a : ℝ) * (1 + Real.log d) - (m : ℝ) * (a - 1) / 2 ≤ -1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (show (4 : ℝ) ≤ a by linarith)) (by linarith : 0 ≤ m - 8 * (1 + Real.log d))]
  have hgt : (2 : ℝ) < Real.exp 1 := by have := Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0); linarith
  have hneg : Real.exp (-1) < 1 / 2 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    simpa using hgt
  exact hprod.trans_lt ((Real.exp_le_exp.mpr hexp).trans_lt hneg)

lemma bound_Z_dense {n q d : ℕ} (hq : 2 ≤ q) (hd : 1 ≤ d) (hn : n = q * d) :
    (n : ℝ) * (n.choose (64 * d) : ℝ) * (1 / (q : ℝ)) ^ (64 * d) ≤ n / 16 := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hq)
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hk : 0 < 64 * d := by omega
  have hN : (n : ℝ) = q * d := by rw [hn]; push_cast; rfl
  have hbase : Real.exp 1 * n / (64 * d : ℕ) * (1 / (q : ℝ)) ≤ (1 / 16 : ℝ) := by
    push_cast
    rw [hN]
    have he : Real.exp 1 ≤ 4 := Real.exp_one_lt_three.le.trans (by norm_num)
    field_simp
    nlinarith
  have hpow : (1 / 16 : ℝ) ^ (64 * d) ≤ 1 / 16 := by
    simpa using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 16) (by norm_num : (1 / 16 : ℝ) ≤ 1)
      (show 1 ≤ 64 * d by omega)
  calc
    _ ≤ (n : ℝ) * (Real.exp 1 * n / (64 * d : ℕ)) ^ (64 * d) * (1 / (q : ℝ)) ^ (64 * d) := by
      gcongr
      exact choose_le_exp_pow n (64 * d) hk
    _ = (n : ℝ) * (Real.exp 1 * n / (64 * d : ℕ) * (1 / (q : ℝ))) ^ (64 * d) := by rw [mul_pow]; ring
    _ ≤ (n : ℝ) * (1 / 16) ^ (64 * d) := by gcongr
    _ ≤ (n : ℝ) * (1 / 16) := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg n)
    _ = _ := by ring

lemma exists_good_bounded_flags {n g a k : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n)
    (hX : ∑ m ∈ range (g - 2), ((n : ℝ) * p) ^ (m + 3) < n / 8)
    (hY : (n.choose a : ℝ) * (1 - p) ^ (a.choose 2) < 1 / 2)
    (hZ : (n : ℝ) * (n.choose k : ℝ) * p ^ k ≤ n / 16) :
    ∃ x : Sym2 (Fin n) → Bool, ((Xc n g x + Zc n k x : ℕ) : ℝ) < n / 2 ∧ Yc n a x = 0 := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  by_contra hcon
  push Not at hcon
  have hTerm : ∀ x : Sym2 (Fin n) → Bool,
      1 ≤ (Yc n a x : ℝ) + 2 / n * ((Xc n g x : ℝ) + Zc n k x) := by
    intro x
    by_cases h : ((Xc n g x + Zc n k x : ℕ) : ℝ) < n / 2
    · have hy : Yc n a x ≠ 0 := hcon x h
      have hh : (1 : ℝ) ≤ (Yc n a x : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hy
      have hnon : 0 ≤ 2 / (n : ℝ) * ((Xc n g x : ℝ) + Zc n k x) := by positivity
      linarith
    · have hh : n / 2 ≤ (Xc n g x : ℝ) + Zc n k x := by push_cast at h; linarith
      have hmul : 1 ≤ 2 / (n : ℝ) * ((Xc n g x : ℝ) + Zc n k x) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hnr]; linarith
      have : (0 : ℝ) ≤ Yc n a x := Nat.cast_nonneg _
      linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ => mul_le_mul_of_nonneg_left (hTerm x) (wt_nonneg hp0 hp1 x))
  simp only [mul_one, sum_wt_univ] at hsum
  have heq : (∑ x : Sym2 (Fin n) → Bool, wt p x *
      ((Yc n a x : ℝ) + 2 / n * ((Xc n g x : ℝ) + Zc n k x))) =
      (n.choose a : ℝ) * (1 - p) ^ (a.choose 2) +
        2 / n * ((∑ x : Sym2 (Fin n) → Bool, wt p x * (Xc n g x : ℝ)) +
          (n : ℝ) * (n.choose k : ℝ) * p ^ k) := by
    rw [← sum_wt_Yc n a p, ← sum_wt_Zc n k p]
    simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [heq] at hsum
  have hx := sum_wt_Xc (n := n) (g := g) hp0
  have hsmall : (∑ x : Sym2 (Fin n) → Bool, wt p x * (Xc n g x : ℝ)) +
      (n : ℝ) * (n.choose k : ℝ) * p ^ k < 3 * n / 16 := by linarith
  have hsmall' := mul_lt_mul_of_pos_left hsmall (by positivity : 0 < 2 / (n : ℝ))
  have heq' : 2 / (n : ℝ) * (3 * n / 16) = 3 / 8 := by field_simp; ring
  rw [heq'] at hsmall'
  linarith

lemma exists_bounded_graph {n g a k : ℕ} (hg : 3 ≤ g) {x : Sym2 (Fin n) → Bool}
    (hX : ((Xc n g x + Zc n k x : ℕ) : ℝ) < n / 2) (hY : Yc n a x = 0) :
    ∃ (N : ℕ) (G : SimpleGraph (Fin N)), (n : ℝ) / 2 < N ∧
      (∀ v, G.degree v < k) ∧ (g : ℕ∞) < G.egirth ∧
      ∀ S : Finset (Fin N), (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬G.Adj u v) → S.card < a := by
  let Cyc : Finset (Fin n) := (range (g - 2)).biUnion fun m =>
    (Finset.univ.filter (fun u : Fin (m + 3) → Fin n =>
      Function.Injective u ∧ Pres x u)).image (fun u => u 0)
  have hCyc : Cyc.card ≤ Xc n g x := by
    calc
      Cyc.card ≤ ∑ m ∈ range (g - 2), ((Finset.univ.filter (fun u : Fin (m + 3) → Fin n =>
        Function.Injective u ∧ Pres x u)).image (fun u => u 0)).card := Finset.card_biUnion_le
      _ ≤ ∑ m ∈ range (g - 2), (Finset.univ.filter (fun u : Fin (m + 3) → Fin n =>
        Function.Injective u ∧ Pres x u)).card := Finset.sum_le_sum fun m _ => Finset.card_image_le
      _ = Xc n g x := rfl
  let Bad := Finset.univ.filter (fun v => k ≤ (gr x).degree v)
  have hBad : Bad.card ≤ Zc n k x := by
    rw [show Bad.card = ∑ v : Fin n, if k ≤ (gr x).degree v then 1 else 0 by simp only [Bad, Finset.card_filter]]
    apply Finset.sum_le_sum
    intro v _
    split_ifs with hv
    · obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq (show k ≤ ((gr x).neighborFinset v).card by simpa using hv)
      apply Finset.card_pos.mpr
      refine ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hScard⟩, ?_⟩⟩
      intro w hw
      exact (gr_adj x v w).mp (((gr x).mem_neighborFinset v w).mp (hS hw)) |>.1
    · exact Nat.zero_le _
  let D := Cyc ∪ Bad
  have hD : D.card ≤ Xc n g x + Zc n k x :=
    (Finset.card_union_le Cyc Bad).trans (Nat.add_le_add hCyc hBad)
  have hD2 : 2 * D.card < n := by
    have hd : (D.card : ℝ) ≤ (Xc n g x + Zc n k x : ℕ) := by exact_mod_cast hD
    exact_mod_cast (show (2 * D.card : ℝ) < n by linarith)
  let K : Finset (Fin n) := Dᶜ
  let N := K.card
  let e : Fin N ↪o Fin n := K.orderEmbOfFin rfl
  have he_mem : ∀ i, e i ∈ K := fun i => Finset.orderEmbOfFin_mem K rfl i
  let G : SimpleGraph (Fin N) := (gr x).comap e
  have hGadj : ∀ u v : Fin N, G.Adj u v ↔ x s(e u, e v) = true ∧ e u ≠ e v := fun u v => gr_adj x _ _
  refine ⟨N, G, ?_, ?_, ?_, ?_⟩
  · have hKcard : K.card = n - D.card := by change Dᶜ.card = _; rw [Finset.card_compl, Fintype.card_fin]
    have hN : n < 2 * N := by dsimp [N]; omega
    have hNr : (n : ℝ) < 2 * N := by exact_mod_cast hN
    linarith
  · intro v
    have hnot : e v ∉ Bad := fun h => Finset.mem_compl.mp (he_mem v) (Finset.mem_union_right _ h)
    have hdeg : (gr x).degree (e v) < k := by simpa [Bad] using hnot
    apply lt_of_le_of_lt _ hdeg
    rw [← G.card_neighborSet_eq_degree, ← (gr x).card_neighborSet_eq_degree]
    apply Fintype.card_le_of_injective (fun w : G.neighborSet v => (⟨e w.val, w.prop⟩ : (gr x).neighborSet (e v)))
    intro u w h
    apply Subtype.ext
    have hv : e u.val = e w.val := congrArg (fun z : (gr x).neighborSet (e v) => z.val) h
    exact e.injective hv
  · have hle : ((g + 1 : ℕ) : ℕ∞) ≤ G.egirth := by
      rw [SimpleGraph.le_egirth]
      intro a' w hw
      obtain ⟨m, u, hlen, hcyc⟩ := exists_cyc_of_isCycle hw
      rw [hlen]
      by_contra hlt
      have hmg : m + 3 ≤ g := by
        have : ¬ (g + 1 ≤ m + 3) := by exact_mod_cast hlt
        omega
      let τ : Fin (m + 3) → Fin n := fun i => e (u i)
      have hτinj : Function.Injective τ := e.injective.comp hcyc.1
      have hτpres : Pres x τ := fun i => ((hGadj _ _).mp (hcyc.2 i)).1
      have hmem : τ 0 ∈ Cyc := Finset.mem_biUnion.mpr ⟨m, Finset.mem_range.mpr (by omega),
        Finset.mem_image.mpr ⟨τ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hτinj, hτpres⟩, rfl⟩⟩
      exact Finset.mem_compl.mp (he_mem (u 0)) (Finset.mem_union_left _ hmem)
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self g) hle
  · intro S hS
    by_contra hge
    obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (le_of_not_gt hge)
    have h1 : 1 ≤ Yc n a x := by
      apply Finset.card_pos.mpr
      refine ⟨T.image e, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, ?_⟩⟩
      · rw [Finset.card_image_of_injective _ e.injective, hTcard]
      · intro u hu v hv huv
        obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
        by_contra hne
        have hx : x s(e u', e v') = true := by simpa using hne
        exact hS u' (hTS hu') v' (hTS hv') (fun h => huv (congrArg e h)) ((hGadj u' v').mpr ⟨hx, huv⟩)
    omega

lemma exists_independence_graph (d g m : ℕ) (hd : 1 ≤ d) (hg : 3 ≤ g)
    (hm : (8 : ℝ) * (1 + Real.log d) ≤ m) :
    ∃ (N : ℕ) (G : SimpleGraph (Fin N)), 0 < N ∧
      GreedyColoringLCA969.LowerBound.MaxDegreeAtMost G (64 * d : ℝ) ∧
      GreedyColoringLCA969.LowerBound.GirthAtLeast G (g : ℝ) ∧
      ∀ S : Finset (Fin N), (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬G.Adj u v) →
        (S.card : ℝ) ≤ (2 * m / d : ℝ) * N := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hmpos : (0 : ℝ) < m := by
    have hl : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
    linarith
  let B : ℝ := ∑ j ∈ range (g - 2), (d : ℝ) ^ (j + 3)
  obtain ⟨q, hq⟩ := exists_nat_gt (max (8 * B) 2)
  have hq2 : 2 ≤ q := by have := lt_of_le_of_lt (le_max_right (8 * B) 2) hq; exact_mod_cast this.le
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  let n := q * d
  have hnp : 0 < n := Nat.mul_pos (by omega) (by omega)
  have hnp' : (0 : ℝ) < n := by exact_mod_cast hnp
  have hmean : (n : ℝ) * (1 / (q : ℝ)) = d := by dsimp [n]; push_cast; field_simp
  have hX : ∑ j ∈ range (g - 2), ((n : ℝ) * (1 / (q : ℝ))) ^ (j + 3) < n / 8 := by
    simp_rw [hmean]
    have hqb : 8 * B < q := lt_of_le_of_lt (le_max_left _ _) hq
    have hdn : (q : ℝ) ≤ n := by dsimp [n]; push_cast; exact le_mul_of_one_le_right hqp.le (by exact_mod_cast hd)
    change B < n / 8
    linarith
  have hp1 : 1 / (q : ℝ) ≤ 1 := (div_le_one hqp).mpr (by exact_mod_cast (show 1 ≤ q by omega))
  obtain ⟨x, hx, hy⟩ := exists_good_bounded_flags (by positivity) hp1 hnp hX
    (bound_Y_dense hq2 hd rfl rfl hm) (bound_Z_dense hq2 hd rfl)
  obtain ⟨N, G, hN, hdeg, hgirth, hind⟩ := exists_bounded_graph hg hx hy
  refine ⟨N, G, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast (lt_trans (by positivity : (0 : ℝ) < n / 2) hN)
  · intro v
    have hcast : (G.degree v : ℝ) ≤ 64 * d := by exact_mod_cast (hdeg v).le
    change (Nat.card (G.neighborSet v) : ℝ) ≤ _
    rw [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]
    exact hcast
  · intro v p hp
    have hlen : g ≤ p.length := by
      have hle := (SimpleGraph.egirth_le_length hp)
      exact_mod_cast (hgirth.trans_le hle).le
    exact_mod_cast hlen
  · intro S hS
    have hscard : (S.card : ℝ) ≤ q * m := by exact_mod_cast (hind S hS).le
    apply hscard.trans
    have hmult := mul_le_mul_of_nonneg_left hN.le hmpos.le
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hdp).mpr
    dsimp [n] at hmult
    push_cast at hmult
    nlinarith

lemma color_count_from_independence {N : ℕ} (G : SimpleGraph (Fin N)) (α T ε : ℝ)
    (hα : 0 ≤ α) (hT : 0 ≤ T) (hbound : T * α ≤ ε)
    (hind : ∀ S : Finset (Fin N), (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬G.Adj u v) →
      (S.card : ℝ) ≤ α * N)
    (c : Fin N → ℕ+) (hc : GreedyColoringLCA969.LowerBound.IsProper G c) :
    (1 - ε) * (N : ℝ) ≤ (Nat.card {v : Fin N // T ≤ ((c v).val : ℝ)} : ℝ) := by
  let Low := Finset.univ.filter (fun v => ((c v).val : ℝ) < T)
  have hlowSub : Low ⊆ (Finset.Icc 1 ⌊T⌋₊).biUnion (fun k => Finset.univ.filter (fun v => (c v).val = k)) := by
    intro v hv
    have hv' := (Finset.mem_filter.mp hv).2
    exact Finset.mem_biUnion.mpr ⟨(c v).val, Finset.mem_Icc.mpr ⟨(c v).pos,
      (Nat.le_floor hv'.le)⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have hfiber (k : ℕ) : ((Finset.univ.filter (fun v => (c v).val = k)).card : ℝ) ≤ α * N := by
    apply hind
    intro u hu v hv hne hadj
    apply hc u v hadj
    apply PNat.eq
    exact (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm
  have hlow : (Low.card : ℝ) ≤ ε * N := by
    calc
      _ ≤ (((Finset.Icc 1 ⌊T⌋₊).biUnion (fun k => Finset.univ.filter (fun v => (c v).val = k))).card : ℝ) :=
        by exact_mod_cast Finset.card_le_card hlowSub
      _ ≤ ∑ k ∈ Finset.Icc 1 ⌊T⌋₊, ((Finset.univ.filter (fun v => (c v).val = k)).card : ℝ) :=
        by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ Finset.Icc 1 ⌊T⌋₊, α * N := Finset.sum_le_sum (fun k _ => hfiber k)
      _ = (⌊T⌋₊ : ℝ) * (α * N) := by simp [Nat.card_Icc]
      _ ≤ T * (α * N) := mul_le_mul_of_nonneg_right (Nat.floor_le hT) (by positivity)
      _ ≤ ε * N := by simpa [mul_assoc] using mul_le_mul_of_nonneg_right hbound (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hpartition : Low.card + (Finset.univ.filter (fun v => T ≤ ((c v).val : ℝ))).card = N := by
    have hh := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N))) (fun v => ((c v).val : ℝ) < T)
    simpa only [not_lt, Finset.card_univ, Fintype.card_fin] using hh
  have hpart : (Low.card : ℝ) + ((Finset.univ.filter (fun v => T ≤ ((c v).val : ℝ))).card : ℝ) = N := by exact_mod_cast hpartition
  have hcard : Nat.card {v : Fin N // T ≤ ((c v).val : ℝ)} = (Finset.univ.filter (fun v => T ≤ ((c v).val : ℝ))).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard]
  linarith

end HGC

open GreedyColoringLCA969.LowerBound in
theorem solution (ε : ℝ) (hε : 0 < ε) :
    ∃ C C' : ℝ, 0 < C ∧ 1 < C' ∧
      ∀ Δ g : ℝ, C' < Δ → C' < g →
        ∃ (n : ℕ) (G : SimpleGraph (Fin n)), 0 < n ∧
          MaxDegreeAtMost G Δ ∧ GirthAtLeast G g ∧
          ∀ c : Fin n → ℕ+, IsProper G c →
            (1 - ε) * (n : ℝ) ≤
              (Nat.card {v : Fin n // C * Δ / log2 Δ ≤ ((c v).val : ℝ)} : ℝ) := by
  classical
  refine ⟨ε / 4352, 128, by positivity, by norm_num, ?_⟩
  intro Δ g hΔ hg
  have hΔp : 0 < Δ := by linarith
  have hl2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2one : Real.log 2 ≤ 1 := by have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); norm_num at this; exact this
  have hlΔ : 0 ≤ Real.log Δ := (Real.log_pos (by linarith)).le
  have hL : 1 ≤ log2 Δ := by
    change 1 ≤ Real.log Δ / Real.log 2
    apply (le_div_iff₀ hl2p).mpr
    simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ Δ)
  have hLp : 0 < log2 Δ := by linarith
  have hlogL : Real.log Δ ≤ log2 Δ := by
    change Real.log Δ ≤ Real.log Δ / Real.log 2
    apply (le_div_iff₀ hl2p).mpr
    exact mul_le_of_le_one_right hlΔ hl2one
  let d := ⌊Δ / 64⌋₊
  have hdlo : (d : ℝ) ≤ Δ / 64 := Nat.floor_le (by positivity)
  have hdhi : Δ / 64 < (d : ℝ) + 1 := Nat.lt_floor_add_one _
  have hdhalf : Δ / 128 ≤ (d : ℝ) := by linarith
  have hd : 1 ≤ d := by exact_mod_cast (show (1 : ℝ) ≤ d by linarith)
  have hdp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdΔ : (d : ℝ) ≤ Δ := by linarith
  have hlogd : Real.log (d : ℝ) ≤ log2 Δ := (Real.log_le_log hdp hdΔ).trans hlogL
  have hlogdnon : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  let m := ⌈8 * (1 + Real.log (d : ℝ))⌉₊
  have hm : (8 : ℝ) * (1 + Real.log d) ≤ m := Nat.le_ceil _
  have hmupper : (m : ℝ) < 8 * (1 + Real.log d) + 1 := Nat.ceil_lt_add_one (by linarith)
  have hmL : (m : ℝ) ≤ 17 * log2 Δ := by linarith
  have hmpos : (0 : ℝ) < m := by linarith
  let gn := max 3 ⌈g⌉₊
  have hgn : 3 ≤ gn := le_max_left _ _
  have hgnreal : g ≤ (gn : ℝ) := (Nat.le_ceil g).trans (by exact_mod_cast (le_max_right 3 ⌈g⌉₊))
  obtain ⟨n, G, hn, hdeg, hgirth, hind⟩ := HGC.exists_independence_graph d gn m hd hgn hm
  have hα : (2 * m / d : ℝ) ≤ 4352 * log2 Δ / Δ := by
    apply (div_le_div_iff₀ hdp hΔp).mpr
    calc
      (2 : ℝ) * m * Δ ≤ (34 * log2 Δ) * Δ := mul_le_mul_of_nonneg_right (by linarith) hΔp.le
      _ ≤ (34 * log2 Δ) * (128 * d) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 4352 * log2 Δ * d := by ring
  refine ⟨n, G, hn, ?_, ?_, ?_⟩
  · intro v
    exact (hdeg v).trans (by linarith)
  · intro v p hp
    exact hgnreal.trans (hgirth v p hp)
  · intro c hc
    apply HGC.color_count_from_independence G (2 * m / d) (ε / 4352 * Δ / log2 Δ) ε (by positivity) (by positivity) _ hind c hc
    calc
      ε / 4352 * Δ / log2 Δ * (2 * m / d) ≤ ε / 4352 * Δ / log2 Δ * (4352 * log2 Δ / Δ) :=
        mul_le_mul_of_nonneg_left hα (by positivity)
      _ = ε := by field_simp
