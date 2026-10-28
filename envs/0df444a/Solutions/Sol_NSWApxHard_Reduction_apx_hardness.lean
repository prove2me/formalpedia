-- Prove2me | solution 1 for NSWApxHard.Reduction.apx_hardness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T21:39:47.855622+00:00
-- url     : https://prove2.me/submissions/aaed3926-e63d-4b23-ad3b-466adf44dcaa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Complexity
import Definitions.Def_NSWApxHard_Reduction_Welfare
import Definitions.Def_NSWApxHard_Reduction_CubicVC
import Definitions.Def_NSWApxHard_Reduction_Instance
import Theorems.Thm_NSWApxHard_Reduction_instance_size
import Theorems.Thm_NSWApxHard_Reduction_completeness
import Theorems.Thm_NSWApxHard_Reduction_lemma_2_4
import Theorems.Thm_NSWApxHard_Reduction_reduction_encode_polyTime
import Theorems.Thm_CookPvsNP_P_subset_NP
import Theorems.Thm_CookPvsNP_polyTimeComputable_comp

set_option autoImplicit false

namespace NSWApxHard.Reduction

open Finset CookPvsNP

/-! ### Part 1: Parameter selection and basic bounds -/

lemma univ_mem_NP_bool : (Set.univ : Lang Bool) ∈ NP Bool := by
  apply P_subset_NP Bool
  let M : TM Bool := {
    Q := Bool
    q₀ := true
    qaccept := true
    qreject := false
    accept_ne_reject := by decide
    δ := fun _ _ => (true, none, Move.right)
  }
  refine ⟨Bool, inferInstance, Function.Embedding.refl Bool, M, 0, ?_, ?_⟩
  · intro w
    show M.IsHalting (M.run (w.length ^ 0 + 0) (M.init _))
    have h0 : M.IsHalting (M.init (w.map (Function.Embedding.refl Bool))) := Or.inl rfl
    rw [Nat.pow_zero, Nat.add_zero]
    change M.IsHalting (M.step (M.init _))
    rw [TM.step, if_pos h0]
    exact h0
  · intro w
    simp only [Set.mem_univ, true_iff]
    exact ⟨0, rfl⟩

lemma empty_mem_NP_bool : (∅ : Lang Bool) ∈ NP Bool := by
  apply P_subset_NP Bool
  let M : TM Bool := {
    Q := Bool
    q₀ := false
    qaccept := true
    qreject := false
    accept_ne_reject := by decide
    δ := fun _ _ => (false, none, Move.right)
  }
  refine ⟨Bool, inferInstance, Function.Embedding.refl Bool, M, 0, ?_, ?_⟩
  · intro w
    show M.IsHalting (M.run (w.length ^ 0 + 0) (M.init _))
    have h0 : M.IsHalting (M.init (w.map (Function.Embedding.refl Bool))) := Or.inr rfl
    rw [Nat.pow_zero, Nat.add_zero]
    change M.IsHalting (M.step (M.init _))
    rw [TM.step, if_pos h0]
    exact h0
  · intro w
    simp only [Set.mem_empty_iff_false, false_iff]
    rintro ⟨t, ht⟩
    have h0 : M.IsHalting (M.init (w.map (Function.Embedding.refl Bool))) := Or.inr rfl
    have hfix : Function.IsFixedPt M.step (M.init (w.map (Function.Embedding.refl Bool))) := by
      change M.step _ = _
      rw [TM.step, if_pos h0]
    rw [TM.run, hfix.iterate t] at ht
    exact Bool.noConfusion ht

lemma cmin_nonneg_of_theorem21 {cmin cmax : ℝ} (hCC : Theorem21 cmin cmax) : 0 ≤ cmin := by
  obtain ⟨f₀, _, hf₀⟩ := hCC Bool Set.univ univ_mem_NP_bool
  obtain ⟨hN, _, C, _, hC⟩ := (hf₀ []).1 (Set.mem_univ _)
  have h0 : (0 : ℝ) ≤ (C.card : ℝ) := Nat.cast_nonneg _
  have hN' : (0 : ℝ) < (f₀ []).N := Nat.cast_pos.mpr hN
  nlinarith

lemma cmax_le_one_of_theorem21 {cmin cmax : ℝ} (hCC : Theorem21 cmin cmax) : cmax ≤ 1 := by
  obtain ⟨f₀, _, hf₀⟩ := hCC Bool ∅ empty_mem_NP_bool
  obtain ⟨hN, _, hC⟩ := (hf₀ []).2 (by simp)
  have huniv : (f₀ []).G.IsVertexCover
      (↑(Finset.univ : Finset (Fin (f₀ []).N)) : Set (Fin (f₀ []).N)) := by
    rw [Finset.coe_univ]
    exact SimpleGraph.isVertexCover_univ
  have hle := hC Finset.univ huniv
  simp only [Finset.card_univ, Fintype.card_fin] at hle
  have hN' : (0 : ℝ) < (f₀ []).N := Nat.cast_pos.mpr hN
  nlinarith

lemma mu_gt_one {cmin cmax α : ℝ} (hc : cmin < cmax) (hα₁ : 1 / 3 < α) (hα₂ : α < 1 / 2) :
    1 < (2 * (1 + α) / 3) ^ (-(((cmax - cmin) / 3) / 2.5)) := by
  have hbase_pos : 0 < 2 * (1 + α) / 3 := by linarith
  have hbase_lt : 2 * (1 + α) / 3 < 1 := by linarith
  have hexp_neg : -(((cmax - cmin) / 3) / 2.5) < 0 := by norm_num; linarith
  exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hbase_pos hbase_lt hexp_neg

lemma exists_params {cmin cmax α : ℝ} (hc0 : 0 ≤ cmin) (hc : cmin < cmax)
    (hα₁ : 1 / 3 < α) (hα₂ : α < 1 / 2) :
    ∃ (m₀ a b : ℕ), 1 ≤ m₀ ∧ 0 < b ∧
      let α' : ℝ := ((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3)
      1 / 3 < α' ∧ α' < 1 / 2 ∧
      cmin ≤ (a : ℝ) / b ∧ (a : ℝ) / b < cmax ∧
      (2 * (1 + α') / 3) ^ (((cmax - (a : ℝ) / b) / 3) / 2.5) *
        (2 * (1 + α) / 3) ^ (-(((cmax - cmin) / 3) / 2.5)) ≤ 1 := by
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt (1 / (3 * (α - 1 / 3)))
  let m₁ := max m₀ 1
  have hm₁_ge1 : 1 ≤ m₁ := le_max_right _ _
  have hm₁_gt : 1 / (3 * (α - 1 / 3)) < (m₁ : ℝ) :=
    lt_of_lt_of_le hm₀ (Nat.cast_le.mpr (le_max_left _ _))
  let α' : ℝ := ((m₁ : ℝ) + 2) / (3 * (m₁ : ℝ) + 3)
  have h3m_pos : (0 : ℝ) < 3 * (m₁ : ℝ) + 3 := by positivity
  have hα'₁ : 1 / 3 < α' := by
    dsimp [α']
    rw [div_lt_div_iff₀ (by norm_num) h3m_pos]
    linarith
  have hα'_lt_α : α' < α := by
    have hdiff : 0 < α - 1 / 3 := by linarith
    have h1 : 1 < (m₁ : ℝ) * (3 * (α - 1 / 3)) := (div_lt_iff₀ (by positivity)).mp hm₁_gt
    dsimp [α']
    rw [div_lt_iff₀ h3m_pos]
    linarith
  have hα'₂ : α' < 1 / 2 := lt_trans hα'_lt_α hα₂
  let β' : ℝ := 2 * (1 + α') / 3
  let β : ℝ := 2 * (1 + α) / 3
  have hβ'_pos : 0 < β' := by dsimp [β']; linarith
  have hβ'_lt_β : β' < β := by dsimp [β', β]; linarith
  have hβ_lt1 : β < 1 := by dsimp [β]; linarith
  have hlogβ : Real.log β < 0 := Real.log_neg (by linarith) hβ_lt1
  have hlogβ' : Real.log β' < Real.log β := Real.log_lt_log hβ'_pos hβ'_lt_β
  have hlogβ'_neg : Real.log β' < 0 := lt_trans hlogβ' hlogβ
  have hrat_pos : 0 < Real.log β / Real.log β' := div_pos_of_neg_of_neg hlogβ hlogβ'_neg
  have hrat_lt1 : Real.log β / Real.log β' < 1 := by
    have hpos : 0 < -Real.log β' := by linarith
    have h1 : (-Real.log β) / (-Real.log β') < 1 := (div_lt_iff₀ hpos).mpr (by linarith)
    calc Real.log β / Real.log β' = (-Real.log β) / (-Real.log β') := by ring
      _ < 1 := h1
  let cmid : ℝ := cmax - (cmax - cmin) * (Real.log β / Real.log β')
  have hcmid_gt : cmin < cmid := by
    dsimp [cmid]
    nlinarith
  have hcmid_lt : cmid < cmax := by
    dsimp [cmid]
    nlinarith
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hcmid_gt
  have hq_pos : (0 : ℝ) < (q : ℝ) := lt_of_le_of_lt hc0 hq₁
  have hq_num_pos : 0 < q.num := by
    have : (0 : ℚ) < q := by exact_mod_cast hq_pos
    exact Rat.num_pos.mpr this
  let a : ℕ := q.num.toNat
  let b : ℕ := q.den
  have hb_pos : 0 < b := q.den_pos
  have hab_eq : (a : ℝ) / b = (q : ℝ) := by
    rw [Rat.cast_def]
    congr 1
    have : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg (le_of_lt hq_num_pos)
    exact_mod_cast this
  refine ⟨m₁, a, b, hm₁_ge1, hb_pos, hα'₁, hα'₂, ?_, ?_, ?_⟩
  · rw [hab_eq]; exact le_of_lt hq₁
  · rw [hab_eq]; exact lt_trans hq₂ hcmid_lt
  · rw [hab_eq]
    have hle1 : ((cmax - (q : ℝ)) / 3) / 2.5 * Real.log β' ≤
        ((cmax - cmid) / 3) / 2.5 * Real.log β' := by
      have : (cmax - cmid) / 3 / 2.5 ≤ (cmax - (q : ℝ)) / 3 / 2.5 := by norm_num; linarith
      exact mul_le_mul_of_nonpos_right this (le_of_lt hlogβ'_neg)
    have h_eq : ((cmax - cmid) / 3) / 2.5 * Real.log β' =
        ((cmax - cmin) / 3) / 2.5 * Real.log β := by
      dsimp [cmid]
      have hne : Real.log β' ≠ 0 := ne_of_lt hlogβ'_neg
      calc ((cmax - (cmax - (cmax - cmin) * (Real.log β / Real.log β'))) / 3) / 2.5 * Real.log β'
        _ = ((cmax - cmin) / 3) / 2.5 * ((Real.log β / Real.log β') * Real.log β') := by ring
        _ = ((cmax - cmin) / 3) / 2.5 * Real.log β := by rw [div_mul_cancel₀ _ hne]
    rw [Real.rpow_def_of_pos hβ'_pos, Real.rpow_def_of_pos (lt_trans hβ'_pos hβ'_lt_β)]
    rw [← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    linarith

/-! ### Part 2: Completeness for `C.card ≤ k` and welfare-gap correctness -/

lemma completeness_of_le {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (k : ℕ) (α : ℝ)
    (hG : IsCubic G) (hα₁ : 1 / 3 < α) (hα₂ : α < 1 / 2) (hk : k ≤ N)
    (C : Finset (Fin N)) (hC : G.IsVertexCover ↑C) (hCk : C.card ≤ k) :
    ∃ x : Item G k → Agent G,
      nsw (redUtil G k α) x = (1 + α) ^ ((3 * (k : ℝ) - 3 * N / 2) / (5 * N / 2)) := by
  have hk' : k ≤ Fintype.card (Fin N) := by simpa using hk
  obtain ⟨D, hCD, hDk⟩ := Finset.exists_superset_card_eq hCk hk'
  have hD : G.IsVertexCover ↑D := hC.subset (Finset.coe_subset.mpr hCD)
  exact completeness G k α hG hα₁ hα₂ D hD hDk

lemma k_lt_N_of_params {a b N : ℕ} (hb : 0 < b) (hab : (a : ℝ) / b < 1) (hN : 0 < N) :
    (a * N) / b < N := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hab_real : (a : ℝ) < (b : ℝ) := by
    have := (div_lt_iff₀ hb').mp hab
    linarith
  have hab_nat : a < b := by exact_mod_cast hab_real
  exact (Nat.div_lt_iff_lt_mul hb).mpr (by nlinarith)

lemma card_le_k_of_le_cmin {cmin : ℝ} {a b N : ℕ} (hb : 0 < b)
    (hcmin : cmin ≤ (a : ℝ) / b) {c : ℕ} (hc : (c : ℝ) ≤ cmin * N) :
    c ≤ (a * N) / b := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hN' : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 : (c : ℝ) ≤ ((a : ℝ) / b) * N := le_trans hc (mul_le_mul_of_nonneg_right hcmin hN')
  have h2 : (c : ℝ) * b ≤ (a : ℝ) * N := by
    have := (le_div_iff₀ hb').mp (by linarith [div_mul_eq_mul_div (a : ℝ) (b : ℝ) (N : ℝ)] :
      (c : ℝ) ≤ ((a : ℝ) * N) / b)
    linarith
  have h3 : c * b ≤ a * N := by exact_mod_cast h2
  exact (Nat.le_div_iff_mul_le hb).mpr h3

lemma k_cast_le_mul {a b N : ℕ} (hb : 0 < b) :
    (((a * N) / b : ℕ) : ℝ) ≤ ((a : ℝ) / b) * N := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have h1 : ((a * N) / b) * b ≤ a * N := Nat.div_mul_le_self (a * N) b
  have h2 : (((a * N) / b : ℕ) : ℝ) * b ≤ (a : ℝ) * N := by exact_mod_cast h1
  rw [div_mul_eq_mul_div, le_div_iff₀ hb']
  exact h2

lemma soundness_bound_of_vcNo {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {cmax α' μ : ℝ} {a b : ℕ} (hb : 0 < b) (hN : 0 < N) (hG : IsCubic G)
    (hα'₁ : 1 / 3 < α') (hα'₂ : α' < 1 / 2)
    (hab_lt1 : (a : ℝ) / b < 1) (hμ_pos : 0 < μ)
    (hgap : (2 * (1 + α') / 3) ^ (((cmax - (a : ℝ) / b) / 3) / 2.5) * μ ≤ 1)
    (hC : ∀ C : Finset (Fin N), G.IsVertexCover ↑C → cmax * N ≤ (C.card : ℝ))
    (x : Item G ((a * N) / b) → Agent G) :
    let k := (a * N) / b
    nsw (redUtil G k α') x ≤
      (1 + α') ^ ((3 * (k : ℝ) - 3 * N / 2) / (5 * N / 2)) / μ := by
  intro k
  have hk : k < N := k_lt_N_of_params hb hab_lt1 hN
  have h24 := lemma_2_4 G k α' (cmax * N) hG hα'₁ hα'₂ hk hC x
  let β' : ℝ := 2 * (1 + α') / 3
  let W : ℝ := (1 + α') ^ ((3 * (k : ℝ) - 3 * N / 2) / (5 * N / 2))
  have hβ'_pos : 0 < β' := by dsimp [β']; linarith
  have hβ'_le1 : β' ≤ 1 := by dsimp [β']; linarith
  have hW_nn : 0 ≤ W := Real.rpow_nonneg (by linarith) _
  have hk_le : (k : ℝ) ≤ ((a : ℝ) / b) * N := k_cast_le_mul hb
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
  have hexp_eq : ((cmax - (a : ℝ) / b) / 3) / 2.5 =
      ((cmax * N - ((a : ℝ) / b) * N) / 3) / (5 * N / 2) := by
    norm_num
    field_simp
  have hexp_le : ((cmax - (a : ℝ) / b) / 3) / 2.5 ≤ ((cmax * N - k) / 3) / (5 * N / 2) := by
    rw [hexp_eq]
    have hnum : (cmax * N - ((a : ℝ) / b) * N) / 3 ≤ (cmax * N - k) / 3 := by linarith
    exact div_le_div_of_nonneg_right hnum (by positivity)
  have hrpow_le : β' ^ (((cmax * N - k) / 3) / (5 * N / 2)) ≤
      β' ^ (((cmax - (a : ℝ) / b) / 3) / 2.5) :=
    Real.rpow_le_rpow_of_exponent_ge hβ'_pos hβ'_le1 hexp_le
  have hβ'_le_inv : β' ^ (((cmax * N - k) / 3) / (5 * N / 2)) ≤ 1 / μ := by
    rw [le_div_iff₀ hμ_pos]
    calc β' ^ (((cmax * N - k) / 3) / (5 * N / 2)) * μ
      _ ≤ β' ^ (((cmax - (a : ℝ) / b) / 3) / 2.5) * μ :=
          mul_le_mul_of_nonneg_right hrpow_le hμ_pos.le
      _ ≤ 1 := hgap
  calc nsw (redUtil G k α') x
    _ ≤ β' ^ (((cmax * N - k) / 3) / (5 * N / 2)) * W := h24
    _ ≤ (1 / μ) * W := mul_le_mul_of_nonneg_right hβ'_le_inv hW_nn
    _ = W / μ := by ring

/-! ### Part 3: Integer utility and threshold scaling (`NSWInput`) -/

def redNatUtil {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (k m₀ : ℕ) :
    Agent G → Item G k → ℕ
  | Sum.inl _, Sum.inl _ => (3 * m₀ + 3) * (4 * m₀ + 5)
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inl _, Sum.inr (Sum.inl _) => 0
  | Sum.inr e, Sum.inr (Sum.inl e') => if e = e' then (2 * m₀ + 1) * (4 * m₀ + 5) else 0
  | Sum.inl v, Sum.inr (Sum.inr s) => if s.1.1 = v then (m₀ + 1) * (4 * m₀ + 5) else 0
  | Sum.inr e, Sum.inr (Sum.inr s) => if e.1 = s.1.2 then (m₀ + 2) * (4 * m₀ + 5) else 0

lemma redNatUtil_cast {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (k m₀ : ℕ)
    (ag : Agent G) (it : Item G k) :
    let α' : ℝ := ((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3)
    let S : ℕ := (3 * m₀ + 3) * (4 * m₀ + 5)
    (redNatUtil G k m₀ ag it : ℝ) = (S : ℝ) * redUtil G k α' ag it := by
  intro α' S
  have h3m_ne : (3 * (m₀ : ℝ) + 3) ≠ 0 := by positivity
  rcases ag with v | e <;> rcases it with j | (e' | s) <;>
    simp only [redNatUtil, redUtil, α', S] <;> (try split_ifs) <;> push_cast <;> field_simp <;> ring

lemma redUtil_nonneg {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (k : ℕ) (α : ℝ)
    (hα₁ : 1 / 3 < α) (hα₂ : α < 1 / 2) (ag : Agent G) (it : Item G k) :
    0 ≤ redUtil G k α ag it := by
  rcases ag with v | e <;> rcases it with j | (e' | s) <;>
    simp only [redUtil] <;> (try split_ifs) <;> linarith

lemma utility_nonneg_of_nonneg {A B : Type} [Fintype A] [Fintype B] [DecidableEq A]
    (u : A → B → ℝ) (hu : ∀ a b, 0 ≤ u a b) (x : B → A) (a : A) :
    0 ≤ utility u x a :=
  Finset.sum_nonneg fun i _ => hu a i

lemma utility_scale_equiv {A B : Type} [Fintype A] [Fintype B] [DecidableEq A]
    {n m : ℕ} (eA : Fin n ≃ A) (eB : Fin m ≃ B)
    (u : A → B → ℝ) (u' : Fin n → Fin m → ℝ) (S : ℝ)
    (hu : ∀ (a : Fin n) (i : Fin m), u' a i = S * u (eA a) (eB i))
    (x : Fin m → Fin n) (a : Fin n) :
    utility u' x a = S * utility u (fun b => eA (x (eB.symm b))) (eA a) := by
  unfold utility
  have h1 : ∑ i ∈ univ.filter (fun i : Fin m => x i = a), u' a i =
      S * ∑ i ∈ univ.filter (fun i : Fin m => x i = a), u (eA a) (eB i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => hu a i
  rw [h1]
  congr 1
  refine Finset.sum_bij (fun i _ => eB i) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    rw [Equiv.symm_apply_apply, hi]
  · intro i₁ _ i₂ _ h
    exact eB.injective h
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    refine ⟨eB.symm b, ?_, Equiv.apply_symm_apply eB b⟩
    simp only [mem_filter, mem_univ, true_and]
    exact eA.injective hb
  · intros; rfl

lemma nsw_scale_equiv {A B : Type} [Fintype A] [Fintype B] [DecidableEq A]
    {n m : ℕ} (hn : 0 < n) (eA : Fin n ≃ A) (eB : Fin m ≃ B)
    (u : A → B → ℝ) (hu_nn : ∀ a b, 0 ≤ u a b)
    (u' : Fin n → Fin m → ℝ) (S : ℝ) (hS : 0 ≤ S)
    (hu : ∀ (a : Fin n) (i : Fin m), u' a i = S * u (eA a) (eB i))
    (x : Fin m → Fin n) :
    nsw u' x = S * nsw u (fun b => eA (x (eB.symm b))) := by
  let y : B → A := fun b => eA (x (eB.symm b))
  unfold nsw
  have hcard : Fintype.card A = n := by
    rw [← Fintype.card_congr eA, Fintype.card_fin]
  have hprod : (∏ a : Fin n, utility u' x a) = S ^ n * (∏ a : A, utility u y a) := by
    calc (∏ a : Fin n, utility u' x a)
      _ = ∏ a : Fin n, (S * utility u y (eA a)) :=
          Finset.prod_congr rfl fun a _ => utility_scale_equiv eA eB u u' S hu x a
      _ = (∏ _a : Fin n, S) * (∏ a : Fin n, utility u y (eA a)) := Finset.prod_mul_distrib
      _ = S ^ n * (∏ a : A, utility u y a) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, eA.prod_comp]
  have hprod_nn : 0 ≤ ∏ a : A, utility u y a :=
    Finset.prod_nonneg fun a _ => utility_nonneg_of_nonneg u hu_nn y a
  rw [hprod, Fintype.card_fin, hcard]
  rw [Real.mul_rpow (pow_nonneg hS n) hprod_nn]
  congr 1
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  rw [← Real.rpow_natCast S n, ← Real.rpow_mul hS, mul_one_div_cancel hn', Real.rpow_one]

def redT (N k m₀ : ℕ) : ℕ :=
  (3 * m₀ + 3) ^ (4 * N - 3 * k) * (4 * m₀ + 5) ^ (N + 3 * k)

lemma redT_ge_one (N k m₀ : ℕ) : 1 ≤ redT N k m₀ := by
  unfold redT
  exact Nat.one_le_iff_ne_zero.mpr (by positivity)

lemma redT_rpow {N k m₀ n : ℕ} (hN : 0 < N) (hk : k ≤ N) (hn : 2 * n = 5 * N) :
    let α' : ℝ := ((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3)
    let S : ℕ := (3 * m₀ + 3) * (4 * m₀ + 5)
    ((redT N k m₀ : ℝ) ^ ((1 : ℝ) / n)) =
      (S : ℝ) * (1 + α') ^ ((3 * (k : ℝ) - 3 * N / 2) / (5 * N / 2)) := by
  intro α' S
  let A : ℝ := 3 * (m₀ : ℝ) + 3
  let B : ℝ := 4 * (m₀ : ℝ) + 5
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hn_pos : 0 < n := by omega
  have hn_real : (n : ℝ) = 5 * (N : ℝ) / 2 := by
    have : 2 * (n : ℝ) = 5 * (N : ℝ) := by exact_mod_cast hn
    linarith
  have h4N : ((4 * N - 3 * k : ℕ) : ℝ) = 4 * (N : ℝ) - 3 * (k : ℝ) := by
    have hle : 3 * k ≤ 4 * N := by omega
    rw [Nat.cast_sub hle]
    push_cast
    ring
  have hNk : ((N + 3 * k : ℕ) : ℝ) = (N : ℝ) + 3 * (k : ℝ) := by
    push_cast
    ring
  have h1α : 1 + α' = B / A := by
    dsimp [α', A, B]
    have hA_ne : (3 * (m₀ : ℝ) + 3) ≠ 0 := ne_of_gt hA
    field_simp
    ring
  have hS_eq : (S : ℝ) = A * B := by
    dsimp [S, A, B]
    push_cast
    ring
  let β_exp : ℝ := (3 * (k : ℝ) - 3 * N / 2) / (5 * N / 2)
  have hexp1 : (4 * (N : ℝ) - 3 * (k : ℝ)) * (1 / (n : ℝ)) = 1 - β_exp := by
    dsimp [β_exp]
    rw [hn_real]
    have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN)
    field_simp
    ring
  have hexp2 : ((N : ℝ) + 3 * (k : ℝ)) * (1 / (n : ℝ)) = 1 + β_exp := by
    dsimp [β_exp]
    rw [hn_real]
    have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN)
    field_simp
    ring
  have hT_cast : (redT N k m₀ : ℝ) = A ^ (4 * N - 3 * k) * B ^ (N + 3 * k) := by
    unfold redT
    dsimp [A, B]
    push_cast
    rfl
  rw [hT_cast, Real.mul_rpow (pow_nonneg hA.le _) (pow_nonneg hB.le _)]
  rw [← Real.rpow_natCast A, ← Real.rpow_natCast B]
  rw [← Real.rpow_mul hA.le, ← Real.rpow_mul hB.le]
  rw [h4N, hNk, hexp1, hexp2]
  rw [Real.rpow_sub hA, Real.rpow_add hB, Real.rpow_one, Real.rpow_one]
  rw [hS_eq, h1α, Real.div_rpow hB.le hA.le]
  ring

def mkNSWInput {N n m : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (k m₀ : ℕ)
    (eA : Fin n ≃ Agent G) (eB : Fin m ≃ Item G k) : NSWInput where
  n := n
  m := m
  u := fun a i => redNatUtil G k m₀ (eA a) (eB i)
  T := redT N k m₀

lemma mkNSWInput_nswYes {cmin : ℝ} {a b m₀ : ℕ} (hb : 0 < b)
    (hcmin : cmin ≤ (a : ℝ) / b) (hab_lt1 : (a : ℝ) / b < 1)
    (hα'₁ : 1 / 3 < ((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3))
    (hα'₂ : ((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3) < 1 / 2)
    (I : GraphInput) [DecidableRel I.G.Adj]
    {n m : ℕ} (eA : Fin n ≃ Agent I.G) (eB : Fin m ≃ Item I.G ((a * I.N) / b))
    (hyes : vcYes cmin I) :
    nswYes (mkNSWInput I.G ((a * I.N) / b) m₀ eA eB) := by
  obtain ⟨hN, hG, C, hC, hC_card⟩ := hyes
  let k := (a * I.N) / b
  let α' : ℝ := ((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3)
  let S : ℕ := (3 * m₀ + 3) * (4 * m₀ + 5)
  have hcardA : Fintype.card (Agent I.G) = n := by
    rw [← Fintype.card_congr eA, Fintype.card_fin]
  have hcardB : Fintype.card (Item I.G k) = m := by
    rw [← Fintype.card_congr eB, Fintype.card_fin]
  obtain ⟨hsizeA, hsizeB⟩ := instance_size I.G k hG
  rw [hcardA] at hsizeA
  rw [hcardB] at hsizeB
  have hn1 : 1 ≤ n := by omega
  have hnm : n ≤ m := by omega
  have hk_lt : k < I.N := k_lt_N_of_params hb hab_lt1 hN
  have hCk : C.card ≤ k := card_le_k_of_le_cmin hb hcmin hC_card
  obtain ⟨y, hy⟩ := completeness_of_le I.G k α' hG hα'₁ hα'₂ hk_lt.le C hC hCk
  refine ⟨hn1, hnm, redT_ge_one I.N k m₀, ⟨fun i => eA.symm (y (eB i)), ?_⟩⟩
  show (mkNSWInput I.G k m₀ eA eB).tau ≤ (mkNSWInput I.G k m₀ eA eB).nswOf _
  unfold NSWInput.tau NSWInput.nswOf mkNSWInput
  dsimp only
  have h_nsw := nsw_scale_equiv (by omega : 0 < n) eA eB (redUtil I.G k α')
    (redUtil_nonneg I.G k α' hα'₁ hα'₂)
    (fun a i => (redNatUtil I.G k m₀ (eA a) (eB i) : ℝ)) (S : ℝ) (Nat.cast_nonneg S)
    (fun a i => redNatUtil_cast I.G k m₀ (eA a) (eB i))
    (fun i => eA.symm (y (eB i)))
  have hy_eq : (fun b => eA (eA.symm (y (eB (eB.symm b))))) = y := by
    ext b
    simp
  rw [hy_eq, hy] at h_nsw
  rw [h_nsw, redT_rpow hN hk_lt.le hsizeA]

lemma mkNSWInput_nswNo {cmax μ : ℝ} {a b m₀ : ℕ} (hb : 0 < b)
    (hab_lt1 : (a : ℝ) / b < 1) (hμ_pos : 0 < μ)
    (hα'₁ : 1 / 3 < ((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3))
    (hα'₂ : ((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3) < 1 / 2)
    (hgap : (2 * (1 + ((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3)) / 3) ^
      (((cmax - (a : ℝ) / b) / 3) / 2.5) * μ ≤ 1)
    (I : GraphInput) [DecidableRel I.G.Adj]
    {n m : ℕ} (eA : Fin n ≃ Agent I.G) (eB : Fin m ≃ Item I.G ((a * I.N) / b))
    (hno : vcNo cmax I) :
    nswNo μ (mkNSWInput I.G ((a * I.N) / b) m₀ eA eB) := by
  obtain ⟨hN, hG, hC⟩ := hno
  let k := (a * I.N) / b
  let α' : ℝ := ((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3)
  let S : ℕ := (3 * m₀ + 3) * (4 * m₀ + 5)
  have hcardA : Fintype.card (Agent I.G) = n := by
    rw [← Fintype.card_congr eA, Fintype.card_fin]
  have hcardB : Fintype.card (Item I.G k) = m := by
    rw [← Fintype.card_congr eB, Fintype.card_fin]
  obtain ⟨hsizeA, hsizeB⟩ := instance_size I.G k hG
  rw [hcardA] at hsizeA
  rw [hcardB] at hsizeB
  have hn1 : 1 ≤ n := by omega
  have hnm : n ≤ m := by omega
  have hk_lt : k < I.N := k_lt_N_of_params hb hab_lt1 hN
  refine ⟨hn1, hnm, redT_ge_one I.N k m₀, fun x => ?_⟩
  show (mkNSWInput I.G k m₀ eA eB).nswOf x ≤ (mkNSWInput I.G k m₀ eA eB).tau / μ
  unfold NSWInput.tau NSWInput.nswOf mkNSWInput
  dsimp only
  have h_nsw := nsw_scale_equiv (by omega : 0 < n) eA eB (redUtil I.G k α')
    (redUtil_nonneg I.G k α' hα'₁ hα'₂)
    (fun a i => (redNatUtil I.G k m₀ (eA a) (eB i) : ℝ)) (S : ℝ) (Nat.cast_nonneg S)
    (fun a i => redNatUtil_cast I.G k m₀ (eA a) (eB i)) x
  have h_sound := soundness_bound_of_vcNo I.G hb hN hG hα'₁ hα'₂ hab_lt1 hμ_pos hgap hC
    (fun b => eA (x (eB.symm b)))
  rw [h_nsw, redT_rpow hN hk_lt.le hsizeA, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left h_sound (Nat.cast_nonneg S)

open Classical in
noncomputable def reduceGraph (m₀ a b : ℕ) (I : GraphInput) : NSWInput :=
  let k := (a * I.N) / b
  mkNSWInput I.G k m₀ (Fintype.equivFin (Agent I.G)).symm (Fintype.equivFin (Item I.G k)).symm

lemma reduceGraph_nswYes {cmin : ℝ} {a b m₀ : ℕ} (hb : 0 < b)
    (hcmin : cmin ≤ (a : ℝ) / b) (hab_lt1 : (a : ℝ) / b < 1)
    (hα'₁ : 1 / 3 < ((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3))
    (hα'₂ : ((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3) < 1 / 2)
    (I : GraphInput) (hyes : vcYes cmin I) :
    nswYes (reduceGraph m₀ a b I) := by
  classical
  exact mkNSWInput_nswYes hb hcmin hab_lt1 hα'₁ hα'₂ I
    (Fintype.equivFin (Agent I.G)).symm
    (Fintype.equivFin (Item I.G ((a * I.N) / b))).symm hyes

lemma reduceGraph_nswNo {cmax μ : ℝ} {a b m₀ : ℕ} (hb : 0 < b)
    (hab_lt1 : (a : ℝ) / b < 1) (hμ_pos : 0 < μ)
    (hα'₁ : 1 / 3 < ((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3))
    (hα'₂ : ((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3) < 1 / 2)
    (hgap : (2 * (1 + ((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3)) / 3) ^
      (((cmax - (a : ℝ) / b) / 3) / 2.5) * μ ≤ 1)
    (I : GraphInput) (hno : vcNo cmax I) :
    nswNo μ (reduceGraph m₀ a b I) := by
  classical
  exact mkNSWInput_nswNo hb hab_lt1 hμ_pos hα'₁ hα'₂ hgap I
    (Fintype.equivFin (Agent I.G)).symm
    (Fintype.equivFin (Item I.G ((a * I.N) / b))).symm hno

lemma nswYes_of_scaled {cmin : ℝ} {a b m₀ : ℕ} (hb : 0 < b)
    (hcmin : cmin ≤ (a : ℝ) / b) (hab_lt1 : (a : ℝ) / b < 1)
    (hα'₁ : 1 / 3 < ((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3))
    (hα'₂ : ((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3) < 1 / 2)
    (I : GraphInput) [DecidableRel I.G.Adj] (P : NSWInput)
    (hT : P.T = redT I.N ((a * I.N) / b) m₀)
    (eA : Fin P.n ≃ Agent I.G) (eB : Fin P.m ≃ Item I.G ((a * I.N) / b))
    (hu : ∀ ag it, (P.u ag it : ℝ) =
      ((3 * (m₀ : ℝ) + 3) * (4 * (m₀ : ℝ) + 5)) *
        redUtil I.G ((a * I.N) / b) (((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3)) (eA ag) (eB it))
    (hyes : vcYes cmin I) :
    nswYes P := by
  obtain ⟨hN, hG, C, hC, hC_card⟩ := hyes
  let k := (a * I.N) / b
  let α' : ℝ := ((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3)
  let S : ℕ := (3 * m₀ + 3) * (4 * m₀ + 5)
  have hS_cast : (S : ℝ) = (3 * (m₀ : ℝ) + 3) * (4 * (m₀ : ℝ) + 5) := by
    dsimp [S]; push_cast; ring
  have hcardA : Fintype.card (Agent I.G) = P.n := by
    rw [← Fintype.card_congr eA, Fintype.card_fin]
  have hcardB : Fintype.card (Item I.G k) = P.m := by
    rw [← Fintype.card_congr eB, Fintype.card_fin]
  obtain ⟨hsizeA, hsizeB⟩ := instance_size I.G k hG
  rw [hcardA] at hsizeA
  rw [hcardB] at hsizeB
  have hn1 : 1 ≤ P.n := by omega
  have hnm : P.n ≤ P.m := by omega
  have hk_lt : k < I.N := k_lt_N_of_params hb hab_lt1 hN
  have hCk : C.card ≤ k := card_le_k_of_le_cmin hb hcmin hC_card
  obtain ⟨y, hy⟩ := completeness_of_le I.G k α' hG hα'₁ hα'₂ hk_lt.le C hC hCk
  have hT_ge1 : 1 ≤ P.T := by rw [hT]; exact redT_ge_one I.N k m₀
  refine ⟨hn1, hnm, hT_ge1, ⟨fun i => eA.symm (y (eB i)), ?_⟩⟩
  unfold NSWInput.tau NSWInput.nswOf
  have h_nsw := nsw_scale_equiv (by omega : 0 < P.n) eA eB (redUtil I.G k α')
    (redUtil_nonneg I.G k α' hα'₁ hα'₂)
    (fun a i => (P.u a i : ℝ)) (S : ℝ) (Nat.cast_nonneg S)
    (fun a i => by rw [hS_cast]; exact hu a i)
    (fun i => eA.symm (y (eB i)))
  have hy_eq : (fun b => eA (eA.symm (y (eB (eB.symm b))))) = y := by
    ext b
    simp
  rw [hy_eq, hy] at h_nsw
  rw [h_nsw, hT, redT_rpow hN hk_lt.le hsizeA]

lemma nswNo_of_scaled {cmax μ : ℝ} {a b m₀ : ℕ} (hb : 0 < b)
    (hab_lt1 : (a : ℝ) / b < 1) (hμ_pos : 0 < μ)
    (hα'₁ : 1 / 3 < ((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3))
    (hα'₂ : ((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3) < 1 / 2)
    (hgap : (2 * (1 + ((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3)) / 3) ^
      (((cmax - (a : ℝ) / b) / 3) / 2.5) * μ ≤ 1)
    (I : GraphInput) [DecidableRel I.G.Adj] (P : NSWInput)
    (hT : P.T = redT I.N ((a * I.N) / b) m₀)
    (eA : Fin P.n ≃ Agent I.G) (eB : Fin P.m ≃ Item I.G ((a * I.N) / b))
    (hu : ∀ ag it, (P.u ag it : ℝ) =
      ((3 * (m₀ : ℝ) + 3) * (4 * (m₀ : ℝ) + 5)) *
        redUtil I.G ((a * I.N) / b) (((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3)) (eA ag) (eB it))
    (hno : vcNo cmax I) :
    nswNo μ P := by
  obtain ⟨hN, hG, hC⟩ := hno
  let k := (a * I.N) / b
  let α' : ℝ := ((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3)
  let S : ℕ := (3 * m₀ + 3) * (4 * m₀ + 5)
  have hS_cast : (S : ℝ) = (3 * (m₀ : ℝ) + 3) * (4 * (m₀ : ℝ) + 5) := by
    dsimp [S]; push_cast; ring
  have hcardA : Fintype.card (Agent I.G) = P.n := by
    rw [← Fintype.card_congr eA, Fintype.card_fin]
  have hcardB : Fintype.card (Item I.G k) = P.m := by
    rw [← Fintype.card_congr eB, Fintype.card_fin]
  obtain ⟨hsizeA, hsizeB⟩ := instance_size I.G k hG
  rw [hcardA] at hsizeA
  rw [hcardB] at hsizeB
  have hn1 : 1 ≤ P.n := by omega
  have hnm : P.n ≤ P.m := by omega
  have hk_lt : k < I.N := k_lt_N_of_params hb hab_lt1 hN
  have hT_ge1 : 1 ≤ P.T := by rw [hT]; exact redT_ge_one I.N k m₀
  refine ⟨hn1, hnm, hT_ge1, fun x => ?_⟩
  unfold NSWInput.tau NSWInput.nswOf
  have h_nsw := nsw_scale_equiv (by omega : 0 < P.n) eA eB (redUtil I.G k α')
    (redUtil_nonneg I.G k α' hα'₁ hα'₂)
    (fun a i => (P.u a i : ℝ)) (S : ℝ) (Nat.cast_nonneg S)
    (fun a i => by rw [hS_cast]; exact hu a i) x
  have h_sound := soundness_bound_of_vcNo I.G hb hN hG hα'₁ hα'₂ hab_lt1 hμ_pos hgap hC
    (fun b => eA (x (eB.symm b)))
  rw [h_nsw, hT, redT_rpow hN hk_lt.le hsizeA, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left h_sound (Nat.cast_nonneg S)

/-! ### Part 4: Reduction to polynomial-time encoding of the reduced instance -/

theorem apx_hardness_of_polyTime_reduce
    (hpoly : ∀ (m₀ a b : ℕ), 1 ≤ m₀ → 0 < b → a < b →
      ∃ (P : GraphInput → NSWInput) (g : List Bool → List Bool),
        PolyTimeComputable g ∧
        ∀ (I : GraphInput) [DecidableRel I.G.Adj], 0 < I.N → IsCubic I.G →
          let k := (a * I.N) / b
          encNSW (P I) = g (encGraph I) ∧
          (P I).T = (3 * m₀ + 3) ^ (4 * I.N - 3 * k) * (4 * m₀ + 5) ^ (I.N + 3 * k) ∧
          ∃ (eA : Fin (P I).n ≃ Agent I.G) (eB : Fin (P I).m ≃ Item I.G k),
            ∀ (ag : Fin (P I).n) (it : Fin (P I).m),
              ((P I).u ag it : ℝ) =
                ((3 * (m₀ : ℝ) + 3) * (4 * (m₀ : ℝ) + 5)) *
                  redUtil I.G k (((m₀ : ℝ) + 2) / (3 * (m₀ : ℝ) + 3)) (eA ag) (eB it))
    (cmin cmax α : ℝ) (hc : cmin < cmax) (hα₁ : 1 / 3 < α) (hα₂ : α < 1 / 2)
    (hCC : Theorem21 cmin cmax) :
    1 < (2 * (1 + α) / 3) ^ (-(((cmax - cmin) / 3) / 2.5)) ∧
      SetCoverThreshold.SetCover.GapNPHard encNSW nswYes
        (nswNo ((2 * (1 + α) / 3) ^ (-(((cmax - cmin) / 3) / 2.5)))) := by
  classical
  have hμ_gt1 : 1 < (2 * (1 + α) / 3) ^ (-(((cmax - cmin) / 3) / 2.5)) :=
    mu_gt_one hc hα₁ hα₂
  have hμ_pos : 0 < (2 * (1 + α) / 3) ^ (-(((cmax - cmin) / 3) / 2.5)) :=
    lt_trans zero_lt_one hμ_gt1
  refine ⟨hμ_gt1, ?_⟩
  have hc0 : 0 ≤ cmin := cmin_nonneg_of_theorem21 hCC
  have hc1 : cmax ≤ 1 := cmax_le_one_of_theorem21 hCC
  obtain ⟨m₀, a, b, hm₀, hb, hα'₁, hα'₂, hcmin, hcmax, hgap⟩ :=
    exists_params hc0 hc hα₁ hα₂
  have hab_lt1 : (a : ℝ) / b < 1 := lt_of_lt_of_le hcmax hc1
  have hab_nat : a < b := by
    have hb' : (0 : ℝ) < b := Nat.cast_pos.mpr hb
    have : (a : ℝ) < (b : ℝ) := by
      have := (div_lt_iff₀ hb').mp hab_lt1
      linarith
    exact_mod_cast this
  obtain ⟨P, g, hg_poly, hg_spec⟩ := hpoly m₀ a b hm₀ hb hab_nat
  intro Sym' _ _ L' hL'
  obtain ⟨f_G, hf_G_poly, hf_G_corr⟩ := hCC Sym' L' hL'
  refine ⟨fun x => P (f_G x), ?_, fun x => ⟨?_, ?_⟩⟩
  · have hcomp : (fun x => encNSW (P (f_G x))) = g ∘ (fun x => encGraph (f_G x)) := by
      ext1 x
      by_cases hx : x ∈ L'
      · obtain ⟨hN, hG, _⟩ := (hf_G_corr x).1 hx
        exact (hg_spec (f_G x) hN hG).1
      · obtain ⟨hN, hG, _⟩ := (hf_G_corr x).2 hx
        exact (hg_spec (f_G x) hN hG).1
    rw [hcomp]
    exact polyTimeComputable_comp (fun x => encGraph (f_G x)) g hf_G_poly hg_poly
  · intro hx
    have hyes := (hf_G_corr x).1 hx
    have ⟨hN, hG, _⟩ := hyes
    obtain ⟨_, hT, eA, eB, hu⟩ := hg_spec (f_G x) hN hG
    exact nswYes_of_scaled hb hcmin hab_lt1 hα'₁ hα'₂ (f_G x) (P (f_G x)) hT eA eB hu hyes
  · intro hx
    have hno := (hf_G_corr x).2 hx
    have ⟨hN, hG, _⟩ := hno
    obtain ⟨_, hT, eA, eB, hu⟩ := hg_spec (f_G x) hN hG
    exact nswNo_of_scaled hb hab_lt1 hμ_pos hα'₁ hα'₂ hgap (f_G x) (P (f_G x)) hT eA eB hu hno

end NSWApxHard.Reduction

open NSWApxHard.Reduction

theorem solution (cmin cmax α : ℝ) (hc : cmin < cmax) (hα₁ : 1 / 3 < α) (hα₂ : α < 1 / 2)
    (hCC : Theorem21 cmin cmax) :
    1 < (2 * (1 + α) / 3) ^ (-(((cmax - cmin) / 3) / 2.5)) ∧
      SetCoverThreshold.SetCover.GapNPHard encNSW nswYes
        (nswNo ((2 * (1 + α) / 3) ^ (-(((cmax - cmin) / 3) / 2.5)))) :=
  apx_hardness_of_polyTime_reduce reduction_encode_polyTime cmin cmax α hc hα₁ hα₂ hCC
