-- Prove2me | solution 1 for HochbaumShmoys.Uniform.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:54:36.617613+00:00
-- url     : https://prove2.me/submissions/43a78f3f-12ac-46a9-b572-9b510fd6839b

import Mathlib
import Definitions.Def_HochbaumShmoys_Uniform_LayeredGraph
open HochbaumShmoys.Uniform Finset

lemma g69y_binle (N : ℕ) {m : ℕ} (β : Fin m → ℝ) (hm : 0 < m) (hβ : Antitone β)
    (h0 : β ⟨0, hm⟩ = 1) (t : Fin m) :
    β t ≤ ((N : ℝ)⁻¹) ^ (binInterval N β t) := by
  have hle1 : β t ≤ 1 := h0 ▸ hβ (Fin.mk_le_mk.2 (Nat.zero_le _) : (⟨0, hm⟩ : Fin m) ≤ t)
  unfold binInterval intervalIndex
  rcases Nat.eq_zero_or_pos (sInf {q : ℕ | ((N : ℝ)⁻¹) ^ (q + 1) < β t}) with h | h
  · rw [h]; simpa using hle1
  · have := Nat.notMem_of_lt_sInf (show sInf {q : ℕ | ((N : ℝ)⁻¹) ^ (q + 1) < β t} - 1 <
      sInf {q : ℕ | ((N : ℝ)⁻¹) ^ (q + 1) < β t} by omega)
    simp only [Set.mem_setOf_eq, not_lt] at this
    rwa [Nat.sub_add_cancel h] at this

lemma g69y_cfg (N : ℕ) (hN : 2 ≤ N) {n : ℕ} (k : ℕ) (b : ℝ) (hb : b ≤ ((N : ℝ)⁻¹) ^ k)
    (u v : StateVector N n) (h : IsConfigArc N k b u v) (c : Fin (numClasses N)) :
    (u.L c : ℕ) - (v.L c : ℕ) ≤ N ^ 2 ∧ (u.M c : ℕ) - (v.M c : ℕ) ≤ N ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set δ : ℝ := (N : ℝ)⁻¹ with hδdef
  have hδ : 0 < δ := inv_pos.mpr hN0
  have hNδ : (N : ℝ) * δ = 1 := mul_inv_cancel₀ hN0.ne'
  have hk : δ ^ k = (N : ℝ) ^ 2 * δ ^ (k + 2) := by
    rw [pow_add]; have : (N : ℝ) ^ 2 * δ ^ 2 = 1 := by rw [← mul_pow, hNδ, one_pow]
    linear_combination (-(δ ^ k)) * this
  have hcs1 : ∀ c : Fin (numClasses N), δ ^ (k + 2) ≤ classSize N k c := by
    intro c; unfold classSize
    have : (1 : ℝ) ≤ N + c := by have : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
                                 linarith [(Nat.cast_nonneg c : (0:ℝ) ≤ c)]
    nlinarith [pow_pos hδ (k + 2)]
  have hcs2 : ∀ c : Fin (numClasses N), δ ^ (k + 2) ≤ classSize N (k + 1) c := by
    intro c; unfold classSize
    have e : δ ^ (k + 2) = N * δ ^ (k + 1 + 2) := by
      rw [show k + 1 + 2 = (k + 2) + 1 by ring, pow_succ]; linear_combination (-(δ ^ (k + 2))) * hNδ
    rw [e]
    have : (N : ℝ) ≤ N + c := by linarith [(Nat.cast_nonneg c : (0:ℝ) ≤ c)]
    nlinarith [pow_pos hδ (k + 1 + 2)]
  have hcfg := h.2.2.2.2.1
  have hnn1 : ∀ c ∈ (univ : Finset (Fin (numClasses N))),
      0 ≤ (((u.L c : ℕ) - (v.L c : ℕ) : ℕ) : ℝ) * classSize N k c :=
    fun c _ => mul_nonneg (Nat.cast_nonneg _) (le_trans (pow_pos hδ _).le (hcs1 c))
  have hnn2 : ∀ c ∈ (univ : Finset (Fin (numClasses N))),
      0 ≤ (((u.M c : ℕ) - (v.M c : ℕ) : ℕ) : ℝ) * classSize N (k + 1) c :=
    fun c _ => mul_nonneg (Nat.cast_nonneg _) (le_trans (pow_pos hδ _).le (hcs2 c))
  have hs1 := Finset.sum_nonneg hnn1
  have hs2 := Finset.sum_nonneg hnn2
  have key : ∀ x : ℕ, (x : ℝ) * δ ^ (k + 2) ≤ b → x ≤ N ^ 2 := by
    intro x hx
    have : (x : ℝ) * δ ^ (k + 2) ≤ (N : ℝ) ^ 2 * δ ^ (k + 2) := by rw [← hk]; linarith
    have := le_of_mul_le_mul_right this (pow_pos hδ _)
    exact_mod_cast this
  constructor
  · apply key
    have h1 := Finset.single_le_sum hnn1 (Finset.mem_univ c)
    have h2 : (((u.L c : ℕ) - (v.L c : ℕ) : ℕ) : ℝ) * δ ^ (k + 2) ≤
        (((u.L c : ℕ) - (v.L c : ℕ) : ℕ) : ℝ) * classSize N k c :=
      mul_le_mul_of_nonneg_left (hcs1 c) (Nat.cast_nonneg _)
    unfold configSize at hcfg
    linarith
  · apply key
    have h1 := Finset.single_le_sum hnn2 (Finset.mem_univ c)
    have h2 : (((u.M c : ℕ) - (v.M c : ℕ) : ℕ) : ℝ) * δ ^ (k + 2) ≤
        (((u.M c : ℕ) - (v.M c : ℕ) : ℕ) : ℝ) * classSize N (k + 1) c :=
      mul_le_mul_of_nonneg_left (hcs2 c) (Nat.cast_nonneg _)
    unfold configSize at hcfg
    linarith

noncomputable def g69y_enc (N : ℕ) {m n : ℕ} (u : StateVector N n) :
    Node m N n → Bool × (Fin (numClasses N) → Fin (N ^ 2 + 1)) ×
      (Fin (numClasses N) → Fin (N ^ 2 + 1))
  | .pre _ v => (true, fun c => ⟨min ((u.L c : ℕ) - v.L c) (N ^ 2), Nat.lt_succ_of_le (min_le_right _ _)⟩,
      fun c => ⟨min ((u.M c : ℕ) - v.M c) (N ^ 2), Nat.lt_succ_of_le (min_le_right _ _)⟩)
  | .fin _ v => (false, fun c => ⟨min ((u.L c : ℕ) - v.L c) (N ^ 2), Nat.lt_succ_of_le (min_le_right _ _)⟩,
      fun c => ⟨min ((u.M c : ℕ) - v.M c) (N ^ 2), Nat.lt_succ_of_le (min_le_right _ _)⟩)
  | .success => (true, fun _ => 0, fun _ => 0)

lemma g69y_sv_eq (N : ℕ) (hN : 2 ≤ N) {n : ℕ} (k : ℕ) (b : ℝ) (hb : b ≤ ((N : ℝ)⁻¹) ^ k)
    (u v w : StateVector N n) (hv : IsConfigArc N k b u v) (hw : IsConfigArc N k b u w)
    (hL : ∀ c, min ((u.L c : ℕ) - v.L c) (N ^ 2) = min ((u.L c : ℕ) - w.L c) (N ^ 2))
    (hM : ∀ c, min ((u.M c : ℕ) - v.M c) (N ^ 2) = min ((u.M c : ℕ) - w.M c) (N ^ 2)) :
    v = w := by
  have eL : v.L = w.L := funext fun c => by
    have b1 := (g69y_cfg N hN k b hb u v hv c).1
    have b2 := (g69y_cfg N hN k b hb u w hw c).1
    have := hL c; rw [min_eq_left b1, min_eq_left b2] at this
    have h1 := hv.1 c; have h2 := hw.1 c
    exact Fin.ext (by omega)
  have eM : v.M = w.M := funext fun c => by
    have b1 := (g69y_cfg N hN k b hb u v hv c).2
    have b2 := (g69y_cfg N hN k b hb u w hw c).2
    have := hM c; rw [min_eq_left b1, min_eq_left b2] at this
    have h1 := hv.2.1 c; have h2 := hw.2.1 c
    exact Fin.ext (by omega)
  have eC : configSize N k u v = configSize N k u w := by unfold configSize; rw [eL, eM]
  have e1 : v.V₁ = w.V₁ := hv.2.2.1.trans hw.2.2.1.symm
  have e2 : v.V₂ = w.V₂ := hv.2.2.2.1.trans hw.2.2.2.1.symm
  have e3 : v.V = w.V := by rw [hv.2.2.2.2.2, hw.2.2.2.2.2, eC]
  cases v; cases w
  simp only [StateVector.mk.injEq]
  exact ⟨eL, eM, e1, e2, e3⟩

lemma g69y_deg_pre (N : ℕ) (hN : 2 ≤ N) {m n : ℕ} (β : Fin m → ℝ) (π : Fin n → ℝ) (hm : 0 < m)
    (hβ : Antitone β) (h0 : β ⟨0, hm⟩ = 1) (t : Fin m) (u : StateVector N n) :
    Nat.card {w : Node m N n // Arc N β π (.pre t u) w} ≤ 2 * (N ^ 2 + 1) ^ (2 * numClasses N) := by
  have hb := g69y_binle N β hm hβ h0 t
  let f : {w : Node m N n // Arc N β π (.pre t u) w} → Bool × (Fin (numClasses N) → Fin (N ^ 2 + 1)) ×
      (Fin (numClasses N) → Fin (N ^ 2 + 1)) := fun w => g69y_enc N u w.1
  have hf : Function.Injective f := by
    rintro ⟨w1, h1⟩ ⟨w2, h2⟩ heq
    simp only [f] at heq
    cases w1 with
    | pre t1 v1 =>
      cases w2 with
      | pre t2 v2 =>
        simp only [g69y_enc, Prod.mk.injEq, true_and] at heq
        have ht : t1 = t2 := Fin.ext (h1.1.trans h2.1.symm)
        subst ht
        have := g69y_sv_eq N hN _ _ hb u v1 v2 h1.2.2.2 h2.2.2.2
          (fun c => congrArg Fin.val (congrFun heq.1 c)) (fun c => congrArg Fin.val (congrFun heq.2 c))
        subst this; rfl
      | fin t2 v2 => simp [g69y_enc] at heq
      | success => exact absurd h2 (by simp [Arc])
    | fin t1 v1 =>
      cases w2 with
      | pre t2 v2 => simp [g69y_enc] at heq
      | fin t2 v2 =>
        simp only [g69y_enc, Prod.mk.injEq, true_and] at heq
        have ht : t1 = t2 := h1.1.trans h2.1.symm
        subst ht
        have := g69y_sv_eq N hN _ _ hb u v1 v2 h1.2.2.2 h2.2.2.2
          (fun c => congrArg Fin.val (congrFun heq.1 c)) (fun c => congrArg Fin.val (congrFun heq.2 c))
        subst this; rfl
      | success => exact absurd h2 (by simp [Arc])
    | success => exact absurd h1 (by simp [Arc])
  have := Nat.card_le_card_of_injective f hf
  simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_bool, Fintype.card_fun,
    Fintype.card_fin] at this
  calc _ ≤ _ := this
    _ = _ := by ring

lemma g69y_deg_fin (N : ℕ) {m n : ℕ} (β : Fin m → ℝ) (π : Fin n → ℝ) (t : Fin m) (u : StateVector N n) :
    Nat.card {w : Node m N n // Arc N β π (.fin t u) w} ≤ 2 := by
  let f : {w : Node m N n // Arc N β π (.fin t u) w} → Bool := fun w =>
    match w.1 with
    | .success => true
    | _ => false
  have hf : Function.Injective f := by
    rintro ⟨w1, h1⟩ ⟨w2, h2⟩ heq
    cases w1 with
    | pre t1 v1 =>
      cases w2 with
      | pre t2 v2 =>
        have ht : t1 = t2 := Fin.ext (h1.1.trans h2.1.symm)
        subst ht
        have := Option.some.inj (h1.2.2.symm.trans h2.2.2)
        subst this; rfl
      | fin t2 v2 => exact absurd h2 (by simp [Arc])
      | success => simp [f] at heq
    | fin t1 v1 => exact absurd h1 (by simp [Arc])
    | success =>
      cases w2 with
      | pre t2 v2 => simp [f] at heq
      | fin t2 v2 => exact absurd h2 (by simp [Arc])
      | success => rfl
  have := Nat.card_le_card_of_injective f hf
  simpa using this

lemma g69y_deg_succ (N : ℕ) {m n : ℕ} (β : Fin m → ℝ) (π : Fin n → ℝ) :
    Nat.card {w : Node m N n // Arc N β π .success w} = 0 := by
  haveI : IsEmpty {w : Node m N n // Arc N β π .success w} :=
    ⟨fun ⟨w, h⟩ => by cases w <;> exact absurd h (by simp [Arc])⟩
  exact Nat.card_of_isEmpty

lemma g69y_deg (N : ℕ) (hN : 2 ≤ N) {m n : ℕ} (β : Fin m → ℝ) (π : Fin n → ℝ) (hm : 0 < m)
    (hβ : Antitone β) (h0 : β ⟨0, hm⟩ = 1) (v : Node m N n) :
    Nat.card {w : Node m N n // Arc N β π v w} ≤ 2 * (N ^ 2 + 1) ^ (2 * numClasses N) := by
  have h1 : 1 ≤ (N ^ 2 + 1) ^ (2 * numClasses N) := Nat.one_le_pow _ _ (by omega)
  cases v with
  | pre t u => exact g69y_deg_pre N hN β π hm hβ h0 t u
  | fin t u => have := g69y_deg_fin N β π t u; omega
  | success => rw [g69y_deg_succ]; omega

lemma g69y_e (a : ℕ) (ha : 1 ≤ a) : (a + 1) ^ (2 * a) ≤ 8 * a ^ (2 * a) := by
  have haR : (0:ℝ) < a := by exact_mod_cast ha
  have h1 : ((a:ℝ) + 1) = a * (1 + 1 / a) := by field_simp
  have h2 : (1 + 1 / (a:ℝ)) ^ (2 * a) ≤ Real.exp 2 := by
    calc (1 + 1 / (a:ℝ)) ^ (2 * a) ≤ (Real.exp (1 / a)) ^ (2 * a) :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (1 / (a:ℝ))]) _
      _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
  have h3 : Real.exp 2 < 8 := by
    have h4 := Real.exp_one_lt_d9
    have h5 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h5]; nlinarith [Real.exp_pos 1]
  have : ((a + 1 : ℕ) : ℝ) ^ (2 * a) ≤ ((8 * a ^ (2 * a) : ℕ) : ℝ) := by
    push_cast; rw [h1, mul_pow]
    have : (0:ℝ) ≤ (a:ℝ) ^ (2 * a) := by positivity
    nlinarith
  exact_mod_cast this

lemma g69y_num (N : ℕ) (hN : 2 ≤ N) :
    2 * (N ^ 2 + 1) ^ (2 * numClasses N) ≤ 16 * (N ^ 2) ^ (2 * N ^ 2) := by
  have hK : 2 * numClasses N ≤ 2 * N ^ 2 := by
    unfold numClasses
    have : N ≤ N ^ 2 := by nlinarith
    omega
  have h1 : (N ^ 2 + 1) ^ (2 * numClasses N) ≤ (N ^ 2 + 1) ^ (2 * N ^ 2) :=
    Nat.pow_le_pow_right (by omega) hK
  have h2 := g69y_e (N ^ 2) (Nat.one_le_pow _ _ (by omega))
  omega


def g69g_nodeEnc {m N n : ℕ} : Node m N n → Option (Bool × Fin m × StateVector N n)
  | .pre t u => some (true, t, u)
  | .fin t u => some (false, t, u)
  | .success => none

theorem g69g_nodeEnc_inj {m N n : ℕ} : Function.Injective (@g69g_nodeEnc m N n) := by
  intro a b h
  cases a <;> cases b <;> simp_all [g69g_nodeEnc]

def g69g_svEnc {N n : ℕ} (s : StateVector N n) :
    (Fin (numClasses N) → Fin (n + 1)) × (Fin (numClasses N) → Fin (n + 1)) ×
      Fin (slackCap N n + 1) × Fin (slackCap N n + 1) × Fin (slackCap N n + 1) :=
  (s.L, s.M, s.V₁, s.V₂, s.V)

theorem g69g_svEnc_inj {N n : ℕ} : Function.Injective (@g69g_svEnc N n) := by
  intro a b h
  cases a; cases b; simp_all [g69g_svEnc]

theorem g69g_card_node (m N n : ℕ) :
    Fintype.card (Node m N n) ≤ 2 * m * ((n + 1) ^ (2 * numClasses N) *
      (slackCap N n + 1) ^ 3) + 1 := by
  have h1 := Fintype.card_le_of_injective _ (@g69g_nodeEnc_inj m N n)
  have h2 := Fintype.card_le_of_injective _ (@g69g_svEnc_inj N n)
  simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin,
    Fintype.card_fun] at h1 h2
  calc Fintype.card (Node m N n) ≤ 2 * (m * Fintype.card (StateVector N n)) + 1 := h1
    _ ≤ 2 * (m * ((n + 1) ^ numClasses N * ((n + 1) ^ numClasses N *
        ((slackCap N n + 1) * ((slackCap N n + 1) * (slackCap N n + 1)))))) + 1 := by
        gcongr
    _ = _ := by ring


lemma g69y_nodes (N : ℕ) (hN : 2 ≤ N) (m n : ℕ) (hm : 0 < m) (β : Fin m → ℝ) (π : Fin n → ℝ) :
    nodeCount N β π ≤ 9 * (2 * m) * (n + 1) ^ (2 * N ^ 2 + 3) * N ^ 6 := by
  have hc : nodeCount N β π ≤ Fintype.card (Node m N n) := by
    unfold nodeCount
    exact (Finite.card_subtype_le _).trans Nat.card_eq_fintype_card.le
  refine hc.trans ((g69g_card_node m N n).trans ?_)
  have hK : 2 * numClasses N ≤ 2 * N ^ 2 := by
    unfold numClasses
    have : N ≤ N ^ 2 := by nlinarith
    omega
  have hN1 : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hS : slackCap N n + 1 ≤ 2 * (n + 1) * N ^ 2 := by
    unfold slackCap; nlinarith
  have hp1 : (n + 1) ^ (2 * numClasses N) ≤ (n + 1) ^ (2 * N ^ 2) :=
    Nat.pow_le_pow_right (by omega) hK
  have hp2 : (slackCap N n + 1) ^ 3 ≤ (2 * (n + 1) * N ^ 2) ^ 3 := Nat.pow_le_pow_left hS 3
  have hpos : 1 ≤ (n + 1) ^ (2 * N ^ 2 + 3) * N ^ 6 :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc 2 * m * ((n + 1) ^ (2 * numClasses N) * (slackCap N n + 1) ^ 3) + 1
      ≤ 2 * m * ((n + 1) ^ (2 * N ^ 2) * (2 * (n + 1) * N ^ 2) ^ 3) + 1 := by gcongr
    _ = 16 * m * ((n + 1) ^ (2 * N ^ 2 + 3) * N ^ 6) + 1 := by ring
    _ ≤ 9 * (2 * m) * (n + 1) ^ (2 * N ^ 2 + 3) * N ^ 6 := by
        have : 1 ≤ m * ((n + 1) ^ (2 * N ^ 2 + 3) * N ^ 6) := Nat.one_le_iff_ne_zero.mpr (by positivity)
        nlinarith

lemma g69y_src (N : ℕ) {m n : ℕ} (β : Fin m → ℝ) (π : Fin n → ℝ) (v w : Node m N n)
    (h : Arc N β π v w) : IsGraphNode N β π v := by
  cases v with
  | pre t u =>
    cases w with
    | pre t' v' => exact h.2.2.1
    | fin t' v' => exact h.2.2.1
    | success => exact h.elim
  | fin t u =>
    cases w with
    | pre t' v' => exact h.2.1
    | fin t' v' => exact h.elim
    | success => exact fun h' => absurd h' (by have := h.1; omega)
  | success => cases w <;> exact h.elim

lemma g69y_arcs (N : ℕ) (hN : 2 ≤ N) {m n : ℕ} (β : Fin m → ℝ) (π : Fin n → ℝ) (hm : 0 < m)
    (hβ : Antitone β) (h0 : β ⟨0, hm⟩ = 1) :
    arcCount N β π ≤ 16 * (N ^ 2) ^ (2 * N ^ 2) * nodeCount N β π := by
  classical
  have hD : ∀ v, Nat.card {w // Arc N β π v w} ≤ 16 * (N ^ 2) ^ (2 * N ^ 2) := fun v =>
    (g69y_deg N hN β π hm hβ h0 v).trans (g69y_num N hN)
  unfold arcCount nodeCount
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun a b => Arc N β π a b)), Nat.card_sigma,
    Nat.card_eq_fintype_card (α := {v // IsGraphNode N β π v}), Fintype.card_subtype]
  calc ∑ a, Nat.card {w // Arc N β π a w}
      ≤ ∑ a, if IsGraphNode N β π a then 16 * (N ^ 2) ^ (2 * N ^ 2) else 0 := by
        apply Finset.sum_le_sum; intro a _
        split_ifs with hg
        · exact hD a
        · have : IsEmpty {w // Arc N β π a w} := ⟨fun ⟨w, h⟩ => hg (g69y_src N β π a w h)⟩
          simp
    _ = _ := by rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_comm]

open HochbaumShmoys.Uniform
theorem solution : ∃ C : ℕ, ∀ (N : ℕ), 2 ≤ N → ∀ (m n : ℕ) (hm : 0 < m)
    (β : Fin m → ℝ) (π : Fin n → ℝ),
    Antitone β → β ⟨0, hm⟩ = 1 → (∀ t, 0 < β t) → (∀ j, 0 < π j ∧ π j ≤ 1) →
    ∀ v : Node m N n,
      Nat.card {w : Node m N n // Arc N β π v w} ≤ C * (N ^ 2) ^ (2 * N ^ 2) := by
  refine ⟨16, fun N hN m n hm β π hβ h0 _ _ v => ?_⟩
  exact (g69y_deg N hN β π hm hβ h0 v).trans (g69y_num N hN)


