-- Prove2me | solution 1 for GrigorchukPak.superpolynomial_and_exp_rpow_le_card_wordBall
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-25T14:26:27.545386+00:00
-- url     : https://prove2.me/submissions/5f45f874-7938-400e-8a4d-20a8f441c4ab

import Mathlib
import Definitions.Def_Garrido_Grigorchuk


/-!
# Grigorchuk–Pak, Lemma 2.1 (Lower Bound Lemma)

Following the Appendix proof: pass to `π(n) = log f(n)`, turn `f(n)^m ≤ C f(Kn)` into the
linear recursion `π(Kn) ≥ m π(n) - log C`, iterate it along `n₀, K n₀, K² n₀, …`, and
interpolate between consecutive powers of `K`.  The additive constant is absorbed by the
shift `a(n) = π(n) - L` with `L = log C / (m - 1)`, which satisfies `a(Kn) ≥ m a(n)` exactly.
-/

namespace GrigorchukPak

theorem exists_exp_rpow_le_of_pow_le (f : ℕ → ℝ) (hmono : Monotone f) (hpos : ∀ n, 1 ≤ f n)
    (htop : Filter.Tendsto f Filter.atTop Filter.atTop)
    (m : ℕ) (hm : 1 < m) (C : ℝ) (hC : 0 < C) (K : ℕ) (hK : 0 < K)
    (hpow : ∀ n : ℕ, 0 < n → f n ^ m ≤ C * f (K * n)) :
    ∃ α : ℝ, 0 < α ∧ ∃ C' : ℝ, 0 < C' ∧ ∃ K' : ℕ, 0 < K' ∧ ∀ n : ℕ, 0 < n →
      Real.exp ((n : ℝ) ^ α) ≤ C' * f (K' * n) := by
  have hfpos : ∀ n, 0 < f n := fun n => lt_of_lt_of_le one_pos (hpos n)
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (1 : ℝ) < m := by exact_mod_cast hm
    linarith
  set L : ℝ := Real.log C / ((m : ℝ) - 1) with hL
  have hLC : ((m : ℝ) - 1) * L = Real.log C := by
    rw [hL]; field_simp
  -- shifted logarithm
  set a : ℕ → ℝ := fun n => Real.log (f n) - L with ha
  have key : ∀ n : ℕ, 0 < n → (m : ℝ) * a n ≤ a (K * n) := by
    intro n hn
    have h1 := Real.log_le_log (pow_pos (hfpos n) m) (hpow n hn)
    rw [Real.log_pow, Real.log_mul hC.ne' (hfpos _).ne'] at h1
    simp only [ha]
    nlinarith [hLC]
  -- a point where `a ≥ 1`
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (htop.eventually_ge_atTop (Real.exp (1 + L)))
  set n₀ := N + 1 with hn₀
  have hn₀pos : 0 < n₀ := Nat.succ_pos N
  have ha₀ : 1 ≤ a n₀ := by
    have h := hN n₀ (Nat.le_succ N)
    have := Real.log_le_log (Real.exp_pos _) h
    rw [Real.log_exp] at this
    simp only [ha]; linarith
  -- K = 1 is impossible
  have hK2 : 2 ≤ K := by
    by_contra hlt
    have hK1 : K = 1 := by omega
    have h := key n₀ hn₀pos
    rw [hK1, one_mul] at h
    have : (1 : ℝ) < m := by exact_mod_cast hm
    nlinarith
  -- iteration
  have iter : ∀ j : ℕ, (m : ℝ) ^ j ≤ a (K ^ j * n₀) := by
    intro j
    induction j with
    | zero => simpa using ha₀
    | succ j ih =>
      have hp : 0 < K ^ j * n₀ := Nat.mul_pos (pow_pos hK j) hn₀pos
      have h := key _ hp
      have heq : K ^ (j + 1) * n₀ = K * (K ^ j * n₀) := by ring
      rw [heq, pow_succ]
      have hm0 : (0 : ℝ) ≤ m := by positivity
      calc (m : ℝ) ^ j * m = m * m ^ j := by ring
        _ ≤ m * a (K ^ j * n₀) := mul_le_mul_of_nonneg_left ih hm0
        _ ≤ _ := h
  have hKr : (1 : ℝ) < K := by exact_mod_cast hK2
  have hlogK : 0 < Real.log K := Real.log_pos hKr
  have hlogm : 0 < Real.log m := Real.log_pos (by exact_mod_cast hm)
  refine ⟨Real.log m / Real.log K, div_pos hlogm hlogK, Real.exp (-L), Real.exp_pos _,
    K * n₀, Nat.mul_pos hK hn₀pos, ?_⟩
  intro n hn
  set j := Nat.log K n + 1 with hj
  have hnlt : n < K ^ j := Nat.lt_pow_succ_log_self (by omega) n
  have hKj : K ^ j ≤ K * n := by
    rw [hj, pow_succ, mul_comm]
    exact Nat.mul_le_mul_left K (Nat.pow_log_le_self K hn.ne')
  -- exponent bound
  have hexp : (n : ℝ) ^ (Real.log m / Real.log K) ≤ (m : ℝ) ^ j := by
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.rpow_def_of_pos hnr]
    have hlogn : Real.log n ≤ j * Real.log K := by
      rw [← Real.log_pow]
      exact Real.log_le_log hnr (by exact_mod_cast hnlt.le)
    have : Real.log n * (Real.log m / Real.log K) ≤ j * Real.log m := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ hlogK]
      nlinarith
    calc Real.exp (Real.log n * (Real.log m / Real.log K)) ≤ Real.exp (j * Real.log m) :=
          Real.exp_le_exp.2 this
      _ = (m : ℝ) ^ j := by
          rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast (by omega : 0 < m))]
  have hmono' : f (K ^ j * n₀) ≤ f (K * n₀ * n) := by
    apply hmono
    calc K ^ j * n₀ ≤ K * n * n₀ := Nat.mul_le_mul_right _ hKj
      _ = K * n₀ * n := by ring
  have hit := iter j
  simp only [ha] at hit
  have hf : Real.exp ((m : ℝ) ^ j + L) ≤ f (K * n₀ * n) := by
    calc Real.exp ((m : ℝ) ^ j + L) ≤ Real.exp (Real.log (f (K ^ j * n₀))) :=
          Real.exp_le_exp.2 (by linarith)
      _ = f (K ^ j * n₀) := Real.exp_log (hfpos _)
      _ ≤ _ := hmono'
  calc Real.exp ((n : ℝ) ^ (Real.log m / Real.log K)) ≤ Real.exp ((m : ℝ) ^ j) :=
        Real.exp_le_exp.2 hexp
    _ = Real.exp (-L) * Real.exp ((m : ℝ) ^ j + L) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-L) * f (K * n₀ * n) :=
        mul_le_mul_of_nonneg_left hf (Real.exp_pos _).le

end GrigorchukPak


/-!
# Growth of the Grigorchuk group (Grigorchuk–Pak, §§5–6, Exercises 1.3, 1.5)
-/

namespace GrigorchukPak

open Chou

section Ball
variable {G : Type*} [Group G] (S : Set G)

theorem one_mem_wordBall (k : ℕ) : (1 : G) ∈ wordBall S k :=
  ⟨[], by simp, by simp, by simp⟩

theorem wordBall_mono {k k' : ℕ} (h : k ≤ k') : wordBall S k ⊆ wordBall S k' := by
  rintro g ⟨l, hl, hS, rfl⟩
  exact ⟨l, hl.trans h, hS, rfl⟩

theorem mul_mem_wordBall {x y : G} {a b : ℕ} (hx : x ∈ wordBall S a) (hy : y ∈ wordBall S b) :
    x * y ∈ wordBall S (a + b) := by
  obtain ⟨l, hl, hS, rfl⟩ := hx
  obtain ⟨l', hl', hS', rfl⟩ := hy
  refine ⟨l ++ l', by simp; omega, ?_, by simp⟩
  intro z hz
  rcases List.mem_append.mp hz with h | h
  · exact hS z h
  · exact hS' z h

theorem inv_mem_wordBall {x : G} {a : ℕ} (hx : x ∈ wordBall S a) : x⁻¹ ∈ wordBall S a := by
  obtain ⟨l, hl, hS, rfl⟩ := hx
  refine ⟨(l.map (·⁻¹)).reverse, by simpa using hl, ?_, by simp [List.prod_inv_reverse]⟩
  intro z hz
  simp only [List.mem_reverse, List.mem_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rcases hS w hw with h | h
  · right; simpa using h
  · left; exact h

theorem mem_wordBall_one_of_mem {s : G} (hs : s ∈ S) : s ∈ wordBall S 1 :=
  ⟨[s], by simp, by simp [hs], by simp⟩

/-- `B(k+1) = T₁ · B(k)` where `T₁ = {1} ∪ S ∪ S⁻¹`. -/
theorem mem_wordBall_succ_iff {g : G} {k : ℕ} :
    g ∈ wordBall S (k + 1) ↔ ∃ t : G, (t = 1 ∨ t ∈ S ∨ t⁻¹ ∈ S) ∧ ∃ g' ∈ wordBall S k, g = t * g' := by
  constructor
  · rintro ⟨l, hl, hS, rfl⟩
    cases l with
    | nil => exact ⟨1, Or.inl rfl, 1, one_mem_wordBall S k, by simp⟩
    | cons x l =>
      refine ⟨x, Or.inr (hS x (by simp)), l.prod, ⟨l, by simpa using hl, fun z hz => hS z (by simp [hz]), rfl⟩, by simp⟩
  · rintro ⟨t, ht, g', hg', rfl⟩
    rcases ht with rfl | ht
    · simpa using wordBall_mono S (Nat.le_succ k) hg'
    · have : t ∈ wordBall S 1 := ⟨[t], by simp, by simpa using ht, by simp⟩
      simpa [add_comm] using mul_mem_wordBall S this hg'

theorem wordBall_finite (hS : S.Finite) (k : ℕ) : (wordBall S k).Finite := by
  induction k with
  | zero =>
    apply (Set.finite_singleton (1 : G)).subset
    rintro g ⟨l, hl, -, rfl⟩
    simp at hl; simp [hl]
  | succ k ih =>
    have hT : ({t : G | t = 1 ∨ t ∈ S ∨ t⁻¹ ∈ S}).Finite := by
      have : {t : G | t = 1 ∨ t ∈ S ∨ t⁻¹ ∈ S} = {1} ∪ S ∪ S⁻¹ := by
        ext t; simp [or_assoc]
      rw [this]; exact ((Set.finite_singleton _).union hS).union hS.inv
    apply (hT.image2 (· * ·) ih).subset
    intro g hg
    obtain ⟨t, ht, g', hg', rfl⟩ := (mem_wordBall_succ_iff S).mp hg
    exact ⟨t, ht, g', hg', rfl⟩

theorem exists_mem_wordBall (hgen : Subgroup.closure S = ⊤) (g : G) : ∃ k, g ∈ wordBall S k := by
  have hg : g ∈ Subgroup.closure S := by rw [hgen]; trivial
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact ⟨1, mem_wordBall_one_of_mem S hs⟩
  | one => exact ⟨0, one_mem_wordBall S 0⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, mul_mem_wordBall S ha hb⟩
  | inv x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, inv_mem_wordBall S ha⟩


/-- Every element of a ball of `S` of radius `m` lies in the `S'`-ball of radius `K*m`, if
every element of `S` lies in the `S'`-ball of radius `K`. -/
theorem wordBall_subset_of_forall {S' : Set G} {K : ℕ} (hK : ∀ s ∈ S, s ∈ wordBall S' K)
    (n : ℕ) : wordBall S n ⊆ wordBall S' (K * n) := by
  rintro g ⟨l, hl, hS, rfl⟩
  have key : ∀ l : List G, (∀ x ∈ l, x ∈ S ∨ x⁻¹ ∈ S) → l.prod ∈ wordBall S' (K * l.length) := by
    intro l
    induction l with
    | nil => intro _; simpa using one_mem_wordBall S' 0
    | cons x l ih =>
      intro h
      have hx : x ∈ wordBall S' K := by
        rcases h x (by simp) with h1 | h1
        · exact hK x h1
        · simpa using inv_mem_wordBall S' (hK _ h1)
      have := mul_mem_wordBall S' hx (ih fun z hz => h z (by simp [hz]))
      simpa [List.prod_cons, Nat.mul_succ, add_comm] using this
  exact wordBall_mono S' (Nat.mul_le_mul_left K hl) (key l hS)

end Ball

section Generic
variable {G : Type*} [Group G]

/-- Exercise 1.3 (generator change). -/
theorem exists_wordBall_subset (S S' : Finset G) (hS' : Subgroup.closure (S' : Set G) = ⊤) :
    ∃ K : ℕ, 0 < K ∧ ∀ n : ℕ, wordBall (S : Set G) n ⊆ wordBall (S' : Set G) (K * n) := by
  classical
  choose k hk using exists_mem_wordBall (S' : Set G) hS'
  refine ⟨S.sup k + 1, Nat.succ_pos _, wordBall_subset_of_forall _ fun s hs => ?_⟩
  exact wordBall_mono _ ((Finset.le_sup hs).trans (Nat.le_succ _)) (hk s)

theorem card_wordBall_le_of_subset {S S' : Finset G} {m n : ℕ}
    (h : wordBall (S : Set G) m ⊆ wordBall (S' : Set G) n) :
    (Nat.card (wordBall (S : Set G) m) : ℝ) ≤ Nat.card (wordBall (S' : Set G) n) := by
  exact_mod_cast Nat.card_mono (wordBall_finite _ S'.finite_toSet n) h

/-- Exercise 1.3: `γ_S(n) ≤ γ_{S'}(K n)`. -/
theorem exists_card_wordBall_le (S S' : Finset G) (hS' : Subgroup.closure (S' : Set G) = ⊤) :
    ∃ K : ℕ, 0 < K ∧ ∀ n : ℕ, wordBall (S : Set G) n ⊆ wordBall (S' : Set G) (K * n) ∧
      (Nat.card (wordBall (S : Set G) n) : ℝ) ≤ Nat.card (wordBall (S' : Set G) (K * n)) := by
  obtain ⟨K, hK, h⟩ := exists_wordBall_subset S S' hS'
  exact ⟨K, hK, fun n => ⟨h n, card_wordBall_le_of_subset (h n)⟩⟩

theorem monotone_card_wordBall (S : Finset G) :
    Monotone fun n : ℕ => (Nat.card (wordBall (S : Set G) n) : ℝ) := by
  intro m n h
  show (Nat.card (wordBall (S : Set G) m) : ℝ) ≤ Nat.card (wordBall (S : Set G) n)
  exact_mod_cast Nat.card_mono (wordBall_finite _ S.finite_toSet n) (wordBall_mono _ h)

theorem one_le_card_wordBall (S : Finset G) (n : ℕ) :
    (1 : ℝ) ≤ Nat.card (wordBall (S : Set G) n) := by
  have : Finite (wordBall (S : Set G) n) := (wordBall_finite _ S.finite_toSet n).to_subtype
  have : Nonempty (wordBall (S : Set G) n) := ⟨⟨1, one_mem_wordBall _ n⟩⟩
  exact_mod_cast Nat.card_pos

theorem tendsto_card_wordBall [Infinite G] (S : Finset G)
    (hS : Subgroup.closure (S : Set G) = ⊤) :
    Filter.Tendsto (fun n : ℕ => (Nat.card (wordBall (S : Set G) n) : ℝ))
      Filter.atTop Filter.atTop := by
  classical
  refine (monotone_card_wordBall S).tendsto_atTop_atTop fun b => ?_
  obtain ⟨F, hF⟩ := Infinite.exists_subset_card_eq G (⌈b⌉₊)
  choose k hk using exists_mem_wordBall (S : Set G) hS
  refine ⟨F.sup k, ?_⟩
  have hsub : (F : Set G) ⊆ wordBall (S : Set G) (F.sup k) := fun g hg =>
    wordBall_mono _ (Finset.le_sup hg) (hk g)
  have h1 := Nat.card_mono (wordBall_finite _ S.finite_toSet _) hsub
  rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, hF] at h1
  calc b ≤ ⌈b⌉₊ := Nat.le_ceil b
    _ ≤ _ := by exact_mod_cast h1

end Generic

local notation "Γ" => Garrido.GrigorchukGroup

/-! ## The doubling inequality `γ(n)² ≤ C γ(K n)` (Lemmas 6.2, 6.3, Exercise 1.5) -/

section Doubling

open Garrido

local notation "P" => Equiv.Perm (List Bool)

theorem bta_ext {g h : BinaryTreeAut} (H : ∀ w, (g : P) w = (h : P) w) : g = h :=
  Subtype.ext (Equiv.ext H)

theorem treeSection_apply (g : BinaryTreeAut) (v w : List Bool) :
    ((treeSection g v : BinaryTreeAut) : P) w = ((g : P) (v ++ w)).drop v.length := rfl

theorem treeSection_mul (g h : BinaryTreeAut) (v : List Bool) :
    treeSection (g * h) v = treeSection g ((h : P) v) * treeSection h v := by
  apply bta_ext; intro w
  simp only [treeSection_apply, Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply]
  have e := BinaryTreeAut.append_drop h v w
  rw [h.2.1 v]
  conv_lhs => rw [← e]

theorem gext {g h : Γ} (H : ∀ w, ((g : BinaryTreeAut) : P) w = ((h : BinaryTreeAut) : P) w) :
    g = h :=
  Subtype.ext (Subtype.ext (Equiv.ext H))

@[simp] theorem a_apply (w : List Bool) :
    (((GrigorchukGroup.a : Γ) : BinaryTreeAut) : P) w = grigAFun w := rfl
@[simp] theorem b_apply (w : List Bool) :
    (((GrigorchukGroup.b : Γ) : BinaryTreeAut) : P) w = grigBFun w := rfl
@[simp] theorem c_apply (w : List Bool) :
    (((GrigorchukGroup.c : Γ) : BinaryTreeAut) : P) w = grigCFun w := rfl
@[simp] theorem d_apply (w : List Bool) :
    (((GrigorchukGroup.d : Γ) : BinaryTreeAut) : P) w = grigDFun w := rfl
@[simp] theorem mul_apply (g h : Γ) (w : List Bool) :
    (((g * h : Γ) : BinaryTreeAut) : P) w =
      ((g : BinaryTreeAut) : P) (((h : BinaryTreeAut) : P) w) := rfl
@[simp] theorem one_apply (w : List Bool) : (((1 : Γ) : BinaryTreeAut) : P) w = w := rfl

/-- The four generators as letters. -/
inductive Ltr | a | b | c | d

/-- The generator named by a letter. -/
def Ltr.g : Ltr → Γ
  | .a => GrigorchukGroup.a
  | .b => GrigorchukGroup.b
  | .c => GrigorchukGroup.c
  | .d => GrigorchukGroup.d

/-- Evaluation of a word. -/
def ev (u : List Ltr) : Γ := (u.map Ltr.g).prod

@[simp] theorem ev_nil : ev [] = 1 := rfl
@[simp] theorem ev_cons (x : Ltr) (u : List Ltr) : ev (x :: u) = x.g * ev u := by
  simp [ev]
@[simp] theorem ev_append (u v : List Ltr) : ev (u ++ v) = ev u * ev v := by
  simp [ev]

theorem Ltr.g_mul_self (x : Ltr) : x.g * x.g = 1 := by
  cases x <;> exact gext fun w => by
    simp [Ltr.g, grigAFun_involutive w, (grigBCD_involutive w).1, (grigBCD_involutive w).2.1,
      (grigBCD_involutive w).2.2]

theorem Ltr.g_inv (x : Ltr) : x.g⁻¹ = x.g := inv_eq_of_mul_eq_one_right x.g_mul_self

theorem Ltr.g_mem (x : Ltr) : x.g ∈ GrigorchukGroup.generators := by
  cases x <;> simp [Ltr.g, GrigorchukGroup.generators]

theorem ev_mem_wordBall (u : List Ltr) :
    ev u ∈ wordBall GrigorchukGroup.generators u.length :=
  ⟨u.map Ltr.g, by simp, fun z hz => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hz; exact Or.inl x.g_mem, rfl⟩

theorem exists_ev {g : Γ} {n : ℕ} (hg : g ∈ wordBall GrigorchukGroup.generators n) :
    ∃ u : List Ltr, u.length ≤ n ∧ ev u = g := by
  obtain ⟨l, hl, hS, rfl⟩ := hg
  have hlet : ∀ x : Γ, x ∈ GrigorchukGroup.generators → ∃ y : Ltr, y.g = x := by
    rintro x (rfl | rfl | rfl | rfl)
    exacts [⟨.a, rfl⟩, ⟨.b, rfl⟩, ⟨.c, rfl⟩, ⟨.d, rfl⟩]
  have key : ∀ l : List Γ, (∀ x ∈ l, x ∈ GrigorchukGroup.generators ∨
      x⁻¹ ∈ GrigorchukGroup.generators) → ∃ u : List Ltr, u.length = l.length ∧ ev u = l.prod := by
    intro l
    induction l with
    | nil => intro _; exact ⟨[], rfl, rfl⟩
    | cons x l ih =>
      intro h
      obtain ⟨u, hu, he⟩ := ih fun z hz => h z (by simp [hz])
      have : ∃ y : Ltr, y.g = x := by
        rcases h x (by simp) with h1 | h1
        · exact hlet x h1
        · obtain ⟨y, hy⟩ := hlet _ h1
          exact ⟨y, by rw [← y.g_inv, hy, inv_inv]⟩
      obtain ⟨y, rfl⟩ := this
      exact ⟨y :: u, by simp [hu], by simp [he]⟩
  obtain ⟨u, hu, he⟩ := key l hS
  exact ⟨u, hu ▸ hl, he⟩

/-- The substitution `σ`: `a ↦ aca, b ↦ d, c ↦ b, d ↦ c`. -/
def σl : Ltr → List Ltr
  | .a => [.a, .c, .a]
  | .b => [.d]
  | .c => [.b]
  | .d => [.c]

/-- The companion `θ`: `a ↦ d, b ↦ 1, c ↦ a, d ↦ a`, so that `σ(g) = (θ(g), g)`. -/
def θl : Ltr → List Ltr
  | .a => [.d]
  | .b => []
  | .c => [.a]
  | .d => [.a]

/-- Fixing the first level. -/
def Fix1 (g : BinaryTreeAut) : Prop := ∀ p : Bool, (g : P) [p] = [p]

theorem Fix1.mul {g h : BinaryTreeAut} (hg : Fix1 g) (hh : Fix1 h) : Fix1 (g * h) := by
  intro p
  simp only [Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply, hh p, hg p]

theorem Fix1.sec_mul {g h : BinaryTreeAut} (hh : Fix1 h) (p : Bool) :
    treeSection (g * h) [p] = treeSection g [p] * treeSection h [p] := by
  rw [treeSection_mul, hh p]

theorem σl_spec (x : Ltr) :
    Fix1 (ev (σl x) : BinaryTreeAut) ∧
      treeSection (ev (σl x) : BinaryTreeAut) [true] = (x.g : BinaryTreeAut) ∧
      treeSection (ev (σl x) : BinaryTreeAut) [false] = (ev (θl x) : BinaryTreeAut) := by
  refine ⟨fun p => ?_, bta_ext fun w => ?_, bta_ext fun w => ?_⟩ <;>
    cases x <;> (try cases p) <;>
    simp [σl, θl, Ltr.g, treeSection_apply, grigAFun, grigBFun, grigCFun, grigDFun]

theorem σw_spec (u : List Ltr) :
    Fix1 (ev (u.flatMap σl) : BinaryTreeAut) ∧
      treeSection (ev (u.flatMap σl) : BinaryTreeAut) [true] = (ev u : BinaryTreeAut) ∧
      treeSection (ev (u.flatMap σl) : BinaryTreeAut) [false] =
        (ev (u.flatMap θl) : BinaryTreeAut) := by
  induction u with
  | nil =>
    refine ⟨fun p => rfl, bta_ext fun w => ?_, bta_ext fun w => ?_⟩ <;>
      simp [treeSection_apply]
  | cons x u ih =>
    obtain ⟨h1, h2, h3⟩ := σl_spec x
    simp only [List.flatMap_cons, ev_append, ev_cons, Subgroup.coe_mul]
    exact ⟨h1.mul ih.1, by rw [ih.1.sec_mul, h2, ih.2.1], by rw [ih.1.sec_mul, h3, ih.2.2]⟩

theorem σw_length (u : List Ltr) : (u.flatMap σl).length ≤ 3 * u.length := by
  induction u with
  | nil => simp
  | cons x u ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    cases x <;> simp only [σl, List.length_cons, List.length_nil] <;> omega

theorem conj_a_spec {h : BinaryTreeAut} (hh : Fix1 h) :
    Fix1 ((GrigorchukGroup.a : BinaryTreeAut) * h * GrigorchukGroup.a) ∧
      ∀ p, treeSection ((GrigorchukGroup.a : BinaryTreeAut) * h * GrigorchukGroup.a) [p] =
        treeSection h [!p] := by
  have key : ∀ (x : Bool) (w : List Bool), (h : P) (x :: w) = x :: (((h : P) (x :: w)).drop 1) := by
    intro x w
    have e := BinaryTreeAut.append_drop h [x] w
    rw [hh x] at e
    exact e.symm
  refine ⟨fun p => ?_, fun p => bta_ext fun w => ?_⟩
  · change grigAFun ((h : P) (grigAFun [p])) = [p]
    rw [show grigAFun [p] = [!p] from rfl, hh]; simp [grigAFun]
  · rw [treeSection_apply, treeSection_apply]
    change (grigAFun ((h : P) (grigAFun (p :: w)))).drop 1 = _
    rw [show grigAFun (p :: w) = (!p) :: w from rfl, key]
    simp [grigAFun]

/-- The dihedral group `⟨a, d⟩` of order 8. -/
def Dih : Set Γ :=
  open GrigorchukGroup in {1, a, d, a * d, d * a, a * d * a, d * a * d, a * d * a * d}

theorem Dih_finite : Dih.Finite := by
  simp only [Dih]; exact Set.toFinite _

theorem ev_θw_mem (u : List Ltr) : ev (u.flatMap θl) ∈ Dih := by
  open GrigorchukGroup in
  have aa : ∀ x : Γ, a * (a * x) = x := fun x => by
    rw [← mul_assoc, show a * a = 1 from Ltr.g_mul_self .a, one_mul]
  have dd : ∀ x : Γ, d * (d * x) = x := fun x => by
    rw [← mul_assoc, show d * d = 1 from Ltr.g_mul_self .d, one_mul]
  have dd' : d * d = 1 := Ltr.g_mul_self .d
  have aa' : a * a = 1 := Ltr.g_mul_self .a
  have rel : d * (a * (d * a)) = a * (d * (a * d)) := gext fun w => by
    rcases w with _ | ⟨_ | _, w⟩ <;> simp [grigAFun, grigDFun]
  have rel' : ∀ x : Γ, d * (a * (d * (a * x))) = a * (d * (a * (d * x))) := fun x => by
    simp only [← mul_assoc] at rel ⊢; rw [rel]
  have closed : ∀ g ∈ Dih, a * g ∈ Dih ∧ d * g ∈ Dih := by
    intro g hg
    simp only [Dih, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Dih, Set.mem_insert_iff, Set.mem_singleton_iff, mul_assoc, aa, dd, aa', dd', rel,
        rel', mul_one] <;> simp
  induction u with
  | nil => simp [Dih]
  | cons x u ih =>
    simp only [List.flatMap_cons, ev_append]
    cases x <;> simp only [θl, ev_cons, ev_nil, mul_one, one_mul, Ltr.g] <;>
      first | exact ih | exact (closed _ ih).1 | exact (closed _ ih).2

theorem closure_generators : Subgroup.closure GrigorchukGroup.generators = ⊤ := by
  have h : GrigorchukGroup.generators =
      ((↑) : GrigorchukGroup → BinaryTreeAut) ⁻¹' {grigA, grigB, grigC, grigD} := by
    ext x
    simp only [GrigorchukGroup.generators, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_preimage]
    constructor
    · rintro (rfl | rfl | rfl | rfl) <;> simp [GrigorchukGroup.a, GrigorchukGroup.b,
        GrigorchukGroup.c, GrigorchukGroup.d]
    · rintro (h | h | h | h) <;> [left; (right; left); (right; right; left); (right; right; right)]
        <;> exact Subtype.ext h
  rw [h]
  exact Subgroup.closure_closure_coe_preimage

/-- `Γ` is infinite: `x ↦ σ(x)` embeds `Γ` into `St(1) ⊆ Γ \ {a}`. -/
theorem infinite_grigorchukGroup : Infinite Γ := by
  classical
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  have hw : ∀ x : Γ, ∃ u : List Ltr, ev u = x := fun x => by
    obtain ⟨k, hk⟩ := exists_mem_wordBall _ closure_generators x
    obtain ⟨u, -, hu⟩ := exists_ev hk
    exact ⟨u, hu⟩
  choose u hu using hw
  let f : Γ → Γ := fun x => ev ((u x).flatMap σl)
  have hinj : Function.Injective f := by
    intro x y h
    have e := congrArg (fun g : Γ => treeSection (g : BinaryTreeAut) [true]) h
    simp only [f, (σw_spec (u x)).2.1, (σw_spec (u y)).2.1, hu] at e
    exact Subtype.ext e
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hinj) GrigorchukGroup.a
  have h1 := (σw_spec (u x)).1 false
  simp only [f] at hx
  rw [hx] at h1
  simp [grigAFun] at h1

/-- Lemmas 6.2–6.3 with Exercise 1.5 for `{a, b, c, d}`: `γ(n)² ≤ |D|² γ(6n + 2)`. -/
theorem card_wordBall_sq_le_generators (n : ℕ) :
    (Nat.card (wordBall GrigorchukGroup.generators n) : ℝ) ^ 2 ≤
      (Nat.card Dih : ℝ) ^ 2 * Nat.card (wordBall GrigorchukGroup.generators (6 * n + 2)) := by
  set B := wordBall GrigorchukGroup.generators
  have hfin : ∀ m, (B m).Finite := wordBall_finite _ (by
    simp only [GrigorchukGroup.generators]; exact Set.toFinite _)
  choose u hul hue using fun x : B n => exists_ev x.2
  have hD : Finite Dih := Dih_finite.to_subtype
  have hB : Finite (B (6 * n + 2)) := (hfin _).to_subtype
  let F : B n × B n → B (6 * n + 2) × Dih × Dih := fun xy =>
    (⟨GrigorchukGroup.a * ev ((u xy.1).flatMap σl) * GrigorchukGroup.a *
        ev ((u xy.2).flatMap σl), by
      have h1 := ev_mem_wordBall ((u xy.1).flatMap σl)
      have h2 := ev_mem_wordBall ((u xy.2).flatMap σl)
      have ha := ev_mem_wordBall [Ltr.a]
      have := mul_mem_wordBall _ (mul_mem_wordBall _ (mul_mem_wordBall _ ha h1) ha) h2
      refine wordBall_mono _ ?_ this
      have := σw_length (u xy.1); have := σw_length (u xy.2)
      have := hul xy.1; have := hul xy.2
      simp only [List.length_singleton]; omega⟩,
      ⟨_, ev_θw_mem (u xy.1)⟩, ⟨_, ev_θw_mem (u xy.2)⟩)
  have hsec : ∀ xy : B n × B n,
      treeSection ((F xy).1 : BinaryTreeAut) [false] =
          ((xy.1 : Γ) : BinaryTreeAut) * (((F xy).2.2 : Γ) : BinaryTreeAut) ∧
        treeSection ((F xy).1 : BinaryTreeAut) [true] =
          (((F xy).2.1 : Γ) : BinaryTreeAut) * ((xy.2 : Γ) : BinaryTreeAut) := by
    intro xy
    obtain ⟨f1, t1, s1⟩ := σw_spec (u xy.1)
    obtain ⟨f2, t2, s2⟩ := σw_spec (u xy.2)
    obtain ⟨cf, cs⟩ := conj_a_spec f1
    simp only [F, Subgroup.coe_mul]
    rw [f2.sec_mul, f2.sec_mul, cs, cs, t2, s2]
    simp [t1, s1, hue]
  have hinj : Function.Injective F := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    obtain ⟨e1, e2⟩ := hsec (x, y)
    obtain ⟨e1', e2'⟩ := hsec (x', y')
    rw [h] at e1 e2
    rw [e1'] at e1; rw [e2'] at e2
    have hx := (mul_right_cancel e1).symm
    have hy := (mul_left_cancel e2).symm
    exact Prod.ext (Subtype.ext (Subtype.ext hx)) (Subtype.ext (Subtype.ext hy))
  have := Nat.card_le_card_of_injective F hinj
  simp only [Nat.card_prod] at this
  have : ((Nat.card (B n) * Nat.card (B n) : ℕ) : ℝ) ≤
      ((Nat.card (B (6 * n + 2)) * (Nat.card Dih * Nat.card Dih) : ℕ) : ℝ) := by
    exact_mod_cast this
  push_cast at this
  nlinarith

end Doubling

/-- Target 3: the doubling inequality for every finite generating set. -/
theorem exists_card_wordBall_sq_le (S : Finset Γ) (hS : Subgroup.closure (S : Set Γ) = ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      (Nat.card (wordBall (S : Set Γ) n) : ℝ) ^ 2 ≤
        C * Nat.card (wordBall (S : Set Γ) (K * n)) := by
  classical
  open Garrido in
  let S₀ : Finset Γ := {GrigorchukGroup.a, GrigorchukGroup.b, GrigorchukGroup.c,
    GrigorchukGroup.d}
  have hS₀ : (S₀ : Set Γ) = Garrido.GrigorchukGroup.generators := by
    simp [S₀, Garrido.GrigorchukGroup.generators]
  have hgen : Subgroup.closure (S₀ : Set Γ) = ⊤ := by
    rw [hS₀]; exact closure_generators
  obtain ⟨K₁, hK₁, h₁⟩ := exists_card_wordBall_le S S₀ hgen
  obtain ⟨K₂, hK₂, h₂⟩ := exists_card_wordBall_le S₀ S hS
  have hDpos : (0 : ℝ) < Nat.card Dih := by
    have : Finite Dih := Dih_finite.to_subtype
    have : Nonempty Dih := ⟨⟨1, by simp [Dih]⟩⟩
    exact_mod_cast Nat.card_pos
  refine ⟨(Nat.card Dih : ℝ) ^ 2, by positivity, K₂ * (8 * K₁), by positivity, fun n hn => ?_⟩
  have e1 := (h₁ n).2
  have e2 := card_wordBall_sq_le_generators (K₁ * n)
  rw [← hS₀] at e2
  have e3 := monotone_card_wordBall S₀ (show 6 * (K₁ * n) + 2 ≤ 8 * K₁ * n by nlinarith)
  have e4 := (h₂ (8 * K₁ * n)).2
  have e0 : (0 : ℝ) ≤ Nat.card (wordBall (S : Set Γ) n) := Nat.cast_nonneg _
  calc (Nat.card (wordBall (S : Set Γ) n) : ℝ) ^ 2
      ≤ (Nat.card (wordBall (S₀ : Set Γ) (K₁ * n)) : ℝ) ^ 2 := pow_le_pow_left₀ e0 e1 2
    _ ≤ (Nat.card Dih : ℝ) ^ 2 * Nat.card (wordBall (S₀ : Set Γ) (6 * (K₁ * n) + 2)) := e2
    _ ≤ (Nat.card Dih : ℝ) ^ 2 * Nat.card (wordBall (S₀ : Set Γ) (8 * K₁ * n)) := by gcongr
    _ ≤ (Nat.card Dih : ℝ) ^ 2 * Nat.card (wordBall (S : Set Γ) (K₂ * (8 * K₁ * n))) := by
      gcongr
    _ = _ := by rw [show K₂ * (8 * K₁) * n = K₂ * (8 * K₁ * n) by ring]

/-- Target 2. -/
theorem card_wordBall_basic (S : Finset Γ) (hS : Subgroup.closure (S : Set Γ) = ⊤) :
    Monotone (fun n : ℕ => (Nat.card (wordBall (S : Set Γ) n) : ℝ)) ∧
      (∀ n : ℕ, (1 : ℝ) ≤ Nat.card (wordBall (S : Set Γ) n)) ∧
      Filter.Tendsto (fun n : ℕ => (Nat.card (wordBall (S : Set Γ) n) : ℝ))
        Filter.atTop Filter.atTop ∧
      ∀ n : ℕ, (wordBall (S : Set Γ) n).Finite := by
  have := infinite_grigorchukGroup
  exact ⟨monotone_card_wordBall S, one_le_card_wordBall S, tendsto_card_wordBall S hS,
    wordBall_finite _ S.finite_toSet⟩

end GrigorchukPak

namespace GrigorchukPak

theorem superpolynomial_and_exp_rpow_le_card_wordBall' (S : Finset Garrido.GrigorchukGroup)
    (hS : Subgroup.closure (S : Set Garrido.GrigorchukGroup) = ⊤) :
    Filter.Tendsto
        (fun n : ℕ => Real.log (Nat.card (Chou.wordBall (S : Set Garrido.GrigorchukGroup) n) : ℝ) /
          Real.log n) Filter.atTop Filter.atTop ∧
      ∃ α : ℝ, 0 < α ∧ ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, 0 < K ∧ ∀ n : ℕ, 0 < n →
        Real.exp ((n : ℝ) ^ α) ≤
          C * (Nat.card (Chou.wordBall (S : Set Garrido.GrigorchukGroup) (K * n)) : ℝ) := by
  obtain ⟨hmono, hone, htop, -⟩ := card_wordBall_basic S hS
  obtain ⟨C, hC, K, hK, hsq⟩ := exists_card_wordBall_sq_le S hS
  obtain ⟨α, hα, C', hC', K', hK', hexp⟩ :=
    exists_exp_rpow_le_of_pow_le _ hmono hone htop 2 (by norm_num) C hC K hK hsq
  refine ⟨?_, α, hα, C', hC', K', hK', hexp⟩
  set γ : ℕ → ℝ := fun n => (Nat.card (Chou.wordBall (S : Set Garrido.GrigorchukGroup) n) : ℝ)
    with hγ
  have hγpos : ∀ n, 0 < γ n := fun n => lt_of_lt_of_le one_pos (hone n)
  set A : ℝ := (((2 * K' : ℕ) : ℝ)) ^ α with hA
  have hApos : 0 < A := Real.rpow_pos_of_pos (by positivity) _
  have hlow : ∀ n : ℕ, 2 * K' ≤ n → (n : ℝ) ^ α / A - Real.log C' ≤ Real.log (γ n) := by
    intro n hn
    set q := n / K' with hqdef
    have hq : 0 < q := Nat.div_pos (by omega) hK'
    have hKq : K' * q ≤ n := Nat.mul_div_le n K'
    have h2 : n ≤ q * (2 * K') := by
      have := Nat.lt_mul_div_succ n hK'
      nlinarith
    have hqr : (n : ℝ) / ((2 * K' : ℕ) : ℝ) ≤ q := by
      rw [div_le_iff₀ (by positivity)]
      exact_mod_cast h2
    have e3 : ((n : ℝ) / ((2 * K' : ℕ) : ℝ)) ^ α ≤ (q : ℝ) ^ α :=
      Real.rpow_le_rpow (by positivity) hqr hα.le
    rw [Real.div_rpow (by positivity) (by positivity)] at e3
    have e4 : Real.exp ((q : ℝ) ^ α) ≤ C' * γ n :=
      (hexp q hq).trans (mul_le_mul_of_nonneg_left (hmono hKq) hC'.le)
    have e5 := Real.log_le_log (Real.exp_pos _) e4
    rw [Real.log_exp, Real.log_mul hC'.ne' (hγpos n).ne'] at e5
    linarith
  rw [Filter.tendsto_atTop_atTop]
  intro b
  set M : ℝ := max b 0 with hM
  set c : ℝ := 1 / A with hc
  have hcpos : 0 < c := by positivity
  set D : ℝ := |Real.log C'| with hD
  set T : ℝ := max 1 ((M * (2 / α) + D) / c) with hT
  have ht : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (α / 2)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (ht.eventually_ge_atTop T)
  refine ⟨max N (max (2 * K') 2), fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnK : 2 * K' ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn2 : 2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have htn := hN n hnN
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn2
  have hlog_pos : 0 < Real.log n := Real.log_pos hn1
  have hlog_le : Real.log n ≤ (n : ℝ) ^ (α / 2) / (α / 2) :=
    Real.log_le_rpow_div (by positivity) (by linarith)
  have hsq' : (n : ℝ) ^ α = (n : ℝ) ^ (α / 2) * (n : ℝ) ^ (α / 2) := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  have hl := hlow n hnK
  rw [le_div_iff₀ hlog_pos]
  set t : ℝ := (n : ℝ) ^ (α / 2) with htdef
  have hT1 : 1 ≤ t := le_trans (le_max_left _ _) htn
  have hT2 : (M * (2 / α) + D) / c ≤ t := le_trans (le_max_right _ _) htn
  have hct : M * (2 / α) + D ≤ c * t := by
    rw [div_le_iff₀ hcpos] at hT2; linarith
  have hM0 : 0 ≤ M := le_max_right _ _
  have hbM : b ≤ M := le_max_left _ _
  have hD0 : 0 ≤ D := abs_nonneg _
  have hlogC : Real.log C' ≤ D := le_abs_self _
  have hdiv : t / (α / 2) = (2 / α) * t := by field_simp
  have hlow' : c * (t * t) - D ≤ Real.log (γ n) := by
    have : (n : ℝ) ^ α / A = c * (t * t) := by rw [hsq', hc]; ring
    linarith
  have h1 : b * Real.log n ≤ M * Real.log n := mul_le_mul_of_nonneg_right hbM hlog_pos.le
  have h2 : M * Real.log n ≤ M * ((2 / α) * t) := by
    rw [← hdiv]; exact mul_le_mul_of_nonneg_left hlog_le hM0
  have h3 : M * ((2 / α) * t) + D ≤ c * (t * t) := by
    have h2α : 0 ≤ M * (2 / α) := by positivity
    nlinarith
  show b * Real.log n ≤ Real.log (γ n)
  linarith


end GrigorchukPak


theorem solution (S : Finset Garrido.GrigorchukGroup)
    (hS : Subgroup.closure (S : Set Garrido.GrigorchukGroup) = ⊤) :
    Filter.Tendsto
        (fun n : ℕ => Real.log (Nat.card (Chou.wordBall (S : Set Garrido.GrigorchukGroup) n) : ℝ) /
          Real.log n) Filter.atTop Filter.atTop ∧
      ∃ α : ℝ, 0 < α ∧ ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, 0 < K ∧ ∀ n : ℕ, 0 < n →
        Real.exp ((n : ℝ) ^ α) ≤
          C * (Nat.card (Chou.wordBall (S : Set Garrido.GrigorchukGroup) (K * n)) : ℝ) :=
  GrigorchukPak.superpolynomial_and_exp_rpow_le_card_wordBall' S hS
