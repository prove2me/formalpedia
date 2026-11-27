-- Prove2me | solution 1 for HypercliqueAC0.FixedDepth.tail_biased_weak
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:26:47.858577+00:00
-- url     : https://prove2.me/submissions/2fac3c65-77c1-47ab-9511-a9b37eeac1b9

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting
import Theorems.Thm_HypercliqueAC0_FixedDepth_tail_uniform_weak

noncomputable section
namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators
open OAI.Problem313

namespace TBW

theorem chi_true_eq (p : ℝ) :
    BiasedFourier.chi p true = (1 - p) * (1 / Real.sqrt (p * (1 - p))) := by
  rw [BiasedFourier.chi_true]; ring

theorem chi_false_eq (p : ℝ) :
    BiasedFourier.chi p false = -p * (1 / Real.sqrt (p * (1 - p))) := by
  rw [BiasedFourier.chi_false]; ring

theorem r_sq {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (1 / Real.sqrt (p * (1 - p))) ^ 2 * (p * (1 - p)) = 1 := by
  have h0 : 0 < p * (1 - p) := mul_pos hp (by linarith)
  have h1 : (1 - p) ≠ 0 := by linarith
  rw [div_pow, Real.sq_sqrt h0.le]; field_simp

theorem sqrt_quarter : Real.sqrt ((1 / 2 : ℝ) * (1 - 1 / 2)) = 1 / 2 := by
  rw [show (1 / 2 : ℝ) * (1 - 1 / 2) = (1 / 2) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

theorem chi_half_true : BiasedFourier.chi (1 / 2 : ℝ) true = 1 := by
  rw [BiasedFourier.chi_true, sqrt_quarter]; norm_num

theorem chi_half_false : BiasedFourier.chi (1 / 2 : ℝ) false = -1 := by
  rw [BiasedFourier.chi_false, sqrt_quarter]; norm_num

theorem coord_inv {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (a b : Bool) :
    BiasedFourier.scalarWeight p a * (1 + BiasedFourier.chi p a * BiasedFourier.chi p b) =
      if a = b then 1 else 0 := by
  have hr := r_sq hp hp1
  cases a <;> cases b <;>
    simp only [BiasedFourier.scalarWeight_true, BiasedFourier.scalarWeight_false,
      chi_true_eq, chi_false_eq, if_true, if_false, Bool.false_eq_true, reduceCtorEq] 
  · linear_combination p * hr
  · linear_combination (-(1 - p)) * hr
  · linear_combination (-p) * hr
  · linear_combination (1 - p) * hr

theorem char_eq_prod {X : Type} [Fintype X] (p : ℝ) (S : Finset X) (x : X → Bool) :
    BiasedFourier.char p S x = ∏ e, if e ∈ S then BiasedFourier.chi p (x e) else 1 := by
  rw [Finset.prod_ite_mem, Finset.univ_inter]; rfl

theorem inversion {X : Type} [Fintype X] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (X → Bool) → ℝ) (x : X → Bool) :
    g x = ∑ S : Finset X, BiasedFourier.coeff p g S * BiasedFourier.char p S x := by
  have key : ∀ y : X → Bool, BiasedFourier.weight p y *
      (∑ S : Finset X, BiasedFourier.char p S y * BiasedFourier.char p S x) =
        if y = x then 1 else 0 := by
    intro y
    have h1 : (∑ S : Finset X, BiasedFourier.char p S y * BiasedFourier.char p S x) =
        ∏ e, (1 + BiasedFourier.chi p (y e) * BiasedFourier.chi p (x e)) := by
      rw [Finset.prod_one_add, Finset.powerset_univ]
      apply Finset.sum_congr rfl
      intro S _
      unfold BiasedFourier.char
      rw [Finset.prod_mul_distrib]
    rw [h1]
    unfold BiasedFourier.weight
    rw [← Finset.prod_mul_distrib]
    simp_rw [coord_inv hp hp1]
    rw [Fintype.prod_boole]
    simp only [funext_iff]
  calc g x = ∑ y, g y * (if y = x then 1 else 0) := by simp
    _ = ∑ y, g y * (BiasedFourier.weight p y *
          ∑ S : Finset X, BiasedFourier.char p S y * BiasedFourier.char p S x) := by
        simp_rw [key]
    _ = ∑ S : Finset X, BiasedFourier.coeff p g S * BiasedFourier.char p S x := by
        unfold BiasedFourier.coeff
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro S _
        apply Finset.sum_congr rfl; intro y _
        ring


def sel (c : Bool × Bool) (a : Bool) : Bool := if a then c.2 else c.1

def proj {X : Type} (Z : X → Bool × Bool) (y : X → Bool) : X → Bool := fun e => sel (Z e) (y e)

def W {X : Type} [Fintype X] (p : ℝ) (Z : X → Bool × Bool) : ℝ :=
  ∏ e, (BiasedFourier.scalarWeight p (Z e).1 * BiasedFourier.scalarWeight p (Z e).2)

def kf (p : ℝ) (s u : Bool) (c : Bool × Bool) (a : Bool) : ℝ :=
  BiasedFourier.scalarWeight (1 / 2) a * (if s then BiasedFourier.chi p (sel c a) else 1) *
    (if u then BiasedFourier.chi (1 / 2) a else 1)

def K {X : Type} [Fintype X] (p : ℝ) (Z : X → Bool × Bool) (S U : Finset X) : ℝ :=
  ∑ y : X → Bool, BiasedFourier.weight (1 / 2) y * BiasedFourier.char p S (proj Z y) *
    BiasedFourier.char (1 / 2) U y

theorem K_prod {X : Type} [Fintype X] (p : ℝ) (Z : X → Bool × Bool) (S U : Finset X) :
    K p Z S U = ∏ e, ∑ a, kf p (decide (e ∈ S)) (decide (e ∈ U)) (Z e) a := by
  rw [Fintype.prod_sum]
  unfold K
  apply Finset.sum_congr rfl
  intro y _
  rw [char_eq_prod, char_eq_prod]
  unfold BiasedFourier.weight kf proj
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  simp only [decide_eq_true_eq]

def phi : Bool → Bool → Bool → ℝ
  | true, true, _ => 1 / 2
  | false, false, false => 1
  | _, _, _ => 0

theorem coord_moment {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (s t u : Bool) :
    ∑ c : Bool × Bool, BiasedFourier.scalarWeight p c.1 * BiasedFourier.scalarWeight p c.2 *
      (∑ a, kf p s u c a) * (∑ b, kf p t u c b) = phi s t u := by
  have hr := r_sq hp hp1
  cases s <;> cases t <;> cases u <;>
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, kf, sel, phi, chi_true_eq, chi_false_eq,
      chi_half_true, chi_half_false, BiasedFourier.scalarWeight_true,
      BiasedFourier.scalarWeight_false, if_true, if_false, Bool.false_eq_true, reduceCtorEq]
  all_goals first | ring1 | linear_combination (1 / 2 : ℝ) * hr


theorem phi_ne {s t : Bool} (u : Bool) (h : s ≠ t) : phi s t u = 0 := by
  cases s <;> cases t <;> cases u <;> simp_all [phi]

def mF {X : Type} (p : ℝ) (S T U : Finset X) (e : X) (c : Bool × Bool) : ℝ :=
  BiasedFourier.scalarWeight p c.1 * BiasedFourier.scalarWeight p c.2 *
    (∑ a, kf p (decide (e ∈ S)) (decide (e ∈ U)) c a) *
    (∑ b, kf p (decide (e ∈ T)) (decide (e ∈ U)) c b)

theorem moment {X : Type} [Fintype X] {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (S T U : Finset X) :
    ∑ Z : X → Bool × Bool, W p Z * K p Z S U * K p Z T U =
      if S = T ∧ U ⊆ S then (1 / 2 : ℝ) ^ S.card else 0 := by
  have h1 : ∀ Z : X → Bool × Bool, W p Z * K p Z S U * K p Z T U =
      ∏ e, mF p S T U e (Z e) := by
    intro Z
    rw [K_prod, K_prod, W, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    rfl
  rw [Finset.sum_congr rfl (fun Z _ => h1 Z), ← Fintype.prod_sum (mF p S T U)]
  simp only [mF, coord_moment hp hp1]
  split_ifs with h
  · obtain ⟨rfl, hUS⟩ := h
    calc ∏ e, phi (decide (e ∈ S)) (decide (e ∈ S)) (decide (e ∈ U))
        = ∏ e, if e ∈ S then (1 / 2 : ℝ) else 1 := by
          apply Finset.prod_congr rfl
          intro e _
          by_cases he : e ∈ S
          · simp [he, phi]
          · have heU : e ∉ U := fun h' => he (hUS h')
            simp [he, heU, phi]
      _ = (1 / 2 : ℝ) ^ S.card := by
          rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  · by_cases hST : S = T
    · subst hST
      have hn : ¬ U ⊆ S := fun h' => h ⟨rfl, h'⟩
      obtain ⟨e, heU, heS⟩ := Finset.not_subset.mp hn
      exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [heU, heS, phi])
    · have : ∃ e, ¬ (e ∈ S ↔ e ∈ T) := by
        by_contra hc
        push Not at hc
        exact hST (Finset.ext hc)
      obtain ⟨e, he⟩ := this
      refine Finset.prod_eq_zero (Finset.mem_univ e) (phi_ne _ ?_)
      intro h'
      apply he
      simpa using h'

theorem coeffZ {X : Type} [Fintype X] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (X → Bool) → ℝ) (Z : X → Bool × Bool) (U : Finset X) :
    BiasedFourier.coeff (1 / 2) (fun y => g (proj Z y)) U =
      ∑ S, BiasedFourier.coeff p g S * K p Z S U := by
  calc BiasedFourier.coeff (1 / 2) (fun y => g (proj Z y)) U
      = ∑ y : X → Bool, BiasedFourier.weight (1 / 2) y * g (proj Z y) *
          BiasedFourier.char (1 / 2) U y := rfl
    _ = ∑ y : X → Bool, BiasedFourier.weight (1 / 2) y *
          (∑ S : Finset X, BiasedFourier.coeff p g S * BiasedFourier.char p S (proj Z y)) *
          BiasedFourier.char (1 / 2) U y := by
        apply Finset.sum_congr rfl
        intro y _
        rw [← inversion hp hp1 g]
    _ = ∑ S, BiasedFourier.coeff p g S * K p Z S U := by
        unfold K
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro S _
        apply Finset.sum_congr rfl; intro y _
        ring

theorem EZ {X : Type} [Fintype X] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (X → Bool) → ℝ) (U : Finset X) :
    ∑ Z : X → Bool × Bool, W p Z * (BiasedFourier.coeff (1 / 2) (fun y => g (proj Z y)) U) ^ 2 =
      ∑ S, (BiasedFourier.coeff p g S) ^ 2 *
        (if U ⊆ S then (1 / 2 : ℝ) ^ S.card else 0) := by
  simp_rw [coeffZ hp hp1 g]
  calc ∑ Z : X → Bool × Bool, W p Z * (∑ S, BiasedFourier.coeff p g S * K p Z S U) ^ 2
      = ∑ Z : X → Bool × Bool, ∑ S, ∑ T, BiasedFourier.coeff p g S * BiasedFourier.coeff p g T *
          (W p Z * K p Z S U * K p Z T U) := by
        apply Finset.sum_congr rfl; intro Z _
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro S _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro T _
        ring
    _ = ∑ S, ∑ T, BiasedFourier.coeff p g S * BiasedFourier.coeff p g T *
          ∑ Z : X → Bool × Bool, W p Z * K p Z S U * K p Z T U := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro S _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro T _
        rw [Finset.mul_sum]
    _ = ∑ S, ∑ T, BiasedFourier.coeff p g S * BiasedFourier.coeff p g T *
          (if S = T ∧ U ⊆ S then (1 / 2 : ℝ) ^ S.card else 0) := by
        simp only [moment hp hp1]
    _ = _ := by
        apply Finset.sum_congr rfl; intro S _
        rw [Finset.sum_eq_single S (fun T _ hT => by simp [Ne.symm hT]) (by simp)]
        simp only [true_and]
        ring

theorem inner_count {X : Type} [Fintype X] (S : Finset X) (P : Finset X → Prop) (a : ℝ) :
    (∑ U : Finset X, if P U then (if U ⊆ S then a else 0) else 0) =
      ((S.powerset.filter P).card : ℝ) * a := by
  rw [← nsmul_eq_mul, ← Finset.sum_const, Finset.sum_filter,
    ← Finset.univ_inter S.powerset, ← Finset.sum_ite_mem]
  apply Finset.sum_congr rfl
  intro U _
  by_cases h1 : P U <;> by_cases h2 : U ⊆ S <;> simp [h1, h2]

theorem mainEq {X : Type} [Fintype X] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (X → Bool) → ℝ) (D : ℝ) :
    ∑ Z : X → Bool × Bool, W p Z * fourierTailGE (1 / 2) (fun y => g (proj Z y)) (D / 2) =
      ∑ S, (BiasedFourier.coeff p g S) ^ 2 * ((1 / 2 : ℝ) ^ S.card *
        ((S.powerset.filter (fun U => D / 2 ≤ (U.card : ℝ))).card : ℝ)) := by
  unfold fourierTailGE fourierCoeff
  calc ∑ Z : X → Bool × Bool, W p Z * ∑ U : Finset X, (if D / 2 ≤ (U.card : ℝ) then
          (BiasedFourier.coeff (1 / 2) (fun y => g (proj Z y)) U) ^ 2 else 0)
      = ∑ U : Finset X, if D / 2 ≤ (U.card : ℝ) then ∑ Z : X → Bool × Bool,
          W p Z * (BiasedFourier.coeff (1 / 2) (fun y => g (proj Z y)) U) ^ 2 else 0 := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro U _
        split_ifs <;> simp
    _ = ∑ U : Finset X, if D / 2 ≤ (U.card : ℝ) then ∑ S, (BiasedFourier.coeff p g S) ^ 2 *
          (if U ⊆ S then (1 / 2 : ℝ) ^ S.card else 0) else 0 := by
        simp only [EZ hp hp1]
    _ = ∑ S, (BiasedFourier.coeff p g S) ^ 2 * ∑ U : Finset X, if D / 2 ≤ (U.card : ℝ) then
          (if U ⊆ S then (1 / 2 : ℝ) ^ S.card else 0) else 0 := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro U _
        split_ifs <;> simp
    _ = _ := by
        apply Finset.sum_congr rfl; intro S _
        rw [inner_count]
        ring

theorem comb {X : Type} (S : Finset X) (D : ℝ) (hD : D ≤ (S.card : ℝ)) :
    2 ^ S.card ≤ 2 * (S.powerset.filter (fun U => D / 2 ≤ (U.card : ℝ))).card := by
  have hsum := Finset.card_filter_add_card_filter_not (s := S.powerset)
    (fun U : Finset X => D / 2 ≤ (U.card : ℝ))
  rw [Finset.card_powerset] at hsum
  have hinj : (S.powerset.filter (fun U : Finset X => ¬ D / 2 ≤ (U.card : ℝ))).card ≤
      (S.powerset.filter (fun U : Finset X => D / 2 ≤ (U.card : ℝ))).card := by
    apply Finset.card_le_card_of_injOn (fun U => S \ U)
    · intro U hU
      simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_ofPred_eq] at hU ⊢
      refine ⟨Finset.sdiff_subset, ?_⟩
      have h1 := Finset.card_sdiff_add_card_eq_card hU.1
      have h2 : ((S \ U).card : ℝ) + U.card = S.card := by exact_mod_cast h1
      linarith [hU.2]
    · intro U1 hU1 U2 hU2 h
      simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_ofPred_eq] at hU1 hU2
      have e1 := Finset.sdiff_sdiff_eq_self hU1.1
      have e2 := Finset.sdiff_sdiff_eq_self hU2.1
      simp only at h
      rw [← e1, ← e2, h]
  omega

theorem tail_le {X : Type} [Fintype X] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (X → Bool) → ℝ) (D : ℝ) :
    fourierTailGE p g D ≤
      2 * ∑ Z : X → Bool × Bool, W p Z * fourierTailGE (1 / 2) (fun y => g (proj Z y)) (D / 2) := by
  rw [mainEq hp hp1, Finset.mul_sum]
  unfold fourierTailGE fourierCoeff
  apply Finset.sum_le_sum
  intro S _
  have hN : (0 : ℝ) ≤ ((S.powerset.filter (fun U => D / 2 ≤ (U.card : ℝ))).card : ℝ) :=
    Nat.cast_nonneg _
  split_ifs with hS
  · have hc := comb S D hS
    have hc' : (2 : ℝ) ^ S.card ≤
        2 * ((S.powerset.filter (fun U => D / 2 ≤ (U.card : ℝ))).card : ℝ) := by
      exact_mod_cast hc
    have hhalf : (1 / 2 : ℝ) ^ S.card * 2 ^ S.card = 1 := by
      rw [← mul_pow]; norm_num
    have hpos : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ S.card := by positivity
    have h1 : 1 ≤ 2 * ((1 / 2 : ℝ) ^ S.card *
        ((S.powerset.filter (fun U => D / 2 ≤ (U.card : ℝ))).card : ℝ)) := by
      nlinarith
    have := mul_le_mul_of_nonneg_left h1 (sq_nonneg (BiasedFourier.coeff p g S))
    linarith
  · positivity

theorem W_nonneg {X : Type} [Fintype X] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (Z : X → Bool × Bool) : 0 ≤ W p Z := by
  unfold W
  apply Finset.prod_nonneg
  intro e _
  apply mul_nonneg <;>
  · unfold BiasedFourier.scalarWeight; split_ifs <;> linarith

theorem W_sum {X : Type} [Fintype X] (p : ℝ) : ∑ Z : X → Bool × Bool, W p Z = 1 := by
  unfold W
  rw [← Fintype.prod_sum (fun (_ : X) (c : Bool × Bool) =>
    BiasedFourier.scalarWeight p c.1 * BiasedFourier.scalarWeight p c.2)]
  apply Finset.prod_eq_one
  intro e _
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, BiasedFourier.scalarWeight_true,
    BiasedFourier.scalarWeight_false]
  ring


/-! ### Substituting the projection `y ↦ Z^y` into a circuit -/

/-- The image of the literal `(v, b)` under the projection: `Z^y_v` is the constant `c.1` if
`c.1 = c.2`, else `y_v` (if `c = (false, true)`) or `¬ y_v` (if `c = (true, false)`). -/
def projLit {X : Type} (c : Bool × Bool) (v : X) (b : Bool) : MantriCVQ.Src X :=
  if c.1 = c.2 then .const (c.1 == b) else if c.2 then .lit v b else .lit v (!b)

def mapSrc {X : Type} (Z : X → Bool × Bool) : MantriCVQ.Src X → MantriCVQ.Src X
  | .lit v b => projLit (Z v) v b
  | .const b => .const b
  | .gate i => .gate i

theorem mapSrc_eval {X : Type} (Z : X → Bool × Bool) (y : X → Bool) (vals : List Bool)
    (s : MantriCVQ.Src X) :
    (mapSrc Z s).eval y vals = s.eval (proj Z y) vals := by
  cases s with
  | lit v b =>
    simp only [mapSrc, projLit, MantriCVQ.Src.eval, proj, sel]
    generalize Z v = c
    obtain ⟨c1, c2⟩ := c
    cases c1 <;> cases c2 <;> cases b <;> cases hy : y v <;> simp [MantriCVQ.Src.eval, hy]
  | const b => rfl
  | gate i => rfl

theorem mapSrc_depth {X : Type} (Z : X → Bool × Bool) (ds : List ℕ) (s : MantriCVQ.Src X) :
    (mapSrc Z s).depth ds = s.depth ds := by
  cases s with
  | lit v b =>
    simp only [mapSrc, projLit]
    split_ifs <;> rfl
  | const b => rfl
  | gate i => rfl

theorem mapSrc_gate {X : Type} (Z : X → Bool × Bool) (s : MantriCVQ.Src X) (i : ℕ)
    (h : mapSrc Z s = .gate i) : s = .gate i := by
  cases s with
  | lit v b =>
    simp only [mapSrc, projLit] at h
    split_ifs at h
  | const b => simp [mapSrc] at h
  | gate j => simpa [mapSrc] using h

def mapGate {X : Type} (Z : X → Bool × Bool) (g : MantriCVQ.ACGate X) : MantriCVQ.ACGate X :=
  ⟨g.isAnd, g.inputs.map (mapSrc Z)⟩

def mapCirc {X : Type} (Z : X → Bool × Bool) (C : MantriCVQ.ACCircuit X) :
    MantriCVQ.ACCircuit X where
  gates := C.gates.map (mapGate Z)
  output := mapSrc Z C.output
  wf := by
    intro k hk s hs i hsi
    have hk' : k < C.gates.length := by simpa using hk
    simp only [List.getElem_map, mapGate, List.mem_map] at hs
    obtain ⟨a, ha, rfl⟩ := hs
    exact C.wf k hk' a ha i (mapSrc_gate Z a i hsi)
  wf_output := fun i h => by simpa using C.wf_output i (mapSrc_gate Z _ i h)

theorem mapCirc_length {X : Type} (Z : X → Bool × Bool) (C : MantriCVQ.ACCircuit X) :
    (mapCirc Z C).gates.length = C.gates.length := by
  simp [mapCirc]

theorem mapCirc_eval {X : Type} (Z : X → Bool × Bool) (C : MantriCVQ.ACCircuit X)
    (y : X → Bool) : (mapCirc Z C).eval y = C.eval (proj Z y) := by
  unfold MantriCVQ.ACCircuit.eval
  simp only [mapCirc, List.foldl_map, mapSrc_eval]
  congr 2
  funext vals g
  simp [mapGate, List.all_map, List.any_map, Function.comp_def, mapSrc_eval]

theorem mapCirc_depth {X : Type} (Z : X → Bool × Bool) (C : MantriCVQ.ACCircuit X) :
    (mapCirc Z C).depth = C.depth := by
  unfold MantriCVQ.ACCircuit.depth
  simp only [mapCirc, List.foldl_map, mapSrc_depth]
  congr 2
  funext ds g
  simp [mapGate, List.map_map, Function.comp_def, mapSrc_depth]

end TBW
end HypercliqueAC0.FixedDepth

open HypercliqueAC0.FixedDepth in
attribute [local instance] Classical.propDecidable Classical.decEq in
theorem solution (h : ℕ) (hh : 1 ≤ h) :
    ∃ K : ℝ, 0 < K ∧ ∀ (X : Type) [Fintype X] (p : ℝ) (C : MantriCVQ.ACCircuit X) (w : ℕ),
      0 < p → p < 1 → C.depth ≤ h → ∀ D : ℝ, K * (w : ℝ) ^ h ≤ D →
        fourierTailGE p (boolReal C.eval) D ≤
          4 * ((C.gates.length : ℝ) + 1) * (2 : ℝ) ^ (-(w : ℝ)) := by
  obtain ⟨Ku, hKu, hU⟩ := tail_uniform_weak h hh
  refine ⟨2 * Ku, by positivity, ?_⟩
  intro X _ p C w hp hp1 hC D hD
  set B : ℝ := 2 * ((C.gates.length : ℝ) + 1) * (2 : ℝ) ^ (-(w : ℝ)) with hB
  have hZ : ∀ Z : X → Bool × Bool,
      fourierTailGE (1 / 2) (fun y => boolReal C.eval (TBW.proj Z y)) (D / 2) ≤ B := by
    intro Z
    have h1 := hU X (TBW.mapCirc Z C) w (by rw [TBW.mapCirc_depth]; exact hC) (D / 2)
      (by linarith)
    have h2 : boolReal (TBW.mapCirc Z C).eval = fun y => boolReal C.eval (TBW.proj Z y) := by
      funext y
      simp only [boolReal, TBW.mapCirc_eval]
    rw [h2, TBW.mapCirc_length] at h1
    exact h1
  calc fourierTailGE p (boolReal C.eval) D
      ≤ 2 * ∑ Z : X → Bool × Bool, TBW.W p Z *
          fourierTailGE (1 / 2) (fun y => boolReal C.eval (TBW.proj Z y)) (D / 2) :=
        TBW.tail_le hp hp1 (boolReal C.eval) D
    _ ≤ 2 * ∑ Z : X → Bool × Bool, TBW.W p Z * B := by
        gcongr with Z
        · exact TBW.W_nonneg hp hp1 Z
        · exact hZ Z
    _ = 2 * B := by rw [← Finset.sum_mul, TBW.W_sum]; ring
    _ = 4 * ((C.gates.length : ℝ) + 1) * (2 : ℝ) ^ (-(w : ℝ)) := by rw [hB]; ring

