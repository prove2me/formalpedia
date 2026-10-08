-- Prove2me | solution 1 for JMMS.isExtensivelyAmenable_tfae_invertedOrbit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T13:42:02.645261+00:00
-- url     : https://prove2.me/submissions/8e24f957-29c4-42b4-b291-85f43e758b06

import Mathlib
import Definitions.Def_IntervalExchange
import Theorems.Thm_JMMS_isExtensivelyAmenable_tfae

section

/-! # JMMS Proposition 4.1: extensive amenability through the inverted orbit

Juschenko, Matte Bon, Monod and de la Salle, *Extensive amenability and an application to
interval exchanges*, Proposition 4.1. For a finitely generated group acting transitively, a
symmetric probability `μ` with generating support (not necessarily finitely supported) and
`x₀ ∈ X`, the following are equivalent: (0) extensive amenability; (i) `E 2^{-|O_n|}` decays
subexponentially; (ii) `P(|O_n| < εn) > e^{-εn}` infinitely often; (iii) events of
subexponential probability on which `|O_n| = o(n)` on average.

The paper's route goes through Kesten's criterion for the lamplighter action. Here Kesten's
criterion is not used: both directions are proved by hand on the configuration space of finite
subsets of `X`, for the switch–walk–switch operators `T` (toggle `x₀`) and `P` (walk by `μ`):

* `(TP)^j T δ_D` has the explicit form `E[2^{-|O_j|} 1(E ∆ g_j⁻¹ D ⊆ O_j)]` (part A), so
  `⟨W_a, W_b⟩ = E 2^{-|O_{a+b}|}` for `W_n = (TP)^n T δ_∅`, which is supermultiplicative.
* (i) ⇔ (ii) ⇔ (iii): Markov, Jensen (tangent line) and Fekete (part B).
* (i) ⇒ (0): the ratios `p_{2n+2}/p_{2n}` approach `1`, a variance identity makes the
  normalised squares of `W_n` almost invariant under `g h⁻¹` (`g, h ∈ supp μ`), and an ultrafilter
  limit, symmetrised over one generator, is a mean for Lemma 2.2 (part C).
* (0) ⇒ (i): averaging the extensively amenable mean over subsets gives a mean on finite sets
  invariant under the lamplighter moves; Day's convexity argument yields an almost invariant
  `φ` (Reiter); for `f = √φ`, `b_k = ‖(TP)^k T f‖²` is log-convex by Cauchy–Schwarz and is
  bounded by `|supp φ| · E 2^{-|O_{2k}|}` (parts D, F).

The only milestone used is Lemma 2.2 (`JMMS.isExtensivelyAmenable_tfae`). The integral against a
finitely additive measure is copied from `Solutions/WolfWork/GAR_all.lean`. -/

/-! # JMMS Proposition 4.1, part A: walks, the action on finite sets, the switch–walk–switch
operators and the explicit formula for their iterates. -/

open IntervalExchange
open scoped ENNReal symmDiff

set_option linter.unusedSectionVars false

namespace JMMS.IETP41

/-! ## The action on finite subsets -/

section Act

variable {G X : Type*} [Group G] [MulAction G X]

/-- The action of `g` on finite subsets of `X`, as `IsExtensivelyAmenableOn` writes it. -/
def act (g : G) (E : Finset X) : Finset X := E.map (MulAction.toPerm g).toEmbedding

lemma mem_act {g : G} {E : Finset X} {x : X} : x ∈ act g E ↔ g⁻¹ • x ∈ E := by
  unfold act
  rw [Finset.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro h
    exact ⟨g⁻¹ • x, h, by simp⟩

lemma act_mul (g h : G) (E : Finset X) : act (g * h) E = act g (act h E) := by
  ext x
  simp only [mem_act, mul_inv_rev, mul_smul]

lemma act_one (E : Finset X) : act (1 : G) E = E := by
  ext x
  simp only [mem_act, inv_one, one_smul]

lemma act_inv_act (g : G) (E : Finset X) : act g⁻¹ (act g E) = E := by
  rw [← act_mul, inv_mul_cancel, act_one]

lemma act_act_inv (g : G) (E : Finset X) : act g (act g⁻¹ E) = E := by
  rw [← act_mul, mul_inv_cancel, act_one]

/-- `act g` as a permutation of the finite subsets. -/
def actEquiv (g : G) : Finset X ≃ Finset X where
  toFun := act g
  invFun := act g⁻¹
  left_inv E := act_inv_act g E
  right_inv E := act_act_inv g E

@[simp] lemma actEquiv_apply (g : G) (E : Finset X) : actEquiv g E = act g E := rfl

lemma card_act (g : G) (E : Finset X) : (act g E).card = E.card := Finset.card_map _

lemma act_subset_act {g : G} {E F : Finset X} : act g E ⊆ act g F ↔ E ⊆ F := by
  constructor
  · intro h x hx
    have : g • x ∈ act g F := h (mem_act.2 (by simpa using hx))
    simpa using mem_act.1 this
  · intro h x hx
    exact mem_act.2 (h (mem_act.1 hx))

variable [DecidableEq X]

lemma act_symmDiff (g : G) (E F : Finset X) : act g (E ∆ F) = act g E ∆ act g F := by
  ext x
  simp only [mem_act, Finset.mem_symmDiff]

/-- Toggling the lamp at `x₀`. -/
def tog (x₀ : X) (E : Finset X) : Finset X := E ∆ {x₀}

lemma tog_tog (x₀ : X) (E : Finset X) : tog x₀ (tog x₀ E) = E := by
  unfold tog; rw [symmDiff_assoc, symmDiff_self, symmDiff_bot]

/-- `tog x₀` as a permutation of the finite subsets. -/
def togEquiv (x₀ : X) : Finset X ≃ Finset X where
  toFun := tog x₀
  invFun := tog x₀
  left_inv E := tog_tog x₀ E
  right_inv E := tog_tog x₀ E

@[simp] lemma togEquiv_apply (x₀ : X) (E : Finset X) : togEquiv x₀ E = tog x₀ E := rfl

end Act

/-! ## Walks -/

section Walk

variable {G : Type*} [Group G]

/-- The expectation of an `ℝ≥0∞`-valued function of the steps. -/
noncomputable def wE (μ : G → ℝ) (n : ℕ) (F : (Fin n → G) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' h : Fin n → G, (∏ i, ENNReal.ofReal (μ (h i))) * F h

lemma wE_zero (μ : G → ℝ) (F : (Fin 0 → G) → ℝ≥0∞) : wE μ 0 F = F Fin.elim0 := by
  unfold wE
  rw [tsum_fintype, Fintype.sum_unique]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
  congr 1

lemma wE_succ (μ : G → ℝ) (n : ℕ) (F : (Fin (n + 1) → G) → ℝ≥0∞) :
    wE μ (n + 1) F = ∑' g, ENNReal.ofReal (μ g) * wE μ n (fun h => F (Fin.cons g h)) := by
  unfold wE
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => G)).tsum_eq, ENNReal.tsum_prod']
  refine tsum_congr fun g => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun h => ?_
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

lemma wE_add (μ : G → ℝ) (n : ℕ) (F F' : (Fin n → G) → ℝ≥0∞) :
    wE μ n (fun h => F h + F' h) = wE μ n F + wE μ n F' := by
  unfold wE
  rw [← ENNReal.tsum_add]
  exact tsum_congr fun h => mul_add _ _ _

lemma wE_mul_left (μ : G → ℝ) (n : ℕ) (c : ℝ≥0∞) (F : (Fin n → G) → ℝ≥0∞) :
    wE μ n (fun h => c * F h) = c * wE μ n F := by
  unfold wE
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun h => by ring

lemma wE_mono (μ : G → ℝ) (n : ℕ) {F F' : (Fin n → G) → ℝ≥0∞} (hF : ∀ h, F h ≤ F' h) :
    wE μ n F ≤ wE μ n F' :=
  ENNReal.tsum_le_tsum fun h => by gcongr; exact hF h

lemma tsum_ofReal_eq_one {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) :
    ∑' g, ENNReal.ofReal (μ g) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg hμ.1 hμ.2.summable, hμ.2.tsum_eq, ENNReal.ofReal_one]

lemma wE_one {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) (n : ℕ) :
    wE μ n (fun _ => 1) = 1 := by
  induction n with
  | zero => rw [wE_zero]
  | succ n ih =>
    rw [wE_succ]
    simp only [ih, mul_one]
    exact tsum_ofReal_eq_one hμ

lemma wE_const {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) (n : ℕ) (c : ℝ≥0∞) :
    wE μ n (fun _ => c) = c := by
  have := wE_mul_left μ n c (fun _ => 1)
  simp only [mul_one] at this
  rw [this, wE_one hμ, mul_one]

lemma wE_le_const {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) (n : ℕ) {c : ℝ≥0∞}
    {F : (Fin n → G) → ℝ≥0∞} (hF : ∀ h, F h ≤ c) : wE μ n F ≤ c :=
  (wE_mono μ n hF).trans (wE_const hμ n c).le

/-- `walkExp` of a nonnegative function, through `wE`. -/
lemma walkExp_eq_toReal {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) (n : ℕ)
    {F : (Fin n → G) → ℝ} (hF : ∀ h, 0 ≤ F h) :
    walkExp μ n F = (wE μ n (fun h => ENNReal.ofReal (F h))).toReal := by
  unfold walkExp wE
  rw [ENNReal.tsum_toReal_eq]
  · refine tsum_congr fun h => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hF h), ENNReal.toReal_prod]
    congr 1
    exact Finset.prod_congr rfl fun i _ => (ENNReal.toReal_ofReal (hμ.1 _)).symm
  · intro h
    exact ENNReal.mul_ne_top (ENNReal.prod_ne_top fun i _ => ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top

end Walk

/-! ## The left random walk and the inverted orbit -/

section Orbit

variable {G X : Type*} [Group G] [MulAction G X]

lemma walkPos_cons_succ {n : ℕ} (g : G) (h : Fin n → G) (k : ℕ) :
    walkPos (Fin.cons g h : Fin (n + 1) → G) (k + 1) = walkPos h k * g := by
  unfold walkPos
  rw [List.finRange_succ, List.filter_cons]
  simp only [Fin.val_zero, Nat.zero_lt_succ, decide_true, if_true, List.map_cons,
    Fin.cons_zero, List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil, mul_one]
  congr 3
  rw [List.filter_map, List.map_map]
  have e1 : (Fin.cons g h : Fin (n + 1) → G) ∘ Fin.succ = h := by funext i; simp
  have e2 : List.filter ((fun i : Fin (n + 1) => decide (i.val < k + 1)) ∘ Fin.succ)
      (List.finRange n) = List.filter (fun i : Fin n => decide (i.val < k)) (List.finRange n) :=
    List.filter_congr (fun i _ => by simp [Fin.val_succ])
  rw [e1, e2]

lemma walkPos_zero' {n : ℕ} (h : Fin n → G) : walkPos h 0 = 1 := by
  unfold walkPos
  simp

lemma walkPos_full_cons {n : ℕ} (g : G) (h : Fin n → G) :
    walkPos (Fin.cons g h : Fin (n + 1) → G) (n + 1) = walkPos h n * g :=
  walkPos_cons_succ g h n

variable [DecidableEq X]

lemma invertedOrbit_cons (x₀ : X) {n : ℕ} (g : G) (h : Fin n → G) :
    invertedOrbit x₀ (Fin.cons g h : Fin (n + 1) → G) =
      insert x₀ (act g⁻¹ (invertedOrbit x₀ h)) := by
  ext y
  simp only [invertedOrbit, Finset.mem_insert, mem_act, inv_inv, Finset.mem_image,
    Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    cases k with
    | zero => left; simp [walkPos_zero']
    | succ k =>
      right
      refine ⟨k, by omega, ?_⟩
      rw [walkPos_cons_succ, mul_inv_rev, mul_smul, smul_inv_smul]
  · rintro (rfl | ⟨k, hk, hy⟩)
    · exact ⟨0, by omega, by simp [walkPos_zero']⟩
    · refine ⟨k + 1, by omega, ?_⟩
      rw [walkPos_cons_succ, mul_inv_rev, mul_smul, hy, inv_smul_smul]

lemma invertedOrbit_zero (x₀ : X) (h : Fin 0 → G) : invertedOrbit x₀ h = {x₀} := by
  unfold invertedOrbit
  simp [walkPos_zero']

lemma card_invertedOrbit_le (x₀ : X) {n : ℕ} (h : Fin n → G) :
    (invertedOrbit x₀ h).card ≤ n + 1 := by
  unfold invertedOrbit
  exact (Finset.card_image_le).trans (by simp)

end Orbit

/-! ## The switch–walk–switch operators on functions of finite sets -/

section Ops

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X]

/-- The walk operator `P u (E) = ∑ μ(g) u(g E)`. -/
noncomputable def Pop (μ : G → ℝ) : (Finset X → ℝ≥0∞) →ₗ[ℝ≥0∞] (Finset X → ℝ≥0∞) where
  toFun u E := ∑' g, ENNReal.ofReal (μ g) * u (act g E)
  map_add' u v := by
    funext E
    simp only [Pi.add_apply, mul_add]
    exact ENNReal.tsum_add
  map_smul' c u := by
    funext E
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun g => by ring

lemma Pop_apply (μ : G → ℝ) (u : Finset X → ℝ≥0∞) (E : Finset X) :
    Pop μ u E = ∑' g, ENNReal.ofReal (μ g) * u (act g E) := rfl

/-- The switch operator `T u (E) = (u E + u (E ∆ {x₀})) / 2`. -/
noncomputable def Top (x₀ : X) : (Finset X → ℝ≥0∞) →ₗ[ℝ≥0∞] (Finset X → ℝ≥0∞) where
  toFun u E := (u E + u (tog x₀ E)) * 2⁻¹
  map_add' u v := by
    funext E
    simp only [Pi.add_apply]
    ring
  map_smul' c u := by
    funext E
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

lemma Top_apply (x₀ : X) (u : Finset X → ℝ≥0∞) (E : Finset X) :
    Top x₀ u E = (u E + u (tog x₀ E)) * 2⁻¹ := rfl

/-- One step of the switch–walk–switch chain (on `T`-invariant functions). -/
noncomputable def Rop (μ : G → ℝ) (x₀ : X) : (Finset X → ℝ≥0∞) →ₗ[ℝ≥0∞] (Finset X → ℝ≥0∞) :=
  Top x₀ ∘ₗ Pop μ

lemma Rop_apply (μ : G → ℝ) (x₀ : X) (u : Finset X → ℝ≥0∞) :
    Rop μ x₀ u = Top x₀ (Pop μ u) := rfl

/-- The `ℓ²` pairing of `ℝ≥0∞`-valued functions. -/
noncomputable def inr (u v : Finset X → ℝ≥0∞) : ℝ≥0∞ := ∑' E, u E * v E

/-- `u` is invariant under toggling `x₀`. -/
def TInv (x₀ : X) (u : Finset X → ℝ≥0∞) : Prop := ∀ E, u (tog x₀ E) = u E

lemma Top_of_TInv {x₀ : X} {u : Finset X → ℝ≥0∞} (hu : TInv x₀ u) : Top x₀ u = u := by
  funext E
  rw [Top_apply, hu E, ← two_mul, mul_comm, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num)
    (by norm_num), one_mul]

lemma TInv_Top (x₀ : X) (u : Finset X → ℝ≥0∞) : TInv x₀ (Top x₀ u) := by
  intro E
  rw [Top_apply, Top_apply, tog_tog, add_comm]

lemma TInv_Rop (μ : G → ℝ) (x₀ : X) (u : Finset X → ℝ≥0∞) : TInv x₀ (Rop μ x₀ u) :=
  TInv_Top x₀ _

lemma TInv_Rop_pow (μ : G → ℝ) (x₀ : X) {u : Finset X → ℝ≥0∞} (hu : TInv x₀ u) (k : ℕ) :
    TInv x₀ ((Rop μ x₀ ^ k) u) := by
  cases k with
  | zero => simpa using hu
  | succ k => rw [pow_succ', Module.End.mul_apply]; exact TInv_Rop μ x₀ _

lemma inr_Top (x₀ : X) (u v : Finset X → ℝ≥0∞) : inr (Top x₀ u) v = inr u (Top x₀ v) := by
  unfold inr
  have h1 : ∑' E, u (tog x₀ E) * v E = ∑' E, u E * v (tog x₀ E) := by
    rw [← (togEquiv x₀).tsum_eq]
    exact tsum_congr fun E => by simp [tog_tog]
  calc ∑' E, Top x₀ u E * v E
      = 2⁻¹ * (∑' E, u E * v E + ∑' E, u (tog x₀ E) * v E) := by
        rw [← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
        exact tsum_congr fun E => by rw [Top_apply]; ring
    _ = 2⁻¹ * (∑' E, u E * v E + ∑' E, u E * v (tog x₀ E)) := by rw [h1]
    _ = ∑' E, u E * Top x₀ v E := by
        rw [← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
        exact tsum_congr fun E => by rw [Top_apply]; ring

lemma inr_Pop {μ : G → ℝ} (hsymm : ∀ g, μ g⁻¹ = μ g) (u v : Finset X → ℝ≥0∞) :
    inr (Pop μ u) v = inr u (Pop μ v) := by
  unfold inr
  simp only [Pop_apply]
  calc ∑' E, (∑' g, ENNReal.ofReal (μ g) * u (act g E)) * v E
      = ∑' g, ENNReal.ofReal (μ g) * ∑' E, u (act g E) * v E := by
        simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_comm]
        exact tsum_congr fun g => tsum_congr fun E => by ring
    _ = ∑' g, ENNReal.ofReal (μ g) * ∑' E, u E * v (act g⁻¹ E) := by
        refine tsum_congr fun g => ?_
        congr 1
        rw [← (actEquiv (X := X) g⁻¹).tsum_eq]
        exact tsum_congr fun E => by simp [act_act_inv]
    _ = ∑' g, ENNReal.ofReal (μ g) * ∑' E, u E * v (act g E) := by
        rw [← (Equiv.inv G).tsum_eq]
        exact tsum_congr fun g => by simp [hsymm]
    _ = ∑' E, u E * ∑' g, ENNReal.ofReal (μ g) * v (act g E) := by
        simp_rw [← ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_comm]
        exact tsum_congr fun g => tsum_congr fun E => by ring

lemma inr_Rop {μ : G → ℝ} (hsymm : ∀ g, μ g⁻¹ = μ g) {x₀ : X} {u v : Finset X → ℝ≥0∞}
    (hu : TInv x₀ u) (hv : TInv x₀ v) : inr (Rop μ x₀ u) v = inr u (Rop μ x₀ v) := by
  rw [Rop_apply, Rop_apply, inr_Top, Top_of_TInv hv, inr_Pop hsymm, ← Top_of_TInv hu,
    inr_Top, Top_of_TInv hu]

lemma inr_Rop_pow {μ : G → ℝ} (hsymm : ∀ g, μ g⁻¹ = μ g) {x₀ : X} {u v : Finset X → ℝ≥0∞}
    (hu : TInv x₀ u) (hv : TInv x₀ v) (a : ℕ) :
    inr ((Rop μ x₀ ^ a) u) v = inr u ((Rop μ x₀ ^ a) v) := by
  induction a generalizing v with
  | zero => simp
  | succ a ih =>
    rw [pow_succ', Module.End.mul_apply, inr_Rop hsymm (TInv_Rop_pow μ x₀ hu a) hv, ih
      (TInv_Rop μ x₀ v), ← Module.End.mul_apply, ← pow_succ, pow_succ']

/-! ## The explicit formula -/

/-- The weight `2^{-|O|}`. -/
noncomputable def wgt (O : Finset X) : ℝ≥0∞ := (2⁻¹ : ℝ≥0∞) ^ O.card

/-- `Z j D E = E[2^{-|O_j|} 1(E ∆ g_j⁻¹ D ⊆ O_j)]`, the iterate `(TP)^j T δ_D` at `E`. -/
noncomputable def Z (μ : G → ℝ) (x₀ : X) (j : ℕ) (D E : Finset X) : ℝ≥0∞ :=
  wE μ j (fun h => wgt (invertedOrbit x₀ h) *
    if E ∆ act (walkPos h j)⁻¹ D ⊆ invertedOrbit x₀ h then 1 else 0)

/-- `pE j = E[2^{-|O_j|}]`. -/
noncomputable def pE (μ : G → ℝ) (x₀ : X) (j : ℕ) : ℝ≥0∞ :=
  wE μ j (fun h => wgt (invertedOrbit x₀ h))

/-- The indicator of the singleton `{D}`. -/
noncomputable def dlt (D : Finset X) : Finset X → ℝ≥0∞ := fun E => if E = D then 1 else 0

lemma wgt_insert_of_not_mem {x : X} {A : Finset X} (hx : x ∉ A) :
    wgt (insert x A) = wgt A * 2⁻¹ := by
  unfold wgt; rw [Finset.card_insert_of_notMem hx, pow_succ]

/-- The key finite-set identity behind `Z (j+1) = T P Z j`. -/
lemma toggle_avg (x₀ : X) (F A : Finset X) :
    ((wgt A * if F ⊆ A then 1 else 0) + (wgt A * if tog x₀ F ⊆ A then 1 else 0)) * 2⁻¹ =
      wgt (insert x₀ A) * if F ⊆ insert x₀ A then 1 else 0 := by
  by_cases hA : x₀ ∈ A
  · rw [Finset.insert_eq_of_mem hA]
    have : tog x₀ F ⊆ A ↔ F ⊆ A := by
      constructor
      · intro h y hy
        by_cases hyx : y = x₀
        · rw [hyx]; exact hA
        · exact h (by simp [tog, Finset.mem_symmDiff, hy, hyx])
      · intro h y hy
        simp only [tog, Finset.mem_symmDiff, Finset.mem_singleton] at hy
        rcases hy with ⟨hy, _⟩ | ⟨rfl, _⟩
        · exact h hy
        · exact hA
    rw [if_congr this rfl rfl, ← mul_add, ← two_mul, mul_assoc, mul_comm (2 : ℝ≥0∞),
      mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
  · rw [wgt_insert_of_not_mem hA]
    by_cases hF : F ⊆ insert x₀ A
    · by_cases hxF : x₀ ∈ F
      · have h1 : ¬ F ⊆ A := fun h => hA (h hxF)
        have h2 : tog x₀ F ⊆ A := by
          intro y hy
          simp only [tog, Finset.mem_symmDiff, Finset.mem_singleton] at hy
          rcases hy with ⟨hy, hyx⟩ | ⟨rfl, hn⟩
          · rcases Finset.mem_insert.1 (hF hy) with h | h
            · exact absurd h hyx
            · exact h
          · exact absurd hxF hn
        simp [h1, h2, hF]
      · have h1 : F ⊆ A := by
          intro y hy
          rcases Finset.mem_insert.1 (hF hy) with h | h
          · exact absurd (h ▸ hy) hxF
          · exact h
        have h2 : ¬ tog x₀ F ⊆ A := by
          intro h
          exact hA (h (by simp [tog, Finset.mem_symmDiff, hxF]))
        simp [h1, h2, hF]
    · have h1 : ¬ F ⊆ A := fun h => hF (h.trans (Finset.subset_insert _ _))
      have h2 : ¬ tog x₀ F ⊆ A := by
        intro h
        apply hF
        intro y hy
        by_cases hyx : y = x₀
        · rw [hyx]; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (h (by simp [tog, Finset.mem_symmDiff, hy, hyx]))
      simp [h1, h2, hF]

lemma Z_zero (μ : G → ℝ) (x₀ : X) (D : Finset X) : Z μ x₀ 0 D = Top x₀ (dlt D) := by
  funext E
  rw [Z, wE_zero, invertedOrbit_zero, walkPos_zero', inv_one, act_one, Top_apply]
  simp only [wgt, Finset.card_singleton, pow_one, dlt]
  by_cases h1 : E = D
  · subst h1
    have : tog x₀ E ≠ E := by
      intro h
      have := congrArg (fun F => x₀ ∈ F) h
      simp [tog, Finset.mem_symmDiff] at this
    simp [this]
  · by_cases h2 : tog x₀ E = D
    · subst h2
      have hsub : E ∆ tog x₀ E ⊆ {x₀} := by
        unfold tog; rw [← symmDiff_assoc, symmDiff_self, bot_symmDiff]
      simp [h1, hsub]
    · have hsub : ¬ E ∆ D ⊆ {x₀} := by
        intro h
        rcases Finset.subset_singleton_iff.1 h with h | h
        · exact h1 (symmDiff_eq_bot.1 h)
        · apply h2
          unfold tog
          rw [← h, ← symmDiff_assoc, symmDiff_self, bot_symmDiff]
      simp [h1, h2, hsub]

lemma Z_succ (μ : G → ℝ) (x₀ : X) (j : ℕ) (D : Finset X) :
    Z μ x₀ (j + 1) D = Rop μ x₀ (Z μ x₀ j D) := by
  funext E
  rw [Rop_apply, Top_apply, Pop_apply, Pop_apply, ← ENNReal.tsum_add, ← ENNReal.tsum_mul_right,
    Z, wE_succ]
  refine tsum_congr fun g => ?_
  rw [← mul_add, mul_assoc]
  congr 1
  simp only [Z]
  rw [← wE_add, mul_comm, ← wE_mul_left]
  congr 1
  funext h
  rw [invertedOrbit_cons, walkPos_full_cons, mul_comm (2⁻¹ : ℝ≥0∞)]
  set O := invertedOrbit x₀ h
  set k := walkPos h j
  have e1 : ∀ E' : Finset X, (act g E' ∆ act k⁻¹ D ⊆ O ↔
      E' ∆ act (k * g)⁻¹ D ⊆ act g⁻¹ O) := by
    intro E'
    rw [← act_subset_act (g := g⁻¹), act_symmDiff, act_inv_act, ← act_mul, ← mul_inv_rev]
  rw [if_congr (e1 E) rfl rfl, if_congr (e1 (tog x₀ E)) rfl rfl]
  have e2 : tog x₀ E ∆ act (k * g)⁻¹ D = tog x₀ (E ∆ act (k * g)⁻¹ D) := by
    unfold tog
    rw [symmDiff_assoc, symmDiff_comm ({x₀} : Finset X), ← symmDiff_assoc]
  have e3 : wgt O = wgt (act g⁻¹ O) := by unfold wgt; rw [card_act]
  rw [e2, e3]
  exact (toggle_avg x₀ _ _).symm

lemma Rop_pow_Z (μ : G → ℝ) (x₀ : X) (D : Finset X) (j : ℕ) :
    (Rop μ x₀ ^ j) (Z μ x₀ 0 D) = Z μ x₀ j D := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', Module.End.mul_apply, ih, Z_succ]

lemma TInv_Z (μ : G → ℝ) (x₀ : X) (j : ℕ) (D : Finset X) : TInv x₀ (Z μ x₀ j D) := by
  cases j with
  | zero => rw [Z_zero]; exact TInv_Top x₀ _
  | succ j => rw [Z_succ]; exact TInv_Rop μ x₀ _

lemma Z_le_pE (μ : G → ℝ) (x₀ : X) (j : ℕ) (D E : Finset X) : Z μ x₀ j D E ≤ pE μ x₀ j := by
  refine wE_mono μ j fun h => ?_
  split_ifs <;> simp

lemma Z_empty (μ : G → ℝ) (x₀ : X) (j : ℕ) : Z μ x₀ j ∅ ∅ = pE μ x₀ j := by
  unfold Z pE
  congr 1
  funext h
  have : (∅ : Finset X) ∆ act (walkPos h j)⁻¹ ∅ ⊆ invertedOrbit x₀ h := by
    have : act (walkPos h j)⁻¹ (∅ : Finset X) = ∅ := by simp [act]
    rw [this]; simp
  simp [this]

lemma inr_dlt (D : Finset X) (u : Finset X → ℝ≥0∞) : inr (dlt D) u = u D := by
  unfold inr dlt
  rw [tsum_eq_single D (fun E hE => by simp [hE])]
  simp

lemma inr_Z0 {μ : G → ℝ} {x₀ : X} (D : Finset X) {u : Finset X → ℝ≥0∞} (hu : TInv x₀ u) :
    inr (Z μ x₀ 0 D) u = u D := by
  rw [Z_zero, inr_Top, Top_of_TInv hu, inr_dlt]

lemma inr_Z {μ : G → ℝ} (hsymm : ∀ g, μ g⁻¹ = μ g) (x₀ : X) (a b : ℕ) (D D' : Finset X) :
    inr (Z μ x₀ a D) (Z μ x₀ b D') = Z μ x₀ (a + b) D' D := by
  rw [← Rop_pow_Z μ x₀ D a, inr_Rop_pow hsymm (TInv_Z μ x₀ 0 D) (TInv_Z μ x₀ b D'),
    ← Rop_pow_Z μ x₀ D' b, ← Module.End.mul_apply, ← pow_add, Rop_pow_Z,
    inr_Z0 D (TInv_Z μ x₀ _ D')]

lemma pE_add {μ : G → ℝ} (hsymm : ∀ g, μ g⁻¹ = μ g) (x₀ : X) (a b : ℕ) :
    inr (Z μ x₀ a ∅) (Z μ x₀ b ∅) = pE μ x₀ (a + b) := by
  rw [inr_Z hsymm, Z_empty]

lemma pE_mul_le {μ : G → ℝ} (hsymm : ∀ g, μ g⁻¹ = μ g) (x₀ : X) (a b : ℕ) :
    pE μ x₀ a * pE μ x₀ b ≤ pE μ x₀ (a + b) := by
  rw [← pE_add hsymm, ← Z_empty μ x₀ a, ← Z_empty μ x₀ b]
  exact ENNReal.le_tsum (f := fun E => Z μ x₀ a ∅ E * Z μ x₀ b ∅ E) ∅

end Ops

end JMMS.IETP41

/-! # JMMS Proposition 4.1, part B: the elementary equivalences (i) ⇔ (ii) ⇔ (iii). -/

open IntervalExchange Filter Topology
open scoped ENNReal symmDiff

set_option linter.unusedSectionVars false

namespace JMMS.IETP41

/-! ## Fekete's lemma for a supermultiplicative sequence in `(0, 1]` -/

lemma rate_eq (p : ℝ) (n : ℕ) : -(1 / (n : ℝ)) * Real.log p = (-Real.log p) / n := by ring

lemma fekete_tendsto (p : ℕ → ℝ) (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n ≤ 1)
    (hmul : ∀ a b, p a * p b ≤ p (a + b))
    (hsmall : ∀ ε > 0, ∃ n : ℕ, n ≠ 0 ∧ -(1 / (n : ℝ)) * Real.log (p n) ≤ ε) :
    Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log (p n)) atTop (𝓝 0) := by
  set u : ℕ → ℝ := fun n => -Real.log (p n) with hu
  have hsub : Subadditive u := by
    intro a b
    simp only [hu]
    have := Real.log_le_log (mul_pos (hp0 a) (hp0 b)) (hmul a b)
    rw [Real.log_mul (hp0 a).ne' (hp0 b).ne'] at this
    linarith
  have hnn : ∀ n : ℕ, 0 ≤ u n / n := fun n => by
    simp only [hu]
    have := Real.log_nonpos (hp0 n).le (hp1 n)
    exact div_nonneg (by linarith) (Nat.cast_nonneg n)
  have hbdd : BddBelow (Set.range fun n => u n / n) := ⟨0, by rintro _ ⟨n, rfl⟩; exact hnn n⟩
  have ht := hsub.tendsto_lim hbdd
  have hL0 : 0 ≤ hsub.lim := ge_of_tendsto ht (Eventually.of_forall hnn)
  have hL1 : hsub.lim ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨n, hn, hle⟩ := hsmall ε hε
    have := hsub.lim_le_div hbdd hn
    rw [rate_eq] at hle
    simp only [hu] at this
    linarith
  have : hsub.lim = 0 := le_antisymm hL1 hL0
  rw [this] at ht
  refine ht.congr fun n => ?_
  simp only [hu]
  rw [rate_eq]

/-! ## Expectations of bounded functions -/

section Real

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X]

/-- The weight of a path of steps. -/
noncomputable def wt (μ : G → ℝ) {n : ℕ} (h : Fin n → G) : ℝ := ∏ i, μ (h i)

lemma wt_nonneg {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) {n : ℕ} (h : Fin n → G) :
    0 ≤ wt μ h := Finset.prod_nonneg fun _ _ => hμ.1 _

lemma hasSum_wt {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) (n : ℕ) :
    HasSum (fun h : Fin n → G => wt μ h) 1 := by
  have h1 := wE_one hμ n
  unfold wE at h1
  simp only [mul_one] at h1
  have hne : ∑' h : Fin n → G, ∏ i, ENNReal.ofReal (μ (h i)) ≠ ∞ := by rw [h1]; simp
  have hs := ENNReal.summable_toReal hne
  have heq : ∀ h : Fin n → G, (∏ i, ENNReal.ofReal (μ (h i))).toReal = wt μ h := by
    intro h
    rw [ENNReal.toReal_prod]
    exact Finset.prod_congr rfl fun i _ => ENNReal.toReal_ofReal (hμ.1 _)
  simp only [heq] at hs
  refine hs.hasSum_iff.2 ?_
  rw [← tsum_congr heq, ← ENNReal.tsum_toReal_eq
    (fun _ => ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top), h1, ENNReal.toReal_one]

lemma walkExp_eq_wt (μ : G → ℝ) (n : ℕ) (F : (Fin n → G) → ℝ) :
    walkExp μ n F = ∑' h, wt μ h * F h := rfl

lemma summable_wt_mul {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) {n : ℕ}
    {F : (Fin n → G) → ℝ} (C : ℝ) (hF : ∀ h, |F h| ≤ C) :
    Summable (fun h => wt μ h * F h) := by
  refine Summable.of_norm_bounded ((hasSum_wt hμ n).summable.mul_right C) fun h => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (wt_nonneg hμ h)]
  exact mul_le_mul_of_nonneg_left (hF h) (wt_nonneg hμ h)

lemma walkExp_mono {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) {n : ℕ}
    {F F' : (Fin n → G) → ℝ} (C : ℝ) (hF : ∀ h, |F h| ≤ C) (hF' : ∀ h, |F' h| ≤ C)
    (hle : ∀ h, F h ≤ F' h) : walkExp μ n F ≤ walkExp μ n F' :=
  (summable_wt_mul hμ C hF).tsum_le_tsum (fun h => mul_le_mul_of_nonneg_left (hle h)
    (wt_nonneg hμ h)) (summable_wt_mul hμ C hF')

lemma walkExp_add {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) {n : ℕ}
    {F F' : (Fin n → G) → ℝ} (C : ℝ) (hF : ∀ h, |F h| ≤ C) (hF' : ∀ h, |F' h| ≤ C) :
    walkExp μ n (fun h => F h + F' h) = walkExp μ n F + walkExp μ n F' := by
  simp only [walkExp_eq_wt]
  rw [← (summable_wt_mul hμ C hF).tsum_add (summable_wt_mul hμ C hF')]
  exact tsum_congr fun h => mul_add _ _ _

lemma walkExp_mul_left (μ : G → ℝ) (n : ℕ) (c : ℝ) (F : (Fin n → G) → ℝ) :
    walkExp μ n (fun h => c * F h) = c * walkExp μ n F := by
  unfold walkExp
  rw [← tsum_mul_left]
  exact tsum_congr fun h => by ring

lemma walkExp_const {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) (n : ℕ) (c : ℝ) :
    walkExp μ n (fun _ => c) = c := by
  rw [walkExp_eq_wt]
  rw [tsum_mul_right, (hasSum_wt hμ n).tsum_eq, one_mul]

lemma walkExp_nonneg {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) {n : ℕ}
    {F : (Fin n → G) → ℝ} (hF : ∀ h, 0 ≤ F h) : 0 ≤ walkExp μ n F :=
  tsum_nonneg fun h => mul_nonneg (wt_nonneg hμ h) (hF h)

lemma walkProb_eq (μ : G → ℝ) (n : ℕ) (A : Set (Fin n → G)) :
    walkProb μ n A = walkExp μ n (fun h => A.indicator (fun _ => (1 : ℝ)) h) := rfl

lemma abs_indicator_one_le {α : Type*} (A : Set α) (h : α) :
    |A.indicator (fun _ => (1 : ℝ)) h| ≤ 1 := by
  by_cases hh : h ∈ A <;> simp [hh]

lemma walkProb_le_one {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) {n : ℕ}
    (A : Set (Fin n → G)) : walkProb μ n A ≤ 1 := by
  rw [walkProb_eq]
  calc _ ≤ walkExp μ n (fun _ => (1 : ℝ)) :=
        walkExp_mono hμ 1 (abs_indicator_one_le A) (fun _ => by simp)
          (fun h => by by_cases hh : h ∈ A <;> simp [hh])
    _ = 1 := walkExp_const hμ n 1

/-! ## The return probability `p n = E 2^{-|O_n|}` -/

/-- `p n = E(2^{-|O_n|})`, as in the statement. -/
noncomputable def pR (μ : G → ℝ) (x₀ : X) (n : ℕ) : ℝ :=
  walkExp μ n fun h => (2 : ℝ) ^ (-((invertedOrbit x₀ h).card : ℤ))

lemma two_zpow_eq (c : ℕ) : (2 : ℝ) ^ (-(c : ℤ)) = (2⁻¹ : ℝ) ^ c := by
  rw [zpow_neg, zpow_natCast, inv_pow]

lemma two_zpow_pos (c : ℕ) : 0 < (2 : ℝ) ^ (-(c : ℤ)) := by positivity

lemma two_zpow_le_one (c : ℕ) : (2 : ℝ) ^ (-(c : ℤ)) ≤ 1 := by
  rw [two_zpow_eq]; exact pow_le_one₀ (by norm_num) (by norm_num)

lemma abs_two_zpow_le (c : ℕ) : |(2 : ℝ) ^ (-(c : ℤ))| ≤ 1 := by
  rw [abs_of_pos (two_zpow_pos c)]; exact two_zpow_le_one c

lemma ofReal_two_zpow (c : ℕ) : ENNReal.ofReal ((2 : ℝ) ^ (-(c : ℤ))) = (2⁻¹ : ℝ≥0∞) ^ c := by
  rw [two_zpow_eq, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

lemma pE_eq_ofReal {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) (x₀ : X) (n : ℕ) :
    pE μ x₀ n = ENNReal.ofReal (pR μ x₀ n) := by
  unfold pR
  rw [walkExp_eq_toReal hμ n (fun h => (two_zpow_pos _).le), ENNReal.ofReal_toReal]
  · unfold pE wgt; simp only [ofReal_two_zpow]
  · refine ne_top_of_le_ne_top ENNReal.one_ne_top (wE_le_const hμ n fun h => ?_)
    rw [ofReal_two_zpow]; exact pow_le_one₀ (by norm_num) (by norm_num)

lemma pR_le_one {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) (x₀ : X) (n : ℕ) :
    pR μ x₀ n ≤ 1 := by
  unfold pR
  rw [← walkExp_const hμ n 1]
  exact walkExp_mono hμ 1 (fun h => abs_two_zpow_le _) (fun _ => by simp)
    (fun h => two_zpow_le_one _)

lemma pR_ge {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) (x₀ : X) (n : ℕ) :
    (2⁻¹ : ℝ) ^ (n + 1) ≤ pR μ x₀ n := by
  unfold pR
  rw [← walkExp_const hμ n ((2⁻¹ : ℝ) ^ (n + 1))]
  refine walkExp_mono hμ 1 (fun _ => ?_) (fun h => abs_two_zpow_le _) (fun h => ?_)
  · rw [abs_of_pos (by positivity)]; exact pow_le_one₀ (by norm_num) (by norm_num)
  · rw [two_zpow_eq]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (card_invertedOrbit_le x₀ h)

lemma pR_pos {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) (x₀ : X) (n : ℕ) :
    0 < pR μ x₀ n := lt_of_lt_of_le (by positivity) (pR_ge hμ x₀ n)

lemma pR_mul_le {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) (hsymm : ∀ g, μ g⁻¹ = μ g)
    (x₀ : X) (a b : ℕ) : pR μ x₀ a * pR μ x₀ b ≤ pR μ x₀ (a + b) := by
  have := pE_mul_le hsymm x₀ a b
  rw [pE_eq_ofReal hμ, pE_eq_ofReal hμ, pE_eq_ofReal hμ,
    ← ENNReal.ofReal_mul (pR_pos hμ x₀ a).le] at this
  exact (ENNReal.ofReal_le_ofReal_iff (pR_pos hμ x₀ _).le).1 this

/-! ## (i) ⇒ (ii) -/

lemma rate_nonneg {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) (x₀ : X) (n : ℕ) :
    0 ≤ -(1 / (n : ℝ)) * Real.log (pR μ x₀ n) := by
  rw [rate_eq]
  have := Real.log_nonpos (pR_pos hμ x₀ n).le (pR_le_one hμ x₀ n)
  have : 0 ≤ -Real.log (pR μ x₀ n) := by linarith
  positivity

lemma i_to_ii {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) (x₀ : X)
    (h1 : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log (pR μ x₀ n)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
      Real.exp (-(ε * n)) < walkProb μ n {h | ((invertedOrbit x₀ h).card : ℝ) < ε * n} := by
  intro ε hε
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl21 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hev1 : ∀ᶠ n : ℕ in atTop, -(1 / (n : ℝ)) * Real.log (pR μ x₀ n) < ε * Real.log 2 / 2 :=
    (tendsto_order.1 h1).2 _ (by positivity)
  have hev2 : ∀ᶠ n : ℕ in atTop, Real.log 2 / n < ε * Real.log 2 / 2 := by
    have : Tendsto (fun n : ℕ => Real.log 2 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    exact (tendsto_order.1 this).2 _ (by positivity)
  obtain ⟨n, hn1, hn2, hn3, hn0⟩ :=
    (hcon.and (hev1.and (hev2.and (eventually_ge_atTop 1)))).exists
  push Not at hn1
  set A : Set (Fin n → G) := {h | ((invertedOrbit x₀ h).card : ℝ) < ε * n}
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  -- Markov: `2^{-|O|} ≤ 1_A + exp(-ε n log 2)`
  have hpt : ∀ h : Fin n → G, (2 : ℝ) ^ (-((invertedOrbit x₀ h).card : ℤ)) ≤
      A.indicator (fun _ => (1 : ℝ)) h + Real.exp (-(ε * n) * Real.log 2) := by
    intro h
    by_cases hh : h ∈ A
    · simp only [Set.indicator_of_mem hh]
      linarith [two_zpow_le_one (invertedOrbit x₀ h).card, Real.exp_pos (-(ε * n) * Real.log 2)]
    · simp only [Set.indicator_of_notMem hh, zero_add]
      have hc : ε * n ≤ ((invertedOrbit x₀ h).card : ℝ) := not_lt.1 hh
      rw [two_zpow_eq, ← Real.exp_log (by positivity : (0 : ℝ) < (2⁻¹ : ℝ) ^ _),
        Real.log_pow, Real.log_inv]
      apply Real.exp_le_exp.2
      nlinarith
  set e := Real.exp (-(ε * n) * Real.log 2) with he_def
  have he : 0 < e := Real.exp_pos _
  have hp : pR μ x₀ n ≤ walkProb μ n A + e := by
    have hb1 : ∀ h, |A.indicator (fun _ => (1 : ℝ)) h| ≤ 1 + e := fun h => by
      linarith [abs_indicator_one_le A h]
    have hb2 : ∀ h : Fin n → G, |(fun _ => e) h| ≤ 1 + e := fun h => by
      simp only [abs_of_pos he]; linarith
    have hb3 : ∀ h, |A.indicator (fun _ => (1 : ℝ)) h + e| ≤ 1 + e := fun h => by
      rw [abs_of_nonneg (add_nonneg (by by_cases hh : h ∈ A <;> simp [hh]) he.le)]
      have := abs_indicator_one_le A h
      have := le_abs_self (A.indicator (fun _ => (1 : ℝ)) h)
      linarith
    calc pR μ x₀ n ≤ walkExp μ n (fun h => A.indicator (fun _ => (1 : ℝ)) h + e) :=
          walkExp_mono hμ (1 + e) (fun h => by
            linarith [abs_two_zpow_le (invertedOrbit x₀ h).card]) hb3 hpt
      _ = walkProb μ n A + e := by
          rw [walkExp_add hμ (1 + e) hb1 hb2, walkExp_const hμ]; rfl
  have hexp : Real.exp (-(ε * n)) ≤ e := by
    rw [he_def]
    apply Real.exp_le_exp.2
    have : 0 ≤ ε * n := by positivity
    nlinarith [mul_nonneg this (sub_nonneg.2 hl21.le)]
  have hp2 : pR μ x₀ n ≤ 2 * e := by linarith
  have hlog : Real.log (pR μ x₀ n) ≤ Real.log 2 + (-(ε * n) * Real.log 2) := by
    rw [← Real.log_exp (-(ε * n) * Real.log 2), ← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (pR_pos hμ x₀ n) hp2
  rw [rate_eq, div_lt_iff₀ hnpos] at hn2
  rw [div_lt_iff₀ hnpos] at hn3
  nlinarith

/-! ## (ii) ⇒ (i) -/

lemma ii_to_i {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) (hsymm : ∀ g, μ g⁻¹ = μ g)
    (x₀ : X)
    (h2 : ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
      Real.exp (-(ε * n)) < walkProb μ n {h | ((invertedOrbit x₀ h).card : ℝ) < ε * n}) :
    Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log (pR μ x₀ n)) atTop (𝓝 0) := by
  refine fekete_tendsto _ (pR_pos hμ x₀) (pR_le_one hμ x₀) (pR_mul_le hμ hsymm x₀) ?_
  intro ε hε
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set ε' := ε / (1 + Real.log 2) with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨n, hn, hn0⟩ := ((h2 ε' hε'pos).and_eventually (eventually_ge_atTop 1)).exists
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  set A : Set (Fin n → G) := {h | ((invertedOrbit x₀ h).card : ℝ) < ε' * n}
  have hpt : ∀ h : Fin n → G, Real.exp (-(ε' * n) * Real.log 2) * A.indicator (fun _ => 1) h ≤
      (2 : ℝ) ^ (-((invertedOrbit x₀ h).card : ℤ)) := by
    intro h
    by_cases hh : h ∈ A
    · simp only [Set.indicator_of_mem hh, mul_one]
      have hc : ((invertedOrbit x₀ h).card : ℝ) < ε' * n := hh
      rw [two_zpow_eq, ← Real.exp_log (by positivity : (0 : ℝ) < (2⁻¹ : ℝ) ^ _),
        Real.log_pow, Real.log_inv]
      apply Real.exp_le_exp.2
      nlinarith
    · simp only [Set.indicator_of_notMem hh, mul_zero]; exact (two_zpow_pos _).le
  have hp : Real.exp (-(ε' * n) * Real.log 2) * walkProb μ n A ≤ pR μ x₀ n := by
    unfold pR
    rw [walkProb_eq, ← walkExp_mul_left]
    refine walkExp_mono hμ 1 (fun h => ?_) (fun h => abs_two_zpow_le _) hpt
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-(ε' * n) * Real.log 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ ε' * n := by positivity
      nlinarith
    calc Real.exp (-(ε' * n) * Real.log 2) * |A.indicator (fun _ => (1 : ℝ)) h|
        ≤ 1 * 1 := mul_le_mul he (abs_indicator_one_le A h) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  refine ⟨n, by omega, ?_⟩
  have hlt : Real.exp (-(ε' * n) * Real.log 2) * Real.exp (-(ε' * n)) < pR μ x₀ n :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_left hn (Real.exp_pos _)) hp
  rw [← Real.exp_add] at hlt
  have hlog := Real.log_lt_log (Real.exp_pos _) hlt
  rw [Real.log_exp] at hlog
  rw [rate_eq, div_le_iff₀ hnpos]
  have : ε' * (1 + Real.log 2) = ε := by rw [hε']; field_simp
  nlinarith

/-! ## (i) ⇒ (iii) and (iii) ⇒ (i) -/

lemma abs_indicator_card_le (x₀ : X) {n : ℕ} (A : Set (Fin n → G)) (h : Fin n → G) :
    |A.indicator (fun h => ((invertedOrbit x₀ h).card : ℝ)) h| ≤ n + 1 := by
  by_cases hh : h ∈ A
  · simp only [Set.indicator_of_mem hh, Nat.abs_cast]
    exact_mod_cast card_invertedOrbit_le x₀ h
  · simp only [Set.indicator_of_notMem hh, abs_zero]; positivity

lemma i_to_iii {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) (x₀ : X)
    (h1 : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log (pR μ x₀ n)) atTop (𝓝 0)) :
    ∃ A : ∀ n : ℕ, Set (Fin n → G), (∀ n, 0 < walkProb μ n (A n)) ∧
      Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log (walkProb μ n (A n))) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (1 / (n : ℝ)) *
        ((walkExp μ n fun h => (A n).indicator (fun h => ((invertedOrbit x₀ h).card : ℝ)) h) /
          walkProb μ n (A n))) atTop (𝓝 0) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set b : ℕ → ℝ := fun n => -Real.log (pR μ x₀ n) / Real.log 2 + 2 with hb
  have hlogp : ∀ n, Real.log (pR μ x₀ n) ≤ 0 := fun n =>
    Real.log_nonpos (pR_pos hμ x₀ n).le (pR_le_one hμ x₀ n)
  have hb2 : ∀ n, 2 ≤ b n := fun n => by
    have := hlogp n
    have : 0 ≤ -Real.log (pR μ x₀ n) / Real.log 2 := div_nonneg (by linarith) hl2.le
    simp only [hb]; linarith
  set A : ∀ n : ℕ, Set (Fin n → G) := fun n => {h | ((invertedOrbit x₀ h).card : ℝ) ≤ b n}
  have hPA : ∀ n, 3 / 4 * pR μ x₀ n ≤ walkProb μ n (A n) := by
    intro n
    set p := pR μ x₀ n
    have hp0 := pR_pos hμ x₀ n
    have hpt : ∀ h : Fin n → G, (2 : ℝ) ^ (-((invertedOrbit x₀ h).card : ℤ)) ≤
        (A n).indicator (fun _ => (1 : ℝ)) h + p / 4 := by
      intro h
      by_cases hh : h ∈ A n
      · simp only [Set.indicator_of_mem hh]
        linarith [two_zpow_le_one (invertedOrbit x₀ h).card]
      · simp only [Set.indicator_of_notMem hh, zero_add]
        have hc : b n < ((invertedOrbit x₀ h).card : ℝ) := not_le.1 hh
        rw [two_zpow_eq, ← Real.exp_log (by positivity : (0 : ℝ) < (2⁻¹ : ℝ) ^ _),
          Real.log_pow, Real.log_inv]
        have e4 : p / 4 = Real.exp (Real.log p - 2 * Real.log 2) := by
          rw [Real.exp_sub, Real.exp_log hp0, show 2 * Real.log 2 = Real.log 4 by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num,
            Real.exp_log (by norm_num)]
        rw [e4]
        apply Real.exp_le_exp.2
        have : b n * Real.log 2 = -Real.log p + 2 * Real.log 2 := by
          simp only [hb]; field_simp; rfl
        nlinarith
    have hb1 : ∀ h, |(A n).indicator (fun _ => (1 : ℝ)) h| ≤ 1 + p / 4 := fun h => by
      linarith [abs_indicator_one_le (A n) h]
    have hb2' : ∀ h : Fin n → G, |(fun _ => p / 4) h| ≤ 1 + p / 4 := fun h => by
      simp only [abs_of_pos (by positivity : 0 < p / 4)]; linarith
    have hb3 : ∀ h, |(A n).indicator (fun _ => (1 : ℝ)) h + p / 4| ≤ 1 + p / 4 := fun h => by
      rw [abs_of_nonneg (add_nonneg (by by_cases hh : h ∈ A n <;> simp [hh]) (by positivity))]
      have := abs_indicator_one_le (A n) h
      have := le_abs_self ((A n).indicator (fun _ => (1 : ℝ)) h)
      linarith
    have : p ≤ walkProb μ n (A n) + p / 4 :=
      calc p ≤ walkExp μ n (fun h => (A n).indicator (fun _ => (1 : ℝ)) h + p / 4) :=
            walkExp_mono hμ (1 + p / 4) (fun h => by
              linarith [abs_two_zpow_le (invertedOrbit x₀ h).card]) hb3 hpt
        _ = walkProb μ n (A n) + p / 4 := by
            rw [walkExp_add hμ (1 + p / 4) hb1 hb2', walkExp_const hμ]; rfl
    linarith
  have hPpos : ∀ n, 0 < walkProb μ n (A n) := fun n =>
    lt_of_lt_of_le (by have := pR_pos hμ x₀ n; positivity) (hPA n)
  refine ⟨A, hPpos, ?_, ?_⟩
  · -- `0 ≤ -(1/n) log P(A) ≤ -(1/n) log p + (1/n) log (4/3)`
    have hup : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log (pR μ x₀ n) +
        Real.log (4 / 3) / n) atTop (𝓝 (0 + 0)) :=
      h1.add (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
    rw [add_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => ?_)
      (fun n => ?_)
    · have := Real.log_nonpos (hPpos n).le (walkProb_le_one hμ (A n))
      rw [rate_eq]
      exact div_nonneg (by linarith) (Nat.cast_nonneg n)
    · have hl := Real.log_le_log (by have := pR_pos hμ x₀ n; positivity) (hPA n)
      rw [Real.log_mul (by norm_num) (pR_pos hμ x₀ n).ne'] at hl
      have e : Real.log (3 / 4) = -Real.log (4 / 3) := by
        rw [← Real.log_inv]; norm_num
      simp only [rate_eq]
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
  · -- `0 ≤ (1/n) E(|O| : A) ≤ (1/n) b n`
    have hup : Tendsto (fun n : ℕ => (-(1 / (n : ℝ)) * Real.log (pR μ x₀ n)) / Real.log 2 +
        2 / n) atTop (𝓝 (0 / Real.log 2 + 0)) :=
      (h1.div_const _).add (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
    rw [zero_div, add_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => ?_)
      (fun n => ?_)
    · refine mul_nonneg (by positivity) (div_nonneg (walkExp_nonneg hμ fun h => ?_)
        (hPpos n).le)
      by_cases hh : h ∈ A n <;> simp [hh]
    · have hE : (walkExp μ n fun h => (A n).indicator
          (fun h => ((invertedOrbit x₀ h).card : ℝ)) h) ≤ b n * walkProb μ n (A n) := by
        rw [walkProb_eq, ← walkExp_mul_left]
        refine walkExp_mono hμ (n + 1 + b n) (fun h => ?_) (fun h => ?_) (fun h => ?_)
        · have := abs_indicator_card_le x₀ (A n) h
          linarith [hb2 n]
        · rw [abs_mul, abs_of_pos (by linarith [hb2 n] : 0 < b n)]
          have := abs_indicator_one_le (A n) h
          have : 0 ≤ b n := by linarith [hb2 n]
          nlinarith [abs_nonneg ((A n).indicator (fun _ => (1 : ℝ)) h)]
        · by_cases hh : h ∈ A n
          · simp only [Set.indicator_of_mem hh, mul_one]; exact hh
          · simp [Set.indicator_of_notMem hh]
      have hq : (walkExp μ n fun h => (A n).indicator
          (fun h => ((invertedOrbit x₀ h).card : ℝ)) h) / walkProb μ n (A n) ≤ b n := by
        rw [div_le_iff₀ (hPpos n)]; exact hE
      calc (1 / (n : ℝ)) * ((walkExp μ n fun h => (A n).indicator
            (fun h => ((invertedOrbit x₀ h).card : ℝ)) h) / walkProb μ n (A n))
          ≤ (1 / (n : ℝ)) * b n := mul_le_mul_of_nonneg_left hq (by positivity)
        _ = _ := by simp only [hb]; ring

lemma iii_to_i {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) (x₀ : X)
    (h3 : ∃ A : ∀ n : ℕ, Set (Fin n → G), (∀ n, 0 < walkProb μ n (A n)) ∧
      Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log (walkProb μ n (A n))) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (1 / (n : ℝ)) *
        ((walkExp μ n fun h => (A n).indicator (fun h => ((invertedOrbit x₀ h).card : ℝ)) h) /
          walkProb μ n (A n))) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log (pR μ x₀ n)) atTop (𝓝 0) := by
  obtain ⟨A, hPpos, hA1, hA2⟩ := h3
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hup := hA1.add (hA2.mul_const (Real.log 2))
  rw [zero_mul, add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (rate_nonneg hμ x₀) (fun n => ?_)
  set P := walkProb μ n (A n)
  set Ec := walkExp μ n fun h => (A n).indicator (fun h => ((invertedOrbit x₀ h).card : ℝ)) h
  set t := Ec / P
  have hP := hPpos n
  set e := Real.exp (-t * Real.log 2)
  -- Jensen through the tangent line at `t`
  have hjen : e * P ≤ pR μ x₀ n := by
    set a := e * (1 + t * Real.log 2)
    set b := -(e * Real.log 2)
    have hpt : ∀ h : Fin n → G, a * (A n).indicator (fun _ => (1 : ℝ)) h +
        b * (A n).indicator (fun h => ((invertedOrbit x₀ h).card : ℝ)) h ≤
          (2 : ℝ) ^ (-((invertedOrbit x₀ h).card : ℤ)) := by
      intro h
      by_cases hh : h ∈ A n
      · simp only [Set.indicator_of_mem hh, mul_one]
        set c := ((invertedOrbit x₀ h).card : ℝ)
        rw [two_zpow_eq, ← Real.exp_log (by positivity : (0 : ℝ) < (2⁻¹ : ℝ) ^ _),
          Real.log_pow, Real.log_inv]
        have key := Real.add_one_le_exp ((t - c) * Real.log 2)
        have e2 : Real.exp (↑(invertedOrbit x₀ h).card * -Real.log 2) =
            e * Real.exp ((t - c) * Real.log 2) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [e2]
        have he : 0 < e := Real.exp_pos _
        nlinarith
      · simp only [Set.indicator_of_notMem hh, mul_zero, add_zero]
        exact (two_zpow_pos _).le
    have hC1 : ∀ h, |a * (A n).indicator (fun _ => (1 : ℝ)) h| ≤ |a| + |b| * (n + 1) :=
      fun h => by
        rw [abs_mul]
        have := abs_indicator_one_le (A n) h
        have := abs_nonneg b
        nlinarith [abs_nonneg a, abs_nonneg ((A n).indicator (fun _ => (1 : ℝ)) h)]
    have hC2 : ∀ h, |b * (A n).indicator (fun h => ((invertedOrbit x₀ h).card : ℝ)) h| ≤
        |a| + |b| * (n + 1) := fun h => by
      rw [abs_mul]
      have := abs_indicator_card_le x₀ (A n) h
      nlinarith [abs_nonneg a, abs_nonneg b,
        abs_nonneg ((A n).indicator (fun h => ((invertedOrbit x₀ h).card : ℝ)) h)]
    have hC3 : ∀ h, |a * (A n).indicator (fun _ => (1 : ℝ)) h +
        b * (A n).indicator (fun h => ((invertedOrbit x₀ h).card : ℝ)) h| ≤
          2 * (|a| + |b| * (n + 1)) := fun h => by
      have := abs_add_le (a * (A n).indicator (fun _ => (1 : ℝ)) h)
        (b * (A n).indicator (fun h => ((invertedOrbit x₀ h).card : ℝ)) h)
      linarith [hC1 h, hC2 h]
    have hC4 : ∀ h : Fin n → G, |(2 : ℝ) ^ (-((invertedOrbit x₀ h).card : ℤ))| ≤
        2 * (|a| + |b| * (n + 1)) + 1 := fun h => by
      have := abs_two_zpow_le (invertedOrbit x₀ h).card
      nlinarith [abs_nonneg a, abs_nonneg b]
    have hlin : walkExp μ n (fun h => a * (A n).indicator (fun _ => (1 : ℝ)) h +
        b * (A n).indicator (fun h => ((invertedOrbit x₀ h).card : ℝ)) h) = a * P + b * Ec := by
      rw [walkExp_add hμ _ hC1 hC2, walkExp_mul_left, walkExp_mul_left]; rfl
    have hmono := walkExp_mono hμ (2 * (|a| + |b| * (n + 1)) + 1)
      (fun h => (hC3 h).trans (by linarith)) hC4 hpt
    rw [hlin] at hmono
    have hEc : Ec = t * P := (div_mul_cancel₀ Ec hP.ne').symm
    calc e * P = a * P + b * Ec := by rw [hEc]; simp only [a, b]; ring
      _ ≤ _ := hmono
  have hlog := Real.log_le_log (by positivity) hjen
  rw [Real.log_mul (Real.exp_pos _).ne' hP.ne', Real.log_exp] at hlog
  have hn : 0 ≤ 1 / (n : ℝ) := by positivity
  have : -(1 / (n : ℝ)) * Real.log (pR μ x₀ n) ≤
      -(1 / (n : ℝ)) * Real.log P + (1 / (n : ℝ)) * t * Real.log 2 := by nlinarith
  simpa [mul_assoc] using this

end Real

end JMMS.IETP41

/-! # JMMS Proposition 4.1, part C: (i) ⇒ extensive amenability.

If `E 2^{-|O_n|}` decays subexponentially, the normalised squares of the switch–walk–switch
iterates `W_n = (TP)^n T δ_∅` are almost invariant (Kesten's easy direction, by hand), and an
ultrafilter limit gives an invariant mean on the finite subsets charging those containing `x₀`. -/

open IntervalExchange Filter Topology
open scoped ENNReal symmDiff

set_option linter.unusedSectionVars false

namespace JMMS.IETP41

/-! ## Cauchy–Schwarz and small inequalities in `ℝ≥0∞` -/

lemma ennreal_cs {ι : Type*} (x y : ι → ℝ≥0∞) :
    (∑' i, x i * y i) ^ 2 ≤ (∑' i, x i ^ 2) * (∑' i, y i ^ 2) := by
  set A := ∑' i, x i ^ 2
  set B := ∑' i, y i ^ 2
  have hfin : ∀ s : Finset ι, ∑ i ∈ s, x i * y i ≤ A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) := by
    intro s
    have h := ENNReal.inner_le_Lp_mul_Lq s x y Real.HolderConjugate.two_two
    simp only [ENNReal.rpow_two] at h
    refine h.trans ?_
    gcongr
    · exact ENNReal.sum_le_tsum s
    · exact ENNReal.sum_le_tsum s
  have h1 : ∑' i, x i * y i ≤ A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    exact iSup_le hfin
  calc (∑' i, x i * y i) ^ 2 ≤ (A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = A * B := by
      rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (B ^ _), ← ENNReal.rpow_mul,
        ← ENNReal.rpow_mul]
      norm_num

lemma ennreal_add_sq_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  by_cases ha : a = ⊤
  · subst ha; simp
  by_cases hb : b = ⊤
  · subst hb; simp
  rw [← ENNReal.ofReal_toReal ha, ← ENNReal.ofReal_toReal hb]
  set x := a.toReal
  set y := b.toReal
  have hx : 0 ≤ x := ENNReal.toReal_nonneg
  have hy : 0 ≤ y := ENNReal.toReal_nonneg
  rw [← ENNReal.ofReal_add hx hy, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_pow hx, ← ENNReal.ofReal_pow hy, ← ENNReal.ofReal_add (by positivity)
    (by positivity), show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (x - y)])

section Ops

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X]

lemma inr_Top_le (x₀ : X) (v : Finset X → ℝ≥0∞) :
    inr (Top x₀ v) (Top x₀ v) ≤ inr v v := by
  unfold inr
  have h1 : ∑' E, v (tog x₀ E) * v (tog x₀ E) = ∑' E, v E * v E := by
    rw [← (togEquiv x₀).tsum_eq]; simp only [togEquiv_apply, tog_tog]
  calc ∑' E, Top x₀ v E * Top x₀ v E
      ≤ ∑' E, 2⁻¹ * (v E * v E + v (tog x₀ E) * v (tog x₀ E)) := by
        refine ENNReal.tsum_le_tsum fun E => ?_
        rw [Top_apply]
        have := ennreal_add_sq_le (v E) (v (tog x₀ E))
        calc (v E + v (tog x₀ E)) * 2⁻¹ * ((v E + v (tog x₀ E)) * 2⁻¹)
            = (v E + v (tog x₀ E)) ^ 2 * 2⁻¹ * 2⁻¹ := by ring
          _ ≤ 2 * (v E ^ 2 + v (tog x₀ E) ^ 2) * 2⁻¹ * 2⁻¹ := by gcongr
          _ = 2⁻¹ * (v E * v E + v (tog x₀ E) * v (tog x₀ E)) := by
            rw [mul_comm (2 : ℝ≥0∞), mul_assoc _ 2, ENNReal.mul_inv_cancel (by norm_num)
              (by norm_num)]
            ring
    _ = ∑' E, v E * v E := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, h1, ← two_mul, ← mul_assoc,
          ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

/-! ## The variance inequality for the walk operator -/

/-- `∑ (u(kE) - u(E))²`. -/
noncomputable def D1 (u : Finset X → ℝ≥0∞) (k : G) : ℝ≥0∞ :=
  ∑' E, ENNReal.ofReal (((u (act k E)).toReal - (u E).toReal) ^ 2)

lemma real_var_ineq {ι : Type*} (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw : HasSum w 1)
    (a : ι → ℝ) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) (g h : ι) :
    (∑' i, w i * a i) ^ 2 + w g * w h * (a g - a h) ^ 2 ≤ ∑' i, w i * a i ^ 2 := by
  classical
  have hs1 : Summable fun i => w i * a i :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hw0 i) (ha0 i))
      (fun i => mul_le_of_le_one_right (hw0 i) (ha1 i)) hw.summable
  have hs2 : Summable fun i => w i * a i ^ 2 :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hw0 i) (sq_nonneg _))
      (fun i => mul_le_of_le_one_right (hw0 i) (pow_le_one₀ (ha0 i) (ha1 i))) hw.summable
  set m := ∑' i, w i * a i
  set s := ∑' i, w i * a i ^ 2
  have hvar : ∑' i, w i * (a i - m) ^ 2 = s - m ^ 2 := by
    have e : ∀ i, w i * (a i - m) ^ 2 = w i * a i ^ 2 - (2 * m) * (w i * a i) + m ^ 2 * w i :=
      fun i => by ring
    simp_rw [e]
    rw [(hs2.sub (hs1.mul_left _)).tsum_add (hw.summable.mul_left _), hs2.tsum_sub
      (hs1.mul_left _), tsum_mul_left, tsum_mul_left, hw.tsum_eq]
    ring
  have hsv : Summable fun i => w i * (a i - m) ^ 2 := by
    have e : (fun i => w i * (a i - m) ^ 2) =
        fun i => w i * a i ^ 2 - (2 * m) * (w i * a i) + m ^ 2 * w i := by
      funext i; ring
    rw [e]; exact (hs2.sub (hs1.mul_left _)).add (hw.summable.mul_left _)
  have hnn : ∀ i, 0 ≤ w i * (a i - m) ^ 2 := fun i => mul_nonneg (hw0 i) (sq_nonneg _)
  have hsum1 : ∑' i, w i = 1 := hw.tsum_eq
  by_cases hgh : g = h
  · subst hgh
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      add_zero]
    have : 0 ≤ ∑' i, w i * (a i - m) ^ 2 := tsum_nonneg hnn
    linarith
  · have hpair : w g * (a g - m) ^ 2 + w h * (a h - m) ^ 2 ≤ ∑' i, w i * (a i - m) ^ 2 := by
      have := hsv.sum_le_tsum {g, h} (fun i _ => hnn i)
      rwa [Finset.sum_pair hgh] at this
    have hgh1 : w g + w h ≤ 1 := by
      have := hw.summable.sum_le_tsum {g, h} (fun i _ => hw0 i)
      rw [Finset.sum_pair hgh] at this; linarith
    have hq : w g * w h * (a g - a h) ^ 2 ≤ w g * (a g - m) ^ 2 + w h * (a h - m) ^ 2 := by
      have hg0 := hw0 g
      have hh0 := hw0 h
      set x := a g - m
      set y := a h - m
      have e : a g - a h = x - y := by simp only [x, y]; ring
      rw [e]
      nlinarith [sq_nonneg (w g * x + w h * y), mul_nonneg hg0 hh0,
        mul_nonneg (mul_nonneg hg0 hh0) (sq_nonneg (x - y)), sq_nonneg x, sq_nonneg y,
        mul_nonneg (mul_nonneg hg0 (sub_nonneg.2 hgh1)) (sq_nonneg x),
        mul_nonneg (mul_nonneg hh0 (sub_nonneg.2 hgh1)) (sq_nonneg y)]
    linarith

lemma Pop_sq_add_le {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1)
    (u : Finset X → ℝ≥0∞) (hu : ∀ E, u E ≤ 1) (g h : G) :
    inr (Pop μ u) (Pop μ u) + ENNReal.ofReal (μ g * μ h) * D1 u (g * h⁻¹) ≤ inr u u := by
  have hfin : ∀ E, u E ≠ ⊤ := fun E => ne_top_of_le_ne_top ENNReal.one_ne_top (hu E)
  -- per `E`
  have hE : ∀ E, Pop μ u E * Pop μ u E + ENNReal.ofReal (μ g * μ h) *
      ENNReal.ofReal (((u (act g E)).toReal - (u (act h E)).toReal) ^ 2) ≤
        ∑' g', ENNReal.ofReal (μ g') * (u (act g' E) * u (act g' E)) := by
    intro E
    set a : G → ℝ := fun g' => (u (act g' E)).toReal
    have ha0 : ∀ i, 0 ≤ a i := fun i => ENNReal.toReal_nonneg
    have ha1 : ∀ i, a i ≤ 1 := fun i => by
      have := ENNReal.toReal_mono ENNReal.one_ne_top (hu (act i E)); simpa using this
    have hs1 : Summable fun i => μ i * a i :=
      Summable.of_nonneg_of_le (fun i => mul_nonneg (hμ.1 i) (ha0 i))
        (fun i => mul_le_of_le_one_right (hμ.1 i) (ha1 i)) hμ.2.summable
    have hs2 : Summable fun i => μ i * a i ^ 2 :=
      Summable.of_nonneg_of_le (fun i => mul_nonneg (hμ.1 i) (sq_nonneg _))
        (fun i => mul_le_of_le_one_right (hμ.1 i) (pow_le_one₀ (ha0 i) (ha1 i))) hμ.2.summable
    have hua : ∀ i, u (act i E) = ENNReal.ofReal (a i) := fun i =>
      (ENNReal.ofReal_toReal (hfin _)).symm
    have hP : Pop μ u E = ENNReal.ofReal (∑' i, μ i * a i) := by
      rw [Pop_apply, ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (hμ.1 i) (ha0 i)) hs1]
      exact tsum_congr fun i => by rw [hua, ENNReal.ofReal_mul (hμ.1 i)]
    have hS : ∑' g', ENNReal.ofReal (μ g') * (u (act g' E) * u (act g' E)) =
        ENNReal.ofReal (∑' i, μ i * a i ^ 2) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (hμ.1 i) (sq_nonneg _)) hs2]
      exact tsum_congr fun i => by
        rw [hua, ← ENNReal.ofReal_mul (ha0 i), ← ENNReal.ofReal_mul (hμ.1 i), sq]
    rw [hP, hS, ← ENNReal.ofReal_mul (tsum_nonneg fun i => mul_nonneg (hμ.1 i) (ha0 i)),
      ← ENNReal.ofReal_mul (mul_nonneg (hμ.1 g) (hμ.1 h)),
      ← ENNReal.ofReal_add (mul_self_nonneg _)
        (mul_nonneg (mul_nonneg (hμ.1 g) (hμ.1 h)) (sq_nonneg _))]
    apply ENNReal.ofReal_le_ofReal
    have := real_var_ineq μ hμ.1 hμ.2 a ha0 ha1 g h
    simp only [a] at this ⊢
    nlinarith [this]
  -- sum over `E`
  have hR : ∑' E, ∑' g', ENNReal.ofReal (μ g') * (u (act g' E) * u (act g' E)) = inr u u := by
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left]
    have : ∀ g' : G, ∑' E, u (act g' E) * u (act g' E) = inr u u := fun g' => by
      unfold inr; exact (actEquiv g').tsum_eq (fun E => u E * u E)
    simp_rw [this, ENNReal.tsum_mul_right, tsum_ofReal_eq_one hμ, one_mul]
  have hD : D1 u (g * h⁻¹) =
      ∑' E, ENNReal.ofReal (((u (act g E)).toReal - (u (act h E)).toReal) ^ 2) := by
    unfold D1
    rw [← (actEquiv (X := X) h).tsum_eq]
    refine tsum_congr fun E => ?_
    simp only [actEquiv_apply]
    rw [← act_mul, mul_assoc, inv_mul_cancel, mul_one]
  calc inr (Pop μ u) (Pop μ u) + ENNReal.ofReal (μ g * μ h) * D1 u (g * h⁻¹)
      = ∑' E, (Pop μ u E * Pop μ u E + ENNReal.ofReal (μ g * μ h) *
          ENNReal.ofReal (((u (act g E)).toReal - (u (act h E)).toReal) ^ 2)) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, hD]; rfl
    _ ≤ _ := ENNReal.tsum_le_tsum hE
    _ = inr u u := hR

/-! ## Almost invariance of the normalised squares -/

/-- `∑_{E ∈ S} u(E)²`. -/
noncomputable def num (u : Finset X → ℝ≥0∞) (S : Set (Finset X)) : ℝ≥0∞ :=
  ∑' E, S.indicator (fun E => u E * u E) E

lemma num_univ (u : Finset X → ℝ≥0∞) : num u Set.univ = inr u u := by
  unfold num inr; simp

lemma num_union (u : Finset X → ℝ≥0∞) {S S' : Set (Finset X)} (h : Disjoint S S') :
    num u (S ∪ S') = num u S + num u S' := by
  unfold num
  rw [← ENNReal.tsum_add]
  exact tsum_congr fun E => congrFun (Set.indicator_union_of_disjoint h _) E

lemma num_le (u : Finset X → ℝ≥0∞) (S : Set (Finset X)) : num u S ≤ inr u u := by
  rw [← num_univ]
  exact ENNReal.tsum_le_tsum fun E => Set.indicator_le_indicator_of_subset
    (Set.subset_univ _) (fun _ => zero_le) E

lemma num_image (u : Finset X → ℝ≥0∞) (k : G) (S : Set (Finset X)) :
    num u (act k '' S) = ∑' E, S.indicator (fun E => u (act k E) * u (act k E)) E := by
  unfold num
  rw [← (actEquiv (X := X) k).tsum_eq]
  refine tsum_congr fun E => ?_
  simp only [actEquiv_apply]
  have : act k E ∈ act k '' S ↔ E ∈ S :=
    ⟨fun ⟨E', hE', he⟩ => by
      have := congrArg (act k⁻¹) he
      rwa [act_inv_act, act_inv_act] at this ▸ hE', fun h => ⟨E, h, rfl⟩⟩
  by_cases hE : E ∈ S
  · rw [Set.indicator_of_mem (this.2 hE), Set.indicator_of_mem hE]
  · rw [Set.indicator_of_notMem (fun h => hE (this.1 h)), Set.indicator_of_notMem hE]

lemma num_image_le (u : Finset X → ℝ≥0∞) (hu : ∀ E, u E ≤ 1) (k : G) (S : Set (Finset X)) :
    ∃ B : ℝ≥0∞, num u (act k '' S) ≤ num u S + B ∧ B ^ 2 ≤ 4 * D1 u k * inr u u := by
  have hfin : ∀ E, u E ≠ ⊤ := fun E => ne_top_of_le_ne_top ENNReal.one_ne_top (hu E)
  set x : Finset X → ℝ := fun E => (u (act k E)).toReal
  set y : Finset X → ℝ := fun E => (u E).toReal
  refine ⟨∑' E, ENNReal.ofReal |x E - y E| * ENNReal.ofReal (x E + y E), ?_, ?_⟩
  · rw [num_image, num, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun E => ?_
    have hx : u (act k E) = ENNReal.ofReal (x E) := (ENNReal.ofReal_toReal (hfin _)).symm
    have hy : u E = ENNReal.ofReal (y E) := (ENNReal.ofReal_toReal (hfin _)).symm
    have hx0 : 0 ≤ x E := ENNReal.toReal_nonneg
    have hy0 : 0 ≤ y E := ENNReal.toReal_nonneg
    by_cases hE : E ∈ S
    · rw [Set.indicator_of_mem hE, Set.indicator_of_mem hE, hx, hy,
        ← ENNReal.ofReal_mul hx0, ← ENNReal.ofReal_mul hy0, ← ENNReal.ofReal_mul (abs_nonneg _),
        ← ENNReal.ofReal_add (mul_self_nonneg _) (mul_nonneg (abs_nonneg _) (by positivity))]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [le_abs_self (x E - y E)]
    · rw [Set.indicator_of_notMem hE, Set.indicator_of_notMem hE, zero_add]; exact zero_le
  · refine (ennreal_cs _ _).trans ?_
    have h1 : ∑' E, ENNReal.ofReal |x E - y E| ^ 2 = D1 u k := by
      unfold D1
      refine tsum_congr fun E => ?_
      rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    have h2 : ∑' E, ENNReal.ofReal (x E + y E) ^ 2 ≤ 4 * inr u u := by
      have hxx : ∑' E, u (act k E) * u (act k E) = inr u u := by
        unfold inr; exact (actEquiv k).tsum_eq (fun E => u E * u E)
      calc ∑' E, ENNReal.ofReal (x E + y E) ^ 2
          ≤ ∑' E, 2 * (u (act k E) * u (act k E) + u E * u E) := by
            refine ENNReal.tsum_le_tsum fun E => ?_
            rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
            simp only [ENNReal.ofReal_toReal (hfin _)]
            have := ennreal_add_sq_le (u (act k E)) (u E)
            simpa [sq] using this
        _ = 4 * inr u u := by
            rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, hxx]
            unfold inr
            rw [← two_mul, ← mul_assoc]; norm_num
    rw [h1]
    calc D1 u k * ∑' E, ENNReal.ofReal (x E + y E) ^ 2 ≤ D1 u k * (4 * inr u u) := by gcongr
      _ = 4 * D1 u k * inr u u := by ring

lemma D1_inv (u : Finset X → ℝ≥0∞) (k : G) : D1 u k⁻¹ = D1 u k := by
  unfold D1
  rw [← (actEquiv (X := X) k).tsum_eq]
  refine tsum_congr fun E => ?_
  simp only [actEquiv_apply, act_inv_act]
  rw [← neg_sub, neg_sq]

/-- The normalised square `ν(S) = ∑_{E ∈ S} u(E)² / ∑ u²`, as a real number. -/
noncomputable def nu (u : Finset X → ℝ≥0∞) (S : Set (Finset X)) : ℝ :=
  (num u S).toReal / (inr u u).toReal

lemma nu_sub_sq (u : Finset X → ℝ≥0∞) (hu : ∀ E, u E ≤ 1) (hN : inr u u ≠ 0)
    (hNt : inr u u ≠ ⊤) (k : G) (S : Set (Finset X)) :
    (nu u (act k '' S) - nu u S) ^ 2 ≤ 4 * (D1 u k).toReal / (inr u u).toReal := by
  have hNr : 0 < (inr u u).toReal := ENNReal.toReal_pos hN hNt
  obtain ⟨B, hB1, hB2⟩ := num_image_le u hu k S
  obtain ⟨B', hB1', hB2'⟩ := num_image_le u hu k⁻¹ (act k '' S)
  have hSS : act k⁻¹ '' (act k '' S) = S := by
    rw [Set.image_image]
    conv_rhs => rw [← Set.image_id S]
    exact Set.image_congr fun E _ => act_inv_act k E
  rw [hSS] at hB1'
  rw [D1_inv] at hB2'
  have hfinD : D1 u k ≠ ⊤ := by
    have h4 : D1 u k ≤ 4 * inr u u := by
      unfold D1
      have hfin : ∀ E, u E ≠ ⊤ := fun E => ne_top_of_le_ne_top ENNReal.one_ne_top (hu E)
      have hxx : ∑' E, u (act k E) * u (act k E) = inr u u := by
        unfold inr; exact (actEquiv k).tsum_eq (fun E => u E * u E)
      calc ∑' E, ENNReal.ofReal (((u (act k E)).toReal - (u E).toReal) ^ 2)
          ≤ ∑' E, 2 * (u (act k E) * u (act k E) + u E * u E) := by
            refine ENNReal.tsum_le_tsum fun E => ?_
            rw [← ENNReal.ofReal_toReal (hfin (act k E)), ← ENNReal.ofReal_toReal (hfin E)]
            rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul
              ENNReal.toReal_nonneg, ← ENNReal.ofReal_add (mul_self_nonneg _)
              (mul_self_nonneg _), show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
              ← ENNReal.ofReal_mul (by norm_num), ENNReal.toReal_ofReal ENNReal.toReal_nonneg,
              ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
            apply ENNReal.ofReal_le_ofReal
            nlinarith [sq_nonneg ((u (act k E)).toReal + (u E).toReal)]
        _ = 4 * inr u u := by
            rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, hxx]
            unfold inr
            rw [← two_mul, ← mul_assoc]; norm_num
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) hNt) h4
  have hBt : B ≠ ⊤ := by
    intro h; rw [h] at hB2; simp at hB2
    exact absurd hB2 (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hfinD) hNt)
  have hBt' : B' ≠ ⊤ := by
    intro h; rw [h] at hB2'; simp at hB2'
    exact absurd hB2' (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hfinD) hNt)
  have hn1 : num u (act k '' S) ≠ ⊤ := ne_top_of_le_ne_top hNt (num_le u _)
  have hn2 : num u S ≠ ⊤ := ne_top_of_le_ne_top hNt (num_le u _)
  set a := (num u (act k '' S)).toReal
  set b := (num u S).toReal
  set N := (inr u u).toReal
  set D := (D1 u k).toReal
  have r1 : a ≤ b + B.toReal := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hn2, hBt⟩) hB1
    rwa [ENNReal.toReal_add hn2 hBt] at this
  have r2 : b ≤ a + B'.toReal := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hn1, hBt'⟩) hB1'
    rwa [ENNReal.toReal_add hn1 hBt'] at this
  have q1 : B.toReal ^ 2 ≤ 4 * D * N := by
    have := ENNReal.toReal_mono (by finiteness) hB2
    simpa [ENNReal.toReal_mul, ENNReal.toReal_pow] using this
  have q2 : B'.toReal ^ 2 ≤ 4 * D * N := by
    have := ENNReal.toReal_mono (by finiteness) hB2'
    simpa [ENNReal.toReal_mul, ENNReal.toReal_pow] using this
  have hB0 : 0 ≤ B.toReal := ENNReal.toReal_nonneg
  have hB0' : 0 ≤ B'.toReal := ENNReal.toReal_nonneg
  have hab : (a - b) ^ 2 ≤ 4 * D * N := by
    rcases le_total a b with h | h
    · nlinarith
    · nlinarith
  unfold nu
  rw [← sub_div, div_pow, div_le_div_iff₀ (by positivity) hNr]
  nlinarith

end Ops

/-! ## Assembly: (i) ⇒ extensive amenability -/

section Assemble

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X]

lemma ratio_close {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) (x₀ : X)
    (h1 : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log (pR μ x₀ n)) atTop (𝓝 0))
    (δ : ℝ) (hδ : 0 < δ) : ∃ n : ℕ, (1 - δ) * pR μ x₀ (2 * n) ≤ pR μ x₀ (2 * n + 2) := by
  by_contra hcon
  push Not at hcon
  by_cases hδ1 : 1 ≤ δ
  · have := hcon 0
    have h0 := pR_pos hμ x₀ (2 * 0 + 2)
    have h00 := pR_pos hμ x₀ (2 * 0)
    nlinarith
  push Not at hδ1
  have hpow : ∀ n : ℕ, pR μ x₀ (2 * n) ≤ (1 - δ) ^ n := by
    intro n
    induction n with
    | zero => simpa using pR_le_one hμ x₀ 0
    | succ n ih =>
      have := hcon n
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_succ]
      nlinarith
  set c := -Real.log (1 - δ) with hc
  have hcpos : 0 < c := by
    have := Real.log_lt_log (by linarith) (show 1 - δ < 1 by linarith)
    rw [Real.log_one] at this; linarith
  have h2 : Tendsto (fun n : ℕ => -(1 / ((2 * n : ℕ) : ℝ)) * Real.log (pR μ x₀ (2 * n)))
      atTop (𝓝 0) :=
    h1.comp (tendsto_atTop_mono (fun n => (by show n ≤ 2 * n; omega)) tendsto_id)
  obtain ⟨n, hn, hn1⟩ := (((tendsto_order.1 h2).2 (c / 2) (by positivity)).and
    (eventually_ge_atTop 1)).exists
  have hnpos : (0 : ℝ) < 2 * n := by have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
                                     linarith
  have hlog : Real.log (pR μ x₀ (2 * n)) ≤ n * Real.log (1 - δ) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (pR_pos hμ x₀ _) (hpow n)
  rw [rate_eq] at hn
  push_cast at hn
  rw [div_lt_iff₀ hnpos] at hn
  nlinarith

/-- An ultrafilter limit of `[0,1]`-valued set functions. -/
lemma exists_limit {Y : Type*} (ν : ℕ → Set Y → ℝ) (h01 : ∀ j S, ν j S ∈ Set.Icc (0 : ℝ) 1) :
    ∃ L : Set Y → ℝ, ∀ S, L S ∈ Set.Icc (0 : ℝ) 1 ∧
      Tendsto (fun j => ν j S) (↑(Ultrafilter.of (atTop : Filter ℕ))) (𝓝 (L S)) := by
  have hex : ∀ S, ∃ L ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun j => ν j S) (↑(Ultrafilter.of (atTop : Filter ℕ))) (𝓝 L) := by
    intro S
    obtain ⟨L, hL, hle⟩ := isCompact_Icc.ultrafilter_le_nhds
      ((Ultrafilter.of (atTop : Filter ℕ)).map fun j => ν j S) (by
        rw [Ultrafilter.coe_map, Filter.le_principal_iff]
        exact Filter.mem_map.mpr (Filter.univ_mem' fun j => h01 j S))
    exact ⟨L, hL, by rw [Ultrafilter.coe_map] at hle; exact hle⟩
  choose L hL1 hL2 using hex
  exact ⟨L, fun S => ⟨hL1 S, hL2 S⟩⟩

lemma image_act_image (a b : G) (S : Set (Finset X)) :
    act a '' (act b '' S) = act (a * b) '' S := by
  rw [Set.image_image]; exact Set.image_congr fun E _ => (act_mul a b E).symm

lemma act_injective (g : G) : Function.Injective (act (X := X) g) :=
  (actEquiv g).injective

theorem ea_of_i {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) (hsymm : ∀ g, μ g⁻¹ = μ g)
    (hgen : Subgroup.closure (Function.support μ) = ⊤) [MulAction.IsPretransitive G X] (x₀ : X)
    (h1 : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log (pR μ x₀ n)) atTop (𝓝 0)) :
    IsExtensivelyAmenable G X := by
  have hc := fun j : ℕ => ratio_close hμ x₀ h1 (1 / ((j : ℝ) + 1)) (by positivity)
  choose n hn using hc
  set u : ℕ → Finset X → ℝ≥0∞ := fun j => Z μ x₀ (n j) ∅ with hudef
  have hpE1 : ∀ k, pE μ x₀ k ≤ 1 := fun k => by
    rw [pE_eq_ofReal hμ]; exact ENNReal.ofReal_le_one.2 (pR_le_one hμ x₀ k)
  have hu1 : ∀ j E, u j E ≤ 1 := fun j E => (Z_le_pE μ x₀ _ _ _).trans (hpE1 _)
  have hN : ∀ j, inr (u j) (u j) = ENNReal.ofReal (pR μ x₀ (2 * n j)) := fun j => by
    simp only [hudef]; rw [pE_add hsymm, ← two_mul, pE_eq_ofReal hμ]
  have hN0 : ∀ j, inr (u j) (u j) ≠ 0 := fun j => by
    rw [hN, ENNReal.ofReal_ne_zero_iff]; exact pR_pos hμ x₀ _
  have hNt : ∀ j, inr (u j) (u j) ≠ ⊤ := fun j => by rw [hN]; exact ENNReal.ofReal_ne_top
  have hNr : ∀ j, (inr (u j) (u j)).toReal = pR μ x₀ (2 * n j) := fun j => by
    rw [hN, ENNReal.toReal_ofReal (pR_pos hμ x₀ _).le]
  -- the deficit bound
  have hdef : ∀ j (g h : G), 0 < μ g → 0 < μ h →
      μ g * μ h * (D1 (u j) (g * h⁻¹)).toReal ≤
        1 / ((j : ℝ) + 1) * (inr (u j) (u j)).toReal := by
    intro j g h hg hh
    have hP := Pop_sq_add_le hμ (u j) (hu1 j) g h
    have hR : inr (Rop μ x₀ (u j)) (Rop μ x₀ (u j)) ≤ inr (Pop μ (u j)) (Pop μ (u j)) :=
      inr_Top_le x₀ _
    have hR2 : inr (Rop μ x₀ (u j)) (Rop μ x₀ (u j)) =
        ENNReal.ofReal (pR μ x₀ (2 * n j + 2)) := by
      simp only [hudef]
      rw [← Z_succ, pE_add hsymm, pE_eq_ofReal hμ]
      congr 2; ring
    rw [hR2] at hR
    have hsum : ENNReal.ofReal (pR μ x₀ (2 * n j + 2)) + ENNReal.ofReal (μ g * μ h) *
        D1 (u j) (g * h⁻¹) ≤ ENNReal.ofReal (pR μ x₀ (2 * n j)) := by
      rw [← hN]; exact (add_le_add hR le_rfl).trans hP
    have hDt : D1 (u j) (g * h⁻¹) ≠ ⊤ := by
      intro htop
      rw [htop, ENNReal.mul_top (by
        rw [ENNReal.ofReal_ne_zero_iff]; positivity)] at hsum
      simp at hsum
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDt),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pR_pos hμ x₀ _).le,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (pR_pos hμ x₀ _).le] at this
    rw [hNr]
    have := hn j
    nlinarith
  -- the normalised squares
  set ν : ℕ → Set (Finset X) → ℝ := fun j S => nu (u j) S with hν
  have hν01 : ∀ j S, ν j S ∈ Set.Icc (0 : ℝ) 1 := by
    intro j S
    refine ⟨div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg, ?_⟩
    simp only [hν, nu]
    rw [div_le_one (ENNReal.toReal_pos (hN0 j) (hNt j))]
    exact ENNReal.toReal_mono (hNt j) (num_le _ _)
  have hνadd : ∀ j S S', Disjoint S S' → ν j (S ∪ S') = ν j S + ν j S' := by
    intro j S S' hd
    simp only [hν, nu]
    rw [num_union _ hd, ENNReal.toReal_add (ne_top_of_le_ne_top (hNt j) (num_le _ _))
      (ne_top_of_le_ne_top (hNt j) (num_le _ _)), add_div]
  have hνuniv : ∀ j, ν j Set.univ = 1 := fun j => by
    simp only [hν, nu]; rw [num_univ, div_self (ENNReal.toReal_pos (hN0 j) (hNt j)).ne']
  have hνempty : ∀ j, ν j ∅ = 0 := fun j => by simp [hν, nu, num]
  have hνhalf : ∀ j, ν j {E | x₀ ∈ E} = 1 / 2 := by
    intro j
    have hT := TInv_Z μ x₀ (n j) ∅
    have heq : num (u j) {E | x₀ ∈ E} = num (u j) {E | x₀ ∉ E} := by
      unfold num
      rw [← (togEquiv x₀).tsum_eq]
      refine tsum_congr fun E => ?_
      simp only [togEquiv_apply]
      have hmem : x₀ ∈ tog x₀ E ↔ x₀ ∉ E := by simp [tog, Finset.mem_symmDiff]
      by_cases hE : x₀ ∈ E
      · rw [Set.indicator_of_notMem (show tog x₀ E ∉ {E | x₀ ∈ E} from
          fun h => (hmem.1 h) hE), Set.indicator_of_notMem (show E ∉ {E | x₀ ∉ E} from
          fun h => h hE)]
      · rw [Set.indicator_of_mem (show tog x₀ E ∈ {E | x₀ ∈ E} from hmem.2 hE),
          Set.indicator_of_mem (show E ∈ {E | x₀ ∉ E} from hE)]
        simp only [hudef] at hT ⊢
        rw [hT E]
    have hu : num (u j) {E | x₀ ∈ E} + num (u j) {E | x₀ ∉ E} = inr (u j) (u j) := by
      have hd : Disjoint ({E : Finset X | x₀ ∈ E}) {E | x₀ ∉ E} :=
        Set.disjoint_left.2 (by intro E h1 h2; exact h2 h1)
      rw [← num_union _ hd, ← num_univ]
      congr 1; ext E; simp [em]
    rw [← heq, ← two_mul] at hu
    simp only [hν, nu]
    have hne : (num (u j) {E | x₀ ∈ E}).toReal ≠ 0 := by
      intro h0
      have : (inr (u j) (u j)).toReal = 0 := by rw [← hu, ENNReal.toReal_mul, h0, mul_zero]
      exact (ENNReal.toReal_pos (hN0 j) (hNt j)).ne' this
    rw [← hu, ENNReal.toReal_mul, ENNReal.toReal_ofNat]
    field_simp
  -- the limit
  obtain ⟨L, hL⟩ := exists_limit ν hν01
  set U : Filter ℕ := ↑(Ultrafilter.of (atTop : Filter ℕ))
  have hU : U ≤ atTop := Ultrafilter.of_le _
  have huniq : ∀ S (v : ℝ), (∀ j, ν j S = v) → L S = v := fun S v hv =>
    tendsto_nhds_unique (hL S).2 (tendsto_const_nhds.congr fun j => (hv j).symm)
  have hLadd : ∀ S S', Disjoint S S' → L (S ∪ S') = L S + L S' := fun S S' hd =>
    tendsto_nhds_unique (hL (S ∪ S')).2 (((hL S).2.add (hL S').2).congr
      fun j => (hνadd j S S' hd).symm)
  have hLinvD : ∀ g h : G, 0 < μ g → 0 < μ h → ∀ S, L (act (g * h⁻¹) '' S) = L S := by
    intro g h hg hh S
    have h1' : Tendsto (fun j => (ν j (act (g * h⁻¹) '' S) - ν j S) ^ 2) U
        (𝓝 ((L (act (g * h⁻¹) '' S) - L S) ^ 2)) := ((hL _).2.sub (hL S).2).pow 2
    have h2' : Tendsto (fun j : ℕ => 4 * (1 / ((j : ℝ) + 1)) / (μ g * μ h)) U
        (𝓝 (4 * 0 / (μ g * μ h))) :=
      ((tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat).div_const _).mono_left hU
    have hle : (L (act (g * h⁻¹) '' S) - L S) ^ 2 ≤ 4 * 0 / (μ g * μ h) := by
      refine le_of_tendsto_of_tendsto h1' h2' (Eventually.of_forall fun j => ?_)
      refine (nu_sub_sq (u j) (hu1 j) (hN0 j) (hNt j) _ S).trans ?_
      have hd := hdef j g h hg hh
      have hNpos := ENNReal.toReal_pos (hN0 j) (hNt j)
      rw [div_le_div_iff₀ hNpos (by positivity)]
      nlinarith
    have : (L (act (g * h⁻¹) '' S) - L S) ^ 2 = 0 := by
      have := sq_nonneg (L (act (g * h⁻¹) '' S) - L S)
      simp at hle; nlinarith
    nlinarith [sq_nonneg (L (act (g * h⁻¹) '' S) - L S)]
  -- symmetrise over one generator
  have hsupp : ∃ s, 0 < μ s := by
    by_contra hcon
    push Not at hcon
    have h0 : μ = fun _ => 0 := funext fun g => le_antisymm (hcon g) (hμ.1 g)
    have := hμ.2
    rw [h0] at this
    exact one_ne_zero (this.unique hasSum_zero)
  obtain ⟨s, hs⟩ := hsupp
  set m : Set (Finset X) → ℝ≥0∞ := fun S => ENNReal.ofReal ((L S + L (act s '' S)) / 2)
  have hm_t : ∀ t : G, 0 < μ t → ∀ S, m (act t '' S) = m S := by
    intro t ht S
    simp only [m]
    congr 2
    have e1 : L (act t '' S) = L (act s '' S) := by
      rw [show t = t * s⁻¹ * s by group, ← image_act_image, hLinvD t s ht hs]
    have e2 : L (act s '' (act t '' S)) = L S := by
      rw [image_act_image, show s * t = s * t⁻¹⁻¹ by group, hLinvD s t⁻¹ hs (by rw [hsymm]; exact ht)]
    rw [e1, e2, add_comm]
  have hm_all : ∀ g : G, ∀ S, m (act g '' S) = m S := by
    intro g
    have hmem : g ∈ Subgroup.closure (Function.support μ) := hgen ▸ Subgroup.mem_top g
    induction hmem using Subgroup.closure_induction with
    | mem g hg => exact hm_t g (lt_of_le_of_ne (hμ.1 g) (Ne.symm hg))
    | one => intro S; rw [show act (1 : G) '' S = S by
        rw [show act (1 : G) = id from funext act_one, Set.image_id]]
    | mul g k _ _ hg hk => intro S; rw [← image_act_image, hg, hk]
    | inv g _ hg =>
      intro S
      have : S = act g '' (act g⁻¹ '' S) := by
        rw [image_act_image, mul_inv_cancel, show act (1 : G) = id from funext act_one,
          Set.image_id]
      conv_rhs => rw [this]
      rw [hg]
  have hmFA : Garrido.IsFinitelyAdditiveMeasure m := by
    refine ⟨?_, fun S S' hd => ?_⟩
    · simp only [m, Set.image_empty, huniq ∅ 0 hνempty]; simp
    · simp only [m]
      rw [Set.image_union, hLadd S S' hd, hLadd _ _ ((hd.image (act_injective s).injOn
        (Set.subset_univ _) (Set.subset_univ _))), ← ENNReal.ofReal_add (by
          linarith [(hL S).1.1, (hL (act s '' S)).1.1]) (by
          linarith [(hL S').1.1, (hL (act s '' S')).1.1])]
      congr 1; ring
  have hmuniv : m Set.univ = 1 := by
    simp only [m]
    rw [Set.image_univ_of_surjective
      (show Function.Surjective (act (X := X) s) from (actEquiv s).surjective), huniq _ 1 hνuniv]
    norm_num
  have hmpos : ∀ x : X, m {E | x ∈ E} ≠ 0 := by
    intro x
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x₀ x
    have e : {E : Finset X | g • x₀ ∈ E} = act g '' {E | x₀ ∈ E} := by
      ext E
      constructor
      · intro hE
        refine ⟨act g⁻¹ E, ?_, act_act_inv g E⟩
        show x₀ ∈ act g⁻¹ E
        rw [mem_act, inv_inv]; exact hE
      · rintro ⟨E', hE', rfl⟩
        show g • x₀ ∈ act g E'
        rw [mem_act, inv_smul_smul]; exact hE'
    rw [e, hm_all]
    simp only [m]
    rw [huniq _ (1 / 2) hνhalf, ENNReal.ofReal_ne_zero_iff]
    have := (hL (act s '' {E | x₀ ∈ E})).1.1
    linarith
  refine ((JMMS.isExtensivelyAmenable_tfae (G := G) (X := X)).out 3 0).mp ?_
  exact ⟨m, hmFA, hmuniv, fun g S => hm_all g S, hmpos⟩

end Assemble

end JMMS.IETP41

/-! # JMMS Proposition 4.1, part D: extensive amenability ⇒ (i).

From an almost invariant probability `φ` on the finite subsets (Reiter's condition for the
lamplighter action) we build `f = √φ` and `v = T f`; Cauchy–Schwarz makes
`b_k = ‖(TP)^k v‖²` log-convex, `⟨P v, v⟩` is close to `1`, and `b_k ≤ (∑ f)² E 2^{-|O_{2k}|}`.
-/

open IntervalExchange Filter Topology
open scoped ENNReal symmDiff

set_option linter.unusedSectionVars false

namespace JMMS.IETP41

/-! ## Log-convex sequences -/

lemma logconvex_ratio (β : ℕ → ℝ) (h0 : ∀ k, 0 ≤ β k) (hpos : 0 < β 0)
    (hlc : ∀ k, β (k + 1) ^ 2 ≤ β k * β (k + 2)) : ∀ k, β 1 * β k ≤ β 0 * β (k + 1) := by
  intro k
  induction k with
  | zero => rw [mul_comm]
  | succ k ih =>
    rcases (h0 (k + 1)).eq_or_lt with h | h
    · rw [← h, mul_zero]; exact mul_nonneg hpos.le (h0 _)
    · have := hlc k
      have h1 := h0 1
      have h2 := h0 (k + 2)
      have : β 1 * β (k + 1) * β (k + 1) ≤ β 0 * β (k + 2) * β (k + 1) := by
        nlinarith [mul_le_mul_of_nonneg_left ih h1, mul_le_mul_of_nonneg_left this h1]
      exact le_of_mul_le_mul_right this h

lemma logconvex_lower (β : ℕ → ℝ) (h0 : ∀ k, 0 ≤ β k) (hpos : 0 < β 0) (hle1 : β 0 ≤ 1)
    (hlc : ∀ k, β (k + 1) ^ 2 ≤ β k * β (k + 2)) (c : ℝ) (_hc : 0 ≤ c)
    (hc2 : c ^ 2 ≤ β 1 * β 0) : ∀ k, c ^ (2 * k) * β 0 ≤ β k := by
  have hr := logconvex_ratio β h0 hpos hlc
  -- `β 0 ^ k * β k ≥ β 1 ^ k * β 0`
  have hk : ∀ k, β 1 ^ k * β 0 ≤ β 0 ^ k * β k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hr k
      calc β 1 ^ (k + 1) * β 0 = β 1 * (β 1 ^ k * β 0) := by ring
        _ ≤ β 1 * (β 0 ^ k * β k) := mul_le_mul_of_nonneg_left ih (h0 1)
        _ = β 0 ^ k * (β 1 * β k) := by ring
        _ ≤ β 0 ^ k * (β 0 * β (k + 1)) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = β 0 ^ (k + 1) * β (k + 1) := by ring
  intro k
  have h1 : c ^ (2 * k) * β 0 ≤ β 0 ^ (2 * k) * β k := by
    have e : c ^ (2 * k) = (c ^ 2) ^ k := by rw [pow_mul]
    calc c ^ (2 * k) * β 0 ≤ (β 1 * β 0) ^ k * β 0 := by
          rw [e]; gcongr
      _ = β 0 ^ k * (β 1 ^ k * β 0) := by ring
      _ ≤ β 0 ^ k * (β 0 ^ k * β k) := mul_le_mul_of_nonneg_left (hk k) (by positivity)
      _ = β 0 ^ (2 * k) * β k := by ring
  calc c ^ (2 * k) * β 0 ≤ β 0 ^ (2 * k) * β k := h1
    _ ≤ 1 * β k := mul_le_mul_of_nonneg_right (pow_le_one₀ hpos.le hle1) (h0 k)
    _ = β k := one_mul _

lemma fs_summable {α : Type*} (φ : α →₀ ℝ) : Summable fun a => φ a :=
  summable_of_ne_finset_zero (s := φ.support) fun _ ha => Finsupp.notMem_support_iff.1 ha

lemma pow_pow_apply {S M : Type*} [Semiring S] [AddCommMonoid M] [Module S M]
    (R : Module.End S M) (a b : ℕ) (w : M) : (R ^ a) ((R ^ b) w) = (R ^ (a + b)) w := by
  rw [← Module.End.mul_apply, ← pow_add]

section Main

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X]

/-- The four permutations of the finite sets that appear in `⟨π_g T f, T f⟩`. -/
def perm4 (x₀ : X) (g : G) : Fin 4 → Equiv.Perm (Finset X)
  | 0 => actEquiv g
  | 1 => (togEquiv x₀).trans (actEquiv g)
  | 2 => (actEquiv g).trans (togEquiv x₀)
  | 3 => ((togEquiv x₀).trans (actEquiv g)).trans (togEquiv x₀)

end Main

end JMMS.IETP41

/-! # JMMS Proposition 4.1, part F: Reiter's condition for the lamplighter action.

The integral against a finitely additive probability (copied from
`Solutions/WolfWork/GAR_all.lean`, Garrido Theorem 1.15), Day's convexity argument (adapted from
Namioka's step there), and the averaging over subsets that turns an extensively amenable mean into
a mean invariant under the lamplighter moves. -/

section FPart

open IntervalExchange Filter Topology Garrido
open scoped ENNReal symmDiff

set_option linter.unusedSectionVars false

namespace JMMS.IETP41.Mean

open scoped ENNReal Pointwise
open Set


open scoped ENNReal Pointwise
open Set


section Integral

variable {X : Type*} (m : Set X → ℝ≥0∞)

/-- Finite additivity over the fibres of a map. -/
theorem mean_fam_fiber (hm : IsFinitelyAdditiveMeasure m) {α : Type*} [DecidableEq α]
    (π : X → α) (T : Finset α) :
    m (π ⁻¹' (T : Set α)) = ∑ a ∈ T, m (π ⁻¹' {a}) := by
  induction T using Finset.induction_on with
  | empty => simp [hm.1]
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, ← ih, Finset.coe_insert, Set.insert_eq, Set.preimage_union]
    apply hm.2
    exact Disjoint.preimage π (Set.disjoint_singleton_left.2 (by simpa using ha))

theorem mean_mono (hm : IsFinitelyAdditiveMeasure m) {s t : Set X} (h : s ⊆ t) : m s ≤ m t := by
  have : t = s ∪ (t \ s) := (Set.union_sdiff_cancel h).symm
  rw [this, hm.2 _ _ Set.disjoint_sdiff_right]
  exact le_self_add

theorem mean_ne_top (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (s : Set X) :
    m s ≠ ∞ :=
  ne_top_of_le_ne_top (by rw [h1]; exact ENNReal.one_ne_top) (mean_mono m hm (subset_univ s))

/-- The integral of a finitely valued function. -/
noncomputable def meanI (s : X → ℝ) : ℝ := ∑ᶠ v : ℝ, v * (m (s ⁻¹' {v})).toReal

variable {m}

theorem meanI_factor (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1)
    {α : Type*} [DecidableEq α] (π : X → α) (T : Finset α) (hT : ∀ x, π x ∈ T) (ψ : α → ℝ) :
    meanI m (ψ ∘ π) = ∑ a ∈ T, ψ a * (m (π ⁻¹' {a})).toReal := by
  classical
  rw [meanI, finsum_eq_sum_of_support_subset _ (s := T.image ψ) ?_]
  · have e : ∀ v, (ψ ∘ π) ⁻¹' {v} = π ⁻¹' ((T.filter (fun a => ψ a = v) : Finset α) : Set α) := by
      intro v; ext x; simp [hT x]
    simp_rw [e, mean_fam_fiber m hm, ENNReal.toReal_sum (fun a _ => mean_ne_top m hm h1 _),
      Finset.mul_sum]
    rw [← Finset.sum_fiberwise_of_maps_to (g := ψ) (t := T.image ψ)
      (fun a ha => Finset.mem_image_of_mem ψ ha)]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun a ha => ?_
    rw [(Finset.mem_filter.1 ha).2]
  · intro v hv
    rw [Function.mem_support] at hv
    by_contra h
    apply hv
    have : (ψ ∘ π) ⁻¹' {v} = ∅ := by
      ext x
      simp only [mem_preimage, Function.comp_apply, mem_singleton_iff, mem_empty_iff_false,
        iff_false]
      intro hx
      exact h (by simpa using ⟨π x, hT x, hx⟩)
    simp [this, hm.1]

theorem meanI_eq_sum (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1)
    (s : X → ℝ) (T : Finset ℝ) (hT : ∀ x, s x ∈ T) :
    meanI m s = ∑ v ∈ T, v * (m (s ⁻¹' {v})).toReal :=
  meanI_factor hm h1 s T hT id

theorem mean_range_pair {s t : X → ℝ} (hs : (range s).Finite) (ht : (range t).Finite) :
    (range fun x => (s x, t x)).Finite :=
  (hs.prod ht).subset (by rintro _ ⟨x, rfl⟩; exact ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩)

theorem mean_range_map {s : X → ℝ} (hs : (range s).Finite) (φ : ℝ → ℝ) :
    (range fun x => φ (s x)).Finite :=
  (hs.image φ).subset (by rintro _ ⟨x, rfl⟩; exact ⟨s x, ⟨x, rfl⟩, rfl⟩)

theorem mean_range_add {s t : X → ℝ} (hs : (range s).Finite) (ht : (range t).Finite) :
    (range fun x => s x + t x).Finite :=
  ((mean_range_pair hs ht).image (fun p => p.1 + p.2)).subset
    (by rintro _ ⟨x, rfl⟩; exact ⟨(s x, t x), ⟨x, rfl⟩, rfl⟩)

theorem mean_range_const (c : ℝ) : (range fun _ : X => c).Finite :=
  (Set.finite_singleton c).subset Set.range_const_subset

theorem meanI_add (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {s t : X → ℝ}
    (hs : (range s).Finite) (ht : (range t).Finite) :
    meanI m (fun x => s x + t x) = meanI m s + meanI m t := by
  classical
  let π : X → ℝ × ℝ := fun x => (s x, t x)
  have hT : ∀ x, π x ∈ hs.toFinset ×ˢ ht.toFinset := fun x => by simp [π]
  have e1 := meanI_factor hm h1 π _ hT Prod.fst
  have e2 := meanI_factor hm h1 π _ hT Prod.snd
  have e3 := meanI_factor hm h1 π _ hT (fun p => p.1 + p.2)
  simp only [Function.comp_def, π] at e1 e2 e3
  rw [e1, e2, e3, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => add_mul _ _ _

theorem meanI_map (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {s : X → ℝ}
    (hs : (range s).Finite) (c : ℝ) : meanI m (fun x => c * s x) = c * meanI m s := by
  classical
  have hT : ∀ x, s x ∈ hs.toFinset := fun x => by simp
  have e1 := meanI_factor hm h1 s _ hT (fun v => c * v)
  have e2 := meanI_eq_sum hm h1 s _ hT
  simp only [Function.comp_def] at e1
  rw [e1, e2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => mul_assoc _ _ _

theorem meanI_const (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (c : ℝ) :
    meanI m (fun _ : X => c) = c := by
  have e := meanI_factor hm h1 (fun _ : X => ()) Finset.univ (fun _ => Finset.mem_univ _)
    (fun _ => c)
  simp only [Function.comp_def] at e
  rw [e]
  simp [h1]

theorem meanI_mono (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {s t : X → ℝ}
    (hs : (range s).Finite) (ht : (range t).Finite) (hst : ∀ x, s x ≤ t x) :
    meanI m s ≤ meanI m t := by
  classical
  let π : X → ℝ × ℝ := fun x => (s x, t x)
  have hπ := mean_range_pair hs ht
  have hT : ∀ x, π x ∈ hπ.toFinset := fun x => (Set.Finite.mem_toFinset hπ).2 ⟨x, rfl⟩
  have e1 := meanI_factor hm h1 π _ hT Prod.fst
  have e2 := meanI_factor hm h1 π _ hT Prod.snd
  simp only [Function.comp_def, π] at e1 e2
  rw [e1, e2]
  refine Finset.sum_le_sum fun a ha => ?_
  obtain ⟨x, rfl⟩ := (Set.Finite.mem_toFinset hπ).1 ha
  exact mul_le_mul_of_nonneg_right (hst x) ENNReal.toReal_nonneg

theorem meanI_indicator (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (A : Set X) :
    meanI m (A.indicator 1) = (m A).toReal := by
  classical
  have e := meanI_factor hm h1 (fun x => decide (x ∈ A)) Finset.univ
    (fun _ => Finset.mem_univ _) (fun b => if b then (1 : ℝ) else 0)
  have hf : ((fun b : Bool => if b then (1 : ℝ) else 0) ∘ fun x => decide (x ∈ A))
      = A.indicator 1 := by
    funext x; by_cases h : x ∈ A <;> simp [h]
  rw [hf] at e
  rw [e, Fintype.sum_bool]
  have : ((fun x => decide (x ∈ A)) ⁻¹' {true}) = A := by ext x; simp
  simp [this]

/-! ### The upper integral on `ℓ∞` -/

local notation "E" X => lp (fun _ : X => ℝ) ∞

variable (m) in
/-- Upper Darboux integral of a bounded function. -/
noncomputable def meanP (f : E X) : ℝ :=
  sInf {r | ∃ s : X → ℝ, (range s).Finite ∧ (∀ x, (f : X → ℝ) x ≤ s x) ∧ meanI m s = r}

theorem mean_abs_le (f : E X) (x : X) : |(f : X → ℝ) x| ≤ ‖f‖ := by
  have := lp.norm_apply_le_norm ENNReal.top_ne_zero f x
  simpa [Real.norm_eq_abs] using this

theorem meanP_le (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {f : E X} {s : X → ℝ}
    (hs : (range s).Finite) (hfs : ∀ x, (f : X → ℝ) x ≤ s x) : meanP m f ≤ meanI m s := by
  refine csInf_le ⟨-‖f‖, ?_⟩ ⟨s, hs, hfs, rfl⟩
  rintro _ ⟨t, ht, hft, rfl⟩
  rw [← meanI_const hm h1 (-‖f‖)]
  exact meanI_mono hm h1 (mean_range_const _) ht
    (fun x => le_trans (neg_le_of_abs_le (mean_abs_le f x)) (hft x))

theorem le_meanP {f : E X} {r : ℝ}
    (h : ∀ s : X → ℝ, (range s).Finite → (∀ x, (f : X → ℝ) x ≤ s x) → r ≤ meanI m s) :
    r ≤ meanP m f := by
  refine le_csInf ⟨_, fun _ => ‖f‖, mean_range_const _,
    fun x => le_trans (le_abs_self _) (mean_abs_le f x), rfl⟩ ?_
  rintro _ ⟨s, hs, hfs, rfl⟩
  exact h s hs hfs

/-- Approximation from above by a finitely valued function, within `ε`. -/
theorem mean_approx (f : E X) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : X → ℝ, (range s).Finite ∧ (∀ x, (f : X → ℝ) x ≤ s x) ∧
      ∀ x, s x ≤ (f : X → ℝ) x + ε := by
  refine ⟨fun x => ε * ⌈(f : X → ℝ) x / ε⌉, ?_, fun x => ?_, fun x => ?_⟩
  · refine ((Set.finite_Icc ⌈-‖f‖ / ε⌉ ⌈‖f‖ / ε⌉).image (fun k : ℤ => ε * k)).subset ?_
    rintro _ ⟨x, rfl⟩
    refine ⟨_, ⟨Int.ceil_mono ?_, Int.ceil_mono ?_⟩, rfl⟩
    · exact div_le_div_of_nonneg_right (neg_le_of_abs_le (mean_abs_le f x)) hε.le
    · exact div_le_div_of_nonneg_right (le_trans (le_abs_self _) (mean_abs_le f x)) hε.le
  · have := Int.le_ceil ((f : X → ℝ) x / ε)
    calc (f : X → ℝ) x = ε * ((f : X → ℝ) x / ε) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left this hε.le
  · have := Int.ceil_lt_add_one ((f : X → ℝ) x / ε)
    calc ε * (⌈(f : X → ℝ) x / ε⌉ : ℝ) ≤ ε * ((f : X → ℝ) x / ε + 1) :=
          mul_le_mul_of_nonneg_left this.le hε.le
      _ = (f : X → ℝ) x + ε := by field_simp

/-- A finitely valued function as an element of `ℓ∞`. -/
noncomputable def meanOfFin (s : X → ℝ) (hs : (range s).Finite) : E X :=
  ⟨s, memℓp_infty_iff.2 (by
    have : (range fun i => ‖s i‖) = (fun v => ‖v‖) '' range s := by
      rw [← Set.range_comp]; rfl
    rw [this]
    exact (hs.image _).bddAbove)⟩

@[simp] theorem meanOfFin_apply (s : X → ℝ) (hs : (range s).Finite) (x : X) :
    (meanOfFin s hs : X → ℝ) x = s x := rfl

theorem meanP_ofFin (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (s : X → ℝ)
    (hs : (range s).Finite) : meanP m (meanOfFin s hs) = meanI m s :=
  le_antisymm (meanP_le hm h1 hs fun _ => le_rfl)
    (le_meanP fun t ht hst => meanI_mono (t := t) hm h1 hs ht hst)

theorem meanP_smul_le (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {c : ℝ} (hc : 0 < c)
    (f : E X) : meanP m (c • f) ≤ c * meanP m f := by
  have : meanP m (c • f) / c ≤ meanP m f := by
    refine le_meanP fun s hs hfs => ?_
    rw [div_le_iff₀ hc]
    calc meanP m (c • f) ≤ meanI m (fun x => c * s x) :=
          meanP_le hm h1 (mean_range_map hs _) (fun x => by
            simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
            exact mul_le_mul_of_nonneg_left (hfs x) hc.le)
      _ = meanI m s * c := by rw [meanI_map hm h1 hs, mul_comm]
  rwa [div_le_iff₀ hc, mul_comm] at this

theorem meanP_smul (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {c : ℝ} (hc : 0 < c)
    (f : E X) : meanP m (c • f) = c * meanP m f := by
  refine le_antisymm (meanP_smul_le hm h1 hc f) ?_
  have := meanP_smul_le hm h1 (inv_pos.2 hc) (c • f)
  rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this
  calc c * meanP m f ≤ c * (c⁻¹ * meanP m (c • f)) := mul_le_mul_of_nonneg_left this hc.le
    _ = _ := by field_simp

theorem meanP_add_le (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (f g : E X) :
    meanP m (f + g) ≤ meanP m f + meanP m g := by
  have h2 : meanP m (f + g) - meanP m f ≤ meanP m g := by
    refine le_meanP fun t ht hgt => ?_
    have : meanP m (f + g) - meanI m t ≤ meanP m f := by
      refine le_meanP fun s hs hfs => ?_
      have := meanP_le hm h1 (f := f + g) (mean_range_add hs ht)
        (fun x => by simp only [lp.coeFn_add, Pi.add_apply]; exact add_le_add (hfs x) (hgt x))
      rw [meanI_add hm h1 hs ht] at this
      linarith
    linarith
  linarith

theorem meanP_zero (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) :
    meanP m (0 : E X) = 0 := by
  refine le_antisymm ?_ ?_
  · calc meanP m (0 : E X) ≤ meanI m (fun _ => 0) :=
          meanP_le hm h1 (mean_range_const _) (fun x => by simp)
      _ = 0 := meanI_const hm h1 0
  · refine le_meanP fun s hs hfs => ?_
    rw [← meanI_const hm h1 (0 : ℝ) (X := X)]
    exact meanI_mono hm h1 (mean_range_const _) hs (fun x => by simpa using hfs x)

/-- The upper integral is linear (Hahn–Banach plus uniform approximation). -/
theorem mean_exists_linear (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) :
    ∃ L : (E X) →ₗ[ℝ] ℝ, ∀ f, L f = meanP m f := by
  obtain ⟨L, -, hL⟩ := exists_extension_of_le_sublinear
    ({ domain := ⊥, toFun := 0 } : (E X) →ₗ.[ℝ] ℝ) (meanP m)
    (fun c hc f => meanP_smul hm h1 hc f) (meanP_add_le hm h1)
    (fun x => by
      have hx : (x : E X) = 0 := (Submodule.mem_bot ℝ).1 x.2
      simp [hx, meanP_zero hm h1])
  refine ⟨L, fun f => le_antisymm (hL f) ?_⟩
  -- `L` agrees with `meanI` on finitely valued functions.
  have hLs : ∀ s hs, L (meanOfFin s hs) = meanI m s := by
    intro s hs
    refine le_antisymm ((hL _).trans (meanP_ofFin hm h1 s hs).le) ?_
    have hns := mean_range_map hs (fun v => -1 * v)
    have e : -(meanOfFin s hs) = meanOfFin (fun x => -1 * s x) hns := by
      ext x; simp
    have := hL (-(meanOfFin s hs))
    rw [map_neg, e, meanP_ofFin hm h1 _ hns, meanI_map hm h1 hs] at this
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨s, hs, hfs, hsf⟩ := mean_approx f hε
  have hs' := mean_range_map hs (fun v => v + -ε)
  have h3 : meanI m (fun x => s x + -ε) = meanI m s - ε := by
    rw [meanI_add hm h1 hs (mean_range_const _), meanI_const hm h1]; ring
  have h4 : L (meanOfFin _ hs') ≤ L f := by
    have := hL (meanOfFin _ hs' - f)
    have h0 : meanP m (meanOfFin _ hs' - f) ≤ 0 := by
      calc meanP m (meanOfFin _ hs' - f) ≤ meanI m (fun _ => 0) :=
            meanP_le hm h1 (mean_range_const _) (fun x => by
              simp only [lp.coeFn_sub, Pi.sub_apply, meanOfFin_apply]; linarith [hsf x])
        _ = 0 := meanI_const hm h1 0
    rw [map_sub] at this
    linarith
  rw [hLs] at h4
  calc meanP m f ≤ meanI m s := meanP_le hm h1 hs hfs
    _ ≤ L f + ε := by linarith

/-- **The integral** `∫ · dm` of a bounded function against a finitely additive probability
measure. -/
noncomputable def mean_integral (m : Set X → ℝ≥0∞) (hm : IsFinitelyAdditiveMeasure m)
    (h1 : m univ = 1) : (E X) →ₗ[ℝ] ℝ where
  toFun := meanP m
  map_add' f g := by
    obtain ⟨L, hL⟩ := mean_exists_linear hm h1
    rw [← hL, ← hL, ← hL, map_add]
  map_smul' c f := by
    obtain ⟨L, hL⟩ := mean_exists_linear hm h1
    rw [← hL, ← hL, map_smul]; rfl

theorem mean_integral_apply (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (f : E X) :
    mean_integral m hm h1 f = meanP m f := rfl

theorem mean_integral_nonneg (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (f : E X)
    (hf : ∀ x, 0 ≤ (f : X → ℝ) x) : 0 ≤ mean_integral m hm h1 f := by
  refine le_meanP fun s hs hfs => ?_
  rw [← meanI_const hm h1 (0 : ℝ) (X := X)]
  exact meanI_mono hm h1 (mean_range_const _) hs (fun x => (hf x).trans (hfs x))

theorem mean_integral_eq_const (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (f : E X)
    (c : ℝ) (hf : ∀ x, (f : X → ℝ) x = c) : mean_integral m hm h1 f = c := by
  have : f = meanOfFin (fun _ => c) (mean_range_const c) := by ext x; simp [hf]
  rw [this, mean_integral_apply, meanP_ofFin hm h1, meanI_const hm h1]

theorem mean_integral_one (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (f : E X)
    (hf : ∀ x, (f : X → ℝ) x = 1) : mean_integral m hm h1 f = 1 :=
  mean_integral_eq_const hm h1 f 1 hf

theorem mean_range_indicator (A : Set X) : (range (A.indicator (1 : X → ℝ))).Finite :=
  (Set.toFinite ({0, 1} : Set ℝ)).subset (by
    rintro _ ⟨x, rfl⟩; by_cases h : x ∈ A <;> simp [h])

/-- The indicator function of `A` as an element of `ℓ∞`. -/
noncomputable def mean_ind (A : Set X) : E X := meanOfFin _ (mean_range_indicator A)

@[simp] theorem mean_ind_apply (A : Set X) (x : X) :
    (mean_ind A : X → ℝ) x = A.indicator 1 x := rfl

theorem mean_integral_ind (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) (A : Set X) :
    mean_integral m hm h1 (mean_ind A) = (m A).toReal := by
  rw [mean_integral_apply, mean_ind, meanP_ofFin hm h1, meanI_indicator hm h1]

end Integral


section Extra

variable {X : Type*} {m : Set X → ℝ≥0∞}

local notation "EL" X => lp (fun _ : X => ℝ) ∞

/-- Precomposition with a permutation, on `ℓ∞`. -/
noncomputable def compL (σ : X ≃ X) (f : EL X) : EL X :=
  ⟨fun x => (f : X → ℝ) (σ x), memℓp_infty_iff.2 ⟨‖f‖, by
    rintro _ ⟨x, rfl⟩
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero f (σ x)⟩⟩

@[simp] lemma compL_apply (σ : X ≃ X) (f : EL X) (x : X) :
    (compL σ f : X → ℝ) x = (f : X → ℝ) (σ x) := rfl

lemma preserve_symm {σ : X ≃ X} (hσ : ∀ S, m (σ '' S) = m S) (S : Set X) :
    m (σ.symm '' S) = m S := by
  rw [← hσ (σ.symm '' S), ← Set.image_comp]
  simp

theorem meanI_comp_equiv {σ : X ≃ X} (hσ : ∀ S, m (σ '' S) = m S) (s : X → ℝ) :
    meanI m (fun x => s (σ x)) = meanI m s := by
  unfold meanI
  congr 1
  funext v
  have : (fun x => s (σ x)) ⁻¹' {v} = σ.symm '' (s ⁻¹' {v}) := by
    rw [Equiv.image_symm_eq_preimage]; rfl
  rw [this, preserve_symm hσ]

theorem mean_integral_comp (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {σ : X ≃ X}
    (hσ : ∀ S, m (σ '' S) = m S) (f : EL X) :
    mean_integral m hm h1 (compL σ f) = mean_integral m hm h1 f := by
  have key : ∀ (σ : X ≃ X), (∀ S, m (σ '' S) = m S) → ∀ f : EL X,
      meanP m (compL σ f) ≤ meanP m f := by
    intro σ hσ f
    refine le_meanP fun s hs hfs => ?_
    rw [← meanI_comp_equiv hσ s]
    exact meanP_le hm h1 ((hs.image id).subset (by rintro _ ⟨x, rfl⟩; exact ⟨_, ⟨_, rfl⟩, rfl⟩))
      (fun x => hfs _)
  refine le_antisymm (key σ hσ f) ?_
  have e : f = compL σ.symm (compL σ f) := by ext x; simp
  calc mean_integral m hm h1 f = meanP m (compL σ.symm (compL σ f)) := by
        rw [mean_integral_apply, ← e]
    _ ≤ _ := key σ.symm (preserve_symm hσ) _

theorem mean_integral_mono (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1) {f g : EL X}
    (h : ∀ x, (f : X → ℝ) x ≤ (g : X → ℝ) x) :
    mean_integral m hm h1 f ≤ mean_integral m hm h1 g := by
  have := mean_integral_nonneg hm h1 (g - f) (fun x => by
    simp only [lp.coeFn_sub, Pi.sub_apply]; linarith [h x])
  rw [map_sub] at this
  linarith

theorem mean_integral_congr_null (hm : IsFinitelyAdditiveMeasure m) (h1 : m univ = 1)
    {f g : EL X} (N : Set X) (hN : m N = 0) (h : ∀ x ∉ N, (f : X → ℝ) x = (g : X → ℝ) x) :
    mean_integral m hm h1 f = mean_integral m hm h1 g := by
  set k := f - g
  have hk : ∀ x, |(k : X → ℝ) x| ≤ ‖k‖ * N.indicator 1 x := by
    intro x
    by_cases hx : x ∈ N
    · simp only [Set.indicator_of_mem hx, Pi.one_apply, mul_one]; exact mean_abs_le k x
    · simp only [Set.indicator_of_notMem hx, mul_zero, k, lp.coeFn_sub, Pi.sub_apply,
        h x hx, sub_self, abs_zero, le_refl]
  have hI : mean_integral m hm h1 (‖k‖ • mean_ind N) = 0 := by
    rw [map_smul, mean_integral_ind hm h1, hN, ENNReal.toReal_zero, smul_zero]
  have hup : mean_integral m hm h1 k ≤ 0 := by
    rw [← hI]
    exact mean_integral_mono hm h1 fun x => by
      simp only [lp.coeFn_smul, Pi.smul_apply, mean_ind_apply, smul_eq_mul]
      exact (le_abs_self _).trans (hk x)
  have hlo : 0 ≤ mean_integral m hm h1 k := by
    have : mean_integral m hm h1 (-k) ≤ 0 := by
      rw [← hI]
      exact mean_integral_mono hm h1 fun x => by
        simp only [lp.coeFn_smul, Pi.smul_apply, mean_ind_apply, smul_eq_mul, lp.coeFn_neg,
          Pi.neg_apply]
        exact (neg_le_abs _).trans (hk x)
    rw [map_neg] at this; linarith
  have : mean_integral m hm h1 k = 0 := le_antisymm hup hlo
  simp only [k, map_sub] at this
  linarith

end Extra

end JMMS.IETP41.Mean

namespace JMMS.IETP41

open Mean

/-! ## Day's convexity argument -/

section Day

variable {Y : Type*}

local notation "EL" Y => lp (fun _ : Y => ℝ) ∞

/-- A finitely supported function as an element of `ℓ¹`. -/
noncomputable def namι : (Y →₀ ℝ) →ₗ[ℝ] lp (fun _ : Y => ℝ) 1 where
  toFun f := ⟨⇑f, (memℓp_zero (f.support.finite_toSet.subset
    (fun i hi => by simpa using hi))).of_exponent_ge zero_le⟩
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl

lemma nam_ι_apply (f : Y →₀ ℝ) (x : Y) : (namι f : Y → ℝ) x = f x := rfl

lemma namι_norm (f : Y →₀ ℝ) : ‖namι f‖ = ∑' y, |f y| := by
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  simp [nam_ι_apply, Real.norm_eq_abs]

lemma day (M : (EL Y) →ₗ[ℝ] ℝ) (hpos : ∀ f : EL Y, (∀ y, 0 ≤ (f : Y → ℝ) y) → 0 ≤ M f)
    (hone : ∀ f : EL Y, (∀ y, (f : Y → ℝ) y = 1) → M f = 1) {ι : Type*} [Fintype ι]
    (σ : ι → Equiv.Perm Y) (hinv : ∀ i f, M (compL (σ i) f) = M f) (δ : ℝ) (hδ : 0 < δ) :
    ∃ φ : Y →₀ ℝ, (∀ y, 0 ≤ φ y) ∧ (φ.sum fun _ r => r) = 1 ∧
      ∀ i, ‖namι (φ - Finsupp.lmapDomain ℝ ℝ (σ i).symm φ)‖ < δ := by
  classical
  by_contra hcon
  push Not at hcon
  let E := ι → lp (fun _ : Y => ℝ) 1
  let L : (Y →₀ ℝ) →ₗ[ℝ] E := LinearMap.pi fun i =>
    namι ∘ₗ (LinearMap.id - Finsupp.lmapDomain ℝ ℝ (σ i).symm)
  let Φ : Set (Y →₀ ℝ) := {f | (∀ x, 0 ≤ f x) ∧ (f.sum fun _ r => r) = 1}
  have hΦ : Convex ℝ Φ := by
    intro f hf g hg s t hs ht hst
    refine ⟨fun x => ?_, ?_⟩
    · have := hf.1 x; have := hg.1 x
      simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      positivity
    · rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_smul_index' (fun _ => rfl), Finsupp.sum_smul_index' (fun _ => rfl)]
      simp only [smul_eq_mul]
      rw [← Finsupp.mul_sum, ← Finsupp.mul_sum, hf.2, hg.2]
      linarith
  have hC : Convex ℝ (L '' Φ) := hΦ.linear_image L
  have hdisj : Disjoint (Metric.ball (0 : E) δ) (L '' Φ) := by
    rw [Set.disjoint_left]
    rintro v hv ⟨f, hf, rfl⟩
    obtain ⟨i, hle⟩ := hcon f hf.1 hf.2
    have h1 : ‖L f‖ < δ := by rwa [Metric.mem_ball, dist_zero_right] at hv
    have h2 := lt_of_le_of_lt (norm_le_pi_norm (L f) i) h1
    exact absurd h2 (not_lt.2 hle)
  obtain ⟨φ, u, hball, hΦu⟩ :=
    geometric_hahn_banach_open (convex_ball 0 δ) Metric.isOpen_ball hC hdisj
  have hu : 0 < u := by simpa using hball 0 (Metric.mem_ball_self hδ)
  let e1 : Y → lp (fun _ : Y => ℝ) 1 := fun y => lp.single 1 y (1 : ℝ)
  let b : ι → Y → ℝ := fun i y => φ (Pi.single i (e1 y) : E)
  have hb : ∀ i y, |b i y| ≤ ‖φ‖ := fun i y => by
    have := φ.le_opNorm (Pi.single i (e1 y) : E)
    have e : ‖(Pi.single i (e1 y) : E)‖ = 1 := by
      rw [Pi.norm_single, lp.norm_single (by norm_num)]; simp
    rw [e, mul_one] at this
    exact this
  let β : ι → EL Y := fun i =>
    ⟨b i, memℓp_infty_iff.2 ⟨‖φ‖, by rintro _ ⟨y, rfl⟩; simpa [Real.norm_eq_abs] using hb i y⟩⟩
  have key : ∀ y, u ≤ ∑ i, (b i y - b i ((σ i).symm y)) := by
    intro y
    have hy : Finsupp.single y (1 : ℝ) ∈ Φ := by
      refine ⟨fun x => ?_, by simp⟩
      rw [Finsupp.single_apply]; split_ifs <;> norm_num
    have h := hΦu _ ⟨_, hy, rfl⟩
    have hL : L (Finsupp.single y 1) =
        ∑ i, (Pi.single i (e1 y - e1 ((σ i).symm y)) : E) := by
      rw [Finset.univ_sum_single]
      funext i; ext x
      show (namι (Finsupp.single y 1 - Finsupp.lmapDomain ℝ ℝ (σ i).symm
        (Finsupp.single y 1)) : Y → ℝ) x = _
      rw [nam_ι_apply]
      simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.coe_sub,
        Pi.sub_apply, Finsupp.single_apply, e1, lp.coeFn_sub, lp.single_apply, Pi.single_apply]
      simp only [eq_comm]
    rw [hL, map_sum] at h
    refine h.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.single_sub, map_sub]
  let one : EL Y :=
    ⟨fun _ => 1, memℓp_infty_iff.2 ⟨1, by rintro _ ⟨y, rfl⟩; simp⟩⟩
  let B := ∑ i, (β i - compL (σ i).symm (β i))
  have hB : ∀ y, (B : Y → ℝ) y = ∑ i, (b i y - b i ((σ i).symm y)) := by
    intro y
    simp only [B, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_sub, Pi.sub_apply]
    rfl
  have h1 := hpos (B - u • one) (fun y => by
    simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hB]
    have : (one : Y → ℝ) y = 1 := rfl
    rw [this]; linarith [key y])
  have hsi : ∀ i f, M (compL (σ i).symm f) = M f := fun i f => by
    rw [← hinv i (compL (σ i).symm f)]
    congr 1; ext y; simp
  have h2 : M B = 0 := by
    simp only [B, map_sum, map_sub, hsi, sub_self, Finset.sum_const_zero]
  have h3 : M one = 1 := hone one (fun _ => rfl)
  rw [map_sub, map_smul, h2, h3] at h1
  simp at h1
  linarith

end Day

/-! ## Averaging over subsets: the lamplighter mean -/

section Lamp

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X]

local notation "EL" Y => lp (fun _ : Y => ℝ) ∞

/-- `K F (E) = 2^{-|E|} ∑_{D ⊆ E} F(D)`. -/
noncomputable def Kfun (F : Finset X → ℝ) (E : Finset X) : ℝ :=
  (∑ D ∈ E.powerset, F D) / 2 ^ E.card

lemma Kfun_abs_le {F : Finset X → ℝ} {C : ℝ} (hF : ∀ D, |F D| ≤ C) (E : Finset X) :
    |Kfun F E| ≤ C := by
  unfold Kfun
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ E.card), div_le_iff₀ (by positivity)]
  calc |∑ D ∈ E.powerset, F D| ≤ ∑ D ∈ E.powerset, |F D| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ D ∈ E.powerset, C := Finset.sum_le_sum fun D _ => hF D
    _ = C * 2 ^ E.card := by
        rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]; push_cast; ring

/-- The averaging operator on `ℓ∞`. -/
noncomputable def Kop : (EL (Finset X)) →ₗ[ℝ] (EL (Finset X)) where
  toFun F := ⟨Kfun (F : Finset X → ℝ), memℓp_infty_iff.2 ⟨‖F‖, by
    rintro _ ⟨E, rfl⟩
    show ‖Kfun _ E‖ ≤ ‖F‖
    rw [Real.norm_eq_abs]
    exact Kfun_abs_le (fun D => mean_abs_le F D) E⟩⟩
  map_add' F F' := by
    ext E
    simp only [lp.coeFn_add, Pi.add_apply]
    show Kfun _ E = Kfun _ E + Kfun _ E
    simp only [Kfun, Pi.add_apply, Finset.sum_add_distrib, add_div]
  map_smul' c F := by
    ext E
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    show Kfun _ E = c * Kfun _ E
    simp only [Kfun, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_div_assoc]

lemma Kop_apply (F : EL (Finset X)) (E : Finset X) :
    (Kop F : Finset X → ℝ) E = Kfun (F : Finset X → ℝ) E := rfl

lemma Kfun_act (F : Finset X → ℝ) (g : G) (E : Finset X) :
    Kfun (fun D => F (act g D)) E = Kfun F (act g E) := by
  unfold Kfun
  rw [card_act]
  congr 1
  refine Finset.sum_nbij' (act g) (act g⁻¹) (fun D hD => ?_) (fun D hD => ?_)
    (fun D _ => act_inv_act g D) (fun D _ => act_act_inv g D) (fun D _ => rfl)
  · rw [Finset.mem_powerset] at hD ⊢; exact act_subset_act.2 hD
  · rw [Finset.mem_powerset] at hD ⊢
    rw [← act_subset_act (g := g), act_act_inv]; exact hD

lemma Kfun_tog (F : Finset X → ℝ) {x₀ : X} {E : Finset X} (hE : x₀ ∈ E) :
    Kfun (fun D => F (tog x₀ D)) E = Kfun F E := by
  unfold Kfun
  congr 1
  have hmem : ∀ D ∈ E.powerset, tog x₀ D ∈ E.powerset := by
    intro D hD
    rw [Finset.mem_powerset] at hD ⊢
    intro y hy
    simp only [tog, Finset.mem_symmDiff, Finset.mem_singleton] at hy
    rcases hy with ⟨hy, _⟩ | ⟨rfl, _⟩
    · exact hD hy
    · exact hE
  exact Finset.sum_nbij' (tog x₀) (tog x₀) hmem hmem (fun D _ => tog_tog x₀ D)
    (fun D _ => tog_tog x₀ D) (fun D _ => rfl)

lemma Kfun_one (E : Finset X) : Kfun (fun _ => (1 : ℝ)) E = 1 := by
  unfold Kfun
  rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, mul_one]
  push_cast
  exact div_self (by positivity)

lemma Kfun_nonneg {F : Finset X → ℝ} (hF : ∀ D, 0 ≤ F D) (E : Finset X) : 0 ≤ Kfun F E :=
  div_nonneg (Finset.sum_nonneg fun D _ => hF D) (by positivity)

lemma compL_trans {Y : Type*} (σ τ : Y ≃ Y) (f : EL Y) :
    compL (σ.trans τ) f = compL σ (compL τ f) := by
  ext y; simp

/-- Reiter's condition for the lamplighter action, from extensive amenability. -/
lemma reiter' (hEA : IsExtensivelyAmenable G X) (x₀ : X) (A : Finset G) (δ : ℝ) (hδ : 0 < δ) :
    ∃ φ : Finset X →₀ ℝ, (∀ E, 0 ≤ φ E) ∧ ∑' E, φ E = 1 ∧
      ∀ g ∈ A, ∀ i, ∑' E, |φ (perm4 x₀ g i E) - φ E| < δ := by
  classical
  obtain ⟨m, hm, -, h1, hinv, hsup⟩ := hEA
  -- the sets not containing `x₀` are null
  have hnull : m {E : Finset X | x₀ ∉ E} = 0 := by
    have hx := hsup {x₀} (Set.subset_univ _)
    have hd : Disjoint {E : Finset X | {x₀} ⊆ E} {E | x₀ ∉ E} :=
      Set.disjoint_left.2 (by intro E h1 h2; exact h2 (Finset.singleton_subset_iff.1 h1))
    have hu := hm.2 _ _ hd
    have : {E : Finset X | {x₀} ⊆ E} ∪ {E | x₀ ∉ E} = Set.univ := by
      ext E; by_cases h : x₀ ∈ E <;> simp [h]
    rw [this, h1, hx] at hu
    have h := hu.symm
    rw [← add_zero (1 : ℝ≥0∞)] at h
    rw [add_zero] at h
    exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 (by rw [add_zero]; exact h.symm) |>.symm
  set Mm := mean_integral m hm h1
  set M : (EL (Finset X)) →ₗ[ℝ] ℝ := Mm ∘ₗ Kop
  have hMact : ∀ g : G, ∀ F, M (compL (actEquiv g) F) = M F := by
    intro g F
    have e : Kop (compL (actEquiv g) F) = compL (actEquiv g) (Kop F) := by
      ext E
      simp only [Kop_apply, compL_apply, actEquiv_apply]
      exact Kfun_act _ g E
    show Mm (Kop _) = Mm (Kop F)
    rw [e]
    exact mean_integral_comp hm h1 (fun S => hinv g S) _
  have hMtog : ∀ F, M (compL (togEquiv x₀) F) = M F := by
    intro F
    show Mm (Kop _) = Mm (Kop F)
    refine mean_integral_congr_null hm h1 {E | x₀ ∉ E} hnull fun E hE => ?_
    simp only [Set.mem_ofPred_eq, not_not] at hE
    simp only [Kop_apply]
    exact Kfun_tog _ hE
  have hM4 : ∀ g : G, ∀ i F, M (compL (perm4 x₀ g i) F) = M F := by
    intro g i F
    fin_cases i
    · exact hMact g F
    · show M (compL ((togEquiv x₀).trans (actEquiv g)) F) = M F
      rw [compL_trans, hMtog, hMact]
    · show M (compL ((actEquiv g).trans (togEquiv x₀)) F) = M F
      rw [compL_trans, hMact, hMtog]
    · show M (compL (((togEquiv x₀).trans (actEquiv g)).trans (togEquiv x₀)) F) = M F
      rw [compL_trans, compL_trans, hMtog, hMact, hMtog]
  have hpos : ∀ F : EL (Finset X), (∀ y, 0 ≤ (F : Finset X → ℝ) y) → 0 ≤ M F := by
    intro F hF
    exact mean_integral_nonneg hm h1 _ fun E => Kfun_nonneg hF E
  have hone : ∀ F : EL (Finset X), (∀ y, (F : Finset X → ℝ) y = 1) → M F = 1 := by
    intro F hF
    refine mean_integral_one hm h1 _ fun E => ?_
    rw [Kop_apply, show (F : Finset X → ℝ) = fun _ => 1 from funext hF]
    exact Kfun_one E
  obtain ⟨φ, h0, hs, hd⟩ := day M hpos hone (fun p : A × Fin 4 => perm4 x₀ (p.1 : G) p.2)
    (fun p F => hM4 (p.1 : G) p.2 F) δ hδ
  refine ⟨φ, h0, ?_, fun g hg i => ?_⟩
  · rw [tsum_eq_sum (s := φ.support) fun E hE => Finsupp.notMem_support_iff.1 hE]
    exact hs
  · have h := hd (⟨g, hg⟩, i)
    rw [namι_norm] at h
    refine lt_of_eq_of_lt (tsum_congr fun E => ?_) h
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.lmapDomain_apply]
    have : Finsupp.mapDomain (perm4 x₀ g i).symm φ E = φ (perm4 x₀ g i E) := by
      have := Finsupp.mapDomain_apply (perm4 x₀ g i).symm.injective φ (perm4 x₀ g i E)
      simpa using this
    rw [this, abs_sub_comm]

end Lamp

end JMMS.IETP41

end FPart

namespace JMMS.IETP41

section Main2

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X]

/-- `∑ √(φ(σE) φ(E)) ≥ 1 - ½ ∑ |φ(σE) - φ(E)|`. -/
lemma bhatt (φ : Finset X →₀ ℝ) (hφ0 : ∀ E, 0 ≤ φ E) (hφ1 : ∑' E, φ E = 1)
    (σ : Equiv.Perm (Finset X)) :
    ENNReal.ofReal (1 - (∑' E, |φ (σ E) - φ E|) / 2) ≤
      ∑' E, ENNReal.ofReal (Real.sqrt (φ (σ E))) * ENNReal.ofReal (Real.sqrt (φ E)) := by
  have hs : Summable fun E => φ E := fs_summable φ
  have hsσ : Summable fun E => φ (σ E) := (σ.summable_iff (f := fun E => φ E)).2 hs
  have hsd : Summable fun E => |φ (σ E) - φ E| := (hsσ.sub hs).abs
  have hsm : Summable fun E => min (φ (σ E)) (φ E) :=
    Summable.of_nonneg_of_le (fun E => le_min (hφ0 _) (hφ0 _)) (fun E => min_le_right _ _) hs
  have hmin : ∑' E, min (φ (σ E)) (φ E) = 1 - (∑' E, |φ (σ E) - φ E|) / 2 := by
    have e : ∀ E, min (φ (σ E)) (φ E) = (φ (σ E) + φ E - |φ (σ E) - φ E|) / 2 := by
      intro E
      rcases le_total (φ (σ E)) (φ E) with h | h
      · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
      · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
    simp_rw [e]
    rw [tsum_div_const, (hsσ.add hs).tsum_sub hsd, hsσ.tsum_add hs,
      σ.tsum_eq (fun E => φ E), hφ1]
    ring
  rw [← hmin, ENNReal.ofReal_tsum_of_nonneg (fun E => le_min (hφ0 _) (hφ0 _)) hsm]
  refine ENNReal.tsum_le_tsum fun E => ?_
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.sqrt_mul (hφ0 _)]
  rcases le_total (φ (σ E)) (φ E) with h | h
  · rw [min_eq_left h]
    calc φ (σ E) = Real.sqrt (φ (σ E) * φ (σ E)) := (Real.sqrt_mul_self (hφ0 _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h (hφ0 _))
  · rw [min_eq_right h]
    calc φ E = Real.sqrt (φ E * φ E) := (Real.sqrt_mul_self (hφ0 _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right h (hφ0 _))

lemma inr_pi_Top (x₀ : X) (f : Finset X → ℝ≥0∞) (g : G) :
    ∑' E, Top x₀ f (act g E) * Top x₀ f E = 2⁻¹ * 2⁻¹ * ∑ i : Fin 4,
      ∑' E, f (perm4 x₀ g i E) * f E := by
  have e2 : ∑' E, f (act g E) * f (tog x₀ E) = ∑' E, f (perm4 x₀ g 1 E) * f E := by
    rw [← (togEquiv x₀).tsum_eq]
    refine tsum_congr fun E => ?_
    simp [perm4, tog_tog]
  have e4 : ∑' E, f (tog x₀ (act g E)) * f (tog x₀ E) = ∑' E, f (perm4 x₀ g 3 E) * f E := by
    rw [← (togEquiv x₀).tsum_eq]
    refine tsum_congr fun E => ?_
    simp [perm4, tog_tog]
  rw [Fin.sum_univ_four, ← e2, ← e4]
  simp only [perm4, actEquiv_apply, Equiv.trans_apply, togEquiv_apply, Top_apply]
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun E => ?_
  ring

theorem i_of_ea {μ : G → ℝ} (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) (hsymm : ∀ g, μ g⁻¹ = μ g)
    (x₀ : X) (hEA : IsExtensivelyAmenable G X) :
    Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log (pR μ x₀ n)) atTop (𝓝 0) := by
  refine fekete_tendsto _ (pR_pos hμ x₀) (pR_le_one hμ x₀) (pR_mul_le hμ hsymm x₀) ?_
  intro ε hε
  -- the target lower bound `c0`
  set c0 := Real.exp (-(ε / 4)) with hc0
  have hc0pos : 0 < c0 := Real.exp_pos _
  have hc01 : c0 < 1 := by rw [hc0, Real.exp_lt_one_iff]; linarith
  set t := (1 - c0) / 2 with ht
  have htpos : 0 < t := by rw [ht]; linarith
  -- a finite set of steps carrying mass `≥ 1 - t`
  obtain ⟨A, hA⟩ : ∃ A : Finset G, 1 - t < ∑ g ∈ A, μ g := by
    have := (tendsto_order.1 hμ.2).1 (1 - t) (by linarith)
    exact this.exists
  obtain ⟨φ, hφ0, hφ1, hφA⟩ := reiter' hEA x₀ A t htpos
  -- `f = √φ`, `v = T f`
  set f : Finset X → ℝ≥0∞ := fun E => ENNReal.ofReal (Real.sqrt (φ E)) with hf
  set F := φ.support
  have hfF : ∀ E, E ∉ F → f E = 0 := fun E hE => by
    simp only [hf, Finsupp.notMem_support_iff.1 hE, Real.sqrt_zero, ENNReal.ofReal_zero]
  set v := Top x₀ f with hv
  have hvT : TInv x₀ v := TInv_Top x₀ f
  clear_value v
  set b : ℕ → ℝ≥0∞ := fun k => inr ((Rop μ x₀ ^ k) v) ((Rop μ x₀ ^ k) v) with hb
  -- `f` is a unit vector
  have hff : inr f f = 1 := by
    unfold inr
    rw [← ENNReal.ofReal_one, ← hφ1, ENNReal.ofReal_tsum_of_nonneg hφ0 (fs_summable φ)]
    refine tsum_congr fun E => ?_
    rw [hf, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), Real.mul_self_sqrt (hφ0 E)]
  have hb0 : b 0 ≤ 1 := by
    simp only [hb, pow_zero, Module.End.one_apply]; rw [← hff, hv]; exact inr_Top_le x₀ f
  -- `b k = ⟨v, R^{2k} v⟩`
  have hbk : ∀ k, b k = inr v ((Rop μ x₀ ^ (2 * k)) v) := fun k => by
    simp only [hb]
    rw [inr_Rop_pow hsymm hvT (TInv_Rop_pow μ x₀ hvT k), pow_pow_apply, two_mul]
  -- log-convexity
  have hlc : ∀ k, b (k + 1) ^ 2 ≤ b k * b (k + 2) := by
    intro k
    have e : b (k + 1) = inr ((Rop μ x₀ ^ k) v) ((Rop μ x₀ ^ (k + 2)) v) := by
      rw [hbk, inr_Rop_pow hsymm hvT (TInv_Rop_pow μ x₀ hvT _), pow_pow_apply,
        show k + (k + 2) = 2 * (k + 1) by ring]
    rw [e]
    have := ennreal_cs ((Rop μ x₀ ^ k) v) ((Rop μ x₀ ^ (k + 2)) v)
    simpa [inr, sq, hb] using this
  -- the bound by the return probability
  have hupper : ∀ k, b k ≤ (F.card : ℝ≥0∞) * pE μ x₀ (2 * k) := by
    intro k
    have hvsum : v = ∑ D ∈ F, f D • Z μ x₀ 0 D := by
      have hfsum : f = ∑ D ∈ F, f D • dlt D := by
        funext E
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, dlt, smul_eq_mul, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq]
        split_ifs with h
        · rfl
        · exact hfF E h
      rw [hv]
      conv_lhs => rw [hfsum]
      rw [map_sum]
      simp only [map_smul, Z_zero]
    have hR : (Rop μ x₀ ^ (2 * k)) v = ∑ D ∈ F, f D • Z μ x₀ (2 * k) D := by
      rw [hvsum, map_sum]
      simp only [map_smul, Rop_pow_Z]
    rw [hbk]
    nth_rewrite 1 [hv]
    rw [inr_Top,
      Top_of_TInv (TInv_Rop_pow μ x₀ hvT _), hR]
    unfold inr
    calc ∑' E, f E * (∑ D ∈ F, f D • Z μ x₀ (2 * k) D) E
        ≤ ∑' E, f E * ((∑ D ∈ F, f D) * pE μ x₀ (2 * k)) := by
          refine ENNReal.tsum_le_tsum fun E => ?_
          gcongr
          rw [Finset.sum_apply, Finset.sum_mul]
          refine Finset.sum_le_sum fun D _ => ?_
          simp only [Pi.smul_apply, smul_eq_mul]
          gcongr
          exact Z_le_pE μ x₀ _ _ _
      _ = (∑' E, f E) * (∑ D ∈ F, f D) * pE μ x₀ (2 * k) := by
          rw [ENNReal.tsum_mul_right]; ring
      _ ≤ (F.card : ℝ≥0∞) * pE μ x₀ (2 * k) := by
          gcongr
          have hsF : ∑' E, f E = ∑ D ∈ F, f D := tsum_eq_sum fun E hE => hfF E hE
          rw [hsF, ← sq]
          have := ennreal_cs (fun E => f E) (fun E => if E ∈ F then 1 else 0)
          have e1 : ∑' E, f E * (if E ∈ F then 1 else 0) = ∑ D ∈ F, f D := by
            rw [tsum_eq_sum (s := F) fun E hE => by simp [hE]]
            exact Finset.sum_congr rfl fun D hD => by simp [hD]
          have e2 : ∑' E : Finset X, (if E ∈ F then (1 : ℝ≥0∞) else 0) ^ 2 = F.card := by
            rw [tsum_eq_sum (s := F) fun E hE => by simp [hE]]
            rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ≥0∞)) fun D hD => by simp [hD]]
            simp
          have e3 : ∑' E, f E ^ 2 = 1 := by rw [← hff]; unfold inr; simp [sq]
          rw [e1, e2, e3, one_mul] at this
          exact this

  -- `c = ⟨P v, v⟩` and its lower bound
  set c := inr (Pop μ v) v with hcdef
  have hcR : inr (Rop μ x₀ v) v = c := by
    rw [Rop_apply, inr_Top, Top_of_TInv hvT]
  have hcs : c ^ 2 ≤ b 1 * b 0 := by
    rw [← hcR]
    have := ennreal_cs (Rop μ x₀ v) v
    simpa [inr, sq, hb] using this
  set c' := (∑ g ∈ A, μ g) * (1 - t / 2) with hc'
  have hAμ : 0 ≤ ∑ g ∈ A, μ g := Finset.sum_nonneg fun g _ => hμ.1 g
  have ht1 : t < 1 / 2 := by rw [ht]; linarith
  have hc'c0 : c0 ≤ c' := by
    have : (1 - t) * (1 - t / 2) ≤ c' := by
      rw [hc']; exact mul_le_mul_of_nonneg_right hA.le (by linarith)
    nlinarith
  have hc'pos : 0 < c' := lt_of_lt_of_le hc0pos hc'c0
  have hclow : ENNReal.ofReal c' ≤ c := by
    have hpi : ∀ g ∈ A, ENNReal.ofReal (1 - t / 2) ≤ ∑' E, v (act g E) * v E := by
      intro g hg
      rw [hv, inr_pi_Top]
      have hbi : ∀ i, ENNReal.ofReal (1 - t / 2) ≤ ∑' E, f (perm4 x₀ g i E) * f E := by
        intro i
        refine le_trans (ENNReal.ofReal_le_ofReal ?_) (bhatt φ hφ0 hφ1 (perm4 x₀ g i))
        have := hφA g hg i
        linarith
      calc ENNReal.ofReal (1 - t / 2)
          = 2⁻¹ * 2⁻¹ * ∑ _i : Fin 4, ENNReal.ofReal (1 - t / 2) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              ← mul_assoc, show (2⁻¹ : ℝ≥0∞) * 2⁻¹ * ((4 : ℕ) : ℝ≥0∞) = 1 by
                rw [show ((4 : ℕ) : ℝ≥0∞) = 2 * 2 by norm_num, mul_mul_mul_comm,
                  ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul], one_mul]
        _ ≤ _ := by gcongr with i; exact hbi i
    calc ENNReal.ofReal c' = ∑ g ∈ A, ENNReal.ofReal (μ g) * ENNReal.ofReal (1 - t / 2) := by
          rw [hc', ENNReal.ofReal_mul hAμ, ENNReal.ofReal_sum_of_nonneg (fun g _ => hμ.1 g),
            Finset.sum_mul]
      _ ≤ ∑ g ∈ A, ENNReal.ofReal (μ g) * ∑' E, v (act g E) * v E := by
          gcongr with g hg; exact hpi g hg
      _ ≤ ∑' g, ENNReal.ofReal (μ g) * ∑' E, v (act g E) * v E :=
          ENNReal.sum_le_tsum A
      _ = c := by
          rw [hcdef]; unfold inr
          simp only [Pop_apply]
          simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
          rw [ENNReal.tsum_comm]
          exact tsum_congr fun g => tsum_congr fun E => by ring
  -- to real numbers
  have hFne : F.Nonempty := by
    by_contra hF
    rw [Finset.not_nonempty_iff_eq_empty] at hF
    have : ∑' E, φ E = 0 := by
      rw [tsum_eq_sum (s := F) fun E hE => Finsupp.notMem_support_iff.1 hE, hF,
        Finset.sum_empty]
    rw [hφ1] at this; exact one_ne_zero this
  have hFc : (1 : ℝ) ≤ F.card := by exact_mod_cast hFne.card_pos
  have hbfin : ∀ k, b k ≠ ⊤ := fun k => by
    refine ne_top_of_le_ne_top ?_ (hupper k)
    exact ENNReal.mul_ne_top (by simp) (by rw [pE_eq_ofReal hμ]; exact ENNReal.ofReal_ne_top)
  set β : ℕ → ℝ := fun k => (b k).toReal with hβ
  have hβ0 : ∀ k, 0 ≤ β k := fun k => ENNReal.toReal_nonneg
  have hβlc : ∀ k, β (k + 1) ^ 2 ≤ β k * β (k + 2) := by
    intro k
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (hbfin _) (hbfin _)) (hlc k)
    simpa [hβ, ENNReal.toReal_mul, ENNReal.toReal_pow] using this
  have hβ1 : β 0 ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top hb0
    simpa [hβ] using this
  have hcβ : c' ^ 2 ≤ β 1 * β 0 := by
    have hcfin : c ≠ ⊤ := by
      intro h
      rw [h] at hcs
      simp at hcs
      exact ENNReal.mul_ne_top (hbfin 1) (hbfin 0) hcs
    have h1 : c' ≤ c.toReal := by
      have := ENNReal.toReal_mono hcfin hclow
      rwa [ENNReal.toReal_ofReal hc'pos.le] at this
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (hbfin 1) (hbfin 0)) hcs
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at h2
    have : c' ^ 2 ≤ c.toReal ^ 2 := by gcongr
    simp only [hβ]; linarith
  have hβpos : 0 < β 0 := by
    rcases (hβ0 0).eq_or_lt with h | h
    · rw [← h, mul_zero] at hcβ
      have := pow_pos hc'pos 2
      linarith
    · exact h
  have hlow := logconvex_lower β hβ0 hβpos hβ1 hβlc c' hc'pos.le hcβ
  have hup : ∀ k, β k ≤ F.card * pR μ x₀ (2 * k) := by
    intro k
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp)
      (by rw [pE_eq_ofReal hμ]; exact ENNReal.ofReal_ne_top)) (hupper k)
    rwa [ENNReal.toReal_mul, pE_eq_ofReal hμ, ENNReal.toReal_ofReal (pR_pos hμ x₀ _).le,
      ENNReal.toReal_natCast] at this
  -- choose `k`
  set K := Real.log (F.card / β 0) with hK
  obtain ⟨k, hk⟩ := exists_nat_gt (K / ε)
  have hk1 : 1 ≤ k + 1 := by omega
  refine ⟨2 * (k + 1), by omega, ?_⟩
  have hp := (hlow (k + 1)).trans (hup (k + 1))
  have hpR := pR_pos hμ x₀ (2 * (k + 1))
  have hlog := Real.log_le_log (by positivity) hp
  rw [Real.log_mul (by positivity) hβpos.ne', Real.log_mul (by positivity) hpR.ne',
    Real.log_pow] at hlog
  have hlogc : -(ε / 4) ≤ Real.log c' := by
    rw [← Real.log_exp (-(ε / 4))]; exact Real.log_le_log (Real.exp_pos _) hc'c0
  have hKe : K = Real.log F.card - Real.log (β 0) := by
    rw [hK, Real.log_div (by positivity) hβpos.ne']
  have hKk : K < ε * (k + 1) := by
    have := (div_lt_iff₀ hε).1 hk
    nlinarith
  rw [rate_eq, div_le_iff₀ (by positivity)]
  push_cast at hlog ⊢
  nlinarith

end Main2

end JMMS.IETP41

open IntervalExchange

namespace JMMS

theorem chk_isExtensivelyAmenable_tfae_invertedOrbit {G X : Type*} [Group G] [MulAction G X]
    [DecidableEq X] [Group.FG G] [MulAction.IsPretransitive G X] (μ : G → ℝ)
    (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) (hsymm : ∀ g, μ g⁻¹ = μ g)
    (hgen : Subgroup.closure (Function.support μ) = ⊤) (x₀ : X) :
    List.TFAE
      [IsExtensivelyAmenable G X,
       Filter.Tendsto
         (fun n : ℕ => -(1 / (n : ℝ)) *
           Real.log (walkExp μ n fun h => (2 : ℝ) ^ (-((invertedOrbit x₀ h).card : ℤ))))
         Filter.atTop (nhds 0),
       ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in Filter.atTop,
         Real.exp (-(ε * n)) < walkProb μ n {h | ((invertedOrbit x₀ h).card : ℝ) < ε * n},
       ∃ A : ∀ n : ℕ, Set (Fin n → G), (∀ n, 0 < walkProb μ n (A n)) ∧
         Filter.Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log (walkProb μ n (A n)))
           Filter.atTop (nhds 0) ∧
         Filter.Tendsto
           (fun n : ℕ => (1 / (n : ℝ)) *
             ((walkExp μ n fun h =>
                 (A n).indicator (fun h => ((invertedOrbit x₀ h).card : ℝ)) h) /
               walkProb μ n (A n)))
           Filter.atTop (nhds 0)] := by
  tfae_have 1 → 2 := fun h => IETP41.i_of_ea hμ hsymm x₀ h
  tfae_have 2 → 1 := fun h => IETP41.ea_of_i hμ hsymm hgen x₀ h
  tfae_have 2 → 3 := fun h => IETP41.i_to_ii hμ x₀ h
  tfae_have 3 → 2 := fun h => IETP41.ii_to_i hμ hsymm x₀ h
  tfae_have 2 → 4 := fun h => IETP41.i_to_iii hμ x₀ h
  tfae_have 4 → 2 := fun h => IETP41.iii_to_i hμ x₀ h
  tfae_finish

end JMMS

end

open IntervalExchange
theorem solution {G X : Type*} [Group G] [MulAction G X]
    [DecidableEq X] [Group.FG G] [MulAction.IsPretransitive G X] (μ : G → ℝ)
    (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1) (hsymm : ∀ g, μ g⁻¹ = μ g)
    (hgen : Subgroup.closure (Function.support μ) = ⊤) (x₀ : X) :
    List.TFAE
      [IsExtensivelyAmenable G X,
       Filter.Tendsto
         (fun n : ℕ => -(1 / (n : ℝ)) *
           Real.log (walkExp μ n fun h => (2 : ℝ) ^ (-((invertedOrbit x₀ h).card : ℤ))))
         Filter.atTop (nhds 0),
       ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in Filter.atTop,
         Real.exp (-(ε * n)) < walkProb μ n {h | ((invertedOrbit x₀ h).card : ℝ) < ε * n},
       ∃ A : ∀ n : ℕ, Set (Fin n → G), (∀ n, 0 < walkProb μ n (A n)) ∧
         Filter.Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log (walkProb μ n (A n)))
           Filter.atTop (nhds 0) ∧
         Filter.Tendsto
           (fun n : ℕ => (1 / (n : ℝ)) *
             ((walkExp μ n fun h =>
                 (A n).indicator (fun h => ((invertedOrbit x₀ h).card : ℝ)) h) /
               walkProb μ n (A n)))
           Filter.atTop (nhds 0)] :=
  JMMS.chk_isExtensivelyAmenable_tfae_invertedOrbit μ hμ hsymm hgen x₀
