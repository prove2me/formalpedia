-- Prove2me | solution 1 for OAI.PeriodicTilingThree.periodic_tiling_counterexample_and_minimality
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-24T23:38:04.976694+00:00
-- url     : https://prove2.me/submissions/51aa3955-36a8-4bab-b11f-0e9d306682c8

import Mathlib
import Definitions.Def_PeriodicTilingThree

namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
end OAICompat434

end OAI

universe u uG uH uK uR uι uA uB uE uInner uL uJ uF uM uΔ uS uC uN uα uZ uV uΩ uI uX

section
section
namespace OAI

noncomputable section


namespace PeriodicTilingThree


section AdditiveGroup

variable {G : Type u} [AddCommGroup G]




end AdditiveGroup

open MeasureTheory









end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

abbrev Plane := ℤ × ℤ

def planeEquiv : Plane ≃+ Lattice 2 where
  toEquiv := (finTwoArrowEquiv ℤ).symm
  map_add' p q := by
    ext i
    fin_cases i <;> rfl

section AdditiveGroup

variable {G : Type uG} [AddCommGroup G]

theorem tiles_iff_unique_tile {F : Finset G} {A : Set G} :
    Tiles F A ↔ ∀ x : G, ∃! f : ↥F, x - (f : G) ∈ A := by
  constructor
  · intro h x
    obtain ⟨⟨f, a⟩, hx⟩ := h.2 x
    have hfa : x - (f : G) = (a : G) := by
      rw [← hx]
      simp
    refine ⟨f, ?_, ?_⟩
    · change x - (f : G) ∈ A
      rw [hfa]
      exact a.property
    · intro g hg
      have hp : (g, (⟨x - (g : G), hg⟩ : A)) = (f, a) := by
        apply h.1
        change (g : G) + (x - (g : G)) = (f : G) + (a : G)
        simpa [add_comm] using hx.symm
      exact congrArg Prod.fst hp
  · intro h
    constructor
    · rintro ⟨f, a⟩ ⟨g, b⟩ he
      obtain ⟨f₀, _hf₀, huniq⟩ := h ((f : G) + (a : G))
      have hf : (f : G) + (a : G) - (f : G) ∈ A := by
        simp [a.property]
      have hg : (f : G) + (a : G) - (g : G) ∈ A := by
        change (f : G) + (a : G) = (g : G) + (b : G) at he
        rw [he]
        simp [b.property]
      have hfg : f = g := (huniq f hf).trans (huniq g hg).symm
      cases hfg
      have hab : a = b := Subtype.ext (add_left_cancel he)
      exact Prod.ext rfl hab
    · intro x
      obtain ⟨f, hf, _huniq⟩ := h x
      refine ⟨(f, ⟨x - (f : G), hf⟩), ?_⟩
      change (f : G) + (x - (f : G)) = x
      simp

theorem Tiles.tile_nonempty {F : Finset G} {A : Set G} (h : Tiles F A) :
    F.Nonempty := by
  obtain ⟨⟨f, _a⟩, _hx⟩ := h.2 0
  exact ⟨f, f.property⟩

theorem Tiles.complement_nonempty {F : Finset G} {A : Set G} (h : Tiles F A) :
    A.Nonempty := by
  obtain ⟨⟨_f, a⟩, _hx⟩ := h.2 0
  exact ⟨a, a.property⟩

theorem period_zero (A : Set G) : Period A 0 := by
  intro x
  simp

theorem Period.add {A : Set G} {v w : G} (hv : Period A v) (hw : Period A w) :
    Period A (v + w) := by
  intro x
  rw [← add_assoc, hw, hv]

theorem Period.neg {A : Set G} {v : G} (hv : Period A v) : Period A (-v) := by
  intro x
  simpa [sub_eq_add_neg, add_assoc] using (hv (x - v)).symm

def periodSubgroup (A : Set G) : AddSubgroup G where
  carrier := {v | Period A v}
  zero_mem' := period_zero A
  add_mem' := fun hv hw => hv.add hw
  neg_mem' := fun hv => hv.neg

end AdditiveGroup

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree

def intEquiv : ℤ ≃+ Lattice 1 where
  toFun z := fun _ => z
  invFun x := x 0
  left_inv _ := rfl
  right_inv x := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  map_add' _ _ := rfl

theorem fullyPeriodic_lattice_zero (A : Set (Lattice 0)) : FullyPeriodic A := by
  refine ⟨⊤, inferInstance, ?_⟩
  intro v _hv x
  have hx : x + v = x := Subsingleton.elim _ _
  rw [hx]

theorem lattice_zero_tile_has_fullyPeriodic_complement
    (F : Finset (Lattice 0)) (h : ∃ A, Tiles F A) :
    ∃ A, Tiles F A ∧ FullyPeriodic A := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A, hA, fullyPeriodic_lattice_zero A⟩

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators

namespace PeriodicTilingThree

def oneDValue (b : Fin 2) : ℤ := (b.val : ℤ)

private theorem oneDValue_injective : Function.Injective oneDValue := by
  intro a b h
  apply Fin.ext
  unfold oneDValue at h
  omega

def OneDConv (T : Finset ℤ) (a : ℤ → Fin 2) : Prop :=
  ∀ z : ℤ, (∑ t ∈ T, oneDValue (a (z - t))) = 1

def oneDWindow (M : ℕ) (a : ℤ → Fin 2) (n : ℤ) : Fin M → Fin 2 :=
  fun i => a (n + (i.val : ℤ))

def OneDBlockEq (M : ℕ) (a : ℤ → Fin 2) (n m : ℤ) : Prop :=
  ∀ i : ℤ, 0 ≤ i → i < (M : ℤ) → a (n + i) = a (m + i)

private theorem oneDBlockEq_of_window_eq {M : ℕ} {a : ℤ → Fin 2} {n m : ℤ}
    (h : oneDWindow M a n = oneDWindow M a m) : OneDBlockEq M a n m := by
  intro i hi hiM
  have hcast : (i.toNat : ℤ) = i := Int.toNat_of_nonneg hi
  have hbound : i.toNat < M := by omega
  have he := congrFun h (⟨i.toNat, hbound⟩ : Fin M)
  simpa only [oneDWindow, hcast] using he

def oneDIndicator (A : Set ℤ) (n : ℤ) : Fin 2 := by
  classical
  exact if n ∈ A then 1 else 0

theorem oneDConv_of_tiles {T : Finset ℤ} {A : Set ℤ} (hTile : Tiles T A) :
    OneDConv T (oneDIndicator A) := by
  classical
  intro z
  obtain ⟨t₀, ht₀, huniq⟩ := tiles_iff_unique_tile.mp hTile z
  calc
    (∑ t ∈ T, oneDValue (oneDIndicator A (z - t))) =
        oneDValue (oneDIndicator A (z - t₀.val)) := by
      apply Finset.sum_eq_single t₀.val
      · intro t ht hne
        have hnot : z - t ∉ A := by
          intro hmem
          have he := congrArg Subtype.val (huniq (⟨t, ht⟩ : ↥T) hmem)
          exact hne he
        simp [oneDIndicator, hnot, oneDValue]
      · intro hnot
        exact (hnot t₀.property).elim
    _ = 1 := by simp [oneDIndicator, ht₀, oneDValue]

theorem oneD_right_recurrence {T : Finset ℤ} {a : ℤ → Fin 2}
    (lo : ℤ) (M : ℕ) (hlo : lo ∈ T) (hConv : OneDConv T a) (n : ℤ) :
    oneDValue (a (n + (M : ℤ))) =
      1 - ∑ t ∈ T.erase lo, oneDValue (a (n + (M : ℤ) + lo - t)) := by
  have hs := Finset.sum_erase_add T
    (fun t => oneDValue (a (n + (M : ℤ) + lo - t))) hlo
  rw [hConv (n + (M : ℤ) + lo)] at hs
  have harg : n + (M : ℤ) + lo - lo = n + (M : ℤ) := by omega
  rw [harg] at hs
  omega

theorem oneD_left_recurrence {T : Finset ℤ} {a : ℤ → Fin 2}
    (lo : ℤ) (M : ℕ) (hhi : lo + (M : ℤ) ∈ T)
    (hConv : OneDConv T a) (n : ℤ) :
    oneDValue (a (n - 1)) =
      1 - ∑ t ∈ T.erase (lo + (M : ℤ)),
        oneDValue (a (n + (M : ℤ) + lo - 1 - t)) := by
  have hs := Finset.sum_erase_add T
    (fun t => oneDValue (a (n + (M : ℤ) + lo - 1 - t))) hhi
  rw [hConv (n + (M : ℤ) + lo - 1)] at hs
  have harg : n + (M : ℤ) + lo - 1 - (lo + (M : ℤ)) = n - 1 := by omega
  rw [harg] at hs
  omega

theorem oneD_block_eq_add_one {T : Finset ℤ} {a : ℤ → Fin 2}
    {lo : ℤ} {M : ℕ} (hlo : lo ∈ T)
    (hBounds : ∀ t ∈ T, lo ≤ t ∧ t ≤ lo + (M : ℤ))
    (hConv : OneDConv T a) {n m : ℤ} (hBlock : OneDBlockEq M a n m) :
    OneDBlockEq M a (n + 1) (m + 1) := by
  have hsum :
      (∑ t ∈ T.erase lo, oneDValue (a (n + (M : ℤ) + lo - t))) =
      ∑ t ∈ T.erase lo, oneDValue (a (m + (M : ℤ) + lo - t)) := by
    apply Finset.sum_congr rfl
    intro t ht
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp ht
    obtain ⟨hlo', hhi'⟩ := hBounds t hmem
    have he := hBlock ((M : ℤ) + lo - t) (by omega) (by omega)
    have hn : n + ((M : ℤ) + lo - t) = n + (M : ℤ) + lo - t := by omega
    have hm : m + ((M : ℤ) + lo - t) = m + (M : ℤ) + lo - t := by omega
    rw [hn, hm] at he
    exact congrArg oneDValue he
  have hnext : a (n + (M : ℤ)) = a (m + (M : ℤ)) := by
    apply oneDValue_injective
    rw [oneD_right_recurrence lo M hlo hConv n,
      oneD_right_recurrence lo M hlo hConv m, hsum]
  intro i hi hiM
  by_cases hinner : i + 1 < (M : ℤ)
  · have he := hBlock (i + 1) (by omega) hinner
    have hn : n + (i + 1) = n + 1 + i := by omega
    have hm : m + (i + 1) = m + 1 + i := by omega
    simpa only [hn, hm] using he
  · have hieq : i + 1 = (M : ℤ) := by omega
    have hn : n + 1 + i = n + (M : ℤ) := by omega
    have hm : m + 1 + i = m + (M : ℤ) := by omega
    simpa only [hn, hm] using hnext

theorem oneD_block_eq_sub_one {T : Finset ℤ} {a : ℤ → Fin 2}
    {lo : ℤ} {M : ℕ} (hhi : lo + (M : ℤ) ∈ T)
    (hBounds : ∀ t ∈ T, lo ≤ t ∧ t ≤ lo + (M : ℤ))
    (hConv : OneDConv T a) {n m : ℤ} (hBlock : OneDBlockEq M a n m) :
    OneDBlockEq M a (n - 1) (m - 1) := by
  have hsum :
      (∑ t ∈ T.erase (lo + (M : ℤ)),
        oneDValue (a (n + (M : ℤ) + lo - 1 - t))) =
      ∑ t ∈ T.erase (lo + (M : ℤ)),
        oneDValue (a (m + (M : ℤ) + lo - 1 - t)) := by
    apply Finset.sum_congr rfl
    intro t ht
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp ht
    obtain ⟨hlo', hhi'⟩ := hBounds t hmem
    have he := hBlock ((M : ℤ) + lo - 1 - t) (by omega) (by omega)
    have hn : n + ((M : ℤ) + lo - 1 - t) = n + (M : ℤ) + lo - 1 - t := by omega
    have hm : m + ((M : ℤ) + lo - 1 - t) = m + (M : ℤ) + lo - 1 - t := by omega
    rw [hn, hm] at he
    exact congrArg oneDValue he
  have hprev : a (n - 1) = a (m - 1) := by
    apply oneDValue_injective
    rw [oneD_left_recurrence lo M hhi hConv n,
      oneD_left_recurrence lo M hhi hConv m, hsum]
  intro i hi hiM
  by_cases hiz : i = 0
  · simpa only [hiz, add_zero] using hprev
  · have he := hBlock (i - 1) (by omega) (by omega)
    have hn : n + (i - 1) = n - 1 + i := by omega
    have hm : m + (i - 1) = m - 1 + i := by omega
    simpa only [hn, hm] using he

theorem oneD_block_eq_add_int {T : Finset ℤ} {a : ℤ → Fin 2}
    {lo : ℤ} {M : ℕ} (hlo : lo ∈ T) (hhi : lo + (M : ℤ) ∈ T)
    (hBounds : ∀ t ∈ T, lo ≤ t ∧ t ≤ lo + (M : ℤ))
    (hConv : OneDConv T a) {n m : ℤ} (hBlock : OneDBlockEq M a n m) :
    ∀ z : ℤ, OneDBlockEq M a (n + z) (m + z) := by
  have hpos : ∀ r : ℕ, OneDBlockEq M a (n + (r : ℤ)) (m + (r : ℤ)) := by
    intro r
    induction r with
    | zero => simpa only [Nat.cast_zero, add_zero] using hBlock
    | succ r ih =>
        have he := oneD_block_eq_add_one hlo hBounds hConv ih
        simpa only [Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one, add_assoc] using he
  have hneg : ∀ r : ℕ, OneDBlockEq M a (n - (r : ℤ)) (m - (r : ℤ)) := by
    intro r
    induction r with
    | zero => simpa only [Nat.cast_zero, sub_zero] using hBlock
    | succ r ih =>
        have he := oneD_block_eq_sub_one hhi hBounds hConv ih
        simpa only [Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one, sub_sub] using he
  intro z
  cases z with
  | ofNat r => exact hpos r
  | negSucc r =>
      have hn : n + Int.negSucc r = n - ((r + 1 : ℕ) : ℤ) := by omega
      have hm : m + Int.negSucc r = m - ((r + 1 : ℕ) : ℤ) := by omega
      rw [hn, hm]
      exact hneg (r + 1)

theorem oneD_period_of_conv
    (T : Finset ℤ) (a : ℤ → Fin 2) (lo : ℤ) (M : ℕ) (hM : 0 < M)
    (hlo : lo ∈ T) (hhi : lo + (M : ℤ) ∈ T)
    (hBounds : ∀ t ∈ T, lo ≤ t ∧ t ≤ lo + (M : ℤ))
    (hConv : OneDConv T a) :
    ∃ p : ℕ, 0 < p ∧ p ≤ 2 ^ M ∧ Function.Periodic a (p : ℤ) := by
  classical
  have hcard : Fintype.card (Fin M → Fin 2) < Fintype.card (Fin (2 ^ M + 1)) := by
    simp only [Fintype.card_fun, Fintype.card_fin]
    omega
  obtain ⟨i, j, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (2 ^ M + 1) => oneDWindow M a (i.val : ℤ)) hcard
  have derive : ∀ i j : Fin (2 ^ M + 1), i.val < j.val →
      oneDWindow M a (i.val : ℤ) = oneDWindow M a (j.val : ℤ) →
      ∃ p : ℕ, 0 < p ∧ p ≤ 2 ^ M ∧ Function.Periodic a (p : ℤ) := by
    intro i j hij hstate
    refine ⟨j.val - i.val, by omega, by have := j.isLt; omega, ?_⟩
    intro x
    have hBlock := oneDBlockEq_of_window_eq hstate
    have hshift := oneD_block_eq_add_int hlo hhi hBounds hConv hBlock (x - (i.val : ℤ))
    have he := hshift 0 (by omega) (by omega)
    have hn : (i.val : ℤ) + (x - (i.val : ℤ)) + 0 = x := by omega
    have hm : (j.val : ℤ) + (x - (i.val : ℤ)) + 0 =
        x + ((j.val - i.val : ℕ) : ℤ) := by omega
    rw [hn, hm] at he
    exact he.symm
  have hneval : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hneval with hij | hji
  · exact derive i j hij heq
  · exact derive j i hji heq.symm

theorem periodic_of_tiles_int
    (T : Finset ℤ) (hT : T.Nonempty) (A : Set ℤ) (hTile : Tiles T A) :
    ∃ p : ℕ, 0 < p ∧ Period A (p : ℤ) := by
  classical
  let lo : ℤ := T.min' hT
  let hi : ℤ := T.max' hT
  have hlo : lo ∈ T := T.min'_mem hT
  have hhi : hi ∈ T := T.max'_mem hT
  have hlohi : lo ≤ hi := T.min'_le hi hhi
  let M : ℕ := (hi - lo).toNat
  have hMcast : (M : ℤ) = hi - lo := Int.toNat_of_nonneg (by omega)
  have hmax : lo + (M : ℤ) ∈ T := by
    have he : lo + (M : ℤ) = hi := by omega
    rw [he]
    exact hhi
  have hBounds : ∀ t ∈ T, lo ≤ t ∧ t ≤ lo + (M : ℤ) := by
    intro t ht
    have hl : lo ≤ t := T.min'_le t ht
    have hr : t ≤ hi := T.le_max' t ht
    constructor <;> omega
  by_cases hzero : M = 0
  · have hall : ∀ z : ℤ, z ∈ A := by
      intro z
      obtain ⟨t, ht, _⟩ := tiles_iff_unique_tile.mp hTile (lo + z)
      obtain ⟨hl, hr⟩ := hBounds t.val t.property
      have hteq : t.val = lo := by omega
      simpa only [hteq, add_sub_cancel_left] using ht
    refine ⟨1, by omega, ?_⟩
    intro z
    exact ⟨fun _ => hall z, fun _ => hall (z + (1 : ℤ))⟩
  · have hM : 0 < M := Nat.pos_of_ne_zero hzero
    obtain ⟨p, hp, _, hperiod⟩ := oneD_period_of_conv T (oneDIndicator A) lo M hM
      hlo hmax hBounds (oneDConv_of_tiles hTile)
    refine ⟨p, hp, ?_⟩
    intro z
    have he := hperiod z
    constructor
    · intro hz
      by_contra hn
      simp [oneDIndicator, hz, hn] at he
    · intro hz
      by_contra hn
      simp [oneDIndicator, hz, hn] at he

theorem fullyPeriodic_of_nat_period
    (A : Set ℤ) (p : ℕ) (hp : 0 < p) (hPeriod : Period A (p : ℤ)) :
    FullyPeriodic A := by
  refine ⟨AddSubgroup.zmultiples (p : ℤ), ?_, ?_⟩
  · refine ⟨?_⟩
    simpa only [Int.index_zmultiples, Int.natAbs_natCast] using (Nat.ne_of_gt hp)
  · intro v hv
    obtain ⟨k, rfl⟩ := Int.mem_zmultiples_iff.mp hv
    have hFun : Function.Periodic (fun z : ℤ => z ∈ A) (p : ℤ) :=
      fun z => propext (hPeriod z)
    intro z
    have he : (z + (p : ℤ) * k ∈ A) = (z ∈ A) := by
      simpa only [Int.cast_id, id_def, mul_comm] using hFun.int_mul k z
    exact ⟨fun hz => Eq.mp he hz, fun hz => Eq.mpr he hz⟩

theorem fullyPeriodic_of_tiles_int
    (T : Finset ℤ) (hT : T.Nonempty) (A : Set ℤ) (hTile : Tiles T A) :
    FullyPeriodic A := by
  obtain ⟨p, hp, hPeriod⟩ := periodic_of_tiles_int T hT A hTile
  exact fullyPeriodic_of_nat_period A p hp hPeriod

theorem exists_fullyPeriodic_tiling_int
    (T : Finset ℤ) (hT : T.Nonempty) (hTile : ∃ A : Set ℤ, Tiles T A) :
    ∃ A : Set ℤ, Tiles T A ∧ FullyPeriodic A := by
  obtain ⟨A, hA⟩ := hTile
  exact ⟨A, hA, fullyPeriodic_of_tiles_int T hT A hA⟩

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

section AdditiveEquivalence

variable {G : Type uG} {H : Type uH} [AddCommGroup G] [AddCommGroup H]

theorem Tiles.image_addEquiv [DecidableEq H] {F : Finset G} {A : Set G}
    (e : G ≃+ H) (h : Tiles F A) : Tiles (F.image e) (e '' A) := by
  classical
  apply tiles_iff_unique_tile.mpr
  intro x
  obtain ⟨f, hf, huniq⟩ := tiles_iff_unique_tile.mp h (e.symm x)
  refine ⟨⟨e (f : G), Finset.mem_image.mpr ⟨(f : G), f.property, rfl⟩⟩, ?_, ?_⟩
  · refine ⟨e.symm x - (f : G), hf, ?_⟩
    change e (e.symm x - (f : G)) = x - e (f : G)
    rw [map_sub, e.apply_symm_apply]
  · intro g hg
    obtain ⟨y, hyF, hey⟩ := Finset.mem_image.mp g.property
    obtain ⟨a, ha, hea⟩ := hg
    have hyA : e.symm x - y ∈ A := by
      have heq : e.symm x - y = a := by
        apply e.injective
        rw [map_sub, e.apply_symm_apply, hey]
        exact hea.symm
      rw [heq]
      exact ha
    have hyf : (⟨y, hyF⟩ : ↥F) = f := huniq ⟨y, hyF⟩ hyA
    apply Subtype.ext
    calc
      (g : H) = e y := hey.symm
      _ = e (f : G) := congrArg e (congrArg Subtype.val hyf)

theorem tiles_image_addEquiv_iff [DecidableEq H] (e : G ≃+ H)
    {F : Finset G} {A : Set G} :
    Tiles (F.image e) (e '' A) ↔ Tiles F A := by
  classical
  constructor
  · intro h
    simpa only [Finset.image_image, Set.image_image, Function.comp_def,
      e.symm_apply_apply, Finset.image_id', Set.image_id']
      using Tiles.image_addEquiv e.symm h
  · exact Tiles.image_addEquiv e

theorem addEquiv_image_symm_eq_preimage (e : G ≃+ H) (A : Set H) :
    e.symm '' A = e ⁻¹' A := by
  exact e.toEquiv.image_symm_eq_preimage A

theorem Tiles.preimage_addEquiv [DecidableEq G] (e : G ≃+ H)
    {F : Finset H} {A : Set H} (h : Tiles F A) :
    Tiles (F.image e.symm) (e ⁻¹' A) := by
  rw [← addEquiv_image_symm_eq_preimage e A]
  exact Tiles.image_addEquiv e.symm h

theorem tiles_preimage_addEquiv_iff [DecidableEq G] (e : G ≃+ H)
    {F : Finset H} {A : Set H} :
    Tiles (F.image e.symm) (e ⁻¹' A) ↔ Tiles F A := by
  rw [← addEquiv_image_symm_eq_preimage e A]
  exact tiles_image_addEquiv_iff e.symm

end AdditiveEquivalence

section PeriodImages

variable {G : Type uG} {H : Type uH} [AddCommGroup G] [AddCommGroup H]

theorem Period.image {A : Set G} {v : G} (hv : Period A v) (f : G →+ H) :
    Period (f '' A) (f v) := by
  intro y
  constructor
  · rintro ⟨x, hx, hxy⟩
    refine ⟨x - v, ?_, ?_⟩
    · apply (hv (x - v)).mp
      simpa only [sub_add_cancel] using hx
    · rw [map_sub, hxy, add_sub_cancel_right]
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x + v, (hv x).mpr hx, f.map_add x v⟩

theorem finiteIndex_map_of_surjective (P : AddSubgroup G) (hP : P.FiniteIndex)
    (f : G →+ H) (hf : Function.Surjective f) : (P.map f).FiniteIndex := by
  constructor
  intro hz
  have hd := P.index_map_dvd hf
  rw [hz] at hd
  exact hP.index_ne_zero (Nat.eq_zero_of_zero_dvd hd)

theorem FullyPeriodic.image_of_surjective (f : G →+ H)
    (hf : Function.Surjective f) {A : Set G} (h : FullyPeriodic A) :
    FullyPeriodic (f '' A) := by
  obtain ⟨P, hP, hperiod⟩ := h
  refine ⟨P.map f, finiteIndex_map_of_surjective P hP f hf, ?_⟩
  intro w hw
  obtain ⟨v, hv, rfl⟩ := AddSubgroup.mem_map.mp hw
  exact (hperiod v hv).image f

theorem fullyPeriodic_image_addEquiv_iff (e : G ≃+ H) {A : Set G} :
    FullyPeriodic (e '' A) ↔ FullyPeriodic A := by
  constructor
  · intro h
    have h' := FullyPeriodic.image_of_surjective e.symm.toAddMonoidHom
      e.symm.surjective h
    change FullyPeriodic (e.symm '' (e '' A)) at h'
    simpa only [Set.image_image, Function.comp_def, e.symm_apply_apply,
      Set.image_id'] using h'
  · exact FullyPeriodic.image_of_surjective e.toAddMonoidHom e.surjective

theorem FullyPeriodic.preimage_addEquiv (e : G ≃+ H) {A : Set H}
    (h : FullyPeriodic A) : FullyPeriodic (e ⁻¹' A) := by
  rw [← addEquiv_image_symm_eq_preimage e A]
  exact FullyPeriodic.image_of_surjective e.symm.toAddMonoidHom e.symm.surjective h

theorem fullyPeriodic_preimage_addEquiv_iff (e : G ≃+ H) {A : Set H} :
    FullyPeriodic (e ⁻¹' A) ↔ FullyPeriodic A := by
  rw [← addEquiv_image_symm_eq_preimage e A]
  exact fullyPeriodic_image_addEquiv_iff e.symm

end PeriodImages

section FiniteCoordinate

variable {G : Type uG} {K : Type uK} [AddCommGroup G] [AddCommGroup K] [Finite K]

theorem finiteIndex_prod_bot (P : AddSubgroup G) (hP : P.FiniteIndex) :
    (P.prod (⊥ : AddSubgroup K)).FiniteIndex := by
  constructor
  rw [AddSubgroup.index_prod, AddSubgroup.index_bot]
  exact mul_ne_zero hP.index_ne_zero (ne_of_gt (Nat.card_pos : 0 < Nat.card K))

theorem FullyPeriodic.prod_singleton_zero {A : Set G} (h : FullyPeriodic A) :
    FullyPeriodic (A ×ˢ ({0} : Set K)) := by
  obtain ⟨P, hP, hperiod⟩ := h
  refine ⟨P.prod (⊥ : AddSubgroup K), finiteIndex_prod_bot P hP, ?_⟩
  intro v hv x
  obtain ⟨hp, hz⟩ := AddSubgroup.mem_prod.mp hv
  have hzero : v.2 = 0 := AddSubgroup.mem_bot.mp hz
  change (x.1 + v.1 ∈ A ∧ x.2 + v.2 ∈ ({0} : Set K)) ↔
    (x.1 ∈ A ∧ x.2 ∈ ({0} : Set K))
  rw [hzero, add_zero]
  exact and_congr (hperiod v.1 hp x.1) Iff.rfl

end FiniteCoordinate

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree

theorem fullyPeriodic_of_tiles_lattice_one
    {F : Finset (Lattice 1)} {A : Set (Lattice 1)} (h : Tiles F A) :
    FullyPeriodic A := by
  have hInt := h.preimage_addEquiv intEquiv
  have hPeriod := fullyPeriodic_of_tiles_int _ hInt.tile_nonempty _ hInt
  exact (fullyPeriodic_preimage_addEquiv_iff intEquiv).mp hPeriod

theorem lattice_one_tile_has_fullyPeriodic_complement
    (F : Finset (Lattice 1)) (h : ∃ A, Tiles F A) :
    ∃ A, Tiles F A ∧ FullyPeriodic A := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A, hA, fullyPeriodic_of_tiles_lattice_one hA⟩

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators Classical

namespace PeriodicTilingThree

variable {G : Type uG}

def tileIndicator (R : Type uR) [Zero R] [One R] (A : Set G) (x : G) : R :=
  if x ∈ A then 1 else 0

theorem tileIndicator_nonneg (A : Set G) (x : G) :
    0 ≤ tileIndicator ℝ A x := by
  classical
  unfold tileIndicator
  split_ifs <;> simp

theorem tileIndicator_le_one (A : Set G) (x : G) :
    tileIndicator ℝ A x ≤ 1 := by
  classical
  unfold tileIndicator
  split_ifs <;> simp

theorem tileIndicator_nat_le_one (A : Set G) (x : G) :
    tileIndicator ℕ A x ≤ 1 := by
  classical
  unfold tileIndicator
  split_ifs <;> simp

theorem sum_tileIndicator_cast (R : Type uR) [AddCommMonoidWithOne R]
    {ι : Type uι} (s : Finset ι) (A : Set G) (v : ι → G) :
    ((∑ i ∈ s, tileIndicator ℕ A (v i) : ℕ) : R) =
      ∑ i ∈ s, tileIndicator R A (v i) := by
  classical
  simp only [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : v i ∈ A <;> simp [tileIndicator, h]

section Counts

variable [AddCommGroup G]

def tileCount (F : Finset G) (A : Set G) (x : G) : ℕ :=
  ∑ f ∈ F, tileIndicator ℕ A (x - f)

theorem tileCount_eq_card_filter (F : Finset G) (A : Set G) (x : G) :
    tileCount F A x = (F.filter fun f => x - f ∈ A).card := by
  classical
  simp [tileCount, tileIndicator]

theorem tileCount_le_card (F : Finset G) (A : Set G) (x : G) :
    tileCount F A x ≤ F.card := by
  classical
  rw [tileCount_eq_card_filter]
  exact Finset.card_filter_le _ _

theorem tileCount_cast (R : Type uR) [AddCommMonoidWithOne R]
    (F : Finset G) (A : Set G) (x : G) :
    (tileCount F A x : R) = ∑ f ∈ F, tileIndicator R A (x - f) :=
  sum_tileIndicator_cast R F A (fun f => x - f)

theorem tiles_iff_tileCount_eq_one {F : Finset G} {A : Set G} :
    Tiles F A ↔ ∀ x : G, tileCount F A x = 1 := by
  classical
  rw [tiles_iff_unique_tile]
  constructor
  · intro h x
    obtain ⟨f, hf, hu⟩ := h x
    have he : (F.filter fun g => x - g ∈ A) = {f.val} := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hg, hga⟩
        exact congrArg Subtype.val (hu ⟨g, hg⟩ hga)
      · intro hg
        subst g
        exact ⟨f.property, hf⟩
    rw [tileCount_eq_card_filter, he, Finset.card_singleton]
  · intro h x
    obtain ⟨f, hf⟩ := Finset.card_eq_one.mp ((tileCount_eq_card_filter F A x).symm.trans (h x))
    have hm : f ∈ F ∧ x - f ∈ A := by
      apply Finset.mem_filter.mp
      rw [hf]
      exact Finset.mem_singleton_self f
    refine ⟨⟨f, hm.1⟩, hm.2, ?_⟩
    intro g hg
    apply Subtype.ext
    have hg' : g.val ∈ F.filter fun f => x - f ∈ A :=
      Finset.mem_filter.mpr ⟨g.property, hg⟩
    simpa only [hf, Finset.mem_singleton] using hg'

theorem Tiles.tileCount_eq_one {F : Finset G} {A : Set G}
    (h : Tiles F A) (x : G) : tileCount F A x = 1 :=
  tiles_iff_tileCount_eq_one.mp h x

theorem Tiles.sum_tileIndicator_eq_one {F : Finset G} {A : Set G}
    (h : Tiles F A) (R : Type uR) [AddCommMonoidWithOne R] (x : G) :
    (∑ f ∈ F, tileIndicator R A (x - f)) = 1 := by
  rw [← tileCount_cast, h.tileCount_eq_one x, Nat.cast_one]

end Counts

section MaskAction

variable {R : Type uR} [Semiring R] [AddCommGroup G]

def maskAction (m : AddMonoidAlgebra R G) (a : G → R) (x : G) : R :=
  m.coeff.sum fun y c => c * a (x - y)

@[simp] theorem maskAction_zero (a : G → R) (x : G) :
    maskAction (0 : AddMonoidAlgebra R G) a x = 0 := by
  simp [maskAction]

@[simp] theorem maskAction_single (y : G) (c : R) (a : G → R) (x : G) :
    maskAction (AddMonoidAlgebra.single y c) a x = c * a (x - y) := by
  simp [maskAction]

theorem maskAction_add (m n : AddMonoidAlgebra R G) (a : G → R) (x : G) :
    maskAction (m + n) a x = maskAction m a x + maskAction n a x := by
  simpa only [maskAction, AddMonoidAlgebra.coeff_add] using
    (Finsupp.sum_add_index' (f := m.coeff) (g := n.coeff)
      (h := fun y c => c * a (x - y))
      (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _))

theorem maskAction_sum {ι : Type uι} (s : Finset ι)
    (m : ι → AddMonoidAlgebra R G) (a : G → R) (x : G) :
    maskAction (∑ i ∈ s, m i) a x = ∑ i ∈ s, maskAction (m i) a x := by
  simpa only [maskAction, AddMonoidAlgebra.coeff_sum] using
    (Finsupp.sum_finsetSum_index (s := s) (g := fun i => (m i).coeff)
      (h := fun y c => c * a (x - y))
      (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)).symm

private theorem maskAction_single_mul (y : G) (c : R)
    (m : AddMonoidAlgebra R G) (a : G → R) (x : G) :
    maskAction (AddMonoidAlgebra.single y c * m) a x =
      c * maskAction m a (x - y) := by
  induction m using AddMonoidAlgebra.induction with
  | zero => simp
  | single_add z d m hz hd ih =>
    rw [mul_add, maskAction_add, maskAction_add, mul_add, ih]
    rw [AddMonoidAlgebra.single_mul_single, maskAction_single, maskAction_single]
    rw [mul_assoc, sub_sub]

theorem maskAction_mul (m n : AddMonoidAlgebra R G) (a : G → R) (x : G) :
    maskAction (m * n) a x = maskAction m (fun y => maskAction n a y) x := by
  induction m using AddMonoidAlgebra.induction with
  | zero => simp
  | single_add y c m hy hc ih =>
    rw [add_mul, maskAction_add, maskAction_add, ih]
    rw [maskAction_single_mul, maskAction_single]

@[simp] theorem maskAction_one (a : G → R) (x : G) :
    maskAction (1 : AddMonoidAlgebra R G) a x = a x := by
  rw [AddMonoidAlgebra.one_def, maskAction_single]
  simp

theorem maskAction_translate (m : AddMonoidAlgebra R G) (a : G → R) (x v : G) :
    maskAction m (fun y => a (y + v)) x = maskAction m a (x + v) := by
  unfold maskAction
  apply Finsupp.sum_congr
  intro y hy
  congr 2
  abel_nf

def familyMask (R : Type uR) [Semiring R] {ι : Type uι} (s : Finset ι) (v : ι → G) :
    AddMonoidAlgebra R G :=
  ∑ i ∈ s, AddMonoidAlgebra.single (v i) 1

def tileMask (R : Type uR) [Semiring R] (F : Finset G) : AddMonoidAlgebra R G :=
  familyMask R F id

theorem maskAction_familyMask {ι : Type uι} (s : Finset ι) (v : ι → G)
    (a : G → R) (x : G) :
    maskAction (familyMask R s v) a x = ∑ i ∈ s, a (x - v i) := by
  simp only [familyMask, maskAction_sum, maskAction_single, one_mul]

theorem maskAction_tileMask (F : Finset G) (a : G → R) (x : G) :
    maskAction (tileMask R F) a x = ∑ f ∈ F, a (x - f) :=
  maskAction_familyMask F id a x

theorem maskAction_familyMask_const {ι : Type uι} (s : Finset ι) (v : ι → G)
    (c : R) (x : G) :
    maskAction (familyMask R s v) (fun _ => c) x = (s.card : R) * c := by
  simp [maskAction_familyMask, nsmul_eq_mul]

theorem maskAction_familyMask_pow_const {ι : Type uι} (s : Finset ι) (v : ι → G)
    (n : ℕ) (c : R) (x : G) :
    maskAction (familyMask R s v ^ n) (fun _ => c) x = (s.card : R) ^ n * c := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', maskAction_mul]
    simp_rw [ih]
    rw [maskAction_familyMask_const, pow_succ', mul_assoc]

theorem maskAction_familyMask_pow_succ {ι : Type uι} (s : Finset ι) (v : ι → G)
    (a : G → R) (h : ∀ x, (∑ i ∈ s, a (x - v i)) = 1) (n : ℕ) (x : G) :
    maskAction (familyMask R s v ^ (n + 1)) a x = (s.card : R) ^ n := by
  rw [pow_succ, maskAction_mul]
  simp_rw [maskAction_familyMask, h]
  rw [maskAction_familyMask_pow_const, mul_one]

end MaskAction

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators Classical

namespace PeriodicTilingThree

section ArbitraryGroup

variable {G : Type uG} [AddCommGroup G]

theorem sum_tileIndicator_nat_le_card
    {G : Type uG} [AddCommGroup G]
    {ι : Type uι} (s : Finset ι)
    (A : Set G) (v : ι → G) :
    (∑ i ∈ s, tileIndicator ℕ A (v i)) ≤ s.card := by
  calc
    (∑ i ∈ s, tileIndicator ℕ A (v i)) ≤ ∑ _i ∈ s, (1 : ℕ) :=
      Finset.sum_le_sum fun i _hi => tileIndicator_nat_le_one A (v i)
    _ = s.card := by simp

theorem familyMask_pow_prime {ι : Type uι} (s : Finset ι) (v : ι → G)
    {p : ℕ} (hp : p.Prime) :
    familyMask (ZMod p) s v ^ p = familyMask (ZMod p) s (fun i => p • v i) := by
  let : Fact p.Prime := ⟨hp⟩
  let : CharP (AddMonoidAlgebra (ZMod p) G) p :=
    ⟨fun n => by
      rw [AddMonoidAlgebra.natCast_def, AddMonoidAlgebra.single_eq_zero,
        CharP.cast_eq_zero_iff (ZMod p) p]⟩
  unfold familyMask
  rw [sum_pow_char]
  apply Finset.sum_congr rfl
  intro i hi
  rw [AddMonoidAlgebra.single_pow, one_pow]

theorem sum_tileIndicator_dilate_prime {ι : Type uι} (s : Finset ι)
    (v : ι → G) (A : Set G)
    (h : ∀ x, (∑ i ∈ s, tileIndicator ℕ A (x - v i)) = 1)
    {p : ℕ} (hp : p.Prime) (hcard : s.card < p) (x : G) :
    (∑ i ∈ s, tileIndicator ℕ A (x - p • v i)) = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hpos : 0 < s.card := by
    have hb := sum_tileIndicator_nat_le_card s A (fun i => (0 : G) - v i)
    rw [h 0] at hb
    exact lt_of_lt_of_le Nat.zero_lt_one hb
  have hne : (s.card : ZMod p) ≠ 0 := by
    intro hz
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt hcard, ZMod.val_zero] at hv
    exact (Nat.ne_of_gt hpos) hv
  have hfermat : (s.card : ZMod p) ^ (p - 1) = 1 := by
    simpa only [ZMod.card] using
      (FiniteField.pow_card_sub_one_eq_one (s.card : ZMod p) hne)
  have hmod : ∀ y, (∑ i ∈ s, tileIndicator (ZMod p) A (y - v i)) = 1 := by
    intro y
    rw [← sum_tileIndicator_cast, h y, Nat.cast_one]
  have hpower : maskAction (familyMask (ZMod p) s v ^ p)
      (tileIndicator (ZMod p) A) x = (s.card : ZMod p) ^ (p - 1) := by
    simpa only [Nat.sub_add_cancel hp.one_lt.le] using
      (maskAction_familyMask_pow_succ s v (tileIndicator (ZMod p) A) hmod (p - 1) x)
  have hmod_dilate :
      (∑ i ∈ s, tileIndicator (ZMod p) A (x - p • v i)) = 1 := by
    rw [← maskAction_familyMask, ← familyMask_pow_prime s v hp, hpower, hfermat]
  have hc :
      ((∑ i ∈ s, tileIndicator ℕ A (x - p • v i) : ℕ) : ZMod p) = 1 := by
    rw [sum_tileIndicator_cast]
    exact hmod_dilate
  have hv := congrArg ZMod.val hc
  have hbound : (∑ i ∈ s, tileIndicator ℕ A (x - p • v i)) < p :=
    lt_of_le_of_lt (sum_tileIndicator_nat_le_card s A _) hcard
  rwa [ZMod.val_natCast_of_lt hbound, ZMod.val_one_eq_one_mod,
    Nat.mod_eq_of_lt hp.one_lt] at hv

theorem sum_tileIndicator_dilate_of_prime_factors {ι : Type uι} (s : Finset ι)
    (v : ι → G) (A : Set G)
    (h : ∀ x, (∑ i ∈ s, tileIndicator ℕ A (x - v i)) = 1)
    (r : ℕ) (hr : r ≠ 0)
    (hlarge : ∀ p : ℕ, p.Prime → p ∣ r → s.card < p) (x : G) :
    (∑ i ∈ s, tileIndicator ℕ A (x - r • v i)) = 1 := by
  have hall : ∀ n : ℕ, n ≠ 0 →
      (∀ p : ℕ, p.Prime → p ∣ n → s.card < p) →
      ∀ y, (∑ i ∈ s, tileIndicator ℕ A (y - n • v i)) = 1 := by
    apply induction_on_primes
    · intro hn
      exact (hn rfl).elim
    · intro _hn _hpr y
      simpa only [one_nsmul] using h y
    · intro p n hp ih hpn hpr y
      have hn : n ≠ 0 := by
        intro hn
        apply hpn
        simp [hn]
      have hprn : ∀ q : ℕ, q.Prime → q ∣ n → s.card < q := by
        intro q hq hqn
        exact hpr q hq (dvd_mul_of_dvd_right hqn p)
      have hpp : s.card < p := hpr p hp (dvd_mul_right p n)
      simpa only [mul_smul] using
        (sum_tileIndicator_dilate_prime s (fun i => n • v i) A
          (ih hn hprn) hp hpp y)
  exact hall r hr hlarge x

theorem prime_factor_factorial_mul_add_one_gt (N k p : ℕ)
    (hp : p.Prime) (hd : p ∣ 1 + N.factorial * k) : N < p := by
  by_contra hnp
  have hpf : p ∣ N.factorial := Nat.dvd_factorial hp.pos (Nat.le_of_not_gt hnp)
  have hpm : p ∣ N.factorial * k := dvd_mul_of_dvd_left hpf k
  have hpone : p ∣ 1 := (Nat.dvd_add_left hpm).mp hd
  exact hp.ne_one (Nat.dvd_one.mp hpone)

theorem Tiles.sum_tileIndicator_nat_dilate_factorial {F : Finset G} {A : Set G}
    (h : Tiles F A) (k : ℕ) (x : G) :
    (∑ f ∈ F, tileIndicator ℕ A (x - (1 + F.card.factorial * k) • f)) = 1 := by
  apply sum_tileIndicator_dilate_of_prime_factors F id A
    (fun y => h.tileCount_eq_one y) (1 + F.card.factorial * k)
  · omega
  · intro p hp hd
    exact prime_factor_factorial_mul_add_one_gt F.card k p hp hd

theorem Tiles.sum_tileIndicator_dilate_factorial {F : Finset G} {A : Set G}
    (h : Tiles F A) (k : ℕ) (x : G) :
    (∑ f ∈ F, tileIndicator ℝ A (x - (1 + F.card.factorial * k) • f)) = 1 := by
  rw [← sum_tileIndicator_cast, h.sum_tileIndicator_nat_dilate_factorial k x,
    Nat.cast_one]

def dilateTile (r : ℕ) (F : Finset G) : Finset G :=
  F.image (fun f => r • f)

end ArbitraryGroup

theorem plane_nsmul_injective {r : ℕ} (hr : r ≠ 0) :
    Function.Injective (fun x : Plane => r • x) := by
  intro x y hxy
  have hrz : (r : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hr
  apply Prod.ext
  · apply mul_left_cancel₀ hrz
    have hx : r • x.1 = r • y.1 := congrArg Prod.fst hxy
    simpa only [nsmul_eq_mul] using hx
  · apply mul_left_cancel₀ hrz
    have hy : r • x.2 = r • y.2 := congrArg Prod.snd hxy
    simpa only [nsmul_eq_mul] using hy

theorem dilateTile_card (r : ℕ) (hr : r ≠ 0) (F : Finset Plane) :
    (dilateTile r F).card = F.card := by
  let : DecidableEq Plane := fun a b => Classical.propDecidable (a = b)
  exact Finset.card_image_of_injective F (plane_nsmul_injective hr)

theorem tileCount_dilateTile (r : ℕ) (hr : r ≠ 0)
    (F : Finset Plane) (A : Set Plane) (x : Plane) :
    tileCount (dilateTile r F) A x = ∑ f ∈ F, tileIndicator ℕ A (x - r • f) := by
  let : DecidableEq Plane := fun a b => Classical.propDecidable (a = b)
  unfold tileCount dilateTile
  apply Finset.sum_image
  intro f hf g hg hfg
  exact plane_nsmul_injective hr hfg

theorem Tiles.dilate_prime {F : Finset Plane} {A : Set Plane} (h : Tiles F A)
    {p : ℕ} (hp : p.Prime) (hcard : F.card < p) : Tiles (dilateTile p F) A := by
  apply tiles_iff_tileCount_eq_one.mpr
  intro x
  rw [tileCount_dilateTile p hp.ne_zero]
  exact sum_tileIndicator_dilate_prime F id A (fun y => h.tileCount_eq_one y) hp hcard x

theorem Tiles.dilate_of_prime_factors {F : Finset Plane} {A : Set Plane}
    (h : Tiles F A) (r : ℕ) (hr : r ≠ 0)
    (hlarge : ∀ p : ℕ, p.Prime → p ∣ r → F.card < p) :
    Tiles (dilateTile r F) A := by
  apply tiles_iff_tileCount_eq_one.mpr
  intro x
  rw [tileCount_dilateTile r hr]
  exact sum_tileIndicator_dilate_of_prime_factors F id A
    (fun y => h.tileCount_eq_one y) r hr hlarge x

theorem Tiles.dilate_factorial {F : Finset Plane} {A : Set Plane}
    (h : Tiles F A) (k : ℕ) : Tiles (dilateTile (1 + F.card.factorial * k) F) A := by
  apply h.dilate_of_prime_factors (1 + F.card.factorial * k)
  · omega
  · intro p hp hd
    exact prime_factor_factorial_mul_add_one_gt F.card k p hp hd

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace PeriodicTilingThree

open scoped BigOperators

section Periods

variable {G : Type uG} [AddCommGroup G] {A : Set G} {v : G}

theorem Period.zsmul (hv : Period A v) (n : ℤ) : Period A (n • v) :=
  (periodSubgroup A).zsmul_mem hv n

theorem Period.nsmul (hv : Period A v) (n : ℕ) : Period A (n • v) :=
  (periodSubgroup A).nsmul_mem hv n

theorem exists_pos_zsmul_mem (P : AddSubgroup G) (hP : P.FiniteIndex) (v : G) :
    ∃ q : ℕ, 0 < q ∧ (q : ℤ) • v ∈ P := by
  obtain ⟨q, hq, _, hmem⟩ :=
    AddSubgroup.exists_nsmul_mem_of_index_ne_zero (H := P) hP.index_ne_zero v
  exact ⟨q, hq, by simpa only [natCast_zsmul] using hmem⟩

end Periods

def bezoutCoordinates (a b s t : ℤ) (h : s * a + t * b = 1) : Plane ≃+ Plane where
  toFun z := (a * z.1 - t * z.2, b * z.1 + s * z.2)
  invFun z := (s * z.1 + t * z.2, -b * z.1 + a * z.2)
  left_inv := by
    rintro ⟨x, y⟩
    apply Prod.ext
    · change s * (a * x - t * y) + t * (b * x + s * y) = x
      calc
        _ = (s * a + t * b) * x := by ring
        _ = x := by rw [h, one_mul]
    · change -b * (a * x - t * y) + a * (b * x + s * y) = y
      calc
        _ = (s * a + t * b) * y := by ring
        _ = y := by rw [h, one_mul]
  right_inv := by
    rintro ⟨x, y⟩
    apply Prod.ext
    · change a * (s * x + t * y) - t * (-b * x + a * y) = x
      calc
        _ = (s * a + t * b) * x := by ring
        _ = x := by rw [h, one_mul]
    · change b * (s * x + t * y) + s * (-b * x + a * y) = y
      calc
        _ = (s * a + t * b) * y := by ring
        _ = y := by rw [h, one_mul]
  map_add' := by
    rintro ⟨x, y⟩ ⟨z, w⟩
    apply Prod.ext <;> dsimp <;> ring

theorem exists_primitive_coordinates {h : Plane} (hh : h ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ T : Plane ≃+ Plane, T ((m : ℤ), 0) = h := by
  have hcoords : h.1 ≠ 0 ∨ h.2 ≠ 0 := by
    by_cases hx : h.1 = 0
    · right
      intro hy
      exact hh (Prod.ext hx hy)
    · exact Or.inl hx
  have hg : 0 < Int.gcd h.1 h.2 := Int.gcd_pos_iff.mpr hcoords
  obtain ⟨a, b, hab, ha, hb⟩ := Int.exists_gcd_one hg
  have hbez : Int.gcdA a b * a + Int.gcdB a b * b = 1 := by
    have he := Int.gcd_eq_gcd_ab a b
    rw [hab] at he
    simpa only [Int.natCast_one, mul_comm] using he.symm
  refine ⟨Int.gcd h.1 h.2, hg, bezoutCoordinates a b _ _ hbez, ?_⟩
  change (a * (Int.gcd h.1 h.2 : ℤ) - Int.gcdB a b * 0,
    b * (Int.gcd h.1 h.2 : ℤ) + Int.gcdA a b * 0) = h
  apply Prod.ext
  · simpa using ha.symm
  · simpa using hb.symm

def coordinateSubgroup (T : Plane ≃+ Plane) (m L : ℤ) : AddSubgroup Plane :=
  ((AddSubgroup.zmultiples m).prod (AddSubgroup.zmultiples L)).map T.toAddMonoidHom

theorem index_coordinateSubgroup (T : Plane ≃+ Plane) (m L : ℤ) :
    (coordinateSubgroup T m L).index = m.natAbs * L.natAbs := by
  rw [coordinateSubgroup, AddSubgroup.index_map_of_bijective T.bijective,
    AddSubgroup.index_prod, Int.index_zmultiples, Int.index_zmultiples]

theorem coordinateSubgroup_le (P : AddSubgroup Plane) (T : Plane ≃+ Plane) (m L : ℤ)
    (hm : T (m, 0) ∈ P) (hL : T (0, L) ∈ P) : coordinateSubgroup T m L ≤ P := by
  rintro z ⟨x, hx, rfl⟩
  obtain ⟨a, ha⟩ := AddSubgroup.mem_zmultiples_iff.mp hx.1
  obtain ⟨b, hb⟩ := AddSubgroup.mem_zmultiples_iff.mp hx.2
  have he : a • (m, (0 : ℤ)) + b • ((0 : ℤ), L) = x := by
    apply Prod.ext
    · simpa using ha
    · simpa using hb
  have hmem := P.add_mem (P.zsmul_mem hm a) (P.zsmul_mem hL b)
  rwa [← map_zsmul, ← map_zsmul, ← map_add, he] at hmem

theorem finiteIndex_of_coordinate_mem (P : AddSubgroup Plane) (T : Plane ≃+ Plane)
    (m L : ℤ) (hm : m ≠ 0) (hL : L ≠ 0)
    (hpm : T (m, 0) ∈ P) (hpL : T (0, L) ∈ P) : P.FiniteIndex := by
  let : (coordinateSubgroup T m L).FiniteIndex := ⟨by
    rw [index_coordinateSubgroup]
    exact mul_ne_zero (fun h => hm (Int.natAbs_eq_zero.mp h))
      (fun h => hL (Int.natAbs_eq_zero.mp h))⟩
  exact AddSubgroup.finiteIndex_of_le (coordinateSubgroup_le P T m L hpm hpL)

theorem FullyPeriodic.exists_coordinate_period {E : Set Plane}
    (hE : FullyPeriodic E) (T : Plane ≃+ Plane) :
    ∃ Q : ℕ, 0 < Q ∧ Period E (T (0, (Q : ℤ))) := by
  obtain ⟨P, hP, hperiod⟩ := hE
  obtain ⟨Q, hQ, hmem⟩ := exists_pos_zsmul_mem P hP (T (0, 1))
  have he : (Q : ℤ) • T (0, 1) = T (0, (Q : ℤ)) := by
    rw [← map_zsmul]
    congr 1
    ext <;> simp
  refine ⟨Q, hQ, ?_⟩
  rw [← he]
  exact hperiod _ hmem

theorem fullyPeriodic_of_coordinate_periods {E : Set Plane}
    (T : Plane ≃+ Plane) (m L : ℕ) (hm : 0 < m) (hL : 0 < L)
    (hx : Period E (T ((m : ℤ), 0))) (hy : Period E (T (0, (L : ℤ)))) :
    FullyPeriodic E := by
  refine ⟨periodSubgroup E, ?_, fun _ hv => hv⟩
  exact finiteIndex_of_coordinate_mem (periodSubgroup E) T m L
    (by exact_mod_cast (ne_of_gt hm)) (by exact_mod_cast (ne_of_gt hL)) hx hy

theorem Period.mem_coordinate_mod {D : Set Plane} {T : Plane ≃+ Plane} {m : ℕ}
    (hv : Period D (T ((m : ℤ), 0))) (x y : ℤ) :
    T (x, y) ∈ D ↔ T (x % (m : ℤ), y) ∈ D := by
  have he : T (x % (m : ℤ), y) + (x / (m : ℤ)) • T ((m : ℤ), 0) = T (x, y) := by
    rw [← map_zsmul, ← map_add]
    congr 1
    apply Prod.ext
    · change x % (m : ℤ) + (x / (m : ℤ)) * (m : ℤ) = x
      simpa only [add_comm, mul_comm] using Int.emod_add_mul_ediv x (m : ℤ)
    · simp
  have hp := (hv.zsmul (x / (m : ℤ))) (T (x % (m : ℤ), y))
  rwa [he] at hp

def planeDet (u v : Plane) : ℤ := u.1 * v.2 - u.2 * v.1

@[simp] theorem planeDet_self (u : Plane) : planeDet u u = 0 := by
  simp [planeDet, mul_comm]

theorem planeDet_swap (u v : Plane) : planeDet u v = -planeDet v u := by
  dsimp [planeDet]
  ring

theorem planeDet_zsmul_left (n : ℤ) (u v : Plane) :
    planeDet (n • u) v = n * planeDet u v := by
  change (n * u.1) * v.2 - (n * u.2) * v.1 = n * (u.1 * v.2 - u.2 * v.1)
  ring

theorem planeDet_zsmul_right (n : ℤ) (u v : Plane) :
    planeDet u (n • v) = n * planeDet u v := by
  change u.1 * (n * v.2) - u.2 * (n * v.1) = n * (u.1 * v.2 - u.2 * v.1)
  ring

theorem zsmul_plane_ne_zero {n : ℤ} {v : Plane} (hn : n ≠ 0) (hv : v ≠ 0) :
    n • v ≠ 0 := by
  intro he
  apply hv
  apply Prod.ext
  · have h := congrArg Prod.fst he
    change n * v.1 = 0 at h
    exact (mul_eq_zero.mp h).resolve_left hn
  · have h := congrArg Prod.snd he
    change n * v.2 = 0 at h
    exact (mul_eq_zero.mp h).resolve_left hn

def integerCombination (u v : Plane) : Plane →+ Plane where
  toFun z := z.1 • u + z.2 • v
  map_zero' := by simp
  map_add' := by
    intro x y
    change (x.1 + y.1) • u + (x.2 + y.2) • v =
      (x.1 • u + x.2 • v) + (y.1 • u + y.2 • v)
    rw [add_smul, add_smul]
    abel

def integerSpan2 (u v : Plane) : AddSubgroup Plane := (integerCombination u v).range

theorem mem_integerSpan2 (u v z : Plane) :
    z ∈ integerSpan2 u v ↔ ∃ a b : ℤ, a • u + b • v = z := by
  constructor
  · rintro ⟨⟨a, b⟩, he⟩
    exact ⟨a, b, he⟩
  · rintro ⟨a, b, he⟩
    exact ⟨(a, b), he⟩

theorem determinant_smul_eq (u v z : Plane) :
    planeDet u v • z = planeDet z v • u + planeDet u z • v := by
  apply Prod.ext
  · change (u.1 * v.2 - u.2 * v.1) * z.1 =
      (z.1 * v.2 - z.2 * v.1) * u.1 + (u.1 * z.2 - u.2 * z.1) * v.1
    ring
  · change (u.1 * v.2 - u.2 * v.1) * z.2 =
      (z.1 * v.2 - z.2 * v.1) * u.2 + (u.1 * z.2 - u.2 * z.1) * v.2
    ring

theorem integerSpan2_finiteIndex (u v : Plane) (huv : planeDet u v ≠ 0) :
    (integerSpan2 u v).FiniteIndex := by
  have hm (z : Plane) : planeDet u v • z ∈ integerSpan2 u v :=
    (mem_integerSpan2 u v _).mpr ⟨planeDet z v, planeDet u z,
      (determinant_smul_eq u v z).symm⟩
  apply finiteIndex_of_coordinate_mem (integerSpan2 u v) (AddEquiv.refl Plane)
    (planeDet u v) (planeDet u v) huv huv
  · simpa using hm (1, 0)
  · simpa using hm (0, 1)

theorem fullyPeriodic_of_independent_periods {E : Set Plane} {u v : Plane}
    (hu : Period E u) (hv : Period E v) (huv : planeDet u v ≠ 0) : FullyPeriodic E := by
  refine ⟨integerSpan2 u v, integerSpan2_finiteIndex u v huv, ?_⟩
  intro z hz
  obtain ⟨a, b, rfl⟩ := (mem_integerSpan2 u v z).mp hz
  exact (hu.zsmul a).add (hv.zsmul b)

theorem exists_smul_eq_of_collinear {u v : Plane}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : planeDet u v = 0) :
    ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • u = b • v := by
  by_cases hu₁ : u.1 = 0
  · have hu₂ : u.2 ≠ 0 := fun h => hu (Prod.ext hu₁ h)
    have he : u.2 * v.1 = 0 := by
      simpa only [planeDet, hu₁, zero_mul, zero_sub, neg_eq_zero] using huv
    have hv₁ : v.1 = 0 := (mul_eq_zero.mp he).resolve_left hu₂
    have hv₂ : v.2 ≠ 0 := fun h => hv (Prod.ext hv₁ h)
    refine ⟨v.2, u.2, hv₂, hu₂, ?_⟩
    apply Prod.ext
    · change v.2 * u.1 = u.2 * v.1
      simp [hu₁, hv₁]
    · change v.2 * u.2 = u.2 * v.2
      exact mul_comm _ _
  · have he : u.1 * v.2 = u.2 * v.1 := sub_eq_zero.mp huv
    have hv₁ : v.1 ≠ 0 := by
      intro hv₁
      have hv₂ : v.2 = 0 := (mul_eq_zero.mp (by simpa [hv₁] using he)).resolve_left hu₁
      exact hv (Prod.ext hv₁ hv₂)
    refine ⟨v.1, u.1, hv₁, hu₁, ?_⟩
    apply Prod.ext
    · change v.1 * u.1 = u.1 * v.1
      exact mul_comm _ _
    · change v.1 * u.2 = u.1 * v.2
      simpa only [mul_comm] using he.symm

theorem planeDet_zero_trans {u v w : Plane} (hv : v ≠ 0)
    (huv : planeDet u v = 0) (hvw : planeDet v w = 0) : planeDet u w = 0 := by
  by_cases hu : u = 0
  · simp [hu, planeDet]
  obtain ⟨a, b, ha, _, he⟩ := exists_smul_eq_of_collinear hu hv huv
  have hd : planeDet (a • u) w = planeDet (b • v) w :=
    congrArg (fun z => planeDet z w) he
  rw [planeDet_zsmul_left, planeDet_zsmul_left, hvw, mul_zero] at hd
  exact (mul_eq_zero.mp hd).resolve_left ha

theorem exists_common_collinear_multiple (s : Finset Plane) (hne : s.Nonempty)
    (h0 : ∀ v ∈ s, v ≠ 0)
    (hcol : ∀ v ∈ s, ∀ w ∈ s, planeDet v w = 0) :
    ∃ u : Plane, u ≠ 0 ∧ ∀ v ∈ s, ∃ n : ℤ, u = n • v := by
  classical
  obtain ⟨v₀, hv₀⟩ := hne
  have hex : ∀ w : ↥s, ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • v₀ = b • (w : Plane) :=
    fun w => exists_smul_eq_of_collinear (h0 v₀ hv₀) (h0 w w.property)
      (hcol v₀ hv₀ w w.property)
  choose a b ha hb he using hex
  let c : ℤ := ∏ w : ↥s, a w
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun w _ => ha w)
  refine ⟨c • v₀, zsmul_plane_ne_zero hc (h0 v₀ hv₀), ?_⟩
  intro v hv
  let w : ↥s := ⟨v, hv⟩
  let d : ℤ := ∏ w' ∈ (Finset.univ.erase w), a w'
  have hdc : d * a w = c := by
    exact Finset.prod_erase_mul _ _ (Finset.mem_univ w)
  refine ⟨d * b w, ?_⟩
  calc
    c • v₀ = (d * a w) • v₀ := by rw [hdc]
    _ = d • (a w • v₀) := mul_smul _ _ _
    _ = d • (b w • v) := by rw [he w]
    _ = (d * b w) • v := (mul_smul _ _ _).symm

theorem exists_transverse_vector (s : Finset Plane) (h0 : ∀ v ∈ s, v ≠ 0) :
    ∃ e : Plane, e ≠ 0 ∧ ∀ v ∈ s, planeDet e v ≠ 0 := by
  classical
  obtain ⟨N, hN⟩ := (s.image (fun v => v.2 / v.1)).exists_notMem
  refine ⟨(1, N), by simp, ?_⟩
  intro v hv he
  have he' : v.2 = N * v.1 := by
    change 1 * v.2 - N * v.1 = 0 at he
    simpa only [one_mul] using sub_eq_zero.mp he
  have hv₁ : v.1 ≠ 0 := by
    intro hv₁
    have hv₂ : v.2 = 0 := by simpa [hv₁] using he'
    exact h0 v hv (Prod.ext hv₁ hv₂)
  apply hN
  apply Finset.mem_image.mpr
  refine ⟨v, hv, ?_⟩
  rw [he']
  exact Int.mul_ediv_cancel N hv₁

theorem exists_common_transverse {ι : Type uι} [Fintype ι]
    (v : ι → Plane) (h0 : ∀ i, v i ≠ 0)
    (hpair : ∀ i j, i ≠ j → planeDet (v i) (v j) ≠ 0) :
    ∃ e : Plane, e ≠ 0 ∧ (∀ i, planeDet e (v i) ≠ 0) ∧
      ∀ i j, i ≠ j → ∃ a b : ℤ, e = a • v i + b • v j := by
  classical
  obtain ⟨w, hw, htrans⟩ := exists_transverse_vector (Finset.univ.image v) (by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact h0 i)
  let J := {ij : ι × ι // ij.1 ≠ ij.2}
  let P : AddSubgroup Plane := ⨅ ij : J, integerSpan2 (v ij.val.1) (v ij.val.2)
  have hP : P.FiniteIndex := AddSubgroup.finiteIndex_iInf
    (fun ij : J => integerSpan2_finiteIndex _ _ (hpair _ _ ij.property))
  obtain ⟨q, hq, hmem⟩ := exists_pos_zsmul_mem P hP w
  have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  refine ⟨(q : ℤ) • w, zsmul_plane_ne_zero hq' hw, ?_, ?_⟩
  · intro i
    rw [planeDet_zsmul_left]
    exact mul_ne_zero hq' (htrans (v i) (Finset.mem_image_of_mem v (Finset.mem_univ i)))
  · intro i j hij
    have hm : (q : ℤ) • w ∈ integerSpan2 (v i) (v j) :=
      (AddSubgroup.mem_iInf.mp hmem) (⟨(i, j), hij⟩ : J)
    obtain ⟨a, b, he⟩ := (mem_integerSpan2 _ _ _).mp hm
    exact ⟨a, b, he.symm⟩

theorem exists_common_second_vector {ι : Type uι} [Fintype ι]
    (v : ι → Plane) (i₀ : ι) (e : Plane)
    (htrans : ∀ i, planeDet e (v i) ≠ 0) :
    ∃ K : ℕ, 0 < K ∧ ∀ i, ∃ a b : ℤ, a ≠ 0 ∧
      (K : ℤ) • v i₀ = b • e + a • v i := by
  let P : AddSubgroup Plane := ⨅ i, integerSpan2 e (v i)
  have hP : P.FiniteIndex := AddSubgroup.finiteIndex_iInf
    (fun i => integerSpan2_finiteIndex e (v i) (htrans i))
  obtain ⟨K, hK, hmem⟩ := exists_pos_zsmul_mem P hP (v i₀)
  have hK' : (K : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hK)
  refine ⟨K, hK, ?_⟩
  intro i
  obtain ⟨b, a, he⟩ := (mem_integerSpan2 e (v i) _).mp
    ((AddSubgroup.mem_iInf.mp hmem) i)
  refine ⟨a, b, ?_, he.symm⟩
  intro ha
  have hd : planeDet e ((K : ℤ) • v i₀) = 0 := by
    rw [← he, ha, zero_smul, add_zero, planeDet_zsmul_right, planeDet_self, mul_zero]
  rw [planeDet_zsmul_right] at hd
  exact mul_ne_zero hK' (htrans i₀) hd

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace PeriodicTilingThree

open Set Filter
open scoped BigOperators Topology

def directionalAverage (a : Plane → ℝ) (q : ℕ) (v : Plane) (N : ℕ) (x : Plane) : ℝ :=
  (∑ k ∈ Finset.range (N + 1), a (x - (1 + q * (k + 1)) • v)) / (N + 1 : ℕ)

theorem directionalAverage_nonneg {a : Plane → ℝ} (ha : ∀ x, 0 ≤ a x)
    (q : ℕ) (v : Plane) (N : ℕ) (x : Plane) :
    0 ≤ directionalAverage a q v N x := by
  unfold directionalAverage
  exact div_nonneg (Finset.sum_nonneg fun k _ => ha _) (by positivity)

theorem directionalAverage_le_one {a : Plane → ℝ} (ha : ∀ x, a x ≤ 1)
    (q : ℕ) (v : Plane) (N : ℕ) (x : Plane) :
    directionalAverage a q v N x ≤ 1 := by
  have hN : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  apply (div_le_iff₀ hN).2
  calc
    _ ≤ ∑ _k ∈ Finset.range (N + 1), (1 : ℝ) :=
      Finset.sum_le_sum fun k _ => ha _
    _ = _ := by simp

theorem directionalAverage_translate_sub (a : Plane → ℝ) (q : ℕ)
    (v : Plane) (N : ℕ) (x : Plane) :
    directionalAverage a q v N (x + q • v) - directionalAverage a q v N x =
      (a (x - v) - a (x - (1 + q * (N + 1)) • v)) / (N + 1 : ℕ) := by
  have hshift (k : ℕ) :
      x + q • v - (1 + q * (k + 1)) • v = x - (1 + q * k) • v := by
    have hk : 1 + q * (k + 1) = (1 + q * k) + q := by ring
    rw [hk, add_nsmul]
    abel
  unfold directionalAverage
  simp_rw [hshift]
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  simpa only [Nat.mul_zero, Nat.add_zero, one_nsmul] using
    Finset.sum_range_sub' (fun k => a (x - (1 + q * k) • v)) (N + 1)

theorem directionalAverage_translate_error {a : Plane → ℝ}
    (ha0 : ∀ x, 0 ≤ a x) (ha1 : ∀ x, a x ≤ 1)
    (q : ℕ) (v : Plane) (N : ℕ) (x : Plane) :
    |directionalAverage a q v N (x + q • v) - directionalAverage a q v N x| ≤
      1 / (N + 1 : ℕ) := by
  rw [directionalAverage_translate_sub, abs_div,
    abs_of_pos (show (0 : ℝ) < (N + 1 : ℕ) by positivity)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply abs_le.mpr
  constructor <;> linarith [ha0 (x - v), ha1 (x - v),
    ha0 (x - (1 + q * (N + 1)) • v), ha1 (x - (1 + q * (N + 1)) • v)]

theorem sum_directionalAverage {F : Finset Plane} (h0 : (0 : Plane) ∈ F)
    {a : Plane → ℝ} {q : ℕ}
    (hD : ∀ (k : ℕ) (x : Plane), ∑ f ∈ F, a (x - (1 + q * k) • f) = 1)
    (N : ℕ) (x : Plane) :
    (∑ f ∈ F.erase 0, directionalAverage a q f N x) = 1 - a x := by
  classical
  have hs (k : ℕ) :
      (∑ f ∈ F.erase 0, a (x - (1 + q * (k + 1)) • f)) = 1 - a x := by
    have he := Finset.sum_erase_add F
      (fun f => a (x - (1 + q * (k + 1)) • f)) h0
    rw [hD (k + 1) x] at he
    simpa only [smul_zero, sub_zero] using (eq_sub_iff_add_eq.mpr he)
  unfold directionalAverage
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [hs]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact mul_div_cancel_left₀ (1 - a x) (by positivity)

theorem exists_common_directional_subsequence {ι : Type uι} [Countable ι]
    (u : ℕ → ι → Plane → ℝ)
    (hu0 : ∀ N i x, 0 ≤ u N i x) (hu1 : ∀ N i x, u N i x ≤ 1) :
    ∃ (φ : ι → Plane → ℝ) (σ : ℕ → ℕ), StrictMono σ ∧
      (∀ i x, 0 ≤ φ i x ∧ φ i x ≤ 1) ∧
      ∀ i x, Tendsto (fun N => u (σ N) i x) atTop (𝓝 (φ i x)) := by
  let u' : ℕ → ((ι × Plane) → Set.Icc (0 : ℝ) 1) :=
    fun N ix => ⟨u N ix.1 ix.2, hu0 N ix.1 ix.2, hu1 N ix.1 ix.2⟩
  obtain ⟨l, σ, hσ, hl⟩ := CompactSpace.tendsto_subseq u'
  refine ⟨fun i x => (l (i, x) : ℝ), σ, hσ, ?_, ?_⟩
  · intro i x
    exact (l (i, x)).property
  · intro i x
    exact ((continuous_subtype_val.comp (continuous_apply (i, x))).tendsto l).comp hl

theorem exists_ungrouped_directional_limits {F : Finset Plane} (h0 : (0 : Plane) ∈ F)
    {a : Plane → ℝ} (ha0 : ∀ x, 0 ≤ a x) (ha1 : ∀ x, a x ≤ 1)
    {q : ℕ}
    (hD : ∀ (k : ℕ) (x : Plane), ∑ f ∈ F, a (x - (1 + q * k) • f) = 1) :
    ∃ φ : ↥(F.erase 0) → Plane → ℝ,
      (∀ f x, 0 ≤ φ f x ∧ φ f x ≤ 1) ∧
      (∀ x, a x + ∑ f, φ f x = 1) ∧
      ∀ f, Function.Periodic (φ f) (q • (f : Plane)) := by
  classical
  obtain ⟨φ, σ, hσ, hφ, hlim⟩ := exists_common_directional_subsequence
    (fun N (f : ↥(F.erase 0)) x => directionalAverage a q f N x)
    (fun N f x => directionalAverage_nonneg ha0 q f N x)
    (fun N f x => directionalAverage_le_one ha1 q f N x)
  refine ⟨φ, hφ, ?_, ?_⟩
  · intro x
    have hsum := tendsto_finsetSum Finset.univ (fun (f : ↥(F.erase 0)) _ => hlim f x)
    have havg (N : ℕ) :
        (∑ f : ↥(F.erase 0), directionalAverage a q f (σ N) x) = 1 - a x := by
      exact (Finset.sum_coe_sort (F.erase 0)
        (fun f : Plane => directionalAverage a q f (σ N) x)).trans
          (sum_directionalAverage h0 hD (σ N) x)
    have heq : (∑ f, φ f x) = 1 - a x :=
      tendsto_nhds_unique hsum (by simpa only [havg] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => 1 - a x) atTop (𝓝 (1 - a x))))
    linarith
  · intro f x
    have herr := (hlim f (x + q • (f : Plane))).sub (hlim f x)
    have hbound : Tendsto (fun N : ℕ => (1 : ℝ) / (σ N + 1 : ℕ)) atTop (𝓝 0) :=
      (tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).comp
        hσ.tendsto_atTop
    have hz := squeeze_zero (fun N => abs_nonneg
      (directionalAverage a q f (σ N) (x + q • (f : Plane)) -
        directionalAverage a q f (σ N) x))
      (fun N => directionalAverage_translate_error ha0 ha1 q f (σ N) x) hbound
    have heq : |φ f (x + q • (f : Plane)) - φ f x| = 0 :=
      tendsto_nhds_unique herr.abs hz
    exact sub_eq_zero.mp (abs_eq_zero.mp heq)

theorem Tiles.exists_ungrouped_directional_limits {F : Finset Plane} {A : Set Plane}
    (h : Tiles F A) (h0 : (0 : Plane) ∈ F) :
    ∃ φ : ↥(F.erase 0) → Plane → ℝ,
      (∀ f x, 0 ≤ φ f x ∧ φ f x ≤ 1) ∧
      (∀ x, tileIndicator ℝ A x + ∑ f, φ f x = 1) ∧
      ∀ f, Function.Periodic (φ f) (F.card.factorial • (f : Plane)) := by
  exact PeriodicTilingThree.exists_ungrouped_directional_limits h0
    (fun x => tileIndicator_nonneg A x) (fun x => tileIndicator_le_one A x)
    (fun k x => h.sum_tileIndicator_dilate_factorial k x)

theorem exists_grouped_directional_functions {ι : Type uι} [Fintype ι]
    (v : ι → Plane) (hv : ∀ i, v i ≠ 0) (φ : ι → Plane → ℝ)
    (hφ : ∀ i x, 0 ≤ φ i x) (hp : ∀ i, Function.Periodic (φ i) (v i))
    {a : Plane → ℝ} (ha : ∀ x, 0 ≤ a x)
    (hsum : ∀ x, a x + ∑ i, φ i x = 1) :
    ∃ (m : ℕ) (w : Fin m → Plane) (ψ : Fin m → Plane → ℝ),
      (∀ j, w j ≠ 0) ∧
      (∀ i j, i ≠ j → planeDet (w i) (w j) ≠ 0) ∧
      (∀ j x, 0 ≤ ψ j x ∧ ψ j x ≤ 1) ∧
      (∀ x, a x + ∑ j, ψ j x = 1) ∧
      ∀ j, Function.Periodic (ψ j) (w j) := by
  classical
  let r : Setoid ι :=
    { r := fun i j => planeDet (v i) (v j) = 0
      iseqv := ⟨fun i => planeDet_self (v i),
        fun {i j} hij => by rw [planeDet_swap, hij, neg_zero],
        fun {i j k} hij hjk => planeDet_zero_trans (hv j) hij hjk⟩ }
  let Q := Quotient r
  let : Fintype Q := Fintype.ofFinite Q
  let cls : ι → Q := Quotient.mk r
  let fiber (j : Q) : Finset ι := Finset.univ.filter (fun i => cls i = j)
  have mem_fiber (i : ι) (j : Q) : i ∈ fiber j ↔ cls i = j := by
    simp [fiber]
  have out_mem (j : Q) : j.out ∈ fiber j :=
    (mem_fiber _ _).2 (Quotient.out_eq j)
  have hex (j : Q) : ∃ w : Plane, w ≠ 0 ∧ ∀ i ∈ fiber j, ∃ n : ℤ, w = n • v i := by
    have himage : ((fiber j).image v).Nonempty :=
      ⟨v j.out, Finset.mem_image_of_mem v (out_mem j)⟩
    obtain ⟨w, hw, hm⟩ := exists_common_collinear_multiple ((fiber j).image v) himage
      (by
        intro z hz
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
        exact hv i)
      (by
        intro z hz z' hz'
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hz'
        exact Quotient.exact (((mem_fiber i j).1 hi).trans ((mem_fiber i' j).1 hi').symm))
    exact ⟨w, hw, fun i hi => hm (v i) (Finset.mem_image_of_mem v hi)⟩
  choose w hw hm using hex
  let ψ : Q → Plane → ℝ := fun j x => ∑ i ∈ fiber j, φ i x
  have hψ (j : Q) (x : Plane) : 0 ≤ ψ j x :=
    Finset.sum_nonneg (fun i _ => hφ i x)
  have htotal (x : Plane) : (∑ j, ψ j x) = ∑ i, φ i x := by
    simp only [ψ, fiber, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single (cls i)]
    · simp only [ite_true]
    · intro j _ hji
      exact ite_eq_right (Ne.symm hji)
    · intro hi
      exact False.elim (hi (Finset.mem_univ _))
  have hψone (j : Q) (x : Plane) : ψ j x ≤ 1 := by
    have hj : ψ j x ≤ ∑ j', ψ j' x :=
      Finset.single_le_sum (fun j' _ => hψ j' x) (Finset.mem_univ j)
    rw [htotal] at hj
    linarith [hsum x, ha x]
  have hper (j : Q) : Function.Periodic (ψ j) (w j) := by
    intro x
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨n, hn⟩ := hm j i hi
    rw [hn]
    exact (hp i).zsmul n x
  have hpair (j k : Q) (hjk : j ≠ k) : planeDet (w j) (w k) ≠ 0 := by
    intro hdet
    obtain ⟨n, hn⟩ := hm j j.out (out_mem j)
    obtain ⟨m, hmk⟩ := hm k k.out (out_mem k)
    have hn0 : n ≠ 0 := by
      intro hn0
      exact hw j (by simpa [hn0] using hn)
    have hm0 : m ≠ 0 := by
      intro hm0
      exact hw k (by simpa [hm0] using hmk)
    rw [hn, hmk, planeDet_zsmul_left, planeDet_zsmul_right] at hdet
    have hz : planeDet (v j.out) (v k.out) = 0 :=
      (mul_eq_zero.mp ((mul_eq_zero.mp hdet).resolve_left hn0)).resolve_left hm0
    apply hjk
    calc
      j = cls j.out := (Quotient.out_eq j).symm
      _ = cls k.out := Quotient.sound hz
      _ = k := Quotient.out_eq k
  let e : Fin (Fintype.card Q) ≃ Q := (Fintype.equivFin Q).symm
  refine ⟨Fintype.card Q, fun j => w (e j), fun j => ψ (e j),
    fun j => hw (e j), ?_, ?_, ?_, fun j => hper (e j)⟩
  · intro i j hij
    exact hpair (e i) (e j) (fun he => hij (e.injective he))
  · intro j x
    exact ⟨hψ (e j) x, hψone (e j) x⟩
  · intro x
    rw [e.sum_comp (fun j => ψ j x), htotal]
    exact hsum x

theorem Tiles.exists_directional_decomposition {F : Finset Plane} {A : Set Plane}
    (h : Tiles F A) (h0 : (0 : Plane) ∈ F) :
    ∃ (m : ℕ) (v : Fin m → Plane) (φ : Fin m → Plane → ℝ),
      (∀ j, v j ≠ 0) ∧
      (∀ i j, i ≠ j → planeDet (v i) (v j) ≠ 0) ∧
      (∀ j x, 0 ≤ φ j x ∧ φ j x ≤ 1) ∧
      (∀ x, tileIndicator ℝ A x + ∑ j, φ j x = 1) ∧
      ∀ j, Function.Periodic (φ j) (v j) := by
  classical
  obtain ⟨φ, hφ, hsum, hp⟩ := h.exists_ungrouped_directional_limits h0
  apply exists_grouped_directional_functions
    (fun f : ↥(F.erase 0) => F.card.factorial • (f : Plane)) _ φ
    (fun f x => (hφ f x).1) hp (fun x => tileIndicator_nonneg A x) hsum
  intro f
  have hq : (F.card.factorial : ℤ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero F.card
  simpa only [natCast_zsmul] using
    zsmul_plane_ne_zero hq (Finset.mem_erase.mp f.property).1

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

variable {G : Type uG} {A : Type uA} [AddCommGroup G] [AddCommGroup A]

def configDiff (v : G) (f : G → A) : G → A :=
  fun x => f (x + v) - f x

@[simp] theorem configDiff_apply (v : G) (f : G → A) (x : G) :
    configDiff v f x = f (x + v) - f x := rfl

@[simp] theorem configDiff_zero (v : G) : configDiff v (0 : G → A) = 0 := by
  ext x
  simp [configDiff]

@[simp] theorem configDiff_const (v : G) (a : A) :
    configDiff v (fun _ : G => a) = 0 := by
  ext x
  simp [configDiff]

theorem configDiff_add (v : G) (f g : G → A) :
    configDiff v (f + g) = configDiff v f + configDiff v g := by
  ext x
  simp only [configDiff_apply, Pi.add_apply]
  abel

theorem configDiff_sub (v : G) (f g : G → A) :
    configDiff v (f - g) = configDiff v f - configDiff v g := by
  ext x
  simp only [configDiff_apply, Pi.sub_apply]
  abel

theorem configDiff_comm (v w : G) (f : G → A) :
    configDiff v (configDiff w f) = configDiff w (configDiff v f) := by
  ext x
  have h : x + v + w = x + w + v := by abel
  simp only [configDiff_apply, h]
  abel

theorem configDiff_eq_zero_iff (v : G) (f : G → A) :
    configDiff v f = 0 ↔ Function.Periodic f v := by
  constructor
  · intro h x
    have hx := congrFun h x
    exact sub_eq_zero.mp hx
  · intro h
    ext x
    exact sub_eq_zero.mpr (h x)

theorem configDiff_add_period (v p : G) (f : G → A)
    (hp : Function.Periodic f p) : configDiff (v + p) f = configDiff v f := by
  ext x
  simp only [configDiff_apply, ← add_assoc, hp (x + v)]

theorem configDiff_preserves_period (v p : G) (f : G → A)
    (hp : Function.Periodic f p) : Function.Periodic (configDiff v f) p := by
  apply (configDiff_eq_zero_iff p _).mp
  rw [configDiff_comm, (configDiff_eq_zero_iff p f).mpr hp, configDiff_zero]

theorem configDiff_sum {ι : Type uι} (s : Finset ι) (v : G) (f : ι → G → A) :
    configDiff v (∑ i ∈ s, f i) = ∑ i ∈ s, configDiff v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, configDiff_add, ih]

def configDiffs : List G → (G → A) → (G → A)
  | [], f => f
  | v :: vs, f => configDiff v (configDiffs vs f)

@[simp] theorem configDiffs_nil (f : G → A) : configDiffs [] f = f := rfl

@[simp] theorem configDiffs_cons (v : G) (vs : List G) (f : G → A) :
    configDiffs (v :: vs) f = configDiff v (configDiffs vs f) := rfl

@[simp] theorem configDiffs_zero (vs : List G) :
    configDiffs vs (0 : G → A) = 0 := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [configDiffs_cons, ih, configDiff_zero]

theorem configDiff_configDiffs (v : G) (vs : List G) (f : G → A) :
    configDiff v (configDiffs vs f) = configDiffs vs (configDiff v f) := by
  induction vs with
  | nil => rfl
  | cons w vs ih =>
      simp only [configDiffs_cons, configDiff_comm v w, ih]

theorem configDiffs_add (vs : List G) (f g : G → A) :
    configDiffs vs (f + g) = configDiffs vs f + configDiffs vs g := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [configDiffs_cons, ih, configDiff_add]

theorem configDiffs_sub (vs : List G) (f g : G → A) :
    configDiffs vs (f - g) = configDiffs vs f - configDiffs vs g := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [configDiffs_cons, ih, configDiff_sub]

theorem configDiffs_sum {ι : Type uι} (s : Finset ι) (vs : List G)
    (f : ι → G → A) :
    configDiffs vs (∑ i ∈ s, f i) = ∑ i ∈ s, configDiffs vs (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, configDiffs_add, ih]

theorem configDiffs_eq_zero_of_mem {v : G} {vs : List G} (hv : v ∈ vs)
    (f : G → A) (hf : configDiff v f = 0) : configDiffs vs f = 0 := by
  induction vs with
  | nil => simp at hv
  | cons w vs ih =>
      rcases List.mem_cons.mp hv with h | h
      · subst w
        rw [configDiffs_cons, configDiff_configDiffs, hf, configDiffs_zero]
      · rw [configDiffs_cons, ih h, configDiff_zero]

theorem configDiffs_const {vs : List G} (hvs : vs ≠ []) (a : A) :
    configDiffs vs (fun _ : G => a) = 0 := by
  cases vs with
  | nil => exact (hvs rfl).elim
  | cons v vs =>
      rw [configDiffs_cons, configDiff_configDiffs, configDiff_const,
        configDiffs_zero]

theorem configDiffs_preserves_period (vs : List G) (p : G) (f : G → A)
    (hp : Function.Periodic f p) : Function.Periodic (configDiffs vs f) p := by
  apply (configDiff_eq_zero_iff p _).mp
  rw [configDiff_configDiffs, (configDiff_eq_zero_iff p f).mpr hp,
    configDiffs_zero]

theorem configDiffs_replicate (n : ℕ) (v : G) (f : G → A) :
    configDiffs (List.replicate n v) f = (configDiff v)^[n] f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, configDiffs_cons, ih,
        Function.iterate_succ_apply']

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

variable {G : Type uG} {A : Type uA} {B : Type uB}
  [AddCommGroup G] [AddCommGroup A] [AddCommGroup B]

theorem configDiffs_eq_iterate_of_period (vs : List G) (v p : G) (f : G → A)
    (hp : Function.Periodic f p)
    (hvs : ∀ u ∈ vs, ∃ k : ℤ, u = v + k • p) :
    configDiffs vs f = (configDiff v)^[vs.length] f := by
  induction vs with
  | nil => rfl
  | cons u vs ih =>
      obtain ⟨k, hk⟩ := hvs u (List.mem_cons_self ..)
      have htail : ∀ w ∈ vs, ∃ k : ℤ, w = v + k • p := by
        intro w hw
        exact hvs w (List.mem_cons_of_mem _ hw)
      have hper := (configDiffs_preserves_period vs p f hp).zsmul k
      rw [configDiffs_cons, hk, configDiff_add_period v (k • p) _ hper,
        ih htail, List.length_cons, Function.iterate_succ_apply']

theorem configDiffs_component_zero {ι : Type uι} [Fintype ι]
    (j : ι) (vs : List G) (hvs : vs ≠ []) (f : ι → G → A) (a : A)
    (hsum : (∑ i, f i) = fun _ => a)
    (hkill : ∀ i, i ≠ j → ∃ v ∈ vs, Function.Periodic (f i) v) :
    configDiffs vs (f j) = 0 := by
  classical
  have hsum' := congrArg (configDiffs vs) hsum
  rw [configDiffs_sum, configDiffs_const hvs] at hsum'
  have hone : (∑ i, configDiffs vs (f i)) = configDiffs vs (f j) := by
    apply Finset.sum_eq_single j
    · intro i _hi hij
      obtain ⟨v, hv, hp⟩ := hkill i hij
      exact configDiffs_eq_zero_of_mem hv (f i)
        ((configDiff_eq_zero_iff v (f i)).mpr hp)
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  rw [hone] at hsum'
  exact hsum'

theorem map_configDiff (φ : A →+ B) (v : G) (f : G → A) :
    (fun x => φ (configDiff v f x)) = configDiff v (fun x => φ (f x)) := by
  ext x
  exact map_sub φ _ _

theorem map_configDiffs (φ : A →+ B) (vs : List G) (f : G → A) :
    (fun x => φ (configDiffs vs f x)) = configDiffs vs (fun x => φ (f x)) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      rw [configDiffs_cons, map_configDiff, ih, configDiffs_cons]

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

def forwardDiff {A : Type uA} [AddCommGroup A] (f : ℤ → A) (n : ℤ) : A :=
  f (n + 1) - f n

@[simp] theorem forwardDiff_apply {A : Type uA} [AddCommGroup A]
    (f : ℤ → A) (n : ℤ) : forwardDiff f n = f (n + 1) - f n := rfl

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

theorem forwardDiff_slice {B : Type uB} [AddCommGroup B]
    (f : Plane → B) (x e : Plane) :
    forwardDiff (fun n : ℤ => f (x + n • e)) =
      fun n => configDiff e f (x + n • e) := by
  ext n
  simp only [forwardDiff_apply, configDiff_apply, add_zsmul, one_zsmul, add_assoc]

theorem forwardDiff_iterate_slice {B : Type uB} [AddCommGroup B]
    (k : ℕ) (f : Plane → B) (x e : Plane) :
    (forwardDiff^[k]) (fun n : ℤ => f (x + n • e)) =
      fun n => ((configDiff e)^[k] f) (x + n • e) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply, forwardDiff_slice, ih,
        Function.iterate_succ_apply]

theorem circle_sum_of_indicator_decomposition {m : ℕ} (A : Set Plane)
    (φ : Fin m → Plane → ℝ)
    (hsum : ∀ x, tileIndicator ℝ A x + ∑ j, φ j x = 1) :
    (∑ j, (fun x => (φ j x : AddCircle (1 : ℝ)))) = fun _ => 0 := by
  classical
  ext x
  simp only [Finset.sum_apply]
  change (∑ j, (φ j x : AddCircle (1 : ℝ))) = 0
  have hcast : (∑ j, (φ j x : AddCircle (1 : ℝ))) =
      ((∑ j, φ j x : ℝ) : AddCircle (1 : ℝ)) := by
    exact (map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
      (fun j => φ j x) Finset.univ).symm
  rw [hcast, show (∑ j, φ j x) = 1 - tileIndicator ℝ A x by linarith [hsum x]]
  by_cases hx : x ∈ A <;> simp [tileIndicator, hx, AddCircle.coe_period]

theorem directional_circle_slice_polynomial {m : ℕ} (hm : 0 < m)
    (A : Set Plane) (v : Fin m → Plane) (φ : Fin m → Plane → ℝ)
    (e : Plane)
    (hspan : ∀ i j, i ≠ j → ∃ a b : ℤ, e = a • v i + b • v j)
    (hp : ∀ j, Function.Periodic (φ j) (v j))
    (hsum : ∀ x, tileIndicator ℝ A x + ∑ j, φ j x = 1)
    (j : Fin m) (x : Plane) :
    (forwardDiff^[m]) (fun n : ℤ =>
      (φ j (x + n • e) : AddCircle (1 : ℝ))) = 0 := by
  classical
  let ψ : Fin m → Plane → AddCircle (1 : ℝ) := fun i y => (φ i y : AddCircle (1 : ℝ))
  have hψ : ∀ i, Function.Periodic (ψ i) (v i) := by
    intro i y
    change (φ i (y + v i) : AddCircle (1 : ℝ)) = (φ i y : AddCircle (1 : ℝ))
    rw [hp i y]
  have hrep : ∀ i : Fin m, ∃ a b : ℤ, i = j ∨ e = a • v i + b • v j := by
    intro i
    by_cases hij : i = j
    · exact ⟨0, 0, Or.inl hij⟩
    · obtain ⟨a, b, hab⟩ := hspan i j hij
      exact ⟨a, b, Or.inr hab⟩
  choose α β hrep using hrep
  let u : Fin m → Plane := fun i => if i = j then e else α i • v i
  let vs : List Plane := Finset.univ.toList.map u
  have hlen : vs.length = m := by simp [vs]
  have hne : vs ≠ [] := by
    intro h
    have hz : m = 0 := by simpa only [h, List.length_nil] using hlen.symm
    exact (Nat.ne_of_gt hm) hz
  have hkill : ∀ i, i ≠ j → ∃ w ∈ vs, Function.Periodic (ψ i) w := by
    intro i hij
    refine ⟨u i, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨i, by simp, rfl⟩
    · simpa only [u, ite_eq_right hij] using (hψ i).zsmul (α i)
  have hz : configDiffs vs (ψ j) = 0 :=
    configDiffs_component_zero j vs hne ψ 0
      (circle_sum_of_indicator_decomposition A φ hsum) hkill
  have hreplace : ∀ w ∈ vs, ∃ k : ℤ, w = e + k • v j := by
    intro w hw
    obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hw
    by_cases hij : i = j
    · refine ⟨0, ?_⟩
      simp [u, hij]
    · refine ⟨-β i, ?_⟩
      have he := (hrep i).resolve_left hij
      simp only [u, ite_eq_right hij, he, neg_smul]
      abel
  rw [configDiffs_eq_iterate_of_period vs e (v j) (ψ j) (hψ j) hreplace,
    hlen] at hz
  change (forwardDiff^[m]) (fun n : ℤ => ψ j (x + n • e)) = 0
  rw [forwardDiff_iterate_slice, hz]
  rfl

theorem directional_slice_pair_bound {m : ℕ} (A : Set Plane)
    (v : Fin m → Plane) (φ : Fin m → Plane → ℝ) (e : Plane)
    (hspan : ∀ i j, i ≠ j → ∃ a b : ℤ, e = a • v i + b • v j)
    (hφ : ∀ j x, 0 ≤ φ j x)
    (hp : ∀ j, Function.Periodic (φ j) (v j))
    (hsum : ∀ x, tileIndicator ℝ A x + ∑ j, φ j x = 1)
    (x : Plane) (i j : Fin m) (hij : i ≠ j) (n r : ℤ) :
    φ i (x + n • e) + φ j (x + r • e) ≤ 1 := by
  classical
  obtain ⟨a, b, he⟩ := hspan i j hij
  let y : Plane := x + n • e + ((r - n) * a) • v i
  have hy : y = x + r • e + ((n - r) * b) • v j := by
    dsimp [y]
    rw [he]
    simp only [smul_add, mul_smul, sub_smul]
    abel
  have hi : φ i y = φ i (x + n • e) :=
    (hp i).zsmul ((r - n) * a) _
  have hj : φ j y = φ j (x + r • e) := by
    rw [hy]
    exact (hp j).zsmul ((n - r) * b) _
  have hle : φ i y + φ j y ≤ ∑ k, φ k y := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({i, j} : Finset (Fin m)))
      (fun k _hk _hnot => hφ k y)
    simpa [hij] using h
  have htotal := hsum y
  have ha := tileIndicator_nonneg A y
  rw [hi, hj] at hle
  linarith

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace PeriodicTilingThree

open scoped BigOperators

section AddCommGroup

variable {A : Type uA} [AddCommGroup A]

theorem intSequence_eq_of_forwardDiff_eq {f g : ℤ → A}
    (hd : forwardDiff f = forwardDiff g) (hzero : f 0 = g 0) : f = g := by
  have hsucc (n : ℤ) (hn : f n = g n) : f (n + 1) = g (n + 1) := by
    have h := congrFun hd n
    change f (n + 1) - f n = g (n + 1) - g n at h
    rw [hn] at h
    exact sub_left_inj.mp h
  have hpred (n : ℤ) (hn : f n = g n) : f (n - 1) = g (n - 1) := by
    have h := congrFun hd (n - 1)
    change f (n - 1 + 1) - f (n - 1) = g (n - 1 + 1) - g (n - 1) at h
    rw [sub_add_cancel, hn] at h
    exact sub_right_inj.mp h
  funext n
  refine Int.induction_on n hzero ?_ ?_
  · intro m hm
    exact hsucc (m : ℤ) hm
  · intro m hm
    exact hpred (-(m : ℤ)) hm

def newtonSequence {k : ℕ} (c : Fin k → A) (n : ℤ) : A :=
  ∑ i : Fin k, Ring.choose n i.val • c i

theorem newtonSequence_cons {k : ℕ} (a : A) (c : Fin k → A) (n : ℤ) :
    newtonSequence (Fin.cons a c) n =
      a + ∑ i : Fin k, Ring.choose n (i.val + 1) • c i := by
  rw [newtonSequence, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Ring.choose_zero_right, one_zsmul,
    Fin.cons_zero, Fin.val_succ, Fin.cons_succ]

@[simp] theorem newtonSequence_cons_zero {k : ℕ} (a : A) (c : Fin k → A) :
    newtonSequence (Fin.cons a c) 0 = a := by
  simp [newtonSequence_cons]

theorem forwardDiff_newtonSequence_cons {k : ℕ} (a : A) (c : Fin k → A) :
    forwardDiff (newtonSequence (Fin.cons a c)) = newtonSequence c := by
  funext n
  simp only [forwardDiff_apply, newtonSequence_cons]
  unfold newtonSequence
  calc
    (a + ∑ i : Fin k, Ring.choose (n + 1) (i.val + 1) • c i) -
        (a + ∑ i : Fin k, Ring.choose n (i.val + 1) • c i) =
        ∑ i : Fin k,
          (Ring.choose (n + 1) (i.val + 1) • c i -
            Ring.choose n (i.val + 1) • c i) := by
      rw [Finset.sum_sub_distrib]
      abel
    _ = ∑ i : Fin k, Ring.choose n i.val • c i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Ring.choose_succ_succ, add_zsmul, add_sub_cancel_right]

theorem exists_newtonSequence_of_iter_forwardDiff_eq_zero
    (k : ℕ) (f : ℤ → A) (hk : (forwardDiff^[k]) f = 0) :
    ∃ c : Fin k → A, f = newtonSequence c := by
  induction k generalizing f with
  | zero =>
      have hf : f = 0 := by simpa using hk
      refine ⟨Fin.elim0, ?_⟩
      subst f
      funext n
      simp [newtonSequence]
  | succ k ih =>
      have hdiff : (forwardDiff^[k]) (forwardDiff f) = 0 := by
        simpa only [Function.iterate_succ_apply] using hk
      obtain ⟨c, hc⟩ := ih (forwardDiff f) hdiff
      refine ⟨Fin.cons (f 0) c, intSequence_eq_of_forwardDiff_eq ?_ ?_⟩
      · rw [forwardDiff_newtonSequence_cons]
        exact hc
      · simp

end AddCommGroup

def newtonBasisPolynomial (k : ℕ) : Polynomial ℝ :=
  Polynomial.C ((k.factorial : ℝ)⁻¹) * descPochhammer ℝ k

theorem descPochhammer_eval_int_eq_factorial_mul_choose (k : ℕ) (n : ℤ) :
    (descPochhammer ℝ k).eval (n : ℝ) =
      (k.factorial : ℝ) * ((Ring.choose n k : ℤ) : ℝ) := by
  have h : (descPochhammer ℤ k).eval n = (k.factorial : ℤ) * Ring.choose n k := by
    simpa only [Polynomial.eval_eq_smeval, nsmul_eq_mul] using
      (Ring.descPochhammer_eq_factorial_smul_choose n k)
  rw [← descPochhammer_eval_cast ℝ k n, h, Int.cast_mul, Int.cast_natCast]

@[simp] theorem newtonBasisPolynomial_eval_int (k : ℕ) (n : ℤ) :
    (newtonBasisPolynomial k).eval (n : ℝ) = ((Ring.choose n k : ℤ) : ℝ) := by
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [newtonBasisPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    descPochhammer_eval_int_eq_factorial_mul_choose, ← mul_assoc, inv_mul_cancel₀ hk, one_mul]

def newtonPolynomial {k : ℕ} (c : Fin k → ℝ) : Polynomial ℝ :=
  ∑ i : Fin k, Polynomial.C (c i) * newtonBasisPolynomial i.val

theorem newtonPolynomial_eval_int {k : ℕ} (c : Fin k → ℝ) (n : ℤ) :
    (newtonPolynomial c).eval (n : ℝ) =
      ∑ i : Fin k, Ring.choose n i.val • c i := by
  rw [newtonPolynomial, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Polynomial.eval_mul, Polynomial.eval_C,
    newtonBasisPolynomial_eval_int, zsmul_eq_mul]
  exact mul_comm (c i) ((Ring.choose n i.val : ℤ) : ℝ)

theorem exists_polynomial_lift_of_iter_forwardDiff_eq_zero
    (f : ℤ → AddCircle (1 : ℝ)) (k : ℕ) (hk : (forwardDiff^[k]) f = 0) :
    ∃ P : Polynomial ℝ, ∀ n : ℤ, ((P.eval (n : ℝ) : ℝ) : AddCircle (1 : ℝ)) = f n := by
  obtain ⟨c, hc⟩ := exists_newtonSequence_of_iter_forwardDiff_eq_zero k f hk
  have hrepr : ∀ i : Fin k, ∃ x : ℝ, (x : AddCircle (1 : ℝ)) = c i := by
    intro i
    exact QuotientAddGroup.mk_surjective (c i)
  choose a ha using hrepr
  refine ⟨newtonPolynomial a, ?_⟩
  intro n
  change QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))
    ((newtonPolynomial a).eval (n : ℝ)) = f n
  rw [newtonPolynomial_eval_int, map_sum, hc]
  simp only [newtonSequence, map_zsmul, QuotientAddGroup.mk'_apply, ha]

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace PeriodicTilingThree

open Finset Filter
open scoped Topology

def complexAverage (u : ℕ → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ range N, u n

def vectorAverage {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℕ → E) (N : ℕ) : E :=
  (N : ℝ)⁻¹ • ∑ n ∈ range N, u n

theorem complexAverage_eq_vectorAverage (u : ℕ → ℂ) (N : ℕ) :
    complexAverage u N = vectorAverage u N := by
  simp only [complexAverage, vectorAverage, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_natCast]

@[simp] theorem complexAverage_zero (u : ℕ → ℂ) : complexAverage u 0 = 0 := by
  simp [complexAverage]

theorem complexAverage_add (u v : ℕ → ℂ) (N : ℕ) :
    complexAverage (fun n => u n + v n) N = complexAverage u N + complexAverage v N := by
  simp only [complexAverage, Finset.sum_add_distrib, mul_add]

theorem complexAverage_sub (u v : ℕ → ℂ) (N : ℕ) :
    complexAverage (fun n => u n - v n) N = complexAverage u N - complexAverage v N := by
  simp only [complexAverage, Finset.sum_sub_distrib, mul_sub]

theorem complexAverage_const (c : ℂ) {N : ℕ} (hN : N ≠ 0) :
    complexAverage (fun _ => c) N = c := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  simp only [complexAverage, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hNc, one_mul]

theorem complexAverage_mul_const (u : ℕ → ℂ) (c : ℂ) (N : ℕ) :
    complexAverage (fun n => u n * c) N = complexAverage u N * c := by
  simp only [complexAverage, ← Finset.sum_mul, mul_assoc]

theorem complexAverage_const_mul (u : ℕ → ℂ) (c : ℂ) (N : ℕ) :
    complexAverage (fun n => c * u n) N = c * complexAverage u N := by
  simp only [complexAverage, ← Finset.mul_sum]
  ring

theorem norm_complexAverage (u : ℕ → ℂ) (N : ℕ) :
    ‖complexAverage u N‖ = (N : ℝ)⁻¹ * ‖∑ n ∈ range N, u n‖ := by
  simp only [complexAverage, norm_mul, norm_inv, Complex.norm_natCast]

theorem norm_complexAverage_le (u : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ n, ‖u n‖ ≤ C) (N : ℕ) : ‖complexAverage u N‖ ≤ C := by
  by_cases hN : N = 0
  · simpa [hN] using hC
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hs : ‖∑ n ∈ range N, u n‖ ≤ (N : ℝ) * C := by
    calc
      _ ≤ ∑ n ∈ range N, ‖u n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ range N, C := Finset.sum_le_sum fun n _ => hu n
      _ = (N : ℝ) * C := by simp
  rw [norm_complexAverage]
  calc
    _ ≤ (N : ℝ)⁻¹ * ((N : ℝ) * C) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = C := by rw [← mul_assoc, inv_mul_cancel₀ hNr, one_mul]

theorem norm_geometric_sum_le (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (N : ℕ) :
    ‖∑ n ∈ range N, z ^ n‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hz1, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hz]

theorem complexAverage_geometric_tendsto (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    Tendsto (complexAverage (fun n => z ^ n)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hb : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * (2 / ‖z - 1‖)) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      tendsto_inv_atTop_nhds_zero_nat.mul_const (2 / ‖z - 1‖)
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hb
  rw [norm_complexAverage]
  exact mul_le_mul_of_nonneg_left (norm_geometric_sum_le z hz hz1 N) (by positivity)

theorem complexAverage_const_mul_geometric_tendsto (c z : ℂ)
    (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    Tendsto (complexAverage (fun n => c * z ^ n)) atTop (𝓝 0) := by
  have hfun : complexAverage (fun n => c * z ^ n) =
      fun N => c * complexAverage (fun n => z ^ n) N := by
    funext N
    exact complexAverage_const_mul (fun n => z ^ n) c N
  rw [hfun]
  simpa only [mul_zero] using
    (complexAverage_geometric_tendsto z hz hz1).const_mul c

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

open Filter MeasureTheory Set
open scoped Topology

private instance unitPeriodPositive : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

abbrev UnitAddCircle := AddCircle (1 : ℝ)

def CircleFourierCancellation (u : ℕ → UnitAddCircle) : Prop :=
  ∀ k : ℤ, k ≠ 0 →
    Tendsto (complexAverage (fun n => fourier k (u n))) atTop (𝓝 0)

private theorem circle_continuous_integrable (f : C(UnitAddCircle, ℂ)) :
    Integrable f AddCircle.haarAddCircle :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

private theorem circle_integral_fourier (k : ℤ) :
    (∫ x : UnitAddCircle, fourier k x ∂AddCircle.haarAddCircle) =
      if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst k
    simp only [fourier_zero, integral_const, probReal_univ, one_smul]
  · exact integral_eq_zero_of_add_right_eq_neg
      (μ := AddCircle.haarAddCircle)
      (fourier_add_half_inv_index hk (show (0 : ℝ) < 1 from zero_lt_one))

private theorem circle_integral_norm_le (f : C(UnitAddCircle, ℂ)) :
    ‖∫ x, f x ∂AddCircle.haarAddCircle‖ ≤ ‖f‖ := by
  simpa only [probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const
      (μ := AddCircle.haarAddCircle)
      (Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x))

private theorem circle_average_norm_le (u : ℕ → UnitAddCircle)
    (f : C(UnitAddCircle, ℂ)) (N : ℕ) :
    ‖complexAverage (fun n => f (u n)) N‖ ≤ ‖f‖ :=
  norm_complexAverage_le _ _ (norm_nonneg f) (fun n => f.norm_coe_le_norm (u n)) N

private def circleAveragingSubmodule (u : ℕ → UnitAddCircle) :
    Submodule ℂ C(UnitAddCircle, ℂ) where
  carrier := {f | Tendsto (complexAverage (fun n => f (u n))) atTop
    (𝓝 (∫ x, f x ∂AddCircle.haarAddCircle))}
  zero_mem' := by
    change Tendsto (complexAverage (fun _ => (0 : ℂ))) atTop
      (𝓝 (∫ _ : UnitAddCircle, (0 : ℂ) ∂AddCircle.haarAddCircle))
    have hz : complexAverage (fun _ => (0 : ℂ)) = fun _ => 0 := by
      funext N
      simp [complexAverage]
    rw [hz, integral_zero]
    exact tendsto_const_nhds
  add_mem' := by
    intro f g hf hg
    change Tendsto (complexAverage (fun n => f (u n) + g (u n))) atTop
      (𝓝 (∫ x, f x + g x ∂AddCircle.haarAddCircle))
    have ha : complexAverage (fun n => f (u n) + g (u n)) =
        fun N => complexAverage (fun n => f (u n)) N +
          complexAverage (fun n => g (u n)) N := by
      funext N
      exact complexAverage_add _ _ N
    rw [ha, integral_add (circle_continuous_integrable f) (circle_continuous_integrable g)]
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change Tendsto (complexAverage (fun n => c * f (u n))) atTop
      (𝓝 (∫ x, c * f x ∂AddCircle.haarAddCircle))
    have ha : complexAverage (fun n => c * f (u n)) =
        fun N => c * complexAverage (fun n => f (u n)) N := by
      funext N
      exact complexAverage_const_mul _ _ N
    rw [ha, integral_const_mul]
    exact hf.const_mul c

private theorem fourier_mem_circleAveragingSubmodule (u : ℕ → UnitAddCircle)
    (hu : CircleFourierCancellation u) (k : ℤ) :
    fourier k ∈ circleAveragingSubmodule u := by
  change Tendsto _ atTop (𝓝 _)
  rw [circle_integral_fourier]
  by_cases hk : k = 0
  · subst k
    simp only [ite_true, fourier_zero]
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
    exact (complexAverage_const 1 (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hN))).symm
  · simpa only [ite_eq_right hk] using hu k hk

theorem circle_averages_tendsto_integral (u : ℕ → UnitAddCircle)
    (hu : CircleFourierCancellation u) (f : C(UnitAddCircle, ℂ)) :
    Tendsto (complexAverage (fun n => f (u n))) atTop
      (𝓝 (∫ x, f x ∂AddCircle.haarAddCircle)) := by
  have hspan : Submodule.span ℂ (Set.range (@fourier (1 : ℝ))) ≤
      circleAveragingSubmodule u := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact fourier_mem_circleAveragingSubmodule u hu k
  have hdense : Dense (Submodule.span ℂ (Set.range (@fourier (1 : ℝ))) :
      Set C(UnitAddCircle, ℂ)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr span_fourier_closure_eq_top
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨p, hp, hfp⟩ := hdense.exists_dist_lt f (show 0 < ε / 4 by positivity)
  have hpconv := hspan hp
  change Tendsto (complexAverage (fun n => p (u n))) atTop
    (𝓝 (∫ x, p x ∂AddCircle.haarAddCircle)) at hpconv
  filter_upwards [Metric.tendsto_nhds.mp hpconv (ε / 2) (by positivity)] with N hN
  have havg : ‖complexAverage (fun n => f (u n)) N -
      complexAverage (fun n => p (u n)) N‖ ≤ ‖f - p‖ := by
    rw [← complexAverage_sub]
    exact circle_average_norm_le u (f - p) N
  have hint : ‖(∫ x, p x ∂AddCircle.haarAddCircle) -
      (∫ x, f x ∂AddCircle.haarAddCircle)‖ ≤ ‖f - p‖ := by
    rw [← integral_sub (circle_continuous_integrable p) (circle_continuous_integrable f)]
    simpa only [ContinuousMap.sub_apply, norm_sub_rev] using circle_integral_norm_le (p - f)
  have hbound := norm_add_le
    (complexAverage (fun n => f (u n)) N - complexAverage (fun n => p (u n)) N)
    (complexAverage (fun n => p (u n)) N - (∫ x, f x ∂AddCircle.haarAddCircle))
  have hbound' := norm_add_le
    (complexAverage (fun n => p (u n)) N - (∫ x, p x ∂AddCircle.haarAddCircle))
    ((∫ x, p x ∂AddCircle.haarAddCircle) - (∫ x, f x ∂AddCircle.haarAddCircle))
  simp only [sub_add_sub_cancel] at hbound hbound'
  rw [dist_eq_norm] at hfp hN ⊢
  linarith

theorem denseRange_of_circleFourierCancellation (u : ℕ → UnitAddCircle)
    (hu : CircleFourierCancellation u) : DenseRange u := by
  rw [Metric.denseRange_iff]
  intro x r hr
  by_contra h
  have haway : ∀ n, r ≤ dist x (u n) :=
    fun n => le_of_not_gt (fun hn => h ⟨n, hn⟩)
  let b : C(UnitAddCircle, ℝ) :=
    ⟨fun y => max (r - dist x y) 0,
      (continuous_const.sub (continuous_const.dist continuous_id)).max continuous_const⟩
  have hb0 : ∀ n, b (u n) = 0 := by
    intro n
    exact max_eq_right (sub_nonpos.mpr (haway n))
  have hbx : b x ≠ 0 := by simpa [b, dist_self, max_eq_left hr.le] using hr.ne'
  have hbnonneg : (0 : UnitAddCircle → ℝ) ≤ b := fun y => le_max_right _ _
  have hbint : 0 < ∫ y, b y ∂AddCircle.haarAddCircle :=
    b.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace b) hbnonneg hbx
  let bc : C(UnitAddCircle, ℂ) := ⟨fun y => (b y : ℂ), Complex.continuous_ofReal.comp b.continuous⟩
  have hlim := circle_averages_tendsto_integral u hu bc
  have havgzero : complexAverage (fun n => bc (u n)) = fun _ => 0 := by
    funext N
    simp [complexAverage, bc, hb0]
  rw [havgzero] at hlim
  have hi : (∫ y, bc y ∂AddCircle.haarAddCircle) = 0 :=
    tendsto_nhds_unique hlim tendsto_const_nhds
  have hir : (∫ y, b y ∂AddCircle.haarAddCircle) = 0 := by
    apply Complex.ofReal_injective
    change (∫ y, (b y : ℂ) ∂AddCircle.haarAddCircle) = 0 at hi
    rw [integral_complex_ofReal] at hi
    simpa only [Complex.ofReal_zero] using hi
  linarith

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

noncomputable section


namespace PeriodicTilingThree

open Finset Filter
open scoped Topology InnerProductSpace ComplexConjugate

section Normed

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_vectorAverage (u : ℕ → E) (N : ℕ) :
    ‖vectorAverage u N‖ = (N : ℝ)⁻¹ * ‖∑ n ∈ range N, u n‖ := by
  rw [vectorAverage, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]

theorem sum_shift_sub_sum {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℕ → E) (N h : ℕ) :
    (∑ n ∈ range N, u (n + h)) - (∑ n ∈ range N, u n) =
      (∑ n ∈ range h, u (n + N)) - (∑ n ∈ range h, u n) := by
  have h₁ : (∑ n ∈ range (N + h), u n) =
      (∑ n ∈ range N, u n) + (∑ n ∈ range h, u (n + N)) := by
    simpa only [Nat.add_comm] using sum_range_add u N h
  have h₂ : (∑ n ∈ range (N + h), u n) =
      (∑ n ∈ range h, u n) + (∑ n ∈ range N, u (n + h)) := by
    simpa only [Nat.add_comm] using sum_range_add u h N
  apply sub_eq_sub_iff_add_eq_add.mpr
  simpa only [add_comm] using h₂.symm.trans h₁

theorem norm_sum_range_le_length
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℕ → E) (hu : ∀ n, ‖u n‖ ≤ 1) (N : ℕ) :
    ‖∑ n ∈ range N, u n‖ ≤ (N : ℝ) := by
  calc
    _ ≤ ∑ n ∈ range N, ‖u n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ range N, (1 : ℝ) := sum_le_sum fun n _ => hu n
    _ = (N : ℝ) := by simp

theorem norm_shift_sum_sub_le (u : ℕ → E) (hu : ∀ n, ‖u n‖ ≤ 1) (N h : ℕ) :
    ‖(∑ n ∈ range N, u (n + h)) - (∑ n ∈ range N, u n)‖ ≤ 2 * (h : ℝ) := by
  rw [sum_shift_sub_sum]
  calc
    _ ≤ ‖∑ n ∈ range h, u (n + N)‖ + ‖∑ n ∈ range h, u n‖ := norm_sub_le _ _
    _ ≤ (h : ℝ) + h := add_le_add
      (norm_sum_range_le_length (fun n => u (n + N)) (fun n => hu (n + N)) h)
      (norm_sum_range_le_length u hu h)
    _ = 2 * (h : ℝ) := by ring

theorem norm_shift_average_sub_le (u : ℕ → E) (hu : ∀ n, ‖u n‖ ≤ 1) (N h : ℕ) :
    ‖vectorAverage (fun n => u (n + h)) N - vectorAverage u N‖ ≤
      (N : ℝ)⁻¹ * (2 * (h : ℝ)) := by
  simp only [vectorAverage, ← smul_sub]
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  exact mul_le_mul_of_nonneg_left (norm_shift_sum_sub_le u hu N h) (by positivity)

def smoothedAverage (u : ℕ → E) (H N : ℕ) : E :=
  (H : ℝ)⁻¹ • vectorAverage (fun n => ∑ h ∈ range H, u (n + h)) N

theorem smoothedAverage_eq_sum (u : ℕ → E) (H N : ℕ) :
    smoothedAverage u H N =
      (H : ℝ)⁻¹ • ∑ h ∈ range H, vectorAverage (fun n => u (n + h)) N := by
  simp only [smoothedAverage, vectorAverage, smul_sum]
  rw [sum_comm]

theorem smoothedAverage_sub (u : ℕ → E) {H : ℕ} (hH : 0 < H) (N : ℕ) :
    smoothedAverage u H N - vectorAverage u N =
      (H : ℝ)⁻¹ • ∑ h ∈ range H,
        (vectorAverage (fun n => u (n + h)) N - vectorAverage u N) := by
  have hHr : (H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hH.ne'
  rw [sum_sub_distrib, smul_sub, ← smoothedAverage_eq_sum]
  congr 1
  simp only [sum_const, card_range, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, inv_mul_cancel₀ hHr, one_smul]

theorem norm_smoothedAverage_sub_le (u : ℕ → E) (hu : ∀ n, ‖u n‖ ≤ 1)
    {H : ℕ} (hH : 0 < H) (N : ℕ) :
    ‖smoothedAverage u H N - vectorAverage u N‖ ≤
      (N : ℝ)⁻¹ * (2 * (H : ℝ)) := by
  have hHr : (H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hH.ne'
  rw [smoothedAverage_sub u hH N, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg H))]
  have hsum :
      ‖∑ h ∈ range H, (vectorAverage (fun n => u (n + h)) N - vectorAverage u N)‖ ≤
        (H : ℝ) * ((N : ℝ)⁻¹ * (2 * (H : ℝ))) := by
    calc
      _ ≤ ∑ h ∈ range H,
          ‖vectorAverage (fun n => u (n + h)) N - vectorAverage u N‖ := norm_sum_le _ _
      _ ≤ ∑ _h ∈ range H, ((N : ℝ)⁻¹ * (2 * (H : ℝ))) := by
        apply sum_le_sum
        intro h hh
        refine (norm_shift_average_sub_le u hu N h).trans ?_
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hh' : (h : ℝ) ≤ H := by exact_mod_cast (mem_range.mp hh).le
        linarith
      _ = (H : ℝ) * ((N : ℝ)⁻¹ * (2 * (H : ℝ))) := by simp
  calc
    _ ≤ (H : ℝ)⁻¹ * ((H : ℝ) * ((N : ℝ)⁻¹ * (2 * (H : ℝ)))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (N : ℝ)⁻¹ * (2 * (H : ℝ)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hHr, one_mul]

theorem norm_vectorAverage_sq_le (u : ℕ → E) (N : ℕ) :
    ‖vectorAverage u N‖ ^ 2 ≤ (N : ℝ)⁻¹ * ∑ n ∈ range N, ‖u n‖ ^ 2 := by
  by_cases hN : N = 0
  · simp [hN, vectorAverage]
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hsum : ‖∑ n ∈ range N, u n‖ ^ 2 ≤ (∑ n ∈ range N, ‖u n‖) ^ 2 := by
    have hn : 0 ≤ ∑ n ∈ range N, ‖u n‖ := sum_nonneg fun _ _ => norm_nonneg _
    exact (sq_le_sq₀ (norm_nonneg _) hn).mpr (norm_sum_le (range N) u)
  have hc : (∑ n ∈ range N, ‖u n‖) ^ 2 ≤
      (N : ℝ) * ∑ n ∈ range N, ‖u n‖ ^ 2 := by
    simpa only [card_range] using
      (sq_sum_le_card_mul_sum_sq (s := range N) (f := fun n => ‖u n‖))
  rw [norm_vectorAverage, mul_pow]
  calc
    _ ≤ ((N : ℝ)⁻¹) ^ 2 * ((N : ℝ) * ∑ n ∈ range N, ‖u n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hsum.trans hc) (sq_nonneg _)
    _ = (N : ℝ)⁻¹ * ∑ n ∈ range N, ‖u n‖ ^ 2 := by
      field_simp [hNr]

end Normed

section InnerProduct

variable {E : Type uInner} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def offDiagonalAverage (u : ℕ → E) (H N : ℕ) : ℝ :=
  ∑ h ∈ range H, ∑ k ∈ range H,
    if h = k then 0 else vectorAverage (fun n => ⟪u (n + h), u (n + k)⟫_ℝ) N

theorem block_energy_eq (u : ℕ → E) (H N : ℕ) :
    (N : ℝ)⁻¹ * ∑ n ∈ range N, ‖∑ h ∈ range H, u (n + h)‖ ^ 2 =
      ∑ h ∈ range H, ∑ k ∈ range H,
        vectorAverage (fun n => ⟪u (n + h), u (n + k)⟫_ℝ) N := by
  simp only [← real_inner_self_eq_norm_sq, sum_inner, inner_sum,
    vectorAverage, smul_eq_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro h _hh
  rw [sum_comm]
  apply sum_congr rfl
  intro k _hk
  apply sum_congr rfl
  intro n _hn
  rw [real_inner_comm]

theorem diagonal_average_le_one (u : ℕ → E) (hu : ∀ n, ‖u n‖ ≤ 1) (h N : ℕ) :
    vectorAverage (fun n => ⟪u (n + h), u (n + h)⟫_ℝ) N ≤ 1 := by
  by_cases hN : N = 0
  · simp [hN, vectorAverage]
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hb : ∀ n, ⟪u (n + h), u (n + h)⟫_ℝ ≤ 1 := by
    intro n
    rw [real_inner_self_eq_norm_sq]
    simpa only [one_pow] using
      (sq_le_sq₀ (norm_nonneg (u (n + h))) zero_le_one).mpr (hu (n + h))
  simp only [vectorAverage, smul_eq_mul]
  calc
    _ ≤ (N : ℝ)⁻¹ * (∑ _n ∈ range N, (1 : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun n _ => hb n) (by positivity)
    _ = 1 := by simp [inv_mul_cancel₀ hNr]

theorem block_energy_le (u : ℕ → E) (hu : ∀ n, ‖u n‖ ≤ 1) (H N : ℕ) :
    (N : ℝ)⁻¹ * ∑ n ∈ range N, ‖∑ h ∈ range H, u (n + h)‖ ^ 2 ≤
      (H : ℝ) + offDiagonalAverage u H N := by
  rw [block_energy_eq]
  calc
    _ ≤ ∑ h ∈ range H, (1 + ∑ k ∈ range H,
        if h = k then 0 else vectorAverage (fun n => ⟪u (n + h), u (n + k)⟫_ℝ) N) := by
      apply sum_le_sum
      intro h hh
      calc
        _ ≤ ∑ k ∈ range H,
            ((if h = k then (1 : ℝ) else 0) +
              (if h = k then 0 else vectorAverage (fun n => ⟪u (n + h), u (n + k)⟫_ℝ) N)) := by
          apply sum_le_sum
          intro k _hk
          by_cases he : h = k
          · subst k
            simpa using diagonal_average_le_one u hu h N
          · simp [he]
        _ = _ := by simp [sum_add_distrib, hh]
    _ = (H : ℝ) + offDiagonalAverage u H N := by
      simp [sum_add_distrib, offDiagonalAverage]

theorem norm_smoothedAverage_sq_le (u : ℕ → E) (hu : ∀ n, ‖u n‖ ≤ 1)
    {H : ℕ} (hH : 0 < H) (N : ℕ) :
    ‖smoothedAverage u H N‖ ^ 2 ≤
      (H : ℝ)⁻¹ + ((H : ℝ)⁻¹) ^ 2 * offDiagonalAverage u H N := by
  have hHr : (H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hH.ne'
  have hb := (norm_vectorAverage_sq_le (fun n => ∑ h ∈ range H, u (n + h)) N).trans
    (block_energy_le u hu H N)
  rw [smoothedAverage, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg H)), mul_pow]
  calc
    _ ≤ ((H : ℝ)⁻¹) ^ 2 * ((H : ℝ) + offDiagonalAverage u H N) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = (H : ℝ)⁻¹ + ((H : ℝ)⁻¹) ^ 2 * offDiagonalAverage u H N := by
      field_simp [hHr]

theorem finite_vanDerCorput (u : ℕ → E) (hu : ∀ n, ‖u n‖ ≤ 1)
    {H : ℕ} (hH : 0 < H) (N : ℕ) :
    ‖vectorAverage u N‖ ^ 2 ≤
      2 * ((H : ℝ)⁻¹ + ((H : ℝ)⁻¹) ^ 2 * offDiagonalAverage u H N) +
        2 * ((N : ℝ)⁻¹ * (2 * (H : ℝ))) ^ 2 := by
  have hs := norm_smoothedAverage_sq_le u hu hH N
  have he := norm_smoothedAverage_sub_le u hu hH N
  have ht : ‖vectorAverage u N‖ ≤
      ‖smoothedAverage u H N‖ + ‖smoothedAverage u H N - vectorAverage u N‖ := by
    have ht' := norm_sub_le (smoothedAverage u H N)
      (smoothedAverage u H N - vectorAverage u N)
    simpa only [sub_sub_cancel] using ht'
  have he0 : 0 ≤ (N : ℝ)⁻¹ * (2 * (H : ℝ)) := by positivity
  have hn := norm_nonneg (smoothedAverage u H N)
  have hn' := norm_nonneg (smoothedAverage u H N - vectorAverage u N)
  have hn'' := norm_nonneg (vectorAverage u N)
  have hsq : ‖vectorAverage u N‖ ^ 2 ≤
      2 * ‖smoothedAverage u H N‖ ^ 2 +
        2 * ‖smoothedAverage u H N - vectorAverage u N‖ ^ 2 := by
    have ht₂ := (sq_le_sq₀ hn'' (add_nonneg hn hn')).mpr ht
    nlinarith [sq_nonneg (‖smoothedAverage u H N‖ -
      ‖smoothedAverage u H N - vectorAverage u N‖)]
  have he' : ‖smoothedAverage u H N - vectorAverage u N‖ ^ 2 ≤
      ((N : ℝ)⁻¹ * (2 * (H : ℝ))) ^ 2 := (sq_le_sq₀ hn' he0).mpr he
  linarith

theorem offDiagonalAverage_tendsto_zero (u : ℕ → E)
    (hcor : ∀ h k : ℕ, h ≠ k →
      Tendsto (vectorAverage (fun n => ⟪u (n + h), u (n + k)⟫_ℝ)) atTop (𝓝 0))
    (H : ℕ) : Tendsto (offDiagonalAverage u H) atTop (𝓝 0) := by
  have hk (h k : ℕ) : Tendsto
      (fun N => if h = k then (0 : ℝ) else
        vectorAverage (fun n => ⟪u (n + h), u (n + k)⟫_ℝ) N) atTop (𝓝 0) := by
    by_cases he : h = k
    · simp only [he, ite_true]
      exact tendsto_const_nhds
    · simpa only [he, ite_false] using hcor h k he
  have hh (h : ℕ) : Tendsto
      (fun N => ∑ k ∈ range H, if h = k then (0 : ℝ) else
        vectorAverage (fun n => ⟪u (n + h), u (n + k)⟫_ℝ) N) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (range H) (fun k _ => hk h k)
  unfold offDiagonalAverage
  simpa only [sum_const_zero] using
    tendsto_finsetSum (range H) (fun h _ => hh h)

theorem vectorAverage_tendsto_zero_of_shift_inner (u : ℕ → E)
    (hu : ∀ n, ‖u n‖ ≤ 1)
    (hcor : ∀ h k : ℕ, h ≠ k →
      Tendsto (vectorAverage (fun n => ⟪u (n + h), u (n + k)⟫_ℝ)) atTop (𝓝 0)) :
    Tendsto (vectorAverage u) atTop (𝓝 0) := by
  have hsq : Tendsto (fun N => ‖vectorAverage u N‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact Filter.Eventually.of_forall fun N => lt_of_lt_of_le ha (sq_nonneg _)
    · intro b hb
      obtain ⟨H, hH⟩ := exists_nat_gt (2 / b)
      have hHr : (0 : ℝ) < H := lt_trans (by positivity : (0 : ℝ) < 2 / b) hH
      have hHn : 0 < H := Nat.cast_pos.mp hHr
      have hlimit : 2 * (H : ℝ)⁻¹ < b := by
        have hx : 2 < (H : ℝ) * b := (div_lt_iff₀ hb).mp hH
        have hy : 2 / (H : ℝ) < b := (div_lt_iff₀ hHr).mpr (by nlinarith)
        simpa only [div_eq_mul_inv] using hy
      have hoff := offDiagonalAverage_tendsto_zero u hcor H
      have hfirst : Tendsto
          (fun N => (H : ℝ)⁻¹ + ((H : ℝ)⁻¹) ^ 2 * offDiagonalAverage u H N)
          atTop (𝓝 ((H : ℝ)⁻¹)) := by
        simpa only [mul_zero, add_zero] using
          tendsto_const_nhds.add (hoff.const_mul (((H : ℝ)⁻¹) ^ 2))
      have hsecond : Tendsto (fun N : ℕ => ((N : ℝ)⁻¹ * (2 * (H : ℝ))) ^ 2)
          atTop (𝓝 (0 : ℝ)) := by
        simpa only [zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
          (tendsto_inv_atTop_nhds_zero_nat.mul_const (2 * (H : ℝ))).pow 2
      have hg : Tendsto
          (fun N => 2 * ((H : ℝ)⁻¹ + ((H : ℝ)⁻¹) ^ 2 * offDiagonalAverage u H N) +
            2 * ((N : ℝ)⁻¹ * (2 * (H : ℝ))) ^ 2)
          atTop (𝓝 (2 * (H : ℝ)⁻¹)) := by
        simpa only [mul_zero, add_zero] using (hfirst.const_mul 2).add (hsecond.const_mul 2)
      filter_upwards [(tendsto_order.mp hg).2 b hlimit] with N hN
      exact lt_of_le_of_lt (finite_vanDerCorput u hu hHn N) hN
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsq.sqrt

end InnerProduct

theorem vectorAverage_complex_inner_eq_re (u : ℕ → ℂ) (h k N : ℕ) :
    vectorAverage (fun n => ⟪u (n + h), u (n + k)⟫_ℝ) N =
      (complexAverage (fun n => u (n + k) * conj (u (n + h))) N).re := by
  rw [complexAverage_eq_vectorAverage]
  simp only [vectorAverage, Complex.inner, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum, smul_eq_mul]

theorem complexAverage_vanDerCorput (u : ℕ → ℂ)
    (hu : ∀ n, ‖u n‖ ≤ 1)
    (hcor : ∀ h k : ℕ, h ≠ k →
      Tendsto (complexAverage (fun n => u (n + h) * conj (u (n + k)))) atTop (𝓝 0)) :
    Tendsto (complexAverage u) atTop (𝓝 0) := by
  have hi : ∀ h k : ℕ, h ≠ k →
      Tendsto (vectorAverage (fun n => ⟪u (n + h), u (n + k)⟫_ℝ)) atTop (𝓝 0) := by
    intro h k hne
    have hr := (Complex.continuous_re.tendsto 0).comp (hcor k h hne.symm)
    simp only [Complex.zero_re] at hr
    convert hr using 1
    · funext N
      exact vectorAverage_complex_inner_eq_re u h k N
  convert vectorAverage_tendsto_zero_of_shift_inner u hu hi using 1
  funext N
  exact complexAverage_eq_vectorAverage u N

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree

open Polynomial

theorem polynomial_taylor_coeff_top (P : Polynomial ℝ) (r : ℝ) :
    (taylor r P).coeff P.natDegree = P.leadingCoeff := by
  have hd : (hasseDeriv P.natDegree P).natDegree < 1 := by
    have h := natDegree_hasseDeriv_le P P.natDegree
    omega
  rw [taylor_coeff, eval_eq_sum_range' hd]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, mul_one, hasseDeriv_coeff, Nat.choose_self,
    Nat.cast_one, one_mul, Polynomial.leadingCoeff]

theorem polynomial_taylor_coeff_pred (P : Polynomial ℝ)
    (hP : 0 < P.natDegree) (r : ℝ) :
    (taylor r P).coeff (P.natDegree - 1) =
      P.coeff (P.natDegree - 1) +
        (P.natDegree : ℝ) * P.leadingCoeff * r := by
  have hd : (hasseDeriv (P.natDegree - 1) P).natDegree < 2 := by
    have h := natDegree_hasseDeriv_le P (P.natDegree - 1)
    omega
  have hs : 1 + (P.natDegree - 1) = P.natDegree := by omega
  have hc : P.natDegree.choose (P.natDegree - 1) = P.natDegree := by
    have hs' : P.natDegree - 1 + 1 = P.natDegree := by omega
    simpa only [hs'] using Nat.choose_succ_self_right (P.natDegree - 1)
  rw [taylor_coeff, eval_eq_sum_range' hd]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, mul_one, hasseDeriv_coeff,
    Nat.choose_self, Nat.cast_one, one_mul, hs, hc, Polynomial.leadingCoeff]

theorem polynomial_shift_difference_coeff_pred (P : Polynomial ℝ)
    (hP : 0 < P.natDegree) (a b : ℝ) :
    (taylor a P - taylor b P).coeff (P.natDegree - 1) =
      (P.natDegree : ℝ) * P.leadingCoeff * (a - b) := by
  rw [coeff_sub, polynomial_taylor_coeff_pred P hP,
    polynomial_taylor_coeff_pred P hP]
  ring

theorem polynomial_shift_difference_natDegree_le (P : Polynomial ℝ)
    (hP : 0 < P.natDegree) (a b : ℝ) :
    (taylor a P - taylor b P).natDegree ≤ P.natDegree - 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases heq : n = P.natDegree
  · subst n
    rw [coeff_sub, polynomial_taylor_coeff_top, polynomial_taylor_coeff_top,
      sub_self]
  · have hlt : P.natDegree < n := by omega
    have ha : (taylor a P).coeff n = 0 :=
      coeff_eq_zero_of_natDegree_lt (by simpa only [natDegree_taylor] using hlt)
    have hb : (taylor b P).coeff n = 0 :=
      coeff_eq_zero_of_natDegree_lt (by simpa only [natDegree_taylor] using hlt)
    rw [coeff_sub, ha, hb, sub_self]

theorem polynomial_shift_difference_degree_irrational (P : Polynomial ℝ)
    (hP : 1 < P.natDegree) (hI : Irrational P.leadingCoeff)
    (h k : ℕ) (hhk : h ≠ k) :
    let D := taylor (h : ℝ) P - taylor (k : ℝ) P
    D.natDegree = P.natDegree - 1 ∧ Irrational D.leadingCoeff := by
  dsimp only
  have hp : 0 < P.natDegree := by omega
  have hdiff : (h : ℤ) - (k : ℤ) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast hhk
  have hprod : Irrational
      ((P.natDegree : ℝ) * P.leadingCoeff * ((h : ℝ) - (k : ℝ))) := by
    simpa only [Int.cast_sub, Int.cast_natCast] using
      (hI.natCast_mul (Nat.ne_of_gt hp)).mul_intCast hdiff
  have hc := polynomial_shift_difference_coeff_pred P hp (h : ℝ) (k : ℝ)
  have hcn : (taylor (h : ℝ) P - taylor (k : ℝ) P).coeff
      (P.natDegree - 1) ≠ 0 := by
    rw [hc]
    exact hprod.ne_zero
  have hd := natDegree_eq_of_le_of_coeff_ne_zero
    (polynomial_shift_difference_natDegree_le P hp (h : ℝ) (k : ℝ)) hcn
  refine ⟨hd, ?_⟩
  rw [Polynomial.leadingCoeff, hd, hc]
  exact hprod

theorem polynomial_shift_difference_leadingCoeff (P : Polynomial ℝ)
    (hP : 1 < P.natDegree) (hI : Irrational P.leadingCoeff)
    (h k : ℕ) (hhk : h ≠ k) :
    (taylor (h : ℝ) P - taylor (k : ℝ) P).leadingCoeff =
      (P.natDegree : ℝ) * P.leadingCoeff * ((h : ℝ) - (k : ℝ)) := by
  have hd := (polynomial_shift_difference_degree_irrational P hP hI h k hhk).1
  rw [Polynomial.leadingCoeff, hd]
  exact polynomial_shift_difference_coeff_pred P (by omega) (h : ℝ) (k : ℝ)

theorem polynomial_shift_difference_eval (P : Polynomial ℝ) (a b x : ℝ) :
    (taylor a P - taylor b P).eval x = P.eval (x + a) - P.eval (x + b) := by
  rw [eval_sub, taylor_eval, taylor_eval]

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

open Filter Polynomial
open scoped Topology ComplexConjugate

def scalarPhase (x : ℝ) : ℂ :=
  AddCircle.toCircle (x : UnitAddCircle)

@[simp] theorem scalarPhase_zero : scalarPhase 0 = 1 := by
  simp only [scalarPhase, AddCircle.coe_zero, AddCircle.toCircle_zero, Circle.coe_one]

@[simp] theorem norm_scalarPhase (x : ℝ) : ‖scalarPhase x‖ = 1 :=
  Circle.norm_coe _

theorem scalarPhase_add (x y : ℝ) :
    scalarPhase (x + y) = scalarPhase x * scalarPhase y := by
  simp only [scalarPhase, AddCircle.coe_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem scalarPhase_nat_mul (n : ℕ) (x : ℝ) :
    scalarPhase ((n : ℝ) * x) = scalarPhase x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, scalarPhase_add, ih, pow_succ]

theorem scalarPhase_sub (x y : ℝ) :
    scalarPhase (x - y) = scalarPhase x * conj (scalarPhase y) := by
  have hy : scalarPhase y ≠ 0 := Circle.coe_ne_zero _
  apply mul_right_cancel₀ hy
  rw [← scalarPhase_add, sub_add_cancel, mul_assoc, Complex.conj_mul', norm_scalarPhase]
  norm_num

theorem scalarPhase_ne_one_of_irrational {x : ℝ} (hx : Irrational x) :
    scalarPhase x ≠ 1 := by
  intro h
  have he : AddCircle.toCircle (x : UnitAddCircle) = AddCircle.toCircle (0 : UnitAddCircle) := by
    apply Subtype.ext
    simpa only [AddCircle.toCircle_zero, Circle.coe_one, scalarPhase] using h
  have hz : (x : UnitAddCircle) = 0 :=
    AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0) he
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
  exact hx.ne_int m (by simpa only [zsmul_eq_mul, mul_one] using hm.symm)

theorem fourier_eq_scalarPhase (k : ℤ) (x : ℝ) :
    fourier k (x : UnitAddCircle) = scalarPhase ((k : ℝ) * x) := by
  simp only [fourier_apply, scalarPhase, ← AddCircle.coe_zsmul, zsmul_eq_mul]

private theorem eval_degree_one (P : Polynomial ℝ) (hP : P.natDegree = 1) (x : ℝ) :
    P.eval x = P.coeff 0 + P.leadingCoeff * x := by
  have hc : P.coeff 1 = P.leadingCoeff := by
    simpa only [hP] using P.coeff_natDegree
  rw [Polynomial.eval_eq_sum_range' (by omega : P.natDegree < 2)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
    mul_one, pow_one, hc]

theorem polynomial_phase_average_tendsto_zero (P : Polynomial ℝ)
    (hP : 0 < P.natDegree) (hI : Irrational P.leadingCoeff) :
    Tendsto (complexAverage (fun n : ℕ => scalarPhase (P.eval (n : ℝ))))
      atTop (𝓝 0) := by
  have hall : ∀ d : ℕ, ∀ Q : Polynomial ℝ, Q.natDegree = d →
      0 < d → Irrational Q.leadingCoeff →
      Tendsto (complexAverage (fun n : ℕ => scalarPhase (Q.eval (n : ℝ))))
        atTop (𝓝 0) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro Q hQ hd hI
      by_cases hd1 : d = 1
      · have heval : ∀ n : ℕ, scalarPhase (Q.eval (n : ℝ)) =
            scalarPhase (Q.coeff 0) * scalarPhase Q.leadingCoeff ^ n := by
          intro n
          rw [eval_degree_one Q (hQ.trans hd1), scalarPhase_add,
            mul_comm Q.leadingCoeff (n : ℝ), scalarPhase_nat_mul]
        simpa only [heval] using complexAverage_const_mul_geometric_tendsto
          (scalarPhase (Q.coeff 0)) (scalarPhase Q.leadingCoeff)
          (norm_scalarPhase _) (scalarPhase_ne_one_of_irrational hI)
      · apply complexAverage_vanDerCorput
        · intro n
          exact (norm_scalarPhase _).le
        · intro h k hhk
          let D := Polynomial.taylor (h : ℝ) Q - Polynomial.taylor (k : ℝ) Q
          obtain ⟨hDdeg, hDirr⟩ :=
            polynomial_shift_difference_degree_irrational Q (by omega) hI h k hhk
          have hDpos : 0 < D.natDegree := by dsimp [D]; rw [hDdeg]; omega
          have hDlt : D.natDegree < d := by dsimp [D]; rw [hDdeg, hQ]; omega
          have hDlim := ih D.natDegree hDlt D rfl hDpos hDirr
          have hseq :
              (fun n : ℕ => scalarPhase (Q.eval ((n + h : ℕ) : ℝ)) *
                conj (scalarPhase (Q.eval ((n + k : ℕ) : ℝ)))) =
              (fun n : ℕ => scalarPhase (D.eval (n : ℝ))) := by
            funext n
            rw [← scalarPhase_sub]
            congr 1
            simp only [D, Polynomial.eval_sub, Polynomial.taylor_eval, Nat.cast_add]
          rw [hseq]
          exact hDlim
  exact hall P.natDegree P rfl hP hI

theorem denseRange_circlePolynomial_of_irrational_leadingCoeff (P : Polynomial ℝ)
    (hP : 0 < P.natDegree) (hI : Irrational P.leadingCoeff) :
    DenseRange (fun n : ℕ => ((P.eval (n : ℝ) : ℝ) : UnitAddCircle)) := by
  apply denseRange_of_circleFourierCancellation
  intro k hk
  let Q : Polynomial ℝ := Polynomial.C (k : ℝ) * P
  have hkreal : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  have hQdeg : Q.natDegree = P.natDegree := Polynomial.natDegree_C_mul hkreal
  have hQirr : Irrational Q.leadingCoeff := by
    simpa only [Q, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
      using hI.intCast_mul hk
  have hQlim := polynomial_phase_average_tendsto_zero Q (hQdeg.symm ▸ hP) hQirr
  have hseq :
      (fun n : ℕ => fourier k (((P.eval (n : ℝ) : ℝ) : UnitAddCircle))) =
      (fun n : ℕ => scalarPhase (Q.eval (n : ℝ))) := by
    funext n
    rw [fourier_eq_scalarPhase]
    simp only [Q, Polynomial.eval_mul, Polynomial.eval_C]
  change Tendsto (complexAverage
    (fun n : ℕ => fourier k (((P.eval (n : ℝ) : ℝ) : UnitAddCircle)))) atTop (𝓝 0)
  rw [hseq]
  exact hQlim

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators

namespace PeriodicTilingThree

private theorem finite_common_denominator {ι : Type uι} (s : Finset ι) (c : ι → ℝ)
    (hc : ∀ i ∈ s, ∃ q : ℚ, c i = (q : ℝ)) :
    ∃ a : ℕ, 0 < a ∧ ∀ i ∈ s, ∃ z : ℤ, c i * (a : ℝ) = (z : ℝ) := by
  classical
  let q : s → ℚ := fun i => Classical.choose (hc i.1 i.2)
  have hq : ∀ i : s, c i.1 = (q i : ℝ) := fun i => Classical.choose_spec (hc i.1 i.2)
  let a : ℕ := ∏ i : s, (q i).den
  refine ⟨a, Finset.prod_pos (fun i _ => (q i).den_pos), ?_⟩
  intro i hi
  let j : s := ⟨i, hi⟩
  have hj : (q j).den ∣ a := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  obtain ⟨b, hb⟩ := hj
  refine ⟨(q j).num * (b : ℤ), ?_⟩
  have hiq : c i = (q j : ℝ) := hq j
  have hden : ((q j).den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (q j).den_ne_zero
  rw [hiq, hb, Nat.cast_mul, ← mul_assoc, Rat.cast_def,
    div_mul_cancel₀ _ hden,
    Int.cast_mul, Int.cast_natCast]

private theorem circle_eval_eq_sum (P : Polynomial ℝ) (x : ℝ) :
    ((P.eval x : ℝ) : AddCircle (1 : ℝ)) =
      ∑ i ∈ P.support, ((P.coeff i * x ^ i : ℝ) : AddCircle (1 : ℝ)) := by
  change (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) (P.eval x) = _
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, map_sum]
  simp only [QuotientAddGroup.mk'_apply]

private theorem circle_monomial_add_period (c : ℝ) (a : ℕ) (z : ℤ)
    (hc : c * (a : ℝ) = (z : ℝ)) (i : ℕ) (n : ℤ) :
    ((c * ((n + (a : ℤ) : ℤ) : ℝ) ^ i : ℝ) : AddCircle (1 : ℝ)) =
      ((c * (n : ℝ) ^ i : ℝ) : AddCircle (1 : ℝ)) := by
  apply sub_eq_zero.mp
  rw [← AddCircle.coe_sub]
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  have hdiv : (a : ℤ) ∣ (n + (a : ℤ)) ^ i - n ^ i := by
    simpa using sub_dvd_pow_sub_pow (n + (a : ℤ)) n i
  obtain ⟨k, hk⟩ := hdiv
  refine ⟨z * k, ?_⟩
  have hk' : (((n + (a : ℤ) : ℤ) : ℝ) ^ i - (n : ℝ) ^ i) =
      (a : ℝ) * (k : ℝ) := by
    exact_mod_cast hk
  rw [← mul_sub, hk', ← mul_assoc, hc]
  simp only [zsmul_eq_mul, mul_one, Int.cast_mul]

theorem rational_nonconstant_circlePolynomial_periodic (P : Polynomial ℝ)
    (hP : ∀ i : ℕ, 0 < i → ∃ q : ℚ, P.coeff i = (q : ℝ)) :
    ∃ q : ℕ, 0 < q ∧ ∀ n : ℤ,
      ((P.eval ((n + (q : ℤ) : ℤ) : ℝ) : ℝ) : AddCircle (1 : ℝ)) =
        ((P.eval (n : ℝ) : ℝ) : AddCircle (1 : ℝ)) := by
  classical
  obtain ⟨a, ha, hcoeff⟩ := finite_common_denominator (P.support.erase 0) P.coeff
    (fun i hi => hP i (Nat.pos_of_ne_zero (Finset.mem_erase.mp hi).1))
  refine ⟨a, ha, ?_⟩
  intro n
  rw [circle_eval_eq_sum, circle_eval_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hi0 : i = 0
  · simp only [hi0, pow_zero, mul_one]
  · obtain ⟨z, hz⟩ := hcoeff i (Finset.mem_erase.mpr ⟨hi0, hi⟩)
    exact circle_monomial_add_period (P.coeff i) a z hz i n

private theorem circle_monomial_scaled_eq_zero (c : ℝ) (a : ℕ) (z : ℤ)
    (hc : c * (a : ℝ) = (z : ℝ)) (i : ℕ) (hi : 0 < i) (n : ℕ) :
    ((c * ((a * n : ℕ) : ℝ) ^ i : ℝ) : AddCircle (1 : ℝ)) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  refine ⟨z * (a : ℤ) ^ k * (n : ℤ) ^ (k + 1), ?_⟩
  have hmul : c * ((a * n : ℕ) : ℝ) ^ (k + 1) =
      (z : ℝ) * (a : ℝ) ^ k * (n : ℝ) ^ (k + 1) := by
    calc
      _ = (c * (a : ℝ)) * ((a : ℝ) ^ k * (n : ℝ) ^ (k + 1)) := by
        rw [Nat.cast_mul, mul_pow, pow_succ]
        ring
      _ = _ := by rw [hc]; ring
  simpa only [zsmul_eq_mul, mul_one, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    using hmul.symm

theorem exists_progression_irrational_leadingCoeff (P : Polynomial ℝ)
    (hP : ∃ i : ℕ, 0 < i ∧ Irrational (P.coeff i)) :
    ∃ a : ℕ, 0 < a ∧ ∃ Q : Polynomial ℝ,
      0 < Q.natDegree ∧ Irrational Q.leadingCoeff ∧ ∀ n : ℕ,
        ((P.eval ((a * n : ℕ) : ℝ) : ℝ) : AddCircle (1 : ℝ)) =
          ((Q.eval (n : ℝ) : ℝ) : AddCircle (1 : ℝ)) := by
  classical
  let s := P.support.filter fun i => 0 < i ∧ Irrational (P.coeff i)
  have hs : s.Nonempty := by
    obtain ⟨i, hi, hirr⟩ := hP
    exact ⟨i, Finset.mem_filter.mpr ⟨Polynomial.mem_support_iff.mpr hirr.ne_zero, hi, hirr⟩⟩
  let d := s.max' hs
  have hdmem : d ∈ s := Finset.max'_mem s hs
  have hdpos : 0 < d := (Finset.mem_filter.mp hdmem).2.1
  have hdirr : Irrational (P.coeff d) := (Finset.mem_filter.mp hdmem).2.2
  have hrat : ∀ j : ℕ, d < j → ∃ q : ℚ, P.coeff j = (q : ℝ) := by
    intro j hj
    have hnot : ¬ Irrational (P.coeff j) := by
      intro hirr
      have hjmem : j ∈ s := Finset.mem_filter.mpr
        ⟨Polynomial.mem_support_iff.mpr hirr.ne_zero, hdpos.trans hj, hirr⟩
      exact (not_le_of_gt hj) (Finset.le_max' s j hjmem)
    simpa only [Irrational, Set.mem_range, not_not, eq_comm] using hnot
  obtain ⟨a, ha, hcoeff⟩ :=
    finite_common_denominator (P.support.filter fun i => d < i) P.coeff
      (fun i hi => hrat i (Finset.mem_filter.mp hi).2)
  let t := P.support.filter fun i => i ≤ d
  let Q : Polynomial ℝ :=
    ∑ i ∈ t, Polynomial.monomial i (P.coeff i * (a : ℝ) ^ i)
  have hQcoeff : ∀ j : ℕ, Q.coeff j =
      if j ∈ t then P.coeff j * (a : ℝ) ^ j else 0 := by
    intro j
    simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
      Finset.sum_ite_eq']
  have hdmemt : d ∈ t := Finset.mem_filter.mpr
    ⟨Polynomial.mem_support_iff.mpr hdirr.ne_zero, le_rfl⟩
  have hQirr : Irrational (Q.coeff d) := by
    rw [hQcoeff, ite_eq_left hdmemt]
    simpa only [Nat.cast_pow] using hdirr.mul_natCast (pow_ne_zero d ha.ne')
  have hQdeg : Q.natDegree = d := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero _ hQirr.ne_zero
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [hQcoeff, ite_eq_right]
    intro hjmem
    exact (not_le_of_gt hj) (Finset.mem_filter.mp hjmem).2
  refine ⟨a, ha, Q, hQdeg.symm ▸ hdpos, ?_, ?_⟩
  · simpa only [Polynomial.leadingCoeff, hQdeg] using hQirr
  · intro n
    have hQeval : ((Q.eval (n : ℝ) : ℝ) : AddCircle (1 : ℝ)) =
        ∑ i ∈ t, ((P.coeff i * ((a * n : ℕ) : ℝ) ^ i : ℝ) : AddCircle (1 : ℝ)) := by
      simp only [Q, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
      change (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
        (∑ i ∈ t, (P.coeff i * (a : ℝ) ^ i) * (n : ℝ) ^ i) = _
      rw [map_sum]
      simp only [QuotientAddGroup.mk'_apply]
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      rw [Nat.cast_mul, mul_pow]
      ring
    rw [circle_eval_eq_sum, hQeval]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hit
    have hdi : d < i := lt_of_not_ge fun hid =>
      hit (Finset.mem_filter.mpr ⟨hi, hid⟩)
    obtain ⟨z, hz⟩ := hcoeff i (Finset.mem_filter.mpr ⟨hi, hdi⟩)
    exact circle_monomial_scaled_eq_zero (P.coeff i) a z hz i (hdpos.trans hdi) n

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

open Set Polynomial
open scoped Topology

theorem denseRange_circlePolynomial_of_irrational_coefficient (P : Polynomial ℝ)
    (hP : ∃ i : ℕ, 0 < i ∧ Irrational (P.coeff i)) :
    DenseRange (fun n : ℤ => ((P.eval (n : ℝ) : ℝ) : UnitAddCircle)) := by
  obtain ⟨a, ha, Q, hQ, hI, hvalues⟩ := exists_progression_irrational_leadingCoeff P hP
  have hd := denseRange_circlePolynomial_of_irrational_leadingCoeff Q hQ hI
  apply Dense.mono (s₁ := Set.range (fun n : ℕ => ((Q.eval (n : ℝ) : ℝ) : UnitAddCircle))) _ hd
  rintro _ ⟨n, rfl⟩
  refine ⟨((a * n : ℕ) : ℤ), ?_⟩
  simpa only [Int.cast_natCast] using hvalues n

theorem circle_polynomial_periodic_of_not_dense (f : ℤ → UnitAddCircle)
    (r : ℕ) (hpoly : (forwardDiff^[r]) f = 0) (hnd : ¬ DenseRange f) :
    ∃ q : ℕ, 0 < q ∧ Function.Periodic f (q : ℤ) := by
  obtain ⟨P, hP⟩ := exists_polynomial_lift_of_iter_forwardDiff_eq_zero f r hpoly
  have hrat : ∀ i : ℕ, 0 < i → ∃ q : ℚ, P.coeff i = (q : ℝ) := by
    intro i hi
    by_contra h
    have hirr : Irrational (P.coeff i) := by
      rintro ⟨q, hq⟩
      exact h ⟨q, hq.symm⟩
    apply hnd
    have hd := denseRange_circlePolynomial_of_irrational_coefficient P ⟨i, hi, hirr⟩
    have heq : (fun n : ℤ => ((P.eval (n : ℝ) : ℝ) : UnitAddCircle)) = f := funext hP
    rwa [heq] at hd
  obtain ⟨q, hq, hper⟩ := rational_nonconstant_circlePolynomial_periodic P hrat
  refine ⟨q, hq, ?_⟩
  intro n
  rw [← hP (n + q), ← hP n]
  exact hper n

theorem circle_polynomial_periodic_of_omits_open (f : ℤ → UnitAddCircle)
    (r : ℕ) (hpoly : (forwardDiff^[r]) f = 0)
    (U : Set UnitAddCircle) (hU : IsOpen U) (hne : U.Nonempty)
    (hmiss : ∀ n, f n ∉ U) :
    ∃ q : ℕ, 0 < q ∧ Function.Periodic f (q : ℤ) := by
  apply circle_polynomial_periodic_of_not_dense f r hpoly
  intro hd
  obtain ⟨n, hn⟩ := hd.exists_mem_open hU hne
  exact hmiss n hn

private theorem not_denseRange_circle_of_bounded_lt_one (f : ℤ → ℝ) (c : ℝ)
    (h0 : ∀ n, 0 ≤ f n) (hc : ∀ n, f n ≤ c) (hc1 : c < 1) :
    ¬ DenseRange (fun n => (f n : UnitAddCircle)) := by
  intro hd
  have hc0 : 0 ≤ c := (h0 0).trans (hc 0)
  let K : Set UnitAddCircle := ((↑) : ℝ → UnitAddCircle) '' Set.Icc 0 c
  have hK : IsClosed K :=
    (isCompact_Icc.image (AddCircle.continuous_mk' (1 : ℝ))).isClosed
  have hsub : Set.range (fun n => (f n : UnitAddCircle)) ⊆ K := by
    rintro _ ⟨n, rfl⟩
    exact ⟨f n, ⟨h0 n, hc n⟩, rfl⟩
  have hm : (((c + 1) / 2 : ℝ) : UnitAddCircle) ∈ K :=
    (closure_minimal hsub hK) (hd _)
  obtain ⟨y, hy, heq⟩ := hm
  have hyI : y ∈ Set.Ico (0 : ℝ) (0 + 1) := ⟨hy.1, by linarith [hy.2]⟩
  have hmI : (c + 1) / 2 ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    constructor <;> linarith
  have hyEq : y = (c + 1) / 2 :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico hyI hmI).mp heq
  rw [hyEq] at hy
  linarith [hy.2]

theorem real_polynomial_periodic_of_bounded_lt_one
    (r : ℕ) (_hr : 0 < r) (f : ℤ → ℝ) (c : ℝ)
    (h0 : ∀ n, 0 ≤ f n) (hc : ∀ n, f n ≤ c) (hc1 : c < 1)
    (hpoly : (forwardDiff^[r]) (fun n => (f n : AddCircle (1 : ℝ))) = 0) :
    ∃ q : ℕ, 0 < q ∧ Function.Periodic f (q : ℤ) := by
  obtain ⟨q, hq, hper⟩ := circle_polynomial_periodic_of_not_dense
    (fun n => (f n : UnitAddCircle)) r hpoly
    (not_denseRange_circle_of_bounded_lt_one f c h0 hc hc1)
  refine ⟨q, hq, ?_⟩
  intro n
  apply (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (show f (n + q) ∈ Set.Ico (0 : ℝ) (0 + 1) from
      ⟨h0 _, by simpa using (hc _).trans_lt hc1⟩)
    (show f n ∈ Set.Ico (0 : ℝ) (0 + 1) from
      ⟨h0 _, by simpa using (hc _).trans_lt hc1⟩)).mp
  exact hper n

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree

theorem coset_configuration_has_period {m : ℕ}
    (P : Fin m → ℤ → ℝ) (b : Fin m → ℤ) (a : Plane → ℝ)
    (hzero : ∀ j n, 0 ≤ P j n)
    (hpair : ∀ i j, i ≠ j → ∀ n r, P i n + P j r ≤ 1)
    (hsum : ∀ x : Plane, a x = 1 - ∑ j, P j (x.1 + b j * x.2))
    (degree : ℕ) (hdegree : 0 < degree)
    (hpoly : ∀ j, (forwardDiff^[degree])
      (fun n => (P j n : AddCircle (1 : ℝ))) = 0) :
    ∃ v : Plane, v ≠ 0 ∧ Function.Periodic a v := by
  classical
  by_cases hbounded : ∀ j, ∃ c : ℝ, c < 1 ∧ ∀ n, P j n ≤ c
  · have hp : ∀ j, ∃ q : ℕ, 0 < q ∧ Function.Periodic (P j) (q : ℤ) := by
      intro j
      obtain ⟨c, hc, hPc⟩ := hbounded j
      exact real_polynomial_periodic_of_bounded_lt_one degree hdegree
        (P j) c (hzero j) hPc hc (hpoly j)
    choose p hp hperiod using hp
    let Q : ℕ := ∏ j, p j
    have hQ : 0 < Q := Finset.prod_pos fun j _ => hp j
    refine ⟨(0, (Q : ℤ)), ?_, ?_⟩
    · intro h
      have hz : (Q : ℤ) = 0 := congrArg Prod.snd h
      exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hQ)) hz
    · intro x
      rw [hsum, hsum]
      apply congrArg (fun y : ℝ => 1 - y)
      apply Finset.sum_congr rfl
      intro j _hj
      have hd : p j ∣ Q := Finset.dvd_prod_of_mem p (Finset.mem_univ j)
      obtain ⟨k, hk⟩ := hd
      have hperiodQ : Function.Periodic (P j) (b j * (Q : ℤ)) := by
        simpa only [hk, Nat.cast_mul, Int.cast_id, mul_assoc, mul_left_comm, mul_comm] using
          (hperiod j).int_mul (b j * (k : ℤ))
      change P j (x.1 + 0 + b j * (x.2 + (Q : ℤ))) =
        P j (x.1 + b j * x.2)
      rw [show x.1 + 0 + b j * (x.2 + (Q : ℤ)) =
        (x.1 + b j * x.2) + b j * (Q : ℤ) by ring]
      exact hperiodQ _
  · obtain ⟨j, hj⟩ := not_forall.mp hbounded
    have hother : ∀ i, i ≠ j → ∀ n, P i n = 0 := by
      intro i hij n
      apply le_antisymm _ (hzero i n)
      apply le_of_not_gt
      intro hpos
      apply hj
      refine ⟨1 - P i n, by linarith, ?_⟩
      intro r
      have hcross := hpair j i (Ne.symm hij) r n
      linarith
    have hone : ∀ x : Plane, a x = 1 - P j (x.1 + b j * x.2) := by
      intro x
      rw [hsum]
      apply congrArg (fun y : ℝ => 1 - y)
      apply Finset.sum_eq_single j
      · intro i _hi hij
        exact hother i hij _
      · intro hj'
        exact (hj' (Finset.mem_univ j)).elim
    refine ⟨(-b j, 1), ?_, ?_⟩
    · intro h
      have hz : (1 : ℤ) = 0 := congrArg Prod.snd h
      exact one_ne_zero hz
    · intro x
      rw [hone, hone]
      apply congrArg (fun n : ℤ => 1 - P j n)
      change x.1 + -b j + b j * (x.2 + 1) = x.1 + b j * x.2
      ring

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

open scoped BigOperators

theorem integerCombination_injective {e H : Plane} (hdet : planeDet e H ≠ 0) :
    Function.Injective (integerCombination e H) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  change a * e.1 + b * H.1 = c * e.1 + d * H.1 at hx
  change a * e.2 + b * H.2 = c * e.2 + d * H.2 at hy
  apply Prod.ext
  · have hz : planeDet e H * (a - c) = 0 := by
      dsimp [planeDet]
      linear_combination H.2 * hx - H.1 * hy
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hdet)
  · have hz : planeDet e H * (b - d) = 0 := by
      dsimp [planeDet]
      linear_combination e.1 * hy - e.2 * hx
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hdet)

def cosetPart (P : AddSubgroup Plane) (A : Set Plane) (c : Plane ⧸ P) : Set Plane :=
  {x | x ∈ A ∧ (x : Plane ⧸ P) = c}

theorem sum_cosetPart_indicator (P : AddSubgroup Plane) [Fintype (Plane ⧸ P)]
    (A : Set Plane) (x : Plane) :
    (∑ c : Plane ⧸ P, tileIndicator ℝ (cosetPart P A c) x) = tileIndicator ℝ A x := by
  classical
  by_cases hx : x ∈ A <;> simp [tileIndicator, cosetPart, hx]

private theorem mem_iff_of_tileIndicator_eq (A : Set Plane) (x y : Plane)
    (h : tileIndicator ℝ A x = tileIndicator ℝ A y) : x ∈ A ↔ y ∈ A := by
  classical
  by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> simp_all [tileIndicator]

theorem cosetPart_period_of_coordinate_period (A : Set Plane) (e H x v : Plane)
    (hper : Function.Periodic
      (fun st : Plane => tileIndicator ℝ A (x + st.1 • e + st.2 • H)) v) :
    Period (cosetPart (integerSpan2 e H) A (x : Plane ⧸ integerSpan2 e H))
      (integerCombination e H v) := by
  classical
  let P := integerSpan2 e H
  let L := integerCombination e H
  have hvP : L v ∈ P := ⟨v, rfl⟩
  intro y
  have hclass : ((y + L v : Plane) : Plane ⧸ P) = (y : Plane ⧸ P) :=
    QuotientAddGroup.mk_add_of_mem y hvP
  change ((y + L v ∈ A) ∧ ((y + L v : Plane) : Plane ⧸ P) = (x : Plane ⧸ P)) ↔
    (y ∈ A ∧ (y : Plane ⧸ P) = (x : Plane ⧸ P))
  rw [hclass]
  by_cases hyclass : (y : Plane ⧸ P) = (x : Plane ⧸ P)
  · simp only [hyclass, and_true]
    have hdiff : y - x ∈ P := QuotientAddGroup.eq_iff_sub_mem.mp hyclass
    obtain ⟨st, hst⟩ := hdiff
    have hyrep : y = x + L st := by
      rw [hst]
      abel
    have hyshift : y + L v = x + L (st + v) := by
      rw [hyrep, map_add]
      abel
    apply mem_iff_of_tileIndicator_eq
    rw [hyshift, hyrep]
    simpa only [L, integerCombination, AddMonoidHom.coe_mk, ZeroHom.coe_mk, add_assoc] using hper st
  · simp only [hyclass, and_false]

theorem finite_periodic_parts_of_coset_periods {A : Set Plane}
    (e H : Plane) (hdet : planeDet e H ≠ 0)
    (hlocal : ∀ x : Plane, ∃ v : Plane, v ≠ 0 ∧ Function.Periodic
      (fun st : Plane => tileIndicator ℝ A (x + st.1 • e + st.2 • H)) v) :
    ∃ m : ℕ, ∃ parts : Fin m → Set Plane, ∃ w : Fin m → Plane,
      (∀ x, (∑ j, tileIndicator ℝ (parts j) x) = tileIndicator ℝ A x) ∧
      ∀ j, w j ≠ 0 ∧ Period (parts j) (w j) := by
  classical
  let P := integerSpan2 e H
  let : P.FiniteIndex := integerSpan2_finiteIndex e H hdet
  let : Fintype (Plane ⧸ P) := P.fintypeQuotientOfFiniteIndex
  have hex : ∀ c : Plane ⧸ P, ∃ w : Plane, w ≠ 0 ∧ Period (cosetPart P A c) w := by
    intro c
    let x : Plane := Quotient.out c
    have hx : (x : Plane ⧸ P) = c := Quotient.out_eq' c
    obtain ⟨v, hv, hper⟩ := hlocal x
    refine ⟨integerCombination e H v, ?_, ?_⟩
    · intro hz
      apply hv
      apply integerCombination_injective hdet
      simpa only [map_zero] using hz
    · rw [← hx]
      exact cosetPart_period_of_coordinate_period A e H x v hper
  choose w hw0 hwper using hex
  let eqv : Fin (Fintype.card (Plane ⧸ P)) ≃ (Plane ⧸ P) :=
    (Fintype.equivFin (Plane ⧸ P)).symm
  refine ⟨Fintype.card (Plane ⧸ P), (fun j => cosetPart P A (eqv j)),
    (fun j => w (eqv j)), ?_, ?_⟩
  · intro x
    rw [eqv.sum_comp (fun c => tileIndicator ℝ (cosetPart P A c) x)]
    exact sum_cosetPart_indicator P A x
  · intro j
    exact ⟨hw0 (eqv j), hwper (eqv j)⟩

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree

theorem Tiles.exists_weak_periodic_partition {F : Finset Plane} {A : Set Plane}
    (h : Tiles F A) (h0 : (0 : Plane) ∈ F) :
    ∃ (m : ℕ) (parts : Fin m → Set Plane) (v : Fin m → Plane),
      (∀ x, (∑ j, tileIndicator ℝ (parts j) x) = tileIndicator ℝ A x) ∧
      (∀ j, v j ≠ 0) ∧ ∀ j, Period (parts j) (v j) := by
  classical
  obtain ⟨m, v, φ, hv, hpair, hφ, hsum, hp⟩ :=
    h.exists_directional_decomposition h0
  by_cases hm0 : m = 0
  · subst m
    have hA : A = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      have hx := hsum x
      by_contra hnot
      simp [tileIndicator, hnot] at hx
    refine ⟨1, fun _ => A, fun _ => (1, 0), ?_, ?_, ?_⟩
    · intro x
      simp
    · intro j hj
      have hz : (1 : ℤ) = 0 := congrArg Prod.fst hj
      exact one_ne_zero hz
    · intro j x
      simp [hA]
  · have hm : 0 < m := Nat.pos_of_ne_zero hm0
    let j₀ : Fin m := ⟨0, hm⟩
    obtain ⟨e, he, htrans, hspan⟩ := exists_common_transverse v hv hpair
    obtain ⟨K, hK, hKrep⟩ := exists_common_second_vector v j₀ e htrans
    let H : Plane := (K : ℤ) • v j₀
    choose α β hα hH using hKrep
    have hdet : planeDet e H ≠ 0 := by
      dsimp [H]
      rw [planeDet_zsmul_right]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)) (htrans j₀)
    have hlocal : ∀ x : Plane, ∃ w : Plane, w ≠ 0 ∧
        Function.Periodic
          (fun st : Plane => tileIndicator ℝ A (x + st.1 • e + st.2 • H)) w := by
      intro x
      let P : Fin m → ℤ → ℝ := fun j n => φ j (x + n • e)
      have hcoord (j : Fin m) (s t : ℤ) :
          φ j (x + s • e + t • H) = P j (s + β j * t) := by
        have hpoint : x + s • e + t • H =
            (x + (s + β j * t) • e) + (t * α j) • v j := by
          change x + s • e + t • ((K : ℤ) • v j₀) = _
          rw [hH j]
          apply Prod.ext <;> simp [smul_add, add_smul, zsmul_eq_mul] <;> ring
        rw [hpoint]
        exact (hp j).zsmul (t * α j) _
      have hlocalSum (st : Plane) :
          tileIndicator ℝ A (x + st.1 • e + st.2 • H) =
            1 - ∑ j, P j (st.1 + β j * st.2) := by
        have hz := hsum (x + st.1 • e + st.2 • H)
        have heq : (∑ j, φ j (x + st.1 • e + st.2 • H)) =
            ∑ j, P j (st.1 + β j * st.2) := by
          apply Finset.sum_congr rfl
          intro j _
          exact hcoord j st.1 st.2
        rw [heq] at hz
        linarith
      refine coset_configuration_has_period P β _
        (fun j n => (hφ j _).1) ?_ hlocalSum m hm ?_
      · intro i j hij n r
        exact directional_slice_pair_bound A v φ e hspan
          (fun j y => (hφ j y).1) hp hsum x i j hij n r
      · intro j
        exact directional_circle_slice_polynomial hm A v φ e hspan hp hsum j x
    obtain ⟨n, parts, w, hparts, hw⟩ :=
      finite_periodic_parts_of_coset_periods e H hdet hlocal
    exact ⟨n, parts, w, hparts, fun j => (hw j).1, fun j => (hw j).2⟩

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace PeriodicTilingThree

open scoped BigOperators

theorem tileIndicator_finite_union_eq_sum {G : Type uG} {ι : Type uι} [Fintype ι]
    (parts : ι → Set G)
    (hbound : ∀ x, (∑ i, tileIndicator ℝ (parts i) x) ≤ 1)
    (s : Finset ι) (x : G) :
    tileIndicator ℝ {x | ∃ i ∈ s, x ∈ parts i} x =
      ∑ i ∈ s, tileIndicator ℝ (parts i) x := by
  classical
  by_cases hx : ∃ i ∈ s, x ∈ parts i
  · obtain ⟨i, hi, hix⟩ := hx
    have hlo : (1 : ℝ) ≤ ∑ j ∈ s, tileIndicator ℝ (parts j) x := by
      simpa only [tileIndicator, ite_eq_left hix] using
        (Finset.single_le_sum (fun j _ => tileIndicator_nonneg (parts j) x) hi)
    have hhi : (∑ j ∈ s, tileIndicator ℝ (parts j) x) ≤ 1 := by
      calc
        _ ≤ ∑ j, tileIndicator ℝ (parts j) x :=
          Finset.sum_le_univ_sum_of_nonneg (fun j => tileIndicator_nonneg (parts j) x)
        _ ≤ 1 := hbound x
    have hmem : x ∈ {x | ∃ j ∈ s, x ∈ parts j} := ⟨i, hi, hix⟩
    rw [tileIndicator, ite_eq_left hmem]
    exact le_antisymm hlo hhi
  · have hz : (∑ i ∈ s, tileIndicator ℝ (parts i) x) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hix : x ∉ parts i := fun h => hx ⟨i, hi, h⟩
      simp only [tileIndicator, ite_eq_right hix]
    rw [hz]
    simp only [tileIndicator, Set.mem_ofPred_eq, ite_eq_right hx]

theorem exists_grouped_periodic_parts {ι : Type uι} [Fintype ι]
    (parts : ι → Set Plane) (v : ι → Plane)
    (hv : ∀ i, v i ≠ 0) (hp : ∀ i, Period (parts i) (v i))
    {A : Set Plane}
    (hsum : ∀ x, (∑ i, tileIndicator ℝ (parts i) x) = tileIndicator ℝ A x) :
    ∃ (m : ℕ) (w : Fin m → Plane) (grouped : Fin m → Set Plane),
      (∀ j, w j ≠ 0) ∧
      (∀ i j, i ≠ j → planeDet (w i) (w j) ≠ 0) ∧
      (∀ x, (∑ j, tileIndicator ℝ (grouped j) x) = tileIndicator ℝ A x) ∧
      ∀ j, Period (grouped j) (w j) := by
  classical
  let r : Setoid ι :=
    { r := fun i j => planeDet (v i) (v j) = 0
      iseqv := ⟨fun i => planeDet_self (v i),
        fun {i j} hij => by rw [planeDet_swap, hij, neg_zero],
        fun {i j k} hij hjk => planeDet_zero_trans (hv j) hij hjk⟩ }
  let Q := Quotient r
  let : Fintype Q := Fintype.ofFinite Q
  let cls : ι → Q := Quotient.mk r
  let fiber (j : Q) : Finset ι := Finset.univ.filter (fun i => cls i = j)
  have mem_fiber (i : ι) (j : Q) : i ∈ fiber j ↔ cls i = j := by
    simp [fiber]
  have out_mem (j : Q) : j.out ∈ fiber j :=
    (mem_fiber _ _).2 (Quotient.out_eq j)
  have hex (j : Q) : ∃ w : Plane, w ≠ 0 ∧
      ∀ i ∈ fiber j, ∃ n : ℤ, w = n • v i := by
    have himage : ((fiber j).image v).Nonempty :=
      ⟨v j.out, Finset.mem_image_of_mem v (out_mem j)⟩
    obtain ⟨w, hw, hm⟩ := exists_common_collinear_multiple ((fiber j).image v) himage
      (by
        intro z hz
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
        exact hv i)
      (by
        intro z hz z' hz'
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hz'
        exact Quotient.exact (((mem_fiber i j).1 hi).trans ((mem_fiber i' j).1 hi').symm))
    exact ⟨w, hw, fun i hi => hm (v i) (Finset.mem_image_of_mem v hi)⟩
  choose w hw hm using hex
  let grouped : Q → Set Plane := fun j => {x | ∃ i ∈ fiber j, x ∈ parts i}
  have hbound (x : Plane) : (∑ i, tileIndicator ℝ (parts i) x) ≤ 1 := by
    rw [hsum]
    exact tileIndicator_le_one A x
  have hind (j : Q) (x : Plane) : tileIndicator ℝ (grouped j) x =
      ∑ i ∈ fiber j, tileIndicator ℝ (parts i) x :=
    tileIndicator_finite_union_eq_sum parts hbound (fiber j) x
  have htotal (x : Plane) : (∑ j, tileIndicator ℝ (grouped j) x) =
      tileIndicator ℝ A x := by
    simp_rw [hind]
    simp only [fiber, Finset.sum_filter]
    rw [Finset.sum_comm]
    calc
      (∑ i, ∑ j : Q, if cls i = j then tileIndicator ℝ (parts i) x else 0) =
          ∑ i, tileIndicator ℝ (parts i) x := by
        apply Finset.sum_congr rfl
        intro i _
        simpa only [ite_eq_left rfl, ite_true] using
          (Finset.sum_eq_single (s := Finset.univ)
            (f := fun j : Q => if cls i = j then tileIndicator ℝ (parts i) x else 0)
            (cls i) (fun j _ hji => ite_eq_right (Ne.symm hji))
            (fun h => (h (Finset.mem_univ (cls i))).elim))
      _ = tileIndicator ℝ A x := hsum x
  have hper (j : Q) : Period (grouped j) (w j) := by
    intro x
    change (∃ i ∈ fiber j, x + w j ∈ parts i) ↔ ∃ i ∈ fiber j, x ∈ parts i
    constructor
    · rintro ⟨i, hi, hx⟩
      obtain ⟨n, hn⟩ := hm j i hi
      refine ⟨i, hi, ?_⟩
      rw [hn] at hx
      exact ((hp i).zsmul n x).mp hx
    · rintro ⟨i, hi, hx⟩
      obtain ⟨n, hn⟩ := hm j i hi
      refine ⟨i, hi, ?_⟩
      rw [hn]
      exact ((hp i).zsmul n x).mpr hx
  have hpair (j k : Q) (hjk : j ≠ k) : planeDet (w j) (w k) ≠ 0 := by
    intro hdet
    obtain ⟨n, hn⟩ := hm j j.out (out_mem j)
    obtain ⟨m, hmk⟩ := hm k k.out (out_mem k)
    have hn0 : n ≠ 0 := by
      intro hn0
      exact hw j (by simpa [hn0] using hn)
    have hm0 : m ≠ 0 := by
      intro hm0
      exact hw k (by simpa [hm0] using hmk)
    rw [hn, hmk, planeDet_zsmul_left, planeDet_zsmul_right] at hdet
    have hz : planeDet (v j.out) (v k.out) = 0 :=
      (mul_eq_zero.mp ((mul_eq_zero.mp hdet).resolve_left hn0)).resolve_left hm0
    apply hjk
    calc
      j = cls j.out := (Quotient.out_eq j).symm
      _ = cls k.out := Quotient.sound hz
      _ = k := Quotient.out_eq k
  let e : Fin (Fintype.card Q) ≃ Q := (Fintype.equivFin Q).symm
  refine ⟨Fintype.card Q, fun j => w (e j), fun j => grouped (e j),
    fun j => hw (e j), ?_, ?_, fun j => hper (e j)⟩
  · intro i j hij
    exact hpair (e i) (e j) (fun he => hij (e.injective he))
  · intro x
    rw [e.sum_comp (fun j => tileIndicator ℝ (grouped j) x)]
    exact htotal x

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

section Region

variable {G : Type uG} [AddCommGroup G]

structure TilesRegion (F : Finset G) (D E : Set G) : Prop where
  add_mem : ∀ f ∈ F, ∀ d ∈ D, f + d ∈ E
  unique : ∀ x ∈ E, ∃! f : ↥F, x - (f : G) ∈ D

theorem tilesRegion_univ_iff {F : Finset G} {D : Set G} :
    TilesRegion F D Set.univ ↔ Tiles F D := by
  rw [tiles_iff_unique_tile]
  constructor
  · intro h x
    exact h.unique x (Set.mem_univ x)
  · intro h
    exact ⟨fun _ _ _ _ => Set.mem_univ _, fun x _ => h x⟩

theorem TilesRegion.mem_iff {F : Finset G} {D E : Set G}
    (h : TilesRegion F D E) (x : G) :
    x ∈ E ↔ ∃ f : ↥F, x - (f : G) ∈ D := by
  constructor
  · intro hx
    obtain ⟨f, hf, _⟩ := h.unique x hx
    exact ⟨f, hf⟩
  · rintro ⟨f, hf⟩
    simpa [add_comm] using h.add_mem f f.property (x - f) hf

theorem TilesRegion.of_local_copy {F : Finset G} {D D' E : Set G}
    (h : TilesRegion F D E)
    (hcopy : ∀ x : G, ∃ y : G, (y ∈ E ↔ x ∈ E) ∧
      ∀ f : ↥F, (x - (f : G) ∈ D' ↔ y - (f : G) ∈ D)) :
    TilesRegion F D' E := by
  constructor
  · intro f hf d hd
    obtain ⟨y, hE, htests⟩ := hcopy (f + d)
    apply hE.mp
    apply (h.mem_iff y).mpr
    refine ⟨⟨f, hf⟩, (htests ⟨f, hf⟩).mp ?_⟩
    simpa using hd
  · intro x hx
    obtain ⟨y, hE, htests⟩ := hcopy x
    obtain ⟨f, hf, huniq⟩ := h.unique y (hE.mpr hx)
    refine ⟨f, (htests f).mpr hf, ?_⟩
    intro g hg
    exact huniq g ((htests g).mp hg)

end Region

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

variable {G : Type uG} [AddCommGroup G]

theorem configDiff_bounded (v : G) (f : G → ℝ)
    (hf : ∃ B : ℝ, ∀ x, |f x| ≤ B) :
    ∃ B : ℝ, ∀ x, |configDiff v f x| ≤ B := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨B + B, fun x => ?_⟩
  calc
    |configDiff v f x| = |f (x + v) + -f x| := rfl
    _ ≤ |f (x + v)| + |-f x| := abs_add_le _ _
    _ = |f (x + v)| + |f x| := by rw [abs_neg]
    _ ≤ B + B := add_le_add (hB _) (hB _)

theorem configDiff_eq_zero_of_second (v : G) (f : G → ℝ)
    (hf : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (hsecond : configDiff v (configDiff v f) = 0) : configDiff v f = 0 := by
  obtain ⟨B, hB⟩ := hf
  let g := configDiff v f
  have hg : Function.Periodic g v := (configDiff_eq_zero_iff v g).mp hsecond
  ext x
  have hg_nat : ∀ n : ℕ, g (x + n • v) = g x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        simpa only [succ_nsmul, ← add_assoc] using (hg (x + n • v)).trans ih
  have hf_nat : ∀ n : ℕ, f (x + n • v) = f x + (n : ℝ) * g x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hd := hg_nat n
        change f (x + n • v + v) - f (x + n • v) = g x at hd
        simp only [succ_nsmul, ← add_assoc, Nat.cast_add, Nat.cast_one]
        linarith
  have hx := abs_le.mp (hB x)
  have hz : g x = 0 := by
    rcases lt_trichotomy (g x) 0 with hneg | hzero | hpos
    · obtain ⟨n, hn⟩ := exists_nat_gt (2 * B / (-g x))
      have hn' : 2 * B < (n : ℝ) * (-g x) :=
        (div_lt_iff₀ (neg_pos.mpr hneg)).mp hn
      have hy := abs_le.mp (hB (x + n • v))
      have he := hf_nat n
      nlinarith
    · exact hzero
    · obtain ⟨n, hn⟩ := exists_nat_gt (2 * B / g x)
      have hn' : 2 * B < (n : ℝ) * g x := (div_lt_iff₀ hpos).mp hn
      have hy := abs_le.mp (hB (x + n • v))
      have he := hf_nat n
      nlinarith
  exact hz

theorem configDiff_eq_zero_of_iterate (v : G) (n : ℕ) (f : G → ℝ)
    (hf : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (hn : 0 < n) (hiter : (configDiff v)^[n] f = 0) :
    configDiff v f = 0 := by
  induction n generalizing f with
  | zero => exact (Nat.not_lt_zero _ hn).elim
  | succ n ih =>
      cases n with
      | zero =>
          change configDiff v f = 0 at hiter
          exact hiter
      | succ n =>
          have hnext : (configDiff v)^[n + 1] (configDiff v f) = 0 := by
            simpa only [Function.iterate_succ_apply] using hiter
          have hsecond : configDiff v (configDiff v f) = 0 :=
            ih (configDiff v f) (configDiff_bounded v f hf) (Nat.succ_pos _) hnext
          exact configDiff_eq_zero_of_second v f hf hsecond

theorem periodic_of_bounded_configDiff_iterate (v : G) (n : ℕ) (f : G → ℝ)
    (hf : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (hn : 0 < n) (hiter : (configDiff v)^[n] f = 0) :
    Function.Periodic f v :=
  (configDiff_eq_zero_iff v f).mp (configDiff_eq_zero_of_iterate v n f hf hn hiter)

theorem forwardDiff_eq_configDiff {A : Type uA} [AddCommGroup A] :
    (forwardDiff : (ℤ → A) → ℤ → A) = configDiff (1 : ℤ) := rfl

theorem forwardDiff_eq_zero_of_bounded_iterate (n : ℕ) (f : ℤ → ℝ)
    (hf : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (hn : 0 < n) (hiter : (forwardDiff^[n]) f = 0) : forwardDiff f = 0 := by
  rw [forwardDiff_eq_configDiff] at hiter ⊢
  exact configDiff_eq_zero_of_iterate 1 n f hf hn hiter

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators Classical

namespace PeriodicTilingThree

def componentTarget {G : Type uG} [AddCommGroup G]
    (F : Finset G) (D : Set G) : Set G :=
  {x | tileCount F D x = 1}

private theorem unique_of_nat_sum_one {ι : Type uι} [Fintype ι]
    (c : ι → ℕ) (hc : (∑ i, c i) = 1) : ∃! i, c i = 1 := by
  classical
  have hle (i : ι) : c i ≤ 1 := by
    calc
      c i ≤ ∑ j, c j := Finset.single_le_sum (fun j _ => Nat.zero_le (c j))
        (Finset.mem_univ i)
      _ = 1 := hc
  have hcard : (Finset.univ.filter fun i => c i = 1).card = 1 := by
    calc
      (Finset.univ.filter fun i => c i = 1).card =
          ∑ i, if c i = 1 then (1 : ℕ) else 0 := by simp
      _ = ∑ i, c i := by
        apply Finset.sum_congr rfl
        intro i _
        have hi := hle i
        split_ifs <;> omega
      _ = 1 := hc
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
  have hmem : i ∈ Finset.univ.filter (fun i => c i = 1) := by
    rw [hi]
    exact Finset.mem_singleton_self i
  refine ⟨i, (Finset.mem_filter.mp hmem).2, ?_⟩
  intro j hj
  have hjmem : j ∈ Finset.univ.filter (fun i => c i = 1) := by simp [hj]
  simpa only [hi, Finset.mem_singleton] using hjmem

theorem component_tileCount_sum {G : Type uG} [AddCommGroup G]
    {ι : Type uι} [Fintype ι] {F : Finset G} {A : Set G}
    (parts : ι → Set G) (hTile : Tiles F A)
    (hpartition : ∀ x, (∑ j, tileIndicator ℝ (parts j) x) = tileIndicator ℝ A x)
    (x : G) : (∑ j, tileCount F (parts j) x) = 1 := by
  have hreal : ((∑ j, tileCount F (parts j) x : ℕ) : ℝ) = 1 := by
    rw [Nat.cast_sum]
    simp_rw [tileCount_cast]
    rw [Finset.sum_comm]
    simp_rw [hpartition]
    exact hTile.sum_tileIndicator_eq_one ℝ x
  exact_mod_cast hreal

theorem component_tileCount_le_one {G : Type uG} [AddCommGroup G]
    {ι : Type uι} [Fintype ι] {F : Finset G} {A : Set G}
    (parts : ι → Set G) (hTile : Tiles F A)
    (hpartition : ∀ x, (∑ j, tileIndicator ℝ (parts j) x) = tileIndicator ℝ A x)
    (j : ι) (x : G) : tileCount F (parts j) x ≤ 1 := by
  calc
    tileCount F (parts j) x ≤ ∑ i, tileCount F (parts i) x :=
      Finset.single_le_sum (f := fun i => tileCount F (parts i) x)
        (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    _ = 1 := component_tileCount_sum parts hTile hpartition x

theorem tilesRegion_componentTarget {G : Type uG} [AddCommGroup G]
    (F : Finset G) (D : Set G) (hcount : ∀ x, tileCount F D x ≤ 1) :
    TilesRegion F D (componentTarget F D) := by
  classical
  constructor
  · intro f hf d hd
    change tileCount F D (f + d) = 1
    apply Nat.le_antisymm (hcount (f + d))
    have hterm : tileIndicator ℕ D (f + d - f) = 1 := by
      simp [tileIndicator, hd]
    calc
      1 = tileIndicator ℕ D (f + d - f) := hterm.symm
      _ ≤ tileCount F D (f + d) :=
        Finset.single_le_sum (f := fun g => tileIndicator ℕ D (f + d - g))
          (fun g _ => Nat.zero_le _) hf
  · intro x hx
    change tileCount F D x = 1 at hx
    have hcard : (F.filter fun f => x - f ∈ D).card = 1 := by
      rw [← tileCount_eq_card_filter]
      exact hx
    obtain ⟨f, hf⟩ := Finset.card_eq_one.mp hcard
    have hm : f ∈ F ∧ x - f ∈ D := by
      apply Finset.mem_filter.mp
      rw [hf]
      exact Finset.mem_singleton_self f
    refine ⟨⟨f, hm.1⟩, hm.2, ?_⟩
    intro g hg
    apply Subtype.ext
    have hg' : g.val ∈ F.filter (fun f => x - f ∈ D) :=
      Finset.mem_filter.mpr ⟨g.property, hg⟩
    simpa only [hf, Finset.mem_singleton] using hg'

theorem component_targets_partition {G : Type uG} [AddCommGroup G]
    {ι : Type uι} [Fintype ι] {F : Finset G} {A : Set G}
    (parts : ι → Set G) (hTile : Tiles F A)
    (hpartition : ∀ x, (∑ j, tileIndicator ℝ (parts j) x) = tileIndicator ℝ A x)
    (x : G) : ∃! j, x ∈ componentTarget F (parts j) :=
  unique_of_nat_sum_one (fun j => tileCount F (parts j) x)
    (component_tileCount_sum parts hTile hpartition x)

private theorem real_tileCount_periodic {G : Type uG} [AddCommGroup G]
    (F : Finset G) (D : Set G) (v : G) (hD : Period D v) :
    Function.Periodic (fun x => (tileCount F D x : ℝ)) v := by
  intro x
  change (tileCount F D (x + v) : ℝ) = (tileCount F D x : ℝ)
  rw [tileCount_cast, tileCount_cast]
  apply Finset.sum_congr rfl
  intro f _
  have he : x + v - f = (x - f) + v := by abel
  simp only [tileIndicator, he, hD (x - f)]

private theorem componentTarget_period_of_count {G : Type uG} [AddCommGroup G]
    (F : Finset G) (D : Set G) (v : G)
    (h : Function.Periodic (fun x => (tileCount F D x : ℝ)) v) :
    Period (componentTarget F D) v := by
  intro x
  have he : tileCount F D (x + v) = tileCount F D x := by
    have hreal : (tileCount F D (x + v) : ℝ) = (tileCount F D x : ℝ) := h x
    exact_mod_cast hreal
  change tileCount F D (x + v) = 1 ↔ tileCount F D x = 1
  rw [he]

private theorem bounded_component_periodic {ι : Type uι} [Fintype ι]
    (g : ι → Plane → ℝ) (w : ι → Plane) (j : ι) (e : Plane)
    (hperiod : ∀ i, Function.Periodic (g i) (w i))
    (hsum : (∑ i, g i) = fun _ => (1 : ℝ))
    (hbound : ∃ B : ℝ, ∀ x, |g j x| ≤ B)
    (hother : ∃ i, i ≠ j)
    (hspan : ∀ i, i ≠ j → ∃ a b : ℤ, e = a • w i + b • w j) :
    Function.Periodic (g j) e := by
  classical
  have hchoice : ∀ i, ∃ a b : ℤ, i ≠ j → e = a • w i + b • w j := by
    intro i
    by_cases hij : i = j
    · exact ⟨0, 0, fun h => (h hij).elim⟩
    · obtain ⟨a, b, h⟩ := hspan i hij
      exact ⟨a, b, fun _ => h⟩
  choose a b hab using hchoice
  let vs : List Plane := (Finset.univ.erase j).toList.map (fun i => a i • w i)
  have hmem (i : ι) (hij : i ≠ j) : a i • w i ∈ vs := by
    apply List.mem_map.mpr
    refine ⟨i, ?_, rfl⟩
    simpa only [Finset.mem_toList, Finset.mem_erase, Finset.mem_univ, and_true] using hij
  have hvs : vs ≠ [] := by
    obtain ⟨i, hij⟩ := hother
    intro he
    have h := hmem i hij
    rw [he] at h
    exact List.not_mem_nil h
  have hkill : ∀ i, i ≠ j → ∃ v ∈ vs, Function.Periodic (g i) v := by
    intro i hij
    exact ⟨a i • w i, hmem i hij, (hperiod i).zsmul (a i)⟩
  have hmods : ∀ u ∈ vs, ∃ k : ℤ, u = e + k • w j := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hu
    have hij : i ≠ j := (Finset.mem_erase.mp (Finset.mem_toList.mp hi)).1
    refine ⟨-b i, ?_⟩
    rw [hab i hij, neg_smul]
    abel
  have hzero := configDiffs_component_zero j vs hvs g 1 hsum hkill
  rw [configDiffs_eq_iterate_of_period vs e (w j) (g j) (hperiod j) hmods] at hzero
  exact periodic_of_bounded_configDiff_iterate e vs.length (g j) hbound
    (List.length_pos_iff.mpr hvs) hzero

theorem componentTarget_fullyPeriodic {m : ℕ} {F : Finset Plane} {A : Set Plane}
    (parts : Fin m → Set Plane) (w : Fin m → Plane) (hTile : Tiles F A)
    (hpartition : ∀ x, (∑ j, tileIndicator ℝ (parts j) x) = tileIndicator ℝ A x)
    (hw : ∀ j, w j ≠ 0) (hperiod : ∀ j, Period (parts j) (w j))
    (htrans : ∀ i j, i ≠ j → planeDet (w i) (w j) ≠ 0)
    (j : Fin m) : FullyPeriodic (componentTarget F (parts j)) := by
  classical
  let g : Fin m → Plane → ℝ := fun i x => tileCount F (parts i) x
  have hgperiod : ∀ i, Function.Periodic (g i) (w i) :=
    fun i => real_tileCount_periodic F (parts i) (w i) (hperiod i)
  have hsum : (∑ i, g i) = fun _ => (1 : ℝ) := by
    ext x
    simp only [Finset.sum_apply, g, ← Nat.cast_sum]
    rw [component_tileCount_sum parts hTile hpartition x]
    simp
  have hbound : ∃ B : ℝ, ∀ x, |g j x| ≤ B := by
    refine ⟨1, fun x => ?_⟩
    have hn := component_tileCount_le_one parts hTile hpartition j x
    have hr : (tileCount F (parts j) x : ℝ) ≤ 1 := by exact_mod_cast hn
    change |(tileCount F (parts j) x : ℝ)| ≤ 1
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact hr
  by_cases hother : ∃ i, i ≠ j
  · obtain ⟨e, _he, hdet, hspan⟩ := exists_common_transverse w hw htrans
    have hge : Function.Periodic (g j) e := bounded_component_periodic g w j e
      hgperiod hsum hbound hother (fun i hij => hspan i j hij)
    exact fullyPeriodic_of_independent_periods
      (componentTarget_period_of_count F (parts j) e hge)
      (componentTarget_period_of_count F (parts j) (w j) (hgperiod j)) (hdet j)
  · have hall : ∀ i : Fin m, i = j := by
      intro i
      by_contra hij
      exact hother ⟨i, hij⟩
    have hone : ∀ x, tileCount F (parts j) x = 1 := by
      intro x
      have he := component_tileCount_sum parts hTile hpartition x
      have hs : (∑ i, tileCount F (parts i) x) = tileCount F (parts j) x := by
        apply Finset.sum_eq_single j
        · intro i _ hij
          exact (hij (hall i)).elim
        · intro hj
          exact (hj (Finset.mem_univ j)).elim
      rwa [hs] at he
    have hE : componentTarget F (parts j) = Set.univ := by
      ext x
      simp only [componentTarget, Set.mem_ofPred_eq, hone x, Set.mem_univ]
    rw [hE]
    refine ⟨⊤, ?_, fun v _ x => ?_⟩
    · exact ⟨by simp⟩
    · simp

theorem component_targets {m : ℕ} {F : Finset Plane} {A : Set Plane}
    (parts : Fin m → Set Plane) (w : Fin m → Plane) (hTile : Tiles F A)
    (hpartition : ∀ x, (∑ j, tileIndicator ℝ (parts j) x) = tileIndicator ℝ A x)
    (hw : ∀ j, w j ≠ 0) (hperiod : ∀ j, Period (parts j) (w j))
    (htrans : ∀ i j, i ≠ j → planeDet (w i) (w j) ≠ 0) :
    (∀ j, TilesRegion F (parts j) (componentTarget F (parts j))) ∧
      (∀ x, ∃! j, x ∈ componentTarget F (parts j)) ∧
      ∀ j, FullyPeriodic (componentTarget F (parts j)) := by
  refine ⟨?_, component_targets_partition parts hTile hpartition, ?_⟩
  · intro j
    exact tilesRegion_componentTarget F (parts j)
      (component_tileCount_le_one parts hTile hpartition j)
  · exact componentTarget_fullyPeriodic parts w hTile hpartition hw hperiod htrans

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree.FiniteCylinder

def wrap (i L n : ℤ) : ℤ := i + (n - i) % L

theorem wrap_bounds (i n : ℤ) {L : ℤ} (hL : 0 < L) :
    i ≤ wrap i L n ∧ wrap i L n < i + L := by
  have hnonneg := Int.emod_nonneg (n - i) (ne_of_gt hL)
  have hlt := Int.emod_lt_of_pos (n - i) hL
  dsimp [wrap]
  omega

theorem wrap_eq_self {i L n : ℤ} (hi : i ≤ n) (hn : n < i + L) :
    wrap i L n = n := by
  unfold wrap
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  omega

theorem wrap_add_period (i L n : ℤ) : wrap i L (n + L) = wrap i L n := by
  unfold wrap
  rw [show n + L - i = (n - i) + L by omega]
  simp

theorem wrap_dvd (i L n : ℤ) : L ∣ n - wrap i L n := by
  refine ⟨(n - i) / L, ?_⟩
  have h := Int.emod_add_mul_ediv (n - i) L
  dsimp [wrap]
  omega

theorem wrap_shift (i L n k : ℤ) :
    wrap i L (n + k) = wrap i L (wrap i L n + k) := by
  unfold wrap
  congr 1
  rw [show n + k - i = (n - i) + k by omega,
    show i + (n - i) % L + k - i = (n - i) % L + k by omega]
  exact (Int.emod_add_emod (n - i) L k).symm

theorem window_at_wrap {A : Type uA} (a : ℤ → A) (H : ℕ) (i L : ℤ)
    (hL : (H : ℤ) < L)
    (hrows : ∀ c : Fin H, a (i + (c : ℕ)) = a (i + L + (c : ℕ)))
    (n k : ℤ) (hk0 : 0 ≤ k) (hkH : k ≤ H) :
    a (wrap i L (n + k)) = a (wrap i L n + k) := by
  have hL0 : 0 < L := by omega
  obtain ⟨hb0, hbL⟩ := wrap_bounds i n hL0
  rw [wrap_shift]
  by_cases hcross : wrap i L n + k < i + L
  · exact congrArg a (wrap_eq_self (by omega) hcross)
  · let c : ℤ := wrap i L n + k - (i + L)
    have hc0 : 0 ≤ c := by dsimp [c]; omega
    have hcH : c < H := by dsimp [c]; omega
    have hcL : c < L := by omega
    let cN : Fin H := ⟨c.toNat, by omega⟩
    have hcN : ((cN : ℕ) : ℤ) = c := by dsimp [cN]; omega
    have heq : wrap i L n + k = (i + c) + L := by dsimp [c]; omega
    have h := hrows cN
    rw [hcN] at h
    calc
      a (wrap i L (wrap i L n + k)) = a (wrap i L ((i + c) + L)) :=
        congrArg (fun z => a (wrap i L z)) heq
      _ = a (i + c) := congrArg a
        ((wrap_add_period i L (i + c)).trans (wrap_eq_self (by omega) (by omega)))
      _ = a (i + L + c) := h
      _ = a (wrap i L n + k) := congrArg a (by dsimp [c]; omega)

theorem exists_periodic_windows {A : Type uA} [Fintype A]
    (a : ℤ → A) (q H : ℕ) (hq : 0 < q) :
    ∃ (b : ℤ → A) (L : ℤ), 0 < L ∧ (q : ℤ) ∣ L ∧
      (∀ n : ℤ, b (n + L) = b n) ∧
      (∀ n : ℤ, ∃ t : ℤ, (q : ℤ) ∣ t - n ∧
        ∀ k : ℤ, 0 ≤ k → k ≤ H → b (n + k) = a (t + k)) := by
  classical
  let : NeZero q := ⟨Nat.ne_of_gt hq⟩
  let State := ZMod q × (Fin H → A)
  let time (k : ℕ) : ℤ := (k : ℤ) * ((H : ℤ) + 1)
  let state (k : ℕ) : State :=
    ((time k : ZMod q), fun c => a (time k + (c : ℕ)))
  let N := Fintype.card State
  obtain ⟨x, y, hxy, hs⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Fin (N + 1) => state k.val) (by simp [N])
  have hvals : x.val ≠ y.val := fun h => hxy (Fin.ext h)
  have ordered : ∃ x y : ℕ, x < y ∧ state x = state y := by
    rcases lt_or_gt_of_ne hvals with hlt | hgt
    · exact ⟨x.val, y.val, hlt, hs⟩
    · exact ⟨y.val, x.val, hgt, hs.symm⟩
  obtain ⟨x, y, hxy, hs⟩ := ordered
  let i := time x
  let L := time y - time x
  have hxyZ : (x : ℤ) + 1 ≤ (y : ℤ) := by omega
  have hL : (H : ℤ) < L := by
    dsimp [L, time]
    have hH : (0 : ℤ) ≤ H := by omega
    nlinarith
  have hL0 : 0 < L := by omega
  have hphase : (q : ℤ) ∣ L := by
    have heq : (time x : ZMod q) = (time y : ZMod q) := congrArg Prod.fst hs
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub (time x) (time y) q).mp heq
  have hrows : ∀ c : Fin H, a (i + (c : ℕ)) = a (i + L + (c : ℕ)) := by
    intro c
    have heq := congrFun (congrArg Prod.snd hs) c
    change a (time x + (c : ℕ)) = a (time y + (c : ℕ)) at heq
    have htime : i + L = time y := by dsimp [i, L]; omega
    rw [htime]
    exact heq
  let b : ℤ → A := fun n => a (wrap i L n)
  refine ⟨b, L, hL0, hphase, ?_, ?_⟩
  · intro n
    exact congrArg a (wrap_add_period i L n)
  · intro n
    refine ⟨wrap i L n, ?_, ?_⟩
    · have hd : (q : ℤ) ∣ n - wrap i L n := hphase.trans (wrap_dvd i L n)
      simpa only [neg_sub] using (dvd_neg.mpr hd)
    · intro k hk0 hkH
      exact window_at_wrap a H i L hL hrows n k hk0 hkH

end PeriodicTilingThree.FiniteCylinder

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree

namespace PeriodicRegion

def residue (m : ℕ) (hm : 0 < m) (x : ℤ) : Fin m :=
  ⟨(x % (m : ℤ)).toNat, by
    have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
    have hlo := Int.emod_nonneg x (ne_of_gt hmZ)
    have hhi := Int.emod_lt_of_pos x hmZ
    omega⟩

theorem residue_cast (m : ℕ) (hm : 0 < m) (x : ℤ) :
    ((residue m hm x : ℕ) : ℤ) = x % (m : ℤ) := by
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  have hlo := Int.emod_nonneg x (ne_of_gt hmZ)
  dsimp [residue]
  omega

theorem residue_add (m : ℕ) (hm : 0 < m) (x : ℤ) :
    residue m hm (x + m) = residue m hm x := by
  apply Fin.ext
  simp [residue]

private theorem coordinate_sub (T : Plane ≃+ Plane) (x y : ℤ) (f : Plane) :
    T (x, y) - f = T (x - (T.symm f).1, y - (T.symm f).2) := by
  calc
    T (x, y) - f = T (x, y) - T (T.symm f) := by rw [T.apply_symm_apply]
    _ = T ((x, y) - T.symm f) := (map_sub T (x, y) (T.symm f)).symm
    _ = T (x - (T.symm f).1, y - (T.symm f).2) := rfl

private theorem target_phase {E : Set Plane} (T : Plane ≃+ Plane) (q : ℕ)
    (hE : Period E (T (0, (q : ℤ)))) (x y y' : ℤ)
    (hphase : (q : ℤ) ∣ y' - y) :
    T (x, y') ∈ E ↔ T (x, y) ∈ E := by
  obtain ⟨c, hc⟩ := hphase
  have hv := hE.zsmul c
  have heq : T (x, y) + c • T (0, (q : ℤ)) = T (x, y') := by
    rw [← map_zsmul, ← map_add]
    congr 1
    apply Prod.ext
    · simp
    · simp
      nlinarith
  simpa only [heq] using hv (T (x, y))

end PeriodicRegion

theorem periodic_region_replacement {F : Finset Plane} {D E : Set Plane}
    (htile : TilesRegion F D E)
    (hperiod : ∃ h : Plane, h ≠ 0 ∧ Period D h)
    (htarget : FullyPeriodic E) :
    ∃ D' : Set Plane, TilesRegion F D' E ∧ FullyPeriodic D' := by
  classical
  obtain ⟨h, hh, hD⟩ := hperiod
  obtain ⟨m, hm, T, hT⟩ := exists_primitive_coordinates hh
  have hDcoord : Period D (T ((m : ℤ), 0)) := hT.symm ▸ hD
  obtain ⟨q, hq, hEcoord⟩ := htarget.exists_coordinate_period T
  let row : ℤ → (Fin m → Bool) := fun n r => decide (T ((r : ℕ), n) ∈ D)
  have row_iff (x n : ℤ) :
      row n (PeriodicRegion.residue m hm x) = true ↔ T (x, n) ∈ D := by
    change decide (T (((PeriodicRegion.residue m hm x : ℕ) : ℤ), n) ∈ D) = true ↔
      T (x, n) ∈ D
    rw [decide_eq_true_eq, PeriodicRegion.residue_cast]
    exact (hDcoord.mem_coordinate_mod x n).symm
  let R : ℕ := F.sup (fun f => (T.symm f).2.natAbs)
  have offset_bounds (f : ↥F) :
      0 ≤ (R : ℤ) - (T.symm (f : Plane)).2 ∧
      (R : ℤ) - (T.symm (f : Plane)).2 ≤ (2 * R : ℕ) := by
    have habs : (T.symm (f : Plane)).2.natAbs ≤ R :=
      Finset.le_sup (f := fun f : Plane => (T.symm f).2.natAbs) f.property
    have habsZ : ((T.symm (f : Plane)).2.natAbs : ℤ) ≤ R := by
      exact_mod_cast habs
    have hupper : (T.symm (f : Plane)).2 ≤
        ((T.symm (f : Plane)).2.natAbs : ℤ) := Int.le_natAbs
    have hlower : -(T.symm (f : Plane)).2 ≤
        ((T.symm (f : Plane)).2.natAbs : ℤ) := by
      simpa only [Int.natAbs_neg] using
        (Int.le_natAbs (a := -(T.symm (f : Plane)).2))
    have htwo : ((2 * R : ℕ) : ℤ) = 2 * (R : ℤ) := by simp
    rw [htwo]
    omega
  obtain ⟨b, L, hL, hqL, hbperiod, hwindows⟩ :=
    FiniteCylinder.exists_periodic_windows row q (2 * R) hq
  let D' : Set Plane := {z | b (T.symm z).2
    (PeriodicRegion.residue m hm (T.symm z).1) = true}
  have mem_new (x y : ℤ) :
      T (x, y) ∈ D' ↔ b y (PeriodicRegion.residue m hm x) = true := by
    simp only [D', Set.mem_ofPred_eq, T.symm_apply_apply]
  have htiles : TilesRegion F D' E := by
    apply htile.of_local_copy
    intro z
    obtain ⟨⟨x, y⟩, rfl⟩ := T.surjective z
    obtain ⟨t, htphase, hwindow⟩ := hwindows (y - R)
    refine ⟨T (x, t + R), ?_, ?_⟩
    · apply PeriodicRegion.target_phase T q hEcoord
      have heq : t + (R : ℤ) - y = t - (y - (R : ℤ)) := by omega
      simpa only [heq] using htphase
    · intro f
      obtain ⟨hk0, hkH⟩ := offset_bounds f
      have hrow := hwindow ((R : ℤ) - (T.symm (f : Plane)).2) hk0 hkH
      have hind : y - (R : ℤ) + ((R : ℤ) - (T.symm (f : Plane)).2) =
          y - (T.symm (f : Plane)).2 := by omega
      rw [hind] at hrow
      rw [PeriodicRegion.coordinate_sub T x y f,
        PeriodicRegion.coordinate_sub T x (t + R) f, mem_new, hrow]
      have heq : t + (R : ℤ) - (T.symm (f : Plane)).2 =
          t + ((R : ℤ) - (T.symm (f : Plane)).2) := by omega
      rw [heq]
      exact row_iff (x - (T.symm (f : Plane)).1)
        (t + ((R : ℤ) - (T.symm (f : Plane)).2))
  have hx : Period D' (T ((m : ℤ), 0)) := by
    intro z
    obtain ⟨⟨x, y⟩, rfl⟩ := T.surjective z
    have heq : T (x, y) + T ((m : ℤ), 0) = T (x + m, y) := by
      rw [← map_add]
      change T (x + (m : ℤ), y + 0) = T (x + (m : ℤ), y)
      rw [add_zero]
    rw [heq, mem_new, mem_new, PeriodicRegion.residue_add]
  have hy : Period D' (T (0, L)) := by
    intro z
    obtain ⟨⟨x, y⟩, rfl⟩ := T.surjective z
    have heq : T (x, y) + T (0, L) = T (x, y + L) := by
      rw [← map_add]
      change T (x + 0, y + L) = T (x, y + L)
      rw [add_zero]
    rw [heq, mem_new, mem_new, hbperiod]
  have hLn : 0 < L.toNat := by omega
  have hLcast : (L.toNat : ℤ) = L := by omega
  refine ⟨D', htiles, fullyPeriodic_of_coordinate_periods T m L.toNat hm hLn hx ?_⟩
  simpa only [hLcast] using hy

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace PeriodicTilingThree

open scoped BigOperators Classical

theorem Tiles.image_add {G : Type uG} [AddCommGroup G]
    {F : Finset G} {A : Set G} (h : Tiles F A) (u : G) :
    Tiles (F.image (fun f => f + u)) A := by
  classical
  apply tiles_iff_unique_tile.mpr
  intro x
  obtain ⟨f, hf, huniq⟩ := tiles_iff_unique_tile.mp h (x - u)
  let f' : ↥(F.image (fun f => f + u)) :=
    ⟨(f : G) + u, Finset.mem_image_of_mem _ f.property⟩
  have hsub (g : G) : x - (g + u) = (x - u) - g := by abel
  refine ⟨f', ?_, ?_⟩
  · change x - ((f : G) + u) ∈ A
    rwa [hsub]
  · intro g hg
    obtain ⟨z, hz, hzg⟩ := Finset.mem_image.mp g.property
    have hzA : (x - u) - z ∈ A := by
      rw [← hsub, hzg]
      exact hg
    have hzf : (⟨z, hz⟩ : ↥F) = f := huniq ⟨z, hz⟩ hzA
    apply Subtype.ext
    change (g : G) = (f : G) + u
    have hzf' : z = (f : G) := congrArg Subtype.val hzf
    rw [← hzg, hzf']

theorem fullyPeriodic_finite_union {G : Type uG} {ι : Type uι} [AddCommGroup G] [Finite ι]
    (parts : ι → Set G) (hp : ∀ i, FullyPeriodic (parts i)) :
    FullyPeriodic {x | ∃ i, x ∈ parts i} := by
  classical
  choose P hindex hperiod using hp
  let common : AddSubgroup G := ⨅ i, P i
  refine ⟨common, AddSubgroup.finiteIndex_iInf hindex, ?_⟩
  intro v hv x
  have hv' (i : ι) : v ∈ P i := (AddSubgroup.mem_iInf.mp hv) i
  change (∃ i, x + v ∈ parts i) ↔ ∃ i, x ∈ parts i
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (hperiod i v (hv' i) x).mp hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (hperiod i v (hv' i) x).mpr hi⟩

theorem tiles_union_of_region_partition {G : Type uG} {ι : Type uι} [AddCommGroup G]
    (F : Finset G) (parts targets : ι → Set G)
    (htile : ∀ i, TilesRegion F (parts i) (targets i))
    (hcover : ∀ x, ∃! i, x ∈ targets i) :
    Tiles F {x | ∃ i, x ∈ parts i} := by
  apply tiles_iff_unique_tile.mpr
  intro x
  obtain ⟨i, hi, huniq⟩ := hcover x
  obtain ⟨f, hf, hfuniq⟩ := (htile i).unique x hi
  refine ⟨f, ⟨i, hf⟩, ?_⟩
  rintro g ⟨j, hj⟩
  have hxj : x ∈ targets j := by
    simpa [add_comm] using (htile j).add_mem g g.property (x - g) hj
  have hji : j = i := huniq j hxj
  subst j
  exact hfuniq g hj

theorem Tiles.fullyPeriodic_of_finite_periodic_partition
    {ι : Type uι} [Fintype ι] {F : Finset Plane} {A : Set Plane}
    (h : Tiles F A) (parts : ι → Set Plane) (v : ι → Plane)
    (hpartition : ∀ x, (∑ i, tileIndicator ℝ (parts i) x) = tileIndicator ℝ A x)
    (hv : ∀ i, v i ≠ 0) (hperiod : ∀ i, Period (parts i) (v i)) :
    ∃ B : Set Plane, Tiles F B ∧ FullyPeriodic B := by
  classical
  obtain ⟨m, w, grouped, hw, htrans, hsum, hp⟩ :=
    exists_grouped_periodic_parts parts v hv hperiod hpartition
  obtain ⟨htiles, hcover, htargets⟩ := component_targets grouped w h hsum hw hp htrans
  have hex (j : Fin m) : ∃ B : Set Plane,
      TilesRegion F B (componentTarget F (grouped j)) ∧ FullyPeriodic B :=
    periodic_region_replacement (htiles j) ⟨w j, hw j, hp j⟩ (htargets j)
  choose replacements hregion hfull using hex
  refine ⟨{x | ∃ j, x ∈ replacements j}, ?_, ?_⟩
  · exact tiles_union_of_region_partition F replacements
      (fun j => componentTarget F (grouped j)) hregion hcover
  · exact fullyPeriodic_finite_union replacements hfull

theorem plane_tile_has_fullyPeriodic_complement
    (F : Finset Plane) (hF : F.Nonempty)
    (h : ∃ A : Set Plane, Tiles F A) :
    ∃ B : Set Plane, Tiles F B ∧ FullyPeriodic B := by
  classical
  obtain ⟨A, hA⟩ := h
  obtain ⟨f, hf⟩ := hF
  let : DecidableEq Plane := fun a b => Classical.propDecidable (a = b)
  let F₀ := F.image (fun x => x + -f)
  have hzero : (0 : Plane) ∈ F₀ := by
    apply Finset.mem_image.mpr
    exact ⟨f, hf, add_neg_cancel f⟩
  have hA₀ : Tiles F₀ A := hA.image_add (-f)
  obtain ⟨m, parts, v, hpartition, hv, hp⟩ := hA₀.exists_weak_periodic_partition hzero
  obtain ⟨B, hB, hfull⟩ :=
    hA₀.fullyPeriodic_of_finite_periodic_partition parts v hpartition hv hp
  refine ⟨B, ?_, hfull⟩
  have hback := hB.image_add f
  simpa only [F₀, Finset.image_image, Function.comp_def, add_assoc,
    neg_add_cancel, add_zero, Finset.image_id'] using hback

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree

theorem lattice_two_tile_has_fullyPeriodic_complement
    (F : Finset (Lattice 2)) (h : ∃ A, Tiles F A) :
    ∃ B, Tiles F B ∧ FullyPeriodic B := by
  classical
  obtain ⟨A, hA⟩ := h
  have hPlane := hA.preimage_addEquiv planeEquiv
  obtain ⟨B, hB, hPeriod⟩ := plane_tile_has_fullyPeriodic_complement
    (F.image planeEquiv.symm) hPlane.tile_nonempty ⟨_, hPlane⟩
  refine ⟨planeEquiv '' B, ?_, (fullyPeriodic_image_addEquiv_iff planeEquiv).mpr hPeriod⟩
  have hImage := hB.image_addEquiv planeEquiv
  simpa only [Finset.image_image, Function.comp_def, planeEquiv.apply_symm_apply,
    Finset.image_id'] using hImage

theorem tiles_below_three_have_fullyPeriodic_complements
    (d : ℕ) (hd : d < 3) (F : Finset (Lattice d)) (h : ∃ A, Tiles F A) :
    ∃ B, Tiles F B ∧ FullyPeriodic B := by
  cases d with
  | zero => exact lattice_zero_tile_has_fullyPeriodic_complement F h
  | succ d =>
      cases d with
      | zero => exact lattice_one_tile_has_fullyPeriodic_complement F h
      | succ d =>
          cases d with
          | zero => exact lattice_two_tile_has_fullyPeriodic_complement F h
          | succ d => omega

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

structure LabeledBlocks (K : Type uK) (A : Type uA) (B : Type uB) (a b : ℕ) where
  decode : K ≃ ((A × ZMod a) ⊕ (B × ZMod b))

namespace LabeledBlocks

variable {K : Type uK} {A : Type uA} {B : Type uB} {a b : ℕ}

def labelRotation (t : ℤ) : Equiv.Perm ((A × ZMod a) ⊕ (B × ZMod b)) where
  toFun
    | .inl (c, y) => .inl (c, y + (t : ZMod a))
    | .inr (c, y) => .inr (c, y + (t : ZMod b))
  invFun
    | .inl (c, y) => .inl (c, y - (t : ZMod a))
    | .inr (c, y) => .inr (c, y - (t : ZMod b))
  left_inv := by rintro (⟨c, y⟩ | ⟨c, y⟩) <;> simp
  right_inv := by rintro (⟨c, y⟩ | ⟨c, y⟩) <;> simp

def C (D : LabeledBlocks K A B a b) (x : K) : ZMod a × ZMod b :=
  match D.decode x with
  | .inl (_, y) => (y, 0)
  | .inr (_, y) => (0, y)

def T (D : LabeledBlocks K A B a b) (t : ℤ) : Equiv.Perm K :=
  D.decode.trans ((labelRotation t).trans D.decode.symm)

def blockId (D : LabeledBlocks K A B a b) (x : K) : A ⊕ B :=
  match D.decode x with
  | .inl (c, _) => .inl c
  | .inr (c, _) => .inr c

def block (D : LabeledBlocks K A B a b) (c : A ⊕ B) : Set K :=
  {x | D.blockId x = c}

theorem unique_block (D : LabeledBlocks K A B a b) (x : K) :
    ∃! c : A ⊕ B, x ∈ D.block c := by
  exact ⟨D.blockId x, rfl, fun c hc => hc.symm⟩

noncomputable def blockEquivA (D : LabeledBlocks K A B a b) (c : A) :
    {x : K // x ∈ D.block (.inl c)} ≃ ZMod a :=
  (Equiv.ofBijective
    (fun y : ZMod a => (⟨D.decode.symm (.inl (c, y)), by simp [block, blockId]⟩ :
      {x : K // x ∈ D.block (.inl c)}))
    (by
      constructor
      · intro y z h
        have hh := congrArg (fun x => D.decode x.val) h
        simpa using hh
      · rintro ⟨x, hx⟩
        cases h : D.decode x with
        | inl z =>
            have hz : z.1 = c := by simpa [block, blockId, h] using hx
            refine ⟨z.2, Subtype.ext ?_⟩
            apply D.decode.injective
            rw [Equiv.apply_symm_apply, h]
            exact congrArg Sum.inl (Prod.ext hz.symm rfl)
        | inr z => simp [block, blockId, h] at hx)).symm

noncomputable def blockEquivB (D : LabeledBlocks K A B a b) (c : B) :
    {x : K // x ∈ D.block (.inr c)} ≃ ZMod b :=
  (Equiv.ofBijective
    (fun y : ZMod b => (⟨D.decode.symm (.inr (c, y)), by simp [block, blockId]⟩ :
      {x : K // x ∈ D.block (.inr c)}))
    (by
      constructor
      · intro y z h
        have hh := congrArg (fun x => D.decode x.val) h
        simpa using hh
      · rintro ⟨x, hx⟩
        cases h : D.decode x with
        | inl z => simp [block, blockId, h] at hx
        | inr z =>
            have hz : z.1 = c := by simpa [block, blockId, h] using hx
            refine ⟨z.2, Subtype.ext ?_⟩
            apply D.decode.injective
            rw [Equiv.apply_symm_apply, h]
            exact congrArg Sum.inr (Prod.ext hz.symm rfl))).symm

@[simp] theorem C_decode_symm_inl (D : LabeledBlocks K A B a b)
    (c : A) (y : ZMod a) : D.C (D.decode.symm (.inl (c, y))) = (y, 0) := by
  simp [C]

@[simp] theorem C_decode_symm_inr (D : LabeledBlocks K A B a b)
    (c : B) (y : ZMod b) : D.C (D.decode.symm (.inr (c, y))) = (0, y) := by
  simp [C]

@[simp] theorem decode_T (D : LabeledBlocks K A B a b) (t : ℤ) (x : K) :
    D.decode (D.T t x) = labelRotation t (D.decode x) := by
  simp [T]

@[simp] theorem T_decode_symm_inl (D : LabeledBlocks K A B a b)
    (t : ℤ) (c : A) (y : ZMod a) :
    D.T t (D.decode.symm (.inl (c, y))) =
      D.decode.symm (.inl (c, y + (t : ZMod a))) := by
  simp [T, labelRotation]

@[simp] theorem T_decode_symm_inr (D : LabeledBlocks K A B a b)
    (t : ℤ) (c : B) (y : ZMod b) :
    D.T t (D.decode.symm (.inr (c, y))) =
      D.decode.symm (.inr (c, y + (t : ZMod b))) := by
  simp [T, labelRotation]

@[simp] theorem blockId_T (D : LabeledBlocks K A B a b) (t : ℤ) (x : K) :
    D.blockId (D.T t x) = D.blockId x := by
  unfold blockId
  rw [decode_T]
  cases D.decode x <;> rfl

@[simp] theorem T_zero (D : LabeledBlocks K A B a b) (x : K) : D.T 0 x = x := by
  apply D.decode.injective
  rw [decode_T]
  cases h : D.decode x with
  | inl z => simp [labelRotation]
  | inr z => simp [labelRotation]

theorem T_add (D : LabeledBlocks K A B a b) (t u : ℤ) (x : K) :
    D.T (t + u) x = D.T t (D.T u x) := by
  apply D.decode.injective
  simp only [decode_T]
  cases h : D.decode x with
  | inl z => simp [labelRotation, add_comm, add_left_comm]
  | inr z => simp [labelRotation, add_comm, add_left_comm]

@[simp] theorem T_neg_T (D : LabeledBlocks K A B a b) (t : ℤ) (x : K) :
    D.T (-t) (D.T t x) = x := by
  rw [← T_add]
  simp

@[simp] theorem T_T_neg (D : LabeledBlocks K A B a b) (t : ℤ) (x : K) :
    D.T t (D.T (-t) x) = x := by
  rw [← T_add]
  simp

def transport {L : Type uL} (D : LabeledBlocks K A B a b) (e : L ≃ K) :
    LabeledBlocks L A B a b := ⟨e.trans D.decode⟩

@[simp] theorem C_transport {L : Type uL} (D : LabeledBlocks K A B a b)
    (e : L ≃ K) (x : L) : (D.transport e).C x = D.C (e x) := rfl

def copyRight (D : LabeledBlocks K A B a b) (R : Type uR) :
    LabeledBlocks (K × R) (A × R) (B × R) a b where
  decode :=
    { toFun := fun x => match D.decode x.1 with
        | .inl (c, y) => .inl ((c, x.2), y)
        | .inr (c, y) => .inr ((c, x.2), y)
      invFun := fun x => match x with
        | .inl ((c, r), y) => (D.decode.symm (.inl (c, y)), r)
        | .inr ((c, r), y) => (D.decode.symm (.inr (c, y)), r)
      left_inv := by
        rintro ⟨x, r⟩
        cases h : D.decode x with
        | inl z => simpa [h] using congrArg (fun w => (w, r)) (D.decode.symm_apply_apply x)
        | inr z => simpa [h] using congrArg (fun w => (w, r)) (D.decode.symm_apply_apply x)
      right_inv := by
        rintro (⟨⟨c, r⟩, y⟩ | ⟨⟨c, r⟩, y⟩) <;> simp }

@[simp] theorem C_copyRight (D : LabeledBlocks K A B a b) (R : Type uR) (x : K × R) :
    (D.copyRight R).C x = D.C x.1 := by
  rcases x with ⟨x, r⟩
  cases h : D.decode x <;> simp [C, copyRight, h]

@[simp] theorem T_copyRight (D : LabeledBlocks K A B a b) (R : Type uR) (t : ℤ)
    (x : K × R) : (D.copyRight R).T t x = (D.T t x.1, x.2) := by
  rcases x with ⟨x, r⟩
  cases h : D.decode x with
  | inl z => simp [T, copyRight, labelRotation, h]
  | inr z => simp [T, copyRight, labelRotation, h]

noncomputable def digit (a b r A B : ℕ) [NeZero a] [NeZero b] [NeZero r]
    (h : r = A * a + B * b) : LabeledBlocks (ZMod r) (Fin A) (Fin B) a b where
  decode := Fintype.equivOfCardEq (by
    simp only [ZMod.card, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    exact h)

theorem C_nonconstant (D : LabeledBlocks K A B a b) [Nonempty K]
    [Nontrivial (ZMod a)] [Nontrivial (ZMod b)] :
    ∃ x y : K, D.C x ≠ D.C y := by
  obtain ⟨x⟩ := ‹Nonempty K›
  cases h : D.decode x with
  | inl z =>
      refine ⟨D.decode.symm (.inl (z.1, 0)), D.decode.symm (.inl (z.1, 1)), ?_⟩
      rw [C_decode_symm_inl, C_decode_symm_inl]
      intro he
      exact zero_ne_one (congrArg Prod.fst he)
  | inr z =>
      refine ⟨D.decode.symm (.inr (z.1, 0)), D.decode.symm (.inr (z.1, 1)), ?_⟩
      rw [C_decode_symm_inr, C_decode_symm_inr]
      intro he
      exact zero_ne_one (congrArg Prod.snd he)

section Coordinate

variable {J : Type uJ} [DecidableEq J] (F : J → Type uF) (j : J)
variable {a b : ℕ} {A : Type uA} {B : Type uB}

def onCoordinate (D : LabeledBlocks (F j) A B a b) :
    LabeledBlocks (∀ q, F q)
      (A × (∀ q : {q // q ≠ j}, F q))
      (B × (∀ q : {q // q ≠ j}, F q)) a b :=
  (D.copyRight (∀ q : {q // q ≠ j}, F q)).transport (Equiv.piSplitAt j F)

@[simp] theorem C_onCoordinate (D : LabeledBlocks (F j) A B a b) (x : ∀ q, F q) :
    (onCoordinate F j D).C x = D.C (x j) := by
  simp [onCoordinate]

theorem C_eq_of_coordinate_eq (D : LabeledBlocks (F j) A B a b)
    {x y : ∀ q, F q} (h : x j = y j) :
    (onCoordinate F j D).C x = (onCoordinate F j D).C y := by
  simp only [C_onCoordinate, h]

theorem C_designated_witness (D : LabeledBlocks (F j) A B a b)
    [∀ q, Nonempty (F q)] [Nontrivial (ZMod a)] [Nontrivial (ZMod b)] :
    ∃ x y : ∀ q, F q, (∀ q, q ≠ j → x q = y q) ∧
      (onCoordinate F j D).C x ≠ (onCoordinate F j D).C y := by
  classical
  obtain ⟨u, v, huv⟩ := D.C_nonconstant
  let base : ∀ q, F q := fun q => Classical.choice (inferInstance : Nonempty (F q))
  refine ⟨Function.update base j u, Function.update base j v, ?_, ?_⟩
  · intro q hq
    simp [Function.update_of_ne hq]
  · simpa only [C_onCoordinate, Function.update_self] using huv

theorem C_active_iff (D : LabeledBlocks (F j) A B a b)
    [∀ q, Nonempty (F q)] [Nontrivial (ZMod a)] [Nontrivial (ZMod b)] (q : J) :
    (∃ x y : ∀ r, F r, (∀ r, r ≠ q → x r = y r) ∧
      (onCoordinate F j D).C x ≠ (onCoordinate F j D).C y) ↔ q = j := by
  constructor
  · rintro ⟨x, y, hxy, hne⟩
    by_contra hq
    exact hne (C_eq_of_coordinate_eq F j D (hxy j (Ne.symm hq)))
  · intro hq
    subst q
    exact C_designated_witness F j D

end Coordinate

end LabeledBlocks

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree

abbrev Column (p : ℕ) := Fin (p ^ 2)
abbrev Symbol (p : ℕ) := (ZMod p)ˣ
abbrev Word (p : ℕ) := Column p → Symbol p
abbrev WordArray (p : ℕ) := Column p → ℤ → Symbol p
abbrev Channel (p : ℕ) := Column p ⊕ Fin 2

def Label (p : ℕ) : Channel p → Type
  | .inl _ => Symbol p
  | .inr _ => Unit

instance instFintypeLabel (p : ℕ) [NeZero p] (i : Channel p) : Fintype (Label p i) := by
  cases i <;> dsimp [Label] <;> infer_instance

instance instDecidableEqLabel (p : ℕ) (i : Channel p) : DecidableEq (Label p i) := by
  cases i <;> dsimp [Label] <;> infer_instance

instance instInhabitedLabel (p : ℕ) (i : Channel p) : Inhabited (Label p i) := by
  cases i <;> dsimp [Label] <;> infer_instance

def Allowed (p : ℕ) (w : Word p) : Prop :=
  ∃ a b : ℤ,
    (¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ b) ∧
    ∀ n : Column p,
      let t := a * (n.val : ℤ) + b
      (¬ (p : ℤ) ∣ t → (w n : ZMod p) = (t : ZMod p)) ∧
      ((p : ℤ) ∣ t → ¬ (p : ℤ) ^ 2 ∣ t →
        (w n : ZMod p) = ((t / (p : ℤ) : ℤ) : ZMod p))

def LineRule (p : ℕ) (W : WordArray p) : Prop :=
  ∀ d e : ℤ, Allowed p (fun n => W n (d * (n.val : ℤ) + e))

def NonconstantColumns {p : ℕ} (W : WordArray p) : Prop :=
  ∀ n, ∃ m m' : ℤ, W n m ≠ W n m'

def VerticalPeriod {p : ℕ} (W : WordArray p) (M : ℤ) : Prop :=
  ∀ n m, W n (m + M) = W n m

def affineValue {p : ℕ} (A B C : ZMod p) (n : Column p) (m : ℤ) : ZMod p :=
  A * (n.val : ZMod p) + B * (m : ZMod p) + C

def AffineApproximation {p : ℕ} (W : WordArray p) (A B C : ZMod p) : Prop :=
  (A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) ∧
  ∀ n m, affineValue A B C n m ≠ 0 →
    (W n m : ZMod p) = affineValue A B C n m

def lineValue {p : ℕ} (n : Column p) (x : Plane) : ℤ :=
  x.2 + (n.val : ℤ) * x.1

def lineKernelStep {p : ℕ} (n : Column p) : Plane :=
  (1, -(n.val : ℤ))

@[simp] theorem lineValue_vertical {p : ℕ} (n : Column p) (m : ℤ) :
    lineValue n (0, m) = m := by
  simp [lineValue]

noncomputable def allowedWords (p : ℕ) [NeZero p] : Finset (Word p) := by
  classical
  exact Finset.univ.filter (Allowed p)

@[simp] theorem mem_allowedWords {p : ℕ} [NeZero p] (w : Word p) :
    w ∈ allowedWords p ↔ Allowed p w := by
  classical
  simp [allowedWords]

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree

open scoped BigOperators

abbrev PrimeTag (p : ℕ) :=
  Channel p ⊕ (Channel p ⊕ (Σ i : Channel p, Label p i))

structure EncodingParameters (p : ℕ) where
  p_prime : Nat.Prime p
  p_large : 200 < p
  primeAt : PrimeTag p → ℕ
  prime_isPrime : ∀ t, Nat.Prime (primeAt t)
  prime_injective : Function.Injective primeAt
  prime_ne_p : ∀ t, primeAt t ≠ p
  seed_a_eq : ∀ t : Fin 2, primeAt (.inl (.inr t)) = t.val + 2
  seed_b_large : ∀ t : Fin 2, p ^ 4 < primeAt (.inr (.inl (.inr t)))
  blockA : ∀ i : Channel p, Label p i → ℕ
  blockB : ∀ i : Channel p, Label p i → ℕ
  blockA_pos : ∀ i j, 0 < blockA i j
  blockB_pos : ∀ i j, 0 < blockB i j
  digit_representation : ∀ i j,
    primeAt (.inr (.inr ⟨i, j⟩)) =
      blockA i j * primeAt (.inl i) + blockB i j * primeAt (.inr (.inl i))

namespace EncodingParameters

variable {p : ℕ} (E : EncodingParameters p)

def a (i : Channel p) : ℕ := E.primeAt (.inl i)
def b (i : Channel p) : ℕ := E.primeAt (.inr (.inl i))
def digitPrime (i : Channel p) (j : Label p i) : ℕ :=
  E.primeAt (.inr (.inr ⟨i, j⟩))

theorem a_prime (i : Channel p) : Nat.Prime (E.a i) := E.prime_isPrime _
theorem b_prime (i : Channel p) : Nat.Prime (E.b i) := E.prime_isPrime _
theorem digitPrime_prime (i : Channel p) (j : Label p i) :
    Nat.Prime (E.digitPrime i j) := E.prime_isPrime _

theorem a_pos (i : Channel p) : 0 < E.a i := (E.a_prime i).pos
theorem b_pos (i : Channel p) : 0 < E.b i := (E.b_prime i).pos
theorem digitPrime_pos (i : Channel p) (j : Label p i) :
    0 < E.digitPrime i j := (E.digitPrime_prime i j).pos

theorem a_two_le (i : Channel p) : 2 ≤ E.a i := (E.a_prime i).two_le
theorem b_two_le (i : Channel p) : 2 ≤ E.b i := (E.b_prime i).two_le

theorem seed_a (t : Fin 2) : E.a (.inr t) = t.val + 2 := E.seed_a_eq t

theorem digit_eq (i : Channel p) (j : Label p i) :
    E.digitPrime i j = E.blockA i j * E.a i + E.blockB i j * E.b i :=
  E.digit_representation i j

theorem prime_coprime {s t : PrimeTag p} (hst : s ≠ t) :
    Nat.Coprime (E.primeAt s) (E.primeAt t) :=
  (Nat.coprime_primes (E.prime_isPrime s) (E.prime_isPrime t)).2
    (fun h => hst (E.prime_injective h))

theorem prime_coprime_p (t : PrimeTag p) : Nat.Coprime (E.primeAt t) p :=
  (Nat.coprime_primes (E.prime_isPrime t) E.p_prime).2 (E.prime_ne_p t)

theorem a_coprime_b (i : Channel p) : Nat.Coprime (E.a i) (E.b i) := by
  apply E.prime_coprime
  simp

theorem digitPrime_pairwise (i : Channel p) :
    Pairwise (fun j j' : Label p i => Nat.Coprime (E.digitPrime i j) (E.digitPrime i j')) := by
  intro j j' hj
  apply E.prime_coprime
  intro he
  exact hj (by simpa using he)

section Finite

variable [NeZero p]

def r (i : Channel p) : ℕ := ∏ j : Label p i, E.digitPrime i j

theorem r_pos (i : Channel p) : 0 < E.r i := by
  exact Finset.prod_pos (fun j _ => E.digitPrime_pos i j)

instance a_neZero (i : Channel p) : NeZero (E.a i) := ⟨(E.a_pos i).ne'⟩
instance b_neZero (i : Channel p) : NeZero (E.b i) := ⟨(E.b_pos i).ne'⟩
instance digitPrime_neZero (i : Channel p) (j : Label p i) :
    NeZero (E.digitPrime i j) := ⟨(E.digitPrime_pos i j).ne'⟩
instance r_neZero (i : Channel p) : NeZero (E.r i) := ⟨(E.r_pos i).ne'⟩

theorem r_coprime_a (i j : Channel p) : Nat.Coprime (E.r i) (E.a j) := by
  apply Nat.coprime_fintype_prod_left_iff.mpr
  intro k
  apply E.prime_coprime
  simp

theorem r_coprime_b (i j : Channel p) : Nat.Coprime (E.r i) (E.b j) := by
  apply Nat.coprime_fintype_prod_left_iff.mpr
  intro k
  apply E.prime_coprime
  simp

theorem r_coprime_p (i : Channel p) : Nat.Coprime (E.r i) p := by
  apply Nat.coprime_fintype_prod_left_iff.mpr
  intro k
  exact E.prime_coprime_p _

theorem r_pairwise_coprime : Pairwise (fun i j : Channel p => Nat.Coprime (E.r i) (E.r j)) := by
  intro i j hij
  apply Nat.coprime_fintype_prod_left_iff.mpr
  intro k
  apply Nat.coprime_fintype_prod_right_iff.mpr
  intro l
  apply E.prime_coprime
  intro he
  have hs : (⟨i, k⟩ : Σ i : Channel p, Label p i) = ⟨j, l⟩ :=
    Sum.inr.inj (Sum.inr.inj he)
  exact hij (congrArg Sigma.fst hs)

end Finite
end EncodingParameters
end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

open scoped BigOperators

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

def digitEquivRing (i : Channel p) :
    ZMod (E.r i) ≃+* (∀ j : Label p i, ZMod (E.digitPrime i j)) :=
  ZMod.prodEquivPi (E.digitPrime i) (E.digitPrime_pairwise i)

def digitEquiv (i : Channel p) :
    ZMod (E.r i) ≃+ (∀ j : Label p i, ZMod (E.digitPrime i j)) :=
  (digitEquivRing E i).toAddEquiv

theorem digitPrime_dvd_r (i : Channel p) (j : Label p i) :
    E.digitPrime i j ∣ E.r i :=
  Finset.dvd_prod_of_mem (E.digitPrime i) (Finset.mem_univ j)

@[simp] theorem digitEquiv_intCast (i : Channel p) (z : ℤ) (j : Label p i) :
    digitEquiv E i (z : ZMod (E.r i)) j = (z : ZMod (E.digitPrime i j)) := by
  exact congrArg (fun f : ∀ j : Label p i, ZMod (E.digitPrime i j) => f j)
    (map_intCast (digitEquivRing E i) z)

theorem digitEquiv_apply (i : Channel p) (x : ZMod (E.r i)) (j : Label p i) :
    digitEquiv E i x j = (ZMod.cast x : ZMod (E.digitPrime i j)) := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  rw [digitEquiv_intCast, ZMod.cast_intCast (digitPrime_dvd_r E i j)]

def digitSubgroup (i : Channel p) (j : Label p i) : AddSubgroup (ZMod (E.r i)) where
  carrier := {x | ∀ k : Label p i, k ≠ j → digitEquiv E i x k = 0}
  zero_mem' := by
    intro k _hk
    simp
  add_mem' := by
    intro x y hx hy k hk
    simp [map_add, hx k hk, hy k hk]
  neg_mem' := by
    intro x hx k hk
    simp [map_neg, hx k hk]

@[simp] theorem mem_digitSubgroup (i : Channel p) (j : Label p i) (x : ZMod (E.r i)) :
    x ∈ digitSubgroup E i j ↔
      ∀ k : Label p i, k ≠ j → digitEquiv E i x k = 0 := Iff.rfl

theorem sub_mem_digitSubgroup_iff (i : Channel p) (j : Label p i)
    (x y : ZMod (E.r i)) :
    x - y ∈ digitSubgroup E i j ↔
      ∀ k : Label p i, k ≠ j → digitEquiv E i x k = digitEquiv E i y k := by
  simp [mem_digitSubgroup, map_sub, sub_eq_zero]

def digitSingle (i : Channel p) (j : Label p i) (x : ZMod (E.digitPrime i j)) :
    ZMod (E.r i) :=
  (digitEquiv E i).symm (Pi.single j x)

@[simp] theorem digitEquiv_digitSingle (i : Channel p) (j : Label p i)
    (x : ZMod (E.digitPrime i j)) :
    digitEquiv E i (digitSingle E i j x) = Pi.single j x :=
  (digitEquiv E i).apply_symm_apply _

theorem digitSingle_mem (i : Channel p) (j : Label p i)
    (x : ZMod (E.digitPrime i j)) : digitSingle E i j x ∈ digitSubgroup E i j := by
  intro k hk
  rw [digitEquiv_digitSingle]
  exact Pi.single_eq_of_ne (M := fun j : Label p i => ZMod (E.digitPrime i j)) hk x

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace PeriodicTilingThree

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

abbrev ChannelOtherDigits (i : Channel p) (j : Label p i) :=
  ∀ q : {q : Label p i // q ≠ j}, ZMod (E.digitPrime i q)

abbrev ChannelBlockA (i : Channel p) (j : Label p i) :=
  Fin (E.blockA i j) × ChannelOtherDigits E i j

abbrev ChannelBlockB (i : Channel p) (j : Label p i) :=
  Fin (E.blockB i j) × ChannelOtherDigits E i j

def channelDigitBase (i : Channel p) (j : Label p i) :
    LabeledBlocks (ZMod (E.digitPrime i j)) (Fin (E.blockA i j))
      (Fin (E.blockB i j)) (E.a i) (E.b i) :=
  LabeledBlocks.digit (E.a i) (E.b i) (E.digitPrime i j)
    (E.blockA i j) (E.blockB i j) (E.digit_eq i j)

def channelDigitBlocks (i : Channel p) (j : Label p i) :
    LabeledBlocks (ZMod (E.r i)) (ChannelBlockA E i j)
      (ChannelBlockB E i j) (E.a i) (E.b i) :=
  (LabeledBlocks.onCoordinate (fun q => ZMod (E.digitPrime i q)) j
    (channelDigitBase E i j)).transport (digitEquiv E i).toEquiv

@[simp] theorem channelDigitBlocks_C (i : Channel p) (j : Label p i)
    (w : ZMod (E.r i)) :
    (channelDigitBlocks E i j).C w =
      (channelDigitBase E i j).C (digitEquiv E i w j) := by
  simp [channelDigitBlocks]

theorem channelDigitBlocks_C_eq (i : Channel p) (j : Label p i)
    {w w' : ZMod (E.r i)} (h : digitEquiv E i w j = digitEquiv E i w' j) :
    (channelDigitBlocks E i j).C w = (channelDigitBlocks E i j).C w' := by
  simp only [channelDigitBlocks_C, h]

theorem channelDigitBlocks_active_iff (i : Channel p) (j q : Label p i) :
    (∃ w w' : ZMod (E.r i), w - w' ∈ digitSubgroup E i q ∧
      (channelDigitBlocks E i j).C w ≠ (channelDigitBlocks E i j).C w') ↔ q = j := by
  constructor
  · rintro ⟨w, w', hdiff, hne⟩
    by_contra hq
    apply hne
    exact channelDigitBlocks_C_eq E i j
      ((sub_mem_digitSubgroup_iff E i q w w').1 hdiff j (Ne.symm hq))
  · intro hq
    subst q
    let : Fact (1 < E.a i) := ⟨(E.a_prime i).one_lt⟩
    let : Fact (1 < E.b i) := ⟨(E.b_prime i).one_lt⟩
    obtain ⟨x, y, hxy, hne⟩ :=
      LabeledBlocks.C_designated_witness (fun q => ZMod (E.digitPrime i q)) j
        (channelDigitBase E i j)
    refine ⟨(digitEquiv E i).symm x, (digitEquiv E i).symm y, ?_, ?_⟩
    · apply (sub_mem_digitSubgroup_iff E i j _ _).2
      simpa only [AddEquiv.apply_symm_apply] using hxy
    · simpa only [channelDigitBlocks_C, AddEquiv.apply_symm_apply,
        LabeledBlocks.C_onCoordinate] using hne

namespace LabeledBlocks

def castSizes {K : Type uK} {A : Type uA} {B : Type uB} {a b a' b' : ℕ}
    (D : LabeledBlocks K A B a b)
    (ha : a = a') (hb : b = b') : LabeledBlocks K A B a' b' := by
  subst a'
  subst b'
  exact D

@[simp] theorem T_transport_apply {K : Type uK} {L : Type uL} {A : Type uA} {B : Type uB} {a b : ℕ}
    (D : LabeledBlocks K A B a b) (e : L ≃ K) (t : ℤ) (x : L) :
    (D.transport e).T t x = e.symm (D.T t (e x)) := rfl

theorem T_onCoordinate {J : Type uJ} [DecidableEq J] (F : J → Type uF) (j : J)
    {A : Type uA} {B : Type uB} {a b : ℕ} (D : LabeledBlocks (F j) A B a b) (t : ℤ) (x : ∀ q, F q) :
    (onCoordinate F j D).T t x =
      (Equiv.piSplitAt j F).symm (D.T t (x j), fun q => x q) := by
  rw [onCoordinate, T_transport_apply, T_copyRight]
  rfl

theorem T_onCoordinate_other {J : Type uJ} [DecidableEq J] (F : J → Type uF) (j : J)
    {A : Type uA} {B : Type uB} {a b : ℕ} (D : LabeledBlocks (F j) A B a b) (t : ℤ)
    (x : ∀ q, F q) (q : J) (hq : q ≠ j) :
    (onCoordinate F j D).T t x q = x q := by
  rw [T_onCoordinate]
  simp [Equiv.piSplitAt, hq]

theorem T_onCoordinate_transport_other {J : Type uJ} {L : Type uL} [DecidableEq J]
    (F : J → Type uF) (j : J) {A : Type uA} {B : Type uB} {a b : ℕ}
    (D : LabeledBlocks (F j) A B a b) (e : L ≃ (∀ q, F q)) (t : ℤ)
    (x : L) (q : J) (hq : q ≠ j) :
    e (((onCoordinate F j D).transport e).T t x) q = e x q := by
  rw [T_transport_apply, Equiv.apply_symm_apply]
  exact T_onCoordinate_other F j D t (e x) q hq

end LabeledBlocks

theorem channelDigitBlocks_T_other (i : Channel p) (j : Label p i) (t : ℤ)
    (w : ZMod (E.r i)) (q : Label p i) (hq : q ≠ j) :
    digitEquiv E i ((channelDigitBlocks E i j).T t w) q = digitEquiv E i w q := by
  simpa only [channelDigitBlocks, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv] using
    (LabeledBlocks.T_onCoordinate_transport_other
      (fun q : Label p i => ZMod (E.digitPrime i q)) j
      (channelDigitBase E i j) (digitEquiv E i).toEquiv t w q hq)

def seedOneBlocks :
    LabeledBlocks (ZMod (E.r (.inr (0 : Fin 2))))
      (ChannelBlockA E (.inr 0) ()) (ChannelBlockB E (.inr 0) ())
      2 (E.b (.inr 0)) :=
  (channelDigitBlocks E (.inr 0) ()).castSizes
    (by simpa using E.seed_a (0 : Fin 2)) rfl

def seedTwoBlocks :
    LabeledBlocks (ZMod (E.r (.inr (1 : Fin 2))))
      (ChannelBlockA E (.inr 1) ()) (ChannelBlockB E (.inr 1) ())
      3 (E.b (.inr 1)) :=
  (channelDigitBlocks E (.inr 1) ()).castSizes
    (by simpa using E.seed_a (1 : Fin 2)) rfl

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

def pFreeQuotient (p : ℕ) (t : ℤ) : ℤ :=
  t / (p : ℤ) ^ padicValInt p t

theorem pFreeQuotient_factor (p : ℕ) (_hp : p.Prime) (t : ℤ) :
    t = (p : ℤ) ^ padicValInt p t * pFreeQuotient p t := by
  exact (Int.mul_ediv_cancel' (padicValInt_dvd (p := p) t)).symm

theorem pFreeQuotient_not_dvd (p : ℕ) (hp : p.Prime) {t : ℤ}
    (ht : t ≠ 0) : ¬ (p : ℤ) ∣ pFreeQuotient p t := by
  let : Fact p.Prime := ⟨hp⟩
  rintro ⟨u, hu⟩
  have hpow : (p : ℤ) ^ (padicValInt p t + 1) ∣ t := by
    refine ⟨u, ?_⟩
    calc
      t = (p : ℤ) ^ padicValInt p t * pFreeQuotient p t :=
        pFreeQuotient_factor p hp t
      _ = (p : ℤ) ^ padicValInt p t * ((p : ℤ) * u) := by rw [hu]
      _ = (p : ℤ) ^ (padicValInt p t + 1) * u := by
        rw [pow_succ, mul_assoc]
  rcases (padicValInt_dvd_iff (p := p) (padicValInt p t + 1) t).mp hpow with h | h
  · exact ht h
  · omega

theorem pFreeQuotient_prime_pow_mul (p : ℕ) (hp : p.Prime)
    (r : ℕ) (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) :
    pFreeQuotient p ((p : ℤ) ^ r * u) = u := by
  let : Fact p.Prime := ⟨hp⟩
  have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  have hu0 : u ≠ 0 := by
    intro h
    apply hu
    rw [h]
    exact dvd_zero _
  have hvpow : padicValInt p ((p : ℤ) ^ r) = r := by
    rw [← Int.natCast_pow, padicValInt.of_nat, padicValNat.prime_pow]
  have hv : padicValInt p ((p : ℤ) ^ r * u) = r := by
    rw [padicValInt.mul (pow_ne_zero _ hp0) hu0, hvpow,
      padicValInt.eq_zero_of_not_dvd hu, add_zero]
  rw [pFreeQuotient, hv]
  exact Int.mul_ediv_cancel_left u (pow_ne_zero r hp0)

theorem pFreeQuotient_mul_prime_pow (p : ℕ) (hp : p.Prime)
    (r : ℕ) {t : ℤ} (ht : t ≠ 0) :
    pFreeQuotient p ((p : ℤ) ^ r * t) = pFreeQuotient p t := by
  have hfactor : (p : ℤ) ^ r * t =
      (p : ℤ) ^ (r + padicValInt p t) * pFreeQuotient p t := by
    calc
      (p : ℤ) ^ r * t =
          (p : ℤ) ^ r * ((p : ℤ) ^ padicValInt p t * pFreeQuotient p t) :=
        congrArg (fun z : ℤ => (p : ℤ) ^ r * z) (pFreeQuotient_factor p hp t)
      _ = (p : ℤ) ^ (r + padicValInt p t) * pFreeQuotient p t := by
        rw [pow_add, mul_assoc]
  rw [hfactor]
  exact pFreeQuotient_prime_pow_mul p hp _ _ (pFreeQuotient_not_dvd p hp ht)

theorem exists_primitive_pair (p : ℕ) (hp : p.Prime) (d e : ℤ)
    (hde : d ≠ 0 ∨ e ≠ 0) :
    ∃ r : ℕ, ∃ a b : ℤ, d = (p : ℤ) ^ r * a ∧
      e = (p : ℤ) ^ r * b ∧ (¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ b) := by
  let : Fact p.Prime := ⟨hp⟩
  let r := padicValInt p (Int.gcd d e : ℤ)
  have hg : (Int.gcd d e : ℤ) ≠ 0 :=
    Int.natCast_ne_zero.mpr (ne_of_gt (Int.gcd_pos_iff.mpr hde))
  have hr : (p : ℤ) ^ r ∣ (Int.gcd d e : ℤ) := padicValInt_dvd _
  obtain ⟨a, ha⟩ := hr.trans (show (Int.gcd d e : ℤ) ∣ d from Int.gcd_dvd_left d e)
  obtain ⟨b, hb⟩ := hr.trans (show (Int.gcd d e : ℤ) ∣ e from Int.gcd_dvd_right d e)
  refine ⟨r, a, b, ha, hb, ?_⟩
  by_cases hpa : (p : ℤ) ∣ a
  · right
    intro hpb
    have hd' : (p : ℤ) ^ (r + 1) ∣ d := by
      obtain ⟨u, hu⟩ := hpa
      refine ⟨u, ?_⟩
      rw [ha, hu, pow_succ, mul_assoc]
    have he' : (p : ℤ) ^ (r + 1) ∣ e := by
      obtain ⟨v, hv⟩ := hpb
      refine ⟨v, ?_⟩
      rw [hb, hv, pow_succ, mul_assoc]
    rcases (padicValInt_dvd_iff (p := p) (r + 1) (Int.gcd d e : ℤ)).mp
        (Int.dvd_coe_gcd hd' he') with hzero | hle
    · exact hg hzero
    · change r + 1 ≤ r at hle
      omega
  · exact Or.inl hpa

def lastDigit (p : ℕ) (hp : p.Prime) (t : ℤ) : Symbol p := by
  letI : Fact p.Prime := ⟨hp⟩
  exact if ht : t = 0 then 1 else
    Units.mk0 (pFreeQuotient p t : ZMod p) (by
      intro h
      exact pFreeQuotient_not_dvd p hp ht
        ((ZMod.intCast_zmod_eq_zero_iff_dvd (pFreeQuotient p t) p).mp h))

@[simp] theorem lastDigit_zero (p : ℕ) (hp : p.Prime) :
    lastDigit p hp 0 = 1 := by
  simp [lastDigit]

theorem lastDigit_val_of_ne_zero (p : ℕ) (hp : p.Prime) {t : ℤ}
    (ht : t ≠ 0) :
    (lastDigit p hp t : ZMod p) = (pFreeQuotient p t : ZMod p) := by
  simp [lastDigit, ht]

theorem lastDigit_eq_of_not_dvd (p : ℕ) (hp : p.Prime) {t : ℤ}
    (ht : ¬ (p : ℤ) ∣ t) : (lastDigit p hp t : ZMod p) = (t : ZMod p) := by
  have ht0 : t ≠ 0 := by
    intro h
    apply ht
    rw [h]
    exact dvd_zero _
  rw [lastDigit_val_of_ne_zero p hp ht0]
  simp only [pFreeQuotient, padicValInt.eq_zero_of_not_dvd ht, pow_zero,
    Int.ediv_one]

@[simp] theorem lastDigit_one (p : ℕ) (hp : p.Prime) :
    lastDigit p hp 1 = 1 := by
  apply Units.ext
  have hnot : ¬ (p : ℤ) ∣ (1 : ℤ) :=
    fun h => hp.not_dvd_one (Int.natCast_dvd_natCast.mp h)
  simpa only [Units.val_one, Int.cast_one] using lastDigit_eq_of_not_dvd p hp hnot

theorem lastDigit_two (p : ℕ) (hp : p.Prime) (hlarge : 2 < p) :
    (lastDigit p hp 2 : ZMod p) = 2 := by
  have hnot : ¬ (p : ℤ) ∣ (2 : ℤ) := by
    intro h
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hlarge
      (Int.natCast_dvd_natCast.mp h)
  simpa only [Int.cast_ofNat] using lastDigit_eq_of_not_dvd p hp hnot

theorem lastDigit_mul_prime_pow (p : ℕ) (hp : p.Prime) (r : ℕ) (t : ℤ) :
    lastDigit p hp ((p : ℤ) ^ r * t) = lastDigit p hp t := by
  by_cases ht : t = 0
  · subst t
    simp
  · have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
    have hprod : (p : ℤ) ^ r * t ≠ 0 := mul_ne_zero (pow_ne_zero _ hp0) ht
    apply Units.ext
    rw [lastDigit_val_of_ne_zero p hp hprod, lastDigit_val_of_ne_zero p hp ht,
      pFreeQuotient_mul_prime_pow p hp r ht]

theorem lastDigit_eq_div_of_dvd_not_sq_dvd (p : ℕ) (hp : p.Prime) {t : ℤ}
    (hdiv : (p : ℤ) ∣ t) (hsq : ¬ (p : ℤ) ^ 2 ∣ t) :
    (lastDigit p hp t : ZMod p) = ((t / (p : ℤ) : ℤ) : ZMod p) := by
  have ht : t ≠ 0 := by
    intro h
    apply hsq
    rw [h]
    exact dvd_zero _
  have hquot : ¬ (p : ℤ) ∣ t / (p : ℤ) := by
    rintro ⟨u, hu⟩
    apply hsq
    refine ⟨u, ?_⟩
    calc
      t = (p : ℤ) * (t / (p : ℤ)) := (Int.mul_ediv_cancel' hdiv).symm
      _ = (p : ℤ) * ((p : ℤ) * u) := by rw [hu]
      _ = (p : ℤ) ^ 2 * u := by rw [pow_two, mul_assoc]
  have hfree := pFreeQuotient_prime_pow_mul p hp 1 (t / (p : ℤ)) hquot
  rw [pow_one, Int.mul_ediv_cancel' hdiv] at hfree
  rw [lastDigit_val_of_ne_zero p hp ht, hfree]

theorem lastDigit_affine_allowed (p : ℕ) (hp : p.Prime) (d e : ℤ) :
    Allowed p (fun n => lastDigit p hp (d * (n.val : ℤ) + e)) := by
  classical
  by_cases hzero : d = 0 ∧ e = 0
  · rcases hzero with ⟨hd, he⟩
    subst d
    subst e
    have hnot : ¬ (p : ℤ) ∣ (1 : ℤ) :=
      fun h => hp.not_dvd_one (Int.natCast_dvd_natCast.mp h)
    refine ⟨0, 1, Or.inr hnot, ?_⟩
    intro n
    dsimp only
    constructor
    · intro _
      simp only [zero_mul, zero_add, lastDigit_zero, Units.val_one, Int.cast_one]
    · intro h _
      exact (hnot (by simpa only [zero_mul, zero_add] using h)).elim
  · obtain ⟨r, a, b, hd, he, hab⟩ :=
      exists_primitive_pair p hp d e (not_and_or.mp hzero)
    refine ⟨a, b, hab, ?_⟩
    intro n
    have harg : d * (n.val : ℤ) + e =
        (p : ℤ) ^ r * (a * (n.val : ℤ) + b) := by
      rw [hd, he]
      ring
    dsimp only
    rw [harg, lastDigit_mul_prime_pow]
    exact ⟨fun h => lastDigit_eq_of_not_dvd p hp h,
      fun h₁ h₂ => lastDigit_eq_div_of_dvd_not_sq_dvd p hp h₁ h₂⟩

theorem lastDigit_lineRule (p : ℕ) (hp : p.Prime) :
    LineRule p (fun _ m => lastDigit p hp m) := by
  intro d e
  exact lastDigit_affine_allowed p hp d e

theorem lastDigit_nonconstantColumns (p : ℕ) (hp : p.Prime) (hlarge : 2 < p) :
    NonconstantColumns (fun (_ : Column p) m => lastDigit p hp m) := by
  intro n
  refine ⟨1, 2, ?_⟩
  intro h
  have hcoe : (1 : ZMod p) = 2 := by
    simpa only [lastDigit_one, Units.val_one, lastDigit_two p hp hlarge] using
      congrArg (fun u : Symbol p => (u : ZMod p)) h
  have hnat : 1 % p = 2 % p :=
    (ZMod.natCast_eq_natCast_iff' 1 2 p).mp
      (by simpa only [Nat.cast_one, Nat.cast_ofNat] using hcoe)
  have h1 : 1 < p := lt_trans (by decide : 1 < 2) hlarge
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hlarge] at hnat
  omega

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree

abbrev D (p : ℕ) := p ^ 4
abbrev Residues (p : ℕ) := ZMod (p ^ 2) × ZMod (p ^ 2)

variable {p : ℕ} [NeZero p]

abbrev K (E : EncodingParameters p) (i : Channel p) := ZMod (E.r i)
abbrev P (E : EncodingParameters p) (i : Channel p) := ZMod (E.a i) × ZMod (E.b i)
abbrev Input (E : EncodingParameters p) := ∀ i : Channel p, K E i
abbrev Useful (E : EncodingParameters p) := ∀ i : Channel p, P E i

abbrev V (E : EncodingParameters p) :=
  ZMod (D p) × (∀ i : Channel p, ZMod ((E.r i) ^ 2) × P E i)

abbrev Ambient (E : EncodingParameters p) := Plane × V E
abbrev Base (E : EncodingParameters p) := Plane × Input E

abbrev Low (E : EncodingParameters p) := Input E
abbrev G (E : EncodingParameters p) := Ambient E

structure GraphOutputs (E : EncodingParameters p) where
  c : Base E → Useful E
  beta : Base E → Input E
  z : Base E → ZMod (D p)

abbrev Outputs (E : EncodingParameters p) := GraphOutputs E

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree.CyclicShear

noncomputable section

def low (r : ℕ) : ZMod (r ^ 2) →+ ZMod r :=
  (ZMod.castHom (dvd_pow_self r (by decide : 2 ≠ 0)) (ZMod r)).toAddMonoidHom

@[simp] theorem low_natCast (r m : ℕ) : low r (m : ZMod (r ^ 2)) = (m : ZMod r) := by
  simp [low]

@[simp] theorem low_intCast (r : ℕ) (m : ℤ) :
    low r (m : ZMod (r ^ 2)) = (m : ZMod r) := by
  simp [low]

private def highInteger (r : ℕ) : ℤ →+ ZMod (r ^ 2) where
  toFun z := (r : ZMod (r ^ 2)) * (z : ZMod (r ^ 2))
  map_zero' := by simp
  map_add' x y := by simp [mul_add]

private theorem highInteger_modulus (r : ℕ) : highInteger r r = 0 := by
  dsimp only [highInteger]
  change (r : ZMod (r ^ 2)) * ((r : ℤ) : ZMod (r ^ 2)) = 0
  rw [Int.cast_natCast, ← pow_two, ← Nat.cast_pow]
  exact ZMod.natCast_self (r ^ 2)

def highMul (r : ℕ) : ZMod r →+ ZMod (r ^ 2) :=
  ZMod.lift r ⟨highInteger r, highInteger_modulus r⟩

@[simp] theorem highMul_intCast (r : ℕ) (m : ℤ) :
    highMul r (m : ZMod r) = (r : ZMod (r ^ 2)) * (m : ZMod (r ^ 2)) := by
  exact ZMod.lift_coe r ⟨highInteger r, highInteger_modulus r⟩ m

@[simp] theorem highMul_natCast (r m : ℕ) :
    highMul r (m : ZMod r) = (r : ZMod (r ^ 2)) * (m : ZMod (r ^ 2)) := by
  simpa using highMul_intCast r (m : ℤ)

theorem highMul_apply (r : ℕ) [NeZero r] (b : ZMod r) :
    highMul r b = (r : ZMod (r ^ 2)) * (b.val : ZMod (r ^ 2)) := by
  simpa using highMul_natCast r b.val

theorem highMul_val (r : ℕ) [NeZero r] (b : ZMod r) :
    (highMul r b).val = r * b.val := by
  rw [highMul_apply, ← Nat.cast_mul]
  apply ZMod.val_natCast_of_lt
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  simpa [pow_two] using Nat.mul_lt_mul_of_pos_left (ZMod.val_lt b) hr

theorem highMul_injective (r : ℕ) [NeZero r] : Function.Injective (highMul r) := by
  intro b c h
  have hv := congrArg ZMod.val h
  rw [highMul_val, highMul_val] at hv
  have hv' : b.val = c.val := Nat.eq_of_mul_eq_mul_left
    (Nat.pos_of_ne_zero (NeZero.ne r)) hv
  exact ZMod.val_injective r hv'

@[simp] theorem low_highMul (r : ℕ) (b : ZMod r) : low r (highMul r b) = 0 := by
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective b
  rw [highMul_intCast]
  change (ZMod.castHom (dvd_pow_self r (by decide : 2 ≠ 0)) (ZMod r))
    ((r : ZMod (r ^ 2)) * (m : ZMod (r ^ 2))) = 0
  simp only [map_mul, map_natCast, map_intCast, ZMod.natCast_self, zero_mul]

theorem mem_range_highMul_iff (r : ℕ) [NeZero r] (v : ZMod (r ^ 2)) :
    v ∈ Set.range (highMul r) ↔ low r v = 0 := by
  constructor
  · rintro ⟨b, rfl⟩
    exact low_highMul r b
  · intro h
    have hcast : (v.val : ZMod r) = 0 := by
      have hv := congrArg (low r) (ZMod.natCast_zmod_val v)
      simpa only [low_natCast, h] using hv
    obtain ⟨m, hm⟩ := (ZMod.natCast_eq_zero_iff v.val r).mp hcast
    refine ⟨(m : ZMod r), ?_⟩
    rw [highMul_natCast, ← Nat.cast_mul, ← hm]
    exact ZMod.natCast_zmod_val v

theorem range_highMul (r : ℕ) [NeZero r] :
    Set.range (highMul r) = ((low r).ker : Set (ZMod (r ^ 2))) := by
  ext v
  exact mem_range_highMul_iff r v

def highEquiv (r : ℕ) [NeZero r] : ZMod r ≃ (low r).ker :=
  Equiv.ofBijective (fun b => ⟨highMul r b, low_highMul r b⟩)
    ⟨fun _ _ h => highMul_injective r (congrArg Subtype.val h), by
      intro v
      obtain ⟨b, hb⟩ := (mem_range_highMul_iff r v).mpr v.property
      exact ⟨b, Subtype.ext hb⟩⟩

@[simp] theorem highEquiv_apply (r : ℕ) [NeZero r] (b : ZMod r) :
    (highEquiv r b : ZMod (r ^ 2)) = highMul r b := rfl

def shear (r : ℕ) (x : ℤ) (k b : ZMod r) : ZMod (r ^ 2) :=
  (x : ZMod (r ^ 2)) + ((k - (x : ZMod r)).val : ZMod (r ^ 2)) + highMul r b

@[simp] theorem low_shear (r : ℕ) [NeZero r] (x : ℤ) (k b : ZMod r) :
    low r (shear r x k b) = k := by
  simp only [shear, map_add, low_intCast, low_natCast, low_highMul, add_zero,
    ZMod.natCast_zmod_val]
  abel

theorem shear_injective (r : ℕ) [NeZero r] (x : ℤ) (k : ZMod r) :
    Function.Injective (shear r x k) := by
  intro b c h
  apply highMul_injective r
  exact add_left_cancel h

theorem shear_eq_zero_add (r : ℕ) (x : ℤ) (k b : ZMod r) :
    shear r x k b = shear r x k 0 + highMul r b := by
  simp [shear]

theorem shear_surjective_fiber (r : ℕ) [NeZero r] (x : ℤ) (k : ZMod r) :
    Function.Surjective (fun b : ZMod r =>
      (⟨shear r x k b, low_shear r x k b⟩ : {v : ZMod (r ^ 2) // low r v = k})) := by
  intro v
  have hz : low r (v.val - shear r x k 0) = 0 := by
    rw [map_sub, v.property, low_shear, sub_self]
  obtain ⟨b, hb⟩ := (mem_range_highMul_iff r _).mpr hz
  refine ⟨b, Subtype.ext ?_⟩
  change shear r x k b = v.val
  rw [shear_eq_zero_add, hb]
  abel

def shearEquiv (r : ℕ) [NeZero r] (x : ℤ) (k : ZMod r) :
    ZMod r ≃ {v : ZMod (r ^ 2) // low r v = k} :=
  Equiv.ofBijective (fun b => ⟨shear r x k b, low_shear r x k b⟩)
    ⟨fun _ _ h => shear_injective r x k (congrArg Subtype.val h),
      shear_surjective_fiber r x k⟩

@[simp] theorem shearEquiv_apply (r : ℕ) [NeZero r] (x : ℤ) (k b : ZMod r) :
    (shearEquiv r x k b : ZMod (r ^ 2)) = shear r x k b := rfl

theorem shear_add (r : ℕ) (x h : ℤ) (k b : ZMod r) :
    shear r (x + h) (k + (h : ZMod r)) b = shear r x k b + (h : ZMod (r ^ 2)) := by
  simp only [shear, Int.cast_add]
  abel_nf

theorem shear_source_add (r : ℕ) (x h : ℤ) (k l b : ZMod r)
    (hl : (h : ZMod r) = l) :
    shear r (x - h) (k - l) b + (h : ZMod (r ^ 2)) = shear r x k b := by
  simpa [hl] using (shear_add r (x - h) h (k - l) b).symm

end

end PeriodicTilingThree.CyclicShear

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree

noncomputable section

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

abbrev low (i : Channel p) : ZMod ((E.r i) ^ 2) →+ K E i :=
  CyclicShear.low (E.r i)

abbrev highMul (i : Channel p) : K E i →+ ZMod ((E.r i) ^ 2) :=
  CyclicShear.highMul (E.r i)

abbrev shear (i : Channel p) (x : ℤ) (k b : K E i) : ZMod ((E.r i) ^ 2) :=
  CyclicShear.shear (E.r i) x k b

abbrev shearEquiv (i : Channel p) (x : ℤ) (k : K E i) :
    K E i ≃ {v : ZMod ((E.r i) ^ 2) // low E i v = k} :=
  CyclicShear.shearEquiv (E.r i) x k

@[simp] theorem low_shear (i : Channel p) (x : ℤ) (k b : K E i) :
    low E i (shear E i x k b) = k := CyclicShear.low_shear _ _ _ _

theorem highMul_injective (i : Channel p) : Function.Injective (highMul E i) :=
  CyclicShear.highMul_injective _

@[simp] theorem low_highMul (i : Channel p) (b : K E i) : low E i (highMul E i b) = 0 :=
  CyclicShear.low_highMul _ _

theorem shear_injective (i : Channel p) (x : ℤ) (k : K E i) :
    Function.Injective (shear E i x k) := CyclicShear.shear_injective _ _ _

theorem shear_add (i : Channel p) (x h : ℤ) (k b : K E i) :
    shear E i (x + h) (k + (h : K E i)) b =
      shear E i x k b + (h : ZMod ((E.r i) ^ 2)) :=
  CyclicShear.shear_add _ _ _ _ _

theorem shear_source_add (i : Channel p) (x h : ℤ) (k l b : K E i)
    (hl : (h : K E i) = l) :
    shear E i (x - h) (k - l) b + (h : ZMod ((E.r i) ^ 2)) = shear E i x k b :=
  CyclicShear.shear_source_add _ _ _ _ _ _ hl

def q0 : Ambient E →+ Base E where
  toFun g := (g.1, fun i => low E i (g.2.2 i).1)
  map_zero' := by
    refine Prod.ext ?_ ?_
    · rfl
    · funext i
      exact map_zero (low E i)
  map_add' g h := by
    refine Prod.ext ?_ ?_
    · rfl
    · funext i
      exact map_add (low E i) (g.2.2 i).1 (h.2.2 i).1

@[simp] theorem q0_apply (g : Ambient E) :
    q0 E g = (g.1, fun i => low E i (g.2.2 i).1) := rfl

variable {E}

def point (o : GraphOutputs E) (b : Base E) : Ambient E :=
  (b.1, o.z b, fun i => (shear E i b.1.1 (b.2 i) (o.beta b i), o.c b i))

@[simp] theorem point_horizontal (o : GraphOutputs E) (b : Base E) : (point o b).1 = b.1 := rfl
@[simp] theorem point_z (o : GraphOutputs E) (b : Base E) : (point o b).2.1 = o.z b := rfl
@[simp] theorem point_c (o : GraphOutputs E) (b : Base E) (i : Channel p) :
    ((point o b).2.2 i).2 = o.c b i := rfl
@[simp] theorem point_v (o : GraphOutputs E) (b : Base E) (i : Channel p) :
    ((point o b).2.2 i).1 = shear E i b.1.1 (b.2 i) (o.beta b i) := rfl

@[simp] theorem q0_point (o : GraphOutputs E) (b : Base E) : q0 E (point o b) = b := by
  refine Prod.ext ?_ ?_
  · rfl
  · funext i
    exact low_shear E i b.1.1 (b.2 i) (o.beta b i)

theorem point_injective (o : GraphOutputs E) : Function.Injective (point o) := by
  intro b d h
  have hq := congrArg (q0 E) h
  simpa only [q0_point] using hq

def graph (o : GraphOutputs E) : Set (Ambient E) := Set.range (point o)

@[simp] theorem point_mem_graph (o : GraphOutputs E) (b : Base E) : point o b ∈ graph o :=
  ⟨b, rfl⟩

theorem eq_point_of_mem_graph (o : GraphOutputs E) {g : Ambient E} (hg : g ∈ graph o) :
    g = point o (q0 E g) := by
  obtain ⟨b, rfl⟩ := hg
  rw [q0_point]

def zeroOutputs (E : EncodingParameters p) : GraphOutputs E :=
  ⟨fun _ _ => 0, fun _ _ => 0, fun _ => 0⟩

theorem q0_surjective (E : EncodingParameters p) : Function.Surjective (q0 E) := by
  intro b
  exact ⟨point (zeroOutputs E) b, q0_point _ _⟩

private theorem section_low (s : Base E → Ambient E) (hs : ∀ b, q0 E (s b) = b)
    (b : Base E) (i : Channel p) : low E i ((s b).2.2 i).1 = b.2 i :=
  congrArg (fun t : Base E => t.2 i) (hs b)

def outputsOfSection (s : Base E → Ambient E) (hs : ∀ b, q0 E (s b) = b) : GraphOutputs E where
  c b i := ((s b).2.2 i).2
  beta b i := (shearEquiv E i b.1.1 (b.2 i)).symm
    ⟨((s b).2.2 i).1, section_low s hs b i⟩
  z b := (s b).2.1

@[simp] theorem point_outputsOfSection (s : Base E → Ambient E)
    (hs : ∀ b, q0 E (s b) = b) (b : Base E) :
    point (outputsOfSection s hs) b = s b := by
  refine Prod.ext ?_ ?_
  · exact (congrArg (fun t : Base E => t.1) (hs b)).symm
  · refine Prod.ext ?_ ?_
    · rfl
    · funext i
      refine Prod.ext ?_ ?_
      · exact congrArg Subtype.val ((shearEquiv E i b.1.1 (b.2 i)).apply_symm_apply
          ⟨((s b).2.2 i).1, section_low s hs b i⟩)
      · rfl

theorem graph_outputsOfSection (s : Base E → Ambient E) (hs : ∀ b, q0 E (s b) = b) :
    graph (outputsOfSection s hs) = Set.range s := by
  exact congrArg (fun f : Base E → Ambient E => Set.range f)
    (funext (point_outputsOfSection s hs))

end

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

open scoped BigOperators

def shiftMultiplicity (a b : ℕ) (e : ZMod a × ZMod b) : ℕ :=
  if e.2 = 0 then
    if e.1 = 0 then 2 else if e.1 = 1 then 0 else 1
  else if e.2 = 1 then
    if e.1 = 0 then 0 else if e.1 = 1 then 2 else 1
  else 1

def shiftOmega (a b : ℕ) (e : ZMod a × ZMod b) : ℤ :=
  ((if e.1 = 0 then 1 else 0) - (if e.1 = 1 then 1 else 0)) *
    ((if e.2 = 0 then 1 else 0) - (if e.2 = 1 then 1 else 0))

abbrev ShiftIndex (a b : ℕ) :=
  Σ e : ZMod a × ZMod b, Fin (shiftMultiplicity a b e)

def shift (a b : ℕ) (δ : ShiftIndex a b) : ZMod a × ZMod b := δ.1

section Counts

variable {a b : ℕ} [NeZero a] [NeZero b]

theorem shiftMultiplicity_cast {a b : ℕ} [NeZero a] [NeZero b] (ha : 2 ≤ a) (hb : 2 ≤ b)
    (e : ZMod a × ZMod b) :
    (shiftMultiplicity a b e : ℤ) = 1 + shiftOmega a b e := by
  let : Fact (1 < a) := ⟨ha⟩
  let : Fact (1 < b) := ⟨hb⟩
  have ha01 : (0 : ZMod a) ≠ 1 := zero_ne_one
  have hb01 : (0 : ZMod b) ≠ 1 := zero_ne_one
  by_cases hα0 : e.1 = 0 <;> by_cases hα1 : e.1 = 1 <;>
    by_cases hξ0 : e.2 = 0 <;> by_cases hξ1 : e.2 = 1 <;>
    simp_all [shiftMultiplicity, shiftOmega]

@[simp] theorem shiftMultiplicity_zero {a b : ℕ} [NeZero a] [NeZero b] :
    shiftMultiplicity a b (0, 0) = 2 := by
  simp [shiftMultiplicity]

theorem sum_shiftMultiplicity_fst (ha : 2 ≤ a) (hb : 2 ≤ b)
    (ξ : ZMod b) :
    ∑ α : ZMod a, shiftMultiplicity a b (α, ξ) = a := by
  have hω : (∑ α : ZMod a, shiftOmega a b (α, ξ)) = 0 := by
    unfold shiftOmega
    dsimp only
    rw [← Finset.sum_mul (Finset.univ : Finset (ZMod a))
      (fun α : ZMod a =>
        (if α = 0 then (1 : ℤ) else 0) -
          (if α = 1 then (1 : ℤ) else 0))
      ((if ξ = 0 then (1 : ℤ) else 0) -
        (if ξ = 1 then (1 : ℤ) else 0))]
    rw [Finset.sum_sub_distrib]
    simp
  have h : (∑ α : ZMod a, (shiftMultiplicity a b (α, ξ) : ℤ)) = a := by
    simp_rw [shiftMultiplicity_cast ha hb]
    rw [Finset.sum_add_distrib, hω]
    simp [ZMod.card]
  exact_mod_cast h

theorem sum_shiftMultiplicity_snd (ha : 2 ≤ a) (hb : 2 ≤ b)
    (α : ZMod a) :
    ∑ ξ : ZMod b, shiftMultiplicity a b (α, ξ) = b := by
  have hω : (∑ ξ : ZMod b, shiftOmega a b (α, ξ)) = 0 := by
    unfold shiftOmega
    dsimp only
    rw [← Finset.mul_sum (Finset.univ : Finset (ZMod b))
      (fun ξ : ZMod b =>
        (if ξ = 0 then (1 : ℤ) else 0) -
          (if ξ = 1 then (1 : ℤ) else 0))
      ((if α = 0 then (1 : ℤ) else 0) -
        (if α = 1 then (1 : ℤ) else 0))]
    rw [Finset.sum_sub_distrib]
    simp
  have h : (∑ ξ : ZMod b, (shiftMultiplicity a b (α, ξ) : ℤ)) = b := by
    simp_rw [shiftMultiplicity_cast ha hb]
    rw [Finset.sum_add_distrib, hω]
    simp [ZMod.card]
  exact_mod_cast h

theorem sum_shiftMultiplicity (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ∑ e : ZMod a × ZMod b, shiftMultiplicity a b e = a * b := by
  rw [Fintype.sum_prod_type]
  simp_rw [sum_shiftMultiplicity_snd ha hb]
  simp [ZMod.card]

theorem card_shiftIndex (ha : 2 ≤ a) (hb : 2 ≤ b) :
    Fintype.card (ShiftIndex a b) = a * b := by
  simpa only [ShiftIndex, Fintype.card_sigma, Fintype.card_fin] using
    sum_shiftMultiplicity ha hb

theorem sum_shift {M : Type uM} [AddCommMonoid M] (f : ZMod a × ZMod b → M) :
    (∑ δ : ShiftIndex a b, f (shift a b δ)) =
      ∑ e : ZMod a × ZMod b, shiftMultiplicity a b e • f e := by
  simp [ShiftIndex, shift, Fintype.sum_sigma]

private def shiftFibreEquiv (e : ZMod a × ZMod b) :
    {δ : ShiftIndex a b // shift a b δ = e} ≃ Fin (shiftMultiplicity a b e) where
  toFun δ := by
    rcases δ with ⟨⟨e', k⟩, h⟩
    change e' = e at h
    subst e'
    exact k
  invFun k := ⟨⟨e, k⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨e', k⟩, h⟩
    change e' = e at h
    subst e'
    rfl
  right_inv _ := rfl

theorem card_shift_fibre (e : ZMod a × ZMod b) :
    Fintype.card {δ : ShiftIndex a b // shift a b δ = e} =
      shiftMultiplicity a b e := by
  simpa using Fintype.card_congr (shiftFibreEquiv e)

private def shiftFibreAEquiv (ξ : ZMod b) :
    {δ : ShiftIndex a b // (shift a b δ).2 = ξ} ≃
      Σ α : ZMod a, Fin (shiftMultiplicity a b (α, ξ)) where
  toFun δ := by
    rcases δ with ⟨⟨⟨α, ξ'⟩, k⟩, h⟩
    change ξ' = ξ at h
    subst ξ'
    exact ⟨α, k⟩
  invFun δ := ⟨⟨(δ.1, ξ), δ.2⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨⟨α, ξ'⟩, k⟩, h⟩
    change ξ' = ξ at h
    subst ξ'
    rfl
  right_inv _ := rfl

private def shiftFibreBEquiv (α : ZMod a) :
    {δ : ShiftIndex a b // (shift a b δ).1 = α} ≃
      Σ ξ : ZMod b, Fin (shiftMultiplicity a b (α, ξ)) where
  toFun δ := by
    rcases δ with ⟨⟨⟨α', ξ⟩, k⟩, h⟩
    change α' = α at h
    subst α'
    exact ⟨ξ, k⟩
  invFun δ := ⟨⟨(α, δ.1), δ.2⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨⟨α', ξ⟩, k⟩, h⟩
    change α' = α at h
    subst α'
    rfl
  right_inv _ := rfl

theorem card_shift_fibreA (ha : 2 ≤ a) (hb : 2 ≤ b) (ξ : ZMod b) :
    Fintype.card {δ : ShiftIndex a b // (shift a b δ).2 = ξ} = a := by
  calc
    _ = Fintype.card (Σ α : ZMod a, Fin (shiftMultiplicity a b (α, ξ))) :=
      Fintype.card_congr (shiftFibreAEquiv ξ)
    _ = a := by
      simpa only [Fintype.card_sigma, Fintype.card_fin] using
        sum_shiftMultiplicity_fst ha hb ξ

theorem card_shift_fibreB (ha : 2 ≤ a) (hb : 2 ≤ b) (α : ZMod a) :
    Fintype.card {δ : ShiftIndex a b // (shift a b δ).1 = α} = b := by
  calc
    _ = Fintype.card (Σ ξ : ZMod b, Fin (shiftMultiplicity a b (α, ξ))) :=
      Fintype.card_congr (shiftFibreBEquiv α)
    _ = b := by
      simpa only [Fintype.card_sigma, Fintype.card_fin] using
        sum_shiftMultiplicity_snd ha hb α

end Counts

section Orderings

variable {a b : ℕ} [NeZero a] [NeZero b] (ha : 2 ≤ a) (hb : 2 ≤ b)

noncomputable def fibreOrderA (ξ : ZMod b) :
    {δ : ShiftIndex a b // (shift a b δ).2 = ξ} ≃ ZMod a :=
  Fintype.equivOfCardEq ((card_shift_fibreA ha hb ξ).trans (ZMod.card a).symm)

noncomputable def fibreOrderB (α : ZMod a) :
    {δ : ShiftIndex a b // (shift a b δ).1 = α} ≃ ZMod b :=
  Fintype.equivOfCardEq ((card_shift_fibreB ha hb α).trans (ZMod.card b).symm)

noncomputable def rhoA (δ : ShiftIndex a b) : ZMod a :=
  fibreOrderA ha hb (shift a b δ).2 ⟨δ, rfl⟩ - (shift a b δ).1

noncomputable def rhoB (δ : ShiftIndex a b) : ZMod b :=
  fibreOrderB ha hb (shift a b δ).1 ⟨δ, rfl⟩ - (shift a b δ).2

theorem fibreOrderA_apply (ξ : ZMod b)
    (δ : {δ : ShiftIndex a b // (shift a b δ).2 = ξ}) :
    fibreOrderA ha hb ξ δ = (shift a b δ.1).1 + rhoA ha hb δ.1 := by
  rcases δ with ⟨δ, h⟩
  subst ξ
  simp [rhoA]

theorem fibreOrderB_apply (α : ZMod a)
    (δ : {δ : ShiftIndex a b // (shift a b δ).1 = α}) :
    fibreOrderB ha hb α δ = (shift a b δ.1).2 + rhoB ha hb δ.1 := by
  rcases δ with ⟨δ, h⟩
  subst α
  simp [rhoB]

noncomputable def shiftOrderA : ShiftIndex a b ≃ ZMod b × ZMod a :=
  (Equiv.sigmaFiberEquiv (fun δ : ShiftIndex a b => (shift a b δ).2)).symm.trans
    (Equiv.sigmaEquivProdOfEquiv (fibreOrderA ha hb))

noncomputable def shiftOrderB : ShiftIndex a b ≃ ZMod a × ZMod b :=
  (Equiv.sigmaFiberEquiv (fun δ : ShiftIndex a b => (shift a b δ).1)).symm.trans
    (Equiv.sigmaEquivProdOfEquiv (fibreOrderB ha hb))

theorem shiftOrderA_apply (δ : ShiftIndex a b) :
    shiftOrderA ha hb δ = ((shift a b δ).2, (shift a b δ).1 + rhoA ha hb δ) := by
  change ((shift a b δ).2, fibreOrderA ha hb (shift a b δ).2 ⟨δ, rfl⟩) = _
  exact congrArg (fun z : ZMod a => ((shift a b δ).2, z))
    (fibreOrderA_apply ha hb (shift a b δ).2 ⟨δ, rfl⟩)

theorem shiftOrderB_apply (δ : ShiftIndex a b) :
    shiftOrderB ha hb δ = ((shift a b δ).1, (shift a b δ).2 + rhoB ha hb δ) := by
  change ((shift a b δ).1, fibreOrderB ha hb (shift a b δ).1 ⟨δ, rfl⟩) = _
  exact congrArg (fun z : ZMod b => ((shift a b δ).1, z))
    (fibreOrderB_apply ha hb (shift a b δ).1 ⟨δ, rfl⟩)

theorem bijective_fibreOrderA (ξ : ZMod b) :
    Function.Bijective (fun δ : {δ : ShiftIndex a b // (shift a b δ).2 = ξ} =>
      (shift a b δ.1).1 + rhoA ha hb δ.1) := by
  have he : (fun δ : {δ : ShiftIndex a b // (shift a b δ).2 = ξ} =>
      (shift a b δ.1).1 + rhoA ha hb δ.1) = (fibreOrderA ha hb ξ) := by
    funext δ
    exact (fibreOrderA_apply ha hb ξ δ).symm
  rw [he]
  exact (fibreOrderA ha hb ξ).bijective

theorem bijective_fibreOrderB (α : ZMod a) :
    Function.Bijective (fun δ : {δ : ShiftIndex a b // (shift a b δ).1 = α} =>
      (shift a b δ.1).2 + rhoB ha hb δ.1) := by
  have he : (fun δ : {δ : ShiftIndex a b // (shift a b δ).1 = α} =>
      (shift a b δ.1).2 + rhoB ha hb δ.1) = (fibreOrderB ha hb α) := by
    funext δ
    exact (fibreOrderB_apply ha hb α δ).symm
  rw [he]
  exact (fibreOrderB ha hb α).bijective

end Orderings

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

noncomputable section

def separatedResidueLift {J : Type uJ} [Fintype J] (M : ℕ) [NeZero M]
    (v : J → ZMod M) (j : J) : ℤ :=
  ((v j).val : ℤ) + (M : ℤ) * ((Fintype.equivFin J j).val : ℤ)

@[simp] theorem separatedResidueLift_cast {J : Type uJ} [Fintype J]
    (M : ℕ) [NeZero M] (v : J → ZMod M) (j : J) :
    (separatedResidueLift M v j : ZMod M) = v j := by
  simp [separatedResidueLift]

theorem separatedResidueLift_injective {J : Type uJ} [Fintype J]
    (M : ℕ) [NeZero M] (v : J → ZMod M) :
    Function.Injective (separatedResidueLift M v) := by
  intro i j hij
  change ((v i).val : ℤ) + (M : ℤ) * ((Fintype.equivFin J i).val : ℤ) =
    ((v j).val : ℤ) + (M : ℤ) * ((Fintype.equivFin J j).val : ℤ) at hij
  have he : (v i).val + M * (Fintype.equivFin J i).val =
      (v j).val + M * (Fintype.equivFin J j).val := by
    exact_mod_cast hij
  apply (Fintype.equivFin J).injective
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmul := Nat.mul_le_mul_left M (Nat.succ_le_of_lt hlt)
    have hi := ZMod.val_lt (v i)
    nlinarith
  · have hmul := Nat.mul_le_mul_left M (Nat.succ_le_of_lt hgt)
    have hj := ZMod.val_lt (v j)
    nlinarith

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

abbrev ActivationIndex (i : Channel p) :=
  K E i × ShiftIndex (E.a i) (E.b i)

abbrev SeedActivationIndex (t : Fin 2) := ActivationIndex E (.inr t) × Residues p

def otherSeed (t : Fin 2) : Fin 2 := ⟨1 - t.val, by omega⟩

@[simp] theorem otherSeed_ne_self (t : Fin 2) : otherSeed t ≠ t := by
  fin_cases t <;> decide

@[simp] theorem otherSeed_otherSeed (t : Fin 2) : otherSeed (otherSeed t) = t := by
  fin_cases t <;> decide

def activationModulus (i : Channel p) : ℕ := (E.r i * E.a i) * E.b i

instance activationModulus_neZero (i : Channel p) : NeZero (activationModulus E i) := by
  unfold activationModulus
  infer_instance

private theorem activationCoprime (i : Channel p) :
    Nat.Coprime (E.r i * E.a i) (E.b i) := by
  rw [Nat.coprime_mul_iff_left]
  exact ⟨E.r_coprime_b i i, E.a_coprime_b i⟩

def activationCRT (i : Channel p) :
    ZMod (activationModulus E i) ≃+* ((K E i × ZMod (E.a i)) × ZMod (E.b i)) :=
  (ZMod.chineseRemainder (activationCoprime E i)).trans
    (RingEquiv.prodCongr (ZMod.chineseRemainder (E.r_coprime_a i i))
      (RingEquiv.refl _))

def activationResidue (i : Channel p) (j : ActivationIndex E i) :
    ZMod (activationModulus E i) :=
  (activationCRT E i).symm
    ((j.1, rhoA (E.a_two_le i) (E.b_two_le i) j.2),
      rhoB (E.a_two_le i) (E.b_two_le i) j.2)

def ordinaryFirst (n : Column p) : ActivationIndex E (.inl n) → ℤ :=
  separatedResidueLift (activationModulus E (.inl n)) (activationResidue E (.inl n))

def ordinaryOffset (n : Column p) (j : ActivationIndex E (.inl n)) : Plane :=
  (ordinaryFirst E n j, -(n.val : ℤ) * ordinaryFirst E n j)

theorem ordinaryFirst_residues (n : Column p) (j : ActivationIndex E (.inl n)) :
    (((ordinaryFirst E n j : K E (.inl n)),
       (ordinaryFirst E n j : ZMod (E.a (.inl n)))),
       (ordinaryFirst E n j : ZMod (E.b (.inl n)))) =
      ((j.1, rhoA (E.a_two_le (.inl n)) (E.b_two_le (.inl n)) j.2),
        rhoB (E.a_two_le (.inl n)) (E.b_two_le (.inl n)) j.2) := by
  have h := congrArg (activationCRT E (.inl n))
    (separatedResidueLift_cast (activationModulus E (.inl n))
      (activationResidue E (.inl n)) j)
  rw [activationResidue, RingEquiv.apply_symm_apply] at h
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · simpa only [ordinaryFirst, map_intCast, Prod.fst_intCast] using
      congrArg (fun z => z.1.1) h
  · simpa only [ordinaryFirst, map_intCast, Prod.fst_intCast, Prod.snd_intCast] using
      congrArg (fun z => z.1.2) h
  · simpa only [ordinaryFirst, map_intCast, Prod.snd_intCast] using
      congrArg Prod.snd h

@[simp] theorem ordinaryOffset_low (n : Column p) (j : ActivationIndex E (.inl n)) :
    ((ordinaryOffset E n j).1 : K E (.inl n)) = j.1 :=
  congrArg (fun z => z.1.1) (ordinaryFirst_residues E n j)

@[simp] theorem ordinaryOffset_rhoA (n : Column p) (j : ActivationIndex E (.inl n)) :
    ((ordinaryOffset E n j).1 : ZMod (E.a (.inl n))) =
      rhoA (E.a_two_le (.inl n)) (E.b_two_le (.inl n)) j.2 :=
  congrArg (fun z => z.1.2) (ordinaryFirst_residues E n j)

@[simp] theorem ordinaryOffset_rhoB (n : Column p) (j : ActivationIndex E (.inl n)) :
    ((ordinaryOffset E n j).1 : ZMod (E.b (.inl n))) =
      rhoB (E.a_two_le (.inl n)) (E.b_two_le (.inl n)) j.2 :=
  congrArg Prod.snd (ordinaryFirst_residues E n j)

@[simp] theorem ordinaryOffset_lineValue (n : Column p) (j : ActivationIndex E (.inl n)) :
    lineValue n (ordinaryOffset E n j) = 0 := by
  simp [lineValue, ordinaryOffset]

theorem ordinaryOffset_injective (n : Column p) : Function.Injective (ordinaryOffset E n) := by
  intro i j hij
  exact separatedResidueLift_injective _ _ (congrArg Prod.fst hij)

def seedModulus (t : Fin 2) : ℕ :=
  (activationModulus E (.inr t) * p ^ 2) * E.a (.inr (otherSeed t))

instance seedModulus_neZero (t : Fin 2) : NeZero (seedModulus E t) := by
  unfold seedModulus
  infer_instance

private theorem activationCoprime_p (i : Channel p) :
    Nat.Coprime (activationModulus E i) (p ^ 2) := by
  rw [Nat.coprime_pow_right_iff (by decide : 0 < 2)]
  simp only [activationModulus, Nat.coprime_mul_iff_left]
  exact ⟨⟨E.r_coprime_p i, E.prime_coprime_p (.inl i)⟩,
    E.prime_coprime_p (.inr (.inl i))⟩

private theorem seedCoprime_other (t : Fin 2) :
    Nat.Coprime (activationModulus E (.inr t) * p ^ 2)
      (E.a (.inr (otherSeed t))) := by
  simp only [activationModulus, Nat.coprime_mul_iff_left]
  refine ⟨⟨⟨E.r_coprime_a _ _, ?_⟩, ?_⟩, ?_⟩
  · apply E.prime_coprime
    simp only [ne_eq, Sum.inl.injEq, Sum.inr.injEq]
    exact (otherSeed_ne_self t).symm
  · apply E.prime_coprime
    simp
  · exact (E.prime_coprime_p (.inl (.inr (otherSeed t)))).symm.pow_left 2

def seedCRT (t : Fin 2) :
    ZMod (seedModulus E t) ≃+*
      ((((K E (.inr t) × ZMod (E.a (.inr t))) × ZMod (E.b (.inr t))) ×
        ZMod (p ^ 2)) × ZMod (E.a (.inr (otherSeed t)))) :=
  (ZMod.chineseRemainder (seedCoprime_other E t)).trans
    (RingEquiv.prodCongr
      ((ZMod.chineseRemainder (activationCoprime_p E (.inr t))).trans
        (RingEquiv.prodCongr (activationCRT E (.inr t)) (RingEquiv.refl _)))
      (RingEquiv.refl _))

def seedActivationResidue (t : Fin 2) (j : SeedActivationIndex E t) :
    ZMod (seedModulus E t) :=
  (seedCRT E t).symm
    ((((j.1.1, rhoA (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2),
      rhoB (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2), j.2.1), 0)

def seedFirst (t : Fin 2) : SeedActivationIndex E t → ℤ :=
  separatedResidueLift (seedModulus E t) (seedActivationResidue E t)

def seedOffset (t : Fin 2) (j : SeedActivationIndex E t) : Plane :=
  (seedFirst E t j, (j.2.2.val : ℤ))

theorem seedFirst_residues (t : Fin 2) (j : SeedActivationIndex E t) :
    (((((seedFirst E t j : K E (.inr t)),
      (seedFirst E t j : ZMod (E.a (.inr t)))),
      (seedFirst E t j : ZMod (E.b (.inr t)))),
      (seedFirst E t j : ZMod (p ^ 2))),
      (seedFirst E t j : ZMod (E.a (.inr (otherSeed t))))) =
    ((((j.1.1, rhoA (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2),
      rhoB (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2), j.2.1), 0) := by
  have h := congrArg (seedCRT E t)
    (separatedResidueLift_cast (seedModulus E t) (seedActivationResidue E t) j)
  rw [seedActivationResidue, RingEquiv.apply_symm_apply] at h
  refine Prod.ext (Prod.ext (Prod.ext (Prod.ext ?_ ?_) ?_) ?_) ?_
  · simpa only [seedFirst, map_intCast, Prod.fst_intCast] using
      congrArg (fun z => z.1.1.1.1) h
  · simpa only [seedFirst, map_intCast, Prod.fst_intCast, Prod.snd_intCast] using
      congrArg (fun z => z.1.1.1.2) h
  · simpa only [seedFirst, map_intCast, Prod.fst_intCast, Prod.snd_intCast] using
      congrArg (fun z => z.1.1.2) h
  · simpa only [seedFirst, map_intCast, Prod.fst_intCast, Prod.snd_intCast] using
      congrArg (fun z => z.1.2) h
  · simpa only [seedFirst, map_intCast, Prod.snd_intCast] using
      congrArg Prod.snd h

@[simp] theorem seedOffset_low (t : Fin 2) (j : SeedActivationIndex E t) :
    ((seedOffset E t j).1 : K E (.inr t)) = j.1.1 :=
  congrArg (fun z => z.1.1.1.1) (seedFirst_residues E t j)

@[simp] theorem seedOffset_rhoA (t : Fin 2) (j : SeedActivationIndex E t) :
    ((seedOffset E t j).1 : ZMod (E.a (.inr t))) =
      rhoA (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2 :=
  congrArg (fun z => z.1.1.1.2) (seedFirst_residues E t j)

@[simp] theorem seedOffset_rhoB (t : Fin 2) (j : SeedActivationIndex E t) :
    ((seedOffset E t j).1 : ZMod (E.b (.inr t))) =
      rhoB (E.a_two_le (.inr t)) (E.b_two_le (.inr t)) j.1.2 :=
  congrArg (fun z => z.1.1.2) (seedFirst_residues E t j)

@[simp] theorem seedOffset_other (t : Fin 2) (j : SeedActivationIndex E t) :
    ((seedOffset E t j).1 : ZMod (E.a (.inr (otherSeed t)))) = 0 :=
  congrArg Prod.snd (seedFirst_residues E t j)

@[simp] theorem seedOffset_residue (t : Fin 2) (j : SeedActivationIndex E t) :
    (((seedOffset E t j).1 : ZMod (p ^ 2)),
      ((seedOffset E t j).2 : ZMod (p ^ 2))) = j.2 := by
  apply Prod.ext
  · exact congrArg (fun z => z.1.2) (seedFirst_residues E t j)
  · simp [seedOffset]

theorem seedOffset_injective (t : Fin 2) : Function.Injective (seedOffset E t) := by
  intro i j hij
  exact separatedResidueLift_injective _ _ (congrArg Prod.fst hij)

end

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree.SharedSeed

abbrev Residues (p : ℕ) := ZMod (p ^ 2) × ZMod (p ^ 2)
abbrev ActiveLabels := ZMod 3 ⊕ (Fin 2 × ZMod 2)
abbrev InactiveLabels (m : ℕ) := Fin m × (ZMod 2 × ZMod 3)
abbrev LabelledResidue (m : ℕ) :=
  ZMod 3 ⊕ ((Fin 2 × ZMod 2) ⊕ InactiveLabels m)

def residue (p : ℕ) (x : ℤ × ℤ) : Residues p := (x.1, x.2)

def firstPoint (p : ℕ) (y : ZMod 3) : Residues p :=
  ((p * y.val : ℕ), 1)

def secondPoint (p : ℕ) (u : Fin 2 × ZMod 2) : Residues p :=
  ((p * (2 * u.1.val + u.2.val) : ℕ), 2)

def activePoint (p : ℕ) : ActiveLabels → Residues p :=
  Sum.elim (firstPoint p) (secondPoint p)

def firstRegion (p : ℕ) : Set (Residues p) := Set.range (firstPoint p)
def secondRegion (p : ℕ) : Set (Residues p) := Set.range (secondPoint p)
def Rest (p : ℕ) := {s : Residues p // s ∉ Set.range (activePoint p)}
def copyCount (p : ℕ) : ℕ := (p ^ 4 - 7) / 6

private theorem nat_multiple_cast_injective {p u v : ℕ}
    (hp : 0 < p) (hu : u < p) (hv : v < p)
    (h : (p * u : ZMod (p ^ 2)) = (p * v : ZMod (p ^ 2))) : u = v := by
  have hu' : p * u < p ^ 2 := by
    simpa [pow_two] using Nat.mul_lt_mul_of_pos_left hu hp
  have hv' : p * v < p ^ 2 := by
    simpa [pow_two] using Nat.mul_lt_mul_of_pos_left hv hp
  have hn : ((p * u : ℕ) : ZMod (p ^ 2)) = ((p * v : ℕ) : ZMod (p ^ 2)) := by
    simpa only [Nat.cast_mul] using h
  have hh := congrArg ZMod.val hn
  rw [ZMod.val_natCast_of_lt hu', ZMod.val_natCast_of_lt hv'] at hh
  exact Nat.eq_of_mul_eq_mul_left hp hh

theorem firstPoint_injective {p : ℕ} (hlarge : 200 < p) :
    Function.Injective (firstPoint p) := by
  intro y y' h
  apply ZMod.val_injective 3
  apply nat_multiple_cast_injective (by omega)
      (lt_trans (ZMod.val_lt y) (by omega : 3 < p))
      (lt_trans (ZMod.val_lt y') (by omega : 3 < p))
  simpa only [firstPoint, Nat.cast_mul] using congrArg Prod.fst h

theorem secondPoint_injective {p : ℕ} (hlarge : 200 < p) :
    Function.Injective (secondPoint p) := by
  rintro ⟨c,y⟩ ⟨c',y'⟩ h
  have hc := c.isLt
  have hc' := c'.isLt
  have hy := ZMod.val_lt y
  have hy' := ZMod.val_lt y'
  have hcode : 2 * c.val + y.val = 2 * c'.val + y'.val := by
    apply nat_multiple_cast_injective (p := p) (by omega) (by omega) (by omega)
    simpa only [secondPoint, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      using congrArg Prod.fst h
  have hcc : c.val = c'.val := by omega
  have hyy : y.val = y'.val := by omega
  exact Prod.ext (Fin.ext hcc) (ZMod.val_injective 2 hyy)

theorem firstPoint_ne_secondPoint {p : ℕ} (hlarge : 200 < p)
    (y : ZMod 3) (u : Fin 2 × ZMod 2) : firstPoint p y ≠ secondPoint p u := by
  intro h
  have hp2 : 2 < p ^ 2 := lt_of_lt_of_le (by norm_num : 2 < 201 ^ 2)
    (Nat.pow_le_pow_left (by omega : 201 ≤ p) 2)
  have hh := congrArg (fun s : Residues p => s.2.val) h
  change (1 : ZMod (p ^ 2)).val = (2 : ZMod (p ^ 2)).val at hh
  have h1 : (1 : ZMod (p ^ 2)).val = 1 := by
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (by omega : 1 < p ^ 2)
  have h2 : (2 : ZMod (p ^ 2)).val = 2 := by
    simpa only [Nat.cast_ofNat] using ZMod.val_natCast_of_lt hp2
  have h12 : (1 : ℕ) = 2 := h1.symm.trans (hh.trans h2)
  omega

theorem activePoint_injective {p : ℕ} (hlarge : 200 < p) :
    Function.Injective (activePoint p) := by
  intro a b h
  cases a with
  | inl y =>
    cases b with
    | inl y' => exact congrArg Sum.inl (firstPoint_injective hlarge h)
    | inr u => exact (firstPoint_ne_secondPoint hlarge y u h).elim
  | inr u =>
    cases b with
    | inl y => exact (firstPoint_ne_secondPoint hlarge y u h.symm).elim
    | inr u' => exact congrArg Sum.inr (secondPoint_injective hlarge h)

theorem first_second_disjoint {p : ℕ} (hlarge : 200 < p) :
    Disjoint (firstRegion p) (secondRegion p) := by
  rw [Set.disjoint_left]
  rintro s ⟨y, rfl⟩ ⟨u, hu⟩
  exact firstPoint_ne_secondPoint hlarge y u hu.symm

theorem seven_le_pow {p : ℕ} (hlarge : 200 < p) : 7 ≤ p ^ 4 := by
  exact le_trans (by norm_num : 7 ≤ 201 ^ 4)
    (Nat.pow_le_pow_left (by omega : 201 ≤ p) 4)

theorem pow_four_mod_six {p : ℕ} (hp : p.Prime) (hlarge : 200 < p) :
    p ^ 4 % 6 = 1 := by
  have htwo : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hthree : p % 3 ≠ 0 := by
    intro h
    have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    have he : 3 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hd
    omega
  have hsix : p % 6 = 1 ∨ p % 6 = 5 := by omega
  rw [Nat.pow_mod]
  rcases hsix with h | h <;> norm_num [h]

theorem six_dvd_remainder {p : ℕ} (hp : p.Prime) (hlarge : 200 < p) :
    6 ∣ p ^ 4 - 7 := by
  apply Nat.dvd_of_mod_eq_zero
  have hmod := pow_four_mod_six hp hlarge
  have hge := seven_le_pow hlarge
  omega

theorem copyCount_mul_six {p : ℕ} (hp : p.Prime) (hlarge : 200 < p) :
    copyCount p * 6 = p ^ 4 - 7 := by
  exact Nat.div_mul_cancel (six_dvd_remainder hp hlarge)

theorem six_mul_copyCount_add_seven {p : ℕ} (hp : p.Prime)
    (hlarge : 200 < p) : 6 * copyCount p + 7 = p ^ 4 := by
  have h := copyCount_mul_six hp hlarge
  have hge := seven_le_pow hlarge
  omega

noncomputable def restEquiv {p : ℕ} (hp : p.Prime) (hlarge : 200 < p) :
    Rest p ≃ InactiveLabels (copyCount p) := by
  classical
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (by omega)⟩
  letI : Fintype (Rest p) := by unfold Rest; infer_instance
  apply Fintype.equivOfCardEq
  have hactive : Fintype.card (Set.range (activePoint p)) = 7 := by
    rw [← Fintype.card_congr (Equiv.ofInjective _ (activePoint_injective hlarge))]
    norm_num [ActiveLabels]
  have hrest : Fintype.card (Rest p) = p ^ 4 - 7 := by
    change Fintype.card ((Set.range (activePoint p))ᶜ : Set (Residues p)) = _
    rw [Fintype.card_compl_set, hactive]
    simp only [Residues, Fintype.card_prod, ZMod.card]
    congr 1
    ring
  rw [hrest]
  simpa [InactiveLabels, Fintype.card_prod, Nat.mul_assoc]
    using (copyCount_mul_six hp hlarge).symm

noncomputable def residueAssembly {p : ℕ} (hp : p.Prime) (hlarge : 200 < p) :
    LabelledResidue (copyCount p) ≃ Residues p := by
  classical
  exact (Equiv.sumAssoc (ZMod 3) (Fin 2 × ZMod 2)
      (InactiveLabels (copyCount p))).symm |>.trans
    ((Equiv.sumCongr (Equiv.ofInjective (activePoint p)
      (activePoint_injective hlarge)) (restEquiv hp hlarge).symm).trans
      (Equiv.Set.sumCompl (Set.range (activePoint p))))

noncomputable def residueEquiv {p : ℕ} (hp : p.Prime) (hlarge : 200 < p) :
    Residues p ≃ LabelledResidue (copyCount p) :=
  (residueAssembly hp hlarge).symm

@[simp] theorem residueAssembly_first {p : ℕ} (hp : p.Prime)
    (hlarge : 200 < p) (y : ZMod 3) :
    residueAssembly hp hlarge (Sum.inl y) = firstPoint p y := rfl

@[simp] theorem residueAssembly_second {p : ℕ} (hp : p.Prime)
    (hlarge : 200 < p) (u : Fin 2 × ZMod 2) :
    residueAssembly hp hlarge (Sum.inr (Sum.inl u)) = secondPoint p u := rfl

@[simp] theorem residueEquiv_firstPoint {p : ℕ} (hp : p.Prime)
    (hlarge : 200 < p) (y : ZMod 3) :
    residueEquiv hp hlarge (firstPoint p y) = Sum.inl y :=
  (residueAssembly hp hlarge).symm_apply_apply (Sum.inl y)

@[simp] theorem residueEquiv_secondPoint {p : ℕ} (hp : p.Prime)
    (hlarge : 200 < p) (u : Fin 2 × ZMod 2) :
    residueEquiv hp hlarge (secondPoint p u) = Sum.inr (Sum.inl u) :=
  (residueAssembly hp hlarge).symm_apply_apply (Sum.inr (Sum.inl u))

theorem residueEquiv_first_iff {p : ℕ} (hp : p.Prime)
    (hlarge : 200 < p) (s : Residues p) :
    (∃ y, residueEquiv hp hlarge s = Sum.inl y) ↔ s ∈ firstRegion p := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply (residueEquiv hp hlarge).injective
    rw [residueEquiv_firstPoint, hy]
  · rintro ⟨y, rfl⟩
    exact ⟨y, residueEquiv_firstPoint hp hlarge y⟩

theorem residueEquiv_second_iff {p : ℕ} (hp : p.Prime)
    (hlarge : 200 < p) (s : Residues p) :
    (∃ u, residueEquiv hp hlarge s = Sum.inr (Sum.inl u)) ↔
      s ∈ secondRegion p := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    apply (residueEquiv hp hlarge).injective
    rw [residueEquiv_secondPoint, hu]
  · rintro ⟨u, rfl⟩
    exact ⟨u, residueEquiv_secondPoint hp hlarge u⟩

def reduce (p : ℕ) (s : Residues p) : ZMod p × ZMod p :=
  let f := ZMod.castHom (show p ∣ p ^ 2 from ⟨p, by ring⟩) (ZMod p)
  (f s.1, f s.2)

@[simp] theorem reduce_firstPoint (p : ℕ) (y : ZMod 3) :
    reduce p (firstPoint p y) = (0, 1) := by
  let f : ZMod (p ^ 2) →+* ZMod p :=
    ZMod.castHom (show p ∣ p ^ 2 from ⟨p, by ring⟩) (ZMod p)
  change (f ((p * y.val : ℕ) : ZMod (p ^ 2)), f 1) = (0, 1)
  apply Prod.ext
  · rw [map_natCast]
    simp [Nat.cast_mul]
  · exact map_one f

@[simp] theorem reduce_secondPoint (p : ℕ) (u : Fin 2 × ZMod 2) :
    reduce p (secondPoint p u) = (0, 2) := by
  let f : ZMod (p ^ 2) →+* ZMod p :=
    ZMod.castHom (show p ∣ p ^ 2 from ⟨p, by ring⟩) (ZMod p)
  change (f ((p * (2 * u.1.val + u.2.val) : ℕ) : ZMod (p ^ 2)), f 2) = (0, 2)
  apply Prod.ext
  · rw [map_natCast]
    simp [Nat.cast_mul]
  · simpa only [Nat.cast_ofNat] using map_natCast f 2

theorem reduce_of_firstRegion {p : ℕ} {s : Residues p}
    (hs : s ∈ firstRegion p) : reduce p s = (0, 1) := by
  obtain ⟨y, rfl⟩ := hs
  exact reduce_firstPoint p y

theorem reduce_of_secondRegion {p : ℕ} {s : Residues p}
    (hs : s ∈ secondRegion p) : reduce p s = (0, 2) := by
  obtain ⟨u, rfl⟩ := hs
  exact reduce_secondPoint p u

noncomputable def outputEquiv {p : ℕ} (hlarge : 200 < p) :
    Residues p ≃ ZMod (p ^ 4) := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (by omega)⟩
  letI : NeZero (p ^ 4) := ⟨pow_ne_zero 4 (by omega)⟩
  apply Fintype.equivOfCardEq
  simp only [Residues, Fintype.card_prod, ZMod.card]
  ring

end PeriodicTilingThree.SharedSeed

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree.CommonModel

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

def ordinarySymbol (n : Column p) (x : Plane) : Symbol p :=
  lastDigit p E.p_prime (lineValue n x)

def ordinaryUseful (n : Column p) (x : Plane) (w : K E (.inl n)) : P E (.inl n) :=
  (channelDigitBlocks E (.inl n) (ordinarySymbol E n x)).C w

def ordinaryHigh (n : Column p) (x : Plane) (w : K E (.inl n)) : K E (.inl n) :=
  (channelDigitBlocks E (.inl n) (ordinarySymbol E n x)).T x.1 w

def ordinaryWord (x : Plane) : Word p := fun n => ordinarySymbol E n x

theorem ordinaryWord_allowed
    {p : ℕ} [NeZero p] (E : EncodingParameters p)
    (x : Plane) : Allowed p (ordinaryWord E x) := by
  have hword : ordinaryWord E x =
      (fun n : Column p => lastDigit p E.p_prime (x.1 * (n.val : ℤ) + x.2)) := by
    funext n
    change lastDigit p E.p_prime (lineValue n x) = _
    congr 1
    unfold lineValue
    ring
  rw [hword]
  exact lastDigit_affine_allowed p E.p_prime x.1 x.2

theorem ordinaryUseful_eq_of_lineValue_eq (n : Column p) {x y : Plane}
    (hxy : lineValue n x = lineValue n y) (w : K E (.inl n)) :
    ordinaryUseful E n x w = ordinaryUseful E n y w := by
  exact congrArg
    (fun t : ℤ => (channelDigitBlocks E (.inl n) (lastDigit p E.p_prime t)).C w) hxy

theorem ordinaryUseful_active_iff (n : Column p) (x : Plane) (j : Symbol p) :
    (∃ w w' : K E (.inl n), w - w' ∈ digitSubgroup E (.inl n) j ∧
      ordinaryUseful E n x w ≠ ordinaryUseful E n x w') ↔
        j = ordinarySymbol E n x :=
  channelDigitBlocks_active_iff E (.inl n) (ordinarySymbol E n x) j

theorem ordinarySymbol_offset (n : Column p) (x : Plane)
    (j : ActivationIndex E (.inl n)) :
    ordinarySymbol E n (x - ordinaryOffset E n j) = ordinarySymbol E n x := by
  unfold ordinarySymbol
  congr 1
  simp only [lineValue, ordinaryOffset, Prod.fst_sub, Prod.snd_sub]
  ring

theorem ordinaryUseful_offset (n : Column p) (x : Plane)
    (j : ActivationIndex E (.inl n)) (w : K E (.inl n)) :
    ordinaryUseful E n (x - ordinaryOffset E n j) w = ordinaryUseful E n x w := by
  exact congrArg (fun s : Symbol p => (channelDigitBlocks E (.inl n) s).C w)
    (ordinarySymbol_offset E n x j)

theorem ordinaryHigh_offset (n : Column p) (x : Plane)
    (j : ActivationIndex E (.inl n)) (w : K E (.inl n)) :
    ordinaryHigh E n (x - ordinaryOffset E n j) w =
      (channelDigitBlocks E (.inl n) (ordinarySymbol E n x)).T
        (x.1 - (ordinaryOffset E n j).1) w := by
  exact congrArg (fun s : Symbol p => (channelDigitBlocks E (.inl n) s).T
    (x.1 - (ordinaryOffset E n j).1) w) (ordinarySymbol_offset E n x j)

theorem ordinarySymbol_val_of_residue
    {p : ℕ} [NeZero p] (E : EncodingParameters p)
    (n : Column p) (x : Plane)
    (t : ZMod p) (ht : t ≠ 0)
    (hx₁ : (x.1 : ZMod p) = 0) (hx₂ : (x.2 : ZMod p) = t) :
    (ordinarySymbol E n x : ZMod p) = t := by
  have hv : (lineValue n x : ZMod p) = t := by
    simp [lineValue, hx₁, hx₂]
  have hnot : ¬ (p : ℤ) ∣ lineValue n x := by
    intro h
    have hz : (lineValue n x : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    exact ht (hv.symm.trans hz)
  exact (lastDigit_eq_of_not_dvd p E.p_prime hnot).trans hv

theorem reduce_residue
    {p : ℕ} [NeZero p]
    (x : Plane) :
    SharedSeed.reduce p (SharedSeed.residue p x) =
      ((x.1 : ZMod p), (x.2 : ZMod p)) := by
  simp [SharedSeed.reduce, SharedSeed.residue]

theorem ordinarySymbol_firstRegion (n : Column p) (x : Plane)
    (hx : SharedSeed.residue p x ∈ SharedSeed.firstRegion p) :
    ordinarySymbol E n x = 1 := by
  let : Fact (1 < p) := ⟨E.p_prime.one_lt⟩
  have h := SharedSeed.reduce_of_firstRegion hx
  rw [reduce_residue (p := p) x] at h
  apply Units.ext
  exact ordinarySymbol_val_of_residue E n x 1 one_ne_zero
    (congrArg Prod.fst h) (congrArg Prod.snd h)

theorem ordinarySymbol_secondRegion (n : Column p) (x : Plane)
    (hx : SharedSeed.residue p x ∈ SharedSeed.secondRegion p) :
    ordinarySymbol E n x = lastDigit p E.p_prime 2 := by
  have h := SharedSeed.reduce_of_secondRegion hx
  rw [reduce_residue (p := p) x] at h
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
    have hlarge := E.p_large
    omega
  apply Units.ext
  rw [lastDigit_two p E.p_prime (by have h := E.p_large; omega)]
  exact ordinarySymbol_val_of_residue E n x 2 htwo
    (congrArg Prod.fst h) (congrArg Prod.snd h)

end PeriodicTilingThree.CommonModel

end

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

structure BlockShiftData (Δ : Type uΔ) (a b : ℕ) where
  e : Δ → ZMod a × ZMod b
  rhoA : Δ → ZMod a
  rhoB : Δ → ZMod b
  orderA : Δ ≃ (ZMod b × ZMod a)
  orderB : Δ ≃ (ZMod a × ZMod b)
  orderA_apply : ∀ δ, orderA δ = ((e δ).2, (e δ).1 + rhoA δ)
  orderB_apply : ∀ δ, orderB δ = ((e δ).1, (e δ).2 + rhoB δ)

namespace BlockShiftData

noncomputable def ofMultiplicity {a b : ℕ} [NeZero a] [NeZero b]
    (ha : 2 ≤ a) (hb : 2 ≤ b) : BlockShiftData (ShiftIndex a b) a b where
  e := shift a b
  rhoA := PeriodicTilingThree.rhoA ha hb
  rhoB := PeriodicTilingThree.rhoB ha hb
  orderA := shiftOrderA ha hb
  orderB := shiftOrderB ha hb
  orderA_apply := shiftOrderA_apply ha hb
  orderB_apply := shiftOrderB_apply ha hb

variable {K : Type uK} {A : Type uA} {B : Type uB} {Δ : Type uΔ} [AddCommGroup K] {a b : ℕ}

def blockForward (D : LabeledBlocks K A B a b) (S : BlockShiftData Δ a b)
    (H : K × Δ → ℤ) (x : ℤ) (k : K) (z : K × Δ) :
    (ZMod a × ZMod b) × K :=
  (D.C (k - z.1) + S.e z.2, D.T (x - H z) (k - z.1))

def blockInverse (D : LabeledBlocks K A B a b) (S : BlockShiftData Δ a b)
    (x : ℤ) (k : K) (v : (ZMod a × ZMod b) × K) : K × Δ :=
  match D.decode v.2 with
  | .inl (c, q) =>
      let δ := S.orderA.symm (v.1.2, v.1.1 + (x : ZMod a) - q)
      (k - D.decode.symm (.inl (c, v.1.1 - (S.e δ).1)), δ)
  | .inr (c, q) =>
      let δ := S.orderB.symm (v.1.1, v.1.2 + (x : ZMod b) - q)
      (k - D.decode.symm (.inr (c, v.1.2 - (S.e δ).2)), δ)

theorem blockInverse_inl (D : LabeledBlocks K A B a b) (S : BlockShiftData Δ a b)
    (x : ℤ) (k : K) (α : ZMod a) (ξ : ZMod b) (c : A) (q : ZMod a) :
    blockInverse D S x k ((α, ξ), D.decode.symm (.inl (c, q))) =
      let δ := S.orderA.symm (ξ, α + (x : ZMod a) - q)
      (k - D.decode.symm (.inl (c, α - (S.e δ).1)), δ) := by
  simp only [blockInverse, Equiv.apply_symm_apply]

theorem blockInverse_inr (D : LabeledBlocks K A B a b) (S : BlockShiftData Δ a b)
    (x : ℤ) (k : K) (α : ZMod a) (ξ : ZMod b) (c : B) (q : ZMod b) :
    blockInverse D S x k ((α, ξ), D.decode.symm (.inr (c, q))) =
      let δ := S.orderB.symm (α, ξ + (x : ZMod b) - q)
      (k - D.decode.symm (.inr (c, ξ - (S.e δ).2)), δ) := by
  simp only [blockInverse, Equiv.apply_symm_apply]

theorem blockForward_inl (D : LabeledBlocks K A B a b) (S : BlockShiftData Δ a b)
    (H : K × Δ → ℤ) (hA : ∀ z, (H z : ZMod a) = S.rhoA z.2)
    (x : ℤ) (k : K) (c : A) (y : ZMod a) (δ : Δ) :
    blockForward D S H x k (k - D.decode.symm (.inl (c, y)), δ) =
      ((y + (S.e δ).1, (S.e δ).2),
        D.decode.symm (.inl (c, y + (x : ZMod a) - S.rhoA δ))) := by
  simp [blockForward, Int.cast_sub, hA, add_sub_assoc]
  apply Prod.ext <;> simp

theorem blockForward_inr (D : LabeledBlocks K A B a b) (S : BlockShiftData Δ a b)
    (H : K × Δ → ℤ) (hB : ∀ z, (H z : ZMod b) = S.rhoB z.2)
    (x : ℤ) (k : K) (c : B) (y : ZMod b) (δ : Δ) :
    blockForward D S H x k (k - D.decode.symm (.inr (c, y)), δ) =
      (((S.e δ).1, y + (S.e δ).2),
        D.decode.symm (.inr (c, y + (x : ZMod b) - S.rhoB δ))) := by
  simp [blockForward, Int.cast_sub, hB, add_sub_assoc]
  apply Prod.ext <;> simp

theorem recoverA (S : BlockShiftData Δ a b) (δ : Δ) (y t : ZMod a) :
    S.orderA.symm ((S.e δ).2, (y + (S.e δ).1) + t -
      (y + t - S.rhoA δ)) = δ := by
  apply S.orderA.injective
  rw [Equiv.apply_symm_apply, S.orderA_apply]
  apply Prod.ext
  · rfl
  · abel_nf

theorem recoverB (S : BlockShiftData Δ a b) (δ : Δ) (y t : ZMod b) :
    S.orderB.symm ((S.e δ).1, (y + (S.e δ).2) + t -
      (y + t - S.rhoB δ)) = δ := by
  apply S.orderB.injective
  rw [Equiv.apply_symm_apply, S.orderB_apply]
  apply Prod.ext
  · rfl
  · abel_nf

theorem blockInverse_forward_inl (D : LabeledBlocks K A B a b)
    (S : BlockShiftData Δ a b) (H : K × Δ → ℤ)
    (hA : ∀ z, (H z : ZMod a) = S.rhoA z.2)
    (x : ℤ) (k : K) (c : A) (y : ZMod a) (δ : Δ) :
    blockInverse D S x k
      (blockForward D S H x k (k - D.decode.symm (.inl (c, y)), δ)) =
      (k - D.decode.symm (.inl (c, y)), δ) := by
  rw [blockForward_inl D S H hA, blockInverse_inl]
  simp only [recoverA]
  simp

theorem blockInverse_forward_inr (D : LabeledBlocks K A B a b)
    (S : BlockShiftData Δ a b) (H : K × Δ → ℤ)
    (hB : ∀ z, (H z : ZMod b) = S.rhoB z.2)
    (x : ℤ) (k : K) (c : B) (y : ZMod b) (δ : Δ) :
    blockInverse D S x k
      (blockForward D S H x k (k - D.decode.symm (.inr (c, y)), δ)) =
      (k - D.decode.symm (.inr (c, y)), δ) := by
  rw [blockForward_inr D S H hB, blockInverse_inr]
  simp only [recoverB]
  simp

theorem blockInverse_forward (D : LabeledBlocks K A B a b)
    (S : BlockShiftData Δ a b) (H : K × Δ → ℤ)
    (hA : ∀ z, (H z : ZMod a) = S.rhoA z.2)
    (hB : ∀ z, (H z : ZMod b) = S.rhoB z.2)
    (x : ℤ) (k : K) :
    Function.LeftInverse (blockInverse D S x k) (blockForward D S H x k) := by
  rintro ⟨l, δ⟩
  cases he : D.decode (k - l) with
  | inl v =>
      rcases v with ⟨c, y⟩
      have hu : D.decode.symm (.inl (c, y)) = k - l := by
        simpa only [he] using D.decode.symm_apply_apply (k - l)
      simpa only [hu, sub_sub_cancel] using blockInverse_forward_inl D S H hA x k c y δ
  | inr v =>
      rcases v with ⟨c, y⟩
      have hu : D.decode.symm (.inr (c, y)) = k - l := by
        simpa only [he] using D.decode.symm_apply_apply (k - l)
      simpa only [hu, sub_sub_cancel] using blockInverse_forward_inr D S H hB x k c y δ

theorem blockForward_inverse_inl (D : LabeledBlocks K A B a b)
    (S : BlockShiftData Δ a b) (H : K × Δ → ℤ)
    (hA : ∀ z, (H z : ZMod a) = S.rhoA z.2)
    (x : ℤ) (k : K) (α : ZMod a) (ξ : ZMod b) (c : A) (q : ZMod a) :
    blockForward D S H x k
      (blockInverse D S x k ((α, ξ), D.decode.symm (.inl (c, q)))) =
      ((α, ξ), D.decode.symm (.inl (c, q))) := by
  let δ := S.orderA.symm (ξ, α + (x : ZMod a) - q)
  have horder : ((S.e δ).2, (S.e δ).1 + S.rhoA δ) =
      (ξ, α + (x : ZMod a) - q) :=
    (S.orderA_apply δ).symm.trans (S.orderA.apply_symm_apply _)
  have he : (S.e δ).2 = ξ := congrArg Prod.fst horder
  have hr : (S.e δ).1 + S.rhoA δ = α + (x : ZMod a) - q :=
    congrArg Prod.snd horder
  have hlabel : (α - (S.e δ).1) + (x : ZMod a) - S.rhoA δ = q := by
    calc
      _ = (α + (x : ZMod a)) - ((S.e δ).1 + S.rhoA δ) := by abel
      _ = (α + (x : ZMod a)) - (α + (x : ZMod a) - q) := by rw [hr]
      _ = q := sub_sub_cancel _ _
  rw [blockInverse_inl]
  change blockForward D S H x k
    (k - D.decode.symm (.inl (c, α - (S.e δ).1)), δ) = _
  rw [blockForward_inl D S H hA]
  simp only [sub_add_cancel, he, hlabel]

theorem blockForward_inverse_inr (D : LabeledBlocks K A B a b)
    (S : BlockShiftData Δ a b) (H : K × Δ → ℤ)
    (hB : ∀ z, (H z : ZMod b) = S.rhoB z.2)
    (x : ℤ) (k : K) (α : ZMod a) (ξ : ZMod b) (c : B) (q : ZMod b) :
    blockForward D S H x k
      (blockInverse D S x k ((α, ξ), D.decode.symm (.inr (c, q)))) =
      ((α, ξ), D.decode.symm (.inr (c, q))) := by
  let δ := S.orderB.symm (α, ξ + (x : ZMod b) - q)
  have horder : ((S.e δ).1, (S.e δ).2 + S.rhoB δ) =
      (α, ξ + (x : ZMod b) - q) :=
    (S.orderB_apply δ).symm.trans (S.orderB.apply_symm_apply _)
  have he : (S.e δ).1 = α := congrArg Prod.fst horder
  have hr : (S.e δ).2 + S.rhoB δ = ξ + (x : ZMod b) - q :=
    congrArg Prod.snd horder
  have hlabel : (ξ - (S.e δ).2) + (x : ZMod b) - S.rhoB δ = q := by
    calc
      _ = (ξ + (x : ZMod b)) - ((S.e δ).2 + S.rhoB δ) := by abel
      _ = (ξ + (x : ZMod b)) - (ξ + (x : ZMod b) - q) := by rw [hr]
      _ = q := sub_sub_cancel _ _
  rw [blockInverse_inr]
  change blockForward D S H x k
    (k - D.decode.symm (.inr (c, ξ - (S.e δ).2)), δ) = _
  rw [blockForward_inr D S H hB]
  simp only [sub_add_cancel, he, hlabel]

theorem blockForward_inverse (D : LabeledBlocks K A B a b)
    (S : BlockShiftData Δ a b) (H : K × Δ → ℤ)
    (hA : ∀ z, (H z : ZMod a) = S.rhoA z.2)
    (hB : ∀ z, (H z : ZMod b) = S.rhoB z.2)
    (x : ℤ) (k : K) :
    Function.RightInverse (blockInverse D S x k) (blockForward D S H x k) := by
  rintro ⟨⟨α, ξ⟩, β⟩
  cases he : D.decode β with
  | inl v =>
      rcases v with ⟨c, q⟩
      have hβ : D.decode.symm (.inl (c, q)) = β := by
        simpa only [he] using D.decode.symm_apply_apply β
      simpa only [hβ] using blockForward_inverse_inl D S H hA x k α ξ c q
  | inr v =>
      rcases v with ⟨c, q⟩
      have hβ : D.decode.symm (.inr (c, q)) = β := by
        simpa only [he] using D.decode.symm_apply_apply β
      simpa only [hβ] using blockForward_inverse_inr D S H hB x k α ξ c q

def blockInverseEquiv (D : LabeledBlocks K A B a b) (S : BlockShiftData Δ a b)
    (H : K × Δ → ℤ) (hA : ∀ z, (H z : ZMod a) = S.rhoA z.2)
    (hB : ∀ z, (H z : ZMod b) = S.rhoB z.2) (x : ℤ) (k : K) :
    (K × Δ) ≃ ((ZMod a × ZMod b) × K) where
  toFun := blockForward D S H x k
  invFun := blockInverse D S x k
  left_inv := blockInverse_forward D S H hA hB x k
  right_inv := blockForward_inverse D S H hA hB x k

@[simp] theorem blockInverseEquiv_apply (D : LabeledBlocks K A B a b)
    (S : BlockShiftData Δ a b) (H : K × Δ → ℤ)
    (hA : ∀ z, (H z : ZMod a) = S.rhoA z.2)
    (hB : ∀ z, (H z : ZMod b) = S.rhoB z.2) (x : ℤ) (k : K) (z : K × Δ) :
    blockInverseEquiv D S H hA hB x k z =
      (D.C (k - z.1) + S.e z.2, D.T (x - H z) (k - z.1)) := rfl

@[simp] theorem blockInverseEquiv_symm_apply (D : LabeledBlocks K A B a b)
    (S : BlockShiftData Δ a b) (H : K × Δ → ℤ)
    (hA : ∀ z, (H z : ZMod a) = S.rhoA z.2)
    (hB : ∀ z, (H z : ZMod b) = S.rhoB z.2)
    (x : ℤ) (k : K) (v : (ZMod a × ZMod b) × K) :
    (blockInverseEquiv D S H hA hB x k).symm v = blockInverse D S x k v := rfl

end BlockShiftData

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree.CommonModel

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

def ordinaryForward (n : Column p) (x : Plane) (k : K E (.inl n))
    (j : ActivationIndex E (.inl n)) : P E (.inl n) × K E (.inl n) :=
  (ordinaryUseful E n (x - ordinaryOffset E n j) (k - j.1) +
    shift (E.a (.inl n)) (E.b (.inl n)) j.2,
    ordinaryHigh E n (x - ordinaryOffset E n j) (k - j.1))

theorem ordinaryForward_bijective (n : Column p) (x : Plane) (k : K E (.inl n)) :
    Function.Bijective (ordinaryForward E n x k) := by
  let D := channelDigitBlocks E (.inl n) (ordinarySymbol E n x)
  let S := BlockShiftData.ofMultiplicity
    (E.a_two_le (.inl n)) (E.b_two_le (.inl n))
  let e := BlockShiftData.blockInverseEquiv D S
    (fun j => (ordinaryOffset E n j).1)
    (fun j => ordinaryOffset_rhoA E n j)
    (fun j => ordinaryOffset_rhoB E n j) x.1 k
  have he : ordinaryForward E n x k = e := by
    funext j
    simp only [ordinaryForward, ordinaryUseful_offset, ordinaryHigh_offset]
    rfl
  rw [he]
  exact e.bijective

end PeriodicTilingThree.CommonModel

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace PeriodicTilingThree.SharedSeed

def ActiveOne {m : ℕ} : LabelledResidue m → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

def ActiveTwo {m : ℕ} : LabelledResidue m → Prop
  | Sum.inl _ => False
  | Sum.inr (Sum.inl _) => True
  | Sum.inr (Sum.inr _) => False

def firstLabel {m : ℕ} : LabelledResidue m → ZMod 2
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl v) => v.2
  | Sum.inr (Sum.inr v) => v.2.1

def secondLabel {m : ℕ} : LabelledResidue m → ZMod 3
  | Sum.inl y => y
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr v) => v.2.2

def rotateMap {m : ℕ} (t : ℤ) : LabelledResidue m → LabelledResidue m
  | Sum.inl y => Sum.inl (y + (t : ZMod 3))
  | Sum.inr (Sum.inl (c, y)) => Sum.inr (Sum.inl (c, y + (t : ZMod 2)))
  | Sum.inr (Sum.inr (c, y, z)) =>
      Sum.inr (Sum.inr (c, y + (t : ZMod 2), z + (t : ZMod 3)))

@[simp] theorem rotateMap_zero {m : ℕ} (s : LabelledResidue m) :
    rotateMap 0 s = s := by
  rcases s with y | (⟨c, y⟩ | ⟨c, y, z⟩) <;> simp [rotateMap]

theorem rotateMap_add {m : ℕ} (t u : ℤ) (s : LabelledResidue m) :
    rotateMap (t + u) s = rotateMap t (rotateMap u s) := by
  rcases s with y | (⟨c, y⟩ | ⟨c, y, z⟩) <;>
    simp [rotateMap, Int.cast_add, add_comm, add_left_comm]

def rotate {m : ℕ} (t : ℤ) : Equiv.Perm (LabelledResidue m) where
  toFun := rotateMap t
  invFun := rotateMap (-t)
  left_inv s := by rw [← rotateMap_add, neg_add_cancel, rotateMap_zero]
  right_inv s := by rw [← rotateMap_add, add_neg_cancel, rotateMap_zero]

@[simp] theorem rotate_apply {m : ℕ} (t : ℤ) (s : LabelledResidue m) :
    rotate t s = rotateMap t s := rfl

@[simp] theorem rotate_zero {m : ℕ} (s : LabelledResidue m) : rotate 0 s = s :=
  rotateMap_zero s

theorem rotate_add {m : ℕ} (t u : ℤ) (s : LabelledResidue m) :
    rotate (t + u) s = rotate t (rotate u s) := rotateMap_add t u s

@[simp] theorem activeOne_rotate {m : ℕ} (t : ℤ) (s : LabelledResidue m) :
    ActiveOne (rotate t s) ↔ ActiveOne s := by
  rcases s with y | (⟨c, y⟩ | ⟨c, y, z⟩) <;> rfl

@[simp] theorem activeTwo_rotate {m : ℕ} (t : ℤ) (s : LabelledResidue m) :
    ActiveTwo (rotate t s) ↔ ActiveTwo s := by
  rcases s with y | (⟨c, y⟩ | ⟨c, y, z⟩) <;> rfl

theorem firstLabel_rotate {m : ℕ} (t : ℤ) (s : LabelledResidue m)
    (hs : ¬ ActiveOne s) : firstLabel (rotate t s) = firstLabel s + (t : ZMod 2) := by
  rcases s with y | (⟨c, y⟩ | ⟨c, y, z⟩)
  · exact False.elim (hs trivial)
  · rfl
  · rfl

theorem secondLabel_rotate {m : ℕ} (t : ℤ) (s : LabelledResidue m)
    (hs : ¬ ActiveTwo s) : secondLabel (rotate t s) = secondLabel s + (t : ZMod 3) := by
  rcases s with y | (⟨c, y⟩ | ⟨c, y, z⟩)
  · rfl
  · exact False.elim (hs trivial)
  · rfl

theorem rotate_fixed_on_activeOne {m : ℕ} {t : ℤ} {s : LabelledResidue m}
    (hs : ActiveOne s) (ht : (t : ZMod 3) = 0) : rotate t s = s := by
  rcases s with y | (⟨c, y⟩ | ⟨c, y, z⟩)
  · simp [rotate, rotateMap, ht]
  · exact False.elim hs
  · exact False.elim hs

theorem rotate_fixed_on_activeTwo {m : ℕ} {t : ℤ} {s : LabelledResidue m}
    (hs : ActiveTwo s) (ht : (t : ZMod 2) = 0) : rotate t s = s := by
  rcases s with y | (⟨c, y⟩ | ⟨c, y, z⟩)
  · exact False.elim hs
  · simp [rotate, rotateMap, ht]
  · exact False.elim hs

def rotation {S : Type uS} {m : ℕ} (e : S ≃ LabelledResidue m) (t : ℤ) : Equiv.Perm S :=
  (e.trans (rotate t)).trans e.symm

@[simp] theorem rotation_apply {S : Type uS} {m : ℕ}
    (e : S ≃ LabelledResidue m) (t : ℤ) (s : S) :
    rotation e t s = e.symm (rotate t (e s)) := rfl

@[simp] theorem label_rotation {S : Type uS} {m : ℕ}
    (e : S ≃ LabelledResidue m) (t : ℤ) (s : S) :
    e (rotation e t s) = rotate t (e s) := e.apply_symm_apply _

theorem rotation_add {S : Type uS} {m : ℕ}
    (e : S ≃ LabelledResidue m) (t u : ℤ) (s : S) :
    rotation e (t + u) s = rotation e t (rotation e u s) := by
  simp only [rotation_apply, Equiv.apply_symm_apply, rotate_add]

def sharedOutput {S : Type uS} {m D : ℕ}
    (e : S ≃ LabelledResidue m) (code : S ≃ ZMod D) (t : ℤ) (s : S) : ZMod D :=
  code (rotation e t s)

@[simp] theorem decode_sharedOutput {S : Type uS} {m D : ℕ}
    (e : S ≃ LabelledResidue m) (code : S ≃ ZMod D) (t : ℤ) (s : S) :
    e (code.symm (sharedOutput e code t s)) = rotate t (e s) := by
  simp only [sharedOutput, Equiv.symm_apply_apply, label_rotation]

def sharedZ {p m : ℕ} {K : Type uK}
    (e : Residues p ≃ LabelledResidue m) (code : Residues p ≃ ZMod (p ^ 4))
    (x : Plane) (_k : K) : ZMod (p ^ 4) :=
  sharedOutput e code x.1 ((x.1 : ZMod (p ^ 2)), (x.2 : ZMod (p ^ 2)))

def commonZ {p : ℕ} {K : Type uK} (hp : p.Prime) (hlarge : 200 < p)
    (x : Plane) (_k : K) : ZMod (p ^ 4) :=
  sharedOutput (residueEquiv hp hlarge) (outputEquiv hlarge) x.1 (residue p x)

end PeriodicTilingThree.SharedSeed

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace PeriodicTilingThree.SharedSeed

variable {K : Type uK} {Δ : Type uΔ} [AddCommGroup K] {a b : ℕ}

def inactiveForward (S : BlockShiftData Δ a b) (x : ZMod a) (k : K)
    (v : (K × Δ) × ZMod a) : ((ZMod a × ZMod b) × K) × ZMod a :=
  ((((v.2 + (S.e v.1.2).1), (S.e v.1.2).2), k - v.1.1),
    v.2 + x - S.rhoA v.1.2)

def inactiveInverse (S : BlockShiftData Δ a b) (x : ZMod a) (k : K)
    (v : ((ZMod a × ZMod b) × K) × ZMod a) : (K × Δ) × ZMod a :=
  let δ := S.orderA.symm (v.1.1.2, v.1.1.1 + x - v.2)
  ((k - v.1.2, δ), v.1.1.1 - (S.e δ).1)

theorem inactiveInverse_forward (S : BlockShiftData Δ a b) (x : ZMod a) (k : K)
    (v : (K × Δ) × ZMod a) :
    inactiveInverse S x k (inactiveForward S x k v) = v := by
  rcases v with ⟨⟨l, δ⟩, y⟩
  have hd : S.orderA.symm ((S.e δ).2,
      (y + (S.e δ).1) + x - (y + x - S.rhoA δ)) = δ := by
    apply S.orderA.injective
    rw [Equiv.apply_symm_apply, S.orderA_apply]
    apply Prod.ext
    · rfl
    · abel_nf
  dsimp [inactiveInverse, inactiveForward]
  rw [hd]
  simp

theorem inactiveForward_inverse (S : BlockShiftData Δ a b) (x : ZMod a) (k : K)
    (v : ((ZMod a × ZMod b) × K) × ZMod a) :
    inactiveForward S x k (inactiveInverse S x k v) = v := by
  rcases v with ⟨⟨⟨α, ξ⟩, β⟩, q⟩
  let δ := S.orderA.symm (ξ, α + x - q)
  have hd : ((S.e δ).2, (S.e δ).1 + S.rhoA δ) = (ξ, α + x - q) := by
    rw [← S.orderA_apply]
    exact S.orderA.apply_symm_apply _
  have hb : (S.e δ).2 = ξ := congrArg Prod.fst hd
  have ha : (S.e δ).1 + S.rhoA δ = α + x - q := congrArg Prod.snd hd
  have hq : α - (S.e δ).1 + x - S.rhoA δ = q := by
    calc
      α - (S.e δ).1 + x - S.rhoA δ = α + x - ((S.e δ).1 + S.rhoA δ) := by abel
      _ = α + x - (α + x - q) := by rw [ha]
      _ = q := by abel
  change ((((α - (S.e δ).1 + (S.e δ).1), (S.e δ).2), k - (k - β)),
    α - (S.e δ).1 + x - S.rhoA δ) = (((α, ξ), β), q)
  simp only [sub_add_cancel, sub_sub_cancel, hb, hq]

def inactiveEquiv (S : BlockShiftData Δ a b) (x : ZMod a) (k : K) :
    ((K × Δ) × ZMod a) ≃ (((ZMod a × ZMod b) × K) × ZMod a) where
  toFun := inactiveForward S x k
  invFun := inactiveInverse S x k
  left_inv := inactiveInverse_forward S x k
  right_inv := inactiveForward_inverse S x k

end PeriodicTilingThree.SharedSeed

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace PeriodicTilingThree.SharedSeed

variable {K : Type uK} {Δ : Type uΔ} [AddCommGroup K] {m b : ℕ}

def oneLabelEquiv (S : BlockShiftData Δ 2 b) (x : ℤ) (k : K)
    (B : ZMod 3 → (K × Δ) ≃ ((ZMod 2 × ZMod b) × K)) :
    ((K × Δ) × LabelledResidue m) ≃ (((ZMod 2 × ZMod b) × K) × LabelledResidue m) where
  toFun
    | (v, Sum.inl y) => (B y v, Sum.inl (y + (x : ZMod 3)))
    | (v, Sum.inr (Sum.inl (c, y))) =>
        let w := inactiveEquiv S (x : ZMod 2) k (v, y)
        (w.1, Sum.inr (Sum.inl (c, w.2)))
    | (v, Sum.inr (Sum.inr (c, y, z))) =>
        let w := inactiveEquiv S (x : ZMod 2) k (v, y)
        (w.1, Sum.inr (Sum.inr (c, w.2, z + (x : ZMod 3))))
  invFun
    | (v, Sum.inl q) => ((B (q - (x : ZMod 3))).symm v, Sum.inl (q - (x : ZMod 3)))
    | (v, Sum.inr (Sum.inl (c, q))) =>
        let w := (inactiveEquiv S (x : ZMod 2) k).symm (v, q)
        (w.1, Sum.inr (Sum.inl (c, w.2)))
    | (v, Sum.inr (Sum.inr (c, q, r))) =>
        let w := (inactiveEquiv S (x : ZMod 2) k).symm (v, q)
        (w.1, Sum.inr (Sum.inr (c, w.2, r - (x : ZMod 3))))
  left_inv v := by
    rcases v with ⟨v, y | (⟨c, y⟩ | ⟨c, y, z⟩)⟩
    · simp only [add_sub_cancel_right, Equiv.symm_apply_apply]
    · simp only [Prod.mk.eta, Equiv.symm_apply_apply]
    · simp only [Prod.mk.eta, Equiv.symm_apply_apply, add_sub_cancel_right]
  right_inv v := by
    rcases v with ⟨v, q | (⟨c, q⟩ | ⟨c, q, r⟩)⟩
    · simp only [Equiv.apply_symm_apply, sub_add_cancel]
    · simp only [Prod.mk.eta, Equiv.apply_symm_apply]
    · simp only [Prod.mk.eta, Equiv.apply_symm_apply, sub_add_cancel]

def twoLabelEquiv (S : BlockShiftData Δ 3 b) (x : ℤ) (k : K)
    (B : (Fin 2 × ZMod 2) → (K × Δ) ≃ ((ZMod 3 × ZMod b) × K)) :
    ((K × Δ) × LabelledResidue m) ≃ (((ZMod 3 × ZMod b) × K) × LabelledResidue m) where
  toFun
    | (v, Sum.inl y) =>
        let w := inactiveEquiv S (x : ZMod 3) k (v, y)
        (w.1, Sum.inl w.2)
    | (v, Sum.inr (Sum.inl (c, y))) =>
        (B (c, y) v, Sum.inr (Sum.inl (c, y + (x : ZMod 2))))
    | (v, Sum.inr (Sum.inr (c, y, z))) =>
        let w := inactiveEquiv S (x : ZMod 3) k (v, z)
        (w.1, Sum.inr (Sum.inr (c, y + (x : ZMod 2), w.2)))
  invFun
    | (v, Sum.inl q) =>
        let w := (inactiveEquiv S (x : ZMod 3) k).symm (v, q)
        (w.1, Sum.inl w.2)
    | (v, Sum.inr (Sum.inl (c, q))) =>
        ((B (c, q - (x : ZMod 2))).symm v,
          Sum.inr (Sum.inl (c, q - (x : ZMod 2))))
    | (v, Sum.inr (Sum.inr (c, q, r))) =>
        let w := (inactiveEquiv S (x : ZMod 3) k).symm (v, r)
        (w.1, Sum.inr (Sum.inr (c, q - (x : ZMod 2), w.2)))
  left_inv v := by
    rcases v with ⟨v, y | (⟨c, y⟩ | ⟨c, y, z⟩)⟩
    · simp only [Prod.mk.eta, Equiv.symm_apply_apply]
    · simp only [add_sub_cancel_right, Equiv.symm_apply_apply]
    · simp only [Prod.mk.eta, Equiv.symm_apply_apply, add_sub_cancel_right]
  right_inv v := by
    rcases v with ⟨v, q | (⟨c, q⟩ | ⟨c, q, r⟩)⟩
    · simp only [Prod.mk.eta, Equiv.apply_symm_apply]
    · simp only [Equiv.apply_symm_apply, sub_add_cancel]
    · simp only [Prod.mk.eta, Equiv.apply_symm_apply, sub_add_cancel]

end PeriodicTilingThree.SharedSeed

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace PeriodicTilingThree.SharedSeed

variable {K : Type uK} {Δ : Type uΔ} {A : Type uA} {B : Type uB} {R : Type uR}
  [AddCommGroup K] [AddCommGroup R] {m b n : ℕ}

def sourceResidueEquiv (sx : R) (e : R ≃ LabelledResidue m) : R ≃ LabelledResidue m where
  toFun τ := e (sx - τ)
  invFun s := sx - e.symm s
  left_inv τ := by simp
  right_inv s := by simp

@[simp] theorem sourceResidueEquiv_apply (sx : R) (e : R ≃ LabelledResidue m) (τ : R) :
    sourceResidueEquiv sx e τ = e (sx - τ) := rfl

@[simp] theorem sourceResidueEquiv_symm_apply (sx : R) (e : R ≃ LabelledResidue m)
    (s : LabelledResidue m) : (sourceResidueEquiv sx e).symm s = sx - e.symm s := rfl

def usefulOne (D : LabeledBlocks K A B 2 b) (u : K) : LabelledResidue m → ZMod 2 × ZMod b
  | Sum.inl _ => D.C u
  | Sum.inr (Sum.inl (_, y)) => (y, 0)
  | Sum.inr (Sum.inr (_, y, _)) => (y, 0)

def highOne (D : LabeledBlocks K A B 2 b) (t : ℤ) (u : K) : LabelledResidue m → K
  | Sum.inl _ => D.T t u
  | Sum.inr _ => u

def usefulTwo (D : LabeledBlocks K A B 3 b) (u : K) : LabelledResidue m → ZMod 3 × ZMod b
  | Sum.inl y => (y, 0)
  | Sum.inr (Sum.inl _) => D.C u
  | Sum.inr (Sum.inr (_, _, y)) => (y, 0)

def highTwo (D : LabeledBlocks K A B 3 b) (t : ℤ) (u : K) : LabelledResidue m → K
  | Sum.inl _ => u
  | Sum.inr (Sum.inl _) => D.T t u
  | Sum.inr (Sum.inr _) => u

def oneForward (D : LabeledBlocks K A B 2 b) (S : BlockShiftData Δ 2 b)
    (e : R ≃ LabelledResidue m) (code : R ≃ ZMod n)
    (H : (K × Δ) × R → ℤ) (x : ℤ) (sx : R) (k : K)
    (v : (K × Δ) × R) : ((ZMod 2 × ZMod b) × K) × ZMod n :=
  let s := e (sx - v.2)
  let u := k - v.1.1
  let t := x - H v
  ((usefulOne D u s + S.e v.1.2, highOne D t u s),
    sharedOutput e code t (sx - v.2))

def twoForward (D : LabeledBlocks K A B 3 b) (S : BlockShiftData Δ 3 b)
    (e : R ≃ LabelledResidue m) (code : R ≃ ZMod n)
    (H : (K × Δ) × R → ℤ) (x : ℤ) (sx : R) (k : K)
    (v : (K × Δ) × R) : ((ZMod 3 × ZMod b) × K) × ZMod n :=
  let s := e (sx - v.2)
  let u := k - v.1.1
  let t := x - H v
  ((usefulTwo D u s + S.e v.1.2, highTwo D t u s),
    sharedOutput e code t (sx - v.2))

def oneActivationEquiv (D : LabeledBlocks K A B 2 b) (S : BlockShiftData Δ 2 b)
    (e : R ≃ LabelledResidue m) (code : R ≃ ZMod n)
    (H : (K × Δ) × R → ℤ)
    (hA : ∀ v, (H v : ZMod 2) = S.rhoA v.1.2)
    (hB : ∀ v, (H v : ZMod b) = S.rhoB v.1.2)
    (x : ℤ) (sx : R) (k : K) :
    ((K × Δ) × R) ≃ (((ZMod 2 × ZMod b) × K) × ZMod n) :=
  let E := sourceResidueEquiv sx e
  let blocks := fun y : ZMod 3 =>
    BlockShiftData.blockInverseEquiv D S (fun v => H (v, E.symm (Sum.inl y)))
      (fun v => hA (v, E.symm (Sum.inl y)))
      (fun v => hB (v, E.symm (Sum.inl y))) x k
  ((Equiv.prodCongr (Equiv.refl (K × Δ)) E).trans
    (oneLabelEquiv S x k blocks)).trans
      (Equiv.prodCongr (Equiv.refl ((ZMod 2 × ZMod b) × K)) (e.symm.trans code))

def twoActivationEquiv (D : LabeledBlocks K A B 3 b) (S : BlockShiftData Δ 3 b)
    (e : R ≃ LabelledResidue m) (code : R ≃ ZMod n)
    (H : (K × Δ) × R → ℤ)
    (hA : ∀ v, (H v : ZMod 3) = S.rhoA v.1.2)
    (hB : ∀ v, (H v : ZMod b) = S.rhoB v.1.2)
    (x : ℤ) (sx : R) (k : K) :
    ((K × Δ) × R) ≃ (((ZMod 3 × ZMod b) × K) × ZMod n) :=
  let E := sourceResidueEquiv sx e
  let blocks := fun y : Fin 2 × ZMod 2 =>
    BlockShiftData.blockInverseEquiv D S (fun v => H (v, E.symm (Sum.inr (Sum.inl y))))
      (fun v => hA (v, E.symm (Sum.inr (Sum.inl y))))
      (fun v => hB (v, E.symm (Sum.inr (Sum.inl y)))) x k
  ((Equiv.prodCongr (Equiv.refl (K × Δ)) E).trans
    (twoLabelEquiv S x k blocks)).trans
      (Equiv.prodCongr (Equiv.refl ((ZMod 3 × ZMod b) × K)) (e.symm.trans code))

theorem oneActivationEquiv_apply
    (D : LabeledBlocks K A B 2 b) (S : BlockShiftData Δ 2 b)
    (e : R ≃ LabelledResidue m) (code : R ≃ ZMod n)
    (H : (K × Δ) × R → ℤ)
    (hA : ∀ v, (H v : ZMod 2) = S.rhoA v.1.2)
    (hB : ∀ v, (H v : ZMod b) = S.rhoB v.1.2)
    (hOther : ∀ v, (H v : ZMod 3) = 0)
    (x : ℤ) (sx : R) (k : K) (v : (K × Δ) × R) :
    oneActivationEquiv D S e code H hA hB x sx k v =
      oneForward D S e code H x sx k v := by
  rcases v with ⟨⟨l, δ⟩, τ⟩
  have hback : sx - e.symm (e (sx - τ)) = τ := by simp
  cases hs : e (sx - τ) with
  | inl y =>
      rw [hs] at hback
      simp [oneActivationEquiv, oneLabelEquiv, sourceResidueEquiv,
        BlockShiftData.blockInverseEquiv, BlockShiftData.blockForward,
        oneForward, usefulOne, highOne, sharedOutput, rotation, rotate, rotateMap,
        hs, hback, Int.cast_sub, hOther]
  | inr s =>
      cases s with
      | inl cy =>
          rcases cy with ⟨c, y⟩
          simp [oneActivationEquiv, oneLabelEquiv, sourceResidueEquiv,
            inactiveEquiv, inactiveForward, oneForward, usefulOne, highOne,
            sharedOutput, rotation, rotate, rotateMap, hs, Int.cast_sub, hA,
            add_sub_assoc, Prod.add_def]
      | inr cyz =>
          rcases cyz with ⟨c, y, z⟩
          simp [oneActivationEquiv, oneLabelEquiv, sourceResidueEquiv,
            inactiveEquiv, inactiveForward, oneForward, usefulOne, highOne,
            sharedOutput, rotation, rotate, rotateMap, hs, Int.cast_sub, hA, hOther,
            add_sub_assoc, Prod.add_def]

theorem twoActivationEquiv_apply
    (D : LabeledBlocks K A B 3 b) (S : BlockShiftData Δ 3 b)
    (e : R ≃ LabelledResidue m) (code : R ≃ ZMod n)
    (H : (K × Δ) × R → ℤ)
    (hA : ∀ v, (H v : ZMod 3) = S.rhoA v.1.2)
    (hB : ∀ v, (H v : ZMod b) = S.rhoB v.1.2)
    (hOther : ∀ v, (H v : ZMod 2) = 0)
    (x : ℤ) (sx : R) (k : K) (v : (K × Δ) × R) :
    twoActivationEquiv D S e code H hA hB x sx k v =
      twoForward D S e code H x sx k v := by
  rcases v with ⟨⟨l, δ⟩, τ⟩
  have hback : sx - e.symm (e (sx - τ)) = τ := by simp
  cases hs : e (sx - τ) with
  | inl y =>
      simp [twoActivationEquiv, twoLabelEquiv, sourceResidueEquiv,
        inactiveEquiv, inactiveForward, twoForward, usefulTwo, highTwo,
        sharedOutput, rotation, rotate, rotateMap, hs, Int.cast_sub, hA,
        add_sub_assoc, Prod.add_def]
  | inr s =>
      cases s with
      | inl cy =>
          rcases cy with ⟨c, y⟩
          rw [hs] at hback
          simp [twoActivationEquiv, twoLabelEquiv, sourceResidueEquiv,
            BlockShiftData.blockInverseEquiv, BlockShiftData.blockForward,
            twoForward, usefulTwo, highTwo, sharedOutput, rotation, rotate, rotateMap,
            hs, hback, Int.cast_sub, hOther]
      | inr cyz =>
          rcases cyz with ⟨c, y, z⟩
          simp [twoActivationEquiv, twoLabelEquiv, sourceResidueEquiv,
            inactiveEquiv, inactiveForward, twoForward, usefulTwo, highTwo,
            sharedOutput, rotation, rotate, rotateMap, hs, Int.cast_sub, hA, hOther,
            add_sub_assoc, Prod.add_def]

theorem oneForward_bijective
    (D : LabeledBlocks K A B 2 b) (S : BlockShiftData Δ 2 b)
    (e : R ≃ LabelledResidue m) (code : R ≃ ZMod n)
    (H : (K × Δ) × R → ℤ)
    (hA : ∀ v, (H v : ZMod 2) = S.rhoA v.1.2)
    (hB : ∀ v, (H v : ZMod b) = S.rhoB v.1.2)
    (hOther : ∀ v, (H v : ZMod 3) = 0) (x : ℤ) (sx : R) (k : K) :
    Function.Bijective (oneForward D S e code H x sx k) := by
  have he : oneForward D S e code H x sx k =
      oneActivationEquiv D S e code H hA hB x sx k :=
    funext fun v => (oneActivationEquiv_apply D S e code H hA hB hOther x sx k v).symm
  rw [he]
  exact (oneActivationEquiv D S e code H hA hB x sx k).bijective

theorem twoForward_bijective
    (D : LabeledBlocks K A B 3 b) (S : BlockShiftData Δ 3 b)
    (e : R ≃ LabelledResidue m) (code : R ≃ ZMod n)
    (H : (K × Δ) × R → ℤ)
    (hA : ∀ v, (H v : ZMod 3) = S.rhoA v.1.2)
    (hB : ∀ v, (H v : ZMod b) = S.rhoB v.1.2)
    (hOther : ∀ v, (H v : ZMod 2) = 0) (x : ℤ) (sx : R) (k : K) :
    Function.Bijective (twoForward D S e code H x sx k) := by
  have he : twoForward D S e code H x sx k =
      twoActivationEquiv D S e code H hA hB x sx k :=
    funext fun v => (twoActivationEquiv_apply D S e code H hA hB hOther x sx k v).symm
  rw [he]
  exact (twoActivationEquiv D S e code H hA hB x sx k).bijective

end PeriodicTilingThree.SharedSeed

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace PeriodicTilingThree.SharedSeed

variable {K : Type uK} {Δ : Type uΔ} {A : Type uA} {B : Type uB} {R : Type uR}
  [AddCommGroup K] [AddCommGroup R] {a b m n : ℕ}

def usefulOneOfEq (ha : a = 2) (D : LabeledBlocks K A B a b)
    (u : K) (s : LabelledResidue m) : ZMod a × ZMod b := by
  subst a
  exact usefulOne D u s

def highOneOfEq (ha : a = 2) (D : LabeledBlocks K A B a b)
    (t : ℤ) (u : K) (s : LabelledResidue m) : K := by
  subst a
  exact highOne D t u s

def usefulTwoOfEq (ha : a = 3) (D : LabeledBlocks K A B a b)
    (u : K) (s : LabelledResidue m) : ZMod a × ZMod b := by
  subst a
  exact usefulTwo D u s

def highTwoOfEq (ha : a = 3) (D : LabeledBlocks K A B a b)
    (t : ℤ) (u : K) (s : LabelledResidue m) : K := by
  subst a
  exact highTwo D t u s

def oneForwardOfEq (ha : a = 2) (D : LabeledBlocks K A B a b) (S : BlockShiftData Δ a b)
    (e : R ≃ LabelledResidue m) (code : R ≃ ZMod n)
    (H : (K × Δ) × R → ℤ) (x : ℤ) (sx : R) (k : K)
    (v : (K × Δ) × R) : ((ZMod a × ZMod b) × K) × ZMod n :=
  ((usefulOneOfEq ha D (k - v.1.1) (e (sx - v.2)) + S.e v.1.2,
    highOneOfEq ha D (x - H v) (k - v.1.1) (e (sx - v.2))),
    sharedOutput e code (x - H v) (sx - v.2))

def twoForwardOfEq (ha : a = 3) (D : LabeledBlocks K A B a b) (S : BlockShiftData Δ a b)
    (e : R ≃ LabelledResidue m) (code : R ≃ ZMod n)
    (H : (K × Δ) × R → ℤ) (x : ℤ) (sx : R) (k : K)
    (v : (K × Δ) × R) : ((ZMod a × ZMod b) × K) × ZMod n :=
  ((usefulTwoOfEq ha D (k - v.1.1) (e (sx - v.2)) + S.e v.1.2,
    highTwoOfEq ha D (x - H v) (k - v.1.1) (e (sx - v.2))),
    sharedOutput e code (x - H v) (sx - v.2))

theorem oneForwardOfEq_bijective
    (ha : a = 2) (D : LabeledBlocks K A B a b) (S : BlockShiftData Δ a b)
    (e : R ≃ LabelledResidue m) (code : R ≃ ZMod n)
    (H : (K × Δ) × R → ℤ)
    (hA : ∀ v, (H v : ZMod a) = S.rhoA v.1.2)
    (hB : ∀ v, (H v : ZMod b) = S.rhoB v.1.2)
    (hOther : ∀ v, (H v : ZMod 3) = 0) (x : ℤ) (sx : R) (k : K) :
    Function.Bijective (oneForwardOfEq ha D S e code H x sx k) := by
  subst a
  exact oneForward_bijective D S e code H hA hB hOther x sx k

theorem twoForwardOfEq_bijective
    (ha : a = 3) (D : LabeledBlocks K A B a b) (S : BlockShiftData Δ a b)
    (e : R ≃ LabelledResidue m) (code : R ≃ ZMod n)
    (H : (K × Δ) × R → ℤ)
    (hA : ∀ v, (H v : ZMod a) = S.rhoA v.1.2)
    (hB : ∀ v, (H v : ZMod b) = S.rhoB v.1.2)
    (hOther : ∀ v, (H v : ZMod 2) = 0) (x : ℤ) (sx : R) (k : K) :
    Function.Bijective (twoForwardOfEq ha D S e code H x sx k) := by
  subst a
  exact twoForward_bijective D S e code H hA hB hOther x sx k

theorem usefulOneOfEq_active
    {K : Type uK} {A : Type uA} {B : Type uB}
    [AddCommGroup K] {a b m : ℕ}
    (ha : a = 2) (D : LabeledBlocks K A B a b)
    (u : K) {s : LabelledResidue m} (hs : ActiveOne s) : usefulOneOfEq ha D u s = D.C u := by
  subst a
  rcases s with y | (⟨c, y⟩ | ⟨c, y, z⟩)
  · rfl
  · exact False.elim hs
  · exact False.elim hs

theorem usefulTwoOfEq_active
    {K : Type uK} {A : Type uA} {B : Type uB}
    [AddCommGroup K] {a b m : ℕ}
    (ha : a = 3) (D : LabeledBlocks K A B a b)
    (u : K) {s : LabelledResidue m} (hs : ActiveTwo s) : usefulTwoOfEq ha D u s = D.C u := by
  subst a
  rcases s with y | (⟨c, y⟩ | ⟨c, y, z⟩)
  · exact False.elim hs
  · rfl
  · exact False.elim hs

theorem usefulOneOfEq_inactive_eq
    {K : Type uK} {A : Type uA} {B : Type uB}
    [AddCommGroup K] {a b m : ℕ}
    (ha : a = 2) (D : LabeledBlocks K A B a b)
    (u v : K) {s : LabelledResidue m} (hs : ¬ ActiveOne s) :
    usefulOneOfEq ha D u s = usefulOneOfEq ha D v s := by
  subst a
  rcases s with y | (⟨c, y⟩ | ⟨c, y, z⟩)
  · exact False.elim (hs trivial)
  · rfl
  · rfl

theorem usefulTwoOfEq_inactive_eq
    {K : Type uK} {A : Type uA} {B : Type uB}
    [AddCommGroup K] {a b m : ℕ}
    (ha : a = 3) (D : LabeledBlocks K A B a b)
    (u v : K) {s : LabelledResidue m} (hs : ¬ ActiveTwo s) :
    usefulTwoOfEq ha D u s = usefulTwoOfEq ha D v s := by
  subst a
  rcases s with y | (⟨c, y⟩ | ⟨c, y, z⟩)
  · rfl
  · exact False.elim (hs trivial)
  · rfl

theorem usefulOneOfEq_activity_iff (ha : a = 2) (D : LabeledBlocks K A B a b)
    (rel : K → K → Prop) (hC : ∃ u v, rel u v ∧ D.C u ≠ D.C v)
    (s : LabelledResidue m) :
    (∃ u v, rel u v ∧ usefulOneOfEq ha D u s ≠ usefulOneOfEq ha D v s) ↔ ActiveOne s := by
  classical
  constructor
  · rintro ⟨u, v, _, hne⟩
    by_contra hs
    exact hne (usefulOneOfEq_inactive_eq ha D u v hs)
  · intro hs
    obtain ⟨u, v, huv, hne⟩ := hC
    refine ⟨u, v, huv, ?_⟩
    simpa only [usefulOneOfEq_active ha D u hs, usefulOneOfEq_active ha D v hs] using hne

theorem usefulTwoOfEq_activity_iff (ha : a = 3) (D : LabeledBlocks K A B a b)
    (rel : K → K → Prop) (hC : ∃ u v, rel u v ∧ D.C u ≠ D.C v)
    (s : LabelledResidue m) :
    (∃ u v, rel u v ∧ usefulTwoOfEq ha D u s ≠ usefulTwoOfEq ha D v s) ↔ ActiveTwo s := by
  classical
  constructor
  · rintro ⟨u, v, _, hne⟩
    by_contra hs
    exact hne (usefulTwoOfEq_inactive_eq ha D u v hs)
  · intro hs
    obtain ⟨u, v, huv, hne⟩ := hC
    refine ⟨u, v, huv, ?_⟩
    simpa only [usefulTwoOfEq_active ha D u hs, usefulTwoOfEq_active ha D v hs] using hne

end PeriodicTilingThree.SharedSeed

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

open SharedSeed

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

theorem seedOneSize
    {p : ℕ} [NeZero p] (E : EncodingParameters p)
    : E.a (.inr (0 : Fin 2)) = 2 := by
  simpa using E.seed_a (0 : Fin 2)

theorem seedTwoSize
    {p : ℕ} [NeZero p] (E : EncodingParameters p)
    : E.a (.inr (1 : Fin 2)) = 3 := by
  simpa using E.seed_a (1 : Fin 2)

def seedUseful (t : Fin 2) : Residues p → K E (.inr t) → P E (.inr t) :=
  Fin.cases
    (fun s u => usefulOneOfEq (seedOneSize E) (channelDigitBlocks E (.inr 0) ()) u
      (residueEquiv E.p_prime E.p_large s))
    (fun j => by
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact fun s u => usefulTwoOfEq (seedTwoSize E) (channelDigitBlocks E (.inr 1) ()) u
        (residueEquiv E.p_prime E.p_large s)) t

def seedHigh (t : Fin 2) : ℤ → Residues p → K E (.inr t) → K E (.inr t) :=
  Fin.cases
    (fun x s u => highOneOfEq (seedOneSize E) (channelDigitBlocks E (.inr 0) ()) x u
      (residueEquiv E.p_prime E.p_large s))
    (fun j => by
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact fun x s u => highTwoOfEq (seedTwoSize E) (channelDigitBlocks E (.inr 1) ()) x u
        (residueEquiv E.p_prime E.p_large s)) t

@[simp] theorem seedUseful_zero (s : Residues p) (u : K E (.inr (0 : Fin 2))) :
    seedUseful E 0 s u =
      usefulOneOfEq (seedOneSize E) (channelDigitBlocks E (.inr 0) ()) u
        (residueEquiv E.p_prime E.p_large s) := rfl

@[simp] theorem seedUseful_one (s : Residues p) (u : K E (.inr (1 : Fin 2))) :
    seedUseful E 1 s u =
      usefulTwoOfEq (seedTwoSize E) (channelDigitBlocks E (.inr 1) ()) u
        (residueEquiv E.p_prime E.p_large s) := rfl

@[simp] theorem seedHigh_zero (x : ℤ) (s : Residues p) (u : K E (.inr (0 : Fin 2))) :
    seedHigh E 0 x s u =
      highOneOfEq (seedOneSize E) (channelDigitBlocks E (.inr 0) ()) x u
        (residueEquiv E.p_prime E.p_large s) := rfl

@[simp] theorem seedHigh_one (x : ℤ) (s : Residues p) (u : K E (.inr (1 : Fin 2))) :
    seedHigh E 1 x s u =
      highTwoOfEq (seedTwoSize E) (channelDigitBlocks E (.inr 1) ()) x u
        (residueEquiv E.p_prime E.p_large s) := rfl

def seedC (t : Fin 2) (x : Plane) (k : Input E) : P E (.inr t) :=
  seedUseful E t (residue p x) (k (.inr t))

def seedBeta (t : Fin 2) (x : Plane) (k : Input E) : K E (.inr t) :=
  seedHigh E t x.1 (residue p x) (k (.inr t))

theorem seedC_eq_of_residue_low (t : Fin 2) {x y : Plane} {k l : Input E}
    (hx : residue p x = residue p y) (hk : k (.inr t) = l (.inr t)) :
    seedC E t x k = seedC E t y l := by
  simp only [seedC, hx, hk]

def seedSourceInput (t : Fin 2) (k : Input E) (j : SeedActivationIndex E t) : Input E :=
  Function.update k (.inr t) (k (.inr t) - j.1.1)

@[simp] theorem seedSourceInput_same (t : Fin 2) (k : Input E)
    (j : SeedActivationIndex E t) :
    seedSourceInput E t k j (.inr t) = k (.inr t) - j.1.1 := by
  simp [seedSourceInput]

theorem seedSourceInput_low (t : Fin 2) (k : Input E) (j : SeedActivationIndex E t) :
    seedSourceInput E t k j (.inr t) =
      k (.inr t) - ((seedOffset E t j).1 : K E (.inr t)) := by
  rw [seedSourceInput_same, seedOffset_low]

theorem seed_source_residue (t : Fin 2) (x : Plane) (j : SeedActivationIndex E t) :
    residue p (x - seedOffset E t j) = residue p x - j.2 := by
  have hs : residue p (seedOffset E t j) = j.2 := seedOffset_residue E t j
  have hfirst : ((seedOffset E t j).1 : ZMod (p ^ 2)) = j.2.1 := congrArg Prod.fst hs
  have hsecond : ((seedOffset E t j).2 : ZMod (p ^ 2)) = j.2.2 := congrArg Prod.snd hs
  apply Prod.ext
  · change ((x.1 - (seedOffset E t j).1 : ℤ) : ZMod (p ^ 2)) =
      (x.1 : ZMod (p ^ 2)) - j.2.1
    rw [Int.cast_sub, hfirst]
  · change ((x.2 - (seedOffset E t j).2 : ℤ) : ZMod (p ^ 2)) =
      (x.2 : ZMod (p ^ 2)) - j.2.2
    rw [Int.cast_sub, hsecond]

def seedActualForward (t : Fin 2) (x : Plane) (k : Input E)
    (j : SeedActivationIndex E t) : (P E (.inr t) × K E (.inr t)) × ZMod (D p) :=
  let x' := x - seedOffset E t j
  let k' := seedSourceInput E t k j
  ((seedC E t x' k' + shift (E.a (.inr t)) (E.b (.inr t)) j.1.2,
    seedBeta E t x' k'), commonZ E.p_prime E.p_large x' k')

theorem seedActualForward_zero_eq (x : Plane) (k : Input E) :
    seedActualForward E 0 x k =
      oneForwardOfEq (seedOneSize E) (channelDigitBlocks E (.inr 0) ())
        (BlockShiftData.ofMultiplicity (E.a_two_le (.inr 0)) (E.b_two_le (.inr 0)))
        (residueEquiv E.p_prime E.p_large) (outputEquiv E.p_large)
        (fun j => (seedOffset E 0 j).1) x.1 (residue p x) (k (.inr 0)) := by
  funext j
  simp only [seedActualForward, seedC, seedBeta, seedSourceInput_same,
    seed_source_residue, seedUseful_zero, seedHigh_zero, commonZ,
    oneForwardOfEq, BlockShiftData.ofMultiplicity, Prod.fst_sub]

theorem seedActualForward_one_eq (x : Plane) (k : Input E) :
    seedActualForward E 1 x k =
      twoForwardOfEq (seedTwoSize E) (channelDigitBlocks E (.inr 1) ())
        (BlockShiftData.ofMultiplicity (E.a_two_le (.inr 1)) (E.b_two_le (.inr 1)))
        (residueEquiv E.p_prime E.p_large) (outputEquiv E.p_large)
        (fun j => (seedOffset E 1 j).1) x.1 (residue p x) (k (.inr 1)) := by
  funext j
  simp only [seedActualForward, seedC, seedBeta, seedSourceInput_same,
    seed_source_residue, seedUseful_one, seedHigh_one, commonZ,
    twoForwardOfEq, BlockShiftData.ofMultiplicity, Prod.fst_sub]

theorem seedActualForward_bijective (t : Fin 2) (x : Plane) (k : Input E) :
    Function.Bijective (seedActualForward E t x k) := by
  fin_cases t
  · change Function.Bijective (seedActualForward E (0 : Fin 2) x k)
    rw [seedActualForward_zero_eq]
    apply oneForwardOfEq_bijective
    · intro j
      exact seedOffset_rhoA E 0 j
    · intro j
      exact seedOffset_rhoB E 0 j
    · intro j
      have h := seedOffset_other E (0 : Fin 2) j
      have ha : E.a (.inr (otherSeed (0 : Fin 2))) = 3 := by
        change E.a (.inr (1 : Fin 2)) = 3
        exact seedTwoSize E
      exact Eq.mp (congrArg (fun modulus : ℕ =>
        ((seedOffset E (0 : Fin 2) j).1 : ZMod modulus) = 0) ha) h
  · change Function.Bijective (seedActualForward E (1 : Fin 2) x k)
    rw [seedActualForward_one_eq]
    apply twoForwardOfEq_bijective
    · intro j
      exact seedOffset_rhoA E 1 j
    · intro j
      exact seedOffset_rhoB E 1 j
    · intro j
      have h := seedOffset_other E (1 : Fin 2) j
      have ha : E.a (.inr (otherSeed (1 : Fin 2))) = 2 := by
        change E.a (.inr (0 : Fin 2)) = 2
        exact seedOneSize E
      exact Eq.mp (congrArg (fun modulus : ℕ =>
        ((seedOffset E (1 : Fin 2) j).1 : ZMod modulus) = 0) ha) h

theorem both_seed_tests (x : Plane) (k : Input E) :
    Function.Bijective (seedActualForward E 0 x k) ∧
      Function.Bijective (seedActualForward E 1 x k) :=
  ⟨seedActualForward_bijective E 0 x k, seedActualForward_bijective E 1 x k⟩

def seedActiveRegion (p : ℕ) (t : Fin 2) : Set (Residues p) :=
  if t = 0 then firstRegion p else secondRegion p

theorem seedUseful_active_iff (t : Fin 2) (s : Residues p) :
    (∃ u v : K E (.inr t), u - v ∈ digitSubgroup E (.inr t) () ∧
      seedUseful E t s u ≠ seedUseful E t s v) ↔ s ∈ seedActiveRegion p t := by
  classical
  fin_cases t
  · change (∃ u v : K E (.inr (0 : Fin 2)),
        u - v ∈ digitSubgroup E (.inr (0 : Fin 2)) () ∧
        seedUseful E 0 s u ≠ seedUseful E 0 s v) ↔
          s ∈ seedActiveRegion p (0 : Fin 2)
    have hC := (channelDigitBlocks_active_iff E (.inr (0 : Fin 2)) () ()).mpr rfl
    have hlabel : ActiveOne (residueEquiv E.p_prime E.p_large s) ↔ s ∈ firstRegion p := by
      rw [← residueEquiv_first_iff E.p_prime E.p_large s]
      cases hs : residueEquiv E.p_prime E.p_large s <;> simp [ActiveOne]
    have h := usefulOneOfEq_activity_iff (seedOneSize E) (channelDigitBlocks E (.inr 0) ())
      (fun u v => u - v ∈ digitSubgroup E (.inr 0) ()) hC
      (residueEquiv E.p_prime E.p_large s)
    rw [seedActiveRegion, ite_eq_left (rfl : (0 : Fin 2) = 0)]
    simpa only [seedUseful_zero] using h.trans hlabel
  · change (∃ u v : K E (.inr (1 : Fin 2)),
        u - v ∈ digitSubgroup E (.inr (1 : Fin 2)) () ∧
        seedUseful E 1 s u ≠ seedUseful E 1 s v) ↔
          s ∈ seedActiveRegion p (1 : Fin 2)
    have hC := (channelDigitBlocks_active_iff E (.inr (1 : Fin 2)) () ()).mpr rfl
    have hlabel : ActiveTwo (residueEquiv E.p_prime E.p_large s) ↔ s ∈ secondRegion p := by
      rw [← residueEquiv_second_iff E.p_prime E.p_large s]
      cases hs : residueEquiv E.p_prime E.p_large s with
      | inl y => simp [ActiveTwo]
      | inr u => cases u <;> simp [ActiveTwo]
    have h := usefulTwoOfEq_activity_iff (seedTwoSize E) (channelDigitBlocks E (.inr 1) ())
      (fun u v => u - v ∈ digitSubgroup E (.inr 1) ()) hC
      (residueEquiv E.p_prime E.p_large s)
    simpa only [seedUseful_one, seedActiveRegion, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
      using h.trans hlabel

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

section RepresentationFibres

variable {H : Type uH} {B : Type uB} {C : Type uC} [AddCommGroup H]

theorem tiles_range_iff_unique_base (s : B → H) (hs : Function.Injective s)
    (F : Finset H) :
    Tiles F (Set.range s) ↔ ∀ y : H, ∃! b : B, y - s b ∈ F := by
  rw [tiles_iff_unique_tile]
  constructor
  · intro h y
    obtain ⟨f, hf, huniq⟩ := h y
    obtain ⟨b, hb⟩ := hf
    have hbf : y - s b = (f : H) := by rw [hb]; simp
    refine ⟨b, ?_, ?_⟩
    · change y - s b ∈ F
      rw [hbf]
      exact f.property
    · intro b' hb'
      let f' : ↥F := ⟨y - s b', hb'⟩
      have hf' : y - (f' : H) ∈ Set.range s := by
        refine ⟨b', ?_⟩
        simp [f']
      have he : (f' : H) = (f : H) := congrArg Subtype.val (huniq f' hf')
      apply hs
      exact sub_right_inj.mp (he.trans hbf.symm)
  · intro h y
    obtain ⟨b, hb, huniq⟩ := h y
    let f : ↥F := ⟨y - s b, hb⟩
    refine ⟨f, ?_, ?_⟩
    · refine ⟨b, ?_⟩
      simp [f]
    · intro f' hf'
      obtain ⟨b', hb'⟩ := hf'
      have hbf : y - s b' = (f' : H) := by rw [hb']; simp
      have hbb : b' = b := huniq b' (by
        change y - s b' ∈ F
        rw [hbf]
        exact f'.property)
      apply Subtype.ext
      change (f' : H) = y - s b
      rw [← hbf, hbb]

variable [AddCommGroup B] [AddCommGroup C]

theorem tiles_kernel_iff_unique_fibre (q : H →+ B)
    (hq : Function.Surjective q) (F : Finset H)
    (hF : ∀ x : H, x ∈ F ↔ q x = 0) (A : Set H) :
    Tiles F A ↔ ∀ b : B, ∃! a : A, q (a : H) = b := by
  constructor
  · intro h b
    obtain ⟨y, hy⟩ := hq b
    obtain ⟨⟨f, a⟩, hfa⟩ := h.2 y
    change (f : H) + (a : H) = y at hfa
    have hqa : q (a : H) = b := by
      have he := congrArg q hfa
      rw [map_add, (hF _).mp f.property, zero_add, hy] at he
      exact he
    refine ⟨a, hqa, ?_⟩
    intro a' ha'
    have hmem : y - (a' : H) ∈ F := by
      apply (hF _).mpr
      rw [map_sub, hy, ha', sub_self]
    let f' : ↥F := ⟨y - (a' : H), hmem⟩
    have he : ((f', a') : ↥F × A) = (f, a) := by
      apply h.1
      change (y - (a' : H)) + (a' : H) = (f : H) + (a : H)
      rw [sub_add_cancel, hfa]
    exact congrArg Prod.snd he
  · intro h
    constructor
    · rintro ⟨f, a⟩ ⟨f', a'⟩ he
      have hqa : q (a : H) = q (a' : H) := by
        have he' := congrArg q he
        simpa only [map_add, (hF _).mp f.property,
          (hF _).mp f'.property, zero_add] using he'
      obtain ⟨a₀, _ha₀, huniq⟩ := h (q (a : H))
      have haa : a = a' := (huniq a rfl).trans (huniq a' hqa.symm).symm
      have hff : f = f' := by
        apply Subtype.ext
        have hv := congrArg Subtype.val haa
        change (f : H) + (a : H) = (f' : H) + (a' : H) at he
        rw [hv] at he
        exact add_right_cancel he
      exact Prod.ext hff haa
    · intro y
      obtain ⟨a, ha, _huniq⟩ := h (q y)
      have hmem : y - (a : H) ∈ F := by
        apply (hF _).mpr
        rw [map_sub, ha, sub_self]
      refine ⟨(⟨y - (a : H), hmem⟩, a), ?_⟩
      exact sub_add_cancel y (a : H)

theorem tiles_invariance_iff (q : H →+ B) (ψ : H →+ C)
    (s : B → H) (hs : ∀ b, q (s b) = b)
    (σ : B) (F : Finset H)
    (hF : ∀ v : H, v ∈ F ↔
      (q v = 0 ∧ ψ v ≠ 0) ∨ (q v = σ ∧ ψ v = 0)) :
    Tiles F (Set.range s) ↔ ∀ b, ψ (s (b - σ)) = ψ (s b) := by
  have hinj : Function.Injective s := fun b b' h => by
    have := congrArg q h
    simpa only [hs] using this
  have hmem (y : H) (b : B) : y - s b ∈ F ↔
      (q y = b ∧ ψ y ≠ ψ (s b)) ∨
      (q y = σ + b ∧ ψ y = ψ (s b)) := by
    simpa only [map_sub, hs, sub_eq_zero, sub_ne_zero,
      sub_eq_iff_eq_add, zero_add] using hF (y - s b)
  rw [tiles_range_iff_unique_base s hinj F]
  constructor
  · intro h b
    obtain ⟨b', hb', _huniq⟩ := h (s b)
    rcases (hmem _ _).mp hb' with ⟨hq, hne⟩ | ⟨hq, he⟩
    · rw [hs] at hq
      exact False.elim (hne (congrArg (fun b => ψ (s b)) hq))
    · rw [hs] at hq
      have hb : b' = b - σ := by rw [hq]; abel
      rw [hb] at he
      exact he.symm
  · intro h y
    by_cases he : ψ y = ψ (s (q y))
    · refine ⟨q y - σ, ?_, ?_⟩
      · apply (hmem _ _).mpr
        exact Or.inr ⟨by abel, he.trans (h (q y)).symm⟩
      · intro b hb
        rcases (hmem _ _).mp hb with ⟨hq, hne⟩ | ⟨hq, _he⟩
        · exact False.elim (hne (hq ▸ he))
        · rw [hq]
          abel
    · refine ⟨q y, (hmem _ _).mpr (Or.inl ⟨rfl, he⟩), ?_⟩
      intro b hb
      rcases (hmem _ _).mp hb with ⟨hq, _hne⟩ | ⟨hq, he'⟩
      · exact hq.symm
      · have hb : b = q y - σ := by rw [hq]; abel
        rw [hb, h (q y)] at he'
        exact False.elim (he he')

end RepresentationFibres

noncomputable section Concrete

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

local instance : DecidableEq (Ambient E) := Classical.decEq _

def usefulCoord (i : Channel p) : Ambient E →+ P E i where
  toFun v := (v.2.2 i).2
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem usefulCoord_apply (i : Channel p) (v : Ambient E) :
    usefulCoord E i v = (v.2.2 i).2 := rfl

@[simp] theorem usefulCoord_point (i : Channel p) (o : GraphOutputs E) (b : Base E) :
    usefulCoord E i (point o b) = o.c b i := rfl

private theorem kernel_horizontal_zero (v : (q0 E).ker) :
    (v : Ambient E).1 = 0 := by
  have hv := congrArg Prod.fst v.property
  exact hv

noncomputable instance kernelFintype : Fintype (q0 E).ker :=
  Fintype.ofInjective (fun v : (q0 E).ker => (v : Ambient E).2) (by
    intro v w h
    apply Subtype.ext
    exact Prod.ext ((kernel_horizontal_zero E v).trans
      (kernel_horizontal_zero E w).symm) h)

def kernelTile : Finset (Ambient E) :=
  (Finset.univ : Finset (q0 E).ker).map ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem mem_kernelTile (v : Ambient E) :
    v ∈ kernelTile E ↔ q0 E v = 0 := by
  constructor
  · intro hv
    obtain ⟨w, _hw, rfl⟩ := Finset.mem_map.mp hv
    exact w.property
  · intro hv
    exact Finset.mem_map.mpr ⟨⟨v, hv⟩, Finset.mem_univ _, rfl⟩

theorem kernelTile_nonempty : (kernelTile E).Nonempty :=
  ⟨0, (mem_kernelTile E 0).mpr (map_zero _)⟩

def baseLift (b : Base E) : Ambient E := point (zeroOutputs E) b

@[simp] theorem q0_baseLift (b : Base E) : q0 E (baseLift E b) = b :=
  q0_point (zeroOutputs E) b

@[simp] theorem usefulCoord_baseLift (i : Channel p) (b : Base E) :
    usefulCoord E i (baseLift E b) = 0 := rfl

theorem kernelTile_iff_unique_fibre (A : Set (Ambient E)) :
    Tiles (kernelTile E) A ↔
      ∀ b : Base E, ∃! a : A, q0 E (a : Ambient E) = b :=
  tiles_kernel_iff_unique_fibre (q0 E) (q0_surjective E) (kernelTile E)
    (mem_kernelTile E) A

theorem kernelTile_graph (o : GraphOutputs E) : Tiles (kernelTile E) (graph o) := by
  apply (tiles_range_iff_unique_base (point o) (point_injective o) (kernelTile E)).mpr
  intro y
  refine ⟨q0 E y, ?_, ?_⟩
  · change y - point o (q0 E y) ∈ kernelTile E
    rw [mem_kernelTile, map_sub, q0_point, sub_self]
  · intro b hb
    rw [mem_kernelTile, map_sub, q0_point, sub_eq_zero] at hb
    exact hb.symm

theorem kernelTile_iff_graph (A : Set (Ambient E)) :
    Tiles (kernelTile E) A ↔ ∃ o : GraphOutputs E, graph o = A := by
  classical
  constructor
  · intro h
    have hf := (kernelTile_iff_unique_fibre E A).mp h
    let a : Base E → A := fun b => Classical.choose (hf b)
    have ha (b : Base E) : q0 E (a b : Ambient E) = b :=
      (Classical.choose_spec (hf b)).1
    let s : Base E → Ambient E := fun b => (a b : Ambient E)
    have hs : ∀ b, q0 E (s b) = b := ha
    refine ⟨outputsOfSection s hs, ?_⟩
    rw [graph_outputsOfSection]
    ext y
    constructor
    · rintro ⟨b, rfl⟩
      exact (a b).property
    · intro hy
      refine ⟨q0 E y, ?_⟩
      have he : (⟨y, hy⟩ : A) = a (q0 E y) :=
        (Classical.choose_spec (hf (q0 E y))).2 ⟨y, hy⟩ rfl
      exact (congrArg Subtype.val he).symm
  · rintro ⟨o, rfl⟩
    exact kernelTile_graph E o

def invarianceZero (i : Channel p) : Finset (Ambient E) :=
  (kernelTile E).filter (fun v => usefulCoord E i v = 0)

def invarianceNonzero (i : Channel p) : Finset (Ambient E) :=
  (kernelTile E).filter (fun v => usefulCoord E i v ≠ 0)

def invarianceTile (i : Channel p) (σ : Base E) : Finset (Ambient E) :=
  invarianceNonzero E i ∪
    (invarianceZero E i).image (fun v => baseLift E σ + v)

theorem mem_invarianceTile (i : Channel p) (σ : Base E) (v : Ambient E) :
    v ∈ invarianceTile E i σ ↔
      (q0 E v = 0 ∧ usefulCoord E i v ≠ 0) ∨
      (q0 E v = σ ∧ usefulCoord E i v = 0) := by
  constructor
  · intro hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Or.inl (by simpa only [invarianceNonzero, Finset.mem_filter,
        mem_kernelTile] using hv)
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      have hw' : q0 E w = 0 ∧ usefulCoord E i w = 0 := by
        simpa only [invarianceZero, Finset.mem_filter, mem_kernelTile] using hw
      exact Or.inr ⟨by rw [map_add, q0_baseLift, hw'.1, add_zero],
        by rw [map_add, usefulCoord_baseLift, hw'.2, add_zero]⟩
  · rintro (⟨hq, hc⟩ | ⟨hq, hc⟩)
    · apply Finset.mem_union.mpr
      exact Or.inl (by simpa only [invarianceNonzero, Finset.mem_filter,
        mem_kernelTile] using And.intro hq hc)
    · apply Finset.mem_union.mpr
      apply Or.inr
      apply Finset.mem_image.mpr
      refine ⟨v - baseLift E σ, ?_, ?_⟩
      · rw [invarianceZero, Finset.mem_filter, mem_kernelTile]
        constructor
        · rw [map_sub, hq, q0_baseLift, sub_self]
        · rw [map_sub, hc, usefulCoord_baseLift, sub_self]
      · abel

theorem invarianceTile_nonempty (i : Channel p) (σ : Base E) :
    (invarianceTile E i σ).Nonempty := by
  refine ⟨baseLift E σ, (mem_invarianceTile E i σ _).mpr (Or.inr ?_)⟩
  exact ⟨q0_baseLift E σ, usefulCoord_baseLift E i σ⟩

theorem invarianceTile_disjoint (i : Channel p) (σ : Base E) :
    Disjoint (invarianceNonzero E i)
      ((invarianceZero E i).image (fun v => baseLift E σ + v)) := by
  apply Finset.disjoint_left.mpr
  intro v hv hv'
  have hne : usefulCoord E i v ≠ 0 := (Finset.mem_filter.mp hv).2
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv'
  have hw0 : usefulCoord E i w = 0 := (Finset.mem_filter.mp hw).2
  apply hne
  rw [map_add, usefulCoord_baseLift, hw0, add_zero]

theorem invarianceTile_card (i : Channel p) (σ : Base E) :
    (invarianceTile E i σ).card = (kernelTile E).card := by
  rw [invarianceTile, Finset.card_union_of_disjoint (invarianceTile_disjoint E i σ),
    Finset.card_image_of_injective _ (fun _ _ h => add_left_cancel h)]
  have hpart : invarianceNonzero E i ∪ invarianceZero E i = kernelTile E := by
    ext v
    simp only [invarianceNonzero, invarianceZero, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
    · intro hv
      by_cases hc : usefulCoord E i v = 0
      · exact Or.inr ⟨hv, hc⟩
      · exact Or.inl ⟨hv, hc⟩
  have hdisj : Disjoint (invarianceNonzero E i) (invarianceZero E i) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hw).2
  rw [← Finset.card_union_of_disjoint hdisj, hpart]

theorem invarianceTile_iff (i : Channel p) (σ : Base E) (o : GraphOutputs E) :
    Tiles (invarianceTile E i σ) (graph o) ↔
      ∀ b, o.c (b - σ) i = o.c b i := by
  exact tiles_invariance_iff (q0 E) (usefulCoord E i) (point o)
    (q0_point o) σ (invarianceTile E i σ) (mem_invarianceTile E i σ)

end Concrete

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace PeriodicTilingThree

section CoordinateReplacement

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type uA} {B : Type uB}

theorem eq_of_update_invariant (f : (∀ i, A i) → B)
    (hf : ∀ x i (a : A i), f (Function.update x i a) = f x)
    (x y : ∀ i, A i) : f x = f y := by
  have h : ∀ s : Finset ι, f (s.piecewise x y) = f y := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => rw [Finset.piecewise_insert, hf, ih]
  simpa using h Finset.univ

theorem eq_of_update_invariant_off (f : (∀ i, A i) → B) (i : ι)
    (hf : ∀ j, j ≠ i → ∀ x (a : A j), f (Function.update x j a) = f x)
    (x y : ∀ i, A i) (hxy : x i = y i) : f x = f y := by
  have h : ∀ s : Finset ι, f (s.piecewise x y) = f y := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.piecewise_insert]
      by_cases hji : j = i
      · subst j
        have hv : s.piecewise x y i = x i := by
          by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi, hxy]
        rw [← hv, Function.update_eq_self]
        exact ih
      · exact (hf j hji _ _).trans ih
  simpa using h Finset.univ

end CoordinateReplacement

section Activity

variable {A : Type uA} {B : Type uB} [AddGroup A]

def DigitActive (g : A → B) (U : AddSubgroup A) : Prop :=
  ∃ w w', w - w' ∈ U ∧ g w ≠ g w'

theorem not_digitActive_iff (g : A → B) (U : AddSubgroup A) :
    ¬ DigitActive g U ↔ ∀ w w', w - w' ∈ U → g w = g w' := by
  simp only [DigitActive, not_exists, not_and, not_not]

end Activity

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

def seedResidue (p : ℕ) (x : Plane) : Residues p :=
  ((x.1 : ZMod (p ^ 2)), (x.2 : ZMod (p ^ 2)))

def seedRepresentative (p : ℕ) (s : Residues p) : Plane :=
  ((s.1.val : ℤ), (s.2.val : ℤ))

@[simp] theorem seedResidue_representative (s : Residues p) :
    seedResidue p (seedRepresentative p s) = s := by
  apply Prod.ext <;> simp [seedResidue, seedRepresentative]

def usefulAt (o : Outputs E) (i : Channel p) (x : Plane) (w : K E i) : P E i :=
  o.c (x, Function.update 0 i w) i

def ordinaryFactor (o : Outputs E) (n : Column p) (m : ℤ)
    (w : K E (.inl n)) : P E (.inl n) :=
  usefulAt E o (.inl n) (0, m) w

def seedFactor (o : Outputs E) (t : Fin 2) (s : Residues p)
    (w : K E (.inr t)) : P E (.inr t) :=
  usefulAt E o (.inr t) (seedRepresentative p s) w

def HasDependence (o : Outputs E) : Prop :=
  (∀ n x k, o.c (x, k) (.inl n) =
    ordinaryFactor E o n (lineValue n x) (k (.inl n))) ∧
  (∀ t x k, o.c (x, k) (.inr t) =
    seedFactor E o t (seedResidue p x) (k (.inr t)))

theorem ordinaryFactor_spec {o : Outputs E} (h : HasDependence E o)
    (n : Column p) (x : Plane) (k : Low E) :
    o.c (x, k) (.inl n) = ordinaryFactor E o n (lineValue n x) (k (.inl n)) :=
  h.1 n x k

theorem seedFactor_spec {o : Outputs E} (h : HasDependence E o)
    (t : Fin 2) (x : Plane) (k : Low E) :
    o.c (x, k) (.inr t) = seedFactor E o t (seedResidue p x) (k (.inr t)) :=
  h.2 t x k

theorem usefulAt_factor {o : Outputs E} (h : HasDependence E o)
    (x : Plane) (k : Low E) (i : Channel p) :
    o.c (x, k) i = usefulAt E o i x (k i) := by
  cases i with
  | inl n =>
    rw [h.1 n x k]
    symm
    simpa [usefulAt] using h.1 n x (Function.update 0 (.inl n) (k (.inl n)))
  | inr t =>
    rw [h.2 t x k]
    symm
    simpa [usefulAt] using h.2 t x (Function.update 0 (.inr t) (k (.inr t)))

theorem usefulAt_eq_of_lineValue_eq {o : Outputs E} (h : HasDependence E o)
    (n : Column p) {x y : Plane} (hxy : lineValue n x = lineValue n y)
    (w : K E (.inl n)) :
    usefulAt E o (.inl n) x w = usefulAt E o (.inl n) y w := by
  unfold usefulAt
  rw [h.1 n x _, h.1 n y _, hxy]

theorem usefulAt_eq_of_seedResidue_eq {o : Outputs E} (h : HasDependence E o)
    (t : Fin 2) {x y : Plane} (hxy : seedResidue p x = seedResidue p y)
    (w : K E (.inr t)) :
    usefulAt E o (.inr t) x w = usefulAt E o (.inr t) y w := by
  unfold usefulAt
  rw [h.2 t x _, h.2 t y _, hxy]

def Active (o : Outputs E) (i : Channel p) (x : Plane) (j : Label p i) : Prop :=
  DigitActive (usefulAt E o i x) (digitSubgroup E i j)

theorem digitActive_iff_coordinates (i : Channel p) (g : K E i → P E i)
    (j : Label p i) :
    DigitActive g (digitSubgroup E i j) ↔
      ∃ w w', (∀ q, q ≠ j → digitEquiv E i w q = digitEquiv E i w' q) ∧
        g w ≠ g w' := by
  simp only [DigitActive, sub_mem_digitSubgroup_iff]

theorem no_digitActive_iff_constant (i : Channel p) (g : K E i → P E i) :
    (∀ j, ¬ DigitActive g (digitSubgroup E i j)) ↔ ∃ c, ∀ w, g w = c := by
  constructor
  · intro h
    let e := digitEquiv E i
    have hu : ∀ z j (a : ZMod (E.digitPrime i j)),
        g (e.symm (Function.update z j a)) = g (e.symm z) := by
      intro z j a
      apply (not_digitActive_iff g (digitSubgroup E i j)).mp (h j)
      apply (sub_mem_digitSubgroup_iff E i j _ _).mpr
      intro q hq
      simp [e, hq]
    refine ⟨g 0, fun w => ?_⟩
    simpa [e] using eq_of_update_invariant (fun z => g (e.symm z)) hu (e w) (e 0)
  · rintro ⟨c, hc⟩ j
    apply (not_digitActive_iff g (digitSubgroup E i j)).mpr
    intro w w' _hww'
    exact (hc w).trans (hc w').symm

theorem no_active_iff_constant (o : Outputs E) (i : Channel p) (x : Plane) :
    (∀ j, ¬ Active E o i x j) ↔ ∃ c, ∀ w, usefulAt E o i x w = c :=
  no_digitActive_iff_constant E i (usefulAt E o i x)

theorem active_ordinary_iff {o : Outputs E} (h : HasDependence E o)
    (n : Column p) {x y : Plane} (hxy : lineValue n x = lineValue n y)
    (j : Label p (.inl n)) : Active E o (.inl n) x j ↔ Active E o (.inl n) y j := by
  have he : usefulAt E o (.inl n) x = usefulAt E o (.inl n) y :=
    funext (usefulAt_eq_of_lineValue_eq E h n hxy)
  unfold Active
  rw [he]

theorem active_seed_iff {o : Outputs E} (h : HasDependence E o)
    (t : Fin 2) {x y : Plane} (hxy : seedResidue p x = seedResidue p y)
    (j : Label p (.inr t)) : Active E o (.inr t) x j ↔ Active E o (.inr t) y j := by
  have he : usefulAt E o (.inr t) x = usefulAt E o (.inr t) y :=
    funext (usefulAt_eq_of_seedResidue_eq E h t hxy)
  unfold Active
  rw [he]

abbrev DependenceIndex (p : ℕ) :=
  (Σ i : Channel p, {j : Channel p // j ≠ i}) ⊕
    (Column p ⊕ (Fin 2 × Bool))

def lowGenerator (j : Channel p) : Base E :=
  (0, Function.update 0 j 1)

def seedStep (p : ℕ) (second : Bool) : Plane :=
  if second then (0, ((p ^ 2 : ℕ) : ℤ)) else (((p ^ 2 : ℕ) : ℤ), 0)

def dependenceChannel : DependenceIndex p → Channel p
  | .inl ⟨i, _⟩ => i
  | .inr (.inl n) => .inl n
  | .inr (.inr (t, _)) => .inr t

def dependenceShift : DependenceIndex p → Base E
  | .inl ⟨_, j⟩ => lowGenerator E j.1
  | .inr (.inl n) => (lineKernelStep n, 0)
  | .inr (.inr (_, axis)) => (seedStep p axis, 0)

def dependenceTile (d : DependenceIndex p) : Finset (G E) :=
  invarianceTile E (dependenceChannel d) (dependenceShift E d)

theorem dependenceTile_nonempty (d : DependenceIndex p) :
    (dependenceTile E d).Nonempty :=
  invarianceTile_nonempty E (dependenceChannel d) (dependenceShift E d)

theorem dependenceTile_card (d : DependenceIndex p) :
    (dependenceTile E d).card = (kernelTile E).card :=
  invarianceTile_card E (dependenceChannel d) (dependenceShift E d)

def dependenceTiles : Finset (Finset (G E)) := by
  classical
  exact Finset.univ.image (dependenceTile E)

def DependenceTests (o : Outputs E) : Prop :=
  ∀ d : DependenceIndex p, Tiles (dependenceTile E d) (graph o)

def DependenceInvariance (o : Outputs E) : Prop :=
  ∀ d : DependenceIndex p, ∀ b : Base E,
    o.c (b - dependenceShift E d) (dependenceChannel d) = o.c b (dependenceChannel d)

private theorem periodic_of_sub_eq {A : Type uA} {B : Type uB} [AddGroup A]
    (f : A → B) (v : A) (h : ∀ x, f (x - v) = f x) : Function.Periodic f v := by
  intro x
  simpa using (h (x + v)).symm

private theorem useful_update_of_generator (o : Outputs E) (i j : Channel p)
    (h : ∀ b, o.c (b - lowGenerator E j) i = o.c b i)
    (x : Plane) (k : Low E) (w : K E j) :
    o.c (x, Function.update k j w) i = o.c (x, k) i := by
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective (k j - w)
  have he : (x, Function.update k j w) = (x, k) - a • lowGenerator E j := by
    apply Prod.ext
    · simp [lowGenerator]
    · funext l
      by_cases hlj : l = j
      · subst l
        simp [lowGenerator, zsmul_eq_mul, ha]
      · simp [lowGenerator, hlj]
  rw [he]
  exact (periodic_of_sub_eq (fun b => o.c b i) (lowGenerator E j) h).sub_zsmul_eq a

private theorem usefulAt_factor_of_generators (o : Outputs E)
    (h : ∀ i j, j ≠ i → ∀ b, o.c (b - lowGenerator E j) i = o.c b i)
    (x : Plane) (k : Low E) (i : Channel p) :
    o.c (x, k) i = usefulAt E o i x (k i) := by
  unfold usefulAt
  apply eq_of_update_invariant_off (fun k => o.c (x, k) i) i
  · intro j hji k' w
    exact useful_update_of_generator E o i j (h i j hji) x k' w
  · simp

@[simp] theorem seedResidue_sub_step
    {p : ℕ} [NeZero p]
    (x : Plane) (axis : Bool) :
    seedResidue p (x - seedStep p axis) = seedResidue p x := by
  have hp2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  cases axis <;> apply Prod.ext <;> simp [seedResidue, seedStep, hp2]

theorem dependenceInvariance_iff (o : Outputs E) :
    DependenceInvariance E o ↔ HasDependence E o := by
  constructor
  · intro h
    have hlow : ∀ i j, j ≠ i → ∀ b, o.c (b - lowGenerator E j) i = o.c b i := by
      intro i j hji b
      exact h (.inl ⟨i, ⟨j, hji⟩⟩) b
    have hfactor := usefulAt_factor_of_generators E o hlow
    constructor
    · intro n x k
      have hstep : ∀ b : Base E,
          o.c (b - (lineKernelStep n, 0)) (.inl n) = o.c b (.inl n) :=
        h (.inr (.inl n))
      have hp := periodic_of_sub_eq (fun b : Base E => o.c b (.inl n))
        (lineKernelStep n, 0) hstep
      have he : (x, k) - x.1 • (lineKernelStep n, (0 : Low E)) =
          ((0, lineValue n x), k) := by
        apply Prod.ext
        · apply Prod.ext
          · simp [lineKernelStep]
          · simp [lineKernelStep, lineValue]
            ring
        · simp
      have hs := hp.sub_zsmul_eq (x := (x, k)) x.1
      rw [he] at hs
      exact hs.symm.trans (hfactor (0, lineValue n x) k (.inl n))
    · intro t x k
      have hfirst : ∀ b : Base E,
          o.c (b - (seedStep p false, 0)) (.inr t) = o.c b (.inr t) :=
        h (.inr (.inr (t, false)))
      have hsecond : ∀ b : Base E,
          o.c (b - (seedStep p true, 0)) (.inr t) = o.c b (.inr t) :=
        h (.inr (.inr (t, true)))
      have hp := periodic_of_sub_eq (fun b : Base E => o.c b (.inr t))
        (seedStep p false, 0) hfirst
      have hq := periodic_of_sub_eq (fun b : Base E => o.c b (.inr t))
        (seedStep p true, 0) hsecond
      obtain ⟨a, ha⟩ := (ZMod.intCast_eq_iff (p ^ 2) x.1 (seedResidue p x).1).mp rfl
      obtain ⟨b, hb⟩ := (ZMod.intCast_eq_iff (p ^ 2) x.2 (seedResidue p x).2).mp rfl
      have he : (x, k) - a • (seedStep p false, (0 : Low E)) -
          b • (seedStep p true, (0 : Low E)) =
          (seedRepresentative p (seedResidue p x), k) := by
        apply Prod.ext
        · apply Prod.ext
          · simpa [seedStep, seedRepresentative, zsmul_eq_mul,
              sub_eq_iff_eq_add, mul_comm] using ha
          · simpa [seedStep, seedRepresentative, zsmul_eq_mul,
              sub_eq_iff_eq_add, mul_comm] using hb
        · simp
      have hs := (hq.sub_zsmul_eq
        (x := (x, k) - a • (seedStep p false, (0 : Low E))) b).trans
          (hp.sub_zsmul_eq (x := (x, k)) a)
      rw [he] at hs
      exact hs.symm.trans (hfactor (seedRepresentative p (seedResidue p x)) k (.inr t))
  · intro h d xb
    rcases xb with ⟨x, k⟩
    rcases d with ⟨i, j⟩ | d
    · change o.c ((x, k) - (0, Function.update (0 : Low E) j.1 1)) i = o.c (x, k) i
      simp only [Prod.mk_sub_mk, sub_zero]
      rw [usefulAt_factor E h, usefulAt_factor E h]
      simp [Ne.symm j.property]
    · rcases d with n | ⟨t, axis⟩
      · change o.c ((x, k) - (lineKernelStep n, 0)) (.inl n) = o.c (x, k) (.inl n)
        simp only [Prod.mk_sub_mk, sub_zero]
        rw [h.1 n (x - lineKernelStep n) k, h.1 n x k]
        have he : lineValue n (x - lineKernelStep n) = lineValue n x := by
          simp [lineValue, lineKernelStep] ; ring
        rw [he]
      · change o.c ((x, k) - (seedStep p axis, 0)) (.inr t) = o.c (x, k) (.inr t)
        simp only [Prod.mk_sub_mk, sub_zero]
        rw [h.2 t (x - seedStep p axis) k, h.2 t x k, seedResidue_sub_step]

theorem dependenceTests_iff (o : Outputs E) :
    DependenceTests E o ↔ HasDependence E o := by
  have he : DependenceTests E o ↔ DependenceInvariance E o := by
    unfold DependenceTests DependenceInvariance dependenceTile
    simp only [invarianceTile_iff]
  exact he.trans (dependenceInvariance_iff E o)

theorem dependenceTiles_iff (o : Outputs E) :
    (∀ F ∈ dependenceTiles E, Tiles F (graph o)) ↔ HasDependence E o := by
  classical
  rw [← dependenceTests_iff E o]
  constructor
  · intro h d
    apply h (dependenceTile E d)
    exact Finset.mem_image.mpr ⟨d, Finset.mem_univ d, rfl⟩
  · intro h F hF
    obtain ⟨d, _hd, rfl⟩ := Finset.mem_image.mp hF
    exact h d

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree.CommonModel

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

def outputs : GraphOutputs E where
  c b i := match i with
    | .inl n => ordinaryUseful E n b.1 (b.2 (.inl n))
    | .inr t => seedC E t b.1 b.2
  beta b i := match i with
    | .inl n => ordinaryHigh E n b.1 (b.2 (.inl n))
    | .inr t => seedBeta E t b.1 b.2
  z b := SharedSeed.commonZ E.p_prime E.p_large b.1 b.2

def commonGraph : Set (Ambient E) := graph (outputs E)

@[simp] theorem outputs_c_ordinary (n : Column p) (x : Plane) (k : Input E) :
    (outputs E).c (x,k) (.inl n) = ordinaryUseful E n x (k (.inl n)) := rfl

@[simp] theorem outputs_c_seed (t : Fin 2) (x : Plane) (k : Input E) :
    (outputs E).c (x,k) (.inr t) = seedC E t x k := rfl

@[simp] theorem outputs_beta_ordinary (n : Column p) (x : Plane) (k : Input E) :
    (outputs E).beta (x,k) (.inl n) = ordinaryHigh E n x (k (.inl n)) := rfl

@[simp] theorem outputs_beta_seed (t : Fin 2) (x : Plane) (k : Input E) :
    (outputs E).beta (x,k) (.inr t) = seedBeta E t x k := rfl

@[simp] theorem outputs_z (x : Plane) (k : Input E) :
    (outputs E).z (x,k) = SharedSeed.commonZ E.p_prime E.p_large x k := rfl

@[simp] theorem usefulAt_ordinary (n : Column p) (x : Plane) (w : K E (.inl n)) :
    usefulAt E (outputs E) (.inl n) x w = ordinaryUseful E n x w := by
  simp [usefulAt]

@[simp] theorem usefulAt_seed (t : Fin 2) (x : Plane) (w : K E (.inr t)) :
    usefulAt E (outputs E) (.inr t) x w =
      seedUseful E t (SharedSeed.residue p x) w := by
  simp [usefulAt, seedC]

theorem outputs_hasDependence : HasDependence E (outputs E) := by
  constructor
  · intro n x k
    simp only [outputs_c_ordinary, ordinaryFactor, usefulAt_ordinary]
    apply ordinaryUseful_eq_of_lineValue_eq E n
    simp
  · intro t x k
    simp only [outputs_c_seed, seedFactor, usefulAt_seed, seedC]
    have hr : SharedSeed.residue p (seedRepresentative p (seedResidue p x)) =
        SharedSeed.residue p x :=
      seedResidue_representative (p := p) (seedResidue p x)
    rw [hr]

theorem active_ordinary_iff (n : Column p) (x : Plane) (j : Symbol p) :
    Active E (outputs E) (.inl n) x j ↔ j = ordinarySymbol E n x := by
  simpa only [Active, DigitActive, usefulAt_ordinary] using
    ordinaryUseful_active_iff E n x j

theorem active_seed_iff (t : Fin 2) (x : Plane) :
    Active E (outputs E) (.inr t) x () ↔
      SharedSeed.residue p x ∈ seedActiveRegion p t := by
  simpa only [Active, DigitActive, usefulAt_seed] using
    seedUseful_active_iff E t (SharedSeed.residue p x)

theorem active_word_allowed (x : Plane) (w : Word p)
    (hw : ∀ n, Active E (outputs E) (.inl n) x (w n)) : Allowed p w := by
  have he : w = ordinaryWord E x :=
    funext fun n => (active_ordinary_iff E n x (w n)).mp (hw n)
  rw [he]
  exact ordinaryWord_allowed E x

theorem active_seed_forces_symbol (t : Fin 2) (n : Column p) (x : Plane)
    (j : Symbol p) (ht : Active E (outputs E) (.inr t) x ())
    (hj : Active E (outputs E) (.inl n) x j) :
    j = lastDigit p E.p_prime ((t.val : ℤ) + 1) := by
  have hj' := (active_ordinary_iff E n x j).mp hj
  have hr := (active_seed_iff E t x).mp ht
  fin_cases t
  · have hfirst : SharedSeed.residue p x ∈ SharedSeed.firstRegion p := by
      simpa [seedActiveRegion] using hr
    simpa using hj'.trans (ordinarySymbol_firstRegion E n x hfirst)
  · have hsecond : SharedSeed.residue p x ∈ SharedSeed.secondRegion p := by
      simpa [seedActiveRegion] using hr
    simpa using hj'.trans (ordinarySymbol_secondRegion E n x hsecond)

theorem commonGraph_tiles_kernel : Tiles (kernelTile E) (commonGraph E) :=
  kernelTile_graph E (outputs E)

end PeriodicTilingThree.CommonModel

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace PeriodicTilingThree

open scoped BigOperators

section CycleCombinatorics

variable {ι : Type uι} [Fintype ι]
variable {M : ι → Type uM} {N : ι → Type uN}
variable [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (N i)]
variable {t : ℕ} [NeZero t]

def cycleExtend (cycle : ZMod t ↪ ι) (v : ∀ j, M (cycle j)) : ∀ i, M i := by
  classical
  exact ∑ j : ZMod t, Pi.single (cycle j) (v j)

@[simp] theorem cycleExtend_apply
    {ι : Type uι} [Fintype ι]
    {M : ι → Type uM} [∀ i, AddCommGroup (M i)] {t : ℕ} [NeZero t]
    (cycle : ZMod t ↪ ι)
    (v : ∀ j, M (cycle j)) (j : ZMod t) :
    cycleExtend cycle v (cycle j) = v j := by
  classical
  rw [cycleExtend, Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro l _ hlj
    have hne : cycle l ≠ cycle j := fun h => hlj (cycle.injective h)
    simp [Ne.symm hne]
  · simp

theorem cycleExtend_eq_zero
    {ι : Type uι} [Fintype ι]
    {M : ι → Type uM} [∀ i, AddCommGroup (M i)] {t : ℕ} [NeZero t]
    (cycle : ZMod t ↪ ι)
    (v : ∀ j, M (cycle j)) {i : ι} (hi : ∀ j, cycle j ≠ i) :
    cycleExtend cycle v i = 0 := by
  classical
  rw [cycleExtend, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  simp [Ne.symm (hi j)]

def cycleShift (cycle : ZMod t ↪ ι) (U : ∀ j, AddSubgroup (M (cycle j)))
    (d : ∀ j, N (cycle (j - 1)) → U j) (e : ∀ i, N i) : ∀ i, M i :=
  cycleExtend cycle (fun j => (d j (e (cycle (j - 1))) : M (cycle j)))

@[simp] theorem cycleShift_apply
    {ι : Type uι} [Fintype ι]
    {M : ι → Type uM} {N : ι → Type uN}
    [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (N i)] {t : ℕ} [NeZero t]
    (cycle : ZMod t ↪ ι)
    (U : ∀ j, AddSubgroup (M (cycle j)))
    (d : ∀ j, N (cycle (j - 1)) → U j) (e : ∀ i, N i) (j : ZMod t) :
    cycleShift cycle U d e (cycle j) = (d j (e (cycle (j - 1))) : M (cycle j)) :=
  cycleExtend_apply cycle _ j

theorem cycleShift_eq_zero
    {ι : Type uι} [Fintype ι]
    {M : ι → Type uM} {N : ι → Type uN}
    [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (N i)] {t : ℕ} [NeZero t]
    (cycle : ZMod t ↪ ι)
    (U : ∀ j, AddSubgroup (M (cycle j)))
    (d : ∀ j, N (cycle (j - 1)) → U j) (e : ∀ i, N i)
    {i : ι} (hi : ∀ j, cycle j ≠ i) : cycleShift cycle U d e i = 0 :=
  cycleExtend_eq_zero cycle _ hi

def cycleMap (cycle : ZMod t ↪ ι) (U : ∀ j, AddSubgroup (M (cycle j)))
    (d : ∀ j, N (cycle (j - 1)) → U j)
    (g : ∀ i, M i → N i) (k : ∀ i, M i) (e : ∀ i, N i) : ∀ i, N i :=
  fun i => e i + g i (k i - cycleShift cycle U d e i)

@[simp] theorem cycleMap_apply_cycle (cycle : ZMod t ↪ ι)
    (U : ∀ j, AddSubgroup (M (cycle j)))
    (d : ∀ j, N (cycle (j - 1)) → U j)
    (g : ∀ i, M i → N i) (k : ∀ i, M i) (e : ∀ i, N i) (j : ZMod t) :
    cycleMap cycle U d g k e (cycle j) =
      e (cycle j) + g (cycle j) (k (cycle j) - d j (e (cycle (j - 1)))) := by
  simp only [cycleMap, cycleShift_apply]

theorem forall_of_cyclic_step {Q : ZMod t → Prop} (j₀ : ZMod t) (h₀ : Q j₀)
    (hstep : ∀ j, Q j → Q (j + 1)) : ∀ j, Q j := by
  have hnat : ∀ n : ℕ, Q (j₀ + (n : ZMod t)) := by
    intro n
    induction n with
    | zero => simpa using h₀
    | succ n ih => simpa only [Nat.cast_succ, add_assoc] using hstep _ ih
  intro j
  have h := hnat (j - j₀).val
  simpa only [ZMod.natCast_zmod_val, add_sub_cancel] using h

theorem cycleMap_injective_of_inactive (cycle : ZMod t ↪ ι)
    (U : ∀ j, AddSubgroup (M (cycle j)))
    (d : ∀ j, N (cycle (j - 1)) → U j)
    (g : ∀ i, M i → N i) (k : ∀ i, M i)
    (j₀ : ZMod t) (hinactive : ¬ DigitActive (g (cycle j₀)) (U j₀)) :
    Function.Injective (cycleMap cycle U d g k) := by
  classical
  have hagree {w w' : M (cycle j₀)} (hw : w - w' ∈ U j₀) :
      g (cycle j₀) w = g (cycle j₀) w' := by
    by_contra hne
    exact hinactive ⟨w, w', hw, hne⟩
  have hconstant (e : ∀ i, N i) :
      g (cycle j₀) (k (cycle j₀) - d j₀ (e (cycle (j₀ - 1)))) =
        g (cycle j₀) (k (cycle j₀)) := by
    apply hagree
    have heq : (k (cycle j₀) - (d j₀ (e (cycle (j₀ - 1))) : M (cycle j₀))) -
        k (cycle j₀) = -((d j₀ (e (cycle (j₀ - 1)))) : M (cycle j₀)) := by abel
    rw [heq]
    exact (U j₀).neg_mem (d j₀ (e (cycle (j₀ - 1)))).property
  intro e e' he
  have hstart : e (cycle j₀) = e' (cycle j₀) := by
    have h := congrFun he (cycle j₀)
    rw [cycleMap_apply_cycle, cycleMap_apply_cycle, hconstant, hconstant] at h
    exact add_right_cancel h
  have hstep (j : ZMod t) (hj : e (cycle j) = e' (cycle j)) :
      e (cycle (j + 1)) = e' (cycle (j + 1)) := by
    have h := congrFun he (cycle (j + 1))
    simp only [cycleMap_apply_cycle] at h
    have hprev : e (cycle (j + 1 - 1)) = e' (cycle (j + 1 - 1)) := by
      exact Eq.mpr (congrArg (fun l : ZMod t => e (cycle l) = e' (cycle l))
        (add_sub_cancel_right j 1)) hj
    rw [hprev] at h
    exact add_right_cancel h
  have hon := forall_of_cyclic_step j₀ hstart hstep
  funext i
  by_cases hi : ∃ j, cycle j = i
  · obtain ⟨j, rfl⟩ := hi
    exact hon j
  · have hoff : ∀ j, cycle j ≠ i := by simpa only [not_exists] using hi
    have h := congrFun he i
    simp only [cycleMap, cycleShift_eq_zero cycle U d e hoff,
      cycleShift_eq_zero cycle U d e' hoff, sub_zero] at h
    exact add_right_cancel h

theorem cycleMap_bijective_of_inactive [∀ i, Fintype (N i)]
    (cycle : ZMod t ↪ ι) (U : ∀ j, AddSubgroup (M (cycle j)))
    (d : ∀ j, N (cycle (j - 1)) → U j)
    (g : ∀ i, M i → N i) (k : ∀ i, M i)
    (j₀ : ZMod t) (hinactive : ¬ DigitActive (g (cycle j₀)) (U j₀)) :
    Function.Bijective (cycleMap cycle U d g k) :=
  (cycleMap_injective_of_inactive cycle U d g k j₀ hinactive).bijective_of_finite

theorem cycleMap_collision_of_all_active (cycle : ZMod t ↪ ι)
    (U : ∀ j, AddSubgroup (M (cycle j))) (g : ∀ i, M i → N i)
    (hactive : ∀ j, DigitActive (g (cycle j)) (U j)) :
    ∃ (k : ∀ i, M i) (d : ∀ j, N (cycle (j - 1)) → U j)
      (ε : ∀ i, N i), ε ≠ 0 ∧
      cycleMap cycle U d g k 0 = cycleMap cycle U d g k ε := by
  classical
  choose w w' hmem hne using hactive
  let ε₀ : ∀ j, N (cycle j) := fun j => g (cycle j) (w j) - g (cycle j) (w' j)
  have hε₀ (j : ZMod t) : ε₀ j ≠ 0 := sub_ne_zero.mpr (hne j)
  let ε : ∀ i, N i := cycleExtend cycle ε₀
  let k : ∀ i, M i := cycleExtend cycle w
  let d : ∀ j, N (cycle (j - 1)) → U j := fun j v =>
    if v = ε₀ (j - 1) then ⟨w j - w' j, hmem j⟩ else 0
  have hd₀ (j : ZMod t) : d j 0 = 0 := by
    simp only [d, ite_eq_right (Ne.symm (hε₀ (j - 1)))]
  have hdε (j : ZMod t) : d j (ε (cycle (j - 1))) = ⟨w j - w' j, hmem j⟩ := by
    simp only [d, ε, cycleExtend_apply, ite_eq_left rfl]
  refine ⟨k, d, ε, ?_, ?_⟩
  · intro hz
    have h := congrFun hz (cycle 0)
    apply hε₀ 0
    simpa only [ε, cycleExtend_apply, Pi.zero_apply] using h
  · funext i
    by_cases hi : ∃ j, cycle j = i
    · obtain ⟨j, rfl⟩ := hi
      calc
        cycleMap cycle U d g k 0 (cycle j) = g (cycle j) (w j) := by
          simp only [cycleMap_apply_cycle, Pi.zero_apply, hd₀, ZeroMemClass.coe_zero,
            sub_zero, zero_add, k, cycleExtend_apply]
        _ = ε₀ j + g (cycle j) (w' j) := (sub_add_cancel _ _).symm
        _ = cycleMap cycle U d g k ε (cycle j) := by
          rw [cycleMap_apply_cycle, hdε]
          simp only [k, ε, cycleExtend_apply, sub_sub_cancel]
    · have hoff : ∀ j, cycle j ≠ i := by simpa only [not_exists] using hi
      simp only [cycleMap, Pi.zero_apply, ε, cycleExtend_eq_zero cycle ε₀ hoff,
        cycleShift_eq_zero cycle U d 0 hoff,
        cycleShift_eq_zero cycle U d (cycleExtend cycle ε₀) hoff]

theorem forall_cycleMap_bijective_iff [∀ i, Fintype (N i)]
    (cycle : ZMod t ↪ ι) (U : ∀ j, AddSubgroup (M (cycle j)))
    (g : ∀ i, M i → N i) :
    (∀ (d : ∀ j, N (cycle (j - 1)) → U j) (k : ∀ i, M i),
      Function.Bijective (cycleMap cycle U d g k)) ↔
      ∃ j, ¬ DigitActive (g (cycle j)) (U j) := by
  constructor
  · intro hall
    by_contra hnone
    have hactive : ∀ j, DigitActive (g (cycle j)) (U j) := by
      simpa only [not_exists, not_not] using hnone
    obtain ⟨k, d, ε, hε, hcollision⟩ :=
      cycleMap_collision_of_all_active cycle U g hactive
    exact hε ((hall d k).1 hcollision).symm
  · rintro ⟨j, hj⟩ d k
    exact cycleMap_bijective_of_inactive cycle U d g k j hj

end CycleCombinatorics

theorem existsUnique_fixed_comp_iff {A : Type uA} {B : Type uB} (f : A → B) (g : B → A) :
    (∃! a, g (f a) = a) ↔ ∃! b, f (g b) = b := by
  constructor
  · rintro ⟨a, ha, hu⟩
    refine ⟨f a, ?_, ?_⟩
    · exact congrArg f ha
    · intro b hb
      have hg : g b = a := hu _ (congrArg g hb)
      calc
        b = f (g b) := hb.symm
        _ = f a := congrArg f hg
  · rintro ⟨b, hb, hu⟩
    refine ⟨g b, ?_, ?_⟩
    · exact congrArg g hb
    · intro a ha
      have hf : f a = b := hu _ (congrArg f ha)
      calc
        a = g (f a) := ha.symm
        _ = g b := congrArg g hf

theorem tiles_offset_iff_permutation
    {H : Type uH} {B : Type uB} {C : Type uC} [AddCommGroup H] [AddCommGroup B] [AddCommGroup C]
    (q : H →+ B) (ψ : H →+ C) (s : B → H) (hs : ∀ b, q (s b) = b)
    (hjoint : Function.Surjective (fun y => (q y, ψ y)))
    (Δ : C → B) (F : Finset H)
    (hF : ∀ y, y ∈ F ↔ q y = Δ (ψ y)) :
    Tiles F (Set.range s) ↔
      ∀ b, Function.Bijective (fun e => e + ψ (s (b - Δ e))) := by
  have hinj : Function.Injective s := by
    intro b b' h
    simpa only [hs] using congrArg q h
  have hmem (y : H) (b : B) : y - s b ∈ F ↔
      q y - Δ (ψ y - ψ (s b)) = b := by
    rw [hF, map_sub, hs, map_sub]
    simp only [sub_eq_iff_eq_add]
    exact ⟨fun h => h.trans (add_comm _ _), fun h => h.trans (add_comm _ _)⟩
  have hfibre (y : H) : (∃! b, y - s b ∈ F) ↔
      ∃! e, e + ψ (s (q y - Δ e)) = ψ y := by
    calc
      _ ↔ ∃! b, q y - Δ (ψ y - ψ (s b)) = b := existsUnique_congr (hmem y)
      _ ↔ ∃! e, ψ y - ψ (s (q y - Δ e)) = e :=
        existsUnique_fixed_comp_iff (fun b => ψ y - ψ (s b)) (fun e => q y - Δ e)
      _ ↔ _ := existsUnique_congr (fun e => by rw [sub_eq_iff_eq_add]; exact eq_comm)
  rw [tiles_range_iff_unique_base s hinj F]
  constructor
  · intro h b
    apply (Function.bijective_iff_existsUnique _).mpr
    intro c
    obtain ⟨y, hy⟩ := hjoint (b, c)
    have hq : q y = b := congrArg Prod.fst hy
    have hψ : ψ y = c := congrArg Prod.snd hy
    simpa only [hq, hψ] using (hfibre y).mp (h y)
  · intro h y
    exact (hfibre y).mpr ((h (q y)).existsUnique (ψ y))

section ConcreteTiles

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

def usefulProjection : Ambient E →+ Useful E where
  toFun v := fun i => (v.2.2 i).2
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem usefulProjection_apply (v : Ambient E) (i : Channel p) :
    usefulProjection E v i = (v.2.2 i).2 := rfl

@[simp] theorem usefulProjection_point (o : GraphOutputs E) (b : Base E) :
    usefulProjection E (point o b) = o.c b := rfl

theorem q0_usefulProjection_surjective :
    Function.Surjective (fun y : Ambient E => (q0 E y, usefulProjection E y)) := by
  rintro ⟨b, c⟩
  let o : GraphOutputs E := ⟨fun _ => c, fun _ => 0, fun _ => 0⟩
  refine ⟨point o b, ?_⟩
  exact Prod.ext (q0_point o b) rfl

private theorem offset_horizontal_zero (D : Useful E → Low E)
    (v : {v : Ambient E // q0 E v = (0, D (usefulProjection E v))}) :
    (v : Ambient E).1 = 0 := congrArg Prod.fst v.property

noncomputable instance offsetFintype (D : Useful E → Low E) :
    Fintype {v : Ambient E // q0 E v = (0, D (usefulProjection E v))} :=
  Fintype.ofInjective (fun v => (v : Ambient E).2) (by
    intro v w h
    apply Subtype.ext
    exact Prod.ext ((offset_horizontal_zero E D v).trans
      (offset_horizontal_zero E D w).symm) h)

def offsetTile (D : Useful E → Low E) : Finset (Ambient E) :=
  (Finset.univ : Finset {v : Ambient E // q0 E v = (0, D (usefulProjection E v))}).map
    ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem mem_offsetTile (D : Useful E → Low E) (v : Ambient E) :
    v ∈ offsetTile E D ↔ q0 E v = (0, D (usefulProjection E v)) := by
  constructor
  · intro h
    obtain ⟨w, _, rfl⟩ := Finset.mem_map.mp h
    exact w.property
  · intro h
    exact Finset.mem_map.mpr ⟨⟨v, h⟩, Finset.mem_univ _, rfl⟩

theorem offsetTile_nonempty (D : Useful E → Low E) : (offsetTile E D).Nonempty := by
  let o : GraphOutputs E := ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩
  refine ⟨point o (0, D 0), (mem_offsetTile E D _).mpr ?_⟩
  exact q0_point o (0, D 0)

theorem offsetTile_iff (D : Useful E → Low E) (o : GraphOutputs E) :
    Tiles (offsetTile E D) (graph o) ↔
      ∀ x k, Function.Bijective (fun e : Useful E => e + o.c (x, k - D e)) := by
  have h := tiles_offset_iff_permutation (q0 E) (usefulProjection E) (point o)
    (q0_point o) (q0_usefulProjection_surjective E) (fun e => (0, D e))
    (offsetTile E D) (mem_offsetTile E D)
  change Tiles (offsetTile E D) (graph o) ↔ _ at h
  constructor
  · intro htile x k
    have hb := h.mp htile (x, k)
    change Function.Bijective (fun e : Useful E => e + o.c (x - 0, k - D e)) at hb
    simpa only [sub_zero] using hb
  · intro hmap
    apply h.mpr
    rintro ⟨x, k⟩
    change Function.Bijective (fun e : Useful E => e + o.c (x - 0, k - D e))
    simpa only [sub_zero] using hmap x k

variable {t : ℕ} [NeZero t]

def cycleTile (cycle : ZMod t ↪ Channel p)
    (labels : ∀ j, Label p (cycle j))
    (d : ∀ j, P E (cycle (j - 1)) → digitSubgroup E (cycle j) (labels j)) :
    Finset (Ambient E) :=
  offsetTile E (cycleShift cycle (fun j => digitSubgroup E (cycle j) (labels j)) d)

theorem cycleTile_nonempty (cycle : ZMod t ↪ Channel p)
    (labels : ∀ j, Label p (cycle j))
    (d : ∀ j, P E (cycle (j - 1)) → digitSubgroup E (cycle j) (labels j)) :
    (cycleTile E cycle labels d).Nonempty := offsetTile_nonempty E _

theorem cycleTile_iff (cycle : ZMod t ↪ Channel p)
    (labels : ∀ j, Label p (cycle j))
    (d : ∀ j, P E (cycle (j - 1)) → digitSubgroup E (cycle j) (labels j))
    (o : GraphOutputs E) (g : ∀ i, Plane → K E i → P E i)
    (hfactor : ∀ x k i, o.c (x, k) i = g i x (k i)) :
    Tiles (cycleTile E cycle labels d) (graph o) ↔
      ∀ x k, Function.Bijective
        (cycleMap cycle (fun j => digitSubgroup E (cycle j) (labels j)) d
          (fun i => g i x) k) := by
  let U := fun j => digitSubgroup E (cycle j) (labels j)
  have hm (x : Plane) (k : Low E) :
      (fun e : Useful E => e + o.c (x, k - cycleShift cycle U d e)) =
        cycleMap cycle U d (fun i => g i x) k := by
    funext e i
    change e i + o.c (x, k - cycleShift cycle U d e) i =
      e i + g i x (k i - cycleShift cycle U d e i)
    exact congrArg (fun v => e i + v) (hfactor x (k - cycleShift cycle U d e) i)
  simpa only [cycleTile, hm] using offsetTile_iff E (cycleShift cycle U d) o

theorem all_cycleTile_iff (cycle : ZMod t ↪ Channel p)
    (labels : ∀ j, Label p (cycle j))
    (o : GraphOutputs E) (g : ∀ i, Plane → K E i → P E i)
    (hfactor : ∀ x k i, o.c (x, k) i = g i x (k i)) :
    (∀ d : ∀ j, P E (cycle (j - 1)) → digitSubgroup E (cycle j) (labels j),
      Tiles (cycleTile E cycle labels d) (graph o)) ↔
      ∀ x, ∃ j, ¬ DigitActive (g (cycle j) x) (digitSubgroup E (cycle j) (labels j)) := by
  constructor
  · intro h x
    apply (forall_cycleMap_bijective_iff cycle
      (fun j => digitSubgroup E (cycle j) (labels j)) (fun i => g i x)).mp
    intro d k
    exact (cycleTile_iff E cycle labels d o g hfactor).mp (h d) x k
  · intro h d
    apply (cycleTile_iff E cycle labels d o g hfactor).mpr
    intro x k
    obtain ⟨j, hj⟩ := h x
    exact cycleMap_bijective_of_inactive cycle
      (fun j => digitSubgroup E (cycle j) (labels j)) d (fun i => g i x) k j hj

def cycleTiles (cycle : ZMod t ↪ Channel p) (labels : ∀ j, Label p (cycle j)) :
    Finset (Finset (Ambient E)) := by
  classical
  exact Finset.univ.image (cycleTile E cycle labels)

theorem cycleTiles_nonempty (cycle : ZMod t ↪ Channel p)
    (labels : ∀ j, Label p (cycle j)) : (cycleTiles E cycle labels).Nonempty := by
  classical
  exact ⟨cycleTile E cycle labels (fun _ _ => 0),
    Finset.mem_image.mpr ⟨(fun _ _ => 0), Finset.mem_univ _, rfl⟩⟩

theorem nonempty_of_mem_cycleTiles (cycle : ZMod t ↪ Channel p)
    (labels : ∀ j, Label p (cycle j)) {F : Finset (Ambient E)}
    (hF : F ∈ cycleTiles E cycle labels) : F.Nonempty := by
  classical
  obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hF
  exact cycleTile_nonempty E cycle labels d

theorem forall_mem_cycleTiles_iff (cycle : ZMod t ↪ Channel p)
    (labels : ∀ j, Label p (cycle j)) (A : Set (Ambient E)) :
    (∀ F ∈ cycleTiles E cycle labels, Tiles F A) ↔
      ∀ d : ∀ j, P E (cycle (j - 1)) → digitSubgroup E (cycle j) (labels j),
        Tiles (cycleTile E cycle labels d) A := by
  classical
  simp only [cycleTiles, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro h d
    exact h _ ⟨d, rfl⟩
  · intro h F hF
    obtain ⟨d, rfl⟩ := hF
    exact h d

theorem cycle_exclusion_iff (cycle : ZMod t ↪ Channel p)
    (labels : ∀ j, Label p (cycle j)) (o : GraphOutputs E)
    (hdep : HasDependence E o) :
    (∀ F ∈ cycleTiles E cycle labels, Tiles F (graph o)) ↔
      ∀ x, ∃ j, ¬ Active E o (cycle j) x (labels j) := by
  rw [forall_mem_cycleTiles_iff]
  exact all_cycleTile_iff E cycle labels o (usefulAt E o) (usefulAt_factor E hdep)

end ConcreteTiles

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

def seedSymbol {p : ℕ} [NeZero p] (E : EncodingParameters p) (t : Fin 2) : Symbol p :=
  lastDigit p E.p_prime ((t.val : ℤ) + 1)

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

@[simp] theorem seedSymbol_coe (t : Fin 2) :
    (seedSymbol E t : ZMod p) = (t.val : ZMod p) + 1 := by
  have hlt : t.val + 1 < p := by
    have ht := t.isLt
    have hp := E.p_large
    omega
  have hnot : ¬ (p : ℤ) ∣ (t.val : ℤ) + 1 := by
    intro h
    apply Nat.not_dvd_of_pos_of_lt (Nat.succ_pos t.val) hlt
    apply Int.natCast_dvd_natCast.mp
    simpa only [Nat.cast_succ] using h
  simpa only [seedSymbol, Int.cast_add, Int.cast_natCast, Int.cast_one] using
    lastDigit_eq_of_not_dvd p E.p_prime hnot

theorem seedSymbol_injective : Function.Injective (seedSymbol E) := by
  intro s t h
  apply Fin.ext
  have hcoe : (seedSymbol E s : ZMod p) = (seedSymbol E t : ZMod p) :=
    congrArg (fun u : Symbol p => (u : ZMod p)) h
  rw [seedSymbol_coe, seedSymbol_coe] at hcoe
  have hcast : (s.val : ZMod p) = (t.val : ZMod p) := add_right_cancel hcoe
  have hmod := (ZMod.natCast_eq_natCast_iff' s.val t.val p).mp hcast
  have hp : 2 < p := by have := E.p_large; omega
  rw [Nat.mod_eq_of_lt (lt_trans s.isLt hp),
    Nat.mod_eq_of_lt (lt_trans t.isLt hp)] at hmod
  exact hmod

@[simp] theorem seedSymbol_eq_iff {s t : Fin 2} :
    seedSymbol E s = seedSymbol E t ↔ s = t :=
  ⟨fun h => seedSymbol_injective E h, fun h => congrArg (seedSymbol E) h⟩

theorem seedSymbol_ne {s t : Fin 2} (h : s ≠ t) :
    seedSymbol E s ≠ seedSymbol E t :=
  fun hst => h (seedSymbol_injective E hst)

@[simp] theorem seedSymbol_zero : seedSymbol E 0 = 1 := by
  simp [seedSymbol]

@[simp] theorem seedSymbol_one_coe : (seedSymbol E 1 : ZMod p) = 2 := by
  change (lastDigit p E.p_prime 2 : ZMod p) = 2
  exact lastDigit_two p E.p_prime (by have := E.p_large; omega)

theorem seedSymbol_zero_ne_one : seedSymbol E 0 ≠ seedSymbol E 1 :=
  seedSymbol_ne E (by decide)

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

variable {p : ℕ} [NeZero p]

def ordinaryCycle (p : ℕ) [NeZero p] : ZMod (p ^ 2) ↪ Channel p where
  toFun j := .inl ((ZMod.finEquiv (p ^ 2)).symm j)
  inj' _ _ h := (ZMod.finEquiv (p ^ 2)).symm.injective (Sum.inl.inj h)

def ordinaryCycleLabels (w : Word p) (j : ZMod (p ^ 2)) :
    Label p (ordinaryCycle p j) :=
  w ((ZMod.finEquiv (p ^ 2)).symm j)

def seedCycle (t : Fin 2) (n : Column p) : ZMod 2 ↪ Channel p where
  toFun j := Fin.cases (.inr t) (fun _ => .inl n) j
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · change Sum.inr t = Sum.inl n at h
      cases h
    · change Sum.inl n = Sum.inr t at h
      cases h
    · rfl

@[simp] theorem seedCycle_zero
    {p : ℕ} [NeZero p]
    (t : Fin 2) (n : Column p) :
    seedCycle t n 0 = .inr t := rfl

@[simp] theorem seedCycle_one
    {p : ℕ} [NeZero p]
    (t : Fin 2) (n : Column p) :
    seedCycle t n 1 = .inl n := rfl

def seedCycleLabels (t : Fin 2) (n : Column p) (j : Symbol p) (z : ZMod 2) :
    Label p (seedCycle t n z) :=
  Fin.cases (motive := fun z : Fin 2 => Label p (seedCycle t n z))
    () (fun _ => j) z

@[simp] theorem seedCycleLabels_zero
    {p : ℕ} [NeZero p]
    (t : Fin 2) (n : Column p) (j : Symbol p) :
    seedCycleLabels t n j 0 = () := rfl

@[simp] theorem seedCycleLabels_one
    {p : ℕ} [NeZero p]
    (t : Fin 2) (n : Column p) (j : Symbol p) :
    seedCycleLabels t n j 1 = j := rfl

variable (E : EncodingParameters p)

theorem ordinaryCycle_exclusion_iff (w : Word p) (o : GraphOutputs E)
    (hdep : HasDependence E o) :
    (∀ F ∈ cycleTiles E (ordinaryCycle p) (ordinaryCycleLabels w),
      Tiles F (graph o)) ↔
      ∀ x, ¬ (∀ n : Column p, Active E o (.inl n) x (w n)) := by
  classical
  rw [cycle_exclusion_iff E (ordinaryCycle p) (ordinaryCycleLabels w) o hdep]
  constructor
  · intro h x hall
    obtain ⟨z, hz⟩ := h x
    exact hz (hall ((ZMod.finEquiv (p ^ 2)).symm z))
  · intro h x
    obtain ⟨n, hn⟩ := not_forall.mp (h x)
    refine ⟨(ZMod.finEquiv (p ^ 2)) n, ?_⟩
    exact Eq.mpr
      (congrArg (fun m : Column p => ¬ Active E o (.inl m) x (w m))
        ((ZMod.finEquiv (p ^ 2)).symm_apply_apply n)) hn

theorem seedCycle_exclusion_iff (t : Fin 2) (n : Column p) (j : Symbol p)
    (o : GraphOutputs E) (hdep : HasDependence E o) :
    (∀ F ∈ cycleTiles E (seedCycle t n) (seedCycleLabels t n j),
      Tiles F (graph o)) ↔
      ∀ x, ¬ (Active E o (.inr t) x () ∧ Active E o (.inl n) x j) := by
  classical
  rw [cycle_exclusion_iff E (seedCycle t n) (seedCycleLabels t n j) o hdep]
  constructor
  · intro h x hx
    obtain ⟨z, hz⟩ := h x
    fin_cases z
    · exact hz hx.1
    · exact hz hx.2
  · intro h x
    by_cases hs : Active E o (.inr t) x ()
    · refine ⟨1, ?_⟩
      change ¬ Active E o (.inl n) x j
      intro hj
      exact h x ⟨hs, hj⟩
    · exact ⟨0, hs⟩

def wordConstraintTiles : Finset (Finset (Ambient E)) := by
  classical
  exact (Finset.univ.filter (fun w : Word p => w ∉ allowedWords p)).biUnion
    (fun w => cycleTiles E (ordinaryCycle p) (ordinaryCycleLabels w))

def seedConstraintTiles : Finset (Finset (Ambient E)) := by
  classical
  exact (Finset.univ.filter (fun q : Fin 2 × Column p × Symbol p =>
      q.2.2 ≠ seedSymbol E q.1)).biUnion
    (fun q => cycleTiles E (seedCycle q.1 q.2.1) (seedCycleLabels q.1 q.2.1 q.2.2))

theorem nonempty_of_mem_wordConstraintTiles {F : Finset (Ambient E)}
    (hF : F ∈ wordConstraintTiles E) : F.Nonempty := by
  classical
  obtain ⟨w, _, hF⟩ := Finset.mem_biUnion.mp hF
  exact nonempty_of_mem_cycleTiles E (ordinaryCycle p) (ordinaryCycleLabels w) hF

theorem nonempty_of_mem_seedConstraintTiles {F : Finset (Ambient E)}
    (hF : F ∈ seedConstraintTiles E) : F.Nonempty := by
  classical
  obtain ⟨q, _, hF⟩ := Finset.mem_biUnion.mp hF
  exact nonempty_of_mem_cycleTiles E (seedCycle q.1 q.2.1)
    (seedCycleLabels q.1 q.2.1 q.2.2) hF

theorem wordConstraintTiles_iff (o : GraphOutputs E) (hdep : HasDependence E o) :
    (∀ F ∈ wordConstraintTiles E, Tiles F (graph o)) ↔
      ∀ x w, (∀ n : Column p, Active E o (.inl n) x (w n)) → Allowed p w := by
  classical
  constructor
  · intro h x w hw
    by_contra hnot
    have hcycle : ∀ F ∈ cycleTiles E (ordinaryCycle p) (ordinaryCycleLabels w),
        Tiles F (graph o) := by
      intro F hF
      apply h F
      apply Finset.mem_biUnion.mpr
      exact ⟨w, by simp [hnot], hF⟩
    exact (ordinaryCycle_exclusion_iff E w o hdep).mp hcycle x hw
  · intro h F hF
    obtain ⟨w, hw, hF⟩ := Finset.mem_biUnion.mp hF
    have hnot : ¬ Allowed p w := by simpa using (Finset.mem_filter.mp hw).2
    apply (ordinaryCycle_exclusion_iff E w o hdep).mpr ?_ F hF
    intro x hx
    exact hnot (h x w hx)

theorem seedConstraintTiles_iff (o : GraphOutputs E) (hdep : HasDependence E o) :
    (∀ F ∈ seedConstraintTiles E, Tiles F (graph o)) ↔
      ∀ t n x j, Active E o (.inr t) x () → Active E o (.inl n) x j →
        j = seedSymbol E t := by
  classical
  constructor
  · intro h t n x j hseed hord
    by_contra hj
    have hcycle : ∀ F ∈ cycleTiles E (seedCycle t n) (seedCycleLabels t n j),
        Tiles F (graph o) := by
      intro F hF
      apply h F
      apply Finset.mem_biUnion.mpr
      exact ⟨(t, n, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, hF⟩
    exact (seedCycle_exclusion_iff E t n j o hdep).mp hcycle x ⟨hseed, hord⟩
  · intro h F hF
    obtain ⟨⟨t, n, j⟩, hq, hF⟩ := Finset.mem_biUnion.mp hF
    have hj : j ≠ seedSymbol E t := (Finset.mem_filter.mp hq).2
    apply (seedCycle_exclusion_iff E t n j o hdep).mpr ?_ F hF
    intro x hx
    exact hj (h t n x j hx.1 hx.2)

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

noncomputable section

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

def activationBatch (i : Channel p) (h : Plane) (e : P E i)
    (freeZ : Bool) : Finset (Ambient E) := by
  classical
  exact (Finset.univ.filter fun v : V E =>
    (v.2 i).1 = (h.1 : ZMod ((E.r i) ^ 2)) ∧ (v.2 i).2 = e ∧
    (∀ j, j ≠ i → low E j (v.2 j).1 = 0) ∧ (freeZ = true ∨ v.1 = 0)).image
      (fun v => (h, v))

theorem mem_activationBatch (i : Channel p) (h : Plane) (e : P E i)
    (freeZ : Bool) (g : Ambient E) :
    g ∈ activationBatch E i h e freeZ ↔
      g.1 = h ∧ (g.2.2 i).1 = (h.1 : ZMod ((E.r i) ^ 2)) ∧
      (g.2.2 i).2 = e ∧ (∀ j, j ≠ i → low E j (g.2.2 j).1 = 0) ∧
      (freeZ = true ∨ g.2.1 = 0) := by
  classical
  simp only [activationBatch, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨rfl, hv⟩
  · rintro ⟨hh, hv⟩
    exact ⟨g.2, hv, Prod.ext hh.symm rfl⟩

theorem activationBatch_nonempty (i : Channel p) (h : Plane) (e : P E i)
    (freeZ : Bool) : (activationBatch E i h e freeZ).Nonempty := by
  classical
  refine ⟨(h, 0, Function.update 0 i ((h.1 : ZMod ((E.r i) ^ 2)), e)), ?_⟩
  apply (mem_activationBatch E i h e freeZ _).mpr
  refine ⟨rfl, ?_, ?_, ?_, Or.inr rfl⟩
  · simp
  · simp
  · intro j hji
    simp [hji]

theorem activationBatch_q0 (i : Channel p) (h : Plane) (e : P E i)
    (freeZ : Bool) {g : Ambient E} (hg : g ∈ activationBatch E i h e freeZ) :
    q0 E g = (h, Function.update (0 : Input E) i (h.1 : K E i)) := by
  classical
  obtain ⟨hh, hv, _hc, hother, _hz⟩ := (mem_activationBatch E i h e freeZ g).mp hg
  apply Prod.ext hh
  funext j
  by_cases hji : j = i
  · subst j
    change low E i (g.2.2 i).1 = _
    rw [hv]
    simp [low]
  · simpa [hji] using hother j hji

theorem activationBatch_disjoint (i : Channel p) {h h' : Plane}
    (e e' : P E i) (z z' : Bool) (hh : h ≠ h') :
    Disjoint (activationBatch E i h e z) (activationBatch E i h' e' z') := by
  classical
  apply Finset.disjoint_left.mpr
  intro g hg hg'
  exact hh (((mem_activationBatch E i h e z g).mp hg).1.symm.trans
    ((mem_activationBatch E i h' e' z' g).mp hg').1)

def activationSource (i : Channel p) (b : Base E) (h : Plane) (l : K E i) : Base E :=
  (b.1 - h, Function.update b.2 i (b.2 i - l))

theorem activationSource_eq_sub (i : Channel p) (b : Base E) (h : Plane) (l : K E i) :
    activationSource E i b h l = b - (h, Function.update (0 : Input E) i l) := by
  classical
  refine Prod.ext rfl ?_
  funext j
  by_cases hji : j = i
  · subst j
    simp [activationSource]
  · simp [activationSource, hji]

theorem activationSource_shear (i : Channel p) (b : Base E) (h : Plane) (l β : K E i)
    (hl : (h.1 : K E i) = l) :
    shear E i (activationSource E i b h l).1.1
        ((activationSource E i b h l).2 i) β + (h.1 : ZMod ((E.r i) ^ 2)) =
      shear E i b.1.1 (b.2 i) β := by
  simpa [activationSource] using shear_source_add E i b.1.1 h.1 (b.2 i) l β hl

def targetBeta (y : Ambient E) (i : Channel p) : K E i :=
  (shearEquiv E i y.1.1 ((q0 E y).2 i)).symm ⟨(y.2.2 i).1, rfl⟩

@[simp] theorem shear_targetBeta (y : Ambient E) (i : Channel p) :
    shear E i y.1.1 ((q0 E y).2 i) (targetBeta E y i) = (y.2.2 i).1 :=
  congrArg Subtype.val ((shearEquiv E i y.1.1 ((q0 E y).2 i)).apply_symm_apply
    ⟨(y.2.2 i).1, rfl⟩)

@[simp] theorem targetBeta_point (o : GraphOutputs E) (b : Base E) (i : Channel p) :
    targetBeta E (point o b) i = o.beta b i := by
  apply shear_injective E i b.1.1 (b.2 i)
  simpa only [q0_point, point_horizontal, point_v] using shear_targetBeta E (point o b) i

theorem difference_mem_activationBatch (o : GraphOutputs E) (i : Channel p)
    (h : Plane) (l : K E i) (hl : (h.1 : K E i) = l) (e : P E i)
    (freeZ : Bool) (y : Ambient E) (b : Base E) :
    y - point o b ∈ activationBatch E i h e freeZ ↔
      activationSource E i (q0 E y) h l = b ∧
      o.c b i + e = (y.2.2 i).2 ∧ o.beta b i = targetBeta E y i ∧
      (freeZ = true ∨ o.z b = y.2.1) := by
  constructor
  · intro hm
    have hq := activationBatch_q0 E i h e freeZ hm
    have hq' : q0 E y - b = (h, Function.update (0 : Input E) i l) := by
      simpa only [map_sub, q0_point, hl] using hq
    have hb : activationSource E i (q0 E y) h l = b := by
      rw [activationSource_eq_sub]
      have he := congrArg (fun z : Base E => q0 E y - z) hq'
      simpa using he.symm
    obtain ⟨_hh, hv, hc, _hother, hz⟩ :=
      (mem_activationBatch E i h e freeZ (y - point o b)).mp hm
    refine ⟨hb, ?_, ?_, ?_⟩
    · change (y.2.2 i).2 - o.c b i = e at hc
      rw [← hc]
      abel
    · apply shear_injective E i y.1.1 ((q0 E y).2 i)
      rw [shear_targetBeta]
      have hs := activationSource_shear E i (q0 E y) h l (o.beta b i) hl
      rw [hb] at hs
      change (y.2.2 i).1 - shear E i b.1.1 (b.2 i) (o.beta b i) =
        (h.1 : ZMod ((E.r i) ^ 2)) at hv
      change shear E i b.1.1 (b.2 i) (o.beta b i) +
        (h.1 : ZMod ((E.r i) ^ 2)) =
        shear E i y.1.1 ((q0 E y).2 i) (o.beta b i) at hs
      rw [← hs, ← hv]
      abel
    · rcases hz with hz | hz
      · exact Or.inl hz
      · right
        change y.2.1 - o.z b = 0 at hz
        exact (sub_eq_zero.mp hz).symm
  · rintro ⟨hb, hc, hβ, hz⟩
    apply (mem_activationBatch E i h e freeZ (y - point o b)).mpr
    have hs := activationSource_shear E i (q0 E y) h l (o.beta b i) hl
    rw [hb, hβ] at hs
    change shear E i b.1.1 (b.2 i) (targetBeta E y i) +
      (h.1 : ZMod ((E.r i) ^ 2)) =
      shear E i y.1.1 ((q0 E y).2 i) (targetBeta E y i) at hs
    rw [shear_targetBeta] at hs
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change y.1 - b.1 = h
      rw [← hb]
      change y.1 - (y.1 - h) = h
      abel
    · change (y.2.2 i).1 - shear E i b.1.1 (b.2 i) (o.beta b i) =
        (h.1 : ZMod ((E.r i) ^ 2))
      rw [hβ]
      rw [← hs]
      abel
    · change (y.2.2 i).2 - o.c b i = e
      rw [← hc]
      abel
    · intro j hji
      change low E j ((y.2.2 j).1 - shear E j b.1.1 (b.2 j) (o.beta b j)) = 0
      rw [map_sub, low_shear, ← hb]
      simp [activationSource, hji, q0]
    · rcases hz with hz | hz
      · exact Or.inl hz
      · right
        change y.2.1 - o.z b = 0
        rw [hz, sub_self]

def ordinaryActivationTile (n : Column p) : Finset (Ambient E) := by
  classical
  exact Finset.univ.biUnion fun j : ActivationIndex E (.inl n) =>
    activationBatch E (.inl n) (ordinaryOffset E n j)
      (shift (E.a (.inl n)) (E.b (.inl n)) j.2) true

def seedActivationTile (t : Fin 2) : Finset (Ambient E) := by
  classical
  exact Finset.univ.biUnion fun j : SeedActivationIndex E t =>
    activationBatch E (.inr t) (seedOffset E t j)
      (shift (E.a (.inr t)) (E.b (.inr t)) j.1.2) false

def ordinarySource (n : Column p) (b : Base E) (j : ActivationIndex E (.inl n)) : Base E :=
  activationSource E (.inl n) b (ordinaryOffset E n j) j.1

def seedSource (t : Fin 2) (b : Base E) (j : SeedActivationIndex E t) : Base E :=
  activationSource E (.inr t) b (seedOffset E t j) j.1.1

@[simp] theorem ordinarySource_horizontal (n : Column p) (b : Base E)
    (j : ActivationIndex E (.inl n)) :
    (ordinarySource E n b j).1 = b.1 - ordinaryOffset E n j := rfl

@[simp] theorem ordinarySource_own (n : Column p) (b : Base E)
    (j : ActivationIndex E (.inl n)) :
    (ordinarySource E n b j).2 (.inl n) = b.2 (.inl n) - j.1 := by
  simp [ordinarySource, activationSource]

@[simp] theorem seedSource_horizontal (t : Fin 2) (b : Base E)
    (j : SeedActivationIndex E t) :
    (seedSource E t b j).1 = b.1 - seedOffset E t j := rfl

@[simp] theorem seedSource_own (t : Fin 2) (b : Base E)
    (j : SeedActivationIndex E t) :
    (seedSource E t b j).2 (.inr t) = b.2 (.inr t) - j.1.1 := by
  simp [seedSource, activationSource]

@[simp] theorem ordinarySource_lineValue (n : Column p) (b : Base E)
    (j : ActivationIndex E (.inl n)) :
    lineValue n (ordinarySource E n b j).1 = lineValue n b.1 := by
  simp only [ordinarySource_horizontal, lineValue, ordinaryOffset,
    Prod.fst_sub, Prod.snd_sub]
  ring

theorem seedSource_residue (t : Fin 2) (b : Base E) (j : SeedActivationIndex E t) :
    ((((seedSource E t b j).1.1 : ℤ) : ZMod (p ^ 2)),
      (((seedSource E t b j).1.2 : ℤ) : ZMod (p ^ 2))) =
      ((b.1.1 : ZMod (p ^ 2)), (b.1.2 : ZMod (p ^ 2))) - j.2 := by
  rw [seedSource_horizontal]
  simpa only [Prod.fst_sub, Prod.snd_sub, Int.cast_sub, Prod.mk_sub_mk] using
    congrArg (fun z : Residues p =>
      ((b.1.1 : ZMod (p ^ 2)), (b.1.2 : ZMod (p ^ 2))) - z)
      (seedOffset_residue E t j)

def ordinaryActivationMap (n : Column p) (o : GraphOutputs E) (b : Base E)
    (j : ActivationIndex E (.inl n)) : P E (.inl n) × K E (.inl n) :=
  (o.c (ordinarySource E n b j) (.inl n) + shift (E.a (.inl n)) (E.b (.inl n)) j.2,
    o.beta (ordinarySource E n b j) (.inl n))

def seedActivationMap (t : Fin 2) (o : GraphOutputs E) (b : Base E)
    (j : SeedActivationIndex E t) : (P E (.inr t) × K E (.inr t)) × ZMod (D p) :=
  ((o.c (seedSource E t b j) (.inr t) + shift (E.a (.inr t)) (E.b (.inr t)) j.1.2,
    o.beta (seedSource E t b j) (.inr t)), o.z (seedSource E t b j))

def ordinaryTarget (n : Column p) (y : Ambient E) : P E (.inl n) × K E (.inl n) :=
  ((y.2.2 (.inl n)).2, targetBeta E y (.inl n))

def seedTarget (t : Fin 2) (y : Ambient E) :
    (P E (.inr t) × K E (.inr t)) × ZMod (D p) :=
  (((y.2.2 (.inr t)).2, targetBeta E y (.inr t)), y.2.1)

theorem ordinarySource_injective (n : Column p) (b : Base E) :
    Function.Injective (ordinarySource E n b) := by
  intro j j' hj
  apply ordinaryOffset_injective E n
  have hh := congrArg (fun d : Base E => b.1 - d.1) hj
  simpa [ordinarySource, activationSource] using hh

theorem seedSource_injective (t : Fin 2) (b : Base E) :
    Function.Injective (seedSource E t b) := by
  intro j j' hj
  apply seedOffset_injective E t
  have hh := congrArg (fun d : Base E => b.1 - d.1) hj
  simpa [seedSource, activationSource] using hh

theorem difference_mem_ordinaryActivationTile (n : Column p) (o : GraphOutputs E)
    (y : Ambient E) (b : Base E) :
    y - point o b ∈ ordinaryActivationTile E n ↔
      ∃ j, ordinarySource E n (q0 E y) j = b ∧
        ordinaryActivationMap E n o (q0 E y) j = ordinaryTarget E n y := by
  classical
  simp only [ordinaryActivationTile, Finset.mem_biUnion, Finset.mem_univ, true_and]
  apply exists_congr
  intro j
  rw [difference_mem_activationBatch E o (.inl n) (ordinaryOffset E n j) j.1
    (ordinaryOffset_low E n j)]
  simp only [true_or, and_true]
  constructor
  · rintro ⟨hb, hc, hβ⟩
    change ordinarySource E n (q0 E y) j = b at hb
    refine ⟨hb, ?_⟩
    unfold ordinaryActivationMap ordinaryTarget
    rw [hb]
    exact Prod.ext hc hβ
  · rintro ⟨hb, hmap⟩
    unfold ordinaryActivationMap ordinaryTarget at hmap
    rw [hb] at hmap
    exact ⟨hb, congrArg Prod.fst hmap, congrArg Prod.snd hmap⟩

theorem difference_mem_seedActivationTile (t : Fin 2) (o : GraphOutputs E)
    (y : Ambient E) (b : Base E) :
    y - point o b ∈ seedActivationTile E t ↔
      ∃ j, seedSource E t (q0 E y) j = b ∧
        seedActivationMap E t o (q0 E y) j = seedTarget E t y := by
  classical
  simp only [seedActivationTile, Finset.mem_biUnion, Finset.mem_univ, true_and]
  apply exists_congr
  intro j
  rw [difference_mem_activationBatch E o (.inr t) (seedOffset E t j) j.1.1
    (seedOffset_low E t j)]
  simp only [Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨hb, hc, hβ, hz⟩
    change seedSource E t (q0 E y) j = b at hb
    refine ⟨hb, ?_⟩
    unfold seedActivationMap seedTarget
    rw [hb]
    exact Prod.ext (Prod.ext hc hβ) hz
  · rintro ⟨hb, hmap⟩
    unfold seedActivationMap seedTarget at hmap
    rw [hb] at hmap
    exact ⟨hb, congrArg (fun z => z.1.1) hmap,
      congrArg (fun z => z.1.2) hmap, congrArg Prod.snd hmap⟩

private theorem existsUnique_source_iff {J : Type uJ} {B : Type uB} (s : J → B)
    (hs : Function.Injective s) (Q : J → Prop) :
    (∃! b, ∃ j, s j = b ∧ Q j) ↔ ∃! j, Q j := by
  constructor
  · rintro ⟨b, ⟨j, hj, hQ⟩, huniq⟩
    refine ⟨j, hQ, ?_⟩
    intro j' hQ'
    apply hs
    exact (huniq (s j') ⟨j', rfl, hQ'⟩).trans hj.symm
  · rintro ⟨j, hj, huniq⟩
    refine ⟨s j, ⟨j, rfl, hj⟩, ?_⟩
    rintro b ⟨j', hj', hQ'⟩
    rw [← hj', huniq j' hQ']

theorem ordinaryTarget_surjective (n : Column p) (b : Base E)
    (q : P E (.inl n) × K E (.inl n)) :
    ∃ y : Ambient E, q0 E y = b ∧ ordinaryTarget E n y = q := by
  classical
  let o : GraphOutputs E :=
    ⟨fun _ => Function.update 0 (.inl n) q.1,
      fun _ => Function.update 0 (.inl n) q.2, fun _ => 0⟩
  refine ⟨point o b, q0_point o b, ?_⟩
  simp [ordinaryTarget, o]

theorem seedTarget_surjective (t : Fin 2) (b : Base E)
    (q : (P E (.inr t) × K E (.inr t)) × ZMod (D p)) :
    ∃ y : Ambient E, q0 E y = b ∧ seedTarget E t y = q := by
  classical
  let o : GraphOutputs E :=
    ⟨fun _ => Function.update 0 (.inr t) q.1.1,
      fun _ => Function.update 0 (.inr t) q.1.2, fun _ => q.2⟩
  refine ⟨point o b, q0_point o b, ?_⟩
  simp [seedTarget, o]

theorem ordinaryActivationTile_iff (n : Column p) (o : GraphOutputs E) :
    Tiles (ordinaryActivationTile E n) (graph o) ↔
      ∀ b : Base E, Function.Bijective (ordinaryActivationMap E n o b) := by
  rw [graph, tiles_range_iff_unique_base (point o) (point_injective o)]
  simp_rw [difference_mem_ordinaryActivationTile,
    existsUnique_source_iff _ (ordinarySource_injective E n _)]
  constructor
  · intro h b
    apply (Function.bijective_iff_existsUnique _).mpr
    intro q
    obtain ⟨y, hy, hq⟩ := ordinaryTarget_surjective E n b q
    simpa only [hy, hq] using h y
  · intro h y
    exact (h (q0 E y)).existsUnique (ordinaryTarget E n y)

theorem seedActivationTile_iff (t : Fin 2) (o : GraphOutputs E) :
    Tiles (seedActivationTile E t) (graph o) ↔
      ∀ b : Base E, Function.Bijective (seedActivationMap E t o b) := by
  rw [graph, tiles_range_iff_unique_base (point o) (point_injective o)]
  simp_rw [difference_mem_seedActivationTile,
    existsUnique_source_iff _ (seedSource_injective E t _)]
  constructor
  · intro h b
    apply (Function.bijective_iff_existsUnique _).mpr
    intro q
    obtain ⟨y, hy, hq⟩ := seedTarget_surjective E t b q
    simpa only [hy, hq] using h y
  · intro h y
    exact (h (q0 E y)).existsUnique (seedTarget E t y)

theorem ordinaryActivationTile_nonempty (n : Column p) :
    (ordinaryActivationTile E n).Nonempty := by
  classical
  let δ : ShiftIndex (E.a (.inl n)) (E.b (.inl n)) :=
    ⟨(0, 0), ⟨0, by simp [shiftMultiplicity]⟩⟩
  let j : ActivationIndex E (.inl n) := (0, δ)
  obtain ⟨g, hg⟩ := activationBatch_nonempty E (.inl n) (ordinaryOffset E n j)
    (shift (E.a (.inl n)) (E.b (.inl n)) j.2) true
  refine ⟨g, ?_⟩
  simp only [ordinaryActivationTile, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨j, hg⟩

theorem seedActivationTile_nonempty (t : Fin 2) :
    (seedActivationTile E t).Nonempty := by
  classical
  let δ : ShiftIndex (E.a (.inr t)) (E.b (.inr t)) := ⟨(0, 0), ⟨0, by simp [shiftMultiplicity]⟩⟩
  let j : SeedActivationIndex E t := ((0, δ), 0)
  obtain ⟨g, hg⟩ := activationBatch_nonempty E (.inr t) (seedOffset E t j)
    (shift (E.a (.inr t)) (E.b (.inr t)) j.1.2) false
  refine ⟨g, ?_⟩
  simp only [seedActivationTile, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨j, hg⟩

end

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

def testTiles : Finset (Finset (Ambient E)) := by
  classical
  exact {kernelTile E} ∪ dependenceTiles E ∪ wordConstraintTiles E ∪
    seedConstraintTiles E ∪ Finset.univ.image (ordinaryActivationTile E) ∪
    Finset.univ.image (seedActivationTile E)

theorem mem_testTiles_iff (F : Finset (Ambient E)) :
    F ∈ testTiles E ↔ F = kernelTile E ∨ F ∈ dependenceTiles E ∨
      F ∈ wordConstraintTiles E ∨ F ∈ seedConstraintTiles E ∨
      (∃ n : Column p, ordinaryActivationTile E n = F) ∨
      (∃ t : Fin 2, seedActivationTile E t = F) := by
  classical
  simp only [testTiles, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
    Finset.mem_univ, true_and, or_assoc]

theorem kernelTile_mem_testTiles : kernelTile E ∈ testTiles E :=
  (mem_testTiles_iff E _).mpr (Or.inl rfl)

theorem dependenceTiles_subset_testTiles : dependenceTiles E ⊆ testTiles E := by
  intro F hF
  exact (mem_testTiles_iff E F).mpr (Or.inr (Or.inl hF))

theorem wordConstraintTiles_subset_testTiles : wordConstraintTiles E ⊆ testTiles E := by
  intro F hF
  exact (mem_testTiles_iff E F).mpr (Or.inr (Or.inr (Or.inl hF)))

theorem seedConstraintTiles_subset_testTiles : seedConstraintTiles E ⊆ testTiles E := by
  intro F hF
  exact (mem_testTiles_iff E F).mpr (Or.inr (Or.inr (Or.inr (Or.inl hF))))

theorem ordinaryActivationTile_mem_testTiles (n : Column p) :
    ordinaryActivationTile E n ∈ testTiles E :=
  (mem_testTiles_iff E _).mpr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩)))))

theorem seedActivationTile_mem_testTiles (t : Fin 2) :
    seedActivationTile E t ∈ testTiles E :=
  (mem_testTiles_iff E _).mpr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨t, rfl⟩)))))

theorem testTiles_nonempty : (testTiles E).Nonempty :=
  ⟨kernelTile E, kernelTile_mem_testTiles E⟩

theorem nonempty_of_mem_testTiles {F : Finset (Ambient E)}
    (hF : F ∈ testTiles E) : F.Nonempty := by
  classical
  rcases (mem_testTiles_iff E F).mp hF with rfl | hF | hF | hF | ⟨n, rfl⟩ | ⟨t, rfl⟩
  · exact kernelTile_nonempty E
  · obtain ⟨d, _hd, rfl⟩ := Finset.mem_image.mp hF
    exact invarianceTile_nonempty E (dependenceChannel d) (dependenceShift E d)
  · exact nonempty_of_mem_wordConstraintTiles E hF
  · exact nonempty_of_mem_seedConstraintTiles E hF
  · exact ordinaryActivationTile_nonempty E n
  · exact seedActivationTile_nonempty E t

def Solves (A : Set (Ambient E)) : Prop :=
  ∀ F ∈ testTiles E, Tiles F A

theorem solves_iff (A : Set (Ambient E)) : Solves E A ↔
    Tiles (kernelTile E) A ∧
    (∀ F ∈ dependenceTiles E, Tiles F A) ∧
    (∀ F ∈ wordConstraintTiles E, Tiles F A) ∧
    (∀ F ∈ seedConstraintTiles E, Tiles F A) ∧
    (∀ n, Tiles (ordinaryActivationTile E n) A) ∧
    (∀ t, Tiles (seedActivationTile E t) A) := by
  constructor
  · intro h
    exact ⟨h _ (kernelTile_mem_testTiles E),
      fun F hF => h F (dependenceTiles_subset_testTiles E hF),
      fun F hF => h F (wordConstraintTiles_subset_testTiles E hF),
      fun F hF => h F (seedConstraintTiles_subset_testTiles E hF),
      fun n => h _ (ordinaryActivationTile_mem_testTiles E n),
      fun t => h _ (seedActivationTile_mem_testTiles E t)⟩
  · rintro ⟨hg, hd, hw, hs, ha, hb⟩ F hF
    rcases (mem_testTiles_iff E F).mp hF with rfl | hF | hF | hF | ⟨n, rfl⟩ | ⟨t, rfl⟩
    · exact hg
    · exact hd F hF
    · exact hw F hF
    · exact hs F hF
    · exact ha n
    · exact hb t

abbrev TestIndex := ↥(testTiles E)

def testTile (i : TestIndex E) : Finset (Ambient E) := i.val

theorem testTile_nonempty (i : TestIndex E) : (testTile E i).Nonempty :=
  nonempty_of_mem_testTiles E i.property

instance testIndex_nonempty : Nonempty (TestIndex E) :=
  ⟨⟨kernelTile E, kernelTile_mem_testTiles E⟩⟩

theorem solves_iff_index (A : Set (Ambient E)) :
    Solves E A ↔ ∀ i : TestIndex E, Tiles (testTile E i) A := by
  constructor
  · intro h i
    exact h i.val i.property
  · intro h F hF
    exact h ⟨F, hF⟩

theorem exists_graph_of_solves {A : Set (Ambient E)} (hA : Solves E A) :
    ∃ o : GraphOutputs E, graph o = A :=
  (kernelTile_iff_graph E A).mp (hA _ (kernelTile_mem_testTiles E))

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree.CommonModel

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

theorem ordinaryActivationMap_outputs (n : Column p) (b : Base E) :
    ordinaryActivationMap E n (outputs E) b =
      ordinaryForward E n b.1 (b.2 (.inl n)) := by
  funext j
  simp [ordinaryActivationMap, ordinarySource, activationSource, outputs, ordinaryForward]

theorem seedActivationMap_outputs (t : Fin 2) (b : Base E) :
    seedActivationMap E t (outputs E) b = seedActualForward E t b.1 b.2 := by
  rfl

theorem common_solution : Solves E (commonGraph E) := by
  apply (solves_iff E (commonGraph E)).mpr
  refine ⟨commonGraph_tiles_kernel E, ?_, ?_, ?_, ?_, ?_⟩
  · exact (dependenceTiles_iff E (outputs E)).mpr (outputs_hasDependence E)
  · exact (wordConstraintTiles_iff E (outputs E) (outputs_hasDependence E)).mpr
      (active_word_allowed E)
  · apply (seedConstraintTiles_iff E (outputs E) (outputs_hasDependence E)).mpr
    intro t n x j ht hj
    exact active_seed_forces_symbol E t n x j ht hj
  · intro n
    apply (ordinaryActivationTile_iff E n (outputs E)).mpr
    intro b
    rw [ordinaryActivationMap_outputs]
    exact ordinaryForward_bijective E n b.1 (b.2 (.inl n))
  · intro t
    apply (seedActivationTile_iff E t (outputs E)).mpr
    intro b
    rw [seedActivationMap_outputs]
    exact seedActualForward_bijective E t b.1 b.2

theorem commonGraph_tiles_testTile (i : TestIndex E) :
    Tiles (testTile E i) (commonGraph E) :=
  (solves_iff_index E (commonGraph E)).mp (common_solution E) i

end PeriodicTilingThree.CommonModel

namespace PeriodicTilingThree

theorem exists_common_solution {p : ℕ} [NeZero p] (E : EncodingParameters p) :
    ∃ A : Set (Ambient E), Solves E A :=
  ⟨CommonModel.commonGraph E, CommonModel.common_solution E⟩

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace PeriodicTilingThree

open scoped BigOperators

def MixedDifferenceZero {a b : ℕ} (Q : ZMod a × ZMod b → ℤ) : Prop :=
  ∀ x y, Q (x, y) - Q (x - 1, y) - Q (x, y - 1) + Q (x - 1, y - 1) = 0

private theorem zmod_eq_zero_of_pred_invariant {n : ℕ} [NeZero n] {α : Type uα}
    (f : ZMod n → α) (hf : ∀ x, f x = f (x - 1)) (x : ZMod n) : f x = f 0 := by
  have hnat : ∀ m : ℕ, f (m : ZMod n) = f 0 := by
    intro m
    induction m with
    | zero => simp only [Nat.cast_zero]
    | succ m ih =>
        calc
          f ((m + 1 : ℕ) : ZMod n) = f (m : ZMod n) := by
            simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using
              hf ((m : ZMod n) + 1)
          _ = f 0 := ih
  simpa only [ZMod.natCast_zmod_val] using hnat x.val

theorem mixedDifference_rectangle {a b : ℕ} [NeZero a] [NeZero b]
    (Q : ZMod a × ZMod b → ℤ) (hmixed : MixedDifferenceZero Q)
    (x x₀ : ZMod a) (y : ZMod b) :
    Q (x, y) - Q (x₀, y) = Q (x, 0) - Q (x₀, 0) := by
  have hfirst (z : ZMod a) :
      Q (z, y) - Q (z - 1, y) = Q (z, 0) - Q (z - 1, 0) := by
    apply zmod_eq_zero_of_pred_invariant
      (fun w : ZMod b => Q (z, w) - Q (z - 1, w))
    intro w
    have h := hmixed z w
    linarith only [h]
  have hrow (z : ZMod a) :
      Q (z, y) - Q (z, 0) = Q (0, y) - Q (0, 0) := by
    apply zmod_eq_zero_of_pred_invariant
      (fun w : ZMod a => Q (w, y) - Q (w, 0))
    intro w
    have h := hfirst w
    linarith only [h]
  linarith only [hrow x, hrow x₀]

theorem histogram_separable {a b : ℕ} [NeZero a] [NeZero b]
    (Q : ZMod a × ZMod b → ℕ)
    (hmixed : MixedDifferenceZero (fun z => (Q z : ℤ))) :
    ∃ u : ZMod a → ℕ, ∃ v : ZMod b → ℕ, ∀ x y, Q (x, y) = u x + v y := by
  classical
  obtain ⟨x₀, _hx₀, hmin⟩ := Finset.exists_min_image
    (Finset.univ : Finset (ZMod a)) (fun x => Q (x, 0)) Finset.univ_nonempty
  let u : ZMod a → ℕ := fun x => Q (x, 0) - Q (x₀, 0)
  let v : ZMod b → ℕ := fun y => Q (x₀, y)
  refine ⟨u, v, ?_⟩
  intro x y
  have hle : Q (x₀, 0) ≤ Q (x, 0) := hmin x (Finset.mem_univ x)
  have hrectangle := mixedDifference_rectangle
    (fun z => (Q z : ℤ)) hmixed x x₀ y
  dsimp [u, v]
  omega

theorem histogram_mass_eq {a b : ℕ} [NeZero a] [NeZero b]
    (Q : ZMod a × ZMod b → ℕ) (u : ZMod a → ℕ) (v : ZMod b → ℕ)
    (hsep : ∀ x y, Q (x, y) = u x + v y) :
    (∑ z, Q z) = b * (∑ x, u x) + a * (∑ y, v y) := by
  calc
    (∑ z, Q z) = ∑ x : ZMod a, ∑ y : ZMod b, (u x + v y) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      exact hsep x y
    _ = b * (∑ x, u x) + a * (∑ y, v y) := by
      simp [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem histogram_mass_dvd {a b D : ℕ} [NeZero a] [NeZero b]
    (Q : ZMod a × ZMod b → ℕ)
    (hmixed : MixedDifferenceZero (fun z => (Q z : ℤ)))
    (hmass : (∑ z, Q z) = D) (hlarge : D < b) : a ∣ D := by
  obtain ⟨u, v, hsep⟩ := histogram_separable Q hmixed
  have htotal : D = b * (∑ x, u x) + a * (∑ y, v y) := by
    rw [← hmass]
    exact histogram_mass_eq Q u v hsep
  have hu : (∑ x, u x) = 0 := by
    by_contra hne
    have hone : 1 ≤ ∑ x, u x := Nat.one_le_iff_ne_zero.mpr hne
    have hmul : b ≤ b * (∑ x, u x) := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left b hone
    omega
  refine ⟨∑ y, v y, ?_⟩
  simpa only [hu, Nat.mul_zero, Nat.zero_add] using htotal

private theorem sum_histogram_corner {a b : ℕ} [NeZero a] [NeZero b]
    (f : ZMod a × ZMod b → ℤ) (x : ZMod a) (y : ZMod b) :
    (∑ e : ZMod a × ZMod b,
      ((if e.1 = x then (1 : ℤ) else 0) * (if e.2 = y then 1 else 0)) * f e) =
        f (x, y) := by
  classical
  have hterm (e : ZMod a × ZMod b) :
      ((if e.1 = x then (1 : ℤ) else 0) * (if e.2 = y then 1 else 0)) * f e =
        if e = (x, y) then f e else 0 := by
    rcases e with ⟨x', y'⟩
    by_cases hx : x' = x <;> by_cases hy : y' = y <;>
      simp [hx, hy, Prod.mk.injEq]
  simp_rw [hterm]
  simp

theorem sum_shiftOmega_mul {a b : ℕ} [NeZero a] [NeZero b]
    (Q : ZMod a × ZMod b → ℤ) (x : ZMod a) (y : ZMod b) :
    (∑ e : ZMod a × ZMod b, shiftOmega a b e * Q ((x, y) - e)) =
      Q (x, y) - Q (x - 1, y) - Q (x, y - 1) + Q (x - 1, y - 1) := by
  classical
  have hexpand (e : ZMod a × ZMod b) :
      shiftOmega a b e * Q ((x, y) - e) =
        ((if e.1 = 0 then (1 : ℤ) else 0) * (if e.2 = 0 then 1 else 0)) *
            Q ((x, y) - e) -
          ((if e.1 = 1 then (1 : ℤ) else 0) * (if e.2 = 0 then 1 else 0)) *
            Q ((x, y) - e) -
          ((if e.1 = 0 then (1 : ℤ) else 0) * (if e.2 = 1 then 1 else 0)) *
            Q ((x, y) - e) +
          ((if e.1 = 1 then (1 : ℤ) else 0) * (if e.2 = 1 then 1 else 0)) *
            Q ((x, y) - e) := by
    unfold shiftOmega
    ring
  simp_rw [hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [sum_histogram_corner, Prod.mk_sub_mk, sub_zero]

theorem mixedDifferenceZero_of_shift_sum {a b D : ℕ} [NeZero a] [NeZero b]
    (ha : 2 ≤ a) (hb : 2 ≤ b) (Q : ZMod a × ZMod b → ℕ)
    (hmass : (∑ z, Q z) = D)
    (hcoverage : ∀ c : ZMod a × ZMod b,
      (∑ δ : ShiftIndex a b, Q (c - shift a b δ)) = D) :
    MixedDifferenceZero (fun z => (Q z : ℤ)) := by
  classical
  intro x y
  have hcount :
      (∑ δ : ShiftIndex a b, (Q ((x, y) - shift a b δ) : ℤ)) = (D : ℤ) := by
    exact_mod_cast hcoverage (x, y)
  rw [sum_shift (fun e : ZMod a × ZMod b => (Q ((x, y) - e) : ℤ))] at hcount
  simp only [nsmul_eq_mul] at hcount
  simp_rw [shiftMultiplicity_cast ha hb] at hcount
  simp only [add_mul, one_mul, Finset.sum_add_distrib] at hcount
  have hbase : (∑ e : ZMod a × ZMod b, (Q ((x, y) - e) : ℤ)) = (D : ℤ) := by
    have hinv : Function.Involutive (fun e : ZMod a × ZMod b => (x, y) - e) :=
      fun e => sub_sub_cancel (x, y) e
    calc
      (∑ e : ZMod a × ZMod b, (Q ((x, y) - e) : ℤ)) = ∑ e, (Q e : ℤ) :=
        hinv.bijective.sum_comp (fun e => (Q e : ℤ))
      _ = (D : ℤ) := by exact_mod_cast hmass
  rw [hbase, sum_shiftOmega_mul (fun z => (Q z : ℤ)) x y] at hcount
  linarith only [hcount]

theorem histogram_mass_dvd_of_shift_sum {a b D : ℕ} [NeZero a] [NeZero b]
    (ha : 2 ≤ a) (hb : 2 ≤ b) (Q : ZMod a × ZMod b → ℕ)
    (hmass : (∑ z, Q z) = D) (hlarge : D < b)
    (hcoverage : ∀ c : ZMod a × ZMod b,
      (∑ δ : ShiftIndex a b, Q (c - shift a b δ)) = D) : a ∣ D :=
  histogram_mass_dvd Q (mixedDifferenceZero_of_shift_sum ha hb Q hmass hcoverage)
    hmass hlarge

theorem sum_firstCoordinate_of_bijective
    {J : Type uJ} {C : Type uC} {K : Type uK} [Fintype J] [Fintype C] [Fintype K] [DecidableEq C]
    (f : J → C × K) (hf : Function.Bijective f) (c : C) :
    (∑ j, if (f j).1 = c then (1 : ℕ) else 0) = Fintype.card K := by
  calc
    _ = ∑ z : C × K, if z.1 = c then (1 : ℕ) else 0 :=
      hf.sum_comp (fun z => if z.1 = c then (1 : ℕ) else 0)
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      dsimp only
      simp only [Fintype.sum_ite_eq', Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, Nat.cast_id]

theorem card_firstCoordinate_of_bijective
    {J : Type uJ} {C : Type uC} {K : Type uK} [Fintype J] [Fintype C] [Fintype K] [DecidableEq C]
    (f : J → C × K) (hf : Function.Bijective f) (c : C) :
    Fintype.card {j : J // (f j).1 = c} = Fintype.card K := by
  simpa only [Fintype.card_subtype, Finset.card_filter] using
    sum_firstCoordinate_of_bijective f hf c

theorem sum_firstFirstCoordinate_of_bijective
    {J : Type uJ} {C : Type uC} {K : Type uK} {Z : Type uZ}
    [Fintype J] [Fintype C] [Fintype K] [Fintype Z]
    [DecidableEq C] (f : J → (C × K) × Z) (hf : Function.Bijective f) (c : C) :
    (∑ j, if (f j).1.1 = c then (1 : ℕ) else 0) =
      Fintype.card K * Fintype.card Z := by
  have h := sum_firstCoordinate_of_bijective
    (fun j => Equiv.prodAssoc C K Z (f j))
    ((Equiv.prodAssoc C K Z).bijective.comp hf) c
  change (∑ j, if (f j).1.1 = c then (1 : ℕ) else 0) =
    Fintype.card (K × Z) at h
  simpa only [Fintype.card_prod] using h

theorem card_firstFirstCoordinate_of_bijective
    {J : Type uJ} {C : Type uC} {K : Type uK} {Z : Type uZ}
    [Fintype J] [Fintype C] [Fintype K] [Fintype Z]
    [DecidableEq C] (f : J → (C × K) × Z) (hf : Function.Bijective f) (c : C) :
    Fintype.card {j : J // (f j).1.1 = c} =
      Fintype.card K * Fintype.card Z := by
  simpa only [Fintype.card_subtype, Finset.card_filter] using
    sum_firstFirstCoordinate_of_bijective f hf c

def seedHistogram {p : ℕ} [NeZero p] {C : Type uC}
    (q : Residues p → C) (c : C) : ℕ := by
  classical
  exact Fintype.card {s : Residues p // q s = c}

theorem seedHistogram_eq_sum {p : ℕ} [NeZero p] {C : Type uC} [DecidableEq C]
    (q : Residues p → C) (c : C) :
    seedHistogram q c = ∑ s : Residues p, if q s = c then (1 : ℕ) else 0 := by
  simp only [seedHistogram, Fintype.card_subtype, Finset.card_filter]

theorem sum_seedHistogram {p : ℕ} [NeZero p] {C : Type uC} [Fintype C]
    (q : Residues p → C) : (∑ c, seedHistogram q c) = p ^ 4 := by
  classical
  calc
    (∑ c, seedHistogram q c) =
        Fintype.card (Σ c : C, {s : Residues p // q s = c}) := by
      simp only [Fintype.card_sigma, seedHistogram]
    _ = Fintype.card (Residues p) := Fintype.card_congr (Equiv.sigmaFiberEquiv q)
    _ = p ^ 4 := by
      simp only [Residues, Fintype.card_prod, ZMod.card]
      ring

theorem sum_seedHistogram_translate {p : ℕ} [NeZero p]
    {C : Type uC} [AddCommGroup C] [DecidableEq C]
    (q : Residues p → C) (s : Residues p) (e c : C) :
    (∑ τ : Residues p, if q (s - τ) + e = c then (1 : ℕ) else 0) =
      seedHistogram q (c - e) := by
  have hinv : Function.Involutive (fun τ : Residues p => s - τ) :=
    fun τ => sub_sub_cancel s τ
  rw [seedHistogram_eq_sum]
  simpa only [eq_sub_iff_add_eq] using
    hinv.bijective.sum_comp (fun τ => if q τ + e = c then (1 : ℕ) else 0)

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

theorem ordinary_active_of_tile (o : Outputs E) (hdep : HasDependence E o)
    (n : Column p) (htile : Tiles (ordinaryActivationTile E n) (graph o)) :
    ∀ x, ∃ j, Active E o (.inl n) x j := by
  classical
  intro x
  by_contra hno
  obtain ⟨c₀, hc⟩ := (no_active_iff_constant E o (.inl n) x).mp
    (fun j hj => hno ⟨j, hj⟩)
  have hsource (j : ActivationIndex E (.inl n)) :
      o.c (ordinarySource E n (x, 0) j) (.inl n) = c₀ := by
    calc
      _ = usefulAt E o (.inl n) (ordinarySource E n (x, 0) j).1
          ((ordinarySource E n (x, 0) j).2 (.inl n)) :=
        usefulAt_factor E hdep _ _ _
      _ = usefulAt E o (.inl n) x
          ((ordinarySource E n (x, 0) j).2 (.inl n)) :=
        usefulAt_eq_of_lineValue_eq E hdep n (ordinarySource_lineValue E n (x, 0) j) _
      _ = c₀ := hc _
  have hmap (j : ActivationIndex E (.inl n)) :
      (ordinaryActivationMap E n o (x, 0) j).1 =
        c₀ + shift (E.a (.inl n)) (E.b (.inl n)) j.2 := by
    change o.c (ordinarySource E n (x, 0) j) (.inl n) + _ = _
    rw [hsource]
  have htwo : (∑ δ : ShiftIndex (E.a (.inl n)) (E.b (.inl n)),
      if shift (E.a (.inl n)) (E.b (.inl n)) δ = 0 then (1 : ℕ) else 0) = 2 := by
    calc
      _ = ∑ e : P E (.inl n), shiftMultiplicity (E.a (.inl n)) (E.b (.inl n)) e •
          (if e = 0 then (1 : ℕ) else 0) := sum_shift _
      _ = shiftMultiplicity (E.a (.inl n)) (E.b (.inl n)) (0 : P E (.inl n)) := by
        simp [mul_ite]
      _ = 2 := by
        change shiftMultiplicity (E.a (.inl n)) (E.b (.inl n)) (0, 0) = 2
        exact shiftMultiplicity_zero
  have hcount := sum_firstCoordinate_of_bijective
    (ordinaryActivationMap E n o (x, 0))
    ((ordinaryActivationTile_iff E n o).mp htile (x, 0)) c₀
  simp_rw [hmap, add_eq_left] at hcount
  rw [Fintype.sum_prod_type] at hcount
  have hbad : E.r (.inl n) * 2 = E.r (.inl n) := by
    simpa only [htwo, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id, K, ZMod.card]
      using hcount
  have hr := E.r_pos (.inl n)
  omega

theorem seed_active_somewhere_of_tile (o : Outputs E) (hdep : HasDependence E o)
    (t : Fin 2) (htile : Tiles (seedActivationTile E t) (graph o)) :
    ∃ x, Active E o (.inr t) x () := by
  classical
  by_contra hno
  have hinactive (x : Plane) : ¬ Active E o (.inr t) x () :=
    fun hx => hno ⟨x, hx⟩
  let q : Residues p → P E (.inr t) := fun s => seedFactor E o t s 0
  have hconstant (s : Residues p) (w : K E (.inr t)) :
      seedFactor E o t s w = q s := by
    obtain ⟨c, hc⟩ := (no_active_iff_constant E o (.inr t)
      (seedRepresentative p s)).mp (by
        intro j
        cases j
        exact hinactive (seedRepresentative p s))
    exact (hc w).trans (hc 0).symm
  have hfactor (x : Plane) (k : Input E) :
      o.c (x, k) (.inr t) = q (seedResidue p x) :=
    (seedFactor_spec E hdep t x k).trans (hconstant _ _)
  let b₀ : Base E := (0, 0)
  have hmap (j : SeedActivationIndex E t) :
      (seedActivationMap E t o b₀ j).1.1 =
        q (seedResidue p b₀.1 - j.2) +
          shift (E.a (.inr t)) (E.b (.inr t)) j.1.2 := by
    have hf := hfactor (seedSource E t b₀ j).1 (seedSource E t b₀ j).2
    change o.c (seedSource E t b₀ j) (.inr t) = _ at hf
    change o.c (seedSource E t b₀ j) (.inr t) + _ = _
    rw [hf]
    have hs : seedResidue p (seedSource E t b₀ j).1 =
        seedResidue p b₀.1 - j.2 := seedSource_residue E t b₀ j
    rw [hs]
  have hcoverage (c : P E (.inr t)) :
      (∑ δ : ShiftIndex (E.a (.inr t)) (E.b (.inr t)),
        seedHistogram q (c - shift (E.a (.inr t)) (E.b (.inr t)) δ)) = D p := by
    have hcount := sum_firstFirstCoordinate_of_bijective
      (seedActivationMap E t o b₀) ((seedActivationTile_iff E t o).mp htile b₀) c
    simp_rw [hmap] at hcount
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at hcount
    simp_rw [sum_seedHistogram_translate] at hcount
    have hmul : E.r (.inr t) *
        (∑ δ : ShiftIndex (E.a (.inr t)) (E.b (.inr t)),
          seedHistogram q (c - shift (E.a (.inr t)) (E.b (.inr t)) δ)) =
        E.r (.inr t) * D p := by
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id, K, ZMod.card]
        using hcount
    exact Nat.eq_of_mul_eq_mul_left (E.r_pos (.inr t)) hmul
  have hdiv : E.a (.inr t) ∣ p ^ 4 :=
    histogram_mass_dvd_of_shift_sum (E.a_two_le (.inr t)) (E.b_two_le (.inr t))
      (seedHistogram q) (sum_seedHistogram q) (E.seed_b_large t) hcoverage
  exact E.prime_ne_p (.inl (.inr t))
    (Nat.prime_eq_prime_of_dvd_pow (E.a_prime (.inr t)) E.p_prime hdiv)

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

def activeLabels (o : GraphOutputs E) (i : Channel p) (x : Plane) :
    Finset (Label p i) := by
  classical
  exact Finset.univ.filter (Active E o i x)

@[simp] theorem mem_activeLabels (o : GraphOutputs E) (i : Channel p)
    (x : Plane) (j : Label p i) :
    j ∈ activeLabels E o i x ↔ Active E o i x j := by
  classical
  simp [activeLabels]

def selectSymbol (S : Finset (Symbol p)) : Symbol p := by
  classical
  exact if h : S.Nonempty then h.choose else 1

theorem selectSymbol_mem
    {p : ℕ} [NeZero p]
    (S : Finset (Symbol p)) (hS : S.Nonempty) :
    selectSymbol S ∈ S := by
  classical
  rw [selectSymbol, dif_pos hS]
  exact hS.choose_spec

def selectedWord (o : GraphOutputs E) : WordArray p :=
  fun n m => selectSymbol (activeLabels E o (.inl n) (0, m))

theorem selectedWord_active (o : GraphOutputs E)
    (hactive : ∀ n x, ∃ j, Active E o (.inl n) x j) (n : Column p) (m : ℤ) :
    Active E o (.inl n) (0, m) (selectedWord E o n m) := by
  apply (mem_activeLabels E o (.inl n) (0, m) _).mp
  apply selectSymbol_mem
  obtain ⟨j, hj⟩ := hactive n (0, m)
  exact ⟨j, (mem_activeLabels E o (.inl n) (0, m) j).mpr hj⟩

theorem selectedWord_active_at (o : GraphOutputs E) (hdep : HasDependence E o)
    (hactive : ∀ n x, ∃ j, Active E o (.inl n) x j) (n : Column p) (x : Plane) :
    Active E o (.inl n) x (selectedWord E o n (lineValue n x)) := by
  apply (active_ordinary_iff E hdep n (y := (0, lineValue n x))
    (by simp) _).mpr
  exact selectedWord_active E o hactive n _

theorem selectedWord_lineRule (o : GraphOutputs E) (hdep : HasDependence E o)
    (hactive : ∀ n x, ∃ j, Active E o (.inl n) x j)
    (hwords : ∀ x (w : Word p), (∀ n, Active E o (.inl n) x (w n)) → Allowed p w) :
    LineRule p (selectedWord E o) := by
  intro d e
  apply hwords (d, e)
  intro n
  simpa only [lineValue, mul_comm, add_comm] using
    selectedWord_active_at E o hdep hactive n (d, e)

theorem selectedWord_nonconstant_of_forced_letters
    (o : GraphOutputs E) (hdep : HasDependence E o)
    (hactive : ∀ n x, ∃ j, Active E o (.inl n) x j)
    (a b : Symbol p) (hab : a ≠ b) (x y : Plane)
    (hx : ∀ n j, Active E o (.inl n) x j → j = a)
    (hy : ∀ n j, Active E o (.inl n) y j → j = b) :
    NonconstantColumns (selectedWord E o) := by
  intro n
  refine ⟨lineValue n x, lineValue n y, ?_⟩
  have ha := hx n _ (selectedWord_active_at E o hdep hactive n x)
  have hb := hy n _ (selectedWord_active_at E o hdep hactive n y)
  intro he
  exact hab (ha.symm.trans (he.trans hb))

theorem graph_period_useful (o : GraphOutputs E) (v : Plane)
    (hv : Period (graph o) (v, (0 : V E))) (x : Plane) (k : Input E) :
    o.c (x + v, k) = o.c (x, k) := by
  have hm : point o (x, k) + (v, (0 : V E)) ∈ graph o :=
    (hv (point o (x, k))).mpr (point_mem_graph o (x, k))
  have he := eq_point_of_mem_graph o hm
  have hq : q0 E (point o (x, k) + (v, (0 : V E))) = (x + v, k) := by
    rw [map_add, q0_point]
    refine Prod.ext rfl ?_
    funext i
    simp [q0]
  rw [hq] at he
  funext i
  have hi := congrArg (fun z : Ambient E => (z.2.2 i).2) he
  simpa only [Prod.fst_add, Prod.snd_add, Pi.add_apply, point_c,
    Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, add_zero] using hi.symm

theorem activeLabels_eq_of_graph_period (o : GraphOutputs E) (v : Plane)
    (hv : Period (graph o) (v, (0 : V E))) (i : Channel p) (x : Plane) :
    activeLabels E o i (x + v) = activeLabels E o i x := by
  classical
  have hc : usefulAt E o i (x + v) = usefulAt E o i x := by
    funext w
    exact congrFun (graph_period_useful E o v hv x (Function.update 0 i w)) i
  ext j
  simp only [mem_activeLabels, Active, hc]

theorem selectedWord_period_of_graph_period (o : GraphOutputs E) (M : ℤ)
    (hv : Period (graph o) ((0, M), (0 : V E))) :
    VerticalPeriod (selectedWord E o) M := by
  intro n m
  have hs := activeLabels_eq_of_graph_period E o (0, M) hv (.inl n) (0, m)
  have hs' : activeLabels E o (.inl n) (0, m + M) =
      activeLabels E o (.inl n) (0, m) := by simpa only [Prod.mk_add_mk, zero_add] using hs
  exact congrArg selectSymbol hs'

theorem exists_positive_vertical_graph_period (o : GraphOutputs E)
    (hper : FullyPeriodic (graph o)) :
    ∃ M : ℕ, 0 < M ∧ Period (graph o) ((0, (M : ℤ)), (0 : V E)) := by
  obtain ⟨Λ, hΛ, hperiods⟩ := hper
  refine ⟨Λ.index, Nat.pos_of_ne_zero hΛ.index_ne_zero, ?_⟩
  have h := hperiods _ (Λ.nsmul_index_mem (((0, 1) : Plane), (0 : V E)))
  simpa only [Prod.smul_mk, smul_zero, nsmul_eq_mul, mul_one] using h

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

attribute [local instance] Classical.propDecidable

section Field

variable {K : Type uK} [Field K]

theorem affine_coefficients_eq_of_two {a b c d x y : K} (hxy : x ≠ y)
    (hx : a * x + b = c * x + d) (hy : a * y + b = c * y + d) :
    a = c ∧ b = d := by
  have hm : (a - c) * (x - y) = 0 := by linear_combination hx - hy
  have ha : a = c := sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right
    (sub_ne_zero.mpr hxy))
  refine ⟨ha, ?_⟩
  linear_combination hx - x * ha

theorem affine_root_unique {a b x y : K} (hab : a ≠ 0 ∨ b ≠ 0)
    (hx : a * x + b = 0) (hy : a * y + b = 0) : x = y := by
  by_contra hxy
  have h := affine_coefficients_eq_of_two hxy
    (show a * x + b = 0 * x + 0 by simpa using hx)
    (show a * y + b = 0 * y + 0 by simpa using hy)
  exact hab.elim (fun ha => ha h.1) (fun hb => hb h.2)

theorem affine_roots_card_le_one {α : Type uα} [DecidableEq α]
    (s : Finset α) (x : α → K) (hx : Set.InjOn x s)
    (a b : K) (hab : a ≠ 0 ∨ b ≠ 0) :
    (s.filter (fun i => a * x i + b = 0)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  exact hx (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1
    (affine_root_unique hab (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2)

theorem two_common_nonzero_of_four (x : Fin 4 → K) (hx : Function.Injective x)
    (a b c d : K) (hab : a ≠ 0 ∨ b ≠ 0) (hcd : c ≠ 0 ∨ d ≠ 0) :
    ∃ i j : Fin 4, i ≠ j ∧ a * x i + b ≠ 0 ∧ c * x i + d ≠ 0 ∧
      a * x j + b ≠ 0 ∧ c * x j + d ≠ 0 := by
  classical
  let U := Finset.univ.filter (fun i => a * x i + b = 0)
  let V := Finset.univ.filter (fun i => c * x i + d = 0)
  have hu : U.card ≤ 1 := affine_roots_card_le_one _ _ (fun _ _ _ _ h => hx h) _ _ hab
  have hv : V.card ≤ 1 := affine_roots_card_le_one _ _ (fun _ _ _ _ h => hx h) _ _ hcd
  have huv : (U ∪ V).card ≤ 2 := (Finset.card_union_le U V).trans (by omega)
  have hsub : U ∪ V ⊆ (Finset.univ : Finset (Fin 4)) := Finset.subset_univ _
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  have hfour : (Finset.univ : Finset (Fin 4)).card = 4 := by simp
  have hgood : 1 < (Finset.univ \ (U ∪ V)).card := by omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hgood
  have hi' : a * x i + b ≠ 0 ∧ c * x i + d ≠ 0 := by
    simpa [U, V] using hi
  have hj' : a * x j + b ≠ 0 ∧ c * x j + d ≠ 0 := by
    simpa [U, V] using hj
  exact ⟨i, j, hij, hi'.1, hi'.2, hj'.1, hj'.2⟩

private theorem three_rows (h2 : (2 : K) ≠ 0)
    (u₀ u₁ u₂ v₀ v₁ v₂ : K)
    (hp : 2 * u₂ + v₂ - 2 * (u₁ + v₁) + v₀ = 0)
    (hp' : 3 * u₂ + v₂ - 2 * (2 * u₁ + v₁) + u₀ + v₀ = 0)
    (hm : v₂ - 2 * (u₁ + v₁) + 2 * u₀ + v₀ = 0) :
    u₁ = u₀ ∧ u₂ = u₀ ∧ v₂ - 2 * v₁ + v₀ = 0 := by
  have hu : 2 * (u₂ - u₀) = 0 := by linear_combination hp - hm
  have hu₂ : u₂ = u₀ := sub_eq_zero.mp ((mul_eq_zero.mp hu).resolve_left h2)
  have hu' : 2 * (u₁ - u₀) = 0 := by linear_combination hp - hp' + hu₂
  have hu₁ : u₁ = u₀ := sub_eq_zero.mp ((mul_eq_zero.mp hu').resolve_left h2)
  refine ⟨hu₁, hu₂, ?_⟩
  linear_combination hp - 2 * hu₂ + 2 * hu₁

theorem four_rows_affine (h2 : (2 : K) ≠ 0) (U V : Fin 4 → K)
    (hp₀ : 2 * U 2 + V 2 - 2 * (U 1 + V 1) + V 0 = 0)
    (hp₀' : 3 * U 2 + V 2 - 2 * (2 * U 1 + V 1) + U 0 + V 0 = 0)
    (hm₀ : V 2 - 2 * (U 1 + V 1) + 2 * U 0 + V 0 = 0)
    (hp₁ : 2 * U 3 + V 3 - 2 * (U 2 + V 2) + V 1 = 0)
    (hp₁' : 3 * U 3 + V 3 - 2 * (2 * U 2 + V 2) + U 1 + V 1 = 0)
    (hm₁ : V 3 - 2 * (U 2 + V 2) + 2 * U 1 + V 1 = 0) :
    ∀ i j : Fin 4, U j * (i.val : K) + V j =
      U 0 * (i.val : K) + (V 1 - V 0) * (j.val : K) + V 0 := by
  obtain ⟨hu₁, hu₂, hv₂⟩ := three_rows h2 _ _ _ _ _ _ hp₀ hp₀' hm₀
  obtain ⟨_, hu₃, hv₃⟩ := three_rows h2 _ _ _ _ _ _ hp₁ hp₁' hm₁
  have hu₃' : U 3 = U 0 := hu₃.trans hu₁
  have hv₂' : V 2 = 2 * V 1 - V 0 := by linear_combination hv₂
  have hv₃' : V 3 = 3 * V 1 - 2 * V 0 := by linear_combination hv₃ + 2 * hv₂
  intro i j
  fin_cases j <;> simp only [Fin.reduceFinMk,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, hu₁, hu₂, hu₃', hv₂', hv₃'] <;> ring

end Field

theorem four_residues_injective {p : ℕ} (hp : 4 ≤ p) (r : ℤ) :
    Function.Injective (fun i : Fin 4 => ((r + i.val : ℤ) : ZMod p)) := by
  intro i j hij
  have hv : (i.val : ZMod p) = (j.val : ZMod p) := by
    simpa only [Int.cast_add, Int.cast_natCast, add_right_inj] using hij
  apply Fin.ext
  have h := congrArg ZMod.val hv
  simpa only [ZMod.val_natCast_of_lt (i.isLt.trans_le hp),
    ZMod.val_natCast_of_lt (j.isLt.trans_le hp)] using h

theorem affine_int_roots_card_le {p : ℕ} (hp : p.Prime) (a b : ZMod p)
    (hab : a ≠ 0 ∨ b ≠ 0) :
    ((Finset.Ico (0 : ℤ) (p ^ 2 : ℕ)).filter
      (fun n : ℤ => a * (n : ZMod p) + b = 0)).card ≤ p := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hc : (Finset.Ico (0 : ℤ) (p : ℤ)).card = p := by simp
  refine le_trans ?_ (le_of_eq hc)
  apply Finset.card_le_card_of_injOn (fun n : ℤ => n / p)
  · intro n hn
    have hn' := Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1
    apply Finset.mem_Ico.mpr
    refine ⟨Int.ediv_nonneg hn'.1 hpz.le, ?_⟩
    apply Int.ediv_lt_of_lt_mul hpz
    simpa only [pow_two, Nat.cast_mul] using hn'.2
  · intro n hn m hm hq
    have hnm : (n : ZMod p) = (m : ZMod p) := affine_root_unique hab
      (Finset.mem_filter.mp hn).2 (Finset.mem_filter.mp hm).2
    have hr := (ZMod.intCast_eq_intCast_iff' n m p).mp hnm
    have hnq := Int.emod_add_mul_ediv n (p : ℤ)
    have hmq := Int.emod_add_mul_ediv m (p : ℤ)
    change n / (p : ℤ) = m / (p : ℤ) at hq
    rw [hr, hq] at hnq
    omega

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree

noncomputable section

attribute [local instance] Classical.propDecidable

def wordExceptionalCells (N : ℕ) (bad : ℤ → ℤ → ℤ → Prop) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-1 : ℤ) 1).biUnion fun d =>
    (Finset.Ico (-(N : ℤ)) (2 * (N : ℤ))).biUnion fun e =>
      ((Finset.Ico (0 : ℤ) N).filter (bad d e)).image fun n => (n, d * n + e)

theorem card_wordExceptionalCells_le (N p : ℕ) (bad : ℤ → ℤ → ℤ → Prop)
    (hbad : ∀ d e : ℤ, (d = -1 ∨ d = 0 ∨ d = 1) →
      ((Finset.Ico (0 : ℤ) N).filter (bad d e)).card ≤ p) :
    (wordExceptionalCells N bad).card ≤ 9 * N * p := by
  have hE : (Finset.Ico (-(N : ℤ)) (2 * (N : ℤ))).card = 3 * N := by
    rw [Int.card_Ico]
    omega
  have hD : (Finset.Icc (-1 : ℤ) 1).card = 3 := by
    norm_num [Int.card_Icc]
    rfl
  have hinner : ∀ d ∈ Finset.Icc (-1 : ℤ) 1,
      ((Finset.Ico (-(N : ℤ)) (2 * (N : ℤ))).biUnion fun e =>
        ((Finset.Ico (0 : ℤ) N).filter (bad d e)).image
          fun n => (n, d * n + e)).card ≤ 3 * N * p := by
    intro d hd
    have hd' : d = -1 ∨ d = 0 ∨ d = 1 := by
      have hd'' := Finset.mem_Icc.mp hd
      omega
    calc
      _ ≤ (Finset.Ico (-(N : ℤ)) (2 * (N : ℤ))).card * p := by
        apply Finset.card_biUnion_le_card_mul
        intro e _he
        exact Finset.card_image_le.trans (hbad d e hd')
      _ = 3 * N * p := by rw [hE]
  calc
    (wordExceptionalCells N bad).card ≤
        (Finset.Icc (-1 : ℤ) 1).card * (3 * N * p) :=
      Finset.card_biUnion_le_card_mul _ _ _ hinner
    _ = 9 * N * p := by rw [hD]; ring

theorem mem_wordExceptionalCells (N : ℕ) (bad : ℤ → ℤ → ℤ → Prop)
    (n m d : ℤ) (hn0 : 0 ≤ n) (hnN : n < N)
    (hm0 : 0 ≤ m) (hmN : m < N)
    (hd : d = -1 ∨ d = 0 ∨ d = 1) (hb : bad d (m - d * n) n) :
    (n, m) ∈ wordExceptionalCells N bad := by
  have hdmem : d ∈ Finset.Icc (-1 : ℤ) 1 := by
    rcases hd with rfl | rfl | rfl <;> simp
  have hemem : m - d * n ∈ Finset.Ico (-(N : ℤ)) (2 * (N : ℤ)) := by
    apply Finset.mem_Ico.mpr
    rcases hd with rfl | rfl | rfl <;>
      simp only [neg_one_mul, zero_mul, one_mul, sub_zero] <;> constructor <;> omega
  apply Finset.mem_biUnion.mpr
  refine ⟨d, hdmem, Finset.mem_biUnion.mpr ⟨m - d * n, hemem, ?_⟩⟩
  apply Finset.mem_image.mpr
  refine ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hn0, hnN⟩, hb⟩, ?_⟩
  exact Prod.ext rfl (by omega)

def wordBlockedOrigins (B : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  B.biUnion fun c =>
    ((Finset.Icc (0 : ℤ) 3).product (Finset.Icc (0 : ℤ) 3)).image
      fun o => (c.1 - o.1, c.2 - o.2)

theorem card_wordBlockedOrigins_le (B : Finset (ℤ × ℤ)) :
    (wordBlockedOrigins B).card ≤ B.card * 16 := by
  apply Finset.card_biUnion_le_card_mul
  intro c _hc
  calc
    _ ≤ ((Finset.Icc (0 : ℤ) 3).product (Finset.Icc (0 : ℤ) 3)).card :=
      Finset.card_image_le
    _ = 16 := by norm_num [Finset.card_product, Int.card_Icc]; rfl

theorem mem_wordBlockedOrigins (B : Finset (ℤ × ℤ)) (r q : ℤ)
    (i j : Fin 4) (hc : (r + i.val, q + j.val) ∈ B) :
    (r, q) ∈ wordBlockedOrigins B := by
  apply Finset.mem_biUnion.mpr
  refine ⟨(r + i.val, q + j.val), hc, Finset.mem_image.mpr ?_⟩
  refine ⟨((i.val : ℤ), (j.val : ℤ)), ?_, ?_⟩
  · apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_Icc.mpr <;> constructor <;> omega
  · apply Prod.ext <;> simp

private theorem four_square_count_inequality (p : ℕ) (hp : 200 < p) :
    144 * (p ^ 2) * p < (p ^ 2 - 3) ^ 2 := by
  have hp0 : 0 < p := by omega
  have hp201 : 201 ≤ p := by omega
  have hpred : p - 1 + 1 = p := by omega
  have hpredsq := congrArg (fun k : ℕ => k * k) hpred
  have hpredmul := congrArg (fun k : ℕ => p * k) hpred
  have hsq : 3 ≤ p ^ 2 := by nlinarith
  have hsub : p ^ 2 - 3 + 3 = p ^ 2 := Nat.sub_add_cancel hsq
  have hmul : 201 * p ≤ p * p := by nlinarith [Nat.mul_le_mul_right p hp201]
  have hgap : 144 * p < (p - 1) * (p - 1) := by nlinarith
  have hsmall : p * (p - 1) ≤ p ^ 2 - 3 := by nlinarith
  have hlarge := Nat.mul_lt_mul_of_pos_left hgap (pow_pos hp0 2)
  have hbound := Nat.mul_le_mul hsmall hsmall
  nlinarith

theorem exists_clean_four_square (p : ℕ) (hp : 200 < p)
    (bad : ℤ → ℤ → ℤ → Prop)
    (hbad : ∀ d e : ℤ, (d = -1 ∨ d = 0 ∨ d = 1) →
      ((Finset.Ico (0 : ℤ) (p ^ 2 : ℕ)).filter (bad d e)).card ≤ p) :
    ∃ r q : ℤ, 0 ≤ r ∧ r + 3 < (p ^ 2 : ℕ) ∧
      0 ≤ q ∧ q + 3 < (p ^ 2 : ℕ) ∧
      ∀ i j : Fin 4, ∀ d : ℤ, (d = -1 ∨ d = 0 ∨ d = 1) →
        ¬ bad d ((q + j.val) - d * (r + i.val)) (r + i.val) := by
  let N : ℕ := p ^ 2
  have hN : 3 ≤ N := by dsimp [N]; nlinarith
  let C : Finset (ℤ × ℤ) :=
    (Finset.Ico (0 : ℤ) (N - 3 : ℕ)).product
      (Finset.Ico (0 : ℤ) (N - 3 : ℕ))
  let B := wordBlockedOrigins (wordExceptionalCells N bad)
  have hC : C.card = (N - 3) ^ 2 := by
    simp [C, Finset.card_product, Int.card_Ico, pow_two]
  have hB : B.card ≤ 144 * N * p := by
    calc
      B.card ≤ (wordExceptionalCells N bad).card * 16 :=
        card_wordBlockedOrigins_le _
      _ ≤ (9 * N * p) * 16 :=
        Nat.mul_le_mul_right 16 (card_wordExceptionalCells_le N p bad hbad)
      _ = 144 * N * p := by ring
  have hlt : B.card < C.card := by
    rw [hC]
    exact hB.trans_lt (four_square_count_inequality p hp)
  obtain ⟨⟨r, q⟩, hc, hnblocked⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨hr, hq⟩ := Finset.mem_product.mp hc
  have hr' := Finset.mem_Ico.mp hr
  have hq' := Finset.mem_Ico.mp hq
  have hr0 : 0 ≤ r := hr'.1
  have hq0 : 0 ≤ q := hq'.1
  have hr3 : r + 3 < (N : ℤ) := by omega
  have hq3 : q + 3 < (N : ℤ) := by omega
  refine ⟨r, q, hr0, hr3, hq0, hq3, ?_⟩
  intro i j d hd hb
  apply hnblocked
  apply mem_wordBlockedOrigins _ r q i j
  apply mem_wordExceptionalCells N bad (r + i.val) (q + j.val) d
  · omega
  · omega
  · omega
  · omega
  · exact hd
  · exact hb

end

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree

def FourLineClosure (N : ℤ) (Good : ℤ → ℤ → Prop) : Prop :=
  ∀ d e : ℤ, (d = -1 ∨ d = 0 ∨ d = 1) →
    ∀ r : ℤ, 0 ≤ r → r + 3 < N →
      (∀ i : Fin 4, Good (r + i.val) (d * (r + i.val) + e)) →
      ∀ n : ℤ, 0 ≤ n → n < N → Good n (d * n + e)

def FourGoodRows (N : ℤ) (Good : ℤ → ℤ → Prop) (q : ℤ) : Prop :=
  ∀ m : ℤ, q ≤ m → m ≤ q + 3 →
    ∀ n : ℤ, 0 ≤ n → n < N → Good n m

theorem fourGoodRows_row_above (N : ℤ) (hN : 8 ≤ N)
    (Good : ℤ → ℤ → Prop) (hline : FourLineClosure N Good)
    (q : ℤ) (hrows : FourGoodRows N Good q) :
    ∀ n : ℤ, 0 ≤ n → n < N → Good n (q + 4) := by
  intro n hn0 hnN
  by_cases hr : n + 4 < N
  · have hseed : ∀ i : Fin 4,
        Good (n + 1 + i.val) ((-1) * (n + 1 + i.val) + (n + q + 4)) := by
      intro i
      have hi : 0 ≤ (i.val : ℤ) ∧ (i.val : ℤ) < 4 := by omega
      have hg := hrows (q + 3 - i.val) (by omega) (by omega)
        (n + 1 + i.val) (by omega) (by omega)
      convert hg using 1; simp only [neg_one_mul]; omega
    have h := hline (-1) (n + q + 4) (Or.inl rfl)
      (n + 1) (by omega) (by omega) hseed n hn0 hnN
    convert h using 1; simp only [neg_one_mul]; omega
  · have hl : 4 ≤ n := by omega
    have hseed : ∀ i : Fin 4,
        Good (n - 4 + i.val) (1 * (n - 4 + i.val) + (q + 4 - n)) := by
      intro i
      have hi : 0 ≤ (i.val : ℤ) ∧ (i.val : ℤ) < 4 := by omega
      have hg := hrows (q + i.val) (by omega) (by omega)
        (n - 4 + i.val) (by omega) (by omega)
      convert hg using 1; simp only [one_mul]; omega
    have h := hline 1 (q + 4 - n) (Or.inr (Or.inr rfl))
      (n - 4) (by omega) (by omega) hseed n hn0 hnN
    convert h using 1; simp only [one_mul]; omega

theorem fourGoodRows_row_below (N : ℤ) (hN : 8 ≤ N)
    (Good : ℤ → ℤ → Prop) (hline : FourLineClosure N Good)
    (q : ℤ) (hrows : FourGoodRows N Good q) :
    ∀ n : ℤ, 0 ≤ n → n < N → Good n (q - 1) := by
  intro n hn0 hnN
  by_cases hr : n + 4 < N
  · have hseed : ∀ i : Fin 4,
        Good (n + 1 + i.val) (1 * (n + 1 + i.val) + (q - 1 - n)) := by
      intro i
      have hi : 0 ≤ (i.val : ℤ) ∧ (i.val : ℤ) < 4 := by omega
      have hg := hrows (q + i.val) (by omega) (by omega)
        (n + 1 + i.val) (by omega) (by omega)
      convert hg using 1; simp only [one_mul]; omega
    have h := hline 1 (q - 1 - n) (Or.inr (Or.inr rfl))
      (n + 1) (by omega) (by omega) hseed n hn0 hnN
    convert h using 1; simp only [one_mul]; omega
  · have hl : 4 ≤ n := by omega
    have hseed : ∀ i : Fin 4,
        Good (n - 4 + i.val) ((-1) * (n - 4 + i.val) + (q - 1 + n)) := by
      intro i
      have hi : 0 ≤ (i.val : ℤ) ∧ (i.val : ℤ) < 4 := by omega
      have hg := hrows (q + 3 - i.val) (by omega) (by omega)
        (n - 4 + i.val) (by omega) (by omega)
      convert hg using 1; simp only [neg_one_mul]; omega
    have h := hline (-1) (q - 1 + n) (Or.inl rfl)
      (n - 4) (by omega) (by omega) hseed n hn0 hnN
    convert h using 1; simp only [neg_one_mul]; omega

theorem fourGoodRows_add_one (N : ℤ) (hN : 8 ≤ N)
    (Good : ℤ → ℤ → Prop) (hline : FourLineClosure N Good)
    (q : ℤ) (hrows : FourGoodRows N Good q) :
    FourGoodRows N Good (q + 1) := by
  intro m hm0 hm3 n hn0 hnN
  by_cases hm : m ≤ q + 3
  · exact hrows m (by omega) hm n hn0 hnN
  · have he : m = q + 4 := by omega
    rw [he]
    exact fourGoodRows_row_above N hN Good hline q hrows n hn0 hnN

theorem fourGoodRows_sub_one (N : ℤ) (hN : 8 ≤ N)
    (Good : ℤ → ℤ → Prop) (hline : FourLineClosure N Good)
    (q : ℤ) (hrows : FourGoodRows N Good q) :
    FourGoodRows N Good (q - 1) := by
  intro m hm0 hm3 n hn0 hnN
  by_cases hm : q ≤ m
  · exact hrows m hm (by omega) n hn0 hnN
  · have he : m = q - 1 := by omega
    rw [he]
    exact fourGoodRows_row_below N hN Good hline q hrows n hn0 hnN

theorem good_everywhere_of_four_square (N : ℤ) (hN : 8 ≤ N)
    (Good : ℤ → ℤ → Prop) (hline : FourLineClosure N Good)
    (r q : ℤ) (hr0 : 0 ≤ r) (hr3 : r + 3 < N)
    (hsquare : ∀ i j : Fin 4, Good (r + i.val) (q + j.val)) :
    ∀ n m : ℤ, 0 ≤ n → n < N → Good n m := by
  have hbase : FourGoodRows N Good q := by
    intro m hm0 hm3 n hn0 hnN
    let j : Fin 4 := ⟨(m - q).toNat, by omega⟩
    have hj : q + (j.val : ℤ) = m := by dsimp [j]; omega
    have hseed : ∀ i : Fin 4, Good (r + i.val) (0 * (r + i.val) + m) := by
      intro i
      simpa only [zero_mul, zero_add, hj] using hsquare i j
    have h := hline 0 m (Or.inr (Or.inl rfl)) r hr0 hr3 hseed n hn0 hnN
    simpa only [zero_mul, zero_add] using h
  have hall : ∀ t : ℤ, FourGoodRows N Good t := by
    intro t
    exact Int.inductionOn' t q hbase
      (fun k _ hk => fourGoodRows_add_one N hN Good hline k hk)
      (fun k _ hk => fourGoodRows_sub_one N hN Good hline k hk)
  intro n m hn0 hnN
  exact hall m m le_rfl (by omega) n hn0 hnN

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

theorem allowed_affine {p : ℕ} {w : Word p} (hw : Allowed p w) :
    ∃ a b : ZMod p, (a ≠ 0 ∨ b ≠ 0) ∧
      ∀ n : Column p, a * (n.val : ZMod p) + b ≠ 0 →
        (w n : ZMod p) = a * (n.val : ZMod p) + b := by
  obtain ⟨a, b, hab, hw⟩ := hw
  refine ⟨(a : ZMod p), (b : ZMod p), ?_, ?_⟩
  · simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] using hab
  · intro n hn
    have hnd : ¬ (p : ℤ) ∣ a * (n.val : ℤ) + b := by
      intro hd
      apply hn
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
        (a * (n.val : ℤ) + b) p).mpr hd
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using h
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using (hw n).1 hnd

private def intColumn {p : ℕ} (n : ℤ) (hn : 0 ≤ n ∧ n < (p ^ 2 : ℕ)) :
    Column p := ⟨n.toNat, by omega⟩

private theorem intColumn_val {p : ℕ} (n : ℤ)
    (hn : 0 ≤ n ∧ n < (p ^ 2 : ℕ)) :
    ((intColumn n hn).val : ℤ) = n := Int.toNat_of_nonneg hn.1

private theorem intColumn_cast {p : ℕ} (n : ℤ)
    (hn : 0 ≤ n ∧ n < (p ^ 2 : ℕ)) :
    ((intColumn n hn).val : ZMod p) = (n : ZMod p) := by
  simpa only [Int.cast_natCast] using
    congrArg (fun x : ℤ => (x : ZMod p)) (intColumn_val n hn)

private def rawArray {p : ℕ} (W : WordArray p) (n m : ℤ) : ZMod p :=
  if hn : 0 ≤ n ∧ n < (p ^ 2 : ℕ) then (W (intColumn n hn) m : ZMod p) else 1

private theorem rawArray_column {p : ℕ} (W : WordArray p) (n : Column p) (m : ℤ) :
    rawArray W n.val m = (W n m : ZMod p) := by
  have hn : (0 : ℤ) ≤ n.val ∧ (n.val : ℤ) < (p ^ 2 : ℕ) := by
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast n.isLt⟩
  have hc : intColumn (n.val : ℤ) hn = n := by
    apply Fin.ext
    simp [intColumn]
  rw [rawArray, dite_eq_left hn, hc]

private theorem rawArray_ne_zero {p : ℕ} [Fact p.Prime] (W : WordArray p)
    (n m : ℤ) (hn : 0 ≤ n ∧ n < (p ^ 2 : ℕ)) : rawArray W n m ≠ 0 := by
  rw [rawArray, dite_eq_left hn]
  exact Units.ne_zero _

private structure LineAffine {p : ℕ} (W : WordArray p) (d e : ℤ) where
  a : ZMod p
  b : ZMod p
  nonzero : a ≠ 0 ∨ b ≠ 0
  agrees : ∀ n : Column p, a * (n.val : ZMod p) + b ≠ 0 →
    (W n (d * (n.val : ℤ) + e) : ZMod p) = a * (n.val : ZMod p) + b

private def chooseLine {p : ℕ} {W : WordArray p} (hW : LineRule p W)
    (d e : ℤ) : LineAffine W d e := by
  let h := allowed_affine (hW d e)
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.1,
    h.choose_spec.choose_spec.2⟩

private theorem LineAffine.raw_agrees {p : ℕ} {W : WordArray p} {d e : ℤ}
    (L : LineAffine W d e) (n : ℤ) (hn : 0 ≤ n ∧ n < (p ^ 2 : ℕ))
    (hz : L.a * (n : ZMod p) + L.b ≠ 0) :
    rawArray W n (d * n + e) = L.a * (n : ZMod p) + L.b := by
  have h := L.agrees (intColumn n hn) (by simpa only [intColumn_cast] using hz)
  rw [intColumn_val, intColumn_cast] at h
  simpa only [rawArray, dite_eq_left hn] using h

private theorem clean_second_difference {p : ℕ} {W : WordArray p}
    (hW : LineRule p W) (r q : ℤ)
    (hc : ∀ i j : Fin 4, ∀ d : ℤ, (d = -1 ∨ d = 0 ∨ d = 1) →
      rawArray W (r + i.val) (q + j.val) =
        (chooseLine hW d ((q + j.val) - d * (r + i.val))).a *
          ((r + i.val : ℤ) : ZMod p) +
        (chooseLine hW d ((q + j.val) - d * (r + i.val))).b)
    (x₀ y₀ x₁ y₁ x₂ y₂ : Fin 4) (d : ℤ)
    (hd : d = -1 ∨ d = 0 ∨ d = 1)
    (h₁ : (y₁.val : ℤ) - y₀.val = d * ((x₁.val : ℤ) - x₀.val))
    (h₂ : (y₂.val : ℤ) - y₀.val = d * ((x₂.val : ℤ) - x₀.val))
    (hx : (x₂.val : ℤ) - 2 * x₁.val + x₀.val = 0) :
    rawArray W (r + x₂.val) (q + y₂.val) -
      2 * rawArray W (r + x₁.val) (q + y₁.val) +
      rawArray W (r + x₀.val) (q + y₀.val) = 0 := by
  let e := (q + y₀.val) - d * (r + x₀.val)
  have he₁ : (q + y₁.val) - d * (r + x₁.val) = e := by
    dsimp [e]
    linear_combination h₁
  have he₂ : (q + y₂.val) - d * (r + x₂.val) = e := by
    dsimp [e]
    linear_combination h₂
  have h₀' := hc x₀ y₀ d hd
  have h₁' := hc x₁ y₁ d hd
  have h₂' := hc x₂ y₂ d hd
  change rawArray W (r + x₀.val) (q + y₀.val) =
    (chooseLine hW d e).a * ((r + x₀.val : ℤ) : ZMod p) +
      (chooseLine hW d e).b at h₀'
  rw [he₁] at h₁'
  rw [he₂] at h₂'
  have hx' : (x₂.val : ZMod p) - 2 * x₁.val + x₀.val = 0 := by
    simpa only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
      Int.cast_natCast, Int.cast_zero] using
      congrArg (fun z : ℤ => (z : ZMod p)) hx
  rw [h₀', h₁', h₂']
  push_cast
  linear_combination (chooseLine hW d e).a * hx'

private theorem affine_four_line_closure {p : ℕ} (hp : p.Prime) (hlarge : 200 < p)
    {W : WordArray p} (hW : LineRule p W) (A B C : ZMod p) :
    FourLineClosure (p ^ 2 : ℕ)
      (fun n m => A * (n : ZMod p) + B * (m : ZMod p) + C = 0 ∨
        rawArray W n m = A * (n : ZMod p) + B * (m : ZMod p) + C) := by
  let : Fact p.Prime := ⟨hp⟩
  intro d e hd r hr₀ hr₃ hgood n hn₀ hn
  let a : ZMod p := A + B * (d : ZMod p)
  let b : ZMod p := B * (e : ZMod p) + C
  let L := chooseLine hW d e
  have hrest (k : ℤ) : A * (k : ZMod p) + B * ((d * k + e : ℤ) : ZMod p) + C =
      a * (k : ZMod p) + b := by
    dsimp [a, b]
    push_cast
    ring
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · left
      rw [hrest, ha, hb]
      simp
    · have hab : a ≠ 0 ∨ b ≠ 0 := Or.inr hb
      obtain ⟨i, j, hij, hiA, hiL, hjA, hjL⟩ := two_common_nonzero_of_four
        (fun k : Fin 4 => ((r + k.val : ℤ) : ZMod p))
        (four_residues_injective (by omega) r) a b L.a L.b hab L.nonzero
      have heq (k : Fin 4) (hkA : a * ((r + k.val : ℤ) : ZMod p) + b ≠ 0)
          (hkL : L.a * ((r + k.val : ℤ) : ZMod p) + L.b ≠ 0) :
          a * ((r + k.val : ℤ) : ZMod p) + b =
            L.a * ((r + k.val : ℤ) : ZMod p) + L.b := by
        have hk := hgood k
        dsimp only at hk
        rw [hrest] at hk
        have hk' := hk.resolve_left hkA
        have hbound : 0 ≤ r + k.val ∧ r + k.val < (p ^ 2 : ℕ) := by
          have := k.isLt
          omega
        exact hk'.symm.trans (L.raw_agrees _ hbound hkL)
      have hcoef := affine_coefficients_eq_of_two
        (fun h => hij ((four_residues_injective (by omega) r) h))
        (heq i hiA hiL) (heq j hjA hjL)
      by_cases hz : a * (n : ZMod p) + b = 0
      · left
        rw [hrest]
        exact hz
      · right
        rw [hrest]
        rw [hcoef.1, hcoef.2] at hz ⊢
        exact L.raw_agrees n ⟨hn₀, hn⟩ hz
  · have hab : a ≠ 0 ∨ b ≠ 0 := Or.inl ha
    obtain ⟨i, j, hij, hiA, hiL, hjA, hjL⟩ := two_common_nonzero_of_four
      (fun k : Fin 4 => ((r + k.val : ℤ) : ZMod p))
      (four_residues_injective (by omega) r) a b L.a L.b hab L.nonzero
    have heq (k : Fin 4) (hkA : a * ((r + k.val : ℤ) : ZMod p) + b ≠ 0)
        (hkL : L.a * ((r + k.val : ℤ) : ZMod p) + L.b ≠ 0) :
        a * ((r + k.val : ℤ) : ZMod p) + b =
          L.a * ((r + k.val : ℤ) : ZMod p) + L.b := by
      have hk := hgood k
      dsimp only at hk
      rw [hrest] at hk
      have hk' := hk.resolve_left hkA
      have hbound : 0 ≤ r + k.val ∧ r + k.val < (p ^ 2 : ℕ) := by
        have := k.isLt
        omega
      exact hk'.symm.trans (L.raw_agrees _ hbound hkL)
    have hcoef := affine_coefficients_eq_of_two
      (fun h => hij ((four_residues_injective (by omega) r) h))
      (heq i hiA hiL) (heq j hjA hjL)
    by_cases hz : a * (n : ZMod p) + b = 0
    · left
      rw [hrest]
      exact hz
    · right
      rw [hrest]
      rw [hcoef.1, hcoef.2] at hz ⊢
      exact L.raw_agrees n ⟨hn₀, hn⟩ hz

theorem global_affine_approximation {p : ℕ} (hp : p.Prime) (hlarge : 200 < p)
    {W : WordArray p} (hW : LineRule p W) :
    ∃ A B C : ZMod p, AffineApproximation W A B C := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let bad : ℤ → ℤ → ℤ → Prop := fun d e n =>
    (chooseLine hW d e).a * (n : ZMod p) + (chooseLine hW d e).b = 0
  have hbad : ∀ d e, d = -1 ∨ d = 0 ∨ d = 1 →
      ((Finset.Ico (0 : ℤ) (p ^ 2 : ℕ)).filter (bad d e)).card ≤ p := by
    intro d e _
    exact affine_int_roots_card_le hp _ _ (chooseLine hW d e).nonzero
  obtain ⟨r, q, hr₀, hr₃, _, _, hclean⟩ :=
    exists_clean_four_square p hlarge bad
      (by
        intro d e hd
        have hfilter := @Finset.filter_congr_decidable ℤ
          (Finset.Ico (0 : ℤ) (p ^ 2 : ℕ)) (bad d e)
          (fun n => Classical.propDecidable (bad d e n))
          (fun n => ZMod.decidableEq p
            ((chooseLine hW d e).a * (n : ZMod p) + (chooseLine hW d e).b) 0)
        exact (congrArg (fun s : Finset ℤ => s.card ≤ p) hfilter).mpr (hbad d e hd))
  have hcell : ∀ i j : Fin 4, ∀ d : ℤ, (d = -1 ∨ d = 0 ∨ d = 1) →
      rawArray W (r + i.val) (q + j.val) =
        (chooseLine hW d ((q + j.val) - d * (r + i.val))).a *
          ((r + i.val : ℤ) : ZMod p) +
        (chooseLine hW d ((q + j.val) - d * (r + i.val))).b := by
    intro i j d hd
    have hn : 0 ≤ r + i.val ∧ r + i.val < (p ^ 2 : ℕ) := by
      have := i.isLt
      omega
    have h := (chooseLine hW d ((q + j.val) - d * (r + i.val))).raw_agrees
      (r + i.val) hn (hclean i j d hd)
    have he : d * (r + i.val) + ((q + j.val) - d * (r + i.val)) = q + j.val := by ring
    simpa only [he] using h
  let U : Fin 4 → ZMod p := fun j => (chooseLine hW 0 (q + j.val)).a
  let V : Fin 4 → ZMod p := fun j => U j * (r : ZMod p) +
    (chooseLine hW 0 (q + j.val)).b
  have hrow (i j : Fin 4) : rawArray W (r + i.val) (q + j.val) =
      U j * (i.val : ZMod p) + V j := by
    have h := hcell i j 0 (Or.inr (Or.inl rfl))
    have he : (q + j.val) - (0 : ℤ) * (r + i.val) = q + j.val := by ring
    rw [he] at h
    rw [h]
    dsimp [V, U]
    push_cast
    ring
  have hv0 : (0 : Fin 4).val = 0 := rfl
  have hv1 : (1 : Fin 4).val = 1 := rfl
  have hv2 : (2 : Fin 4).val = 2 := rfl
  have hv3 : (3 : Fin 4).val = 3 := rfl
  have hp₀ := clean_second_difference hW r q hcell 0 0 1 1 2 2 1
    (Or.inr (Or.inr rfl))
    (by norm_num [hv0, hv1, hv2, hv3])
    (by norm_num [hv0, hv1, hv2, hv3])
    (by norm_num [hv0, hv1, hv2, hv3])
  have hp₀' := clean_second_difference hW r q hcell 1 0 2 1 3 2 1
    (Or.inr (Or.inr rfl))
    (by norm_num [hv0, hv1, hv2, hv3])
    (by norm_num [hv0, hv1, hv2, hv3])
    (by norm_num [hv0, hv1, hv2, hv3])
  have hm₀ := clean_second_difference hW r q hcell 2 0 1 1 0 2 (-1)
    (Or.inl rfl)
    (by norm_num [hv0, hv1, hv2, hv3])
    (by norm_num [hv0, hv1, hv2, hv3])
    (by norm_num [hv0, hv1, hv2, hv3])
  have hp₁ := clean_second_difference hW r q hcell 0 1 1 2 2 3 1
    (Or.inr (Or.inr rfl))
    (by norm_num [hv0, hv1, hv2, hv3])
    (by norm_num [hv0, hv1, hv2, hv3])
    (by norm_num [hv0, hv1, hv2, hv3])
  have hp₁' := clean_second_difference hW r q hcell 1 1 2 2 3 3 1
    (Or.inr (Or.inr rfl))
    (by norm_num [hv0, hv1, hv2, hv3])
    (by norm_num [hv0, hv1, hv2, hv3])
    (by norm_num [hv0, hv1, hv2, hv3])
  have hm₁ := clean_second_difference hW r q hcell 2 1 1 2 0 3 (-1)
    (Or.inl rfl)
    (by norm_num [hv0, hv1, hv2, hv3])
    (by norm_num [hv0, hv1, hv2, hv3])
    (by norm_num [hv0, hv1, hv2, hv3])
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    have hlt : 2 < p := by omega
    have hv₂ : (2 : ZMod p).val = 2 := ZMod.val_natCast_of_lt hlt
    rw [hv₂, ZMod.val_zero] at hv
    omega
  have hpatch := four_rows_affine htwo U V
    (by
      have h := hp₀
      simp only [hrow] at h
      simp only [hv0, hv1, hv2, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at h
      linear_combination h)
    (by
      have h := hp₀'
      simp only [hrow] at h
      simp only [hv1, hv2, hv3, Nat.cast_one, Nat.cast_ofNat] at h
      linear_combination h)
    (by
      have h := hm₀
      simp only [hrow] at h
      simp only [hv0, hv1, hv2, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at h
      linear_combination h)
    (by
      have h := hp₁
      simp only [hrow] at h
      simp only [hv0, hv1, hv2, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at h
      linear_combination h)
    (by
      have h := hp₁'
      simp only [hrow] at h
      simp only [hv1, hv2, hv3, Nat.cast_one, Nat.cast_ofNat] at h
      linear_combination h)
    (by
      have h := hm₁
      simp only [hrow] at h
      simp only [hv0, hv1, hv2, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at h
      linear_combination h)
  let A := U 0
  let B := V 1 - V 0
  let C := V 0 - A * (r : ZMod p) - B * (q : ZMod p)
  have hsquare (i j : Fin 4) : rawArray W (r + i.val) (q + j.val) =
      A * ((r + i.val : ℤ) : ZMod p) +
        B * ((q + j.val : ℤ) : ZMod p) + C := by
    rw [hrow, hpatch]
    dsimp [A, B, C]
    push_cast
    ring
  have hnonzero : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0 := by
    by_cases hA : A = 0
    · by_cases hB : B = 0
      · refine Or.inr (Or.inr ?_)
        intro hC
        have hz := hsquare 0 0
        simp only [Fin.val_zero, Nat.cast_zero, add_zero, hA, hB, hC,
          zero_mul] at hz
        exact rawArray_ne_zero W r q ⟨hr₀, by omega⟩ hz
      · exact Or.inr (Or.inl hB)
    · exact Or.inl hA
  have hN : (8 : ℤ) ≤ (p ^ 2 : ℕ) := by
    have hp' : 201 ≤ p := by omega
    have hsq : 201 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp' 2
    exact_mod_cast (show 8 ≤ p ^ 2 by omega)
  have hglobal := good_everywhere_of_four_square (p ^ 2 : ℕ) hN
    (fun n m => A * (n : ZMod p) + B * (m : ZMod p) + C = 0 ∨
      rawArray W n m = A * (n : ZMod p) + B * (m : ZMod p) + C)
    (affine_four_line_closure hp hlarge hW A B C) r q hr₀ hr₃
    (fun i j => Or.inr (hsquare i j))
  refine ⟨A, B, C, hnonzero, ?_⟩
  intro n m hn
  have h := hglobal (n.val : ℤ) m (Int.natCast_nonneg _)
    (by exact_mod_cast n.isLt)
  rw [rawArray_column] at h
  simpa only [affineValue, Int.cast_natCast] using
    (h.resolve_left (by simpa only [affineValue, Int.cast_natCast] using hn))

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

private theorem word_one_ne_two {p : ℕ} (hlarge : 200 < p) :
    (1 : ZMod p) ≠ 2 := by
  intro h
  have hv := congrArg (fun x : ZMod p => x.val) h
  rw [ZMod.val_one_eq_one_mod, ZMod.val_two_eq_two_mod,
    Nat.mod_eq_of_lt (by omega : 1 < p),
    Nat.mod_eq_of_lt (by omega : 2 < p)] at hv
  omega

private theorem word_two_ne_zero {p : ℕ} (hlarge : 200 < p) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < p) hd

private def smallColumn {p : ℕ} (hlarge : 200 < p) (n : Fin p) : Column p :=
  ⟨n.val, by have := n.isLt; nlinarith⟩

private def fourColumn {p : ℕ} (hlarge : 200 < p) (i : Fin 4) : Column p :=
  smallColumn hlarge ⟨i.val, by have := i.isLt; omega⟩

private theorem small_affine_nonzero {p : ℕ} (hp : p.Prime)
    (A C : ZMod p) (hAC : A ≠ 0 ∨ C ≠ 0) :
    ∃ n : Fin p, A * (n.val : ZMod p) + C ≠ 0 := by
  by_cases hC : C = 0
  · have hA : A ≠ 0 := hAC.resolve_right (fun h => h hC)
    refine ⟨⟨1, hp.one_lt⟩, ?_⟩
    simpa only [Nat.cast_one, mul_one, hC, add_zero] using hA
  · refine ⟨⟨0, hp.pos⟩, ?_⟩
    simpa only [Nat.cast_zero, mul_zero, zero_add] using hC

private theorem exists_vertical_value {p : ℕ} (hp : p.Prime)
    (A B C : ZMod p) (hB : B ≠ 0) (n : Column p) (t : ZMod p) :
    ∃ m : ℤ, affineValue A B C n m = t := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective
    (B⁻¹ * (t - A * (n.val : ZMod p) - C))
  refine ⟨m, ?_⟩
  have hBm : B * (m : ZMod p) = t - A * (n.val : ZMod p) - C := by
    rw [hm, ← mul_assoc, mul_inv_cancel₀ hB, one_mul]
  unfold affineValue
  rw [hBm]
  ring

theorem nonconstantColumns_iff_vertical_coefficient {p : ℕ} (hp : p.Prime)
    (hlarge : 200 < p) {W : WordArray p} {A B C : ZMod p}
    (hH : AffineApproximation W A B C) : NonconstantColumns W ↔ B ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  constructor
  · intro hcolumns hB
    have hAC : A ≠ 0 ∨ C ≠ 0 := by
      rcases hH.1 with hA | hB' | hC
      · exact Or.inl hA
      · exact (hB' hB).elim
      · exact Or.inr hC
    obtain ⟨n₀, hn₀⟩ := small_affine_nonzero hp A C hAC
    let n := smallColumn hlarge n₀
    obtain ⟨m, m', hmm'⟩ := hcolumns n
    apply hmm'
    apply Units.ext
    have hval (z : ℤ) : (W n z : ZMod p) = A * (n₀.val : ZMod p) + C := by
      have hn : affineValue A B C n z ≠ 0 := by
        simpa only [affineValue, n, smallColumn, hB, zero_mul, add_zero] using hn₀
      simpa only [affineValue, n, smallColumn, hB, zero_mul, add_zero] using hH.2 n z hn
    exact (hval m).trans (hval m').symm
  · intro hB n
    obtain ⟨m, hm⟩ := exists_vertical_value hp A B C hB n 1
    obtain ⟨m', hm'⟩ := exists_vertical_value hp A B C hB n 2
    refine ⟨m, m', ?_⟩
    intro heq
    have hwm : (W n m : ZMod p) = 1 :=
      (hH.2 n m (by rw [hm]; exact one_ne_zero)).trans hm
    have hwm' : (W n m' : ZMod p) = 2 :=
      (hH.2 n m' (by rw [hm']; exact word_two_ne_zero hlarge)).trans hm'
    exact word_one_ne_two hlarge
      (hwm.symm.trans ((congrArg (fun u : Symbol p => (u : ZMod p)) heq).trans hwm'))

theorem prime_dvd_vertical_period {p : ℕ} (hp : p.Prime)
    (hlarge : 200 < p) {W : WordArray p} {A B C : ZMod p}
    (hH : AffineApproximation W A B C) (hB : B ≠ 0) {M : ℤ}
    (hperiod : VerticalPeriod W M) : (p : ℤ) ∣ M := by
  let : Fact p.Prime := ⟨hp⟩
  let n : Column p := ⟨0, pow_pos hp.pos 2⟩
  let x : Fin 4 → ZMod p := fun i => (i.val : ZMod p)
  have hx : Function.Injective x := by
    simpa only [zero_add, Int.cast_natCast] using
      (four_residues_injective (p := p) (by omega : 4 ≤ p) 0)
  obtain ⟨i, j, hij, hi, hiM, hj, hjM⟩ := two_common_nonzero_of_four x hx
    B (A * (n.val : ZMod p) + C)
    B (B * (M : ZMod p) + A * (n.val : ZMod p) + C)
    (Or.inl hB) (Or.inl hB)
  let m : ℤ := i.val
  have hm : affineValue A B C n m ≠ 0 := by
    have heq : affineValue A B C n m = B * x i + (A * (n.val : ZMod p) + C) := by
      simp only [affineValue, m, x, Int.cast_natCast]
      ring
    rw [heq]
    exact hi
  have hmM : affineValue A B C n (m + M) ≠ 0 := by
    have heq : affineValue A B C n (m + M) =
        B * x i + (B * (M : ZMod p) + A * (n.val : ZMod p) + C) := by
      simp only [affineValue, m, x, Int.cast_add, Int.cast_natCast]
      ring
    rw [heq]
    exact hiM
  have heq : affineValue A B C n (m + M) = affineValue A B C n m :=
    (hH.2 n (m + M) hmM).symm.trans
      ((congrArg (fun u : Symbol p => (u : ZMod p)) (hperiod n m)).trans (hH.2 n m hm))
  have hBM : B * (M : ZMod p) = 0 := by
    simp only [affineValue, Int.cast_add] at heq
    linear_combination heq
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd M p).mp
    ((mul_eq_zero.mp hBM).resolve_left hB)

def straighten {p : ℕ} (W : WordArray p) (u v : ℤ) : WordArray p :=
  fun n m => W n (m + u * (n.val : ℤ) + v)

theorem straighten_lineRule {p : ℕ} {W : WordArray p}
    (hW : LineRule p W) (u v : ℤ) : LineRule p (straighten W u v) := by
  intro d e
  have heq : (fun n => straighten W u v n (d * (n.val : ℤ) + e)) =
      (fun n => W n ((d + u) * (n.val : ℤ) + (e + v))) := by
    funext n
    unfold straighten
    congr 1
    ring
  rw [heq]
  exact hW (d + u) (e + v)

theorem straighten_nonconstantColumns_iff {p : ℕ} (W : WordArray p) (u v : ℤ) :
    NonconstantColumns (straighten W u v) ↔ NonconstantColumns W := by
  constructor
  · intro h n
    obtain ⟨m, m', hmm'⟩ := h n
    exact ⟨m + u * (n.val : ℤ) + v, m' + u * (n.val : ℤ) + v, hmm'⟩
  · intro h n
    obtain ⟨m, m', hmm'⟩ := h n
    refine ⟨m - u * (n.val : ℤ) - v, m' - u * (n.val : ℤ) - v, ?_⟩
    have hm : m - u * (n.val : ℤ) - v + u * (n.val : ℤ) + v = m := by ring
    have hm' : m' - u * (n.val : ℤ) - v + u * (n.val : ℤ) + v = m' := by ring
    simpa only [straighten, hm, hm'] using hmm'

theorem straighten_verticalPeriod_iff {p : ℕ} (W : WordArray p)
    (u v M : ℤ) : VerticalPeriod (straighten W u v) M ↔ VerticalPeriod W M := by
  constructor
  · intro h n m
    have hh := h n (m - u * (n.val : ℤ) - v)
    change W n ((m - u * (n.val : ℤ) - v + M) + u * (n.val : ℤ) + v) =
      W n ((m - u * (n.val : ℤ) - v) + u * (n.val : ℤ) + v) at hh
    convert hh using 1 <;> congr 1 <;> ring
  · intro h n m
    change W n ((m + M) + u * (n.val : ℤ) + v) = W n (m + u * (n.val : ℤ) + v)
    convert h n (m + u * (n.val : ℤ) + v) using 1 ; congr 1 ; ring

theorem exists_straighten_affine {p : ℕ} (hp : p.Prime)
    {W : WordArray p} {A B C : ZMod p} (hH : AffineApproximation W A B C)
    (hB : B ≠ 0) : ∃ u v : ℤ, AffineApproximation (straighten W u v) 0 B 0 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu⟩ := ZMod.intCast_surjective (-(B⁻¹ * A))
  obtain ⟨v, hv⟩ := ZMod.intCast_surjective (-(B⁻¹ * C))
  have hbu : A + B * (u : ZMod p) = 0 := by
    rw [hu, mul_neg, ← mul_assoc, mul_inv_cancel₀ hB, one_mul, add_neg_cancel]
  have hbv : C + B * (v : ZMod p) = 0 := by
    rw [hv, mul_neg, ← mul_assoc, mul_inv_cancel₀ hB, one_mul, add_neg_cancel]
  refine ⟨u, v, Or.inr (Or.inl hB), ?_⟩
  intro n m hm
  have hnorm : affineValue A B C n (m + u * (n.val : ℤ) + v) =
      affineValue 0 B 0 n m := by
    simp only [affineValue, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    linear_combination (n.val : ZMod p) * hbu + hbv
  exact (hH.2 n _ (by rw [hnorm]; exact hm)).trans hnorm

def rescale {p : ℕ} (W : WordArray p) : WordArray p :=
  fun n m => W n ((p : ℤ) * m)

theorem rescale_lineRule {p : ℕ} {W : WordArray p} (hW : LineRule p W) :
    LineRule p (rescale W) := by
  intro d e
  have heq : (fun n => rescale W n (d * (n.val : ℤ) + e)) =
      (fun n => W n (((p : ℤ) * d) * (n.val : ℤ) + (p : ℤ) * e)) := by
    funext n
    unfold rescale
    congr 1
    ring
  rw [heq]
  exact hW ((p : ℤ) * d) ((p : ℤ) * e)

private theorem exists_nonzero_affine_ne {p : ℕ} (hp : p.Prime)
    (hlarge : 200 < p) (a z c : ZMod p) (ha : a ≠ 0) :
    ∃ k : Fin p, z + a * (k.val : ZMod p) ≠ 0 ∧
      z + a * (k.val : ZMod p) ≠ c := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  have ht : ∃ t : ZMod p, t ≠ 0 ∧ t ≠ c := by
    by_cases hc : c = 1
    · exact ⟨2, word_two_ne_zero hlarge, by
        rw [hc]
        exact Ne.symm (word_one_ne_two hlarge)⟩
    · exact ⟨1, one_ne_zero, Ne.symm hc⟩
  obtain ⟨t, ht0, htc⟩ := ht
  let x : ZMod p := a⁻¹ * (t - z)
  let k : Fin p := ⟨x.val, ZMod.val_lt x⟩
  have hk : (k.val : ZMod p) = x := ZMod.natCast_zmod_val x
  have heq : z + a * (k.val : ZMod p) = t := by
    rw [hk]
    dsimp only [x]
    rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
    ring
  exact ⟨k, by rw [heq]; exact ht0, by rw [heq]; exact htc⟩

private def fiberColumn {p : ℕ} (n₀ k : Fin p) : Column p :=
  ⟨n₀.val + p * k.val, by
    calc
      n₀.val + p * k.val < p + p * k.val := Nat.add_lt_add_right n₀.isLt _
      _ = p * (k.val + 1) := by ring
      _ ≤ p * p := Nat.mul_le_mul_left p (Nat.succ_le_of_lt k.isLt)
      _ = p ^ 2 := by ring⟩

theorem rescale_vertical_coefficient_ne_zero {p : ℕ} (hp : p.Prime)
    (hlarge : 200 < p) {W : WordArray p} (hW : LineRule p W)
    {B : ZMod p} (hB : B ≠ 0) (hH : AffineApproximation W 0 B 0)
    {A₁ B₁ C₁ : ZMod p} (hH₁ : AffineApproximation (rescale W) A₁ B₁ C₁) :
    B₁ ≠ 0 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  intro hB₁
  have hAC : A₁ ≠ 0 ∨ C₁ ≠ 0 := by
    rcases hH₁.1 with hA | hB' | hC
    · exact Or.inl hA
    · exact (hB' hB₁).elim
    · exact Or.inr hC
  obtain ⟨n₀, hc⟩ := small_affine_nonzero hp A₁ C₁ hAC
  let c : ZMod p := A₁ * (n₀.val : ZMod p) + C₁
  obtain ⟨a, b, hab, hw⟩ := hW 1 (-(n₀.val : ℤ))
  have hab' : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0 := by
    rcases hab with ha | hb
    · exact Or.inl (fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h))
    · exact Or.inr (fun h => hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp h))
  let x : Fin 4 → ZMod p := fun i => (i.val : ZMod p)
  have hx : Function.Injective x := by
    simpa only [zero_add, Int.cast_natCast] using
      (four_residues_injective (p := p) (by omega : 4 ≤ p) 0)
  obtain ⟨i, j, hij, hai, hbi, haj, hbj⟩ := two_common_nonzero_of_four x hx
    (a : ZMod p) (b : ZMod p) B (-B * (n₀.val : ZMod p)) hab' (Or.inl hB)
  have hmatch (s : Fin 4)
      (has : (a : ZMod p) * x s + (b : ZMod p) ≠ 0)
      (hbs : B * x s + -B * (n₀.val : ZMod p) ≠ 0) :
      (a : ZMod p) * x s + (b : ZMod p) =
        B * x s + -B * (n₀.val : ZMod p) := by
    let n := fourColumn hlarge s
    have hnot : ¬ (p : ℤ) ∣ a * (n.val : ℤ) + b := by
      intro hd
      apply has
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, n, fourColumn, smallColumn, x] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd (a * (n.val : ℤ) + b) p).mpr hd
    have harg : affineValue 0 B 0 n (1 * (n.val : ℤ) + -(n₀.val : ℤ)) =
        B * x s + -B * (n₀.val : ZMod p) := by
      simp only [affineValue, zero_mul, zero_add, add_zero, one_mul,
        Int.cast_add, Int.cast_neg, Int.cast_natCast]
      change B * ((s.val : ZMod p) + -(n₀.val : ZMod p)) =
        B * (s.val : ZMod p) + -B * (n₀.val : ZMod p)
      ring
    have hw' := (hw n).1 hnot
    dsimp only at hw'
    have hH' := hH.2 n (1 * (n.val : ℤ) + -(n₀.val : ℤ))
      (by rw [harg]; exact hbs)
    calc
      (a : ZMod p) * x s + (b : ZMod p) =
          (W n (1 * (n.val : ℤ) + -(n₀.val : ℤ)) : ZMod p) := by
        simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, n, fourColumn, smallColumn, x] using hw'.symm
      _ = B * x s + -B * (n₀.val : ZMod p) := hH'.trans harg
  obtain ⟨haB, hbB⟩ := affine_coefficients_eq_of_two (fun h => hij (hx h))
    (hmatch i hai hbi) (hmatch j haj hbj)
  have ha0 : (a : ZMod p) ≠ 0 := by rw [haB]; exact hB
  have hdiv : (p : ℤ) ∣ a * (n₀.val : ℤ) + b := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
    rw [haB, hbB]
    ring
  obtain ⟨z, hz⟩ := hdiv
  obtain ⟨k, hk0, hkc⟩ := exists_nonzero_affine_ne hp hlarge (a : ZMod p) (z : ZMod p) c ha0
  let n := fiberColumn n₀ k
  have hnv : (n.val : ℤ) = (n₀.val : ℤ) + (p : ℤ) * (k.val : ℤ) := by
    simp only [n, fiberColumn, Nat.cast_add, Nat.cast_mul]
  have hnvmod : (n.val : ZMod p) = (n₀.val : ZMod p) := by
    simp only [n, fiberColumn, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self,
      zero_mul, add_zero]
  have hnew : affineValue A₁ B₁ C₁ n (k.val : ℤ) = c := by
    simp only [affineValue, hB₁, zero_mul, add_zero, hnvmod, c]
  have hvalue : (W n ((p : ℤ) * (k.val : ℤ)) : ZMod p) = c :=
    (hH₁.2 n (k.val : ℤ) (by rw [hnew]; exact hc)).trans hnew
  have hfactor : a * (n.val : ℤ) + b = (p : ℤ) * (z + a * (k.val : ℤ)) := by
    rw [hnv]
    linear_combination hz
  have hnot : ¬ (p : ℤ) ∣ z + a * (k.val : ℤ) := by
    intro hd
    apply hk0
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd (z + a * (k.val : ℤ)) p).mpr hd
  have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  have hnotSq : ¬ (p : ℤ) ^ 2 ∣ a * (n.val : ℤ) + b := by
    intro hd
    apply hnot
    apply (Int.mul_dvd_mul_iff_left hp0).mp
    simpa only [pow_two, hfactor] using hd
  have hdivn : (p : ℤ) ∣ a * (n.val : ℤ) + b := ⟨z + a * (k.val : ℤ), hfactor⟩
  have hsecond := (hw n).2 hdivn hnotSq
  dsimp only at hsecond
  have hline : 1 * (n.val : ℤ) + -(n₀.val : ℤ) = (p : ℤ) * (k.val : ℤ) := by
    rw [hnv]
    ring
  rw [hline, hvalue, hfactor, Int.mul_ediv_cancel_left _ hp0] at hsecond
  apply hkc
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using hsecond.symm

theorem no_positive_nat_vertical_period {p : ℕ} (hp : p.Prime)
    (hlarge : 200 < p) :
    ∀ M : ℕ, ∀ W : WordArray p, LineRule p W → NonconstantColumns W →
      0 < M → VerticalPeriod W (M : ℤ) → False := by
  intro M
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro W hW hcolumns hM hperiod
    obtain ⟨A, B, C, hH⟩ := global_affine_approximation hp hlarge hW
    have hB := (nonconstantColumns_iff_vertical_coefficient hp hlarge hH).mp hcolumns
    have hdivZ := prime_dvd_vertical_period hp hlarge hH hB hperiod
    have hdiv : p ∣ M := Int.natCast_dvd_natCast.mp hdivZ
    obtain ⟨u, v, hnorm⟩ := exists_straighten_affine hp hH hB
    let W₀ := straighten W u v
    have hW₀ : LineRule p W₀ := straighten_lineRule hW u v
    have hperiod₀ : VerticalPeriod W₀ (M : ℤ) :=
      (straighten_verticalPeriod_iff W u v (M : ℤ)).mpr hperiod
    have hW₁ : LineRule p (rescale W₀) := rescale_lineRule hW₀
    obtain ⟨A₁, B₁, C₁, hH₁⟩ := global_affine_approximation hp hlarge hW₁
    have hB₁ := rescale_vertical_coefficient_ne_zero hp hlarge hW₀ hB hnorm hH₁
    have hcolumns₁ := (nonconstantColumns_iff_vertical_coefficient hp hlarge hH₁).mpr hB₁
    have hsmall : M / p < M := Nat.div_lt_self hM hp.one_lt
    have hpos : 0 < M / p := Nat.div_pos (Nat.le_of_dvd hM hdiv) hp.pos
    have hquot : (p : ℤ) * ((M / p : ℕ) : ℤ) = (M : ℤ) := by
      exact_mod_cast Nat.mul_div_cancel' hdiv
    have hperiod₁ : VerticalPeriod (rescale W₀) ((M / p : ℕ) : ℤ) := by
      intro n m
      change W₀ n ((p : ℤ) * (m + ((M / p : ℕ) : ℤ))) = W₀ n ((p : ℤ) * m)
      rw [mul_add, hquot]
      exact hperiod₀ n ((p : ℤ) * m)
    exact ih (M / p) hsmall (rescale W₀) hW₁ hcolumns₁ hpos hperiod₁

theorem no_positive_vertical_period {p : ℕ} (hp : p.Prime)
    (hlarge : 200 < p) {W : WordArray p} (hW : LineRule p W)
    (hcolumns : NonconstantColumns W) {M : ℤ} (hM : 0 < M)
    (hperiod : VerticalPeriod W M) : False := by
  have hpos : 0 < M.toNat := Int.pos_iff_toNat_pos.mp hM
  have hcast : (M.toNat : ℤ) = M := Int.toNat_of_nonneg hM.le
  exact no_positive_nat_vertical_period hp hlarge M.toNat W hW hcolumns hpos
    (by simpa only [hcast] using hperiod)

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

theorem graph_not_fully_periodic_of_activity
    (o : GraphOutputs E) (hdep : HasDependence E o)
    (hwords : ∀ x (w : Word p), (∀ n, Active E o (.inl n) x (w n)) → Allowed p w)
    (hseeds : ∀ (t : Fin 2) (n : Column p) (x : Plane) (j : Symbol p),
      Active E o (.inr t) x () → Active E o (.inl n) x j → j = seedSymbol E t)
    (hordinary : ∀ n x, ∃ j, Active E o (.inl n) x j)
    (hseedactive : ∀ t : Fin 2, ∃ x : Plane, Active E o (.inr t) x ()) :
    ¬ FullyPeriodic (graph o) := by
  intro hper
  obtain ⟨x, hx⟩ := hseedactive 0
  obtain ⟨y, hy⟩ := hseedactive 1
  have hline : LineRule p (selectedWord E o) :=
    selectedWord_lineRule E o hdep hordinary hwords
  have hcolumns : NonconstantColumns (selectedWord E o) :=
    selectedWord_nonconstant_of_forced_letters E o hdep hordinary
      (seedSymbol E 0) (seedSymbol E 1) (seedSymbol_zero_ne_one E) x y
      (fun n j hj => hseeds 0 n x j hx hj)
      (fun n j hj => hseeds 1 n y j hy hj)
  obtain ⟨M, hM, hperiod⟩ := exists_positive_vertical_graph_period E o hper
  exact no_positive_vertical_period E.p_prime E.p_large hline hcolumns
    (Int.natCast_pos.mpr hM) (selectedWord_period_of_graph_period E o (M : ℤ) hperiod)

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

theorem solves_not_fully_periodic {A : Set (Ambient E)} (hA : Solves E A) :
    ¬ FullyPeriodic A := by
  obtain ⟨o, rfl⟩ := exists_graph_of_solves E hA
  obtain ⟨_hg, hd, hw, hs, ho, ht⟩ := (solves_iff E (graph o)).mp hA
  have hdep : HasDependence E o := (dependenceTiles_iff E o).mp hd
  apply graph_not_fully_periodic_of_activity E o hdep
  · exact (wordConstraintTiles_iff E o hdep).mp hw
  · exact (seedConstraintTiles_iff E o hdep).mp hs
  · intro n
    exact ordinary_active_of_tile E o hdep n (ho n)
  · intro t
    exact seed_active_somewhere_of_tile E o hdep t (ht t)

theorem testTile_not_fully_periodic {A : Set (Ambient E)}
    (hA : ∀ i : TestIndex E, Tiles (testTile E i) A) : ¬ FullyPeriodic A :=
  solves_not_fully_periodic E ((solves_iff_index E A).mpr hA)

theorem no_periodic_common_solution :
    ¬ ∃ A : Set (Ambient E), Solves E A ∧ FullyPeriodic A := by
  rintro ⟨A, hA, hperiod⟩
  exact solves_not_fully_periodic E hA hperiod

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace PeriodicTilingThree
namespace EncodingPrimeSelection

private def nextPrime (bound : ℕ) : ℕ :=
  Classical.choose (Nat.exists_infinite_primes (bound + 1))

private theorem nextPrime_prime (bound : ℕ) : Nat.Prime (nextPrime bound) :=
  (Classical.choose_spec (Nat.exists_infinite_primes (bound + 1))).2

private theorem nextPrime_gt (bound : ℕ) : bound < nextPrime bound := by
  have h := (Classical.choose_spec (Nat.exists_infinite_primes (bound + 1))).1
  exact h

private def primeSequence (bound : ℕ) : ℕ → ℕ
  | 0 => nextPrime bound
  | n + 1 => nextPrime (primeSequence bound n)

private theorem primeSequence_strictMono (bound : ℕ) :
    StrictMono (primeSequence bound) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact nextPrime_gt _

private theorem primeSequence_prime (bound n : ℕ) :
    Nat.Prime (primeSequence bound n) := by
  cases n with
  | zero => exact nextPrime_prime _
  | succ n => exact nextPrime_prime _

private theorem primeSequence_gt (bound n : ℕ) : bound < primeSequence bound n :=
  lt_of_lt_of_le (nextPrime_gt bound)
    ((primeSequence_strictMono bound).monotone (Nat.zero_le n))

theorem exists_prime_family (ι : Type uι) [Fintype ι] (bound : ℕ) :
    ∃ f : ι → ℕ, Function.Injective f ∧
      ∀ i, Nat.Prime (f i) ∧ bound < f i := by
  let e := Fintype.equivFin ι
  refine ⟨fun i => primeSequence bound (e i).val, ?_, ?_⟩
  · intro i j hij
    apply e.injective
    apply Fin.ext
    exact (primeSequence_strictMono bound).injective hij
  · intro i
    exact ⟨primeSequence_prime _ _, primeSequence_gt _ _⟩

theorem exists_positive_combination {a b r : ℕ} (hab : Nat.Coprime a b)
    (ha : 1 < a) (hb : 1 < b) (hr : a * b + a + b < r) :
    ∃ A B : ℕ, 0 < A ∧ 0 < B ∧ r = A * a + B * b := by
  have hmem : r - a - b ∈ AddSubmonoid.closure ({a, b} : Set ℕ) := by
    by_contra hnot
    have hle := (frobeniusNumber_pair hab ha hb).2 hnot
    have hbound : a * b - a - b ≤ a * b :=
      (Nat.sub_le (a * b - a) b).trans (Nat.sub_le (a * b) a)
    omega
  obtain ⟨A, B, hAB⟩ := (AddSubmonoid.mem_closure_pair a b (r - a - b)).mp hmem
  simp only [smul_eq_mul] at hAB
  refine ⟨A + 1, B + 1, by omega, by omega, ?_⟩
  calc
    r = (r - a - b) + a + b := by omega
    _ = (A * a + B * b) + a + b := by rw [hAB]
    _ = (A + 1) * a + (B + 1) * b := by ring

private abbrev UsefulTag (p : ℕ) := Channel p ⊕ Channel p
private abbrev FreshUsefulTag (p : ℕ) := Column p ⊕ Channel p
private abbrev DigitTag (p : ℕ) := Σ i, Label p i

private def usefulTagEquiv (p : ℕ) :
    UsefulTag p ≃ Fin 2 ⊕ FreshUsefulTag p :=
  (Equiv.sumCongr (Equiv.sumComm (Column p) (Fin 2))
    (Equiv.refl (Channel p))).trans (Equiv.sumAssoc (Fin 2) (Column p) (Channel p))

private def usefulPrime {p : ℕ} (f : FreshUsefulTag p → ℕ) : UsefulTag p → ℕ :=
  Sum.elim (fun t : Fin 2 => t.val + 2) f ∘ usefulTagEquiv p

private theorem usefulPrime_injective {p : ℕ} {f : FreshUsefulTag p → ℕ}
    (hf : Function.Injective f) (hlarge : ∀ t, 3 < f t) :
    Function.Injective (usefulPrime f) := by
  have hseed : Function.Injective (fun t : Fin 2 => t.val + 2) := by
    intro t u htu
    apply Fin.ext
    change t.val + 2 = u.val + 2 at htu
    exact Nat.add_right_cancel htu
  have hsep : ∀ t : Fin 2, ∀ i, t.val + 2 ≠ f i := by
    intro t i heq
    have ht := t.isLt
    have hi := hlarge i
    omega
  exact (hseed.sumElim hf hsep).comp (usefulTagEquiv p).injective

private theorem usefulPrime_prime {p : ℕ} {f : FreshUsefulTag p → ℕ}
    (hf : ∀ i, Nat.Prime (f i)) (i : UsefulTag p) :
    Nat.Prime (usefulPrime f i) := by
  rcases i with (i | t) | i
  · exact hf (.inl i)
  · change Nat.Prime (t.val + 2)
    fin_cases t
    · exact Nat.prime_two
    · exact Nat.prime_three
  · exact hf (.inr i)

private def attachDigits {p : ℕ} (f : UsefulTag p → ℕ) (g : DigitTag p → ℕ) :
    PrimeTag p → ℕ :=
  Sum.elim f g ∘ (Equiv.sumAssoc (Channel p) (Channel p) (DigitTag p)).symm

private theorem attachDigits_injective {p : ℕ}
    {f : UsefulTag p → ℕ} {g : DigitTag p → ℕ}
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hsep : ∀ i j, f i ≠ g j) : Function.Injective (attachDigits f g) :=
  (hf.sumElim hg hsep).comp
    (Equiv.sumAssoc (Channel p) (Channel p) (DigitTag p)).symm.injective

theorem exists_parameters {p : ℕ} (hp : Nat.Prime p) (hlarge : 200 < p) :
    Nonempty (EncodingParameters p) := by
  classical
  let : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨f, hfinj, hf⟩ := exists_prime_family (FreshUsefulTag p) (p ^ 4 + p + 3)
  let useful : UsefulTag p → ℕ := usefulPrime f
  have huseful_prime : ∀ i, Nat.Prime (useful i) :=
    usefulPrime_prime (fun i => (hf i).1)
  have huseful_inj : Function.Injective useful := by
    apply usefulPrime_injective hfinj
    intro i
    have := (hf i).2
    omega
  have huseful_ne_p : ∀ i, useful i ≠ p := by
    intro i
    rcases i with (i | t) | i
    · change f (.inl i) ≠ p
      have := (hf (.inl i)).2
      omega
    · change t.val + 2 ≠ p
      have := t.isLt
      omega
    · change f (.inr i) ≠ p
      have := (hf (.inr i)).2
      omega
  let threshold : Channel p → ℕ := fun i =>
    useful (.inl i) * useful (.inr i) + useful (.inl i) + useful (.inr i)
  let bound := p + Finset.univ.sup useful + Finset.univ.sup threshold
  obtain ⟨g, hginj, hg⟩ := exists_prime_family (DigitTag p) bound
  have hseparate : ∀ i j, useful i < g j := by
    intro i j
    have hi : useful i ≤ Finset.univ.sup useful := Finset.le_sup (Finset.mem_univ i)
    have hj := (hg j).2
    dsimp [bound] at hj
    omega
  have hthreshold : ∀ i j, threshold i < g ⟨i, j⟩ := by
    intro i j
    have hi : threshold i ≤ Finset.univ.sup threshold :=
      Finset.le_sup (Finset.mem_univ i)
    have hj := (hg ⟨i, j⟩).2
    dsimp [bound] at hj
    omega
  have hrepresentation : ∀ i (j : Label p i), ∃ A B : ℕ,
      0 < A ∧ 0 < B ∧ g ⟨i, j⟩ = A * useful (.inl i) + B * useful (.inr i) := by
    intro i j
    have hcop : Nat.Coprime (useful (.inl i)) (useful (.inr i)) := by
      apply (Nat.coprime_primes (huseful_prime _) (huseful_prime _)).2
      intro h
      have htags := huseful_inj h
      cases htags
    exact exists_positive_combination hcop
      (huseful_prime _).one_lt (huseful_prime _).one_lt (hthreshold i j)
  choose A B hA hB hrepresentation using hrepresentation
  refine ⟨{
    p_prime := hp
    p_large := hlarge
    primeAt := attachDigits useful g
    prime_isPrime := ?_
    prime_injective := attachDigits_injective huseful_inj hginj
      (fun i j => (hseparate i j).ne)
    prime_ne_p := ?_
    seed_a_eq := ?_
    seed_b_large := ?_
    blockA := A
    blockB := B
    blockA_pos := hA
    blockB_pos := hB
    digit_representation := ?_
  }⟩
  · intro t
    rcases t with i | (i | j)
    · exact huseful_prime (.inl i)
    · exact huseful_prime (.inr i)
    · exact (hg j).1
  · intro t
    rcases t with i | (i | j)
    · exact huseful_ne_p (.inl i)
    · exact huseful_ne_p (.inr i)
    · change g j ≠ p
      have hj := (hg j).2
      dsimp [bound] at hj
      omega
  · intro t
    rfl
  · intro t
    change p ^ 4 < f (.inr (.inr t))
    have ht := (hf (.inr (.inr t))).2
    omega
  · intro i j
    exact hrepresentation i j

end EncodingPrimeSelection

theorem exists_encodingParameters {p : ℕ} (hp : Nat.Prime p) (hlarge : 200 < p) :
    Nonempty (EncodingParameters p) :=
  EncodingPrimeSelection.exists_parameters hp hlarge

def encodingParameters {p : ℕ} (hp : Nat.Prime p) (hlarge : 200 < p) :
    EncodingParameters p :=
  Classical.choice (exists_encodingParameters hp hlarge)

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

open scoped BigOperators

variable {p : ℕ} [NeZero p]

namespace EncodingParameters

variable (E : EncodingParameters p)

def blockModulus (i : Channel p) : ℕ := (E.r i) ^ 2 * E.a i * E.b i
def cyclicOrder : ℕ := p ^ 4 * ∏ i : Channel p, E.blockModulus i

theorem blockModulus_pos (i : Channel p) : 0 < E.blockModulus i :=
  Nat.mul_pos (Nat.mul_pos (pow_pos (E.r_pos i) 2) (E.a_pos i)) (E.b_pos i)

theorem cyclicOrder_pos : 0 < E.cyclicOrder :=
  Nat.mul_pos (pow_pos E.p_prime.pos 4)
    (Finset.prod_pos (fun i _ => E.blockModulus_pos i))

instance blockModulus_neZero (i : Channel p) : NeZero (E.blockModulus i) :=
  ⟨(E.blockModulus_pos i).ne'⟩
instance cyclicOrder_neZero : NeZero E.cyclicOrder := ⟨E.cyclicOrder_pos.ne'⟩

theorem a_coprime_b_all
    {p : ℕ} [NeZero p] (E : EncodingParameters p)
    (i j : Channel p) : Nat.Coprime (E.a i) (E.b j) := by
  apply E.prime_coprime
  simp

theorem a_pairwise_coprime
    {p : ℕ} [NeZero p] (E : EncodingParameters p)
    : Pairwise (fun i j : Channel p => Nat.Coprime (E.a i) (E.a j)) := by
  intro i j hij
  apply E.prime_coprime
  simpa using hij

theorem b_pairwise_coprime
    {p : ℕ} [NeZero p] (E : EncodingParameters p)
    : Pairwise (fun i j : Channel p => Nat.Coprime (E.b i) (E.b j)) := by
  intro i j hij
  apply E.prime_coprime
  simpa using hij

theorem blockModulus_pairwise :
    Pairwise (fun i j : Channel p => Nat.Coprime (E.blockModulus i) (E.blockModulus j)) := by
  intro i j hij
  have hrr := (E.r_pairwise_coprime hij).pow 2 2
  have hra := (E.r_coprime_a i j).pow_left 2
  have hrb := (E.r_coprime_b i j).pow_left 2
  have har := (E.r_coprime_a j i).symm.pow_right 2
  have haa := E.a_pairwise_coprime hij
  have hab := E.a_coprime_b_all i j
  have hbr := (E.r_coprime_b j i).symm.pow_right 2
  have hba := (E.a_coprime_b_all j i).symm
  have hbb := E.b_pairwise_coprime hij
  simp only [blockModulus, Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right]
  exact ⟨⟨⟨⟨hrr, har⟩, hbr⟩, ⟨⟨hra, haa⟩, hba⟩⟩, ⟨⟨hrb, hab⟩, hbb⟩⟩

theorem p_coprime_blockModulus (i : Channel p) :
    Nat.Coprime p (E.blockModulus i) := by
  have hr := (E.r_coprime_p i).symm.pow_right 2
  have ha : Nat.Coprime p (E.a i) := (E.prime_coprime_p (.inl i)).symm
  have hb : Nat.Coprime p (E.b i) := (E.prime_coprime_p (.inr (.inl i))).symm
  simp only [blockModulus, Nat.coprime_mul_iff_right]
  exact ⟨⟨hr, ha⟩, hb⟩

theorem p4_coprime_blocks :
    Nat.Coprime (p ^ 4) (∏ i : Channel p, E.blockModulus i) := by
  apply Nat.coprime_fintype_prod_right_iff.mpr
  intro i
  exact (E.p_coprime_blockModulus i).pow_left 4

end EncodingParameters

variable (E : EncodingParameters p)

def channelCRT (i : Channel p) :
    ZMod (E.blockModulus i) ≃+ (ZMod ((E.r i) ^ 2) × P E i) := by
  have hRA : Nat.Coprime ((E.r i) ^ 2) (E.a i) := (E.r_coprime_a i i).pow_left 2
  have hRAB : Nat.Coprime ((E.r i) ^ 2 * E.a i) (E.b i) :=
    Nat.coprime_mul_iff_left.mpr ⟨(E.r_coprime_b i i).pow_left 2, E.a_coprime_b i⟩
  exact ((ZMod.chineseRemainder hRAB).toAddEquiv.trans
    (AddEquiv.prodCongr (ZMod.chineseRemainder hRA).toAddEquiv
      (AddEquiv.refl (ZMod (E.b i))))).trans AddEquiv.prodAssoc

def cyclicToFiniteFactor : ZMod E.cyclicOrder ≃+ V E :=
  (ZMod.chineseRemainder E.p4_coprime_blocks).toAddEquiv.trans
    (AddEquiv.prodCongr (AddEquiv.refl (ZMod (p ^ 4)))
      ((ZMod.prodEquivPi E.blockModulus E.blockModulus_pairwise).toAddEquiv.trans
        (AddEquiv.piCongrRight (fun i => channelCRT E i))))

def finiteFactorEquiv : V E ≃+ ZMod E.cyclicOrder := (cyclicToFiniteFactor E).symm

def ambientCyclicEquiv : Ambient E ≃+ (Plane × ZMod E.cyclicOrder) :=
  AddEquiv.prodCongr (AddEquiv.refl Plane) (finiteFactorEquiv E)

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

section FiniteStack

variable {H : Type uH} {K : Type uK} {ι : Type uι} [Fintype ι]

def IsColorPartition (E : ι → Finset K) : Prop :=
  ∀ t : K, ∃! ν : ι, t ∈ E ν

def HasFullDifferences [AddGroup K] (E : ι → Finset K) : Prop :=
  ∀ (ν : ι) (d : K), ∃ e ∈ E ν, ∃ e' ∈ E ν, e - e' = d

noncomputable def stack (F : ι → Finset H) (E : ι → Finset K) :
    Finset (H × K) := by
  classical
  exact Finset.univ.biUnion (fun ν => (F ν).product (E ν))

@[simp] theorem mem_stack {F : ι → Finset H} {E : ι → Finset K} {p : H × K} :
    p ∈ stack F E ↔ ∃ ν, p.1 ∈ F ν ∧ p.2 ∈ E ν := by
  classical
  simp [stack]

theorem stack_nonempty [Nonempty ι] {F : ι → Finset H} {E : ι → Finset K}
    (hF : ∀ ν, (F ν).Nonempty) (hE : ∀ ν, (E ν).Nonempty) :
    (stack F E).Nonempty := by
  obtain ⟨ν⟩ := ‹Nonempty ι›
  obtain ⟨f, hf⟩ := hF ν
  obtain ⟨e, he⟩ := hE ν
  exact ⟨(f, e), mem_stack.mpr ⟨ν, hf, he⟩⟩

theorem IsColorPartition.eq_of_mem
    {K : Type uK} {ι : Type uι} [Fintype ι]
    {E : ι → Finset K} (hpart : IsColorPartition E)
    {ν μ : ι} {e : K} (hν : e ∈ E ν) (hμ : e ∈ E μ) : ν = μ := by
  obtain ⟨i, _, hi⟩ := hpart e
  exact (hi ν hν).trans (hi μ hμ).symm

theorem HasFullDifferences.nonempty
    {K : Type uK} {ι : Type uι} [Fintype ι]
    [AddGroup K] {E : ι → Finset K}
    (hfull : HasFullDifferences E) (ν : ι) : (E ν).Nonempty := by
  obtain ⟨e, he, _, _, _⟩ := hfull ν 0
  exact ⟨e, he⟩

theorem card_stack {F : ι → Finset H} {E : ι → Finset K}
    (hpart : IsColorPartition E) :
    (stack F E).card = ∑ ν, (F ν).card * (E ν).card := by
  classical
  have hdisj : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
      (fun ν => (F ν).product (E ν)) := by
    intro ν _ μ _ hne
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    exact hne (hpart.eq_of_mem (Finset.mem_product.mp hp).2
      (Finset.mem_product.mp hp').2)
  simpa only [stack, Finset.product_eq_sprod, Finset.card_product] using
    Finset.card_biUnion hdisj

theorem IsColorPartition.sum_card [Fintype K] {E : ι → Finset K}
    (hpart : IsColorPartition E) : ∑ ν, (E ν).card = Fintype.card K := by
  classical
  let f : (Σ ν, ↥(E ν)) → K := fun z => z.2.1
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨ν, e⟩ ⟨μ, e'⟩ heq
      change (e : K) = (e' : K) at heq
      have hνμ : ν = μ := hpart.eq_of_mem e.property (heq.symm ▸ e'.property)
      cases hνμ
      have he : e = e' := Subtype.ext heq
      cases he
      rfl
    · intro e
      obtain ⟨ν, hν, _⟩ := hpart e
      exact ⟨⟨ν, ⟨e, hν⟩⟩, rfl⟩
  simpa only [Fintype.card_sigma, Fintype.card_coe] using
    Fintype.card_congr (Equiv.ofBijective f hf)

end FiniteStack

section Contributions

variable {H : Type uH} {K : Type uK} {ι : Type uι} [AddCommGroup H] [AddCommGroup K]
variable [Fintype K] [Fintype ι]

noncomputable def stackContributions (F : ι → Finset H) (B : Set (H × K))
    (g : H) (ν : ι) : Finset (H × K) := by
  classical
  exact ((F ν).product Finset.univ).filter (fun ft => (g - ft.1, ft.2) ∈ B)

@[simp] theorem mem_stackContributions
    {H : Type uH} {K : Type uK} {ι : Type uι}
    [AddCommGroup H] [AddCommGroup K] [Fintype K] [Fintype ι]
    {F : ι → Finset H} {B : Set (H × K)}
    {g : H} {ν : ι} {c : H × K} :
    c ∈ stackContributions F B g ν ↔ c.1 ∈ F ν ∧ (g - c.1, c.2) ∈ B := by
  classical
  simp [stackContributions]

theorem stackContributions_eq_of_mem {F : ι → Finset H} {E : ι → Finset K}
    {B : Set (H × K)} (hfull : HasFullDifferences E) (hB : Tiles (stack F E) B)
    {g : H} {ν : ι} {c c' : H × K}
    (hc : c ∈ stackContributions F B g ν)
    (hc' : c' ∈ stackContributions F B g ν) : c = c' := by
  obtain ⟨hcf, hcB⟩ := mem_stackContributions.mp hc
  obtain ⟨hc'f, hc'B⟩ := mem_stackContributions.mp hc'
  obtain ⟨e, he, e', he', hd⟩ := hfull ν (c'.2 - c.2)
  have hvertical : c.2 + e = c'.2 + e' := by
    calc
      c.2 + e = c.2 + (e - e') + e' := by abel
      _ = c.2 + (c'.2 - c.2) + e' := by rw [hd]
      _ = c'.2 + e' := by abel
  let p : ↥(stack F E) × B :=
    (⟨(c.1, e), mem_stack.mpr ⟨ν, hcf, he⟩⟩, ⟨(g - c.1, c.2), hcB⟩)
  let p' : ↥(stack F E) × B :=
    (⟨(c'.1, e'), mem_stack.mpr ⟨ν, hc'f, he'⟩⟩, ⟨(g - c'.1, c'.2), hc'B⟩)
  have hp : p = p' := by
    apply hB.1
    apply Prod.ext
    · change c.1 + (g - c.1) = c'.1 + (g - c'.1)
      simp
    · change e + c.2 = e' + c'.2
      simpa only [add_comm] using hvertical
  apply Prod.ext
  · exact congrArg (fun z : ↥(stack F E) × B => z.1.1.1) hp
  · exact congrArg (fun z : ↥(stack F E) × B => z.2.1.2) hp

theorem stackContributions_card_le_one {F : ι → Finset H} {E : ι → Finset K}
    {B : Set (H × K)} (hfull : HasFullDifferences E) (hB : Tiles (stack F E) B)
    (g : H) (ν : ι) : (stackContributions F B g ν).card ≤ 1 := by
  classical
  exact Finset.card_le_one.mpr fun _ hc _ hc' =>
    stackContributions_eq_of_mem hfull hB hc hc'

theorem stack_projection_injective [Nonempty ι]
    {F : ι → Finset H} {E : ι → Finset K} {B : Set (H × K)}
    (hF : ∀ ν, (F ν).Nonempty) (hfull : HasFullDifferences E)
    (hB : Tiles (stack F E) B) : Set.InjOn Prod.fst B := by
  obtain ⟨ν⟩ := ‹Nonempty ι›
  obtain ⟨f, hf⟩ := hF ν
  intro b hb b' hb' heq
  have hc : (f, b.2) ∈ stackContributions F B (b.1 + f) ν := by
    apply mem_stackContributions.mpr
    exact ⟨hf, by simpa using hb⟩
  have hc' : (f, b'.2) ∈ stackContributions F B (b.1 + f) ν := by
    apply mem_stackContributions.mpr
    refine ⟨hf, ?_⟩
    simpa [heq] using hb'
  have ht := congrArg Prod.snd (stackContributions_eq_of_mem hfull hB hc hc')
  exact Prod.ext heq ht

def StackFiber (F : ι → Finset H) (E : ι → Finset K)
    (B : Set (H × K)) (g : H) :=
  Σ ν : ι, ↥(stackContributions F B g ν) × ↥(E ν)

def stackFiberSum {F : ι → Finset H} {E : ι → Finset K}
    {B : Set (H × K)} {g : H} (z : StackFiber F E B g) : K :=
  z.2.1.1.2 + z.2.2.1

theorem stackFiberSum_bijective {F : ι → Finset H} {E : ι → Finset K}
    {B : Set (H × K)} (hpart : IsColorPartition E) (hB : Tiles (stack F E) B)
    (g : H) : Function.Bijective (stackFiberSum (F := F) (E := E) (B := B) (g := g)) := by
  classical
  constructor
  · rintro ⟨ν, c, e⟩ ⟨μ, c', e'⟩ heq
    obtain ⟨hcf, hcB⟩ := mem_stackContributions.mp c.property
    obtain ⟨hc'f, hc'B⟩ := mem_stackContributions.mp c'.property
    let p : ↥(stack F E) × B :=
      (⟨(c.1.1, e.1), mem_stack.mpr ⟨ν, hcf, e.property⟩⟩,
        ⟨(g - c.1.1, c.1.2), hcB⟩)
    let p' : ↥(stack F E) × B :=
      (⟨(c'.1.1, e'.1), mem_stack.mpr ⟨μ, hc'f, e'.property⟩⟩,
        ⟨(g - c'.1.1, c'.1.2), hc'B⟩)
    have hp : p = p' := by
      apply hB.1
      apply Prod.ext
      · change c.1.1 + (g - c.1.1) = c'.1.1 + (g - c'.1.1)
        simp
      · change e.1 + c.1.2 = e'.1 + c'.1.2
        simpa only [stackFiberSum, add_comm] using heq
    have hf : c.1.1 = c'.1.1 :=
      congrArg (fun z : ↥(stack F E) × B => z.1.1.1) hp
    have ht : c.1.2 = c'.1.2 :=
      congrArg (fun z : ↥(stack F E) × B => z.2.1.2) hp
    have he : (e : K) = (e' : K) :=
      congrArg (fun z : ↥(stack F E) × B => z.1.1.2) hp
    have hνμ : ν = μ := hpart.eq_of_mem e.property (he.symm ▸ e'.property)
    cases hνμ
    have hc : c = c' := Subtype.ext (Prod.ext hf ht)
    have he' : e = e' := Subtype.ext he
    cases hc
    cases he'
    rfl
  · intro u
    obtain ⟨p, hp⟩ := hB.2 (g, u)
    obtain ⟨ν, hf, he⟩ := mem_stack.mp p.1.property
    have hhorizontal : p.1.1.1 + p.2.1.1 = g := congrArg Prod.fst hp
    have hcenter : g - p.1.1.1 = p.2.1.1 := by
      rw [← hhorizontal]
      simp
    have hc : (p.1.1.1, p.2.1.2) ∈ stackContributions F B g ν := by
      apply mem_stackContributions.mpr
      exact ⟨hf, by simpa only [hcenter] using p.2.property⟩
    refine ⟨⟨ν, ⟨(p.1.1.1, p.2.1.2), hc⟩, ⟨p.1.1.2, he⟩⟩, ?_⟩
    change p.2.1.2 + p.1.1.2 = u
    have hvertical : p.1.1.2 + p.2.1.2 = u := congrArg Prod.snd hp
    simpa only [add_comm] using hvertical

theorem stackContributions_sum_card {F : ι → Finset H} {E : ι → Finset K}
    {B : Set (H × K)} (hpart : IsColorPartition E) (hB : Tiles (stack F E) B)
    (g : H) :
    ∑ ν, (stackContributions F B g ν).card * (E ν).card = Fintype.card K := by
  classical
  let e : (Σ ν : ι, ↥(stackContributions F B g ν) × ↥(E ν)) ≃ K :=
    Equiv.ofBijective (stackFiberSum (F := F) (E := E) (B := B) (g := g))
      (stackFiberSum_bijective hpart hB g)
  simpa only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_coe] using
    Fintype.card_congr e

theorem stackContributions_card_eq_one {F : ι → Finset H} {E : ι → Finset K}
    {B : Set (H × K)} (hpart : IsColorPartition E) (hfull : HasFullDifferences E)
    (hE : ∀ ν, (E ν).Nonempty) (hB : Tiles (stack F E) B)
    (g : H) (ν : ι) : (stackContributions F B g ν).card = 1 := by
  classical
  have hle := stackContributions_card_le_one hfull hB g ν
  by_contra hne
  have hz : (stackContributions F B g ν).card = 0 := by omega
  have hstrict :
      (∑ i, (stackContributions F B g i).card * (E i).card) < ∑ i, (E i).card := by
    apply Finset.sum_lt_sum
    · intro i _
      calc
        (stackContributions F B g i).card * (E i).card ≤ 1 * (E i).card :=
          Nat.mul_le_mul_right _ (stackContributions_card_le_one hfull hB g i)
        _ = (E i).card := one_mul _
    · exact ⟨ν, Finset.mem_univ ν, by simpa only [hz, zero_mul] using (hE ν).card_pos⟩
  rw [stackContributions_sum_card hpart hB g, hpart.sum_card] at hstrict
  exact (lt_irrefl _) hstrict

theorem tiles_of_tiles_stack {F : ι → Finset H} {E : ι → Finset K}
    {B : Set (H × K)} (hpart : IsColorPartition E) (hfull : HasFullDifferences E)
    (hE : ∀ ν, (E ν).Nonempty) (hB : Tiles (stack F E) B) :
    ∀ ν, Tiles (F ν) (Prod.fst '' B) := by
  classical
  intro ν
  apply tiles_iff_unique_tile.mpr
  intro g
  have hcard := stackContributions_card_eq_one hpart hfull hE hB g ν
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (by omega : 0 < (stackContributions F B g ν).card)
  obtain ⟨hcf, hcB⟩ := mem_stackContributions.mp hc
  refine ⟨⟨c.1, hcf⟩, ⟨(g - c.1, c.2), hcB, rfl⟩, ?_⟩
  intro f hf
  obtain ⟨b, hb, hbf⟩ := hf
  have hc' : ((f : H), b.2) ∈ stackContributions F B g ν := by
    apply mem_stackContributions.mpr
    exact ⟨f.property, by simpa only [← hbf] using hb⟩
  apply Subtype.ext
  exact congrArg Prod.fst (stackContributions_eq_of_mem hfull hB hc' hc)

end Contributions

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

section Stacking

variable {H : Type uH} {K : Type uK} {ι : Type uι} [AddCommGroup H] [AddCommGroup K]
variable [Fintype K] [Fintype ι]

theorem tiles_stack_lift
    {H : Type uH} {K : Type uK} {ι : Type uι}
    [AddCommGroup H] [AddCommGroup K] [Fintype K] [Fintype ι]
    {F : ι → Finset H} {E : ι → Finset K} {A : Set H}
    (hpart : IsColorPartition E) (hA : ∀ ν, Tiles (F ν) A) :
    Tiles (stack F E) (A ×ˢ ({0} : Set K)) := by
  classical
  apply tiles_iff_unique_tile.mpr
  intro x
  obtain ⟨ν, hν, _⟩ := hpart x.2
  obtain ⟨f, hf, huniq⟩ := tiles_iff_unique_tile.mp (hA ν) x.1
  refine ⟨⟨((f : H), x.2), mem_stack.mpr ⟨ν, f.property, hν⟩⟩, ?_, ?_⟩
  · change x.1 - (f : H) ∈ A ∧ x.2 - x.2 ∈ ({0} : Set K)
    exact ⟨hf, by simp⟩
  · intro y hy
    change x.1 - y.1.1 ∈ A ∧ x.2 - y.1.2 ∈ ({0} : Set K) at hy
    obtain ⟨μ, hyF, hyE⟩ := mem_stack.mp y.property
    have hy2 : y.1.2 = x.2 := (sub_eq_zero.mp (Set.mem_singleton_iff.mp hy.2)).symm
    have hμν : μ = ν := hpart.eq_of_mem (hy2 ▸ hyE) hν
    cases hμν
    have hy1 : (⟨y.1.1, hyF⟩ : ↥(F ν)) = f := huniq ⟨y.1.1, hyF⟩ hy.1
    apply Subtype.ext
    exact Prod.ext (congrArg Subtype.val hy1) hy2

theorem fullyPeriodic_stack_lift {A : Set H} (hA : FullyPeriodic A) :
    FullyPeriodic (A ×ˢ ({0} : Set K)) :=
  hA.prod_singleton_zero

theorem fullyPeriodic_stack_project
    {H : Type uH} {K : Type uK}
    [AddCommGroup H] [AddCommGroup K] [Fintype K]
    {B : Set (H × K)} (hB : FullyPeriodic B) :
    FullyPeriodic (Prod.fst '' B) :=
  FullyPeriodic.image_of_surjective (AddMonoidHom.fst H K)
    (fun x => ⟨(x, 0), rfl⟩) hB

theorem exists_tiles_stack_iff {F : ι → Finset H} {E : ι → Finset K}
    (hpart : IsColorPartition E) (hfull : HasFullDifferences E)
    (hE : ∀ ν, (E ν).Nonempty) :
    (∃ A : Set H, ∀ ν, Tiles (F ν) A) ↔
      ∃ B : Set (H × K), Tiles (stack F E) B := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨A ×ˢ ({0} : Set K), tiles_stack_lift hpart hA⟩
  · rintro ⟨B, hB⟩
    exact ⟨Prod.fst '' B, tiles_of_tiles_stack hpart hfull hE hB⟩

theorem exists_fullyPeriodic_tiles_stack_iff
    {F : ι → Finset H} {E : ι → Finset K}
    (hpart : IsColorPartition E) (hfull : HasFullDifferences E)
    (hE : ∀ ν, (E ν).Nonempty) :
    (∃ A : Set H, (∀ ν, Tiles (F ν) A) ∧ FullyPeriodic A) ↔
      ∃ B : Set (H × K), Tiles (stack F E) B ∧ FullyPeriodic B := by
  constructor
  · rintro ⟨A, hA, hperiod⟩
    exact ⟨A ×ˢ ({0} : Set K), tiles_stack_lift hpart hA,
      fullyPeriodic_stack_lift hperiod⟩
  · rintro ⟨B, hB, hperiod⟩
    exact ⟨Prod.fst '' B, tiles_of_tiles_stack hpart hfull hE hB,
      fullyPeriodic_stack_project hperiod⟩

theorem stack_counterexample_of_common_system [Nonempty ι]
    {F : ι → Finset H} {E : ι → Finset K}
    (hF : ∀ ν, (F ν).Nonempty) (hE : ∀ ν, (E ν).Nonempty)
    (hpart : IsColorPartition E) (hfull : HasFullDifferences E)
    (hcommon : ∃ A : Set H, ∀ ν, Tiles (F ν) A)
    (hnone : ∀ A : Set H, (∀ ν, Tiles (F ν) A) → ¬ FullyPeriodic A) :
    (stack F E).Nonempty ∧ (∃ B, Tiles (stack F E) B) ∧
      ∀ B, Tiles (stack F E) B → ¬ FullyPeriodic B := by
  refine ⟨stack_nonempty hF hE, (exists_tiles_stack_iff hpart hfull hE).mp hcommon, ?_⟩
  intro B hB hperiod
  exact hnone (Prod.fst '' B) (tiles_of_tiles_stack hpart hfull hE hB)
    (fullyPeriodic_stack_project hperiod)

end Stacking

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

theorem not_dvd_card_of_lt (V : Type uV) [AddCommGroup V] [Finite V]
    {q : ℕ} (hq : Nat.card V < q) : ¬ q ∣ Nat.card V := by
  intro hdiv
  exact (Nat.not_le_of_gt hq) (Nat.le_of_dvd Nat.card_pos hdiv)

theorem cyclicStackOrder_pos (V : Type uV) [AddCommGroup V] [Finite V]
    (q : ℕ) (hq : q.Prime) : 0 < q * Nat.card V :=
  Nat.mul_pos hq.pos Nat.card_pos

noncomputable def freshCyclicEquiv
    (V : Type uV) [AddCommGroup V] [Finite V] [IsAddCyclic V]
    (q : ℕ) (hq : q.Prime) (havoid : ¬ q ∣ Nat.card V) :
    V × ZMod q ≃+ ZMod (q * Nat.card V) := by
  let eV : V ≃+ ZMod (Nat.card V) :=
    (zmodAddCyclicAddEquiv (G := V) inferInstance).symm
  let hcop : q.Coprime (Nat.card V) :=
    hq.coprime_iff_not_dvd.mpr havoid
  exact
    ((eV.prodCongr (AddEquiv.refl (ZMod q))).trans
      (AddEquiv.prodComm :
        ZMod (Nat.card V) × ZMod q ≃+
          ZMod q × ZMod (Nat.card V))).trans
      (ZMod.chineseRemainder hcop).toAddEquiv.symm

noncomputable def cyclicStackEquiv
    (V : Type uV) [AddCommGroup V] [Finite V] [IsAddCyclic V]
    (q : ℕ) (hq : q.Prime) (havoid : ¬ q ∣ Nat.card V) :
    ((Plane × V) × ZMod q) ≃+ Plane × ZMod (q * Nat.card V) :=
  (AddEquiv.prodAssoc :
    ((Plane × V) × ZMod q) ≃+ Plane × (V × ZMod q)).trans
      ((AddEquiv.refl Plane).prodCongr (freshCyclicEquiv V q hq havoid))

@[simp]
theorem cyclicStackEquiv_fst
    (V : Type uV) [AddCommGroup V] [Finite V] [IsAddCyclic V]
    (q : ℕ) (hq : q.Prime) (havoid : ¬ q ∣ Nat.card V)
    (x : (Plane × V) × ZMod q) :
    (cyclicStackEquiv V q hq havoid x).1 = x.1.1 := rfl

section Transport

variable (V : Type uV) [AddCommGroup V] [Finite V] [IsAddCyclic V]
variable (q : ℕ) (hq : q.Prime) (havoid : ¬ q ∣ Nat.card V)

noncomputable def cyclicStackComplement (A : Set (Plane × V)) :
    Set (Plane × ZMod (q * Nat.card V)) :=
  cyclicStackEquiv V q hq havoid '' (A ×ˢ ({0} : Set (ZMod q)))

noncomputable def cyclicStackProjection
    (B : Set (Plane × ZMod (q * Nat.card V))) : Set (Plane × V) :=
  Prod.fst '' (cyclicStackEquiv V q hq havoid ⁻¹' B)

theorem fullyPeriodic_cyclicStackComplement {A : Set (Plane × V)}
    (hA : FullyPeriodic A) :
    FullyPeriodic (cyclicStackComplement V q hq havoid A) := by
  let : NeZero q := ⟨hq.ne_zero⟩
  exact (fullyPeriodic_image_addEquiv_iff
    (cyclicStackEquiv V q hq havoid)).mpr hA.prod_singleton_zero

theorem fullyPeriodic_cyclicStackProjection
    {B : Set (Plane × ZMod (q * Nat.card V))} (hB : FullyPeriodic B) :
    FullyPeriodic (cyclicStackProjection V q hq havoid B) := by
  exact FullyPeriodic.image_of_surjective
    (AddMonoidHom.fst (Plane × V) (ZMod q))
    (fun x => ⟨(x, 0), rfl⟩)
    (FullyPeriodic.preimage_addEquiv (cyclicStackEquiv V q hq havoid) hB)

end Transport

section FiniteFamily

variable {ι : Type uι} [Fintype ι]
variable (V : Type uV) [AddCommGroup V] [Finite V] [IsAddCyclic V]
variable (q : ℕ) (hq : q.Prime) (havoid : ¬ q ∣ Nat.card V)

noncomputable def cyclicStackTile
    (F : ι → Finset (Plane × V)) (E : ι → Finset (ZMod q)) :
    Finset (Plane × ZMod (q * Nat.card V)) := by
  classical
  letI : NeZero q := ⟨hq.ne_zero⟩
  exact (stack F E).image (cyclicStackEquiv V q hq havoid)

theorem tiles_cyclicStackTile
    {F : ι → Finset (Plane × V)} {E : ι → Finset (ZMod q)}
    (hpart : IsColorPartition E) {A : Set (Plane × V)}
    (hA : ∀ ν, Tiles (F ν) A) :
    Tiles (cyclicStackTile V q hq havoid F E)
      (cyclicStackComplement V q hq havoid A) := by
  classical
  let : NeZero q := ⟨hq.ne_zero⟩
  exact Tiles.image_addEquiv (cyclicStackEquiv V q hq havoid)
    (tiles_stack_lift hpart hA)

theorem tiles_stack_of_tiles_cyclicStackTile
    {F : ι → Finset (Plane × V)} {E : ι → Finset (ZMod q)}
    {B : Set (Plane × ZMod (q * Nat.card V))}
    (hB : Tiles (cyclicStackTile V q hq havoid F E) B) :
    Tiles (stack F E) (cyclicStackEquiv V q hq havoid ⁻¹' B) := by
  classical
  let : NeZero q := ⟨hq.ne_zero⟩
  simpa only [cyclicStackTile, Finset.image_image, Function.comp_def,
    AddEquiv.symm_apply_apply, Finset.image_id'] using
    Tiles.preimage_addEquiv (cyclicStackEquiv V q hq havoid) hB

theorem tiles_of_tiles_cyclicStackTile
    {F : ι → Finset (Plane × V)} {E : ι → Finset (ZMod q)}
    (hpart : IsColorPartition E) (hfull : HasFullDifferences E)
    (hE : ∀ ν, (E ν).Nonempty)
    {B : Set (Plane × ZMod (q * Nat.card V))}
    (hB : Tiles (cyclicStackTile V q hq havoid F E) B) :
    ∀ ν, Tiles (F ν) (cyclicStackProjection V q hq havoid B) := by
  classical
  let : NeZero q := ⟨hq.ne_zero⟩
  exact tiles_of_tiles_stack hpart hfull hE
    (tiles_stack_of_tiles_cyclicStackTile V q hq havoid hB)

theorem cyclicStack_counterexample_of_common_system
    {F : ι → Finset (Plane × V)} {E : ι → Finset (ZMod q)}
    (hpart : IsColorPartition E) (hfull : HasFullDifferences E)
    (hE : ∀ ν, (E ν).Nonempty)
    (hcommon : ∃ A, ∀ ν, Tiles (F ν) A)
    (hnone : ∀ A, (∀ ν, Tiles (F ν) A) → ¬ FullyPeriodic A) :
    (cyclicStackTile V q hq havoid F E).Nonempty ∧
      (∃ A, Tiles (cyclicStackTile V q hq havoid F E)
        (cyclicStackComplement V q hq havoid A)) ∧
      ∀ B, Tiles (cyclicStackTile V q hq havoid F E) B →
        ¬ FullyPeriodic B := by
  obtain ⟨A, hA⟩ := hcommon
  have ht := tiles_cyclicStackTile V q hq havoid hpart hA
  refine ⟨ht.tile_nonempty, ⟨A, ht⟩, ?_⟩
  intro B hB hperiod
  exact hnone (cyclicStackProjection V q hq havoid B)
    (tiles_of_tiles_cyclicStackTile V q hq havoid hpart hfull hE hB)
    (fullyPeriodic_cyclicStackProjection V q hq havoid hperiod)

end FiniteFamily

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

open scoped BigOperators Classical

section

variable {V : Type uV} {C : Type uC} [Fintype V] [Fintype C] {k : ℕ}

noncomputable def allBadAssignments
    (pair : (Fin k × Fin 2) ↪ V) (Good : Fin k → Finset (C × C)) :
    Finset (V → C) := by
  classical
  exact Finset.univ.filter fun f =>
    ∀ j, (f (pair (j, 0)), f (pair (j, 1))) ∉ Good j

@[simp] theorem mem_allBadAssignments
    (pair : (Fin k × Fin 2) ↪ V) (Good : Fin k → Finset (C × C)) (f : V → C) :
    f ∈ allBadAssignments pair Good ↔
      ∀ j, (f (pair (j, 0)), f (pair (j, 1))) ∉ Good j := by
  classical
  simp [allBadAssignments]

private abbrev Outside (pair : (Fin k × Fin 2) ↪ V) :=
  {v : V // v ∉ Set.range pair}

private noncomputable def vertexDecomposition (pair : (Fin k × Fin 2) ↪ V) :
    ((Fin k × Fin 2) ⊕ Outside pair) ≃ V := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective pair pair.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range pair))

private theorem vertexDecomposition_inl {V : Type uV} [Fintype V] (pair : (Fin k × Fin 2) ↪ V)
    (x : Fin k × Fin 2) : vertexDecomposition pair (Sum.inl x) = pair x := rfl

private theorem outside_card (pair : (Fin k × Fin 2) ↪ V) :
    Fintype.card (Outside pair) = Fintype.card V - 2 * k := by
  classical
  have h := Fintype.card_congr (vertexDecomposition pair)
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at h
  omega

private def edgeAssignmentEquiv : ((Fin k × Fin 2) → C) ≃ (Fin k → C × C) where
  toFun f j := (f (j, 0), f (j, 1))
  invFun f x := if x.2 = 0 then (f x.1).1 else (f x.1).2
  left_inv f := by
    funext x
    rcases x with ⟨j, b⟩
    fin_cases b <;> simp
  right_inv f := by
    funext j
    simp

private noncomputable def assignmentDecomposition (pair : (Fin k × Fin 2) ↪ V) :
    (V → C) ≃ (Fin k → C × C) × (Outside pair → C) :=
  ((Equiv.arrowCongr (vertexDecomposition pair).symm (Equiv.refl C)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)).trans
    (Equiv.prodCongr edgeAssignmentEquiv (Equiv.refl _))

private theorem assignmentDecomposition_apply
    {V : Type uV} {C : Type uC} [Fintype V] [Fintype C] (pair : (Fin k × Fin 2) ↪ V)
    (f : V → C) (j : Fin k) :
    (assignmentDecomposition pair f).1 j = (f (pair (j, 0)), f (pair (j, 1))) := rfl

private def constrainedProductEquiv {ι : Type uι} {A : Type uA} {B : Type uB} (p : ι → A → Prop) :
    {x : (ι → A) × B // ∀ i, p i (x.1 i)} ≃ (∀ i, {a : A // p i a}) × B where
  toFun x := (fun i => ⟨x.1.1 i, x.2 i⟩, x.1.2)
  invFun x := ⟨(fun i => (x.1 i).1, x.2), fun i => (x.1 i).2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

private noncomputable def badAssignmentEquiv
    (pair : (Fin k × Fin 2) ↪ V) (Good : Fin k → Finset (C × C)) :
    {f : V → C // ∀ j, (f (pair (j, 0)), f (pair (j, 1))) ∉ Good j} ≃
      (∀ j : Fin k, {c : C × C // c ∉ Good j}) × (Outside pair → C) :=
  ((assignmentDecomposition pair).subtypeEquiv (fun _ => Iff.rfl)).trans
    (constrainedProductEquiv fun j c => c ∉ Good j)

theorem allBadAssignments_card
    (pair : (Fin k × Fin 2) ↪ V) (Good : Fin k → Finset (C × C)) :
    (allBadAssignments pair Good).card =
      (∏ j : Fin k, (Fintype.card C ^ 2 - (Good j).card)) *
        Fintype.card C ^ (Fintype.card V - 2 * k) := by
  classical
  have hbad : (allBadAssignments pair Good).card =
      Fintype.card {f : V → C // ∀ j, (f (pair (j, 0)), f (pair (j, 1))) ∉ Good j} := by
    rw [Fintype.card_subtype]
    rfl
  have hcolor (j : Fin k) : Fintype.card {c : C × C // c ∉ Good j} =
      Fintype.card C ^ 2 - (Good j).card := by
    rw [Fintype.card_subtype_compl]
    simp [Fintype.card_prod, pow_two]
  rw [hbad, Fintype.card_congr (badAssignmentEquiv pair Good), Fintype.card_prod,
    Fintype.card_pi, Fintype.card_fun, outside_card]
  simp_rw [hcolor]

theorem allBadAssignments_card_le
    (pair : (Fin k × Fin 2) ↪ V) (Good : Fin k → Finset (C × C)) (g : ℕ)
    (hgood : ∀ j, g ≤ (Good j).card) :
    (allBadAssignments pair Good).card ≤
      (Fintype.card C ^ 2 - g) ^ k * Fintype.card C ^ (Fintype.card V - 2 * k) := by
  classical
  rw [allBadAssignments_card]
  apply Nat.mul_le_mul_right
  calc
    (∏ j : Fin k, (Fintype.card C ^ 2 - (Good j).card)) ≤
        ∏ _j : Fin k, (Fintype.card C ^ 2 - g) :=
      Finset.prod_le_prod' (fun j _ => Nat.sub_le_sub_left (hgood j) _)
    _ = (Fintype.card C ^ 2 - g) ^ k := by simp

end

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree

def primeDifferencePairs (q m : ℕ) [Fact q.Prime]
    (hq : q = 2 * m + 1) (d : ZMod q) (hd : d ≠ 0) :
    (Fin m × Fin 2) ↪ ZMod q where
  toFun p := ((2 * p.1.val + p.2.val : ℕ) : ZMod q) * d
  inj' := by
    rintro ⟨j, b⟩ ⟨k, c⟩ h
    have hj := j.isLt
    have hk := k.isLt
    have hb := b.isLt
    have hc := c.isLt
    have hjb : 2 * j.val + b.val < q := by omega
    have hkc : 2 * k.val + c.val < q := by omega
    have hcast : ((2 * j.val + b.val : ℕ) : ZMod q) =
        ((2 * k.val + c.val : ℕ) : ZMod q) :=
      mul_right_cancel₀ hd h
    have hindices := congrArg ZMod.val hcast
    rw [ZMod.val_natCast_of_lt hjb, ZMod.val_natCast_of_lt hkc] at hindices
    apply Prod.ext
    · apply Fin.ext
      change j.val = k.val
      omega
    · apply Fin.ext
      change b.val = c.val
      omega

@[simp]
theorem primeDifferencePairs_apply (q m : ℕ) [Fact q.Prime]
    (hq : q = 2 * m + 1) (d : ZMod q) (hd : d ≠ 0)
    (j : Fin m) (b : Fin 2) :
    primeDifferencePairs q m hq d hd (j, b) =
      ((2 * j.val + b.val : ℕ) : ZMod q) * d := rfl

theorem primeDifferencePairs_step (q m : ℕ) [Fact q.Prime]
    (hq : q = 2 * m + 1) (d : ZMod q) (hd : d ≠ 0) (j : Fin m) :
    primeDifferencePairs q m hq d hd (j, 1) -
      primeDifferencePairs q m hq d hd (j, 0) = d := by
  change ((2 * j.val + 1 : ℕ) : ZMod q) * d -
    ((2 * j.val : ℕ) : ZMod q) * d = d
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_sub_cancel_left]

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree

open scoped BigOperators

private theorem binomial_two_terms_le (a m : ℕ) (hm : 2 ≤ m) :
    a ^ m + a ^ (m - 2) * m.choose 2 ≤ (1 + a) ^ m := by
  have hsub : ({0, 2} : Finset ℕ) ⊆ Finset.range (m + 1) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · simp only [Finset.mem_range]
      omega
    · simp only [Finset.mem_range]
      omega
  calc
    a ^ m + a ^ (m - 2) * m.choose 2 =
        ∑ k ∈ ({0, 2} : Finset ℕ), 1 ^ k * a ^ (m - k) * m.choose k := by
      simp
    _ ≤ ∑ k ∈ Finset.range (m + 1), 1 ^ k * a ^ (m - k) * m.choose k :=
      Finset.sum_le_sum_of_subset hsub
    _ = (1 + a) ^ m := (add_pow 1 a m).symm

theorem fullDifference_bad_bound (s m : ℕ) (hs : 2 ≤ s)
    (hm : 4 * s * (s ^ 2 - 1) ^ 2 + 1 ≤ m) :
    s * (2 * m) * (s ^ 2 - 1) ^ m < s ^ (2 * m) := by
  let a : ℕ := s ^ 2 - 1
  have hsquare : 4 ≤ s ^ 2 := by
    simpa using Nat.pow_le_pow_left hs 2
  have ha : 0 < a := by
    dsimp [a]
    omega
  have ha_succ : 1 + a = s ^ 2 := by
    dsimp [a]
    omega
  change 4 * s * a ^ 2 + 1 ≤ m at hm
  have hthreshold : 0 < 4 * s * a ^ 2 :=
    Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (pow_pos ha 2)
  have hm_two : 2 ≤ m := by omega
  have hpred : 4 * s * a ^ 2 ≤ m - 1 := by omega
  have hchoose : m.choose 2 * 2 = m * (m - 1) := by
    simpa using Nat.choose_succ_right_eq m 1
  have hdoubled : (2 * s * m * a ^ 2) * 2 ≤ m.choose 2 * 2 := by
    calc
      (2 * s * m * a ^ 2) * 2 = m * (4 * s * a ^ 2) := by ring
      _ ≤ m * (m - 1) := Nat.mul_le_mul_left m hpred
      _ = m.choose 2 * 2 := hchoose.symm
  have hcoefficient : 2 * s * m * a ^ 2 ≤ m.choose 2 := by
    omega
  have hpower : a ^ 2 * a ^ (m - 2) = a ^ m := by
    rw [← pow_add, Nat.add_sub_cancel' hm_two]
  have hterm : (2 * s * m) * a ^ m ≤ a ^ (m - 2) * m.choose 2 := by
    calc
      (2 * s * m) * a ^ m = a ^ (m - 2) * (2 * s * m * a ^ 2) := by
        rw [← hpower]
        ring
      _ ≤ a ^ (m - 2) * m.choose 2 :=
        Nat.mul_le_mul_left (a ^ (m - 2)) hcoefficient
  have hpositive : 0 < a ^ m := pow_pos ha m
  calc
    s * (2 * m) * (s ^ 2 - 1) ^ m = (2 * s * m) * a ^ m := by
      dsimp [a]
      ring
    _ < a ^ m + a ^ (m - 2) * m.choose 2 := by omega
    _ ≤ (1 + a) ^ m := binomial_two_terms_le a m hm_two
    _ = s ^ (2 * m) := by rw [ha_succ, ← pow_mul]

theorem fullDifference_bad_bound_poly (s m : ℕ) (hs : 2 ≤ s)
    (hm : 4 * s ^ 5 + 1 ≤ m) :
    s * (2 * m) * (s ^ 2 - 1) ^ m < s ^ (2 * m) := by
  apply fullDifference_bad_bound s m hs
  calc
    4 * s * (s ^ 2 - 1) ^ 2 + 1 ≤ 4 * s * (s ^ 2) ^ 2 + 1 :=
      Nat.add_le_add_right
        (Nat.mul_le_mul_left (4 * s) (Nat.pow_le_pow_left (Nat.sub_le _ _) 2)) 1
    _ = 4 * s ^ 5 + 1 := by ring
    _ ≤ m := hm

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

open Classical
open scoped BigOperators

abbrev Coloring (q s : ℕ) := ZMod q → Fin s

def BadDifference {q s : ℕ} (c : Coloring q s) (ν : Fin s) (d : ZMod q) : Prop :=
  ¬ ∃ x y, c x = ν ∧ c y = ν ∧ x - y = d

def badDifferenceColorings {q s : ℕ} [NeZero q]
    (ν : Fin s) (d : ZMod q) : Finset (Coloring q s) :=
  Finset.univ.filter (fun c => BadDifference c ν d)

@[simp]
theorem mem_badDifferenceColorings {q s : ℕ} [NeZero q]
    (c : Coloring q s) (ν : Fin s) (d : ZMod q) :
    c ∈ badDifferenceColorings ν d ↔ BadDifference c ν d := by
  simp [badDifferenceColorings]

theorem badDifference_card_le {q s m : ℕ} [Fact q.Prime]
    (hq : q = 2 * m + 1) (ν : Fin s) (d : ZMod q) (hd : d ≠ 0) :
    (badDifferenceColorings ν d).card ≤ s * (s ^ 2 - 1) ^ m := by
  let pair := primeDifferencePairs q m hq d hd
  let good : Fin m → Finset (Fin s × Fin s) := fun _ => {(ν, ν)}
  have hsub : badDifferenceColorings ν d ⊆ allBadAssignments pair good := by
    intro c hc
    apply (mem_allBadAssignments pair good c).mpr
    intro j hj
    have heq : (c (pair (j, 0)), c (pair (j, 1))) = (ν, ν) :=
      Finset.mem_singleton.mp hj
    apply (mem_badDifferenceColorings c ν d).mp hc
    refine ⟨pair (j, 1), pair (j, 0), congrArg Prod.snd heq,
      congrArg Prod.fst heq, ?_⟩
    exact primeDifferencePairs_step q m hq d hd j
  have hleft : q - 2 * m = 1 := by omega
  calc
    (badDifferenceColorings ν d).card ≤ (allBadAssignments pair good).card :=
      Finset.card_le_card hsub
    _ ≤ (Fintype.card (Fin s) ^ 2 - 1) ^ m *
        Fintype.card (Fin s) ^ (Fintype.card (ZMod q) - 2 * m) :=
      allBadAssignments_card_le pair good 1 (by intro j; simp [good])
    _ = s * (s ^ 2 - 1) ^ m := by
      simp only [Fintype.card_fin, ZMod.card, hleft, pow_one]
      exact Nat.mul_comm _ _

def badDifferenceLabels (q s : ℕ) [NeZero q] : Finset (Fin s × ZMod q) :=
  Finset.univ.product ((Finset.univ : Finset (ZMod q)).erase 0)

@[simp]
theorem badDifferenceLabels_card (q s : ℕ) [NeZero q] :
    (badDifferenceLabels q s).card = s * (q - 1) := by
  simp [badDifferenceLabels, ZMod.card]

def someBadDifferenceColorings (q s : ℕ) [NeZero q] : Finset (Coloring q s) :=
  (badDifferenceLabels q s).biUnion (fun p => badDifferenceColorings p.1 p.2)

theorem someBadDifferenceColorings_card_le {q s m : ℕ} [Fact q.Prime]
    (hq : q = 2 * m + 1) :
    (someBadDifferenceColorings q s).card ≤
      (s * (q - 1)) * (s * (s ^ 2 - 1) ^ m) := by
  calc
    (someBadDifferenceColorings q s).card ≤
        ∑ p ∈ badDifferenceLabels q s, (badDifferenceColorings p.1 p.2).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ badDifferenceLabels q s, s * (s ^ 2 - 1) ^ m := by
      apply Finset.sum_le_sum
      intro p hp
      have hd : p.2 ≠ 0 := (Finset.mem_erase.mp (Finset.mem_product.mp hp).2).1
      exact badDifference_card_le hq p.1 p.2 hd
    _ = (s * (q - 1)) * (s * (s ^ 2 - 1) ^ m) := by
      rw [Finset.sum_const, nsmul_eq_mul, badDifferenceLabels_card, Nat.cast_id]

theorem exists_coloring_nonzero_differences {q s m : ℕ} [Fact q.Prime]
    (hs : 2 ≤ s) (hq : q = 2 * m + 1) (hm : 4 * s ^ 5 + 1 ≤ m) :
    ∃ c : Coloring q s, ∀ ν d, d ≠ 0 →
      ∃ x y, c x = ν ∧ c y = ν ∧ x - y = d := by
  have hspos : 0 < s := by omega
  have hstrict := Nat.mul_lt_mul_of_pos_left
    (fullDifference_bad_bound_poly s m hs hm) hspos
  have hcard : (someBadDifferenceColorings q s).card <
      (Finset.univ : Finset (Coloring q s)).card := by
    calc
      (someBadDifferenceColorings q s).card ≤
          (s * (q - 1)) * (s * (s ^ 2 - 1) ^ m) :=
        someBadDifferenceColorings_card_le hq
      _ = s * (s * (2 * m) * (s ^ 2 - 1) ^ m) := by
        rw [hq]
        simp only [Nat.add_sub_cancel]
        ring
      _ < s * s ^ (2 * m) := hstrict
      _ = (Finset.univ : Finset (Coloring q s)).card := by
        simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card]
        rw [hq, pow_succ]
        exact Nat.mul_comm _ _
  obtain ⟨c, _hc, hgood⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨c, ?_⟩
  intro ν d hd
  by_contra hbad
  apply hgood
  apply Finset.mem_biUnion.mpr
  refine ⟨(ν, d), ?_, ?_⟩
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_univ _, Finset.mem_erase.mpr ⟨hd, Finset.mem_univ _⟩⟩
  · exact (mem_badDifferenceColorings c ν d).mpr hbad

theorem exists_partition_of_nonzero_coloring {q s : ℕ} [Fact q.Prime]
    (c : Coloring q s)
    (hc : ∀ ν d, d ≠ 0 → ∃ x y, c x = ν ∧ c y = ν ∧ x - y = d) :
    ∃ E : Fin s → Finset (ZMod q),
      (∀ ν, (E ν).Nonempty) ∧
      (∀ x, ∃! ν, x ∈ E ν) ∧
      (∀ ν d, ∃ x ∈ E ν, ∃ y ∈ E ν, x - y = d) := by
  let E : Fin s → Finset (ZMod q) :=
    fun ν => Finset.univ.filter (fun x => c x = ν)
  have hne : ∀ ν, (E ν).Nonempty := by
    intro ν
    obtain ⟨x, _y, hx, _hy, _hxy⟩ := hc ν 1 one_ne_zero
    exact ⟨x, by simp [E, hx]⟩
  refine ⟨E, hne, ?_, ?_⟩
  · intro x
    refine ⟨c x, by simp [E], ?_⟩
    intro ν hν
    exact (Finset.mem_filter.mp hν).2.symm
  · intro ν d
    by_cases hd : d = 0
    · subst d
      obtain ⟨x, hx⟩ := hne ν
      exact ⟨x, hx, x, hx, sub_self x⟩
    · obtain ⟨x, y, hx, hy, hxy⟩ := hc ν d hd
      exact ⟨x, by simp [E, hx], y, by simp [E, hy], hxy⟩

theorem exists_fresh_prime_fullDifference_partition
    (s : ℕ) (hs : 0 < s) (forbidden : Finset ℕ) (lower : ℕ) :
    ∃ q : ℕ, q.Prime ∧ lower < q ∧ q ∉ forbidden ∧
      ∃ E : Fin s → Finset (ZMod q),
        (∀ ν, (E ν).Nonempty) ∧
        (∀ x, ∃! ν, x ∈ E ν) ∧
        (∀ ν d, ∃ x ∈ E ν, ∃ y ∈ E ν, x - y = d) := by
  let N := max (8 * s ^ 5 + 3) (max (lower + 1) (forbidden.sup id + 1))
  obtain ⟨q, hqN, hprime⟩ := Nat.exists_infinite_primes N
  have hqbig : 8 * s ^ 5 + 3 ≤ q := (le_max_left _ _).trans hqN
  have hqrest : max (lower + 1) (forbidden.sup id + 1) ≤ q :=
    (le_max_right _ _).trans hqN
  have hqlower : lower + 1 ≤ q := (le_max_left _ _).trans hqrest
  have hqforbidden : forbidden.sup id + 1 ≤ q := (le_max_right _ _).trans hqrest
  have hfresh : q ∉ forbidden := by
    intro hmem
    have hsup : q ≤ forbidden.sup id := Finset.le_sup (f := id) hmem
    omega
  have hq2 : 2 < q := by omega
  let : Fact q.Prime := ⟨hprime⟩
  refine ⟨q, hprime, by omega, hfresh, ?_⟩
  by_cases hs1 : s = 1
  · subst s
    let c : Coloring q 1 := fun _ => 0
    apply exists_partition_of_nonzero_coloring c
    intro ν d _hd
    have hν : (0 : Fin 1) = ν := Subsingleton.elim _ _
    exact ⟨d, 0, hν, hν, sub_zero d⟩
  · have hs2 : 2 ≤ s := by omega
    have hodd : q % 2 = 1 := hprime.eq_two_or_odd.resolve_left (by omega)
    let m := q / 2
    have hqm : q = 2 * m + 1 := by dsimp [m]; omega
    have hm : 4 * s ^ 5 + 1 ≤ m := by dsimp [m]; omega
    obtain ⟨c, hc⟩ := exists_coloring_nonzero_differences hs2 hqm hm
    exact exists_partition_of_nonzero_coloring c hc

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

theorem exists_cyclic_stack_of_system
    {ι : Type uι} [Fintype ι] [Nonempty ι]
    (V : Type uV) [AddCommGroup V] [Finite V] [IsAddCyclic V]
    (F : ι → Finset (Plane × V))
    (hcommon : ∃ A, ∀ ν, Tiles (F ν) A)
    (hnone : ∀ A, (∀ ν, Tiles (F ν) A) → ¬ FullyPeriodic A) :
    ∃ Q : ℕ, 0 < Q ∧
      ∃ T : Finset (Plane × ZMod Q), T.Nonempty ∧
        (∃ B, Tiles T B) ∧ ∀ B, Tiles T B → ¬ FullyPeriodic B := by
  classical
  let s := Fintype.card ι
  have hs : 0 < s := Fintype.card_pos
  let e : ι ≃ Fin s := Fintype.equivFin ι
  let F' : Fin s → Finset (Plane × V) := fun ν => F (e.symm ν)
  have hcommon' : ∃ A, ∀ ν, Tiles (F' ν) A := by
    obtain ⟨A, hA⟩ := hcommon
    exact ⟨A, fun ν => hA (e.symm ν)⟩
  have hnone' : ∀ A, (∀ ν, Tiles (F' ν) A) → ¬ FullyPeriodic A := by
    intro A hA
    apply hnone A
    intro ν
    simpa only [F', Equiv.symm_apply_apply] using hA (e ν)
  obtain ⟨q, hq, hcard, _hfresh, E, hE, hpart, hfull⟩ :=
    exists_fresh_prime_fullDifference_partition s hs ∅ (Nat.card V)
  let havoid : ¬ q ∣ Nat.card V := not_dvd_card_of_lt V hcard
  have hc := cyclicStack_counterexample_of_common_system V q hq havoid
    (F := F') (E := E) hpart hfull hE hcommon' hnone'
  refine ⟨q * Nat.card V, cyclicStackOrder_pos V q hq,
    cyclicStackTile V q hq havoid F' E, hc.1, ?_, hc.2.2⟩
  obtain ⟨A, hA⟩ := hc.2.1
  exact ⟨cyclicStackComplement V q hq havoid A, hA⟩

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree

theorem cyclic_counterexample_of_parameters {p : ℕ} [NeZero p]
    (E : EncodingParameters p) :
    ∃ Q : ℕ, 0 < Q ∧
      ∃ F : Finset (Plane × ZMod Q), F.Nonempty ∧
        (∃ A, Tiles F A) ∧ ∀ A, Tiles F A → ¬ FullyPeriodic A := by
  classical
  let : IsAddCyclic (V E) := isAddCyclic_of_surjective
    (finiteFactorEquiv E).symm (finiteFactorEquiv E).symm.surjective
  apply exists_cyclic_stack_of_system (V E) (testTile E)
  · exact ⟨CommonModel.commonGraph E, CommonModel.commonGraph_tiles_testTile E⟩
  · intro A hA
    exact testTile_not_fully_periodic E hA

theorem exists_cyclic_counterexample :
    ∃ Q : ℕ, 0 < Q ∧
      ∃ F : Finset (Plane × ZMod Q), F.Nonempty ∧
        (∃ A, Tiles F A) ∧ ∀ A, Tiles F A → ¬ FullyPeriodic A := by
  obtain ⟨p, hpbound, hp⟩ := Nat.exists_infinite_primes 201
  let : NeZero p := ⟨hp.ne_zero⟩
  let E : EncodingParameters p := encodingParameters hp (by omega)
  exact cyclic_counterexample_of_parameters E

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

variable {G : Type uG} [AddCommGroup G] [DecidableEq G]

theorem Tiles.translate_tile {F : Finset G} {A : Set G}
    (h : Tiles F A) (v : G) : Tiles (F.image (fun f => f + v)) A := by
  classical
  apply tiles_iff_unique_tile.mpr
  intro x
  obtain ⟨f, hf, huniq⟩ := tiles_iff_unique_tile.mp h (x - v)
  refine ⟨⟨(f : G) + v, Finset.mem_image.mpr ⟨f, f.property, rfl⟩⟩, ?_, ?_⟩
  · change x - ((f : G) + v) ∈ A
    have heq : x - ((f : G) + v) = x - v - (f : G) := by abel
    rw [heq]
    exact hf
  · intro g hg
    obtain ⟨f', hf', hfg⟩ := Finset.mem_image.mp g.property
    have heq : x - (f' + v) = x - v - f' := by abel
    change x - (g : G) ∈ A at hg
    rw [← hfg, heq] at hg
    have hff : (⟨f', hf'⟩ : ↥F) = f := huniq _ hg
    apply Subtype.ext
    change (g : G) = (f : G) + v
    rw [← hfg]
    exact congrArg (fun z : G => z + v) (congrArg Subtype.val hff)

theorem tiles_translate_tile_iff (F : Finset G) (A : Set G) (v : G) :
    Tiles (F.image (fun f => f + v)) A ↔ Tiles F A := by
  constructor
  · intro h
    have h' := h.translate_tile (-v)
    simpa only [Finset.image_image, Function.comp_def, add_neg_cancel_right, Finset.image_id'] using h'
  · intro h
    exact h.translate_tile v

theorem exists_zero_mem_normalization (F : Finset G) (hF : F.Nonempty)
    (htile : ∃ A, Tiles F A)
    (haperiodic : ∀ A, Tiles F A → ¬ FullyPeriodic A) :
    ∃ U : Finset G, 0 ∈ U ∧
      (∃ A, Tiles U A) ∧ (∀ A, Tiles U A → ¬ FullyPeriodic A) := by
  classical
  obtain ⟨f0, hf0⟩ := hF
  refine ⟨F.image (fun f => f + -f0), ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨f0, hf0, add_neg_cancel f0⟩
  · obtain ⟨A, hA⟩ := htile
    exact ⟨A, hA.translate_tile (-f0)⟩
  · intro A hA
    exact haperiodic A ((tiles_translate_tile_iff F A (-f0)).mp hA)

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree

abbrev Residue3 (m : ℕ) := Fin 3 → ZMod m
abbrev LiftAlphabet := Fin 3 → Fin 5
abbrev LiftAssignment (m : ℕ) := Residue3 m → LiftAlphabet

def residueMod (m : ℕ) (d : Lattice 3) : Residue3 m := fun i => (d i : ZMod m)

def can {m : ℕ} (v : Residue3 m) : Lattice 3 := fun i => ((v i).val : ℤ)

def signed (h : LiftAlphabet) : Lattice 3 := fun i => (h i).val - (2 : ℤ)

def representative (m : ℕ) [NeZero m] (ω : LiftAssignment m)
    (v : Residue3 m) : Lattice 3 :=
  fun i => can v i + (m : ℤ) * signed (ω v) i

@[simp] theorem residueMod_can {m : ℕ} [NeZero m] (v : Residue3 m) :
    residueMod m (can v) = v := by
  funext i
  simp [residueMod, can]

@[simp] theorem representative_residue (m : ℕ) [NeZero m]
    (ω : LiftAssignment m) (v : Residue3 m) :
    residueMod m (representative m ω v) = v := by
  funext i
  simp [residueMod, representative, can]

theorem representative_injective (m : ℕ) [NeZero m] (ω : LiftAssignment m) :
    Function.Injective (representative m ω) := by
  intro u v huv
  have h := congrArg (residueMod m) huv
  simpa only [representative_residue] using h

theorem can_nonneg {m : ℕ} (v : Residue3 m) (i : Fin 3) : 0 ≤ can v i := by
  dsimp only [can]
  exact_mod_cast (Nat.zero_le (v i).val)

theorem can_lt {m : ℕ} [NeZero m] (v : Residue3 m) (i : Fin 3) :
    can v i < (m : ℤ) := by
  dsimp only [can]
  exact_mod_cast (v i).val_lt

theorem signed_bounds (h : LiftAlphabet) (i : Fin 3) :
    -2 ≤ signed h i ∧ signed h i ≤ 2 := by
  have hi := (h i).isLt
  dsimp [signed]
  omega

def Requested (m : ℕ) (d : Lattice 3) : Prop :=
  (∀ i, |d i| ≤ (m : ℤ)) ∧ ¬ ∀ i, (m : ℤ) ∣ d i

noncomputable def requestedVectors (m : ℕ) : Finset (Lattice 3) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(m : ℤ)) (m : ℤ))).filter
    (fun d => ¬ ∀ i, (m : ℤ) ∣ d i)

@[simp] theorem mem_requestedVectors {m : ℕ} {d : Lattice 3} :
    d ∈ requestedVectors m ↔ Requested m d := by
  classical
  simp only [requestedVectors, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_Icc, Requested, abs_le]

theorem card_requestedVectors_le (m : ℕ) :
    (requestedVectors m).card ≤ (2 * m + 1) ^ 3 := by
  classical
  have hc : (Finset.Icc (-(m : ℤ)) (m : ℤ)).card = 2 * m + 1 := by
    rw [Int.card_Icc]
    omega
  calc
    (requestedVectors m).card ≤
        (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(m : ℤ)) (m : ℤ))).card :=
      Finset.card_filter_le _ _
    _ = (2 * m + 1) ^ 3 := by rw [Fintype.card_piFinset_const, hc]

theorem requested_residueMod_ne_zero {m : ℕ} {d : Lattice 3}
    (hd : Requested m d) : residueMod m d ≠ 0 := by
  intro h
  apply hd.2
  intro i
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (d i) m).mp
  exact congrFun h i

theorem requested_successor_ne {m : ℕ} {d : Lattice 3}
    (hd : Requested m d) (u : Residue3 m) : u + residueMod m d ≠ u := by
  intro h
  apply requested_residueMod_ne_zero hd
  apply add_left_cancel (a := u)
  simpa using h

theorem card_residue3 (m : ℕ) [NeZero m] : Fintype.card (Residue3 m) = m ^ 3 := by
  simp [Residue3]

theorem card_liftAlphabet : Fintype.card LiftAlphabet = 125 := by
  norm_num [LiftAlphabet]

theorem card_liftAlphabet_pairs : Fintype.card (LiftAlphabet × LiftAlphabet) = 15625 := by
  norm_num [Fintype.card_prod, card_liftAlphabet]

def liftDifference (m : ℕ) (d : Lattice 3) (u v : Residue3 m) : Lattice 3 :=
  fun i => (d i - (can v i - can u i)) / (m : ℤ)

theorem liftDifference_eq {m : ℕ} [NeZero m] {d : Lattice 3} {u v : Residue3 m}
    (hv : v = u + residueMod m d) (i : Fin 3) :
    (m : ℤ) * liftDifference m d u v i = d i - (can v i - can u i) := by
  apply Int.mul_ediv_cancel'
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp
  have hvi := congrFun hv i
  change v i = u i + (d i : ZMod m) at hvi
  simp only [Int.cast_sub, can, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [hvi]
  ring

theorem liftDifference_bounds {m : ℕ} [NeZero m] {d : Lattice 3} {u v : Residue3 m}
    (hd : Requested m d) (hv : v = u + residueMod m d) (i : Fin 3) :
    -1 ≤ liftDifference m d u v i ∧ liftDifference m d u v i ≤ 1 := by
  have hm : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hdu := (abs_le.mp (hd.1 i)).1
  have hdv := (abs_le.mp (hd.1 i)).2
  have hu0 := can_nonneg u i
  have hv0 := can_nonneg v i
  have hum := can_lt u i
  have hvm := can_lt v i
  have heq := liftDifference_eq hv i
  constructor
  · by_contra h
    have hz : liftDifference m d u v i ≤ -2 := by omega
    have hmz := mul_le_mul_of_nonneg_left hz (le_of_lt hm)
    nlinarith
  · by_contra h
    have hz : 2 ≤ liftDifference m d u v i := by omega
    have hmz := mul_le_mul_of_nonneg_left hz (le_of_lt hm)
    nlinarith

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

noncomputable def PairGood (m : ℕ) (d : Lattice 3) (u v : Residue3 m) :
    Finset (LiftAlphabet × LiftAlphabet) := by
  classical
  exact Finset.univ.filter (fun p => ∀ i,
    can v i + (m : ℤ) * signed p.2 i - (can u i + (m : ℤ) * signed p.1 i) = d i)

@[simp] theorem mem_PairGood {m : ℕ} {d : Lattice 3} {u v : Residue3 m}
    {p : LiftAlphabet × LiftAlphabet} :
    p ∈ PairGood m d u v ↔ ∀ i,
      can v i + (m : ℤ) * signed p.2 i - (can u i + (m : ℤ) * signed p.1 i) = d i := by
  classical
  simp only [PairGood, Finset.mem_filter, Finset.mem_univ, true_and]

theorem pairGood_assignment_iff {m : ℕ} [NeZero m] {d : Lattice 3}
    (ω : LiftAssignment m) (u v : Residue3 m) :
    (ω u, ω v) ∈ PairGood m d u v ↔ representative m ω v - representative m ω u = d := by
  rw [mem_PairGood, funext_iff]
  rfl

private def coordinateLiftPair (z : ℤ) (hz : -2 ≤ z ∧ z ≤ 2) (j : Fin 3) :
    Fin 5 × Fin 5 :=
  (⟨j.val + (-z).toNat, by have hj := j.isLt; omega⟩,
   ⟨j.val + z.toNat, by have hj := j.isLt; omega⟩)

private theorem coordinateLiftPair_difference (z : ℤ) (hz : -2 ≤ z ∧ z ≤ 2)
    (j : Fin 3) :
    ((coordinateLiftPair z hz j).2.val : ℤ) - (coordinateLiftPair z hz j).1.val = z := by
  dsimp [coordinateLiftPair]
  omega

private theorem coordinateLiftPair_injective (z : ℤ) (hz : -2 ≤ z ∧ z ≤ 2) :
    Function.Injective (coordinateLiftPair z hz) := by
  intro a b hab
  apply Fin.ext
  have h := congrArg (fun p : Fin 5 × Fin 5 => p.1.val) hab
  dsimp [coordinateLiftPair] at h
  exact Nat.add_right_cancel h

private def liftPairForDifference (z : Lattice 3) (hz : ∀ i, -2 ≤ z i ∧ z i ≤ 2)
    (a : Fin 3 → Fin 3) : LiftAlphabet × LiftAlphabet :=
  (fun i => (coordinateLiftPair (z i) (hz i) (a i)).1,
   fun i => (coordinateLiftPair (z i) (hz i) (a i)).2)

private theorem liftPairForDifference_injective (z : Lattice 3)
    (hz : ∀ i, -2 ≤ z i ∧ z i ≤ 2) : Function.Injective (liftPairForDifference z hz) := by
  intro a b hab
  funext i
  apply coordinateLiftPair_injective (z i) (hz i)
  apply Prod.ext
  · exact congrArg (fun p : LiftAlphabet × LiftAlphabet => p.1 i) hab
  · exact congrArg (fun p : LiftAlphabet × LiftAlphabet => p.2 i) hab

private theorem liftPairForDifference_signed_sub (z : Lattice 3)
    (hz : ∀ i, -2 ≤ z i ∧ z i ≤ 2) (a : Fin 3 → Fin 3) (i : Fin 3) :
    signed (liftPairForDifference z hz a).2 i -
      signed (liftPairForDifference z hz a).1 i = z i := by
  have h := coordinateLiftPair_difference (z i) (hz i) (a i)
  dsimp [signed, liftPairForDifference]
  omega

private theorem card_le_finset_of_injective {A : Type uA} {B : Type uB} [Fintype A]
    (s : Finset B) (f : A → B) (hfinj : Function.Injective f)
    (hmem : ∀ a, f a ∈ s) : Fintype.card A ≤ s.card := by
  classical
  let g : A → ↥s := fun a => ⟨f a, hmem a⟩
  have hginj : Function.Injective g := by
    intro a b hab
    exact hfinj (congrArg Subtype.val hab)
  have hc := Fintype.card_le_of_injective g hginj
  simpa only [Fintype.card_coe] using hc

theorem card_PairGood_ge {m : ℕ} [NeZero m] {d : Lattice 3} {u v : Residue3 m}
    (hd : Requested m d) (hv : v = u + residueMod m d) :
    27 ≤ (PairGood m d u v).card := by
  classical
  let z := liftDifference m d u v
  have hz : ∀ i, -2 ≤ z i ∧ z i ≤ 2 := by
    intro i
    have h := liftDifference_bounds hd hv i
    change -2 ≤ liftDifference m d u v i ∧ liftDifference m d u v i ≤ 2
    omega
  let f : (Fin 3 → Fin 3) → LiftAlphabet × LiftAlphabet := liftPairForDifference z hz
  have hfinj : Function.Injective f := liftPairForDifference_injective z hz
  have hf : ∀ a, f a ∈ PairGood m d u v := by
    intro a
    rw [mem_PairGood]
    intro i
    have hdiff := liftPairForDifference_signed_sub z hz a i
    have hcarry := liftDifference_eq hv i
    change (m : ℤ) * z i = d i - (can v i - can u i) at hcarry
    change can v i + (m : ℤ) * signed (liftPairForDifference z hz a).2 i -
      (can u i + (m : ℤ) * signed (liftPairForDifference z hz a).1 i) = d i
    rw [← hdiff] at hcarry
    nlinarith
  generalize hS : PairGood m d u v = S at hf ⊢
  have hc : Fintype.card (Fin 3 → Fin 3) ≤ S.card :=
    card_le_finset_of_injective S f hfinj hf
  have h27 : Fintype.card (Fin 3 → Fin 3) = 27 := by norm_num
  rwa [h27] at hc

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree

theorem one_sub_pow_mul_linear_le_one (c : ℚ) (_hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (r : ℕ) : (1 - c) ^ r * (1 + (r : ℚ) * c) ≤ 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hstep : (1 - c) * (1 + ((r : ℚ) + 1) * c) ≤ 1 + (r : ℚ) * c := by
        calc
          (1 - c) * (1 + ((r : ℚ) + 1) * c) =
              (1 + (r : ℚ) * c) - ((r : ℚ) + 1) * c ^ 2 := by ring
          _ ≤ 1 + (r : ℚ) * c :=
            sub_le_self _ (mul_nonneg (add_nonneg (Nat.cast_nonneg r) zero_le_one)
              (sq_nonneg c))
      calc
        (1 - c) ^ (r + 1) * (1 + ((r + 1 : ℕ) : ℚ) * c) =
            (1 - c) ^ r * ((1 - c) * (1 + ((r : ℚ) + 1) * c)) := by
              rw [pow_succ, Nat.cast_add, Nat.cast_one]
              ring
        _ ≤ (1 - c) ^ r * (1 + (r : ℚ) * c) :=
          mul_le_mul_of_nonneg_left hstep (pow_nonneg (sub_nonneg.mpr hc1) r)
        _ ≤ 1 := ih

private theorem scalar_half_bound (x c : ℚ) (hx : 0 ≤ x)
    (hc : (1 : ℚ) / 1000 ≤ c) (h : x * (1 + 1000 * c) ≤ 1) : x ≤ 1 / 2 := by
  have htwo : (2 : ℚ) ≤ 1 + 1000 * c := by linarith only [hc]
  apply (le_div_iff₀ (by norm_num : (0 : ℚ) < 2)).mpr
  exact (mul_le_mul_of_nonneg_left htwo hx).trans h

theorem residue_block_bound (c : ℚ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hc : (1 : ℚ) / 1000 ≤ c) : (1 - c) ^ 1000 ≤ 1 / 2 := by
  apply scalar_half_bound ((1 - c) ^ 1000) c
    (pow_nonneg (sub_nonneg.mpr hc1) 1000) hc
  exact one_sub_pow_mul_linear_le_one c hc0 hc1 1000

theorem residue_failure_block_bound : ((15598 : ℚ) / 15625) ^ 1000 ≤ 1 / 2 := by
  have h := residue_block_bound ((27 : ℚ) / 15625) (by norm_num)
    (by norm_num) (by norm_num)
  have heq : (1 : ℚ) - 27 / 15625 = 15598 / 15625 := by norm_num
  rw [heq] at h
  exact h

private theorem union_bound_from_block (p : ℚ) (hp : 0 ≤ p)
    (hblock : p ^ 1000 ≤ 1 / 2) : (129 : ℚ) ^ 3 * p ^ 32000 < 1 := by
  have hblocks : p ^ 32000 ≤ ((1 : ℚ) / 2) ^ 32 := by
    rw [show (32000 : ℕ) = 1000 * 32 by norm_num, pow_mul]
    exact pow_le_pow_left₀ (a := p ^ 1000) (b := (1 : ℚ) / 2)
      (pow_nonneg hp 1000) hblock 32
  calc
    (129 : ℚ) ^ 3 * p ^ 32000 ≤
        (129 : ℚ) ^ 3 * ((1 : ℚ) / 2) ^ 32 :=
      mul_le_mul_of_nonneg_left hblocks (by norm_num)
    _ < 1 := by norm_num

theorem residue_union_bound_32000 :
    (129 : ℚ) ^ 3 * ((15598 : ℚ) / 15625) ^ 32000 < 1 := by
  exact union_bound_from_block ((15598 : ℚ) / 15625) (by norm_num)
    residue_failure_block_bound

theorem residue_union_bound_of_large_exponent {k : ℕ} (hk : 32000 ≤ k) :
    (129 : ℚ) ^ 3 * ((15598 : ℚ) / 15625) ^ k < 1 := by
  apply lt_of_le_of_lt _ residue_union_bound_32000
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk) (by norm_num)

theorem residue_cube_64 : (64 : ℕ) ^ 3 = 262144 := by norm_num

theorem residue_matching_budget_64 : 32000 ≤ (64 : ℕ) ^ 3 / 3 - 1 := by
  norm_num

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

private theorem exists_successor_anchors {V : Type uV} [Fintype V] [DecidableEq V]
    (τ : Equiv.Perm V) (hτ : ∀ v, τ v ≠ v) (marked : V) (k : ℕ)
    (hcard : 3 * (k + 1) ≤ Fintype.card V) :
    ∃ M : Finset V, M.card = k ∧
      (∀ u ∈ M, u ≠ marked ∧ τ u ≠ marked) ∧
      ∀ u ∈ M, ∀ v ∈ M, u ≠ τ v := by
  revert hcard
  induction k with
  | zero =>
      intro _
      refine ⟨∅, rfl, ?_, ?_⟩ <;> simp
  | succ k ih =>
      intro hcard
      obtain ⟨M, hM, hmarked, hseparated⟩ := ih (by omega)
      let B : Finset V := insert marked (insert (τ.symm marked)
        ((M ∪ M.image τ) ∪ M.image τ.symm))
      have hB : B.card ≤ 3 * k + 2 := by
        have hi₁ : (M.image τ).card ≤ M.card := Finset.card_image_le
        have hi₂ : (M.image τ.symm).card ≤ M.card := Finset.card_image_le
        have hu₁ := Finset.card_union_le M (M.image τ)
        have hu₂ := Finset.card_union_le (M ∪ M.image τ) (M.image τ.symm)
        have ha₁ := Finset.card_insert_le (τ.symm marked)
          ((M ∪ M.image τ) ∪ M.image τ.symm)
        have ha₂ := Finset.card_insert_le marked (insert (τ.symm marked)
          ((M ∪ M.image τ) ∪ M.image τ.symm))
        dsimp only [B]
        omega
      have hBlt : B.card < (Finset.univ : Finset V).card := by
        rw [Finset.card_univ]
        omega
      obtain ⟨x, _, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hBlt
      have hxM : x ∉ M := by
        intro h
        exact hx (by simp [B, h])
      have hximage : x ∉ M.image τ := by
        intro h
        exact hx (by simp [B, h])
      have hxpreimage : x ∉ M.image τ.symm := by
        intro h
        exact hx (by simp [B, h])
      have hxmarked : x ≠ marked := by
        intro h
        exact hx (by simp [B, h])
      have hτxmarked : τ x ≠ marked := by
        intro h
        have he : x = τ.symm marked := by
          rw [← h]
          exact (τ.symm_apply_apply x).symm
        exact hx (by simp [B, he])
      refine ⟨insert x M, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hxM, hM]
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact ⟨hxmarked, hτxmarked⟩
        · exact hmarked u hu
      · intro u hu v hv
        rcases Finset.mem_insert.mp hu with hux | huM
        · subst u
          rcases Finset.mem_insert.mp hv with hvx | hvM
          · subst v
            exact (hτ x).symm
          · intro he
            exact hximage (Finset.mem_image.mpr ⟨v, hvM, he.symm⟩)
        · rcases Finset.mem_insert.mp hv with hvx | hvM
          · subst v
            intro he
            apply hxpreimage
            refine Finset.mem_image.mpr ⟨u, huM, ?_⟩
            rw [he, τ.symm_apply_apply]
          · exact hseparated u huM v hvM

theorem exists_disjoint_successor_pairs {V : Type uV} [Fintype V]
    (τ : Equiv.Perm V) (hτ : ∀ v, τ v ≠ v) (marked : V) (k : ℕ)
    (hcard : 3 * (k + 1) ≤ Fintype.card V) :
    ∃ pair : (Fin k × Fin 2) ↪ V,
      (∀ j, pair (j, 1) = τ (pair (j, 0))) ∧ ∀ x, pair x ≠ marked := by
  classical
  obtain ⟨M, hM, hmarked, hseparated⟩ :=
    exists_successor_anchors τ hτ marked k hcard
  let e : Fin k ≃ ↥M := (Finset.equivFinOfCardEq hM).symm
  let a : Fin k → V := fun j => (e j : V)
  have ha : Function.Injective a := by
    intro i j h
    apply e.injective
    exact Subtype.ext h
  have hamem (j : Fin k) : a j ∈ M := (e j).property
  let f : Fin k × Fin 2 → V :=
    fun p => if p.2 = 0 then a p.1 else τ (a p.1)
  have hf : Function.Injective f := by
    rintro ⟨i, b⟩ ⟨j, c⟩ h
    fin_cases b <;> fin_cases c
    · have hij : i = j := ha (by simpa [f] using h)
      cases hij
      rfl
    · exact False.elim (hseparated (a i) (hamem i) (a j) (hamem j)
        (by simpa [f] using h))
    · exact False.elim (hseparated (a j) (hamem j) (a i) (hamem i)
        (by simpa [f] using h.symm))
    · have hij : i = j := ha (τ.injective (by simpa [f] using h))
      cases hij
      rfl
  refine ⟨⟨f, hf⟩, ?_, ?_⟩
  · intro j
    simp [f]
  · rintro ⟨j, b⟩
    fin_cases b
    · simpa [f] using (hmarked (a j) (hamem j)).1
    · simpa [f] using (hmarked (a j) (hamem j)).2

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

open scoped Classical

theorem allBadAssignments_card_ratio_le {V : Type uV} {C : Type uC} [Fintype V] [Fintype C]
    {k : ℕ} (pair : (Fin k × Fin 2) ↪ V) (Good : Fin k → Finset (C × C))
    (g : ℕ) (hC : 0 < Fintype.card C) (hgB : g ≤ Fintype.card C ^ 2)
    (hgood : ∀ j, g ≤ (Good j).card) :
    ((allBadAssignments pair Good).card : ℚ) / (Fintype.card (V → C) : ℚ) ≤
      (1 - (g : ℚ) / (Fintype.card C : ℚ) ^ 2) ^ k := by
  let B : ℚ := Fintype.card C
  let N : ℕ := Fintype.card V
  have hBpos : 0 < B := Nat.cast_pos.mpr hC
  have hBne : B ≠ 0 := ne_of_gt hBpos
  have hdim : 2 * k ≤ N := by
    have h := Fintype.card_le_of_embedding pair
    simpa only [Fintype.card_prod, Fintype.card_fin, mul_comm, N] using h
  have hcast : ((allBadAssignments pair Good).card : ℚ) ≤
      (B ^ 2 - (g : ℚ)) ^ k * B ^ (N - 2 * k) := by
    have h := (Nat.cast_le (α := ℚ)).mpr
      (allBadAssignments_card_le pair Good g hgood)
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hgB, B, N] using h
  have hsplit : B ^ N = (B ^ 2) ^ k * B ^ (N - 2 * k) := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_of_le hdim]
  rw [Fintype.card_fun, Nat.cast_pow]
  change ((allBadAssignments pair Good).card : ℚ) / B ^ N ≤
    (1 - (g : ℚ) / B ^ 2) ^ k
  calc
    ((allBadAssignments pair Good).card : ℚ) / B ^ N
        ≤ ((B ^ 2 - (g : ℚ)) ^ k * B ^ (N - 2 * k)) / B ^ N :=
      div_le_div_of_nonneg_right hcast (pow_pos hBpos N).le
    _ = (B ^ 2 - (g : ℚ)) ^ k / (B ^ 2) ^ k := by
      rw [hsplit]
      exact mul_div_mul_right _ _ (pow_ne_zero _ hBne)
    _ = ((B ^ 2 - (g : ℚ)) / B ^ 2) ^ k := (div_pow _ _ _).symm
    _ = (1 - (g : ℚ) / B ^ 2) ^ k := by
      rw [sub_div, div_self (pow_ne_zero _ hBne)]

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

open scoped BigOperators

theorem exists_avoiding_of_sum_card_lt {Ω : Type uΩ} {I : Type uI} [Fintype Ω]
    (events : Finset I) (bad : I → Finset Ω)
    (hsmall : (∑ i ∈ events, (bad i).card) < Fintype.card Ω) :
    ∃ ω, ∀ i ∈ events, ω ∉ bad i := by
  classical
  have hUnion : (events.biUnion bad).card < (Finset.univ : Finset Ω).card := by
    rw [Finset.card_univ]
    exact lt_of_le_of_lt Finset.card_biUnion_le hsmall
  obtain ⟨ω, _, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card hUnion
  refine ⟨ω, ?_⟩
  intro i hi hbad
  exact hω (Finset.mem_biUnion.mpr ⟨i, hi, hbad⟩)

theorem exists_avoiding_of_uniform_ratio_lt {Ω : Type uΩ} {I : Type uI} [Fintype Ω]
    (events : Finset I) (bad : I → Finset Ω) (r : ℚ)
    (hΩ : 0 < Fintype.card Ω)
    (hbound : ∀ i ∈ events, ((bad i).card : ℚ) / (Fintype.card Ω : ℚ) ≤ r)
    (hsmall : (events.card : ℚ) * r < 1) :
    ∃ ω, ∀ i ∈ events, ω ∉ bad i := by
  have hpos : (0 : ℚ) < (Fintype.card Ω : ℚ) := Nat.cast_pos.mpr hΩ
  have hsum : (∑ i ∈ events, ((bad i).card : ℚ)) < (Fintype.card Ω : ℚ) := by
    calc
      (∑ i ∈ events, ((bad i).card : ℚ))
          ≤ ∑ i ∈ events, r * (Fintype.card Ω : ℚ) :=
        Finset.sum_le_sum fun i hi => (div_le_iff₀ hpos).mp (hbound i hi)
      _ = (events.card : ℚ) * r * (Fintype.card Ω : ℚ) := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ < 1 * (Fintype.card Ω : ℚ) := mul_lt_mul_of_pos_right hsmall hpos
      _ = (Fintype.card Ω : ℚ) := one_mul _
  apply exists_avoiding_of_sum_card_lt events bad
  apply (Nat.cast_lt (α := ℚ)).mp
  simpa only [Nat.cast_sum] using hsum

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree.MarkedTile

abbrev Residue (m : ℕ) := Fin 3 → ZMod m

def scale (m : ℕ) : Lattice 3 →+ Lattice 3 where
  toFun x i := (m : ℤ) * x i
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp [mul_add]

@[simp] theorem scale_apply (m : ℕ) (x : Lattice 3) (i : Fin 3) :
    scale m x i = (m : ℤ) * x i := rfl

theorem scale_injective (m : ℕ) [NeZero m] : Function.Injective (scale m) := by
  have hm : (m : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  intro x y h
  funext i
  exact mul_left_cancel₀ hm (congrFun h i)

def residue (m : ℕ) : Lattice 3 →+ Residue m where
  toFun x i := (x i : ZMod m)
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

@[simp] theorem residue_apply (m : ℕ) (x : Lattice 3) (i : Fin 3) :
    residue m x i = (x i : ZMod m) := rfl

@[simp] theorem residue_scale (m : ℕ) (x : Lattice 3) :
    residue m (scale m x) = 0 := by
  ext i
  simp [scale, residue]

theorem exists_scale_of_residue_eq_zero (m : ℕ) {x : Lattice 3}
    (h : residue m x = 0) : ∃ a : Lattice 3, scale m a = x := by
  have hd : ∀ i : Fin 3, ∃ a : ℤ, x i = (m : ℤ) * a := by
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (x i) m).mp
    exact congrFun h i
  choose a ha using hd
  exact ⟨a, funext fun i => (ha i).symm⟩

structure ResidueSection (m : ℕ) where
  t : Residue m → Lattice 3
  residue_t : ∀ v, residue m (t v) = v

namespace ResidueSection

variable {m : ℕ} (s : ResidueSection m)

@[simp] theorem residue_t_apply (v : Residue m) : residue m (s.t v) = v :=
  s.residue_t v

theorem t_injective : Function.Injective s.t := by
  intro v v' h
  have := congrArg (residue m) h
  simpa using this

def t0 : Lattice 3 := s.t 0

@[simp] theorem residue_t0 : residue m s.t0 = 0 := s.residue_t 0

theorem coordinates_injective [NeZero m] :
    Function.Injective (fun p : Lattice 3 × Residue m => scale m p.1 + s.t p.2) := by
  rintro ⟨a, v⟩ ⟨a', v'⟩ h
  have hv : v = v' := by
    have := congrArg (residue m) h
    simpa using this
  subst v'
  have ha : a = a' := scale_injective m (add_right_cancel h)
  exact Prod.ext ha rfl

theorem coordinates_surjective :
    Function.Surjective (fun p : Lattice 3 × Residue m => scale m p.1 + s.t p.2) := by
  intro x
  have hz : residue m (x - s.t (residue m x)) = 0 := by simp
  obtain ⟨a, ha⟩ := exists_scale_of_residue_eq_zero m hz
  refine ⟨(a, residue m x), ?_⟩
  change scale m a + s.t (residue m x) = x
  rw [ha, sub_add_cancel]

theorem coordinates_bijective [NeZero m] :
    Function.Bijective (fun p : Lattice 3 × Residue m => scale m p.1 + s.t p.2) :=
  ⟨s.coordinates_injective, s.coordinates_surjective⟩

noncomputable section

variable [NeZero m]

def T0 : Finset (Lattice 3) := Finset.univ.image s.t

def Tstar : Finset (Lattice 3) := s.T0.erase s.t0

def t1 (w : Lattice 3) (v : Residue m) : Lattice 3 :=
  if v = 0 then scale m w + s.t0 else s.t v

def T1 (w : Lattice 3) : Finset (Lattice 3) := Finset.univ.image (s.t1 w)

@[simp] theorem mem_T0 {x : Lattice 3} : x ∈ s.T0 ↔ ∃ v, s.t v = x := by
  classical
  simp [T0]

@[simp] theorem t0_mem_T0 : s.t0 ∈ s.T0 := by
  exact s.mem_T0.mpr ⟨0, rfl⟩

theorem mem_Tstar {x : Lattice 3} :
    x ∈ s.Tstar ↔ ∃ v : Residue m, v ≠ 0 ∧ s.t v = x := by
  classical
  constructor
  · intro hx
    obtain ⟨hx0, hxT⟩ := Finset.mem_erase.mp hx
    obtain ⟨v, hv⟩ := s.mem_T0.mp hxT
    refine ⟨v, ?_, hv⟩
    intro h0
    apply hx0
    simpa [h0, t0] using hv.symm
  · rintro ⟨v, hv0, rfl⟩
    apply Finset.mem_erase.mpr
    refine ⟨?_, s.mem_T0.mpr ⟨v, rfl⟩⟩
    intro h
    exact hv0 (s.t_injective h)

@[simp] theorem residue_t1
    {m : ℕ} (s : ResidueSection m) [NeZero m]
    (w : Lattice 3) (v : Residue m) :
    residue m (s.t1 w v) = v := by
  classical
  by_cases hv : v = 0
  · simp [t1, hv]
  · simp [t1, hv]

theorem t1_injective (w : Lattice 3) : Function.Injective (s.t1 w) := by
  intro v v' h
  have := congrArg (residue m) h
  simpa using this

@[simp] theorem mem_T1 {w x : Lattice 3} : x ∈ s.T1 w ↔ ∃ v, s.t1 w v = x := by
  classical
  simp [T1]

theorem T1_eq_insert (w : Lattice 3) :
    s.T1 w = insert (scale m w + s.t0) s.Tstar := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨v, rfl⟩ := s.mem_T1.mp hx
    by_cases hv : v = 0
    · simp [t1, hv]
    · apply Finset.mem_insert_of_mem
      exact s.mem_Tstar.mpr ⟨v, hv, by simp [t1, hv]⟩
  · intro hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · exact s.mem_T1.mpr ⟨0, by simp [t1, hx]⟩
    · obtain ⟨v, hv, rfl⟩ := s.mem_Tstar.mp hx
      exact s.mem_T1.mpr ⟨v, by simp [t1, hv]⟩

theorem card_T0 : s.T0.card = m ^ 3 := by
  classical
  rw [T0, Finset.card_image_of_injective _ s.t_injective]
  simp [Residue]

theorem card_Tstar : s.Tstar.card = m ^ 3 - 1 := by
  classical
  rw [Tstar, Finset.card_erase_of_mem s.t0_mem_T0, s.card_T0]

theorem card_T1 (w : Lattice 3) : (s.T1 w).card = m ^ 3 := by
  classical
  rw [T1, Finset.card_image_of_injective _ (s.t1_injective w)]
  simp [Residue]

def point (w u : Lattice 3) (v : Residue m) : Lattice 3 :=
  if u = 0 ∧ v = 0 then scale m w + s.t0 else scale m u + s.t v

@[simp] theorem point_zero
    {m : ℕ} (s : ResidueSection m) [NeZero m]
    (w : Lattice 3) (v : Residue m) :
    s.point w 0 v = s.t1 w v := by
  classical
  by_cases hv : v = 0 <;> simp [point, t1, hv]

theorem point_of_ne_zero
    {m : ℕ} (s : ResidueSection m) [NeZero m]
    (w : Lattice 3) {u : Lattice 3} (hu : u ≠ 0)
    (v : Residue m) : s.point w u v = scale m u + s.t v := by
  classical
  simp [point, hu]

@[simp] theorem residue_point
    {m : ℕ} (s : ResidueSection m) [NeZero m]
    (w u : Lattice 3) (v : Residue m) :
    residue m (s.point w u v) = v := by
  classical
  by_cases h : u = 0 ∧ v = 0
  · simp [point, h]
  · simp [point, h]

theorem point_injective {w : Lattice 3} {U : Finset (Lattice 3)}
    (hw : w ∉ U) :
    Function.Injective (fun q : ↥U × Residue m => s.point w q.1 q.2) := by
  classical
  rintro ⟨u, v⟩ ⟨u', v'⟩ h
  have hv : v = v' := by
    have := congrArg (residue m) h
    simpa using this
  subst v'
  suffices hu : u = u' from congrArg (fun a : ↥U => (a, v)) hu
  apply Subtype.ext
  by_cases h0 : (u : Lattice 3) = 0
  · by_cases h0' : (u' : Lattice 3) = 0
    · exact h0.trans h0'.symm
    · by_cases hv0 : v = 0
      · have he : scale m w = scale m (u' : Lattice 3) := by
          apply add_right_cancel (b := s.t0)
          simpa [point, h0, h0', hv0, t0] using h
        have he' := scale_injective m he
        exact False.elim (hw (he'.symm ▸ u'.property))
      · have he : scale m (u : Lattice 3) = scale m (u' : Lattice 3) := by
          apply add_right_cancel (b := s.t v)
          simpa [point, hv0] using h
        exact scale_injective m he
  · by_cases h0' : (u' : Lattice 3) = 0
    · by_cases hv0 : v = 0
      · have he : scale m (u : Lattice 3) = scale m w := by
          apply add_right_cancel (b := s.t0)
          simpa [point, h0, h0', hv0, t0] using h
        have he' := scale_injective m he
        exact False.elim (hw (he' ▸ u.property))
      · have he : scale m (u : Lattice 3) = scale m (u' : Lattice 3) := by
          apply add_right_cancel (b := s.t v)
          simpa [point, hv0] using h
        exact scale_injective m he
    · have he : scale m (u : Lattice 3) = scale m (u' : Lattice 3) := by
        apply add_right_cancel (b := s.t v)
        simpa [point, h0, h0'] using h
      exact scale_injective m he

def finalTile (w : Lattice 3) (U : Finset (Lattice 3)) : Finset (Lattice 3) :=
  Finset.univ.image (fun q : ↥U × Residue m => s.point w q.1 q.2)

theorem mem_finalTile {w x : Lattice 3} {U : Finset (Lattice 3)} :
    x ∈ s.finalTile w U ↔ ∃ u ∈ U, ∃ v, s.point w u v = x := by
  classical
  simp only [finalTile, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨u, v⟩, h⟩
    exact ⟨u, u.property, v, h⟩
  · rintro ⟨u, hu, v, h⟩
    exact ⟨(⟨u, hu⟩, v), h⟩

theorem card_finalTile {w : Lattice 3} {U : Finset (Lattice 3)} (hw : w ∉ U) :
    (s.finalTile w U).card = U.card * m ^ 3 := by
  classical
  rw [finalTile, Finset.card_image_of_injective _ (s.point_injective hw)]
  simp [Residue]

theorem finalTile_nonempty (w : Lattice 3) {U : Finset (Lattice 3)}
    (h0 : 0 ∈ U) : (s.finalTile w U).Nonempty := by
  exact ⟨s.point w 0 0, s.mem_finalTile.mpr ⟨0, h0, 0, rfl⟩⟩

theorem finalTile_eq_union (w : Lattice 3) {U : Finset (Lattice 3)} (h0 : 0 ∈ U) :
    s.finalTile w U = s.T1 w ∪
      (U.erase 0).biUnion (fun u => s.T0.image (fun x => scale m u + x)) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu, v, rfl⟩ := s.mem_finalTile.mp hx
    by_cases hu0 : u = 0
    · apply Finset.mem_union_left
      exact s.mem_T1.mpr ⟨v, by simp [hu0]⟩
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨u, Finset.mem_erase.mpr ⟨hu0, hu⟩, ?_⟩
      apply Finset.mem_image.mpr
      exact ⟨s.t v, s.mem_T0.mpr ⟨v, rfl⟩, (s.point_of_ne_zero w hu0 v).symm⟩
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨v, hv⟩ := s.mem_T1.mp hx
      exact s.mem_finalTile.mpr ⟨0, h0, v, by simpa using hv⟩
    · obtain ⟨u, hu, hx⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨hu0, huU⟩ := Finset.mem_erase.mp hu
      obtain ⟨t, ht, htx⟩ := Finset.mem_image.mp hx
      obtain ⟨v, hv⟩ := s.mem_T0.mp ht
      refine s.mem_finalTile.mpr ⟨u, huU, v, ?_⟩
      rw [s.point_of_ne_zero w hu0 v, hv, htx]

theorem constituent_disjoint {w : Lattice 3} {U : Finset (Lattice 3)}
    (hw : w ∉ U) {u u' : ↥U} (hne : u ≠ u') :
    Disjoint (Set.range (s.point w (u : Lattice 3)))
      (Set.range (s.point w (u' : Lattice 3))) := by
  rw [Set.disjoint_left]
  rintro x ⟨v, hv⟩ ⟨v', hv'⟩
  apply hne
  have hp : (u, v) = (u', v') := s.point_injective hw (hv.trans hv'.symm)
  exact congrArg Prod.fst hp

end
end ResidueSection
end PeriodicTilingThree.MarkedTile

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

open scoped Classical

private def residueSuccessor (m : ℕ) (d : Lattice 3) : Equiv.Perm (Residue3 m) where
  toFun u := u + residueMod m d
  invFun u := u - residueMod m d
  left_inv u := add_sub_cancel_right u _
  right_inv u := sub_add_cancel u _

private theorem exists_residue_pairs
    {D : Finset (Lattice 3)} (hD : ∀ d, d ∈ D ↔ Requested 64 d) (d : ↥D) :
    ∃ pair : (Fin 32000 × Fin 2) ↪ Residue3 64,
      (∀ j, pair (j, 1) = pair (j, 0) + residueMod 64 d.1) ∧
      ∀ x, pair x ≠ 0 := by
  have hd : Requested 64 d.1 := (hD d.1).mp d.2
  exact exists_disjoint_successor_pairs (residueSuccessor 64 d.1)
    (requested_successor_ne hd) 0 32000 (by rw [card_residue3]; norm_num)

private noncomputable def residuePairs
    {D : Finset (Lattice 3)} (hD : ∀ d, d ∈ D ↔ Requested 64 d) (d : ↥D) :
    (Fin 32000 × Fin 2) ↪ Residue3 64 :=
  Classical.choose (exists_residue_pairs hD d)

private theorem residuePairs_step
    {D : Finset (Lattice 3)} (hD : ∀ d, d ∈ D ↔ Requested 64 d)
    (d : ↥D) (j : Fin 32000) :
    residuePairs hD d (j, 1) = residuePairs hD d (j, 0) + residueMod 64 d.1 :=
  (Classical.choose_spec (exists_residue_pairs hD d)).1 j

private theorem residuePairs_ne_zero
    {D : Finset (Lattice 3)} (hD : ∀ d, d ∈ D ↔ Requested 64 d)
    (d : ↥D) (x : Fin 32000 × Fin 2) : residuePairs hD d x ≠ 0 :=
  (Classical.choose_spec (exists_residue_pairs hD d)).2 x

private noncomputable def residuePairGood
    {D : Finset (Lattice 3)} (hD : ∀ d, d ∈ D ↔ Requested 64 d)
    (d : ↥D) (j : Fin 32000) : Finset (LiftAlphabet × LiftAlphabet) :=
  PairGood 64 d.1 (residuePairs hD d (j, 0)) (residuePairs hD d (j, 1))

private theorem normalized_bad_assignment_ratio
    {V : Type uV} {C : Type uC} [Fintype V] [Fintype C] {k : ℕ}
    (pair : (Fin k × Fin 2) ↪ V) (Good : Fin k → Finset (C × C))
    (Bad : Finset (V → C)) (hBad : Bad = allBadAssignments pair Good)
    (N : ℕ) (hN : N = Fintype.card C ^ Fintype.card V)
    (hC : Fintype.card C = 125) (hgood : ∀ j, 27 ≤ (Good j).card) :
    (Bad.card : ℚ) / (N : ℚ) ≤ ((15598 : ℚ) / 15625) ^ k := by
  have hCpos : 0 < Fintype.card C := by rw [hC]; norm_num
  have hg : 27 ≤ Fintype.card C ^ 2 := by rw [hC]; norm_num
  have heq : (1 : ℚ) - ((27 : ℕ) : ℚ) / (Fintype.card C : ℚ) ^ 2 =
      15598 / 15625 := by
    rw [hC]
    norm_num
  have h := allBadAssignments_card_ratio_le pair Good 27 hCpos hg hgood
  rw [Fintype.card_fun, ← hN, ← hBad, heq] at h
  exact h

private theorem residuePairGood_card
    {D : Finset (Lattice 3)} (hD : ∀ d, d ∈ D ↔ Requested 64 d)
    (d : ↥D) (j : Fin 32000) : 27 ≤ (residuePairGood hD d j).card := by
  have hd : Requested 64 d.1 := (hD d.1).mp d.2
  exact card_PairGood_ge (m := 64) (d := d.1)
    (u := residuePairs hD d (j, 0)) (v := residuePairs hD d (j, 1))
    hd (residuePairs_step hD d j)

private theorem representative_difference_of_pairGood {m : ℕ} [NeZero m]
    (ω : LiftAssignment m) (d : Lattice 3) (u v : Residue3 m) :
    (ω u, ω v) ∈ PairGood m d u v →
      representative m ω v - representative m ω u = d := by
  have hiff := pairGood_assignment_iff (m := m) (d := d) ω u v
  generalize hset : PairGood m d u v = S at hiff ⊢
  exact hiff.mp

private theorem exists_good_pair {V : Type uV} {C : Type uC} [Fintype V] [Fintype C] {k : ℕ}
    (pair : (Fin k × Fin 2) ↪ V) (Good : Fin k → Finset (C × C)) (ω : V → C)
    (P : Fin k → Prop)
    (hP : ∀ j, (ω (pair (j, 0)), ω (pair (j, 1))) ∈ Good j → P j)
    (hbad : ω ∉ allBadAssignments pair Good) : ∃ j, P j := by
  rw [mem_allBadAssignments] at hbad
  push Not at hbad
  obtain ⟨j, hj⟩ := hbad
  exact ⟨j, hP j hj⟩

private theorem exists_simultaneous_good_pairs
    {I : Type uI} {V : Type uV} {C : Type uC} [Fintype V] [Fintype C] {k : ℕ}
    (events : Finset I) (pair : I → (Fin k × Fin 2) ↪ V)
    (Good : I → Fin k → Finset (C × C))
    (hC : Fintype.card C = 125) (hgood : ∀ i j, 27 ≤ (Good i j).card)
    (P : I → (V → C) → Fin k → Prop)
    (hP : ∀ i ω j, (ω (pair i (j, 0)), ω (pair i (j, 1))) ∈ Good i j → P i ω j)
    (hsmall : (events.card : ℚ) * ((15598 : ℚ) / 15625) ^ k < 1) :
    ∃ ω : V → C, ∀ i ∈ events, ∃ j, P i ω j := by
  classical
  have hΩ : 0 < Fintype.card (V → C) := by
    rw [Fintype.card_fun, hC]
    exact pow_pos (by norm_num) _
  have hbound (i : I) :
      ((allBadAssignments (pair i) (Good i)).card : ℚ) /
          (Fintype.card (V → C) : ℚ) ≤ ((15598 : ℚ) / 15625) ^ k := by
    exact normalized_bad_assignment_ratio (pair i) (Good i)
      (allBadAssignments (pair i) (Good i)) rfl (Fintype.card (V → C))
      (by rw [Fintype.card_fun]) hC (hgood i)
  obtain ⟨ω, hω⟩ := exists_avoiding_of_uniform_ratio_lt events
    (fun i => allBadAssignments (pair i) (Good i))
    (((15598 : ℚ) / 15625) ^ k) hΩ (fun i _ => hbound i) hsmall
  refine ⟨ω, ?_⟩
  intro i hi
  exact exists_good_pair (pair i) (Good i) ω (P i ω) (hP i ω) (hω i hi)

private theorem exists_rigid_assignment_of_requests
    (D : Finset (Lattice 3)) (hD : ∀ d, d ∈ D ↔ Requested 64 d)
    (hcardD : D.card ≤ 129 ^ 3) :
    ∃ ω : LiftAssignment 64, ∀ d : Lattice 3, Requested 64 d →
      ∃ u v : Residue3 64, u ≠ 0 ∧ v ≠ 0 ∧
        representative 64 ω v - representative 64 ω u = d := by
  classical
  have hcard : (Finset.univ : Finset ↥D).card ≤ 129 ^ 3 := by
    rw [Finset.card_univ, Fintype.card_coe]
    exact hcardD
  have hsmall : ((Finset.univ : Finset ↥D).card : ℚ) *
      ((15598 : ℚ) / 15625) ^ 32000 < 1 := by
    apply lt_of_le_of_lt _ residue_union_bound_32000
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast hcard
    · exact pow_nonneg (by norm_num) _
  have himp (e : ↥D) (ω : LiftAssignment 64) (j : Fin 32000) :
      (ω (residuePairs hD e (j, 0)), ω (residuePairs hD e (j, 1))) ∈
        residuePairGood hD e j →
      representative 64 ω (residuePairs hD e (j, 1)) -
        representative 64 ω (residuePairs hD e (j, 0)) = e.1 := by
    dsimp only [residuePairGood]
    exact representative_difference_of_pairGood (m := 64) ω e.1
      (residuePairs hD e (j, 0)) (residuePairs hD e (j, 1))
  obtain ⟨ω, hω⟩ := exists_simultaneous_good_pairs
    (Finset.univ : Finset ↥D) (residuePairs hD) (residuePairGood hD)
    card_liftAlphabet (residuePairGood_card hD)
    (fun e ω j => representative 64 ω (residuePairs hD e (j, 1)) -
      representative 64 ω (residuePairs hD e (j, 0)) = e.1) himp hsmall
  refine ⟨ω, ?_⟩
  intro d hd
  let e : ↥D := ⟨d, (hD d).mpr hd⟩
  obtain ⟨j, hj⟩ := hω e (Finset.mem_univ _)
  exact ⟨residuePairs hD e (j, 0), residuePairs hD e (j, 1),
    residuePairs_ne_zero hD e (j, 0), residuePairs_ne_zero hD e (j, 1), hj⟩

theorem exists_rigid_assignment64 :
    ∃ ω : LiftAssignment 64, ∀ d : Lattice 3, Requested 64 d →
      ∃ u v : Residue3 64, u ≠ 0 ∧ v ≠ 0 ∧
        representative 64 ω v - representative 64 ω u = d := by
  exact exists_rigid_assignment_of_requests (requestedVectors 64)
    (fun d => mem_requestedVectors (m := 64) (d := d)) (card_requestedVectors_le 64)

noncomputable def rigidAssignment64 : LiftAssignment 64 :=
  Classical.choose exists_rigid_assignment64

theorem rigidAssignment64_difference (d : Lattice 3) (hd : Requested 64 d) :
    ∃ u v : Residue3 64, u ≠ 0 ∧ v ≠ 0 ∧
      representative 64 rigidAssignment64 v - representative 64 rigidAssignment64 u = d :=
  Classical.choose_spec exists_rigid_assignment64 d hd

noncomputable def rigidSection : MarkedTile.ResidueSection 64 where
  t := representative 64 rigidAssignment64
  residue_t v := representative_residue 64 rigidAssignment64 v

theorem rigidSection_difference (d : Lattice 3) (hd : Requested 64 d) :
    ∃ u v : MarkedTile.Residue 64, u ≠ 0 ∧ v ≠ 0 ∧ rigidSection.t v - rigidSection.t u = d :=
  rigidAssignment64_difference d hd

private theorem section_difference_to_Tstar {m : ℕ} [NeZero m]
    (s : MarkedTile.ResidueSection m) (d : Lattice 3)
    (h : ∃ u v : MarkedTile.Residue m,
      u ≠ 0 ∧ v ≠ 0 ∧ s.t v - s.t u = d) :
    ∃ x ∈ s.Tstar, ∃ y ∈ s.Tstar, x - y = d := by
  obtain ⟨u, v, hu, hv, hdiff⟩ := h
  have hvT : s.t v ∈ s.Tstar :=
    (s.mem_Tstar (x := s.t v)).mpr ⟨v, hv, rfl⟩
  have huT : s.t u ∈ s.Tstar :=
    (s.mem_Tstar (x := s.t u)).mpr ⟨u, hu, rfl⟩
  exact ⟨s.t v, hvT, s.t u, huT, hdiff⟩

theorem rigidSection_Tstar_difference (d : Lattice 3) (hd : Requested 64 d) :
    ∃ x ∈ rigidSection.Tstar, ∃ y ∈ rigidSection.Tstar, x - y = d := by
  exact section_difference_to_Tstar rigidSection d (rigidSection_difference d hd)

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

open MeasureTheory

@[simp] theorem castLattice_apply {d : ℕ} (z : Lattice d) (i : Fin d) :
    castLattice z i = (z i : ℝ) := rfl

theorem castLattice_injective {d : ℕ} :
    Function.Injective (castLattice : Lattice d → Space d) := by
  intro z w h
  funext i
  exact Int.cast_injective (congrArg (fun x : Space d => x i) h)

def unitVoxel {d : ℕ} (c : Space d) : Set (Space d) :=
  {x | x - c ∈ unitCube d}

theorem mem_unitCube {d : ℕ} {x : Space d} :
    x ∈ unitCube d ↔ ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
  constructor
  · intro h i
    exact ⟨h.1 i, h.2 i⟩
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩

@[simp] theorem mem_unitVoxel {d : ℕ} {c x : Space d} :
    x ∈ unitVoxel c ↔ x - c ∈ unitCube d := Iff.rfl

theorem unitVoxel_eq_Icc {d : ℕ} (c : Space d) :
    unitVoxel c = Set.Icc c (c + 1) := by
  ext x
  constructor
  · intro hx
    have h := mem_unitCube.mp hx
    constructor
    · intro i
      exact sub_nonneg.mp (h i).1
    · intro i
      have hi := (sub_le_iff_le_add.mp (h i).2)
      simpa [add_comm] using hi
  · intro hx
    apply mem_unitCube.mpr
    intro i
    constructor
    · exact sub_nonneg.mpr (hx.1 i)
    · apply sub_le_iff_le_add.mpr
      simpa [add_comm] using hx.2 i

@[simp] theorem mem_Thickening {d : ℕ} {F : Finset (Lattice d)} {x : Space d} :
    x ∈ Thickening F ↔ ∃ z ∈ F, x - castLattice z ∈ unitCube d := Iff.rfl

theorem unitVoxel_subset_Thickening {d : ℕ} {F : Finset (Lattice d)}
    {z : Lattice d} (hz : z ∈ F) : unitVoxel (castLattice z) ⊆ Thickening F := by
  intro x hx
  exact ⟨z, hz, hx⟩

def TypedAETiles {d : ℕ} (Ω0 Ω1 C C1 : Set (Space d)) : Prop := by
  classical
  exact ∀ᵐ x ∂volume, ∃! c : C,
    x - (c : Space d) ∈ if (c : Space d) ∈ C1 then Ω1 else Ω0

def scaledCast {d : ℕ} (m : ℕ) : Lattice d →+ Space d where
  toFun z := (m : ℝ) • castLattice z
  map_zero' := by simp
  map_add' z w := by simp [smul_add]

@[simp] theorem scaledCast_apply {d : ℕ} (m : ℕ) (z : Lattice d) :
    scaledCast m z = (m : ℝ) • castLattice z := rfl

theorem scaledCast_injective {d : ℕ} {m : ℕ} (hm : m ≠ 0) :
    Function.Injective (scaledCast m : Lattice d → Space d) := by
  intro z w h
  funext i
  have hi := congrArg (fun x : Space d => x i) h
  change (m : ℝ) * (z i : ℝ) = (m : ℝ) * (w i : ℝ) at hi
  exact Int.cast_injective (mul_left_cancel₀ (Nat.cast_ne_zero.mpr hm) hi)

def scaledGrid (m : ℕ) : AddSubgroup (Space 3) :=
  (scaledCast m : Lattice 3 →+ Space 3).range

theorem mem_scaledGrid {m : ℕ} {x : Space 3} :
    x ∈ scaledGrid m ↔ ∃ z : Lattice 3, (m : ℝ) • castLattice z = x := Iff.rfl

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

private theorem floor_abs_le_nat {m : ℕ} {x : ℝ} (hx : |x| ≤ (m : ℝ)) :
    |⌊x⌋| ≤ (m : ℤ) := by
  apply abs_le.mpr
  constructor
  · apply Int.le_floor.mpr
    exact_mod_cast (abs_le.mp hx).1
  · have hh : (⌊x⌋ : ℝ) ≤ (m : ℝ) := (Int.floor_le x).trans (abs_le.mp hx).2
    exact_mod_cast hh

private theorem floor_error_lt_one (x : ℝ) : |x - (⌊x⌋ : ℝ)| < 1 := by
  rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le x))]
  have := Int.lt_floor_add_one x
  linarith

private theorem floor_successor_error_lt_one {x : ℝ} (hx : x ≠ (⌊x⌋ : ℝ)) :
    |x - ((⌊x⌋ + 1 : ℤ) : ℝ)| < 1 := by
  have hlo : (⌊x⌋ : ℝ) < x := lt_of_le_of_ne (Int.floor_le x) hx.symm
  have hhi := Int.lt_floor_add_one x
  simp only [Int.cast_add, Int.cast_one]
  apply abs_lt.mpr
  constructor <;> linarith

theorem closed_box_rounding_exists {n : ℕ} (m : ℕ) (hm : 2 ≤ m) (δ : Space n)
    (hδ : ∀ i, |δ i| ≤ (m : ℝ))
    (hnot : ¬ ∃ z : Lattice n, δ = (m : ℝ) • castLattice z) :
    ∃ z : Lattice n,
      (∀ i, |z i| ≤ (m : ℤ)) ∧
      (∃ i, ¬ (m : ℤ) ∣ z i) ∧
      (∀ i, |δ i - (z i : ℝ)| < 1) := by
  classical
  let a : Lattice n := fun i => ⌊δ i⌋
  have habs (i : Fin n) : |a i| ≤ (m : ℤ) := floor_abs_le_nat (hδ i)
  have herr (i : Fin n) : |δ i - (a i : ℝ)| < 1 := floor_error_lt_one (δ i)
  by_cases hdiv : ∀ i, (m : ℤ) ∣ a i
  · have hnonint : ∃ j, δ j ≠ (a j : ℝ) := by
      by_contra h
      have heq (i : Fin n) : δ i = (a i : ℝ) := by
        by_contra hi
        exact h ⟨i, hi⟩
      let z : Lattice n := fun i => Classical.choose (hdiv i)
      have hz (i : Fin n) : a i = (m : ℤ) * z i := Classical.choose_spec (hdiv i)
      apply hnot
      refine ⟨z, ?_⟩
      funext i
      change δ i = (m : ℝ) * (z i : ℝ)
      rw [heq i]
      exact_mod_cast hz i
    obtain ⟨j, hj⟩ := hnonint
    have hjstrict : (a j : ℝ) < δ j := lt_of_le_of_ne (Int.floor_le (δ j)) hj.symm
    have hjlt : a j < (m : ℤ) := by
      have hh : (a j : ℝ) < (m : ℝ) := hjstrict.trans_le (abs_le.mp (hδ j)).2
      exact_mod_cast hh
    let z : Lattice n := Function.update a j (a j + 1)
    refine ⟨z, ?_, ?_, ?_⟩
    · intro i
      by_cases hij : i = j
      · subst i
        simp only [z, Function.update_self]
        apply abs_le.mpr
        have ha := (abs_le.mp (habs j)).1
        constructor <;> omega
      · simpa only [z, Function.update_of_ne hij] using habs i
    · refine ⟨j, ?_⟩
      simp only [z, Function.update_self]
      intro hsucc
      have hone : (m : ℤ) ∣ 1 := by
        simpa using dvd_sub hsucc (hdiv j)
      have hmle : (m : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num : (0 : ℤ) < 1) hone
      have hmtwo : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
      omega
    · intro i
      by_cases hij : i = j
      · subst i
        simp only [z, Function.update_self]
        exact floor_successor_error_lt_one hj
      · simpa only [z, Function.update_of_ne hij] using herr i
  · exact ⟨a, habs, not_forall.mp hdiv, herr⟩

theorem closed_box_rounding (m : ℕ) (hm : 2 ≤ m) (δ : Space 3)
    (hδ : ∀ i, |δ i| ≤ (m : ℝ)) (hnot : δ ∉ scaledGrid m) :
    ∃ z : Lattice 3,
      (∀ i, |z i| ≤ (m : ℤ)) ∧
      (∃ i, ¬ (m : ℤ) ∣ z i) ∧
      (∀ i, |δ i - (z i : ℝ)| < 1) := by
  apply closed_box_rounding_exists m hm δ hδ
  rintro ⟨z, hz⟩
  exact hnot (mem_scaledGrid.mpr ⟨z, hz.symm⟩)

theorem closed_box_rounding_norm (m : ℕ) (hm : 2 ≤ m) (δ : Space 3)
    (hδ : ∀ i, |δ i| ≤ (m : ℝ)) (hnot : δ ∉ scaledGrid m) :
    ∃ z : Lattice 3,
      (∀ i, |z i| ≤ (m : ℤ)) ∧
      (∃ i, ¬ (m : ℤ) ∣ z i) ∧
      ‖δ - castLattice z‖ < 1 := by
  obtain ⟨z, hz, hdiv, herr⟩ := closed_box_rounding m hm δ hδ hnot
  refine ⟨z, hz, hdiv, (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr ?_⟩
  intro i
  simpa only [Pi.sub_apply, castLattice_apply, Real.norm_eq_abs] using herr i

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

open Set MeasureTheory

def openUnitVoxel {d : ℕ} (c : Space d) : Set (Space d) :=
  Set.pi Set.univ (fun i => Set.Ioo (c i) (c i + 1))

theorem mem_openUnitVoxel {d : ℕ} {c x : Space d} :
    x ∈ openUnitVoxel c ↔ ∀ i, c i < x i ∧ x i < c i + 1 := by
  simp [openUnitVoxel, Set.mem_pi]

theorem openUnitVoxel_nonempty {d : ℕ} (c : Space d) :
    (openUnitVoxel c).Nonempty := by
  refine ⟨fun i => c i + 1 / 2, mem_openUnitVoxel.mpr ?_⟩
  intro i
  constructor <;> linarith

theorem isOpen_openUnitVoxel {d : ℕ} (c : Space d) :
    IsOpen (openUnitVoxel c) :=
  isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)

theorem openUnitVoxel_subset {d : ℕ} (c : Space d) :
    openUnitVoxel c ⊆ unitVoxel c := by
  intro x hx
  rw [unitVoxel_eq_Icc]
  have h := mem_openUnitVoxel.mp hx
  exact ⟨fun i => (h i).1.le, fun i => (h i).2.le⟩

theorem unitVoxel_isCompact {d : ℕ} (c : Space d) :
    IsCompact (unitVoxel c) := by
  rw [unitVoxel_eq_Icc]
  exact isCompact_Icc

theorem unitVoxel_isClosed {d : ℕ} (c : Space d) :
    IsClosed (unitVoxel c) := (unitVoxel_isCompact c).isClosed

theorem unitVoxel_measurableSet {d : ℕ} (c : Space d) :
    MeasurableSet (unitVoxel c) := (unitVoxel_isClosed c).measurableSet

theorem unitVoxel_inter_eq_Icc {d : ℕ} (a b : Space d) :
    unitVoxel a ∩ unitVoxel b =
      Set.Icc (fun i => max (a i) (b i))
        (fun i => min (a i + 1) (b i + 1)) := by
  rw [unitVoxel_eq_Icc, unitVoxel_eq_Icc]
  ext x
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨fun i => max_le (ha.1 i) (hb.1 i),
      fun i => le_min (ha.2 i) (hb.2 i)⟩
  · rintro ⟨hl, hu⟩
    exact ⟨⟨fun i => (le_max_left _ _).trans (hl i),
      fun i => (hu i).trans (min_le_left _ _)⟩,
      ⟨fun i => (le_max_right _ _).trans (hl i),
      fun i => (hu i).trans (min_le_right _ _)⟩⟩

theorem mem_unitVoxel_cast_iff_of_mem_open {d : ℕ} {x : Space d}
    {z z' : Lattice d} (hx : x ∈ openUnitVoxel (castLattice z)) :
    x ∈ unitVoxel (castLattice z') ↔ z' = z := by
  constructor
  · intro hx'
    have ho := mem_openUnitVoxel.mp hx
    rw [unitVoxel_eq_Icc] at hx'
    funext i
    have hi := ho i
    have hl := hx'.1 i
    have hu := hx'.2 i
    change (z i : ℝ) < x i ∧ x i < (z i : ℝ) + 1 at hi
    change (z' i : ℝ) ≤ x i at hl
    change x i ≤ (z' i : ℝ) + 1 at hu
    rcases lt_trichotomy (z' i) (z i) with hlt | heq | hgt
    · have hh : (z' i : ℝ) + 1 ≤ (z i : ℝ) := by
        have hh' : ((z' i + 1 : ℤ) : ℝ) ≤ (z i : ℝ) :=
          Int.cast_le.mpr (Int.add_one_le_of_lt hlt)
        simpa only [Int.cast_add, Int.cast_one] using hh'
      linarith
    · exact heq
    · have hh : (z i : ℝ) + 1 ≤ (z' i : ℝ) := by
        have hh' : ((z i + 1 : ℤ) : ℝ) ≤ (z' i : ℝ) :=
          Int.cast_le.mpr (Int.add_one_le_of_lt hgt)
        simpa only [Int.cast_add, Int.cast_one] using hh'
      linarith
  · rintro rfl
    exact openUnitVoxel_subset _ hx

theorem openUnitVoxel_disjoint_unitVoxel_int {d : ℕ} {z z' : Lattice d}
    (hne : z ≠ z') :
    Disjoint (openUnitVoxel (castLattice z)) (unitVoxel (castLattice z')) := by
  apply Set.disjoint_left.mpr
  intro x hx hx'
  exact hne ((mem_unitVoxel_cast_iff_of_mem_open hx).mp hx').symm

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

open Set MeasureTheory Filter
open scoped ENNReal

theorem unitVoxel_volume {d : ℕ} (c : Space d) :
    volume (unitVoxel c) = 1 := by
  rw [unitVoxel_eq_Icc, Real.volume_Icc_pi]
  simp

theorem unitCube_volume (d : ℕ) : volume (unitCube d) = 1 := by
  simpa only [unitVoxel, sub_zero, Set.ofPred_mem_eq] using
    unitVoxel_volume (0 : Space d)

theorem openUnitVoxel_volume {d : ℕ} (c : Space d) :
    volume (openUnitVoxel c) = 1 := by
  rw [openUnitVoxel, Real.volume_pi_Ioo]
  simp

theorem openUnitVoxel_ae_eq_unitVoxel {d : ℕ} (c : Space d) :
    openUnitVoxel c =ᵐ[volume] unitVoxel c := by
  rw [unitVoxel_eq_Icc]
  exact Measure.univ_pi_Ioo_ae_eq_Icc

theorem unitVoxel_frontier_volume_zero {d : ℕ} (c : Space d) :
    volume (frontier (unitVoxel c)) = 0 := by
  have hnull : volume (unitVoxel c \ openUnitVoxel c) = 0 :=
    ae_le_set.mp (openUnitVoxel_ae_eq_unitVoxel c).symm.le
  apply measure_mono_null _ hnull
  intro x hx
  refine ⟨(unitVoxel_isClosed c).frontier_subset hx, ?_⟩
  intro ho
  exact hx.2 (interior_maximal (openUnitVoxel_subset c)
    (isOpen_openUnitVoxel c) ho)

theorem unitVoxel_inter_volume_pos {d : ℕ} (a b : Space d)
    (h : ∀ i, |b i - a i| < 1) :
    0 < volume (unitVoxel a ∩ unitVoxel b) := by
  rw [unitVoxel_inter_eq_Icc, Real.volume_Icc_pi]
  apply bot_lt_iff_ne_bot.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  apply sub_pos.mpr
  apply max_lt
  · apply lt_min
    · linarith
    · have hi := (abs_lt.mp (h i)).1
      linarith
  · apply lt_min
    · have hi := (abs_lt.mp (h i)).2
      linarith
    · linarith

theorem closedBall_volume {d : ℕ} (c : Space d) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.closedBall c r) = ENNReal.ofReal ((2 * r) ^ d) := by
  simpa using Real.volume_pi_closedBall c hr

theorem closedBall_ae_eq_ball {d : ℕ} (c : Space d) {r : ℝ} (hr : 0 < r) :
    Metric.closedBall c r =ᵐ[volume] Metric.ball c r := by
  rw [closedBall_pi c hr.le, ball_pi c hr]
  simp only [Real.closedBall_eq_Icc, Real.ball_eq_Ioo]
  exact Measure.pi_Ioo_ae_eq_pi_Icc.symm

theorem closedBall_frontier_volume_zero {d : ℕ} (c : Space d)
    {r : ℝ} (hr : 0 < r) :
    volume (frontier (Metric.closedBall c r)) = 0 := by
  have hnull : volume (Metric.closedBall c r \ Metric.ball c r) = 0 :=
    ae_le_set.mp (closedBall_ae_eq_ball c hr).le
  apply measure_mono_null _ hnull
  intro x hx
  refine ⟨Metric.isClosed_closedBall.frontier_subset hx, ?_⟩
  intro hb
  exact hx.2 (Metric.ball_subset_interior_closedBall hb)

theorem unitVoxel_aedisjoint_int {d : ℕ} {z z' : Lattice d} (hne : z ≠ z') :
    AEDisjoint volume (unitVoxel (castLattice z)) (unitVoxel (castLattice z')) := by
  exact (openUnitVoxel_disjoint_unitVoxel_int hne).aedisjoint.congr
    (openUnitVoxel_ae_eq_unitVoxel _).symm EventuallyEq.rfl

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

open Set MeasureTheory
open scoped ENNReal

theorem Thickening_eq_iUnion {d : ℕ} (F : Finset (Lattice d)) :
    Thickening F = ⋃ z ∈ F, unitVoxel (castLattice z) := by
  ext x
  simp only [mem_Thickening, Set.mem_iUnion, mem_unitVoxel, exists_prop]

theorem thickening_isCompact {d : ℕ} (F : Finset (Lattice d)) :
    IsCompact (Thickening F) := by
  rw [Thickening_eq_iUnion]
  exact F.isCompact_biUnion (fun z _ => unitVoxel_isCompact (castLattice z))

theorem thickening_isClosed {d : ℕ} (F : Finset (Lattice d)) :
    IsClosed (Thickening F) := (thickening_isCompact F).isClosed

theorem thickening_measurableSet {d : ℕ} (F : Finset (Lattice d)) :
    MeasurableSet (Thickening F) := (thickening_isClosed F).measurableSet

theorem thickening_isBounded {d : ℕ} (F : Finset (Lattice d)) :
    Bornology.IsBounded (Thickening F) := (thickening_isCompact F).isBounded

theorem thickening_volume {d : ℕ} (F : Finset (Lattice d)) :
    volume (Thickening F) = (F.card : ℝ≥0∞) := by
  classical
  rw [Thickening_eq_iUnion]
  rw [measure_biUnion_finset₀
    (fun z _ z' _ hne => unitVoxel_aedisjoint_int hne)
    (fun z _ => (unitVoxel_measurableSet (castLattice z)).nullMeasurableSet)]
  simp [unitVoxel_volume]

theorem thickening_aedisjoint_of_disjoint {d : ℕ}
    {S T : Finset (Lattice d)} (h : Disjoint S T) :
    AEDisjoint volume (Thickening S) (Thickening T) := by
  classical
  simp only [Thickening_eq_iUnion, AEDisjoint.iUnion_left_iff,
    AEDisjoint.iUnion_right_iff]
  intro z hz z' hz'
  apply unitVoxel_aedisjoint_int
  intro heq
  subst z'
  exact Finset.disjoint_left.mp h hz' hz

theorem thickening_inter_measure_zero_of_disjoint {d : ℕ}
    {S T : Finset (Lattice d)} (h : Disjoint S T) :
    volume (Thickening S ∩ Thickening T) = 0 :=
  (thickening_aedisjoint_of_disjoint h).eq

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

open Set MeasureTheory
open scoped Classical

def RigidDifferences (m : ℕ) (S : Finset (Lattice 3)) : Prop :=
  ∀ d : Lattice 3, (∀ i, |d i| ≤ (m : ℤ)) → (∃ i, ¬ (m : ℤ) ∣ d i) →
    ∃ t ∈ S, ∃ t' ∈ S, t - t' = d

theorem TypedAETiles.aedisjoint {d : ℕ} {Ω0 Ω1 C C1 : Set (Space d)}
    (h : TypedAETiles Ω0 Ω1 C C1) {c c' : C} (hne : c ≠ c') :
    AEDisjoint volume
      {x | x - (c : Space d) ∈ if (c : Space d) ∈ C1 then Ω1 else Ω0}
      {x | x - (c' : Space d) ∈ if (c' : Space d) ∈ C1 then Ω1 else Ω0} := by
  apply measure_mono_null ?_ (ae_iff.mp h)
  rintro x ⟨hx, hx'⟩ ⟨a, _ha, huniq⟩
  exact hne ((huniq c hx).trans (huniq c' hx').symm)

theorem AETiles.aedisjoint {d : ℕ} {Ω A : Set (Space d)}
    (h : AETiles Ω A) {a a' : A} (hne : a ≠ a') :
    AEDisjoint volume {x | x - (a : Space d) ∈ Ω}
      {x | x - (a' : Space d) ∈ Ω} := by
  apply measure_mono_null ?_ (ae_iff.mp h)
  rintro x ⟨hx, hx'⟩ ⟨c, _hc, huniq⟩
  exact hne ((huniq a hx).trans (huniq a' hx').symm)

theorem common_unitVoxel_subset_piece {d : ℕ}
    {S0 S1 S : Finset (Lattice d)} (h0 : S ⊆ S0) (h1 : S ⊆ S1)
    (C1 : Set (Space d)) (c : Space d) {t : Lattice d} (ht : t ∈ S) :
    unitVoxel (c + castLattice t) ⊆
      {x | x - c ∈ if c ∈ C1 then Thickening S1 else Thickening S0} := by
  intro x hx
  have hcube : (x - c) - castLattice t ∈ unitCube d := by
    simpa only [mem_unitVoxel, sub_add_eq_sub_sub] using hx
  by_cases hc : c ∈ C1
  · simp only [hc, ite_eq_left, mem_ofPred_eq]
    exact ⟨t, h1 ht, hcube⟩
  · simp only [hc, mem_ofPred_eq]
    exact ⟨t, h0 ht, hcube⟩

theorem typed_nearby_centers_mem_scaledGrid
    {m : ℕ} (hm : 2 ≤ m) {S0 S1 S : Finset (Lattice 3)}
    (h0 : S ⊆ S0) (h1 : S ⊆ S1) (hdiff : RigidDifferences m S)
    {C C1 : Set (Space 3)} (htile : TypedAETiles (Thickening S0) (Thickening S1) C C1)
    {c c' : C} (hne : c ≠ c') (hclose : ‖(c' : Space 3) - (c : Space 3)‖ ≤ (m : ℝ)) :
    (c' : Space 3) - (c : Space 3) ∈ scaledGrid m := by
  by_contra hnot
  have hcoords : ∀ i, |((c' : Space 3) - (c : Space 3)) i| ≤ (m : ℝ) := by
    intro i
    have hcoord : |((c' : Space 3) - (c : Space 3)) i| ≤
        ‖(c' : Space 3) - (c : Space 3)‖ := by
      simpa only [Real.norm_eq_abs] using
        norm_le_pi_norm ((c' : Space 3) - (c : Space 3)) i
    exact hcoord.trans hclose
  obtain ⟨d, hd, hdiv, hround⟩ :=
    closed_box_rounding m hm ((c' : Space 3) - (c : Space 3)) hcoords hnot
  obtain ⟨t, ht, t', ht', htd⟩ := hdiff d hd hdiv
  have hcorners : ∀ i,
      |((c' : Space 3) + castLattice t') i - ((c : Space 3) + castLattice t) i| < 1 := by
    intro i
    have hid : ((c' : Space 3) + castLattice t') i -
        ((c : Space 3) + castLattice t) i =
        (((c' : Space 3) - (c : Space 3)) i - (d i : ℝ)) := by
      rw [← htd]
      simp only [Pi.add_apply, Pi.sub_apply, castLattice_apply, Int.cast_sub]
      ring
    rw [hid]
    exact hround i
  have hpos := unitVoxel_inter_volume_pos
    ((c : Space 3) + castLattice t) ((c' : Space 3) + castLattice t') hcorners
  have hnull := (htile.aedisjoint hne).mono
    (common_unitVoxel_subset_piece h0 h1 C1 c ht)
    (common_unitVoxel_subset_piece h0 h1 C1 c' ht')
  exact (ne_of_gt hpos) hnull

theorem scaledGrid_eq_zero_of_norm_lt {m : ℕ} (hm : 0 < m)
    {x : Space 3} (hx : x ∈ scaledGrid m) (hnorm : ‖x‖ < (m : ℝ)) : x = 0 := by
  obtain ⟨z, rfl⟩ := mem_scaledGrid.mp hx
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hz : z = 0 := by
    funext i
    have hi : |(m : ℝ) * (z i : ℝ)| < (m : ℝ) := by
      have hle := norm_le_pi_norm ((m : ℝ) • castLattice z) i
      have hle' : |(m : ℝ) * (z i : ℝ)| ≤ ‖(m : ℝ) • castLattice z‖ := by
        simpa only [Pi.smul_apply, smul_eq_mul, castLattice_apply,
          Real.norm_eq_abs] using hle
      exact hle'.trans_lt hnorm
    rw [abs_mul, abs_of_nonneg hmR.le] at hi
    have hzi : |(z i : ℝ)| < 1 := by
      exact (mul_lt_mul_iff_right₀ hmR).mp (by simpa only [mul_one] using hi)
    rw [← Int.cast_abs, ← Int.cast_one, Int.cast_lt] at hzi
    exact Int.abs_lt_one_iff.mp hzi
  simp [hz]

theorem typed_centers_separated
    {m : ℕ} (hm : 2 ≤ m) {S0 S1 S : Finset (Lattice 3)}
    (h0 : S ⊆ S0) (h1 : S ⊆ S1) (hdiff : RigidDifferences m S)
    {C C1 : Set (Space 3)} (htile : TypedAETiles (Thickening S0) (Thickening S1) C C1)
    {c c' : C} (hne : c ≠ c') : (m : ℝ) ≤ ‖(c' : Space 3) - (c : Space 3)‖ := by
  by_contra h
  have hsmall := lt_of_not_ge h
  have hgrid := typed_nearby_centers_mem_scaledGrid hm h0 h1 hdiff htile hne hsmall.le
  have hzero := scaledGrid_eq_zero_of_norm_lt
    (lt_of_lt_of_le (by decide : 0 < 2) hm) hgrid hsmall
  exact hne (Subtype.ext (sub_eq_zero.mp hzero).symm)

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree

theorem rigidSection_rigidDifferences : RigidDifferences 64 rigidSection.Tstar := by
  intro d hbound hdiv
  apply rigidSection_Tstar_difference d
  refine ⟨hbound, ?_⟩
  intro hall
  obtain ⟨i, hi⟩ := hdiv
  exact hi (hall i)

theorem rigidSection_Tstar_subset_T0 : rigidSection.Tstar ⊆ rigidSection.T0 :=
  Finset.erase_subset _ _

theorem rigidSection_Tstar_subset_T1 (w : Lattice 3) :
    rigidSection.Tstar ⊆ rigidSection.T1 w := by
  rw [rigidSection.T1_eq_insert w]
  exact Finset.subset_insert _ _

theorem rigidSection_Tstar_nonempty : rigidSection.Tstar.Nonempty := by
  apply Finset.card_pos.mp
  rw [rigidSection.card_Tstar]
  norm_num

theorem rigidSection_T0_card : rigidSection.T0.card = 64 ^ 3 :=
  rigidSection.card_T0

theorem rigidSection_T1_card (w : Lattice 3) : (rigidSection.T1 w).card = 64 ^ 3 :=
  rigidSection.card_T1 w

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree
namespace CyclicQuotient

abbrev Group (Q : ℕ) := Plane × ZMod Q

def projection (Q : ℕ) : Lattice 3 →+ Group Q where
  toFun z := ((z 0, z 1), (z 2 : ZMod Q))
  map_zero' := by simp
  map_add' x y := by simp

def kernelStep (Q : ℕ) : Lattice 3 := ![0, 0, (Q : ℤ)]

@[simp] theorem projection_kernelStep (Q : ℕ) :
    projection Q (kernelStep Q) = 0 := by
  simp [projection, kernelStep]

theorem kernelStep_ne_zero (Q : ℕ) [NeZero Q] : kernelStep Q ≠ 0 := by
  intro h
  have hz : (Q : ℤ) = 0 := by
    simpa [kernelStep] using congrFun h 2
  exact (NeZero.ne Q) (Int.ofNat_inj.mp hz)

def lift (Q : ℕ) (g : Group Q) : Lattice 3 :=
  ![g.1.1, g.1.2, (g.2.val : ℤ)]

@[simp] theorem projection_lift (Q : ℕ) [NeZero Q] (g : Group Q) :
    projection Q (lift Q g) = g := by
  rcases g with ⟨⟨x, y⟩, r⟩
  simp [projection, lift]

@[simp] theorem lift_zero (Q : ℕ) : lift Q 0 = 0 := by
  ext i
  fin_cases i <;> simp [lift]

theorem projection_surjective (Q : ℕ) [NeZero Q] :
    Function.Surjective (projection Q) :=
  fun g => ⟨lift Q g, projection_lift Q g⟩

theorem lift_injective (Q : ℕ) [NeZero Q] : Function.Injective (lift Q) := by
  intro g h hgh
  have he := congrArg (projection Q) hgh
  simpa only [projection_lift] using he

theorem mem_ker_iff_zsmul_kernelStep (Q : ℕ) (z : Lattice 3) :
    z ∈ (projection Q).ker ↔ ∃ k : ℤ, z = k • kernelStep Q := by
  constructor
  · intro hz
    have hp : projection Q z = 0 := hz
    have h0 : z 0 = 0 := congrArg (fun g : Group Q => g.1.1) hp
    have h1 : z 1 = 0 := congrArg (fun g : Group Q => g.1.2) hp
    have h2 : (z 2 : ZMod Q) = 0 := congrArg (fun g : Group Q => g.2) hp
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (z 2) Q).mp h2
    refine ⟨k, ?_⟩
    ext i
    fin_cases i <;> simp [kernelStep, h0, h1, hk, mul_comm]
  · rintro ⟨k, rfl⟩
    change projection Q (k • kernelStep Q) = 0
    simp only [map_zsmul, projection_kernelStep, zsmul_zero]

def representatives (Q : ℕ) (F : Finset (Group Q)) : Finset (Lattice 3) :=
  F.image (lift Q)

theorem lift_mem_representatives (Q : ℕ) {F : Finset (Group Q)}
    {f : Group Q} (hf : f ∈ F) : lift Q f ∈ representatives Q F :=
  Finset.mem_image_of_mem _ hf

theorem projection_mem_of_mem_representatives (Q : ℕ) [NeZero Q]
    {F : Finset (Group Q)} {u : Lattice 3} (hu : u ∈ representatives Q F) :
    projection Q u ∈ F := by
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hu
  simpa only [projection_lift] using hf

theorem projection_injOn_representatives (Q : ℕ) [NeZero Q]
    (F : Finset (Group Q)) :
    Set.InjOn (projection Q) (representatives Q F : Set (Lattice 3)) := by
  intro u hu v hv huv
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hv
  have hfg : f = g := by simpa only [projection_lift] using huv
  exact congrArg (lift Q) hfg

theorem projection_image_representatives (Q : ℕ) [NeZero Q]
    (F : Finset (Group Q)) :
    (representatives Q F).image (projection Q) = F := by
  ext f
  constructor
  · intro hf
    obtain ⟨u, hu, huf⟩ := Finset.mem_image.mp hf
    rw [← huf]
    exact projection_mem_of_mem_representatives Q hu
  · intro hf
    exact Finset.mem_image.mpr
      ⟨lift Q f, lift_mem_representatives Q hf, projection_lift Q f⟩

theorem zero_mem_representatives (Q : ℕ) {F : Finset (Group Q)}
    (hF : 0 ∈ F) : 0 ∈ representatives Q F := by
  simpa only [lift_zero] using lift_mem_representatives Q hF

theorem eq_zero_of_mem_representatives_mem_ker (Q : ℕ) [NeZero Q]
    {F : Finset (Group Q)} {u : Lattice 3}
    (hu : u ∈ representatives Q F) (hk : u ∈ (projection Q).ker) : u = 0 := by
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hu
  have hf0 : f = 0 := by
    simpa only [AddMonoidHom.mem_ker, projection_lift] using hk
  rw [hf0, lift_zero]

theorem kernelStep_not_mem_representatives (Q : ℕ) [NeZero Q]
    (F : Finset (Group Q)) : kernelStep Q ∉ representatives Q F := by
  intro h
  exact kernelStep_ne_zero Q
    (eq_zero_of_mem_representatives_mem_ker Q h (projection_kernelStep Q))

theorem preimage_tiles (Q : ℕ) [NeZero Q]
    {F : Finset (Group Q)} {A : Set (Group Q)} (h : Tiles F A) :
    Tiles (representatives Q F) ((projection Q) ⁻¹' A) := by
  rw [tiles_iff_unique_tile]
  intro x
  obtain ⟨f, hf, huniq⟩ := (tiles_iff_unique_tile.mp h) (projection Q x)
  refine ⟨⟨lift Q f, lift_mem_representatives Q f.property⟩, ?_, ?_⟩
  · change projection Q (x - lift Q f) ∈ A
    simpa only [map_sub, projection_lift] using hf
  · intro u hu
    have hpu : projection Q u ∈ F :=
      projection_mem_of_mem_representatives Q u.property
    have hp : projection Q x - projection Q u ∈ A := by
      simpa only [Set.mem_preimage, map_sub] using hu
    have he := huniq ⟨projection Q u, hpu⟩ hp
    apply Subtype.ext
    apply projection_injOn_representatives Q F u.property
      (lift_mem_representatives Q f.property)
    simpa only [projection_lift] using congrArg Subtype.val he

theorem period_preimage_of_mem_ker (Q : ℕ) (A : Set (Group Q))
    {k : Lattice 3} (hk : k ∈ (projection Q).ker) :
    Period ((projection Q) ⁻¹' A) k := by
  intro x
  change projection Q (x + k) ∈ A ↔ projection Q x ∈ A
  have hk' : projection Q k = 0 := hk
  simp only [map_add, hk', add_zero]

theorem period_preimage_kernelStep (Q : ℕ) (A : Set (Group Q)) :
    Period ((projection Q) ⁻¹' A) (kernelStep Q) :=
  period_preimage_of_mem_ker Q A (projection_kernelStep Q)

end CyclicQuotient
end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree.MarkedTile

noncomputable section

def periodEquiv {B : Set (Lattice 3)} {w : Lattice 3} (hB : Period B w) : B ≃ B where
  toFun b := ⟨(b : Lattice 3) + w, (hB b).mpr b.property⟩
  invFun b := ⟨(b : Lattice 3) - w, by
    have h := (hB ((b : Lattice 3) - w)).mp
    apply h
    simp [b.property]⟩
  left_inv b := by
    apply Subtype.ext
    change ((b : Lattice 3) + w) - w = (b : Lattice 3)
    exact add_sub_cancel_right _ _
  right_inv b := by
    apply Subtype.ext
    change ((b : Lattice 3) - w) + w = (b : Lattice 3)
    exact sub_add_cancel _ _

@[simp] theorem periodEquiv_apply {B : Set (Lattice 3)} {w : Lattice 3}
    (hB : Period B w) (b : B) : (periodEquiv hB b : Lattice 3) = (b : Lattice 3) + w := rfl

@[simp] theorem periodEquiv_symm_apply {B : Set (Lattice 3)} {w : Lattice 3}
    (hB : Period B w) (b : B) : ((periodEquiv hB).symm b : Lattice 3) = (b : Lattice 3) - w := rfl

def relocate {m : ℕ} {U : Finset (Lattice 3)} {B : Set (Lattice 3)}
    {w : Lattice 3} (hB : Period B w) :
    ((↥U × B) × Residue m) ≃ ((↥U × B) × Residue m) where
  toFun q := if (q.1.1 : Lattice 3) = 0 ∧ q.2 = 0 then
    ((q.1.1, periodEquiv hB q.1.2), q.2) else q
  invFun q := if (q.1.1 : Lattice 3) = 0 ∧ q.2 = 0 then
    ((q.1.1, (periodEquiv hB).symm q.1.2), q.2) else q
  left_inv q := by
    rcases q with ⟨⟨u, b⟩, v⟩
    by_cases h : (u : Lattice 3) = 0 ∧ v = 0 <;> simp [h]
  right_inv q := by
    rcases q with ⟨⟨u, b⟩, v⟩
    by_cases h : (u : Lattice 3) = 0 ∧ v = 0 <;> simp [h]

namespace ResidueSection

variable {m : ℕ} [NeZero m] (s : ResidueSection m)

def baseline {U : Finset (Lattice 3)} {B : Set (Lattice 3)}
    (q : (↥U × B) × Residue m) : Lattice 3 :=
  scale m ((q.1.1 : Lattice 3) + (q.1.2 : Lattice 3)) + s.t q.2

theorem baseline_bijective {U : Finset (Lattice 3)} {B : Set (Lattice 3)}
    (h : Tiles U B) : Function.Bijective (s.baseline (U := U) (B := B)) := by
  constructor
  · rintro ⟨⟨u, b⟩, v⟩ ⟨⟨u', b'⟩, v'⟩ he
    have hc : ((u : Lattice 3) + (b : Lattice 3), v) =
        ((u' : Lattice 3) + (b' : Lattice 3), v') :=
      s.coordinates_injective he
    have hi : (u, b) = (u', b') := h.1 (congrArg Prod.fst hc)
    have hv : v = v' := congrArg (fun p : Lattice 3 × Residue m => p.2) hc
    exact Prod.ext hi hv
  · intro x
    obtain ⟨⟨a, v⟩, hx⟩ := s.coordinates_surjective x
    obtain ⟨⟨u, b⟩, ha⟩ := h.2 a
    refine ⟨((u, b), v), ?_⟩
    change scale m ((u : Lattice 3) + (b : Lattice 3)) + s.t v = x
    change (u : Lattice 3) + (b : Lattice 3) = a at ha
    rw [ha]
    exact hx

def placement {U : Finset (Lattice 3)} {B : Set (Lattice 3)}
    (w : Lattice 3) (q : (↥U × B) × Residue m) : Lattice 3 :=
  s.point w q.1.1 q.2 + scale m q.1.2

theorem placement_eq_baseline_relocate
    {m : ℕ} [NeZero m] (s : ResidueSection m)
    {U : Finset (Lattice 3)}
    {B : Set (Lattice 3)} {w : Lattice 3} (hB : Period B w)
    (q : (↥U × B) × Residue m) :
    s.placement w q = s.baseline (relocate hB q) := by
  classical
  rcases q with ⟨⟨u, b⟩, v⟩
  by_cases h : (u : Lattice 3) = 0 ∧ v = 0
  · simp only [placement, point, relocate, Equiv.coe_fn_mk, baseline,
      h.1, h.2, and_self, ite_true, periodEquiv_apply, zero_add, map_add, t0]
    abel
  · simp only [placement, point, h, ite_false, relocate, Equiv.coe_fn_mk, baseline,
      map_add]
    abel

theorem placement_bijective {U : Finset (Lattice 3)} {B : Set (Lattice 3)}
    {w : Lattice 3} (h : Tiles U B) (hB : Period B w) :
    Function.Bijective (s.placement (U := U) (B := B) w) := by
  have he : s.placement (U := U) (B := B) w = s.baseline ∘ relocate hB := by
    funext q
    exact s.placement_eq_baseline_relocate hB q
  rw [he]
  exact (s.baseline_bijective h).comp (relocate hB).bijective

theorem finalTile_tiles {U : Finset (Lattice 3)} {B : Set (Lattice 3)}
    {w : Lattice 3} (h : Tiles U B) (hB : Period B w) :
    Tiles (s.finalTile w U) ((scale m) '' B) := by
  classical
  have hp := s.placement_bijective h hB
  constructor
  · rintro ⟨⟨t, ht⟩, ⟨c, hc⟩⟩ ⟨⟨t', ht'⟩, ⟨c', hc'⟩⟩ he
    obtain ⟨u, hu, v, hv⟩ := s.mem_finalTile.mp ht
    obtain ⟨u', hu', v', hv'⟩ := s.mem_finalTile.mp ht'
    obtain ⟨b, hb, hbc⟩ := hc
    obtain ⟨b', hb', hbc'⟩ := hc'
    have hi : (((⟨u, hu⟩ : ↥U), (⟨b, hb⟩ : B)), v) =
        (((⟨u', hu'⟩ : ↥U), (⟨b', hb'⟩ : B)), v') := by
      apply hp.1
      change s.point w u v + scale m b = s.point w u' v' + scale m b'
      rw [hv, hv', hbc, hbc']
      exact he
    have htt : t = t' := by
      have hh := congrArg
        (fun q : (↥U × B) × Residue m => s.point w q.1.1 q.2) hi
      simpa only [hv, hv'] using hh
    have hcc : c = c' := by
      have hh := congrArg
        (fun q : (↥U × B) × Residue m => scale m q.1.2) hi
      simpa only [hbc, hbc'] using hh
    exact Prod.ext (Subtype.ext htt) (Subtype.ext hcc)
  · intro x
    obtain ⟨⟨⟨u, b⟩, v⟩, hx⟩ := hp.2 x
    refine ⟨(⟨s.point w u v, s.mem_finalTile.mpr ⟨u, u.property, v, rfl⟩⟩,
      ⟨scale m b, ⟨b, b.property, rfl⟩⟩), ?_⟩
    exact hx

theorem cyclic_finalTile_tiles (Q : ℕ) [NeZero Q]
    {F : Finset (CyclicQuotient.Group Q)} {A : Set (CyclicQuotient.Group Q)}
    (h : Tiles F A) :
    Tiles (s.finalTile (CyclicQuotient.kernelStep Q) (CyclicQuotient.representatives Q F))
      ((scale m) '' ((CyclicQuotient.projection Q) ⁻¹' A)) :=
  s.finalTile_tiles (CyclicQuotient.preimage_tiles Q h)
    (CyclicQuotient.period_preimage_kernelStep Q A)

end ResidueSection
end
end PeriodicTilingThree.MarkedTile

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree.MarkedTile

open Set MeasureTheory

@[simp] theorem castLattice_scale (m : ℕ) (u : Lattice 3) :
    castLattice (scale m u) = scaledCast m u := by
  ext i
  simp [scale, scaledCast, castLattice]

def center (m : ℕ) (a : Space 3) (u : Lattice 3) : Space 3 :=
  a + scaledCast m u

@[simp] theorem center_zero (m : ℕ) (a : Space 3) : center m a 0 = a := by
  simp [center]

def centers (m : ℕ) (U : Finset (Lattice 3)) (A : Set (Space 3)) : Set (Space 3) :=
  Set.range (fun q : A × ↥U => center m q.1 q.2)

theorem mem_centers {m : ℕ} {U : Finset (Lattice 3)} {A : Set (Space 3)}
    {c : Space 3} : c ∈ centers m U A ↔ ∃ a ∈ A, ∃ u ∈ U, center m a u = c := by
  constructor
  · rintro ⟨⟨a, u⟩, h⟩
    exact ⟨a, a.property, u, u.property, h⟩
  · rintro ⟨a, ha, u, hu, h⟩
    exact ⟨(⟨a, ha⟩, ⟨u, hu⟩), h⟩

theorem subset_centers {m : ℕ} {U : Finset (Lattice 3)} (h0 : 0 ∈ U)
    (A : Set (Space 3)) : A ⊆ centers m U A := by
  intro a ha
  exact mem_centers.mpr ⟨a, ha, 0, h0, center_zero m a⟩

namespace ResidueSection

variable {m : ℕ} [NeZero m] (s : ResidueSection m)

def constituent (w u : Lattice 3) : Finset (Lattice 3) :=
  if u = 0 then s.T1 w else s.T0

def part (w u : Lattice 3) : Finset (Lattice 3) :=
  (s.constituent w u).image (fun t => scale m u + t)

theorem mem_part {w u z : Lattice 3} :
    z ∈ s.part w u ↔ ∃ v, s.point w u v = z := by
  classical
  by_cases hu : u = 0
  · subst u
    simp [part, constituent, mem_T1]
  · simp only [part, constituent, hu, ite_false, Finset.mem_image]
    constructor
    · rintro ⟨t, ht, he⟩
      obtain ⟨v, rfl⟩ := s.mem_T0.mp ht
      exact ⟨v, by simpa only [s.point_of_ne_zero w hu] using he⟩
    · rintro ⟨v, hv⟩
      exact ⟨s.t v, s.mem_T0.mpr ⟨v, rfl⟩,
        by simpa only [s.point_of_ne_zero w hu] using hv⟩

theorem part_subset_finalTile {w : Lattice 3} {U : Finset (Lattice 3)}
    {u : Lattice 3} (hu : u ∈ U) : s.part w u ⊆ s.finalTile w U := by
  intro z hz
  obtain ⟨v, hv⟩ := s.mem_part.mp hz
  exact s.mem_finalTile.mpr ⟨u, hu, v, hv⟩

theorem parts_disjoint {w : Lattice 3} {U : Finset (Lattice 3)} (hw : w ∉ U)
    {u u' : ↥U} (hne : u ≠ u') : Disjoint (s.part w u) (s.part w u') := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨v, hv⟩ := s.mem_part.mp hz
  obtain ⟨v', hv'⟩ := s.mem_part.mp hz'
  have hp : (u, v) = (u', v') := s.point_injective hw (hv.trans hv'.symm)
  exact hne (congrArg Prod.fst hp)

theorem mem_thickening_part {w u : Lattice 3} {x : Space 3} :
    x ∈ Thickening (s.part w u) ↔
      x - scaledCast m u ∈ Thickening (s.constituent w u) := by
  classical
  constructor
  · rintro ⟨z, hz, hx⟩
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
    refine ⟨t, ht, ?_⟩
    simpa only [map_add, castLattice_scale, sub_add_eq_sub_sub] using hx
  · rintro ⟨t, ht, hx⟩
    refine ⟨scale m u + t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, ?_⟩
    simpa only [map_add, castLattice_scale, sub_add_eq_sub_sub] using hx

theorem mem_translated_part {w u : Lattice 3} {a x : Space 3} :
    x - a ∈ Thickening (s.part w u) ↔
      x - center m a u ∈ Thickening (s.constituent w u) := by
  simpa only [center, sub_add_eq_sub_sub] using
    (s.mem_thickening_part (w := w) (u := u) (x := x - a))

theorem mem_thickening_finalTile {w : Lattice 3} {U : Finset (Lattice 3)}
    {x : Space 3} :
    x ∈ Thickening (s.finalTile w U) ↔
      ∃ u : ↥U, x ∈ Thickening (s.part w u) := by
  constructor
  · rintro ⟨z, hz, hx⟩
    obtain ⟨u, hu, v, hv⟩ := s.mem_finalTile.mp hz
    exact ⟨⟨u, hu⟩, z, s.mem_part.mpr ⟨v, hv⟩, hx⟩
  · rintro ⟨u, z, hz, hx⟩
    exact ⟨z, s.part_subset_finalTile u.property hz, hx⟩

theorem mem_translated_finalTile {w : Lattice 3} {U : Finset (Lattice 3)}
    {a x : Space 3} :
    x - a ∈ Thickening (s.finalTile w U) ↔
      ∃ u : ↥U, x - center m a u ∈ Thickening (s.constituent w u) := by
  rw [s.mem_thickening_finalTile]
  exact exists_congr fun u => s.mem_translated_part

theorem Tstar_subset_constituent (w u : Lattice 3) :
    s.Tstar ⊆ s.constituent w u := by
  classical
  intro z hz
  by_cases hu : u = 0
  · simp only [constituent, hu, ite_true, s.T1_eq_insert]
    exact Finset.mem_insert_of_mem hz
  · simpa only [constituent, hu, ite_false] using (Finset.mem_erase.mp hz).2

theorem Tstar_nonempty (hm : 2 ≤ m) : s.Tstar.Nonempty := by
  apply Finset.card_pos.mp
  rw [s.card_Tstar]
  have hp := Nat.pow_le_pow_left hm 3
  exact Nat.sub_pos_of_lt ((by decide : 1 < 2 ^ 3).trans_le hp)

theorem common_voxel_subset_constituent (w u : Lattice 3) (a : Space 3)
    {t : Lattice 3} (ht : t ∈ s.Tstar) :
    unitVoxel (center m a u + castLattice t) ⊆
      {x | x - center m a u ∈ Thickening (s.constituent w u)} := by
  intro x hx
  refine ⟨t, s.Tstar_subset_constituent w u ht, ?_⟩
  simpa only [mem_unitVoxel, sub_add_eq_sub_sub] using hx

end ResidueSection
end PeriodicTilingThree.MarkedTile

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

open Set MeasureTheory

theorem AETiles.eq_of_voxel_close {d : ℕ} {F : Finset (Lattice d)}
    {A : Set (Space d)} (h : AETiles (Thickening F) A)
    {z : Lattice d} (hz : z ∈ F) {a b : A}
    (hc : ∀ i, |(b : Space d) i - (a : Space d) i| < 1) : a = b := by
  by_contra hne
  have hpos := unitVoxel_inter_volume_pos
    ((a : Space d) + castLattice z) ((b : Space d) + castLattice z) (by
      intro i
      simpa only [Pi.add_apply, add_sub_add_right_eq_sub] using hc i)
  have hsub : ∀ c : A, unitVoxel ((c : Space d) + castLattice z) ⊆
      {x | x - (c : Space d) ∈ Thickening F} := by
    intro c x hx
    refine ⟨z, hz, ?_⟩
    simpa only [mem_unitVoxel, sub_add_eq_sub_sub] using hx
  have hnull := (h.aedisjoint hne).mono (hsub a) (hsub b)
  exact (ne_of_gt hpos) hnull

theorem AETiles.floor_injective {d : ℕ} {F : Finset (Lattice d)}
    {A : Set (Space d)} (h : AETiles (Thickening F) A) (hF : F.Nonempty) :
    Function.Injective (fun a : A => (fun i => ⌊(a : Space d) i⌋ : Lattice d)) := by
  obtain ⟨z, hz⟩ := hF
  intro a b he
  apply h.eq_of_voxel_close hz
  intro i
  have hi : ⌊(a : Space d) i⌋ = ⌊(b : Space d) i⌋ := congrFun he i
  have ha := Int.floor_le ((a : Space d) i)
  have ha' := Int.lt_floor_add_one ((a : Space d) i)
  have hb := Int.floor_le ((b : Space d) i)
  have hb' := Int.lt_floor_add_one ((b : Space d) i)
  rw [hi] at ha ha'
  apply abs_lt.mpr
  constructor <;> linarith

theorem AETiles.countable_of_thickening {d : ℕ} {F : Finset (Lattice d)}
    {A : Set (Space d)} (h : AETiles (Thickening F) A) (hF : F.Nonempty) :
    A.Countable :=
  Set.countable_coe_iff.mp (h.floor_injective hF).countable

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree.MarkedTile

open Set MeasureTheory Filter

namespace ResidueSection

variable {m : ℕ} [NeZero m] (s : ResidueSection m)

theorem translated_parts_unique_ae {w : Lattice 3} {U : Finset (Lattice 3)}
    (hw : w ∉ U) (a : Space 3) (u u' : ↥U) :
    ∀ᵐ x ∂volume,
      x - center m a u ∈ Thickening (s.constituent w u) →
      x - center m a u' ∈ Thickening (s.constituent w u') → u = u' := by
  classical
  by_cases he : u = u'
  · exact Eventually.of_forall (fun _ _ _ => he)
  · have hnull := thickening_inter_measure_zero_of_disjoint (s.parts_disjoint hw he)
    have havoid : ∀ᵐ x ∂volume,
        x ∉ Thickening (s.part w u) ∩ Thickening (s.part w u') :=
      compl_mem_ae_iff.mpr hnull
    have hshift := (measurePreserving_sub_right volume a).quasiMeasurePreserving.ae havoid
    filter_upwards [hshift] with x hx
    intro hu hu'
    exact False.elim (hx ⟨s.mem_translated_part.mpr hu,
      s.mem_translated_part.mpr hu'⟩)

theorem indexed_constituents_ae {w : Lattice 3} {U : Finset (Lattice 3)}
    (h0 : 0 ∈ U) (hw : w ∉ U) {A : Set (Space 3)}
    (htile : AETiles (Thickening (s.finalTile w U)) A) :
    ∀ᵐ x ∂volume, ∃! q : A × ↥U,
      x - center m q.1 q.2 ∈ Thickening (s.constituent w q.2) := by
  classical
  have hcount := htile.countable_of_thickening (s.finalTile_nonempty w h0)
  let : Countable A := hcount.to_subtype
  have hall : ∀ᵐ x ∂volume, ∀ (a : A) (u u' : ↥U),
      x - center m a u ∈ Thickening (s.constituent w u) →
      x - center m a u' ∈ Thickening (s.constituent w u') → u = u' := by
    apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro u
    apply ae_all_iff.mpr
    intro u'
    exact s.translated_parts_unique_ae hw a u u'
  filter_upwards [htile, hall] with x hx hpieces
  obtain ⟨a, ha, haunique⟩ := hx
  obtain ⟨u, hu⟩ := s.mem_translated_finalTile.mp ha
  refine ⟨(a, u), hu, ?_⟩
  rintro ⟨a', u'⟩ hq
  have ha' : a' = a := haunique a' (s.mem_translated_finalTile.mpr ⟨u', hq⟩)
  subst a'
  exact Prod.ext rfl (hpieces a u' u hq hu)

theorem center_injective {w : Lattice 3} {U : Finset (Lattice 3)}
    (hm : 2 ≤ m) (h0 : 0 ∈ U) (hw : w ∉ U) {A : Set (Space 3)}
    (htile : AETiles (Thickening (s.finalTile w U)) A) :
    Function.Injective (fun q : A × ↥U => center m q.1 q.2) := by
  classical
  have hcover := s.indexed_constituents_ae h0 hw htile
  obtain ⟨t, ht⟩ := s.Tstar_nonempty hm
  intro q q' he
  by_contra hne
  have hnull : volume (unitVoxel (center m q.1 q.2 + castLattice t)) = 0 := by
    apply measure_mono_null ?_ (ae_iff.mp hcover)
    intro x hx huniq
    obtain ⟨r, _hr, hruniq⟩ := huniq
    have hq : x - center m q.1 q.2 ∈ Thickening (s.constituent w q.2) :=
      s.common_voxel_subset_constituent w q.2 q.1 ht hx
    have hq' : x - center m q'.1 q'.2 ∈ Thickening (s.constituent w q'.2) := by
      apply s.common_voxel_subset_constituent w q'.2 q'.1 ht
      simpa only [he] using hx
    exact hne ((hruniq q hq).trans (hruniq q' hq').symm)
  rw [unitVoxel_volume] at hnull
  exact one_ne_zero hnull

theorem center_mem_A_iff
    {m : ℕ} [NeZero m]
    {U : Finset (Lattice 3)} (h0 : 0 ∈ U)
    {A : Set (Space 3)}
    (hinj : Function.Injective (fun q : A × ↥U => center m q.1 q.2))
    (q : A × ↥U) : center m q.1 q.2 ∈ A ↔ (q.2 : Lattice 3) = 0 := by
  constructor
  · intro hc
    have he : q = ((⟨center m q.1 q.2, hc⟩ : A), (⟨0, h0⟩ : ↥U)) := by
      apply hinj
      simp
    exact congrArg (fun p : A × ↥U => (p.2 : Lattice 3)) he
  · intro hu
    simpa only [hu, center_zero] using q.1.property

open scoped Classical in
theorem constituent_type_eq {w : Lattice 3} {U : Finset (Lattice 3)} (h0 : 0 ∈ U)
    {A : Set (Space 3)}
    (hinj : Function.Injective (fun q : A × ↥U => center m q.1 q.2))
    (q : A × ↥U) :
    (if center m q.1 q.2 ∈ A then Thickening (s.T1 w) else Thickening s.T0) =
      Thickening (s.constituent w q.2) := by
  classical
  by_cases hu : (q.2 : Lattice 3) = 0
  · rw [ite_eq_left ((center_mem_A_iff h0 hinj q).mpr hu)]
    simp only [constituent, ite_eq_left hu]
  · have hc : center m q.1 q.2 ∉ A := fun h => hu ((center_mem_A_iff h0 hinj q).mp h)
    simp only [hc, ite_false, constituent, hu]

theorem typed_constituents {w : Lattice 3} {U : Finset (Lattice 3)}
    (hm : 2 ≤ m) (h0 : 0 ∈ U) (hw : w ∉ U) {A : Set (Space 3)}
    (htile : AETiles (Thickening (s.finalTile w U)) A) :
    TypedAETiles (Thickening s.T0) (Thickening (s.T1 w)) (centers m U A) A := by
  classical
  have hinj := s.center_injective hm h0 hw htile
  have hcover := s.indexed_constituents_ae h0 hw htile
  filter_upwards [hcover] with x hx
  obtain ⟨q, hq, hqunique⟩ := hx
  let c : centers m U A := ⟨center m q.1 q.2, ⟨q, rfl⟩⟩
  refine ⟨c, ?_, ?_⟩
  · change x - center m q.1 q.2 ∈
      if center m q.1 q.2 ∈ A then Thickening (s.T1 w) else Thickening s.T0
    rw [s.constituent_type_eq h0 hinj q]
    exact hq
  · intro c' hc'
    obtain ⟨q', he⟩ := c'.property
    change center m q'.1 q'.2 = (c' : Space 3) at he
    have hq' : x - center m q'.1 q'.2 ∈ Thickening (s.constituent w q'.2) := by
      rw [← s.constituent_type_eq h0 hinj q', he]
      exact hc'
    have hqq := hqunique q' hq'
    apply Subtype.ext
    change (c' : Space 3) = center m q.1 q.2
    rw [← he, hqq]

end ResidueSection

theorem period_centers {m : ℕ} {U : Finset (Lattice 3)} {A : Set (Space 3)}
    {v : Space 3} (hA : Period A v) : Period (centers m U A) v := by
  intro c
  constructor
  · intro hc
    obtain ⟨a, ha, u, hu, he⟩ := mem_centers.mp hc
    have hav : a - v ∈ A := (hA (a - v)).mp (by simpa using ha)
    refine mem_centers.mpr ⟨a - v, hav, u, hu, ?_⟩
    calc
      center m (a - v) u = center m a u - v := by unfold center; abel
      _ = c := by rw [he]; abel
  · intro hc
    obtain ⟨a, ha, u, hu, he⟩ := mem_centers.mp hc
    refine mem_centers.mpr ⟨a + v, (hA a).mpr ha, u, hu, ?_⟩
    calc
      center m (a + v) u = center m a u + v := by unfold center; abel
      _ = c + v := by rw [he]

theorem fullyPeriodic_centers {m : ℕ} {U : Finset (Lattice 3)} {A : Set (Space 3)}
    (hA : EuclideanFullyPeriodic A) : EuclideanFullyPeriodic (centers m U A) := by
  obtain ⟨b, hb⟩ := hA
  exact ⟨b, fun v hv => period_centers (hb v hv)⟩

theorem tiles_of_centers_grid {m : ℕ} {U : Finset (Lattice 3)} {A : Set (Space 3)}
    {c0 : Space 3}
    (hinj : Function.Injective (fun q : A × ↥U => center m q.1 q.2))
    (hgrid : centers m U A = Set.range (fun z : Lattice 3 => c0 + scaledCast m z)) :
    Tiles U {z : Lattice 3 | c0 + scaledCast m z ∈ A} := by
  classical
  rw [tiles_iff_unique_tile]
  intro z
  have hz : c0 + scaledCast m z ∈ centers m U A := by
    rw [hgrid]
    exact ⟨z, rfl⟩
  obtain ⟨q, hq⟩ := hz
  have hd : c0 + scaledCast m (z - (q.2 : Lattice 3)) = (q.1 : Space 3) := by
    have he : (q.1 : Space 3) + scaledCast m (q.2 : Lattice 3) =
        c0 + scaledCast m z := hq
    rw [map_sub]
    calc
      c0 + (scaledCast m z - scaledCast m (q.2 : Lattice 3)) =
          (c0 + scaledCast m z) - scaledCast m (q.2 : Lattice 3) := by abel
      _ = (q.1 : Space 3) := by rw [← he]; abel
  refine ⟨q.2, ?_, ?_⟩
  · change c0 + scaledCast m (z - (q.2 : Lattice 3)) ∈ A
    rw [hd]
    exact q.1.property
  · intro u hu
    let a : A := ⟨c0 + scaledCast m (z - (u : Lattice 3)), hu⟩
    have hc : center m a u = c0 + scaledCast m z := by
      change (c0 + scaledCast m (z - (u : Lattice 3))) + scaledCast m u = _
      rw [map_sub]
      abel
    have he : (a, u) = q := hinj (hc.trans hq.symm)
    exact congrArg Prod.snd he

end PeriodicTilingThree.MarkedTile

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree.MarkedTile

open MeasureTheory
open scoped Classical

private theorem cast_scale_eq (m : ℕ) (z : Lattice 3) :
    castLattice (scale m z) = scaledCast m z := by
  ext i
  simp [scaledCast, scale]

namespace ResidueSection

variable {m : ℕ} [NeZero m] (s : ResidueSection m)

theorem Tstar_subset_T0 : s.Tstar ⊆ s.T0 := Finset.erase_subset _ _

theorem Tstar_subset_T1 (w : Lattice 3) : s.Tstar ⊆ s.T1 w := by
  rw [s.T1_eq_insert w]
  exact Finset.subset_insert _ _

theorem marked_cell_mem_thickening_iff
    {m : ℕ} [NeZero m] (s : ResidueSection m)
    {a g : Lattice 3} {x : Space 3}
    (hx : x ∈ openUnitVoxel (castLattice (scale m a + s.t0)))
    (F : Finset (Lattice 3)) :
    x - scaledCast m g ∈ Thickening F ↔
      ∃ z ∈ F, scale m g + z = scale m a + s.t0 := by
  have he (z : Lattice 3) :
      x - castLattice (scale m g + z) =
        (x - scaledCast m g) - castLattice z := by
    rw [map_add, cast_scale_eq]
    abel
  constructor
  · rintro ⟨z, hz, hcell⟩
    refine ⟨z, hz, (mem_unitVoxel_cast_iff_of_mem_open hx).mp ?_⟩
    change x - castLattice (scale m g + z) ∈ unitCube 3
    rwa [he z]
  · rintro ⟨z, hz, hcorner⟩
    refine ⟨z, hz, ?_⟩
    have hcell := (mem_unitVoxel_cast_iff_of_mem_open hx).mpr hcorner
    change x - castLattice (scale m g + z) ∈ unitCube 3 at hcell
    rwa [he z] at hcell

theorem marked_cell_T0_iff {a g : Lattice 3} {x : Space 3}
    (hx : x ∈ openUnitVoxel (castLattice (scale m a + s.t0))) :
    x - scaledCast m g ∈ Thickening s.T0 ↔ g = a := by
  rw [s.marked_cell_mem_thickening_iff hx]
  constructor
  · rintro ⟨z, hz, he⟩
    obtain ⟨v, hv⟩ := s.mem_T0.mp hz
    rw [← hv] at he
    have hp : (g, v) = (a, (0 : Residue m)) := by
      apply s.coordinates_injective
      exact he
    exact congrArg Prod.fst hp
  · rintro rfl
    exact ⟨s.t0, s.t0_mem_T0, rfl⟩

theorem marked_cell_T1_iff (w : Lattice 3) {a g : Lattice 3} {x : Space 3}
    (hx : x ∈ openUnitVoxel (castLattice (scale m a + s.t0))) :
    x - scaledCast m g ∈ Thickening (s.T1 w) ↔ g = a - w := by
  rw [s.marked_cell_mem_thickening_iff hx]
  constructor
  · rintro ⟨z, hz, he⟩
    obtain ⟨v, hv⟩ := s.mem_T1.mp hz
    rw [← hv] at he
    have hv0 : v = 0 := by
      have hr := congrArg (residue m) he
      simpa only [map_add, residue_scale, s.residue_t1, s.residue_t0,
        zero_add] using hr
    subst v
    have hga : g + w = a := by
      apply scale_injective m
      apply add_right_cancel (b := s.t0)
      simpa only [t1, ite_eq_left rfl, ite_true, map_add, add_assoc] using he
    exact eq_sub_iff_add_eq.mpr hga
  · rintro rfl
    refine ⟨s.t1 w 0, s.mem_T1.mpr ⟨0, rfl⟩, ?_⟩
    simp only [t1, ite_true]
    rw [← add_assoc, ← map_add, sub_add_cancel]

theorem marked_cell_sources (w : Lattice 3) (B : Set (Lattice 3))
    {a g : Lattice 3} {x : Space 3}
    (hx : x ∈ openUnitVoxel (castLattice (scale m a + s.t0))) :
    (x - scaledCast m g ∈ if g ∈ B then Thickening (s.T1 w) else Thickening s.T0) ↔
      (g = a ∧ g ∉ B) ∨ (g = a - w ∧ g ∈ B) := by
  by_cases hg : g ∈ B
  · simp only [hg, ite_eq_left, not_true_eq_false, and_false, false_or, and_true,
      s.marked_cell_T1_iff w hx]
  · simp only [hg, ite_false, not_false_eq_true, and_true, and_false, or_false,
      s.marked_cell_T0_iff hx]

theorem period_of_marked_cells (w : Lattice 3) (hw : w ≠ 0)
    (B : Set (Lattice 3))
    (hcover : ∀ᵐ x ∂volume, ∃! g : Lattice 3,
      x - scaledCast m g ∈
        if g ∈ B then Thickening (s.T1 w) else Thickening s.T0) :
    Period B w := by
  have hiff : ∀ a : Lattice 3, a ∈ B ↔ a - w ∈ B := by
    intro a
    have hvol : volume (openUnitVoxel (castLattice (scale m a + s.t0))) ≠ 0 := by
      rw [openUnitVoxel_volume]
      exact one_ne_zero
    obtain ⟨x, hx, hgcover⟩ :=
      Measure.exists_mem_of_measure_ne_zero_of_ae hvol (ae_restrict_of_ae hcover)
    obtain ⟨g, hg, huniq⟩ := hgcover
    constructor
    · intro ha
      rcases (s.marked_cell_sources w B hx).mp hg with ⟨hga, hgB⟩ | ⟨hga, hgB⟩
      · exact False.elim (hgB (hga.symm ▸ ha))
      · exact hga ▸ hgB
    · intro haw
      by_contra ha
      have hpa : x - scaledCast m a ∈
          if a ∈ B then Thickening (s.T1 w) else Thickening s.T0 :=
        (s.marked_cell_sources w B hx).mpr (Or.inl ⟨rfl, ha⟩)
      have hpaw : x - scaledCast m (a - w) ∈
          if a - w ∈ B then Thickening (s.T1 w) else Thickening s.T0 :=
        (s.marked_cell_sources w B hx).mpr (Or.inr ⟨rfl, haw⟩)
      have he : a = a - w := (huniq a hpa).trans (huniq (a - w) hpaw).symm
      apply hw
      calc
        w = a - (a - w) := by abel
        _ = a - a := by rw [← he]
        _ = 0 := sub_self a
  intro z
  simpa only [add_sub_cancel_right] using hiff (z + w)

theorem kernel_periods_of_marked_cells (Q : ℕ) [NeZero Q]
    (B : Set (Lattice 3))
    (hcover : ∀ᵐ x ∂volume, ∃! g : Lattice 3,
      x - scaledCast m g ∈ if g ∈ B then
        Thickening (s.T1 (CyclicQuotient.kernelStep Q)) else Thickening s.T0) :
    ∀ k ∈ (CyclicQuotient.projection Q).ker, Period B k := by
  have hw := s.period_of_marked_cells (CyclicQuotient.kernelStep Q)
    (CyclicQuotient.kernelStep_ne_zero Q) B hcover
  intro k hk
  obtain ⟨n, rfl⟩ := (CyclicQuotient.mem_ker_iff_zsmul_kernelStep Q k).mp hk
  exact (periodSubgroup B).zsmul_mem hw n

end ResidueSection
end PeriodicTilingThree.MarkedTile

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

def centerBoxIndex {n : ℕ} (r : ℝ) (x : Space n) : Lattice n :=
  fun i => ⌊x i / r⌋

theorem norm_sub_lt_of_centerBoxIndex_eq {n : ℕ} {r : ℝ} (hr : 0 < r)
    {x y : Space n} (hxy : centerBoxIndex r x = centerBoxIndex r y) :
    ‖x - y‖ < r := by
  apply (pi_norm_lt_iff hr).mpr
  intro i
  have heq : ⌊x i / r⌋ = ⌊y i / r⌋ := congrFun hxy i
  have hxl := Int.floor_le (x i / r)
  have hxu := Int.lt_floor_add_one (x i / r)
  have hyl := Int.floor_le (y i / r)
  have hyu := Int.lt_floor_add_one (y i / r)
  rw [← heq] at hyl hyu
  have hxl' := (le_div_iff₀ hr).mp hxl
  have hxu' := (div_lt_iff₀ hr).mp hxu
  have hyl' := (le_div_iff₀ hr).mp hyl
  have hyu' := (div_lt_iff₀ hr).mp hyu
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  apply abs_lt.mpr
  constructor <;> nlinarith

theorem centerBoxIndex_injOn {n : ℕ} {C : Set (Space n)} {r : ℝ}
    (hr : 0 < r) (hsep : C.Pairwise (fun x y => r ≤ ‖x - y‖)) :
    Set.InjOn (centerBoxIndex r) C := by
  intro x hx y hy hxy
  by_contra hne
  exact (not_lt_of_ge (hsep hx hy hne)) (norm_sub_lt_of_centerBoxIndex_eq hr hxy)

theorem centers_countable {n : ℕ} {C : Set (Space n)} {r : ℝ}
    (hr : 0 < r) (hsep : C.Pairwise (fun x y => r ≤ ‖x - y‖)) : C.Countable := by
  apply Set.countable_of_injective_of_countable_image (centerBoxIndex_injOn hr hsep)
  exact Set.to_countable _

theorem centerBoxIndex_image_finite {n : ℕ} {r : ℝ} (hr : 0 < r)
    {K : Set (Space n)} (hK : Bornology.IsBounded K) :
    (centerBoxIndex r '' K).Finite := by
  obtain ⟨R, hR⟩ := hK.exists_norm_le
  let lo : Lattice n := fun _ => ⌊-R / r⌋
  let hi : Lattice n := fun _ => ⌊R / r⌋
  apply (Set.finite_Icc lo hi).subset
  rintro z ⟨x, hx, rfl⟩
  have hcoord (i : Fin n) : |x i| ≤ R := by
    calc
      |x i| = ‖x i‖ := by simp only [Real.norm_eq_abs]
      _ ≤ ‖x‖ := norm_le_pi_norm x i
      _ ≤ R := hR x hx
  constructor
  · intro i
    change ⌊-R / r⌋ ≤ ⌊x i / r⌋
    exact Int.floor_mono (div_le_div_of_nonneg_right (abs_le.mp (hcoord i)).1 hr.le)
  · intro i
    change ⌊x i / r⌋ ≤ ⌊R / r⌋
    exact Int.floor_mono (div_le_div_of_nonneg_right (abs_le.mp (hcoord i)).2 hr.le)

theorem centers_finite_on_bounded {n : ℕ} {C K : Set (Space n)} {r : ℝ}
    (hr : 0 < r) (hsep : C.Pairwise (fun x y => r ≤ ‖x - y‖))
    (hK : Bornology.IsBounded K) : (C ∩ K).Finite := by
  have hfin : (centerBoxIndex r '' (C ∩ K)).Finite :=
    (centerBoxIndex_image_finite hr hK).subset (Set.image_mono Set.inter_subset_right)
  exact hfin.of_finite_image ((centerBoxIndex_injOn hr hsep).mono Set.inter_subset_left)

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

open Set MeasureTheory

section Topological

variable {X : Type uX} {I : Type uI} [TopologicalSpace X] [PreconnectedSpace X]

def CoverIntersects (K : I → Set X) (i j : I) : Prop :=
  (K i ∩ K j).Nonempty

theorem closed_cover_chain_connected (K : I → Set X)
    (hne : ∀ i, (K i).Nonempty) (hclosed : ∀ i, IsClosed (K i))
    (hlocal : LocallyFinite K) (hcover : ∀ x : X, ∃ i, x ∈ K i)
    (i₀ j : I) : Relation.ReflTransGen (CoverIntersects K) i₀ j := by
  classical
  let R : I → Prop := Relation.ReflTransGen (CoverIntersects K) i₀
  let A : Set X := ⋃ i : {i // R i}, K i.val
  let B : Set X := ⋃ i : {i // ¬ R i}, K i.val
  have hA : IsClosed A :=
    (hlocal.comp_injective (g := fun i : {i // R i} => i.val)
      Subtype.val_injective).isClosed_iUnion (fun i => hclosed i.val)
  have hB : IsClosed B :=
    (hlocal.comp_injective (g := fun i : {i // ¬ R i} => i.val)
      Subtype.val_injective).isClosed_iUnion (fun i => hclosed i.val)
  have hab : (univ : Set X) ⊆ A ∪ B := by
    intro x _
    obtain ⟨i, hxi⟩ := hcover x
    by_cases hi : R i
    · exact Or.inl (mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩)
  have hAnonempty : ((univ : Set X) ∩ A).Nonempty := by
    obtain ⟨x, hx⟩ := hne i₀
    exact ⟨x, mem_univ x,
      mem_iUnion.mpr ⟨⟨i₀, Relation.ReflTransGen.refl⟩, hx⟩⟩
  by_contra hj
  have hBnonempty : ((univ : Set X) ∩ B).Nonempty := by
    obtain ⟨x, hx⟩ := hne j
    exact ⟨x, mem_univ x, mem_iUnion.mpr ⟨⟨j, hj⟩, hx⟩⟩
  obtain ⟨x, _, hxA, hxB⟩ :=
    isPreconnected_closed_iff.mp isPreconnected_univ A B hA hB hab hAnonempty hBnonempty
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hxA
  obtain ⟨k, hxk⟩ := mem_iUnion.mp hxB
  exact k.property (i.property.tail ⟨x, hxi, hxk⟩)

end Topological

section Measure

variable {X : Type uX} {I : Type uI} [TopologicalSpace X] [MeasurableSpace X]
variable (μ : Measure X) [MeasureTheory.Measure.IsOpenPosMeasure μ]

theorem closed_locallyFinite_cover_of_ae (K : I → Set X)
    (hclosed : ∀ i, IsClosed (K i)) (hlocal : LocallyFinite K)
    (hcover : ∀ᵐ x ∂μ, ∃ i, x ∈ K i) : ∀ x, ∃ i, x ∈ K i := by
  have hc : IsClosed (⋃ i, K i) := hlocal.isClosed_iUnion hclosed
  have hae : ∀ᵐ x ∂μ, x ∈ ⋃ i, K i :=
    hcover.mono fun _ hx => mem_iUnion.mpr hx
  have hnull : μ (⋃ i, K i)ᶜ = 0 := mem_ae_iff.mp hae
  have hempty : (⋃ i, K i)ᶜ = ∅ :=
    (hc.isOpen_compl.measure_eq_zero_iff μ).mp hnull
  have huniv : (⋃ i, K i) = univ := Set.compl_empty_iff.mp hempty
  intro x
  exact mem_iUnion.mp (by rw [huniv]; exact mem_univ x)

end Measure

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

open Set MeasureTheory
open scoped ENNReal

def auxiliaryCube (m : ℕ) (c : Space 3) : Set (Space 3) :=
  Metric.closedBall c ((m : ℝ) / 2)

theorem auxiliaryCube_isClosed (m : ℕ) (c : Space 3) :
    IsClosed (auxiliaryCube m c) := Metric.isClosed_closedBall

theorem auxiliaryCube_measurableSet (m : ℕ) (c : Space 3) :
    MeasurableSet (auxiliaryCube m c) := (auxiliaryCube_isClosed m c).measurableSet

theorem auxiliaryCube_nonempty (m : ℕ) (c : Space 3) :
    (auxiliaryCube m c).Nonempty :=
  ⟨c, Metric.mem_closedBall_self (by positivity)⟩

theorem auxiliaryCube_volume (m : ℕ) (c : Space 3) :
    volume (auxiliaryCube m c) = ((m ^ 3 : ℕ) : ℝ≥0∞) := by
  rw [auxiliaryCube, closedBall_volume c (by positivity)]
  rw [show 2 * ((m : ℝ) / 2) = (m : ℝ) by ring]
  rw [ENNReal.ofReal_pow (Nat.cast_nonneg m) 3, ENNReal.ofReal_natCast]
  simp only [Nat.cast_pow]

theorem auxiliaryCube_translate (m : ℕ) (c : Space 3) :
    {x : Space 3 | x - c ∈ auxiliaryCube m 0} = auxiliaryCube m c := by
  ext x
  simp only [mem_ofPred_eq, auxiliaryCube, Metric.mem_closedBall,
    dist_eq_norm, sub_zero]

theorem auxiliaryCube_aedisjoint {m : ℕ} (hm : 0 < m)
    {c c' : Space 3} (hsep : (m : ℝ) ≤ ‖c - c'‖) :
    AEDisjoint volume (auxiliaryCube m c) (auxiliaryCube m c') := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hballs : Disjoint (Metric.ball c ((m : ℝ) / 2))
      (Metric.ball c' ((m : ℝ) / 2)) := by
    apply Metric.ball_disjoint_ball
    rw [dist_eq_norm]
    linarith
  exact hballs.aedisjoint.congr
    (closedBall_ae_eq_ball c (by positivity))
    (closedBall_ae_eq_ball c' (by positivity))

theorem auxiliaryCube_inter_norm_le {m : ℕ} {c c' : Space 3}
    (h : (auxiliaryCube m c ∩ auxiliaryCube m c').Nonempty) :
    ‖c' - c‖ ≤ (m : ℝ) := by
  obtain ⟨x, hx, hx'⟩ := h
  have hxle : dist x c ≤ (m : ℝ) / 2 := hx
  have hxle' : dist x c' ≤ (m : ℝ) / 2 := hx'
  have ht := dist_triangle c' x c
  rw [dist_comm c' x, dist_eq_norm c' c] at ht
  linarith

theorem auxiliaryCube_locallyFinite (m : ℕ) (C : Set (Space 3))
    (hfin : ∀ K : Set (Space 3), Bornology.IsBounded K → (C ∩ K).Finite) :
    LocallyFinite (fun c : C => auxiliaryCube m c) := by
  intro x
  have hindex : {c : C | (c : Space 3) ∈
      Metric.closedBall x ((m : ℝ) / 2 + 1)}.Finite := by
    have hf := Set.Finite.preimage
      (f := fun c : C => (c : Space 3)) Subtype.val_injective.injOn
      (hfin (Metric.closedBall x ((m : ℝ) / 2 + 1)) Metric.isBounded_closedBall)
    exact hf.subset fun c hc => ⟨c.property, hc⟩
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x (by norm_num), hindex.subset ?_⟩
  rintro c ⟨y, hy, hyx⟩
  have hyc : dist y (c : Space 3) ≤ (m : ℝ) / 2 := hy
  have hyx' : dist y x < 1 := hyx
  change dist (c : Space 3) x ≤ (m : ℝ) / 2 + 1
  have ht := dist_triangle (c : Space 3) y x
  rw [dist_comm (c : Space 3) y] at ht
  linarith

theorem auxiliaryCube_cover_of_ae (m : ℕ) (C : Set (Space 3))
    (hfin : ∀ K : Set (Space 3), Bornology.IsBounded K → (C ∩ K).Finite)
    (hcover : ∀ᵐ x ∂volume, ∃ c : C, x ∈ auxiliaryCube m c) :
    ∀ x, ∃ c : C, x ∈ auxiliaryCube m c :=
  closed_locallyFinite_cover_of_ae volume (fun c : C => auxiliaryCube m c)
    (fun c => auxiliaryCube_isClosed m c) (auxiliaryCube_locallyFinite m C hfin) hcover

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Set MeasureTheory
open scoped Pointwise ENNReal

namespace PeriodicTilingThree.PeriodicVolume

variable {d : ℕ}

def representatives (b : Module.Basis (Fin d) ℝ (Space d)) (C : Set (Space d)) : Set (Space d) :=
  C ∩ ZSpan.fundamentalDomain b

theorem representatives_finite (b : Module.Basis (Fin d) ℝ (Space d)) (C : Set (Space d))
    (hfin : ∀ K : Set (Space d), Bornology.IsBounded K → (C ∩ K).Finite) :
    (representatives b C).Finite :=
  hfin _ (ZSpan.fundamentalDomain_isBounded b)

def orbitMap (b : Module.Basis (Fin d) ℝ (Space d)) (C : Set (Space d))
    (hp : ∀ v ∈ latticeOfBasis b, Period C v)
    (p : representatives b C × latticeOfBasis b) : C :=
  ⟨(p.1 : Space d) + (p.2 : Space d),
    (hp p.2 p.2.property p.1).2 p.1.property.1⟩

theorem orbitMap_injective (b : Module.Basis (Fin d) ℝ (Space d)) (C : Set (Space d))
    (hp : ∀ v ∈ latticeOfBasis b, Period C v) :
    Function.Injective (orbitMap b C hp) := by
  rintro ⟨r, g⟩ ⟨s, h⟩ he
  have he' : (r : Space d) + (g : Space d) = s + (h : Space d) :=
    congrArg Subtype.val he
  have hr : ZSpan.fract b (r : Space d) = r :=
    ZSpan.fract_eq_self.mpr r.property.2
  have hs : ZSpan.fract b (s : Space d) = s :=
    ZSpan.fract_eq_self.mpr s.property.2
  have hfract := congrArg (ZSpan.fract b) he'
  rw [ZSpan.fract_add_ZSpan b _ g.property,
    ZSpan.fract_add_ZSpan b _ h.property, hr, hs] at hfract
  have hrs : r = s := Subtype.ext hfract
  subst s
  have hgh : g = h := Subtype.ext (add_left_cancel he')
  subst h
  rfl

theorem orbitMap_surjective (b : Module.Basis (Fin d) ℝ (Space d)) (C : Set (Space d))
    (hp : ∀ v ∈ latticeOfBasis b, Period C v) :
    Function.Surjective (orbitMap b C hp) := by
  intro c
  let g : latticeOfBasis b := ZSpan.floor b (c : Space d)
  have hneg : -(g : Space d) ∈ latticeOfBasis b :=
    (latticeOfBasis b).neg_mem g.property
  have hc : ZSpan.fract b (c : Space d) ∈ C := by
    rw [ZSpan.fract_apply, sub_eq_add_neg]
    exact (hp _ hneg c).2 c.property
  let r : representatives b C :=
    ⟨ZSpan.fract b c, hc, ZSpan.fract_mem_fundamentalDomain b c⟩
  refine ⟨(r, g), Subtype.ext ?_⟩
  change ZSpan.fract b (c : Space d) + (ZSpan.floor b (c : Space d) : Space d) = c
  rw [ZSpan.fract_apply, sub_add_cancel]

def orbitEquiv (b : Module.Basis (Fin d) ℝ (Space d)) (C : Set (Space d))
    (hp : ∀ v ∈ latticeOfBasis b, Period C v) :
    representatives b C × latticeOfBasis b ≃ C :=
  Equiv.ofBijective (orbitMap b C hp)
    ⟨orbitMap_injective b C hp, orbitMap_surjective b C hp⟩

@[simp] theorem orbitEquiv_apply_coe (b : Module.Basis (Fin d) ℝ (Space d))
    (C : Set (Space d)) (hp : ∀ v ∈ latticeOfBasis b, Period C v)
    (r : representatives b C) (g : latticeOfBasis b) :
    ((orbitEquiv b C hp (r, g) : C) : Space d) = (r : Space d) + (g : Space d) :=
  rfl

theorem type_constant_on_orbit (b : Module.Basis (Fin d) ℝ (Space d))
    (C C1 : Set (Space d)) (hp : ∀ v ∈ latticeOfBasis b, Period C v)
    (ht : ∀ v ∈ latticeOfBasis b, Period C1 v)
    (r : representatives b C) (g : latticeOfBasis b) :
    ((orbitEquiv b C hp (r, g) : C) : Space d) ∈ C1 ↔ (r : Space d) ∈ C1 :=
  ht g g.property r

end PeriodicTilingThree.PeriodicVolume

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Set MeasureTheory
open scoped Pointwise ENNReal

namespace PeriodicTilingThree.PeriodicVolume

variable {d : ℕ}

def translate (c : Space d) (K : Set (Space d)) : Set (Space d) :=
  {x | x - c ∈ K}

@[simp] theorem mem_translate {c x : Space d} {K : Set (Space d)} :
    x ∈ translate c K ↔ x - c ∈ K := Iff.rfl

theorem translate_eq_vadd (c : Space d) (K : Set (Space d)) :
    translate c K = c +ᵥ K := by
  ext x
  simp only [mem_translate, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  rw [sub_eq_add_neg, add_comm x (-c)]

@[simp] theorem measure_translate (c : Space d) (K : Set (Space d)) :
    volume (translate c K) = volume K := by
  rw [translate_eq_vadd, measure_vadd]

theorem measurableSet_translate (c : Space d) {K : Set (Space d)}
    (hK : MeasurableSet K) : MeasurableSet (translate c K) :=
  hK.preimage (measurable_id.sub measurable_const)

theorem lattice_vadd_translate (b : Module.Basis (Fin d) ℝ (Space d))
    (g : latticeOfBasis b) (r : Space d) (K : Set (Space d)) :
    g +ᵥ translate r K = translate (r + (g : Space d)) K := by
  ext x
  rw [mem_vadd_set_iff_neg_vadd_mem]
  change (-(g : Space d) + x) - r ∈ K ↔ x - (r + (g : Space d)) ∈ K
  have he : (-(g : Space d) + x) - r = x - (r + (g : Space d)) := by abel
  rw [he]

def assembly (C : Set (Space d)) (K : Space d → Set (Space d)) : Set (Space d) :=
  ⋃ c : C, translate c (K c)

@[simp] theorem mem_assembly {C : Set (Space d)} {K : Space d → Set (Space d)}
    {x : Space d} : x ∈ assembly C K ↔ ∃ c : C, x - (c : Space d) ∈ K c := by
  simp only [assembly, mem_iUnion, mem_translate]

theorem measurableSet_assembly (C : Set (Space d)) (hC : C.Countable)
    (K : Space d → Set (Space d)) (hK : ∀ c ∈ C, MeasurableSet (K c)) :
    MeasurableSet (assembly C K) := by
  let : Countable C := hC.to_subtype
  exact MeasurableSet.iUnion fun c : C => measurableSet_translate c (hK c c.property)

theorem periodic_piece_mass (b : Module.Basis (Fin d) ℝ (Space d))
    (C : Set (Space d)) (hp : ∀ v ∈ latticeOfBasis b, Period C v)
    (K : Space d → Set (Space d))
    (hKp : ∀ (g : latticeOfBasis b) x, K (x + (g : Space d)) = K x) :
    (∑' c : C, volume (translate c (K c) ∩ ZSpan.fundamentalDomain b)) =
      ∑' r : representatives b C, volume (K r) := by
  let : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  have hP := ZSpan.isAddFundamentalDomain' b (volume : Measure (Space d))
  calc
    (∑' c : C, volume (translate c (K c) ∩ ZSpan.fundamentalDomain b)) =
        ∑' p : representatives b C × latticeOfBasis b,
          volume (translate (orbitEquiv b C hp p) (K (orbitEquiv b C hp p)) ∩
            ZSpan.fundamentalDomain b) :=
      ((orbitEquiv b C hp).tsum_eq _).symm
    _ = ∑' r : representatives b C, ∑' g : latticeOfBasis b,
          volume (translate ((r : Space d) + (g : Space d))
            (K ((r : Space d) + (g : Space d))) ∩ ZSpan.fundamentalDomain b) :=
      ENNReal.tsum_prod'
    _ = ∑' r : representatives b C, volume (K r) := by
      apply tsum_congr
      intro r
      calc
        (∑' g : latticeOfBasis b,
            volume (translate ((r : Space d) + (g : Space d))
              (K ((r : Space d) + (g : Space d))) ∩ ZSpan.fundamentalDomain b)) =
            ∑' g : latticeOfBasis b,
              volume ((g +ᵥ translate r (K r)) ∩ ZSpan.fundamentalDomain b) := by
          apply tsum_congr
          intro g
          rw [hKp g r, lattice_vadd_translate]
        _ = volume (translate r (K r)) := (hP.measure_eq_tsum _).symm
        _ = volume (K r) := measure_translate _ _

theorem periodic_piece_mass_eq_card (b : Module.Basis (Fin d) ℝ (Space d))
    (C : Set (Space d)) (hp : ∀ v ∈ latticeOfBasis b, Period C v)
    (hfin : ∀ B : Set (Space d), Bornology.IsBounded B → (C ∩ B).Finite)
    (K : Space d → Set (Space d))
    (hKp : ∀ (g : latticeOfBasis b) x, K (x + (g : Space d)) = K x)
    (v : ℝ≥0∞) (hv : ∀ c ∈ C, volume (K c) = v) :
    (∑' c : C, volume (translate c (K c) ∩ ZSpan.fundamentalDomain b)) =
      Nat.card (representatives b C) • v := by
  let := (representatives_finite b C hfin).fintype
  rw [periodic_piece_mass b C hp K hKp]
  have hvr : ∀ r : representatives b C, volume (K r) = v := fun r => hv r r.property.1
  simp only [hvr, tsum_fintype, Finset.sum_const,
    Finset.card_univ, Nat.card_eq_fintype_card]

theorem packed_assembly_mass (b : Module.Basis (Fin d) ℝ (Space d))
    (C : Set (Space d)) (hC : C.Countable)
    (hp : ∀ v ∈ latticeOfBasis b, Period C v)
    (K : Space d → Set (Space d))
    (hKp : ∀ (g : latticeOfBasis b) x, K (x + (g : Space d)) = K x)
    (hK : ∀ c ∈ C, MeasurableSet (K c))
    (hpack : Pairwise fun c c' : C =>
      AEDisjoint volume (translate c (K c)) (translate c' (K c'))) :
    volume (assembly C K ∩ ZSpan.fundamentalDomain b) =
      ∑' r : representatives b C, volume (K r) := by
  let : Countable C := hC.to_subtype
  calc
    volume (assembly C K ∩ ZSpan.fundamentalDomain b) =
        ∑' c : C, volume (translate c (K c) ∩ ZSpan.fundamentalDomain b) := by
      rw [assembly, iUnion_inter]
      apply measure_iUnion₀
      · intro c c' hne
        exact (hpack hne).mono inter_subset_left inter_subset_left
      · intro c
        exact ((measurableSet_translate c (hK c c.property)).inter
          (ZSpan.fundamentalDomain_measurableSet b)).nullMeasurableSet
    _ = ∑' r : representatives b C, volume (K r) :=
      periodic_piece_mass b C hp K hKp

end PeriodicTilingThree.PeriodicVolume

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Set MeasureTheory Filter
open scoped Pointwise ENNReal

namespace PeriodicTilingThree.PeriodicVolume

variable {d : ℕ}

def typedPiece (Ω0 Ω1 C1 : Set (Space d)) (c : Space d) : Set (Space d) := by
  classical
  exact if c ∈ C1 then Ω1 else Ω0

theorem typedPiece_measurable (Ω0 Ω1 C1 : Set (Space d))
    (h0 : MeasurableSet Ω0) (h1 : MeasurableSet Ω1) (c : Space d) :
    MeasurableSet (typedPiece Ω0 Ω1 C1 c) := by
  classical
  unfold typedPiece
  split_ifs <;> assumption

theorem typedPiece_periodic (b : Module.Basis (Fin d) ℝ (Space d))
    (Ω0 Ω1 C1 : Set (Space d))
    (ht : ∀ v ∈ latticeOfBasis b, Period C1 v)
    (g : latticeOfBasis b) (x : Space d) :
    typedPiece Ω0 Ω1 C1 (x + (g : Space d)) = typedPiece Ω0 Ω1 C1 x := by
  classical
  simp only [typedPiece, ht g g.property x]

theorem typedPiece_volume (Ω0 Ω1 C1 : Set (Space d))
    (hv : volume Ω1 = volume Ω0) (c : Space d) :
    volume (typedPiece Ω0 Ω1 C1 c) = volume Ω0 := by
  classical
  unfold typedPiece
  split_ifs
  · exact hv
  · rfl

theorem typed_aedisjoint (Ω0 Ω1 C C1 : Set (Space d))
    (htile : TypedAETiles Ω0 Ω1 C C1) :
    Pairwise fun c c' : C => AEDisjoint volume
      (translate c (typedPiece Ω0 Ω1 C1 c))
      (translate c' (typedPiece Ω0 Ω1 C1 c')) := by
  classical
  intro c c' hne
  have ha : ∀ᵐ x ∂volume,
      x ∉ translate c (typedPiece Ω0 Ω1 C1 c) ∩
        translate c' (typedPiece Ω0 Ω1 C1 c') := by
    filter_upwards [htile] with x hx
    intro hmem
    exact hne (hx.unique hmem.1 hmem.2)
  simpa only [AEDisjoint, not_not, Set.ofPred_mem_eq] using (ae_iff.mp ha)

theorem typed_assembly_ae_eq_univ (Ω0 Ω1 C C1 : Set (Space d))
    (htile : TypedAETiles Ω0 Ω1 C C1) :
    assembly C (typedPiece Ω0 Ω1 C1) =ᵐ[volume] Set.univ := by
  classical
  filter_upwards [htile] with x hx
  apply propext
  exact ⟨fun _ => mem_univ x, fun _ => mem_assembly.mpr hx.exists⟩

theorem typed_cell_mass (b : Module.Basis (Fin d) ℝ (Space d))
    (Ω0 Ω1 C C1 : Set (Space d))
    (hC : C.Countable)
    (hfin : ∀ B : Set (Space d), Bornology.IsBounded B → (C ∩ B).Finite)
    (h0 : MeasurableSet Ω0) (h1 : MeasurableSet Ω1)
    (hv : volume Ω1 = volume Ω0)
    (hp : ∀ v ∈ latticeOfBasis b, Period C v)
    (ht : ∀ v ∈ latticeOfBasis b, Period C1 v)
    (htile : TypedAETiles Ω0 Ω1 C C1) :
    volume (ZSpan.fundamentalDomain b) =
      Nat.card (representatives b C) • volume Ω0 := by
  classical
  let := (representatives_finite b C hfin).fintype
  have hu := ae_eq_set_inter (typed_assembly_ae_eq_univ Ω0 Ω1 C C1 htile)
    (Filter.EventuallyEq.rfl : ZSpan.fundamentalDomain b =ᵐ[volume]
      ZSpan.fundamentalDomain b)
  calc
    volume (ZSpan.fundamentalDomain b) =
        volume (assembly C (typedPiece Ω0 Ω1 C1) ∩ ZSpan.fundamentalDomain b) := by
      simpa only [univ_inter] using (measure_congr hu).symm
    _ = ∑' r : representatives b C, volume (typedPiece Ω0 Ω1 C1 r) :=
      packed_assembly_mass b C hC hp (typedPiece Ω0 Ω1 C1)
        (typedPiece_periodic b Ω0 Ω1 C1 ht)
        (fun c _ => typedPiece_measurable Ω0 Ω1 C1 h0 h1 c)
        (typed_aedisjoint Ω0 Ω1 C C1 htile)
    _ = Nat.card (representatives b C) • volume Ω0 := by
      simp only [typedPiece_volume Ω0 Ω1 C1 hv, tsum_fintype,
        Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]

theorem assembly_period (b : Module.Basis (Fin d) ℝ (Space d))
    (C : Set (Space d)) (hp : ∀ v ∈ latticeOfBasis b, Period C v)
    (K : Space d → Set (Space d))
    (hKp : ∀ (g : latticeOfBasis b) x, K (x + (g : Space d)) = K x)
    (g : latticeOfBasis b) : Period (assembly C K) (g : Space d) := by
  intro x
  rw [mem_assembly, mem_assembly]
  constructor
  · rintro ⟨c, hc⟩
    have hcg : (c : Space d) - (g : Space d) ∈ C := by
      simpa only [sub_eq_add_neg] using
        (hp _ ((latticeOfBasis b).neg_mem g.property) c).2 c.property
    refine ⟨⟨(c : Space d) - (g : Space d), hcg⟩, ?_⟩
    have hKm : K ((c : Space d) - (g : Space d)) = K c := by
      simpa only [NegMemClass.coe_neg, sub_eq_add_neg] using hKp (-g) c
    change x - ((c : Space d) - (g : Space d)) ∈ K ((c : Space d) - (g : Space d))
    rw [hKm]
    have he : x - ((c : Space d) - (g : Space d)) =
        (x + (g : Space d)) - (c : Space d) := by abel
    rw [he]
    exact hc
  · rintro ⟨c, hc⟩
    have hcg : (c : Space d) + (g : Space d) ∈ C :=
      (hp g g.property c).2 c.property
    refine ⟨⟨(c : Space d) + (g : Space d), hcg⟩, ?_⟩
    change (x + (g : Space d)) - ((c : Space d) + (g : Space d)) ∈
      K ((c : Space d) + (g : Space d))
    rw [hKp g c, add_sub_add_right_eq_sub]
    exact hc

theorem lattice_vadd_assembly (b : Module.Basis (Fin d) ℝ (Space d))
    (C : Set (Space d)) (hp : ∀ v ∈ latticeOfBasis b, Period C v)
    (K : Space d → Set (Space d))
    (hKp : ∀ (g : latticeOfBasis b) x, K (x + (g : Space d)) = K x)
    (g : latticeOfBasis b) : g +ᵥ assembly C K = assembly C K := by
  ext x
  rw [mem_vadd_set_iff_neg_vadd_mem]
  change -(g : Space d) + x ∈ assembly C K ↔ x ∈ assembly C K
  simpa only [NegMemClass.coe_neg, add_comm] using
    assembly_period b C hp K hKp (-g) x

theorem ae_covers_of_cell_mass (b : Module.Basis (Fin d) ℝ (Space d))
    (C : Set (Space d)) (hC : C.Countable)
    (hp : ∀ v ∈ latticeOfBasis b, Period C v)
    (K : Space d → Set (Space d))
    (hKp : ∀ (g : latticeOfBasis b) x, K (x + (g : Space d)) = K x)
    (hK : ∀ c ∈ C, MeasurableSet (K c))
    (hmass : volume (assembly C K ∩ ZSpan.fundamentalDomain b) =
      volume (ZSpan.fundamentalDomain b)) :
    ∀ᵐ x ∂volume, ∃ c : C, x - (c : Space d) ∈ K c := by
  let : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  have hU := measurableSet_assembly C hC K hK
  have hP := ZSpan.fundamentalDomain_measurableSet b
  have hPfin : volume (ZSpan.fundamentalDomain b) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded b).measure_lt_top.ne
  have hae : (assembly C K ∩ ZSpan.fundamentalDomain b : Set (Space d)) =ᵐ[volume]
      ZSpan.fundamentalDomain b :=
    ae_eq_of_subset_of_measure_ge inter_subset_right hmass.symm.le
      (hU.inter hP).nullMeasurableSet hPfin
  have hnull := (ae_eq_set.mp hae).2
  have hdiff : ZSpan.fundamentalDomain b \
      (assembly C K ∩ ZSpan.fundamentalDomain b) =
      (assembly C K)ᶜ ∩ ZSpan.fundamentalDomain b := by
    ext x
    simp only [Set.mem_sdiff, mem_inter_iff, mem_compl_iff]
    tauto
  rw [hdiff] at hnull
  have hglobal : volume (assembly C K)ᶜ = 0 :=
    (ZSpan.isAddFundamentalDomain' b volume).measure_zero_of_invariant
      ((assembly C K)ᶜ)
      (fun g => by
        ext x
        rw [mem_vadd_set_iff_neg_vadd_mem]
        change (-(g : Space d) + x ∉ assembly C K) ↔ x ∉ assembly C K
        simpa only [NegMemClass.coe_neg, add_comm] using
          not_congr (assembly_period b C hp K hKp (-g) x))
      hnull
  have hcover : ∀ᵐ x ∂volume, x ∈ assembly C K := ae_iff.mpr hglobal
  exact hcover.mono fun _ hx => mem_assembly.mp hx

theorem replacement_ae_covers (b : Module.Basis (Fin d) ℝ (Space d))
    (Ω0 Ω1 J C C1 : Set (Space d))
    (hC : C.Countable)
    (hfin : ∀ B : Set (Space d), Bornology.IsBounded B → (C ∩ B).Finite)
    (h0 : MeasurableSet Ω0) (h1 : MeasurableSet Ω1) (hJ : MeasurableSet J)
    (hv : volume Ω1 = volume Ω0) (hJv : volume J = volume Ω0)
    (hp : ∀ v ∈ latticeOfBasis b, Period C v)
    (ht : ∀ v ∈ latticeOfBasis b, Period C1 v)
    (htile : TypedAETiles Ω0 Ω1 C C1)
    (hpack : Pairwise fun c c' : C =>
      AEDisjoint volume (translate c J) (translate c' J)) :
    ∀ᵐ x ∂volume, ∃ c : C, x - (c : Space d) ∈ J := by
  classical
  let := (representatives_finite b C hfin).fintype
  apply ae_covers_of_cell_mass b C hC hp (fun _ => J) (fun _ _ => rfl)
    (fun _ _ => hJ)
  calc
    volume (assembly C (fun _ => J) ∩ ZSpan.fundamentalDomain b) =
        ∑' _r : representatives b C, volume J :=
      packed_assembly_mass b C hC hp (fun _ => J) (fun _ _ => rfl)
        (fun _ _ => hJ) hpack
    _ = Nat.card (representatives b C) • volume Ω0 := by
      simp only [hJv, tsum_fintype, Finset.sum_const, Finset.card_univ,
        Nat.card_eq_fintype_card]
    _ = volume (ZSpan.fundamentalDomain b) :=
      (typed_cell_mass b Ω0 Ω1 C C1 hC hfin h0 h1 hv hp ht htile).symm

end PeriodicTilingThree.PeriodicVolume

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

open Set MeasureTheory

theorem grid_difference_of_cube_chain {m : ℕ} {C : Set (Space 3)}
    (hnear : ∀ c c' : C, ‖(c' : Space 3) - (c : Space 3)‖ ≤ (m : ℝ) →
      (c' : Space 3) - (c : Space 3) ∈ scaledGrid m)
    {c₀ c : C}
    (hchain : Relation.ReflTransGen
      (CoverIntersects (fun a : C => auxiliaryCube m a)) c₀ c) :
    (c : Space 3) - (c₀ : Space 3) ∈ scaledGrid m := by
  induction hchain with
  | refl => simpa only [sub_self] using (scaledGrid m).zero_mem
  | @tail a b _ hab ih =>
      have hedge := hnear a b (auxiliaryCube_inter_norm_le hab)
      have hid : (b : Space 3) - (c₀ : Space 3) =
          ((b : Space 3) - (a : Space 3)) + ((a : Space 3) - (c₀ : Space 3)) := by
        abel
      rw [hid]
      exact (scaledGrid m).add_mem hedge ih

theorem grid_coset_of_auxiliary_cover {m : ℕ} (hm : 0 < m)
    (C : Set (Space 3))
    (hlocal : LocallyFinite (fun c : C => auxiliaryCube m c))
    (hcover : ∀ x : Space 3, ∃ c : C, x ∈ auxiliaryCube m c)
    (hnear : ∀ c c' : C, ‖(c' : Space 3) - (c : Space 3)‖ ≤ (m : ℝ) →
      (c' : Space 3) - (c : Space 3) ∈ scaledGrid m) :
    ∃ c₀ ∈ C, C = {x : Space 3 | x - c₀ ∈ scaledGrid m} := by
  obtain ⟨c₀, _hc₀⟩ := hcover 0
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hgrid (c : C) : (c : Space 3) - (c₀ : Space 3) ∈ scaledGrid m := by
    apply grid_difference_of_cube_chain hnear
    exact closed_cover_chain_connected (fun a : C => auxiliaryCube m a)
      (fun a => auxiliaryCube_nonempty m a) (fun a => auxiliaryCube_isClosed m a)
      hlocal hcover c₀ c
  refine ⟨c₀, c₀.property, ?_⟩
  ext x
  constructor
  · intro hx
    exact hgrid ⟨x, hx⟩
  · intro hx
    obtain ⟨c, hxc⟩ := hcover x
    have hdiff : x - (c : Space 3) ∈ scaledGrid m := by
      have h := (scaledGrid m).sub_mem hx (hgrid c)
      have hid : (x - (c₀ : Space 3)) - ((c : Space 3) - (c₀ : Space 3)) =
          x - (c : Space 3) := by abel
      rwa [hid] at h
    have hnorm : ‖x - (c : Space 3)‖ < (m : ℝ) := by
      have hle : dist x (c : Space 3) ≤ (m : ℝ) / 2 := hxc
      rw [dist_eq_norm] at hle
      linarith
    have hxc' : x = (c : Space 3) :=
      sub_eq_zero.mp (scaledGrid_eq_zero_of_norm_lt hm hdiff hnorm)
    rw [hxc']
    exact c.property

theorem periodic_voxel_assembly_grid
    {m : ℕ} (hm : 2 ≤ m) {S0 S1 S : Finset (Lattice 3)}
    (h0 : S ⊆ S0) (h1 : S ⊆ S1) (hdiff : RigidDifferences m S)
    (hcard0 : S0.card = m ^ 3) (hcard1 : S1.card = m ^ 3)
    {C C1 : Set (Space 3)}
    (b : Module.Basis (Fin 3) ℝ (Space 3))
    (hp : ∀ v ∈ latticeOfBasis b, Period C v)
    (ht : ∀ v ∈ latticeOfBasis b, Period C1 v)
    (htile : TypedAETiles (Thickening S0) (Thickening S1) C C1) :
    ∃ c₀ ∈ C, C = {x : Space 3 | x - c₀ ∈ scaledGrid m} := by
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hsep : C.Pairwise (fun x y => (m : ℝ) ≤ ‖x - y‖) := by
    intro x hx y hy hxy
    have hne : (⟨y, hy⟩ : C) ≠ ⟨x, hx⟩ := by
      intro heq
      exact hxy (congrArg Subtype.val heq).symm
    exact typed_centers_separated hm h0 h1 hdiff htile hne
  have hcount := centers_countable hmR hsep
  have hfin : ∀ K : Set (Space 3), Bornology.IsBounded K → (C ∩ K).Finite :=
    fun _ hK => centers_finite_on_bounded hmR hsep hK
  have hnear : ∀ c c' : C, ‖(c' : Space 3) - (c : Space 3)‖ ≤ (m : ℝ) →
      (c' : Space 3) - (c : Space 3) ∈ scaledGrid m := by
    intro c c' hcc'
    by_cases heq : c = c'
    · subst c'
      simpa only [sub_self] using (scaledGrid m).zero_mem
    · exact typed_nearby_centers_mem_scaledGrid hm h0 h1 hdiff htile heq hcc'
  have hvol : volume (Thickening S1) = volume (Thickening S0) := by
    rw [thickening_volume, thickening_volume, hcard0, hcard1]
  have hJvol : volume (auxiliaryCube m 0) = volume (Thickening S0) := by
    rw [auxiliaryCube_volume, thickening_volume, hcard0]
  have hpack : Pairwise fun c c' : C => AEDisjoint volume
      (PeriodicVolume.translate c (auxiliaryCube m 0))
      (PeriodicVolume.translate c' (auxiliaryCube m 0)) := by
    intro c c' hne
    change AEDisjoint volume {x | x - (c : Space 3) ∈ auxiliaryCube m 0}
      {x | x - (c' : Space 3) ∈ auxiliaryCube m 0}
    rw [auxiliaryCube_translate, auxiliaryCube_translate]
    apply auxiliaryCube_aedisjoint hmpos
    exact hsep c.property c'.property (fun heq => hne (Subtype.ext heq))
  have hae := PeriodicVolume.replacement_ae_covers b
    (Thickening S0) (Thickening S1) (auxiliaryCube m 0) C C1
    hcount hfin (thickening_measurableSet S0) (thickening_measurableSet S1)
    (auxiliaryCube_measurableSet m 0) hvol hJvol hp ht htile hpack
  have haecubes : ∀ᵐ x ∂volume, ∃ c : C, x ∈ auxiliaryCube m c := by
    filter_upwards [hae] with x hx
    obtain ⟨c, hc⟩ := hx
    refine ⟨c, ?_⟩
    rw [← auxiliaryCube_translate]
    exact hc
  exact grid_coset_of_auxiliary_cover hmpos C (auxiliaryCube_locallyFinite m C hfin)
    (auxiliaryCube_cover_of_ae m C hfin haecubes) hnear

theorem periodic_voxel_assembly_grid_range
    {m : ℕ} (hm : 2 ≤ m) {S0 S1 S : Finset (Lattice 3)}
    (h0 : S ⊆ S0) (h1 : S ⊆ S1) (hdiff : RigidDifferences m S)
    (hcard0 : S0.card = m ^ 3) (hcard1 : S1.card = m ^ 3)
    {C C1 : Set (Space 3)}
    (b : Module.Basis (Fin 3) ℝ (Space 3))
    (hp : ∀ v ∈ latticeOfBasis b, Period C v)
    (ht : ∀ v ∈ latticeOfBasis b, Period C1 v)
    (htile : TypedAETiles (Thickening S0) (Thickening S1) C C1) :
    ∃ c₀ ∈ C, C = Set.range (fun z : Lattice 3 => c₀ + (m : ℝ) • castLattice z) := by
  obtain ⟨c₀, hc₀, heq⟩ := periodic_voxel_assembly_grid hm h0 h1 hdiff
    hcard0 hcard1 b hp ht htile
  refine ⟨c₀, hc₀, heq.trans ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := mem_scaledGrid.mp hx
    refine ⟨z, ?_⟩
    change c₀ + (m : ℝ) • castLattice z = x
    rw [hz, add_sub_cancel]
  · rintro ⟨z, rfl⟩
    apply mem_scaledGrid.mpr
    refine ⟨z, ?_⟩
    change (m : ℝ) • castLattice z = (c₀ + (m : ℝ) • castLattice z) - c₀
    exact (add_sub_cancel_left c₀ ((m : ℝ) • castLattice z)).symm

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

open Matrix
open scoped BigOperators

theorem integer_mulVec_mem_of_columns
    (L : AddSubgroup (Lattice 3)) (M : Matrix (Fin 3) (Fin 3) ℤ)
    (hM : ∀ j, M.col j ∈ L) (z : Lattice 3) : M *ᵥ z ∈ L := by
  have hs : (∑ j : Fin 3, z j • M.col j) ∈ L := by
    apply L.sum_mem
    intro j _hj
    exact L.zsmul_mem (hM j) (z j)
  have he : M *ᵥ z = ∑ j : Fin 3, z j • M.col j := by
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.col, mul_comm]
  rwa [he]

theorem determinant_smul_mem_of_columns
    (L : AddSubgroup (Lattice 3)) (M : Matrix (Fin 3) (Fin 3) ℤ)
    (hM : ∀ j, M.col j ∈ L) (z : Lattice 3) : M.det • z ∈ L := by
  have h := integer_mulVec_mem_of_columns L M hM (M.adjugate *ᵥ z)
  simpa only [Matrix.mulVec_mulVec, Matrix.mul_adjugate,
    Matrix.smul_mulVec, Matrix.one_mulVec] using h

theorem finiteIndex_of_integer_columns
    (L : AddSubgroup (Lattice 3)) (M : Matrix (Fin 3) (Fin 3) ℤ)
    (hdet : M.det ≠ 0) (hM : ∀ j, M.col j ∈ L) : L.FiniteIndex := by
  let d : ℕ := M.det.natAbs
  have hd : d ≠ 0 := (Int.natAbs_pos.mpr hdet).ne'
  let : NeZero d := ⟨hd⟩
  have hker : (MarkedTile.residue d).ker ≤ L := by
    intro x hx
    obtain ⟨z, hz⟩ := MarkedTile.exists_scale_of_residue_eq_zero d hx
    have habs : (d : ℤ) • z ∈ L := by
      have h := determinant_smul_mem_of_columns L M hM z
      change (M.det.natAbs : ℤ) • z ∈ L
      rw [Int.natCast_natAbs]
      by_cases hsign : 0 ≤ M.det
      · simpa only [abs_of_nonneg hsign] using h
      · simpa only [abs_of_nonpos (le_of_not_ge hsign), neg_smul] using L.neg_mem h
    have he : MarkedTile.scale d z = (d : ℤ) • z := by
      ext i
      simp only [MarkedTile.scale_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hz, he]
    exact habs
  let : (MarkedTile.residue d).ker.FiniteIndex := inferInstance
  exact AddSubgroup.finiteIndex_of_le hker

theorem det_ne_zero_of_scaled_columns_basis (m : ℕ)
    (b : Module.Basis (Fin 3) ℝ (Space 3)) (z : Fin 3 → Lattice 3)
    (hz : ∀ j, scaledCast m (z j) = b j) :
    Matrix.det (fun i j : Fin 3 => z j i) ≠ 0 := by
  let M : Matrix (Fin 3) (Fin 3) ℤ := fun i j => z j i
  let e := Pi.basisFun ℝ (Fin 3)
  have hreal : (e.toMatrix b).det ≠ 0 := (e.isUnit_det b).ne_zero
  have hmatrix : e.toMatrix b = (m : ℝ) • (M.map fun a => (a : ℝ)) := by
    ext i j
    change (e.repr (b j)) i = (m : ℝ) * (z j i : ℝ)
    rw [Pi.basisFun_repr]
    exact (congrFun (hz j) i).symm
  change M.det ≠ 0
  intro hzero
  have hcast : (M.map fun a => (a : ℝ)).det = 0 := by
    rw [← Int.cast_det, hzero, Int.cast_zero]
  apply hreal
  rw [hmatrix, Matrix.det_smul, hcast, mul_zero]

theorem lattice_pullback_finiteIndex (m : ℕ)
    (b : Module.Basis (Fin 3) ℝ (Space 3))
    (hb : latticeOfBasis b ≤ scaledGrid m) :
    ((latticeOfBasis b).comap (scaledCast m)).FiniteIndex := by
  have hbmem : ∀ j : Fin 3, b j ∈ latticeOfBasis b := by
    intro j
    exact Submodule.subset_span ⟨j, rfl⟩
  have hex : ∀ j : Fin 3, ∃ z : Lattice 3, scaledCast m z = b j := by
    intro j
    exact hb (hbmem j)
  choose z hz using hex
  let M : Matrix (Fin 3) (Fin 3) ℤ := fun i j => z j i
  apply finiteIndex_of_integer_columns _ M
    (det_ne_zero_of_scaled_columns_basis m b z hz)
  intro j
  change scaledCast m (z j) ∈ latticeOfBasis b
  rw [hz j]
  exact hbmem j

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

open MeasureTheory
open scoped Classical

def normalizedComplement (m : ℕ) (c₀ : Space 3) (A : Set (Space 3)) :
    Set (Lattice 3) := {z | c₀ + scaledCast m z ∈ A}

theorem period_lattice_le_scaledGrid (m : ℕ) (c₀ : Space 3)
    {A : Set (Space 3)} (hne : A.Nonempty)
    (hgrid : ∀ a ∈ A, ∃ z : Lattice 3, c₀ + scaledCast m z = a)
    (b : Module.Basis (Fin 3) ℝ (Space 3))
    (hp : ∀ v ∈ latticeOfBasis b, Period A v) :
    latticeOfBasis b ≤ scaledGrid m := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨z₀, hz₀⟩ := hgrid a ha
  intro v hv
  obtain ⟨z₁, hz₁⟩ := hgrid (a + v) ((hp v hv a).mpr ha)
  refine ⟨z₁ - z₀, ?_⟩
  change scaledCast m (z₁ - z₀) = v
  calc
    scaledCast m (z₁ - z₀) =
        (c₀ + scaledCast m z₁) - (c₀ + scaledCast m z₀) := by
      rw [map_sub]
      abel
    _ = (a + v) - a := by rw [hz₀, hz₁]
    _ = v := by abel

theorem fullyPeriodic_normalizedComplement (m : ℕ) (c₀ : Space 3)
    {A : Set (Space 3)} (hne : A.Nonempty)
    (hgrid : ∀ a ∈ A, ∃ z : Lattice 3, c₀ + scaledCast m z = a)
    (hperiodic : EuclideanFullyPeriodic A) :
    FullyPeriodic (normalizedComplement m c₀ A) := by
  obtain ⟨b, hb⟩ := hperiodic
  have hle := period_lattice_le_scaledGrid m c₀ hne hgrid b hb
  refine ⟨(latticeOfBasis b).comap (scaledCast m),
    lattice_pullback_finiteIndex m b hle, ?_⟩
  intro v hv z
  change c₀ + scaledCast m (z + v) ∈ A ↔ c₀ + scaledCast m z ∈ A
  rw [map_add, ← add_assoc]
  exact hb (scaledCast m v) hv (c₀ + scaledCast m z)

theorem normalized_typedAETiles (m : ℕ) (hm : m ≠ 0) (c₀ : Space 3)
    {Ω₀ Ω₁ C A : Set (Space 3)}
    (hgrid : C = Set.range (fun z : Lattice 3 => c₀ + scaledCast m z))
    (htile : TypedAETiles Ω₀ Ω₁ C A) :
    ∀ᵐ x ∂volume, ∃! z : Lattice 3,
      x - scaledCast m z ∈
        if z ∈ normalizedComplement m c₀ A then Ω₁ else Ω₀ := by
  classical
  have hshift : ∀ᵐ x ∂volume, ∃! c : C,
      (c₀ + x) - (c : Space 3) ∈
        if (c : Space 3) ∈ A then Ω₁ else Ω₀ :=
    (eventually_add_left_iff volume c₀).mpr htile
  filter_upwards [hshift] with x hx
  obtain ⟨c, hc, huniq⟩ := hx
  obtain ⟨z, hz⟩ : ∃ z : Lattice 3, c₀ + scaledCast m z = (c : Space 3) := by
    exact Eq.mp
      (congrArg (fun S : Set (Space 3) => (c : Space 3) ∈ S) hgrid) c.property
  refine ⟨z, ?_, ?_⟩
  · rw [← hz] at hc
    have he : (c₀ + x) - (c₀ + scaledCast m z) = x - scaledCast m z := by abel
    by_cases hzA : c₀ + scaledCast m z ∈ A
    · simpa only [he, normalizedComplement, Set.mem_ofPred_eq, hzA, ite_true] using hc
    · simpa only [he, normalizedComplement, Set.mem_ofPred_eq, hzA, ite_false] using hc
  · intro y hy
    let cy : C := ⟨c₀ + scaledCast m y, by rw [hgrid]; exact ⟨y, rfl⟩⟩
    have hcy : (c₀ + x) - (cy : Space 3) ∈
        if (cy : Space 3) ∈ A then Ω₁ else Ω₀ := by
      change (c₀ + x) - (c₀ + scaledCast m y) ∈
        if c₀ + scaledCast m y ∈ A then Ω₁ else Ω₀
      have he : (c₀ + x) - (c₀ + scaledCast m y) = x - scaledCast m y := by abel
      rw [he]
      exact hy
    have he : c₀ + scaledCast m y = c₀ + scaledCast m z := by
      exact (congrArg Subtype.val (huniq cy hcy)).trans hz.symm
    exact scaledCast_injective hm (add_left_cancel he)

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI


namespace PeriodicTilingThree

section

variable {G : Type uG} {H : Type uH} [AddCommGroup G] [AddCommGroup H] [DecidableEq H]

theorem tiles_preimage_of_section (φ : G →+ H)
    {U : Finset G} {F : Finset H} {A : Set H}
    (himage : U.image φ = F) (hinj : Set.InjOn φ (U : Set G))
    (h : Tiles F A) : Tiles U (φ ⁻¹' A) := by
  classical
  apply tiles_iff_unique_tile.mpr
  intro g
  obtain ⟨f, hf, huniq⟩ := tiles_iff_unique_tile.mp h (φ g)
  have hfimage : (f : H) ∈ U.image φ := by
    rw [himage]
    exact f.property
  obtain ⟨u, hu, huf⟩ := Finset.mem_image.mp hfimage
  refine ⟨⟨u, hu⟩, ?_, ?_⟩
  · change φ (g - u) ∈ A
    simpa only [map_sub, huf] using hf
  · intro v hv
    have hvF : φ (v : G) ∈ F := by
      rw [← himage]
      exact Finset.mem_image.mpr ⟨v, v.property, rfl⟩
    have hvA : φ g - φ (v : G) ∈ A := by
      simpa only [Set.mem_preimage, map_sub] using hv
    have hvf : (⟨φ (v : G), hvF⟩ : ↥F) = f := huniq _ hvA
    apply Subtype.ext
    apply hinj v.property hu
    exact (congrArg Subtype.val hvf).trans huf.symm

theorem tiles_image_of_kernel_periods (φ : G →+ H)
    (hφ : Function.Surjective φ) {U : Finset G} {B : Set G}
    (h : Tiles U B) (hker : ∀ k ∈ φ.ker, Period B k) :
    Tiles (U.image φ) (φ '' B) := by
  classical
  apply tiles_iff_unique_tile.mpr
  intro y
  obtain ⟨g, hg⟩ := hφ y
  obtain ⟨u, hu, huniq⟩ := tiles_iff_unique_tile.mp h g
  have hfu : φ (u : G) ∈ U.image φ :=
    Finset.mem_image.mpr ⟨u, u.property, rfl⟩
  refine ⟨⟨φ (u : G), hfu⟩, ?_, ?_⟩
  · refine ⟨g - (u : G), hu, ?_⟩
    simp only [map_sub, hg]
  · intro f hf
    obtain ⟨v, hv, hvf⟩ := Finset.mem_image.mp f.property
    obtain ⟨b, hb, hbf⟩ := hf
    have hgvb : φ (g - v - b) = 0 := by
      simp only [map_sub, hg, hvf, hbf, sub_self]
    have hk : g - v - b ∈ φ.ker := hgvb
    have hgv : g - v ∈ B := by
      have hp := (hker (g - v - b) hk b).mpr hb
      have heq : b + (g - v - b) = g - v := by
        rw [add_comm, sub_add_cancel]
      rw [heq] at hp
      exact hp
    have hvu : (⟨v, hv⟩ : ↥U) = u := huniq _ hgv
    apply Subtype.ext
    calc
      (f : H) = φ v := hvf.symm
      _ = φ (u : G) := congrArg φ (congrArg Subtype.val hvu)

end

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree.MarkedTile.ResidueSection

open CyclicQuotient

variable {m : ℕ} [NeZero m] (s : ResidueSection m)

theorem no_euclideanFullyPeriodic
    (hm : 2 ≤ m) (hdiff : RigidDifferences m s.Tstar)
    (Q : ℕ) [NeZero Q] (F : Finset (CyclicQuotient.Group Q)) (hF0 : 0 ∈ F)
    (haperiodic : ∀ B, Tiles F B → ¬ FullyPeriodic B)
    {A : Set (Space 3)}
    (htile : AETiles
      (Thickening (s.finalTile (kernelStep Q) (representatives Q F))) A) :
    ¬ EuclideanFullyPeriodic A := by
  classical
  rintro ⟨b, hb⟩
  let U := representatives Q F
  let w := kernelStep Q
  have h0 : 0 ∈ U := zero_mem_representatives Q hF0
  have hw : w ∉ U := kernelStep_not_mem_representatives Q F
  have htyped := s.typed_constituents hm h0 hw htile
  have hinj := s.center_injective hm h0 hw htile
  obtain ⟨c₀, _hc₀, hgrid'⟩ := periodic_voxel_assembly_grid_range hm
    s.Tstar_subset_T0 (s.Tstar_subset_T1 w) hdiff s.card_T0 (s.card_T1 w)
    b (fun v hv => period_centers (hb v hv)) hb htyped
  have hgrid : centers m U A =
      Set.range (fun z : Lattice 3 => c₀ + scaledCast m z) := hgrid'
  let B := normalizedComplement m c₀ A
  have hBtile : Tiles U B := tiles_of_centers_grid hinj hgrid
  have hAne : A.Nonempty := by
    obtain ⟨z, hz⟩ := hBtile.complement_nonempty
    exact ⟨c₀ + scaledCast m z, hz⟩
  have hAgrid : ∀ a ∈ A, ∃ z : Lattice 3, c₀ + scaledCast m z = a := by
    intro a ha
    have hc := subset_centers (m := m) h0 A ha
    rw [hgrid] at hc
    exact hc
  have hBperiodic : FullyPeriodic B :=
    fullyPeriodic_normalizedComplement m c₀ hAne hAgrid ⟨b, hb⟩
  have hnormalized := normalized_typedAETiles m (NeZero.ne m) c₀ hgrid htyped
  have hkernel : ∀ k ∈ (projection Q).ker, Period B k :=
    s.kernel_periods_of_marked_cells Q B hnormalized
  have hquotient : Tiles F ((projection Q) '' B) := by
    have h := tiles_image_of_kernel_periods (projection Q) (projection_surjective Q)
      hBtile hkernel
    simpa only [U, projection_image_representatives] using h
  exact haperiodic _ hquotient
    (FullyPeriodic.image_of_surjective (projection Q) (projection_surjective Q) hBperiodic)

end PeriodicTilingThree.MarkedTile.ResidueSection

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

def scaledCoordinateBasis (d q : ℕ) (hq : q ≠ 0) : Module.Basis (Fin d) ℝ (Space d) :=
  (Units.mk0 (q : ℝ) (Nat.cast_ne_zero.mpr hq)) • Pi.basisFun ℝ (Fin d)

theorem scaledCoordinateBasis_eq_cast {d q : ℕ} (hq : q ≠ 0) (i : Fin d) :
    scaledCoordinateBasis d q hq i =
      castLattice (q • (Pi.single i 1 : Lattice d)) := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [scaledCoordinateBasis, Module.Basis.smul_apply, Units.smul_def]
  · simp [scaledCoordinateBasis, Module.Basis.smul_apply,
      hji]

theorem exists_positive_scalar_sublattice {d : ℕ} (P : AddSubgroup (Lattice d))
    (hP : P.FiniteIndex) : ∃ q : ℕ, 0 < q ∧ ∀ z : Lattice d, q • z ∈ P := by
  refine ⟨P.index, Nat.pos_of_ne_zero hP.index_ne_zero, ?_⟩
  intro z
  exact P.nsmul_index_mem z

theorem FullyPeriodic.castLattice_image {d : ℕ} {A : Set (Lattice d)}
    (hA : FullyPeriodic A) : EuclideanFullyPeriodic (castLattice '' A) := by
  classical
  obtain ⟨P, hP, hPeriods⟩ := hA
  obtain ⟨q, hq, hqP⟩ := exists_positive_scalar_sublattice P hP
  refine ⟨scaledCoordinateBasis d q hq.ne', ?_⟩
  intro v hv
  change v ∈ Submodule.span ℤ (Set.range (scaledCoordinateBasis d q hq.ne')) at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      rw [scaledCoordinateBasis_eq_cast]
      exact (hPeriods _ (hqP (Pi.single i 1))).image castLattice
  | zero => exact period_zero _
  | add x y _ _ hx hy => exact hx.add hy
  | smul n x _ hx =>
      exact (periodSubgroup (castLattice '' A)).zsmul_mem hx n

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

open MeasureTheory

def floorLattice {d : ℕ} (x : Space d) : Lattice d := fun i => ⌊x i⌋

theorem ae_noninteger_coordinates (d : ℕ) :
    ∀ᵐ x : Space d ∂volume, ∀ i : Fin d, ∀ z : ℤ, x i ≠ (z : ℝ) := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro z
  exact Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) i (z : ℝ)

theorem sub_floorLattice_mem_unitCube {d : ℕ} (x : Space d) :
    x - castLattice (floorLattice x) ∈ unitCube d := by
  apply mem_unitCube.mpr
  intro i
  change 0 ≤ x i - (⌊x i⌋ : ℝ) ∧ x i - (⌊x i⌋ : ℝ) ≤ 1
  have hl := Int.floor_le (x i)
  have hu := Int.lt_floor_add_one (x i)
  constructor <;> linarith

theorem floorLattice_eq_of_mem_unitVoxel {d : ℕ} {x : Space d}
    (hx : ∀ i : Fin d, ∀ z : ℤ, x i ≠ (z : ℝ)) {z : Lattice d}
    (hz : x - castLattice z ∈ unitCube d) : floorLattice x = z := by
  funext i
  apply Int.floor_eq_iff.mpr
  have hi := mem_unitCube.mp hz i
  change 0 ≤ x i - (z i : ℝ) ∧ x i - (z i : ℝ) ≤ 1 at hi
  constructor
  · linarith
  · have hne : x i ≠ (z i : ℝ) + 1 := by
      simpa using hx i (z i + 1)
    by_contra hn
    apply hne
    linarith

theorem Tiles.aeTiles_thickening {d : ℕ} {F : Finset (Lattice d)}
    {A : Set (Lattice d)} (h : Tiles F A) :
    AETiles (Thickening F) (castLattice '' A) := by
  apply (ae_noninteger_coordinates d).mono
  intro x hx
  obtain ⟨⟨f, a⟩, hfa⟩ := h.2 (floorLattice x)
  change (f : Lattice d) + (a : Lattice d) = floorLattice x at hfa
  refine ⟨⟨castLattice (a : Lattice d), ⟨(a : Lattice d), a.property, rfl⟩⟩, ?_, ?_⟩
  · refine ⟨(f : Lattice d), f.property, ?_⟩
    change x - castLattice (a : Lattice d) - castLattice (f : Lattice d) ∈ unitCube d
    have heq : x - castLattice (a : Lattice d) - castLattice (f : Lattice d) =
        x - castLattice (floorLattice x) := by
      rw [← hfa, map_add]
      abel
    rw [heq]
    exact sub_floorLattice_mem_unitCube x
  · intro b hb
    obtain ⟨b', hb', hb_eq⟩ := b.property
    obtain ⟨f', hf', hf'b⟩ := hb
    have hvoxel : x - castLattice (f' + b') ∈ unitCube d := by
      have heq : x - castLattice (f' + b') =
          x - (b : Space d) - castLattice f' := by
        rw [map_add, ← hb_eq]
        abel
      rw [heq]
      exact hf'b
    have hcorner := floorLattice_eq_of_mem_unitVoxel hx hvoxel
    have hp : ((⟨f', hf'⟩ : ↥F), (⟨b', hb'⟩ : A)) = (f, a) := by
      apply h.1
      change f' + b' = (f : Lattice d) + (a : Lattice d)
      exact hcorner.symm.trans hfa.symm
    apply Subtype.ext
    calc
      (b : Space d) = castLattice b' := hb_eq.symm
      _ = castLattice (a : Lattice d) :=
        congrArg castLattice (congrArg (fun p : ↥F × A => (p.2 : Lattice d)) hp)

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace PeriodicTilingThree

theorem three_dimensional_tile_of_cyclic_counterexample
    (Q : ℕ) [NeZero Q] (F : Finset (CyclicQuotient.Group Q))
    (hF : F.Nonempty) (htile : ∃ A, Tiles F A)
    (haperiodic : ∀ A, Tiles F A → ¬ FullyPeriodic A) :
    ∃ T : Finset (Lattice 3),
      T.Nonempty ∧
      (∃ A : Set (Lattice 3), Tiles T A) ∧
      (∀ A : Set (Lattice 3), Tiles T A → ¬ FullyPeriodic A) ∧
      (∃ A : Set (Space 3), AETiles (Thickening T) A) ∧
      (∀ A : Set (Space 3), AETiles (Thickening T) A →
        ¬ EuclideanFullyPeriodic A) := by
  classical
  obtain ⟨F₀, hF₀, ⟨B, hB⟩, hBaperiodic⟩ :=
    exists_zero_mem_normalization F hF htile haperiodic
  let T : Finset (Lattice 3) := rigidSection.finalTile
    (CyclicQuotient.kernelStep Q) (CyclicQuotient.representatives Q F₀)
  let C : Set (Lattice 3) :=
    (MarkedTile.scale 64) '' ((CyclicQuotient.projection Q) ⁻¹' B)
  have hT : Tiles T C := rigidSection.cyclic_finalTile_tiles Q hB
  have hreal : ∀ A : Set (Space 3),
      AETiles (Thickening T) A → ¬ EuclideanFullyPeriodic A := by
    intro A hA
    exact rigidSection.no_euclideanFullyPeriodic (by norm_num)
      rigidSection_rigidDifferences Q F₀ hF₀ hBaperiodic hA
  refine ⟨T, hT.tile_nonempty, ⟨C, hT⟩, ?_,
    ⟨castLattice '' C, hT.aeTiles_thickening⟩, hreal⟩
  intro A hA hperiodic
  exact hreal (castLattice '' A) hA.aeTiles_thickening hperiodic.castLattice_image

end PeriodicTilingThree

end

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree

theorem exists_three_dimensional_tile :
    ∃ T : Finset (Lattice 3),
      T.Nonempty ∧
      (∃ A : Set (Lattice 3), Tiles T A) ∧
      (∀ A : Set (Lattice 3), Tiles T A → ¬ FullyPeriodic A) ∧
      (∃ A : Set (Space 3), AETiles (Thickening T) A) ∧
      (∀ A : Set (Space 3), AETiles (Thickening T) A →
        ¬ EuclideanFullyPeriodic A) := by
  obtain ⟨Q, hQ, F, hF, htile, haperiodic⟩ := exists_cyclic_counterexample
  let : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  exact three_dimensional_tile_of_cyclic_counterexample Q F hF htile haperiodic

end PeriodicTilingThree

end OAI
end
end

section
section
namespace OAI

namespace PeriodicTilingThree

theorem least_lattice_dimension_three :
    IsLeast {d : ℕ | HasTileWithoutPeriodicComplement d} 3 := by
  classical
  constructor
  · obtain ⟨T, hT, hTiles, hNoPeriod, _hRealTiles, _hNoRealPeriod⟩ :=
      exists_three_dimensional_tile
    exact ⟨T, hT, hTiles, hNoPeriod⟩
  · intro d hd
    by_contra hnot
    have hlt : d < 3 := Nat.lt_of_not_ge hnot
    obtain ⟨T, _hT, hTiles, hNoPeriod⟩ := hd
    obtain ⟨A, hA, hPeriod⟩ :=
      tiles_below_three_have_fullyPeriodic_complements d hlt T hTiles
    exact hNoPeriod A hA hPeriod

theorem periodic_tiling_counterexample_and_minimality_oai :
    (∃ T : Finset (Lattice 3), T.Nonempty ∧
      (∃ A : Set (Lattice 3), Tiles T A) ∧
      (∀ A : Set (Lattice 3), Tiles T A → ¬ FullyPeriodic A) ∧
      (∃ A : Set (Space 3), AETiles (Thickening T) A) ∧
      (∀ A : Set (Space 3),
        AETiles (Thickening T) A → ¬ EuclideanFullyPeriodic A)) ∧
    IsLeast {d : ℕ | HasTileWithoutPeriodicComplement d} 3 :=
  ⟨exists_three_dimensional_tile, least_lattice_dimension_three⟩

end PeriodicTilingThree

end OAI
end
end

section
section

end
end

theorem solution : type_of% @OAI.PeriodicTilingThree.periodic_tiling_counterexample_and_minimality_oai := @OAI.PeriodicTilingThree.periodic_tiling_counterexample_and_minimality_oai
