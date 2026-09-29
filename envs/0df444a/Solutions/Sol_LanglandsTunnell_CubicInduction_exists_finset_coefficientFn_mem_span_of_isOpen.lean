-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_finset_coefficientFn_mem_span_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d2fff3b7-8c45-5ff9-b825-95d051128df7

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_AdditiveJacquet
import Theorems.Thm_LanglandsTunnell_CubicInduction_isCompact_localMaximalCompact3
import Theorems.Thm_LanglandsTunnell_CubicInduction_isOpen_localMaximalCompact3
import Theorems.Thm_LanglandsTunnell_CubicInduction_finiteDimensional_fixedPoints_principalSeries3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_finset_coefficientFn_mem_span_of_isOpen

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "principalSeries3 rightTranslate_mem_principalSeries3 coefficientFn gl3Entry gl3AmbientRightTranslate gl3AmbientRightTranslate_apply valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 isClopen_setOf_valued_sub_le isCompact_localMaximalCompact3 isOpen_localMaximalCompact3 finiteDimensional_fixedPoints_principalSeries3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def IsLevel3 (m : ℕ) (κ : LocalGL3 v) : Prop :=
  ∀ i j : Fin 3,
    Valued.v (gl3Entry v κ i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))

private theorem isLevel3_iff (m : ℕ) (κ : LocalGL3 v) :
    IsLevel3 v m κ ↔ ∀ i j : Fin 3,
      Valued.v (gl3Entry v κ i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
        WithZero.exp (-(m : ℤ)) :=
  Iff.rfl

private theorem isLevel3_iff_sub_one (m : ℕ) (κ : LocalGL3 v) :
    IsLevel3 v m κ ↔ ∀ i j : Fin 3,
      Valued.v (((κ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) i j) ≤ WithZero.exp (-(m : ℤ)) :=
  Iff.rfl

private theorem isLevel3_one (m : ℕ) : IsLevel3 v m 1 := by
  intro i j
  simp only [gl3Entry, Units.val_one, sub_self, map_zero]
  exact zero_le

private theorem valued_coe_apply_le_one_of_mem_localMaximalCompact3 {k : LocalGL3 v}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) (i j : Fin 3) :
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1 :=
  hk.1 i j

private theorem isLevel3_mul {m : ℕ} {a b : LocalGL3 v} (ha : IsLevel3 v m a) (hb : IsLevel3 v m b)
    (hbK : b ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) : IsLevel3 v m (a * b) := by
  rw [isLevel3_iff_sub_one] at ha hb ⊢
  intro i j
  have hid : ((a * b : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1 =
      ((a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) * (b : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) +
        ((b : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) := by
    rw [Units.val_mul, sub_mul, one_mul]
    abel
  rw [hid, Matrix.add_apply]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hb i j))
  exact valued_mul_apply_le3 (𝓞 ℚ) ℚ v (fun l => ha i l) (fun l => hbK.1 l j)

private theorem
    isLevel3_inv {m : ℕ} {a : LocalGL3 v} (ha : IsLevel3 v m a) (haK : a ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    IsLevel3 v m a⁻¹ := by
  rw [isLevel3_iff_sub_one] at ha ⊢
  intro i j
  have hid : ((a⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1 =
      (1 - (a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) *
        ((a⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) := by
    rw [sub_mul, one_mul, Units.mul_inv]
  rw [hid]
  refine valued_mul_apply_le3 (𝓞 ℚ) ℚ v (fun l => ?_) (fun l => haK.2 l j)
  rw [← neg_sub, Matrix.neg_apply, Valuation.map_neg]
  exact ha i l

private def levelSubgroup3 (m : ℕ) : Subgroup (LocalGL3 v) where
  carrier := {k | k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧ IsLevel3 v m k}
  one_mem' := ⟨(localMaximalCompact3 (𝓞 ℚ) ℚ v).one_mem, isLevel3_one v m⟩
  mul_mem' := fun {_ _} ⟨haK, ha⟩ ⟨hbK, hb⟩ =>
    ⟨(localMaximalCompact3 (𝓞 ℚ) ℚ v).mul_mem haK hbK, isLevel3_mul v ha hb hbK⟩
  inv_mem' := fun {_} ⟨haK, ha⟩ => ⟨(localMaximalCompact3 (𝓞 ℚ) ℚ v).inv_mem haK, isLevel3_inv v ha haK⟩

private theorem mem_levelSubgroup3_iff (m : ℕ) (k : LocalGL3 v) :
    k ∈ levelSubgroup3 v m ↔ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧ IsLevel3 v m k :=
  Iff.rfl

private theorem mem_localMaximalCompact3_of_mem_levelSubgroup3 {m : ℕ} {k : LocalGL3 v} (hk : k ∈ levelSubgroup3 v m) :
    k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v :=
  hk.1

private theorem
    isLevel3_of_mem_levelSubgroup3 {m : ℕ} {k : LocalGL3 v} (hk : k ∈ levelSubgroup3 v m) : IsLevel3 v m k :=
  hk.2

private theorem mem_levelSubgroup3_of_eq_mul {m : ℕ} {s k κ : LocalGL3 v} (hs : s ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) (hκ : IsLevel3 v m κ) (h : k = s * κ) : κ ∈ levelSubgroup3 v m := by
  refine (mem_levelSubgroup3_iff v m κ).2 ⟨?_, hκ⟩
  have : κ = s⁻¹ * k := by rw [h, inv_mul_cancel_left]
  rw [this]
  exact (localMaximalCompact3 (𝓞 ℚ) ℚ v).mul_mem ((localMaximalCompact3 (𝓞 ℚ) ℚ v).inv_mem hs) hk

private theorem isLevel3_of_le {n m : ℕ} (hnm : n ≤ m) {k : LocalGL3 v} (hk : IsLevel3 v m k) : IsLevel3 v n k := by
  intro i j
  refine le_trans (hk i j) ?_
  rw [WithZero.exp_le_exp]
  omega

private theorem levelSubgroup3_le_of_le {n m : ℕ} (hnm : n ≤ m) : levelSubgroup3 v m ≤ levelSubgroup3 v n :=
  fun k hk => (mem_levelSubgroup3_iff v n k).2
    ⟨((mem_levelSubgroup3_iff v m k).1 hk).1, isLevel3_of_le v hnm ((mem_levelSubgroup3_iff v m k).1 hk).2⟩

private theorem isLevel3_zero_of_mem_localMaximalCompact3 {k : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    IsLevel3 v 0 k := by
  intro i j
  have h1 : WithZero.exp (-((0 : ℕ) : ℤ)) = 1 := by simp
  rw [h1]
  exact le_trans (Valuation.map_sub _ _ _) (max_le (hk.1 i j) (valued_one_entry_le3 (𝓞 ℚ) ℚ v i j))

private theorem levelSubgroup3_zero : levelSubgroup3 v 0 = localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  ext k
  exact ⟨fun hk => ((mem_levelSubgroup3_iff v 0 k).1 hk).1,
    fun hk => (mem_levelSubgroup3_iff v 0 k).2 ⟨hk, isLevel3_zero_of_mem_localMaximalCompact3 v hk⟩⟩

private theorem mem_levelSubgroup3_zero_iff (k : LocalGL3 v) :
    k ∈ levelSubgroup3 v 0 ↔ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [levelSubgroup3_zero]

private theorem valued_mul_apply_le3_right {C : WithZero (Multiplicative ℤ)}
    {a b : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} {i j : Fin 3}
    (ha : ∀ l, Valued.v (a i l) ≤ 1) (hb : ∀ l, Valued.v (b l j) ≤ C) :
    Valued.v ((a * b) i j) ≤ C := by
  have hterm : ∀ l, Valued.v (a i l * b l j) ≤ C := fun l => by
    rw [map_mul]
    calc Valued.v (a i l) * Valued.v (b l j) ≤ 1 * Valued.v (b l j) := mul_le_mul_left (ha l) _
      _ = Valued.v (b l j) := one_mul _
      _ ≤ C := hb l
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hterm 2))
  exact le_trans (Valuation.map_add _ _ _) (max_le (hterm 0) (hterm 1))

private theorem isLevel3_conj {m : ℕ} {k κ : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (hκ : IsLevel3 v m κ) : IsLevel3 v m (k * κ * k⁻¹) := by
  rw [isLevel3_iff_sub_one] at hκ ⊢
  intro i j
  have hid : ((k * κ * k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1 =
      (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
        (((κ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) *
          ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) := by
    rw [Units.val_mul, Units.val_mul, sub_mul, one_mul, mul_sub, ← mul_assoc, Units.mul_inv]
  rw [hid]
  refine valued_mul_apply_le3_right v (fun l => hk.1 i l) (fun l => ?_)
  exact valued_mul_apply_le3 (𝓞 ℚ) ℚ v (fun l' => hκ l l') (fun l' => hk.2 l' j)

private theorem mul_mul_inv_mem_levelSubgroup3 {m : ℕ} {k κ : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (hκ : κ ∈ levelSubgroup3 v m) : k * κ * k⁻¹ ∈ levelSubgroup3 v m :=
  (mem_levelSubgroup3_iff v m _).2
    ⟨(localMaximalCompact3 (𝓞 ℚ) ℚ v).mul_mem
        ((localMaximalCompact3 (𝓞 ℚ) ℚ v).mul_mem hk (mem_localMaximalCompact3_of_mem_levelSubgroup3 v hκ))
        ((localMaximalCompact3 (𝓞 ℚ) ℚ v).inv_mem hk),
      isLevel3_conj v hk (isLevel3_of_mem_levelSubgroup3 v hκ)⟩

private theorem valued_mul_apply_le3_mul {C C' : WithZero (Multiplicative ℤ)}
    {a b : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} {i j : Fin 3}
    (ha : ∀ l, Valued.v (a i l) ≤ C) (hb : ∀ l, Valued.v (b l j) ≤ C') :
    Valued.v ((a * b) i j) ≤ C * C' := by
  have hterm : ∀ l, Valued.v (a i l * b l j) ≤ C * C' := fun l => by
    rw [map_mul]
    exact mul_le_mul' (ha l) (hb l)
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hterm 2))
  exact le_trans (Valuation.map_add _ _ _) (max_le (hterm 0) (hterm 1))

private theorem le_one_of_le_max_mul {M e : WithZero (Multiplicative ℤ)} (he : e < 1) (h : M ≤ max 1 (M * e)) :
    M ≤ 1 := by
  rcases le_or_gt M 1 with hM | hM
  · exact hM
  · exfalso
    have h' : M ≤ M * e := (le_max_iff.1 h).resolve_left (not_le.2 hM)
    obtain ⟨u, rfl⟩ := WithZero.ne_zero_iff_exists.1 (zero_lt_one.trans hM).ne'
    rcases eq_or_ne e 0 with rfl | he0
    · rw [mul_zero] at h'
      exact absurd h' (not_le.2 (WithZero.zero_lt_coe u))
    · obtain ⟨w, rfl⟩ := WithZero.ne_zero_iff_exists.1 he0
      rw [← WithZero.coe_mul, WithZero.coe_le_coe] at h'
      rw [← WithZero.coe_one, WithZero.coe_lt_coe] at he
      exact absurd ((le_mul_iff_one_le_right' _).1 h') (not_le.2 he)

private theorem exp_neg_one_lt_one : WithZero.exp (-((1 : ℕ) : ℤ)) < (1 : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

private theorem mem_localMaximalCompact3_of_isLevel3 {n : ℕ} (hn : 1 ≤ n) {k : LocalGL3 v} (hk : IsLevel3 v n k) :
    k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  have h1 := isLevel3_of_le v hn hk
  rw [isLevel3_iff_sub_one] at h1
  refine ⟨fun i j => ?_, ?_⟩
  · have hsplit : (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j =
        ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) i j +
          (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j := by
      simp
    rw [hsplit]
    exact le_trans (Valuation.map_add _ _ _)
      (max_le (le_trans (h1 i j) (exp_neg_one_lt_one).le) (valued_one_entry_le3 (𝓞 ℚ) ℚ v i j))
  · have hid : ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
        1 - ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
          ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) := by
      rw [mul_sub, mul_one, Units.inv_mul, sub_sub_cancel]
    have hle : ∀ p : Fin 3 × Fin 3,
        Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) p.1 p.2) ≤
          Finset.univ.sup fun q : Fin 3 × Fin 3 =>
            Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) q.1 q.2) :=
      fun p => Finset.le_sup (f := fun q : Fin 3 × Fin 3 =>
        Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) q.1 q.2)) (Finset.mem_univ p)
    have hbound : ∀ i j, Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
        max 1 ((Finset.univ.sup fun p : Fin 3 × Fin 3 =>
          Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) p.1 p.2)) *
            WithZero.exp (-((1 : ℕ) : ℤ))) := by
      intro i j
      conv_lhs => rw [hid]
      rw [Matrix.sub_apply]
      refine le_trans (Valuation.map_sub _ _ _) (max_le_max (valued_one_entry_le3 (𝓞 ℚ) ℚ v i j) ?_)
      exact valued_mul_apply_le3_mul v (fun l => hle (i, l)) (fun l => h1 l j)
    have hM := le_one_of_le_max_mul (exp_neg_one_lt_one) (Finset.sup_le fun (p : Fin 3 × Fin 3) _ => hbound p.1 p.2)
    exact fun i j => le_trans (hle (i, j)) hM

private theorem mem_levelSubgroup3_of_isLevel3 {n : ℕ} (hn : 1 ≤ n) {k : LocalGL3 v} (hk : IsLevel3 v n k) :
    k ∈ levelSubgroup3 v n :=
  (mem_levelSubgroup3_iff v n k).2 ⟨mem_localMaximalCompact3_of_isLevel3 v hn hk, hk⟩

private theorem isClopen_setOf_isLevel3 (l : ℕ) : IsClopen {k : LocalGL3 v | IsLevel3 v l k} := by
  have hcont : ∀ i j : Fin 3, Continuous fun k : LocalGL3 v => gl3Entry v k i j := fun i j => by
    unfold gl3Entry
    exact Units.continuous_val.matrix_elem i j
  have hset : {k : LocalGL3 v | IsLevel3 v l k} = ⋂ i : Fin 3, ⋂ j : Fin 3,
      (fun k : LocalGL3 v => gl3Entry v k i j) ⁻¹'
        {x : v.adicCompletion ℚ |
          Valued.v (x - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(l : ℤ))} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, IsLevel3]
  rw [hset]
  exact isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j =>
    (isClopen_setOf_valued_sub_le v _ _).preimage (hcont i j)

private theorem eq_zero_of_forall_valued_le (x : v.adicCompletion ℚ)
    (hx : ∀ n : ℕ, Valued.v x ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ))) : x = 0 := by
  by_contra hx0
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
  obtain ⟨m, hm⟩ : ∃ m : ℤ, m = WithZero.log (Valued.v x) := ⟨_, rfl⟩
  have hexp : WithZero.exp m = Valued.v x := by rw [hm]; exact WithZero.exp_log hv
  have h := hx m.natAbs
  rw [← hexp, WithZero.exp_le_exp] at h
  omega

private theorem eq_one_of_forall_isLevel3 {κ : LocalGL3 v} (h : ∀ n : ℕ, IsLevel3 v (n + 1) κ) : κ = 1 := by
  apply Units.ext
  rw [Units.val_one]
  ext i j
  have hzero := eq_zero_of_forall_valued_le v
    (gl3Entry v κ i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) fun n => h n i j
  exact sub_eq_zero.1 hzero

private theorem exists_isLevel3_imp_mem_of_isOpen {U : Set (LocalGL3 v)} (hU : IsOpen U)
    (h1 : (1 : LocalGL3 v) ∈ U) : ∃ n : ℕ, 1 ≤ n ∧ ∀ κ : LocalGL3 v, IsLevel3 v n κ → κ ∈ U := by
  by_contra hcon
  let t : ℕ → Set (LocalGL3 v) := fun n => {κ : LocalGL3 v | IsLevel3 v (n + 1) κ} ∩ Uᶜ
  have hanti : ∀ n : ℕ, t (n + 1) ⊆ t n := fun n κ hκ =>
    ⟨isLevel3_of_le v (Nat.le_succ (n + 1)) hκ.1, hκ.2⟩
  have hclosed : ∀ n : ℕ, IsClosed (t n) := fun n =>
    (isClopen_setOf_isLevel3 v (n + 1)).isClosed.inter hU.isClosed_compl
  have hcpt : IsCompact (t 0) :=
    (isCompact_localMaximalCompact3 v).of_isClosed_subset (hclosed 0)
      fun κ hκ => mem_localMaximalCompact3_of_isLevel3 v (Nat.le_add_left 1 0) hκ.1
  have hne : ∀ n : ℕ, (t n).Nonempty := by
    intro n
    by_contra hempty
    exact hcon ⟨n + 1, Nat.le_add_left 1 n, fun κ hκ => by_contra fun hκU => hempty ⟨κ, hκ, hκU⟩⟩
  obtain ⟨κ, hκ⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t hanti hne hcpt hclosed
  have hκ0 : κ ∈ t 0 := Set.mem_iInter.1 hκ 0
  apply hκ0.2
  rw [eq_one_of_forall_isLevel3 v fun n => (Set.mem_iInter.1 hκ n).1]
  exact h1

section Averaging

variable {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}

private theorem gl3AmbientRightTranslate_mul_apply (a b : LocalGL3 v) (f : LocalGL3 v → ℂ) :
    gl3AmbientRightTranslate (R := ℂ) (a * b) f =
      gl3AmbientRightTranslate (R := ℂ) a (gl3AmbientRightTranslate (R := ℂ) b f) := by
  funext x
  simp [gl3AmbientRightTranslate_apply, mul_assoc]

private noncomputable def coeffL (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) : ↥(principalSeries3 v χ) →ₗ[ℂ] (LocalGL3 v → ℂ) where
  toFun f := coefficientFn Λ f
  map_add' f g := by
    funext x
    show Λ _ = Λ _ + Λ _
    rw [← map_add]
    congr 1
  map_smul' c f := by
    funext x
    show Λ _ = c * Λ _
    rw [← smul_eq_mul, ← map_smul]
    congr 1

private theorem coeffL_apply (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 v χ)) :
    coeffL v Λ f = coefficientFn Λ f := rfl

private theorem gl3AmbientRightTranslate_coefficientFn (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 v χ))
    (h : LocalGL3 v) :
    gl3AmbientRightTranslate (R := ℂ) h (coefficientFn Λ f) =
      coefficientFn Λ ⟨gl3AmbientRightTranslate (R := ℂ) h f, rightTranslate_mem_principalSeries3 f.2 h⟩ := by
  funext g
  show Λ _ = Λ _
  congr 1
  apply Subtype.ext
  funext x
  show (f : LocalGL3 v → ℂ) (x * (g * h)) = (f : LocalGL3 v → ℂ) (x * g * h)
  rw [mul_assoc]

private noncomputable def Rsub (a : LocalGL3 v) (f : ↥(principalSeries3 v χ)) : ↥(principalSeries3 v χ) :=
  ⟨gl3AmbientRightTranslate (R := ℂ) a f, rightTranslate_mem_principalSeries3 f.2 a⟩

@[scoped simp] private theorem coe_Rsub (a : LocalGL3 v) (f : ↥(principalSeries3 v χ)) :
    ((Rsub v a f : ↥(principalSeries3 v χ)) : LocalGL3 v → ℂ) = gl3AmbientRightTranslate (R := ℂ) a f := rfl

private theorem exists_levelFixed_of_coefficient_invariant (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) {n m : ℕ}
    (hn1 : 1 ≤ n) (f : ↥(principalSeries3 v χ))
    (hmf : ∀ k : LocalGL3 v, IsLevel3 v m k → gl3AmbientRightTranslate (R := ℂ) k (f : LocalGL3 v → ℂ) = f)
    (hFk : ∀ k : LocalGL3 v, IsLevel3 v n k →
      gl3AmbientRightTranslate (R := ℂ) k (coefficientFn Λ f) = coefficientFn Λ f) :
    ∃ e : ↥(principalSeries3 v χ),
      (∀ k : LocalGL3 v, IsLevel3 v n k → gl3AmbientRightTranslate (R := ℂ) k (e : LocalGL3 v → ℂ) = e) ∧
      coefficientFn Λ e = coefficientFn Λ f := by
  classical

  have hKn_cpt : IsCompact ((levelSubgroup3 v n : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by
    refine (isCompact_localMaximalCompact3 v).of_isClosed_subset ?_ fun k hk => hk.1
    show IsClosed ((localMaximalCompact3 (𝓞 ℚ) ℚ v : Set (LocalGL3 v)) ∩ {k | IsLevel3 v n k})
    exact (isCompact_localMaximalCompact3 v).isClosed.inter (isClopen_setOf_isLevel3 v n).isClosed
  haveI : CompactSpace ↥(levelSubgroup3 v n) := isCompact_iff_compactSpace.mp hKn_cpt
  have hKm_open : IsOpen ((levelSubgroup3 v m : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by
    show IsOpen ((localMaximalCompact3 (𝓞 ℚ) ℚ v : Set (LocalGL3 v)) ∩ {k | IsLevel3 v m k})
    exact (isOpen_localMaximalCompact3 (𝓞 ℚ) ℚ v).inter (isClopen_setOf_isLevel3 v m).isOpen
  have hH_open : IsOpen (((levelSubgroup3 v m).subgroupOf (levelSubgroup3 v n) : Subgroup ↥(levelSubgroup3 v n)) :
      Set ↥(levelSubgroup3 v n)) := by
    rw [Subgroup.coe_subgroupOf]
    exact hKm_open.preimage continuous_subtype_val
  haveI : Finite (↥(levelSubgroup3 v n) ⧸ (levelSubgroup3 v m).subgroupOf (levelSubgroup3 v n)) :=
    Subgroup.quotient_finite_of_isOpen _ hH_open
  letI : Fintype (↥(levelSubgroup3 v n) ⧸ (levelSubgroup3 v m).subgroupOf (levelSubgroup3 v n)) := Fintype.ofFinite _

  have hconst : ∀ a b : ↥(levelSubgroup3 v n),
      (QuotientGroup.mk a : ↥(levelSubgroup3 v n) ⧸ (levelSubgroup3 v m).subgroupOf (levelSubgroup3 v n)) =
        QuotientGroup.mk b → Rsub v (a : LocalGL3 v) f = Rsub v (b : LocalGL3 v) f := by
    intro a b hab
    have hmem : a⁻¹ * b ∈ (levelSubgroup3 v m).subgroupOf (levelSubgroup3 v n) := QuotientGroup.eq.mp hab
    rw [Subgroup.mem_subgroupOf] at hmem
    have hmem' : ((a : LocalGL3 v))⁻¹ * (b : LocalGL3 v) ∈ levelSubgroup3 v m := hmem
    apply Subtype.ext
    rw [coe_Rsub, coe_Rsub, show (b : LocalGL3 v) = (a : LocalGL3 v) * (((a : LocalGL3 v))⁻¹ * (b : LocalGL3 v)) by
      rw [mul_inv_cancel_left], gl3AmbientRightTranslate_mul_apply, hmf _ hmem'.2]

  let T : ↥(levelSubgroup3 v n) ⧸ (levelSubgroup3 v m).subgroupOf (levelSubgroup3 v n) → ↥(principalSeries3 v χ) :=
    fun q => Rsub v ((q.out : ↥(levelSubgroup3 v n)) : LocalGL3 v) f
  have hT : ∀ a : ↥(levelSubgroup3 v n), T (QuotientGroup.mk a) = Rsub v (a : LocalGL3 v) f :=
    fun a => hconst _ _ (QuotientGroup.out_eq' _)
  let e : ↥(principalSeries3 v χ) := ∑ q, T q
  let N : ℕ := Fintype.card (↥(levelSubgroup3 v n) ⧸ (levelSubgroup3 v m).subgroupOf (levelSubgroup3 v n))
  have hN : (N : ℂ) ≠ 0 := by
    have : 0 < N := Fintype.card_pos_iff.mpr ⟨QuotientGroup.mk 1⟩
    exact_mod_cast this.ne'
  letI instMA : MulAction ↥(levelSubgroup3 v n)
      (↥(levelSubgroup3 v n) ⧸ (levelSubgroup3 v m).subgroupOf (levelSubgroup3 v n)) :=
    MulAction.quotient ↥(levelSubgroup3 v n) ((levelSubgroup3 v m).subgroupOf (levelSubgroup3 v n))

  have he_fix : ∀ k : LocalGL3 v, IsLevel3 v n k →
      gl3AmbientRightTranslate (R := ℂ) k (e : LocalGL3 v → ℂ) = e := by
    intro k hk
    have hkK : k ∈ levelSubgroup3 v n := mem_levelSubgroup3_of_isLevel3 v hn1 hk
    simp only [e, Submodule.coe_sum, map_sum]
    conv_rhs => rw [← Equiv.sum_comp (MulAction.toPerm (⟨k, hkK⟩ : ↥(levelSubgroup3 v n)))]
    refine Finset.sum_congr rfl fun q _ => ?_
    show gl3AmbientRightTranslate (R := ℂ) k ((T q : ↥(principalSeries3 v χ)) : LocalGL3 v → ℂ) =
      ((T ((⟨k, hkK⟩ : ↥(levelSubgroup3 v n)) • q) : ↥(principalSeries3 v χ)) : LocalGL3 v → ℂ)
    have hq : q = QuotientGroup.mk q.out := (QuotientGroup.out_eq' q).symm
    have h1 : T ((⟨k, hkK⟩ : ↥(levelSubgroup3 v n)) • q) = Rsub v (k * ((q.out : ↥(levelSubgroup3 v n)) : LocalGL3 v)) f := by
      conv_lhs => rw [hq, MulAction.Quotient.smul_mk, smul_eq_mul, hT]
      rfl
    have h2 : T q = Rsub v ((q.out : ↥(levelSubgroup3 v n)) : LocalGL3 v) f := by
      conv_lhs => rw [hq, hT]
    rw [h1, h2, coe_Rsub, coe_Rsub, ← gl3AmbientRightTranslate_mul_apply]

  have he_coef : coefficientFn Λ e = N • coefficientFn Λ f := by
    have : coeffL v Λ e = ∑ q, coeffL v Λ (T q) := by simp only [e, map_sum]
    rw [← coeffL_apply, this]
    have hq : ∀ q, coeffL v Λ (T q) = coefficientFn Λ f := by
      intro q
      rw [← QuotientGroup.out_eq' q, hT, coeffL_apply]
      have := gl3AmbientRightTranslate_coefficientFn v Λ f ((q.out : ↥(levelSubgroup3 v n)) : LocalGL3 v)
      rw [hFk _ (q.out).2.2] at this
      exact this.symm
    simp only [hq, Finset.sum_const, Finset.card_univ, N]
  refine ⟨(N : ℂ)⁻¹ • e, fun k hk => ?_, ?_⟩
  · rw [Submodule.coe_smul, map_smul, he_fix k hk]
  · rw [← coeffL_apply, map_smul, coeffL_apply, he_coef, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN,
      one_smul]

end Averaging

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_finset_coefficientFn_mem_span_of_isOpen.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_finset_coefficientFn_mem_span_of_isOpen.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_finset_coefficientFn_mem_span_of_isOpen.LanglandsTunnell"

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_finset_coefficientFn_mem_span_of_isOpen.LanglandsTunnell.CubicInduction in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)
    (Uv : Subgroup (LocalGL3 v)) (hU : IsOpen (Uv : Set (LocalGL3 v))) :
    ∃ B : Finset (LocalGL3 v → ℂ), ∀ f : ↥(principalSeries3 v χ),
      (∀ k ∈ Uv, ∀ g : LocalGL3 v, coefficientFn Λ f (g * k) = coefficientFn Λ f g) →
        coefficientFn Λ f ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)) := by
  classical

  obtain ⟨n, hn1, hsub⟩ := exists_isLevel3_imp_mem_of_isOpen v hU (one_mem Uv)

  haveI hfin := finiteDimensional_fixedPoints_principalSeries3 v χ n
  obtain ⟨S, hS⟩ := Module.finite_def.mp hfin

  let cV := (coeffL v Λ).comp (Submodule.inclusion
    (inf_le_left : principalSeries3 v χ ⊓
      ⨅ k ∈ {k : LocalGL3 v | ∀ i j : Fin 3,
          Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
            ≤ WithZero.exp (-(n : ℤ))},
        LinearMap.ker (gl3AmbientRightTranslate (R := ℂ) k - LinearMap.id) ≤ principalSeries3 v χ))
  refine ⟨S.image cV, fun f hFk => ?_⟩

  obtain ⟨m₀, hm₀⟩ := exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v χ f f.2
  have hmf : ∀ k : LocalGL3 v, IsLevel3 v (max m₀ n) k →
      gl3AmbientRightTranslate (R := ℂ) k (f : LocalGL3 v → ℂ) = f :=
    fun k hk => hm₀ k (isLevel3_of_le v (le_max_left m₀ n) hk)
  have hFk' : ∀ k : LocalGL3 v, IsLevel3 v n k →
      gl3AmbientRightTranslate (R := ℂ) k (coefficientFn Λ f) = coefficientFn Λ f :=
    fun k hk => funext fun g => hFk k (hsub k hk) g
  obtain ⟨e, he_fix, he_coef⟩ :=
    exists_levelFixed_of_coefficient_invariant v Λ hn1 f hmf hFk'

  have he_mem : (e : LocalGL3 v → ℂ) ∈ principalSeries3 v χ ⊓
      ⨅ k ∈ {k : LocalGL3 v | ∀ i j : Fin 3,
          Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
            ≤ WithZero.exp (-(n : ℤ))},
        LinearMap.ker (gl3AmbientRightTranslate (R := ℂ) k - LinearMap.id) := by
    refine Submodule.mem_inf.mpr ⟨e.2, ?_⟩
    refine (Submodule.mem_iInf _).mpr fun k => (Submodule.mem_iInf _).mpr fun hk => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    exact he_fix k hk
  have hspan : (⟨(e : LocalGL3 v → ℂ), he_mem⟩ : ↥(principalSeries3 v χ ⊓ _)) ∈ Submodule.span ℂ (S : Set _) := by
    rw [hS]; exact Submodule.mem_top
  have himg := Submodule.apply_mem_span_image_of_mem_span cV hspan
  rw [← he_coef, Finset.coe_image]
  exact himg

end S_LanglandsTunnell_CubicInduction_exists_finset_coefficientFn_mem_span_of_isOpen
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_finset_coefficientFn_mem_span_of_isOpen (solution)
