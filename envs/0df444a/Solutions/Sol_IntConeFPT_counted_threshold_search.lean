-- Prove2me | solution 1 for IntConeFPT.counted_threshold_search
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-25T15:02:07.41256+00:00
-- url     : https://prove2.me/submissions/e1b8b854-2185-45b2-8644-d731086cf0c2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntConeFPT_Homogenized
import Definitions.Def_IntConeFPT_Machine
import Theorems.Thm_IntConeFPT_corollary_8
import Theorems.Thm_IntConeFPT_corollary_10
import Theorems.Thm_IntConeFPT_lemma_13
import Theorems.Thm_IntConeFPT_lemma_6
import Theorems.Thm_IntConeFPT_counted_grid
import Theorems.Thm_IntConeFPT_section_3_6_nstar_bound
import Theorems.Thm_IntConeFPT_counted_threshold_driver

/- Stack volume accounting adapted from Prove2Me submission 70c7eb16-aa64-45fc-9619-d6fd621972a7 (Apache-2.0). -/
open Turing

attribute [instance] Turing.FinTM2.kDecidableEq Turing.FinTM2.kFin Turing.FinTM2.ΛFin
  Turing.FinTM2.σFin Turing.FinTM2.Γk₀Fin

namespace Turing

namespace TM2

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

def pushes : Stmt Γ Λ σ → ℕ
  | .push _ _ q => 1 + pushes q
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q r => max (pushes q) (pushes r)
  | .goto _ => 0
  | .halt => 0

variable [Fintype K] [DecidableEq K]

def volume (s : (k : K) → List (Γ k)) : ℕ := ∑ k, (s k).length

omit [Fintype K] in
theorem length_update (s : (k : K) → List (Γ k)) (k : K) (v : List (Γ k)) :
    (fun j => (Function.update s k v j).length) =
      Function.update (fun j => (s j).length) k v.length := by
  funext j
  by_cases h : j = k
  · subst h
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne h, Function.update_of_ne h]

theorem volume_update (s : (k : K) → List (Γ k)) (k : K) (v : List (Γ k)) :
    volume (Function.update s k v) + (s k).length = volume s + v.length := by
  classical
  unfold volume
  rw [length_update, Finset.sum_update_of_mem (Finset.mem_univ k)]
  have hh := Finset.sum_erase_add (Finset.univ : Finset K) (fun j => (s j).length)
    (Finset.mem_univ k)
  rw [Finset.sdiff_singleton_eq_erase]
  omega

theorem stepAux_volume (q : Stmt Γ Λ σ) (v : σ) (s : (k : K) → List (Γ k)) :
    volume (TM2.stepAux q v s).stk ≤ volume s + pushes q := by
  induction q generalizing v s with
  | push k g q ih =>
      have hv := volume_update s k (g v :: s k)
      simp only [List.length_cons] at hv
      have hq := ih v (Function.update s k (g v :: s k))
      simp only [TM2.stepAux, pushes]
      omega
  | peek k g q ih => exact ih _ _
  | pop k g q ih =>
      have hv := volume_update s k (s k).tail
      have hl := List.length_tail (l := s k)
      have hq := ih (g v (s k).head?) (Function.update s k (s k).tail)
      simp only [TM2.stepAux, pushes]
      omega
  | load g q ih => exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v
      · simp only [TM2.stepAux, hg, Bool.cond_false, pushes]
        exact (ihr v s).trans (Nat.add_le_add_left (le_max_right (pushes q) _) _)
      · simp only [TM2.stepAux, hg, Bool.cond_true, pushes]
        exact (ihq v s).trans (Nat.add_le_add_left (le_max_left _ (pushes r)) _)
  | goto g => simp only [TM2.stepAux, pushes, Nat.add_zero]; exact le_refl _
  | halt => simp only [TM2.stepAux, pushes, Nat.add_zero]; exact le_refl _

end TM2

open TM2 in
noncomputable def FinTM2.growth (tm : FinTM2) : ℕ := ∑ l, TM2.pushes (tm.m l)

namespace FinTM2

variable (tm : FinTM2)

theorem flip_bind_none : (flip bind tm.step) (none : Option tm.Cfg) = none := rfl

theorem flip_bind_some (c : tm.Cfg) : (flip bind tm.step) (some c) = tm.step c := rfl

theorem step_volume {a b : tm.Cfg} (h : tm.step a = some b) :
    TM2.volume b.stk ≤ TM2.volume a.stk + tm.growth := by
  classical
  obtain ⟨l, v, s⟩ := a
  cases l with
  | none => exact absurd h (by simp [FinTM2.step, TM2.step])
  | some l =>
      have hb : b = TM2.stepAux (tm.m l) v s := (Option.some.inj h).symm
      rw [hb, FinTM2.growth]
      refine (TM2.stepAux_volume _ _ _).trans (Nat.add_le_add_left ?_ _)
      exact Finset.single_le_sum (f := fun x => TM2.pushes (tm.m x))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)

theorem iterate_volume (tm : FinTM2) : ∀ (m : ℕ) (a b : tm.Cfg),
    (flip bind tm.step)^[m] (some a) = some b →
      TM2.volume b.stk ≤ TM2.volume a.stk + m * tm.growth
  | 0, a, b, h => by
      simp only [Function.iterate_zero, id_eq, Option.some.injEq] at h
      subst h; simp
  | m + 1, a, b, h => by
      rw [Function.iterate_succ_apply'] at h
      cases hprev : (flip bind tm.step)^[m] (some a) with
      | none => rw [hprev, tm.flip_bind_none] at h; exact absurd h (by simp)
      | some c =>
          rw [hprev, tm.flip_bind_some] at h
          have ih := iterate_volume tm m a c hprev
          have hs := tm.step_volume h
          have hmul : (m + 1) * tm.growth = m * tm.growth + tm.growth := Nat.succ_mul _ _
          rw [hmul]
          omega

theorem volume_initList (s : List (tm.Γ tm.k₀)) : TM2.volume (initList tm s).stk = s.length := by
  classical
  unfold TM2.volume
  rw [Finset.sum_eq_single tm.k₀]
  · simp [initList]
  · intro k _ hk
    simp only [initList, dif_neg hk, List.length_nil]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem volume_haltList (s : List (tm.Γ tm.k₁)) : TM2.volume (haltList tm s).stk = s.length := by
  classical
  unfold TM2.volume
  rw [Finset.sum_eq_single tm.k₁]
  · simp [haltList]
  · intro k _ hk
    simp only [haltList, dif_neg hk, List.length_nil]
  · intro h; exact absurd (Finset.mem_univ _) h

end FinTM2

theorem TM2OutputsInTime.output_length_le {tm : FinTM2} {s : List (tm.Γ tm.k₀)}
    {t : List (tm.Γ tm.k₁)} {n : ℕ}
    (h : TM2OutputsInTime tm s (some t) n) : t.length ≤ s.length + n * tm.growth := by
  have hvol := tm.iterate_volume h.steps (initList tm s) (haltList tm t) h.evals_in_steps
  rw [tm.volume_initList, tm.volume_haltList] at hvol
  exact hvol.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ h.steps_le_m) _)

end Turing

open OnlineCRS.Combine IntConeFPT

namespace IntConeFPT.CountedThresholdSearch

/-! ### 1. TM2 output length bound -/

private lemma runsWithin_output_length_le {M : Machine} {inp out : List Sym} {T : ℝ}
    (h : RunsWithin M inp out T) :
    (out.length : ℝ) ≤ (inp.length : ℝ) + T * (M.tm.growth : ℝ) := by
  obtain ⟨m, hm, ⟨hh⟩⟩ := h
  have hl := hh.output_length_le
  simp only [List.length_map] at hl
  exact (by exact_mod_cast hl : (out.length : ℝ) ≤ (inp.length : ℝ) + (m : ℝ) * (M.tm.growth : ℝ)).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg _)))

/-! ### 2. Canonical candidate permutation invariance -/

private def resKey {d : ℕ} (r : Residue d) : List ℕ :=
  (List.finRange d).map fun j => (r j : ℕ)

private lemma resKey_injective {d : ℕ} : Function.Injective (resKey (d := d)) := by
  intro r₁ r₂ h
  ext j
  have hj := congr_arg (fun l : List ℕ => l.getD j 0) h
  have hj₁ : (resKey r₁).getD j 0 = (r₁ j : ℕ) := by
    simp [resKey, List.getD_eq_getElem?_getD]
  have hj₂ : (resKey r₂).getD j 0 = (r₂ j : ℕ) := by
    simp [resKey, List.getD_eq_getElem?_getD]
  rw [hj₁, hj₂] at hj
  exact hj

private def CanonCand (I : Instance) (R : Cand I) : Prop :=
  ∀ t, (R t).length ≤ 2 ^ I.d ∧ ((R t).map resKey).Pairwise (· < ·)

private lemma canonCand_isCandidate {I : Instance} {R : Cand I} (h : CanonCand I R) :
    IsCandidate I R := by
  intro t
  refine ⟨?_, (h t).1⟩
  apply List.Nodup.of_map resKey
  rw [List.nodup_iff_pairwise_ne]
  exact (h t).2.imp (fun {a b} hab => ne_of_lt hab)

private lemma perm_equiv {α : Type*} {l₁ l₂ : List α} (h : l₁.Perm l₂) :
    ∃ e : Fin l₁.length ≃ Fin l₂.length, ∀ i, l₂.get (e i) = l₁.get i := by
  induction h with
  | nil => exact ⟨Equiv.refl _, fun i => Fin.elim0 i⟩
  | cons x _ ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨{ toFun := Fin.cases 0 (fun j => (e j).succ)
              invFun := Fin.cases 0 (fun j => (e.symm j).succ)
              left_inv := Fin.cases rfl (fun j => by simp)
              right_inv := Fin.cases rfl (fun j => by simp) }, ?_⟩
    exact Fin.cases rfl (fun j => by simpa using he j)
  | swap x y l =>
    refine ⟨Equiv.swap ⟨0, by simp⟩ ⟨1, by simp⟩, ?_⟩
    intro i
    rcases i with ⟨_ | _ | n, hn⟩
    · simp
    · simp
    · simp [Equiv.swap_apply_of_ne_of_ne]
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨e₁, he₁⟩ := ih₁
    obtain ⟨e₂, he₂⟩ := ih₂
    exact ⟨e₁.trans e₂, fun i => (he₂ (e₁ i)).trans (he₁ i)⟩

private lemma exists_canonCand_perm (I : Instance) (R : Cand I) (hR : IsCandidate I R) :
    ∃ R' : Cand I, CanonCand I R' ∧ ∀ t, (R' t).Perm (R t) := by
  let cmp : Residue I.d → Residue I.d → Bool := fun r₁ r₂ => decide (resKey r₁ ≤ resKey r₂)
  refine ⟨fun t => (R t).mergeSort cmp, ?_, fun t => List.mergeSort_perm _ _⟩
  intro t
  have hperm : ((R t).mergeSort cmp).Perm (R t) := List.mergeSort_perm _ _
  refine ⟨?_, ?_⟩
  · rw [hperm.length_eq]
    exact (hR t).2
  · have hnodup : (((R t).mergeSort cmp).map resKey).Nodup :=
      (hperm.nodup_iff.mpr (hR t).1).map resKey_injective
    have hne : (((R t).mergeSort cmp).map resKey).Pairwise (· ≠ ·) :=
      List.nodup_iff_pairwise_ne.mp hnodup
    have hle_raw : ((R t).mergeSort cmp).Pairwise (fun a b => resKey a ≤ resKey b) := by
      have hp := List.pairwise_mergeSort
        (le := cmp)
        (fun a b c hab hbc => by
          simp only [cmp, decide_eq_true_eq] at hab hbc ⊢
          exact le_trans hab hbc)
        (fun a b => by
          simp only [cmp, Bool.or_eq_true, decide_eq_true_eq]
          exact le_total (resKey a) (resKey b))
        (R t)
      exact hp.imp (fun {a b} hab => by simpa [cmp] using hab)
    have hle : (((R t).mergeSort cmp).map resKey).Pairwise (· ≤ ·) :=
      List.pairwise_map.mpr hle_raw
    exact (hle.and hne).imp (fun {a b} hab => lt_of_le_of_ne hab.1 hab.2)

private lemma khat_integral_of_perm {I : Instance} {R R' : Cand I} {N : ℕ} {γ : ℚ}
    (hperm : ∀ t, (R' t).Perm (R t))
    (hex : ∃ zn ∈ Khat I R N γ, IsIntegral zn) :
    ∃ zn' ∈ Khat I R' N γ, IsIntegral zn' := by
  choose e he using fun t => perm_equiv (hperm t)
  obtain ⟨zn, ⟨ξ, hξK, hξzn⟩, hInt⟩ := hex
  let ξ' : Blocks I R' := fun t i => ξ t (e t i)
  let zn' : (t : Fin I.τ) → Fin (R' t).length → (Fin I.d → ℝ) × ℝ :=
    fun t i => zn t (e t i)
  have hagg : ∀ t, blockAgg ξ' t = blockAgg ξ t := fun t => by
    unfold blockAgg
    exact Equiv.sum_comp (e t) (fun i => ((ξ t i).1, (ξ t i).2.1))
  have hcnt : ∀ t, blockCount ξ' t = blockCount ξ t := fun t => by
    unfold blockCount
    exact Equiv.sum_comp (e t) (fun i => (ξ t i).2.2)
  refine ⟨zn', ⟨ξ', ?_, fun t i => hξzn t (e t i)⟩, fun t i => hInt t (e t i)⟩
  rcases hξK with ⟨hQ, hCr, hA, hN, hPhi⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hagg] using hQ
  · intro t i
    simpa only [he t i] using hCr t (e t i)
  · simpa only [hagg, hcnt] using hA
  · simpa only [hcnt] using hN
  · have hPhiEq : (∑ t, ∑ i, I.Phi t ((R' t).get i) (ξ' t i)) =
        ∑ t, ∑ i, I.Phi t ((R t).get i) (ξ t i) := by
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [ξ', ← he t]
      exact Equiv.sum_comp (e t) (fun i => I.Phi t ((R t).get i) (ξ t i))
    rw [hPhiEq]
    exact hPhi

/-! ### 3. Encoding length bounds -/

private lemma posNum_pow_len_sub_one_le (p : PosNum) :
    1 ≤ (Computability.encodePosNum p).length ∧
      2 ^ ((Computability.encodePosNum p).length - 1) ≤ (p : ℕ) := by
  induction p with
  | one => simp [Computability.encodePosNum]
  | bit0 p ih =>
      obtain ⟨h1, h2⟩ := ih
      simp only [Computability.encodePosNum, List.length_cons, PosNum.cast_bit0]
      refine ⟨by omega, ?_⟩
      have hlen : (Computability.encodePosNum p).length =
          ((Computability.encodePosNum p).length - 1) + 1 := by omega
      conv_lhs => rw [Nat.add_sub_cancel, hlen, pow_succ']
      omega
  | bit1 p ih =>
      obtain ⟨h1, h2⟩ := ih
      simp only [Computability.encodePosNum, List.length_cons, PosNum.cast_bit1]
      refine ⟨by omega, ?_⟩
      have hlen : (Computability.encodePosNum p).length =
          ((Computability.encodePosNum p).length - 1) + 1 := by omega
      conv_lhs => rw [Nat.add_sub_cancel, hlen, pow_succ']
      omega

private lemma encNat_len_le_of_lt {n m : ℕ} (h : n < 2 ^ m) : (encNat n).length ≤ m := by
  simp only [encNat, List.length_map, Computability.encodeNat]
  conv_lhs at h => rw [← Num.to_of_nat n]
  cases hn : (n : Num) with
  | zero => simp [Computability.encodeNum]
  | pos p =>
      simp only [Computability.encodeNum]
      simp only [hn] at h
      obtain ⟨h1, h2⟩ := posNum_pow_len_sub_one_le p
      have hp : 2 ^ ((Computability.encodePosNum p).length - 1) < 2 ^ m :=
        lt_of_le_of_lt h2 (by simpa using h)
      have hlt : (Computability.encodePosNum p).length - 1 < m :=
        (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hp
      omega

private lemma encNat_len_le_of_le {n m : ℕ} (h : n ≤ 2 ^ m) : (encNat n).length ≤ m + 1 :=
  encNat_len_le_of_lt (lt_of_le_of_lt h (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self m)))

private lemma length_flatMap_finRange_le {n : ℕ} {α : Type*} (f : Fin n → List α) (c : ℕ)
    (hc : ∀ i, (f i).length ≤ c) :
    ((List.finRange n).flatMap f).length ≤ n * c := by
  rw [List.length_flatMap, ← Fin.sum_univ_def]
  calc ∑ i : Fin n, (f i).length
    _ ≤ ∑ _ : Fin n, c := Finset.sum_le_sum fun i _ => hc i
    _ = n * c := by simp

private lemma list_sum_map_le {α : Type*} (l : List α) (f : α → ℕ) (c : ℕ)
    (hc : ∀ a ∈ l, f a ≤ c) : (l.map f).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hx := hc x List.mem_cons_self
      have hxs := ih fun a ha => hc a (List.mem_cons_of_mem x ha)
      nlinarith

private lemma length_le_length_flatMap {α β : Type*} {l : List α} {f : α → List β} {a : α}
    (ha : a ∈ l) : (f a).length ≤ (l.flatMap f).length := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append]
      rcases List.mem_cons.mp ha with rfl | hxs
      · exact Nat.le_add_right _ _
      · exact (ih hxs).trans (Nat.le_add_left _ _)

private lemma encResidue_len_le {d : ℕ} (r : Residue d) :
    (encResidue r).length ≤ d * (d + 1) := by
  unfold encResidue
  refine length_flatMap_finRange_le _ (d + 1) fun i => ?_
  rw [List.length_append, List.length_singleton]
  exact Nat.add_le_add_right (encNat_len_le_of_lt (r i).isLt) 1

private lemma encCand_len_le {I : Instance} {R : Cand I} (hR : IsCandidate I R) :
    (encCand R).length ≤ I.τ * (I.d + 2 + 2 ^ I.d * (I.d * (I.d + 1))) := by
  unfold encCand
  refine length_flatMap_finRange_le _ _ fun t => ?_
  simp only [List.length_append, List.length_singleton]
  have h1 : (encNat (R t).length).length ≤ I.d + 1 := encNat_len_le_of_le (hR t).2
  have h2 : ((R t).flatMap (fun r => encResidue r)).length ≤ 2 ^ I.d * (I.d * (I.d + 1)) := by
    rw [List.length_flatMap]
    calc ((R t).map (fun r => (encResidue r).length)).sum
      _ ≤ (R t).length * (I.d * (I.d + 1)) :=
          list_sum_map_le (R t) (fun r => (encResidue r).length) (I.d * (I.d + 1))
            (fun r _ => encResidue_len_le r)
      _ ≤ 2 ^ I.d * (I.d * (I.d + 1)) := Nat.mul_le_mul_right _ (hR t).2
  omega

private lemma encRat_div_len_le {numZ : ℤ} {q L : ℕ}
    (hq0 : 0 < q) (hqB : q ≤ 2 ^ L) (hnum : numZ.natAbs ≤ 2 ^ (L ^ 2 + 4 * L)) :
    (encRat ((numZ : ℚ) / (q : ℚ))).length ≤ L ^ 2 + 5 * L + 4 := by
  set γ : ℚ := (numZ : ℚ) / (q : ℚ)
  have hqR0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq0.ne'
  have hdenR0 : (γ.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr γ.den_nz
  have hrat : (γ.num : ℚ) / (γ.den : ℚ) = (numZ : ℚ) / (q : ℚ) := by
    rw [Rat.num_div_den]
  have hcrossQ : (γ.num : ℚ) * (q : ℚ) = (numZ : ℚ) * (γ.den : ℚ) := by
    field_simp [hqR0, hdenR0] at hrat
    linarith
  have hcrossZ : γ.num * (q : ℤ) = numZ * (γ.den : ℤ) := by
    exact_mod_cast hcrossQ
  have hcrossN : γ.num.natAbs * q = numZ.natAbs * γ.den := by
    have h := congr_arg Int.natAbs hcrossZ
    simpa [Int.natAbs_mul] using h
  have hdvd : γ.den ∣ q := by
    refine γ.reduced.symm.dvd_of_dvd_mul_left ?_
    rw [hcrossN]
    exact dvd_mul_left _ _
  have hden_le_q : γ.den ≤ q := Nat.le_of_dvd hq0 hdvd
  have hden_le : γ.den ≤ 2 ^ L := le_trans hden_le_q hqB
  have hnum_le : γ.num.natAbs ≤ 2 ^ (L ^ 2 + 4 * L) := by
    have hmul : γ.num.natAbs * q ≤ numZ.natAbs * q := by
      rw [hcrossN]
      exact Nat.mul_le_mul_left _ hden_le_q
    exact le_trans (Nat.le_of_mul_le_mul_right hmul hq0) hnum
  have hnum_len : (encNat γ.num.natAbs).length ≤ L ^ 2 + 4 * L + 1 :=
    encNat_len_le_of_le hnum_le
  have hden_len : (encNat γ.den).length ≤ L + 1 :=
    encNat_len_le_of_le hden_le
  simp only [encRat, encInt, List.length_append, List.length_cons, List.length_nil]
  omega

private lemma encLift_block_len_le {I : Instance} {R : Cand I}
    (s : (t : Fin I.τ) → Fin (R t).length → (Fin I.d → ℤ) × (Fin I.k → ℚ) × ℕ)
    (t : Fin I.τ) (i : Fin (R t).length) :
    (encIntVec (s t i).1 ++ encVec (s t i).2.1 ++ encNat (s t i).2.2 ++ [3]).length ≤
      (encLift (R := R) (some s)).length := by
  have ht_mem : t ∈ List.finRange I.τ := List.mem_finRange t
  have hi_mem : i ∈ List.finRange (R t).length := List.mem_finRange i
  have h1 := length_le_length_flatMap
    (f := fun j => encGen (s t j).1 (s t j).2.1 ++ encNat (s t j).2.2 ++ [3]) hi_mem
  have h2 := length_le_length_flatMap (f := fun t' =>
    (List.finRange (R t').length).flatMap fun j =>
      encGen (s t' j).1 (s t' j).2.1 ++ encNat (s t' j).2.2 ++ [3]) ht_mem
  calc (encIntVec (s t i).1 ++ encVec (s t i).2.1 ++ encNat (s t i).2.2 ++ [3]).length
    _ = (encGen (s t i).1 (s t i).2.1 ++ encNat (s t i).2.2 ++ [3]).length := by
        simp [encGen, List.length_append]
    _ ≤ ((List.finRange (R t).length).flatMap fun j =>
          encGen (s t j).1 (s t j).2.1 ++ encNat (s t j).2.2 ++ [3]).length := h1
    _ ≤ ((List.finRange I.τ).flatMap fun t' =>
          (List.finRange (R t').length).flatMap fun j =>
            encGen (s t' j).1 (s t' j).2.1 ++ encNat (s t' j).2.2 ++ [3]).length := h2
    _ ≤ (encLift (R := R) (some s)).length := by
        simp [encLift]

private lemma encLocal_len_le {I : Instance} {t : Fin I.τ} {r : Residue I.d} {L : ℕ}
    (hIlen : (encInstance I).length ≤ L) (hτL : I.τ ≤ L) (hdL : I.d ≤ L) (hL1 : 1 ≤ L) :
    (encLocal I t r).length ≤ 5 * L ^ 2 := by
  have ht_lt : (t : ℕ) < 2 ^ L :=
    lt_of_lt_of_le (lt_of_lt_of_le t.isLt hτL) (Nat.le_of_lt Nat.lt_two_pow_self)
  have ht_len : (encNat t).length ≤ L := encNat_len_le_of_lt ht_lt
  have hr_len : (encResidue r).length ≤ L * (L + 1) :=
    (encResidue_len_le r).trans (Nat.mul_le_mul hdL (Nat.add_le_add_right hdL 1))
  have hL_le : L ≤ L ^ 2 := by nlinarith
  have h1_le : 1 ≤ L ^ 2 := by nlinarith
  unfold encLocal
  simp only [List.length_append, List.length_singleton]
  nlinarith

/-! ### 4. Certificate algebra (`aggr`, `count`, `costOf`, `Supported`, `EReal`) -/

private lemma aggr_zero {d k : ℕ} : aggr (d := d) (k := k) 0 = 0 := by
  simp [aggr]

private lemma aggr_add {d k : ℕ} (μ₁ μ₂ : Gen d k →₀ ℕ) :
    aggr (μ₁ + μ₂) = aggr μ₁ + aggr μ₂ := by
  unfold aggr
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; module)

private lemma aggr_single {d k : ℕ} (g : Gen d k) (n : ℕ) :
    aggr (Finsupp.single g n) = (n : ℝ) • g.toReal := by
  unfold aggr
  exact Finsupp.sum_single_index (by simp)

private lemma aggr_certList {d k : ℕ} (l : List ((Fin d → ℤ) × (Fin k → ℚ) × ℕ)) :
    aggr ((l.map fun c => Finsupp.single (certGen c) c.2.2).sum) =
      (l.map fun c => (c.2.2 : ℝ) • (certGen c).toReal).sum := by
  induction l with
  | nil => simp [aggr_zero]
  | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons, aggr_add, aggr_single, ih]

private lemma aggr_finset_sum {d k : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Gen d k →₀ ℕ) :
    aggr (∑ i ∈ s, f i) = ∑ i ∈ s, aggr (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [aggr_zero]
  | insert a s ha ih => simp [Finset.sum_insert ha, aggr_add, ih]

private lemma count_zero {d k : ℕ} : count (d := d) (k := k) 0 = 0 := by
  simp [count]

private lemma count_add {d k : ℕ} (μ₁ μ₂ : Gen d k →₀ ℕ) :
    count (μ₁ + μ₂) = count μ₁ + count μ₂ := by
  unfold count
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

private lemma count_single {d k : ℕ} (g : Gen d k) (n : ℕ) :
    count (Finsupp.single g n) = n := by
  unfold count
  exact Finsupp.sum_single_index rfl

private lemma count_certList {d k : ℕ} (l : List ((Fin d → ℤ) × (Fin k → ℚ) × ℕ)) :
    count ((l.map fun c => Finsupp.single (certGen c) c.2.2).sum) =
      (l.map fun c => c.2.2).sum := by
  induction l with
  | nil => simp [count_zero]
  | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons, count_add, count_single, ih]

private lemma count_finset_sum {d k : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Gen d k →₀ ℕ) :
    count (∑ i ∈ s, f i) = ∑ i ∈ s, count (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [count_zero]
  | insert a s ha ih => simp [Finset.sum_insert ha, count_add, ih]

private lemma costOf_zero {d k : ℕ} (f : (Fin d → ℝ) → ℝ) :
    costOf (d := d) (k := k) f 0 = 0 := by
  simp [costOf]

private lemma costOf_add {d k : ℕ} (f : (Fin d → ℝ) → ℝ) (μ₁ μ₂ : Gen d k →₀ ℕ) :
    costOf f (μ₁ + μ₂) = costOf f μ₁ + costOf f μ₂ := by
  unfold costOf
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring)

private lemma costOf_single {d k : ℕ} (f : (Fin d → ℝ) → ℝ) (g : Gen d k) (n : ℕ) :
    costOf f (Finsupp.single g n) = (n : ℝ) * f (fun i => (g.1 i : ℝ)) := by
  unfold costOf
  exact Finsupp.sum_single_index (by simp)

private lemma costOf_certList {d k : ℕ} (f : (Fin d → ℝ) → ℝ)
    (l : List ((Fin d → ℤ) × (Fin k → ℚ) × ℕ)) :
    costOf f ((l.map fun c => Finsupp.single (certGen c) c.2.2).sum) =
      (l.map fun c => (c.2.2 : ℝ) * f (fun i => (c.1 i : ℝ))).sum := by
  induction l with
  | nil => simp [costOf_zero]
  | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons, costOf_add, costOf_single, ih]
      rfl

private lemma costOf_finset_sum {d k : ℕ} {ι : Type*} (f : (Fin d → ℝ) → ℝ)
    (s : Finset ι) (μ : ι → Gen d k →₀ ℕ) :
    costOf f (∑ i ∈ s, μ i) = ∑ i ∈ s, costOf f (μ i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [costOf_zero]
  | insert a s ha ih => simp [Finset.sum_insert ha, costOf_add, ih]

private lemma mem_support_certList {d k : ℕ}
    (l : List ((Fin d → ℤ) × (Fin k → ℚ) × ℕ)) {g : Gen d k}
    (hg : g ∈ ((l.map fun c => Finsupp.single (certGen c) c.2.2).sum).support) :
    ∃ c ∈ l, g = certGen c := by
  induction l with
  | nil => simp at hg
  | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons] at hg
      have hsub := Finsupp.support_add hg
      rcases Finset.mem_union.mp hsub with hc | hcs
      · have hgc : g = certGen c := Finset.mem_singleton.mp (Finsupp.support_single_subset hc)
        exact ⟨c, List.mem_cons_self, hgc⟩
      · obtain ⟨c', hc'mem, hgc'⟩ := ih hcs
        exact ⟨c', List.mem_cons_of_mem c hc'mem, hgc'⟩

private lemma coe_finset_sum_ereal {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, ((f i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

private lemma finset_sum_le_sum_ereal {ι : Type*} (s : Finset ι) (f g : ι → EReal)
    (h : ∀ i ∈ s, f i ≤ g i) :
    ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact add_le_add (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ### 5. FPT runtime absorption -/

private lemma one_le_tau_logb {τ : ℕ} (hτ : 1 ≤ τ) :
    (1 : ℝ) ≤ (τ : ℝ) * Real.logb 2 ((τ : ℝ) + 1) := by
  have hτR : (1 : ℝ) ≤ (τ : ℝ) := by exact_mod_cast hτ
  have hlog : (1 : ℝ) ≤ Real.logb 2 ((τ : ℝ) + 1) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (by linarith)]
    linarith [Real.rpow_one (2 : ℝ)]
  nlinarith

private lemma nat_le_two_rpow (n : ℕ) : (n : ℝ) ≤ (2 : ℝ) ^ (n : ℝ) := by
  rw [Real.rpow_natCast]
  exact_mod_cast Nat.le_of_lt Nat.lt_two_pow_self

private lemma fptBound_mono_L {C τ d L₁ L₂ : ℕ} (hL : L₁ ≤ L₂) :
    fptBound C τ d L₁ ≤ fptBound C τ d L₂ := by
  unfold fptBound
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hL) C

private lemma fptBound_nonneg (C τ d L : ℕ) : 0 ≤ fptBound C τ d L := by
  unfold fptBound
  positivity

private lemma oracleBound_mono_L {C d L₁ L₂ : ℕ} (hL : L₁ ≤ L₂) :
    oracleBound C d L₁ ≤ oracleBound C d L₂ := by
  unfold oracleBound
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hL) C

private lemma oracleBound_nonneg (C d L : ℕ) : 0 ≤ oracleBound C d L := by
  unfold oracleBound
  positivity

private lemma exp_factor_bound {C_base C_drv k₁ C d : ℕ} {α : ℝ}
    (hd1 : 1 ≤ d) (hα1 : 1 ≤ α) (hC : C_base + C_drv + k₁ + 4 ≤ C) :
    ((2 : ℝ) ^ (α * (2 : ℝ) ^ ((C_base : ℝ) * d))) ^ C_drv * (2 : ℝ) ^ (k₁ * d) ≤
      (2 : ℝ) ^ (α * (2 : ℝ) ^ ((C : ℝ) * d)) := by
  have hα0 : 0 ≤ α := le_trans zero_le_one hα1
  have hdR : (1 : ℝ) ≤ (d : ℝ) := Nat.one_le_cast.mpr hd1
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := le_trans zero_le_one hdR
  have hF_pow : ((2 : ℝ) ^ (α * (2 : ℝ) ^ ((C_base : ℝ) * d))) ^ C_drv =
      (2 : ℝ) ^ ((C_drv : ℝ) * (α * (2 : ℝ) ^ ((C_base : ℝ) * d))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have h2_pow : ((2 : ℝ) ^ (k₁ * d)) = (2 : ℝ) ^ (((k₁ * d : ℕ) : ℝ)) :=
    (Real.rpow_natCast 2 (k₁ * d)).symm
  rw [hF_pow, h2_pow, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hd_le_2d : (d : ℝ) ≤ (2 : ℝ) ^ ((C_base + 1 : ℝ) * d) := by
    calc (d : ℝ) ≤ (2 : ℝ) ^ (d : ℝ) := nat_le_two_rpow d
      _ ≤ (2 : ℝ) ^ ((C_base + 1 : ℝ) * d) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          calc (d : ℝ) = 1 * (d : ℝ) := (one_mul _).symm
            _ ≤ ((C_base : ℝ) + 1) * (d : ℝ) :=
                mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) C_base]) hd0
  have h2d_mono : (2 : ℝ) ^ ((C_base : ℝ) * d) ≤ (2 : ℝ) ^ ((C_base + 1 : ℝ) * d) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    exact mul_le_mul_of_nonneg_right (by linarith) hd0
  have hKd : ((k₁ * d : ℕ) : ℝ) ≤ α * ((k₁ : ℝ) * (2 : ℝ) ^ ((C_base + 1 : ℝ) * d)) := by
    calc ((k₁ * d : ℕ) : ℝ) = 1 * ((k₁ : ℝ) * (d : ℝ)) := by push_cast; ring
      _ ≤ α * ((k₁ : ℝ) * (2 : ℝ) ^ ((C_base + 1 : ℝ) * d)) :=
          mul_le_mul hα1 (mul_le_mul_of_nonneg_left hd_le_2d (Nat.cast_nonneg _))
            (by positivity) hα0
  have hCd : (C_drv : ℝ) * (α * (2 : ℝ) ^ ((C_base : ℝ) * d)) ≤
      α * ((C_drv : ℝ) * (2 : ℝ) ^ ((C_base + 1 : ℝ) * d)) := by
    calc (C_drv : ℝ) * (α * (2 : ℝ) ^ ((C_base : ℝ) * d))
      _ = ((C_drv : ℝ) * α) * (2 : ℝ) ^ ((C_base : ℝ) * d) := by ring
      _ ≤ ((C_drv : ℝ) * α) * (2 : ℝ) ^ ((C_base + 1 : ℝ) * d) :=
          mul_le_mul_of_nonneg_left h2d_mono (mul_nonneg (Nat.cast_nonneg _) hα0)
      _ = α * ((C_drv : ℝ) * (2 : ℝ) ^ ((C_base + 1 : ℝ) * d)) := by ring
  have hCoef : (C_drv : ℝ) + (k₁ : ℝ) ≤ (2 : ℝ) ^ ((C_drv + k₁ + 1 : ℕ) : ℝ) := by
    have h := nat_le_two_rpow (C_drv + k₁ + 1)
    have hcast : ((C_drv + k₁ + 1 : ℕ) : ℝ) = (C_drv : ℝ) + (k₁ : ℝ) + 1 := by push_cast; ring
    linarith
  have hExpC : (2 : ℝ) ^ ((C_drv + k₁ + 1 : ℕ) : ℝ) * (2 : ℝ) ^ ((C_base + 1 : ℝ) * d) ≤
      (2 : ℝ) ^ ((C : ℝ) * d) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hC_geR : ((C_base + C_drv + k₁ + 4 : ℕ) : ℝ) ≤ (C : ℝ) := Nat.cast_le.mpr hC
    have hcast1 : ((C_drv + k₁ + 1 : ℕ) : ℝ) = (C_drv : ℝ) + (k₁ : ℝ) + 1 := by push_cast; ring
    have hcast2 : ((C_base + C_drv + k₁ + 4 : ℕ) : ℝ) =
        (C_base : ℝ) + (C_drv : ℝ) + (k₁ : ℝ) + 4 := by push_cast; ring
    rw [hcast1]
    rw [hcast2] at hC_geR
    have h1d : ((C_drv : ℝ) + (k₁ : ℝ) + 1) ≤ ((C_drv : ℝ) + (k₁ : ℝ) + 1) * (d : ℝ) :=
      le_mul_of_one_le_right (by positivity) hdR
    calc ((C_drv : ℝ) + (k₁ : ℝ) + 1) + ((C_base : ℝ) + 1) * (d : ℝ)
      _ ≤ ((C_drv : ℝ) + (k₁ : ℝ) + 1) * (d : ℝ) + ((C_base : ℝ) + 1) * (d : ℝ) := by linarith [h1d]
      _ = ((C_base : ℝ) + (C_drv : ℝ) + (k₁ : ℝ) + 2) * (d : ℝ) := by ring
      _ ≤ (C : ℝ) * (d : ℝ) := mul_le_mul_of_nonneg_right (by linarith) hd0
  calc (C_drv : ℝ) * (α * (2 : ℝ) ^ ((C_base : ℝ) * d)) + ((k₁ * d : ℕ) : ℝ)
    _ ≤ α * ((C_drv : ℝ) * (2 : ℝ) ^ ((C_base + 1 : ℝ) * d)) +
          α * ((k₁ : ℝ) * (2 : ℝ) ^ ((C_base + 1 : ℝ) * d)) := add_le_add hCd hKd
    _ = α * (((C_drv : ℝ) + (k₁ : ℝ)) * (2 : ℝ) ^ ((C_base + 1 : ℝ) * d)) := by ring
    _ ≤ α * ((2 : ℝ) ^ ((C_drv + k₁ + 1 : ℕ) : ℝ) * (2 : ℝ) ^ ((C_base + 1 : ℝ) * d)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hCoef (by positivity)) hα0
    _ ≤ α * (2 : ℝ) ^ ((C : ℝ) * d) :=
        mul_le_mul_of_nonneg_left hExpC hα0

private lemma d_add_one_le_two_pow (d : ℕ) : d + 1 ≤ 2 ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      have h2 : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by decide)
      rw [pow_succ']
      omega

private lemma cand_exp_le {d : ℕ} (hd : 1 ≤ d) : d + 1 + d ^ 2 * 2 ^ d ≤ 2 ^ (4 * d) := by
  have h1 : d + 1 ≤ 2 ^ d := d_add_one_le_two_pow d
  have hd_le : d ≤ 2 ^ d := Nat.le_trans (Nat.le_succ d) h1
  have hd2 : d ^ 2 ≤ 2 ^ (2 * d) := by
    calc d ^ 2 ≤ (2 ^ d) ^ 2 := Nat.pow_le_pow_left hd_le 2
      _ = 2 ^ (2 * d) := by rw [← pow_mul, mul_comm]
  have hterm : d ^ 2 * 2 ^ d ≤ 2 ^ (3 * d) := by
    calc d ^ 2 * 2 ^ d ≤ 2 ^ (2 * d) * 2 ^ d := Nat.mul_le_mul_right _ hd2
      _ = 2 ^ (3 * d) := by rw [← pow_add]; congr 1; omega
  have h1le3 : 2 ^ d ≤ 2 ^ (3 * d) := Nat.pow_le_pow_right (by decide) (by omega)
  have h3add1 : 3 * d + 1 ≤ 4 * d := by omega
  calc d + 1 + d ^ 2 * 2 ^ d
    _ ≤ 2 ^ (3 * d) + 2 ^ (3 * d) := Nat.add_le_add (le_trans h1 h1le3) hterm
    _ = 2 ^ (3 * d + 1) := by rw [pow_succ']; omega
    _ ≤ 2 ^ (4 * d) := Nat.pow_le_pow_right (by decide) h3add1

private lemma logb_d_add_one_le (d : ℕ) : Real.logb 2 ((d : ℝ) + 1) ≤ (d : ℝ) := by
  rw [Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (by positivity)]
  rw [Real.rpow_natCast]
  exact_mod_cast d_add_one_le_two_pow d

private lemma fptBound_threshold_absorb (C_13 C_6 C_drv g_13 : ℕ) :
    ∃ e : ℕ, ∀ {τ d L N_cand L13_max L6_max : ℕ},
      1 ≤ d → 1 ≤ τ → 1 ≤ L →
      N_cand ≤ 2 ^ (τ * (d + 1 + d ^ 2 * 2 ^ d)) →
      L13_max ≤ 2 ^ (7 * d) * L ^ 2 →
      (L6_max : ℝ) ≤ 5 * (L : ℝ) ^ 2 + (L13_max : ℝ) + (fptBound C_13 τ d L13_max + 1) * (g_13 : ℝ) →
      ((N_cand : ℝ) + (L : ℝ) + (2 ^ d : ℝ) + fptBound C_13 τ d L13_max +
        oracleBound C_6 d L6_max + 2) ^ C_drv ≤ fptBound e τ d L := by
  set C_base : ℕ := max (max C_13 (C_6 + 3)) 4
  set P_13 : ℕ := 7 * C_13
  set E_13 : ℕ := 2 * C_13
  set P_L6 : ℕ := max 7 P_13 + g_13 + 2
  set E_L6 : ℕ := max 2 E_13
  set P_6 : ℕ := C_6 * P_L6
  set E_6 : ℕ := C_6 * E_L6
  set P : ℕ := max (max 1 P_13) P_6 + 3
  set E : ℕ := max (max 1 E_13) E_6
  set C_pow : ℕ := (C_6 + 1) * C_drv
  set K_pow : ℕ := P * C_drv
  set e : ℕ := max (E * C_drv) (C_base + C_pow + K_pow + 4)
  refine ⟨e, fun {τ d L N_cand L13_max L6_max} hd1 hτ1 hL1 hNcand hL13 hL6 => ?_⟩
  have hdR : (1 : ℝ) ≤ (d : ℝ) := Nat.one_le_cast.mpr hd1
  have hLR : (1 : ℝ) ≤ (L : ℝ) := Nat.one_le_cast.mpr hL1
  have hτR : (1 : ℝ) ≤ (τ : ℝ) := Nat.one_le_cast.mpr hτ1
  set α : ℝ := (τ : ℝ) * Real.logb 2 ((τ : ℝ) + 1)
  have hlogτ : (1 : ℝ) ≤ Real.logb 2 ((τ : ℝ) + 1) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (by linarith)]
    linarith [Real.rpow_one (2 : ℝ)]
  have hτ_le_α : (τ : ℝ) ≤ α := le_mul_of_one_le_right (by positivity) hlogτ
  have hα1 : 1 ≤ α := le_trans hτR hτ_le_α
  have hα0 : 0 ≤ α := le_trans zero_le_one hα1
  set F_base : ℝ := (2 : ℝ) ^ (α * (2 : ℝ) ^ ((C_base : ℝ) * d))
  have hF1 : 1 ≤ F_base := Real.one_le_rpow (by norm_num) (by positivity)
  have hF0 : 0 ≤ F_base := le_trans zero_le_one hF1
  have hF_mono : ∀ c ≤ C_base, (2 : ℝ) ^ (α * (2 : ℝ) ^ ((c : ℝ) * d)) ≤ F_base := fun c hc => by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_) hα0
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (by positivity)
  set F_13 : ℝ := (2 : ℝ) ^ (α * (2 : ℝ) ^ ((C_13 : ℝ) * d))
  have hF13_le : F_13 ≤ F_base := hF_mono C_13 (le_trans (le_max_left _ _) (le_max_left _ _))
  have hF13_1 : 1 ≤ F_13 := Real.one_le_rpow (by norm_num) (by positivity)
  have hfpt13 : fptBound C_13 τ d L13_max ≤ F_base * (2 : ℝ) ^ (P_13 * d) * (L : ℝ) ^ E_13 := by
    calc fptBound C_13 τ d L13_max
      _ ≤ fptBound C_13 τ d (2 ^ (7 * d) * L ^ 2) := fptBound_mono_L hL13
      _ = F_13 * ((2 : ℝ) ^ (7 * d) * (L : ℝ) ^ 2) ^ C_13 := by
          unfold fptBound
          push_cast
          rfl
      _ = F_13 * (2 : ℝ) ^ (P_13 * d) * (L : ℝ) ^ E_13 := by
          rw [mul_pow, ← pow_mul, ← pow_mul]
          have hp : 7 * d * C_13 = P_13 * d := by ring
          have he2 : 2 * C_13 = E_13 := rfl
          rw [hp, he2]
          ring
      _ ≤ F_base * (2 : ℝ) ^ (P_13 * d) * (L : ℝ) ^ E_13 := by
          gcongr
  have hNcand_le : (N_cand : ℝ) ≤ F_base := by
    have h1 : (N_cand : ℝ) ≤ (2 : ℝ) ^ (((τ * (d + 1 + d ^ 2 * 2 ^ d) : ℕ) : ℝ)) := by
      rw [Real.rpow_natCast]
      exact_mod_cast hNcand
    have h2 : ((τ * (d + 1 + d ^ 2 * 2 ^ d) : ℕ) : ℝ) ≤ α * (2 : ℝ) ^ ((4 : ℝ) * d) := by
      have hce : (d : ℝ) + 1 + (d : ℝ) ^ 2 * (2 : ℝ) ^ d ≤ (2 : ℝ) ^ ((4 : ℝ) * d) := by
        have hnat : ((d + 1 + d ^ 2 * 2 ^ d : ℕ) : ℝ) ≤ ((2 ^ (4 * d) : ℕ) : ℝ) :=
          Nat.cast_le.mpr (cand_exp_le hd1)
        rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast 2 (4 * d)] at hnat
        push_cast at hnat
        exact hnat
      push_cast
      exact mul_le_mul hτ_le_α hce (by positivity) hα0
    exact h1.trans ((Real.rpow_le_rpow_of_exponent_le (by norm_num) h2).trans
      (hF_mono 4 (le_max_right _ _)))
  have hL6_bound : (L6_max : ℝ) ≤ F_base * (2 : ℝ) ^ (P_L6 * d) * (L : ℝ) ^ E_L6 := by
    have h2_pow_d : ∀ c : ℕ, c ≤ 2 ^ (c * d) := fun c => by
      have h1 : c ≤ 2 ^ c := Nat.le_of_lt Nat.lt_two_pow_self
      exact le_trans h1 (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right c hd1))
    have hg13 : (g_13 : ℝ) ≤ (2 : ℝ) ^ (g_13 * d) := by exact_mod_cast h2_pow_d g_13
    have h5 : (5 : ℝ) ≤ (2 : ℝ) ^ (7 * d) := by
      have h5_le : 5 ≤ 2 ^ 7 := by decide
      exact_mod_cast le_trans h5_le (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right 7 hd1))
    have hL2_le : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ E_L6 := pow_le_pow_right₀ hLR (le_max_left 2 E_13)
    have hLE13_le : (L : ℝ) ^ E_13 ≤ (L : ℝ) ^ E_L6 := pow_le_pow_right₀ hLR (le_max_right 2 E_13)
    have hL13R : (L13_max : ℝ) ≤ (2 : ℝ) ^ (7 * d) * (L : ℝ) ^ 2 := by exact_mod_cast hL13
    have hP7 : (2 : ℝ) ^ (7 * d) ≤ (2 : ℝ) ^ (max 7 P_13 * d) :=
      pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right d (le_max_left _ _))
    have hP13_le : (2 : ℝ) ^ (P_13 * d) ≤ (2 : ℝ) ^ (max 7 P_13 * d) :=
      pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right d (le_max_right _ _))
    have hterm1 : 5 * (L : ℝ) ^ 2 ≤ F_base * (2 : ℝ) ^ ((max 7 P_13 + g_13) * d) * (L : ℝ) ^ E_L6 := by
      calc 5 * (L : ℝ) ^ 2
        _ ≤ 1 * (2 : ℝ) ^ (7 * d) * (L : ℝ) ^ 2 := by
            rw [one_mul]
            exact mul_le_mul_of_nonneg_right h5 (by positivity)
        _ ≤ F_base * (2 : ℝ) ^ ((max 7 P_13 + g_13) * d) * (L : ℝ) ^ E_L6 := by
            refine mul_le_mul (mul_le_mul hF1 (hP7.trans (pow_le_pow_right₀ (by norm_num)
              (Nat.mul_le_mul_right d (Nat.le_add_right _ _)))) (by positivity) hF0) hL2_le
              (by positivity) (by positivity)
    have hterm2 : (L13_max : ℝ) ≤ F_base * (2 : ℝ) ^ ((max 7 P_13 + g_13) * d) * (L : ℝ) ^ E_L6 := by
      calc (L13_max : ℝ)
        _ ≤ 1 * (2 : ℝ) ^ (7 * d) * (L : ℝ) ^ 2 := by rw [one_mul]; exact hL13R
        _ ≤ F_base * (2 : ℝ) ^ ((max 7 P_13 + g_13) * d) * (L : ℝ) ^ E_L6 := by
            refine mul_le_mul (mul_le_mul hF1 (hP7.trans (pow_le_pow_right₀ (by norm_num)
              (Nat.mul_le_mul_right d (Nat.le_add_right _ _)))) (by positivity) hF0) hL2_le
              (by positivity) (by positivity)
    have hterm3 : fptBound C_13 τ d L13_max * (g_13 : ℝ) ≤
        F_base * (2 : ℝ) ^ ((max 7 P_13 + g_13) * d) * (L : ℝ) ^ E_L6 := by
      calc fptBound C_13 τ d L13_max * (g_13 : ℝ)
        _ ≤ (F_base * (2 : ℝ) ^ (P_13 * d) * (L : ℝ) ^ E_13) * (2 : ℝ) ^ (g_13 * d) :=
            mul_le_mul hfpt13 hg13 (by positivity) (by positivity)
        _ = F_base * ((2 : ℝ) ^ (P_13 * d) * (2 : ℝ) ^ (g_13 * d)) * (L : ℝ) ^ E_13 := by ring
        _ = F_base * (2 : ℝ) ^ ((P_13 + g_13) * d) * (L : ℝ) ^ E_13 := by
            rw [← pow_add, ← add_mul]
        _ ≤ F_base * (2 : ℝ) ^ ((max 7 P_13 + g_13) * d) * (L : ℝ) ^ E_L6 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num)
              (Nat.mul_le_mul_right d (Nat.add_le_add_right (le_max_right _ _) _))) hF0)
              hLE13_le (by positivity) (by positivity)
    have hterm4 : (g_13 : ℝ) ≤ F_base * (2 : ℝ) ^ ((max 7 P_13 + g_13) * d) * (L : ℝ) ^ E_L6 := by
      have h1L : (1 : ℝ) ≤ (L : ℝ) ^ E_L6 := one_le_pow₀ hLR
      have h2_le : (2 : ℝ) ^ (g_13 * d) ≤ (2 : ℝ) ^ ((max 7 P_13 + g_13) * d) :=
        pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right d (Nat.le_add_left _ _))
      calc (g_13 : ℝ) = 1 * (g_13 : ℝ) * 1 := by ring
        _ ≤ F_base * (2 : ℝ) ^ ((max 7 P_13 + g_13) * d) * (L : ℝ) ^ E_L6 :=
            mul_le_mul (mul_le_mul hF1 (hg13.trans h2_le) (by positivity) hF0) h1L
              (by positivity) (by positivity)
    have h4_le : (4 : ℝ) * (2 : ℝ) ^ ((max 7 P_13 + g_13) * d) ≤ (2 : ℝ) ^ (P_L6 * d) := by
      have h4 : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      rw [h4, mul_comm, ← pow_add]
      refine pow_le_pow_right₀ (by norm_num) ?_
      have h2d : 2 ≤ 2 * d := by omega
      calc (max 7 P_13 + g_13) * d + 2
        _ ≤ (max 7 P_13 + g_13) * d + 2 * d := Nat.add_le_add_left h2d _
        _ = P_L6 * d := by ring
    calc (L6_max : ℝ)
      _ ≤ 5 * (L : ℝ) ^ 2 + (L13_max : ℝ) + fptBound C_13 τ d L13_max * (g_13 : ℝ) + (g_13 : ℝ) := by
          linarith
      _ ≤ 4 * (F_base * (2 : ℝ) ^ ((max 7 P_13 + g_13) * d) * (L : ℝ) ^ E_L6) := by
          linarith [hterm1, hterm2, hterm3, hterm4]
      _ = F_base * (4 * (2 : ℝ) ^ ((max 7 P_13 + g_13) * d)) * (L : ℝ) ^ E_L6 := by ring
      _ ≤ F_base * (2 : ℝ) ^ (P_L6 * d) * (L : ℝ) ^ E_L6 := by
          gcongr
  have horacle6 : oracleBound C_6 d L6_max ≤ F_base ^ (C_6 + 1) * (2 : ℝ) ^ (P_6 * d) * (L : ℝ) ^ E_6 := by
    have h_orac_exp : (2 : ℝ) ^ ((C_6 : ℝ) * (d : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) + 1)) ≤ F_base := by
      have h1 : (C_6 : ℝ) * (d : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) + 1) ≤ (C_6 : ℝ) * (d : ℝ) ^ 3 := by
        have hl := logb_d_add_one_le d
        calc (C_6 : ℝ) * (d : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) + 1)
          _ ≤ (C_6 : ℝ) * (d : ℝ) ^ 2 * (d : ℝ) := by gcongr
          _ = (C_6 : ℝ) * (d : ℝ) ^ 3 := by ring
      have hC6 : (C_6 : ℝ) ≤ (2 : ℝ) ^ (C_6 : ℝ) := nat_le_two_rpow C_6
      have hd3 : (d : ℝ) ^ 3 ≤ (2 : ℝ) ^ ((3 : ℝ) * d) := by
        calc (d : ℝ) ^ 3 ≤ ((2 : ℝ) ^ (d : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) (nat_le_two_rpow d) 3
          _ = (2 : ℝ) ^ ((3 : ℝ) * d) := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; ring
      have h2 : (C_6 : ℝ) * (d : ℝ) ^ 3 ≤ α * (2 : ℝ) ^ (((C_6 + 3 : ℕ) : ℝ) * d) := by
        have hd_mul : (C_6 : ℝ) ≤ (2 : ℝ) ^ ((C_6 : ℝ) * d) := by
          refine hC6.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
          exact le_mul_of_one_le_right (Nat.cast_nonneg _) hdR
        have hprod : (C_6 : ℝ) * (d : ℝ) ^ 3 ≤ (2 : ℝ) ^ ((C_6 : ℝ) * d) * (2 : ℝ) ^ ((3 : ℝ) * d) :=
          mul_le_mul hd_mul hd3 (by positivity) (by positivity)
        have hsum : (2 : ℝ) ^ ((C_6 : ℝ) * d) * (2 : ℝ) ^ ((3 : ℝ) * d) =
            (2 : ℝ) ^ (((C_6 + 3 : ℕ) : ℝ) * d) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1
          push_cast
          ring
        calc (C_6 : ℝ) * (d : ℝ) ^ 3
          _ ≤ 1 * (2 : ℝ) ^ (((C_6 + 3 : ℕ) : ℝ) * d) := by rw [one_mul, ← hsum]; exact hprod
          _ ≤ α * (2 : ℝ) ^ (((C_6 + 3 : ℕ) : ℝ) * d) :=
              mul_le_mul_of_nonneg_right hα1 (by positivity)
      exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) (h1.trans h2)).trans
        (hF_mono (C_6 + 3) (le_trans (le_max_right _ _) (le_max_left _ _)))
    have hL6pow : (L6_max : ℝ) ^ C_6 ≤ F_base ^ C_6 * (2 : ℝ) ^ (P_6 * d) * (L : ℝ) ^ E_6 := by
      calc (L6_max : ℝ) ^ C_6
        _ ≤ (F_base * (2 : ℝ) ^ (P_L6 * d) * (L : ℝ) ^ E_L6) ^ C_6 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hL6_bound C_6
        _ = F_base ^ C_6 * (2 : ℝ) ^ (P_6 * d) * (L : ℝ) ^ E_6 := by
            rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
            have hp : P_L6 * d * C_6 = P_6 * d := by ring
            have he2 : E_L6 * C_6 = E_6 := by ring
            rw [hp, he2]
    unfold oracleBound
    calc (2 : ℝ) ^ ((C_6 : ℝ) * (d : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) + 1)) * (L6_max : ℝ) ^ C_6
      _ ≤ F_base * (F_base ^ C_6 * (2 : ℝ) ^ (P_6 * d) * (L : ℝ) ^ E_6) :=
          mul_le_mul h_orac_exp hL6pow (by positivity) hF0
      _ = F_base ^ (C_6 + 1) * (2 : ℝ) ^ (P_6 * d) * (L : ℝ) ^ E_6 := by
          rw [pow_succ']
          ring
  set P₀ : ℕ := max (max 1 P_13) P_6
  set B_unit : ℝ := F_base ^ (C_6 + 1) * (2 : ℝ) ^ (P₀ * d) * (L : ℝ) ^ E
  have hF_pow_ge : (1 : ℝ) ≤ F_base ^ (C_6 + 1) := one_le_pow₀ hF1
  have hF_le_pow : F_base ≤ F_base ^ (C_6 + 1) :=
    le_self_pow₀ hF1 (Nat.succ_ne_zero C_6)
  have h2P₀_ge : (1 : ℝ) ≤ (2 : ℝ) ^ (P₀ * d) := one_le_pow₀ (by norm_num)
  have hLE_ge : (1 : ℝ) ≤ (L : ℝ) ^ E := one_le_pow₀ hLR
  have h1_le_B : (1 : ℝ) ≤ B_unit :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hF_pow_ge h2P₀_ge) hLE_ge
  have ht1 : (N_cand : ℝ) ≤ B_unit := by
    calc (N_cand : ℝ) ≤ F_base * 1 * 1 := by linarith [hNcand_le]
      _ ≤ F_base ^ (C_6 + 1) * (2 : ℝ) ^ (P₀ * d) * (L : ℝ) ^ E :=
          mul_le_mul (mul_le_mul hF_le_pow h2P₀_ge (by positivity) (by positivity)) hLE_ge
            (by positivity) (by positivity)
  have ht2 : (L : ℝ) ≤ B_unit := by
    have hL_le : (L : ℝ) ≤ (L : ℝ) ^ E :=
      le_self_pow₀ hLR (ne_of_gt (lt_of_lt_of_le (by decide : 0 < 1)
        (le_trans (le_max_left _ _) (le_max_left _ _))))
    calc (L : ℝ) = 1 * 1 * (L : ℝ) := by ring
      _ ≤ F_base ^ (C_6 + 1) * (2 : ℝ) ^ (P₀ * d) * (L : ℝ) ^ E :=
          mul_le_mul (mul_le_mul hF_pow_ge h2P₀_ge (by positivity) (by positivity)) hL_le
            (by positivity) (by positivity)
  have ht3 : (2 ^ d : ℝ) ≤ B_unit := by
    have h2d_le : (2 : ℝ) ^ d ≤ (2 : ℝ) ^ (P₀ * d) :=
      pow_le_pow_right₀ (by norm_num)
        (Nat.le_mul_of_pos_left d (lt_of_lt_of_le (by decide : 0 < 1)
          (le_trans (le_max_left _ _) (le_max_left _ _))))
    calc (2 ^ d : ℝ) = 1 * (2 : ℝ) ^ d * 1 := by ring
      _ ≤ F_base ^ (C_6 + 1) * (2 : ℝ) ^ (P₀ * d) * (L : ℝ) ^ E :=
          mul_le_mul (mul_le_mul hF_pow_ge h2d_le (by positivity) (by positivity)) hLE_ge
            (by positivity) (by positivity)
  have ht4 : fptBound C_13 τ d L13_max ≤ B_unit := by
    have h2P13 : (2 : ℝ) ^ (P_13 * d) ≤ (2 : ℝ) ^ (P₀ * d) :=
      pow_le_pow_right₀ (by norm_num)
        (Nat.mul_le_mul_right d (le_trans (le_max_right _ _) (le_max_left _ _)))
    have hLE13 : (L : ℝ) ^ E_13 ≤ (L : ℝ) ^ E :=
      pow_le_pow_right₀ hLR (le_trans (le_max_right _ _) (le_max_left _ _))
    exact hfpt13.trans (mul_le_mul (mul_le_mul hF_le_pow h2P13 (by positivity) (by positivity))
      hLE13 (by positivity) (by positivity))
  have ht5 : oracleBound C_6 d L6_max ≤ B_unit := by
    have h2P6 : (2 : ℝ) ^ (P_6 * d) ≤ (2 : ℝ) ^ (P₀ * d) :=
      pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right d (le_max_right _ _))
    have hLE6 : (L : ℝ) ^ E_6 ≤ (L : ℝ) ^ E := pow_le_pow_right₀ hLR (le_max_right _ _)
    exact horacle6.trans (mul_le_mul (mul_le_mul_of_nonneg_left h2P6 (by positivity))
      hLE6 (by positivity) (by positivity))
  have ht6 : (2 : ℝ) ≤ 2 * B_unit := by linarith
  have hBase : (N_cand : ℝ) + (L : ℝ) + (2 ^ d : ℝ) + fptBound C_13 τ d L13_max +
      oracleBound C_6 d L6_max + 2 ≤ 8 * B_unit := by
    linarith
  have h8B : 8 * B_unit ≤ F_base ^ (C_6 + 1) * (2 : ℝ) ^ (P * d) * (L : ℝ) ^ E := by
    have h3d : P₀ * d + 3 ≤ P * d := by
      have : 3 ≤ 3 * d := by omega
      calc P₀ * d + 3 ≤ P₀ * d + 3 * d := Nat.add_le_add_left this _
        _ = P * d := by ring
    calc 8 * B_unit = F_base ^ (C_6 + 1) * ((2 : ℝ) ^ (P₀ * d) * (2 : ℝ) ^ 3) * (L : ℝ) ^ E := by
          change 8 * (F_base ^ (C_6 + 1) * (2 : ℝ) ^ (P₀ * d) * (L : ℝ) ^ E) = _
          ring
      _ = F_base ^ (C_6 + 1) * (2 : ℝ) ^ (P₀ * d + 3) * (L : ℝ) ^ E := by rw [← pow_add]
      _ ≤ F_base ^ (C_6 + 1) * (2 : ℝ) ^ (P * d) * (L : ℝ) ^ E := by
          gcongr
          norm_num
  have hLHS0 : 0 ≤ (N_cand : ℝ) + (L : ℝ) + (2 ^ d : ℝ) + fptBound C_13 τ d L13_max +
      oracleBound C_6 d L6_max + 2 := by
    have h1 := fptBound_nonneg C_13 τ d L13_max
    have h2 := oracleBound_nonneg C_6 d L6_max
    positivity
  have hPow : ((N_cand : ℝ) + (L : ℝ) + (2 ^ d : ℝ) + fptBound C_13 τ d L13_max +
      oracleBound C_6 d L6_max + 2) ^ C_drv ≤
      F_base ^ C_pow * (2 : ℝ) ^ (K_pow * d) * (L : ℝ) ^ (E * C_drv) := by
    calc _ ≤ (F_base ^ (C_6 + 1) * (2 : ℝ) ^ (P * d) * (L : ℝ) ^ E) ^ C_drv :=
          pow_le_pow_left₀ hLHS0 (le_trans hBase h8B) C_drv
      _ = F_base ^ C_pow * (2 : ℝ) ^ (K_pow * d) * (L : ℝ) ^ (E * C_drv) := by
          rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
          have hp : P * d * C_drv = K_pow * d := by ring
          rw [hp]
  have hExpFactor : F_base ^ C_pow * (2 : ℝ) ^ (K_pow * d) ≤
      (2 : ℝ) ^ (α * (2 : ℝ) ^ ((e : ℝ) * d)) :=
    exp_factor_bound hd1 hα1 (le_max_right _ _)
  have hLPow : (L : ℝ) ^ (E * C_drv) ≤ (L : ℝ) ^ e :=
    pow_le_pow_right₀ hLR (le_max_left _ _)
  refine le_trans hPow ?_
  unfold fptBound
  exact mul_le_mul hExpFactor hLPow (by positivity) (by positivity)

private lemma inp13_len_le {I : Instance} {R : Cand I} {L : ℕ} {γ : ℚ}
    (hd1 : 1 ≤ I.d) (hL1 : 1 ≤ L) (hτL : I.τ ≤ L)
    (hR : IsCandidate I R) (hγ : (encRat γ).length ≤ L ^ 2 + 5 * L + 4) :
    L + (encCand R).length + (encRat γ).length + 1 ≤ 2 ^ (7 * I.d) * L ^ 2 := by
  have hCand := encCand_len_le hR
  have h2d : 2 ≤ 2 ^ I.d := Nat.le_self_pow (by omega) 2
  have hd_le_2d : I.d ≤ 2 ^ I.d := Nat.le_of_lt Nat.lt_two_pow_self
  have hd1_le_2d : I.d + 1 ≤ 2 ^ I.d := d_add_one_le_two_pow I.d
  have hcand_block : I.d + 2 + 2 ^ I.d * (I.d * (I.d + 1)) ≤ 2 ^ (5 * I.d) := by
    have hmul : 2 ^ I.d * (I.d * (I.d + 1)) ≤ 2 ^ I.d * (2 ^ I.d * 2 ^ I.d) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul hd_le_2d hd1_le_2d)
    have hpow3 : 2 ^ I.d * (2 ^ I.d * 2 ^ I.d) = 2 ^ (3 * I.d) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    have h1_le_3 : 2 ^ I.d ≤ 2 ^ (3 * I.d) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have h4_le_5 : 3 * I.d + 2 ≤ 5 * I.d := by omega
    calc I.d + 2 + 2 ^ I.d * (I.d * (I.d + 1))
      _ ≤ 2 ^ I.d + 2 ^ I.d + 2 ^ (3 * I.d) := by omega
      _ ≤ 2 ^ (3 * I.d) + 2 ^ (3 * I.d) + 2 ^ (3 * I.d) := by omega
      _ ≤ 4 * 2 ^ (3 * I.d) := by omega
      _ = 2 ^ (3 * I.d + 2) := by
          rw [show (4 : ℕ) = 2 ^ 2 by decide, mul_comm, ← pow_add]
      _ ≤ 2 ^ (5 * I.d) := Nat.pow_le_pow_right (by decide) h4_le_5
  have hCand2 : (encCand R).length ≤ L ^ 2 * 2 ^ (5 * I.d) := by
    calc (encCand R).length
      _ ≤ I.τ * (I.d + 2 + 2 ^ I.d * (I.d * (I.d + 1))) := hCand
      _ ≤ I.τ * 2 ^ (5 * I.d) := Nat.mul_le_mul_left _ hcand_block
      _ ≤ L * 2 ^ (5 * I.d) := Nat.mul_le_mul_right _ hτL
      _ ≤ L ^ 2 * 2 ^ (5 * I.d) :=
          Nat.mul_le_mul_right _ (by nlinarith : L ≤ L ^ 2)
  have h12_le : 12 ≤ 2 ^ (5 * I.d) := by
    have h1 : 12 ≤ 2 ^ 4 := by decide
    exact le_trans h1 (Nat.pow_le_pow_right (by decide) (by omega))
  have h12_add : 12 + 2 ^ (5 * I.d) ≤ 2 ^ (7 * I.d) := by
    calc 12 + 2 ^ (5 * I.d) ≤ 2 ^ (5 * I.d) + 2 ^ (5 * I.d) := Nat.add_le_add_right h12_le _
      _ = 2 ^ (5 * I.d + 1) := by rw [pow_succ']; omega
      _ ≤ 2 ^ (7 * I.d) := Nat.pow_le_pow_right (by decide) (by omega)
  have hx_le : L ≤ L ^ 2 := by nlinarith
  have h1_le : 1 ≤ L ^ 2 := by nlinarith
  have hγ_le : L ^ 2 + 5 * L + 4 ≤ 10 * L ^ 2 := by nlinarith
  calc L + (encCand R).length + (encRat γ).length + 1
    _ ≤ L ^ 2 + L ^ 2 * 2 ^ (5 * I.d) + 10 * L ^ 2 + 1 := by omega
    _ ≤ (12 + 2 ^ (5 * I.d)) * L ^ 2 := by nlinarith
    _ ≤ 2 ^ (7 * I.d) * L ^ 2 := Nat.mul_le_mul_right _ h12_add

end IntConeFPT.CountedThresholdSearch

open IntConeFPT.CountedThresholdSearch

set_option maxHeartbeats 1200000 in
theorem solution :
    ∃ e : ℕ, ∃ A : Machine, ∀ I : Instance, I.Valid → ∀ N : ℕ,
      let x := encInstance I ++ encNat N ++ [3]
      let B := 2^(x.length^2 + 4*x.length)
      let q := ∏ t, ∏ j, (I.coeff t j).den
      ∀ k : ℕ, k ≤ 2*B → ∃ o : Output I,
        (match o with
         | .unbounded => False
         | .infeasible => ¬ ∃ μ, I.FeasibleN N μ ∧ (q : ℝ)*I.cost μ ≤ (k:ℝ)-B
         | .optimal y v cert => CertOK I cert ∧ I.FeasibleN N (certMult I cert) ∧
             I.totalAgg (certMult I cert) = ((fun i => (y i : ℝ)), fun i => (v i : ℝ)) ∧
             (q:ℝ)*I.cost (certMult I cert) ≤ (k:ℝ)-B) ∧
        RunsWithin A (x ++ encNat k ++ [3]) (encOutput o) (fptBound e I.τ I.d x.length) := by
  classical
  obtain ⟨C_13, M_13, h13⟩ := IntConeFPT.lemma_13
  obtain ⟨C_6, M_6, h6⟩ := IntConeFPT.lemma_6
  obtain ⟨C_drv, W, hW⟩ := IntConeFPT.counted_threshold_driver M_13 M_6
  obtain ⟨e, he⟩ := fptBound_threshold_absorb C_13 C_6 C_drv M_13.tm.growth
  refine ⟨e, W, ?_⟩
  intro I hI N x B q k hk
  obtain ⟨hq0, hqB, _⟩ := IntConeFPT.counted_grid I hI N
  have hq0R : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq0
  have hq0Q : (0 : ℚ) < (q : ℚ) := Nat.cast_pos.mpr hq0
  obtain ⟨_, _, _, _, _, _, hIlen1, hdI, _, hτI, _⟩ := IntConeFPT.section_3_6_nstar_bound I hI 1 le_rfl
  have hI_le_x : (encInstance I).length ≤ x.length := by
    simp [x]
  have hL1 : 1 ≤ x.length := le_trans hIlen1 hI_le_x
  have hdL : I.d ≤ x.length := le_trans hdI hI_le_x
  have hτL : I.τ ≤ x.length := le_trans hτI hI_le_x
  let γ : ℚ := ((k : ℤ) - (B : ℤ)) / (q : ℚ)
  let L13_max : ℕ := 2 ^ (7 * I.d) * x.length ^ 2
  let T_13 : ℝ := fptBound C_13 I.τ I.d L13_max
  have hT_13_nonneg : 0 ≤ T_13 := fptBound_nonneg C_13 I.τ I.d L13_max
  have hγ_len : (encRat γ).length ≤ x.length ^ 2 + 5 * x.length + 4 := by
    let numZ : ℤ := (k : ℤ) - (B : ℤ)
    have hγ_eq : γ = (numZ : ℚ) / (q : ℚ) := by
      dsimp only [γ, numZ]
      push_cast
      rfl
    have hnum : numZ.natAbs ≤ 2 ^ (x.length ^ 2 + 4 * x.length) := by
      change numZ.natAbs ≤ B
      omega
    rw [hγ_eq]
    exact encRat_div_len_le hq0 hqB hnum
  have hinp13_len : ∀ R : Cand I, IsCandidate I R →
      (x ++ encCand R ++ encRat γ ++ [3]).length ≤ L13_max := fun R hR => by
    simp only [List.length_append, List.length_singleton]
    exact inp13_len_le hI.one_le_d hL1 hτL hR hγ_len
  have h13_prop : ∀ R : Cand I,
      ∃ oR : Option ((t : Fin I.τ) → Fin (R t).length → (Fin I.d → ℤ) × (Fin I.k → ℚ) × ℕ),
        CanonCand I R →
          (oR = none ↔ ¬ ∃ zn ∈ Khat I R N γ, IsIntegral zn) ∧
          (∀ s, oR = some s →
            (fun t i => ((fun j => ((s t i).1 j : ℝ)), (fun j => ((s t i).2.1 j : ℝ)),
              ((s t i).2.2 : ℝ))) ∈ K I R N γ) ∧
          RunsWithin M_13 (x ++ encCand R ++ encRat γ ++ [3]) (encLift (R := R) oR) T_13 := by
    intro R
    by_cases hR : CanonCand I R
    · have hCand := canonCand_isCandidate hR
      obtain ⟨oR, hoNone, hoSome, hoRun⟩ := h13 I hI N R hCand γ
      refine ⟨oR, fun _ => ⟨hoNone, hoSome, ?_⟩⟩
      have hlen : (encInstance I ++ encNat N ++ [3] ++ encCand R ++ encRat γ ++ [3]).length ≤ L13_max := by
        simpa only [x, List.append_assoc] using hinp13_len R hCand
      obtain ⟨m, hm, hr⟩ := hoRun
      refine ⟨m, hm.trans (fptBound_mono_L hlen), ?_⟩
      simpa only [x, List.append_assoc] using hr
    · exact ⟨none, fun h => absurd h hR⟩
  choose o ho_spec using h13_prop
  let L6_max : ℕ := 5 * x.length ^ 2 + L13_max + Nat.ceil T_13 * M_13.tm.growth
  let T_6 : ℝ := oracleBound C_6 I.d L6_max
  have hT_6_nonneg : 0 ≤ T_6 := oracleBound_nonneg C_6 I.d L6_max
  have h6_prop : ∀ (R : Cand I)
      (s : (t : Fin I.τ) → Fin (R t).length → (Fin I.d → ℤ) × (Fin I.k → ℚ) × ℕ)
      (t : Fin I.τ) (i : Fin (R t).length),
      ∃ lout : List ((Fin I.d → ℤ) × (Fin I.k → ℚ) × ℕ),
        (CanonCand I R → o R = some s →
          lout.length ≤ 2 ^ (I.d + 1) - 1 ∧
          (lout.map fun e => (e.1, e.2.1)).Nodup ∧
          (∀ e ∈ lout, 1 ≤ e.2.2 ∧ (certGen e).toReal ∈ I.Pr t ((R t).get i) ∧ certGen e ∈ I.S t) ∧
          (lout.map fun e => (e.2.2 : ℝ) • (certGen e).toReal).sum =
            ((fun j => ((s t i).1 j : ℝ)), fun j => ((s t i).2.1 j : ℝ)) ∧
          (lout.map fun e => e.2.2).sum = (s t i).2.2 ∧
          (((lout.map fun e => (e.2.2 : ℝ) * I.f t (fun j => (e.1 j : ℝ))).sum : ℝ) : EReal) ≤
            I.Phi t ((R t).get i)
              ((fun j => ((s t i).1 j : ℝ)), (fun j => ((s t i).2.1 j : ℝ)), ((s t i).2.2 : ℝ)) ∧
          RunsWithin M_6
            (encLocal I t ((R t).get i) ++ encIntVec (s t i).1 ++ encVec (s t i).2.1 ++
              encNat (s t i).2.2 ++ [3])
            (encCert lout) T_6) := by
    intro R s t i
    by_cases hcond : CanonCand I R ∧ o R = some s
    · rcases hcond with ⟨hR, hs⟩
      have hK := (ho_spec R hR).2.1 s hs
      have hCr : ((fun j => ((s t i).1 j : ℝ)), (fun j => ((s t i).2.1 j : ℝ)),
          ((s t i).2.2 : ℝ)) ∈ I.Cr t ((R t).get i) := hK.2.1 t i
      obtain ⟨lout, hl1, hl2, hl3, hl4, hl5, hl6, hlRun⟩ :=
        h6 I hI t ((R t).get i) (s t i).1 (s t i).2.1 (s t i).2.2 hCr
      have hRun13 := (ho_spec R hR).2.2
      rw [hs] at hRun13
      have hout13 := runsWithin_output_length_le hRun13
      have hinp13 : ((x ++ encCand R ++ encRat γ ++ [3]).length : ℝ) ≤ (L13_max : ℝ) :=
        Nat.cast_le.mpr (hinp13_len R (canonCand_isCandidate hR))
      have hT13_ceil : T_13 ≤ (Nat.ceil T_13 : ℝ) := Nat.le_ceil T_13
      have hout13_nat : (encLift (R := R) (some s)).length ≤ L13_max + Nat.ceil T_13 * M_13.tm.growth := by
        have hRbound : ((encLift (R := R) (some s)).length : ℝ) ≤
            ((L13_max + Nat.ceil T_13 * M_13.tm.growth : ℕ) : ℝ) := by
          push_cast
          calc ((encLift (R := R) (some s)).length : ℝ)
            _ ≤ ((x ++ encCand R ++ encRat γ ++ [3]).length : ℝ) + T_13 * (M_13.tm.growth : ℝ) := hout13
            _ ≤ (L13_max : ℝ) + (Nat.ceil T_13 : ℝ) * (M_13.tm.growth : ℝ) :=
                add_le_add hinp13 (mul_le_mul_of_nonneg_right hT13_ceil (Nat.cast_nonneg _))
        exact Nat.cast_le.mp hRbound
      have hblock_len := le_trans (encLift_block_len_le s t i) hout13_nat
      have hloc_len := encLocal_len_le (t := t) (r := (R t).get i) hI_le_x hτL hdL hL1
      have hinp6_len :
          (encLocal I t ((R t).get i) ++ encIntVec (s t i).1 ++ encVec (s t i).2.1 ++
            encNat (s t i).2.2 ++ [3]).length ≤ L6_max := by
        simp only [List.length_append, List.length_singleton] at hblock_len ⊢
        omega
      refine ⟨lout, fun _ _ => ⟨hl1, hl2, hl3, hl4, hl5, hl6, ?_⟩⟩
      obtain ⟨m, hm, hr⟩ := hlRun
      exact ⟨m, hm.trans (oracleBound_mono_L hinp6_len), hr⟩
    · exact ⟨[], fun hR hs => absurd ⟨hR, hs⟩ hcond⟩
  choose out hout_spec using h6_prop
  have hdrv := hW I hI N k hk o out T_13 T_6 hT_13_nonneg hT_6_nonneg
    (fun R hR => (ho_spec R hR).2.2)
    (fun R hR s hs t i =>
      ⟨fun e he => ((hout_spec R s t i hR hs).2.2.1 e he).1,
       (hout_spec R s t i hR hs).2.2.2.2.2.2⟩)
  let N_cand : ℕ :=
    ((Finset.univ : Finset (Fin I.τ → Finset (Residue I.d))).filter
      (fun R => ∀ t, (R t).card ≤ 2 ^ I.d)).card
  have hNcand_bound : N_cand ≤ 2 ^ (I.τ * (I.d + 1 + I.d ^ 2 * 2 ^ I.d)) :=
    IntConeFPT.corollary_8 I.d I.τ hI.one_le_d
  have hL6_bound : (L6_max : ℝ) ≤
      5 * (x.length : ℝ) ^ 2 + (L13_max : ℝ) + (T_13 + 1) * (M_13.tm.growth : ℝ) := by
    have hceil : (Nat.ceil T_13 : ℝ) ≤ T_13 + 1 := (Nat.ceil_lt_add_one hT_13_nonneg).le
    push_cast [L6_max]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hceil (Nat.cast_nonneg _))
  have hFPT : ((N_cand : ℝ) + (x.length : ℝ) + (2 ^ I.d : ℝ) + T_13 + T_6 + 2) ^ C_drv ≤
      fptBound e I.τ I.d x.length :=
    he hI.one_le_d hI.one_le_τ hL1 hNcand_bound le_rfl hL6_bound
  rcases hdrv with ⟨hAllNone, hRunInf⟩ | ⟨R, s, cert, hR, hs, hcert_spec, hRunOpt⟩
  · refine ⟨.infeasible, ?_, ?_⟩
    · intro ⟨μ, hμ_feas, hμ_cost⟩
      have hcost_le : I.cost μ ≤ (γ : ℝ) := by
        have hγR : (γ : ℝ) = ((k : ℝ) - (B : ℝ)) / (q : ℝ) := by
          dsimp only [γ]
          push_cast
          rfl
        rw [hγR]
        exact (le_div_iff₀' hq0R).mpr hμ_cost
      have hcor10 := (IntConeFPT.corollary_10 I hI N γ).mp ⟨μ, hμ_feas, hcost_le⟩
      obtain ⟨R₀, hR₀_cand, hex₀⟩ := hcor10
      obtain ⟨R', hR'_canon, hR'_perm⟩ := exists_canonCand_perm I R₀ hR₀_cand
      have hex' := khat_integral_of_perm hR'_perm hex₀
      exact ((ho_spec R' hR'_canon).1.mp (hAllNone R' hR'_canon)) hex'
    · obtain ⟨m, hm, hr⟩ := hRunInf
      exact ⟨m, hm.trans hFPT, hr⟩
  · let y : Fin I.d → ℚ :=
      fun j => ∑ t : Fin I.τ, ∑ i : Fin (R t).length, ((s t i).1 j : ℚ)
    let v : Fin I.k → ℚ :=
      fun j => ∑ t : Fin I.τ, ∑ i : Fin (R t).length, (s t i).2.1 j
    have hK : (fun t i => ((fun j => ((s t i).1 j : ℝ)), (fun j => ((s t i).2.1 j : ℝ)),
        ((s t i).2.2 : ℝ))) ∈ K I R N γ := (ho_spec R hR).2.1 s hs
    let ξ : Blocks I R := fun t i =>
      ((fun j => ((s t i).1 j : ℝ)), (fun j => ((s t i).2.1 j : ℝ)), ((s t i).2.2 : ℝ))
    have hcert_aggr : ∀ t, aggr (certMult I cert t) = blockAgg ξ t := fun t => by
      have hmult := (hcert_spec t).2.2.2
      rw [hmult, aggr_finset_sum]
      unfold blockAgg
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [aggr_certList]
      exact (hout_spec R s t i hR hs).2.2.2.1
    have hcert_count : ∀ t, count (certMult I cert t) = ∑ i : Fin (R t).length, (s t i).2.2 := fun t => by
      have hmult := (hcert_spec t).2.2.2
      rw [hmult, count_finset_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [count_certList]
      exact (hout_spec R s t i hR hs).2.2.2.2.1
    have hcert_countR : ∀ t, (count (certMult I cert t) : ℝ) = blockCount ξ t := fun t => by
      rw [hcert_count t]
      unfold blockCount ξ
      push_cast
      rfl
    have hCertOK : CertOK I cert := fun t => by
      rcases hcert_spec t with ⟨hlen, hnodup, hmem, _⟩
      refine ⟨?_, hnodup, ?_⟩
      · calc (cert t).length
          _ ≤ ∑ i : Fin (R t).length, (out R s t i).length := hlen
          _ ≤ ∑ _ : Fin (R t).length, (2 ^ (I.d + 1) - 1) :=
              Finset.sum_le_sum fun i _ => (hout_spec R s t i hR hs).1
          _ = (R t).length * (2 ^ (I.d + 1) - 1) := by simp
          _ ≤ 2 ^ I.d * 2 ^ (I.d + 1) :=
              Nat.mul_le_mul (hR t).1 (Nat.sub_le _ 1)
          _ = 2 ^ (2 * I.d + 1) := by
              rw [← pow_add]
              congr 1
              omega
      · intro c hc
        rcases hmem c hc with ⟨hc_pos, i, e', he'_mem, he'_eq⟩
        refine ⟨hc_pos, ?_⟩
        have hS : certGen e' ∈ I.S t := ((hout_spec R s t i hR hs).2.2.1 e' he'_mem).2.2
        have hgen_eq : certGen c = certGen e' := by
          unfold certGen
          rcases Prod.mk.inj he'_eq with ⟨h1, h2⟩
          rw [← h1, ← h2]
        rw [hgen_eq]
        exact hS
    have hSupp : I.Supported (certMult I cert) := fun t g hg => by
      unfold certMult at hg
      obtain ⟨c, hc, rfl⟩ := mem_support_certList (cert t) hg
      exact (hCertOK t).2.2 c hc |>.2
    have htotAgg_eq : I.totalAgg (certMult I cert) = ∑ t, blockAgg ξ t := by
      unfold Instance.totalAgg
      exact Finset.sum_congr rfl fun t _ => hcert_aggr t
    have htypeAgg_eq : (fun t => I.typeAgg (certMult I cert) t) =
        (fun t => ((blockAgg ξ t).1, (blockAgg ξ t).2, blockCount ξ t)) := by
      ext t <;> simp [Instance.typeAgg, hcert_aggr t, hcert_countR t]
    have htotCount_eq : (I.totalCount (certMult I cert) : ℝ) = ∑ t, blockCount ξ t := by
      unfold Instance.totalCount
      push_cast
      exact Finset.sum_congr rfl fun t _ => hcert_countR t
    have hFeasN : I.FeasibleN N (certMult I cert) := by
      refine ⟨⟨hSupp, ?_, ?_⟩, ?_⟩
      · rw [htotAgg_eq]
        exact hK.1
      · rw [htypeAgg_eq]
        exact hK.2.2.1
      · rw [← Nat.cast_le (α := ℝ), htotCount_eq]
        exact hK.2.2.2.1
    have hAgg_yv : I.totalAgg (certMult I cert) = ((fun j => (y j : ℝ)), fun j => (v j : ℝ)) := by
      rw [htotAgg_eq]
      unfold blockAgg ξ y v
      ext j
      · simp [Prod.fst_sum, Finset.sum_apply, Rat.cast_sum]
      · simp [Prod.snd_sum, Finset.sum_apply, Rat.cast_sum]
    have hcost_le_γ : ((I.cost (certMult I cert) : ℝ) : EReal) ≤ ((γ : ℝ) : EReal) := by
      have hcost_blocks : I.cost (certMult I cert) =
          ∑ t : Fin I.τ, ∑ i : Fin (R t).length,
            ((out R s t i).map fun e => (e.2.2 : ℝ) * I.f t (fun j => (e.1 j : ℝ))).sum := by
        unfold Instance.cost
        refine Finset.sum_congr rfl fun t _ => ?_
        have hmult := (hcert_spec t).2.2.2
        rw [hmult, costOf_finset_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [costOf_certList]
      rw [hcost_blocks, coe_finset_sum_ereal]
      refine le_trans (finset_sum_le_sum_ereal Finset.univ _ _ fun t _ => ?_) hK.2.2.2.2
      rw [coe_finset_sum_ereal]
      exact finset_sum_le_sum_ereal Finset.univ _ _ fun i _ =>
        (hout_spec R s t i hR hs).2.2.2.2.2.1
    have hcost_real : (q : ℝ) * I.cost (certMult I cert) ≤ (k : ℝ) - (B : ℝ) := by
      have hle : I.cost (certMult I cert) ≤ (γ : ℝ) := EReal.coe_le_coe_iff.mp hcost_le_γ
      have hγR : (γ : ℝ) = ((k : ℝ) - (B : ℝ)) / (q : ℝ) := by
        dsimp only [γ]
        push_cast
        rfl
      rw [hγR] at hle
      exact (le_div_iff₀' hq0R).mp hle
    refine ⟨.optimal y v cert, ⟨hCertOK, hFeasN, hAgg_yv, hcost_real⟩, ?_⟩
    obtain ⟨m, hm, hr⟩ := hRunOpt
    exact ⟨m, hm.trans hFPT, hr⟩
