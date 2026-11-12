-- Prove2me | solution 1 for HindsightGain.Uniform.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T01:53:16.85975+00:00
-- url     : https://prove2.me/submissions/0e2018ac-103e-4107-b278-c134c470cb2a

import Mathlib
import Definitions.Def_HindsightGain_Uniform_tensors

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HindsightGain.Uniform.Dev.Lem31
open HindsightGain.Uniform

variable {ι : Type} [Fintype ι]

/-- The r-linear form with slot vectors `V`. -/
def Tf {r : ℕ} (C : Tensor ι r) (V : Fin r → EuclideanSpace ℝ ι) : ℝ :=
  ∑ b : Fin r → ι, C b * ∏ l, V l (b l)

lemma Tf_perm {r : ℕ} (C : Tensor ι r) (hC : symmetric C) (V : Fin r → EuclideanSpace ℝ ι)
    (σ : Equiv.Perm (Fin r)) : Tf C (V ∘ σ) = Tf C V := by
  unfold Tf
  let e : (Fin r → ι) ≃ (Fin r → ι) := Equiv.arrowCongr σ (Equiv.refl ι)
  refine Fintype.sum_equiv e _ _ fun b => ?_
  have h1 : C (e b) = C b := by
    have := hC σ.symm b
    simpa [e, Equiv.arrowCongr] using this.symm ▸ rfl
  rw [h1]
  congr 1
  rw [← Equiv.prod_comp σ (fun l => V l ((e b) l))]
  refine Finset.prod_congr rfl fun l _ => ?_
  show (V (σ l)) (b l) = (V (σ l)) (b (σ.symm (σ l)))
  simp

lemma prod_update_slot {r : ℕ} (V : Fin r → EuclideanSpace ℝ ι) (l : Fin r)
    (v : EuclideanSpace ℝ ι) (b : Fin r → ι) :
    ∏ m, (Function.update V l v m) (b m) =
      v (b l) * ∏ m ∈ Finset.univ.erase l, V m (b m) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun m hm => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hm)]

lemma Tf_update_sub {r : ℕ} (C : Tensor ι r) (V : Fin r → EuclideanSpace ℝ ι) (l : Fin r)
    (u w : EuclideanSpace ℝ ι) :
    Tf C (Function.update V l (u - w)) =
      Tf C (Function.update V l u) - Tf C (Function.update V l w) := by
  unfold Tf
  simp only [prod_update_slot, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [PiLp.sub_apply]; ring

lemma Tf_zero_slot {r : ℕ} (C : Tensor ι r) (V : Fin r → EuclideanSpace ℝ ι) (l : Fin r)
    (h : V l = 0) : Tf C V = 0 := by
  unfold Tf
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [Finset.prod_eq_zero (Finset.mem_univ l) (by simp [h]), mul_zero]

lemma Tf_hasDerivAt {r : ℕ} (C : Tensor ι r) (c d : Fin r → EuclideanSpace ℝ ι) :
    HasDerivAt (fun ε : ℝ => Tf C (fun l => c l + ε • d l))
      (∑ l, Tf C (Function.update c l (d l))) 0 := by
  classical
  unfold Tf
  have hb : ∀ b : Fin r → ι, HasDerivAt
      (fun ε : ℝ => C b * ∏ l, (c l + ε • d l) (b l))
      (C b * ∑ l, (∏ m ∈ Finset.univ.erase l, c m (b m)) * d l (b l)) 0 := by
    intro b
    have h1 : ∀ l ∈ (Finset.univ : Finset (Fin r)),
        HasDerivAt (fun ε : ℝ => (c l + ε • d l) (b l)) (d l (b l)) 0 := by
      intro l _
      have : HasDerivAt (fun ε : ℝ => c l (b l) + ε * d l (b l)) (d l (b l)) 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).mul_const (d l (b l))).const_add (c l (b l))
      simpa using this
    have h2 := HasDerivAt.finset_prod (u := Finset.univ) h1
    have h3 := h2.const_mul (C b)
    have e1 : (fun ε : ℝ => C b * ∏ l, (c l + ε • d l) (b l)) =
        fun y => C b * (∏ i, fun ε : ℝ => (c i + ε • d i) (b i)) y := by
      funext ε; simp [Finset.prod_apply]
    rw [e1]
    refine h3.congr_deriv ?_
    simp
  have := HasDerivAt.fun_sum (u := Finset.univ) (fun b _ => hb b)
  refine HasDerivAt.congr_deriv this ?_
  simp only [prod_update_slot, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- Slots below `k` hold `y`, the others hold `z`. -/
def Pk {r : ℕ} (y z : EuclideanSpace ℝ ι) (k : ℕ) : Fin r → EuclideanSpace ℝ ι :=
  fun l => if l.val < k then y else z

/-- Slot 0 holds `h`, slots `1..k` hold `y`, the rest hold `z`. -/
def Hpat {s : ℕ} (y z h : EuclideanSpace ℝ ι) (k : ℕ) : Fin (s + 1) → EuclideanSpace ℝ ι :=
  fun q => if q.val = 0 then h else if q.val ≤ k then y else z

lemma perm_pattern {s : ℕ} (C : Tensor ι (s + 1)) (hC : symmetric C)
    (y z h : EuclideanSpace ℝ ι) (k : ℕ) (l : Fin (s + 1)) (hkl : k ≤ l.val) :
    Tf C (Function.update (Pk y z k) l h) = Tf C (Hpat y z h k) := by
  rw [← Tf_perm C hC (Hpat y z h k) (Fin.cycleRange l)]
  congr 1
  funext q
  show _ = Hpat y z h k (l.cycleRange q)
  rcases lt_trichotomy q l with hq | hq | hq
  · rw [Fin.cycleRange_of_lt hq]
    have hlast : q < Fin.last s := lt_of_lt_of_le hq (Fin.le_last l)
    have hv : ((q + 1 : Fin (s + 1)) : ℕ) = q.val + 1 := Fin.val_add_one_of_lt hlast
    have hql : q ≠ l := hq.ne
    simp only [Hpat, Pk, Function.update_of_ne hql, hv]
    have : ¬ (q.val + 1 = 0) := by omega
    simp only [this, if_false]
    have : (q.val + 1 ≤ k) ↔ (q.val < k) := by omega
    simp only [this]
  · subst hq
    simp [Hpat, Fin.cycleRange_self]
  · rw [Fin.cycleRange_of_gt hq]
    have hql : q ≠ l := hq.ne'
    have hlq : l.val < q.val := hq
    simp only [Hpat, Pk, Function.update_of_ne hql]
    have h1 : ¬ (q.val = 0) := by omega
    have h2 : ¬ (q.val ≤ k) := by omega
    have h3 : ¬ (q.val < k) := by omega
    simp [h1, h2, h3]

lemma sum_split {s : ℕ} (F : (Fin (s + 1) → ι) → ℝ) :
    ∑ b, F b = ∑ i : ι, ∑ a : Fin s → ι, F (Fin.cons i a) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (s + 1) => ι)) F, Fintype.sum_prod_type]
  rfl

lemma prepend_eq_cons {s : ℕ} (i : ι) (a : Fin (s + 1 - 1) → ι) :
    prepend (r := s + 1) i a = Fin.cons i (a : Fin s → ι) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [prepend]
  · simp [prepend]

lemma inner_LW {s : ℕ} (C : Tensor ι (s + 1)) (y z h : EuclideanSpace ℝ ι) :
    inner ℝ h (tensorL C (comparisonTensor (s + 1) y z)) =
      ∑ k : Fin (s + 1), Tf C (Hpat y z h k.val) := by
  simp only [PiLp.inner_apply, tensorL, comparisonTensor, mixedTensor]
  simp only [WithLp.ofLp_sum, WithLp.ofLp_toLp, Finset.sum_apply, Finset.mul_sum]
  unfold Tf
  simp only [Finset.mul_sum, sum_split (s := s)]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm, RCLike.inner_apply, conj_trivial, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.prod_univ_succ]
  simp only [Hpat, Fin.cons_zero, Fin.cons_succ, prepend_eq_cons]
  simp only [Fin.val_zero, if_true, Fin.val_succ, Nat.succ_ne_zero, if_false]
  have : ∀ j : Fin s, ((j.val + 1 ≤ k.val) ↔ (j.val < k.val)) := fun j => by omega
  simp only [this]
  have e : ∀ j : Fin s, (if j.val < k.val then y else z).ofLp (a j) =
      if j.val < k.val then y.ofLp (a j) else z.ofLp (a j) := fun j => by split_ifs <;> rfl
  simp only [e]
  exact (mul_right_comm (C.ofLp (Fin.cons x a)) _ (h.ofLp x)).trans (mul_assoc _ _ _)

/-- The auxiliary polynomial Φ_y. -/
def Phi {s : ℕ} (C : Tensor ι (s + 1)) (y u : EuclideanSpace ℝ ι) : ℝ :=
  ∑ k : Fin (s + 1), (1 / (((s + 1 : ℕ) : ℝ) - k.val)) * Tf C (Pk y u k.val)

lemma Phi_hasDerivAt {s : ℕ} (C : Tensor ι (s + 1)) (hC : symmetric C)
    (y z h : EuclideanSpace ℝ ι) :
    HasDerivAt (fun ε : ℝ => Phi C y (z + ε • h))
      (inner ℝ h (tensorL C (comparisonTensor (s + 1) y z))) 0 := by
  classical
  rw [inner_LW]
  unfold Phi
  have hk : ∀ k : Fin (s + 1), HasDerivAt
      (fun ε : ℝ => (1 / (((s + 1 : ℕ) : ℝ) - k.val)) * Tf C (Pk y (z + ε • h) k.val))
      (Tf C (Hpat y z h k.val)) 0 := by
    intro k
    have hd := Tf_hasDerivAt C (Pk y z k.val)
      (fun l : Fin (s + 1) => if l.val < k.val then (0 : EuclideanSpace ℝ ι) else h)
    have hfun : ∀ ε : ℝ, Tf C (Pk y (z + ε • h) k.val) =
        Tf C (fun l => Pk y z k.val l +
          ε • (if l.val < k.val then (0 : EuclideanSpace ℝ ι) else h)) := by
      intro ε
      congr 1
      funext l
      by_cases hl : l.val < k.val <;> simp [Pk, hl]
    simp only [hfun]
    have hsum : ∑ l : Fin (s + 1), Tf C (Function.update (Pk y z k.val) l
        (if l.val < k.val then (0 : EuclideanSpace ℝ ι) else h)) =
        (((s + 1 : ℕ) : ℝ) - k.val) * Tf C (Hpat y z h k.val) := by
      have h1 : ∀ l : Fin (s + 1), Tf C (Function.update (Pk y z k.val) l
          (if l.val < k.val then (0 : EuclideanSpace ℝ ι) else h)) =
          if k.val ≤ l.val then Tf C (Hpat y z h k.val) else 0 := by
        intro l
        by_cases hl : l.val < k.val
        · rw [if_pos hl, if_neg (by omega)]
          exact Tf_zero_slot C _ l (by simp)
        · rw [if_neg hl, if_pos (by omega)]
          exact perm_pattern C hC y z h k.val l (by omega)
      simp only [h1]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have : (Finset.univ.filter (fun l : Fin (s + 1) => k.val ≤ l.val)) = Finset.Ici k := by
        refine Finset.ext fun l => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici, Fin.le_def]
      rw [this, Fin.card_Ici]
      have hk' : k.val ≤ s + 1 := k.isLt.le
      rw [Nat.cast_sub hk']
    have hne : (((s + 1 : ℕ) : ℝ) - k.val) ≠ 0 := by
      have : (k.val : ℝ) < ((s + 1 : ℕ) : ℝ) := by exact_mod_cast k.isLt
      linarith
    refine (hd.const_mul (1 / (((s + 1 : ℕ) : ℝ) - k.val))).congr_deriv ?_
    rw [hsum]; field_simp
  have := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => hk k)
  exact this

lemma Tf_cont {r : ℕ} {X : Type} [TopologicalSpace X] (C : Tensor ι r)
    (W : Fin r → X → EuclideanSpace ℝ ι) (hW : ∀ l, Continuous (W l)) :
    Continuous fun x => Tf C (fun l => W l x) := by
  unfold Tf
  refine continuous_finset_sum _ fun b _ => ?_
  refine Continuous.mul continuous_const ?_
  refine continuous_finset_prod _ fun l _ => ?_
  exact (EuclideanSpace.proj (b l)).continuous.comp (hW l)

lemma Phi_cont {s : ℕ} (C : Tensor ι (s + 1)) (y : EuclideanSpace ℝ ι) :
    Continuous (Phi C y) := by
  unfold Phi
  refine continuous_finset_sum _ fun k _ => ?_
  refine Continuous.mul continuous_const ?_
  refine Tf_cont C (fun l u => Pk y u k.val l) fun l => ?_
  by_cases hl : l.val < k.val <;> simp [Pk, hl] <;> fun_prop

lemma diagonal_cont {r : ℕ} (C : Tensor ι r) : Continuous (diagonal C) := by
  have := Tf_cont C (fun _ x => x) (fun _ => continuous_id)
  exact this

lemma telescope {s : ℕ} (C : Tensor ι (s + 1)) (hC : symmetric C) (y z : EuclideanSpace ℝ ι) :
    diagonal C y - diagonal C z = ∑ k : Fin (s + 1), Tf C (Hpat y z (y - z) k.val) := by
  have hrange := Finset.sum_range_sub (fun k : ℕ => Tf C (Pk (r := s + 1) y z k)) (s + 1)
  have e1 : Tf C (Pk (r := s + 1) y z (s + 1)) = diagonal C y := by
    show _ = Tf C (fun _ => y)
    congr 1; funext l; have := l.isLt; simp [Pk, this]
  have e0 : Tf C (Pk (r := s + 1) y z 0) = diagonal C z := by
    show _ = Tf C (fun _ => z)
    congr 1
  rw [e1, e0, Finset.sum_range] at hrange
  rw [← hrange]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hP1 : Pk (r := s + 1) y z (k.val + 1) = Function.update (Pk y z k.val) k y := by
    funext l
    by_cases hl : l = k
    · subst hl; simp [Pk]
    · have : l.val ≠ k.val := fun h => hl (Fin.ext h)
      simp only [Pk, Function.update_of_ne hl]
      have : (l.val < k.val + 1) ↔ (l.val < k.val) := by omega
      simp only [this]
  have hP0 : Pk (r := s + 1) y z k.val = Function.update (Pk y z k.val) k z := by
    funext l
    by_cases hl : l = k
    · subst hl; simp [Pk]
    · simp [Function.update_of_ne hl]
  rw [← perm_pattern C hC y z (y - z) k.val k le_rfl, Tf_update_sub, ← hP1, ← hP0]

end HindsightGain.Uniform.Dev.Lem31

namespace HindsightGain.Uniform
open HindsightGain.Uniform.Dev.Lem31 in
/-- Lemma 3.1, (17)-(18), p.15, in arbitrary finite orthonormal coordinates. -/
theorem chk_lemma_3_1 {ι : Type} [Fintype ι] {r : ℕ} (hr : 2 ≤ r)
    (C : Tensor ι r) (hC : symmetric C)
    (Z Z' : Set (EuclideanSpace ℝ ι))
    (hZ : Z.Nonempty) (hZc : IsCompact Z)
    (hZ' : Z'.Nonempty) (hZ'c : IsCompact Z') (hconv : Convex ℝ Z')
    (y : EuclideanSpace ℝ ι) (hy : y ∈ Z)
    (hmax : ∀ x ∈ Z, diagonal C x ≤ diagonal C y) :
    ∃ z ∈ Z', polynomialMax C Z - polynomialMax C Z' ≤
      support Z (tensorL C (comparisonTensor r y z)) -
        support Z' (tensorL C (comparisonTensor r y z)) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  obtain ⟨z, hzZ', hzmax⟩ := hZ'c.exists_isMaxOn hZ' (Phi_cont C y).continuousOn
  refine ⟨z, hzZ', ?_⟩
  set v := tensorL C (comparisonTensor (s + 1) y z) with hv
  have hFOC : ∀ u ∈ Z', inner ℝ (u - z) v ≤ 0 := by
    intro u hu
    have hd := Phi_hasDerivAt C hC y z (u - z)
    have hlim := hd.tendsto_slope_zero_right
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with t ht
    have hmem : z + t • (u - z) ∈ Z' := hconv.add_smul_sub_mem hzZ' hu ⟨ht.1.le, ht.2⟩
    have := hzmax hmem
    simp only [Set.mem_setOf_eq] at this
    have h0 : Phi C y (z + (0:ℝ) • (u - z)) = Phi C y z := by simp
    simp only [zero_add, h0, smul_eq_mul]
    have : Phi C y (z + t • (u - z)) - Phi C y z ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.1.le) this
  have hcontI : Continuous fun u : EuclideanSpace ℝ ι => inner ℝ u v :=
    continuous_id.inner continuous_const
  have hsZ' : support Z' v ≤ inner ℝ z v := by
    refine csSup_le (hZ'.image _) ?_
    rintro _ ⟨u, hu, rfl⟩
    have := hFOC u hu
    rw [inner_sub_left] at this
    linarith
  have hsZ : inner ℝ y v ≤ support Z v :=
    le_csSup ((hZc.image hcontI).bddAbove) ⟨y, hy, rfl⟩
  have hpZ : polynomialMax C Z = diagonal C y := by
    refine IsGreatest.csSup_eq ⟨⟨y, hy, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩; exact hmax x hx
  have hpZ' : diagonal C z ≤ polynomialMax C Z' :=
    le_csSup ((hZ'c.image (diagonal_cont C)).bddAbove) ⟨z, hzZ', rfl⟩
  have htel := telescope C hC y z
  have hin := inner_LW C y z (y - z)
  rw [← hv] at hin
  rw [← htel, inner_sub_left] at hin
  rw [hpZ]
  linarith
end HindsightGain.Uniform
end
end

theorem solution : type_of% @HindsightGain.Uniform.chk_lemma_3_1 := @HindsightGain.Uniform.chk_lemma_3_1
