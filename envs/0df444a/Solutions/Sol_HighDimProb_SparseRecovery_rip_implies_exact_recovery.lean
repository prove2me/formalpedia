-- Prove2me | solution 1 for HighDimProb.SparseRecovery.rip_implies_exact_recovery
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T17:15:47.947993+00:00
-- url     : https://prove2.me/submissions/da12b336-3d70-4bbe-9c6a-3093a5838770

import Mathlib
import Definitions.Def_HighDimProb_SparseRecovery_L2Norm
import Definitions.Def_HighDimProb_SparseRecovery_L1Norm
import Definitions.Def_HighDimProb_SparseRecovery_Sparsity
import Definitions.Def_HighDimProb_SparseRecovery_RIP

set_option autoImplicit false

namespace F2C302B2

theorem poly01_extreme {n k : ℕ} (y : Fin n → ℝ)
    (hy : y ∈ ({z : Fin n → ℝ | (∀ j, 0 ≤ z j ∧ z j ≤ 1) ∧ ∑ j, z j ≤ k}).extremePoints ℝ) :
    ∀ j, y j = 0 ∨ y j = 1 := by
  rw [mem_extremePoints] at hy
  obtain ⟨⟨hb, hsum⟩, hext⟩ := hy
  have key : ∀ d : Fin n → ℝ, d ≠ 0 → (∀ j, 0 ≤ y j + d j ∧ y j + d j ≤ 1) →
      (∀ j, 0 ≤ y j - d j ∧ y j - d j ≤ 1) → ∑ j, (y j + d j) ≤ k →
      ∑ j, (y j - d j) ≤ k → False := by
    intro d hd h1 h2 h3 h4
    have hseg : y ∈ openSegment ℝ (y + d) (y - d) := by
      refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
      ext j; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    have hyd := (hext (y + d) ⟨h1, h3⟩ (y - d) ⟨h2, h4⟩ hseg).1
    apply hd
    ext j
    have := congrFun hyd j
    simp only [Pi.add_apply] at this
    simp only [Pi.zero_apply]; linarith
  by_contra hcon
  push_neg at hcon
  obtain ⟨j, hj0, hj1⟩ := hcon
  have hj0' : 0 < y j := lt_of_le_of_ne (hb j).1 (Ne.symm hj0)
  have hj1' : y j < 1 := lt_of_le_of_ne (hb j).2 hj1
  by_cases hother : ∃ j', j' ≠ j ∧ 0 < y j' ∧ y j' < 1
  · obtain ⟨j', hne, h0', h1'⟩ := hother
    set ε := min (min (y j) (1 - y j)) (min (y j') (1 - y j')) with hε
    have hεpos : 0 < ε := lt_min (lt_min hj0' (by linarith)) (lt_min h0' (by linarith))
    have e1 : ε ≤ y j := le_trans (min_le_left _ _) (min_le_left _ _)
    have e2 : ε ≤ 1 - y j := le_trans (min_le_left _ _) (min_le_right _ _)
    have e3 : ε ≤ y j' := le_trans (min_le_right _ _) (min_le_left _ _)
    have e4 : ε ≤ 1 - y j' := le_trans (min_le_right _ _) (min_le_right _ _)
    set d : Fin n → ℝ := fun i => (if i = j then ε else 0) - (if i = j' then ε else 0) with hd
    have hdsum : ∑ i, d i = 0 := by
      simp only [hd, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]; ring
    have hcoord : ∀ i, (d i = ε ∧ i = j) ∨ (d i = -ε ∧ i = j') ∨ (d i = 0 ∧ i ≠ j ∧ i ≠ j') := by
      intro i
      by_cases h1 : i = j
      · subst h1; left; simp [hd, hne.symm]
      · by_cases h2 : i = j'
        · subst h2; right; left; simp [hd, h1]
        · right; right; simp [hd, h1, h2]
    apply key d
    · intro h0
      have := congrFun h0 j
      simp [hd, hne.symm] at this
      linarith
    · intro i
      rcases hcoord i with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, -, -⟩ <;> rw [h] <;>
        constructor <;> linarith [hb i]
    · intro i
      rcases hcoord i with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, -, -⟩ <;> rw [h] <;>
        constructor <;> linarith [hb i]
    · rw [Finset.sum_add_distrib, hdsum]; linarith
    · rw [Finset.sum_sub_distrib, hdsum]; linarith
  · push_neg at hother
    have hbin : ∀ i, i ≠ j → y i = 0 ∨ y i = 1 := by
      intro i hi
      by_cases h0 : y i = 0
      · left; exact h0
      · right
        have : 0 < y i := lt_of_le_of_ne (hb i).1 (Ne.symm h0)
        exact le_antisymm (hb i).2 (hother i hi this)
    rcases lt_or_eq_of_le hsum with hlt | heq
    · set ε := min (min (y j) (1 - y j)) ((k : ℝ) - ∑ i, y i) with hε
      have hεpos : 0 < ε := lt_min (lt_min hj0' (by linarith)) (by linarith)
      have e1 : ε ≤ y j := le_trans (min_le_left _ _) (min_le_left _ _)
      have e2 : ε ≤ 1 - y j := le_trans (min_le_left _ _) (min_le_right _ _)
      have e3 : ε ≤ (k : ℝ) - ∑ i, y i := min_le_right _ _
      set d : Fin n → ℝ := fun i => if i = j then ε else 0 with hd
      have hdsum : ∑ i, d i = ε := by simp [hd]
      apply key d
      · intro h0
        have := congrFun h0 j
        simp [hd] at this
        linarith
      · intro i
        by_cases h : i = j
        · subst h; simp only [hd, if_true]; constructor <;> linarith
        · simp only [hd, if_neg h]; constructor <;> linarith [hb i]
      · intro i
        by_cases h : i = j
        · subst h; simp only [hd, if_true]; constructor <;> linarith
        · simp only [hd, if_neg h]; constructor <;> linarith [hb i]
      · rw [Finset.sum_add_distrib, hdsum]; linarith
      · rw [Finset.sum_sub_distrib, hdsum]; linarith
    · have hsplit : ∑ i, y i = y j + ∑ i ∈ Finset.univ.erase j, y i := by
        rw [Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      have hcount : ∑ i ∈ Finset.univ.erase j, y i =
          (((Finset.univ.erase j).filter (fun i => y i = 1)).card : ℝ) := by
        rw [← Finset.sum_boole]
        apply Finset.sum_congr rfl
        intro i hi
        have hij : i ≠ j := Finset.ne_of_mem_erase hi
        rcases hbin i hij with h | h
        · rw [h, if_neg (by norm_num)]
        · rw [h, if_pos rfl]
      set M := ((Finset.univ.erase j).filter (fun i => y i = 1)).card
      have hyj : y j = (k : ℝ) - M := by linarith
      have hMk : (M : ℝ) < k := by linarith
      have hkM : (k : ℝ) < M + 1 := by linarith
      have hMk' : M < k := by exact_mod_cast hMk
      have hkM' : k < M + 1 := by exact_mod_cast hkM
      omega

theorem poly01 {n k : ℕ} (c : Fin n → ℝ) (h0 : ∀ j, 0 ≤ c j) (h1 : ∀ j, c j ≤ 1)
    (hs : ∑ j, c j ≤ k) :
    ∃ (F : Finset (Fin n → ℝ)) (w : (Fin n → ℝ) → ℝ), (∀ y ∈ F, 0 ≤ w y) ∧
      ∑ y ∈ F, w y = 1 ∧ ∑ y ∈ F, w y • y = c ∧
      ∀ y ∈ F, (∀ j, y j = 0 ∨ y j = 1) ∧ ∑ j, y j ≤ k := by
  set Q : Set (Fin n → ℝ) := {z | (∀ j, 0 ≤ z j ∧ z j ≤ 1) ∧ ∑ j, z j ≤ k} with hQ
  set E : Set (Fin n → ℝ) := {z | (∀ j, z j = 0 ∨ z j = 1) ∧ ∑ j, z j ≤ k} with hE
  have hEfin : E.Finite := by
    apply Set.Finite.subset (Set.Finite.pi' (t := fun _ => ({0, 1} : Set ℝ))
      (fun _ => Set.toFinite _))
    intro z hz
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hz.1
  have hQc : IsClosed Q := by
    have : Q = (⋂ j, {z : Fin n → ℝ | 0 ≤ z j}) ∩ (⋂ j, {z : Fin n → ℝ | z j ≤ 1}) ∩
        {z | ∑ j, z j ≤ (k : ℝ)} := by
      ext z; simp [hQ, forall_and]
    rw [this]
    exact ((isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)).inter
      (isClosed_iInter fun j => isClosed_le (continuous_apply j) continuous_const)).inter
      (isClosed_le (continuous_finset_sum _ fun j _ => continuous_apply j) continuous_const)
  have hQcomp : IsCompact Q :=
    (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := fun _ => 1)).of_isClosed_subset hQc
      (fun z hz => ⟨fun j => (hz.1 j).1, fun j => (hz.1 j).2⟩)
  have hQconv : Convex ℝ Q := by
    intro x hx y hy a b ha hb hab
    refine ⟨fun j => ⟨?_, ?_⟩, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hx.1 j, hy.1 j]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hx.1 j, hy.1 j]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      nlinarith [hx.2, hy.2]
  have hKM := closure_convexHull_extremePoints hQcomp hQconv
  have hcQ : c ∈ Q := ⟨fun j => ⟨h0 j, h1 j⟩, hs⟩
  have hextE : Q.extremePoints ℝ ⊆ E := by
    intro y hy
    exact ⟨poly01_extreme y hy, (extremePoints_subset hy).2⟩
  have hsub : Q ⊆ convexHull ℝ E := by
    rw [← hKM]
    have hcl : IsClosed (convexHull ℝ E) := (hEfin.isCompact_convexHull (𝕜 := ℝ)).isClosed
    exact closure_minimal (convexHull_mono hextE) hcl
  have hcE := hsub hcQ
  have hEeq : E = ((hEfin.toFinset : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) := by simp
  rw [hEeq, Finset.mem_convexHull'] at hcE
  obtain ⟨w, hw0, hw1, hwc⟩ := hcE
  refine ⟨hEfin.toFinset, w, hw0, hw1, hwc, ?_⟩
  intro y hy
  rw [Set.Finite.mem_toFinset] at hy
  exact hy

end F2C302B2

namespace F2C302B2

open HighDimProb.SparseRecovery in
theorem ssparse_of_supp {n : ℕ} (v : Fin n → ℝ) (S : Finset (Fin n)) (r : ℝ)
    (hS : ∀ j, j ∉ S → v j = 0) (hr : (S.card : ℝ) ≤ r) : IsSSparse v r := by
  unfold IsSSparse
  refine le_trans ?_ hr
  exact_mod_cast Finset.card_le_card (fun j hj => by
    by_contra hjS
    exact (Finset.mem_filter.1 hj).2 (hS j hjS))

open HighDimProb.SparseRecovery in
theorem rip_sq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (α β r : ℝ) (hα : 0 < α)
    (hRIP : SatisfiesRIP A α β r) (v : Fin n → ℝ) (hv : IsSSparse v r) :
    α ^ 2 * ∑ j, v j ^ 2 ≤ ∑ i, (A.mulVec v) i ^ 2 ∧
      ∑ i, (A.mulVec v) i ^ 2 ≤ β ^ 2 * ∑ j, v j ^ 2 := by
  obtain ⟨h1, h2⟩ := hRIP v hv
  unfold l2Norm at h1 h2
  have e1 := Real.sq_sqrt (Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg (v j)))
  have e2 := Real.sq_sqrt (Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
    sq_nonneg ((A.mulVec v) i)))
  have p1 := Real.sqrt_nonneg (∑ j, v j ^ 2)
  have p2 := Real.sqrt_nonneg (∑ i, (A.mulVec v) i ^ 2)
  constructor
  · have := mul_le_mul h1 h1 (by positivity) p2
    nlinarith
  · have := mul_le_mul h2 h2 p2 (le_trans p2 h2)
    nlinarith

end F2C302B2

set_option maxHeartbeats 1600000 in
open HighDimProb.SparseRecovery in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (α β s lam : ℝ)
    (hα : 0 < α) (hlam : lam > (β / α) ^ 2)
    (hRIP : SatisfiesRIP A α β ((1 + lam) * s)) (x : Fin n → ℝ) (hx : IsSSparse x s)
    (xhat : Fin n → ℝ) (hfeas : A.mulVec xhat = A.mulVec x)
    (hopt : ∀ x' : Fin n → ℝ, A.mulVec x' = A.mulVec x → l1Norm xhat ≤ l1Norm x') :
    xhat = x := by
  set h : Fin n → ℝ := xhat - x with hh
  have hAh : A.mulVec h = 0 := by
    rw [hh, Matrix.mulVec_sub, hfeas, sub_self]
  set T : Finset (Fin n) := Finset.univ.filter (fun j => x j ≠ 0) with hTdef
  have hxT : ∀ j, j ∉ T → x j = 0 := by
    intro j hj
    by_contra hne
    exact hj (Finset.mem_filter.2 ⟨Finset.mem_univ j, hne⟩)
  set L : ℝ := ∑ j ∈ T, |h j| with hLdef
  set V : ℝ := ∑ j ∈ Tᶜ, |h j| with hVdef
  have hVL : V ≤ L := by
    have h1 := hopt x rfl
    unfold l1Norm at h1
    have e1 : ∑ j, |xhat j| = ∑ j ∈ T, |xhat j| + ∑ j ∈ Tᶜ, |xhat j| :=
      (Finset.sum_add_sum_compl T _).symm
    have e2 : ∑ j, |x j| = ∑ j ∈ T, |x j| + ∑ j ∈ Tᶜ, |x j| :=
      (Finset.sum_add_sum_compl T _).symm
    have hc1 : ∑ j ∈ Tᶜ, |x j| = 0 :=
      Finset.sum_eq_zero (fun j hj => by rw [hxT j (Finset.mem_compl.1 hj)]; simp)
    have hc2 : ∑ j ∈ Tᶜ, |xhat j| = V :=
      Finset.sum_congr rfl (fun j hj => by
        simp [hh, hxT j (Finset.mem_compl.1 hj)])
    have hT : ∑ j ∈ T, |x j| ≤ ∑ j ∈ T, |xhat j| + L := by
      rw [hLdef, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro j _
      have := abs_sub_abs_le_abs_sub (x j) (xhat j)
      rw [abs_sub_comm] at this
      simp only [hh, Pi.sub_apply]
      linarith
    linarith
  have hL0 : 0 ≤ L := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  by_cases hL : L = 0
  · have hLz : ∀ j ∈ T, |h j| = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg _)).1 hL
    have hV0 : V = 0 := le_antisymm (hL ▸ hVL) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    have hVz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg _)).1 hV0
    funext j
    have : h j = 0 := by
      by_cases hj : j ∈ T
      · exact abs_eq_zero.1 (hLz j hj)
      · exact abs_eq_zero.1 (hVz j (Finset.mem_compl.2 hj))
    simp only [hh, Pi.sub_apply] at this
    linarith
  exfalso
  have hLpos : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hL)
  set t : ℕ := T.card with htdef
  have hts : (t : ℝ) ≤ s := hx
  have ht1 : 1 ≤ t := by
    rw [htdef, Nat.one_le_iff_ne_zero]
    intro h0
    rw [Finset.card_eq_zero] at h0
    apply hL
    rw [hLdef, h0, Finset.sum_empty]
  have ht1r : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  have hlam0 : 0 ≤ lam := le_trans (sq_nonneg _) hlam.le
  have hβ2 : β ^ 2 < lam * α ^ 2 := by
    rw [div_pow, gt_iff_lt, div_lt_iff₀ (by positivity)] at hlam
    exact hlam
  have hs0 : 0 ≤ s := le_trans (by positivity) hts
  -- sum of squares on T
  have hCS : L ^ 2 ≤ t * ∑ j ∈ T, h j ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := T) (f := fun j => |h j|)
    simpa [sq_abs] using this
  have hST : 0 < ∑ j ∈ T, h j ^ 2 := by
    by_contra hneg
    push_neg at hneg
    have : L ^ 2 ≤ 0 := le_trans hCS (mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg)
    nlinarith
  -- restriction of h to T, to get α ≤ β
  set hT : Fin n → ℝ := fun j => if j ∈ T then h j else 0 with hhT
  have hTsp : IsSSparse hT ((1 + lam) * s) :=
    F2C302B2.ssparse_of_supp hT T _ (fun j hj => by simp [hhT, hj]) (by nlinarith)
  have hTsq : ∑ j, hT j ^ 2 = ∑ j ∈ T, h j ^ 2 := by
    have : ∀ j, hT j ^ 2 = if j ∈ T then h j ^ 2 else 0 := by
      intro j; by_cases hj : j ∈ T <;> simp [hhT, hj]
    rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_ite_mem, Finset.univ_inter]
  have hαβ : α ^ 2 ≤ β ^ 2 := by
    obtain ⟨r1, r2⟩ := F2C302B2.rip_sq A α β _ hα hRIP hT hTsp
    rw [hTsq] at r1 r2
    have := le_trans r1 r2
    exact le_of_mul_le_mul_right this hST
  have hα2 : 0 < α ^ 2 := by positivity
  have hlam1 : 1 < lam := by nlinarith
  -- the block size K
  set K : ℕ := ⌊(1 + lam) * s - t⌋₊ with hKdef
  have hKarg : lam * t ≤ (1 + lam) * s - t := by nlinarith
  have hK1 : (K : ℝ) ≤ (1 + lam) * s - t := Nat.floor_le (by nlinarith)
  have hK2 : (1 + lam) * s - t < K + 1 := Nat.lt_floor_add_one _
  have hKpos : 1 ≤ K := by
    rw [hKdef]
    apply Nat.le_floor
    push_cast
    nlinarith
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hKpos
  have hKcond : (β ^ 2 - α ^ 2) * t < 2 * α ^ 2 * K := by
    have a1 : (K : ℝ) > lam * t - 1 := by linarith
    have a2 : (β ^ 2 - α ^ 2) * t < (lam - 1) * α ^ 2 * t := by
      have : β ^ 2 - α ^ 2 < (lam - 1) * α ^ 2 := by linarith
      exact mul_lt_mul_of_pos_right this (by linarith)
    have a3 : (lam - 1) * α ^ 2 * t ≤ 2 * α ^ 2 * (lam * t - 1) := by
      have : 0 ≤ lam * t + t - 2 := by nlinarith
      nlinarith [mul_nonneg hα2.le this]
    have a4 : 2 * α ^ 2 * (lam * t - 1) < 2 * α ^ 2 * K := by
      have := mul_lt_mul_of_pos_left a1 (by positivity : (0:ℝ) < 2 * α ^ 2)
      linarith
    linarith
  -- threshold
  set a : ℝ := L / K with hadef
  have hapos : 0 < a := by positivity
  have hKa : (K : ℝ) * a = L := by rw [hadef]; field_simp
  set T1 : Finset (Fin n) := Tᶜ.filter (fun j => a < |h j|) with hT1def
  set R : Finset (Fin n) := Tᶜ.filter (fun j => ¬ a < |h j|) with hRdef
  set k1 : ℕ := T1.card with hk1def
  have hsplitV : ∑ j ∈ T1, |h j| + ∑ j ∈ R, |h j| = V :=
    Finset.sum_filter_add_sum_filter_not Tᶜ _ _
  have hk1a : (k1 : ℝ) * a ≤ ∑ j ∈ T1, |h j| := by
    have := Finset.card_nsmul_le_sum T1 (fun j => |h j|) a
      (fun j hj => le_of_lt (Finset.mem_filter.1 hj).2)
    simpa [nsmul_eq_mul] using this
  have hRnn : 0 ≤ ∑ j ∈ R, |h j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hk1K : k1 ≤ K := by
    have : (k1 : ℝ) * a ≤ K * a := by linarith
    have := le_of_mul_le_mul_right this hapos
    exact_mod_cast this
  have hRsum : ∑ j ∈ R, |h j| ≤ ((K - k1 : ℕ) : ℝ) * a := by
    rw [Nat.cast_sub hk1K]
    nlinarith
  have hRle : ∀ j ∈ R, |h j| ≤ a := fun j hj => not_lt.1 (Finset.mem_filter.1 hj).2
  have hRT : ∀ j ∈ R, j ∉ T := fun j hj => Finset.mem_compl.1 (Finset.mem_filter.1 hj).1
  -- card of Rᶜ
  have hcardR : Rᶜ.card = t + k1 := by
    have c1 := Finset.card_filter_add_card_filter_not (s := Tᶜ) (fun j => a < |h j|)
    have c2 := Finset.card_compl R
    have c3 := Finset.card_compl T
    have c4 : T.card ≤ Fintype.card (Fin n) := Finset.card_le_univ T
    have c5 : R.card ≤ Fintype.card (Fin n) := Finset.card_le_univ R
    rw [← hT1def, ← hRdef] at c1
    omega
  -- normalized vector c
  set c : Fin n → ℝ := fun j => if j ∈ R then |h j| / a else 0 with hcdef
  have hc0 : ∀ j, 0 ≤ c j := by
    intro j; by_cases hj : j ∈ R
    · simp only [hcdef, if_pos hj]; positivity
    · simp [hcdef, hj]
  have hc1 : ∀ j, c j ≤ 1 := by
    intro j; by_cases hj : j ∈ R
    · simp only [hcdef, if_pos hj]; rw [div_le_one hapos]; exact hRle j hj
    · simp [hcdef, hj]
  have hcsum : ∑ j, c j ≤ ((K - k1 : ℕ) : ℝ) := by
    have : ∑ j, c j = (∑ j ∈ R, |h j|) / a := by
      rw [hcdef, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_div]
    rw [this, div_le_iff₀ hapos]
    exact hRsum
  obtain ⟨F, w, hw0, hw1, hwc, hF⟩ := F2C302B2.poly01 c hc0 hc1 hcsum
  -- signs
  set g : Fin n → ℝ := fun j => if j ∈ R then a * h j / |h j| else 0 with hgdef
  set v' : Fin n → ℝ := fun j => if j ∈ R then h j else 0 with hv'def
  set H : Fin n → ℝ := fun j => if j ∈ R then 0 else h j with hHdef
  have hgc : ∀ j, c j * g j = v' j := by
    intro j
    by_cases hj : j ∈ R
    · simp only [hcdef, hgdef, hv'def, if_pos hj]
      by_cases h0 : h j = 0
      · simp [h0]
      · have : |h j| ≠ 0 := abs_ne_zero.2 h0
        field_simp
    · simp [hcdef, hgdef, hv'def, hj]
  have hg2c : ∀ j, g j ^ 2 * c j ≤ a * (if j ∈ R then |h j| else 0) := by
    intro j
    by_cases hj : j ∈ R
    · simp only [hcdef, hgdef, if_pos hj]
      by_cases h0 : h j = 0
      · simp [h0]
      · have hne : |h j| ≠ 0 := abs_ne_zero.2 h0
        have hsq : h j ^ 2 = |h j| ^ 2 := (sq_abs _).symm
        apply le_of_eq
        field_simp
        rw [hsq]
    · simp [hcdef, hgdef, hj]
  set u : (Fin n → ℝ) → (Fin n → ℝ) := fun y j => y j * g j with hudef
  have hcoord : ∀ j, ∑ y ∈ F, w y * y j = c j := by
    intro j
    have := congrFun hwc j
    rw [Finset.sum_apply] at this
    simpa using this
  have hv'eq : ∑ y ∈ F, w y • u y = v' := by
    funext j
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, hudef]
    rw [← hgc j, ← hcoord j, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _; ring
  have hhHv : h = H + v' := by
    funext j
    by_cases hj : j ∈ R <;> simp [hHdef, hv'def, hj]
  have hAHv : A.mulVec H = -(∑ y ∈ F, w y • A.mulVec (u y)) := by
    have : A.mulVec H + A.mulVec v' = 0 := by rw [← Matrix.mulVec_add, ← hhHv, hAh]
    rw [← hv'eq, Matrix.mulVec_sum] at this
    simp only [Matrix.mulVec_smul] at this
    exact eq_neg_of_add_eq_zero_left this
  -- sparsity facts
  have hbound : ((t + K : ℕ) : ℝ) ≤ (1 + lam) * s := by push_cast; linarith
  have hHsp : IsSSparse H ((1 + lam) * s) := by
    apply F2C302B2.ssparse_of_supp H Rᶜ
    · intro j hj
      simp [hHdef, Finset.notMem_compl.1 hj]
    · rw [hcardR]
      refine le_trans ?_ hbound
      exact_mod_cast (by omega : t + k1 ≤ t + K)
  have hcardy : ∀ y ∈ F, (Finset.univ.filter (fun j => y j ≠ 0)).card ≤ K - k1 := by
    intro y hy
    obtain ⟨h01, hsum⟩ := hF y hy
    have : ∑ j, y j = ((Finset.univ.filter (fun j => y j ≠ 0)).card : ℝ) := by
      rw [← Finset.sum_boole]
      apply Finset.sum_congr rfl
      intro j _
      rcases h01 j with h | h
      · simp [h]
      · simp [h]
    rw [this] at hsum
    exact_mod_cast hsum
  have hHusp : ∀ y ∈ F, IsSSparse (H + u y) ((1 + lam) * s) := by
    intro y hy
    apply F2C302B2.ssparse_of_supp _ (Rᶜ ∪ Finset.univ.filter (fun j => y j ≠ 0))
    · intro j hj
      rw [Finset.mem_union, not_or] at hj
      have hjR : j ∈ R := by simpa using hj.1
      have hyj : y j = 0 := by simpa using hj.2
      simp [hHdef, hudef, hjR, hyj]
    · refine le_trans ?_ hbound
      have := Finset.card_union_le Rᶜ (Finset.univ.filter (fun j => y j ≠ 0))
      have := hcardy y hy
      exact_mod_cast (by omega : (Rᶜ ∪ Finset.univ.filter (fun j => y j ≠ 0)).card ≤ t + K)
  have husp : ∀ y ∈ F, IsSSparse (u y) ((1 + lam) * s) := by
    intro y hy
    apply F2C302B2.ssparse_of_supp _ (Finset.univ.filter (fun j => y j ≠ 0))
    · intro j hj
      have hyj : y j = 0 := by simpa using hj
      simp [hudef, hyj]
    · refine le_trans ?_ hbound
      have := hcardy y hy
      exact_mod_cast (by omega : (Finset.univ.filter (fun j => y j ≠ 0)).card ≤ t + K)
  -- norms
  set X : ℝ := ∑ j, H j ^ 2 with hXdef
  set U : (Fin n → ℝ) → ℝ := fun y => ∑ j, u y j ^ 2 with hUdef
  have hHu_orth : ∀ y, ∑ j, (H + u y) j ^ 2 = X + U y := by
    intro y
    rw [hXdef, hUdef, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ R
    · simp [hHdef, hudef, hgdef, hj]
    · simp [hHdef, hudef, hgdef, hj]
  have hXT : ∑ j ∈ T, h j ^ 2 ≤ X := by
    rw [← hTsq, hXdef]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j ∈ T
    · have : j ∉ R := fun hjR => hRT j hjR hj
      simp [hhT, hHdef, hj, this]
    · simp only [hhT, if_neg hj]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact sq_nonneg _
  -- W bound
  set W : ℝ := ∑ y ∈ F, w y * U y with hWdef
  have hW : W ≤ a * L := by
    have e1 : ∀ y ∈ F, U y = ∑ j, y j * g j ^ 2 := by
      intro y hy
      obtain ⟨h01, -⟩ := hF y hy
      apply Finset.sum_congr rfl
      intro j _
      rcases h01 j with h | h <;> simp [hudef, h]
    have e2 : W = ∑ j, g j ^ 2 * c j := by
      rw [hWdef, Finset.sum_congr rfl (fun y hy => by rw [e1 y hy])]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← hcoord j, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _; ring
    rw [e2]
    calc ∑ j, g j ^ 2 * c j ≤ ∑ j, a * (if j ∈ R then |h j| else 0) :=
          Finset.sum_le_sum (fun j _ => hg2c j)
      _ = a * ∑ j ∈ R, |h j| := by
          rw [← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter]
      _ ≤ a * L := by
          apply mul_le_mul_of_nonneg_left _ hapos.le
          have hT1nn : 0 ≤ ∑ j ∈ T1, |h j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
          linarith
  have hW0 : 0 ≤ W := by
    apply Finset.sum_nonneg
    intro y hy
    exact mul_nonneg (hw0 y hy) (Finset.sum_nonneg (fun j _ => sq_nonneg _))
  -- the identity
  set Y : Fin m → ℝ := A.mulVec H with hYdef
  set Z : (Fin n → ℝ) → Fin m → ℝ := fun y => A.mulVec (u y) with hZdef
  have hYZ : ∀ i, Y i = -∑ y ∈ F, w y * Z y i := by
    intro i
    have := congrFun hAHv i
    rw [Pi.neg_apply, Finset.sum_apply] at this
    simpa using this
  have hident : ∑ y ∈ F, w y * ∑ i, (Y i + Z y i) ^ 2 + ∑ i, Y i ^ 2 =
      ∑ y ∈ F, w y * ∑ i, Z y i ^ 2 := by
    have hpt : ∀ i, ∑ y ∈ F, w y * (Y i + Z y i) ^ 2 + Y i ^ 2 =
        ∑ y ∈ F, w y * Z y i ^ 2 := by
      intro i
      have e : ∀ y, w y * (Y i + Z y i) ^ 2 =
          Y i ^ 2 * w y + 2 * Y i * (w y * Z y i) + w y * Z y i ^ 2 := by intro y; ring
      simp_rw [e]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        hw1]
      have := hYZ i
      have h2 : ∑ y ∈ F, w y * Z y i = - Y i := by linarith
      rw [h2]; ring
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => hpt i)
  -- bounds
  have hlow1 : ∀ y ∈ F, α ^ 2 * (X + U y) ≤ ∑ i, (Y i + Z y i) ^ 2 := by
    intro y hy
    have := (F2C302B2.rip_sq A α β _ hα hRIP (H + u y) (hHusp y hy)).1
    rw [hHu_orth, Matrix.mulVec_add] at this
    simpa [hYdef, hZdef] using this
  have hlow2 : α ^ 2 * X ≤ ∑ i, Y i ^ 2 := (F2C302B2.rip_sq A α β _ hα hRIP H hHsp).1
  have hup : ∀ y ∈ F, ∑ i, Z y i ^ 2 ≤ β ^ 2 * U y := by
    intro y hy
    exact (F2C302B2.rip_sq A α β _ hα hRIP (u y) (husp y hy)).2
  have hS1 : ∑ y ∈ F, w y * (α ^ 2 * (X + U y)) ≤ ∑ y ∈ F, w y * ∑ i, (Y i + Z y i) ^ 2 :=
    Finset.sum_le_sum (fun y hy => mul_le_mul_of_nonneg_left (hlow1 y hy) (hw0 y hy))
  have hS2 : ∑ y ∈ F, w y * ∑ i, Z y i ^ 2 ≤ ∑ y ∈ F, w y * (β ^ 2 * U y) :=
    Finset.sum_le_sum (fun y hy => mul_le_mul_of_nonneg_left (hup y hy) (hw0 y hy))
  have hS1' : ∑ y ∈ F, w y * (α ^ 2 * (X + U y)) = α ^ 2 * X + α ^ 2 * W := by
    have e : ∀ y, w y * (α ^ 2 * (X + U y)) = α ^ 2 * X * w y + α ^ 2 * (w y * U y) := by
      intro y; ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hw1, hWdef]; ring
  have hS2' : ∑ y ∈ F, w y * (β ^ 2 * U y) = β ^ 2 * W := by
    rw [hWdef, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro y _; ring
  have hmain : 2 * α ^ 2 * X + α ^ 2 * W ≤ β ^ 2 * W := by linarith
  -- final contradiction
  have hXpos : L ^ 2 ≤ t * X := le_trans hCS (mul_le_mul_of_nonneg_left hXT (Nat.cast_nonneg t))
  have hD : 0 ≤ β ^ 2 - α ^ 2 := by linarith
  have f1 : 2 * α ^ 2 * X ≤ (β ^ 2 - α ^ 2) * (a * L) := by
    have := mul_le_mul_of_nonneg_left hW hD
    linarith
  have f2 : 2 * α ^ 2 * K * X ≤ (β ^ 2 - α ^ 2) * L ^ 2 := by
    have := mul_le_mul_of_nonneg_left f1 (by positivity : (0:ℝ) ≤ K)
    have e : (K : ℝ) * ((β ^ 2 - α ^ 2) * (a * L)) = (β ^ 2 - α ^ 2) * L ^ 2 := by
      rw [← hKa]; ring
    nlinarith
  have f3 : (β ^ 2 - α ^ 2) * L ^ 2 ≤ (β ^ 2 - α ^ 2) * (t * X) :=
    mul_le_mul_of_nonneg_left hXpos hD
  have hXp : 0 < X := by nlinarith
  nlinarith
