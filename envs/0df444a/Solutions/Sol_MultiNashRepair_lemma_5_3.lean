-- Prove2me | solution 1 for MultiNashRepair.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T00:12:41.241883+00:00
-- url     : https://prove2.me/submissions/606f8163-f309-43ef-8171-37495cbff873

import Mathlib
import Definitions.Def_NashAmplification_Filtering_Model
import Definitions.Def_MultiNashRepair_DescentLP
import Definitions.Def_MultiNashRepair_Sweeps
import Definitions.Def_MultiNashRepair_Generation

open NashAmplification.Filtering (Mixed Utility Tuple BoundedGame)
open Finset
open MultiNashRepair

theorem MNR51_pp_update {m : ℕ} {n : Fin m → ℕ} (y : Mixed n) (j : Fin m)
    (w : Fin (n j) → ℝ) (s : Tuple n) :
    AGT.profileProb (Function.update y j w) s = w (s j) * ∏ k ∈ univ.erase j, y k (s k) := by
  unfold AGT.profileProb
  rw [← Finset.mul_prod_erase univ _ (mem_univ j)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (ne_of_mem_erase hk)]

theorem MNR51_lin {m : ℕ} {n : Fin m → ℕ} (y : Mixed n) (j : Fin m)
    (z : Fin (n j) → ℝ) (D : Tuple n → ℝ) :
    ∑ s, AGT.profileProb (Function.update y j z) s * D s
      = ∑ b, z b * ∑ s, AGT.profileProb (Function.update y j (ePure b)) s * D s := by
  simp only [MNR51_pp_update, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have : z (s j) = ∑ b, z b * (ePure b) (s j) := by
    simp [ePure, DGPNash.WellSupported.pureStrategy]
  rw [this, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _; ring

theorem MNR51_swap {m : ℕ} {n : Fin m → ℕ} (y : Mixed n) (i : Fin m) (a c : Fin (n i))
    (F : Tuple n → ℝ) :
    ∑ s, AGT.profileProb (Function.update y i (ePure c)) s * F (Function.update s i a)
      = ∑ s, AGT.profileProb (Function.update y i (ePure a)) s * F s := by
  let φ : Tuple n → Tuple n := fun s => Function.update s i (Equiv.swap a c (s i))
  have hφ : Function.Involutive φ := by
    intro s
    simp only [φ, Function.update_self, Function.update_idem, Equiv.swap_apply_self,
      Function.update_eq_self]
  rw [← Equiv.sum_comp hφ.toPerm (fun s => AGT.profileProb (Function.update y i (ePure a)) s * F s)]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Function.Involutive.coe_toPerm, MNR51_pp_update]
  have hR : ∏ k ∈ univ.erase i, y k (φ s k) = ∏ k ∈ univ.erase i, y k (s k) := by
    apply Finset.prod_congr rfl
    intro k hk
    simp only [φ, Function.update_of_ne (ne_of_mem_erase hk)]
  rw [hR]
  have hφi : φ s i = Equiv.swap a c (s i) := by simp [φ]
  rw [hφi]
  by_cases hs : s i = c
  · have h1 : Equiv.swap a c (s i) = a := by rw [hs]; exact Equiv.swap_apply_right a c
    have h2 : φ s = Function.update s i a := by simp only [φ, h1]
    rw [h1, h2, hs]
    simp [ePure, DGPNash.WellSupported.pureStrategy]
  · have h1 : Equiv.swap a c (s i) ≠ a := by
      intro h; apply hs
      have := congrArg (Equiv.swap a c) h
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
    simp [ePure, DGPNash.WellSupported.pureStrategy, hs, h1]

theorem MNR51_sum_pp {m : ℕ} {n : Fin m → ℕ} (y : Mixed n) (hy : AGT.IsMixedProfile y) :
    ∑ s : Tuple n, AGT.profileProb y s = 1 := by
  unfold AGT.profileProb
  rw [← Fintype.prod_sum]
  exact Finset.prod_eq_one (fun j _ => (hy j).2)

theorem MNR51_pure_shift {m : ℕ} {n : Fin m → ℕ} (y : Mixed n) (hy : AGT.IsMixedProfile y)
    (i : Fin m) (a : Fin (n i)) (F : Tuple n → ℝ) :
    ∑ s, AGT.profileProb y s * F (Function.update s i a)
      = ∑ s, AGT.profileProb (Function.update y i (ePure a)) s * F s := by
  have h0 : y = Function.update y i (y i) := (Function.update_eq_self i y).symm
  conv_lhs => rw [h0]
  rw [MNR51_lin y i (y i) (fun s => F (Function.update s i a))]
  simp only [MNR51_swap]
  rw [← Finset.sum_mul, (hy i).2, one_mul]

theorem MNR51_deficit_eq {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (y : Mixed n)
    (hy : AGT.IsMixedProfile y) (i : Fin m) (a : Fin (n i)) :
    deficit u y i a = ∑ s, AGT.profileProb y s * (1 + u i s - u i (Function.update s i a)) := by
  have h1 : DGPNash.NashMap.purePayoff u y i a
      = ∑ s, AGT.profileProb y s * u i (Function.update s i a) := by
    rw [MNR51_pure_shift y hy i a (fun s => u i s)]
    rfl
  unfold deficit gain
  rw [h1]
  unfold AGT.expectedPayoff
  simp only [mul_sub, mul_add, mul_one, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    MNR51_sum_pp y hy]
  ring

theorem MNR51_prod_expand {ι : Type*} [DecidableEq ι] (S : Finset ι) (A B : ι → ℝ)
    (hA : ∀ k, 0 ≤ A k) (hB : ∀ k, 0 ≤ B k) :
    ∏ k ∈ S, A k + ∑ j ∈ S, B j * ∏ k ∈ S.erase j, A k ≤ ∏ k ∈ S, (A k + B k) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha, Finset.erase_insert ha]
    have hrest : ∑ j ∈ S, B j * ∏ k ∈ (insert a S).erase j, A k
        = A a * ∑ j ∈ S, B j * ∏ k ∈ S.erase j, A k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hja : j ≠ a := fun h => ha (h ▸ hj)
      rw [Finset.erase_insert_of_ne (Ne.symm hja), Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
      ring
    rw [hrest]
    have hP : 0 ≤ ∏ k ∈ S, A k := Finset.prod_nonneg (fun k _ => hA k)
    have hSig : 0 ≤ ∑ j ∈ S, B j * ∏ k ∈ S.erase j, A k :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (hB j) (Finset.prod_nonneg (fun k _ => hA k)))
    have := mul_le_mul_of_nonneg_left ih (add_nonneg (hA a) (hB a))
    nlinarith only [this, mul_nonneg (hB a) hSig, hP]

theorem MNR51_xp_apply {m : ℕ} {n : Fin m → ℕ} (x : Mixed n) (η : ℝ)
    (z : (j : Fin m) → Fin (n j) → ℝ) (j : Fin m) (c : Fin (n j)) :
    descentProfile x η z j c = (1 - η * ∑ b, z j b) * x j c + η * z j c := by
  simp only [descentProfile, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  congr 1
  simp [ePure, DGPNash.WellSupported.pureStrategy]

theorem MNR51_xp_mixed {m : ℕ} {n : Fin m → ℕ} (x : Mixed n) (hx : AGT.IsMixedProfile x)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (z : (j : Fin m) → Fin (n j) → ℝ) (hz : LPFeasible z) :
    AGT.IsMixedProfile (descentProfile x η z) := by
  intro j
  have hZj : ∑ b, z j b ≤ 1 := by
    have h1 : ∑ b, z j b ≤ ∑ k, ∑ b, z k b :=
      Finset.single_le_sum (f := fun k => ∑ b, z k b)
        (fun k _ => Finset.sum_nonneg (fun b _ => hz.1 k b)) (mem_univ j)
    linarith [hz.2]
  have hZj0 : 0 ≤ ∑ b, z j b := Finset.sum_nonneg (fun b _ => hz.1 j b)
  have hc : 0 ≤ 1 - η * ∑ b, z j b := by nlinarith only [hZj, hZj0, hη0, hη1]
  constructor
  · intro c
    rw [MNR51_xp_apply]
    exact add_nonneg (mul_nonneg hc ((hx j).1 c)) (mul_nonneg hη0 (hz.1 j c))
  · simp only [MNR51_xp_apply, Finset.sum_add_distrib, ← Finset.mul_sum, (hx j).2]
    ring

theorem MNR51_ePure_lottery {m : ℕ} {n : Fin m → ℕ} {j : Fin m} (b : Fin (n j)) :
    AGT.IsLottery (ePure b) := by
  constructor
  · intro c; simp only [ePure, DGPNash.WellSupported.pureStrategy]; split_ifs <;> norm_num
  · simp [ePure, DGPNash.WellSupported.pureStrategy]

theorem MNR51_update_mixed {m : ℕ} {n : Fin m → ℕ} (x : Mixed n) (hx : AGT.IsMixedProfile x)
    (j : Fin m) (y : Fin (n j) → ℝ) (hy : AGT.IsLottery y) :
    AGT.IsMixedProfile (Function.update x j y) := by
  intro k
  by_cases hk : k = j
  · subst hk; simpa using hy
  · simpa [Function.update_of_ne hk] using hx k

theorem MNR51_cfac {m : ℕ} {n : Fin m → ℕ} (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (z : (j : Fin m) → Fin (n j) → ℝ) (hz : LPFeasible z) (j : Fin m) :
    0 ≤ 1 - η * ∑ b, z j b ∧ 1 - η * ∑ b, z j b ≤ 1 := by
  have hZj : ∑ b, z j b ≤ 1 := by
    have h1 : ∑ b, z j b ≤ ∑ k, ∑ b, z k b :=
      Finset.single_le_sum (f := fun k => ∑ b, z k b)
        (fun k _ => Finset.sum_nonneg (fun b _ => hz.1 k b)) (mem_univ j)
    linarith [hz.2]
  have hZj0 : 0 ≤ ∑ b, z j b := Finset.sum_nonneg (fun b _ => hz.1 j b)
  constructor
  · nlinarith only [hZj, hZj0, hη0, hη1]
  · nlinarith only [hZj0, hη0]

theorem MNR51_pp_xp {m : ℕ} {n : Fin m → ℕ} (x : Mixed n) (hx : AGT.IsMixedProfile x)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (z : (j : Fin m) → Fin (n j) → ℝ) (hz : LPFeasible z)
    (s : Tuple n) :
    descentFactor η z * AGT.profileProb x s
      + ∑ j, descentFactor η z * η * AGT.profileProb (Function.update x j (z j)) s
      ≤ AGT.profileProb (descentProfile x η z) s := by
  set A : Fin m → ℝ := fun k => (1 - η * ∑ b, z k b) * x k (s k) with hA
  set B : Fin m → ℝ := fun k => η * z k (s k) with hB
  have hc := MNR51_cfac η hη0 hη1 z hz
  have hA0 : ∀ k, 0 ≤ A k := fun k => mul_nonneg (hc k).1 ((hx k).1 _)
  have hB0 : ∀ k, 0 ≤ B k := fun k => mul_nonneg hη0 (hz.1 k _)
  have hexp := MNR51_prod_expand univ A B hA0 hB0
  have hxp : AGT.profileProb (descentProfile x η z) s = ∏ k, (A k + B k) := by
    unfold AGT.profileProb
    apply Finset.prod_congr rfl
    intro k _; rw [MNR51_xp_apply]
  have hPA : descentFactor η z * AGT.profileProb x s = ∏ k, A k := by
    unfold descentFactor AGT.profileProb; rw [← Finset.prod_mul_distrib]
  rw [hxp, hPA]
  refine le_trans (add_le_add le_rfl (Finset.sum_le_sum (fun j _ => ?_))) hexp
  rw [MNR51_pp_update]
  have hP : descentFactor η z ≤ ∏ k ∈ univ.erase j, (1 - η * ∑ b, z k b) := by
    unfold descentFactor
    rw [← Finset.mul_prod_erase univ _ (mem_univ j)]
    have : 0 ≤ ∏ k ∈ univ.erase j, (1 - η * ∑ b, z k b) :=
      Finset.prod_nonneg (fun k _ => (hc k).1)
    nlinarith only [this, (hc j).2]
  have hAe : ∏ k ∈ univ.erase j, A k
      = (∏ k ∈ univ.erase j, (1 - η * ∑ b, z k b)) * ∏ k ∈ univ.erase j, x k (s k) := by
    rw [← Finset.prod_mul_distrib]
  rw [hAe]
  have hX : 0 ≤ ∏ k ∈ univ.erase j, x k (s k) := Finset.prod_nonneg (fun k _ => (hx k).1 _)
  have hzz : 0 ≤ η * z j (s j) := mul_nonneg hη0 (hz.1 j _)
  have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hP hX) hzz
  simp only [hB]
  nlinarith only [this]

theorem MNR51_deficit_xp {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (hu : BoundedGame u)
    (x : Mixed n) (hx : AGT.IsMixedProfile x)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (z : (j : Fin m) → Fin (n j) → ℝ) (hz : LPFeasible z)
    (i : Fin m) (a : Fin (n i)) :
    descentFactor η z * ((1 + η * ∑ j, ∑ b, z j b) * deficit u x i a
        - η * ∑ j, ∑ b, z j b * repl u x j b i a)
      ≤ deficit u (descentProfile x η z) i a := by
  have hxp := MNR51_xp_mixed x hx η hη0 hη1 z hz
  set D : Tuple n → ℝ := fun s => 1 + u i s - u i (Function.update s i a) with hD
  have hD0 : ∀ s, 0 ≤ D s := by
    intro s; simp only [hD]
    have h1 := (hu i s).1; have h2 := (hu i (Function.update s i a)).2
    linarith
  rw [MNR51_deficit_eq u _ hxp i a]
  have step1 : ∑ s, (descentFactor η z * AGT.profileProb x s
      + ∑ j, descentFactor η z * η * AGT.profileProb (Function.update x j (z j)) s) * D s
      ≤ ∑ s, AGT.profileProb (descentProfile x η z) s * D s :=
    Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_right (MNR51_pp_xp x hx η hη0 hη1 z hz s) (hD0 s))
  refine le_trans (le_of_eq ?_) step1
  have hdx := MNR51_deficit_eq u x hx i a
  have hdj : ∀ j (b : Fin (n j)), deficit u (Function.update x j (ePure b)) i a
      = deficit u x i a - repl u x j b i a := by
    intro j b; unfold repl deficit; ring
  have hlin : ∀ j, ∑ s, AGT.profileProb (Function.update x j (z j)) s * D s
      = ∑ b, z j b * (deficit u x i a - repl u x j b i a) := by
    intro j
    rw [MNR51_lin x j (z j) D]
    apply Finset.sum_congr rfl
    intro b _
    rw [← hdj j b, MNR51_deficit_eq u _ (MNR51_update_mixed x hx j _ (MNR51_ePure_lottery b)) i a]
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, ← mul_assoc]
  have e1 : ∀ j, ∑ s, descentFactor η z * η * AGT.profileProb (Function.update x j (z j)) s * D s
      = descentFactor η z * η * ∑ b, z j b * (deficit u x i a - repl u x j b i a) := by
    intro j; rw [← hlin j, Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring
  simp only [e1]
  rw [show ∑ s, descentFactor η z * AGT.profileProb x s * D s
      = descentFactor η z * ∑ s, AGT.profileProb x s * D s by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring]
  rw [← hdx]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem MNR51_ep_bounds {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (hu : BoundedGame u)
    (x : Mixed n) (hx : AGT.IsMixedProfile x) (i : Fin m) :
    0 ≤ AGT.expectedPayoff u x i ∧ AGT.expectedPayoff u x i ≤ 1 := by
  have hp : ∀ s : Tuple n, 0 ≤ AGT.profileProb x s := fun s =>
    Finset.prod_nonneg (fun j _ => (hx j).1 (s j))
  unfold AGT.expectedPayoff
  constructor
  · exact Finset.sum_nonneg (fun s _ => mul_nonneg (hp s) (hu i s).1)
  · calc ∑ s, AGT.profileProb x s * u i s ≤ ∑ s, AGT.profileProb x s * 1 :=
          Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hu i s).2 (hp s))
      _ = 1 := by simp [MNR51_sum_pp x hx]

theorem MNR51_deficitMix_nonneg {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (hu : BoundedGame u)
    (x : Mixed n) (hx : AGT.IsMixedProfile x) (i : Fin m) (b : Fin (n i) → ℝ)
    (hb : AGT.IsLottery b) : 0 ≤ deficitMix u x i b := by
  unfold deficitMix
  have h1 := (MNR51_ep_bounds u hu _ (MNR51_update_mixed x hx i b hb) i).2
  have h2 := (MNR51_ep_bounds u hu x hx i).1
  linarith

theorem MNR51_ep_lin {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (x : Mixed n) (j : Fin m)
    (y : Fin (n j) → ℝ) (i : Fin m) :
    AGT.expectedPayoff u (Function.update x j y) i
      = ∑ b, y b * AGT.expectedPayoff u (Function.update x j (ePure b)) i := by
  unfold AGT.expectedPayoff
  exact MNR51_lin x j y (fun s => u i s)

theorem MNR51_gain_lin {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (x : Mixed n) (j : Fin m)
    (y : Fin (n j) → ℝ) (hy : AGT.IsLottery y) (i : Fin m) (a : Fin (n i)) :
    gain u (Function.update x j y) i a = ∑ b, y b * gain u (Function.update x j (ePure b)) i a := by
  unfold gain
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← MNR51_ep_lin u x j y i]
  congr 1
  unfold DGPNash.NashMap.purePayoff
  by_cases hij : j = i
  · subst hij
    simp only [Function.update_idem]
    rw [← Finset.sum_mul, hy.2, one_mul]
  · rw [Function.update_comm hij, MNR51_ep_lin u _ j y i]
    apply Finset.sum_congr rfl
    intro b _
    rw [Function.update_comm hij]

theorem MNR51_lam_deficit {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (x : Mixed n)
    (w : (i : Fin m) → Fin (n i) → ℝ) (hw0 : ∀ i a, 0 ≤ w i a) (i : Fin m) :
    lam w i * deficitMix u x i (bdev w i) = ∑ a, w i a * (1 - gain u x i a) := by
  by_cases hl : 0 < lam w i
  · have hb : bdev w i = fun a => w i a / lam w i := by simp [bdev, hl]
    unfold deficitMix
    rw [hb, MNR51_ep_lin u x i]
    have hlam : lam w i = ∑ a, w i a := rfl
    unfold gain DGPNash.NashMap.purePayoff
    simp only [mul_sub, mul_add, mul_one, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.mul_sum]
    rw [← hlam]
    have e : ∀ a, lam w i * (w i a / lam w i * AGT.expectedPayoff u (Function.update x i (ePure a)) i)
        = w i a * AGT.expectedPayoff u (Function.update x i (fun k => if k = a then 1 else 0)) i := by
      intro a; field_simp; rfl
    simp only [e, ← Finset.sum_mul, ← hlam]
    ring
  · have h0 : lam w i = 0 := le_antisymm (not_lt.mp hl) (Finset.sum_nonneg (fun a _ => hw0 i a))
    have hw : ∀ a, w i a = 0 := by
      intro a
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hw0 i a)).mp h0 a (mem_univ a)
    rw [h0]; simp [hw]

theorem MNR51_Fsum {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (x : Mixed n)
    (w : (i : Fin m) → Fin (n i) → ℝ) (hw0 : ∀ i a, 0 ≤ w i a) (hw1 : ∑ i, ∑ a, w i a = 1) :
    ∑ i, lam w i * deficitMix u x i (bdev w i) = 1 - ∑ i, ∑ a, w i a * gain u x i a := by
  simp only [MNR51_lam_deficit u x w hw0, mul_sub, mul_one, Finset.sum_sub_distrib, hw1]

theorem MNR51_gain_le_Reg {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (x : Mixed n)
    (i : Fin m) (a : Fin (n i)) : gain u x i a ≤ Reg u x := by
  have h1 : gain u x i a ≤ regret u x i := le_ciSup (f := fun a => gain u x i a) (Set.finite_range _).bddAbove a
  have h2 : regret u x i ≤ Reg u x := le_ciSup (f := fun i => regret u x i) (Set.finite_range _).bddAbove i
  linarith

theorem MNR51_wgain_le {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (x : Mixed n)
    (w : (i : Fin m) → Fin (n i) → ℝ) (hw0 : ∀ i a, 0 ≤ w i a) (hw1 : ∑ i, ∑ a, w i a = 1) :
    ∑ i, ∑ a, w i a * gain u x i a ≤ Reg u x := by
  calc ∑ i, ∑ a, w i a * gain u x i a ≤ ∑ i, ∑ a, w i a * Reg u x :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun a _ =>
          mul_le_mul_of_nonneg_left (MNR51_gain_le_Reg u x i a) (hw0 i a)))
    _ = Reg u x := by simp only [← Finset.sum_mul, hw1, one_mul]

theorem MNR53_list_fsum {m : ℕ} {n : Fin m → ℕ} {ι : Type*} (S : Finset ι) (gs : List (Gen n))
    (f : ι → Gen n → ℝ) :
    ∑ i ∈ S, (gs.map (f i)).sum = (gs.map fun g => ∑ i ∈ S, f i g).sum := by
  induction gs with
  | nil => simp
  | cons g gs ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

theorem MNR53_list_le {m : ℕ} {n : Fin m → ℕ} (gs : List (Gen n)) (f g : Gen n → ℝ)
    (h : ∀ x ∈ gs, f x ≤ g x) : (gs.map f).sum ≤ (gs.map g).sum := by
  induction gs with
  | nil => simp
  | cons a gs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a (List.mem_cons_self ..)) (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem MNR53_list_nonneg {m : ℕ} {n : Fin m → ℕ} (gs : List (Gen n)) (f : Gen n → ℝ)
    (h : ∀ x ∈ gs, 0 ≤ f x) : 0 ≤ (gs.map f).sum := by
  have := MNR53_list_le gs (fun _ => 0) f h
  simpa using this

theorem MNR53_list_mul {m : ℕ} {n : Fin m → ℕ} (gs : List (Gen n)) (c : ℝ) (f : Gen n → ℝ) :
    (gs.map fun g => c * f g).sum = c * (gs.map f).sum := by
  induction gs with
  | nil => simp
  | cons g gs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem MNR53_gen_lb {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (hu : BoundedGame u)
    (g : Gen n) (hg : GenLegal g) (j : Fin m) (y : Fin (n j) → ℝ) (hy : AGT.IsLottery y)
    (i : Fin m) (hij : i ≠ j) :
    g.A * g.t * g.γ i * (1 - g.col u i j y)
      ≤ ∑ a, (∑ i' ∈ univ.erase j, g.A * g.odds i' *
          AGT.profileProb (Function.update (Function.update g.base i' (g.dev i')) j y) a) * u i a := by
  obtain ⟨hbase, hdev, hγ, htγ, hA⟩ := hg
  have hmix : ∀ i', AGT.IsMixedProfile (Function.update (Function.update g.base i' (g.dev i')) j y) :=
    fun i' => MNR51_update_mixed _ (MNR51_update_mixed _ hbase i' _ (hdev i')) j y hy
  have hpp : ∀ i' a, 0 ≤ AGT.profileProb (Function.update (Function.update g.base i' (g.dev i')) j y) a :=
    fun i' a => Finset.prod_nonneg (fun k _ => ((hmix i') k).1 _)
  have hodds : ∀ i', g.t * g.γ i' ≤ g.odds i' := by
    intro i'
    unfold Gen.odds
    have h1 := (htγ i').1; have h2 := (htγ i').2
    rw [le_div_iff₀ (by linarith)]
    nlinarith only [h1, h2]
  have hodds0 : ∀ i', 0 ≤ g.odds i' := fun i' => le_trans (htγ i').1 (hodds i')
  have hi : i ∈ univ.erase j := Finset.mem_erase.mpr ⟨hij, mem_univ i⟩
  have h1 : ∑ a, (g.A * g.odds i * AGT.profileProb (Function.update (Function.update g.base i (g.dev i)) j y) a) * u i a
      ≤ ∑ a, (∑ i' ∈ univ.erase j, g.A * g.odds i' *
          AGT.profileProb (Function.update (Function.update g.base i' (g.dev i')) j y) a) * u i a := by
    apply Finset.sum_le_sum; intro a _
    apply mul_le_mul_of_nonneg_right _ (hu i a).1
    exact Finset.single_le_sum (f := fun i' => g.A * g.odds i' *
      AGT.profileProb (Function.update (Function.update g.base i' (g.dev i')) j y) a)
      (fun i' _ => mul_nonneg (mul_nonneg hA (hodds0 i')) (hpp i' a)) hi
  refine le_trans ?_ h1
  set E := AGT.expectedPayoff u (Function.update (Function.update g.base i (g.dev i)) j y) i with hE
  have hEeq : ∑ a, (g.A * g.odds i * AGT.profileProb (Function.update (Function.update g.base i (g.dev i)) j y) a) * u i a
      = g.A * g.odds i * E := by
    rw [hE]; unfold AGT.expectedPayoff; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _; ring
  rw [hEeq]
  have hE0 : 0 ≤ E := (MNR51_ep_bounds u hu _ (hmix i) i).1
  have hcol : 1 - g.col u i j y ≤ E := by
    unfold Gen.col deficitMix
    rw [hE, Function.update_comm hij]
    have := (MNR51_ep_bounds u hu _ (MNR51_update_mixed _ hbase j y hy) i).1
    linarith
  have hAt : 0 ≤ g.A * (g.t * g.γ i) := mul_nonneg hA (htγ i).1
  have k1 : g.A * (g.t * g.γ i) * (1 - g.col u i j y) ≤ g.A * (g.t * g.γ i) * E :=
    mul_le_mul_of_nonneg_left hcol hAt
  have k2 : g.A * (g.t * g.γ i) * E ≤ g.A * g.odds i * E :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hodds i) hA) hE0
  nlinarith only [k1, k2]

theorem MNR53_payoff_lb {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (hu : BoundedGame u)
    (x : Mixed n) (gs : List (Gen n)) (hgs : ∀ g ∈ gs, GenLegal g) (hcert : CertLaw x gs)
    (j : Fin m) (y : Fin (n j) → ℝ) (hy : AGT.IsLottery y) (i : Fin m) (hij : i ≠ j) :
    (gs.map fun g => g.A * g.t * g.γ i * (1 - g.col u i j y)).sum
      ≤ AGT.expectedPayoff u (Function.update x j y) i := by
  have hc := hcert.2 j y hy
  set F : Gen n → Tuple n → ℝ := fun g a => ∑ i' ∈ univ.erase j, g.A * g.odds i' *
        AGT.profileProb (Function.update (Function.update g.base i' (g.dev i')) j y) a with hF
  have hstep : ∀ a : Tuple n, (gs.map fun g => F g a).sum * u i a
      ≤ AGT.profileProb (Function.update x j y) a * u i a :=
    fun a => mul_le_mul_of_nonneg_right (hc a) (hu i a).1
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ univ) => hstep a)
  unfold AGT.expectedPayoff
  refine le_trans ?_ hsum
  have hswap : ∑ a, (gs.map fun g => F g a).sum * u i a
      = (gs.map fun g => ∑ a, F g a * u i a).sum := by
    rw [← MNR53_list_fsum]
    apply Finset.sum_congr rfl; intro a _
    rw [mul_comm, ← MNR53_list_mul]
    congr 1; apply List.map_congr_left; intro g _; ring
  rw [hswap]
  exact MNR53_list_le gs _ _ (fun g hg => MNR53_gen_lb u hu g (hgs g hg) j y hy i hij)

theorem MNR53_list_sub {m : ℕ} {n : Fin m → ℕ} (gs : List (Gen n)) (f g : Gen n → ℝ) :
    (gs.map fun x => f x - g x).sum = (gs.map f).sum - (gs.map g).sum := by
  induction gs with
  | nil => simp
  | cons a gs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

set_option maxHeartbeats 4000000 in
theorem solution {m : ℕ} {n : Fin m → ℕ} (hm : 1 ≤ m) (hn : ∀ i, 0 < n i)
    (u : Utility n) (hu : BoundedGame u) (x : Mixed n) (hx : AGT.IsMixedProfile x)
    (lam' : Fin m → ℝ) (b : Mixed n) (hlam : AGT.IsLottery lam') (hb : AGT.IsMixedProfile b)
    (mu : ℝ)
    (h511 : ∀ (j : Fin m) (y : Fin (n j) → ℝ), AGT.IsLottery y →
      ∑ i, lam' i * deficitMix u (Function.update x j y) i (b i) < (scaled u x + mu) / m)
    (gs : List (Gen n)) (hgs : ∀ g ∈ gs, GenLegal g) (hcert : CertLaw x gs)
    (Lcol : ℝ) (hL : 0 ≤ Lcol) (hcol : ColumnBound u gs Lcol)
    (h : Fin m → ℝ) (hh : ∀ i, h i = (gs.map fun g => g.A * g.t * g.γ i).sum)
    (hh0 : ∀ i, 0 ≤ h i) (Y : ℝ) (hY : 0 ≤ Y) (hmh : ∀ i, (m : ℝ) * h i ≤ ∑ j, h j + Y) :
    let H := ∑ i, h i
    let r := (⨆ i, (m : ℝ) * lam' i) - 1
    let Hψ := ∑ i, lam' i * ((m : ℝ) * h i - H)
    ∃ ϑ : ℝ, 0 ≤ ϑ ∧ ϑ ≤ (H + Y + Lcol * H) / m ∧
      (1 + r) * (1 - ϑ) + (H + Hψ) < scaled u x + mu := by
  intro H r Hψ
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hH0 : 0 ≤ H := Finset.sum_nonneg (fun i _ => hh0 i)
  refine ⟨(H + Y + Lcol * H) / m, by positivity, le_rfl, ?_⟩
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun i => (m:ℝ) * lam' i)
  have hr : 1 + r = (m:ℝ) * lam' j := by
    show 1 + ((⨆ i, (m : ℝ) * lam' i) - 1) = _
    rw [← hj]; ring
  have hlmle : ∀ i, (m:ℝ) * lam' i ≤ (m:ℝ) * lam' j := by
    intro i; rw [hj]
    exact le_ciSup (f := fun i => (m:ℝ) * lam' i) (Set.finite_range _).bddAbove i
  have hlm0 := hlam.1
  have hlm1 := hlam.2
  set z := Function.update x j (b j) with hz
  have hzm : AGT.IsMixedProfile z := MNR51_update_mixed x hx j (b j) (hb j)
  have hF := h511 j (b j) (hb j)
  -- split off player j
  rw [← Finset.add_sum_erase univ _ (mem_univ j)] at hF
  have hdj : deficitMix u z j (b j) = 1 := by
    unfold deficitMix; rw [hz]; simp only [Function.update_idem]; ring
  rw [hdj, mul_one] at hF
  -- lower bound of the other deficits
  have hdi : ∀ i ∈ univ.erase j, lam' i * (h i - (gs.map fun g => g.A * g.t * g.γ i * g.col u i j (b j)).sum)
      ≤ lam' i * deficitMix u z i (b i) := by
    intro i hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    apply mul_le_mul_of_nonneg_left _ (hlm0 i)
    have h1 := MNR53_payoff_lb u hu x gs hgs hcert j (b j) (hb j) i hij
    have h2 : (gs.map fun g => g.A * g.t * g.γ i * (1 - g.col u i j (b j))).sum
        = h i - (gs.map fun g => g.A * g.t * g.γ i * g.col u i j (b j)).sum := by
      rw [hh i, ← MNR53_list_sub]; congr 1; apply List.map_congr_left; intro g _; ring
    have h3 : AGT.expectedPayoff u z i ≤ deficitMix u z i (b i) := by
      unfold deficitMix
      have := (MNR51_ep_bounds u hu _ (MNR51_update_mixed z hzm i (b i) (hb i)) i).2
      linarith
    rw [← h2]; exact le_trans h1 h3
  have hsum1 := Finset.sum_le_sum hdi
  -- the column term
  have hcolterm : ∑ i ∈ univ.erase j, lam' i * (gs.map fun g => g.A * g.t * g.γ i * g.col u i j (b j)).sum
      ≤ lam' j * Lcol / m * H := by
    have e1 : ∑ i ∈ univ.erase j, lam' i * (gs.map fun g => g.A * g.t * g.γ i * g.col u i j (b j)).sum
        = (gs.map fun g => ∑ i ∈ univ.erase j, lam' i * (g.A * g.t * g.γ i * g.col u i j (b j))).sum := by
      rw [← MNR53_list_fsum]
      apply Finset.sum_congr rfl; intro i _
      rw [MNR53_list_mul]
    have e2 : H = (gs.map fun g => g.A * g.t).sum := by
      show ∑ i, h i = _
      simp only [hh]
      rw [MNR53_list_fsum]
      congr 1; apply List.map_congr_left; intro g hg
      rw [← Finset.mul_sum, (hgs g hg).2.2.1.2, mul_one]
    rw [e1, e2, ← MNR53_list_mul]
    apply MNR53_list_le; intro g hg
    obtain ⟨hbase, hdev, hγ, htγ, hA⟩ := hgs g hg
    have ht0 : 0 ≤ g.t := by
      have : g.t = ∑ i, g.t * g.γ i := by rw [← Finset.mul_sum, hγ.2, mul_one]
      rw [this]; exact Finset.sum_nonneg (fun i _ => (htγ i).1)
    have hAt : 0 ≤ g.A * g.t := mul_nonneg hA ht0
    have hcolnn : ∀ i, 0 ≤ g.γ i * g.col u i j (b j) := fun i =>
      mul_nonneg (hγ.1 i) (MNR51_deficitMix_nonneg u hu _ (MNR51_update_mixed _ hbase j _ (hb j)) i _ (hdev i))
    have hcb := hcol g hg j (b j) (hb j)
    have k1 : ∑ i ∈ univ.erase j, lam' i * (g.A * g.t * g.γ i * g.col u i j (b j))
        ≤ ∑ i ∈ univ.erase j, (lam' j) * (g.A * g.t * (g.γ i * g.col u i j (b j))) := by
      apply Finset.sum_le_sum; intro i _
      have hli : lam' i ≤ lam' j := le_of_mul_le_mul_left (hlmle i) hmpos
      have := mul_nonneg hAt (hcolnn i)
      have e : g.A * g.t * g.γ i * g.col u i j (b j) = g.A * g.t * (g.γ i * g.col u i j (b j)) := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right hli this
    have k2 : ∑ i ∈ univ.erase j, (lam' j) * (g.A * g.t * (g.γ i * g.col u i j (b j)))
        = lam' j * (g.A * g.t) * ∑ i ∈ univ.erase j, g.γ i * g.col u i j (b j) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    have k3 : lam' j * (g.A * g.t) * ∑ i ∈ univ.erase j, g.γ i * g.col u i j (b j)
        ≤ lam' j * (g.A * g.t) * (Lcol / m) :=
      mul_le_mul_of_nonneg_left (by unfold Gen.col at *; exact hcb) (mul_nonneg (hlm0 j) hAt)
    have e3 : lam' j * Lcol / m * (g.A * g.t) = lam' j * (g.A * g.t) * (Lcol / m) := by ring
    rw [e3]; linarith
  -- assemble
  have hsplit : ∑ i ∈ univ.erase j, lam' i * (h i - (gs.map fun g => g.A * g.t * g.γ i * g.col u i j (b j)).sum)
      = ∑ i ∈ univ.erase j, lam' i * h i
        - ∑ i ∈ univ.erase j, lam' i * (gs.map fun g => g.A * g.t * g.γ i * g.col u i j (b j)).sum := by
    rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
  have hlh : ∑ i ∈ univ.erase j, lam' i * h i = ∑ i, lam' i * h i - lam' j * h j := by
    rw [← Finset.add_sum_erase univ _ (mem_univ j)]; ring
  have hjh : lam' j * h j ≤ lam' j * ((H + Y) / m) := by
    apply mul_le_mul_of_nonneg_left _ (hlm0 j)
    rw [le_div_iff₀ hmpos]; linarith [hmh j]
  have hHψ : H + Hψ = (m:ℝ) * ∑ i, lam' i * h i := by
    show H + ∑ i, lam' i * ((m : ℝ) * h i - H) = _
    have e1 : ∑ i, lam' i * ((m:ℝ) * h i - H) = ∑ i, ((m:ℝ) * (lam' i * h i) - lam' i * H) :=
      Finset.sum_congr rfl (fun i _ => by ring)
    rw [e1, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hlm1]; ring
  have hlow : lam' j + ∑ i, lam' i * h i - lam' j * ((H + Y) / m) - lam' j * Lcol / m * H
      < (scaled u x + mu) / m := by linarith
  rw [lt_div_iff₀ hmpos] at hlow
  rw [hHψ, hr]
  have e : ((m:ℝ) * lam' j) * (1 - (H + Y + Lcol * H) / m) + (m:ℝ) * ∑ i, lam' i * h i
      = (lam' j + ∑ i, lam' i * h i - lam' j * ((H + Y) / m) - lam' j * Lcol / m * H) * m := by
    field_simp; ring
  rw [e]; exact hlow
