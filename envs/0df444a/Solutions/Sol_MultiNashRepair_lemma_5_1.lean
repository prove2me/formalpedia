-- Prove2me | solution 1 for MultiNashRepair.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T00:06:21.19831+00:00
-- url     : https://prove2.me/submissions/58b451c8-db3d-4b55-8588-23b9476a65e5

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

theorem MNR51_weierstrass {ι : Type*} [DecidableEq ι] (S : Finset ι) (t : ι → ℝ)
    (h0 : ∀ k, 0 ≤ t k) (h1 : ∀ k, t k ≤ 1) : 1 - ∑ k ∈ S, t k ≤ ∏ k ∈ S, (1 - t k) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hS : 0 ≤ ∑ k ∈ S, t k := Finset.sum_nonneg (fun k _ => h0 k)
    have := mul_le_mul_of_nonneg_left ih (by linarith [h1 a] : (0:ℝ) ≤ 1 - t a)
    nlinarith only [this, mul_nonneg (h0 a) hS]

theorem MNR51_scaled_eq {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (x : Mixed n) :
    scaled u x = (m:ℝ) * (1 - Reg u x) := rfl

theorem MNR51_cert_scale {m : ℕ} {n : Fin m → ℕ} (gs : List (Gen n)) (P : ℝ) (f : Gen n → ℝ)
    (hf : ∀ g : Gen n, f { g with A := P * g.A } = P * f g) :
    ((gs.map fun g => { g with A := P * g.A }).map f).sum = P * (gs.map f).sum := by
  induction gs with
  | nil => simp
  | cons g gs ih => simp only [List.map_cons, List.sum_cons, ih, hf]; ring

set_option maxHeartbeats 4000000 in
theorem solution {m : ℕ} {n : Fin m → ℕ} (hm : 1 ≤ m) (hn : ∀ i, 0 < n i)
    (u : Utility n) (hu : BoundedGame u) (x : Mixed n) (hx : AGT.IsMixedProfile x)
    (η mu : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hmu : 0 < mu) :
    (∀ z : (j : Fin m) → Fin (n j) → ℝ, LPFeasible z → lpObj u x η z ≤ Reg u x - η * mu / m →
      let Z := ∑ j, ∑ b, z j b
      let P := descentFactor η z
      let xp := descentProfile x η z
      P * ((1 + η * Z) * scaled u x + η * mu) ≤ scaled u xp ∧
        scaled u x + η * mu - η ^ 2 * (scaled u x + mu) ≤
          P * ((1 + η * Z) * scaled u x + η * mu) ∧
        (∀ a : Tuple n, P * AGT.profileProb x a ≤ AGT.profileProb xp a) ∧
        (∀ (j : Fin m) (y : Fin (n j) → ℝ), AGT.IsLottery y → ∀ a : Tuple n,
          P * AGT.profileProb (Function.update x j y) a ≤
            AGT.profileProb (Function.update xp j y) a) ∧
        ∀ gs : List (Gen n), CertLaw x gs →
          CertLaw xp (gs.map fun g => { g with A := P * g.A })) ∧
    (¬ LPPasses u x η mu → ∀ (w : (i : Fin m) → Fin (n i) → ℝ) (α : ℝ),
      DualOptimal u x η w α →
        AGT.IsLottery (lam w) ∧ AGT.IsMixedProfile (bdev w) ∧
        (∀ (j : Fin m) (y : Fin (n j) → ℝ), AGT.IsLottery y →
          Fcol u x w j y < (scaled u x + mu) / m) ∧
        (∀ j, lam w j ≤ Fcol u x w j (bdev w j)) ∧
        ∑ i, lam w i * deficitMix u x i (bdev w i) < (scaled u x + η * mu) / m) := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hReg1 : Reg u x ≤ 1 := by
    apply ciSup_le; intro i
    haveI : Nonempty (Fin (n i)) := ⟨⟨0, hn i⟩⟩
    apply ciSup_le; intro a
    unfold gain DGPNash.NashMap.purePayoff
    have h1 := (MNR51_ep_bounds u hu _ (MNR51_update_mixed x hx i _ (MNR51_ePure_lottery a)) i).2
    have h2 := (MNR51_ep_bounds u hu x hx i).1
    have : (fun k => if k = a then (1:ℝ) else 0) = ePure a := rfl
    rw [this]; linarith
  have hς0 : 0 ≤ scaled u x := by rw [MNR51_scaled_eq]; exact mul_nonneg hmpos.le (by linarith)
  constructor
  · intro z hz hobj
    intro Z P xp
    have hZ0 : 0 ≤ Z := Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun b _ => hz.1 j b))
    have hZ1 : Z ≤ 1 := hz.2
    have hc := MNR51_cfac η hη0.le hη1.le z hz
    have hP0 : 0 ≤ P := Finset.prod_nonneg (fun k _ => (hc k).1)
    have hxpm : AGT.IsMixedProfile xp := MNR51_xp_mixed x hx η hη0.le hη1.le z hz
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- (5.10) first inequality
      set B := 1 - P * ((1 + η * Z) * scaled u x + η * mu) / m with hB
      have hgain : ∀ i (a : Fin (n i)), gain u xp i a ≤ B := by
        intro i a
        have hd := MNR51_deficit_xp u hu x hx η hη0.le hη1.le z hz i a
        have hlp : gain u x i a + η * ∑ j, ∑ b, z j b * repl u x j b i a ≤ lpObj u x η z :=
          le_ciSup (f := fun p : (Σ i : Fin m, Fin (n i)) =>
            gain u x p.1 p.2 + η * ∑ j, ∑ b, z j b * repl u x j b p.1 p.2)
            (Set.finite_range _).bddAbove ⟨i, a⟩
        have hgR := MNR51_gain_le_Reg u x i a
        have hdef : deficit u x i a = 1 - gain u x i a := rfl
        have hdef' : deficit u xp i a = 1 - gain u xp i a := rfl
        have key : ((1 + η * Z) * scaled u x + η * mu) / m
            ≤ (1 + η * Z) * deficit u x i a - η * ∑ j, ∑ b, z j b * repl u x j b i a := by
          rw [MNR51_scaled_eq, div_le_iff₀ hmpos]
          have e : ((1 + η * Z) * (↑m * (1 - Reg u x)) + η * mu) = ((1 + η * Z) * (1 - Reg u x) + η * mu / m) * m := by
            field_simp
          rw [e]
          apply mul_le_mul_of_nonneg_right _ hmpos.le
          have hηZ : 0 ≤ η * Z := mul_nonneg hη0.le hZ0
          rw [hdef]
          nlinarith only [hlp, hobj, hgR, hηZ, mul_le_mul_of_nonneg_left hgR hηZ]
        have := mul_le_mul_of_nonneg_left key hP0
        rw [hB]
        rw [mul_div_assoc] at *
        linarith
      have hReg : Reg u xp ≤ B := by
        apply ciSup_le; intro i
        haveI : Nonempty (Fin (n i)) := ⟨⟨0, hn i⟩⟩
        exact ciSup_le (fun a => hgain i a)
      rw [MNR51_scaled_eq u xp, hB] at *
      have e2 : (m:ℝ) * (1 - (1 - P * ((1 + η * Z) * scaled u x + η * mu) / m))
          = P * ((1 + η * Z) * scaled u x + η * mu) := by field_simp; ring
      nlinarith only [mul_le_mul_of_nonneg_left hReg hmpos.le, e2]
    · -- (5.10) second inequality
      have hW : 1 - η * Z ≤ P := by
        have := MNR51_weierstrass univ (fun j => η * ∑ b, z j b)
          (fun j => mul_nonneg hη0.le (Finset.sum_nonneg (fun b _ => hz.1 j b)))
          (fun j => by linarith [(hc j).1])
        simp only [← Finset.mul_sum] at this
        exact this
      have hX : 0 ≤ (1 + η * Z) * scaled u x + η * mu := by
        have := mul_nonneg hη0.le hZ0
        nlinarith only [this, hς0, hη0, hmu]
      have := mul_le_mul_of_nonneg_right hW hX
      have hZ2 : Z ^ 2 ≤ 1 := by nlinarith only [hZ0, hZ1]
      nlinarith only [this, mul_le_mul_of_nonneg_left hZ2 (mul_nonneg (sq_nonneg η) hς0),
        mul_le_mul_of_nonneg_left hZ1 (mul_nonneg (sq_nonneg η) hmu.le)]
    · intro a
      have h1 := MNR51_pp_xp x hx η hη0.le hη1.le z hz a
      have h2 : 0 ≤ ∑ j, descentFactor η z * η * AGT.profileProb (Function.update x j (z j)) a := by
        apply Finset.sum_nonneg; intro j _
        apply mul_nonneg (mul_nonneg hP0 hη0.le)
        rw [MNR51_pp_update]
        exact mul_nonneg (hz.1 j _) (Finset.prod_nonneg (fun k _ => (hx k).1 _))
      linarith
    · intro j y hy a
      rw [MNR51_pp_update, MNR51_pp_update]
      have hP : P ≤ ∏ k ∈ univ.erase j, (1 - η * ∑ b, z k b) := by
        show descentFactor η z ≤ _
        unfold descentFactor
        rw [← Finset.mul_prod_erase univ _ (mem_univ j)]
        have : 0 ≤ ∏ k ∈ univ.erase j, (1 - η * ∑ b, z k b) :=
          Finset.prod_nonneg (fun k _ => (hc k).1)
        nlinarith only [this, (hc j).2]
      have hprod : (∏ k ∈ univ.erase j, (1 - η * ∑ b, z k b)) * ∏ k ∈ univ.erase j, x k (a k)
          ≤ ∏ k ∈ univ.erase j, xp k (a k) := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_le_prod
        · intro k _; exact mul_nonneg (hc k).1 ((hx k).1 _)
        · intro k _
          show _ ≤ descentProfile x η z k (a k)
          rw [MNR51_xp_apply]
          have := mul_nonneg hη0.le (hz.1 k (a k))
          linarith
      have hX : 0 ≤ ∏ k ∈ univ.erase j, x k (a k) := Finset.prod_nonneg (fun k _ => (hx k).1 _)
      have := mul_le_mul_of_nonneg_right hP hX
      have hy0 := hy.1 (a j)
      nlinarith only [mul_le_mul_of_nonneg_left (le_trans this hprod) hy0]
    · intro gs hgs
      have ha3 : ∀ a : Tuple n, P * AGT.profileProb x a ≤ AGT.profileProb xp a := by
        intro a
        have h1 := MNR51_pp_xp x hx η hη0.le hη1.le z hz a
        have h2 : 0 ≤ ∑ j, descentFactor η z * η * AGT.profileProb (Function.update x j (z j)) a := by
          apply Finset.sum_nonneg; intro j _
          apply mul_nonneg (mul_nonneg hP0 hη0.le)
          rw [MNR51_pp_update]
          exact mul_nonneg (hz.1 j _) (Finset.prod_nonneg (fun k _ => (hx k).1 _))
        linarith
      have ha4 : ∀ (j : Fin m) (y : Fin (n j) → ℝ), AGT.IsLottery y → ∀ a : Tuple n,
          P * AGT.profileProb (Function.update x j y) a ≤ AGT.profileProb (Function.update xp j y) a := by
        intro j y hy a
        rw [MNR51_pp_update, MNR51_pp_update]
        have hP : P ≤ ∏ k ∈ univ.erase j, (1 - η * ∑ b, z k b) := by
          show descentFactor η z ≤ _
          unfold descentFactor
          rw [← Finset.mul_prod_erase univ _ (mem_univ j)]
          have : 0 ≤ ∏ k ∈ univ.erase j, (1 - η * ∑ b, z k b) :=
            Finset.prod_nonneg (fun k _ => (hc k).1)
          nlinarith only [this, (hc j).2]
        have hprod : (∏ k ∈ univ.erase j, (1 - η * ∑ b, z k b)) * ∏ k ∈ univ.erase j, x k (a k)
            ≤ ∏ k ∈ univ.erase j, xp k (a k) := by
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_le_prod
          · intro k _; exact mul_nonneg (hc k).1 ((hx k).1 _)
          · intro k _
            show _ ≤ descentProfile x η z k (a k)
            rw [MNR51_xp_apply]
            have := mul_nonneg hη0.le (hz.1 k (a k))
            linarith
        have hX : 0 ≤ ∏ k ∈ univ.erase j, x k (a k) := Finset.prod_nonneg (fun k _ => (hx k).1 _)
        have := mul_le_mul_of_nonneg_right hP hX
        have hy0 := hy.1 (a j)
        nlinarith only [mul_le_mul_of_nonneg_left (le_trans this hprod) hy0]
      refine ⟨fun a => ?_, fun j y hy a => ?_⟩
      · rw [MNR51_cert_scale gs P _ (fun g => by simp only [Gen.odds]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring)]
        exact le_trans (mul_le_mul_of_nonneg_left (hgs.1 a) hP0) (ha3 a)
      · rw [MNR51_cert_scale gs P _ (fun g => by simp only [Gen.odds]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring)]
        exact le_trans (mul_le_mul_of_nonneg_left (hgs.2 j y hy a) hP0) (ha4 j y hy a)
  · intro hfail w α hw
    obtain ⟨⟨hw0, hw1, hα0, hwrep⟩, hobj⟩ := hw
    have hlp : Reg u x - η * mu / m < lpValue u x η := lt_of_not_ge hfail
    set G := ∑ i, ∑ a, w i a * gain u x i a with hG
    have hGα : Reg u x - η * mu / m < G - α := by
      have : dualObj u x w α = G - α := rfl
      rw [← this, hobj]; exact hlp
    have hGR : G ≤ Reg u x := MNR51_wgain_le u x w hw0 hw1
    have hbdev : AGT.IsMixedProfile (bdev w) := by
      intro i
      by_cases hl : 0 < lam w i
      · have hb : bdev w i = fun a => w i a / lam w i := by simp [bdev, hl]
        rw [hb]
        refine ⟨fun a => div_nonneg (hw0 i a) hl.le, ?_⟩
        rw [← Finset.sum_div]; exact div_self hl.ne'
      · have hb : bdev w i = (fun a : Fin (n i) => if (a : ℕ) = 0 then (1:ℝ) else 0) := by
          simp [bdev, hl]
        rw [hb]
        refine ⟨fun a => by dsimp only; split_ifs <;> norm_num, ?_⟩
        have : (fun a : Fin (n i) => if (a : ℕ) = 0 then (1:ℝ) else 0)
            = fun a => if a = ⟨0, hn i⟩ then 1 else 0 := by
          funext a; congr 1; apply propext; constructor
          · intro h; exact Fin.ext h
          · intro h; rw [h]
        rw [this]; simp
    refine ⟨⟨fun i => Finset.sum_nonneg (fun a _ => hw0 i a), hw1⟩, hbdev, ?_, ?_, ?_⟩
    · intro j y hy
      have hxj := MNR51_update_mixed x hx j y hy
      have hF : Fcol u x w j y = 1 - ∑ i, ∑ a, w i a * gain u (Function.update x j y) i a :=
        MNR51_Fsum u _ w hw0 hw1
      rw [hF]
      have hS : ∀ b : Fin (n j), G - α / η ≤ ∑ i, ∑ a, w i a * gain u (Function.update x j (ePure b)) i a := by
        intro b
        have hrep := hwrep j b
        have e : ∑ i, ∑ a, w i a * gain u (Function.update x j (ePure b)) i a
            = G + ∑ i, ∑ a, w i a * repl u x j b i a := by
          rw [hG, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro i _
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro a _
          unfold repl; ring
        rw [e]
        have : -(α / η) ≤ ∑ i, ∑ a, w i a * repl u x j b i a := by
          rw [neg_le, le_div_iff₀ hη0]; nlinarith only [hrep]
        linarith
      have hlin : ∑ i, ∑ a, w i a * gain u (Function.update x j y) i a
          = ∑ b, y b * ∑ i, ∑ a, w i a * gain u (Function.update x j (ePure b)) i a := by
        simp only [MNR51_gain_lin u x j y hy, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro a _
        apply Finset.sum_congr rfl; intro b _
        ring
      have hge : G - α / η ≤ ∑ b, y b * ∑ i, ∑ a, w i a * gain u (Function.update x j (ePure b)) i a := by
        calc G - α / η = ∑ b, y b * (G - α / η) := by rw [← Finset.sum_mul, hy.2, one_mul]
          _ ≤ _ := Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (hS b) (hy.1 b))
      have hkey : Reg u x - mu / m < G - α / η := by
        have h1 : η * (Reg u x - mu / m) < η * (G - α / η) := by
          have e : η * (G - α / η) = η * G - α := by field_simp
          rw [e]
          have : η * (Reg u x - mu / ↑m) = η * Reg u x - η * mu / m := by ring
          rw [this]
          nlinarith only [hGα, hGR, hη1, hη0]
        exact lt_of_mul_lt_mul_left h1 hη0.le
      rw [MNR51_scaled_eq, lt_div_iff₀ hmpos]
      have : (1 - ∑ b, y b * ∑ i, ∑ a, w i a * gain u (Function.update x j (ePure b)) i a) * m
          < (1 - (Reg u x - mu / m)) * m := by
        apply mul_lt_mul_of_pos_right _ hmpos; rw [hlin] at *; linarith
      rw [hlin]
      have e : (1 - (Reg u x - mu / m)) * m = m * (1 - Reg u x) + mu := by field_simp; ring
      linarith
    · intro j
      have hxj := MNR51_update_mixed x hx j (bdev w j) (hbdev j)
      unfold Fcol
      have hnn : ∀ i ∈ univ, 0 ≤ lam w i * deficitMix u (Function.update x j (bdev w j)) i (bdev w i) :=
        fun i _ => mul_nonneg (Finset.sum_nonneg (fun a _ => hw0 i a))
          (MNR51_deficitMix_nonneg u hu _ hxj i _ (hbdev i))
      have hj := Finset.single_le_sum hnn (mem_univ j)
      have h1 : deficitMix u (Function.update x j (bdev w j)) j (bdev w j) = 1 := by
        unfold deficitMix; simp only [Function.update_idem]; ring
      rw [h1, mul_one] at hj
      exact hj
    · rw [MNR51_Fsum u x w hw0 hw1, ← hG, MNR51_scaled_eq, lt_div_iff₀ hmpos]
      have e : (m:ℝ) * (1 - Reg u x) + η * mu = (1 - Reg u x + η * mu / m) * m := by field_simp
      rw [e]
      apply mul_lt_mul_of_pos_right _ hmpos
      linarith
