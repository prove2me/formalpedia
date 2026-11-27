-- Prove2me | solution 1 for MultiNashRepair.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T00:30:50.080404+00:00
-- url     : https://prove2.me/submissions/10d9ea71-e357-409f-a0a2-39b74be37bf0

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


theorem MNR54_filter_succ {m : ℕ} (k : ℕ) (hk : k < m) :
    (univ.filter (fun j : Fin m => j.val < k + 1))
      = insert ⟨k, hk⟩ (univ.filter (fun j : Fin m => j.val < k)) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
    · right; exact h'
    · left; exact Fin.ext h'
  · rintro (h | h)
    · rw [h]; exact Nat.lt_succ_self k
    · exact Nat.lt_succ_of_lt h

theorem MNR54_filter_lt {m : ℕ} (i : Fin m) :
    univ.filter (fun j : Fin m => j < i) = univ.filter (fun j : Fin m => j.val < i.val) := by
  ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact Fin.lt_def

theorem MNR54_filter_le {m : ℕ} (i : Fin m) :
    univ.filter (fun j : Fin m => j ≤ i) = univ.filter (fun j : Fin m => j.val < i.val + 1) := by
  ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Fin.le_def, Nat.lt_succ_iff]

theorem MNR54_filter_all {m : ℕ} :
    univ.filter (fun j : Fin m => j.val < m) = univ := by
  ext j; simp [j.isLt]

/-- Telescoping for the reverse sweep: `Π_{j<k} (1 - p_j) = 1 - Σ_{j<k} δ_j`. -/
theorem MNR54_rev_tele {m : ℕ} (δ : Fin m → ℝ) (hδ0 : ∀ i, 0 ≤ δ i) (ρ : ℝ) (hρ : 0 < ρ)
    (hδ1 : ∑ i, δ i = 1 - ρ) :
    ∀ k ≤ m, ∏ j ∈ univ.filter (fun j : Fin m => j.val < k), (1 - revProb δ j)
      = 1 - ∑ j ∈ univ.filter (fun j : Fin m => j.val < k), δ j := by
  have hpos : ∀ S : Finset (Fin m), 0 < 1 - ∑ j ∈ S, δ j := by
    intro S
    have : ∑ j ∈ S, δ j ≤ ∑ j, δ j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun j _ _ => hδ0 j)
    linarith
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [MNR54_filter_succ k hk, Finset.prod_insert (by simp), Finset.sum_insert (by simp),
      ih (Nat.le_of_succ_le hk)]
    have hp : revProb δ ⟨k, hk⟩ = δ ⟨k, hk⟩ / (1 - ∑ j ∈ univ.filter (fun j : Fin m => j.val < k), δ j) := by
      unfold revProb; rw [MNR54_filter_lt]
    rw [hp]
    have := hpos (univ.filter (fun j : Fin m => j.val < k))
    field_simp; ring

/-- Telescoping for the forward sweep: `Π_{j<k} (1 - θ_j) = 1 / (1 + Σ_{j<k} e_j)`. -/
theorem MNR54_fwd_tele {m : ℕ} (e : Fin m → ℝ) (he : ∀ i, 0 ≤ e i) :
    ∀ k ≤ m, ∏ j ∈ univ.filter (fun j : Fin m => j.val < k), (1 - fwdProb e j)
      = 1 / (1 + ∑ j ∈ univ.filter (fun j : Fin m => j.val < k), e j) := by
  have hpos : ∀ S : Finset (Fin m), 0 < 1 + ∑ j ∈ S, e j := fun S => by
    have := Finset.sum_nonneg (fun j (_ : j ∈ S) => he j); linarith
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [MNR54_filter_succ k hk, Finset.prod_insert (by simp), Finset.sum_insert (by simp),
      ih (Nat.le_of_succ_le hk)]
    have hp : fwdProb e ⟨k, hk⟩ = e ⟨k, hk⟩ / (1 + (e ⟨k, hk⟩ + ∑ j ∈ univ.filter (fun j : Fin m => j.val < k), e j)) := by
      unfold fwdProb
      rw [MNR54_filter_le]
      simp only [Fin.val_mk]
      rw [MNR54_filter_succ k hk, Finset.sum_insert (by simp)]
    rw [hp]
    have h1 := hpos (univ.filter (fun j : Fin m => j.val < k))
    have h2 : 0 < 1 + (e ⟨k, hk⟩ + ∑ j ∈ univ.filter (fun j : Fin m => j.val < k), e j) := by
      linarith [he ⟨k, hk⟩]
    field_simp; ring

theorem MNR54_pp_self {m : ℕ} {n : Fin m → ℕ} (x : Mixed n) (i : Fin m) (s : Tuple n) :
    AGT.profileProb x s = x i (s i) * ∏ k ∈ univ.erase i, x k (s k) := by
  have := MNR51_pp_update x i (x i) s
  rwa [Function.update_eq_self] at this

theorem MNR54_pp_update2 {m : ℕ} {n : Fin m → ℕ} (x : Mixed n) (i j : Fin m) (hij : i ≠ j)
    (v : Fin (n i) → ℝ) (w : Fin (n j) → ℝ) (s : Tuple n) :
    AGT.profileProb (Function.update (Function.update x i v) j w) s
      = v (s i) * w (s j) * ∏ l ∈ (univ.erase i).erase j, x l (s l) := by
  rw [MNR51_pp_update]
  have hi : i ∈ univ.erase j := Finset.mem_erase.mpr ⟨hij, mem_univ i⟩
  rw [← Finset.mul_prod_erase _ _ hi]
  rw [Function.update_self, Finset.erase_right_comm]
  have : ∏ l ∈ (univ.erase i).erase j, Function.update x i v l (s l) = ∏ l ∈ (univ.erase i).erase j, x l (s l) := by
    apply Finset.prod_congr rfl; intro l hl
    rw [Function.update_of_ne (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl))]
  rw [this]; ring

theorem MNR54_pp_update1' {m : ℕ} {n : Fin m → ℕ} (x : Mixed n) (i j : Fin m) (hij : i ≠ j)
    (w : Fin (n j) → ℝ) (s : Tuple n) :
    AGT.profileProb (Function.update x j w) s
      = x i (s i) * w (s j) * ∏ l ∈ (univ.erase i).erase j, x l (s l) := by
  have := MNR54_pp_update2 x i j hij (x i) w s
  rwa [Function.update_eq_self] at this

theorem MNR54_actY_apply {m : ℕ} {n : Fin m → ℕ} (x b : Mixed n) (t : ℝ) (γ : Fin m → ℝ)
    (k : Fin m) (c : Fin (n k)) :
    actY x b t γ k c = (1 - t * γ k) * x k c + t * γ k * b k c := by
  simp [actY]

theorem MNR54_rev_apply {m : ℕ} {n : Fin m → ℕ} (y : Mixed n) (δ : Fin m → ℝ)
    (arev : (i : Fin m) → Fin (n i)) (k : Fin m) (c : Fin (n k)) :
    revSweep y δ arev k c = (1 - revProb δ k) * y k c + revProb δ k * ePure (arev k) c := by
  simp [revSweep]

theorem MNR54_ePure_nonneg {m : ℕ} {n : Fin m → ℕ} {j : Fin m} (a c : Fin (n j)) :
    0 ≤ (ePure a) c := (MNR51_ePure_lottery a).1 c

theorem MNR54_rev_facts {m : ℕ} (δ : Fin m → ℝ) (hδ0 : ∀ i, 0 ≤ δ i) (ρ : ℝ) (hρ : 0 < ρ)
    (hδ1 : ∑ i, δ i = 1 - ρ) :
    (∀ k, 0 ≤ revProb δ k ∧ revProb δ k < 1) ∧
    (∀ k, 0 ≤ δ k / (1 - ∑ j ∈ univ.filter (· ≤ k), δ j)) ∧
    (∀ k, (1 - revProb δ k) * (δ k / (1 - ∑ j ∈ univ.filter (· ≤ k), δ j)) = revProb δ k) ∧
    (∏ k, (1 - revProb δ k) = ρ) ∧
    (∀ i, revProb δ i * ∏ j ∈ univ.filter (· < i), (1 - revProb δ j) = δ i) := by
  have hle : ∀ S : Finset (Fin m), ∑ j ∈ S, δ j ≤ 1 - ρ := fun S => by
    rw [← hδ1]; exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun j _ _ => hδ0 j)
  -- P_{k-1} - δ_k = P_k ≥ ρ
  have hsplit : ∀ k : Fin m, ∑ j ∈ univ.filter (· ≤ k), δ j = δ k + ∑ j ∈ univ.filter (· < k), δ j := by
    intro k
    have : univ.filter (· ≤ k) = insert k (univ.filter (· < k)) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h; rcases lt_or_eq_of_le h with h' | h'
        · right; exact h'
        · left; exact h'
      · rintro (h | h)
        · rw [h]
        · exact le_of_lt h
    rw [this, Finset.sum_insert (by simp)]
  have hPk : ∀ k : Fin m, ρ ≤ 1 - ∑ j ∈ univ.filter (· ≤ k), δ j := fun k => by linarith [hle (univ.filter (· ≤ k))]
  have hPk1 : ∀ k : Fin m, ρ + δ k ≤ 1 - ∑ j ∈ univ.filter (· < k), δ j := fun k => by
    have := hPk k; rw [hsplit k] at this; linarith
  have hp : ∀ k, revProb δ k = δ k / (1 - ∑ j ∈ univ.filter (· < k), δ j) := fun k => rfl
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_, ?_, fun i => ?_⟩
  · have h1 := hPk1 k
    have hden : 0 < 1 - ∑ j ∈ univ.filter (· < k), δ j := by linarith [hδ0 k]
    rw [hp]
    constructor
    · exact div_nonneg (hδ0 k) hden.le
    · rw [div_lt_one hden]; linarith
  · exact div_nonneg (hδ0 k) (by linarith [hPk k])
  · have h1 := hPk1 k
    have hden : 0 < 1 - ∑ j ∈ univ.filter (· < k), δ j := by linarith [hδ0 k]
    have hden2 : 0 < 1 - ∑ j ∈ univ.filter (· ≤ k), δ j := by linarith [hPk k]
    rw [hsplit k] at hden2
    rw [hp, hsplit k]
    field_simp
    ring
  · have := MNR54_rev_tele δ hδ0 ρ hρ hδ1 m le_rfl
    rw [MNR54_filter_all] at this
    rw [this, hδ1]; ring
  · have := MNR54_rev_tele δ hδ0 ρ hρ hδ1 i.val (le_of_lt i.isLt)
    rw [← MNR54_filter_lt] at this
    rw [this, hp]
    have h1 := hPk1 i
    have hden : 0 < 1 - ∑ j ∈ univ.filter (· < i), δ j := by linarith [hδ0 i]
    field_simp

set_option maxHeartbeats 2000000 in
theorem MNR54_pp_xt {m : ℕ} {n : Fin m → ℕ} (x b : Mixed n) (hx : AGT.IsMixedProfile x)
    (hb : AGT.IsMixedProfile b) (γ : Fin m → ℝ) (t : ℝ) (htγ : ∀ i, 0 ≤ t * γ i ∧ t * γ i < 1)
    (δ : Fin m → ℝ) (hδ0 : ∀ i, 0 ≤ δ i) (ρ : ℝ) (hρ : 0 < ρ) (hδ1 : ∑ i, δ i = 1 - ρ)
    (arev : (i : Fin m) → Fin (n i)) (i : Fin m) (s : Tuple n) :
    δ i * AGT.profileProb (Function.update (fun j => if j < i then actY x b t γ j
        else revSweep (actY x b t γ) δ arev j) i (ePure (arev i))) s
      + (ρ * ∏ k, (1 - t * γ k)) * (AGT.profileProb x s
        + t * γ i / (1 - t * γ i) * AGT.profileProb (Function.update x i (b i)) s
        + ∑ j ∈ univ.erase i, (t * γ j / (1 - t * γ j) * AGT.profileProb (Function.update x j (b j)) s
            + δ j / (1 - ∑ l ∈ univ.filter (· ≤ j), δ l) * AGT.profileProb (Function.update x j (ePure (arev j))) s)
        + t * γ i / (1 - t * γ i) * ∑ j ∈ univ.erase i,
            (t * γ j / (1 - t * γ j) * AGT.profileProb (Function.update (Function.update x i (b i)) j (b j)) s
            + δ j / (1 - ∑ l ∈ univ.filter (· ≤ j), δ l) *
                AGT.profileProb (Function.update (Function.update x i (b i)) j (ePure (arev j))) s))
      ≤ AGT.profileProb (revSweep (actY x b t γ) δ arev) s := by
  obtain ⟨hp01, hω0, hpω, hprodρ, hpP⟩ := MNR54_rev_facts δ hδ0 ρ hρ hδ1
  set p := revProb δ with hpdef
  set ω : Fin m → ℝ := fun k => δ k / (1 - ∑ l ∈ univ.filter (· ≤ k), δ l) with hωdef
  set α : Fin m → ℝ := fun k => t * γ k / (1 - t * γ k) with hαdef
  have hα0 : ∀ k, 0 ≤ α k := fun k => div_nonneg (htγ k).1 (by linarith [(htγ k).2])
  have hαe : ∀ k, (1 - t * γ k) * α k = t * γ k := fun k => by
    simp only [hαdef]; field_simp [show (1 - t * γ k) ≠ 0 by linarith [(htγ k).2]]
  set y := actY x b t γ with hy
  set xt := revSweep y δ arev with hxtdef
  have hxt : ∀ k c, xt k c = (1 - p k) * ((1 - t * γ k) * x k c + t * γ k * b k c)
      + p k * ePure (arev k) c := by
    intro k c; rw [hxtdef, MNR54_rev_apply, hy, MNR54_actY_apply]
  have hyc : ∀ k c, y k c = (1 - t * γ k) * x k c + t * γ k * b k c := fun k c => by
    rw [hy, MNR54_actY_apply]
  have hx0 : ∀ k c, 0 ≤ x k c := fun k c => (hx k).1 c
  have hb0 : ∀ k c, 0 ≤ b k c := fun k c => (hb k).1 c
  have he0 : ∀ k c, 0 ≤ ePure (arev k) c := fun k c => MNR54_ePure_nonneg _ c
  have hy0 : ∀ k c, 0 ≤ y k c := fun k c => by
    rw [hyc]; exact add_nonneg (mul_nonneg (by linarith [(htγ k).2]) (hx0 k c)) (mul_nonneg (htγ k).1 (hb0 k c))
  have hxt0 : ∀ k c, 0 ≤ xt k c := fun k c => by
    rw [hxt]; exact add_nonneg (mul_nonneg (by linarith [(hp01 k).2]) (by rw [← hyc]; exact hy0 k c))
      (mul_nonneg (hp01 k).1 (he0 k c))
  rw [MNR54_pp_self xt i s]
  set R := ∏ k ∈ univ.erase i, xt k (s k) with hR
  -- Part A: the reverse best-response event
  set wrev : Mixed n := fun j => if j < i then y j else xt j with hwrev
  have hA : (∏ k ∈ univ.filter (· < i), (1 - p k)) * ∏ k ∈ univ.erase i, wrev k (s k) ≤ R := by
    have e1 : ∏ k ∈ univ.filter (· < i), (1 - p k)
        = ∏ k ∈ univ.erase i, (if k < i then 1 - p k else 1) := by
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
      congr 1; ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
      constructor
      · intro h; exact ⟨ne_of_lt h, h⟩
      · intro h; exact h.2
    rw [e1, ← Finset.prod_mul_distrib, hR]
    apply Finset.prod_le_prod
    · intro k _
      split_ifs with hk
      · exact mul_nonneg (by linarith [(hp01 k).2]) (by simp only [hwrev, if_pos hk]; exact hy0 k _)
      · simp only [hwrev, if_neg hk, one_mul]; exact hxt0 k _
    · intro k _
      split_ifs with hk
      · simp only [hwrev, if_pos hk]
        rw [hxt, ← hyc]
        have := mul_nonneg (hp01 k).1 (he0 k (s k))
        linarith
      · simp only [hwrev, if_neg hk, one_mul]; exact le_rfl
  have hAterm : δ i * AGT.profileProb (Function.update wrev i (ePure (arev i))) s
      ≤ p i * ePure (arev i) (s i) * R := by
    rw [MNR51_pp_update, ← hpP i]
    have := mul_le_mul_of_nonneg_left hA (mul_nonneg (hp01 i).1 (he0 i (s i)))
    nlinarith only [this]
  -- Part B: the base and single-change events
  set Bk : Fin m → ℝ := fun k => α k * b k (s k) + ω k * ePure (arev k) (s k) with hBk
  have hBk0 : ∀ k, 0 ≤ Bk k := fun k =>
    add_nonneg (mul_nonneg (hα0 k) (hb0 k _)) (mul_nonneg (hω0 k) (he0 k _))
  have hB : (∏ k ∈ univ.erase i, ((1 - p k) * (1 - t * γ k)))
      * ∏ k ∈ univ.erase i, (x k (s k) + Bk k) ≤ R := by
    rw [← Finset.prod_mul_distrib, hR]
    apply Finset.prod_le_prod
    · intro k _
      exact mul_nonneg (mul_nonneg (by linarith [(hp01 k).2]) (by linarith [(htγ k).2]))
        (add_nonneg (hx0 k _) (hBk0 k))
    · intro k _
      rw [hxt]
      simp only [hBk]
      have h1 : (1 - p k) * (1 - t * γ k) * (α k * b k (s k)) = (1 - p k) * (t * γ k * b k (s k)) := by
        linear_combination ((1 - p k) * b k (s k)) * hαe k
      have h2 : (1 - p k) * (1 - t * γ k) * (ω k * ePure (arev k) (s k))
          = (1 - t * γ k) * p k * ePure (arev k) (s k) := by
        have hpω' : (1 - p k) * ω k = p k := hpω k
        linear_combination ((1 - t * γ k) * ePure (arev k) (s k)) * hpω'
      have h3 : (1 - t * γ k) * p k * ePure (arev k) (s k) ≤ p k * ePure (arev k) (s k) := by
        have := mul_nonneg (htγ k).1 (mul_nonneg (hp01 k).1 (he0 k (s k)))
        nlinarith only [this]
      nlinarith only [h1, h2, h3]
  have hexp := MNR51_prod_expand (univ.erase i) (fun k => x k (s k)) Bk (fun k => hx0 k _) hBk0
  have hCraw : (1 - p i) * (1 - t * γ i) * ∏ k ∈ univ.erase i, ((1 - p k) * (1 - t * γ k))
      = ρ * ∏ k, (1 - t * γ k) := by
    have := Finset.mul_prod_erase univ (fun k => (1 - p k) * (1 - t * γ k)) (mem_univ i)
    rw [this, Finset.prod_mul_distrib, hprodρ]
  have hCraw0 : 0 ≤ ρ * ∏ k, (1 - t * γ k) :=
    mul_nonneg hρ.le (Finset.prod_nonneg (fun k _ => by linarith [(htγ k).2]))
  have hyi : y i (s i) = (1 - t * γ i) * (x i (s i) + α i * b i (s i)) := by
    rw [hyc]; rw [mul_add, ← mul_assoc, hαe i]
  set P0v := ∏ k ∈ univ.erase i, x k (s k) with hP0v
  set S1v := ∑ j ∈ univ.erase i, Bk j * ∏ l ∈ (univ.erase i).erase j, x l (s l) with hS1v
  have hBterm : (ρ * ∏ k, (1 - t * γ k)) * ((x i (s i) + α i * b i (s i)) * (P0v + S1v))
      ≤ (1 - p i) * y i (s i) * R := by
    rw [hyi, ← hCraw]
    have hP0 : 0 ≤ ∏ k ∈ univ.erase i, ((1 - p k) * (1 - t * γ k)) :=
      Finset.prod_nonneg (fun k _ => mul_nonneg (by linarith [(hp01 k).2]) (by linarith [(htγ k).2]))
    have hc : 0 ≤ (1 - p i) * (1 - t * γ i) * (x i (s i) + α i * b i (s i)) :=
      mul_nonneg (mul_nonneg (by linarith [(hp01 i).2]) (by linarith [(htγ i).2]))
        (add_nonneg (hx0 i _) (mul_nonneg (hα0 i) (hb0 i _)))
    have k1 := mul_le_mul_of_nonneg_left hexp hP0
    have k2 := le_trans k1 hB
    have k3 := mul_le_mul_of_nonneg_left k2 hc
    nlinarith only [k3]
  -- identify the expansion with the stated profile probabilities
  have hT : AGT.profileProb x s
        + α i * AGT.profileProb (Function.update x i (b i)) s
        + ∑ j ∈ univ.erase i, (α j * AGT.profileProb (Function.update x j (b j)) s
            + ω j * AGT.profileProb (Function.update x j (ePure (arev j))) s)
        + α i * ∑ j ∈ univ.erase i,
            (α j * AGT.profileProb (Function.update (Function.update x i (b i)) j (b j)) s
            + ω j * AGT.profileProb (Function.update (Function.update x i (b i)) j (ePure (arev j))) s)
      = (x i (s i) + α i * b i (s i)) * (P0v + S1v) := by
    rw [MNR54_pp_self x i s, MNR51_pp_update x i (b i) s]
    have e1 : ∀ j ∈ univ.erase i, α j * AGT.profileProb (Function.update x j (b j)) s
            + ω j * AGT.profileProb (Function.update x j (ePure (arev j))) s
          = x i (s i) * (Bk j * ∏ l ∈ (univ.erase i).erase j, x l (s l)) := by
      intro j hj
      have hij : i ≠ j := Ne.symm (Finset.ne_of_mem_erase hj)
      rw [MNR54_pp_update1' x i j hij, MNR54_pp_update1' x i j hij]
      simp only [hBk]; ring
    have e2 : ∀ j ∈ univ.erase i,
            α j * AGT.profileProb (Function.update (Function.update x i (b i)) j (b j)) s
            + ω j * AGT.profileProb (Function.update (Function.update x i (b i)) j (ePure (arev j))) s
          = b i (s i) * (Bk j * ∏ l ∈ (univ.erase i).erase j, x l (s l)) := by
      intro j hj
      have hij : i ≠ j := Ne.symm (Finset.ne_of_mem_erase hj)
      rw [MNR54_pp_update2 x i j hij, MNR54_pp_update2 x i j hij]
      simp only [hBk]; ring
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.mul_sum, ← Finset.mul_sum, ← hS1v]
    ring
  have hsplitxt : xt i (s i) * R = (1 - p i) * y i (s i) * R + p i * ePure (arev i) (s i) * R := by
    rw [hxt, ← hyc]; ring
  rw [hsplitxt, hT]
  linarith

theorem MNR54_deficit_ge_ep {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (hu : BoundedGame u)
    (z : Mixed n) (hz : AGT.IsMixedProfile z) (i : Fin m) (a : Fin (n i)) :
    AGT.expectedPayoff u z i ≤ deficit u z i a := by
  unfold deficit gain DGPNash.NashMap.purePayoff
  have := (MNR51_ep_bounds u hu _ (MNR51_update_mixed z hz i _ (MNR51_ePure_lottery a)) i).2
  have e : (fun k => if k = a then (1:ℝ) else 0) = ePure a := rfl
  rw [e]; linarith

theorem MNR54_deficit_act {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (hu : BoundedGame u)
    (z : Mixed n) (hz : AGT.IsMixedProfile z) (i : Fin m) (bi : Fin (n i) → ℝ)
    (hbi : AGT.IsLottery bi) (a : Fin (n i)) :
    1 - deficitMix u z i bi ≤ deficit u (Function.update z i bi) i a := by
  have h1 := MNR54_deficit_ge_ep u hu _ (MNR51_update_mixed z hz i bi hbi) i a
  have h2 := (MNR51_ep_bounds u hu z hz i).1
  unfold deficitMix
  linarith

theorem MNR54_deficit_rev {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (w : Mixed n) (i : Fin m)
    (e : Fin (n i)) (hBR : ∀ a, DGPNash.NashMap.purePayoff u w i a ≤ DGPNash.NashMap.purePayoff u w i e)
    (a : Fin (n i)) : 1 ≤ deficit u (Function.update w i (ePure e)) i a := by
  unfold deficit gain
  have h1 : DGPNash.NashMap.purePayoff u (Function.update w i (ePure e)) i a
      = DGPNash.NashMap.purePayoff u w i a := by
    unfold DGPNash.NashMap.purePayoff; rw [Function.update_idem]
  have h2 : AGT.expectedPayoff u (Function.update w i (ePure e)) i = DGPNash.NashMap.purePayoff u w i e := rfl
  rw [h1, h2]; linarith [hBR a]

theorem MNR54_deficit_ge_q {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (x : Mixed n) (i : Fin m)
    (a : Fin (n i)) : q u x ≤ deficit u x i a := by
  unfold q deficit; linarith [MNR51_gain_le_Reg u x i a]

/-- The retained-event lower bound with the full odds. -/
theorem MNR54_payoff_lb_odds {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (hu : BoundedGame u)
    (x : Mixed n) (gs : List (Gen n)) (hgs : ∀ g ∈ gs, GenLegal g) (hcert : CertLaw x gs)
    (j : Fin m) (y : Fin (n j) → ℝ) (hy : AGT.IsLottery y) (i : Fin m) (hij : i ≠ j) :
    (gs.map fun g => g.A * g.odds i * (1 - g.col u i j y)).sum
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
  apply MNR53_list_le; intro g hg
  obtain ⟨hbase, hdev, hγ, htγ, hA⟩ := hgs g hg
  have hmix : ∀ i', AGT.IsMixedProfile (Function.update (Function.update g.base i' (g.dev i')) j y) :=
    fun i' => MNR51_update_mixed _ (MNR51_update_mixed _ hbase i' _ (hdev i')) j y hy
  have hpp : ∀ i' a, 0 ≤ AGT.profileProb (Function.update (Function.update g.base i' (g.dev i')) j y) a :=
    fun i' a => Finset.prod_nonneg (fun k _ => ((hmix i') k).1 _)
  have hodds0 : ∀ i', 0 ≤ g.odds i' := fun i' =>
    div_nonneg (htγ i').1 (by linarith [(htγ i').2])
  have hi : i ∈ univ.erase j := Finset.mem_erase.mpr ⟨hij, mem_univ i⟩
  have h1 : ∑ a, (g.A * g.odds i * AGT.profileProb (Function.update (Function.update g.base i (g.dev i)) j y) a) * u i a
      ≤ ∑ a, F g a * u i a := by
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
  have hcol : 1 - g.col u i j y ≤ E := by
    unfold Gen.col deficitMix
    rw [hE, Function.update_comm hij]
    have := (MNR51_ep_bounds u hu _ (MNR51_update_mixed _ hbase j y hy) i).1
    linarith
  exact mul_le_mul_of_nonneg_left hcol (mul_nonneg hA (hodds0 i))

theorem MNR54_xt_mixed {m : ℕ} {n : Fin m → ℕ} (x b : Mixed n) (hx : AGT.IsMixedProfile x)
    (hb : AGT.IsMixedProfile b) (γ : Fin m → ℝ) (t : ℝ) (htγ : ∀ i, 0 ≤ t * γ i ∧ t * γ i < 1)
    (δ : Fin m → ℝ) (hδ0 : ∀ i, 0 ≤ δ i) (ρ : ℝ) (hρ : 0 < ρ) (hδ1 : ∑ i, δ i = 1 - ρ)
    (arev : (i : Fin m) → Fin (n i)) :
    AGT.IsMixedProfile (actY x b t γ) ∧ AGT.IsMixedProfile (revSweep (actY x b t γ) δ arev) := by
  obtain ⟨hp01, -, -, -, -⟩ := MNR54_rev_facts δ hδ0 ρ hρ hδ1
  have hy : AGT.IsMixedProfile (actY x b t γ) := by
    intro k
    refine ⟨fun c => ?_, ?_⟩
    · rw [MNR54_actY_apply]
      exact add_nonneg (mul_nonneg (by linarith [(htγ k).2]) ((hx k).1 c)) (mul_nonneg (htγ k).1 ((hb k).1 c))
    · simp only [MNR54_actY_apply, Finset.sum_add_distrib, ← Finset.mul_sum, (hx k).2, (hb k).2]; ring
  refine ⟨hy, fun k => ⟨fun c => ?_, ?_⟩⟩
  · rw [MNR54_rev_apply]
    exact add_nonneg (mul_nonneg (by linarith [(hp01 k).2]) ((hy k).1 c))
      (mul_nonneg (hp01 k).1 (MNR54_ePure_nonneg _ c))
  · simp only [MNR54_rev_apply, Finset.sum_add_distrib, ← Finset.mul_sum, (hy k).2,
      (MNR51_ePure_lottery (arev k)).2]; ring

theorem MNR54_sum_expand {S J : Type*} [Fintype S] (T : Finset J) (δ C αi : ℝ) (f1 f2 f3 : S → ℝ)
    (aj wj : J → ℝ) (g h k l : J → S → ℝ) (D : S → ℝ) :
    ∑ s, (δ * f1 s + C * (f2 s + αi * f3 s + ∑ j ∈ T, (aj j * g j s + wj j * h j s)
        + αi * ∑ j ∈ T, (aj j * k j s + wj j * l j s))) * D s
    = δ * ∑ s, f1 s * D s + C * (∑ s, f2 s * D s + αi * ∑ s, f3 s * D s
        + ∑ j ∈ T, (aj j * ∑ s, g j s * D s + wj j * ∑ s, h j s * D s)
        + αi * ∑ j ∈ T, (aj j * ∑ s, k j s * D s + wj j * ∑ s, l j s * D s)) := by
  have e1 : ∀ s, (δ * f1 s + C * (f2 s + αi * f3 s + ∑ j ∈ T, (aj j * g j s + wj j * h j s)
        + αi * ∑ j ∈ T, (aj j * k j s + wj j * l j s))) * D s
      = δ * (f1 s * D s) + C * (f2 s * D s + αi * (f3 s * D s)
        + ∑ j ∈ T, (aj j * (g j s * D s) + wj j * (h j s * D s))
        + αi * ∑ j ∈ T, (aj j * (k j s * D s) + wj j * (l j s * D s))) := by
    intro s
    have a1 : (∑ j ∈ T, (aj j * g j s + wj j * h j s)) * D s
        = ∑ j ∈ T, (aj j * (g j s * D s) + wj j * (h j s * D s)) := by
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; ring
    have a2 : (∑ j ∈ T, (aj j * k j s + wj j * l j s)) * D s
        = ∑ j ∈ T, (aj j * (k j s * D s) + wj j * (l j s * D s)) := by
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; ring
    rw [← a1, ← a2]; ring
  rw [Finset.sum_congr rfl (fun s _ => e1 s)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_comm (s := (univ : Finset S)) (t := T), Finset.sum_comm (s := (univ : Finset S)) (t := T)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem MNR54_perg {ι : Type*} (T : Finset ι) (Craw Sev K ai wi : ℝ) (aj wj cb ce : ι → ℝ)
    (hSev : Sev = ai + wi + ∑ j ∈ T, (aj j + wj j)) :
    Craw * Sev * K - Craw * K * (ai + wi + ∑ j ∈ T, aj j * cb j + ∑ j ∈ T, wj j * ce j)
      = Craw * ∑ j ∈ T, (aj j * (K * (1 - cb j)) + wj j * (K * (1 - ce j))) := by
  rw [hSev]
  have e : ∑ j ∈ T, (aj j * (K * (1 - cb j)) + wj j * (K * (1 - ce j)))
      = K * (∑ j ∈ T, (aj j + wj j)) - K * (∑ j ∈ T, aj j * cb j + ∑ j ∈ T, wj j * ce j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [e]; ring

theorem MNR54_new_id {ι : Type*} (T : Finset ι) (Craw Sev ai wi d0 : ℝ) (aj wj db de : ι → ℝ)
    (hSev : Sev = ai + wi + ∑ j ∈ T, (aj j + wj j)) :
    Craw * ai * (1 + Sev) - Craw * ai * (d0 + ai + wi + ∑ j ∈ T, aj j * db j + ∑ j ∈ T, wj j * de j)
      = Craw * (ai * (1 - d0) + ai * ∑ j ∈ T, (aj j * (1 - db j) + wj j * (1 - de j))) := by
  rw [hSev]
  have e : ∑ j ∈ T, (aj j * (1 - db j) + wj j * (1 - de j))
      = ∑ j ∈ T, (aj j + wj j) - (∑ j ∈ T, aj j * db j + ∑ j ∈ T, wj j * de j) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [e]; ring

theorem MNR54_list_add {m : ℕ} {n : Fin m → ℕ} (gs : List (Gen n)) (f g : Gen n → ℝ) :
    (gs.map fun x => f x + g x).sum = (gs.map f).sum + (gs.map g).sum := by
  induction gs with
  | nil => simp
  | cons a gs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

set_option maxHeartbeats 4000000 in
theorem MNR54_part1 {m : ℕ} {n : Fin m → ℕ} (hn : ∀ i, 0 < n i)
    (u : Utility n) (hu : BoundedGame u) (x : Mixed n) (hx : AGT.IsMixedProfile x)
    (b : Mixed n) (hb : AGT.IsMixedProfile b) (γ : Fin m → ℝ)
    (t ρ : ℝ) (htγ : ∀ i, 0 ≤ t * γ i ∧ t * γ i < 1) (hρ : 0 < ρ)
    (δ : Fin m → ℝ) (hδ0 : ∀ i, 0 ≤ δ i) (hδ1 : ∑ i, δ i = 1 - ρ)
    (gs : List (Gen n)) (hgs : ∀ g ∈ gs, GenLegal g) (hcert : CertLaw x gs)
    (arev : (i : Fin m) → Fin (n i))
    (hrev : IsRevBR u (actY x b t γ) δ arev) (i : Fin m) :
    let Craw := ρ * ∏ i, (1 - t * γ i)
    let α : Fin m → ℝ := fun i => t * γ i / (1 - t * γ i)
    let ω : Fin m → ℝ := fun i => δ i / (1 - ∑ j ∈ univ.filter (· ≤ i), δ j)
    let Sev := ∑ i, (α i + ω i)
    let d0 : Fin m → ℝ := fun i => deficitMix u x i (b i)
    let dij : (i j : Fin m) → (Fin (n j) → ℝ) → ℝ :=
      fun i j yj => deficitMix u (Function.update x j yj) i (b i)
    let enew : Fin m → ℝ := fun i => Craw * α i * (d0 i + α i + ω i
      + ∑ j ∈ univ.erase i, α j * dij i j (b j)
      + ∑ j ∈ univ.erase i, ω j * dij i j (ePure (arev j)))
    let eold : Fin m → ℝ := fun i => (gs.map fun g => Craw * g.A * g.odds i * (α i + ω i
      + ∑ j ∈ univ.erase i, α j * g.col u i j (b j)
      + ∑ j ∈ univ.erase i, ω j * g.col u i j (ePure (arev j)))).sum
    let oldMass : Fin m → ℝ := fun i => (gs.map fun g => g.A * g.odds i).sum
    Craw * q u x + δ i + Craw * α i * (1 + Sev) + Craw * Sev * oldMass i - enew i
        - eold i ≤ qi u (revSweep (actY x b t γ) δ arev) i := by
  intro Craw α ω Sev d0 dij enew eold oldMass
  obtain ⟨hp01, hω0, -, -, -⟩ := MNR54_rev_facts δ hδ0 ρ hρ hδ1
  obtain ⟨hym, hxtm⟩ := MNR54_xt_mixed x b hx hb γ t htγ δ hδ0 ρ hρ hδ1 arev
  have hα0 : ∀ k, 0 ≤ α k := fun k => div_nonneg (htγ k).1 (by linarith [(htγ k).2])
  have hCraw0 : 0 ≤ Craw := mul_nonneg hρ.le (Finset.prod_nonneg (fun k _ => by linarith [(htγ k).2]))
  -- historical lower bounds
  set L : (j : Fin m) → (Fin (n j) → ℝ) → ℝ := fun j w =>
    (gs.map fun g => g.A * g.odds i * (1 - g.col u i j w)).sum with hL
  -- the bound B
  set B := δ i + Craw * (q u x + α i * (1 - d0 i)
      + ∑ j ∈ univ.erase i, (α j * L j (b j) + ω j * L j (ePure (arev j)))
      + α i * ∑ j ∈ univ.erase i, (α j * (1 - dij i j (b j)) + ω j * (1 - dij i j (ePure (arev j)))))
    with hB
  have key : ∀ a, B ≤ deficit u (revSweep (actY x b t γ) δ arev) i a := by
    intro a
    set D : Tuple n → ℝ := fun s => 1 + u i s - u i (Function.update s i a) with hD
    have hD0 : ∀ s, 0 ≤ D s := by
      intro s; simp only [hD]
      have h1 := (hu i s).1; have h2 := (hu i (Function.update s i a)).2
      linarith
    have M : ∀ z : Mixed n, AGT.IsMixedProfile z → deficit u z i a = ∑ s, AGT.profileProb z s * D s :=
      fun z hz => MNR51_deficit_eq u z hz i a
    rw [M _ hxtm]
    have hpt := fun s => MNR54_pp_xt x b hx hb γ t htγ δ hδ0 ρ hρ hδ1 arev i s
    refine le_trans ?_ (Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_right (hpt s) (hD0 s)))
    set wrev : Mixed n := fun j => if j < i then actY x b t γ j else revSweep (actY x b t γ) δ arev j
      with hwrev
    have hwrevm : AGT.IsMixedProfile wrev := by
      intro j; simp only [hwrev]; split_ifs
      · exact hym j
      · exact hxtm j
    refine le_trans ?_ (le_of_eq (MNR54_sum_expand (univ.erase i) (δ i) Craw (α i)
      (fun s => AGT.profileProb (Function.update wrev i (ePure (arev i))) s)
      (fun s => AGT.profileProb x s)
      (fun s => AGT.profileProb (Function.update x i (b i)) s) α ω
      (fun j s => AGT.profileProb (Function.update x j (b j)) s)
      (fun j s => AGT.profileProb (Function.update x j (ePure (arev j))) s)
      (fun j s => AGT.profileProb (Function.update (Function.update x i (b i)) j (b j)) s)
      (fun j s => AGT.profileProb (Function.update (Function.update x i (b i)) j (ePure (arev j))) s)
      D).symm)
    have m1 : 1 ≤ ∑ s, AGT.profileProb (Function.update wrev i (ePure (arev i))) s * D s := by
      rw [← M _ (MNR51_update_mixed _ hwrevm i _ (MNR51_ePure_lottery _))]
      exact MNR54_deficit_rev u wrev i (arev i) (fun a' => hrev i a') a
    have m2 : q u x ≤ ∑ s, AGT.profileProb x s * D s := by
      rw [← M _ hx]; exact MNR54_deficit_ge_q u x i a
    have m3 : 1 - d0 i ≤ ∑ s, AGT.profileProb (Function.update x i (b i)) s * D s := by
      rw [← M _ (MNR51_update_mixed _ hx i _ (hb i))]
      exact MNR54_deficit_act u hu x hx i (b i) (hb i) a
    have m4 : ∀ j ∈ univ.erase i, ∀ w : Fin (n j) → ℝ, AGT.IsLottery w →
        L j w ≤ ∑ s, AGT.profileProb (Function.update x j w) s * D s := by
      intro j hj w hw
      have hij : i ≠ j := Ne.symm (Finset.ne_of_mem_erase hj)
      have hm := MNR51_update_mixed _ hx j w hw
      rw [← M _ hm]
      exact le_trans (MNR54_payoff_lb_odds u hu x gs hgs hcert j w hw i hij)
        (MNR54_deficit_ge_ep u hu _ hm i a)
    have m5 : ∀ j ∈ univ.erase i, ∀ w : Fin (n j) → ℝ, AGT.IsLottery w →
        1 - dij i j w ≤ ∑ s, AGT.profileProb (Function.update (Function.update x i (b i)) j w) s * D s := by
      intro j hj w hw
      have hij : i ≠ j := Ne.symm (Finset.ne_of_mem_erase hj)
      have hm1 := MNR51_update_mixed _ hx j w hw
      rw [Function.update_comm hij, ← M _ (MNR51_update_mixed _ hm1 i _ (hb i))]
      exact MNR54_deficit_act u hu _ hm1 i (b i) (hb i) a
    rw [hB]
    have hb' : ∀ j, AGT.IsLottery (b j) := hb
    have he' : ∀ j, AGT.IsLottery (ePure (arev j)) := fun j => MNR51_ePure_lottery _
    have s1 : ∑ j ∈ univ.erase i, (α j * L j (b j) + ω j * L j (ePure (arev j)))
        ≤ ∑ j ∈ univ.erase i, (α j * ∑ s, AGT.profileProb (Function.update x j (b j)) s * D s
            + ω j * ∑ s, AGT.profileProb (Function.update x j (ePure (arev j))) s * D s) :=
      Finset.sum_le_sum (fun j hj => add_le_add
        (mul_le_mul_of_nonneg_left (m4 j hj _ (hb' j)) (hα0 j))
        (mul_le_mul_of_nonneg_left (m4 j hj _ (he' j)) (hω0 j)))
    have s2 : ∑ j ∈ univ.erase i, (α j * (1 - dij i j (b j)) + ω j * (1 - dij i j (ePure (arev j))))
        ≤ ∑ j ∈ univ.erase i, (α j * ∑ s, AGT.profileProb (Function.update (Function.update x i (b i)) j (b j)) s * D s
            + ω j * ∑ s, AGT.profileProb (Function.update (Function.update x i (b i)) j (ePure (arev j))) s * D s) :=
      Finset.sum_le_sum (fun j hj => add_le_add
        (mul_le_mul_of_nonneg_left (m5 j hj _ (hb' j)) (hα0 j))
        (mul_le_mul_of_nonneg_left (m5 j hj _ (he' j)) (hω0 j)))
    have t1 := mul_le_mul_of_nonneg_left m1 (hδ0 i)
    have t3 := mul_le_mul_of_nonneg_left m3 (hα0 i)
    have t5 := mul_le_mul_of_nonneg_left s2 (hα0 i)
    have tot : q u x + α i * (1 - d0 i)
        + ∑ j ∈ univ.erase i, (α j * L j (b j) + ω j * L j (ePure (arev j)))
        + α i * ∑ j ∈ univ.erase i, (α j * (1 - dij i j (b j)) + ω j * (1 - dij i j (ePure (arev j))))
        ≤ ∑ s, AGT.profileProb x s * D s + α i * ∑ s, AGT.profileProb (Function.update x i (b i)) s * D s
          + ∑ j ∈ univ.erase i, (α j * ∑ s, AGT.profileProb (Function.update x j (b j)) s * D s
            + ω j * ∑ s, AGT.profileProb (Function.update x j (ePure (arev j))) s * D s)
          + α i * ∑ j ∈ univ.erase i, (α j * ∑ s, AGT.profileProb (Function.update (Function.update x i (b i)) j (b j)) s * D s
            + ω j * ∑ s, AGT.profileProb (Function.update (Function.update x i (b i)) j (ePure (arev j))) s * D s) := by
      linarith
    have := mul_le_mul_of_nonneg_left tot hCraw0
    linarith
  -- from deficits to q_i
  have hqi : B ≤ qi u (revSweep (actY x b t γ) δ arev) i := by
    haveI : Nonempty (Fin (n i)) := ⟨⟨0, hn i⟩⟩
    unfold qi regret
    have : (⨆ a, gain u (revSweep (actY x b t γ) δ arev) i a) ≤ 1 - B := by
      apply ciSup_le; intro a
      have := key a; unfold deficit at this; linarith
    linarith
  refine le_trans (le_of_eq ?_) hqi
  -- algebraic identification of the bound
  have hSev : Sev = α i + ω i + ∑ j ∈ univ.erase i, (α j + ω j) := by
    show ∑ k, (α k + ω k) = _
    rw [← Finset.add_sum_erase univ _ (mem_univ i)]
  have hI : Craw * Sev * oldMass i - eold i
      = Craw * ∑ j ∈ univ.erase i, (α j * L j (b j) + ω j * L j (ePure (arev j))) := by
    show Craw * Sev * (gs.map fun g => g.A * g.odds i).sum
      - (gs.map fun g => Craw * g.A * g.odds i * (α i + ω i
        + ∑ j ∈ univ.erase i, α j * g.col u i j (b j)
        + ∑ j ∈ univ.erase i, ω j * g.col u i j (ePure (arev j)))).sum = _
    rw [← MNR53_list_mul, ← MNR53_list_sub]
    have e1 : ∀ g : Gen n, Craw * Sev * (g.A * g.odds i) - Craw * g.A * g.odds i * (α i + ω i
        + ∑ j ∈ univ.erase i, α j * g.col u i j (b j)
        + ∑ j ∈ univ.erase i, ω j * g.col u i j (ePure (arev j)))
        = Craw * ∑ j ∈ univ.erase i, (α j * (g.A * g.odds i * (1 - g.col u i j (b j)))
            + ω j * (g.A * g.odds i * (1 - g.col u i j (ePure (arev j))))) := by
      intro g
      have := MNR54_perg (univ.erase i) Craw Sev (g.A * g.odds i) (α i) (ω i) α ω
        (fun j => g.col u i j (b j)) (fun j => g.col u i j (ePure (arev j))) hSev
      rw [← this]; ring
    rw [List.map_congr_left (fun g _ => e1 g), MNR53_list_mul, ← MNR53_list_fsum]
    congr 1; apply Finset.sum_congr rfl; intro j _
    simp only [hL]
    rw [← MNR53_list_mul, ← MNR53_list_mul]
    exact MNR54_list_add gs _ _
  have hII : Craw * α i * (1 + Sev) - enew i
      = Craw * (α i * (1 - d0 i) + α i * ∑ j ∈ univ.erase i, (α j * (1 - dij i j (b j))
          + ω j * (1 - dij i j (ePure (arev j))))) := by
    show Craw * α i * (1 + Sev) - Craw * α i * (d0 i + α i + ω i
      + ∑ j ∈ univ.erase i, α j * dij i j (b j)
      + ∑ j ∈ univ.erase i, ω j * dij i j (ePure (arev j))) = _
    exact MNR54_new_id (univ.erase i) Craw Sev (α i) (ω i) (d0 i) α ω
      (fun j => dij i j (b j)) (fun j => dij i j (ePure (arev j))) hSev
  rw [hB]
  linarith [hI, hII]

theorem MNR54_fwd_facts {m : ℕ} (e : Fin m → ℝ) (he : ∀ i, 0 ≤ e i) :
    (∀ k, 0 ≤ fwdProb e k ∧ fwdProb e k < 1) ∧
    (∏ k, (1 - fwdProb e k) = 1 / (1 + ∑ k, e k)) ∧
    (∀ i, fwdProb e i * ∏ k ∈ univ.filter (fun k => ¬ k ≤ i), (1 - fwdProb e k)
        = e i / (1 + ∑ k, e k)) := by
  have hpos : ∀ S : Finset (Fin m), 0 < 1 + ∑ j ∈ S, e j := fun S => by
    have := Finset.sum_nonneg (fun j (_ : j ∈ S) => he j); linarith
  have hθ : ∀ k, fwdProb e k = e k / (1 + ∑ j ∈ univ.filter (· ≤ k), e j) := fun k => rfl
  have hall : ∏ k, (1 - fwdProb e k) = 1 / (1 + ∑ k, e k) := by
    have := MNR54_fwd_tele e he m le_rfl
    rw [MNR54_filter_all] at this; exact this
  refine ⟨fun k => ?_, hall, fun i => ?_⟩
  · rw [hθ]
    have h1 : e k ≤ ∑ j ∈ univ.filter (· ≤ k), e j :=
      Finset.single_le_sum (f := e) (fun j _ => he j) (by simp)
    have h2 := hpos (univ.filter (· ≤ k))
    exact ⟨div_nonneg (he k) h2.le, by rw [div_lt_one h2]; linarith⟩
  · have hle : ∏ k ∈ univ.filter (· ≤ i), (1 - fwdProb e k) = 1 / (1 + ∑ j ∈ univ.filter (· ≤ i), e j) := by
      have := MNR54_fwd_tele e he (i.val + 1) i.isLt
      rw [← MNR54_filter_le] at this; exact this
    have hsplit := Finset.prod_filter_mul_prod_filter_not univ (fun k : Fin m => k ≤ i)
      (fun k => 1 - fwdProb e k)
    rw [hall, hle] at hsplit
    have h2 := hpos (univ.filter (· ≤ i))
    have h3 := hpos univ
    have hR : ∏ k ∈ univ.filter (fun k => ¬ k ≤ i), (1 - fwdProb e k)
        = (1 + ∑ j ∈ univ.filter (· ≤ i), e j) / (1 + ∑ k, e k) := by
      field_simp at hsplit ⊢; linarith
    rw [hR, hθ]; field_simp

theorem MNR54_fwd_apply {m : ℕ} {n : Fin m → ℕ} (xt : Mixed n) (e : Fin m → ℝ)
    (acor : (i : Fin m) → Fin (n i)) (k : Fin m) (c : Fin (n k)) :
    fwdSweep xt e acor k c = (1 - fwdProb e k) * xt k c + fwdProb e k * ePure (acor k) c := by
  simp [fwdSweep]

/-- The forward correction: `d_{i,a}(x⁺) ≥ (q_i(x̃) + e_i)/(1 + E)`. -/
theorem MNR54_fwd_deficit {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (hu : BoundedGame u)
    (xt : Mixed n) (hxt : AGT.IsMixedProfile xt) (e : Fin m → ℝ) (he : ∀ i, 0 ≤ e i)
    (acor : (i : Fin m) → Fin (n i)) (hfwd : IsFwdBR u xt e acor) (i : Fin m) (a : Fin (n i))
    (hn : ∀ i, 0 < n i) :
    (qi u xt i + e i) / (1 + ∑ k, e k) ≤ deficit u (fwdSweep xt e acor) i a := by
  obtain ⟨hθ01, hall, hgt⟩ := MNR54_fwd_facts e he
  set θ := fwdProb e with hθdef
  set xp := fwdSweep xt e acor with hxpdef
  have hxt0 : ∀ k c, 0 ≤ xt k c := fun k c => (hxt k).1 c
  have he0 : ∀ k c, 0 ≤ ePure (acor k) c := fun k c => MNR54_ePure_nonneg _ c
  have hxpm : AGT.IsMixedProfile xp := by
    intro k; refine ⟨fun c => ?_, ?_⟩
    · rw [hxpdef, MNR54_fwd_apply]
      exact add_nonneg (mul_nonneg (by linarith [(hθ01 k).2]) (hxt0 k c)) (mul_nonneg (hθ01 k).1 (he0 k c))
    · simp only [hxpdef, MNR54_fwd_apply, Finset.sum_add_distrib, ← Finset.mul_sum, (hxt k).2,
        (MNR51_ePure_lottery (acor k)).2]; ring
  set D : Tuple n → ℝ := fun s => 1 + u i s - u i (Function.update s i a) with hD
  have hD0 : ∀ s, 0 ≤ D s := by
    intro s; simp only [hD]
    have h1 := (hu i s).1; have h2 := (hu i (Function.update s i a)).2
    linarith
  have M : ∀ z : Mixed n, AGT.IsMixedProfile z → deficit u z i a = ∑ s, AGT.profileProb z s * D s :=
    fun z hz => MNR51_deficit_eq u z hz i a
  -- the best-response profile
  set wf : Mixed n := fun j => if j < i then xp j else xt j with hwf
  have hwfm : AGT.IsMixedProfile wf := by
    intro j; simp only [hwf]; split_ifs
    · exact hxpm j
    · exact hxt j
  have hBR : 1 ≤ deficit u (Function.update wf i (ePure (acor i))) i a :=
    MNR54_deficit_rev u wf i (acor i) (fun a' => hfwd i a') a
  have hqi : qi u xt i ≤ deficit u xt i a := by
    unfold qi deficit regret
    haveI : Nonempty (Fin (n i)) := ⟨⟨0, hn i⟩⟩
    linarith [le_ciSup (f := fun a => gain u xt i a) (Set.finite_range _).bddAbove a]
  -- pointwise bound
  have hpt : ∀ s, (∏ k, (1 - θ k)) * AGT.profileProb xt s * D s
      + θ i * (∏ k ∈ univ.filter (fun k => ¬ k ≤ i), (1 - θ k))
          * AGT.profileProb (Function.update wf i (ePure (acor i))) s * D s
      ≤ AGT.profileProb xp s * D s := by
    intro s
    rw [← add_mul]
    apply mul_le_mul_of_nonneg_right _ (hD0 s)
    rw [MNR54_pp_self xp i s, MNR54_pp_self xt i s, MNR51_pp_update]
    rw [hxpdef, MNR54_fwd_apply]
    rw [← Finset.mul_prod_erase univ _ (mem_univ i)]
    set R := ∏ k ∈ univ.erase i, fwdSweep xt e acor k (s k) with hR
    have hR1 : (∏ k ∈ univ.erase i, (1 - θ k)) * ∏ k ∈ univ.erase i, xt k (s k) ≤ R := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_le_prod
      · intro k _; exact mul_nonneg (by linarith [(hθ01 k).2]) (hxt0 k _)
      · intro k _; rw [MNR54_fwd_apply]
        have := mul_nonneg (hθ01 k).1 (he0 k (s k)); linarith
    have hR2 : (∏ k ∈ univ.filter (fun k => ¬ k ≤ i), (1 - θ k)) * ∏ k ∈ univ.erase i, wf k (s k) ≤ R := by
      have e1 : ∏ k ∈ univ.filter (fun k => ¬ k ≤ i), (1 - θ k)
          = ∏ k ∈ univ.erase i, (if k < i then 1 else 1 - θ k) := by
        rw [Finset.prod_ite, Finset.prod_const_one, one_mul]
        congr 1; ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true, not_le, not_lt]
        constructor
        · intro h; exact ⟨ne_of_gt h, le_of_lt h⟩
        · intro h; exact lt_of_le_of_ne h.2 (Ne.symm h.1)
      rw [e1, ← Finset.prod_mul_distrib]
      apply Finset.prod_le_prod
      · intro k _; split_ifs with hk
        · simp only [hwf, if_pos hk, one_mul]; exact (hxpm k).1 _
        · simp only [hwf, if_neg hk]; exact mul_nonneg (by linarith [(hθ01 k).2]) (hxt0 k _)
      · intro k hk; split_ifs with hk'
        · simp only [hwf, if_pos hk', one_mul, hxpdef]; exact le_rfl
        · simp only [hwf, if_neg hk']; rw [MNR54_fwd_apply]
          have := mul_nonneg (hθ01 k).1 (he0 k (s k)); linarith
    have hall' : ∏ k, (1 - θ k) = (1 - θ i) * ∏ k ∈ univ.erase i, (1 - θ k) :=
      (Finset.mul_prod_erase univ (fun k => 1 - θ k) (mem_univ i)).symm
    rw [← hθdef]
    have k1 := mul_le_mul_of_nonneg_left hR1
      (mul_nonneg (by linarith [(hθ01 i).2] : (0:ℝ) ≤ 1 - θ i) (hxt0 i (s i)))
    have k2 := mul_le_mul_of_nonneg_left hR2 (mul_nonneg (hθ01 i).1 (he0 i (s i)))
    nlinarith only [k1, k2]
  have hsum := Finset.sum_le_sum (fun s (_ : s ∈ univ) => hpt s)
  rw [Finset.sum_add_distrib] at hsum
  have e1 : ∑ s, (∏ k, (1 - θ k)) * AGT.profileProb xt s * D s = (∏ k, (1 - θ k)) * deficit u xt i a := by
    rw [M _ hxt, Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring
  have e2 : ∑ s, θ i * (∏ k ∈ univ.filter (fun k => ¬ k ≤ i), (1 - θ k))
          * AGT.profileProb (Function.update wf i (ePure (acor i))) s * D s
      = θ i * (∏ k ∈ univ.filter (fun k => ¬ k ≤ i), (1 - θ k))
          * deficit u (Function.update wf i (ePure (acor i))) i a := by
    rw [M _ (MNR51_update_mixed _ hwfm i _ (MNR51_ePure_lottery _)), Finset.mul_sum]
    apply Finset.sum_congr rfl; intro s _; ring
  rw [e1, e2, ← M _ hxpm] at hsum
  rw [hall, hgt] at hsum
  have hc0 : 0 ≤ θ i * ∏ k ∈ univ.filter (fun k => ¬ k ≤ i), (1 - θ k) := by
    rw [hgt]; exact div_nonneg (he i) (by have := Finset.sum_nonneg (fun k (_ : k ∈ univ) => he k); linarith)
  have hE1 : 0 < 1 + ∑ k, e k := by have := Finset.sum_nonneg (fun k (_ : k ∈ univ) => he k); linarith
  have k1 : 1 / (1 + ∑ k, e k) * qi u xt i ≤ 1 / (1 + ∑ k, e k) * deficit u xt i a :=
    mul_le_mul_of_nonneg_left hqi (by positivity)
  have k2 : e i / (1 + ∑ k, e k) * 1
      ≤ e i / (1 + ∑ k, e k) * deficit u (Function.update wf i (ePure (acor i))) i a :=
    mul_le_mul_of_nonneg_left hBR (by rw [← hgt]; exact hc0)
  rw [mul_one] at k2
  have e3 : (qi u xt i + e i) / (1 + ∑ k, e k) = 1 / (1 + ∑ k, e k) * qi u xt i + e i / (1 + ∑ k, e k) := by
    field_simp
  rw [e3]; linarith

theorem MNR54_xt_dom {m : ℕ} {n : Fin m → ℕ} (x b : Mixed n) (hx : AGT.IsMixedProfile x)
    (hb : AGT.IsMixedProfile b) (γ : Fin m → ℝ) (t : ℝ) (htγ : ∀ i, 0 ≤ t * γ i ∧ t * γ i < 1)
    (δ : Fin m → ℝ) (hδ0 : ∀ i, 0 ≤ δ i) (ρ : ℝ) (hρ : 0 < ρ) (hδ1 : ∑ i, δ i = 1 - ρ)
    (arev : (i : Fin m) → Fin (n i)) (j : Fin m) (y : Fin (n j) → ℝ) (hy : ∀ c, 0 ≤ y c) (s : Tuple n) :
    (ρ * ∏ k, (1 - t * γ k)) * (AGT.profileProb x s
        + ∑ i, t * γ i / (1 - t * γ i) * AGT.profileProb (Function.update x i (b i)) s)
      ≤ AGT.profileProb (revSweep (actY x b t γ) δ arev) s ∧
    (ρ * ∏ k, (1 - t * γ k)) * (AGT.profileProb (Function.update x j y) s
        + ∑ i ∈ univ.erase j, t * γ i / (1 - t * γ i)
            * AGT.profileProb (Function.update (Function.update x i (b i)) j y) s)
      ≤ AGT.profileProb (Function.update (revSweep (actY x b t γ) δ arev) j y) s := by
  obtain ⟨hp01, -, -, hprodρ, -⟩ := MNR54_rev_facts δ hδ0 ρ hρ hδ1
  set p := revProb δ with hpdef
  set α : Fin m → ℝ := fun k => t * γ k / (1 - t * γ k) with hαdef
  have hα0 : ∀ k, 0 ≤ α k := fun k => div_nonneg (htγ k).1 (by linarith [(htγ k).2])
  have hαe : ∀ k, (1 - t * γ k) * α k = t * γ k := fun k => by
    simp only [hαdef]; field_simp [show (1 - t * γ k) ≠ 0 by linarith [(htγ k).2]]
  set xt := revSweep (actY x b t γ) δ arev with hxtdef
  have hx0 : ∀ k c, 0 ≤ x k c := fun k c => (hx k).1 c
  have hb0 : ∀ k c, 0 ≤ b k c := fun k c => (hb k).1 c
  set β : Fin m → ℝ := fun k => (1 - p k) * (1 - t * γ k) with hβdef
  have hβ0 : ∀ k, 0 ≤ β k := fun k => mul_nonneg (by linarith [(hp01 k).2]) (by linarith [(htγ k).2])
  have hβ1 : ∀ k, β k ≤ 1 := fun k => by
    simp only [hβdef]
    have h1 := hp01 k; have h2 := htγ k
    nlinarith only [h1.1, h1.2, h2.1, h2.2]
  have hcoord : ∀ k c, β k * (x k c + α k * b k c) ≤ xt k c := by
    intro k c
    rw [hxtdef, MNR54_rev_apply, MNR54_actY_apply]
    simp only [hβdef]
    have h1 : (1 - p k) * (1 - t * γ k) * (α k * b k c) = (1 - p k) * (t * γ k * b k c) := by
      linear_combination ((1 - p k) * b k c) * hαe k
    have h2 := mul_nonneg (hp01 k).1 (MNR54_ePure_nonneg (arev k) c)
    nlinarith only [h1, h2]
  have hall : ∏ k, β k = ρ * ∏ k, (1 - t * γ k) := by
    simp only [hβdef]; rw [Finset.prod_mul_distrib, hprodρ]
  have hBk0 : ∀ k, 0 ≤ α k * b k (s k) := fun k => mul_nonneg (hα0 k) (hb0 k _)
  constructor
  · unfold AGT.profileProb
    have h1 : (∏ k, β k) * ∏ k, (x k (s k) + α k * b k (s k)) ≤ ∏ k, xt k (s k) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod (fun k _ => mul_nonneg (hβ0 k) (add_nonneg (hx0 k _) (hBk0 k)))
        (fun k _ => hcoord k (s k))
    have h2 := MNR51_prod_expand univ (fun k => x k (s k)) (fun k => α k * b k (s k))
      (fun k => hx0 k _) hBk0
    have e : ∑ i, α i * ∏ k, Function.update x i (b i) k (s k)
        = ∑ i, α i * b i (s i) * ∏ k ∈ univ.erase i, x k (s k) := by
      apply Finset.sum_congr rfl; intro i _
      have := MNR51_pp_update x i (b i) s
      unfold AGT.profileProb at this; rw [this]; ring
    rw [e, ← hall]
    have := mul_le_mul_of_nonneg_left h2 (Finset.prod_nonneg (fun k (_ : k ∈ (univ : Finset (Fin m))) => hβ0 k))
    linarith
  · rw [MNR51_pp_update, MNR51_pp_update]
    have h1 : (∏ k ∈ univ.erase j, β k) * ∏ k ∈ univ.erase j, (x k (s k) + α k * b k (s k))
        ≤ ∏ k ∈ univ.erase j, xt k (s k) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod (fun k _ => mul_nonneg (hβ0 k) (add_nonneg (hx0 k _) (hBk0 k)))
        (fun k _ => hcoord k (s k))
    have h2 := MNR51_prod_expand (univ.erase j) (fun k => x k (s k)) (fun k => α k * b k (s k))
      (fun k => hx0 k _) hBk0
    have hβj : ∏ k, β k ≤ ∏ k ∈ univ.erase j, β k := by
      rw [← Finset.mul_prod_erase univ β (mem_univ j)]
      have := Finset.prod_nonneg (fun k (_ : k ∈ univ.erase j) => hβ0 k)
      nlinarith only [this, hβ1 j]
    have hP0 : 0 ≤ ∏ k ∈ univ.erase j, x k (s k) + ∑ i ∈ univ.erase j, α i * b i (s i) * ∏ k ∈ (univ.erase j).erase i, x k (s k) :=
      add_nonneg (Finset.prod_nonneg (fun k _ => hx0 k _))
        (Finset.sum_nonneg (fun i _ => mul_nonneg (hBk0 i) (Finset.prod_nonneg (fun k _ => hx0 k _))))
    have e : ∑ i ∈ univ.erase j, α i * AGT.profileProb (Function.update (Function.update x i (b i)) j y) s
        = y (s j) * ∑ i ∈ univ.erase j, α i * b i (s i) * ∏ k ∈ (univ.erase j).erase i, x k (s k) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      rw [MNR54_pp_update2 x i j hij, Finset.erase_right_comm]; ring
    rw [e, ← hall]
    have k1 := mul_le_mul_of_nonneg_right hβj hP0
    have k2 := mul_le_mul_of_nonneg_left h2 (Finset.prod_nonneg (fun k (_ : k ∈ univ.erase j) => hβ0 k))
    have k3 := le_trans k2 h1
    have k4 := mul_le_mul_of_nonneg_left (le_trans k1 k3) (hy (s j))
    nlinarith only [k4]

theorem MNR54_xp_dom {m : ℕ} {n : Fin m → ℕ} (xt : Mixed n) (hxt : AGT.IsMixedProfile xt)
    (e : Fin m → ℝ) (he : ∀ i, 0 ≤ e i) (acor : (i : Fin m) → Fin (n i))
    (j : Fin m) (y : Fin (n j) → ℝ) (hy : ∀ c, 0 ≤ y c) (s : Tuple n) :
    AGT.profileProb xt s / (1 + ∑ k, e k) ≤ AGT.profileProb (fwdSweep xt e acor) s ∧
    AGT.profileProb (Function.update xt j y) s / (1 + ∑ k, e k)
      ≤ AGT.profileProb (Function.update (fwdSweep xt e acor) j y) s := by
  obtain ⟨hθ01, hall, -⟩ := MNR54_fwd_facts e he
  have hcoord : ∀ k c, (1 - fwdProb e k) * xt k c ≤ fwdSweep xt e acor k c := by
    intro k c; rw [MNR54_fwd_apply]
    have := mul_nonneg (hθ01 k).1 (MNR54_ePure_nonneg (acor k) c); linarith
  have hc0 : ∀ k, 0 ≤ 1 - fwdProb e k := fun k => by linarith [(hθ01 k).2]
  have hxt0 : ∀ k c, 0 ≤ xt k c := fun k c => (hxt k).1 c
  constructor
  · rw [div_eq_mul_one_div, mul_comm, ← hall]
    unfold AGT.profileProb
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun k _ => mul_nonneg (hc0 k) (hxt0 k _)) (fun k _ => hcoord k _)
  · rw [MNR51_pp_update, MNR51_pp_update, div_eq_mul_one_div, ← hall]
    have h1 : (∏ k ∈ univ.erase j, (1 - fwdProb e k)) * ∏ k ∈ univ.erase j, xt k (s k)
        ≤ ∏ k ∈ univ.erase j, fwdSweep xt e acor k (s k) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod (fun k _ => mul_nonneg (hc0 k) (hxt0 k _)) (fun k _ => hcoord k _)
    have h2 : ∏ k, (1 - fwdProb e k) ≤ ∏ k ∈ univ.erase j, (1 - fwdProb e k) := by
      rw [← Finset.mul_prod_erase univ (fun k => 1 - fwdProb e k) (mem_univ j)]
      have := Finset.prod_nonneg (fun k (_ : k ∈ univ.erase j) => hc0 k)
      nlinarith only [this, (hθ01 j).1]
    have hX : 0 ≤ ∏ k ∈ univ.erase j, xt k (s k) := Finset.prod_nonneg (fun k _ => hxt0 k _)
    have k1 := mul_le_mul_of_nonneg_right h2 hX
    have k2 := mul_le_mul_of_nonneg_left (le_trans k1 h1) (hy (s j))
    nlinarith only [k2]

theorem MNR51_cert_scale {m : ℕ} {n : Fin m → ℕ} (gs : List (Gen n)) (P : ℝ) (f : Gen n → ℝ)
    (hf : ∀ g : Gen n, f { g with A := P * g.A } = P * f g) :
    ((gs.map fun g => { g with A := P * g.A }).map f).sum = P * (gs.map f).sum := by
  induction gs with
  | nil => simp
  | cons g gs ih => simp only [List.map_cons, List.sum_cons, ih, hf]; ring

set_option maxHeartbeats 8000000 in
theorem solution {m : ℕ} {n : Fin m → ℕ} (hm : 1 ≤ m) (hn : ∀ i, 0 < n i)
    (u : Utility n) (hu : BoundedGame u) (x : Mixed n) (hx : AGT.IsMixedProfile x)
    (b : Mixed n) (hb : AGT.IsMixedProfile b) (γ : Fin m → ℝ) (hγ : AGT.IsLottery γ)
    (t ρ β ν c : ℝ) (htγ : ∀ i, 0 ≤ t * γ i ∧ t * γ i < 1) (hρ : 0 < ρ) (hβ : 0 ≤ β)
    (hν : 0 ≤ ν) (hc : 0 < c)
    (δ : Fin m → ℝ) (hδ0 : ∀ i, 0 ≤ δ i) (hδ1 : ∑ i, δ i = 1 - ρ)
    (gs : List (Gen n)) (hgs : ∀ g ∈ gs, GenLegal g) (hcert : CertLaw x gs)
    (h : Fin m → ℝ) (hh : ∀ i, h i = (gs.map fun g => g.A * g.t * g.γ i).sum)
    (arev acor : (i : Fin m) → Fin (n i))
    (hrev : IsRevBR u (actY x b t γ) δ arev) :
    let y := actY x b t γ
    let xt := revSweep y δ arev
    let Craw := ρ * ∏ i, (1 - t * γ i)
    let α : Fin m → ℝ := fun i => t * γ i / (1 - t * γ i)
    let ω : Fin m → ℝ := fun i => δ i / (1 - ∑ j ∈ univ.filter (· ≤ i), δ j)
    let Sev := ∑ i, (α i + ω i)
    let d0 : Fin m → ℝ := fun i => deficitMix u x i (b i)
    let dij : (i j : Fin m) → (Fin (n j) → ℝ) → ℝ :=
      fun i j yj => deficitMix u (Function.update x j yj) i (b i)
    let enew : Fin m → ℝ := fun i => Craw * α i * (d0 i + α i + ω i
      + ∑ j ∈ univ.erase i, α j * dij i j (b j)
      + ∑ j ∈ univ.erase i, ω j * dij i j (ePure (arev j)))
    let eold : Fin m → ℝ := fun i => (gs.map fun g => Craw * g.A * g.odds i * (α i + ω i
      + ∑ j ∈ univ.erase i, α j * g.col u i j (b j)
      + ∑ j ∈ univ.erase i, ω j * g.col u i j (ePure (arev j)))).sum
    let oldMass : Fin m → ℝ := fun i => (gs.map fun g => g.A * g.odds i).sum
    let H := ∑ i, h i
    let D := 1 - ρ + β + ν * H
    let ecor : Fin m → ℝ := corrDef u (scaled u x) Craw D xt
    let E := ∑ i, ecor i
    let xp := fwdSweep xt ecor acor
    (∀ i, Craw * q u x + δ i + Craw * α i * (1 + Sev) + Craw * Sev * oldMass i - enew i
        - eold i ≤ qi u xt i) ∧
    (β ≤ Craw * t * (1 + Sev) → ν ≤ Craw * Sev → (∀ i, δ i = D / m - β * γ i - ν * h i) →
      IsFwdBR u xt ecor acor →
      E ≤ ∑ i, (enew i + eold i) ∧ (Craw * scaled u x + D) / (1 + E) ≤ scaled u xp ∧
      (c ≤ Craw / (1 + E) →
        CertLaw xp (gs.map (fun g => { g with A := c * g.A }) ++ [⟨x, b, γ, t, c⟩]) ∧
        c * scaled u x + D - D * E ≤ scaled u xp)) := by
  intro y xt Craw α ω Sev d0 dij enew eold oldMass H D ecor E xp
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨hp01, hω0, -, -, -⟩ := MNR54_rev_facts δ hδ0 ρ hρ hδ1
  obtain ⟨hym, hxtm⟩ := MNR54_xt_mixed x b hx hb γ t htγ δ hδ0 ρ hρ hδ1 arev
  have hα0 : ∀ k, 0 ≤ α k := fun k => div_nonneg (htγ k).1 (by linarith [(htγ k).2])
  have hαt : ∀ k, t * γ k ≤ α k := fun k => by
    show t * γ k ≤ t * γ k / (1 - t * γ k)
    have h1 := (htγ k).1; have h2 := (htγ k).2
    rw [le_div_iff₀ (by linarith)]; nlinarith only [h1, h2]
  have hCraw0 : 0 ≤ Craw := mul_nonneg hρ.le (Finset.prod_nonneg (fun k _ => by linarith [(htγ k).2]))
  have hSev0 : 0 ≤ Sev := Finset.sum_nonneg (fun k _ => add_nonneg (hα0 k) (hω0 k))
  have hP1 : ∀ i, Craw * q u x + δ i + Craw * α i * (1 + Sev) + Craw * Sev * oldMass i - enew i
      - eold i ≤ qi u xt i :=
    fun i => MNR54_part1 hn u hu x hx b hb γ t ρ htγ hρ δ hδ0 hδ1 gs hgs hcert arev hrev i
  refine ⟨hP1, ?_⟩
  intro hβ' hν' hδeq hfwd
  -- basic facts
  have hreg1 : Reg u x ≤ 1 := by
    apply ciSup_le; intro i
    haveI : Nonempty (Fin (n i)) := ⟨⟨0, hn i⟩⟩
    apply ciSup_le; intro a
    unfold gain DGPNash.NashMap.purePayoff
    have h1 := (MNR51_ep_bounds u hu _ (MNR51_update_mixed x hx i _ (MNR51_ePure_lottery a)) i).2
    have h2 := (MNR51_ep_bounds u hu x hx i).1
    have : (fun k => if k = a then (1:ℝ) else 0) = ePure a := rfl
    rw [this]; linarith
  have hq0 : 0 ≤ q u x := by unfold q; linarith
  have hς : scaled u x = (m:ℝ) * q u x := rfl
  have hh0 : ∀ i, 0 ≤ h i := fun i => by
    rw [hh i]; apply MNR53_list_nonneg; intro g hg
    obtain ⟨-, -, hγg, htγg, hA⟩ := hgs g hg
    have := mul_nonneg hA (htγg i).1
    nlinarith only [this]
  have hH0 : 0 ≤ H := Finset.sum_nonneg (fun i _ => hh0 i)
  have hD0 : 0 ≤ D := by
    show 0 ≤ 1 - ρ + β + ν * H
    have : 0 ≤ 1 - ρ := by rw [← hδ1]; exact Finset.sum_nonneg (fun i _ => hδ0 i)
    nlinarith only [this, hβ, mul_nonneg hν hH0]
  have hecor0 : ∀ i, 0 ≤ ecor i := fun i => le_max_left _ _
  have hE0 : 0 ≤ E := Finset.sum_nonneg (fun i _ => hecor0 i)
  have hecor_ge : ∀ i, Craw * q u x + D / m - qi u xt i ≤ ecor i := by
    intro i
    show Craw * q u x + D / m - qi u xt i ≤ max 0 ((Craw * scaled u x + D) / m - qi u xt i)
    have : (Craw * scaled u x + D) / m = Craw * q u x + D / m := by rw [hς]; field_simp
    rw [this]; exact le_max_right _ _
  -- nonnegativity of the error terms
  have hdefnn : ∀ (z : Mixed n), AGT.IsMixedProfile z → ∀ i, 0 ≤ deficitMix u z i (b i) :=
    fun z hz i => MNR51_deficitMix_nonneg u hu z hz i _ (hb i)
  have henew0 : ∀ i, 0 ≤ enew i := by
    intro i
    show 0 ≤ Craw * α i * (d0 i + α i + ω i + ∑ j ∈ univ.erase i, α j * dij i j (b j)
      + ∑ j ∈ univ.erase i, ω j * dij i j (ePure (arev j)))
    apply mul_nonneg (mul_nonneg hCraw0 (hα0 i))
    have h1 : 0 ≤ d0 i := hdefnn x hx i
    have h2 : 0 ≤ ∑ j ∈ univ.erase i, α j * dij i j (b j) :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (hα0 j) (hdefnn _ (MNR51_update_mixed x hx j _ (hb j)) i))
    have h3 : 0 ≤ ∑ j ∈ univ.erase i, ω j * dij i j (ePure (arev j)) :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (hω0 j)
        (hdefnn _ (MNR51_update_mixed x hx j _ (MNR51_ePure_lottery _)) i))
    linarith [hα0 i, hω0 i]
  have heold0 : ∀ i, 0 ≤ eold i := by
    intro i
    apply MNR53_list_nonneg; intro g hg
    obtain ⟨hbase, hdev, hγg, htγg, hA⟩ := hgs g hg
    have hodds : 0 ≤ g.odds i := div_nonneg (htγg i).1 (by linarith [(htγg i).2])
    have hcol : ∀ j (w : Fin (n j) → ℝ), AGT.IsLottery w → 0 ≤ g.col u i j w := fun j w hw =>
      MNR51_deficitMix_nonneg u hu _ (MNR51_update_mixed _ hbase j w hw) i _ (hdev i)
    apply mul_nonneg (mul_nonneg (mul_nonneg hCraw0 hA) hodds)
    have h2 : 0 ≤ ∑ j ∈ univ.erase i, α j * g.col u i j (b j) :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (hα0 j) (hcol j _ (hb j)))
    have h3 : 0 ≤ ∑ j ∈ univ.erase i, ω j * g.col u i j (ePure (arev j)) :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (hω0 j) (hcol j _ (MNR51_ePure_lottery _)))
    linarith [hα0 i, hω0 i]
  -- memory balancing
  have hbal : ∀ i, D / m ≤ δ i + Craw * α i * (1 + Sev) + Craw * Sev * oldMass i := by
    intro i
    have h1 : β * γ i ≤ Craw * α i * (1 + Sev) := by
      have k1 : γ i * β ≤ γ i * (Craw * t * (1 + Sev)) := mul_le_mul_of_nonneg_left hβ' (hγ.1 i)
      have k2 : Craw * (t * γ i) * (1 + Sev) ≤ Craw * α i * (1 + Sev) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hαt i) hCraw0) (by linarith)
      nlinarith only [k1, k2]
    have h2 : ν * h i ≤ Craw * Sev * oldMass i := by
      have k1 : h i ≤ oldMass i := by
        rw [hh i]; apply MNR53_list_le; intro g hg
        obtain ⟨-, -, -, htγg, hA⟩ := hgs g hg
        have hodds : g.t * g.γ i ≤ g.odds i := by
          unfold Gen.odds
          have h1 := (htγg i).1; have h2 := (htγg i).2
          rw [le_div_iff₀ (by linarith)]; nlinarith only [h1, h2]
        have := mul_le_mul_of_nonneg_left hodds hA
        nlinarith only [this]
      have k2 := mul_le_mul_of_nonneg_left k1 (mul_nonneg hCraw0 hSev0)
      have k3 := mul_le_mul_of_nonneg_right hν' (hh0 i)
      nlinarith only [k2, k3]
    rw [hδeq i]; linarith
  have hecor_le : ∀ i, ecor i ≤ enew i + eold i := by
    intro i
    show max 0 ((Craw * scaled u x + D) / m - qi u xt i) ≤ enew i + eold i
    have : (Craw * scaled u x + D) / m = Craw * q u x + D / m := by rw [hς]; field_simp
    rw [this]
    apply max_le (add_nonneg (henew0 i) (heold0 i))
    have := hP1 i; have := hbal i; linarith
  have hEle : E ≤ ∑ i, (enew i + eold i) := Finset.sum_le_sum (fun i _ => hecor_le i)
  -- the forward correction
  have hE1 : 0 < 1 + E := by linarith
  have hsc : (Craw * scaled u x + D) / (1 + E) ≤ scaled u xp := by
    set K := (Craw * q u x + D / m) / (1 + E) with hK
    have hgain : ∀ i (a : Fin (n i)), gain u xp i a ≤ 1 - K := by
      intro i a
      have h1 := MNR54_fwd_deficit u hu xt hxtm ecor hecor0 acor hfwd i a hn
      have h2 : K ≤ (qi u xt i + ecor i) / (1 + ∑ k, ecor k) := by
        rw [hK]; apply div_le_div_of_nonneg_right _ hE1.le
        linarith [hecor_ge i]
      have : deficit u xp i a = 1 - gain u xp i a := rfl
      linarith
    have hReg : Reg u xp ≤ 1 - K := by
      apply ciSup_le; intro i
      haveI : Nonempty (Fin (n i)) := ⟨⟨0, hn i⟩⟩
      exact ciSup_le (fun a => hgain i a)
    have e : (Craw * scaled u x + D) / (1 + E) = (m:ℝ) * K := by
      rw [hK, hς]; field_simp
    rw [e]
    show (m:ℝ) * K ≤ (m:ℝ) * (1 - Reg u xp)
    exact mul_le_mul_of_nonneg_left (by linarith) hmpos.le
  refine ⟨hEle, hsc, ?_⟩
  intro hc'
  constructor
  · -- the new certificate law
    have hγ' : ∀ k, (⟨x, b, γ, t, c⟩ : Gen n).odds k = α k := fun k => rfl
    constructor
    · intro a
      rw [List.map_append, List.sum_append, MNR51_cert_scale gs c _
        (fun g => by simp only [Gen.odds]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring)]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have hd := (MNR54_xt_dom x b hx hb γ t htγ δ hδ0 ρ hρ hδ1 arev ⟨0, hm⟩ (x ⟨0, hm⟩)
        (fun c' => (hx _).1 c') a).1
      have hp := (MNR54_xp_dom xt hxtm ecor hecor0 acor ⟨0, hm⟩ (x ⟨0, hm⟩) (fun c' => (hx _).1 c') a).1
      have hold := hcert.1 a
      have hS0 : 0 ≤ AGT.profileProb x a + ∑ i, α i * AGT.profileProb (Function.update x i (b i)) a := by
        apply add_nonneg (Finset.prod_nonneg (fun k _ => (hx k).1 _))
        exact Finset.sum_nonneg (fun i _ => mul_nonneg (hα0 i)
          (Finset.prod_nonneg (fun k _ => (MNR51_update_mixed x hx i _ (hb i) k).1 _)))
      have e1 : ∑ i, c * (⟨x, b, γ, t, c⟩ : Gen n).odds i * AGT.profileProb (Function.update x i (b i)) a
          = c * ∑ i, α i * AGT.profileProb (Function.update x i (b i)) a := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [hγ']; ring
      show c * _ + ∑ i, c * (⟨x, b, γ, t, c⟩ : Gen n).odds i *
        AGT.profileProb (Function.update (⟨x, b, γ, t, c⟩ : Gen n).base i ((⟨x, b, γ, t, c⟩ : Gen n).dev i)) a ≤ _
      have e2 : ∑ i, c * (⟨x, b, γ, t, c⟩ : Gen n).odds i *
          AGT.profileProb (Function.update (⟨x, b, γ, t, c⟩ : Gen n).base i ((⟨x, b, γ, t, c⟩ : Gen n).dev i)) a
          = c * ∑ i, α i * AGT.profileProb (Function.update x i (b i)) a := e1
      rw [e2]
      have k1 : c * (AGT.profileProb x a + ∑ i, α i * AGT.profileProb (Function.update x i (b i)) a)
          ≤ Craw / (1 + E) * (AGT.profileProb x a + ∑ i, α i * AGT.profileProb (Function.update x i (b i)) a) :=
        mul_le_mul_of_nonneg_right hc' hS0
      have k2 : Craw / (1 + E) * (AGT.profileProb x a + ∑ i, α i * AGT.profileProb (Function.update x i (b i)) a)
          ≤ AGT.profileProb xt a / (1 + E) := by
        rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right hd hE1.le
      have k3 := mul_le_mul_of_nonneg_left hold hc.le
      linarith
    · intro j yj hyj a
      rw [List.map_append, List.sum_append, MNR51_cert_scale gs c _
        (fun g => by simp only [Gen.odds]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring)]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have hd := (MNR54_xt_dom x b hx hb γ t htγ δ hδ0 ρ hρ hδ1 arev j yj hyj.1 a).2
      have hp := (MNR54_xp_dom xt hxtm ecor hecor0 acor j yj hyj.1 a).2
      have hold := hcert.2 j yj hyj a
      have hS0 : 0 ≤ AGT.profileProb (Function.update x j yj) a + ∑ i ∈ univ.erase j, α i *
          AGT.profileProb (Function.update (Function.update x i (b i)) j yj) a := by
        apply add_nonneg (Finset.prod_nonneg (fun k _ => (MNR51_update_mixed x hx j yj hyj k).1 _))
        exact Finset.sum_nonneg (fun i _ => mul_nonneg (hα0 i)
          (Finset.prod_nonneg (fun k _ => (MNR51_update_mixed _ (MNR51_update_mixed x hx i _ (hb i)) j yj hyj k).1 _)))
      have e2 : ∑ i ∈ univ.erase j, c * (⟨x, b, γ, t, c⟩ : Gen n).odds i *
          AGT.profileProb (Function.update (Function.update (⟨x, b, γ, t, c⟩ : Gen n).base i
            ((⟨x, b, γ, t, c⟩ : Gen n).dev i)) j yj) a
          = c * ∑ i ∈ univ.erase j, α i * AGT.profileProb (Function.update (Function.update x i (b i)) j yj) a := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [hγ']; ring
      rw [e2]
      have k1 := mul_le_mul_of_nonneg_right hc' hS0
      have k2 : Craw / (1 + E) * (AGT.profileProb (Function.update x j yj) a + ∑ i ∈ univ.erase j, α i *
          AGT.profileProb (Function.update (Function.update x i (b i)) j yj) a)
          ≤ AGT.profileProb (Function.update xt j yj) a / (1 + E) := by
        rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right hd hE1.le
      have k3 := mul_le_mul_of_nonneg_left hold hc.le
      linarith
  · -- the retained bound
    have hς0 : 0 ≤ scaled u x := by rw [hς]; exact mul_nonneg hmpos.le hq0
    have k1 : c * scaled u x ≤ Craw / (1 + E) * scaled u x := mul_le_mul_of_nonneg_right hc' hς0
    have k2 : D - D * E ≤ D / (1 + E) := by
      rw [le_div_iff₀ hE1]; nlinarith only [mul_nonneg hD0 (mul_nonneg hE0 hE0)]
    have e : (Craw * scaled u x + D) / (1 + E) = Craw / (1 + E) * scaled u x + D / (1 + E) := by
      field_simp
    linarith
