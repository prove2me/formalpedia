-- Prove2me | solution 1 for MFGPlanning.Existence.eq_30
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:20:13.561331+00:00
-- url     : https://prove2.me/submissions/72f0384c-3d5a-408f-aa69-6b69c90aa57b

import Mathlib
import Definitions.Def_MFGPlanning_Existence_Grid
import Definitions.Def_MFGPlanning_Existence_Duality

set_option autoImplicit false

open MFGPlanning.Existence in
theorem f93_sh1p (d : Data) (f : d.Pt → ℝ) :
    ∑ p : d.Pt, f (p.1 + 1, p.2) = ∑ p, f p :=
  Fintype.sum_equiv (Equiv.addRight ((1 : ZMod d.Nh), (0 : ZMod d.Nh))) _ _
    (fun p => by
      show f (p.1 + 1, p.2) = f (p + ((1 : ZMod d.Nh), (0 : ZMod d.Nh))); exact congrArg f (Prod.ext (by simp) (by simp)))

open MFGPlanning.Existence in
theorem f93_sh1m (d : Data) (f : d.Pt → ℝ) :
    ∑ p : d.Pt, f (p.1 - 1, p.2) = ∑ p, f p :=
  Fintype.sum_equiv (Equiv.subRight ((1 : ZMod d.Nh), (0 : ZMod d.Nh))) _ _
    (fun p => by
      simp only [Equiv.subRight_apply]; exact congrArg f (Prod.ext (by simp) (by simp)))

open MFGPlanning.Existence in
theorem f93_sh2p (d : Data) (f : d.Pt → ℝ) :
    ∑ p : d.Pt, f (p.1, p.2 + 1) = ∑ p, f p :=
  Fintype.sum_equiv (Equiv.addRight ((0 : ZMod d.Nh), (1 : ZMod d.Nh))) _ _
    (fun p => by
      show f (p.1, p.2 + 1) = f (p + ((0 : ZMod d.Nh), (1 : ZMod d.Nh))); exact congrArg f (Prod.ext (by simp) (by simp)))

open MFGPlanning.Existence in
theorem f93_sh2m (d : Data) (f : d.Pt → ℝ) :
    ∑ p : d.Pt, f (p.1, p.2 - 1) = ∑ p, f p :=
  Fintype.sum_equiv (Equiv.subRight ((0 : ZMod d.Nh), (1 : ZMod d.Nh))) _ _
    (fun p => by
      simp only [Equiv.subRight_apply]; exact congrArg f (Prod.ext (by simp) (by simp)))

open MFGPlanning.Existence in
theorem f93_lap_adj (d : Data) (U V : d.Pt → ℝ) :
    ∑ p, U p * lap d V p = ∑ p, lap d U p * V p := by
  have a1 := f93_sh1p d (fun q => U (q.1 - 1, q.2) * V q)
  have a2 := f93_sh1m d (fun q => U (q.1 + 1, q.2) * V q)
  have a3 := f93_sh2p d (fun q => U (q.1, q.2 - 1) * V q)
  have a4 := f93_sh2m d (fun q => U (q.1, q.2 + 1) * V q)
  simp only [add_sub_cancel_right, sub_add_cancel] at a1 a2 a3 a4
  have e1 : ∀ p, U p * lap d V p = -(1 / d.h ^ 2) * (4 * (U p * V p)) + (1 / d.h ^ 2) *
      (U p * V (p.1 + 1, p.2)) + (1 / d.h ^ 2) * (U p * V (p.1 - 1, p.2))
      + (1 / d.h ^ 2) * (U p * V (p.1, p.2 + 1)) + (1 / d.h ^ 2) * (U p * V (p.1, p.2 - 1)) := by
    intro p; simp only [lap]; ring
  have e2 : ∀ p, lap d U p * V p = -(1 / d.h ^ 2) * (4 * (U p * V p)) + (1 / d.h ^ 2) *
      (U (p.1 + 1, p.2) * V p) + (1 / d.h ^ 2) * (U (p.1 - 1, p.2) * V p)
      + (1 / d.h ^ 2) * (U (p.1, p.2 + 1) * V p) + (1 / d.h ^ 2) * (U (p.1, p.2 - 1) * V p) := by
    intro p; simp only [lap]; ring
  rw [Finset.sum_congr rfl (fun p _ => e1 p), Finset.sum_congr rfl (fun p _ => e2 p)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [a1, a2, a3, a4]
  ring

open MFGPlanning.Existence in
theorem f93_div_adj (d : Data) (Z : d.Pt → Fin 4 → ℝ) (V : d.Pt → ℝ) :
    ∑ p, ∑ l, Z p l * Dh d V p l = -∑ p, divh d Z p * V p := by
  have b1 := f93_sh1p d (fun q => Z (q.1 - 1, q.2) 0 * V q)
  have b3 := f93_sh2p d (fun q => Z (q.1, q.2 - 1) 2 * V q)
  have b2 := f93_sh1m d (fun q => Z (q.1 + 1, q.2) 1 * V q)
  have b4 := f93_sh2m d (fun q => Z (q.1, q.2 + 1) 3 * V q)
  simp only [add_sub_cancel_right, sub_add_cancel, Prod.mk.eta] at b1 b2 b3 b4
  have e1 : ∀ p, ∑ l, Z p l * Dh d V p l = (1 / d.h) * (Z p 0 * V (p.1 + 1, p.2)) - (1 / d.h) * (Z p 0 * V p)
      + (1 / d.h) * (Z p 1 * V p) - (1 / d.h) * (Z p 1 * V (p.1 - 1, p.2))
      + (1 / d.h) * (Z p 2 * V (p.1, p.2 + 1)) - (1 / d.h) * (Z p 2 * V p)
      + (1 / d.h) * (Z p 3 * V p) - (1 / d.h) * (Z p 3 * V (p.1, p.2 - 1)) := by
    intro p
    simp [Fin.sum_univ_four, Dh, D1, D2]
    ring
  have e2 : ∀ p, divh d Z p * V p = (1 / d.h) * (Z p 0 * V p) - (1 / d.h) * (Z (p.1 - 1, p.2) 0 * V p)
      + (1 / d.h) * (Z (p.1 + 1, p.2) 1 * V p) - (1 / d.h) * (Z p 1 * V p)
      + (1 / d.h) * (Z p 2 * V p) - (1 / d.h) * (Z (p.1, p.2 - 1) 2 * V p)
      + (1 / d.h) * (Z (p.1, p.2 + 1) 3 * V p) - (1 / d.h) * (Z p 3 * V p) := by
    intro p; simp only [divh]; ring
  rw [Finset.sum_congr rfl (fun p _ => e1 p), Finset.sum_congr rfl (fun p _ => e2 p)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [b1, b2, b3, b4]
  ring

open MFGPlanning.Existence in
theorem f93_snoc0 (d : Data) (M : Fin d.NT → d.Pt → ℝ) :
    (Fin.snoc (α := fun _ => d.Pt → ℝ) M d.mT 0 : d.Pt → ℝ) = M 0 := by
  have : (0 : Fin (d.NT + 1)) = Fin.castSucc (0 : Fin d.NT) := by ext; simp
  rw [this, Fin.snoc_castSucc]

open MFGPlanning.Existence in
theorem f93_ident (d : Data) (M : Fin d.NT → d.Pt → ℝ) (Z : Fin d.NT → d.Pt → Fin 4 → ℝ)
    (Ψ : Fin (d.NT + 1) → d.Pt → ℝ) :
    pair d (-M) (-Z) (Lam d Ψ).1 (Lam d Ψ).2 - F d Ψ =
      ∑ k : Fin d.NT, ∑ p, (((Fin.snoc (α := fun _ => d.Pt → ℝ) M d.mT k.succ p) - M k p) / d.dt
        + d.ν * lap d (M k) p + divh d (Z k) p) * Ψ k.succ p
      + (1 / d.dt) * ∑ p, (M 0 p - d.m0 p) * Ψ 0 p := by
  have hL : ∀ k : Fin d.NT, ∑ p, ((-M) k p * (Lam d Ψ).1 k p + ∑ l, (-Z) k p l * (Lam d Ψ).2 k p l)
      = (1 / d.dt) * ∑ p, M k p * Ψ k.castSucc p - (1 / d.dt) * ∑ p, M k p * Ψ k.succ p
        + d.ν * ∑ p, lap d (M k) p * Ψ k.succ p + ∑ p, divh d (Z k) p * Ψ k.succ p := by
    intro k
    have e : ∀ p, ((-M) k p * (Lam d Ψ).1 k p + ∑ l, (-Z) k p l * (Lam d Ψ).2 k p l)
        = (1 / d.dt) * (M k p * Ψ k.castSucc p) - (1 / d.dt) * (M k p * Ψ k.succ p)
          + d.ν * (M k p * lap d (Ψ k.succ) p) - ∑ l, Z k p l * Dh d (Ψ k.succ) p l := by
      intro p
      simp only [Lam, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
      ring
    rw [Finset.sum_congr rfl (fun p _ => e p)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [f93_lap_adj, f93_div_adj]
    ring
  have hR : ∀ k : Fin d.NT, ∑ p, (((Fin.snoc (α := fun _ => d.Pt → ℝ) M d.mT k.succ p) - M k p) / d.dt
        + d.ν * lap d (M k) p + divh d (Z k) p) * Ψ k.succ p
      = (1 / d.dt) * ∑ p, (Fin.snoc (α := fun _ => d.Pt → ℝ) M d.mT k.succ p) * Ψ k.succ p
        - (1 / d.dt) * ∑ p, M k p * Ψ k.succ p
        + d.ν * ∑ p, lap d (M k) p * Ψ k.succ p + ∑ p, divh d (Z k) p * Ψ k.succ p := by
    intro k
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    ring
  set a : Fin (d.NT + 1) → ℝ := fun j => ∑ p, (Fin.snoc (α := fun _ => d.Pt → ℝ) M d.mT j p) * Ψ j p
    with ha
  have h1 := Fin.sum_univ_succ a
  have h2 := Fin.sum_univ_castSucc a
  have hc : ∀ k : Fin d.NT, a k.castSucc = ∑ p, M k p * Ψ k.castSucc p := by
    intro k; simp only [ha, Fin.snoc_castSucc]
  have hl : a (Fin.last d.NT) = ∑ p, d.mT p * Ψ (Fin.last d.NT) p := by
    simp only [ha, Fin.snoc_last]
  have h0 : a 0 = ∑ p, M 0 p * Ψ 0 p := by
    simp only [ha, f93_snoc0]
  simp only [pair]
  rw [Finset.sum_congr rfl (fun k _ => hL k), Finset.sum_congr rfl (fun k _ => hR k)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [hc] at h2
  have hs : ∑ k : Fin d.NT, a k.succ = ∑ k : Fin d.NT, ∑ p,
      (Fin.snoc (α := fun _ => d.Pt → ℝ) M d.mT k.succ p) * Ψ k.succ p := rfl
  rw [← hs]
  simp only [F]
  rw [h0] at h1
  rw [hl] at h2
  have hm : ∑ p, (M 0 p - d.m0 p) * Ψ 0 p = ∑ p, M 0 p * Ψ 0 p - ∑ p, d.m0 p * Ψ 0 p := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun p _ => by ring)
  rw [hm]
  linear_combination (1 / d.dt) * h1 - (1 / d.dt) * h2

open MFGPlanning.Existence in
theorem f93_lower (d : Data) (M : Fin d.NT → d.Pt → ℝ) (Z : Fin d.NT → d.Pt → Fin 4 → ℝ)
    (Ψ : Fin (d.NT + 1) → d.Pt → ℝ) (hΨ : ∑ p, Ψ 0 p = 0) :
    (((pair d (-M) (-Z) (Lam d Ψ).1 (Lam d Ψ).2 - F d Ψ : ℝ)) : EReal) ≤ SigmaStar d (-M) (-Z) := by
  unfold SigmaStar
  refine le_iSup₂_of_le (Lam d Ψ).1 (Lam d Ψ).2 ?_
  have hS : SigmaF d (Lam d Ψ).1 (Lam d Ψ).2 ≤ (F d Ψ : EReal) := by
    unfold SigmaF
    exact iInf₂_le Ψ ⟨rfl, hΨ⟩
  rw [EReal.coe_sub]
  exact EReal.sub_le_sub le_rfl hS

open MFGPlanning.Existence in
theorem f93_sum_lap (d : Data) (U : d.Pt → ℝ) : ∑ p, lap d U p = 0 := by
  have := f93_lap_adj d (fun _ => 1) U
  have h0 : ∀ p, lap d (fun _ => (1 : ℝ)) p = 0 := by intro p; simp only [lap]; ring
  simp only [h0, one_mul, zero_mul, Finset.sum_const_zero] at this
  exact this

open MFGPlanning.Existence in
theorem f93_sum_divh (d : Data) (Z : d.Pt → Fin 4 → ℝ) : ∑ p, divh d Z p = 0 := by
  have := f93_div_adj d Z (fun _ => 1)
  have h0 : ∀ p l, Dh d (fun _ => (1 : ℝ)) p l = 0 := by
    intro p l; fin_cases l <;> simp [Dh, D1, D2]
  simp only [h0, mul_zero, mul_one, Finset.sum_const_zero] at this
  linarith

open MFGPlanning.Existence in
theorem solution (d : Data) (hm0 : InK d d.m0) (hmT : InK d d.mT) :
    ∀ (M : Fin d.NT → d.Pt → ℝ) (Z : Fin d.NT → d.Pt → Fin 4 → ℝ),
      (PlanningConstraint d M Z → SigmaStar d (-M) (-Z) = 0) ∧
        (¬ PlanningConstraint d M Z → SigmaStar d (-M) (-Z) = ⊤) := by
  intro M Z
  have hdt : 0 < d.dt := div_pos d.hT (by exact_mod_cast d.hNT)
  have hh : d.h ≠ 0 := by
    unfold Data.h; exact inv_ne_zero (by exact_mod_cast d.hNh.ne')
  constructor
  · rintro ⟨hC, hM0⟩
    apply le_antisymm
    · unfold SigmaStar
      refine iSup₂_le fun α β => ?_
      rw [EReal.sub_nonpos]
      unfold SigmaF
      refine le_iInf₂ fun Ψ hΨ => ?_
      obtain ⟨hL, h0⟩ := hΨ
      have hα : α = (Lam d Ψ).1 := by rw [hL]
      have hβ : β = (Lam d Ψ).2 := by rw [hL]
      subst hα hβ
      have hid := f93_ident d M Z Ψ
      simp only [hC, zero_mul, Finset.sum_const_zero, hM0, sub_self, zero_add, mul_zero] at hid
      exact_mod_cast (sub_eq_zero.mp hid).le
    · have := f93_lower d M Z 0 (by simp)
      have hid := f93_ident d M Z 0
      simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero] at hid
      rw [hid] at this
      exact_mod_cast this
  · intro hnot
    rw [EReal.eq_top_iff_forall_lt]
    intro r
    by_cases hC : ∀ (n : Fin d.NT) (p : d.Pt),
        ((Fin.snoc (α := fun _ => d.Pt → ℝ) M d.mT n.succ p) - M n p) / d.dt
          + d.ν * lap d (M n) p + divh d (Z n) p = 0
    · -- mass conservation
      have hstep : ∀ n : Fin d.NT, ∑ p, (Fin.snoc (α := fun _ => d.Pt → ℝ) M d.mT n.succ p)
          = ∑ p, (Fin.snoc (α := fun _ => d.Pt → ℝ) M d.mT n.castSucc p) := by
        intro n
        have hs : ∑ p, (((Fin.snoc (α := fun _ => d.Pt → ℝ) M d.mT n.succ p) - M n p) / d.dt
          + d.ν * lap d (M n) p + divh d (Z n) p) = 0 := by
          simp only [hC n, Finset.sum_const_zero]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, f93_sum_lap,
          f93_sum_divh, ← Finset.sum_div, Finset.sum_sub_distrib] at hs
        rw [Fin.snoc_castSucc]
        have : (∑ p, (Fin.snoc (α := fun _ => d.Pt → ℝ) M d.mT n.succ p) - ∑ p, M n p) = 0 := by
          have := hs; field_simp at this; linarith
        linarith
      have hind : ∀ i (hi : i < d.NT + 1),
          ∑ p, (Fin.snoc (α := fun _ => d.Pt → ℝ) M d.mT ⟨i, hi⟩ p)
            = ∑ p, (Fin.snoc (α := fun _ => d.Pt → ℝ) M d.mT 0 p) := by
        intro i
        induction i with
        | zero => intro hi; rfl
        | succ i ih =>
          intro hi
          have e1 : (⟨i + 1, hi⟩ : Fin (d.NT + 1)) = (⟨i, by omega⟩ : Fin d.NT).succ := rfl
          have e2 : (⟨i, by omega⟩ : Fin (d.NT + 1)) = (⟨i, by omega⟩ : Fin d.NT).castSucc := rfl
          rw [e1, hstep, ← e2, ih]
      have hmass : ∑ p, M 0 p = ∑ p, d.mT p := by
        have := hind d.NT (by omega)
        have e : (⟨d.NT, by omega⟩ : Fin (d.NT + 1)) = Fin.last d.NT := rfl
        rw [e, Fin.snoc_last, f93_snoc0] at this
        exact this.symm
      have hm0mT : ∑ p, d.m0 p = ∑ p, d.mT p := by
        have h1 := hm0.1; have h2 := hmT.1
        have hh2 : d.h ^ 2 ≠ 0 := pow_ne_zero 2 hh
        have := h1.trans h2.symm
        exact mul_left_cancel₀ hh2 this
      have hne : M 0 ≠ d.m0 := fun h => hnot ⟨hC, h⟩
      set v : d.Pt → ℝ := fun p => M 0 p - d.m0 p with hv
      have hvs : ∑ p, v p = 0 := by
        simp only [hv, Finset.sum_sub_distrib, hmass, hm0mT, sub_self]
      obtain ⟨q, hq⟩ : ∃ q, v q ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hne (funext fun p => sub_eq_zero.mp (hcon p))
      have hpos : 0 < ∑ p, v p * v p :=
        Finset.sum_pos' (fun p _ => mul_self_nonneg _) ⟨q, Finset.mem_univ _, mul_self_pos.mpr hq⟩
      set t : ℝ := d.dt * (|r| + 1) / ∑ p, v p * v p with ht
      have hlow := f93_lower d M Z (fun j p => if j = 0 then t * v p else 0)
        (by simp only [if_true, ← Finset.mul_sum, hvs, mul_zero])
      have hid := f93_ident d M Z (fun j p => if j = 0 then t * v p else 0)
      simp only [hC, zero_mul, Finset.sum_const_zero, zero_add, if_true] at hid
      rw [hid] at hlow
      have hval : (1 / d.dt) * ∑ p, (M 0 p - d.m0 p) * (t * v p) = |r| + 1 := by
        have : ∑ p, (M 0 p - d.m0 p) * (t * v p) = t * ∑ p, v p * v p := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun p _ => by simp only [hv]; ring)
        rw [this, ht, div_mul_cancel₀ _ hpos.ne']; field_simp
      rw [hval] at hlow
      refine lt_of_lt_of_le ?_ hlow
      exact_mod_cast (show r < |r| + 1 by linarith [le_abs_self r])
    · push Not at hC
      obtain ⟨n, p, hnp⟩ := hC
      set c := ((Fin.snoc (α := fun _ => d.Pt → ℝ) M d.mT n.succ p) - M n p) / d.dt
          + d.ν * lap d (M n) p + divh d (Z n) p with hc
      set t : ℝ := (|r| + 1) / c with ht
      set Ψ' : Fin (d.NT + 1) → d.Pt → ℝ :=
        fun j q => if j = n.succ then (if q = p then t else 0) else 0 with hΨ'
      have hlow := f93_lower d M Z Ψ' (by simp [hΨ', (Fin.succ_ne_zero n).symm])
      have hid := f93_ident d M Z Ψ'
      have hΨ0 : ∑ q, (M 0 q - d.m0 q) * Ψ' 0 q = 0 := by
        simp [hΨ', (Fin.succ_ne_zero n).symm]
      have hsum : ∑ k : Fin d.NT, ∑ q, (((Fin.snoc (α := fun _ => d.Pt → ℝ) M d.mT k.succ q)
          - M k q) / d.dt + d.ν * lap d (M k) q + divh d (Z k) q) * Ψ' k.succ q = c * t := by
        rw [Finset.sum_eq_single n (fun k _ hk => by simp [hΨ', hk]) (by simp)]
        rw [Finset.sum_eq_single p (fun q _ hq => by simp [hΨ', hq]) (by simp)]
        simp [hΨ', hc]
      rw [hsum, hΨ0, mul_zero, add_zero] at hid
      rw [hid] at hlow
      have hval : c * t = |r| + 1 := by rw [ht]; field_simp
      rw [hval] at hlow
      refine lt_of_lt_of_le ?_ hlow
      exact_mod_cast (show r < |r| + 1 by linarith [le_abs_self r])
