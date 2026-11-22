-- Prove2me | solution 1 for HarmonicRanking.Main.Supplement.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-22T20:09:44.541801+00:00
-- url     : https://prove2.me/submissions/7e05329a-f31e-4691-8838-0d97c67195cc

import Definitions.Def_HarmonicRanking_Main_Supplement_PriceLP
import Theorems.Thm_LP_farkas

set_option autoImplicit false

noncomputable section

namespace HarmonicRanking.Main.Supplement.LemmaB1Aux

open Matrix

abbrev Ex (m : ℕ) := Fin m → Fin m → Fin m → ℝ
abbrev T3 (m : ℕ) := Fin m × Fin m × Fin m
abbrev Iι (m : ℕ) := Option (T3 m ⊕ T3 m ⊕ T3 m ⊕ T3 m)
abbrev Iκ (m : ℕ) := (Fin m × Fin m) ⊕ T3 m

def projL {m : ℕ} (ℓ r p : Fin m) : Module.Dual ℝ (Ex m) where
  toFun x := x ℓ r p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cumYL {m : ℕ} (ℓ r p : Fin m) : Module.Dual ℝ (Ex m) where
  toFun x := cumY x ℓ r p
  map_add' x y := by
    simp only [cumY, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs <;> simp
  map_smul' c x := by
    simp only [cumY, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs <;> simp

def rowMassL {m : ℕ} (ℓ r : Fin m) : Module.Dual ℝ (Ex m) where
  toFun x := rowMass x ℓ r
  map_add' x y := by simp [rowMass, Finset.sum_add_distrib]
  map_smul' c x := by simp [rowMass, Finset.mul_sum]

def objL (m : ℕ) : Module.Dual ℝ (Ex m) where
  toFun x := lpObjective x
  map_add' x y := by simp [lpObjective, Finset.sum_add_distrib, add_div]
  map_smul' c x := by
    simp only [lpObjective, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

def aL (m : ℕ) : Iι m → Module.Dual ℝ (Ex m)
  | none => objL m
  | some (Sum.inl (ℓ, r, p)) => -projL ℓ r p
  | some (Sum.inr (Sum.inl (ℓ, r, p))) => -(cumYL ℓ r ℓ + cumYL r ℓ p)
  | some (Sum.inr (Sum.inr (Sum.inl (ℓ, r, p)))) =>
      if h : ℓ.val + 1 < m ∧ p.val ≤ ℓ.val then
        cumYL ℓ r p - cumYL ⟨ℓ.val + 1, h.1⟩ r ⟨p.val + 1, by omega⟩
      else 0
  | some (Sum.inr (Sum.inr (Sum.inr (ℓ, r, p)))) =>
      if h : ℓ.val + 1 < m ∧ p ≤ ℓ then
        cumYL ℓ r ⟨ℓ.val + 1, h.1⟩ - cumYL ⟨ℓ.val + 1, h.1⟩ r p
      else 0

def bL (m : ℕ) (t : ℝ) : Iι m → ℝ
  | none => t
  | some (Sum.inl _) => 0
  | some (Sum.inr (Sum.inl _)) => -(1 / (m : ℝ))
  | some (Sum.inr (Sum.inr (Sum.inl _))) => 0
  | some (Sum.inr (Sum.inr (Sum.inr _))) => 0

def eL (m : ℕ) : Iκ m → Module.Dual ℝ (Ex m)
  | Sum.inl (ℓ, r) => rowMassL ℓ r - rowMassL r ℓ
  | Sum.inr (ℓ, r, p) =>
      if h : ℓ.val + 1 < m ∧ ℓ < p then cumYL ℓ r p - cumYL ℓ r ⟨ℓ.val + 1, h.1⟩ else 0

lemma lemA {m : ℕ} (t : ℝ) {x : Ex m} (hx : InC x) (i : T3 m ⊕ T3 m ⊕ T3 m ⊕ T3 m) :
    aL m (some i) x ≤ bL m t (some i) := by
  obtain ⟨h0, h50, h51, h52, h53⟩ := hx
  rcases i with ⟨ℓ, r, p⟩ | ⟨ℓ, r, p⟩ | ⟨ℓ, r, p⟩ | ⟨ℓ, r, p⟩
  · simp only [aL, bL, LinearMap.neg_apply, projL, LinearMap.coe_mk, AddHom.coe_mk]
    linarith [h0 ℓ r p]
  · simp only [aL, bL, LinearMap.neg_apply, LinearMap.add_apply, cumYL, LinearMap.coe_mk,
      AddHom.coe_mk]
    linarith [h50 ℓ r p]
  · simp only [aL, bL]
    split_ifs with h
    · simp only [LinearMap.sub_apply, cumYL, LinearMap.coe_mk, AddHom.coe_mk]
      linarith [h51 ℓ r p h.1 h.2]
    · simp
  · simp only [aL, bL]
    split_ifs with h
    · simp only [LinearMap.sub_apply, cumYL, LinearMap.coe_mk, AddHom.coe_mk]
      linarith [h53 ℓ r p h.1 h.2]
    · simp

lemma lemB {m : ℕ} {x : Ex m} (hx : InC x) (j : T3 m) : eL m (Sum.inr j) x = 0 := by
  obtain ⟨h0, h50, h51, h52, h53⟩ := hx
  obtain ⟨ℓ, r, p⟩ := j
  simp only [eL]
  split_ifs with h
  · simp only [LinearMap.sub_apply, cumYL, LinearMap.coe_mk, AddHom.coe_mk]
    rw [h52 ℓ r p h.1 h.2, sub_self]
  · simp

lemma lemC {m : ℕ} (t : ℝ) {x : Ex m} (ha : ∀ i, aL m i x ≤ bL m t i)
    (he : ∀ j, eL m j x = (0 : Iκ m → ℝ) j) : LPFeasible x ∧ lpObjective x ≤ t := by
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro ℓ r p
    have := ha (some (Sum.inl (ℓ, r, p)))
    simp only [aL, bL, LinearMap.neg_apply, projL, LinearMap.coe_mk, AddHom.coe_mk] at this
    linarith
  · intro ℓ r p
    have := ha (some (Sum.inr (Sum.inl (ℓ, r, p))))
    simp only [aL, bL, LinearMap.neg_apply, LinearMap.add_apply, cumYL, LinearMap.coe_mk,
      AddHom.coe_mk] at this
    linarith
  · intro ℓ r p hℓ hp
    have := ha (some (Sum.inr (Sum.inr (Sum.inl (ℓ, r, p)))))
    simp only [aL, bL] at this
    rw [dif_pos ⟨hℓ, hp⟩] at this
    simp only [LinearMap.sub_apply, cumYL, LinearMap.coe_mk, AddHom.coe_mk] at this
    linarith
  · intro ℓ r p hℓ hlt
    have := he (Sum.inr (ℓ, r, p))
    simp only [eL, Pi.zero_apply] at this
    rw [dif_pos ⟨hℓ, hlt⟩] at this
    simp only [LinearMap.sub_apply, cumYL, LinearMap.coe_mk, AddHom.coe_mk] at this
    linarith
  · intro ℓ r p hℓ hp
    have := ha (some (Sum.inr (Sum.inr (Sum.inr (ℓ, r, p)))))
    simp only [aL, bL] at this
    rw [dif_pos ⟨hℓ, hp⟩] at this
    simp only [LinearMap.sub_apply, cumYL, LinearMap.coe_mk, AddHom.coe_mk] at this
    linarith
  · intro ℓ r
    have := he (Sum.inl (ℓ, r))
    have h' : rowMass x ℓ r - rowMass x r ℓ = 0 := this
    linarith
  · exact ha none

lemma sum_rowMass {m : ℕ} (F : Fin m → Fin m → ℝ) (x : Ex m) :
    (∑ ℓ, ∑ r, ∑ p, F ℓ r * x ℓ r p) = ∑ ℓ, ∑ r, F ℓ r * rowMass x ℓ r := by
  simp [rowMass, Finset.mul_sum]

lemma priced_eq {m : ℕ} (F : Fin m → Fin m → ℝ) (hF : InD F) (x : Ex m) (hx : LPFeasible x) :
    pricedObjective F x = lpObjective x := by
  have hsym : (∑ ℓ, ∑ r, F ℓ r * rowMass x ℓ r) = ∑ ℓ, ∑ r, F r ℓ * rowMass x ℓ r := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun r _ => ?_
    rw [hx.2 r ℓ]
  have h2 : (∑ ℓ, ∑ r, F ℓ r * rowMass x ℓ r) + ∑ ℓ, ∑ r, F r ℓ * rowMass x ℓ r =
      ∑ ℓ, ∑ r, rowMass x ℓ r := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← add_mul, hF ℓ r, one_mul]
  have h3 : (∑ ℓ, ∑ r, ∑ p, x ℓ r p) = ∑ ℓ, ∑ r, rowMass x ℓ r := rfl
  unfold pricedObjective lpObjective
  rw [sum_rowMass, h3, ← h2, ← hsym]
  ring

lemma priced_dual {m : ℕ} (hm : (m : ℝ) ≠ 0) (c : Fin m → Fin m → ℝ) (x : Ex m) :
    pricedObjective (fun ℓ r => 1 / 2 + (m : ℝ) / 2 * (c ℓ r - c r ℓ)) x =
      lpObjective x + ∑ ℓ, ∑ r, c ℓ r * (rowMass x ℓ r - rowMass x r ℓ) := by
  have e1 : pricedObjective (fun ℓ r => 1 / 2 + (m : ℝ) / 2 * (c ℓ r - c r ℓ)) x =
      ∑ ℓ, ∑ r, (rowMass x ℓ r / m + c ℓ r * rowMass x ℓ r - c r ℓ * rowMass x ℓ r) := by
    unfold pricedObjective
    rw [sum_rowMass, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    field_simp
    ring
  have e2 : (∑ ℓ, ∑ r, c r ℓ * rowMass x ℓ r) = ∑ ℓ, ∑ r, c ℓ r * rowMass x r ℓ := by
    rw [Finset.sum_comm]
  have h3 : lpObjective x = ∑ ℓ, ∑ r, rowMass x ℓ r / m := by
    unfold lpObjective
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [Finset.sum_div]
    rfl
  rw [e1, h3]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_sub]
  rw [e2]
  ring

def xs (m : ℕ) : Ex m := fun _ _ _ => 1 / (2 * (m : ℝ))

lemma cumY_xs {m : ℕ} (ℓ r p : Fin m) : cumY (xs m) ℓ r p = ((ℓ : ℕ) + 1) * (1 / (2 * (m : ℝ))) := by
  unfold cumY xs
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    Finset.filter_ge_eq_Iic, Fin.card_Iic, nsmul_eq_mul]
  push_cast
  ring

lemma xs_InC {m : ℕ} (hm : 1 ≤ m) : InC (xs m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hc : 0 ≤ 1 / (2 * (m : ℝ)) := by positivity
  refine ⟨fun _ _ _ => hc, ?_, ?_, ?_, ?_⟩
  · intro ℓ r p
    rw [cumY_xs, cumY_xs]
    have h1 : (0 : ℝ) ≤ (ℓ : ℕ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (r : ℕ) := Nat.cast_nonneg _
    have : 1 / (m : ℝ) = 2 * (1 / (2 * (m : ℝ))) := by field_simp
    rw [this]
    nlinarith
  · intro ℓ r p hℓ hp
    rw [cumY_xs, cumY_xs]
    push_cast
    nlinarith
  · intro ℓ r p hℓ _
    rw [cumY_xs, cumY_xs]
  · intro ℓ r p hℓ _
    rw [cumY_xs, cumY_xs]
    push_cast
    nlinarith

lemma xs_bal {m : ℕ} (ℓ r : Fin m) : rowMass (xs m) ℓ r = rowMass (xs m) r ℓ := rfl

end HarmonicRanking.Main.Supplement.LemmaB1Aux

open HarmonicRanking.Main.Supplement HarmonicRanking.Main.Supplement.LemmaB1Aux in
theorem solution (m : ℕ) (hm : 1 ≤ m) :
    lpValue m = ⨆ (F : Fin m → Fin m → ℝ) (_ : InD F), Rm F := by
  apply le_antisymm
  · by_contra hcon
    rw [not_le] at hcon
    obtain ⟨t, ht1, ht2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
    have hinf : ¬ ∃ x : Ex m, (∀ i, aL m i x ≤ bL m t i) ∧
        ∀ j, eL m j x = (0 : Iκ m → ℝ) j := by
      rintro ⟨x, ha, he⟩
      obtain ⟨hfe, hobj⟩ := lemC t ha he
      have h1 : lpValue m ≤ ((lpObjective x : ℝ) : EReal) := iInf₂_le x hfe
      have h2 : ((lpObjective x : ℝ) : EReal) ≤ (t : EReal) := EReal.coe_le_coe_iff.mpr hobj
      exact lt_irrefl _ (lt_of_le_of_lt (h1.trans h2) ht2)
    obtain ⟨y, z, hy, hcomb, hlt⟩ := (LP.farkas (aL m) (bL m t) (eL m) 0).mp hinf
    have key : ∀ x : Ex m, InC x → 0 < y none * (lpObjective x - t) +
        ∑ ℓ, ∑ r, z (Sum.inl (ℓ, r)) * (rowMass x ℓ r - rowMass x r ℓ) := by
      intro x hx
      have h0 := congrArg (fun f => f x) hcomb
      simp only [LinearMap.add_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply] at h0
      have hs1 : ∑ i : Iι m, y i * aL m i x =
          y none * aL m none x + ∑ i, y (some i) * aL m (some i) x := Fintype.sum_option _
      have hs2 : ∑ j : Iκ m, z j * eL m j x =
          ∑ p, z (Sum.inl p) * eL m (Sum.inl p) x + ∑ j, z (Sum.inr j) * eL m (Sum.inr j) x :=
        Fintype.sum_sum_type _
      rw [hs1, hs2] at h0
      have hb : y ⬝ᵥ bL m t + z ⬝ᵥ (0 : Iκ m → ℝ) =
          y none * t + ∑ i, y (some i) * bL m t (some i) := by
        simp only [dotProduct, Fintype.sum_option, Pi.zero_apply, mul_zero,
          Finset.sum_const_zero, add_zero]
        rfl
      have hle : ∑ i, y (some i) * aL m (some i) x ≤ ∑ i, y (some i) * bL m t (some i) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (lemA t hx i) (hy (some i))
      have hz2 : ∑ j, z (Sum.inr j) * eL m (Sum.inr j) x = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [lemB hx j, mul_zero]
      have hz1 : ∑ p : Fin m × Fin m, z (Sum.inl p) * eL m (Sum.inl p) x =
          ∑ ℓ, ∑ r, z (Sum.inl (ℓ, r)) * (rowMass x ℓ r - rowMass x r ℓ) := by
        rw [Fintype.sum_prod_type]
        rfl
      have haN : aL m none x = lpObjective x := rfl
      rw [haN, hz2, hz1] at h0
      rw [hb] at hlt
      rw [mul_sub]
      linarith
    have hy0 : 0 < y none := by
      have := key (xs m) (xs_InC hm)
      have hbal : ∑ ℓ, ∑ r, z (Sum.inl (ℓ, r)) * (rowMass (xs m) ℓ r - rowMass (xs m) r ℓ) = 0 :=
        Finset.sum_eq_zero fun ℓ _ => Finset.sum_eq_zero fun r _ => by
          rw [xs_bal ℓ r, sub_self, mul_zero]
      rw [hbal, add_zero] at this
      rcases (hy none).lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h] at this
        simp at this
    have hmR : (m : ℝ) ≠ 0 := by
      have : (0 : ℝ) < m := by exact_mod_cast hm
      exact this.ne'
    set c : Fin m → Fin m → ℝ := fun ℓ r => z (Sum.inl (ℓ, r)) / y none with hcdef
    have hF : InD (fun ℓ r => 1 / 2 + (m : ℝ) / 2 * (c ℓ r - c r ℓ)) := by
      intro ℓ r
      ring
    have hR : (t : EReal) ≤ Rm (fun ℓ r => 1 / 2 + (m : ℝ) / 2 * (c ℓ r - c r ℓ)) := by
      apply le_iInf₂
      intro x hx
      rw [EReal.coe_le_coe_iff, priced_dual hmR c x]
      have h1 := div_pos (key x hx) hy0
      rw [add_div, mul_div_cancel_left₀ _ hy0.ne'] at h1
      have hc : ∑ ℓ, ∑ r, c ℓ r * (rowMass x ℓ r - rowMass x r ℓ) =
          (∑ ℓ, ∑ r, z (Sum.inl (ℓ, r)) * (rowMass x ℓ r - rowMass x r ℓ)) / y none := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [hcdef]
        ring
      linarith
    exact lt_irrefl _ (lt_of_le_of_lt (hR.trans (le_iSup₂_of_le _ hF le_rfl)) ht1)
  · exact iSup₂_le fun F hF => le_iInf₂ fun x hx =>
      (iInf₂_le x hx.1).trans (le_of_eq (by rw [priced_eq F hF x hx]))
