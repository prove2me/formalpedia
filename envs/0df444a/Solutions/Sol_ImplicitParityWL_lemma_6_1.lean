-- Prove2me | solution 1 for ImplicitParityWL.lemma_6_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T05:00:32.989804+00:00
-- url     : https://prove2.me/submissions/bacc5fb3-bd3f-4dde-8fa6-db21faf318a0

import Mathlib
import Definitions.Def_ImplicitParityWL_Counter
import Definitions.Def_ImplicitParityWL_CheckMatrix

open ImplicitParityWL

namespace Aux_lemma_6_1

lemma address_supp_card {k ℓ : ℕ} (a : Address k ℓ) : a.supp.card = k := by
  unfold Address.supp
  rw [Finset.card_image_of_injective _ (fun i j h => (Prod.mk.inj h).1), Finset.card_fin]

lemma prefixDom_fixed_row {k ℓ j : ℕ} (hk : 3 ≤ k) {c : Coord k ℓ}
    (hc : c ∈ prefixDom k ℓ j) {r : Fin ℓ} (hr : r.val < j / (k - 1)) :
    c.2 r = ∑ p : Fin (k - 1), checkMatrix k ℓ (Sum.inl p) c := by
  classical
  simp only [prefixDom, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  obtain ⟨a, ha_pref, hc_supp⟩ := hc
  unfold Address.supp at hc_supp
  obtain ⟨i₀, _, rfl⟩ := Finset.mem_image.mp hc_supp
  have hdata_one : ∀ i : Fin k, i.val + 1 < k → a.1 i r = 1 := by
    intro i hi
    apply (ha_pref i r hi).1
    unfold dataPos
    have hmul : (r.val + 1) * (k - 1) ≤ (j / (k - 1)) * (k - 1) :=
      Nat.mul_le_mul_right (k - 1) hr
    have hdiv : (j / (k - 1)) * (k - 1) ≤ j := Nat.div_mul_le_self j (k - 1)
    have hexp : (r.val + 1) * (k - 1) = r.val * (k - 1) + (k - 1) := by ring
    omega
  change a.1 i₀ r = ∑ p : Fin (k - 1), checkMatrix k ℓ (Sum.inl p) (i₀, a.1 i₀)
  by_cases hi₀ : i₀.val + 1 < k
  · rw [hdata_one i₀ hi₀]
    have hne_last : ¬ (i₀.val + 1 = k) := by omega
    let p₀ : Fin (k - 1) := ⟨i₀.val, by omega⟩
    have hsum : ∑ p : Fin (k - 1), checkMatrix k ℓ (Sum.inl p) (i₀, a.1 i₀) =
        ∑ p : Fin (k - 1), if p = p₀ then (1 : ZMod 2) else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      simp only [checkMatrix, hne_last, or_false]
      by_cases hp : p = p₀
      · subst hp; simp [p₀]
      · have hval : i₀.val ≠ p.val := fun h => hp (Fin.ext h.symm)
        simp [hp, hval]
    rw [hsum]
    simp
  · have hi₀_last : i₀.val + 1 = k := by omega
    have hsum_chk : ∑ p : Fin (k - 1), checkMatrix k ℓ (Sum.inl p) (i₀, a.1 i₀) =
        ((k - 1 : ℕ) : ZMod 2) := by
      have h1 : ∀ p : Fin (k - 1), checkMatrix k ℓ (Sum.inl p) (i₀, a.1 i₀) = 1 := by
        intro p
        simp [checkMatrix, hi₀_last]
      simp [h1]
    rw [hsum_chk]
    have ha_sum : ∑ i : Fin k, a.1 i r = 0 := by
      have := congrFun a.2 r
      simpa [Finset.sum_apply] using this
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)] at ha_sum
    have hrest : ∑ i ∈ Finset.univ.erase i₀, a.1 i r = ((k - 1 : ℕ) : ZMod 2) := by
      have hcongr : ∀ i ∈ Finset.univ.erase i₀, a.1 i r = 1 := by
        intro i hi
        have hne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
        have hval_ne : i.val ≠ i₀.val := fun h => hne (Fin.ext h)
        exact hdata_one i (by omega)
      rw [Finset.sum_congr rfl hcongr]
      simp
    rw [hrest] at ha_sum
    have hself := CharTwo.add_self_eq_zero ((k - 1 : ℕ) : ZMod 2)
    exact add_right_cancel (ha_sum.trans hself.symm)

lemma prefixDom_card_le {k ℓ j : ℕ} (hk : 3 ≤ k) (hj : j / (k - 1) ≤ ℓ) :
    (prefixDom k ℓ j).card ≤ k * 2 ^ (ℓ - j / (k - 1)) := by
  classical
  set rj := j / (k - 1)
  let proj : {c // c ∈ prefixDom k ℓ j} → Fin k × (Fin (ℓ - rj) → ZMod 2) :=
    fun c => (c.1.1, fun t => c.1.2 ⟨t.val + rj, by omega⟩)
  have hinj : Function.Injective proj := by
    intro c₁ c₂ heq
    rcases Prod.mk.inj heq with ⟨hi, ht⟩
    apply Subtype.ext
    apply Prod.ext hi
    ext r
    by_cases hr : r.val < rj
    · have h1 := prefixDom_fixed_row hk c₁.2 hr
      have h2 := prefixDom_fixed_row hk c₂.2 hr
      rw [h1, h2]
      apply Finset.sum_congr rfl
      intro p _
      simp [checkMatrix, hi]
    · have hge : rj ≤ r.val := by omega
      have ht' := congrFun ht ⟨r.val - rj, by omega⟩
      dsimp at ht'
      have hr_eq : (⟨r.val - rj + rj, by omega⟩ : Fin ℓ) = r :=
        Fin.ext (by dsimp; omega)
      simpa [hr_eq] using ht'
  have hle := Fintype.card_le_of_injective proj hinj
  simpa using hle

lemma prefixDom_rank_le {k ℓ j : ℕ} (hk : 3 ≤ k) (hj : j / (k - 1) ≤ ℓ) :
    (restrictedCheck (prefixDom k ℓ j)).rank ≤ (k - 1) + (ℓ - j / (k - 1)) := by
  classical
  set rj := j / (k - 1)
  let B := restrictedCheck (prefixDom k ℓ j)
  let π : ((Fin (k - 1) ⊕ Fin ℓ) → ZMod 2) →ₗ[ZMod 2] ((Fin (k - 1) ⊕ Fin (ℓ - rj)) → ZMod 2) :=
    { toFun := fun y s => match s with
        | Sum.inl p => y (Sum.inl p)
        | Sum.inr t => y (Sum.inr ⟨t.val + rj, by omega⟩)
      map_add' := fun y₁ y₂ => by ext s; cases s <;> rfl
      map_smul' := fun a y => by ext s; cases s <;> rfl }
  let f := π.comp (LinearMap.range B.mulVecLin).subtype
  have hrel : ∀ y ∈ LinearMap.range B.mulVecLin, ∀ r : Fin ℓ, r.val < rj →
      y (Sum.inr r) = ∑ p : Fin (k - 1), y (Sum.inl p) := by
    rintro _ ⟨v, rfl⟩ r hr
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, B, restrictedCheck,
      Matrix.submatrix_apply, id_eq]
    have hrow : ∀ c : {c // c ∈ prefixDom k ℓ j},
        checkMatrix k ℓ (Sum.inr r) c.1 * v c =
          ∑ p : Fin (k - 1), checkMatrix k ℓ (Sum.inl p) c.1 * v c := by
      intro c
      have hfix := prefixDom_fixed_row hk c.2 hr
      change c.1.2 r * v c = _
      rw [hfix, Finset.sum_mul]
    simp_rw [hrow]
    exact Finset.sum_comm
  have hf_inj : Function.Injective f := by
    intro y₁ y₂ heq
    apply Subtype.ext
    ext s
    cases s with
    | inl p =>
      exact congrFun heq (Sum.inl p)
    | inr r =>
      by_cases hr : r.val < rj
      · rw [hrel y₁.1 y₁.2 r hr, hrel y₂.1 y₂.2 r hr]
        apply Finset.sum_congr rfl
        intro p _
        exact congrFun heq (Sum.inl p)
      · have hge : rj ≤ r.val := by omega
        have ht := congrFun heq (Sum.inr ⟨r.val - rj, by omega⟩)
        dsimp [f, π] at ht
        have hr_eq : (⟨r.val - rj + rj, by omega⟩ : Fin ℓ) = r :=
          Fin.ext (by dsimp; omega)
        simpa [hr_eq] using ht
  have hfr := LinearMap.finrank_le_finrank_of_injective hf_inj
  have hcod : Module.finrank (ZMod 2) ((Fin (k - 1) ⊕ Fin (ℓ - rj)) → ZMod 2) =
      (k - 1) + (ℓ - rj) := by
    rw [Module.finrank_pi, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  exact hfr.trans_eq hcod

lemma restrictedCheck_rank_le_card {k ℓ : ℕ} (dom : Finset (Coord k ℓ)) :
    (restrictedCheck dom).rank ≤ dom.card := by
  classical
  have h := LinearMap.finrank_range_le (restrictedCheck dom).mulVecLin
  have hdom : Module.finrank (ZMod 2) ({c // c ∈ dom} → ZMod 2) = dom.card := by
    rw [Module.finrank_pi, Fintype.card_coe]
  exact h.trans_eq hdom

lemma sum_two_pow_sub_le : ∀ ℓ : ℕ, ∑ r : Fin ℓ, 2 ^ (ℓ - r.val) ≤ 2 * 2 ^ ℓ
  | 0 => by simp
  | ℓ + 1 => by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ, Nat.succ_sub_succ_eq_sub]
    have ih := sum_two_pow_sub_le ℓ
    have hpow : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by ring
    omega

lemma sum_fin_mul_two_pow (d ℓ : ℕ) (hd : 0 < d) :
    ∑ j : Fin (d * ℓ), 2 ^ (ℓ - j.val / d) ≤ 2 * d * 2 ^ ℓ := by
  let eqv : Fin ℓ × Fin d ≃ Fin (d * ℓ) :=
    { toFun := fun ⟨r, i⟩ => ⟨r.val * d + i.val, by
        have hr := r.isLt
        have hi := i.isLt
        have h1 : (r.val + 1) * d ≤ ℓ * d := Nat.mul_le_mul_right d hr
        have h2 : (r.val + 1) * d = r.val * d + d := by ring
        have h3 : ℓ * d = d * ℓ := Nat.mul_comm ℓ d
        omega⟩
      invFun := fun j =>
        (⟨j.val / d, (Nat.div_lt_iff_lt_mul hd).mpr (j.isLt.trans_eq (Nat.mul_comm d ℓ))⟩,
         ⟨j.val % d, Nat.mod_lt j.val hd⟩)
      left_inv := fun ⟨r, i⟩ => by
        have hdiv : (r.val * d + i.val) / d = r.val := by
          rw [Nat.mul_comm, Nat.mul_add_div hd, Nat.div_eq_of_lt i.isLt, add_zero]
        have hmod : (r.val * d + i.val) % d = i.val := by
          rw [Nat.mul_add_mod', Nat.mod_eq_of_lt i.isLt]
        ext <;> dsimp <;> assumption
      right_inv := fun j => by
        apply Fin.ext
        dsimp
        have h := Nat.div_add_mod j.val d
        rw [Nat.mul_comm] at h
        exact h }
  have heq : ∑ j : Fin (d * ℓ), 2 ^ (ℓ - j.val / d) =
      ∑ p : Fin ℓ × Fin d, 2 ^ (ℓ - p.1.val) := by
    rw [← Fintype.sum_equiv eqv]
    intro ⟨r, i⟩
    dsimp [eqv]
    have hdiv : (r.val * d + i.val) / d = r.val := by
      rw [Nat.mul_comm, Nat.mul_add_div hd, Nat.div_eq_of_lt i.isLt, add_zero]
    rw [hdiv]
  rw [heq, Fintype.sum_prod_type]
  simp_rw [Finset.sum_const, Finset.card_fin, smul_eq_mul]
  calc ∑ r : Fin ℓ, d * 2 ^ (ℓ - r.val)
      = d * ∑ r : Fin ℓ, 2 ^ (ℓ - r.val) := (Finset.mul_sum _ _ _).symm
    _ ≤ d * (2 * 2 ^ ℓ) := Nat.mul_le_mul_left d (sum_two_pow_sub_le ℓ)
    _ = 2 * d * 2 ^ ℓ := by ring

end Aux_lemma_6_1

theorem solution (k : ℕ) (hk : 3 ≤ k) : ∃ C : ℕ, ∀ ℓ : ℕ, 1 ≤ ℓ →
    ∑ v : CounterLoc ((k - 1) * ℓ), ((counter k ℓ).dom v).card +
      ∑ e : CounterSchema ((k - 1) * ℓ),
        (((counter k ℓ).schema e).dom.card +
          2 ^ (restrictedCheck ((counter k ℓ).schema e).dom).rank) ≤ C * 2 ^ ℓ := by
  classical
  let C : ℕ := k + 4 * k + 2 * 2 ^ k + 2 * (k - 1) * (5 * k + 3 * 2 ^ (k - 1))
  refine ⟨C, fun ℓ _hℓ => ?_⟩
  set m := (k - 1) * ℓ
  have hd : 0 < k - 1 := by omega
  have hj_le : ∀ j : Fin m, j.val / (k - 1) ≤ ℓ := by
    intro j
    have hlt : j.val < ℓ * (k - 1) := by rw [Nat.mul_comm]; exact j.isLt
    exact Nat.le_of_lt ((Nat.div_lt_iff_lt_mul hd).mpr hlt)
  have hloc : ∑ v : CounterLoc m, ((counter k ℓ).dom v).card =
      k * 2 ^ ℓ + 2 * k + 2 * ∑ j : Fin m, (prefixDom k ℓ j.val).card := by
    have hcard_univ : (Finset.univ : Finset (Coord k ℓ)).card = k * 2 ^ ℓ := by
      simp [Coord, BlockCoord]
    have hs_card : (counterStart k ℓ).supp.card = k := Aux_lemma_6_1.address_supp_card _
    have ht_card : (counterEnd k ℓ).supp.card = k := Aux_lemma_6_1.address_supp_card _
    let eLoc : (Unit ⊕ Unit ⊕ Unit ⊕ Fin m ⊕ Fin m) ≃ CounterLoc m :=
      { toFun := fun
          | Sum.inl _ => .main
          | Sum.inr (Sum.inl _) => .z0
          | Sum.inr (Sum.inr (Sum.inl _)) => .z1
          | Sum.inr (Sum.inr (Sum.inr (Sum.inl j))) => .p j
          | Sum.inr (Sum.inr (Sum.inr (Sum.inr j))) => .q j
        invFun := fun
          | .main => Sum.inl ()
          | .z0 => Sum.inr (Sum.inl ())
          | .z1 => Sum.inr (Sum.inr (Sum.inl ()))
          | .p j => Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))
          | .q j => Sum.inr (Sum.inr (Sum.inr (Sum.inr j)))
        left_inv := fun x => by rcases x with _ | _ | _ | j | j <;> rfl
        right_inv := fun v => by cases v <;> rfl }
    rw [← Fintype.sum_equiv eLoc _ (fun v => ((counter k ℓ).dom v).card) (fun _ => rfl)]
    simp only [Fintype.sum_sum_type, Fintype.sum_unique, eLoc, Equiv.coe_fn_mk,
      counter, counterDom, hcard_univ, hs_card, ht_card]
    ring
  have hsch : ∑ e : CounterSchema m, (((counter k ℓ).schema e).dom.card +
        2 ^ (restrictedCheck ((counter k ℓ).schema e).dom).rank) ≤
      2 * k + 2 * 2 ^ k +
        ∑ j : Fin m, (3 * (prefixDom k ℓ j.val).card +
          3 * 2 ^ (restrictedCheck (prefixDom k ℓ j.val)).rank) := by
    let eSch : (Unit ⊕ Unit ⊕ Fin m ⊕ Fin m ⊕ Fin m) ≃ CounterSchema m :=
      { toFun := fun
          | Sum.inl _ => .start
          | Sum.inr (Sum.inl _) => .stop
          | Sum.inr (Sum.inr (Sum.inl j)) => .vp j
          | Sum.inr (Sum.inr (Sum.inr (Sum.inl j))) => .pq j
          | Sum.inr (Sum.inr (Sum.inr (Sum.inr j))) => .qv j
        invFun := fun
          | .start => Sum.inl ()
          | .stop => Sum.inr (Sum.inl ())
          | .vp j => Sum.inr (Sum.inr (Sum.inl j))
          | .pq j => Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))
          | .qv j => Sum.inr (Sum.inr (Sum.inr (Sum.inr j)))
        left_inv := fun x => by rcases x with _ | _ | j | j | j <;> rfl
        right_inv := fun e => by cases e <;> rfl }
    rw [← Fintype.sum_equiv eSch _
      (fun e => ((counter k ℓ).schema e).dom.card +
        2 ^ (restrictedCheck ((counter k ℓ).schema e).dom).rank) (fun _ => rfl)]
    simp only [Fintype.sum_sum_type, Fintype.sum_unique]
    change ((counterStart k ℓ).supp.card + 2 ^ (restrictedCheck (counterStart k ℓ).supp).rank) +
      (((counterEnd k ℓ).supp.card + 2 ^ (restrictedCheck (counterEnd k ℓ).supp).rank) +
        ((∑ j : Fin m, ((prefixDom k ℓ j.val).card + 2 ^ (restrictedCheck (prefixDom k ℓ j.val)).rank)) +
          ((∑ j : Fin m, ((prefixDom k ℓ j.val).card + 2 ^ (restrictedCheck (prefixDom k ℓ j.val)).rank)) +
           (∑ j : Fin m, ((prefixDom k ℓ j.val).card + 2 ^ (restrictedCheck (prefixDom k ℓ j.val)).rank))))) ≤ _
    have hs_card : (counterStart k ℓ).supp.card = k := Aux_lemma_6_1.address_supp_card _
    have ht_card : (counterEnd k ℓ).supp.card = k := Aux_lemma_6_1.address_supp_card _
    have hs_rk : 2 ^ (restrictedCheck (counterStart k ℓ).supp).rank ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by omega)
        ((Aux_lemma_6_1.restrictedCheck_rank_le_card _).trans_eq hs_card)
    have ht_rk : 2 ^ (restrictedCheck (counterEnd k ℓ).supp).rank ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by omega)
        ((Aux_lemma_6_1.restrictedCheck_rank_le_card _).trans_eq ht_card)
    rw [hs_card, ht_card]
    have hcomb : (∑ j : Fin m, ((prefixDom k ℓ j.val).card +
          2 ^ (restrictedCheck (prefixDom k ℓ j.val)).rank)) +
        ((∑ j : Fin m, ((prefixDom k ℓ j.val).card +
          2 ^ (restrictedCheck (prefixDom k ℓ j.val)).rank)) +
         (∑ j : Fin m, ((prefixDom k ℓ j.val).card +
          2 ^ (restrictedCheck (prefixDom k ℓ j.val)).rank))) =
        ∑ j : Fin m, (3 * (prefixDom k ℓ j.val).card +
          3 * 2 ^ (restrictedCheck (prefixDom k ℓ j.val)).rank) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hcomb]
    linarith
  have hj_term : ∀ j : Fin m,
      2 * (prefixDom k ℓ j.val).card +
        (3 * (prefixDom k ℓ j.val).card +
          3 * 2 ^ (restrictedCheck (prefixDom k ℓ j.val)).rank) ≤
      (5 * k + 3 * 2 ^ (k - 1)) * 2 ^ (ℓ - j.val / (k - 1)) := by
    intro j
    have hc := Aux_lemma_6_1.prefixDom_card_le hk (hj_le j)
    have hrk := Aux_lemma_6_1.prefixDom_rank_le hk (hj_le j)
    have hpow : 2 ^ (restrictedCheck (prefixDom k ℓ j.val)).rank ≤
        2 ^ (k - 1) * 2 ^ (ℓ - j.val / (k - 1)) := by
      rw [← Nat.pow_add]
      exact Nat.pow_le_pow_right (by omega) hrk
    nlinarith
  have hsum_j : 2 * ∑ j : Fin m, (prefixDom k ℓ j.val).card +
      ∑ j : Fin m, (3 * (prefixDom k ℓ j.val).card +
        3 * 2 ^ (restrictedCheck (prefixDom k ℓ j.val)).rank) ≤
      2 * (k - 1) * (5 * k + 3 * 2 ^ (k - 1)) * 2 ^ ℓ := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    calc ∑ j : Fin m, (2 * (prefixDom k ℓ j.val).card +
          (3 * (prefixDom k ℓ j.val).card +
            3 * 2 ^ (restrictedCheck (prefixDom k ℓ j.val)).rank))
        ≤ ∑ j : Fin m, (5 * k + 3 * 2 ^ (k - 1)) * 2 ^ (ℓ - j.val / (k - 1)) :=
          Finset.sum_le_sum (fun j _ => hj_term j)
      _ = (5 * k + 3 * 2 ^ (k - 1)) * ∑ j : Fin m, 2 ^ (ℓ - j.val / (k - 1)) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ (5 * k + 3 * 2 ^ (k - 1)) * (2 * (k - 1) * 2 ^ ℓ) :=
          Nat.mul_le_mul_left _ (Aux_lemma_6_1.sum_fin_mul_two_pow (k - 1) ℓ hd)
      _ = 2 * (k - 1) * (5 * k + 3 * 2 ^ (k - 1)) * 2 ^ ℓ := by ring
  have h2ℓ_ge1 : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  rw [hloc]
  have hconst : 4 * k + 2 * 2 ^ k ≤ (4 * k + 2 * 2 ^ k) * 2 ^ ℓ :=
    Nat.le_mul_of_pos_right _ h2ℓ_ge1
  dsimp [C]
  nlinarith
