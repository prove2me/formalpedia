-- Prove2me | solution 1 for MvPowerSeries.subst_add_sum_smul_eq_add_sum_smul_mul_subst_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/df8e6259-38c3-5951-973f-4a2e89f0169c

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Theorems.Thm_MvPowerSeries_coeff_sumElim_single_subst_add_sum_X_mul_eq
import Theorems.Thm_MvPowerSeries_coeff_sumElim_zero_subst_add_sum_X_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_subst_add_sum_smul_eq_add_sum_smul_mul_subst_pderiv

set_option autoImplicit false

open MvPowerSeries

theorem K1Aux_prod_pow_eq_zero {R κ : Type} [CommRing R] (j : κ → R) (hj : ∀ k k', j k * j k' = 0)
    (d : κ →₀ ℕ) (hd : 2 ≤ d.degree) : d.prod (fun k e => j k ^ e) = 0 := by
  classical
  rw [Finsupp.prod]
  by_cases h2 : ∃ k ∈ d.support, 2 ≤ d k
  · obtain ⟨k, hk, hk2⟩ := h2
    apply Finset.prod_eq_zero hk
    obtain ⟨e, he⟩ : ∃ e, d k = e + 2 := ⟨d k - 2, by omega⟩
    rw [he, pow_add, pow_two, hj, mul_zero]
  · push_neg at h2
    have h1 : ∀ k ∈ d.support, d k = 1 := fun k hk =>
      le_antisymm (Nat.lt_succ_iff.mp (h2 k hk)) (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hk))
    have hcard : 2 ≤ d.support.card := by
      have : d.degree = ∑ k ∈ d.support, d k := Finsupp.degree_apply d
      rw [this, Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_one] at hd
      exact hd
    obtain ⟨k₁, hk₁, k₂, hk₂, hne⟩ := Finset.one_lt_card.mp hcard
    rw [← Finset.mul_prod_erase _ _ hk₁, ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hne.symm, hk₂⟩),
      h1 k₁ hk₁, h1 k₂ hk₂, pow_one, pow_one, ← mul_assoc, hj, zero_mul]

theorem K1Aux_eq_zero_or_single {κ : Type} (d : κ →₀ ℕ) (hd : d.degree < 2) :
    d = 0 ∨ ∃ k, d = Finsupp.single k 1 := by
  classical
  rcases Nat.lt_succ_iff.mp hd |>.eq_or_lt with h1 | h0
  · right
    have hne : d ≠ 0 := by intro h; rw [h, map_zero] at h1; exact zero_ne_one h1
    obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.mpr hne
    have hk1 : d k = 1 := by
      have hle : d k ≤ 1 := h1 ▸ Finsupp.le_degree k d
      have hpos : d k ≠ 0 := Finsupp.mem_support_iff.mp hk
      omega
    refine ⟨k, ?_⟩
    have hsplit : d = Finsupp.single k 1 + (d - Finsupp.single k 1) := by
      ext i
      simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
      split_ifs with hki
      · subst hki; omega
      · omega
    have hdeg : (d - Finsupp.single k 1).degree = 0 := by
      have := congrArg Finsupp.degree hsplit
      rw [map_add, Finsupp.degree_single, h1] at this
      omega
    rw [(Finsupp.degree_eq_zero_iff _).mp hdeg, add_zero] at hsplit
    exact hsplit
  · left
    exact (Finsupp.degree_eq_zero_iff _).mp (by omega)

theorem K1Aux_prod_X_pow {R τ : Type} [CommRing R] (d : τ →₀ ℕ) :
    d.prod (fun t e => (MvPowerSeries.X t : MvPowerSeries τ R) ^ e) = MvPowerSeries.monomial d 1 := by
  classical
  induction d using Finsupp.induction with
  | zero => rw [Finsupp.prod_zero_index, MvPowerSeries.monomial_zero_one]
  | single_add a b f ha hb ih =>
    have hs : (Finsupp.single a b).prod (fun t e => (MvPowerSeries.X t : MvPowerSeries τ R) ^ e) = MvPowerSeries.X a ^ b :=
      Finsupp.prod_single_index (pow_zero _)
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), hs, ih,
      MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul]

theorem K1Aux_coeff_subst_elim {R τ κ : Type} [CommRing R] [Fintype τ] [Fintype κ]
    (j : κ → R) (hj : ∀ k k', j k * j k' = 0) (F : MvPowerSeries (τ ⊕ κ) R) (m : τ →₀ ℕ) :
    MvPowerSeries.coeff m (MvPowerSeries.subst (Sum.elim (fun t => (MvPowerSeries.X t : MvPowerSeries τ R)) (fun k => MvPowerSeries.C (j k))) F) =
      MvPowerSeries.coeff (m.sumElim 0) F + ∑ k, j k * MvPowerSeries.coeff (m.sumElim (Finsupp.single k 1)) F := by
  classical
  have hEs : MvPowerSeries.HasSubst (Sum.elim (fun t => (MvPowerSeries.X t : MvPowerSeries τ R)) (fun k => MvPowerSeries.C (j k))) :=
    MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (by
      rintro (t | k)
      · show IsNilpotent (MvPowerSeries.constantCoeff (MvPowerSeries.X t : MvPowerSeries τ R))
        rw [MvPowerSeries.constantCoeff_X]; exact IsNilpotent.zero
      · show IsNilpotent (MvPowerSeries.constantCoeff (MvPowerSeries.C (j k) : MvPowerSeries τ R))
        rw [MvPowerSeries.constantCoeff_C]; exact ⟨2, by rw [pow_two]; exact hj k k⟩)
  rw [MvPowerSeries.coeff_subst hEs F m,
    ← finsum_comp_equiv (Finsupp.sumFinsuppAddEquivProdFinsupp (α := τ) (β := κ) (M := ℕ)).symm.toEquiv]
  have hterm : ∀ p : (τ →₀ ℕ) × (κ →₀ ℕ),
      MvPowerSeries.coeff ((Finsupp.sumFinsuppAddEquivProdFinsupp (α := τ) (β := κ) (M := ℕ)).symm.toEquiv p) F •
        MvPowerSeries.coeff m (((Finsupp.sumFinsuppAddEquivProdFinsupp (α := τ) (β := κ) (M := ℕ)).symm.toEquiv p).prod
          fun s e => (Sum.elim (fun t => (MvPowerSeries.X t : MvPowerSeries τ R)) (fun k => MvPowerSeries.C (j k))) s ^ e) =
      if m = p.1 then MvPowerSeries.coeff (p.1.sumElim p.2) F * p.2.prod (fun k e => j k ^ e) else 0 := by
    intro p
    show MvPowerSeries.coeff (p.1.sumElim p.2) F • MvPowerSeries.coeff m ((p.1.sumElim p.2).prod fun s e => (Sum.elim (fun t => (MvPowerSeries.X t : MvPowerSeries τ R)) (fun k => MvPowerSeries.C (j k))) s ^ e) = _
    rw [Finsupp.prod_sumElim]
    have h1 : p.1.prod ((fun s e => (Sum.elim (fun t => (MvPowerSeries.X t : MvPowerSeries τ R)) (fun k => MvPowerSeries.C (j k))) s ^ e) ∘ Sum.inl) = MvPowerSeries.monomial p.1 1 := K1Aux_prod_X_pow p.1
    have h2 : p.2.prod ((fun s e => (Sum.elim (fun t => (MvPowerSeries.X t : MvPowerSeries τ R)) (fun k => MvPowerSeries.C (j k))) s ^ e) ∘ Sum.inr) = MvPowerSeries.C (p.2.prod fun k e => j k ^ e) := by
      show p.2.prod (fun k e => (MvPowerSeries.C (j k) : MvPowerSeries τ R) ^ e) = _
      rw [Finsupp.prod, Finsupp.prod, map_prod]
      exact Finset.prod_congr rfl (fun k _ => (map_pow _ _ _).symm)
    rw [h1, h2, mul_comm, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_monomial, smul_eq_mul]
    split_ifs with h
    · ring
    · rw [mul_zero, mul_zero]
  rw [finsum_congr hterm]

  let emb : Option κ → (τ →₀ ℕ) × (κ →₀ ℕ) := fun o => (m, o.elim (0 : κ →₀ ℕ) fun k => Finsupp.single k 1)
  have hemb : Function.Injective emb := by
    intro o o' h
    have h2 := congrArg Prod.snd h
    cases o with
    | none => cases o' with
      | none => rfl
      | some k' => exact absurd h2.symm (Finsupp.single_ne_zero.mpr one_ne_zero)
    | some k => cases o' with
      | none => exact absurd h2 (Finsupp.single_ne_zero.mpr one_ne_zero)
      | some k' => exact congrArg some (Finsupp.single_left_injective one_ne_zero h2)
  have hsupp : Function.support (fun p : (τ →₀ ℕ) × (κ →₀ ℕ) =>
      if m = p.1 then MvPowerSeries.coeff (p.1.sumElim p.2) F * p.2.prod (fun k e => j k ^ e) else 0) ⊆
      ↑((Finset.univ : Finset (Option κ)).image emb) := by
    intro p hp
    rw [Function.mem_support] at hp
    split_ifs at hp with h
    · have hJ : p.2.prod (fun k e => j k ^ e) ≠ 0 := fun h0 => hp (by rw [h0, mul_zero])
      have hdeg : p.2.degree < 2 := by
        by_contra hc; push_neg at hc; exact hJ (K1Aux_prod_pow_eq_zero j hj p.2 hc)
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
      rcases K1Aux_eq_zero_or_single p.2 hdeg with h0 | ⟨k, hk⟩
      · exact ⟨none, Prod.ext h (by simp [emb, h0])⟩
      · exact ⟨some k, Prod.ext h (by simp [emb, hk])⟩
    · exact absurd rfl hp
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image (fun o _ o' _ h => hemb h), Fintype.sum_option]
  have hsingle : ∀ k : κ, (Finsupp.single k 1).prod (fun k e => j k ^ e) = j k ^ 1 := fun k =>
    Finsupp.prod_single_index (pow_zero _)
  simp only [emb, Option.elim, if_true, eq_self_iff_true, Finsupp.prod_zero_index, mul_one]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hsingle, pow_one, mul_comm]

theorem solution
    {R : Type} [CommRing R] {σ : Type} [Fintype σ] {τ : Type} [Fintype τ] {κ : Type} [Fintype κ]
    (j : κ → R) (hj : ∀ k k', j k * j k' = 0)
    (f : MvPowerSeries σ R)
    (A : σ → MvPowerSeries τ R) (hA : ∀ i, MvPowerSeries.constantCoeff (A i) = 0)
    (B : σ → κ → MvPowerSeries τ R) :
    MvPowerSeries.subst (fun i => A i + ∑ k, j k • B i k) f =
      MvPowerSeries.subst A f + ∑ k, j k • ∑ i, B i k * MvPowerSeries.subst A (MvPowerSeries.pderivLin i f) := by
  classical

  let ι : τ → MvPowerSeries (τ ⊕ κ) R := fun t => MvPowerSeries.X (Sum.inl t)
  have hι : MvPowerSeries.HasSubst ι := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun t => MvPowerSeries.constantCoeff_X _)
  let G : σ → MvPowerSeries (τ ⊕ κ) R := fun i =>
    MvPowerSeries.subst ι (A i) + ∑ k', MvPowerSeries.X (Sum.inr k') * MvPowerSeries.subst ι (B i k')
  have hG0 : ∀ i, MvPowerSeries.constantCoeff (G i) = 0 := by
    intro i
    show MvPowerSeries.constantCoeff (MvPowerSeries.subst ι (A i) + ∑ k', MvPowerSeries.X (Sum.inr k') * MvPowerSeries.subst ι (B i k')) = 0
    rw [map_add, map_sum, MvPowerSeries.constantCoeff_subst_eq_zero hι (fun t => MvPowerSeries.constantCoeff_X _) (hA i), zero_add]
    exact Finset.sum_eq_zero (fun k' _ => MvPowerSeries.coeff_zero_X_mul _ _)
  have hG : MvPowerSeries.HasSubst G := MvPowerSeries.hasSubst_of_constantCoeff_zero hG0
  have hEs : MvPowerSeries.HasSubst (Sum.elim (fun t => (MvPowerSeries.X t : MvPowerSeries τ R)) (fun k => MvPowerSeries.C (j k))) :=
    MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (by
      rintro (t | k)
      · show IsNilpotent (MvPowerSeries.constantCoeff (MvPowerSeries.X t : MvPowerSeries τ R))
        rw [MvPowerSeries.constantCoeff_X]; exact IsNilpotent.zero
      · show IsNilpotent (MvPowerSeries.constantCoeff (MvPowerSeries.C (j k) : MvPowerSeries τ R))
        rw [MvPowerSeries.constantCoeff_C]; exact ⟨2, by rw [pow_two]; exact hj k k⟩)

  have hEι : ∀ g : MvPowerSeries τ R, MvPowerSeries.subst (Sum.elim (fun t => (MvPowerSeries.X t : MvPowerSeries τ R)) (fun k => MvPowerSeries.C (j k))) (MvPowerSeries.subst ι g) = g := by
    intro g
    rw [MvPowerSeries.subst_comp_subst_apply hι hEs]
    have : (fun t => MvPowerSeries.subst (Sum.elim (fun t => (MvPowerSeries.X t : MvPowerSeries τ R)) (fun k => MvPowerSeries.C (j k))) (ι t)) = MvPowerSeries.X := by
      funext t; exact MvPowerSeries.subst_X hEs (Sum.inl t)
    rw [this, MvPowerSeries.subst_self]; rfl
  have hEG : ∀ i, MvPowerSeries.subst (Sum.elim (fun t => (MvPowerSeries.X t : MvPowerSeries τ R)) (fun k => MvPowerSeries.C (j k))) (G i) = A i + ∑ k, j k • B i k := by
    intro i
    show MvPowerSeries.subst (Sum.elim (fun t => (MvPowerSeries.X t : MvPowerSeries τ R)) (fun k => MvPowerSeries.C (j k))) (MvPowerSeries.subst ι (A i) + ∑ k', MvPowerSeries.X (Sum.inr k') * MvPowerSeries.subst ι (B i k')) = _
    rw [← MvPowerSeries.coe_substAlgHom hEs, map_add, map_sum]
    simp only [map_mul, MvPowerSeries.coe_substAlgHom]
    rw [hEι]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [MvPowerSeries.subst_X hEs, hEι, MvPowerSeries.smul_eq_C_mul]
    rfl

  have hL : MvPowerSeries.subst (fun i => A i + ∑ k, j k • B i k) f =
      MvPowerSeries.subst (Sum.elim (fun t => (MvPowerSeries.X t : MvPowerSeries τ R)) (fun k => MvPowerSeries.C (j k))) (MvPowerSeries.subst G f) := by
    rw [MvPowerSeries.subst_comp_subst_apply hG hEs]
    congr 1
    funext i
    exact (hEG i).symm
  rw [hL]
  ext m
  rw [K1Aux_coeff_subst_elim j hj (MvPowerSeries.subst G f) m,
    MvPowerSeries.coeff_sumElim_zero_subst_add_sum_X_mul_eq f A hA B m, map_add, map_sum]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [MvPowerSeries.coeff_sumElim_single_subst_add_sum_X_mul_eq f (fun i => MvPowerSeries.pderivLin i f) ?_ A hA B m k,
    MvPowerSeries.coeff_smul]
  intro i n
  rw [MvPowerSeries.kw_coeff_pderiv, nsmul_eq_mul]

end S_MvPowerSeries_subst_add_sum_smul_eq_add_sum_smul_mul_subst_pderiv
end P2MW
export P2MW.S_MvPowerSeries_subst_add_sum_smul_eq_add_sum_smul_mul_subst_pderiv (solution)
