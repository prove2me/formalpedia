-- Prove2me | solution 1 for HararySachs.Hyper.newtonTr_two_gradings
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-13T04:05:40.64018+00:00
-- url     : https://prove2.me/submissions/17430848-b86c-4184-8ae7-daff97733c9f

import Mathlib
import Definitions.Def_HararySachs_Hyper_TensorPhi
import Definitions.Def_HararySachs_Hyper_RowProj

open HararySachs.Hyper Finset

namespace TwoGradAux

variable {σ : Type*}

/-! ### Euler operators and graded components on `MvPowerSeries σ ℚ` -/

/-- the Euler operator of a grading `ω`: multiplies the coefficient of `μ` by `ω μ` -/
noncomputable def eul (ω : (σ →₀ ℕ) →+ ℕ) (f : MvPowerSeries σ ℚ) : MvPowerSeries σ ℚ :=
  fun μ => (ω μ : ℚ) * MvPowerSeries.coeff μ f

/-- the `ω`-graded component of degree `m` -/
noncomputable def comp (ω : (σ →₀ ℕ) →+ ℕ) (m : ℕ) (f : MvPowerSeries σ ℚ) :
    MvPowerSeries σ ℚ :=
  fun μ => if ω μ = m then MvPowerSeries.coeff μ f else 0

variable (ω ω' : (σ →₀ ℕ) →+ ℕ)

lemma coeff_eul (f : MvPowerSeries σ ℚ) (μ : σ →₀ ℕ) :
    MvPowerSeries.coeff μ (eul ω f) = (ω μ : ℚ) * MvPowerSeries.coeff μ f := rfl

lemma coeff_comp (m : ℕ) (f : MvPowerSeries σ ℚ) (μ : σ →₀ ℕ) :
    MvPowerSeries.coeff μ (comp ω m f) = if ω μ = m then MvPowerSeries.coeff μ f else 0 := rfl

lemma coeff_natCast_mul (n : ℕ) (f : MvPowerSeries σ ℚ) (μ : σ →₀ ℕ) :
    MvPowerSeries.coeff μ ((n : MvPowerSeries σ ℚ) * f) = (n : ℚ) * MvPowerSeries.coeff μ f := by
  rw [← map_natCast (MvPowerSeries.C (σ := σ) (R := ℚ)) n, MvPowerSeries.coeff_C_mul]

lemma eul_sub (f g : MvPowerSeries σ ℚ) : eul ω (f - g) = eul ω f - eul ω g := by
  ext μ; simp only [coeff_eul, map_sub, mul_sub]

lemma eul_mul (f g : MvPowerSeries σ ℚ) : eul ω (f * g) = eul ω f * g + f * eul ω g := by
  classical
  ext μ
  rw [coeff_eul, map_add, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul,
    MvPowerSeries.coeff_mul, ← sum_add_distrib, mul_sum]
  refine sum_congr rfl fun p hp => ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  rw [coeff_eul, coeff_eul, ← hp, map_add]
  push_cast; ring

lemma eul_comm (f : MvPowerSeries σ ℚ) : eul ω (eul ω' f) = eul ω' (eul ω f) := by
  ext μ; simp only [coeff_eul]; ring

lemma comp_eul_self (m : ℕ) (f : MvPowerSeries σ ℚ) :
    comp ω m (eul ω f) = (m : MvPowerSeries σ ℚ) * comp ω m f := by
  ext μ
  rw [coeff_natCast_mul]
  simp only [coeff_comp, coeff_eul]
  split_ifs with h
  · rw [h]
  · simp

lemma comp_sub (m : ℕ) (f g : MvPowerSeries σ ℚ) :
    comp ω m (f - g) = comp ω m f - comp ω m g := by
  ext μ; simp only [coeff_comp, map_sub]; split_ifs <;> simp

lemma comp_neg (m : ℕ) (f : MvPowerSeries σ ℚ) : comp ω m (-f) = -comp ω m f := by
  ext μ; simp only [coeff_comp, map_neg]; split_ifs <;> simp

lemma comp_comm (m n : ℕ) (f : MvPowerSeries σ ℚ) :
    comp ω m (comp ω' n f) = comp ω' n (comp ω m f) := by
  ext μ; simp only [coeff_comp]; split_ifs <;> rfl

lemma comp_natCast_mul (m n : ℕ) (f : MvPowerSeries σ ℚ) :
    comp ω m ((n : MvPowerSeries σ ℚ) * f) = (n : MvPowerSeries σ ℚ) * comp ω m f := by
  ext μ; rw [coeff_natCast_mul]; simp only [coeff_comp, coeff_natCast_mul]; split_ifs <;> simp

lemma comp_C_mul (m : ℕ) (r : ℚ) (f : MvPowerSeries σ ℚ) :
    comp ω m (MvPowerSeries.C r * f) = MvPowerSeries.C r * comp ω m f := by
  ext μ; rw [MvPowerSeries.coeff_C_mul]; simp only [coeff_comp, MvPowerSeries.coeff_C_mul]
  split_ifs <;> simp

lemma comp_mul (n : ℕ) (f g : MvPowerSeries σ ℚ) :
    comp ω n (f * g) = ∑ j ∈ range (n + 1), comp ω j f * comp ω (n - j) g := by
  classical
  ext μ
  rw [coeff_comp, map_sum]
  simp only [MvPowerSeries.coeff_mul, coeff_comp]
  rw [sum_comm]
  split_ifs with h
  · refine sum_congr rfl fun p hp => ?_
    rw [HasAntidiagonal.mem_antidiagonal] at hp
    have hs : ω p.1 + ω p.2 = n := by rw [← map_add, hp, h]
    rw [sum_eq_single (ω p.1)]
    · rw [if_pos rfl, if_pos (by omega)]
    · intro j _ hj; rw [if_neg (Ne.symm hj), zero_mul]
    · intro hj; exfalso; rw [mem_range] at hj; omega
  · symm
    refine sum_eq_zero fun p hp => sum_eq_zero fun j hj => ?_
    rw [HasAntidiagonal.mem_antidiagonal] at hp
    rw [mem_range] at hj
    have hs : ω p.1 + ω p.2 = ω μ := by rw [← map_add, hp]
    split_ifs with h1 h2 <;> first | omega | simp

lemma eq_zero_of_comp (f : MvPowerSeries σ ℚ) (h : ∀ n, comp ω n f = 0) : f = 0 := by
  ext μ
  have := congrArg (MvPowerSeries.coeff μ) (h (ω μ))
  simpa [coeff_comp] using this

/-- the degree grading -/
abbrev dg : (σ →₀ ℕ) →+ ℕ := Finsupp.degree

lemma comp_dg_zero_eul (f : MvPowerSeries σ ℚ) : comp dg 0 (eul ω f) = 0 := by
  ext μ
  rw [coeff_comp, coeff_eul, map_zero]
  split_ifs with h
  · rw [(Finsupp.degree_eq_zero_iff μ).mp h, map_zero, Nat.cast_zero, zero_mul]
  · rfl

/-! ### Polynomials inside power series -/

/-- the coercion of polynomials into power series, as a ring hom -/
noncomputable abbrev ι : MvPolynomial σ ℚ →+* MvPowerSeries σ ℚ :=
  MvPolynomial.coeToMvPowerSeries.ringHom

lemma coeff_ι (p : MvPolynomial σ ℚ) (μ : σ →₀ ℕ) :
    MvPowerSeries.coeff μ (ι p) = MvPolynomial.coeff μ p := by
  rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeff_coe]

lemma comp_dg_ι (n : ℕ) (p : MvPolynomial σ ℚ) :
    comp dg n (ι p) = ι (MvPolynomial.homogeneousComponent n p) := by
  ext μ
  rw [coeff_comp, coeff_ι, coeff_ι, MvPolynomial.coeff_homogeneousComponent]

lemma comp_wt_ι (w : σ → ℕ) (n : ℕ) (p : MvPolynomial σ ℚ) :
    comp (Finsupp.weight w) n (ι p) = ι (MvPolynomial.weightedHomogeneousComponent w n p) := by
  ext μ
  rw [coeff_comp, coeff_ι, coeff_ι, MvPolynomial.coeff_weightedHomogeneousComponent]

lemma ι_C (r : ℚ) : ι (MvPolynomial.C r : MvPolynomial σ ℚ) = MvPowerSeries.C r := by
  rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_C]

/-! ### Newton traces -/

lemma newton_all {R : Type*} [CommRing R] (Φ : Polynomial R) (h0 : Φ.coeff 0 = 1) (n : ℕ) :
    (n : R) * Φ.coeff n = -∑ j ∈ range (n + 1), newtonTr Φ j * Φ.coeff (n - j) := by
  cases n with
  | zero => simp [newtonTr]
  | succ e =>
    rw [sum_range_succ, Nat.sub_self, h0, mul_one, newtonTr.eq_2,
      ← Fin.sum_univ_eq_sum_range (fun j => newtonTr Φ j * Φ.coeff (e + 1 - j))]
    ring

lemma tau_hom (Φ : Polynomial (MvPolynomial σ ℚ)) (hΦ : ∀ j, (Φ.coeff j).IsHomogeneous j)
    (d : ℕ) : (newtonTr Φ d).IsHomogeneous d := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    cases d with
    | zero => rw [newtonTr]; exact MvPolynomial.isHomogeneous_zero _ _ _
    | succ d =>
      rw [newtonTr]
      refine MvPolynomial.IsHomogeneous.sub ?_ ?_
      · refine MvPolynomial.IsHomogeneous.neg ?_
        rw [← map_natCast (MvPolynomial.C : ℚ →+* MvPolynomial σ ℚ) (d + 1)]
        have := (MvPolynomial.isHomogeneous_C σ ((d + 1 : ℕ) : ℚ)).mul (hΦ (d + 1))
        rwa [zero_add] at this
      · refine MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ => ?_
        have := (ih j j.isLt).mul (hΦ (d + 1 - j))
        rwa [show (j : ℕ) + (d + 1 - j) = d + 1 by omega] at this

lemma coeff_hatPhi {R : Type*} [CommRing R] (C : R) (q : ℕ → R) (M j : ℕ) :
    (hatPhi C q M).coeff j = if j = 0 then 1 else if j ≤ M then C ^ (j - 1) * q j else 0 := by
  classical
  unfold hatPhi
  rw [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [sum_ite_eq']
  simp only [mem_Icc]
  split_ifs <;> first | omega | simp_all

/-- the logarithm `log Q = -∑_d τ_d / d`, graded by total degree -/
noncomputable def Lser (Φ : Polynomial (MvPolynomial σ ℚ)) : MvPowerSeries σ ℚ :=
  fun μ => -(1 / (dg μ : ℚ)) * MvPolynomial.coeff μ (newtonTr Φ (dg μ))

lemma comp_Lser (Φ : Polynomial (MvPolynomial σ ℚ)) (hΦ : ∀ j, (Φ.coeff j).IsHomogeneous j)
    (n : ℕ) : comp dg n (Lser Φ) = MvPowerSeries.C (-(1 / (n : ℚ))) * ι (newtonTr Φ n) := by
  ext μ
  rw [coeff_comp, MvPowerSeries.coeff_C_mul, coeff_ι]
  split_ifs with h
  · subst h; rfl
  · rw [(tau_hom Φ hΦ n).coeff_eq_zero h, mul_zero]

lemma comp_eul_Lser (Φ : Polynomial (MvPolynomial σ ℚ)) (hΦ : ∀ j, (Φ.coeff j).IsHomogeneous j)
    (n : ℕ) : comp dg n (eul dg (Lser Φ)) = -ι (newtonTr Φ n) := by
  rw [comp_eul_self, comp_Lser Φ hΦ]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [newtonTr]
  · rw [← map_natCast (MvPowerSeries.C (σ := σ) (R := ℚ)) n, ← mul_assoc, ← map_mul,
      show (n : ℚ) * -(1 / (n : ℚ)) = -1 by field_simp, map_neg, map_one, neg_one_mul]

end TwoGradAux

open TwoGradAux in
theorem solution {σ : Type*} (w : σ → ℕ) (Q : MvPolynomial σ ℚ)
    (hQ : MvPolynomial.constantCoeff Q = 1)
    (Φ : Polynomial (MvPolynomial σ ℚ))
    (hΦ : ∀ d, Φ.coeff d = MvPolynomial.homogeneousComponent d Q) (m D : ℕ) :
    MvPolynomial.homogeneousComponent D
        (newtonTr (hatPhi (MvPolynomial.weightedHomogeneousComponent w 0 Q)
          (fun j => MvPolynomial.weightedHomogeneousComponent w j Q) m) m) =
      ∑ d ∈ Finset.range (D + 1),
        MvPolynomial.homogeneousComponent (D - d)
            ((MvPolynomial.weightedHomogeneousComponent w 0 Q) ^ m) *
          (((m : ℚ) / d) • MvPolynomial.weightedHomogeneousComponent w m (newtonTr Φ d)) := by
  classical
  -- the trivial case `m = 0`
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp [newtonTr]
  have hΦh : ∀ j, (Φ.coeff j).IsHomogeneous j := fun j => by
    rw [hΦ]; exact MvPolynomial.homogeneousComponent_isHomogeneous _ _
  have h0 : Φ.coeff 0 = 1 := by
    rw [hΦ, MvPolynomial.homogeneousComponent_zero]
    have : MvPolynomial.coeff 0 Q = 1 := by rw [← hQ]; rfl
    rw [this, map_one]
  set L := Lser Φ with hL
  set ωw : (σ →₀ ℕ) →+ ℕ := Finsupp.weight w with hωw
  -- (F1) `E_deg Q = E_deg(L) · Q`
  have F1 : eul dg (ι Q) = eul dg L * ι Q := by
    rw [← sub_eq_zero]
    refine eq_zero_of_comp dg _ fun n => ?_
    rw [comp_sub, comp_eul_self, comp_mul, comp_dg_ι]
    rw [hL]
    simp_rw [comp_eul_Lser Φ hΦh, comp_dg_ι]
    have h := congrArg ι (newton_all Φ h0 n)
    simp only [map_mul, map_natCast, map_neg, map_sum, hΦ] at h
    rw [h, ← sum_neg_distrib]
    simp only [neg_mul, sub_self]
  -- (B3) `E_w Q = E_w(L) · Q`, via the defect `Dd`
  have B3 : eul ωw (ι Q) = eul ωw L * ι Q := by
    rw [← sub_eq_zero]
    set Dd := eul ωw (ι Q) - eul ωw L * ι Q with hDd
    have e1 : eul dg (eul ωw (ι Q)) = eul ωw (eul dg L) * ι Q + eul dg L * eul ωw (ι Q) := by
      rw [eul_comm dg ωw, F1, eul_mul]
    have e2 : eul dg (eul ωw L * ι Q) =
        eul ωw (eul dg L) * ι Q + eul ωw L * (eul dg L * ι Q) := by
      rw [eul_mul, eul_comm dg ωw, F1]
    have hD : eul dg Dd = eul dg L * Dd := by
      rw [hDd, eul_sub, e1, e2]; ring
    refine eq_zero_of_comp dg _ fun n => ?_
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        rw [hDd, comp_sub, comp_dg_zero_eul, comp_mul, sum_range_one, comp_dg_zero_eul,
          zero_mul, sub_zero]
      · have h := congrArg (comp dg n) hD
        rw [comp_eul_self, comp_mul] at h
        have hz : ∑ j ∈ range (n + 1), comp dg j (eul dg L) * comp dg (n - j) Dd = 0 := by
          refine sum_eq_zero fun j hj => ?_
          rcases Nat.eq_zero_or_pos j with hj0 | hj0
          · subst hj0; rw [hL, comp_eul_Lser Φ hΦh, newtonTr, map_zero, neg_zero, zero_mul]
          · rw [ih (n - j) (by omega), mul_zero]
        rw [hz] at h
        have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
        calc comp dg n Dd = MvPowerSeries.C ((1 / (n : ℚ)) * n) * comp dg n Dd := by
              rw [one_div_mul_cancel hn', map_one, one_mul]
          _ = MvPowerSeries.C (1 / (n : ℚ)) * ((n : MvPowerSeries σ ℚ) * comp dg n Dd) := by
              rw [map_mul, map_natCast, mul_assoc]
          _ = 0 := by rw [h, mul_zero]
  -- (F2) the weight components of (B3)
  have F2 : ∀ j : ℕ, (j : MvPowerSeries σ ℚ) * ι (MvPolynomial.weightedHomogeneousComponent w j Q) =
      ∑ i ∈ range (j + 1), (i : MvPowerSeries σ ℚ) * comp ωw i L *
        ι (MvPolynomial.weightedHomogeneousComponent w (j - i) Q) := by
    intro j
    have h := congrArg (comp ωw j) B3
    rw [comp_eul_self, comp_mul, hωw, comp_wt_ι] at h
    simp_rw [comp_eul_self, comp_wt_ι] at h
    exact h
  -- (S) `S_j = -j C^j [L]_{w = j}`
  set c := MvPolynomial.weightedHomogeneousComponent w 0 Q with hc
  set Ψ := hatPhi c (fun j => MvPolynomial.weightedHomogeneousComponent w j Q) m with hΨ
  have hS : ∀ j, 1 ≤ j → j ≤ m →
      ι (newtonTr Ψ j) = -((j : MvPowerSeries σ ℚ) * (ι c ^ j * comp ωw j L)) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj1 hjm
      obtain ⟨e, rfl⟩ : ∃ e, j = e + 1 := ⟨j - 1, by omega⟩
      rw [newtonTr.eq_2, Fin.sum_univ_eq_sum_range (fun i => newtonTr Ψ i * Ψ.coeff (e + 1 - i)),
        map_sub, map_neg, map_mul, map_natCast, map_sum]
      have hterm : ∀ i ∈ range (e + 1), ι (newtonTr Ψ i * Ψ.coeff (e + 1 - i)) =
          -((i : MvPowerSeries σ ℚ) * comp ωw i L *
            ι (MvPolynomial.weightedHomogeneousComponent w (e + 1 - i) Q) * ι c ^ e) := by
        intro i hi
        rw [mem_range] at hi
        rcases Nat.eq_zero_or_pos i with hi0 | hi0
        · subst hi0; rw [newtonTr, zero_mul, map_zero, Nat.cast_zero, zero_mul, zero_mul,
            zero_mul, neg_zero]
        · rw [map_mul, ih i (by omega) hi0 (by omega), hΨ, coeff_hatPhi,
            if_neg (by omega), if_pos (by omega), map_mul, map_pow,
            show e + 1 - i - 1 = e - i by omega,
            show ι c ^ e = ι c ^ i * ι c ^ (e - i) by rw [← pow_add]; congr 1; omega]
          ring
      rw [sum_congr rfl hterm, sum_neg_distrib, ← sum_mul, hΨ, coeff_hatPhi, if_neg (by omega),
        if_pos hjm, Nat.add_sub_cancel, map_mul, map_pow]
      have hF := F2 (e + 1)
      rw [sum_range_succ, Nat.sub_self, ← hc] at hF
      linear_combination (-(ι c ^ e)) * hF
  -- final assembly
  have hinj : Function.Injective (ι : MvPolynomial σ ℚ →+* MvPowerSeries σ ℚ) :=
    MvPolynomial.coe_injective σ ℚ
  apply hinj
  rw [← comp_dg_ι, hS m hm le_rfl,
    show -((m : MvPowerSeries σ ℚ) * (ι c ^ m * comp ωw m L)) =
      -((m : MvPowerSeries σ ℚ) * (comp ωw m L * ι (c ^ m))) by rw [map_pow, mul_comm (ι c ^ m)],
    comp_neg, comp_natCast_mul, comp_mul, map_sum, mul_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun d _ => ?_
  rw [comp_comm, hL, comp_Lser Φ hΦh, comp_C_mul, hωw, comp_wt_ι, comp_dg_ι, map_mul,
    MvPolynomial.smul_eq_C_mul, map_mul, ι_C,
    show (m : ℚ) / d = (m : ℚ) * (1 / d) by ring, map_mul, map_neg, map_natCast]
  ring
