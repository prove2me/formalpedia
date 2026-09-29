-- Prove2me | solution 1 for MvFormalGroup.exists_subst_eq_X_of_linearPart_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/9276befd-17bc-528b-b821-70881cdd0164

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_subst_eq_X_of_linearPart_eq_one

set_option autoImplicit false

open MvPowerSeries

universe u

namespace FormalInverse

variable {R : Type u} [CommRing R] {d : ℕ}

section Perturb

variable (φ : Fin d → MvPowerSeries (Fin d) R)

private noncomputable def tail (i : Fin d) : MvPowerSeries (Fin d) R := φ i - X i

private theorem coeff_tail_eq_zero (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1) (i : Fin d) {e : Fin d →₀ ℕ} (he : e.degree ≤ 1) :
    coeff e (tail φ i) = 0 := by
  classical
  rcases Nat.lt_or_ge e.degree 1 with h0 | h1
  · have he0 : e = 0 := (Finsupp.degree_eq_zero_iff e).mp (by omega)
    subst he0
    rw [tail, map_sub, coeff_zero_eq_constantCoeff_apply, hφ0 i, coeff_zero_X, sub_zero]
  · have he1 : e.degree = 1 := le_antisymm he h1
    have hne : e ≠ 0 := fun h => by rw [h, (Finsupp.degree_eq_zero_iff _).mpr rfl] at he1; omega
    obtain ⟨j, hj⟩ : ∃ j, e j ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (Finsupp.ext h)
    have hj1 : e j = 1 := by
      have := Finsupp.le_degree j e
      omega
    have hej : e = Finsupp.single j 1 := by

      have hle : Finsupp.single j 1 ≤ e := by
        rw [Finsupp.single_le_iff]; omega
      obtain ⟨e', he'⟩ := exists_add_of_le hle
      have hdeg : e'.degree = 0 := by
        have := congrArg Finsupp.degree he'
        rw [map_add, Finsupp.degree_single] at this
        omega
      rw [(Finsupp.degree_eq_zero_iff _).mp hdeg, add_zero] at he'
      exact he'
    subst hej
    have hlin : (φ i).coeff (Finsupp.single j 1) = if i = j then 1 else 0 := by
      have := congrFun (congrFun hφ1 i) j
      simpa [MvFormalGroup.linearPart, Matrix.one_apply] using this
    rw [tail, map_sub, hlin, coeff_index_single_X]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]

private theorem subst_eq_add_subst_tail {τ : Type*} (ψ : Fin d → MvPowerSeries τ R)
    (hψ : ∀ j, (ψ j).constantCoeff = 0) (i : Fin d) :
    subst ψ (φ i) = ψ i + subst ψ (tail φ i) := by
  have hs := hasSubst_of_constantCoeff_zero hψ
  rw [tail, subst_sub hs, subst_X hs]
  ring

private theorem coeff_subst_tail_congr (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1) {τ : Type*}
    {ψ ψ' : Fin d → MvPowerSeries τ R}
    (hψ : ∀ j, (ψ j).constantCoeff = 0) (hψ' : ∀ j, (ψ' j).constantCoeff = 0)
    {N : ℕ} (hN : 1 ≤ N) (hcc : ∀ j, ∀ e : τ →₀ ℕ, e.degree < N → coeff e (ψ j) = coeff e (ψ' j))
    (i : Fin d) {e : τ →₀ ℕ} (he : e.degree ≤ N) :
    coeff e (subst ψ (tail φ i)) = coeff e (subst ψ' (tail φ i)) := by
  classical
  rw [coeff_subst (hasSubst_of_constantCoeff_zero hψ),
    coeff_subst (hasSubst_of_constantCoeff_zero hψ')]
  refine finsum_congr fun m => ?_
  rcases Nat.lt_or_ge m.degree 2 with hm | hm
  · rw [coeff_tail_eq_zero φ hφ0 hφ1 i (by omega), zero_smul, zero_smul]
  · rw [MvFormalGroup.coeff_finsuppProd_pow_sub_congr hN hψ hψ' hcc (by omega)]

end Perturb

section Newton

variable (φ : Fin d → MvPowerSeries (Fin d) R)

private noncomputable def invApprox : ℕ → Fin d → MvPowerSeries (Fin d) R
  | 0 => fun i => X i
  | n + 1 => fun i =>
      invApprox n i - homogeneousComponent (n + 2) (subst (invApprox n) (φ i) - X i)

private theorem invApprox_succ (n : ℕ) (i : Fin d) :
    invApprox φ (n + 1) i =
      invApprox φ n i - homogeneousComponent (n + 2) (subst (invApprox φ n) (φ i) - X i) := rfl

private theorem coeff_invApprox_of_degree_le_one (n : ℕ) (i : Fin d) {e : Fin d →₀ ℕ}
    (he : e.degree ≤ 1) : coeff e (invApprox φ n i) = coeff e (X i : MvPowerSeries (Fin d) R) := by
  induction n with
  | zero => rfl
  | succ n IH =>
    rw [invApprox_succ, map_sub, coeff_homogeneousComponent, if_neg (by omega), sub_zero, IH]

private theorem constantCoeff_invApprox (n : ℕ) (i : Fin d) :
    (invApprox φ n i).constantCoeff = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply,
    coeff_invApprox_of_degree_le_one φ n i (by rw [(Finsupp.degree_eq_zero_iff _).mpr rfl]; omega),
    coeff_zero_X]

private theorem coeff_invApprox_stable {n m : ℕ} (hnm : n ≤ m) (i : Fin d) {e : Fin d →₀ ℕ}
    (he : e.degree ≤ n + 1) : coeff e (invApprox φ m i) = coeff e (invApprox φ n i) := by
  induction m with
  | zero =>
    have : n = 0 := by omega
    subst this; rfl
  | succ m IH =>
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · rw [invApprox_succ, map_sub, coeff_homogeneousComponent, if_neg (by omega), sub_zero]
      exact IH (by omega)
    · have : n = m + 1 := by omega
      subst this; rfl

private theorem coeff_error_invApprox (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1) (n : ℕ) (i : Fin d) {e : Fin d →₀ ℕ}
    (he : e.degree ≤ n + 1) : coeff e (subst (invApprox φ n) (φ i) - X i) = 0 := by
  induction n generalizing e i with
  | zero =>
    have h0 : ∀ j, (invApprox φ 0 j).constantCoeff = 0 := constantCoeff_invApprox φ 0
    rw [subst_eq_add_subst_tail φ _ h0, map_sub, map_add]
    show coeff e (X i) + coeff e (subst (fun j => (X j : MvPowerSeries (Fin d) R)) (tail φ i))
      - coeff e (X i) = 0
    rw [show (fun j => (X j : MvPowerSeries (Fin d) R)) = X from rfl, subst_self]
    simp only [id_eq, add_sub_cancel_left]
    exact coeff_tail_eq_zero φ hφ0 hφ1 i he
  | succ n IH =>
    have hn : ∀ j, (invApprox φ n j).constantCoeff = 0 := constantCoeff_invApprox φ n
    have hn1 : ∀ j, (invApprox φ (n + 1) j).constantCoeff = 0 := constantCoeff_invApprox φ (n + 1)
    have hcc : ∀ j, ∀ e : Fin d →₀ ℕ, e.degree < n + 2 →
        coeff e (invApprox φ n j) = coeff e (invApprox φ (n + 1) j) := fun j e he =>
      (coeff_invApprox_stable φ (Nat.le_succ n) j (by omega)).symm
    rw [subst_eq_add_subst_tail φ _ hn1, map_sub, map_add,
      ← coeff_subst_tail_congr φ hφ0 hφ1 hn hn1 (by omega) hcc i (by omega), invApprox_succ,
      map_sub, coeff_homogeneousComponent]
    have herr : coeff e (subst (invApprox φ n) (φ i) - X i)
        = coeff e (invApprox φ n i) + coeff e (subst (invApprox φ n) (tail φ i)) - coeff e (X i) := by
      rw [subst_eq_add_subst_tail φ _ hn, map_sub, map_add]
    split_ifs with hdeg
    · rw [herr]; ring
    · have h := IH i (e := e) (by omega)
      rw [herr] at h
      rw [sub_zero]
      exact h

private noncomputable def invSeries (i : Fin d) : MvPowerSeries (Fin d) R :=
  fun e => coeff e (invApprox φ e.degree i)

private theorem coeff_invSeries {n : ℕ} (i : Fin d) {e : Fin d →₀ ℕ} (he : e.degree ≤ n + 1) :
    coeff e (invSeries φ i) = coeff e (invApprox φ n i) := by
  show coeff e (invApprox φ e.degree i) = _
  rcases Nat.lt_or_ge e.degree (n + 1) with h | h
  · exact (coeff_invApprox_stable φ (show e.degree ≤ n by omega) i (Nat.le_succ _)).symm
  · have hdeg : e.degree = n + 1 := by omega
    rw [hdeg]
    exact coeff_invApprox_stable φ (Nat.le_succ n) i he

private theorem coeff_invSeries_of_degree_le_one (i : Fin d) {e : Fin d →₀ ℕ} (he : e.degree ≤ 1) :
    coeff e (invSeries φ i) = coeff e (X i : MvPowerSeries (Fin d) R) := by
  rw [coeff_invSeries φ (n := 0) i he, coeff_invApprox_of_degree_le_one φ 0 i he]

private theorem constantCoeff_invSeries (i : Fin d) : (invSeries φ i).constantCoeff = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply,
    coeff_invSeries_of_degree_le_one φ i (by rw [(Finsupp.degree_eq_zero_iff _).mpr rfl]; omega),
    coeff_zero_X]

private theorem linearPart_invSeries : MvFormalGroup.linearPart (invSeries φ) = 1 := by
  ext i j
  rw [MvFormalGroup.linearPart, Matrix.of_apply, coeff_invSeries_of_degree_le_one φ i
    (by rw [Finsupp.degree_single]), coeff_index_single_X, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

private theorem subst_invSeries (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1) (i : Fin d) :
    subst (invSeries φ) (φ i) = X i := by
  ext e
  have h0 : ∀ j, (invSeries φ j).constantCoeff = 0 := constantCoeff_invSeries φ
  have hn : ∀ j, (invApprox φ e.degree j).constantCoeff = 0 := constantCoeff_invApprox φ _
  have hcc : ∀ j, ∀ e' : Fin d →₀ ℕ, e'.degree < e.degree + 1 →
      coeff e' (invSeries φ j) = coeff e' (invApprox φ e.degree j) := fun j e' he' =>
    coeff_invSeries φ j (by omega)
  have herr := coeff_error_invApprox φ hφ0 hφ1 e.degree i (e := e) (Nat.le_succ _)
  rw [map_sub, subst_eq_add_subst_tail φ _ hn, map_add, sub_eq_zero] at herr
  rw [subst_eq_add_subst_tail φ _ h0, map_add,
    coeff_subst_tail_congr φ hφ0 hφ1 h0 hn (by omega) hcc i (Nat.le_succ _),
    coeff_invSeries φ i (Nat.le_succ _), herr]

end Newton

end FormalInverse

open FormalInverse in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] {d : ℕ}
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1) :
    ∃ ψ : Fin d → MvPowerSeries (Fin d) 𝓞,
      (∀ i, (ψ i).constantCoeff = 0) ∧
      (∀ i, subst φ (ψ i) = X i) ∧
      (∀ i, subst ψ (φ i) = X i) := by
  classical

  have hψ0 : ∀ i, (FormalInverse.invSeries φ i).constantCoeff = 0 :=
    FormalInverse.constantCoeff_invSeries φ
  have hψ1 : MvFormalGroup.linearPart (FormalInverse.invSeries φ) = 1 :=
    FormalInverse.linearPart_invSeries φ
  have hφψ : ∀ i, subst (FormalInverse.invSeries φ) (φ i) = X i :=
    FormalInverse.subst_invSeries φ hφ0 hφ1
  set ψ := FormalInverse.invSeries φ with hψdef
  set χ := FormalInverse.invSeries ψ with hχdef
  have hχ0 : ∀ i, (χ i).constantCoeff = 0 := FormalInverse.constantCoeff_invSeries ψ
  have hψχ : ∀ i, subst χ (ψ i) = X i := FormalInverse.subst_invSeries ψ hψ0 hψ1

  have hχφ : ∀ i, χ i = φ i := fun i => by
    have h := congrArg (subst χ) (hφψ i)
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hψ0)
      (hasSubst_of_constantCoeff_zero hχ0), subst_X (hasSubst_of_constantCoeff_zero hχ0)] at h
    have hfun : (fun s => subst χ (ψ s)) = (X : Fin d → MvPowerSeries (Fin d) 𝓞) := funext hψχ
    rw [hfun, subst_self] at h
    exact h.symm
  refine ⟨ψ, hψ0, fun i => ?_, hφψ⟩
  rw [← funext hχφ]
  exact hψχ i

end S_MvFormalGroup_exists_subst_eq_X_of_linearPart_eq_one
end P2MW
export P2MW.S_MvFormalGroup_exists_subst_eq_X_of_linearPart_eq_one (solution)
