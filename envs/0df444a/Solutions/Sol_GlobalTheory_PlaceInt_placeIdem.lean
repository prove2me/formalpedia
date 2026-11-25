-- Prove2me | solution 1 for GlobalTheory.PlaceInt.placeIdem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:28:09.949033+00:00
-- url     : https://prove2.me/submissions/dfc55cb0-c68c-4a41-9146-97bd7c0b1fc4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_PlaceIdem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSCCols
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_IdemDen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsRingOfIntegersLift
import Theorems.Thm_GlobalTheory_PlaceInt_exists_ringOfIntegers_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.PlaceInt
open NumberField Polynomial IsLocalRing
namespace GlobalTheory.PlaceInt
namespace _root_.GlobalTheory.PlaceInt
theorem _root_.solution : _root_.ReciprocityTheory.ChartRestriction.G.PullbackSections.PlaceIdemSt := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.PullbackSections.PlaceIdemSt
  intro E _ _ V _ _ _ _ k _ _ _ P hP hP0
  classical
  choose σ hσ using fun ψ : E →+* k => _root_.GlobalTheory.PlaceInt.exists_ringOfIntegers_lift E V k ψ
  have inj : Function.Injective (algebraMap V k) := IsFractionRing.injective V k
  obtain ⟨Q, hQ, hQp⟩ : ∃ Q : (E →+* k) → Ideal (𝓞 E),
      (∀ ψ x, x ∈ Q ψ ↔ σ ψ x ∈ maximalIdeal V) ∧ ∀ ψ, (Q ψ).IsPrime :=
    ⟨fun ψ => (maximalIdeal V).comap (σ ψ), fun _ _ => Iff.rfl, fun _ => inferInstance⟩
  have hcond : ∀ ψ : E →+* k, (∀ x : 𝓞 E, x ∈ P ↔
      ψ (x : E) ∈ algebraMap V k '' (maximalIdeal V : Set V)) ↔ Q ψ = P := by
    intro ψ
    have key : ∀ x : 𝓞 E, ψ (x : E) ∈ algebraMap V k '' (maximalIdeal V : Set V) ↔ x ∈ Q ψ := by
      intro x
      rw [hQ, ← hσ]
      constructor
      · rintro ⟨y, hy, h⟩
        exact inj h ▸ hy
      · intro h
        exact ⟨_, h, rfl⟩
    simp only [key]
    rw [eq_comm, SetLike.ext_iff]
  by_cases hex : ∃ ψ0 : E →+* k, Q ψ0 = P
  swap
  · refine ⟨0, Fin.elim0, Fin.elim0, fun ψ => ?_⟩
    rw [if_neg (fun h => hex ⟨ψ, (hcond ψ).mp h⟩)]
    simp
  obtain ⟨ψ0, hψ0⟩ := hex
  haveI : CharZero k := ⟨fun a b h => by
    rw [← map_natCast ψ0, ← map_natCast ψ0 b] at h
    exact Nat.cast_injective (ψ0.injective h)⟩
  have hPmax : P.IsMaximal := hP.isMaximal hP0

  set N : ℕ := Ideal.absNorm P with hN
  have hNP : (N : 𝓞 E) ∈ P := Ideal.absNorm_mem P
  have hN0 : (N : 𝓞 E) ≠ 0 := by
    rw [Nat.cast_ne_zero, hN]
    exact fun h => hP0 (Ideal.absNorm_eq_zero_iff.mp h)
  have hNQ : ∀ ψ, (N : 𝓞 E) ∈ Q ψ := by
    intro ψ
    have h0 : (N : 𝓞 E) ∈ Q ψ0 := hψ0 ▸ hNP
    rw [hQ, map_natCast] at h0 ⊢
    exact h0
  have hc : ∀ ψ, ∃ c : 𝓞 E, c ∉ P ∧ (Q ψ ≠ P → c ∈ Q ψ) := by
    intro ψ
    by_cases h : Q ψ = P
    · exact ⟨1, fun h1 => hPmax.ne_top ((Ideal.eq_top_iff_one _).2 h1), fun h' => (h' h).elim⟩
    · have hQ0 : Q ψ ≠ ⊥ := fun h0 => hN0 (by simpa [h0] using hNQ ψ)
      have hQmax : (Q ψ).IsMaximal := (hQp ψ).isMaximal hQ0
      have hnle : ¬ Q ψ ≤ P := fun hle => h (hQmax.eq_of_le hPmax.ne_top hle)
      obtain ⟨c, hcQ, hcP⟩ := SetLike.not_le_iff_exists.mp hnle
      exact ⟨c, hcP, fun _ => hcQ⟩
  choose c hcP hcQ using hc
  have hprod : ∏ ψ, c ψ ∉ P := by
    rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨ψ, -, h⟩
    exact hcP ψ h
  obtain ⟨y, i, hi, hyi⟩ := hPmax.exists_inv hprod
  set b : 𝓞 E := y * ∏ ψ, c ψ with hb
  have hb1 : ∀ ψ, Q ψ = P → σ ψ b - 1 ∈ maximalIdeal V := by
    intro ψ h
    have : b - 1 ∈ Q ψ := by
      rw [h]
      have : b - 1 = -i := by rw [hb, ← hyi]; ring
      rw [this]
      exact P.neg_mem hi
    rw [hQ, map_sub, map_one] at this
    exact this
  have hb0 : ∀ ψ, Q ψ ≠ P → σ ψ b ∈ maximalIdeal V := by
    intro ψ h
    rw [← hQ]
    obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem c (Finset.mem_univ ψ)
    rw [hb, hr]
    exact (Q ψ).mul_mem_left _ ((Q ψ).mul_mem_right _ (hcQ ψ h))

  set p0 : V[X] := ∏ ψ ∈ Finset.univ.filter (fun ψ => Q ψ ≠ P), (X - C (σ ψ b)) with hp0
  set p1 : V[X] := ∏ ψ ∈ Finset.univ.filter (fun ψ => Q ψ = P), (X - C (σ ψ b)) with hp1
  have hcop : IsCoprime p0 p1 := by
    rw [hp0, hp1]
    refine IsCoprime.prod_left fun ψ hψ => IsCoprime.prod_right fun φ hφ => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ hφ
    apply isCoprime_X_sub_C_of_isUnit_sub
    have h0 := hb0 ψ hψ
    have h1 := hb1 φ hφ
    have hnot : σ ψ b - σ φ b ∉ maximalIdeal V := by
      intro h
      apply (maximalIdeal.isMaximal V).ne_top
      rw [Ideal.eq_top_iff_one]
      have := sub_mem (sub_mem h0 h) h1
      simpa using this
    simpa [mem_maximalIdeal, mem_nonunits_iff] using hnot
  obtain ⟨u, v, huv⟩ := hcop
  set g : V[X] := u * p0 with hg
  refine ⟨g.natDegree + 1, fun j => b ^ (j : ℕ), fun j => g.coeff j, fun ψ => ?_⟩
  have hsum : ∑ j : Fin (g.natDegree + 1), algebraMap V k (g.coeff j) * ψ ((b ^ (j : ℕ) : 𝓞 E) : E)
      = algebraMap V k (g.eval (σ ψ b)) := by
    rw [eval_eq_sum_range' (Nat.lt_succ_self _), map_sum,
      ← Fin.sum_univ_eq_sum_range (fun j => algebraMap V k (g.coeff j * σ ψ b ^ j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hσ]
    simp only [map_pow, map_mul]
  rw [hsum]
  by_cases h : Q ψ = P
  · rw [if_pos ((hcond ψ).mpr h)]
    have hp1z : p1.eval (σ ψ b) = 0 := by
      rw [hp1, eval_prod]
      exact Finset.prod_eq_zero (i := ψ) (by simp [h]) (by simp)
    have : g.eval (σ ψ b) = 1 := by
      have h2 : (u * p0 + v * p1).eval (σ ψ b) = 1 := by rw [huv, eval_one]
      rw [eval_add, show (v * p1).eval (σ ψ b) = 0 by rw [eval_mul, hp1z, mul_zero],
        add_zero] at h2
      exact h2
    rw [this, map_one]
  · rw [if_neg (fun h' => h ((hcond ψ).mp h'))]
    have hp0z : p0.eval (σ ψ b) = 0 := by
      rw [hp0, eval_prod]
      exact Finset.prod_eq_zero (i := ψ) (by simp [h]) (by simp)
    rw [hg, eval_mul, hp0z, mul_zero, map_zero]
end _root_.GlobalTheory.PlaceInt
end GlobalTheory.PlaceInt
