-- Prove2me | solution 1 for MvPowerSeries.free_and_finite_and_finrank_quotient_span_range_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/dcec10ae-5036-5610-b1a2-fa763bf0763e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_free_and_finite_and_finrank_quotient_span_range_X_pow

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

noncomputable section

open MvPowerSeries

namespace P2mKcBoxBasis

variable {R : Type*} [CommRing R] {g : ℕ} {N : Fin g → ℕ}

abbrev powIdeal (R : Type*) [CommRing R] (g : ℕ) (N : Fin g → ℕ) : Ideal (MvPowerSeries (Fin g) R) :=
  Ideal.span (Set.range fun i : Fin g => (X i : MvPowerSeries (Fin g) R) ^ N i)

def InBox (N : Fin g → ℕ) (d : Fin g →₀ ℕ) : Prop := ∀ i, d i < N i

scoped instance instDecidableInBox (N : Fin g → ℕ) (d : Fin g →₀ ℕ) : Decidable (InBox N d) := by
  unfold InBox; infer_instance

def boxKer (R : Type*) [CommRing R] (g : ℕ) (N : Fin g → ℕ) : Ideal (MvPowerSeries (Fin g) R) where
  carrier := {θ | ∀ d : Fin g →₀ ℕ, InBox N d → coeff d θ = 0}
  zero_mem' := fun d _ => map_zero _
  add_mem' := by
    intro a b ha hb d hd
    rw [map_add, ha d hd, hb d hd, add_zero]
  smul_mem' := by
    intro c θ hθ d hd
    rw [smul_eq_mul, coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have hx2 : InBox N x.2 := fun i => lt_of_le_of_lt (by rw [← hx]; simp) (hd i)
    rw [hθ x.2 hx2, mul_zero]

theorem mem_boxKer {θ : MvPowerSeries (Fin g) R} :
    θ ∈ boxKer R g N ↔ ∀ d : Fin g →₀ ℕ, InBox N d → coeff d θ = 0 := Iff.rfl

theorem X_pow_mem_boxKer (i : Fin g) :
    (X i : MvPowerSeries (Fin g) R) ^ N i ∈ boxKer R g N := by
  classical
  intro d hd
  rw [coeff_X_pow, if_neg]
  rintro rfl
  have := hd i
  rw [Finsupp.single_eq_same] at this
  exact lt_irrefl _ this

theorem powIdeal_le_boxKer : powIdeal R g N ≤ boxKer R g N :=
  Ideal.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    exact X_pow_mem_boxKer i)

def part (N : Fin g → ℕ) (θ : MvPowerSeries (Fin g) R) (i : Fin g) : MvPowerSeries (Fin g) R :=
  fun e => if (∀ j, j < i → e j < N j) then coeff (e + Finsupp.single i (N i)) θ else 0

theorem coeff_part (θ : MvPowerSeries (Fin g) R) (i : Fin g) (e : Fin g →₀ ℕ) :
    coeff e (part N θ i)
      = if (∀ j, j < i → e j < N j) then coeff (e + Finsupp.single i (N i)) θ else 0 :=
  rfl

theorem coeff_X_pow_mul_part (θ : MvPowerSeries (Fin g) R) (i : Fin g) (d : Fin g →₀ ℕ) :
    coeff d ((X i : MvPowerSeries (Fin g) R) ^ N i * part N θ i)
      = if (N i ≤ d i ∧ ∀ j, j < i → d j < N j) then coeff d θ else 0 := by
  classical
  rw [X_pow_eq, coeff_monomial_mul, one_mul]
  by_cases hi : N i ≤ d i
  · have hle : Finsupp.single i (N i) ≤ d := Finsupp.single_le_iff.mpr hi
    rw [if_pos hle, coeff_part]
    have hsub : ∀ j, j < i → (d - Finsupp.single i (N i)) j = d j := by
      intro j hj
      rw [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_of_ne (ne_of_lt hj), Nat.sub_zero]
    by_cases hj : ∀ j, j < i → d j < N j
    · rw [if_pos (fun j hj' => by rw [hsub j hj']; exact hj j hj'), if_pos ⟨hi, hj⟩,
        tsub_add_cancel_of_le hle]
    · rw [if_neg (fun h => hj fun j hj' => by rw [← hsub j hj']; exact h j hj'), if_neg]
      exact fun h => hj h.2
  · rw [if_neg (fun h => hi (Finsupp.single_le_iff.mp h)), if_neg]
    exact fun h => hi h.1

theorem eq_sum_X_pow_mul_part {θ : MvPowerSeries (Fin g) R} (hθ : θ ∈ boxKer R g N) :
    θ = ∑ i, (X i : MvPowerSeries (Fin g) R) ^ N i * part N θ i := by
  classical
  refine MvPowerSeries.ext fun d => ?_
  rw [map_sum]
  simp_rw [coeff_X_pow_mul_part]
  by_cases hd : InBox N d
  · rw [hθ d hd, Finset.sum_eq_zero]
    intro i _
    rw [if_neg]
    exact fun h => absurd (hd i) (not_lt.mpr h.1)
  ·
    have hne : (Finset.univ.filter fun i : Fin g => N i ≤ d i).Nonempty := by
      by_contra hc
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hc
      exact hd fun i => not_le.mp (hc (Finset.mem_univ i))
    set i₀ := (Finset.univ.filter fun i : Fin g => N i ≤ d i).min' hne with hi₀
    have hi₀mem : N i₀ ≤ d i₀ := by
      have := Finset.min'_mem _ hne
      rw [Finset.mem_filter] at this
      exact this.2
    have hi₀min : ∀ j, j < i₀ → d j < N j := by
      intro j hj
      by_contra hc
      have hjmem : j ∈ Finset.univ.filter fun i : Fin g => N i ≤ d i :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ j, not_lt.mp hc⟩
      exact absurd (Finset.min'_le _ j hjmem) (not_le.mpr hj)
    rw [Finset.sum_eq_single i₀]
    · rw [if_pos ⟨hi₀mem, hi₀min⟩]
    · intro j _ hj
      rw [if_neg]
      rintro ⟨hj1, hj2⟩
      rcases lt_trichotomy j i₀ with hlt | heq | hgt
      · exact absurd (hi₀min j hlt) (not_lt.mpr hj1)
      · exact hj heq
      · exact absurd (hj2 i₀ hgt) (not_lt.mpr hi₀mem)
    · intro h
      exact absurd (Finset.mem_univ i₀) h

theorem boxKer_le_powIdeal : boxKer R g N ≤ powIdeal R g N := by
  intro θ hθ
  rw [eq_sum_X_pow_mul_part hθ]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem powIdeal_eq_boxKer : powIdeal R g N = boxKer R g N :=
  le_antisymm powIdeal_le_boxKer boxKer_le_powIdeal

def toFinsupp (u : (i : Fin g) → Fin (N i)) : Fin g →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (u i : ℕ)

@[scoped simp] theorem toFinsupp_apply (u : (i : Fin g) → Fin (N i)) (i : Fin g) : toFinsupp u i = u i := rfl

theorem inBox_toFinsupp (u : (i : Fin g) → Fin (N i)) : InBox N (toFinsupp u) := fun i => (u i).isLt

def extend (v : ((i : Fin g) → Fin (N i)) → R) : MvPowerSeries (Fin g) R :=
  fun d => if h : InBox N d then v (fun i => ⟨d i, h i⟩) else 0

theorem coeff_extend (v : ((i : Fin g) → Fin (N i)) → R) (d : Fin g →₀ ℕ) :
    coeff d (extend v) = if h : InBox N d then v (fun i => ⟨d i, h i⟩) else 0 :=
  rfl

theorem coeff_extend_toFinsupp (v : ((i : Fin g) → Fin (N i)) → R) (u : (i : Fin g) → Fin (N i)) :
    coeff (toFinsupp u) (extend v) = v u := by
  rw [coeff_extend, dif_pos (inBox_toFinsupp u)]
  rfl

theorem coeff_extend_of_not (v : ((i : Fin g) → Fin (N i)) → R) {d : Fin g →₀ ℕ}
    (hd : ¬ InBox N d) : coeff d (extend v) = 0 := by
  rw [coeff_extend, dif_neg hd]

theorem toFinsupp_mk {d : Fin g →₀ ℕ} (h : InBox N d) :
    toFinsupp (fun i => (⟨d i, h i⟩ : Fin (N i))) = d := by
  ext i
  rfl

def extendLin (R : Type*) [CommRing R] (g : ℕ) (N : Fin g → ℕ) :
    (((i : Fin g) → Fin (N i)) → R) →ₗ[R] (MvPowerSeries (Fin g) R ⧸ powIdeal R g N) :=
  (Ideal.Quotient.mkₐ R (powIdeal R g N)).toLinearMap ∘ₗ
    { toFun := extend
      map_add' := fun v w => by
        refine MvPowerSeries.ext fun d => ?_
        rw [map_add, coeff_extend, coeff_extend, coeff_extend]
        split_ifs <;> simp
      map_smul' := fun c v => by
        refine MvPowerSeries.ext fun d => ?_
        rw [map_smul, coeff_extend, coeff_extend, RingHom.id_apply, smul_eq_mul]
        split_ifs <;> simp }

theorem extendLin_apply (v : ((i : Fin g) → Fin (N i)) → R) :
    extendLin R g N v = Ideal.Quotient.mk (powIdeal R g N) (extend v) := rfl

theorem extendLin_injective : Function.Injective (extendLin R g N) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  rw [extendLin_apply, Ideal.Quotient.eq_zero_iff_mem, powIdeal_eq_boxKer] at hv
  funext u
  rw [← coeff_extend_toFinsupp v u]
  exact hv _ (inBox_toFinsupp u)

theorem extendLin_surjective : Function.Surjective (extendLin R g N) := by
  intro x
  obtain ⟨θ, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨fun u => coeff (toFinsupp u) θ, ?_⟩
  rw [extendLin_apply, Ideal.Quotient.eq, powIdeal_eq_boxKer]
  intro d hd
  rw [map_sub, coeff_extend, dif_pos hd, toFinsupp_mk hd, sub_self]

def boxEquiv (R : Type*) [CommRing R] (g : ℕ) (N : Fin g → ℕ) :
    (((i : Fin g) → Fin (N i)) → R) ≃ₗ[R] (MvPowerSeries (Fin g) R ⧸ powIdeal R g N) :=
  LinearEquiv.ofBijective (extendLin R g N) ⟨extendLin_injective, extendLin_surjective⟩

end P2mKcBoxBasis
p2m_reactivate "P2MW.S_MvPowerSeries_free_and_finite_and_finrank_quotient_span_range_X_pow.P2mKcBoxBasis"

end
p2m_reactivate "P2MW.S_MvPowerSeries_free_and_finite_and_finrank_quotient_span_range_X_pow.P2mKcBoxBasis"

open P2mKcBoxBasis in
theorem solution (R : Type u) [CommRing R] [Nontrivial R] (g : ℕ) (N : Fin g → ℕ) :
    Module.Free R (MvPowerSeries (Fin g) R ⧸
        Ideal.span (Set.range fun i : Fin g => (MvPowerSeries.X i : MvPowerSeries (Fin g) R) ^ N i)) ∧
      Module.Finite R (MvPowerSeries (Fin g) R ⧸
        Ideal.span (Set.range fun i : Fin g => (MvPowerSeries.X i : MvPowerSeries (Fin g) R) ^ N i)) ∧
      Module.finrank R (MvPowerSeries (Fin g) R ⧸
        Ideal.span (Set.range fun i : Fin g => (MvPowerSeries.X i : MvPowerSeries (Fin g) R) ^ N i))
          = ∏ i, N i := by
  refine ⟨Module.Free.of_equiv (boxEquiv R g N), Module.Finite.equiv (boxEquiv R g N), ?_⟩
  rw [← (boxEquiv R g N).finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_pi]
  simp only [Fintype.card_fin]

end S_MvPowerSeries_free_and_finite_and_finrank_quotient_span_range_X_pow
end P2MW
export P2MW.S_MvPowerSeries_free_and_finite_and_finrank_quotient_span_range_X_pow (solution)
