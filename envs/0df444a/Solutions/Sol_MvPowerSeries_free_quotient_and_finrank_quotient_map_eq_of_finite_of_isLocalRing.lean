-- Prove2me | solution 1 for MvPowerSeries.free_quotient_and_finrank_quotient_map_eq_of_finite_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/79ea43b5-2591-55f9-922b-a13caa751688

import Mathlib
import Theorems.Thm_MvPowerSeries_exists_basis_subst_of_finite_quotient_of_isLocalRing
import Theorems.Thm_MvPowerSeries_exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_free_quotient_and_finrank_quotient_map_eq_of_finite_of_isLocalRing
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open scoped TensorProduct

namespace K2HKD

open MvPowerSeries

variable {B : Type*} [CommRing B]

theorem mem_span_X_pow {σ : Type*} [DecidableEq σ] (N : ℕ) (T : Finset σ) :
    ∀ f : MvPowerSeries σ B, (∀ e : σ →₀ ℕ, (∀ s ∈ T, e s < N) → coeff e f = 0) →
      f ∈ Ideal.span ((fun s => (X s : MvPowerSeries σ B) ^ N) '' (T : Set σ)) := by
  induction T using Finset.induction_on with
  | empty =>
    intro f hf
    have : f = 0 := by
      ext e
      rw [coeff_zero]
      exact hf e (fun s hs => absurd hs (Finset.notMem_empty s))
    rw [this]
    exact zero_mem _
  | insert s₀ T hs₀ ih =>
    intro f hf
    let f₀ : MvPowerSeries σ B := fun e => if e s₀ < N then coeff e f else 0
    have hf₀ : ∀ e, coeff e f₀ = if e s₀ < N then coeff e f else 0 := fun e => rfl
    have h1 : (X s₀ : MvPowerSeries σ B) ^ N ∣ f - f₀ := by
      rw [X_pow_dvd_iff]
      intro m hm
      rw [map_sub, hf₀, if_pos hm, sub_self]
    have h2 : f₀ ∈ Ideal.span ((fun s => (X s : MvPowerSeries σ B) ^ N) '' (T : Set σ)) := by
      refine ih f₀ fun e he => ?_
      rw [hf₀]
      by_cases h : e s₀ < N
      · rw [if_pos h]
        refine hf e fun s hs => ?_
        rcases Finset.mem_insert.1 hs with rfl | hs
        · exact h
        · exact he s hs
      · rw [if_neg h]
    have h3 : Ideal.span ((fun s => (X s : MvPowerSeries σ B) ^ N) '' (T : Set σ)) ≤
        Ideal.span ((fun s => (X s : MvPowerSeries σ B) ^ N) '' ((insert s₀ T : Finset σ) : Set σ)) :=
      Ideal.span_mono (Set.image_mono (by simp))
    obtain ⟨g, hg⟩ := h1
    have : f = f₀ + (X s₀ : MvPowerSeries σ B) ^ N * g := by rw [← hg]; ring
    rw [this]
    refine Ideal.add_mem _ (h3 h2) (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s₀, by simp, rfl⟩))

theorem mem_span_range_X_of_constantCoeff {n : ℕ} {f : MvPowerSeries (Fin n) B}
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) B)) := by
  classical
  have h := mem_span_X_pow 1 Finset.univ f fun e he => by
    have : e = 0 := by
      ext s
      have := he s (Finset.mem_univ s)
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
    rw [this, coeff_zero_eq_constantCoeff_apply, hf]
  simpa only [pow_one, Finset.coe_univ, Set.image_univ] using h

theorem subst_sub_C_constantCoeff_mem {n m : ℕ} (ρ : Fin n → MvPowerSeries (Fin m) B) (hρ : HasSubst ρ)
    (c : MvPowerSeries (Fin n) B) :
    subst ρ c - C (constantCoeff c) ∈ Ideal.span (Set.range ρ) := by
  classical
  have h0 : constantCoeff (c - C (constantCoeff c)) = 0 := by
    rw [map_sub, constantCoeff_C, sub_self]
  obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun (MvPowerSeries (Fin n) B)).mp
    (mem_span_range_X_of_constantCoeff h0)
  have : subst ρ c - C (constantCoeff c) = ∑ i, subst ρ (q i) * ρ i := by
    rw [← subst_C (a := ρ) (constantCoeff c), ← subst_sub hρ, ← hq, ← coe_substAlgHom hρ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, map_mul, substAlgHom_X]
  rw [this]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

end K2HKD

open MvPowerSeries in
theorem solution
    {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] {n : ℕ}
    (ρ : Fin n → MvPowerSeries (Fin n) B) (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0)
    (hN : ∃ N : ℕ, ∀ i : Fin n, (MvPowerSeries.X i : MvPowerSeries (Fin n) B) ^ N ∈ Ideal.span (Set.range ρ))
    (hfin : Module.Finite B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ))) :
    Module.Free B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ)) ∧
      ∀ (κ : Type) [Field κ] (f : B →+* κ),
        Module.finrank κ (MvPowerSeries (Fin n) κ ⧸ Ideal.span (Set.range fun i => MvPowerSeries.map f (ρ i))) =
          Module.finrank B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ)) := by
  classical
  have hρ : MvPowerSeries.HasSubst ρ := MvPowerSeries.hasSubst_of_constantCoeff_zero hρ0
  obtain ⟨d, b, hb⟩ := MvPowerSeries.exists_basis_subst_of_finite_quotient_of_isLocalRing ρ hρ0 hN hfin
  let I : Ideal (MvPowerSeries (Fin n) B) := Ideal.span (Set.range ρ)
  let K := MvPowerSeries (Fin n) B ⧸ I
  let mk : MvPowerSeries (Fin n) B →+* K := Ideal.Quotient.mk I
  let v : Fin d → K := fun j => mk (b j)

  have hred : ∀ c : Fin d → MvPowerSeries (Fin n) B,
      mk (∑ j, subst ρ (c j) * b j) = ∑ j, constantCoeff (c j) • v j := by
    intro c
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show Ideal.Quotient.mk I (subst ρ (c j) * b j) = constantCoeff (c j) • Ideal.Quotient.mk I (b j)
    rw [← Ideal.Quotient.mkₐ_eq_mk B, ← map_smul, smul_eq_C_mul, map_mul, map_mul]
    congr 1
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact K2HKD.subst_sub_C_constantCoeff_mem ρ hρ (c j)

  have hspan : ⊤ ≤ Submodule.span B (Set.range v) := by
    rintro x -
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, hc, -⟩ := hb g
    rw [show Ideal.Quotient.mk I g = mk g from rfl, hc, hred]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

  have hli : LinearIndependent B v := by
    rw [Fintype.linearIndependent_iff]
    intro β hβ j
    have h1 : ∑ j, C (β j) * b j ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, show Ideal.Quotient.mk I = mk from rfl, ← hβ]
      have := hred (fun j => C (β j))
      simp only [subst_C, constantCoeff_C] at this
      exact this
    obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun (MvPowerSeries (Fin n) B)).mp h1
    have hqi : ∀ i, ∃ cq : Fin d → MvPowerSeries (Fin n) B, q i = ∑ j, subst ρ (cq j) * b j :=
      fun i => (hb (q i)).exists
    choose cq hcq using hqi
    have hsub : ∀ j, subst ρ (∑ i, X i * cq i j) = ∑ i, ρ i * subst ρ (cq i j) := by
      intro j
      rw [← coe_substAlgHom hρ, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul, substAlgHom_X]
    have h2 : ∑ i, q i • ρ i = ∑ j, subst ρ (∑ i, X i * cq i j) * b j := by
      simp only [smul_eq_mul, hcq, hsub, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    have h3 : (fun j => C (β j)) = fun j => ∑ i, X i * cq i j :=
      (hb (∑ j, C (β j) * b j)).unique (by simp only [subst_C]) (by rw [← hq, h2])
    have h4 := congrArg constantCoeff (congrFun h3 j)
    simp only [constantCoeff_C, map_sum, map_mul, constantCoeff_X, zero_mul, Finset.sum_const_zero] at h4
    exact h4
  let basis : Module.Basis (Fin d) B K := Module.Basis.mk hli hspan
  haveI hfree : Module.Free B K := Module.Free.of_basis basis
  refine ⟨hfree, fun κ _ f => ?_⟩

  letI : Algebra B κ := f.toAlgebra
  obtain ⟨e, -⟩ := MvPowerSeries.exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem (S := κ) ρ hN
  rw [← Module.finrank_baseChange (R := κ) (S := B) (M' := K)]
  exact (e.toLinearEquiv.finrank_eq).symm

end S_MvPowerSeries_free_quotient_and_finrank_quotient_map_eq_of_finite_of_isLocalRing
end P2MW
export P2MW.S_MvPowerSeries_free_quotient_and_finrank_quotient_map_eq_of_finite_of_isLocalRing (solution)
