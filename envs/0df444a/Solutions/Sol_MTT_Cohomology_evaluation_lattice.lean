-- Prove2me | solution 1 for MTT.Cohomology.evaluation_lattice
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-06T14:46:49.747115+00:00
-- url     : https://prove2.me/submissions/c1f75f61-2369-4099-8e5d-db2cfee0025a

import Definitions.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

namespace P2MLat

open MvPolynomial

variable {N n : ℕ}

/-- Evaluating a class obtained from an integral class by coefficientwise extension
returns the image of the integer evaluation of the integral class. -/
theorem evaluation_extends {R : Type*} [CommRing R]
    (φ : Hc N n ℤ) (Φ : Hc N n R) (h : Extends (Int.castRingHom R) φ Φ)
    (j : ℕ) (r : ℚ) :
    evaluation j r Φ = ((evaluation j r φ : ℤ) : R) := by
  simp only [evaluation, LinearMap.coe_mk, AddHom.coe_mk]
  rw [h OnePoint.infty ((r : Cusp)), MvPolynomial.coeff_map]
  simp

end P2MLat

open P2MLat in
theorem solution {N n : ℕ} (hZ : Module.Finite ℤ (Hc N n ℤ))
    (hQ : BaseChange N n MTT.Qbar) (ψ : Bool → Hc N n MTT.Qbar) :
    (Submodule.span ℤ {v : MTT.Qbar | ∃ s j r, j ≤ n ∧
      v = evaluation j r (ψ s) / (n.choose j : MTT.Qbar)}).FG := by
  classical
  obtain ⟨e, he⟩ := hQ
  -- Every class is a finite algebraic combination of coefficientwise-integral classes.
  have hex : ∀ s : Bool, ∃ S : Finset (MTT.Qbar × Hc N n ℤ),
      e.symm (ψ s) = ∑ i ∈ S, i.1 ⊗ₜ[ℤ] i.2 := fun s => TensorProduct.exists_finset _
  choose S hS using hex
  have key : ∀ (s : Bool) (j : ℕ) (r : ℚ),
      evaluation j r (ψ s) = ∑ i ∈ S s, i.1 * ((evaluation j r i.2 : ℤ) : MTT.Qbar) := by
    intro s j r
    have h1 : ψ s = ∑ i ∈ S s, i.1 • e (1 ⊗ₜ[ℤ] i.2) := by
      conv_lhs => rw [← e.apply_symm_apply (ψ s), hS s]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← LinearEquiv.map_smul e]
      congr 1
      rw [TensorProduct.smul_tmul']
      simp
    rw [h1, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, evaluation_extends i.2 _ (he i.2) j r, smul_eq_mul]
  -- The finitely many algebraic coefficients, divided by the finitely many binomials.
  set G : Finset MTT.Qbar :=
    ((S true ∪ S false) ×ˢ Finset.range (n + 1)).image
      (fun q => q.1.1 / (n.choose q.2 : MTT.Qbar)) with hG
  refine Submodule.FG.of_le (T := Submodule.span ℤ (G : Set MTT.Qbar)) ⟨G, rfl⟩ ?_
  rw [Submodule.span_le]
  rintro v ⟨s, j, r, hj, rfl⟩
  rw [key s j r, Finset.sum_div]
  refine Submodule.sum_mem _ fun i hi => ?_
  have hrw : i.1 * ((evaluation j r i.2 : ℤ) : MTT.Qbar) / (n.choose j : MTT.Qbar)
      = (evaluation j r i.2 : ℤ) • (i.1 / (n.choose j : MTT.Qbar)) := by
    rw [zsmul_eq_mul]; ring
  rw [hrw]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  rw [hG, Finset.coe_image]
  refine ⟨(i, j), ?_, rfl⟩
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_union,
    Finset.mem_range]
  exact ⟨by cases s with | false => exact Or.inr hi | true => exact Or.inl hi, by omega⟩
