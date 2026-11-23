-- Prove2me | solution 1 for GlobalTheory.UnitLemma.HilbertNinety.exists_unit_sigma
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:14.481012+00:00
-- url     : https://prove2.me/submissions/65a858f5-03d2-4d61-bb9c-d3095c535365

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitSigmaEqMulHilbert90InvAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.HilbertNinety
namespace GlobalTheory.UnitLemma.HilbertNinety
theorem _root_.solution (K : UQ) (B : InvAlg K) (u : B.A) (hu : u * B.σ u = 1) :
    ∃ β : B.Aˣ, B.σ (β : B.A) = β * u := by
  classical
  letI : Module ℚ B.A := Module.compHom B.A (algebraMap ℚ K.E)
  let b : B.A →+ B.A :=
    { toFun := fun a => a + B.σ a * B.σ u
      map_zero' := by simp
      map_add' := by intro x y; simp only [map_add]; ring }
  have hb : ∀ a, b a = a + B.σ a * B.σ u := fun a => rfl
  have hbσ : ∀ a, B.σ (b a) = b a * u := by
    intro a
    rw [hb, map_add, map_mul, B.σ_σ, B.σ_σ]
    linear_combination (-(B.σ a)) * hu
  obtain ⟨x, y, hxy, hne⟩ := K.c_res
  set e : K.E := algebraMap K.O K.E x with he
  have hce : K.c e - e ≠ 0 := by
    intro h
    rw [sub_eq_zero, he, hxy] at h
    have := IsFractionRing.injective K.O K.E h
    exact hne (by rw [this, sub_self]; exact Ideal.zero_mem _)
  have key : ∀ z : B.A, algebraMap K.E B.A (K.c e - e) * z =
      algebraMap K.E B.A (K.c e) * b z - b (algebraMap K.E B.A e * z) := by
    intro z
    rw [hb, hb, map_mul, B.σ_alg, map_sub]
    ring
  haveI : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A
  haveI : Fintype (MaximalSpectrum B.A) := Fintype.ofFinite _
  let S : MaximalSpectrum B.A → Submodule ℚ B.A := fun m =>
    { carrier := {a | b a ∈ m.asIdeal}
      add_mem' := fun {a c} ha hc => by
        change b (a + c) ∈ m.asIdeal
        rw [map_add]; exact m.asIdeal.add_mem ha hc
      zero_mem' := by change b 0 ∈ m.asIdeal; rw [map_zero]; exact m.asIdeal.zero_mem
      smul_mem' := fun q a ha => by
        change b (q • a) ∈ m.asIdeal
        rw [map_rat_smul]
        change (algebraMap ℚ K.E q) • b a ∈ m.asIdeal
        rw [Algebra.smul_def]
        exact m.asIdeal.mul_mem_left _ ha }
  have hS : ⊤ ∉ Finset.univ.image S := by
    intro h
    obtain ⟨m, -, hm⟩ := Finset.mem_image.1 h
    have hall : ∀ a, b a ∈ m.asIdeal := fun a => by
      have : a ∈ S m := hm ▸ Submodule.mem_top
      exact this
    have h1 : algebraMap K.E B.A (K.c e - e) ∈ m.asIdeal := by
      have := key 1
      rw [mul_one] at this
      rw [this]
      exact m.asIdeal.sub_mem (m.asIdeal.mul_mem_left _ (hall 1)) (hall _)
    apply m.isMaximal.ne_top
    rw [Ideal.eq_top_iff_one]
    have h2 : algebraMap K.E B.A (K.c e - e)⁻¹ * algebraMap K.E B.A (K.c e - e) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hce, map_one]
    rw [← h2]
    exact m.asIdeal.mul_mem_left _ h1
  have h3 := Subspace.biUnion_ne_univ_of_top_notMem hS
  obtain ⟨a, ha⟩ := (Set.ne_univ_iff_exists_notMem _).1 h3
  have hunit : IsUnit (b a) := by
    by_contra hn
    obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits hn
    apply ha
    exact Set.mem_biUnion (x := S ⟨m, hm⟩) (by simp) hxm
  exact ⟨hunit.unit, by rw [IsUnit.unit_spec]; exact hbσ a⟩
end GlobalTheory.UnitLemma.HilbertNinety
