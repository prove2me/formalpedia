-- Prove2me | solution 1 for GlobalTheory.exists_hensel_generator_of_residue_finite_unramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:42:33.711836+00:00
-- url     : https://prove2.me/submissions/924f02a2-8274-40af-adb1-3caf2b9be624

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPrimitiveElementUnramified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open IsLocalRing Polynomial
namespace GlobalTheory
open IsLocalRing Polynomial in
private lemma residue_eval_map_eq {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R]
    [IsLocalRing R] (φ : A →+* R) [IsLocalHom φ] (P : A[X]) (x : R) :
    residue R ((P.map φ).eval x) =
      (P.map (residue A)).eval₂ (ResidueField.map φ) (residue R x) := by
  rw [eval_map, hom_eval₂, eval₂_map]
  congr 1
end GlobalTheory
end

set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory
open IsLocalRing Polynomial
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (φ : A →+* R) [IsLocalHom φ], ((residue R).comp φ).Finite → ((residue R).comp φ).FormallyUnramified → ∃ (θ : R) (q : Polynomial A), q.Monic ∧ (q.map φ).eval θ = 0 ∧ IsUnit ((q.derivative.map φ).eval θ) ∧ (∀ r : R, ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R) ∧ ∀ P : Polynomial A, P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R → ∀ i, P.coeff i ∈ maximalIdeal A := by
  intro A R _ _ _ _ _ φ _ hfin hunr
  have hcomp : (residue R).comp φ = (ResidueField.map φ).comp (residue A) :=
    RingHom.ext fun a => (ResidueField.map_residue φ a).symm
  rw [hcomp] at hfin hunr
  letI : Algebra (ResidueField A) (ResidueField R) := (ResidueField.map φ).toAlgebra
  haveI : Module.Finite (ResidueField A) (ResidueField R) := hfin.of_comp_finite
  haveI : Algebra.FormallyUnramified (ResidueField A) (ResidueField R) := hunr.of_comp
  haveI : Algebra.IsSeparable (ResidueField A) (ResidueField R) :=
    Algebra.FormallyUnramified.isSeparable _ _
  set pb := Field.powerBasisOfFiniteOfSeparable (ResidueField A) (ResidueField R)
  set f := minpoly (ResidueField A) pb.gen with hf
  have hfmonic : f.Monic := minpoly.monic pb.isIntegral_gen
  have hfroot : aeval pb.gen f = 0 := minpoly.aeval _ _
  have hfder : aeval pb.gen (derivative f) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable _ pb.gen).aeval_derivative_ne_zero hfroot
  obtain ⟨q, hqf, hqdeg, hqmonic⟩ := lifts_and_natDegree_eq_and_monic
    ((mem_lifts f).2 (map_surjective (residue A) residue_surjective f)) hfmonic
  obtain ⟨θ₀, hθ₀⟩ := residue_surjective pb.gen
  have key : ∀ (P : A[X]) (x : R), residue R x = pb.gen →
      residue R ((P.map φ).eval x) = aeval pb.gen (P.map (residue A)) := by
    intro P x hx
    rw [residue_eval_map_eq, hx]
    rfl
  obtain ⟨θ, hroot, hθ⟩ := HenselianRing.is_henselian (I := maximalIdeal R) (q.map φ)
    (hqmonic.map φ) θ₀
    (by rw [← residue_eq_zero_iff, key _ _ hθ₀, hqf, hfroot])
    (by
      rw [derivative_map]
      change IsUnit (residue R _)
      rw [key _ _ hθ₀, ← derivative_map, hqf]
      exact isUnit_iff_ne_zero.2 hfder)
  have hθres : residue R θ = pb.gen := by
    rw [← hθ₀, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hθ
  refine ⟨θ, q, hqmonic, hroot, ?_, ?_, ?_⟩
  · rw [← residue_ne_zero_iff_isUnit, key _ _ hθres, ← derivative_map, hqf]
    exact hfder
  · intro r
    obtain ⟨g, hg⟩ := pb.exists_eq_aeval' (residue R r)
    obtain ⟨P, hP⟩ := map_surjective (residue A) residue_surjective g
    refine ⟨P, ?_⟩
    rw [← residue_eq_zero_iff, map_sub, key _ _ hθres, hP, hg, sub_self]
  · intro P hdeg hmem i
    rw [← residue_eq_zero_iff, key _ _ hθres] at hmem
    have hzero : P.map (residue A) = 0 := by
      by_contra hne
      have h1 := minpoly.degree_le_of_ne_zero (ResidueField A) pb.gen hne hmem
      have h2 := natDegree_le_natDegree h1
      have h3 : (P.map (residue A)).natDegree ≤ P.natDegree := natDegree_map_le
      rw [← hf, ← hqdeg] at h2
      omega
    rw [← residue_eq_zero_iff, ← coeff_map, hzero, coeff_zero]
end _root_.GlobalTheory
end GlobalTheory
