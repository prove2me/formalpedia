-- Prove2me | solution 1 for GlobalTheory.JR.Hyp.coord_structure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:59:57.679114+00:00
-- url     : https://prove2.me/submissions/f9b6c618-2851-4aad-9dd3-ece13e71875f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdempotentCoordinatesStructure
import Theorems.Thm_GlobalTheory_JR_Et_quadratic_structure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Hyp
namespace GlobalTheory.JR.Hyp
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (e : A.L), e * e = e → star e = 1 - e → (∀ p, Hyp.ci A e (Hyp.cc A e p) = p) ∧ (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) ∧ (∀ p, A.NL (Hyp.cc A e p) = p.1 * p.2) ∧ (∀ (ψ : AddChar F ℂ) (x : A.K) (p q : A.K × A.K), A.kerL ψ x (Hyp.cc A e q) (Hyp.cc A e p) = Hyp.kx A ψ x q.1 p.2 * Hyp.kx A ψ x q.2 p.1) ∧ (∀ (s : A.K) p, s • Hyp.cc A e p = Hyp.cc A e (s * p.1, s * p.2)) ∧ ∀ s : A.Kˣ, IsUnit (Hyp.cc A e ((s : A.K), 1)) := by
  intro F E _ _ _ _ _ A e hee hse
  obtain ⟨-, hinj, hnorm, htr, -⟩ := Et.quadratic_structure F E A
  have htrs : ∀ (a : A.K) (f : A.L),
      Algebra.trace A.K A.L (algebraMap A.K A.L a * f) = a * Algebra.trace A.K A.L f := by
    intro a f
    rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  have hone : ∀ f : A.L, star f = 1 - f → Algebra.trace A.K A.L f = 1 := by
    intro f hf
    apply hinj
    rw [htr, hf, map_one]
    ring
  have hte : Algebra.trace A.K A.L e = 1 := hone e hse
  have htf : Algebra.trace A.K A.L (1 - e) = 1 :=
    hone (1 - e) (by rw [star_sub, star_one, hse])
  have hst : ∀ p : A.K × A.K, star (Hyp.cc A e p) =
      algebraMap A.K A.L p.1 * (1 - e) + algebraMap A.K A.L p.2 * e := by
    intro p
    simp only [Hyp.cc, star_add, star_mul, star_sub, star_one, hse, A.star_K]
    ring
  have hme : ∀ p : A.K × A.K, Hyp.cc A e p * e = algebraMap A.K A.L p.1 * e := by
    intro p
    simp only [Hyp.cc]
    linear_combination (algebraMap A.K A.L p.1 - algebraMap A.K A.L p.2) * hee
  have hmf : ∀ p : A.K × A.K, Hyp.cc A e p * (1 - e) = algebraMap A.K A.L p.2 * (1 - e) := by
    intro p
    simp only [Hyp.cc]
    linear_combination (algebraMap A.K A.L p.2 - algebraMap A.K A.L p.1) * hee
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    simp only [Hyp.ci]
    rw [hme p, hmf p, htrs, htrs, hte, htf, mul_one, mul_one]
  · intro y
    simp only [Hyp.cc, Hyp.ci, htr, star_mul, star_sub, star_one, hse]
    linear_combination (2 * y - 2 * star y) * hee
  · intro p
    apply hinj
    rw [hnorm, hst, map_mul]
    simp only [Hyp.cc]
    linear_combination (-(algebraMap A.K A.L p.1 - algebraMap A.K A.L p.2) ^ 2) * hee
  · intro ψ x p q
    have hprod : star (Hyp.cc A e q) * Hyp.cc A e p =
        algebraMap A.K A.L (q.1 * p.2) * (1 - e) + algebraMap A.K A.L (q.2 * p.1) * e := by
      rw [hst]
      simp only [Hyp.cc, map_mul]
      linear_combination
        (algebraMap A.K A.L q.1 * algebraMap A.K A.L p.2 + algebraMap A.K A.L q.2 * algebraMap A.K A.L p.1
          - algebraMap A.K A.L q.1 * algebraMap A.K A.L p.1
          - algebraMap A.K A.L q.2 * algebraMap A.K A.L p.2) * hee
    have ht : Algebra.trace A.K A.L (star (Hyp.cc A e q) * Hyp.cc A e p) = q.1 * p.2 + q.2 * p.1 := by
      rw [hprod, map_add, htrs, htrs, hte, htf, mul_one, mul_one]
    simp only [Et.kerL, Hyp.kx, Et.psiK]
    rw [ht]
    rw [show x * (q.1 * p.2 + q.2 * p.1) = x * q.1 * p.2 + x * q.2 * p.1 by ring, map_add,
      AddChar.map_add_eq_mul]
  · intro s p
    simp only [Hyp.cc, Algebra.smul_def, map_mul]
    ring
  · intro s
    have hs : algebraMap A.K A.L (s : A.K) * algebraMap A.K A.L ((s⁻¹ : A.Kˣ) : A.K) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    refine isUnit_iff_exists_inv.mpr ⟨Hyp.cc A e (((s⁻¹ : A.Kˣ) : A.K), 1), ?_⟩
    simp only [Hyp.cc, map_one]
    linear_combination
      (2 - algebraMap A.K A.L (s : A.K) - algebraMap A.K A.L ((s⁻¹ : A.Kˣ) : A.K)) * hee + e * e * hs
end GlobalTheory.JR.Hyp
