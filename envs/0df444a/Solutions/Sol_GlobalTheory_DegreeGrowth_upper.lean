-- Prove2me | solution 1 for GlobalTheory.DegreeGrowth.upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:45:27.366947+00:00
-- url     : https://prove2.me/submissions/e1e06bf4-861e-4d36-977d-4ba1128cc616

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankTotalDegreeImageGrowth
import Theorems.Thm_GlobalTheory_DegreeGrowth_finrank_boxSpan_le
import Theorems.Thm_GlobalTheory_DegreeGrowth_boxSpan_mono
import Theorems.Thm_GlobalTheory_DegreeGrowth_prod_mul_mem_boxSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.DegreeGrowth
variable {K B : Type} [Field K] [CommRing B] [Algebra K B]
namespace GlobalTheory.DegreeGrowth
theorem _root_.solution {s n m : ℕ} (y : Fin s → B) (b : Fin n → B)
    (hall : ∀ x : B, ∃ D, x ∈ boxSpan K y b D) (r : Fin m → B) :
    ∃ C : ℕ, ∀ t : ℕ, 1 ≤ t →
      Module.finrank K ((MvPolynomial.restrictTotalDegree (Fin m) K t).map
        (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap) ≤ C * t ^ s := by
  choose f hf using hall
  obtain ⟨d, hd⟩ : ∃ d, ∀ il : Fin m × Fin n, f (r il.1 * b il.2) ≤ d :=
    (Set.finite_range fun il : Fin m × Fin n => f (r il.1 * b il.2)).bddAbove.imp
      fun d hd il => hd ⟨il, rfl⟩
  have hr : ∀ i l, r i * b l ∈ boxSpan K y b d := fun i l =>
    boxSpan_mono y b (hd (i, l)) (hf _)
  refine ⟨n * (d + f 1 + 1) ^ s, fun t ht => ?_⟩
  have hle : (MvPolynomial.restrictTotalDegree (Fin m) K t).map
        (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap ≤
        boxSpan K y b (t * d + f 1) := by
    rintro _ ⟨p, hp, rfl⟩
    have hp' : p.totalDegree ≤ t := (MvPolynomial.mem_restrictTotalDegree _ _ _).1 hp
    rw [p.as_sum, map_sum]
    refine Submodule.sum_mem _ fun a ha => ?_
    have h1 := prod_mul_mem_boxSpan y b (f 1) d r hr a.support a (hf 1)
    have h2 : ∑ i ∈ a.support, a i ≤ t := (MvPolynomial.le_totalDegree ha).trans hp'
    rw [AlgHom.toLinearMap_apply, MvPolynomial.aeval_monomial, ← Algebra.smul_def]
    refine Submodule.smul_mem _ _ ?_
    rw [_root_.mul_one] at h1
    exact boxSpan_mono y b (by gcongr) h1
  refine (Submodule.finrank_mono hle).trans ((finrank_boxSpan_le y b _).trans ?_)
  rw [mul_comm, _root_.mul_assoc, ← mul_pow]
  gcongr
  nlinarith
end GlobalTheory.DegreeGrowth
