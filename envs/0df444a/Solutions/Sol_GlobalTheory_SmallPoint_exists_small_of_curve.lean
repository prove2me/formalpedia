-- Prove2me | solution 1 for GlobalTheory.SmallPoint.exists_small_of_curve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:18:21.314224+00:00
-- url     : https://prove2.me/submissions/2ec855f9-ee4c-419d-b3b6-370b7953e0c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SpecialisationNumberFieldAndCountableValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowCardLeNormProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsComplexPointNormLtOfNotIsUnit
import Theorems.Thm_GlobalTheory_SmallPoint_exists_extend_apply_eq
import Theorems.Thm_GlobalTheory_SmallPoint_exists_root_norm_lt
import Theorems.Thm_GlobalTheory_SmallPoint_exists_eventually_norm_le
import Theorems.Thm_GlobalTheory_RootNormLowerBound_exists_root_norm_lt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Topology
open GlobalTheory
open GlobalTheory.SmallPoint
namespace GlobalTheory.SmallPoint
theorem _root_.solution {R B : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing B] [IsDomain B] [Algebra R B] [Algebra.IsIntegral R B] [FaithfulSMul R B]
    (Ψ : R →+* ℂ[X]) (p : B →+* ℂ) (hp : p.comp (algebraMap R B) = (evalRingHom 0).comp Ψ)
    {n : ℕ} (w : Fin n → B) {u : B} (hu : p u = 0) {r : R} (hr : Ψ r ≠ 0) :
    ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ∃ (s : ℂ) (φ : B →+* ℂ),
      φ.comp (algebraMap R B) = (evalRingHom s).comp Ψ ∧ (Ψ r).eval s ≠ 0 ∧ ‖φ u‖ < ε ∧
        ∀ i, ‖φ (w i)‖ ≤ M := by
  choose M hM using fun i => exists_eventually_norm_le Ψ
    (Algebra.IsIntegral.isIntegral (R := R) (w i))
  refine ⟨∑ i, |M i|, fun ε hε => ?_⟩
  have hint := Algebra.IsIntegral.isIntegral (R := R) u
  have hF := minpoly.monic hint
  have h0 : (Ψ ((minpoly R u).coeff 0)).eval 0 = 0 := by
    have h := congrArg p (minpoly.aeval R u)
    rw [aeval_def, hom_eval₂, hu, eval₂_at_zero, hp, map_zero] at h
    exact h
  have h1 : ∀ᶠ s in 𝓝 (0 : ℂ),
      ‖(Ψ ((minpoly R u).coeff 0)).eval s‖ < ε ^ (minpoly R u).natDegree :=
    ((Ψ _).continuous.norm.tendsto 0).eventually (gt_mem_nhds (by
      simp only [h0, norm_zero]
      positivity))
  have h2 : ∀ᶠ s in 𝓝[≠] (0 : ℂ), ¬ (Ψ r).IsRoot s :=
    nhdsNE_le_cofinite _ (eventually_cofinite.2 (by
      simpa using (Ψ r).finite_setOf_isRoot hr))
  obtain ⟨s, hs2, hs1, hs3⟩ := (h2.and
    ((h1.and (eventually_all.2 hM)).filter_mono nhdsWithin_le_nhds)).exists
  obtain ⟨t, ht, htε⟩ := exists_root_norm_lt (hF.map ((evalRingHom s).comp Ψ)) hε (by
    rw [coeff_map, hF.natDegree_map]
    exact hs1)
  obtain ⟨φ, hφ, hφu⟩ := exists_extend_apply_eq ((evalRingHom s).comp Ψ) u t (by
    rwa [IsRoot, eval_map] at ht)
  refine ⟨s, φ, hφ, hs2, hφu ▸ htε, fun i => (hs3 i φ hφ).trans ((le_abs_self _).trans ?_)⟩
  exact Finset.single_le_sum (f := fun i => |M i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
end GlobalTheory.SmallPoint
