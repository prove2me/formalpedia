-- Prove2me | solution 1 for GlobalTheory.generic_points_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:36:38.282391+00:00
-- url     : https://prove2.me/submissions/71187565-9a89-4db3-b67b-580ca1dce8e9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsEmbeddingsOverInjective
import Theorems.Thm_GlobalTheory_exists_natForm_norm_ge
import Theorems.Thm_GlobalTheory_exists_root_near_of_norm_eval_lt
import Theorems.Thm_GlobalTheory_exists_embeddings_over_injective
import Theorems.Thm_P2M_GlobalTheory_continuous_eval_map_eval_Hom_64cad5ce05d5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : (∀ (K : Type) [Field K] [Countable K] (sg : K →+* ℂ) (D : ℕ) (z₀ : Fin D → ℂ) (ε : ℝ), 0 < ε → ∃ z : Fin D → ℂ, (∀ i, ‖z i - z₀ i‖ < ε) ∧ ∀ p : MvPolynomial (Fin D) K, p ≠ 0 → MvPolynomial.eval₂ sg z p ≠ 0) → ∀ (K A Ω : Type) [Field K] [NumberField K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω] [Algebra K Ω] [IsScalarTower K A Ω] (sg : K →+* ℂ) (φ : A →+* ℂ), φ.comp (algebraMap K A) = sg → ∀ (S : Finset A) (ε : ℝ), 0 < ε → ∃ P ∈ PT (Ω := Ω) sg, ∀ a ∈ S, ‖P (algebraMap A Ω a) - φ a‖ < ε := by
  intro hgen K A Ω _ _ _ _ _ _ _ _ _ _ _ sg φ hφ S ε hε
  classical
  obtain ⟨D, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg K A
  let R := MvPolynomial (Fin D) K
  let _ : Algebra R A := g.toRingHom.toAlgebra
  have : Module.Finite R A := hfin
  have : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).2 hinj
  have : Countable K := Countable.of_equiv _ (Module.finBasis ℚ K).equivFun.toEquiv.symm
  obtain ⟨n, hn⟩ := exists_embeddings_over_injective R A Ω
  let z₀ : Fin D → ℂ := fun i => φ (g (MvPolynomial.X i))
  have hz₀ : MvPolynomial.eval₂Hom sg z₀ = φ.comp (algebraMap R A) := by
    apply MvPolynomial.ringHom_ext
    · intro k
      change _ = φ (g (algebraMap K _ k))
      rw [AlgHom.commutes, ← hφ]
      simp
    · intro i
      simp only [MvPolynomial.eval₂Hom_X']
      rfl
  let b : (S → Fin (n + 1)) → A := fun c => ∑ a : S, ((c a : ℕ) : A) * (a : A)
  have hev : ∀ᶠ z in nhds z₀, ∀ c, ‖((minpoly R (b c)).map (MvPolynomial.eval₂Hom sg z)).eval
      (φ (b c))‖ < (ε / 2) ^ (minpoly R (b c)).natDegree := by
    rw [Filter.eventually_all]
    intro c
    refine ((continuous_eval_map_eval₂Hom sg (minpoly R (b c)) (φ (b c))).norm.tendsto
      z₀).eventually_lt_const ?_
    have h0 : ((minpoly R (b c)).map (MvPolynomial.eval₂Hom sg z₀)).eval (φ (b c)) = 0 := by
      rw [hz₀, Polynomial.eval_map, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def,
        minpoly.aeval, map_zero]
    simp only [h0, norm_zero]
    positivity
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨z, hz, hzg⟩ := hgen K sg D z₀ η hη
  have hτ : Function.Injective (MvPolynomial.eval₂Hom sg z) := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra h
    exact hzg p h hp
  obtain ⟨T, hT, hover, hroot⟩ := hn _ hτ
  have hsmall := hball (y := z) ((dist_pi_lt_iff hη).2 fun i => by
    rw [dist_eq_norm]; exact hz i)
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hc⟩ := exists_natForm_norm_ge T n hT
    (fun σ (a : S) => σ (algebraMap A Ω a) - φ a) ε (by
      intro σ hσ
      have hP : σ ∈ PT (Ω := Ω) sg := by
        ext k
        have := RingHom.congr_fun (hover σ hσ) (MvPolynomial.C k)
        rw [MvPolynomial.eval₂Hom_C] at this
        rw [← this]
        change σ _ = σ (algebraMap A Ω (g (algebraMap K _ k)))
        rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
      obtain ⟨a, ha, h⟩ := hcon σ hP
      exact ⟨⟨a, ha⟩, h⟩)
  have hmon : (minpoly R (b c)).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral _)
  obtain ⟨r, hr, hrε⟩ := exists_root_near_of_norm_eval_lt _
    (hmon.map (MvPolynomial.eval₂Hom sg z)) (φ (b c)) (ε / 2) (by positivity)
    (by rw [hmon.natDegree_map]; exact hsmall c)
  obtain ⟨σ, hσ, rfl⟩ := hroot _ r hr
  refine absurd hrε (not_lt.2 ?_)
  have hc' := hc σ hσ
  simpa only [b, map_sum, map_mul, map_natCast, mul_sub, Finset.sum_sub_distrib] using hc'
end GlobalTheory
