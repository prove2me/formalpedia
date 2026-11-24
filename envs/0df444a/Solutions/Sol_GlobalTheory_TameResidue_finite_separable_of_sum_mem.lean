-- Prove2me | solution 1 for GlobalTheory.TameResidue.finite_separable_of_sum_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:27:41.46541+00:00
-- url     : https://prove2.me/submissions/015383d2-e0d6-4b28-9fdf-2a2a8a1d582d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FiniteSeparableOfSumMem
import Theorems.Thm_GlobalTheory_TameResidue_exists_sum_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.TameResidue
namespace GlobalTheory.TameResidue
theorem _root_.solution {D k K : Type} [Group D] [Fintype D] [Field k] [Field K]
    [Algebra k K] (φ : D →* (K ≃ₐ[k] K)) (h : (Nat.card φ.ker : K) ≠ 0)
    (hT : ∀ x : K, ∃ c : k, algebraMap k K c = ∑ g, φ g x) :
    FiniteDimensional k K ∧ Algebra.IsSeparable k K := by
  classical
  obtain ⟨w, hw⟩ := exists_sum_ne_zero φ h
  obtain ⟨c, hc⟩ := hT w
  have hcw : algebraMap k K c ≠ 0 := by rw [hc]; exact hw
  have hfix : ∀ y : K, (∀ g : D, φ g y = y) → ∃ c' : k, algebraMap k K c' = y := by
    intro y hy
    obtain ⟨c', hc'⟩ := hT (y * w)
    refine ⟨c' / c, ?_⟩
    rw [map_div₀, hc', div_eq_iff hcw, hc]
    simp only [map_mul, hy, Finset.mul_sum]
  letI : MulSemiringAction D K := MulSemiringAction.compHom K φ
  have hF : ∀ x : FixedPoints.subfield D K, ∃ c' : k, algebraMap k K c' = x :=
    fun x => hfix x fun g => x.2 g
  refine ⟨?_, ?_⟩
  · let b := Module.finBasis (FixedPoints.subfield D K) K
    refine ⟨⟨Finset.univ.image b, eq_top_iff.2 fun x _ => ?_⟩⟩
    rw [← b.sum_repr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c', hc'⟩ := hF (b.repr x i)
    have he : b.repr x i • b i = c' • b i := by
      rw [Algebra.smul_def, Algebra.smul_def, hc']
      rfl
    rw [he]
    exact Submodule.smul_mem _ c' (Submodule.subset_span
      (Finset.mem_coe.2 (Finset.mem_image_of_mem b (Finset.mem_univ i))))
  · refine ⟨fun x => ?_⟩
    have hsF : (minpoly (FixedPoints.subfield D K) x).Separable :=
      Algebra.IsSeparable.isSeparable (FixedPoints.subfield D K) x
    have hl : (minpoly (FixedPoints.subfield D K) x).map
        (algebraMap (FixedPoints.subfield D K) K) ∈ Polynomial.lifts (algebraMap k K) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      obtain ⟨c', hc'⟩ := hF ((minpoly (FixedPoints.subfield D K) x).coeff n)
      exact ⟨c', hc'⟩
    obtain ⟨pk, hpk⟩ := Polynomial.mem_lifts _ |>.1 hl
    have hsep : pk.Separable := by
      rw [← Polynomial.separable_map (algebraMap k K), hpk, Polynomial.separable_map]
      exact hsF
    have hx : Polynomial.aeval x pk = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, hpk, Polynomial.eval_map,
        ← Polynomial.aeval_def, minpoly.aeval]
    exact hsep.of_dvd (minpoly.dvd k x hx)
end GlobalTheory.TameResidue
