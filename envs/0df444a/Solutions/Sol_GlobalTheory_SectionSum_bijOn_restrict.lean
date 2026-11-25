-- Prove2me | solution 1 for GlobalTheory.SectionSum.bijOn_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:11:36.134845+00:00
-- url     : https://prove2.me/submissions/4d3153f4-8f01-4606-b7d0-ce6d4ae94a4a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SacSuccAbove
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AemeasurableFinsumSection
import Theorems.Thm_GlobalTheory_SectionSum_sImg_rel

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
open GlobalTheory.SectionSum
open MvPolynomial MeasureTheory
namespace GlobalTheory.SectionSum
theorem _root_.solution {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
    (j₀ : Fin (N + 1)) (x : Fin N → Ω) (sg : K →+* ℂ) (pt : TVar D N → ℂ)
    (hext : ∀ Q : Ω →+* ℂ, Q ∈ PT (Ω := Ω) sg →
      (∀ i : Fin D, pt (i.succ, j₀) + ∑ k, pt (i.succ, j₀.succAbove k) * Q (x k) = 0) →
      ∃! P : OmS Ω D N →+* ℂ, (∀ a : Ω, P (algebraMap Ω (OmS Ω D N) a) = Q a) ∧
        ∀ p, P (sImg j₀ x p) = pt p) :
    Set.BijOn (fun P : OmS Ω D N →+* ℂ => P.comp (algebraMap Ω (OmS Ω D N)))
      {P | ∀ p : MvPolynomial (TVar D N) K, P (sHom (K := K) j₀ x p) = eval₂ sg pt p}
      {Q | Q ∈ PT (Ω := Ω) sg ∧
        ∀ i : Fin D, pt (i.succ, j₀) + ∑ k, pt (i.succ, j₀.succAbove k) * Q (x k) = 0} := by
  have hX : ∀ P : OmS Ω D N →+* ℂ,
      (∀ p : MvPolynomial (TVar D N) K, P (sHom (K := K) j₀ x p) = eval₂ sg pt p) →
      ∀ p, P (sImg j₀ x p) = pt p := fun P hP p => by
    simpa [sHom] using hP (X p)
  have hmaps : Set.MapsTo (fun P : OmS Ω D N →+* ℂ => P.comp (algebraMap Ω (OmS Ω D N)))
      {P | ∀ p : MvPolynomial (TVar D N) K, P (sHom (K := K) j₀ x p) = eval₂ sg pt p}
      {Q | Q ∈ PT (Ω := Ω) sg ∧
        ∀ i : Fin D, pt (i.succ, j₀) + ∑ k, pt (i.succ, j₀.succAbove k) * Q (x k) = 0} := by
    intro P hP
    refine ⟨?_, fun i => ?_⟩
    · ext a
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply K Ω (OmS Ω D N)]
      have := hP (C a)
      rwa [show sHom (K := K) (D := D) j₀ x (C a) = algebraMap K _ a by
        rw [← MvPolynomial.algebraMap_eq]; exact (sHom (K := K) (D := D) j₀ x).commutes a,
        eval₂_C] at this
    · have := congrArg P (sImg_rel (D := D) j₀ x i)
      simpa [map_sum, map_mul, hX P hP] using this
  refine ⟨hmaps, ?_, ?_⟩
  · intro P₁ h₁ P₂ h₂ he
    have hm := hmaps h₁
    refine (hext _ hm.1 hm.2).unique ⟨fun a => rfl, hX _ h₁⟩ ⟨fun a => ?_, hX _ h₂⟩
    exact (DFunLike.congr_fun he a).symm
  · rintro Q ⟨hQ, hrel⟩
    obtain ⟨P, ⟨hP1, hP2⟩, -⟩ := hext Q hQ hrel
    refine ⟨P, fun p => ?_, RingHom.ext hP1⟩
    have : P.comp (sHom (K := K) (D := D) j₀ x).toRingHom = eval₂Hom sg pt := by
      apply MvPolynomial.ringHom_ext
      · intro a
        have h1 : sHom (K := K) (D := D) j₀ x (C a) = algebraMap K _ a := by
          rw [← MvPolynomial.algebraMap_eq]; exact (sHom (K := K) (D := D) j₀ x).commutes a
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, h1,
          coe_eval₂Hom, eval₂_C]
        rw [IsScalarTower.algebraMap_apply K Ω (OmS Ω D N), hP1]
        exact DFunLike.congr_fun hQ a
      · intro q
        simp [sHom, hP2]
    exact DFunLike.congr_fun this p
end GlobalTheory.SectionSum
