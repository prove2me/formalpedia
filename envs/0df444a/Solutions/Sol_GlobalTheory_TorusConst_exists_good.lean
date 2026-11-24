-- Prove2me | solution 1 for GlobalTheory.TorusConst.exists_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:48:28.525543+00:00
-- url     : https://prove2.me/submissions/554494c3-2cd3-4b3c-9a99-f8ee501c15cf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst
import Theorems.Thm_GlobalTheory_TorusConst_exists_elim
import Theorems.Thm_GlobalTheory_TorusConst_spm_val
import Theorems.Thm_GlobalTheory_TorusConst_Glue_symm
import Theorems.Thm_GlobalTheory_TorusConst_exists_poly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.TorusConst
open Polynomial TorusToProper
variable {K : Type} [Field K] {B : Over (Spec (CommRingCat.of K))}
namespace GlobalTheory.TorusConst
theorem _root_.solution {R L : Type} [CommRing R] [Algebra K R] [Field L] [Algebra K L]
    {F G : sp K R[X] ⟶ B} (h : Glue F G) (V : B.left.Opens) (e : R →ₐ[K] L)
    (he : Function.Surjective e)
    (hF : ∀ q, (val F (CAlgHom.comp e) (X : L[X])).left q ∈ V)
    (hG : ∀ q, (val G (CAlgHom.comp e) (X : L[X])).left q ∈ V) :
    ∃ g : R, e g ≠ 0 ∧ ∀ (A : Type) [Field A] [Algebra K A] (c : R →ₐ[K] A), c g ≠ 0 →
      ∀ q, (val F (CAlgHom.comp c) (X : A[X])).left q ∈ V := by
  obtain ⟨a, ha, ha'⟩ := exists_poly F V e he hF
  obtain ⟨b, hb, hb'⟩ := exists_poly G V e he hG
  obtain ⟨g, hg, hg'⟩ := exists_elim (e : R →+* L) a b ha hb
  refine ⟨g, hg, fun A _ _ c hc (q : PrimeSpectrum A[X]) => ?_⟩
  let κ := q.asIdeal.ResidueField
  let π : A[X] →ₐ[K] κ := IsScalarTower.toAlgHom K A[X] κ
  let o : PrimeSpectrum κ := ⟨⊥, Ideal.isPrime_bot⟩
  have hq : (spm π).left o = q := by
    apply PrimeSpectrum.ext
    exact Ideal.ker_algebraMap_residueField q.asIdeal
  have h1 : (val F (π.comp (CAlgHom.comp c)) (π X)).left o =
      (val F (CAlgHom.comp c) (X : A[X])).left q := by
    rw [← spm_val]
    exact congrArg (val F (CAlgHom.comp c) (X : A[X])).left hq
  by_contra hn
  rw [← h1] at hn
  have h2 := hg' κ _ (π X) (ha' κ _ _ o hn) (fun hx => hb' κ _ _ o (by rwa [← h κ _ _ hx]))
  exact hc (((π.comp CAlgHom : A →ₐ[K] κ) : A →+* κ).injective (h2.trans (map_zero _).symm))
end GlobalTheory.TorusConst
