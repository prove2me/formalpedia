-- Prove2me | solution 1 for GlobalTheory.exists_grCube_hom_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:08:06.088605+00:00
-- url     : https://prove2.me/submissions/63eabd70-3466-47e5-9993-70ff776f2f2d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsHomLocBijectiveGrSum
import Theorems.Thm_GlobalTheory_exists_homLoc_bijective_grSum
import Theorems.Thm_GlobalTheory_homLoc_grSum_res

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory DirectSum MvPolynomial
noncomputable section
open GlobalTheory
open GradedHilbert
namespace GlobalTheory
theorem _root_.solution (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R]
    (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢]
    [Decomposition 𝒢] (A : ℤ → Cube.{0} ι R) (x : ι → ∀ t, A t ⟶ A (t + 1))
    (hx : ∀ I : Finset ι,
      OperatorsCommute (A := fun t => (A t).obj I) fun i t => ((x i t).app I).hom)
    (ρ : ∀ I : Finset ι, G →ₗ[MvPolynomial ι R] GrSum (hx I))
    (hρ : ∀ I, IsGradedMap 𝒢 (GrSum.grading (hx I)) (ρ I))
    (hres : ∀ (I J : Finset ι) (h : I ⊆ J) (n : ℤ) (y : G) (a : (A n).obj I),
      ρ I y = GrSum.of (hx I) n a → ρ J y = GrSum.of (hx J) n (Cube.res (A n) h a))
    (hbij : ∀ (I : Finset ι), ∀ i ∈ I, ∀ t, Function.Bijective ((x i t).app I).hom)
    (hker : ∀ (I : Finset ι) (n : ℤ), ∀ y ∈ 𝒢 n, ρ I y = 0 → ∃ k : ℕ, xProd R I ^ k • y = 0)
    (hcoker : ∀ (I : Finset ι) (t : ℤ) (a : (A t).obj I), ∃ (k : ℕ) (y : G),
      ρ I y = xProd R I ^ k • GrSum.of (hx I) t a) (t : ℤ) :
    ∃ φ : grCube ι 𝒢 t ⟶ A t, ∀ I, Function.Bijective (φ.app I).hom := by
  choose φ hφ hφ' using fun I =>
    exists_homLoc_bijective_grSum (hx I) (hρ I) I (hbij I) (hker I) (hcoker I) t
  refine ⟨Cube.homMk (A := grCube ι 𝒢 t) φ fun {I J} h z => ?_, hφ⟩
  exact homLoc_grSum_res (hx I) (hx J) (fun n => Cube.res (A n) h)
    (fun i n a => (Cube.app_res (x i n) h a).symm) (hρ I) (hres I J h) h (hbij J) z _ _
    (hφ' I z) (hφ' J _)
end GlobalTheory
