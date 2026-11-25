-- Prove2me | solution 1 for GlobalTheory.homLoc_grSum_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:36:09.476339+00:00
-- url     : https://prove2.me/submissions/26ab965b-27c6-44a7-b2ba-7646a1c9a255

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsHomLocBijectiveGrSum
import Theorems.Thm_GlobalTheory_GrSum_X_smul_bijective
import Theorems.Thm_GlobalTheory_xProd_smul_bijective_of
import Theorems.Thm_GlobalTheory_GrSum_map_of
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GrSum.map_of



set_option autoImplicit false
open CategoryTheory DirectSum MvPolynomial
noncomputable section
open GlobalTheory
open GradedHilbert
variable {ι : Type} {R : Type} [CommRing R]
namespace GlobalTheory
theorem _root_.solution
    {M : Type} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M]
    {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ]
    {A : ℤ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x)
    {B : ℤ → Type} [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
    {y : ι → ∀ n, B n →ₗ[R] B (n + 1)} (hy : OperatorsCommute y)
    (r : ∀ n, A n →ₗ[R] B n) (hr : ∀ i n a, r (n + 1) (x i n a) = y i n (r n a))
    {f : M →ₗ[MvPolynomial ι R] GrSum hx} (hf : IsGradedMap ℳ (GrSum.grading hx) f)
    {g : M →ₗ[MvPolynomial ι R] GrSum hy}
    (hfg : ∀ n m a, f m = GrSum.of hx n a → g m = GrSum.of hy n (r n a))
    {s t : Finset ι} (h : s ⊆ t) (hb : ∀ i ∈ t, ∀ n, Function.Bijective (y i n)) {n : ℤ}
    (z : homLoc ℳ s n) (a : A n) (b : B n)
    (ha : ∀ (k : ℕ) (m : M), awayFrac M (xProd R s) k m = z →
      xProd R s ^ k • GrSum.of hx n a = f m)
    (hb' : ∀ (k : ℕ) (m : M), awayFrac M (xProd R t) k m = homLocRes ℳ h n z →
      xProd R t ^ k • GrSum.of hy n b = g m) : b = r n a := by
  obtain ⟨k, m, hm, e⟩ := z.2
  obtain ⟨a', ha'⟩ := hf hm
  have h1 : g m = GrSum.map hx hy r hr (f m) := by
    rw [hfg _ m a' ha'.symm, ← ha', GrSum.map_of]
  obtain ⟨c, hc⟩ : ∃ c, xProd R t = c * xProd R s :=
    exists_eq_mul_left_of_dvd (Finset.prod_dvd_prod_of_subset s t X h)
  have h2 := hb' k (c ^ k • m) (by rw [coe_homLocRes, ← e, locRes_awayFrac X h hc])
  rw [map_smul, h1, ← ha k m e, map_smul, GrSum.map_of, ← mul_smul, ← mul_pow, ← hc] at h2
  have h3 := xProd_smul_bijective_of t fun i hi => GrSum.X_smul_bijective hy (hb i hi)
  exact GrSum.of_injective hy n (IsSMulRegular.pow k h3.1 h2)
end GlobalTheory
