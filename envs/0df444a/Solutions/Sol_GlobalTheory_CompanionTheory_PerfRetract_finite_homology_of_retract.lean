-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfRetract.finite_homology_of_retract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:38:59.810445+00:00
-- url     : https://prove2.me/submissions/03e3b56c-47a6-470e-a147-ca619cf43c1a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HomotopyProjectorComplexBounded
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfRetract_finite_homology_of_surjective
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfRetract_cyclesMap_surjective
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PerfRetract
variable {R : Type} [CommRing R] {E : ℕ → Type} [∀ n, AddCommGroup (E n)] [∀ n, Module R (E n)]
namespace GlobalTheory.CompanionTheory.PerfRetract
theorem _root_.solution (d : ∀ n, E n →ₗ[R] E (n + 1))
    (C : CochainComplex (ModuleCat.{0} R) ℕ) (inc : ∀ n, C.X n →ₗ[R] E n)
    (r : ∀ n, E n →ₗ[R] C.X n) (hri : ∀ p, r p ∘ₗ inc p = LinearMap.id)
    (hinc : ∀ p, inc (p + 1) ∘ₗ (C.d p (p + 1)).hom = d p ∘ₗ inc p)
    (hr : ∀ p, r (p + 1) ∘ₗ d p = (C.d p (p + 1)).hom ∘ₗ r p)
    (hf0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfs : ∀ n, Module.Finite R (LinearMap.ker (d (n + 1)) ⧸
      (LinearMap.range (d n)).comap (LinearMap.ker (d (n + 1))).subtype)) (p : ℕ) :
    Module.Finite R (C.homology p) := by
  have hsurj := cyclesMap_surjective d C inc r hri hinc hr
  cases p with
  | zero =>
    refine finite_homology_of_surjective C 0 0 1 (by simp) (by simp) (LinearMap.ker (d 0))
      (Submodule.mkQ _ ∘ₗ cyclesMap d C r hr 0) ?_
    exact (Submodule.mkQ_surjective _).comp (hsurj 0)
  | succ p =>
    have := hfs p
    refine finite_homology_of_surjective C p (p + 1) (p + 1 + 1) (by simp) (by simp)
      (LinearMap.ker (d (p + 1)) ⧸
        (LinearMap.range (d p)).comap (LinearMap.ker (d (p + 1))).subtype)
      (Submodule.mapQ ((LinearMap.range (d p)).comap (LinearMap.ker (d (p + 1))).subtype)
        ((LinearMap.range (C.d p (p + 1)).hom).comap
          (LinearMap.ker (C.d (p + 1) (p + 1 + 1)).hom).subtype)
        (cyclesMap d C r hr (p + 1)) ?_) ?_
    · rintro x ⟨y, hy⟩
      refine ⟨r p y, ?_⟩
      have h1 := LinearMap.congr_fun (hr p) y
      simp only [LinearMap.comp_apply] at h1
      rw [← h1, hy]
      rfl
    · intro y
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
      obtain ⟨x, rfl⟩ := hsurj (p + 1) y
      exact ⟨Submodule.Quotient.mk x, rfl⟩
end GlobalTheory.CompanionTheory.PerfRetract
