-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfRetract.exists_model_of_complex_retract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:43:13.297932+00:00
-- url     : https://prove2.me/submissions/fae2bedf-d4ee-4967-8e23-b2dd8ce7d7ed

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HomotopyProjectorComplexBounded
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfRetract_qIsoAt_of_retract
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_cochain_comm_apply
import Theorems.Thm_GlobalTheory_coneExact_lTensor_of_quasiIso
import Theorems.Thm_GlobalTheory_exists_finite_projective_complex_quasiIso
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
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.PerfRetract
theorem _root_.solution [IsNoetherianRing R] {E : ℕ → Type}
    [∀ n, AddCommGroup (E n)] [∀ n, Module R (E n)] (d : ∀ n, E n →ₗ[R] E (n + 1))
    (e : ∀ n, E n →ₗ[R] E n) (h : ∀ n, E (n + 1) →ₗ[R] E n) (B : ℕ)
    (he0 : e 0 = LinearMap.id + h 0 ∘ₗ d 0)
    (hes : ∀ n, e (n + 1) = LinearMap.id + d n ∘ₗ h n + h (n + 1) ∘ₗ d (n + 1))
    (C : CochainComplex (ModuleCat.{0} R) ℕ) (inc : ∀ n, C.X n →ₗ[R] E n)
    (r : ∀ n, E n →ₗ[R] C.X n) (hri : ∀ p, r p ∘ₗ inc p = LinearMap.id)
    (hinc : ∀ p, inc (p + 1) ∘ₗ (C.d p (p + 1)).hom = d p ∘ₗ inc p)
    (hr : ∀ p, r (p + 1) ∘ₗ d p = (C.d p (p + 1)).hom ∘ₗ r p)
    (hir : ∀ p, inc p ∘ₗ r p = e p)
    (hB : ∀ p, B < p → Limits.IsZero (C.X p)) (hflat : ∀ p, Module.Flat R (C.X p))
    (hfin : ∀ p, Module.Finite R (C.homology p)) :
    ∃ (Q : CochainComplex (ModuleCat.{0} R) ℕ) (ψ : ∀ n, Q.X n →ₗ[R] E n),
      (∀ n, Module.Finite R (Q.X n)) ∧ (∀ n, Module.Projective R (Q.X n)) ∧
      (∀ n, ψ (n + 1) ∘ₗ (Q.d n (n + 1)).hom = d n ∘ₗ ψ n) ∧
      ∀ M : ModuleCat.{0} R,
        QIsoAt (0 : R →ₗ[R] M ⊗[R] Q.X 0) ((Q.d 0 1).hom.lTensor M) (0 : R →ₗ[R] M ⊗[R] E 0)
          ((d 0).lTensor M) ((ψ 0).lTensor M) ∧
        ∀ n, QIsoAt ((Q.d n (n + 1)).hom.lTensor M) ((Q.d (n + 1) (n + 2)).hom.lTensor M)
          ((d n).lTensor M) ((d (n + 1)).lTensor M) ((ψ (n + 1)).lTensor M) := by
  obtain ⟨Q, φ, hQ0, hQfin, -, hQproj, hq, -, -⟩ :=
    GlobalTheory.exists_finite_projective_complex_quasiIso.{0, 0} C B hB hflat hfin
  have hQflat : ∀ p, Module.Flat R (Q.X p) := fun p => by
    have := hQproj p
    infer_instance
  refine ⟨Q, fun n => inc n ∘ₗ (φ.f n).hom, hQfin, hQproj, fun n => ?_, fun M => ?_⟩
  · refine LinearMap.ext fun x => ?_
    have h1 := LinearMap.congr_fun (hinc n) ((φ.f n).hom x)
    have h2 := GlobalTheory.cochain_comm_apply φ n (n + 1) x
    simp only [LinearMap.comp_apply] at h1 ⊢
    rw [← h1, h2]
  · have hc := GlobalTheory.coneExact_lTensor_of_quasiIso φ hQflat hflat B hQ0 hB M
    have key := qIsoAt_of_retract (R := R) (K := fun p => M ⊗[R] Q.X p)
      (C := fun p => M ⊗[R] C.X p) (E := fun p => M ⊗[R] E p)
      (fun p => (Q.d p (p + 1)).hom.lTensor M) (fun p => (C.d p (p + 1)).hom.lTensor M)
      (fun p => (d p).lTensor M) (fun p => (φ.f p).hom.lTensor M)
      (fun p => (inc p).lTensor M) (fun p => (r p).lTensor M) (fun p => (h p).lTensor M) hc
      (fun p => by rw [← LinearMap.lTensor_comp, hri, LinearMap.lTensor_id])
      (fun p => by rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, hinc])
      (fun p => by rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, hr])
      (by
        rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, hir, he0, LinearMap.lTensor_add,
          LinearMap.lTensor_id])
      (fun p => by
        rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, hir, hes,
          LinearMap.lTensor_add, LinearMap.lTensor_add, LinearMap.lTensor_id])
    simp only [LinearMap.lTensor_comp]
    exact key
end GlobalTheory.CompanionTheory.PerfRetract
