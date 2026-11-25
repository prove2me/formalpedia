-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfRetract.exists_finite_projective_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:49:49.724678+00:00
-- url     : https://prove2.me/submissions/ac9bb1bb-86a2-4b68-b0a9-efa341afe1f5

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HomotopyProjectorComplexBounded
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfRetract_finite_homology_of_retract
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfRetract_exists_model_of_complex_retract
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
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
theorem _root_.solution : ∀ {R : Type} [CommRing R] [IsNoetherianRing R] (E : ℕ → Type) [∀ n, AddCommGroup (E n)]
    [∀ n, Module R (E n)] [∀ n, Module.Flat R (E n)] (d : ∀ n, E n →ₗ[R] E (n + 1))
    (_ : ∀ n, d (n + 1) ∘ₗ d n = 0) (e : ∀ n, E n →ₗ[R] E n) (h : ∀ n, E (n + 1) →ₗ[R] E n) (B : ℕ)
    (_ : ∀ n, e n ∘ₗ e n = e n) (_ : ∀ n, e (n + 1) ∘ₗ d n = d n ∘ₗ e n)
    (_ : e 0 = LinearMap.id + h 0 ∘ₗ d 0)
    (_ : ∀ n, e (n + 1) = LinearMap.id + d n ∘ₗ h n + h (n + 1) ∘ₗ d (n + 1))
    (_ : ∀ n, B < n → e n = 0)
    (_ : Module.Finite R (LinearMap.ker (d 0)))
    (_ : ∀ n, Module.Finite R (LinearMap.ker (d (n + 1)) ⧸
      (LinearMap.range (d n)).comap (LinearMap.ker (d (n + 1))).subtype)),
    ∃ (Q : CochainComplex (ModuleCat.{0} R) ℕ) (ψ : ∀ n, Q.X n →ₗ[R] E n),
      (∀ n, Module.Finite R (Q.X n)) ∧ (∀ n, Module.Projective R (Q.X n)) ∧
      (∀ n, ψ (n + 1) ∘ₗ (Q.d n (n + 1)).hom = d n ∘ₗ ψ n) ∧
      ∀ M : ModuleCat.{0} R,
        QIsoAt (0 : R →ₗ[R] M ⊗[R] Q.X 0) ((Q.d 0 1).hom.lTensor M) (0 : R →ₗ[R] M ⊗[R] E 0)
          ((d 0).lTensor M) ((ψ 0).lTensor M) ∧
        ∀ n, QIsoAt ((Q.d n (n + 1)).hom.lTensor M) ((Q.d (n + 1) (n + 2)).hom.lTensor M)
          ((d n).lTensor M) ((d (n + 1)).lTensor M) ((ψ (n + 1)).lTensor M) := by
  intro R _ _ E _ _ _ d hdd e h B hee hed he0 hes hB hf0 hfs
  have hrange : ∀ n (x : E n), x ∈ LinearMap.range (e n) → e n x = x := by
    rintro n _ ⟨y, rfl⟩
    exact LinearMap.congr_fun (hee n) y
  let dN : ∀ n, LinearMap.range (e n) →ₗ[R] LinearMap.range (e (n + 1)) := fun n =>
    (d n ∘ₗ (LinearMap.range (e n)).subtype).codRestrict _ (by
      rintro ⟨_, y, rfl⟩
      exact ⟨d n y, LinearMap.congr_fun (hed n) y⟩)
  have hdN : ∀ n (x : LinearMap.range (e n)), ((dN n x : LinearMap.range (e (n + 1))) : E (n + 1)) =
      d n x := fun _ _ => rfl
  let C : CochainComplex (ModuleCat.{0} R) ℕ :=
    CochainComplex.of (fun n => ModuleCat.of R (LinearMap.range (e n)))
      (fun n => ModuleCat.ofHom (dN n)) (fun n => by
        refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
        exact LinearMap.congr_fun (hdd n) x.1)
  have hCd : ∀ p, C.d p (p + 1) = ModuleCat.ofHom (dN p) := fun p => by
    simp [C, CochainComplex.of_d]
  let inc : ∀ n, C.X n →ₗ[R] E n := fun n => (LinearMap.range (e n)).subtype
  let r : ∀ n, E n →ₗ[R] C.X n := fun n => (e n).rangeRestrict
  have hri : ∀ p, r p ∘ₗ inc p = LinearMap.id := fun p => by
    refine LinearMap.ext fun x => Subtype.ext ?_
    exact hrange p _ x.2
  have hinc : ∀ p, inc (p + 1) ∘ₗ (C.d p (p + 1)).hom = d p ∘ₗ inc p := fun p => by
    rw [hCd]
    rfl
  have hr : ∀ p, r (p + 1) ∘ₗ d p = (C.d p (p + 1)).hom ∘ₗ r p := fun p => by
    rw [hCd]
    refine LinearMap.ext fun x => Subtype.ext ?_
    exact LinearMap.congr_fun (hed p) x
  have hflat : ∀ p, Module.Flat R (C.X p) := fun p =>
    Module.Flat.of_retract (inc p) (r p) (hri p)
  refine exists_model_of_complex_retract d e h B he0 hes C inc r hri hinc hr (fun _ => rfl)
    (fun p hp => ?_) hflat (finite_homology_of_retract d C inc r hri hinc hr hf0 hfs)
  refine ModuleCat.isZero_iff_subsingleton.2 ?_
  change Subsingleton (LinearMap.range (e p))
  rw [hB p hp, LinearMap.range_zero]
  infer_instance
end GlobalTheory.CompanionTheory.PerfRetract
