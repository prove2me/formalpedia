-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfRetract.qIsoAt_of_retract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:29:04.417629+00:00
-- url     : https://prove2.me/submissions/75b86c9c-c931-48aa-bf0c-369c5d45fa37

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HomotopyProjectorComplexBounded
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
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
variable {R : Type} [CommRing R] {K C E : ℕ → Type}
  [∀ p, AddCommGroup (K p)] [∀ p, AddCommGroup (C p)] [∀ p, AddCommGroup (E p)]
  [∀ p, Module R (K p)] [∀ p, Module R (C p)] [∀ p, Module R (E p)]
namespace GlobalTheory.CompanionTheory.PerfRetract
theorem _root_.solution
    (dK : ∀ p, K p →ₗ[R] K (p + 1)) (dC : ∀ p, C p →ₗ[R] C (p + 1))
    (dE : ∀ p, E p →ₗ[R] E (p + 1))
    (φ : ∀ p, K p →ₗ[R] C p) (inc : ∀ p, C p →ₗ[R] E p) (r : ∀ p, E p →ₗ[R] C p)
    (h : ∀ p, E (p + 1) →ₗ[R] E p)
    (hc : ConeExact (K := K) (C := C) (fun p => dK p) (fun p => dC p) (fun p => φ p))
    (hri : ∀ p, r p ∘ₗ inc p = LinearMap.id)
    (hinc : ∀ p, inc (p + 1) ∘ₗ dC p = dE p ∘ₗ inc p)
    (hr : ∀ p, r (p + 1) ∘ₗ dE p = dC p ∘ₗ r p)
    (h0 : inc 0 ∘ₗ r 0 = LinearMap.id + h 0 ∘ₗ dE 0)
    (hs : ∀ p, inc (p + 1) ∘ₗ r (p + 1) =
      LinearMap.id + dE p ∘ₗ h p + h (p + 1) ∘ₗ dE (p + 1)) :
    QIsoAt (0 : R →ₗ[R] K 0) (dK 0) (0 : R →ₗ[R] E 0) (dE 0) (inc 0 ∘ₗ φ 0) ∧
    ∀ n, QIsoAt (dK n) (dK (n + 1)) (dE n) (dE (n + 1)) (inc (n + 1) ∘ₗ φ (n + 1)) := by
  have hri' : ∀ p x, r p (inc p x) = x := fun p x => LinearMap.congr_fun (hri p) x
  have hinc' : ∀ p x, inc (p + 1) (dC p x) = dE p (inc p x) := fun p x => LinearMap.congr_fun (hinc p) x
  have hr' : ∀ p x, r (p + 1) (dE p x) = dC p (r p x) := fun p x => LinearMap.congr_fun (hr p) x
  have h0' : ∀ x, inc 0 (r 0 x) = x + h 0 (dE 0 x) := fun x => LinearMap.congr_fun h0 x
  have hs' : ∀ p x, inc (p + 1) (r (p + 1) x) = x + dE p (h p x) + h (p + 1) (dE (p + 1) x) :=
    fun p x => LinearMap.congr_fun (hs p) x
  refine ⟨⟨?_, ?_⟩, fun n => ⟨?_, ?_⟩⟩
  · rintro x hx ⟨y, hy⟩
    have h1 : inc 0 (φ 0 x) = 0 := by simpa using hy.symm
    have h2 : φ 0 x = 0 := by rw [← hri' 0 (φ 0 x), h1, map_zero]
    exact ⟨0, by simpa using (hc.inj x h2 hx).symm⟩
  · intro z hz
    obtain ⟨x, hx, hx'⟩ := hc.zero (r 0 z) 0
      (by change dC 0 (r 0 z) = φ 1 0; rw [← hr', hz]; simp) (by simp)
    have hx2 : φ 0 x = r 0 z := hx
    refine ⟨x, 0, hx', ?_⟩
    simp [hx2, h0', hz]
  · rintro x hx ⟨y, hy⟩
    have hy' : dE n y = inc (n + 1) (φ (n + 1) x) := hy
    have h1 : dC n (r n y) = φ (n + 1) x := by rw [← hr', hy', hri']
    cases n with
    | zero =>
      obtain ⟨w, -, hw⟩ := hc.zero (r 0 y) x h1 hx
      exact ⟨w, hw⟩
    | succ m =>
      obtain ⟨-, w, -, hw⟩ := hc.succ m (r (m + 1) y) x h1 hx
      exact ⟨w, hw⟩
  · intro z hz
    obtain ⟨c, k, hck, hk⟩ := hc.succ n (r (n + 1) z) 0
      (by change dC (n + 1) (r (n + 1) z) = φ (n + 2) 0; rw [← hr', hz]; simp) (by simp)
    have hck' : dC n c + φ (n + 1) k = r (n + 1) z := hck
    refine ⟨k, h n z - inc n c, hk, ?_⟩
    have h3 : φ (n + 1) k = r (n + 1) z - dC n c := eq_sub_of_add_eq' hck'
    simp only [LinearMap.comp_apply, h3, map_sub, hs', hinc', hz, map_zero, add_zero]
    abel
end GlobalTheory.CompanionTheory.PerfRetract
