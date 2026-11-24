-- Prove2me | solution 1 for GlobalTheory.QCoh.isLocalizing_restrict_fromSpec_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:17:50.127733+00:00
-- url     : https://prove2.me/submissions/4ab7ec0c-bdd2-4c5e-b641-6ab89f8ba9c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_res_self_ring
import Theorems.Thm_GlobalTheory_QCoh_isLocalizedModule_resBasicOpen_iff
import Theorems.Thm_GlobalTheory_QCoh_restrict_fromSpec_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.QCoh.resLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
variable (hU : IsAffineOpen U)
namespace GlobalTheory.QCoh
theorem _root_.solution :
    IsLocalizing (modulesSpecToSheaf.obj (F.restrict hU.fromSpec)) ↔
      ∀ f : Γ(X, U), IsLocalizedModule.Away f (resBasicOpen F f) := by
  refine forall_congr' fun f ↦ ?_
  rw [isLocalizedModule_resBasicOpen_iff]
  have key : ∀ (U' V' : X.Opens) (hU' : U' ≤ U) (hV' : V' ≤ U'), U' = U → V' = X.basicOpen f →
      (((∀ s : Γ(F, V'), ∃ (n : ℕ) (t : Γ(F, U')),
        X.presheaf.map (homOfLE (hV'.trans hU')).op (f ^ n) • s =
          F.presheaf.map (homOfLE hV').op t) ∧
      (∀ t : Γ(F, U'), F.presheaf.map (homOfLE hV').op t = 0 →
        ∃ n : ℕ, X.presheaf.map (homOfLE hU').op (f ^ n) • t = 0)) ↔
      ((∀ s : Γ(F, X.basicOpen f), ∃ (n : ℕ) (t : Γ(F, U)),
        X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n • s =
          F.presheaf.map (homOfLE (X.basicOpen_le f)).op t) ∧
      (∀ t : Γ(F, U), F.presheaf.map (homOfLE (X.basicOpen_le f)).op t = 0 →
        ∃ n : ℕ, f ^ n • t = 0))) := by
    intro U' V' hU' hV' e e'
    subst e e'
    simp only [res_self_ring, map_pow]
  rw [← key (hU.fromSpec ''ᵁ ⊤) (hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen f)
    (fromSpec_image_le hU _) (hU.fromSpec.image_mono le_top)
    (by rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec])
    (hU.fromSpec_image_basicOpen f)]
  let φ := ((modulesSpecToSheaf.obj (F.restrict hU.fromSpec)).obj.map
    (PrimeSpectrum.basicOpen f).leTop.op).hom
  constructor
  · intro h
    have h : IsLocalizedModule.Away f φ := h
    refine ⟨fun s ↦ ?_, fun t ht ↦ ?_⟩
    · obtain ⟨n, t, ht⟩ := IsLocalizedModule.Away.surj φ f s
      exact ⟨n, t, (restrict_fromSpec_smul F hU _ (f ^ n) s).symm.trans ht⟩
    · obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (f := φ) f
        (x := t) (y := 0) (by rw [map_zero]; exact ht)
      rw [smul_zero] at hn
      exact ⟨n, (restrict_fromSpec_smul F hU _ (f ^ n) t).symm.trans hn⟩
  · rintro ⟨h₁, h₂⟩
    refine IsLocalizedModule.Away.mk_of_addCommGroup (f := φ) ?_ (fun s ↦ ?_) (fun t ht ↦ ?_)
    · exact Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen f le_rfl
    · obtain ⟨n, t, ht⟩ := h₁ s
      exact ⟨n, t, (restrict_fromSpec_smul F hU _ (f ^ n) s).trans ht⟩
    · obtain ⟨n, hn⟩ := h₂ t ht
      exact ⟨n, (restrict_fromSpec_smul F hU _ (f ^ n) t).trans hn⟩
end GlobalTheory.QCoh
