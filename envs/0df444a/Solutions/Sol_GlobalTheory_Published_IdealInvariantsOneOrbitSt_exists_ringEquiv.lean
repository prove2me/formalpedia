-- Prove2me | solution 1 for GlobalTheory.Published.IdealInvariantsOneOrbitSt.exists_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:12:08.507378+00:00
-- url     : https://prove2.me/submissions/deb3946b-962e-4121-b037-8aaa98d29bd7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_ExistsMemIdealInvariants
import Theorems.Thm_GlobalTheory_Published_IdealInvariantsOneOrbitSt_exists_algEquiv
import Theorems.Thm_GlobalTheory_Published_latticeCurve_j_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors IntermediateField
open GlobalTheory GlobalTheory.Published
variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
namespace GlobalTheory.Published
namespace IdealInvariantsOneOrbitSt
theorem _root_.solution (h : IdealInvariantsOneOrbitSt)
    (h2 : Module.finrank ℚ K = 2) (φ : K →+* ℂ) {𝔠 𝔠' : (Ideal (𝓞 K))⁰} {L L' : PeriodPair}
    (hL : (L.lattice : Set ℂ) = (fun x : 𝓞 K => φ x) '' (𝔠 : Ideal (𝓞 K)))
    (hL' : (L'.lattice : Set ℂ) = (fun x : 𝓞 K => φ x) '' (𝔠' : Ideal (𝓞 K))) :
    ∃ s : ℂ ≃+* ℂ, (∀ x : K, s (φ x) = φ x) ∧
      s (1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) =
        1728 * L'.g₂ ^ 3 / (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2) := by
  let _ : Algebra K ℂ := φ.toAlgebra
  have hlat : ∀ (𝔡 : (Ideal (𝓞 K))⁰) (M : PeriodPair),
      (M.lattice : Set ℂ) = (fun x : 𝓞 K => φ x) '' (𝔡 : Ideal (𝓞 K)) →
      IsIdealLattice (Units.mk0 ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
        (FractionalIdeal.coeIdeal_ne_zero.mpr (nonZeroDivisors.coe_ne_zero 𝔡))) M := by
    intro 𝔡 M hM
    unfold IsIdealLattice
    rw [hM]
    ext z
    simp only [Set.mem_image, Units.val_mk0, SetLike.mem_coe, FractionalIdeal.mem_coeIdeal]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨algebraMap (𝓞 K) K x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  obtain ⟨ρ, hρ⟩ := h.exists_algEquiv h2 (hlat 𝔠 L hL) (hlat 𝔠' L' hL')
  refine ⟨ρ.toRingEquiv, fun x => ρ.commutes x, ?_⟩
  rw [← latticeCurve_j_eq, ← latticeCurve_j_eq]
  exact hρ
end IdealInvariantsOneOrbitSt
end GlobalTheory.Published
