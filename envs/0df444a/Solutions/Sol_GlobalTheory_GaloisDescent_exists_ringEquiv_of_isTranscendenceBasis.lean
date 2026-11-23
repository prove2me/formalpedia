-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.exists_ringEquiv_of_isTranscendenceBasis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:15.452822+00:00
-- url     : https://prove2.me/submissions/fa482ac2-2d07-4511-a9ec-35489730d11c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Cardinal
open GlobalTheory GlobalTheory.GaloisDescent
open MvPolynomial Cardinal
namespace GlobalTheory.GaloisDescent
namespace _root_.GlobalTheory.GaloisDescent
theorem _root_.solution {F F' L L' ι κ : Type*} [Field F] [Field F']
    [Field L] [Field L'] [Algebra F L] [Algebra F' L'] [IsAlgClosed L] [IsAlgClosed L']
    {v : ι → L} {w : κ → L'} (hv : IsTranscendenceBasis F v) (hw : IsTranscendenceBasis F' w)
    (e : MvPolynomial ι F ≃+* MvPolynomial κ F') :
    ∃ σ : L ≃+* L', ∀ p, σ (aeval v p) = aeval w (e p) := by
  letI : Algebra (MvPolynomial ι F) L := (aeval v).toRingHom.toAlgebra
  letI : Algebra (MvPolynomial κ F') L' := (aeval w).toRingHom.toAlgebra
  have : Module.IsTorsionFree (MvPolynomial ι F) L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hv.1
  have : Module.IsTorsionFree (MvPolynomial κ F') L' :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hw.1
  have : IsAlgClosure (MvPolynomial ι F) L := by
    refine ⟨inferInstance, ?_⟩
    have := hv.isAlgebraic
    refine Algebra.IsAlgebraic.ringHom_of_comp_eq hv.1.aevalEquiv.symm (RingHom.id L)
      hv.1.aevalEquiv.symm.injective Function.surjective_id ?_
    ext a
    change aeval v (hv.1.aevalEquiv.symm a) = algebraMap _ L a
    rw [← hv.1.algebraMap_aevalEquiv, AlgEquiv.apply_symm_apply]
  have : IsAlgClosure (MvPolynomial κ F') L' := by
    refine ⟨inferInstance, ?_⟩
    have := hw.isAlgebraic
    refine Algebra.IsAlgebraic.ringHom_of_comp_eq hw.1.aevalEquiv.symm (RingHom.id L')
      hw.1.aevalEquiv.symm.injective Function.surjective_id ?_
    ext a
    change aeval w (hw.1.aevalEquiv.symm a) = algebraMap _ L' a
    rw [← hw.1.algebraMap_aevalEquiv, AlgEquiv.apply_symm_apply]
  exact ⟨IsAlgClosure.equivOfEquiv L L' e, fun p => IsAlgClosure.equivOfEquiv_algebraMap L L' e p⟩
end _root_.GlobalTheory.GaloisDescent
end GlobalTheory.GaloisDescent
