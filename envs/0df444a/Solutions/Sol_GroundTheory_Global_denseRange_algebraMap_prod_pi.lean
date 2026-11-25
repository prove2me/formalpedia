-- Prove2me | solution 1 for GroundTheory.Global.denseRange_algebraMap_prod_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:26:38.813507+00:00
-- url     : https://prove2.me/submissions/d4b24e33-5cfa-48fd-bc4d-24caf0099e4e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_WeakApprox
import Theorems.Thm_GroundTheory_Global_placeAbv_isNontrivial
import Theorems.Thm_GroundTheory_Global_placeAbv_pairwise_not_isEquiv
import Theorems.Thm_GroundTheory_Global_isometry_algebraMap_adicCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField
variable {K : Type*} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))
namespace GroundTheory.Global
theorem _root_.solution :
    DenseRange (fun x : K ↦ ((fun v : S ↦ algebraMap K (v.1.adicCompletion K) x),
      (fun w : T ↦ algebraMap K w.1.Completion x))) := by
  classical
  let φ : ∀ v : S, WithAbs (placeAbv S T (.inl v)) → v.1.adicCompletion K := fun v ↦
    (algebraMap K (v.1.adicCompletion K)).comp
      (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v.1)).toRingHom
  let ψ : ∀ w : T, WithAbs (placeAbv S T (.inr w)) → w.1.Completion := fun w y ↦
    ((show WithAbs w.1.1 from y) : w.1.Completion)
  have hφc : ∀ v, Continuous (φ v) := fun v ↦ (isometry_algebraMap_adicCompletion v.1).continuous
  have hφd : ∀ v, DenseRange (φ v) := by
    intro v
    have h := HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) (K := K) v.1
    unfold DenseRange at h ⊢
    convert h using 1
    show Set.range (⇑(algebraMap K (v.1.adicCompletion K)) ∘
      ⇑(WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v.1))) = _
    exact (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v.1)).surjective.range_comp _
  have hψc : ∀ w, Continuous (ψ w) := fun w ↦ InfinitePlace.Completion.continuous_coe w.1
  have hψd : ∀ w, DenseRange (ψ w) := fun w ↦ InfinitePlace.Completion.denseRange_coe w.1
  let e := Homeomorph.sumPiEquivProdPi S T (fun i ↦ WithAbs (placeAbv S T i))
  have hc : Continuous (Prod.map (Pi.map φ) (Pi.map ψ) ∘ e) :=
    ((continuous_pi fun v ↦ (hφc v).comp (continuous_apply v)).prodMap
      (continuous_pi fun w ↦ (hψc w).comp (continuous_apply w))).comp e.continuous
  have hg : DenseRange (Prod.map (Pi.map φ) (Pi.map ψ) ∘ e) :=
    ((DenseRange.piMap hφd).prodMap (DenseRange.piMap hψd)).comp e.surjective.denseRange
      ((continuous_pi fun v ↦ (hφc v).comp (continuous_apply v)).prodMap
        (continuous_pi fun w ↦ (hψc w).comp (continuous_apply w)))
  have hd := AbsoluteValue.denseRange_algebraMap_pi (placeAbv_isNontrivial S T)
    (placeAbv_pairwise_not_isEquiv S T)
  convert hg.comp hd hc using 1
  funext x
  rfl
end GroundTheory.Global
