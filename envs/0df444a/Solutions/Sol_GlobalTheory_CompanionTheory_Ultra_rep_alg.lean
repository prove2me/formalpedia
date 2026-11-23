-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.rep_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:05.966839+00:00
-- url     : https://prove2.me/submissions/cfc08adc-37f9-4c65-aa42-7d71519e8d2d

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsProperSpreadsOut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ultra
variable {R₀ R : Type} [CommRing R₀] [CommRing R] {X Y : Scheme.{0}}
  (f₀ : X ⟶ Spec (CommRingCat.of R₀))
variable {f₀}
variable (f₀)
variable {ι : Type} (U : Ultrafilter ι) {T V K : ι → Type} [∀ i, CommRing (T i)]
  [∀ i, CommRing (V i)] [∀ i, IsDomain (V i)] [∀ i, ValuationRing (V i)] [∀ i, Field (K i)]
  [∀ i, Algebra (V i) (K i)] [∀ i, IsFractionRing (V i) (K i)]
  (ψ : ∀ i, R₀ →+* T i)
  (a : ∀ i, Spec (CommRingCat.of (K i)) ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom (ψ i))))
  (β : ∀ i, T i →+* V i)
omit [∀ i, ValuationRing (V i)] [∀ i, IsFractionRing (V i) (K i)]
namespace GlobalTheory.CompanionTheory.Ultra
theorem _root_.solution {B : Type} [CommRing B] {h : ∀ i, B → V i} {g : B →+* Ult U V} (r : Rep U h g) :
    Rep U (fun i b => algebraMap (V i) (K i) (h i b))
      ((algebraMap (Ult U V) (Ult U K)).comp g) := by
  refine ⟨?_, fun b => ?_⟩
  · filter_upwards [r.1] with i ⟨p, hp⟩
    exact ⟨(algebraMap (V i) (K i)).comp p, by funext b; simp [← hp]⟩
  · rw [RingHom.comp_apply, r.2, algebraMap_mk]
end GlobalTheory.CompanionTheory.Ultra
