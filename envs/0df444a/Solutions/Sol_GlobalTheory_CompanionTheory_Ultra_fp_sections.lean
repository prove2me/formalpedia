-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.fp_sections
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:50:22.388511+00:00
-- url     : https://prove2.me/submissions/9164b05f-2b99-4004-8a91-a48016049375

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsProperSpreadsOut
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_fromSpec_comp

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
omit [CommRing R]
namespace GlobalTheory.CompanionTheory.Ultra
theorem _root_.solution [LocallyOfFinitePresentation f₀] [Algebra.FiniteType ℤ R₀] (W : X.affineOpens) :
    Algebra.FinitePresentation ℤ Γ(X, W.1) := by
  have h1 : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (baseHom f₀ W))) := by
    rw [← fromSpec_comp]; infer_instance
  have h2 : (baseHom f₀ W).FinitePresentation :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).1 h1
  have h3 : Algebra.FinitePresentation ℤ R₀ := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  have h4 := h2.comp ((RingHom.finitePresentation_algebraMap).2 h3)
  rw [← RingHom.finitePresentation_algebraMap]
  convert h4
  exact RingHom.ext_int _ _
end GlobalTheory.CompanionTheory.Ultra
