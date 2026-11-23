-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ultra.base_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:58.472834+00:00
-- url     : https://prove2.me/submissions/c2b45371-b867-4b90-876a-47d0af292774

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsProperSpreadsOut
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_spec_comp
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_spec_inj
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_pt_comp

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
namespace GlobalTheory.CompanionTheory.Ultra
theorem _root_.solution {T A : Type} [CommRing T] [CommRing A] (ψ : R₀ →+* T) (W : X.affineOpens)
    (p : Γ(X, W.1) →+* A) (t : T →+* A)
    (l : Spec (CommRingCat.of A) ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom ψ)))
    (h1 : l ≫ pullback.fst _ _ = pt W p)
    (h2 : l ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom t)) :
    p.comp (baseHom f₀ W) = t.comp ψ := by
  apply spec_inj
  rw [← pt_comp, ← h1, Category.assoc, pullback.condition, ← Category.assoc, h2, spec_comp]
end GlobalTheory.CompanionTheory.Ultra
