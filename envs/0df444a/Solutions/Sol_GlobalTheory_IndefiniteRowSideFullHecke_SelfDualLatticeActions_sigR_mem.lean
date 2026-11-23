-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.sigR_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:17.150802+00:00
-- url     : https://prove2.me/submissions/f3f9d56d-fe4b-4941-80a4-5a16bf6a8ecd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualLatticeActions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E)
open scoped TensorProduct
open NumberField IsDedekindDomain
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E)
namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions
theorem _root_.solution {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.Ev E v}
    (hz : z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.OEv E v) :
    _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.OEv E v := by
  let φ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.Ev E v →ₐ[_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v] _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.Ev E v :=
    Algebra.TensorProduct.map (AlgHom.id (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) σ
  have h := (hz : IsIntegral (v.adicCompletionIntegers F) z).map
    (φ.restrictScalars (v.adicCompletionIntegers F))
  exact h
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions
end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions
