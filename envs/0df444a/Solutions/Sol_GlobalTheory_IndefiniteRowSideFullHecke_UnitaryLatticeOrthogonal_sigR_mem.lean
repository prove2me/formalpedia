-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.sigR_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:17.14464+00:00
-- url     : https://prove2.me/submissions/05f0f9b2-fc20-4b10-b06d-ef83a4f7d0b6

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_UnitaryLatticeOrthogonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {F E} (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
  (v : HeightOneSpectrum (𝓞 F))
end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
section Basic₂
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
open scoped TensorProduct in
open NumberField IsDedekindDomain in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) in
private lemma involution_apply_eq_tensorProductMap_restrictScalars (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v) :
    _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ a =
      ((Algebra.TensorProduct.map (AlgHom.id (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) σ).restrictScalars
        (v.adicCompletionIntegers F)) a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR; simp
  | add x y hx hy => simp [map_add, hx, hy]
end Basic₂
end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
open scoped TensorProduct
open NumberField IsDedekindDomain
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
theorem _root_.solution {a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v}
    (ha : a ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v) :
    _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ a ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v := by
  rw [involution_apply_eq_tensorProductMap_restrictScalars]
  exact IsIntegral.map _ ha
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
