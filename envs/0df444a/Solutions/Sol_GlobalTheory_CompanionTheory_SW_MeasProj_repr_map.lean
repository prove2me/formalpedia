-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.MeasProj.repr_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:57.117959+00:00
-- url     : https://prove2.me/submissions/aeac647b-9ba9-4ed1-8f44-b63c9a4bc133

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjections
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.MeasProj
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E]
  {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]
namespace GlobalTheory.CompanionTheory.SW.MeasProj
theorem _root_.solution {d : ℕ} (b : Module.Basis (Fin d) F E) (f : R →ₐ[F] S) (y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis S b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) y) k =
      f ((Algebra.TensorProduct.basis R b).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy => simp [map_add, hx, hy]
end GlobalTheory.CompanionTheory.SW.MeasProj
