-- Prove2me | solution 1 for GlobalTheory.AdelicComp.coord_compAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:55:29.613908+00:00
-- url     : https://prove2.me/submissions/ce23f1db-1944-41d2-85dc-9743aafa34dc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EqZeroOfCompAtEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
open GlobalTheory GlobalTheory.AdelicComp
namespace GlobalTheory.AdelicComp
theorem _root_.solution (L : Type) [Field L] [NumberField L] [IsCMField L] {ι : Type} [DecidableEq ι] [Finite ι]
    (b : Module.Basis ι (maximalRealSubfield L) L)
    (w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (i : ι) (z : AL L) :
    TensorProduct.lid (maximalRealSubfield L) _ ((b.coord i).rTensor _ (compAt L w z))
      = evalAt L w (TensorProduct.lid (maximalRealSubfield L) _ ((b.coord i).rTensor _ z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x a =>
    have h : compAt L w (x ⊗ₜ a) = x ⊗ₜ evalAt L w a := rfl
    rw [h]
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]
end GlobalTheory.AdelicComp
