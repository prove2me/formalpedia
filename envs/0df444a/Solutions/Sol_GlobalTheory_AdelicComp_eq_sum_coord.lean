-- Prove2me | solution 1 for GlobalTheory.AdelicComp.eq_sum_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:55:30.38631+00:00
-- url     : https://prove2.me/submissions/534fe3ab-0d30-4cde-8d17-e26e55c6e07b

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
theorem _root_.solution {K V M : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup M] [Module K M]
    {ι : Type} [Fintype ι] (b : Module.Basis ι K V) (z : V ⊗[K] M) :
    z = ∑ i, b i ⊗ₜ[K] TensorProduct.lid K M ((b.coord i).rTensor M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x a =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, ← TensorProduct.smul_tmul,
      ← TensorProduct.sum_tmul, Module.Basis.coord_apply, Module.Basis.sum_repr]
  | add x y hx hy =>
    simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
    rw [← hx, ← hy]
end GlobalTheory.AdelicComp
