-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.FrobSemisimple.minpoly_eval_zero_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:05:46.12381+00:00
-- url     : https://prove2.me/submissions/d3b7c217-43cf-4675-bbcc-ec0edd73972a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPowEqPowOfWeilDegreeEqSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_WeilGroupIsSemisimpleOfSemisimpleFrob

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.FrobSemisimple
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
namespace GlobalTheory.WeilDeligne.FrobSemisimple
theorem _root_.solution {f : End ℂ V} (hf : IsUnit f) : (minpoly ℂ f).eval 0 ≠ 0 := by
  intro h0
  have h1 : f.HasEigenvalue 0 := End.hasEigenvalue_iff_isRoot.mpr h0
  exact spectrum.zero_notMem ℂ hf (End.hasEigenvalue_iff_mem_spectrum.mp h1)
end GlobalTheory.WeilDeligne.FrobSemisimple
