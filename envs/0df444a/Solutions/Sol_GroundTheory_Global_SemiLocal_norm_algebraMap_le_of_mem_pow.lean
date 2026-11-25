-- Prove2me | solution 1 for GroundTheory.Global.SemiLocal.norm_algebraMap_le_of_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:07:59.869631+00:00
-- url     : https://prove2.me/submissions/370acf3b-7cab-43d2-b570-3da1516cd07f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Approximation

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
open IsDedekindDomain NumberField WithZeroMulInt WithZero Topology Filter
noncomputable section
open GroundTheory.Global.SemiLocal
variable {L : Type*} [Field L] [NumberField L]
namespace GroundTheory.Global.SemiLocal
theorem _root_.solution (w : HeightOneSpectrum (𝓞 L)) (a : 𝓞 L) (n : ℕ)
    (ha : a ∈ w.asIdeal ^ n) :
    ‖algebraMap (𝓞 L) (w.adicCompletion L) a‖ ≤
      ((toNNReal (HeightOneSpectrum.absNorm_ne_zero w) (exp (-1 : ℤ)) : ℝ)) ^ n := by
  rw [IsScalarTower.algebraMap_apply (𝓞 L) L (w.adicCompletion L),
    HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply, ← FinitePlace.embedding_apply, FinitePlace.norm_embedding_int, ← NNReal.coe_pow,
    NNReal.coe_le_coe, ← map_pow]
  apply (toNNReal_strictMono (HeightOneSpectrum.one_lt_absNorm_nnreal w)).monotone
  rw [← exp_nsmul, smul_neg, nsmul_one]
  exact (w.intValuation_le_pow_iff_mem a n).2 ha
end GroundTheory.Global.SemiLocal
