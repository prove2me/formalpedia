-- Prove2me | solution 1 for GlobalTheory.RowLev.PlFrame.ActsAs.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:15:35.860884+00:00
-- url     : https://prove2.me/submissions/552319e6-9bb5-4c1c-bab8-e46f08b7d9d2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowLev
open Formalism.MainNotions.S MeasureTheory NumberField IsDedekindDomain Matrix
open Formalism.UG Formalism.UG.P
open scoped TensorProduct
open Inhab
open GlobalTheory.RowLev.PlFrame
variable {I : AutInst} {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w)
namespace GlobalTheory.RowLev.PlFrame
namespace ActsAs
theorem _root_.solution {x x' : I.Gf} (hx' : x' ∈ I.Kset) {M M' : Matrix (Fin N) (Fin N) (ZMod p)}
    (h : fr.ActsAs x M) (h' : fr.ActsAs x' M') : fr.ActsAs (x * x') (M * M') := by
  intro y hy
  have e : I.fmat (x * x') *ᵥ (y : Fin I.n → _) = I.fmat x *ᵥ (I.fmat x' *ᵥ (y : Fin I.n → _)) := by
    rw [fmat_mul, Matrix.mulVec_mulVec]
  rw [← Matrix.mulVec_mulVec, ← h' y (mulVec_mem hx' y.2), ← h ⟨_, mulVec_mem hx' y.2⟩ (e ▸ hy)]
  exact congrArg fr.c (Subtype.ext e)
end ActsAs
end GlobalTheory.RowLev.PlFrame
