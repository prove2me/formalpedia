-- Prove2me | solution 1 for GlobalTheory.CayleyCapelli.list_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:39:51.256045+00:00
-- url     : https://prove2.me/submissions/822bb654-bc5a-4056-a2df-768a25f163ea

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdIccMulFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds
noncomputable section
open GlobalTheory GlobalTheory.CayleyCapelli
open MvPolynomial Formalism.IncomingBounds ReciprocityTheory.PGsh GlobalTheory.DetPowPairing
variable {σ : Type} {C : Type} [Field C]
namespace GlobalTheory.CayleyCapelli
theorem _root_.solution {ι τ : Type} (g : σ → τ) (hg : Function.Injective g) (f : ι → σ) (l : List ι)
    (Q : MvPolynomial σ C) :
    ((l.map fun j => ((pderiv (g (f j)) : Derivation C _ _) :
        MvPolynomial τ C →ₗ[C] MvPolynomial τ C)).prod : Module.End C (MvPolynomial τ C))
        (rename g Q) =
      rename g (((l.map fun j => ((pderiv (f j) : Derivation C _ _) :
        MvPolynomial σ C →ₗ[C] MvPolynomial σ C)).prod : Module.End C (MvPolynomial σ C)) Q) := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih]
    exact pderiv_rename hg _ _
end GlobalTheory.CayleyCapelli
