-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.WD.lpChar_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:05:44.070577+00:00
-- url     : https://prove2.me/submissions/b3058d1a-c3b8-4bf4-b99e-2d30e6b76252

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsEquivOfMapEq
import Theorems.Thm_GlobalTheory_WeilDeligne_Unram_mk_eq_diag
import Theorems.Thm_GlobalTheory_WeilDeligne_Unram_diag_frob_basisFun
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_unr_lpChar
import Theorems.Thm_GlobalTheory_WeilDeligne_WDRep_unr_diag
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpChar_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_unr_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpChar_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.unr_mk



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
open GlobalTheory.WeilDeligne.WD
open Unram
namespace GlobalTheory.WeilDeligne.WD
theorem _root_.solution {ι κ : Type*} [Finite ι] [Finite κ] (c : ι → ℂˣ) (d : κ → ℂˣ) :
    lpChar (mk (WDRep.diag h c)) (mk (WDRep.diag h d)) =
      mk (WDRep.diag h fun p : ι × κ => c p.1 * d p.2) := by
  classical
  have hu := unr_lpChar _ _ ((unr_mk _).mpr (WDRep.unr_diag (h := h) c))
    ((unr_mk _).mpr (WDRep.unr_diag (h := h) d))
  rw [lpChar_mk] at hu ⊢
  refine mk_eq_diag ((unr_mk _).mp hu) ((Pi.basisFun ℂ ι).tensorProduct (Pi.basisFun ℂ κ)) _ ?_
  rintro ⟨i, k⟩
  rw [Basis.tensorProduct_apply, WDRep.tensor_ρ, TensorProduct.map_tmul, diag_frob_basisFun,
    diag_frob_basisFun, TensorProduct.smul_tmul_smul, Units.val_mul]
end GlobalTheory.WeilDeligne.WD
