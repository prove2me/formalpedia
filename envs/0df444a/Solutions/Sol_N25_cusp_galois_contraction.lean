-- Prove2me | solution 1 for N25.cusp_galois_contraction
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:32:31.7576+00:00
-- url     : https://prove2.me/submissions/c935cb7a-2c70-4ad7-8569-223c87419460

import Mathlib
import Definitions.Def_N25_Endgame
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option autoImplicit false

noncomputable section

open ModularCurve AlgebraicCurve

open scoped Pointwise

namespace N25

open Endgame

/-- Arithmetic conjugates have exactly the same contracted closed place over the rationals. -/
theorem _root_.solution (σ : Gal) (P : GPlace) :
    (arithmeticGalois FQ σ • P).toValuationSubring.comap emb25.toRingHom =
      P.toValuationSubring.comap emb25.toRingHom := by
  have hfix (τ : Gal) (x : FQ) : arithmeticGalois FQ τ • emb25 x = emb25 x := by
    apply Subtype.ext
    rw [coe_arithmeticGalois_smul, coe_emb25, coeffMap_coeffEmb]
  apply SetLike.ext
  intro x
  change emb25 x ∈ (arithmeticGalois FQ σ • P).toValuationSubring ↔
    emb25 x ∈ P.toValuationSubring
  rw [SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rw [← map_inv, hfix]

end N25
