-- Prove2me | solution 1 for N25.Endgame.constantFieldLift25_galois_fixed
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:06.429218+00:00
-- url     : https://prove2.me/submissions/0882df52-5a63-4d85-a60d-0e0b8747d64a

import Definitions.Def_N25_ConstantFieldLift
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option autoImplicit false

open ModularCurve AlgebraicCurve

open scoped Pointwise

namespace N25.Endgame

theorem _root_.solution (P : QPlace) (P' : GPlace)
    (hLift : IsConstantFieldLift25 P P')
    (huniq : ∀ Q' : GPlace, Q'.toValuationSubring.comap emb25.toRingHom =
      P.toValuationSubring → Q' = P') :
    ∀ σ : N25.Gal, arithmeticGalois FQ σ • P' = P' := by
  have hfix (σ : N25.Gal) (f : FQ) : arithmeticGalois FQ σ • emb25 f = emb25 f := by
    apply Subtype.ext
    rw [coe_arithmeticGalois_smul, coe_emb25]
    change coeffMap (σ : Qbar →+* Qbar)
      (coeffMap (algebraMap ℚ Qbar) (f : LaurentSeries ℚ)) =
      coeffMap (algebraMap ℚ Qbar) (f : LaurentSeries ℚ)
    rw [coeffMap_coeffMap, RingHom.ext_rat ((σ : Qbar →+* Qbar).comp (algebraMap ℚ Qbar))
      (algebraMap ℚ Qbar)]
  intro σ
  apply huniq
  ext f
  change emb25 f ∈ (arithmeticGalois FQ σ • P').toValuationSubring ↔
    f ∈ P.toValuationSubring
  rw [SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have hi : (arithmeticGalois FQ σ)⁻¹ • emb25 f = emb25 f := by
    rw [← map_inv]
    exact hfix σ⁻¹ f
  rw [hi]
  change f ∈ P'.toValuationSubring.comap emb25.toRingHom ↔ f ∈ P.toValuationSubring
  rw [hLift.1]

end N25.Endgame
