-- Prove2me | solution 1 for MazurP23.det_galoisRep_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-14T23:10:25.345695+00:00
-- url     : https://prove2.me/submissions/2aceeeb4-adff-42de-938f-36798ea14722

import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ValuationSubring_IsFrobeniusAt_apply_rootOfUnity_eq_pow
import Theorems.Thm_WeierstrassCurve_apply_eq_pow_det_galoisRep_of_pow_eq_one
import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open CuspForm ModularFormClass UpperHalfPlane

namespace MazurP23

private theorem tw_det_seam (W : WeierstrassCurve ℤ) (p : ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.det ((DistribSMul.toAddMonoidHom (Submodule.torsionBy ℤ
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) σ).toZModLinearMap p)
      = LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
          (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ) := by
  congr 1

private theorem tw_isElliptic (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) :
    (W.map (Int.castRingHom ℚ)).IsElliptic := by
  refine (WeierstrassCurve.isElliptic_iff _).mpr (isUnit_iff_ne_zero.mpr ?_)
  rw [WeierstrassCurve.map_Δ, eq_intCast]
  exact_mod_cast hΔ

theorem _root_.solution (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hΔ : W.Δ ≠ 0)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : A.IsFrobeniusAt σ q) :
    LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
        (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ)
      = ((q : ℕ) : ZMod p) := by
  classical
  have hp : p.Prime := Fact.out
  haveI := tw_isElliptic W hΔ
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpK : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p
  have h1 : σ ξ = ξ ^ (LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
      (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ)).val := by
    have h0 := WeierstrassCurve.apply_eq_pow_det_galoisRep_of_pow_eq_one
      (W.map (Int.castRingHom ℚ)) hp hpK σ ξ hξ.pow_eq_one
    rwa [tw_det_seam] at h0
  have h2 : σ ξ = ξ ^ q :=
    ValuationSubring.IsFrobeniusAt.apply_rootOfUnity_eq_pow hp hq hqp A hA hσ ξ hξ.pow_eq_one
  have hord : IsOfFinOrder ξ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.pos, hξ.pow_eq_one⟩
  have h4 : (LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
      (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ)).val ≡ q [MOD p] := by
    have h5 := hord.pow_eq_pow_iff_modEq.mp (h1.symm.trans h2)
    rwa [← hξ.eq_orderOf] at h5
  calc LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
        (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ)
      = ((LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
          (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ)).val : ZMod p) := by
        rw [ZMod.natCast_val, ZMod.cast_id]
    _ = ((q : ℕ) : ZMod p) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h4

end MazurP23
