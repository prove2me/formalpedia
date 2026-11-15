-- Prove2me | solution 1 for MazurP23.det_galoisRep_eq_cycloExp
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-14T23:10:24.468771+00:00
-- url     : https://prove2.me/submissions/60faa910-9313-41b1-a808-aa59f752154c

import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_WeierstrassCurve_apply_eq_pow_det_galoisRep_of_pow_eq_one
import Theorems.Thm_ExtCitation_map_primitiveRoot_eq_pow_cycloExp
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
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
        (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ)
      = ((ExtCitation.cycloExp p σ : ℕ) : ZMod p) := by
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
  have h2 : σ ξ = ξ ^ ExtCitation.cycloExp p σ :=
    ExtCitation.map_primitiveRoot_eq_pow_cycloExp σ hξ
  have hord : IsOfFinOrder ξ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.pos, hξ.pow_eq_one⟩
  have h4 : (LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
      (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ)).val
      ≡ ExtCitation.cycloExp p σ [MOD p] := by
    have h5 := hord.pow_eq_pow_iff_modEq.mp (h1.symm.trans h2)
    rwa [← hξ.eq_orderOf] at h5
  calc LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
        (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ)
      = ((LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
          (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ)).val : ZMod p) := by
        rw [ZMod.natCast_val, ZMod.cast_id]
    _ = ((ExtCitation.cycloExp p σ : ℕ) : ZMod p) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr h4

end MazurP23
