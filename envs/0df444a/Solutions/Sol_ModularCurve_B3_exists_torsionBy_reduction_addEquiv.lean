-- Prove2me | solution 1 for ModularCurve.B3.exists_torsionBy_reduction_addEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/45f040e2-7cb2-5205-af9d-61e92078d3e5

import Definitions.Def_ModularCurve_HahnSpecialise
import Theorems.Thm_ModularCurve_HahnSpecialise_specialise_bijOn_torsion
import Mathlib.Algebra.Module.Torsion.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_B3_exists_torsionBy_reduction_addEquiv
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

noncomputable section

open ModularCurve ModularCurve.B3 ModularCurve.HahnSpecialise
open ModularCurve.TatePoint (Qbar H CycSubH)
open IsLocalRing WeierstrassCurve
open scoped Classical

namespace Sol3a

variable (W : WeierstrassCurve H) (hW : IntegralCoeffs W) (hΔ' : (specialFibre W).Δ ≠ 0)

theorem nsmul_of_mem {M : Type*} [AddCommGroup M] {N : ℕ} {x : M}
    (hx : x ∈ Submodule.torsionBy ℤ M (N : ℤ)) : N • x = 0 := by
  rw [Submodule.mem_torsionBy_iff] at hx; rwa [natCast_zsmul] at hx

theorem mem_of_nsmul {M : Type*} [AddCommGroup M] {N : ℕ} {x : M}
    (hx : N • x = 0) : x ∈ Submodule.torsionBy ℤ M (N : ℤ) := by
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul]; exact hx

def torsHom (N : ℕ) :
    Submodule.torsionBy ℤ W.toAffine.Point (N : ℤ) →+
      Submodule.torsionBy ℤ (specialFibre W).toAffine.Point (N : ℤ) where
  toFun P := ⟨specialise W hW hΔ' P, by
    have hP := P.2
    rw [Submodule.mem_torsionBy_iff] at hP ⊢
    rw [← map_zsmul, hP, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' P Q := Subtype.ext (map_add _ _ _)

theorem torsHom_bijective (N : ℕ) [NeZero N] : Function.Bijective (torsHom W hW hΔ' N) := by
  have hb := ModularCurve.HahnSpecialise.specialise_bijOn_torsion W hW hΔ' N
  refine ⟨fun P Q h => Subtype.ext (hb.2.1 (nsmul_of_mem P.2) (nsmul_of_mem Q.2)
    (congrArg Subtype.val h)), fun Q => ?_⟩
  obtain ⟨P, hP, hPQ⟩ := hb.2.2 (nsmul_of_mem Q.2)
  exact ⟨⟨P, mem_of_nsmul hP⟩, Subtype.ext hPQ⟩

end Sol3a

theorem solution (W : WeierstrassCurve H)
    [W.IsElliptic] (hW : IntegralCoeffs W) (hΔ : W.Δ.orderTop = 0)
    [(specialFibre W).IsElliptic] (p : ℕ) [Fact p.Prime] :
    ∃ e : Submodule.torsionBy ℤ W.toAffine.Point (p : ℤ) ≃+
        Submodule.torsionBy ℤ (specialFibre W).toAffine.Point (p : ℤ),
      ∀ (P : Submodule.torsionBy ℤ W.toAffine.Point (p : ℤ)) (x y : H)
        (h : W.toAffine.Nonsingular x y),
        (P : W.toAffine.Point) = WeierstrassCurve.Affine.Point.some x y h →
          ∃ h₀ : (specialFibre W).toAffine.Nonsingular (x.coeff 0) (y.coeff 0),
            ((e P : Submodule.torsionBy ℤ (specialFibre W).toAffine.Point (p : ℤ)) :
                (specialFibre W).toAffine.Point) =
              WeierstrassCurve.Affine.Point.some (x.coeff 0) (y.coeff 0) h₀ := by
  have hΔ' : (specialFibre W).Δ ≠ 0 := (specialFibre_Δ_ne_zero_iff W hW).mpr hΔ
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine ⟨AddEquiv.ofBijective (Sol3a.torsHom W hW hΔ' p) (Sol3a.torsHom_bijective W hW hΔ' p), ?_⟩
  intro P x y h hP

  have hPt : p • (P : W.toAffine.Point) = 0 := Sol3a.nsmul_of_mem P.2
  have h' : ((liftModel W hW).map valuationSubringH.subtype).toAffine.Nonsingular x y := by
    rw [liftModel_map_subtype]; exact h
  have hx : x ∈ valuationSubringH := by
    refine X_mem_of_nsmul_eq_zero' (liftModel W hW) (natCast_residueField_ne_zero (NeZero.ne p)) h' ?_
    have : (P : W.toAffine.Point) = (Affine.Point.some x y h' :
        ((liftModel W hW).map valuationSubringH.subtype).toAffine.Point) := hP
    rw [← this]; exact hPt
  refine ⟨nonsingular_specialFibre_coeff_zero W hW hΔ' h hx, ?_⟩
  show specialise W hW hΔ' (P : W.toAffine.Point) = _
  rw [hP, specialise_some_of_nonneg W hW hΔ' h hx]

end
end S_ModularCurve_B3_exists_torsionBy_reduction_addEquiv
end P2MW
export P2MW.S_ModularCurve_B3_exists_torsionBy_reduction_addEquiv (solution)
