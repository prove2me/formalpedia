-- Prove2me | solution 1 for ModularCurve.forall_aeval_mem_iff_forall_aeval_qExpand_mem_of_valuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/989acb56-3e22-5406-9701-84a83ca0b58f

import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Theorems.Thm_ValuationSubring_forall_aeval_mem_and_inv_mem_of_isRoot_of_isRoot
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_forall_aeval_mem_iff_forall_aeval_qExpand_mem_of_valuationSubring
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in

theorem solution
    (q : ℕ) [Fact q.Prime]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)
    (j' : ↥K) (hj' : ((j' : LaurentSeries L)) = ModularCurve.qExpand L q ((j : ↥K) : LaurentSeries L))
    (V : ValuationSubring ↥K)
    (hA : ∀ a : A, algebraMap L ↥K (algebraMap A L a) ∈ V)
    (hm : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap L ↥K (algebraMap A L a) ∈ V.nonunits) :
    (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j (P.map (algebraMap A L)) ∈ V ∧ (Polynomial.aeval j (P.map (algebraMap A L)))⁻¹ ∈ V) ↔
      (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j' (P.map (algebraMap A L)) ∈ V ∧ (Polynomial.aeval j' (P.map (algebraMap A L)))⁻¹ ∈ V) := by
  haveI hqne : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨data, hsymm⟩ := ModularCurve.exists_modularPolynomialData_evalSymm q

  have hΦ1 : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) ModularCurve.jq).toRingHom (ModularCurve.qExpand ℚ q ModularCurve.jq) = 0 :=
    data.eval_eq_zero
  have hΦ2 : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (ModularCurve.qExpand ℚ q ModularCurve.jq)).toRingHom ModularCurve.jq = 0 := by
    rw [← hsymm]; exact hΦ1

  have hj'e : ((j' : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ q ModularCurve.jq) := by
    rw [hj', hj, ModularCurve.coeffEmb_qExpand]
  have key : ∀ (x y : LaurentSeries ℚ) (X Y : ↥K), ((X : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L x →
      ((Y : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L y →
      data.Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y = 0 →
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ↥K) X)).IsRoot Y := by
    intro x y X Y hX hY h0
    rw [Polynomial.IsRoot, Polynomial.eval_map]
    apply Subtype.val_injective
    show (algebraMap ↥K (LaurentSeries L)) (data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ↥K) X) Y) =
      ((0 : ↥K) : LaurentSeries L)
    rw [Polynomial.hom_eval₂, ZeroMemClass.coe_zero]
    have h1 := congrArg (ModularCurve.coeffEmb L) h0
    rw [Polynomial.hom_eval₂, map_zero] at h1
    have hhom : (algebraMap ↥K (LaurentSeries L)).comp (Polynomial.eval₂RingHom (Int.castRingHom ↥K) X) =
        (ModularCurve.coeffEmb L : LaurentSeries ℚ →+* LaurentSeries L).comp (Polynomial.aeval (R := ℤ) x).toRingHom := by
      refine Polynomial.ringHom_ext (fun a => by simp) ?_
      show (algebraMap ↥K (LaurentSeries L)) (Polynomial.eval₂RingHom (Int.castRingHom ↥K) X Polynomial.X) =
        ModularCurve.coeffEmb L ((Polynomial.aeval (R := ℤ) x).toRingHom Polynomial.X)
      rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X]
      exact hX
    rw [hhom, show (algebraMap ↥K (LaurentSeries L)) Y = ModularCurve.coeffEmb L y from hY]
    exact h1
  have hR1 := key _ _ j j' hj hj'e hΦ1
  have hR2 := key _ _ j' j hj'e hj hΦ2

  letI algAK : Algebra A ↥K := ((algebraMap L ↥K).comp (algebraMap A L)).toAlgebra
  haveI : IsScalarTower A L ↥K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hev : ∀ (x : ↥K) (P : Polynomial A), Polynomial.aeval x (P.map (algebraMap A L)) = Polynomial.aeval x P :=
    fun x P => Polynomial.aeval_map_algebraMap L x P
  have hA' : ∀ a : A, algebraMap A ↥K a ∈ V := hA
  have hm' : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V.nonunits := hm
  constructor
  · intro h P hP
    rw [hev]
    exact ValuationSubring.forall_aeval_mem_and_inv_mem_of_isRoot_of_isRoot A ↥K V hA' hm' j j'
      data.Φ data.monic hR1 data.Φ data.monic hR2 (fun P hP => by rw [← hev]; exact h P hP) P hP
  · intro h P hP
    rw [hev]
    exact ValuationSubring.forall_aeval_mem_and_inv_mem_of_isRoot_of_isRoot A ↥K V hA' hm' j' j
      data.Φ data.monic hR2 data.Φ data.monic hR1 (fun P hP => by rw [← hev]; exact h P hP) P hP

end S_ModularCurve_forall_aeval_mem_iff_forall_aeval_qExpand_mem_of_valuationSubring
end P2MW
export P2MW.S_ModularCurve_forall_aeval_mem_iff_forall_aeval_qExpand_mem_of_valuationSubring (solution)
