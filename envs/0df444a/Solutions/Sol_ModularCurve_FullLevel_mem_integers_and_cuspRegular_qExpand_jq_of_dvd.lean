-- Prove2me | solution 1 for ModularCurve.FullLevel.mem_integers_and_cuspRegular_qExpand_jq_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/371a2c57-a83e-58ec-ba8c-7c81617db6d2

import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Theorems.Thm_AlgebraicCurve_Place_ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_ModularCurve_ModuliPointMap
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_mem_integers_and_cuspRegular_qExpand_jq_of_dvd
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups Classical

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

section JQDaux
open ModularCurve

noncomputable def Jbar (M' : ℕ) [NeZero M'] (n : ℕ) [NeZero n] (hn : n ∣ M') : ↥(modularFunctionFieldBar M') :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ n ModularCurve.jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.jqd_mem_full M' hn)⟩

theorem Jbar_coe (M' : ℕ) [NeZero M'] (n : ℕ) [NeZero n] (hn : n ∣ M') :
    ((Jbar M' n hn : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ n ModularCurve.jq) := rfl

theorem ringHom_int_poly_ext {S : Type*} [CommRing S] (f g : Polynomial ℤ →+* S) (h : f Polynomial.X = g Polynomial.X) : f = g := by
  apply Polynomial.ringHom_ext
  · intro a
    exact RingHom.congr_fun (RingHom.ext_int (f.comp Polynomial.C) (g.comp Polynomial.C)) a
  · exact h

theorem isIntegral_Jbar_mul (M' : ℕ) [NeZero M'] (ℓ m : ℕ) [NeZero m] [Fact ℓ.Prime] [NeZero (ℓ * m)]
    (hm : m ∣ M') (hml : ℓ * m ∣ M') :
    IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ) ({Jbar M' m hm} : Set ↥(modularFunctionFieldBar M')))
      (Jbar M' (ℓ * m) hml) := by
  classical
  obtain ⟨data, -⟩ := ModularCurve.exists_modularPolynomialData_evalSymm ℓ
  set R := Algebra.adjoin (AlgebraicClosure ℚ) ({Jbar M' m hm} : Set ↥(modularFunctionFieldBar M')) with hR
  let x : ↥R := ⟨Jbar M' m hm, Algebra.self_mem_adjoin_singleton (AlgebraicClosure ℚ) _⟩
  let g : Polynomial ℤ →+* ↥R := (Polynomial.aeval (R := ℤ) x).toRingHom
  refine ⟨data.Φ.map g, data.monic.map g, ?_⟩

  have hinj : Function.Injective ((modularFunctionFieldBar M').val : ↥(modularFunctionFieldBar M') →ₐ[(AlgebraicClosure ℚ)] LaurentSeries (AlgebraicClosure ℚ)) :=
    fun a b h => Subtype.ext h
  apply hinj
  rw [map_zero, Polynomial.eval₂_map]
  show (modularFunctionFieldBar M').val.toRingHom (Polynomial.eval₂ _ _ _) = 0
  rw [Polynomial.hom_eval₂]

  set hmap : LaurentSeries ℚ →+* LaurentSeries (AlgebraicClosure ℚ) := (coeffEmb (AlgebraicClosure ℚ)).comp (ModularCurve.qExpand ℚ m) with hhmap
  have hcomp : ((modularFunctionFieldBar M').val.toRingHom.comp ((algebraMap ↥R ↥(modularFunctionFieldBar M')).comp g)) =
      hmap.comp ModularCurve.evalAtJ := by
    apply ringHom_int_poly_ext
    simp only [RingHom.coe_comp, Function.comp_apply, hhmap]
    rw [ModularCurve.evalAtJ_X]
    show ((algebraMap ↥R ↥(modularFunctionFieldBar M') (g Polynomial.X) : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) = _
    have : g Polynomial.X = x := by simp [g]
    rw [this]
    rfl
  have qExpand_congr : ∀ (a b : ℕ) [NeZero a] [NeZero b], a = b → ModularCurve.qExpand ℚ a = ModularCurve.qExpand ℚ b := by
    intro a b _ _ h; subst h; rfl
  haveI : NeZero (m * ℓ) := ⟨by rw [Nat.mul_comm]; exact NeZero.ne (ℓ * m)⟩
  have hval : ((modularFunctionFieldBar M').val.toRingHom (Jbar M' (ℓ * m) hml)) = hmap (ModularCurve.jqN ℓ) := by
    show coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ (ℓ * m) ModularCurve.jq) = coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ m (ModularCurve.qExpand ℚ ℓ ModularCurve.jq))
    rw [ModularCurve.qExpand_qExpand, qExpand_congr (ℓ * m) (m * ℓ) (Nat.mul_comm ℓ m)]
  rw [hval, hcomp, ← Polynomial.hom_eval₂, data.eval_eq_zero, map_zero]

end JQDaux

theorem solution
    (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (d : ℕ) [NeZero d] (hd : d ∣ M') :
    (⟨coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ d ModularCurve.jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.jqd_mem_full M' hd)⟩ :
        ↥(modularFunctionFieldBar M')) ∈ R₀.integers ∧
    (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
      0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
      0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ d ModularCurve.jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.jqd_mem_full M' hd)⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))) := by
  classical
  refine ⟨?_, ?_⟩
  ·
    set y : LaurentSeries ↥A := ModularCurve.qExpand ↥A d (ModularCurve.jqModC ↥A) with hy
    have hcoe : coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ d ModularCurve.jq) := by
      rw [hy, ModularCurve.coeffMap_qExpand]
      have h1 : coeffMap A.subtype (ModularCurve.jqModC ↥A) = ModularCurve.jqModC (AlgebraicClosure ℚ) :=
        ModularCurve.map_jqModC A.subtype
      have h2 : coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ d ModularCurve.jq) =
          ModularCurve.qExpand (AlgebraicClosure ℚ) d (ModularCurve.jqModC (AlgebraicClosure ℚ)) := by
        show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (ModularCurve.qExpand ℚ d ModularCurve.jq) = _
        rw [ModularCurve.coeffMap_qExpand]
        congr 1
        exact ModularCurve.map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))
      rw [h1, h2]
    have hymem : coeffMap A.subtype y ∈ modularFunctionFieldBar M' := by
      rw [hcoe]; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.jqd_mem_full M' hd)
    obtain ⟨h, -⟩ := hR₀ y hymem
    have heq : (⟨coeffMap A.subtype y, hymem⟩ : ↥(modularFunctionFieldBar M')) =
        ⟨coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ d ModularCurve.jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.jqd_mem_full M' hd)⟩ :=
      Subtype.ext hcoe
    rw [heq] at h
    exact h
  ·
    intro P hP
    suffices key : ∀ (n : ℕ) (hn0 : n ≠ 0) (hn : n ∣ M'),
        0 ≤ P.ord (@Jbar M' _ n ⟨hn0⟩ hn : ↥(modularFunctionFieldBar M')) by
      exact key d (NeZero.ne d) hd
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn0 hn
      by_cases h1 : n = 1
      · subst h1
        have hJ1 : (@Jbar M' _ 1 ⟨hn0⟩ hn : ↥(modularFunctionFieldBar M')) =
            ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ := by
          apply Subtype.ext
          show coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ 1 ModularCurve.jq) = coeffEmb (AlgebraicClosure ℚ) jq
          rw [ModularCurve.qExpand_one_apply]
        rw [hJ1]
        exact hP
      · obtain ⟨ℓ, hℓp, hℓn⟩ := Nat.exists_prime_and_dvd h1
        obtain ⟨m, rfl⟩ := hℓn
        have hm0 : m ≠ 0 := by rintro rfl; exact hn0 (by simp)
        haveI : NeZero m := ⟨hm0⟩
        haveI : Fact ℓ.Prime := ⟨hℓp⟩
        haveI : NeZero (ℓ * m) := ⟨hn0⟩
        have hmM : m ∣ M' := dvd_trans (dvd_mul_left m ℓ) hn
        have hm_lt : m < ℓ * m := lt_mul_left (Nat.pos_of_ne_zero hm0) hℓp.one_lt
        have ihm : 0 ≤ P.ord (Jbar M' m hmM : ↥(modularFunctionFieldBar M')) := ih m hm_lt hm0 hmM
        have hint := isIntegral_Jbar_mul M' ℓ m hmM hn
        exact AlgebraicCurve.Place.ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg P hint ihm

end S_ModularCurve_FullLevel_mem_integers_and_cuspRegular_qExpand_jq_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_mem_integers_and_cuspRegular_qExpand_jq_of_dvd (solution)
