-- Prove2me | solution 1 for ModularCurve.FullLevel.residue_mem_qExpFunctionFieldC_gamma0_and_surj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/c85b3c88-f16c-58ad-8aaa-476bf5effb38

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_exists_gaussFracForm_mem_laurentBaseChange_qExpFunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_residue_mem_qExpFunctionFieldC_gamma0_and_surj

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_residue_mem_qExpFunctionFieldC_gamma0_and_surj.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_residue_mem_qExpFunctionFieldC_gamma0_and_surj.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC qExpFunctionFieldC_mono coeffMap coeffMap_single algebraMap_laurentSeries_eq_single laurentBaseChange exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC exists_gaussFracForm_mem_laurentBaseChange_qExpFunctionFieldC"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "levelH fieldBar"
namespace ResE0
p2m_open "ModularCurve.FullLevel ModularCurve"

section Res

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))

@[reducible] def instAlgResE : Algebra (ResidueField A) (qExpFunctionFieldC (ResidueField A) Γ') := inferInstance
@[reducible] def instAlgLF : Algebra (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) :=
  inferInstance
@[reducible] def instAlgResLaurent : Algebra (ResidueField A) (LaurentSeries (ResidueField A)) := inferInstance
attribute [local instance] instAlgResE instAlgLF instAlgResLaurent

variable (R : RegularProlongation A (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))
    (qExpFunctionFieldC (ResidueField A) Γ'))

local notation "L" => AlgebraicClosure ℚ
local notation "F" => laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)
local notation "E" => qExpFunctionFieldC (ResidueField A) Γ'

private theorem residue_mul_eq_of_fracForm
    (hpin : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ F),
        ∃ hOy : (⟨coeffMap A.subtype y, hy⟩ : F) ∈ R.integers,
          ((R.residue ⟨_, hOy⟩ : E) : LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y)
    (f : F) (hf : f ∈ R.integers) (c : L) (x y : LaurentSeries A)
    (hx : coeffMap (IsLocalRing.residue A) x ≠ 0)
    (hxF : coeffMap A.subtype x ∈ F) (hyF : coeffMap A.subtype y ∈ F)
    (hfrac : (f : LaurentSeries L) * coeffMap A.subtype y = algebraMap L (LaurentSeries L) c * coeffMap A.subtype x) :
    ∃ hc : c ∈ A, ((R.residue ⟨f, hf⟩ : E) : LaurentSeries (ResidueField A)) * coeffMap (IsLocalRing.residue A) y =
      algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (IsLocalRing.residue A ⟨c, hc⟩) *
        coeffMap (IsLocalRing.residue A) x := by
  obtain ⟨hxO, hxres⟩ := hpin x hxF
  obtain ⟨hyO, hyres⟩ := hpin y hyF

  have hxunit : IsUnit (⟨⟨coeffMap A.subtype x, hxF⟩, hxO⟩ : R.integers) := by
    apply R.isUnit_of_residue_ne_zero
    intro h0
    apply hx
    rw [← hxres, h0]; rfl
  obtain ⟨u, hu⟩ := hxunit
  have hcF : (algebraMap L F c : LaurentSeries L) = algebraMap L (LaurentSeries L) c := rfl
  have hid : f * ⟨coeffMap A.subtype y, hyF⟩ = algebraMap L F c * ⟨coeffMap A.subtype x, hxF⟩ := by
    apply Subtype.ext
    show (f : LaurentSeries L) * coeffMap A.subtype y = (algebraMap L F c : LaurentSeries L) * coeffMap A.subtype x
    rw [hcF, hfrac]
  have hinv : (⟨coeffMap A.subtype x, hxF⟩ : F) * (((u⁻¹ : (R.integers)ˣ) : R.integers) : F) = 1 := by
    have h2 := congrArg (fun z : R.integers => (z : F)) u.mul_inv
    rw [hu] at h2
    simpa using h2
  have hgO : algebraMap L F c ∈ R.integers := by
    have h1 : algebraMap L F c = f * ⟨coeffMap A.subtype y, hyF⟩ * (((u⁻¹ : (R.integers)ˣ) : R.integers) : F) := by
      rw [hid, mul_assoc, hinv, mul_one]
    rw [h1]
    exact R.integers.mul_mem _ _ (R.integers.mul_mem _ _ hf hyO) ((u⁻¹ : (R.integers)ˣ) : R.integers).2
  have hc : c ∈ A := (R.algebraMap_mem_iff c).mp hgO
  refine ⟨hc, ?_⟩
  have hidO : (⟨f, hf⟩ : R.integers) * ⟨⟨coeffMap A.subtype y, hyF⟩, hyO⟩ =
      ⟨algebraMap L F ((⟨c, hc⟩ : A) : L), (R.algebraMap_mem_iff _).mpr hc⟩ * ⟨⟨coeffMap A.subtype x, hxF⟩, hxO⟩ :=
    Subtype.ext hid
  have hres := congrArg R.residue hidO
  rw [map_mul, map_mul, R.residue_algebraMap ⟨c, hc⟩] at hres
  have hres' := congrArg (fun z : E => (z : LaurentSeries (ResidueField A))) hres
  simp only [MulMemClass.coe_mul] at hres'
  rw [hxres, hyres] at hres'
  rw [hres']
  rfl

end Res

section Incl

private theorem gamma0_le_of_dvd {N N' : ℕ} (h : N' ∣ N) : Gamma0 N ≤ Gamma0 N' := by
  intro γ hγ
  rw [Gamma0_mem] at hγ ⊢
  have h1 := congrArg (ZMod.castHom h (ZMod N')) hγ
  rwa [map_intCast, map_zero] at h1

private theorem laurentBaseChange_mono {F₀ F₀' : IntermediateField ℚ (LaurentSeries ℚ)} (h : F₀ ≤ F₀') :
    laurentBaseChange (AlgebraicClosure ℚ) F₀ ≤ laurentBaseChange (AlgebraicClosure ℚ) F₀' := by
  change IntermediateField.adjoin _ _ ≤ IntermediateField.adjoin _ _
  exact IntermediateField.adjoin.mono _ _ _ (Set.image_mono h)

private theorem levelZero_le_fieldBar (q : ℕ) (M' : ℕ) :
    laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) ≤ fieldBar q M' := by
  apply laurentBaseChange_mono
  apply qExpFunctionFieldC_mono ℚ
  exact (CohCarrier.GammaH_le_Gamma0 _).trans (gamma0_le_of_dvd ⟨q ^ 2, by ring⟩)

private theorem T_mem_gamma0 (N : ℕ) : ModularGroup.T ∈ Gamma0 N := by
  rw [Gamma0_mem]; simp [ModularGroup.T]

private theorem coeffMap_subtype_C (A : ValuationSubring (AlgebraicClosure ℚ)) (a : A) :
    coeffMap A.subtype (HahnSeries.C a) = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ) := by
  rw [HahnSeries.C_apply, coeffMap_single, algebraMap_laurentSeries_eq_single]; rfl

private theorem coeffMap_residue_C (A : ValuationSubring (AlgebraicClosure ℚ)) (a : A) :
    coeffMap (IsLocalRing.residue A) (HahnSeries.C a) =
      algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (IsLocalRing.residue A a) := by
  rw [HahnSeries.C_apply, coeffMap_single, algebraMap_laurentSeries_eq_single]

end Incl

end ModularCurve.FullLevel.ResE0

attribute [local instance] ModularCurve.FullLevel.ResE0.instAlgResE ModularCurve.FullLevel.ResE0.instAlgLF
  ModularCurve.FullLevel.ResE0.instAlgResLaurent

open ModularCurve.FullLevel.ResE0 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (A : ValuationSubring (AlgebraicClosure ℚ))
    (R : RegularProlongation A (fieldBar q M')
      (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))))
    (hA : A.LiesOverPrime q)
    (hR : ∀ f : fieldBar q M', f ∈ R.integers ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hpin : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ fieldBar q M'),
        ∃ hOy : (⟨coeffMap A.subtype y, hy⟩ : fieldBar q M') ∈ R.integers,
          ((R.residue ⟨_, hOy⟩ : qExpFunctionFieldC (ResidueField A)
              (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) =
            coeffMap (IsLocalRing.residue A) y) :
    (∀ (f : fieldBar q M') (hf : f ∈ R.integers), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈
        laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) →
      ((R.residue ⟨f, hf⟩ : qExpFunctionFieldC (ResidueField A)
          (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) ∈
        qExpFunctionFieldC (ResidueField A) (Gamma0 M')) ∧
    (∀ e ∈ qExpFunctionFieldC (ResidueField A) (Gamma0 M'),
      ∃ (f : fieldBar q M') (hf : f ∈ R.integers), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈
        laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) ∧
        ((R.residue ⟨f, hf⟩ : qExpFunctionFieldC (ResidueField A)
            (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) = e) := by

  have hex : ∃ R₀ : RegularProlongation A (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')))
      (qExpFunctionFieldC (ResidueField A) (Gamma0 M')),
      (∀ f : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')), f ∈ R₀.integers ↔
        ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
          (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x) ∧
      ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈
          laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))),
        ∃ hO : (⟨coeffMap A.subtype y, hy⟩ : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))) ∈
            R₀.integers,
          ((R₀.residue ⟨_, hO⟩ : qExpFunctionFieldC (ResidueField A) (Gamma0 M')) :
              LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y :=
    ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
      (AlgebraicClosure ℚ) A (Gamma0 M') (T_mem_gamma0 M')
  obtain ⟨R₀, hR₀, hpin₀⟩ := hex
  have hle := levelZero_le_fieldBar q M'
  refine ⟨?_, ?_⟩
  ·
    intro f hf hK
    by_cases hf0 : f = 0
    · subst hf0
      have : (⟨(0 : fieldBar q M'), hf⟩ : R.integers) = 0 := rfl
      rw [this, map_zero]
      exact zero_mem _
    have hf0' : (⟨(f : LaurentSeries (AlgebraicClosure ℚ)), hK⟩ :
        laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))) ≠ 0 := by
      intro h; apply hf0; ext1; simpa using congrArg Subtype.val h
    obtain ⟨c, x, y, hc0, hx, hy, hxK, hyK, hfrac⟩ :=
      ModularCurve.exists_gaussFracForm_mem_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ) A
        (Gamma0 M') (T_mem_gamma0 M') _ hf0'
    obtain ⟨hc, heq⟩ := residue_mul_eq_of_fracForm A (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) R hpin f hf c x y hx (hle hxK) (hle hyK) hfrac

    obtain ⟨hx0, hxres0⟩ := hpin₀ x hxK
    obtain ⟨hy0, hyres0⟩ := hpin₀ y hyK
    have hxE : coeffMap (IsLocalRing.residue A) x ∈ qExpFunctionFieldC (ResidueField A) (Gamma0 M') := by
      rw [← hxres0]; exact SetLike.coe_mem _
    have hyE : coeffMap (IsLocalRing.residue A) y ∈ qExpFunctionFieldC (ResidueField A) (Gamma0 M') := by
      rw [← hyres0]; exact SetLike.coe_mem _
    have hcE : algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (IsLocalRing.residue A ⟨c, hc⟩) ∈
        qExpFunctionFieldC (ResidueField A) (Gamma0 M') := IntermediateField.algebraMap_mem _ _
    have hsolve : ((R.residue ⟨f, hf⟩ : qExpFunctionFieldC (ResidueField A)
          (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) =
        algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (IsLocalRing.residue A ⟨c, hc⟩) *
          coeffMap (IsLocalRing.residue A) x / coeffMap (IsLocalRing.residue A) y :=
      eq_div_of_mul_eq hy heq
    rw [hsolve]
    exact div_mem (mul_mem hcE hxE) hyE
  ·
    intro e he
    by_cases he0 : e = 0
    · refine ⟨0, zero_mem _, zero_mem _, ?_⟩
      have : (⟨(0 : fieldBar q M'), zero_mem _⟩ : R.integers) = 0 := rfl
      rw [this, map_zero, he0]; rfl
    obtain ⟨g₀, hg₀⟩ := R₀.residue_surjective ⟨e, he⟩
    have hg0 : (g₀ : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))) ≠ 0 := by
      intro h
      apply he0
      have h1 : g₀ = 0 := Subtype.ext h
      rw [h1, map_zero] at hg₀
      exact (congrArg Subtype.val hg₀).symm
    obtain ⟨c, x, y, hc0, hx, hy, hxK, hyK, hfrac⟩ :=
      ModularCurve.exists_gaussFracForm_mem_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ) A
        (Gamma0 M') (T_mem_gamma0 M') _ hg0

    obtain ⟨hc, heq0⟩ := residue_mul_eq_of_fracForm A (Gamma0 M') (Gamma0 M') R₀ hpin₀ _ g₀.2 c x y hx hxK hyK hfrac
    have heq0' : e * coeffMap (IsLocalRing.residue A) y =
        algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (IsLocalRing.residue A ⟨c, hc⟩) *
          coeffMap (IsLocalRing.residue A) x := by
      rw [← heq0]
      congr 1
      have : (⟨(g₀ : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))), g₀.2⟩ :
          R₀.integers) = g₀ := rfl
      rw [this, hg₀]

    set f : fieldBar q M' := ⟨((g₀ : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))) :
        LaurentSeries (AlgebraicClosure ℚ)), hle (SetLike.coe_mem _)⟩ with hfdef
    have hfO : f ∈ R.integers := by
      rw [hR]
      refine ⟨HahnSeries.C (⟨c, hc⟩ : A) * x, y, hy, ?_⟩
      rw [map_mul, coeffMap_subtype_C]
      exact hfrac
    have hres1 := residue_mul_eq_of_fracForm A (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))
      (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) R hpin f hfO c x y hx (hle hxK) (hle hyK) hfrac
    obtain ⟨hc', hfin⟩ := hres1
    have hgoal : ((R.residue ⟨f, hfO⟩ : qExpFunctionFieldC (ResidueField A)
          (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) = e :=
      mul_right_cancel₀ hy (hfin.trans heq0'.symm)
    exact ⟨f, hfO, SetLike.coe_mem _, hgoal⟩

end
end S_ModularCurve_FullLevel_residue_mem_qExpFunctionFieldC_gamma0_and_surj
end P2MW
export P2MW.S_ModularCurve_FullLevel_residue_mem_qExpFunctionFieldC_gamma0_and_surj (solution)
