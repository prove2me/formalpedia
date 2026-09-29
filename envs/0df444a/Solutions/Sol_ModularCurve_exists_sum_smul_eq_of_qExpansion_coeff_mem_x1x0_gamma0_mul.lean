-- Prove2me | solution 1 for ModularCurve.exists_sum_smul_eq_of_qExpansion_coeff_mem_x1x0_gamma0_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/81ee509e-b1f3-5378-a2ca-8a9cc15cbc18

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularCurve_exists_sum_smul_eq_of_isIntegralQExp_gammaH
import Theorems.Thm_PowerSeries_exists_sum_smul_eq_of_forall_coeff_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_sum_smul_eq_of_qExpansion_coeff_mem_x1x0_gamma0_mul
p2m_attr_erase "instance" "TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq"
p2m_attr_erase "simp" "CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

open scoped MatrixGroups ModularForm

namespace GenRoofE107

open UpperHalfPlane CongruenceSubgroup

def castMF {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (h : Γ = Γ') (f : ModularForm Γ k) : ModularForm Γ' k := h ▸ f

@[scoped simp] theorem coe_castMF {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (h : Γ = Γ') (f : ModularForm Γ k) :
    (⇑(castMF h f) : ℍ → ℂ) = ⇑f := by
  subst h; rfl

def H₁ (A ℓ : ℕ) : Subgroup (ZMod (A * ℓ))ˣ := (ZMod.unitsMap (dvd_mul_right A ℓ)).ker

theorem mem_H₁ {A ℓ : ℕ} (u : (ZMod (A * ℓ))ˣ) :
    u ∈ H₁ A ℓ ↔ (ZMod.cast (u : ZMod (A * ℓ)) : ZMod A) = 1 := by
  rw [H₁, MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, Units.val_one]

theorem gamma1_inf_gamma0_mul_eq_gammaH (A ℓ : ℕ) :
    Gamma1 A ⊓ Gamma0 (A * ℓ) = CohCarrier.GammaH (A * ℓ) (H₁ A ℓ) := by
  ext γ
  rw [Subgroup.mem_inf, Gamma1_mem, CohCarrier.mem_GammaH_iff]
  constructor
  · rintro ⟨⟨-, hd, -⟩, hc⟩
    refine ⟨hc, ?_⟩
    rw [mem_H₁, CohCarrier.val_gamma0Units]
    change (ZMod.cast (((γ 1 1 : ℤ) : ZMod (A * ℓ))) : ZMod A) = 1
    rw [ZMod.cast_intCast (dvd_mul_right A ℓ)]
    exact hd
  · rintro ⟨hA0, hH⟩
    rw [mem_H₁, CohCarrier.val_gamma0Units] at hH
    change (ZMod.cast (((γ 1 1 : ℤ) : ZMod (A * ℓ))) : ZMod A) = 1 at hH
    rw [ZMod.cast_intCast (dvd_mul_right A ℓ)] at hH
    have hc : ((A * ℓ : ℕ) : ℤ) ∣ (γ 1 0 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hA0)
    push_cast at hc
    have hcA : ((γ 1 0 : ℤ) : ZMod A) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ((dvd_mul_right _ _).trans hc)
    have h1 : (⟨γ, Gamma0_mem.mpr hcA⟩ : Gamma0 A) ∈ Gamma1' A := by
      rw [Gamma1_mem']
      exact hH
    rw [Gamma1_to_Gamma0_mem] at h1
    exact ⟨h1, hA0⟩

section Split

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {k : ℤ} (h1 : (1 : ℝ) ∈ Γ.strictPeriods)
include h1

theorem qExpansion_coe_smul (c : ℂ) (G : ModularForm Γ k) :
    qExpansion 1 (⇑(c • G) : ℍ → ℂ) = c • qExpansion 1 (⇑G : ℍ → ℂ) := by
  rw [ModularForm.IsGLPos.coe_smul]; exact ModularForm.qExpansion_smul one_pos h1 c G

theorem qExpansion_coe_sum {n : ℕ} (c : Fin n → ℂ) (G : Fin n → ModularForm Γ k) :
    qExpansion 1 (⇑(∑ i, c i • G i) : ℍ → ℂ) = ∑ i, c i • qExpansion 1 (⇑(G i) : ℍ → ℂ) := by
  classical
  have key : ∀ s : Finset (Fin n), qExpansion 1 (⇑(∑ i ∈ s, c i • G i) : ℍ → ℂ) =
      ∑ i ∈ s, c i • qExpansion 1 (⇑(G i) : ℍ → ℂ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty, ModularForm.coe_zero, qExpansion_zero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.coe_add,
        ModularForm.qExpansion_add one_pos h1 (c a • G a) (∑ i ∈ s, c i • G i), ih, qExpansion_coe_smul h1]
  exact key Finset.univ

omit h1 in
theorem coe_sum {n : ℕ} (c : Fin n → ℂ) (G : Fin n → ModularForm Γ k) :
    (⇑(∑ i, c i • G i) : ℍ → ℂ) = ∑ i, c i • (⇑(G i) : ℍ → ℂ) := by
  rw [show (⇑(∑ i, c i • G i) : ℍ → ℂ) = FunLike.coeAddMonoidHom (ModularForm _ k) ℍ ℂ (∑ i, c i • G i) from rfl, map_sum]
  rfl

theorem split (K₀ : IntermediateField ℚ ℂ) (F : ModularForm Γ k)
    (hF : ∀ n : ℕ, (qExpansion 1 (⇑F : ℍ → ℂ)).coeff n ∈ K₀)
    (hspan : ∃ (n : ℕ) (c : Fin n → ℂ) (G : Fin n → ModularForm Γ k) (r : Fin n → PowerSeries ℤ),
      (∀ i, ModularCurve.IsIntegralQExp (G i) (r i)) ∧ (⇑F : ℍ → ℂ) = ∑ i, c i • (⇑(G i) : ℍ → ℂ)) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (G : Fin n → ModularForm Γ k) (r : Fin n → PowerSeries ℤ),
      (∀ i, c i ∈ K₀) ∧ (∀ i, ModularCurve.IsIntegralQExp (G i) (r i)) ∧
      (⇑F : ℍ → ℂ) = ∑ i, c i • (⇑(G i) : ℍ → ℂ) := by
  classical
  obtain ⟨n, c, G, r, hG, hsum⟩ := hspan
  let g : Fin n → PowerSeries ℂ := fun i => (r i).map (Int.castRingHom ℂ)
  have hgq : ∀ i, g i = qExpansion 1 (⇑(G i) : ℍ → ℂ) := fun i => hG i
  have hg : ∀ (i : Fin n) (m : ℕ), (g i).coeff m ∈ K₀.toSubfield := by
    intro i m
    simp only [g, PowerSeries.coeff_map, eq_intCast]
    exact intCast_mem _ _
  have hF' : F = ∑ i, c i • G i := DFunLike.coe_injective (by
    show (⇑F : ℍ → ℂ) = ⇑(∑ i, c i • G i); rw [hsum, coe_sum])
  have hqF : qExpansion 1 (⇑F : ℍ → ℂ) = ∑ i, c i • g i := by
    rw [hF', qExpansion_coe_sum h1]; simp only [hgq]
  have hcoef : ∀ m : ℕ, (∑ i, c i • g i).coeff m ∈ K₀.toSubfield := fun m => by rw [← hqF]; exact hF m
  obtain ⟨c', hc', heq⟩ := PowerSeries.exists_sum_smul_eq_of_forall_coeff_mem K₀.toSubfield g hg c hcoef
  refine ⟨n, c', G, r, fun i => hc' i, hG, ?_⟩
  have hq : qExpansion 1 (⇑(∑ i, c' i • G i) : ℍ → ℂ) = qExpansion 1 (⇑F : ℍ → ℂ) := by
    rw [qExpansion_coe_sum h1, hqF, ← heq]; simp only [hgq]
  have hform : (∑ i, c' i • G i) = F := by
    have h0 : qExpansion 1 (⇑((∑ i, c' i • G i) - F) : ℍ → ℂ) = 0 := by
      rw [ModularForm.coe_sub, ModularForm.qExpansion_sub one_pos h1 (∑ i, c' i • G i) F, hq, sub_self]
    exact sub_eq_zero.mp ((ModularForm.qExpansion_eq_zero_iff one_pos h1 _).mp h0)
  rw [← hform, coe_sum]

end Split

end GenRoofE107
p2m_reactivate "P2MW.S_ModularCurve_exists_sum_smul_eq_of_qExpansion_coeff_mem_x1x0_gamma0_mul.GenRoofE107"

open GenRoofE107 CongruenceSubgroup UpperHalfPlane in
open scoped MatrixGroups ModularForm in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (ℓ : ℕ) [Fact ℓ.Prime] {k : ℤ} (K₀ : IntermediateField ℚ ℂ)
    (F : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * ℓ) : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)) k)
    (hF : ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 (⇑F : UpperHalfPlane → ℂ)).coeff n ∈ K₀) :
    ∃ (n : ℕ) (c : Fin n → ℂ)
      (G : Fin n → ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * ℓ) : Subgroup SL(2, ℤ)) :
        Subgroup (GL (Fin 2) ℝ)) k)
      (r : Fin n → PowerSeries ℤ),
      (∀ i, c i ∈ K₀) ∧ (∀ i, ModularCurve.IsIntegralQExp (G i) (r i)) ∧
      (⇑F : UpperHalfPlane → ℂ) = ∑ i, c i • (⇑(G i) : UpperHalfPlane → ℂ) := by
  classical
  have hp : p.Prime := Fact.out
  have hℓ : ℓ.Prime := Fact.out
  haveI : NeZero (M * p * ℓ) := ⟨mul_ne_zero (mul_ne_zero (NeZero.ne M) hp.ne_zero) hℓ.ne_zero⟩
  have hΓ : Gamma1 (M * p) ⊓ Gamma0 (M * p * ℓ) = CohCarrier.GammaH (M * p * ℓ) (H₁ (M * p) ℓ) :=
    gamma1_inf_gamma0_mul_eq_gammaH (M * p) ℓ
  have hΓ' : ((Gamma1 (M * p) ⊓ Gamma0 (M * p * ℓ) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) =
      ((CohCarrier.GammaH (M * p * ℓ) (H₁ (M * p) ℓ) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := congrArg _ hΓ
  have hT : ModularGroup.T ∈ Gamma1 (M * p) ⊓ Gamma0 (M * p * ℓ) :=
    Subgroup.mem_inf.mpr ⟨by simp [ModularGroup.T], by simp [ModularGroup.T]⟩
  have h1 : (1 : ℝ) ∈ Subgroup.strictPeriods
      ((Gamma1 (M * p) ⊓ Gamma0 (M * p * ℓ) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
    rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
    exact AddSubgroup.mem_zmultiples 1

  let F' : ModularForm ((CohCarrier.GammaH (M * p * ℓ) (H₁ (M * p) ℓ) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k :=
    castMF hΓ' F
  obtain ⟨n, c, G, r, hG, hsum⟩ := ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gammaH (M * p * ℓ) (H₁ (M * p) ℓ) F'
  have hspan : ∃ (n : ℕ) (c : Fin n → ℂ)
      (G : Fin n → ModularForm ((Gamma1 (M * p) ⊓ Gamma0 (M * p * ℓ) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
      (r : Fin n → PowerSeries ℤ),
      (∀ i, ModularCurve.IsIntegralQExp (G i) (r i)) ∧ (⇑F : ℍ → ℂ) = ∑ i, c i • (⇑(G i) : ℍ → ℂ) := by
    refine ⟨n, c, fun i => castMF hΓ'.symm (G i), r, fun i => ?_, ?_⟩
    · simpa only [coe_castMF] using hG i
    · rw [← coe_castMF hΓ' F]
      change (⇑F' : ℍ → ℂ) = _
      rw [hsum]
      simp only [coe_castMF]
  exact GenRoofE107.split h1 K₀ F hF hspan

end S_ModularCurve_exists_sum_smul_eq_of_qExpansion_coeff_mem_x1x0_gamma0_mul
end P2MW
export P2MW.S_ModularCurve_exists_sum_smul_eq_of_qExpansion_coeff_mem_x1x0_gamma0_mul (solution)
