-- Prove2me | solution 1 for ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/24fa251c-20e4-575e-a399-3a85441704c8

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularCurve_X1
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularCurve_exists_sum_smul_eq_of_isIntegralQExp_gamma1
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_sum_smul_eq_of_isIntegralQExp_gammaH
p2m_attr_erase "instance" "TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq"
p2m_attr_erase "simp" "CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

p2m_open "UpperHalfPlane ModularFormClass ModularCurve~Gamma1_le_GammaH CongruenceSubgroup"
open scoped MatrixGroups ModularForm

namespace IntSpanH

variable (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ)

omit [NeZero N] in

theorem Gamma1_le_GammaH : Gamma1 N ≤ CohCarrier.GammaH N H := by
  intro A hA
  rw [CohCarrier.mem_GammaH_iff]
  have hA' := (Gamma1_mem N A).mp hA
  have h0 : A ∈ Gamma0 N := by rw [Gamma0_mem]; exact hA'.2.2
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units N ⟨A, h0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    show ((A 1 1 : ℤ) : ZMod N) = ((1 : (ZMod N)ˣ) : ZMod N)
    rw [hA'.2.1, Units.val_one]
  rw [this]
  exact one_mem H

omit [NeZero N] in
theorem Gamma1_le_GammaH_GL :
    (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) ≤ (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.map_mono (Gamma1_le_GammaH N H)

scoped instance isFiniteRelIndex :
    (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).IsFiniteRelIndex (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) := by
  refine ⟨?_⟩
  show (Subgroup.map _ (Gamma1 N)).relIndex (Subgroup.map _ (CohCarrier.GammaH N H)) ≠ 0
  rw [Subgroup.relIndex_map_map_of_injective _ _ (Matrix.SpecialLinearGroup.mapGL_injective)]
  intro h0
  have hdvd := Subgroup.relIndex_dvd_index_of_le (Gamma1_le_GammaH N H)
  rw [h0, zero_dvd_iff] at hdvd
  exact Subgroup.FiniteIndex.index_ne_zero hdvd

def restrict1 {k : ℤ} (F : ModularForm (CohCarrier.GammaH N H) k) : ModularForm (Gamma1 N) k where
  toFun := F
  slash_action_eq' γ hγ := SlashInvariantForm.slash_action_eqn F γ (Gamma1_le_GammaH_GL N H hγ)
  holo' := F.holo'
  bdd_at_cusps' hc := F.bdd_at_cusps' (hc.mono (Gamma1_le_GammaH_GL N H))

omit [NeZero N] in
@[scoped simp] theorem coe_restrict1 {k : ℤ} (F : ModularForm (CohCarrier.GammaH N H) k) :
    (⇑(restrict1 N H F) : UpperHalfPlane → ℂ) = ⇑F := rfl

omit [NeZero N] in
theorem one_mem_strictPeriods_Gamma1 : (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp

omit [NeZero N] in
theorem coe_finset_sum {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {ι : Type*} (s : Finset ι) (f : ι → ModularForm Γ k) :
    (⇑(∑ i ∈ s, f i) : UpperHalfPlane → ℂ) = ∑ i ∈ s, (⇑(f i) : UpperHalfPlane → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.coe_add, ih]

end IntSpanH
p2m_reactivate "P2MW.S_ModularCurve_exists_sum_smul_eq_of_isIntegralQExp_gammaH.IntSpanH"

open IntSpanH in
theorem solution
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) {k : ℤ}
    (F : ModularForm (CohCarrier.GammaH N H) k) :
    ∃ (n : ℕ) (c : Fin n → ℂ)
      (G : Fin n → ModularForm (CohCarrier.GammaH N H) k)
      (r : Fin n → PowerSeries ℤ),
      (∀ i, ModularCurve.IsIntegralQExp (G i) (r i)) ∧
      (⇑F : UpperHalfPlane → ℂ) = ∑ i, c i • (⇑(G i) : UpperHalfPlane → ℂ) := by
  classical

  obtain ⟨n, c, G, r, hG, hF⟩ := ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1 N (restrict1 N H F)
  rw [coe_restrict1] at hF

  let Q := (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) ⧸ ((Gamma1 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)))
  letI : Fintype Q := Fintype.ofFinite Q
  have hm : (Fintype.card Q : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero

  have hrep : ∀ q : Q, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 N ∧
      (q.out : GL (Fin 2) ℝ)⁻¹ = (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) := by
    intro q
    obtain ⟨γ, hγ, hγeq⟩ := q.out.2
    refine ⟨γ⁻¹, CohCarrier.GammaH_le_Gamma0 H (inv_mem hγ), ?_⟩
    rw [map_inv, ← hγeq]
  choose γq hγ0 hγeq using hrep

  have hqf : ∀ (f : ModularForm (Gamma1 N) k) (q : Q),
      SlashInvariantForm.quotientFunc (ℋ := (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ))) f q = (⇑f : UpperHalfPlane → ℂ) ∣[k] (γq q) := by
    intro f q
    conv_lhs => rw [← q.out_eq]
    rw [SlashInvariantForm.quotientFunc_mk, hγeq q]
    rfl

  have hclear : ∀ (i : Fin n) (q : Q), ∃ (a : ℕ) (f₁ : ModularForm (Gamma1 N) k) (p₁ : PowerSeries ℤ),
      IsIntegralQExp f₁ p₁ ∧ (⇑f₁ : UpperHalfPlane → ℂ) = ((N : ℂ) ^ a) • ((⇑(G i) : UpperHalfPlane → ℂ) ∣[k] (γq q)) :=
    fun i q => ModularCurve.exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0 N (G i) (hG i) (γq q) (hγ0 q)
  choose a f₁ p₁ hf₁ hf₁coe using hclear
  let A : Fin n → ℕ := fun i => ∑ q, a i q
  have hAge : ∀ i q, a i q ≤ A i := fun i q => Finset.single_le_sum (fun q _ => Nat.zero_le (a i q)) (Finset.mem_univ q)

  let S : Fin n → ModularForm (Gamma1 N) k := fun i => ∑ q, ((N : ℂ) ^ (A i - a i q)) • f₁ i q
  let P : Fin n → PowerSeries ℤ := fun i => ∑ q, ((N : ℤ) ^ (A i - a i q)) • p₁ i q
  have h1 := one_mem_strictPeriods_Gamma1 N

  have hT : ∀ i, (⇑(ModularForm.trace (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) (G i)) : UpperHalfPlane → ℂ) =
      ∑ q, (⇑(G i) : UpperHalfPlane → ℂ) ∣[k] (γq q) := by
    intro i
    rw [ModularForm.coe_trace]
    simp only [hqf]
    convert rfl
  have hScoe : ∀ i, (⇑(S i) : UpperHalfPlane → ℂ) =
      ((N : ℂ) ^ (A i)) • (⇑(ModularForm.trace (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) (G i)) : UpperHalfPlane → ℂ) := by
    intro i
    rw [hT, Finset.smul_sum]
    show (⇑(∑ q, ((N : ℂ) ^ (A i - a i q)) • f₁ i q) : UpperHalfPlane → ℂ) = _
    rw [coe_finset_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [ModularForm.IsGLPos.coe_smul, hf₁coe, smul_smul, ← pow_add, Nat.sub_add_cancel (hAge i q)]
  have hSint : ∀ i, IsIntegralQExp (⇑(S i)) (P i) := by
    intro i
    show (P i).map (Int.castRingHom ℂ) = qExpansion 1 ⇑(S i)
    have hq : qExpansion 1 ⇑(S i) = ModularForm.qExpansionAddHom one_pos h1 k (S i) := rfl
    rw [hq, map_sum, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    show (PowerSeries.map (Int.castRingHom ℂ)) (((N : ℤ) ^ (A i - a i q)) • p₁ i q) =
      qExpansion 1 ⇑(((N : ℂ) ^ (A i - a i q)) • f₁ i q)
    rw [ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos h1, ← (hf₁ i q)]
    rw [zsmul_eq_mul, map_mul, PowerSeries.smul_eq_C_mul]
    congr 1
    simp

  let G' : Fin n → ModularForm (CohCarrier.GammaH N H) k := fun i => ((N : ℂ) ^ (A i)) • ModularForm.trace (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) (G i)
  have hG'coe : ∀ i, (⇑(G' i) : UpperHalfPlane → ℂ) = ⇑(S i) := by
    intro i
    show (⇑(((N : ℂ) ^ (A i)) • ModularForm.trace (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) (G i)) : UpperHalfPlane → ℂ) = _
    rw [ModularForm.IsGLPos.coe_smul, hScoe]
  have hG'int : ∀ i, IsIntegralQExp (⇑(G' i)) (P i) := fun i => by rw [hG'coe]; exact hSint i

  have hFinv : ∀ q : Q, (⇑F : UpperHalfPlane → ℂ) ∣[k] (γq q) = ⇑F := by
    intro q
    have hmem : ((Matrix.SpecialLinearGroup.mapGL ℝ (γq q) : GL (Fin 2) ℝ)) ∈ (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) := by
      rw [← hγeq q]; exact inv_mem q.out.2
    have := SlashInvariantForm.slash_action_eqn F _ hmem
    exact this
  have htrF : (⇑(ModularForm.trace (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) (restrict1 N H F)) : UpperHalfPlane → ℂ) = (Fintype.card Q : ℂ) • ⇑F := by
    rw [ModularForm.coe_trace]
    simp only [hqf, coe_restrict1, hFinv, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ]
  have htrF' : (⇑(ModularForm.trace (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) (restrict1 N H F)) : UpperHalfPlane → ℂ) =
      ∑ i, c i • (⇑(ModularForm.trace (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) (G i)) : UpperHalfPlane → ℂ) := by
    rw [ModularForm.coe_trace]
    simp only [hqf, coe_restrict1, hF, hT, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [SlashAction.sum_slash]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ModularForm.SL_smul_slash]

  refine ⟨n, fun i => c i / ((Fintype.card Q : ℂ) * (N : ℂ) ^ (A i)), G', P, hG'int, ?_⟩
  have hN : ∀ i, ((N : ℂ) ^ (A i)) ≠ 0 := fun i => pow_ne_zero _ (by exact_mod_cast (NeZero.ne N))
  have key : (Fintype.card Q : ℂ) • (⇑F : UpperHalfPlane → ℂ) =
      ∑ i, c i • (⇑(ModularForm.trace (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) (G i)) : UpperHalfPlane → ℂ) := by rw [← htrF, htrF']
  calc (⇑F : UpperHalfPlane → ℂ)
      = (Fintype.card Q : ℂ)⁻¹ • ((Fintype.card Q : ℂ) • (⇑F : UpperHalfPlane → ℂ)) := by
        rw [smul_smul, inv_mul_cancel₀ hm, one_smul]
    _ = ∑ i, (c i / ((Fintype.card Q : ℂ) * (N : ℂ) ^ (A i))) • (⇑(G' i) : UpperHalfPlane → ℂ) := by
        rw [key, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hG'coe, hScoe, smul_smul, smul_smul]
        congr 1
        field_simp [hm, hN i]

end S_ModularCurve_exists_sum_smul_eq_of_isIntegralQExp_gammaH
end P2MW
export P2MW.S_ModularCurve_exists_sum_smul_eq_of_isIntegralQExp_gammaH (solution)
