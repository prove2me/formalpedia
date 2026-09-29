-- Prove2me | solution 1 for ModularCurve.index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField_comap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/7338aa86-35d8-506c-953b-9fa583e2b9ea

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_CohCarrier_Level
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_coeffMap_mem_qExpFunctionFieldC_and_eq_adjoin_image_coeffMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField_comap
p2m_attr_erase "instance" "TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X"
p2m_attr_erase "simp" "CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

namespace IgusaTransport_node13

open IsLocalRing ModularCurve

section ResidueIso

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))

def incl : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) →+* ↥A where
  toFun a := ⟨((a : ↥k₀) : AlgebraicClosure ℚ), a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

@[scoped simp] theorem coe_incl (a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) :
    ((incl A k₀ a : ↥A) : AlgebraicClosure ℚ) = ((a : ↥k₀) : AlgebraicClosure ℚ) := rfl

scoped instance incl_isLocalHom : IsLocalHom (incl A k₀) := by
  constructor
  intro a ha
  have ha0 : ((a : ↥k₀) : AlgebraicClosure ℚ) ≠ 0 := by
    intro h
    have : incl A k₀ a = 0 := Subtype.ext h
    rw [this] at ha
    exact not_isUnit_zero ha
  have ha0' : (a : ↥k₀) ≠ 0 := fun h => ha0 (by rw [h]; rfl)
  obtain ⟨u, hu⟩ := ha
  have hinv : (((a : ↥k₀) : AlgebraicClosure ℚ))⁻¹ ∈ A := by
    have hmul : ((incl A k₀ a : ↥A) : AlgebraicClosure ℚ) * (((u⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) = 1 := by
      have h := congrArg (fun z : ↥A => (z : AlgebraicClosure ℚ)) u.mul_inv
      rw [hu] at h
      simpa using h
    rw [coe_incl] at hmul
    rw [← eq_inv_of_mul_eq_one_right hmul]
    exact ((u⁻¹ : (↥A)ˣ) : ↥A).2
  have hinv₀ : (a : ↥k₀)⁻¹ ∈ A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) := by
    show algebraMap ↥k₀ (AlgebraicClosure ℚ) (a : ↥k₀)⁻¹ ∈ A
    rw [map_inv₀]
    exact hinv
  exact ⟨⟨a, ⟨(a : ↥k₀)⁻¹, hinv₀⟩, Subtype.ext (mul_inv_cancel₀ ha0'), Subtype.ext (inv_mul_cancel₀ ha0')⟩, rfl⟩

noncomputable def θ : ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) →+* ResidueField ↥A :=
  ResidueField.map (incl A k₀)

theorem θ_residue (a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) :
    θ A k₀ (residue _ a) = residue ↥A (incl A k₀ a) := ResidueField.map_residue _ a

theorem θ_bijective
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧
      ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) :
    Function.Bijective (θ A k₀) := by
  refine ⟨(θ A k₀).injective, ?_⟩
  intro r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  obtain ⟨c, hc, h, hm⟩ := hκ (a : AlgebraicClosure ℚ) a.2
  refine ⟨residue _ ⟨c, hc⟩, ?_⟩
  rw [θ_residue]

  have : a - incl A k₀ ⟨c, hc⟩ = ⟨_, h⟩ := Subtype.ext rfl
  symm
  rw [← sub_eq_zero, ← map_sub, this, IsLocalRing.residue_eq_zero_iff]
  exact hm

end ResidueIso

theorem algebraMap_eq_C {L : Type} [Field L] (c : L) : algebraMap L (LaurentSeries L) c = HahnSeries.C c := by
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]

theorem coe_algebraMap_eq_C {L : Type} [Field L] (F : IntermediateField L (LaurentSeries L)) (c : L) :
    ((algebraMap L F c : F) : LaurentSeries L) = HahnSeries.C c := by
  rw [SubalgebraClass.coe_algebraMap, algebraMap_eq_C]

section Transport

variable {κ₀ κ : Type} [Field κ₀] [Field κ] (θ : κ₀ →+* κ)
  (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))

theorem coeffMap_injective' : Function.Injective (coeffMap θ) := by
  intro a b h
  ext n
  apply θ.injective
  exact congrArg (fun z : LaurentSeries κ => z.coeff n) h

theorem coeffMap_C' (c : κ₀) : coeffMap θ (HahnSeries.C c) = HahnSeries.C (θ c) :=
  HahnSeries.map_C c θ

noncomputable def Ψ : ↥(qExpFunctionFieldC κ₀ Γ) →+* ↥(qExpFunctionFieldC κ Γ) where
  toFun y := ⟨coeffMap θ y, (coeffMap_mem_qExpFunctionFieldC_and_eq_adjoin_image_coeffMap κ₀ κ θ Γ).1 y y.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

@[scoped simp] theorem coe_Ψ (y : ↥(qExpFunctionFieldC κ₀ Γ)) :
    ((Ψ θ Γ y : ↥(qExpFunctionFieldC κ Γ)) : LaurentSeries κ) = coeffMap θ y := rfl

theorem Ψ_injective : Function.Injective (Ψ θ Γ) := fun a b h =>
  Subtype.ext (coeffMap_injective' θ (congrArg (fun z : ↥(qExpFunctionFieldC κ Γ) => (z : LaurentSeries κ)) h))

theorem Ψ_algebraMap (c : κ₀) : Ψ θ Γ (algebraMap κ₀ _ c) = algebraMap κ _ (θ c) := by
  apply Subtype.ext
  rw [coe_Ψ, coe_algebraMap_eq_C, coe_algebraMap_eq_C, coeffMap_C']

theorem Ψ_surjective (hθ : Function.Surjective θ) : Function.Surjective (Ψ θ Γ) := by
  let S : Subfield (LaurentSeries κ) := (qExpFunctionFieldC κ₀ Γ).toSubfield.map (coeffMap θ)
  have hSalg : ∀ c : κ, algebraMap κ (LaurentSeries κ) c ∈ S := by
    intro c
    obtain ⟨c₀, rfl⟩ := hθ c
    refine ⟨HahnSeries.C c₀, ?_, ?_⟩
    · show HahnSeries.C c₀ ∈ qExpFunctionFieldC κ₀ Γ
      rw [← algebraMap_eq_C]
      exact (qExpFunctionFieldC κ₀ Γ).algebraMap_mem c₀
    · rw [coeffMap_C', algebraMap_eq_C]
  let T : IntermediateField κ (LaurentSeries κ) := S.toIntermediateField hSalg
  have hle : qExpFunctionFieldC κ Γ ≤ T := by
    rw [(coeffMap_mem_qExpFunctionFieldC_and_eq_adjoin_image_coeffMap κ₀ κ θ Γ).2, IntermediateField.adjoin_le_iff]
    rintro z ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  intro z
  obtain ⟨y, hy, hyz⟩ := hle z.2
  exact ⟨⟨y, hy⟩, Subtype.ext hyz⟩

theorem Ψ_aeval (x : ↥(qExpFunctionFieldC κ₀ Γ)) (p : Polynomial κ₀) :
    Ψ θ Γ (Polynomial.aeval x p) = Polynomial.aeval (Ψ θ Γ x) (p.map θ) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂]
  congr 1
  exact RingHom.ext fun c => Ψ_algebraMap θ Γ c

theorem Ψ_mem_adjoin (x : ↥(qExpFunctionFieldC κ₀ Γ)) (a : ↥(qExpFunctionFieldC κ₀ Γ))
    (ha : a ∈ IntermediateField.adjoin κ₀ ({x} : Set ↥(qExpFunctionFieldC κ₀ Γ))) :
    Ψ θ Γ a ∈ IntermediateField.adjoin κ ({Ψ θ Γ x} : Set ↥(qExpFunctionFieldC κ Γ)) := by
  rw [IntermediateField.mem_adjoin_simple_iff] at ha ⊢
  obtain ⟨r, s, rfl⟩ := ha
  exact ⟨r.map θ, s.map θ, by rw [map_div₀, Ψ_aeval, Ψ_aeval]⟩

theorem exists_Ψ_eq_of_mem_adjoin (hθ : Function.Surjective θ) (x : ↥(qExpFunctionFieldC κ₀ Γ))
    (b : ↥(qExpFunctionFieldC κ Γ))
    (hb : b ∈ IntermediateField.adjoin κ ({Ψ θ Γ x} : Set ↥(qExpFunctionFieldC κ Γ))) :
    ∃ a ∈ IntermediateField.adjoin κ₀ ({x} : Set ↥(qExpFunctionFieldC κ₀ Γ)), Ψ θ Γ a = b := by
  rw [IntermediateField.mem_adjoin_simple_iff] at hb
  obtain ⟨r, s, rfl⟩ := hb
  obtain ⟨r₀, rfl⟩ := Polynomial.map_surjective θ hθ r
  obtain ⟨s₀, rfl⟩ := Polynomial.map_surjective θ hθ s
  refine ⟨Polynomial.aeval x r₀ / Polynomial.aeval x s₀, ?_, by rw [map_div₀, Ψ_aeval, Ψ_aeval]⟩
  rw [IntermediateField.mem_adjoin_simple_iff]
  exact ⟨r₀, s₀, rfl⟩

noncomputable def ι (x : ↥(qExpFunctionFieldC κ₀ Γ)) :
    ↥(IntermediateField.adjoin κ₀ ({x} : Set ↥(qExpFunctionFieldC κ₀ Γ))) →+*
      ↥(IntermediateField.adjoin κ ({Ψ θ Γ x} : Set ↥(qExpFunctionFieldC κ Γ))) where
  toFun a := ⟨Ψ θ Γ a, Ψ_mem_adjoin θ Γ x a a.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem ι_bijective (hθ : Function.Surjective θ) (x : ↥(qExpFunctionFieldC κ₀ Γ)) :
    Function.Bijective (ι θ Γ x) := by
  refine ⟨fun a b h => Subtype.ext (Ψ_injective θ Γ (congrArg Subtype.val h)), ?_⟩
  intro b
  obtain ⟨a, ha, hab⟩ := exists_Ψ_eq_of_mem_adjoin θ Γ hθ x b b.2
  exact ⟨⟨a, ha⟩, Subtype.ext hab⟩

theorem finrank_adjoin_eq (hθ : Function.Surjective θ) (x : ↥(qExpFunctionFieldC κ₀ Γ)) :
    Module.finrank ↥(IntermediateField.adjoin κ₀ ({x} : Set ↥(qExpFunctionFieldC κ₀ Γ))) ↥(qExpFunctionFieldC κ₀ Γ) =
      Module.finrank ↥(IntermediateField.adjoin κ ({Ψ θ Γ x} : Set ↥(qExpFunctionFieldC κ Γ))) ↥(qExpFunctionFieldC κ Γ) :=
  Algebra.finrank_eq_of_equiv_equiv (RingEquiv.ofBijective (ι θ Γ x) (ι_bijective θ Γ hθ x))
    (RingEquiv.ofBijective (Ψ θ Γ) ⟨Ψ_injective θ Γ, Ψ_surjective θ Γ hθ⟩) (RingHom.ext fun a => rfl)

end Transport

section PlusMinus

open CongruenceSubgroup

theorem neg_one_mem_Gamma0 (M : ℕ) : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Gamma0 M := by
  rw [Gamma0_mem]
  simp [Matrix.SpecialLinearGroup.coe_neg]

theorem gamma0Units_neg_one (M : ℕ) :
    CohCarrier.gamma0Units M ⟨-1, neg_one_mem_Gamma0 M⟩ = -1 := by
  ext
  rw [CohCarrier.val_gamma0Units, Units.val_neg, Units.val_one]
  simp [Gamma0Map, Matrix.SpecialLinearGroup.coe_neg]

theorem GammaH_sup_eq (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) =
      CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1)) := by
  apply le_antisymm
  · apply sup_le
    · intro γ hγ
      obtain ⟨h0, h⟩ := CohCarrier.mem_GammaH_iff.mp hγ
      exact CohCarrier.mem_GammaH_iff.mpr ⟨h0, Subgroup.mem_sup_left h⟩
    · rw [Subgroup.zpowers_le, CohCarrier.mem_GammaH_iff]
      exact ⟨neg_one_mem_Gamma0 M, by
        rw [gamma0Units_neg_one]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)⟩
  · intro γ hγ
    obtain ⟨h0, hH⟩ := CohCarrier.mem_GammaH_iff.mp hγ
    obtain ⟨u, hu, z, hz, huz⟩ := Subgroup.mem_sup.mp hH
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    let ν : ↥(Gamma0 M) := ⟨-1, neg_one_mem_Gamma0 M⟩
    have hνk : CohCarrier.gamma0Units M (ν ^ k) = (-1) ^ k := by
      rw [map_zpow, gamma0Units_neg_one]
    have hs : ((ν ^ k : ↥(Gamma0 M)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈
        Subgroup.zpowers (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) := by
      rw [Subgroup.coe_zpow]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
    have hγ' : γ * ((ν ^ k : ↥(Gamma0 M)) : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹ ∈ CohCarrier.GammaH M H := by
      rw [CohCarrier.mem_GammaH_iff]
      refine ⟨(Gamma0 M).mul_mem h0 ((Gamma0 M).inv_mem (ν ^ k).2), ?_⟩
      have : (⟨γ * ((ν ^ k : ↥(Gamma0 M)) : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹,
          (Gamma0 M).mul_mem h0 ((Gamma0 M).inv_mem (ν ^ k).2)⟩ : ↥(Gamma0 M)) = ⟨γ, h0⟩ * (ν ^ k)⁻¹ :=
        Subtype.ext rfl
      rw [this, map_mul, map_inv, hνk, ← huz, mul_inv_cancel_right]
      exact hu
    have hγeq : γ = γ * ((ν ^ k : ↥(Gamma0 M)) : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹ *
        ((ν ^ k : ↥(Gamma0 M)) : Matrix.SpecialLinearGroup (Fin 2) ℤ) := by
      rw [inv_mul_cancel_right]
    rw [hγeq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hγ') (Subgroup.mem_sup_right hs)

end PlusMinus

end IgusaTransport_node13
p2m_reactivate "P2MW.S_ModularCurve_index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField_comap.IgusaTransport_node13"

open IgusaTransport_node13 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hqM : ¬ q ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧
      ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ IsLocalRing.maximalIdeal A)
    (x : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
      (CohCarrier.GammaH M H)))
    (hx : (x : LaurentSeries (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) =
      ModularCurve.jqModC (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) :
    (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)).index ≤
      Module.finrank
        ↥(IntermediateField.adjoin (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
          ({x} : Set ↥(ModularCurve.qExpFunctionFieldC
            (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (CohCarrier.GammaH M H))))
        ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
          (CohCarrier.GammaH M H))  := by
  classical
  obtain ⟨-, hθsurj⟩ := θ_bijective A k₀ hκ
  have hx' : ((Ψ (θ A k₀) (CohCarrier.GammaH M H) x :
      ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH M H))) :
        LaurentSeries (IsLocalRing.ResidueField ↥A)) = ModularCurve.jqModC _ := by
    rw [coe_Ψ, hx]
    change (ModularCurve.jqModC _).map _ = _
    exact ModularCurve.map_jqModC _
  have h1 := ModularCurve.index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField M H hqM A hA
    (Ψ (θ A k₀) (CohCarrier.GammaH M H) x) hx'
  rw [← GammaH_sup_eq] at h1
  rw [finrank_adjoin_eq (θ A k₀) (CohCarrier.GammaH M H) hθsurj x]
  exact h1

end S_ModularCurve_index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField_comap
end P2MW
export P2MW.S_ModularCurve_index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField_comap (solution)
