-- Prove2me | solution 1 for ModularCurve.exists_iso_twoChartIntegralModel_qExpFunctionFieldC_gammaH_diamond
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/5154f691-4dee-5e45-8e08-fc72add35840

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_algEquiv_apply_eq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegral
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_iso_twoChartIntegralModel_qExpFunctionFieldC_gammaH_diamond

set_option autoImplicit false

open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve CongruenceSubgroup

namespace DiaBody

abbrev RR (p : ℕ) : Type := ↥(GaloisRep.ratLocalizedAt p)

abbrev FF (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Type := ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))

section Alg
variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {p : ℕ} [Fact p.Prime]

theorem algebraMap_RR_apply (r : RR p) : algebraMap (RR p) (FF M H) r = ((r : ℚ) : FF M H) :=
  eq_ratCast (@algebraMap ℚ (FF M H) _ _ DivisionRing.toRatAlgebra) (r : ℚ)

noncomputable def toAlgEquivR (p : ℕ) [Fact p.Prime] (σ : RingAut (FF M H)) : FF M H ≃ₐ[RR p] FF M H :=
  AlgEquiv.ofRingEquiv (f := σ) (fun r => by rw [algebraMap_RR_apply]; exact map_ratCast σ (r : ℚ))

@[scoped simp] theorem toAlgEquivR_apply (σ : RingAut (FF M H)) (x : FF M H) : toAlgEquivR p σ x = σ x := rfl

end Alg

section Group
variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

theorem exists_gamma0_apply_eq (d : (ZMod M)ˣ) :
    ∃ γ : Gamma0 M, (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
  set a : ℤ := ((d : ZMod M).val : ℤ) with ha
  have hcop : Nat.Coprime (d : ZMod M).val M := ZMod.val_coe_unit_coprime d
  have hg : Int.gcd a (M : ℤ) = 1 := by rw [ha, Int.gcd_natCast_natCast]; exact hcop
  have hbez : a * Int.gcdA a M + (M : ℤ) * Int.gcdB a M = 1 := by
    have h := Int.gcd_eq_gcd_ab a M
    rw [hg] at h
    push_cast at h
    linarith
  let A : Matrix (Fin 2) (Fin 2) ℤ := !![a, -Int.gcdB a M; (M : ℤ), Int.gcdA a M]
  have hdet : A.det = 1 := by
    rw [Matrix.det_fin_two_of]
    linarith
  refine ⟨⟨⟨A, hdet⟩, ?_⟩, ?_⟩
  · rw [Gamma0_mem]
    show (((M : ℤ) : ℤ) : ZMod M) = 0
    simp
  · show ((a : ℤ) : ZMod M) = d
    rw [ha, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem gamma0_diag (γ : Gamma0 M) :
    (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) * (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = 1 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe (γ : SL(2, ℤ))
  rw [Matrix.det_fin_two] at hdet
  have h10 : (((γ : SL(2, ℤ)) 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp γ.2
  have := congrArg (Int.cast : ℤ → ZMod M) hdet
  push_cast at this
  rw [h10, mul_zero, sub_zero] at this
  exact this

theorem mul_inv_mem_Gamma1 (γ γ' : Gamma0 M)
    (h : (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (((γ' : SL(2, ℤ)) 0 0 : ℤ) : ZMod M)) :
    ((γ * γ'⁻¹ : Gamma0 M) : SL(2, ℤ)) ∈ Gamma1 M := by
  have hd := gamma0_diag γ
  have hd' := gamma0_diag γ'
  have h10 : (((γ : SL(2, ℤ)) 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp γ.2
  have h10' : (((γ' : SL(2, ℤ)) 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp γ'.2

  have hmul : ((γ * γ'⁻¹ : Gamma0 M) : SL(2, ℤ)) = (γ : SL(2, ℤ)) * (γ' : SL(2, ℤ))⁻¹ := rfl
  rw [Gamma1_mem, hmul]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  push_cast
  rw [h10, h10']
  refine ⟨?_, ?_, by ring⟩
  ·
    rw [h]; linear_combination hd'
  ·
    rw [← h]; linear_combination hd

theorem Gamma1_le_GammaH : Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  have hA' := hA
  rw [Gamma1_mem] at hA'
  have hA0 : A ∈ Gamma0 M := by rw [Gamma0_mem]; exact hA'.2.2
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
  have h1 : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact hA'.2.1
  rw [h1]
  exact one_mem H

theorem mem_GammaH_of_apply_mem (γ : Gamma0 M) (d : (ZMod M)ˣ)
    (h : (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (d : ZMod M)) (hd : d ∈ H) :
    (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H := by
  refine CohCarrier.mem_GammaH_iff.mpr ⟨γ.2, ?_⟩
  have hu : CohCarrier.gamma0Units M ⟨γ, γ.2⟩ = d⁻¹ := by
    rw [← mul_eq_one_iff_eq_inv', eq_comm]
    symm
    ext
    rw [Units.val_mul, CohCarrier.val_gamma0Units, Units.val_one, ← h]
    exact gamma0_diag γ
  rw [hu]
  exact inv_mem hd

end Group

section Model
universe u
variable {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] {j : F} [Fact (j ≠ 0)]

theorem iso_eq_of_pin [IsSeparated (TwoChartIntegralModel.toBase R F j)]
    (w₁ w₂ : TwoChartIntegralModel R F j ≅ TwoChartIntegralModel R F j)
    (h₁ : w₁.hom ≫ TwoChartIntegralModel.toBase R F j = TwoChartIntegralModel.toBase R F j)
    (h₂ : w₂.hom ≫ TwoChartIntegralModel.toBase R F j = TwoChartIntegralModel.toBase R F j)
    (e₁ e₂ : ↥(TwoChartIntegralModel.chartAlgFin R F j) →ₐ[R] ↥(TwoChartIntegralModel.chartAlgFin R F j))
    (he : ∀ x, (e₁ x : F) = (e₂ x : F))
    (p₁ : Spec.map (CommRingCat.ofHom e₁.toRingHom) ≫ TwoChartIntegralModel.ιFin R F j = TwoChartIntegralModel.ιFin R F j ≫ w₁.inv)
    (p₂ : Spec.map (CommRingCat.ofHom e₂.toRingHom) ≫ TwoChartIntegralModel.ιFin R F j = TwoChartIntegralModel.ιFin R F j ≫ w₂.inv) :
    w₁ = w₂ := by
  have hee : e₁ = e₂ := AlgHom.ext fun x => Subtype.ext (he x)
  rw [hee] at p₁
  haveI := TwoChartIntegralModel.isIntegral R F j
  haveI : IsDominant (TwoChartIntegralModel.ιFin R F j) := ⟨by
    have hopen : IsOpen (Set.range (TwoChartIntegralModel.ιFin R F j).base) :=
      (TwoChartIntegralModel.ιFin R F j).isOpenEmbedding.isOpen_range
    exact hopen.dense (Set.range_nonempty _)⟩
  have hover₁ : w₁.inv ≫ TwoChartIntegralModel.toBase R F j = TwoChartIntegralModel.toBase R F j := by
    rw [Iso.inv_comp_eq, h₁]
  have hover₂ : w₂.inv ≫ TwoChartIntegralModel.toBase R F j = TwoChartIntegralModel.toBase R F j := by
    rw [Iso.inv_comp_eq, h₂]
  have hinv : w₁.inv = w₂.inv :=
    ext_of_isDominant_of_isSeparated (TwoChartIntegralModel.toBase R F j) (by rw [hover₁, hover₂])
      (TwoChartIntegralModel.ιFin R F j) (by rw [← p₁, ← p₂])
  ext1
  rw [← cancel_mono w₁.inv, Iso.hom_inv_id, hinv, Iso.hom_inv_id]

end Model

end DiaBody
p2m_reactivate "P2MW.S_ModularCurve_exists_iso_twoChartIntegralModel_qExpFunctionFieldC_gammaH_diamond.DiaBody"

open DiaBody in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (p : ℕ) [Fact p.Prime]
    (j : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) [Fact (j ≠ 0)] (hj : (j : LaurentSeries ℚ) = jqModC ℚ)
    [IsSeparated (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j)]
    (ρ : CongruenceSubgroup.Gamma0 M →* RingAut ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hρH : ∀ γ : CongruenceSubgroup.Gamma0 M, (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H → ρ γ = 1)
    (hρ0 : ∀ (γ : CongruenceSubgroup.Gamma0 M) (x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))),
      (x : LaurentSeries ℚ) ∈ qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M) → ρ γ x = x) :
    ∃ (dia : (ZMod M)ˣ →
        (TwoChartIntegralModel ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j ≅
          TwoChartIntegralModel ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j))
      (diaFin : (ZMod M)ˣ →
        (↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j)
          →ₐ[↥(GaloisRep.ratLocalizedAt p)]
          ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j)))
      (diaInf : (ZMod M)ˣ →
        (↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j)
          →ₐ[↥(GaloisRep.ratLocalizedAt p)]
          ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j))),
      (∀ d, (dia d).hom ≫ TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j =
        TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j) ∧
      (∀ d d', (dia (d * d')).hom = (dia d).hom ≫ (dia d').hom) ∧
      (∀ d, d ∈ H → dia d = Iso.refl _) ∧
      (∀ (d : (ZMod M)ˣ) (γ : CongruenceSubgroup.Gamma0 M), (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = d →
        (∀ x, ((diaFin d x : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p)
            ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) = ρ γ x) ∧
        (∀ x, ((diaInf d x : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p)
            ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) = ρ γ x) ∧
        Spec.map (CommRingCat.ofHom (diaFin d).toRingHom) ≫
            TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j =
          TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j ≫ (dia d).inv ∧
        Spec.map (CommRingCat.ofHom (diaInf d).toRingHom) ≫
            TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j =
          TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j ≫ (dia d).inv) := by
  classical

  have hjmem : ∀ γ : Gamma0 M, toAlgEquivR p (ρ γ) j = j := fun γ =>
    hρ0 γ j (by rw [hj]; exact intFormRatiosC_subset ℚ _ (jqModC_mem_intFormRatiosC ℚ (Gamma0 M)))
  have hρeq : ∀ γ γ' : Gamma0 M, (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (((γ' : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) → ρ γ = ρ γ' := by
    intro γ γ' h
    have hmem := Gamma1_le_GammaH (H := H) (mul_inv_mem_Gamma1 γ γ' h)
    have := hρH _ hmem
    rwa [map_mul, map_inv, mul_inv_eq_one] at this

  choose W EF EI hEF hEI hover hpF hpI using fun γ : Gamma0 M =>
    TwoChartIntegralModel.exists_iso_of_algEquiv_apply_eq (RR p) (FF M H) (FF M H) j j (toAlgEquivR p (ρ γ)) (hjmem γ)

  choose γ_ hγ_ using fun d : (ZMod M)ˣ => exists_gamma0_apply_eq (M := M) d
  refine ⟨fun d => W (γ_ d), fun d => EF (γ_ d), fun d => EI (γ_ d), fun d => hover (γ_ d), ?_, ?_, ?_⟩
  ·
    intro d d'

    have hprod : ρ (γ_ (d * d')) = ρ (γ_ d' * γ_ d) := by
      apply hρeq
      rw [hγ_, mul_comm d d']
      have h10 : ((((γ_ d) : SL(2, ℤ)) 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp (γ_ d).2
      rw [Units.val_mul, ← hγ_ d, ← hγ_ d']
      show _ = ((((γ_ d' : SL(2, ℤ)) * (γ_ d : SL(2, ℤ))) 0 0 : ℤ) : ZMod M)
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      push_cast
      rw [h10, mul_zero, add_zero]

    have key := iso_eq_of_pin (W (γ_ (d * d'))) (W (γ_ d) ≪≫ W (γ_ d')) (hover _)
      (by rw [Iso.trans_hom, Category.assoc, hover, hover])
      (EF (γ_ (d * d'))) ((EF (γ_ d')).comp (EF (γ_ d)))
      (fun x => by
        rw [hEF, AlgHom.comp_apply, hEF, toAlgEquivR_apply, toAlgEquivR_apply, hprod, map_mul]
        show _ = ρ (γ_ d') (EF (γ_ d) x : FF M H)
        rw [hEF, toAlgEquivR_apply]
        rfl)
      (hpF _)
      (by
        rw [Iso.trans_inv]
        show Spec.map (CommRingCat.ofHom ((EF (γ_ d')).toRingHom.comp (EF (γ_ d)).toRingHom)) ≫ _ = _
        rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hpF, ← Category.assoc, hpF, Category.assoc])
    exact (congrArg Iso.hom key).trans (Iso.trans_hom _ _)
  ·
    intro d hd
    have h1 : ρ (γ_ d) = 1 := hρH _ (mem_GammaH_of_apply_mem (γ_ d) d (hγ_ d) hd)
    apply iso_eq_of_pin (W (γ_ d)) (Iso.refl _) (hover _) (by simp) (EF (γ_ d)) (AlgHom.id _ _)
      (fun x => by rw [hEF, toAlgEquivR_apply, h1]; rfl) (hpF _)
    simp
  ·
    intro d γ hγ
    have hγρ : ρ γ = ρ (γ_ d) := hρeq γ (γ_ d) (by rw [hγ, hγ_])
    refine ⟨fun x => ?_, fun x => ?_, hpF _, hpI _⟩
    · rw [hEF, toAlgEquivR_apply, hγρ]
    · rw [hEI, toAlgEquivR_apply, hγρ]

#print axioms solution

end S_ModularCurve_exists_iso_twoChartIntegralModel_qExpFunctionFieldC_gammaH_diamond
end P2MW
export P2MW.S_ModularCurve_exists_iso_twoChartIntegralModel_qExpFunctionFieldC_gammaH_diamond (solution)
