-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.exists_levelReading_baseChange_of_isAlgClosed_rigidDataH1Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/70dec364-ca7c-5329-af3d-7ab82c07254a

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Theorems.Thm_WeierstrassCurve_Affine_Point_eval_prePsi_eq_zero_iff_smul_eq_zero_and_two_smul_ne_zero
import Theorems.Thm_ModularCurve_IsGamma0PowAt_isAddCyclic_closure_and_natCard_eq_pow
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_basisReading_levelComponent_map_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_nonsingular_nsmul_eq_zero_and_two_nsmul_ne_zero_of_eval_prePsi_eq_zero
import Theorems.Thm_ModularCurve_InLine_some_mem_zmultiples_some_of_nonsingular
import Theorems.Thm_WeierstrassCurve_isCoprime_Phi_PsiSq
import Theorems.Thm_WeierstrassCurve_Affine_Point_eval_psiSq_eq_zero_of_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_psi_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_exists_levelReading_baseChange_of_isAlgClosed_rigidDataH1Pow
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

universe u

noncomputable section

namespace P2M
namespace LevelReading

section Cyclic

variable {G : Type*} [AddCommGroup G]

theorem mem_zmultiples_add_of_coprime {g l : G} (hco : (addOrderOf g).Coprime (addOrderOf l)) :
    g ∈ AddSubgroup.zmultiples (g + l) := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hco

  have hlo : (addOrderOf l : ℤ) • l = 0 := by
    rw [natCast_zsmul]; exact addOrderOf_nsmul_eq_zero l
  have hgo : (addOrderOf g : ℤ) • g = 0 := by
    rw [natCast_zsmul]; exact addOrderOf_nsmul_eq_zero g
  have hn : (addOrderOf l : ℤ) • (g + l) = (addOrderOf l : ℤ) • g := by
    rw [smul_add, hlo, add_zero]
  have hg : g = (b * (addOrderOf l : ℤ)) • (g + l) := by
    rw [← smul_smul, hn, smul_smul]
    have h1 : (b * (addOrderOf l : ℤ)) = 1 - a * (addOrderOf g : ℤ) := by linear_combination hab
    rw [h1, sub_zsmul, one_zsmul, ← smul_smul, hgo, smul_zero]
    simp
  have hmem := AddSubgroup.zsmul_mem_zmultiples (g + l) (b * (addOrderOf l : ℤ))
  rwa [← hg] at hmem

theorem zmultiples_sup_zmultiples_of_coprime {g l : G} (hco : (addOrderOf g).Coprime (addOrderOf l)) :
    AddSubgroup.zmultiples g ⊔ AddSubgroup.zmultiples l = AddSubgroup.zmultiples (g + l) := by
  apply le_antisymm
  · rw [sup_le_iff, AddSubgroup.zmultiples_le, AddSubgroup.zmultiples_le]
    refine ⟨mem_zmultiples_add_of_coprime hco, ?_⟩
    rw [add_comm]
    exact mem_zmultiples_add_of_coprime hco.symm
  · rw [AddSubgroup.zmultiples_le]
    exact AddSubgroup.add_mem _ (AddSubgroup.mem_sup_left (AddSubgroup.mem_zmultiples g))
      (AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples l))

theorem isAddCyclic_biSup_and_natCard {ι : Type*} (s : Finset ι) (H : ι → AddSubgroup G) (n : ι → ℕ)
    (hpos : ∀ i ∈ s, 0 < n i) (hcyc : ∀ i ∈ s, IsAddCyclic (H i)) (hcard : ∀ i ∈ s, Nat.card (H i) = n i)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (n i).Coprime (n j)) :
    IsAddCyclic (⨆ i ∈ s, H i : AddSubgroup G) ∧ Nat.card (⨆ i ∈ s, H i : AddSubgroup G) = ∏ i ∈ s, n i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hbot : (⨆ i ∈ (∅ : Finset ι), H i : AddSubgroup G) = ⊥ := by simp
    rw [hbot, Finset.prod_empty]
    exact ⟨inferInstance, by simp⟩
  | insert a s ha ih =>
    obtain ⟨hcyc', hcard'⟩ := ih (fun i hi => hpos i (Finset.mem_insert_of_mem hi))
      (fun i hi => hcyc i (Finset.mem_insert_of_mem hi)) (fun i hi => hcard i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj hij => hcop i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)

    obtain ⟨g, hg⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top (H a)).mp
      (hcyc a (Finset.mem_insert_self a s))
    obtain ⟨l, hl⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top _).mp hcyc'
    have hordg : addOrderOf g = n a := by
      rw [← Nat.card_zmultiples, hg, hcard a (Finset.mem_insert_self a s)]
    have hordl : addOrderOf l = ∏ i ∈ s, n i := by
      rw [← Nat.card_zmultiples, hl, hcard']
    have hco : (addOrderOf g).Coprime (addOrderOf l) := by
      rw [hordg, hordl]
      exact Nat.Coprime.prod_right fun i hi => hcop a (Finset.mem_insert_self a s) i
        (Finset.mem_insert_of_mem hi) (fun h => ha (h ▸ hi))
    rw [Finset.iSup_insert, ← hg, ← hl, zmultiples_sup_zmultiples_of_coprime hco, Finset.prod_insert ha]
    refine ⟨inferInstance, ?_⟩
    rw [Nat.card_zmultiples, (AddCommute.all g l).addOrderOf_add_eq_mul_addOrderOf_of_coprime hco, hordg, hordl]

end Cyclic

section Readings

variable {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

open Classical in

def rd (x y : F) : W.toAffine.Point :=
  if h : W.toAffine.Nonsingular x y then WeierstrassCurve.Affine.Point.some x y h else 0

omit [DecidableEq F] in
theorem rd_of_nonsingular {x y : F} (h : W.toAffine.Nonsingular x y) :
    rd W x y = WeierstrassCurve.Affine.Point.some x y h := by
  classical
  unfold rd
  rw [dif_pos h]

def kerPts (h : Polynomial F) : Set W.toAffine.Point :=
  {P | ∃ (x y : F) (hxy : W.toAffine.Nonsingular x y), P = WeierstrassCurve.Affine.Point.some x y hxy ∧ h.eval x = 0}

def kerRd (h : Polynomial F) : AddSubgroup W.toAffine.Point :=
  AddSubgroup.closure (kerPts W h)

end Readings

section Galois

variable {K₀ Ω : Type u} [Field K₀] [Field Ω] [DecidableEq Ω] [Algebra K₀ Ω]
  (E : WeierstrassCurve K₀)

scoped instance isElliptic_baseChange [E.IsElliptic] : (E.baseChange Ω).IsElliptic := by
  show (E.map (algebraMap K₀ Ω)).IsElliptic
  infer_instance

theorem rd_map (σ : Ω →ₐ[K₀] Ω) (x y : Ω) :
    rd (E.baseChange Ω) (σ x) (σ y) = WeierstrassCurve.Affine.Point.map σ (rd (E.baseChange Ω) x y) := by
  classical
  unfold rd
  by_cases hns : (E.baseChange Ω).toAffine.Nonsingular x y
  · have hns' : (E.baseChange Ω).toAffine.Nonsingular (σ x) (σ y) :=
      (WeierstrassCurve.Affine.baseChange_nonsingular (W := E) (f := σ) σ.toRingHom.injective x y).mpr hns
    rw [dif_pos hns, dif_pos hns', WeierstrassCurve.Affine.Point.map_some]
  · have hns' : ¬ (E.baseChange Ω).toAffine.Nonsingular (σ x) (σ y) := fun h' =>
      hns ((WeierstrassCurve.Affine.baseChange_nonsingular (W := E) (f := σ) σ.toRingHom.injective x y).mp h')
    rw [dif_neg hns, dif_neg hns', map_zero]

theorem map_id' (P : (E.baseChange Ω).toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (AlgHom.id K₀ Ω) P = P := by
  cases P <;> rfl

theorem image_kerPts (σ : Ω ≃ₐ[K₀] Ω) (h : Polynomial Ω) :
    (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω)) '' kerPts (E.baseChange Ω) h =
      kerPts (E.baseChange Ω) (h.map (σ : Ω →+* Ω)) := by
  ext P'
  constructor
  · rintro ⟨P, ⟨x, y, hxy, rfl, hx⟩, rfl⟩
    refine ⟨σ x, σ y, (WeierstrassCurve.Affine.baseChange_nonsingular (W := E) (f := (σ : Ω →ₐ[K₀] Ω))
      (σ : Ω →ₐ[K₀] Ω).toRingHom.injective x y).mpr hxy, ?_, ?_⟩
    · rw [WeierstrassCurve.Affine.Point.map_some]
      rfl
    · have : (h.map (σ : Ω →+* Ω)).eval ((σ : Ω →+* Ω) x) = 0 := by
        rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hx, map_zero]
      simpa using this
  · rintro ⟨x', y', hxy', rfl, hx'⟩
    refine ⟨WeierstrassCurve.Affine.Point.map (σ.symm : Ω →ₐ[K₀] Ω)
      (WeierstrassCurve.Affine.Point.some x' y' hxy'), ⟨σ.symm x', σ.symm y',
        (WeierstrassCurve.Affine.baseChange_nonsingular (W := E) (f := (σ.symm : Ω →ₐ[K₀] Ω))
          (σ.symm : Ω →ₐ[K₀] Ω).toRingHom.injective x' y').mpr hxy', ?_, ?_⟩, ?_⟩
    · rw [WeierstrassCurve.Affine.Point.map_some]
      rfl
    · have h1 : (h.map (σ : Ω →+* Ω)).eval ((σ : Ω →+* Ω) (σ.symm x')) = (σ : Ω →+* Ω) (h.eval (σ.symm x')) := by
        rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
      have h2 : (σ : Ω →+* Ω) (σ.symm x') = x' := σ.apply_symm_apply x'
      rw [h2, hx'] at h1
      have h3 : σ.symm ((σ : Ω →+* Ω) (h.eval (σ.symm x'))) = σ.symm 0 := congrArg σ.symm h1.symm
      rw [map_zero] at h3
      rw [← h3]
      exact (σ.symm_apply_apply _).symm
    · rw [WeierstrassCurve.Affine.Point.map_map]
      have hc : (σ : Ω →ₐ[K₀] Ω).comp (σ.symm : Ω →ₐ[K₀] Ω) = AlgHom.id K₀ Ω := AlgEquiv.comp_symm σ
      rw [hc, map_id']

theorem kerRd_map (σ : Ω ≃ₐ[K₀] Ω) (h : Polynomial Ω) :
    kerRd (E.baseChange Ω) (h.map (σ : Ω →+* Ω)) =
      (kerRd (E.baseChange Ω) h).map (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω)) := by
  unfold kerRd
  rw [AddMonoidHom.map_closure, image_kerPts]

end Galois

section Gamma0

variable {K₀ Ω : Type u} [Field K₀] [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [DecidableEq Ω] [Algebra K₀ Ω]
  (E : WeierstrassCurve K₀) [E.IsElliptic] (M' : ℕ) [NeZero M']

def gamma0Rd (h : ↥M'.primeFactors → Polynomial Ω) : AddSubgroup (E.baseChange Ω).toAffine.Point :=
  ⨆ p ∈ (Finset.univ : Finset ↥M'.primeFactors), kerRd (E.baseChange Ω) (h p)

omit [IsAlgClosed Ω] [CharZero Ω] [E.IsElliptic] [NeZero M'] in
theorem gamma0Rd_map (σ : Ω ≃ₐ[K₀] Ω) (h : ↥M'.primeFactors → Polynomial Ω) :
    gamma0Rd E M' (fun p => (h p).map (σ : Ω →+* Ω)) =
      (gamma0Rd E M' h).map (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω)) := by
  unfold gamma0Rd
  simp only [AddSubgroup.map_iSup, kerRd_map]

theorem isAddCyclic_gamma0Rd_and_natCard (h : ↥M'.primeFactors → Polynomial Ω)
    (hh : ∀ p : ↥M'.primeFactors, IsGamma0PowAt (E.baseChange Ω) (p : ℕ) (M'.factorization (p : ℕ)) (h p)) :
    IsAddCyclic (gamma0Rd E M' h) ∧ Nat.card (gamma0Rd E M' h) = M' := by
  have hM' : M' ≠ 0 := NeZero.ne M'
  have key := isAddCyclic_biSup_and_natCard (G := (E.baseChange Ω).toAffine.Point)
    (Finset.univ : Finset ↥M'.primeFactors) (fun p => kerRd (E.baseChange Ω) (h p))
    (fun p => (p : ℕ) ^ M'.factorization (p : ℕ))
    (fun p _ => pow_pos (Nat.prime_of_mem_primeFactors p.2).pos _)
    (fun p _ => by
      haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
      exact (ModularCurve.IsGamma0PowAt.isAddCyclic_closure_and_natCard_eq_pow (E.baseChange Ω) (p : ℕ)
        (Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors p.2).ne_zero) _ (h p) (hh p)).1)
    (fun p _ => by
      haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
      exact (ModularCurve.IsGamma0PowAt.isAddCyclic_closure_and_natCard_eq_pow (E.baseChange Ω) (p : ℕ)
        (Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors p.2).ne_zero) _ (h p) (hh p)).2)
    (fun p _ p' _ hpp' => by
      apply Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors p.2) (Nat.prime_of_mem_primeFactors p'.2)
      exact fun heq => hpp' (Subtype.ext heq))
  refine ⟨key.1, key.2.trans ?_⟩
  rw [Finset.prod_coe_sort M'.primeFactors (fun p : ℕ => p ^ M'.factorization p)]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hM']
  rw [Finsupp.prod, Nat.support_factorization]

end Gamma0

end P2M.LevelReading
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_levelReading_baseChange_of_isAlgClosed_rigidDataH1Pow.P2M P2MW.S_ModularCurve_FullLevel_Diamond_exists_levelReading_baseChange_of_isAlgClosed_rigidDataH1Pow.P2M.LevelReading"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_levelReading_baseChange_of_isAlgClosed_rigidDataH1Pow.P2M"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_levelReading_baseChange_of_isAlgClosed_rigidDataH1Pow.P2M P2MW.S_ModularCurve_FullLevel_Diamond_exists_levelReading_baseChange_of_isAlgClosed_rigidDataH1Pow.P2M.LevelReading"

namespace P2M
namespace LevelReading

section Gamma1

variable {K₀ Ω : Type u} [Field K₀] [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [DecidableEq Ω] [Algebra K₀ Ω]
  (E : WeierstrassCurve K₀) [E.IsElliptic]

theorem gamma1_reading {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) {D : LevelPData Ω}
    (hD : IsGamma1Point (E.baseChange Ω) ℓ D) :
    ∃ hP : (E.baseChange Ω).toAffine.Nonsingular D.xP D.yP,
      ℓ • WeierstrassCurve.Affine.Point.some D.xP D.yP hP = 0 ∧
      WeierstrassCurve.Affine.Point.some D.xP D.yP hP ≠ 0 := by
  have hP : (E.baseChange Ω).toAffine.Nonsingular D.xP D.yP :=
    ((E.baseChange Ω).toAffine.equation_iff_nonsingular).mp hD.equation_P
  have hn : ((ℓ : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
  have hpre : ((E.baseChange Ω).preΨ' ℓ).eval D.xP = 0 := by
    rw [← WeierstrassCurve.preΨ_ofNat]; exact hD.preΨ_P
  obtain ⟨h1, h2⟩ := (WeierstrassCurve.Affine.Point.eval_prePsi_eq_zero_iff_smul_eq_zero_and_two_smul_ne_zero
    (E.baseChange Ω) hn hP).mp hpre
  refine ⟨hP, h1, ?_⟩
  intro h0; apply h2; rw [h0, smul_zero]

theorem rd_mem_gamma0Rd_of_isGamma1Link (M' : ℕ) [NeZero M'] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓM' : ℓ ∣ M')
    (h : ↥M'.primeFactors → Polynomial Ω)
    (hh : ∀ p : ↥M'.primeFactors, IsGamma0PowAt (E.baseChange Ω) (p : ℕ) (M'.factorization (p : ℕ)) (h p))
    {D : LevelPData Ω} (hD : IsGamma1Point (E.baseChange Ω) ℓ D)
    (hlink : IsGamma1Link (E.baseChange Ω) ℓ M' h D) :
    rd (E.baseChange Ω) D.xP D.yP ∈ gamma0Rd E M' h := by
  classical
  have hM0 : M' ≠ 0 := NeZero.ne M'
  have hmem : ℓ ∈ M'.primeFactors := Nat.mem_primeFactors.mpr ⟨hℓ, hℓM', hM0⟩
  obtain ⟨hP, hℓP, hP0⟩ := gamma1_reading E hℓ hℓ3 hD
  rw [rd_of_nonsingular _ hP]

  have hk1 : 1 ≤ M'.factorization ℓ := (Nat.Prime.dvd_iff_one_le_factorization hℓ hM0).mp hℓM'
  set k : ℕ := M'.factorization ℓ with hk
  set n : ℕ := ℓ ^ (k - 1) with hn
  have hdvd : h ⟨ℓ, hmem⟩ ∣ inLineMulPoly (E.baseChange Ω) ℓ n D.xP := hlink hmem
  have hhl : IsGamma0PowAt (E.baseChange Ω) ℓ k (h ⟨ℓ, hmem⟩) := hh ⟨ℓ, hmem⟩
  have hℓ2 : 2 ≤ ℓ := by omega
  have hpk2 : ℓ ^ k ≠ 2 := by
    intro h2
    have h3 : ℓ ≤ ℓ ^ k := Nat.le_self_pow (by omega) ℓ
    omega
  have hcg : (E.baseChange Ω).IsCyclicGenKernel ℓ k (h ⟨ℓ, hmem⟩) :=
    (ModularCurve.isGamma0PowAt_of_pow_ne_two (E.baseChange Ω) hpk2 (h ⟨ℓ, hmem⟩)).1 hhl

  have hmonic := hcg.monic
  have hnat : (h ⟨ℓ, hmem⟩).natDegree = Nat.totient (ℓ ^ k) / 2 :=
    le_antisymm hcg.natDegree_le (Polynomial.le_natDegree_of_ne_zero (by rw [hcg.coeff_eq_one]; exact one_ne_zero))
  have hdegpos : 0 < (h ⟨ℓ, hmem⟩).natDegree := by
    rw [hnat, Nat.totient_prime_pow hℓ (by omega)]
    have h1 : 1 ≤ ℓ ^ (k - 1) := Nat.one_le_pow _ _ hℓ.pos
    have h2 : 2 ≤ ℓ ^ (k - 1) * (ℓ - 1) :=
      calc 2 ≤ 1 * (ℓ - 1) := by omega
        _ ≤ ℓ ^ (k - 1) * (ℓ - 1) := Nat.mul_le_mul_right _ h1
    omega
  have hdeg0 : (h ⟨ℓ, hmem⟩).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero]; exact_mod_cast hdegpos.ne'
  obtain ⟨xG, hxG⟩ := IsAlgClosed.exists_root (h ⟨ℓ, hmem⟩) hdeg0
  have hxG0 : (h ⟨ℓ, hmem⟩).eval xG = 0 := hxG

  have hpre : ((E.baseChange Ω).preΨ' (ℓ ^ k)).eval xG = 0 := by
    have hd : h ⟨ℓ, hmem⟩ ∣ (E.baseChange Ω).preΨ' (ℓ ^ k) := by
      have h1 := dvd_trans (dvd_mul_right (h ⟨ℓ, hmem⟩) ((E.baseChange Ω).preΨ (ℓ ^ (k - 1)))) hcg.mul_preΨ_dvd
      rw [← WeierstrassCurve.preΨ_ofNat]
      exact_mod_cast h1
    exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hd hxG0
  have hnΩ : ((ℓ ^ k : ℕ) : Ω) ≠ 0 := by exact_mod_cast pow_ne_zero k hℓ.ne_zero
  obtain ⟨yG, hG, hGtor, hG2⟩ :=
    WeierstrassCurve.exists_nonsingular_nsmul_eq_zero_and_two_nsmul_ne_zero_of_eval_prePsi_eq_zero
      (E.baseChange Ω) (ℓ ^ k) hnΩ xG hpre

  have hGmem : WeierstrassCurve.Affine.Point.some xG yG hG ∈ gamma0Rd E M' h := by
    have h1 : WeierstrassCurve.Affine.Point.some xG yG hG ∈ kerRd (E.baseChange Ω) (h ⟨ℓ, hmem⟩) :=
      AddSubgroup.subset_closure ⟨xG, yG, hG, rfl, hxG0⟩
    have h2 : kerRd (E.baseChange Ω) (h ⟨ℓ, hmem⟩) ≤ gamma0Rd E M' h := by
      unfold gamma0Rd
      exact le_iSup₂_of_le (f := fun p _ => kerRd (E.baseChange Ω) (h p)) ⟨ℓ, hmem⟩ (Finset.mem_univ _) le_rfl
    exact h2 h1

  have heval : (inLineMulPoly (E.baseChange Ω) ℓ n D.xP).eval xG = 0 :=
    Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdvd hxG0
  rw [inLineMulPoly, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at heval
  obtain ⟨a, ha, hfa⟩ := heval
  rw [Finset.mem_Icc] at ha
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C] at hfa

  set P := WeierstrassCurve.Affine.Point.some D.xP D.yP hP with hPdef
  set G := WeierstrassCurve.Affine.Point.some xG yG hG with hGdef

  have haP : (a : ℤ) • P ≠ 0 := by
    intro h0
    rw [natCast_zsmul] at h0
    have hdvda : addOrderOf P ∣ a := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0
    have hdvdl : addOrderOf P ∣ ℓ := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hℓP
    have hcop : Nat.Coprime a ℓ :=
      ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).symm
    have h1 : addOrderOf P ∣ 1 := by rw [← hcop]; exact Nat.dvd_gcd hdvda hdvdl
    exact hP0 (AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp h1))
  have hψa : ((E.baseChange Ω).ψ a).evalEval D.xP D.yP ≠ 0 := fun h0 =>
    haP ((WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff (E.baseChange Ω) hP a).mpr h0)
  have hΨa : ((E.baseChange Ω).ΨSq a).eval D.xP ≠ 0 := by
    rw [← WeierstrassCurve.Affine.evalEval_psi_sq (E.baseChange Ω) hP.1 a]
    exact pow_ne_zero 2 hψa

  have hnG : (n : ℤ) • G ≠ 0 := by
    intro h0
    have hΨn : ((E.baseChange Ω).ΨSq n).eval xG = 0 :=
      WeierstrassCurve.Affine.Point.eval_psiSq_eq_zero_of_smul_eq_zero hG h0
    have hΦn : ((E.baseChange Ω).Φ n).eval xG = 0 := by
      rw [hΨn, mul_zero, sub_zero] at hfa
      exact (mul_eq_zero.mp hfa).resolve_right hΨa
    obtain ⟨u, v, huv⟩ := WeierstrassCurve.isCoprime_Phi_PsiSq (E.baseChange Ω) (n : ℤ)
    have := congrArg (Polynomial.eval xG) huv
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, hΦn, hΨn, mul_zero, mul_zero, add_zero,
      Polynomial.eval_one] at this
    exact zero_ne_one this
  have hψn : ((E.baseChange Ω).ψ n).evalEval xG yG ≠ 0 := fun h0 =>
    hnG ((WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff (E.baseChange Ω) hG n).mpr h0)
  have hΨn0 : ((E.baseChange Ω).ΨSq n).eval xG ≠ 0 := by
    rw [← WeierstrassCurve.Affine.evalEval_psi_sq (E.baseChange Ω) hG.1 n]
    exact pow_ne_zero 2 hψn

  obtain ⟨y', h', hnGeq⟩ := WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div (E.baseChange Ω) hG hψn
  have hline : InLine (E.baseChange Ω) ℓ D.xP (((E.baseChange Ω).Φ n).eval xG / ((E.baseChange Ω).ΨSq n).eval xG) := by
    refine ⟨a, ha.1, ha.2, ?_⟩
    rw [div_mul_eq_mul_div, div_eq_iff hΨn0]
    linear_combination hfa
  have hmemP := ModularCurve.InLine.some_mem_zmultiples_some_of_nonsingular (E.baseChange Ω) ℓ hP h' hline

  rw [← hnGeq, AddSubgroup.mem_zmultiples_iff] at hmemP
  obtain ⟨m, hm⟩ := hmemP

  have hℓm : ¬ (ℓ : ℤ) ∣ m := by
    rintro ⟨c, rfl⟩
    apply hnG
    rw [← hm, mul_comm, ← smul_smul, natCast_zsmul, hℓP, smul_zero]
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  obtain ⟨u, v, huv⟩ := (Irreducible.coprime_iff_not_dvd hprime.irreducible).mpr hℓm

  have hPeq : P = v • ((n : ℤ) • G) := by
    calc P = (1 : ℤ) • P := (one_zsmul P).symm
      _ = (u * (ℓ : ℤ) + v * m) • P := by rw [huv]
      _ = v • ((n : ℤ) • G) := by
          rw [add_zsmul, mul_zsmul, mul_zsmul, natCast_zsmul, hℓP, zsmul_zero, zero_add, hm]
  rw [hPeq]
  exact AddSubgroup.zsmul_mem _ (AddSubgroup.zsmul_mem _ hGmem _) _

end Gamma1
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_levelReading_baseChange_of_isAlgClosed_rigidDataH1Pow.P2M P2MW.S_ModularCurve_FullLevel_Diamond_exists_levelReading_baseChange_of_isAlgClosed_rigidDataH1Pow.P2M.LevelReading"

end P2M.LevelReading
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_levelReading_baseChange_of_isAlgClosed_rigidDataH1Pow.P2M P2MW.S_ModularCurve_FullLevel_Diamond_exists_levelReading_baseChange_of_isAlgClosed_rigidDataH1Pow.P2M.LevelReading"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_levelReading_baseChange_of_isAlgClosed_rigidDataH1Pow.P2M P2MW.S_ModularCurve_FullLevel_Diamond_exists_levelReading_baseChange_of_isAlgClosed_rigidDataH1Pow.P2M.LevelReading"

open P2M.LevelReading in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg3 : 3 ≤ ℓg) (hℓgM' : ℓg ∣ M')
    (A : Type u) [CommRing A]

    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)

    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [DecidableEq Ω] [Algebra A Ω]
    (K₀ : Type u) [Field K₀] [Algebra A K₀] [Algebra K₀ Ω] [IsScalarTower A K₀ Ω]
    (E : WeierstrassCurve K₀) [E.IsElliptic] :
    ∃ Θ : ((((ModularCurve.gamma0PowComponent A M' hM).prod
        ((ModularCurve.gamma1Component A ℓg hℓ).prod (WeierstrassCurve.DrinfeldGlobal.levelComponent A 𝒢 q 𝒯))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem)))).obj Ω →
        ((E.baseChange Ω).toAffine.Point ×
          ((E.baseChange Ω).toAffine.Point × (E.baseChange Ω).toAffine.Point)) ×
          AddSubgroup (E.baseChange Ω).toAffine.Point,
      ∀ β : ((((ModularCurve.gamma0PowComponent A M' hM).prod
        ((ModularCurve.gamma1Component A ℓg hℓ).prod (WeierstrassCurve.DrinfeldGlobal.levelComponent A 𝒢 q 𝒯))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem)))).obj Ω,
        ((((ModularCurve.gamma0PowComponent A M' hM).prod
        ((ModularCurve.gamma1Component A ℓg hℓ).prod (WeierstrassCurve.DrinfeldGlobal.levelComponent A 𝒢 q 𝒯))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem)))).IsLevel (E.baseChange Ω) β →

        (ℓg • (Θ β).1.1 = 0 ∧ (Θ β).1.1 ≠ 0 ∧ (Θ β).1.1 ∈ (Θ β).2) ∧

        (q • (Θ β).1.2.1 = 0 ∧ q • (Θ β).1.2.2 = 0 ∧
          ∀ a b : ℤ, a • (Θ β).1.2.1 + b • (Θ β).1.2.2 = 0 → (q : ℤ) ∣ a ∧ (q : ℤ) ∣ b) ∧

        (IsAddCyclic (Θ β).2 ∧ Nat.card (Θ β).2 = M') ∧

        (∀ σ : Ω ≃ₐ[K₀] Ω,
          Θ (((((ModularCurve.gamma0PowComponent A M' hM).prod
        ((ModularCurve.gamma1Component A ℓg hℓ).prod (WeierstrassCurve.DrinfeldGlobal.levelComponent A 𝒢 q 𝒯))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem)))).map
              ((σ : Ω →ₐ[K₀] Ω).restrictScalars A) β) =
            ((WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω) (Θ β).1.1,
              (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω) (Θ β).1.2.1,
                WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω) (Θ β).1.2.2)),
              ((Θ β).2).map (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω)))) := by
  classical
  obtain ⟨Θq, hΘq⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_basisReading_levelComponent_map_of_isAlgClosed q (Fact.out : q.Prime).pos
      A 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hCO Ω K₀ E
  refine ⟨fun β => ((rd (E.baseChange Ω) β.2.1.xP β.2.1.yP, Θq β.2.2), gamma0Rd E M' β.1), ?_⟩
  intro β hβ
  set h : ↥M'.primeFactors → Polynomial Ω := β.1 with hhdef
  set D : LevelPData Ω := β.2.1 with hDdef
  set x : RawDrinfeldPair Ω := β.2.2 with hxdef
  have hh : ∀ p : ↥M'.primeFactors, IsGamma0PowAt (E.baseChange Ω) (p : ℕ) (M'.factorization (p : ℕ)) (h p) := hβ.1.1
  have hD : IsGamma1Point (E.baseChange Ω) ℓg D := hβ.1.2.1
  have hx : RawDrinfeldPair.IsLevel 𝒢 q (E.baseChange Ω) x := hβ.1.2.2
  have hlink : IsGamma1Link (E.baseChange Ω) ℓg M' h D := hβ.2
  obtain ⟨hP, hℓP, hP0⟩ := gamma1_reading E hℓg hℓg3 hD
  obtain ⟨hbasis, hgal⟩ := hΘq x hx
  refine ⟨?_, hbasis, isAddCyclic_gamma0Rd_and_natCard E M' h hh, ?_⟩
  · dsimp only
    refine ⟨?_, ?_, rd_mem_gamma0Rd_of_isGamma1Link E M' hℓg hℓg3 hℓgM' h hh hD hlink⟩
    · rw [rd_of_nonsingular _ hP]; exact hℓP
    · rw [rd_of_nonsingular _ hP]; exact hP0
  · intro σ
    show ((rd (E.baseChange Ω) ((σ : Ω →ₐ[K₀] Ω) D.xP) ((σ : Ω →ₐ[K₀] Ω) D.yP),
        Θq (𝒯.map ((σ : Ω →ₐ[K₀] Ω).restrictScalars A) x)),
        gamma0Rd E M' (fun p => (h p).map (σ : Ω →+* Ω))) = _
    rw [rd_map, hgal σ, gamma0Rd_map]

end S_ModularCurve_FullLevel_Diamond_exists_levelReading_baseChange_of_isAlgClosed_rigidDataH1Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_exists_levelReading_baseChange_of_isAlgClosed_rigidDataH1Pow (solution)
