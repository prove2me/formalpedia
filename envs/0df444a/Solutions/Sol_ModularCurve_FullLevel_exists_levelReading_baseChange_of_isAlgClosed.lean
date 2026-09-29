-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_levelReading_baseChange_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/f2c24dda-80ec-5262-8dab-d44c2c4ea6be

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Theorems.Thm_ModularCurve_IsLevelPStructure_exists_nsmul_eq_zero_and_dvd_of_zsmul_add_zsmul_eq_zero
import Theorems.Thm_ModularCurve_IsGamma0PowAt_isAddCyclic_closure_and_natCard_eq_pow
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_basisReading_levelComponent_map_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_levelReading_baseChange_of_isAlgClosed
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

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
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_levelReading_baseChange_of_isAlgClosed.P2M P2MW.S_ModularCurve_FullLevel_exists_levelReading_baseChange_of_isAlgClosed.P2M.LevelReading"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_levelReading_baseChange_of_isAlgClosed.P2M"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_levelReading_baseChange_of_isAlgClosed.P2M P2MW.S_ModularCurve_FullLevel_exists_levelReading_baseChange_of_isAlgClosed.P2M.LevelReading"

open P2M.LevelReading in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (A : Type u) [CommRing A]

    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
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
    ∃ Θ : ((ModularCurve.gamma0PowComponent A M' hM).prod
        ((ModularCurve.levelPComponent A ℓ hℓ).prod (WeierstrassCurve.DrinfeldGlobal.levelComponent A 𝒢 q 𝒯))).obj Ω →
        (((E.baseChange Ω).toAffine.Point × (E.baseChange Ω).toAffine.Point) ×
          ((E.baseChange Ω).toAffine.Point × (E.baseChange Ω).toAffine.Point)) ×
          AddSubgroup (E.baseChange Ω).toAffine.Point,
      ∀ β : ((ModularCurve.gamma0PowComponent A M' hM).prod
        ((ModularCurve.levelPComponent A ℓ hℓ).prod (WeierstrassCurve.DrinfeldGlobal.levelComponent A 𝒢 q 𝒯))).obj Ω,
        ((ModularCurve.gamma0PowComponent A M' hM).prod
          ((ModularCurve.levelPComponent A ℓ hℓ).prod
            (WeierstrassCurve.DrinfeldGlobal.levelComponent A 𝒢 q 𝒯))).IsLevel (E.baseChange Ω) β →

        (ℓ • (Θ β).1.1.1 = 0 ∧ ℓ • (Θ β).1.1.2 = 0 ∧
          ∀ a b : ℤ, a • (Θ β).1.1.1 + b • (Θ β).1.1.2 = 0 → (ℓ : ℤ) ∣ a ∧ (ℓ : ℤ) ∣ b) ∧

        (q • (Θ β).1.2.1 = 0 ∧ q • (Θ β).1.2.2 = 0 ∧
          ∀ a b : ℤ, a • (Θ β).1.2.1 + b • (Θ β).1.2.2 = 0 → (q : ℤ) ∣ a ∧ (q : ℤ) ∣ b) ∧

        (IsAddCyclic (Θ β).2 ∧ Nat.card (Θ β).2 = M') ∧

        (∀ σ : Ω ≃ₐ[K₀] Ω,
          Θ (((ModularCurve.gamma0PowComponent A M' hM).prod
              ((ModularCurve.levelPComponent A ℓ hℓ).prod
                (WeierstrassCurve.DrinfeldGlobal.levelComponent A 𝒢 q 𝒯))).map
              ((σ : Ω →ₐ[K₀] Ω).restrictScalars A) β) =
            (((WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω) (Θ β).1.1.1,
                WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω) (Θ β).1.1.2),
              (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω) (Θ β).1.2.1,
                WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω) (Θ β).1.2.2)),
              ((Θ β).2).map (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K₀] Ω)))) := by
  classical

  obtain ⟨Θq, hΘq⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_basisReading_levelComponent_map_of_isAlgClosed q (Fact.out : q.Prime).pos
      A 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hCO Ω K₀ E

  set Lc : ModularCurve.LevelComponent A := (ModularCurve.gamma0PowComponent A M' hM).prod
    ((ModularCurve.levelPComponent A ℓ hℓ).prod (WeierstrassCurve.DrinfeldGlobal.levelComponent A 𝒢 q 𝒯)) with hLc
  have hℓ2 : ℓ ≠ 2 := by omega
  refine ⟨fun β => (((rd (E.baseChange Ω) β.2.1.xP β.2.1.yP, rd (E.baseChange Ω) β.2.1.xQ β.2.1.yQ), Θq β.2.2),
    gamma0Rd E M' β.1), ?_⟩
  intro β hβ

  set h : ↥M'.primeFactors → Polynomial Ω := β.1 with hhdef
  set D : LevelPData Ω := β.2.1 with hDdef
  set x : RawDrinfeldPair Ω := β.2.2 with hxdef
  have hh : ∀ p : ↥M'.primeFactors, IsGamma0PowAt (E.baseChange Ω) (p : ℕ) (M'.factorization (p : ℕ)) (h p) := hβ.1
  have hD : IsLevelPStructure (E.baseChange Ω) ℓ D := hβ.2.1
  have hx : RawDrinfeldPair.IsLevel 𝒢 q (E.baseChange Ω) x := hβ.2.2

  obtain ⟨hP, hQ, hℓP, hℓQ, hind⟩ :=
    ModularCurve.IsLevelPStructure.exists_nsmul_eq_zero_and_dvd_of_zsmul_add_zsmul_eq_zero (E.baseChange Ω) ℓ hℓ2 D hD
  obtain ⟨hbasis, hgal⟩ := hΘq x hx
  refine ⟨?_, hbasis, isAddCyclic_gamma0Rd_and_natCard E M' h hh, ?_⟩
  · dsimp only
    rw [rd_of_nonsingular _ hP, rd_of_nonsingular _ hQ]
    exact ⟨hℓP, hℓQ, hind⟩
  · intro σ

    show (((rd (E.baseChange Ω) ((σ : Ω →ₐ[K₀] Ω) D.xP) ((σ : Ω →ₐ[K₀] Ω) D.yP),
        rd (E.baseChange Ω) ((σ : Ω →ₐ[K₀] Ω) D.xQ) ((σ : Ω →ₐ[K₀] Ω) D.yQ)),
        Θq (𝒯.map ((σ : Ω →ₐ[K₀] Ω).restrictScalars A) x)),
        gamma0Rd E M' (fun p => (h p).map (σ : Ω →+* Ω))) = _
    rw [rd_map, rd_map, hgal σ, gamma0Rd_map]

end S_ModularCurve_FullLevel_exists_levelReading_baseChange_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_levelReading_baseChange_of_isAlgClosed (solution)
