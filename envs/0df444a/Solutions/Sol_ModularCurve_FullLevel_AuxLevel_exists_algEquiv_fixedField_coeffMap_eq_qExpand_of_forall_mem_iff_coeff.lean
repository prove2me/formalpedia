-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.exists_algEquiv_fixedField_coeffMap_eq_qExpand_of_forall_mem_iff_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/086c194d-33ba-5e71-8420-0930ac7ecb83

import Mathlib
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_exists_ringEquiv_laurentBaseChange_coe_eq_coeffMap_of_forall_mem_iff_forall_coeff_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_algEquiv_fixedField_coeffMap_eq_qExpand_of_forall_mem_iff_coeff
p2m_attr_erase "instance" "ModularCurve.FullLevel.SemistableCovering.instAlgebraSS ModularCurve.FullLevel.SemistableCovering.instFieldIg ModularCurve.FullLevel.SemistableCovering.instFieldSS ModularCurve.FullLevel.SemistableCovering.instAlgebraIg AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.Gamma0Pair.isElliptic DrinfeldCurve.instAlgebraCoordRing DrinfeldCurve.instCommRingCoordRing"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.FullLevel.SemistableCovering.mk.sizeOf_spec ModularCurve.FullLevel.SemistableCovering.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow"
p2m_attr_erase "simp" "ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.JZeroSemistableSpecialization.mk.sizeOf_spec ModularCurve.JZeroSemistableSpecialization.mk.injEq AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit AlgebraicCurve.SemilinearAut.coe_admissibleMap AlgebraicCurve.SemilinearAut.gluingMap_apply AlgebraicCurve.GluedPic0.glueMap_mk AlgebraicCurve.SemilinearAut.nodePerm_apply AlgebraicCurve.SemilinearAut.baseAutUnitsHom_apply ModularCurve.jqNModC_one ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply AlgebraicCurve.ComponentChart.comap_placeMap AlgebraicCurve.ComponentChart.comap_residue_apply AlgebraicCurve.ComponentChart.coe_comapIntegersEquiv AlgebraicCurve.ComponentChart.comapResidue_apply AlgebraicCurve.ComponentChart.comap_integers AlgebraicCurve.ComponentChart.comap_dom AlgebraicCurve.ComponentChart.mem_comapIntegers AlgebraicCurve.Annulus.comap_param AlgebraicCurve.Annulus.comap_dom AlgebraicCurve.Annulus.comap_modulus AlgebraicCurve.ComponentChart.mem_comap_integers AlgebraicCurve.ComponentChart.comap_nodes ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.RegularProlongation.coe_integersEquiv"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 12800000

noncomputable section

p2m_open "ModularCurve~coeffMap_qExpand ModularCurve.FullLevel CongruenceSubgroup IntermediateField HahnSeries"
open scoped MatrixGroups

namespace W1ISO

abbrev en (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

theorem exists_emb_bar {n : ℕ} (hn : 0 < n) {z : AlgebraicClosure ℚ} (hz : IsPrimitiveRoot z n) :
    ∃ ι₀ : AlgebraicClosure ℚ →+* ℂ, ι₀ z = en n := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  haveI : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr hn0⟩
  have hmin : minpoly ℚ z = Polynomial.cyclotomic n ℚ :=
    (Polynomial.cyclotomic_eq_minpoly_rat hz hn).symm
  have hroot : en n ∈ (minpoly ℚ z).rootSet ℂ := by
    rw [hmin, Polynomial.mem_rootSet]
    refine ⟨Polynomial.cyclotomic_ne_zero n ℚ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact (Polynomial.isRoot_cyclotomic_iff.mpr (Complex.isPrimitiveRoot_exp n hn0)).eq_zero
  rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly ℂ z] at hroot
  obtain ⟨ψ, hψ⟩ := hroot
  exact ⟨ψ.toRingHom, hψ⟩

theorem exists_emb_sub (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) {n : ℕ} (hn : 0 < n) {ξ : ↥k₀}
    (hξ : IsPrimitiveRoot ξ n) : ∃ ι : ↥k₀ →+* ℂ, ι ξ = en n := by
  have hξ' : IsPrimitiveRoot (ξ : AlgebraicClosure ℚ) n :=
    hξ.map_of_injective (f := algebraMap ↥k₀ (AlgebraicClosure ℚ)) Subtype.val_injective
  obtain ⟨ι₀, hι₀⟩ := exists_emb_bar hn hξ'
  exact ⟨ι₀.comp (algebraMap ↥k₀ (AlgebraicClosure ℚ)), hι₀⟩

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) [NeZero n]
    (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext m
  by_cases hdvd : (n : ℤ) ∣ m
  · obtain ⟨m', rfl⟩ := hdvd
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hdvd, qExpand_coeff_of_not_dvd n _ hdvd, map_zero]

theorem coeffMap_algebraMap_coeffEmb (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (x : LaurentSeries ℚ) :
    coeffMap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) (coeffEmb ↥k₀ x) = coeffEmb (AlgebraicClosure ℚ) x := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) x

theorem mem_fixedField_closure_iff {F E : Type*} [Field F] [Field E] [Algebra F E] (S : Set (E ≃ₐ[F] E)) (w : E) :
    w ∈ fixedField (Subgroup.closure S) ↔ ∀ τ ∈ S, τ w = w := by
  rw [mem_fixedField_iff]
  constructor
  · intro h τ hτ
    exact h τ (Subgroup.subset_closure hτ)
  · intro h τ hτ
    induction hτ using Subgroup.closure_induction with
    | mem σ hσ => exact h σ hσ
    | one => rfl
    | mul σ σ' _ _ h1 h2 => rw [AlgEquiv.mul_apply, h2, h1]
    | inv σ _ h1 =>
        rw [AlgEquiv.aut_inv]
        conv_lhs => rw [← h1]
        exact σ.symm_apply_apply w

section Transport

variable {L L' : Type} [Field L] [CharZero L] [Field L'] [CharZero L']

theorem coeffMap_mem_laurentBaseChange_of_mem (σ : L →+* L') (F : IntermediateField ℚ (LaurentSeries ℚ))
    {f : LaurentSeries L} (hf : f ∈ laurentBaseChange L F) :
    coeffMap σ f ∈ laurentBaseChange L' F := by
  rw [mem_laurentBaseChange_iff] at hf
  induction hf using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨c, rfl⟩ | ⟨x, hx, rfl⟩
      · rw [algebraMap_laurentSeries_eq_single, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
        exact IntermediateField.algebraMap_mem _ _
      · have : coeffMap σ (coeffEmb L x) = coeffEmb L' x := by
          rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
          exact coeffMap_congr (Subsingleton.elim _ _) x
        rw [this]
        exact coeffEmb_mem_laurentBaseChange L' hx
  | one => rw [map_one]; exact one_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

def transport (σ : L ≃+* L') (F : IntermediateField ℚ (LaurentSeries ℚ)) :
    ↥(laurentBaseChange L F) ≃+* ↥(laurentBaseChange L' F) where
  toFun f := ⟨coeffMap (σ : L →+* L') (f : LaurentSeries L),
    coeffMap_mem_laurentBaseChange_of_mem (σ : L →+* L') F f.2⟩
  invFun g := ⟨coeffMap (σ.symm : L' →+* L) (g : LaurentSeries L'),
    coeffMap_mem_laurentBaseChange_of_mem (σ.symm : L' →+* L) F g.2⟩
  left_inv f := by
    apply Subtype.ext
    change coeffMap (σ.symm : L' →+* L) (coeffMap (σ : L →+* L') (f : LaurentSeries L)) = _
    rw [coeffMap_coeffMap]
    have hid : (σ.symm : L' →+* L).comp (σ : L →+* L') = RingHom.id L := by ext x; simp
    rw [hid, coeffMap_id]
  right_inv g := by
    apply Subtype.ext
    change coeffMap (σ : L →+* L') (coeffMap (σ.symm : L' →+* L) (g : LaurentSeries L')) = _
    rw [coeffMap_coeffMap]
    have hid : (σ : L →+* L').comp (σ.symm : L' →+* L) = RingHom.id L' := by ext x; simp
    rw [hid, coeffMap_id]
  map_mul' f g := Subtype.ext (by simp)
  map_add' f g := Subtype.ext (by simp)

@[scoped simp] theorem coe_transport (σ : L ≃+* L') (F : IntermediateField ℚ (LaurentSeries ℚ))
    (f : ↥(laurentBaseChange L F)) :
    ((transport σ F f : ↥(laurentBaseChange L' F)) : LaurentSeries L') = coeffMap (σ : L →+* L') (f : LaurentSeries L) :=
  rfl

end Transport

section Constants

variable (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))

def subCongr : ↥k₀ ≃+* ↥k₀.toSubfield where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem subtype_comp_subCongr :
    k₀.toSubfield.subtype.comp (subCongr k₀ : ↥k₀ →+* ↥k₀.toSubfield) = algebraMap ↥k₀ (AlgebraicClosure ℚ) := by
  ext x; rfl

end Constants

section Rho

variable {k : Type} [Field k] (ℓ : ℕ) [NeZero ℓ]
  (B K : IntermediateField k (LaurentSeries k)) (K₀ : IntermediateField k ↥K)
  (hBK : ∀ x : LaurentSeries k, x ∈ B → qExpand k ℓ x ∈ K)
  (hK₀ : ∀ w : ↥K, w ∈ K₀ ↔ ∃ x : LaurentSeries k, x ∈ B ∧ ((w : ↥K) : LaurentSeries k) = qExpand k ℓ x)

def rho : ↥B →ₐ[k] ↥K₀ where
  toFun x := ⟨⟨qExpand k ℓ (x : LaurentSeries k), hBK x x.2⟩, (hK₀ _).mpr ⟨x, x.2, rfl⟩⟩
  map_one' := Subtype.ext (Subtype.ext (by simp))
  map_mul' x y := Subtype.ext (Subtype.ext (by simp))
  map_zero' := Subtype.ext (Subtype.ext (by simp))
  map_add' x y := Subtype.ext (Subtype.ext (by simp))
  commutes' c := by
    apply Subtype.ext; apply Subtype.ext
    change qExpand k ℓ (algebraMap k (LaurentSeries k) c) = algebraMap k (LaurentSeries k) c
    rw [algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply, qExpand_C]

theorem coe_rho (x : ↥B) : (((rho ℓ B K K₀ hBK hK₀ x : ↥K₀) : ↥K) : LaurentSeries k) = qExpand k ℓ x := rfl

theorem rho_bijective : Function.Bijective (rho ℓ B K K₀ hBK hK₀) := by
  constructor
  · intro x y h
    have h' := congrArg (fun z : ↥K₀ => ((z : ↥K) : LaurentSeries k)) h
    simp only [coe_rho] at h'
    exact Subtype.ext (qExpand_injective ℓ h')
  · intro w
    obtain ⟨x, hx, hw⟩ := (hK₀ (w : ↥K)).mp w.2
    exact ⟨⟨x, hx⟩, Subtype.ext (Subtype.ext hw.symm)⟩

def rhoE : ↥B ≃ₐ[k] ↥K₀ := AlgEquiv.ofBijective _ (rho_bijective ℓ B K K₀ hBK hK₀)

theorem coe_rhoE_symm (w : ↥K₀) :
    qExpand k ℓ (((rhoE ℓ B K K₀ hBK hK₀).symm w : ↥B) : LaurentSeries k) = ((w : ↥K) : LaurentSeries k) := by
  have h := (rhoE ℓ B K K₀ hBK hK₀).apply_symm_apply w
  have h' := congrArg (fun z : ↥K₀ => ((z : ↥K) : LaurentSeries k)) h
  simpa only [rhoE, AlgEquiv.ofBijective_apply, coe_rho] using h'

end Rho

end W1ISO
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_algEquiv_fixedField_coeffMap_eq_qExpand_of_forall_mem_iff_coeff.W1ISO"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_algEquiv_fixedField_coeffMap_eq_qExpand_of_forall_mem_iff_coeff.W1ISO"

p2m_open "ModularCurve~coeffMap_qExpand ModularCurve.FullLevel CongruenceSubgroup IntermediateField HahnSeries P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_algEquiv_fixedField_coeffMap_eq_qExpand_of_forall_mem_iff_coeff.W1ISO"
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 3200000 in
set_option maxHeartbeats 12800000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (K : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hK : K = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (G : Subgroup (↥K ≃ₐ[↥k₀] ↥K))
    (hG : G = Subgroup.closure {τ : ↥K ≃ₐ[↥k₀] ↥K | ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧
      γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ})
    (K₀ : IntermediateField ↥k₀ ↥K) (hK₀ : K₀ = IntermediateField.fixedField G) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),

      (∀ f : ↥(fieldBar q M'), f ∈ F₀ ↔ ∀ n : ℤ, ∃ c : ↥k₀,
        ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n = ((c : ↥k₀) : AlgebraicClosure ℚ)) →
    ∃ φ : ↥K₀ ≃ₐ[↥k₀] ↥F₀,

      (∀ f : ↥K₀, coeffMap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) (((f : ↥K)) : LaurentSeries ↥k₀) =
        ModularCurve.qExpand (AlgebraicClosure ℚ) ℓ (((φ f : ↥F₀) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ))) ∧

      (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
        (hgK : ModularCurve.qExpand ↥k₀ ℓ (coeffEmb ↥k₀ g) ∈ K) (hgK₀ : (⟨_, hgK⟩ : ↥K) ∈ K₀),
        ((φ ⟨⟨_, hgK⟩, hgK₀⟩ : ↥F₀) : ↥(fieldBar q M')) =
          IntermediateField.inclusion hle
            ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩) := by
  letI instk₀ : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
  intro F₀ hF₀

  let incl : ↥k₀ →+* AlgebraicClosure ℚ := algebraMap ↥k₀ (AlgebraicClosure ℚ)
  let B : IntermediateField ↥k₀ (LaurentSeries ↥k₀) :=
    laurentBaseChange ↥k₀ (xHFunctionField (q ^ 2 * M') (levelH q M'))
  have hqℓpos : 0 < q * ℓ := Nat.mul_pos (Fact.out : q.Prime).pos (Fact.out : ℓ.Prime).pos

  have hι : ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)) := by
    obtain ⟨ι, hι⟩ := exists_emb_sub k₀ hqℓpos hξ
    refine ⟨ι, ?_⟩
    rw [hι, en, Nat.cast_mul]

  obtain ⟨hBK, hfix⟩ :=
    ModularCurve.FullLevel.AuxLevel.forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand_of_exists_ringHom
      q hq M' hqM' ℓ hℓ3 hℓq hℓM' ↥k₀ ξ hξ hι K hK
  have hK₀' : ∀ w : ↥K, w ∈ K₀ ↔ ∃ x : LaurentSeries ↥k₀, x ∈ B ∧ ((w : ↥K) : LaurentSeries ↥k₀) = qExpand ↥k₀ ℓ x := by
    intro w
    rw [hK₀, hG, mem_fixedField_closure_iff, ← hfix w]
    constructor
    · intro h γ hγ hγ0 τ hτ
      exact h τ ⟨γ, hγ, hγ0, hτ⟩
    · rintro h τ ⟨γ, hγ, hγ0, hτ⟩
      exact h γ hγ hγ0 τ hτ

  let ρ : ↥B ≃ₐ[↥k₀] ↥K₀ := rhoE ℓ B K K₀ hBK hK₀'

  let k₀' : Subfield (AlgebraicClosure ℚ) := k₀.toSubfield
  let σ : ↥k₀ ≃+* ↥k₀' := subCongr k₀
  have hζ : IsPrimitiveRoot (σ (ξ ^ ℓ)) q := by
    have h1 : IsPrimitiveRoot (ξ ^ ℓ) q := hξ.pow hqℓpos (by ring)
    exact h1.map_of_injective σ.injective
  let F₀' : Subfield ↥(fieldBar q M') := F₀.toSubfield
  have hF₀' : ∀ f : ↥(fieldBar q M'), f ∈ F₀' ↔
      ∀ n : ℤ, ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ k₀' := by
    intro f
    change f ∈ F₀.toSubfield ↔ _
    rw [IntermediateField.mem_toSubfield, hF₀ f]
    refine forall_congr' fun n => ?_
    constructor
    · rintro ⟨c, hc⟩
      rw [hc]
      exact c.2
    · intro h
      exact ⟨⟨_, h⟩, rfl⟩
  obtain ⟨e, he⟩ :=
    ModularCurve.FullLevel.exists_ringEquiv_laurentBaseChange_coe_eq_coeffMap_of_forall_mem_iff_forall_coeff_mem
      q hq M' hqM' k₀' (σ (ξ ^ ℓ)) hζ F₀' hF₀'

  let castF : ↥F₀' ≃+* ↥F₀ :=
    { toFun := fun y => ⟨y.1, y.2⟩
      invFun := fun y => ⟨y.1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }

  let Φ : ↥K₀ ≃+* ↥F₀ :=
    ρ.symm.toRingEquiv.trans
      (((transport σ (xHFunctionField (q ^ 2 * M') (levelH q M'))).trans e).trans castF)

  have hΦ : ∀ w : ↥K₀, (((Φ w : ↥F₀) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap incl (((ρ.symm w : ↥B)) : LaurentSeries ↥k₀) := by
    intro w
    change (((e (transport σ _ (ρ.symm w)) : ↥F₀') : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = _
    rw [he, coe_transport, coeffMap_coeffMap, subtype_comp_subCongr]
  have hΦ1 : ∀ w : ↥K₀, coeffMap incl (((w : ↥K)) : LaurentSeries ↥k₀) =
      qExpand (AlgebraicClosure ℚ) ℓ (((Φ w : ↥F₀) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) := by
    intro w
    rw [hΦ, ← coeffMap_qExpand, coe_rhoE_symm]

  have hΦc : ∀ c : ↥k₀, Φ (algebraMap ↥k₀ ↥K₀ c) = algebraMap ↥k₀ ↥F₀ c := by
    intro c
    apply Subtype.ext; apply Subtype.ext
    have e1 : ((((algebraMap ↥k₀ ↥K₀ c : ↥K₀) : ↥K)) : LaurentSeries ↥k₀) = algebraMap ↥k₀ (LaurentSeries ↥k₀) c :=
      rfl
    have e2 : ((((algebraMap ↥k₀ ↥F₀ c : ↥F₀) : ↥(fieldBar q M'))) : LaurentSeries (AlgebraicClosure ℚ)) =
        algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (incl c) := rfl
    have h1 := hΦ1 (algebraMap ↥k₀ ↥K₀ c)
    rw [e1, algebraMap_laurentSeries_eq_single, coeffMap_single, ← HahnSeries.C_apply,
      ← qExpand_C ℓ (incl c)] at h1
    have h3 := qExpand_injective ℓ h1
    rw [e2, ← h3, algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
  refine ⟨AlgEquiv.ofRingEquiv (f := Φ) hΦc, ?_, ?_⟩
  · intro w
    exact hΦ1 w
  · intro g hg hgK hgK₀
    apply Subtype.ext
    have h1 := hΦ1 ⟨⟨_, hgK⟩, hgK₀⟩
    change coeffMap incl (qExpand ↥k₀ ℓ (coeffEmb ↥k₀ g)) = _ at h1
    rw [coeffMap_qExpand, coeffMap_algebraMap_coeffEmb] at h1
    have h2 := qExpand_injective ℓ h1
    rw [IntermediateField.coe_inclusion]
    exact h2.symm

end S_ModularCurve_FullLevel_AuxLevel_exists_algEquiv_fixedField_coeffMap_eq_qExpand_of_forall_mem_iff_coeff
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_algEquiv_fixedField_coeffMap_eq_qExpand_of_forall_mem_iff_coeff (solution)
