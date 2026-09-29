-- Prove2me | solution 1 for ModularCurve.JZero.absLogHeight_chordVec_eq_evalAt_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/4f593fc1-da3b-569c-ac73-9bcb703705f3

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_Height_inv_finrank_mul_logHeight_inclusion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_absLogHeight_chordVec_eq_evalAt_of_ne
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 480000
set_option maxHeartbeats 6400000

open AlgebraicCurve ModularCurve

noncomputable section

namespace P2MCard18a2a4be

section PlaceLemmas

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem evalAt_sub_of_mem (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_sub, v.algebraMap_evalAt hv (sub_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_sub]
  rfl

theorem evalAt_smul_of_mem (hv : v.IsRational) (a : K) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt (a • f) = a * v.evalAt f := by
  rw [Algebra.smul_def, v.evalAt_mul_of_mem hv (v.algebraMap_mem' a) hf, v.evalAt_algebraMap_eq]

theorem ord_eq_zero_of_evalAt_ne_zero (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : v.evalAt f ≠ 0) : v.ord f = 0 := by
  have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ ≠ 0 := by
    intro h0
    apply h
    apply v.algebraMap_residueField_injective
    rw [v.algebraMap_evalAt hv hf, h0, map_zero]
  obtain ⟨u, hu⟩ := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hres
  have := v.ord_coe_unit u
  rwa [hu] at this

theorem evalAt_inv_of_ord_eq_zero (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    v.evalAt f⁻¹ = (v.evalAt f)⁻¹ := by
  have hfm : f ∈ v.toValuationSubring := v.mem_toValuationSubring_of_ord_nonneg_alt hf h.ge
  have hfi : f⁻¹ ∈ v.toValuationSubring :=
    v.mem_toValuationSubring_of_ord_nonneg_alt (inv_ne_zero hf) (by rw [v.ord_inv, h, neg_zero])
  have key : v.evalAt f * v.evalAt f⁻¹ = 1 := by
    rw [← v.evalAt_mul_of_mem hv hfm hfi, mul_inv_cancel₀ hf, v.evalAt_one]
  exact (eq_inv_of_mul_eq_one_right key)

theorem smul_mem_of_mem (a : K) {f : F} (hf : f ∈ v.toValuationSubring) :
    a • f ∈ v.toValuationSubring := by
  rw [Algebra.smul_def]
  exact mul_mem (v.algebraMap_mem' a) hf

theorem mk_smul_eq (a : K) {f : F} (hf : f ∈ v.toValuationSubring) :
    (⟨a • f, smul_mem_of_mem v a hf⟩ : v.toValuationSubring)
      = ⟨algebraMap K F a, v.algebraMap_mem' a⟩ * ⟨f, hf⟩ :=
  Subtype.ext (Algebra.smul_def a f)

theorem exists_evalAt_ne_zero_of_one_mem_span (hv : v.IsRational) {ι : Type*} (s : ι → F)
    (hmem : ∀ i, s i ∈ v.toValuationSubring)
    (h1 : (1 : F) ∈ Submodule.span K (Set.range s)) : ∃ j, v.evalAt (s j) ≠ 0 := by
  by_contra hall0
  have hall : ∀ j, v.evalAt (s j) = 0 := fun j => by
    by_contra h; exact hall0 ⟨j, h⟩
  have key : ∀ f ∈ Submodule.span K (Set.range s),
      ∃ hf : f ∈ v.toValuationSubring, IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = 0 := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      refine ⟨hmem j, ?_⟩
      rw [← v.algebraMap_evalAt hv (hmem j), hall j, map_zero]
    | zero =>
      exact ⟨zero_mem _, by
        rw [show (⟨(0 : F), zero_mem _⟩ : v.toValuationSubring) = 0 from rfl, RingHom.map_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨hx, hx0⟩ := hx
      obtain ⟨hy, hy0⟩ := hy
      refine ⟨add_mem hx hy, ?_⟩
      have : (⟨x + y, add_mem hx hy⟩ : v.toValuationSubring) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [this, RingHom.map_add, hx0, hy0, add_zero]
    | smul a x _ hx =>
      obtain ⟨hx, hx0⟩ := hx
      exact ⟨smul_mem_of_mem v a hx, by rw [mk_smul_eq v a hx, RingHom.map_mul, hx0, mul_zero]⟩
  obtain ⟨h1m, h10⟩ := key 1 h1
  rw [show (⟨(1 : F), h1m⟩ : v.toValuationSubring) = 1 from rfl, RingHom.map_one] at h10
  exact one_ne_zero h10

end PlaceLemmas

section Geometry

variable (N : ℕ) [NeZero N] {r : ℕ}

theorem embDivisor_apply_of_ne {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hw : w ≠ cuspInftyBar N) : embDivisor N w = 0 := by
  classical
  rw [embDivisor, Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hw), smul_zero]

theorem embDivisor_nonneg (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    0 ≤ embDivisor N w := by
  classical
  rw [embDivisor, Finsupp.smul_apply, Finsupp.single_apply]
  split_ifs <;> simp

theorem one_mem_riemannRochSpace_embDivisor :
    (1 : modularFunctionFieldBar N) ∈ riemannRochSpace (embDivisor N) := by
  rw [mem_riemannRochSpace_iff]
  intro v
  right
  rw [Place.ord_one, neg_nonpos]
  exact embDivisor_nonneg N v

variable {N}
variable {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s)
  {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (hw : w ≠ cuspInftyBar N)

include hs in
theorem emb_ne_zero (i : Fin r) : s i ≠ 0 := hs.1.ne_zero i

include hs hw in

theorem emb_ord_nonneg (i : Fin r) : 0 ≤ w.ord (s i) := by
  have hmem : s i ∈ riemannRochSpace (embDivisor N) := by
    rw [← hs.2]; exact Submodule.subset_span ⟨i, rfl⟩
  rcases (mem_riemannRochSpace_iff.mp hmem) w with h | h
  · exact absurd h (emb_ne_zero hs i)
  · rwa [embDivisor_apply_of_ne N hw, neg_zero] at h

include hs hw in
theorem emb_mem (i : Fin r) : s i ∈ w.toValuationSubring :=
  w.mem_toValuationSubring_of_ord_nonneg_alt (emb_ne_zero hs i) (emb_ord_nonneg hs hw i)

include hs hw in

theorem emb_exists_evalAt_ne_zero (hrat : w.IsRational) : ∃ j : Fin r, w.evalAt (s j) ≠ 0 :=
  exists_evalAt_ne_zero_of_one_mem_span w hrat s (emb_mem hs hw)
    (by rw [hs.2]; exact one_mem_riemannRochSpace_embDivisor N)

include hs hw in

theorem emb_ord_pivot (hrat : w.IsRational) (hr : 0 < r) : w.ord (s (pivotIndex s w hr)) = 0 := by
  classical
  have hex : ∃ i : Fin r, ∀ j : Fin r, w.ord (s i) ≤ w.ord (s j) := by
    haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => w.ord (s i)) Finset.univ_nonempty
    exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩
  have hpiv : pivotIndex s w hr = Classical.choose hex := by
    rw [pivotIndex, dif_pos hex]
  obtain ⟨j, hj⟩ := emb_exists_evalAt_ne_zero hs hw hrat
  have hj0 : w.ord (s j) = 0 := ord_eq_zero_of_evalAt_ne_zero w hrat (emb_mem hs hw j) hj
  have hle : w.ord (s (pivotIndex s w hr)) ≤ 0 := by
    rw [hpiv, ← hj0]; exact Classical.choose_spec hex j
  exact le_antisymm hle (emb_ord_nonneg hs hw _)

include hs hw in

theorem emb_evalAt_chordFun_eq (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hr : 0 < r) :
    (fun p : Fin r × Fin r => w.evalAt (evalVec s v p.1 • s p.2 - evalVec s v p.2 • s p.1))
      = w.evalAt (s (pivotIndex s w hr)) • chordVec s v w := by
  have hrat : w.IsRational :=
    (Place.isRational_iff_deg_eq_one w).mpr (deg_eq_one_modularFunctionFieldBar N w)
  set k := pivotIndex s w hr with hk
  have hk0 : w.ord (s k) = 0 := emb_ord_pivot hs hw hrat hr
  set c := w.evalAt (s k) with hc
  have hc0 : c ≠ 0 := w.evalAt_ne_zero_of_ord_eq_zero hrat (emb_ne_zero hs k) hk0
  have hkinv_mem : (s k)⁻¹ ∈ w.toValuationSubring :=
    w.mem_toValuationSubring_of_ord_nonneg_alt (inv_ne_zero (emb_ne_zero hs k))
      (by rw [w.ord_inv, hk0, neg_zero])
  have hkinv : w.evalAt (s k)⁻¹ = c⁻¹ := evalAt_inv_of_ord_eq_zero w hrat (emb_ne_zero hs k) hk0
  have hev : ∀ i, evalVec s w i = w.evalAt (s i) * c⁻¹ := by
    intro i
    rw [evalVec]
    simp only [dif_pos hr]
    rw [w.evalAt_mul_of_mem hrat (emb_mem hs hw i) hkinv_mem, hkinv]
  funext p
  rw [Pi.smul_apply, chordVec, smul_eq_mul,
    evalAt_sub_of_mem w hrat (smul_mem_of_mem w _ (emb_mem hs hw _)) (smul_mem_of_mem w _ (emb_mem hs hw _)),
    evalAt_smul_of_mem w hrat _ (emb_mem hs hw _), evalAt_smul_of_mem w hrat _ (emb_mem hs hw _), hev, hev]
  field_simp

end Geometry

section AbsHeight

theorem normLogHeight_eq_of_le (E E' : IntermediateField ℚ (AlgebraicClosure ℚ)) (h : E ≤ E')
    [FiniteDimensional ℚ E] [FiniteDimensional ℚ E'] {ι : Type} [Fintype ι]
    (x : ι → AlgebraicClosure ℚ) (hx : ∀ i, x i ∈ E) :
    (Module.finrank ℚ E : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, hx i⟩ : E))
      = (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, h (hx i)⟩ : E')) :=
  (Height.inv_finrank_mul_logHeight_inclusion (K := E) (L := E') h (fun i => (⟨x i, hx i⟩ : E))).symm

theorem absLogHeight_eq_of_mem {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ)
    (E' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E'] (h : ∀ i, x i ∈ E') :
    absLogHeight x = (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, h i⟩ : E')) := by
  have hle : IntermediateField.adjoin ℚ (Set.range x) ≤ E' :=
    IntermediateField.adjoin_le_iff.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
  haveI := finiteDimensional_adjoin_range x
  exact normLogHeight_eq_of_le _ E' hle x (fun i => IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩)

theorem absLogHeight_smul {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ)
    {c : AlgebraicClosure ℚ} (hc : c ≠ 0) : absLogHeight (c • x) = absLogHeight x := by
  set E' : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.adjoin ℚ (insert c (Set.range x)) with hE'
  haveI : FiniteDimensional ℚ E' :=
    IntermediateField.finiteDimensional_adjoin fun y _ =>
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic y).isIntegral
  have hcE : c ∈ E' := IntermediateField.subset_adjoin ℚ _ (Set.mem_insert c _)
  have hx' : ∀ i, x i ∈ E' := fun i =>
    IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem c ⟨i, rfl⟩)
  have hcx : ∀ i, (c • x) i ∈ E' := fun i => by
    rw [Pi.smul_apply, smul_eq_mul]; exact mul_mem hcE (hx' i)
  rw [absLogHeight_eq_of_mem (c • x) E' hcx, absLogHeight_eq_of_mem x E' hx']
  congr 1
  convert Height.logHeight_smul_eq_logHeight (fun i => (⟨x i, hx' i⟩ : E')) (c := ⟨c, hcE⟩) ?_ using 2
  all_goals first
    | exact fun h0 => hc (by simpa using congrArg Subtype.val h0)
    | (funext i; apply Subtype.ext; simp [Pi.smul_apply, smul_eq_mul])

end AbsHeight

end P2MCard18a2a4be

end

open P2MCard18a2a4be in
theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (v w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hw : w ≠ cuspInftyBar N) :
    absLogHeight (chordVec s v w)
      = absLogHeight (fun p : Fin r × Fin r => w.evalAt (evalVec s v p.1 • s p.2 - evalVec s v p.2 • s p.1)) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    congr 1
    funext p
    exact p.1.elim0
  · have hrat : w.IsRational :=
      (Place.isRational_iff_deg_eq_one w).mpr (deg_eq_one_modularFunctionFieldBar N w)
    rw [emb_evalAt_chordFun_eq hs hw v hr, absLogHeight_smul _
      (w.evalAt_ne_zero_of_ord_eq_zero hrat (emb_ne_zero hs _) (emb_ord_pivot hs hw hrat hr))]

end S_ModularCurve_JZero_absLogHeight_chordVec_eq_evalAt_of_ne
end P2MW
export P2MW.S_ModularCurve_JZero_absLogHeight_chordVec_eq_evalAt_of_ne (solution)
