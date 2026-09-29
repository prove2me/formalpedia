-- Prove2me | solution 1 for ModularCurve.exists_place_of_emb
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/aa026c6d-f9d9-5692-a82a-9066f00dedf5

import Mathlib
import Definitions.Def_ModularCurve_EMD
import Definitions.Def_HahnSeries_RamificationBound
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_hasRamBound
import Theorems.Thm_HahnSeries_hasRamBound_natDegree_factorial_of_isRoot
import Theorems.Thm_ModularCurve_adjoin_jBar_jNBar_eq_top
import Theorems.Thm_HahnSeries_mem_puiseuxRamSubfield_iff
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_place_of_emb
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open ModularCurve AlgebraicCurve IntermediateField Polynomial

namespace S12P

variable (N : ℕ) [NeZero N]

abbrev jb : ↥(modularFunctionFieldBar N) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩

abbrev jNb : ↥(modularFunctionFieldBar N) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩

theorem eval₂_Phi_jb_jNb (data : ModularPolynomialData N) :
    data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldBar N)) (jb N)) (jNb N)
      = 0 := by
  apply Subtype.ext
  have hval : ((modularFunctionFieldBar N).toSubfield.subtype).comp
      (Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldBar N)) (jb N))
      = (coeffEmb (AlgebraicClosure ℚ)).comp evalAtJ := by
    refine Polynomial.ringHom_ext (fun z => by simp) ?_
    show ((Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldBar N)) (jb N) X :
        ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (evalAtJ X)
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, evalAtJ_X]
  have h0 := congrArg (coeffEmb (AlgebraicClosure ℚ)) data.eval_eq_zero
  rw [map_zero, Polynomial.hom_eval₂, ← hval] at h0
  rw [ZeroMemClass.coe_zero, ← h0]
  show ((modularFunctionFieldBar N).toSubfield.subtype) _ = _
  rw [Polynomial.hom_eval₂]
  rfl

section Hahn

variable {e : ℕ}

theorem hasRamBound_of_one (he : 0 < e) {y : HahnSeries ℚ (AlgebraicClosure ℚ)}
    (hy : HahnSeries.HasRamBound 1 y) : HahnSeries.HasRamBound e y := by
  intro g hg
  obtain ⟨k, hk⟩ := hy hg
  refine ⟨k * e, ?_⟩
  simp only [Nat.cast_one, div_one] at hk
  have he' : (e : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  rw [← hk]; push_cast; field_simp

theorem hasRamBound_C (a : AlgebraicClosure ℚ) :
    HahnSeries.HasRamBound 1 (HahnSeries.C a : HahnSeries ℚ (AlgebraicClosure ℚ)) := by
  intro g hg
  have : g ∈ ({0} : Set ℚ) := HahnSeries.support_single_subset (a := (0 : ℚ)) (r := a) hg
  rw [Set.mem_singleton_iff] at this
  exact ⟨0, by simp [this]⟩

theorem hasRamBound_C_add_single (a : AlgebraicClosure ℚ) :
    HahnSeries.HasRamBound 1
      (HahnSeries.C a + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ)) := by
  intro g hg
  rcases (HahnSeries.support_add_subset (x := HahnSeries.C a)
      (y := HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ))) hg with h | h
  · exact hasRamBound_C a h
  · have : g ∈ ({1} : Set ℚ) :=
      HahnSeries.support_single_subset (a := (1 : ℚ)) (r := (1 : AlgebraicClosure ℚ)) h
    rw [Set.mem_singleton_iff] at this
    exact ⟨1, by simp [this]⟩

theorem algebraMap_hahn_eq_C (a : AlgebraicClosure ℚ) :
    algebraMap (AlgebraicClosure ℚ) (HahnSeries ℚ (AlgebraicClosure ℚ)) a = HahnSeries.C a := by
  rw [HahnSeries.algebraMap_apply']; simp

theorem eval₂RingHom_mem_puiseuxRamSubfield_one (y : HahnSeries ℚ (AlgebraicClosure ℚ))
    (hy : HahnSeries.HasRamBound 1 y) (q : Polynomial ℤ) :
    Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ))) y q
      ∈ HahnSeries.puiseuxRamSubfield (AlgebraicClosure ℚ) (e := 1) one_pos := by
  rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range]
  refine Subfield.sum_mem _ (fun i _ => Subfield.mul_mem _ ?_ (Subfield.pow_mem _ ?_ _))
  · exact intCast_mem _ _
  · exact (HahnSeries.mem_puiseuxRamSubfield_iff one_pos).mpr hy

end Hahn

theorem exists_forall_hasRamBound (j₀ : AlgebraicClosure ℚ)
    (ψ : ↥(modularFunctionFieldBar N) →ₐ[AlgebraicClosure ℚ] HahnSeries ℚ (AlgebraicClosure ℚ))
    (hψ : ψ (jb N) = HahnSeries.C j₀ + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ)) :
    ∃ e : ℕ, 0 < e ∧ ∀ z, HahnSeries.HasRamBound e (ψ z) := by
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData N

  set P : Polynomial (HahnSeries ℚ (AlgebraicClosure ℚ)) :=
    data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ)))
      (HahnSeries.C j₀ + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ))) with hPdef
  have hPmonic : P.Monic := data.monic.map _
  have hP0 : P ≠ 0 := hPmonic.ne_zero
  have hcoeff : ∀ i : ℕ, HahnSeries.HasRamBound 1 (P.coeff i) := by
    intro i
    rw [hPdef, Polynomial.coeff_map]
    exact (HahnSeries.mem_puiseuxRamSubfield_iff one_pos).mp
      (eval₂RingHom_mem_puiseuxRamSubfield_one _ (hasRamBound_C_add_single j₀) _)

  have hroot : P.IsRoot (ψ (jNb N)) := by
    rw [Polynomial.IsRoot, hPdef, Polynomial.eval_map, ← hψ]
    have hcomp : Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ))) (ψ (jb N))
        = (ψ.toRingHom).comp (Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldBar N)) (jb N)) := by
      refine Polynomial.ringHom_ext (fun z => by simp) ?_
      simp
    rw [hcomp]
    have h := (Polynomial.hom_eval₂ data.Φ
      (Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldBar N)) (jb N)) ψ.toRingHom (jNb N)).symm
    rw [eval₂_Phi_jb_jNb N data, map_zero] at h
    simpa using h
  have hbN := HahnSeries.hasRamBound_natDegree_factorial_of_isRoot hP0 hcoeff hroot
  set e := P.natDegree.factorial with hedef
  have he : 0 < e := Nat.factorial_pos _
  refine ⟨e, he, ?_⟩

  let S := HahnSeries.puiseuxRamSubfield (AlgebraicClosure ℚ) (e := e) he
  have hS : ∀ y, y ∈ S ↔ HahnSeries.HasRamBound e y := fun y => HahnSeries.mem_puiseuxRamSubfield_iff he
  let T : IntermediateField (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    (S.comap ψ.toRingHom).toIntermediateField (fun a => by
      show ψ (algebraMap (AlgebraicClosure ℚ) _ a) ∈ S
      rw [ψ.commutes, hS, algebraMap_hahn_eq_C]
      exact hasRamBound_of_one he (hasRamBound_C a))
  have hjb : jb N ∈ T := by
    show ψ (jb N) ∈ S
    rw [hψ, hS]
    exact hasRamBound_of_one he (hasRamBound_C_add_single j₀)
  have hjNb : jNb N ∈ T := by
    show ψ (jNb N) ∈ S
    rw [hS]; exact hbN
  have htop := ModularCurve.adjoin_jBar_jNBar_eq_top (AlgebraicClosure ℚ) N
  have hle : (⊤ : IntermediateField (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) ≤ T := by
    rw [← htop, IntermediateField.adjoin_le_iff]
    intro z hz
    rcases hz with rfl | rfl
    · exact hjb
    · exact hjNb
  intro z
  exact (hS _).mp (hle IntermediateField.mem_top)

theorem mem_iff_ord_nonneg (w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N))
    {x : ↥(modularFunctionFieldBar N)} (hx : x ≠ 0) :
    x ∈ w.toValuationSubring ↔ 0 ≤ w.ord x := by
  rw [Place.mem_iff_adicValuation_le_one, Place.ord, neg_nonneg,
    WithZero.log_le_iff_le_exp (w.adicValuation_ne_zero hx), WithZero.exp_zero]

theorem induces_unique
    {ψ : ↥(modularFunctionFieldBar N) →ₐ[AlgebraicClosure ℚ] HahnSeries ℚ (AlgebraicClosure ℚ)}
    {w w' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)}
    (hw : Induces ψ w) (hw' : Induces ψ w') : w = w' := by
  obtain ⟨g, hg, h⟩ := hw
  obtain ⟨g', hg', h'⟩ := hw'
  have key : ∀ x, 0 ≤ w.ord x ↔ 0 ≤ w'.ord x := by
    intro x
    have hx := h x
    rw [← h' x] at hx

    constructor
    · intro h0
      have : 0 ≤ (w'.ord x : ℚ) * g' := by rw [← hx]; positivity
      exact_mod_cast nonneg_of_mul_nonneg_left this hg'
    · intro h0
      have : 0 ≤ (w.ord x : ℚ) * g := by rw [hx]; positivity
      exact_mod_cast nonneg_of_mul_nonneg_left this hg
  apply Place.ext
  ext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp [zero_mem]
  · rw [mem_iff_ord_nonneg N w hx, mem_iff_ord_nonneg N w' hx, key]

theorem pos_ord_of_induces (j₀ : AlgebraicClosure ℚ) (ψ : Emb N j₀)
    {w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)} (hw : Induces ψ.1 w) :
    0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) j₀) := by
  obtain ⟨g, hg, h⟩ := hw
  have hx := h (jBar N - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) j₀)
  rw [map_sub, ψ.2, AlgHom.commutes, algebraMap_hahn_eq_C, add_sub_cancel_left,
    HahnSeries.order_single (one_ne_zero)] at hx
  have : (0 : ℚ) < (w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) j₀) : ℚ) * g := by
    rw [hx]; exact_mod_cast one_pos
  exact_mod_cast pos_of_mul_pos_left this hg.le

theorem exists_induces (j₀ : AlgebraicClosure ℚ) (ψ : Emb N j₀) :
    ∃ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), Induces ψ.1 w := by
  obtain ⟨e, he, hall⟩ := exists_forall_hasRamBound N j₀ ψ.1 ψ.2
  have hnt : ∃ x : ↥(modularFunctionFieldBar N), (ψ.1 x).order ≠ 0 := by
    refine ⟨jBar N - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) j₀, ?_⟩
    rw [map_sub, ψ.2, AlgHom.commutes, algebraMap_hahn_eq_C, add_sub_cancel_left,
      HahnSeries.order_single (one_ne_zero)]
    exact one_ne_zero
  obtain ⟨w, g, hg, h⟩ := AlgebraicCurve.Place.exists_ord_mul_eq_order_of_hasRamBound ψ.1 he hall hnt
  exact ⟨w, g, hg, h⟩

end S12P

end

open ModularCurve AlgebraicCurve in
theorem solution (N : ℕ) [NeZero N] (j₀ : AlgebraicClosure ℚ)
    (ψ : Emb N j₀) :
    ∃ (w : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) (g : ℚ), 0 < g ∧
      ∀ x : ↥(modularFunctionFieldBar N), (w.ord x : ℚ) * g = (ψ.1 x).order := by
  obtain ⟨w, g, hg, h⟩ := S12P.exists_induces N j₀ ψ
  exact ⟨w, g, hg, h⟩

end S_ModularCurve_exists_place_of_emb
end P2MW
export P2MW.S_ModularCurve_exists_place_of_emb (solution)
