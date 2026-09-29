-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/969c6ba8-9912-5aaa-9064-cfd389feab85

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AdditiveJacquet
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal

noncomputable section

namespace TranslatedJacquetStabilisation

section

open IsDedekindDomain NumberField Topology
open LanglandsTunnell.CubicInduction

private theorem exists_forall_valued_sub_one_le_imp_eq_one_of_isLocallyConstant_single (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    ∃ f : ℕ, ∀ u : (v.adicCompletion ℚ)ˣ,
      Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(f : ℤ) - 1) → χ u = 1 := by
  have hO : IsOpen {u : (v.adicCompletion ℚ)ˣ | χ u = 1} := hχ.isOpen_fiber 1
  obtain ⟨U, hU, hUO⟩ := (Units.isEmbedding_val₀ (G₀ := v.adicCompletion ℚ)).isInducing.isOpen_iff.mp hO
  have h1U : (1 : v.adicCompletion ℚ) ∈ U := by
    have h1 : (1 : (v.adicCompletion ℚ)ˣ) ∈ Units.val ⁻¹' U := by
      rw [hUO]
      simp only [Set.mem_setOf_eq, map_one]
    simpa using h1
  obtain ⟨j, hj⟩ := exists_setOf_valued_sub_le_subset_of_isOpen v hU h1U
  refine ⟨j.toNat, fun u hu => ?_⟩
  have hle : WithZero.exp (-(j.toNat : ℤ) - 1) ≤ WithZero.exp (-j) := by
    rw [WithZero.exp_le_exp]
    have := Int.self_le_toNat j
    omega
  have hmem : u ∈ Units.val ⁻¹' U := hj (le_trans hu hle)
  rw [hUO] at hmem
  exact hmem

private theorem exists_forall_valued_sub_one_le_imp_eq_one_of_isLocallyConstant (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hχ : ∀ i, IsLocallyConstant (χ i)) :
    ∃ f : ℕ, ∀ (i : Fin 3) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(f : ℤ) - 1) → χ i u = 1 := by
  choose f hf using fun i =>
    exists_forall_valued_sub_one_le_imp_eq_one_of_isLocallyConstant_single v (χ i) (hχ i)
  refine ⟨max (f 0) (max (f 1) (f 2)), fun i u hu => hf i u (le_trans hu ?_)⟩
  rw [WithZero.exp_le_exp]
  have hi : f i ≤ max (f 0) (max (f 1) (f 2)) := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hi' : (f i : ℤ) ≤ ((max (f 0) (max (f 1) (f 2)) : ℕ) : ℤ) := by exact_mod_cast hi
  omega

end

section

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction Filter Topology

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem isOpen_valued_le_exp (n : ℕ) :
    IsOpen {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (n : ℤ)} := by
  have h : {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (n : ℤ)}
      = {x : v.adicCompletion ℚ | Valued.v (x - 0) ≤ WithZero.exp (- -(n : ℤ))} := by
    simp only [sub_zero, neg_neg]
  rw [h]
  exact (isClopen_setOf_valued_sub_le v 0 (-(n : ℤ))).isOpen

private theorem exists_forall_valued_le_of_isCompact {S : Set (v.adicCompletion ℚ)} (hS : IsCompact S) :
    ∃ R : ℤ, ∀ x ∈ S, Valued.v x ≤ WithZero.exp R := by
  have hcov : S ⊆ ⋃ n : ℕ, {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (n : ℤ)} := by
    intro x _
    obtain ⟨n, hn⟩ := exists_valued_le_exp v x
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  have hdir : Directed (· ⊆ ·) fun n : ℕ => {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (n : ℤ)} := by
    intro a b
    refine ⟨max a b, fun x hx => ?_, fun x hx => ?_⟩
    · exact le_trans hx (WithZero.exp_le_exp.mpr (Nat.cast_le.mpr (le_max_left a b)))
    · exact le_trans hx (WithZero.exp_le_exp.mpr (Nat.cast_le.mpr (le_max_right a b)))
  obtain ⟨n, hn⟩ := hS.elim_directed_cover _ (isOpen_valued_le_exp v) hcov hdir
  exact ⟨n, fun x hx => hn hx⟩

private theorem exists_forall_apply_eq_zero_of_exp_lt {Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ}
    (hΦc : HasCompactSupport Φ) :
    ∃ R : ℤ, ∀ (q : Fin 3 → v.adicCompletion ℚ) (i : Fin 3), WithZero.exp R < Valued.v (q i) → Φ q = 0 := by
  have hK : IsCompact (tsupport Φ) := hΦc
  have hb : ∀ i : Fin 3, ∃ R : ℤ, ∀ q ∈ tsupport Φ, Valued.v (q i) ≤ WithZero.exp R := by
    intro i
    obtain ⟨R, hR⟩ := exists_forall_valued_le_of_isCompact v (hK.image (continuous_apply i))
    exact ⟨R, fun q hq => hR _ (Set.mem_image_of_mem _ hq)⟩
  choose R hR using hb
  have hRmax : ∀ j : Fin 3, R j ≤ max (R 0) (max (R 1) (R 2)) := by
    intro j
    fin_cases j <;> simp
  refine ⟨max (R 0) (max (R 1) (R 2)), fun q i hi => ?_⟩
  by_contra hq
  have hqs : q ∈ tsupport Φ := subset_tsupport Φ hq
  exact absurd ((hR i q hqs).trans (WithZero.exp_le_exp.mpr (hRmax i))) (not_le.mpr hi)

private theorem eventually_exp_lt_valued_div {n d : LocalGL3 v → v.adicCompletion ℚ} {g : LocalGL3 v}
    (hn : Continuous n)
    (hd : Continuous d) (hng : n g ≠ 0) (hdg : d g = 0) (R : ℤ) :
    ∀ᶠ h in 𝓝 g, d h ≠ 0 → WithZero.exp R < Valued.v (n h / d h) := by
  obtain ⟨t, ht0, ht⟩ := exists_valued_eq_exp v (-R)
  have h1 : ∀ᶠ h in 𝓝 g, Valued.v (n h) = Valued.v (n g) := (hn.tendsto g).eventually (eventually_valued_eq v hng)
  have h2 : ∀ᶠ h in 𝓝 g, Valued.v (d h) < Valued.v (t * n g) := by
    have hlim : Tendsto d (𝓝 g) (𝓝 0) := by simpa [hdg] using hd.tendsto g
    exact hlim.eventually (eventually_valued_lt v (mul_ne_zero ht0 hng))
  filter_upwards [h1, h2] with h hn' hd' hd0
  have hvd : Valued.v (d h) ≠ 0 := (Valuation.ne_zero_iff _).mpr hd0
  rw [Valuation.map_mul, ht] at hd'
  rw [map_div₀, hn', lt_div_iff₀ (lt_of_le_of_ne zero_le' hvd.symm)]
  calc WithZero.exp R * Valued.v (d h) < WithZero.exp R * (WithZero.exp (-R) * Valued.v (n g)) :=
        mul_lt_mul_of_pos_left hd' WithZero.exp_pos
    _ = Valued.v (n g) := by rw [← mul_assoc, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, one_mul]

private theorem eventually_cellSectionOf_eq_of_den {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ} {R : ℤ}
    (hR : ∀ (q : Fin 3 → v.adicCompletion ℚ) (i : Fin 3), WithZero.exp R < Valued.v (q i) → Φ q = 0) {g : LocalGL3 v}
    {n d : LocalGL3 v → v.adicCompletion ℚ} (i : Fin 3) (hn : Continuous n) (hd : Continuous d) (hng : n g ≠ 0)
    (hdg : d g = 0) (hratio : ∀ h, cellRatio v h i = n h / d h) (hden : ∀ h, h ∈ bigCell3 v → d h ≠ 0) :
    ∀ᶠ h in 𝓝 g, cellSectionOf v χ Φ h = cellSectionOf v χ Φ g := by
  have hg : g ∉ bigCell3 v := fun hmem => hden g hmem hdg
  rw [cellSectionOf_apply_of_notMem v χ Φ hg]
  filter_upwards [eventually_exp_lt_valued_div v hn hd hng hdg R] with h hh
  by_cases hhB : h ∈ bigCell3 v
  · rw [cellSectionOf_apply_of_mem v χ Φ hhB, hR (cellRatio v h) i (by rw [hratio]; exact hh (hden h hhB)), mul_zero]
  · exact cellSectionOf_apply_of_notMem v χ Φ hhB

private theorem isLocallyConstant_cellSectionOf {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (hχ : ∀ i, IsLocallyConstant (χ i)) {Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ} (hΦ : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) : IsLocallyConstant (cellSectionOf v χ Φ) := by
  obtain ⟨R, hR⟩ := exists_forall_apply_eq_zero_of_exp_lt v hΦc
  have hΦ' := hΦ
  rw [IsLocallyConstant.iff_eventually_eq] at hΦ' ⊢
  intro g
  by_cases hc : cornerEntry v g = 0
  · rcases exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero v hc with h21 | h22
    · exact eventually_cellSectionOf_eq_of_den v hR 0 (continuous_gl3Entry v 2 1) (continuous_cornerEntry v) h21 hc
        (fun h => rfl) (fun h hh => hh.1)
    · exact eventually_cellSectionOf_eq_of_den v hR 1 (continuous_gl3Entry v 2 2) (continuous_cornerEntry v) h22 hc
        (fun h => rfl) (fun h hh => hh.1)
  by_cases hl : lowerMinor v g = 0
  · exact eventually_cellSectionOf_eq_of_den v hR 2 (continuous_outerMinor v) (continuous_lowerMinor v)
      (outerMinor_ne_zero_of_lowerMinor_eq_zero v hc hl) hl (fun h => rfl) (fun h hh => hh.2)
  have hgB : g ∈ bigCell3 v := ⟨hc, hl⟩
  have hcA : ContinuousAt (cornerEntry v) g := (continuous_cornerEntry v).continuousAt
  have hlA : ContinuousAt (lowerMinor v) g := (continuous_lowerMinor v).continuousAt
  have hdA : ContinuousAt (gl3Det v) g := (continuous_gl3Det v).continuousAt
  have hmem : ∀ᶠ h in 𝓝 g, h ∈ bigCell3 v := by
    filter_upwards [hcA.eventually_ne hc, hlA.eventually_ne hl] with h hch hlh
    exact ⟨hch, hlh⟩
  have hval : ∀ᶠ h in 𝓝 g, cellValue v χ h = cellValue v χ g := by
    have hq0 : gl3Det v g / lowerMinor v g ≠ 0 := div_ne_zero (gl3Det_ne_zero v g) hl
    have hq1 : lowerMinor v g / cornerEntry v g ≠ 0 := div_ne_zero hl hc
    have e0 : ∀ᶠ h in nhds g,
        LanglandsTunnell.TateLocal.charExt (χ 0) (gl3Det v h / lowerMinor v h)
          = LanglandsTunnell.TateLocal.charExt (χ 0) (gl3Det v g / lowerMinor v g) :=
      (hdA.div hlA hl).eventually (eventually_charExt_eq v (χ 0) (hχ 0) hq0)
    have e1 : ∀ᶠ h in nhds g,
        LanglandsTunnell.TateLocal.charExt (χ 1) (lowerMinor v h / cornerEntry v h)
          = LanglandsTunnell.TateLocal.charExt (χ 1) (lowerMinor v g / cornerEntry v g) :=
      (hlA.div hcA hc).eventually (eventually_charExt_eq v (χ 1) (hχ 1) hq1)
    have e2 : ∀ᶠ h in nhds g, LanglandsTunnell.TateLocal.charExt (χ 2) (cornerEntry v h)
      = LanglandsTunnell.TateLocal.charExt (χ 2) (cornerEntry v g) :=
      hcA.eventually (eventually_charExt_eq v (χ 2) (hχ 2) hc)
    have e3 : ∀ᶠ h in nhds g, ‖gl3Det v h / lowerMinor v h‖ = ‖gl3Det v g / lowerMinor v g‖ :=
      (hdA.div hlA hl).eventually (eventually_norm_eq v hq0)
    have e4 : ∀ᶠ h in nhds g, ‖cornerEntry v h‖ = ‖cornerEntry v g‖ := hcA.eventually (eventually_norm_eq v hc)
    filter_upwards [e0, e1, e2, e3, e4] with h h0 h1 h2 h3 h4
    simp only [cellValue, h0, h1, h2, h3, h4]
  have hrA : ContinuousAt (cellRatio v) g := by
    rw [continuousAt_pi]
    intro i
    fin_cases i
    · exact ((continuous_gl3Entry v 2 1).continuousAt).div hcA hc
    · exact ((continuous_gl3Entry v 2 2).continuousAt).div hcA hc
    · exact ((continuous_outerMinor v).continuousAt).div hlA hl
  have hΦr : ∀ᶠ h in 𝓝 g, Φ (cellRatio v h) = Φ (cellRatio v g) := hrA.eventually (hΦ' (cellRatio v g))
  filter_upwards [hmem, hval, hΦr] with h h1 h2 h3
  rw [cellSectionOf_apply_of_mem v χ Φ h1, cellSectionOf_apply_of_mem v χ Φ hgB, h2, h3]

private theorem cellSectionOf_mem_principalSeries3 {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (hχ : ∀ i, IsLocallyConstant (χ i)) {Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ} (hΦ : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) : cellSectionOf v χ Φ ∈ principalSeries3 v χ :=
  ⟨isLocallyConstant_cellSectionOf v hχ hΦ hΦc, cellSectionOf_upperUnipotent3_mul v χ Φ,
    cellSectionOf_diagonal3_mul v χ Φ⟩

end

section

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem exists_invariance_level {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {F : LocalGL3 v → ℂ}
    (hF : F ∈ principalSeries3 v χ) :
    ∃ M : ℕ, ∀ (g k : LocalGL3 v), k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v →
      (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
          - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(M : ℤ))) →
        F (g * k) = F g := by
  obtain ⟨n, hn⟩ := exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v χ F hF
  exact ⟨n, fun g k _ hk => congrFun (hn k hk) g⟩

private theorem valued_conj_sub_one_le {k₀ k : LocalGL3 v} (hk₀ : k₀ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) {M : ℕ}
    (hk : ∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
        - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
      ≤ WithZero.exp (-(M : ℤ))) :
    ∀ i j, Valued.v (((k₀⁻¹ * k * k₀ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
      - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(M : ℤ)) := by
  obtain ⟨h₀, h₀'⟩ := (mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mp hk₀
  intro i j
  have hmat : ((k₀⁻¹ * k * k₀ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1
      = ((k₀⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
        * ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1)
        * (k₀ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Units.inv_mul, Units.val_mul, Units.val_mul]
  rw [← Matrix.sub_apply, hmat, Matrix.mul_apply]
  refine Valued.v.map_sum_le fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Valued.v.map_sum_le fun p _ => ?_
  rw [Valuation.map_mul, Valuation.map_mul]
  have h₁ : Valued.v (((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) p l) ≤ WithZero.exp (-(M : ℤ)) := by
    rw [Matrix.sub_apply]
    exact hk p l
  have h₂ : Valued.v (((k₀⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i p)
        * Valued.v (((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) p l)
        * Valued.v ((k₀ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) l j)
      ≤ 1 * WithZero.exp (-(M : ℤ)) * 1 :=
    mul_le_mul' (mul_le_mul' (h₀' i p) h₁) (h₀ l j)
  simpa only [one_mul, mul_one] using h₂

private theorem rightTranslate_invariant_of_mem_localMaximalCompact3 {F : LocalGL3 v → ℂ} {M : ℕ}
    (hm : ∀ (g k : LocalGL3 v), k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v →
      (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
          - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(M : ℤ))) →
        F (g * k) = F g)
    {k₀ : LocalGL3 v} (hk₀ : k₀ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    ∀ (g k : LocalGL3 v), k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v →
      (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
          - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(M : ℤ))) →
        gl3AmbientRightTranslate (R := ℂ) k₀ F (g * k) = gl3AmbientRightTranslate (R := ℂ) k₀ F g := by
  intro g k hk hk'
  have hmem : k₀⁻¹ * k * k₀ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := mul_mem (mul_mem (inv_mem hk₀) hk) hk₀
  show F (g * k * k₀) = F (g * k₀)
  rw [← hm (g * k₀) (k₀⁻¹ * k * k₀) hmem (valued_conj_sub_one_le v hk₀ hk')]
  congr 1
  group

end

section

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction Matrix

section Core

variable {K : Type*} [Field K]

private def unipMat (x y z : K) : Matrix (Fin 3) (Fin 3) K := !![1, x, z; 0, 1, y; 0, 0, 1]

private def antidiagMat : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

private def shearShiftCompactByX (x y z Δ : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0; Δ / (x * (x - Δ)), 1, Δ / (x * (x - Δ)) * (z - x * y); 0, 0, 1]

private def shearShiftCompactByXInv (x y z Δ : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0; -(Δ / (x * (x - Δ))), 1, -(Δ / (x * (x - Δ)) * (z - x * y)); 0, 0, 1]

private theorem shearShiftCompactByX_mul_inv (x y z Δ : K) : shearShiftCompactByX x y z Δ *
    shearShiftCompactByXInv x y z Δ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shearShiftCompactByX, shearShiftCompactByXInv, Matrix.mul_apply,
      Fin.sum_univ_three]

private theorem shearShiftCompactByX_inv_mul (x y z Δ : K) : shearShiftCompactByXInv x y z Δ *
    shearShiftCompactByX x y z Δ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shearShiftCompactByX, shearShiftCompactByXInv, Matrix.mul_apply,
      Fin.sum_univ_three]

private theorem antidiagMat_mul_unipMat (x y z : K) : antidiagMat * unipMat x y z = !![0, 0, 1; 0, 1, y; 1, x, z] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antidiagMat, unipMat, Matrix.mul_apply, Fin.sum_univ_three]

private def shearShiftTorusByX (x Δ : K) : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, x / (x - Δ), 0; 0, 0, (x -
    Δ) / x]

private theorem diagonal_eq_shearShiftTorusByX (x Δ : K) : Matrix.diagonal ![1, x / (x - Δ), (x - Δ) / x] =
    shearShiftTorusByX x Δ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shearShiftTorusByX, Matrix.diagonal]

private theorem unipMat_mul_shearShiftTorusByX (x Δ : K) :
    unipMat 0 (-(Δ / (x - Δ) ^ 2)) 0 * shearShiftTorusByX x Δ
      = !![1, 0, 0; 0, x / (x - Δ), -(Δ / (x - Δ) ^ 2) * ((x - Δ) / x); 0, 0, (x - Δ) / x] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipMat, shearShiftTorusByX, Matrix.mul_apply, Fin.sum_univ_three]

private theorem shearShiftByX_left_mul (x y z Δ : K) (hx : x ≠ 0) (hxΔ : x - Δ ≠ 0) :
    (!![1, 0, 0; 0, x / (x - Δ), -(Δ / (x - Δ) ^ 2) * ((x - Δ) / x); 0, 0, (x - Δ) / x] : Matrix (Fin 3) (Fin 3) K)
        * !![0, 0, 1; 0, 1, y; 1, x, z]
      = !![0, 0, 1;
           -(Δ / ((x - Δ) * x)), 1, x / (x - Δ) * y - Δ / ((x - Δ) * x) * z;
           (x - Δ) / x, x - Δ, (x - Δ) / x * z] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> ring

private theorem shearShiftByX_matrix (x y z Δ : K) (hx : x ≠ 0) (hxΔ : x - Δ ≠ 0) :
    antidiagMat * unipMat (x - Δ) y (z - Δ * y)
      = unipMat 0 (-(Δ / (x - Δ) ^ 2)) 0 * Matrix.diagonal ![1, x / (x - Δ), (x - Δ) / x] * (antidiagMat *
          unipMat x y z)
          * shearShiftCompactByX x y z Δ := by
  rw [diagonal_eq_shearShiftTorusByX, unipMat_mul_shearShiftTorusByX, antidiagMat_mul_unipMat,
      antidiagMat_mul_unipMat, shearShiftByX_left_mul x y z Δ hx hxΔ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shearShiftCompactByX, Matrix.mul_apply, Fin.sum_univ_three] <;>
      field_simp <;> ring

end Core

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def shearShiftCompactByXGL (x y z Δ : v.adicCompletion ℚ) : LocalGL3 v where
  val := shearShiftCompactByX x y z Δ
  inv := shearShiftCompactByXInv x y z Δ
  val_inv := shearShiftCompactByX_mul_inv x y z Δ
  inv_val := shearShiftCompactByX_inv_mul x y z Δ

private theorem shearShiftCompactByXGL_coe (x y z Δ : v.adicCompletion ℚ) :
    (shearShiftCompactByXGL v x y z Δ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = shearShiftCompactByX x y
        z Δ := rfl

private theorem shearShiftCompactByXGL_inv_coe (x y z Δ : v.adicCompletion ℚ) :
    (((shearShiftCompactByXGL v x y z Δ)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
        shearShiftCompactByXInv x y z Δ := rfl

private theorem valued_shearShiftByX_entry_le {x Δ : v.adicCompletion ℚ} {e : WithZero (Multiplicative ℤ)} (hx : x ≠ 0)
    (hlt : Valued.v Δ < Valued.v x)
    (h2 : Valued.v Δ ≤ Valued.v x * Valued.v x * e) : Valued.v (Δ / (x * (x - Δ))) ≤ e := by
  have hvx : Valued.v x ≠ (0 : WithZero (Multiplicative ℤ)) := (Valuation.ne_zero_iff _).mpr hx
  rw [map_div₀, map_mul, Valuation.map_sub_eq_of_lt_left _ hlt, div_le_iff₀ (zero_lt_iff.mpr (mul_ne_zero hvx hvx))]
  simpa [mul_comm, mul_left_comm, mul_assoc] using h2

private theorem valued_shearShiftByX_entry_mul_le {x y z Δ : v.adicCompletion ℚ} {e : WithZero (Multiplicative
    ℤ)} (hx : x ≠ 0)
    (hlt : Valued.v Δ < Valued.v x)
    (h3 : Valued.v Δ * Valued.v (z - x * y) ≤ Valued.v x * Valued.v x * e) :
    Valued.v (Δ / (x * (x - Δ)) * (z - x * y)) ≤ e := by
  have hvx : Valued.v x ≠ (0 : WithZero (Multiplicative ℤ)) := (Valuation.ne_zero_iff _).mpr hx
  rw [map_mul, map_div₀, map_mul, Valuation.map_sub_eq_of_lt_left _ hlt, div_mul_eq_mul_div,
    div_le_iff₀ (zero_lt_iff.mpr (mul_ne_zero hvx hvx))]
  simpa [mul_comm, mul_left_comm, mul_assoc] using h3

private theorem shearShiftCompactByXGL_mem_and_congruent {x y z Δ : v.adicCompletion ℚ} (M : ℕ) (hx : x ≠ 0)
    (hlt : Valued.v Δ < Valued.v x) (h2 : Valued.v Δ ≤ Valued.v x * Valued.v x * WithZero.exp (-(M : ℤ)))
    (h3 : Valued.v Δ * Valued.v (z - x * y) ≤ Valued.v x * Valued.v x * WithZero.exp (-(M : ℤ))) :
    shearShiftCompactByXGL v x y z Δ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧
      ∀ i j, Valued.v ((shearShiftCompactByXGL v x y z Δ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
          - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(M : ℤ)) := by
  have hr : Valued.v (Δ / (x * (x - Δ))) ≤ WithZero.exp (-(M : ℤ)) := valued_shearShiftByX_entry_le v hx hlt h2
  have hrz : Valued.v (Δ / (x * (x - Δ)) * (z - x * y)) ≤ WithZero.exp (-(M : ℤ)) :=
      valued_shearShiftByX_entry_mul_le v hx hlt h3
  have hM : WithZero.exp (-(M : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
    simpa using WithZero.exp_le_exp.mpr (show (-(M : ℤ)) ≤ 0 by omega)
  have hr1 : Valued.v (Δ / (x * (x - Δ))) ≤ (1 : WithZero (Multiplicative ℤ)) := hr.trans hM
  have hrz1 : Valued.v (Δ / (x * (x - Δ)) * (z - x * y)) ≤ (1 : WithZero (Multiplicative ℤ)) := hrz.trans hM
  refine ⟨(mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mpr ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · rw [shearShiftCompactByXGL_coe]
    unfold shearShiftCompactByX
    set rz := Δ / (x * (x - Δ)) * (z - x * y) with hrz_def
    set r := Δ / (x * (x - Δ)) with hr_def
    fin_cases i <;> fin_cases j <;> simp <;> first | simpa using hr1 | simpa using hrz1
  · rw [shearShiftCompactByXGL_inv_coe]
    unfold shearShiftCompactByXInv
    set rz := Δ / (x * (x - Δ)) * (z - x * y) with hrz_def
    set r := Δ / (x * (x - Δ)) with hr_def
    fin_cases i <;> fin_cases j <;> simp <;> first | simpa using hr1 | simpa using hrz1
  · rw [shearShiftCompactByXGL_coe]
    unfold shearShiftCompactByX
    set rz := Δ / (x * (x - Δ)) * (z - x * y) with hrz_def
    set r := Δ / (x * (x - Δ)) with hr_def
    fin_cases i <;> fin_cases j <;> simp <;> first | simpa using hr | simpa using hrz

private theorem shearShiftByX_gl {x Δ : v.adicCompletion ℚ} (y z : v.adicCompletion ℚ) (hx : x ≠ 0) (hxΔ : x - Δ ≠ 0) :
    antidiagonal3 v * upperUnipotent3 (x - Δ) y (z - Δ * y)
      = upperUnipotent3 0 (-(Δ / (x - Δ) ^ 2)) 0
          * diagonal3 v
              ![1, Units.mk0 (x / (x - Δ)) (div_ne_zero hx hxΔ), Units.mk0 ((x - Δ) / x) (div_ne_zero hxΔ hx)]
          * (antidiagonal3 v * upperUnipotent3 x y z) * shearShiftCompactByXGL v x y z Δ := by
  apply Units.ext
  simp only [Units.val_mul, antidiagonal3_coe, upperUnipotent3_coe, diagonal3_coe, shearShiftCompactByXGL_coe]
  have hd : (fun i => ((![1, Units.mk0 (x / (x - Δ)) (div_ne_zero hx hxΔ),
      Units.mk0 ((x - Δ) / x) (div_ne_zero hxΔ hx)] : Fin 3 → (v.adicCompletion ℚ)ˣ) i : v.adicCompletion ℚ))
        = ![1, x / (x - Δ), (x - Δ) / x] := by
    funext i
    fin_cases i <;> simp
  rw [hd]
  exact shearShiftByX_matrix x y z Δ hx hxΔ

private theorem shearShiftTorusByX_char_eq_one {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {f : ℕ}
    (hχf : ∀ (i : Fin 3) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(f : ℤ) - 1) → χ i u = 1)
    {x Δ : v.adicCompletion ℚ} (hx : x ≠ 0) (hxΔ : x - Δ ≠ 0) (hlt : Valued.v Δ < Valued.v x)
    (h1 : Valued.v Δ ≤ Valued.v x * WithZero.exp (-(f : ℤ) - 1)) :
    torusChar3 v χ ![1, Units.mk0 (x / (x - Δ)) (div_ne_zero hx hxΔ), Units.mk0 ((x - Δ) / x) (div_ne_zero hxΔ hx)]
        = 1 ∧
      halfModulus3 v ![1, Units.mk0 (x / (x - Δ)) (div_ne_zero hx hxΔ), Units.mk0 ((x - Δ) / x) (div_ne_zero hxΔ hx)]
        = 1 := by
  have hvx : Valued.v x ≠ (0 : WithZero (Multiplicative ℤ)) := (Valuation.ne_zero_iff _).mpr hx
  have hvxΔ : Valued.v (x - Δ) = Valued.v x := Valuation.map_sub_eq_of_lt_left _ hlt
  have hu1 : Valued.v ((x / (x - Δ) : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(f : ℤ) - 1) := by
    have : (x / (x - Δ) : v.adicCompletion ℚ) - 1 = Δ / (x - Δ) := by
      rw [div_sub_one hxΔ, sub_sub_cancel]
    rw [this, map_div₀, hvxΔ, div_le_iff₀ (zero_lt_iff.mpr hvx), mul_comm]
    exact h1
  have hu2 : Valued.v (((x - Δ) / x : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(f : ℤ) - 1) := by
    have : ((x - Δ) / x : v.adicCompletion ℚ) - 1 = -Δ / x := by
      rw [div_sub_one hx, sub_sub_cancel_left]
    rw [this, map_div₀, Valuation.map_neg, div_le_iff₀ (zero_lt_iff.mpr hvx), mul_comm]
    exact h1
  constructor
  · simp only [torusChar3, Fin.prod_univ_three]
    simp [hχf 1 (Units.mk0 _ (div_ne_zero hx hxΔ)) hu1, hχf 2 (Units.mk0 _ (div_ne_zero hxΔ hx)) hu2]
  · simp only [halfModulus3]
    have hn : ‖(x - Δ : v.adicCompletion ℚ)‖ = ‖x‖ := by
      rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def, hvxΔ]
    have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    simp [norm_div, hn, hx']

private theorem principalSeries3_apply_shearShiftByX_eq {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {F :
    LocalGL3 v → ℂ} (hF : F ∈ principalSeries3 v χ)
    {M : ℕ}
    (hm : ∀ (g k : LocalGL3 v), k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v →
      (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
          - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(M : ℤ))) →
        F (g * k) = F g)
    {f : ℕ}
    (hχf : ∀ (i : Fin 3) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(f : ℤ) - 1) → χ i u = 1)
    (hMf : f + 1 ≤ M) {x y z Δ : v.adicCompletion ℚ} (hx : x ≠ 0) (hlt : Valued.v Δ < Valued.v x)
    (h1 : Valued.v Δ ≤ Valued.v x * WithZero.exp (-(M : ℤ)))
    (h2 : Valued.v Δ ≤ Valued.v x * Valued.v x * WithZero.exp (-(M : ℤ)))
    (h3 : Valued.v Δ * Valued.v (z - x * y) ≤ Valued.v x * Valued.v x * WithZero.exp (-(M : ℤ))) :
    F (antidiagonal3 v * upperUnipotent3 (x - Δ) y (z - Δ * y)) = F (antidiagonal3 v * upperUnipotent3 x y z) := by
  have hxΔ : x - Δ ≠ 0 := by
    intro h0
    rw [(sub_eq_zero.mp h0).symm] at hlt
    exact lt_irrefl _ hlt
  have hMM : WithZero.exp (-(M : ℤ)) ≤ WithZero.exp (-(f : ℤ) - 1) := by
    rw [WithZero.exp_le_exp]
    omega
  have h1' : Valued.v Δ ≤ Valued.v x * WithZero.exp (-(f : ℤ) - 1) := by
    refine h1.trans ?_
    gcongr
  obtain ⟨hk, hk'⟩ := shearShiftCompactByXGL_mem_and_congruent v M hx hlt h2 h3
  obtain ⟨hτ, hδ⟩ := shearShiftTorusByX_char_eq_one v hχf hx hxΔ hlt h1'
  rw [shearShiftByX_gl v y z hx hxΔ, hm _ _ hk hk', mul_assoc, apply_upperUnipotent3_mul_of_mem_principalSeries3 hF,
    apply_diagonal3_mul_of_mem_principalSeries3 hF, hτ, hδ, one_mul, one_mul]

private theorem apply_eq_of_eq_mul {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {F : LocalGL3 v → ℂ}
    (hF : F ∈ principalSeries3 v χ) {M : ℕ}
    (hm : ∀ (g k : LocalGL3 v), k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v →
      (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
          - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(M : ℤ))) →
        F (g * k) = F g)
    {g H k : LocalGL3 v} {a b c : v.adicCompletion ℚ} {d : Fin 3 → (v.adicCompletion ℚ)ˣ}
    (hg : g = upperUnipotent3 a b c * diagonal3 v d * H * k) (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (hk' : ∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
        - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(M : ℤ)))
    (hτ : torusChar3 v χ d = 1) (hδ : halfModulus3 v d = 1) : F g = F H := by
  rw [hg, hm _ _ hk hk', mul_assoc, apply_upperUnipotent3_mul_of_mem_principalSeries3 hF,
    apply_diagonal3_mul_of_mem_principalSeries3 hF, hτ, hδ, one_mul, one_mul]

private theorem exp_neg_natCast_le_one (M : ℕ) : WithZero.exp (-(M : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
  simpa using WithZero.exp_le_exp.mpr (show (-(M : ℤ)) ≤ 0 by omega)

private theorem exp_neg_natCast_le {M f : ℕ} (hMf : f + 1 ≤ M) :
    WithZero.exp (-(M : ℤ)) ≤ WithZero.exp (-(f : ℤ) - 1) := by
  rw [WithZero.exp_le_exp]
  omega

private theorem valued_div_le {a b : v.adicCompletion ℚ} {e : WithZero (Multiplicative ℤ)} (hb : b ≠ 0)
    (h : Valued.v a ≤ Valued.v b * e) : Valued.v (a / b) ≤ e := by
  have hvb : Valued.v b ≠ (0 : WithZero (Multiplicative ℤ)) := (Valuation.ne_zero_iff _).mpr hb
  rw [map_div₀, div_le_iff₀ (zero_lt_iff.mpr hvb)]
  simpa [mul_comm] using h

private theorem char_div_sub_eq_one {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {f : ℕ}
    (hχf : ∀ (i : Fin 3) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(f : ℤ) - 1) → χ i u = 1)
    (i : Fin 3) {a b : v.adicCompletion ℚ} (hb : b ≠ 0) (hlt : Valued.v a < Valued.v b)
    (h : Valued.v a ≤ Valued.v b * WithZero.exp (-(f : ℤ) - 1)) (hba : b - a ≠ 0) :
    χ i (Units.mk0 (b / (b - a)) (div_ne_zero hb hba)) = 1 := by
  apply hχf
  have hsub : Valued.v (b - a) = Valued.v b := Valuation.map_sub_eq_of_lt_left _ hlt
  have : (b / (b - a) : v.adicCompletion ℚ) - 1 = a / (b - a) := by
    rw [div_sub_one hba, sub_sub_cancel]
  rw [Units.val_mk0, this]
  exact valued_div_le v hba (hsub.symm ▸ h)

private theorem norm_div_sub_eq_one {a b : v.adicCompletion ℚ} (hlt : Valued.v a < Valued.v b) (hb : b ≠ 0) :
    ‖(b / (b - a) : v.adicCompletion ℚ)‖ = 1 := by
  have hsub : Valued.v (b - a) = Valued.v b := Valuation.map_sub_eq_of_lt_left _ hlt
  have hn : ‖(b - a : v.adicCompletion ℚ)‖ = ‖b‖ := by
    rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def, hsub]
  rw [norm_div, hn, div_self (norm_ne_zero_iff.mpr hb)]

section ShearShiftByZ

variable {K : Type*} [Field K]

private def shearShiftCompactByZ (y z Δ : K) : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, 1, 0; 0, -(Δ / z), 1 -
    Δ * y / z]

private def shearShiftCompactByZInv (y z Δ : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0; 0, 1, 0; 0, Δ / (z - Δ * y), z / (z - Δ * y)]

private theorem shearShiftCompactByZ_mul_inv (y z Δ : K) (hz : z ≠ 0) (hzΔ : z - Δ * y ≠ 0) :
    shearShiftCompactByZ y z Δ * shearShiftCompactByZInv y z Δ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shearShiftCompactByZ, shearShiftCompactByZInv, Matrix.mul_apply,
      Fin.sum_univ_three] <;>
    field_simp
  ring

private theorem shearShiftCompactByZ_inv_mul (y z Δ : K) (hz : z ≠ 0) (hzΔ : z - Δ * y ≠ 0) :
    shearShiftCompactByZInv y z Δ * shearShiftCompactByZ y z Δ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shearShiftCompactByZ, shearShiftCompactByZInv, Matrix.mul_apply,
      Fin.sum_univ_three] <;>
    field_simp
  ring

private theorem diagonal_eq_shearShiftTorusByZ (y z Δ : K) :
    Matrix.diagonal ![1, z / (z - Δ * y), 1] = !![1, 0, 0; 0, z / (z - Δ * y), 0; 0, 0, (1 : K)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

private theorem unipMat_mul_shearShiftTorusByZ (y z Δ : K) :
    unipMat (Δ / z) 0 0 * !![1, 0, 0; 0, z / (z - Δ * y), 0; 0, 0, (1 : K)]
      = !![1, Δ / z * (z / (z - Δ * y)), 0; 0, z / (z - Δ * y), 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipMat, Matrix.mul_apply, Fin.sum_univ_three]

private theorem shearShiftByZ_left_mul (x y z Δ : K) :
    (!![1, Δ / z * (z / (z - Δ * y)), 0; 0, z / (z - Δ * y), 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K)
        * !![0, 0, 1; 0, 1, y; 1, x, z]
      = !![0, Δ / z * (z / (z - Δ * y)), 1 + Δ / z * (z / (z - Δ * y)) * y;
           0, z / (z - Δ * y), z / (z - Δ * y) * y; 1, x, z] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem shearShiftByZ_matrix (x y z Δ : K) (hz : z ≠ 0) (hzΔ : z - Δ * y ≠ 0) :
    antidiagMat * unipMat (x - Δ) y (z - Δ * y)
      = unipMat (Δ / z) 0 0 * Matrix.diagonal ![1, z / (z - Δ * y), 1] * (antidiagMat * unipMat x y z) *
          shearShiftCompactByZ y z Δ := by
  rw [diagonal_eq_shearShiftTorusByZ, unipMat_mul_shearShiftTorusByZ, antidiagMat_mul_unipMat,
    antidiagMat_mul_unipMat, shearShiftByZ_left_mul]
  unfold shearShiftCompactByZ
  obtain ⟨u, hu⟩ : ∃ u, u = z - Δ * y := ⟨_, rfl⟩
  rw [← hu] at hzΔ ⊢
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> subst hu <;> ring

end ShearShiftByZ

private def shearShiftCompactByZGL {y z Δ : v.adicCompletion ℚ} (hz : z ≠ 0) (hzΔ : z - Δ * y ≠ 0) : LocalGL3 v where
  val := shearShiftCompactByZ y z Δ
  inv := shearShiftCompactByZInv y z Δ
  val_inv := shearShiftCompactByZ_mul_inv y z Δ hz hzΔ
  inv_val := shearShiftCompactByZ_inv_mul y z Δ hz hzΔ

private theorem shearShiftCompactByZGL_mem_and_congruent (M : ℕ) {y z Δ : v.adicCompletion ℚ} (hz : z ≠ 0)
    (hlt : Valued.v (Δ * y) < Valued.v z) (h1 : Valued.v Δ ≤ Valued.v z * WithZero.exp (-(M : ℤ)))
    (h2 : Valued.v (Δ * y) ≤ Valued.v z * WithZero.exp (-(M : ℤ))) (hzΔ : z - Δ * y ≠ 0) :
    shearShiftCompactByZGL v hz hzΔ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧
      ∀ i j, Valued.v ((shearShiftCompactByZGL v hz hzΔ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
          - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(M : ℤ)) := by
  have hM := exp_neg_natCast_le_one M
  have hs : Valued.v (Δ / z) ≤ WithZero.exp (-(M : ℤ)) := valued_div_le v hz h1
  have ht : Valued.v (Δ * y / z) ≤ WithZero.exp (-(M : ℤ)) := valued_div_le v hz h2
  have hsub : Valued.v (z - Δ * y) = Valued.v z := Valuation.map_sub_eq_of_lt_left _ hlt
  have hs' : Valued.v (Δ / (z - Δ * y)) ≤ (1 : WithZero (Multiplicative ℤ)) :=
    (valued_div_le v hzΔ (hsub.symm ▸ h1)).trans hM
  have hu : Valued.v (z / (z - Δ * y)) = (1 : WithZero (Multiplicative ℤ)) := by
    rw [map_div₀, hsub, div_self ((Valuation.ne_zero_iff _).mpr hz)]
  have h1t : Valued.v ((1 : v.adicCompletion ℚ) - Δ * y / z) ≤ (1 : WithZero (Multiplicative ℤ)) :=
    Valuation.map_sub_le _ (le_of_eq (map_one _)) (ht.trans hM)
  refine ⟨(mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mpr ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · show Valued.v (shearShiftCompactByZ y z Δ i j) ≤ 1
    unfold shearShiftCompactByZ
    set t := Δ * y / z with ht_def
    set s := Δ / z with hs_def
    fin_cases i <;> fin_cases j <;> simp <;> first | simpa using hs.trans hM | simpa using h1t
  · show Valued.v (shearShiftCompactByZInv y z Δ i j) ≤ 1
    unfold shearShiftCompactByZInv
    set s' := Δ / (z - Δ * y) with hs'_def
    set u := z / (z - Δ * y) with hu_def
    fin_cases i <;> fin_cases j <;> simp <;> first | simpa using hs' | simpa using le_of_eq hu
  · show Valued.v (shearShiftCompactByZ y z Δ i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ _
    unfold shearShiftCompactByZ
    set t := Δ * y / z with ht_def
    set s := Δ / z with hs_def
    fin_cases i <;> fin_cases j <;> simp <;> first | simpa using hs | simpa using ht

private theorem shearShiftByZ_gl (x : v.adicCompletion ℚ) {y z Δ : v.adicCompletion ℚ} (hz : z ≠ 0) (hzΔ : z - Δ
    * y ≠ 0) :
    antidiagonal3 v * upperUnipotent3 (x - Δ) y (z - Δ * y)
      = upperUnipotent3 (Δ / z) 0 0 * diagonal3 v ![1, Units.mk0 (z / (z - Δ * y)) (div_ne_zero hz hzΔ), 1]
          * (antidiagonal3 v * upperUnipotent3 x y z) * shearShiftCompactByZGL v hz hzΔ := by
  apply Units.ext
  simp only [Units.val_mul, antidiagonal3_coe, upperUnipotent3_coe, diagonal3_coe]
  have hd : (fun i => ((![1, Units.mk0 (z / (z - Δ * y)) (div_ne_zero hz hzΔ), 1] :
      Fin 3 → (v.adicCompletion ℚ)ˣ) i : v.adicCompletion ℚ)) = ![1, z / (z - Δ * y), 1] := by
    funext i
    fin_cases i <;> simp
  rw [hd]
  exact shearShiftByZ_matrix x y z Δ hz hzΔ

private theorem principalSeries3_apply_shearShiftByZ_eq {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {F :
    LocalGL3 v → ℂ} (hF : F ∈ principalSeries3 v χ)
    {M : ℕ}
    (hm : ∀ (g k : LocalGL3 v), k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v →
      (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
          - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(M : ℤ))) →
        F (g * k) = F g)
    {f : ℕ}
    (hχf : ∀ (i : Fin 3) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(f : ℤ) - 1) → χ i u = 1)
    (hMf : f + 1 ≤ M) (x : v.adicCompletion ℚ) {y z Δ : v.adicCompletion ℚ} (hz : z ≠ 0)
    (hlt : Valued.v (Δ * y) < Valued.v z) (h1 : Valued.v Δ ≤ Valued.v z * WithZero.exp (-(M : ℤ)))
    (h2 : Valued.v (Δ * y) ≤ Valued.v z * WithZero.exp (-(M : ℤ))) :
    F (antidiagonal3 v * upperUnipotent3 (x - Δ) y (z - Δ * y)) = F (antidiagonal3 v * upperUnipotent3 x y z) := by
  have hzΔ : z - Δ * y ≠ 0 := by
    intro h0
    rw [(sub_eq_zero.mp h0).symm] at hlt
    exact lt_irrefl _ hlt
  have h2' : Valued.v (Δ * y) ≤ Valued.v z * WithZero.exp (-(f : ℤ) - 1) := by
    refine h2.trans ?_
    gcongr
    exact exp_neg_natCast_le hMf
  obtain ⟨hk, hk'⟩ := shearShiftCompactByZGL_mem_and_congruent v M hz hlt h1 h2 hzΔ
  refine apply_eq_of_eq_mul v hF hm (shearShiftByZ_gl v x hz hzΔ) hk hk' ?_ ?_
  · simp only [torusChar3, Fin.prod_univ_three]
    simp [char_div_sub_eq_one v hχf 1 hz hlt h2' hzΔ]
  · simp [halfModulus3]

section PlainShiftByMinor

variable {K : Type*} [Field K]

private def plainShiftCompactByMinor (x y z Δ : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0; 0, 1 - Δ * y / (x * y - z), 0; 0, Δ / (x * y - z), 1]

private def plainShiftCompactByMinorInv (x y z Δ : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0; 0, (x * y - z) / (x * y - z - Δ * y), 0; 0, -(Δ / (x * y - z - Δ * y)), 1]

private theorem plainShiftCompactByMinor_mul_inv (x y z Δ : K) (hw : x * y - z ≠ 0) (hwΔ : x * y - z - Δ * y ≠ 0) :
    plainShiftCompactByMinor x y z Δ * plainShiftCompactByMinorInv x y z Δ = 1 := by
  unfold plainShiftCompactByMinor plainShiftCompactByMinorInv
  obtain ⟨wΔ, hwΔ_def⟩ : ∃ wΔ, wΔ = x * y - z - Δ * y := ⟨_, rfl⟩
  obtain ⟨w, hw_def⟩ : ∃ w, w = x * y - z := ⟨_, rfl⟩
  rw [← hwΔ_def] at hwΔ ⊢
  rw [← hw_def] at hw ⊢
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> subst hwΔ_def <;>
    subst hw_def <;> ring

private theorem plainShiftCompactByMinor_inv_mul (x y z Δ : K) (hw : x * y - z ≠ 0) (hwΔ : x * y - z - Δ * y ≠ 0) :
    plainShiftCompactByMinorInv x y z Δ * plainShiftCompactByMinor x y z Δ = 1 := by
  unfold plainShiftCompactByMinor plainShiftCompactByMinorInv
  obtain ⟨wΔ, hwΔ_def⟩ : ∃ wΔ, wΔ = x * y - z - Δ * y := ⟨_, rfl⟩
  obtain ⟨w, hw_def⟩ : ∃ w, w = x * y - z := ⟨_, rfl⟩
  rw [← hwΔ_def] at hwΔ ⊢
  rw [← hw_def] at hw ⊢
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> subst hwΔ_def <;>
    subst hw_def <;> ring

private theorem diagonal_eq_plainShiftTorusByMinor (x y z Δ : K) :
    Matrix.diagonal ![(x * y - z) / (x * y - z - Δ * y), 1, 1]
      = !![(x * y - z) / (x * y - z - Δ * y), 0, 0; 0, 1, 0; 0, 0, (1 : K)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

private theorem unipMat_mul_plainShiftTorusByMinor (x y z Δ : K) :
    unipMat (-(Δ / (x * y - z - Δ * y))) 0 0 * !![(x * y - z) / (x * y - z - Δ * y), 0, 0; 0, 1, 0; 0, 0, (1 : K)]
      = !![(x * y - z) / (x * y - z - Δ * y), -(Δ / (x * y - z - Δ * y)), 0; 0, 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipMat, Matrix.mul_apply, Fin.sum_univ_three]

private theorem plainShiftByMinor_left_mul (x y z Δ : K) (hw : x * y - z ≠ 0) (hwΔ : x * y - z - Δ * y ≠ 0) :
    (!![(x * y - z) / (x * y - z - Δ * y), -(Δ / (x * y - z - Δ * y)), 0; 0, 1, 0; 0, 0, 1] :
        Matrix (Fin 3) (Fin 3) K) * !![0, 0, 1; 0, 1, y; 1, x, z]
      = !![0, -(Δ / (x * y - z - Δ * y)), 1; 0, 1, y; 1, x, z] := by
  obtain ⟨wΔ, hwΔ_def⟩ : ∃ wΔ, wΔ = x * y - z - Δ * y := ⟨_, rfl⟩
  obtain ⟨w, hw_def⟩ : ∃ w, w = x * y - z := ⟨_, rfl⟩
  rw [← hwΔ_def] at hwΔ ⊢
  rw [← hw_def] at hw ⊢
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  field_simp
  subst hwΔ_def
  subst hw_def
  ring

private theorem plainShiftByMinor_matrix (x y z Δ : K) (hw : x * y - z ≠ 0) (hwΔ : x * y - z - Δ * y ≠ 0) :
    antidiagMat * unipMat (x - Δ) y z
      = unipMat (-(Δ / (x * y - z - Δ * y))) 0 0 * Matrix.diagonal ![(x * y - z) / (x * y - z - Δ * y), 1, 1]
          * (antidiagMat * unipMat x y z) * plainShiftCompactByMinor x y z Δ := by
  rw [diagonal_eq_plainShiftTorusByMinor, unipMat_mul_plainShiftTorusByMinor, antidiagMat_mul_unipMat,
      antidiagMat_mul_unipMat, plainShiftByMinor_left_mul x y z Δ hw hwΔ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [plainShiftCompactByMinor, Matrix.mul_apply, Fin.sum_univ_three] <;>
      field_simp <;> ring

end PlainShiftByMinor

private def plainShiftCompactByMinorGL {x y z Δ : v.adicCompletion ℚ} (hw : x * y - z ≠ 0) (hwΔ : x * y - z - Δ
    * y ≠ 0) : LocalGL3 v where
  val := plainShiftCompactByMinor x y z Δ
  inv := plainShiftCompactByMinorInv x y z Δ
  val_inv := plainShiftCompactByMinor_mul_inv x y z Δ hw hwΔ
  inv_val := plainShiftCompactByMinor_inv_mul x y z Δ hw hwΔ

private theorem plainShiftCompactByMinorGL_mem_and_congruent (M : ℕ) {x y z Δ : v.adicCompletion ℚ} (hw : x * y
    - z ≠ 0)
    (hlt : Valued.v (Δ * y) < Valued.v (x * y - z))
    (h1 : Valued.v Δ ≤ Valued.v (x * y - z) * WithZero.exp (-(M : ℤ)))
    (h2 : Valued.v (Δ * y) ≤ Valued.v (x * y - z) * WithZero.exp (-(M : ℤ))) (hwΔ : x * y - z - Δ * y ≠ 0) :
    plainShiftCompactByMinorGL v hw hwΔ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧
      ∀ i j, Valued.v ((plainShiftCompactByMinorGL v hw hwΔ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
          - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(M : ℤ)) := by
  have hM := exp_neg_natCast_le_one M
  have hs : Valued.v (Δ / (x * y - z)) ≤ WithZero.exp (-(M : ℤ)) := valued_div_le v hw h1
  have ht : Valued.v (Δ * y / (x * y - z)) ≤ WithZero.exp (-(M : ℤ)) := valued_div_le v hw h2
  have hsub : Valued.v (x * y - z - Δ * y) = Valued.v (x * y - z) := Valuation.map_sub_eq_of_lt_left _ hlt
  have hs' : Valued.v (Δ / (x * y - z - Δ * y)) ≤ (1 : WithZero (Multiplicative ℤ)) :=
    (valued_div_le v hwΔ (hsub.symm ▸ h1)).trans hM
  have hu : Valued.v ((x * y - z) / (x * y - z - Δ * y)) = (1 : WithZero (Multiplicative ℤ)) := by
    rw [map_div₀, hsub, div_self ((Valuation.ne_zero_iff _).mpr hw)]
  have h1t : Valued.v ((1 : v.adicCompletion ℚ) - Δ * y / (x * y - z)) ≤ (1 : WithZero (Multiplicative ℤ)) :=
    Valuation.map_sub_le _ (le_of_eq (map_one _)) (ht.trans hM)
  refine ⟨(mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mpr ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · show Valued.v (plainShiftCompactByMinor x y z Δ i j) ≤ 1
    unfold plainShiftCompactByMinor
    set t := Δ * y / (x * y - z) with ht_def
    set s := Δ / (x * y - z) with hs_def
    fin_cases i <;> fin_cases j <;> simp <;> first | simpa using hs.trans hM | simpa using h1t
  · show Valued.v (plainShiftCompactByMinorInv x y z Δ i j) ≤ 1
    unfold plainShiftCompactByMinorInv
    set s' := Δ / (x * y - z - Δ * y) with hs'_def
    set u := (x * y - z) / (x * y - z - Δ * y) with hu_def
    fin_cases i <;> fin_cases j <;> simp <;> first | simpa using hs' | simpa using le_of_eq hu
  · show Valued.v (plainShiftCompactByMinor x y z Δ i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ _
    unfold plainShiftCompactByMinor
    set t := Δ * y / (x * y - z) with ht_def
    set s := Δ / (x * y - z) with hs_def
    fin_cases i <;> fin_cases j <;> simp <;> first | simpa using hs | simpa using ht

private theorem plainShiftByMinor_gl {x y z Δ : v.adicCompletion ℚ} (hw : x * y - z ≠ 0) (hwΔ : x * y - z - Δ *
    y ≠ 0) :
    antidiagonal3 v * upperUnipotent3 (x - Δ) y z
      = upperUnipotent3 (-(Δ / (x * y - z - Δ * y))) 0 0
          * diagonal3 v ![Units.mk0 ((x * y - z) / (x * y - z - Δ * y)) (div_ne_zero hw hwΔ), 1, 1]
          * (antidiagonal3 v * upperUnipotent3 x y z) * plainShiftCompactByMinorGL v hw hwΔ := by
  apply Units.ext
  simp only [Units.val_mul, antidiagonal3_coe, upperUnipotent3_coe, diagonal3_coe]
  have hd : (fun i => ((![Units.mk0 ((x * y - z) / (x * y - z - Δ * y)) (div_ne_zero hw hwΔ), 1, 1] :
      Fin 3 → (v.adicCompletion ℚ)ˣ) i : v.adicCompletion ℚ)) = ![(x * y - z) / (x * y - z - Δ * y), 1, 1] := by
    funext i
    fin_cases i <;> simp
  rw [hd]
  exact plainShiftByMinor_matrix x y z Δ hw hwΔ

private theorem principalSeries3_apply_plainShiftByMinor_eq {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {F :
    LocalGL3 v → ℂ} (hF : F ∈ principalSeries3 v χ)
    {M : ℕ}
    (hm : ∀ (g k : LocalGL3 v), k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v →
      (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
          - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(M : ℤ))) →
        F (g * k) = F g)
    {f : ℕ}
    (hχf : ∀ (i : Fin 3) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(f : ℤ) - 1) → χ i u = 1)
    (hMf : f + 1 ≤ M) {x y z Δ : v.adicCompletion ℚ} (hw : x * y - z ≠ 0)
    (hlt : Valued.v (Δ * y) < Valued.v (x * y - z))
    (h1 : Valued.v Δ ≤ Valued.v (x * y - z) * WithZero.exp (-(M : ℤ)))
    (h2 : Valued.v (Δ * y) ≤ Valued.v (x * y - z) * WithZero.exp (-(M : ℤ))) :
    F (antidiagonal3 v * upperUnipotent3 (x - Δ) y z) = F (antidiagonal3 v * upperUnipotent3 x y z) := by
  have hwΔ : x * y - z - Δ * y ≠ 0 := by
    intro h0
    rw [(sub_eq_zero.mp h0).symm] at hlt
    exact lt_irrefl _ hlt
  have h2' : Valued.v (Δ * y) ≤ Valued.v (x * y - z) * WithZero.exp (-(f : ℤ) - 1) := by
    refine h2.trans ?_
    gcongr
    exact exp_neg_natCast_le hMf
  obtain ⟨hk, hk'⟩ := plainShiftCompactByMinorGL_mem_and_congruent v M hw hlt h1 h2 hwΔ
  refine apply_eq_of_eq_mul v hF hm (plainShiftByMinor_gl v hw hwΔ) hk hk' ?_ ?_
  · simp only [torusChar3, Fin.prod_univ_three]
    simp [char_div_sub_eq_one v hχf 0 hw hlt h2' hwΔ]
  · simp [halfModulus3, norm_div_sub_eq_one v hlt hw]

private theorem valued_quot_mul_le {b c Δ : v.adicCompletion ℚ} {e : WithZero (Multiplicative ℤ)} (hb : b ≠ 0)
    (hlt : Valued.v Δ < Valued.v b) (h : Valued.v Δ * Valued.v c ≤ Valued.v b * Valued.v b * e) :
    Valued.v (Δ / (b * (b - Δ)) * c) ≤ e := by
  have hvb : Valued.v b ≠ (0 : WithZero (Multiplicative ℤ)) := (Valuation.ne_zero_iff _).mpr hb
  rw [map_mul, map_div₀, map_mul, Valuation.map_sub_eq_of_lt_left _ hlt, div_mul_eq_mul_div,
    div_le_iff₀ (zero_lt_iff.mpr (mul_ne_zero hvb hvb))]
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

private theorem valued_one_add_le {t : v.adicCompletion ℚ} (ht : Valued.v t ≤ (1 : WithZero (Multiplicative ℤ))) :
    Valued.v ((1 : v.adicCompletion ℚ) + t) ≤ 1 :=
  (Valuation.map_add _ _ _).trans (max_le (le_of_eq (map_one _)) ht)

private theorem char_sub_div_eq_one {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {f : ℕ}
    (hχf : ∀ (i : Fin 3) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(f : ℤ) - 1) → χ i u = 1)
    (i : Fin 3) {a b : v.adicCompletion ℚ} (hb : b ≠ 0) (h : Valued.v a ≤ Valued.v b * WithZero.exp (-(f : ℤ) - 1))
    (hba : b - a ≠ 0) : χ i (Units.mk0 ((b - a) / b) (div_ne_zero hba hb)) = 1 := by
  apply hχf
  have : ((b - a) / b : v.adicCompletion ℚ) - 1 = -a / b := by
    rw [div_sub_one hb, sub_sub_cancel_left]
  rw [Units.val_mk0, this, neg_div, Valuation.map_neg]
  exact valued_div_le v hb h

private theorem norm_sub_div_eq_one {a b : v.adicCompletion ℚ} (hlt : Valued.v a < Valued.v b) (hb : b ≠ 0) :
    ‖((b - a) / b : v.adicCompletion ℚ)‖ = 1 := by
  have hsub : Valued.v (b - a) = Valued.v b := Valuation.map_sub_eq_of_lt_left _ hlt
  have hn : ‖(b - a : v.adicCompletion ℚ)‖ = ‖b‖ := by
    rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def, hsub]
  rw [norm_div, hn, div_self (norm_ne_zero_iff.mpr hb)]

section PlainSecondShiftByY

variable {K : Type*} [Field K]

private def plainSecondShiftCompactByY (y z Δ : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, -(Δ / (y * (y - Δ)) * z), 0; 0, 1, 0; 0, Δ / (y * (y - Δ)), 1]

private def plainSecondShiftCompactByYInv (y z Δ : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, Δ / (y * (y - Δ)) * z, 0; 0, 1, 0; 0, -(Δ / (y * (y - Δ))), 1]

private theorem plainSecondShiftCompactByY_mul_inv (y z Δ : K) :
    plainSecondShiftCompactByY y z Δ * plainSecondShiftCompactByYInv y z Δ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [plainSecondShiftCompactByY, plainSecondShiftCompactByYInv, Matrix.mul_apply, Fin.sum_univ_three]

private theorem plainSecondShiftCompactByY_inv_mul (y z Δ : K) :
    plainSecondShiftCompactByYInv y z Δ * plainSecondShiftCompactByY y z Δ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [plainSecondShiftCompactByY, plainSecondShiftCompactByYInv, Matrix.mul_apply, Fin.sum_univ_three]

private theorem diagonal_eq_plainSecondShiftTorusByY (y Δ : K) :
    Matrix.diagonal ![y / (y - Δ), (y - Δ) / y, 1] = !![y / (y - Δ), 0, 0; 0, (y - Δ) / y, 0; 0, 0, (1 : K)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

private theorem unipMat_mul_plainSecondShiftTorusByY (y Δ : K) (hy : y ≠ 0) (hyΔ : y - Δ ≠ 0) :
    unipMat (-(Δ / (y - Δ) ^ 2)) 0 0 * !![y / (y - Δ), 0, 0; 0, (y - Δ) / y, 0; 0, 0, (1 : K)]
      = !![y / (y - Δ), -(Δ / (y * (y - Δ))), 0; 0, (y - Δ) / y, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipMat, Matrix.mul_apply, Fin.sum_univ_three]
  field_simp

private theorem plainSecondShiftByY_left_mul (x y z Δ : K) (hy : y ≠ 0) (hyΔ : y - Δ ≠ 0) :
    (!![y / (y - Δ), -(Δ / (y * (y - Δ))), 0; 0, (y - Δ) / y, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K)
        * !![0, 0, 1; 0, 1, y; 1, x, z]
      = !![0, -(Δ / (y * (y - Δ))), 1; 0, (y - Δ) / y, y - Δ; 1, x, z] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp
  ring

private theorem plainSecondShiftByY_matrix (x y z Δ : K) (hy : y ≠ 0) (hyΔ : y - Δ ≠ 0) :
    antidiagMat * unipMat x (y - Δ) z
      = unipMat (-(Δ / (y - Δ) ^ 2)) 0 0 * Matrix.diagonal ![y / (y - Δ), (y - Δ) / y, 1]
          * (antidiagMat * unipMat x y z) * plainSecondShiftCompactByY y z Δ := by
  rw [diagonal_eq_plainSecondShiftTorusByY, unipMat_mul_plainSecondShiftTorusByY y Δ hy hyΔ, antidiagMat_mul_unipMat,
    antidiagMat_mul_unipMat, plainSecondShiftByY_left_mul x y z Δ hy hyΔ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [plainSecondShiftCompactByY, Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp <;> ring

end PlainSecondShiftByY

private def plainSecondShiftCompactByYGL (y z Δ : v.adicCompletion ℚ) : LocalGL3 v where
  val := plainSecondShiftCompactByY y z Δ
  inv := plainSecondShiftCompactByYInv y z Δ
  val_inv := plainSecondShiftCompactByY_mul_inv y z Δ
  inv_val := plainSecondShiftCompactByY_inv_mul y z Δ

private theorem plainSecondShiftCompactByYGL_mem_and_congruent (M : ℕ) {y z Δ : v.adicCompletion ℚ} (hy : y ≠ 0)
    (hlt : Valued.v Δ < Valued.v y) (h2 : Valued.v Δ ≤ Valued.v y * Valued.v y * WithZero.exp (-(M : ℤ)))
    (h3 : Valued.v Δ * Valued.v z ≤ Valued.v y * Valued.v y * WithZero.exp (-(M : ℤ))) :
    plainSecondShiftCompactByYGL v y z Δ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧
      ∀ i j, Valued.v ((plainSecondShiftCompactByYGL v y z Δ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
          - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(M : ℤ)) := by
  have hM := exp_neg_natCast_le_one M
  have hr : Valued.v (Δ / (y * (y - Δ))) ≤ WithZero.exp (-(M : ℤ)) := valued_shearShiftByX_entry_le v hy hlt h2
  have hrz : Valued.v (Δ / (y * (y - Δ)) * z) ≤ WithZero.exp (-(M : ℤ)) := valued_quot_mul_le v hy hlt h3
  have hr1 := hr.trans hM
  have hrz1 := hrz.trans hM
  refine ⟨(mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mpr ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · show Valued.v (plainSecondShiftCompactByY y z Δ i j) ≤ 1
    unfold plainSecondShiftCompactByY
    set rz := Δ / (y * (y - Δ)) * z with hrz_def
    set r := Δ / (y * (y - Δ)) with hr_def
    fin_cases i <;> fin_cases j <;> simp <;> first | simpa using hr1 | simpa using hrz1
  · show Valued.v (plainSecondShiftCompactByYInv y z Δ i j) ≤ 1
    unfold plainSecondShiftCompactByYInv
    set rz := Δ / (y * (y - Δ)) * z with hrz_def
    set r := Δ / (y * (y - Δ)) with hr_def
    fin_cases i <;> fin_cases j <;> simp <;> first | simpa using hr1 | simpa using hrz1
  · show Valued.v (plainSecondShiftCompactByY y z Δ i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ _
    unfold plainSecondShiftCompactByY
    set rz := Δ / (y * (y - Δ)) * z with hrz_def
    set r := Δ / (y * (y - Δ)) with hr_def
    fin_cases i <;> fin_cases j <;> simp <;> first | simpa using hr | simpa using hrz

private theorem plainSecondShiftByY_gl (x : v.adicCompletion ℚ) {y : v.adicCompletion ℚ} (z : v.adicCompletion ℚ)
    {Δ : v.adicCompletion ℚ} (hy : y ≠ 0) (hyΔ : y - Δ ≠ 0) :
    antidiagonal3 v * upperUnipotent3 x (y - Δ) z
      = upperUnipotent3 (-(Δ / (y - Δ) ^ 2)) 0 0
          * diagonal3 v ![Units.mk0 (y / (y - Δ)) (div_ne_zero hy hyΔ), Units.mk0 ((y - Δ) / y) (div_ne_zero hyΔ
              hy), 1]
          * (antidiagonal3 v * upperUnipotent3 x y z) * plainSecondShiftCompactByYGL v y z Δ := by
  apply Units.ext
  simp only [Units.val_mul, antidiagonal3_coe, upperUnipotent3_coe, diagonal3_coe]
  have hd : (fun i => ((![Units.mk0 (y / (y - Δ)) (div_ne_zero hy hyΔ), Units.mk0 ((y - Δ) / y) (div_ne_zero hyΔ
      hy), 1] :
      Fin 3 → (v.adicCompletion ℚ)ˣ) i : v.adicCompletion ℚ)) = ![y / (y - Δ), (y - Δ) / y, 1] := by
    funext i
    fin_cases i <;> simp
  rw [hd]
  exact plainSecondShiftByY_matrix x y z Δ hy hyΔ

private theorem principalSeries3_apply_plainSecondShiftByY_eq {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {F : LocalGL3 v → ℂ} (hF : F ∈ principalSeries3 v χ) {M : ℕ}
    (hm : ∀ (g k : LocalGL3 v), k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v →
      (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
          - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(M : ℤ))) →
        F (g * k) = F g)
    {f : ℕ}
    (hχf : ∀ (i : Fin 3) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(f : ℤ) - 1) → χ i u = 1)
    (hMf : f + 1 ≤ M) (x : v.adicCompletion ℚ) {y : v.adicCompletion ℚ} (z : v.adicCompletion ℚ)
    {Δ : v.adicCompletion ℚ} (hy : y ≠ 0) (hlt : Valued.v Δ < Valued.v y)
    (h1 : Valued.v Δ ≤ Valued.v y * WithZero.exp (-(M : ℤ)))
    (h2 : Valued.v Δ ≤ Valued.v y * Valued.v y * WithZero.exp (-(M : ℤ)))
    (h3 : Valued.v Δ * Valued.v z ≤ Valued.v y * Valued.v y * WithZero.exp (-(M : ℤ))) :
    F (antidiagonal3 v * upperUnipotent3 x (y - Δ) z) = F (antidiagonal3 v * upperUnipotent3 x y z) := by
  have hyΔ : y - Δ ≠ 0 := by
    intro h0
    rw [(sub_eq_zero.mp h0).symm] at hlt
    exact lt_irrefl _ hlt
  have h1' : Valued.v Δ ≤ Valued.v y * WithZero.exp (-(f : ℤ) - 1) := by
    refine h1.trans ?_
    gcongr
    exact exp_neg_natCast_le hMf
  obtain ⟨hk, hk'⟩ := plainSecondShiftCompactByYGL_mem_and_congruent v M hy hlt h2 h3
  refine apply_eq_of_eq_mul v hF hm (plainSecondShiftByY_gl v x z hy hyΔ) hk hk' ?_ ?_
  · simp only [torusChar3, Fin.prod_univ_three]
    simp [char_div_sub_eq_one v hχf 0 hy hlt h1' hyΔ, char_sub_div_eq_one v hχf 1 hy h1' hyΔ]
  · simp [halfModulus3, norm_div_sub_eq_one v hlt hy]

section PlainSecondShiftByMinor

variable {K : Type*} [Field K]

private def plainSecondShiftCompactByMinor (x y z Δ : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1 + Δ * x / (x * y - z - Δ * x), 0, 0; -(Δ / (x * y - z - Δ * x)), 1, 0; 0, 0, 1]

private def plainSecondShiftCompactByMinorInv (x y z Δ : K) : Matrix (Fin 3) (Fin 3) K :=
  !![(x * y - z - Δ * x) / (x * y - z), 0, 0; Δ / (x * y - z), 1, 0; 0, 0, 1]

private theorem plainSecondShiftCompactByMinor_mul_inv (x y z Δ : K) (hw : x * y - z ≠ 0)
    (hwΔ : x * y - z - Δ * x ≠ 0) :
    plainSecondShiftCompactByMinor x y z Δ * plainSecondShiftCompactByMinorInv x y z Δ = 1 := by
  unfold plainSecondShiftCompactByMinor plainSecondShiftCompactByMinorInv
  obtain ⟨wΔ, hwΔ_def⟩ : ∃ wΔ, wΔ = x * y - z - Δ * x := ⟨_, rfl⟩
  obtain ⟨w, hw_def⟩ : ∃ w, w = x * y - z := ⟨_, rfl⟩
  rw [← hwΔ_def] at hwΔ ⊢
  rw [← hw_def] at hw ⊢
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> subst hwΔ_def <;>
    subst hw_def <;> ring

private theorem plainSecondShiftCompactByMinor_inv_mul (x y z Δ : K) (hw : x * y - z ≠ 0)
    (hwΔ : x * y - z - Δ * x ≠ 0) :
    plainSecondShiftCompactByMinorInv x y z Δ * plainSecondShiftCompactByMinor x y z Δ = 1 := by
  unfold plainSecondShiftCompactByMinor plainSecondShiftCompactByMinorInv
  obtain ⟨wΔ, hwΔ_def⟩ : ∃ wΔ, wΔ = x * y - z - Δ * x := ⟨_, rfl⟩
  obtain ⟨w, hw_def⟩ : ∃ w, w = x * y - z := ⟨_, rfl⟩
  rw [← hwΔ_def] at hwΔ ⊢
  rw [← hw_def] at hw ⊢
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> subst hwΔ_def <;>
    subst hw_def <;> ring

private theorem diagonal_eq_plainSecondShiftTorusByMinor (x y z Δ : K) :
    Matrix.diagonal ![1, (x * y - z - Δ * x) / (x * y - z), 1]
      = !![1, 0, 0; 0, (x * y - z - Δ * x) / (x * y - z), 0; 0, 0, (1 : K)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

private theorem unipMat_mul_plainSecondShiftTorusByMinor (x y z Δ : K) :
    unipMat 0 (Δ / (x * y - z)) 0 * !![1, 0, 0; 0, (x * y - z - Δ * x) / (x * y - z), 0; 0, 0, (1 : K)]
      = !![1, 0, 0; 0, (x * y - z - Δ * x) / (x * y - z), Δ / (x * y - z); 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipMat, Matrix.mul_apply, Fin.sum_univ_three]

private theorem plainSecondShiftByMinor_left_mul (x y z Δ : K) (hw : x * y - z ≠ 0) :
    (!![1, 0, 0; 0, (x * y - z - Δ * x) / (x * y - z), Δ / (x * y - z); 0, 0, 1] : Matrix (Fin 3) (Fin 3) K)
        * !![0, 0, 1; 0, 1, y; 1, x, z]
      = !![0, 0, 1; Δ / (x * y - z), 1, y - Δ; 1, x, z] := by
  obtain ⟨w, hw_def⟩ : ∃ w, w = x * y - z := ⟨_, rfl⟩
  rw [← hw_def] at hw ⊢
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> subst hw_def <;> ring

private theorem plainSecondShiftByMinor_matrix (x y z Δ : K) (hw : x * y - z ≠ 0) (hwΔ : x * y - z - Δ * x ≠ 0) :
    antidiagMat * unipMat x (y - Δ) z
      = unipMat 0 (Δ / (x * y - z)) 0 * Matrix.diagonal ![1, (x * y - z - Δ * x) / (x * y - z), 1]
          * (antidiagMat * unipMat x y z) * plainSecondShiftCompactByMinor x y z Δ := by
  rw [diagonal_eq_plainSecondShiftTorusByMinor, unipMat_mul_plainSecondShiftTorusByMinor, antidiagMat_mul_unipMat,
    antidiagMat_mul_unipMat, plainSecondShiftByMinor_left_mul x y z Δ hw]
  unfold plainSecondShiftCompactByMinor
  obtain ⟨wΔ, hwΔ_def⟩ : ∃ wΔ, wΔ = x * y - z - Δ * x := ⟨_, rfl⟩
  obtain ⟨w, hw_def⟩ : ∃ w, w = x * y - z := ⟨_, rfl⟩
  rw [← hwΔ_def] at hwΔ ⊢
  rw [← hw_def] at hw ⊢
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> subst hwΔ_def <;>
    subst hw_def <;> ring

end PlainSecondShiftByMinor

private def plainSecondShiftCompactByMinorGL {x y z Δ : v.adicCompletion ℚ} (hw : x * y - z ≠ 0)
    (hwΔ : x * y - z - Δ * x ≠ 0) : LocalGL3 v where
  val := plainSecondShiftCompactByMinor x y z Δ
  inv := plainSecondShiftCompactByMinorInv x y z Δ
  val_inv := plainSecondShiftCompactByMinor_mul_inv x y z Δ hw hwΔ
  inv_val := plainSecondShiftCompactByMinor_inv_mul x y z Δ hw hwΔ

private theorem plainSecondShiftCompactByMinorGL_mem_and_congruent (M : ℕ) {x y z Δ : v.adicCompletion ℚ}
    (hw : x * y - z ≠ 0) (hlt : Valued.v (Δ * x) < Valued.v (x * y - z))
    (h1 : Valued.v Δ ≤ Valued.v (x * y - z) * WithZero.exp (-(M : ℤ)))
    (h2 : Valued.v (Δ * x) ≤ Valued.v (x * y - z) * WithZero.exp (-(M : ℤ))) (hwΔ : x * y - z - Δ * x ≠ 0) :
    plainSecondShiftCompactByMinorGL v hw hwΔ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧
      ∀ i j, Valued.v ((plainSecondShiftCompactByMinorGL v hw hwΔ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
          - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(M : ℤ)) := by
  have hM := exp_neg_natCast_le_one M
  have hsub : Valued.v (x * y - z - Δ * x) = Valued.v (x * y - z) := Valuation.map_sub_eq_of_lt_left _ hlt
  have hs : Valued.v (Δ / (x * y - z - Δ * x)) ≤ WithZero.exp (-(M : ℤ)) := valued_div_le v hwΔ (hsub.symm ▸ h1)
  have ht : Valued.v (Δ * x / (x * y - z - Δ * x)) ≤ WithZero.exp (-(M : ℤ)) := valued_div_le v hwΔ (hsub.symm ▸ h2)
  have h1t : Valued.v ((1 : v.adicCompletion ℚ) + Δ * x / (x * y - z - Δ * x)) ≤ 1 := valued_one_add_le v (ht.trans hM)
  have hs' : Valued.v (Δ / (x * y - z)) ≤ (1 : WithZero (Multiplicative ℤ)) := (valued_div_le v hw h1).trans hM
  have hu : Valued.v ((x * y - z - Δ * x) / (x * y - z)) = (1 : WithZero (Multiplicative ℤ)) := by
    rw [map_div₀, hsub, div_self ((Valuation.ne_zero_iff _).mpr hw)]
  refine ⟨(mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mpr ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · show Valued.v (plainSecondShiftCompactByMinor x y z Δ i j) ≤ 1
    unfold plainSecondShiftCompactByMinor
    set t := Δ * x / (x * y - z - Δ * x) with ht_def
    set s := Δ / (x * y - z - Δ * x) with hs_def
    fin_cases i <;> fin_cases j <;> simp <;> first | simpa using h1t | simpa using hs.trans hM
  · show Valued.v (plainSecondShiftCompactByMinorInv x y z Δ i j) ≤ 1
    unfold plainSecondShiftCompactByMinorInv
    set u := (x * y - z - Δ * x) / (x * y - z) with hu_def
    set s' := Δ / (x * y - z) with hs'_def
    fin_cases i <;> fin_cases j <;> simp <;> first | simpa using le_of_eq hu | simpa using hs'
  · show Valued.v (plainSecondShiftCompactByMinor x y z Δ i j
        - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ _
    unfold plainSecondShiftCompactByMinor
    set t := Δ * x / (x * y - z - Δ * x) with ht_def
    set s := Δ / (x * y - z - Δ * x) with hs_def
    fin_cases i <;> fin_cases j <;> simp <;> first | simpa using ht | simpa using hs

private theorem plainSecondShiftByMinor_gl {x y z Δ : v.adicCompletion ℚ} (hw : x * y - z ≠ 0)
    (hwΔ : x * y - z - Δ * x ≠ 0) :
    antidiagonal3 v * upperUnipotent3 x (y - Δ) z
      = upperUnipotent3 0 (Δ / (x * y - z)) 0
          * diagonal3 v ![1, Units.mk0 ((x * y - z - Δ * x) / (x * y - z)) (div_ne_zero hwΔ hw), 1]
          * (antidiagonal3 v * upperUnipotent3 x y z) * plainSecondShiftCompactByMinorGL v hw hwΔ := by
  apply Units.ext
  simp only [Units.val_mul, antidiagonal3_coe, upperUnipotent3_coe, diagonal3_coe]
  have hd : (fun i => ((![1, Units.mk0 ((x * y - z - Δ * x) / (x * y - z)) (div_ne_zero hwΔ hw), 1] :
      Fin 3 → (v.adicCompletion ℚ)ˣ) i : v.adicCompletion ℚ)) = ![1, (x * y - z - Δ * x) / (x * y - z), 1] := by
    funext i
    fin_cases i <;> simp
  rw [hd]
  exact plainSecondShiftByMinor_matrix x y z Δ hw hwΔ

private theorem principalSeries3_apply_plainSecondShiftByMinor_eq {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {F : LocalGL3 v → ℂ} (hF : F ∈ principalSeries3 v χ) {M : ℕ}
    (hm : ∀ (g k : LocalGL3 v), k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v →
      (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
          - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(M : ℤ))) →
        F (g * k) = F g)
    {f : ℕ}
    (hχf : ∀ (i : Fin 3) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(f : ℤ) - 1) → χ i u = 1)
    (hMf : f + 1 ≤ M) {x y z Δ : v.adicCompletion ℚ} (hw : x * y - z ≠ 0)
    (hlt : Valued.v (Δ * x) < Valued.v (x * y - z))
    (h1 : Valued.v Δ ≤ Valued.v (x * y - z) * WithZero.exp (-(M : ℤ)))
    (h2 : Valued.v (Δ * x) ≤ Valued.v (x * y - z) * WithZero.exp (-(M : ℤ))) :
    F (antidiagonal3 v * upperUnipotent3 x (y - Δ) z) = F (antidiagonal3 v * upperUnipotent3 x y z) := by
  have hwΔ : x * y - z - Δ * x ≠ 0 := by
    intro h0
    rw [(sub_eq_zero.mp h0).symm] at hlt
    exact lt_irrefl _ hlt
  have h2' : Valued.v (Δ * x) ≤ Valued.v (x * y - z) * WithZero.exp (-(f : ℤ) - 1) := by
    refine h2.trans ?_
    gcongr
    exact exp_neg_natCast_le hMf
  obtain ⟨hk, hk'⟩ := plainSecondShiftCompactByMinorGL_mem_and_congruent v M hw hlt h1 h2 hwΔ
  refine apply_eq_of_eq_mul v hF hm (plainSecondShiftByMinor_gl v hw hwΔ) hk hk' ?_ ?_
  · simp only [torusChar3, Fin.prod_univ_three]
    simp [char_sub_div_eq_one v hχf 1 hw h2' hwΔ]
  · simp [halfModulus3]

section ShearSecondShiftByZ

variable {K : Type*} [Field K]

private def shearSecondShiftCompactByZ (x z Δ : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0; Δ / (z - Δ * x), 1 + Δ * x / (z - Δ * x), 0; 0, 0, 1]

private def shearSecondShiftCompactByZInv (x z Δ : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0; -(Δ / z), (z - Δ * x) / z, 0; 0, 0, 1]

private theorem shearSecondShiftCompactByZ_mul_inv (x z Δ : K) (hz : z ≠ 0) (hzΔ : z - Δ * x ≠ 0) :
    shearSecondShiftCompactByZ x z Δ * shearSecondShiftCompactByZInv x z Δ = 1 := by
  unfold shearSecondShiftCompactByZ shearSecondShiftCompactByZInv
  obtain ⟨u, hu⟩ : ∃ u, u = z - Δ * x := ⟨_, rfl⟩
  rw [← hu] at hzΔ ⊢
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> subst hu <;> ring

private theorem shearSecondShiftCompactByZ_inv_mul (x z Δ : K) (hz : z ≠ 0) (hzΔ : z - Δ * x ≠ 0) :
    shearSecondShiftCompactByZInv x z Δ * shearSecondShiftCompactByZ x z Δ = 1 := by
  unfold shearSecondShiftCompactByZ shearSecondShiftCompactByZInv
  obtain ⟨u, hu⟩ : ∃ u, u = z - Δ * x := ⟨_, rfl⟩
  rw [← hu] at hzΔ ⊢
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> subst hu <;> ring

private theorem diagonal_eq_shearSecondShiftTorusByZ (x z Δ : K) :
    Matrix.diagonal ![1, 1, (z - Δ * x) / z] = !![1, 0, 0; 0, 1, 0; 0, 0, ((z - Δ * x) / z : K)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

private theorem unipMat_mul_shearSecondShiftTorusByZ (x z Δ : K) (hz : z ≠ 0) (hzΔ : z - Δ * x ≠ 0) :
    unipMat 0 (-(Δ / (z - Δ * x))) 0 * !![1, 0, 0; 0, 1, 0; 0, 0, ((z - Δ * x) / z : K)]
      = !![1, 0, 0; 0, 1, -(Δ / z); 0, 0, (z - Δ * x) / z] := by
  unfold unipMat
  obtain ⟨u, hu⟩ : ∃ u, u = z - Δ * x := ⟨_, rfl⟩
  rw [← hu] at hzΔ ⊢
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  field_simp

private theorem shearSecondShiftByZ_left_mul (x y z Δ : K) (hz : z ≠ 0) :
    (!![1, 0, 0; 0, 1, -(Δ / z); 0, 0, (z - Δ * x) / z] : Matrix (Fin 3) (Fin 3) K) * !![0, 0, 1; 0, 1, y; 1, x, z]
      = !![0, 0, 1; -(Δ / z), (z - Δ * x) / z, y - Δ; (z - Δ * x) / z, x * ((z - Δ * x) / z), z - Δ * x] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> ring

private theorem shearSecondShiftByZ_matrix (x y z Δ : K) (hz : z ≠ 0) (hzΔ : z - Δ * x ≠ 0) :
    antidiagMat * unipMat x (y - Δ) (z - Δ * x)
      = unipMat 0 (-(Δ / (z - Δ * x))) 0 * Matrix.diagonal ![1, 1, (z - Δ * x) / z] * (antidiagMat * unipMat x y z)
          * shearSecondShiftCompactByZ x z Δ := by
  rw [diagonal_eq_shearSecondShiftTorusByZ, unipMat_mul_shearSecondShiftTorusByZ x z Δ hz hzΔ, antidiagMat_mul_unipMat,
    antidiagMat_mul_unipMat, shearSecondShiftByZ_left_mul x y z Δ hz]
  unfold shearSecondShiftCompactByZ
  obtain ⟨u, hu⟩ : ∃ u, u = z - Δ * x := ⟨_, rfl⟩
  rw [← hu] at hzΔ ⊢
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> subst hu <;> ring

end ShearSecondShiftByZ

private def shearSecondShiftCompactByZGL {x z Δ : v.adicCompletion ℚ} (hz : z ≠ 0) (hzΔ : z - Δ * x ≠ 0) :
    LocalGL3 v where
  val := shearSecondShiftCompactByZ x z Δ
  inv := shearSecondShiftCompactByZInv x z Δ
  val_inv := shearSecondShiftCompactByZ_mul_inv x z Δ hz hzΔ
  inv_val := shearSecondShiftCompactByZ_inv_mul x z Δ hz hzΔ

private theorem shearSecondShiftCompactByZGL_mem_and_congruent (M : ℕ) {x z Δ : v.adicCompletion ℚ} (hz : z ≠ 0)
    (hlt : Valued.v (Δ * x) < Valued.v z) (h1 : Valued.v Δ ≤ Valued.v z * WithZero.exp (-(M : ℤ)))
    (h2 : Valued.v (Δ * x) ≤ Valued.v z * WithZero.exp (-(M : ℤ))) (hzΔ : z - Δ * x ≠ 0) :
    shearSecondShiftCompactByZGL v hz hzΔ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧
      ∀ i j, Valued.v ((shearSecondShiftCompactByZGL v hz hzΔ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
          - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(M : ℤ)) := by
  have hM := exp_neg_natCast_le_one M
  have hsub : Valued.v (z - Δ * x) = Valued.v z := Valuation.map_sub_eq_of_lt_left _ hlt
  have hs : Valued.v (Δ / (z - Δ * x)) ≤ WithZero.exp (-(M : ℤ)) := valued_div_le v hzΔ (hsub.symm ▸ h1)
  have ht : Valued.v (Δ * x / (z - Δ * x)) ≤ WithZero.exp (-(M : ℤ)) := valued_div_le v hzΔ (hsub.symm ▸ h2)
  have h1t : Valued.v ((1 : v.adicCompletion ℚ) + Δ * x / (z - Δ * x)) ≤ 1 := valued_one_add_le v (ht.trans hM)
  have hs' : Valued.v (Δ / z) ≤ (1 : WithZero (Multiplicative ℤ)) := (valued_div_le v hz h1).trans hM
  have hu : Valued.v ((z - Δ * x) / z) = (1 : WithZero (Multiplicative ℤ)) := by
    rw [map_div₀, hsub, div_self ((Valuation.ne_zero_iff _).mpr hz)]
  refine ⟨(mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mpr ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · show Valued.v (shearSecondShiftCompactByZ x z Δ i j) ≤ 1
    unfold shearSecondShiftCompactByZ
    set t := Δ * x / (z - Δ * x) with ht_def
    set s := Δ / (z - Δ * x) with hs_def
    fin_cases i <;> fin_cases j <;> simp <;> first | simpa using hs.trans hM | simpa using h1t
  · show Valued.v (shearSecondShiftCompactByZInv x z Δ i j) ≤ 1
    unfold shearSecondShiftCompactByZInv
    set u := (z - Δ * x) / z with hu_def
    set s' := Δ / z with hs'_def
    fin_cases i <;> fin_cases j <;> simp <;> first | simpa using hs' | simpa using le_of_eq hu
  · show Valued.v (shearSecondShiftCompactByZ x z Δ i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ _
    unfold shearSecondShiftCompactByZ
    set t := Δ * x / (z - Δ * x) with ht_def
    set s := Δ / (z - Δ * x) with hs_def
    fin_cases i <;> fin_cases j <;> simp <;> first | simpa using hs | simpa using ht

private theorem shearSecondShiftByZ_gl {x : v.adicCompletion ℚ} (y : v.adicCompletion ℚ) {z Δ : v.adicCompletion ℚ}
    (hz : z ≠ 0) (hzΔ : z - Δ * x ≠ 0) :
    antidiagonal3 v * upperUnipotent3 x (y - Δ) (z - Δ * x)
      = upperUnipotent3 0 (-(Δ / (z - Δ * x))) 0 * diagonal3 v ![1, 1, Units.mk0 ((z - Δ * x) / z) (div_ne_zero
          hzΔ hz)]
          * (antidiagonal3 v * upperUnipotent3 x y z) * shearSecondShiftCompactByZGL v hz hzΔ := by
  apply Units.ext
  simp only [Units.val_mul, antidiagonal3_coe, upperUnipotent3_coe, diagonal3_coe]
  have hd : (fun i => ((![1, 1, Units.mk0 ((z - Δ * x) / z) (div_ne_zero hzΔ hz)] : Fin 3 → (v.adicCompletion ℚ)ˣ) i :
      v.adicCompletion ℚ)) = ![1, 1, (z - Δ * x) / z] := by
    funext i
    fin_cases i <;> simp
  rw [hd]
  exact shearSecondShiftByZ_matrix x y z Δ hz hzΔ

private theorem principalSeries3_apply_shearSecondShiftByZ_eq {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {F : LocalGL3 v → ℂ} (hF : F ∈ principalSeries3 v χ) {M : ℕ}
    (hm : ∀ (g k : LocalGL3 v), k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v →
      (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
          - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(M : ℤ))) →
        F (g * k) = F g)
    {f : ℕ}
    (hχf : ∀ (i : Fin 3) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(f : ℤ) - 1) → χ i u = 1)
    (hMf : f + 1 ≤ M) {x : v.adicCompletion ℚ} (y : v.adicCompletion ℚ) {z Δ : v.adicCompletion ℚ} (hz : z ≠ 0)
    (hlt : Valued.v (Δ * x) < Valued.v z) (h1 : Valued.v Δ ≤ Valued.v z * WithZero.exp (-(M : ℤ)))
    (h2 : Valued.v (Δ * x) ≤ Valued.v z * WithZero.exp (-(M : ℤ))) :
    F (antidiagonal3 v * upperUnipotent3 x (y - Δ) (z - Δ * x)) = F (antidiagonal3 v * upperUnipotent3 x y z) := by
  have hzΔ : z - Δ * x ≠ 0 := by
    intro h0
    rw [(sub_eq_zero.mp h0).symm] at hlt
    exact lt_irrefl _ hlt
  have h2' : Valued.v (Δ * x) ≤ Valued.v z * WithZero.exp (-(f : ℤ) - 1) := by
    refine h2.trans ?_
    gcongr
    exact exp_neg_natCast_le hMf
  obtain ⟨hk, hk'⟩ := shearSecondShiftCompactByZGL_mem_and_congruent v M hz hlt h1 h2 hzΔ
  refine apply_eq_of_eq_mul v hF hm (shearSecondShiftByZ_gl v y hz hzΔ) hk hk' ?_ ?_
  · simp only [torusChar3, Fin.prod_univ_three]
    simp [char_sub_div_eq_one v hχf 2 hz h2' hzΔ]
  · simp [halfModulus3, norm_sub_div_eq_one v hlt hz]

open MeasureTheory NumberField.StandardAddChar LanglandsTunnell.TateLocal

private abbrev Unip3 : Type := v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ

private noncomputable def unipotentShift (p₀ : Unip3 v) : Unip3 v ≃ₜ Unip3 v where
  toFun p := (p.1 + p₀.1, p.2.1 + p₀.2.1, p.2.2 + p₀.2.2 + p.1 * p₀.2.1)
  invFun p := (p.1 - p₀.1, p.2.1 - p₀.2.1, p.2.2 - p₀.2.2 - (p.1 - p₀.1) * p₀.2.1)
  left_inv p := by
    obtain ⟨a, b, d⟩ := p
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> ring
  right_inv p := by
    obtain ⟨a, b, d⟩ := p
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> ring
  continuous_toFun :=
    (continuous_fst.add continuous_const).prodMk
      (((continuous_fst.comp continuous_snd).add continuous_const).prodMk
        (((continuous_snd.comp continuous_snd).add continuous_const).add (continuous_fst.mul continuous_const)))
  continuous_invFun :=
    (continuous_fst.sub continuous_const).prodMk
      (((continuous_fst.comp continuous_snd).sub continuous_const).prodMk
        (((continuous_snd.comp continuous_snd).sub continuous_const).sub
          ((continuous_fst.sub continuous_const).mul continuous_const)))

private theorem unipotentShift_apply (p₀ p : Unip3 v) :
    unipotentShift v p₀ p = (p.1 + p₀.1, p.2.1 + p₀.2.1, p.2.2 + p₀.2.2 + p.1 * p₀.2.1) :=
  rfl

private theorem preimage_unipotentBall3_unipotentShift {c : ℤ} {p₀ : Unip3 v} (hp₀ : p₀ ∈ unipotentBall3 v c) :
    unipotentShift v p₀ ⁻¹' unipotentBall3 v c = unipotentBall3 v c := by
  ext p
  constructor
  · intro hp
    have hmem := unipotentBall3_mul_mem v (c := c) (p := unipotentShift v p₀ p)
      (p' := (-p₀.1, -p₀.2.1, p₀.1 * p₀.2.1 - p₀.2.2)) hp (unipotentBall3_inv_mem v hp₀)
    convert hmem using 1
    obtain ⟨a, b, d⟩ := p
    simp only [unipotentShift_apply, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> ring
  · intro hp
    exact unipotentBall3_mul_mem v hp hp₀

private theorem isAddHaarMeasure_selfDualHaarAt_rat :
    letI := localBorel ℚ v
    (selfDualHaarAt ℚ v).IsAddHaarMeasure := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  have hN : (0 : NNReal) < (Ideal.absNorm v.asIdeal : NNReal) := by
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero h0
  unfold selfDualHaarAt
  exact Measure.IsAddHaarMeasure.nnreal_smul _ (NNReal.rpow_pos hN).ne'

private theorem measurePreserving_unipotentShift (p₀ : Unip3 v) :
    letI := localBorel ℚ v
    MeasurePreserving (unipotentShift v p₀) (jacquetHaar3 v) (jacquetHaar3 v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt_rat v
  have hshape : (unipotentShift v p₀ : Unip3 v → Unip3 v)
      = fun p : Unip3 v => (p₀.1 + p.1, (p₀.2.1, p₀.2.2 + p.1 * p₀.2.1) + p.2) := by
    funext p
    obtain ⟨a, b, d⟩ := p
    simp only [unipotentShift_apply, Prod.mk_add_mk, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> ring
  show MeasurePreserving (unipotentShift v p₀)
    ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)))
    ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)))
  rw [hshape]
  refine MeasurePreserving.skew_product
    (g := fun (a : v.adicCompletion ℚ) (q : v.adicCompletion ℚ × v.adicCompletion ℚ) =>
      (p₀.2.1, p₀.2.2 + a * p₀.2.1) + q)
    (measurePreserving_add_left (selfDualHaarAt ℚ v) p₀.1) ?_ ?_
  · exact (((continuous_const.prodMk (continuous_const.add (continuous_fst.mul continuous_const))).add
      continuous_snd) : Continuous fun q : v.adicCompletion ℚ × (v.adicCompletion ℚ × v.adicCompletion ℚ) =>
        (p₀.2.1, p₀.2.2 + q.1 * p₀.2.1) + q.2).measurable
  · exact Filter.Eventually.of_forall fun a =>
      map_add_left_eq_self ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)) (p₀.2.1, p₀.2.2 + a * p₀.2.1)

private noncomputable def unipotentLeftShift (p₀ : Unip3 v) : Unip3 v ≃ₜ Unip3 v where
  toFun p := (p₀.1 + p.1, p₀.2.1 + p.2.1, p₀.2.2 + p.2.2 + p₀.1 * p.2.1)
  invFun p := (p.1 - p₀.1, p.2.1 - p₀.2.1, p.2.2 - p₀.2.2 - p₀.1 * (p.2.1 - p₀.2.1))
  left_inv p := by
    obtain ⟨a, b, d⟩ := p
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> ring
  right_inv p := by
    obtain ⟨a, b, d⟩ := p
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> ring
  continuous_toFun :=
    (continuous_const.add continuous_fst).prodMk
      ((continuous_const.add (continuous_fst.comp continuous_snd)).prodMk
        ((continuous_const.add (continuous_snd.comp continuous_snd)).add
          (continuous_const.mul (continuous_fst.comp continuous_snd))))
  continuous_invFun :=
    (continuous_fst.sub continuous_const).prodMk
      (((continuous_fst.comp continuous_snd).sub continuous_const).prodMk
        (((continuous_snd.comp continuous_snd).sub continuous_const).sub
          (continuous_const.mul ((continuous_fst.comp continuous_snd).sub continuous_const))))

private theorem unipotentLeftShift_apply (p₀ p : Unip3 v) :
    unipotentLeftShift v p₀ p = (p₀.1 + p.1, p₀.2.1 + p.2.1, p₀.2.2 + p.2.2 + p₀.1 * p.2.1) :=
  rfl

private theorem preimage_unipotentBall3_unipotentLeftShift {c : ℤ} {p₀ : Unip3 v} (hp₀ : p₀ ∈ unipotentBall3 v c) :
    unipotentLeftShift v p₀ ⁻¹' unipotentBall3 v c = unipotentBall3 v c := by
  ext p
  constructor
  · intro hp
    have hmem := unipotentBall3_mul_mem v (c := c) (p := (-p₀.1, -p₀.2.1, p₀.1 * p₀.2.1 - p₀.2.2))
      (p' := unipotentLeftShift v p₀ p) (unipotentBall3_inv_mem v hp₀) hp
    convert hmem using 1
    obtain ⟨a, b, d⟩ := p
    simp only [unipotentLeftShift_apply, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> ring
  · intro hp
    exact unipotentBall3_mul_mem v hp₀ hp

private theorem measurePreserving_unipotentLeftShift (p₀ : Unip3 v) :
    letI := localBorel ℚ v
    MeasurePreserving (unipotentLeftShift v p₀) (jacquetHaar3 v) (jacquetHaar3 v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt_rat v
  have hT : MeasurePreserving
      (fun q : v.adicCompletion ℚ × v.adicCompletion ℚ => (p₀.2.1 + q.1, (p₀.2.2 + p₀.1 * q.1) + q.2))
      ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)) ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)) :=
    (measurePreserving_add_left (selfDualHaarAt ℚ v) p₀.2.1).skew_product
      (g := fun (a : v.adicCompletion ℚ) (d : v.adicCompletion ℚ) => (p₀.2.2 + p₀.1 * a) + d)
      (((continuous_const.add (continuous_const.mul continuous_fst)).add continuous_snd) :
        Continuous fun q : v.adicCompletion ℚ × v.adicCompletion ℚ => (p₀.2.2 + p₀.1 * q.1) + q.2).measurable
      (Filter.Eventually.of_forall fun a => map_add_left_eq_self (selfDualHaarAt ℚ v) (p₀.2.2 + p₀.1 * a))
  have hshape : (unipotentLeftShift v p₀ : Unip3 v → Unip3 v)
      = fun p : Unip3 v => (p₀.1 + p.1, (p₀.2.1 + p.2.1, (p₀.2.2 + p₀.1 * p.2.1) + p.2.2)) := by
    funext p
    obtain ⟨a, b, d⟩ := p
    simp only [unipotentLeftShift_apply]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    show p₀.2.2 + d + p₀.1 * b = p₀.2.2 + p₀.1 * b + d
    ring
  show MeasurePreserving (unipotentLeftShift v p₀)
    ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)))
    ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)))
  rw [hshape]
  refine MeasurePreserving.skew_product
    (g := fun (_ : v.adicCompletion ℚ) (q : v.adicCompletion ℚ × v.adicCompletion ℚ) =>
      (p₀.2.1 + q.1, (p₀.2.2 + p₀.1 * q.1) + q.2))
    (measurePreserving_add_left (selfDualHaarAt ℚ v) p₀.1) ?_ (Filter.Eventually.of_forall fun _ => hT.map_eq)
  exact ((continuous_const.add (continuous_fst.comp continuous_snd)).prodMk
    ((continuous_const.add (continuous_const.mul (continuous_fst.comp continuous_snd))).add
      (continuous_snd.comp continuous_snd)) :
    Continuous fun r : v.adicCompletion ℚ × (v.adicCompletion ℚ × v.adicCompletion ℚ) =>
      (p₀.2.1 + r.2.1, (p₀.2.2 + p₀.1 * r.2.1) + r.2.2)).measurable

private theorem setIntegral_eq_zero_of_preimage_eq {X : Type*} [MeasurableSpace X] {μ : Measure X} {s : X → X}
    (hs : MeasurePreserving s μ μ) (hemb : MeasurableEmbedding s) {P : Set X} (hP : MeasurableSet P)
    (hsP : s ⁻¹' P = P) {g : X → ℂ} {ω : ℂ} (hω : ω ≠ 1) (hg : ∀ p ∈ P, g (s p) = ω * g p) :
    ∫ p in P, g p ∂μ = 0 := by
  have h1 : ∫ p in P, g (s p) ∂μ = ∫ p in P, g p ∂μ := by
    have h := hs.setIntegral_preimage_emb hemb g P
    rwa [hsP] at h
  have h2 : ∫ p in P, g (s p) ∂μ = ω * ∫ p in P, g p ∂μ := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun hP fun p hp => hg p hp
  have h3 : (1 - ω) * ∫ p in P, g p ∂μ = 0 := by
    rw [sub_mul, one_mul, ← h2, h1, sub_self]
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm hω))

private def jacquetIntegrand (F : LocalGL3 v → ℂ) (p : Unip3 v) : ℂ :=
  psiLocal ℚ v (-(p.1 + p.2.1)) * F (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2)

private theorem jacquetTruncated3_eq_setIntegral_jacquetIntegrand (c : ℤ) (F : LocalGL3 v → ℂ) :
    jacquetTruncated3 v c F
      = (letI := localBorel ℚ v; ∫ p in unipotentBall3 v c, jacquetIntegrand v F p ∂(jacquetHaar3 v)) :=
  rfl

private theorem jacquetIntegrand_shift_eq {F : LocalGL3 v → ℂ} {p : Unip3 v} {Δ : v.adicCompletion ℚ}
    {x' y' z' : v.adicCompletion ℚ} (hx : x' + y' = p.1 + p.2.1 - Δ)
    (hF : F (antidiagonal3 v * upperUnipotent3 x' y' z') = F (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2)) :
    jacquetIntegrand v F (x', y', z') = psiLocal ℚ v Δ * jacquetIntegrand v F p := by
  simp only [jacquetIntegrand, hF]
  rw [show -(x' + y') = Δ + -(p.1 + p.2.1) by rw [hx]; ring, AddChar.map_add_eq_mul, mul_assoc]

private theorem isClosed_valued_le (n : ℤ) :
    IsClosed {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n} := by
  have h : {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n}
      = {x : v.adicCompletion ℚ | Valued.v (x - 0) ≤ WithZero.exp (- -n)} := by
    simp only [sub_zero, neg_neg]
  rw [h]
  exact (isClopen_setOf_valued_sub_le v 0 (-n)).isClosed

private theorem isCompact_valued_le (n : ℤ) :
    IsCompact {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n} := by
  have h : {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n}
      = {x : v.adicCompletion ℚ | Valued.v (x - 0) ≤ WithZero.exp (- -n)} := by
    simp only [sub_zero, neg_neg]
  rw [h]
  exact isCompact_setOf_valued_sub_le v 0 (-n)

private theorem measurableSet_valued_le {φ : Unip3 v → v.adicCompletion ℚ} (hφ : Continuous φ) (n : ℤ) :
    letI := localBorel ℚ v
    MeasurableSet {p : Unip3 v | Valued.v (φ p) ≤ WithZero.exp n} := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  exact ((isClosed_valued_le v n).preimage hφ).measurableSet

private theorem measurableSet_exp_lt_valued {φ : Unip3 v → v.adicCompletion ℚ} (hφ : Continuous φ) (n : ℤ) :
    letI := localBorel ℚ v
    MeasurableSet {p : Unip3 v | WithZero.exp n < Valued.v (φ p)} := by
  letI := localBorel ℚ v
  have h : {p : Unip3 v | WithZero.exp n < Valued.v (φ p)} = {p : Unip3 v | Valued.v (φ p) ≤ WithZero.exp n}ᶜ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  rw [h]
  exact (measurableSet_valued_le v hφ n).compl

private theorem continuous_coordFst : Continuous fun p : Unip3 v => p.1 := continuous_fst
private theorem continuous_coordSnd : Continuous fun p : Unip3 v => p.2.1 := continuous_fst.comp continuous_snd
private theorem continuous_coordThd : Continuous fun p : Unip3 v => p.2.2 := continuous_snd.comp continuous_snd
private theorem continuous_coordMinor : Continuous fun p : Unip3 v => p.2.2 - p.1 * p.2.1 :=
  (continuous_coordThd v).sub ((continuous_coordFst v).mul (continuous_coordSnd v))

private theorem unipotentLeftShift_shearFst (Δ : v.adicCompletion ℚ) (p : Unip3 v) :
    unipotentLeftShift v (-Δ, 0, 0) p = (p.1 - Δ, p.2.1, p.2.2 - Δ * p.2.1) := by
  simp only [unipotentLeftShift_apply, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

private theorem unipotentShift_plainFst (Δ : v.adicCompletion ℚ) (p : Unip3 v) :
    unipotentShift v (-Δ, 0, 0) p = (p.1 - Δ, p.2.1, p.2.2) := by
  simp only [unipotentShift_apply, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

private theorem unipotentLeftShift_plainSnd (Δ : v.adicCompletion ℚ) (p : Unip3 v) :
    unipotentLeftShift v (0, -Δ, 0) p = (p.1, p.2.1 - Δ, p.2.2) := by
  simp only [unipotentLeftShift_apply, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

private theorem unipotentShift_shearSnd (Δ : v.adicCompletion ℚ) (p : Unip3 v) :
    unipotentShift v (0, -Δ, 0) p = (p.1, p.2.1 - Δ, p.2.2 - Δ * p.1) := by
  simp only [unipotentShift_apply, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

private theorem unipotentLeftShift_shearFst_neg (Δ : v.adicCompletion ℚ) (p : Unip3 v) :
    unipotentLeftShift v (- -Δ, 0, 0) (unipotentLeftShift v (-Δ, 0, 0) p) = p := by
  obtain ⟨x, y, z⟩ := p
  simp only [unipotentLeftShift_shearFst]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show x - Δ - -Δ = x
    ring
  · rfl
  · show z - Δ * y - -Δ * y = z
    ring

private theorem unipotentShift_plainFst_neg (Δ : v.adicCompletion ℚ) (p : Unip3 v) :
    unipotentShift v (- -Δ, 0, 0) (unipotentShift v (-Δ, 0, 0) p) = p := by
  obtain ⟨x, y, z⟩ := p
  simp only [unipotentShift_plainFst]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show x - Δ - -Δ = x
    ring
  · rfl
  · rfl

private theorem unipotentLeftShift_plainSnd_neg (Δ : v.adicCompletion ℚ) (p : Unip3 v) :
    unipotentLeftShift v (0, - -Δ, 0) (unipotentLeftShift v (0, -Δ, 0) p) = p := by
  obtain ⟨x, y, z⟩ := p
  simp only [unipotentLeftShift_plainSnd]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rfl
  · show y - Δ - -Δ = y
    ring
  · rfl

private theorem unipotentShift_shearSnd_neg (Δ : v.adicCompletion ℚ) (p : Unip3 v) :
    unipotentShift v (0, - -Δ, 0) (unipotentShift v (0, -Δ, 0) p) = p := by
  obtain ⟨x, y, z⟩ := p
  simp only [unipotentShift_shearSnd]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rfl
  · show y - Δ - -Δ = y
    ring
  · show z - Δ * x - -Δ * x = z
    ring

private theorem preimage_eq_of_mapsTo {X : Type*} {P : Set X} {s s' : X → X} (h : ∀ p ∈ P, s p ∈ P)
    (h' : ∀ p ∈ P, s' p ∈ P) (hinv : ∀ p, s' (s p) = p) : s ⁻¹' P = P := by
  ext p
  constructor
  · intro hp
    have := h' _ hp
    rwa [hinv] at this
  · intro hp
    exact h p hp

private theorem valued_lt_of_exp_lt {a Δ : v.adicCompletion ℚ} (hΔ : Valued.v Δ ≤ WithZero.exp 1) {c : ℤ} (hc : 1 ≤ c)
    (ha : WithZero.exp c < Valued.v a) : Valued.v Δ < Valued.v a :=
  lt_of_le_of_lt (hΔ.trans (WithZero.exp_le_exp.mpr hc)) ha

private theorem valued_sub_eq_of_exp_lt {a Δ : v.adicCompletion ℚ} (hΔ : Valued.v Δ ≤ WithZero.exp 1) {c : ℤ}
    (hc : 1 ≤ c) (ha : WithZero.exp c < Valued.v a) : Valued.v (a - Δ) = Valued.v a :=
  Valuation.map_sub_eq_of_lt_left _ (valued_lt_of_exp_lt v hΔ hc ha)

private theorem valued_mul_le_exp {Δ b : v.adicCompletion ℚ} (hΔ : Valued.v Δ ≤ WithZero.exp 1) {k : ℤ}
    (hb : Valued.v b ≤ WithZero.exp k) : Valued.v (Δ * b) ≤ WithZero.exp (1 + k) := by
  rw [Valuation.map_mul, WithZero.exp_add]
  exact mul_le_mul' hΔ hb

private theorem exp_le_mul_exp_neg {a : v.adicCompletion ℚ} {c : ℤ} (ha : WithZero.exp c < Valued.v a) {M : ℕ} {n : ℤ}
    (h : n ≤ c - M) : WithZero.exp n ≤ Valued.v a * WithZero.exp (-(M : ℤ)) :=
  calc WithZero.exp n ≤ WithZero.exp (c + -(M : ℤ)) := WithZero.exp_le_exp.mpr (by omega)
    _ = WithZero.exp c * WithZero.exp (-(M : ℤ)) := WithZero.exp_add _ _
    _ ≤ Valued.v a * WithZero.exp (-(M : ℤ)) := mul_le_mul_left ha.le _

private theorem exp_le_mul_mul_exp_neg {a : v.adicCompletion ℚ} {c : ℤ} (ha : WithZero.exp c < Valued.v a) {M : ℕ}
    {n : ℤ} (h : n ≤ c + c - M) :
    WithZero.exp n ≤ Valued.v a * Valued.v a * WithZero.exp (-(M : ℤ)) :=
  calc WithZero.exp n ≤ WithZero.exp (c + c + -(M : ℤ)) := WithZero.exp_le_exp.mpr (by omega)
    _ = WithZero.exp c * WithZero.exp c * WithZero.exp (-(M : ℤ)) := by rw [WithZero.exp_add, WithZero.exp_add]
    _ ≤ Valued.v a * Valued.v a * WithZero.exp (-(M : ℤ)) := mul_le_mul' (mul_le_mul' ha.le ha.le) le_rfl

private theorem ne_zero_of_exp_lt {a : v.adicCompletion ℚ} {n : ℤ} (ha : WithZero.exp n < Valued.v a) : a ≠ 0 :=
  (Valuation.ne_zero_iff _).mp (lt_of_le_of_lt zero_le' ha).ne'

private def partXA (c : ℤ) (M : ℕ) : Set (Unip3 v) :=
  {p | WithZero.exp c < Valued.v p.1 ∧ Valued.v p.1 ≤ WithZero.exp (c + 1) ∧ Valued.v p.2.1 ≤ WithZero.exp (c + 1) ∧
    Valued.v p.2.2 ≤ WithZero.exp (2 * (c + 1)) ∧ Valued.v (p.2.2 - p.1 * p.2.1) ≤ WithZero.exp (2 * c - M - 1)}

private def partXB (c : ℤ) (M : ℕ) : Set (Unip3 v) :=
  {p | WithZero.exp c < Valued.v p.1 ∧ Valued.v p.1 ≤ WithZero.exp (c + 1) ∧ Valued.v p.2.1 ≤ WithZero.exp (c + 1) ∧
    Valued.v p.2.2 ≤ WithZero.exp (2 * (c + 1)) ∧ WithZero.exp (2 * c - M - 1) < Valued.v (p.2.2 - p.1 * p.2.1)}

private def partWS (c : ℤ) (M : ℕ) : Set (Unip3 v) :=
  {p | Valued.v p.1 ≤ WithZero.exp c ∧ WithZero.exp c < Valued.v p.2.1 ∧ Valued.v p.2.1 ≤ WithZero.exp (c + 1) ∧
    Valued.v p.2.2 ≤ WithZero.exp (2 * c - M - 1)}

private def partWB (c : ℤ) (M : ℕ) : Set (Unip3 v) :=
  {p | Valued.v p.1 ≤ WithZero.exp c ∧ Valued.v p.2.1 ≤ WithZero.exp (c + 1) ∧
    WithZero.exp (2 * c - M - 1) < Valued.v p.2.2 ∧ Valued.v p.2.2 ≤ WithZero.exp (2 * (c + 1)) ∧
    (WithZero.exp c < Valued.v p.2.1 ∨ WithZero.exp (2 * c) < Valued.v p.2.2)}

private theorem measurableSet_partXA (c : ℤ) (M : ℕ) :
    letI := localBorel ℚ v
    MeasurableSet (partXA v c M) := by
  letI := localBorel ℚ v
  simp only [partXA, Set.setOf_and]
  exact (measurableSet_exp_lt_valued v (continuous_coordFst v) c).inter
    ((measurableSet_valued_le v (continuous_coordFst v) (c + 1)).inter
      ((measurableSet_valued_le v (continuous_coordSnd v) (c + 1)).inter
        ((measurableSet_valued_le v (continuous_coordThd v) (2 * (c + 1))).inter
          (measurableSet_valued_le v (continuous_coordMinor v) (2 * c - M - 1)))))

private theorem measurableSet_partXB (c : ℤ) (M : ℕ) :
    letI := localBorel ℚ v
    MeasurableSet (partXB v c M) := by
  letI := localBorel ℚ v
  simp only [partXB, Set.setOf_and]
  exact (measurableSet_exp_lt_valued v (continuous_coordFst v) c).inter
    ((measurableSet_valued_le v (continuous_coordFst v) (c + 1)).inter
      ((measurableSet_valued_le v (continuous_coordSnd v) (c + 1)).inter
        ((measurableSet_valued_le v (continuous_coordThd v) (2 * (c + 1))).inter
          (measurableSet_exp_lt_valued v (continuous_coordMinor v) (2 * c - M - 1)))))

private theorem measurableSet_partWS (c : ℤ) (M : ℕ) :
    letI := localBorel ℚ v
    MeasurableSet (partWS v c M) := by
  letI := localBorel ℚ v
  simp only [partWS, Set.setOf_and]
  exact (measurableSet_valued_le v (continuous_coordFst v) c).inter
    ((measurableSet_exp_lt_valued v (continuous_coordSnd v) c).inter
      ((measurableSet_valued_le v (continuous_coordSnd v) (c + 1)).inter
        (measurableSet_valued_le v (continuous_coordThd v) (2 * c - M - 1))))

private theorem measurableSet_partWB (c : ℤ) (M : ℕ) :
    letI := localBorel ℚ v
    MeasurableSet (partWB v c M) := by
  letI := localBorel ℚ v
  simp only [partWB, Set.setOf_and, Set.setOf_or]
  exact (measurableSet_valued_le v (continuous_coordFst v) c).inter
    ((measurableSet_valued_le v (continuous_coordSnd v) (c + 1)).inter
      ((measurableSet_exp_lt_valued v (continuous_coordThd v) (2 * c - M - 1)).inter
        ((measurableSet_valued_le v (continuous_coordThd v) (2 * (c + 1))).inter
          ((measurableSet_exp_lt_valued v (continuous_coordSnd v) c).union
            (measurableSet_exp_lt_valued v (continuous_coordThd v) (2 * c))))))

private theorem mapsTo_partXA {c : ℤ} {M : ℕ} (hc : 2 * (M : ℤ) + 3 ≤ c) {Δ : v.adicCompletion ℚ}
    (hΔ : Valued.v Δ ≤ WithZero.exp 1) {p : Unip3 v} (hp : p ∈ partXA v c M) :
    unipotentLeftShift v (-Δ, 0, 0) p ∈ partXA v c M := by
  rw [unipotentLeftShift_shearFst]
  simp only [partXA, Set.mem_setOf_eq] at hp ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := hp
  have hsub : Valued.v (p.1 - Δ) = Valued.v p.1 := valued_sub_eq_of_exp_lt v hΔ (by omega) h1
  have hΔy : Valued.v (Δ * p.2.1) ≤ WithZero.exp (2 * (c + 1)) :=
    (valued_mul_le_exp v hΔ h3).trans (WithZero.exp_le_exp.mpr (by omega))
  refine ⟨by rw [hsub]; exact h1, by rw [hsub]; exact h2, h3, (Valuation.map_sub _ _ _).trans (max_le h4 hΔy), ?_⟩
  have e : p.2.2 - Δ * p.2.1 - (p.1 - Δ) * p.2.1 = p.2.2 - p.1 * p.2.1 := by ring
  rw [e]
  exact h5

private theorem mapsTo_partXB {c : ℤ} {M : ℕ} (hc : 2 * (M : ℤ) + 3 ≤ c) {Δ : v.adicCompletion ℚ}
    (hΔ : Valued.v Δ ≤ WithZero.exp 1) {p : Unip3 v} (hp : p ∈ partXB v c M) :
    unipotentShift v (-Δ, 0, 0) p ∈ partXB v c M := by
  rw [unipotentShift_plainFst]
  simp only [partXB, Set.mem_setOf_eq] at hp ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := hp
  have hsub : Valued.v (p.1 - Δ) = Valued.v p.1 := valued_sub_eq_of_exp_lt v hΔ (by omega) h1
  have hΔy : Valued.v (Δ * p.2.1) < Valued.v (p.2.2 - p.1 * p.2.1) :=
    lt_of_le_of_lt ((valued_mul_le_exp v hΔ h3).trans (WithZero.exp_le_exp.mpr (by omega))) h5
  refine ⟨by rw [hsub]; exact h1, by rw [hsub]; exact h2, h3, h4, ?_⟩
  have e : p.2.2 - (p.1 - Δ) * p.2.1 = (p.2.2 - p.1 * p.2.1) + Δ * p.2.1 := by ring
  rw [e, Valuation.map_add_eq_of_lt_left _ hΔy]
  exact h5

private theorem mapsTo_partWS {c : ℤ} {M : ℕ} (hc : 2 * (M : ℤ) + 3 ≤ c) {Δ : v.adicCompletion ℚ}
    (hΔ : Valued.v Δ ≤ WithZero.exp 1) {p : Unip3 v} (hp : p ∈ partWS v c M) :
    unipotentLeftShift v (0, -Δ, 0) p ∈ partWS v c M := by
  rw [unipotentLeftShift_plainSnd]
  simp only [partWS, Set.mem_setOf_eq] at hp ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hsub : Valued.v (p.2.1 - Δ) = Valued.v p.2.1 := valued_sub_eq_of_exp_lt v hΔ (by omega) h2
  exact ⟨h1, by rw [hsub]; exact h2, by rw [hsub]; exact h3, h4⟩

private theorem mapsTo_partWB {c : ℤ} {M : ℕ} (hc : 2 * (M : ℤ) + 3 ≤ c) {Δ : v.adicCompletion ℚ}
    (hΔ : Valued.v Δ ≤ WithZero.exp 1) {p : Unip3 v} (hp : p ∈ partWB v c M) :
    unipotentShift v (0, -Δ, 0) p ∈ partWB v c M := by
  rw [unipotentShift_shearSnd]
  simp only [partWB, Set.mem_setOf_eq] at hp ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := hp
  have hΔx : Valued.v (Δ * p.1) < Valued.v p.2.2 :=
    lt_of_le_of_lt ((valued_mul_le_exp v hΔ h1).trans (WithZero.exp_le_exp.mpr (by omega))) h3
  have hz : Valued.v (p.2.2 - Δ * p.1) = Valued.v p.2.2 := Valuation.map_sub_eq_of_lt_left _ hΔx
  have hΔ' : Valued.v Δ ≤ WithZero.exp (c + 1) := hΔ.trans (WithZero.exp_le_exp.mpr (by omega))
  refine ⟨h1, (Valuation.map_sub _ _ _).trans (max_le h2 hΔ'), by rw [hz]; exact h3, by rw [hz]; exact h4, ?_⟩
  rcases h5 with h5 | h5
  · left
    rw [valued_sub_eq_of_exp_lt v hΔ (by omega) h5]
    exact h5
  · right
    rw [hz]
    exact h5

private theorem setIntegral_partXA_eq_zero {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {F : LocalGL3 v → ℂ}
    (hF : F ∈ principalSeries3 v χ) {M : ℕ}
    (hm : ∀ (g k : LocalGL3 v), k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v →
      (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
          - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(M : ℤ))) →
        F (g * k) = F g)
    {f : ℕ}
    (hχf : ∀ (i : Fin 3) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(f : ℤ) - 1) → χ i u = 1)
    (hMf : f + 1 ≤ M) {Δ : v.adicCompletion ℚ} (hΔ : Valued.v Δ ≤ WithZero.exp 1) (hψ : psiLocal ℚ v Δ ≠ 1) {c : ℤ}
    (hc : 2 * (M : ℤ) + 3 ≤ c) :
    letI := localBorel ℚ v
    ∫ p in partXA v c M, jacquetIntegrand v F p ∂(jacquetHaar3 v) = 0 := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  have hΔn : Valued.v (-Δ) ≤ WithZero.exp 1 := by
    rw [Valuation.map_neg]
    exact hΔ
  refine setIntegral_eq_zero_of_preimage_eq (measurePreserving_unipotentLeftShift v (-Δ, 0, 0))
    (unipotentLeftShift v (-Δ, 0, 0)).measurableEmbedding (measurableSet_partXA v c M) ?_ hψ ?_
  · exact preimage_eq_of_mapsTo (fun p hp => mapsTo_partXA v hc hΔ hp) (fun p hp => mapsTo_partXA v hc hΔn hp)
      (unipotentLeftShift_shearFst_neg v Δ)
  · intro p hp
    simp only [partXA, Set.mem_setOf_eq] at hp
    obtain ⟨h1, -, -, -, h5⟩ := hp
    rw [unipotentLeftShift_shearFst]
    refine jacquetIntegrand_shift_eq v (by ring) (principalSeries3_apply_shearShiftByX_eq v hF hm hχf hMf
      (ne_zero_of_exp_lt v h1) (valued_lt_of_exp_lt v hΔ (by omega) h1) (hΔ.trans (exp_le_mul_exp_neg v h1 (by omega)))
      (hΔ.trans (exp_le_mul_mul_exp_neg v h1 (by omega))) ?_)
    calc Valued.v Δ * Valued.v (p.2.2 - p.1 * p.2.1) ≤ WithZero.exp 1 * WithZero.exp (2 * c - M - 1) :=
          mul_le_mul' hΔ h5
      _ = WithZero.exp (1 + (2 * c - M - 1)) := (WithZero.exp_add _ _).symm
      _ ≤ Valued.v p.1 * Valued.v p.1 * WithZero.exp (-(M : ℤ)) := exp_le_mul_mul_exp_neg v h1 (by omega)

private theorem setIntegral_partXB_eq_zero {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {F : LocalGL3 v → ℂ}
    (hF : F ∈ principalSeries3 v χ) {M : ℕ}
    (hm : ∀ (g k : LocalGL3 v), k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v →
      (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
          - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(M : ℤ))) →
        F (g * k) = F g)
    {f : ℕ}
    (hχf : ∀ (i : Fin 3) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(f : ℤ) - 1) → χ i u = 1)
    (hMf : f + 1 ≤ M) {Δ : v.adicCompletion ℚ} (hΔ : Valued.v Δ ≤ WithZero.exp 1) (hψ : psiLocal ℚ v Δ ≠ 1) {c : ℤ}
    (hc : 2 * (M : ℤ) + 3 ≤ c) :
    letI := localBorel ℚ v
    ∫ p in partXB v c M, jacquetIntegrand v F p ∂(jacquetHaar3 v) = 0 := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  have hΔn : Valued.v (-Δ) ≤ WithZero.exp 1 := by
    rw [Valuation.map_neg]
    exact hΔ
  refine setIntegral_eq_zero_of_preimage_eq (measurePreserving_unipotentShift v (-Δ, 0, 0))
    (unipotentShift v (-Δ, 0, 0)).measurableEmbedding (measurableSet_partXB v c M) ?_ hψ ?_
  · exact preimage_eq_of_mapsTo (fun p hp => mapsTo_partXB v hc hΔ hp) (fun p hp => mapsTo_partXB v hc hΔn hp)
      (unipotentShift_plainFst_neg v Δ)
  · intro p hp
    simp only [partXB, Set.mem_setOf_eq] at hp
    obtain ⟨-, -, h3, -, h5⟩ := hp
    have h5' : WithZero.exp (2 * c - M - 1) < Valued.v (p.1 * p.2.1 - p.2.2) := by
      rwa [Valuation.map_sub_swap]
    have hΔy : Valued.v (Δ * p.2.1) ≤ WithZero.exp (1 + (c + 1)) := valued_mul_le_exp v hΔ h3
    rw [unipotentShift_plainFst]
    exact jacquetIntegrand_shift_eq v (by ring) (principalSeries3_apply_plainShiftByMinor_eq v hF hm hχf hMf
      (ne_zero_of_exp_lt v h5') (lt_of_le_of_lt (hΔy.trans (WithZero.exp_le_exp.mpr (by omega))) h5')
      (hΔ.trans (exp_le_mul_exp_neg v h5' (by omega))) (hΔy.trans (exp_le_mul_exp_neg v h5' (by omega))))

private theorem setIntegral_partWS_eq_zero {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {F : LocalGL3 v → ℂ}
    (hF : F ∈ principalSeries3 v χ) {M : ℕ}
    (hm : ∀ (g k : LocalGL3 v), k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v →
      (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
          - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(M : ℤ))) →
        F (g * k) = F g)
    {f : ℕ}
    (hχf : ∀ (i : Fin 3) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(f : ℤ) - 1) → χ i u = 1)
    (hMf : f + 1 ≤ M) {Δ : v.adicCompletion ℚ} (hΔ : Valued.v Δ ≤ WithZero.exp 1) (hψ : psiLocal ℚ v Δ ≠ 1) {c : ℤ}
    (hc : 2 * (M : ℤ) + 3 ≤ c) :
    letI := localBorel ℚ v
    ∫ p in partWS v c M, jacquetIntegrand v F p ∂(jacquetHaar3 v) = 0 := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  have hΔn : Valued.v (-Δ) ≤ WithZero.exp 1 := by
    rw [Valuation.map_neg]
    exact hΔ
  refine setIntegral_eq_zero_of_preimage_eq (measurePreserving_unipotentLeftShift v (0, -Δ, 0))
    (unipotentLeftShift v (0, -Δ, 0)).measurableEmbedding (measurableSet_partWS v c M) ?_ hψ ?_
  · exact preimage_eq_of_mapsTo (fun p hp => mapsTo_partWS v hc hΔ hp) (fun p hp => mapsTo_partWS v hc hΔn hp)
      (unipotentLeftShift_plainSnd_neg v Δ)
  · intro p hp
    simp only [partWS, Set.mem_setOf_eq] at hp
    obtain ⟨-, h2, -, h4⟩ := hp
    rw [unipotentLeftShift_plainSnd]
    refine jacquetIntegrand_shift_eq v (by ring) (principalSeries3_apply_plainSecondShiftByY_eq v hF hm hχf hMf p.1
      p.2.2 (ne_zero_of_exp_lt v h2) (valued_lt_of_exp_lt v hΔ (by omega) h2)
      (hΔ.trans (exp_le_mul_exp_neg v h2 (by omega))) (hΔ.trans (exp_le_mul_mul_exp_neg v h2 (by omega))) ?_)
    calc Valued.v Δ * Valued.v p.2.2 ≤ WithZero.exp 1 * WithZero.exp (2 * c - M - 1) := mul_le_mul' hΔ h4
      _ = WithZero.exp (1 + (2 * c - M - 1)) := (WithZero.exp_add _ _).symm
      _ ≤ Valued.v p.2.1 * Valued.v p.2.1 * WithZero.exp (-(M : ℤ)) := exp_le_mul_mul_exp_neg v h2 (by omega)

private theorem setIntegral_partWB_eq_zero {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {F : LocalGL3 v → ℂ}
    (hF : F ∈ principalSeries3 v χ) {M : ℕ}
    (hm : ∀ (g k : LocalGL3 v), k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v →
      (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
          - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(M : ℤ))) →
        F (g * k) = F g)
    {f : ℕ}
    (hχf : ∀ (i : Fin 3) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(f : ℤ) - 1) → χ i u = 1)
    (hMf : f + 1 ≤ M) {Δ : v.adicCompletion ℚ} (hΔ : Valued.v Δ ≤ WithZero.exp 1) (hψ : psiLocal ℚ v Δ ≠ 1) {c : ℤ}
    (hc : 2 * (M : ℤ) + 3 ≤ c) :
    letI := localBorel ℚ v
    ∫ p in partWB v c M, jacquetIntegrand v F p ∂(jacquetHaar3 v) = 0 := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  have hΔn : Valued.v (-Δ) ≤ WithZero.exp 1 := by
    rw [Valuation.map_neg]
    exact hΔ
  refine setIntegral_eq_zero_of_preimage_eq (measurePreserving_unipotentShift v (0, -Δ, 0))
    (unipotentShift v (0, -Δ, 0)).measurableEmbedding (measurableSet_partWB v c M) ?_ hψ ?_
  · exact preimage_eq_of_mapsTo (fun p hp => mapsTo_partWB v hc hΔ hp) (fun p hp => mapsTo_partWB v hc hΔn hp)
      (unipotentShift_shearSnd_neg v Δ)
  · intro p hp
    simp only [partWB, Set.mem_setOf_eq] at hp
    obtain ⟨h1, -, h3, -, -⟩ := hp
    have hΔx : Valued.v (Δ * p.1) ≤ WithZero.exp (1 + c) := valued_mul_le_exp v hΔ h1
    rw [unipotentShift_shearSnd]
    exact jacquetIntegrand_shift_eq v (by ring) (principalSeries3_apply_shearSecondShiftByZ_eq v hF hm hχf hMf p.2.1
      (ne_zero_of_exp_lt v h3) (lt_of_le_of_lt (hΔx.trans (WithZero.exp_le_exp.mpr (by omega))) h3)
      (hΔ.trans (exp_le_mul_exp_neg v h3 (by omega))) (hΔx.trans (exp_le_mul_exp_neg v h3 (by omega))))

private theorem unipotentBall3_succ_diff_eq (c : ℤ) (M : ℕ) :
    unipotentBall3 v (c + 1) \ unipotentBall3 v c = (partXA v c M ∪ partXB v c M) ∪ (partWS v c M ∪ partWB v c M) := by
  ext p
  simp only [Set.mem_diff, Set.mem_union, mem_unipotentBall3_iff, partXA, partXB, partWS, partWB, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hx', hy', hz'⟩, hnot⟩
    rcases le_or_gt (Valued.v p.1) (WithZero.exp c) with hx | hx
    · rcases le_or_gt (Valued.v p.2.2) (WithZero.exp (2 * c - M - 1)) with hz | hz
      · have hy : ¬ Valued.v p.2.1 ≤ WithZero.exp c :=
          fun hy => hnot ⟨hx, hy, hz.trans (WithZero.exp_le_exp.mpr (by omega))⟩
        exact Or.inr (Or.inl ⟨hx, not_le.mp hy, hy', hz⟩)
      · refine Or.inr (Or.inr ⟨hx, hy', hz, hz', ?_⟩)
        by_cases hy : Valued.v p.2.1 ≤ WithZero.exp c
        · exact Or.inr (not_le.mp fun hz2 => hnot ⟨hx, hy, hz2⟩)
        · exact Or.inl (not_le.mp hy)
    · rcases le_or_gt (Valued.v (p.2.2 - p.1 * p.2.1)) (WithZero.exp (2 * c - M - 1)) with hw | hw
      · exact Or.inl (Or.inl ⟨hx, hx', hy', hz', hw⟩)
      · exact Or.inl (Or.inr ⟨hx, hx', hy', hz', hw⟩)
  · rintro ((⟨hx, hx', hy', hz', -⟩ | ⟨hx, hx', hy', hz', -⟩) | (⟨hx, hy, hy', hz⟩ | ⟨hx, hy', hz, hz', hor⟩))
    · exact ⟨⟨hx', hy', hz'⟩, fun hB => absurd hB.1 (not_le.mpr hx)⟩
    · exact ⟨⟨hx', hy', hz'⟩, fun hB => absurd hB.1 (not_le.mpr hx)⟩
    · refine ⟨⟨hx.trans (WithZero.exp_le_exp.mpr (by omega)), hy', hz.trans (WithZero.exp_le_exp.mpr (by omega))⟩, ?_⟩
      exact fun hB => absurd hB.2.1 (not_le.mpr hy)
    · refine ⟨⟨hx.trans (WithZero.exp_le_exp.mpr (by omega)), hy', hz'⟩, fun hB => ?_⟩
      rcases hor with h | h
      · exact absurd hB.2.1 (not_le.mpr h)
      · exact absurd hB.2.2 (not_le.mpr h)

private theorem disjoint_partXA_partXB (c : ℤ) (M : ℕ) : Disjoint (partXA v c M) (partXB v c M) := by
  refine Set.disjoint_left.mpr fun p hA hB => ?_
  simp only [partXA, partXB, Set.mem_setOf_eq] at hA hB
  exact absurd hA.2.2.2.2 (not_le.mpr hB.2.2.2.2)

private theorem disjoint_partWS_partWB (c : ℤ) (M : ℕ) : Disjoint (partWS v c M) (partWB v c M) := by
  refine Set.disjoint_left.mpr fun p hA hB => ?_
  simp only [partWS, partWB, Set.mem_setOf_eq] at hA hB
  exact absurd hA.2.2.2 (not_le.mpr hB.2.2.1)

private theorem disjoint_partsX_partsW (c : ℤ) (M : ℕ) :
    Disjoint (partXA v c M ∪ partXB v c M) (partWS v c M ∪ partWB v c M) := by
  refine Set.disjoint_left.mpr fun p hX hW => ?_
  have hx : WithZero.exp c < Valued.v p.1 := by
    rcases hX with h | h
    · simp only [partXA, Set.mem_setOf_eq] at h
      exact h.1
    · simp only [partXB, Set.mem_setOf_eq] at h
      exact h.1
  have hx' : Valued.v p.1 ≤ WithZero.exp c := by
    rcases hW with h | h
    · simp only [partWS, Set.mem_setOf_eq] at h
      exact h.1
    · simp only [partWB, Set.mem_setOf_eq] at h
      exact h.1
  exact absurd hx' (not_le.mpr hx)

private theorem isCompact_unipotentBall3 (c : ℤ) : IsCompact (unipotentBall3 v c) := by
  have h : unipotentBall3 v c
      = {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c} ×ˢ
        ({y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp c} ×ˢ
          {z : v.adicCompletion ℚ | Valued.v z ≤ WithZero.exp (2 * c)}) := by
    ext p
    simp only [mem_unipotentBall3_iff, Set.mem_prod, Set.mem_setOf_eq]
  rw [h]
  exact (isCompact_valued_le v c).prod ((isCompact_valued_le v c).prod (isCompact_valued_le v (2 * c)))

private theorem continuous_upperUnipotent3_coords :
    Continuous fun p : Unip3 v => (upperUnipotent3 p.1 p.2.1 p.2.2 : LocalGL3 v) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun p : Unip3 v =>
      (!![1, p.1, p.2.2; 0, 1, p.2.1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun p : Unip3 v =>
      (!![1, -p.1, p.1 * p.2.1 - p.2.2; 0, 1, -p.2.1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem continuous_jacquetIntegrand {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {F : LocalGL3 v → ℂ}
    (hF : F ∈ principalSeries3 v χ) : Continuous (jacquetIntegrand v F) := by
  have hFc : Continuous F := (isLocallyConstant_of_mem_principalSeries3 hF).continuous
  show Continuous fun p : Unip3 v =>
    psiLocal ℚ v (-(p.1 + p.2.1)) * F (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2)
  exact ((continuous_psiLocal (K := ℚ) (v := v)).comp (((continuous_coordFst v).add (continuous_coordSnd v)).neg)).mul
    (hFc.comp (continuous_const.mul (continuous_upperUnipotent3_coords v)))

private theorem integrableOn_jacquetIntegrand {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {F : LocalGL3 v → ℂ}
    (hF : F ∈ principalSeries3 v χ) (c : ℤ) :
    letI := localBorel ℚ v
    IntegrableOn (jacquetIntegrand v F) (unipotentBall3 v c) (jacquetHaar3 v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt_rat v
  show IntegrableOn (jacquetIntegrand v F) (unipotentBall3 v c)
    ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)))
  exact (continuous_jacquetIntegrand v hF).continuousOn.integrableOn_compact (isCompact_unipotentBall3 v c)

private theorem measurableSet_unipotentBall3 (c : ℤ) :
    letI := localBorel ℚ v
    MeasurableSet (unipotentBall3 v c) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  exact (isCompact_unipotentBall3 v c).isClosed.measurableSet

private theorem exists_valued_le_exp_one_psiLocal_ne_one :
    ∃ Δ : v.adicCompletion ℚ, Valued.v Δ ≤ WithZero.exp 1 ∧ psiLocal ℚ v Δ ≠ 1 := by
  by_contra hcon
  have h1 : (1 : ℤ) ∈ {n : ℤ | ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → psiLocal ℚ v x = 1} := by
    intro x hx
    by_contra hne
    exact hcon ⟨x, hx, hne⟩
  obtain ⟨x₀, hx₀⟩ := AddChar.ne_one_iff.mp (psiLocal_ne_one ℚ v)
  obtain ⟨n₀, hn₀⟩ := exists_valued_le_exp v x₀
  have hbdd : BddAbove {n : ℤ | ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → psiLocal ℚ v x = 1} := by
    refine ⟨n₀, fun n hn => ?_⟩
    have hn' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → psiLocal ℚ v x = 1 := hn
    by_contra hlt
    rw [not_le] at hlt
    exact hx₀ (hn' x₀ (hn₀.trans (WithZero.exp_le_exp.mpr hlt.le)))
  have hkey := addCharLevel_psiLocal_rat v
  rw [addCharLevel_def] at hkey
  have hle : (1 : ℤ) ≤ 0 := (le_csSup hbdd h1).trans_eq hkey
  omega

private theorem jacquetTruncated3_add_one_eq {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {F : LocalGL3 v → ℂ}
    (hF : F ∈ principalSeries3 v χ) {M : ℕ}
    (hm : ∀ (g k : LocalGL3 v), k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v →
      (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
          - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(M : ℤ))) →
        F (g * k) = F g)
    {f : ℕ}
    (hχf : ∀ (i : Fin 3) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(f : ℤ) - 1) → χ i u = 1)
    (hMf : f + 1 ≤ M) {c : ℤ} (hc : 2 * (M : ℤ) + 3 ≤ c) :
    jacquetTruncated3 v (c + 1) F = jacquetTruncated3 v c F := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  obtain ⟨Δ, hΔ, hψ⟩ := exists_valued_le_exp_one_psiLocal_ne_one v
  rw [jacquetTruncated3_eq_setIntegral_jacquetIntegrand, jacquetTruncated3_eq_setIntegral_jacquetIntegrand]
  have hint : IntegrableOn (jacquetIntegrand v F) (unipotentBall3 v (c + 1)) (jacquetHaar3 v) :=
    integrableOn_jacquetIntegrand v hF (c + 1)
  have hpart := unipotentBall3_succ_diff_eq v c M
  have hall : (partXA v c M ∪ partXB v c M) ∪ (partWS v c M ∪ partWB v c M) ⊆ unipotentBall3 v (c + 1) := by
    rw [← hpart]
    exact Set.diff_subset
  have hX : partXA v c M ∪ partXB v c M ⊆ unipotentBall3 v (c + 1) := Set.subset_union_left.trans hall
  have hW : partWS v c M ∪ partWB v c M ⊆ unipotentBall3 v (c + 1) := Set.subset_union_right.trans hall
  have hdiff := setIntegral_diff (measurableSet_unipotentBall3 v c) hint (unipotentBall3_mono v (by omega))
  have hzero : ∫ p in unipotentBall3 v (c + 1) \ unipotentBall3 v c, jacquetIntegrand v F p ∂(jacquetHaar3 v) = 0 := by
    rw [hpart, setIntegral_union (disjoint_partsX_partsW v c M)
        ((measurableSet_partWS v c M).union (measurableSet_partWB v c M)) (hint.mono_set hX) (hint.mono_set hW),
      setIntegral_union (disjoint_partXA_partXB v c M) (measurableSet_partXB v c M)
        (hint.mono_set (Set.subset_union_left.trans hX)) (hint.mono_set (Set.subset_union_right.trans hX)),
      setIntegral_union (disjoint_partWS_partWB v c M) (measurableSet_partWB v c M)
        (hint.mono_set (Set.subset_union_left.trans hW)) (hint.mono_set (Set.subset_union_right.trans hW)),
      setIntegral_partXA_eq_zero v hF hm hχf hMf hΔ hψ hc, setIntegral_partXB_eq_zero v hF hm hχf hMf hΔ hψ hc,
      setIntegral_partWS_eq_zero v hF hm hχf hMf hΔ hψ hc, setIntegral_partWB_eq_zero v hF hm hχf hMf hΔ hψ hc,
      add_zero, add_zero]
  rw [hzero] at hdiff
  exact sub_eq_zero.mp hdiff.symm

private theorem exists_le_forall_jacquetTruncated3_eq_of_congruence (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (m f : ℕ)
    (hχf : ∀ (i : Fin 3) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(f : ℤ) - 1) → χ i u = 1) :
    ∃ c₀ : ℕ, c₀ ≤ 2 * (m + f) + 8 ∧ ∀ F : LocalGL3 v → ℂ, F ∈ principalSeries3 v χ →
      (∀ (g k : LocalGL3 v), k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v →
        (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
            - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))) →
          F (g * k) = F g) →
      ∀ c : ℤ, (c₀ : ℤ) ≤ c → jacquetTruncated3 v c F = jacquetTruncated3 v c₀ F := by
  obtain ⟨M, hmM, hfM, hMle⟩ : ∃ M : ℕ, m ≤ M ∧ f + 1 ≤ M ∧ M ≤ m + f + 1 :=
    ⟨max m (f + 1), le_max_left _ _, le_max_right _ _, max_le (by omega) (by omega)⟩
  refine ⟨2 * M + 3, by omega, fun F hF hm c hc => ?_⟩
  have hm' : ∀ (g k : LocalGL3 v), k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v →
      (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
          - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(M : ℤ))) →
        F (g * k) = F g :=
    fun g k hk hk' => hm g k hk fun i j => (hk' i j).trans (WithZero.exp_le_exp.mpr (by omega))
  have hstep : ∀ n : ℕ,
      jacquetTruncated3 v (((2 * M + 3 : ℕ) : ℤ) + n) F = jacquetTruncated3 v ((2 * M + 3 : ℕ) : ℤ) F := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← ih, ← jacquetTruncated3_add_one_eq v hF hm' hχf hfM (c := ((2 * M + 3 : ℕ) : ℤ) + n) (by omega)]
      congr 1
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hc)
  have hcn : c = ((2 * M + 3 : ℕ) : ℤ) + n := by omega
  rw [hcn]
  exact hstep n

end

end TranslatedJacquetStabilisation

end

open LanglandsTunnell LanglandsTunnell.CubicInduction TranslatedJacquetStabilisation in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (g : LocalGL3 v) :
    letI := localBorel ℚ v
    ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c →
      IntegrableOn (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => psiLocal ℚ v (-(p.1 +
        p.2.1)) * (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v ν Φ)) (antidiagonal3 v * upperUnipotent3 p.1
        p.2.1 p.2.2)) (unipotentBall3 v c) (jacquetHaar3 v) ∧
      jacquetTruncated3 v c (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v ν Φ)) = jacquetTruncated3 v c₀
        (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v ν Φ)) := by
  letI := localBorel ℚ v
  have hφ : cellSectionOf v ν Φ ∈ principalSeries3 v ν := cellSectionOf_mem_principalSeries3 v hν hΦ.1 hΦ.2
  have hF : gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v ν Φ) ∈ principalSeries3 v ν :=
    rightTranslate_mem_principalSeries3 hφ g
  obtain ⟨M, hM⟩ := exists_invariance_level v hF
  obtain ⟨f, hνf⟩ := exists_forall_valued_sub_one_le_imp_eq_one_of_isLocallyConstant v ν hν
  obtain ⟨c₀, -, hc₀⟩ := exists_le_forall_jacquetTruncated3_eq_of_congruence v ν M f hνf
  exact ⟨c₀, fun c hc => ⟨integrableOn_jacquetIntegrand v hF c, hc₀ _ hF hM c hc⟩⟩

end S_LanglandsTunnell_CubicInduction_exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf (solution)
