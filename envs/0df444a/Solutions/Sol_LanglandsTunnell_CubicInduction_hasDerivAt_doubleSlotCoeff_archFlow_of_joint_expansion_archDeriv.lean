-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.hasDerivAt_doubleSlotCoeff_archFlow_of_joint_expansion_archDeriv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/cb9a9a7a-264b-5005-845f-2c2a4ea73ce8

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmoothSpace3
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_hasDerivAt_apply_mul_archRealLift3_of_isArchSmooth3
import Theorems.Thm_LanglandsTunnell_CubicInduction_whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3
import Theorems.Thm_LanglandsTunnell_CubicInduction_joint_expansion_coeff_eq_zero_of_forall_whittaker3_diag_mul_eq_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_continuousOn_archRealLift3
import Theorems.Thm_LanglandsTunnell_CubicInduction_expLogSum_coeff_eq_zero_of_re_lt_of_forall_norm_le_rpow
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_archRealLift3_one_and_ideleNorm_det_archRealLift3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_hasDerivAt_doubleSlotCoeff_archFlow_of_joint_expansion_archDeriv
p2m_attr_erase "instance" "WhittakerBlock.sigmaCompactSpace_adelicGL3 M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.WhittakerBlock

namespace CoeffFlowAux

def fl (c d : Fin 3) (s : ℝ) : Fin 3 → Fin 3 → ℝ := fun a b => (if a = b then (1 : ℝ) else 0) + if a = c ∧ b = d then s else 0

theorem fl_apply (c d : Fin 3) (s : ℝ) :
    fl c d s = fun a b => (if a = b then (1 : ℝ) else 0) + if a = c ∧ b = d then s else 0 := rfl

theorem continuous_fl (c d : Fin 3) : Continuous (fl c d) :=
  continuous_pi fun a => continuous_pi fun b => by
    unfold fl
    by_cases h : a = c ∧ b = d
    · simp only [h, and_self, if_true]; exact continuous_const.add continuous_id
    · simp only [h, if_false, add_zero]; exact continuous_const

theorem det_fl (c d : Fin 3) (s : ℝ) : (Matrix.of (fl c d s)).det = 1 + if c = d then s else 0 := by
  unfold fl
  fin_cases c <;> fin_cases d <;> simp [Matrix.det_fin_three]

theorem det_fl_ne_zero (c d : Fin 3) {s : ℝ} (hs : |s| < 1) : (Matrix.of (fl c d s)).det ≠ 0 := by
  rw [det_fl]
  split_ifs
  · have := abs_lt.1 hs; linarith
  · norm_num

theorem continuousOn_mul_lift_fl (c d : Fin 3) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ContinuousOn (fun σ : ℝ => x * WhittakerBlock.archRealLift3 (fl c d σ)) {σ | |σ| < 1} :=
  continuousOn_const.mul (continuousOn_archRealLift3.comp (continuous_fl c d).continuousOn
    (fun σ hσ => det_fl_ne_zero c d hσ))

end CoeffFlowAux

namespace CoeffFlowAux

noncomputable def Wh (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ := whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) NumberField.StandardAddChar.psiQ u

theorem Wh_def (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Wh u = whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) NumberField.StandardAddChar.psiQ u := rfl

noncomputable def wt (c d : Fin 3) (σ : ℝ) : ℂ := (((1 + (if c = d then σ else 0))⁻¹ : ℝ) : ℂ)

theorem one_add_ne_zero (c d : Fin 3) {σ : ℝ} (hσ : |σ| < 1) : (1 + (if c = d then σ else 0) : ℝ) ≠ 0 := by
  split_ifs
  · have := abs_lt.1 hσ; linarith
  · norm_num

theorem continuousOn_wt (c d : Fin 3) : ContinuousOn (wt c d) {σ | |σ| < 1} := by
  unfold wt
  refine Complex.continuous_ofReal.continuousOn.comp ?_ (Set.mapsTo_univ _ _)
  refine ContinuousOn.inv₀ ?_ (fun σ hσ => one_add_ne_zero c d hσ)
  split_ifs
  · exact (continuous_const.add continuous_id).continuousOn
  · exact continuousOn_const

theorem wt_zero (c d : Fin 3) : wt c d 0 = 1 := by unfold wt; simp

theorem norm_wt_le (c d : Fin 3) {σ : ℝ} (hσ : |σ| ≤ 1 / 2) : ‖wt c d σ‖ ≤ 2 := by
  unfold wt
  rw [Complex.norm_real, Real.norm_eq_abs, abs_inv]
  split_ifs
  · have h := abs_le.1 hσ
    rw [abs_of_pos (by linarith)]
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  · simp

structure Reg (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop where
  smooth : WhittakerBlock.IsArchSmooth3 v
  wsmooth : WhittakerBlock.IsArchSmooth3 (Wh v)
  words : ∀ wd : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) v wd)

theorem Reg.deriv {v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hv : Reg v) (c d : Fin 3) : Reg (archDeriv c d v) := by
  have hwords : ∀ wd : List (Fin 3 × Fin 3),
      Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) (archDeriv c d v) wd) := fun wd => by
    have := hv.words (wd ++ [(c, d)])
    rwa [List.foldr_append] at this
  have hsm : WhittakerBlock.IsArchSmooth3 (archDeriv c d v) :=
    isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.1 v hv.smooth c d
  exact ⟨hsm, (whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3 _ hsm hwords).2, hwords⟩

theorem Reg.archDeriv_Wh {v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hv : Reg v) (c d : Fin 3) :
    archDeriv c d (Wh v) = Wh (archDeriv c d v) := by
  have := (whittaker3_iterate_archDeriv_eq_iterate_archDeriv_whittaker3 v hv.smooth hv.words).1 [(c, d)]
  simpa [Wh] using this.symm

theorem continuousOn_comp_fl {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : WhittakerBlock.IsArchSmooth3 F) (c d : Fin 3)
    (x : AdelicGL 3 (𝓞 ℚ) ℚ) : ContinuousOn (fun σ : ℝ => F (x * WhittakerBlock.archRealLift3 (fl c d σ))) {σ | |σ| < 1} :=
  (hF x).continuousOn.comp (continuous_fl c d).continuousOn fun σ hσ => det_fl_ne_zero c d hσ

theorem Wh_flow_ftc {v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hv : Reg v) (c d : Fin 3) (x : AdelicGL 3 (𝓞 ℚ) ℚ)
    {s : ℝ} (hs : |s| < 1) :
    Wh v (x * WhittakerBlock.archRealLift3 (fl c d s)) - Wh v (x * WhittakerBlock.archRealLift3 (fl c d 0)) =
      ∫ σ in 0..s, wt c d σ * Wh (archDeriv c d v) (x * WhittakerBlock.archRealLift3 (fl c d σ)) := by
  have hsub : Set.uIcc 0 s ⊆ {σ : ℝ | |σ| < 1} := fun σ hσ => by
    rcases Set.mem_uIcc.1 hσ with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact lt_of_le_of_lt (by rw [abs_of_nonneg h0]; exact h1) (lt_of_le_of_lt (le_abs_self s) hs)
    · show |σ| < 1
      rw [abs_of_nonpos h1]
      have := abs_lt.1 hs
      linarith
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro σ hσ
    have hσ' := hsub hσ
    have h := hasDerivAt_apply_mul_archRealLift3_of_isArchSmooth3 (Wh v) hv.wsmooth x c d σ (one_add_ne_zero c d hσ')
    rw [hv.archDeriv_Wh] at h
    exact h
  · refine ContinuousOn.intervalIntegrable ?_
    refine ((continuousOn_wt c d).mul (continuousOn_comp_fl (hv.deriv c d).wsmooth c d x)).mono hsub

end CoeffFlowAux

namespace CoeffFlowAux

theorem continuousOn_coeff_fl {f : ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hf : ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => f p.1 p.2) {p | 0 < p.1}) (y : ℝ) (hy : 0 < y)
    (c d : Fin 3) (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ContinuousOn (fun σ : ℝ => f y (k * WhittakerBlock.archRealLift3 (fl c d σ))) {σ | |σ| < 1} := by
  have h1 : ContinuousOn (fun σ : ℝ => ((y, k * WhittakerBlock.archRealLift3 (fl c d σ)) : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ))
      {σ | |σ| < 1} := continuousOn_const.prodMk (continuousOn_mul_lift_fl c d k)
  exact hf.comp h1 fun σ _ => hy

theorem uIcc_subset {s : ℝ} (hs : |s| ≤ 1 / 2) : Set.uIcc 0 s ⊆ {σ : ℝ | |σ| ≤ 1 / 2} := fun σ hσ => by
  rcases Set.mem_uIcc.1 hσ with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · show |σ| ≤ 1 / 2
    rw [abs_of_nonneg h0]; exact h1.trans ((le_abs_self s).trans hs)
  · show |σ| ≤ 1 / 2
    rw [abs_of_nonpos h1]; have := abs_le.1 hs; linarith

theorem half_subset : {σ : ℝ | |σ| ≤ 1 / 2} ⊆ {σ : ℝ | |σ| < 1} := fun σ hσ => by
  show |σ| < 1
  exact lt_of_le_of_lt (show |σ| ≤ 1 / 2 from hσ) (by norm_num)

end CoeffFlowAux

open CoeffFlowAux in
theorem solution
    (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hv : WhittakerBlock.IsArchSmooth3 v ∧
        WhittakerBlock.IsArchSmooth3
          (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ v) ∧
        (∀ wd : List (Fin 3 × Fin 3),
          Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) v wd)) ∧
        ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), v (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = v g)
    (c d : Fin 3)
    (ρ : ℝ) (n J : ℕ) (e : Fin n → ℂ) (δ : ℝ) (hδ : 0 < δ)
    (he : Function.Injective e) (hre : ∀ i, (e i).re ≤ ρ)
    (cv : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (cv' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hexp :
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => cv i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
        ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ v
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
          (∑ i : Fin n, ∑ j : Fin J, cv i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
        C * y₁ ^ (ρ + δ)) ∧
        (∀ i j i' j', Continuous (cv' i j i' j')) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
        ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
        ‖cv i j y₂ k - (∑ i' : Fin n, ∑ j' : Fin J, cv' i j i' j' k *
          ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤ C * y₂ ^ (ρ + δ)))
    (dv : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (dv' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hexpd :
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => dv i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
        ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (WhittakerBlock.archDeriv c d v)
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
          (∑ i : Fin n, ∑ j : Fin J, dv i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
        C * y₁ ^ (ρ + δ)) ∧
        (∀ i j i' j', Continuous (dv' i j i' j')) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
        ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
        ‖dv i j y₂ k - (∑ i' : Fin n, ∑ j' : Fin J, dv' i j i' j' k *
          ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤ C * y₂ ^ (ρ + δ))) :
    ∀ (i : Fin n) (j : Fin J) (i' : Fin n) (j' : Fin J) (k : AdelicGL 3 (𝓞 ℚ) ℚ),
      HasDerivAt
        (fun s : ℝ => cv' i j i' j' (k * WhittakerBlock.archRealLift3 fun a b =>
          (if a = b then (1 : ℝ) else 0) + if a = c ∧ b = d then s else 0))
        (dv' i j i' j' k) 0  := by
  classical
  intro i₀ j₀ i₀' j₀' k
  have hreg : Reg v := ⟨hv.1, hv.2.1, hv.2.2.1⟩
  have hregd : Reg (archDeriv c d v) := hreg.deriv c d
  obtain ⟨hcvc, hcve, hcv'c, hcv'e⟩ := hexp
  obtain ⟨hdvc, hdve, hdv'c, hdv'e⟩ := hexpd

  let L : ℝ → AdelicGL 3 (𝓞 ℚ) ℚ := fun s => WhittakerBlock.archRealLift3 (fl c d s)
  have hL0 : L 0 = 1 := by
    show WhittakerBlock.archRealLift3 (fl c d 0) = 1
    have : fl c d 0 = fun a b : Fin 3 => if a = b then (1 : ℝ) else 0 := by
      funext a b; simp [fl]
    rw [this]; exact WhittakerBlock.archRealLift3_one_and_ideleNorm_det_archRealLift3.1
  have hkL0 : k * L 0 = k := by rw [hL0, mul_one]

  let Kc : Set (AdelicGL 3 (𝓞 ℚ) ℚ) := (fun σ : ℝ => k * L σ) '' {σ | |σ| ≤ 1 / 2}
  have hKc : IsCompact Kc := by
    have hcpt : IsCompact {σ : ℝ | |σ| ≤ 1 / 2} := by
      have : {σ : ℝ | |σ| ≤ 1 / 2} = Set.Icc (-(1 / 2)) (1 / 2) := by ext σ; simp [abs_le]
      rw [this]; exact isCompact_Icc
    exact hcpt.image_of_continuousOn ((continuousOn_mul_lift_fl c d k).mono half_subset)
  have hmemK : ∀ σ : ℝ, |σ| ≤ 1 / 2 → k * L σ ∈ Kc := fun σ hσ => ⟨σ, hσ, rfl⟩

  have hI2 : ∀ s : ℝ, |s| ≤ 1 / 2 → ∀ (i : Fin n) (j : Fin J) (y₂ : ℝ), 0 < y₂ →
      cv i j y₂ (k * L s) - cv i j y₂ (k * L 0) - ∫ σ in 0..s, wt c d σ * dv i j y₂ (k * L σ) = 0 := by
    intro s hs
    have hs1 : |s| < 1 := lt_of_le_of_lt hs (by norm_num)

    let P := {y : ℝ // 0 < y}
    let A : Fin n × Fin J → P → ℂ := fun ij p =>
      cv ij.1 ij.2 p.1 (k * L s) - cv ij.1 ij.2 p.1 (k * L 0) - ∫ σ in 0..s, wt c d σ * dv ij.1 ij.2 p.1 (k * L σ)
    have hinj : Function.Injective fun ij : Fin n × Fin J => (e ij.1, (ij.2 : ℕ)) := by
      intro a b hab
      simp only [Prod.mk.injEq] at hab
      exact Prod.ext (he hab.1) (Fin.ext hab.2)
    have key := expLogSum_coeff_eq_zero_of_re_lt_of_forall_norm_le_rpow (fun ij : Fin n × Fin J => e ij.1)
      (fun ij => (ij.2 : ℕ)) A hinj (ρ + δ) (fun _ _ => 0)
      (fun y p => -∑ ij : Fin n × Fin J, A ij p * ((y : ℂ) ^ e ij.1 * ((Real.log y : ℝ) : ℂ) ^ (ij.2 : ℕ)))
      (fun p y _ _ => by ring) ?_ (fun p => ⟨0, fun y hy _ => by simp⟩)
    · intro i j y₂ hy₂
      have := congrFun (key (i, j) (by linarith [hre i])) ⟨y₂, hy₂⟩
      exact this

    rintro ⟨y₂, hy₂⟩

    set b : ℝ := max y₂ y₂⁻¹ with hbdef
    have hb1 : 1 ≤ b := by
      rw [hbdef]
      rcases le_or_gt 1 y₂ with h | h
      · exact le_max_of_le_left h
      · exact le_max_of_le_right ((one_le_inv₀ hy₂).2 h.le)
    have hyb1 : b⁻¹ ≤ y₂ := by
      rw [hbdef]; rw [inv_le_comm₀ (by positivity) hy₂]; exact le_max_right _ _
    have hyb2 : y₂ ≤ b := by rw [hbdef]; exact le_max_left _ _
    obtain ⟨C₁, hC₁⟩ := hcve Kc hKc b hb1
    obtain ⟨C₂, hC₂⟩ := hdve Kc hKc b hb1
    refine ⟨C₁ + C₁ + |C₂|, fun y₁ hy₁ hy₁1 => ?_⟩

    let φ : Fin n × Fin J → ℂ := fun ij => (y₁ : ℂ) ^ e ij.1 * ((Real.log y₁ : ℝ) : ℂ) ^ (ij.2 : ℕ)
    let pt : AdelicGL 3 (𝓞 ℚ) ℚ := WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k
    have hpt : ∀ σ, pt * L σ = WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * (k * L σ) := fun σ => mul_assoc _ _ _

    let E : ℝ → ℂ := fun σ => Wh v (pt * L σ) - ∑ ij : Fin n × Fin J, cv ij.1 ij.2 y₂ (k * L σ) * φ ij
    let D : ℝ → ℂ := fun σ => Wh (archDeriv c d v) (pt * L σ) - ∑ ij : Fin n × Fin J, dv ij.1 ij.2 y₂ (k * L σ) * φ ij
    have hsum2 : ∀ (f : Fin n → Fin J → ℂ), (∑ ij : Fin n × Fin J, f ij.1 ij.2 * φ ij) =
        ∑ i : Fin n, ∑ j : Fin J, f i j * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)) := fun f => by
      rw [← Finset.sum_product']; rfl
    have hE : ∀ σ, |σ| ≤ 1 / 2 → ‖E σ‖ ≤ C₁ * y₁ ^ (ρ + δ) := fun σ hσ => by
      show ‖Wh v (pt * L σ) - ∑ ij : Fin n × Fin J, cv ij.1 ij.2 y₂ (k * L σ) * φ ij‖ ≤ _
      rw [hsum2 (fun a b' => cv a b' y₂ (k * L σ)), hpt, Wh_def]
      exact hC₁ _ (hmemK σ hσ) y₂ hyb1 hyb2 y₁ hy₁ hy₁1
    have hD : ∀ σ, |σ| ≤ 1 / 2 → ‖D σ‖ ≤ |C₂| * y₁ ^ (ρ + δ) := fun σ hσ => by
      show ‖Wh (archDeriv c d v) (pt * L σ) - ∑ ij : Fin n × Fin J, dv ij.1 ij.2 y₂ (k * L σ) * φ ij‖ ≤ _
      rw [hsum2 (fun a b' => dv a b' y₂ (k * L σ)), hpt, Wh_def]
      exact (hC₂ _ (hmemK σ hσ) y₂ hyb1 hyb2 y₁ hy₁ hy₁1).trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hy₁.le _))

    have hcontW : ContinuousOn (fun σ => Wh (archDeriv c d v) (pt * L σ)) {σ | |σ| < 1} :=
      continuousOn_comp_fl hregd.wsmooth c d pt
    have hcontdv : ∀ ij : Fin n × Fin J, ContinuousOn (fun σ => dv ij.1 ij.2 y₂ (k * L σ)) {σ | |σ| < 1} :=
      fun ij => continuousOn_coeff_fl (hdvc ij.1 ij.2) y₂ hy₂ c d k
    have hsubs : Set.uIcc 0 s ⊆ {σ : ℝ | |σ| < 1} := (uIcc_subset hs).trans half_subset
    have hint_w : IntervalIntegrable (fun σ => wt c d σ * Wh (archDeriv c d v) (pt * L σ)) volume 0 s :=
      (((continuousOn_wt c d).mul hcontW).mono hsubs).intervalIntegrable
    have hint_dv : ∀ ij : Fin n × Fin J,
        IntervalIntegrable (fun σ => wt c d σ * dv ij.1 ij.2 y₂ (k * L σ) * φ ij) volume 0 s := fun ij =>
      ((((continuousOn_wt c d).mul (hcontdv ij)).mul continuousOn_const).mono hsubs).intervalIntegrable
    have hint_sum : IntervalIntegrable (fun σ => ∑ ij : Fin n × Fin J, wt c d σ * dv ij.1 ij.2 y₂ (k * L σ) * φ ij) volume 0 s := by
      have := (continuousOn_finset_sum Finset.univ fun ij _ =>
        (((continuousOn_wt c d).mul (hcontdv ij)).mul (continuousOn_const (c := φ ij)))).mono hsubs
      exact this.intervalIntegrable

    have hI1 := Wh_flow_ftc hreg c d pt hs1
    have hswap : (∑ ij : Fin n × Fin J, (∫ σ in 0..s, wt c d σ * dv ij.1 ij.2 y₂ (k * L σ)) * φ ij) =
        ∫ σ in 0..s, ∑ ij : Fin n × Fin J, wt c d σ * dv ij.1 ij.2 y₂ (k * L σ) * φ ij := by
      rw [intervalIntegral.integral_finsetSum fun ij _ => hint_dv ij]
      exact Finset.sum_congr rfl fun ij _ => by rw [← intervalIntegral.integral_mul_const]
    have hD_int : (∫ σ in 0..s, wt c d σ * D σ) =
        (∫ σ in 0..s, wt c d σ * Wh (archDeriv c d v) (pt * L σ)) -
          ∫ σ in 0..s, ∑ ij : Fin n × Fin J, wt c d σ * dv ij.1 ij.2 y₂ (k * L σ) * φ ij := by
      rw [← intervalIntegral.integral_sub hint_w hint_sum]
      congr 1; funext σ
      simp only [D, mul_sub, Finset.mul_sum, mul_assoc]
    have hid : (∑ ij : Fin n × Fin J, A ij ⟨y₂, hy₂⟩ * φ ij) = -E s + E 0 + ∫ σ in 0..s, wt c d σ * D σ := by
      simp only [A, E, sub_mul, Finset.sum_sub_distrib]
      rw [hswap, hD_int, ← hI1]
      ring

    have hnorm_int : ‖∫ σ in 0..s, wt c d σ * D σ‖ ≤ |C₂| * y₁ ^ (ρ + δ) := by
      have h1 : ‖∫ σ in 0..s, wt c d σ * D σ‖ ≤ (2 * (|C₂| * y₁ ^ (ρ + δ))) * |s - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro σ hσ
        have hσ' : |σ| ≤ 1 / 2 := uIcc_subset hs (Set.uIoc_subset_uIcc hσ)
        rw [norm_mul]
        exact mul_le_mul (norm_wt_le c d hσ') (hD σ hσ') (norm_nonneg _) (by norm_num)
      rw [sub_zero] at h1
      refine h1.trans ?_
      have : 0 ≤ |C₂| * y₁ ^ (ρ + δ) := by positivity
      nlinarith [abs_nonneg s]
    show ‖-∑ ij : Fin n × Fin J, A ij ⟨y₂, hy₂⟩ * φ ij‖ ≤ (C₁ + C₁ + |C₂|) * y₁ ^ (ρ + δ)
    rw [norm_neg, hid]
    have h0 : |(0:ℝ)| ≤ 1 / 2 := by norm_num
    calc ‖-E s + E 0 + ∫ σ in 0..s, wt c d σ * D σ‖ ≤ ‖E s‖ + ‖E 0‖ + ‖∫ σ in 0..s, wt c d σ * D σ‖ := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (by rw [norm_neg]) le_rfl)) le_rfl)
      _ ≤ C₁ * y₁ ^ (ρ + δ) + C₁ * y₁ ^ (ρ + δ) + |C₂| * y₁ ^ (ρ + δ) := add_le_add (add_le_add (hE s hs) (hE 0 h0)) hnorm_int
      _ = (C₁ + C₁ + |C₂|) * y₁ ^ (ρ + δ) := by ring

  have hI3 : ∀ s : ℝ, |s| ≤ 1 / 2 →
      cv' i₀ j₀ i₀' j₀' (k * L s) - cv' i₀ j₀ i₀' j₀' (k * L 0) -
        ∫ σ in 0..s, wt c d σ * dv' i₀ j₀ i₀' j₀' (k * L σ) = 0 := by
    intro s hs
    have hs1 : |s| < 1 := lt_of_le_of_lt hs (by norm_num)
    have hsubs : Set.uIcc 0 s ⊆ {σ : ℝ | |σ| < 1} := (uIcc_subset hs).trans half_subset
    let B : Fin n × Fin J → Unit → ℂ := fun ij _ =>
      cv' i₀ j₀ ij.1 ij.2 (k * L s) - cv' i₀ j₀ ij.1 ij.2 (k * L 0) - ∫ σ in 0..s, wt c d σ * dv' i₀ j₀ ij.1 ij.2 (k * L σ)
    have hinj : Function.Injective fun ij : Fin n × Fin J => (e ij.1, (ij.2 : ℕ)) := by
      intro a b hab
      simp only [Prod.mk.injEq] at hab
      exact Prod.ext (he hab.1) (Fin.ext hab.2)
    have key := expLogSum_coeff_eq_zero_of_re_lt_of_forall_norm_le_rpow (fun ij : Fin n × Fin J => e ij.1)
      (fun ij => (ij.2 : ℕ)) B hinj (ρ + δ) (fun _ _ => 0)
      (fun y _ => -∑ ij : Fin n × Fin J, B ij () * ((y : ℂ) ^ e ij.1 * ((Real.log y : ℝ) : ℂ) ^ (ij.2 : ℕ)))
      (fun p y _ _ => by ring) ?_ (fun p => ⟨0, fun y hy _ => by simp⟩)
    · have := congrFun (key (i₀', j₀') (by linarith [hre i₀'])) ()
      exact this

    intro _
    obtain ⟨C₃, hC₃⟩ := hcv'e Kc hKc
    obtain ⟨C₄, hC₄⟩ := hdv'e Kc hKc
    refine ⟨C₃ + C₃ + |C₄|, fun y₂ hy₂ hy₂1 => ?_⟩
    let ψ : Fin n × Fin J → ℂ := fun ij => (y₂ : ℂ) ^ e ij.1 * ((Real.log y₂ : ℝ) : ℂ) ^ (ij.2 : ℕ)
    have hsum2 : ∀ (f : Fin n → Fin J → ℂ), (∑ ij : Fin n × Fin J, f ij.1 ij.2 * ψ ij) =
        ∑ i : Fin n, ∑ j : Fin J, f i j * ((y₂ : ℂ) ^ e i * ((Real.log y₂ : ℝ) : ℂ) ^ (j : ℕ)) := fun f => by
      rw [← Finset.sum_product']; rfl
    let E : ℝ → ℂ := fun σ => cv i₀ j₀ y₂ (k * L σ) - ∑ ij : Fin n × Fin J, cv' i₀ j₀ ij.1 ij.2 (k * L σ) * ψ ij
    let D : ℝ → ℂ := fun σ => dv i₀ j₀ y₂ (k * L σ) - ∑ ij : Fin n × Fin J, dv' i₀ j₀ ij.1 ij.2 (k * L σ) * ψ ij
    have hE : ∀ σ, |σ| ≤ 1 / 2 → ‖E σ‖ ≤ C₃ * y₂ ^ (ρ + δ) := fun σ hσ => by
      show ‖cv i₀ j₀ y₂ (k * L σ) - ∑ ij : Fin n × Fin J, cv' i₀ j₀ ij.1 ij.2 (k * L σ) * ψ ij‖ ≤ _
      rw [hsum2 (fun a b' => cv' i₀ j₀ a b' (k * L σ))]
      exact hC₃ _ (hmemK σ hσ) i₀ j₀ y₂ hy₂ hy₂1
    have hD : ∀ σ, |σ| ≤ 1 / 2 → ‖D σ‖ ≤ |C₄| * y₂ ^ (ρ + δ) := fun σ hσ => by
      show ‖dv i₀ j₀ y₂ (k * L σ) - ∑ ij : Fin n × Fin J, dv' i₀ j₀ ij.1 ij.2 (k * L σ) * ψ ij‖ ≤ _
      rw [hsum2 (fun a b' => dv' i₀ j₀ a b' (k * L σ))]
      exact (hC₄ _ (hmemK σ hσ) i₀ j₀ y₂ hy₂ hy₂1).trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hy₂.le _))
    have hcontdv : ContinuousOn (fun σ => dv i₀ j₀ y₂ (k * L σ)) {σ | |σ| < 1} :=
      continuousOn_coeff_fl (hdvc i₀ j₀) y₂ hy₂ c d k
    have hcontdv' : ∀ ij : Fin n × Fin J, ContinuousOn (fun σ => dv' i₀ j₀ ij.1 ij.2 (k * L σ)) {σ | |σ| < 1} :=
      fun ij => (hdv'c i₀ j₀ ij.1 ij.2).continuousOn.comp (continuousOn_mul_lift_fl c d k) (Set.mapsTo_univ _ _)
    have hint_d : IntervalIntegrable (fun σ => wt c d σ * dv i₀ j₀ y₂ (k * L σ)) volume 0 s :=
      (((continuousOn_wt c d).mul hcontdv).mono hsubs).intervalIntegrable
    have hint_dv' : ∀ ij : Fin n × Fin J,
        IntervalIntegrable (fun σ => wt c d σ * dv' i₀ j₀ ij.1 ij.2 (k * L σ) * ψ ij) volume 0 s := fun ij =>
      ((((continuousOn_wt c d).mul (hcontdv' ij)).mul continuousOn_const).mono hsubs).intervalIntegrable
    have hint_sum : IntervalIntegrable (fun σ => ∑ ij : Fin n × Fin J, wt c d σ * dv' i₀ j₀ ij.1 ij.2 (k * L σ) * ψ ij) volume 0 s := by
      have := (continuousOn_finset_sum Finset.univ fun ij _ =>
        (((continuousOn_wt c d).mul (hcontdv' ij)).mul (continuousOn_const (c := ψ ij)))).mono hsubs
      exact this.intervalIntegrable
    have hlevel1 := hI2 s hs i₀ j₀ y₂ hy₂
    have hswap : (∑ ij : Fin n × Fin J, (∫ σ in 0..s, wt c d σ * dv' i₀ j₀ ij.1 ij.2 (k * L σ)) * ψ ij) =
        ∫ σ in 0..s, ∑ ij : Fin n × Fin J, wt c d σ * dv' i₀ j₀ ij.1 ij.2 (k * L σ) * ψ ij := by
      rw [intervalIntegral.integral_finsetSum fun ij _ => hint_dv' ij]
      exact Finset.sum_congr rfl fun ij _ => by rw [← intervalIntegral.integral_mul_const]
    have hD_int : (∫ σ in 0..s, wt c d σ * D σ) =
        (∫ σ in 0..s, wt c d σ * dv i₀ j₀ y₂ (k * L σ)) -
          ∫ σ in 0..s, ∑ ij : Fin n × Fin J, wt c d σ * dv' i₀ j₀ ij.1 ij.2 (k * L σ) * ψ ij := by
      rw [← intervalIntegral.integral_sub hint_d hint_sum]
      congr 1; funext σ
      simp only [D, mul_sub, Finset.mul_sum, mul_assoc]
    have hid : (∑ ij : Fin n × Fin J, B ij () * ψ ij) = -E s + E 0 + ∫ σ in 0..s, wt c d σ * D σ := by
      simp only [B, E, sub_mul, Finset.sum_sub_distrib]
      rw [hswap, hD_int]
      linear_combination hlevel1
    have hnorm_int : ‖∫ σ in 0..s, wt c d σ * D σ‖ ≤ |C₄| * y₂ ^ (ρ + δ) := by
      have h1 : ‖∫ σ in 0..s, wt c d σ * D σ‖ ≤ (2 * (|C₄| * y₂ ^ (ρ + δ))) * |s - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro σ hσ
        have hσ' : |σ| ≤ 1 / 2 := uIcc_subset hs (Set.uIoc_subset_uIcc hσ)
        rw [norm_mul]
        exact mul_le_mul (norm_wt_le c d hσ') (hD σ hσ') (norm_nonneg _) (by norm_num)
      rw [sub_zero] at h1
      refine h1.trans ?_
      have : 0 ≤ |C₄| * y₂ ^ (ρ + δ) := by positivity
      nlinarith [abs_nonneg s]
    show ‖-∑ ij : Fin n × Fin J, B ij () * ψ ij‖ ≤ (C₃ + C₃ + |C₄|) * y₂ ^ (ρ + δ)
    rw [norm_neg, hid]
    have h0 : |(0:ℝ)| ≤ 1 / 2 := by norm_num
    calc ‖-E s + E 0 + ∫ σ in 0..s, wt c d σ * D σ‖ ≤ ‖E s‖ + ‖E 0‖ + ‖∫ σ in 0..s, wt c d σ * D σ‖ := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (by rw [norm_neg]) le_rfl)) le_rfl)
      _ ≤ C₃ * y₂ ^ (ρ + δ) + C₃ * y₂ ^ (ρ + δ) + |C₄| * y₂ ^ (ρ + δ) := add_le_add (add_le_add (hE s hs) (hE 0 h0)) hnorm_int
      _ = (C₃ + C₃ + |C₄|) * y₂ ^ (ρ + δ) := by ring

  let g : ℝ → ℂ := fun σ => wt c d σ * dv' i₀ j₀ i₀' j₀' (k * L σ)
  have hgc : ContinuousOn g {σ | |σ| < 1} :=
    (continuousOn_wt c d).mul ((hdv'c i₀ j₀ i₀' j₀').continuousOn.comp (continuousOn_mul_lift_fl c d k) (Set.mapsTo_univ _ _))
  have hopen : IsOpen {σ : ℝ | |σ| < 1} := isOpen_lt continuous_abs continuous_const
  have h0mem : (0 : ℝ) ∈ {σ : ℝ | |σ| < 1} := by show |(0:ℝ)| < 1; norm_num
  have hg0 : g 0 = dv' i₀ j₀ i₀' j₀' k := by
    show wt c d 0 * dv' i₀ j₀ i₀' j₀' (k * L 0) = _
    rw [wt_zero, one_mul, hkL0]
  have hInt : HasDerivAt (fun u => ∫ σ in 0..u, g σ) (g 0) 0 :=
    intervalIntegral.integral_hasDerivAt_right (by simp)
      (hgc.stronglyMeasurableAtFilter hopen _ h0mem) (hgc.continuousAt (hopen.mem_nhds h0mem))
  have hsum : HasDerivAt (fun u => cv' i₀ j₀ i₀' j₀' (k * L 0) + ∫ σ in 0..u, g σ) (dv' i₀ j₀ i₀' j₀' k) 0 := by
    rw [← hg0]; exact hInt.const_add _
  refine hsum.congr_of_eventuallyEq ?_
  have hnb : {σ : ℝ | |σ| < 1 / 2} ∈ nhds (0 : ℝ) :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (by show |(0:ℝ)| < 1 / 2; norm_num)
  filter_upwards [hnb] with u hu
  have := hI3 u (le_of_lt hu)
  show cv' i₀ j₀ i₀' j₀' (k * WhittakerBlock.archRealLift3 (fl c d u)) = cv' i₀ j₀ i₀' j₀' (k * L 0) + ∫ σ in 0..u, g σ
  linear_combination this

end S_LanglandsTunnell_CubicInduction_hasDerivAt_doubleSlotCoeff_archFlow_of_joint_expansion_archDeriv
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_hasDerivAt_doubleSlotCoeff_archFlow_of_joint_expansion_archDeriv (solution)
