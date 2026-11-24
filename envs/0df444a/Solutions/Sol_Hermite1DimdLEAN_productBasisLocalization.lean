-- Prove2me | solution 1 for Hermite1DimdLEAN.productBasisLocalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:41:51.656034+00:00
-- url     : https://prove2.me/submissions/f122bb4e-bbad-4f08-99c7-cdcc9c533580

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_MissingMathlib
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_BlockLocalization
public import Theorems.Thm_Hermite1DimdLEAN_localizationIncludingZero
public import Theorems.Thm_Hermite1DimdLEAN_tensorGaussianFactorization
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_integrable_weightedCross
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
namespace Hermite1DimdLEAN
private lemma mem_squareBlock_iff_blockIndexMulti_eq
    {d : ℕ} (α ℓ : MultiIndex d) :
    α ∈ squareBlock ℓ ↔ blockIndexMulti α = ℓ := by
  constructor
  · intro h
    funext q
    have hq : α q ∈ HermiteLEAN.squareBlock (ℓ q) := h q
    rw [HermiteLEAN.squareBlock, Finset.mem_Ico] at hq
    exact ((Nat.eq_sqrt).2 (by simpa [Nat.pow_two] using hq)).symm
  · intro h q
    rw [HermiteLEAN.squareBlock, Finset.mem_Ico]
    have hq : Nat.sqrt (α q) = ℓ q := by
      simpa [blockIndexMulti, HermiteLEAN.blockIndex] using congrArg (fun f => f q) h
    exact by simpa [Nat.pow_two] using (Nat.eq_sqrt).1 hq.symm
private lemma gaussianInner_self
    {d : ℕ} (F : CSpace d → ℂ) :
    gaussianInner F F = ((gaussianL2NormSq F : ℝ) : ℂ) := by
  unfold gaussianInner gaussianL2NormSq
  have hfun :
      (fun z : CSpace d => F z * conj (F z)) =
        fun z : CSpace d => ((‖F z‖ ^ 2 : ℝ) : ℂ) := by
    funext z
    simpa using Complex.mul_conj' (F z)
  rw [hfun, integral_complex_ofReal]
private lemma measurableSet_oneDimAnnulus
    (j : ℕ) :
    MeasurableSet (productAnnulus (d := 1) (fun _ => j)) := by
  have hge :
      MeasurableSet {z : CSpace 1 | (j : ℝ) ≤ ‖z 0‖} := measurableSet_le measurable_const
      (measurable_norm.comp (continuous_apply 0).measurable)
  have hlt :
      MeasurableSet {z : CSpace 1 | ‖z 0‖ < (j : ℝ) + 1} := measurableSet_lt
      (measurable_norm.comp (continuous_apply 0).measurable) measurable_const
  simpa [productAnnulus, Set.ofPred_forall, Set.ofPred_and] using hge.inter hlt
private lemma integrable_oneDimPhi_cross_gaussian
    (k m n : ℕ) :
    Integrable
      (fun z : CSpace 1 => oneDimPhi k m (z 0) * conj (oneDimPhi k n (z 0)))
      (gaussianMeasure 1) := by
  change
    Integrable
      (fun z : CSpace 1 => HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))
      (gaussianMeasure 1)
  rw [gaussianMeasure, MeasureTheory.integrable_withDensity_iff_integrable_smul']
  · have hcross :
        Integrable
          (fun z : CSpace 1 =>
            HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)) *
              (Real.exp (-‖z 0‖ ^ 2) : ℂ)) := by
      have h :=
        (MeasureTheory.volume_preserving_funUnique (Fin 1) ℂ).integrable_comp_of_integrable
          (g := fun z : ℂ =>
            HermitekLEAN.Phi k m z * conj (HermitekLEAN.Phi k n z) *
              (Real.exp (-‖z‖ ^ 2) : ℂ))
          (HermitekLEAN.integrable_weightedCross k m n)
      refine h.congr ?_
      filter_upwards with z
      rfl
    have hsmul :
        Integrable
          (fun z : CSpace 1 =>
            Real.exp (-‖z 0‖ ^ 2) •
              (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))) := by
      convert hcross using 1
      funext z
      simp [Algebra.smul_def, mul_left_comm, mul_comm]
    refine (hsmul.const_mul (1 / Real.pi)).congr ?_
    filter_upwards with z
    symm
    have hnonneg : 0 ≤ π⁻¹ * rexp (-‖z 0‖ ^ 2) := by positivity
    simp only [gaussianDensity, pow_one, one_div, univ_unique, Fin.default_eq_zero,
      Fin.isValue, sum_singleton, hnonneg, ENNReal.toReal_ofReal, real_smul, ofReal_exp,
      ofReal_neg, ofReal_pow]
    have hleft :
        (π⁻¹ * rexp (-‖z 0‖ ^ 2)) •
            (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) =
          (((π⁻¹ * rexp (-‖z 0‖ ^ 2) : ℝ) : ℂ) *
            (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))) := by
      simp [Algebra.smul_def]
    calc
      (π⁻¹ * rexp (-‖z 0‖ ^ 2)) •
          (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) =
        (((π⁻¹ * rexp (-‖z 0‖ ^ 2) : ℝ) : ℂ) *
          (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))) := hleft
      _ = (↑π)⁻¹ * (cexp (-↑‖z 0‖ ^ 2) *
            (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))) := by
          simp [mul_assoc, mul_left_comm]
  · change
      Measurable
        (fun z : CSpace 1 =>
          ENNReal.ofReal ((1 / Real.pi ^ 1) * Real.exp (-(∑ q : Fin 1, ‖z q‖ ^ 2))))
    fun_prop
  · simp
private lemma productBasis_annulusFactorization
    {d : ℕ} (κ α j : MultiIndex d) :
    annulusMass j (PhiKappaAlpha κ α) =
      ∏ q : Fin d,
        annulusMass (d := 1) (fun _ => j q) (oneDimLift (oneDimPhi (κ q) (α q))) := by
  classical
  let F : Fin d → ℂ → ℂ := fun q z =>
    if (j q : ℝ) ≤ ‖z‖ ∧ ‖z‖ < (j q : ℝ) + 1 then oneDimPhi (κ q) (α q) z else 0
  have hFG :
      ∀ q : Fin d,
        Integrable
          (fun z : CSpace 1 => F q (z 0) * conj (F q (z 0)))
          (gaussianMeasure 1) := by
    intro q
    have hbase :=
      integrable_oneDimPhi_cross_gaussian (κ q) (α q) (α q)
    have hind :
        Integrable
          (fun z : CSpace 1 =>
            if z ∈ productAnnulus (d := 1) (fun _ => j q) then
              oneDimPhi (κ q) (α q) (z 0) * conj (oneDimPhi (κ q) (α q) (z 0))
            else 0)
          (gaussianMeasure 1) := by
      refine (hbase.indicator (measurableSet_oneDimAnnulus (j q))).congr ?_
      filter_upwards with z
      simp only [Set.indicator]
    convert hind using 1
    funext z
    by_cases hz : z ∈ productAnnulus (d := 1) (fun _ => j q)
    · have hz0 : (j q : ℝ) ≤ ‖z 0‖ ∧ ‖z 0‖ < (j q : ℝ) + 1 := by simpa [productAnnulus] using hz
      simp [F, hz, hz0]
    · have hz0 : ¬ ((j q : ℝ) ≤ ‖z 0‖ ∧ ‖z 0‖ < (j q : ℝ) + 1) := by simpa [productAnnulus] using hz
      simp [F, hz, hz0]
  have htensor := tensorGaussianFactorization d F F hFG
  apply Complex.ofReal_injective
  calc
    (((annulusMass j (PhiKappaAlpha κ α) : ℝ)) : ℂ)
        = gaussianInner (fun z => ∏ q : Fin d, F q (z q)) (fun z => ∏ q : Fin d, F q (z q)) := by
            rw [gaussianInner_self]
            congr 1
            unfold annulusMass gaussianL2NormSq
            refine integral_congr_ae ?_
            filter_upwards with z
            by_cases hz : z ∈ productAnnulus j
            · have hq :
                ∀ q : Fin d, (j q : ℝ) ≤ ‖z q‖ ∧ ‖z q‖ < (j q : ℝ) + 1 := hz
              simp [F, PhiKappaAlpha, hz, hq]
            · have hq : ∃ q : Fin d, ¬ ((j q : ℝ) ≤ ‖z q‖ ∧ ‖z q‖ < (j q : ℝ) + 1) := by
                simpa [productAnnulus] using hz
              rcases hq with ⟨q, hq⟩
              have hFq : F q (z q) = 0 := by simp [F, hq]
              have hprod : (∏ q' : Fin d, F q' (z q')) = 0 := by
                refine Finset.prod_eq_zero_iff.mpr ?_
                exact ⟨q, Finset.mem_univ q, hFq⟩
              simp [hz, hprod]
    _ = ∏ q : Fin d,
          gaussianInner (d := 1) (fun z : CSpace 1 => F q (z 0)) (fun z : CSpace 1 => F q (z 0))
              := by simpa using htensor.2
    _ = ∏ q : Fin d, (((annulusMass (d := 1) (fun _ => j q) (oneDimLift (oneDimPhi (κ q) (α q))) :
        ℝ)) : ℂ) := by
          refine Finset.prod_congr rfl ?_
          intro q hq
          rw [gaussianInner_self]
          congr 1
          unfold gaussianL2NormSq annulusMass
          refine integral_congr_ae ?_
          filter_upwards with z
          by_cases hz : z ∈ productAnnulus (d := 1) (fun _ => j q)
          · have hz0 : (j q : ℝ) ≤ ‖z 0‖ ∧ ‖z 0‖ < (j q : ℝ) + 1 := by
              simpa [productAnnulus] using hz
            simp [F, hz, hz0, oneDimLift]
          · have hz0 : ¬ ((j q : ℝ) ≤ ‖z 0‖ ∧ ‖z 0‖ < (j q : ℝ) + 1) := by
              simpa [productAnnulus] using hz
            simp [F, hz, hz0]
    _ = (((∏ q : Fin d,
            annulusMass (d := 1) (fun _ => j q) (oneDimLift (oneDimPhi (κ q) (α q))) : ℝ)) : ℂ) :=
                by
          simp
private lemma block_decay_compare_coord
    {d : ℕ} (κ α j ℓ : MultiIndex d) (q : Fin d)
    (hblock : α ∈ squareBlock ℓ) :
    max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0
      ≤
    max (|((j q : ℕ) : ℝ) - Real.sqrt (α q : ℝ)| - ((κ q + 4 : ℕ) : ℝ)) 0 := by
  have hsqrt : Nat.sqrt (α q) = ℓ q := by
    simpa [blockIndexMulti, HermiteLEAN.blockIndex] using
      congrArg (fun f => f q) ((mem_squareBlock_iff_blockIndexMulti_eq α ℓ).mp hblock)
  have hle : ((ℓ q : ℕ) : ℝ) ≤ Real.sqrt (α q : ℝ) := by
    simpa [hsqrt] using (Real.nat_sqrt_le_real_sqrt (a := α q))
  have hlt : Real.sqrt (α q : ℝ) < ((ℓ q + 1 : ℕ) : ℝ) := by
    simpa [hsqrt] using (Real.real_sqrt_lt_nat_sqrt_succ (a := α q))
  have hclose : |Real.sqrt (α q : ℝ) - ((ℓ q : ℕ) : ℝ)| < 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    push_cast at hlt ⊢
    linarith only [hlt]
  have hdist_eq : ((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) = |((j q : ℕ) : ℝ) - ((ℓ q : ℕ) : ℝ)| := by
    rcases Nat.le_total (j q) (ℓ q) with hj | hℓ
    · rw [Nat.dist_eq_sub_of_le hj, abs_of_nonpos]
      · simp_all
      · exact sub_nonpos.mpr (by exact_mod_cast hj)
    · rw [Nat.dist_eq_sub_of_le_right hℓ, abs_of_nonneg]
      · rw [Nat.cast_sub hℓ]
      · exact sub_nonneg.mpr (by exact_mod_cast hℓ)
  have htri :
      |((j q : ℕ) : ℝ) - ((ℓ q : ℕ) : ℝ)|
        ≤ |((j q : ℕ) : ℝ) - Real.sqrt (α q : ℝ)| +
            |Real.sqrt (α q : ℝ) - ((ℓ q : ℕ) : ℝ)| := by
    calc
      |((j q : ℕ) : ℝ) - ((ℓ q : ℕ) : ℝ)|
          = |(((j q : ℕ) : ℝ) - Real.sqrt (α q : ℝ)) +
              (Real.sqrt (α q : ℝ) - ((ℓ q : ℕ) : ℝ))| := by ring_nf
      _ ≤ |((j q : ℕ) : ℝ) - Real.sqrt (α q : ℝ)| +
            |Real.sqrt (α q : ℝ) - ((ℓ q : ℕ) : ℝ)| := by
              simpa using
                abs_add_le (((j q : ℕ) : ℝ) - Real.sqrt (α q : ℝ))
                  (Real.sqrt (α q : ℝ) - ((ℓ q : ℕ) : ℝ))
  have hbound :
      ((Nat.dist (j q) (ℓ q) : ℕ) : ℝ)
        ≤ |((j q : ℕ) : ℝ) - Real.sqrt (α q : ℝ)| + 1 := by
    rw [hdist_eq]
    linarith only [hclose, htri]
  have hk : (((κ q + 5 : ℕ) : ℝ)) = (((κ q + 4 : ℕ) : ℝ)) + 1 := by
    push_cast
    ring
  exact max_le_max (by linarith only [hclose, hdist_eq, htri, hk]) le_rfl
private lemma sup_coord_exists
    {d : ℕ} (hd : d ≠ 0) (j ℓ : MultiIndex d) :
    ∃ q0 : Fin d, blockDistance j ℓ = Nat.dist (j q0) (ℓ q0) := by
  let q0 : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨q0, Finset.mem_univ q0⟩
  have hbd_eq :
      blockDistance j ℓ = Finset.univ.sup' hne (fun q : Fin d => Nat.dist (j q) (ℓ q)) := by
    rw [blockDistance, Finset.sup'_eq_sup hne]
  rw [hbd_eq]
  rcases Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Fin d))) hne
      (f := fun q : Fin d => Nat.dist (j q) (ℓ q)) with ⟨q0, hq0, hsup⟩
  refine ⟨q0, ?_⟩
  simpa [Finset.sup'_eq_sup hne] using hsup
end Hermite1DimdLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
open Hermite1DimdLEAN
namespace Hermite1DimdLEAN
theorem _root_.solution
    {d : ℕ} (κ : MultiIndex d) :
    ∃ C c B : ℝ, 0 < C ∧ 0 < c ∧ 0 ≤ B ∧
      ∀ α j ℓ : MultiIndex d, α ∈ squareBlock ℓ →
        annulusMass j (PhiKappaAlpha κ α) ≤
          C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) := by
  /-
  Scaffolding guidance:
  this is the coordinatewise product version of the imported one-dimensional
  localization estimate.
  -/
  by_cases hd : d = 0
  · subst hd
    refine ⟨1, 1, 0, by positivity, by positivity, le_rfl, ?_⟩
    intro α j ℓ hblock
    have hα : α = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    have hℓ : ℓ = 0 := Subsingleton.elim _ _
    subst hα hj hℓ
    rw [productBasis_annulusFactorization]
    simp [blockDistance]
  · choose Cq cq hCq_pos hcq_pos hloc using (fun q : Fin d => localizationIncludingZero (κ q))
    let q0 : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
    let C : ℝ := ∏ q : Fin d, Cq q
    let c : ℝ := Finset.univ.inf' ⟨q0, Finset.mem_univ q0⟩ cq
    let B : ℝ := ∑ q : Fin d, ((κ q + 5 : ℕ) : ℝ)
    have hC_pos : 0 < C := by
      dsimp [C]
      exact Finset.prod_pos (fun q hq => hCq_pos q)
    have hc_pos : 0 < c := by
      dsimp [c]
      exact (Finset.lt_inf'_iff ⟨q0, Finset.mem_univ q0⟩).2
        (fun q _ => hcq_pos q)
    have hB_nonneg : 0 ≤ B := by
      dsimp [B]
      positivity
    refine ⟨C, c, B, hC_pos, hc_pos, hB_nonneg, ?_⟩
    intro α j ℓ hblock
    rw [productBasis_annulusFactorization]
    have hcoord :
        ∀ q : Fin d,
          annulusMass (d := 1) (fun _ => j q) (oneDimLift (oneDimPhi (κ q) (α q))) ≤
            Cq q *
              Real.exp
                (-(cq q) *
                  max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 ^ 2) := by
      intro q
      have hbase := hloc q (α q) (j q)
      have hcmp := block_decay_compare_coord (κ := κ) (α := α) (j := j) (ℓ := ℓ) q hblock
      have hsq :
          max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 ^ 2 ≤
            max (|((j q : ℕ) : ℝ) - Real.sqrt (α q : ℝ)| - ((κ q + 4 : ℕ) : ℝ)) 0 ^ 2 := by
        nlinarith only [
          hcmp, le_max_right (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0,
          le_max_right (|((j q : ℕ) : ℝ) - Real.sqrt (α q : ℝ)| - ((κ q + 4 : ℕ) : ℝ)) 0
        ]
      have hexp :
          Real.exp
              (-(cq q) *
                max (|((j q : ℕ) : ℝ) - Real.sqrt (α q : ℝ)| - ((κ q + 4 : ℕ) : ℝ)) 0 ^ 2) ≤
            Real.exp
              (-(cq q) *
                max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 ^ 2) := by
        simp_all
      exact le_trans hbase <| mul_le_mul_of_nonneg_left hexp (le_of_lt (hCq_pos q))
    have hprod_bound :
        ∏ q : Fin d, annulusMass (d := 1) (fun _ => j q) (oneDimLift (oneDimPhi (κ q) (α q))) ≤
          ∏ q : Fin d,
            (Cq q *
              Real.exp
                (-(cq q) *
                  max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 ^ 2)) := by
      refine Finset.prod_le_prod ?_ ?_
      · intro q hq
        unfold annulusMass
        positivity
      · simp_all
    refine le_trans hprod_bound ?_
    have hcsmall : ∀ q : Fin d, c ≤ cq q := by
      intro q
      dsimp [c]
      exact Finset.inf'_le _ (Finset.mem_univ q)
    have hsq_ge :
        max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2 ≤
          ∑ q : Fin d, max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 ^ 2 := by
      rcases sup_coord_exists hd j ℓ with ⟨q0, hq0⟩
      have hBq : ((κ q0 + 5 : ℕ) : ℝ) ≤ B := by
        dsimp [B]
        simpa using
          (Finset.single_le_sum
            (s := (Finset.univ : Finset (Fin d)))
            (a := q0)
            (f := fun q : Fin d => ((κ q + 5 : ℕ) : ℝ))
            (fun q hq => by positivity)
            (Finset.mem_univ q0))
      have hmax :
          max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ≤
            max (((Nat.dist (j q0) (ℓ q0) : ℕ) : ℝ) - ((κ q0 + 5 : ℕ) : ℝ)) 0 := by
        rw [hq0]
        exact max_le_max (sub_le_sub_left hBq _) le_rfl
      have hsq0 :
          max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2 ≤
            max (((Nat.dist (j q0) (ℓ q0) : ℕ) : ℝ) - ((κ q0 + 5 : ℕ) : ℝ)) 0 ^ 2 := by
        nlinarith only [
          hmax, le_max_right (((blockDistance j ℓ : ℕ) : ℝ) - B) 0,
          le_max_right (((Nat.dist (j q0) (ℓ q0) : ℕ) : ℝ) - ((κ q0 + 5 : ℕ) : ℝ)) 0
        ]
      have hsingle :
          max (((Nat.dist (j q0) (ℓ q0) : ℕ) : ℝ) - ((κ q0 + 5 : ℕ) : ℝ)) 0 ^ 2 ≤
            ∑ q : Fin d, max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 ^ 2 := by
        simpa using
          (Finset.single_le_sum
            (s := (Finset.univ : Finset (Fin d)))
            (a := q0)
            (f := fun q : Fin d =>
              max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 ^ 2)
            (fun q hq => by positivity)
            (Finset.mem_univ q0))
      exact le_trans hsq0 hsingle
    calc
      ∏ q : Fin d,
          (Cq q *
            Real.exp
              (-(cq q) * max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 ^ 2))
        = C *
            Real.exp
              (∑ q : Fin d,
                (-(cq q) * max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 ^ 2)) :=
                    by
              rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      _ ≤ C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) := by
            have hsum_le :
                ∑ q : Fin d,
                    (-(cq q) * max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 ^ 2) ≤
                  -(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2 := by
              have hsum_term :
                  ∑ q : Fin d,
                      (-(cq q) * max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0 ^
                          2) ≤
                    -(c) *
                      ∑ q : Fin d, max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0
                          ^ 2 := by
                rw [Finset.mul_sum]
                refine Finset.sum_le_sum fun q _ => ?_
                nlinarith only [hcsmall, hcsmall q,
                    sq_nonneg (max (((Nat.dist (j q) (ℓ q) : ℕ) : ℝ) - ((κ q + 5 : ℕ) : ℝ)) 0)]
              nlinarith only [hc_pos, hsq_ge, hsum_term]
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum_le) (le_of_lt hC_pos)
end Hermite1DimdLEAN
