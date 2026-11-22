-- Prove2me | solution 1 for Lean4LPD.LayerCounterexample.pf2_coeff_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:48:48.227178+00:00
-- url     : https://prove2.me/submissions/85a5ad2e-7ba0-4550-9219-a4e5235abecd

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerCounterexample
public import Theorems.Thm_Lean4LPD_LayerCounterexample_pf2Rotations_hermitian
public import Theorems.Thm_Lean4LPD_LayerCounterexample_input_coeffVec
public import Theorems.Thm_Lean4LPD_PauliString_cls_fst
public import Theorems.Thm_Lean4LPD_PauliString_cls_herm
public import Theorems.Thm_Lean4LPD_PauliString_cls_snd
public import Theorems.Thm_Lean4LPD_PauliString_coeffVec_apply
public import Theorems.Thm_Lean4LPD_PauliString_coeffVec_layerConj
public import Theorems.Thm_Lean4LPD_PauliString_cover_nil
public import Theorems.Thm_Lean4LPD_PauliString_herm_x
public import Theorems.Thm_Lean4LPD_PauliString_herm_z
public import Theorems.Thm_Lean4LPD_PauliString_jumpAct_apply
public import Theorems.Thm_Lean4LPD_PauliString_jumpAct_zero
public import Theorems.Thm_Lean4LPD_PauliString_mem_antiLayer
public import Theorems.Thm_Lean4LPD_PauliString_mem_antiSites
public import Theorems.Thm_Lean4LPD_PauliString_mem_highSet
public import Theorems.Thm_Lean4LPD_PauliString_mem_support
public import Theorems.Thm_Lean4LPD_PauliString_oneLayer_cons
public import Theorems.Thm_Lean4LPD_PauliString_oneLayer_nil
public import Theorems.Thm_Lean4LPD_PauliString_pauliNorm_sq
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_phaseMul_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_self_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_phase
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_x
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_z
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_zero
public import Theorems.Thm_Lean4LPD_PauliString_reachable_cons
public import Theorems.Thm_Lean4LPD_PauliString_reachable_nil
public import Theorems.Thm_Lean4LPD_PauliString_restr_apply
public import Theorems.Thm_Lean4LPD_PauliString_restr_univ
public import Theorems.Thm_Lean4LPD_PauliString_self_mem_branch
public import Theorems.Thm_Lean4LPD_PauliString_site_mul
public import Theorems.Thm_Lean4LPD_PauliString_site_one
public import Theorems.Thm_Lean4LPD_PauliString_site_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_stayAct_apply
public import Theorems.Thm_Lean4LPD_PauliString_stayAct_zero
public import Theorems.Thm_Lean4LPD_PauliString_support_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_mul_self_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_left
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_self
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_one
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_weight_one
public import Theorems.Thm_Lean4LPD_PauliString_weight_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_wt_cls
public import Theorems.Thm_Lean4LPD_conj_negOnePow
public import Theorems.Thm_Lean4LPD_iPow_signPhase
public import Theorems.Thm_Lean4LPD_iPow_two
public import Theorems.Thm_Lean4LPD_negOnePow_mul_self
public import Theorems.Thm_Lean4LPD_negOnePow_one
public import Theorems.Thm_Lean4LPD_negOnePow_zero
public import Theorems.Thm_Lean4LPD_norm_iPow
public import Theorems.Thm_Lean4LPD_rungWeight_one
public import Theorems.Thm_Lean4LPD_star_negOnePow
attribute [local simp] Lean4LPD.PauliString.cls_fst
attribute [local simp] Lean4LPD.PauliString.cls_herm
attribute [local simp] Lean4LPD.PauliString.cls_snd
attribute [local simp] Lean4LPD.PauliString.coeffVec_apply
attribute [local simp] Lean4LPD.PauliString.cover_nil
attribute [local simp] Lean4LPD.PauliString.herm_x
attribute [local simp] Lean4LPD.PauliString.herm_z
attribute [local simp] Lean4LPD.PauliString.jumpAct_apply
attribute [local simp] Lean4LPD.PauliString.jumpAct_zero
attribute [local simp] Lean4LPD.PauliString.mem_antiLayer
attribute [local simp] Lean4LPD.PauliString.mem_antiSites
attribute [local simp] Lean4LPD.PauliString.mem_highSet
attribute [local simp] Lean4LPD.PauliString.mem_support
attribute [local simp] Lean4LPD.PauliString.oneLayer_cons
attribute [local simp] Lean4LPD.PauliString.oneLayer_nil
attribute [local simp] Lean4LPD.PauliString.pauliNorm_sq
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_phaseMul_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_self_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_phase
attribute [local simp] Lean4LPD.PauliString.phaseMul_x
attribute [local simp] Lean4LPD.PauliString.phaseMul_z
attribute [local simp] Lean4LPD.PauliString.phaseMul_zero
attribute [local simp] Lean4LPD.PauliString.reachable_cons
attribute [local simp] Lean4LPD.PauliString.reachable_nil
attribute [local simp] Lean4LPD.PauliString.restr_apply
attribute [local simp] Lean4LPD.PauliString.restr_univ
attribute [local simp] Lean4LPD.PauliString.self_mem_branch
attribute [local simp] Lean4LPD.PauliString.site_mul
attribute [local simp] Lean4LPD.PauliString.site_one
attribute [local simp] Lean4LPD.PauliString.site_phaseMul
attribute [local simp] Lean4LPD.PauliString.stayAct_apply
attribute [local simp] Lean4LPD.PauliString.stayAct_zero
attribute [local simp] Lean4LPD.PauliString.support_phaseMul
attribute [local simp] Lean4LPD.PauliString.sympForm_mul_self_right
attribute [local simp] Lean4LPD.PauliString.sympForm_phaseMul_left
attribute [local simp] Lean4LPD.PauliString.sympForm_phaseMul_right
attribute [local simp] Lean4LPD.PauliString.sympForm_self
attribute [local simp] Lean4LPD.PauliString.toMatrix_one
attribute [local simp] Lean4LPD.PauliString.toMatrix_phaseMul
attribute [local simp] Lean4LPD.PauliString.weight_one
attribute [local simp] Lean4LPD.PauliString.weight_phaseMul
attribute [local simp] Lean4LPD.PauliString.wt_cls
attribute [local simp] Lean4LPD.conj_negOnePow
attribute [local simp] Lean4LPD.iPow_signPhase
attribute [local simp] Lean4LPD.iPow_two
attribute [local simp] Lean4LPD.negOnePow_mul_self
attribute [local simp] Lean4LPD.negOnePow_one
attribute [local simp] Lean4LPD.negOnePow_zero
attribute [local simp] Lean4LPD.norm_iPow
attribute [local simp] Lean4LPD.rungWeight_one
attribute [local simp] Lean4LPD.star_negOnePow


section
@[expose] public section
namespace Lean4LPD.LayerCounterexample
open PauliString LayerWitness Finset
private theorem coeff_zero_of_not_backward {n : ℕ} (L : List (PauliString n)) (θ : ℝ)
    (p q : PauliIndex n) (h : backwardReaches L p q = false) :
    (layerAct (L.map fun G => (G, θ))
      (WithLp.toLp 2 (Pi.single q (1 : ℂ)))).ofLp p = 0 := by
  induction L generalizing p with
  | nil =>
      have hpq : p ≠ q := by simpa [backwardReaches] using h
      simp [layerAct, hpq]
  | cons G L ih =>
      by_cases hp : sympForm G (herm p) = 0
      · have ht : backwardReaches L p q = false := by simpa [backwardReaches, hp] using h
        simp only [List.map_cons, layerAct, rotAct_apply, hp, ↓reduceIte]
        exact ih p ht
      · have ht : backwardReaches L p q = false ∧ backwardReaches L (partner G p) q = false := by
          simpa [backwardReaches, hp] using h
        simp only [List.map_cons, layerAct, rotAct_apply, hp, ↓reduceIte]
        rw [ih p ht.1, ih (partner G p) ht.2, mul_zero, mul_zero, mul_zero, sub_self]
private theorem suffix_coeff_step (θ : ℝ) (i : ℕ) (g : Fin 7)
    (v : EuclideanSpace ℂ (PauliIndex 8)) (p : PauliIndex 8)
    (h : (pf2Rotations θ).drop i = (generator g, θ) :: (pf2Rotations θ).drop (i + 1)) :
    (layerAct ((pf2Rotations θ).drop i) v).ofLp p =
      if sympForm (generator g) (herm p) = 0 then
        (layerAct ((pf2Rotations θ).drop (i + 1)) v).ofLp p
      else (Real.cos θ : ℂ) * (layerAct ((pf2Rotations θ).drop (i + 1)) v).ofLp p
        - (Real.sin θ : ℂ) * (partnerSign (generator g) p *
          (layerAct ((pf2Rotations θ).drop (i + 1)) v).ofLp (partner (generator g) p)) := by
  rw [h, layerAct, rotAct_apply]
attribute [local irreducible] layerAct
private theorem suffixCoefficient_14_0_8 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 14) coefficientSeed).ofLp
    (bitIndex 0 8) = 1 := by
  rw [show (pf2Rotations θ).drop 14 = [] by rfl, layerAct]
  exact Pi.single_eq_same (M := fun _ : PauliIndex 8 => ℂ) (bitIndex 0 8) (1 : ℂ)
private theorem suffixCoefficient_13_0_8 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 13) coefficientSeed).ofLp
    (bitIndex 0 8) = 1 := by
  rw [suffix_coeff_step θ 13 3
    coefficientSeed (bitIndex 0 8) (by rfl),
    if_pos (by decide)]
  all_goals exact (suffixCoefficient_14_0_8 θ)
private theorem suffixCoefficient_12_0_8 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 12) coefficientSeed).ofLp
    (bitIndex 0 8) = 1 := by
  rw [suffix_coeff_step θ 12 2
    coefficientSeed (bitIndex 0 8) (by rfl),
    if_pos (by decide)]
  all_goals exact (suffixCoefficient_13_0_8 θ)
private theorem suffixCoefficient_11_12_8 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 11) coefficientSeed).ofLp
    (bitIndex 12 8) = (Real.sin θ : ℂ) := by
  rw [suffix_coeff_step θ 11 1
    coefficientSeed (bitIndex 12 8) (by rfl),
    if_neg (by decide)]
  have h_12_12_8 :
    (layerAct ((pf2Rotations θ).drop 12) coefficientSeed).ofLp
      (bitIndex 12 8) = 0 :=
    coeff_zero_of_not_backward ((L₁ ++ L₂ ++ L₂ ++ L₁).drop 12) θ
      (bitIndex 12 8) (bitIndex 0 8) (by decide)
  have hp : partner (generator 1) (bitIndex 12 8) = bitIndex 0 8 := by decide
  have hs : partnerSign (generator 1) (bitIndex 12 8) = (-1 : ℂ) := by
    rw [partnerSign, show
      (phaseMul 1 ((generator 1) * herm (bitIndex 12 8))).phase
        - (herm (partner (generator 1) (bitIndex 12 8))).phase = 2 by decide]
    all_goals exact iPow_two
  rw [hp, hs, h_12_12_8, (suffixCoefficient_12_0_8 θ)]
  ring
private theorem suffixCoefficient_10_12_8 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 10) coefficientSeed).ofLp
    (bitIndex 12 8) = (Real.sin θ : ℂ) := by
  rw [suffix_coeff_step θ 10 0
    coefficientSeed (bitIndex 12 8) (by rfl),
    if_pos (by decide)]
  all_goals exact (suffixCoefficient_11_12_8 θ)
private theorem suffixCoefficient_9_12_8 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 9) coefficientSeed).ofLp
    (bitIndex 12 8) = (Real.sin θ : ℂ) := by
  rw [suffix_coeff_step θ 9 6
    coefficientSeed (bitIndex 12 8) (by rfl),
    if_pos (by decide)]
  all_goals exact (suffixCoefficient_10_12_8 θ)
private theorem suffixCoefficient_8_20_8 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 8) coefficientSeed).ofLp
    (bitIndex 20 8) = -(Real.sin θ : ℂ) ^ 2 := by
  rw [suffix_coeff_step θ 8 5
    coefficientSeed (bitIndex 20 8) (by rfl),
    if_neg (by decide)]
  have h_9_20_8 :
    (layerAct ((pf2Rotations θ).drop 9) coefficientSeed).ofLp
      (bitIndex 20 8) = 0 :=
    coeff_zero_of_not_backward ((L₁ ++ L₂ ++ L₂ ++ L₁).drop 9) θ
      (bitIndex 20 8) (bitIndex 0 8) (by decide)
  have hp : partner (generator 5) (bitIndex 20 8) = bitIndex 12 8 := by decide
  have hs : partnerSign (generator 5) (bitIndex 20 8) = (1 : ℂ) := by
    rw [partnerSign, show
      (phaseMul 1 ((generator 5) * herm (bitIndex 20 8))).phase
        - (herm (partner (generator 5) (bitIndex 20 8))).phase = 0 by decide]
    all_goals exact iPow_zero
  rw [hp, hs, h_9_20_8, (suffixCoefficient_9_12_8 θ)]
  ring
private theorem suffixCoefficient_8_12_8 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 8) coefficientSeed).ofLp
    (bitIndex 12 8) = (Real.cos θ : ℂ) * (Real.sin θ : ℂ) := by
  rw [suffix_coeff_step θ 8 5
    coefficientSeed (bitIndex 12 8) (by rfl),
    if_neg (by decide)]
  have h_9_20_8 :
    (layerAct ((pf2Rotations θ).drop 9) coefficientSeed).ofLp
      (bitIndex 20 8) = 0 :=
    coeff_zero_of_not_backward ((L₁ ++ L₂ ++ L₂ ++ L₁).drop 9) θ
      (bitIndex 20 8) (bitIndex 0 8) (by decide)
  have hp : partner (generator 5) (bitIndex 12 8) = bitIndex 20 8 := by decide
  have hs : partnerSign (generator 5) (bitIndex 12 8) = (-1 : ℂ) := by
    rw [partnerSign, show
      (phaseMul 1 ((generator 5) * herm (bitIndex 12 8))).phase
        - (herm (partner (generator 5) (bitIndex 12 8))).phase = 2 by decide]
    all_goals exact iPow_two
  rw [hp, hs, (suffixCoefficient_9_12_8 θ), h_9_20_8]
  ring
private theorem suffixCoefficient_7_22_12 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 7) coefficientSeed).ofLp
    (bitIndex 22 12) = (Real.sin θ : ℂ) ^ 3 := by
  rw [suffix_coeff_step θ 7 4
    coefficientSeed (bitIndex 22 12) (by rfl),
    if_neg (by decide)]
  have h_8_22_12 :
    (layerAct ((pf2Rotations θ).drop 8) coefficientSeed).ofLp
      (bitIndex 22 12) = 0 :=
    coeff_zero_of_not_backward ((L₁ ++ L₂ ++ L₂ ++ L₁).drop 8) θ
      (bitIndex 22 12) (bitIndex 0 8) (by decide)
  have hp : partner (generator 4) (bitIndex 22 12) = bitIndex 20 8 := by decide
  have hs : partnerSign (generator 4) (bitIndex 22 12) = (1 : ℂ) := by
    rw [partnerSign, show
      (phaseMul 1 ((generator 4) * herm (bitIndex 22 12))).phase
        - (herm (partner (generator 4) (bitIndex 22 12))).phase = 0 by decide]
    all_goals exact iPow_zero
  rw [hp, hs, h_8_22_12, (suffixCoefficient_8_20_8 θ)]
  ring
private theorem suffixCoefficient_7_20_8 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 7) coefficientSeed).ofLp
    (bitIndex 20 8) = -(Real.cos θ : ℂ) * (Real.sin θ : ℂ) ^ 2 := by
  rw [suffix_coeff_step θ 7 4
    coefficientSeed (bitIndex 20 8) (by rfl),
    if_neg (by decide)]
  have h_8_22_12 :
    (layerAct ((pf2Rotations θ).drop 8) coefficientSeed).ofLp
      (bitIndex 22 12) = 0 :=
    coeff_zero_of_not_backward ((L₁ ++ L₂ ++ L₂ ++ L₁).drop 8) θ
      (bitIndex 22 12) (bitIndex 0 8) (by decide)
  have hp : partner (generator 4) (bitIndex 20 8) = bitIndex 22 12 := by decide
  have hs : partnerSign (generator 4) (bitIndex 20 8) = (-1 : ℂ) := by
    rw [partnerSign, show
      (phaseMul 1 ((generator 4) * herm (bitIndex 20 8))).phase
        - (herm (partner (generator 4) (bitIndex 20 8))).phase = 2 by decide]
    all_goals exact iPow_two
  rw [hp, hs, (suffixCoefficient_8_20_8 θ), h_8_22_12]
  ring
private theorem suffixCoefficient_7_14_12 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 7) coefficientSeed).ofLp
    (bitIndex 14 12) = (Real.cos θ : ℂ) * (Real.sin θ : ℂ) ^ 2 := by
  rw [suffix_coeff_step θ 7 4
    coefficientSeed (bitIndex 14 12) (by rfl),
    if_neg (by decide)]
  have h_8_14_12 :
    (layerAct ((pf2Rotations θ).drop 8) coefficientSeed).ofLp
      (bitIndex 14 12) = 0 :=
    coeff_zero_of_not_backward ((L₁ ++ L₂ ++ L₂ ++ L₁).drop 8) θ
      (bitIndex 14 12) (bitIndex 0 8) (by decide)
  have hp : partner (generator 4) (bitIndex 14 12) = bitIndex 12 8 := by decide
  have hs : partnerSign (generator 4) (bitIndex 14 12) = (-1 : ℂ) := by
    rw [partnerSign, show
      (phaseMul 1 ((generator 4) * herm (bitIndex 14 12))).phase
        - (herm (partner (generator 4) (bitIndex 14 12))).phase = 2 by decide]
    all_goals exact iPow_two
  rw [hp, hs, h_8_14_12, (suffixCoefficient_8_12_8 θ)]
  ring
private theorem suffixCoefficient_7_12_8 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 7) coefficientSeed).ofLp
    (bitIndex 12 8) = (Real.cos θ : ℂ) ^ 2 * (Real.sin θ : ℂ) := by
  rw [suffix_coeff_step θ 7 4
    coefficientSeed (bitIndex 12 8) (by rfl),
    if_neg (by decide)]
  have h_8_14_12 :
    (layerAct ((pf2Rotations θ).drop 8) coefficientSeed).ofLp
      (bitIndex 14 12) = 0 :=
    coeff_zero_of_not_backward ((L₁ ++ L₂ ++ L₂ ++ L₁).drop 8) θ
      (bitIndex 14 12) (bitIndex 0 8) (by decide)
  have hp : partner (generator 4) (bitIndex 12 8) = bitIndex 14 12 := by decide
  have hs : partnerSign (generator 4) (bitIndex 12 8) = (1 : ℂ) := by
    rw [partnerSign, show
      (phaseMul 1 ((generator 4) * herm (bitIndex 12 8))).phase
        - (herm (partner (generator 4) (bitIndex 12 8))).phase = 0 by decide]
    all_goals exact iPow_zero
  rw [hp, hs, (suffixCoefficient_8_12_8 θ), h_8_14_12]
  ring
private theorem suffixCoefficient_6_22_12 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 6) coefficientSeed).ofLp
    (bitIndex 22 12) = (Real.sin θ : ℂ) ^ 3 := by
  rw [suffix_coeff_step θ 6 6
    coefficientSeed (bitIndex 22 12) (by rfl),
    if_pos (by decide)]
  all_goals exact (suffixCoefficient_7_22_12 θ)
private theorem suffixCoefficient_6_20_8 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 6) coefficientSeed).ofLp
    (bitIndex 20 8) = -(Real.cos θ : ℂ) * (Real.sin θ : ℂ) ^ 2 := by
  rw [suffix_coeff_step θ 6 6
    coefficientSeed (bitIndex 20 8) (by rfl),
    if_pos (by decide)]
  all_goals exact (suffixCoefficient_7_20_8 θ)
private theorem suffixCoefficient_6_14_12 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 6) coefficientSeed).ofLp
    (bitIndex 14 12) = (Real.cos θ : ℂ) * (Real.sin θ : ℂ) ^ 2 := by
  rw [suffix_coeff_step θ 6 6
    coefficientSeed (bitIndex 14 12) (by rfl),
    if_pos (by decide)]
  all_goals exact (suffixCoefficient_7_14_12 θ)
private theorem suffixCoefficient_6_12_8 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 6) coefficientSeed).ofLp
    (bitIndex 12 8) = (Real.cos θ : ℂ) ^ 2 * (Real.sin θ : ℂ) := by
  rw [suffix_coeff_step θ 6 6
    coefficientSeed (bitIndex 12 8) (by rfl),
    if_pos (by decide)]
  all_goals exact (suffixCoefficient_7_12_8 θ)
private theorem suffixCoefficient_5_22_12 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 5) coefficientSeed).ofLp
    (bitIndex 22 12) = 2 * (Real.cos θ : ℂ) * (Real.sin θ : ℂ) ^ 3 := by
  rw [suffix_coeff_step θ 5 5
    coefficientSeed (bitIndex 22 12) (by rfl),
    if_neg (by decide)]
  have hp : partner (generator 5) (bitIndex 22 12) = bitIndex 14 12 := by decide
  have hs : partnerSign (generator 5) (bitIndex 22 12) = (-1 : ℂ) := by
    rw [partnerSign, show
      (phaseMul 1 ((generator 5) * herm (bitIndex 22 12))).phase
        - (herm (partner (generator 5) (bitIndex 22 12))).phase = 2 by decide]
    all_goals exact iPow_two
  rw [hp, hs, (suffixCoefficient_6_22_12 θ), (suffixCoefficient_6_14_12 θ)]
  ring
private theorem suffixCoefficient_5_20_8 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 5) coefficientSeed).ofLp
    (bitIndex 20 8) = -2 * (Real.cos θ : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 2 := by
  rw [suffix_coeff_step θ 5 5
    coefficientSeed (bitIndex 20 8) (by rfl),
    if_neg (by decide)]
  have hp : partner (generator 5) (bitIndex 20 8) = bitIndex 12 8 := by decide
  have hs : partnerSign (generator 5) (bitIndex 20 8) = (1 : ℂ) := by
    rw [partnerSign, show
      (phaseMul 1 ((generator 5) * herm (bitIndex 20 8))).phase
        - (herm (partner (generator 5) (bitIndex 20 8))).phase = 0 by decide]
    all_goals exact iPow_zero
  rw [hp, hs, (suffixCoefficient_6_20_8 θ), (suffixCoefficient_6_12_8 θ)]
  ring
private theorem suffixCoefficient_4_22_12 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 4) coefficientSeed).ofLp
    (bitIndex 22 12) = 4 * (Real.cos θ : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 3 := by
  rw [suffix_coeff_step θ 4 4
    coefficientSeed (bitIndex 22 12) (by rfl),
    if_neg (by decide)]
  have hp : partner (generator 4) (bitIndex 22 12) = bitIndex 20 8 := by decide
  have hs : partnerSign (generator 4) (bitIndex 22 12) = (1 : ℂ) := by
    rw [partnerSign, show
      (phaseMul 1 ((generator 4) * herm (bitIndex 22 12))).phase
        - (herm (partner (generator 4) (bitIndex 22 12))).phase = 0 by decide]
    all_goals exact iPow_zero
  rw [hp, hs, (suffixCoefficient_5_22_12 θ), (suffixCoefficient_5_20_8 θ)]
  ring
private theorem suffixCoefficient_3_22_12 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 3) coefficientSeed).ofLp
    (bitIndex 22 12) = 4 * (Real.cos θ : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 3 := by
  rw [suffix_coeff_step θ 3 3
    coefficientSeed (bitIndex 22 12) (by rfl),
    if_pos (by decide)]
  all_goals exact (suffixCoefficient_4_22_12 θ)
private theorem suffixCoefficient_2_54_28 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 2) coefficientSeed).ofLp
    (bitIndex 54 28) = 4 * (Real.cos θ : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 4 := by
  rw [suffix_coeff_step θ 2 2
    coefficientSeed (bitIndex 54 28) (by rfl),
    if_neg (by decide)]
  have h_3_54_28 :
    (layerAct ((pf2Rotations θ).drop 3) coefficientSeed).ofLp
      (bitIndex 54 28) = 0 :=
    coeff_zero_of_not_backward ((L₁ ++ L₂ ++ L₂ ++ L₁).drop 3) θ
      (bitIndex 54 28) (bitIndex 0 8) (by decide)
  have hp : partner (generator 2) (bitIndex 54 28) = bitIndex 22 12 := by decide
  have hs : partnerSign (generator 2) (bitIndex 54 28) = (-1 : ℂ) := by
    rw [partnerSign, show
      (phaseMul 1 ((generator 2) * herm (bitIndex 54 28))).phase
        - (herm (partner (generator 2) (bitIndex 54 28))).phase = 2 by decide]
    all_goals exact iPow_two
  rw [hp, hs, h_3_54_28, (suffixCoefficient_3_22_12 θ)]
  ring
private theorem suffixCoefficient_1_54_28 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 1) coefficientSeed).ofLp
    (bitIndex 54 28) = 4 * (Real.cos θ : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 4 := by
  rw [suffix_coeff_step θ 1 1
    coefficientSeed (bitIndex 54 28) (by rfl),
    if_pos (by decide)]
  all_goals exact (suffixCoefficient_2_54_28 θ)
private theorem suffixCoefficient_0_55_30 (θ : ℝ) :
    (layerAct ((pf2Rotations θ).drop 0) coefficientSeed).ofLp
    (bitIndex 55 30) = -4 * (Real.cos θ : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 5 := by
  rw [suffix_coeff_step θ 0 0
    coefficientSeed (bitIndex 55 30) (by rfl),
    if_neg (by decide)]
  have h_1_55_30 :
    (layerAct ((pf2Rotations θ).drop 1) coefficientSeed).ofLp
      (bitIndex 55 30) = 0 :=
    coeff_zero_of_not_backward ((L₁ ++ L₂ ++ L₂ ++ L₁).drop 1) θ
      (bitIndex 55 30) (bitIndex 0 8) (by decide)
  have hp : partner (generator 0) (bitIndex 55 30) = bitIndex 54 28 := by decide
  have hs : partnerSign (generator 0) (bitIndex 55 30) = (1 : ℂ) := by
    rw [partnerSign, show
      (phaseMul 1 ((generator 0) * herm (bitIndex 55 30))).phase
        - (herm (partner (generator 0) (bitIndex 55 30))).phase = 0 by decide]
    all_goals exact iPow_zero
  rw [hp, hs, h_1_55_30, (suffixCoefficient_1_54_28 θ)]
  ring
end Lean4LPD.LayerCounterexample
end
end

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.LayerCounterexample
open PauliString LayerWitness Finset
attribute [local irreducible] layerAct
namespace Lean4LPD.LayerCounterexample
theorem _root_.solution (θ : ℝ) :
    coeff (pf2Output θ) (cls P₆) =
      -4 * (Real.cos θ : ℂ) ^ 2 * (Real.sin θ : ℂ) ^ 5 := by
  change (coeffVec (pf2Output θ)).ofLp (cls P₆) = _
  rw [pf2Output, coeffVec_layerConj _ (pf2Rotations_hermitian θ), input_coeffVec]
  have hseed : cls (Z (3 : Fin 8)) = bitIndex 0 8 := by decide
  have htarget : cls P₆ = bitIndex 55 30 := by decide
  rw [hseed, htarget]
  simpa only [List.drop_zero] using suffixCoefficient_0_55_30 θ
end Lean4LPD.LayerCounterexample
