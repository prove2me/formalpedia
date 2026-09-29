-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_schwartz_godementZeta2_whittaker_eq_godementZeta2_section_and_dual_of_equivariant_embedding
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/1d5cd25a-e944-5f68-9666-47f95e210223

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Theorems.Thm_LanglandsTunnell_CubicInduction_matFourier22_comp_inv_mul_eq
import Theorems.Thm_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_of_finite_maximalSpectrum
import Theorems.Thm_AutomorphicForm_secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_CubicInduction_isSchwartzBruhat_colFourier23
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_schwartz_godementZeta2_whittaker_eq_godementZeta2_section_and_dual_of_equivariant_embedding

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

namespace KCSA

section KBblock
open IsDedekindDomain NumberField
open scoped WithZero Pointwise

section Valuation

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem exists_uniformizer :
    ∃ ϖ : v.adicCompletion K, Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer K v
  exact ⟨((WithVal.equiv (HeightOneSpectrum.valuation K v)).symm π : v.adicCompletion K),
    by rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hπ⟩

variable {K v}

theorem uniformizer_ne_zero {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) :
    ϖ ≠ 0 := by
  intro h; rw [h, Valuation.map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm

theorem v_uniformizer_zpow {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (j : ℤ) : Valued.v (ϖ ^ j) = WithZero.exp (-j) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem v_add_le {x y : v.adicCompletion K} {γ : ℤᵐ⁰} (hx : Valued.v x ≤ γ) (hy : Valued.v y ≤ γ) :
    Valued.v (x + y) ≤ γ :=
  (Valuation.map_add _ x y).trans (max_le hx hy)

theorem v_sub_le {x y : v.adicCompletion K} {γ : ℤᵐ⁰} (hx : Valued.v x ≤ γ) (hy : Valued.v y ≤ γ) :
    Valued.v (x - y) ≤ γ := by
  rw [sub_eq_add_neg]; exact v_add_le hx (by rwa [Valuation.map_neg])

theorem exp_neg_succ_lt_one (n : ℕ) : WithZero.exp (-((n : ℤ) + 1)) < (1 : ℤᵐ⁰) := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega

theorem exp_neg_succ_le_one (n : ℕ) : WithZero.exp (-((n : ℤ) + 1)) ≤ (1 : ℤᵐ⁰) :=
  (exp_neg_succ_lt_one n).le

theorem exp_antitone_succ (n : ℕ) :
    WithZero.exp (-(((n + 1 : ℕ) : ℤ) + 1)) ≤ WithZero.exp (-((n : ℤ) + 1)) := by
  rw [WithZero.exp_le_exp]; push_cast; omega

theorem eq_zero_of_forall_v_le (x : v.adicCompletion K)
    (h : ∀ n : ℕ, Valued.v x ≤ WithZero.exp (-((n : ℤ) + 1))) : x = 0 := by
  by_contra hx
  have hx' : Valued.v x ≠ 0 := by rwa [ne_eq, Valuation.zero_iff]
  set L := WithZero.log (Valued.v x) with hL
  have hxL : Valued.v x = WithZero.exp L := (WithZero.exp_log hx').symm
  have := h ((-L).toNat)
  rw [hxL, WithZero.exp_le_exp] at this
  omega

theorem v_eq_one_of_sub_one {x : v.adicCompletion K} {n : ℕ}
    (hx : Valued.v (x - 1) ≤ WithZero.exp (-((n : ℤ) + 1))) : Valued.v x = 1 := by
  have : x = 1 + (x - 1) := by ring
  rw [this]
  exact Valuation.map_one_add_of_lt _ (hx.trans_lt (exp_neg_succ_lt_one n))

theorem ne_zero_of_v_eq_one {x : v.adicCompletion K} (hx : Valued.v x = 1) : x ≠ 0 := by
  intro h; rw [h, Valuation.map_zero] at hx; exact zero_ne_one hx

theorem isOpen_ball (m : ℤ) : IsOpen {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp m} := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer K v
  have hϖ0 : ϖ ≠ 0 := uniformizer_ne_zero hϖ
  have hset : {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp m} =
      (fun x => ϖ ^ m * x) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, v_uniformizer_zpow hϖ,
      WithZero.exp_neg]
    constructor
    · intro h
      calc (WithZero.exp m)⁻¹ * Valued.v x ≤ (WithZero.exp m)⁻¹ * WithZero.exp m :=
            mul_le_mul_right h _
        _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
    · intro h
      calc Valued.v x = WithZero.exp m * ((WithZero.exp m)⁻¹ * Valued.v x) := by
            rw [← mul_assoc, mul_inv_cancel₀ WithZero.exp_ne_zero, one_mul]
        _ ≤ WithZero.exp m * 1 := mul_le_mul_right h _
        _ = WithZero.exp m := mul_one _
  rw [hset]
  exact (Valued.isOpen_valuationSubring _).preimage (continuous_const_mul _)

end Valuation

section GLtwo

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => HeightOneSpectrum.adicCompletion K v
local notation "Mat" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)
local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)

theorem gl_eq_of_entries {g h : G}
    (h00 : (g : Mat) 0 0 = (h : Mat) 0 0) (h01 : (g : Mat) 0 1 = (h : Mat) 0 1)
    (h10 : (g : Mat) 1 0 = (h : Mat) 1 0) (h11 : (g : Mat) 1 1 = (h : Mat) 1 1) : g = h := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

def lvl (n : ℕ) : ℤᵐ⁰ := WithZero.exp (-((n : ℤ) + 1))

theorem lvl_le_one (n : ℕ) : lvl n ≤ 1 := exp_neg_succ_le_one n

theorem lvl_lt_one (n : ℕ) : lvl n < 1 := exp_neg_succ_lt_one n

theorem lvl_succ_le (n : ℕ) : lvl (n + 1) ≤ lvl n := exp_antitone_succ n

theorem v_mul_le_lvl_left {n : ℕ} {x y : F} (hx : Valued.v x ≤ lvl n) (hy : Valued.v y ≤ 1) :
    Valued.v (x * y) ≤ lvl n := by
  rw [Valuation.map_mul]; simpa using mul_le_mul' hx hy

theorem v_mul_le_lvl_right {n : ℕ} {x y : F} (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ lvl n) :
    Valued.v (x * y) ≤ lvl n := by
  rw [Valuation.map_mul]; simpa using mul_le_mul' hx hy

structure IsCong (n : ℕ) (m : Mat) : Prop where
  h00 : Valued.v (m 0 0 - 1) ≤ lvl n
  h01 : Valued.v (m 0 1) ≤ lvl n
  h10 : Valued.v (m 1 0) ≤ lvl n
  h11 : Valued.v (m 1 1 - 1) ≤ lvl n

theorem IsCong.v00 {n : ℕ} {m : Mat} (h : IsCong n m) : Valued.v (m 0 0) = 1 := v_eq_one_of_sub_one h.h00
theorem IsCong.v11 {n : ℕ} {m : Mat} (h : IsCong n m) : Valued.v (m 1 1) = 1 := v_eq_one_of_sub_one h.h11

theorem IsCong.integral {n : ℕ} {m : Mat} (h : IsCong n m) (i j : Fin 2) : Valued.v (m i j) ≤ 1 := by
  fin_cases i <;> fin_cases j
  · exact h.v00.le
  · exact h.h01.trans (lvl_le_one n)
  · exact h.h10.trans (lvl_le_one n)
  · exact h.v11.le

theorem IsCong.sub_one {n : ℕ} {m : Mat} (h : IsCong n m) (i j : Fin 2) : Valued.v ((m - 1) i j) ≤ lvl n := by
  fin_cases i <;> fin_cases j
  · simpa [Matrix.sub_apply] using h.h00
  · simpa [Matrix.sub_apply] using h.h01
  · simpa [Matrix.sub_apply] using h.h10
  · simpa [Matrix.sub_apply] using h.h11

theorem isCong_of_sub_one {n : ℕ} {m : Mat} (h : ∀ i j, Valued.v ((m - 1) i j) ≤ lvl n) : IsCong n m := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Matrix.sub_apply] using h 0 0
  · simpa [Matrix.sub_apply] using h 0 1
  · simpa [Matrix.sub_apply] using h 1 0
  · simpa [Matrix.sub_apply] using h 1 1

theorem isCong_one (n : ℕ) : IsCong n (1 : Mat) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

theorem IsCong.mul {n : ℕ} {a b : Mat} (ha : IsCong n a) (hb : IsCong n b) : IsCong n (a * b) := by
  have e00 : (a * b) 0 0 - 1 = (a 0 0 - 1) * b 0 0 + (b 0 0 - 1) + a 0 1 * b 1 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]; ring
  have e01 : (a * b) 0 1 = a 0 0 * b 0 1 + a 0 1 * b 1 1 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (a * b) 1 0 = a 1 0 * b 0 0 + a 1 1 * b 1 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (a * b) 1 1 - 1 = a 1 0 * b 0 1 + ((a 1 1 - 1) * b 1 1 + (b 1 1 - 1)) := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e00]
    exact v_add_le (v_add_le (v_mul_le_lvl_left ha.h00 hb.v00.le) hb.h00)
      (v_mul_le_lvl_left ha.h01 (hb.integral 1 0))
  · rw [e01]
    exact v_add_le (v_mul_le_lvl_right ha.v00.le hb.h01) (v_mul_le_lvl_left ha.h01 hb.v11.le)
  · rw [e10]
    exact v_add_le (v_mul_le_lvl_left ha.h10 hb.v00.le) (v_mul_le_lvl_right ha.v11.le hb.h10)
  · rw [e11]
    exact v_add_le (v_mul_le_lvl_left ha.h10 (hb.integral 0 1))
      (v_add_le (v_mul_le_lvl_left ha.h11 hb.v11.le) hb.h11)

theorem IsCong.v_det_sub_one {n : ℕ} {m : Mat} (h : IsCong n m) :
    Valued.v (m 0 0 * m 1 1 - m 0 1 * m 1 0 - 1) ≤ lvl n := by
  have : m 0 0 * m 1 1 - m 0 1 * m 1 0 - 1 = (m 0 0 - 1) * m 1 1 + (m 1 1 - 1) - m 0 1 * m 1 0 := by ring
  rw [this]
  exact v_sub_le (v_add_le (v_mul_le_lvl_left h.h00 h.v11.le) h.h11) (v_mul_le_lvl_left h.h01 (h.integral 1 0))

theorem IsCong.v_det {n : ℕ} {m : Mat} (h : IsCong n m) : Valued.v (m 0 0 * m 1 1 - m 0 1 * m 1 0) = 1 :=
  v_eq_one_of_sub_one h.v_det_sub_one

theorem IsCong.inv {n : ℕ} {g : G} (h : IsCong n (g : Mat)) : IsCong n ((g⁻¹ : G) : Mat) := by
  set D : F := (g : Mat) 0 0 * (g : Mat) 1 1 - (g : Mat) 0 1 * (g : Mat) 1 0 with hD
  have hvD : Valued.v D = 1 := h.v_det
  have hD0 : D ≠ 0 := ne_zero_of_v_eq_one hvD
  set B : Mat := !![(g : Mat) 1 1 / D, -(g : Mat) 0 1 / D; -(g : Mat) 1 0 / D, (g : Mat) 0 0 / D] with hB
  have hmul : (g : Mat) * B = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
  have hinv : ((g⁻¹ : G) : Mat) = B := by
    rw [Matrix.coe_units_inv, Matrix.inv_eq_right_inv hmul]
  have hvdiv : ∀ x : F, Valued.v (x / D) = Valued.v x := by
    intro x; rw [map_div₀, hvD, div_one]
  rw [hinv]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : B 0 0 - 1 = ((g : Mat) 1 1 - 1 - (D - 1)) / D := by
      simp only [B, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]
      field_simp; ring
    rw [this, hvdiv]
    exact v_sub_le h.h11 h.v_det_sub_one
  · have : B 0 1 = -(g : Mat) 0 1 / D := by simp [B]
    rw [this, hvdiv, Valuation.map_neg]; exact h.h01
  · have : B 1 0 = -(g : Mat) 1 0 / D := by simp [B]
    rw [this, hvdiv, Valuation.map_neg]; exact h.h10
  · have : B 1 1 - 1 = ((g : Mat) 0 0 - 1 - (D - 1)) / D := by
      simp only [B, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one]
      field_simp; ring
    rw [this, hvdiv]
    exact v_sub_le h.h00 h.v_det_sub_one

theorem IsCong.conj {n : ℕ} {m k kinv : Mat} (hm : IsCong n m)
    (hk : ∀ i j, Valued.v (k i j) ≤ 1) (hkinv : ∀ i j, Valued.v (kinv i j) ≤ 1) (hkk : kinv * k = 1) :
    IsCong n (kinv * m * k) := by
  apply isCong_of_sub_one
  have hE : kinv * m * k - 1 = kinv * (m - 1) * k := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hkk]
  intro i j
  rw [hE, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two]
  have t : ∀ a b : Fin 2, Valued.v (kinv i a * (m - 1) a b * k b j) ≤ lvl n := fun a b =>
    v_mul_le_lvl_left (v_mul_le_lvl_right (hkinv i a) (hm.sub_one a b)) (hk b j)
  have t' : ∀ b : Fin 2, Valued.v ((kinv i 0 * (m - 1) 0 b + kinv i 1 * (m - 1) 1 b) * k b j) ≤ lvl n := by
    intro b
    rw [add_mul]
    exact v_add_le (t 0 b) (t 1 b)
  exact v_add_le (t' 0) (t' 1)

variable (K v) in

private def _root_.KCSA.congr (n : ℕ) : Subgroup G where
  carrier := {g | IsCong n (g : Mat)}
  one_mem' := by simpa using isCong_one n
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Matrix.GeneralLinearGroup.coe_mul] at *
    exact ha.mul hb
  inv_mem' := by
    intro g hg
    exact hg.inv

p2m_export "KCSA" "congr"
theorem mem_congr {n : ℕ} {g : G} : g ∈ congr K v n ↔ IsCong n (g : Mat) := Iff.rfl

theorem congr_antitone (n : ℕ) : congr K v (n + 1) ≤ congr K v n := by
  intro g hg
  exact ⟨hg.h00.trans (lvl_succ_le n), hg.h01.trans (lvl_succ_le n), hg.h10.trans (lvl_succ_le n),
    hg.h11.trans (lvl_succ_le n)⟩

theorem congr_antitone' {m n : ℕ} (h : m ≤ n) : congr K v n ≤ congr K v m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (congr_antitone _).trans ih

theorem isOpen_congr (n : ℕ) : IsOpen (congr K v n : Set G) := by
  have hc : ∀ i j : Fin 2, Continuous fun g : G => (g : Mat) i j := fun i j =>
    Units.continuous_val.matrix_elem i j
  have hball : IsOpen {x : F | Valued.v x ≤ lvl n} := isOpen_ball _
  have hball' : IsOpen {x : F | Valued.v (x - 1) ≤ lvl n} :=
    hball.preimage (continuous_id.sub continuous_const)
  have hset : (congr K v n : Set G) =
      ((fun g : G => (g : Mat) 0 0) ⁻¹' {x : F | Valued.v (x - 1) ≤ lvl n}) ∩
      ((fun g : G => (g : Mat) 0 1) ⁻¹' {x : F | Valued.v x ≤ lvl n}) ∩
      ((fun g : G => (g : Mat) 1 0) ⁻¹' {x : F | Valued.v x ≤ lvl n}) ∩
      ((fun g : G => (g : Mat) 1 1) ⁻¹' {x : F | Valued.v (x - 1) ≤ lvl n}) := by
    ext g
    simp only [SetLike.mem_coe, mem_congr, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨⟨⟨h.h00, h.h01⟩, h.h10⟩, h.h11⟩, fun h => ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩⟩
  rw [hset]
  exact (((hball'.preimage (hc 0 0)).inter (hball.preimage (hc 0 1))).inter
    (hball.preimage (hc 1 0))).inter (hball'.preimage (hc 1 1))

theorem congr_subset_localIntegralSet (n : ℕ) :
    (congr K v n : Set G) ⊆ AutomorphicForm.localIntegralSet K v := by
  intro g hg
  rw [AutomorphicForm.mem_localIntegralSet]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact (mem_congr.mp hg).integral i j
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact (mem_congr.mp ((congr K v n).inv_mem hg)).integral i j

theorem isCompact_congr (n : ℕ) : IsCompact (congr K v n : Set G) :=
  (AutomorphicForm.isCompact_localIntegralSet K v).of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ (isOpen_congr n)) (congr_subset_localIntegralSet n)

theorem eq_one_of_forall_mem_congr {g : G} (hg : ∀ n, g ∈ congr K v n) : g = 1 := by
  have h00 : (g : Mat) 0 0 - 1 = 0 := eq_zero_of_forall_v_le _ fun n => (hg n).h00
  have h01 : (g : Mat) 0 1 = 0 := eq_zero_of_forall_v_le _ fun n => (hg n).h01
  have h10 : (g : Mat) 1 0 = 0 := eq_zero_of_forall_v_le _ fun n => (hg n).h10
  have h11 : (g : Mat) 1 1 - 1 = 0 := eq_zero_of_forall_v_le _ fun n => (hg n).h11
  apply gl_eq_of_entries
  · simpa [sub_eq_zero] using h00
  · simpa using h01
  · simpa using h10
  · simpa [sub_eq_zero] using h11

theorem exists_congr_subset {U : Set G} (hU : IsOpen U) (h1 : (1 : G) ∈ U) :
    ∃ n, (congr K v n : Set G) ⊆ U := by
  have hdir : Directed (fun x1 x2 : Set G => x1 ⊇ x2) fun n : ℕ => (congr K v n : Set G) := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · exact fun g hg => congr_antitone' (le_max_left i j) hg
    · exact fun g hg => congr_antitone' (le_max_right i j) hg
  refine exists_subset_nhds_of_isCompact' hdir (fun n => isCompact_congr n)
    (fun n => Subgroup.isClosed_of_isOpen _ (isOpen_congr n)) ?_
  intro x hx
  rw [Set.mem_iInter] at hx
  have : x = 1 := eq_one_of_forall_mem_congr hx
  subst this
  exact hU.mem_nhds h1

theorem conj_mem_congr {n : ℕ} {N : Ideal (𝓞 K)} {u k : G} (hu : u ∈ congr K v n)
    (hk : k ∈ AdelicDock.localLevelOne (𝓞 K) K v N) : k⁻¹ * u * k ∈ congr K v n := by
  rw [AdelicDock.mem_localLevelOne_iff] at hk
  rw [mem_congr, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  refine (mem_congr.mp hu).conj (fun i j => ?_) (fun i j => ?_) ?_
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp (hk.1.integral i j)
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp (hk.2.integral i j)
  · rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel]; rfl

end GLtwo

end KBblock

section Extras

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => HeightOneSpectrum.adicCompletion K v
local notation "Mat" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)
local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)

theorem det_eq_formula (m : Mat) : m.det = m 0 0 * m 1 1 - m 0 1 * m 1 0 := Matrix.det_fin_two m

theorem IsCong.v_det' {n : ℕ} {m : Mat} (h : IsCong n m) : Valued.v m.det = 1 := by
  rw [det_eq_formula]; exact h.v_det

theorem IsCong.v_det_sub_one' {n : ℕ} {m : Mat} (h : IsCong n m) : Valued.v (m.det - 1) ≤ lvl n := by
  rw [det_eq_formula]; exact h.v_det_sub_one

end Extras

section Dictionary

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ

noncomputable def qR : ℝ := ((Ideal.absNorm p.asIdeal : NNReal) : ℝ)

theorem one_lt_qR : 1 < qR p := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p
  unfold qR; exact_mod_cast this

theorem qR_pos : 0 < qR p := lt_trans one_pos (one_lt_qR p)

theorem norm_eq_qR_zpow (y : F) (j : ℤ) (hy : Valued.v y = WithZero.exp (-j)) : ‖y‖ = qR p ^ (-j) := by
  rw [NumberField.FinitePlace.norm_def, hy, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, NNReal.coe_zpow]
  unfold qR
  congr 1

theorem norm_eq_one_of_v {u : F} (hu : Valued.v u = 1) : ‖u‖ = 1 := by
  have := norm_eq_qR_zpow p u 0 (by rw [hu, neg_zero, WithZero.exp_zero])
  rw [this, neg_zero, zpow_zero]

end Dictionary

end KCSA

noncomputable section

namespace KCS

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (p.adicCompletion ℚ)
local notation "G" => (GL (Fin 2) (p.adicCompletion ℚ))
local notation "M2" => (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))

local instance instGLmeas : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
local instance instGLborel : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

local instance kcs_secondCountable : SecondCountableTopology (GL (Fin 2) (p.adicCompletion ℚ)) :=
  (AutomorphicForm.secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom ℚ p).1

local instance kcs_locallyCompact : LocallyCompactSpace (GL (Fin 2) (p.adicCompletion ℚ)) :=
  AutomorphicForm.locallyCompactSpace_localGL ℚ p

def gjIntegrand (c : G → ℂ) (φ : M2 → ℂ) (χ : Fˣ →* ℂˣ) (s : ℂ) (g : G) : ℂ :=
  c g * φ ((g : G) : M2) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
    ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) ^ s

theorem godementZeta2_eq_integral_gjIntegrand (μ₂ : Measure G) (c : G → ℂ) (φ : M2 → ℂ) (χ : Fˣ →* ℂˣ) (s : ℂ) :
    godementZeta2 p μ₂ c φ χ s = ∫ g, gjIntegrand p c φ χ s g ∂μ₂ := rfl

def leftAvg (μ₂ : Measure G) (K' : Set G) (u : G → ℂ) (g : G) : ℂ :=
  (μ₂.real K')⁻¹ * ∫ k in K', u (k * g) ∂μ₂

section K2

local instance k2_secondCountable : SecondCountableTopology (GL (Fin 2) (p.adicCompletion ℚ)) :=
  (AutomorphicForm.secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom ℚ p).1

local instance k2_locallyCompact : LocallyCompactSpace (GL (Fin 2) (p.adicCompletion ℚ)) :=
  AutomorphicForm.locallyCompactSpace_localGL ℚ p

theorem isMulRightInvariant_of_isHaarMeasure (μ₂ : Measure G) [μ₂.IsHaarMeasure] : μ₂.IsMulRightInvariant :=
  AutomorphicForm.isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_of_finite_maximalSpectrum
    (p.adicCompletion ℚ) μ₂ inferInstance

theorem k2_real_ne_zero (μ₂ : Measure G) [μ₂.IsHaarMeasure]
    (K' : Subgroup G) (hK'o : IsOpen (K' : Set G)) (hK'c : IsCompact (K' : Set G)) :
    μ₂.real (K' : Set G) ≠ 0 := by
  rw [measureReal_def]
  exact ENNReal.toReal_ne_zero.mpr ⟨(hK'o.measure_pos μ₂ ⟨1, K'.one_mem⟩).ne', hK'c.measure_lt_top.ne⟩

theorem k2_continuous_transposeInvN : Continuous (fun g : G => transposeInvN (Fin 2) g) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have : (Units.val ∘ fun g : G => transposeInvN (Fin 2) g) = fun g : G => Matrix.transpose (((g⁻¹ : G) : M2)) :=
      funext fun g => coe_transposeInvN (Fin 2) g
    rw [this]
    exact Units.continuous_coe_inv.matrix_transpose
  · have : (fun g : G => (((transposeInvN (Fin 2) g)⁻¹ : G) : M2)) = fun g : G => Matrix.transpose (((g : G) : M2)) :=
      funext fun g => coe_inv_transposeInvN (Fin 2) g
    rw [this]
    exact Units.continuous_val.matrix_transpose

theorem k2_det_transposeInvN (g : G) :
    Matrix.GeneralLinearGroup.det (transposeInvN (Fin 2) g) = (Matrix.GeneralLinearGroup.det g)⁻¹ := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_transposeInvN, Matrix.det_transpose,
    ← Matrix.GeneralLinearGroup.val_det_apply, map_inv]

theorem k2_modulus_det_transposeInvN (g : G)
    (hg : modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) = 1) :
    modulus ((Matrix.GeneralLinearGroup.det (transposeInvN (Fin 2) g) : Fˣ) : F) = 1 := by
  rw [k2_det_transposeInvN, modulus_coe_units, map_inv, ← modulus_coe_units, hg, inv_one]

theorem k2_gjIntegrand_mul_left (c : G → ℂ) (φ : M2 → ℂ) (χ : Fˣ →* ℂˣ) (s : ℂ) (a g : G)
    (ha : modulus ((Matrix.GeneralLinearGroup.det a : Fˣ) : F) = 1) :
    gjIntegrand p c (fun X : M2 => φ (((a⁻¹ : G) : M2) * X)) χ s (a * g) =
      ((χ (Matrix.GeneralLinearGroup.det a) : ℂˣ) : ℂ) * gjIntegrand p (fun h : G => c (a * h)) φ χ s g := by
  simp only [gjIntegrand, Units.val_mul, Units.inv_mul_cancel_left, map_mul, modulus_mul, ha, one_mul]
  ring

theorem k2_godementZeta2_comp_mul_left (μ₂ : Measure G) [μ₂.IsHaarMeasure]
    (c : G → ℂ) (φ : M2 → ℂ) (χ : Fˣ →* ℂˣ) (s : ℂ) (a : G)
    (ha : modulus ((Matrix.GeneralLinearGroup.det a : Fˣ) : F) = 1) :
    godementZeta2 p μ₂ (fun h : G => c (a * h)) φ χ s =
      (((χ (Matrix.GeneralLinearGroup.det a) : ℂˣ) : ℂ))⁻¹ *
        godementZeta2 p μ₂ c (fun X : M2 => φ (((a⁻¹ : G) : M2) * X)) χ s := by
  rw [godementZeta2_eq_integral_gjIntegrand, godementZeta2_eq_integral_gjIntegrand,
    ← integral_mul_left_eq_self (gjIntegrand p c (fun X : M2 => φ (((a⁻¹ : G) : M2) * X)) χ s) a]
  simp_rw [k2_gjIntegrand_mul_left p c φ χ s a _ ha]
  rw [integral_const_mul, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]

theorem k2_integrable_gjIntegrand_comp_mul_left (μ₂ : Measure G) [μ₂.IsHaarMeasure]
    (c : G → ℂ) (φ : M2 → ℂ) (χ : Fˣ →* ℂˣ) (s : ℂ) (a : G)
    (ha : modulus ((Matrix.GeneralLinearGroup.det a : Fˣ) : F) = 1)
    (hint : Integrable (gjIntegrand p c (fun X : M2 => φ (((a⁻¹ : G) : M2) * X)) χ s) μ₂) :
    Integrable (gjIntegrand p (fun h : G => c (a * h)) φ χ s) μ₂ := by
  refine ((hint.comp_mul_left a).const_mul
    ((((χ (Matrix.GeneralLinearGroup.det a) : ℂˣ) : ℂ))⁻¹)).congr (Filter.Eventually.of_forall fun g => ?_)
  beta_reduce
  rw [k2_gjIntegrand_mul_left p c φ χ s a g ha, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]

theorem k2_godementZeta2_avg_eq (μ₂ : Measure G) [μ₂.IsHaarMeasure]
    (S : Set G) (hSm : MeasurableSet S) (hStop : μ₂ S ≠ ⊤) (hS0 : μ₂ S ≠ 0)
    (α : G → G) (hα : Measurable α)
    (u : G → ℂ) (φ : M2 → ℂ) (χ : Fˣ →* ℂˣ) (s : ℂ)
    (hint : Integrable (gjIntegrand p u φ χ s) μ₂)
    (hk : ∀ k ∈ S, ∀ g : G,
      gjIntegrand p (fun h : G => u (α k * h)) φ χ s g = gjIntegrand p u φ χ s (α k * g)) :
    godementZeta2 p μ₂ (fun g : G => (μ₂.real S)⁻¹ * ∫ k in S, u (α k * g) ∂μ₂) φ χ s =
      godementZeta2 p μ₂ u φ χ s := by
  haveI : IsFiniteMeasure (μ₂.restrict S) := isFiniteMeasure_restrict.mpr hStop
  have hreal : μ₂.real S ≠ 0 := by
    rw [measureReal_def]; exact ENNReal.toReal_ne_zero.mpr ⟨hS0, hStop⟩

  have h1 : ∀ g : G, gjIntegrand p (fun g : G => (μ₂.real S)⁻¹ * ∫ k in S, u (α k * g) ∂μ₂) φ χ s g
      = (μ₂.real S)⁻¹ * ∫ k in S, gjIntegrand p u φ χ s (α k * g) ∂μ₂ := by
    intro g
    have h1a : ∫ k in S, gjIntegrand p u φ χ s (α k * g) ∂μ₂ =
        ∫ k in S, u (α k * g) * (φ ((g : G) : M2) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) ^ s) ∂μ₂ :=
      setIntegral_congr_fun hSm fun k hk' => by
        show _ = _
        rw [← hk k hk' g]; simp only [gjIntegrand]; ring
    rw [h1a, integral_mul_const]
    simp only [gjIntegrand]; ring

  have hI : Integrable (Function.uncurry fun (g : G) (k : G) => gjIntegrand p u φ χ s (α k * g))
      (μ₂.prod (μ₂.restrict S)) := by
    have hT : MeasurePreserving (fun z : G × G => (id z.1, α z.1 * z.2))
        ((μ₂.restrict S).prod μ₂) ((μ₂.restrict S).prod μ₂) :=
      (MeasurePreserving.id (μ₂.restrict S)).skew_product (g := fun k h => α k * h)
        (show Measurable fun z : G × G => α z.1 * z.2 from (hα.comp measurable_fst).mul measurable_snd)
        (Filter.Eventually.of_forall fun k => map_mul_left_eq_self μ₂ (α k))
    have h2 : Integrable (fun z : G × G => gjIntegrand p u φ χ s z.2) ((μ₂.restrict S).prod μ₂) :=
      hint.comp_snd (μ₂.restrict S)
    have h3 := (hT.integrable_comp h2.aestronglyMeasurable).mpr h2
    exact h3.swap
  rw [godementZeta2_eq_integral_gjIntegrand, godementZeta2_eq_integral_gjIntegrand]
  simp_rw [h1]
  rw [integral_const_mul, integral_integral_swap hI]
  simp_rw [integral_mul_left_eq_self]
  rw [setIntegral_const, Complex.real_smul, ← mul_assoc]
  push_cast
  rw [inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hreal), one_mul]

theorem k2_hk_of_leftInvariant
    (K' : Subgroup G)
    (hK'det : ∀ k ∈ K', modulus ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) = 1)
    (u : G → ℂ) (Φ : M2 → ℂ) (hΦK : ∀ k ∈ K', ∀ X : M2, Φ (((k : G) : M2) * X) = Φ X)
    (χ : Fˣ →* ℂˣ) (hχK : ∀ k ∈ K', χ (Matrix.GeneralLinearGroup.det k) = 1) (s : ℂ) :
    ∀ k ∈ (K' : Set G), ∀ g : G,
      gjIntegrand p (fun h : G => u (id k * h)) Φ χ s g = gjIntegrand p u Φ χ s (id k * g) := by
  intro k hk g
  have hΦ' : (fun X : M2 => Φ (((k⁻¹ : G) : M2) * X)) = Φ := funext fun X => hΦK k⁻¹ (K'.inv_mem hk) X
  have h := k2_gjIntegrand_mul_left p u Φ χ s k g (hK'det k hk)
  rw [hΦ', hχK k hk, Units.val_one, one_mul] at h
  exact h.symm

theorem k2_matFourier22_transposeInvN_inv_mul
    (K' : Subgroup G)
    (hK'det : ∀ k ∈ K', modulus ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) = 1)
    (Φ : M2 → ℂ) (hΦK : ∀ k ∈ K', ∀ X : M2, Φ (((k : G) : M2) * X) = Φ X) (k : G) (hk : k ∈ K') :
    (fun X : M2 => matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ
        ((((transposeInvN (Fin 2) k)⁻¹ : G) : M2) * X)) =
      matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ := by
  funext X
  rw [coe_inv_transposeInvN]
  have h205 := LanglandsTunnell.CubicInduction.matFourier22_comp_inv_mul_eq p
    (NumberField.StandardAddChar.psiLocal ℚ p) k Φ X
  rw [show (fun Y : M2 => Φ (((k⁻¹ : G) : M2) * Y)) = Φ from funext fun Y => hΦK k⁻¹ (K'.inv_mem hk) Y,
    hK'det k hk] at h205
  rw [h205]; push_cast; ring

theorem k2_matFourier22_translate
    (Φ : M2 → ℂ) (t : G) (ht : modulus ((Matrix.GeneralLinearGroup.det t : Fˣ) : F) = 1) :
    (fun X : M2 => matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ
        ((((transposeInvN (Fin 2) t)⁻¹ : G) : M2) * X)) =
      matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) (fun X : M2 => Φ (((t⁻¹ : G) : M2) * X)) := by
  funext X
  rw [coe_inv_transposeInvN, LanglandsTunnell.CubicInduction.matFourier22_comp_inv_mul_eq p
    (NumberField.StandardAddChar.psiLocal ℚ p) t Φ X, ht]
  push_cast; ring

theorem godementZeta2_eq_leftAvg
    (μ₂ : Measure G) [μ₂.IsHaarMeasure]
    (K' : Subgroup G) (hK'o : IsOpen (K' : Set G)) (hK'c : IsCompact (K' : Set G))
    (hK'det : ∀ k ∈ K', modulus ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) = 1)
    (w : G → ℂ) (hw : Continuous w)
    (Φ : M2 → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (hΦK : ∀ k ∈ K', ∀ X : M2, Φ (((k : G) : M2) * X) = Φ X)
    (χ : Fˣ →* ℂˣ) (hχ : IsLocallyConstant χ) (hχK : ∀ k ∈ K', χ (Matrix.GeneralLinearGroup.det k) = 1)
    (s : ℂ) (hint : Integrable (gjIntegrand p w Φ χ s) μ₂) :
    godementZeta2 p μ₂ w Φ χ s = godementZeta2 p μ₂ (leftAvg p μ₂ (K' : Set G) w) Φ χ s :=
  (k2_godementZeta2_avg_eq p μ₂ (K' : Set G) hK'o.measurableSet hK'c.measure_lt_top.ne
    (hK'o.measure_pos μ₂ ⟨1, K'.one_mem⟩).ne' id measurable_id w Φ χ s hint
    (k2_hk_of_leftInvariant p K' hK'det w Φ hΦK χ hχK s)).symm

theorem godementZeta2_leftAvg_translate_eq
    (μ₂ : Measure G) [μ₂.IsHaarMeasure]
    (K' : Subgroup G) (hK'o : IsOpen (K' : Set G)) (hK'c : IsCompact (K' : Set G))
    (hK'det : ∀ k ∈ K', modulus ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) = 1)
    (Fw : G → ℂ) (hFw : Continuous Fw)
    (Φ : M2 → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (hΦK : ∀ k ∈ K', ∀ X : M2, Φ (((k : G) : M2) * X) = Φ X)
    (χ : Fˣ →* ℂˣ) (hχ : IsLocallyConstant χ) (hχK : ∀ k ∈ K', χ (Matrix.GeneralLinearGroup.det k) = 1)
    (t : G) (ht : modulus ((Matrix.GeneralLinearGroup.det t : Fˣ) : F) = 1)
    (s : ℂ)
    (hint : Integrable (gjIntegrand p Fw (fun X : M2 => Φ (((t⁻¹ : G) : M2) * X)) χ s) μ₂) :
    godementZeta2 p μ₂ (fun g : G => (μ₂.real (K' : Set G))⁻¹ * ∫ k in (K' : Set G), Fw (t * k * g) ∂μ₂) Φ χ s =
      (((χ (Matrix.GeneralLinearGroup.det t) : ℂˣ) : ℂ))⁻¹ *
        godementZeta2 p μ₂ Fw (fun X : M2 => Φ (((t⁻¹ : G) : M2) * X)) χ s := by
  have hu : Integrable (gjIntegrand p (fun h : G => Fw (t * h)) Φ χ s) μ₂ :=
    k2_integrable_gjIntegrand_comp_mul_left p μ₂ Fw Φ χ s t ht hint
  have hcoef : (fun g : G => (μ₂.real (K' : Set G))⁻¹ * ∫ k in (K' : Set G), Fw (t * k * g) ∂μ₂) =
      fun g : G => (μ₂.real (K' : Set G))⁻¹ * ∫ k in (K' : Set G), (fun h : G => Fw (t * h)) (id k * g) ∂μ₂ := by
    funext g; simp only [id, mul_assoc]
  rw [hcoef, k2_godementZeta2_avg_eq p μ₂ (K' : Set G) hK'o.measurableSet hK'c.measure_lt_top.ne
    (hK'o.measure_pos μ₂ ⟨1, K'.one_mem⟩).ne' id measurable_id (fun h : G => Fw (t * h)) Φ χ s hu
    (k2_hk_of_leftInvariant p K' hK'det (fun h : G => Fw (t * h)) Φ hΦK χ hχK s),
    k2_godementZeta2_comp_mul_left p μ₂ Fw Φ χ s t ht]

theorem godementZeta2_transposeInv_eq_leftAvg
    (μ₂ : Measure G) [μ₂.IsHaarMeasure]
    (K' : Subgroup G) (hK'o : IsOpen (K' : Set G)) (hK'c : IsCompact (K' : Set G))
    (hK'det : ∀ k ∈ K', modulus ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) = 1)
    (w : G → ℂ) (hw : Continuous w)
    (Φ : M2 → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (hΦK : ∀ k ∈ K', ∀ X : M2, Φ (((k : G) : M2) * X) = Φ X)
    (χ : Fˣ →* ℂˣ) (hχ : IsLocallyConstant χ) (hχK : ∀ k ∈ K', χ (Matrix.GeneralLinearGroup.det k) = 1)
    (s : ℂ)
    (hint : Integrable (gjIntegrand p (fun g : G => w (transposeInvN (Fin 2) g))
      (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) χ⁻¹ s) μ₂) :
    godementZeta2 p μ₂ (fun g : G => w (transposeInvN (Fin 2) g))
        (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) χ⁻¹ s =
      godementZeta2 p μ₂ (fun g : G => leftAvg p μ₂ (K' : Set G) w (transposeInvN (Fin 2) g))
        (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) χ⁻¹ s := by
  set Φh := matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ with hΦh
  set u : G → ℂ := fun g : G => w (transposeInvN (Fin 2) g) with hu
  have hcoef : (fun g : G => leftAvg p μ₂ (K' : Set G) w (transposeInvN (Fin 2) g)) =
      fun g : G => (μ₂.real (K' : Set G))⁻¹ * ∫ k in (K' : Set G), u (transposeInvN (Fin 2) k * g) ∂μ₂ := by
    funext g; simp only [leftAvg, hu, transposeInvN_mul, transposeInvN_transposeInvN]
  have hk : ∀ k ∈ (K' : Set G), ∀ g : G,
      gjIntegrand p (fun h : G => u (transposeInvN (Fin 2) k * h)) Φh χ⁻¹ s g =
        gjIntegrand p u Φh χ⁻¹ s (transposeInvN (Fin 2) k * g) := by
    intro k hk g
    have hmod := k2_modulus_det_transposeInvN p k (hK'det k hk)
    have h := k2_gjIntegrand_mul_left p u Φh χ⁻¹ s (transposeInvN (Fin 2) k) g hmod
    rw [hΦh, k2_matFourier22_transposeInvN_inv_mul p K' hK'det Φ hΦK k hk, k2_det_transposeInvN,
      MonoidHom.inv_apply, map_inv, hχK k hk, inv_inv, Units.val_one, one_mul] at h
    exact h.symm
  rw [hcoef]
  exact (k2_godementZeta2_avg_eq p μ₂ (K' : Set G) hK'o.measurableSet hK'c.measure_lt_top.ne
    (hK'o.measure_pos μ₂ ⟨1, K'.one_mem⟩).ne' (fun g : G => transposeInvN (Fin 2) g)
    (k2_continuous_transposeInvN p).measurable u Φh χ⁻¹ s hint hk).symm

theorem godementZeta2_leftAvg_translate_transposeInv_eq
    (μ₂ : Measure G) [μ₂.IsHaarMeasure]
    (K' : Subgroup G) (hK'o : IsOpen (K' : Set G)) (hK'c : IsCompact (K' : Set G))
    (hK'det : ∀ k ∈ K', modulus ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) = 1)
    (Fw : G → ℂ) (hFw : Continuous Fw)
    (Φ : M2 → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (hΦK : ∀ k ∈ K', ∀ X : M2, Φ (((k : G) : M2) * X) = Φ X)
    (χ : Fˣ →* ℂˣ) (hχ : IsLocallyConstant χ) (hχK : ∀ k ∈ K', χ (Matrix.GeneralLinearGroup.det k) = 1)
    (t : G) (ht : modulus ((Matrix.GeneralLinearGroup.det t : Fˣ) : F) = 1)
    (s : ℂ)
    (hint : Integrable (gjIntegrand p (fun g : G => Fw (transposeInvN (Fin 2) g))
      (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) (fun X : M2 => Φ (((t⁻¹ : G) : M2) * X))) χ⁻¹ s) μ₂) :
    godementZeta2 p μ₂ (fun g : G => (μ₂.real (K' : Set G))⁻¹ * ∫ k in (K' : Set G), Fw (t * k * transposeInvN (Fin 2) g) ∂μ₂)
        (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) χ⁻¹ s =
      (((χ (Matrix.GeneralLinearGroup.det t) : ℂˣ) : ℂ))⁻¹ *
        godementZeta2 p μ₂ (fun g : G => Fw (transposeInvN (Fin 2) g))
          (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) (fun X : M2 => Φ (((t⁻¹ : G) : M2) * X))) χ⁻¹ s := by
  set ψ := NumberField.StandardAddChar.psiLocal ℚ p with hψ
  set uτ : G → ℂ := fun g : G => Fw (transposeInvN (Fin 2) g) with huτ
  have htm := k2_modulus_det_transposeInvN p t ht

  have hΦt := k2_matFourier22_translate p Φ t ht

  have hint' : Integrable (gjIntegrand p (fun h : G => uτ (transposeInvN (Fin 2) t * h))
      (matFourier22 p ψ Φ) χ⁻¹ s) μ₂ := by
    apply k2_integrable_gjIntegrand_comp_mul_left p μ₂ uτ (matFourier22 p ψ Φ) χ⁻¹ s (transposeInvN (Fin 2) t) htm
    rw [hψ, hΦt]; exact hint
  have htr : (fun g : G => Fw (t * transposeInvN (Fin 2) g)) = fun h : G => uτ (transposeInvN (Fin 2) t * h) := by
    funext g; simp only [huτ, transposeInvN_mul, transposeInvN_transposeInvN]

  have hcoef : (fun g : G => (μ₂.real (K' : Set G))⁻¹ * ∫ k in (K' : Set G), Fw (t * k * transposeInvN (Fin 2) g) ∂μ₂) =
      fun g : G => leftAvg p μ₂ (K' : Set G) (fun h : G => Fw (t * h)) (transposeInvN (Fin 2) g) := by
    funext g; simp only [leftAvg, mul_assoc]
  have hB := godementZeta2_transposeInv_eq_leftAvg p μ₂ K' hK'o hK'c hK'det (fun h : G => Fw (t * h))
    (hFw.comp (continuous_const_mul t)) Φ hΦ hΦc hΦK χ hχ hχK s (by rw [htr]; exact hint')
  rw [hcoef, ← hB, htr, k2_godementZeta2_comp_mul_left p μ₂ uτ (matFourier22 p ψ Φ) χ⁻¹ s (transposeInvN (Fin 2) t) htm,
    hψ, hΦt, k2_det_transposeInvN, MonoidHom.inv_apply, map_inv, inv_inv]

theorem leftAvg_translate_const
    (μ₂ : Measure G) [μ₂.IsHaarMeasure]
    (K' : Subgroup G) (hK'o : IsOpen (K' : Set G)) (hK'c : IsCompact (K' : Set G))
    (u : G → ℂ) (t : G) (hu : ∀ k ∈ K', u (t * k) = u t) :
    (μ₂.real (K' : Set G))⁻¹ * ∫ k in (K' : Set G), u (t * k) ∂μ₂ = u t := by
  have hreal := k2_real_ne_zero p μ₂ K' hK'o hK'c
  rw [setIntegral_congr_fun hK'o.measurableSet (fun k hk => hu k hk), setIntegral_const, Complex.real_smul,
    ← mul_assoc]
  push_cast
  rw [inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hreal), one_mul]

theorem setIntegral_translate_mul_right
    (μ₂ : Measure G) [μ₂.IsHaarMeasure]
    (K' : Subgroup G) (hK'o : IsOpen (K' : Set G)) (hK'c : IsCompact (K' : Set G))
    (u : G → ℂ) (t k₀ : G) (hk₀ : k₀ ∈ K') :
    ∫ k in (K' : Set G), u (t * k * k₀) ∂μ₂ = ∫ k in (K' : Set G), u (t * k) ∂μ₂ := by
  haveI := isMulRightInvariant_of_isHaarMeasure p μ₂
  rw [← integral_indicator hK'o.measurableSet, ← integral_indicator hK'o.measurableSet]
  have hind : (K' : Set G).indicator (fun k : G => u (t * k * k₀)) =
      fun k : G => (K' : Set G).indicator (fun k : G => u (t * k)) (k * k₀) := by
    funext k
    have hiff : k * k₀ ∈ (K' : Set G) ↔ k ∈ (K' : Set G) :=
      ⟨fun h => by simpa using K'.mul_mem h (K'.inv_mem hk₀), fun h => K'.mul_mem h hk₀⟩
    by_cases hk : k ∈ (K' : Set G)
    · rw [Set.indicator_of_mem hk, Set.indicator_of_mem (hiff.mpr hk), mul_assoc]
    · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem (fun h => hk (hiff.mp h))]
  rw [hind, integral_mul_right_eq_self]

end K2

section Generic
variable {H : Type*} [Group H]

theorem translate_mem_span (f : H → ℂ) (h : H) {W : H → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : H => fun g : H => f (g * h'))) :
    (fun g : H => W (g * h)) ∈ Submodule.span ℂ (Set.range fun h' : H => fun g : H => f (g * h')) := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h', rfl⟩ := hWm
      exact Submodule.subset_span ⟨h * h', funext fun g => by simp only [mul_assoc]⟩
  | zero => exact Submodule.zero_mem _
  | add W₁ W₂ _ _ h₁ h₂ =>
      have : (fun g : H => (W₁ + W₂) (g * h)) = (fun g : H => W₁ (g * h)) + fun g : H => W₂ (g * h) := rfl
      rw [this]; exact Submodule.add_mem _ h₁ h₂
  | smul a W _ h₁ =>
      have : (fun g : H => (a • W) (g * h)) = a • fun g : H => W (g * h) := rfl
      rw [this]; exact Submodule.smul_mem _ a h₁

variable [TopologicalSpace H] [ContinuousMul H]

theorem exists_open_stabilizer_of_mem_span (f : H → ℂ) (K : Subgroup H) (hK : IsOpen (K : Set H))
    (hf : ∀ k ∈ K, ∀ g : H, f (g * k) = f g) {W : H → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : H => fun g : H => f (g * h'))) :
    ∃ U : Subgroup H, IsOpen (U : Set H) ∧ ∀ k ∈ U, ∀ g : H, W (g * k) = W g := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h, rfl⟩ := hWm
      refine ⟨K.comap (MulAut.conj h⁻¹).toMonoidHom, ?_, ?_⟩
      · have hc : Continuous fun k : H => h⁻¹ * k * h⁻¹⁻¹ :=
          (continuous_const.mul continuous_id).mul continuous_const
        have hset : ((K.comap (MulAut.conj h⁻¹).toMonoidHom : Subgroup H) : Set H) =
            (fun k : H => h⁻¹ * k * h⁻¹⁻¹) ⁻¹' (K : Set H) := by
          ext k
          simp only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            SetLike.mem_coe]
        rw [hset]
        exact hK.preimage hc
      · intro k hk g
        have hk' : h⁻¹ * k * h⁻¹⁻¹ ∈ K := by
          simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hk
        show f (g * k * h) = f (g * h)
        have := hf _ hk' (g * h)
        rw [inv_inv] at this
        calc f (g * k * h) = f (g * h * (h⁻¹ * k * h)) := by group
          _ = f (g * h) := this
  | zero => exact ⟨⊤, isOpen_univ, fun _ _ _ => rfl⟩
  | add W₁ W₂ _ _ h₁ h₂ =>
      obtain ⟨U₁, hU₁, h₁⟩ := h₁
      obtain ⟨U₂, hU₂, h₂⟩ := h₂
      exact ⟨U₁ ⊓ U₂, hU₁.inter hU₂, fun k hk g => by
        simp only [Pi.add_apply, h₁ k hk.1 g, h₂ k hk.2 g]⟩
  | smul c W _ h₁ =>
      obtain ⟨U₁, hU₁, h₁⟩ := h₁
      exact ⟨U₁, hU₁, fun k hk g => by simp only [Pi.smul_apply, h₁ k hk g]⟩

theorem isLocallyConstant_of_open_stabilizer (f : H → ℂ)
    (hF : ∃ U : Subgroup H, IsOpen (U : Set H) ∧ ∀ k ∈ U, ∀ g : H, f (g * k) = f g) :
    IsLocallyConstant f := by
  obtain ⟨U, hU, hinv⟩ := hF
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(fun k => g * k) '' (U : Set H), (Homeomorph.mulLeft g).isOpenMap _ hU, ⟨1, U.one_mem, mul_one g⟩, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  exact hinv k hk g

theorem isLocallyConstant_of_mem_span (f : H → ℂ) (K : Subgroup H) (hK : IsOpen (K : Set H))
    (hf : ∀ k ∈ K, ∀ g : H, f (g * k) = f g) {W : H → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : H => fun g : H => f (g * h'))) :
    IsLocallyConstant W :=
  isLocallyConstant_of_open_stabilizer W (exists_open_stabilizer_of_mem_span f K hK hf hW)

end Generic

section K1

theorem exists_nhds_one_forall_apply_eq (act : G × M2 → M2) (hact : Continuous act) (h1 : ∀ X, act (1, X) = X)
    (Φ : M2 → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ U : Set G, IsOpen U ∧ (1 : G) ∈ U ∧ ∀ k ∈ U, ∀ X ∈ tsupport Φ, Φ (act (k, X)) = Φ X := by
  have hW : ∀ X : M2, ∃ W : Set M2, IsOpen W ∧ X ∈ W ∧ ∀ Y ∈ W, Φ Y = Φ X :=
    (IsLocallyConstant.iff_exists_open Φ).mp hΦ
  choose W hWo hWx hWc using hW
  have hbox : ∀ X : M2, ∃ U : Set G, ∃ V : Set M2, IsOpen U ∧ IsOpen V ∧ (1 : G) ∈ U ∧ X ∈ V ∧ V ⊆ W X ∧
      ∀ k ∈ U, ∀ Y ∈ V, act (k, Y) ∈ W X := by
    intro X
    have ho : IsOpen (act ⁻¹' W X) := (hWo X).preimage hact
    have hm : ((1 : G), X) ∈ act ⁻¹' W X := by
      show act (1, X) ∈ W X
      rw [h1]; exact hWx X
    obtain ⟨U, V, hU, hV, h1U, hXV, hUV⟩ := isOpen_prod_iff.mp ho 1 X hm
    exact ⟨U, V ∩ W X, hU, hV.inter (hWo X), h1U, ⟨hXV, hWx X⟩, Set.inter_subset_right,
      fun k hk Y hY => hUV ⟨hk, hY.1⟩⟩
  choose U V hUo hVo h1U hXV hVW hUV using hbox
  obtain ⟨T, hT⟩ := IsCompact.elim_finite_subcover hΦc V hVo (fun X _ => Set.mem_iUnion.mpr ⟨X, hXV X⟩)
  refine ⟨⋂ X ∈ T, U X, isOpen_biInter_finset fun X _ => hUo X, Set.mem_iInter₂.mpr fun X _ => h1U X, ?_⟩
  intro k hk X hX
  obtain ⟨X₀, hX₀T, hXV₀⟩ := Set.mem_iUnion₂.mp (hT hX)
  have hk₀ : k ∈ U X₀ := Set.mem_iInter₂.mp hk X₀ hX₀T
  rw [hWc X₀ _ (hUV X₀ k hk₀ X hXV₀), hWc X₀ X (hVW X₀ hXV₀)]

theorem congr_le_localLevelOne_top (n : ℕ) :
    KCSA.congr ℚ p n ≤ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  intro k hk
  have key : ∀ m : M2, KCSA.IsCong n m → AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ m := by
    intro m hm
    refine ⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).mpr (hm.integral i j), ?_, ?_⟩
    · rw [NumberField.AdelicLevel.idealBound_top]; exact hm.h10.trans (KCSA.lvl_le_one n)
    · rw [NumberField.AdelicLevel.idealBound_top]; exact hm.h11.trans (KCSA.lvl_le_one n)
  rw [AdelicDock.mem_localLevelOne_iff]
  exact ⟨key _ hk, key _ ((KCSA.congr ℚ p n).inv_mem hk)⟩

theorem modulus_det_eq_one_of_mem_congr {n : ℕ} {k : G} (hk : k ∈ KCSA.congr ℚ p n) :
    modulus ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) = 1 := by
  have hv : Valued.v ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) = 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]; exact (show KCSA.IsCong n (k : M2) from hk).v_det'
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p]
  apply NNReal.eq; rw [coe_nnnorm]; exact KCSA.norm_eq_one_of_v p hv

theorem exists_good_congr
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (w₂base : G → ℂ)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : G, w₂base (g * k) = w₂base g)
    (w : G → ℂ) (hw : w ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w₂base (g * h)))
    (Φ : M2 → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : Fˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    ∃ n : ℕ, (∀ k ∈ KCSA.congr ℚ p n, ∀ g : G, w (g * k) = w g) ∧
      (∀ k ∈ KCSA.congr ℚ p n, ∀ X : M2, Φ (((k : G) : M2) * X) = Φ X) ∧
      (∀ k ∈ KCSA.congr ℚ p n, ∀ X : M2, Φ (X * ((k : G) : M2)) = Φ X) ∧
      (∀ k ∈ KCSA.congr ℚ p n, χ (Matrix.GeneralLinearGroup.det k) = 1) := by

  obtain ⟨Uw, hUwo, hUw⟩ := exists_open_stabilizer_of_mem_span w₂base _
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN).2 hw₂K hw
  obtain ⟨n₁, hn₁⟩ := KCSA.exists_congr_subset (K := ℚ) (v := p) hUwo (Subgroup.one_mem Uw)

  obtain ⟨UL, hULo, hUL1, hUL⟩ := exists_nhds_one_forall_apply_eq p (fun q : G × M2 => ((q.1 : G) : M2) * q.2)
    ((Units.continuous_val.comp continuous_fst).matrix_mul continuous_snd) (fun X => by simp) Φ hΦ hΦc
  obtain ⟨n₂, hn₂⟩ := KCSA.exists_congr_subset (K := ℚ) (v := p) hULo hUL1

  obtain ⟨UR, hURo, hUR1, hUR⟩ := exists_nhds_one_forall_apply_eq p (fun q : G × M2 => q.2 * ((q.1 : G) : M2))
    (continuous_snd.matrix_mul (Units.continuous_val.comp continuous_fst)) (fun X => by simp) Φ hΦ hΦc
  obtain ⟨n₃, hn₃⟩ := KCSA.exists_congr_subset (K := ℚ) (v := p) hURo hUR1

  obtain ⟨c, hc⟩ := LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous ℚ p χ hχ.continuous
  refine ⟨n₁ + n₂ + n₃ + c, ?_, ?_, ?_, ?_⟩
  · intro k hk g
    exact hUw k (hn₁ (KCSA.congr_antitone' (K := ℚ) (v := p) (by omega) hk)) g
  · intro k hk X
    have hkL : ∀ k' ∈ KCSA.congr ℚ p (n₁ + n₂ + n₃ + c), ∀ Y ∈ tsupport Φ, Φ (((k' : G) : M2) * Y) = Φ Y :=
      fun k' hk' Y hY => hUL k' (hn₂ (KCSA.congr_antitone' (K := ℚ) (v := p) (by omega) hk')) Y hY
    by_cases hX : X ∈ tsupport Φ
    · exact hkL k hk X hX
    · have h0 : Φ X = 0 := image_eq_zero_of_notMem_tsupport hX
      rw [h0]
      by_contra hne
      have hmem : ((k : G) : M2) * X ∈ tsupport Φ := subset_tsupport _ hne
      have := hkL k⁻¹ ((KCSA.congr ℚ p _).inv_mem hk) _ hmem
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, h0] at this
      exact hne this.symm
  · intro k hk X
    have hkR : ∀ k' ∈ KCSA.congr ℚ p (n₁ + n₂ + n₃ + c), ∀ Y ∈ tsupport Φ, Φ (Y * ((k' : G) : M2)) = Φ Y :=
      fun k' hk' Y hY => hUR k' (hn₃ (KCSA.congr_antitone' (K := ℚ) (v := p) (by omega) hk')) Y hY
    by_cases hX : X ∈ tsupport Φ
    · exact hkR k hk X hX
    · have h0 : Φ X = 0 := image_eq_zero_of_notMem_tsupport hX
      rw [h0]
      by_contra hne
      have hmem : X * ((k : G) : M2) ∈ tsupport Φ := subset_tsupport _ hne
      have := hkR k⁻¹ ((KCSA.congr ℚ p _).inv_mem hk) _ hmem
      rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one, h0] at this
      exact hne this.symm
  · intro k hk
    apply hc.1
    rw [LanglandsTunnell.TateLocal.mem_higherUnitsAt_iff]
    have hkc : KCSA.IsCong (n₁ + n₂ + n₃ + c) (k : M2) := hk
    refine ⟨?_, Or.inr ?_⟩
    · rw [Matrix.GeneralLinearGroup.val_det_apply]; exact hkc.v_det'
    · rw [Matrix.GeneralLinearGroup.val_det_apply]
      refine le_trans hkc.v_det_sub_one' ?_
      rw [KCSA.lvl, WithZero.exp_le_exp]; push_cast; omega

end K1

section K3

def rho (h : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun v := fun g => v (g * h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rho_apply (h : G) (v : G → ℂ) (g : G) : rho p h v g = v (g * h) := rfl

def lowerUnit (e : F) : G :=
  ⟨!![1, 0; e, 1], !![1, 0; -e, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def flipUnit (e : F) : G :=
  ⟨!![0, 1; 1, e], !![-e, 1; 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem mem_K0_of_entries (k : G)
    (h1 : ∀ i j, Valued.v ((k : M2) i j) ≤ 1) (h2 : ∀ i j, Valued.v (((k⁻¹ : G) : M2) i j) ≤ 1) :
    k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  have key : ∀ m : M2, (∀ i j, Valued.v (m i j) ≤ 1) → AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ m := by
    intro m hm
    refine ⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).mpr (hm i j), ?_, ?_⟩
    · rw [NumberField.AdelicLevel.idealBound_top]; exact hm 1 0
    · rw [NumberField.AdelicLevel.idealBound_top]
      refine (Valuation.map_sub _ _ _).trans (max_le (hm 1 1) ?_)
      rw [Valuation.map_one]
  rw [AdelicDock.mem_localLevelOne_iff]
  exact ⟨key _ h1, key _ h2⟩

theorem lowerUnit_mem_K0 {e : F} (he : Valued.v e ≤ 1) : lowerUnit p e ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  apply mem_K0_of_entries
  · intro i j
    change Valued.v ((!![1, 0; e, 1] : M2) i j) ≤ 1
    fin_cases i <;> fin_cases j <;> simp [he]
  · intro i j
    change Valued.v ((!![1, 0; -e, 1] : M2) i j) ≤ 1
    fin_cases i <;> fin_cases j <;> simp [Valuation.map_neg, he]

theorem flipUnit_mem_K0 {e : F} (he : Valued.v e ≤ 1) : flipUnit p e ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  apply mem_K0_of_entries
  · intro i j
    change Valued.v ((!![0, 1; 1, e] : M2) i j) ≤ 1
    fin_cases i <;> fin_cases j <;> simp [he]
  · intro i j
    change Valued.v ((!![-e, 1; 1, 0] : M2) i j) ≤ 1
    fin_cases i <;> fin_cases j <;> simp [Valuation.map_neg, he]

theorem diagonal2_coe_mk0 (α δ : F) (hα : α ≠ 0) (hδ : δ ≠ 0) :
    ((diagonal2 p ![Units.mk0 α hα, Units.mk0 δ hδ] : G) : M2) = !![α, 0; 0, δ] := by
  change Matrix.diagonal (fun i => ((![Units.mk0 α hα, Units.mk0 δ hδ] : Fin 2 → Fˣ) i : F)) = _
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem exists_iwasawa (g : G) :
    ∃ (x : F) (a : Fin 2 → Fˣ) (k : G), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ ∧
      g = upperUnipotent2 p x * diagonal2 p a * k := by
  obtain ⟨a, b, c, d, hg⟩ : ∃ a b c d : F, (g : M2) = !![a, b; c, d] :=
    ⟨(g : M2) 0 0, (g : M2) 0 1, (g : M2) 1 0, (g : M2) 1 1, by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
  have hdet : a * d - b * c ≠ 0 := by
    have := Matrix.GeneralLinearGroup.det_ne_zero g
    rwa [hg, Matrix.det_fin_two_of] at this
  by_cases hcd : Valued.v c ≤ Valued.v d
  ·
    have hd : d ≠ 0 := by
      intro hd
      have hc : c = 0 := by
        rw [hd, Valuation.map_zero, le_zero_iff] at hcd; exact (Valuation.zero_iff _).mp hcd
      apply hdet; rw [hc, hd]; ring
    have hα' : (a * d - b * c) / d ≠ 0 := div_ne_zero hdet hd
    refine ⟨b / d, ![Units.mk0 _ hα', Units.mk0 d hd], lowerUnit p (c / d), lowerUnit_mem_K0 p ?_, ?_⟩
    · rw [map_div₀]; exact div_le_one_of_le₀ hcd zero_le'
    · apply Units.ext
      rw [Units.val_mul, Units.val_mul, diagonal2_coe_mk0 p, hg]
      change (!![a, b; c, d] : M2) = (!![1, b / d; 0, 1] : M2) * !![(a * d - b * c) / d, 0; 0, d] * !![1, 0; c / d, 1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
  ·
    rw [not_le] at hcd
    have hc : c ≠ 0 := by
      intro hc; rw [hc, Valuation.map_zero] at hcd; exact absurd hcd (not_lt.mpr zero_le')
    have hα' : -(a * d - b * c) / c ≠ 0 := div_ne_zero (neg_ne_zero.mpr hdet) hc
    refine ⟨a / c, ![Units.mk0 _ hα', Units.mk0 c hc], flipUnit p (d / c), flipUnit_mem_K0 p ?_, ?_⟩
    · rw [map_div₀]; exact (div_le_one₀ (lt_of_le_of_lt zero_le' hcd)).mpr hcd.le
    · apply Units.ext
      rw [Units.val_mul, Units.val_mul, diagonal2_coe_mk0 p, hg]
      change (!![a, b; c, d] : M2) = (!![1, a / c; 0, 1] : M2) * !![-(a * d - b * c) / c, 0; 0, c] * !![0, 1; 1, d / c]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem section_eq_zero_of_forall_reps
    (lam : Fin 2 → (Fˣ →* ℂˣ)) (K' : Subgroup G) (T : Finset G)
    (hT : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∃ t ∈ T, t⁻¹ * k ∈ K')
    (φ : G → ℂ) (hφ : φ ∈ principalSeries2 p lam) (hφK : ∀ k ∈ K', ∀ g : G, φ (g * k) = φ g)
    (h0 : ∀ t ∈ T, φ t = 0) : φ = 0 := by
  obtain ⟨-, hn, ht⟩ := mem_principalSeries2_iff.mp hφ
  funext g
  show φ g = 0
  obtain ⟨x, a, k, hk, rfl⟩ := exists_iwasawa p g
  obtain ⟨t, htT, htk⟩ := hT k hk
  have hk' : φ (t * (t⁻¹ * k)) = 0 := by rw [hφK _ htk, h0 t htT]
  have hk'' : φ k = 0 := by rwa [mul_inv_cancel_left] at hk'
  rw [mul_assoc, hn, ht, hk'', mul_zero]

theorem exists_finset_inv_mul_mem' (K : Set G) (hK : IsCompact K) (U : Subgroup G) (hU : IsOpen (U : Set G)) :
    ∃ R : Finset G, (↑R : Set G) ⊆ K ∧ ∀ k ∈ K, ∃ r ∈ R, r⁻¹ * k ∈ U := by
  let O : K → Set G := fun r => (fun g : G => ((r : G))⁻¹ * g) ⁻¹' (U : Set G)
  have hO : ∀ r, IsOpen (O r) := fun r => hU.preimage (continuous_const.mul continuous_id)
  have hcov : K ⊆ ⋃ r, O r := by
    intro k hk
    refine Set.mem_iUnion.mpr ⟨⟨k, hk⟩, ?_⟩
    show k⁻¹ * k ∈ (U : Set G)
    rw [inv_mul_cancel]; exact U.one_mem
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover O hO hcov
  refine ⟨t.image Subtype.val, ?_, fun k hk => ?_⟩
  · intro r hr
    obtain ⟨r', -, rfl⟩ := Finset.mem_image.mp hr
    exact r'.2
  · obtain ⟨r, hrt, hkr⟩ := Set.mem_iUnion₂.mp (ht hk)
    exact ⟨r, Finset.mem_image.mpr ⟨r, hrt, rfl⟩, hkr⟩

def ell (μ₂ : Measure G) (K' : Set G) (u : G → ℂ) : ℂ := (μ₂.real K')⁻¹ * ∫ k in K', u k ∂μ₂

theorem leftAvg_eq_ell (μ₂ : Measure G) (K' : Set G) (u : G → ℂ) (g : G) :
    leftAvg p μ₂ K' u g = ell p μ₂ K' (rho p g u) := rfl

theorem ell_add (μ₂ : Measure G) (K' : Set G) (u v : G → ℂ) (hu : IntegrableOn u K' μ₂) (hv : IntegrableOn v K' μ₂) :
    ell p μ₂ K' (u + v) = ell p μ₂ K' u + ell p μ₂ K' v := by
  unfold ell
  rw [show (fun k => (u + v) k) = fun k => u k + v k from rfl, integral_add hu hv, mul_add]

theorem ell_smul (μ₂ : Measure G) (K' : Set G) (c : ℂ) (u : G → ℂ) :
    ell p μ₂ K' (c • u) = c * ell p μ₂ K' u := by
  unfold ell
  rw [show (fun k => (c • u) k) = fun k => c * u k from rfl, integral_const_mul]
  ring

theorem ell_finset_sum {ι : Type*} (μ₂ : Measure G) (K' : Set G) (s : Finset ι) (u : ι → G → ℂ)
    (hu : ∀ i ∈ s, IntegrableOn (u i) K' μ₂) :
    ell p μ₂ K' (∑ i ∈ s, u i) = ∑ i ∈ s, ell p μ₂ K' (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ell]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        ell_add p μ₂ K' _ _ (hu i (Finset.mem_insert_self i s))
          (integrable_finset_sum' s (fun j hj => hu j (Finset.mem_insert_of_mem hj))),
        ih (fun j hj => hu j (Finset.mem_insert_of_mem hj))]

section Kernel

variable (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
  (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
  (lam : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
  (Φe : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))
  (hΦeq : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
    Φe (fun g => w (g * h)) = fun g => Φe w (g * h))
  (hΦinj : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), Φe w = 0 → w = 0)
  (hΦPS : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), Φe w ∈ principalSeries2 p lam)

def W0 (K' : Subgroup G) : Submodule ℂ (G → ℂ) where
  carrier := {u | u ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w₂base (g * h)) ∧
    ∀ k ∈ K', ∀ g : G, u (g * k) = u g}
  zero_mem' := ⟨Submodule.zero_mem _, fun _ _ _ => rfl⟩
  add_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    exact ⟨Submodule.add_mem _ hu hv, fun k hk g => by simp only [Pi.add_apply, hu' k hk g, hv' k hk g]⟩
  smul_mem' := by
    rintro c u ⟨hu, hu'⟩
    exact ⟨Submodule.smul_mem _ c hu, fun k hk g => by simp only [Pi.smul_apply, hu' k hk g]⟩

include hΦeq in
theorem phie_right_inv (K' : Subgroup G) (u : G → ℂ) (hu : u ∈ W0 p w₂base K') (k : G) (hk : k ∈ K') (g : G) :
    Φe u (g * k) = Φe u g := by
  have h1 := hΦeq u hu.1 k
  have h2 : (fun g => u (g * k)) = u := funext fun g => hu.2 k hk g
  rw [h2] at h1
  exact (congrFun h1 g).symm

def Amap (K' : Subgroup G) (T : Finset G) : W0 p w₂base K' →ₗ[ℂ] (T → ℂ) where
  toFun u := fun t => Φe u.1 t.1
  map_add' u v := by funext t; simp
  map_smul' c u := by funext t; simp

include hΦeq hΦinj hΦPS in
theorem ker_Amap_eq_bot (K' : Subgroup G) (T : Finset G)
    (hT : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∃ t ∈ T, t⁻¹ * k ∈ K') :
    LinearMap.ker (Amap p w₂base Φe K' T) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro u hu
  have h0 : Φe u.1 = 0 := by
    refine section_eq_zero_of_forall_reps p lam K' T hT (Φe u.1) (hΦPS u.1 u.2.1)
      (fun k hk g => phie_right_inv p w₂base Φe hΦeq K' u.1 u.2 k hk g) (fun t ht => ?_)
    exact congrFun hu ⟨t, ht⟩
  exact Subtype.ext (hΦinj u.1 u.2.1 h0)

theorem exists_reproducing (K' : Subgroup G) (T : Finset G)
    (hT : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∃ t ∈ T, t⁻¹ * k ∈ K')
    (hΦeq' : ∀ w ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w₂base (g * h)), ∀ h : G,
      Φe (fun g => w (g * h)) = fun g => Φe w (g * h))
    (hΦinj' : ∀ w ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w₂base (g * h)), Φe w = 0 → w = 0)
    (hΦPS' : ∀ w ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w₂base (g * h)), Φe w ∈ principalSeries2 p lam) :
    ∃ ub : T → W0 p w₂base K', ∀ u : W0 p w₂base K', (u : G → ℂ) = ∑ t : T, (Φe u.1 t.1) • (ub t : G → ℂ) := by
  classical
  obtain ⟨B, hB⟩ := LinearMap.exists_leftInverse_of_injective (Amap p w₂base Φe K' T)
    (ker_Amap_eq_bot p w₂base lam Φe hΦeq' hΦinj' hΦPS' K' T hT)
  refine ⟨fun t => B (fun j => if t = j then 1 else 0), fun u => ?_⟩
  have hu : B (Amap p w₂base Φe K' T u) = u := by
    have := congrArg (fun f => f u) hB
    simpa using this
  conv_lhs => rw [← hu, LinearMap.pi_apply_eq_sum_univ B]
  rw [Submodule.coe_sum]
  rfl

end Kernel

section Kernel2

variable (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
  (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
  (lam : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
  (Φe : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))
  (hΦeq : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
    Φe (fun g => w (g * h)) = fun g => Φe w (g * h))
  (hΦinj : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), Φe w = 0 → w = 0)
  (hΦPS : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), Φe w ∈ principalSeries2 p lam)

local notation "VV" => Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
  fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h))

theorem rho_mem (h : G) {u : G → ℂ} (hu : u ∈ VV) : rho p h u ∈ VV := translate_mem_span w₂base h hu

include hN hw₂K in
theorem continuous_of_mem_V {u : G → ℂ} (hu : u ∈ VV) : Continuous u :=
  (isLocallyConstant_of_mem_span w₂base _ (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN).2 hw₂K hu).continuous

include hΦPS in
theorem continuous_phie {u : G → ℂ} (hu : u ∈ VV) : Continuous (Φe u) :=
  ((mem_principalSeries2_iff.mp (hΦPS u hu)).1).continuous

theorem ell_rho (μ₂ : Measure G) [μ₂.IsHaarMeasure] (K' : Subgroup G) (hK'o : IsOpen (K' : Set G))
    (hK'c : IsCompact (K' : Set G)) (u : G → ℂ) (h : G) (hh : h ∈ K') :
    ell p μ₂ (K' : Set G) (rho p h u) = ell p μ₂ (K' : Set G) u := by
  unfold ell
  congr 1
  have := setIntegral_translate_mul_right p μ₂ K' hK'o hK'c u 1 h hh
  simpa only [rho_apply, one_mul] using this

theorem ell_leftTranslate_mul_right (μ₂ : Measure G) [μ₂.IsHaarMeasure] (K' : Subgroup G) (hK'o : IsOpen (K' : Set G))
    (hK'c : IsCompact (K' : Set G)) (φ : G → ℂ) (t h : G) (hh : h ∈ K') :
    ell p μ₂ (K' : Set G) (fun k => φ (t * k * h)) = ell p μ₂ (K' : Set G) (fun k => φ (t * k)) := by
  unfold ell
  rw [setIntegral_translate_mul_right p μ₂ K' hK'o hK'c φ t h hh]

include hN hw₂K hΦeq hΦPS in

theorem exists_W0_same_averages (μ₂ : Measure G) [μ₂.IsHaarMeasure] (K' : Subgroup G) (hK'o : IsOpen (K' : Set G))
    (hK'c : IsCompact (K' : Set G)) (T : Finset G) (a : T → ℂ) (u : G → ℂ) (hu : u ∈ VV) :
    ∃ v ∈ W0 p w₂base K', ell p μ₂ (K' : Set G) v = ell p μ₂ (K' : Set G) u ∧
      (∑ t : T, a t * ell p μ₂ (K' : Set G) (fun k => Φe v ((t : G) * k))) =
        ∑ t : T, a t * ell p μ₂ (K' : Set G) (fun k => Φe u ((t : G) * k)) := by
  classical

  obtain ⟨Uu, hUuo, hUu⟩ := exists_open_stabilizer_of_mem_span w₂base _
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN).2 hw₂K hu
  set H : Subgroup G := K' ⊓ Uu with hH
  have hHo : IsOpen (H : Set G) := by rw [hH, Subgroup.coe_inf]; exact hK'o.inter hUuo
  set Q := (K' : Type _) ⧸ (H.subgroupOf K') with hQ

  obtain ⟨R, hRK, hR⟩ := exists_finset_inv_mul_mem' p (K' : Set G) hK'c H hHo
  haveI : Finite Q := by
    refine Finite.of_surjective (fun r : R => (QuotientGroup.mk ⟨(r : G), hRK r.2⟩ : Q)) ?_
    intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      obtain ⟨r, hrR, hrk⟩ := hR k k.2
      refine ⟨⟨r, hrR⟩, ?_⟩
      apply QuotientGroup.eq.mpr
      rw [Subgroup.mem_subgroupOf]
      simpa using hrk
  letI : Fintype Q := Fintype.ofFinite Q
  have hcard : (Fintype.card Q : ℂ) ≠ 0 := by
    have : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨(QuotientGroup.mk 1 : Q)⟩
    exact_mod_cast this.ne'

  set v : G → ℂ := (Fintype.card Q : ℂ)⁻¹ • ∑ q : Q, rho p ((q.out : K') : G) u with hv
  have hvV : v ∈ VV := by
    rw [hv]; refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => rho_mem p w₂base _ hu)
  have hvfix : ∀ k ∈ K', ∀ g : G, v (g * k) = v g := by
    intro k hk g
    simp only [hv, Pi.smul_apply, Finset.sum_apply, rho_apply, smul_eq_mul]
    congr 1

    let kk : K' := ⟨k, hk⟩
    have key : ∀ q : Q, u (g * k * ((q.out : K') : G)) = u (g * (((kk • q).out : K') : G)) := by
      intro q
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (H.subgroupOf K') (kk * q.out)
      have hmk : (QuotientGroup.mk (kk * q.out) : Q) = kk • q := by
        rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
      rw [hmk] at hh

      have hhU : ((h : K') : G) ∈ Uu := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h.2)).2
      have : (((kk • q).out : K') : G) = k * ((q.out : K') : G) * ((h : K') : G) := by
        rw [hh]; rfl
      rw [this, ← mul_assoc, ← mul_assoc, hUu _ hhU]
    rw [Fintype.sum_congr _ _ key]
    exact Fintype.sum_equiv (MulAction.toPerm kk) _ _ (fun q => rfl)
  refine ⟨v, ⟨hvV, hvfix⟩, ?_, ?_⟩
  ·
    rw [hv, ell_smul, ell_finset_sum p μ₂ _ _ _ (fun q _ =>
      ((continuous_of_mem_V p N hN w₂base hw₂K (rho_mem p w₂base _ hu)).continuousOn.integrableOn_compact hK'c))]
    simp_rw [ell_rho p μ₂ K' hK'o hK'c u _ (Subtype.coe_prop _)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
  ·
    refine Finset.sum_congr rfl fun t _ => ?_
    congr 1
    have hlin : (fun k => Φe v ((t : G) * k)) =
        (Fintype.card Q : ℂ)⁻¹ • ∑ q : Q, fun k => Φe (rho p ((q.out : K') : G) u) ((t : G) * k) := by
      funext k
      simp only [hv, map_smul, map_sum, Pi.smul_apply, Finset.sum_apply]
    rw [hlin, ell_smul, ell_finset_sum p μ₂ _ _ _ (fun q _ => ?_)]
    · have hq : ∀ q : Q, ell p μ₂ (K' : Set G) (fun k => Φe (rho p ((q.out : K') : G) u) ((t : G) * k)) =
          ell p μ₂ (K' : Set G) (fun k => Φe u ((t : G) * k)) := by
        intro q
        have := hΦeq u hu ((q.out : K') : G)
        rw [show rho p ((q.out : K') : G) u = fun g => u (g * ((q.out : K') : G)) from rfl, this]
        exact ell_leftTranslate_mul_right p μ₂ K' hK'o hK'c (Φe u) t _ (Subtype.coe_prop _)
      simp_rw [hq]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
    · exact ((continuous_phie p w₂base lam Φe hΦPS (rho_mem p w₂base _ hu)).comp
        (continuous_const.mul continuous_id)).continuousOn.integrableOn_compact hK'c

include hN hw₂K hΦeq hΦinj hΦPS in

theorem kernel (μ₂ : Measure G) [μ₂.IsHaarMeasure] (K' : Subgroup G) (hK'o : IsOpen (K' : Set G))
    (hK'c : IsCompact (K' : Set G)) (T : Finset G)
    (hT : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∃ t ∈ T, t⁻¹ * k ∈ K') :
    ∃ a : T → ℂ, ∀ u ∈ VV,
      ell p μ₂ (K' : Set G) u = ∑ t : T, a t * ell p μ₂ (K' : Set G) (fun k => Φe u ((t : G) * k)) := by
  classical
  obtain ⟨ub, hub⟩ := exists_reproducing p w₂base lam Φe K' T hT hΦeq hΦinj hΦPS
  refine ⟨fun t => ell p μ₂ (K' : Set G) (ub t : G → ℂ), fun u hu => ?_⟩
  obtain ⟨v, hvW, hv1, hv2⟩ := exists_W0_same_averages p N hN w₂base hw₂K lam Φe hΦeq hΦPS μ₂ K' hK'o hK'c T
    (fun t => ell p μ₂ (K' : Set G) (ub t : G → ℂ)) u hu
  rw [← hv1, ← hv2]

  have hrep := hub ⟨v, hvW⟩
  have hint : ∀ t : T, IntegrableOn ((Φe v (t : G)) • (ub t : G → ℂ)) (K' : Set G) μ₂ := fun t =>
    ((continuous_of_mem_V p N hN w₂base hw₂K (ub t).2.1).continuousOn.integrableOn_compact hK'c).smul _
  calc ell p μ₂ (K' : Set G) v = ell p μ₂ (K' : Set G) (∑ t : T, (Φe v (t : G)) • (ub t : G → ℂ)) := by
          rw [← hrep]
    _ = ∑ t : T, Φe v (t : G) * ell p μ₂ (K' : Set G) (ub t : G → ℂ) := by
          rw [ell_finset_sum p μ₂ (K' : Set G) Finset.univ (fun t : T => (Φe v (t : G)) • (ub t : G → ℂ))
            (fun t _ => hint t)]
          simp_rw [ell_smul]
    _ = ∑ t : T, ell p μ₂ (K' : Set G) (ub t : G → ℂ) * ell p μ₂ (K' : Set G) (fun k => Φe v ((t : G) * k)) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [mul_comm]
          congr 1
          unfold ell
          exact (leftAvg_translate_const p μ₂ K' hK'o hK'c (Φe v) (t : G)
            (fun k hk => phie_right_inv p w₂base Φe hΦeq K' v hvW k hk (t : G))).symm

end Kernel2

end K3

section K4

theorem godementZeta2_finset_sum_coeff {ι : Type*} (μ₂ : Measure G) (S : Finset ι) (b : ι → ℂ) (c : ι → G → ℂ)
    (φ : M2 → ℂ) (χ : Fˣ →* ℂˣ) (s : ℂ) (hint : ∀ i ∈ S, Integrable (gjIntegrand p (c i) φ χ s) μ₂) :
    godementZeta2 p μ₂ (fun g => ∑ i ∈ S, b i * c i g) φ χ s = ∑ i ∈ S, b i * godementZeta2 p μ₂ (c i) φ χ s := by
  rw [godementZeta2_eq_integral_gjIntegrand]
  have hpt : ∀ g : G, gjIntegrand p (fun g => ∑ i ∈ S, b i * c i g) φ χ s g = ∑ i ∈ S, b i * gjIntegrand p (c i) φ χ s g := by
    intro g; simp only [gjIntegrand, Finset.sum_mul, mul_assoc]
  simp_rw [hpt]
  rw [integral_finset_sum S (fun i hi => (hint i hi).const_mul (b i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, godementZeta2_eq_integral_gjIntegrand]

theorem godementZeta2_finset_sum_test {ι : Type*} (μ₂ : Measure G) (S : Finset ι) (b : ι → ℂ) (c : G → ℂ)
    (φ : ι → M2 → ℂ) (χ : Fˣ →* ℂˣ) (s : ℂ) (hint : ∀ i ∈ S, Integrable (gjIntegrand p c (φ i) χ s) μ₂) :
    godementZeta2 p μ₂ c (fun X => ∑ i ∈ S, b i * φ i X) χ s = ∑ i ∈ S, b i * godementZeta2 p μ₂ c (φ i) χ s := by
  rw [godementZeta2_eq_integral_gjIntegrand]
  have hpt : ∀ g : G, gjIntegrand p c (fun X => ∑ i ∈ S, b i * φ i X) χ s g = ∑ i ∈ S, b i * gjIntegrand p c (φ i) χ s g := by
    intro g; simp only [gjIntegrand, Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  simp_rw [hpt]
  rw [integral_finset_sum S (fun i hi => (hint i hi).const_mul (b i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, godementZeta2_eq_integral_gjIntegrand]

def mulLeftHomeo (t : G) : M2 ≃ₜ M2 where
  toFun X := ((t⁻¹ : G) : M2) * X
  invFun X := ((t : G) : M2) * X
  left_inv X := by simp [← Matrix.mul_assoc, ← Units.val_mul]
  right_inv X := by simp [← Matrix.mul_assoc, ← Units.val_mul]
  continuous_toFun := continuous_const.matrix_mul continuous_id
  continuous_invFun := continuous_const.matrix_mul continuous_id

theorem isLocallyConstant_translate (Φ : M2 → ℂ) (hΦ : IsLocallyConstant Φ) (t : G) :
    IsLocallyConstant (fun X : M2 => Φ (((t⁻¹ : G) : M2) * X)) :=
  fun s => (hΦ s).preimage (continuous_const.matrix_mul continuous_id)

theorem hasCompactSupport_translate (Φ : M2 → ℂ) (hΦc : HasCompactSupport Φ) (t : G) :
    HasCompactSupport (fun X : M2 => Φ (((t⁻¹ : G) : M2) * X)) :=
  hΦc.comp_homeomorph (mulLeftHomeo p t)

theorem isLocallyConstant_finset_sum {ι : Type*} (S : Finset ι) (b : ι → ℂ) (φ : ι → M2 → ℂ)
    (h : ∀ i ∈ S, IsLocallyConstant (φ i)) : IsLocallyConstant (fun X => ∑ i ∈ S, b i * φ i X) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact IsLocallyConstant.const _
  | insert j S hj ih =>
      simp only [Finset.sum_insert hj]
      exact ((h j (Finset.mem_insert_self j S)).comp (fun y => b j * y)).comp₂
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi)) (· + ·)

theorem hasCompactSupport_finset_sum {ι : Type*} (S : Finset ι) (b : ι → ℂ) (φ : ι → M2 → ℂ)
    (h : ∀ i ∈ S, HasCompactSupport (φ i)) : HasCompactSupport (fun X => ∑ i ∈ S, b i * φ i X) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact HasCompactSupport.zero
  | insert j S hj ih =>
      simp only [Finset.sum_insert hj]
      exact ((h j (Finset.mem_insert_self j S)).mul_left).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end K4

section K4b

theorem modulus_det_eq_one_of_mem_K0 {k : G} (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤) :
    modulus ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) = 1 := by
  rw [AdelicDock.mem_localLevelOne_iff] at hk
  have hle : ∀ m : M2, AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ m → Valued.v m.det ≤ 1 := by
    intro m hm
    have hi : ∀ i j, Valued.v (m i j) ≤ 1 := fun i j =>
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).mp (hm.1 i j)
    rw [Matrix.det_fin_two]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
    · rw [Valuation.map_mul]; exact mul_le_one' (hi 0 0) (hi 1 1)
    · rw [Valuation.map_mul]; exact mul_le_one' (hi 0 1) (hi 1 0)
  have h1 := hle _ hk.1
  have h2 := hle _ hk.2
  have hprod : Valued.v ((k : G) : M2).det * Valued.v (((k⁻¹ : G) : M2)).det = 1 := by
    rw [← Valuation.map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one,
      Valuation.map_one]
  have hv : Valued.v ((k : G) : M2).det = 1 := by
    apply le_antisymm h1
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v ((k : G) : M2).det * Valued.v (((k⁻¹ : G) : M2)).det := hprod.symm
      _ ≤ Valued.v ((k : G) : M2).det * 1 := mul_le_mul_right h2 _
      _ = _ := mul_one _
  rw [Matrix.GeneralLinearGroup.val_det_apply, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p]
  apply NNReal.eq; rw [coe_nnnorm]; exact KCSA.norm_eq_one_of_v p hv

end K4b
section K4aux

theorem k2_gjIntegrand_avg (μ₂ : Measure G) (S : Set G) (hSm : MeasurableSet S) (α : G → G)
    (u : G → ℂ) (φ : M2 → ℂ) (χ : Fˣ →* ℂˣ) (s : ℂ)
    (hk : ∀ k ∈ S, ∀ g : G,
      gjIntegrand p (fun h : G => u (α k * h)) φ χ s g = gjIntegrand p u φ χ s (α k * g)) (g : G) :
    gjIntegrand p (fun g : G => (μ₂.real S)⁻¹ * ∫ k in S, u (α k * g) ∂μ₂) φ χ s g
      = (μ₂.real S)⁻¹ * ∫ k in S, gjIntegrand p u φ χ s (α k * g) ∂μ₂ := by
  have h1a : ∫ k in S, gjIntegrand p u φ χ s (α k * g) ∂μ₂ =
      ∫ k in S, u (α k * g) * (φ ((g : G) : M2) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) ^ s) ∂μ₂ :=
    setIntegral_congr_fun hSm fun k hk' => by
      show _ = _
      rw [← hk k hk' g]; simp only [gjIntegrand]; ring
  rw [h1a, integral_mul_const]
  simp only [gjIntegrand]; ring

theorem k2_integrable_shear (μ₂ : Measure G) [μ₂.IsHaarMeasure]
    (S : Set G) (hStop : μ₂ S ≠ ⊤) (α : G → G) (hα : Measurable α)
    (u : G → ℂ) (φ : M2 → ℂ) (χ : Fˣ →* ℂˣ) (s : ℂ)
    (hint : Integrable (gjIntegrand p u φ χ s) μ₂) :
    Integrable (Function.uncurry fun (g : G) (k : G) => gjIntegrand p u φ χ s (α k * g))
      (μ₂.prod (μ₂.restrict S)) := by
  haveI : IsFiniteMeasure (μ₂.restrict S) := isFiniteMeasure_restrict.mpr hStop
  have hT : MeasurePreserving (fun z : G × G => (id z.1, α z.1 * z.2))
      ((μ₂.restrict S).prod μ₂) ((μ₂.restrict S).prod μ₂) :=
    (MeasurePreserving.id (μ₂.restrict S)).skew_product (g := fun k h => α k * h)
      (show Measurable fun z : G × G => α z.1 * z.2 from (hα.comp measurable_fst).mul measurable_snd)
      (Filter.Eventually.of_forall fun k => map_mul_left_eq_self μ₂ (α k))
  have h2 : Integrable (fun z : G × G => gjIntegrand p u φ χ s z.2) ((μ₂.restrict S).prod μ₂) :=
    hint.comp_snd (μ₂.restrict S)
  have h3 := (hT.integrable_comp h2.aestronglyMeasurable).mpr h2
  exact h3.swap

theorem k2_integrable_gjIntegrand_avg (μ₂ : Measure G) [μ₂.IsHaarMeasure]
    (S : Set G) (hSm : MeasurableSet S) (hStop : μ₂ S ≠ ⊤)
    (α : G → G) (hα : Measurable α)
    (u : G → ℂ) (φ : M2 → ℂ) (χ : Fˣ →* ℂˣ) (s : ℂ)
    (hint : Integrable (gjIntegrand p u φ χ s) μ₂)
    (hk : ∀ k ∈ S, ∀ g : G,
      gjIntegrand p (fun h : G => u (α k * h)) φ χ s g = gjIntegrand p u φ χ s (α k * g)) :
    Integrable (gjIntegrand p (fun g : G => (μ₂.real S)⁻¹ * ∫ k in S, u (α k * g) ∂μ₂) φ χ s) μ₂ := by
  have h := ((k2_integrable_shear p μ₂ S hStop α hα u φ χ s hint).integral_prod_left).const_mul
    (((μ₂.real S)⁻¹ : ℝ) : ℂ)
  refine h.congr (Filter.Eventually.of_forall fun g => ?_)
  beta_reduce
  rw [k2_gjIntegrand_avg p μ₂ S hSm α u φ χ s hk g]
  rfl

theorem k2_hk_transposeInvN
    (K' : Subgroup G)
    (hK'det : ∀ k ∈ K', modulus ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) = 1)
    (u : G → ℂ) (Φ : M2 → ℂ) (hΦK : ∀ k ∈ K', ∀ X : M2, Φ (((k : G) : M2) * X) = Φ X)
    (χ : Fˣ →* ℂˣ) (hχK : ∀ k ∈ K', χ (Matrix.GeneralLinearGroup.det k) = 1) (s : ℂ) :
    ∀ k ∈ (K' : Set G), ∀ g : G,
      gjIntegrand p (fun h : G => u (transposeInvN (Fin 2) k * h))
          (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) χ⁻¹ s g =
        gjIntegrand p u (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) χ⁻¹ s
          (transposeInvN (Fin 2) k * g) := by
  intro k hk g
  have hmod := k2_modulus_det_transposeInvN p k (hK'det k hk)
  have h := k2_gjIntegrand_mul_left p u (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) χ⁻¹ s
    (transposeInvN (Fin 2) k) g hmod
  rw [k2_matFourier22_transposeInvN_inv_mul p K' hK'det Φ hΦK k hk, k2_det_transposeInvN,
    MonoidHom.inv_apply, map_inv, hχK k hk, inv_inv, Units.val_one, one_mul] at h
  exact h.symm

theorem integrable_gjIntegrand_avg_translate
    (μ₂ : Measure G) [μ₂.IsHaarMeasure]
    (K' : Subgroup G) (hK'o : IsOpen (K' : Set G)) (hK'c : IsCompact (K' : Set G))
    (hK'det : ∀ k ∈ K', modulus ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) = 1)
    (Fw : G → ℂ) (hFw : Continuous Fw)
    (Φ : M2 → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (hΦK : ∀ k ∈ K', ∀ X : M2, Φ (((k : G) : M2) * X) = Φ X)
    (χ : Fˣ →* ℂˣ) (hχ : IsLocallyConstant χ) (hχK : ∀ k ∈ K', χ (Matrix.GeneralLinearGroup.det k) = 1)
    (t : G) (ht : modulus ((Matrix.GeneralLinearGroup.det t : Fˣ) : F) = 1)
    (s : ℂ)
    (hint : Integrable (gjIntegrand p Fw (fun X : M2 => Φ (((t⁻¹ : G) : M2) * X)) χ s) μ₂) :
    Integrable (gjIntegrand p
      (fun g : G => (μ₂.real (K' : Set G))⁻¹ * ∫ k in (K' : Set G), Fw (t * k * g) ∂μ₂) Φ χ s) μ₂ := by
  have hu : Integrable (gjIntegrand p (fun h : G => Fw (t * h)) Φ χ s) μ₂ :=
    k2_integrable_gjIntegrand_comp_mul_left p μ₂ Fw Φ χ s t ht hint
  have hcoef : (fun g : G => (μ₂.real (K' : Set G))⁻¹ * ∫ k in (K' : Set G), Fw (t * k * g) ∂μ₂) =
      fun g : G => (μ₂.real (K' : Set G))⁻¹ * ∫ k in (K' : Set G), (fun h : G => Fw (t * h)) (id k * g) ∂μ₂ := by
    funext g; simp only [id, mul_assoc]
  rw [hcoef]
  exact k2_integrable_gjIntegrand_avg p μ₂ (K' : Set G) hK'o.measurableSet hK'c.measure_lt_top.ne id measurable_id
    (fun h : G => Fw (t * h)) Φ χ s hu (k2_hk_of_leftInvariant p K' hK'det (fun h : G => Fw (t * h)) Φ hΦK χ hχK s)

theorem integrable_gjIntegrand_avg_translate_transposeInv
    (μ₂ : Measure G) [μ₂.IsHaarMeasure]
    (K' : Subgroup G) (hK'o : IsOpen (K' : Set G)) (hK'c : IsCompact (K' : Set G))
    (hK'det : ∀ k ∈ K', modulus ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) = 1)
    (Fw : G → ℂ) (hFw : Continuous Fw)
    (Φ : M2 → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (hΦK : ∀ k ∈ K', ∀ X : M2, Φ (((k : G) : M2) * X) = Φ X)
    (χ : Fˣ →* ℂˣ) (hχ : IsLocallyConstant χ) (hχK : ∀ k ∈ K', χ (Matrix.GeneralLinearGroup.det k) = 1)
    (t : G) (ht : modulus ((Matrix.GeneralLinearGroup.det t : Fˣ) : F) = 1)
    (s : ℂ)
    (hint : Integrable (gjIntegrand p (fun g : G => Fw (transposeInvN (Fin 2) g))
      (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) (fun X : M2 => Φ (((t⁻¹ : G) : M2) * X))) χ⁻¹ s) μ₂) :
    Integrable (gjIntegrand p
      (fun g : G => (μ₂.real (K' : Set G))⁻¹ * ∫ k in (K' : Set G), Fw (t * k * transposeInvN (Fin 2) g) ∂μ₂)
      (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) χ⁻¹ s) μ₂ := by
  set ψ := NumberField.StandardAddChar.psiLocal ℚ p with hψ
  set uτ : G → ℂ := fun g : G => Fw (transposeInvN (Fin 2) g) with huτ
  have htm := k2_modulus_det_transposeInvN p t ht
  have hΦt := k2_matFourier22_translate p Φ t ht
  have hint' : Integrable (gjIntegrand p (fun h : G => uτ (transposeInvN (Fin 2) t * h))
      (matFourier22 p ψ Φ) χ⁻¹ s) μ₂ := by
    apply k2_integrable_gjIntegrand_comp_mul_left p μ₂ uτ (matFourier22 p ψ Φ) χ⁻¹ s (transposeInvN (Fin 2) t) htm
    rw [hψ, hΦt]; exact hint
  have hcoef : (fun g : G => (μ₂.real (K' : Set G))⁻¹ * ∫ k in (K' : Set G), Fw (t * k * transposeInvN (Fin 2) g) ∂μ₂) =
      fun g : G => (μ₂.real (K' : Set G))⁻¹ * ∫ k in (K' : Set G),
        (fun h : G => uτ (transposeInvN (Fin 2) t * h)) (transposeInvN (Fin 2) k * g) ∂μ₂ := by
    funext g; simp only [huτ, transposeInvN_mul, transposeInvN_transposeInvN, mul_assoc]
  rw [hcoef]
  exact k2_integrable_gjIntegrand_avg p μ₂ (K' : Set G) hK'o.measurableSet hK'c.measure_lt_top.ne
    (fun g : G => transposeInvN (Fin 2) g) (k2_continuous_transposeInvN p).measurable
    (fun h : G => uτ (transposeInvN (Fin 2) t * h)) (matFourier22 p ψ Φ) χ⁻¹ s hint'
    (k2_hk_transposeInvN p K' hK'det (fun h : G => uτ (transposeInvN (Fin 2) t * h)) Φ hΦK χ hχK s)

end K4aux
section K4C

local notation "M23" => (Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ))

theorem k4c_level_zero :
    (∀ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (0 : ℤ) → NumberField.StandardAddChar.psiLocal ℚ p x = 1) ∧
      ∃ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ NumberField.StandardAddChar.psiLocal ℚ p x ≠ 1 := by
  have hk : ∃ k : ℤ, ∀ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp k → NumberField.StandardAddChar.psiLocal ℚ p x = 1 := by
    refine ⟨0, fun x hx => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ p x ?_⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simpa using hx
  have h := LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ p
    (NumberField.StandardAddChar.psiLocal ℚ p) hk (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p)
  rwa [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p] at h

noncomputable def k4cPad (X : M2) : M23 := Matrix.of fun i k => if h : (k : ℕ) < 2 then X i ⟨k, h⟩ else 0

noncomputable def k4cCut (Y : M23) : M2 := Matrix.of fun i k => Y i (Fin.castSucc k)

theorem k4c_continuous_cut : Continuous (k4cCut p) := by
  refine continuous_pi fun i => continuous_pi fun k => ?_
  simp only [k4cCut, Matrix.of_apply]; fun_prop

theorem k4c_continuous_pad : Continuous (k4cPad p) := by
  refine continuous_pi fun i => continuous_pi fun k => ?_
  simp only [k4cPad, Matrix.of_apply]
  split_ifs <;> fun_prop

theorem k4c_pad_castSucc (X : M2) (i : Fin 2) (k : Fin 2) : k4cPad p X i (Fin.castSucc k) = X i k := by
  have hk : ((Fin.castSucc k : Fin 3) : ℕ) < 2 := by simp [k.isLt]
  simp only [k4cPad, Matrix.of_apply, dif_pos hk]
  congr 1

theorem k4c_pad_two (X : M2) (i : Fin 2) : k4cPad p X i 2 = 0 := by
  simp [k4cPad]

theorem k4c_cut_pad (X : M2) : k4cCut p (k4cPad p X) = X := by
  ext i k; simp only [k4cCut, Matrix.of_apply, k4c_pad_castSucc]

theorem k4c_setCol23_pad (X : M2) (j : Fin 2) (u : p.adicCompletion ℚ × p.adicCompletion ℚ) :
    setCol23 p (k4cPad p X) (Fin.castSucc j) u = k4cPad p (setCol22 p X j u) := by
  ext i k
  simp only [setCol23_apply]
  by_cases hk : (k : ℕ) < 2
  · have hk' : k = Fin.castSucc ⟨k, hk⟩ := by ext; simp
    rw [hk', k4c_pad_castSucc, k4c_pad_castSucc, setCol22_apply]
    by_cases hkj : (⟨k, hk⟩ : Fin 2) = j
    · subst hkj; simp
    · have : (Fin.castSucc ⟨(k : ℕ), hk⟩ : Fin 3) ≠ Fin.castSucc j := fun h => hkj (Fin.castSucc_injective _ h)
      rw [if_neg this, if_neg hkj]
  · have hk2 : k = 2 := by ext; simp; omega
    subst hk2
    have : (2 : Fin 3) ≠ Fin.castSucc j := by
      intro h; have := congrArg Fin.val h; fin_cases j <;> simp at this
    rw [if_neg this, k4c_pad_two]
    simp [k4cPad]

noncomputable def k4cLift (φ : M2 → ℂ) (Y : M23) : ℂ :=
  φ (k4cCut p Y) * ((Metric.closedBall (0 : p.adicCompletion ℚ) 1).indicator (fun _ => (1 : ℂ)) (Y 0 2) *
    (Metric.closedBall (0 : p.adicCompletion ℚ) 1).indicator (fun _ => (1 : ℂ)) (Y 1 2))

theorem k4c_lift_comp_pad (φ : M2 → ℂ) : k4cLift p φ ∘ k4cPad p = φ := by
  funext X
  simp only [Function.comp_apply, k4cLift, k4c_cut_pad, k4c_pad_two,
    Set.indicator_of_mem (Metric.mem_closedBall_self zero_le_one), mul_one]

theorem k4c_isSchwartzBruhat_lift (φ : M2 → ℂ) (hφ : IsSchwartzBruhat φ) : IsSchwartzBruhat (k4cLift p φ) := by
  have hS : IsCompact (Metric.closedBall (0 : p.adicCompletion ℚ) 1) := isCompact_closedBall 0 1
  have hSo : IsClopen (Metric.closedBall (0 : p.adicCompletion ℚ) 1) :=
    ⟨Metric.isClosed_closedBall, IsUltrametricDist.isOpen_closedBall 0 one_ne_zero⟩
  have hind : IsSchwartzBruhat ((Metric.closedBall (0 : p.adicCompletion ℚ) 1).indicator fun _ : p.adicCompletion ℚ => (1 : ℂ)) :=
    IsSchwartzBruhat.indicator_const hSo hS 1
  have hc02 : Continuous fun Y : M23 => Y 0 2 := (continuous_apply 2).comp (continuous_apply 0)
  have hc12 : Continuous fun Y : M23 => Y 1 2 := (continuous_apply 2).comp (continuous_apply 1)
  refine ⟨(hφ.1.comp_continuous (k4c_continuous_cut p)).mul ((hind.1.comp_continuous hc02).mul (hind.1.comp_continuous hc12)), ?_⟩
  let A : M2 × (p.adicCompletion ℚ × p.adicCompletion ℚ) → M23 := fun q =>
    Matrix.of fun i k => if h : (k : ℕ) < 2 then q.1 i ⟨k, h⟩ else (if i = 0 then q.2.1 else q.2.2)
  have hAc : Continuous A := by
    refine continuous_pi fun i => continuous_pi fun k => ?_
    simp only [A, Matrix.of_apply]
    split_ifs <;> fun_prop
  have hAR : ∀ Y : M23, A (k4cCut p Y, (Y 0 2, Y 1 2)) = Y := by
    intro Y; ext i k
    simp only [A, k4cCut, Matrix.of_apply]
    by_cases hk : (k : ℕ) < 2
    · rw [dif_pos hk]; congr 1
    · rw [dif_neg hk]
      have : k = 2 := by ext; simp; omega
      subst this
      fin_cases i <;> simp
  refine HasCompactSupport.intro ((hφ.2.prod (hS.prod hS)).image hAc) fun Y hY => ?_
  rw [k4cLift]
  by_cases h1 : k4cCut p Y ∈ tsupport φ
  · by_cases h2 : Y 0 2 ∈ Metric.closedBall (0 : p.adicCompletion ℚ) 1
    · by_cases h3 : Y 1 2 ∈ Metric.closedBall (0 : p.adicCompletion ℚ) 1
      · exact absurd ⟨(k4cCut p Y, (Y 0 2, Y 1 2)), ⟨h1, h2, h3⟩, hAR Y⟩ hY
      · rw [Set.indicator_of_notMem h3, mul_zero, mul_zero]
    · rw [Set.indicator_of_notMem h2, zero_mul, mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul]

theorem k4c_colFourier22_comp_pad (η : AddChar (p.adicCompletion ℚ) ℂ) (H : M23 → ℂ) (j : Fin 2) :
    colFourier22 p η j (H ∘ k4cPad p) = colFourier23 p η (Fin.castSucc j) H ∘ k4cPad p := by
  funext X
  simp only [Function.comp_apply, colFourier22_apply, colFourier23_apply, k4c_setCol23_pad, k4c_pad_castSucc]

theorem k4c_isSchwartzBruhat_colFourier22 (j : Fin 2) (φ : M2 → ℂ) (hφ : IsSchwartzBruhat φ) :
    IsSchwartzBruhat (colFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) j φ) := by
  obtain ⟨h0, h0'⟩ := k4c_level_zero p
  rw [← k4c_lift_comp_pad p φ, k4c_colFourier22_comp_pad]
  have hG := LanglandsTunnell.CubicInduction.isSchwartzBruhat_colFourier23 p (NumberField.StandardAddChar.psiLocal ℚ p) 0 h0 h0'
    (Fin.castSucc j) _ (k4c_isSchwartzBruhat_lift p φ hφ)
  refine ⟨hG.1.comp_continuous (k4c_continuous_pad p), ?_⟩
  refine HasCompactSupport.intro (hG.2.image (k4c_continuous_cut p)) fun X hX => ?_
  show colFourier23 p (NumberField.StandardAddChar.psiLocal ℚ p) (Fin.castSucc j) (k4cLift p φ) (k4cPad p X) = 0
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  exact hX ⟨k4cPad p X, hmem, k4c_cut_pad p X⟩

theorem k4c_continuous_setCol22 (X : M2) (j : Fin 2) :
    Continuous fun u : p.adicCompletion ℚ × p.adicCompletion ℚ => setCol22 p X j u := by
  refine continuous_pi fun i => continuous_pi fun k => ?_
  simp only [setCol22, Matrix.of_apply]
  split_ifs <;> fun_prop

theorem k4c_isSchwartzBruhat_comp_setCol22 (g : M2 → ℂ) (hg : IsSchwartzBruhat g) (X : M2) (j : Fin 2) :
    IsSchwartzBruhat fun u : p.adicCompletion ℚ × p.adicCompletion ℚ => g (setCol22 p X j u) := by
  refine ⟨hg.1.comp_continuous (k4c_continuous_setCol22 p X j), ?_⟩
  have hc : Continuous fun Y : M2 => (Y 0 j, Y 1 j) :=
    ((continuous_apply j).comp (continuous_apply 0)).prodMk ((continuous_apply j).comp (continuous_apply 1))
  refine HasCompactSupport.intro (hg.2.image hc) fun u hu => ?_
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  exact hu ⟨setCol22 p X j u, hmem, by simp [setCol22_apply]⟩

theorem k4c_integrable_colIntegrand (g : M2 → ℂ) (hg : IsSchwartzBruhat g) (X : M2) (j : Fin 2) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    Integrable (fun u : p.adicCompletion ℚ × p.adicCompletion ℚ =>
        g (setCol22 p X j u) * NumberField.StandardAddChar.psiLocal ℚ p (u.1 * X 0 j + u.2 * X 1 j))
      ((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) := by
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI : (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
    set c : NNReal := (Ideal.absNorm p.asIdeal : NNReal) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)
      with hc
    have hc0 : c ≠ 0 := by
      rw [hc]
      exact (NNReal.rpow_pos
        (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot))).ne'
    have hdef : selfDualHaarAt ℚ p = (c : ENNReal) • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) := rfl
    rw [hdef]
    exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top
  have hSB := k4c_isSchwartzBruhat_comp_setCol22 p g hg X j
  have hψ : Continuous fun u : p.adicCompletion ℚ × p.adicCompletion ℚ =>
      NumberField.StandardAddChar.psiLocal ℚ p (u.1 * X 0 j + u.2 * X 1 j) :=
    (NumberField.StandardAddChar.continuous_psiLocal ℚ p).comp (by fun_prop)
  exact (hSB.1.continuous.mul hψ).integrable_of_hasCompactSupport (hSB.2.mul_right)

theorem k4c_colFourier22_finset_sum {ι : Type*} (S : Finset ι) (b : ι → ℂ) (φ : ι → M2 → ℂ)
    (h : ∀ i ∈ S, IsSchwartzBruhat (φ i)) (j : Fin 2) :
    colFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) j (fun X => ∑ i ∈ S, b i * φ i X) =
      fun Y => ∑ i ∈ S, b i * colFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) j (φ i) Y := by
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  funext Y
  simp only [colFourier22_apply]
  have hint := fun i (hi : i ∈ S) => k4c_integrable_colIntegrand p (φ i) (h i hi) Y j
  calc (∫ u : p.adicCompletion ℚ × p.adicCompletion ℚ, (∑ i ∈ S, b i * φ i (setCol22 p Y j u)) *
          NumberField.StandardAddChar.psiLocal ℚ p (u.1 * Y 0 j + u.2 * Y 1 j) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)))
      = ∫ u : p.adicCompletion ℚ × p.adicCompletion ℚ, ∑ i ∈ S, b i * (φ i (setCol22 p Y j u) *
          NumberField.StandardAddChar.psiLocal ℚ p (u.1 * Y 0 j + u.2 * Y 1 j)) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) := by
        congr 1; funext u; rw [Finset.sum_mul]; simp only [mul_assoc]
    _ = ∑ i ∈ S, ∫ u : p.adicCompletion ℚ × p.adicCompletion ℚ, b i * (φ i (setCol22 p Y j u) *
          NumberField.StandardAddChar.psiLocal ℚ p (u.1 * Y 0 j + u.2 * Y 1 j)) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) :=
        integral_finset_sum S fun i hi => (hint i hi).const_mul (b i)
    _ = _ := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [integral_const_mul]

theorem matFourier22_finset_sum {ι : Type*} (S : Finset ι) (b : ι → ℂ) (φ : ι → M2 → ℂ)
    (h : ∀ i ∈ S, IsLocallyConstant (φ i) ∧ HasCompactSupport (φ i)) :
    matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) (fun X => ∑ i ∈ S, b i * φ i X) =
      fun Y => ∑ i ∈ S, b i * matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) (φ i) Y := by
  have h' : ∀ i ∈ S, IsSchwartzBruhat (φ i) := fun i hi => ⟨(h i hi).1, (h i hi).2⟩
  rw [matFourier22_eq, k4c_colFourier22_finset_sum p S b φ h' 1,
    k4c_colFourier22_finset_sum p S b _ (fun i hi => k4c_isSchwartzBruhat_colFourier22 p 1 (φ i) (h' i hi)) 0]
  funext Y
  simp only [matFourier22_eq]

end K4C

section K4main

theorem primal_identity (μ₂ : Measure G) [μ₂.IsHaarMeasure]
    (K' : Subgroup G) (hK'o : IsOpen (K' : Set G)) (hK'c : IsCompact (K' : Set G))
    (hK'det : ∀ k ∈ K', modulus ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) = 1)
    (w : G → ℂ) (hwc : Continuous w) (Fw : G → ℂ) (hFc : Continuous Fw)
    (Φ : M2 → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (hΦL : ∀ k ∈ K', ∀ X : M2, Φ (((k : G) : M2) * X) = Φ X)
    (χ : Fˣ →* ℂˣ) (hχ : IsLocallyConstant χ) (hχK : ∀ k ∈ K', χ (Matrix.GeneralLinearGroup.det k) = 1)
    (T : Finset G) (a : T → ℂ)
    (htdet : ∀ t : T, modulus ((Matrix.GeneralLinearGroup.det (t : G) : Fˣ) : F) = 1)
    (hleft : leftAvg p μ₂ (K' : Set G) w =
      fun g => ∑ t : T, a t * ((μ₂.real (K' : Set G))⁻¹ * ∫ k in (K' : Set G), Fw ((t : G) * k * g) ∂μ₂))
    (s : ℂ) (hint : Integrable (gjIntegrand p w Φ χ s) μ₂)
    (hintT : ∀ t : T, Integrable (gjIntegrand p Fw (fun X : M2 => Φ ((((t : G)⁻¹ : G) : M2) * X)) χ s) μ₂) :
    godementZeta2 p μ₂ w Φ χ s =
      godementZeta2 p μ₂ Fw (fun X : M2 => ∑ t : T,
        (a t * (((χ (Matrix.GeneralLinearGroup.det (t : G)) : ℂˣ) : ℂ))⁻¹) * Φ ((((t : G)⁻¹ : G) : M2) * X)) χ s := by
  rw [godementZeta2_eq_leftAvg p μ₂ K' hK'o hK'c hK'det w hwc Φ hΦ hΦc hΦL χ hχ hχK s hint, hleft,
    godementZeta2_finset_sum_coeff p μ₂ Finset.univ a
      (fun (t : T) (g : G) => (μ₂.real (K' : Set G))⁻¹ * ∫ k in (K' : Set G), Fw ((t : G) * k * g) ∂μ₂) Φ χ s
      (fun t _ => integrable_gjIntegrand_avg_translate p μ₂ K' hK'o hK'c hK'det Fw hFc Φ hΦ hΦc hΦL χ hχ hχK
        (t : G) (htdet t) s (hintT t)),
    godementZeta2_finset_sum_test p μ₂ Finset.univ
      (fun t : T => a t * (((χ (Matrix.GeneralLinearGroup.det (t : G)) : ℂˣ) : ℂ))⁻¹) Fw
      (fun (t : T) (X : M2) => Φ ((((t : G)⁻¹ : G) : M2) * X)) χ s (fun t _ => hintT t)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [godementZeta2_leftAvg_translate_eq p μ₂ K' hK'o hK'c hK'det Fw hFc Φ hΦ hΦc hΦL χ hχ hχK (t : G) (htdet t) s
    (hintT t), mul_assoc]

theorem dual_identity (μ₂ : Measure G) [μ₂.IsHaarMeasure]
    (K' : Subgroup G) (hK'o : IsOpen (K' : Set G)) (hK'c : IsCompact (K' : Set G))
    (hK'det : ∀ k ∈ K', modulus ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) = 1)
    (w : G → ℂ) (hwc : Continuous w) (Fw : G → ℂ) (hFc : Continuous Fw)
    (Φ : M2 → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (hΦL : ∀ k ∈ K', ∀ X : M2, Φ (((k : G) : M2) * X) = Φ X)
    (χ : Fˣ →* ℂˣ) (hχ : IsLocallyConstant χ) (hχK : ∀ k ∈ K', χ (Matrix.GeneralLinearGroup.det k) = 1)
    (T : Finset G) (a : T → ℂ)
    (htdet : ∀ t : T, modulus ((Matrix.GeneralLinearGroup.det (t : G) : Fˣ) : F) = 1)
    (hleft : leftAvg p μ₂ (K' : Set G) w =
      fun g => ∑ t : T, a t * ((μ₂.real (K' : Set G))⁻¹ * ∫ k in (K' : Set G), Fw ((t : G) * k * g) ∂μ₂))
    (s : ℂ)
    (hint : Integrable (gjIntegrand p (fun g : G => w (transposeInvN (Fin 2) g))
      (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) χ⁻¹ s) μ₂)
    (hintT : ∀ t : T, Integrable (gjIntegrand p (fun g : G => Fw (transposeInvN (Fin 2) g))
      (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) (fun X : M2 => Φ ((((t : G)⁻¹ : G) : M2) * X))) χ⁻¹ s) μ₂) :
    godementZeta2 p μ₂ (fun g : G => w (transposeInvN (Fin 2) g))
        (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) χ⁻¹ s =
      godementZeta2 p μ₂ (fun g : G => Fw (transposeInvN (Fin 2) g))
        (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) (fun X : M2 => ∑ t : T,
          (a t * (((χ (Matrix.GeneralLinearGroup.det (t : G)) : ℂˣ) : ℂ))⁻¹) * Φ ((((t : G)⁻¹ : G) : M2) * X))) χ⁻¹ s := by
  have hleft' : (fun g : G => leftAvg p μ₂ (K' : Set G) w (transposeInvN (Fin 2) g)) =
      fun g => ∑ t : T, a t * ((μ₂.real (K' : Set G))⁻¹ * ∫ k in (K' : Set G), Fw ((t : G) * k * transposeInvN (Fin 2) g) ∂μ₂) := by
    funext g; exact congrFun hleft (transposeInvN (Fin 2) g)
  rw [godementZeta2_transposeInv_eq_leftAvg p μ₂ K' hK'o hK'c hK'det w hwc Φ hΦ hΦc hΦL χ hχ hχK s hint, hleft',
    godementZeta2_finset_sum_coeff p μ₂ Finset.univ a
      (fun (t : T) (g : G) => (μ₂.real (K' : Set G))⁻¹ * ∫ k in (K' : Set G), Fw ((t : G) * k * transposeInvN (Fin 2) g) ∂μ₂)
      (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) χ⁻¹ s
      (fun t _ => integrable_gjIntegrand_avg_translate_transposeInv p μ₂ K' hK'o hK'c hK'det Fw hFc Φ hΦ hΦc hΦL χ hχ hχK
        (t : G) (htdet t) s (hintT t)),
    matFourier22_finset_sum p Finset.univ
      (fun t : T => a t * (((χ (Matrix.GeneralLinearGroup.det (t : G)) : ℂˣ) : ℂ))⁻¹)
      (fun (t : T) (X : M2) => Φ ((((t : G)⁻¹ : G) : M2) * X))
      (fun t _ => ⟨isLocallyConstant_translate p Φ hΦ (t : G), hasCompactSupport_translate p Φ hΦc (t : G)⟩),
    godementZeta2_finset_sum_test p μ₂ Finset.univ
      (fun t : T => a t * (((χ (Matrix.GeneralLinearGroup.det (t : G)) : ℂˣ) : ℂ))⁻¹) (fun g : G => Fw (transposeInvN (Fin 2) g))
      (fun (t : T) => matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) (fun X : M2 => Φ ((((t : G)⁻¹ : G) : M2) * X)))
      χ⁻¹ s (fun t _ => hintT t)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [godementZeta2_leftAvg_translate_transposeInv_eq p μ₂ K' hK'o hK'c hK'det Fw hFc Φ hΦ hΦc hΦL χ hχ hχK (t : G)
    (htdet t) s (hintT t), mul_assoc]

end K4main

end KCS

end
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))

    (lam : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φe : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))
    (hΦeq : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
      Φe (fun g => w (g * h)) = fun g => Φe w (g * h))
    (hΦinj : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), Φe w = 0 → w = 0)
    (hΦPS : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), Φe w ∈ principalSeries2 p lam)

    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
          ∃ Φt : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ, IsLocallyConstant Φt ∧ HasCompactSupport Φt ∧
            ∃ S : Finset (GL (Fin 2) (p.adicCompletion ℚ)), ∀ s : ℂ,
              ((Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    w g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s) μ₂ →
                (∀ t ∈ S, Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    Φe w g * Φ (((t⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) *
                      ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s) μ₂) →
                godementZeta2 p μ₂ w Φ χ s = godementZeta2 p μ₂ (Φe w) Φt χ s) ∧
              (Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    w (transposeInvN (Fin 2) g) *
                      matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                      ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s) μ₂ →
                (∀ t ∈ S, Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    Φe w (transposeInvN (Fin 2) g) *
                      matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p)
                        (fun X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) => Φ (((t⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * X)) (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                      ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s) μ₂) →
                godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (transposeInvN (Fin 2) g))
                    (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) χ⁻¹ s =
                  godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => Φe w (transposeInvN (Fin 2) g))
                    (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φt) χ⁻¹ s)) := by
  intro μ₂ hμ₂ w hw Φ hΦ hΦc
  classical
  obtain ⟨n, hwK, hΦL, hΦR, hχK⟩ := KCS.exists_good_congr p N hN w₂base hw₂K w hw Φ hΦ hΦc χ hχ
  have hK'o : IsOpen ((KCSA.congr ℚ p n : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) :
      Set (GL (Fin 2) (p.adicCompletion ℚ))) := KCSA.isOpen_congr (K := ℚ) (v := p) n
  have hK'c : IsCompact ((KCSA.congr ℚ p n : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) :
      Set (GL (Fin 2) (p.adicCompletion ℚ))) := KCSA.isCompact_congr (K := ℚ) (v := p) n
  have hK'det : ∀ k ∈ KCSA.congr ℚ p n,
      modulus ((Matrix.GeneralLinearGroup.det k : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = 1 :=
    fun k hk => KCS.modulus_det_eq_one_of_mem_congr p hk
  have hK0c : IsCompact ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) :
      Set (GL (Fin 2) (p.adicCompletion ℚ))) := (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p ⊤ (by simp)).1
  obtain ⟨T, hTK0, hT⟩ := KCS.exists_finset_inv_mul_mem' p _ hK0c (KCSA.congr ℚ p n) hK'o
  obtain ⟨a, ha⟩ := KCS.kernel p N hN w₂base hw₂K lam Φe hΦeq hΦinj hΦPS μ₂ (KCSA.congr ℚ p n) hK'o hK'c T hT
  have hwc : Continuous w := KCS.continuous_of_mem_V p N hN w₂base hw₂K hw
  have hFc : Continuous (Φe w) := KCS.continuous_phie p w₂base lam Φe hΦPS hw
  have htdet : ∀ t : T, modulus ((Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (p.adicCompletion ℚ)) :
      (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = 1 := fun t => KCS.modulus_det_eq_one_of_mem_K0 p (hTK0 t.2)
  have hleft : KCS.leftAvg p μ₂ ((KCSA.congr ℚ p n : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set _) w =
      fun g => ∑ t : T, a t * ((μ₂.real ((KCSA.congr ℚ p n : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set _))⁻¹ *
        ∫ k in ((KCSA.congr ℚ p n : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set _),
          Φe w ((t : GL (Fin 2) (p.adicCompletion ℚ)) * k * g) ∂μ₂) := by
    funext g
    rw [KCS.leftAvg_eq_ell, ha _ (KCS.rho_mem p w₂base g hw)]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hrho : Φe (KCS.rho p g w) = fun x => Φe w (x * g) := hΦeq w hw g
    unfold KCS.ell
    rw [hrho]
  refine ⟨fun X => ∑ t : T, (a t * (((χ (Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (p.adicCompletion ℚ))) : ℂˣ) : ℂ))⁻¹) *
      Φ ((((t : GL (Fin 2) (p.adicCompletion ℚ))⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * X),
    KCS.isLocallyConstant_finset_sum p Finset.univ _ _ (fun t _ => KCS.isLocallyConstant_translate p Φ hΦ _),
    KCS.hasCompactSupport_finset_sum p Finset.univ _ _ (fun t _ => KCS.hasCompactSupport_translate p Φ hΦc _),
    T, fun s => ⟨fun hint hintT => ?_, fun hint hintT => ?_⟩⟩
  · exact KCS.primal_identity p μ₂ (KCSA.congr ℚ p n) hK'o hK'c hK'det w hwc (Φe w) hFc Φ hΦ hΦc hΦL χ hχ hχK T a htdet
      hleft s hint (fun t => hintT (t : GL (Fin 2) (p.adicCompletion ℚ)) t.2)
  · exact KCS.dual_identity p μ₂ (KCSA.congr ℚ p n) hK'o hK'c hK'det w hwc (Φe w) hFc Φ hΦ hΦc hΦL χ hχ hχK T a htdet
      hleft s hint (fun t => hintT (t : GL (Fin 2) (p.adicCompletion ℚ)) t.2)

end S_LanglandsTunnell_RankinSelberg_exists_schwartz_godementZeta2_whittaker_eq_godementZeta2_section_and_dual_of_equivariant_embedding
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_schwartz_godementZeta2_whittaker_eq_godementZeta2_section_and_dual_of_equivariant_embedding (solution)
