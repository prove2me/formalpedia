-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_isOpen_forall_mul_eq_of_mem_principalSeries2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ef201d32-ede5-509a-9725-17fc3739af6a

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_isOpen_forall_mul_eq_of_mem_principalSeries2

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction Filter Topology Matrix
open scoped Pointwise Topology

noncomputable section

namespace LTPrincipalSmooth

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

def qR : ℝ := ((Ideal.absNorm p.asIdeal : ℕ) : ℝ)

theorem one_lt_qR : (1 : ℝ) < qR p := by
  unfold qR
  exact_mod_cast HeightOneSpectrum.one_lt_absNorm p

theorem qR_pos : (0 : ℝ) < qR p := lt_trans one_pos (one_lt_qR p)

private theorem toAdd_unzero_exp (n : ℤ) (h : (WithZero.exp n : WithZero (Multiplicative ℤ)) ≠ 0) :
    Multiplicative.toAdd (WithZero.unzero h) = n :=
  rfl

theorem norm_eq_zpow_of_valued {y : F} {k : ℤ} (h : Valued.v y = WithZero.exp k) : ‖y‖ = qR p ^ k := by
  rw [NumberField.FinitePlace.norm_def, h, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero,
    toAdd_unzero_exp]
  unfold qR
  push_cast
  rfl

def ball (k : ℤ) : Set F := {y | Valued.v y ≤ WithZero.exp k}

theorem mem_ball {k : ℤ} {y : F} : y ∈ ball p k ↔ Valued.v y ≤ WithZero.exp k := Iff.rfl

variable {p} in
theorem valued_zpow (ϖ : Fˣ) (hϖ : Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    Valued.v (((ϖ ^ k : Fˣ) : F)) = WithZero.exp (-k) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ, ← WithZero.exp_zsmul]
  congr 1
  ring

theorem ball_eq_setOf_le_valued {k : ℤ} {t : F} (hvt : Valued.v t = WithZero.exp k) :
    ball p k = {y : F | Valued.v y ≤ Valued.v t} := by
  rw [hvt]; rfl

theorem isClosed_ball' {k : ℤ} {t : F} (ht : t ≠ 0) (hvt : Valued.v t = WithZero.exp k) : IsClosed (ball p k) := by
  rw [ball_eq_setOf_le_valued p hvt]
  exact AdelicLevel.isClosed_setOf_valued_le p t ht

theorem isOpen_ball' {k : ℤ} {t : F} (ht : t ≠ 0) (hvt : Valued.v t = WithZero.exp k) : IsOpen (ball p k) := by
  rw [ball_eq_setOf_le_valued p hvt]
  exact AdelicLevel.isOpen_setOf_valued_le p t ht

theorem ball_eq_smul {k : ℤ} (t : Fˣ) (hvt : Valued.v (t : F) = WithZero.exp k) :
    ball p k = t • ((HeightOneSpectrum.adicCompletionIntegers ℚ p : Set F)) := by
  ext y
  rw [mem_ball, Set.mem_smul_set]
  simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro hy
    refine ⟨(t⁻¹ : Fˣ) • y, ?_, by simp⟩
    rw [Units.smul_def, smul_eq_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hvt]
    calc (WithZero.exp k)⁻¹ * Valued.v y ≤ (WithZero.exp k)⁻¹ * WithZero.exp k := mul_le_mul_right hy _
      _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
  · rintro ⟨z, hz, rfl⟩
    rw [Units.smul_def, smul_eq_mul, map_mul, hvt]
    calc WithZero.exp k * Valued.v z ≤ WithZero.exp k * 1 := mul_le_mul_right hz _
      _ = WithZero.exp k := mul_one _

theorem isCompact_ball {k : ℤ} (t : Fˣ) (hvt : Valued.v (t : F) = WithZero.exp k) : IsCompact (ball p k) := by
  rw [ball_eq_smul p t hvt, ← coe_integersPositiveCompacts ℚ p]
  exact (integersPositiveCompacts ℚ p).isCompact.smul _

def lowerUnip (y : F) : G where
  val := !![1, 0; y, 1]
  inv := !![1, 0; -y, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem lowerUnip_coe (y : F) : ((lowerUnip p y : G) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; y, 1] := rfl

theorem lowerUnip_zero : lowerUnip p 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem continuous_lowerUnip : Continuous (lowerUnip p) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [lowerUnip] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [lowerUnip] <;> fun_prop

theorem continuous_upperUnipotent2 : Continuous (upperUnipotent2 p) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent2] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent2] <;> fun_prop

theorem diagonal2_coe' (a : Fin 2 → Fˣ) :
    ((diagonal2 p a : G) : Matrix (Fin 2) (Fin 2) F) = !![(a 0 : F), 0; 0, (a 1 : F)] := by
  rw [diagonal2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem eq_antidiagonal2 (w₀ : G) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0]) : w₀ = antidiagonal2 p := by
  apply Units.ext
  rw [hw₀, antidiagonal2_coe]

theorem coe_upper_diag (x : F) (a : Fin 2 → Fˣ) :
    ((upperUnipotent2 p x * diagonal2 p a : G) : Matrix (Fin 2) (Fin 2) F)
      = !![(a 0 : F), x * (a 1 : F); 0, (a 1 : F)] := by
  rw [Units.val_mul, upperUnipotent2_coe, diagonal2_coe', Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem coe_weyl_upper (y : F) :
    ((antidiagonal2 p * upperUnipotent2 p y : G) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, y] := by
  rw [Units.val_mul, upperUnipotent2_coe, antidiagonal2_coe, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem weyl_upper_eq (y : F) (hy : y ≠ 0) :
    antidiagonal2 p * upperUnipotent2 p y
      = upperUnipotent2 p y⁻¹ * diagonal2 p ![Units.mk0 (-y⁻¹) (neg_ne_zero.mpr (inv_ne_zero hy)),
          Units.mk0 y hy] * lowerUnip p y⁻¹ := by
  apply Units.ext
  rw [coe_weyl_upper, Units.val_mul, coe_upper_diag, lowerUnip_coe, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

variable (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ))

theorem law {f : G → ℂ} (hf : f ∈ principalSeries2 p χ) (x : F) (a : Fin 2 → Fˣ) (g : G) :
    f (upperUnipotent2 p x * (diagonal2 p a * g)) = torusChar2 p χ a * halfModulus2 p a * f g := by
  obtain ⟨-, hn, ht⟩ := mem_principalSeries2_iff.mp hf
  rw [hn, ht]

theorem halfModulus2_boundary (y : F) (hy : y ≠ 0) :
    halfModulus2 p ![Units.mk0 (-y⁻¹) (neg_ne_zero.mpr (inv_ne_zero hy)), Units.mk0 y hy] = ((‖y‖⁻¹ : ℝ) : ℂ) := by
  unfold halfModulus2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_mk0, norm_neg, norm_inv]
  congr 1
  rw [div_eq_mul_inv, Real.sqrt_mul_self (inv_nonneg.mpr (norm_nonneg _))]

theorem apply_weyl_upper {f : G → ℂ} (hf : f ∈ principalSeries2 p χ) (y : F) (hy : y ≠ 0) (g : G) :
    f (antidiagonal2 p * upperUnipotent2 p y * g) =
      ((χ 0 (Units.mk0 (-y⁻¹) (neg_ne_zero.mpr (inv_ne_zero hy))) : ℂˣ) : ℂ) * ((χ 1 (Units.mk0 y hy) : ℂˣ) : ℂ) *
        ((‖y‖⁻¹ : ℝ) : ℂ) * f (lowerUnip p y⁻¹ * g) := by
  rw [weyl_upper_eq p y hy]
  simp only [mul_assoc]
  rw [law p χ hf, halfModulus2_boundary p y hy]
  simp only [torusChar2, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem exists_radius_lowerUnip {f : G → ℂ} (hf : f ∈ principalSeries2 p χ) (g : G) :
    ∃ k₀ : ℕ, ∀ t : F, Valued.v t ≤ WithZero.exp (-(k₀ : ℤ)) → f (lowerUnip p t * g) = f g := by
  obtain ⟨hlc, -, -⟩ := mem_principalSeries2_iff.mp hf
  have hcont : Continuous fun t : F => lowerUnip p t * g := (continuous_lowerUnip p).mul continuous_const
  obtain ⟨U, hU, hgU, hfU⟩ := hlc.exists_open g
  have hU0 : (fun t : F => lowerUnip p t * g) ⁻¹' U ∈ 𝓝 (0 : F) :=
    hcont.continuousAt.preimage_mem_nhds (by rw [lowerUnip_zero, one_mul]; exact hU.mem_nhds hgU)
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hU0
  obtain ⟨k, hk⟩ := WithZero.exists_exp_neg_natCast_lt (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)
  refine ⟨k, fun t ht => hfU _ (hγ ?_)⟩
  show Valued.v.restrict t < _
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt ht hk

theorem exists_radius_of_mem_nhds {s : Set F} (hs : s ∈ 𝓝 (0 : F)) :
    ∃ k : ℕ, ∀ t : F, Valued.v t ≤ WithZero.exp (-(k : ℤ)) → t ∈ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hs
  obtain ⟨k, hk⟩ := WithZero.exists_exp_neg_natCast_lt (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)
  refine ⟨k, fun t ht => hγ ?_⟩
  show Valued.v.restrict t < _
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt ht hk

theorem exists_eq_upper_mul_diag_of_corner_eq_zero (g : G) (hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    ∃ (x : F) (a : Fin 2 → Fˣ), g = upperUnipotent2 p x * diagonal2 p a := by
  have hdet := gl2Det_ne_zero p g
  rw [gl2Det_eq] at hdet
  simp only [gl2Entry, hc, mul_zero, sub_zero] at hdet
  have ha : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  have hd : (g : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  refine ⟨(g : Matrix (Fin 2) (Fin 2) F) 0 1 / (g : Matrix (Fin 2) (Fin 2) F) 1 1,
    ![Units.mk0 _ ha, Units.mk0 _ hd], ?_⟩
  apply Units.ext
  rw [coe_upper_diag]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_mk0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hc]
  all_goals (field_simp)

theorem exists_eq_upper_mul_diag_mul_weyl_upper_of_corner_ne_zero (g : G)
    (hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    ∃ (x : F) (a : Fin 2 → Fˣ) (y : F),
      g = upperUnipotent2 p x * diagonal2 p a * (antidiagonal2 p * upperUnipotent2 p y) := by
  have hdet : -((g : Matrix (Fin 2) (Fin 2) F).det) / (g : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
    refine div_ne_zero (neg_ne_zero.mpr ?_) hc
    have := gl2Det_ne_zero p g
    rwa [gl2Det] at this
  refine ⟨(g : Matrix (Fin 2) (Fin 2) F) 0 0 / (g : Matrix (Fin 2) (Fin 2) F) 1 0, ![Units.mk0 _ hdet, Units.mk0 _ hc],
    (g : Matrix (Fin 2) (Fin 2) F) 1 1 / (g : Matrix (Fin 2) (Fin 2) F) 1 0, ?_⟩
  apply Units.ext
  rw [Units.val_mul, coe_upper_diag, coe_weyl_upper]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_mk0]
  rw [Matrix.det_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals (field_simp; try ring)

def stabilizer (f : G → ℂ) : Subgroup G where
  carrier := {k | ∀ g : G, f (g * k) = f g}
  mul_mem' := fun {a b} ha hb g => by rw [← mul_assoc, hb, ha]
  one_mem' := fun g => by rw [mul_one]
  inv_mem' := fun {a} ha g => by rw [← ha (g * a⁻¹), inv_mul_cancel_right]

theorem mem_stabilizer_iff (f : G → ℂ) (k : G) : k ∈ stabilizer p f ↔ ∀ g : G, f (g * k) = f g := Iff.rfl

theorem exists_radius_nhds_lowerUnip {f : G → ℂ} (hf : f ∈ principalSeries2 p χ) :
    ∃ k₀ : ℕ, ∃ W ∈ 𝓝 (1 : G), ∀ w ∈ W, ∀ s : F, Valued.v s ≤ WithZero.exp (-(k₀ : ℤ)) →
      f (lowerUnip p s * w) = f 1 := by
  obtain ⟨hlc, -, -⟩ := mem_principalSeries2_iff.mp hf
  have hc : Continuous fun q : F × G => lowerUnip p q.1 * q.2 :=
    ((continuous_lowerUnip p).comp continuous_fst).mul continuous_snd
  have hopen : IsOpen ((fun q : F × G => f (lowerUnip p q.1 * q.2)) ⁻¹' {f 1}) :=
    (hlc.comp_continuous hc) {f 1}
  have hP : (fun q : F × G => f (lowerUnip p q.1 * q.2)) ⁻¹' {f 1} ∈ 𝓝 ((0 : F), (1 : G)) :=
    hopen.mem_nhds (by show f (lowerUnip p 0 * 1) = f 1; rw [lowerUnip_zero, one_mul])
  obtain ⟨B, hB, W, hW, hBW⟩ := mem_nhds_prod_iff.mp hP
  obtain ⟨k₀, hk₀⟩ := exists_radius_of_mem_nhds p hB
  refine ⟨k₀, W, hW, fun w hw s hs => ?_⟩
  have hmem := hBW (Set.mk_mem_prod (hk₀ s hs) hw)
  exact hmem

theorem exists_nhds_weyl_near {f : G → ℂ} (hf : f ∈ principalSeries2 p χ) (k₀ : ℕ) :
    ∃ W ∈ 𝓝 (1 : G), ∀ w ∈ W, ∀ y : F, Valued.v y ≤ WithZero.exp (k₀ : ℤ) →
      f (antidiagonal2 p * upperUnipotent2 p y * w) = f (antidiagonal2 p * upperUnipotent2 p y * 1) := by
  obtain ⟨hlc, -, -⟩ := mem_principalSeries2_iff.mp hf
  have h1 : IsLocallyConstant fun q : F × G => f (antidiagonal2 p * upperUnipotent2 p q.1 * q.2) :=
    hlc.comp_continuous ((continuous_const.mul ((continuous_upperUnipotent2 p).comp continuous_fst)).mul
      continuous_snd)
  have h2 : IsLocallyConstant fun q : F × G => f (antidiagonal2 p * upperUnipotent2 p q.1 * 1) :=
    hlc.comp_continuous ((continuous_const.mul ((continuous_upperUnipotent2 p).comp continuous_fst)).mul
      continuous_const)
  have h3 := h1.comp₂ h2 (· - ·)
  have hQopen : IsOpen ((fun q : F × G => f (antidiagonal2 p * upperUnipotent2 p q.1 * q.2) -
      f (antidiagonal2 p * upperUnipotent2 p q.1 * 1)) ⁻¹' {0}) := h3 {0}
  have hvk : Valued.v (((AdelicLevel.uniformizerUnit ℚ p ^ (-(k₀ : ℤ)) : Fˣ) : F)) = WithZero.exp (k₀ : ℤ) := by
    rw [valued_zpow _ (AdelicLevel.valued_uniformizerUnit ℚ p), neg_neg]
  have hballc : IsCompact (ball p k₀) := isCompact_ball p _ hvk
  have hsub : ball p k₀ ×ˢ ({1} : Set G) ⊆ ((fun q : F × G => f (antidiagonal2 p * upperUnipotent2 p q.1 * q.2) -
      f (antidiagonal2 p * upperUnipotent2 p q.1 * 1)) ⁻¹' {0}) := by
    rintro ⟨y, w⟩ ⟨-, hw⟩
    rw [Set.mem_singleton_iff] at hw
    subst hw
    simp
  obtain ⟨u, W, -, hWo, hbu, h1W, huW⟩ := generalized_tube_lemma hballc isCompact_singleton hQopen hsub
  refine ⟨W, hWo.mem_nhds (h1W (Set.mem_singleton 1)), fun w hw y hy => ?_⟩
  have hmem := huW (Set.mk_mem_prod (hbu hy) hw)
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hmem
  exact sub_eq_zero.mp hmem

theorem stabilizer_mem_nhds {f : G → ℂ} (hf : f ∈ principalSeries2 p χ) :
    (stabilizer p f : Set G) ∈ 𝓝 (1 : G) := by
  obtain ⟨hlc, hn, ht⟩ := mem_principalSeries2_iff.mp hf
  obtain ⟨k₀, W₃, hW₃, hnear1⟩ := exists_radius_nhds_lowerUnip p χ hf
  obtain ⟨W₄, hW₄, hnear⟩ := exists_nhds_weyl_near p χ hf k₀
  refine Filter.mem_of_superset (Filter.inter_mem hW₃ hW₄) ?_
  rintro w ⟨hw₃, hw₄⟩
  rw [SetLike.mem_coe, mem_stabilizer_iff]
  intro g
  have hw1 : f w = f 1 := by
    have := hnear1 w hw₃ 0 (by simp)
    rwa [lowerUnip_zero, one_mul] at this

  have hweyl : ∀ y : F,
      f (antidiagonal2 p * upperUnipotent2 p y * w) = f (antidiagonal2 p * upperUnipotent2 p y) := by
    intro y
    by_cases hy : Valued.v y ≤ WithZero.exp (k₀ : ℤ)
    · rw [hnear w hw₄ y hy, mul_one]
    · rw [not_le] at hy
      have hy0 : y ≠ 0 := by
        intro h
        rw [h, map_zero] at hy
        exact not_lt_zero hy
      have hvy0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy0
      have hlog : Valued.v y = WithZero.exp (WithZero.log (Valued.v y)) := (WithZero.exp_log hvy0).symm
      have hyi : Valued.v y⁻¹ ≤ WithZero.exp (-(k₀ : ℤ)) := by
        rw [hlog] at hy
        rw [map_inv₀, hlog, ← WithZero.exp_neg, WithZero.exp_le_exp]
        have := WithZero.exp_lt_exp.mp hy
        omega
      rw [apply_weyl_upper p χ hf y hy0 w, ← mul_one (antidiagonal2 p * upperUnipotent2 p y),
        apply_weyl_upper p χ hf y hy0 1, hnear1 w hw₃ _ hyi, hnear1 1 (mem_of_mem_nhds hW₃) _ hyi]

  by_cases hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · obtain ⟨x, a, hg⟩ := exists_eq_upper_mul_diag_of_corner_eq_zero p g hc
    have e1 : f (g * w) = torusChar2 p χ a * halfModulus2 p a * f w := by
      rw [hg, mul_assoc, hn, ht]
    have e2 : f g = torusChar2 p χ a * halfModulus2 p a * f 1 := by
      rw [hg, ← mul_one (diagonal2 p a), hn, ht]
    rw [e1, e2, hw1]
  · obtain ⟨x, a, y, hg⟩ := exists_eq_upper_mul_diag_mul_weyl_upper_of_corner_ne_zero p g hc
    have key := hweyl y
    rw [hg]
    simp only [mul_assoc]
    rw [hn, hn, ht, ht]
    rw [mul_assoc] at key
    rw [key]

theorem exists_isOpen_subgroup_forall_mul_eq {f : G → ℂ} (hf : f ∈ principalSeries2 p χ) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, f (g * k) = f g :=
  ⟨stabilizer p f, Subgroup.isOpen_of_mem_nhds _ (stabilizer_mem_nhds p χ hf), fun _ hk g => hk g⟩

theorem eventually_forall_apply_mul_upperUnipotent2_eq {f : G → ℂ} (hf : f ∈ principalSeries2 p χ) :
    ∀ᶠ t in 𝓝 (0 : F), ∀ g : G, f (g * upperUnipotent2 p t) = f g := by
  obtain ⟨U, hU, hfU⟩ := exists_isOpen_subgroup_forall_mul_eq p χ hf
  have hmem : (upperUnipotent2 p) ⁻¹' (U : Set G) ∈ 𝓝 (0 : F) :=
    (continuous_upperUnipotent2 p).continuousAt.preimage_mem_nhds
      (by rw [upperUnipotent2_zero]; exact hU.mem_nhds U.one_mem)
  filter_upwards [hmem] with t ht g
  exact hfU _ ht g

end LTPrincipalSmooth
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isOpen_forall_mul_eq_of_mem_principalSeries2.LTPrincipalSmooth"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isOpen_forall_mul_eq_of_mem_principalSeries2.LTPrincipalSmooth"

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p θ) :
    ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), f (g * k) = f g :=
  LTPrincipalSmooth.exists_isOpen_subgroup_forall_mul_eq p θ hf

end S_LanglandsTunnell_CubicInduction_exists_isOpen_forall_mul_eq_of_mem_principalSeries2
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_isOpen_forall_mul_eq_of_mem_principalSeries2 (solution)
