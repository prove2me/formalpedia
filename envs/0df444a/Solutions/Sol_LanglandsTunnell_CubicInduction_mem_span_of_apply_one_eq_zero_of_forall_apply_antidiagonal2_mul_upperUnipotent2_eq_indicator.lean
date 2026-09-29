-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.mem_span_of_apply_one_eq_zero_of_forall_apply_antidiagonal2_mul_upperUnipotent2_eq_indicator
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/0411a8fd-797f-5d85-8b5d-134e8553b3cf

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isOpen_forall_mul_eq_of_mem_principalSeries2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_mem_span_of_apply_one_eq_zero_of_forall_apply_antidiagonal2_mul_upperUnipotent2_eq_indicator

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

noncomputable section

namespace W5b3G

open NumberField.AdelicLevel Topology
open scoped Pointwise

variable (v : HeightOneSpectrum (𝓞 ℚ))

abbrev Fv : Type := v.adicCompletion ℚ
abbrev G2 : Type := GL (Fin 2) (v.adicCompletion ℚ)

def ball (j : ℤ) : Set (Fv v) := {y : Fv v | Valued.v y ≤ WithZero.exp j}

theorem mem_ball {j : ℤ} {y : Fv v} : y ∈ ball v j ↔ Valued.v y ≤ WithZero.exp j := Iff.rfl

theorem zero_mem_ball (j : ℤ) : (0 : Fv v) ∈ ball v j := by
  rw [mem_ball, map_zero]; exact zero_le'

theorem add_mem_ball {j : ℤ} {a b : Fv v} (ha : a ∈ ball v j) (hb : b ∈ ball v j) : a + b ∈ ball v j := by
  show Valued.v (a + b) ≤ WithZero.exp j
  exact (Valuation.map_add _ _ _).trans (max_le ha hb)

theorem ball_mono {i j : ℤ} (h : i ≤ j) : ball v i ⊆ ball v j :=
  fun _ hy => hy.trans (WithZero.exp_le_exp.mpr h)

abbrev ϖu : (Fv v)ˣ := uniformizerUnit ℚ v

theorem v_ϖu : Valued.v ((ϖu v : (Fv v)ˣ) : Fv v) = WithZero.exp (-1 : ℤ) := valued_uniformizerUnit ℚ v

theorem v_ϖu_zpow (a : ℤ) : Valued.v (((ϖu v) ^ a : (Fv v)ˣ) : Fv v) = WithZero.exp (-a) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, v_ϖu]
  have hne : (WithZero.exp (-1 : ℤ)) ^ a ≠ 0 := zpow_ne_zero a WithZero.exp_ne_zero
  rw [← WithZero.exp_log hne, WithZero.log_zpow, WithZero.log_exp, smul_eq_mul, mul_neg_one]

theorem ball_eq_smul (j : ℤ) : ball v j = ((ϖu v) ^ (-j) : (Fv v)ˣ) • ball v 0 := by
  ext y
  constructor
  · intro hy
    refine ⟨(((ϖu v) ^ j : (Fv v)ˣ) : Fv v) * y, ?_, ?_⟩
    · show Valued.v ((((ϖu v) ^ j : (Fv v)ˣ) : Fv v) * y) ≤ WithZero.exp 0
      rw [map_mul, v_ϖu_zpow]
      rcases eq_or_ne y 0 with rfl | hy0
      · rw [map_zero, mul_zero]; exact zero_le'
      · have hvy : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy0
        rw [mem_ball, ← WithZero.exp_log hvy, WithZero.exp_le_exp] at hy
        rw [← WithZero.exp_log hvy, ← WithZero.exp_add, WithZero.exp_le_exp]
        omega
    · show ((ϖu v) ^ (-j) : (Fv v)ˣ) • ((((ϖu v) ^ j : (Fv v)ˣ) : Fv v) * y) = y
      rw [Units.smul_def, smul_eq_mul, ← mul_assoc, ← Units.val_mul, zpow_neg, inv_mul_cancel, Units.val_one, one_mul]
  · rintro ⟨z, hz, rfl⟩
    show Valued.v (((ϖu v) ^ (-j) : (Fv v)ˣ) • z) ≤ WithZero.exp j
    rw [Units.smul_def, smul_eq_mul, map_mul, v_ϖu_zpow, neg_neg]
    have hz' : Valued.v z ≤ WithZero.exp 0 := hz
    calc WithZero.exp j * Valued.v z ≤ WithZero.exp j * WithZero.exp 0 := mul_le_mul_right hz' _
      _ = WithZero.exp j := by rw [WithZero.exp_zero, mul_one]

theorem isCompact_ball_zero : IsCompact (ball v 0) := by
  have h : ball v 0 = Set.range ((↑) : v.adicCompletionIntegers ℚ → Fv v) := by
    rw [Subtype.range_coe]
    ext y
    rw [mem_ball, WithZero.exp_zero]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).symm
  rw [h]
  exact isCompact_range continuous_subtype_val

theorem isCompact_ball (j : ℤ) : IsCompact (ball v j) := by
  rw [ball_eq_smul v j, ← Set.image_smul]
  have hc : Continuous fun x : Fv v => ((ϖu v) ^ (-j) : (Fv v)ˣ) • x := by
    have : (fun x : Fv v => ((ϖu v) ^ (-j) : (Fv v)ˣ) • x) =
        fun x : Fv v => ((((ϖu v) ^ (-j) : (Fv v)ˣ)) : Fv v) * x := by
      funext x; rw [Units.smul_def, smul_eq_mul]
    rw [this]; exact continuous_const_mul _
  exact (isCompact_ball_zero v).image hc

theorem restrict_ne_zero {y : Fv v} (hy : y ≠ 0) :
    (Valued.v.restrict y : MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v : Valuation (Fv v) (WithZero (Multiplicative ℤ))))) ≠ 0 := by
  rw [Ne, Valuation.restrict_eq_zero_iff]
  exact (Valuation.ne_zero_iff _).2 hy

theorem ball_eq_restrict (j : ℤ) :
    ball v j = {x : Fv v | Valued.v.restrict x ≤ Valued.v.restrict ((((ϖu v) ^ (-j) : (Fv v)ˣ) : Fv v))} := by
  ext x
  rw [mem_ball, Set.mem_setOf_eq, ← not_lt, ← not_lt, Valuation.restrict_lt_iff, v_ϖu_zpow, neg_neg]

theorem isOpen_ball (j : ℤ) : IsOpen (ball v j) := by
  rw [ball_eq_restrict]
  exact Valued.isOpen_closedBall (R := Fv v) (restrict_ne_zero v (Units.ne_zero _))

theorem exists_ball_subset_of_mem_nhds_zero {s : Set (Fv v)} (hs : s ∈ 𝓝 (0 : Fv v)) :
    ∃ k : ℤ, ∀ y : Fv v, Valued.v y ≤ WithZero.exp k → y ∈ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := fun h =>
    γ.ne_zero ((map_eq_zero_iff _ MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective).1 h)
  refine ⟨WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) - 1, fun y hy => hγ ?_⟩
  simp only [Set.mem_setOf_eq]
  rw [Valuation.restrict_lt_iff_lt_embedding]
  calc Valued.v y ≤ WithZero.exp (WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) - 1) := hy
    _ < WithZero.exp (WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)) :=
        WithZero.exp_lt_exp.2 (by omega)
    _ = MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := WithZero.exp_log hne

def cball (r : ℤ) (x : Fv v) : Set (Fv v) := {z : Fv v | Valued.v (z - x) ≤ WithZero.exp r}

theorem mem_cball {r : ℤ} {x z : Fv v} : z ∈ cball v r x ↔ Valued.v (z - x) ≤ WithZero.exp r := Iff.rfl

theorem mem_cball_self (r : ℤ) (x : Fv v) : x ∈ cball v r x := by
  rw [mem_cball, sub_self, map_zero]; exact zero_le'

theorem cball_eq_of_mem {r : ℤ} {x z : Fv v} (hz : z ∈ cball v r x) : cball v r z = cball v r x := by
  ext w
  rw [mem_cball, mem_cball]
  rw [mem_cball] at hz
  constructor
  · intro hw
    have : w - x = (w - z) + (z - x) := by abel
    rw [this]; exact Valuation.map_add_le _ hw hz
  · intro hw
    have : w - z = (w - x) - (z - x) := by abel
    rw [this]; exact Valuation.map_sub_le _ hw hz

theorem isOpen_cball (r : ℤ) (x : Fv v) : IsOpen (cball v r x) := by
  have h : cball v r x = (fun z => z - x) ⁻¹' ball v r := rfl
  rw [h]
  exact (isOpen_ball v r).preimage (continuous_id.sub continuous_const)

theorem exists_reps (R r : ℤ) : ∃ T : Finset (Fv v), (∀ t ∈ T, t ∈ ball v R) ∧
    ∀ y ∈ ball v R, ∃! t, t ∈ T ∧ Valued.v (y - t) ≤ WithZero.exp r := by
  classical
  have hcov : ball v R ⊆ ⋃ x ∈ ball v R, cball v r x :=
    fun x hx => Set.mem_biUnion hx (mem_cball_self v r x)
  obtain ⟨T₀, hT₀sub, hT₀fin, hT₀cov⟩ :=
    (isCompact_ball v R).elim_finite_subcover_image (fun x _ => isOpen_cball v r x) hcov
  let c : Set (Fv v) → Fv v := fun S => Classical.epsilon fun t => t ∈ T₀ ∧ t ∈ S
  have hc : ∀ x ∈ T₀, c (cball v r x) ∈ T₀ ∧ c (cball v r x) ∈ cball v r x :=
    fun x hx => Classical.epsilon_spec (p := fun t => t ∈ T₀ ∧ t ∈ cball v r x) ⟨x, hx, mem_cball_self v r x⟩
  refine ⟨hT₀fin.toFinset.image fun x => c (cball v r x), ?_, ?_⟩
  · intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨x, hx, rfl⟩ := ht
    rw [Set.Finite.mem_toFinset] at hx
    exact hT₀sub (hc x hx).1
  · intro y hy
    obtain ⟨x, hxT, hyx⟩ := Set.mem_iUnion₂.1 (hT₀cov hy)
    refine ⟨c (cball v r x), ⟨Finset.mem_image.2 ⟨x, (Set.Finite.mem_toFinset _).2 hxT, rfl⟩, ?_⟩, ?_⟩
    ·
      have h1 : y ∈ cball v r (c (cball v r x)) := by
        rw [cball_eq_of_mem v (hc x hxT).2]; exact hyx
      exact h1
    · rintro t ⟨htT, hty⟩
      rw [Finset.mem_image] at htT
      obtain ⟨x', hx'T, rfl⟩ := htT
      rw [Set.Finite.mem_toFinset] at hx'T
      have e1 : cball v r (c (cball v r x')) = cball v r x' := cball_eq_of_mem v (hc x' hx'T).2
      have e2 : cball v r y = cball v r (c (cball v r x')) := cball_eq_of_mem v hty
      have e3 : cball v r y = cball v r x := cball_eq_of_mem v hyx
      show c (cball v r x') = c (cball v r x)
      rw [← e1, ← e2, e3]

def lowerUnipotent2 (c : Fv v) : G2 v where
  val := !![1, 0; c, 1]
  inv := !![1, 0; -c, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem lowerUnipotent2_coe (c : Fv v) :
    (lowerUnipotent2 v c : Matrix (Fin 2) (Fin 2) (Fv v)) = !![1, 0; c, 1] := rfl

theorem lowerUnipotent2_zero : lowerUnipotent2 v 0 = 1 := by
  apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;> simp

theorem continuous_lowerUnipotent2 : Continuous (lowerUnipotent2 v) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [lowerUnipotent2] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [lowerUnipotent2] <;> fun_prop

theorem continuous_upperUnipotent2 : Continuous (upperUnipotent2 v) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent2] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent2] <;> fun_prop

theorem diagonal2_coe' (a : Fin 2 → (Fv v)ˣ) :
    (diagonal2 v a : Matrix (Fin 2) (Fin 2) (Fv v)) = !![(a 0 : Fv v), 0; 0, (a 1 : Fv v)] := by
  rw [diagonal2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem antidiagonal2_mul_upperUnipotent2_eq {x : Fv v} (hx : x ≠ 0) :
    antidiagonal2 v * upperUnipotent2 v x =
      upperUnipotent2 v x⁻¹ * diagonal2 v ![Units.mk0 (-x⁻¹) (neg_ne_zero.2 (inv_ne_zero hx)), Units.mk0 x hx] *
        lowerUnipotent2 v x⁻¹ := by
  apply Units.ext
  simp only [Units.val_mul, lowerUnipotent2_coe, upperUnipotent2_coe, diagonal2_coe', antidiagonal2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem eq_of_corner_eq_zero (g : G2 v) (hc : (g : Matrix (Fin 2) (Fin 2) (Fv v)) 1 0 = 0) :
    ∃ (y : Fv v) (a : Fin 2 → (Fv v)ˣ), g = upperUnipotent2 v y * diagonal2 v a := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) (Fv v)).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det g).ne_zero
  have hdet' : (g : Matrix (Fin 2) (Fin 2) (Fv v)) 0 0 * (g : Matrix (Fin 2) (Fin 2) (Fv v)) 1 1 ≠ 0 := by
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet; exact hdet
  have h00 : (g : Matrix (Fin 2) (Fin 2) (Fv v)) 0 0 ≠ 0 := left_ne_zero_of_mul hdet'
  have h11 : (g : Matrix (Fin 2) (Fin 2) (Fv v)) 1 1 ≠ 0 := right_ne_zero_of_mul hdet'
  refine ⟨(g : Matrix (Fin 2) (Fin 2) (Fv v)) 0 1 / (g : Matrix (Fin 2) (Fin 2) (Fv v)) 1 1,
    ![Units.mk0 _ h00, Units.mk0 _ h11], ?_⟩
  apply Units.ext
  simp only [Units.val_mul, upperUnipotent2_coe, diagonal2_coe']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc] <;> field_simp

theorem eq_of_corner_ne_zero (g : G2 v) (hc : (g : Matrix (Fin 2) (Fin 2) (Fv v)) 1 0 ≠ 0) :
    ∃ (y : Fv v) (a : Fin 2 → (Fv v)ˣ) (x : Fv v),
      g = upperUnipotent2 v y * diagonal2 v a * (antidiagonal2 v * upperUnipotent2 v x) := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) (Fv v)).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det g).ne_zero
  have hp : -(g : Matrix (Fin 2) (Fin 2) (Fv v)).det / (g : Matrix (Fin 2) (Fin 2) (Fv v)) 1 0 ≠ 0 :=
    div_ne_zero (neg_ne_zero.2 hdet) hc
  refine ⟨(g : Matrix (Fin 2) (Fin 2) (Fv v)) 0 0 / (g : Matrix (Fin 2) (Fin 2) (Fv v)) 1 0,
    ![Units.mk0 _ hp, Units.mk0 _ hc],
    (g : Matrix (Fin 2) (Fin 2) (Fv v)) 1 1 / (g : Matrix (Fin 2) (Fin 2) (Fv v)) 1 0, ?_⟩
  apply Units.ext
  simp only [Units.val_mul, upperUnipotent2_coe, diagonal2_coe', antidiagonal2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> field_simp <;> ring

variable {v}
variable (θ : Fin 2 → ((Fv v)ˣ →* ℂˣ))

theorem eq_zero_of_profile (g : ↥(principalSeries2 v θ)) (h1 : (g : G2 v → ℂ) 1 = 0)
    (hw : ∀ x : Fv v, (g : G2 v → ℂ) (antidiagonal2 v * upperUnipotent2 v x) = 0) : g = 0 := by
  obtain ⟨-, hN, hT⟩ := g.2
  apply Subtype.ext
  funext k
  show (g : G2 v → ℂ) k = 0
  by_cases hc : (k : Matrix (Fin 2) (Fin 2) (Fv v)) 1 0 = 0
  · obtain ⟨y, a, rfl⟩ := eq_of_corner_eq_zero v k hc
    rw [hN, ← mul_one (diagonal2 v a), hT, h1, mul_zero]
  · obtain ⟨y, a, x, rfl⟩ := eq_of_corner_ne_zero v k hc
    rw [mul_assoc, hN, hT, hw, mul_zero]

theorem coe_sum_smul_apply {ι : Type} (T : Finset ι) (c : ι → ℂ) (w : ι → ↥(principalSeries2 v θ)) (k : G2 v) :
    ((∑ t ∈ T, c t • w t : ↥(principalSeries2 v θ)) : G2 v → ℂ) k = ∑ t ∈ T, c t * ((w t : ↥(principalSeries2 v θ)) : G2 v → ℂ) k := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Submodule.coe_add, Pi.add_apply, ih, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul]

theorem main (φ : ℤ → Fv v → ↥(principalSeries2 v θ))
    (hφ1 : ∀ (n : ℤ) (t : Fv v), (φ n t : G2 v → ℂ) 1 = 0)
    (hφ : ∀ (n : ℤ) (t x : Fv v),
      (φ n t : G2 v → ℂ) (antidiagonal2 v * upperUnipotent2 v x) =
        if Valued.v (x - t) ≤ WithZero.exp (-n) then 1 else 0)
    (f : ↥(principalSeries2 v θ)) (h1 : (f : G2 v → ℂ) 1 = 0) :
    f ∈ Submodule.span ℂ (Set.range fun nt : ℤ × Fv v => φ nt.1 nt.2) := by
  classical
  obtain ⟨-, hN, hT⟩ := f.2
  obtain ⟨U, hUo, hU⟩ :=
    LanglandsTunnell.CubicInduction.exists_isOpen_forall_mul_eq_of_mem_principalSeries2 v θ (f : G2 v → ℂ) f.2

  have hUn : ∀ (u : Fv v → G2 v), Continuous u → u 0 = 1 →
      ∃ k : ℤ, ∀ s : Fv v, Valued.v s ≤ WithZero.exp k → u s ∈ U := by
    intro u hu hu0
    have : {s : Fv v | u s ∈ U} ∈ 𝓝 (0 : Fv v) := by
      apply (hUo.preimage hu).mem_nhds
      show u 0 ∈ (U : Set (G2 v))
      rw [hu0]; exact U.one_mem
    exact exists_ball_subset_of_mem_nhds_zero v this
  obtain ⟨k₁, hk₁⟩ := hUn (upperUnipotent2 v) (continuous_upperUnipotent2 v) (upperUnipotent2_zero v)
  obtain ⟨k₀, hk₀⟩ := hUn (lowerUnipotent2 v) (continuous_lowerUnipotent2 v) (lowerUnipotent2_zero v)

  obtain ⟨P, hP⟩ : ∃ P : Fv v → ℂ, ∀ x, P x = (f : G2 v → ℂ) (antidiagonal2 v * upperUnipotent2 v x) :=
    ⟨_, fun _ => rfl⟩
  have hP1 : ∀ x s : Fv v, Valued.v s ≤ WithZero.exp k₁ → P (x + s) = P x := by
    intro x s hs
    rw [hP, hP, ← upperUnipotent2_mul, ← mul_assoc, hU _ (hk₁ s hs)]
  set R : ℤ := -k₀ with hR
  have hP2 : ∀ x : Fv v, x ∉ ball v R → P x = 0 := by
    intro x hx
    rw [mem_ball, not_le] at hx
    have hx0 : x ≠ 0 := by
      intro h; rw [h, map_zero] at hx; exact not_lt_of_ge zero_le' hx
    have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
    have hinv : Valued.v x⁻¹ ≤ WithZero.exp k₀ := by
      rw [map_inv₀, ← WithZero.exp_log hvx, ← WithZero.exp_neg, WithZero.exp_le_exp]
      rw [← WithZero.exp_log hvx, WithZero.exp_lt_exp] at hx
      omega
    rw [hP, antidiagonal2_mul_upperUnipotent2_eq v hx0, mul_assoc, hN, hT, ← one_mul (lowerUnipotent2 v x⁻¹),
      hU _ (hk₀ _ hinv), h1, mul_zero]

  set m : ℤ := max (-k₁) (-R) with hm
  have hm1 : -m ≤ k₁ := by omega
  have hm2 : -m ≤ R := by omega
  obtain ⟨T, hTR, hT⟩ := exists_reps v R (-m)

  have key : f = ∑ t ∈ T, P t • φ m t := by
    rw [← sub_eq_zero]
    apply eq_zero_of_profile θ
    · rw [Submodule.coe_sub, Pi.sub_apply, coe_sum_smul_apply, h1]
      simp [hφ1]
    · intro x
      rw [Submodule.coe_sub, Pi.sub_apply, coe_sum_smul_apply, ← hP x]
      simp only [hφ]
      by_cases hx : x ∈ ball v R
      · obtain ⟨t₀, ⟨ht₀T, ht₀⟩, huniq⟩ := hT x hx
        rw [Finset.sum_eq_single_of_mem t₀ ht₀T]
        · rw [if_pos ht₀, mul_one]
          have : P x = P t₀ := by
            have e : x = t₀ + (x - t₀) := by abel
            rw [e]; exact hP1 t₀ (x - t₀) (ht₀.trans (WithZero.exp_le_exp.2 hm1))
          rw [this]; exact sub_self _
        · intro t htT hne
          rw [if_neg, mul_zero]
          intro ht
          exact hne (huniq t ⟨htT, ht⟩)
      · rw [hP2 x hx, Finset.sum_eq_zero, sub_zero]
        intro t htT
        rw [if_neg, mul_zero]
        intro ht
        apply hx
        have e : x = t + (x - t) := by abel
        rw [e]
        exact add_mem_ball v (hTR t htT) ((ht.trans (WithZero.exp_le_exp.2 hm2)))
  rw [key]
  exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(m, t), rfl⟩)

end W5b3G
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mem_span_of_apply_one_eq_zero_of_forall_apply_antidiagonal2_mul_upperUnipotent2_eq_indicator.W5b3G"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mem_span_of_apply_one_eq_zero_of_forall_apply_antidiagonal2_mul_upperUnipotent2_eq_indicator.W5b3G"

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (φ : ℤ → p.adicCompletion ℚ → ↥(principalSeries2 p θ))
    (hφ1 : ∀ (n : ℤ) (t : p.adicCompletion ℚ), (φ n t : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) 1 = 0)
    (hφ : ∀ (n : ℤ) (t x : p.adicCompletion ℚ),
      (φ n t : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (antidiagonal2 p * upperUnipotent2 p x) =
        if Valued.v (x - t) ≤ WithZero.exp (-n) then 1 else 0)
    (f : ↥(principalSeries2 p θ)) (h1 : (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) 1 = 0) :
    f ∈ Submodule.span ℂ (Set.range fun nt : ℤ × p.adicCompletion ℚ => φ nt.1 nt.2) :=
  W5b3G.main θ φ hφ1 hφ f h1

end S_LanglandsTunnell_CubicInduction_mem_span_of_apply_one_eq_zero_of_forall_apply_antidiagonal2_mul_upperUnipotent2_eq_indicator
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_mem_span_of_apply_one_eq_zero_of_forall_apply_antidiagonal2_mul_upperUnipotent2_eq_indicator (solution)
