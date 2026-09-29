-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_eq_smul_of_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/a1abe87b-b3ae-5e01-98dd-c733fab0b669

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

noncomputable section

namespace WhittakerPS2Mult

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal Matrix Topology Filter NumberField.AdelicLevel

section Main

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

def qR : ℝ := ((Ideal.absNorm p.asIdeal : ℕ) : ℝ)

theorem one_lt_qR : (1 : ℝ) < qR p := by
  unfold qR
  exact_mod_cast HeightOneSpectrum.one_lt_absNorm p

theorem qR_pos : (0 : ℝ) < qR p := lt_trans one_pos (one_lt_qR p)

theorem qR_zpow_pos (k : ℤ) : (0 : ℝ) < qR p ^ k := zpow_pos (qR_pos p) k

def varpi : Fˣ := uniformizerUnit ℚ p

private theorem toAdd_unzero_exp (n : ℤ) (h : (WithZero.exp n : WithZero (Multiplicative ℤ)) ≠ 0) :
    Multiplicative.toAdd (WithZero.unzero h) = n :=
  rfl

theorem valued_varpi_zpow (k : ℤ) :
    Valued.v (((varpi p ^ k : Fˣ) : F)) = WithZero.exp (-k) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
  unfold varpi
  rw [valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  ring

theorem norm_varpi_zpow (k : ℤ) : ‖((varpi p ^ k : Fˣ) : F)‖ = qR p ^ (-k) := by
  rw [NumberField.FinitePlace.norm_def, valued_varpi_zpow,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, toAdd_unzero_exp]
  unfold qR
  push_cast
  rfl

theorem norm_le_zpow_iff_valued (k : ℤ) (y : F) :
    ‖y‖ ≤ qR p ^ (-k) ↔ Valued.v (y * ((varpi p ^ (-k) : Fˣ) : F)) ≤ 1 := by
  rw [← Valued.toNormedField.norm_le_one_iff, norm_mul, norm_varpi_zpow, neg_neg]
  rw [← le_div_iff₀ (qR_zpow_pos p k), one_div, ← _root_.zpow_neg]

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

theorem continuous_diagonal2 : Continuous (diagonal2 p) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun a : Fin 2 → Fˣ => Matrix.diagonal fun i => (a i : F)
    exact Continuous.matrix_diagonal (continuous_pi fun i => Units.continuous_val.comp (continuous_apply i))
  · show Continuous fun a : Fin 2 → Fˣ => Matrix.diagonal fun i => (((a i)⁻¹ : Fˣ) : F)
    exact Continuous.matrix_diagonal
      (continuous_pi fun i => Units.continuous_coe_inv.comp (continuous_apply i))

theorem diagonal2_one : diagonal2 p 1 = 1 := by
  ext i j
  simp [diagonal2, Matrix.one_apply]

theorem diagonal2_coe' (a : Fin 2 → Fˣ) :
    ((diagonal2 p a : G) : Matrix (Fin 2) (Fin 2) F) = !![(a 0 : F), 0; 0, (a 1 : F)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

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

theorem coe_upper_diag_weyl_upper (x : F) (a : Fin 2 → Fˣ) (y : F) :
    ((upperUnipotent2 p x * diagonal2 p a * (antidiagonal2 p * upperUnipotent2 p y) : G) :
        Matrix (Fin 2) (Fin 2) F)
      = !![x * (a 1 : F), (a 0 : F) + x * (a 1 : F) * y; (a 1 : F), (a 1 : F) * y] := by
  rw [Units.val_mul, coe_upper_diag, coe_weyl_upper, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem bruhat_small (g : G) (hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    ∃ (x : F) (a : Fin 2 → Fˣ), g = upperUnipotent2 p x * diagonal2 p a := by
  set A : F := (g : Matrix (Fin 2) (Fin 2) F) 0 0 with hA
  set B : F := (g : Matrix (Fin 2) (Fin 2) F) 0 1 with hB
  set D : F := (g : Matrix (Fin 2) (Fin 2) F) 1 1 with hD
  have hdet : A * D ≠ 0 := by
    have h := (Matrix.GeneralLinearGroup.det g).ne_zero
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, hc, mul_zero, sub_zero] at h
    exact h
  have hA0 : A ≠ 0 := left_ne_zero_of_mul hdet
  have hD0 : D ≠ 0 := right_ne_zero_of_mul hdet
  have hg : (g : Matrix (Fin 2) (Fin 2) F) = !![A, B; 0, D] := by
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · exact hc
    · rfl
  refine ⟨B / D, ![Units.mk0 A hA0, Units.mk0 D hD0], ?_⟩
  apply Units.ext
  rw [hg, coe_upper_diag]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

theorem bruhat_big (g : G) (hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    ∃ (x : F) (a : Fin 2 → Fˣ) (y : F),
      g = upperUnipotent2 p x * diagonal2 p a * (antidiagonal2 p * upperUnipotent2 p y) := by
  set A : F := (g : Matrix (Fin 2) (Fin 2) F) 0 0 with hA
  set B : F := (g : Matrix (Fin 2) (Fin 2) F) 0 1 with hB
  set Cc : F := (g : Matrix (Fin 2) (Fin 2) F) 1 0 with hC
  set D : F := (g : Matrix (Fin 2) (Fin 2) F) 1 1 with hD
  have hdet : A * D - B * Cc ≠ 0 := by
    have h := (Matrix.GeneralLinearGroup.det g).ne_zero
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at h
    exact h
  have hg : (g : Matrix (Fin 2) (Fin 2) F) = !![A, B; Cc, D] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hα : -(A * D - B * Cc) / Cc ≠ 0 := div_ne_zero (neg_ne_zero.mpr hdet) hc
  refine ⟨A / Cc, ![Units.mk0 _ hα, Units.mk0 Cc hc], D / Cc, ?_⟩
  apply Units.ext
  rw [hg, coe_upper_diag_weyl_upper]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

theorem weyl_upper_eq (y : F) (hy : y ≠ 0) :
    antidiagonal2 p * upperUnipotent2 p y
      = upperUnipotent2 p y⁻¹ * diagonal2 p ![Units.mk0 (-y⁻¹) (neg_ne_zero.mpr (inv_ne_zero hy)),
          Units.mk0 y hy] * lowerUnip p y⁻¹ := by
  apply Units.ext
  rw [coe_weyl_upper, Units.val_mul, coe_upper_diag, lowerUnip_coe, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

theorem weyl_upper_mul_diagonal2 (y : F) (t : Fˣ) :
    antidiagonal2 p * upperUnipotent2 p y * diagonal2 p ![1, t]
      = diagonal2 p ![t, 1] * (antidiagonal2 p * upperUnipotent2 p (y * (t : F))) := by
  apply Units.ext
  rw [Units.val_mul, coe_weyl_upper, Units.val_mul, coe_weyl_upper, diagonal2_coe', diagonal2_coe',
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem upper_mul_upper (y x : F) :
    upperUnipotent2 p y * upperUnipotent2 p x = upperUnipotent2 p (y + x) :=
  upperUnipotent2_mul p y x

variable (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))

theorem law {f : G → ℂ} (hf : f ∈ principalSeries2 p χ) (x : F) (a : Fin 2 → Fˣ) (g : G) :
    f (upperUnipotent2 p x * diagonal2 p a * g) = torusChar2 p χ a * halfModulus2 p a * f g := by
  obtain ⟨-, hn, ht⟩ := mem_principalSeries2_iff.mp hf
  rw [mul_assoc, hn, ht]

theorem law_one {f : G → ℂ} (hf : f ∈ principalSeries2 p χ) (x : F) (a : Fin 2 → Fˣ) :
    f (upperUnipotent2 p x * diagonal2 p a) = torusChar2 p χ a * halfModulus2 p a * f 1 := by
  rw [← law p χ hf x a 1, mul_one]

theorem rho_coe (g : G) (f : ↥(principalSeries2 p χ)) :
    ((principalSeries2Rep χ g f : ↥(principalSeries2 p χ)) : G → ℂ) = fun h => (f : G → ℂ) (h * g) := rfl

theorem rho_apply (g : G) (f : ↥(principalSeries2 p χ)) (h : G) :
    ((principalSeries2Rep χ g f : ↥(principalSeries2 p χ)) : G → ℂ) h = (f : G → ℂ) (h * g) := rfl

theorem rho_mul (g g' : G) (f : ↥(principalSeries2 p χ)) :
    principalSeries2Rep χ (g * g') f = principalSeries2Rep χ g (principalSeries2Rep χ g' f) := by
  rw [map_mul]
  rfl

theorem rho_one (f : ↥(principalSeries2 p χ)) : principalSeries2Rep χ (1 : G) f = f := by
  rw [map_one]
  rfl

def evalOne : ↥(principalSeries2 p χ) →ₗ[ℂ] ℂ where
  toFun f := (f : G → ℂ) 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evalOne_apply (f : ↥(principalSeries2 p χ)) : evalOne p χ f = (f : G → ℂ) 1 := rfl

def V0 : Submodule ℂ ↥(principalSeries2 p χ) := LinearMap.ker (evalOne p χ)

theorem mem_V0_iff (f : ↥(principalSeries2 p χ)) : f ∈ V0 p χ ↔ (f : G → ℂ) 1 = 0 :=
  LinearMap.mem_ker

def phi (f : ↥(principalSeries2 p χ)) (y : F) : ℂ :=
  (f : G → ℂ) (antidiagonal2 p * upperUnipotent2 p y)

theorem phi_add (f g : ↥(principalSeries2 p χ)) (y : F) : phi p χ (f + g) y = phi p χ f y + phi p χ g y := rfl

theorem phi_sub (f g : ↥(principalSeries2 p χ)) (y : F) : phi p χ (f - g) y = phi p χ f y - phi p χ g y := rfl

theorem phi_smul (c : ℂ) (f : ↥(principalSeries2 p χ)) (y : F) : phi p χ (c • f) y = c * phi p χ f y := rfl

theorem phi_zero (y : F) : phi p χ 0 y = 0 := rfl

theorem phi_rho_upper (f : ↥(principalSeries2 p χ)) (x y : F) :
    phi p χ (principalSeries2Rep χ (upperUnipotent2 p x) f) y = phi p χ f (y + x) := by
  unfold phi
  rw [rho_apply, mul_assoc, upper_mul_upper]

theorem rho_upper_sub_mem_V0 (f : ↥(principalSeries2 p χ)) (x : F) :
    principalSeries2Rep χ (upperUnipotent2 p x) f - f ∈ V0 p χ := by
  rw [mem_V0_iff, Submodule.coe_sub, Pi.sub_apply, rho_apply, one_mul]
  obtain ⟨-, hn, -⟩ := mem_principalSeries2_iff.mp f.2
  have := hn x 1
  rw [mul_one] at this
  rw [this, sub_self]

theorem rho_upper_mem_V0 {f : ↥(principalSeries2 p χ)} (hf : f ∈ V0 p χ) (x : F) :
    principalSeries2Rep χ (upperUnipotent2 p x) f ∈ V0 p χ := by
  have h := (V0 p χ).add_mem (rho_upper_sub_mem_V0 p χ f x) hf
  rwa [sub_add_cancel] at h

theorem eq_zero_of_mem_V0_of_phi_eq_zero {f : ↥(principalSeries2 p χ)} (hf : f ∈ V0 p χ)
    (hphi : ∀ y, phi p χ f y = 0) : f = 0 := by
  rw [mem_V0_iff] at hf
  apply Subtype.ext
  funext g
  show (f : G → ℂ) g = 0
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · obtain ⟨x, a, rfl⟩ := bruhat_small p g hc
    rw [law_one p χ f.2, hf, mul_zero]
  · obtain ⟨x, a, y, rfl⟩ := bruhat_big p g hc
    rw [law p χ f.2]
    have := hphi y
    unfold phi at this
    rw [this, mul_zero]

theorem isLocallyConstant_phi (f : ↥(principalSeries2 p χ)) : IsLocallyConstant (phi p χ f) := by
  obtain ⟨hlc, -, -⟩ := mem_principalSeries2_iff.mp f.2
  exact hlc.comp_continuous (continuous_const.mul (continuous_upperUnipotent2 p))

theorem exists_bound_phi_eq_zero {f : ↥(principalSeries2 p χ)} (hf : f ∈ V0 p χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : F, C < ‖y‖ → phi p χ f y = 0 := by
  rw [mem_V0_iff] at hf
  obtain ⟨hlc, -, -⟩ := mem_principalSeries2_iff.mp f.2
  obtain ⟨U, hUopen, hU1, hUconst⟩ := hlc.exists_open 1
  have hpre : ∃ ε > 0, ∀ c : F, ‖c‖ < ε → lowerUnip p c ∈ U := by
    have hcont : ContinuousAt (lowerUnip p) 0 := (continuous_lowerUnip p).continuousAt
    have hmem : U ∈ 𝓝 (lowerUnip p 0) := by
      rw [lowerUnip_zero]
      exact hUopen.mem_nhds hU1
    have := hcont.preimage_mem_nhds hmem
    rw [Metric.mem_nhds_iff] at this
    obtain ⟨ε, hε, hball⟩ := this
    refine ⟨ε, hε, fun c hc => hball ?_⟩
    rw [Metric.mem_ball, dist_zero_right]
    exact hc
  obtain ⟨ε, hε, hεU⟩ := hpre
  refine ⟨ε⁻¹, inv_pos.mpr hε, fun y hy => ?_⟩
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, norm_zero] at hy
    exact absurd hy (not_lt.mpr (le_of_lt (inv_pos.mpr hε)))
  have hyinv : ‖y⁻¹‖ < ε := by
    rw [norm_inv, inv_lt_comm₀ (norm_pos_iff.mpr hy0) hε]
    exact hy
  unfold phi
  rw [weyl_upper_eq p y hy0, law p χ f.2, hUconst _ (hεU _ hyinv), hf, mul_zero]

theorem exists_uniform_scale_phi {f : ↥(principalSeries2 p χ)} (hf : f ∈ V0 p χ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : F, ‖y‖ ≤ δ → phi p χ f (x + y) = phi p χ f x := by
  obtain ⟨C, hC, hCz⟩ := exists_bound_phi_eq_zero p χ hf
  have hφlc := isLocallyConstant_phi p χ f
  set S : Set F := Metric.closedBall 0 C with hS
  have hScomp : IsCompact S := isCompact_closedBall 0 C
  have hcover : ∀ a ∈ S, ∃ εa > 0, ∀ z, ‖z - a‖ < εa → phi p χ f z = phi p χ f a := by
    intro a _
    obtain ⟨U, hUopen, hUa, hUconst⟩ := hφlc.exists_open a
    obtain ⟨εa, hεa, hball⟩ := Metric.isOpen_iff.mp hUopen a hUa
    refine ⟨εa, hεa, fun z hz => ?_⟩
    have : z ∈ Metric.ball a εa := by rwa [Metric.mem_ball, dist_eq_norm]
    exact hUconst _ (hball this)
  choose! eps heps hepsconst using hcover
  obtain ⟨t, hts, htcov⟩ := hScomp.elim_nhds_subcover
    (fun a => Metric.ball a (eps a)) (fun a ha => Metric.ball_mem_nhds a (heps a ha))
  have h0S : (0 : F) ∈ S := by
    rw [hS, Metric.mem_closedBall, dist_self]
    exact le_of_lt hC
  have htne : t.Nonempty := by
    by_contra ht
    rw [Finset.not_nonempty_iff_eq_empty] at ht
    have := htcov h0S
    rw [ht] at this
    simp at this
  set δ0 : ℝ := t.inf' htne (fun a => eps a) with hδ0
  have hδ0pos : 0 < δ0 := by
    rw [hδ0, Finset.lt_inf'_iff]
    intro a ha
    exact heps a (hts a ha)
  refine ⟨min (δ0 / 2) (C / 2), lt_min (by linarith) (by linarith), fun x y hy => ?_⟩
  by_cases hxS : x ∈ S
  · have hx' := htcov hxS
    rw [Set.mem_iUnion₂] at hx'
    obtain ⟨a, hat, hxa⟩ := hx'
    rw [Metric.mem_ball, dist_eq_norm] at hxa
    have hxy : ‖(x + y) - a‖ < eps a := by
      have h1 : ‖y‖ < eps a := by
        have h2 : δ0 ≤ eps a := Finset.inf'_le _ hat
        have h3 : ‖y‖ ≤ δ0 / 2 := le_trans hy (min_le_left _ _)
        linarith
      calc ‖(x + y) - a‖ = ‖(x - a) + y‖ := by ring_nf
        _ ≤ max ‖x - a‖ ‖y‖ := IsUltrametricDist.norm_add_le_max _ _
        _ < eps a := max_lt hxa h1
    rw [hepsconst a (hts a hat) _ hxy, hepsconst a (hts a hat) _ hxa]
  · have hxC : C < ‖x‖ := by
      rw [hS, Metric.mem_closedBall, dist_zero_right, not_le] at hxS
      exact hxS
    have hyx : ‖y‖ < ‖x‖ := by
      have : ‖y‖ ≤ C / 2 := le_trans hy (min_le_right _ _)
      linarith
    have hxyC : C < ‖x + y‖ := by
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hyx), max_eq_left hyx.le]
      exact hxC
    rw [hCz _ hxyC, hCz _ hxC]

theorem norm_add_le_iff_of_norm_le {x y : F} {R : ℝ} (hy : ‖y‖ ≤ R) : ‖x + y‖ ≤ R ↔ ‖x‖ ≤ R := by
  constructor
  · intro h
    have : x = (x + y) + (-y) := by ring
    rw [this]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le h ?_)
    rwa [norm_neg]
  · intro h
    exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le h hy)

theorem norm_sub_add_le_iff_of_norm_le {x y a : F} {R : ℝ} (hy : ‖y‖ ≤ R) : ‖x + y - a‖ ≤ R ↔ ‖x - a‖ ≤ R := by
  rw [show x + y - a = (x - a) + y by ring]
  exact norm_add_le_iff_of_norm_le p hy

def IsWhitt (ψ : AddChar F ℂ) (ℓ : ↥(principalSeries2 p χ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ (x : F) (f : ↥(principalSeries2 p χ)), ℓ (principalSeries2Rep χ (upperUnipotent2 p x) f) = ψ x * ℓ f

variable {χ}

theorem IsWhitt.sub {ψ : AddChar F ℂ} {ℓ₁ ℓ₂ : ↥(principalSeries2 p χ) →ₗ[ℂ] ℂ} (h₁ : IsWhitt p χ ψ ℓ₁)
    (h₂ : IsWhitt p χ ψ ℓ₂) (c : ℂ) : IsWhitt p χ ψ (ℓ₂ - c • ℓ₁) := by
  intro x f
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, h₁ x f, h₂ x f, smul_eq_mul]
  ring

theorem exists_ne_one_of_ne_one {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) : ∃ y : F, ψ y ≠ 1 := by
  by_contra h
  push Not at h
  exact hψ (by
    ext z
    rw [h z, AddChar.one_apply])

theorem eq_zero_of_isWhitt_of_forall_V0 {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {ℓ : ↥(principalSeries2 p χ) →ₗ[ℂ] ℂ} (hw : IsWhitt p χ ψ ℓ) (h0 : ∀ f ∈ V0 p χ, ℓ f = 0) : ℓ = 0 := by
  obtain ⟨y, hy⟩ := exists_ne_one_of_ne_one p hψ
  ext f
  have hker := h0 _ (rho_upper_sub_mem_V0 p χ f y)
  rw [map_sub, hw y f, sub_eq_zero] at hker
  have : (ψ y - 1) * ℓ f = 0 := by rw [sub_mul, one_mul, hker, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hy
  · simpa using h

def IsTame (ψ : AddChar F ℂ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ y : F, ‖y‖ ≤ δ → ψ y = 1

theorem isTame_one : IsTame p (1 : AddChar F ℂ) :=
  ⟨1, one_pos, fun y _ => AddChar.one_apply y⟩

theorem forall_V0_eq_zero_of_not_isTame {ψ : AddChar F ℂ} (hwild : ¬ IsTame p ψ)
    {ℓ : ↥(principalSeries2 p χ) →ₗ[ℂ] ℂ} (hw : IsWhitt p χ ψ ℓ) : ∀ f ∈ V0 p χ, ℓ f = 0 := by
  intro f hf
  obtain ⟨δ, hδ, hδconst⟩ := exists_uniform_scale_phi p χ hf
  have hex : ∃ y : F, ‖y‖ ≤ δ ∧ ψ y ≠ 1 := by
    by_contra h
    push Not at h
    exact hwild ⟨δ, hδ, h⟩
  obtain ⟨y, hyδ, hy1⟩ := hex
  have hfix : principalSeries2Rep χ (upperUnipotent2 p y) f = f := by
    have hsub : principalSeries2Rep χ (upperUnipotent2 p y) f - f ∈ V0 p χ :=
      rho_upper_sub_mem_V0 p χ f y
    have hphi : ∀ x, phi p χ (principalSeries2Rep χ (upperUnipotent2 p y) f - f) x = 0 := by
      intro x
      rw [phi_sub, phi_rho_upper, hδconst x y hyδ, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_mem_V0_of_phi_eq_zero p χ hsub hphi)
  have hval := hw y f
  rw [hfix] at hval
  have h2 : (ψ y - 1) * ℓ f = 0 := by rw [sub_mul, one_mul, ← hval, sub_self]
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp h) hy1
  · exact h

theorem eq_zero_of_isWhitt_of_not_isTame {ψ : AddChar F ℂ} (hwild : ¬ IsTame p ψ)
    {ℓ : ↥(principalSeries2 p χ) →ₗ[ℂ] ℂ} (hw : IsWhitt p χ ψ ℓ) : ℓ = 0 := by
  have hψ : ψ ≠ 1 := fun h => hwild (h ▸ isTame_one p)
  exact eq_zero_of_isWhitt_of_forall_V0 p hψ hw (forall_V0_eq_zero_of_not_isTame p hwild hw)

theorem eq_zero_of_isWhitt_of_V0_eq_bot {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) (hbot : V0 p χ = ⊥)
    {ℓ : ↥(principalSeries2 p χ) →ₗ[ℂ] ℂ} (hw : IsWhitt p χ ψ ℓ) : ℓ = 0 := by
  refine eq_zero_of_isWhitt_of_forall_V0 p hψ hw fun f hf => ?_
  rw [hbot, Submodule.mem_bot] at hf
  rw [hf, map_zero]

theorem isLocallyConstant_norm_units : IsLocallyConstant fun a : Fˣ => ‖(a : F)‖ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro a
  exact (Units.continuous_val.tendsto a).eventually (eventually_norm_eq p a.ne_zero)

theorem continuous_vec2_left : Continuous fun a : Fˣ => (![a, 1] : Fin 2 → Fˣ) := by
  refine continuous_pi fun j => ?_
  fin_cases j
  · exact continuous_id
  · exact continuous_const

theorem continuous_vec2_right : Continuous fun a : Fˣ => (![1, a] : Fin 2 → Fˣ) := by
  refine continuous_pi fun j => ?_
  fin_cases j
  · exact continuous_const
  · exact continuous_id

theorem torusChar2_left (a : Fˣ) : torusChar2 p χ ![a, 1] = ((χ 0 a : ℂˣ) : ℂ) := by
  simp [torusChar2, Fin.prod_univ_two]

theorem torusChar2_right (a : Fˣ) : torusChar2 p χ ![1, a] = ((χ 1 a : ℂˣ) : ℂ) := by
  simp [torusChar2, Fin.prod_univ_two]

theorem isLocallyConstant_halfModulus2_left : IsLocallyConstant fun a : Fˣ => halfModulus2 p ![a, 1] := by
  have h := (isLocallyConstant_norm_units p).comp fun r : ℝ => ((Real.sqrt (r / ‖((1 : Fˣ) : F)‖) : ℝ) : ℂ)
  convert h using 1
  all_goals first | rfl | (funext a; simp [halfModulus2, Function.comp])

theorem isLocallyConstant_halfModulus2_right : IsLocallyConstant fun a : Fˣ => halfModulus2 p ![1, a] := by
  have h := (isLocallyConstant_norm_units p).comp fun r : ℝ => ((Real.sqrt (‖((1 : Fˣ) : F)‖ / r) : ℝ) : ℂ)
  convert h using 1
  all_goals first | rfl | (funext a; simp [halfModulus2, Function.comp])

theorem isLocallyConstant_char_of {χ' : Fˣ →* ℂˣ} {r h : Fˣ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hr : ∀ a, r a ≠ 0) (hrlc : IsLocallyConstant r) (hhlc : IsLocallyConstant h)
    (heq : ∀ a, h a = ((χ' a : ℂˣ) : ℂ) * r a * c) : IsLocallyConstant χ' := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro a
  have e1 := (IsLocallyConstant.iff_eventually_eq _).mp hrlc a
  have e2 := (IsLocallyConstant.iff_eventually_eq _).mp hhlc a
  filter_upwards [e1, e2] with b hb1 hb2
  rw [heq, heq, hb1] at hb2
  have h3 : (((χ' b : ℂˣ) : ℂ) - χ' a) * (r a * c) = 0 := by linear_combination hb2
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact Units.ext (sub_eq_zero.mp h4)
  · exact absurd h4 (mul_ne_zero (hr a) hc)

theorem isLocallyConstant_chi_of_ne_zero {f : ↥(principalSeries2 p χ)} (hf : f ≠ 0) :
    ∀ i, IsLocallyConstant (χ i) := by
  have hex : ∃ g₀ : G, (f : G → ℂ) g₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (Subtype.ext (funext h))
  obtain ⟨g₀, hg₀⟩ := hex
  obtain ⟨hlc, -, ht⟩ := mem_principalSeries2_iff.mp f.2
  have hL : IsLocallyConstant fun a : Fˣ => (f : G → ℂ) (diagonal2 p ![a, 1] * g₀) :=
    hlc.comp_continuous (((continuous_diagonal2 p).comp (continuous_vec2_left p)).mul continuous_const)
  have hR : IsLocallyConstant fun a : Fˣ => (f : G → ℂ) (diagonal2 p ![1, a] * g₀) :=
    hlc.comp_continuous (((continuous_diagonal2 p).comp (continuous_vec2_right p)).mul continuous_const)
  have h0 : IsLocallyConstant (χ 0) :=
    isLocallyConstant_char_of p hg₀ (fun a => halfModulus2_ne_zero p _) (isLocallyConstant_halfModulus2_left p)
      hL (fun a => by
        show (f : G → ℂ) (diagonal2 p ![a, 1] * g₀) = _
        rw [ht, torusChar2_left])
  have h1 : IsLocallyConstant (χ 1) :=
    isLocallyConstant_char_of p hg₀ (fun a => halfModulus2_ne_zero p _) (isLocallyConstant_halfModulus2_right p)
      hR (fun a => by
        show (f : G → ℂ) (diagonal2 p ![1, a] * g₀) = _
        rw [ht, torusChar2_right])
  intro i
  fin_cases i
  · exact h0
  · exact h1

theorem isLocallyConstant_chi_of_V0_ne_bot (hne : V0 p χ ≠ ⊥) : ∀ i, IsLocallyConstant (χ i) := by
  obtain ⟨f, -, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact isLocallyConstant_chi_of_ne_zero p hf

section Indicators

variable (χ)
variable (hχ : ∀ i, IsLocallyConstant (χ i))

def sVec : ↥(principalSeries2 p χ) := ⟨cellSection2 p χ, cellSection2_mem_principalSeries2 p χ hχ⟩

theorem sVec_coe : ((sVec p χ hχ : ↥(principalSeries2 p χ)) : G → ℂ) = cellSection2 p χ := rfl

theorem cellSection2_weyl_upper (y : F) :
    cellSection2 p χ (antidiagonal2 p * upperUnipotent2 p y)
      = if Valued.v y ≤ 1 then (((χ 0 (-1) : ℂˣ) : ℂ)) else 0 := by
  have hcorner : cornerEntry2 p (antidiagonal2 p * upperUnipotent2 p y) = 1 := by
    simp only [cornerEntry2, gl2Entry]
    rw [coe_weyl_upper]
    simp
  have h11 : gl2Entry p (antidiagonal2 p * upperUnipotent2 p y) 1 1 = y := by
    simp only [gl2Entry]
    rw [coe_weyl_upper]
    simp
  have hdet : gl2Det p (antidiagonal2 p * upperUnipotent2 p y) = -1 := by
    simp only [gl2Det]
    rw [coe_weyl_upper, Matrix.det_fin_two_of]
    ring
  have hmem : antidiagonal2 p * upperUnipotent2 p y ∈ cellCutoff2 p ↔ Valued.v y ≤ 1 := by
    simp only [cellCutoff2, Set.mem_setOf_eq, hcorner, h11, ne_eq, one_ne_zero, not_false_eq_true, div_one,
      true_and]
  by_cases hy : Valued.v y ≤ 1
  · rw [if_pos hy, cellSection2, Set.indicator_of_mem (hmem.mpr hy)]
    have h0 : charExt (χ 0) (-1 : F) = ((χ 0 (-1) : ℂˣ) : ℂ) := by
      simpa using charExt_coe_units (χ 0) (-1)
    have h1 : charExt (χ 1) (1 : F) = ((χ 1 1 : ℂˣ) : ℂ) := by
      simpa using charExt_coe_units (χ 1) 1
    simp only [cellValue2, hdet, hcorner, div_one, h0, h1, map_one, Units.val_one, norm_neg, norm_one,
      Real.sqrt_one, Complex.ofReal_one, mul_one]
  · rw [if_neg hy, cellSection2, Set.indicator_of_notMem (fun h => hy (hmem.mp h))]

theorem phi_sVec (y : F) :
    phi p χ (sVec p χ hχ) y = if Valued.v y ≤ 1 then (((χ 0 (-1) : ℂˣ) : ℂ)) else 0 :=
  cellSection2_weyl_upper p χ y

def dElt (k : ℤ) : G := diagonal2 p ![1, varpi p ^ (-k)]

def eVec (k : ℤ) : ↥(principalSeries2 p χ) := principalSeries2Rep χ (dElt p k) (sVec p χ hχ)

def cst (k : ℤ) : ℂ :=
  torusChar2 p χ ![varpi p ^ (-k), 1] * halfModulus2 p ![varpi p ^ (-k), 1] * ((χ 0 (-1) : ℂˣ) : ℂ)

theorem cst_ne_zero (k : ℤ) : cst p χ k ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero ?_ (halfModulus2_ne_zero p _)) (Units.ne_zero _)
  simp only [torusChar2]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => Units.ne_zero _

theorem phi_eVec (k : ℤ) (y : F) :
    phi p χ (eVec p χ hχ k) y = if ‖y‖ ≤ qR p ^ (-k) then cst p χ k else 0 := by
  unfold phi eVec dElt
  rw [rho_apply, weyl_upper_mul_diagonal2]
  obtain ⟨-, -, ht⟩ := mem_principalSeries2_iff.mp (sVec p χ hχ).2
  rw [ht, sVec_coe, cellSection2_weyl_upper]
  by_cases hy : ‖y‖ ≤ qR p ^ (-k)
  · rw [if_pos hy, if_pos ((norm_le_zpow_iff_valued p k y).mp hy)]
    rfl
  · rw [if_neg hy, if_neg (fun h => hy ((norm_le_zpow_iff_valued p k y).mpr h)), mul_zero]

def ind0 (k : ℤ) : ↥(principalSeries2 p χ) := (cst p χ k)⁻¹ • eVec p χ hχ k

theorem phi_ind0 (k : ℤ) (y : F) :
    phi p χ (ind0 p χ hχ k) y = if ‖y‖ ≤ qR p ^ (-k) then 1 else 0 := by
  unfold ind0
  rw [phi_smul, phi_eVec]
  by_cases hy : ‖y‖ ≤ qR p ^ (-k)
  · rw [if_pos hy, if_pos hy, inv_mul_cancel₀ (cst_ne_zero p χ k)]
  · rw [if_neg hy, if_neg hy, mul_zero]

def ind (a : F) (k : ℤ) : ↥(principalSeries2 p χ) :=
  principalSeries2Rep χ (upperUnipotent2 p (-a)) (ind0 p χ hχ k)

theorem phi_ind (a : F) (k : ℤ) (y : F) :
    phi p χ (ind p χ hχ a k) y = if ‖y - a‖ ≤ qR p ^ (-k) then 1 else 0 := by
  unfold ind
  rw [phi_rho_upper, phi_ind0, ← sub_eq_add_neg]

theorem ind_zero (k : ℤ) : ind p χ hχ 0 k = ind0 p χ hχ k := by
  unfold ind
  rw [neg_zero, upperUnipotent2_zero, rho_one]

theorem cellSection2_one : cellSection2 p χ (1 : G) = 0 := by
  rw [cellSection2, Set.indicator_of_notMem]
  intro h
  exact h.1 (by simp [cornerEntry2, gl2Entry])

theorem eVec_mem_V0 (k : ℤ) : eVec p χ hχ k ∈ V0 p χ := by
  rw [mem_V0_iff]
  unfold eVec dElt
  rw [rho_apply, one_mul, sVec_coe]
  obtain ⟨-, -, ht⟩ := mem_principalSeries2_iff.mp (sVec p χ hχ).2
  have := ht ![1, varpi p ^ (-k)] 1
  rw [mul_one, sVec_coe] at this
  rw [this, cellSection2_one, mul_zero]

theorem ind0_mem_V0 (k : ℤ) : ind0 p χ hχ k ∈ V0 p χ :=
  (V0 p χ).smul_mem _ (eVec_mem_V0 p χ hχ k)

theorem ind_mem_V0 (a : F) (k : ℤ) : ind p χ hχ a k ∈ V0 p χ :=
  rho_upper_mem_V0 p χ (ind0_mem_V0 p χ hχ k) (-a)

theorem ind0_ne_zero (k : ℤ) : ind0 p χ hχ k ≠ 0 := by
  intro h
  have := phi_ind0 p χ hχ k 0
  rw [h, phi_zero, norm_zero, if_pos (le_of_lt (qR_zpow_pos p (-k)))] at this
  exact zero_ne_one this

theorem apply_ind {ψ : AddChar F ℂ} {ℓ : ↥(principalSeries2 p χ) →ₗ[ℂ] ℂ} (hw : IsWhitt p χ ψ ℓ)
    (a : F) (k : ℤ) : ℓ (ind p χ hχ a k) = ψ (-a) * ℓ (ind0 p χ hχ k) :=
  hw (-a) _

theorem phi_ind0_add_of_le {m k : ℤ} (hmk : m ≤ k) (x y : F) (hy : ‖y‖ ≤ qR p ^ (-k)) :
    phi p χ (ind0 p χ hχ m) (x + y) = phi p χ (ind0 p χ hχ m) x := by
  have hy' : ‖y‖ ≤ qR p ^ (-m) :=
    le_trans hy (zpow_le_zpow_right₀ (le_of_lt (one_lt_qR p)) (neg_le_neg hmk))
  rw [phi_ind0, phi_ind0]
  exact if_congr (norm_add_le_iff_of_norm_le p hy') rfl rfl

theorem apply_eq_zero_of_forall_apply_ind_eq_zero {ℓ : ↥(principalSeries2 p χ) →ₗ[ℂ] ℂ} {k : ℤ}
    (hc0 : ∀ a : F, ℓ (ind p χ hχ a k) = 0) :
    ∀ (T : Finset F) (f : ↥(principalSeries2 p χ)), f ∈ V0 p χ →
      (∀ x y : F, ‖y‖ ≤ qR p ^ (-k) → phi p χ f (x + y) = phi p χ f x) →
      (∀ x, phi p χ f x ≠ 0 → ∃ a ∈ T, ‖x - a‖ ≤ qR p ^ (-k)) →
      ℓ f = 0 := by
  intro T
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro f hf _ hsupp
    have hphi : ∀ x, phi p χ f x = 0 := by
      intro x
      by_contra h
      obtain ⟨a, ha, _⟩ := hsupp x h
      exact absurd ha (Finset.notMem_empty a)
    rw [eq_zero_of_mem_V0_of_phi_eq_zero p χ hf hphi, map_zero]
  | insert a T ha ih =>
    intro f hf hconst hsupp
    set f' : ↥(principalSeries2 p χ) := f - phi p χ f a • ind p χ hχ a k with hf'def
    have hphi' : ∀ x, phi p χ f' x
        = phi p χ f x - phi p χ f a * (if ‖x - a‖ ≤ qR p ^ (-k) then (1 : ℂ) else 0) := by
      intro x
      rw [hf'def, phi_sub, phi_smul, phi_ind]
    have hf'mem : f' ∈ V0 p χ :=
      Submodule.sub_mem _ hf (Submodule.smul_mem _ _ (ind_mem_V0 p χ hχ a k))
    have hconst' : ∀ x y : F, ‖y‖ ≤ qR p ^ (-k) → phi p χ f' (x + y) = phi p χ f' x := by
      intro x y hy
      rw [hphi', hphi', hconst x y hy]
      congr 1
      congr 1
      exact if_congr (norm_sub_add_le_iff_of_norm_le p hy) rfl rfl
    have hsupp' : ∀ x, phi p χ f' x ≠ 0 → ∃ b ∈ T, ‖x - b‖ ≤ qR p ^ (-k) := by
      intro x hx
      by_cases hxa : ‖x - a‖ ≤ qR p ^ (-k)
      · exfalso
        apply hx
        rw [hphi', if_pos hxa]
        have hfx : phi p χ f x = phi p χ f a := by
          have := hconst a (x - a) hxa
          rwa [show a + (x - a) = x by ring] at this
        rw [hfx, mul_one, sub_self]
      · have hfx : phi p χ f' x = phi p χ f x := by
          rw [hphi', if_neg hxa, mul_zero, sub_zero]
        rw [hfx] at hx
        obtain ⟨b, hbmem, hbball⟩ := hsupp x hx
        rcases Finset.mem_insert.mp hbmem with hb | hb
        · exact absurd (hb ▸ hbball) hxa
        · exact ⟨b, hb, hbball⟩
    have hℓf' : ℓ f' = 0 := ih f' hf'mem hconst' hsupp'
    have hexp : ℓ f' = ℓ f - phi p χ f a * ℓ (ind p χ hχ a k) := by
      rw [hf'def, map_sub, map_smul, smul_eq_mul]
    rw [hexp, hc0 a, mul_zero, sub_zero] at hℓf'
    exact hℓf'

theorem exists_apply_eq_natCast_mul {ψ : AddChar F ℂ} {ℓ : ↥(principalSeries2 p χ) →ₗ[ℂ] ℂ}
    (hw : IsWhitt p χ ψ ℓ) {δ : ℝ} (hδ : ∀ y : F, ‖y‖ ≤ δ → ψ y = 1) {k : ℤ} :
    ∀ (T : Finset F) (f : ↥(principalSeries2 p χ)), f ∈ V0 p χ →
      (∀ x y : F, ‖y‖ ≤ qR p ^ (-k) → phi p χ f (x + y) = phi p χ f x) →
      (∀ x, phi p χ f x ≠ 0 → ∃ a ∈ T, ‖x - a‖ ≤ qR p ^ (-k)) →
      (∀ x, phi p χ f x = 0 ∨ phi p χ f x = 1) →
      (∀ x, phi p χ f x ≠ 0 → ‖x‖ ≤ δ) →
      ∃ N : ℕ, ℓ f = N * ℓ (ind0 p χ hχ k) ∧ (f ≠ 0 → N ≠ 0) := by
  intro T
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro f hf _ hsupp _ _
    have hphi : ∀ x, phi p χ f x = 0 := by
      intro x
      by_contra h
      obtain ⟨a, ha, _⟩ := hsupp x h
      exact absurd ha (Finset.notMem_empty a)
    have hf0 := eq_zero_of_mem_V0_of_phi_eq_zero p χ hf hphi
    exact ⟨0, by rw [hf0, map_zero, Nat.cast_zero, zero_mul], fun h => absurd hf0 h⟩
  | insert a T ha ih =>
    intro f hf hconst hsupp h01 hδsupp
    by_cases hfa : phi p χ f a = 0
    ·
      refine ih f hf hconst (fun x hx => ?_) h01 hδsupp
      obtain ⟨b, hbmem, hbball⟩ := hsupp x hx
      rcases Finset.mem_insert.mp hbmem with hb | hb
      · exfalso
        apply hx
        subst hb
        have := hconst b (x - b) hbball
        rw [show b + (x - b) = x by ring] at this
        rw [this, hfa]
      · exact ⟨b, hb, hbball⟩
    · have hfa1 : phi p χ f a = 1 := (h01 a).resolve_left hfa
      set f' : ↥(principalSeries2 p χ) := f - ind p χ hχ a k with hf'def
      have hphi' : ∀ x, phi p χ f' x
          = phi p χ f x - (if ‖x - a‖ ≤ qR p ^ (-k) then (1 : ℂ) else 0) := by
        intro x
        rw [hf'def, phi_sub, phi_ind]
      have hf'mem : f' ∈ V0 p χ := Submodule.sub_mem _ hf (ind_mem_V0 p χ hχ a k)
      have hconst' : ∀ x y : F, ‖y‖ ≤ qR p ^ (-k) → phi p χ f' (x + y) = phi p χ f' x := by
        intro x y hy
        rw [hphi', hphi', hconst x y hy]
        congr 1
        exact if_congr (norm_sub_add_le_iff_of_norm_le p hy) rfl rfl
      have hin : ∀ x, ‖x - a‖ ≤ qR p ^ (-k) → phi p χ f x = 1 := by
        intro x hxa
        have := hconst a (x - a) hxa
        rw [show a + (x - a) = x by ring] at this
        rw [this, hfa1]
      have hphi'val : ∀ x, phi p χ f' x = if ‖x - a‖ ≤ qR p ^ (-k) then 0 else phi p χ f x := by
        intro x
        rw [hphi']
        by_cases hxa : ‖x - a‖ ≤ qR p ^ (-k)
        · rw [if_pos hxa, if_pos hxa, hin x hxa, sub_self]
        · rw [if_neg hxa, if_neg hxa, sub_zero]
      have hsupp' : ∀ x, phi p χ f' x ≠ 0 → ∃ b ∈ T, ‖x - b‖ ≤ qR p ^ (-k) := by
        intro x hx
        rw [hphi'val] at hx
        by_cases hxa : ‖x - a‖ ≤ qR p ^ (-k)
        · rw [if_pos hxa] at hx
          exact absurd rfl hx
        · rw [if_neg hxa] at hx
          obtain ⟨b, hbmem, hbball⟩ := hsupp x hx
          rcases Finset.mem_insert.mp hbmem with hb | hb
          · exact absurd (hb ▸ hbball) hxa
          · exact ⟨b, hb, hbball⟩
      have h01' : ∀ x, phi p χ f' x = 0 ∨ phi p χ f' x = 1 := by
        intro x
        rw [hphi'val]
        by_cases hxa : ‖x - a‖ ≤ qR p ^ (-k)
        · rw [if_pos hxa]
          exact Or.inl rfl
        · rw [if_neg hxa]
          exact h01 x
      have hδsupp' : ∀ x, phi p χ f' x ≠ 0 → ‖x‖ ≤ δ := by
        intro x hx
        rw [hphi'val] at hx
        by_cases hxa : ‖x - a‖ ≤ qR p ^ (-k)
        · rw [if_pos hxa] at hx
          exact absurd rfl hx
        · rw [if_neg hxa] at hx
          exact hδsupp x hx
      obtain ⟨N', hN', -⟩ := ih f' hf'mem hconst' hsupp' h01' hδsupp'
      have haδ : ‖-a‖ ≤ δ := by
        rw [norm_neg]
        exact hδsupp a hfa
      have hexp : ℓ f' = ℓ f - ℓ (ind0 p χ hχ k) := by
        rw [hf'def, map_sub, apply_ind p χ hχ hw, hδ _ haδ, one_mul]
      refine ⟨N' + 1, ?_, fun _ => Nat.succ_ne_zero N'⟩
      rw [hexp] at hN'
      push_cast
      linear_combination hN'

end Indicators

theorem exists_finset_cover (C : ℝ) (k : ℤ) :
    ∃ T : Finset F, ∀ x : F, ‖x‖ ≤ C → ∃ a ∈ T, ‖x - a‖ ≤ qR p ^ (-k) := by
  have hpkpos : (0 : ℝ) < qR p ^ (-k) := qR_zpow_pos p (-k)
  obtain ⟨T, -, hTcov⟩ := (isCompact_closedBall (0 : F) C).elim_nhds_subcover
    (fun a => Metric.closedBall a (qR p ^ (-k)))
    (fun a _ => (IsUltrametricDist.isOpen_closedBall a (ne_of_gt hpkpos)).mem_nhds
      (Metric.mem_closedBall_self (le_of_lt hpkpos)))
  refine ⟨T, fun x hx => ?_⟩
  have hxS : x ∈ Metric.closedBall (0 : F) C := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hx
  have hmem := hTcov hxS
  rw [Set.mem_iUnion₂] at hmem
  obtain ⟨a, haT, hxa⟩ := hmem
  rw [Metric.mem_closedBall, dist_eq_norm] at hxa
  exact ⟨a, haT, hxa⟩

theorem exists_zpow_le {δ : ℝ} (hδ : 0 < δ) : ∃ n : ℕ, qR p ^ (-(n : ℤ)) ≤ δ := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ
    (by rw [inv_lt_one_iff₀]; right; exact one_lt_qR p : (qR p)⁻¹ < 1)
  refine ⟨n, ?_⟩
  rw [_root_.zpow_neg, zpow_natCast, ← inv_pow]
  exact le_of_lt hn

theorem eq_zero_of_apply_ind0_eq_zero {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) {δ : ℝ}
    (hδtriv : ∀ y : F, ‖y‖ ≤ δ → ψ y = 1) (hχ : ∀ i, IsLocallyConstant (χ i))
    {ℓ : ↥(principalSeries2 p χ) →ₗ[ℂ] ℂ} (hw : IsWhitt p χ ψ ℓ)
    {m : ℤ} (hmδ : qR p ^ (-m) ≤ δ)
    (h0 : ℓ (ind0 p χ hχ m) = 0) : ℓ = 0 := by
  refine eq_zero_of_isWhitt_of_forall_V0 p hψ hw fun f hf => ?_
  obtain ⟨δf, hδf, hδfconst⟩ := exists_uniform_scale_phi p χ hf
  obtain ⟨C, hC, hCz⟩ := exists_bound_phi_eq_zero p χ hf
  obtain ⟨n, hn⟩ := exists_zpow_le p hδf
  set k : ℤ := max m n with hkdef
  have hkm : m ≤ k := le_max_left _ _
  have hkδf : qR p ^ (-k) ≤ δf :=
    le_trans (zpow_le_zpow_right₀ (le_of_lt (one_lt_qR p)) (neg_le_neg (le_max_right _ _))) hn

  have hβ : ℓ (ind0 p χ hχ k) = 0 := by
    obtain ⟨T, hT⟩ := exists_finset_cover p (qR p ^ (-m)) k
    obtain ⟨N, hN, hN0⟩ := exists_apply_eq_natCast_mul p χ hχ hw hδtriv T (ind0 p χ hχ m)
      (ind0_mem_V0 p χ hχ m) (fun x y hy => phi_ind0_add_of_le p χ hχ hkm x y hy)
      (fun x hx => by
        refine hT x ?_
        rw [phi_ind0] at hx
        by_contra h
        exact hx (if_neg h))
      (fun x => by
        rw [phi_ind0]
        by_cases h : ‖x‖ ≤ qR p ^ (-m)
        · exact Or.inr (if_pos h)
        · exact Or.inl (if_neg h))
      (fun x hx => by
        rw [phi_ind0] at hx
        by_contra h
        exact hx (if_neg fun h' => h (le_trans h' hmδ)))
    have hN0' := hN0 (ind0_ne_zero p χ hχ m)
    rw [h0] at hN
    have : (N : ℂ) * ℓ (ind0 p χ hχ k) = 0 := hN.symm
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (by exact_mod_cast h) hN0'
    · exact h

  have hc0 : ∀ a : F, ℓ (ind p χ hχ a k) = 0 := by
    intro a
    rw [apply_ind p χ hχ hw, hβ, mul_zero]
  obtain ⟨T, hT⟩ := exists_finset_cover p C k
  refine apply_eq_zero_of_forall_apply_ind_eq_zero p χ hχ hc0 T f hf
    (fun x y hy => hδfconst x y (le_trans hy hkδf)) fun x hx => hT x ?_
  by_contra h
  push Not at h
  exact hx (hCz x h)

variable (χ)

theorem main (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (ℓ₁ ℓ₂ : ↥(principalSeries2 p χ) →ₗ[ℂ] ℂ)
    (h₁ : IsWhitt p χ ψ ℓ₁) (h₂ : IsWhitt p χ ψ ℓ₂) (hne : ℓ₁ ≠ 0) : ∃ c : ℂ, ℓ₂ = c • ℓ₁ := by
  by_cases htame : IsTame p ψ
  · by_cases hV : V0 p χ = ⊥
    · exact absurd (eq_zero_of_isWhitt_of_V0_eq_bot p hψ hV h₁) hne
    · have hχ : ∀ i, IsLocallyConstant (χ i) := isLocallyConstant_chi_of_V0_ne_bot p hV
      obtain ⟨δ, hδpos, hδtriv⟩ := htame
      obtain ⟨n, hn⟩ := exists_zpow_le p hδpos
      set v₀ : ↥(principalSeries2 p χ) := ind0 p χ hχ (n : ℤ) with hv₀
      have hΛ₁ : ℓ₁ v₀ ≠ 0 := fun h0 => hne (eq_zero_of_apply_ind0_eq_zero p hψ hδtriv hχ h₁ hn h0)
      refine ⟨ℓ₂ v₀ / ℓ₁ v₀, ?_⟩
      have hzero : ℓ₂ - (ℓ₂ v₀ / ℓ₁ v₀) • ℓ₁ = 0 := by
        refine eq_zero_of_apply_ind0_eq_zero p hψ hδtriv hχ (h₁.sub p h₂ _) hn ?_
        rw [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hΛ₁, sub_self]
      exact (sub_eq_zero.mp hzero)
  · exact absurd (eq_zero_of_isWhitt_of_not_isTame p htame h₁) hne

end Main

end WhittakerPS2Mult
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul.WhittakerPS2Mult"

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (ψ : AddChar (p.adicCompletion ℚ) ℂ) (hψ : ψ ≠ 1)
    (ℓ₁ ℓ₂ : ↥(principalSeries2 p χ) →ₗ[ℂ] ℂ)
    (hℓ₁ : ∀ (x : p.adicCompletion ℚ) (f : ↥(principalSeries2 p χ)),
      ℓ₁ (principalSeries2Rep χ (upperUnipotent2 p x) f) = ψ x * ℓ₁ f)
    (hℓ₂ : ∀ (x : p.adicCompletion ℚ) (f : ↥(principalSeries2 p χ)),
      ℓ₂ (principalSeries2Rep χ (upperUnipotent2 p x) f) = ψ x * ℓ₂ f)
    (hne : ℓ₁ ≠ 0) :
    ∃ c : ℂ, ℓ₂ = c • ℓ₁ :=
  WhittakerPS2Mult.main p χ ψ hψ ℓ₁ ℓ₂ hℓ₁ hℓ₂ hne

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul.WhittakerPS2Mult"

end S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul (solution)
