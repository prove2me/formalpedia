-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.continuous_and_isGaugeMajorised3_of_eq_mul_prod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/724e0376-9894-59fa-b11b-5b80ebee5cce

import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_continuous_and_isGaugeMajorised3_of_eq_mul_prod

set_option autoImplicit false

open IsDedekindDomain NumberField

section

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "LocalGL3 IsRightInvariant lastRowSup bottomMinor minorSup lastRowEucl minorEucl detSize finRoot₁ finRoot₂ archRoot₁ archRoot₂ rootSizeProd archRootSum InRootLevel IsGaugeMajorised3 AdelicGL localMaximalCompact3 mem_localMaximalCompact3_iff componentAt3 archComponent3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section SizeAlgebra

variable {L : Type*} [NormedField L]

private theorem det_eq_bottomMinor_expansion (k : GL (Fin 3) L) :
    (k : Matrix (Fin 3) (Fin 3) L).det =
      (k : Matrix (Fin 3) (Fin 3) L) 0 0 * bottomMinor k 1 2 - (k : Matrix (Fin 3) (Fin 3) L) 0 1 * bottomMinor k 0 2 +
        (k : Matrix (Fin 3) (Fin 3) L) 0 2 * bottomMinor k 0 1 := by
  rw [Matrix.det_fin_three]
  unfold bottomMinor
  ring

private theorem det_coe_ne_zero (k : GL (Fin 3) L) : (k : Matrix (Fin 3) (Fin 3) L).det ≠ 0 := by
  intro h
  have h1 : ((k : Matrix (Fin 3) (Fin 3) L) * ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)).det = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  rw [Matrix.det_mul, h, zero_mul] at h1
  exact zero_ne_one h1

private theorem detSize_pos (k : GL (Fin 3) L) : 0 < detSize k :=
  norm_pos_iff.mpr (det_coe_ne_zero k)

private theorem norm_entry_le_lastRowSup (k : GL (Fin 3) L) (j : Fin 3) :
    ‖(k : Matrix (Fin 3) (Fin 3) L) 2 j‖ ≤ lastRowSup k := by
  unfold lastRowSup
  fin_cases j
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_max_right _ _

private theorem norm_bottomMinor_le_minorSup (k : GL (Fin 3) L) :
    ‖bottomMinor k 0 1‖ ≤ minorSup k ∧ ‖bottomMinor k 0 2‖ ≤ minorSup k ∧ ‖bottomMinor k 1 2‖ ≤ minorSup k := by
  unfold minorSup
  exact ⟨le_trans (le_max_left _ _) (le_max_left _ _), le_trans (le_max_right _ _) (le_max_left _ _),
    le_max_right _ _⟩

private theorem lastRowSup_pos (k : GL (Fin 3) L) : 0 < lastRowSup k := by
  by_contra hle
  push Not at hle
  have hz : ∀ j : Fin 3, (k : Matrix (Fin 3) (Fin 3) L) 2 j = 0 := fun j =>
    norm_le_zero_iff.mp ((norm_entry_le_lastRowSup k j).trans hle)
  apply det_coe_ne_zero k
  rw [Matrix.det_fin_three, hz 0, hz 1, hz 2]
  ring

private theorem minorSup_pos (k : GL (Fin 3) L) : 0 < minorSup k := by
  by_contra hle
  push Not at hle
  obtain ⟨h01, h02, h12⟩ := norm_bottomMinor_le_minorSup k
  apply det_coe_ne_zero k
  rw [det_eq_bottomMinor_expansion, norm_le_zero_iff.mp (h01.trans hle), norm_le_zero_iff.mp (h02.trans hle),
    norm_le_zero_iff.mp (h12.trans hle)]
  ring

private theorem lastRowSup_le_of_forall_norm_le {k : GL (Fin 3) L} {c : ℝ}
    (hk : ∀ j : Fin 3, ‖(k : Matrix (Fin 3) (Fin 3) L) 2 j‖ ≤ c) : lastRowSup k ≤ c :=
  max_le (max_le (hk 0) (hk 1)) (hk 2)

private theorem bottomMinor_eq_det_mul_inv_entry (k : GL (Fin 3) L) :
    bottomMinor k 1 2 = (k : Matrix (Fin 3) (Fin 3) L).det * ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 0 0 ∧
      bottomMinor k 0 2 =
        -((k : Matrix (Fin 3) (Fin 3) L).det * ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 1 0) ∧
      bottomMinor k 0 1 =
        (k : Matrix (Fin 3) (Fin 3) L).det * ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 2 0 := by
  have hadj : Matrix.adjugate (k : Matrix (Fin 3) (Fin 3) L) =
      (k : Matrix (Fin 3) (Fin 3) L).det • ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) := by
    calc Matrix.adjugate (k : Matrix (Fin 3) (Fin 3) L)
        = (((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) * (k : Matrix (Fin 3) (Fin 3) L)) *
            Matrix.adjugate (k : Matrix (Fin 3) (Fin 3) L) := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
      _ = ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) *
            ((k : Matrix (Fin 3) (Fin 3) L).det • (1 : Matrix (Fin 3) (Fin 3) L)) := by
          rw [Matrix.mul_assoc, Matrix.mul_adjugate]
      _ = (k : Matrix (Fin 3) (Fin 3) L).det • ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) := by
          rw [Matrix.mul_smul, Matrix.mul_one]
  have h00 := congrFun (congrFun hadj 0) 0
  have h10 := congrFun (congrFun hadj 1) 0
  have h20 := congrFun (congrFun hadj 2) 0
  simp only [Matrix.adjugate_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.smul_apply, smul_eq_mul] at h00 h10 h20
  refine ⟨?_, ?_, ?_⟩
  · unfold bottomMinor; linear_combination h00
  · unfold bottomMinor; linear_combination -h10
  · unfold bottomMinor; linear_combination h20

end SizeAlgebra

section IntegralSizes

variable {L : Type*} [NormedField L]

private theorem norm_add3_le_of_le (hult : ∀ x y : L, ‖x + y‖ ≤ max ‖x‖ ‖y‖) {x y z : L} {c : ℝ}
    (hx : ‖x‖ ≤ c) (hy : ‖y‖ ≤ c) (hz : ‖z‖ ≤ c) : ‖x + y + z‖ ≤ c :=
  (hult _ _).trans (max_le ((hult _ _).trans (max_le hx hy)) hz)

private theorem eq_one_of_dot_eq_one (hult : ∀ x y : L, ‖x + y‖ ≤ max ‖x‖ ‖y‖) {a₀ a₁ a₂ b₀ b₁ b₂ : L} {c : ℝ}
    (h : a₀ * b₀ + a₁ * b₁ + a₂ * b₂ = 1) (hb₀ : ‖b₀‖ ≤ 1) (hb₁ : ‖b₁‖ ≤ 1) (hb₂ : ‖b₂‖ ≤ 1)
    (ha₀ : ‖a₀‖ ≤ c) (ha₁ : ‖a₁‖ ≤ c) (ha₂ : ‖a₂‖ ≤ c) (hc : c ≤ 1) : c = 1 := by
  refine le_antisymm hc ?_
  have hterm : ∀ {a b : L}, ‖a‖ ≤ c → ‖b‖ ≤ 1 → ‖a * b‖ ≤ c := fun {a b} ha hb => by
    rw [norm_mul]
    calc ‖a‖ * ‖b‖ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left hb (norm_nonneg a)
      _ = ‖a‖ := mul_one _
      _ ≤ c := ha
  have := norm_add3_le_of_le hult (hterm ha₀ hb₀) (hterm ha₁ hb₁) (hterm ha₂ hb₂)
  rwa [h, norm_one] at this

variable (hult : ∀ x y : L, ‖x + y‖ ≤ max ‖x‖ ‖y‖) (k : GL (Fin 3) L)
  (hk : ∀ i j : Fin 3, ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ 1)
  (hk' : ∀ i j : Fin 3, ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ 1)
include hult hk hk'

private theorem lastRowSup_eq_one_of_integral : lastRowSup k = 1 := by
  have hdot : (k : Matrix (Fin 3) (Fin 3) L) 2 0 * ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 0 2 +
      (k : Matrix (Fin 3) (Fin 3) L) 2 1 * ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 1 2 +
      (k : Matrix (Fin 3) (Fin 3) L) 2 2 * ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 2 2 = 1 := by
    have h := congrFun (congrFun (Units.mul_inv k) 2) 2
    rw [Matrix.mul_apply, Fin.sum_univ_three] at h
    simp only [Matrix.one_apply_eq] at h
    linear_combination h
  exact eq_one_of_dot_eq_one hult hdot (hk' 0 2) (hk' 1 2) (hk' 2 2) (norm_entry_le_lastRowSup k 0)
    (norm_entry_le_lastRowSup k 1) (norm_entry_le_lastRowSup k 2)
    (lastRowSup_le_of_forall_norm_le fun j => hk 2 j)

private theorem detSize_eq_one_of_integral : detSize k = 1 := by
  have hdet_le : ∀ (m : GL (Fin 3) L), (∀ i j : Fin 3, ‖(m : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ 1) →
      ‖(m : Matrix (Fin 3) (Fin 3) L).det‖ ≤ 1 := by
    intro m hm
    have hmul3 : ∀ i₀ j₀ i₁ j₁ i₂ j₂ : Fin 3,
        ‖(m : Matrix (Fin 3) (Fin 3) L) i₀ j₀ * (m : Matrix (Fin 3) (Fin 3) L) i₁ j₁ *
          (m : Matrix (Fin 3) (Fin 3) L) i₂ j₂‖ ≤ 1 := by
      intro i₀ j₀ i₁ j₁ i₂ j₂
      rw [norm_mul, norm_mul]
      exact mul_le_one₀ (mul_le_one₀ (hm _ _) (norm_nonneg _) (hm _ _)) (norm_nonneg _) (hm _ _)
    have hsub : ∀ {x y : L}, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖x - y‖ ≤ 1 := fun {x y} hx hy => by
      rw [sub_eq_add_neg]
      exact (hult _ _).trans (max_le hx (by rwa [norm_neg]))
    have hadd : ∀ {x y : L}, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖x + y‖ ≤ 1 := fun {x y} hx hy => (hult _ _).trans (max_le hx hy)
    rw [Matrix.det_fin_three]
    exact hsub (hadd (hadd (hsub (hsub (hmul3 _ _ _ _ _ _) (hmul3 _ _ _ _ _ _)) (hmul3 _ _ _ _ _ _))
      (hmul3 _ _ _ _ _ _)) (hmul3 _ _ _ _ _ _)) (hmul3 _ _ _ _ _ _)
  have hprod : (k : Matrix (Fin 3) (Fin 3) L).det * ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have h1 : ‖(k : Matrix (Fin 3) (Fin 3) L).det‖ * ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det‖ = 1 := by
    rw [← norm_mul, hprod, norm_one]
  refine le_antisymm (hdet_le k hk) ?_
  calc (1 : ℝ)
      = ‖(k : Matrix (Fin 3) (Fin 3) L).det‖ * ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det‖ := h1.symm
    _ ≤ ‖(k : Matrix (Fin 3) (Fin 3) L).det‖ * 1 :=
        mul_le_mul_of_nonneg_left (hdet_le k⁻¹ hk') (norm_nonneg _)
    _ = detSize k := mul_one _

private theorem minorSup_eq_one_of_integral : minorSup k = 1 := by
  obtain ⟨h12, h02, h01⟩ := bottomMinor_eq_det_mul_inv_entry k
  have hdet : ‖(k : Matrix (Fin 3) (Fin 3) L).det‖ = 1 := detSize_eq_one_of_integral hult k hk hk'

  have n12 : ‖bottomMinor k 1 2‖ = ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 0 0‖ := by
    rw [h12, norm_mul, hdet, one_mul]
  have n02 : ‖bottomMinor k 0 2‖ = ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 1 0‖ := by
    rw [h02, norm_neg, norm_mul, hdet, one_mul]
  have n01 : ‖bottomMinor k 0 1‖ = ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 2 0‖ := by
    rw [h01, norm_mul, hdet, one_mul]

  have hdot : ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 0 0 * (k : Matrix (Fin 3) (Fin 3) L) 0 0 +
      ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 1 0 * (k : Matrix (Fin 3) (Fin 3) L) 0 1 +
      ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 2 0 * (k : Matrix (Fin 3) (Fin 3) L) 0 2 = 1 := by
    have h := congrFun (congrFun (Units.mul_inv k) 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_three] at h
    simp only [Matrix.one_apply_eq] at h
    linear_combination h
  obtain ⟨m01, m02, m12⟩ := norm_bottomMinor_le_minorSup k
  rw [n01] at m01; rw [n02] at m02; rw [n12] at m12
  have hle : minorSup k ≤ 1 := by
    unfold minorSup
    rw [n01, n02, n12]
    exact max_le (max_le (hk' 2 0) (hk' 1 0)) (hk' 0 0)
  exact eq_one_of_dot_eq_one hult hdot (hk 0 0) (hk 0 1) (hk 0 2) m12 m02 m01 hle

private theorem rootSizes_eq_one_of_integral :
    detSize k * lastRowSup k / minorSup k ^ 2 = 1 ∧ minorSup k / lastRowSup k ^ 2 = 1 := by
  rw [detSize_eq_one_of_integral hult k hk hk', lastRowSup_eq_one_of_integral hult k hk hk',
    minorSup_eq_one_of_integral hult k hk hk']
  norm_num

end IntegralSizes

section LocalPlace

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem norm_add_le_max_adicCompletion (x y : v.adicCompletion ℚ) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  rcases le_total (Valued.v x) (Valued.v y) with hxy | hxy
  · refine le_trans ?_ (le_max_right _ _)
    exact Valued.toNormedField.norm_le_iff.mpr ((Valuation.map_add Valued.v x y).trans (max_eq_right hxy).le)
  · refine le_trans ?_ (le_max_left _ _)
    exact Valued.toNormedField.norm_le_iff.mpr ((Valuation.map_add Valued.v x y).trans (max_eq_left hxy).le)

private theorem norm_entries_le_one_of_mem_localMaximalCompact3 {k : GL (Fin 3) (v.adicCompletion ℚ)}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    (∀ i j : Fin 3, ‖(k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j‖ ≤ 1) ∧
      ∀ i j : Fin 3,
        ‖((k⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j‖ ≤ 1 :=
  ⟨fun i j => Valued.toNormedField.norm_le_one_iff.mpr (hk.1 i j),
    fun i j => Valued.toNormedField.norm_le_one_iff.mpr (hk.2 i j)⟩

private theorem rootSizes_eq_one_of_mem_localMaximalCompact3 {k : GL (Fin 3) (v.adicCompletion ℚ)}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    detSize k * lastRowSup k / minorSup k ^ 2 = 1 ∧ minorSup k / lastRowSup k ^ 2 = 1 :=
  rootSizes_eq_one_of_integral (norm_add_le_max_adicCompletion v) k
    (norm_entries_le_one_of_mem_localMaximalCompact3 v hk).1 (norm_entries_le_one_of_mem_localMaximalCompact3 v hk).2

end LocalPlace

end LanglandsTunnell.CubicInduction

end
end

section

open IsDedekindDomain NumberField

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "LocalGL3 IsRightInvariant lastRowSup bottomMinor minorSup lastRowEucl minorEucl detSize finRoot₁ finRoot₂ archRoot₁ archRoot₂ rootSizeProd archRootSum InRootLevel IsGaugeMajorised3 AdelicGL localMaximalCompact3 mem_localMaximalCompact3_iff componentAt3 archComponent3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section EuclSizes

variable {L : Type*} [NormedField L]

private theorem le_sqrt_sq_add₁ (a b c : ℝ) : a ≤ Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) :=
  (le_abs_self a).trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg b, sq_nonneg c]))

private theorem le_sqrt_sq_add₂ (a b c : ℝ) : b ≤ Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) :=
  (le_abs_self b).trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg a, sq_nonneg c]))

private theorem le_sqrt_sq_add₃ (a b c : ℝ) : c ≤ Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) :=
  (le_abs_self c).trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg a, sq_nonneg b]))

private theorem lastRowSup_le_lastRowEucl (k : GL (Fin 3) L) : lastRowSup k ≤ lastRowEucl k := by
  unfold lastRowSup lastRowEucl
  exact max_le (max_le (le_sqrt_sq_add₁ _ _ _) (le_sqrt_sq_add₂ _ _ _)) (le_sqrt_sq_add₃ _ _ _)

private theorem minorSup_le_minorEucl (k : GL (Fin 3) L) : minorSup k ≤ minorEucl k := by
  unfold minorSup minorEucl
  exact max_le (max_le (le_sqrt_sq_add₁ _ _ _) (le_sqrt_sq_add₂ _ _ _)) (le_sqrt_sq_add₃ _ _ _)

private theorem lastRowEucl_pos (k : GL (Fin 3) L) : 0 < lastRowEucl k :=
  (lastRowSup_pos k).trans_le (lastRowSup_le_lastRowEucl k)

private theorem minorEucl_pos (k : GL (Fin 3) L) : 0 < minorEucl k :=
  (minorSup_pos k).trans_le (minorSup_le_minorEucl k)

end EuclSizes

section ArchRoots

variable (F : Type) [Field F] [NumberField F]

private theorem archRoot₁_pos (w : InfinitePlace F) (g : AdelicGL 3 (𝓞 F) F) : 0 < archRoot₁ F w g := by
  unfold archRoot₁
  exact div_pos (mul_pos (detSize_pos _) (lastRowEucl_pos _)) (pow_pos (minorEucl_pos _) 2)

private theorem archRoot₂_pos (w : InfinitePlace F) (g : AdelicGL 3 (𝓞 F) F) : 0 < archRoot₂ F w g := by
  unfold archRoot₂
  exact div_pos (minorEucl_pos _) (pow_pos (lastRowEucl_pos _) 2)

private theorem archRootSum_nonneg (g : AdelicGL 3 (𝓞 F) F) : 0 ≤ archRootSum F g := by
  unfold archRootSum
  exact Finset.sum_nonneg fun w _ => (add_pos (archRoot₁_pos F w g) (archRoot₂_pos F w g)).le

private theorem archRoot₁_le_archRootSum (w : InfinitePlace F) (g : AdelicGL 3 (𝓞 F) F) :
    archRoot₁ F w g ≤ archRootSum F g := by
  unfold archRootSum
  exact (le_add_of_nonneg_right (archRoot₂_pos F w g).le).trans
    (Finset.single_le_sum (fun w _ => (add_pos (archRoot₁_pos F w g) (archRoot₂_pos F w g)).le) (Finset.mem_univ w))

private theorem archRoot₂_le_archRootSum (w : InfinitePlace F) (g : AdelicGL 3 (𝓞 F) F) :
    archRoot₂ F w g ≤ archRootSum F g := by
  unfold archRootSum
  exact (le_add_of_nonneg_left (archRoot₁_pos F w g).le).trans
    (Finset.single_le_sum (fun w _ => (add_pos (archRoot₁_pos F w g) (archRoot₂_pos F w g)).le) (Finset.mem_univ w))

private theorem prod_archRoots_pos (g : AdelicGL 3 (𝓞 F) F) :
    0 < ∏ w : InfinitePlace F, archRoot₁ F w g * archRoot₂ F w g :=
  Finset.prod_pos fun w _ => mul_pos (archRoot₁_pos F w g) (archRoot₂_pos F w g)

private theorem prod_archRoots_le (g : AdelicGL 3 (𝓞 F) F) :
    ∏ w : InfinitePlace F, archRoot₁ F w g * archRoot₂ F w g ≤
      (1 + archRootSum F g) ^ (2 * Fintype.card (InfinitePlace F)) := by
  have hs : 0 ≤ archRootSum F g := archRootSum_nonneg F g
  calc ∏ w : InfinitePlace F, archRoot₁ F w g * archRoot₂ F w g
      ≤ ∏ _w : InfinitePlace F, (1 + archRootSum F g) ^ 2 := by
        refine Finset.prod_le_prod (fun w _ => (mul_pos (archRoot₁_pos F w g) (archRoot₂_pos F w g)).le) fun w _ => ?_
        rw [sq]
        exact mul_le_mul ((archRoot₁_le_archRootSum F w g).trans (le_add_of_nonneg_left zero_le_one))
          ((archRoot₂_le_archRootSum F w g).trans (le_add_of_nonneg_left zero_le_one)) (archRoot₂_pos F w g).le
          (by linarith)
    _ = (1 + archRootSum F g) ^ (2 * Fintype.card (InfinitePlace F)) := by
        rw [Finset.prod_const, Finset.card_univ, ← pow_mul]

end ArchRoots

section Conversions

private theorem le_abs_mul_pow_div_pow_of_le_div_pow {x C ρ M : ℝ} {t₀ t : ℕ} (hρ : 0 < ρ) (hM : 0 < M) (hρM : ρ ≤ M)
    (ht : t₀ ≤ t) (hx : x ≤ C / ρ ^ t₀) : x ≤ |C| * M ^ (t - t₀) / ρ ^ t := by
  obtain ⟨d, rfl⟩ : ∃ d, t = t₀ + d := ⟨t - t₀, (Nat.add_sub_of_le ht).symm⟩
  rw [Nat.add_sub_cancel_left]
  have hpow : ρ ^ (t₀ + d) ≤ ρ ^ t₀ * M ^ d := by
    rw [pow_add]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ.le hρM d) (pow_nonneg hρ.le _)
  calc x ≤ C / ρ ^ t₀ := hx
    _ ≤ |C| / ρ ^ t₀ := div_le_div_of_nonneg_right (le_abs_self C) (pow_pos hρ _).le
    _ = |C| * M ^ d / (ρ ^ t₀ * M ^ d) := by rw [mul_div_mul_right _ _ (pow_pos hM _).ne']
    _ ≤ |C| * M ^ d / ρ ^ (t₀ + d) :=
        div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg C) (pow_nonneg hM.le _)) (pow_pos hρ _) hpow

private theorem le_abs_div_pow_mul_pow_of_le_div {x C ρ s : ℝ} {e t₀ t N : ℕ} (hρ : 0 < ρ) (hs : 0 ≤ s)
    (hρs : ρ ≤ (1 + s) ^ e) (ht : t₀ ≤ t) (hx : x ≤ C / (ρ ^ t₀ * (1 + s) ^ (N + e * (t - t₀)))) :
    x ≤ |C| / (ρ ^ t * (1 + s) ^ N) := by
  have h1s : 0 < 1 + s := by linarith
  obtain ⟨d, rfl⟩ : ∃ d, t = t₀ + d := ⟨t - t₀, (Nat.add_sub_of_le ht).symm⟩
  rw [Nat.add_sub_cancel_left] at hx
  have hden : ρ ^ (t₀ + d) * (1 + s) ^ N ≤ ρ ^ t₀ * (1 + s) ^ (N + e * d) := by
    calc ρ ^ (t₀ + d) * (1 + s) ^ N = ρ ^ t₀ * ρ ^ d * (1 + s) ^ N := by rw [pow_add]
      _ ≤ ρ ^ t₀ * ((1 + s) ^ e) ^ d * (1 + s) ^ N := by
            gcongr
      _ = ρ ^ t₀ * (1 + s) ^ (N + e * d) := by rw [← pow_mul]; ring
  calc x ≤ C / (ρ ^ t₀ * (1 + s) ^ (N + e * d)) := hx
    _ ≤ |C| / (ρ ^ t₀ * (1 + s) ^ (N + e * d)) :=
        div_le_div_of_nonneg_right (le_abs_self C) (mul_pos (pow_pos hρ _) (pow_pos h1s _)).le
    _ ≤ |C| / (ρ ^ (t₀ + d) * (1 + s) ^ N) :=
        div_le_div_of_nonneg_left (abs_nonneg C) (mul_pos (pow_pos hρ _) (pow_pos h1s _)) hden

end Conversions

end LanglandsTunnell.CubicInduction

end
end

section

open IsDedekindDomain NumberField

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "LocalGL3 IsRightInvariant lastRowSup bottomMinor minorSup lastRowEucl minorEucl detSize finRoot₁ finRoot₂ archRoot₁ archRoot₂ rootSizeProd archRootSum InRootLevel IsGaugeMajorised3 AdelicGL localMaximalCompact3 mem_localMaximalCompact3_iff componentAt3 archComponent3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section CofiniteIntegrality

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

private def nonIntegralPlaces (x : AdeleRing R K) : Set (HeightOneSpectrum R) :=
  {v | ¬ Valued.v (AdelicLevel.adeleFin R K x v) ≤ 1}

private theorem nonIntegralPlaces_finite (x : AdeleRing R K) : (nonIntegralPlaces R K x).Finite := by
  unfold nonIntegralPlaces
  refine Filter.eventually_cofinite.mp ((AdelicLevel.adeleFin R K x).2.mono fun v hv => ?_)
  exact (HeightOneSpectrum.mem_adicCompletionIntegers R K v).mp hv

variable {R K}

private theorem coe_componentAt3_apply (v : HeightOneSpectrum R) (g : AdelicGL 3 R K) (i j : Fin 3) :
    ((componentAt3 R K v g : GL (Fin 3) (v.adicCompletion K)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j =
      AdelicLevel.adeleFin R K ((g : Matrix (Fin 3) (Fin 3) (AdeleRing R K)) i j) v :=
  rfl

private theorem coe_componentAt3_inv_apply (v : HeightOneSpectrum R) (g : AdelicGL 3 R K) (i j : Fin 3) :
    (((componentAt3 R K v g)⁻¹ : GL (Fin 3) (v.adicCompletion K)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j =
      AdelicLevel.adeleFin R K (((g⁻¹ : AdelicGL 3 R K) : Matrix (Fin 3) (Fin 3) (AdeleRing R K)) i j) v := by
  rw [← map_inv]
  exact coe_componentAt3_apply v g⁻¹ i j

private def nonIntegralPlacesGL (g : AdelicGL 3 R K) : Set (HeightOneSpectrum R) :=
  ⋃ i : Fin 3, ⋃ j : Fin 3,
    nonIntegralPlaces R K ((g : Matrix (Fin 3) (Fin 3) (AdeleRing R K)) i j) ∪
      nonIntegralPlaces R K (((g⁻¹ : AdelicGL 3 R K) : Matrix (Fin 3) (Fin 3) (AdeleRing R K)) i j)

private theorem nonIntegralPlacesGL_finite (g : AdelicGL 3 R K) : (nonIntegralPlacesGL g).Finite :=
  Set.finite_iUnion fun _ => Set.finite_iUnion fun _ =>
    (nonIntegralPlaces_finite R K _).union (nonIntegralPlaces_finite R K _)

private theorem componentAt3_mem_localMaximalCompact3_of_notMem (g : AdelicGL 3 R K) {v : HeightOneSpectrum R}
    (hv : v ∉ nonIntegralPlacesGL g) : componentAt3 R K v g ∈ localMaximalCompact3 R K v := by
  unfold nonIntegralPlacesGL at hv
  rw [mem_localMaximalCompact3_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · by_contra h
    rw [coe_componentAt3_apply] at h
    exact hv (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, Or.inl h⟩⟩)
  · by_contra h
    rw [coe_componentAt3_inv_apply] at h
    exact hv (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, Or.inr h⟩⟩)

private theorem exists_finset_componentAt3_mem_localMaximalCompact3 (g : AdelicGL 3 R K) :
    ∃ T : Finset (HeightOneSpectrum R), ∀ v, v ∉ T → componentAt3 R K v g ∈ localMaximalCompact3 R K v :=
  ⟨(nonIntegralPlacesGL_finite g).toFinset, fun _ hv =>
    componentAt3_mem_localMaximalCompact3_of_notMem g fun h => hv ((nonIntegralPlacesGL_finite g).mem_toFinset.mpr h)⟩

end CofiniteIntegrality

end LanglandsTunnell.CubicInduction

end
end

section

open IsDedekindDomain NumberField

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "LocalGL3 IsRightInvariant lastRowSup bottomMinor minorSup lastRowEucl minorEucl detSize finRoot₁ finRoot₂ archRoot₁ archRoot₂ rootSizeProd archRootSum InRootLevel IsGaugeMajorised3 AdelicGL localMaximalCompact3 mem_localMaximalCompact3_iff componentAt3 archComponent3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section IntegralOffFinset

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

private def integralOff (T : Finset (HeightOneSpectrum R)) : Set (FiniteAdeleRing R K) :=
  {a | ∀ v, v ∉ T → a v ∈ v.adicCompletionIntegers K}

private theorem isOpen_integralOff (T : Finset (HeightOneSpectrum R)) : IsOpen (integralOff R K T) :=
  RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : HeightOneSpectrum R => v.adicCompletion K)
    (A := fun v : HeightOneSpectrum R => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    Fact.out (p := fun v => v ∉ T)

private theorem setOf_forall_notMem_componentAt3_mem_eq (T : Finset (HeightOneSpectrum R)) :
    {g : AdelicGL 3 R K | ∀ v, v ∉ T → componentAt3 R K v g ∈ localMaximalCompact3 R K v} =
      ⋂ i : Fin 3, ⋂ j : Fin 3,
        (fun g : AdelicGL 3 R K => AdelicLevel.adeleFin R K ((g : Matrix (Fin 3) (Fin 3) (AdeleRing R K)) i j)) ⁻¹'
            integralOff R K T ∩
          (fun g : AdelicGL 3 R K =>
            AdelicLevel.adeleFin R K (((g⁻¹ : AdelicGL 3 R K) : Matrix (Fin 3) (Fin 3) (AdeleRing R K)) i j)) ⁻¹'
            integralOff R K T := by
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, mem_localMaximalCompact3_iff,
    integralOff, coe_componentAt3_apply, coe_componentAt3_inv_apply, HeightOneSpectrum.mem_adicCompletionIntegers]
  exact ⟨fun h i j => ⟨fun v hv => (h v hv).1 i j, fun v hv => (h v hv).2 i j⟩,
    fun h v hv => ⟨fun i j => (h i j).1 v hv, fun i j => (h i j).2 v hv⟩⟩

private theorem isOpen_setOf_forall_notMem_componentAt3_mem (T : Finset (HeightOneSpectrum R)) :
    IsOpen {g : AdelicGL 3 R K | ∀ v, v ∉ T → componentAt3 R K v g ∈ localMaximalCompact3 R K v} := by
  rw [setOf_forall_notMem_componentAt3_mem_eq]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    ((isOpen_integralOff R K T).preimage ?_).inter ((isOpen_integralOff R K T).preimage ?_)
  · exact (AdelicLevel.continuous_adeleFin R K).comp (Units.continuous_val.matrix_elem i j)
  · exact (AdelicLevel.continuous_adeleFin R K).comp (Units.continuous_coe_inv.matrix_elem i j)

end IntegralOffFinset

end LanglandsTunnell.CubicInduction

end
end

section

open IsDedekindDomain NumberField

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "LocalGL3 IsRightInvariant lastRowSup bottomMinor minorSup lastRowEucl minorEucl detSize finRoot₁ finRoot₂ archRoot₁ archRoot₂ rootSizeProd archRootSum InRootLevel IsGaugeMajorised3 AdelicGL localMaximalCompact3 mem_localMaximalCompact3_iff componentAt3 archComponent3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section ComponentContinuity

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

private theorem continuous_glMap3 {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 3) f) :=
  Continuous.units_map _ ((continuous_id.matrix_map hf) : Continuous fun m : Matrix (Fin 3) (Fin 3) A => m.map f)

private theorem continuous_componentAt3 (v : HeightOneSpectrum R) : Continuous (componentAt3 R K v) :=
  continuous_glMap3 ((AdelicLevel.finAdeleEval R K v).comp (AdelicLevel.adeleFin R K))
    ((AdelicLevel.continuous_finAdeleEval R K v).comp (AdelicLevel.continuous_adeleFin R K))

private theorem continuous_archComponent3 : Continuous (archComponent3 R K) :=
  continuous_glMap3 (AdelicLevel.adeleArch R K) (AdelicLevel.continuous_adeleArch R K)

private theorem isOpen_setOf_valued_le_one (v : HeightOneSpectrum R) :
    IsOpen {y : v.adicCompletion K | Valued.v y ≤ 1} := by
  simpa using AdelicLevel.isOpen_setOf_valued_le (K := K) v (1 : v.adicCompletion K) one_ne_zero

private theorem coe_localMaximalCompact3_eq (v : HeightOneSpectrum R) :
    (localMaximalCompact3 R K v : Set (GL (Fin 3) (v.adicCompletion K))) =
      ⋂ i : Fin 3, ⋂ j : Fin 3,
        (fun k : GL (Fin 3) (v.adicCompletion K) => (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j) ⁻¹'
            {y : v.adicCompletion K | Valued.v y ≤ 1} ∩
          (fun k : GL (Fin 3) (v.adicCompletion K) =>
            ((k⁻¹ : GL (Fin 3) (v.adicCompletion K)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j) ⁻¹'
            {y : v.adicCompletion K | Valued.v y ≤ 1} := by
  ext k
  simp only [SetLike.mem_coe, mem_localMaximalCompact3_iff, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_setOf_eq]
  exact ⟨fun h i j => ⟨h.1 i j, h.2 i j⟩, fun h => ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩⟩

private theorem isOpen_localMaximalCompact3 (v : HeightOneSpectrum R) :
    IsOpen (localMaximalCompact3 R K v : Set (GL (Fin 3) (v.adicCompletion K))) := by
  rw [coe_localMaximalCompact3_eq]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    ((isOpen_setOf_valued_le_one R K v).preimage (Units.continuous_val.matrix_elem i j)).inter
      ((isOpen_setOf_valued_le_one R K v).preimage (Units.continuous_coe_inv.matrix_elem i j))

end ComponentContinuity

section OpenInvariance

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]

private theorem continuous_of_forall_mul_mem_eq (U : Subgroup G) (hU : IsOpen (U : Set G)) (f : G → ℂ)
    (hf : ∀ g : G, ∀ u ∈ U, f (g * u) = f g) : Continuous f := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq f).mpr fun g => ?_)
  have hopen : IsOpen ((fun y : G => g⁻¹ * y) ⁻¹' (U : Set G)) := hU.preimage (continuous_const_mul g⁻¹)
  have hmem : g ∈ (fun y : G => g⁻¹ * y) ⁻¹' (U : Set G) := by simp
  filter_upwards [hopen.mem_nhds hmem] with y hy
  have h := hf g (g⁻¹ * y) hy
  rwa [mul_inv_cancel_left] at h

end OpenInvariance

section FiniteRoots

variable (v : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ)

private theorem finRoot₁_pos : 0 < finRoot₁ ℚ v g := by
  unfold finRoot₁
  exact div_pos (mul_pos (detSize_pos _) (lastRowSup_pos _)) (pow_pos (minorSup_pos _) 2)

private theorem finRoot₂_pos : 0 < finRoot₂ ℚ v g := by
  unfold finRoot₂
  exact div_pos (minorSup_pos _) (pow_pos (lastRowSup_pos _) 2)

private theorem finRoots_eq_one_of_mem (hk : componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    finRoot₁ ℚ v g = 1 ∧ finRoot₂ ℚ v g = 1 := by
  unfold finRoot₁ finRoot₂
  exact rootSizes_eq_one_of_mem_localMaximalCompact3 v hk

variable {v g}

private theorem finRoot_mul_eq_one_of_mem (hk : componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    finRoot₁ ℚ v g * finRoot₂ ℚ v g = 1 := by
  rw [(finRoots_eq_one_of_mem v g hk).1, (finRoots_eq_one_of_mem v g hk).2, one_mul]

private theorem rootSizeProd_eq_prod {T : Finset (HeightOneSpectrum (𝓞 ℚ))}
    (hT : ∀ w, w ∉ T → componentAt3 (𝓞 ℚ) ℚ w g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w) :
    rootSizeProd ℚ g =
      (∏ w ∈ T, finRoot₁ ℚ w g * finRoot₂ ℚ w g) * ∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g := by
  have hsub : Function.mulSupport (fun w => finRoot₁ ℚ w g * finRoot₂ ℚ w g) ⊆
      (T : Set (HeightOneSpectrum (𝓞 ℚ))) := by
    intro w hw
    rw [Function.mem_mulSupport] at hw
    rw [Finset.mem_coe]
    by_contra h
    exact hw (finRoot_mul_eq_one_of_mem (hT w h))
  unfold rootSizeProd
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]

private theorem prod_finRoots_pos (T : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    0 < ∏ w ∈ T, finRoot₁ ℚ w g * finRoot₂ ℚ w g :=
  Finset.prod_pos fun w _ => mul_pos (finRoot₁_pos w g) (finRoot₂_pos w g)

private theorem rootSizeProd_pos {T : Finset (HeightOneSpectrum (𝓞 ℚ))}
    (hT : ∀ w, w ∉ T → componentAt3 (𝓞 ℚ) ℚ w g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w) : 0 < rootSizeProd ℚ g := by
  rw [rootSizeProd_eq_prod hT]
  exact mul_pos (prod_finRoots_pos T) (prod_archRoots_pos ℚ g)

end FiniteRoots

end LanglandsTunnell.CubicInduction

end
end

section

open IsDedekindDomain NumberField

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "LocalGL3 IsRightInvariant lastRowSup bottomMinor minorSup lastRowEucl minorEucl detSize finRoot₁ finRoot₂ archRoot₁ archRoot₂ rootSizeProd archRootSum InRootLevel IsGaugeMajorised3 AdelicGL localMaximalCompact3 mem_localMaximalCompact3_iff componentAt3 archComponent3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Assembly

variable (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (Wloc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
  (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)

private theorem continuous_of_eq_mul_prod
    (hfac : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))), S ⊆ T →
      (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
      W g = Warch (archComponent3 (𝓞 ℚ) ℚ g) * ∏ v ∈ T, Wloc v (componentAt3 (𝓞 ℚ) ℚ v g))
    (hinv : ∀ v, v ∉ S → IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) (Wloc v))
    (hSinv : ∀ v ∈ S, ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, Wloc v (g * k) = Wloc v g)
    (hWarch : Continuous Warch) : Continuous W := by
  classical
  have hloc : ∀ v, Continuous (Wloc v) := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨Uv, hUv, hWU⟩ := hSinv v hv
      exact continuous_of_forall_mul_mem_eq Uv hUv (Wloc v) fun g k hk => hWU k hk g
    · exact continuous_of_forall_mul_mem_eq _ (isOpen_localMaximalCompact3 (𝓞 ℚ) ℚ v) (Wloc v) (hinv v hv)
  rw [continuous_iff_continuousAt]
  intro g₀
  obtain ⟨T₀, hT₀⟩ := exists_finset_componentAt3_mem_localMaximalCompact3 g₀
  have hST : S ⊆ S ∪ T₀ := fun v hv => Finset.mem_union_left T₀ hv
  have hO := isOpen_setOf_forall_notMem_componentAt3_mem (𝓞 ℚ) ℚ (S ∪ T₀)
  have hg₀ : g₀ ∈ {g : AdelicGL 3 (𝓞 ℚ) ℚ |
      ∀ v, v ∉ S ∪ T₀ → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v} :=
    fun v hv => hT₀ v fun h => hv (Finset.mem_union_right S h)
  have hF : Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
      Warch (archComponent3 (𝓞 ℚ) ℚ g) * ∏ v ∈ S ∪ T₀, Wloc v (componentAt3 (𝓞 ℚ) ℚ v g) :=
    (hWarch.comp (continuous_archComponent3 (𝓞 ℚ) ℚ)).mul
      (continuous_finsetProd (S ∪ T₀) fun v _ => (hloc v).comp (continuous_componentAt3 (𝓞 ℚ) ℚ v))
  exact hF.continuousAt.congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (hO.mem_nhds hg₀) fun g hg => hfac g (S ∪ T₀) hST hg)

private theorem isGaugeMajorised3_of_eq_mul_prod
    (hfac : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))), S ⊆ T →
      (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
      W g = Warch (archComponent3 (𝓞 ℚ) ℚ g) * ∏ v ∈ T, Wloc v (componentAt3 (𝓞 ℚ) ℚ v g))
    (hsph : ∃ t : ℕ, ∀ v, v ∉ S → ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ 1 ∧ minorSup h / lastRowSup h ^ 2 ≤ 1) → Wloc v h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ 1 ∧ minorSup h / lastRowSup h ^ 2 ≤ 1 →
        ‖Wloc v h‖ ≤ 1 / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    (hS : ∀ v ∈ S, ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → Wloc v h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖Wloc v h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    (harch : ∃ t : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖Warch (archComponent3 (𝓞 ℚ) ℚ g)‖ ≤
        C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N)) :
    IsGaugeMajorised3 ℚ W := by
  classical
  obtain ⟨t₀, hsph⟩ := hsph
  obtain ⟨ta, harch⟩ := harch
  choose Ca hCa using harch
  have hS' : ∀ v, ∃ (B : ℝ) (t : ℕ) (C : ℝ), v ∈ S → ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → Wloc v h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖Wloc v h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t) := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨B, t, C, h⟩ := hS v hv
      exact ⟨B, t, C, fun _ => h⟩
    · exact ⟨0, 0, 0, fun h => absurd h hv⟩
  choose Bf tf Cf hSf using hS'
  obtain ⟨B, hB1, hBv⟩ : ∃ B : ℝ, 1 ≤ B ∧ ∀ v ∈ S, Bf v ≤ B :=
    ⟨1 + ∑ v ∈ S, |Bf v|, le_add_of_nonneg_right (Finset.sum_nonneg fun v _ => abs_nonneg (Bf v)), fun v hv =>
      (le_abs_self (Bf v)).trans ((Finset.single_le_sum (fun w _ => abs_nonneg (Bf w)) hv).trans
        (le_add_of_nonneg_left zero_le_one))⟩
  obtain ⟨t, ht₀, hta, htv⟩ : ∃ t : ℕ, t₀ ≤ t ∧ ta ≤ t ∧ ∀ v ∈ S, tf v ≤ t :=
    ⟨t₀ + ta + ∑ v ∈ S, tf v, by omega, by omega, fun v hv =>
      (Finset.single_le_sum (fun w _ => Nat.zero_le (tf w)) hv).trans (by omega)⟩
  have hBpos : 0 < B := zero_lt_one.trans_le hB1
  unfold IsGaugeMajorised3
  refine ⟨t, S, B, fun N => ?_⟩
  refine ⟨|Ca (N + 2 * Fintype.card (InfinitePlace ℚ) * (t - ta))| * ∏ v ∈ S, (|Cf v| * (B ^ 2) ^ (t - tf v)),
    fun g => ?_⟩
  obtain ⟨T₀, hT₀⟩ := exists_finset_componentAt3_mem_localMaximalCompact3 g
  have hST : S ⊆ S ∪ T₀ := fun v hv => Finset.mem_union_left T₀ hv
  have hint : ∀ w, w ∉ S ∪ T₀ → componentAt3 (𝓞 ℚ) ℚ w g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w :=
    fun w hw => hT₀ w fun h => hw (Finset.mem_union_right S h)
  have hzero : ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)), S ⊆ T →
      (∀ w, w ∉ T → componentAt3 (𝓞 ℚ) ℚ w g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w) →
      ∀ v ∈ T, Wloc v (componentAt3 (𝓞 ℚ) ℚ v g) = 0 → W g = 0 := by
    intro T hT hTint v hv h0
    rw [hfac g T hT hTint, Finset.prod_eq_zero hv h0, mul_zero]
  unfold InRootLevel
  refine ⟨fun hnot => ?_, fun hlev => ?_⟩
  · rcases not_and_or.mp hnot with h1 | h2
    · obtain ⟨v, hv⟩ := not_forall.mp h1
      obtain ⟨hvS, hroots⟩ := Classical.not_imp.mp hv
      refine hzero (insert v (S ∪ T₀)) (fun w hw => Finset.mem_insert_of_mem (hST hw))
        (fun w hw => hint w fun h => hw (Finset.mem_insert_of_mem h)) v (Finset.mem_insert_self v _) ?_
      exact (hsph v hvS (componentAt3 (𝓞 ℚ) ℚ v g)).1 hroots
    · obtain ⟨v, hv⟩ := not_forall.mp h2
      obtain ⟨hvS, hroots⟩ := Classical.not_imp.mp hv
      refine hzero (S ∪ T₀) hST hint v (hST hvS) ((hSf v hvS (componentAt3 (𝓞 ℚ) ℚ v g)).1 fun h => hroots ?_)
      exact ⟨h.1.trans (hBv v hvS), h.2.trans (hBv v hvS)⟩
  · obtain ⟨hoff, hon⟩ := hlev
    have hplace : ∀ v ∈ S ∪ T₀, ‖Wloc v (componentAt3 (𝓞 ℚ) ℚ v g)‖ ≤
        (if v ∈ S then |Cf v| * (B ^ 2) ^ (t - tf v) else 1) / (finRoot₁ ℚ v g * finRoot₂ ℚ v g) ^ t := by
      intro v _
      have hρ : 0 < finRoot₁ ℚ v g * finRoot₂ ℚ v g := mul_pos (finRoot₁_pos v g) (finRoot₂_pos v g)
      by_cases hvS : v ∈ S
      · rw [if_pos hvS]
        have hρM : finRoot₁ ℚ v g * finRoot₂ ℚ v g ≤ B ^ 2 := by
          rw [sq]
          exact mul_le_mul (hon v hvS).1 (hon v hvS).2 (finRoot₂_pos v g).le hBpos.le
        by_cases hbox : finRoot₁ ℚ v g ≤ Bf v ∧ finRoot₂ ℚ v g ≤ Bf v
        · exact le_abs_mul_pow_div_pow_of_le_div_pow hρ (pow_pos hBpos 2) hρM (htv v hvS)
            ((hSf v hvS (componentAt3 (𝓞 ℚ) ℚ v g)).2 hbox)
        · rw [(hSf v hvS (componentAt3 (𝓞 ℚ) ℚ v g)).1 hbox, norm_zero]
          exact div_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg (sq_nonneg B) _)) (pow_pos hρ t).le
      · rw [if_neg hvS]
        have hρ1 : finRoot₁ ℚ v g * finRoot₂ ℚ v g ≤ 1 :=
          (mul_le_mul (hoff v hvS).1 (hoff v hvS).2 (finRoot₂_pos v g).le zero_le_one).trans_eq (mul_one 1)
        have h := le_abs_mul_pow_div_pow_of_le_div_pow hρ one_pos hρ1 ht₀
          ((hsph v hvS (componentAt3 (𝓞 ℚ) ℚ v g)).2 (hoff v hvS))
        rwa [abs_one, one_pow, mul_one] at h
    have hprod : ‖∏ v ∈ S ∪ T₀, Wloc v (componentAt3 (𝓞 ℚ) ℚ v g)‖ ≤
        (∏ v ∈ S ∪ T₀, (if v ∈ S then |Cf v| * (B ^ 2) ^ (t - tf v) else 1)) /
          (∏ v ∈ S ∪ T₀, finRoot₁ ℚ v g * finRoot₂ ℚ v g) ^ t := by
      rw [norm_prod, ← Finset.prod_pow, ← Finset.prod_div_distrib]
      exact Finset.prod_le_prod (fun v _ => norm_nonneg _) hplace
    have hprodS : (∏ v ∈ S ∪ T₀, (if v ∈ S then |Cf v| * (B ^ 2) ^ (t - tf v) else 1)) =
        ∏ v ∈ S, (|Cf v| * (B ^ 2) ^ (t - tf v)) := by
      rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hST]
    have harchb := le_abs_div_pow_mul_pow_of_le_div (prod_archRoots_pos ℚ g) (archRootSum_nonneg ℚ g)
      (prod_archRoots_le ℚ g) hta (hCa (N + 2 * Fintype.card (InfinitePlace ℚ) * (t - ta)) g)
    have harchpos := prod_archRoots_pos ℚ g
    have hs := archRootSum_nonneg ℚ g
    rw [hfac g (S ∪ T₀) hST hint, norm_mul, rootSizeProd_eq_prod hint]
    calc ‖Warch (archComponent3 (𝓞 ℚ) ℚ g)‖ * ‖∏ v ∈ S ∪ T₀, Wloc v (componentAt3 (𝓞 ℚ) ℚ v g)‖
        ≤ (|Ca (N + 2 * Fintype.card (InfinitePlace ℚ) * (t - ta))| /
              ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N)) *
            ((∏ v ∈ S ∪ T₀, (if v ∈ S then |Cf v| * (B ^ 2) ^ (t - tf v) else 1)) /
              (∏ v ∈ S ∪ T₀, finRoot₁ ℚ v g * finRoot₂ ℚ v g) ^ t) :=
          mul_le_mul harchb hprod (norm_nonneg _)
            (div_nonneg (abs_nonneg _) (mul_pos (pow_pos harchpos t) (pow_pos (by linarith) N)).le)
      _ = (|Ca (N + 2 * Fintype.card (InfinitePlace ℚ) * (t - ta))| * ∏ v ∈ S, (|Cf v| * (B ^ 2) ^ (t - tf v))) /
            (((∏ v ∈ S ∪ T₀, finRoot₁ ℚ v g * finRoot₂ ℚ v g) *
                ∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N) := by
          rw [hprodS]
          ring

private theorem continuous_and_isGaugeMajorised3_of_eq_mul_prod_aux
    (hfac : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))), S ⊆ T →
      (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
      W g = Warch (archComponent3 (𝓞 ℚ) ℚ g) * ∏ v ∈ T, Wloc v (componentAt3 (𝓞 ℚ) ℚ v g))
    (hinv : ∀ v, v ∉ S → IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) (Wloc v))
    (hsph : ∃ t : ℕ, ∀ v, v ∉ S → ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ 1 ∧ minorSup h / lastRowSup h ^ 2 ≤ 1) → Wloc v h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ 1 ∧ minorSup h / lastRowSup h ^ 2 ≤ 1 →
        ‖Wloc v h‖ ≤ 1 / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    (hS : ∀ v ∈ S,
      (∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, Wloc v (g * k) = Wloc v g) ∧
      ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
          (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → Wloc v h = 0) ∧
          (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
            ‖Wloc v h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    (harch : Continuous Warch ∧ ∃ t : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖Warch (archComponent3 (𝓞 ℚ) ℚ g)‖ ≤
        C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N)) :
    Continuous W ∧ IsGaugeMajorised3 ℚ W :=
  ⟨continuous_of_eq_mul_prod Warch Wloc S W hfac hinv (fun v hv => (hS v hv).1) harch.1,
    isGaugeMajorised3_of_eq_mul_prod Warch Wloc S W hfac hsph (fun v hv => (hS v hv).2) harch.2⟩

end Assembly

end LanglandsTunnell.CubicInduction

end
end

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_continuous_and_isGaugeMajorised3_of_eq_mul_prod.LanglandsTunnell.CubicInduction in
theorem solution
    (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (Wloc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hfac : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))), S ⊆ T →
      (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
      W g = Warch (archComponent3 (𝓞 ℚ) ℚ g) * ∏ v ∈ T, Wloc v (componentAt3 (𝓞 ℚ) ℚ v g))
    (hinv : ∀ v, v ∉ S → IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) (Wloc v))
    (hsph : ∃ t : ℕ, ∀ v, v ∉ S → ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ 1 ∧ minorSup h / lastRowSup h ^ 2 ≤ 1) → Wloc v h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ 1 ∧ minorSup h / lastRowSup h ^ 2 ≤ 1 →
        ‖Wloc v h‖ ≤ 1 / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    (hS : ∀ v ∈ S,
      (∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, Wloc v (g * k) = Wloc v g) ∧
      ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
          (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → Wloc v h = 0) ∧
          (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
            ‖Wloc v h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    (harch : Continuous Warch ∧ ∃ t : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖Warch (archComponent3 (𝓞 ℚ) ℚ g)‖ ≤
        C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N)) :
    Continuous W ∧ IsGaugeMajorised3 ℚ W := by
  exact continuous_and_isGaugeMajorised3_of_eq_mul_prod_aux Warch Wloc S W hfac hinv hsph hS harch

end S_LanglandsTunnell_CubicInduction_continuous_and_isGaugeMajorised3_of_eq_mul_prod
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_continuous_and_isGaugeMajorised3_of_eq_mul_prod (solution)
