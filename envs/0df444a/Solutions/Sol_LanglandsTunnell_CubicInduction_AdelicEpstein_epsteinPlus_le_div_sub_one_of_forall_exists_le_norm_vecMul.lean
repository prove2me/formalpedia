-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.AdelicEpstein.epsteinPlus_le_div_sub_one_of_forall_exists_le_norm_vecMul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/983333f4-0aa6-5b51-8fc5-1edb6b114bd6

import Definitions.Def_LanglandsTunnell_CubicInduction_AdelicEpstein
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_epsteinPlus_le_div_sub_one_of_forall_exists_le_norm_vecMul

set_option autoImplicit false

noncomputable section

open NumberField MeasureTheory LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.AdelicEpstein
open scoped ENNReal

namespace KcEpsteinTail

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "𝔸f" => IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "Ẑˣ" => IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ

def re : 𝔸 →+* ℝ :=
  ((InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).comp
    (Pi.evalRingHom (fun v : InfinitePlace ℚ => v.Completion) Rat.infinitePlace)).comp
    (RingHom.fst (InfiniteAdeleRing ℚ) 𝔸f)

theorem re_apply (x : 𝔸) :
    re x = InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (x.1 Rat.infinitePlace) :=
  rfl

theorem abs_re (x : 𝔸) : |re x| = ‖x.1 Rat.infinitePlace‖ := by
  rw [re_apply, ← Real.norm_eq_abs]
  exact Isometry.norm_map_of_map_zero
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace) (map_zero _) _

theorem re_ofReal (t : ℝ) : InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
    (ofReal t) = t := by
  unfold ofReal
  exact (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply t

theorem archIdele_of_ne_zero {t : ℝ} (ht : t ≠ 0) :
    ((archIdele t : 𝔸ˣ) : 𝔸) =
      ((NumberField.AdelicVolume.archCentralUnit ℚ Rat.infinitePlace
        (Units.mk0 (ofReal t) (by unfold ofReal; exact (map_ne_zero _).mpr ht)) : 𝔸ˣ) : 𝔸) := by
  unfold archIdele
  rw [dif_neg ht]
  rfl

theorem re_archIdele {t : ℝ} (ht : t ≠ 0) : re ((archIdele t : 𝔸ˣ) : 𝔸) = t := by
  rw [re_apply, archIdele_of_ne_zero ht, NumberField.AdelicVolume.archCentralUnit_fst_self, Units.val_mk0,
    re_ofReal]

theorem snd_archIdele (t : ℝ) : ((archIdele t : 𝔸ˣ) : 𝔸).2 = 1 := by
  by_cases ht : t = 0
  · subst ht
    unfold archIdele
    rw [dif_pos rfl]
    rfl
  · rw [archIdele_of_ne_zero ht]
    exact NumberField.AdelicVolume.archCentralUnit_snd _ _

theorem re_finUnitIdele (u : Ẑˣ) : re ((finUnitIdele u : 𝔸ˣ) : 𝔸) = 1 := by
  rw [re_apply, finUnitIdele, Units.coe_map]
  erw [AdelicLevel.finIncl_apply_fst]
  exact map_one _

def fin : 𝔸 →+* 𝔸f := RingHom.snd (InfiniteAdeleRing ℚ) 𝔸f

theorem fin_apply (x : 𝔸) : fin x = x.2 := rfl

theorem fin_finUnitIdele (u : Ẑˣ) : fin ((finUnitIdele u : 𝔸ˣ) : 𝔸) = ((u : 𝔸fˣ) : 𝔸f) := by
  rw [fin_apply, finUnitIdele, Units.coe_map]
  exact AdelicLevel.finIncl_apply_snd (𝓞 ℚ) ℚ _

def Y (g : AdelicGL 3 (𝓞 ℚ) ℚ) (ξ : Fin 3 → ℚ) (i : Fin 3) : ℝ :=
  re (Matrix.vecMul (adelicDiag ξ) (g : Matrix (Fin 3) (Fin 3) 𝔸) i)

def Z (g : AdelicGL 3 (𝓞 ℚ) ℚ) (ξ : Fin 3 → ℚ) (i : Fin 3) : 𝔸f :=
  fin (Matrix.vecMul (adelicDiag ξ) (g : Matrix (Fin 3) (Fin 3) 𝔸) i)

theorem Z_apply (g : AdelicGL 3 (𝓞 ℚ) ℚ) (ξ : Fin 3 → ℚ) (i : Fin 3) :
    Z g ξ i = (Matrix.vecMul (adelicDiag ξ) (g : Matrix (Fin 3) (Fin 3) 𝔸) i).2 := rfl

theorem adelicDiag_sub (ξ ξ' : Fin 3 → ℚ) : adelicDiag (ξ - ξ') = adelicDiag ξ - adelicDiag ξ' := by
  funext i
  simp [adelicDiag]

theorem adelicDiag_zero : adelicDiag 0 = 0 := by
  funext i
  simp [adelicDiag]

theorem Y_sub (g : AdelicGL 3 (𝓞 ℚ) ℚ) (ξ ξ' : Fin 3 → ℚ) (i : Fin 3) :
    Y g (ξ - ξ') i = Y g ξ i - Y g ξ' i := by
  simp only [Y, adelicDiag_sub, Matrix.sub_vecMul, Pi.sub_apply, map_sub]

theorem Z_sub (g : AdelicGL 3 (𝓞 ℚ) ℚ) (ξ ξ' : Fin 3 → ℚ) :
    Z g (ξ - ξ') = Z g ξ - Z g ξ' := by
  funext i
  simp only [Z, adelicDiag_sub, Matrix.sub_vecMul, Pi.sub_apply, map_sub]

theorem Y_zero (g : AdelicGL 3 (𝓞 ℚ) ℚ) (i : Fin 3) : Y g 0 i = 0 := by
  simp only [Y, adelicDiag_zero, Matrix.zero_vecMul, Pi.zero_apply, map_zero]

theorem Z_zero (g : AdelicGL 3 (𝓞 ℚ) ℚ) : Z g 0 = 0 := by
  funext i
  simp only [Z, adelicDiag_zero, Matrix.zero_vecMul, Pi.zero_apply, map_zero]

theorem abs_Y (g : AdelicGL 3 (𝓞 ℚ) ℚ) (ξ : Fin 3 → ℚ) (i : Fin 3) :
    |Y g ξ i| = ‖(Matrix.vecMul (adelicDiag ξ) (g : Matrix (Fin 3) (Fin 3) 𝔸) i).1 Rat.infinitePlace‖ :=
  abs_re _

theorem re_point {t : ℝ} (ht : t ≠ 0) (u : Ẑˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (ξ : Fin 3 → ℚ) (i : Fin 3) :
    re (point t u g ξ i) = t * Y g ξ i := by
  unfold point Y
  rw [map_mul, Units.val_mul, map_mul, re_archIdele ht, re_finUnitIdele, mul_one]

theorem snd_point (t : ℝ) (u : Ẑˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (ξ : Fin 3 → ℚ) (i : Fin 3) :
    (point t u g ξ i).2 = ((u : 𝔸fˣ) : 𝔸f) * Z g ξ i := by
  unfold point Z
  rw [← fin_apply, map_mul, Units.val_mul, map_mul, fin_apply, snd_archIdele, fin_finUnitIdele, one_mul]

theorem norm_fst_point {t : ℝ} (ht : t ≠ 0) (u : Ẑˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (ξ : Fin 3 → ℚ) (i : Fin 3) :
    ‖(point t u g ξ i).1 Rat.infinitePlace‖ = |t * Y g ξ i| := by
  rw [← abs_re, re_point ht]

theorem tsum_indicator_le_of_separated {ι : Type*} [Countable ι] (y : ι → Fin 3 → ℝ) (C : Set ι)
    {s R : ℝ} (hs : 0 < s) (hR : 0 ≤ R)
    (hin : ∀ ξ ∈ C, ∀ i, |y ξ i| ≤ R)
    (hsep : ∀ ξ ∈ C, ∀ ξ' ∈ C, ξ ≠ ξ' → ∃ i, s ≤ |y ξ i - y ξ' i|) :
    ∑' ξ, C.indicator (fun _ => (1 : ℝ≥0∞)) ξ ≤ ENNReal.ofReal (((2 * R + s) / s) ^ 3) := by
  classical
  let box : ι → Set (Fin 3 → ℝ) := fun ξ => Set.univ.pi fun i => Set.Ico (y ξ i) (y ξ i + s)
  let S : ι → Set (Fin 3 → ℝ) := fun ξ => if ξ ∈ C then box ξ else ∅
  have hSmeas : ∀ ξ, MeasurableSet (S ξ) := by
    intro ξ
    by_cases hξ : ξ ∈ C
    · simp only [S, if_pos hξ, box]
      exact MeasurableSet.univ_pi fun _ => measurableSet_Ico
    · simp only [S, if_neg hξ]
      exact MeasurableSet.empty
  have hSvol : ∀ ξ, volume (S ξ) = C.indicator (fun _ => (1 : ℝ≥0∞)) ξ * ENNReal.ofReal s ^ 3 := by
    intro ξ
    by_cases hξ : ξ ∈ C
    · simp only [S, if_pos hξ, box, Set.indicator_of_mem hξ, one_mul]
      rw [Real.volume_pi_Ico]
      simp only [add_sub_cancel_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · simp only [S, if_neg hξ, Set.indicator_of_notMem hξ, measure_empty, zero_mul]
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    intro ξ ξ' hne
    change Disjoint (S ξ) (S ξ')
    by_cases hξ : ξ ∈ C
    swap
    · simp only [S, if_neg hξ]
      exact Set.empty_disjoint _
    by_cases hξ' : ξ' ∈ C
    swap
    · simp only [S, if_neg hξ']
      exact Set.disjoint_empty _
    simp only [S, if_pos hξ, if_pos hξ', box]
    obtain ⟨i, hi⟩ := hsep ξ hξ ξ' hξ' hne
    rw [Set.disjoint_left]
    intro z hz hz'
    have h1 := (Set.mem_univ_pi.mp hz) i
    have h2 := (Set.mem_univ_pi.mp hz') i
    rw [Set.mem_Ico] at h1 h2
    have h3 : |y ξ i - y ξ' i| < s := by
      rw [abs_sub_lt_iff]
      constructor <;> linarith
    linarith
  have hsub : (⋃ ξ, S ξ) ⊆ Set.univ.pi fun _ : Fin 3 => Set.Ico (-R) (R + s) := by
    intro z hz
    obtain ⟨ξ, hξz⟩ := Set.mem_iUnion.mp hz
    by_cases hξ : ξ ∈ C
    swap
    · simp only [S, if_neg hξ] at hξz
      exact absurd hξz (Set.notMem_empty _)
    simp only [S, if_pos hξ, box] at hξz
    refine Set.mem_univ_pi.mpr fun i => ?_
    have h1 := (Set.mem_univ_pi.mp hξz) i
    rw [Set.mem_Ico] at h1 ⊢
    have h2 := hin ξ hξ i
    rw [abs_le] at h2
    constructor <;> linarith
  have hvol : (∑' ξ, C.indicator (fun _ => (1 : ℝ≥0∞)) ξ) * ENNReal.ofReal s ^ 3 ≤
      ENNReal.ofReal (2 * R + s) ^ 3 := by
    rw [← ENNReal.tsum_mul_right]
    calc ∑' ξ, C.indicator (fun _ => (1 : ℝ≥0∞)) ξ * ENNReal.ofReal s ^ 3
        = ∑' ξ, volume (S ξ) := tsum_congr fun ξ => (hSvol ξ).symm
      _ = volume (⋃ ξ, S ξ) := (measure_iUnion hdisj hSmeas).symm
      _ ≤ volume (Set.univ.pi fun _ : Fin 3 => Set.Ico (-R) (R + s)) := measure_mono hsub
      _ = ENNReal.ofReal (2 * R + s) ^ 3 := by
          rw [Real.volume_pi_Ico]
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          congr 2
          ring
  have hs3 : ENNReal.ofReal s ^ 3 ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr hs).ne'
  have hs3' : ENNReal.ofReal s ^ 3 ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  calc ∑' ξ, C.indicator (fun _ => (1 : ℝ≥0∞)) ξ
      ≤ ENNReal.ofReal (2 * R + s) ^ 3 / ENNReal.ofReal s ^ 3 :=
        (ENNReal.le_div_iff_mul_le (Or.inl hs3) (Or.inl hs3')).mpr hvol
    _ = ENNReal.ofReal (((2 * R + s) / s) ^ 3) := by
        rw [div_pow, ENNReal.ofReal_div_of_pos (pow_pos hs 3), ENNReal.ofReal_pow (by linarith),
          ENNReal.ofReal_pow hs.le]

section LatticeSum

variable (Φ : (Fin 3 → 𝔸) → ℂ) (M R₀ r : ℝ)
  (L : AddSubgroup (Fin 3 → 𝔸f)) (g : AdelicGL 3 (𝓞 ℚ) ℚ)

def contrib (t : ℝ) (u : Ẑˣ) : Set {ξ : Fin 3 → ℚ // ξ ≠ 0} :=
  {ξ | Φ (point t u g ξ.1) ≠ 0}

variable {Φ M R₀ r L g}
variable (hM : ∀ x, ‖Φ x‖ ≤ M)
  (hsupp : ∀ x, Φ x ≠ 0 → ∀ i, ‖(x i).1 Rat.infinitePlace‖ ≤ R₀)
  (hL : ∀ x, Φ x ≠ 0 → (fun i => (x i).2) ∈ L)
  (hLu : ∀ (u : Ẑˣ) (z : Fin 3 → 𝔸f), z ∈ L → (fun i => ((u : 𝔸fˣ) : 𝔸f) * z i) ∈ L)
  (hsep : ∀ ξ : Fin 3 → ℚ, ξ ≠ 0 →
    (fun i => (Matrix.vecMul (adelicDiag ξ) (g : Matrix (Fin 3) (Fin 3) 𝔸) i).2) ∈ L →
      ∃ i, r ≤ ‖(Matrix.vecMul (adelicDiag ξ) (g : Matrix (Fin 3) (Fin 3) 𝔸) i).1 Rat.infinitePlace‖)

include hL hLu in

theorem Z_mem_of_contrib {t : ℝ} {u : Ẑˣ} {ξ : Fin 3 → ℚ} (h : Φ (point t u g ξ) ≠ 0) : Z g ξ ∈ L := by
  have h1 := hLu u⁻¹ _ (hL _ h)
  convert h1 using 1
  funext i
  rw [snd_point, ← mul_assoc, Subgroup.coe_inv, Units.inv_mul, one_mul]

include hsep in

theorem exists_le_abs_Y_sub {ξ ξ' : Fin 3 → ℚ} (hξ : Z g ξ ∈ L) (hξ' : Z g ξ' ∈ L) (hne : ξ ≠ ξ') :
    ∃ i, r ≤ |Y g ξ i - Y g ξ' i| := by
  have hmem : (fun i => (Matrix.vecMul (adelicDiag (ξ - ξ')) (g : Matrix (Fin 3) (Fin 3) 𝔸) i).2) ∈ L := by
    have : (fun i => (Matrix.vecMul (adelicDiag (ξ - ξ')) (g : Matrix (Fin 3) (Fin 3) 𝔸) i).2) = Z g (ξ - ξ') :=
      rfl
    rw [this, Z_sub]
    exact L.sub_mem hξ hξ'
  obtain ⟨i, hi⟩ := hsep (ξ - ξ') (sub_ne_zero.mpr hne) hmem
  refine ⟨i, ?_⟩
  rw [← Y_sub, abs_Y]
  exact hi

include hsupp hL hLu hsep in

theorem contrib_eq_empty {t : ℝ} (ht : 0 < t) (hr : 0 < r) (htr : R₀ / r < t) (u : Ẑˣ) :
    contrib Φ g t u = ∅ := by
  ext ⟨ξ, hξ0⟩
  simp only [contrib, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
  by_contra h
  have hZ : Z g ξ ∈ L := Z_mem_of_contrib hL hLu h
  obtain ⟨i, hi⟩ := exists_le_abs_Y_sub hsep hZ (by rw [Z_zero]; exact L.zero_mem) hξ0
  rw [Y_zero, sub_zero] at hi
  have h1 := hsupp _ h i
  rw [norm_fst_point ht.ne' u g ξ i, abs_mul, abs_of_pos ht] at h1
  have h2 : R₀ < t * r := (div_lt_iff₀ hr).mp htr
  have h3 : t * r ≤ t * |Y g ξ i| := mul_le_mul_of_nonneg_left hi ht.le
  linarith

include hM hsupp hL hLu hsep in

theorem tsum_nnnorm_le {t : ℝ} (ht : 0 < t) (hr : 0 < r) (hR₀ : 0 ≤ R₀) (u : Ẑˣ) :
    ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, (‖Φ (point t u g ξ.1)‖₊ : ℝ≥0∞) ≤
      if t ≤ R₀ / r then ENNReal.ofReal (M * (3 * R₀ / (t * r)) ^ 3) else 0 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)

  have hpt : ∀ ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, (‖Φ (point t u g ξ.1)‖₊ : ℝ≥0∞) ≤
      ENNReal.ofReal M * (contrib Φ g t u).indicator (fun _ => (1 : ℝ≥0∞)) ξ := by
    intro ξ
    by_cases hξ : ξ ∈ contrib Φ g t u
    · rw [Set.indicator_of_mem hξ, mul_one]
      have h1 : (‖Φ (point t u g ξ.1)‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖Φ (point t u g ξ.1)‖ := by
        rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]
      rw [h1]
      exact ENNReal.ofReal_le_ofReal (hM _)
    · have h0 : Φ (point t u g ξ.1) = 0 := by
        simpa [contrib] using hξ
      rw [h0, nnnorm_zero, ENNReal.coe_zero]
      exact bot_le
  split_ifs with hle
  ·
    have hpack := tsum_indicator_le_of_separated (fun ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0} => fun i => t * Y g ξ.1 i)
      (contrib Φ g t u) (mul_pos ht hr) hR₀
      (fun ξ hξ i => by
        have h1 := hsupp _ hξ i
        rwa [norm_fst_point ht.ne'] at h1)
      (fun ξ hξ ξ' hξ' hne => by
        obtain ⟨i, hi⟩ := exists_le_abs_Y_sub hsep (Z_mem_of_contrib hL hLu hξ) (Z_mem_of_contrib hL hLu hξ')
          (fun h => hne (Subtype.ext h))
        refine ⟨i, ?_⟩
        rw [← mul_sub, abs_mul, abs_of_pos ht]
        exact mul_le_mul_of_nonneg_left hi ht.le)
    calc ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, (‖Φ (point t u g ξ.1)‖₊ : ℝ≥0∞)
        ≤ ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, ENNReal.ofReal M * (contrib Φ g t u).indicator (fun _ => (1 : ℝ≥0∞)) ξ :=
          ENNReal.tsum_le_tsum hpt
      _ = ENNReal.ofReal M * ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, (contrib Φ g t u).indicator (fun _ => (1 : ℝ≥0∞)) ξ :=
          ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal (((2 * R₀ + t * r) / (t * r)) ^ 3) := by gcongr
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal ((3 * R₀ / (t * r)) ^ 3) := by
          refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
          have htr : 0 < t * r := mul_pos ht hr
          have h1 : t * r ≤ R₀ := by rwa [le_div_iff₀ hr] at hle
          have h2 : (2 * R₀ + t * r) / (t * r) ≤ 3 * R₀ / (t * r) :=
            div_le_div_of_nonneg_right (by linarith) htr.le
          exact pow_le_pow_left₀ (by positivity) h2 3
      _ = ENNReal.ofReal (M * (3 * R₀ / (t * r)) ^ 3) := by rw [← ENNReal.ofReal_mul hM0]
  · rw [contrib_eq_empty hsupp hL hLu hsep ht hr (lt_of_not_ge hle) u] at hpt
    calc ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, (‖Φ (point t u g ξ.1)‖₊ : ℝ≥0∞)
        ≤ ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, ENNReal.ofReal M * (∅ : Set _).indicator (fun _ => (1 : ℝ≥0∞)) ξ :=
          ENNReal.tsum_le_tsum hpt
      _ = 0 := by simp

end LatticeSum

def scaleBound (M R₀ r t : ℝ) : ℝ≥0∞ :=
  if t ≤ R₀ / r then ENNReal.ofReal (M * (3 * R₀ / (t * r)) ^ 3) else 0

theorem inv_mul_rpow_mul_scaleBound {M R₀ r σ t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    ENNReal.ofReal t⁻¹ * (ENNReal.ofReal (t ^ (3 * σ)) * scaleBound M R₀ r t) =
      (Set.Ioc 0 (R₀ / r)).indicator (fun t => ENNReal.ofReal (27 * M * (R₀ / r) ^ 3 * t ^ (3 * σ - 4))) t := by
  unfold scaleBound
  by_cases hle : t ≤ R₀ / r
  · rw [if_pos hle, Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨ht, hle⟩),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le)]
    congr 1
    have h4 : t ^ (3 * σ - 4) = t ^ (3 * σ) / t ^ 4 := by
      rw [Real.rpow_sub ht, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h4]
    simp only [div_pow, mul_pow]
    have ht0 : t ≠ 0 := ht.ne'
    have hr0 : r ≠ 0 := hr.ne'
    have ht3 : t ^ 3 ≠ 0 := pow_ne_zero 3 ht0
    have ht4 : t ^ 4 ≠ 0 := pow_ne_zero 4 ht0
    have hr3 : r ^ 3 ≠ 0 := pow_ne_zero 3 hr0
    calc t⁻¹ * (t ^ (3 * σ) * (M * (3 ^ 3 * R₀ ^ 3 / (t ^ 3 * r ^ 3))))
        = (t⁻¹ * (t ^ 3)⁻¹) * t ^ (3 * σ) * (27 * M * R₀ ^ 3 / r ^ 3) := by
          rw [div_eq_mul_inv, mul_inv]
          ring
      _ = (t ^ 4)⁻¹ * t ^ (3 * σ) * (27 * M * R₀ ^ 3 / r ^ 3) := by
          rw [← mul_inv, ← pow_succ']
      _ = 27 * M * (R₀ ^ 3 / r ^ 3) * (t ^ (3 * σ) / t ^ 4) := by
          rw [div_eq_mul_inv (t ^ (3 * σ)), mul_div_assoc]
          ring
  · rw [if_neg hle, mul_zero, mul_zero, Set.indicator_of_notMem]
    exact fun h => hle (Set.mem_Ioc.mp h).2

theorem measurable_scaleIntegrand (K e : ℝ) :
    Measurable fun t : ℝ => ENNReal.ofReal (K * t ^ e) :=
  (measurable_const.mul (measurable_id.pow_const e)).ennreal_ofReal

theorem lintegral_Ioc_rpow {K c σ : ℝ} (hK : 0 ≤ K) (hc : 0 ≤ c) (hσ : 1 < σ) :
    ∫⁻ t in Set.Ioc 0 c, ENNReal.ofReal (K * t ^ (3 * σ - 4)) =
      ENNReal.ofReal (K * c ^ (3 * σ - 3) / (3 * σ - 3)) := by
  have he : -1 < 3 * σ - 4 := by linarith
  have hint : IntegrableOn (fun t : ℝ => K * t ^ (3 * σ - 4)) (Set.Ioc 0 c) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hc).mp (intervalIntegral.intervalIntegrable_rpow' he)).const_mul K
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 c)] fun t : ℝ => K * t ^ (3 * σ - 4) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun t ht => mul_nonneg hK (Real.rpow_nonneg ht.1.le _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [integral_const_mul, ← intervalIntegral.integral_of_le hc, integral_rpow (Or.inl he),
    show 3 * σ - 4 + 1 = 3 * σ - 3 by ring, Real.zero_rpow (by linarith), sub_zero, mul_div_assoc]

theorem lintegral_scaleMeasure_le {M R₀ r σ : ℝ} (hM : 0 ≤ M) (hR₀ : 0 ≤ R₀) (hr : 0 < r) (hσ : 1 < σ)
    (F : ℝ → ℝ≥0∞) (A : ℝ≥0∞)
    (hF : ∀ t, 0 < t → F t ≤ ENNReal.ofReal (t ^ (3 * σ)) * scaleBound M R₀ r t * A) :
    ∫⁻ t, F t ∂scaleMeasure ≤ ENNReal.ofReal (9 * M * (R₀ / r) ^ (3 * σ) / (σ - 1)) * A := by
  have hc : 0 ≤ R₀ / r := div_nonneg hR₀ hr.le
  set K : ℝ := 27 * M * (R₀ / r) ^ 3 with hK
  have hK0 : 0 ≤ K := by positivity

  have hA : ∫⁻ t, F t ∂scaleMeasure = ∫⁻ t in Set.Ioi 0, ENNReal.ofReal t⁻¹ * F t := by
    unfold scaleMeasure
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ measurable_inv.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    rfl

  have hB : ∫⁻ t in Set.Ioi 0, ENNReal.ofReal t⁻¹ * F t ≤
      ∫⁻ t in Set.Ioi 0, (Set.Ioc 0 (R₀ / r)).indicator (fun t => ENNReal.ofReal (K * t ^ (3 * σ - 4))) t * A := by
    refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
    rw [← inv_mul_rpow_mul_scaleBound (σ := σ) hr ht]
    calc ENNReal.ofReal t⁻¹ * F t
        ≤ ENNReal.ofReal t⁻¹ * (ENNReal.ofReal (t ^ (3 * σ)) * scaleBound M R₀ r t * A) :=
          mul_le_mul_right (hF t ht) _
      _ = ENNReal.ofReal t⁻¹ * (ENNReal.ofReal (t ^ (3 * σ)) * scaleBound M R₀ r t) * A := by
          simp only [mul_assoc]

  have hC : ∫⁻ t in Set.Ioi 0, (Set.Ioc 0 (R₀ / r)).indicator (fun t => ENNReal.ofReal (K * t ^ (3 * σ - 4))) t * A =
      ENNReal.ofReal (K * (R₀ / r) ^ (3 * σ - 3) / (3 * σ - 3)) * A := by
    rw [lintegral_mul_const _ ((measurable_scaleIntegrand K _).indicator measurableSet_Ioc),
      lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
      Set.inter_eq_left.mpr Set.Ioc_subset_Ioi_self, lintegral_Ioc_rpow hK0 hc hσ]

  have hD : K * (R₀ / r) ^ (3 * σ - 3) / (3 * σ - 3) = 9 * M * (R₀ / r) ^ (3 * σ) / (σ - 1) := by
    have h3 : (R₀ / r) ^ (3 * σ) = (R₀ / r) ^ 3 * (R₀ / r) ^ (3 * σ - 3) := by
      have h : ((3 : ℕ) : ℝ) + (3 * σ - 3) ≠ 0 := by push_cast; linarith
      rw [← Real.rpow_natCast _ 3, ← Real.rpow_add' hc h]
      congr 1
      push_cast
      ring
    rw [h3, hK]
    have hσ' : σ - 1 ≠ 0 := by linarith
    have hσ'' : 3 * σ - 3 ≠ 0 := by linarith
    field_simp
    ring
  rw [hA, ← hD]
  exact hB.trans hC.le

theorem epsteinPlus_le [MeasurableSpace Ẑˣ] (du : Measure Ẑˣ)
    (Φ : (Fin 3 → 𝔸) → ℂ) (M R₀ r : ℝ) (hR₀ : 0 ≤ R₀) (hr : 0 < r)
    (hM : ∀ x, ‖Φ x‖ ≤ M)
    (hsupp : ∀ x, Φ x ≠ 0 → ∀ i, ‖(x i).1 Rat.infinitePlace‖ ≤ R₀)
    (L : AddSubgroup (Fin 3 → 𝔸f))
    (hL : ∀ x, Φ x ≠ 0 → (fun i => (x i).2) ∈ L)
    (hLu : ∀ (u : Ẑˣ) (z : Fin 3 → 𝔸f), z ∈ L → (fun i => ((u : 𝔸fˣ) : 𝔸f) * z i) ∈ L)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hsep : ∀ ξ : Fin 3 → ℚ, ξ ≠ 0 →
      (fun i => (Matrix.vecMul (adelicDiag ξ) (g : Matrix (Fin 3) (Fin 3) 𝔸) i).2) ∈ L →
        ∃ i, r ≤ ‖(Matrix.vecMul (adelicDiag ξ) (g : Matrix (Fin 3) (Fin 3) 𝔸) i).1 Rat.infinitePlace‖)
    (σ : ℝ) (hσ : 1 < σ) :
    epsteinPlus du Φ σ g ≤
      ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ *
          (9 * M * (R₀ / r) ^ (3 * σ) / (σ - 1))) * du Set.univ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hinner : ∀ t, 0 < t →
      ENNReal.ofReal (t ^ (3 * σ)) *
          ∫⁻ u, ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, (‖Φ (point t u g ξ.1)‖₊ : ℝ≥0∞) ∂du ≤
        ENNReal.ofReal (t ^ (3 * σ)) * scaleBound M R₀ r t * du Set.univ := by
    intro t ht
    rw [mul_assoc]
    refine mul_le_mul_right ?_ _
    calc ∫⁻ u, ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, (‖Φ (point t u g ξ.1)‖₊ : ℝ≥0∞) ∂du
        ≤ ∫⁻ _u, scaleBound M R₀ r t ∂du :=
          lintegral_mono fun u => tsum_nnnorm_le hM hsupp hL hLu hsep ht hr hR₀ u
      _ = scaleBound M R₀ r t * du Set.univ := lintegral_const _
  have hscale := lintegral_scaleMeasure_le hM0 hR₀ hr hσ _ (du Set.univ) hinner
  unfold epsteinPlus
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (TateGlobal.ideleNorm_pos _).le _), mul_assoc]
  exact mul_le_mul_right hscale _

end KcEpsteinTail

open LanglandsTunnell.CubicInduction.AdelicEpstein in
theorem solution
    [MeasurableSpace (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ)]
    (du : Measure (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ))
    (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (M R₀ r : ℝ) (hR₀ : 0 ≤ R₀) (hr : 0 < r)
    (hM : ∀ x, ‖Φ x‖ ≤ M)
    (hsupp : ∀ x, Φ x ≠ 0 → ∀ i, ‖(x i).1 Rat.infinitePlace‖ ≤ R₀)
    (L : AddSubgroup (Fin 3 → IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ))
    (hL : ∀ x, Φ x ≠ 0 → (fun i => (x i).2) ∈ L)
    (hLu : ∀ (u : IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ)
      (z : Fin 3 → IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ), z ∈ L →
        (fun i => ((u : (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
          IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) * z i) ∈ L)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hsep : ∀ ξ : Fin 3 → ℚ, ξ ≠ 0 →
      (fun i => (Matrix.vecMul (adelicDiag ξ) (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i).2) ∈ L →
        ∃ i, r ≤ ‖(Matrix.vecMul (adelicDiag ξ) (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i).1
          Rat.infinitePlace‖)
    (σ : ℝ) (hσ : 1 < σ) :
    epsteinPlus du Φ σ g ≤
      ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ *
          (9 * M * (R₀ / r) ^ (3 * σ) / (σ - 1))) * du Set.univ :=
  KcEpsteinTail.epsteinPlus_le du Φ M R₀ r hR₀ hr hM hsupp L hL hLu g hsep σ hσ

end

end S_LanglandsTunnell_CubicInduction_AdelicEpstein_epsteinPlus_le_div_sub_one_of_forall_exists_le_norm_vecMul
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_epsteinPlus_le_div_sub_one_of_forall_exists_le_norm_vecMul (solution)
