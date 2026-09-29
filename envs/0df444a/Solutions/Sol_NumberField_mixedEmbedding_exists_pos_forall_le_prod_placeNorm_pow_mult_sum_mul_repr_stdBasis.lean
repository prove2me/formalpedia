-- Prove2me | solution 1 for NumberField.mixedEmbedding.exists_pos_forall_le_prod_placeNorm_pow_mult_sum_mul_repr_stdBasis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/93ab96fd-d581-5d28-9860-e0f176b6c036

import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_mixedEmbedding_exists_pos_forall_le_prod_placeNorm_pow_mult_sum_mul_repr_stdBasis

set_option autoImplicit false

noncomputable section

open scoped nonZeroDivisors NNReal ENNReal Classical Topology
open MeasureTheory Filter Function NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

namespace L4Sol

section Arithmetic

variable (F : Type) [Field F] [NumberField F] (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)

private abbrev idealBasis : Module.Basis (Module.Free.ChooseBasisIndex ℤ I) ℝ (mixedSpace F) :=
  fractionalIdealLatticeBasis F I

private def modeForm (m : Module.Free.ChooseBasisIndex ℤ I → ℤ) : mixedSpace F →ₗ[ℝ] ℝ :=
  ∑ i, (m i : ℝ) • (idealBasis F I).coord i

private theorem modeForm_apply (m : Module.Free.ChooseBasisIndex ℤ I → ℤ) (x : mixedSpace F) :
    modeForm F I m x = ∑ i, (m i : ℝ) * (idealBasis F I).repr x i := by
  simp [modeForm, LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply]

private theorem modeForm_basis (m : Module.Free.ChooseBasisIndex ℤ I → ℤ) (j : Module.Free.ChooseBasisIndex ℤ I) :
    modeForm F I m (idealBasis F I j) = m j := by
  rw [modeForm_apply]
  simp only [Module.Basis.repr_self, Finsupp.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

private theorem exists_int_modeForm_eq (m : Module.Free.ChooseBasisIndex ℤ I → ℤ) {x : mixedSpace F}
    (hx : x ∈ Submodule.span ℤ (Set.range (idealBasis F I))) :
    ∃ z : ℤ, modeForm F I m x = z := by
  rw [Module.Basis.mem_span_iff_repr_mem] at hx
  choose z hz using hx
  refine ⟨∑ i, m i * z i, ?_⟩
  rw [modeForm_apply]
  push_cast
  exact Finset.sum_congr rfl fun i _ => by rw [← hz i]; rfl

private theorem mul_mem_span_idealBasis (a : 𝓞 F) {x : mixedSpace F}
    (hx : x ∈ Submodule.span ℤ (Set.range (idealBasis F I))) :
    mixedEmbedding F (a : F) * x ∈ Submodule.span ℤ (Set.range (idealBasis F I)) := by
  have hx' : x ∈ mixedEmbedding F '' ((I : FractionalIdeal (𝓞 F)⁰ F) : Set F) :=
    (mem_span_fractionalIdealLatticeBasis F I).mp hx
  obtain ⟨y, hy, rfl⟩ := hx'
  have hyI : y ∈ (I : FractionalIdeal (𝓞 F)⁰ F) := hy
  have hay : a • y ∈ (I : FractionalIdeal (𝓞 F)⁰ F) :=
    (FractionalIdeal.mem_coe).mp (Submodule.smul_mem _ a ((FractionalIdeal.mem_coe).mpr hyI))
  refine (mem_span_fractionalIdealLatticeBasis F I).mpr ⟨(a : F) * y, ?_, by rw [map_mul]⟩
  have h : (a : F) * y = a • y := (Algebra.smul_def a y).symm
  rw [h]
  exact hay

private def cR (m : Module.Free.ChooseBasisIndex ℤ I → ℤ) (v : {w : InfinitePlace F // w.IsReal}) : ℝ :=
  modeForm F I m (stdBasis F (Sum.inl v))

private def c0 (m : Module.Free.ChooseBasisIndex ℤ I → ℤ) (w : {w : InfinitePlace F // w.IsComplex}) : ℝ :=
  modeForm F I m (stdBasis F (Sum.inr (w, 0)))

private def c1 (m : Module.Free.ChooseBasisIndex ℤ I → ℤ) (w : {w : InfinitePlace F // w.IsComplex}) : ℝ :=
  modeForm F I m (stdBasis F (Sum.inr (w, 1)))

private def cC (m : Module.Free.ChooseBasisIndex ℤ I → ℤ) (w : {w : InfinitePlace F // w.IsComplex}) : ℝ :=
  Real.sqrt (c0 F I m w ^ 2 + c1 F I m w ^ 2)

private theorem cC_nonneg (m : Module.Free.ChooseBasisIndex ℤ I → ℤ) (w : {w : InfinitePlace F // w.IsComplex}) :
    0 ≤ cC F I m w := Real.sqrt_nonneg _

private theorem modeForm_eq_sum (m : Module.Free.ChooseBasisIndex ℤ I → ℤ) (x : mixedSpace F) :
    modeForm F I m x
      = (∑ v : {w : InfinitePlace F // w.IsReal}, x.1 v * cR F I m v)
        + ∑ w : {w : InfinitePlace F // w.IsComplex}, ((x.2 w).re * c0 F I m w + (x.2 w).im * c1 F I m w) := by
  conv_lhs => rw [← (stdBasis F).sum_repr x]
  rw [map_sum, Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_smul, smul_eq_mul, stdBasis_apply_isReal]
    rfl
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Fin.sum_univ_two, map_smul, map_smul, smul_eq_mul, smul_eq_mul, stdBasis_apply_isComplex_fst,
      stdBasis_apply_isComplex_snd]
    rfl

private theorem abs_re_mul_add_im_mul_le (u : ℂ) (p q : ℝ) :
    |u.re * p + u.im * q| ≤ ‖u‖ * Real.sqrt (p ^ 2 + q ^ 2) := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, ← Real.sqrt_mul (by positivity)]
  refine Real.abs_le_sqrt ?_
  nlinarith [sq_nonneg (u.re * q - u.im * p)]

private def basisSum : ℝ :=
  ∑ j : Module.Free.ChooseBasisIndex ℤ I,
    ((∑ v : {w : InfinitePlace F // w.IsReal}, |(idealBasis F I j).1 v|)
      + ∑ w : {w : InfinitePlace F // w.IsComplex}, ‖(idealBasis F I j).2 w‖)

private theorem basisSum_nonneg : 0 ≤ basisSum F I :=
  Finset.sum_nonneg fun _ _ => add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (Finset.sum_nonneg fun _ _ => norm_nonneg _)

private theorem abs_modeForm_mul_le (m : Module.Free.ChooseBasisIndex ℤ I → ℤ) (a : F) (x : mixedSpace F) :
    |modeForm F I m (mixedEmbedding F a * x)|
      ≤ (∑ v : {w : InfinitePlace F // w.IsReal}, (|cR F I m v| * v.1 a) * |x.1 v|)
        + ∑ w : {w : InfinitePlace F // w.IsComplex}, (cC F I m w * w.1 a) * ‖x.2 w‖ := by
  rw [modeForm_eq_sum]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun v _ => le_of_eq ?_)
    have h1 : (mixedEmbedding F a * x).1 v = embedding_of_isReal v.prop a * x.1 v := by
      show (mixedEmbedding F a).1 v * x.1 v = _
      rw [mixedEmbedding_apply_isReal]
    rw [h1, abs_mul, abs_mul, ← Real.norm_eq_abs (embedding_of_isReal v.prop a), norm_embedding_of_isReal]
    ring
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
    have h1 : (mixedEmbedding F a * x).2 w = w.1.embedding a * x.2 w := by
      show (mixedEmbedding F a).2 w * x.2 w = _
      rw [mixedEmbedding_apply_isComplex]
    rw [h1]
    refine (abs_re_mul_add_im_mul_le _ _ _).trans (le_of_eq ?_)
    rw [norm_mul, norm_embedding_eq]
    show w.1 a * ‖x.2 w‖ * cC F I m w = cC F I m w * w.1 a * ‖x.2 w‖
    ring

private theorem eq_zero_of_multiplier (m : Module.Free.ChooseBasisIndex ℤ I → ℤ) (a : 𝓞 F) (ha : a ≠ 0)
    (hR : ∀ v : {w : InfinitePlace F // w.IsReal}, |cR F I m v| * v.1 (a : F) < 1 / (basisSum F I + 1))
    (hC : ∀ w : {w : InfinitePlace F // w.IsComplex}, cC F I m w * w.1 (a : F) < 1 / (basisSum F I + 1)) :
    m = 0 := by
  set b := idealBasis F I with hb
  have hS := basisSum_nonneg F I
  have hS1 : 0 < basisSum F I + 1 := by linarith

  have hzero : ∀ j, modeForm F I m (mixedEmbedding F (a : F) * b j) = 0 := by
    intro j
    obtain ⟨z, hz⟩ := exists_int_modeForm_eq F I m
      (mul_mem_span_idealBasis F I a (Submodule.subset_span (Set.mem_range_self j)))
    have hlt : |modeForm F I m (mixedEmbedding F (a : F) * b j)| < 1 := by
      calc |modeForm F I m (mixedEmbedding F (a : F) * b j)|
          ≤ (∑ v : {w : InfinitePlace F // w.IsReal}, (|cR F I m v| * v.1 (a : F)) * |(b j).1 v|)
              + ∑ w : {w : InfinitePlace F // w.IsComplex}, (cC F I m w * w.1 (a : F)) * ‖(b j).2 w‖ :=
            abs_modeForm_mul_le F I m (a : F) (b j)
        _ ≤ (∑ v : {w : InfinitePlace F // w.IsReal}, (1 / (basisSum F I + 1)) * |(b j).1 v|)
              + ∑ w : {w : InfinitePlace F // w.IsComplex}, (1 / (basisSum F I + 1)) * ‖(b j).2 w‖ :=
            add_le_add (Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_right (hR v).le (abs_nonneg _))
              (Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_right (hC w).le (norm_nonneg _))
        _ = (1 / (basisSum F I + 1))
              * ((∑ v : {w : InfinitePlace F // w.IsReal}, |(b j).1 v|)
                  + ∑ w : {w : InfinitePlace F // w.IsComplex}, ‖(b j).2 w‖) := by
            rw [mul_add, Finset.mul_sum, Finset.mul_sum]
        _ ≤ (1 / (basisSum F I + 1)) * basisSum F I := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact Finset.single_le_sum
              (f := fun j => (∑ v : {w : InfinitePlace F // w.IsReal}, |(b j).1 v|)
                + ∑ w : {w : InfinitePlace F // w.IsComplex}, ‖(b j).2 w‖)
              (fun j _ => add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
                (Finset.sum_nonneg fun _ _ => norm_nonneg _)) (Finset.mem_univ j)
        _ < 1 := by rw [div_mul_eq_mul_div, one_mul, div_lt_one hS1]; linarith
    rw [hz] at hlt ⊢
    have : |z| < 1 := by exact_mod_cast hlt
    exact_mod_cast (Int.abs_lt_one_iff.mp this)

  have hall : ∀ x : mixedSpace F, modeForm F I m (mixedEmbedding F (a : F) * x) = 0 := by
    have hL : (modeForm F I m) ∘ₗ (LinearMap.mulLeft ℝ (mixedEmbedding F (a : F))) = 0 :=
      b.ext fun j => by rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, hzero j, LinearMap.zero_apply]
    intro x
    have := LinearMap.congr_fun hL x
    rwa [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.zero_apply] at this

  have ha' : (a : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr ha
  have hinv : mixedEmbedding F (a : F) * mixedEmbedding F (a : F)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ ha', map_one]
  have hmx : ∀ x : mixedSpace F, modeForm F I m x = 0 := fun x => by
    have := hall (mixedEmbedding F (a : F)⁻¹ * x)
    rwa [← mul_assoc, hinv, one_mul] at this

  funext j
  have := modeForm_basis F I m j
  rw [hmx] at this
  exact_mod_cast this.symm

private theorem exists_pos_le_prod :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ m : Module.Free.ChooseBasisIndex ℤ I → ℤ, m ≠ 0 →
      δ₀ ≤ (∏ v : {w : InfinitePlace F // w.IsReal}, |cR F I m v| ^ v.1.mult)
             * ∏ w : {w : InfinitePlace F // w.IsComplex}, cC F I m w ^ w.1.mult := by

  have hBk : minkowskiBound F 1 < ⊤ := minkowskiBound_lt_top F 1
  set Mb : ℝ := ((minkowskiBound F 1).toNNReal : ℝ) + 1 with hMb
  have hMb0 : 0 < Mb := by positivity
  set Φ : ℝ := (convexBodyLTFactor F : ℝ) with hΦ
  have hΦ0 : 0 < Φ := by
    have := one_le_convexBodyLTFactor F
    rw [hΦ]; exact_mod_cast zero_lt_one.trans_le this
  set ε : ℝ := 1 / (basisSum F I + 1) with hε
  have hε0 : 0 < ε := by have := basisSum_nonneg F I; positivity
  set n : ℕ := Module.finrank ℚ F with hn
  refine ⟨Φ * ε ^ n / Mb, by positivity, fun m hm => ?_⟩

  set K : InfinitePlace F → ℝ := fun w =>
    if hw : w.IsReal then |cR F I m ⟨w, hw⟩| else cC F I m ⟨w, not_isReal_iff_isComplex.mp hw⟩ with hK
  have hK0 : ∀ w, 0 ≤ K w := fun w => by
    rw [hK]; dsimp only; split_ifs
    · exact abs_nonneg _
    · exact cC_nonneg F I m _
  have hKR : ∀ v : {w : InfinitePlace F // w.IsReal}, K v.1 = |cR F I m v| := fun v => by
    rw [hK]; dsimp only; rw [dif_pos v.prop]
  have hKC : ∀ w : {w : InfinitePlace F // w.IsComplex}, K w.1 = cC F I m w := fun w => by
    rw [hK]; dsimp only; rw [dif_neg (not_isReal_iff_isComplex.mpr w.prop)]
  have hsplit : (∏ w : InfinitePlace F, K w ^ w.mult)
      = (∏ v : {w : InfinitePlace F // w.IsReal}, |cR F I m v| ^ v.1.mult)
          * ∏ w : {w : InfinitePlace F // w.IsComplex}, cC F I m w ^ w.1.mult := by
    rw [prod_eq_prod_mul_prod (fun w : InfinitePlace F => K w ^ w.mult)]
    congr 1
    · exact Finset.prod_congr rfl fun v _ => by rw [hKR]
    · exact Finset.prod_congr rfl fun w _ => by rw [hKC]
  by_contra hlt
  push Not at hlt
  rw [← hsplit] at hlt

  obtain ⟨η, hη, hη0⟩ : ∃ η : ℝ, (∏ w : InfinitePlace F, (max (K w) η) ^ w.mult) < Φ * ε ^ n / Mb ∧ 0 < η := by
    have hcont : Continuous fun η : ℝ => ∏ w : InfinitePlace F, (max (K w) η) ^ w.mult :=
      continuous_finsetProd _ fun w _ => (continuous_const.max continuous_id).pow _
    have h0 : (fun η : ℝ => ∏ w : InfinitePlace F, (max (K w) η) ^ w.mult) 0 < Φ * ε ^ n / Mb := by
      show (∏ w : InfinitePlace F, (max (K w) 0) ^ w.mult) < Φ * ε ^ n / Mb
      calc (∏ w : InfinitePlace F, (max (K w) 0) ^ w.mult) = ∏ w : InfinitePlace F, K w ^ w.mult :=
            Finset.prod_congr rfl fun w _ => by rw [max_eq_left (hK0 w)]
        _ < Φ * ε ^ n / Mb := hlt
    have hev : ∀ᶠ η in 𝓝 (0 : ℝ), (∏ w : InfinitePlace F, (max (K w) η) ^ w.mult) < Φ * ε ^ n / Mb :=
      hcont.continuousAt.eventually_lt_const h0
    exact ((hev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)))).exists
  have hM : ∀ w, 0 < max (K w) η := fun w => hη0.trans_le (le_max_right _ _)
  set P : ℝ := ∏ w : InfinitePlace F, (max (K w) η) ^ w.mult with hP
  have hP0 : 0 < P := Finset.prod_pos fun w _ => pow_pos (hM w) _

  let f : InfinitePlace F → ℝ≥0 := fun w => ⟨ε / max (K w) η, (div_pos hε0 (hM w)).le⟩
  have hf : ∀ w, ((f w : ℝ≥0) : ℝ) = ε / max (K w) η := fun w => rfl
  have hvol : minkowskiBound F 1 < volume (convexBodyLT F f) := by
    rw [convexBodyLT_volume, ← ENNReal.coe_mul, ← ENNReal.coe_toNNReal hBk.ne, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe,
      NNReal.coe_mul, NNReal.coe_prod]
    have hprod : ∏ w : InfinitePlace F, (((f w) ^ (w.mult) : ℝ≥0) : ℝ) = ε ^ n / P := by
      rw [hP]
      calc ∏ w : InfinitePlace F, (((f w) ^ (w.mult) : ℝ≥0) : ℝ) = ∏ w : InfinitePlace F, (ε / max (K w) η) ^ w.mult :=
            Finset.prod_congr rfl fun w _ => by rw [NNReal.coe_pow, hf]
        _ = ∏ w : InfinitePlace F, ε ^ w.mult / (max (K w) η) ^ w.mult :=
            Finset.prod_congr rfl fun w _ => by rw [div_pow]
        _ = (∏ w : InfinitePlace F, ε ^ w.mult) / ∏ w : InfinitePlace F, (max (K w) η) ^ w.mult := by
            rw [Finset.prod_div_distrib]
        _ = ε ^ n / ∏ w : InfinitePlace F, (max (K w) η) ^ w.mult := by
            rw [Finset.prod_pow_eq_pow_sum, sum_mult_eq]
    rw [hprod]
    show ((minkowskiBound F 1).toNNReal : ℝ) < Φ * (ε ^ n / P)
    have h1 : Mb < Φ * ε ^ n / P := by
      rw [lt_div_iff₀ hP0]
      have := (lt_div_iff₀ hMb0).mp hη
      linarith [this]
    have h2 : ((minkowskiBound F 1).toNNReal : ℝ) < Mb := by rw [hMb]; linarith
    rw [mul_div_assoc] at h1
    exact h2.trans h1
  obtain ⟨a, ha, hlt'⟩ := exists_ne_zero_mem_ringOfIntegers_lt F hvol

  refine hm (eq_zero_of_multiplier F I m a ha (fun v => ?_) (fun w => ?_))
  · have hva : v.1 (a : F) < ε / max (K v.1) η := by have := hlt' v.1; rwa [hf] at this
    rw [← hKR]
    calc K v.1 * v.1 (a : F) ≤ max (K v.1) η * v.1 (a : F) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (apply_nonneg v.1 _)
      _ < max (K v.1) η * (ε / max (K v.1) η) := mul_lt_mul_of_pos_left hva (hM v.1)
      _ = ε := mul_div_cancel₀ ε (hM v.1).ne'
  · have hwa : w.1 (a : F) < ε / max (K w.1) η := by have := hlt' w.1; rwa [hf] at this
    rw [← hKC]
    calc K w.1 * w.1 (a : F) ≤ max (K w.1) η * w.1 (a : F) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (apply_nonneg w.1 _)
      _ < max (K w.1) η * (ε / max (K w.1) η) := mul_lt_mul_of_pos_left hwa (hM w.1)
      _ = ε := mul_div_cancel₀ ε (hM w.1).ne'

private theorem exists_pos_le_prod_expanded :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ m : Module.Free.ChooseBasisIndex ℤ I → ℤ, m ≠ 0 →
      δ₀ ≤ (∏ w : {w : InfinitePlace F // w.IsReal},
              |∑ j, (m j : ℝ) * (fractionalIdealLatticeBasis F I).repr (stdBasis F (Sum.inl w)) j| ^ w.1.mult)
           * ∏ w : {w : InfinitePlace F // w.IsComplex},
             Real.sqrt ((∑ j, (m j : ℝ) * (fractionalIdealLatticeBasis F I).repr (stdBasis F (Sum.inr (w, 0))) j)^2
               + (∑ j, (m j : ℝ) * (fractionalIdealLatticeBasis F I).repr (stdBasis F (Sum.inr (w, 1))) j)^2)
               ^ w.1.mult := by
  obtain ⟨δ₀, h0, h⟩ := exists_pos_le_prod F I
  refine ⟨δ₀, h0, fun m hm => ?_⟩
  have h1 := h m hm
  simp only [cR, cC, c0, c1, modeForm_apply] at h1
  exact h1

end Arithmetic

end L4Sol

end

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding in
open scoped nonZeroDivisors in
open scoped Classical in
theorem solution
    {F : Type} [Field F] [NumberField F] (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    let L : (Module.Free.ChooseBasisIndex ℤ I → ℤ) → index F → ℝ := fun m i =>
      ∑ j, (m j : ℝ) * (fractionalIdealLatticeBasis F I).repr (stdBasis F i) j
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ m : Module.Free.ChooseBasisIndex ℤ I → ℤ, m ≠ 0 →
      δ₀ ≤ (∏ w : {w : InfinitePlace F // w.IsReal}, |L m (Sum.inl w)| ^ w.1.mult)
           * ∏ w : {w : InfinitePlace F // w.IsComplex},
             Real.sqrt ((L m (Sum.inr (w, 0)))^2 + (L m (Sum.inr (w, 1)))^2) ^ w.1.mult := by
  exact L4Sol.exists_pos_le_prod_expanded F I

end S_NumberField_mixedEmbedding_exists_pos_forall_le_prod_placeNorm_pow_mult_sum_mul_repr_stdBasis
end P2MW
export P2MW.S_NumberField_mixedEmbedding_exists_pos_forall_le_prod_placeNorm_pow_mult_sum_mul_repr_stdBasis (solution)
