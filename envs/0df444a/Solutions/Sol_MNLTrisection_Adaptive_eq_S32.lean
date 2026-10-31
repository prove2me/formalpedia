-- Prove2me | solution 1 for MNLTrisection.Adaptive.eq_S32
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T17:07:24.967928+00:00
-- url     : https://prove2.me/submissions/8fe217f3-d663-4622-bcbd-eff90c1cb985

import Mathlib
import Definitions.Def_UnderstandingML_Framework
import Definitions.Def_MNLTrisection_Adaptive_Model

namespace MNLTriProb

open MeasureTheory ProbabilityTheory UnderstandingML

variable {Ω : Type*} [MeasurableSpace Ω]

theorem coord_ae (D : Measure Ω) [IsProbabilityMeasure D] (n : ℕ) (i : Fin n)
    {p : Ω → Prop} (hp : ∀ᵐ x ∂D, p x) : ∀ᵐ ω ∂(iidLaw D n), p (ω i) := by
  have hmp := measurePreserving_eval (fun _ : Fin n => D) i
  have h2 : ∀ᵐ x ∂(Measure.map (fun ω : Fin n → Ω => ω i) (iidLaw D n)), p x := by
    unfold iidLaw; rw [hmp.map_eq]; exact hp
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable h2

theorem coord_integral (D : Measure Ω) [IsProbabilityMeasure D] (X : Ω → ℝ) (hX : Measurable X)
    (n : ℕ) (i : Fin n) : ∫ ω, X (ω i) ∂(iidLaw D n) = ∫ x, X x ∂D := by
  have hmp := measurePreserving_eval (fun _ : Fin n => D) i
  unfold iidLaw
  rw [← integral_map (measurable_pi_apply i).aemeasurable hX.aestronglyMeasurable, hmp.map_eq]

/-- One-sided Hoeffding inequality for a sub-sum of coordinates of an i.i.d. sample. -/
theorem hoeffding_upper (D : Measure Ω) [IsProbabilityMeasure D] (X : Ω → ℝ) (hX : Measurable X)
    {a b : ℝ} (hab : ∀ᵐ x ∂D, X x ∈ Set.Icc a b) (n : ℕ) (s : Finset (Fin n)) {ε : ℝ}
    (hε : 0 ≤ ε) :
    (iidLaw D n).real {ω | ε ≤ ∑ i ∈ s, (X (ω i) - ∫ x, X x ∂D)} ≤
      Real.exp (-(2 * ε ^ 2) / (s.card * (b - a) ^ 2)) := by
  haveI : IsProbabilityMeasure (iidLaw D n) := by unfold iidLaw; infer_instance
  have hind : iIndepFun (fun (i : Fin n) (ω : Fin n → Ω) => X (ω i) - ∫ x, X x ∂D)
      (iidLaw D n) := by
    have := iIndepFun_pi (μ := fun _ : Fin n => D) (X := fun _ x => X x - ∫ x, X x ∂D)
      (fun _ => (hX.sub_const _).aemeasurable)
    exact this
  have hsub : ∀ i ∈ s, HasSubgaussianMGF (fun ω : Fin n → Ω => X (ω i) - ∫ x, X x ∂D)
      ((‖b - a‖₊ / 2) ^ 2) (iidLaw D n) := by
    intro i _
    have h := hasSubgaussianMGF_of_mem_Icc (μ := iidLaw D n) (X := fun ω : Fin n → Ω => X (ω i))
      (a := a) (b := b) ((hX.comp (measurable_pi_apply i)).aemeasurable) (coord_ae D n i hab)
    rw [coord_integral D X hX n i] at h
    exact h
  have := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hsub hε
  refine this.trans (le_of_eq ?_)
  congr 1
  have hc : ((∑ i ∈ s, (‖b - a‖₊ / 2) ^ 2 : NNReal) : ℝ) = s.card * ((b - a) ^ 2 / 4) := by
    push_cast
    rw [Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [Real.norm_eq_abs, div_pow, sq_abs]
    ring
  rw [hc, show 2 * (↑s.card * ((b - a) ^ 2 / 4)) = (↑s.card * (b - a) ^ 2) / 2 by ring,
    div_div_eq_mul_div]
  ring

end MNLTriProb

namespace MNLTriS32

open MNLTrisection.Adaptive

theorem eps_succ (k : ℕ) : eps (k + 1) = 2 / 3 * eps k := by
  unfold eps; rw [pow_succ]; ring

theorem eps_pos (k : ℕ) : 0 < eps k := by unfold eps; positivity

theorem eps_zero : eps 0 = 1 / 3 := by simp [eps]

/-- `n ε² ≥ 8 ln(8 T ε²)`. -/
theorem nEpoch_ge (T τ : ℕ) :
    8 * Real.log (8 * T * eps τ ^ 2) ≤ (nEpoch T τ : ℝ) * eps τ ^ 2 := by
  have he := eps_pos τ
  set L := Real.log (8 * T * eps τ ^ 2)
  have h1 : ((eps τ)⁻¹ ^ 2 * L) ≤ (⌈(eps τ)⁻¹ ^ 2 * L⌉₊ : ℝ) := Nat.le_ceil _
  have h2n : 8 * ⌈(eps τ)⁻¹ ^ 2 * L⌉₊ ≤ nEpoch T τ := by
    unfold nEpoch innerLen; exact le_max_right _ _
  have h2 : (8 * ⌈(eps τ)⁻¹ ^ 2 * L⌉₊ : ℝ) ≤ (nEpoch T τ : ℝ) := by exact_mod_cast h2n
  have h3 : (eps τ)⁻¹ ^ 2 * eps τ ^ 2 = 1 := by field_simp
  have he2 : 0 < eps τ ^ 2 := by positivity
  calc 8 * L = 8 * ((eps τ)⁻¹ ^ 2 * L) * eps τ ^ 2 := by
        rw [show 8 * ((eps τ)⁻¹ ^ 2 * L) * eps τ ^ 2 = 8 * L * ((eps τ)⁻¹ ^ 2 * eps τ ^ 2) by ring,
          h3, mul_one]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ he2.le
        linarith

theorem nEpoch_pos (T τ : ℕ) : 1 ≤ nEpoch T τ := by
  unfold nEpoch innerLen; exact le_max_left _ _

/-- Key size fact: if epoch `τ` can start and `T ≥ 25` then `8 T ε_τ² ≥ 6/5`. -/
theorem x_ge (T τ : ℕ) (hT : 25 ≤ T) (hτ : ∑ τ' ∈ Finset.range τ, nEpoch T τ' < T) :
    6 / 5 ≤ 8 * (T : ℝ) * eps τ ^ 2 := by
  by_contra hcon
  push Not at hcon
  have hTpos : (25 : ℝ) ≤ T := by exact_mod_cast hT
  have hex : ∃ k, 8 * (T : ℝ) * eps k ^ 2 < 27 / 10 := ⟨τ, by linarith⟩
  classical
  let k := Nat.find hex
  have hk : 8 * (T : ℝ) * eps k ^ 2 < 27 / 10 := Nat.find_spec hex
  have hkτ : k ≤ τ := Nat.find_min' hex (by linarith)
  have hk0 : k ≠ 0 := by
    intro h0
    have : 8 * (T : ℝ) * eps 0 ^ 2 < 27 / 10 := h0 ▸ hk
    rw [eps_zero] at this
    linarith
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hjnot : ¬ (8 * (T : ℝ) * eps j ^ 2 < 27 / 10) := Nat.find_min hex (by omega)
  push Not at hjnot
  have hkj : eps k = 2 / 3 * eps j := by rw [hj, eps_succ]
  have hxk : 6 / 5 ≤ 8 * (T : ℝ) * eps k ^ 2 := by
    rw [hkj]; nlinarith
  have hkne : k ≠ τ := by
    intro he; rw [he] at hxk; linarith
  have hklt : k < τ := lt_of_le_of_ne hkτ hkne
  -- n_k > T
  set x := 8 * (T : ℝ) * eps k ^ 2 with hx
  have hlog : 1 - 1 / x ≤ Real.log x := by
    have := Real.one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < x)
    simpa [one_div] using this
  have hn := nEpoch_ge T k
  rw [← hx] at hn
  have hepos := eps_pos k
  have hxpos : 0 < x := by linarith
  -- n_k * eps^2 ≥ 8 log x ≥ 8 (1 - 1/x), and eps^2 = x/(8T)
  have he2 : eps k ^ 2 = x / (8 * T) := by rw [hx]; field_simp
  have hT0 : (0 : ℝ) < T := by linarith
  have hnx : (nEpoch T k : ℝ) * x = 8 * T * ((nEpoch T k : ℝ) * eps k ^ 2) := by
    rw [he2]; field_simp
  have hA : 64 * T * Real.log x ≤ (nEpoch T k : ℝ) * x := by
    have := mul_le_mul_of_nonneg_left hn (by positivity : (0 : ℝ) ≤ 8 * T)
    linarith
  have hB : x - 1 ≤ x * Real.log x := by
    have := mul_le_mul_of_nonneg_left hlog hxpos.le
    rw [mul_sub, mul_one, mul_one_div_cancel hxpos.ne'] at this
    exact this
  have hC : 64 * T * (x - 1) ≤ (nEpoch T k : ℝ) * x * x := by
    have h1 := mul_le_mul_of_nonneg_left hA hxpos.le
    have h2 := mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ 64 * T)
    nlinarith
  have hq : x * x < 64 * (x - 1) := by nlinarith
  have hnk : (T : ℝ) < nEpoch T k := by
    by_contra hle
    push Not at hle
    have h1 : (nEpoch T k : ℝ) * x * x ≤ T * x * x := by
      have := mul_le_mul_of_nonneg_right hle (by positivity : (0 : ℝ) ≤ x * x)
      linarith
    have h2 : (T : ℝ) * (64 * (x - 1) - x * x) ≤ 0 := by nlinarith
    have h3 : 0 < (T : ℝ) * (64 * (x - 1) - x * x) := mul_pos hT0 (by linarith)
    linarith
  have hsum : (nEpoch T k : ℝ) ≤ ∑ τ' ∈ Finset.range τ, (nEpoch T τ' : ℝ) :=
    Finset.single_le_sum (f := fun τ' => (nEpoch T τ' : ℝ)) (fun _ _ => by positivity)
      (Finset.mem_range.mpr hklt)
  have hτR : (∑ τ' ∈ Finset.range τ, (nEpoch T τ' : ℝ)) < T := by exact_mod_cast hτ
  linarith

/-- The confidence radius at `ℓ = n_τ` is at most `ε_τ / 2`. -/
theorem radius_le (T τ : ℕ) (hT : 25 ≤ T) (hτ : ∑ τ' ∈ Finset.range τ, nEpoch T τ' < T) :
    radius T (nEpoch T τ) ≤ eps τ / 2 := by
  have hx := x_ge T τ hT hτ
  have hn := nEpoch_ge T τ
  have hn1 := nEpoch_pos T τ
  have hepos := eps_pos τ
  set n := nEpoch T τ
  set x := 8 * (T : ℝ) * eps τ ^ 2 with hxdef
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlogx : (1 : ℝ) / 6 ≤ Real.log x := by
    have := Real.one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < x)
    have : 1 - x⁻¹ ≥ 1 / 6 := by
      rw [ge_iff_le, le_sub_comm, inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    linarith
  set u := (n : ℝ) * eps τ ^ 2 with hu
  have hu1 : 1 ≤ u := by linarith
  have hupos : 0 < u := by linarith
  -- 8T/n = x/u
  have hT0 : (0 : ℝ) < T := by
    have : (25 : ℝ) ≤ T := by exact_mod_cast hT
    linarith
  have hratio : 8 * (T : ℝ) / n = x / u := by
    rw [hxdef, hu]; field_simp
  have hlog_le : Real.log (8 * (T : ℝ) / n) ≤ u / 8 := by
    rw [hratio, Real.log_div (by positivity) (by positivity)]
    have := Real.log_nonneg hu1
    linarith
  unfold radius
  rw [show (eps τ / 2) = Real.sqrt ((eps τ / 2) ^ 2) by
    rw [Real.sqrt_sq (by positivity)]]
  apply Real.sqrt_le_sqrt
  rw [div_le_iff₀ hnpos]
  calc 2 * Real.log (8 * (T : ℝ) / n) ≤ 2 * (u / 8) := by linarith
    _ = (eps τ / 2) ^ 2 * n := by rw [hu]; ring

end MNLTriS32

open MeasureTheory UnderstandingML MNLTrisection.Adaptive in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (D : Measure Ω) [IsProbabilityMeasure D]
    (X : Ω → ℝ) (hX : Measurable X) (hX01 : ∀ᵐ ω ∂D, X ω ∈ Set.Icc (0 : ℝ) 1)
    (y : ℝ) (T τ : ℕ) (hT : 25 ≤ T) (hτ : ∑ τ' ∈ Finset.range τ, nEpoch T τ' < T)
    (hΔ : eps τ ≤ y - ∫ x, X x ∂D) :
    iidLaw D (nEpoch T τ) {ω | ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ nEpoch T τ →
        y ≤ (∑ i ∈ Finset.univ.filter (fun i : Fin (nEpoch T τ) => (i : ℕ) < ℓ), X (ω i)) / ℓ +
          radius T ℓ} ≤
      ENNReal.ofReal (Real.exp (-((nEpoch T τ : ℝ) * (y - ∫ x, X x ∂D) ^ 2 / 2))) := by
  set n := nEpoch T τ with hn
  set μ := ∫ x, X x ∂D
  set Δ := y - μ with hΔdef
  have hn1 : 1 ≤ n := MNLTriS32.nEpoch_pos T τ
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hrad := MNLTriS32.radius_le T τ hT hτ
  have hepos := MNLTriS32.eps_pos τ
  haveI : IsProbabilityMeasure (iidLaw D n) := by unfold iidLaw; infer_instance
  have hsub : {ω : Fin n → Ω | ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ n →
        y ≤ (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < ℓ), X (ω i)) / ℓ +
          radius T ℓ} ⊆
      {ω | (n : ℝ) * Δ / 2 ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)), (X (ω i) - μ)} := by
    intro ω hω
    have h := hω n hn1 le_rfl
    have hfil : Finset.univ.filter (fun i : Fin n => (i : ℕ) < n) = Finset.univ := by
      ext i; simp [i.isLt]
    rw [hfil] at h
    simp only [Set.mem_setOf_eq]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have h2 : (y - radius T n) * n ≤ ∑ i, X (ω i) := by
      have := sub_le_iff_le_add.mpr h
      rwa [le_div_iff₀ hnpos] at this
    nlinarith
  have hΔpos : 0 < Δ := by linarith
  have hεnn : (0 : ℝ) ≤ (n : ℝ) * Δ / 2 := by positivity
  have hH := MNLTriProb.hoeffding_upper D X hX hX01 n Finset.univ hεnn
  calc iidLaw D n _ ≤ iidLaw D n {ω | (n : ℝ) * Δ / 2 ≤
        ∑ i ∈ (Finset.univ : Finset (Fin n)), (X (ω i) - μ)} := measure_mono hsub
    _ = ENNReal.ofReal ((iidLaw D n).real {ω | (n : ℝ) * Δ / 2 ≤
        ∑ i ∈ (Finset.univ : Finset (Fin n)), (X (ω i) - μ)}) := by
        rw [ofReal_measureReal]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        refine hH.trans (le_of_eq ?_)
        congr 1
        rw [Finset.card_univ, Fintype.card_fin]
        field_simp
        ring
