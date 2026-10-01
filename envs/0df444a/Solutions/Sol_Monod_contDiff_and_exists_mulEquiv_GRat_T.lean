-- Prove2me | solution 1 for Monod.contDiff_and_exists_mulEquiv_GRat_T
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-30T14:46:39.206127+00:00
-- url     : https://prove2.me/submissions/281c710b-b6e1-4533-ae60-1faded3500b2

import Theorems.Thm_CannonFloydParry_exists_toCircle_eq_of_mem_T_of_apply_zero
import Definitions.Def_Monod_PiecewiseProjective
import Mathlib
import Definitions.Def_CannonFloydParry_PIP
import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Theorems.Thm_CannonFloydParry_exists_isReduced_represents
import Definitions.Def_CannonFloydParry_T
import Theorems.Thm_CannonFloydParry_mem_T_iff_isThompsonCircle
import Theorems.Thm_CannonFloydParry_closure_range_symT_eq_T_and_relations
import Theorems.Thm_CannonFloydParry_mem_F_iff_isThompson
import Theorems.Thm_CannonFloydParry_bijOn_dyadic

section
/-!
# Real Möbius maps from `SL(2, ℤ)`, and maps that are locally Möbius off finitely many rationals
-/

namespace Monod.Dev.Thur

open OnePoint Filter Topology Set

abbrev SL2Z := Matrix.SpecialLinearGroup (Fin 2) ℤ

/-- `SL(2, ℤ) → SL(2, ⊥)`, with `⊥` the subring `ℤ` of `ℝ`. -/
noncomputable def ι : SL2Z →* Matrix.SpecialLinearGroup (Fin 2) (⊥ : Subring ℝ) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom _)

lemma slToGL_ι (M : SL2Z) (i j : Fin 2) :
    ((slToGL ⊥ (ι M) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = (M.1 i j : ℝ) := by
  simp [slToGL, ι]

/-- Numerator, denominator and value of the real Möbius map of `M`. -/
def nR (M : SL2Z) (x : ℝ) : ℝ := (M.1 0 0 : ℝ) * x + M.1 0 1
def dR (M : SL2Z) (x : ℝ) : ℝ := (M.1 1 0 : ℝ) * x + M.1 1 1
noncomputable def mR (M : SL2Z) (x : ℝ) : ℝ := nR M x / dR M x

lemma detZ (M : SL2Z) : M.1 0 0 * M.1 1 1 - M.1 0 1 * M.1 1 0 = 1 := by
  have := M.2; rwa [Matrix.det_fin_two] at this

lemma detR (M : SL2Z) : (M.1 0 0 : ℝ) * M.1 1 1 - (M.1 0 1 : ℝ) * M.1 1 0 = 1 := by
  exact_mod_cast detZ M

lemma mul_entry (M N : SL2Z) (i j : Fin 2) :
    (M * N).1 i j = M.1 i 0 * N.1 0 j + M.1 i 1 * N.1 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma nR_mul (M N : SL2Z) (x : ℝ) :
    nR (M * N) x = (M.1 0 0 : ℝ) * nR N x + M.1 0 1 * dR N x := by
  simp only [nR, dR, mul_entry]; push_cast; ring

lemma dR_mul (M N : SL2Z) (x : ℝ) :
    dR (M * N) x = (M.1 1 0 : ℝ) * nR N x + M.1 1 1 * dR N x := by
  simp only [nR, dR, mul_entry]; push_cast; ring

lemma dR_mul' (M N : SL2Z) {x : ℝ} (h : dR N x ≠ 0) :
    dR (M * N) x = dR M (mR N x) * dR N x := by
  rw [dR_mul, mR]
  simp only [dR] at h ⊢
  field_simp

lemma mR_mul (M N : SL2Z) {x : ℝ} (h : dR N x ≠ 0) : mR (M * N) x = mR M (mR N x) := by
  rw [mR, nR_mul, dR_mul]
  show _ = nR M (nR N x / dR N x) / dR M (nR N x / dR N x)
  generalize nR N x = n
  generalize dR N x = d at h ⊢
  simp only [nR, dR]
  have e1 : (M.1 0 0 : ℝ) * (n / d) + M.1 0 1 = ((M.1 0 0 : ℝ) * n + M.1 0 1 * d) / d := by
    field_simp
  have e2 : (M.1 1 0 : ℝ) * (n / d) + M.1 1 1 = ((M.1 1 0 : ℝ) * n + M.1 1 1 * d) / d := by
    field_simp
  rw [e1, e2, div_div_div_cancel_right₀ h]

lemma continuous_dR (M : SL2Z) : Continuous (dR M) := by
  unfold dR; fun_prop

lemma continuous_nR (M : SL2Z) : Continuous (nR M) := by
  unfold nR; fun_prop

lemma eventually_dR_ne (M : SL2Z) {x : ℝ} (h : dR M x ≠ 0) : ∀ᶠ y in 𝓝 x, dR M y ≠ 0 :=
  (continuous_dR M).continuousAt.eventually_ne h

/-- `mR M` increases: `mR M y - mR M x = (y - x) / (dR M x * dR M y)`. -/
lemma mR_sub (M : SL2Z) {x y : ℝ} (hx : dR M x ≠ 0) (hy : dR M y ≠ 0) :
    mR M y - mR M x = (y - x) / (dR M x * dR M y) := by
  have := detR M
  rw [mR, mR, div_sub_div _ _ hy hx, div_eq_div_iff (mul_ne_zero hy hx) (mul_ne_zero hx hy)]
  simp only [nR, dR]
  linear_combination (y - x) * ((M.1 1 0 : ℝ) * x + M.1 1 1) * ((M.1 1 0 : ℝ) * y + M.1 1 1) * this

/-- The value at a rational point of `mR M` is rational only at rational points. -/
lemma rat_of_mR (M : SL2Z) {x : ℝ} (hx : dR M x ≠ 0) {q : ℚ} (hq : mR M x = q) :
    ∃ q' : ℚ, x = q' := by
  have hdet := detR M
  have e : (M.1 0 0 : ℝ) * x + M.1 0 1 = q * ((M.1 1 0 : ℝ) * x + M.1 1 1) := by
    have := hq
    rw [mR, div_eq_iff hx] at this
    simpa only [nR, dR] using this
  have hne : (M.1 0 0 : ℝ) - q * M.1 1 0 ≠ 0 := by
    intro h0
    have : ((M.1 0 0 : ℝ) - q * M.1 1 0) * ((M.1 1 0 : ℝ) * x + M.1 1 1) = 1 := by
      linear_combination hdet + (M.1 1 0 : ℝ) * e
    rw [h0, zero_mul] at this; exact zero_ne_one this
  refine ⟨((q * M.1 1 1 - M.1 0 1) / (M.1 0 0 - q * M.1 1 0) : ℚ), ?_⟩
  push_cast
  field_simp
  linear_combination e

lemma rat_mR (M : SL2Z) (q : ℚ) : ∃ q' : ℚ, mR M q = q' := by
  refine ⟨(M.1 0 0 * q + M.1 0 1) / (M.1 1 0 * q + M.1 1 1), ?_⟩
  simp [mR, nR, dR]

/-! ### Two Möbius maps agreeing near a point -/

lemma quad_zero {A B C y₁ y₂ y₃ : ℝ} (h12 : y₁ ≠ y₂) (h13 : y₁ ≠ y₃) (h23 : y₂ ≠ y₃)
    (e₁ : A * y₁ ^ 2 + B * y₁ + C = 0) (e₂ : A * y₂ ^ 2 + B * y₂ + C = 0)
    (e₃ : A * y₃ ^ 2 + B * y₃ + C = 0) : A = 0 ∧ B = 0 ∧ C = 0 := by
  have f₁ : A * (y₁ + y₂) + B = 0 := by
    have : (y₁ - y₂) * (A * (y₁ + y₂) + B) = 0 := by linear_combination e₁ - e₂
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h12)
  have f₂ : A * (y₁ + y₃) + B = 0 := by
    have : (y₁ - y₃) * (A * (y₁ + y₃) + B) = 0 := by linear_combination e₁ - e₃
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h13)
  have hA : A = 0 := by
    have : (y₂ - y₃) * A = 0 := by linear_combination f₁ - f₂
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h23)
  subst hA
  have hB : B = 0 := by linarith
  subst hB
  exact ⟨rfl, rfl, by linarith⟩

/-- `N = ± M`. -/
def PM (M N : SL2Z) : Prop := ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ i j, N.1 i j = s * M.1 i j

lemma PM.symm {M N : SL2Z} (h : PM M N) : PM N M := by
  obtain ⟨s, hs, h⟩ := h
  refine ⟨s, hs, fun i j => ?_⟩
  rw [h]; rcases hs with rfl | rfl <;> ring

lemma PM.dR_eq {M N : SL2Z} (h : PM M N) (x : ℝ) : ∃ s : ℝ, s ≠ 0 ∧ dR N x = s * dR M x := by
  obtain ⟨s, hs, h⟩ := h
  refine ⟨s, by rcases hs with rfl | rfl <;> norm_num, ?_⟩
  simp only [Monod.Dev.Thur.dR, h]; push_cast; ring

lemma PM.dR_ne {M N : SL2Z} (h : PM M N) {x : ℝ} (hx : dR M x ≠ 0) : dR N x ≠ 0 := by
  obtain ⟨s, hs, e⟩ := h.dR_eq x
  rw [e]; exact mul_ne_zero hs hx

lemma PM.mR_eq {M N : SL2Z} (h : PM M N) : mR N = mR M := by
  funext x
  obtain ⟨s, hs, h⟩ := h
  have hs' : (s : ℝ) ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  simp only [Monod.Dev.Thur.mR, nR, Monod.Dev.Thur.dR, h]
  push_cast
  rw [show (s : ℝ) * M.1 0 0 * x + s * M.1 0 1 = s * ((M.1 0 0 : ℝ) * x + M.1 0 1) by ring,
    show (s : ℝ) * M.1 1 0 * x + s * M.1 1 1 = s * ((M.1 1 0 : ℝ) * x + M.1 1 1) by ring,
    mul_div_mul_left _ _ hs']

lemma pm_of_eq (a b c d a' b' c' d' : ℤ) (hD : a * d - b * c = 1) (hD' : a' * d' - b' * c' = 1)
    (E1 : a * c' = a' * c) (E2 : a * d' + b * c' = a' * d + b' * c) (E3 : b * d' = b' * d) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ a' = s * a ∧ b' = s * b ∧ c' = s * c ∧ d' = s * d := by
  set s := a' * d - b * c' with hs
  have h1 : a' = s * a := by linear_combination (-a') * hD + b * E1
  have h2 : b' = s * b := by linear_combination (-b') * hD - a * E3 + b * E2
  have h3 : c' = s * c := by linear_combination (-c') * hD + d * E1
  have h4 : d' = s * d := by linear_combination (-d') * hD + d * E2 - c * E3
  have hss : s * s = 1 := by
    rw [h1, h2, h3, h4] at hD'
    linear_combination hD' - s * s * hD
  exact ⟨s, Int.eq_one_or_neg_one_of_mul_eq_one hss, h1, h2, h3, h4⟩

/-- Two Möbius maps of `SL(2, ℤ)` agreeing near a point where both are finite are `±` each
other. -/
lemma pm_of_eventually {M N : SL2Z} {x : ℝ} (hM : dR M x ≠ 0) (hN : dR N x ≠ 0)
    (h : ∀ᶠ y in 𝓝 x, mR M y = mR N y) : PM M N := by
  have h' : ∀ᶠ y in 𝓝 x, mR M y = mR N y ∧ dR M y ≠ 0 ∧ dR N y ≠ 0 :=
    h.and ((eventually_dR_ne M hM).and (eventually_dR_ne N hN))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h'
  have key : ∀ y, dist y x < ε → nR M y * dR N y - nR N y * dR M y = 0 := by
    intro y hy
    obtain ⟨e, h1, h2⟩ := hball hy
    have : nR M y / dR M y = nR N y / dR N y := e
    rw [div_eq_div_iff h1 h2] at this
    linarith
  have d1 : dist x x < ε := by simpa using hε
  have d2 : dist (x + ε / 2) x < ε := by
    rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith
  have d3 : dist (x + ε / 3) x < ε := by
    rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith
  set a := M.1 0 0; set b := M.1 0 1; set c := M.1 1 0; set d := M.1 1 1
  set a' := N.1 0 0; set b' := N.1 0 1; set c' := N.1 1 0; set d' := N.1 1 1
  have expand : ∀ y, nR M y * dR N y - nR N y * dR M y =
      ((a : ℝ) * c' - a' * c) * y ^ 2 + ((a : ℝ) * d' + b * c' - a' * d - b' * c) * y +
        ((b : ℝ) * d' - b' * d) := by
    intro y; simp only [nR, Monod.Dev.Thur.dR]; ring
  have k1 := key x d1; have k2 := key _ d2; have k3 := key _ d3
  rw [expand] at k1 k2 k3
  obtain ⟨E1, E2, E3⟩ := quad_zero (by linarith) (by linarith) (by linarith) k1 k2 k3
  have E1' : a * c' = a' * c := by
    have : ((a * c' - a' * c : ℤ) : ℝ) = 0 := by push_cast; exact E1
    have := Int.cast_eq_zero.mp this; linarith
  have E2' : a * d' + b * c' = a' * d + b' * c := by
    have : ((a * d' + b * c' - a' * d - b' * c : ℤ) : ℝ) = 0 := by push_cast; exact E2
    have := Int.cast_eq_zero.mp this; linarith
  have E3' : b * d' = b' * d := by
    have : ((b * d' - b' * d : ℤ) : ℝ) = 0 := by push_cast; exact E3
    have := Int.cast_eq_zero.mp this; linarith
  obtain ⟨s, hs, h1, h2, h3, h4⟩ := pm_of_eq a b c d a' b' c' d' (detZ M) (detZ N) E1' E2' E3'
  refine ⟨s, hs, fun i j => ?_⟩
  fin_cases i <;> fin_cases j
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-! ### Locally Möbius maps -/

/-- `f` is **locally Möbius** on `U` off finitely many rationals: near every other point of `U`
it agrees with the Möbius map of an element of `SL(2, ℤ)` that is finite there. -/
def LM (U : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ R : Set ℝ, R.Finite ∧ (∀ r ∈ R, ∃ q : ℚ, r = q) ∧
    ∀ x ∈ U, x ∉ R → ∃ M : SL2Z, dR M x ≠ 0 ∧ ∀ᶠ y in 𝓝 x, f y = mR M y

lemma LM.mono {U V : Set ℝ} {f : ℝ → ℝ} (h : LM V f) (hUV : U ⊆ V) : LM U f := by
  obtain ⟨R, h1, h2, h3⟩ := h
  exact ⟨R, h1, h2, fun x hx => h3 x (hUV hx)⟩

lemma LM.congr {U : Set ℝ} {f g : ℝ → ℝ} (hU : IsOpen U) (h : LM U f) (he : EqOn f g U) :
    LM U g := by
  obtain ⟨R, h1, h2, h3⟩ := h
  refine ⟨R, h1, h2, fun x hx hxR => ?_⟩
  obtain ⟨M, hM, hev⟩ := h3 x hx hxR
  refine ⟨M, hM, ?_⟩
  filter_upwards [hev, hU.mem_nhds hx] with y hy hyU
  rw [← he hyU, hy]

lemma LM.comp {U V : Set ℝ} {f g : ℝ → ℝ} (hU : IsOpen U) (hf : LM U f) (hg : LM V g)
    (hc : ContinuousOn f U) (hmaps : MapsTo f U V) (hinj : InjOn f U) : LM U (g ∘ f) := by
  obtain ⟨Rf, hRf, hRfq, hf⟩ := hf
  obtain ⟨Rg, hRg, hRgq, hg⟩ := hg
  refine ⟨Rf ∪ (U ∩ f ⁻¹' Rg), hRf.union ?_, ?_, ?_⟩
  · refine Set.Finite.of_finite_image (hRg.subset ?_) (hinj.mono inter_subset_left)
    rintro _ ⟨y, hy, rfl⟩; exact hy.2
  · rintro r (hr | ⟨hrU, hrg⟩)
    · exact hRfq r hr
    · by_cases hr' : r ∈ Rf
      · exact hRfq r hr'
      · obtain ⟨M, hM, hev⟩ := hf r hrU hr'
        obtain ⟨q, hq⟩ := hRgq _ hrg
        exact rat_of_mR M hM (hev.self_of_nhds ▸ hq)
  · intro x hx hxR
    simp only [mem_union, mem_inter_iff, mem_preimage, not_or, not_and] at hxR
    obtain ⟨M, hM, hev⟩ := hf x hx hxR.1
    obtain ⟨N, hN, hevg⟩ := hg (f x) (hmaps hx) (hxR.2 hx)
    have hfx : f x = mR M x := hev.self_of_nhds
    have hcont : ContinuousAt f x := hc.continuousAt (hU.mem_nhds hx)
    have hevg' : ∀ᶠ y in 𝓝 x, g (f y) = mR N (f y) := hcont.eventually hevg
    refine ⟨N * M, ?_, ?_⟩
    · rw [dR_mul' N M hM, ← hfx]; exact mul_ne_zero hN hM
    · filter_upwards [hev, hevg', eventually_dR_ne M hM] with y h1 h2 h3
      rw [Function.comp_apply, h2, h1, mR_mul N M h3]

/-! ### The identity theorem on a preconnected open set -/

lemma single_of_local {S : Set ℝ} (hS : IsPreconnected S) {x₀ : ℝ}
    (hx₀ : x₀ ∈ S) {f : ℝ → ℝ}
    (hf : ∀ x ∈ S, ∃ M : SL2Z, dR M x ≠ 0 ∧ ∀ᶠ y in 𝓝 x, f y = mR M y) :
    ∃ M : SL2Z, ∀ x ∈ S, dR M x ≠ 0 ∧ f x = mR M x := by
  classical
  choose! Mx hMx using hf
  let F : S → Set (Matrix (Fin 2) (Fin 2) ℤ) := fun x => {(Mx x).1, -(Mx x).1}
  have hPM : ∀ x y : S, PM (Mx x) (Mx y) → F y = F x := by
    intro x y ⟨s, hs, h⟩
    have e : (Mx y).1 = s • (Mx x).1 := by ext i j; simp [h i j]
    simp only [F, e]
    rcases hs with rfl | rfl
    · simp
    · simp [Set.pair_comm]
  have hloc : IsLocallyConstant F := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨x, hx⟩
    obtain ⟨hMd, hev⟩ := hMx x hx
    have hev2 : ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, f z = mR (Mx x) z := hev.eventually_nhds
    have : ∀ᶠ y in 𝓝 x, ∀ hyS : y ∈ S, F ⟨y, hyS⟩ = F ⟨x, hx⟩ := by
      filter_upwards [hev2, eventually_dR_ne _ hMd] with y hy hyd hyS
      obtain ⟨hMy, hevy⟩ := hMx y hyS
      refine hPM ⟨x, hx⟩ ⟨y, hyS⟩ (pm_of_eventually hyd hMy ?_)
      filter_upwards [hy, hevy] with z h1 h2
      rw [← h1, ← h2]
    rw [nhds_subtype_eq_comap]
    exact (this.filter_mono le_rfl).comap _ |>.mono fun y hy => hy y.2
  have := Subtype.preconnectedSpace hS
  refine ⟨Mx x₀, fun x hx => ?_⟩
  have hFeq := hloc.apply_eq_of_isPreconnected isPreconnected_univ (x := ⟨x, hx⟩)
    (y := ⟨x₀, hx₀⟩) trivial trivial
  have hmem : (Mx x₀).1 ∈ F ⟨x, hx⟩ := by rw [hFeq]; simp [F]
  have hpm : PM (Mx x) (Mx x₀) := by
    rcases hmem with h | h
    · exact ⟨1, Or.inl rfl, fun i j => by rw [h]; simp⟩
    · refine ⟨-1, Or.inr rfl, fun i j => ?_⟩
      rw [Set.mem_singleton_iff] at h; rw [h]; simp
  obtain ⟨hd, hev⟩ := hMx x hx
  exact ⟨hpm.dR_ne hd, by rw [hpm.mR_eq]; exact hev.self_of_nhds⟩

/-- At an end of an interval where `f = mR M`, continuity forces `mR M` to be finite and to agree
with `f`. -/
lemma endpoint_of_within {f : ℝ → ℝ} {M : SL2Z} {a : ℝ} {s : Set ℝ} [(𝓝[s] a).NeBot]
    (h : ∀ x ∈ s, dR M x ≠ 0 ∧ f x = mR M x) (hc : ContinuousWithinAt f s a) :
    dR M a ≠ 0 ∧ f a = mR M a := by
  have hφ : ContinuousWithinAt (fun y => f y * dR M y - nR M y) s a :=
    (hc.mul (continuous_dR M).continuousWithinAt).sub (continuous_nR M).continuousWithinAt
  have hzero : ∀ᶠ y in 𝓝[s] a, f y * dR M y - nR M y = 0 := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    obtain ⟨h1, h2⟩ := h y hy
    rw [h2, mR, div_mul_cancel₀ _ h1, sub_self]
  have hlim : f a * dR M a - nR M a = 0 :=
    tendsto_nhds_unique hφ (tendsto_const_nhds.congr' (hzero.mono fun y hy => hy.symm))
  have hdet := detR M
  have hd : dR M a ≠ 0 := by
    intro hd
    rw [hd, mul_zero, zero_sub, neg_eq_zero] at hlim
    unfold dR at hd; unfold nR at hlim
    have : (M.1 0 0 : ℝ) * ((M.1 1 0 : ℝ) * a + M.1 1 1) -
        (M.1 1 0 : ℝ) * ((M.1 0 0 : ℝ) * a + M.1 0 1) = 1 := by linear_combination hdet
    rw [hd, hlim] at this; simp at this
  refine ⟨hd, ?_⟩
  rw [mR, eq_div_iff hd]; linarith

end Monod.Dev.Thur
end

section
/-!
# The identification `τ : (0,1) → ℝ`

`τ t = (2t - 1)/t` on `(0, 1/2]` and `(2t - 1)/(1 - t)` on `[1/2, 1)`, with inverse
`τi x = 1/(2 - x)` on `(-∞, 0]` and `(1 + x)/(2 + x)` on `[0, ∞)`; both pieces of both are Möbius
maps of `SL(2, ℤ)`.
-/

namespace Monod.Dev.Thur

open OnePoint Filter Topology Set

/-- An element of `SL(2, ℤ)` from its entries. -/
def mk (a b c d : ℤ) (h : a * d - b * c = 1) : SL2Z :=
  ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h⟩

@[simp] lemma mk_00 (a b c d : ℤ) (h) : (mk a b c d h).1 0 0 = a := rfl
@[simp] lemma mk_01 (a b c d : ℤ) (h) : (mk a b c d h).1 0 1 = b := rfl
@[simp] lemma mk_10 (a b c d : ℤ) (h) : (mk a b c d h).1 1 0 = c := rfl
@[simp] lemma mk_11 (a b c d : ℤ) (h) : (mk a b c d h).1 1 1 = d := rfl

lemma mR_mk (a b c d : ℤ) (h) (x : ℝ) :
    mR (mk a b c d h) x = ((a : ℝ) * x + b) / ((c : ℝ) * x + d) := by
  simp [mR, nR, dR]

lemma dR_mk (a b c d : ℤ) (h) (x : ℝ) : dR (mk a b c d h) x = (c : ℝ) * x + d := by
  simp [dR]

noncomputable def τ (t : ℝ) : ℝ := if t ≤ 1 / 2 then (2 * t - 1) / t else (2 * t - 1) / (1 - t)

noncomputable def τi (x : ℝ) : ℝ := if x ≤ 0 then 1 / (2 - x) else (1 + x) / (2 + x)

lemma τ_of_le {t : ℝ} (h : t ≤ 1 / 2) : τ t = (2 * t - 1) / t := if_pos h
lemma τ_of_ge {t : ℝ} (h : 1 / 2 ≤ t) : τ t = (2 * t - 1) / (1 - t) := by
  unfold τ; split_ifs with h'
  · have : t = 1 / 2 := le_antisymm h' h
    subst this; norm_num
  · rfl
lemma τi_of_le {x : ℝ} (h : x ≤ 0) : τi x = 1 / (2 - x) := if_pos h
lemma τi_of_ge {x : ℝ} (h : 0 ≤ x) : τi x = (1 + x) / (2 + x) := by
  unfold τi; split_ifs with h'
  · have : x = 0 := le_antisymm h' h
    subst this; norm_num
  · rfl

lemma τi_mem (x : ℝ) : τi x ∈ Ioo (0 : ℝ) 1 := by
  rcases le_total x 0 with h | h
  · rw [τi_of_le h]
    have : 0 < 2 - x := by linarith
    exact ⟨by positivity, by rw [div_lt_one this]; linarith⟩
  · rw [τi_of_ge h]
    have : 0 < 2 + x := by linarith
    exact ⟨by positivity, by rw [div_lt_one this]; linarith⟩

lemma τi_le_half_iff (x : ℝ) : τi x ≤ 1 / 2 ↔ x ≤ 0 := by
  rcases le_total x 0 with h | h
  · rw [τi_of_le h]
    have : 0 < 2 - x := by linarith
    simp only [h, iff_true]
    rw [div_le_iff₀ this]; linarith
  · rw [τi_of_ge h]
    have : 0 < 2 + x := by linarith
    rw [div_le_iff₀ this]
    constructor <;> intro h' <;> linarith

lemma τ_τi (x : ℝ) : τ (τi x) = x := by
  rcases le_total x 0 with h | h
  · rw [τ_of_le ((τi_le_half_iff x).2 h), τi_of_le h]
    have : 2 - x ≠ 0 := by linarith
    field_simp; ring
  · have h2 : 1 / 2 ≤ τi x := by
      rw [τi_of_ge h]; have : 0 < 2 + x := by linarith
      rw [le_div_iff₀ this]; linarith
    rw [τ_of_ge h2, τi_of_ge h]
    have : 2 + x ≠ 0 := by linarith
    have : 1 - (1 + x) / (2 + x) ≠ 0 := by
      rw [sub_ne_zero]; intro e; rw [eq_div_iff ‹_›] at e; linarith
    field_simp; ring

lemma τ_le_zero_iff {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : τ t ≤ 0 ↔ t ≤ 1 / 2 := by
  obtain ⟨h0, h1⟩ := ht
  rcases le_total t (1 / 2) with h | h
  · rw [τ_of_le h]; simp only [h, iff_true]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) h0.le
  · rw [τ_of_ge h]
    constructor
    · intro h'
      have : 0 ≤ (2 * t - 1) / (1 - t) := div_nonneg (by linarith) (by linarith)
      have : 2 * t - 1 = 0 := by
        have := le_antisymm h' this
        rcases div_eq_zero_iff.mp this with h'' | h''
        · exact h''
        · linarith
      linarith
    · intro h'; have : t = 1 / 2 := le_antisymm h' h
      subst this; norm_num

lemma τi_τ {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : τi (τ t) = t := by
  obtain ⟨h0, h1⟩ := ht
  rcases le_total t (1 / 2) with h | h
  · have hn : τ t ≤ 0 := (τ_le_zero_iff ⟨h0, h1⟩).2 h
    rw [τi_of_le hn, τ_of_le h]
    have : t ≠ 0 := h0.ne'
    field_simp; ring
  · have hn : 0 ≤ τ t := by rw [τ_of_ge h]; exact div_nonneg (by linarith) (by linarith)
    rw [τi_of_ge hn, τ_of_ge h]
    have : 1 - t ≠ 0 := by linarith
    field_simp; ring

lemma τi_strictMono : StrictMono τi := by
  intro x y hxy
  rcases le_total y 0 with hy | hy
  · rw [τi_of_le hy, τi_of_le (hxy.le.trans hy)]
    apply one_div_lt_one_div_of_lt <;> linarith
  · rcases le_total x 0 with hx | hx
    · have h1 := (τi_le_half_iff x).2 hx
      have : 1 / 2 ≤ τi y := by
        rw [τi_of_ge hy]; have : 0 < 2 + y := by linarith
        rw [le_div_iff₀ this]; linarith
      rcases lt_or_eq_of_le (h1.trans this) with h | h
      · exact h
      · exfalso
        rw [τi_of_le hx, τi_of_ge hy, div_eq_div_iff (by linarith) (by linarith)] at h
        nlinarith
    · rw [τi_of_ge hy, τi_of_ge hx, div_lt_div_iff₀ (by linarith) (by linarith)]
      nlinarith

lemma continuous_τi : Continuous τi := by
  unfold τi
  refine continuous_if_le continuous_id continuous_const ?_ ?_ ?_
  · refine continuousOn_const.div (continuousOn_const.sub continuousOn_id) ?_
    intro x hx; simp only [mem_setOf_eq, id] at hx; linarith
  · refine (continuousOn_const.add continuousOn_id).div
      (continuousOn_const.add continuousOn_id) ?_
    intro x hx; simp only [mem_setOf_eq, id] at hx; linarith
  · intro x hx; rw [hx]; norm_num

lemma τ_strictMonoOn : StrictMonoOn τ (Ioo 0 1) := by
  intro s hs t ht hst
  rw [← τi_τ hs, ← τi_τ ht] at hst
  exact τi_strictMono.lt_iff_lt.mp hst

lemma τ_injOn : InjOn τ (Ioo 0 1) := τ_strictMonoOn.injOn

lemma continuousOn_τ : ContinuousOn τ (Ioo 0 1) := by
  intro t ht
  rcases lt_trichotomy t (1 / 2) with h | h | h
  · have e : τ =ᶠ[𝓝 t] fun s => (2 * s - 1) / s := by
      filter_upwards [Iio_mem_nhds h] with s hs using τ_of_le hs.le
    exact (((continuous_const.mul continuous_id).sub continuous_const).continuousAt.div
      continuous_id.continuousAt ht.1.ne').congr e.symm |>.continuousWithinAt
  · subst h
    refine ContinuousAt.continuousWithinAt ?_
    have hl : ContinuousWithinAt τ (Iic (1 / 2)) (1 / 2) := by
      refine (ContinuousWithinAt.div ?_ continuousWithinAt_id (by norm_num)).congr
        (fun s hs => τ_of_le hs) (τ_of_le le_rfl)
      exact ((continuous_const.mul continuous_id).sub continuous_const).continuousWithinAt
    have hr : ContinuousWithinAt τ (Ici (1 / 2)) (1 / 2) := by
      refine (ContinuousWithinAt.div ?_ ?_ (by norm_num)).congr
        (fun s hs => τ_of_ge hs) (τ_of_ge le_rfl)
      · exact ((continuous_const.mul continuous_id).sub continuous_const).continuousWithinAt
      · exact (continuous_const.sub continuous_id).continuousWithinAt
    exact continuousAt_iff_continuous_left_right.2 ⟨hl, hr⟩
  · have e : τ =ᶠ[𝓝 t] fun s => (2 * s - 1) / (1 - s) := by
      filter_upwards [Ioi_mem_nhds h] with s hs using τ_of_ge hs.le
    exact (((continuous_const.mul continuous_id).sub continuous_const).continuousAt.div
      (continuous_const.sub continuous_id).continuousAt
        (show (1 : ℝ) - t ≠ 0 by linarith [ht.2])).congr e.symm
        |>.continuousWithinAt

lemma LM_τi : LM univ τi := by
  refine ⟨{0}, finite_singleton 0, fun r hr => ⟨0, by simpa using hr⟩, fun x _ hx => ?_⟩
  rcases lt_or_gt_of_ne (show x ≠ 0 from hx) with h | h
  · refine ⟨mk 0 1 (-1) 2 (by norm_num), by rw [dR_mk]; push_cast; linarith, ?_⟩
    filter_upwards [Iio_mem_nhds h] with y hy
    rw [τi_of_le hy.le, mR_mk]; push_cast; congr 1 <;> ring
  · refine ⟨mk 1 1 1 2 (by norm_num), by rw [dR_mk]; push_cast; linarith, ?_⟩
    filter_upwards [Ioi_mem_nhds h] with y hy
    rw [τi_of_ge hy.le, mR_mk]; push_cast; congr 1 <;> ring

lemma LM_τ : LM (Ioo 0 1) τ := by
  refine ⟨{1 / 2}, finite_singleton _, fun r hr => ⟨1 / 2, by simp at hr; rw [hr]; norm_num⟩,
    fun x hx hx' => ?_⟩
  rcases lt_or_gt_of_ne (show x ≠ 1 / 2 from hx') with h | h
  · refine ⟨mk 2 (-1) 1 0 (by norm_num), by rw [dR_mk]; push_cast; linarith [hx.1], ?_⟩
    filter_upwards [Iio_mem_nhds h] with y hy
    rw [τ_of_le hy.le, mR_mk]; push_cast; congr 1 <;> ring
  · refine ⟨mk 2 (-1) (-1) 1 (by norm_num), by rw [dR_mk]; push_cast; linarith [hx.2], ?_⟩
    filter_upwards [Ioi_mem_nhds h] with y hy
    rw [τ_of_ge hy.le, mR_mk]; push_cast; congr 1 <;> ring

lemma τ_rat (q : ℚ) : ∃ q' : ℚ, τ q = q' := by
  rcases le_total (q : ℝ) (1 / 2) with h | h
  · refine ⟨(2 * q - 1) / q, ?_⟩; rw [τ_of_le h]; push_cast; rfl
  · refine ⟨(2 * q - 1) / (1 - q), ?_⟩; rw [τ_of_ge h]; push_cast; rfl

lemma tendsto_τi_atBot : Tendsto τi atBot (𝓝 0) := by
  have e : ∀ᶠ x in atBot, (fun x : ℝ => (2 + -x)⁻¹) x = τi x := by
    filter_upwards [eventually_le_atBot 0] with x hx
    rw [τi_of_le hx, one_div, sub_eq_add_neg]
  have h2 : Tendsto (fun x : ℝ => 2 + -x) atBot atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_neg_atBot_atTop
  exact Tendsto.congr' e (tendsto_inv_atTop_zero.comp h2)

lemma tendsto_τi_atTop : Tendsto τi atTop (𝓝 1) := by
  have e : ∀ᶠ x in atTop, (fun x : ℝ => 1 - (2 + x)⁻¹) x = τi x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [τi_of_ge hx]
    have : 2 + x ≠ 0 := by linarith
    field_simp; ring
  refine Tendsto.congr' e ?_
  have : Tendsto (fun x : ℝ => (2 + x)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ _ tendsto_id)
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this

end Monod.Dev.Thur
end

section
/-!
# Möbius maps of `SL(2, ℤ)` on `P¹ = OnePoint ℝ`
-/

namespace Monod.Dev.Thur

open OnePoint Filter Topology Set

lemma mob_ι_coe (M : SL2Z) (x : ℝ) :
    mob (ι M) (x : OnePoint ℝ) = if dR M x = 0 then ∞ else ((mR M x : ℝ) : OnePoint ℝ) := by
  rw [mob, smul_some_eq_ite]
  simp only [slToGL_ι, dR, mR, nR]
  congr

lemma mob_ι_coe_of_ne (M : SL2Z) {x : ℝ} (h : dR M x ≠ 0) :
    mob (ι M) (x : OnePoint ℝ) = ((mR M x : ℝ) : OnePoint ℝ) := by
  rw [mob_ι_coe, if_neg h]

lemma mob_ι_coe_of_eq (M : SL2Z) {x : ℝ} (h : dR M x = 0) : mob (ι M) (x : OnePoint ℝ) = ∞ := by
  rw [mob_ι_coe, if_pos h]

lemma mob_ι_infty (M : SL2Z) :
    mob (ι M) ∞ = if (M.1 1 0 : ℝ) = 0 then ∞ else (((M.1 0 0 : ℝ) / M.1 1 0 : ℝ) : OnePoint ℝ) := by
  rw [mob, smul_infty_eq_ite]
  simp only [slToGL_ι]

lemma mob_mul {A : Subring ℝ} (g h : Matrix.SpecialLinearGroup (Fin 2) A) (z : OnePoint ℝ) :
    mob (g * h) z = mob g (mob h z) := by
  simp only [mob, map_mul, mul_smul]

lemma mob_one {A : Subring ℝ} (z : OnePoint ℝ) : mob (1 : Matrix.SpecialLinearGroup (Fin 2) A) z = z := by
  simp [mob]

lemma ι_surjective : Function.Surjective ι := by
  intro g
  have hmem : ∀ i j, ∃ n : ℤ, (n : ℝ) = ((g.1 i j : (⊥ : Subring ℝ)) : ℝ) :=
    fun i j => Subring.mem_bot.mp (g.1 i j).2
  choose N hN using hmem
  have hdet : (N 0 0 * N 1 1 - N 0 1 * N 1 0 : ℤ) = 1 := by
    have hg := g.2
    rw [Matrix.det_fin_two] at hg
    have hg' := congrArg (fun z : (⊥ : Subring ℝ) => (z : ℝ)) hg
    push_cast at hg'
    have : ((N 0 0 * N 1 1 - N 0 1 * N 1 0 : ℤ) : ℝ) = 1 := by
      push_cast; rw [hN, hN, hN, hN]; exact hg'
    exact_mod_cast this
  refine ⟨⟨Matrix.of N, by rw [Matrix.det_fin_two]; exact hdet⟩, ?_⟩
  ext i j
  rw [← hN i j]
  show ((Int.castRingHom (⊥ : Subring ℝ) (N i j) : (⊥ : Subring ℝ)) : ℝ) = _
  simp

lemma mob_ratPoints (M : SL2Z) {z : OnePoint ℝ} (hz : z ∈ ratPoints) :
    mob (ι M) z ∈ ratPoints := by
  rcases hz with rfl | ⟨r, rfl⟩
  · rw [mob_ι_infty]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr ⟨(M.1 0 0 : ℚ) / M.1 1 0, by push_cast; rfl⟩
  · rw [mob_ι_coe]
    split_ifs
    · exact Or.inl rfl
    · obtain ⟨q, hq⟩ := rat_mR M r
      exact Or.inr ⟨q, by rw [hq]⟩

lemma exists_mob_infty {q : OnePoint ℝ} (hq : q ∈ ratPoints) : ∃ M : SL2Z, mob (ι M) ∞ = q := by
  rcases hq with rfl | ⟨r, rfl⟩
  · exact ⟨1, by rw [map_one, mob_one]⟩
  · have hcop : Int.gcd r.num (r.den : ℤ) = 1 := by
      have := r.reduced; simpa [Int.gcd] using this
    have hbez := Int.gcd_eq_gcd_ab r.num r.den
    rw [hcop] at hbez
    refine ⟨mk r.num (-Int.gcdB r.num r.den) r.den (Int.gcdA r.num r.den)
      (by push_cast at hbez; linear_combination -hbez), ?_⟩
    rw [mob_ι_infty]
    have hden : ((r.den : ℤ) : ℝ) ≠ 0 := by exact_mod_cast r.den_pos.ne'
    simp only [mk_10, mk_00]
    simp only [hden, ↓reduceIte, Rat.cast_def]
    push_cast; rfl

/-! ### Continuity -/

lemma mob_T_eq : (fun z => mob (ι ModularGroup.T) z) =
    (Homeomorph.addRight (1 : ℝ)).onePointCongr := by
  funext z
  induction z using OnePoint.rec with
  | infty =>
    rw [mob_ι_infty]
    simp [ModularGroup.T, Homeomorph.onePointCongr]
  | coe x =>
    rw [mob_ι_coe_of_ne]
    · simp [ModularGroup.T, Homeomorph.onePointCongr, mR, nR, dR]
    · simp [ModularGroup.T, dR]

lemma continuous_mob_T : Continuous (fun z => mob (ι ModularGroup.T) z) := by
  rw [mob_T_eq]; exact Homeomorph.continuous _

lemma mob_S_coe (x : ℝ) (hx : x ≠ 0) :
    mob (ι ModularGroup.S) (x : OnePoint ℝ) = ((-x⁻¹ : ℝ) : OnePoint ℝ) := by
  rw [mob_ι_coe_of_ne]
  · simp [ModularGroup.S, mR, nR, dR]; ring
  · simp [ModularGroup.S, dR, hx]

lemma continuous_mob_S : Continuous (fun z => mob (ι ModularGroup.S) z) := by
  have hinf : mob (ι ModularGroup.S) ∞ = ((0 : ℝ) : OnePoint ℝ) := by
    rw [mob_ι_infty]; simp [ModularGroup.S]
  have h0 : mob (ι ModularGroup.S) ((0 : ℝ) : OnePoint ℝ) = ∞ := by
    rw [mob_ι_coe_of_eq]; simp [ModularGroup.S, dR]
  rw [continuous_iff_continuousAt]
  intro z
  induction z using OnePoint.rec with
  | infty =>
    rw [continuousAt_infty', hinf, coclosedCompact_eq_cocompact,
      ← Metric.cobounded_eq_cocompact]
    have hev : ∀ᶠ y in Bornology.cobounded ℝ, ((-y⁻¹ : ℝ) : OnePoint ℝ) =
        (fun z => mob (ι ModularGroup.S) z) ((y : ℝ) : OnePoint ℝ) := by
      have : ∀ᶠ y in Bornology.cobounded ℝ, y ≠ 0 := by
        have := (Metric.hasBasis_cobounded_compl_closedBall (0 : ℝ)).mem_of_mem
          (i := 1) trivial
        filter_upwards [this] with y hy
        intro h; subst h; simp at hy
      filter_upwards [this] with y hy
      exact (mob_S_coe y hy).symm
    refine Tendsto.congr' hev ?_
    have : Tendsto (fun y : ℝ => -y⁻¹) (Bornology.cobounded ℝ) (𝓝 0) := by
      simpa using (tendsto_inv₀_cobounded (α := ℝ)).neg
    exact (continuous_coe.tendsto 0).comp this
  | coe x =>
    rw [continuousAt_coe]
    rcases eq_or_ne x 0 with rfl | hx
    · show Tendsto _ _ _
      rw [Function.comp_apply, h0, ← nhdsNE_sup_pure, tendsto_sup]
      refine ⟨?_, ?_⟩
      · have hev : ∀ᶠ y in 𝓝[≠] (0 : ℝ), ((-y⁻¹ : ℝ) : OnePoint ℝ) =
            ((fun z => mob (ι ModularGroup.S) z) ∘ OnePoint.some) y := by
          filter_upwards [self_mem_nhdsWithin] with y hy
          exact (mob_S_coe y hy).symm
        refine Tendsto.congr' hev ?_
        have h1 : Tendsto (fun y : ℝ => -y⁻¹) (𝓝[≠] 0) (Bornology.cobounded ℝ) :=
          tendsto_neg_cobounded.comp tendsto_inv₀_nhdsNE_zero
        rw [Metric.cobounded_eq_cocompact, ← coclosedCompact_eq_cocompact] at h1
        exact tendsto_coe_infty.comp h1
      · rw [tendsto_pure_left]
        intro s hs
        simpa [h0] using mem_of_mem_nhds hs
    · have hev : (fun y : ℝ => ((-y⁻¹ : ℝ) : OnePoint ℝ)) =ᶠ[𝓝 x]
          ((fun z => mob (ι ModularGroup.S) z) ∘ OnePoint.some) := by
        filter_upwards [isOpen_ne.mem_nhds hx] with y hy
        exact (mob_S_coe y hy).symm
      refine ContinuousAt.congr ?_ hev
      exact continuous_coe.continuousAt.comp ((continuousAt_inv₀ hx).neg)

/-- The Möbius permutation of `P¹`. -/
noncomputable def mobPerm (M : SL2Z) : Equiv.Perm (OnePoint ℝ) :=
  MulAction.toPerm (slToGL ⊥ (ι M))

lemma continuous_mob (M : SL2Z) : Continuous (fun z => mob (ι M) z) := by
  let K : Subgroup SL2Z :=
    { carrier := {M | Continuous (fun z => mob (ι M) z)}
      one_mem' := by simp only [mem_setOf_eq, map_one, mob_one]; exact continuous_id
      mul_mem' := by
        intro a b ha hb
        simp only [mem_setOf_eq, map_mul] at ha hb ⊢
        simp only [mob_mul]
        exact ha.comp hb
      inv_mem' := by
        intro a ha
        simp only [mem_setOf_eq] at ha ⊢
        have hc : Continuous (mobPerm a) := ha
        convert (hc.homeoOfEquivCompactToT2).symm.continuous using 1
        funext z
        simp [mobPerm, mob, map_inv]
        rfl }
  have hK : Subgroup.closure {ModularGroup.S, ModularGroup.T} ≤ K := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact continuous_mob_S
    · exact continuous_mob_T
  rw [SpecialLinearGroup.SL2Z_generators] at hK
  exact hK (Subgroup.mem_top M)

/-- The Möbius homeomorphism of `P¹`. -/
noncomputable def mobH (M : SL2Z) : OnePoint ℝ ≃ₜ OnePoint ℝ :=
  Continuous.homeoOfEquivCompactToT2 (f := mobPerm M) (continuous_mob M)

lemma mobH_apply (M : SL2Z) (z : OnePoint ℝ) : mobH M z = mob (ι M) z := rfl

lemma mobH_mul (M N : SL2Z) : mobH (M * N) = mobH M * mobH N := by
  ext z; simp [mobH_apply, mob_mul]

lemma mobH_symm_apply (M : SL2Z) (z : OnePoint ℝ) : (mobH M).symm z = mob (ι M⁻¹) z := by
  rw [Homeomorph.symm_apply_eq, mobH_apply, ← mob_mul, ← map_mul, mul_inv_cancel, map_one,
    mob_one]

/-! ### The generators of `GRat` -/

/-- The generating set of `GRat`. -/
def Gen : Set (OnePoint ℝ ≃ₜ OnePoint ℝ) := {f | IsPiecewiseProjOn ⊥ ratPoints f}

lemma ratPoints_coe_iff (x : ℝ) : (x : OnePoint ℝ) ∈ ratPoints ↔ ∃ q : ℚ, x = q := by
  constructor
  · rintro (h | ⟨q, hq⟩)
    · exact absurd h (coe_ne_infty x)
    · exact ⟨q, coe_injective hq⟩
  · rintro ⟨q, rfl⟩; exact Or.inr ⟨q, rfl⟩

lemma infty_mem_ratPoints : (∞ : OnePoint ℝ) ∈ ratPoints := Or.inl rfl

lemma symm_mem_ratPoints {g : OnePoint ℝ ≃ₜ OnePoint ℝ} (hg : g ∈ Gen) {q : OnePoint ℝ}
    (hq : q ∈ ratPoints) : g.symm q ∈ ratPoints := by
  obtain ⟨B, hB, hloc⟩ := hg
  by_cases hy : g.symm q ∈ B
  · exact hB hy
  obtain ⟨g', hev⟩ := hloc _ hy
  obtain ⟨M, rfl⟩ := ι_surjective g'
  have hself : g (g.symm q) = mob (ι M) (g.symm q) := hev.self_of_nhds
  rw [Homeomorph.apply_symm_apply] at hself
  generalize g.symm q = y at hself ⊢
  induction y using OnePoint.rec with
  | infty => exact infty_mem_ratPoints
  | coe x =>
    rw [ratPoints_coe_iff]
    by_cases hd : dR M x = 0
    · have hc : (M.1 1 0 : ℝ) ≠ 0 := by
        intro hc; have := detR M; simp only [dR, hc, zero_mul, zero_add] at hd
        rw [hd, hc] at this; simp at this
      refine ⟨-(M.1 1 1 : ℚ) / M.1 1 0, ?_⟩
      push_cast
      simp only [dR] at hd
      field_simp; linarith
    · rw [mob_ι_coe_of_ne M hd] at hself
      rw [hself, ratPoints_coe_iff] at hq
      obtain ⟨r, hr⟩ := hq
      exact rat_of_mR M hd hr

lemma mobH_mem_Gen (M : SL2Z) : mobH M ∈ Gen :=
  ⟨∅, by simp, fun x _ => ⟨ι M, Eventually.of_forall fun y => rfl⟩⟩

lemma mul_mobH_mem_Gen {g : OnePoint ℝ ≃ₜ OnePoint ℝ} (hg : g ∈ Gen) (M : SL2Z) :
    g * mobH M ∈ Gen := by
  classical
  obtain ⟨B, hB, hloc⟩ := hg
  refine ⟨B.image (mobH M).symm, ?_, fun x hx => ?_⟩
  · intro z hz
    simp only [Finset.coe_image, mem_image, Finset.mem_coe] at hz
    obtain ⟨b, hb, rfl⟩ := hz
    rw [mobH_symm_apply]; exact mob_ratPoints _ (hB hb)
  · have hx' : mobH M x ∉ B := by
      intro h; apply hx
      exact Finset.mem_image.mpr ⟨_, h, by simp⟩
    obtain ⟨g', hev⟩ := hloc _ hx'
    refine ⟨g' * ι M, ?_⟩
    have := (mobH M).continuous.continuousAt (x := x) |>.eventually hev
    filter_upwards [this] with y hy
    rw [Homeomorph.mul_apply, hy, mob_mul, mobH_apply]

end Monod.Dev.Thur
end

section
/-!
# Farey and dyadic nodes (for Minkowski's question-mark function)

The dyadic interval `dyadicNode w` reached from `[0,1]` by halving along a path, the Farey
invariants of `fareyNode w`, the increasing integral projective parametrization `phi I` of a
Farey interval, and the covering lemmas.
-/

namespace CannonFloydParry.S7

open FracInterval Set

/-- The dyadic interval reached from `[0,1]` by halving along `w` (`false` = left half,
`true` = right half), read from the root as in `fareyNode`. -/
noncomputable def dyadicNode (w : List Bool) : ℝ × ℝ :=
  w.foldl (fun p b => if b then ((p.1 + p.2) / 2, p.2) else (p.1, (p.1 + p.2) / 2)) (0, 1)

/-- The increasing linear fractional map `[0,1] → [a/b, c/d]`,
`s ↦ (a (1 - s) + c s) / (b (1 - s) + d s)`; in the coordinate `(s, 1)` it is given by the
integer matrix `!![c - a, a; d - b, b]` (determinant `bc - ad`). -/
noncomputable def phi (I : FracInterval) (s : ℝ) : ℝ :=
  ((I.a : ℝ) * (1 - s) + I.c * s) / ((I.b : ℝ) * (1 - s) + I.d * s)

namespace Mink

theorem fareyNode_nil : fareyNode [] = ⟨0, 1, 1, 1⟩ := rfl

theorem fareyNode_append (w : List Bool) (b : Bool) :
    fareyNode (w ++ [b]) = if b then (fareyNode w).rightPart else (fareyNode w).leftPart := by
  simp [fareyNode, List.foldl_append]

theorem fareyNode_append_false (w : List Bool) :
    fareyNode (w ++ [false]) = (fareyNode w).leftPart := by
  simp [fareyNode_append]

theorem fareyNode_append_true (w : List Bool) :
    fareyNode (w ++ [true]) = (fareyNode w).rightPart := by
  simp [fareyNode_append]

theorem dyadicNode_nil : dyadicNode [] = (0, 1) := rfl

theorem dyadicNode_append_false (w : List Bool) :
    dyadicNode (w ++ [false]) =
      ((dyadicNode w).1, ((dyadicNode w).1 + (dyadicNode w).2) / 2) := by
  simp [dyadicNode, List.foldl_append]

theorem dyadicNode_append_true (w : List Bool) :
    dyadicNode (w ++ [true]) =
      (((dyadicNode w).1 + (dyadicNode w).2) / 2, (dyadicNode w).2) := by
  simp [dyadicNode, List.foldl_append]

theorem dyadicNode_width (w : List Bool) :
    (dyadicNode w).2 - (dyadicNode w).1 = (1 / 2 : ℝ) ^ w.length := by
  induction w using List.reverseRecOn with
  | nil => simp [dyadicNode_nil]
  | append_singleton w b ih =>
    cases b
    · rw [dyadicNode_append_false]; simp only [List.length_append, List.length_singleton,
        pow_succ]; rw [← ih]; ring
    · rw [dyadicNode_append_true]; simp only [List.length_append, List.length_singleton,
        pow_succ]; rw [← ih]; ring

theorem dyadicNode_bounds (w : List Bool) :
    0 ≤ (dyadicNode w).1 ∧ (dyadicNode w).1 < (dyadicNode w).2 ∧ (dyadicNode w).2 ≤ 1 := by
  induction w using List.reverseRecOn with
  | nil => simp [dyadicNode_nil]
  | append_singleton w b ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    cases b
    · rw [dyadicNode_append_false]; exact ⟨h1, by simp; linarith, by simp; linarith⟩
    · rw [dyadicNode_append_true]; exact ⟨by simp; linarith, by simp; linarith, h3⟩

/-- The dyadic intervals of each depth cover `[0,1]`. -/
theorem dyadic_cover (n : ℕ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    ∃ w : List Bool, w.length = n ∧ (dyadicNode w).1 ≤ y ∧ y ≤ (dyadicNode w).2 := by
  induction n with
  | zero => exact ⟨[], rfl, by simpa [dyadicNode_nil] using hy.1, by simpa [dyadicNode_nil]
      using hy.2⟩
  | succ n ih =>
    obtain ⟨w, hw, h1, h2⟩ := ih
    by_cases hm : y ≤ ((dyadicNode w).1 + (dyadicNode w).2) / 2
    · exact ⟨w ++ [false], by simp [hw], by rw [dyadicNode_append_false]; exact h1,
        by rw [dyadicNode_append_false]; exact hm⟩
    · exact ⟨w ++ [true], by simp [hw], by rw [dyadicNode_append_true]; simp only; linarith,
        by rw [dyadicNode_append_true]; exact h2⟩

/-- The Farey invariants of a node of depth `n`. -/
structure Inv (I : FracInterval) (n : ℕ) : Prop where
  hb : 1 ≤ I.b
  hd : 1 ≤ I.d
  hab : I.a ≤ I.b
  hcd : I.c ≤ I.d
  hdet : I.b * I.c = I.a * I.d + 1
  hsum : n + 2 ≤ I.b + I.d

theorem inv_fareyNode (w : List Bool) : Inv (fareyNode w) w.length := by
  induction w using List.reverseRecOn with
  | nil => rw [fareyNode_nil]; exact ⟨le_rfl, le_rfl, by norm_num, le_rfl, rfl, le_rfl⟩
  | append_singleton w b ih =>
    obtain ⟨hb, hd, hab, hcd, hdet, hsum⟩ := ih
    cases b
    · rw [fareyNode_append_false]
      refine ⟨hb, by simp [leftPart]; omega, hab, by simp [leftPart]; omega, ?_,
        by simp [leftPart]; omega⟩
      simp only [leftPart]; rw [Nat.mul_add, hdet, Nat.mul_add]; ring
    · rw [fareyNode_append_true]
      refine ⟨by simp [rightPart]; omega, hd, by simp [rightPart]; omega, hcd, ?_,
        by simp [rightPart]; omega⟩
      simp only [rightPart]; rw [Nat.add_mul, hdet, Nat.add_mul]; ring

theorem isFarey_fareyNode (w : List Bool) : (fareyNode w).IsFarey := by
  obtain ⟨hb, hd, hab, hcd, hdet, -⟩ := inv_fareyNode w
  refine ⟨hb, ?_, hd, hab, hcd, ?_⟩
  · rcases Nat.eq_zero_or_pos (fareyNode w).c with h | h
    · rw [h] at hdet; simp at hdet
    · exact h
  · have : ((fareyNode w).b : ℤ) * (fareyNode w).c = (fareyNode w).a * (fareyNode w).d + 1 := by
      exact_mod_cast hdet
    linarith

section real

variable {I : FracInterval} {n : ℕ}

theorem Inv.hdetR (h : Inv I n) : (I.b : ℝ) * I.c = I.a * I.d + 1 := by
  exact_mod_cast h.hdet

theorem Inv.bpos (h : Inv I n) : (0 : ℝ) < I.b := by
  have := h.hb; exact_mod_cast this

theorem Inv.dpos (h : Inv I n) : (0 : ℝ) < I.d := by
  have := h.hd; exact_mod_cast this

theorem Inv.cdR (h : Inv I n) : (I.c : ℝ) ≤ I.d := by exact_mod_cast h.hcd

theorem Inv.width (h : Inv I n) : I.hi - I.lo = 1 / ((I.b : ℝ) * I.d) := by
  have hb := h.bpos; have hd := h.dpos; have := h.hdetR
  simp only [FracInterval.hi, FracInterval.lo]
  field_simp
  linarith

theorem Inv.width_le (h : Inv I n) : I.hi - I.lo ≤ 1 / ((n : ℝ) + 1) := by
  rw [h.width]
  have hb := h.hb; have hd := h.hd; have hs := h.hsum
  have key : n + 1 ≤ I.b * I.d := by nlinarith
  have key' : (n : ℝ) + 1 ≤ (I.b : ℝ) * I.d := by exact_mod_cast key
  exact one_div_le_one_div_of_le (by positivity) key'

theorem Inv.lo_lt_hi (h : Inv I n) : I.lo < I.hi := by
  have := h.width; have hb := h.bpos; have hd := h.dpos
  have : 0 < 1 / ((I.b : ℝ) * I.d) := by positivity
  linarith

theorem Inv.lo_nonneg (_h : Inv I n) : 0 ≤ I.lo := by
  simp only [FracInterval.lo]; positivity

theorem Inv.hi_le_one (h : Inv I n) : I.hi ≤ 1 := by
  simp only [FracInterval.hi]; rw [div_le_one h.dpos]; exact h.cdR

theorem Inv.den_pos (h : Inv I n) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    0 < (I.b : ℝ) * (1 - s) + I.d * s := by
  have hb := h.bpos; have hd := h.dpos
  rcases eq_or_lt_of_le hs.2 with h1 | h1
  · subst h1; simpa using hd
  · have : 0 < 1 - s := by linarith
    nlinarith [hs.1]

theorem phi_zero (I : FracInterval) : phi I 0 = I.lo := by
  simp [phi, FracInterval.lo]

theorem phi_one (I : FracInterval) : phi I 1 = I.hi := by
  simp [phi, FracInterval.hi]

theorem phi_root (s : ℝ) : phi (fareyNode []) s = s := by
  simp [phi, fareyNode_nil]

theorem phi_leftPart (h : Inv I n) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    phi I.leftPart s = phi I (s / (1 + s)) := by
  have hb := h.bpos; have hd := h.dpos
  have h1 : (0 : ℝ) < 1 + s := by linarith [hs.1]
  simp only [phi, leftPart]
  push_cast
  have e1 : (I.a : ℝ) * (1 - s / (1 + s)) + I.c * (s / (1 + s)) = (I.a + I.c * s) / (1 + s) := by
    field_simp; ring
  have e2 : (I.b : ℝ) * (1 - s / (1 + s)) + I.d * (s / (1 + s)) = (I.b + I.d * s) / (1 + s) := by
    field_simp; ring
  rw [e1, e2, div_div_div_cancel_right₀ h1.ne']
  congr 1 <;> ring

theorem phi_rightPart (h : Inv I n) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    phi I.rightPart s = phi I (1 / (2 - s)) := by
  have hb := h.bpos; have hd := h.dpos
  have h1 : (0 : ℝ) < 2 - s := by linarith [hs.2]
  simp only [phi, rightPart]
  push_cast
  have e1 : (I.a : ℝ) * (1 - 1 / (2 - s)) + I.c * (1 / (2 - s)) =
      (I.a * (1 - s) + I.c) / (2 - s) := by
    field_simp; ring
  have e2 : (I.b : ℝ) * (1 - 1 / (2 - s)) + I.d * (1 / (2 - s)) =
      (I.b * (1 - s) + I.d) / (2 - s) := by
    field_simp; ring
  rw [e1, e2, div_div_div_cancel_right₀ h1.ne']
  congr 1 <;> ring

end real

/-- The Farey intervals of each depth cover `[0,1]`. -/
theorem farey_cover (n : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ w : List Bool, w.length = n ∧ (fareyNode w).lo ≤ x ∧ x ≤ (fareyNode w).hi := by
  induction n with
  | zero => exact ⟨[], rfl, by simpa [fareyNode_nil, FracInterval.lo] using hx.1,
      by simpa [fareyNode_nil, FracInterval.hi] using hx.2⟩
  | succ n ih =>
    obtain ⟨w, hw, h1, h2⟩ := ih
    by_cases hm : x ≤ (fareyNode w).leftPart.hi
    · exact ⟨w ++ [false], by simp [hw], by rw [fareyNode_append_false]; exact h1,
        by rw [fareyNode_append_false]; exact hm⟩
    · refine ⟨w ++ [true], by simp [hw], ?_, ?_⟩
      · rw [fareyNode_append_true]
        have : (fareyNode w).rightPart.lo = (fareyNode w).leftPart.hi := rfl
        rw [this]; linarith
      · rw [fareyNode_append_true]; exact h2

end Mink

end CannonFloydParry.S7
end

section
/-!
# Minkowski's question-mark function

`mink` is constructed as the pointwise limit of the iterates of the contraction
`T f x = f (x / (1 - x)) / 2` (`x ≤ 1/2`), `1/2 + f (2 - 1/x) / 2` (`x > 1/2`), starting from the
identity.  It satisfies `mink (s / (1 + s)) = mink s / 2` and `mink (1 / (2 - s)) = 1/2 + mink s / 2`
on `[0,1]`, whence the self-similarity on every Farey node, the endpoint values, strict
monotonicity (Farey widths tend to `0`), continuity (monotone with dense range) and surjectivity.
-/

namespace CannonFloydParry.S7

open FracInterval Set Filter Topology

namespace Mink

/-- One step of the defining functional equation. -/
noncomputable def T (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ 1 / 2 then f (x / (1 - x)) / 2 else 1 / 2 + f (2 - 1 / x) / 2

/-- The iterates of `T` from the identity. -/
noncomputable def approx : ℕ → ℝ → ℝ
  | 0 => id
  | n + 1 => T (approx n)

/-- Monotone on `[0,1]`, fixing `0` and `1`. -/
def Good (f : ℝ → ℝ) : Prop := MonotoneOn f (Icc 0 1) ∧ f 0 = 0 ∧ f 1 = 1

theorem Good.mem {f : ℝ → ℝ} (hf : Good f) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    f x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hm, h0, h1⟩ := hf
  exact ⟨h0 ▸ hm ⟨le_rfl, zero_le_one⟩ hx hx.1, h1 ▸ hm hx ⟨zero_le_one, le_rfl⟩ hx.2⟩

theorem mapL {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (h : x ≤ 1 / 2) : x / (1 - x) ∈ Icc (0 : ℝ) 1 := by
  have : 0 < 1 - x := by linarith
  refine ⟨div_nonneg hx.1 this.le, ?_⟩
  rw [div_le_one this]; linarith

theorem mapR {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (h : ¬ x ≤ 1 / 2) : 2 - 1 / x ∈ Icc (0 : ℝ) 1 := by
  rw [not_le] at h
  have hx0 : 0 < x := by linarith
  refine ⟨?_, ?_⟩
  · have : 1 / x ≤ 2 := by rw [div_le_iff₀ hx0]; linarith
    linarith
  · have : 1 ≤ 1 / x := by rw [le_div_iff₀ hx0]; linarith [hx.2]
    linarith

theorem Good.T {f : ℝ → ℝ} (hf : Good f) : Good (T f) := by
  obtain ⟨hm, h0, h1⟩ := hf
  have hg : Good f := ⟨hm, h0, h1⟩
  refine ⟨?_, by simp [Mink.T, h0], by norm_num [Mink.T, h1]⟩
  intro x hx y hy hxy
  simp only [Mink.T]
  by_cases h1x : x ≤ 1 / 2
  · by_cases h1y : y ≤ 1 / 2
    · rw [if_pos h1x, if_pos h1y]
      have : x / (1 - x) ≤ y / (1 - y) := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
      have := hm (mapL hx h1x) (mapL hy h1y) this; linarith
    · rw [if_pos h1x, if_neg h1y]
      have a := (hg.mem (mapL hx h1x)).2
      have b := (hg.mem (mapR hy h1y)).1
      linarith
  · have h1y : ¬ y ≤ 1 / 2 := fun h => h1x (hxy.trans h)
    rw [if_neg h1x, if_neg h1y]
    have hx0 : 0 < x := by rw [not_le] at h1x; linarith
    have : 1 / y ≤ 1 / x := one_div_le_one_div_of_le hx0 hxy
    have := hm (mapR hx h1x) (mapR hy h1y) (by linarith); linarith

theorem approx_good (n : ℕ) : Good (approx n) := by
  induction n with
  | zero => exact ⟨monotoneOn_id, rfl, rfl⟩
  | succ n ih => exact ih.T

theorem approx_dist (n : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |approx (n + 1) x - approx n x| ≤ (1 / 2) ^ n := by
  induction n generalizing x with
  | zero =>
    have a := (approx_good 1).mem hx; have b := (approx_good 0).mem hx
    rw [abs_le]; simp only [pow_zero]; constructor <;> linarith [a.1, a.2, b.1, b.2]
  | succ n ih =>
    show |T (approx (n + 1)) x - T (approx n) x| ≤ _
    simp only [Mink.T]
    by_cases h : x ≤ 1 / 2
    · rw [if_pos h, if_pos h]
      have := ih (mapL hx h)
      rw [abs_le] at this ⊢; rw [pow_succ]; constructor <;> linarith [this.1, this.2]
    · rw [if_neg h, if_neg h]
      have := ih (mapR hx h)
      rw [abs_le] at this ⊢; rw [pow_succ]; constructor <;> linarith [this.1, this.2]

theorem approx_cauchy {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : CauchySeq (fun n => approx n x) :=
  cauchySeq_of_le_geometric (1 / 2) 1 (by norm_num) (fun n => by
    rw [Real.dist_eq, abs_sub_comm, one_mul]; exact approx_dist n hx)

end Mink

/-- **Minkowski's question-mark function** on `[0,1]` (its values off `[0,1]` are irrelevant). -/
noncomputable def mink (x : ℝ) : ℝ := limUnder atTop (fun n => Mink.approx n x)

namespace Mink

theorem tendsto_approx {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => approx n x) atTop (𝓝 (mink x)) :=
  (approx_cauchy hx).tendsto_limUnder

theorem mink_T {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : mink x = T mink x := by
  have h1 : Tendsto (fun n => approx (n + 1) x) atTop (𝓝 (mink x)) :=
    (tendsto_approx hx).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => approx (n + 1) x) atTop (𝓝 (T mink x)) := by
    show Tendsto (fun n => T (approx n) x) atTop _
    unfold Mink.T
    by_cases h : x ≤ 1 / 2
    · simp only [if_pos h]
      exact (tendsto_approx (mapL hx h)).div_const 2
    · simp only [if_neg h]
      exact ((tendsto_approx (mapR hx h)).div_const 2).const_add _
  exact tendsto_nhds_unique h1 h2

theorem mink_zero : mink 0 = 0 := by
  have h := tendsto_approx (x := 0) ⟨le_rfl, zero_le_one⟩
  have : (fun n => approx n 0) = fun _ => 0 := funext fun n => (approx_good n).2.1
  rw [this] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

theorem mink_one : mink 1 = 1 := by
  have h := tendsto_approx (x := 1) ⟨zero_le_one, le_rfl⟩
  have : (fun n => approx n 1) = fun _ => 1 := funext fun n => (approx_good n).2.2
  rw [this] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

theorem mink_monotoneOn : MonotoneOn mink (Icc 0 1) := fun _ hx _ hy hxy =>
  le_of_tendsto_of_tendsto' (tendsto_approx hx) (tendsto_approx hy) fun n =>
    (approx_good n).1 hx hy hxy

theorem mink_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : mink x ∈ Icc (0 : ℝ) 1 :=
  Good.mem ⟨mink_monotoneOn, mink_zero, mink_one⟩ hx

theorem memL {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : s / (1 + s) ∈ Icc (0 : ℝ) 1 := by
  have : 0 < 1 + s := by linarith [hs.1]
  exact ⟨div_nonneg hs.1 this.le, by rw [div_le_one this]; linarith [hs.1]⟩

theorem memR {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : 1 / (2 - s) ∈ Icc (0 : ℝ) 1 := by
  have : 0 < 2 - s := by linarith [hs.2]
  exact ⟨by positivity, by rw [div_le_one this]; linarith [hs.2]⟩

theorem mink_L {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : mink (s / (1 + s)) = mink s / 2 := by
  have h1 : 0 < 1 + s := by linarith [hs.1]
  have hle : s / (1 + s) ≤ 1 / 2 := by rw [div_le_iff₀ h1]; linarith [hs.2]
  rw [mink_T (memL hs), Mink.T, if_pos hle]
  congr 2
  field_simp
  ring

theorem mink_R {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : mink (1 / (2 - s)) = 1 / 2 + mink s / 2 := by
  have h1 : 0 < 2 - s := by linarith [hs.2]
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · subst h0
    have hh : (1 : ℝ) / (2 - 0) = 1 / 2 := by norm_num
    rw [hh, mink_T ⟨by norm_num, by norm_num⟩, Mink.T, if_pos le_rfl, mink_zero]
    norm_num [mink_one]
  · have hlt : ¬ 1 / (2 - s) ≤ 1 / 2 := by
      rw [not_le, div_lt_div_iff₀ (by norm_num) h1]; linarith
    rw [mink_T (memR hs), Mink.T, if_neg hlt]
    congr 3
    rw [one_div_one_div]; ring

/-- Self-similarity on the Farey node `fareyNode w`. -/
theorem mink_phi (w : List Bool) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    mink (phi (fareyNode w) s) =
      (dyadicNode w).1 + ((dyadicNode w).2 - (dyadicNode w).1) * mink s := by
  induction w using List.reverseRecOn generalizing s with
  | nil => rw [phi_root, dyadicNode_nil]; ring
  | append_singleton w b ih =>
    have hI := inv_fareyNode w
    cases b
    · rw [fareyNode_append_false, phi_leftPart hI hs, ih (memL hs), mink_L hs,
        dyadicNode_append_false]
      ring
    · rw [fareyNode_append_true, phi_rightPart hI hs, ih (memR hs), mink_R hs,
        dyadicNode_append_true]
      ring

theorem mink_lo (w : List Bool) : mink (fareyNode w).lo = (dyadicNode w).1 := by
  rw [← phi_zero, mink_phi w ⟨le_rfl, zero_le_one⟩, mink_zero]; ring

theorem mink_hi (w : List Bool) : mink (fareyNode w).hi = (dyadicNode w).2 := by
  rw [← phi_one, mink_phi w ⟨zero_le_one, le_rfl⟩, mink_one]; ring

theorem mink_strictMonoOn : StrictMonoOn mink (Icc 0 1) := by
  intro x hx y hy hxy
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < (y - x) / 2 by linarith)
  have hm : (x + y) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩
  obtain ⟨w, hw, h1, h2⟩ := farey_cover n hm
  have hI := inv_fareyNode w
  rw [hw] at hI
  have hwid := hI.width_le
  have hlh := hI.lo_lt_hi
  have hlo : x < (fareyNode w).lo := by linarith
  have hhi : (fareyNode w).hi < y := by linarith
  have hlo01 : (fareyNode w).lo ∈ Icc (0 : ℝ) 1 :=
    ⟨hI.lo_nonneg, by linarith [hI.hi_le_one]⟩
  have hhi01 : (fareyNode w).hi ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hI.lo_nonneg], hI.hi_le_one⟩
  have a := mink_monotoneOn hx hlo01 hlo.le
  have b := mink_monotoneOn hhi01 hy hhi.le
  rw [mink_lo] at a; rw [mink_hi] at b
  have := (dyadicNode_bounds w).2.1
  linarith

theorem mink_lt_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : mink t < 1 :=
  mink_one ▸ mink_strictMonoOn ⟨ht0, ht1.le⟩ ⟨zero_le_one, le_rfl⟩ ht1

end Mink

/-- The periodic extension `x ↦ ⌊x⌋ + mink (fract x)`. -/
noncomputable def minkFun (x : ℝ) : ℝ := ⌊x⌋ + mink (Int.fract x)

namespace Mink

theorem minkFun_int_add (k : ℤ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    minkFun (k + t) = k + mink t := by
  have hf : ⌊t⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨ht0, ht1⟩
  have hfr : Int.fract t = t := Int.fract_eq_self.mpr ⟨ht0, ht1⟩
  simp [minkFun, Int.floor_intCast_add, Int.fract_intCast_add, hf, hfr]

theorem minkFun_intCast (k : ℤ) : minkFun k = k := by
  simp [minkFun, mink_zero]

theorem minkFun_add_one (x : ℝ) : minkFun (x + 1) = minkFun x + 1 := by
  simp only [minkFun, Int.floor_add_one, Int.fract_add_one]; push_cast; ring

theorem minkFun_eq_mink {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : minkFun x = mink x := by
  rcases eq_or_lt_of_le hx.2 with h | h
  · subst h; simpa [mink_one] using minkFun_intCast 1
  · simpa using minkFun_int_add 0 hx.1 h

theorem minkFun_strictMono : StrictMono minkFun := by
  intro x y hxy
  simp only [minkFun]
  have hx0 := Int.fract_nonneg x; have hx1 := Int.fract_lt_one x
  have hy0 := Int.fract_nonneg y; have hy1 := Int.fract_lt_one y
  have ex := Int.floor_add_fract x; have ey := Int.floor_add_fract y
  rcases (Int.floor_mono hxy.le).lt_or_eq with h | h
  · have h' : ⌊x⌋ + 1 ≤ ⌊y⌋ := Int.add_one_le_of_lt h
    have h'' : (⌊x⌋ : ℝ) + 1 ≤ ⌊y⌋ := by exact_mod_cast h'
    have := mink_lt_one hx0 hx1
    have := (mink_mem ⟨hy0, hy1.le⟩).1
    linarith
  · have hc : (⌊x⌋ : ℝ) = ⌊y⌋ := by rw [h]
    have : Int.fract x < Int.fract y := by linarith
    linarith [mink_strictMonoOn ⟨hx0, hx1.le⟩ ⟨hy0, hy1.le⟩ this]

theorem minkFun_denseRange : DenseRange minkFun := by
  apply dense_of_exists_between
  intro a b hab
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < (b - a) / 2 by linarith)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  obtain ⟨w, hw, h1, h2⟩ := dyadic_cover n (y := Int.fract ((a + b) / 2))
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hwd := dyadicNode_width w
  rw [hw] at hwd
  have hI := inv_fareyNode w
  have ec := Int.floor_add_fract ((a + b) / 2)
  refine ⟨⌊(a + b) / 2⌋ + (dyadicNode w).1, ⟨⌊(a + b) / 2⌋ + (fareyNode w).lo, ?_⟩, ?_, ?_⟩
  · rw [minkFun_int_add _ hI.lo_nonneg (by linarith [hI.lo_lt_hi, hI.hi_le_one]), mink_lo]
  · linarith
  · linarith

theorem minkFun_continuous : Continuous minkFun :=
  minkFun_strictMono.monotone.continuous_of_denseRange minkFun_denseRange

theorem minkFun_surjective : Function.Surjective minkFun := by
  intro z
  have hk0 := minkFun_intCast ⌊z⌋
  have hk1 : minkFun (⌊z⌋ + 1) = ⌊z⌋ + 1 := by rw [minkFun_add_one, hk0]
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc (show (⌊z⌋ : ℝ) ≤ ⌊z⌋ + 1 by linarith)
    minkFun_continuous.continuousOn
    (show z ∈ Icc (minkFun ⌊z⌋) (minkFun (⌊z⌋ + 1)) by
      rw [hk0, hk1]; exact ⟨Int.floor_le z, (Int.lt_floor_add_one z).le⟩)
  exact ⟨x, hx⟩

theorem mink_continuousOn : ContinuousOn mink (Icc 0 1) :=
  minkFun_continuous.continuousOn.congr fun _ hx => (minkFun_eq_mink hx).symm

theorem mink_image : mink '' Icc 0 1 = Icc 0 1 := by
  apply subset_antisymm
  · rintro _ ⟨x, hx, rfl⟩; exact mink_mem hx
  · have := intermediate_value_Icc zero_le_one mink_continuousOn
    rwa [mink_zero, mink_one] at this

end Mink

/-- The periodic extension of `mink`, as an order isomorphism of `ℝ`. -/
noncomputable def minkR : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective minkFun Mink.minkFun_strictMono Mink.minkFun_surjective

/-- `mink` as a map of `UI`. -/
noncomputable def minkUI (x : UI) : UI := ⟨mink x, Mink.mink_mem x.2⟩

theorem minkUI_strictMono : StrictMono minkUI := fun x y h =>
  Mink.mink_strictMonoOn x.2 y.2 h

theorem minkUI_surjective : Function.Surjective minkUI := by
  intro y
  have : (y : ℝ) ∈ mink '' Icc 0 1 := by rw [Mink.mink_image]; exact y.2
  obtain ⟨x, hx, hxy⟩ := this
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- Minkowski's question-mark function as an order isomorphism of `[0,1]`. -/
noncomputable def minkIso : UI ≃o UI :=
  StrictMono.orderIsoOfSurjective minkUI minkUI_strictMono minkUI_surjective

namespace Mink

theorem minkR_add_one (x : ℝ) : minkR (x + 1) = minkR x + 1 := minkFun_add_one x

theorem minkR_eq_mink {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : minkR x = mink x := minkFun_eq_mink hx

/-- The Farey breakpoints of the tree `t` below the node `w` go to the dyadic ones. -/
theorem map_fareyMarksAux (t : TTree) (w : List Bool) :
    (fareyMarksAux t (fareyNode w)).map (fun I => mink I.lo) =
      t.marksAux (dyadicNode w).1 (dyadicNode w).2 := by
  induction t generalizing w with
  | leaf => simp [fareyMarksAux, TTree.marksAux]
  | node l r ihl ihr =>
    simp only [fareyMarksAux, TTree.marksAux, List.map_append, List.map_cons]
    rw [← fareyNode_append_false, ← fareyNode_append_true, ihl, ihr, mink_lo,
      dyadicNode_append_false, dyadicNode_append_true]

theorem map_mink_fareyMarks (t : TTree) : (fareyMarks t).map mink = TTree.marks t := by
  have h := map_fareyMarksAux t []
  rw [dyadicNode_nil] at h
  simp only [fareyMarks, TTree.marks, List.map_cons, List.map_append, List.map_map,
    mink_zero, mink_one]
  rw [← h]
  rfl

end Mink

end CannonFloydParry.S7
end

section
/-!
# Farey intervals and integral projective maps of `[0,1]` (CFP §7, pp. 251–253)

Basic facts: the action of `GL(2, ℤ)` on `(t, 1)`, Farey intervals, and the explicit linear
fractional map `mob I J` between two Farey intervals.
-/

namespace CannonFloydParry.S7

open FracInterval

/-! ### `glAct` on `(t, 1)` -/

lemma glAct_t0 (A : GL (Fin 2) ℤ) (t : ℝ) :
    glAct A ![t, 1] 0 = ((A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℝ) * t +
      ((A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℝ) := by
  simp [glAct, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma glAct_t1 (A : GL (Fin 2) ℤ) (t : ℝ) :
    glAct A ![t, 1] 1 = ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) * t +
      ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) := by
  simp [glAct, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma det_GL (A : GL (Fin 2) ℤ) :
    (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
        (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 ∨
      (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
        (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = -1 := by
  have h := Matrix.isUnits_det_units A
  rw [Matrix.det_fin_two] at h
  exact Int.isUnit_iff.mp h

lemma glAct_entries (A : GL (Fin 2) ℤ) : ∃ p q r s : ℤ, (p * s - q * r = 1 ∨ p * s - q * r = -1) ∧
    ∀ t : ℝ, glAct A ![t, 1] 0 = (p : ℝ) * t + q ∧ glAct A ![t, 1] 1 = (r : ℝ) * t + s :=
  ⟨_, _, _, _, det_GL A, fun t => ⟨glAct_t0 A t, glAct_t1 A t⟩⟩

/-- The denominator of an integral projective map is positive. -/
lemma denom_pos {A : GL (Fin 2) ℤ} {U : Set ℝ} {f : ℝ → ℝ} (h : IsIntegralProjective01Via A U f)
    {t : ℝ} (ht : t ∈ U) : 0 < glAct A ![t, 1] 1 := by
  obtain ⟨h0, h1, -⟩ := h t ht
  by_contra hle
  have hy : glAct A ![t, 1] 1 = 0 := le_antisymm (not_lt.mp hle) (h0.trans h1)
  have hx : glAct A ![t, 1] 0 = 0 := le_antisymm (hy ▸ h1) h0
  rw [glAct_t0] at hx
  rw [glAct_t1] at hy
  set M := (A : Matrix (Fin 2) (Fin 2) ℤ)
  have hd : ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ℝ) = 0 := by
    push_cast
    linear_combination (M 0 0 : ℝ) * hy - (M 1 0 : ℝ) * hx
  rcases det_GL A with h | h <;> rw [h] at hd <;> norm_num at hd

lemma IsIntegralProjective01.mono {U V : Set ℝ} {f : ℝ → ℝ} (h : IsIntegralProjective01 U f)
    (hVU : V ⊆ U) : IsIntegralProjective01 V f := by
  obtain ⟨hU, A, hA⟩ := h
  exact ⟨hVU.trans hU, A, fun t ht => hA t (hVU ht)⟩

/-! ### Farey intervals -/

section Farey

variable {I : FracInterval}

lemma IsFarey.det (hI : I.IsFarey) : (I.a : ℤ) * I.d - (I.b : ℤ) * I.c = -1 := hI.2.2.2.2.2

lemma IsFarey.detR (hI : I.IsFarey) : (I.a : ℝ) * I.d - (I.b : ℝ) * I.c = -1 := by
  exact_mod_cast (IsFarey.det hI)

lemma IsFarey.b_pos (hI : I.IsFarey) : (0 : ℝ) < I.b := by exact_mod_cast hI.1
lemma IsFarey.d_pos (hI : I.IsFarey) : (0 : ℝ) < I.d := by exact_mod_cast hI.2.2.1
lemma IsFarey.a_le_b (hI : I.IsFarey) : (I.a : ℝ) ≤ I.b := by exact_mod_cast hI.2.2.2.1
lemma IsFarey.c_le_d (hI : I.IsFarey) : (I.c : ℝ) ≤ I.d := by exact_mod_cast hI.2.2.2.2.1

lemma IsFarey.leftPart (hI : I.IsFarey) : I.leftPart.IsFarey := by
  obtain ⟨hb, hc, hd, hab, hcd, hdet⟩ := hI
  refine ⟨hb, by simp [FracInterval.leftPart]; omega, by simp [FracInterval.leftPart]; omega,
    le_refl _ |>.trans hab, by simp [FracInterval.leftPart]; omega, ?_⟩
  simp only [FracInterval.leftPart]
  push_cast
  linear_combination hdet

lemma IsFarey.rightPart (hI : I.IsFarey) : I.rightPart.IsFarey := by
  obtain ⟨hb, hc, hd, hab, hcd, hdet⟩ := hI
  refine ⟨by simp [FracInterval.rightPart]; omega, hc, hd, by simp [FracInterval.rightPart]; omega,
    hcd, ?_⟩
  simp only [FracInterval.rightPart]
  push_cast
  linear_combination hdet

lemma IsFarey.isCoprime_ab (hI : I.IsFarey) : IsCoprime (I.a : ℤ) (I.b : ℤ) :=
  ⟨-(I.d : ℤ), I.c, by linear_combination (-1 : ℤ) * (IsFarey.det hI)⟩

lemma IsFarey.isCoprime_cd (hI : I.IsFarey) : IsCoprime (I.c : ℤ) (I.d : ℤ) :=
  ⟨I.b, -(I.a : ℤ), by linear_combination (-1 : ℤ) * (IsFarey.det hI)⟩

lemma IsFarey.lo_nonneg (hI : I.IsFarey) : 0 ≤ I.lo := by
  unfold FracInterval.lo; positivity

lemma IsFarey.hi_le_one (hI : I.IsFarey) : I.hi ≤ 1 := by
  unfold FracInterval.hi
  rw [div_le_one (IsFarey.d_pos hI)]; exact (IsFarey.c_le_d hI)

lemma IsFarey.lo_lt_hi (hI : I.IsFarey) : I.lo < I.hi := by
  unfold FracInterval.lo FracInterval.hi
  rw [div_lt_div_iff₀ (IsFarey.b_pos hI) (IsFarey.d_pos hI)]
  linarith [(IsFarey.detR hI)]

lemma IsFarey.Icc_subset (hI : I.IsFarey) : Set.Icc I.lo I.hi ⊆ Set.Icc 0 1 :=
  Set.Icc_subset_Icc (IsFarey.lo_nonneg hI) (IsFarey.hi_le_one hI)

end Farey

/-! ### Reduced fractions -/

/-! ### A continuous map with the right bounds maps `[l, h]` onto `[f l, f h]` -/

lemma image_Icc_of_bounds {f : ℝ → ℝ} {l h : ℝ} (hlh : l ≤ h) (hc : ContinuousOn f (Set.Icc l h))
    (hb : ∀ t ∈ Set.Icc l h, f l ≤ f t ∧ f t ≤ f h) : f '' Set.Icc l h = Set.Icc (f l) (f h) := by
  apply le_antisymm
  · rintro _ ⟨t, ht, rfl⟩; exact hb t ht
  · exact intermediate_value_Icc hlh hc

lemma image_Icc_of_bounds' {f : ℝ → ℝ} {l h : ℝ} (hlh : l ≤ h) (hc : ContinuousOn f (Set.Icc l h))
    (hb : ∀ t ∈ Set.Icc l h, f h ≤ f t ∧ f t ≤ f l) : f '' Set.Icc l h = Set.Icc (f h) (f l) := by
  apply le_antisymm
  · rintro _ ⟨t, ht, rfl⟩; exact hb t ht
  · exact intermediate_value_Icc' hlh hc

end CannonFloydParry.S7
end

section
/-!
# The linear fractional map between two Farey intervals (CFP §7, p. 252)

`mob I J` is the map `ρ ∘ (M_J M_I⁻¹)` in the coordinate `t`; it is integral projective on
`[I.lo, I.hi]`, maps it onto `[J.lo, J.hi]` endpoint to endpoint, and it is the only integral
projective map on `[I.lo, I.hi]` with those endpoint values.
-/

namespace CannonFloydParry.S7


/-- Numerator of the map `I → J`. -/
noncomputable def mobN (I J : FracInterval) (t : ℝ) : ℝ :=
  ((J.c : ℝ) * I.b - (J.a : ℝ) * I.d) * t + ((J.a : ℝ) * I.c - (J.c : ℝ) * I.a)

/-- Denominator of the map `I → J`. -/
noncomputable def mobD (I J : FracInterval) (t : ℝ) : ℝ :=
  ((J.d : ℝ) * I.b - (J.b : ℝ) * I.d) * t + ((J.b : ℝ) * I.c - (J.d : ℝ) * I.a)

/-- The linear fractional map carrying `[I.lo, I.hi]` onto `[J.lo, J.hi]`. -/
noncomputable def mob (I J : FracInterval) (t : ℝ) : ℝ := mobN I J t / mobD I J t

lemma mobN_eq (I J : FracInterval) (t : ℝ) :
    mobN I J t = ((I.c : ℝ) - I.d * t) * J.a + ((I.b : ℝ) * t - I.a) * J.c := by
  unfold mobN; ring

lemma mobD_eq (I J : FracInterval) (t : ℝ) :
    mobD I J t = ((I.c : ℝ) - I.d * t) * J.b + ((I.b : ℝ) * t - I.a) * J.d := by
  unfold mobD; ring

variable {I J : FracInterval}

lemma alpha_nonneg (hI : I.IsFarey) {t : ℝ} (ht : t ∈ Set.Icc I.lo I.hi) :
    0 ≤ (I.c : ℝ) - I.d * t := by
  have h := ht.2
  unfold FracInterval.hi at h
  rw [le_div_iff₀ (IsFarey.d_pos hI)] at h
  linarith

lemma beta_nonneg (hI : I.IsFarey) {t : ℝ} (ht : t ∈ Set.Icc I.lo I.hi) :
    0 ≤ (I.b : ℝ) * t - I.a := by
  have h := ht.1
  unfold FracInterval.lo at h
  rw [div_le_iff₀ (IsFarey.b_pos hI)] at h
  linarith

lemma alpha_beta (hI : I.IsFarey) (t : ℝ) :
    (I.b : ℝ) * ((I.c : ℝ) - I.d * t) + (I.d : ℝ) * ((I.b : ℝ) * t - I.a) = 1 := by
  linear_combination -(IsFarey.detR hI)

lemma mobD_pos (hI : I.IsFarey) (hJ : J.IsFarey) {t : ℝ} (ht : t ∈ Set.Icc I.lo I.hi) :
    0 < mobD I J t := by
  rw [mobD_eq]
  have hα := alpha_nonneg hI ht
  have hβ := beta_nonneg hI ht
  have hab := alpha_beta hI t
  have hb := IsFarey.b_pos hJ
  have hd := IsFarey.d_pos hJ
  rcases hα.lt_or_eq with hα | hα
  · have := mul_pos hα hb
    nlinarith [mul_nonneg hβ hd.le]
  · rw [← hα] at hab ⊢
    have : 0 < (I.b : ℝ) * t - I.a := by
      by_contra h
      have : (I.b : ℝ) * t - I.a = 0 := le_antisymm (not_lt.mp h) hβ
      rw [this] at hab; simp at hab
    simp only [zero_mul, zero_add]
    exact mul_pos this hd

lemma continuousOn_mob (hI : I.IsFarey) (hJ : J.IsFarey) :
    ContinuousOn (mob I J) (Set.Icc I.lo I.hi) := by
  unfold mob mobN mobD
  exact ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => (mobD_pos hI hJ ht).ne'

/-- The integer matrix of the map. -/
def mobMat (I J : FracInterval) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(J.c : ℤ) * I.b - (J.a : ℤ) * I.d, (J.a : ℤ) * I.c - (J.c : ℤ) * I.a;
     (J.d : ℤ) * I.b - (J.b : ℤ) * I.d, (J.b : ℤ) * I.c - (J.d : ℤ) * I.a]

lemma mobMat_det (hI : I.IsFarey) (hJ : J.IsFarey) : (mobMat I J).det = 1 := by
  rw [Matrix.det_fin_two]
  simp only [mobMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  linear_combination ((I.a : ℤ) * I.d - (I.b : ℤ) * I.c) * (IsFarey.det hJ) - (IsFarey.det hI)

/-- The matrix as an element of `GL(2, ℤ)`. -/
def glOfDetOne (M : Matrix (Fin 2) (Fin 2) ℤ) (h : M.det = 1) : GL (Fin 2) ℤ :=
  ⟨M, M.adjugate, by rw [Matrix.mul_adjugate, h, one_smul],
    by rw [Matrix.adjugate_mul, h, one_smul]⟩

lemma mob_via (hI : I.IsFarey) (hJ : J.IsFarey) :
    IsIntegralProjective01Via (glOfDetOne (mobMat I J) (mobMat_det hI hJ))
      (Set.Icc I.lo I.hi) (mob I J) := by
  intro t ht
  have e0 : glAct (glOfDetOne (mobMat I J) (mobMat_det hI hJ)) ![t, 1] 0 = mobN I J t := by
    rw [glAct_t0]
    simp [glOfDetOne, mobMat, mobN]
  have e1 : glAct (glOfDetOne (mobMat I J) (mobMat_det hI hJ)) ![t, 1] 1 = mobD I J t := by
    rw [glAct_t1]
    simp [glOfDetOne, mobMat, mobD]
  rw [e0, e1]
  refine ⟨?_, ?_, rfl⟩
  · rw [mobN_eq]
    have := alpha_nonneg hI ht
    have := beta_nonneg hI ht
    positivity
  · rw [mobN_eq, mobD_eq]
    have := mul_nonneg (alpha_nonneg hI ht) (sub_nonneg.mpr (IsFarey.a_le_b hJ))
    have := mul_nonneg (beta_nonneg hI ht) (sub_nonneg.mpr (IsFarey.c_le_d hJ))
    nlinarith

lemma mob_isIP (hI : I.IsFarey) (hJ : J.IsFarey) :
    IsIntegralProjective01 (Set.Icc I.lo I.hi) (mob I J) :=
  ⟨IsFarey.Icc_subset hI, _, mob_via hI hJ⟩

lemma lo_mem (hI : I.IsFarey) : I.lo ∈ Set.Icc I.lo I.hi := ⟨le_rfl, (IsFarey.lo_lt_hi hI).le⟩
lemma hi_mem (hI : I.IsFarey) : I.hi ∈ Set.Icc I.lo I.hi := ⟨(IsFarey.lo_lt_hi hI).le, le_rfl⟩

lemma mob_lo (hI : I.IsFarey) (hJ : J.IsFarey) : mob I J I.lo = J.lo := by
  have hD := mobD_pos hI hJ (lo_mem hI)
  have hb := IsFarey.b_pos hI
  unfold mob FracInterval.lo at *
  rw [div_eq_div_iff hD.ne' (IsFarey.b_pos hJ).ne']
  unfold mobN mobD
  field_simp
  ring

lemma mob_hi (hI : I.IsFarey) (hJ : J.IsFarey) : mob I J I.hi = J.hi := by
  have hD := mobD_pos hI hJ (hi_mem hI)
  have hd := IsFarey.d_pos hI
  unfold mob FracInterval.hi at *
  rw [div_eq_div_iff hD.ne' (IsFarey.d_pos hJ).ne']
  unfold mobN mobD
  field_simp
  ring

lemma mob_bounds (hI : I.IsFarey) (hJ : J.IsFarey) {t : ℝ} (ht : t ∈ Set.Icc I.lo I.hi) :
    J.lo ≤ mob I J t ∧ mob I J t ≤ J.hi := by
  have hD := mobD_pos hI hJ ht
  have hβ := beta_nonneg hI ht
  have hα := alpha_nonneg hI ht
  have hdJ := IsFarey.detR hJ
  unfold mob FracInterval.lo FracInterval.hi
  constructor
  · rw [div_le_div_iff₀ (IsFarey.b_pos hJ) hD, mobN_eq, mobD_eq]
    nlinarith
  · rw [div_le_div_iff₀ hD (IsFarey.d_pos hJ), mobN_eq, mobD_eq]
    nlinarith

lemma mob_image (hI : I.IsFarey) (hJ : J.IsFarey) :
    mob I J '' Set.Icc I.lo I.hi = Set.Icc J.lo J.hi := by
  have h := image_Icc_of_bounds (IsFarey.lo_lt_hi hI).le (continuousOn_mob hI hJ)
    (fun t ht => by rw [mob_lo hI hJ, mob_hi hI hJ]; exact mob_bounds hI hJ ht)
  rwa [mob_lo hI hJ, mob_hi hI hJ] at h

/-! ### Uniqueness -/

lemma prim_mult {x y u v : ℤ} (hc : IsCoprime x y) (hy : 0 < y) (hv : 0 < v)
    (h : x * v = u * y) : ∃ l : ℤ, 0 < l ∧ u = l * x ∧ v = l * y := by
  obtain ⟨k, hk⟩ : y ∣ v := hc.symm.dvd_of_dvd_mul_left ⟨u, by rw [h]; ring⟩
  refine ⟨k, ?_, ?_, by rw [hk]; ring⟩
  · rw [hk] at hv
    exact pos_of_mul_pos_right hv hy.le
  · rw [hk] at h
    have : (u - k * x) * y = 0 := by linear_combination -h
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · exact absurd h' hy.ne'

lemma mob_unique (hI : I.IsFarey) (hJ : J.IsFarey) {g : ℝ → ℝ}
    (hg : IsIntegralProjective01 (Set.Icc I.lo I.hi) g) (hlo : g I.lo = J.lo)
    (hhi : g I.hi = J.hi) : Set.EqOn g (mob I J) (Set.Icc I.lo I.hi) := by
  obtain ⟨-, B, hB⟩ := hg
  obtain ⟨p, q, r, s, hdet, hgl⟩ := glAct_entries B
  have hbI := IsFarey.b_pos hI
  have hdI := IsFarey.d_pos hI
  have hbJ := IsFarey.b_pos hJ
  have hdJ := IsFarey.d_pos hJ
  -- at the left endpoint
  have y0 := denom_pos hB (lo_mem hI)
  have g0 := (hB _ (lo_mem hI)).2.2
  rw [(hgl _).2] at y0
  rw [hlo, (hgl _).1, (hgl _).2] at g0
  have hv0 : (0 : ℝ) < r * I.a + s * I.b := by
    have : (r : ℝ) * I.a + s * I.b = I.b * (r * I.lo + s) := by
      unfold FracInterval.lo; field_simp
    rw [this]; positivity
  have huv0 : (J.a : ℝ) * (r * I.a + s * I.b) = (p * I.a + q * I.b) * J.b := by
    have y0' := y0
    unfold FracInterval.lo at g0 y0'
    rw [div_eq_div_iff hbJ.ne' y0'.ne'] at g0
    field_simp at g0
    linear_combination g0
  -- at the right endpoint
  have y1 := denom_pos hB (hi_mem hI)
  have g1 := (hB _ (hi_mem hI)).2.2
  rw [(hgl _).2] at y1
  rw [hhi, (hgl _).1, (hgl _).2] at g1
  have hv1 : (0 : ℝ) < r * I.c + s * I.d := by
    have : (r : ℝ) * I.c + s * I.d = I.d * (r * I.hi + s) := by
      unfold FracInterval.hi; field_simp
    rw [this]; positivity
  have huv1 : (J.c : ℝ) * (r * I.c + s * I.d) = (p * I.c + q * I.d) * J.d := by
    have y1' := y1
    unfold FracInterval.hi at g1 y1'
    rw [div_eq_div_iff hdJ.ne' y1'.ne'] at g1
    field_simp at g1
    linear_combination g1
  obtain ⟨l, hl, hl1, hl2⟩ := prim_mult (IsFarey.isCoprime_ab hJ) (by exact_mod_cast hJ.1)
    (by exact_mod_cast hv0) (by exact_mod_cast huv0)
  obtain ⟨m, hm, hm1, hm2⟩ := prim_mult (IsFarey.isCoprime_cd hJ) (by exact_mod_cast hJ.2.2.1)
    (by exact_mod_cast hv1) (by exact_mod_cast huv1)
  have hdI' := IsFarey.det hI
  have hdJ' := IsFarey.det hJ
  have hlm : l * m = p * s - q * r := by
    have key : (p * I.a + q * I.b) * (r * I.c + s * I.d) - (p * I.c + q * I.d) * (r * I.a + s * I.b)
        = (p * s - q * r) * ((I.a : ℤ) * I.d - (I.b : ℤ) * I.c) := by ring
    rw [hl1, hl2, hm1, hm2, hdI'] at key
    linear_combination -key + l * m * hdJ'
  have hl1' : l = 1 := by
    rcases hdet with h | h
    · exact Int.eq_one_of_mul_eq_one_right hl.le (hlm.trans h)
    · nlinarith [mul_pos hl hm]
  have hm1' : m = 1 := by
    rw [hl1', one_mul] at hlm
    rcases hdet with h | h
    · exact hlm.trans h
    · nlinarith
  subst hl1' hm1'
  simp only [one_mul] at hl1 hl2 hm1 hm2
  have ep : p = (J.c : ℤ) * I.b - (J.a : ℤ) * I.d := by
    linear_combination (-(I.d : ℤ)) * hl1 + (I.b : ℤ) * hm1 + p * hdI'
  have eq' : q = (J.a : ℤ) * I.c - (J.c : ℤ) * I.a := by
    linear_combination (-(I.a : ℤ)) * hm1 + (I.c : ℤ) * hl1 + q * hdI'
  have er : r = (J.d : ℤ) * I.b - (J.b : ℤ) * I.d := by
    linear_combination (-(I.d : ℤ)) * hl2 + (I.b : ℤ) * hm2 + r * hdI'
  have es : s = (J.b : ℤ) * I.c - (J.d : ℤ) * I.a := by
    linear_combination (-(I.a : ℤ)) * hm2 + (I.c : ℤ) * hl2 + s * hdI'
  intro t ht
  rw [(hB t ht).2.2, (hgl _).1, (hgl _).2, ep, eq', er, es]
  unfold mob mobN mobD
  push_cast
  rfl

end CannonFloydParry.S7
end

section
/-!
# Integral subsimplices of `[0,1]` and the maps between them (CFP §7, pp. 251–253)
-/

namespace CannonFloydParry.S7

/-- The root `[0/1, 1/1]` of the Farey tree. -/
def root : FracInterval := ⟨0, 1, 1, 1⟩

lemma root_isFarey : root.IsFarey := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by norm_num [root]⟩

lemma root_Icc : Set.Icc root.lo root.hi = Set.Icc 0 1 := by
  simp [root, FracInterval.lo, FracInterval.hi]

lemma subsimplex_of_farey {K : FracInterval} (hK : K.IsFarey) : IsIntegralSubsimplex01 K.lo K.hi :=
  ⟨mob root K, root_Icc ▸ mob_isIP root_isFarey hK, root_Icc ▸ mob_image root_isFarey hK⟩

/-- Every integral subsimplex of `[0,1]` is a Farey interval. -/
lemma exists_farey_of_subsimplex {p q : ℝ} (h : IsIntegralSubsimplex01 p q) :
    ∃ K : FracInterval, K.IsFarey ∧ K.lo = p ∧ K.hi = q := by
  obtain ⟨f, ⟨-, B, hB⟩, himg⟩ := h
  obtain ⟨P, Q, R, S, hdet, hgl⟩ := glAct_entries B
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have y0 := denom_pos hB h0
  have y1 := denom_pos hB h1
  obtain ⟨x0, xy0, -⟩ := hB 0 h0
  obtain ⟨x1, xy1, -⟩ := hB 1 h1
  rw [(hgl _).2] at y0 y1 xy0 xy1
  rw [(hgl _).1] at x0 x1 xy0 xy1
  simp only [mul_zero, zero_add, mul_one] at y0 y1 xy0 xy1 x0 x1
  have iQ : 0 ≤ Q := by exact_mod_cast x0
  have iS : 0 < S := by exact_mod_cast y0
  have iQS : Q ≤ S := by exact_mod_cast xy0
  have iX : 0 ≤ P + Q := by exact_mod_cast x1
  have iY : 0 < R + S := by exact_mod_cast y1
  have iXY : P + Q ≤ R + S := by exact_mod_cast xy1
  lift Q to ℕ using iQ with a
  lift S to ℕ using iS.le with b
  obtain ⟨c, hc⟩ : ∃ c : ℕ, P + a = c := ⟨(P + a).toNat, (Int.toNat_of_nonneg iX).symm⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ, R + b = d := ⟨(R + b).toNat, (Int.toNat_of_nonneg iY.le).symm⟩
  have hP : P = c - a := by omega
  have hR : R = d - b := by omega
  subst hP hR
  have hb : 0 < b := by exact_mod_cast iS
  have hd0 : 0 < d := by omega
  have hab : a ≤ b := by exact_mod_cast iQS
  have hcd : c ≤ d := by omega
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  -- the formula for `f`
  have hden : ∀ t ∈ Set.Icc (0 : ℝ) 1, (0 : ℝ) < ((d : ℝ) - b) * t + b := by
    intro t ht
    have := denom_pos hB ht
    rw [(hgl _).2] at this
    push_cast at this
    exact this
  have hf : Set.EqOn f (fun t => (((c : ℝ) - a) * t + a) / (((d : ℝ) - b) * t + b))
      (Set.Icc 0 1) := by
    intro t ht
    rw [(hB t ht).2.2, (hgl _).1, (hgl _).2]
    push_cast
    rfl
  have hcont : ContinuousOn f (Set.Icc 0 1) :=
    ContinuousOn.congr (ContinuousOn.div (by fun_prop) (by fun_prop)
      fun t ht => (hden t ht).ne') hf
  have f0 : f 0 = (a : ℝ) / b := by rw [hf h0]; simp
  have f1 : f 1 = (c : ℝ) / d := by rw [hf h1]; simp
  have hdR' : ((c - a : ℤ) * b - a * (d - b) : ℤ) = (c : ℤ) * b - a * d := by ring
  rcases hdet with hdet | hdet <;> rw [hdR'] at hdet
  · -- orientation preserving: `K = [a/b, c/d]`
    have hK : (⟨a, b, c, d⟩ : FracInterval).IsFarey := by
      refine ⟨hb, ?_, hd0, hab, hcd, by simp only; linarith⟩
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; push_cast at hdet; nlinarith
      · exact h
    have hdetR : (c : ℝ) * b - a * d = 1 := by exact_mod_cast hdet
    have himg' : f '' Set.Icc 0 1 = Set.Icc (f 0) (f 1) := by
      refine image_Icc_of_bounds zero_le_one hcont fun t ht => ?_
      have hD := hden t ht
      rw [f0, f1, hf ht]
      constructor
      · rw [div_le_div_iff₀ hbR hD]; nlinarith [ht.1]
      · rw [div_le_div_iff₀ hD hdR]; nlinarith [ht.2]
    rw [himg', f0, f1] at himg
    have hle : (a : ℝ) / b ≤ c / d := by
      rw [div_le_div_iff₀ hbR hdR]; linarith
    obtain ⟨hp, hq⟩ := (Set.Icc_eq_Icc_iff hle).mp himg
    exact ⟨_, hK, hp, hq⟩
  · -- orientation reversing: `K = [c/d, a/b]`
    have hK : (⟨c, d, a, b⟩ : FracInterval).IsFarey := by
      refine ⟨hd0, ?_, hb, hcd, hab, by simp only; linarith⟩
      rcases Nat.eq_zero_or_pos a with h | h
      · subst h; push_cast at hdet; nlinarith
      · exact h
    have hdetR : (c : ℝ) * b - a * d = -1 := by exact_mod_cast hdet
    have himg' : f '' Set.Icc 0 1 = Set.Icc (f 1) (f 0) := by
      refine image_Icc_of_bounds' zero_le_one hcont fun t ht => ?_
      have hD := hden t ht
      rw [f0, f1, hf ht]
      constructor
      · rw [div_le_div_iff₀ hdR hD]; nlinarith [ht.2]
      · rw [div_le_div_iff₀ hD hbR]; nlinarith [ht.1]
    rw [himg', f0, f1] at himg
    have hle : (c : ℝ) / d ≤ a / b := by
      rw [div_le_div_iff₀ hdR hbR]; linarith
    obtain ⟨hp, hq⟩ := (Set.Icc_eq_Icc_iff hle).mp himg
    exact ⟨_, hK, hp, hq⟩

/-! ### Target: the criterion of p. 251 -/


/-! ### Target: the two parts are integral subsimplices -/


/-! ### Target: the unique integral projective map between two Farey intervals -/


/-! ### Target: restriction and gluing -/


end CannonFloydParry.S7
end

section
/-!
# The tree `𝒯′` of integral subsimplices of `[0,1]` (CFP §7, p. 252)
-/

namespace CannonFloydParry.S7

/-- One step down the Farey tree. -/
def fstep (I : FracInterval) (x : Bool) : FracInterval := if x then I.rightPart else I.leftPart

lemma fareyNode_eq (w : List Bool) : fareyNode w = w.foldl fstep root := rfl

lemma fareyNode_nil : fareyNode [] = root := rfl

lemma fareyNode_append (w : List Bool) (x : Bool) :
    fareyNode (w ++ [x]) = fstep (fareyNode w) x := by
  simp [fareyNode_eq, List.foldl_append]

/-- Euclid descent: every Farey interval is a vertex of `𝒯′`. -/
lemma exists_fareyNode_aux (n : ℕ) :
    ∀ K : FracInterval, K.IsFarey → K.b + K.d = n → ∃ w, fareyNode w = K := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rintro ⟨a, b, c, d⟩ ⟨hb, hc, hd, hab, hcd, hdet⟩ hn
  simp only at hb hc hd hab hcd hdet hn
  have hN : a * d + 1 = b * c := by
    have : ((a * d + 1 : ℕ) : ℤ) = ((b * c : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  rcases lt_trichotomy b d with hbd | hbd | hbd
  · -- a left part: parent `[a/b, (c-a)/(d-b)]`
    have hac : a ≤ c := by
      by_contra h
      push Not at h
      nlinarith
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hac
    obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_lt hbd
    have hN' : a * (f + 1) + 1 = b * e := by nlinarith
    have he : 0 < e := by
      rcases Nat.eq_zero_or_pos e with h | h
      · subst h; simp at hN'
      · exact h
    have hef : e ≤ f + 1 := by
      by_contra h
      push Not at h
      have hb1 : b ≤ 1 := by nlinarith
      have hb1' : b = 1 := by omega
      subst hb1'
      have ha : a ≤ 1 := hab
      interval_cases a <;> omega
    have hlt : b + (f + 1) < n := by omega
    have hZ : (a : ℤ) * (f + 1) + 1 = b * e := by exact_mod_cast hN'
    have hK' : (⟨a, b, e, f + 1⟩ : FracInterval).IsFarey :=
      ⟨hb, he, by simp, hab, hef, by push_cast; linear_combination hZ⟩
    obtain ⟨w, hw⟩ := ih (b + (f + 1)) hlt ⟨a, b, e, f + 1⟩ hK' rfl
    refine ⟨w ++ [false], ?_⟩
    rw [fareyNode_append, hw]
    simp [fstep, FracInterval.leftPart]
    omega
  · -- the root
    subst hbd
    have hca : a < c := by
      by_contra h
      push Not at h
      nlinarith
    have hb1 : b = 1 := by
      have : b * (a + 1) ≤ b * c := Nat.mul_le_mul_left b hca
      nlinarith
    subst hb1
    have hc1 : c = 1 := by omega
    subst hc1
    have ha0 : a = 0 := by omega
    subst ha0
    exact ⟨[], rfl⟩
  · -- a right part: parent `[(a-c)/(b-d), c/d]`
    have hca : c ≤ a := by
      by_contra h
      push Not at h
      nlinarith
    obtain ⟨h', rfl⟩ := Nat.exists_eq_add_of_le hca
    obtain ⟨g, rfl⟩ := Nat.exists_eq_add_of_lt hbd
    have hN' : h' * d + 1 = (g + 1) * c := by nlinarith
    have hhg : h' ≤ g + 1 := by
      by_contra h
      push Not at h
      nlinarith
    have hlt : g + 1 + d < n := by omega
    have hZ : (h' : ℤ) * d + 1 = (g + 1) * c := by exact_mod_cast hN'
    have hK' : (⟨h', g + 1, c, d⟩ : FracInterval).IsFarey :=
      ⟨by simp, hc, hd, hhg, hcd, by push_cast; linear_combination hZ⟩
    obtain ⟨w, hw⟩ := ih (g + 1 + d) hlt ⟨h', g + 1, c, d⟩ hK' rfl
    refine ⟨w ++ [true], ?_⟩
    rw [fareyNode_append, hw]
    simp [fstep, FracInterval.rightPart]
    omega

lemma exists_fareyNode {K : FracInterval} (hK : K.IsFarey) : ∃ w, fareyNode w = K :=
  exists_fareyNode_aux _ K hK rfl


end CannonFloydParry.S7
end

section
/-!
# Transport through Minkowski's `?`: basic lemmas

List lemmas, the Farey pieces of `fareyMarks`, the conjugation identity
`mink ∘ mob I J = affine ∘ mink` on a Farey node, composition of integral projective maps, and
`IsThompson` from an affine-pieces chain.
-/

namespace CannonFloydParry.S7

open FracInterval Set

/-! ### Lists -/

theorem chain_and {α : Type*} {R S : α → α → Prop} :
    ∀ {l : List α}, l.IsChain R → l.IsChain S → l.IsChain (fun a b => R a b ∧ S a b)
  | [], _, _ => List.IsChain.nil
  | [a], _, _ => List.IsChain.singleton a
  | a :: b :: l, h1, h2 => by
    rw [List.isChain_cons_cons] at h1 h2 ⊢
    exact ⟨⟨h1.1, h2.1⟩, chain_and h1.2 h2.2⟩

theorem chain_cover {R : ℝ → ℝ → Prop} :
    ∀ (l : List ℝ) (a b m : ℝ), (a :: l).IsChain R → (a :: l).getLast? = some b → a < b →
      a ≤ m → m ≤ b → ∃ u v, u ∈ a :: l ∧ v ∈ a :: l ∧ R u v ∧ u ≤ m ∧ m ≤ v
  | [], a, b, m, _, hl, hab, _, _ => by
    simp at hl; subst hl; exact absurd hab (lt_irrefl _)
  | c :: l, a, b, m, hc, hl, hab, ham, hmb => by
    rw [List.isChain_cons_cons] at hc
    by_cases hmc : m ≤ c
    · exact ⟨a, c, by simp, by simp, hc.1, ham, hmc⟩
    · have hl' : (c :: l).getLast? = some b := by
        rw [← hl]; simp [List.getLast?_cons_cons]
      have hcm : c < m := lt_of_not_ge hmc
      obtain ⟨u, v, hu, hv, h⟩ := chain_cover l c b m hc.2 hl' (by linarith) hcm.le hmb
      exact ⟨u, v, List.mem_cons_of_mem _ hu, List.mem_cons_of_mem _ hv, h⟩

theorem chain_join {α : Type*} {R : α → α → Prop} {a b c : α} {xs ys : List α}
    (h1 : (a :: (xs ++ [b])).IsChain R) (h2 : (b :: (ys ++ [c])).IsChain R) :
    (a :: (xs ++ b :: (ys ++ [c]))).IsChain R := by
  have e : a :: (xs ++ b :: (ys ++ [c])) = (a :: (xs ++ [b])) ++ (ys ++ [c]) := by simp
  rw [e, List.isChain_append]
  obtain ⟨y, zs, hy⟩ : ∃ y zs, ys ++ [c] = y :: zs := by
    cases ys with
    | nil => exact ⟨c, [], rfl⟩
    | cons y ys => exact ⟨y, ys ++ [c], rfl⟩
  rw [hy] at h2 ⊢
  rw [List.isChain_cons_cons] at h2
  refine ⟨h1, h2.2, ?_⟩
  intro x hx z hz
  have hx' : x = b := by
    have : (a :: (xs ++ [b])).getLast? = some b := by
      rw [List.getLast?_eq_some_getLast (by simp)]; simp
    rw [this] at hx; exact (Option.mem_some_iff.mp hx).symm
  simp at hz
  subst hx' hz
  exact h2.1

/-! ### Farey pieces -/

/-- `[p, q]` is a node of the Farey tree. -/
def FP (p q : ℝ) : Prop := ∃ w, (fareyNode w).lo = p ∧ (fareyNode w).hi = q

theorem fareyNode_lo_nil : (fareyNode []).lo = 0 := by simp [fareyNode, FracInterval.lo]
theorem fareyNode_hi_nil : (fareyNode []).hi = 1 := by simp [fareyNode, FracInterval.hi]

theorem chain_fareyMarksAux (t : TTree) (w : List Bool) :
    ((fareyNode w).lo :: ((fareyMarksAux t (fareyNode w)).map FracInterval.lo ++
      [(fareyNode w).hi])).IsChain FP := by
  induction t generalizing w with
  | leaf =>
    simp only [fareyMarksAux, List.map_nil, List.nil_append]
    exact List.IsChain.cons_cons ⟨w, rfl, rfl⟩ (List.IsChain.singleton _)
  | node l r ihl ihr =>
    have hl := ihl (w ++ [false])
    have hr := ihr (w ++ [true])
    rw [Mink.fareyNode_append_false] at hl
    rw [Mink.fareyNode_append_true] at hr
    simp only [fareyMarksAux, List.map_append, List.map_cons, List.append_assoc,
      List.cons_append]
    exact chain_join hl hr

theorem fareyMarks_eq (t : TTree) : fareyMarks t = (fareyNode []).lo ::
    ((fareyMarksAux t (fareyNode [])).map FracInterval.lo ++ [(fareyNode []).hi]) := by
  rw [fareyNode_lo_nil, fareyNode_hi_nil]; rfl

theorem chain_fareyMarks (t : TTree) : (fareyMarks t).IsChain FP := by
  rw [fareyMarks_eq]; exact chain_fareyMarksAux t []

theorem mem_fareyMarksAux (t : TTree) (w : List Bool) :
    ∀ K ∈ fareyMarksAux t (fareyNode w), ∃ v, K = fareyNode v := by
  induction t generalizing w with
  | leaf => simp [fareyMarksAux]
  | node l r ihl ihr =>
    intro K hK
    simp only [fareyMarksAux, List.mem_append, List.mem_cons] at hK
    rcases hK with h | h | h
    · rw [← Mink.fareyNode_append_false] at h; exact ihl _ K h
    · exact ⟨w ++ [true], by rw [h, Mink.fareyNode_append_true]⟩
    · rw [← Mink.fareyNode_append_true] at h; exact ihr _ K h

theorem fareyNode_lo_mem (w : List Bool) : (fareyNode w).lo ∈ Icc (0 : ℝ) 1 :=
  ⟨(Mink.inv_fareyNode w).lo_nonneg,
    ((Mink.inv_fareyNode w).lo_lt_hi.trans_le (Mink.inv_fareyNode w).hi_le_one).le⟩

theorem fareyNode_hi_mem (w : List Bool) : (fareyNode w).hi ∈ Icc (0 : ℝ) 1 :=
  ⟨(Mink.inv_fareyNode w).lo_nonneg.trans (Mink.inv_fareyNode w).lo_lt_hi.le,
    (Mink.inv_fareyNode w).hi_le_one⟩

theorem mem_fareyMarks {t : TTree} {x : ℝ} (hx : x ∈ fareyMarks t) : x ∈ Icc (0 : ℝ) 1 := by
  simp only [fareyMarks, List.mem_cons, List.mem_append, List.mem_map] at hx
  rcases hx with h | ⟨K, hK, h⟩ | h
  · subst h; exact ⟨le_rfl, zero_le_one⟩
  · obtain ⟨v, rfl⟩ := mem_fareyMarksAux t [] K hK
    subst h; exact fareyNode_lo_mem v
  · rcases h with h | h
    · subst h; exact ⟨zero_le_one, le_rfl⟩
    · simp at h

theorem fareyNode_Icc_subset (w : List Bool) :
    Icc (fareyNode w).lo (fareyNode w).hi ⊆ Icc 0 1 :=
  Icc_subset_Icc (fareyNode_lo_mem w).1 (fareyNode_hi_mem w).2

/-! ### `mob` and `phi` -/

theorem phi_eq_mob_root (I : FracInterval) (s : ℝ) : phi I s = mob root I s := by
  simp only [phi, mob, mobN, mobD, root]
  push_cast
  congr 1 <;> ring

theorem exists_phi_eq {I : FracInterval} (hI : I.IsFarey) {x : ℝ}
    (hx : x ∈ Icc I.lo I.hi) : ∃ s ∈ Icc (0 : ℝ) 1, phi I s = x := by
  rw [← mob_image root_isFarey hI, root_Icc] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  exact ⟨s, hs, phi_eq_mob_root I s⟩

theorem mob_phi {I J : FracInterval} (hI : I.IsFarey) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    mob I J (phi I s) = phi J s := by
  have hb := IsFarey.b_pos hI
  have hd := IsFarey.d_pos hI
  have hdet := IsFarey.detR hI
  set Q : ℝ := (I.b : ℝ) * (1 - s) + I.d * s with hQdef
  have hQ : 0 < Q := by
    rcases eq_or_lt_of_le hs.2 with h1 | h1
    · rw [hQdef, h1]; simpa using hd
    · have : 0 < 1 - s := by linarith
      nlinarith [hs.1]
  set u := phi I s with hudef
  have hu : u * Q = (I.a : ℝ) * (1 - s) + I.c * s := by
    rw [hudef, phi, ← hQdef, div_mul_cancel₀ _ hQ.ne']
  have e1 : mobN I J u * Q = (J.a : ℝ) * (1 - s) + J.c * s := by
    unfold mobN
    linear_combination ((J.c : ℝ) * I.b - (J.a : ℝ) * I.d) * hu +
      (-((J.a : ℝ) * (1 - s) + J.c * s)) * hdet
  have e2 : mobD I J u * Q = (J.b : ℝ) * (1 - s) + J.d * s := by
    unfold mobD
    linear_combination ((J.d : ℝ) * I.b - (J.b : ℝ) * I.d) * hu +
      (-((J.b : ℝ) * (1 - s) + J.d * s)) * hdet
  rw [mob, ← mul_div_mul_right _ _ hQ.ne', e1, e2, phi]

theorem dyadicNode_width_pos (w : List Bool) : 0 < (dyadicNode w).2 - (dyadicNode w).1 := by
  have := (Mink.dyadicNode_bounds w).2.1; linarith

/-- The conjugation identity on a Farey node. -/
theorem mink_mob (w w' : List Bool) {x : ℝ} (hx : x ∈ Icc (fareyNode w).lo (fareyNode w).hi) :
    mink (mob (fareyNode w) (fareyNode w') x) = (dyadicNode w').1 +
      ((dyadicNode w').2 - (dyadicNode w').1) / ((dyadicNode w).2 - (dyadicNode w).1) *
        (mink x - (dyadicNode w).1) := by
  obtain ⟨s, hs, rfl⟩ := exists_phi_eq (Mink.isFarey_fareyNode w) hx
  rw [mob_phi (Mink.isFarey_fareyNode w) hs, Mink.mink_phi w' hs, Mink.mink_phi w hs]
  have := dyadicNode_width_pos w
  field_simp
  ring

theorem width_ratio (w w' : List Bool) :
    ((dyadicNode w').2 - (dyadicNode w').1) / ((dyadicNode w).2 - (dyadicNode w).1) =
      (2 : ℝ) ^ ((w.length : ℤ) - w'.length) := by
  rw [Mink.dyadicNode_width, Mink.dyadicNode_width, zpow_sub₀ (by norm_num), zpow_natCast,
    zpow_natCast]
  rw [one_div, inv_pow, inv_pow]
  field_simp

/-! ### Composition of integral projective maps -/

theorem glAct_mul_t (A B : GL (Fin 2) ℤ) (t : ℝ) (i : Fin 2) :
    glAct (B * A) ![t, 1] i = glAct B (glAct A ![t, 1]) i := by
  simp only [glAct, Units.val_mul]
  rw [Matrix.mulVec_mulVec]
  congr 2
  ext j k
  simp [Matrix.mul_apply]

theorem glAct_smul_trans (A : GL (Fin 2) ℤ) (c : ℝ) (v : Fin 2 → ℝ) :
    glAct A (c • v) = c • glAct A v := by
  simp only [glAct, Matrix.mulVec_smul]

theorem ip_comp {A B : GL (Fin 2) ℤ} {U V : Set ℝ} {f g : ℝ → ℝ}
    (hg : IsIntegralProjective01Via B V g) (hf : IsIntegralProjective01Via A U f)
    (hmaps : ∀ t ∈ U, f t ∈ V) : IsIntegralProjective01Via (B * A) U (g ∘ f) := by
  intro t ht
  have hy := denom_pos hf ht
  obtain ⟨-, -, hft⟩ := hf t ht
  set y := glAct A ![t, 1] 1
  have hv : glAct A ![t, 1] = y • ![f t, 1] := by
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul]
      rw [hft]; field_simp
    · simp [y]
  have e : ∀ i, glAct (B * A) ![t, 1] i = y * glAct B ![f t, 1] i := by
    intro i; rw [glAct_mul_t, hv, glAct_smul_trans]; rfl
  obtain ⟨g0, g1, g2⟩ := hg (f t) (hmaps t ht)
  refine ⟨?_, ?_, ?_⟩
  · rw [e]; positivity
  · rw [e, e]; exact mul_le_mul_of_nonneg_left g1 hy.le
  · rw [e, e, Function.comp_apply, g2, mul_div_mul_left _ _ hy.ne']

/-! ### `extend` -/

theorem extend_coe (g : UI ≃o UI) (z : UI) : extend g (z : ℝ) = (g z : ℝ) := by
  rw [extend_apply, extendFun_of_mem g z.2]

theorem extend_mem (g : UI ≃o UI) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    extend g x ∈ Icc (0 : ℝ) 1 := by
  rw [extend_apply, extendFun_of_mem g hx]; exact (g _).2

/-! ### Dyadic numbers -/

theorem isDyadic_add_half {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) :
    IsDyadic ((x + y) / 2) := by
  obtain ⟨m, k, rfl⟩ := hx
  obtain ⟨m', k', rfl⟩ := hy
  refine ⟨m * 2 ^ k' + m' * 2 ^ k, k + k' + 1, ?_⟩
  push_cast
  field_simp
  ring

theorem isDyadic_dyadicNode (w : List Bool) :
    IsDyadic (dyadicNode w).1 ∧ IsDyadic (dyadicNode w).2 := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨⟨0, 0, by simp [Mink.dyadicNode_nil]⟩, ⟨1, 0, by simp [Mink.dyadicNode_nil]⟩⟩
  | append_singleton w b ih =>
    cases b
    · rw [Mink.dyadicNode_append_false]; exact ⟨ih.1, isDyadic_add_half ih.1 ih.2⟩
    · rw [Mink.dyadicNode_append_true]; exact ⟨isDyadic_add_half ih.1 ih.2, ih.2⟩

/-! ### `IsThompson` from a chain of affine pieces -/

/-- An affine piece with power-of-two slope and dyadic ends. -/
def DPiece (G : ℝ → ℝ) (u v : ℝ) : Prop :=
  IsDyadic u ∧ IsDyadic v ∧ ∃ n : ℤ, ∃ c : ℝ, ∀ z ∈ Icc u v, G z = 2 ^ n * z + c

theorem isThompson_of_chain (g : UI ≃o UI) (ys : List ℝ) (h0 : ys.head? = some 0)
    (h1 : ys.getLast? = some 1) (hc : ys.IsChain (DPiece (extend g))) : IsThompson g := by
  classical
  obtain ⟨a, l, rfl⟩ : ∃ a l, ys = a :: l := by
    cases ys with
    | nil => simp at h0
    | cons a l => exact ⟨a, l, rfl⟩
  simp only [List.head?_cons, Option.some.injEq] at h0
  subst h0
  refine ⟨((0 : ℝ) :: l).toFinset.filter IsDyadic, fun b hb => (Finset.mem_filter.mp hb).2, ?_⟩
  intro x y hxy hB
  obtain ⟨u, v, hu, hv, ⟨du, dv, n, c, hpc⟩, hum, hmv⟩ :=
    chain_cover l 0 1 (((x : ℝ) + y) / 2) hc h1 zero_lt_one (by linarith [x.2.1, y.2.1])
      (by linarith [x.2.2, y.2.2])
  have hux : u ≤ x := by
    by_contra hcon
    have : u ∈ Ioo (x : ℝ) y ∩ ↑(((0 : ℝ) :: l).toFinset.filter IsDyadic) :=
      ⟨⟨lt_of_not_ge hcon, by linarith⟩, by simpa [List.mem_toFinset, du] using hu⟩
    rw [hB] at this; exact this
  have hyv : (y : ℝ) ≤ v := by
    by_contra hcon
    have : v ∈ Ioo (x : ℝ) y ∩ ↑(((0 : ℝ) :: l).toFinset.filter IsDyadic) :=
      ⟨⟨by linarith, lt_of_not_ge hcon⟩, by simpa [List.mem_toFinset, dv] using hv⟩
    rw [hB] at this; exact this
  refine ⟨n, c, fun z hz => ?_⟩
  rw [← extend_coe]
  exact hpc z ⟨hux.trans hz.1, hz.2.trans hyv⟩

end CannonFloydParry.S7
end

section
namespace CannonFloydParry

end CannonFloydParry
end

section
/-!
# Transport of tree diagrams through Minkowski's `?` (CFP p. 253)

`RepresentsPIP d f ↔ Represents d (minkIso * f * minkIso⁻¹)`, the bijection milestone, and
`PIP⁺([0,1])` as the conjugate of `F`.
-/

namespace CannonFloydParry.S7

open Set

/-- Conjugation by Minkowski's `?`. -/
noncomputable def cj : (UI ≃o UI) ≃* (UI ≃o UI) := MulAut.conj minkIso

theorem cj_apply (f : UI ≃o UI) (x : UI) : cj f x = minkIso (f (minkIso.symm x)) := by
  simp only [cj, MulAut.conj_apply]; rfl

theorem minkIso_mk {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    minkIso ⟨x, hx⟩ = ⟨mink x, Mink.mink_mem hx⟩ := Subtype.ext rfl

theorem extend_cj (f : UI ≃o UI) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    extend (cj f) (mink x) = mink (extend f x) := by
  have hm := Mink.mink_mem hx
  rw [extend_apply, extendFun_of_mem _ hm, extend_apply, extendFun_of_mem _ hx, cj_apply,
    ← minkIso_mk hx, OrderIso.symm_apply_apply]
  rfl

theorem mink_injOn : InjOn mink (Icc (0 : ℝ) 1) := Mink.mink_strictMonoOn.injOn

theorem map_mink_inj : ∀ (l₁ l₂ : List ℝ), (∀ x ∈ l₁, x ∈ Icc (0 : ℝ) 1) →
    (∀ x ∈ l₂, x ∈ Icc (0 : ℝ) 1) → l₁.map mink = l₂.map mink → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [mink_injOn (h₁ a (by simp)) (h₂ b (by simp)) h.1,
      map_mink_inj l₁ l₂ (fun x hx => h₁ x (by simp [hx])) (fun x hx => h₂ x (by simp [hx])) h.2]

theorem ip_congr {U : Set ℝ} {f g : ℝ → ℝ} (h : IsIntegralProjective01 U g) (he : EqOn f g U) :
    IsIntegralProjective01 U f := by
  obtain ⟨hU, A, hA⟩ := h
  refine ⟨hU, A, fun t ht => ?_⟩
  rw [he ht]; exact hA t ht

/-- A point of a dyadic node is `mink` of a point of the Farey node. -/
theorem exists_mink_eq (w : List Bool) {z : ℝ}
    (hz : z ∈ Icc (mink (fareyNode w).lo) (mink (fareyNode w).hi)) :
    ∃ x ∈ Icc (fareyNode w).lo (fareyNode w).hi, mink x = z := by
  have hz01 : z ∈ Icc (0 : ℝ) 1 :=
    ⟨(Mink.mink_mem (fareyNode_lo_mem w)).1.trans hz.1,
      hz.2.trans (Mink.mink_mem (fareyNode_hi_mem w)).2⟩
  rw [← Mink.mink_image] at hz01
  obtain ⟨x, hx, rfl⟩ := hz01
  refine ⟨x, ⟨?_, ?_⟩, rfl⟩
  · exact (Mink.mink_strictMonoOn.le_iff_le (fareyNode_lo_mem w) hx).mp hz.1
  · exact (Mink.mink_strictMonoOn.le_iff_le hx (fareyNode_hi_mem w)).mp hz.2

theorem piece_fwd (f : UI ≃o UI) {p q : ℝ} (hip : IsIntegralProjective01 (Icc p q) (extend f))
    (h1 : FP p q) (h2 : FP (extend f p) (extend f q)) :
    DPiece (extend (cj f)) (mink p) (mink q) := by
  obtain ⟨w, rfl, rfl⟩ := h1
  obtain ⟨w', hp', hq'⟩ := h2
  have he := mob_unique (Mink.isFarey_fareyNode w) (Mink.isFarey_fareyNode w') hip hp'.symm
    hq'.symm
  rw [Mink.mink_lo, Mink.mink_hi]
  refine ⟨(isDyadic_dyadicNode w).1, (isDyadic_dyadicNode w).2, (w.length : ℤ) - w'.length,
    (dyadicNode w').1 - 2 ^ ((w.length : ℤ) - w'.length) * (dyadicNode w).1, ?_⟩
  intro z hz
  rw [← Mink.mink_lo, ← Mink.mink_hi] at hz
  obtain ⟨x, hx, rfl⟩ := exists_mink_eq w hz
  rw [extend_cj f (fareyNode_Icc_subset w hx), he hx, mink_mob w w' hx, width_ratio]
  ring

theorem piece_bwd (f : UI ≃o UI) {p q : ℝ} (h1 : FP p q) (h2 : FP (extend f p) (extend f q))
    (ha : ∃ a c : ℝ, ∀ z ∈ Icc (mink p) (mink q), extend (cj f) z = a * z + c) :
    IsIntegralProjective01 (Icc p q) (extend f) := by
  obtain ⟨w, rfl, rfl⟩ := h1
  obtain ⟨w', hp', hq'⟩ := h2
  obtain ⟨a, c, hac⟩ := ha
  set I := fareyNode w
  set J := fareyNode w'
  have hI := Mink.isFarey_fareyNode w
  have hJ := Mink.isFarey_fareyNode w'
  refine ip_congr (mob_isIP hI hJ) (fun x hx => ?_)
  have hx01 := fareyNode_Icc_subset w hx
  apply mink_injOn (extend_mem f hx01) (fareyNode_Icc_subset w' (mob_bounds hI hJ hx))
  have key : ∀ y ∈ Icc I.lo I.hi, mink (extend f y) = a * mink y + c := by
    intro y hy
    rw [← extend_cj f (fareyNode_Icc_subset w hy)]
    exact hac _ ⟨Mink.mink_strictMonoOn.monotoneOn (fareyNode_lo_mem w)
      (fareyNode_Icc_subset w hy) hy.1, Mink.mink_strictMonoOn.monotoneOn
      (fareyNode_Icc_subset w hy) (fareyNode_hi_mem w) hy.2⟩
  have k1 := key _ (lo_mem hI)
  have k2 := key _ (hi_mem hI)
  rw [hp'.symm, hq'.symm] at *
  rw [← hp', Mink.mink_lo, Mink.mink_lo] at k1
  rw [← hq', Mink.mink_hi, Mink.mink_hi] at k2
  rw [key x hx, mink_mob w w' hx]
  have hw := dyadicNode_width_pos w
  have ha' : a = ((dyadicNode w').2 - (dyadicNode w').1) / ((dyadicNode w).2 - (dyadicNode w).1) := by
    field_simp; linarith
  rw [← ha']
  linarith

theorem fareyMarks_head (t : TTree) : (fareyMarks t).head? = some 0 := by simp [fareyMarks]

theorem fareyMarks_getLast (t : TTree) : (fareyMarks t).getLast? = some 1 := by
  simp only [fareyMarks]; rw [← List.cons_append, List.getLast?_append]; simp

theorem map_extend_fareyMarks (f : UI ≃o UI) (t : TTree) :
    (TTree.marks t).map (extend (cj f)) = ((fareyMarks t).map (extend f)).map mink := by
  rw [← Mink.map_mink_fareyMarks, List.map_map, List.map_map]
  apply List.map_congr_left
  intro x hx
  exact extend_cj f (mem_fareyMarks hx)

/-- Backward transport. -/
theorem transport_bwd {d : TreeDiagram} {f : UI ≃o UI}
    (hA : AffineOnPieces (extend (cj f)) (TTree.marks d.dom))
    (hM : (TTree.marks d.dom).map (extend (cj f)) = TTree.marks d.ran) : RepresentsPIP d f := by
  have hmap : (fareyMarks d.dom).map (extend f) = fareyMarks d.ran := by
    rw [map_extend_fareyMarks, ← Mink.map_mink_fareyMarks] at hM
    refine map_mink_inj _ _ ?_ (fun x hx => mem_fareyMarks hx) hM
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact extend_mem f (mem_fareyMarks hy)
  refine ⟨?_, hmap⟩
  have h3 := chain_fareyMarks d.ran
  rw [← hmap, List.isChain_map] at h3
  unfold AffineOnPieces at hA
  rw [← Mink.map_mink_fareyMarks, List.isChain_map] at hA
  exact (chain_and (chain_and (chain_fareyMarks d.dom) h3) hA).imp
    (fun p q hpq => piece_bwd f hpq.1.1 hpq.1.2 hpq.2)

theorem representsPIP_of_represents {d : TreeDiagram} {f : UI ≃o UI}
    (h : Represents d (cj f)) : RepresentsPIP d f :=
  transport_bwd h.2.1 h.2.2

theorem mem_PIPPlus01Set_of_representsPIP {d : TreeDiagram} {f : UI ≃o UI}
    (h : RepresentsPIP d f) : f ∈ PIPPlus01Set := by
  refine ⟨fareyMarks d.dom, ⟨fareyMarks_head _, fareyMarks_getLast _, ?_⟩, h.1⟩
  exact (chain_fareyMarks d.dom).imp (fun p q ⟨w, hp, hq⟩ => by
    rw [← hp, ← hq]; exact subsimplex_of_farey (Mink.isFarey_fareyNode w))

/-- An integral subsimplex is a Farey node. -/
theorem fp_of_subsimplex {p q : ℝ} (h : IsIntegralSubsimplex01 p q) : FP p q := by
  obtain ⟨K, hK, hp, hq⟩ := exists_farey_of_subsimplex h
  obtain ⟨w, rfl⟩ := exists_fareyNode hK
  exact ⟨w, hp, hq⟩

/-- The image of an integral subsimplex under an integral projective order isomorphism. -/
theorem subsimplex_image (f : UI ≃o UI) {p q : ℝ} (h : IsIntegralSubsimplex01 p q)
    (hip : IsIntegralProjective01 (Icc p q) (extend f)) :
    IsIntegralSubsimplex01 (extend f p) (extend f q) := by
  obtain ⟨K, hK, rfl, rfl⟩ := exists_farey_of_subsimplex h
  obtain ⟨-, A, hA⟩ := hip
  have hv := mob_via root_isFarey hK
  rw [root_Icc] at hv
  refine ⟨extend f ∘ mob root K, ⟨subset_rfl, _, ip_comp hA hv ?_⟩, ?_⟩
  · intro t ht
    rw [← root_Icc] at ht
    exact mob_bounds root_isFarey hK ht
  · rw [Set.image_comp, ← root_Icc, mob_image root_isFarey hK, OrderIso.image_Icc]

theorem mem_F_of_mem_PIPPlus01Set {f : UI ≃o UI} (hf : f ∈ PIPPlus01Set) : cj f ∈ F := by
  obtain ⟨xs, ⟨h0, h1, hsub⟩, hip⟩ := hf
  apply mem_F_of_isThompson
  refine isThompson_of_chain _ (xs.map mink) (by rw [List.head?_map, h0]; simp [Mink.mink_zero])
    (by rw [List.getLast?_map, h1]; simp [Mink.mink_one]) ?_
  rw [List.isChain_map]
  exact (chain_and hsub hip).imp (fun p q hpq =>
    piece_fwd f hpq.2 (fp_of_subsimplex hpq.1) (fp_of_subsimplex (subsimplex_image f hpq.1 hpq.2)))

theorem mem_PIPPlus01Set_iff (f : UI ≃o UI) : f ∈ PIPPlus01Set ↔ cj f ∈ F := by
  refine ⟨mem_F_of_mem_PIPPlus01Set, fun h => ?_⟩
  obtain ⟨d, -, hd⟩ := exists_isReduced_represents h
  exact mem_PIPPlus01Set_of_representsPIP (representsPIP_of_represents hd)

end CannonFloydParry.S7
end

section
/-!
# The circle: conjugation by Minkowski's `?` and the direction `PIP⁺(S¹) → T`
-/

namespace CannonFloydParry.S7

open Set

/-! ### Dyadic arithmetic -/

theorem isDyadic_add {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x + y) := by
  obtain ⟨m, k, rfl⟩ := hx
  obtain ⟨m', k', rfl⟩ := hy
  refine ⟨m * 2 ^ k' + m' * 2 ^ k, k + k', ?_⟩
  push_cast; field_simp; ring

theorem isDyadic_neg {x : ℝ} (hx : IsDyadic x) : IsDyadic (-x) := by
  obtain ⟨m, k, rfl⟩ := hx
  exact ⟨-m, k, by push_cast; ring⟩

theorem isDyadic_sub {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x - y) := by
  rw [sub_eq_add_neg]; exact isDyadic_add hx (isDyadic_neg hy)

theorem isDyadic_intCast (k : ℤ) : IsDyadic (k : ℝ) := ⟨k, 0, by simp⟩

/-! ### Maps of the circle induced by maps of the line commuting with `+1` -/

theorem orderIso_symm_add_one (L : ℝ ≃o ℝ) (hL : ∀ x, L (x + 1) = L x + 1) (y : ℝ) :
    L.symm (y + 1) = L.symm y + 1 := by
  apply L.injective
  rw [hL, OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]

theorem coe_add_int (x : ℝ) (k : ℤ) : ((x + k : ℝ) : UnitAddCircle) = (x : UnitAddCircle) := by
  simp

theorem periodic_coe (L : ℝ ≃o ℝ) (hL : ∀ x, L (x + 1) = L x + 1) :
    Function.Periodic (fun x => ((L x : ℝ) : UnitAddCircle)) 1 := by
  intro x
  simp only [hL]
  simpa using coe_add_int (L x) 1

/-- The map of the circle covered by `L`. -/
noncomputable def circFun (L : ℝ ≃o ℝ) (hL : ∀ x, L (x + 1) = L x + 1) :
    UnitAddCircle → UnitAddCircle :=
  (periodic_coe L hL).lift

theorem circFun_coe (L : ℝ ≃o ℝ) (hL : ∀ x, L (x + 1) = L x + 1) (x : ℝ) :
    circFun L hL (x : UnitAddCircle) = ((L x : ℝ) : UnitAddCircle) :=
  (periodic_coe L hL).lift_coe x

/-- The permutation of the circle covered by `L`. -/
noncomputable def circPerm (L : ℝ ≃o ℝ) (hL : ∀ x, L (x + 1) = L x + 1) :
    Equiv.Perm UnitAddCircle where
  toFun := circFun L hL
  invFun := circFun L.symm (orderIso_symm_add_one L hL)
  left_inv p := by
    induction p using QuotientAddGroup.induction_on with
    | H z =>
      show circFun L.symm (orderIso_symm_add_one L hL) (circFun L hL (z : UnitAddCircle)) = z
      rw [circFun_coe, circFun_coe, OrderIso.symm_apply_apply]
  right_inv p := by
    induction p using QuotientAddGroup.induction_on with
    | H z =>
      show circFun L hL (circFun L.symm (orderIso_symm_add_one L hL) (z : UnitAddCircle)) = z
      rw [circFun_coe, circFun_coe, OrderIso.apply_symm_apply]

theorem circPerm_coe (L : ℝ ≃o ℝ) (hL : ∀ x, L (x + 1) = L x + 1) (x : ℝ) :
    circPerm L hL (x : UnitAddCircle) = ((L x : ℝ) : UnitAddCircle) := circFun_coe L hL x

theorem circPerm_symm_coe (L : ℝ ≃o ℝ) (hL : ∀ x, L (x + 1) = L x + 1) (x : ℝ) :
    (circPerm L hL).symm (x : UnitAddCircle) = ((L.symm x : ℝ) : UnitAddCircle) :=
  circFun_coe L.symm (orderIso_symm_add_one L hL) x

/-- Minkowski's `?` on the circle. -/
noncomputable def mu : Equiv.Perm UnitAddCircle := circPerm minkR Mink.minkR_add_one

theorem mu_coe (x : ℝ) : mu (x : UnitAddCircle) = ((minkR x : ℝ) : UnitAddCircle) :=
  circPerm_coe _ _ x

theorem mu_inv_coe (x : ℝ) : mu⁻¹ (x : UnitAddCircle) = ((minkR.symm x : ℝ) : UnitAddCircle) :=
  circPerm_symm_coe _ _ x

/-! ### Generalized pieces -/

/-! ### `PIP⁺(S¹) → T` -/

end CannonFloydParry.S7
end

section
/-!
# The circle: the direction `T → PIP⁺(S¹)`, by refining to a uniform dyadic grid
-/

namespace CannonFloydParry.S7

open Set

/-! ### Levels of dyadic numbers -/

/-- `x` is a multiple of `2⁻ᴺ`. -/
def Lev (N : ℕ) (x : ℝ) : Prop := ∃ m : ℤ, x = m / 2 ^ N

theorem Lev.mono {N N' : ℕ} {x : ℝ} (h : Lev N x) (hN : N ≤ N') : Lev N' x := by
  obtain ⟨m, rfl⟩ := h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
  refine ⟨m * 2 ^ d, ?_⟩
  push_cast
  rw [pow_add]
  field_simp

theorem exists_lev_finset (B : Finset ℝ) (hB : ∀ b ∈ B, IsDyadic b) :
    ∃ N, ∀ b ∈ B, Lev N b := by
  classical
  induction B using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a B _ ih =>
    obtain ⟨N, hN⟩ := ih (fun b hb => hB b (Finset.mem_insert_of_mem hb))
    obtain ⟨m, k, hk⟩ := hB a (Finset.mem_insert_self a B)
    refine ⟨max N k, fun b hb => ?_⟩
    rcases Finset.mem_insert.mp hb with h | h
    · subst h; exact Lev.mono ⟨m, hk⟩ (le_max_right _ _)
    · exact (hN b h).mono (le_max_left _ _)

theorem not_lev_between {N : ℕ} {t : ℝ} (ht : Lev N t) (j : ℕ) (h1 : (j : ℝ) / 2 ^ N < t)
    (h2 : t < ((j : ℝ) + 1) / 2 ^ N) : False := by
  obtain ⟨m, rfl⟩ := ht
  have hp : (0 : ℝ) < 2 ^ N := by positivity
  rw [div_lt_div_iff_of_pos_right hp] at h1 h2
  have a1 : (j : ℤ) < m := by exact_mod_cast h1
  have a2 : m < (j : ℤ) + 1 := by exact_mod_cast h2
  omega

/-- The standard dyadic intervals of depth `N` are the dyadic nodes of depth `N`. -/
theorem dyadic_grid : ∀ (N j : ℕ), j < 2 ^ N →
    ∃ w : List Bool, w.length = N ∧ dyadicNode w = ((j : ℝ) / 2 ^ N, ((j : ℝ) + 1) / 2 ^ N)
  | 0, j, hj => by
    have : j = 0 := by simpa using hj
    subst this
    exact ⟨[], rfl, by simp [Mink.dyadicNode_nil]⟩
  | N + 1, j, hj => by
    obtain ⟨j', hj'⟩ := Nat.even_or_odd' j
    have hlt : j' < 2 ^ N := by rw [pow_succ] at hj; omega
    obtain ⟨w, hw, hd⟩ := dyadic_grid N j' hlt
    rcases hj' with rfl | rfl
    · refine ⟨w ++ [false], by simp [hw], ?_⟩
      rw [Mink.dyadicNode_append_false, hd]
      simp only [Prod.mk.injEq]
      push_cast
      constructor <;> · rw [pow_succ]; field_simp <;> ring
    · refine ⟨w ++ [true], by simp [hw], ?_⟩
      rw [Mink.dyadicNode_append_true, hd]
      simp only [Prod.mk.injEq]
      push_cast
      constructor <;> · rw [pow_succ]; field_simp <;> ring

/-! ### The affine pieces on a fine grid -/

/-- On the `j`-th interval of depth `N0`, `L` is `2ⁿ z + c` with `n ≤ N` and `c ∈ 2^{n-N} ℤ`. -/
def GoodPiece (L : ℝ → ℝ) (N0 N j : ℕ) : Prop :=
  N0 ≤ N ∧ ∃ (n : ℤ) (c : ℝ) (m : ℤ), n ≤ N ∧ c * 2 ^ ((N : ℤ) - n) = m ∧
    ∀ z ∈ Icc ((j : ℝ) / 2 ^ N0) (((j : ℝ) + 1) / 2 ^ N0), L z = 2 ^ n * z + c

theorem GoodPiece.mono {L : ℝ → ℝ} {N0 N N' j : ℕ} (hNN : N ≤ N') (h : GoodPiece L N0 N j) :
    GoodPiece L N0 N' j := by
  obtain ⟨h0, n, c, m, hn, hc, hz⟩ := h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNN
  refine ⟨h0.trans hNN, n, c, m * 2 ^ d, by push_cast; omega, ?_, hz⟩
  rw [show ((N + d : ℕ) : ℤ) - n = ((N : ℤ) - n) + (d : ℤ) by push_cast; ring,
    zpow_add₀ (by norm_num), ← mul_assoc, hc, zpow_natCast]
  push_cast; ring

/-! ### Pieces, backwards -/

theorem minkR_symm_dyadicNode (w : List Bool) : minkR.symm (dyadicNode w).1 = (fareyNode w).lo := by
  rw [OrderIso.symm_apply_eq, Mink.minkR_eq_mink (fareyNode_lo_mem w), Mink.mink_lo]

theorem minkR_symm_dyadicNode_hi (w : List Bool) :
    minkR.symm (dyadicNode w).2 = (fareyNode w).hi := by
  rw [OrderIso.symm_apply_eq, Mink.minkR_eq_mink (fareyNode_hi_mem w), Mink.mink_hi]

/-! ### `T → PIP⁺(S¹)` -/

end CannonFloydParry.S7
end

section
/-!
# `Δ₁` versus `[0,1]` (CFP p. 251): coordinates, matrices, integral subsimplices
-/

namespace CannonFloydParry.S7

open Set

/-! ### The parametrization `t ↦ (t, 1 - t)` -/

/-- The point `(t, 1 - t)`. -/
def e1 (t : ℝ) : Fin 2 → ℝ := ![t, 1 - t]

@[simp] theorem e1_zero_apply (t : ℝ) : e1 t 0 = t := rfl
@[simp] theorem e1_one_apply (t : ℝ) : e1 t 1 = 1 - t := rfl

theorem simplex_sum {x : Fin 2 → ℝ} (hx : x ∈ Simplex 1) : x 0 + x 1 = 1 := by
  have := hx.2; simpa [Fin.sum_univ_two] using this

theorem simplex_eq {x : Fin 2 → ℝ} (hx : x ∈ Simplex 1) : x = e1 (x 0) := by
  funext i
  fin_cases i
  · rfl
  · show x 1 = 1 - x 0; linarith [simplex_sum hx]

theorem simplex_mem0 {x : Fin 2 → ℝ} (hx : x ∈ Simplex 1) : x 0 ∈ Icc (0 : ℝ) 1 :=
  ⟨hx.1 0, by linarith [hx.1 1, simplex_sum hx]⟩

/-! ### `Δ₁ ≅ [0,1]` as spaces, and the induced homomorphism -/

/-- The first coordinate. -/
def piS (x : Simplex 1) : UI := ⟨x.1 0, simplex_mem0 x.2⟩

/-- `toSimplexOne` as a homeomorphism. -/
noncomputable def eS : UI ≃ₜ Simplex 1 where
  toFun := toSimplexOne
  invFun := piS
  left_inv t := Subtype.ext rfl
  right_inv x := Subtype.ext (simplex_eq x.2).symm
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_subtype_val
    · exact continuous_const.sub continuous_subtype_val
  continuous_invFun := ((continuous_apply 0).comp continuous_subtype_val).subtype_mk _

/-! ### The change of coordinates `(x₀, x₁) ↦ (x₀, x₀ + x₁)` -/

/-! ### The pointwise dictionary -/

/-! ### Orientation -/

theorem det_one_of_lt {A : GL (Fin 2) ℤ} {U : Set ℝ} {F : ℝ → ℝ}
    (h : IsIntegralProjective01Via A U F) {u v : ℝ} (hu : u ∈ U) (hv : v ∈ U) (huv : u < v)
    (hF : F u < F v) : (A : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  have yu := denom_pos h hu
  have yv := denom_pos h hv
  have fu := (h u hu).2.2
  have fv := (h v hv).2.2
  rw [glAct_t0, glAct_t1] at fu fv
  rw [glAct_t1] at yu yv
  rw [Matrix.det_fin_two]
  set M := (A : Matrix (Fin 2) (Fin 2) ℤ)
  rcases det_GL A with hd | hd
  · exact hd
  · exfalso
    rw [fu, fv, div_lt_div_iff₀ yu yv] at hF
    have hdR : ((M 0 0 : ℝ) * M 1 1 - M 0 1 * M 1 0) = -1 := by exact_mod_cast hd
    nlinarith

end CannonFloydParry.S7
end

section
/-!
# `Δ₁` versus `[0,1]`: integral subsimplices, and the subdivision of `Δ₁` cut out by a
partition of `[0,1]`
-/

namespace CannonFloydParry.S7

open Set

/-! ### Integral subsimplices -/

/-! ### Pieces of a finite set of breakpoints -/

end CannonFloydParry.S7
end

section
/-!
# `PIP⁺(Δ₁) ≅ PIP⁺([0,1])` and Theorem 7.2 `F ≅ PIP⁺(Δ₁)`
-/

namespace CannonFloydParry.S7

open Set

/-! ### Lists -/

theorem chain_forall {R : ℝ → ℝ → Prop} {P : ℝ → Prop} (hR : ∀ u v, R u v → P u ∧ P v) :
    ∀ (l : List ℝ) (a b : ℝ), (a :: b :: l).IsChain R → ∀ x ∈ a :: b :: l, P x
  | [], a, b, h, x, hx => by
    rw [List.isChain_cons_cons] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact (hR _ _ h.1).1
    · exact (hR _ _ h.1).2
  | c :: l, a, b, h, x, hx => by
    rw [List.isChain_cons_cons] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (hR _ _ h.1).1
    · exact chain_forall hR l b c h.2 x hx

/-! ### From `PIP⁺([0,1])` to `PIP⁺(Δ₁)` -/

/-! ### From `PIP⁺(Δ₁)` to `PIP⁺([0,1])` -/

/-! ### The targets -/


end CannonFloydParry.S7
end

section
/-!
# `PIP⁺([0,1])` as the order isomorphisms of `[0,1]` that are locally Möbius off finitely many
rationals
-/

namespace Monod.Dev.Thur

open OnePoint Filter Topology Set CannonFloydParry CannonFloydParry.S7

/-! ### From a PIP partition to local Möbius data -/

lemma rat_of_FP {p q : ℝ} (h : FP p q) : (∃ r : ℚ, p = r) ∧ ∃ r : ℚ, q = r := by
  obtain ⟨w, rfl, rfl⟩ := h
  exact ⟨⟨((fareyNode w).a : ℚ) / (fareyNode w).b, by simp [FracInterval.lo]⟩,
    ⟨((fareyNode w).c : ℚ) / (fareyNode w).d, by simp [FracInterval.hi]⟩⟩

lemma glAct_eq_nR (M : SL2Z) (t : ℝ) :
    glAct (Matrix.SpecialLinearGroup.toGL M) ![t, 1] 0 = nR M t := by
  rw [glAct_t0]; simp [nR]

lemma glAct_eq_dR (M : SL2Z) (t : ℝ) :
    glAct (Matrix.SpecialLinearGroup.toGL M) ![t, 1] 1 = dR M t := by
  rw [glAct_t1]; simp [dR]

lemma LM_of_mem_PIPPlus01Set {f : UI ≃o UI} (hf : f ∈ PIPPlus01Set) :
    LM (Ioo 0 1) (extend f) := by
  obtain ⟨xs, ⟨h0, h1, hsub⟩, hip⟩ := hf
  obtain ⟨l, rfl⟩ : ∃ l, xs = 0 :: l := by
    cases xs with
    | nil => simp at h0
    | cons a l => simp at h0; exact ⟨l, by rw [h0]⟩
  refine ⟨{x | x ∈ (0 : ℝ) :: l}, (0 :: l).finite_toSet, ?_, ?_⟩
  · intro r hr
    obtain ⟨b, l', rfl⟩ : ∃ b l', l = b :: l' := by
      cases l with
      | nil => simp at h1
      | cons b l' => exact ⟨b, l', rfl⟩
    exact chain_forall (P := fun x => ∃ q : ℚ, x = q) (fun u v h => rat_of_FP (fp_of_subsimplex h))
      l' 0 b hsub r hr
  · intro x hx hxR
    obtain ⟨u, v, hu, hv, ⟨-, hIP⟩, hux, hxv⟩ :=
      chain_cover l 0 1 x (chain_and hsub hip) h1 zero_lt_one hx.1.le hx.2.le
    have hux' : u < x := lt_of_le_of_ne hux (fun e => hxR (e ▸ hu))
    have hxv' : x < v := lt_of_le_of_ne hxv (fun e => hxR (e ▸ hv))
    obtain ⟨-, A, hA⟩ := hIP
    have huv : u < v := hux'.trans hxv'
    have hdet := det_one_of_lt hA ⟨le_rfl, huv.le⟩ ⟨huv.le, le_rfl⟩ huv
      ((extend f).strictMono huv)
    let M : SL2Z := ⟨A, hdet⟩
    have hAM : Matrix.SpecialLinearGroup.toGL M = A := by ext i j; rfl
    refine ⟨M, ?_, ?_⟩
    · rw [← glAct_eq_dR, hAM]; exact (denom_pos hA ⟨hux, hxv⟩).ne'
    · filter_upwards [Icc_mem_nhds hux' hxv'] with y hy
      rw [(hA y hy).2.2, ← hAM, glAct_eq_nR, glAct_eq_dR]; rfl

/-! ### Rational points have dyadic `?` -/

lemma isDyadic_mink_rat (q : ℚ) (hq : (q : ℝ) ∈ Icc (0 : ℝ) 1) : IsDyadic (mink q) := by
  rcases eq_or_lt_of_le hq.2 with h1 | h1
  · rw [h1, Mink.mink_one]; exact ⟨1, 0, by simp⟩
  rcases eq_or_lt_of_le hq.1 with h0 | h0
  · rw [← h0, Mink.mink_zero]; exact ⟨0, 0, by simp⟩
  have hnum : 0 < q.num := by
    have : (0 : ℚ) < q := by exact_mod_cast h0
    exact Rat.num_pos.mpr this
  set a : ℤ := q.num
  set b : ℤ := (q.den : ℤ)
  have hb : 0 < b := by simp [b, q.den_pos]
  have hqab : (q : ℝ) = (a : ℝ) / b := by
    rw [← Rat.num_div_den q]; push_cast; rfl
  have hab : a < b := by
    have : (a : ℝ) / b < 1 := hqab ▸ h1
    rw [div_lt_one (by exact_mod_cast hb)] at this
    exact_mod_cast this
  have hgcd : Int.gcd a b = 1 := by
    have := q.reduced
    simpa [a, b, Int.gcd] using this
  have hbez := Int.gcd_eq_gcd_ab a b
  rw [hgcd] at hbez
  set u := Int.gcdA a b
  set v := Int.gcdB a b
  set k : ℤ := |u| + |v| + 1
  have hk : 0 < k := by positivity
  set c : ℤ := v + a * k
  set d : ℤ := -u + b * k
  have hc : 0 < c := by
    have : k ≤ a * k := le_mul_of_one_le_left hk.le hnum
    have := neg_abs_le v; have := abs_nonneg u
    omega
  have hcd : c ≤ d := by
    have : k ≤ (b - a) * k := le_mul_of_one_le_left hk.le (by omega)
    have := le_abs_self v; have := le_abs_self u
    have e : d - c = -u - v + (b - a) * k := by ring
    omega
  have hdet : a * d - b * c = -1 := by
    push_cast at hbez
    simp only [c, d]; linear_combination hbez
  let K : FracInterval := ⟨a.toNat, b.toNat, c.toNat, d.toNat⟩
  have ha' : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg hnum.le
  have hb' : ((b.toNat : ℕ) : ℤ) = b := Int.toNat_of_nonneg hb.le
  have hc' : ((c.toNat : ℕ) : ℤ) = c := Int.toNat_of_nonneg hc.le
  have hd' : ((d.toNat : ℕ) : ℤ) = d := Int.toNat_of_nonneg (by omega)
  have hK : K.IsFarey := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [K]
    · omega
    · omega
    · omega
    · omega
    · omega
    · rw [ha', hb', hc', hd']; exact hdet
  obtain ⟨w, hw⟩ := exists_fareyNode hK
  have hlo : (fareyNode w).lo = q := by
    rw [hw, hqab, FracInterval.lo]
    simp only [K]
    congr 1
    exact_mod_cast ha'
  rw [← hlo, Mink.mink_lo]
  exact (isDyadic_dyadicNode w).1

/-! ### From local Möbius data to a PIP partition -/

lemma same_sign {g : ℝ → ℝ} (hg : Continuous g) {p q : ℝ}
    (hne : ∀ t ∈ Icc p q, g t ≠ 0) (hp : 0 < g p) : ∀ t ∈ Icc p q, 0 < g t := by
  intro t ht
  by_contra hneg
  rw [not_lt] at hneg
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' ht.1 hg.continuousOn ⟨hneg, hp.le⟩
  exact hne s ⟨hs.1, hs.2.trans ht.2⟩ hs0

lemma ip_of_local {g : ℝ → ℝ} (hgc : Continuous g) {p q : ℝ} (hpq : p < q)
    (hsub : Icc p q ⊆ Icc 0 1) (hmem : ∀ t ∈ Icc p q, g t ∈ Icc (0 : ℝ) 1)
    (hloc : ∀ x ∈ Ioo p q, ∃ M : SL2Z, dR M x ≠ 0 ∧ ∀ᶠ y in 𝓝 x, g y = mR M y) :
    IsIntegralProjective01 (Icc p q) g := by
  obtain ⟨M, hM⟩ := single_of_local isPreconnected_Ioo
    (x₀ := (p + q) / 2) ⟨by linarith, by linarith⟩ hloc
  have hp : dR M p ≠ 0 ∧ g p = mR M p := by
    have := left_nhdsWithin_Ioo_neBot hpq
    exact endpoint_of_within hM hgc.continuousWithinAt
  have hq : dR M q ≠ 0 ∧ g q = mR M q := by
    have := right_nhdsWithin_Ioo_neBot hpq
    exact endpoint_of_within hM hgc.continuousWithinAt
  have hall : ∀ t ∈ Icc p q, dR M t ≠ 0 ∧ g t = mR M t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]; exact hp
    rcases eq_or_lt_of_le ht.2 with h' | h'
    · rw [h']; exact hq
    exact hM t ⟨h, h'⟩
  obtain ⟨M', hPM, hpos⟩ : ∃ M' : SL2Z, PM M M' ∧ 0 < dR M' p := by
    rcases lt_or_gt_of_ne hp.1 with h | h
    · refine ⟨-M, ⟨-1, Or.inr rfl, fun i j => by simp⟩, ?_⟩
      simp only [dR] at h ⊢; simp; linarith
    · exact ⟨M, ⟨1, Or.inl rfl, fun i j => by simp⟩, h⟩
  have hall' : ∀ t ∈ Icc p q, 0 < dR M' t ∧ g t = mR M' t := by
    have hne : ∀ t ∈ Icc p q, dR M' t ≠ 0 := fun t ht => hPM.dR_ne (hall t ht).1
    intro t ht
    exact ⟨same_sign (continuous_dR M') hne hpos t ht, by rw [hPM.mR_eq]; exact (hall t ht).2⟩
  refine ⟨hsub, Matrix.SpecialLinearGroup.toGL M', fun t ht => ?_⟩
  obtain ⟨hd, he⟩ := hall' t ht
  rw [glAct_eq_nR, glAct_eq_dR]
  have hn : nR M' t = g t * dR M' t := by rw [he, mR, div_mul_cancel₀ _ hd.ne']
  obtain ⟨hm0, hm1⟩ := hmem t ht
  refine ⟨?_, ?_, ?_⟩
  · rw [hn]; positivity
  · rw [hn]; nlinarith
  · rw [he]; rfl

lemma minkR_symm_zero : minkR.symm 0 = 0 := by
  rw [OrderIso.symm_apply_eq, Mink.minkR_eq_mink ⟨le_rfl, zero_le_one⟩, Mink.mink_zero]

lemma minkR_symm_one : minkR.symm 1 = 1 := by
  rw [OrderIso.symm_apply_eq, Mink.minkR_eq_mink ⟨zero_le_one, le_rfl⟩, Mink.mink_one]

theorem mem_PIPPlus01Set_of_LM {f : UI ≃o UI} (hf : LM (Ioo 0 1) (extend f)) :
    f ∈ PIPPlus01Set := by
  classical
  obtain ⟨R, hRf, hRq, hloc⟩ := hf
  have hSf : (R ∩ Icc 0 1).Finite := hRf.inter_of_left _
  set B : Finset ℝ := hSf.toFinset.image mink
  have hB : ∀ b ∈ B, IsDyadic b := by
    intro b hb
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hb
    rw [Set.Finite.mem_toFinset] at hr
    obtain ⟨q, rfl⟩ := hRq r hr.1
    exact isDyadic_mink_rat q hr.2
  obtain ⟨N, hN⟩ := exists_lev_finset B hB
  set xs := (List.range (2 ^ N + 1)).map (fun j : ℕ => minkR.symm ((j : ℝ) / 2 ^ N))
  have hchain : xs.IsChain (fun a b => IsIntegralSubsimplex01 a b ∧
      IsIntegralProjective01 (Icc a b) (extend f)) := by
    rw [List.isChain_map]
    refine (List.isChain_range_succ _ _).2 (fun j hj => ?_)
    obtain ⟨w, -, hw⟩ := dyadic_grid N j hj
    have hlo : minkR.symm ((j : ℝ) / 2 ^ N) = (fareyNode w).lo := by
      rw [← minkR_symm_dyadicNode, hw]
    have hhi : minkR.symm (((j.succ : ℕ) : ℝ) / 2 ^ N) = (fareyNode w).hi := by
      rw [← minkR_symm_dyadicNode_hi, hw, Nat.cast_succ]
    rw [hlo, hhi]
    have hI := Mink.isFarey_fareyNode w
    refine ⟨subsimplex_of_farey hI, ?_⟩
    refine ip_of_local (extend f).continuous (IsFarey.lo_lt_hi hI) (fareyNode_Icc_subset w)
      (fun t ht => extend_mem f (fareyNode_Icc_subset w ht)) (fun x hx => ?_)
    have hx01 : x ∈ Icc (0 : ℝ) 1 := fareyNode_Icc_subset w (Ioo_subset_Icc_self hx)
    have hxR : x ∉ R := by
      intro hxR
      have hmem : mink x ∈ B :=
        Finset.mem_image.mpr ⟨x, (Set.Finite.mem_toFinset _).2 ⟨hxR, hx01⟩, rfl⟩
      have h1 : mink (fareyNode w).lo < mink x :=
        Mink.mink_strictMonoOn (fareyNode_lo_mem w) hx01 hx.1
      have h2 : mink x < mink (fareyNode w).hi :=
        Mink.mink_strictMonoOn hx01 (fareyNode_hi_mem w) hx.2
      rw [Mink.mink_lo, hw] at h1
      rw [Mink.mink_hi, hw] at h2
      exact not_lev_between (hN _ hmem) j h1 h2
    refine hloc x ⟨?_, ?_⟩ hxR
    · exact lt_of_le_of_lt (fareyNode_lo_mem w).1 hx.1
    · exact lt_of_lt_of_le hx.2 (fareyNode_hi_mem w).2
  refine ⟨xs, ⟨?_, ?_, hchain.imp fun a b h => h.1⟩, hchain.imp fun a b h => h.2⟩
  · simp [xs, List.range_succ_eq_map, minkR_symm_zero]
  · rw [List.getLast?_map, List.getLast?_range]
    simp [minkR_symm_one]

end Monod.Dev.Thur
end

section
/-!
# Order isomorphisms of `ℝ` versus order isomorphisms of `[0,1]`, through `τ`
-/

namespace Monod.Dev.Thur

open OnePoint Filter Topology Set CannonFloydParry CannonFloydParry.S7

/-! ### Endpoints -/

lemma orderIso_zero (f : UI ≃o UI) : f ⟨0, zero_mem_UI⟩ = ⟨0, zero_mem_UI⟩ := by
  apply le_antisymm
  · obtain ⟨z, hz⟩ := f.surjective ⟨0, zero_mem_UI⟩
    have := f.monotone (show (⟨0, zero_mem_UI⟩ : UI) ≤ z from Subtype.coe_le_coe.mp z.2.1)
    rwa [hz] at this
  · exact Subtype.coe_le_coe.mp (f ⟨0, zero_mem_UI⟩).2.1

lemma extend_zero (f : UI ≃o UI) : extend f 0 = 0 := by
  rw [show (0 : ℝ) = ((⟨0, zero_mem_UI⟩ : UI) : ℝ) from rfl, extend_coe, orderIso_zero]

lemma extend_one (f : UI ≃o UI) : extend f 1 = 1 := by
  rw [show (1 : ℝ) = ((⟨1, one_mem_UI⟩ : UI) : ℝ) from rfl, extend_coe, orderIso_one]

lemma extend_mem_Ioo (f : UI ≃o UI) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    extend f t ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · have := (extend f).strictMono ht.1; rwa [extend_zero] at this
  · have := (extend f).strictMono ht.2; rwa [extend_one] at this

lemma extend_symm (f : UI ≃o UI) : (extend f).symm = extend f.symm := rfl

/-! ### From `ℝ` to `[0,1]` -/

noncomputable def phiFun (u : ℝ ≃o ℝ) (t : ℝ) : ℝ := if 0 < t ∧ t < 1 then τi (u (τ t)) else t

lemma phiFun_of_mem (u : ℝ ≃o ℝ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : phiFun u t = τi (u (τ t)) :=
  if_pos ht

lemma phiFun_of_not_mem (u : ℝ ≃o ℝ) {t : ℝ} (ht : t ∉ Ioo (0 : ℝ) 1) : phiFun u t = t :=
  if_neg ht

lemma phiFun_strictMono (u : ℝ ≃o ℝ) : StrictMono (phiFun u) := by
  intro s t hst
  by_cases hs : s ∈ Ioo (0 : ℝ) 1 <;> by_cases ht : t ∈ Ioo (0 : ℝ) 1
  · rw [phiFun_of_mem u hs, phiFun_of_mem u ht]
    exact τi_strictMono (u.strictMono (τ_strictMonoOn hs ht hst))
  · rw [phiFun_of_mem u hs, phiFun_of_not_mem u ht]
    have : 1 ≤ t := by
      by_contra h; exact ht ⟨hs.1.trans hst, lt_of_not_ge h⟩
    exact (τi_mem _).2.trans_le this
  · rw [phiFun_of_not_mem u hs, phiFun_of_mem u ht]
    have : s ≤ 0 := by
      by_contra h; exact hs ⟨lt_of_not_ge h, hst.trans ht.2⟩
    exact this.trans_lt (τi_mem _).1
  · rw [phiFun_of_not_mem u hs, phiFun_of_not_mem u ht]; exact hst

lemma phiFun_surjective (u : ℝ ≃o ℝ) : Function.Surjective (phiFun u) := by
  intro y
  by_cases hy : y ∈ Ioo (0 : ℝ) 1
  · refine ⟨τi (u.symm (τ y)), ?_⟩
    rw [phiFun_of_mem u (τi_mem _), τ_τi, OrderIso.apply_symm_apply, τi_τ hy]
  · exact ⟨y, phiFun_of_not_mem u hy⟩

noncomputable def phiIso (u : ℝ ≃o ℝ) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (phiFun u) (phiFun_strictMono u) (phiFun_surjective u)

/-- `τ⁻¹ ∘ u ∘ τ` as an order isomorphism of `[0,1]`. -/
noncomputable def fU (u : ℝ ≃o ℝ) : UI ≃o UI :=
  restrict (phiIso u) (fun x hx => phiFun_of_not_mem u (fun h => by linarith [h.1]))
    (fun x hx => phiFun_of_not_mem u (fun h => by linarith [h.2]))

lemma extend_fU (u : ℝ ≃o ℝ) (t : ℝ) : extend (fU u) t = phiFun u t := by
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · rw [extend_apply, extendFun_of_mem _ ht]; rfl
  · rw [extend_apply, extendFun_of_notMem _ ht, phiFun_of_not_mem u (fun h => ht (Ioo_subset_Icc_self h))]

lemma extend_fU_of_mem (u : ℝ ≃o ℝ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    extend (fU u) t = τi (u (τ t)) := by
  rw [extend_fU, phiFun_of_mem u ht]

/-! ### From `[0,1]` to `ℝ` -/

lemma uFun_strictMono (f : UI ≃o UI) : StrictMono (fun x => τ (extend f (τi x))) := by
  intro x y hxy
  exact τ_strictMonoOn (extend_mem_Ioo f (τi_mem x)) (extend_mem_Ioo f (τi_mem y))
    ((extend f).strictMono (τi_strictMono hxy))

lemma uFun_surjective (f : UI ≃o UI) : Function.Surjective (fun x => τ (extend f (τi x))) := by
  intro y
  refine ⟨τ ((extend f).symm (τi y)), ?_⟩
  have hm : (extend f).symm (τi y) ∈ Ioo (0 : ℝ) 1 := by
    rw [extend_symm]; exact extend_mem_Ioo _ (τi_mem y)
  simp only
  rw [τi_τ hm, OrderIso.apply_symm_apply, τ_τi]

/-- `τ ∘ f ∘ τ⁻¹` as an order isomorphism of `ℝ`. -/
noncomputable def uF (f : UI ≃o UI) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective _ (uFun_strictMono f) (uFun_surjective f)

lemma uF_apply (f : UI ≃o UI) (x : ℝ) : uF f x = τ (extend f (τi x)) := rfl

lemma fU_uF (f : UI ≃o UI) : fU (uF f) = f := by
  ext t
  rw [← extend_coe, ← extend_coe]
  by_cases ht : (t : ℝ) ∈ Ioo (0 : ℝ) 1
  · rw [extend_fU_of_mem _ ht, uF_apply, τi_τ ht, τi_τ (extend_mem_Ioo f ht)]
  · rw [extend_fU, phiFun_of_not_mem _ ht]
    have : (t : ℝ) = 0 ∨ (t : ℝ) = 1 := by
      rcases eq_or_lt_of_le t.2.1 with h | h
      · exact Or.inl h.symm
      rcases eq_or_lt_of_le t.2.2 with h' | h'
      · exact Or.inr h'
      exact absurd ⟨h, h'⟩ ht
    rcases this with h | h <;> rw [h]
    · rw [extend_zero]
    · rw [extend_one]

/-! ### Local Möbius data -/

lemma mem_PIPPlus01Set_fU {u : ℝ ≃o ℝ} (hu : LM univ u) : fU u ∈ PIPPlus01Set := by
  apply mem_PIPPlus01Set_of_LM
  have h1 : LM (Ioo 0 1) (u ∘ τ) :=
    LM.comp isOpen_Ioo LM_τ hu continuousOn_τ (mapsTo_univ _ _) τ_injOn
  have h2 : LM (Ioo 0 1) (τi ∘ (u ∘ τ)) :=
    LM.comp isOpen_Ioo h1 LM_τi (u.continuous.comp_continuousOn continuousOn_τ)
      (mapsTo_univ _ _) (u.injective.comp_injOn τ_injOn)
  refine h2.congr isOpen_Ioo (fun t ht => ?_)
  rw [extend_fU_of_mem u ht]; rfl

lemma LM_uF {f : UI ≃o UI} (hf : f ∈ PIPPlus01Set) : LM univ (uF f) := by
  have h1 : LM univ (extend f ∘ τi) :=
    LM.comp isOpen_univ LM_τi (LM_of_mem_PIPPlus01Set hf) continuous_τi.continuousOn
      (fun x _ => τi_mem x) τi_strictMono.injective.injOn
  have h2 : LM univ (τ ∘ (extend f ∘ τi)) :=
    LM.comp isOpen_univ h1 LM_τ ((extend f).continuous.comp continuous_τi).continuousOn
      (fun x _ => extend_mem_Ioo f (τi_mem x))
      ((extend f).injective.comp τi_strictMono.injective).injOn
  exact h2

/-! ### Homeomorphisms of `P¹` fixing `∞` -/

/-- The homeomorphism of `P¹` extending `u` by `∞ ↦ ∞`. -/
noncomputable def hbar (u : ℝ ≃o ℝ) : OnePoint ℝ ≃ₜ OnePoint ℝ := u.toHomeomorph.onePointCongr

@[simp] lemma hbar_coe (u : ℝ ≃o ℝ) (x : ℝ) : hbar u (x : OnePoint ℝ) = ((u x : ℝ) : OnePoint ℝ) :=
  rfl

@[simp] lemma hbar_infty (u : ℝ ≃o ℝ) : hbar u ∞ = ∞ := rfl

lemma hbar_mem_Gen {u : ℝ ≃o ℝ} (hu : LM univ u) : hbar u ∈ Gen := by
  classical
  obtain ⟨R, hRf, hRq, hloc⟩ := hu
  refine ⟨insert ∞ (hRf.toFinset.image (fun x : ℝ => (x : OnePoint ℝ))), ?_, fun z hz => ?_⟩
  · intro z hz
    simp only [Finset.coe_insert, Finset.coe_image, mem_insert_iff, mem_image,
      Finite.coe_toFinset] at hz
    rcases hz with rfl | ⟨x, hx, rfl⟩
    · exact infty_mem_ratPoints
    · exact (ratPoints_coe_iff x).2 (hRq x hx)
  · induction z using OnePoint.rec with
    | infty => exact absurd (Finset.mem_insert_self _ _) hz
    | coe x =>
      have hx : x ∉ R := by
        intro h; apply hz
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, by simpa using h, rfl⟩)
      obtain ⟨M, hM, hev⟩ := hloc x (mem_univ x) hx
      refine ⟨ι M, ?_⟩
      rw [nhds_coe_eq, eventually_map]
      filter_upwards [hev, eventually_dR_ne M hM] with y h1 h2
      rw [hbar_coe, mob_ι_coe_of_ne M h2, h1]

lemma exists_hbar_of_Gen {g : OnePoint ℝ ≃ₜ OnePoint ℝ} (hg : g ∈ Gen) (hinf : g ∞ = ∞) :
    ∃ u : ℝ ≃o ℝ, LM univ u ∧ g = hbar u := by
  classical
  have hex : ∀ x : ℝ, ∃ y : ℝ, g (x : OnePoint ℝ) = y := by
    intro x
    have : g (x : OnePoint ℝ) ≠ ∞ := by
      rw [← hinf]; exact fun h => coe_ne_infty x (g.injective h)
    exact ne_infty_iff_exists.mp this |>.imp fun y hy => hy.symm
  choose ur hur using hex
  have hcont : Continuous ur := by
    rw [isOpenEmbedding_coe.isEmbedding.continuous_iff]
    have : (fun x : ℝ => ((ur x : ℝ) : OnePoint ℝ)) = g ∘ (fun x : ℝ => (x : OnePoint ℝ)) := by
      funext x; exact (hur x).symm
    rw [Function.comp_def, this]
    exact g.continuous.comp continuous_coe
  have hinj : Function.Injective ur := by
    intro x y h
    apply coe_injective (X := ℝ)
    apply g.injective
    rw [hur, hur, h]
  have hsurj : Function.Surjective ur := by
    intro y
    have : g.symm (y : OnePoint ℝ) ≠ ∞ := by
      intro h
      have := congrArg g h
      rw [Homeomorph.apply_symm_apply, hinf] at this
      exact coe_ne_infty y this
    obtain ⟨x, hx⟩ := ne_infty_iff_exists.mp this
    refine ⟨x, coe_injective ?_⟩
    rw [← hur, hx, Homeomorph.apply_symm_apply]
  obtain ⟨B, hB, hloc⟩ := hg
  have hLM : LM univ ur := by
    refine ⟨{x | (x : OnePoint ℝ) ∈ B}, ?_, ?_, ?_⟩
    · exact (B.finite_toSet.preimage (coe_injective.injOn))
    · intro r hr; exact (ratPoints_coe_iff r).1 (hB hr)
    · intro x _ hx
      obtain ⟨g', hev⟩ := hloc _ hx
      obtain ⟨M, rfl⟩ := ι_surjective g'
      have hev' : ∀ᶠ y : ℝ in 𝓝 x, g (y : OnePoint ℝ) = mob (ι M) (y : OnePoint ℝ) :=
        continuous_coe.continuousAt.eventually hev
      have hd : dR M x ≠ 0 := by
        intro hd
        have := hev'.self_of_nhds
        rw [mob_ι_coe_of_eq M hd, hur] at this
        exact coe_ne_infty _ this
      refine ⟨M, hd, ?_⟩
      filter_upwards [hev', eventually_dR_ne M hd] with y h1 h2
      rw [hur, mob_ι_coe_of_ne M h2] at h1
      exact coe_injective h1
  have hmono : StrictMono ur := by
    rcases hcont.strictMono_of_inj hinj with h | h
    · exact h
    · exfalso
      obtain ⟨R, hRf, -, hloc'⟩ := hLM
      obtain ⟨x, hx⟩ := hRf.infinite_compl.nonempty
      obtain ⟨M, hM, hev⟩ := hloc' x (mem_univ x) hx
      have hpos : ∀ᶠ y in 𝓝 x, 0 < dR M x * dR M y := by
        have : Tendsto (fun y => dR M x * dR M y) (𝓝 x) (𝓝 (dR M x * dR M x)) :=
          tendsto_const_nhds.mul (continuous_dR M).continuousAt
        exact this.eventually (lt_mem_nhds (mul_self_pos.mpr hM))
      obtain ⟨y, hxy, hy⟩ := (hev.and hpos).exists_gt
      have hlt := h hxy
      rw [hy.1, hev.self_of_nhds] at hlt
      have hdy : dR M y ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hy; exact lt_irrefl _ hy.2
      have := mR_sub M hM hdy
      have : 0 < mR M y - mR M x := by
        rw [this]; exact div_pos (by linarith) hy.2
      linarith
  refine ⟨StrictMono.orderIsoOfSurjective ur hmono hsurj, hLM, ?_⟩
  ext z
  induction z using OnePoint.rec with
  | infty => rw [hinf]; rfl
  | coe x => rw [hur]; rfl

end Monod.Dev.Thur
end

section
/-!
# Theorem 7.3: `T ≅ PIP⁺(S¹)`, with `A, B, C ↦` the maps of p. 254
-/

namespace CannonFloydParry.S7

open Set

theorem equivIco_symm_coe (x : Ico (0 : ℝ) (0 + 1)) :
    (AddCircle.equivIco (1 : ℝ) 0).symm x = ((x : ℝ) : UnitAddCircle) := rfl

theorem toCircle_coe (g : UI ≃o UI) {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    toCircle g (s : UnitAddCircle) =
      (((g ⟨s, hs.1, hs.2.le⟩ : UI) : ℝ) : UnitAddCircle) := by
  have hs' : s ∈ Ico (0 : ℝ) (0 + 1) := by simpa using hs
  simp only [toCircle, Equiv.trans_apply]
  rw [AddCircle.equivIco_coe_eq hs', equivIco_symm_coe]
  rfl

theorem mapC_coe {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    mapC (s : UnitAddCircle) = ((cFun s : ℝ) : UnitAddCircle) := by
  have hs' : s ∈ Ico (0 : ℝ) (0 + 1) := by simpa using hs
  simp only [mapC, Equiv.trans_apply]
  rw [AddCircle.equivIco_coe_eq hs', equivIco_symm_coe]
  rfl

theorem mink_mem_Ico {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) : mink t ∈ Ico (0 : ℝ) 1 :=
  ⟨(Mink.mink_mem ⟨ht.1, ht.2.le⟩).1, Mink.mink_lt_one ht.1 ht.2⟩

theorem conj_eval (g : Equiv.Perm UnitAddCircle) (G : ℝ → ℝ)
    (hg : ∀ s ∈ Ico (0 : ℝ) 1, g (s : UnitAddCircle) = ((G s : ℝ) : UnitAddCircle))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    (mu⁻¹ * g * mu) (t : UnitAddCircle) = ((minkR.symm (G (mink t)) : ℝ) : UnitAddCircle) := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, mu_coe, Mink.minkR_eq_mink ⟨ht.1, ht.2.le⟩,
    hg _ (mink_mem_Ico ht), mu_inv_coe]

/-- Evaluation on a Farey piece. -/
theorem piece_eval (w w' : List Bool) (P : ℝ → ℝ) (a c : ℝ)
    (hP : ∀ t ∈ Icc (fareyNode w).lo (fareyNode w).hi, P t = mob (fareyNode w) (fareyNode w') t)
    (ha : a = ((dyadicNode w').2 - (dyadicNode w').1) / ((dyadicNode w).2 - (dyadicNode w).1))
    (hc : c = (dyadicNode w').1 - a * (dyadicNode w).1) :
    ∀ t ∈ Icc (fareyNode w).lo (fareyNode w).hi, minkR.symm (a * mink t + c) = P t := by
  intro t ht
  have hI := Mink.isFarey_fareyNode w
  have hJ := Mink.isFarey_fareyNode w'
  rw [OrderIso.symm_apply_eq, hP t ht,
    Mink.minkR_eq_mink (fareyNode_Icc_subset w' (mob_bounds hI hJ ht)), mink_mob w w' ht, ← ha, hc]
  ring


/-! ### The pieces of `A`, `B`, `C` -/

theorem pieceA1 : ∀ t ∈ Icc (0 : ℝ) (1 / 2), minkR.symm ((1 / 2) * mink t + (0)) = t / (t + 1) := by
  have e : Icc (fareyNode [false]).lo (fareyNode [false]).hi = Icc (0 : ℝ) (1 / 2) := by
    norm_num [fareyNode, FracInterval.lo, FracInterval.hi, FracInterval.leftPart, FracInterval.rightPart]
  rw [← e]
  refine piece_eval [false] [false, false] _ _ _ (fun t _ => ?_) ?_ ?_
  · norm_num [mob, mobN, mobD, fareyNode, FracInterval.leftPart, FracInterval.rightPart] <;> ring_nf
  · norm_num [dyadicNode]
  · norm_num [dyadicNode]

theorem pieceA2 : ∀ t ∈ Icc (1 / 2 : ℝ) (2 / 3), minkR.symm ((1) * mink t + (-1 / 4)) = (-t + 1) / (-5 * t + 4) := by
  have e : Icc (fareyNode [true, false]).lo (fareyNode [true, false]).hi = Icc (1 / 2 : ℝ) (2 / 3) := by
    norm_num [fareyNode, FracInterval.lo, FracInterval.hi, FracInterval.leftPart, FracInterval.rightPart]
  rw [← e]
  refine piece_eval [true, false] [false, true] _ _ _ (fun t _ => ?_) ?_ ?_
  · norm_num [mob, mobN, mobD, fareyNode, FracInterval.leftPart, FracInterval.rightPart] <;> ring_nf
  · norm_num [dyadicNode]
  · norm_num [dyadicNode]

theorem pieceA3 : ∀ t ∈ Icc (2 / 3 : ℝ) (1), minkR.symm ((2) * mink t + (-1)) = (2 * t - 1) / t := by
  have e : Icc (fareyNode [true, true]).lo (fareyNode [true, true]).hi = Icc (2 / 3 : ℝ) (1) := by
    norm_num [fareyNode, FracInterval.lo, FracInterval.hi, FracInterval.leftPart, FracInterval.rightPart]
  rw [← e]
  refine piece_eval [true, true] [true] _ _ _ (fun t _ => ?_) ?_ ?_
  · norm_num [mob, mobN, mobD, fareyNode, FracInterval.leftPart, FracInterval.rightPart] <;> ring_nf
  · norm_num [dyadicNode]
  · norm_num [dyadicNode]

theorem pieceC1 : ∀ t ∈ Icc (0 : ℝ) (1 / 2), minkR.symm ((1 / 2) * mink t + (3 / 4)) = (-3 * t + 2) / (-5 * t + 3) := by
  have e : Icc (fareyNode [false]).lo (fareyNode [false]).hi = Icc (0 : ℝ) (1 / 2) := by
    norm_num [fareyNode, FracInterval.lo, FracInterval.hi, FracInterval.leftPart, FracInterval.rightPart]
  rw [← e]
  refine piece_eval [false] [true, true] _ _ _ (fun t _ => ?_) ?_ ?_
  · norm_num [mob, mobN, mobD, fareyNode, FracInterval.leftPart, FracInterval.rightPart] <;> ring_nf
  · norm_num [dyadicNode]
  · norm_num [dyadicNode]

theorem pieceC2 : ∀ t ∈ Icc (1 / 2 : ℝ) (2 / 3), minkR.symm ((2) * mink t + (-1)) = (2 * t - 1) / t := by
  have e : Icc (fareyNode [true, false]).lo (fareyNode [true, false]).hi = Icc (1 / 2 : ℝ) (2 / 3) := by
    norm_num [fareyNode, FracInterval.lo, FracInterval.hi, FracInterval.leftPart, FracInterval.rightPart]
  rw [← e]
  refine piece_eval [true, false] [false] _ _ _ (fun t _ => ?_) ?_ ?_
  · norm_num [mob, mobN, mobD, fareyNode, FracInterval.leftPart, FracInterval.rightPart] <;> ring_nf
  · norm_num [dyadicNode]
  · norm_num [dyadicNode]

theorem pieceC3 : ∀ t ∈ Icc (2 / 3 : ℝ) (1), minkR.symm ((1) * mink t + (-1 / 4)) = (5 * t - 3) / (7 * t - 4) := by
  have e : Icc (fareyNode [true, true]).lo (fareyNode [true, true]).hi = Icc (2 / 3 : ℝ) (1) := by
    norm_num [fareyNode, FracInterval.lo, FracInterval.hi, FracInterval.leftPart, FracInterval.rightPart]
  rw [← e]
  refine piece_eval [true, true] [true, false] _ _ _ (fun t _ => ?_) ?_ ?_
  · norm_num [mob, mobN, mobD, fareyNode, FracInterval.leftPart, FracInterval.rightPart] <;> ring_nf
  · norm_num [dyadicNode]
  · norm_num [dyadicNode]

theorem mink_half : mink (1 / 2) = 1 / 2 := by
  have := Mink.mink_lo [true]
  norm_num [fareyNode, dyadicNode, FracInterval.lo, FracInterval.rightPart] at this
  exact this

theorem mink_two_thirds : mink (2 / 3) = 3 / 4 := by
  have := Mink.mink_lo [true, true]
  norm_num [fareyNode, dyadicNode, FracInterval.lo, FracInterval.rightPart] at this
  exact this

theorem mink_le_of_le {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (h : s ≤ t) :
    mink s ≤ mink t := Mink.mink_strictMonoOn.monotoneOn hs ht h

theorem mink_lt_of_lt {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (h : s < t) :
    mink s < mink t := Mink.mink_strictMonoOn hs ht h

end CannonFloydParry.S7
end

section
/-!
# Theorem 7.3: `T ≅ PIP⁺(S¹)`, with `A, B, C ↦` the maps of p. 254
-/

namespace CannonFloydParry.S7

open Set

theorem symT_mem (s : FormalABC) : symT s ∈ T := by
  rw [← closure_range_symT_eq_T_and_relations.1]
  exact Subgroup.subset_closure ⟨s, rfl⟩

theorem eval_Icc (g : Equiv.Perm UnitAddCircle) (P : ℝ → ℝ)
    (h : ∀ t ∈ Ico (0 : ℝ) 1, g (t : UnitAddCircle) = ((P t : ℝ) : UnitAddCircle))
    (h1 : ((P 1 : ℝ) : UnitAddCircle) = ((P 0 : ℝ) : UnitAddCircle)) :
    ∀ t ∈ Icc (0 : ℝ) 1, g (t : UnitAddCircle) = ((P t : ℝ) : UnitAddCircle) := by
  intro t ht
  rcases eq_or_lt_of_le ht.2 with rfl | h'
  · rw [h1, show ((1 : ℝ) : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) by simp]
    exact h 0 ⟨le_rfl, zero_lt_one⟩
  · exact h t ⟨ht.1, h'⟩

theorem mink_ge {t a b : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (ha : a ∈ Icc (0 : ℝ) 1) (hab : a ≤ t)
    (hb : mink a = b) : b ≤ mink t := hb ▸ mink_le_of_le ha ht hab

theorem mink_le {t a b : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (ha : a ∈ Icc (0 : ℝ) 1) (hab : t ≤ a)
    (hb : mink a = b) : mink t ≤ b := hb ▸ mink_le_of_le ht ha hab

theorem evalA : ∀ t ∈ Icc (0 : ℝ) 1, (mu⁻¹ * symT FormalABC.A * mu) (t : UnitAddCircle) =
    ((pipA t : ℝ) : UnitAddCircle) := by
  refine eval_Icc _ _ (fun t ht => ?_) (by norm_num [pipA])
  rw [show symT FormalABC.A = toCircle mapA from rfl,
    conj_eval _ aFun (fun s hs => by rw [toCircle_coe mapA hs]; rfl) ht]
  congr 1
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
  have m0 := Mink.mink_mem ht'
  unfold pipA
  split_ifs with h1 h2
  · have hm := mink_le ht' ⟨by norm_num, by norm_num⟩ h1 mink_half
    rw [aFun_of_mem1 m0.1 hm, show mink t / 2 = 1 / 2 * mink t + 0 by ring]
    exact pieceA1 t ⟨ht.1, h1⟩
  · have hm1 := mink_ge ht' ⟨by norm_num, by norm_num⟩ (le_of_lt (not_le.mp h1)) mink_half
    have hm2 := mink_le ht' ⟨by norm_num, by norm_num⟩ h2 mink_two_thirds
    rw [aFun_of_mem2 hm1 hm2, show mink t - 1 / 4 = 1 * mink t + (-1 / 4) by ring]
    exact pieceA2 t ⟨(le_of_lt (not_le.mp h1)), h2⟩
  · have hm1 := mink_ge ht' ⟨by norm_num, by norm_num⟩ (le_of_lt (not_le.mp h2)) mink_two_thirds
    rw [aFun_of_mem3 hm1 m0.2, show 2 * mink t - 1 = 2 * mink t + (-1) by ring]
    exact pieceA3 t ⟨(le_of_lt (not_le.mp h2)), ht'.2⟩

theorem evalC : ∀ t ∈ Icc (0 : ℝ) 1, (mu⁻¹ * symT FormalABC.C * mu) (t : UnitAddCircle) =
    ((pipC t : ℝ) : UnitAddCircle) := by
  refine eval_Icc _ _ (fun t ht => ?_) (by norm_num [pipC])
  rw [show symT FormalABC.C = mapC from rfl, conj_eval _ cFun (fun s hs => mapC_coe hs) ht]
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
  have m0 := Mink.mink_mem ht'
  unfold pipC
  split_ifs with h1 h2
  · rcases eq_or_lt_of_le h1 with rfl | h1'
    · have h0 : minkR.symm 0 = 0 := by
        rw [OrderIso.symm_apply_eq, Mink.minkR_eq_mink ⟨le_rfl, zero_le_one⟩, Mink.mink_zero]
      have e1 : cFun (1 / 2) = 0 := by norm_num [cFun]
      have e2 : ((-3 * (1 / 2 : ℝ) + 2) / (-5 * (1 / 2) + 3)) = 1 := by norm_num
      rw [mink_half, e1, h0, e2]
      exact (AddCircle.coe_period (1 : ℝ)).symm
    · have hm := mink_lt_of_lt ht' ⟨by norm_num, by norm_num⟩ h1'
      rw [mink_half] at hm
      have e : cFun (mink t) = 1 / 2 * mink t + 3 / 4 := by
        unfold cFun; rw [if_pos hm]; ring
      rw [e, pieceC1 t ⟨ht.1, h1⟩]
  · have hm1 := mink_ge ht' ⟨by norm_num, by norm_num⟩ (le_of_lt (not_le.mp h1)) mink_half
    have hm2 := mink_le ht' ⟨by norm_num, by norm_num⟩ h2 mink_two_thirds
    have e : cFun (mink t) = 2 * mink t + (-1) := by
      unfold cFun; split_ifs <;> linarith
    rw [e, pieceC2 t ⟨(le_of_lt (not_le.mp h1)), h2⟩]
  · have hm1 := mink_ge ht' ⟨by norm_num, by norm_num⟩ (le_of_lt (not_le.mp h2)) mink_two_thirds
    have e : cFun (mink t) = 1 * mink t + (-1 / 4) := by
      unfold cFun; split_ifs <;> linarith
    rw [e, pieceC3 t ⟨(le_of_lt (not_le.mp h2)), ht'.2⟩]


end CannonFloydParry.S7
end

section
/-! Lifts of elements of `T` to the line, and the closure theorem (the first milestone): the
maps satisfying `IsThompsonCircle` form a group. -/

namespace CannonFloydParry.S5

/-! ### Dyadic arithmetic -/

lemma isDyadic_int (k : ℤ) : IsDyadic (k : ℝ) := ⟨k, 0, by simp⟩

lemma dy_add {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x + y) := by
  obtain ⟨m, k, rfl⟩ := hx
  obtain ⟨n, l, rfl⟩ := hy
  refine ⟨m * 2 ^ l + n * 2 ^ k, k + l, ?_⟩
  push_cast
  field_simp
  ring

lemma dy_neg {x : ℝ} (hx : IsDyadic x) : IsDyadic (-x) := by
  obtain ⟨m, k, rfl⟩ := hx
  exact ⟨-m, k, by push_cast; ring⟩

lemma dy_sub {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x - y) := by
  simpa [sub_eq_add_neg] using dy_add hx (dy_neg hy)

lemma dy_zpow {x : ℝ} (hx : IsDyadic x) (n : ℤ) : IsDyadic ((2 : ℝ) ^ n * x) := by
  obtain ⟨m, k, rfl⟩ := hx
  rcases n with n | n
  · refine ⟨m * 2 ^ n, k, ?_⟩
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    push_cast
    ring
  · refine ⟨m, k + (n + 1), ?_⟩
    rw [zpow_negSucc, pow_add]
    field_simp
    ring

lemma dy_fract {x : ℝ} (hx : IsDyadic x) : IsDyadic (Int.fract x) := by
  rw [Int.fract]; exact dy_sub hx (isDyadic_int _)

/-! ### Good lifts -/

/-- `L` is affine with slope a power of `2` on every closed interval whose interior avoids the
integer translates of `B`. -/
def IsPL (L : ℝ ≃o ℝ) (B : Finset ℝ) : Prop :=
  ∀ x y : ℝ, x < y → (∀ t ∈ Set.Ioo x y, ∀ b ∈ B, ∀ k : ℤ, t ≠ b + k) →
    ∃ (n : ℤ) (c : ℝ), ∀ z ∈ Set.Icc x y, L z = 2 ^ n * z + c

structure GoodLift (L : ℝ ≃o ℝ) : Prop where
  per : ∀ x, L (x + 1) = L x + 1
  dy : ∀ x, IsDyadic x → IsDyadic (L x)
  pl : ∃ B : Finset ℝ, (∀ b ∈ B, IsDyadic b) ∧ IsPL L B

lemma isThompsonCircle_iff {f : Equiv.Perm UnitAddCircle} :
    IsThompsonCircle f ↔ ∃ L : ℝ ≃o ℝ, GoodLift L ∧ ∀ x : ℝ, f (x : UnitAddCircle) = ((L x : ℝ) : UnitAddCircle) := by
  constructor
  · rintro ⟨L, hper, hcov, hdy, B, hB, hpl⟩
    exact ⟨L, ⟨hper, hdy, B, hB, hpl⟩, hcov⟩
  · rintro ⟨L, ⟨hper, hdy, B, hB, hpl⟩, hcov⟩
    exact ⟨L, hper, hcov, hdy, B, hB, hpl⟩

namespace GoodLift
variable {L : ℝ ≃o ℝ}

lemma per_nat (hL : GoodLift L) (x : ℝ) (n : ℕ) : L (x + n) = L x + n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, ← add_assoc, hL.per, ih]; ring

lemma per_int (hL : GoodLift L) (x : ℝ) (k : ℤ) : L (x + k) = L x + k := by
  rcases k with n | n
  · simpa using hL.per_nat x n
  · have hc : ((Int.negSucc n : ℤ) : ℝ) = -((n : ℝ) + 1) := by rw [Int.cast_negSucc]; push_cast; ring
    have := hL.per_nat (x + ((Int.negSucc n : ℤ) : ℝ)) (n + 1)
    rw [hc] at this ⊢
    push_cast at this
    rw [show x + -((n : ℝ) + 1) + ((n : ℝ) + 1) = x by ring] at this
    linarith

lemma symm_per_int (hL : GoodLift L) (x : ℝ) (k : ℤ) : L.symm (x + k) = L.symm x + k := by
  apply L.injective
  rw [hL.per_int, OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]

/-- The key fact: the inverse of a good lift maps dyadic rationals to dyadic rationals. -/
lemma symm_dy (hL : GoodLift L) (w : ℝ) (hw : IsDyadic w) : IsDyadic (L.symm w) := by
  obtain ⟨B, hB, hpl⟩ := hL.pl
  set z := L.symm w
  let S : Finset ℝ := insert ((⌊z⌋ : ℤ) : ℝ) (B.image fun b => b + ⌊z - b⌋)
  have hS : S.Nonempty := Finset.insert_nonempty _ _
  set x := S.max' hS
  have hxS : x ∈ S := S.max'_mem hS
  have hle : ∀ s ∈ S, s ≤ z := by
    intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact Int.floor_le z
    · obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hs
      linarith [Int.floor_le (z - b)]
  have hxz : x ≤ z := hle x hxS
  have hxdy : IsDyadic x := by
    rcases Finset.mem_insert.1 hxS with h | h
    · rw [h]; exact isDyadic_int _
    · obtain ⟨b, hb, h⟩ := Finset.mem_image.1 h
      rw [← h]; exact dy_add (hB b hb) (isDyadic_int _)
  rcases eq_or_lt_of_le hxz with h | h
  · rw [← h]; exact hxdy
  have havoid : ∀ t ∈ Set.Ioo x z, ∀ b ∈ B, ∀ k : ℤ, t ≠ b + k := by
    rintro t ⟨ht1, ht2⟩ b hb k rfl
    have hk : k ≤ ⌊z - b⌋ := Int.le_floor.2 (by linarith)
    have : b + ⌊z - b⌋ ≤ x := S.le_max' _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hb))
    have : (k : ℝ) ≤ ⌊z - b⌋ := by exact_mod_cast hk
    linarith
  obtain ⟨n, c, hc⟩ := hpl x z h havoid
  have hcx := hc x ⟨le_rfl, hxz⟩
  have hcz := hc z ⟨hxz, le_rfl⟩
  have hcdy : IsDyadic c := by
    have : c = L x - 2 ^ n * x := by linarith
    rw [this]; exact dy_sub (hL.dy x hxdy) (dy_zpow hxdy n)
  have hzw : L z = w := OrderIso.apply_symm_apply L w
  have : z = 2 ^ (-n) * (w - c) := by
    rw [← hzw, hcz, zpow_neg]
    field_simp
    ring
  rw [this]
  exact dy_zpow (dy_sub hw hcdy) _

lemma symm (hL : GoodLift L) : GoodLift L.symm := by
  obtain ⟨B, hB, hpl⟩ := hL.pl
  refine ⟨fun x => by simpa using hL.symm_per_int x 1, hL.symm_dy, B.image (fun b => Int.fract (L b)), ?_, ?_⟩
  · intro b' hb'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hb'
    exact dy_fract (hL.dy b (hB b hb))
  · intro x y hxy havoid
    have hxy' : L.symm x < L.symm y := L.symm.strictMono hxy
    have havoid' : ∀ t ∈ Set.Ioo (L.symm x) (L.symm y), ∀ b ∈ B, ∀ k : ℤ, t ≠ b + k := by
      rintro t ⟨ht1, ht2⟩ b hb k rfl
      refine havoid (L (b + k)) ⟨?_, ?_⟩ (Int.fract (L b)) (Finset.mem_image_of_mem _ hb) (⌊L b⌋ + k) ?_
      · have := L.strictMono ht1; rwa [OrderIso.apply_symm_apply] at this
      · have := L.strictMono ht2; rwa [OrderIso.apply_symm_apply] at this
      · rw [hL.per_int]; push_cast; rw [Int.fract]; ring
    obtain ⟨n, c, hc⟩ := hpl _ _ hxy' havoid'
    refine ⟨-n, -(2 ^ (-n) * c), fun z hz => ?_⟩
    have hs : L.symm z ∈ Set.Icc (L.symm x) (L.symm y) :=
      ⟨L.symm.monotone hz.1, L.symm.monotone hz.2⟩
    have := hc _ hs
    rw [OrderIso.apply_symm_apply] at this
    rw [zpow_neg]
    field_simp
    linarith

lemma trans {L₁ L₂ : ℝ ≃o ℝ} (h₁ : GoodLift L₁) (h₂ : GoodLift L₂) : GoodLift (L₁.trans L₂) := by
  obtain ⟨B₁, hB₁, hpl₁⟩ := h₁.pl
  obtain ⟨B₂, hB₂, hpl₂⟩ := h₂.pl
  refine ⟨fun x => by simp [h₁.per, h₂.per], fun x hx => h₂.dy _ (h₁.dy x hx),
    B₁ ∪ B₂.image (fun b => Int.fract (L₁.symm b)), ?_, ?_⟩
  · intro b hb
    rcases Finset.mem_union.1 hb with hb | hb
    · exact hB₁ b hb
    · obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hb
      exact dy_fract (h₁.symm_dy b' (hB₂ b' hb'))
  · intro x y hxy havoid
    obtain ⟨m, c₁, hc₁⟩ := hpl₁ x y hxy (fun t ht b hb k => havoid t ht b (Finset.mem_union_left _ hb) k)
    have hxy' : L₁ x < L₁ y := L₁.strictMono hxy
    have havoid' : ∀ t ∈ Set.Ioo (L₁ x) (L₁ y), ∀ b ∈ B₂, ∀ k : ℤ, t ≠ b + k := by
      rintro t ⟨ht1, ht2⟩ b hb k rfl
      refine havoid (L₁.symm (b + k)) ⟨?_, ?_⟩ (Int.fract (L₁.symm b))
        (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb)) (⌊L₁.symm b⌋ + k) ?_
      · have := L₁.symm.strictMono ht1; rwa [OrderIso.symm_apply_apply] at this
      · have := L₁.symm.strictMono ht2; rwa [OrderIso.symm_apply_apply] at this
      · rw [h₁.symm_per_int]; push_cast; rw [Int.fract]; ring
    obtain ⟨n, c₂, hc₂⟩ := hpl₂ _ _ hxy' havoid'
    refine ⟨n + m, 2 ^ n * c₁ + c₂, fun z hz => ?_⟩
    have hz' : L₁ z ∈ Set.Icc (L₁ x) (L₁ y) := ⟨L₁.monotone hz.1, L₁.monotone hz.2⟩
    simp only [OrderIso.trans_apply]
    rw [hc₂ _ hz', hc₁ z hz, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring

end GoodLift

/-! ### The closure theorem -/


end CannonFloydParry.S5
end

section
/-! `toCircle` is an injective group homomorphism from the order isomorphisms of `[0,1]`. -/

namespace CannonFloydParry.S5

lemma icoPerm_mul (f g : UI ≃o UI) : icoPerm (f * g) = icoPerm f * icoPerm g := by
  ext x; rfl

lemma toCircle_mul (f g : UI ≃o UI) : toCircle (f * g) = toCircle f * toCircle g := by
  ext x
  simp only [toCircle, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.trans_apply,
    Equiv.apply_symm_apply, icoPerm_mul]

lemma toCircle_one : toCircle 1 = 1 := by
  ext x
  simp only [toCircle, Equiv.trans_apply, Equiv.Perm.coe_one, id]
  have : icoPerm (1 : UI ≃o UI) = 1 := by ext y; rfl
  rw [this, Equiv.Perm.coe_one, id, Equiv.symm_apply_apply]

/-- `toCircle` as a group homomorphism. -/
noncomputable def toCircleHom : (UI ≃o UI) →* Equiv.Perm UnitAddCircle where
  toFun := toCircle
  map_one' := toCircle_one
  map_mul' := toCircle_mul

@[simp] lemma toCircleHom_apply (f : UI ≃o UI) : toCircleHom f = toCircle f := rfl

end CannonFloydParry.S5
end

section
/-! Evaluating `A`, `B`, `C` and their inverses on `[0,1)` representatives of the circle. -/

namespace CannonFloydParry.S5

/-- The representative in `[0,1)` of a point of the circle. -/
noncomputable def ico (x : UnitAddCircle) : ℝ := (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)

lemma ico_nonneg (x : UnitAddCircle) : 0 ≤ ico x := (AddCircle.equivIco (1 : ℝ) 0 x).2.1
lemma ico_lt_one (x : UnitAddCircle) : ico x < 1 := by
  have h := (AddCircle.equivIco (1 : ℝ) 0 x).2.2
  unfold ico
  linarith

lemma ico_symm (y : Set.Ico (0 : ℝ) (0 + 1)) : ico ((AddCircle.equivIco (1 : ℝ) 0).symm y) = y := by
  simp [ico]

lemma ico_toCircle (f : UI ≃o UI) (x : UnitAddCircle) :
    ico (toCircle f x) = (f ⟨ico x, ico_nonneg x, (ico_lt_one x).le⟩ : ℝ) := by
  simp only [toCircle, Equiv.trans_apply, ico_symm]
  rfl

/-! Piecewise formulas. -/

/-! The generators and their inverses on representatives. -/

end CannonFloydParry.S5
end

section
/-! Example 5.1 (the second milestone): elements of `F` induce elements of `T`, and `C ∈ T`.
Both lifts are periodic extensions `x ↦ ℓ(fract x) + ⌊x⌋`. -/

namespace CannonFloydParry.S5

lemma ico_coe (x : ℝ) : ico (x : UnitAddCircle) = Int.fract x := by
  simp [ico, AddCircle.coe_equivIco_mk_apply]

lemma circle_ext {u v : UnitAddCircle} (h : ico u = ico v) : u = v :=
  (AddCircle.equivIco (1 : ℝ) 0).injective (Subtype.ext h)

/-! ### Periodic extensions -/

noncomputable def perExt (ℓ : ℝ → ℝ) (x : ℝ) : ℝ := ℓ (Int.fract x) + ⌊x⌋

structure PerData (ℓ : ℝ → ℝ) : Prop where
  mono : StrictMonoOn ℓ (Set.Icc 0 1)
  one : ℓ 1 = ℓ 0 + 1
  surj : ∀ v ∈ Set.Icc (ℓ 0) (ℓ 0 + 1), ∃ u ∈ Set.Icc (0 : ℝ) 1, ℓ u = v

namespace PerData
variable {ℓ : ℝ → ℝ} (h : PerData ℓ)
include h

lemma fract_mem (x : ℝ) : Int.fract x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩

lemma lt_top (x : ℝ) : ℓ (Int.fract x) < ℓ 0 + 1 := by
  rw [← h.one]; exact h.mono (h.fract_mem x) ⟨zero_le_one, le_rfl⟩ (Int.fract_lt_one x)

lemma bot_le (x : ℝ) : ℓ 0 ≤ ℓ (Int.fract x) :=
  h.mono.monotoneOn ⟨le_rfl, zero_le_one⟩ (h.fract_mem x) (Int.fract_nonneg x)

lemma strictMono : StrictMono (perExt ℓ) := by
  intro x y hxy
  unfold perExt
  rcases eq_or_lt_of_le (Int.floor_mono hxy.le) with he | hl
  · have : Int.fract x < Int.fract y := by
      unfold Int.fract; rw [he]; linarith
    rw [he]
    have := h.mono (h.fract_mem x) (h.fract_mem y) this
    linarith
  · have hk : (⌊x⌋ : ℝ) + 1 ≤ ⌊y⌋ := by exact_mod_cast hl
    linarith [h.lt_top x, h.bot_le y]

lemma surjective : Function.Surjective (perExt ℓ) := by
  intro v
  set k := ⌊v - ℓ 0⌋
  have hk1 : (k : ℝ) ≤ v - ℓ 0 := Int.floor_le _
  have hk2 : v - ℓ 0 < k + 1 := Int.lt_floor_add_one _
  obtain ⟨u, hu, hlu⟩ := h.surj (v - k) ⟨by linarith, by linarith⟩
  have hu1 : u < 1 := by
    rcases eq_or_lt_of_le hu.2 with rfl | h1
    · rw [h.one] at hlu; linarith
    · exact h1
  refine ⟨u + k, ?_⟩
  unfold perExt
  rw [Int.fract_add_intCast, Int.fract_eq_self.2 ⟨hu.1, hu1⟩, Int.floor_add_intCast,
    Int.floor_eq_zero_iff.2 ⟨hu.1, hu1⟩]
  push_cast
  linarith

/-- The lift as an order isomorphism of the line. -/
noncomputable def lift : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective _ h.strictMono h.surjective

@[simp] lemma lift_apply (x : ℝ) : h.lift x = perExt ℓ x := rfl

lemma per (x : ℝ) : h.lift (x + 1) = h.lift x + 1 := by
  simp only [lift_apply, perExt]
  rw [Int.fract_add_one, Int.floor_add_one]; push_cast; ring

lemma eq_on {k : ℤ} {z : ℝ} (hz : z ∈ Set.Icc (k : ℝ) (k + 1)) : h.lift z = ℓ (z - k) + k := by
  simp only [lift_apply, perExt]
  rcases eq_or_lt_of_le hz.2 with he | hlt
  · rw [he, show (k : ℝ) + 1 = ((k + 1 : ℤ) : ℝ) by push_cast; ring, Int.fract_intCast,
      Int.floor_intCast]
    push_cast
    rw [show (k : ℝ) + 1 - k = 1 by ring, h.one]; ring
  · have hfl : ⌊z⌋ = k := Int.floor_eq_iff.2 ⟨hz.1, hlt⟩
    rw [Int.fract, hfl]

end PerData

/-! ### Elements of `F` -/

lemma orderIso_zero (f : UI ≃o UI) : f ⟨0, zero_mem_UI⟩ = ⟨0, zero_mem_UI⟩ := by
  apply le_antisymm
  · obtain ⟨z, hz⟩ := f.surjective ⟨0, zero_mem_UI⟩
    have := f.monotone (show (⟨0, zero_mem_UI⟩ : UI) ≤ z from Subtype.coe_le_coe.mp z.2.1)
    rwa [hz] at this
  · exact Subtype.coe_le_coe.mp (f ⟨0, zero_mem_UI⟩).2.1

lemma perData_extendFun (f : UI ≃o UI) : PerData (extendFun f) := by
  have h0 : extendFun f 0 = 0 := by
    rw [extendFun_of_mem f zero_mem_UI, orderIso_zero]
  have h1 : extendFun f 1 = 1 := by
    rw [extendFun_of_mem f one_mem_UI, orderIso_one]
  refine ⟨fun a _ b _ hab => (extend f).strictMono hab, by rw [h0, h1]; ring, ?_⟩
  intro v hv
  rw [h0] at hv
  have hv' : v ∈ Set.Icc (0 : ℝ) 1 := by simpa using hv
  refine ⟨f.symm ⟨v, hv'⟩, (f.symm ⟨v, hv'⟩).2, ?_⟩
  rw [extendFun_of_mem f (f.symm ⟨v, hv'⟩).2]
  simp

lemma extendFun_lt_one (f : UI ≃o UI) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (hu1 : u < 1) :
    extendFun f u < 1 := by
  rw [extendFun_of_mem f hu]
  exact (orderIso_lt_one_iff f ⟨u, hu⟩).2 hu1

lemma extendFun_nonneg (f : UI ≃o UI) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ extendFun f u := by
  rw [extendFun_of_mem f hu]; exact (f ⟨u, hu⟩).2.1

lemma toCircle_mem_T_of_mem_F {f : UI ≃o UI} (hf : f ∈ F) : toCircle f ∈ T := by
  apply Subgroup.subset_closure
  have hd := perData_extendFun f
  obtain ⟨B, hB, hpl⟩ := mem_F_iff_isThompson.1 hf
  refine isThompsonCircle_iff.2 ⟨hd.lift, ⟨hd.per, ?_, insert 0 B, ?_, ?_⟩, ?_⟩
  · -- dyadics to dyadics
    intro x hx
    simp only [PerData.lift_apply, perExt]
    have hfx := dy_fract hx
    have hm := (bijOn_dyadic hf).mapsTo (show (⟨Int.fract x, hd.fract_mem x⟩ : UI) ∈
      {z : UI | IsDyadic (z : ℝ)} from hfx)
    rw [extendFun_of_mem f (hd.fract_mem x)]
    exact dy_add hm (isDyadic_int _)
  · intro b hb
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact ⟨0, 0, by norm_num⟩
    · exact hB b hb
  · intro x y hxy havoid
    set k := ⌊x⌋
    have hkx : (k : ℝ) ≤ x := Int.floor_le x
    have hxk : x < k + 1 := Int.lt_floor_add_one x
    have hyk : y ≤ k + 1 := by
      by_contra hy; push Not at hy
      exact havoid (k + 1) ⟨hxk, hy⟩ 0 (Finset.mem_insert_self _ _) (k + 1) (by push_cast; ring)
    have hx' : x - k ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hy' : y - k ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    obtain ⟨n, c, hc⟩ := hpl ⟨x - k, hx'⟩ ⟨y - k, hy'⟩ (by simp; linarith) (by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Ioo, Finset.mem_coe, Set.mem_empty_iff_false, iff_false,
        not_and]
      intro ht hbt
      exact havoid (t + k) ⟨by linarith [ht.1], by linarith [ht.2]⟩ t
        (Finset.mem_insert_of_mem hbt) k rfl)
    refine ⟨n, c + k - 2 ^ n * k, fun z hz => ?_⟩
    have hzk : z ∈ Set.Icc (k : ℝ) (k + 1) := ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have hz' : z - k ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hzk.1], by linarith [hzk.2]⟩
    rw [hd.eq_on hzk, extendFun_of_mem f hz']
    have := hc ⟨z - k, hz'⟩ ⟨by simp; linarith [hz.1], by simp; linarith [hz.2]⟩
    simp only at this
    rw [this]; ring
  · -- covering
    intro x
    apply circle_ext
    have e : (⟨ico (x : UnitAddCircle), ico_nonneg _, (ico_lt_one _).le⟩ : UI) =
        ⟨Int.fract x, hd.fract_mem x⟩ := Subtype.ext (ico_coe x)
    rw [ico_toCircle, e, ico_coe]
    simp only [PerData.lift_apply, perExt]
    rw [Int.fract_add_intCast, Int.fract_eq_self.2 ⟨extendFun_nonneg f (hd.fract_mem x),
      extendFun_lt_one f (hd.fract_mem x) (Int.fract_lt_one x)⟩, extendFun_of_mem f (hd.fract_mem x)]

/-! ### The map `C` -/


end CannonFloydParry.S5
end

section
/-! The third milestone: an element of `T` fixing `[0]` comes from `F` (CFP p. 235). -/

namespace CannonFloydParry.S5

lemma coe_ico (p : UnitAddCircle) : ((ico p : ℝ) : UnitAddCircle) = p := by
  apply circle_ext
  rw [ico_coe, Int.fract_eq_self.2 ⟨ico_nonneg p, ico_lt_one p⟩]

/-- An order isomorphism of the line fixing `0` and `1` restricts to one of `[0,1]`. -/
noncomputable def restrictUI (L : ℝ ≃o ℝ) (h0 : L 0 = 0) (h1 : L 1 = 1) : UI ≃o UI := by
  have hs0 : L.symm 0 = 0 := by rw [L.symm_apply_eq, h0]
  have hs1 : L.symm 1 = 1 := by rw [L.symm_apply_eq, h1]
  refine
    { toFun := fun z => ⟨L z, ?_, ?_⟩
      invFun := fun z => ⟨L.symm z, ?_, ?_⟩
      left_inv := ?_, right_inv := ?_, map_rel_iff' := ?_ }
  · have := L.monotone z.2.1; rwa [h0] at this
  · have := L.monotone z.2.2; rwa [h1] at this
  · have := L.symm.monotone z.2.1; rwa [hs0] at this
  · have := L.symm.monotone z.2.2; rwa [hs1] at this
  · intro z; ext; simp
  · intro z; ext; simp
  · intro a b; exact L.le_iff_le

@[simp] lemma restrictUI_coe (L : ℝ ≃o ℝ) (h0 : L 0 = 0) (h1 : L 1 = 1) (z : UI) :
    ((restrictUI L h0 h1 z : UI) : ℝ) = L z := rfl

theorem exists_toCircle_eq_of_mem_T_of_apply_zero' {f : Equiv.Perm UnitAddCircle} (hf : f ∈ T)
    (h0 : f 0 = 0) : ∃ g ∈ F, toCircle g = f :=
  by
  try haveI := hf; try haveI := h0; first
    | exact CannonFloydParry.exists_toCircle_eq_of_mem_T_of_apply_zero hf h0
    | exact CannonFloydParry.exists_toCircle_eq_of_mem_T_of_apply_zero
    | exact CannonFloydParry.exists_toCircle_eq_of_mem_T_of_apply_zero ..
    | (apply CannonFloydParry.exists_toCircle_eq_of_mem_T_of_apply_zero <;> first | assumption | infer_instance)
    | simpa using CannonFloydParry.exists_toCircle_eq_of_mem_T_of_apply_zero


end CannonFloydParry.S5
end

section
/-!
# The circle `ℝ/ℤ` and `P¹`: the homeomorphism `c`, `[s] ↦ τ(?⁻¹(s))`, `[0] ↦ ∞`
-/

namespace Monod.Dev.Thur

open OnePoint Filter Topology Set CannonFloydParry CannonFloydParry.S7

/-! ### `?` on `(0,1)` -/

lemma minkR_zero : minkR 0 = 0 := by
  rw [Mink.minkR_eq_mink ⟨le_rfl, zero_le_one⟩, Mink.mink_zero]

lemma minkR_one : minkR 1 = 1 := by
  rw [Mink.minkR_eq_mink ⟨zero_le_one, le_rfl⟩, Mink.mink_one]

lemma minkR_mem_Ioo {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : minkR t ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · have := minkR.strictMono ht.1; rwa [minkR_zero] at this
  · have := minkR.strictMono ht.2; rwa [minkR_one] at this

lemma minkR_symm_mem_Ioo {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : minkR.symm t ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · have := minkR.symm.strictMono ht.1; rwa [minkR_symm_zero] at this
  · have := minkR.symm.strictMono ht.2; rwa [minkR_symm_one] at this

lemma coe_eq_coe_of_Ico {s s' : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) (hs' : s' ∈ Ico (0 : ℝ) 1)
    (h : (s : UnitAddCircle) = s') : s = s' := by
  have hs0 : s ∈ Ico (0 : ℝ) (0 + 1) := by simpa using hs
  have hs0' : s' ∈ Ico (0 : ℝ) (0 + 1) := by simpa using hs'
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico hs0 hs0').1 h

lemma circle_cases (y : UnitAddCircle) : ∃ s ∈ Ico (0 : ℝ) 1, y = (s : UnitAddCircle) :=
  ⟨S5.ico y, ⟨S5.ico_nonneg y, S5.ico_lt_one y⟩, (S5.coe_ico y).symm⟩

/-! ### The map `c⁻¹` -/

noncomputable def cinv (z : OnePoint ℝ) : UnitAddCircle :=
  z.elim 0 (fun x => ((minkR (τi x) : ℝ) : UnitAddCircle))

@[simp] lemma cinv_infty : cinv ∞ = 0 := rfl

@[simp] lemma cinv_coe (x : ℝ) : cinv (x : OnePoint ℝ) = ((minkR (τi x) : ℝ) : UnitAddCircle) := rfl

lemma cinv_τ {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    cinv ((τ (minkR.symm s) : ℝ) : OnePoint ℝ) = (s : UnitAddCircle) := by
  rw [cinv_coe, τi_τ (minkR_symm_mem_Ioo hs), OrderIso.apply_symm_apply]

lemma cinv_bijective : Function.Bijective cinv := by
  constructor
  · intro z z' h
    induction z using OnePoint.rec with
    | infty =>
      induction z' using OnePoint.rec with
      | infty => rfl
      | coe x' =>
        exfalso
        have hm := minkR_mem_Ioo (τi_mem x')
        rw [cinv_infty, cinv_coe, ← AddCircle.coe_zero] at h
        have := coe_eq_coe_of_Ico ⟨le_rfl, zero_lt_one⟩ ⟨hm.1.le, hm.2⟩ h
        exact hm.1.ne this
    | coe x =>
      induction z' using OnePoint.rec with
      | infty =>
        exfalso
        have hm := minkR_mem_Ioo (τi_mem x)
        rw [cinv_infty, cinv_coe, ← AddCircle.coe_zero] at h
        have := coe_eq_coe_of_Ico ⟨hm.1.le, hm.2⟩ ⟨le_rfl, zero_lt_one⟩ h
        exact hm.1.ne' this
      | coe x' =>
        have hm := minkR_mem_Ioo (τi_mem x)
        have hm' := minkR_mem_Ioo (τi_mem x')
        rw [cinv_coe, cinv_coe] at h
        have := coe_eq_coe_of_Ico ⟨hm.1.le, hm.2⟩ ⟨hm'.1.le, hm'.2⟩ h
        rw [minkR.injective.eq_iff, τi_strictMono.injective.eq_iff] at this
        rw [this]
  · intro y
    obtain ⟨s, hs, rfl⟩ := circle_cases y
    rcases eq_or_lt_of_le hs.1 with h | h
    · exact ⟨∞, by rw [cinv_infty, ← h, AddCircle.coe_zero]⟩
    · exact ⟨_, cinv_τ ⟨h, hs.2⟩⟩

lemma continuous_coe_circle : Continuous (fun x : ℝ => (x : UnitAddCircle)) :=
  AddCircle.continuous_mk' 1

lemma continuous_cinv : Continuous cinv := by
  rw [continuous_iff_continuousAt]
  intro z
  induction z using OnePoint.rec with
  | infty =>
    rw [continuousAt_infty', coclosedCompact_eq_cocompact, cocompact_eq_atBot_atTop,
      tendsto_sup]
    have hm : Continuous minkR := minkR.continuous
    refine ⟨?_, ?_⟩
    · have h1 : Tendsto (fun x => minkR (τi x)) atBot (𝓝 0) := by
        have := (hm.tendsto 0).comp tendsto_τi_atBot
        rwa [minkR_zero] at this
      have := (continuous_coe_circle.tendsto 0).comp h1
      simpa [Function.comp_def] using this
    · have h1 : Tendsto (fun x => minkR (τi x)) atTop (𝓝 1) := by
        have := (hm.tendsto 1).comp tendsto_τi_atTop
        rwa [minkR_one] at this
      have := (continuous_coe_circle.tendsto 1).comp h1
      simpa [Function.comp_def, AddCircle.coe_period] using this
  | coe x =>
    rw [continuousAt_coe]
    exact (continuous_coe_circle.comp (minkR.continuous.comp continuous_τi)).continuousAt

/-- The homeomorphism `c : ℝ/ℤ → P¹`. -/
noncomputable def c : UnitAddCircle ≃ₜ OnePoint ℝ :=
  (Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective cinv cinv_bijective)
    continuous_cinv).symm

lemma c_symm_apply (z : OnePoint ℝ) : c.symm z = cinv z := rfl

lemma c_zero : c 0 = ∞ :=
  ((c.symm_apply_eq).mp (by rw [c_symm_apply, cinv_infty])).symm

lemma c_coe {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    c (s : UnitAddCircle) = ((τ (minkR.symm s) : ℝ) : OnePoint ℝ) :=
  ((c.symm_apply_eq).mp (by rw [c_symm_apply, cinv_τ hs])).symm

/-! ### Conjugation by `c` -/

noncomputable def Φ0 : (OnePoint ℝ ≃ₜ OnePoint ℝ) →* Equiv.Perm UnitAddCircle where
  toFun g := (c.toEquiv.trans g.toEquiv).trans c.symm.toEquiv
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

lemma Φ0_apply (g : OnePoint ℝ ≃ₜ OnePoint ℝ) (x : UnitAddCircle) : Φ0 g x = c.symm (g (c x)) := rfl

lemma Φ0_injective : Function.Injective Φ0 := by
  intro g h e
  ext z
  have := congrArg (fun φ : Equiv.Perm UnitAddCircle => φ (c.symm z)) e
  simp only [Φ0_apply, Homeomorph.apply_symm_apply] at this
  exact c.symm.injective this

lemma toCircle_zero (g : UI ≃o UI) : toCircle g 0 = 0 := by
  rw [← AddCircle.coe_zero, toCircle_coe g ⟨le_rfl, zero_lt_one⟩]
  have : g ⟨0, le_rfl, zero_le_one⟩ = ⟨0, zero_mem_UI⟩ := orderIso_zero g
  rw [this]

/-- The key identity: conjugating `hbar u` by `c` gives the image in `T` of `? ∘ fU u ∘ ?⁻¹`. -/
theorem Φ0_hbar (u : ℝ ≃o ℝ) : Φ0 (hbar u) = toCircle (cj (fU u)) := by
  ext y
  obtain ⟨z, rfl⟩ := c.symm.surjective y
  rw [Φ0_apply, Homeomorph.apply_symm_apply]
  induction z using OnePoint.rec with
  | infty => rw [hbar_infty, c_symm_apply, cinv_infty, toCircle_zero]
  | coe x =>
    have hm := minkR_mem_Ioo (τi_mem x)
    rw [hbar_coe, c_symm_apply, c_symm_apply, cinv_coe, cinv_coe,
      toCircle_coe _ ⟨hm.1.le, hm.2⟩, ← extend_coe]
    congr 1
    show minkR (τi (u x)) = extend (cj (fU u)) (minkR (τi x))
    have hx := τi_mem x
    rw [Mink.minkR_eq_mink (Ioo_subset_Icc_self hx), extend_cj _ (Ioo_subset_Icc_self hx),
      extend_fU_of_mem u hx, τ_τi, Mink.minkR_eq_mink (Ioo_subset_Icc_self (τi_mem _))]

/-! ### Two Möbius maps -/

def Tinv : SL2Z := mk 1 (-1) 0 1 (by norm_num)
def Umat : SL2Z := mk 1 (-1) 1 0 (by norm_num)

lemma mu_circle (y : UnitAddCircle) : ∃ t ∈ Ico (0 : ℝ) 1, y = mu (t : UnitAddCircle) := by
  obtain ⟨s, hs, rfl⟩ := circle_cases y
  refine ⟨minkR.symm s, ?_, ?_⟩
  · rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h, minkR_symm_zero]; exact ⟨le_rfl, zero_lt_one⟩
    · exact ⟨(minkR_symm_mem_Ioo ⟨h, hs.2⟩).1.le, (minkR_symm_mem_Ioo ⟨h, hs.2⟩).2⟩
  · rw [mu_coe, OrderIso.apply_symm_apply]

lemma c_mu_zero : c (mu ((0 : ℝ) : UnitAddCircle)) = ∞ := by
  rw [mu_coe, minkR_zero, AddCircle.coe_zero, c_zero]

lemma c_mu {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    c (mu (t : UnitAddCircle)) = ((τ t : ℝ) : OnePoint ℝ) := by
  rw [mu_coe, c_coe (minkR_mem_Ioo ht), OrderIso.symm_apply_apply]

lemma symT_mu (s : FormalABC) (P : ℝ → ℝ)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, (mu⁻¹ * symT s * mu) (t : UnitAddCircle) = ((P t : ℝ) : UnitAddCircle))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    symT s (mu (t : UnitAddCircle)) = ((minkR (P t) : ℝ) : UnitAddCircle) := by
  have := congrArg mu (h t ht)
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.inv_def,
    Equiv.apply_symm_apply] at this
  rw [this, mu_coe]

lemma τi_τ_sub_one {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : τi (τ t - 1) = pipA t := by
  obtain ⟨h0, h1⟩ := ht
  have ht0 : t ≠ 0 := h0.ne'
  have ht1 : 1 - t ≠ 0 := by linarith
  unfold pipA
  split_ifs with ha hb
  · rw [τ_of_le ha]
    have : (2 * t - 1) / t - 1 ≤ 0 := by
      rw [div_sub_one ht0]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) h0.le
    rw [τi_of_le this]
    have e : 2 - ((2 * t - 1) / t - 1) = (t + 1) / t := by field_simp; ring
    rw [e, one_div_div]
  · have ha' : 1 / 2 ≤ t := (not_le.mp ha).le
    rw [τ_of_ge ha']
    have : (2 * t - 1) / (1 - t) - 1 ≤ 0 := by
      rw [div_sub_one ht1]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    rw [τi_of_le this]
    have e : 2 - ((2 * t - 1) / (1 - t) - 1) = (-5 * t + 4) / (1 - t) := by field_simp; ring
    rw [e, one_div_div]; ring
  · have hb' : 2 / 3 ≤ t := (not_le.mp hb).le
    rw [τ_of_ge (by linarith)]
    have : 0 ≤ (2 * t - 1) / (1 - t) - 1 := by
      rw [div_sub_one ht1]; exact div_nonneg (by linarith) (by linarith)
    rw [τi_of_ge this]
    have e1 : 1 + ((2 * t - 1) / (1 - t) - 1) = (2 * t - 1) / (1 - t) := by ring
    have e2 : 2 + ((2 * t - 1) / (1 - t) - 1) = t / (1 - t) := by field_simp; ring
    rw [e1, e2, div_div_div_cancel_right₀ ht1]

lemma Φ0_mobH_Tinv : Φ0 (mobH Tinv) = symT FormalABC.A := by
  ext y
  obtain ⟨t, ht, rfl⟩ := mu_circle y
  rw [symT_mu _ _ evalA ⟨ht.1, ht.2.le⟩, Φ0_apply, mobH_apply]
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h, c_mu_zero, mob_ι_infty, c_symm_apply]
    simp [Tinv, pipA, minkR_zero]
  · rw [c_mu ⟨h, ht.2⟩, mob_ι_coe_of_ne _ (by simp [Tinv, dR]), c_symm_apply, cinv_coe,
      ← τi_τ_sub_one ⟨h, ht.2⟩]
    congr 4
    simp [Tinv, mR, nR, dR]; ring

lemma τi_mob_U {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (ht2 : t ≠ 1 / 2) :
    τi ((τ t - 1) / τ t) = pipC t := by
  obtain ⟨h0, h1⟩ := ht
  have ht0 : t ≠ 0 := h0.ne'
  have ht1 : 1 - t ≠ 0 := by linarith
  have hne2 : 2 * t - 1 ≠ 0 := by intro h; apply ht2; linarith
  unfold pipC
  split_ifs with ha hb
  · have ha' : t < 1 / 2 := lt_of_le_of_ne ha ht2
    rw [τ_of_le ha]
    have e : ((2 * t - 1) / t - 1) / ((2 * t - 1) / t) = (t - 1) / (2 * t - 1) := by
      field_simp; ring
    have : 0 ≤ (t - 1) / (2 * t - 1) := div_nonneg_of_nonpos (by linarith) (by linarith)
    rw [e, τi_of_ge this]
    have e1 : 1 + (t - 1) / (2 * t - 1) = (3 * t - 2) / (2 * t - 1) := by
      rw [add_div' _ _ _ hne2]; congr 1; ring
    have e2 : 2 + (t - 1) / (2 * t - 1) = (5 * t - 3) / (2 * t - 1) := by
      rw [add_div' _ _ _ hne2]; congr 1; ring
    rw [e1, e2, div_div_div_cancel_right₀ hne2, ← neg_div_neg_eq]; ring_nf
  · have ha' : 1 / 2 < t := not_le.mp ha
    rw [τ_of_ge ha'.le]
    have e : ((2 * t - 1) / (1 - t) - 1) / ((2 * t - 1) / (1 - t)) = (3 * t - 2) / (2 * t - 1) := by
      field_simp; ring
    have : (3 * t - 2) / (2 * t - 1) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    rw [e, τi_of_le this]
    have e1 : 2 - (3 * t - 2) / (2 * t - 1) = t / (2 * t - 1) := by
      rw [sub_div' hne2]; congr 1; ring
    rw [e1, one_div_div]
  · have hb' : 2 / 3 < t := not_le.mp hb
    rw [τ_of_ge (by linarith)]
    have e : ((2 * t - 1) / (1 - t) - 1) / ((2 * t - 1) / (1 - t)) = (3 * t - 2) / (2 * t - 1) := by
      field_simp; ring
    have : 0 ≤ (3 * t - 2) / (2 * t - 1) := div_nonneg (by linarith) (by linarith)
    rw [e, τi_of_ge this]
    have e1 : 1 + (3 * t - 2) / (2 * t - 1) = (5 * t - 3) / (2 * t - 1) := by
      rw [add_div' _ _ _ hne2]; congr 1; ring
    have e2 : 2 + (3 * t - 2) / (2 * t - 1) = (7 * t - 4) / (2 * t - 1) := by
      rw [add_div' _ _ _ hne2]; congr 1; ring
    rw [e1, e2, div_div_div_cancel_right₀ hne2]

lemma Φ0_mobH_U : Φ0 (mobH Umat) = symT FormalABC.C := by
  ext y
  obtain ⟨t, ht, rfl⟩ := mu_circle y
  rw [symT_mu _ _ evalC ⟨ht.1, ht.2.le⟩, Φ0_apply, mobH_apply]
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h, c_mu_zero, mob_ι_infty, c_symm_apply]
    have : pipC 0 = τi 1 := by
      rw [τi_of_ge zero_le_one]; norm_num [pipC]
    simp [Umat]
    rw [this]
  · by_cases h2 : t = 1 / 2
    · subst h2
      have hτ : τ (1 / 2) = 0 := by rw [τ_of_le le_rfl]; norm_num
      rw [c_mu ⟨h, ht.2⟩, hτ, mob_ι_coe_of_eq _ (by simp [Umat, dR]), c_symm_apply, cinv_infty]
      have : pipC (1 / 2) = 1 := by norm_num [pipC]
      rw [this, minkR_one, AddCircle.coe_period]
    · have hτ : τ t ≠ 0 := by
        intro e
        have := τi_τ ⟨h, ht.2⟩
        rw [e, τi_of_le le_rfl] at this
        exact h2 (by norm_num at this; linarith)
      rw [c_mu ⟨h, ht.2⟩, mob_ι_coe_of_ne _ (by simp [Umat, dR, hτ]), c_symm_apply, cinv_coe,
        ← τi_mob_U ⟨h, ht.2⟩ h2]
      congr 4
      simp [Umat, mR, nR, dR]; ring

lemma Φ0_mobH_mem_T (M : SL2Z) : Φ0 (mobH M) ∈ T := by
  let K : Subgroup SL2Z :=
    { carrier := {M | Φ0 (mobH M) ∈ T}
      one_mem' := by
        simp only [mem_setOf_eq]
        have : mobH 1 = 1 := by ext z; simp [mobH_apply, mob_one]
        rw [this, map_one]; exact T.one_mem
      mul_mem' := by
        intro a b ha hb
        simp only [mem_setOf_eq] at ha hb ⊢
        rw [mobH_mul, map_mul]; exact T.mul_mem ha hb
      inv_mem' := by
        intro a ha
        simp only [mem_setOf_eq] at ha ⊢
        have : mobH a⁻¹ = (mobH a)⁻¹ := by
          rw [eq_inv_iff_mul_eq_one, ← mobH_mul, inv_mul_cancel]
          ext z; simp [mobH_apply, mob_one]
        rw [this, map_inv]; exact T.inv_mem ha }
  have hT : Tinv ∈ K := by
    show Φ0 (mobH Tinv) ∈ T; rw [Φ0_mobH_Tinv]; exact symT_mem _
  have hU : Umat ∈ K := by
    show Φ0 (mobH Umat) ∈ T; rw [Φ0_mobH_U]; exact symT_mem _
  have eT : ModularGroup.T = Tinv⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    ext i j
    rw [mul_entry]
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.T, Tinv]
  have eS : ModularGroup.S = Tinv * Umat := by
    ext i j
    rw [mul_entry]
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.S, Tinv, Umat]
  have hK : Subgroup.closure {ModularGroup.S, ModularGroup.T} ≤ K := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · rw [eS]; exact K.mul_mem hT hU
    · rw [eT]; exact K.inv_mem hT
  rw [SpecialLinearGroup.SL2Z_generators] at hK
  exact hK (Subgroup.mem_top M)

end Monod.Dev.Thur
end

section
/-!
# A continuous map of `ℝ` that is locally Möbius off finitely many rationals is `C¹`

At a rational breakpoint `p/q` the two adjacent pieces `M⁻`, `M⁺` of `SL(2, ℤ)` send the primitive
vector `(p, q)` to proportional primitive vectors, hence to `±` each other; so their
denominators at `p/q` agree up to sign and the one-sided derivatives `1/(cx + d)²` agree.
-/

namespace Monod.Dev.Thur

open Filter Topology Set

lemma hasDerivAt_mR (M : SL2Z) {y : ℝ} (hy : dR M y ≠ 0) :
    HasDerivAt (mR M) (1 / dR M y ^ 2) y := by
  have hn : HasDerivAt (nR M) (M.1 0 0 : ℝ) y := by
    unfold nR
    simpa using ((hasDerivAt_id y).const_mul (M.1 0 0 : ℝ)).add_const (M.1 0 1 : ℝ)
  have hd : HasDerivAt (dR M) (M.1 1 0 : ℝ) y := by
    unfold dR
    simpa using ((hasDerivAt_id y).const_mul (M.1 1 0 : ℝ)).add_const (M.1 1 1 : ℝ)
  have e : ((M.1 0 0 : ℝ) * dR M y - nR M y * M.1 1 0) / dR M y ^ 2 = 1 / dR M y ^ 2 := by
    congr 1; simp only [nR, dR]; linear_combination detR M
  exact (hn.div hd hy).congr_deriv e

lemma eventually_not_mem_of_finite {R : Set ℝ} (hR : R.Finite) (x : ℝ) :
    ∀ᶠ y in 𝓝[≠] x, y ∉ R := by
  have ho : IsOpen (R \ {x})ᶜ := (hR.diff).isClosed.isOpen_compl
  filter_upwards [nhdsWithin_le_nhds (ho.mem_nhds (by simp)), self_mem_nhdsWithin] with y h1 h2
  intro hy; exact h1 ⟨hy, h2⟩

lemma left_piece {u : ℝ → ℝ} (hc : Continuous u) (hu : LM univ u) (x : ℝ) :
    ∃ a < x, ∃ M : SL2Z, ∀ y ∈ Ioc a x, dR M y ≠ 0 ∧ u y = mR M y := by
  obtain ⟨R, hRf, -, hloc⟩ := hu
  have hev : ∀ᶠ y in 𝓝[<] x, y ∉ R :=
    nhdsWithin_mono _ (fun y hy => ne_of_lt hy) (eventually_not_mem_of_finite hRf x)
  obtain ⟨a, hax, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hev
  have hax : a < x := hax
  obtain ⟨M, hM⟩ := single_of_local (S := Ioo a x) isPreconnected_Ioo
    (x₀ := (a + x) / 2) ⟨by linarith, by linarith⟩
    (fun y hy => hloc y (mem_univ y) (hsub hy))
  have hx : dR M x ≠ 0 ∧ u x = mR M x := by
    have := right_nhdsWithin_Ioo_neBot hax
    exact endpoint_of_within hM hc.continuousWithinAt
  refine ⟨a, hax, M, fun y hy => ?_⟩
  rcases eq_or_lt_of_le hy.2 with h | h
  · rw [h]; exact hx
  · exact hM y ⟨hy.1, h⟩

lemma right_piece {u : ℝ → ℝ} (hc : Continuous u) (hu : LM univ u) (x : ℝ) :
    ∃ b > x, ∃ M : SL2Z, ∀ y ∈ Ico x b, dR M y ≠ 0 ∧ u y = mR M y := by
  obtain ⟨R, hRf, -, hloc⟩ := hu
  have hev : ∀ᶠ y in 𝓝[>] x, y ∉ R :=
    nhdsWithin_mono _ (fun y hy => ne_of_gt hy) (eventually_not_mem_of_finite hRf x)
  obtain ⟨b, hxb, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hxb : x < b := hxb
  obtain ⟨M, hM⟩ := single_of_local (S := Ioo x b) isPreconnected_Ioo
    (x₀ := (x + b) / 2) ⟨by linarith, by linarith⟩
    (fun y hy => hloc y (mem_univ y) (hsub hy))
  have hx : dR M x ≠ 0 ∧ u x = mR M x := by
    have := left_nhdsWithin_Ioo_neBot hxb
    exact endpoint_of_within hM hc.continuousWithinAt
  refine ⟨b, hxb, M, fun y hy => ?_⟩
  rcases eq_or_lt_of_le hy.1 with h | h
  · rw [← h]; exact hx
  · exact hM y ⟨h, hy.2⟩

/-- Proportional primitive integer vectors are `±` each other. -/
lemma pm_vec {w₀ w₁ v₀ v₁ : ℤ} (hc : w₀ * v₁ = v₀ * w₁) (hw : ∃ a b : ℤ, a * w₀ + b * w₁ = 1)
    (hv : ∃ a b : ℤ, a * v₀ + b * v₁ = 1) : v₁ = w₁ ∨ v₁ = -w₁ := by
  obtain ⟨a, b, hab⟩ := hw
  obtain ⟨a', b', hab'⟩ := hv
  set l := a * v₀ + b * v₁
  set l' := a' * w₀ + b' * w₁
  have h0 : v₀ = l * w₀ := by linear_combination (-v₀) * hab - b * hc
  have h1 : v₁ = l * w₁ := by linear_combination (-v₁) * hab + a * hc
  have h0' : w₀ = l' * v₀ := by linear_combination (-w₀) * hab' + b' * hc
  have h1' : w₁ = l' * v₁ := by linear_combination (-w₁) * hab' - a' * hc
  have hll : l * l' = 1 := by
    have : (l * l' - 1) * (a * w₀ + b * w₁) = 0 := by
      linear_combination (-a * l') * h0 - a * h0' - (b * l') * h1 - b * h1'
    rw [hab, mul_one, sub_eq_zero] at this; exact this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hll with h | h
  · left; rw [h1, h, one_mul]
  · right; rw [h1, h]; ring

/-- The denominators at a rational point of two Möbius maps of `SL(2, ℤ)` with the same finite
value there agree up to sign. -/
lemma dR_sq_eq_of_rat {M N : SL2Z} {q : ℚ} (hM : dR M q ≠ 0) (hN : dR N q ≠ 0)
    (he : mR M q = mR N q) : dR M q ^ 2 = dR N q ^ 2 := by
  set p := q.num
  set s : ℤ := (q.den : ℤ)
  have hs : (s : ℝ) ≠ 0 := by simp [s, q.den_ne_zero]
  have hq : (q : ℝ) = p / s := by rw [← Rat.num_div_den q]; push_cast; rfl
  have hcop : ∃ α β : ℤ, α * p + β * s = 1 := by
    have hg : Int.gcd p s = 1 := by have := q.reduced; simpa [p, s, Int.gcd] using this
    have hbez := Int.gcd_eq_gcd_ab p s
    rw [hg] at hbez
    exact ⟨Int.gcdA p s, Int.gcdB p s, by push_cast at hbez; linear_combination -hbez⟩
  have prim : ∀ K : SL2Z, ∃ a b : ℤ, a * (K.1 0 0 * p + K.1 0 1 * s) +
      b * (K.1 1 0 * p + K.1 1 1 * s) = 1 := by
    intro K
    obtain ⟨α, β, hαβ⟩ := hcop
    have hd := detZ K
    refine ⟨α * K.1 1 1 - β * K.1 1 0, -α * K.1 0 1 + β * K.1 0 0, ?_⟩
    linear_combination hαβ + (α * p + β * s) * hd
  have hnR : ∀ K : SL2Z, nR K q = ((K.1 0 0 * p + K.1 0 1 * s : ℤ) : ℝ) / s := by
    intro K; rw [nR, hq]; push_cast; field_simp
  have hdR : ∀ K : SL2Z, dR K q = ((K.1 1 0 * p + K.1 1 1 * s : ℤ) : ℝ) / s := by
    intro K; rw [dR, hq]; push_cast; field_simp
  have hcross : (M.1 0 0 * p + M.1 0 1 * s) * (N.1 1 0 * p + N.1 1 1 * s) =
      (N.1 0 0 * p + N.1 0 1 * s) * (M.1 1 0 * p + M.1 1 1 * s) := by
    have := he
    rw [mR, mR, div_eq_div_iff hM hN, hnR, hnR, hdR, hdR] at this
    field_simp at this
    exact_mod_cast this
  rcases pm_vec hcross (prim M) (prim N) with h | h
  · rw [hdR, hdR, h]
  · rw [hdR, hdR, h]; push_cast; ring

theorem contDiff_of_LM {u : ℝ → ℝ} (hc : Continuous u) (hu : LM univ u) : ContDiff ℝ 1 u := by
  have key : ∀ x, ∃ a < x, ∃ b > x, ∃ M N : SL2Z, (∀ y ∈ Ioc a x, dR M y ≠ 0 ∧ u y = mR M y) ∧
      (∀ y ∈ Ico x b, dR N y ≠ 0 ∧ u y = mR N y) ∧ dR M x ^ 2 = dR N x ^ 2 := by
    intro x
    obtain ⟨a, hax, M, hM⟩ := left_piece hc hu x
    obtain ⟨b, hxb, N, hN⟩ := right_piece hc hu x
    refine ⟨a, hax, b, hxb, M, N, hM, hN, ?_⟩
    obtain ⟨R, -, hRq, hloc⟩ := hu
    have hMx := hM x ⟨hax, le_rfl⟩
    have hNx := hN x ⟨le_rfl, hxb⟩
    by_cases hxR : x ∈ R
    · obtain ⟨q, rfl⟩ := hRq x hxR
      exact dR_sq_eq_of_rat hMx.1 hNx.1 (hMx.2.symm.trans hNx.2)
    · obtain ⟨K, hK, hev⟩ := hloc x (mem_univ x) hxR
      -- `M` and `N` both agree with `K` on open intervals next to `x`
      have agree : ∀ (L : SL2Z) (y : ℝ) (U : Set ℝ), IsOpen U → y ∈ U →
          (∀ z ∈ U, dR L z ≠ 0 ∧ u z = mR L z) → (∀ᶠ z in 𝓝 y, u z = mR K z) →
          dR K y ≠ 0 → PM K L := by
        intro L y U hU hyU hL hevK hKy
        refine pm_of_eventually hKy (hL y hyU).1 ?_
        filter_upwards [hevK, hU.mem_nhds hyU] with z h1 h2
        rw [← h1, (hL z h2).2]
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
        (hev.and (eventually_dR_ne K hK))
      have hev2 : ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, u z = mR K z := hev.eventually_nhds
      obtain ⟨ε', hε', hball'⟩ := Metric.eventually_nhds_iff.mp (hev2.and (eventually_dR_ne K hK))
      set δ := min (min ε' (x - a)) (b - x) / 2
      have hδ : 0 < δ := by
        have : 0 < min (min ε' (x - a)) (b - x) := lt_min (lt_min hε' (by linarith)) (by linarith)
        positivity
      have hδ1 : δ < ε' := by
        have := min_le_left (min ε' (x - a)) (b - x)
        have := min_le_left ε' (x - a); simp only [δ]; linarith
      have hδ2 : δ < x - a := by
        have := min_le_left (min ε' (x - a)) (b - x)
        have := min_le_right ε' (x - a); simp only [δ]; linarith
      have hδ3 : δ < b - x := by
        have := min_le_right (min ε' (x - a)) (b - x); simp only [δ]; linarith
      have hyl : dist (x - δ) x < ε' := by
        rw [Real.dist_eq, show x - δ - x = -δ by ring, abs_neg, abs_of_pos hδ]; exact hδ1
      have hyr : dist (x + δ) x < ε' := by
        rw [Real.dist_eq, show x + δ - x = δ by ring, abs_of_pos hδ]; exact hδ1
      have pM : PM K M := agree M (x - δ) (Ioo a x) isOpen_Ioo ⟨by linarith, by linarith⟩
        (fun z hz => hM z ⟨hz.1, hz.2.le⟩) (hball' hyl).1 (hball' hyl).2
      have pN : PM K N := agree N (x + δ) (Ioo x b) isOpen_Ioo ⟨by linarith, by linarith⟩
        (fun z hz => hN z ⟨hz.1.le, hz.2⟩) (hball' hyr).1 (hball' hyr).2
      obtain ⟨s, hs, hsM⟩ := pM.dR_eq x
      obtain ⟨s', hs', hsN⟩ := pN.dR_eq x
      obtain ⟨t, ht, htM⟩ := pM
      obtain ⟨t', ht', htN⟩ := pN
      have e1 : dR M x = t * dR K x := by simp only [dR, htM]; push_cast; ring
      have e2 : dR N x = t' * dR K x := by simp only [dR, htN]; push_cast; ring
      rw [e1, e2]
      rcases ht with rfl | rfl <;> rcases ht' with rfl | rfl <;> push_cast <;> ring
  choose a ha b hb M N hM hN hsq using key
  have hder : ∀ x, HasDerivAt u (1 / dR (M x) x ^ 2) x := by
    intro x
    have hMx := hM x x ⟨ha x, le_rfl⟩
    have hNx := hN x x ⟨le_rfl, hb x⟩
    have hl : HasDerivWithinAt u (1 / dR (M x) x ^ 2) (Iic x) x := by
      refine (hasDerivAt_mR (M x) hMx.1).hasDerivWithinAt.congr_of_eventuallyEq ?_ hMx.2
      filter_upwards [Ioc_mem_nhdsLE (ha x)] with y hy using (hM x y hy).2
    have hr : HasDerivWithinAt u (1 / dR (M x) x ^ 2) (Ici x) x := by
      rw [hsq x]
      refine (hasDerivAt_mR (N x) hNx.1).hasDerivWithinAt.congr_of_eventuallyEq ?_ hNx.2
      filter_upwards [Ico_mem_nhdsGE (hb x)] with y hy using (hN x y hy).2
    have := hl.union hr
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (hder x).differentiableAt, ?_⟩
  have hderiv : ∀ x, deriv u x = 1 / dR (M x) x ^ 2 := fun x => (hder x).deriv
  rw [continuous_iff_continuousAt]
  intro x
  have hMx := hM x x ⟨ha x, le_rfl⟩
  have hNx := hN x x ⟨le_rfl, hb x⟩
  have hl : ContinuousWithinAt (deriv u) (Iic x) x := by
    have hcont : ContinuousAt (fun y => 1 / dR (M x) y ^ 2) x :=
      continuousAt_const.div ((continuous_dR _).continuousAt.pow 2) (pow_ne_zero 2 hMx.1)
    refine hcont.continuousWithinAt.congr_of_eventuallyEq ?_ (hderiv x)
    filter_upwards [Ioc_mem_nhdsLE (ha x)] with y hy
    rcases eq_or_lt_of_le hy.2 with h | h
    · rw [h, hderiv]
    · have hy' := hM x y hy
      have : HasDerivAt u (1 / dR (M x) y ^ 2) y := by
        refine (hasDerivAt_mR (M x) hy'.1).congr_of_eventuallyEq ?_
        filter_upwards [Ioo_mem_nhds hy.1 h] with z hz using (hM x z ⟨hz.1, hz.2.le⟩).2
      exact this.deriv
  have hr : ContinuousWithinAt (deriv u) (Ici x) x := by
    have hcont : ContinuousAt (fun y => 1 / dR (N x) y ^ 2) x :=
      continuousAt_const.div ((continuous_dR _).continuousAt.pow 2) (pow_ne_zero 2 hNx.1)
    refine hcont.continuousWithinAt.congr_of_eventuallyEq ?_ (by rw [hderiv, hsq])
    filter_upwards [Ico_mem_nhdsGE (hb x)] with y hy
    rcases eq_or_lt_of_le hy.1 with h | h
    · rw [← h, hderiv, hsq]
    · have hy' := hN x y hy
      have : HasDerivAt u (1 / dR (N x) y ^ 2) y := by
        refine (hasDerivAt_mR (N x) hy'.1).congr_of_eventuallyEq ?_
        filter_upwards [Ioo_mem_nhds h hy.2] with z hz using (hN x z ⟨hz.1.le, hz.2⟩).2
      exact this.deriv
  exact continuousAt_iff_continuous_left_right.2 ⟨hl, hr⟩

end Monod.Dev.Thur
end

section
/-!
# Piecewise `PSL(2, A)` maps lie in Monod's `G`

A map that is locally Möbius with `SL(2, A)` matrices off a finite subset of `P_A` is locally
Möbius with `SL(2, ℝ)` matrices (the same real entries) off a finite set. Hence the condition
`f ∈ Gpp` in the definition of `G A` is automatic, and `G A` is the subgroup generated by the maps
piecewise in `PSL(2, A)` with breakpoints in `P_A`.
-/

open Filter Topology

namespace Monod.Dev.GMono

open Monod

/-- An element of `SL(2, A)` viewed in `SL(2, ℝ) = SL(2, ⊤)`, with the same real entries. -/
noncomputable def toTop {A : Subring ℝ} (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    Matrix.SpecialLinearGroup (Fin 2) (⊤ : Subring ℝ) :=
  Matrix.SpecialLinearGroup.map (Subring.inclusion le_top) g

lemma slToGL_toTop {A : Subring ℝ} (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    slToGL ⊤ (toTop g) = slToGL A g := by
  ext i j
  rfl

lemma mob_toTop {A : Subring ℝ} (g : Matrix.SpecialLinearGroup (Fin 2) A) (x : OnePoint ℝ) :
    mob (toTop g) x = mob g x := by
  unfold mob
  rw [slToGL_toTop]

/-- A map piecewise in `PSL(2, A)` with breakpoints in `E` is piecewise in `PSL(2, ℝ)` with
breakpoints anywhere. -/
theorem isPiecewiseProjOn_top_univ {A : Subring ℝ} {E : Set (OnePoint ℝ)}
    {f : OnePoint ℝ ≃ₜ OnePoint ℝ} (hf : IsPiecewiseProjOn A E f) :
    IsPiecewiseProjOn ⊤ Set.univ f := by
  obtain ⟨B, -, hB⟩ := hf
  refine ⟨B, Set.subset_univ _, fun x hx => ?_⟩
  obtain ⟨g, hg⟩ := hB x hx
  exact ⟨toTop g, hg.mono fun y hy => by rw [hy, mob_toTop]⟩

/-- A map piecewise in `PSL(2, A)` with finitely many breakpoints in any set `E` lies in `Gpp`. -/
theorem mem_Gpp_of_isPiecewiseProjOn {A : Subring ℝ} {E : Set (OnePoint ℝ)}
    {f : OnePoint ℝ ≃ₜ OnePoint ℝ} (hf : IsPiecewiseProjOn A E f) : f ∈ Gpp :=
  Subgroup.subset_closure (isPiecewiseProjOn_top_univ hf)

/-- The condition `f ∈ Gpp` in the definition of `GRat` is automatic. -/
theorem GRat_eq_closure : GRat = Subgroup.closure {f | IsPiecewiseProjOn ⊥ ratPoints f} := by
  unfold GRat
  congr 1
  ext f
  exact ⟨fun h => h.2, fun h => ⟨mem_Gpp_of_isPiecewiseProjOn h, h⟩⟩

end Monod.Dev.GMono
end

section
/-!
# Monod p. 2: rational breakpoints give `C¹` maps, `HRat ≅ F` and `GRat ≅ T`
-/

namespace Monod.Dev.Thur

open OnePoint Filter Topology Set CannonFloydParry CannonFloydParry.S7

/-! ### `GRat → T` -/

lemma Φ0_mem_T_of_Gen {g : OnePoint ℝ ≃ₜ OnePoint ℝ} (hg : g ∈ Gen) : Φ0 g ∈ T := by
  obtain ⟨M, hM⟩ := exists_mob_infty (symm_mem_ratPoints hg infty_mem_ratPoints)
  have hh : g * mobH M ∈ Gen := mul_mobH_mem_Gen hg M
  have hinf : (g * mobH M) ∞ = ∞ := by
    rw [Homeomorph.mul_apply, mobH_apply, hM, Homeomorph.apply_symm_apply]
  obtain ⟨u, hu, he⟩ := exists_hbar_of_Gen hh hinf
  have h1 : Φ0 (g * mobH M) ∈ T := by
    rw [he, Φ0_hbar]
    exact S5.toCircle_mem_T_of_mem_F (mem_F_of_mem_PIPPlus01Set (mem_PIPPlus01Set_fU hu))
  have e : g = (g * mobH M) * (mobH M)⁻¹ := by group
  rw [e, map_mul, map_inv]
  exact T.mul_mem h1 (T.inv_mem (Φ0_mobH_mem_T M))

lemma Gen_subset_GRat {g : OnePoint ℝ ≃ₜ OnePoint ℝ} (hg : g ∈ Gen) : g ∈ GRat :=
  Monod.Dev.GMono.GRat_eq_closure ▸ Subgroup.subset_closure hg

/-! ### `T → GRat` -/

lemma hbar_of_F {g₀ : UI ≃o UI} (hg₀ : g₀ ∈ F) :
    ∃ u : ℝ ≃o ℝ, LM univ u ∧ Φ0 (hbar u) = toCircle g₀ := by
  have hf : cj.symm g₀ ∈ PIPPlus01Set := by
    rw [mem_PIPPlus01Set_iff, MulEquiv.apply_symm_apply]; exact hg₀
  refine ⟨uF (cj.symm g₀), LM_uF hf, ?_⟩
  rw [Φ0_hbar, fU_uF, MulEquiv.apply_symm_apply]

lemma rat_minkR_symm_dyadic {d : ℝ} (hd : IsDyadic d) (h0 : 0 < d) (h1 : d < 1) :
    ∃ q : ℚ, minkR.symm d = q := by
  obtain ⟨m, k, rfl⟩ := hd
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have hm0 : 0 < m := by
    have : (0 : ℝ) < m := by
      have := mul_pos h0 hp; rwa [div_mul_cancel₀ _ hp.ne'] at this
    exact_mod_cast this
  have hm1 : m < 2 ^ k := by
    have : (m : ℝ) < 2 ^ k := by rwa [div_lt_one hp] at h1
    exact_mod_cast this
  obtain ⟨w, -, hw⟩ := dyadic_grid k m.toNat (by
    have := Int.toNat_of_nonneg hm0.le
    zify; omega)
  have hmn : ((m.toNat : ℕ) : ℝ) = m := by exact_mod_cast Int.toNat_of_nonneg hm0.le
  have : minkR.symm ((m : ℝ) / 2 ^ k) = (fareyNode w).lo := by
    rw [← minkR_symm_dyadicNode, hw, hmn]
  rw [this]
  exact ⟨((fareyNode w).a : ℚ) / (fareyNode w).b, by simp [FracInterval.lo]⟩

lemma c_dyadic_mem_ratPoints {d : ℝ} (hd : IsDyadic d) : c (d : UnitAddCircle) ∈ ratPoints := by
  have hd' : IsDyadic (Int.fract d) := by
    rw [Int.fract]; exact isDyadic_sub hd (isDyadic_intCast _)
  have e : ((Int.fract d : ℝ) : UnitAddCircle) = (d : UnitAddCircle) := by
    rw [Int.fract, sub_eq_add_neg, show -(⌊d⌋ : ℝ) = ((-⌊d⌋ : ℤ) : ℝ) by push_cast; ring,
      coe_add_int]
  rw [← e]
  rcases eq_or_lt_of_le (Int.fract_nonneg d) with h | h
  · rw [← h, AddCircle.coe_zero, c_zero]; exact infty_mem_ratPoints
  · rw [c_coe ⟨h, Int.fract_lt_one d⟩]
    obtain ⟨q, hq⟩ := rat_minkR_symm_dyadic hd' h (Int.fract_lt_one d)
    rw [hq]
    obtain ⟨q', hq'⟩ := τ_rat q
    rw [hq']; exact Or.inr ⟨q', rfl⟩

lemma exists_of_mem_T {x : Equiv.Perm UnitAddCircle} (hx : x ∈ T) : ∃ g ∈ GRat, Φ0 g = x := by
  obtain ⟨L, -, hlift, hdy, -⟩ := mem_T_iff_isThompsonCircle.1 hx
  have hx0 : x 0 = ((L 0 : ℝ) : UnitAddCircle) := by
    rw [← hlift 0]; rfl
  have hq : c ((L 0 : ℝ) : UnitAddCircle) ∈ ratPoints :=
    c_dyadic_mem_ratPoints (hdy 0 ⟨0, 0, by simp⟩)
  obtain ⟨M, hM⟩ := exists_mob_infty hq
  set y := (Φ0 (mobH M))⁻¹ * x
  have hyT : y ∈ T := T.mul_mem (T.inv_mem (Φ0_mobH_mem_T M)) hx
  have hΦ0 : Φ0 (mobH M) 0 = x 0 := by
    rw [Φ0_apply, c_zero, mobH_apply, hM, Homeomorph.symm_apply_apply, hx0]
  have hy0 : y 0 = 0 := by
    simp only [y, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [← hΦ0, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  obtain ⟨g₀, hg₀F, hg₀⟩ := S5.exists_toCircle_eq_of_mem_T_of_apply_zero' hyT hy0
  obtain ⟨u, hu, hΦ⟩ := hbar_of_F hg₀F
  refine ⟨mobH M * hbar u, GRat.mul_mem (Gen_subset_GRat (mobH_mem_Gen M))
    (Gen_subset_GRat (hbar_mem_Gen hu)), ?_⟩
  rw [map_mul, hΦ, hg₀]
  simp [y]

lemma GRat_map : GRat.map Φ0 = T := by
  apply le_antisymm
  · rw [Monod.Dev.GMono.GRat_eq_closure, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    exact Φ0_mem_T_of_Gen hg
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := exists_of_mem_T hx
    exact ⟨g, hg, rfl⟩

/-! ### The targets -/

theorem exists_mulEquiv_GRat_T' :
    ∃ (c : UnitAddCircle ≃ₜ OnePoint ℝ) (φ : GRat ≃* CannonFloydParry.T),
      ∀ (g : GRat) (x : UnitAddCircle),
        (g : OnePoint ℝ ≃ₜ OnePoint ℝ) (c x) = c ((φ g : Equiv.Perm UnitAddCircle) x) := by
  refine ⟨c, (GRat.equivMapOfInjective Φ0 Φ0_injective).trans (MulEquiv.subgroupCongr GRat_map),
    fun g x => ?_⟩
  show _ = c (Φ0 g x)
  rw [Φ0_apply, Homeomorph.apply_symm_apply]


end Monod.Dev.Thur
end

section
/-!
# Every element of `GRat` is `C¹` in the two standard charts of `P¹`

Every `g ∈ GRat` is `mobH M ∘ hbar u` with `u : ℝ ≃o ℝ` locally Möbius off finitely many
rationals, hence `C¹` (`contDiff_of_LM`: adjacent `SL(2, ℤ)` pieces at a rational breakpoint have
equal derivative there). So in the affine chart `g` is `t ↦ mR M (u t)`, which is `C¹` wherever it is
finite. The second chart `t ↦ -1/t` is the Möbius map of `W = [[0, -1], [1, 0]] ∈ SL(2, ℤ)`, and
conjugating by `W` stays inside `GRat`, so all four chart cases reduce to the affine one.
-/

namespace Monod.Dev.Thur

open OnePoint Filter Topology Set CannonFloydParry CannonFloydParry.S7

/-- Every element of `T` is `Φ0 (mobH M * hbar u)` with `u` locally Möbius. -/
lemma exists_mobH_hbar_of_mem_T {x : Equiv.Perm UnitAddCircle} (hx : x ∈ T) :
    ∃ (M : SL2Z) (u : ℝ ≃o ℝ), LM univ u ∧ Φ0 (mobH M * hbar u) = x := by
  obtain ⟨L, -, hlift, hdy, -⟩ := mem_T_iff_isThompsonCircle.1 hx
  have hx0 : x 0 = ((L 0 : ℝ) : UnitAddCircle) := by
    rw [← hlift 0]; rfl
  have hq : c ((L 0 : ℝ) : UnitAddCircle) ∈ ratPoints :=
    c_dyadic_mem_ratPoints (hdy 0 ⟨0, 0, by simp⟩)
  obtain ⟨M, hM⟩ := exists_mob_infty hq
  set y := (Φ0 (mobH M))⁻¹ * x
  have hyT : y ∈ T := T.mul_mem (T.inv_mem (Φ0_mobH_mem_T M)) hx
  have hΦ0 : Φ0 (mobH M) 0 = x 0 := by
    rw [Φ0_apply, c_zero, mobH_apply, hM, Homeomorph.symm_apply_apply, hx0]
  have hy0 : y 0 = 0 := by
    simp only [y, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [← hΦ0, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  obtain ⟨g₀, hg₀F, hg₀⟩ := S5.exists_toCircle_eq_of_mem_T_of_apply_zero' hyT hy0
  obtain ⟨u, hu, hΦ⟩ := hbar_of_F hg₀F
  refine ⟨M, u, hu, ?_⟩
  rw [map_mul, hΦ, hg₀]
  simp [y]

/-- Every element of `GRat` is `mobH M * hbar u` with `u` locally Möbius. -/
lemma exists_mobH_hbar_of_mem_GRat {g : OnePoint ℝ ≃ₜ OnePoint ℝ} (hg : g ∈ GRat) :
    ∃ (M : SL2Z) (u : ℝ ≃o ℝ), LM univ u ∧ g = mobH M * hbar u := by
  have hT : Φ0 g ∈ T := GRat_map ▸ ⟨g, hg, rfl⟩
  obtain ⟨M, u, hu, he⟩ := exists_mobH_hbar_of_mem_T hT
  exact ⟨M, u, hu, Φ0_injective he.symm⟩

lemma contDiffOn_mR (M : SL2Z) : ContDiffOn ℝ 1 (mR M) {y | dR M y ≠ 0} := by
  have hn : ContDiff ℝ 1 (nR M) := by unfold nR; fun_prop
  have hd : ContDiff ℝ 1 (dR M) := by unfold dR; fun_prop
  exact hn.contDiffOn.div hd.contDiffOn fun y hy => hy

/-- The affine chart: `g ∈ GRat` is `C¹` where it is finite. -/
lemma contDiff_GRat_affine {g : OnePoint ℝ ≃ₜ OnePoint ℝ} (hg : g ∈ GRat) :
    ∃ u : ℝ → ℝ, ContDiffOn ℝ 1 u {t : ℝ | g t ≠ ∞} ∧ ∀ t : ℝ, g t ≠ ∞ → g t = u t := by
  obtain ⟨M, v, hv, rfl⟩ := exists_mobH_hbar_of_mem_GRat hg
  have hvC : ContDiff ℝ 1 v := contDiff_of_LM v.continuous hv
  have happ : ∀ t : ℝ,
      (mobH M * hbar v) (t : OnePoint ℝ) = mob (ι M) ((v t : ℝ) : OnePoint ℝ) := by
    intro t; rw [Homeomorph.mul_apply, hbar_coe, mobH_apply]
  have hset : {t : ℝ | (mobH M * hbar v) (t : OnePoint ℝ) ≠ ∞} = {t | dR M (v t) ≠ 0} := by
    ext t
    simp only [mem_ofPred_eq, happ]
    constructor
    · intro h hd; exact h (mob_ι_coe_of_eq M hd)
    · intro hd; rw [mob_ι_coe_of_ne M hd]; exact coe_ne_infty _
  refine ⟨fun t => mR M (v t), ?_, fun t ht => ?_⟩
  · rw [hset]
    exact (contDiffOn_mR M).comp hvC.contDiffOn fun t ht => ht
  · have ht' : t ∈ {t | dR M (v t) ≠ 0} := hset ▸ ht
    rw [happ, mob_ι_coe_of_ne M ht']

/-- The chart change `t ↦ -1/t`. -/
def Wm : SL2Z := mk 0 (-1) 1 0 (by norm_num)

/-- The chart matrices. -/
def chartM (i : Fin 2) : SL2Z := if i = 0 then 1 else Wm

lemma chart_eq (i : Fin 2) (t : ℝ) :
    (![fun t => (t : OnePoint ℝ),
        fun t => if t = 0 then OnePoint.infty else ((-t⁻¹ : ℝ) : OnePoint ℝ)] :
        Fin 2 → ℝ → OnePoint ℝ) i t = mobH (chartM i) t := by
  fin_cases i
  · simp [chartM, mobH_apply, mob_one]
  · simp only [chartM, Fin.mk_one, Fin.isValue, one_ne_zero, if_false, Matrix.cons_val_one,
      Matrix.cons_val_zero, mobH_apply]
    by_cases ht : t = 0
    · rw [if_pos ht, mob_ι_coe_of_eq]; simp [Wm, dR_mk, ht]
    · rw [if_neg ht, mob_ι_coe_of_ne]
      · congr 1; simp only [Wm, mR_mk]; push_cast; simp [div_eq_mul_inv]
      · simp [Wm, dR_mk, ht]

lemma mobH_mem_GRat (M : SL2Z) : mobH M ∈ GRat := Gen_subset_GRat (mobH_mem_Gen M)

theorem contDiff_GRat' :
    let σ : Fin 2 → ℝ → OnePoint ℝ :=
        ![fun t => (t : OnePoint ℝ),
          fun t => if t = 0 then OnePoint.infty else ((-t⁻¹ : ℝ) : OnePoint ℝ)]
      ∀ g ∈ GRat, ∀ i j : Fin 2, ∃ u : ℝ → ℝ,
        ContDiffOn ℝ 1 u {t | g (σ i t) ∈ Set.range (σ j)} ∧
          ∀ t, g (σ i t) ∈ Set.range (σ j) → g (σ i t) = σ j (u t) := by
  intro σ g hg i j
  have hσ : ∀ (k : Fin 2) (t : ℝ), σ k t = mobH (chartM k) t := chart_eq
  set A := mobH (chartM j)
  set B := mobH (chartM i)
  have hg' : A⁻¹ * g * B ∈ GRat :=
    GRat.mul_mem (GRat.mul_mem (GRat.inv_mem (mobH_mem_GRat _)) hg) (mobH_mem_GRat _)
  obtain ⟨u, hu, hue⟩ := contDiff_GRat_affine hg'
  have happ : ∀ t : ℝ, (A⁻¹ * g * B) (t : OnePoint ℝ) = A.symm (g (σ i t)) := by
    intro t; rw [hσ]; rfl
  have hiff : ∀ t : ℝ, g (σ i t) ∈ Set.range (σ j) ↔ (A⁻¹ * g * B) (t : OnePoint ℝ) ≠ ∞ := by
    intro t
    rw [happ]
    constructor
    · rintro ⟨s, hs⟩
      rw [← hs, hσ, Homeomorph.symm_apply_apply]; exact coe_ne_infty _
    · intro h
      obtain ⟨s, hs⟩ := OnePoint.ne_infty_iff_exists.mp h
      refine ⟨s, ?_⟩
      rw [hσ, hs, Homeomorph.apply_symm_apply]
  refine ⟨u, ?_, fun t ht => ?_⟩
  · have : {t | g (σ i t) ∈ Set.range (σ j)} = {t : ℝ | (A⁻¹ * g * B) (t : OnePoint ℝ) ≠ ∞} := by
      ext t; exact hiff t
    rw [this]; exact hu
  · have h := hue t ((hiff t).1 ht)
    rw [happ] at h
    rw [hσ j (u t), ← h, Homeomorph.apply_symm_apply]

theorem contDiff_and_exists_mulEquiv_GRat_T' :
    (let σ : Fin 2 → ℝ → OnePoint ℝ :=
        ![fun t => (t : OnePoint ℝ),
          fun t => if t = 0 then OnePoint.infty else ((-t⁻¹ : ℝ) : OnePoint ℝ)]
      ∀ g ∈ GRat, ∀ i j : Fin 2, ∃ u : ℝ → ℝ,
        ContDiffOn ℝ 1 u {t | g (σ i t) ∈ Set.range (σ j)} ∧
          ∀ t, g (σ i t) ∈ Set.range (σ j) → g (σ i t) = σ j (u t)) ∧
      ∃ (c : UnitAddCircle ≃ₜ OnePoint ℝ) (φ : GRat ≃* CannonFloydParry.T),
        ∀ (g : GRat) (x : UnitAddCircle),
          (g : OnePoint ℝ ≃ₜ OnePoint ℝ) (c x) = c ((φ g : Equiv.Perm UnitAddCircle) x) :=
  ⟨contDiff_GRat', exists_mulEquiv_GRat_T'⟩

end Monod.Dev.Thur
end

open Monod in
theorem solution :
    (let σ : Fin 2 → ℝ → OnePoint ℝ :=
        ![fun t => (t : OnePoint ℝ),
          fun t => if t = 0 then OnePoint.infty else ((-t⁻¹ : ℝ) : OnePoint ℝ)]
      ∀ g ∈ GRat, ∀ i j : Fin 2, ∃ u : ℝ → ℝ,
        ContDiffOn ℝ 1 u {t | g (σ i t) ∈ Set.range (σ j)} ∧
          ∀ t, g (σ i t) ∈ Set.range (σ j) → g (σ i t) = σ j (u t)) ∧
      ∃ (c : UnitAddCircle ≃ₜ OnePoint ℝ) (φ : GRat ≃* CannonFloydParry.T),
        ∀ (g : GRat) (x : UnitAddCircle),
          (g : OnePoint ℝ ≃ₜ OnePoint ℝ) (c x) = c ((φ g : Equiv.Perm UnitAddCircle) x) := by
  exact Monod.Dev.Thur.contDiff_and_exists_mulEquiv_GRat_T'
