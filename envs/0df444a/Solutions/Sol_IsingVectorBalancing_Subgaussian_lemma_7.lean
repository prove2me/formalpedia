-- Prove2me | solution 1 for IsingVectorBalancing.Subgaussian.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T17:25:58.563231+00:00
-- url     : https://prove2.me/submissions/8f51344e-52c3-41fa-ad33-78e3364d4bfd

import Mathlib
import Theorems.Thm_IsingVectorBalancing_Subgaussian_theorem_5
import Theorems.Thm_IsingVectorBalancing_Subgaussian_lemma_6
import Definitions.Def_IsingVectorBalancing_Subgaussian_Lorentz
import Definitions.Def_IsingVectorBalancing_Subgaussian_Law

section
set_option autoImplicit false
open scoped BigOperators
namespace IsingVectorBalancing.Subgaussian.Dev.L7
open IsingVectorBalancing.Subgaussian

theorem sum_fin_succ {C : Type*} [Fintype C] (k : ℕ) (G : (Fin (k+1) → C) → ℝ) :
    ∑ c : Fin (k+1) → C, G c = ∑ a : C, ∑ c' : Fin k → C, G (Fin.cons a c') := by
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Fin.consEquiv (fun _ => C)).symm _ _ ?_
  intro c
  simp

theorem pairs_succ {k : ℕ} (P : Fin (k+1) → Fin (k+1) → ℝ) :
    ∏ i, ∏ j ∈ Finset.univ.filter (fun j : Fin (k+1) => i < j), P i j =
      (∏ j : Fin k, P 0 j.succ) *
        ∏ i : Fin k, ∏ j ∈ Finset.univ.filter (fun j : Fin k => i < j), P i.succ j.succ := by
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Finset.prod_filter, Fin.prod_univ_succ]
    simp [Fin.succ_pos]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_succ]
    simp [Fin.succ_lt_succ_iff]


def ind {C : Type*} [DecidableEq C] (p : C) : C → ℝ := fun c => if c = p then 1 else 0

theorem poly_split {C : Type*} [Fintype C] [DecidableEq C] (n : ℕ)
    (A : Matrix C C ℝ) (w : Fin n → C → ℝ) (p q : C) :
    selectionPolynomial A (selections (ind p) (ind q) w) =
      A p q * ∑ c : Fin n → C, (∏ i, w i (c i)) * ((∏ i, A p (c i)) * (∏ i, A q (c i)) *
        ∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j : Fin n => i < j), A (c i) (c j)) := by
  unfold selectionPolynomial selections
  rw [sum_fin_succ]
  rw [Finset.sum_eq_single p (fun a _ ha => ?_) (fun h => absurd (Finset.mem_univ p) h)]
  · simp only [sum_fin_succ n]
    rw [Finset.sum_eq_single q (fun a _ ha => ?_) (fun h => absurd (Finset.mem_univ q) h)]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ, pairs_succ, pairs_succ]
      simp [ind, Fin.prod_univ_succ]
      ring
    · refine Finset.sum_eq_zero fun c _ => ?_
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      simp [ind, ha]
  · refine Finset.sum_eq_zero fun c _ => ?_
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp [ind, ‹a ≠ p›]


theorem tail_reduce {C : Type*} [Fintype C] [DecidableEq C] (n : ℕ)
    (enc : Fin n → Bool → C) (henc : ∀ i, Function.Injective (enc i))
    (w : Fin n → C → ℝ) (hw : ∀ i c, w i c ≠ 0 → ∃ b, c = enc i b)
    (R : (Fin n → C) → ℝ) :
    ∑ c : Fin n → C, (∏ i, w i (c i)) * R c =
      ∑ σ : Fin n → Bool, (∏ i, w i (enc i (σ i))) * R (fun i => enc i (σ i)) := by
  have hinj : Function.Injective (fun σ : Fin n → Bool => fun i => enc i (σ i)) := by
    intro σ τ h
    funext i
    exact henc i (congrFun h i)
  rw [← Finset.sum_image (f := fun c : Fin n → C => (∏ i, w i (c i)) * R c) (s := Finset.univ)
    (g := fun σ : Fin n → Bool => fun i => enc i (σ i)) (fun x _ y _ h => hinj h)]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun c _ hc => ?_
  have : ∏ i, w i (c i) = 0 := by
    by_contra hne
    have h2 := Finset.prod_ne_zero_iff.mp hne
    choose b hb using fun i => hw i (c i) (h2 i (Finset.mem_univ i))
    exact hc (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, (funext hb).symm⟩)
  rw [this, zero_mul]


abbrev Idx (n : ℕ) := Option (Option (Fin n × Bool))

def enc (n : ℕ) (i : Fin n) (b : Bool) : Idx n := some (some (i, b))

noncomputable def uvec {n d : ℕ} (v : Fin n → Vec d) (θ : Vec d) (ε : ℝ) : Idx n → Vec d
  | none => ε • θ
  | some none => 0
  | some (some (i, b)) => spin b • v i

noncomputable def wtail {n : ℕ} (h : Fin n → ℝ) (i : Fin n) : Idx n → ℝ
  | some (some (j, b)) => if j = i then Real.exp (h i * spin b) else 0
  | _ => 0

theorem enc_inj (n : ℕ) (i : Fin n) : Function.Injective (enc n i) := by
  intro a b hab
  simpa [enc] using hab

theorem wtail_ne {n : ℕ} (h : Fin n → ℝ) (i : Fin n) (c : Idx n) (hc : wtail h i c ≠ 0) :
    ∃ b, c = enc n i b := by
  rcases c with _ | _ | ⟨j, b⟩
  · simp [wtail] at hc
  · simp [wtail] at hc
  · by_cases hj : j = i
    · subst hj; exact ⟨b, rfl⟩
    · simp [wtail, hj] at hc

theorem wtail_enc {n : ℕ} (h : Fin n → ℝ) (i : Fin n) (b : Bool) :
    wtail h i (enc n i b) = Real.exp (h i * spin b) := by
  simp [wtail, enc]

theorem inner_spin {d : ℕ} (a b : Bool) (x y : Vec d) :
    inner ℝ (spin a • x) (spin b • y) = spin a * spin b * inner ℝ x y := by
  rw [real_inner_smul_left, real_inner_smul_right]; ring

theorem tilted_eq {n d : ℕ} (v : Fin n → Vec d) (h : Fin n → ℝ) (σ : Configuration n) :
    tiltedWeight v h σ = (∏ i, wtail h i (enc n i (σ i))) * weight v σ := by
  simp only [tiltedWeight, wtail_enc]
  rw [← Real.exp_sum]

theorem weight_eq {n d : ℕ} (v : Fin n → Vec d) (θ : Vec d) (ε : ℝ) (σ : Configuration n) :
    (∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
      lorentzMatrix (uvec v θ ε) (enc n i (σ i)) (enc n j (σ j))) = weight v σ := by
  unfold weight
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  simp only [lorentzMatrix, uvec, enc, inner_spin]

noncomputable def Phi {n d : ℕ} (v : Fin n → Vec d) (θ : Vec d) (ε : ℝ) (σ : Configuration n) : ℝ :=
  ∏ i, (1 - ε * (spin (σ i) * inner ℝ θ (v i)))

theorem a_zero {n d : ℕ} (v : Fin n → Vec d) (θ : Vec d) (ε : ℝ) (σ : Configuration n) :
    (∏ i, lorentzMatrix (uvec v θ ε) (some none) (enc n i (σ i))) = 1 := by
  simp [lorentzMatrix, uvec, enc]

theorem a_neg {n d : ℕ} (v : Fin n → Vec d) (θ : Vec d) (ε : ℝ) (σ : Configuration n) :
    (∏ i, lorentzMatrix (uvec v θ ε) none (enc n i (σ i))) = Phi v θ ε σ := by
  unfold Phi
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [lorentzMatrix, uvec, enc, real_inner_smul_left, real_inner_smul_right]
  ring

theorem poly_concrete {n d : ℕ} (v : Fin n → Vec d) (θ : Vec d) (ε : ℝ) (h : Fin n → ℝ)
    (p q : Idx n) :
    selectionPolynomial (lorentzMatrix (uvec v θ ε)) (selections (ind p) (ind q) (wtail h)) =
      lorentzMatrix (uvec v θ ε) p q * ∑ σ : Configuration n, tiltedWeight v h σ *
        ((∏ i, lorentzMatrix (uvec v θ ε) p (enc n i (σ i))) *
          (∏ i, lorentzMatrix (uvec v θ ε) q (enc n i (σ i)))) := by
  rw [poly_split, tail_reduce n (enc n) (enc_inj n) (wtail h) (wtail_ne h)]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [weight_eq, tilted_eq]
  ring


theorem spin_norm (b : Bool) : |spin b| = 1 := by cases b <;> simp [spin]

theorem uvec_norm {n d : ℕ} (v : Fin n → Vec d) (hv : ∀ i, ‖v i‖ ≤ 1) (θ : Vec d) (ε : ℝ)
    (hε : 0 ≤ ε) (hεθ : ε * ‖θ‖ ≤ 1) (c : Idx n) : ‖uvec v θ ε c‖ ≤ 1 := by
  rcases c with _ | _ | ⟨i, b⟩
  · simp only [uvec, norm_smul, Real.norm_eq_abs, abs_of_nonneg hε]; exact hεθ
  · simp [uvec]
  · simp only [uvec, norm_smul, Real.norm_eq_abs, spin_norm, one_mul]; exact hv i

theorem key_ineq {n d : ℕ} (v : Fin n → Vec d) (hv : ∀ i, ‖v i‖ ≤ 1) (h : Fin n → ℝ) (θ : Vec d)
    (ε : ℝ) (hε : 0 ≤ ε) (hεθ : ε * ‖θ‖ ≤ 1) :
    (∑ σ : Configuration n, tiltedWeight v h σ * Phi v θ ε σ) ^ 2 ≥
      partition v h * ((1 - ε ^ 2 * ‖θ‖ ^ 2) *
        ∑ σ : Configuration n, tiltedWeight v h σ * Phi v θ ε σ ^ 2) := by
  have hL := lemma_6 (uvec v θ ε) (uvec_norm v hv θ ε hε hεθ)
  have h5 := theorem_5 n (lorentzMatrix (uvec v θ ε)) hL (ind (some none)) (ind (none : Idx n))
    (wtail h) (fun c => by unfold ind; split_ifs <;> norm_num) (fun i c => by
      rcases c with _ | _ | ⟨j, b⟩
      · simp [wtail]
      · simp [wtail]
      · simp only [wtail]; split_ifs <;> [exact (Real.exp_pos _).le; exact le_rfl])
  have e00 : selectionPolynomial (lorentzMatrix (uvec v θ ε))
      (selections (ind (some none)) (ind (some none)) (wtail h)) = partition v h := by
    rw [poly_concrete]
    simp [a_zero, lorentzMatrix, uvec, partition]
  have e01 : selectionPolynomial (lorentzMatrix (uvec v θ ε))
      (selections (ind (some none)) (ind none) (wtail h)) =
      ∑ σ : Configuration n, tiltedWeight v h σ * Phi v θ ε σ := by
    rw [poly_concrete]
    simp only [a_zero, a_neg]
    simp [lorentzMatrix, uvec]
  have e11 : selectionPolynomial (lorentzMatrix (uvec v θ ε))
      (selections (ind none) (ind none) (wtail h)) =
      (1 - ε ^ 2 * ‖θ‖ ^ 2) * ∑ σ : Configuration n, tiltedWeight v h σ * Phi v θ ε σ ^ 2 := by
    rw [poly_concrete]
    simp only [a_neg]
    have : lorentzMatrix (uvec v θ ε) none none = 1 - ε ^ 2 * ‖θ‖ ^ 2 := by
      simp only [lorentzMatrix, uvec, real_inner_smul_left, real_inner_smul_right,
        real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [this]
    congr 1
    exact Finset.sum_congr rfl fun σ _ => by ring
  rw [e00, e01, e11] at h5
  exact h5


theorem factor_nonneg {d : ℕ} {x y : Vec d} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (a b : Bool) :
    0 ≤ 1 - spin a * spin b * inner ℝ x y := by
  have h0 : |inner ℝ x y| ≤ 1 :=
    (abs_real_inner_le_norm x y).trans (mul_le_one₀ hx (norm_nonneg _) hy)
  rw [abs_le] at h0
  have sc : ∀ b : Bool, spin b = 1 ∨ spin b = -1 := by intro b; cases b <;> simp [spin]
  rcases sc a with ha | ha <;> rcases sc b with hb | hb <;> rw [ha, hb] <;>
    nlinarith [h0.1, h0.2]

theorem partition_nonneg {n d : ℕ} (v : Fin n → Vec d) (hv : ∀ i, ‖v i‖ ≤ 1) (h : Fin n → ℝ) :
    0 ≤ partition v h := by
  refine Finset.sum_nonneg fun σ _ => mul_nonneg (Real.exp_pos _).le ?_
  exact Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => factor_nonneg (hv i) (hv j) _ _

theorem expectation_eq {n d : ℕ} (v : Fin n → Vec d) (h : Fin n → ℝ)
    (f : Configuration n → ℝ) :
    expectation v h f = (∑ σ : Configuration n, tiltedWeight v h σ * f σ) / partition v h := by
  unfold expectation probability
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun σ _ => by ring

theorem sumP {n d : ℕ} (v : Fin n → Vec d) (h : Fin n → ℝ) (hZ : partition v h ≠ 0) :
    ∑ σ : Configuration n, probability v h σ = 1 := by
  unfold probability
  rw [← Finset.sum_div]
  exact div_self hZ

theorem E_aff {n d : ℕ} (v : Fin n → Vec d) (h : Fin n → ℝ) (hZ : partition v h ≠ 0)
    (c e : ℝ) (f : Configuration n → ℝ) :
    expectation v h (fun σ => c + e * f σ) = c + e * expectation v h f := by
  unfold expectation
  have := sumP v h hZ
  have h1 : ∀ σ, probability v h σ * (c + e * f σ) =
      c * probability v h σ + e * (probability v h σ * f σ) := fun σ => by ring
  simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum, this]
  ring

theorem var_eq {n d : ℕ} (v : Fin n → Vec d) (h : Fin n → ℝ) (hZ : partition v h ≠ 0)
    (f : Configuration n → ℝ) :
    variance v h f = expectation v h (fun σ => f σ ^ 2) - expectation v h f ^ 2 := by
  unfold variance
  set m := expectation v h f with hm
  unfold expectation
  have := sumP v h hZ
  have h1 : ∀ σ, probability v h σ * (f σ - m) ^ 2 =
      probability v h σ * f σ ^ 2 - 2 * m * (probability v h σ * f σ) + m ^ 2 * probability v h σ :=
    fun σ => by ring
  simp only [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, this]
  rw [hm]; unfold expectation; ring

theorem var_aff {n d : ℕ} (v : Fin n → Vec d) (h : Fin n → ℝ) (hZ : partition v h ≠ 0)
    (c e : ℝ) (f : Configuration n → ℝ) :
    variance v h (fun σ => c + e * f σ) = e ^ 2 * variance v h f := by
  unfold variance
  rw [E_aff v h hZ]
  have : (fun σ => (c + e * f σ - (c + e * expectation v h f)) ^ 2) =
      fun σ => 0 + e ^ 2 * (f σ - expectation v h f) ^ 2 := by
    funext σ; ring
  rw [this, E_aff v h hZ]
  ring

theorem key_var {n d : ℕ} (v : Fin n → Vec d) (hv : ∀ i, ‖v i‖ ≤ 1) (h : Fin n → ℝ) (θ : Vec d)
    (ε : ℝ) (hε : 0 ≤ ε) (hεθ : ε * ‖θ‖ ≤ 1) (hZ : 0 < partition v h) :
    variance v h (Phi v θ ε) ≤
      ε ^ 2 * ‖θ‖ ^ 2 * expectation v h (fun σ => Phi v θ ε σ ^ 2) := by
  have hk := key_ineq v hv h θ ε hε hεθ
  rw [var_eq v h hZ.ne']
  simp only [expectation_eq]
  set Z := partition v h
  set S1 := ∑ σ : Configuration n, tiltedWeight v h σ * Phi v θ ε σ
  set S2 := ∑ σ : Configuration n, tiltedWeight v h σ * Phi v θ ε σ ^ 2
  have : S2 / Z - (S1 / Z) ^ 2 - ε ^ 2 * ‖θ‖ ^ 2 * (S2 / Z) =
      (Z * ((1 - ε ^ 2 * ‖θ‖ ^ 2) * S2) - S1 ^ 2) / Z ^ 2 := by
    field_simp
    ring
  have h3 : (Z * ((1 - ε ^ 2 * ‖θ‖ ^ 2) * S2) - S1 ^ 2) / Z ^ 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  linarith


open Filter Topology in
theorem E_tendsto {n d : ℕ} (v : Fin n → Vec d) (h : Fin n → ℝ) {l : Filter ℝ}
    (g : ℝ → Configuration n → ℝ) (g0 : Configuration n → ℝ)
    (hg : ∀ σ, Tendsto (fun ε => g ε σ) l (𝓝 (g0 σ))) :
    Tendsto (fun ε => expectation v h (g ε)) l (𝓝 (expectation v h g0)) :=
  tendsto_finsetSum _ fun σ _ => tendsto_const_nhds.mul (hg σ)

open Filter Topology in
theorem var_tendsto {n d : ℕ} (v : Fin n → Vec d) (h : Fin n → ℝ) {l : Filter ℝ}
    (g : ℝ → Configuration n → ℝ) (g0 : Configuration n → ℝ)
    (hg : ∀ σ, Tendsto (fun ε => g ε σ) l (𝓝 (g0 σ))) :
    Tendsto (fun ε => variance v h (g ε)) l (𝓝 (variance v h g0)) := by
  have hE := E_tendsto v h g g0 hg
  exact tendsto_finsetSum _ fun σ _ => tendsto_const_nhds.mul (((hg σ).sub hE).pow 2)

open Filter Topology in
theorem Psi_tendsto {n d : ℕ} (v : Fin n → Vec d) (θ : Vec d) (σ : Configuration n) :
    Tendsto (fun ε : ℝ => ε⁻¹ * (Phi v θ ε σ - 1)) (𝓝[>] 0)
      (𝓝 (-inner ℝ θ (signedSum v σ))) := by
  set a : Fin n → ℝ := fun i => spin (σ i) * inner ℝ θ (v i) with ha
  have hd : HasDerivAt (fun ε : ℝ => ∏ i, (1 - ε * a i))
      (∑ i, (∏ j ∈ Finset.univ.erase i, (1 - (0:ℝ) * a j)) • (-(1 * a i))) 0 :=
    HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun i (ε : ℝ) => 1 - ε * a i)
      (f' := fun i => -(1 * a i)) (x := 0)
      (fun i _ => ((hasDerivAt_id' (0:ℝ)).mul_const (a i)).const_sub 1)
  have hval : (∑ i, (∏ j ∈ Finset.univ.erase i, (1 - (0:ℝ) * a j)) • (-(1 * a i))) =
      -inner ℝ θ (signedSum v σ) := by
    simp only [zero_mul, sub_zero, Finset.prod_const_one, one_smul, one_mul, signedSum,
      inner_sum, real_inner_smul_right, Finset.sum_neg_distrib, ha]
  rw [hval] at hd
  have hs := hasDerivAt_iff_tendsto_slope.mp hd
  refine (hs.mono_left (nhdsGT_le_nhdsNE 0)).congr fun ε => ?_
  rw [slope_def_field]
  simp [Phi, ha, div_eq_inv_mul]


open Filter Topology in
theorem Phi_tendsto {n d : ℕ} (v : Fin n → Vec d) (θ : Vec d) (σ : Configuration n) :
    Tendsto (fun ε : ℝ => Phi v θ ε σ) (𝓝[>] 0) (𝓝 1) := by
  have hc : Continuous (fun ε : ℝ => Phi v θ ε σ) := by
    unfold Phi
    exact continuous_finsetProd _ fun i _ => by fun_prop
  have := hc.tendsto 0
  simp only [Phi, zero_mul, sub_zero, Finset.prod_const_one] at this
  exact this.mono_left nhdsWithin_le_nhds

open Filter Topology in
theorem main_bound {n d : ℕ} (v : Fin n → Vec d) (hv : ∀ i, ‖v i‖ ≤ 1) (h : Fin n → ℝ)
    (θ : Vec d) (hZ : 0 < partition v h) :
    variance v h (fun σ => inner ℝ θ (signedSum v σ)) ≤ ‖θ‖ ^ 2 := by
  set f0 : Configuration n → ℝ := fun σ => inner ℝ θ (signedSum v σ) with hf0
  have hZ' := hZ.ne'
  have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ),
      variance v h (fun σ => ε⁻¹ * (Phi v θ ε σ - 1)) ≤
        ‖θ‖ ^ 2 * expectation v h (fun σ => Phi v θ ε σ ^ 2) := by
    have hm : Set.Ioo (0:ℝ) ((‖θ‖ + 1)⁻¹) ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT (by positivity)
    filter_upwards [hm] with ε hε
    have hε0 : 0 < ε := hε.1
    have hεθ : ε * ‖θ‖ ≤ 1 := by
      have h1 : ε * (‖θ‖ + 1) < 1 := by
        have := mul_lt_mul_of_pos_right hε.2 (by positivity : (0:ℝ) < ‖θ‖ + 1)
        rwa [inv_mul_cancel₀ (by positivity)] at this
      nlinarith
    have hk := key_var v hv h θ ε hε0.le hεθ hZ
    have hPhi : Phi v θ ε = fun σ => 1 + ε * (ε⁻¹ * (Phi v θ ε σ - 1)) := by
      funext σ; field_simp; ring
    have hv2 := var_aff v h hZ' 1 ε (fun σ => ε⁻¹ * (Phi v θ ε σ - 1))
    rw [← hPhi] at hv2
    rw [hv2] at hk
    refine le_of_mul_le_mul_left ?_ (pow_pos hε0 2)
    linarith
  have hlim1 : Tendsto (fun ε : ℝ => variance v h (fun σ => ε⁻¹ * (Phi v θ ε σ - 1)))
      (𝓝[>] 0) (𝓝 (variance v h (fun σ => -f0 σ))) :=
    var_tendsto v h _ _ fun σ => Psi_tendsto v θ σ
  have hlim2 : Tendsto (fun ε : ℝ => ‖θ‖ ^ 2 * expectation v h (fun σ => Phi v θ ε σ ^ 2))
      (𝓝[>] 0) (𝓝 (‖θ‖ ^ 2 * expectation v h (fun _ => (1:ℝ) ^ 2))) :=
    (E_tendsto v h (fun ε σ => Phi v θ ε σ ^ 2) (fun _ => 1 ^ 2)
      fun σ => (Phi_tendsto v θ σ).pow 2).const_mul _
  have hle := le_of_tendsto_of_tendsto hlim1 hlim2 hev
  have hE1 : expectation v h (fun _ => (1:ℝ) ^ 2) = 1 := by
    simp [expectation, sumP v h hZ']
  have hneg : variance v h (fun σ => -f0 σ) = variance v h f0 := by
    have := var_aff v h hZ' 0 (-1) f0
    have e : (fun σ => -f0 σ) = fun σ => 0 + (-1) * f0 σ := by funext σ; ring
    rw [e, this]; ring
  rw [hneg, hE1] at hle
  linarith

end IsingVectorBalancing.Subgaussian.Dev.L7

namespace IsingVectorBalancing.Subgaussian
open IsingVectorBalancing.Subgaussian.Dev.L7 in
theorem chk_lemma_7 {n d : ℕ} (v : Fin n → Vec d) (hv : Admissible v)
    (h : Fin n → ℝ) (θ : Vec d) :
    variance v h (fun σ => inner ℝ θ (signedSum v σ)) ≤ ‖θ‖ ^ 2 := by
  by_cases hZ : partition v h = 0
  · simp [variance, expectation, probability, hZ]
  · exact main_bound v hv.1 h θ (lt_of_le_of_ne (partition_nonneg v hv.1 h) (Ne.symm hZ))

end IsingVectorBalancing.Subgaussian
end

theorem solution : type_of% @IsingVectorBalancing.Subgaussian.chk_lemma_7 := @IsingVectorBalancing.Subgaussian.chk_lemma_7
