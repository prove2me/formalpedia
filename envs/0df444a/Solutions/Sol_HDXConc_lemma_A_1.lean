-- Prove2me | solution 1 for HDXConc.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:38:09.003439+00:00
-- url     : https://prove2.me/submissions/74c5b4b1-84d7-44ff-a34e-a7f52bd8e1ec

import Mathlib

section
open Matrix
set_option autoImplicit false
namespace HDXConc.Dev.A1

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

local notation "E" => EuclideanSpace 𝕜 n

/-- quadratic form of a matrix -/
noncomputable def qf (H : Matrix n n 𝕜) (y : E) : ℝ :=
  RCLike.re (inner 𝕜 y (toEuclideanLin H y))

noncomputable def nf (y : E) : ℝ := ‖y‖ ^ 2

lemma qf_expand {H : Matrix n n 𝕜} (hH : H.IsHermitian) (y : E) :
    qf H y = ∑ i, hH.eigenvalues i * ‖inner 𝕜 (hH.eigenvectorBasis i) y‖ ^ 2 := by
  have hT := isSymmetric_toEuclideanLin_iff.mpr hH
  have hev : ∀ i, toEuclideanLin H (hH.eigenvectorBasis i)
      = (hH.eigenvalues i : 𝕜) • hH.eigenvectorBasis i := by
    intro i
    apply WithLp.ofLp_injective
    have h := hH.mulVec_eigenvectorBasis i
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)] at h
    exact h
  unfold qf
  rw [← (hH.eigenvectorBasis).sum_inner_mul_inner y (toEuclideanLin H y)]
  rw [show ∀ s : Finset n, ∀ f : n → 𝕜, RCLike.re (∑ i ∈ s, f i) = ∑ i ∈ s, RCLike.re (f i) from fun s f => map_sum RCLike.reLm f s]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← hT, hev]
  rw [inner_smul_left]
  rw [RCLike.conj_ofReal]
  have : inner 𝕜 y (hH.eigenvectorBasis i) = starRingEnd 𝕜 (inner 𝕜 (hH.eigenvectorBasis i) y) :=
    (inner_conj_symm _ _).symm
  rw [this]
  have h2 : starRingEnd 𝕜 (inner 𝕜 (hH.eigenvectorBasis i) y) *
      ((hH.eigenvalues i : 𝕜) * inner 𝕜 (hH.eigenvectorBasis i) y)
      = ((hH.eigenvalues i * ‖inner 𝕜 (hH.eigenvectorBasis i) y‖ ^ 2 : ℝ) : 𝕜) := by
    push_cast
    rw [mul_left_comm, RCLike.conj_mul]
  rw [h2]; simp

lemma nf_expand (b : OrthonormalBasis n 𝕜 E) (y : E) :
    nf y = ∑ i, ‖inner 𝕜 (b i) y‖ ^ 2 := by
  unfold nf; exact (b.sum_sq_norm_inner_right y).symm


lemma qf_bounds {H : Matrix n n 𝕜} (hH : H.IsHermitian) (lo hi : ℝ)
    (h : ∀ i, lo ≤ hH.eigenvalues i ∧ hH.eigenvalues i ≤ hi) (y : E) :
    lo * nf y ≤ qf H y ∧ qf H y ≤ hi * nf y := by
  rw [qf_expand hH, nf_expand hH.eigenvectorBasis, Finset.mul_sum, Finset.mul_sum]
  constructor
  · exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h i).1 (by positivity)
  · exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h i).2 (by positivity)

/-- span of the eigenvectors satisfying `p` -/
noncomputable def vspan {H : Matrix n n 𝕜} (hH : H.IsHermitian) (p : n → Prop) :
    Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range fun i : {i // p i} => (hH.eigenvectorBasis i : E))

lemma vspan_finrank {H : Matrix n n 𝕜} (hH : H.IsHermitian) (p : n → Prop) [DecidablePred p] :
    Module.finrank 𝕜 (vspan hH p) = Fintype.card {i // p i} := by
  unfold vspan
  exact finrank_span_eq_card
    ((hH.eigenvectorBasis.orthonormal.linearIndependent).comp _ Subtype.val_injective)

lemma vspan_inner {H : Matrix n n 𝕜} (hH : H.IsHermitian) (p : n → Prop) (y : E)
    (hy : y ∈ vspan hH p) (i : n) (hi : ¬ p i) : inner 𝕜 (hH.eigenvectorBasis i) y = 0 := by
  unfold vspan at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    have hne : i ≠ k.1 := fun h => hi (h ▸ k.2)
    exact hH.eigenvectorBasis.orthonormal.2 hne
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_right, hx, mul_zero]

lemma exists_sub_ge {H : Matrix n n 𝕜} (hH : H.IsHermitian) (j : Fin (Fintype.card n)) :
    ∃ V : Submodule 𝕜 E, Module.finrank 𝕜 V = j.1 + 1 ∧
      ∀ y ∈ V, hH.eigenvalues₀ j * nf y ≤ qf H y := by
  classical
  let σ : n ≃ Fin (Fintype.card n) := (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  have hσ : ∀ i, hH.eigenvalues i = hH.eigenvalues₀ (σ i) := fun i => rfl
  refine ⟨vspan hH (fun i => σ i ≤ j), ?_, ?_⟩
  · rw [vspan_finrank]
    rw [Fintype.card_congr (Equiv.subtypeEquiv σ (q := fun k => k ≤ j) (fun i => Iff.rfl))]
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun x : Fin (Fintype.card n) => x ≤ j) = Finset.Iic j := by
      ext; simp
    rw [this, Fin.card_Iic]
  · intro y hy
    rw [qf_expand hH, nf_expand hH.eigenvectorBasis, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : σ i ≤ j
    · rw [hσ]
      exact mul_le_mul_of_nonneg_right (hH.eigenvalues₀_antitone hi) (by positivity)
    · rw [vspan_inner hH _ y hy i hi]; simp

lemma exists_sub_le {H : Matrix n n 𝕜} (hH : H.IsHermitian) (j : Fin (Fintype.card n)) :
    ∃ V : Submodule 𝕜 E, Module.finrank 𝕜 V = Fintype.card n - j.1 ∧
      ∀ y ∈ V, qf H y ≤ hH.eigenvalues₀ j * nf y := by
  classical
  let σ : n ≃ Fin (Fintype.card n) := (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  have hσ : ∀ i, hH.eigenvalues i = hH.eigenvalues₀ (σ i) := fun i => rfl
  refine ⟨vspan hH (fun i => j ≤ σ i), ?_, ?_⟩
  · rw [vspan_finrank]
    rw [Fintype.card_congr (Equiv.subtypeEquiv σ (q := fun k => j ≤ k) (fun i => Iff.rfl))]
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun x : Fin (Fintype.card n) => j ≤ x) = Finset.Ici j := by
      ext; simp
    rw [this, Fin.card_Ici]
  · intro y hy
    rw [qf_expand hH, nf_expand hH.eigenvectorBasis, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : j ≤ σ i
    · rw [hσ]
      exact mul_le_mul_of_nonneg_right (hH.eigenvalues₀_antitone hi) (by positivity)
    · rw [vspan_inner hH _ y hy i hi]; simp


lemma inter_ge {H : Matrix n n 𝕜} (hH : H.IsHermitian) (j : Fin (Fintype.card n)) (c : ℝ)
    (V : Submodule 𝕜 E) (hV : j.1 + 1 ≤ Module.finrank 𝕜 V)
    (h : ∀ y ∈ V, c * nf y ≤ qf H y) : c ≤ hH.eigenvalues₀ j := by
  obtain ⟨W, hW, hW2⟩ := exists_sub_le hH j
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq V W
  have h2 : Module.finrank 𝕜 ↥(V ⊔ W) ≤ Fintype.card n := by
    have := Submodule.finrank_le (V ⊔ W)
    rwa [finrank_euclideanSpace] at this
  have h3 : 0 < Module.finrank 𝕜 ↥(V ⊓ W) := by
    have := j.2; omega
  obtain ⟨⟨y, hy⟩, hne⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h3
  have hy0 : y ≠ 0 := fun h0 => hne (Subtype.ext h0)
  have hpos : 0 < nf y := by unfold nf; positivity
  have a1 := h y hy.1
  have a2 := hW2 y hy.2
  exact le_of_mul_le_mul_right (a1.trans a2) hpos

lemma inter_le {H : Matrix n n 𝕜} (hH : H.IsHermitian) (j : Fin (Fintype.card n)) (c : ℝ)
    (W : Submodule 𝕜 E) (hW : Fintype.card n - j.1 ≤ Module.finrank 𝕜 W)
    (h : ∀ y ∈ W, qf H y ≤ c * nf y) : hH.eigenvalues₀ j ≤ c := by
  obtain ⟨V, hV, hV2⟩ := exists_sub_ge hH j
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq V W
  have h2 : Module.finrank 𝕜 ↥(V ⊔ W) ≤ Fintype.card n := by
    have := Submodule.finrank_le (V ⊔ W)
    rwa [finrank_euclideanSpace] at this
  have h3 : 0 < Module.finrank 𝕜 ↥(V ⊓ W) := by
    have := j.2; omega
  obtain ⟨⟨y, hy⟩, hne⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h3
  have hy0 : y ≠ 0 := fun h0 => hne (Subtype.ext h0)
  have hpos : 0 < nf y := by unfold nf; positivity
  have a1 := hV2 y hy.1
  have a2 := h y hy.2
  exact le_of_mul_le_mul_right (a1.trans a2) hpos

lemma toEuclideanLin_mul' (X Y : Matrix n n 𝕜) (v : E) :
    toEuclideanLin (X * Y) v = toEuclideanLin X (toEuclideanLin Y v) := by
  apply WithLp.ofLp_injective
  simp only [ofLp_toEuclideanLin_apply, mulVec_mulVec]

lemma qf_conj (A C : Matrix n n 𝕜) (y : E) :
    qf (Cᴴ * A * C) y = qf A (toEuclideanLin C y) := by
  unfold qf
  rw [toEuclideanLin_mul', toEuclideanLin_mul', toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_inner_right]

lemma qf_one (z : E) : qf (1 : Matrix n n 𝕜) z = nf z := by
  unfold qf nf
  have : toEuclideanLin (1 : Matrix n n 𝕜) z = z := by
    apply WithLp.ofLp_injective; simp
  rw [this, inner_self_eq_norm_sq_to_K]
  norm_cast

lemma nf_conj (C : Matrix n n 𝕜) (y : E) : nf (toEuclideanLin C y) = qf (Cᴴ * C) y := by
  have := qf_conj (1 : Matrix n n 𝕜) C y
  rw [Matrix.mul_one, qf_one] at this
  exact this.symm


noncomputable def lequiv (C : Matrix n n 𝕜) (hC : C.det ≠ 0) : E ≃ₗ[𝕜] E :=
  LinearEquiv.ofInjectiveEndo (toEuclideanLin C) (by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply WithLp.ofLp_injective
    have : C *ᵥ y.ofLp = 0 := by
      have := congrArg WithLp.ofLp hy
      simpa [ofLp_toEuclideanLin_apply] using this
    simpa using Matrix.eq_zero_of_mulVec_eq_zero hC this)

lemma lower {A : Matrix n n 𝕜} (hA : A.IsHermitian) (C : Matrix n n 𝕜) (hC : C.det ≠ 0)
    (hB : (Cᴴ * A * C).IsHermitian) (j : Fin (Fintype.card n)) (c : ℝ)
    (hc : ∀ y : E, c * nf y ≤ hA.eigenvalues₀ j * nf (toEuclideanLin C y)) :
    c ≤ hB.eigenvalues₀ j := by
  obtain ⟨V, hV, hV2⟩ := exists_sub_ge hA j
  refine inter_ge hB j c (V.comap (lequiv C hC : E →ₗ[𝕜] E)) ?_ ?_
  · have : V.comap (lequiv C hC : E →ₗ[𝕜] E) = V.map ((lequiv C hC).symm : E →ₗ[𝕜] E) :=
      Submodule.comap_equiv_eq_map_symm _ _
    rw [this, LinearEquiv.finrank_map_eq, hV]
  · intro y hy
    have := hV2 _ hy
    rw [qf_conj]
    exact (hc y).trans this

lemma upper {A : Matrix n n 𝕜} (hA : A.IsHermitian) (C : Matrix n n 𝕜) (hC : C.det ≠ 0)
    (hB : (Cᴴ * A * C).IsHermitian) (j : Fin (Fintype.card n)) (c : ℝ)
    (hc : ∀ y : E, hA.eigenvalues₀ j * nf (toEuclideanLin C y) ≤ c * nf y) :
    hB.eigenvalues₀ j ≤ c := by
  obtain ⟨V, hV, hV2⟩ := exists_sub_le hA j
  refine inter_le hB j c (V.comap (lequiv C hC : E →ₗ[𝕜] E)) ?_ ?_
  · have : V.comap (lequiv C hC : E →ₗ[𝕜] E) = V.map ((lequiv C hC).symm : E →ₗ[𝕜] E) :=
      Submodule.comap_equiv_eq_map_symm _ _
    rw [this, LinearEquiv.finrank_map_eq, hV]
  · intro y hy
    have := hV2 _ hy
    rw [qf_conj]
    exact this.trans (hc y)

lemma main {A : Matrix n n 𝕜} (hA : A.IsHermitian) (C : Matrix n n 𝕜) (hC : C.det ≠ 0)
    (hB : (Cᴴ * A * C).IsHermitian) (hG : (Cᴴ * C).IsHermitian) (j : Fin (Fintype.card n)) :
    ∃ θ : ℝ, ⨅ i, hG.eigenvalues₀ i ≤ θ ∧ θ ≤ ⨆ i, hG.eigenvalues₀ i ∧
      hB.eigenvalues₀ j = θ * hA.eigenvalues₀ j := by
  set m := ⨅ i, hG.eigenvalues₀ i with hm
  set M := ⨆ i, hG.eigenvalues₀ i with hM
  have hbd : ∀ i : n, m ≤ hG.eigenvalues i ∧ hG.eigenvalues i ≤ M := fun i =>
    ⟨ciInf_le (Set.finite_range _).bddBelow _, by
      show hG.eigenvalues₀ _ ≤ M
      exact le_ciSup (Set.finite_range _).bddAbove _⟩
  have hg : ∀ y : E, m * nf y ≤ nf (toEuclideanLin C y) ∧ nf (toEuclideanLin C y) ≤ M * nf y := by
    intro y
    rw [nf_conj]
    exact qf_bounds hG m M hbd y
  have hmM : m ≤ M := (ciInf_le (Set.finite_range _).bddBelow j).trans
    (le_ciSup (Set.finite_range _).bddAbove j)
  set a := hA.eigenvalues₀ j with ha
  set b := hB.eigenvalues₀ j with hb
  have hnf : ∀ y : E, 0 ≤ nf y := fun y => by unfold nf; positivity
  by_cases ha0 : 0 ≤ a
  · have h1 : m * a ≤ b := lower hA C hC hB j (m * a) fun y => by
      have := mul_le_mul_of_nonneg_left (hg y).1 ha0
      nlinarith
    have h2 : b ≤ M * a := upper hA C hC hB j (M * a) fun y => by
      have := mul_le_mul_of_nonneg_left (hg y).2 ha0
      nlinarith
    rcases ha0.eq_or_lt with h0 | hpos
    · refine ⟨m, le_refl _, hmM, ?_⟩
      rw [← h0] at h1 h2 ⊢
      linarith
    · refine ⟨b / a, ?_, ?_, ?_⟩
      · rw [le_div_iff₀ hpos]; exact h1
      · rw [div_le_iff₀ hpos]; exact h2
      · field_simp
  · rw [not_le] at ha0
    have h1 : M * a ≤ b := lower hA C hC hB j (M * a) fun y => by
      have := mul_le_mul_of_nonpos_left (hg y).2 ha0.le
      nlinarith
    have h2 : b ≤ m * a := upper hA C hC hB j (m * a) fun y => by
      have := mul_le_mul_of_nonpos_left (hg y).1 ha0.le
      nlinarith
    refine ⟨b / a, ?_, ?_, ?_⟩
    · rw [le_div_iff_of_neg ha0]; exact h2
    · rw [div_le_iff_of_neg ha0]; exact h1
    · have := ha0.ne
      field_simp

end HDXConc.Dev.A1

namespace HDXConc
open HDXConc.Dev.A1 in
theorem chk_lemma_A_1 {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
    (A C : Matrix n n 𝕜) (hA : A.IsHermitian) (hC : C.det ≠ 0) (j : Fin (Fintype.card n)) :
    ∃ θ : ℝ,
      ⨅ i, (isHermitian_conjTranspose_mul_self C).eigenvalues₀ i ≤ θ ∧
      θ ≤ ⨆ i, (isHermitian_conjTranspose_mul_self C).eigenvalues₀ i ∧
      (isHermitian_conjTranspose_mul_mul C hA).eigenvalues₀ j = θ * hA.eigenvalues₀ j :=
  main hA C hC _ _ j

end HDXConc
end

theorem solution : type_of% @HDXConc.chk_lemma_A_1 := @HDXConc.chk_lemma_A_1
