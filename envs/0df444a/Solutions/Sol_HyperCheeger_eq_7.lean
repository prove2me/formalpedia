-- Prove2me | solution 1 for HyperCheeger.eq_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T13:05:48.572892+00:00
-- url     : https://prove2.me/submissions/8362303e-ead3-431f-903e-bbbd99a2de24

import Mathlib
import Definitions.Def_HyperCheeger_Hypergraph_nu2
import Theorems.Thm_HyperCheeger_eq_5

section
set_option autoImplicit false

open scoped Matrix

namespace HyperCheeger.Dev.Eq7

open HyperCheeger HyperCheeger.Hypergraph Matrix

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem degree_nonneg (H : Hypergraph V) (u : V) : 0 ≤ H.degree u :=
  Finset.sum_nonneg fun e he => H.w_nonneg e (Finset.mem_filter.1 he).1

omit [Fintype V] in
theorem w_le_degree (H : Hypergraph V) {e : Finset V} (he : e ∈ H.edges) {u : V} (hu : u ∈ e) :
    H.w e ≤ H.degree u := by
  unfold Hypergraph.degree
  exact Finset.single_le_sum (f := H.w) (fun e he => H.w_nonneg e (Finset.mem_filter.1 he).1)
    (Finset.mem_filter.2 ⟨he, hu⟩)

theorem lap_quad_nonneg (H : Hypergraph V) (x : V → ℝ) : 0 ≤ x ⬝ᵥ (H.lap *ᵥ x) := by
  rw [HyperCheeger.eq_5]
  refine Finset.sum_nonneg fun e he => ?_
  rcases Finset.eq_empty_or_nonempty e with rfl | hne
  · simp
  · have h2 : (2 : ℝ) ≤ e.card := by
      have h1 := H.card_ne_one e he
      have := hne.card_pos
      exact_mod_cast (by omega : 2 ≤ e.card)
    apply mul_nonneg
    · exact div_nonneg (H.w_nonneg e he) (by linarith)
    · exact mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem lap_quad_eq_zero_of (H : Hypergraph V) (x : V → ℝ)
    (hx : ∀ e ∈ H.edges, 0 < H.w e → ∀ u ∈ e, ∀ v ∈ e, x u = x v) :
    x ⬝ᵥ (H.lap *ᵥ x) = 0 := by
  rw [HyperCheeger.eq_5]
  refine Finset.sum_eq_zero fun e he => ?_
  rcases (H.w_nonneg e he).eq_or_lt with h | h
  · rw [← h]; simp
  · have : ∑ u ∈ e, ∑ v ∈ e, (x u - x v) ^ 2 = 0 :=
      Finset.sum_eq_zero fun u hu => Finset.sum_eq_zero fun v hv => by
        rw [hx e he h u hu v hv]; ring
    rw [this]; ring

omit [Fintype V] in
theorem adj_symm (H : Hypergraph V) (u v : V) : H.adj u v = H.adj v u := by
  simp only [Hypergraph.adj, Matrix.of_apply]
  rw [Finset.pair_comm u v]
  by_cases h : u = v
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

omit [Fintype V] in
theorem lap_transpose (H : Hypergraph V) : H.lapᵀ = H.lap := by
  ext u v
  simp only [Hypergraph.lap, Hypergraph.degMat, transpose_apply, Matrix.sub_apply, diagonal_apply]
  rw [adj_symm H v u]
  by_cases h : u = v
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

omit [Fintype V] in
theorem lap_isHermitian (H : Hypergraph V) : H.lap.IsHermitian := by
  show H.lapᴴ = H.lap
  rw [conjTranspose_eq_transpose_of_trivial, lap_transpose]

theorem lap_posSemidef (H : Hypergraph V) : H.lap.PosSemidef :=
  PosSemidef.of_dotProduct_mulVec_nonneg (lap_isHermitian H) fun x => by
    simpa using lap_quad_nonneg H x

theorem normLap_transpose (H : Hypergraph V) : H.normLapᵀ = H.normLap := by
  simp only [Hypergraph.normLap, Hypergraph.degInvSqrt, transpose_mul, diagonal_transpose,
    lap_transpose, Matrix.mul_assoc]

theorem normLap_isHermitian (H : Hypergraph V) : H.normLap.IsHermitian := by
  show H.normLapᴴ = H.normLap
  rw [conjTranspose_eq_transpose_of_trivial, normLap_transpose]

theorem diag_dot (f x z : V → ℝ) :
    x ⬝ᵥ (diagonal f *ᵥ z) = (diagonal f *ᵥ x) ⬝ᵥ z := by
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem normLap_mulVec (H : Hypergraph V) (x : V → ℝ) :
    H.normLap *ᵥ x = H.degInvSqrt *ᵥ (H.lap *ᵥ (H.degInvSqrt *ᵥ x)) := by
  simp only [Hypergraph.normLap, mulVec_mulVec, Matrix.mul_assoc]

theorem normLap_quad (H : Hypergraph V) (x : V → ℝ) :
    x ⬝ᵥ (H.normLap *ᵥ x) = (H.degInvSqrt *ᵥ x) ⬝ᵥ (H.lap *ᵥ (H.degInvSqrt *ᵥ x)) := by
  rw [normLap_mulVec, Hypergraph.degInvSqrt, diag_dot]

theorem normLap_quad_nonneg (H : Hypergraph V) (x : V → ℝ) : 0 ≤ x ⬝ᵥ (H.normLap *ᵥ x) := by
  rw [normLap_quad]; exact lap_quad_nonneg H _

theorem normLap_posSemidef (H : Hypergraph V) : H.normLap.PosSemidef :=
  PosSemidef.of_dotProduct_mulVec_nonneg (normLap_isHermitian H) fun x => by
    simpa using normLap_quad_nonneg H x

theorem normLap_sqrt (H : Hypergraph V) :
    H.normLap *ᵥ (fun u => Real.sqrt (H.degree u)) = 0 := by
  have hz : H.lap *ᵥ (H.degInvSqrt *ᵥ (fun u => Real.sqrt (H.degree u))) = 0 := by
    refine ((lap_posSemidef H).dotProduct_mulVec_zero_iff _).1 ?_
    rw [star_trivial]
    refine lap_quad_eq_zero_of H _ fun e he hw u hu v hv => ?_
    have hdu : 0 < Real.sqrt (H.degree u) := Real.sqrt_pos.2 (hw.trans_le (w_le_degree H he hu))
    have hdv : 0 < Real.sqrt (H.degree v) := Real.sqrt_pos.2 (hw.trans_le (w_le_degree H he hv))
    simp only [Hypergraph.degInvSqrt, mulVec_diagonal]
    rw [inv_mul_cancel₀ hdu.ne', inv_mul_cancel₀ hdv.ne']
  rw [normLap_mulVec, hz, mulVec_zero]

/-- The abstract Courant–Fischer step, in eigen-coordinates. -/
theorem abstract_isLeast (lam σ : V → ℝ) (i₁ i₂ : V) (hne : i₁ ≠ i₂) (hnn : ∀ k, 0 ≤ lam k)
    (hge : ∀ k, k ≠ i₁ → lam i₂ ≤ lam k) (hle : lam i₁ ≤ lam i₂)
    (hσ : ∑ k, lam k * σ k ^ 2 = 0) (hσ0 : σ = 0 → lam i₂ = 0) :
    IsLeast {r : ℝ | ∃ c : V → ℝ, c ≠ 0 ∧ c ⬝ᵥ σ = 0 ∧
      r = (∑ k, lam k * c k ^ 2) / (c ⬝ᵥ c)} (lam i₂) := by
  have hsum_nonneg : ∀ c : V → ℝ, 0 ≤ ∑ k, lam k * c k ^ 2 := fun c =>
    Finset.sum_nonneg fun k _ => mul_nonneg (hnn k) (sq_nonneg _)
  have hdot_nonneg : ∀ c : V → ℝ, 0 ≤ c ⬝ᵥ c := fun c =>
    Finset.sum_nonneg fun k _ => mul_self_nonneg (c k)
  rcases le_or_gt (lam i₂) 0 with hl | hl
  · have h2 : lam i₂ = 0 := le_antisymm hl (hnn _)
    have h1 : lam i₁ = 0 := le_antisymm (hle.trans hl) (hnn _)
    constructor
    · by_cases hz : σ i₁ = 0 ∧ σ i₂ = 0
      · refine ⟨Pi.single i₂ 1, ?_, ?_, ?_⟩
        · intro h; have := congrFun h i₂; simp at this
        · rw [single_one_dotProduct, hz.2]
        · rw [h2]
          have : ∑ k, lam k * Pi.single (M := fun _ => ℝ) i₂ 1 k ^ 2 = 0 := by
            rw [Finset.sum_eq_single i₂]
            · simp [h2]
            · intro k _ hk; simp [hk]
            · simp
          rw [this, zero_div]
      · set c : V → ℝ := fun k => if k = i₂ then σ i₁ else if k = i₁ then -σ i₂ else 0 with hc
        have hc2 : c i₂ = σ i₁ := by simp [hc]
        have hc1 : c i₁ = -σ i₂ := by simp [hc, hne]
        have hco : ∀ k, k ≠ i₂ ∧ k ≠ i₁ → c k = 0 := fun k hk => by simp [hc, hk.1, hk.2]
        refine ⟨c, ?_, ?_, ?_⟩
        · intro h
          apply hz
          have a := congrFun h i₂
          have b := congrFun h i₁
          rw [hc2] at a; rw [hc1] at b
          simp only [Pi.zero_apply] at a b
          exact ⟨a, by linarith⟩
        · rw [dotProduct, Fintype.sum_eq_add i₂ i₁ (Ne.symm hne)
            (fun k hk => by rw [hco k hk, zero_mul]), hc2, hc1]
          ring
        · rw [Fintype.sum_eq_add i₂ i₁ (Ne.symm hne)
            (fun k hk => by rw [hco k hk]; ring), h1, h2]
          simp
    · rintro r ⟨c, -, -, rfl⟩
      rw [h2]
      exact div_nonneg (hsum_nonneg c) (hdot_nonneg c)
  · have hpos : ∀ k, k ≠ i₁ → 0 < lam k := fun k hk => hl.trans_le (hge k hk)
    have hσk : ∀ k, k ≠ i₁ → σ k = 0 := by
      intro k hk
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_nonneg (hnn j) (sq_nonneg (σ j)))).1 hσ k (Finset.mem_univ _)
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (hpos k hk).ne'
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
    have hσ1 : σ i₁ ≠ 0 := by
      intro h
      have : σ = 0 := funext fun k => by
        by_cases hk : k = i₁
        · subst hk; exact h
        · exact hσk k hk
      exact hl.ne' (hσ0 this)
    constructor
    · refine ⟨Pi.single i₂ 1, ?_, ?_, ?_⟩
      · intro h; have := congrFun h i₂; simp at this
      · rw [single_one_dotProduct, hσk i₂ (Ne.symm hne)]
      · have : ∑ k, lam k * Pi.single (M := fun _ => ℝ) i₂ 1 k ^ 2 = lam i₂ := by
          rw [Finset.sum_eq_single i₂]
          · simp
          · intro k _ hk; simp [hk]
          · simp
        rw [this, single_one_dotProduct]
        simp
    · rintro r ⟨c, hc, hcσ, rfl⟩
      have hc1 : c i₁ = 0 := by
        have : c ⬝ᵥ σ = c i₁ * σ i₁ := by
          rw [dotProduct, Finset.sum_eq_single i₁]
          · intro k _ hk; rw [hσk k hk, mul_zero]
          · simp
        rw [this] at hcσ
        exact (mul_eq_zero.1 hcσ).resolve_right hσ1
      have hcc : 0 < c ⬝ᵥ c := by
        obtain ⟨k, hk⟩ : ∃ k, c k ≠ 0 := by
          by_contra h; push Not at h; exact hc (funext h)
        exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
          ⟨k, Finset.mem_univ _, mul_self_pos.2 hk⟩
      rw [le_div_iff₀ hcc, dotProduct, Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      by_cases hk : k = i₁
      · subst hk; rw [hc1]; simp
      · have := hge k hk
        nlinarith [mul_self_nonneg (c k)]

theorem transfer (H : Hypergraph V) (hpos : ∀ u, 0 < Real.sqrt (H.degree u)) (y : V → ℝ) :
    ((fun u => Real.sqrt (H.degree u) * y u) = 0 ↔ y = 0) ∧
    (fun u => Real.sqrt (H.degree u) * y u) ⬝ᵥ (fun u => Real.sqrt (H.degree u)) =
      y ⬝ᵥ H.degree ∧
    ((fun u => Real.sqrt (H.degree u) * y u) ⬝ᵥ
        (H.normLap *ᵥ (fun u => Real.sqrt (H.degree u) * y u))) /
      ((fun u => Real.sqrt (H.degree u) * y u) ⬝ᵥ (fun u => Real.sqrt (H.degree u) * y u)) =
      (y ⬝ᵥ (H.lap *ᵥ y)) / (y ⬝ᵥ (H.degMat *ᵥ y)) := by
  have hD : H.degInvSqrt *ᵥ (fun u => Real.sqrt (H.degree u) * y u) = y := funext fun u => by
    simp only [Hypergraph.degInvSqrt, mulVec_diagonal]
    rw [← mul_assoc, inv_mul_cancel₀ (hpos u).ne', one_mul]
  refine ⟨⟨fun h => funext fun u => ?_, fun h => by subst h; funext u; simp⟩, ?_, ?_⟩
  · have := congrFun h u
    simp only [Pi.zero_apply, mul_eq_zero] at this
    exact this.resolve_left (hpos u).ne'
  · simp only [dotProduct]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [show Real.sqrt (H.degree u) * y u * Real.sqrt (H.degree u) =
      y u * (Real.sqrt (H.degree u) * Real.sqrt (H.degree u)) by ring,
      Real.mul_self_sqrt (degree_nonneg H u)]
  · rw [normLap_quad, hD]
    congr 1
    simp only [dotProduct, Hypergraph.degMat, mulVec_diagonal]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [show Real.sqrt (H.degree u) * y u * (Real.sqrt (H.degree u) * y u) =
      y u * ((Real.sqrt (H.degree u) * Real.sqrt (H.degree u)) * y u) by ring,
      Real.mul_self_sqrt (degree_nonneg H u)]

end HyperCheeger.Dev.Eq7

namespace HyperCheeger

open HyperCheeger.Dev.Eq7 in
theorem chk_eq_7 {V : Type} [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V) (H : Hypergraph V) :
    H.normLap *ᵥ (fun u => Real.sqrt (H.degree u)) = 0 ∧
    IsLeast {r : ℝ | ∃ x : V → ℝ, x ≠ 0 ∧ x ⬝ᵥ (fun u => Real.sqrt (H.degree u)) = 0 ∧
        r = (x ⬝ᵥ (H.normLap *ᵥ x)) / (x ⬝ᵥ x)} H.nu2 ∧
    IsLeast {r : ℝ | ∃ y : V → ℝ, y ≠ 0 ∧ y ⬝ᵥ H.degree = 0 ∧
        r = (y ⬝ᵥ (H.lap *ᵥ y)) / (y ⬝ᵥ (H.degMat *ᵥ y))} H.nu2 := by
  have hN := normLap_isHermitian H
  have hPSD := normLap_posSemidef H
  have hker := normLap_sqrt H
  set U : Matrix V V ℝ := (hN.eigenvectorUnitary : Matrix V V ℝ) with hU
  set lam : V → ℝ := hN.eigenvalues with hlam
  have hspec : H.normLap = U * Matrix.diagonal lam * Uᵀ := by
    conv_lhs => rw [hN.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, hU, hlam]
  have hUU : Uᵀ * U = 1 := by
    have := Unitary.coe_star_mul_self hN.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial, hU] using this
  have hUU' : U * Uᵀ = 1 := by
    have := Unitary.coe_mul_star_self hN.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial, hU] using this
  have hinv1 : ∀ x : V → ℝ, U *ᵥ (Uᵀ *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, hUU', Matrix.one_mulVec]
  have hinv2 : ∀ c : V → ℝ, Uᵀ *ᵥ (U *ᵥ c) = c := fun c => by
    rw [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
  have hdot : ∀ x y : V → ℝ, (Uᵀ *ᵥ x) ⬝ᵥ (Uᵀ *ᵥ y) = x ⬝ᵥ y := fun x y => by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hinv1]
  have hquad : ∀ x : V → ℝ, x ⬝ᵥ (H.normLap *ᵥ x) = ∑ k, lam k * (Uᵀ *ᵥ x) k ^ 2 := fun x => by
    rw [hspec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    simp only [dotProduct, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hset1 : {r : ℝ | ∃ x : V → ℝ, x ≠ 0 ∧ x ⬝ᵥ (fun u => Real.sqrt (H.degree u)) = 0 ∧
        r = (x ⬝ᵥ (H.normLap *ᵥ x)) / (x ⬝ᵥ x)} =
      {r : ℝ | ∃ c : V → ℝ, c ≠ 0 ∧ c ⬝ᵥ (Uᵀ *ᵥ (fun u => Real.sqrt (H.degree u))) = 0 ∧
        r = (∑ k, lam k * c k ^ 2) / (c ⬝ᵥ c)} := by
    ext r
    constructor
    · rintro ⟨x, hx, hxs, rfl⟩
      refine ⟨Uᵀ *ᵥ x, fun h => hx ?_, by rw [hdot]; exact hxs, by rw [hquad, hdot]⟩
      rw [← hinv1 x, h, Matrix.mulVec_zero]
    · rintro ⟨c, hc, hcs, rfl⟩
      refine ⟨U *ᵥ c, fun h => hc ?_, ?_, ?_⟩
      · rw [← hinv2 c, h, Matrix.mulVec_zero]
      · rw [← hdot, hinv2]; exact hcs
      · rw [hquad, ← hdot (U *ᵥ c) (U *ᵥ c), hinv2]
  -- indices
  have hn2 : Fintype.card V - 2 < Fintype.card V := by omega
  have hn1 : Fintype.card V - 1 < Fintype.card V := by omega
  set e : Fin (Fintype.card V) ≃ V := Fintype.equivOfCardEq (Fintype.card_fin _) with he
  have hlam_eq : ∀ j : Fin (Fintype.card V), lam (e j) = hN.eigenvalues₀ j := fun j => by
    simp only [hlam, Matrix.IsHermitian.eigenvalues, he, Equiv.symm_apply_apply]
  set i₂ := e ⟨Fintype.card V - 2, hn2⟩ with hi₂
  set i₁ := e ⟨Fintype.card V - 1, hn1⟩ with hi₁
  have hnu : H.nu2 = lam i₂ := by
    rw [hi₂, hlam_eq]
    unfold Hypergraph.nu2 AlonMilman.PropertyT.lambda1
    rw [dif_pos ⟨hN, hV⟩]
  have hne : i₁ ≠ i₂ := by
    intro h
    have := congrArg Fin.val (e.injective h)
    simp only at this
    omega
  have hge : ∀ k, k ≠ i₁ → lam i₂ ≤ lam k := by
    intro k hk
    obtain ⟨j, rfl⟩ := e.surjective k
    rw [hi₂, hlam_eq, hlam_eq]
    apply hN.eigenvalues₀_antitone
    have hj : (j : ℕ) ≠ Fintype.card V - 1 := fun h => hk (by rw [hi₁]; congr 1; exact Fin.ext h)
    have := j.2
    rw [Fin.le_def]
    simp only
    omega
  have hle : lam i₁ ≤ lam i₂ := by
    rw [hi₁, hi₂, hlam_eq, hlam_eq]
    apply hN.eigenvalues₀_antitone
    rw [Fin.le_def]
    simp only
    omega
  have hnn : ∀ k, 0 ≤ lam k := fun k => hPSD.eigenvalues_nonneg k
  have hσ : ∑ k, lam k * (Uᵀ *ᵥ (fun u => Real.sqrt (H.degree u))) k ^ 2 = 0 := by
    rw [← hquad, hker, dotProduct_zero]
  have hσ0 : Uᵀ *ᵥ (fun u => Real.sqrt (H.degree u)) = 0 → lam i₂ = 0 := by
    intro h
    have hs0 : (fun u => Real.sqrt (H.degree u)) = 0 := by rw [← hinv1 (fun u => _), h, Matrix.mulVec_zero]
    have hDis : H.degInvSqrt = 0 := by
      ext u v
      simp only [Hypergraph.degInvSqrt, Matrix.diagonal_apply, Matrix.zero_apply]
      have : Real.sqrt (H.degree u) = 0 := congrFun hs0 u
      split_ifs <;> simp [this]
    have hN0 : H.normLap = 0 := by simp [Hypergraph.normLap, hDis]
    have := hN.eigenvalues_eq_zero_iff.2 hN0
    rw [hlam, this]
    rfl
  have hL1 : IsLeast {r : ℝ | ∃ x : V → ℝ, x ≠ 0 ∧ x ⬝ᵥ (fun u => Real.sqrt (H.degree u)) = 0 ∧
        r = (x ⬝ᵥ (H.normLap *ᵥ x)) / (x ⬝ᵥ x)} H.nu2 := by
    rw [hset1, hnu]
    exact abstract_isLeast lam _ i₁ i₂ hne hnn hge hle hσ hσ0
  refine ⟨hker, hL1, ?_⟩
  by_cases h0 : ∃ u₀, H.degree u₀ = 0
  · obtain ⟨u₀, hu₀⟩ := h0
    have hnu0 : H.nu2 = 0 := by
      apply le_antisymm
      · apply hL1.2
        refine ⟨Pi.single u₀ 1, ?_, ?_, ?_⟩
        · intro h; have := congrFun h u₀; simp at this
        · rw [single_one_dotProduct]; simp [hu₀]
        · rw [normLap_quad]
          have : H.degInvSqrt *ᵥ Pi.single u₀ 1 = 0 := by
            funext u
            simp only [Hypergraph.degInvSqrt, Matrix.mulVec_diagonal, Pi.zero_apply]
            by_cases hu : u = u₀
            · subst hu; simp [hu₀]
            · simp [hu]
          rw [this]; simp
      · obtain ⟨x, -, -, hx⟩ := hL1.1
        rw [hx]
        exact div_nonneg (normLap_quad_nonneg H x)
          (Finset.sum_nonneg fun k _ => mul_self_nonneg (x k))
    rw [hnu0]
    constructor
    · refine ⟨Pi.single u₀ 1, ?_, ?_, ?_⟩
      · intro h; have := congrFun h u₀; simp at this
      · rw [single_one_dotProduct, hu₀]
      · have : Pi.single u₀ 1 ⬝ᵥ (H.degMat *ᵥ Pi.single u₀ (1 : ℝ)) = 0 := by
          rw [single_one_dotProduct]; simp [Hypergraph.degMat, Matrix.mulVec_diagonal, hu₀]
        rw [this, div_zero]
    · rintro r ⟨y, -, -, rfl⟩
      apply div_nonneg (lap_quad_nonneg H y)
      simp only [Hypergraph.degMat, dotProduct, Matrix.mulVec_diagonal]
      exact Finset.sum_nonneg fun k _ => by
        nlinarith [mul_nonneg (degree_nonneg H k) (mul_self_nonneg (y k))]
  · push Not at h0
    have hpos : ∀ u, 0 < Real.sqrt (H.degree u) := fun u =>
      Real.sqrt_pos.2 (lt_of_le_of_ne (degree_nonneg H u) (h0 u).symm)
    have hset : {r : ℝ | ∃ y : V → ℝ, y ≠ 0 ∧ y ⬝ᵥ H.degree = 0 ∧
          r = (y ⬝ᵥ (H.lap *ᵥ y)) / (y ⬝ᵥ (H.degMat *ᵥ y))} =
        {r : ℝ | ∃ x : V → ℝ, x ≠ 0 ∧ x ⬝ᵥ (fun u => Real.sqrt (H.degree u)) = 0 ∧
          r = (x ⬝ᵥ (H.normLap *ᵥ x)) / (x ⬝ᵥ x)} := by
      ext r
      constructor
      · rintro ⟨y, hy, hyd, rfl⟩
        obtain ⟨h1, h2, h3⟩ := transfer H hpos y
        exact ⟨_, fun h => hy (h1.1 h), by rw [h2]; exact hyd, h3.symm⟩
      · rintro ⟨x, hx, hxs, rfl⟩
        have hxy : x = fun u => Real.sqrt (H.degree u) * ((Real.sqrt (H.degree u))⁻¹ * x u) :=
          funext fun u => by rw [← mul_assoc, mul_inv_cancel₀ (hpos u).ne', one_mul]
        obtain ⟨h1, h2, h3⟩ := transfer H hpos (fun u => (Real.sqrt (H.degree u))⁻¹ * x u)
        rw [← hxy] at h1 h2 h3
        exact ⟨_, fun h => hx (h1.2 h), by rw [← h2]; exact hxs, h3⟩
    rw [hset]
    exact hL1

end HyperCheeger
end

theorem solution : type_of% @HyperCheeger.chk_eq_7 := @HyperCheeger.chk_eq_7
