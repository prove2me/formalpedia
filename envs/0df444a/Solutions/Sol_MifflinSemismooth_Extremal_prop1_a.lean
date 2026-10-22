-- Prove2me | solution 1 for MifflinSemismooth.Extremal.prop1_a
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:52:49.220185+00:00
-- url     : https://prove2.me/submissions/a999825e-91fc-4ac1-bbeb-8196b5ad5c3b

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_genDirDeriv
import Definitions.Def_MifflinSemismooth_Extremal_Basic

set_option autoImplicit false
open Filter Topology ClarkeGradients.Shared MifflinSemismooth.Extremal

namespace ClarkeCore

variable {n : ℕ}


/-- the filter along which the limsup defining `genDirDeriv` is taken -/
noncomputable abbrev LF (n : ℕ) : Filter (EuclideanSpace ℝ (Fin n) × ℝ) :=
  𝓝 (0 : EuclideanSpace ℝ (Fin n)) ×ˢ 𝓝[>] (0 : ℝ)

noncomputable def qf (F : (EuclideanSpace ℝ (Fin n)) → ℝ) (x d : (EuclideanSpace ℝ (Fin n))) : (EuclideanSpace ℝ (Fin n)) × ℝ → ℝ :=
  fun p => (F (x + p.1 + p.2 • d) - F (x + p.1)) / p.2

lemma genDirDeriv_eq (F : (EuclideanSpace ℝ (Fin n)) → ℝ) (x d : (EuclideanSpace ℝ (Fin n))) :
    genDirDeriv F x d = limsup (qf F x d) (LF n) := rfl

lemma snd_pos : ∀ᶠ p in LF n, 0 < p.2 := by
  have : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t := self_mem_nhdsWithin
  exact tendsto_snd.eventually this

lemma bound_ev (F : (EuclideanSpace ℝ (Fin n)) → ℝ) (B : Set (EuclideanSpace ℝ (Fin n))) (hB : IsOpen B) (K : NNReal) (hFB : LipschitzOnWith K F B)
    (x : (EuclideanSpace ℝ (Fin n))) (hx : x ∈ B) (d : (EuclideanSpace ℝ (Fin n))) : ∀ᶠ p in LF n, |qf F x d p| ≤ K * ‖d‖ := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hB x hx
  have hpos : 0 < r / (2 * (‖d‖ + 1)) := by positivity
  have h1 : ∀ᶠ p in LF n, p.1 ∈ Metric.ball (0 : (EuclideanSpace ℝ (Fin n))) (r / 2) :=
    tendsto_fst.eventually (Metric.ball_mem_nhds _ (by positivity))
  have h2 : ∀ᶠ p in LF n, p.2 ∈ Set.Ioo (0:ℝ) (r / (2 * (‖d‖ + 1))) :=
    tendsto_snd.eventually (Ioo_mem_nhdsGT hpos)
  filter_upwards [h1, h2] with p hp1 hp2
  have hn1 : ‖p.1‖ < r / 2 := by simpa using hp1
  obtain ⟨hp2a, hp2b⟩ := hp2
  have hd : p.2 * ‖d‖ < r / 2 := by
    have : p.2 * ‖d‖ ≤ r / (2 * (‖d‖ + 1)) * ‖d‖ :=
      mul_le_mul_of_nonneg_right hp2b.le (norm_nonneg _)
    have h3 : r / (2 * (‖d‖ + 1)) * ‖d‖ < r / 2 := by
      rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [norm_nonneg d]
    linarith
  have ha : x + p.1 ∈ B := hball (by simp [Metric.mem_ball, dist_eq_norm]; linarith)
  have hb : x + p.1 + p.2 • d ∈ B := hball (by
    simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    calc ‖x + p.1 + p.2 • d - x‖ = ‖p.1 + p.2 • d‖ := by congr 1; abel
      _ ≤ ‖p.1‖ + ‖p.2 • d‖ := norm_add_le _ _
      _ = ‖p.1‖ + p.2 * ‖d‖ := by rw [norm_smul, Real.norm_of_nonneg hp2a.le]
      _ < r := by linarith)
  have hdist := hFB.dist_le_mul _ hb _ ha
  rw [dist_eq_norm, dist_eq_norm] at hdist
  have e : x + p.1 + p.2 • d - (x + p.1) = p.2 • d := by abel
  rw [e, norm_smul, Real.norm_of_nonneg hp2a.le] at hdist
  simp only [qf]
  rw [abs_div, abs_of_pos hp2a, div_le_iff₀ hp2a]
  have : |F (x + p.1 + p.2 • d) - F (x + p.1)| ≤ K * (p.2 * ‖d‖) := by
    simpa [Real.norm_eq_abs] using hdist
  linarith


section lip
variable (F : (EuclideanSpace ℝ (Fin n)) → ℝ) (B : Set (EuclideanSpace ℝ (Fin n))) (hB : IsOpen B) (K : NNReal) (hFB : LipschitzOnWith K F B)
  (x : (EuclideanSpace ℝ (Fin n))) (hx : x ∈ B)
include hB hFB hx

lemma bdd_le (d : (EuclideanSpace ℝ (Fin n))) : IsBoundedUnder (· ≤ ·) (LF n) (qf F x d) := by
  refine isBoundedUnder_of_eventually_le (a := K * ‖d‖) ?_
  filter_upwards [bound_ev F B hB K hFB x hx d] with p hp using (le_abs_self _).trans hp

lemma bdd_ge (d : (EuclideanSpace ℝ (Fin n))) : IsBoundedUnder (· ≥ ·) (LF n) (qf F x d) := by
  refine isBoundedUnder_of_eventually_ge (a := -(K * ‖d‖)) ?_
  filter_upwards [bound_ev F B hB K hFB x hx d] with p hp
  have := neg_abs_le (qf F x d p)
  linarith

lemma dd_le_bound (d : (EuclideanSpace ℝ (Fin n))) : genDirDeriv F x d ≤ K * ‖d‖ := by
  rw [genDirDeriv_eq]
  refine limsup_le_of_le (bdd_ge F B hB K hFB x hx d).isCoboundedUnder_flip ?_
  filter_upwards [bound_ev F B hB K hFB x hx d] with p hp using (le_abs_self _).trans hp

lemma dd_zero : genDirDeriv F x 0 = 0 := by
  rw [genDirDeriv_eq]
  have : qf F x 0 = fun _ => 0 := by
    funext p; simp [qf]
  rw [this]
  exact limsup_const 0

lemma dd_add (d1 d2 : (EuclideanSpace ℝ (Fin n))) :
    genDirDeriv F x (d1 + d2) ≤ genDirDeriv F x d1 + genDirDeriv F x d2 := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have ev1 : ∀ᶠ p in LF n, qf F x d1 p < genDirDeriv F x d1 + ε / 2 :=
    eventually_lt_of_limsup_lt (by rw [← genDirDeriv_eq]; linarith) (bdd_le F B hB K hFB x hx d1)
  have ev2 : ∀ᶠ p in LF n, qf F x d2 p < genDirDeriv F x d2 + ε / 2 :=
    eventually_lt_of_limsup_lt (by rw [← genDirDeriv_eq]; linarith) (bdd_le F B hB K hFB x hx d2)
  have hψ : Tendsto (fun p : (EuclideanSpace ℝ (Fin n)) × ℝ => (p.1 + p.2 • d2, p.2)) (LF n) (LF n) := by
    refine Tendsto.prodMk ?_ tendsto_snd
    have h0 : Tendsto (fun p : (EuclideanSpace ℝ (Fin n)) × ℝ => p.2) (LF n) (𝓝 0) :=
      tendsto_snd.mono_right nhdsWithin_le_nhds
    have := (tendsto_fst (f := 𝓝 (0 : (EuclideanSpace ℝ (Fin n)))) (g := 𝓝[>] (0:ℝ))).add (h0.smul_const d2)
    simpa using this
  have ev1' : ∀ᶠ p in LF n, qf F x d1 (p.1 + p.2 • d2, p.2) < genDirDeriv F x d1 + ε / 2 :=
    hψ.eventually ev1
  have key : ∀ᶠ p in LF n, qf F x (d1 + d2) p ≤
      genDirDeriv F x d1 + genDirDeriv F x d2 + ε := by
    filter_upwards [ev1', ev2] with p h1 h2
    have e : qf F x (d1 + d2) p = qf F x d1 (p.1 + p.2 • d2, p.2) + qf F x d2 p := by
      simp only [qf]
      have e1 : x + (p.1 + p.2 • d2) + p.2 • d1 = x + p.1 + p.2 • (d1 + d2) := by module
      have e2 : x + (p.1 + p.2 • d2) = x + p.1 + p.2 • d2 := by abel
      rw [e1, e2]; ring
    linarith
  rw [genDirDeriv_eq (d := d1 + d2)]
  exact limsup_le_of_le (bdd_ge F B hB K hFB x hx (d1 + d2)).isCoboundedUnder_flip key

lemma dd_smul_le (c : ℝ) (hc : 0 < c) (d : (EuclideanSpace ℝ (Fin n))) :
    genDirDeriv F x (c • d) ≤ c * genDirDeriv F x d := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have ev : ∀ᶠ p in LF n, qf F x d p < genDirDeriv F x d + ε / c :=
    eventually_lt_of_limsup_lt (by rw [← genDirDeriv_eq]; have : 0 < ε / c := by positivity
                                   linarith) (bdd_le F B hB K hFB x hx d)
  have hψ : Tendsto (fun p : (EuclideanSpace ℝ (Fin n)) × ℝ => (p.1, c * p.2)) (LF n) (LF n) := by
    refine Tendsto.prodMk tendsto_fst ?_
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h0 : Tendsto (fun p : (EuclideanSpace ℝ (Fin n)) × ℝ => p.2) (LF n) (𝓝 0) :=
        tendsto_snd.mono_right nhdsWithin_le_nhds
      simpa using h0.const_mul c
    · filter_upwards [snd_pos (n := n)] with p hp
      exact mul_pos hc hp
  have ev' : ∀ᶠ p in LF n, qf F x d (p.1, c * p.2) < genDirDeriv F x d + ε / c :=
    hψ.eventually ev
  have key : ∀ᶠ p in LF n, qf F x (c • d) p ≤ c * genDirDeriv F x d + ε := by
    filter_upwards [ev', snd_pos (n := n)] with p h1 hp
    have e : qf F x (c • d) p = c * qf F x d (p.1, c * p.2) := by
      simp only [qf]
      have e1 : p.2 • c • d = (c * p.2) • d := by rw [smul_smul, mul_comm]
      rw [e1]
      field_simp
    rw [e]
    have := mul_lt_mul_of_pos_left h1 hc
    have e2 : c * (genDirDeriv F x d + ε / c) = c * genDirDeriv F x d + ε := by field_simp
    linarith
  rw [genDirDeriv_eq (d := c • d)]
  exact limsup_le_of_le (bdd_ge F B hB K hFB x hx (c • d)).isCoboundedUnder_flip key

lemma dd_smul (c : ℝ) (hc : 0 < c) (d : (EuclideanSpace ℝ (Fin n))) :
    genDirDeriv F x (c • d) = c * genDirDeriv F x d := by
  apply le_antisymm (dd_smul_le F B hB K hFB x hx c hc d)
  have h := dd_smul_le F B hB K hFB x hx c⁻¹ (inv_pos.2 hc) (c • d)
  rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at h
  have := mul_le_mul_of_nonneg_left h hc.le
  rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at this
  exact this


lemma dd_hb (f : (EuclideanSpace ℝ (Fin n)) →ₗ.[ℝ] ℝ) (hf : ∀ v : f.domain, f v ≤ genDirDeriv F x v) :
    ∃ g ∈ genGrad F x, ∀ v : f.domain, inner ℝ g (v : EuclideanSpace ℝ (Fin n)) = f v := by
  obtain ⟨G, hG1, hG2⟩ := exists_extension_of_le_sublinear f (fun v => genDirDeriv F x v)
    (fun c hc v => dd_smul F B hB K hFB x hx c hc v) (fun a b => dd_add F B hB K hFB x hx a b) hf
  refine ⟨(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
    (LinearMap.toContinuousLinearMap G), ?_, ?_⟩
  · intro d
    rw [InnerProductSpace.toDual_symm_apply]
    simpa using hG2 d
  · intro v
    rw [InnerProductSpace.toDual_symm_apply]
    simpa using hG1 v

lemma exists_mem : ∃ g, g ∈ genGrad F x := by
  let f : (EuclideanSpace ℝ (Fin n)) →ₗ.[ℝ] ℝ := ⟨⊥, 0⟩
  obtain ⟨g, hg, _⟩ := dd_hb F B hB K hFB x hx f (by
    rintro ⟨v, hv⟩
    have : v = 0 := by simpa [f] using hv
    subst this
    simp [f, dd_zero F B hB K hFB x hx])
  exact ⟨g, hg⟩

lemma exists_gg (d : (EuclideanSpace ℝ (Fin n))) :
    ∃ g ∈ genGrad F x, inner ℝ g d = genDirDeriv F x d := by
  by_cases hd : d = 0
  · subst hd
    obtain ⟨g, hg⟩ := exists_mem F B hB K hFB x hx
    exact ⟨g, hg, by simp [dd_zero F B hB K hFB x hx]⟩
  · let f : (EuclideanSpace ℝ (Fin n)) →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton d (genDirDeriv F x d) hd
    obtain ⟨g, hg, hg2⟩ := dd_hb F B hB K hFB x hx f (by
      rintro ⟨v, hv⟩
      have hv' : v ∈ (ℝ ∙ d) := by simpa [f] using hv
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv'
      have : f ⟨c • d, hv⟩ = c • genDirDeriv F x d :=
        LinearPMap.mkSpanSingleton'_apply _ _ _ c hv
      rw [this, smul_eq_mul]
      rcases lt_trichotomy c 0 with hc | hc | hc
      · have e : c • d = (-c) • (-d) := by simp
        have h1 := dd_smul F B hB K hFB x hx (-c) (by linarith) (-d)
        have h2 := dd_add F B hB K hFB x hx d (-d)
        rw [add_neg_cancel, dd_zero F B hB K hFB x hx] at h2
        show c * genDirDeriv F x d ≤ genDirDeriv F x (c • d)
        rw [e, h1]
        nlinarith
      · subst hc; simp [dd_zero F B hB K hFB x hx]
      · exact (dd_smul F B hB K hFB x hx c hc d).symm.le)
    refine ⟨g, hg, ?_⟩
    have := hg2 ⟨d, Submodule.mem_span_singleton_self d⟩
    rw [this]
    exact LinearPMap.mkSpanSingleton_apply ℝ ℝ hd _

lemma nonempty_gg : (genGrad F x).Nonempty := exists_mem F B hB K hFB x hx

lemma convex_gg : Convex ℝ (genGrad F x) := by
  intro g1 hg1 g2 hg2 a b ha hb hab d
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have h1 := hg1 d
  have h2 := hg2 d
  have e : (a + b) * genDirDeriv F x d = genDirDeriv F x d := by rw [hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb, e]

lemma compact_gg : IsCompact (genGrad F x) := by
  have hcl : IsClosed (genGrad F x) := by
    have : genGrad F x = ⋂ d, {g : EuclideanSpace ℝ (Fin n) | inner ℝ g d ≤ genDirDeriv F x d} := by
      ext g; simp [genGrad]
    rw [this]
    exact isClosed_iInter (fun d => isClosed_le (continuous_id.inner continuous_const) continuous_const)
  have hbd : Bornology.IsBounded (genGrad F x) := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨K, fun g hg => ?_⟩
    rw [mem_closedBall_zero_iff]
    have h1 := hg g
    have h2 := dd_le_bound F B hB K hFB x hx g
    rw [real_inner_self_eq_norm_sq] at h1
    have h3 : ‖g‖ ^ 2 ≤ K * ‖g‖ := h1.trans h2
    rcases (norm_nonneg g).eq_or_lt with h | h
    · rw [← h]; exact K.coe_nonneg
    · nlinarith
  exact Metric.isCompact_of_isClosed_isBounded hcl hbd

end lip

end ClarkeCore

theorem solution {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (B : Set (EuclideanSpace ℝ (Fin n)))
    (hB : IsOpen B) (K : NNReal) (hFB : LipschitzOnWith K F B) (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ B) :
    (MifflinSemismooth.Extremal.genGrad F x).Nonempty ∧ Convex ℝ (MifflinSemismooth.Extremal.genGrad F x) ∧
      IsCompact (MifflinSemismooth.Extremal.genGrad F x) :=
  ⟨ClarkeCore.nonempty_gg F B hB K hFB x hx, ClarkeCore.convex_gg F B hB K hFB x hx,
    ClarkeCore.compact_gg F B hB K hFB x hx⟩
