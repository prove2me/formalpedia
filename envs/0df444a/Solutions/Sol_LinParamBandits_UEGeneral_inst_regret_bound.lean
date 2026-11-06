-- Prove2me | solution 1 for LinParamBandits.UEGeneral.inst_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T20:54:00.965298+00:00
-- url     : https://prove2.me/submissions/7cc0d84c-c72a-4fbe-b89a-67bb503c7f65

import Mathlib
import Definitions.Def_LinParamBandits_UEGeneral_Model
import Definitions.Def_LinParamBandits_UEGeneral_UEPolicy
import Theorems.Thm_LinParamBandits_UEGeneral_radius_large_deviation

open MeasureTheory ProbabilityTheory

namespace UEGenB7Aux

open Matrix LinParamBandits.UEGeneral

variable {r : ℕ}

lemma measurable_stepZ (ψ : Policy r) (n : ℕ) :
    Measurable (fun q : LinParamBandits.LowerBound.Vec r × (LinParamBandits.LowerBound.History r n × ℝ) =>
      Fin.snoc (α := fun _ => LinParamBandits.LowerBound.Vec r × ℝ) q.2.1
        (ψ.act n q.2.1, inner ℝ (ψ.act n q.2.1) q.1 + q.2.2)) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    have ha : Measurable (fun q : LinParamBandits.LowerBound.Vec r ×
        (LinParamBandits.LowerBound.History r n × ℝ) => ψ.act n q.2.1) :=
      (ψ.measurable_act n).comp (measurable_fst.comp measurable_snd)
    refine ha.prodMk ?_
    exact (Measurable.inner ha measurable_fst).add (measurable_snd.comp measurable_snd)
  · simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)

lemma measurable_step (ψ : Policy r) (z : LinParamBandits.LowerBound.Vec r) (n : ℕ) :
    Measurable (fun p : LinParamBandits.LowerBound.History r n × ℝ =>
      Fin.snoc (α := fun _ => LinParamBandits.LowerBound.Vec r × ℝ) p.1
        (ψ.act n p.1, inner ℝ (ψ.act n p.1) z + p.2)) :=
  (measurable_stepZ ψ n).comp (measurable_const.prodMk measurable_id)

/-- The admissible arm set of period `s + 1`: arms of `𝒰`, equal to `b_{s+1}` if `s < r`. -/
def admissible (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (b : Fin r → LinParamBandits.LowerBound.Vec r)
    (s : ℕ) : Set (LinParamBandits.LowerBound.Vec r) :=
  {v | v ∈ 𝒰 ∧ ∀ hs : s < r, v = b ⟨s, hs⟩}

lemma measurableSet_admissible (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰 : MeasurableSet 𝒰)
    (b : Fin r → LinParamBandits.LowerBound.Vec r) (s : ℕ) : MeasurableSet (admissible 𝒰 b s) := by
  by_cases hs : s < r
  · have : admissible 𝒰 b s = 𝒰 ∩ {b ⟨s, hs⟩} := by
      ext v; simp only [admissible, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_singleton_iff]
      exact ⟨fun h => ⟨h.1, h.2 hs⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩
    rw [this]; exact h𝒰.inter (measurableSet_singleton _)
  · have : admissible 𝒰 b s = 𝒰 := by
      ext v; simp only [admissible, Set.mem_setOf_eq]
      exact ⟨fun h => h.1, fun h => ⟨h, fun h' => absurd h' hs⟩⟩
    rw [this]; exact h𝒰

lemma measurableSet_good (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰 : MeasurableSet 𝒰)
    (b : Fin r → LinParamBandits.LowerBound.Vec r) (n : ℕ) :
    MeasurableSet {h : LinParamBandits.LowerBound.History r n | ∀ s : Fin n, (h s).1 ∈ admissible 𝒰 b s} := by
  have : {h : LinParamBandits.LowerBound.History r n | ∀ s : Fin n, (h s).1 ∈ admissible 𝒰 b s} =
      ⋂ s : Fin n, (fun h : LinParamBandits.LowerBound.History r n => (h s).1) ⁻¹' admissible 𝒰 b s := by
    ext h; simp
  rw [this]
  exact MeasurableSet.iInter fun s =>
    (measurable_fst.comp (measurable_pi_apply s)) (measurableSet_admissible 𝒰 h𝒰 b s)

lemma ae_good (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰 : MeasurableSet 𝒰)
    (b : Fin r → LinParamBandits.LowerBound.Vec r)
    (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ)
    (z : LinParamBandits.LowerBound.Vec r) (ψ : Policy r)
    (hact : ∀ t h, ψ.act t h ∈ 𝒰)
    (hinit : ∀ (t : ℕ) (h : LinParamBandits.LowerBound.History r t) (ht : t < r), ψ.act t h = b ⟨t, ht⟩) :
    ∀ n, ∀ᵐ h ∂(histMeasure ν z ψ n), ∀ s : Fin n, (h s).1 ∈ admissible 𝒰 b s
  | 0 => Filter.Eventually.of_forall (fun h s => Fin.elim0 s)
  | n + 1 => by
      have ih := ae_good 𝒰 h𝒰 b ν z ψ hact hinit n
      simp only [histMeasure]
      rw [ae_map_iff (measurable_step ψ z n).aemeasurable (measurableSet_good 𝒰 h𝒰 b (n + 1))]
      have hms : MeasurableSet {p : LinParamBandits.LowerBound.History r n × ℝ |
          ∀ s : Fin n, (p.1 s).1 ∈ admissible 𝒰 b s} :=
        measurable_fst (measurableSet_good 𝒰 h𝒰 b n)
      have h2 : ∀ᵐ p ∂((histMeasure ν z ψ n) ⊗ₘ (ν.comap (ψ.act n) (ψ.measurable_act n))),
          ∀ s : Fin n, (p.1 s).1 ∈ admissible 𝒰 b s := by
        apply Measure.ae_compProd_of_ae_ae hms
        filter_upwards [ih] with h hh
        exact Filter.Eventually.of_forall (fun _ => hh)
      filter_upwards [h2] with p hp
      intro s
      refine Fin.lastCases ?_ (fun j => ?_) s
      · simp only [Fin.snoc_last, Fin.val_last]
        exact ⟨hact n p.1, fun hs => hinit n p.1 hs⟩
      · simp only [Fin.snoc_castSucc, Fin.coe_castSucc]
        exact hp j

lemma bddAbove_image (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰c : IsCompact 𝒰)
    (z : LinParamBandits.LowerBound.Vec r) : BddAbove ((fun v => inner ℝ v z) '' 𝒰) :=
  (h𝒰c.image (by fun_prop : Continuous fun v : LinParamBandits.LowerBound.Vec r => inner ℝ v z)).bddAbove

lemma le_bestValue (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰c : IsCompact 𝒰)
    (u : LinParamBandits.LowerBound.Vec r) (hu : u ∈ 𝒰) (z : LinParamBandits.LowerBound.Vec r) :
    inner ℝ u z ≤ bestValue 𝒰 z :=
  le_csSup (bddAbove_image 𝒰 h𝒰c z) ⟨u, hu, rfl⟩

theorem inner_vec (x y : LinParamBandits.LowerBound.Vec r) :
    inner ℝ x y = x.ofLp ⬝ᵥ y.ofLp := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

theorem norm_sq_vec (x : LinParamBandits.LowerBound.Vec r) : ‖x‖ ^ 2 = x.ofLp ⬝ᵥ x.ofLp := by
  rw [← real_inner_self_eq_norm_sq, inner_vec]

theorem design_succ (U : ℕ → LinParamBandits.LowerBound.Vec r) (n : ℕ) :
    design (fun s : Fin (n + 1) => U s) =
      design (fun s : Fin n => U s) + vecMulVec (U n).ofLp (U n).ofLp := by
  unfold design
  rw [Fin.sum_univ_castSucc]
  simp

theorem quad_design (U : ℕ → LinParamBandits.LowerBound.Vec r) (n : ℕ) (x : Fin r → ℝ) :
    x ⬝ᵥ (design (fun s : Fin n => U s) *ᵥ x) =
      ∑ s ∈ Finset.range n, ((U s).ofLp ⬝ᵥ x) ^ 2 := by
  unfold design
  rw [Matrix.sum_mulVec, dotProduct_sum, ← Fin.sum_univ_eq_sum_range (fun s => ((U s).ofLp ⬝ᵥ x) ^ 2) n]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [vecMulVec_mulVec, dotProduct_smul]
  simp [dotProduct_comm x, sq]

theorem design_psd (U : ℕ → LinParamBandits.LowerBound.Vec r) (n : ℕ) :
    (design (fun s : Fin n => U s)).PosSemidef := by
  unfold design
  refine Finset.sum_induction _ (fun M : Matrix (Fin r) (Fin r) ℝ => M.PosSemidef)
    (fun _ _ => PosSemidef.add) PosSemidef.zero (fun s _ => ?_)
  have := posSemidef_vecMulVec_self_star (R := ℝ) (U s).ofLp
  simpa using this


theorem design_lower {b : Fin r → LinParamBandits.LowerBound.Vec r} {lam0 : ℝ}
    (hb : ∀ x : LinParamBandits.LowerBound.Vec r, lam0 * ‖x‖ ^ 2 ≤ ∑ k, inner ℝ (b k) x ^ 2)
    (U : ℕ → LinParamBandits.LowerBound.Vec r) (hU_init : ∀ (k : ℕ) (hk : k < r), U k = b ⟨k, hk⟩)
    (n : ℕ) (hn : r ≤ n) (x : LinParamBandits.LowerBound.Vec r) :
    lam0 * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ (design (fun s : Fin n => U s) *ᵥ x.ofLp) := by
  rw [quad_design]
  refine (hb x).trans ?_
  have h1 : ∑ k : Fin r, inner ℝ (b k) x ^ 2 = ∑ s ∈ Finset.range r, ((U s).ofLp ⬝ᵥ x.ofLp) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun s => ((U s).ofLp ⬝ᵥ x.ofLp) ^ 2) r]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hU_init k k.2, inner_vec]
  rw [h1]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn) (fun _ _ _ => sq_nonneg _)


lemma dot_symm (A : Matrix (Fin r) (Fin r) ℝ) (hA : Aᵀ = A) (x y : Fin r → ℝ) :
    y ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (A *ᵥ y) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, dotProduct_comm]

lemma form_tri (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosSemidef) (x y : Fin r → ℝ) :
    Real.sqrt ((x - y) ⬝ᵥ (A *ᵥ (x - y))) ≤
      Real.sqrt (x ⬝ᵥ (A *ᵥ x)) + Real.sqrt (y ⬝ᵥ (A *ᵥ y)) := by
  have hT : Aᵀ = A := by
    have := hA.1
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
    exact this
  have hnn : ∀ v : Fin r → ℝ, 0 ≤ v ⬝ᵥ (A *ᵥ v) := by
    intro v
    have := hA.dotProduct_mulVec_nonneg v
    simpa using this
  set a := x ⬝ᵥ (A *ᵥ x)
  set c := y ⬝ᵥ (A *ᵥ y)
  set m := x ⬝ᵥ (A *ᵥ y)
  have hexp : ∀ s : ℝ, (s • x - y) ⬝ᵥ (A *ᵥ (s • x - y)) = s ^ 2 * a - 2 * s * m + c := by
    intro s
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dot_symm A hT x y]
    ring
  have ha : 0 ≤ a := hnn x
  have hc : 0 ≤ c := hnn y
  have hm : m ^ 2 ≤ a * c := by
    rcases ha.lt_or_eq with ha' | ha'
    · have h1 := hnn ((m / a) • x - y)
      rw [hexp] at h1
      have : (m / a) ^ 2 * a - 2 * (m / a) * m + c = c - m ^ 2 / a := by field_simp; ring
      rw [this] at h1
      have : m ^ 2 / a ≤ c := by linarith
      rw [div_le_iff₀ ha'] at this
      linarith
    · have hm0 : m = 0 := by
        by_contra hm0
        have h1 := hnn (((c + 1) / (2 * m)) • x - y)
        rw [hexp, ← ha'] at h1
        have : ((c + 1) / (2 * m)) ^ 2 * 0 - 2 * ((c + 1) / (2 * m)) * m + c = -1 := by
          field_simp; ring
        linarith
      rw [hm0, ← ha']; simp
  have hxy : (x - y) ⬝ᵥ (A *ᵥ (x - y)) = a - 2 * m + c := by
    have := hexp 1
    simp only [one_smul, one_pow, one_mul, mul_one] at this
    exact this
  rw [hxy, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 : |m| ≤ Real.sqrt (a * c) := Real.abs_le_sqrt hm
  rw [Real.sqrt_mul ha] at h1
  have h2 := neg_abs_le m
  have h3 := Real.sq_sqrt ha
  have h4 := Real.sq_sqrt hc
  nlinarith

lemma design_posDef {b : Fin r → LinParamBandits.LowerBound.Vec r} {lam0 : ℝ} (hlam0 : 0 < lam0)
    (hb : ∀ x : LinParamBandits.LowerBound.Vec r, lam0 * ‖x‖ ^ 2 ≤ ∑ k, inner ℝ (b k) x ^ 2)
    (U : ℕ → LinParamBandits.LowerBound.Vec r) (hU_init : ∀ (k : ℕ) (hk : k < r), U k = b ⟨k, hk⟩)
    (n : ℕ) (hn : r ≤ n) : (design (fun s : Fin n => U s)).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (design_psd U n).1 ?_
  intro x hx
  have h := design_lower hb U hU_init n hn (WithLp.toLp 2 x)
  simp only [star_trivial]
  have hx' : WithLp.toLp 2 x ≠ (0 : LinParamBandits.LowerBound.Vec r) := by
    intro h0; apply hx
    have := congrArg WithLp.ofLp h0
    simpa using this
  have : 0 < ‖(WithLp.toLp 2 x : LinParamBandits.LowerBound.Vec r)‖ := norm_pos_iff.mpr hx'
  have : 0 < lam0 * ‖(WithLp.toLp 2 x : LinParamBandits.LowerBound.Vec r)‖ ^ 2 := by positivity
  simp only [WithLp.ofLp_toLp] at h
  linarith

end UEGenB7Aux

open UEGenB7Aux LinParamBandits.UEGeneral in
theorem solution {r : ℕ} (hr : 2 ≤ r) {𝒰 : Set (LinParamBandits.LowerBound.Vec r)} (h𝒰c : IsCompact 𝒰) (h𝒰n : 𝒰.Nonempty)
    {ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ} [IsMarkovKernel ν] {b : Fin r → LinParamBandits.LowerBound.Vec r} {σ₀ ubar lam0 : ℝ}
    (hA : Assumption1 𝒰 ν b σ₀ ubar lam0) {ψ : Policy r} (hψ : IsUE 𝒰 b σ₀ ubar lam0 ψ)
    (t : ℕ) (ht : r ≤ t) (z : LinParamBandits.LowerBound.Vec r) :
    histMeasure ν z ψ t
        {h | 2 * radiusFactor 𝒰 σ₀ ubar lam0 t * wnorm (Cmat (armsOf h)) (ψ.act t h) <
          instRegret 𝒰 z (ψ.act t h)} ≤
      ENNReal.ofReal (1 / (t : ℝ) ^ 2) := by
  have h𝒰m : MeasurableSet 𝒰 := h𝒰c.isClosed.measurableSet
  obtain ⟨w, hw, hwmax⟩ := h𝒰c.exists_isMaxOn h𝒰n
    (f := fun v : LinParamBandits.LowerBound.Vec r => inner ℝ v z) (by fun_prop)
  have hbest : bestValue 𝒰 z = inner ℝ w z := by
    apply le_antisymm
    · unfold bestValue
      apply csSup_le (h𝒰n.image _)
      rintro _ ⟨v, hv, rfl⟩
      exact hwmax hv
    · exact le_bestValue 𝒰 h𝒰c w hw z
  have hβ : 0 ≤ radiusFactor 𝒰 σ₀ ubar lam0 t := by
    have := hA.σ₀_pos
    unfold radiusFactor alpha; positivity
  have key := (radius_large_deviation hr h𝒰c h𝒰n hA hψ t ht z).2 w
  refine le_trans (measure_mono_ae ?_) key
  filter_upwards [ae_good 𝒰 h𝒰m b ν z ψ hψ.act_mem hψ.act_init t] with h hg
  intro hB
  replace hB : 2 * radiusFactor 𝒰 σ₀ ubar lam0 t * wnorm (Cmat (armsOf h)) (ψ.act t h) <
      instRegret 𝒰 z (ψ.act t h) := hB
  show radiusFactor 𝒰 σ₀ ubar lam0 t * wnorm (Cmat (armsOf h)) (ψ.act t h - w) <
    inner ℝ (ψ.act t h - w) (Zhat h - z)
  set β := radiusFactor 𝒰 σ₀ ubar lam0 t
  set U := ψ.act t h
  set C := Cmat (armsOf h)
  have hinit : ∀ (k : Fin t) (hk : (k : ℕ) < r), (h k).1 = b ⟨k, hk⟩ := fun k hk => (hg k).2 hk
  have harg := hψ.act_argmax t ht h hinit w hw
  have hrad : ∀ v, radius 𝒰 σ₀ ubar lam0 h v = β * wnorm C v := fun v => rfl
  rw [hrad, hrad] at harg
  -- C is positive semidefinite
  let V : ℕ → LinParamBandits.LowerBound.Vec r := fun s => if hs : s < t then (h ⟨s, hs⟩).1 else 0
  have hV : armsOf h = fun s : Fin t => V s := by
    funext s; simp only [armsOf, V, dif_pos s.isLt]
  have hVinit : ∀ (k : ℕ) (hk : k < r), V k = b ⟨k, hk⟩ := by
    intro k hk
    have hkt : k < t := by omega
    simp only [V, dif_pos hkt]
    exact hinit ⟨k, hkt⟩ hk
  have hCpsd : C.PosSemidef := by
    simp only [C, Cmat, hV]
    exact (design_posDef hA.lam0_pos hA.b_minEig V hVinit t ht).inv.posSemidef
  have htri : wnorm C (U - w) ≤ wnorm C U + wnorm C w := by
    unfold wnorm quadForm
    have := form_tri C hCpsd U.ofLp w.ofLp
    simpa [WithLp.ofLp_sub] using this
  have hin : inner ℝ (U - w) (Zhat h - z) =
      (inner ℝ U (Zhat h) - inner ℝ w (Zhat h)) + (inner ℝ w z - inner ℝ U z) := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]; ring
  have hQ : instRegret 𝒰 z U = inner ℝ w z - inner ℝ U z := by
    unfold instRegret; rw [hbest]
  rw [hQ] at hB
  rw [hin]
  have := mul_le_mul_of_nonneg_left htri hβ
  nlinarith
