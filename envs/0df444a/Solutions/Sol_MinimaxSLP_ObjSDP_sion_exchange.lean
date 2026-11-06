-- Prove2me | solution 1 for MinimaxSLP.ObjSDP.sion_exchange
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T01:45:53.323321+00:00
-- url     : https://prove2.me/submissions/d867e8da-aea5-48cf-87f8-00a3f8f8d293

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjSDP_Model

open MeasureTheory Matrix

namespace MinimaxSLP.ObjSDP.SionAux

lemma recourseSet_isClosed {n r d : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (x : Fin n → ℝ) : IsClosed (recourseSet W T h x) := by
  have : recourseSet W T h x = {w | W *ᵥ w = h - T *ᵥ x} ∩ {w | 0 ≤ w} := rfl
  rw [this]
  exact IsClosed.inter (isClosed_eq (Continuous.matrix_mulVec continuous_const continuous_id)
    continuous_const) (isClosed_le continuous_const continuous_id)

lemma recourseSet_convex {n r d : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (x : Fin n → ℝ) : Convex ℝ (recourseSet W T h x) := by
  intro w1 hw1 w2 hw2 s t hs ht hst
  refine ⟨?_, ?_⟩
  · rw [mulVec_add, mulVec_smul, mulVec_smul, hw1.1, hw2.1, ← add_smul, hst, one_smul]
  · exact add_nonneg (smul_nonneg hs hw1.2) (smul_nonneg ht hw2.2)

/-- `q ↦ q′Yq + q′y + y₀ − a q′w − b` is convex for `Y ⪰ 0`. -/
lemma convexOn_G {d : ℕ} (Y : Matrix (Fin d) (Fin d) ℝ) (hY : Y.PosSemidef) (y : Fin d → ℝ)
    (y₀ a b : ℝ) (w : Fin d → ℝ) :
    ConvexOn ℝ Set.univ
      (fun q : Fin d → ℝ => q ⬝ᵥ (Y *ᵥ q) + q ⬝ᵥ y + y₀ - a * (q ⬝ᵥ w) - b) := by
  have hYt : Yᵀ = Y := by
    have := hY.isHermitian
    unfold IsHermitian at this
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  refine ⟨convex_univ, fun u _ v _ s t hs ht hst => ?_⟩
  have hsym : v ⬝ᵥ (Y *ᵥ u) = u ⬝ᵥ (Y *ᵥ v) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hYt, dotProduct_comm]
  have hpsd := hY.dotProduct_mulVec_nonneg (u - v)
  simp only [star_trivial, mulVec_sub, dotProduct_sub, sub_dotProduct] at hpsd
  rw [hsym] at hpsd
  obtain rfl : t = 1 - s := by linarith
  simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul]
  rw [hsym]
  nlinarith [mul_nonneg (mul_nonneg hs ht) hpsd]

/-- `w ↦ q′Yq + q′y + y₀ − a q′w − b` is affine, hence concave. -/
lemma concaveOn_G {d : ℕ} (S : Set (Fin d → ℝ)) (hS : Convex ℝ S)
    (Y : Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ) (y₀ a b : ℝ) (q : Fin d → ℝ) :
    ConcaveOn ℝ S
      (fun w : Fin d → ℝ => q ⬝ᵥ (Y *ᵥ q) + q ⬝ᵥ y + y₀ - a * (q ⬝ᵥ w) - b) := by
  refine ⟨hS, fun u _ v _ s t hs ht hst => ?_⟩
  obtain rfl : t = 1 - s := by linarith
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
  apply le_of_eq
  ring

end MinimaxSLP.ObjSDP.SionAux

open MinimaxSLP.ObjSDP MinimaxSLP.ObjSDP.SionAux in
theorem solution {n r d : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty)
    (hbdd : Bornology.IsBounded (recourseSet W T h x))
    (Y : Matrix (Fin d) (Fin d) ℝ) (hY : Y.PosSemidef) (y : Fin d → ℝ) (y₀ a b : ℝ) :
    (⨅ q : Fin d → ℝ, ⨆ w ∈ recourseSet W T h x,
        ((q ⬝ᵥ (Y *ᵥ q) + q ⬝ᵥ y + y₀ - a * (q ⬝ᵥ w) - b : ℝ) : EReal)) =
      (⨆ w ∈ recourseSet W T h x, ⨅ q : Fin d → ℝ,
        ((q ⬝ᵥ (Y *ᵥ q) + q ⬝ᵥ y + y₀ - a * (q ⬝ᵥ w) - b : ℝ) : EReal)) ∧
    ∃ w₀ ∈ recourseSet W T h x,
      (⨅ q : Fin d → ℝ, ((q ⬝ᵥ (Y *ᵥ q) + q ⬝ᵥ y + y₀ - a * (q ⬝ᵥ w₀) - b : ℝ) : EReal)) =
        ⨆ w ∈ recourseSet W T h x, ⨅ q : Fin d → ℝ,
          ((q ⬝ᵥ (Y *ᵥ q) + q ⬝ᵥ y + y₀ - a * (q ⬝ᵥ w) - b : ℝ) : EReal) := by
  set S := recourseSet W T h x with hSdef
  set G : (Fin d → ℝ) → (Fin d → ℝ) → ℝ :=
    fun q w => q ⬝ᵥ (Y *ᵥ q) + q ⬝ᵥ y + y₀ - a * (q ⬝ᵥ w) - b with hG
  have cS : Convex ℝ S := recourseSet_convex W T h x
  have kS : IsCompact S := Metric.isCompact_of_isClosed_isBounded
    (recourseSet_isClosed W T h x) hbdd
  have hcontq : ∀ w, Continuous fun q => G q w := by
    intro w
    simp only [hG]
    fun_prop
  have hcontw : ∀ q, Continuous fun w => G q w := by
    intro q
    simp only [hG]
    fun_prop
  have hmono : Monotone (fun t : ℝ => (t : EReal)) := fun s t hst => EReal.coe_le_coe_iff.2 hst
  -- apply Sion's theorem to `f(w, q) = toDual (G q w)` with the compact convex set `S`
  let f : (Fin d → ℝ) → (Fin d → ℝ) → ERealᵒᵈ := fun w q => OrderDual.toDual ((G q w : ℝ) : EReal)
  have hfy : ∀ q ∈ (Set.univ : Set (Fin d → ℝ)), LowerSemicontinuousOn (fun w => f w q) S :=
    fun q _ => (continuous_toDual.comp
      (continuous_coe_real_ereal.comp (hcontw q))).lowerSemicontinuous.lowerSemicontinuousOn S
  have hfy' : ∀ q ∈ (Set.univ : Set (Fin d → ℝ)), QuasiconvexOn ℝ S (fun w => f w q) :=
    fun q _ => (((concaveOn_G S cS Y y y₀ a b q).quasiconcaveOn).monotone_comp hmono).dual
  have hfx : ∀ w ∈ S, UpperSemicontinuousOn (fun q => f w q) Set.univ :=
    fun w _ => (continuous_toDual.comp
      (continuous_coe_real_ereal.comp (hcontq w))).upperSemicontinuous.upperSemicontinuousOn _
  have hfx' : ∀ w ∈ S, QuasiconcaveOn ℝ Set.univ (fun q => f w q) :=
    fun w _ => (((convexOn_G Y hY y y₀ a b w).quasiconvexOn).monotone_comp hmono).dual
  have hmm := Sion.minimax' hrec cS kS hfy hfy' convex_univ hfx hfx'
  have hmm' := congrArg OrderDual.ofDual hmm
  simp only [ofDual_iInf, ofDual_iSup, f, OrderDual.ofDual_toDual, Set.mem_univ, iSup_pos] at hmm'
  refine ⟨hmm'.symm, ?_⟩
  -- the outer maximum is attained: `w ↦ inf_q G q w` is upper semicontinuous on compact `S`
  have husc : UpperSemicontinuousOn (fun w => ⨅ q : Fin d → ℝ, ((G q w : ℝ) : EReal)) S :=
    upperSemicontinuousOn_iInf fun q =>
      (continuous_coe_real_ereal.comp (hcontw q)).upperSemicontinuous.upperSemicontinuousOn _
  obtain ⟨w₀, hw₀, hmax⟩ := husc.exists_isMaxOn hrec kS
  refine ⟨w₀, hw₀, le_antisymm ?_ ?_⟩
  · exact le_iSup₂_of_le w₀ hw₀ le_rfl
  · exact iSup₂_le fun w hw => hmax hw
