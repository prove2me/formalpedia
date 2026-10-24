-- Prove2me | solution 1 for MonoSkew.Main.proposition_2_7_i_iii
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-23T12:58:51.543028+00:00
-- url     : https://prove2.me/submissions/262a768a-2749-4910-9366-2a59ff7f3011

import Mathlib
import Definitions.Def_MonoSkew_Main_Basic



/-! Standard weak-strong sequential closedness of a maximal monotone graph,
with the bound on the weakly convergent sequence supplied explicitly.
No completeness or uniform boundedness theorem is needed. -/

open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence

namespace MonoSkew.FBF

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A point monotonically related to a maximal monotone graph belongs to the graph. -/
theorem mem_of_monotone_related (A : E → Set E) (hA : IsMaximalMonotone A)
    (w v : E) (hrel : ∀ p a, a ∈ A p → 0 ≤ ⟪w - p, v - a⟫_ℝ) : v ∈ A w := by
  let T : E → Set E := fun p => {a | a ∈ A p ∨ (p = w ∧ a = v)}
  have hT : IsMonotoneOp T := by
    intro p q a b ha hb
    rcases ha with ha | ⟨hpw, hav⟩
    · rcases hb with hb | ⟨hqw, hbv⟩
      · exact hA.1 p q a b ha hb
      · subst q
        subst b
        have he : ⟪p - w, a - v⟫_ℝ = ⟪w - p, v - a⟫_ℝ := by
          calc
            _ = ⟪-(w - p), -(v - a)⟫_ℝ := by simp only [neg_sub]
            _ = _ := inner_neg_neg _ _
        rw [he]
        exact hrel p a ha
    · subst p
      subst a
      rcases hb with hb | ⟨hqw, hbv⟩
      · exact hrel q b hb
      · subst q
        subst b
        simp
  have heq : T = A := hA.2 T hT (fun p a ha => Or.inl ha)
  rw [← heq]
  exact Or.inr ⟨rfl, rfl⟩

/-- Pairing a bounded weakly convergent sequence with a strongly convergent sequence
converges to the pairing of their limits. -/
theorem inner_tendsto_of_weak_strong_bounded (x u : ℕ → E) (w v : E) (R : ℝ)
    (hweak : WeakTendsto x w) (hstrong : Tendsto u atTop (𝓝 v))
    (hbound : ∀ n, ‖x n‖ ≤ R) :
    Tendsto (fun n => ⟪x n, u n⟫_ℝ) atTop (𝓝 ⟪w, v⟫_ℝ) := by
  have hnorm : Tendsto (fun n => ‖u n - v‖) atTop (𝓝 0) := by
    simpa using (hstrong.sub_const v).norm
  have herror : Tendsto (fun n => ⟪x n, u n - v⟫_ℝ) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n => R * ‖u n - v‖)
    · intro n
      calc
        ‖⟪x n, u n - v⟫_ℝ‖ = |⟪x n, u n - v⟫_ℝ| := Real.norm_eq_abs _
        _ ≤ ‖x n‖ * ‖u n - v‖ := abs_real_inner_le_norm _ _
        _ ≤ R * ‖u n - v‖ := mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _)
    · simpa using hnorm.const_mul R
  have hsum := (hweak v).add herror
  have he (n : ℕ) : v + (u n - v) = u n := by abel
  simpa only [← inner_add_right, he, add_zero] using hsum

/-- A maximal monotone graph is sequentially closed for weak convergence of its first
coordinate and strong convergence of its second, when a bound on the first is supplied. -/
theorem weak_strong_closed_of_bounded (A : E → Set E) (hA : IsMaximalMonotone A)
    (x u : ℕ → E) (w v : E) (R : ℝ)
    (hweak : WeakTendsto x w) (hstrong : Tendsto u atTop (𝓝 v))
    (hbound : ∀ n, ‖x n‖ ≤ R) (hgraph : ∀ n, u n ∈ A (x n)) : v ∈ A w := by
  apply mem_of_monotone_related A hA w v
  intro p a ha
  have hweak' : WeakTendsto (fun n => x n - p) (w - p) := by
    intro z
    simpa only [inner_sub_left] using (hweak z).sub_const ⟪p, z⟫_ℝ
  have hbound' : ∀ n, ‖x n - p‖ ≤ R + ‖p‖ := by
    intro n
    calc
      _ ≤ ‖x n‖ + ‖p‖ := norm_sub_le _ _
      _ ≤ R + ‖p‖ := by gcongr; exact hbound n
  have hlim := inner_tendsto_of_weak_strong_bounded (fun n => x n - p)
    (fun n => u n - a) (w - p) (v - a) (R + ‖p‖)
    hweak' (hstrong.sub_const a) hbound'
  exact ge_of_tendsto hlim (Eventually.of_forall fun n => hA.1 (x n) p (u n) a (hgraph n) ha)

end MonoSkew.FBF


/-! Elementary maximal-monotone calculus for the product-space construction.
All maximality arguments use monotonically related points; no resolvent
existence theorem or completeness assumption is required. -/

open InnerProductSpace
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR MonoSkew.Main

namespace MonoSkew.Structure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The related-point criterion also suffices to prove maximality. -/
theorem maximal_of_monotone_related (A : E → Set E) (hA : IsMonotoneOp A)
    (hmem : ∀ w v, (∀ p a, a ∈ A p → 0 ≤ ⟪w - p, v - a⟫_ℝ) → v ∈ A w) :
    IsMaximalMonotone A := by
  refine ⟨hA, ?_⟩
  intro T hT hsub
  funext w
  apply Set.Subset.antisymm
  · intro v hv
    exact hmem w v (fun p a ha => hT w p v a hv (hsub p ha))
  · exact hsub w

/-- At any candidate point a maximal graph has a graph point with nonpositive
monotonicity pairing. This includes the candidate itself when it is in the graph. -/
theorem exists_graph_nonpos (A : E → Set E) (hA : IsMaximalMonotone A) (w v : E) :
    ∃ p a, a ∈ A p ∧ ⟪w - p, v - a⟫_ℝ ≤ 0 := by
  classical
  by_cases hv : v ∈ A w
  · exact ⟨w, v, hv, by simp⟩
  · by_contra hn
    push Not at hn
    exact hv (FBF.mem_of_monotone_related A hA w v (fun p a ha => (hn p a ha).le))

/-- Inverting a maximal monotone graph preserves maximal monotonicity. -/
theorem maximal_inv (A : E → Set E) (hA : IsMaximalMonotone A) :
    IsMaximalMonotone (opInv A) := by
  apply maximal_of_monotone_related
  · intro x y u v hu hv
    simpa only [real_inner_comm] using hA.1 u v x y hu hv
  · intro w v hrel
    exact FBF.mem_of_monotone_related A hA v w (fun p a ha => by
      simpa only [real_inner_comm] using hrel a p ha)

/-- A constant output shift preserves maximal monotonicity. The shifted
operator sends `x` to the values `u` such that `u+c ∈ A x`. -/
theorem maximal_outputShift (A : E → Set E) (hA : IsMaximalMonotone A) (c : E) :
    IsMaximalMonotone (fun x => {u | u + c ∈ A x}) := by
  apply maximal_of_monotone_related
  · intro x y u v hu hv
    have he : (u + c) - (v + c) = u - v := by abel
    simpa only [he] using hA.1 x y (u + c) (v + c) hu hv
  · intro w v hrel
    apply FBF.mem_of_monotone_related A hA w (v + c)
    intro p a ha
    have hr := hrel p (a - c) (by
      change (a - c) + c ∈ A p
      simpa only [sub_add_cancel] using ha)
    have he : v - (a - c) = (v + c) - a := by abel
    simpa only [he] using hr

section Product

variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- The Cartesian product of two set-valued operators on the Hilbert direct sum. -/
def productOp (A : H → Set H) (B : G → Set G) : K H G → Set (K H G) :=
  fun x => {u | u.fst ∈ A x.fst ∧ u.snd ∈ B x.snd}

/-- The product graph of two maximal monotone graphs is maximal monotone. -/
theorem maximal_product (A : H → Set H) (B : G → Set G)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B) :
    IsMaximalMonotone (productOp A B) := by
  apply maximal_of_monotone_related
  · intro x y u v hu hv
    rw [WithLp.prod_inner_apply]
    exact add_nonneg (hA.1 x.fst y.fst u.fst v.fst hu.1 hv.1)
      (hB.1 x.snd y.snd u.snd v.snd hu.2 hv.2)
  · intro w v hrel
    obtain ⟨q, b, hb, hnonpos⟩ := exists_graph_nonpos B hB w.snd v.snd
    have hfst : v.fst ∈ A w.fst := by
      apply FBF.mem_of_monotone_related A hA w.fst v.fst
      intro p a ha
      have hr := hrel (WithLp.toLp 2 (p, q)) (WithLp.toLp 2 (a, b)) ⟨ha, hb⟩
      rw [WithLp.prod_inner_apply] at hr
      change 0 ≤ ⟪w.fst - p, v.fst - a⟫_ℝ + ⟪w.snd - q, v.snd - b⟫_ℝ at hr
      linarith
    refine ⟨hfst, ?_⟩
    apply FBF.mem_of_monotone_related B hB w.snd v.snd
    intro q b hb
    have hr := hrel (WithLp.toLp 2 (w.fst, q)) (WithLp.toLp 2 (v.fst, b)) ⟨hfst, hb⟩
    rw [WithLp.prod_inner_apply] at hr
    change 0 ≤ ⟪w.fst - w.fst, v.fst - v.fst⟫_ℝ + ⟪w.snd - q, v.snd - b⟫_ℝ at hr
    simpa only [sub_self, inner_zero_left, zero_add] using hr

/-- Maximality of the translated primal/inverse-dual product operator `M`. -/
theorem opM_maximal (A : H → Set H) (B : G → Set G)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B) (z : H) (r : G) :
    IsMaximalMonotone (opM A B z r) := by
  have he : opM A B z r = productOp (fun x => {u | u + z ∈ A x})
      (fun v => {w | w + -r ∈ opInv B v}) := by
    funext x
    apply Set.ext
    intro u
    change (u.fst + z ∈ A x.fst ∧ u.snd - r ∈ opInv B x.snd) ↔
      (u.fst + z ∈ A x.fst ∧ u.snd + -r ∈ opInv B x.snd)
    simp only [sub_eq_add_neg]
  rw [he]
  exact maximal_product (fun x => {u | u + z ∈ A x})
      (fun v => {w | w + -r ∈ opInv B v})
      (maximal_outputShift A hA z) (maximal_outputShift (opInv B) (maximal_inv B hB) (-r))

end Product

/-- An everywhere-defined map with zero monotonicity pairing may be added to a
maximal monotone graph. In particular this applies to any linear skew map. -/
theorem maximal_addSingle_skew (A : E → Set E) (hA : IsMaximalMonotone A)
    (S : E → E) (hskew : ∀ x y, ⟪x - y, S x - S y⟫_ℝ = 0) :
    IsMaximalMonotone (addSingle A S) := by
  apply maximal_of_monotone_related
  · intro x y u v hu hv
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨b, hb, rfl⟩ := hv
    have he : (a + S x) - (b + S y) = (a - b) + (S x - S y) := by abel
    rw [he, inner_add_right, hskew x y, add_zero]
    exact hA.1 x y a b ha hb
  · intro w v hrel
    have hv : v - S w ∈ A w := by
      apply FBF.mem_of_monotone_related A hA w (v - S w)
      intro p a ha
      have hr := hrel p (a + S p) ⟨a, ha, rfl⟩
      have he : v - (a + S p) = ((v - S w) - a) + (S w - S p) := by abel
      rw [he, inner_add_right, hskew w p, add_zero] at hr
      exact hr
    exact ⟨v - S w, hv, by abel⟩

end MonoSkew.Structure


open InnerProductSpace
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR MonoSkew.Main

namespace MonoSkew.Structure
variable {H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

noncomputable def skewCLM (L : H →L[ℝ] G) : K H G →L[ℝ] K H G :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ H G).symm.toContinuousLinearMap.comp
    ((L.adjoint.comp (WithLp.sndL 2 ℝ H G)).prod
      (-(L.comp (WithLp.fstL 2 ℝ H G))))

theorem skewCLM_apply (L : H →L[ℝ] G) (p : K H G) : skewCLM L p = opS L p := rfl

theorem skewCLM_adjoint (L : H →L[ℝ] G) : (skewCLM L).adjoint = -skewCLM L := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change ⟪-(opS L x), y⟫_ℝ = ⟪x, opS L y⟫_ℝ
  simp only [inner_neg_left, WithLp.prod_inner_apply, opS, WithLp.toLp_fst,
    WithLp.toLp_snd, inner_neg_left, inner_neg_right,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  simp only [WithLp.fst, WithLp.snd]
  ring

theorem skewCLM_norm (L : H →L[ℝ] G) : ‖skewCLM L‖ = ‖L‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro p
    have h1 := L.adjoint.le_opNorm p.snd
    have h2 := L.le_opNorm p.fst
    have hn : ‖L.adjoint‖ = ‖L‖ := ContinuousLinearMap.adjoint.norm_map L
    rw [hn] at h1
    have hs1 := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr h1
    have hs2 := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr h2
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    change ‖L.adjoint p.snd‖ ^ 2 + ‖-(L p.fst)‖ ^ 2 ≤ _
    rw [norm_neg]
    nlinarith
  · apply L.opNorm_le_bound (norm_nonneg (skewCLM L))
    intro x
    have h := (skewCLM L).le_opNorm (WithLp.toLp 2 (x, (0 : G)))
    simpa [skewCLM_apply, opS, WithLp.norm_toLp_fst, WithLp.norm_toLp_snd] using h

theorem opS_self_inner (L : H →L[ℝ] G) (p : K H G) : ⟪p, opS L p⟫_ℝ = 0 := by
  simp only [WithLp.prod_inner_apply, opS, WithLp.toLp_fst, WithLp.toLp_snd,
    inner_neg_right, ContinuousLinearMap.adjoint_inner_right]
  change ⟪L p.fst, p.snd⟫_ℝ + -⟪p.snd, L p.fst⟫_ℝ = 0
  rw [real_inner_comm (L p.fst) p.snd]
  ring

theorem opS_monotone (L : H →L[ℝ] G) : IsMonotoneOp (fun p => ({opS L p} : Set (K H G))) := by
  intro x y u v hu hv
  obtain rfl := hu
  obtain rfl := hv
  have he : opS L x - opS L y = opS L (x-y) := (map_sub (skewCLM L) x y).symm
  rw [he, opS_self_inner]

end MonoSkew.Structure


open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

open MonoSkew.Main

/-- Proposition 2.7(i)–(iii) (p. 8): in the setting of Problems 1.1 and 1.2, `M` is maximally
monotone; `S` is a bounded linear operator on `𝒦` with `S* = −S` and `‖S‖ = ‖L‖`; and
`M + S` is maximally monotone. -/
theorem solution {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (A : H → Set H) (B : G → Set G) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (L : H →L[ℝ] G) (z : H) (r : G) :
    IsMaximalMonotone (opM A B z r) ∧
    (∃ T : K H G →L[ℝ] K H G, (∀ p, T p = opS L p) ∧
      ContinuousLinearMap.adjoint T = -T ∧ ‖T‖ = ‖L‖) ∧
    IsMaximalMonotone (addSingle (opM A B z r) (opS L)) := by
  have hm := MonoSkew.Structure.opM_maximal A B hA hB z r
  refine ⟨hm, ⟨MonoSkew.Structure.skewCLM L, MonoSkew.Structure.skewCLM_apply L,
    MonoSkew.Structure.skewCLM_adjoint L, MonoSkew.Structure.skewCLM_norm L⟩, ?_⟩
  apply MonoSkew.Structure.maximal_addSingle_skew (opM A B z r) hm (opS L)
  intro x y
  have he : opS L x - opS L y = opS L (x - y) :=
    (map_sub (MonoSkew.Structure.skewCLM L) x y).symm
  rw [he, MonoSkew.Structure.opS_self_inner]


