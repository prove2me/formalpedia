-- Prove2me | solution 1 for MonoSkew.Main.proposition_2_8_i
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-23T13:18:46.892368+00:00
-- url     : https://prove2.me/submissions/8cbc44a3-44d6-49cb-8504-cc864d3ba70e

import Mathlib
import Definitions.Def_MonoSkew_Main_Basic
import Theorems.Thm_MonoSkew_Main_proposition_2_7_i_iii



/-! Standard weak-strong sequential closedness of a maximal monotone graph,
with the bound on the weakly convergent sequence supplied explicitly.
No completeness or uniform boundedness theorem is needed. -/

open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence

namespace MonoSkew.ZeroSetProof

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

end MonoSkew.ZeroSetProof


open InnerProductSpace ThreeOpSplitting.Convergence

namespace MonoSkew.Structure
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem zero_set_eq_halfspaces (A : E → Set E) (hA : IsMaximalMonotone A) :
    zer A = ⋂ y : E, ⋂ v : E, ⋂ (_ : v ∈ A y), {x : E | 0 ≤ ⟪x-y, -v⟫_ℝ} := by
  ext x
  simp only [Set.mem_iInter, Set.mem_setOf_eq]
  constructor
  · intro hx y v hv
    simpa only [zero_sub] using hA.1 x y 0 v hx hv
  · intro hx
    apply MonoSkew.ZeroSetProof.mem_of_monotone_related A hA x 0
    simpa only [zero_sub] using hx

theorem maximal_zero_set_closed (A : E → Set E) (hA : IsMaximalMonotone A) :
    IsClosed (zer A) := by
  rw [zero_set_eq_halfspaces A hA]
  apply isClosed_iInter
  intro y
  apply isClosed_iInter
  intro v
  apply isClosed_iInter
  intro hv
  exact isClosed_le continuous_const ((continuous_id.sub continuous_const).inner continuous_const)

theorem maximal_zero_set_convex (A : E → Set E) (hA : IsMaximalMonotone A) :
    Convex ℝ (zer A) := by
  intro x hx y hy a b ha hb hab
  apply MonoSkew.ZeroSetProof.mem_of_monotone_related A hA _ 0
  intro w v hv
  have h1 := hA.1 x w 0 v hx hv
  have h2 := hA.1 y w 0 v hy hv
  have he : a • x + b • y - w = a • (x-w) + b • (y-w) := by
    linear_combination (norm := module) hab • w
  rw [he, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  exact add_nonneg (mul_nonneg ha h1) (mul_nonneg hb h2)

end MonoSkew.Structure



open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open MonoSkew.Main

/-- Proposition 2.8(i) (p. 8): in the setting of Problems 1.1 and 1.2, `zer(M + S)` is a closed
convex subset of `𝒫 × 𝒟`. -/
theorem solution {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (A : H → Set H) (B : G → Set G) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (L : H →L[ℝ] G) (z : H) (r : G) :
    IsClosed (zer (addSingle (opM A B z r) (opS L))) ∧
    Convex ℝ (zer (addSingle (opM A B z r) (opS L))) ∧
    ∀ p ∈ zer (addSingle (opM A B z r) (opS L)),
      p.fst ∈ primalSet A B L z r ∧ p.snd ∈ dualSet A B L z r := by
  have hmax := (proposition_2_7_i_iii A B hA hB L z r).2.2
  refine ⟨MonoSkew.Structure.maximal_zero_set_closed _ hmax,
    MonoSkew.Structure.maximal_zero_set_convex _ hmax, ?_⟩
  have hpr : ∀ x, x ∈ primalSet A B L z r ↔
      ∃ v, z - L.adjoint v ∈ A x ∧ v ∈ B (L x - r) := by
    intro x
    constructor
    · rintro ⟨u, hu, w, ⟨v, hv, rfl⟩, he⟩
      exact ⟨v, by convert hu using 1 <;> (rw [he]; abel), hv⟩
    · rintro ⟨v, hv, hb⟩
      exact ⟨z - L.adjoint v, hv, L.adjoint v, ⟨v, hb, rfl⟩, by abel⟩
  have hdu : ∀ v, v ∈ dualSet A B L z r ↔
      ∃ x, z - L.adjoint v ∈ A x ∧ v ∈ B (L x - r) := by
    intro v
    constructor
    · rintro ⟨x, hx, t, ht, he⟩
      refine ⟨x, hx, ?_⟩
      have ht' : t = L x - r := by linear_combination (norm := module) -he
      simpa only [ht', opInv, Set.mem_setOf_eq] using ht
    · rintro ⟨x, hx, hv⟩
      exact ⟨x, hx, L x - r, hv, by abel⟩
  have hze : ∀ w : K H G, w ∈ zer (addSingle (opM A B z r) (opS L)) ↔
      z - L.adjoint w.snd ∈ A w.fst ∧ w.snd ∈ B (L w.fst - r) := by
    intro w
    constructor
    · rintro ⟨u, ⟨hu, hv⟩, he⟩
      have he1 := congrArg WithLp.fst he
      have he2 := congrArg WithLp.snd he
      change 0 = u.fst + L.adjoint w.snd at he1
      change 0 = u.snd + -(L w.fst) at he2
      have hu' : u.fst + z = z - L.adjoint w.snd := by linear_combination (norm := module) -he1
      have hv' : u.snd - r = L w.fst - r := by linear_combination (norm := module) -he2
      exact ⟨by simpa only [hu'] using hu, by simpa only [opInv, hv', Set.mem_setOf_eq] using hv⟩
    · rintro ⟨hx, hv⟩
      refine ⟨WithLp.toLp 2 (-L.adjoint w.snd, L w.fst), ?_, ?_⟩
      · constructor
        · change -L.adjoint w.snd + z ∈ A w.fst
          simpa only [sub_eq_add_neg, add_comm] using hx
        · exact hv
      · apply WithLp.ofLp_injective
        apply Prod.ext <;> simp [opS]
  intro p hp
  have hw := (hze p).mp hp
  exact ⟨(hpr p.fst).mpr ⟨p.snd, hw⟩, (hdu p.snd).mpr ⟨p.fst, hw⟩⟩

