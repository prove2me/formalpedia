-- Prove2me | solution 1 for MasulloGRH.strictLF_quotient_regular_of_condM_of_quasiComplete
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:03:01.957221+00:00
-- url     : https://prove2.me/submissions/68370d14-db8e-4d0e-a3c6-8cfb7f54ba75

import Theorems.Thm_MasulloGRH_strictLF_hlcs_and_closed_steps
import Theorems.Thm_MasulloGRH_nuclear_of_countable_inductive_limit
import Theorems.Thm_MasulloGRH_nuclear_quotient
import Theorems.Thm_MasulloGRH_frechet_stage_image_lifts_in_strict_quotient
import Theorems.Thm_MasulloGRH_strictLF_quotient_regular_of_bounded_lifting

set_option autoImplicit false

open MasulloGRH Filter Set Topology TopologicalSpace Bornology
open scoped ENNReal Uniformity

universe u

private theorem banach_isFrechet (H : Type u) [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] : IsFrechet H := by
  refine ⟨⟨_, ⟨⟨0, continuous_const⟩⟩, _, PolynormableSpace.withSeminorms ℂ H⟩,
    ⟨inferInstance, ?_⟩, inferInstance⟩
  intro l hl
  apply CompleteSpace.complete
  apply (IsUniformAddGroup.cauchy_iff_tendsto l).mpr
  refine ⟨hl.1, fun U hU => ?_⟩
  obtain ⟨A, hA, hAA⟩ := hl.2 U hU
  exact Filter.mem_prod_iff.mpr ⟨A, hA, A, hA, fun a ha => hAA _ ha.1 _ ha.2⟩

/-- Absolute summability of the scalar coefficients makes the partial sums a bounded
Cauchy net in the target. Quasi-completeness supplies its limit. -/
private theorem bounded_family_image_of_l1_ball {G : Type*} [AddCommGroup G]
    [Module ℂ G] [TopologicalSpace G] (hG : IsHLCS G) (hQC : IsQuasiComplete G)
    {B : Set G} (hB : IsVonNBounded ℂ B) :
    ∃ T : lp (fun _ : B => ℂ) 1 →L[ℂ] G, B ⊆ T '' Metric.closedBall 0 1 := by
  classical
  obtain ⟨ι, _, P, hP⟩ := hG.1
  let : IsTopologicalAddGroup G := hP.topologicalAddGroup
  let : ContinuousSMul ℂ G := hP.continuousSMul
  let : T2Space G := hQC.1
  let : PolynormableSpace ℂ G := hP.toPolynormableSpace
  let : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  let : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  let H := lp (fun _ : B => ℂ) 1
  let a (v : H) (i : B) : G := v i • (i : G)
  have hℓ (v : H) : HasSum (fun i : B => ‖v i‖) ‖v‖ := by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using
      (lp.hasSum_norm (p := (1 : ℝ≥0∞)) (by norm_num) v)
  have hbound (p : Seminorm ℂ G) (hp : Continuous p) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ B, p x ≤ C := by
    obtain ⟨C, hC, hx⟩ :=
      ((PolynormableSpace.withSeminorms ℂ G).isVonNBounded_iff_seminorm_bounded.mp hB) ⟨p, hp⟩
    exact ⟨C, hC.le, fun x hx' => (hx x hx').le⟩
  have hsumBound (p : Seminorm ℂ G) (C : ℝ) (hC : ∀ x ∈ B, p x ≤ C)
      (v : H) (s : Finset B) :
      p (∑ i ∈ s, a v i) ≤ ∑ i ∈ s, C * ‖v i‖ := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      refine (map_add_le_add p _ _).trans (add_le_add ?_ ih)
      change p (v i • (i : G)) ≤ _
      rw [map_smul_eq_mul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hC i i.property) (norm_nonneg _)
  have hPBounded (v : H) :
      IsVonNBounded ℂ (range fun s : Finset B => ∑ i ∈ s, a v i) := by
    apply hP.isVonNBounded_iff_seminorm_bounded.mpr
    intro j
    obtain ⟨C, hC, hC'⟩ := hbound (P j) (hP.continuous_seminorm j)
    refine ⟨C * ‖v‖ + 1, by positivity, ?_⟩
    rintro _ ⟨s, rfl⟩
    have hCu := (hℓ v).mul_left C
    have hsum : (∑ i ∈ s, C * ‖v i‖) ≤ C * ‖v‖ :=
      (hCu.summable.sum_le_tsum s (fun i _ => mul_nonneg hC (norm_nonneg _))).trans_eq hCu.tsum_eq
    exact ((hsumBound (P j) C hC' v s).trans hsum).trans_lt (by linarith)
  have hCauchy (v : H) : CauchySeq (fun s : Finset B => ∑ i ∈ s, a v i) := by
    apply cauchySeq_finset_iff_sum_vanishing.mpr
    intro U hU
    obtain ⟨⟨I, ε⟩, hε, hU'⟩ := hP.hasBasis_zero_ball.mem_iff.mp hU
    let p := I.sup P
    have hp : Continuous p :=
      Seminorm.continuous (hP.hasBasis_zero_ball.mem_of_mem (i := (I, ε)) hε)
    obtain ⟨C, hC, hC'⟩ := hbound p hp
    have hs : Summable (fun i : B => C * ‖v i‖) := ((hℓ v).mul_left C).summable
    obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp hs ε hε
    refine ⟨s, fun t hst => hU' ?_⟩
    change (∑ i ∈ t, a v i) ∈ p.ball 0 ε
    rw [Seminorm.ball_zero_eq]
    refine lt_of_le_of_lt (hsumBound p C hC' v t) ?_
    simpa only [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg hC (norm_nonneg (v i)))]
      using hs t hst
  have hHasSum (v : H) : ∃ z : G, HasSum (a v) z := by
    let g : Finset B → G := fun s => ∑ i ∈ s, a v i
    let l : Filter G := Filter.map g atTop
    obtain ⟨hne, hd⟩ := (IsUniformAddGroup.cauchy_iff_tendsto l).mp (hCauchy v)
    have hl : IsCauchyFilter l := by
      refine ⟨hne, fun U hU => ?_⟩
      obtain ⟨s, hs, t, ht, hst⟩ := Filter.mem_prod_iff.mp (hd hU)
      exact ⟨s ∩ t, inter_mem hs ht, fun x hx y hy => hst
        (show (x, y) ∈ s ×ˢ t from ⟨hx.1, hy.2⟩)⟩
    exact hQC.2 l hl ⟨range g, by simp [l], hPBounded v⟩
  choose z hz using hHasSum
  let T₀ : H →ₗ[ℂ] G :=
    { toFun := z
      map_add' := fun v w => (hz (v + w)).unique <|
        (HasSum.add (hz v) (hz w)).congr_fun (fun i => (add_smul (v i) (w i) (i : G)))
      map_smul' := fun c v => (hz (c • v)).unique <|
        ((hz v).const_smul c).congr_fun (fun i => (mul_smul c (v i) (i : G))) }
  have hT : Continuous T₀ := by
    apply continuous_of_continuousAt_zero T₀
    rw [ContinuousAt, map_zero]
    apply hP.hasBasis_zero_ball.tendsto_right_iff.mpr
    rintro ⟨I, ε⟩ hε
    let p := I.sup P
    have hp : Continuous p :=
      Seminorm.continuous (hP.hasBasis_zero_ball.mem_of_mem (i := (I, ε)) hε)
    obtain ⟨C, hC, hC'⟩ := hbound p hp
    have hzero : Tendsto (fun v : H => C * ‖v‖) (𝓝 0) (𝓝 0) := by
      have hn : Continuous (fun v : H => C * ‖v‖) := continuous_const.mul continuous_norm
      simpa only [norm_zero, mul_zero] using hn.tendsto 0
    filter_upwards [hzero (Iio_mem_nhds hε)] with v hv
    change T₀ v ∈ p.ball 0 ε
    rw [Seminorm.ball_zero_eq]
    change C * ‖v‖ < ε at hv
    refine lt_of_le_of_lt ?_ hv
    apply le_of_tendsto (hp.continuousAt.tendsto.comp (hz v))
    filter_upwards with s
    have hCu := (hℓ v).mul_left C
    exact (hsumBound p C hC' v s).trans
      ((hCu.summable.sum_le_tsum s (fun i _ => mul_nonneg hC (norm_nonneg _))).trans_eq hCu.tsum_eq)
  let T : H →L[ℂ] G := ⟨T₀, hT⟩
  refine ⟨T, ?_⟩
  intro x hx
  let i : B := ⟨x, hx⟩
  let v : H := lp.single 1 i 1
  refine ⟨v, ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, lp.norm_single (by norm_num)]
    simp
  · change z v = x
    apply (hz v).unique
    have hsingle : HasSum (a v) (a v i) := hasSum_single i (fun j hj => by
      change (lp.single 1 i (1 : ℂ) : H) j • (j : G) = 0
      simp [lp.single_apply, Pi.single_eq_of_ne hj])
    simpa [a, v, i, lp.single_apply] using hsingle

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E)) (hQ : IsQuasiComplete (E ⧸ V)) :
    ∀ B : Set (E ⧸ V), IsVonNBounded ℂ B →
      ∃ (n : ℕ) (A : Set (X n ⧸ V.comap (X n).subtype)), IsVonNBounded ℂ A ∧
        B ⊆ Submodule.mapQ (V.comap (X n).subtype) V (X n).subtype le_rfl '' A := by
  have hE := (strictLF_hlcs_and_closed_steps E X hmono hexh (fun n => (hX n).1) htop).1
  have hn : IsNuclear E :=
    nuclear_of_countable_inductive_limit E hE X (fun _ => inferInstance) hexh
      (fun n => ⟨hmono (Nat.le_succ n), continuous_subtype_val.subtype_mk _⟩)
      (fun n => (hX n).2) htop
  have hG := (nuclear_quotient E hn V hV).1
  let : T2Space (E ⧸ V) := hQ.1
  apply strictLF_quotient_regular_of_bounded_lifting E X hmono hexh hX htop V hV
  intro B hB
  obtain ⟨T, hT⟩ := bounded_family_image_of_l1_ball hG hQ hB
  obtain ⟨A, hA, hcover⟩ := frechet_stage_image_lifts_in_strict_quotient
    E _ ⟨X, hmono, hexh, hX, htop⟩ V hV (banach_isFrechet _) T
    (Metric.closedBall 0 1) (NormedSpace.isVonNBounded_closedBall ℂ _ _)
  exact ⟨A, hA, hT.trans hcover⟩
