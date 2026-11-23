-- Prove2me | solution 1 for LogConcaveLattice.Lift.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:04:48.296025+00:00
-- url     : https://prove2.me/submissions/5df4039f-5ca4-42a0-8d50-8b18e7c05712

import Mathlib
import Definitions.Def_LogConcaveLattice_Lift_Lattice

open scoped RealInnerProductSpace
open LogConcaveLattice.Lift

namespace AuxLemma22

lemma starProj_mem {n : ℕ} (E : Submodule ℝ (V n)) (x : V n) :
    E.starProjection x ∈ E :=
  (E.orthogonalProjectionOnto x).2

lemma starProj_eq_zero_iff {n : ℕ} (E : Submodule ℝ (V n)) (x : V n) :
    E.starProjection x = 0 ↔ x ∈ Eᗮ := by
  have hdecomp := E.starProjection_add_starProjection_orthogonal x
  constructor
  · intro h0
    rw [h0, zero_add] at hdecomp
    rw [← hdecomp]
    exact starProj_mem Eᗮ x
  · intro hx
    have hself : Eᗮ.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
    rw [hself] at hdecomp
    simpa using hdecomp

lemma norm_starProj_le {n : ℕ} (E : Submodule ℝ (V n)) (x : V n) :
    ‖E.starProjection x‖ ≤ ‖x‖ := by
  have hdecomp := (E.starProjection_add_starProjection_orthogonal x).symm
  have horth : ⟪E.starProjection x, Eᗮ.starProjection x⟫ = 0 := by
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal' E (Eᗮ.starProjection x)).mp (starProj_mem Eᗮ x)
      (E.starProjection x) (starProj_mem E x)
  have hsq : ‖x‖ ^ 2 = ‖E.starProjection x‖ ^ 2 + ‖Eᗮ.starProjection x‖ ^ 2 := by
    conv_lhs => rw [hdecomp]
    rw [norm_add_sq_real, horth]
    ring
  nlinarith [sq_nonneg ‖Eᗮ.starProjection x‖, norm_nonneg x, norm_nonneg (E.starProjection x)]

lemma covering_bound {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (L : Submodule ℤ W) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ R : ℝ, 0 < R ∧ ∀ x : W, ∃ l ∈ L, ‖(l : W) - x‖ ≤ R := by
  let b := Module.Free.chooseBasis ℤ L
  let B := b.ofZLatticeBasis ℝ L
  refine ⟨1 + ∑ i, ‖(B i : W)‖, ?_, ?_⟩
  · have hsum : 0 ≤ ∑ i, ‖(B i : W)‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    linarith
  · intro x
    let c : Module.Free.ChooseBasisIndex ℤ L → ℝ := fun i => B.repr x i
    let l : L := ∑ i, ⌊c i⌋ • b i
    refine ⟨(l : W), l.2, ?_⟩
    have hl : (l : W) = ∑ i, (⌊c i⌋ : ℝ) • B i := by
      rw [AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [SetLike.val_smul, ← Int.cast_smul_eq_zsmul ℝ]
      simp [B]
    have hx : (∑ i, c i • B i) = x := B.sum_repr x
    have hdiff : (l : W) - x = ∑ i, ((⌊c i⌋ : ℝ) - c i) • B i := by
      calc
        (l : W) - x = (∑ i, (⌊c i⌋ : ℝ) • B i) - (∑ i, c i • B i) := by rw [hl, hx]
        _ = ∑ i, ((⌊c i⌋ : ℝ) - c i) • B i := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [sub_smul]
    rw [hdiff]
    calc
      ‖∑ i, ((⌊c i⌋ : ℝ) - c i) • B i‖
          ≤ ∑ i, ‖((⌊c i⌋ : ℝ) - c i) • B i‖ := norm_sum_le _ _
      _ = ∑ i, |((⌊c i⌋ : ℝ) - c i)| * ‖B i‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ i, 1 * ‖B i‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          rw [abs_le]
          constructor
          · linarith [Int.lt_floor_add_one (c i)]
          · linarith [Int.floor_le (c i)]
      _ ≤ 1 + ∑ i, ‖B i‖ := by
          simp only [one_mul]
          linarith

lemma isClosed_of_discrete {n : ℕ} (H : Submodule ℤ (V n)) [DiscreteTopology H] :
    IsClosed (H : Set (V n)) :=
  H.toAddSubgroup.isClosed_of_discrete

lemma finite_inter_closedBall {n : ℕ} (H : Submodule ℤ (V n)) [DiscreteTopology H] (C : ℝ) :
    ((H : Set (V n)) ∩ Metric.closedBall 0 C).Finite := by
  have hcpt : IsCompact ((H : Set (V n)) ∩ Metric.closedBall 0 C) :=
    (isCompact_closedBall (0 : V n) C).inter_left (isClosed_of_discrete H)
  have hsub : IsCompact ((Subtype.val : H → V n) ⁻¹' Metric.closedBall 0 C) := by
    rw [Topology.IsInducing.subtypeVal.isCompact_iff]
    convert hcpt using 1
    ext x
    simp [and_comm]
  have hfin : ((Subtype.val : H → V n) ⁻¹' Metric.closedBall 0 C).Finite :=
    hsub.finite_of_discrete
  convert hfin.image (Subtype.val : H → V n) using 1
  ext x
  simp [and_comm]

lemma discrete_of_latticeSubspace {n : ℕ} (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ]
    (E : Submodule ℝ (V n)) (hE : IsLatticeSubspace Λ Eᗮ) :
    DiscreteTopology (projLattice E Λ) := by
  let L₀ : Submodule ℤ Eᗮ := (interSubspace Λ Eᗮ).comap (Eᗮ.subtype.restrictScalars ℤ)
  have hL₀_disc : DiscreteTopology L₀ := by
    have hopen : IsOpen ({0} : Set Λ) :=
      discreteTopology_iff_isOpen_singleton_zero.mp inferInstance
    obtain ⟨δ, hδpos, hδ⟩ := Metric.isOpen_iff.mp hopen 0 (Set.mem_singleton 0)
    rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨δ, hδpos, fun y hy => ?_⟩
    have hy' : (⟨(y.1 : V n), y.2.1⟩ : Λ) ∈ Metric.ball (0 : Λ) δ := by
      simpa [Metric.mem_ball, Subtype.dist_eq] using hy
    have h0 : (⟨(y.1 : V n), y.2.1⟩ : Λ) = 0 := Set.mem_singleton_iff.mp (hδ hy')
    have hval : ((y : Eᗮ) : V n) = 0 := congrArg (fun u : Λ => (u : V n)) h0
    exact Subtype.ext (Subtype.ext hval)
  have : DiscreteTopology L₀ := hL₀_disc
  have hL₀_lat : IsZLattice ℝ L₀ := by
    refine ⟨?_⟩
    apply Submodule.map_injective_of_injective Eᗮ.injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Eᗮ.range_subtype]
    have hset : Eᗮ.subtype '' (L₀ : Set Eᗮ) = (interSubspace Λ Eᗮ : Set (V n)) := by
      ext x
      constructor
      · rintro ⟨⟨y, hyE⟩, hyL, rfl⟩
        exact hyL
      · intro hx
        exact ⟨⟨x, hx.2⟩, hx, rfl⟩
    rw [hset]
    exact hE
  have : IsZLattice ℝ L₀ := hL₀_lat
  obtain ⟨R, hRpos, hR⟩ := covering_bound L₀
  have hFfin : (((Λ : Set (V n)) ∩ Metric.closedBall 0 (R + 1))).Finite :=
    finite_inter_closedBall Λ (R + 1)
  classical
  let F := hFfin.toFinset
  let Fpos := F.filter (fun z => E.starProjection z ≠ 0)
  let imgs := Fpos.image (fun z => ‖E.starProjection z‖)
  have himgs_pos : ∀ r ∈ imgs, 0 < r := by
    intro r hr
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hr
    exact norm_pos_iff.mpr (Finset.mem_filter.mp hz).2
  obtain ⟨ε, hεpos, hε1, hεle⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ r ∈ imgs, ε ≤ r := by
    by_cases hne : imgs.Nonempty
    · refine ⟨min 1 (imgs.min' hne), ?_, min_le_left _ _, fun r hr => ?_⟩
      · exact lt_min zero_lt_one (himgs_pos _ (imgs.min'_mem hne))
      · exact le_trans (min_le_right _ _) (imgs.min'_le r hr)
    · refine ⟨1, zero_lt_one, le_rfl, fun r hr => False.elim (hne ⟨r, hr⟩)⟩
  rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_iff]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  refine ⟨ε, hεpos, fun y hy => ?_⟩
  rw [Set.mem_singleton_iff]
  have hynorm : ‖(y : V n)‖ < ε := by
    simpa [Subtype.dist_eq, dist_zero_right] using hy
  obtain ⟨l, hlΛ, hly⟩ : ∃ l ∈ Λ, E.starProjection l = (y : V n) := by
    simpa [projLattice] using y.2
  obtain ⟨μ₀, hμ₀, hμdist⟩ := hR ⟨Eᗮ.starProjection l, starProj_mem Eᗮ l⟩
  have hμ_mem : (μ₀ : V n) ∈ interSubspace Λ Eᗮ := hμ₀
  let z : V n := l - (μ₀ : V n)
  have hzΛ : z ∈ Λ := Submodule.sub_mem Λ hlΛ hμ_mem.1
  have hμE : E.starProjection (μ₀ : V n) = 0 :=
    (starProj_eq_zero_iff E (μ₀ : V n)).mpr hμ_mem.2
  have hμEperp : Eᗮ.starProjection (μ₀ : V n) = (μ₀ : V n) :=
    Submodule.starProjection_eq_self_iff.mpr hμ_mem.2
  have hzE : E.starProjection z = (y : V n) := by
    simp [z, map_sub, hly, hμE]
  have hzEperp : Eᗮ.starProjection z = Eᗮ.starProjection l - (μ₀ : V n) := by
    simp [z, map_sub, hμEperp]
  have hznorm : ‖z‖ ≤ R + 1 := by
    have hdecomp : z = E.starProjection z + Eᗮ.starProjection z :=
      (E.starProjection_add_starProjection_orthogonal z).symm
    have hperp_le : ‖Eᗮ.starProjection z‖ ≤ R := by
      rw [hzEperp, norm_sub_rev]
      exact hμdist
    calc
      ‖z‖ = ‖E.starProjection z + Eᗮ.starProjection z‖ := congrArg norm hdecomp
      _ ≤ ‖E.starProjection z‖ + ‖Eᗮ.starProjection z‖ := norm_add_le _ _
      _ ≤ 1 + R := by
        rw [hzE]
        linarith
      _ = R + 1 := add_comm _ _
  have hzF : z ∈ F := by
    rw [Set.Finite.mem_toFinset]
    exact ⟨hzΛ, by simpa [Metric.mem_closedBall, dist_zero_right] using hznorm⟩
  by_contra hy0
  have hyval0 : (y : V n) ≠ 0 := fun h => hy0 (Subtype.ext h)
  have hzFpos : z ∈ Fpos := Finset.mem_filter.mpr ⟨hzF, by rw [hzE]; exact hyval0⟩
  have hmem : ‖(y : V n)‖ ∈ imgs := by
    rw [← hzE]
    exact Finset.mem_image_of_mem _ hzFpos
  linarith [hεle _ hmem]

lemma latticeSubspace_of_discrete {n : ℕ} (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (E : Submodule ℝ (V n)) [DiscreteTopology (projLattice E Λ)] :
    IsLatticeSubspace Λ Eᗮ := by
  classical
  let W : Submodule ℝ (V n) := Submodule.span ℝ (interSubspace Λ Eᗮ : Set (V n))
  change W = Eᗮ
  have hWle : W ≤ Eᗮ := by
    rw [Submodule.span_le]
    intro x hx
    exact hx.2
  by_contra hne
  have hex : ∃ x ∈ Eᗮ, x ∉ W := by
    by_contra hall
    apply hne
    apply le_antisymm hWle
    intro x hx
    by_contra hxW
    exact hall ⟨x, hx, hxW⟩
  obtain ⟨x, hxE, hxW⟩ := hex
  let w : V n := x - W.starProjection x
  have hwE : w ∈ Eᗮ := Submodule.sub_mem Eᗮ hxE (hWle (starProj_mem W x))
  have hwWperp : w ∈ Wᗮ := by
    have hdecomp := W.starProjection_add_starProjection_orthogonal x
    have hw_eq : w = Wᗮ.starProjection x := (eq_sub_of_add_eq' hdecomp).symm
    rw [hw_eq]
    exact starProj_mem Wᗮ x
  have hw0 : w ≠ 0 := by
    intro h0
    have : x = W.starProjection x := sub_eq_zero.mp h0
    exact hxW (this ▸ starProj_mem W x)
  let v : V n := ‖w‖⁻¹ • w
  have hvE : v ∈ Eᗮ := Eᗮ.smul_mem _ hwE
  have hvWperp : v ∈ Wᗮ := Wᗮ.smul_mem _ hwWperp
  have hvnorm : ‖v‖ = 1 := norm_smul_inv_norm hw0
  obtain ⟨C, hCpos, hC⟩ := covering_bound Λ
  have hSfin := finite_inter_closedBall (projLattice E Λ) C
  let SF := hSfin.toFinset
  let M := SF.card
  choose l hlΛ hldist using fun k : Fin (M + 1) => hC (((k : ℝ) * (3 * C)) • v)
  have hv_proj : E.starProjection v = 0 := (starProj_eq_zero_iff E v).mpr hvE
  have hl_mem : ∀ k : Fin (M + 1), E.starProjection (l k) ∈ SF := by
    intro k
    rw [Set.Finite.mem_toFinset]
    refine ⟨?_, ?_⟩
    · exact ⟨l k, hlΛ k, rfl⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      have hsub : E.starProjection (l k) =
          E.starProjection (l k - ((k : ℝ) * (3 * C)) • v) := by
        simp [map_sub, map_smul, hv_proj]
      rw [hsub]
      exact le_trans (norm_starProj_le E _) (hldist k)
  let f : Fin (M + 1) → SF := fun k => ⟨E.starProjection (l k), hl_mem k⟩
  have hcard : Fintype.card SF < Fintype.card (Fin (M + 1)) := by
    simp [M]
  obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm hfij.symm (lt_of_le_of_ne (le_of_not_gt hlt) hij.symm)
  have hproj_eq : E.starProjection (l i) = E.starProjection (l j) :=
    congrArg (fun u : SF => (u : V n)) hfij
  let μ : V n := l j - l i
  have hμΛ : μ ∈ Λ := Submodule.sub_mem Λ (hlΛ j) (hlΛ i)
  have hμE : μ ∈ Eᗮ := by
    rw [← starProj_eq_zero_iff E]
    simp [μ, map_sub, hproj_eq]
  have hμW : μ ∈ W := Submodule.subset_span ⟨hμΛ, hμE⟩
  have hinner0 : ⟪v, μ⟫ = 0 := (Submodule.mem_orthogonal' W v).mp hvWperp μ hμW
  let dj : V n := l j - ((j : ℝ) * (3 * C)) • v
  let di : V n := l i - ((i : ℝ) * (3 * C)) • v
  have hμ_decomp : μ = (((j : ℝ) - (i : ℝ)) * (3 * C)) • v + dj - di := by
    simp only [μ, dj, di]
    module
  have hvv : ⟪v, v⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hvnorm, one_pow]
  have hdj : |⟪v, dj⟫| ≤ C := by
    calc
      |⟪v, dj⟫| ≤ ‖v‖ * ‖dj‖ := abs_real_inner_le_norm v dj
      _ = 1 * ‖dj‖ := by rw [hvnorm]
      _ ≤ 1 * C := mul_le_mul_of_nonneg_left (hldist j) zero_le_one
      _ = C := one_mul C
  have hdi : |⟪v, di⟫| ≤ C := by
    calc
      |⟪v, di⟫| ≤ ‖v‖ * ‖di‖ := abs_real_inner_le_norm v di
      _ = 1 * ‖di‖ := by rw [hvnorm]
      _ ≤ 1 * C := mul_le_mul_of_nonneg_left (hldist i) zero_le_one
      _ = C := one_mul C
  have hij_ge : (1 : ℝ) ≤ (j : ℝ) - (i : ℝ) := by
    have hij_nat : (i : ℕ) + 1 ≤ (j : ℕ) := hlt
    have hij_real : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hij_nat
    linarith
  have hinner_expand : ⟪v, μ⟫ = ((j : ℝ) - (i : ℝ)) * (3 * C) + ⟪v, dj⟫ - ⟪v, di⟫ := by
    rw [hμ_decomp, inner_sub_right, inner_add_right, inner_smul_right, hvv, mul_one]
  have h1 : -C ≤ ⟪v, dj⟫ := neg_le_of_abs_le hdj
  have h2 : ⟪v, di⟫ ≤ C := le_of_abs_le hdi
  have h3 : 3 * C ≤ ((j : ℝ) - (i : ℝ)) * (3 * C) := by
    nlinarith
  linarith

end AuxLemma22

theorem solution (n : ℕ) (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (E : Submodule ℝ (V n)) :
    DiscreteTopology (projLattice E Λ) ↔ IsLatticeSubspace Λ Eᗮ :=
  ⟨fun h => @AuxLemma22.latticeSubspace_of_discrete n Λ _ _ E h,
   AuxLemma22.discrete_of_latticeSubspace Λ E⟩
