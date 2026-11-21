-- Prove2me | solution 1 for MasulloGRH.nuclear_quasinuclear_domination
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:10:47.038378+00:00
-- url     : https://prove2.me/submissions/688e5d39-cafc-4279-9810-6bfcfdd2138f

import Theorems.Thm_MasulloGRH_schwartz_kernel_theorem

open Set Filter Topology MasulloGRH

private theorem domination_of_normed_map {E H : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsNuclear E)
    [SeminormedAddCommGroup H] [NormedSpace ℂ H] (j : E →L[ℂ] H) :
    ∃ (q : Seminorm ℂ E) (f : ℕ → StrongDual ℂ E) (c : ℕ → ℝ),
      Continuous q ∧ (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n x, ‖f n x‖ ≤ q x) ∧
      ∀ x, ‖j x‖ ≤ ∑' n, c n * ‖f n x‖ := by
  obtain ⟨ι, _, P, hP⟩ := hE.1.1
  let := hP.topologicalAddGroup
  let := hP.continuousSMul
  let := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let F := StrongDual ℂ H
  have hF : IsHLCS F := ⟨⟨_, ⟨⟨0, continuous_zero⟩⟩, _, PolynormableSpace.withSeminorms ℂ F⟩, inferInstance⟩
  let B : E →ₗ[ℂ] F →ₗ[ℂ] ℂ :=
    (ContinuousLinearMap.coeLM ℂ).comp ((ContinuousLinearMap.apply ℂ ℂ).toLinearMap.comp j.toLinearMap)
  have hB : Continuous (fun z : E × F => B z.1 z.2) :=
    continuous_snd.clm_apply (j.continuous.comp continuous_fst)
  obtain ⟨φ,ψ,c,hφ,hψ,hc,hexp⟩ := schwartz_kernel_theorem E F hE hF B hB
  have hseminorm := ((norm_withSeminorms ℂ ℂ).equicontinuous_TFAE
    (fun n => (φ n).toLinearMap)).out 1 3
  obtain ⟨q,hq,hφq⟩ := hseminorm.mp hφ (0 : Fin 1)
  obtain ⟨C,hC,hψC⟩ := ((NormedSpace.equicontinuous_TFAE ψ).out 1 4).mp hψ
  have hbound (i : ℕ) (x : E) : ‖φ i x‖ ≤ q x := hφq i x
  refine ⟨q,φ,(fun i => ‖c i‖ * C),hq,fun i => mul_nonneg (norm_nonneg _) hC,
    hc.mul_right C,hbound,?_⟩
  intro x
  obtain ⟨g,hg,hgx⟩ := exists_dual_vector'' ℂ (j x)
  have ht := (hexp {x} {g} (Bornology.isVonNBounded_singleton x)
    (Bornology.isVonNBounded_singleton g)).tendsto_at (x := (x,g)) (by simp)
  change Tendsto (fun N => ∑ i ∈ Finset.range N, c i * φ i x * ψ i g) atTop (𝓝 (g (j x))) at ht
  rw [hgx] at ht
  have hlim := ht.norm
  simp only [RCLike.norm_ofReal, abs_norm] at hlim
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro N
  have hs : Summable fun i => (‖c i‖ * C) * ‖φ i x‖ :=
    Summable.of_nonneg_of_le (fun _ => by positivity)
      (fun i => mul_le_mul_of_nonneg_left (hbound i x) (by positivity))
      ((hc.mul_right C).mul_right (q x))
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun i (_ : i ∈ Finset.range N) => ?_)).trans
    (hs.sum_le_tsum _ (fun _ _ => by positivity)))
  rw [norm_mul, norm_mul, mul_right_comm _ C]
  exact mul_le_mul_of_nonneg_left ((hψC i g).trans ((mul_le_mul_of_nonneg_left hg hC).trans_eq (mul_one C)))
    (by positivity)

-- Keep the original topology on E while giving a second copy the pseudonorm p.
private def SeminormModel {E : Type*} [AddCommGroup E] [Module ℂ E] (_ : Seminorm ℂ E) := E

private noncomputable instance modelGroup {E : Type*} [AddCommGroup E] [Module ℂ E]
    (p : Seminorm ℂ E) : SeminormedAddCommGroup (SeminormModel p) := p.toAddGroupSeminorm.toSeminormedAddCommGroup

private noncomputable instance modelSpace {E : Type*} [AddCommGroup E] [Module ℂ E]
    (p : Seminorm ℂ E) : NormedSpace ℂ (SeminormModel p) :=
  { (inferInstance : Module ℂ E) with norm_smul_le := fun a x => (map_smul_eq_mul p a x).le }

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsNuclear E) (p : Seminorm ℂ E) (hp : Continuous p) :
    ∃ (q : Seminorm ℂ E) (f : ℕ → StrongDual ℂ E) (c : ℕ → ℝ),
      Continuous q ∧ (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n x, ‖f n x‖ ≤ q x) ∧
      ∀ x, p x ≤ ∑' n, c n * ‖f n x‖ := by
  obtain ⟨ι, _, P, hP⟩ := hE.1.1
  let := hP.topologicalAddGroup
  let j : E →ₗ[ℂ] SeminormModel p := LinearMap.id
  have hj : Continuous j := by
    apply continuous_of_continuousAt_zero j
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hs := (hp.tendsto 0).eventually_lt_const (show p 0 < ε by simpa using hε)
    filter_upwards [hs] with x hx
    change dist (j x) (j 0) < ε
    rw [map_zero, dist_zero_right]
    exact hx
  exact domination_of_normed_map hE (⟨j,hj⟩ : E →L[ℂ] SeminormModel p)
