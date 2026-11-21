-- Prove2me | solution 2 for MasulloGRH.nuclear_dual_domination
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:22:41.034183+00:00
-- url     : https://prove2.me/submissions/6ed3b86a-34be-4136-8688-3b1738c2f24c

import Theorems.Thm_MasulloGRH_nuclear_banach_map_representation

open MasulloGRH Function Filter Topology UniformSpace
universe u

-- Keep the original topology on E while giving a second copy the pseudonorm p.
private def SeminormModel {E : Type*} [AddCommGroup E] [Module ℂ E] (_ : Seminorm ℂ E) := E

private noncomputable instance modelGroup {E : Type*} [AddCommGroup E] [Module ℂ E]
    (p : Seminorm ℂ E) : SeminormedAddCommGroup (SeminormModel p) := p.toAddGroupSeminorm.toSeminormedAddCommGroup

private noncomputable instance modelSpace {E : Type*} [AddCommGroup E] [Module ℂ E]
    (p : Seminorm ℂ E) : NormedSpace ℂ (SeminormModel p) :=
  { (inferInstance : Module ℂ E) with norm_smul_le := fun a x => (map_smul_eq_mul p a x).le }


private theorem continuous_of_seminorm_bound {E H : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [SeminormedAddCommGroup H] [NormedSpace ℂ H]
    (p : Seminorm ℂ E) (hp : Continuous p) (u : E →ₗ[ℂ] H) (hu : ∀ x, ‖u x‖ ≤ p x) :
    Continuous u := by
  apply continuous_of_continuousAt_zero u
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(hp.tendsto 0).eventually_lt_const (show p 0 < ε by simpa using hε)] with x hx
  simpa using (hu x).trans_lt hx

private noncomputable def weight (k : ℕ) : ℝ := 2 * (1 / 2 : ℝ) ^ k

private theorem weight_pos (k : ℕ) : 0 < weight k := by unfold weight; positivity

private theorem weight_summable : Summable weight :=
  (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_left 2

/-- Resolve a unit vector in the completion using normalized vectors in the dense subspace.
The geometric coefficient sequence is independent of the vector and of the two spaces. -/
private theorem dense_unit_series {X H : Type*} [SeminormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup H] [NormedSpace ℂ H] (j : X →ₗᵢ[ℂ] H) (hj : DenseRange j)
    (v : H) (hv : ‖v‖ ≤ 1) :
    ∃ y : ℕ → X, (∀ k, ‖y k‖ ≤ 1) ∧ HasSum (fun k => (weight k : ℂ) • j (y k)) v := by
  let e (k : ℕ) := (1 / 2 : ℝ) ^ k
  have he (k : ℕ) : 0 < e k := by dsimp [e]; positivity
  choose a ha using fun k => (Metric.denseRange_iff.mp hj v (e k) (he k))
  let z : ℕ → X := fun k => if k = 0 then 0 else a k
  have hz0 : z 0 = 0 := by simp [z]
  have hz (k : ℕ) : ‖j (z k) - v‖ ≤ e k := by
    by_cases h : k = 0
    · subst k; simpa [hz0,e] using hv
    · simpa [z,h,← dist_eq_norm,dist_comm] using (ha k).le
  have hinc (k : ℕ) : ‖z (k+1) - z k‖ ≤ weight k := by
    calc
      ‖z (k+1) - z k‖ = ‖j (z (k+1)) - j (z k)‖ := by rw [← map_sub, j.norm_map]
      _ ≤ ‖j (z (k+1)) - v‖ + ‖j (z k) - v‖ := by
        simpa only [norm_sub_rev v (j (z k))] using norm_sub_le_norm_sub_add_norm_sub (j (z (k+1))) v (j (z k))
      _ ≤ e (k+1) + e k := add_le_add (hz _) (hz _)
      _ ≤ weight k := by dsimp [e,weight]; rw [pow_succ]; nlinarith [he k]
  let y (k : ℕ) := ((weight k : ℂ)⁻¹) • (z (k+1) - z k)
  have hval (k : ℕ) : (weight k : ℂ) • j (y k) = j (z (k+1)) - j (z k) := by
    have hw : (weight k : ℂ) ≠ 0 := by exact_mod_cast (weight_pos k).ne'
    simp only [y, map_smul, smul_smul, mul_inv_cancel₀ hw, one_smul, map_sub]
  refine ⟨y,fun k => ?_,?_⟩
  · dsimp [y]
    rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (weight_pos k).le,
      inv_mul_le_iff₀ (weight_pos k),mul_one]
    exact hinc k
  · have hs : Summable fun k => ‖(weight k : ℂ) • j (y k)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by
        rw [hval,← map_sub,j.norm_map]; exact hinc k) weight_summable
    apply (hasSum_iff_tendsto_nat_of_summable_norm hs).mpr
    have ht : Tendsto (fun k => j (z k)) atTop (𝓝 v) := by
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      exact squeeze_zero (fun k => norm_nonneg _) hz
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    simpa only [hval, Finset.sum_range_sub (fun k => j (z k)), hz0, map_zero,sub_zero] using ht

theorem solution (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsNuclear E) (q : Seminorm ℂ E) (hq : Continuous q) :
    ∃ (p : Seminorm ℂ E) (y : ℕ → E) (c : ℕ → ℝ),
      Continuous p ∧ (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n, q (y n) ≤ 1) ∧
      ∀ f : StrongDual ℂ E, (∀ x, ‖f x‖ ≤ q x) →
        ∀ x, p x ≤ 1 → ‖f x‖ ≤ ∑' n, c n * ‖f (y n)‖ := by
  obtain ⟨ι,_,P,hP⟩ := hE.1.1
  let := hP.topologicalAddGroup
  let X := SeminormModel q
  let H := Completion X
  let j : E →ₗ[ℂ] X := LinearMap.id
  let J : E →L[ℂ] X := ⟨j, continuous_of_seminorm_bound q hq j (fun _ => le_rfl)⟩
  let i : X →ₗᵢ[ℂ] H := Completion.toComplₗᵢ
  have hi : DenseRange i := Completion.denseRange_coe
  let u : E →L[ℂ] H := i.toContinuousLinearMap.comp J
  obtain ⟨p,φ,v,c,hp,hφ,hv,hc,hu⟩ := nuclear_banach_map_representation E H hE u
  choose y hy hyexp using fun n => dense_unit_series i hi (v n) (hv n)
  let b (t : ℕ × ℕ) : ℝ := ‖c t.1‖ * weight t.2
  let e := Nat.pairEquiv.symm
  have hb : Summable b := hc.mul_of_nonneg weight_summable (fun n => norm_nonneg _) (fun k => (weight_pos k).le)
  refine ⟨p,(fun m => (y (e m).1 (e m).2 : E)),b ∘ e,hp,fun m => mul_nonneg (norm_nonneg _) (weight_pos _).le,
    e.summable_iff.mpr hb,fun m => hy _ _,?_⟩
  intro f hf x hx
  let fX : X →ₗ[ℂ] ℂ := f.toLinearMap
  let F : X →L[ℂ] ℂ := fX.mkContinuous 1 (fun z => by
    change ‖f (z : E)‖ ≤ 1 * q (z : E)
    rw [one_mul]
    exact hf _)
  let I : X →L[ℂ] H := i.toContinuousLinearMap
  let G : H →L[ℂ] ℂ := F.extend I
  have hG (z : X) : G (i z) = f (z : E) :=
    F.extend_eq hi (Completion.isUniformInducing_coe X) z
  let t (a : ℕ × ℕ) := b a * ‖f (y a.1 a.2 : E)‖
  have hty (n k : ℕ) : ‖f (y n k : E)‖ ≤ 1 := (hf _).trans (hy n k)
  have ht : Summable t := Summable.of_nonneg_of_le
    (fun a => mul_nonneg (mul_nonneg (norm_nonneg _) (weight_pos _).le) (norm_nonneg _))
    (fun a => mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (weight_pos _).le) (hty _ _)) hb
  have hg (n : ℕ) : ‖c n‖ * ‖G (v n)‖ ≤ ∑' k, t (n,k) := by
    let d (k : ℕ) := weight k * ‖f (y n k : E)‖
    have hd : Summable d := Summable.of_nonneg_of_le
      (fun k => mul_nonneg (weight_pos _).le (norm_nonneg _))
      (fun k => mul_le_of_le_one_right (weight_pos _).le (hty _ _)) weight_summable
    have hGn : ‖G (v n)‖ ≤ ∑' k, d k := (G.hasSum (hyexp n)).norm_le_of_bounded hd.hasSum
      (fun k => by rw [map_smul,norm_smul,hG,Complex.norm_real,Real.norm_of_nonneg (weight_pos _).le])
    calc
      ‖c n‖ * ‖G (v n)‖ ≤ ‖c n‖ * ∑' k, d k := mul_le_mul_of_nonneg_left hGn (norm_nonneg _)
      _ = ∑' k, ‖c n‖ * d k := (hd.tsum_mul_left _).symm
      _ = ∑' k, t (n,k) := tsum_congr (fun k => by dsimp [t,b,d]; ring)
  have hfinal : ‖G (u x)‖ ≤ ∑' n, ∑' k, t (n,k) := (G.hasSum (hu x)).norm_le_of_bounded ht.prod.hasSum
    (fun n => by
      rw [map_smul,norm_smul,norm_mul]
      apply le_trans _ (hg n)
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right (norm_nonneg _) ((hφ n x).trans hx)) (norm_nonneg _))
  change ‖f x‖ ≤ ∑' m, t (e m)
  rw [e.tsum_eq t,ht.tsum_prod]
  change ‖G (i (J x))‖ ≤ _ at hfinal
  rwa [hG] at hfinal
