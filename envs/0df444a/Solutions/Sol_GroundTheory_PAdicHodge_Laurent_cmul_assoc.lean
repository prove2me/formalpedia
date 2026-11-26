-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.cmul_assoc
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T15:03:56.882669+00:00
-- url     : https://prove2.me/submissions/59a290cb-0f91-4776-91c4-fe3dfce5e98f

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Filter Topology
open GroundTheory.PAdicHodge.Laurent
set_option linter.unusedSectionVars false
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {a b c : ℤ → K} {ρ : ℝ}
variable [CompleteSpace K]

private theorem tendsto_cmul_term (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ)
    (n : ℤ) : Tendsto (fun i : ℤ => ‖a i * b (n - i)‖) cofinite (𝓝 0) := by
  have hw := tendsto_weight_prod (a := a) (b := b) ha hb
  have hinj : Function.Injective (fun i : ℤ => (i, n - i)) := fun i j hij =>
    (Prod.mk.inj hij).1
  have hmap : Tendsto (fun i : ℤ => (‖a i‖ * ρ ^ i) * (‖b (n - i)‖ * ρ ^ (n - i)))
      cofinite (𝓝 0) := hw.comp hinj.tendsto_cofinite
  have : Tendsto (fun i : ℤ =>
      ((‖a i‖ * ρ ^ i) * (‖b (n - i)‖ * ρ ^ (n - i))) / ρ ^ n) cofinite (𝓝 0) := by
    convert hmap.div_const (ρ ^ n)
    exact (zero_div _).symm
  convert this using 2 with i
  exact norm_mul_term (a := a) (b := b) hρ.ne' n i

private theorem summable_cmul_term (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ)
    (n : ℤ) : Summable fun i : ℤ => a i * b (n - i) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  exact (tendsto_zero_iff_norm_tendsto_zero).2 (tendsto_cmul_term (a := a) (b := b) hρ ha hb n)

private theorem tendsto_triple_weight (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ)
    (hc : ConvergesAt c ρ) :
    Tendsto (fun q : (ℤ × ℤ) × ℤ =>
      ((‖a q.1.1‖ * ρ ^ q.1.1) * (‖b q.1.2‖ * ρ ^ q.1.2)) * (‖c q.2‖ * ρ ^ q.2))
      cofinite (𝓝 0) :=
  tendsto_mul_cofinite_nhds_zero (tendsto_weight_prod (a := a) (b := b) ha hb) hc

private theorem summable_triple (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ)
    (hc : ConvergesAt c ρ) (n : ℤ) :
    Summable fun p : ℤ × ℤ => a p.1 * b p.2 * c (n - p.1 - p.2) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  refine (tendsto_zero_iff_norm_tendsto_zero).2 ?_
  let ι : ℤ × ℤ → (ℤ × ℤ) × ℤ := fun p => ((p.1, p.2), n - p.1 - p.2)
  have hinj : Function.Injective ι := by
    intro p q h
    have h1 := congrArg (fun z : (ℤ × ℤ) × ℤ => z.1.1) h
    have h2 := congrArg (fun z : (ℤ × ℤ) × ℤ => z.1.2) h
    exact Prod.ext h1 h2
  have hw := (tendsto_triple_weight (a := a) (b := b) (c := c) ha hb hc).comp
    hinj.tendsto_cofinite
  have hdiv : Tendsto (fun p : ℤ × ℤ =>
      (((‖a p.1‖ * ρ ^ p.1) * (‖b p.2‖ * ρ ^ p.2)) *
        (‖c (n - p.1 - p.2)‖ * ρ ^ (n - p.1 - p.2))) / ρ ^ n) cofinite (𝓝 0) := by
    have hdiv' := hw.div_const (ρ ^ n : ℝ)
    rwa [zero_div] at hdiv'
  convert hdiv using 2 with p
  have hρn : ρ ^ n ≠ 0 := (zpow_pos hρ n).ne'
  have hz : ρ ^ n = ρ ^ p.1 * ρ ^ p.2 * ρ ^ (n - p.1 - p.2) := by
    rw [← zpow_add₀ hρ.ne', ← zpow_add₀ hρ.ne']
    congr 1
    ring
  simp only [norm_mul, mul_assoc]
  rw [eq_div_iff hρn, hz]
  ring

private def reindexPair : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.2, p.1 - p.2)
  invFun p := (p.1 + p.2, p.1)
  left_inv p := Prod.ext (by dsimp; ring) (by dsimp)
  right_inv p := Prod.ext (by dsimp) (by dsimp; ring)

theorem solution (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ)
    (hc : ConvergesAt c ρ) : cmul (cmul a b) c = cmul a (cmul b c) := by
  funext n
  let F : ℤ × ℤ → K := fun p => a p.1 * b p.2 * c (n - p.1 - p.2)
  have hF : Summable F := summable_triple (a := a) (b := b) (c := c) hρ ha hb hc n
  have hFe : (fun p : ℤ × ℤ => a p.2 * b (p.1 - p.2) * c (n - p.1)) = F ∘ reindexPair := by
    ext p
    dsimp [F, reindexPair]
    have : n - p.2 - (p.1 - p.2) = n - p.1 := by ring
    rw [this]
  have hL : cmul (cmul a b) c n = ∑' p, F p := by
    unfold cmul
    have hmul : ∀ i, (∑' j, a j * b (i - j)) * c (n - i) =
        ∑' j, a j * b (i - j) * c (n - i) := fun i => (tsum_mul_right).symm
    simp_rw [hmul]
    have hG : Summable fun p : ℤ × ℤ => a p.2 * b (p.1 - p.2) * c (n - p.1) := by
      rw [hFe]
      exact hF.comp_injective (reindexPair).injective
    rw [← hG.tsum_prod, hFe]
    exact reindexPair.tsum_eq F
  have hR : cmul a (cmul b c) n = ∑' p, F p := by
    unfold cmul
    have hmul : ∀ i, a i * ∑' j, b j * c (n - i - j) =
        ∑' j, a i * (b j * c (n - i - j)) := fun i => (tsum_mul_left).symm
    simp_rw [hmul]
    simp_rw [← mul_assoc]
    exact (hF.tsum_prod).symm
  exact hL.trans hR.symm
