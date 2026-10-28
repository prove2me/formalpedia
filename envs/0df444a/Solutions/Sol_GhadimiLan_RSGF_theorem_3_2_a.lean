-- Prove2me | solution 1 for GhadimiLan.RSGF.theorem_3_2_a
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-25T06:58:23.632279+00:00
-- url     : https://prove2.me/submissions/02a4d60e-a19c-4afc-86e3-e9cdaa6f0862

import Mathlib
import Definitions.Def_GhadimiLan_RSGF_Model
import Definitions.Def_GhadimiLan_RSGF_Method


section
open MeasureTheory ProbabilityTheory
open GhadimiLan.RSGF

namespace RSGFProof
section
variable {n : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
local notation "E" => EuclideanSpace ℝ (Fin n)

noncomputable def replay (F : E → Ξ → ℝ) (a : ℝ) (γ : ℕ → ℝ) (x1 : E) :
    (k : ℕ) → (Fin k → Ξ × E) → E
  | 0, _ => x1
  | k+1, z => replay F a γ x1 k (fun i => z i.castSucc) -
      γ (k+1) • szoGrad F a (replay F a γ x1 k (fun i => z i.castSucc))
        (z (Fin.last k)).1 (z (Fin.last k)).2

lemma oracle_measurable {F : E → Ξ → ℝ} {a : ℝ}
    (hF : Measurable (Function.uncurry F)) (ha : a ≠ 0) :
    Measurable (fun z : E × (Ξ × E) => szoGrad F a z.1 z.2.1 z.2.2) := by
  simp only [szoGrad, RandomGradFree.Shared.oracle, ha, if_false]
  exact ((hF.comp ((measurable_fst.add (measurable_snd.snd.const_smul a)).prodMk
    measurable_snd.fst)).sub (hF.comp (measurable_fst.prodMk measurable_snd.fst))).div_const a |>.smul measurable_snd.snd

lemma replay_measurable {F : E → Ξ → ℝ} {a : ℝ}
    (hF : Measurable (Function.uncurry F)) (ha : a ≠ 0) (γ : ℕ → ℝ) (x1 : E) (k : ℕ) :
    Measurable (replay F a γ x1 k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have hm : Measurable (fun z : Fin (k+1) → Ξ × E => replay F a γ x1 k (fun i => z i.castSucc)) :=
      ih.comp (measurable_pi_lambda _ fun i => measurable_pi_apply i.castSucc)
    exact hm.sub (((oracle_measurable hF ha).comp
      (hm.prodMk ((measurable_pi_apply (Fin.last k)).fst.prodMk
        (measurable_pi_apply (Fin.last k)).snd))).const_smul (γ (k+1)))

omit [MeasurableSpace Ξ] [MeasurableSpace Ω] in
lemma replay_eq_run (F : E → Ξ → ℝ) (a : ℝ) (γ : ℕ → ℝ) (x1 : E)
    (ξ : ℕ → Ω → Ξ) (u : ℕ → Ω → E) (x : ℕ → Ω → E)
    (hx : IsRSGFRun F a γ x1 ξ u x) (k : ℕ) (ω : Ω) :
    replay F a γ x1 k (fun i => (ξ (i.val+1) ω, u (i.val+1) ω)) = x (k+1) ω := by
  induction k with
  | zero => exact (hx.1 ω).symm
  | succ k ih =>
    rw [replay, hx.2 (k+1) (by omega) ω]
    change replay F a γ x1 k (fun i => (ξ (i.val+1) ω, u (i.val+1) ω)) - _ = _
    simp only [Fin.val_castSucc, Fin.val_last, ih]

lemma run_measurable {μ : Measure Ω} {P : Measure Ξ} {F : E → Ξ → ℝ} {a : ℝ}
    (hF : Measurable (Function.uncurry F)) (ha : a ≠ 0)
    (γ : ℕ → ℝ) (x1 : E) (ξ : ℕ → Ω → Ξ) (u : ℕ → Ω → E)
    (hs : IsSZOSampling μ P ξ u) (x : ℕ → Ω → E)
    (hx : IsRSGFRun F a γ x1 ξ u x) (k : ℕ) : Measurable (x (k+1)) := by
  have he : x (k+1) = fun ω => replay F a γ x1 k (fun i => (ξ (i.val+1) ω,u (i.val+1) ω)) :=
    funext fun ω => (replay_eq_run F a γ x1 ξ u x hx k ω).symm
  rw [he]
  exact (replay_measurable hF ha γ x1 k).comp
    (measurable_pi_lambda _ fun i => (hs.measurable_xi _).prodMk (hs.measurable_u _))

lemma prefix_fresh_indep {μ : Measure Ω} {P : Measure Ξ}
    (ξ : ℕ → Ω → Ξ) (u : ℕ → Ω → E) (hs : IsSZOSampling μ P ξ u) (k : ℕ) :
    IndepFun (fun ω (i : Fin k) => (ξ (i.val+1) ω,u (i.val+1) ω))
      (fun ω => (ξ (k+1) ω,u (k+1) ω)) μ := by
  have hi := hs.indep_pairs.precomp (g := fun j : ℕ => j+1) (by intro i j h; exact Nat.add_right_cancel h)
  have hd : Disjoint (Finset.range k) {k} := by simp
  have hh := hi.indepFun_finset (Finset.range k) {k} hd
    (fun j => (hs.measurable_xi (j+1)).prodMk (hs.measurable_u (j+1)))
  have hcomp : IndepFun (fun ω (i : Fin k) => (ξ (i.val+1) ω,u (i.val+1) ω))
      (fun ω => (ξ (k+1) ω,u (k+1) ω)) μ := hh.comp
    (φ := fun z : (j : ↥(Finset.range k)) → Ξ × E => fun i : Fin k => z ⟨i.val, by simp⟩)
    (ψ := fun z : (j : ↥({k} : Finset ℕ)) → Ξ × E => z ⟨k, by simp⟩)
    (measurable_pi_lambda _ fun _ => measurable_pi_apply _) (measurable_pi_apply (⟨k, by simp⟩ : ↥({k} : Finset ℕ)))
  exact hcomp

lemma run_fresh_indep {μ : Measure Ω} {P : Measure Ξ} {F : E → Ξ → ℝ} {a : ℝ}
    (hF : Measurable (Function.uncurry F)) (ha : a ≠ 0)
    (γ : ℕ → ℝ) (x1 : E) (ξ : ℕ → Ω → Ξ) (u : ℕ → Ω → E)
    (hs : IsSZOSampling μ P ξ u) (x : ℕ → Ω → E)
    (hx : IsRSGFRun F a γ x1 ξ u x) (k : ℕ) :
    IndepFun (x (k+1)) (fun ω => (ξ (k+1) ω,u (k+1) ω)) μ := by
  have h := (prefix_fresh_indep ξ u hs k).comp (replay_measurable hF ha γ x1 k) measurable_id
  convert h using 1
  · exact funext fun ω => (replay_eq_run F a γ x1 ξ u x hx k ω).symm
  · rfl

lemma fresh_pair_law {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure Ξ}
    (ξ : ℕ → Ω → Ξ) (u : ℕ → Ω → E) (hs : IsSZOSampling μ P ξ u) (k : ℕ) :
    μ.map (fun ω => (ξ k ω,u k ω)) = P.prod (stdGaussian E) := by
  rw [(indepFun_iff_map_prod_eq_prod_map_map (hs.measurable_xi k).aemeasurable
    (hs.measurable_u k).aemeasurable).mp (hs.indep_xi_u k),hs.law_xi,hs.law_u]

lemma run_fresh_law {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure Ξ}
    {F : E → Ξ → ℝ} {a : ℝ} (hF : Measurable (Function.uncurry F)) (ha : a ≠ 0)
    (γ : ℕ → ℝ) (x1 : E) (ξ : ℕ → Ω → Ξ) (u : ℕ → Ω → E)
    (hs : IsSZOSampling μ P ξ u) (x : ℕ → Ω → E)
    (hx : IsRSGFRun F a γ x1 ξ u x) (k : ℕ) :
    μ.map (fun ω => (x (k+1) ω,(ξ (k+1) ω,u (k+1) ω))) =
      (μ.map (x (k+1))).prod (P.prod (stdGaussian E)) := by
  rw [(indepFun_iff_map_prod_eq_prod_map_map
    (run_measurable hF ha γ x1 ξ u hs x hx k).aemeasurable
    ((hs.measurable_xi _).prodMk (hs.measurable_u _)).aemeasurable).mp
      (run_fresh_indep hF ha γ x1 ξ u hs x hx k),fresh_pair_law ξ u hs]
end
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory
namespace RSGFProof
section
variable {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Z]

omit [NormedSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
lemma product_square_integrable (ν : Measure E) (ρ : Measure Z)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (G : E → Z → E) (hm : Measurable (Function.uncurry G))
    (hg : ∀ x, Integrable (fun z => ‖G x z‖^2) ρ)
    (A B : ℝ) (hb : ∀ x, ∫ z, ‖G x z‖^2 ∂ρ ≤ A*‖x‖^2+B)
    (hx : Integrable (fun x : E => ‖x‖^2) ν) :
    Integrable (fun z : E × Z => ‖G z.1 z.2‖^2) (ν.prod ρ) := by
  have hme : Measurable (fun z : E × Z => ‖G z.1 z.2‖^2) := hm.norm.pow_const 2
  apply (integrable_prod_iff hme.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall hg
  · have hbound : Integrable (fun x : E => A*‖x‖^2+B) ν := (hx.const_mul A).add (integrable_const B)
    have hmi := hme.stronglyMeasurable.integral_prod_right' (ν := ρ)
    have hh : Integrable (fun x => ∫ z, ‖G x z‖^2 ∂ρ) ν :=
      hbound.mono' hmi.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
        exact hb x)
    simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using hh

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma square_integrable_implies_integrable (ν : Measure E) [IsProbabilityMeasure ν]
    {f : E → E} (hm : Measurable f) (hf : Integrable (fun x => ‖f x‖^2) ν) : Integrable f ν := by
  refine ((integrable_const (1:ℝ)).add hf).mono' hm.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x => by
    change ‖f x‖ ≤ 1 + ‖f x‖^2
    nlinarith [sq_nonneg (‖f x‖-1)]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma norm_square_sub_smul_le (x y : E) (c : ℝ) :
    ‖x-c•y‖^2 ≤ 2*‖x‖^2 + 2*c^2*‖y‖^2 := by
  have h := norm_sub_le x (c•y)
  rw [norm_smul, Real.norm_eq_abs] at h
  have ha := abs_nonneg c
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  have hc : |c|^2=c^2 := sq_abs c
  have hh : ‖x-c•y‖^2 ≤ (‖x‖+|c| * ‖y‖)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 h
  nlinarith [sq_nonneg (‖x‖-|c| *‖y‖)]
end
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory
open GhadimiLan.RSGF
namespace RSGFProof
section
variable {n : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
local notation "E" => EuclideanSpace ℝ (Fin n)
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure Ξ} [IsProbabilityMeasure P]
variable {F : EuclideanSpace ℝ (Fin n) → Ξ → ℝ} {a : ℝ}

lemma adaptive_oracle_square (hF : Measurable (Function.uncurry F)) (ha : a ≠ 0)
    (γ : ℕ → ℝ) (x1 : E) (ξ : ℕ → Ω → Ξ) (u : ℕ → Ω → E)
    (hs : IsSZOSampling μ P ξ u) (x : ℕ → Ω → E)
    (hx : IsRSGFRun F a γ x1 ξ u x) (A B : ℝ)
    (hg : ∀ y, Integrable (fun z : Ξ × E => ‖szoGrad F a y z.1 z.2‖^2) (P.prod (stdGaussian E)))
    (hb : ∀ y, (∫ z : Ξ × E, ‖szoGrad F a y z.1 z.2‖^2 ∂(P.prod (stdGaussian E))) ≤ A*‖y‖^2+B)
    (k : ℕ) (hik : Integrable (fun ω => ‖x (k+1) ω‖^2) μ) :
    Integrable (fun ω => ‖szoGrad F a (x (k+1) ω) (ξ (k+1) ω) (u (k+1) ω)‖^2) μ := by
  have hmX := run_measurable hF ha γ x1 ξ u hs x hx k
  let ν := μ.map (x (k+1))
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hmX.aemeasurable
  have hxm : Integrable (fun y : E => ‖y‖^2) ν :=
    (integrable_map_measure (by fun_prop) hmX.aemeasurable).2 hik
  have hG := product_square_integrable ν (P.prod (stdGaussian E))
    (fun y z => szoGrad F a y z.1 z.2) (oracle_measurable hF ha) hg A B hb hxm
  rw [← run_fresh_law hF ha γ x1 ξ u hs x hx k] at hG
  exact (integrable_map_measure ((oracle_measurable hF ha).norm.pow_const 2).aestronglyMeasurable
    (hmX.prodMk ((hs.measurable_xi _).prodMk (hs.measurable_u _))).aemeasurable).1 hG

lemma iterate_square_integrable (hF : Measurable (Function.uncurry F)) (ha : a ≠ 0)
    (γ : ℕ → ℝ) (x1 : E) (ξ : ℕ → Ω → Ξ) (u : ℕ → Ω → E)
    (hs : IsSZOSampling μ P ξ u) (x : ℕ → Ω → E)
    (hx : IsRSGFRun F a γ x1 ξ u x) (A B : ℝ)
    (hg : ∀ y, Integrable (fun z : Ξ × E => ‖szoGrad F a y z.1 z.2‖^2) (P.prod (stdGaussian E)))
    (hb : ∀ y, (∫ z : Ξ × E, ‖szoGrad F a y z.1 z.2‖^2 ∂(P.prod (stdGaussian E))) ≤ A*‖y‖^2+B)
    (k : ℕ) : Integrable (fun ω => ‖x (k+1) ω‖^2) μ := by
  induction k with
  | zero => simpa only [Nat.zero_add,hx.1] using (integrable_const (‖x1‖^2) : Integrable (fun _ : Ω => ‖x1‖^2) μ)
  | succ k ih =>
    have hiG := adaptive_oracle_square hF ha γ x1 ξ u hs x hx A B hg hb k ih
    have hbound := (ih.const_mul 2).add (hiG.const_mul (2*(γ (k+1))^2))
    apply hbound.mono' ((run_measurable hF ha γ x1 ξ u hs x hx (k+1)).norm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),hx.2 (k+1) (by omega) ω]
      exact norm_square_sub_smul_le _ _ _

lemma adaptive_integral (hF : Measurable (Function.uncurry F)) (ha : a ≠ 0)
    (γ : ℕ → ℝ) (x1 : E) (ξ : ℕ → Ω → Ξ) (u : ℕ → Ω → E)
    (hs : IsSZOSampling μ P ξ u) (x : ℕ → Ω → E)
    (hx : IsRSGFRun F a γ x1 ξ u x) (k : ℕ)
    (f : E × (Ξ × E) → ℝ) (hf : Measurable f)
    (hi : Integrable f ((μ.map (x (k+1))).prod (P.prod (stdGaussian E)))) :
    (∫ ω, f (x (k+1) ω,(ξ (k+1) ω,u (k+1) ω)) ∂μ) =
      ∫ y, (∫ z, f (y,z) ∂(P.prod (stdGaussian E))) ∂(μ.map (x (k+1))) := by
  rw [← integral_prod f hi,← run_fresh_law hF ha γ x1 ξ u hs x hx k]
  exact (integral_map ((run_measurable hF ha γ x1 ξ u hs x hx k).prodMk
    ((hs.measurable_xi _).prodMk (hs.measurable_u _))).aemeasurable hf.aestronglyMeasurable).symm
end
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory
namespace RSGFProof
section
variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace Ω]

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gradient_continuous {g : E → E} {L : ℝ} (hL : 0 ≤ L)
    (hl : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖) : Continuous g := by
  apply LipschitzWith.continuous (K := ⟨L,hL⟩)
  exact LipschitzWith.of_dist_le_mul fun x y => by
    change dist (g x) (g y) ≤ L*dist x y
    simpa only [dist_eq_norm] using hl x y

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gradient_growth {g : E → E} {L : ℝ} (hL : 0 ≤ L)
    (hl : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖) (x : E) :
    ‖g x‖^2 ≤ 2*‖g 0‖^2+2*L^2*‖x‖^2 := by
  have h := hl x 0
  simp only [sub_zero] at h
  have htri := norm_le_norm_sub_add (g x) (g 0)
  have hb : ‖g x‖ ≤ ‖g 0‖+L*‖x‖ := by linarith
  have hs : ‖g x‖^2 ≤ (‖g 0‖+L*‖x‖)^2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hb
  nlinarith [sq_nonneg (‖g 0‖-L*‖x‖)]

omit [MeasurableSpace E] [BorelSpace E] in
lemma objective_growth (f : E → ℝ) (v : E) (L : ℝ)
    (ht : ∀ x, |f x-f 0-inner ℝ v x| ≤ L/2*‖x‖^2) (x : E) :
    |f x| ≤ (‖v‖+L/2)*‖x‖^2+(|f 0|+‖v‖) := by
  have h := ht x
  have hi := abs_real_inner_le_norm v x
  have hn : ‖x‖ ≤ 1+‖x‖^2 := by nlinarith [sq_nonneg (‖x‖-1)]
  have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg v)
  have he : f x = (f x-f 0-inner ℝ v x)+f 0+inner ℝ v x := by ring
  have ha := abs_add_le ((f x-f 0-inner ℝ v x)+f 0) (inner ℝ v x)
  have hb := abs_add_le (f x-f 0-inner ℝ v x) (f 0)
  rw [← he] at ha
  nlinarith

omit [InnerProductSpace ℝ E] [BorelSpace E] in
lemma polynomial_integrable {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → E) (hX : Measurable X) (hx : Integrable (fun ω => ‖X ω‖^2) μ)
    (f : E → ℝ) (hf : Measurable f) (A B : ℝ)
    (hb : ∀ x, |f x| ≤ A*‖x‖^2+B) : Integrable (fun ω => f (X ω)) μ := by
  exact ((hx.const_mul A).add (integrable_const B)).mono' (hf.comp hX).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by
      change ‖f (X ω)‖ ≤ A*‖X ω‖^2+B
      simpa only [Real.norm_eq_abs] using hb (X ω))

omit [InnerProductSpace ℝ E] in
lemma gradient_square_integrable {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → E) (hX : Measurable X) (hx : Integrable (fun ω => ‖X ω‖^2) μ)
    (g : E → E) (L : ℝ) (hL : 0 ≤ L) (hl : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖) :
    Integrable (fun ω => ‖g (X ω)‖^2) μ := by
  apply polynomial_integrable X hX hx (fun y => ‖g y‖^2)
    ((gradient_continuous hL hl).measurable.norm.pow_const 2) (2*L^2) (2*‖g 0‖^2)
  intro y
  rw [abs_of_nonneg (sq_nonneg _)]
  have h := gradient_growth hL hl y
  linarith
end
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory
namespace RSGFProof
section
variable {E Z : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Z]

lemma update_square_integrable (ρ : Measure Z) [IsProbabilityMeasure ρ]
    (x : E) (γ : ℝ) (G : Z → E) (hm : Measurable G)
    (hG2 : Integrable (fun z => ‖G z‖^2) ρ) :
    Integrable (fun z => ‖x-γ•G z‖^2) ρ := by
  apply ((integrable_const (2*‖x‖^2)).add (hG2.const_mul (2*γ^2))).mono'
    ((measurable_const.sub (hm.const_smul γ)).norm.pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    change ‖‖x-γ•G z‖^2‖ ≤ 2*‖x‖^2+2*γ^2*‖G z‖^2
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact norm_square_sub_smul_le _ _ _

lemma update_objective_integrable (ρ : Measure Z) [IsProbabilityMeasure ρ]
    (x : E) (γ : ℝ) (G : Z → E) (hm : Measurable G)
    (hG2 : Integrable (fun z => ‖G z‖^2) ρ)
    (f : E → ℝ) (hf : Measurable f) (v : E) (L : ℝ)
    (ht : ∀ y, |f y-f 0-inner ℝ v y| ≤ L/2*‖y‖^2) :
    Integrable (fun z => f (x-γ•G z)) ρ :=
  polynomial_integrable (fun z => x-γ•G z) (measurable_const.sub (hm.const_smul γ))
    (update_square_integrable ρ x γ G hm hG2) f hf _ _ (objective_growth f v L ht)
end
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory
namespace RSGFProof
section
variable {E Z : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace Z]

omit [CompleteSpace E] in
lemma bias_inner_lower (v m : E) (b : ℝ) (hb : ‖m-v‖^2 ≤ b) :
    ‖v‖^2-b ≤ 2*inner ℝ v m := by
  have h : 0 ≤ ‖m‖^2 := sq_nonneg _
  rw [norm_sub_sq_real] at hb
  nlinarith [real_inner_comm m v]

lemma one_step_descent (ρ : Measure Z) [IsProbabilityMeasure ρ]
    (f : E → ℝ) (v x : E) (G : Z → E) (L γ b c : ℝ)
    (hL : 0 ≤ L) (hγ : 0 ≤ γ)
    (hG : Integrable G ρ) (hG2 : Integrable (fun z => ‖G z‖^2) ρ)
    (hnext : Integrable (fun z => f (x-γ•G z)) ρ)
    (ht : ∀ y, f y ≤ f x+inner ℝ v (y-x)+L/2*‖y-x‖^2)
    (hb : ‖(∫ z, G z ∂ρ)-v‖^2 ≤ b)
    (hc : ∫ z, ‖G z‖^2 ∂ρ ≤ c) :
    γ*‖v‖^2 ≤ 2*(f x-∫ z, f (x-γ•G z) ∂ρ)+γ*b+L*γ^2*c := by
  have hpoint (z : Z) : f (x-γ•G z) ≤ f x-γ*inner ℝ v (G z)+L/2*γ^2*‖G z‖^2 := by
    have hh := ht (x-γ•G z)
    have he : x-γ•G z-x = -(γ•G z) := by abel
    rw [he,inner_neg_right,inner_smul_right,norm_neg,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at hh
    nlinarith
  have hbound : Integrable (fun z => f x-γ*inner ℝ v (G z)+L/2*γ^2*‖G z‖^2) ρ :=
    ((integrable_const _).sub ((hG.const_inner v).const_mul γ)).add (hG2.const_mul _)
  have hi := integral_mono hnext hbound hpoint
  have hpart : Integrable (fun z => f x-γ*inner ℝ v (G z)) ρ :=
    (integrable_const (f x)).sub ((hG.const_inner v).const_mul γ)
  have hlast : Integrable (fun z => L/2*γ^2*‖G z‖^2) ρ := hG2.const_mul _
  rw [integral_add hpart hlast] at hi
  have hinner : Integrable (fun z => γ*inner ℝ v (G z)) ρ := (hG.const_inner v).const_mul γ
  rw [integral_sub (integrable_const (f x)) hinner,integral_const,
    probReal_univ,one_smul,integral_const_mul,integral_const_mul,integral_inner hG] at hi
  have hbi := mul_le_mul_of_nonneg_left (bias_inner_lower v (∫ z,G z ∂ρ) b hb) hγ
  have hci := mul_le_mul_of_nonneg_left hc (show 0 ≤ L*γ^2 by positivity)
  nlinarith
end
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace
namespace RSGFProof
lemma smooth_taylor {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}
    (hf : Differentiable ℝ f)
    (hL : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (x y : EuclideanSpace ℝ (Fin n)) :
    |f y-f x-⟪gradient f x,y-x⟫_ℝ| ≤ L/2*‖y-x‖^2 := by
  let d := y-x
  have hc : Continuous (gradient f) := by
    by_cases h : 0 ≤ L
    · exact (lipschitzWith_iff_norm_sub_le.mpr (by exact hL) :
        LipschitzWith ⟨L,h⟩ (gradient f)).continuous
    · have he : ∀ a b : EuclideanSpace ℝ (Fin n), a=b := by
        intro a b
        by_contra hab
        have := hL a b
        have hn : 0 < ‖a-b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
        nlinarith [norm_nonneg (gradient f a-gradient f b)]
      have heq : gradient f = fun _ => gradient f x := by funext a; rw [he a x]
      rw [heq]; fun_prop
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => f (x+t • d)-f x-t*⟪gradient f x,d⟫_ℝ)
      ⟪gradient f (x+t • d)-gradient f x,d⟫_ℝ t := by
    have hh := ((hf (x+t • d)).hasGradientAt.hasFDerivAt).comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const d |>.const_add x)
    convert (hh.sub_const (f x)).sub ((hasDerivAt_id t).mul_const ⟪gradient f x,d⟫_ℝ) using 1 <;>
      first | rfl | simp [inner_sub_left]
  have hi : IntervalIntegrable (fun t : ℝ => ⟪gradient f (x+t • d)-gradient f x,d⟫_ℝ) volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => ⟪gradient f (x+t • d)-gradient f x,d⟫_ℝ)).intervalIntegrable _ _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  have hb : ‖∫ t in (0:ℝ)..1, ⟪gradient f (x+t • d)-gradient f x,d⟫_ℝ‖ ≤
      ∫ t in (0:ℝ)..1, L*t*‖d‖^2 := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    · filter_upwards [] with t ht
      calc
        ‖⟪gradient f (x+t • d)-gradient f x,d⟫_ℝ‖ ≤
            ‖gradient f (x+t • d)-gradient f x‖*‖d‖ := norm_inner_le_norm _ _
        _ ≤ (L*‖(x+t • d)-x‖)*‖d‖ := mul_le_mul_of_nonneg_right (hL _ _) (norm_nonneg _)
        _ = L*t*‖d‖^2 := by rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]; ring
    · exact (by fun_prop : Continuous (fun t : ℝ => L*t*‖d‖^2)).intervalIntegrable _ _
  rw [he] at hb
  have hint : (∫ t in (0:ℝ)..1, L*t*‖d‖^2) = L/2*‖d‖^2 := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_id]
    ring
  rw [hint] at hb
  simpa [d, Real.norm_eq_abs] using hb
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace Topology
namespace RSGFProof
open GhadimiLan.RSGF
lemma objective_taylor {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] {P : Measure Ξ}
    [IsProbabilityMeasure P] {F : EuclideanSpace ℝ (Fin n) → Ξ → ℝ} {L σ : ℝ}
    (hF : SZOAssumptions P F L σ) (x y : EuclideanSpace ℝ (Fin n)) :
    |objective P F y-objective P F x-⟪gradient (objective P F) x,y-x⟫_ℝ| ≤
      L/2*‖y-x‖^2 := by
  have hg := (hF.grad_integrable x).inner_const (𝕜 := ℝ) (y-x)
  have he : (∫ ξ, F y ξ-F x ξ-⟪gradient (fun z => F z ξ) x,y-x⟫_ℝ ∂P) =
      objective P F y-objective P F x-⟪gradient (objective P F) x,y-x⟫_ℝ := by
    rw [integral_sub (f := fun ξ => F y ξ-F x ξ) ((hF.integrable y).sub (hF.integrable x)) hg,
      integral_sub (hF.integrable y) (hF.integrable x)]
    simp_rw [real_inner_comm]
    rw [integral_inner (hF.grad_integrable x), hF.unbiased]
    rfl
  rw [← he, ← Real.norm_eq_abs]
  suffices hb : ‖∫ ξ, F y ξ-F x ξ-⟪gradient (fun z => F z ξ) x,y-x⟫_ℝ ∂P‖ ≤ (L/2*‖y-x‖^2)*P.real univ by simpa using hb
  apply norm_integral_le_of_norm_le_const
  filter_upwards [hF.smooth] with ξ hξ
  simpa only [Real.norm_eq_abs] using smooth_taylor hξ.1 hξ.2 x y
lemma objective_gradient_lipschitz {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] {P : Measure Ξ}
    [IsProbabilityMeasure P] {F : EuclideanSpace ℝ (Fin n) → Ξ → ℝ} {L σ : ℝ}
    (hF : SZOAssumptions P F L σ) (x y : EuclideanSpace ℝ (Fin n)) :
    ‖gradient (objective P F) x-gradient (objective P F) y‖ ≤ L*‖x-y‖ := by
  rw [← hF.unbiased x, ← hF.unbiased y, ← integral_sub (hF.grad_integrable x) (hF.grad_integrable y)]
  suffices hb : ‖∫ ξ, gradient (fun z => F z ξ) x-gradient (fun z => F z ξ) y ∂P‖ ≤ (L*‖x-y‖)*P.real univ by simpa using hb
  apply norm_integral_le_of_norm_le_const
  filter_upwards [hF.smooth] with ξ hξ using hξ.2 x y
lemma objective_hasGradient {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] {P : Measure Ξ}
    [IsProbabilityMeasure P] {F : EuclideanSpace ℝ (Fin n) → Ξ → ℝ} {L σ : ℝ}
    (hL : 0 < L) (hF : SZOAssumptions P F L σ) (x : EuclideanSpace ℝ (Fin n)) :
    HasGradientAt (objective P F) (gradient (objective P F) x) x := by
  rw [hasGradientAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hh : ∀ᶠ d : EuclideanSpace ℝ (Fin n) in 𝓝 0, ‖d‖ < 2*c/L :=
    by
      change {d : EuclideanSpace ℝ (Fin n) | ‖d‖ < 2*c/L} ∈ 𝓝 0
      simpa [Metric.ball, dist_zero_right] using
      (Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin n)) (show 0 < 2*c/L by positivity))
  filter_upwards [hh] with d hd
  have ht := objective_taylor hF x (x+d)
  simp only [add_sub_cancel_left, Real.norm_eq_abs] at ht ⊢
  apply ht.trans
  have hb : L*‖d‖ ≤ 2*c := by nlinarith [(lt_div_iff₀ hL).mp hd]
  nlinarith [norm_nonneg d, mul_nonneg (norm_nonneg d) (sub_nonneg.mpr hb)]
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory
open GhadimiLan.RSGF
namespace RSGFProof
section
variable {n : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
local notation "E" => EuclideanSpace ℝ (Fin n)
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure Ξ} [IsProbabilityMeasure P]
variable {F : EuclideanSpace ℝ (Fin n) → Ξ → ℝ} {L σ a : ℝ}

lemma objective_continuous (hL : 0 < L) (hF : SZOAssumptions P F L σ) : Continuous (objective P F) :=
  continuous_iff_continuousAt.2 fun x => (objective_hasGradient hL hF x).hasFDerivAt.continuousAt

lemma native_iterate_integrability (hL : 0 < L) (hF : SZOAssumptions P F L σ) (ha : a ≠ 0)
    (γ : ℕ → ℝ) (x1 : E) (ξ : ℕ → Ω → Ξ) (u : ℕ → Ω → E)
    (hs : IsSZOSampling μ P ξ u) (x : ℕ → Ω → E) (hx : IsRSGFRun F a γ x1 ξ u x)
    (hG2 : ∀ y, Integrable (fun z : Ξ × E => ‖szoGrad F a y z.1 z.2‖^2) (P.prod (stdGaussian E)))
    (hb : ∀ y, (∫ z : Ξ × E, ‖szoGrad F a y z.1 z.2‖^2 ∂(P.prod (stdGaussian E))) ≤
      2*((n:ℝ)+2)*(‖gradient (objective P F) y‖^2+σ^2)+a^2*L^2*(n:ℝ)*((n:ℝ)+2)*((n:ℝ)+4)/2)
    (k : ℕ) :
    Integrable (fun ω => ‖x (k+1) ω‖^2) μ ∧
    Integrable (fun ω => ‖gradient (objective P F) (x (k+1) ω)‖^2) μ ∧
    Integrable (fun ω => objective P F (x (k+1) ω)) μ := by
  let g := gradient (objective P F)
  have hbound (y : E) : (∫ z : Ξ × E, ‖szoGrad F a y z.1 z.2‖^2 ∂(P.prod (stdGaussian E))) ≤
      (4*((n:ℝ)+2)*L^2)*‖y‖^2 +
      (4*((n:ℝ)+2)*‖g 0‖^2+2*((n:ℝ)+2)*σ^2+a^2*L^2*(n:ℝ)*((n:ℝ)+2)*((n:ℝ)+4)/2) := by
    have hg := gradient_growth hL.le (objective_gradient_lipschitz hF) y
    have hm := mul_le_mul_of_nonneg_left hg (show 0 ≤ 2*((n:ℝ)+2) by positivity)
    have hh := hb y
    dsimp [g]
    nlinarith
  have hx2 := iterate_square_integrable hF.measurable ha γ x1 ξ u hs x hx _ _ hG2 hbound k
  have hxm := run_measurable hF.measurable ha γ x1 ξ u hs x hx k
  refine ⟨hx2,gradient_square_integrable _ hxm hx2 _ L hL.le (objective_gradient_lipschitz hF),?_⟩
  apply polynomial_integrable _ hxm hx2 (objective P F) (objective_continuous hL hF).measurable
    (‖g 0‖+L/2) (|objective P F 0|+‖g 0‖)
  apply objective_growth
  intro y
  simpa only [sub_zero] using objective_taylor hF 0 y

end
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory
open GhadimiLan.RSGF
namespace RSGFProof
/-- Internal certificate, constructed from the native assumptions before root application. -/
structure OracleData {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) (F : EuclideanSpace ℝ (Fin n) → Ξ → ℝ) (L σ a : ℝ) : Prop where
  integrable : ∀ y, Integrable
    (fun z : Ξ × EuclideanSpace ℝ (Fin n) => szoGrad F a y z.1 z.2)
    (P.prod (stdGaussian (EuclideanSpace ℝ (Fin n))))
  square_integrable : ∀ y, Integrable
    (fun z : Ξ × EuclideanSpace ℝ (Fin n) => ‖szoGrad F a y z.1 z.2‖^2)
    (P.prod (stdGaussian (EuclideanSpace ℝ (Fin n))))
  bias : ∀ y, ‖(∫ z : Ξ × EuclideanSpace ℝ (Fin n), szoGrad F a y z.1 z.2
      ∂(P.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))))-gradient (objective P F) y‖^2 ≤
      a^2*L^2*(n:ℝ)*((n:ℝ)+2)*((n:ℝ)+4)/4
  moment : ∀ y, (∫ z : Ξ × EuclideanSpace ℝ (Fin n), ‖szoGrad F a y z.1 z.2‖^2
      ∂(P.prod (stdGaussian (EuclideanSpace ℝ (Fin n))))) ≤
      2*((n:ℝ)+2)*(‖gradient (objective P F) y‖^2+σ^2)+a^2*L^2*(n:ℝ)*((n:ℝ)+2)*((n:ℝ)+4)/2
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory
open GhadimiLan.RSGF
namespace RSGFProof
section
variable {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
local notation "V" => EuclideanSpace ℝ (Fin n)
variable {P : Measure Ξ} [IsProbabilityMeasure P]
variable {F : EuclideanSpace ℝ (Fin n) → Ξ → ℝ} {L σ a : ℝ}
omit [IsProbabilityMeasure P] in
lemma native_fixed_measurable (hF : SZOAssumptions P F L σ) (ha : a ≠ 0) (y : V) :
    Measurable (fun z : Ξ × V => szoGrad F a y z.1 z.2) := by
  have hpair : Measurable (fun z : Ξ × V => (y,z)) := measurable_const.prodMk measurable_id
  simpa only [Function.comp_def] using
    (oracle_measurable (n := n) (Ξ := Ξ) (F := F) (a := a) hF.measurable ha).comp hpair

lemma native_zero_taylor (hF : SZOAssumptions P F L σ) (z : V) :
    |objective P F z-objective P F 0-inner ℝ (gradient (objective P F) 0) z| ≤ L/2*‖z‖^2 := by
  have h := objective_taylor hF 0 z
  rw [sub_zero] at h
  exact h

lemma native_update_integrable (hL : 0 < L) (hF : SZOAssumptions P F L σ) (ha : a ≠ 0)
    (hd : OracleData P F L σ a) (y : V) (γ : ℝ) :
    Integrable (fun z : Ξ × V => objective P F (y-γ•szoGrad F a y z.1 z.2))
      (P.prod (stdGaussian V)) := by
  exact update_objective_integrable (E := EuclideanSpace ℝ (Fin n))
    (Z := Ξ × EuclideanSpace ℝ (Fin n)) (P.prod (stdGaussian V)) y γ
    (fun z : Ξ × V => szoGrad F a y z.1 z.2) (native_fixed_measurable hF ha y) (hd.square_integrable y)
    (objective P F) (objective_continuous hL hF).measurable (gradient (objective P F) 0) L (native_zero_taylor hF)

lemma native_deterministic_descent (hL : 0 < L) (hF : SZOAssumptions P F L σ) (ha : a ≠ 0)
    (hd : OracleData P F L σ a)
    (y : V) (γ : ℝ) (hγ : 0 ≤ γ) :
    γ*‖gradient (objective P F) y‖^2 ≤
      2*(objective P F y - ∫ z : Ξ × V, objective P F (y-γ•szoGrad F a y z.1 z.2) ∂(P.prod (stdGaussian V)))+
      γ*(a^2*L^2*(n:ℝ)*((n:ℝ)+2)*((n:ℝ)+4)/4)+
      L*γ^2*(2*((n:ℝ)+2)*‖gradient (objective P F) y‖^2+
        (2*((n:ℝ)+2)*σ^2+a^2*L^2*(n:ℝ)*((n:ℝ)+2)*((n:ℝ)+4)/2)) := by
  have hn := native_update_integrable hL hF ha hd y γ
  have ht (z : V) : objective P F z ≤ objective P F y+
      inner ℝ (gradient (objective P F) y) (z-y)+L/2*‖z-y‖^2 := by
    have h := (le_abs_self _).trans (objective_taylor hF y z)
    linarith
  apply one_step_descent (P.prod (stdGaussian V)) (objective P F)
    (gradient (objective P F) y) y (fun z : Ξ × V => szoGrad F a y z.1 z.2)
    L γ _ _ hL.le hγ (hd.integrable y) (hd.square_integrable y) hn ht (hd.bias y)
  calc (∫ z : Ξ × V, ‖szoGrad F a y z.1 z.2‖^2 ∂(P.prod (stdGaussian V))) ≤
      2*((n:ℝ)+2)*(‖gradient (objective P F) y‖^2+σ^2)+a^2*L^2*(n:ℝ)*((n:ℝ)+2)*((n:ℝ)+4)/2 := hd.moment y
    _ = _ := by ring
end
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory
namespace RSGFProof
section
variable {E Z Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Z] [MeasurableSpace Ω]

lemma averaged_descent (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ρ : Measure Z) [IsProbabilityMeasure ρ]
    (X Xnext : Ω → E) (Y : Ω → Z) (hmX : Measurable X) (hmY : Measurable Y)
    (G : E → Z → E) (hmG : Measurable (Function.uncurry G))
    (γ L C D b : ℝ)
    (hlaw : μ.map (fun ω => (X ω,Y ω))=(μ.map X).prod ρ)
    (hupdate : ∀ ω, Xnext ω=X ω-γ•G (X ω) (Y ω))
    (f : E → ℝ) (hf : Measurable f) (q : E → ℝ) (hq : Measurable q)
    (hiX : Integrable (fun ω => f (X ω)) μ)
    (hinext : Integrable (fun ω => f (Xnext ω)) μ)
    (hiq : Integrable (fun ω => q (X ω)) μ)
    (hstep : ∀ y, γ*q y ≤ 2*(f y-∫ z, f (y-γ•G y z) ∂ρ)+γ*b+L*γ^2*(C*q y+D)) :
    (γ-L*γ^2*C)*(∫ ω,q (X ω) ∂μ) ≤
      2*((∫ ω,f (X ω) ∂μ)-(∫ ω,f (Xnext ω) ∂μ))+γ*b+L*γ^2*D := by
  let ν := μ.map X
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hmX.aemeasurable
  let H : E × Z → ℝ := fun z => f (z.1-γ•G z.1 z.2)
  have hmH : Measurable H := hf.comp (measurable_fst.sub (hmG.const_smul γ))
  have hiH : Integrable H (ν.prod ρ) := by
    rw [← hlaw]
    apply (integrable_map_measure hmH.aestronglyMeasurable (hmX.prodMk hmY).aemeasurable).2
    change Integrable (fun ω => f (X ω-γ•G (X ω) (Y ω))) μ
    simpa only [← hupdate] using hinext
  have hif : Integrable f ν := (integrable_map_measure hf.aestronglyMeasurable hmX.aemeasurable).2 hiX
  have hiq' : Integrable q ν := (integrable_map_measure hq.aestronglyMeasurable hmX.aemeasurable).2 hiq
  have hiR : Integrable (fun y => ∫ z,H (y,z) ∂ρ) ν := hiH.integral_prod_left
  have hpoint (y : E) : (γ-L*γ^2*C)*q y ≤ 2*(f y-∫ z,H (y,z) ∂ρ)+γ*b+L*γ^2*D := by
    have h := hstep y
    change γ*q y ≤ 2*(f y-∫ z,H (y,z) ∂ρ)+γ*b+L*γ^2*(C*q y+D) at h
    nlinarith
  have hright : Integrable (fun y => 2*(f y-∫ z,H (y,z) ∂ρ)+γ*b+L*γ^2*D) ν :=
    (((hif.sub hiR).const_mul 2).add (integrable_const _)).add (integrable_const _)
  have hleft : Integrable (fun y => (γ-L*γ^2*C)*q y) ν := hiq'.const_mul _
  have hi := integral_mono hleft hright hpoint
  have hsub : Integrable (fun y => f y-∫ z,H (y,z) ∂ρ) ν := hif.sub hiR
  have hsum : Integrable (fun y => 2*(f y-∫ z,H (y,z) ∂ρ)+γ*b) ν :=
    (hsub.const_mul 2).add (integrable_const _)
  rw [integral_const_mul,integral_add hsum (integrable_const (L*γ^2*D)),
    integral_add (hsub.const_mul 2) (integrable_const (γ*b)),integral_const_mul,
    integral_sub hif hiR,integral_const,integral_const,probReal_univ,one_smul,one_smul] at hi
  have hqmap : (∫ y,q y ∂ν)=∫ ω,q (X ω) ∂μ := integral_map hmX.aemeasurable hq.aestronglyMeasurable
  have hfmap : (∫ y,f y ∂ν)=∫ ω,f (X ω) ∂μ := integral_map hmX.aemeasurable hf.aestronglyMeasurable
  have hnextmap : (∫ y,∫ z,H (y,z) ∂ρ ∂ν)=∫ ω,f (Xnext ω) ∂μ := by
    rw [← integral_prod H hiH,← hlaw,integral_map (hmX.prodMk hmY).aemeasurable hmH.aestronglyMeasurable]
    congr 1
    exact funext fun ω => by simp only [H,← hupdate]
  rwa [hqmap,hfmap,hnextmap] at hi
end
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory
open GhadimiLan.RSGF
namespace RSGFProof

lemma telescoping_Icc (f : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, (f k-f (k+1))) = f 1-f (N+1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega),ih]
    ring

lemma weight_positive {L : ℝ} {n : ℕ} {γ : ℝ}
    (hL : 0 < L) (hγ : 0 < γ) (hg : γ < 1/(2*((n:ℝ)+4)*L)) :
    0 < γ-2*L*((n:ℝ)+4)*γ^2 := by
  have hd : 0 < 2*((n:ℝ)+4)*L := by positivity
  have h := (lt_div_iff₀ hd).mp hg
  have hh := mul_pos hγ (sub_pos.mpr h)
  nlinarith

lemma weight_sum_positive {L : ℝ} {n N : ℕ} {γ : ℕ → ℝ}
    (hL : 0 < L) (hN : 1 ≤ N)
    (hγ : ∀ k ∈ Finset.Icc 1 N, 0 < γ k ∧ γ k < 1/(2*((n:ℝ)+4)*L)) :
    0 < ∑ k ∈ Finset.Icc 1 N, (γ k-2*L*((n:ℝ)+4)*γ k^2) := by
  apply Finset.sum_pos
  · intro k hk; exact weight_positive hL (hγ k hk).1 (hγ k hk).2
  · exact ⟨1,by simp [hN]⟩

lemma pmf_nonneg {L : ℝ} {n N : ℕ} {γ : ℕ → ℝ}
    (hL : 0 < L) (hN : 1 ≤ N)
    (hγ : ∀ k ∈ Finset.Icc 1 N, 0 < γ k ∧ γ k < 1/(2*((n:ℝ)+4)*L))
    (k : ℕ) (hk : k ∈ Finset.Icc 1 N) : 0 ≤ rsgfPMF L n γ N k :=
  div_nonneg (weight_positive hL (hγ k hk).1 (hγ k hk).2).le (weight_sum_positive hL hN hγ).le

lemma moment_six_le (n : ℕ) : (n:ℝ)*((n:ℝ)+2)*((n:ℝ)+4) ≤ ((n:ℝ)+4)^3 := by
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  nlinarith [sq_nonneg (n:ℝ)]

lemma step_error_comparison (n : ℕ) (L a σ γ : ℝ) (hL : 0 ≤ L) (hγ : 0 ≤ γ) :
    γ*(a^2*L^2*(n:ℝ)*((n:ℝ)+2)*((n:ℝ)+4)/4) +
      L*γ^2*(2*((n:ℝ)+2)*σ^2+a^2*L^2*(n:ℝ)*((n:ℝ)+2)*((n:ℝ)+4)/2)
    ≤ L*(2*a^2*((n:ℝ)+4)*L*((n:ℝ)+4)^2*(γ/4+L*γ^2)
       +2*((n:ℝ)+4)*σ^2*γ^2) := by
  have hm := moment_six_le n
  have h1 := mul_le_mul_of_nonneg_left hm (show 0 ≤ γ*a^2*L^2/4 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hm (show 0 ≤ a^2*L^3*γ^2/2 by positivity)
  have h3 : 0 ≤ a^2*L^2*((n:ℝ)+4)^3*γ := by positivity
  have h4 : 0 ≤ a^2*L^3*((n:ℝ)+4)^3*γ^2 := by positivity
  have h5 : 0 ≤ L*σ^2*γ^2 := by positivity
  nlinarith
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory
open GhadimiLan.RSGF
namespace RSGFProof
section
variable {n : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
local notation "E" => EuclideanSpace ℝ (Fin n)
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure Ξ} [IsProbabilityMeasure P]
variable {F : EuclideanSpace ℝ (Fin n) → Ξ → ℝ} {L σ a : ℝ}

lemma expected_registered_step (hL : 0 < L) (hF : SZOAssumptions P F L σ) (ha : a ≠ 0)
    (hd : OracleData P F L σ a)
    (γ : ℕ → ℝ) (x1 : E) (ξ : ℕ → Ω → Ξ) (u : ℕ → Ω → E)
    (hs : IsSZOSampling μ P ξ u) (x : ℕ → Ω → E) (hx : IsRSGFRun F a γ x1 ξ u x)
    (k : ℕ) (hk : 1 ≤ k) (hγ : 0 ≤ γ k) :
    (γ k-2*L*((n:ℝ)+4)*(γ k)^2)*(∫ ω,‖gradient (objective P F) (x k ω)‖^2 ∂μ) ≤
      2*((∫ ω,objective P F (x k ω) ∂μ)-(∫ ω,objective P F (x (k+1) ω) ∂μ))+
      L*(2*a^2*((n:ℝ)+4)*L*((n:ℝ)+4)^2*(γ k/4+L*γ k^2)+2*((n:ℝ)+4)*σ^2*γ k^2) := by
  have hkm : k-1+1=k := Nat.sub_add_cancel hk
  have hmX : Measurable (x k) := by
    simpa only [hkm] using run_measurable hF.measurable ha γ x1 ξ u hs x hx (k-1)
  have hii : Integrable (fun ω => ‖x k ω‖^2) μ ∧
      Integrable (fun ω => ‖gradient (objective P F) (x k ω)‖^2) μ ∧
      Integrable (fun ω => objective P F (x k ω)) μ := by
    simpa only [hkm] using native_iterate_integrability hL hF ha γ x1 ξ u hs x hx hd.square_integrable hd.moment (k-1)
  have hinext := (native_iterate_integrability hL hF ha γ x1 ξ u hs x hx hd.square_integrable hd.moment k).2.2
  have hlaw : μ.map (fun ω => (x k ω,(ξ k ω,u k ω)))=(μ.map (x k)).prod (P.prod (stdGaussian E)) := by
    simpa only [hkm] using run_fresh_law hF.measurable ha γ x1 ξ u hs x hx (k-1)
  have hh := averaged_descent μ (P.prod (stdGaussian E)) (x k) (x (k+1))
    (fun ω => (ξ k ω,u k ω)) hmX ((hs.measurable_xi k).prodMk (hs.measurable_u k))
    (fun y z => szoGrad F a y z.1 z.2) (oracle_measurable hF.measurable ha)
    (γ k) L (2*((n:ℝ)+2))
    (2*((n:ℝ)+2)*σ^2+a^2*L^2*(n:ℝ)*((n:ℝ)+2)*((n:ℝ)+4)/2)
    (a^2*L^2*(n:ℝ)*((n:ℝ)+2)*((n:ℝ)+4)/4)
    hlaw (hx.2 k hk) (objective P F) (objective_continuous hL hF).measurable
    (fun y => ‖gradient (objective P F) y‖^2)
    ((gradient_continuous hL.le (objective_gradient_lipschitz hF)).measurable.norm.pow_const 2)
    hii.2.2 hinext hii.2.1 (fun y => native_deterministic_descent hL hF ha hd y (γ k) hγ)
  have hq : 0 ≤ ∫ ω,‖gradient (objective P F) (x k ω)‖^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have he := step_error_comparison n L a σ (γ k) hL.le hγ
  have hslack : 0 ≤ L*γ k^2*(∫ ω,‖gradient (objective P F) (x k ω)‖^2 ∂μ) := by positivity
  nlinarith
end
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory
open GhadimiLan.RSGF
namespace RSGFProof
section
variable {n : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma output_run_indep {μ : Measure Ω} {F : E → Ξ → ℝ} {a : ℝ}
    (hF : Measurable (Function.uncurry F)) (ha : a ≠ 0)
    (γ : ℕ → ℝ) (x1 : E) (ξ : ℕ → Ω → Ξ) (u : ℕ → Ω → E)
    (x : ℕ → Ω → E) (hx : IsRSGFRun F a γ x1 ξ u x)
    (N : ℕ) (p : ℕ → ℝ) (R : Ω → ℕ) (hR : IsOutputIndex μ ξ u N p R) (k : ℕ) :
    IndepFun R (x (k+1)) μ := by
  have hm : Measurable (fun z : ℕ → Ξ × E => replay F a γ x1 k (fun i => z (i.val+1))) :=
    (replay_measurable hF ha γ x1 k).comp
      (measurable_pi_lambda _ fun i => measurable_pi_apply (i.val+1))
  have hh := hR.indep.comp measurable_id hm
  convert hh using 1
  · rfl
  · exact funext fun ω => (replay_eq_run F a γ x1 ξ u x hx k ω).symm

lemma independent_output_weighting {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → E} {R : Ω → ℕ} {N : ℕ} {p : ℕ → ℝ}
    (hR : Measurable R) (hmem : ∀ ω, R ω ∈ Finset.Icc 1 N)
    (hlaw : ∀ k ∈ Finset.Icc 1 N, μ {ω | R ω=k}=ENNReal.ofReal (p k))
    (hp : ∀ k ∈ Finset.Icc 1 N, 0 ≤ p k)
    (hm : ∀ k ∈ Finset.Icc 1 N, Measurable (X k))
    (hi : ∀ k ∈ Finset.Icc 1 N, IndepFun R (X k) μ)
    (g : E → ℝ) (hg : Measurable g)
    (hint : ∀ k ∈ Finset.Icc 1 N, Integrable (fun ω => g (X k ω)) μ) :
    Integrable (fun ω => g (X (R ω) ω)) μ ∧
    (∫ ω, g (X (R ω) ω) ∂μ)=∑ k ∈ Finset.Icc 1 N, p k*(∫ ω, g (X k ω) ∂μ) := by
  classical
  let f : ℕ → Ω → ℝ := fun k ω => if R ω=k then g (X k ω) else 0
  have hf (k : ℕ) (hk : k ∈ Finset.Icc 1 N) : Integrable (f k) μ := by
    apply ((hint k hk).indicator (measurableSet_eq_fun hR (measurable_const (a := k)))).congr
    exact Filter.Eventually.of_forall fun ω => by
      by_cases h : R ω=k <;> simp [f,h]
  have he (ω : Ω) : g (X (R ω) ω) = ∑ k ∈ Finset.Icc 1 N, f k ω := by
    rw [Finset.sum_eq_single (R ω)]
    · simp [f]
    · intro k _ hne; simp [f,Ne.symm hne]
    · exact fun h => False.elim (h (hmem ω))
  have hefun : (fun ω => g (X (R ω) ω)) = fun ω => ∑ k ∈ Finset.Icc 1 N, f k ω := funext he
  rw [hefun]
  constructor
  · exact integrable_finsetSum _ hf
  · rw [integral_finsetSum _ hf]
    apply Finset.sum_congr rfl
    intro k hk
    have hmI : Measurable (fun j : ℕ => if j=k then (1:ℝ) else 0) := by fun_prop
    have hind := (hi k hk).comp hmI hg
    have hI : AEStronglyMeasurable (fun ω => if R ω=k then (1:ℝ) else 0) μ :=
      (hmI.comp hR).aestronglyMeasurable
    have hG : AEStronglyMeasurable (fun ω => g (X k ω)) μ := (hg.comp (hm k hk)).aestronglyMeasurable
    have hh := hind.integral_mul_eq_mul_integral hI hG
    have heI : (∫ ω, (if R ω=k then (1:ℝ) else 0) ∂μ)=p k := by
      have hhI := integral_indicator_one (μ := μ) (measurableSet_eq_fun hR (measurable_const (a := k)))
      simp only [Set.indicator,Set.mem_ofPred_eq,Pi.one_apply] at hhI
      rw [hhI]
      rw [Measure.real,hlaw k hk,ENNReal.toReal_ofReal (hp k hk)]
    simpa only [Function.comp_apply,Pi.mul_apply,ite_mul,one_mul,zero_mul,heI] using hh
end
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory
open GhadimiLan.RSGF
namespace RSGFProof
section
variable {n : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
local notation "E" => EuclideanSpace ℝ (Fin n)
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure Ξ} [IsProbabilityMeasure P]
variable {F : EuclideanSpace ℝ (Fin n) → Ξ → ℝ} {L σ a : ℝ}

lemma weighted_sum_bound (hL : 0 < L) (hF : SZOAssumptions P F L σ) (ha : a ≠ 0)
    (hd : OracleData P F L σ a) (fstar : ℝ) (hfstar : IsGLB (Set.range (objective P F)) fstar)
    (N : ℕ) (hN : 1 ≤ N) (γ : ℕ → ℝ)
    (hγ : ∀ k ∈ Finset.Icc 1 N, 0 < γ k ∧ γ k < 1/(2*((n:ℝ)+4)*L))
    (x1 : E) (ξ : ℕ → Ω → Ξ) (u : ℕ → Ω → E)
    (hs : IsSZOSampling μ P ξ u) (x : ℕ → Ω → E) (hx : IsRSGFRun F a γ x1 ξ u x) :
    (∑ k ∈ Finset.Icc 1 N, (γ k-2*L*((n:ℝ)+4)*γ k^2)*
      (∫ ω,‖gradient (objective P F) (x k ω)‖^2 ∂μ)) ≤
    L*(2*(objective P F x1-fstar)/L+
      2*a^2*((n:ℝ)+4)*(1+L*((n:ℝ)+4)^2*(∑ k ∈ Finset.Icc 1 N,(γ k/4+L*γ k^2)))+
      2*((n:ℝ)+4)*σ^2*(∑ k ∈ Finset.Icc 1 N,γ k^2)) := by
  have _ := hN
  have hsum := Finset.sum_le_sum (s := Finset.Icc 1 N) (fun k hk =>
    expected_registered_step hL hF ha hd γ x1 ξ u hs x hx k (Finset.mem_Icc.mp hk).1 (hγ k hk).1.le)
  have htel := telescoping_Icc (fun k => ∫ ω,objective P F (x k ω) ∂μ) N
  have hstart : (∫ ω,objective P F (x 1 ω) ∂μ)=objective P F x1 := by simp only [hx.1,integral_const,probReal_univ,one_smul]
  have hnext := (native_iterate_integrability hL hF ha γ x1 ξ u hs x hx hd.square_integrable hd.moment N).2.2
  have hlow : fstar ≤ ∫ ω,objective P F (x (N+1) ω) ∂μ := by
    have h := integral_mono (integrable_const fstar) hnext (fun ω => hfstar.1 ⟨x (N+1) ω,rfl⟩)
    simpa only [integral_const,probReal_univ,one_smul] using h
  simp only [Finset.sum_add_distrib] at hsum
  have htel2 : (∑ k ∈ Finset.Icc 1 N, 2*((∫ ω,objective P F (x k ω) ∂μ)-
      (∫ ω,objective P F (x (k+1) ω) ∂μ))) =
      2*(objective P F x1-(∫ ω,objective P F (x (N+1) ω) ∂μ)) := by
    rw [← Finset.mul_sum,htel,hstart]
  rw [htel2] at hsum
  simp only [← Finset.mul_sum] at hsum
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hsum
  have hpos : 0 ≤ 2*L*a^2*((n:ℝ)+4) := by positivity
  have hLne := ne_of_gt hL
  refine hsum.trans ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  calc
    _ ≤ 2*(objective P F x1-fstar) + L*(2*a^2*((n:ℝ)+4)*L*((n:ℝ)+4)^2*((∑ k ∈ Finset.Icc 1 N, γ k/4)+L*(∑ k ∈ Finset.Icc 1 N, γ k^2))+2*((n:ℝ)+4)*σ^2*(∑ k ∈ Finset.Icc 1 N,γ k^2)) + 2*L*a^2*((n:ℝ)+4) := by nlinarith
    _ = _ := by field_simp [hLne]; ring

lemma full_bound (hL : 0 < L) (hF : SZOAssumptions P F L σ) (ha : a ≠ 0)
    (hd : OracleData P F L σ a) (fstar : ℝ) (hfstar : IsGLB (Set.range (objective P F)) fstar)
    (N : ℕ) (hN : 1 ≤ N) (γ : ℕ → ℝ)
    (hγ : ∀ k ∈ Finset.Icc 1 N, 0 < γ k ∧ γ k < 1/(2*((n:ℝ)+4)*L))
    (ξ : ℕ → Ω → Ξ) (u : ℕ → Ω → E) (hs : IsSZOSampling μ P ξ u)
    (x1 : E) (x : ℕ → Ω → E) (hx : IsRSGFRun F a γ x1 ξ u x)
    (R : Ω → ℕ) (hR : IsOutputIndex μ ξ u N (rsgfPMF L n γ N) R) :
    Integrable (fun ω => ‖gradient (objective P F) (x (R ω) ω)‖^2) μ ∧
    1/L*(∫ ω,‖gradient (objective P F) (x (R ω) ω)‖^2 ∂μ) ≤
    1/(∑ k ∈ Finset.Icc 1 N,(γ k-2*L*((n:ℝ)+4)*γ k^2))*
    (2*(objective P F x1-fstar)/L+
      2*a^2*((n:ℝ)+4)*(1+L*((n:ℝ)+4)^2*(∑ k ∈ Finset.Icc 1 N,(γ k/4+L*γ k^2)))+
      2*((n:ℝ)+4)*σ^2*(∑ k ∈ Finset.Icc 1 N,γ k^2)) := by
  have hm (k : ℕ) (hk : k ∈ Finset.Icc 1 N) : Measurable (x k) := by
    have he : k-1+1=k := Nat.sub_add_cancel (Finset.mem_Icc.mp hk).1
    simpa only [he] using run_measurable hF.measurable ha γ x1 ξ u hs x hx (k-1)
  have hind (k : ℕ) (hk : k ∈ Finset.Icc 1 N) : IndepFun R (x k) μ := by
    have he : k-1+1=k := Nat.sub_add_cancel (Finset.mem_Icc.mp hk).1
    simpa only [he] using output_run_indep hF.measurable ha γ x1 ξ u x hx N _ R hR (k-1)
  have hi (k : ℕ) (hk : k ∈ Finset.Icc 1 N) : Integrable (fun ω => ‖gradient (objective P F) (x k ω)‖^2) μ := by
    have he : k-1+1=k := Nat.sub_add_cancel (Finset.mem_Icc.mp hk).1
    simpa only [he] using (native_iterate_integrability hL hF ha γ x1 ξ u hs x hx hd.square_integrable hd.moment (k-1)).2.1
  have ho := independent_output_weighting hR.measurable hR.mem_range hR.law (pmf_nonneg hL hN hγ)
    hm hind (fun y => ‖gradient (objective P F) y‖^2)
    ((gradient_continuous hL.le (objective_gradient_lipschitz hF)).measurable.norm.pow_const 2) hi
  refine ⟨ho.1,?_⟩
  rw [ho.2]
  have hdpos := weight_sum_positive hL hN hγ
  have hsum := weighted_sum_bound hL hF ha hd fstar hfstar N hN γ hγ x1 ξ u hs x hx
  have he : (∑ k ∈ Finset.Icc 1 N, rsgfPMF L n γ N k * (∫ ω, ‖gradient (objective P F) (x k ω)‖^2 ∂μ)) =
      (∑ k ∈ Finset.Icc 1 N, (γ k-2*L*((n:ℝ)+4)*γ k^2)*(∫ ω, ‖gradient (objective P F) (x k ω)‖^2 ∂μ)) /
      (∑ k ∈ Finset.Icc 1 N, (γ k-2*L*((n:ℝ)+4)*γ k^2)) := by
    simp only [rsgfPMF, div_mul_eq_mul_div, ← Finset.sum_div]
  rw [he]
  have hdiv := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsum hdpos.le)
    (show 0 ≤ 1/L by positivity)
  have hr (B D : ℝ) : 1/L*(L*B/D)=1/D*B := by field_simp [ne_of_gt hL]
  rw [hr] at hdiv
  exact hdiv
end
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
namespace RSGFProof
lemma oracle_taylor {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {L a : ℝ}
    (ha : 0 < a) (hf : Differentiable ℝ f)
    (hL : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (x u : EuclideanSpace ℝ (Fin n)) :
    ‖RandomGradFree.Shared.oracle f a x u-⟪gradient f x,u⟫_ℝ • u‖ ≤
      a*L/2*‖u‖^3 := by
  have ht := smooth_taylor hf hL x (x+a • u)
  simp only [add_sub_cancel_left, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos ha] at ht
  have he : (f (x+a • u)-f x)/a-⟪gradient f x,u⟫_ℝ =
      (f (x+a • u)-f x-a*⟪gradient f x,u⟫_ℝ)/a := by field_simp [ha.ne']
  simp only [RandomGradFree.Shared.oracle, ne_of_gt ha, ↓reduceIte]
  rw [← sub_smul, norm_smul, Real.norm_eq_abs, he, abs_div, abs_of_pos ha]
  calc |f (x+a • u)-f x-a*⟪gradient f x,u⟫_ℝ| / a * ‖u‖ ≤
      (L/2*(a*‖u‖)^2)/a*‖u‖ := by
        exact mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right ha).mpr ht) (norm_nonneg _)
  _ = a*L/2*‖u‖^3 := by field_simp
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory
namespace RSGFProof
lemma exp_deriv_poly (p : Polynomial ℝ) :
    deriv (fun t : ℝ => p.eval t * Real.exp (t^2/2)) =
      fun t => (p.derivative + Polynomial.X * p).eval t * Real.exp (t^2/2) := by
  funext t
  rw [deriv_fun_mul (by fun_prop) (by fun_prop), (p.hasDerivAt t).deriv,
    _root_.deriv_exp (by fun_prop)]
  simp only [deriv_div_const, deriv_fun_pow, differentiableAt_fun_id, deriv_id'',
    Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
  ring
lemma gaussian_moment_formula (n : ℕ) :
    (∫ x : ℝ, x^n ∂gaussianReal 0 1) =
      iteratedDeriv n (fun t : ℝ => Real.exp (t^2/2)) 0 := by
  have h := iteratedDeriv_mgf_zero (X := fun x : ℝ => x)
    (μ := gaussianReal 0 1) (by simp) n
  simpa only [Pi.pow_apply, mgf_fun_id_gaussianReal, NNReal.coe_one, zero_mul, one_mul, zero_add] using h.symm
lemma gaussian_moment_four : (∫ x : ℝ, x^4 ∂gaussianReal 0 1) = 3 := by
  rw [gaussian_moment_formula]
  have h0 : (fun t : ℝ => Real.exp (t^2/2)) =
      fun t => (1 : Polynomial ℝ).eval t * Real.exp (t^2/2) := by simp
  rw [h0]
  norm_num only [iteratedDeriv_succ, iteratedDeriv_zero]
  simp only [exp_deriv_poly]
  norm_num [Polynomial.derivative_add, Polynomial.derivative_mul]
lemma gaussian_moment_two : (∫ x : ℝ, x^2 ∂gaussianReal 0 1) = 1 := by
  rw [gaussian_moment_formula]
  have h0 : (fun t : ℝ => Real.exp (t^2/2)) =
      fun t => (1 : Polynomial ℝ).eval t * Real.exp (t^2/2) := by simp
  rw [h0]
  norm_num only [iteratedDeriv_succ, iteratedDeriv_zero]
  simp only [exp_deriv_poly]
  norm_num [Polynomial.derivative_add, Polynomial.derivative_mul]
lemma gaussian_moment_six : (∫ x : ℝ, x^6 ∂gaussianReal 0 1) = 15 := by
  rw [gaussian_moment_formula]
  have h0 : (fun t : ℝ => Real.exp (t^2/2)) =
      fun t => (1 : Polynomial ℝ).eval t * Real.exp (t^2/2) := by simp
  rw [h0]
  norm_num only [iteratedDeriv_succ, iteratedDeriv_zero]
  simp only [exp_deriv_poly]
  norm_num [Polynomial.derivative_add, Polynomial.derivative_mul]
lemma gaussian_moment_one : (∫ x : ℝ, x^1 ∂gaussianReal 0 1) = 0 := by
  rw [gaussian_moment_formula]
  have h0 : (fun t : ℝ => Real.exp (t^2/2)) =
      fun t => (1 : Polynomial ℝ).eval t * Real.exp (t^2/2) := by simp
  rw [h0]
  norm_num only [iteratedDeriv_succ, iteratedDeriv_zero]
  simp only [exp_deriv_poly]
  norm_num [Polynomial.derivative_add, Polynomial.derivative_mul]
lemma gaussian_moment_three : (∫ x : ℝ, x^3 ∂gaussianReal 0 1) = 0 := by
  rw [gaussian_moment_formula]
  have h0 : (fun t : ℝ => Real.exp (t^2/2)) =
      fun t => (1 : Polynomial ℝ).eval t * Real.exp (t^2/2) := by simp
  rw [h0]
  norm_num only [iteratedDeriv_succ, iteratedDeriv_zero]
  simp only [exp_deriv_poly]
  norm_num [Polynomial.derivative_add, Polynomial.derivative_mul]
lemma gaussian_moment_five : (∫ x : ℝ, x^5 ∂gaussianReal 0 1) = 0 := by
  rw [gaussian_moment_formula]
  have h0 : (fun t : ℝ => Real.exp (t^2/2)) =
      fun t => (1 : Polynomial ℝ).eval t * Real.exp (t^2/2) := by simp
  rw [h0]
  norm_num only [iteratedDeriv_succ, iteratedDeriv_zero]
  simp only [exp_deriv_poly]
  norm_num [Polynomial.derivative_add, Polynomial.derivative_mul]
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory Finset
namespace RSGFProof
noncomputable abbrev gaussianPi (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)
lemma gaussian_pow_integrable (k : ℕ) : Integrable (fun x : ℝ => x^k) (gaussianReal 0 1) := by
  simpa only [Pi.pow_apply] using integrable_pow_of_mem_interior_integrableExpSet
    (X := fun x : ℝ => x) (μ := gaussianReal 0 1) (by simp) k
lemma gaussian_monomial_integrable {n : ℕ} (e : Fin n → ℕ) :
    Integrable (fun x : Fin n → ℝ => ∏ i, x i ^ e i) (gaussianPi n) :=
  Integrable.fintype_prod (fun i => gaussian_pow_integrable (e i))
lemma gaussian_monomial_integral {n : ℕ} (e : Fin n → ℕ) :
    (∫ x : Fin n → ℝ, ∏ i, x i ^ e i ∂gaussianPi n) =
      ∏ i, ∫ x : ℝ, x ^ e i ∂gaussianReal 0 1 :=
  integral_fintype_prod_eq_prod _
lemma power_product_one {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (a : ℕ) :
    (∏ l, x l ^ (if l=i then a else 0)) = x i^a := by simp
lemma power_product_three {n : ℕ} (x : Fin n → ℝ) (i j k : Fin n) (a b c : ℕ) :
    (∏ l, x l ^ ((if l=i then a else 0)+(if l=j then b else 0)+(if l=k then c else 0))) =
      x i^a*x j^b*x k^c := by
  simp_rw [pow_add, Finset.prod_mul_distrib, power_product_one]
lemma gaussian_triple_sq {n : ℕ} (i j k : Fin n) :
    (∫ x : Fin n → ℝ, x i^2*x j^2*x k^2 ∂gaussianPi n) =
      1 + (if i=j then 2 else 0) + (if i=k then 2 else 0) +
    (if j=k then 2 else 0) + (if i=j ∧ j=k then 8 else 0) := by
  simp_rw [← power_product_three (a := 2) (b := 2) (c := 2)]
  rw [gaussian_monomial_integral]
  have hm : ∀ l : Fin n,
    (∫ x : ℝ, x ^ ((if l=i then 2 else 0)+(if l=j then 2 else 0)+(if l=k then 2 else 0))
      ∂gaussianReal 0 1) =
    (if l=i then (if i=j then (if i=k then 15 else 3) else (if i=k then 3 else 1))
     else if l=j then (if j=k then 3 else 1) else 1) := by
    intro l
    split_ifs <;> simp_all [gaussian_moment_two, gaussian_moment_four, gaussian_moment_six]
  simp_rw [hm]
  by_cases hij : i=j <;> by_cases hik : i=k <;> by_cases hjk : j=k
  all_goals simp_all <;> norm_num
  all_goals
    have he : (fun l : Fin n => if l=i then (1:ℝ) else if l=k then 3 else 1) =
        fun l => if l=k then 3 else 1 := by
      funext l
      split_ifs <;> simp_all
    rw [he]
    simp
lemma gaussian_triple_integrable {n : ℕ} (i j k : Fin n) (a b c : ℕ) :
    Integrable (fun x : Fin n → ℝ => x i^a*x j^b*x k^c) (gaussianPi n) := by
  simp_rw [← power_product_three (a := a) (b := b) (c := c)]
  exact gaussian_monomial_integrable _
lemma gaussian_cross_four {n : ℕ} (i j k : Fin n) :
    (∫ x : Fin n → ℝ, x i*x j*x k^2 ∂gaussianPi n) =
      if i=j then (if i=k then 3 else 1) else 0 := by
  have hp (x : Fin n → ℝ) := power_product_three x i j k 1 1 2
  simp only [pow_one] at hp
  simp_rw [← hp]
  rw [gaussian_monomial_integral]
  by_cases hij : i=j
  · subst j
    have hm : ∀ l : Fin n,
        (∫ x : ℝ, x^((if l=i then 1 else 0)+(if l=i then 1 else 0)+(if l=k then 2 else 0))
          ∂gaussianReal 0 1) = if l=i ∧ i=k then 3 else 1 := by
      intro l
      split_ifs <;> simp_all [gaussian_moment_two, gaussian_moment_four]
    simp_rw [hm]
    by_cases hik : i=k <;> simp [hik]
  · simp only [hij, ↓reduceIte]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hik : i=k
    · subst k
      simp [hij, gaussian_moment_three]
    · simp [hij, hik]
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory Finset
namespace RSGFProof
lemma gaussian_sum_sq_cube {n : ℕ} :
    (∫ x : Fin n → ℝ, (∑ i, x i^2)^3 ∂gaussianPi n) =
      (n:ℝ)*((n:ℝ)+2)*((n:ℝ)+4) := by
  have he (x : Fin n → ℝ) : (∑ i, x i^2)^3 = ∑ i, ∑ j, ∑ k, x i^2*x j^2*x k^2 := by
    simp only [← mul_sum, ← sum_mul]
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun k _ => gaussian_triple_integrable i j k 2 2 2)))]
  simp_rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ =>
    gaussian_triple_integrable _ j k 2 2 2)),
    integral_finsetSum _ (fun k _ => gaussian_triple_integrable _ _ k 2 2 2),
    gaussian_triple_sq]
  simp only [sum_add_distrib]
  simp [ite_and]
  ring
lemma gaussian_cross_norm {n : ℕ} (v : Fin n → ℝ) :
    (∫ x : Fin n → ℝ, (∑ i, v i*x i)^2*(∑ k, x k^2) ∂gaussianPi n) =
      ((n:ℝ)+2)*(∑ i, v i^2) := by
  have he (x : Fin n → ℝ) : (∑ i, v i*x i)^2*(∑ k, x k^2) =
      ∑ i, ∑ j, ∑ k, (v i*v j)*(x i*x j*x k^2) := by
    have hr (i j k : Fin n) : (v i*v j)*(x i*x j*x k^2) =
        (v i*x i)*(v j*x j)*(x k^2) := by ring
    simp_rw [hr]
    simp only [← mul_sum, ← sum_mul]
    ring
  have hi (i j k : Fin n) : Integrable (fun x : Fin n → ℝ => (v i*v j)*(x i*x j*x k^2))
      (gaussianPi n) := by
    simpa only [pow_one] using (gaussian_triple_integrable i j k 1 1 2).const_mul (v i*v j)
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun k _ => hi i j k)))]
  simp_rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hi _ j k)),
    integral_finsetSum _ (fun k _ => hi _ _ k), integral_const_mul, gaussian_cross_four]
  simp only [mul_ite, mul_zero]
  simp_rw [sum_ite_irrel]
  have hm (i : Fin n) : (∑ k : Fin n, if i=k then v i*v i*3 else v i*v i*1) =
      ((n:ℝ)+2)*v i^2 := by
    have he (k : Fin n) : (if i=k then v i*v i*3 else v i*v i*1) =
        v i^2 + (if i=k then 2*v i^2 else 0) := by split_ifs <;> ring
    simp_rw [he]
    simp [sum_add_distrib]
    ring
  simp only [sum_const_zero, Finset.sum_ite_eq, mem_univ, ↓reduceIte]
  simp_rw [hm, mul_sum]
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory Finset
open scoped InnerProductSpace
namespace RSGFProof
lemma gaussian_norm_pow_integrable {n : ℕ} (k : ℕ) :
    Integrable (fun u : EuclideanSpace ℝ (Fin n) => ‖u‖^k)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  exact (IsGaussian.memLp_id (μ := stdGaussian (EuclideanSpace ℝ (Fin n))) (p := k)
    (by simp)).integrable_norm_pow'
lemma gaussian_norm_six {n : ℕ} :
    (∫ u : EuclideanSpace ℝ (Fin n), ‖u‖^6 ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      (n:ℝ)*((n:ℝ)+2)*((n:ℝ)+4) := by
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
  have he (x : Fin n → ℝ) : ‖WithLp.toLp 2 x‖^6 = (∑ i, x i^2)^3 := by
    rw [show (6:ℕ)=2*3 from rfl, pow_mul, EuclideanSpace.real_norm_sq_eq]
  simpa only [he] using (gaussian_sum_sq_cube (n := n))
lemma gaussian_inner_sq_norm_sq {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    (∫ u : EuclideanSpace ℝ (Fin n), ⟪v,u⟫_ℝ^2*‖u‖^2
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) = ((n:ℝ)+2)*‖v‖^2 := by
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
  simpa only [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial, dotProduct, mul_comm] using gaussian_cross_norm (fun i => v i)
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
namespace RSGFProof
open GhadimiLan.RSGF
lemma sample_gradient_sq_integrable {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] {P : Measure Ξ}
    [IsProbabilityMeasure P] {F : EuclideanSpace ℝ (Fin n) → Ξ → ℝ} {L σ : ℝ}
    (hF : SZOAssumptions P F L σ) (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun ξ => ‖gradient (fun y => F y ξ) x‖^2) P := by
  have hi := ((hF.var_integrable x).add
    (((hF.grad_integrable x).const_inner (𝕜 := ℝ) (gradient (objective P F) x)).const_mul 2)).sub
      (integrable_const (‖gradient (objective P F) x‖^2))
  convert hi using 1
  funext ξ
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [norm_sub_sq_real, real_inner_comm (gradient (fun y => F y ξ) x)]
  ring
lemma sample_gradient_sq_bound {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] {P : Measure Ξ}
    [IsProbabilityMeasure P] {F : EuclideanSpace ℝ (Fin n) → Ξ → ℝ} {L σ : ℝ}
    (hF : SZOAssumptions P F L σ) (x : EuclideanSpace ℝ (Fin n)) :
    (∫ ξ, ‖gradient (fun y => F y ξ) x‖^2 ∂P) ≤ ‖gradient (objective P F) x‖^2+σ^2 := by
  have he (ξ : Ξ) : ‖gradient (fun y => F y ξ) x‖^2 =
      ‖gradient (fun y => F y ξ) x-gradient (objective P F) x‖^2+
      2*⟪gradient (objective P F) x,gradient (fun y => F y ξ) x⟫_ℝ-
      ‖gradient (objective P F) x‖^2 := by
    rw [norm_sub_sq_real, real_inner_comm (gradient (fun y => F y ξ) x)]; ring
  simp_rw [he]
  rw [integral_sub (f := fun ξ => ‖gradient (fun y => F y ξ) x-gradient (objective P F) x‖^2+
      2*⟪gradient (objective P F) x,gradient (fun y => F y ξ) x⟫_ℝ) ((hF.var_integrable x).add
      (((hF.grad_integrable x).const_inner (𝕜 := ℝ) (gradient (objective P F) x)).const_mul 2)) (integrable_const _),
    integral_add (hF.var_integrable x) (((hF.grad_integrable x).const_inner (𝕜 := ℝ) (gradient (objective P F) x)).const_mul 2),
    integral_const_mul, integral_inner (hF.grad_integrable x), hF.unbiased]
  simp only [real_inner_self_eq_norm_sq]
  simp
  linarith [hF.variance x]
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
namespace RSGFProof
open GhadimiLan.RSGF
section
variable {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] {P : Measure Ξ} [IsProbabilityMeasure P]
local notation "E" => EuclideanSpace ℝ (Fin n)
variable {F : EuclideanSpace ℝ (Fin n) → Ξ → ℝ} {L σ a : ℝ}
noncomputable def oracleRemainder (F : E → Ξ → ℝ) (a : ℝ) (x : E) (z : Ξ × E) : E :=
  szoGrad F a x z.1 z.2-⟪gradient (fun y => F y z.1) x,z.2⟫_ℝ • z.2
omit [IsProbabilityMeasure P] in
lemma fixed_oracle_measurable (ha : 0<a) (hF : SZOAssumptions P F L σ) (x : E) :
    Measurable (fun z : Ξ × E => szoGrad F a x z.1 z.2) := by
  have hp : Measurable (fun z : Ξ × E => (x,z)) := measurable_const.prodMk measurable_id
  simpa only [Function.comp_def] using
    (oracle_measurable (n := n) (Ξ := Ξ) (F := F) (a := a) hF.measurable ha.ne').comp hp
omit [IsProbabilityMeasure P] in
lemma remainder_aesm (ha : 0<a) (hF : SZOAssumptions P F L σ) (x : E) :
    AEStronglyMeasurable (oracleRemainder F a x) (P.prod (stdGaussian E)) := by
  unfold oracleRemainder
  have hg : AEStronglyMeasurable (fun z : Ξ × E => gradient (fun y => F y z.1) x)
      (P.prod (stdGaussian E)) := (hF.grad_integrable x).aestronglyMeasurable.comp_fst
  have hu : AEStronglyMeasurable (fun z : Ξ × E => z.2) (P.prod (stdGaussian E)) := measurable_snd.aestronglyMeasurable
  convert (fixed_oracle_measurable ha hF x).aestronglyMeasurable.sub
    ((hg.inner (𝕜 := ℝ) hu).smul hu) using 1
  funext z
  rfl

omit [IsProbabilityMeasure P] in
lemma remainder_bound (ha : 0<a) (hF : SZOAssumptions P F L σ) (x : E) :
    ∀ᵐ z : Ξ × E ∂P.prod (stdGaussian E), ‖oracleRemainder F a x z‖ ≤ a*L/2*‖z.2‖^3 := by
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := stdGaussian E)).ae hF.smooth] with z hz
  exact oracle_taylor ha hz.1 hz.2 x z.2
lemma remainder_integrable (ha : 0<a) (hF : SZOAssumptions P F L σ) (x : E) :
    Integrable (oracleRemainder F a x) (P.prod (stdGaussian E)) := by
  exact (((gaussian_norm_pow_integrable (n := n) 3).const_mul (a*L/2)).comp_snd P).mono'
    (remainder_aesm ha hF x) (remainder_bound ha hF x)
omit [IsProbabilityMeasure P] in
lemma remainder_sq_bound (ha : 0<a) (hF : SZOAssumptions P F L σ) (x : E) :
    ∀ᵐ z : Ξ × E ∂P.prod (stdGaussian E), ‖oracleRemainder F a x z‖^2 ≤
      (a*L/2)^2*‖z.2‖^6 := by
  filter_upwards [remainder_bound ha hF x] with z hz
  have h := pow_le_pow_left₀ (norm_nonneg _) hz 2
  simpa only [mul_pow, ← pow_mul] using h
lemma remainder_sq_integrable (ha : 0<a) (hF : SZOAssumptions P F L σ) (x : E) :
    Integrable (fun z => ‖oracleRemainder F a x z‖^2) (P.prod (stdGaussian E)) := by
  apply (((gaussian_norm_pow_integrable (n := n) 6).const_mul ((a*L/2)^2)).comp_snd P).mono'
    ((remainder_aesm ha hF x).norm.pow 2)
  filter_upwards [remainder_sq_bound ha hF x] with z hz
  change ‖‖oracleRemainder F a x z‖^2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖oracleRemainder F a x z‖)]
  exact hz
lemma remainder_sq_integral (ha : 0<a) (hF : SZOAssumptions P F L σ) (x : E) :
    (∫ z : Ξ × E, ‖oracleRemainder F a x z‖^2 ∂P.prod (stdGaussian E)) ≤
      a^2*L^2*(n:ℝ)*((n:ℝ)+2)*((n:ℝ)+4)/4 := by
  have hb := integral_mono_ae (remainder_sq_integrable ha hF x)
    (((gaussian_norm_pow_integrable (n := n) 6).const_mul ((a*L/2)^2)).comp_snd P)
    (remainder_sq_bound ha hF x)
  have hi : Integrable (fun z : Ξ × E => (a*L/2)^2*‖z.2‖^6)
      (P.prod (stdGaussian E)) :=
    (((gaussian_norm_pow_integrable (n := n) 6).const_mul ((a*L/2)^2)).comp_snd P)
  have he : (∫ z : Ξ × E, (a*L/2)^2*‖z.2‖^6 ∂P.prod (stdGaussian E)) =
      (a*L/2)^2*((n:ℝ)*((n:ℝ)+2)*((n:ℝ)+4)) := by
    rw [integral_prod _ hi]
    simp_rw [integral_const_mul, gaussian_norm_six]
    simp
  rw [he] at hb
  nlinarith
end
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory Finset
namespace RSGFProof
lemma gaussian_cross_two {n : ℕ} (i j : Fin n) :
    (∫ x : Fin n → ℝ, x i*x j ∂gaussianPi n) = if i=j then 1 else 0 := by
  have hp (x : Fin n → ℝ) := power_product_three x i j j 1 1 0
  simp only [pow_one, pow_zero, mul_one, ite_self, add_zero] at hp
  simp_rw [← hp]
  rw [gaussian_monomial_integral]
  by_cases hij : i=j
  · subst j
    have hm (l : Fin n) : (∫ x : ℝ, x^((if l=i then 1 else 0)+(if l=i then 1 else 0))
        ∂gaussianReal 0 1) = 1 := by
      by_cases h : l=i <;> simp [h, gaussian_moment_two]
    simp_rw [hm]
    simp
  · simp only [hij, ↓reduceIte]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hij]
lemma gaussian_cross_two_integrable {n : ℕ} (i j : Fin n) :
    Integrable (fun x : Fin n → ℝ => x i*x j) (gaussianPi n) := by
  simpa only [pow_one, pow_zero, mul_one] using gaussian_triple_integrable i j j 1 1 0
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory Finset
open scoped InnerProductSpace
namespace RSGFProof
lemma gaussian_linear_integrable {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun u : EuclideanSpace ℝ (Fin n) => ⟪v,u⟫_ℝ • u)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  apply ((gaussian_norm_pow_integrable 2).const_mul ‖v‖).mono' (by fun_prop)
  filter_upwards [] with u
  rw [norm_smul, Real.norm_eq_abs]
  calc |⟪v,u⟫_ℝ| *‖u‖ ≤ (‖v‖*‖u‖)*‖u‖ :=
    mul_le_mul_of_nonneg_right (abs_real_inner_le_norm _ _) (norm_nonneg _)
  _ = ‖v‖*‖u‖^2 := by ring
lemma gaussian_linear_mean {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    (∫ u : EuclideanSpace ℝ (Fin n), ⟪v,u⟫_ℝ • u
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) = v := by
  ext i
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).toContinuousLinearMap
  have hA := A.integral_comp_comm (gaussian_linear_integrable v)
  change (∫ u : EuclideanSpace ℝ (Fin n), ⟪v,u⟫_ℝ * u i
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      (∫ u : EuclideanSpace ℝ (Fin n), ⟪v,u⟫_ℝ • u
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) i at hA
  rw [← hA, ← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
  have he (x : Fin n → ℝ) : (∑ j, x j*v j)*x i = ∑ j, v j*(x j*x i) := by
    rw [sum_mul]
    apply sum_congr rfl; intro j _; ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun j _ => (gaussian_cross_two_integrable j i).const_mul (v j))]
  simp_rw [integral_const_mul, gaussian_cross_two, mul_ite, mul_one, mul_zero]
  simp
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
namespace RSGFProof
section
variable {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] {P : Measure Ξ} [IsProbabilityMeasure P]
local notation "E" => EuclideanSpace ℝ (Fin n)

omit [IsProbabilityMeasure P] in
lemma gaussian_product_linear_measurable (v : Ξ → E) (hv : Integrable v P) :
    AEStronglyMeasurable (fun z : Ξ × E => ⟪v z.1,z.2⟫_ℝ • z.2) (P.prod (stdGaussian E)) := by
  have hfst : AEStronglyMeasurable (fun z : Ξ × E => v z.1) (P.prod (stdGaussian E)) := hv.aestronglyMeasurable.comp_fst
  have hsnd : AEStronglyMeasurable (fun z : Ξ × E => z.2) (P.prod (stdGaussian E)) := measurable_snd.aestronglyMeasurable
  exact (hfst.inner (𝕜 := ℝ) hsnd).smul hsnd

omit [IsProbabilityMeasure P] in
lemma gaussian_product_linear_integrable (v : Ξ → E) (hv : Integrable v P) :
    Integrable (fun z : Ξ × E => ⟪v z.1,z.2⟫_ℝ • z.2) (P.prod (stdGaussian E)) := by
  apply (hv.norm.mul_prod (gaussian_norm_pow_integrable 2)).mono' (gaussian_product_linear_measurable v hv)
  exact Filter.Eventually.of_forall fun z => by
    change ‖⟪v z.1,z.2⟫_ℝ • z.2‖ ≤ ‖v z.1‖*‖z.2‖^2
    rw [norm_smul,Real.norm_eq_abs]
    calc |⟪v z.1,z.2⟫_ℝ| *‖z.2‖ ≤ (‖v z.1‖*‖z.2‖)*‖z.2‖ :=
      mul_le_mul_of_nonneg_right (abs_real_inner_le_norm _ _) (norm_nonneg _)
    _ = _ := by ring

omit [IsProbabilityMeasure P] in
lemma gaussian_product_linear_square_integrable (v : Ξ → E) (hv : Integrable v P)
    (hv2 : Integrable (fun ξ => ‖v ξ‖^2) P) :
    Integrable (fun z : Ξ × E => ‖⟪v z.1,z.2⟫_ℝ • z.2‖^2) (P.prod (stdGaussian E)) := by
  apply (hv2.mul_prod (gaussian_norm_pow_integrable 4)).mono'
    ((gaussian_product_linear_measurable v hv).norm.pow 2)
  exact Filter.Eventually.of_forall fun z => by
    change ‖‖⟪v z.1,z.2⟫_ℝ • z.2‖^2‖ ≤ ‖v z.1‖^2*‖z.2‖^4
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    have h := abs_real_inner_le_norm (v z.1) z.2
    have hh := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 h
    rw [sq_abs,mul_pow] at hh
    have hm := mul_le_mul_of_nonneg_right hh (sq_nonneg ‖z.2‖)
    nlinarith

lemma gaussian_product_linear_mean (v : Ξ → E) (hv : Integrable v P) :
    (∫ z : Ξ × E, ⟪v z.1,z.2⟫_ℝ • z.2 ∂(P.prod (stdGaussian E))) = ∫ ξ,v ξ ∂P := by
  rw [integral_prod _ (gaussian_product_linear_integrable v hv)]
  simp only [gaussian_linear_mean]

lemma gaussian_product_linear_second (v : Ξ → E) (hv : Integrable v P)
    (hv2 : Integrable (fun ξ => ‖v ξ‖^2) P) :
    (∫ z : Ξ × E, ‖⟪v z.1,z.2⟫_ℝ • z.2‖^2 ∂(P.prod (stdGaussian E))) =
      ((n:ℝ)+2)*(∫ ξ,‖v ξ‖^2 ∂P) := by
  rw [integral_prod _ (gaussian_product_linear_square_integrable v hv hv2)]
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,gaussian_inner_sq_norm_sq]
  exact integral_const_mul _ _
end
end RSGFProof
end

section
open MeasureTheory
open scoped InnerProductSpace
namespace RSGFProof
lemma mean_norm_sq_le {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : Ω → E} (hf : Integrable f μ) (h2 : Integrable (fun x => ‖f x‖^2) μ) :
    ‖∫ x, f x ∂μ‖^2 ≤ ∫ x, ‖f x‖^2 ∂μ := by
  have hi := (hf.const_inner (𝕜 := ℝ) (∫ x, f x ∂μ)).const_mul 2
  have he (x : Ω) : ‖f x-(∫ x, f x ∂μ)‖^2 =
      ‖f x‖^2-2*⟪(∫ x, f x ∂μ),f x⟫_ℝ+‖∫ x, f x ∂μ‖^2 := by
    rw [norm_sub_sq_real, real_inner_comm]
  have hn : 0 ≤ ∫ x, ‖f x-(∫ y, f y ∂μ)‖^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  simp_rw [he] at hn
  rw [integral_add (f := fun x => ‖f x‖^2-2*⟪(∫ y, f y ∂μ),f x⟫_ℝ) (h2.sub hi) (integrable_const _), integral_sub h2 hi,
    integral_const_mul, integral_inner hf] at hn
  simp only [real_inner_self_eq_norm_sq] at hn
  simp at hn
  linarith
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
namespace RSGFProof
open GhadimiLan.RSGF
lemma native_oracle_data {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] {P : Measure Ξ}
    [IsProbabilityMeasure P] {F : EuclideanSpace ℝ (Fin n) → Ξ → ℝ} {L σ a : ℝ}
    (ha : 0<a) (hF : SZOAssumptions P F L σ) : OracleData P F L σ a := by
  have hB (x : (EuclideanSpace ℝ (Fin n))) := gaussian_product_linear_integrable
    (fun ξ => gradient (fun y => F y ξ) x) (hF.grad_integrable x)
  have hB2 (x : (EuclideanSpace ℝ (Fin n))) := gaussian_product_linear_square_integrable
    (fun ξ => gradient (fun y => F y ξ) x) (hF.grad_integrable x) (sample_gradient_sq_integrable hF x)
  have hG (x : (EuclideanSpace ℝ (Fin n))) : Integrable (fun z : Ξ × (EuclideanSpace ℝ (Fin n)) => szoGrad F a x z.1 z.2) (P.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
    apply ((hB x).add (remainder_integrable ha hF x)).congr
    filter_upwards [] with z
    simp only [Pi.add_apply, oracleRemainder]
    abel
  have hbound (x : (EuclideanSpace ℝ (Fin n))) (z : Ξ × (EuclideanSpace ℝ (Fin n))) : ‖szoGrad F a x z.1 z.2‖^2 ≤
      2*‖⟪gradient (fun y => F y z.1) x,z.2⟫_ℝ • z.2‖^2+
      2*‖oracleRemainder F a x z‖^2 := by
    have he : szoGrad F a x z.1 z.2 =
        ⟪gradient (fun y => F y z.1) x,z.2⟫_ℝ • z.2+oracleRemainder F a x z := by
      simp [oracleRemainder]
    rw [he]
    have ht := norm_add_le (⟪gradient (fun y => F y z.1) x,z.2⟫_ℝ • z.2) (oracleRemainder F a x z)
    nlinarith [norm_nonneg (⟪gradient (fun y => F y z.1) x,z.2⟫_ℝ • z.2),
      norm_nonneg (oracleRemainder F a x z),norm_nonneg (⟪gradient (fun y => F y z.1) x,z.2⟫_ℝ • z.2+oracleRemainder F a x z),
      sq_nonneg (‖⟪gradient (fun y => F y z.1) x,z.2⟫_ℝ • z.2‖-‖oracleRemainder F a x z‖)]
  have hG2 (x : (EuclideanSpace ℝ (Fin n))) : Integrable (fun z : Ξ × (EuclideanSpace ℝ (Fin n)) => ‖szoGrad F a x z.1 z.2‖^2) (P.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
    apply (((hB2 x).const_mul 2).add ((remainder_sq_integrable ha hF x).const_mul 2)).mono'
      ((hG x).aestronglyMeasurable.norm.pow 2)
    filter_upwards [] with z
    change ‖‖szoGrad F a x z.1 z.2‖^2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖szoGrad F a x z.1 z.2‖)]
    exact hbound x z
  refine ⟨hG,hG2,?_,?_⟩
  · intro x
    have he : (∫ z : Ξ × (EuclideanSpace ℝ (Fin n)), szoGrad F a x z.1 z.2 ∂(P.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))))-gradient (objective P F) x =
        ∫ z : Ξ × (EuclideanSpace ℝ (Fin n)), oracleRemainder F a x z ∂(P.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
      simp only [oracleRemainder]
      rw [integral_sub (hG x) (hB x),
        gaussian_product_linear_mean _ (hF.grad_integrable x), hF.unbiased]
    rw [he]
    exact (mean_norm_sq_le (remainder_integrable ha hF x) (remainder_sq_integrable ha hF x)).trans
      (remainder_sq_integral ha hF x)
  · intro x
    have hb := integral_mono (hG2 x)
      (((hB2 x).const_mul 2).add ((remainder_sq_integrable ha hF x).const_mul 2)) (hbound x)
    simp only [Pi.add_apply] at hb
    rw [integral_add ((hB2 x).const_mul 2) ((remainder_sq_integrable ha hF x).const_mul 2),
      integral_const_mul, integral_const_mul,
      gaussian_product_linear_second _ (hF.grad_integrable x) (sample_gradient_sq_integrable hF x)] at hb
    have hfirst := mul_le_mul_of_nonneg_left (sample_gradient_sq_bound hF x)
      (show 0 ≤ (n:ℝ)+2 by positivity)
    have hrem := remainder_sq_integral ha hF x
    nlinarith
end RSGFProof
end

section
open MeasureTheory ProbabilityTheory
namespace GhadimiLan.RSGF

/-- Theorem 3.2 a), Eq. (3.16) (Ghadimi & Lan, arXiv:1309.5549v1, pp. 16–17). Under the standing
assumptions of §3 (A1 for `G = ∇_x F`, A3, `F(·, ξ) ∈ C^{1,1}_L` a.s.), with `f = objective P F`
bounded below with infimum `fstar`, stepsizes `0 < γ_k < 1/[2(n+4)L]`, smoothing parameter
`μs > 0` (the paper's `µ`; `μ` is the probability measure) and the random output index `R` with
the pmf (3.15), drawn independently of the samples, the RSGF output satisfies
`(1/L) E‖∇f(x_R)‖² ≤ [D_f² + 2µ²(n+4)(1 + L(n+4)² Σ(γ_k/4 + Lγ_k²)) + 2(n+4)σ² Σγ_k²] / Σ[γ_k − 2L(n+4)γ_k²]`
with `D_f² = 2(f(x_1) − f*)/L` (2.5). The integrability of `‖∇f(x_R)‖²` is part of the claim. -/
theorem proved_root {n : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure Ξ) [IsProbabilityMeasure P]
    (F : EuclideanSpace ℝ (Fin n) → Ξ → ℝ) (L σ μs : ℝ) (hL : 0 < L) (hσ : 0 ≤ σ) (hμs : 0 < μs)
    (hF : SZOAssumptions P F L σ)
    (fstar : ℝ) (hfstar : IsGLB (Set.range (objective P F)) fstar)
    (N : ℕ) (hN : 1 ≤ N) (γ : ℕ → ℝ)
    (hγ : ∀ k ∈ Finset.Icc 1 N, 0 < γ k ∧ γ k < 1 / (2 * ((n : ℝ) + 4) * L))
    (ξ : ℕ → Ω → Ξ) (u : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (hs : IsSZOSampling μ P ξ u)
    (x1 : EuclideanSpace ℝ (Fin n)) (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (hx : IsRSGFRun F μs γ x1 ξ u x)
    (R : Ω → ℕ) (hR : IsOutputIndex μ ξ u N (rsgfPMF L n γ N) R) :
    Integrable (fun ω => ‖gradient (objective P F) (x (R ω) ω)‖ ^ 2) μ ∧
      1 / L * ∫ ω, ‖gradient (objective P F) (x (R ω) ω)‖ ^ 2 ∂μ ≤
        1 / (∑ k ∈ Finset.Icc 1 N, (γ k - 2 * L * ((n : ℝ) + 4) * γ k ^ 2)) *
          (2 * (objective P F x1 - fstar) / L
            + 2 * μs ^ 2 * ((n : ℝ) + 4) *
                (1 + L * ((n : ℝ) + 4) ^ 2 * ∑ k ∈ Finset.Icc 1 N, (γ k / 4 + L * γ k ^ 2))
            + 2 * ((n : ℝ) + 4) * σ ^ 2 * ∑ k ∈ Finset.Icc 1 N, γ k ^ 2) := by
  have _ := hσ
  exact RSGFProof.full_bound hL hF hμs.ne' (RSGFProof.native_oracle_data hμs hF)
    fstar hfstar N hN γ hγ ξ u hs x1 x hx R hR

end GhadimiLan.RSGF
end

open MeasureTheory ProbabilityTheory GhadimiLan.RSGF

theorem solution {n : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure Ξ) [IsProbabilityMeasure P]
    (F : EuclideanSpace ℝ (Fin n) → Ξ → ℝ) (L σ μs : ℝ) (hL : 0 < L) (hσ : 0 ≤ σ) (hμs : 0 < μs)
    (hF : SZOAssumptions P F L σ)
    (fstar : ℝ) (hfstar : IsGLB (Set.range (objective P F)) fstar)
    (N : ℕ) (hN : 1 ≤ N) (γ : ℕ → ℝ)
    (hγ : ∀ k ∈ Finset.Icc 1 N, 0 < γ k ∧ γ k < 1 / (2 * ((n : ℝ) + 4) * L))
    (ξ : ℕ → Ω → Ξ) (u : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (hs : IsSZOSampling μ P ξ u)
    (x1 : EuclideanSpace ℝ (Fin n)) (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (hx : IsRSGFRun F μs γ x1 ξ u x)
    (R : Ω → ℕ) (hR : IsOutputIndex μ ξ u N (rsgfPMF L n γ N) R) :
    Integrable (fun ω => ‖gradient (objective P F) (x (R ω) ω)‖ ^ 2) μ ∧
      1 / L * ∫ ω, ‖gradient (objective P F) (x (R ω) ω)‖ ^ 2 ∂μ ≤
        1 / (∑ k ∈ Finset.Icc 1 N, (γ k - 2 * L * ((n : ℝ) + 4) * γ k ^ 2)) *
          (2 * (objective P F x1 - fstar) / L
            + 2 * μs ^ 2 * ((n : ℝ) + 4) *
                (1 + L * ((n : ℝ) + 4) ^ 2 * ∑ k ∈ Finset.Icc 1 N, (γ k / 4 + L * γ k ^ 2))
            + 2 * ((n : ℝ) + 4) * σ ^ 2 * ∑ k ∈ Finset.Icc 1 N, γ k ^ 2) := by
  exact GhadimiLan.RSGF.proved_root μ P F L σ μs hL hσ hμs hF fstar hfstar N hN γ hγ ξ u hs x1 x hx R hR

theorem GhadimiLan.RSGF.theorem_3_2_a {n : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure Ξ) [IsProbabilityMeasure P]
    (F : EuclideanSpace ℝ (Fin n) → Ξ → ℝ) (L σ μs : ℝ) (hL : 0 < L) (hσ : 0 ≤ σ) (hμs : 0 < μs)
    (hF : SZOAssumptions P F L σ)
    (fstar : ℝ) (hfstar : IsGLB (Set.range (objective P F)) fstar)
    (N : ℕ) (hN : 1 ≤ N) (γ : ℕ → ℝ)
    (hγ : ∀ k ∈ Finset.Icc 1 N, 0 < γ k ∧ γ k < 1 / (2 * ((n : ℝ) + 4) * L))
    (ξ : ℕ → Ω → Ξ) (u : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (hs : IsSZOSampling μ P ξ u)
    (x1 : EuclideanSpace ℝ (Fin n)) (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (hx : IsRSGFRun F μs γ x1 ξ u x)
    (R : Ω → ℕ) (hR : IsOutputIndex μ ξ u N (rsgfPMF L n γ N) R) :
    Integrable (fun ω => ‖gradient (objective P F) (x (R ω) ω)‖ ^ 2) μ ∧
      1 / L * ∫ ω, ‖gradient (objective P F) (x (R ω) ω)‖ ^ 2 ∂μ ≤
        1 / (∑ k ∈ Finset.Icc 1 N, (γ k - 2 * L * ((n : ℝ) + 4) * γ k ^ 2)) *
          (2 * (objective P F x1 - fstar) / L
            + 2 * μs ^ 2 * ((n : ℝ) + 4) *
                (1 + L * ((n : ℝ) + 4) ^ 2 * ∑ k ∈ Finset.Icc 1 N, (γ k / 4 + L * γ k ^ 2))
            + 2 * ((n : ℝ) + 4) * σ ^ 2 * ∑ k ∈ Finset.Icc 1 N, γ k ^ 2) := by
  exact _root_.solution μ P F L σ μs hL hσ hμs hF fstar hfstar N hN γ hγ ξ u hs x1 x hx R hR
