-- Prove2me | solution 1 for OAI.TranslativeCovering.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T15:02:55.56799+00:00
-- url     : https://prove2.me/submissions/2fb091d5-7bc1-4e77-b38f-f0c2a1ac6a95

import Mathlib
import Definitions.Def_CoveringDensity
import Definitions.Def_OAIQ16Cd002
import Theorems.Thm_OAI_AllLatticeExclusion_no_cover
import Theorems.Thm_OAI_BodySelection_volume_lower
import Theorems.Thm_OAI_SourcePatternTail_uniform
import Theorems.Thm_OAI_TranslativeCovering_periodization_exact

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_LocalizationRounding
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal

namespace LocalizationRounding
open Set Finset
open scoped BigOperators

lemma alphabet_card {n : ℕ} {h L : ℝ} (hh : 0 < h) (hL : 0 ≤ L) :
    ((alphabet n h L).card:ℝ) ≤ (1+2*L/h)^n := by
  classical
  have hn : (alphabet n h L).card ≤ (integerBox n ⌊L/h⌋).card :=
    (Finset.card_filter_le _ _).trans (Finset.card_image_le)
  have hc : (integerBox n ⌊L/h⌋).card = (⌊L/h⌋+1-(-⌊L/h⌋)).toNat^n := by
    simp [integerBox,Fintype.card_piFinset,Int.card_Icc]
  have hm : 0 ≤ ⌊L/h⌋ := Int.floor_nonneg.mpr (div_nonneg hL hh.le)
  have hz : 0 ≤ ⌊L/h⌋+1-(-⌊L/h⌋) := by omega
  have hcast : ((⌊L/h⌋+1-(-⌊L/h⌋)).toNat:ℝ) = (⌊L/h⌋:ℝ)+1-(-(⌊L/h⌋:ℝ)) := by
    rw [← Int.cast_natCast,Int.toNat_of_nonneg hz]
    push_cast
    rfl
  have hb : ((⌊L/h⌋+1-(-⌊L/h⌋)).toNat:ℝ) ≤ 1+2*L/h := by
    rw [hcast]
    have hf := Int.floor_le (L/h)
    rw [mul_div_assoc]
    linarith only [hf]
  calc
    _ ≤ ((integerBox n ⌊L/h⌋).card:ℝ) := by exact_mod_cast hn
    _ = (((⌊L/h⌋+1-(-⌊L/h⌋)).toNat:ℝ))^n := by rw [hc,Nat.cast_pow]
    _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg _) hb _

lemma boundedLists_card (n N : ℕ) (h L : ℝ) :
    Fintype.card (BoundedLists n h L N) ≤ (N+1)*max 1 (alphabet n h L).card^N := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun,Fintype.card_coe,Fintype.card_fin]
  calc
    _ ≤ ∑ _m : Fin (N+1), max 1 (alphabet n h L).card^N := Finset.sum_le_sum fun i _ => by
      calc
        _ ≤ max 1 (alphabet n h L).card^i.val := Nat.pow_le_pow_left (le_max_right _ _) _
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
    _ = _ := by simp

end LocalizationRounding

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PoissonConfig
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace PoissonConfig

variable {Ω : Type u_1} [MeasurableSpace Ω]

lemma measurableSet_sigma {β : ℕ → Type u_3} [∀ n, MeasurableSpace (β n)]
    {s : Set (Σ n, β n)} (h : ∀ n, MeasurableSet (Sigma.mk n ⁻¹' s)) :
    MeasurableSet s := by
  exact MeasurableSpace.measurableSet_iInf.mpr h

lemma measurable_sigma {β : ℕ → Type u_4} [∀ n, MeasurableSpace (β n)]
    {Γ : Type u_5} [MeasurableSpace Γ] {f : (Σ n, β n) → Γ}
    (h : ∀ n, Measurable (f ∘ Sigma.mk n)) : Measurable f := by
  intro s hs
  apply measurableSet_sigma
  intro n
  exact h n hs

end PoissonConfig

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PoissonSample
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3 u_4

namespace PoissonSample
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal NNReal

variable {Ω : Type u_1} [MeasurableSpace Ω]

lemma measurable_sigmaMk {β : ℕ → Type u_3} [∀ n, MeasurableSpace (β n)] (n : ℕ) :
    Measurable (Sigma.mk n : β n → Σ n, β n) := by
  intro s hs
  exact (MeasurableSpace.measurableSet_iInf.mp hs) n

instance sample_probability (r : ℝ≥0) (σ : Measure Ω) [IsProbabilityMeasure σ] :
    IsProbabilityMeasure (sample r σ) := by
  constructor
  rw [sample, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.map_apply (measurable_sigmaMk _) MeasurableSet.univ,
    preimage_univ, measure_univ, smul_eq_mul, mul_one]
  simp only [poissonMeasure_singleton]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    (hasSum_one_poissonMeasure r).summable, (hasSum_one_poissonMeasure r).tsum_eq,
    ENNReal.ofReal_one]

end PoissonSample

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PoissonRealization
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace PoissonSample
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal NNReal
variable {Ω : Type u_1} [MeasurableSpace Ω] [StandardBorelSpace Ω]

lemma measurable_injective (n : ℕ) :
    MeasurableSet {f : Fin n → Ω | Function.Injective f} := by
  simp only [Function.Injective, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases hij : i = j
  · simp only [hij, implies_true, ofPred_true]
    exact MeasurableSet.univ
  · simp only [hij, imp_false]
    exact (measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)).compl

lemma measurable_simplify : Measurable (simplify (Ω := Ω)) := by
  apply PoissonConfig.measurable_sigma
  intro n
  change Measurable (fun f : Fin n → Ω => if h : Function.Injective f then
    (⟨n, ⟨f,h⟩⟩ : PoissonConfig.Config Ω) else ⟨0, ⟨Fin.elim0, fun i => Fin.elim0 i⟩⟩)
  have hm := (measurable_sigmaMk (β := fun k => {f : Fin k → Ω // Function.Injective f}) n).dite
      (g := fun _ => (⟨0, ⟨Fin.elim0, fun i => Fin.elim0 i⟩⟩ : PoissonConfig.Config Ω))
      measurable_const (measurable_injective n)
  convert! hm using 1
  all_goals try with_reducible_and_instances rfl
  funext f
  split_ifs <;> first | rfl | contradiction

instance simpleSample_probability (r : ℝ≥0) (σ : Measure Ω) [IsProbabilityMeasure σ] :
    IsProbabilityMeasure (simpleSample r σ) :=
  Measure.isProbabilityMeasure_map measurable_simplify.aemeasurable

end PoissonSample

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_RandomBody
attribute [-instance] _root_.OAI.CapCost.intensity_finite _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3

namespace RandomBody
open Set MeasureTheory Metric SphericalLaw
open scoped ENNReal NNReal

lemma body_closed {n : ℕ} (b t : ℝ) (U : PoissonConfig.Config (Sphere n)) :
    IsClosed (body b t U) := by
  apply isClosed_closedBall.inter
  exact isClosed_iInter fun i => isClosed_le ((continuous_const.inner continuous_id).abs) continuous_const

lemma body_compact {n : ℕ} (b t : ℝ) (U : PoissonConfig.Config (Sphere n)) :
    IsCompact (body b t U) :=
  (isCompact_closedBall (0 : Space n) b).of_isClosed_subset (body_closed b t U) inter_subset_left

lemma convex_slab {n : ℕ} (u : Space n) (t : ℝ) :
    Convex ℝ {x | |inner ℝ u x| ≤ t} := by
  intro x hx y hy a b ha hb hab
  change |inner ℝ u (a • x+b • y)| ≤ t
  rw [inner_add_right,inner_smul_right,inner_smul_right]
  have hx' : |inner ℝ u x| ≤ t := hx
  have hy' : |inner ℝ u y| ≤ t := hy
  calc
    _ ≤ |a*inner ℝ u x|+|b*inner ℝ u y| := abs_add_le _ _
    _ = a*|inner ℝ u x|+b*|inner ℝ u y| := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]
    _ ≤ a*t+b*t := add_le_add (mul_le_mul_of_nonneg_left hx' ha) (mul_le_mul_of_nonneg_left hy' hb)
    _ = t := by rw [← add_mul,hab,one_mul]

lemma body_convex {n : ℕ} (b t : ℝ) (U : PoissonConfig.Config (Sphere n)) :
    Convex ℝ (body b t U) :=
  (convex_closedBall (0 : Space n) b).inter (convex_iInter fun i => convex_slab (U.2.val i).val t)

lemma ball_subset {n : ℕ} (b t r : ℝ) (U : PoissonConfig.Config (Sphere n))
    (hrb : r ≤ b) (hrt : r ≤ t) : closedBall 0 r ⊆ body b t U := by
  intro x hx
  refine ⟨closedBall_subset_closedBall hrb hx,mem_iInter.mpr fun i => ?_⟩
  have hnx : ‖x‖ ≤ r := mem_closedBall_zero_iff.mp hx
  have hu : ‖(U.2.val i).val‖ = 1 := mem_sphere_zero_iff_norm.mp (U.2.val i).property
  exact (abs_real_inner_le_norm _ _).trans (by rw [hu,one_mul]; exact hnx.trans hrt)

lemma body_symm {n : ℕ} (b t : ℝ) (U : PoissonConfig.Config (Sphere n)) :
    TranslativeCovering.CentrallySymmetric (body b t U) := by
  refine ⟨0,?_⟩
  intro x
  simp only [smul_zero,zero_sub,body,mem_inter_iff,mem_iInter,mem_ofPred_eq,
    mem_closedBall_zero_iff,norm_neg,inner_neg_right,abs_neg]

lemma body_isBody {n : ℕ} (b t : ℝ) (U : PoissonConfig.Config (Sphere n))
    (hb : 0 < b) (ht : 0 < t) : TranslativeCovering.ConvexBody (body b t U) := by
  refine ⟨body_compact b t U,body_convex b t U,?_⟩
  have hr : 0 < min b t := lt_min hb ht
  have hsub : ball (0 : Space n) (min b t) ⊆ body b t U :=
    ball_subset_closedBall.trans (ball_subset b t (min b t) U (min_le_left _ _) (min_le_right _ _))
  exact ⟨0, (isOpen_ball.subset_interior_iff.mpr hsub) (mem_ball_self hr)⟩

end RandomBody

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_RadialShell
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace RadialShell
open Filter
open scoped Topology

lemma inv_limit : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
lemma eta_limit : Tendsto η atTop (𝓝 0) := by
  unfold η
  simpa only [zero_pow (by norm_num : (4:ℕ) ≠ 0)] using inv_limit.pow 4
lemma log_div_limit : Tendsto (fun n : ℕ => Real.log n/(n:ℝ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  exact ht.comp tendsto_natCast_atTop_atTop

end RadialShell

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CoveringGrowth
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CoveringGrowth
open Filter Real
open scoped Topology

lemma polynomial {C δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,C*(n:ℝ)^k ≤ Real.exp (δ*(n:ℝ)) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k:ℝ) δ hδ).comp
    tendsto_natCast_atTop_atTop
  have ht' : Tendsto (fun n : ℕ => C*((n:ℝ)^k*Real.exp (-δ*(n:ℝ)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_natCast,mul_zero] using ht.const_mul C
  filter_upwards [ht'.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn
  have he := mul_le_mul_of_nonneg_right hn.le (Real.exp_pos (δ*(n:ℝ))).le
  have hid : Real.exp (-δ*(n:ℝ))*Real.exp (δ*(n:ℝ)) = 1 := by rw [← Real.exp_add]; convert Real.exp_zero using 2 ; ring
  calc
    _ = (C*((n:ℝ)^k*Real.exp (-δ*(n:ℝ))))*Real.exp (δ*(n:ℝ)) := by rw [mul_assoc,mul_assoc,hid,mul_one]
    _ ≤ _ := by simpa only [one_mul] using he

lemma moving_base {b : ℕ → ℝ} {B rate : ℝ} (hB : 0 < B)
    (hb : Tendsto b atTop (𝓝 B)) (hrate : Real.log B < rate) :
    ∀ᶠ n : ℕ in atTop,0 < b n ∧ (b n)^n ≤ Real.exp (rate*(n:ℝ)) := by
  have ht : Tendsto (fun n => Real.log (b n)) atTop (𝓝 (Real.log B)) :=
    (Real.continuousAt_log hB.ne').tendsto.comp hb
  filter_upwards [hb.eventually (lt_mem_nhds hB),ht.eventually (gt_mem_nhds hrate)] with n hn hlog
  refine ⟨hn,?_⟩
  calc
    _ = Real.exp ((n:ℝ)*Real.log (b n)) := by rw [Real.exp_nat_mul,Real.exp_log hn]
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlog.le (Nat.cast_nonneg n) |>.trans_eq (mul_comm _ _))

lemma combined {b : ℕ → ℝ} {B C rate : ℝ} (hB : 0 < B)
    (hb : Tendsto b atTop (𝓝 B)) (hrate : Real.log B < rate) (_hC : 0 ≤ C) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,C*(n:ℝ)^k*(b n)^n ≤ Real.exp (rate*(n:ℝ)) := by
  let rate₁ := (Real.log B+rate)/2
  have h₁ : Real.log B < rate₁ := by dsimp [rate₁]; linarith
  have h₂ : 0 < rate-rate₁ := by dsimp [rate₁]; linarith
  filter_upwards [moving_base hB hb h₁,polynomial (C := C) h₂ k] with n hn hp
  have hm := mul_le_mul hp hn.2 (pow_nonneg hn.1.le _) (Real.exp_pos ((rate-rate₁)*(n:ℝ))).le
  apply hm.trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

lemma union_decay {α β C : ℝ} (hαβ : α < β) (hβ : 0 < β) (hC : 0 < C) :
    Tendsto (fun n : ℕ => Real.exp (Real.exp (α*n)-C*Real.exp (β*n))) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => Real.exp ((α-β)*(n:ℝ))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by linarith : α-β<0)
  have hbig : Tendsto (fun n : ℕ => Real.exp (β*(n:ℝ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hβ)
  have hprod : Tendsto (fun n : ℕ => (Real.exp ((α-β)*(n:ℝ))-C)*Real.exp (β*(n:ℝ))) atTop atBot :=
    (hbase.sub_const C).neg_mul_atTop (by simpa using neg_neg_of_pos hC) hbig
  have he (n : ℕ) : (Real.exp ((α-β)*(n:ℝ))-C)*Real.exp (β*(n:ℝ)) =
      Real.exp (α*n)-C*Real.exp (β*n) := by
    rw [sub_mul,← Real.exp_add]
    congr 2
    ring
  exact Real.tendsto_exp_atBot.comp (by simpa only [he] using hprod)

end CoveringGrowth

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_SourceParameters
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace SourceParameters
open Filter
open scoped Topology
lemma a_pos : 0 < a := by norm_num [a,ε]
lemma D_pos : 0 < D := by norm_num [D]
lemma L_limit : Tendsto L atTop (𝓝 (D+a)) := by
  unfold L b
  convert (tendsto_const_nhds (x := D)).add
    (((tendsto_const_nhds (x := (1:ℝ))).add RadialShell.inv_limit).const_mul a) |>.add
      (RadialShell.eta_limit.const_mul 5) using 1 ; simp
lemma base_limit : Tendsto (fun n => L n/a) atTop (𝓝 ((D+a)/a)) :=
  L_limit.div_const a
lemma base_log : Real.log ((D+a)/a) < 1/200 := by
  have hp : 0 < (D+a)/a := div_pos (add_pos D_pos a_pos) a_pos
  have hh := Real.log_le_sub_one_of_pos hp
  have he : (D+a)/a-1 < (1:ℝ)/200 := by norm_num [D,a,ε]
  exact hh.trans_lt he
lemma length_rate : ∀ᶠ n : ℕ in atTop,∀ R : ℝ,0 ≤ R → R ≤ (n:ℝ)^2 →
    (N n R:ℝ) ≤ Real.exp ((1/100:ℝ)*(n:ℝ)) := by
  have ha := a_pos
  have hv : 0 < v := by norm_num [v]
  have hb : 0 < (D+a)/a := div_pos (add_pos D_pos a_pos) a_pos
  have hx := CoveringGrowth.combined (C := 1281) hb base_limit
    (base_log.trans (by norm_num : (1:ℝ)/200<1/100)) (by norm_num) 2
  filter_upwards [hx,eventually_ge_atTop 1] with n hn hn1 R hR hRn
  have hnp : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hbase : 1 ≤ L n/a := by
    apply (le_div_iff₀ a_pos).mpr
    have hh : 0 ≤ a*(n:ℝ)⁻¹ := by positivity
    have heta : 0 ≤ RadialShell.η n := by unfold RadialShell.η; positivity
    dsimp [L,b]
    nlinarith only [D_pos,hh,heta]
  have hp : 1 ≤ (L n/a)^n := one_le_pow₀ hbase
  have hceil : (N n R:ℝ) ≤ 20*R/v*(L n/a)^n+1 := by
    exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ 20*R/v*(L n/a)^n)).le
  calc
    _ ≤ 20*R/v*(L n/a)^n+1 := hceil
    _ ≤ 1280*(n:ℝ)^2*(L n/a)^n+1 := by
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRn (by norm_num : (0:ℝ)≤1280)) (le_trans (by norm_num) hp)
      norm_num [v] at *
      linarith only [hh]
    _ ≤ 1281*(n:ℝ)^2*(L n/a)^n := by
      have hn2 : 1 ≤ (n:ℝ)^2 := one_le_pow₀ hnp
      have hh := mul_le_mul hn2 hp (by norm_num : (0:ℝ)≤1) (sq_nonneg (n:ℝ))
      nlinarith only [hh]
    _ ≤ _ := hn
end SourceParameters

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_EntropyRates
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace EntropyRates
open Filter SourceParameters LocalizationRounding
open scoped Topology Classical
lemma mesh {n : ℕ} (hn : 0 < n) : h n = 1/(100*(n:ℝ)^5) := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  dsimp [h,RadialShell.η]
  field_simp
lemma mesh_pos {n : ℕ} (hn : 0 < n) : 0 < h n := by rw [mesh hn]; positivity
lemma error_bound {n : ℕ} (hn : 1 ≤ n) : Real.sqrt n*h n/2 ≤ RadialShell.η n := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hs : Real.sqrt n ≤ (n:ℝ) := (Real.sqrt_le_iff).mpr ⟨hn0.le,by nlinarith only [hn1]⟩
  have he : (n:ℝ)*h n/2 = RadialShell.η n/200 := by dsimp [h]; field_simp ; ring
  calc
    _ ≤ (n:ℝ)*h n/2 := by gcongr; exact mesh_pos (by omega) |>.le
    _ = _ := he
    _ ≤ _ := by have hh : 0 ≤ RadialShell.η n := by unfold RadialShell.η; positivity
                linarith only [hh]
lemma alphabet_rate : ∀ᶠ n : ℕ in atTop,
    ((alphabet n (h n) (L n)).card:ℝ) ≤ Real.exp ((n:ℝ)^2) := by
  filter_upwards [L_limit.eventually (gt_mem_nhds (show D+a<3 by norm_num [D,a,ε])),
    CoveringGrowth.polynomial (C := 601) (by norm_num : (0:ℝ)<1) 5,eventually_ge_atTop 1] with n hL hp hn
  have hnp : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hm : 0 < h n := mesh_pos (by omega)
  have hLp : 0 ≤ L n := by
    have ha := a_pos; have hD := D_pos; have hh := mesh_pos (by omega : 0<n)
    dsimp [L,b,RadialShell.η]; positivity
  have hQ := alphabet_card (n := n) (mesh_pos (n := n) (by omega)) hLp
  apply hQ.trans
  have hb : 1+2*(L n)/h n ≤ 601*(n:ℝ)^5 := by
    have h5 : 1 ≤ (n:ℝ)^5 := one_le_pow₀ (by exact_mod_cast hn)
    have h3 : L n ≤ 3 := hL.le
    calc
      _ ≤ 1+2*3/h n := by gcongr
      _ = 1+600*(n:ℝ)^5 := by rw [mesh (by omega)]; field_simp ; ring
      _ ≤ _ := by linarith only [h5]
  calc
    _ ≤ (601*(n:ℝ)^5)^n := pow_le_pow_left₀ (by positivity) hb n
    _ ≤ (Real.exp (n:ℝ))^n := pow_le_pow_left₀ (by positivity) (by simpa using hp) n
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

lemma list_rate : ∀ᶠ n : ℕ in atTop,∀ R : ℝ,0≤R → R≤(n:ℝ)^2 →
    (Fintype.card (BoundedLists n (h n) (L n) (N n R)):ℝ) ≤
      Real.exp (Real.exp ((1/10:ℝ)*(n:ℝ))) := by
  filter_upwards [alphabet_rate,length_rate,
    CoveringGrowth.polynomial (C := 3) (by norm_num : (0:ℝ)<9/100) 2,
    eventually_ge_atTop 1] with n hQ hN hp hn R hR hRn
  let E := Real.exp ((1/100:ℝ)*(n:ℝ))
  have hNE : (N n R:ℝ) ≤ E := hN R hR hRn
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (by positivity)
  have hn2 : 1 ≤ (n:ℝ)^2 := one_le_pow₀ (by exact_mod_cast hn)
  have hq : (max 1 (alphabet n (h n) (L n)).card:ℝ) ≤ Real.exp ((n:ℝ)^2) := by
    exact max_le (Real.one_le_exp_iff.mpr (sq_nonneg _)) hQ
  have hcard := Nat.cast_le (α := ℝ) |>.mpr (boundedLists_card n (N n R) (h n) (L n))
  push_cast at hcard
  apply hcard.trans
  calc
    _ ≤ Real.exp ((N n R:ℝ)+1)*(Real.exp ((n:ℝ)^2))^(N n R) := by
      gcongr
      exact le_trans (by linarith : (N n R:ℝ)+1 ≤ ((N n R:ℝ)+1)+1) (Real.add_one_le_exp _)
    _ = Real.exp (((N n R:ℝ)+1)+(N n R:ℝ)*(n:ℝ)^2) := by rw [← Real.exp_nat_mul,← Real.exp_add]
    _ ≤ Real.exp (3*(n:ℝ)^2*E) := by
      apply Real.exp_le_exp.mpr
      have h1 := mul_le_mul_of_nonneg_right hNE (sq_nonneg (n:ℝ))
      have h2 := mul_le_mul_of_nonneg_right hn2 (show 0 ≤ E from (Real.exp_pos _).le)
      dsimp [E] at *
      nlinarith only [hNE,hE,h1,h2]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ Real.exp ((9/100:ℝ)*(n:ℝ))*E := by gcongr
        _ = _ := by dsimp [E]; rw [← Real.exp_add]; congr 1; ring
end EntropyRates

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_LocalizationRates
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace LocalizationRates
open Filter SourceParameters Metric MeasureTheory
open scoped Topology ENNReal
lemma n_eta_limit : Tendsto (fun n : ℕ => (n:ℝ)*RadialShell.η n) atTop (𝓝 0) := by
  have he (n : ℕ) : (n:ℝ)*RadialShell.η n = ((n:ℝ)⁻¹)^3 := by
    by_cases hn : n=0
    · subst n; norm_num [RadialShell.η]
    · have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn
      dsimp [RadialShell.η]; field_simp
  simpa only [he,zero_pow (by norm_num : 3≠0)] using RadialShell.inv_limit.pow 3
lemma rminus_limit : Tendsto rminus atTop (𝓝 a) := by
  convert ((tendsto_const_nhds (x := (1:ℝ))).sub (RadialShell.log_div_limit.const_mul 10)).const_mul a using 1 <;>
    first | rfl | simp only [mul_zero,sub_zero,mul_one] | (funext n; dsimp [rminus]; ring)
lemma outer_rate : ∀ᶠ n : ℕ in atTop,0 < β n ∧ (β n/a)^n ≤ 3 := by
  have hlog3 : 1 < Real.log 3 := (Real.lt_log_iff_exp_lt (by norm_num)).mpr
    (Real.exp_one_lt_d9.trans (by norm_num))
  have ht : Tendsto (fun n : ℕ => 1+4*(n:ℝ)*RadialShell.η n/a) atTop (𝓝 1) := by
    convert (tendsto_const_nhds (x := (1:ℝ))).add ((n_eta_limit.const_mul 4).div_const a) using 1 <;> (try funext n) <;> ring_nf
  filter_upwards [ht.eventually_le_const hlog3,eventually_ge_atTop 1] with n hn hn1
  have hnp : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have ha := a_pos
  have hβ : 0 < β n := by dsimp [β,b,RadialShell.η]; positivity
  refine ⟨hβ,?_⟩
  have hb : 0 < β n/a := div_pos hβ ha
  have hlog := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hb) hnp.le
  have he : (n:ℝ)*(β n/a-1) = 1+4*(n:ℝ)*RadialShell.η n/a := by
    dsimp [β,b]; field_simp ; ring
  rw [he] at hlog
  calc
    _ = Real.exp ((n:ℝ)*Real.log (β n/a)) := by rw [Real.exp_nat_mul,Real.exp_log hb]
    _ ≤ Real.exp (Real.log 3) := Real.exp_le_exp.mpr (hlog.trans hn)
    _ = _ := Real.exp_log (by norm_num)
lemma inner_rate : ∀ᶠ n : ℕ in atTop,0 < rminus n ∧
    (n:ℝ)^2/(2*v)*(rminus n/a)^n ≤ 1/200 := by
  filter_upwards [rminus_limit.eventually (lt_mem_nhds a_pos),eventually_ge_atTop 10] with n hr hn
  have hnp : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have h10 : (10:ℝ)≤n := by exact_mod_cast hn
  have ha := a_pos
  have hb : 0 < rminus n/a := div_pos hr ha
  have hlog := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hb) hnp.le
  have he : (n:ℝ)*(rminus n/a-1) = -10*Real.log n := by dsimp [rminus]; field_simp ; ring
  rw [he] at hlog
  have hp : (rminus n/a)^n ≤ ((n:ℝ)⁻¹)^10 := by
    calc
      _ = Real.exp ((n:ℝ)*Real.log (rminus n/a)) := by rw [Real.exp_nat_mul,Real.exp_log hb]
      _ ≤ Real.exp (-10*Real.log n) := Real.exp_le_exp.mpr hlog
      _ = _ := by rw [show -10*Real.log n = -(10*Real.log n) by ring,Real.exp_neg,show Real.exp (10*Real.log n) = (n:ℝ)^10 by simpa using Real.exp_nat_mul (Real.log n) 10 |>.trans (by rw [Real.exp_log hnp])]; simp only [inv_pow]
  refine ⟨hr,?_⟩
  calc
    _ ≤ (n:ℝ)^2/(2*v)*((n:ℝ)⁻¹)^10 := mul_le_mul_of_nonneg_left hp (by norm_num [v]; positivity)
    _ = 32/((n:ℝ)^8) := by norm_num [v]; field_simp
    _ ≤ _ := by
      apply (div_le_iff₀ (pow_pos hnp 8)).mpr
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤10) h10 8
      norm_num at hh ⊢
      linarith only [hh]
lemma dimension : ∀ᶠ n : ℕ in atTop,1≤n ∧ 0 < rminus n ∧ 0<β n ∧
    (β n/a)^n≤3 ∧ (n:ℝ)^2/(2*v)*(rminus n/a)^n≤1/200 ∧
    (2*(n:ℝ)/a)*(Real.sqrt n*h n/2)≤1 := by
  have ht : Tendsto (fun n : ℕ => 2*(n:ℝ)*RadialShell.η n/a) atTop (𝓝 0) := by
    convert (n_eta_limit.const_mul 2).div_const a using 1 <;> (try funext n) <;> ring_nf
  filter_upwards [outer_rate,inner_rate,eventually_ge_atTop 1,ht.eventually_le_const (by norm_num : (0:ℝ)<1)] with n ho hi hn ht
  refine ⟨hn,hi.1,ho.1,ho.2,hi.2,?_⟩
  calc
    _ ≤ (2*(n:ℝ)/a)*RadialShell.η n := mul_le_mul_of_nonneg_left (EntropyRates.error_bound hn) (by have := a_pos; positivity)
    _ ≤ _ := by simpa only [div_mul_eq_mul_div] using ht
end LocalizationRates

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_BodyVolume
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace BodyVolume
open Set MeasureTheory Metric SphericalLaw RandomBody CapCost
open scoped ENNReal NNReal

instance law_probability {n : ℕ} [NeZero n] (e : Sphere n) (a : ℝ) :
    IsProbabilityMeasure (law e a) := inferInstanceAs (IsProbabilityMeasure (PoissonSample.simpleSample _ _))

end BodyVolume

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_SourceLocalization
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2

namespace SourceLocalization
open Set Metric MeasureTheory SourceParameters LocalizationRates LocalizationRounding PatternGeometry PatternEnumeration
open scoped ENNReal Classical
lemma good_mono_inner {n : ℕ} {J : Type u_1} [Fintype J] (p : J → Space n)
    {a D r r' b C : ℝ} (hr : r' ≤ r) : roundedGood p a D r b C ⊆ roundedGood p a D r' b C := by
  intro y hy
  exact ⟨hy.1,fun i => hr.trans (hy.2.1 i),hy.2.2⟩
lemma low_le {n : ℕ} : RadialShell.low a n ≤ rround n := by
  have he : 0≤RadialShell.η n := by unfold RadialShell.η; positivity
  dsimp [RadialShell.low,rround,rminus]
  simp only [mul_div_assoc]
  linarith only [he]
lemma pattern_good {n : ℕ} {R : ℝ} (P : Patterns n R) :
    volume (closedBall (0:Space n) D) ≤ 4*volume (roundedGood (points P.val) a D
      (RadialShell.low a n) (RadialShell.high a n) (2*Cloc*R)) :=
  P.property.trans (mul_le_mul_right (measure_mono (good_mono_inner _ low_le)) 4)
end SourceLocalization

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_BodySelection
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace BodySelection
open Set Metric MeasureTheory Filter SourceParameters LocalizationRates PatternEnumeration SourceLocalization SphericalLaw
open scoped ENNReal Topology Classical
lemma union_bound {n : ℕ} [NeZero n] (e : Sphere n) {R t : ℝ} (ht : 0≤t)
    (hlist : (Fintype.card (LocalizationRounding.BoundedLists n (h n) (L n) (N n R)):ℝ)≤Real.exp (Real.exp ((1/10:ℝ)*n)))
    (hP : ∀ P : Patterns n R,(BodyVolume.law e a).real (PatternTail.coverEvent (points P.val) a D)≤t) :
    (BodyVolume.law e a).real (bad R) ≤ Real.exp (Real.exp ((1/10:ℝ)*n))*t := by
  have hc : (Fintype.card (Patterns n R):ℝ)≤Real.exp (Real.exp ((1/10:ℝ)*n)) :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hlist
  calc
    _ ≤ ∑ P : Patterns n R,(BodyVolume.law e a).real (PatternTail.coverEvent (points P.val) a D) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _P : Patterns n R,t := Finset.sum_le_sum (fun P _ => hP P)
    _ = (Fintype.card (Patterns n R):ℝ)*t := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc ht

theorem uniform : ∃ c : ℝ,0 < c ∧ ∃ n₀ : ℕ,∀ n : ℕ,n₀≤n →
    ∀ [NeZero n] [Fact (2≤n)] (_e : Sphere n) (R : ℝ),
    1≤R → R ≤ c*(n:ℝ)*Real.log n → R≤(n:ℝ)^2 →
    ∃ U : PoissonConfig.Config (Sphere n),
      2*v*volume.real (closedBall (0:Space n) a)<volume.real (RandomBody.body (b n) 1 U) ∧
      U ∉ bad R := by
  obtain ⟨c,hc,n₁,hbound⟩ := SourcePatternTail.uniform
  have hdecay := CoveringGrowth.union_decay (α:=1/10) (β:=1/2) (C:=1) (by norm_num) (by norm_num) (by norm_num)
  have hevent : ∀ᶠ n : ℕ in atTop,
      Real.exp (Real.exp ((1/10:ℝ)*n)-Real.exp ((1/2:ℝ)*n))<1/20 := by
    simpa only [one_mul] using hdecay.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/20))
  have hd := LocalizationRates.dimension
  have hE := EntropyRates.list_rate
  obtain ⟨n₂,hn₂⟩ := eventually_atTop.mp (hevent.and (hd.and hE))
  refine ⟨c,hc,max n₁ n₂,?_⟩
  intro n hn _ _ e R hR hRc hRn
  have hdim := (hn₂ n (le_trans (le_max_right _ _) hn)).2.1
  have hlist := (hn₂ n (le_trans (le_max_right _ _) hn)).2.2 R (by linarith only [hR]) hRn
  have hP (P : Patterns n R) : (BodyVolume.law e a).real (PatternTail.coverEvent (points P.val) a D) ≤ Real.exp (-Real.exp ((1/2:ℝ)*n)) := by
    cases isEmpty_or_nonempty (Fin P.val.1.val) with
    | inl h =>
      have hem : PatternTail.coverEvent (points P.val) a D=∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro U hU
        obtain ⟨i,_⟩ := hU 0 (mem_closedBall_self D_pos.le)
        exact isEmptyElim i
      rw [hem,measureReal_empty]
      positivity
    | inr h =>
      exact hbound n (le_trans (le_max_left _ _) hn) _ e _ R (by linarith only [hR]) hRc hRn (by simpa using (Nat.le_of_lt_succ P.val.1.isLt)) (pattern_good P)
  have hbad : (BodyVolume.law e a).real (bad R)<1/20 := by
    apply lt_of_le_of_lt (union_bound e (Real.exp_pos _).le hlist hP)
    rw [← Real.exp_add]
    exact (hn₂ n (le_trans (le_max_right _ _) hn)).1
  have hvol := volume_lower e hdim.2.2.1 hdim.2.2.2.1
  by_contra! hnone
  have hsub : {U : PoissonConfig.Config (Sphere n) | 2*v*volume.real (closedBall (0:Space n) a)<volume.real (RandomBody.body (b n) 1 U)} ⊆ bad R := by
    intro U hU
    exact hnone U hU
  have hh := measureReal_mono (μ:=BodyVolume.law e a) hsub (measure_ne_top _ _)
  linarith only [hbad,hvol,hh]
end BodySelection

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_SourceScale
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace SourceScale
open Filter SourceParameters
open scoped Topology
lemma dimension {c : ℝ} (hc : 0 < c) : ∀ᶠ n : ℕ in atTop,
    2≤n ∧ 1 ≤ c*(n:ℝ)*Real.log n ∧ c*(n:ℝ)*Real.log n≤(n:ℝ)^2 := by
  have hlog : ∀ᶠ n : ℕ in atTop,1≤Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  have hlarge : ∀ᶠ n : ℕ in atTop,1/c≤(n:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (1/c))
  filter_upwards [hlog,hlarge,RadialShell.log_div_limit.eventually_le_const (one_div_pos.mpr hc),eventually_ge_atTop 2] with n hl hn hs hn2
  have hnp : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hcn : 1 ≤ c*(n:ℝ) := by have hh := (div_le_iff₀ hc).mp hn; linarith only [hh]
  refine ⟨hn2,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left hl (mul_nonneg hc.le hnp.le)
    exact hcn.trans (by simpa only [mul_one] using hh)
  · have hh := (div_le_iff₀ hnp).mp hs
    have hm := mul_le_mul_of_nonneg_left hh (mul_nonneg hc.le hnp.le)
    have he : (c*(n:ℝ))*(1/c*(n:ℝ))=(n:ℝ)^2 := by field_simp
    rwa [he] at hm
end SourceScale

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_Main
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

namespace SourceMain
open Set Metric MeasureTheory Filter TranslativeCovering SourceParameters LocalizationRates
open scoped ENNReal Topology Classical

theorem main : TranslativeCovering.MainStatement := by
  obtain ⟨c,hc,n₁,hselect⟩ := BodySelection.uniform
  obtain ⟨n₂,hn₂⟩ := eventually_atTop.mp ((SourceScale.dimension hc).and LocalizationRates.dimension)
  refine ⟨c/2,by positivity,max n₁ n₂,?_⟩
  intro n hn
  have hdim := hn₂ n (le_trans (le_max_right _ _) hn)
  let : NeZero n := ⟨by omega⟩
  let : Fact (2≤n) := ⟨hdim.1.1⟩
  let e : SphericalLaw.Sphere n := ⟨(EuclideanSpace.basisFun (Fin n) ℝ) (0:Fin n),by
    simp only [mem_sphere_zero_iff_norm]
    exact (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one _⟩
  let R := c*(n:ℝ)*Real.log n
  obtain ⟨U,hvol,hbad⟩ := hselect n (le_trans (le_max_left _ _) hn) e R hdim.1.2.1 le_rfl hdim.1.2.2
  let K := RandomBody.body (b n) 1 U
  have hb : 0<b n := by have ha := a_pos; dsimp [b]; positivity
  have hbody : ConvexBody K := RandomBody.body_isBody _ _ _ hb (by norm_num)
  have hKtop : volume K≠∞ := hbody.1.measure_ne_top
  have hK0 : volume K≠0 := ne_of_gt ((isOpen_interior.measure_pos volume hbody.2.2).trans_le (measure_mono interior_subset))
  have hP (P : PeriodicCover K) : ENNReal.ofReal R ≤ volume K*P.intensity := by
    apply le_of_not_gt
    intro hlt
    let := P.discrete
    let := P.fullrank
    let B := Module.Free.chooseBasis ℤ P.lattice
    let F := ZSpan.fundamentalDomain (B.ofZLatticeBasis ℝ)
    have hF : IsAddFundamentalDomain P.lattice F volume := ZLattice.isAddFundamentalDomain B volume
    have hF0 : volume F≠0 := ZSpan.measure_fundamentalDomain_ne_zero _
    have hFtop : volume F≠∞ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
    have hFvol : ENNReal.ofReal (ZLattice.covolume P.lattice volume)=volume F := by
      rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ hF,Measure.real,ENNReal.ofReal_toReal hFtop]
    have hdensity : volume K*((Fintype.card (Fin P.m):ℝ≥0∞)/volume F)≤ENNReal.ofReal R := by
      simpa only [PeriodicCover.intensity,Fintype.card_fin,hFvol] using hlt.le
    have hno := AllLatticeExclusion.no_cover hdim.1.2.1 hdim.1.2.2 hdim.2.1 hdim.2.2.1 hdim.2.2.2.1
      hdim.2.2.2.2.1 hdim.2.2.2.2.2.1 hdim.2.2.2.2.2.2 U hvol hbad P.lattice
      P.offsets hF hF0 hFtop hdensity
    exact hno P.covers
  have hlower : ENNReal.ofReal R≤thetaT K := by
    rw [periodization_exact hbody,thetaPer]
    exact le_iInf fun P => hP P.val
  refine ⟨K,hbody,RandomBody.body_symm _ _ _,?_⟩
  apply lt_of_lt_of_le _ hlower
  have hRpos : 0<R := lt_of_lt_of_le (by norm_num) hdim.1.2.1
  have hhalf : c/2*(n:ℝ)*Real.log n=R/2 := by dsimp [R]; ring
  rw [hhalf]
  exact ENNReal.ofReal_lt_ofReal_iff hRpos |>.mpr (by linarith only [hRpos])
end SourceMain

theorem TranslativeCovering.main_oai : TranslativeCovering.MainStatement := SourceMain.main

end OAI
end

theorem solution : type_of% @OAI.TranslativeCovering.main_oai := @OAI.TranslativeCovering.main_oai
