-- Prove2me | solution 1 for OAI.KServer.JointEmbedding.key_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T15:02:57.511642+00:00
-- url     : https://prove2.me/submissions/0a9bc39b-c3fe-4e12-b958-db620688f36e

import Mathlib
import Definitions.Def_KServer
import Definitions.Def_OAIQ17Ks000

section
-- module Solutions.OAIQ17_KS.KServer_Behavior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace KServer
universe u

section OfflineComparison
variable {k : ℕ} [NeZero k] {X : Type u} [MetricSpace X]

lemma optimalCost_nonneg (s : Configuration k X) (σ : List X) : 0  ≤  optimalCost s σ := by
  exact le_csInf (Set.range_nonempty _) (by rintro _ ⟨w,rfl⟩; exact serviceCost_nonneg _ _ _)

end OfflineComparison


/-! ## Explicit causal realization of finite hidden-state algorithms.
This discharges a policy-existence interface needed both by correlated rounding
and by the fictitious-prefix episode extraction. It is not a competitiveness
premise: the machine below is arbitrary and its behavioral policy is constructed. -/
end KServer

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Amplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace KServer
universe u
namespace Episode
open Finset
variable {k : ℕ} {X : Type u} [MetricSpace X]

omit [MetricSpace X] in
lemma configurationAfter_cons (s : Configuration k X) (r : X) (i : Fin k)
    (h : List (X × Fin k)) :
    configurationAfter s ((r,i)::h) = configurationAfter (serve s i r) h := rfl

lemma traceCost_append (s : Configuration k X) (h g : List (X × Fin k)) :
    traceCost s (h++g) = traceCost s h + traceCost (configurationAfter s h) g := by
  induction h generalizing s with
  | nil => simp [traceCost,configurationAfter]
  | cons ri h ih =>
    rcases ri with ⟨r,i⟩
    simp only [List.cons_append,traceCost,configurationAfter_cons,ih]
    ring

lemma serviceTrace_cost (s : Configuration k X) (σ : List X)
    (j : Fin σ.length → Fin k) : traceCost s (serviceTrace σ j) = serviceCost s σ j := by
  induction σ generalizing s with
  | nil => rfl
  | cons r σ ih => exact congrArg (fun x => dist (s (j 0)) r+x) (ih _ _)

end Episode
end KServer

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Ranks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
namespace KServer.RankTracking

variable {Ω : Type*} [Fintype Ω]

lemma avg_add (w f g : Ω → ℝ) : avg w (fun ω => f ω+g ω)=avg w f+avg w g := by
  simp [avg,mul_add,sum_add_distrib]
lemma avg_mul (w f : Ω → ℝ) (c : ℝ) : avg w (fun ω => c*f ω)=c*avg w f := by
  simp only [avg,mul_sum,mul_left_comm (w _) c]
lemma avg_sum (w : Ω → ℝ) {ι : Type*} [Fintype ι] (f : ι → Ω → ℝ) :
    avg w (fun ω => ∑ i, f i ω)=∑ i, avg w (f i) := by
  simp only [avg,mul_sum]; rw [sum_comm]
lemma avg_mono {w f g : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (h : ∀ ω, f ω ≤ g ω) :
    avg w f ≤ avg w g := sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (hw ω)
lemma avg_const (w : Ω → ℝ) (hw : ∑ ω, w ω=1) (c : ℝ) : avg w (fun _ => c)=c := by
  simp [avg,←sum_mul,hw]

end KServer.RankTracking

/-! Construction of the rank martingales from the actual finite hidden law.
No filtering identity is postulated in the construction below. -/
namespace KServer.PosteriorRanks
open Finset
open RankTracking
variable {Ω : Type*} [Fintype Ω]

lemma posterior_avg {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (H : Ω → ℕ) (f : Ω → ℝ) :
    avg w (posterior w H f)=avg w f := by
  simpa only [one_mul] using weighted_posterior hw H f (fun _ => 1) (by intro _ _ _; rfl)

lemma posterior_sub (w : Ω → ℝ) (H : Ω → ℕ) (f g : Ω → ℝ) (ω : Ω) :
    posterior w H (fun z => f z-g z) ω = posterior w H f ω-posterior w H g ω := by
  simp only [posterior,numerator,mul_sub,sum_sub_distrib,sub_div]

end KServer.PosteriorRanks


/-! ## The actual finite hidden experiment of §02

The input is drawn once. Its selected optimum is hidden, whereas a finite
independent partition tape and the true request prefix are observed. No
conditioning on rounding outcomes enters this experiment. -/
namespace KServer.PosteriorRanks
variable {Ω : Type*} [Fintype Ω]

lemma mass_pos_of_weight {w : Ω → ℝ} (hw : ∀ ω, 0≤w ω) (H : Ω → ℕ)
    (ω : Ω) (hω : 0<w ω) : 0 < mass w H (H ω) := by
  apply hω.trans_le
  exact single_le_sum (fun z _ => hw z) (by simp [fiber])

lemma posterior_sum {I : Type*} [Fintype I] (w : Ω → ℝ) (H : Ω → ℕ)
    (f : I → Ω → ℝ) (ω : Ω) :
    posterior w H (fun z => ∑ i,f i z) ω=∑ i,posterior w H (f i) ω := by
  simp only [posterior,numerator,mul_sum,sum_div]
  rw [sum_comm]

lemma posterior_add (w : Ω → ℝ) (H : Ω → ℕ) (f g : Ω → ℝ) (ω : Ω) :
    posterior w H (fun z => f z+g z) ω=posterior w H f ω+posterior w H g ω := by
  simp [posterior,numerator,mul_add,sum_add_distrib,add_div]

lemma posterior_mul (w : Ω → ℝ) (H : Ω → ℕ) (f : Ω → ℝ) (c : ℝ) (ω : Ω) :
    posterior w H (fun z => f z*c) ω=posterior w H f ω*c := by
  simp only [posterior,numerator,←mul_assoc,←sum_mul]
  ring

end KServer.PosteriorRanks

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Experiments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset

namespace KServer.FiniteExperiment
attribute [local instance] Classical.propDecidable
open Finset Episode PosteriorRanks
universe u v
variable {Y : Type u} [MetricSpace Y] [Fintype Y] {k H : ℕ} [NeZero k]

omit [Fintype Y] in
lemma optimalTrace_cost (s : Configuration k Y) (σ : Fin H → Y) :
    traceCost s (optimalTrace s σ)=optimalCost s (List.ofFn σ) := by
  rw [optimalTrace,serviceTrace_cost]
  exact (optimalCost_attained s (List.ofFn σ)).choose_spec

omit [Fintype Y] in
lemma optimalTrace_get_request (s : Configuration k Y) (σ : Fin H → Y) (t : Fin H) :
    ((optimalTrace s σ)[t.val]'(by rw [optimalTrace_length]; exact t.isLt)).1=σ t := by
  have he := congrArg (fun l : List Y => l[t.val]?) (optimalTrace_requests s σ)
  apply Option.some.inj
  simpa only [List.getElem?_map,List.getElem?_eq_getElem
    (show t.val<(optimalTrace s σ).length by rw [optimalTrace_length]; exact t.isLt),
    Option.map_some,List.getElem?_ofFn,Fin.isLt,dite_eq_left] using he

omit [Fintype Y] in
lemma hidden_step (s : Configuration k Y) (σ : Fin H → Y) (t : Fin H) :
    hidden s σ (t.val+1)=serve (hidden s σ t.val) (mover s σ t) (σ t) := by
  have ht : t.val<(optimalTrace s σ).length := by rw [optimalTrace_length]; exact t.isLt
  rw [hidden,List.take_succ_eq_append_getElem ht,configurationAfter_append]
  simp only [configurationAfter]
  rw [optimalTrace_get_request]
  rfl

omit [Fintype Y] in
lemma hidden_covers (s : Configuration k Y) (σ : Fin H → Y) (t : Fin H) :
    hidden s σ (t.val+1) (mover s σ t)=σ t := by
  rw [hidden_step]
  simp [serve]

variable {T : Type v} [Fintype T]

omit [MetricSpace Y] in
lemma weight_nonneg (law : FiniteDistribution (Fin H → Y)) (tape : FiniteDistribution T)
    (ω : (Fin H → Y) × T) : 0≤weight law tape ω :=
  mul_nonneg (law.property.1 _) (tape.property.1 _)


omit [Fintype Y] in
lemma hidden_movement (s : Configuration k Y) (σ : Fin H → Y) (t : Fin H) :
    (∑ i,dist (hidden s σ t.val i) (hidden s σ (t.val+1) i))=
      dist (hidden s σ t.val (mover s σ t)) (σ t) := by
  classical
  rw [hidden_step]
  simp [serve,Function.update_apply,apply_ite]

omit [Fintype Y] in
lemma hidden_total_cost (s : Configuration k Y) (σ : Fin H → Y) :
    (∑ t : Fin H,∑ i,dist (hidden s σ t.val i) (hidden s σ (t.val+1) i))=
      optimalCost s (List.ofFn σ) := by
  have he (n : ℕ) (hn : n≤H) :
      traceCost s ((optimalTrace s σ).take n)=
        ∑ t ∈ range n,∑ i,dist (hidden s σ t i) (hidden s σ (t+1) i) := by
    induction n with
    | zero => simp [traceCost]
    | succ n ih =>
      have hlt : n<(optimalTrace s σ).length := by rw [optimalTrace_length]; omega
      rw [List.take_succ_eq_append_getElem hlt,traceCost_append,ih (by omega),sum_range_succ]
      congr 1
      rw [hidden_movement s σ ⟨n,by omega⟩]
      simp only [traceCost,add_zero]
      rw [optimalTrace_get_request s σ ⟨n,by omega⟩]
      rfl
  have htake : (optimalTrace s σ).take H=optimalTrace s σ := by
    apply List.take_of_length_le
    exact (optimalTrace_length s σ).le
  rw [←optimalTrace_cost,←htake,he H le_rfl]
  exact (Finset.sum_range (fun t : ℕ => ∑ i,
    dist (hidden s σ t i) (hidden s σ (t+1) i))).symm

omit [MetricSpace Y] in
lemma requestHistory_eq_iff (t : ℕ) (σ ρ : Fin H → Y) :
    requestHistory t σ=requestHistory t ρ ↔ requestPrefix σ t=requestPrefix ρ t := by
  unfold requestHistory
  rw [Fin.val_inj,(Fintype.equivFin _).injective.eq_iff]

omit [MetricSpace Y] [Fintype Y] [NeZero k] in
lemma metricCount_nonneg (c : Configuration k Y) (y : Y) : 0 ≤ metricCount c y := by
  classical
  exact sum_nonneg fun i _ => by split_ifs <;> norm_num

omit [MetricSpace Y] [NeZero k] in
lemma metricCount_total (c : Configuration k Y) : ∑ y,metricCount c y=(k:ℝ) := by
  classical
  simp only [metricCount]
  rw [sum_comm]
  simp

omit [MetricSpace Y] [Fintype Y] [NeZero k] in
lemma metricCount_at (c : Configuration k Y) (y : Y) (h : ∃ i,c i=y) :
    1 ≤ metricCount c y := by
  classical
  obtain ⟨i,hi⟩ := h
  have hs := single_le_sum (s := (univ : Finset (Fin k))) (f := fun j =>
    if c j=y then (1:ℝ) else 0) (fun j _ => by split_ifs <;> norm_num) (mem_univ i)
  simpa [hi,metricCount] using hs

lemma mu_nonneg (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : ℕ) (σ : Fin H → Y) (y : Y) : 0 ≤ mu s law t σ y :=
  posterior_nonneg law.property.1 _ (fun _ => metricCount_nonneg _ _) _

lemma mu_total (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : ℕ) (σ : Fin H → Y) (hσ : 0<law.val σ) : ∑ y,mu s law t σ y=(k:ℝ) := by
  unfold mu
  rw [←posterior_sum]
  exact posterior_fiber_const σ (fun ρ _ => metricCount_total _) (mass_pos_of_weight law.property.1 _ σ hσ).ne'

omit [MetricSpace Y] in
lemma request_of_history (t : Fin H) (σ ρ : Fin H → Y)
    (h : requestHistory (t.val+1) σ=requestHistory (t.val+1) ρ) : σ t=ρ t := by
  have he := congrFun ((requestHistory_eq_iff _ _ _).mp h) t
  simpa [requestPrefix,t.isLt] using he

lemma mu_served (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : Fin H) (σ : Fin H → Y) (hσ : 0<law.val σ) : 1 ≤ mu s law (t.val+1) σ (σ t) := by
  have hc : posterior law.val (requestHistory (t.val+1)) (fun _ => (1:ℝ)) σ=1 :=
    posterior_fiber_const σ (fun _ _ => rfl) (mass_pos_of_weight law.property.1 _ σ hσ).ne'
  rw [←hc]
  apply posterior_mono_fiber law.property.1
  intro ρ hρ
  apply metricCount_at
  rw [←request_of_history t ρ σ hρ]
  exact ⟨mover s ρ t,hidden_covers s ρ t⟩

lemma mu_adapted (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : ℕ) (y : Y) : RankTracking.Adapted (requestHistory t) (fun σ => mu s law t σ y) :=
  posterior_adapted _ _ _

omit [MetricSpace Y] [Fintype Y] [NeZero k] in
lemma metricCount_move (c : Configuration k Y) (i : Fin k) (x y : Y) :
    metricCount (serve c i x) y=metricCount c y-(if c i=y then 1 else 0)+
      (if x=y then 1 else 0) := by
  classical
  unfold metricCount
  rw [←add_sum_erase univ _ (mem_univ i),←add_sum_erase univ _ (mem_univ i)]
  have he : (∑ j∈univ.erase i,if serve c i x j=y then (1:ℝ) else 0)=
      ∑ j∈univ.erase i,if c j=y then (1:ℝ) else 0 := by
    apply sum_congr rfl
    intro j hj
    simp [serve,Function.update_of_ne (mem_erase.mp hj).1]
  rw [he]
  simp only [serve,Function.update_self]
  ring

lemma muBefore_nonneg (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : Fin H) (σ : Fin H → Y) (y : Y) : 0 ≤ muBefore s law t σ y :=
  posterior_nonneg law.property.1 _ (fun _ => metricCount_nonneg _ _) _

lemma nu_nonneg (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : Fin H) (σ : Fin H → Y) (y : Y) : 0 ≤ nu s law t σ y := by
  apply posterior_nonneg law.property.1
  intro ρ
  split_ifs <;> norm_num

lemma nu_total (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : Fin H) (σ : Fin H → Y) (hσ : 0<law.val σ) : ∑ y,nu s law t σ y=1 := by
  classical
  unfold nu
  rw [←posterior_sum]
  apply posterior_fiber_const σ _ (mass_pos_of_weight law.property.1 _ σ hσ).ne'
  intro ρ _
  simp

lemma nu_le_muBefore (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : Fin H) (σ : Fin H → Y) (y : Y) : nu s law t σ y ≤ muBefore s law t σ y := by
  apply posterior_mono_fiber law.property.1
  intro ρ _
  split_ifs with he
  · exact metricCount_at _ _ ⟨mover s ρ t,he⟩
  · exact metricCount_nonneg _ _

lemma muBefore_total (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : Fin H) (σ : Fin H → Y) (hσ : 0<law.val σ) : ∑ y,muBefore s law t σ y=(k:ℝ) := by
  unfold muBefore
  rw [←posterior_sum]
  exact posterior_fiber_const σ (fun ρ _ => metricCount_total _) (mass_pos_of_weight law.property.1 _ σ hσ).ne'

/-- Exact one-mover decomposition used by the pilot potential. -/
lemma mu_move (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : Fin H) (σ : Fin H → Y) (hσ : 0<law.val σ) (y : Y) :
    mu s law (t.val+1) σ y=muBefore s law t σ y-nu s law t σ y+
      (if σ t=y then 1 else 0) := by
  classical
  unfold mu muBefore nu
  simp_rw [hidden_step,metricCount_move]
  rw [posterior_add,posterior_sub]
  congr 1
  apply posterior_fiber_const σ _ (mass_pos_of_weight law.property.1 _ σ hσ).ne'
  intro ρ hρ
  rw [request_of_history t ρ σ hρ]

lemma conditional_moveCost (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : Fin H) (σ : Fin H → Y) :
    (∑ y,nu s law t σ y*dist y (σ t))=
      posterior law.val (requestHistory (t.val+1))
        (fun ρ => dist (hidden s ρ t.val (mover s ρ t)) (ρ t)) σ := by
  classical
  unfold nu
  simp_rw [←posterior_mul]
  rw [←posterior_sum]
  unfold posterior numerator
  congr 1
  apply sum_congr rfl
  intro ρ hρ
  dsimp only
  rw [request_of_history t ρ σ (mem_filter.mp hρ).2]
  simp

/-- The entire physical-drift budget is the expectation of the attained optimum,
not a separate assumed bound or a policy-dependent comparator. -/
lemma expected_moveCost (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y)) :
    (∑ t : Fin H,∑ σ,law.val σ*(∑ y,nu s law t σ y*dist y (σ t)))=
      ∑ σ,law.val σ*optimalCost s (List.ofFn σ) := by
  simp_rw [conditional_moveCost]
  change (∑ t : Fin H,RankTracking.avg law.val
    (posterior law.val (requestHistory (t.val+1))
      (fun ρ => dist (hidden s ρ t.val (mover s ρ t)) (ρ t))))=_
  simp_rw [posterior_avg law.property.1]
  unfold RankTracking.avg
  rw [sum_comm]
  apply sum_congr rfl
  intro σ _
  rw [←mul_sum]
  congr 1
  simp_rw [←hidden_movement]
  exact hidden_total_cost s σ

end KServer.FiniteExperiment

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Potential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deterministic heavy-center schedule and its clipped distance profile.
Random heavy radii do not affect this schedule. -/
noncomputable section
open scoped BigOperators Classical
open Finset Set
namespace KServer.HeavyCenters

lemma ramp_bounds (u : ℝ) : ramp u ∈ Set.Icc 0 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩
lemma ramp_zero {u : ℝ} (hu : u ≤ 3) : ramp u=0 := by
  simp [ramp,max_eq_left (by linarith : u-3 ≤ 0)]
lemma ramp_one {u : ℝ} (hu : 4 ≤ u) : ramp u=1 := by
  exact min_eq_left ((by linarith : 1 ≤ u-3).trans (le_max_right _ _))
lemma ramp_lipschitz (u v : ℝ) : |ramp u-ramp v| ≤ |u-v| := by
  rw [abs_le]
  constructor <;> unfold ramp <;>
    simp only [min_def,max_def] <;> split_ifs <;>
    have h1 := le_abs_self (u-v) <;> have h2 := neg_le_abs (u-v) <;> linarith

variable {Y : Type*} [MetricSpace Y]

lemma profile_nonneg (r : ℝ) (C : Finset Y) (y : Y) : 0 ≤ profile r C y := by
  apply le_min'
  intro z hz
  rcases mem_insert.mp hz with rfl | hz
  · norm_num
  · obtain ⟨a,_,rfl⟩ := mem_image.mp hz
    exact (ramp_bounds _).1

lemma profile_le_one (r : ℝ) (C : Finset Y) (y : Y) : profile r C y ≤ 1 :=
  min'_le _ _ (mem_insert_self _ _)
lemma profile_bounds (r : ℝ) (C : Finset Y) (y : Y) : profile r C y ∈ Set.Icc 0 1 :=
  ⟨profile_nonneg _ _ _,profile_le_one _ _ _⟩
lemma profile_le (r : ℝ) {C : Finset Y} {a : Y} (ha : a∈C) (y : Y) :
    profile r C y ≤ ramp (dist a y/r) :=
  min'_le _ _ (mem_insert_of_mem (mem_image.mpr ⟨a,ha,rfl⟩))
lemma le_profile (r : ℝ) (C : Finset Y) (y : Y) {u : ℝ} (hu : u ≤ 1)
    (h : ∀ a∈C,u ≤ ramp (dist a y/r)) : u ≤ profile r C y := by
  apply le_min'
  intro z hz
  rcases mem_insert.mp hz with rfl | hz
  · exact hu
  · obtain ⟨a,ha,rfl⟩ := mem_image.mp hz
    exact h a ha
lemma profile_eq_one {r : ℝ} (hr : 0 < r) {C : Finset Y} {y : Y}
    (h : ∀ a∈C,4*r ≤ dist a y) : profile r C y=1 := by
  apply le_antisymm (profile_le_one _ _ _)
  apply le_profile _ _ _ le_rfl
  intro a ha
  rw [ramp_one ((le_div_iff₀ hr).mpr (h a ha))]
lemma profile_eq_zero {r : ℝ} (hr : 0 < r) {C : Finset Y} {a y : Y}
    (ha : a∈C) (hay : dist a y ≤ 3*r) : profile r C y=0 := by
  apply le_antisymm _ (profile_nonneg _ _ _)
  exact (profile_le r ha y).trans_eq (ramp_zero ((div_le_iff₀ hr).mpr hay))

lemma profile_gt_witness {r : ℝ} {C : Finset Y} {y : Y} {u : ℝ}
    (hu : u ≤ 1) (h : profile r C y<u) :
    ∃ a∈C,ramp (dist a y/r)<u := by
  by_contra hn
  push Not at hn
  exact (not_lt_of_ge (le_profile r C y hu hn)) h

lemma profile_lipschitz {r : ℝ} (hr : 0 < r) (C : Finset Y) (y z : Y) :
    |profile r C y-profile r C z| ≤ dist y z/r := by
  have hdir (y z : Y) : profile r C y-profile r C z ≤ dist y z/r := by
    suffices profile r C y-dist y z/r ≤ profile r C z by linarith
    apply le_profile r C z
    · linarith [profile_le_one r C y,div_nonneg (dist_nonneg (x := y) (y := z)) hr.le]
    · intro a ha
      have hl := ramp_lipschitz (dist a y/r) (dist a z/r)
      have hm : |dist a y-dist a z| ≤ dist y z := by
        simpa only [dist_comm a] using abs_dist_sub_le y z a
      rw [←sub_div,abs_div,abs_of_pos hr] at hl
      have hb := hl.trans (div_le_div_of_nonneg_right hm hr.le)
      have hc := (le_abs_self (ramp (dist a y/r)-ramp (dist a z/r))).trans hb
      linarith [profile_le r ha y]
  rw [abs_sub_le_iff]
  exact ⟨hdir y z,by simpa only [dist_comm z y] using hdir z y⟩

lemma new_profile_zero {r : ℝ} (hr : 0 < r) (C : Finset Y) {x y : Y}
    (hy : dist x y ≤ 3*r) : profile r (replace r C x) y=0 :=
  profile_eq_zero hr (mem_insert_self _ _) hy

lemma profile_increase_support {r : ℝ} (hr : 0 < r) (C : Finset Y) (x y : Y)
    (h : profile r C y < profile r (replace r C x) y) :
    3*r<dist x y ∧ dist x y ≤ 104*r := by
  constructor
  · by_contra hh
    rw [new_profile_zero hr C (le_of_not_gt hh)] at h
    exact (not_lt_of_ge (profile_nonneg _ _ _)) h
  · obtain ⟨a,ha,hai⟩ := profile_gt_witness (profile_le_one r (replace r C x) y) h
    have har : dist a y<4*r := by
      by_contra hn
      rw [ramp_one ((le_div_iff₀ hr).mpr (le_of_not_gt hn))] at hai
      linarith [profile_le_one r (replace r C x) y]
    have han : a∉replace r C x := by
      intro he
      exact (not_lt_of_ge (profile_le r he y)) hai
    have had : dist a x ≤ 100*r := by
      by_contra hd
      exact han (mem_insert_of_mem (mem_filter.mpr ⟨ha,lt_of_not_ge hd⟩))
    have ht := dist_triangle x a y
    rw [dist_comm x a] at ht
    linarith

lemma near_profile_edit {r : ℝ} (hr : 0 < r) {C : Finset Y} {x s : Y}
    (hfar : ∀ a∈C,8*r<dist a x) (hs : dist s x < r/4) :
    profile r C s=1 ∧ profile r (replace r C x) s=0 := by
  constructor
  · apply profile_eq_one hr
    intro a ha
    have ht := dist_triangle a s x
    have hf := hfar a ha
    linarith
  · apply new_profile_zero hr
    rw [dist_comm]
    linarith

end KServer.HeavyCenters

end


/- The finite variational pilot potential. -/

noncomputable section
open scoped BigOperators Classical
open Finset Set
namespace KServer.Pilot

lemma b_nonneg (T : Template) (v : ℝ) : 0 ≤ b T v := le_max_left _ _
lemma b_le_one (T : Template) (v : ℝ) : b T v ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)
lemma b_eq_one {T : Template} {v : ℝ} (hv : v ≤ T.σ) : b T v = 1 := by
  have : v / T.σ ≤ 1 := (div_le_one T.σ_pos).mpr hv
  simp [b, min_eq_left (show 1 ≤ 2 - v / T.σ by linarith)]
lemma b_eq_zero {T : Template} {v : ℝ} (hv : 2 * T.σ ≤ v) : b T v = 0 := by
  have : 2 ≤ v / T.σ := (le_div_iff₀ T.σ_pos).mpr hv
  exact max_eq_left (le_trans (min_le_right _ _) (by linarith))
lemma b_pos_iff {T : Template} {v : ℝ} : 0 < b T v ↔ v < 2 * T.σ := by
  simp only [b, lt_max_iff, lt_self_iff_false, false_or, lt_min_iff]
  constructor
  · intro h
    have : v / T.σ < 2 := by linarith [h.2]
    exact (div_lt_iff₀ T.σ_pos).mp this
  · intro h
    have : v / T.σ < 2 := (div_lt_iff₀ T.σ_pos).mpr h
    exact ⟨by norm_num, by linarith⟩
lemma a_nonneg (T : Template) (v : ℝ) : 0 ≤ a T v := by
  unfold a
  split_ifs with h h'
  · exact le_min (div_nonneg (sq_nonneg _) (sq_nonneg _)) zero_le_one
  · have : v / T.R ≤ 2 := (div_le_iff₀ (by linarith [T.R_ge])).mpr h'
    linarith
  · rfl
lemma a_le_one (T : Template) (v : ℝ) : a T v ≤ 1 := by
  unfold a
  split_ifs with h h'
  · exact min_le_right _ _
  · have : 1 ≤ v / T.R := (le_div_iff₀ (by linarith [T.R_ge])).mpr (by linarith)
    linarith
  · norm_num
lemma a_eq_zero {T : Template} {v : ℝ} (hv : 2 * T.R ≤ v) : a T v = 0 := by
  have hR : 0 < T.R := by linarith [T.R_ge]
  unfold a
  split_ifs with h h'
  · linarith
  · have he : v = 2 * T.R := le_antisymm h' hv
    rw [he]; field_simp; ring
  · rfl
lemma G_eq_one {T : Template} {v : ℝ} (hv : 20 * T.R ≤ v) : G T v = 1 := by
  have : 2 ≤ v / (10 * T.R) := (le_div_iff₀ (by linarith [T.R_ge])).mpr (by linarith)
  simp [G, min_eq_left (show 1 ≤ v / (10 * T.R) - 1 by linarith)]

variable {Y : Type*} [Fintype Y] [MetricSpace Y]

lemma minimizer_spec (T : Template) (r : ℝ) (μ g : Y → ℝ) :
    Feasible T r (minimizer T r μ g) ∧
    IsMinOn (objective T r μ g) {z | Feasible T r z} (minimizer T r μ g) :=
  (exists_minimizer T r μ g).choose_spec

lemma potential_le {T : Template} {r : ℝ} {μ g z : Y → ℝ}
    (hz : Feasible T r z) : potential T r μ g ≤ objective T r μ g z :=
  (minimizer_spec T r μ g).2 hz

lemma weighted_bump_le_capacity {T : Template} {r : ℝ} {z f : Y → ℝ} {p : Y}
    (hz : Feasible T r z) (hf0 : ∀ s, 0 ≤ f s) (hf1 : ∀ s, f s ≤ 1)
    (hG : ∀ s, 0 < f s → G T (dist s p / r) = 0) : ∑ s, z s * f s ≤ 1 := by
  apply le_trans (sum_le_sum fun s _ => ?_) (hz.2.1 p)
  by_cases hs : 0 < f s
  · rw [hG s hs, sub_zero, max_eq_left (hz.1 s)]
    exact mul_le_of_le_one_right (hz.1 s) (hf1 s)
  · have he : f s = 0 := le_antisymm (le_of_not_gt hs) (hf0 s)
    rw [he, mul_zero]
    exact le_max_right _ _

lemma sum_b_le_one {T : Template} {r : ℝ} {z : Y → ℝ} (hz : Feasible T r z) (p : Y) :
    ∑ s, z s * b T (dist s p / r) ≤ 1 := by
  apply weighted_bump_le_capacity hz (fun _ => b_nonneg _ _) (fun _ => b_le_one _ _)
  intro s hs
  apply G_eq_zero
  exact (b_pos_iff.mp hs).le.trans (by linarith only [T.σ_le, T.R_ge])

lemma sum_a_le_one {T : Template} {r : ℝ} {z : Y → ℝ} (hz : Feasible T r z) (p : Y) :
    ∑ s, z s * a T (dist s p / r) ≤ 1 := by
  apply weighted_bump_le_capacity hz (fun _ => a_nonneg _ _) (fun _ => a_le_one _ _)
  intro s hs
  apply G_eq_zero
  have hv : dist s p / r < 2 * T.R := by
    by_contra hv
    rw [a_eq_zero (le_of_not_gt hv)] at hs
    exact lt_irrefl _ hs
  exact hv.le.trans (by linarith only [T.R_ge])

lemma integrand_bounds {T : Template} {r : ℝ} {g z : Y → ℝ}
    (hz : Feasible T r z) (hg : ∀ s, g s ∈ Set.Icc 0 1) (p : Y) :
    integrand T r g z p ∈ Set.Icc 0 514 := by
  have hb0 : 0 ≤ ∑ s, z s * b T (dist s p / r) :=
    sum_nonneg fun s _ => mul_nonneg (hz.1 s) (b_nonneg _ _)
  have hb1 := sum_b_le_one hz p
  have ha0 : 0 ≤ ∑ s, z s * (1 + g s) * a T (dist s p / r) := by
    exact sum_nonneg fun s _ => mul_nonneg (mul_nonneg (hz.1 s) (by linarith [(hg s).1])) (a_nonneg _ _)
  have ha1 : (∑ s, z s * (1 + g s) * a T (dist s p / r)) ≤ 2 := by
    calc _ ≤ ∑ s, 2 * (z s * a T (dist s p / r)) := by
           apply sum_le_sum
           intro s _
           have := mul_le_mul_of_nonneg_left (hg s).2 (mul_nonneg (hz.1 s) (a_nonneg T (dist s p / r)))
           nlinarith
         _ = 2 * ∑ s, z s * a T (dist s p / r) := (mul_sum _ _ _).symm
         _ ≤ 2 := by linarith [sum_a_le_one hz p]
  have hres : (1 + g p) * (1 - ∑ s, z s * b T (dist s p / r)) ∈ Set.Icc 0 2 := by
    constructor
    · exact mul_nonneg (by linarith [(hg p).1]) (by linarith)
    · nlinarith [(hg p).1, (hg p).2, mul_nonneg (by linarith [(hg p).1] : 0 ≤ 1 + g p) hb0]
  unfold integrand
  constructor <;> linarith [hres.1, hres.2]

lemma potential_bounds {T : Template} {r : ℝ} {μ g : Y → ℝ}
    (hr : 0 ≤ r) (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc 0 1) :
    potential T r μ g ∈ Set.Icc 0 (2 * r * ∑ p, μ p) := by
  constructor
  · exact mul_nonneg hr (sum_nonneg fun p _ => mul_nonneg (hμ p)
      (integrand_bounds (minimizer_spec T r μ g).1 hg p).1)
  · apply le_trans (potential_le (feasible_zero T r))
    unfold objective integrand
    simp only [Pi.zero_apply, zero_mul, sum_const_zero, sub_zero, mul_zero, add_zero, mul_one]
    calc _ ≤ r * ∑ p, μ p * 2 := by
           apply mul_le_mul_of_nonneg_left _ hr
           apply sum_le_sum
           intro p _
           exact mul_le_mul_of_nonneg_left (by linarith [(hg p).2]) (hμ p)
         _ = _ := by rw [← sum_mul]; ring

lemma positive_b_support_disjoint {T : Template} {r : ℝ} {z : Y → ℝ}
    (hr : 0 < r) (hz : Feasible T r z) {s t p : Y}
    (hs : 0 < z s) (ht : 0 < z t) (hb : 0 < b T (dist s p / r))
    (hb' : 0 < b T (dist t p / r)) : s = t := by
  by_contra hst
  have hs' : dist s p < 2 * T.σ * r := (div_lt_iff₀ hr).mp (b_pos_iff.mp hb)
  have ht' : dist t p < 2 * T.σ * r := (div_lt_iff₀ hr).mp (b_pos_iff.mp hb')
  have hd : dist s t < 5 * T.σ * r := by
    have := dist_triangle s p t
    rw [dist_comm p t] at this
    nlinarith [mul_pos T.σ_pos hr]
  have he := hz.2.2 s t hst hd
  have := mul_pos hs ht
  linarith

lemma feasible_downward {T : Template} {r : ℝ} {z w : Y → ℝ}
    (hz : Feasible T r z) (hw : ∀ s, 0 ≤ w s) (hle : ∀ s, w s ≤ z s) :
    Feasible T r w := by
  refine ⟨hw, fun p => ?_, fun s t hst hd => ?_⟩
  · exact (sum_le_sum fun s _ => max_le_max (sub_le_sub_right (hle s) _) le_rfl).trans (hz.2.1 p)
  · have hm := mul_le_mul (hle s) (hle t) (hw t) (hz.1 s)
    rw [hz.2.2 s t hst hd] at hm
    exact le_antisymm hm (mul_nonneg (hw s) (hw t))

lemma objective_linear (T : Template) (r : ℝ) (μ g z : Y → ℝ) :
    objective T r μ g z = r * ((∑ p, μ p * (1 + g p)) + ∑ s, z s * coefficient T r μ g s) := by
  have hi : ∀ p, integrand T r g z p = (1 + g p) +
      ∑ s, z s * (256 * (1 + g s) * a T (dist s p / r) - (1 + g p) * b T (dist s p / r)) := by
    intro p
    calc _ = (1 + g p) + (256 * (∑ s, z s * (1 + g s) * a T (dist s p / r)) -
        (1 + g p) * ∑ s, z s * b T (dist s p / r)) := by unfold integrand; ring
      _ = _ := by
        rw [mul_sum, mul_sum, ← sum_sub_distrib]
        congr 1
        apply sum_congr rfl
        intro s _
        ring
  unfold objective
  congr 1
  calc
    _ = ∑ p, (μ p * (1 + g p) + ∑ s, μ p * (z s *
        (256 * (1 + g s) * a T (dist s p / r) - (1 + g p) * b T (dist s p / r)))) := by
      apply sum_congr rfl
      intro p _
      rw [hi, mul_add, mul_sum]
    _ = _ := by
      rw [sum_add_distrib, sum_comm]
      congr 1
      unfold coefficient
      simp only [mul_sum]
      apply sum_congr rfl
      intro s _
      apply sum_congr rfl
      intro p _
      ring

lemma minimizer_zero_of_coefficient_pos {T : Template} {r : ℝ} {μ g z : Y → ℝ}
    (hr : 0 < r) (hz : Feasible T r z)
    (hmin : IsMinOn (objective T r μ g) {w | Feasible T r w} z)
    {s : Y} (hc : 0 < coefficient T r μ g s) : z s = 0 := by
  let w := Function.update z s 0
  have hw : Feasible T r w := by
    apply feasible_downward hz
    · intro t; by_cases ht : t = s <;> simp [w, ht, hz.1]
    · intro t; by_cases ht : t = s <;> simp [w, ht, hz.1]
  have hs := hmin hw
  change objective T r μ g z ≤ objective T r μ g w at hs
  rw [objective_linear, objective_linear] at hs
  have he : (∑ t, w t * coefficient T r μ g t) =
      (∑ t, z t * coefficient T r μ g t) - z s * coefficient T r μ g s := by
    classical
    rw [← sum_erase_add _ _ (mem_univ s), ← sum_erase_add _ _ (mem_univ s)]
    have hsum : (∑ t ∈ univ.erase s, w t * coefficient T r μ g t) =
        ∑ t ∈ univ.erase s, z t * coefficient T r μ g t := by
      apply sum_congr rfl
      intro t ht
      simp [w, ne_of_mem_erase ht]
    rw [hsum]
    simp [w]
  rw [he] at hs
  have : r * z s * coefficient T r μ g s ≤ 0 := by nlinarith
  have : z s ≤ 0 := by nlinarith [mul_pos hr hc]
  exact le_antisymm this (hz.1 s)

lemma a_middle_lower {T : Template} {v : ℝ}
    (hv : 15 * T.σ / 64 ≤ v) (hR : v ≤ T.R) : 225 / 4096 ≤ a T v := by
  rw [a, ite_eq_left hR]
  apply le_min _ (by norm_num)
  apply (le_div_iff₀ (sq_pos_of_pos T.σ_pos)).mpr
  have hv0 : 0 ≤ v := by linarith [T.σ_pos]
  nlinarith [sq_nonneg (v - 15 * T.σ / 64), mul_nonneg
    (sub_nonneg.mpr hv) (show 0 ≤ v + 15 * T.σ / 64 by linarith [T.σ_pos])]

lemma coefficient_middle_pos {T : Template} {r γ δ : ℝ} {μ g : Y → ℝ} {x s : Y}
    (hr : 0 < r) (hγ : γ ≤ T.σ / 64) (hδ : δ ≤ 1 / 4112)
    (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc 0 1)
    (hslo : T.σ * r / 4 ≤ dist s x) (hshi : dist s x ≤ T.R * r / 2)
    (hM : 0 < mass μ (ball x (γ * r)))
    (hconc : mass μ (ball x (100 * T.R * r)) ≤ (1 + δ) * mass μ (ball x (γ * r))) :
    0 < coefficient T r μ g s := by
  have ha : ∀ p ∈ ball x (γ * r), 225 / 4096 ≤ a T (dist s p / r) := by
    intro p hp
    have hp' : dist x p ≤ γ * r := (mem_filter.mp hp).2
    have hγr : γ * r ≤ T.σ * r / 64 := by nlinarith [mul_le_mul_of_nonneg_right hγ hr.le]
    apply a_middle_lower
    · apply (le_div_iff₀ hr).mpr
      have ht := dist_triangle s p x
      rw [dist_comm p x] at ht
      linarith
    · apply (div_le_iff₀ hr).mpr
      have ht := dist_triangle s x p
      have hσr : T.σ * r ≤ r := by nlinarith [T.σ_le]
      have hRr : 256 * r ≤ T.R * r := mul_le_mul_of_nonneg_right T.R_ge hr.le
      linarith
  have hb : ∀ p, b T (dist s p / r) ≠ 0 → p ∈ ball x (100 * T.R * r) := by
    intro p hp
    have hbpos : 0 < b T (dist s p / r) := lt_of_le_of_ne (b_nonneg _ _) (Ne.symm hp)
    have hd := (div_lt_iff₀ hr).mp (b_pos_iff.mp hbpos)
    have ht := dist_triangle x s p
    rw [dist_comm x s] at ht
    have hσr : T.σ * r ≤ r := by nlinarith [T.σ_le]
    have hRr : 256 * r ≤ T.R * r := mul_le_mul_of_nonneg_right T.R_ge hr.le
    apply mem_filter.mpr ⟨mem_univ _, ?_⟩
    linarith
  have hapos : 225 / 16 * mass μ (ball x (γ * r)) ≤
      ∑ p, μ p * (256 * (1 + g s) * a T (dist s p / r)) := by
    calc _ ≤ ∑ p ∈ ball x (γ * r), μ p * (256 * (1 + g s) * a T (dist s p / r)) := by
           unfold mass
           rw [mul_sum]
           apply sum_le_sum
           intro p hp
           have h := ha p hp
           have had := mul_nonneg (hg s).1 (a_nonneg T (dist s p / r))
           have hh : 225 / 16 ≤ 256 * (1 + g s) * a T (dist s p / r) := by nlinarith
           nlinarith [mul_le_mul_of_nonneg_left hh (hμ p)]
         _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun p _ _ =>
           mul_nonneg (hμ p) (mul_nonneg (by linarith [(hg s).1]) (a_nonneg _ _))
  have hbneg : (∑ p, μ p * ((1 + g p) * b T (dist s p / r))) ≤
      2 * mass μ (ball x (100 * T.R * r)) := by
    calc _ = ∑ p ∈ ball x (100 * T.R * r), μ p * ((1 + g p) * b T (dist s p / r)) := by
           apply (sum_subset (subset_univ _) ?_).symm
           intro p _ hnot
           have hz : b T (dist s p / r) = 0 := by by_contra hn; exact hnot (hb p hn)
           simp [hz]
         _ ≤ _ := by
           unfold mass
           rw [mul_sum]
           apply sum_le_sum
           intro p _
           have hg0 := (hg p).1
           have hg1 := (hg p).2
           have hb0 := b_nonneg T (dist s p / r)
           have hb1 := b_le_one T (dist s p / r)
           have hh : (1 + g p) * b T (dist s p / r) ≤ 2 := by
             nlinarith [mul_nonneg hg0 (sub_nonneg.mpr hb1)]
           nlinarith [mul_le_mul_of_nonneg_left hh (hμ p)]
  unfold coefficient
  simp only [mul_sub, sum_sub_distrib]
  have htwo := mul_le_mul_of_nonneg_left hconc (show (0 : ℝ) ≤ 2 by norm_num)
  have hdel := mul_le_mul_of_nonneg_right hδ hM.le
  nlinarith

lemma no_middle_site {T : Template} {r γ δ : ℝ} {μ g z : Y → ℝ} {x s : Y}
    (hr : 0 < r) (hγ : γ ≤ T.σ / 64) (hδ : δ ≤ 1 / 4112)
    (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc 0 1)
    (hz : Feasible T r z) (hmin : IsMinOn (objective T r μ g) {w | Feasible T r w} z)
    (hslo : T.σ * r / 4 ≤ dist s x) (hshi : dist s x ≤ T.R * r / 2)
    (hM : 0 < mass μ (ball x (γ * r)))
    (hconc : mass μ (ball x (100 * T.R * r)) ≤ (1 + δ) * mass μ (ball x (γ * r))) : z s = 0 :=
  minimizer_zero_of_coefficient_pos hr hz hmin
    (coefficient_middle_pos hr hγ hδ hμ hg hslo hshi hM hconc)

omit [Fintype Y] in
lemma insertUnit_self (T : Template) (r : ℝ) (z : Y → ℝ) (x : Y) :
    insertUnit T r z x x = 1 := by simp [insertUnit]

lemma insertUnit_le {T : Template} {r : ℝ} {z : Y → ℝ} {x s : Y}
    (hz : Feasible T r z) (hs : s ≠ x) : insertUnit T r z x s ≤ z s := by
  simp only [insertUnit, ite_eq_right hs]
  split_ifs <;> simp [hz.1]

lemma G_lt_one {T : Template} {v : ℝ} (hv : G T v < 1) : v < 20 * T.R := by
  by_contra h
  rw [G_eq_one (le_of_not_gt h)] at hv
  exact lt_irrefl _ hv

lemma insertUnit_feasible {T : Template} {r : ℝ} {z : Y → ℝ}
    (hr : 0 < r) (hz : Feasible T r z) (x : Y) : Feasible T r (insertUnit T r z x) := by
  have hnon : ∀ s, 0 ≤ insertUnit T r z x s := by
    intro s
    unfold insertUnit
    split_ifs <;> simp [hz.1]
  refine ⟨hnon, fun p => ?_, fun s t hst hd => ?_⟩
  · by_cases hp : 0 < 1 - G T (dist x p / r)
    · have hxp : dist x p < 20 * T.R * r :=
        (div_lt_iff₀ hr).mp (G_lt_one (by linarith))
      have he : ∀ s ≠ x, max (insertUnit T r z x s - G T (dist s p / r)) 0 = 0 := by
        intro s hs
        by_cases hclear : dist x s < 50 * T.R * r
        · simp only [insertUnit, ite_eq_right hs, ite_eq_left hclear]
          exact max_eq_right (by linarith [G_nonneg T (dist s p / r)])
        · have hsp : 20 * T.R ≤ dist s p / r := by
            apply (le_div_iff₀ hr).mpr
            have ht := dist_triangle x p s
            rw [dist_comm p s] at ht
            have hRr : 0 < T.R * r := mul_pos (by linarith [T.R_ge]) hr
            linarith
          rw [G_eq_one hsp]
          exact max_eq_right (by linarith [insertUnit_le hz hs, coordinate_le_one hz s])
      rw [sum_eq_single x]
      · rw [insertUnit_self]
        exact max_le (by linarith [G_nonneg T (dist x p / r)]) (by norm_num)
      · intro s _ hs; exact he s hs
      · simp
    · apply le_trans (sum_le_sum fun s _ => ?_) (hz.2.1 p)
      by_cases hs : s = x
      · subst s
        rw [insertUnit_self, max_eq_right (le_of_not_gt hp)]
        exact le_max_right _ _
      · exact max_le_max (sub_le_sub_right (insertUnit_le hz hs) _) le_rfl
  · by_cases hs : s = x
    · subst s
      have ht : dist x t < 50 * T.R * r := by
        have hσr : T.σ * r ≤ r := mul_le_of_le_one_left hr.le T.σ_le
        have hRr : 256 * r ≤ T.R * r := mul_le_mul_of_nonneg_right T.R_ge hr.le
        linarith
      simp [insertUnit, Ne.symm hst, ht]
    · by_cases ht : t = x
      · subst t
        have hs' : dist x s < 50 * T.R * r := by
          have hσr : T.σ * r ≤ r := mul_le_of_le_one_left hr.le T.σ_le
          have hRr : 256 * r ≤ T.R * r := mul_le_mul_of_nonneg_right T.R_ge hr.le
          rw [dist_comm s x] at hd
          linarith
        simp [insertUnit, hs, hs']
      · have hm := mul_le_mul (insertUnit_le hz hs) (insertUnit_le hz ht) (hnon t) (hz.1 s)
        rw [hz.2.2 s t hst hd] at hm
        exact le_antisymm hm (mul_nonneg (hnon s) (hnon t))

/-- No changed bump reaches the complement of the outer ball. -/
lemma insertUnit_integrand_outside {T : Template} {r : ℝ} {g z : Y → ℝ} {x p : Y}
    (hr : 0 < r) (hp : 100 * T.R * r ≤ dist x p) :
    integrand T r g (insertUnit T r z x) p = integrand T r g z p := by
  have hab : ∀ s, insertUnit T r z x s ≠ z s →
      a T (dist s p / r) = 0 ∧ b T (dist s p / r) = 0 := by
    intro s hs
    have hxs : dist x s ≤ 50 * T.R * r := by
      by_cases he : s = x
      · subst s; simp; nlinarith [T.R_ge]
      · by_contra hn
        have hnc : ¬ dist x s < 50 * T.R * r := not_lt.mpr (le_of_not_ge hn)
        exact hs (by simp [insertUnit, he, hnc])
    have ht := dist_triangle x s p
    have hd : 2 * T.R ≤ dist s p / r := by
      apply (le_div_iff₀ hr).mpr
      have hRr : 0 ≤ T.R * r := mul_nonneg (by linarith [T.R_ge]) hr.le
      linarith
    exact ⟨a_eq_zero hd, b_eq_zero (by linarith [T.σ_le, T.R_ge])⟩
  unfold integrand
  congr 2
  · congr 1
    apply sum_congr rfl
    intro s _
    by_cases hs : insertUnit T r z x s = z s
    · rw [hs]
    · simp [(hab s hs).2]
  · apply sum_congr rfl
    intro s _
    by_cases hs : insertUnit T r z x s = z s
    · rw [hs]
    · simp [(hab s hs).1]

/-- Dimension-free repair inequality used in relocating a pilot site. -/
lemma sum_min_ge_min_sum {I : Type*} [Fintype I] {q : ℝ} {β : I → ℝ}
    (hq : 0 ≤ q) (hβ : ∀ i, 0 ≤ β i) :
    min q (∑ i, β i) ≤ ∑ i, min q (β i) := by
  by_cases h : ∃ i, q ≤ β i
  · obtain ⟨i, hi⟩ := h
    calc _ ≤ q := min_le_left _ _
         _ = min q (β i) := (min_eq_left hi).symm
         _ ≤ _ := single_le_sum (fun j _ => le_min hq (hβ j)) (mem_univ i)
  · push Not at h
    simp only [min_eq_right (le_of_lt (h _))]
    exact min_le_right _ _

lemma capacity_repair {I : Type*} [Fintype I] {q A A' : ℝ} {β : I → ℝ}
    (hq : 0 ≤ q) (hβ : ∀ i, 0 ≤ β i)
    (hcap : A + ∑ i, β i ≤ 1) (hA' : A' ≤ 1) (hchange : A' - A ≤ q) :
    A' + ∑ i, max (β i - q) 0 ≤ 1 := by
  have he : (∑ i, max (β i - q) 0) = (∑ i, β i) - ∑ i, min q (β i) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    by_cases h : q ≤ β i
    · rw [max_eq_left (by linarith), min_eq_left h]
    · rw [max_eq_right (by linarith), min_eq_right (le_of_not_ge h)]
      ring
  rw [he]
  have h := sum_min_ge_min_sum hq hβ
  by_cases hB : q ≤ ∑ i, β i
  · rw [min_eq_left hB] at h
    linarith
  · rw [min_eq_right (le_of_not_ge hB)] at h
    linarith

lemma innerMoment_le {μ : Y → ℝ} {x : Y} {γ r : ℝ}
    (hr : 0 < r) (hμ : ∀ p, 0 ≤ μ p) :
    innerMoment μ x γ r ≤ γ * mass μ (ball x (γ * r)) := by
  unfold innerMoment mass
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hd : dist x p / r ≤ γ := (div_le_iff₀ hr).mpr (mem_filter.mp hp).2
  nlinarith [mul_le_mul_of_nonneg_left hd (hμ p)]

lemma nearWeight_eq_b_sum {T : Template} {r γ : ℝ} {z : Y → ℝ} {x p : Y}
    (hr : 0 < r) (hγ : γ ≤ T.σ / 64)
    (hmiddle : ∀ s, T.σ * r / 4 ≤ dist s x → dist s x ≤ T.R * r / 2 → z s = 0)
    (hp : p ∈ ball x (γ * r)) : ∑ s, z s * b T (dist s p / r) = nearWeight T r z x := by
  have hp' : dist x p ≤ γ * r := (mem_filter.mp hp).2
  have hγr : γ * r ≤ T.σ * r / 64 := by nlinarith [mul_le_mul_of_nonneg_right hγ hr.le]
  have hσr : T.σ * r ≤ r := mul_le_of_le_one_left hr.le T.σ_le
  have hσr0 : 0 < T.σ * r := mul_pos T.σ_pos hr
  have hRr : 256 * r ≤ T.R * r := mul_le_mul_of_nonneg_right T.R_ge hr.le
  unfold nearWeight nearBall
  rw [sum_filter]
  apply sum_congr rfl
  intro s _
  by_cases hs : dist x s < T.σ * r / 4
  · simp only [hs, ite_true]
    have hb : b T (dist s p / r) = 1 := by
      apply b_eq_one
      apply (div_le_iff₀ hr).mpr
      have ht := dist_triangle s x p
      rw [dist_comm s x] at ht
      linarith
    simp [hb]
  · simp only [hs, ite_false]
    by_cases hm : dist s x ≤ T.R * r / 2
    · rw [hmiddle s (by simpa only [dist_comm s x] using le_of_not_gt hs) hm, zero_mul]
    · have hb : b T (dist s p / r) = 0 := by
        apply b_eq_zero
        apply (le_div_iff₀ hr).mpr
        have ht := dist_triangle s p x
        rw [dist_comm p x] at ht
        linarith
      simp [hb]

lemma old_integrand_inner_lower {T : Template} {r γ : ℝ} {g z : Y → ℝ} {x p : Y}
    (hr : 0 < r) (hγ : γ ≤ T.σ / 64) (hz : Feasible T r z)
    (hg : ∀ s, g s ∈ Set.Icc 0 1)
    (hmiddle : ∀ s, T.σ * r / 4 ≤ dist s x → dist s x ≤ T.R * r / 2 → z s = 0)
    (hp : p ∈ ball x (γ * r)) : 1 - nearWeight T r z x ≤ integrand T r g z p := by
  have hb := nearWeight_eq_b_sum hr hγ hmiddle hp
  have hZ : nearWeight T r z x ≤ 1 := by rw [← hb]; exact sum_b_le_one hz p
  have ha : 0 ≤ ∑ s, z s * (1 + g s) * a T (dist s p / r) :=
    sum_nonneg fun s _ => mul_nonneg (mul_nonneg (hz.1 s) (by linarith [(hg s).1])) (a_nonneg _ _)
  unfold integrand
  rw [hb]
  nlinarith [mul_nonneg (hg p).1 (sub_nonneg.mpr hZ)]

lemma insertUnit_integrand_inner {T : Template} {r γ : ℝ} {g z : Y → ℝ} {x p : Y}
    (hr : 0 < r) (hγ : γ ≤ T.σ / 64) (hg : ∀ s, g s ∈ Set.Icc 0 1)
    (hp : p ∈ ball x (γ * r)) :
    integrand T r g (insertUnit T r z x) p ≤ 512 * γ / T.σ ^ 2 * (dist x p / r) := by
  have hp' : dist x p ≤ γ * r := (mem_filter.mp hp).2
  have hv0 : 0 ≤ dist x p / r := div_nonneg dist_nonneg hr.le
  have hvγ : dist x p / r ≤ γ := (div_le_iff₀ hr).mpr hp'
  have hσr : T.σ * r ≤ r := mul_le_of_le_one_left hr.le T.σ_le
  have hRr : 256 * r ≤ T.R * r := mul_le_mul_of_nonneg_right T.R_ge hr.le
  have hγr : γ * r ≤ T.σ * r / 64 := by nlinarith [mul_le_mul_of_nonneg_right hγ hr.le]
  have hb : b T (dist x p / r) = 1 := b_eq_one (by linarith [T.σ_pos])
  have hz : ∀ s ≠ x, insertUnit T r z x s * b T (dist s p / r) = 0 ∧
      insertUnit T r z x s * (1 + g s) * a T (dist s p / r) = 0 := by
    intro s hs
    by_cases hc : dist x s < 50 * T.R * r
    · simp [insertUnit, hs, hc]
    · have hd : 2 * T.R ≤ dist s p / r := by
        apply (le_div_iff₀ hr).mpr
        have ht := dist_triangle x p s
        rw [dist_comm p s] at ht
        linarith
      simp [a_eq_zero hd, b_eq_zero (show 2 * T.σ ≤ dist s p / r by linarith [T.σ_le, T.R_ge])]
  have hbsum : (∑ s, insertUnit T r z x s * b T (dist s p / r)) = 1 := by
    rw [sum_eq_single x]
    · simp [insertUnit_self, hb]
    · intro s _ hs; exact (hz s hs).1
    · simp
  have hasum : (∑ s, insertUnit T r z x s * (1 + g s) * a T (dist s p / r)) =
      (1 + g x) * a T (dist x p / r) := by
    rw [sum_eq_single x]
    · simp [insertUnit_self]
    · intro s _ hs; exact (hz s hs).2
    · simp
  rw [integrand, hbsum, hasum]
  simp only [sub_self, mul_zero, zero_add]
  have ha : a T (dist x p / r) ≤ (dist x p / r) ^ 2 / T.σ ^ 2 := by
    rw [a, ite_eq_left (show dist x p / r ≤ T.R by linarith [T.R_ge, T.σ_le])]
    exact min_le_left _ _
  have hmul : 256 * ((1 + g x) * a T (dist x p / r)) ≤
      512 * ((dist x p / r) ^ 2 / T.σ ^ 2) := by
    have hg1 := (hg x).2
    have ha0 := a_nonneg T (dist x p / r)
    nlinarith [mul_nonneg (sub_nonneg.mpr hg1) ha0]
  apply hmul.trans
  have hprod : (dist x p / r) ^ 2 ≤ γ * (dist x p / r) := by nlinarith
  have hdpos : 0 < T.σ ^ 2 := sq_pos_of_pos T.σ_pos
  have := div_le_div_of_nonneg_right hprod hdpos.le
  calc _ ≤ 512 * (γ * (dist x p / r) / T.σ ^ 2) := mul_le_mul_of_nonneg_left this (by norm_num)
       _ = _ := by ring

lemma nearWeight_deficit {T : Template} {r γ : ℝ} {μ g z : Y → ℝ} {x : Y}
    (hr : 0 < r) (hγ : γ ≤ T.σ / 64) (hμ : ∀ p, 0 ≤ μ p)
    (hg : ∀ p, g p ∈ Set.Icc 0 1) (hz : Feasible T r z)
    (hmin : IsMinOn (objective T r μ g) {w | Feasible T r w} z)
    (hmiddle : ∀ s, T.σ * r / 4 ≤ dist s x → dist s x ≤ T.R * r / 2 → z s = 0) :
    (1 - nearWeight T r z x) * mass μ (ball x (γ * r)) ≤
      512 * γ / T.σ ^ 2 * innerMoment μ x γ r +
      514 * mass μ (ball x (100 * T.R * r) \ ball x (γ * r)) := by
  let w := insertUnit T r z x
  have hw := insertUnit_feasible hr hz x
  have hmin' := hmin hw
  change r * (∑ p, μ p * integrand T r g z p) ≤ r * (∑ p, μ p * integrand T r g w p) at hmin'
  have hcost : 0 ≤ ∑ p, μ p * (integrand T r g w p - integrand T r g z p) := by
    simp only [mul_sub, sum_sub_distrib]
    exact sub_nonneg.mpr ((mul_le_mul_iff_right₀ hr).mp hmin')
  have innerOuter : ball x (γ * r) ⊆ ball x (100 * T.R * r) := by
    intro p hp
    apply mem_filter.mpr ⟨mem_univ _, ?_⟩
    have hp' := (mem_filter.mp hp).2
    have hσr : T.σ * r ≤ r := mul_le_of_le_one_left hr.le T.σ_le
    have hRr : 256 * r ≤ T.R * r := mul_le_mul_of_nonneg_right T.R_ge hr.le
    have hγr : γ * r ≤ T.σ * r / 64 := by nlinarith [mul_le_mul_of_nonneg_right hγ hr.le]
    linarith
  have hpoint : ∀ p, μ p * (integrand T r g w p - integrand T r g z p) ≤
      (if p ∈ ball x (γ * r) then μ p * (512 * γ / T.σ ^ 2 * (dist x p / r) -
        (1 - nearWeight T r z x)) else 0) +
      (if p ∈ ball x (100 * T.R * r) \ ball x (γ * r) then 514 * μ p else 0) := by
    intro p
    by_cases hp : p ∈ ball x (γ * r)
    · have hout : p ∉ ball x (100 * T.R * r) \ ball x (γ * r) := by simp [hp]
      rw [ite_eq_left hp, ite_eq_right hout, add_zero]
      apply mul_le_mul_of_nonneg_left _ (hμ p)
      have hnew := insertUnit_integrand_inner hr hγ hg hp (z := z)
      have hold := old_integrand_inner_lower hr hγ hz hg hmiddle hp
      dsimp [w]
      linarith
    · rw [ite_eq_right hp, zero_add]
      by_cases hout : p ∈ ball x (100 * T.R * r)
      · rw [ite_eq_left (mem_sdiff.mpr ⟨hout, hp⟩)]
        have hnew := (integrand_bounds hw hg p).2
        have hold := (integrand_bounds hz hg p).1
        nlinarith [mul_le_mul_of_nonneg_left (show integrand T r g w p - integrand T r g z p ≤ 514 by linarith) (hμ p)]
      · rw [ite_eq_right (by simp [hout])]
        have he := insertUnit_integrand_outside (g := g) (z := z) hr
          (show 100 * T.R * r ≤ dist x p from le_of_lt (by simpa [ball] using hout))
        dsimp [w]
        rw [he, sub_self, mul_zero]
  have hsum := sum_le_sum fun p (_ : p ∈ (Finset.univ : Finset Y)) => hpoint p
  rw [sum_add_distrib] at hsum
  simp only [← sum_filter] at hsum
  have he1 : (∑ p ∈ univ.filter (fun p => p ∈ ball x (γ * r)),
      μ p * (512 * γ / T.σ ^ 2 * (dist x p / r) - (1 - nearWeight T r z x))) =
      512 * γ / T.σ ^ 2 * innerMoment μ x γ r -
        (1 - nearWeight T r z x) * mass μ (ball x (γ * r)) := by
    simp only [filter_mem_eq_inter, Finset.univ_inter, innerMoment, mass]
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro p _
    ring
  have he2 : (∑ p ∈ univ.filter (fun p => p ∈ ball x (100 * T.R * r) \ ball x (γ * r)), 514 * μ p) =
      514 * mass μ (ball x (100 * T.R * r) \ ball x (γ * r)) := by
    simp only [filter_mem_eq_inter, Finset.univ_inter, mass, mul_sum]
  rw [he1, he2] at hsum
  linarith

lemma nearWeight_large {T : Template} {r γ δ : ℝ} {μ g z : Y → ℝ} {x : Y}
    (hr : 0 < r) (hγ0 : 0 ≤ γ) (hγ : γ ≤ T.σ / 64) (hδ : δ ≤ 1 / 4112)
    (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc 0 1) (hz : Feasible T r z)
    (hmin : IsMinOn (objective T r μ g) {w | Feasible T r w} z)
    (hmiddle : ∀ s, T.σ * r / 4 ≤ dist s x → dist s x ≤ T.R * r / 2 → z s = 0)
    (hM : 0 < mass μ (ball x (γ * r)))
    (hconc : mass μ (ball x (100 * T.R * r) \ ball x (γ * r)) ≤
      δ * mass μ (ball x (γ * r))) : 3 / 4 ≤ nearWeight T r z x := by
  have hdef := nearWeight_deficit hr hγ hμ hg hz hmin hmiddle (x := x)
  have hmoment := innerMoment_le hr hμ (x := x) (γ := γ)
  have hc0 : 0 ≤ 512 * γ / T.σ ^ 2 := div_nonneg (by positivity) (sq_nonneg _)
  have hσ2 : 0 < T.σ ^ 2 := sq_pos_of_pos T.σ_pos
  have hc : (512 * γ / T.σ ^ 2) * γ ≤ 1 / 8 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hσ2).mpr
    have hprod := mul_le_mul hγ hγ hγ0 (show 0 ≤ T.σ / 64 by linarith [T.σ_pos])
    nlinarith
  have hterm : 512 * γ / T.σ ^ 2 * innerMoment μ x γ r ≤
      (1 / 8) * mass μ (ball x (γ * r)) := by
    calc _ ≤ (512 * γ / T.σ ^ 2) * (γ * mass μ (ball x (γ * r))) :=
           mul_le_mul_of_nonneg_left hmoment hc0
         _ = ((512 * γ / T.σ ^ 2) * γ) * mass μ (ball x (γ * r)) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right hc hM.le
  have hshell : 514 * mass μ (ball x (100 * T.R * r) \ ball x (γ * r)) ≤
      (1 / 8) * mass μ (ball x (γ * r)) := by
    have := mul_le_mul_of_nonneg_right hδ hM.le
    linarith
  nlinarith

lemma near_sites_unique {T : Template} {r : ℝ} {z : Y → ℝ} {x s t : Y}
    (hr : 0 < r) (hz : Feasible T r z)
    (hs : s ∈ nearBall x (T.σ * r / 4)) (ht : t ∈ nearBall x (T.σ * r / 4))
    (hspos : 0 < z s) (htpos : 0 < z t) : s = t := by
  by_contra hne
  have hs' := (mem_filter.mp hs).2
  have ht' := (mem_filter.mp ht).2
  have hd : dist s t < 5 * T.σ * r := by
    have htri := dist_triangle s x t
    rw [dist_comm s x] at htri
    nlinarith [mul_pos T.σ_pos hr]
  have he := hz.2.2 s t hne hd
  have := mul_pos hspos htpos
  linarith

lemma near_site_of_large {T : Template} {r : ℝ} {z : Y → ℝ} {x : Y}
    (hr : 0 < r) (hz : Feasible T r z) (hlarge : 3 / 4 ≤ nearWeight T r z x) :
    ∃ s, s ∈ nearBall x (T.σ * r / 4) ∧ 3 / 4 ≤ z s ∧
      nearWeight T r z x = z s ∧
      ∀ t, t ∈ nearBall x (T.σ * r / 4) → 0 < z t → t = s := by
  have hpos : ∃ s ∈ nearBall x (T.σ * r / 4), 0 < z s := by
    apply exists_lt_of_sum_lt (f := fun _ => (0 : ℝ)) (g := z)
    simpa only [sum_const_zero, nearWeight] using (show 0 < nearWeight T r z x by linarith)
  obtain ⟨s, hs, hspos⟩ := hpos
  have hun : ∀ t, t ∈ nearBall x (T.σ * r / 4) → 0 < z t → t = s :=
    fun t ht htpos => near_sites_unique hr hz ht hs htpos hspos
  have he : nearWeight T r z x = z s := by
    unfold nearWeight
    apply sum_eq_single s
    · intro t ht hne
      have hnot : ¬ 0 < z t := fun htpos => hne (hun t ht htpos)
      exact le_antisymm (le_of_not_gt hnot) (hz.1 t)
    · exact fun h => (h hs).elim
  exact ⟨s, hs, by rwa [← he], he, hun⟩

/-! Relocation at a concentrated request and local optimality,
including the dimension-free capacity repair competitor. -/
lemma clamp_abs {u v : ℝ} :
    |max 0 (min 1 u) - max 0 (min 1 v)| ≤ |u - v| := by
  calc _ ≤ max |(0 : ℝ) - 0| |min 1 u - min 1 v| := abs_max_sub_max_le_max _ _ _ _
       _ = |min 1 u - min 1 v| := by simp
       _ ≤ max |(1 : ℝ) - 1| |u - v| := abs_min_sub_min_le_max _ _ _ _
       _ = _ := by simp

lemma b_lipschitz (T : Template) (u v : ℝ) :
    |b T u - b T v| ≤ |u - v| / T.σ := by
  have h := clamp_abs (u := 2 - u / T.σ) (v := 2 - v / T.σ)
  have he : (2 - u / T.σ) - (2 - v / T.σ) = -(u - v) / T.σ := by ring
  simpa only [b, he, abs_div, abs_neg, abs_of_pos T.σ_pos] using h

lemma G_lipschitz (T : Template) (u v : ℝ) :
    |G T u - G T v| ≤ |u - v| / (10 * T.R) := by
  have h := clamp_abs (u := u / (10 * T.R) - 1) (v := v / (10 * T.R) - 1)
  have he : (u / (10 * T.R) - 1) - (v / (10 * T.R) - 1) = (u - v) / (10 * T.R) := by ring
  simpa only [G, he, abs_div, abs_of_pos (show 0 < 10 * T.R by linarith [T.R_ge])] using h

lemma a_min_rep {T : Template} {v : ℝ} (hv : 0 ≤ v) :
    a T v = min ((min 1 (v / T.σ)) ^ 2) (max 0 (2 - v / T.R)) := by
  have hR : 0 < T.R := by linarith [T.R_ge]
  have hσR : T.σ ≤ T.R := by linarith [T.σ_le, T.R_ge]
  have hvσ : 0 ≤ v / T.σ := div_nonneg hv T.σ_pos.le
  by_cases hvR : v ≤ T.R
  · have htail : 1 ≤ max 0 (2 - v / T.R) := le_trans (by
      have := (div_le_one hR).mpr hvR; linarith) (le_max_right _ _)
    have hc : (min 1 (v / T.σ)) ^ 2 ≤ 1 := by
      have hlo : 0 ≤ min 1 (v / T.σ) := le_min zero_le_one hvσ
      have hhi : min 1 (v / T.σ) ≤ 1 := min_le_left _ _
      nlinarith
    rw [min_eq_left (le_trans hc htail), a, ite_eq_left hvR]
    by_cases h : v / T.σ ≤ 1
    · have hs : v ^ 2 / T.σ ^ 2 ≤ 1 := by
        rw [← div_pow]; nlinarith
      rw [min_eq_left hs, min_eq_right h, div_pow]
    · have hs : 1 ≤ v ^ 2 / T.σ ^ 2 := by
        rw [← div_pow]; nlinarith
      simp [min_eq_right hs, min_eq_left (le_of_not_ge h)]
  · have hvσ1 : 1 ≤ v / T.σ := (le_div_iff₀ T.σ_pos).mpr (by linarith)
    rw [min_eq_left hvσ1, one_pow]
    have htail : max 0 (2 - v / T.R) ≤ 1 := by
      apply max_le zero_le_one
      have := (one_lt_div hR).mpr (lt_of_not_ge hvR)
      linarith
    rw [min_eq_right htail, a, ite_eq_right hvR]
    by_cases h : v ≤ 2 * T.R
    · rw [ite_eq_left h, max_eq_right]
      have := (div_le_iff₀ hR).mpr h
      linarith
    · rw [ite_eq_right h, max_eq_left]
      have : 2 ≤ v / T.R := (le_div_iff₀ hR).mpr (le_of_not_ge h)
      linarith

lemma a_lipschitz {T : Template} {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |a T u - a T v| ≤ 2 / T.σ * |u - v| := by
  have hR : 0 < T.R := by linarith [T.R_ge]
  have hu' : 0 ≤ min 1 (u / T.σ) := le_min zero_le_one (div_nonneg hu T.σ_pos.le)
  have hv' : 0 ≤ min 1 (v / T.σ) := le_min zero_le_one (div_nonneg hv T.σ_pos.le)
  have hs : |min 1 (u / T.σ) + min 1 (v / T.σ)| ≤ 2 := by
    rw [abs_of_nonneg (add_nonneg hu' hv')]
    linarith [min_le_left (1 : ℝ) (u / T.σ), min_le_left (1 : ℝ) (v / T.σ)]
  have hd : |min 1 (u / T.σ) - min 1 (v / T.σ)| ≤ |u-v| / T.σ := by
    have := abs_min_sub_min_le_max (1 : ℝ) (u/T.σ) 1 (v/T.σ)
    simp only [sub_self, abs_zero, max_eq_right (abs_nonneg (u / T.σ - v / T.σ))] at this
    simpa only [← sub_div, abs_div, abs_of_pos T.σ_pos] using this
  have hsq : |(min 1 (u / T.σ)) ^ 2 - (min 1 (v / T.σ)) ^ 2| ≤
      2 / T.σ * |u-v| := by
    have he : (min 1 (u / T.σ)) ^ 2 - (min 1 (v / T.σ)) ^ 2 =
        (min 1 (u / T.σ) - min 1 (v / T.σ)) *
        (min 1 (u / T.σ) + min 1 (v / T.σ)) := by ring
    rw [he, abs_mul]
    calc _ ≤ (|u-v| / T.σ) * 2 :=
           mul_le_mul hd hs (abs_nonneg _) (div_nonneg (abs_nonneg _) T.σ_pos.le)
         _ = _ := by ring
  have ht : |max 0 (2 - u / T.R) - max 0 (2 - v / T.R)| ≤ 2 / T.σ * |u-v| := by
    have hm := abs_max_sub_max_le_max (0 : ℝ) (2-u/T.R) 0 (2-v/T.R)
    have he : (2-u/T.R)-(2-v/T.R) = -(u-v)/T.R := by ring
    simp only [sub_self, abs_zero, he,
      abs_div, abs_neg, abs_of_pos hR] at hm
    rw [max_eq_right (div_nonneg (abs_nonneg _) hR.le)] at hm
    calc _ ≤ |u-v| / T.R := hm
         _ ≤ 2 / T.σ * |u-v| := by
           have hc : 1 / T.R ≤ 2 / T.σ := (div_le_div_iff₀ hR T.σ_pos).mpr (by
             linarith [T.σ_le, T.R_ge])
           have := mul_le_mul_of_nonneg_right hc (abs_nonneg (u-v))
           simpa only [one_div_mul_eq_div] using this
  rw [a_min_rep hu, a_min_rep hv]
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le hsq ht)

omit [Fintype Y] in
lemma scaled_dist_lipschitz {r : ℝ} (hr : 0 < r) (s x p : Y) :
    |dist s p / r - dist x p / r| ≤ dist s x / r := by
  rw [← sub_div, abs_div, abs_of_pos hr]
  exact div_le_div_of_nonneg_right (abs_dist_sub_le s x p) hr.le

omit [MetricSpace Y] in
lemma finite_sum_split (f : Y → ℝ) (s : Y) :
    (∑ i, f i) = f s + ∑ i, if i = s then 0 else f i := by
  calc _ = ∑ i, ((if i = s then f s else 0) + (if i = s then 0 else f i)) := by
         apply sum_congr rfl; intro i _; by_cases h : i = s <;> simp [h]
       _ = _ := by rw [sum_add_distrib]; simp

lemma clip_reduction {z G q : ℝ} (hG : 0 ≤ G) (hq : 0 ≤ q) :
    max (max (z-q) 0 - G) 0 = max (max (z-G) 0 - q) 0 := by
  by_cases hzq : z ≤ q
  · have h1 : max (z-q) 0 = 0 := max_eq_right (by linarith)
    have h2 : max (z-G) 0 ≤ q := max_le (by linarith) hq
    rw [h1, max_eq_right (by linarith), max_eq_right (by linarith)]
  · rw [max_eq_left (by linarith : 0 ≤ z-q)]
    by_cases hzG : z ≤ G
    · rw [max_eq_right (by linarith : z-G ≤ 0), max_eq_right (by linarith),
        max_eq_right (by linarith)]
    · rw [max_eq_left (by linarith : 0 ≤ z-G)]
      congr 1; ring

omit [Fintype Y] in
lemma relocate_at {T : Template} {r : ℝ} {z : Y → ℝ} {s x : Y} (hne : s ≠ x) :
    relocate T r z s x x = z s ∧ relocate T r z s x s = 0 := by
  simp [relocate, hne]

lemma relocate_le {T : Template} {r : ℝ} {z : Y → ℝ} {s x i : Y}
    (hr : 0 < r) (hz : Feasible T r z) (hi : i ≠ x) :
    0 ≤ relocate T r z s x i ∧ relocate T r z s x i ≤ z i := by
  have hq : 0 ≤ (dist s x/r)/(10*T.R) := div_nonneg (div_nonneg dist_nonneg hr.le)
    (by linarith [T.R_ge])
  unfold relocate
  rw [ite_eq_right hi]
  split_ifs <;> first | exact ⟨hz.1 i, le_rfl⟩ | exact ⟨le_rfl, hz.1 i⟩ |
    exact ⟨le_max_right _ _, max_le (by linarith) (hz.1 i)⟩

lemma near_site_others_vanish {T : Template} {r : ℝ} {z : Y → ℝ} {s x : Y}
    (hr : 0 < r) (hz : Feasible T r z) (hs : dist s x < T.σ*r/4)
    (hspos : 0 < z s)
    (hmiddle : ∀ i, T.σ*r/4 ≤ dist i x → dist i x ≤ T.R*r/2 → z i = 0) :
    ∀ i, i ≠ s → dist i x ≤ T.R*r/2 → z i = 0 := by
  intro i hi hix
  by_cases hl : T.σ*r/4 ≤ dist i x
  · exact hmiddle i hl hix
  · by_contra hzi
    have hipos : 0 < z i := lt_of_le_of_ne (hz.1 i) (Ne.symm hzi)
    have his : i = s := near_sites_unique (x := x) (s := i) (t := s) hr hz
      (by apply mem_filter.mpr; exact ⟨mem_univ _, by simpa [dist_comm] using lt_of_not_ge hl⟩)
      (by apply mem_filter.mpr; exact ⟨mem_univ _, by simpa [dist_comm] using hs⟩)
      hipos hspos
    exact hi his

lemma relocate_feasible {T : Template} {r : ℝ} {z : Y → ℝ} {s x : Y}
    (hr : 0 < r) (hz : Feasible T r z) (hne : s ≠ x)
    (hother : ∀ i, i ≠ s → dist i x ≤ T.R*r/2 → z i = 0) :
    Feasible T r (relocate T r z s x) := by
  have hRr : 0 < T.R*r := mul_pos (by linarith [T.R_ge]) hr
  have hzX : z x = 0 := hother x (Ne.symm hne) (by simp; positivity)
  have hq : 0 ≤ (dist s x/r)/(10*T.R) := div_nonneg (div_nonneg dist_nonneg hr.le)
    (by linarith [T.R_ge])
  have hn : ∀ i, 0 ≤ relocate T r z s x i := by
    intro i; by_cases hi : i=x
    · subst i; exact (relocate_at hne).1 ▸ hz.1 s
    · exact (relocate_le hr hz hi).1
  refine ⟨hn, ?_, ?_⟩
  · intro p
    let A := max (z s - G T (dist s p/r)) 0
    let A' := max (z s - G T (dist x p/r)) 0
    let β : Y → ℝ := fun i => if i=s then 0 else max (z i-G T (dist i p/r)) 0
    let β' : Y → ℝ := fun i => if i=x then 0 else max (relocate T r z s x i-G T (dist i p/r)) 0
    have hcap : A + ∑ i, β i ≤ 1 := by
      have hc := hz.2.1 p
      rw [finite_sum_split _ s] at hc
      exact hc
    have he : (∑ i, max (relocate T r z s x i - G T (dist i p/r)) 0) = A' + ∑ i, β' i := by
      rw [finite_sum_split _ x, (relocate_at hne).1]
    rw [he]
    have hβ : ∀ i, 0 ≤ β i := by intro i; exact ite_nonneg le_rfl (le_max_right _ _)
    have hb' : ∀ i, β' i ≤ β i := by
      intro i
      by_cases hix : i=x
      · subst i; exact le_trans (by simp [β']) (hβ x)
      · by_cases his : i=s
        · subst i; simp only [β', ite_eq_right hix, β, ite_eq_left rfl, (relocate_at hne).2]
          exact max_le (by linarith [G_nonneg T (dist s p/r)]) le_rfl
        · simp only [β', ite_eq_right hix, β, ite_eq_right his]
          exact max_le_max (sub_le_sub_right (relocate_le hr hz hix).2 _) le_rfl
    by_cases hAA : A' ≤ A
    · exact (add_le_add hAA (sum_le_sum (fun i _ => hb' i))).trans hcap
    · have hAp : 0 < A' := lt_of_le_of_lt (le_max_right _ _) (lt_of_not_ge hAA)
      have hxp : dist x p < 20*T.R*r := by
        by_contra hh
        have hG : G T (dist x p/r) = 1 := G_eq_one ((le_div_iff₀ hr).mpr (le_of_not_gt hh))
        have hz1 := coordinate_le_one hz s
        have : A' = 0 := by dsimp [A']; rw [hG, max_eq_right (by linarith)]
        linarith
      have hchange : A'-A ≤ (dist s x/r)/(10*T.R) := by
        have h1 := abs_max_sub_max_le_abs (z s-G T (dist x p/r)) (z s-G T (dist s p/r)) 0
        have heq : (z s-G T (dist x p/r))-(z s-G T (dist s p/r)) =
            G T (dist s p/r)-G T (dist x p/r) := by ring
        rw [heq] at h1
        exact (le_abs_self _).trans (h1.trans ((G_lipschitz T _ _).trans
          (div_le_div_of_nonneg_right (scaled_dist_lipschitz hr s x p)
            (by linarith [T.R_ge]))))
      have hrepair : ∀ i, β' i ≤ max (β i - (dist s x/r)/(10*T.R)) 0 := by
        intro i
        by_cases hix : i=x
        · simp only [β', ite_eq_left hix]; exact le_max_right _ _
        · by_cases his : i=s
          · subst i
            have hzero : β' s = 0 := le_antisymm (by simpa [β] using hb' s)
              (by simp only [β', ite_eq_right hix]; exact le_max_right _ _)
            rw [hzero]; exact le_max_right _ _
          · by_cases hi : dist x i < 50*T.R*r
            · simp only [β', ite_eq_right hix, β, ite_eq_right his, relocate, ite_eq_left hi]
              rw [clip_reduction (G_nonneg T _) hq]
            · have hβzero : β i = 0 := by
                have hip : 20*T.R*r ≤ dist i p := by
                  have ht := dist_triangle x p i
                  rw [dist_comm p i] at ht
                  linarith
                have hG : G T (dist i p/r) = 1 := G_eq_one ((le_div_iff₀ hr).mpr hip)
                simp only [β, ite_eq_right his, hG]
                exact max_eq_right (by linarith [coordinate_le_one hz i])
              exact (hb' i).trans (by rw [hβzero]; exact le_max_right _ _)
      have hAone : A' ≤ 1 := max_le (by
        have := coordinate_le_one hz s
        linarith [G_nonneg T (dist x p/r)]) zero_le_one
      exact (add_le_add (le_refl A') (sum_le_sum (fun i _ => hrepair i))).trans
        (capacity_repair hq hβ hcap hAone hchange)
  · intro i j hij hd
    have hσr : T.σ*r ≤ r := mul_le_of_le_one_left hr.le T.σ_le
    have hbig : 5*T.σ*r ≤ T.R*r/2 := by
      have hR := mul_le_mul_of_nonneg_right T.R_ge hr.le
      linarith
    by_cases hix : i=x
    · subst i
      by_cases hjs : j=s
      · subst j; rw [(relocate_at hne).2, mul_zero]
      · have hzj := hother j hjs (by rw [dist_comm j x]; linarith)
        have hjx : j ≠ x := Ne.symm hij
        have hjzero : relocate T r z s x j = 0 := le_antisymm
          (by simpa only [hzj] using (relocate_le hr hz hjx).2) (hn j)
        rw [hjzero, mul_zero]
    · by_cases hjx : j=x
      · subst j
        by_cases his : i=s
        · subst i; rw [(relocate_at hne).2, zero_mul]
        · have hzi := hother i his (by linarith)
          have hizero : relocate T r z s x i = 0 := le_antisymm
            (by simpa only [hzi] using (relocate_le hr hz hix).2) (hn i)
          rw [hizero, zero_mul]
      · have hmul := mul_le_mul (relocate_le (s := s) hr hz hix).2 (relocate_le (s := s) hr hz hjx).2 (hn j) (hz.1 i)
        rw [hz.2.2 i j hij hd] at hmul
        exact le_antisymm hmul (mul_nonneg (hn i) (hn j))

lemma b_sum_single {T : Template} {r γ : ℝ} {z : Y → ℝ} {s x p : Y}
    (hr : 0 < r) (hγ : γ ≤ T.σ/64) (hs : dist s x < T.σ*r/4)
    (hp : dist x p ≤ γ*r)
    (hother : ∀ i, i ≠ s → dist i x ≤ T.R*r/2 → z i = 0) :
    (∑ i, z i * b T (dist i p/r)) = z s := by
  have hsr : 0 < T.σ*r := mul_pos T.σ_pos hr
  have hγr : γ*r ≤ T.σ*r/64 := by nlinarith [mul_le_mul_of_nonneg_right hγ hr.le]
  have hsp : dist s p/r ≤ T.σ := (div_le_iff₀ hr).mpr (by
    have := dist_triangle s x p; linarith)
  have hb_one : b T (dist s p/r) = 1 := b_eq_one hsp
  rw [← mul_one (z s), ← hb_one]
  apply sum_eq_single s
  · intro i _ his
    by_cases hi : dist i x ≤ T.R*r/2
    · rw [hother i his hi, zero_mul]
    · have hip : 2*T.σ ≤ dist i p/r := by
        apply (le_div_iff₀ hr).mpr
        have htri := dist_triangle i p x
        rw [dist_comm p x] at htri
        have hRr := mul_le_mul_of_nonneg_right T.R_ge hr.le
        have hσr := mul_le_of_le_one_left hr.le T.σ_le
        linarith
      rw [b_eq_zero hip, mul_zero]
  · simp

lemma sum_relocate_le {T : Template} {r : ℝ} {z f : Y → ℝ} {s x : Y}
    (hr : 0 < r) (hz : Feasible T r z) (hne : s ≠ x) (hzx : z x = 0)
    (hf : ∀ i, 0 ≤ f i) :
    (∑ i, relocate T r z s x i * f i) ≤ (∑ i, z i*f i) - z s*f s + z s*f x := by
  calc _ ≤ ∑ i, (z i*f i - (if i=s then z s*f s else 0) + (if i=x then z s*f x else 0)) := by
         apply sum_le_sum
         intro i _
         by_cases hix : i=x
         · subst i; simp [Ne.symm hne, hzx, (relocate_at hne).1]
         · by_cases his : i=s
           · subst i; simp [hne, (relocate_at hne).2]
           · simp only [ite_eq_right his, ite_eq_right hix, sub_zero, add_zero]
             exact mul_le_mul_of_nonneg_right (relocate_le hr hz hix).2 (hf i)
       _ = _ := by rw [sum_add_distrib, sum_sub_distrib]; simp

lemma moved_square_gain {L γ w u v gs gx : ℝ}
    (hL : 0 ≤ L) (hγL : L*γ ≤ 1) (hw : 0 ≤ w) (_ : 0 ≤ u)
    (hv : 0 ≤ v) (hvγ : v ≤ γ) (hwu : w ≤ u+v) (hvu : v ≤ u+w)
    (hgs : gs ∈ Set.Icc 0 1) (hgg : |gs-gx| ≤ L*w) :
    w^2-5*w*v ≤ (1+gs)*u^2-(1+gx)*v^2 := by
  have hquad : w^2-2*w*v+v^2 ≤ u^2 := by
    have hp := mul_nonneg (show 0 ≤ u-w+v by linarith) (show 0 ≤ u+w-v by linarith)
    nlinarith
  have hq := mul_le_mul_of_nonneg_left hquad (show 0 ≤ 1+gs by linarith [hgs.1])
  have hgg' : -(L*w) ≤ gs-gx := (abs_le.mp hgg).1
  have hgm := mul_le_mul_of_nonneg_right hgg' (sq_nonneg v)
  have hvL : L*v ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hvγ hL) hγL
  have herr := mul_le_mul_of_nonneg_right hvL (mul_nonneg hw hv)
  have hgsw := mul_nonneg hgs.1 (sq_nonneg w)
  have hgsv := mul_le_mul_of_nonneg_right hgs.2 (mul_nonneg hw hv)
  nlinarith

lemma a_eq_square {T : Template} {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ T.σ) :
    a T v = v^2/T.σ^2 := by
  have hvR : v ≤ T.R := le_trans hv (by linarith [T.σ_le, T.R_ge])
  rw [a, ite_eq_left hvR, min_eq_left]
  apply (div_le_one (sq_pos_of_pos T.σ_pos)).mpr
  nlinarith [T.σ_pos]

lemma relocate_inner_gain {T : Template} {r γ : ℝ} {g z : Y → ℝ} {s x p : Y}
    (hr : 0 < r) (hγ : γ ≤ T.σ/64) (hγL : T.L*γ ≤ 1)
    (hg : ∀ i, g i ∈ Set.Icc 0 1)
    (hglip : ∀ i j, |g i-g j| ≤ T.L*(dist i j/r))
    (hz : Feasible T r z) (hne : s ≠ x) (hs : dist s x < T.σ*r/4)
    (hp : dist x p ≤ γ*r)
    (hother : ∀ i, i ≠ s → dist i x ≤ T.R*r/2 → z i = 0) :
    (256*z s/T.σ^2) * ((dist s x/r)^2-5*(dist s x/r)*(dist x p/r)) ≤
      integrand T r g z p - integrand T r g (relocate T r z s x) p := by
  have hγr : γ*r ≤ T.σ*r/64 := by nlinarith [mul_le_mul_of_nonneg_right hγ hr.le]
  have hσr : 0 < T.σ*r := mul_pos T.σ_pos hr
  have hsp : dist s p/r ≤ T.σ := (div_le_iff₀ hr).mpr (by
    have := dist_triangle s x p; linarith)
  have hxp : dist x p/r ≤ T.σ := (div_le_iff₀ hr).mpr (by linarith)
  have hzX : z x = 0 := hother x (Ne.symm hne) (by simp; nlinarith [T.R_ge])
  have hnewother : ∀ i, i ≠ x → dist i x ≤ T.R*r/2 → relocate T r z s x i = 0 := by
    intro i hix hi
    by_cases his : i=s
    · subst i; exact (relocate_at hne).2
    · exact le_antisymm (by simpa only [hother i his hi] using (relocate_le hr hz hix).2)
        (relocate_le hr hz hix).1
  have hb := b_sum_single hr hγ hs hp hother
  have hb' := b_sum_single hr hγ (s := x) (by simp; linarith) hp hnewother
  rw [(relocate_at hne).1] at hb'
  have hsum := sum_relocate_le hr hz hne hzX (f := fun i => (1+g i)*a T (dist i p/r))
    (fun i => mul_nonneg (by linarith [(hg i).1]) (a_nonneg _ _))
  have hquad := moved_square_gain T.L_nonneg hγL (div_nonneg dist_nonneg hr.le)
    (div_nonneg dist_nonneg hr.le) (div_nonneg dist_nonneg hr.le)
    ((div_le_iff₀ hr).mpr hp)
    (show dist s x/r ≤ dist s p/r + dist x p/r by
      rw [← add_div]; apply div_le_div_of_nonneg_right _ hr.le
      have := dist_triangle s p x; simpa only [dist_comm p x] using this)
    (show dist x p/r ≤ dist s p/r + dist s x/r by
      rw [← add_div]; apply div_le_div_of_nonneg_right _ hr.le
      have := dist_triangle x s p; simpa only [dist_comm x s, add_comm] using this)
    (hg s) (hglip s x)
  have hquad' := mul_le_mul_of_nonneg_left hquad
    (show 0 ≤ 256*z s/T.σ^2 by exact div_nonneg (mul_nonneg (by norm_num) (hz.1 s)) (sq_nonneg _))
  rw [a_eq_square (div_nonneg dist_nonneg hr.le) hsp,
    a_eq_square (div_nonneg dist_nonneg hr.le) hxp] at hsum
  unfold integrand
  rw [hb, hb']
  have heq : (256*z s/T.σ^2)*((1+g s)*(dist s p/r)^2-(1+g x)*(dist x p/r)^2) =
      256*(z s*(1+g s)*((dist s p/r)^2/T.σ^2)-z s*(1+g x)*((dist x p/r)^2/T.σ^2)) := by ring
  rw [heq] at hquad'
  simp only [mul_assoc] at hsum hquad' ⊢
  linarith only [hquad', hsum]

omit [MetricSpace Y] in
lemma sum_unique_le {f : Y → ℝ} {q : ℝ} (hq : 0 ≤ q)
    (hf : ∀ i, 0 ≤ f i) (hfq : ∀ i, f i ≤ q)
    (hun : ∀ i j, 0 < f i → 0 < f j → i=j) : (∑ i, f i) ≤ q := by
  by_cases h : ∃ i, 0 < f i
  · obtain ⟨i, hi⟩ := h
    have he : (∑ j, f j) = f i := by
      apply sum_eq_single i
      · intro j _ hji
        exact le_antisymm (le_of_not_gt (fun hj => hji (hun j i hj hi))) (hf j)
      · simp
    rw [he]; exact hfq i
  · push Not at h
    have : ∀ i, f i = 0 := fun i => le_antisymm (h i) (hf i)
    simpa only [this, sum_const_zero] using hq

omit [Fintype Y] in
lemma relocate_decrease_le {T : Template} {r : ℝ} {z : Y → ℝ} {s x i : Y}
    (hr : 0 < r) (hix : i ≠ x) (his : i ≠ s) :
    z i-relocate T r z s x i ≤ (dist s x/r)/(10*T.R) := by
  have hq : 0 ≤ (dist s x/r)/(10*T.R) := div_nonneg (div_nonneg dist_nonneg hr.le)
    (by linarith [T.R_ge])
  unfold relocate
  rw [ite_eq_right hix, ite_eq_right his]
  split_ifs
  · linarith [le_max_left (z i-(dist s x/r)/(10*T.R)) 0]
  · simpa only [sub_self] using hq

lemma relocate_residual_loss {T : Template} {r : ℝ} {z : Y → ℝ} {s x p : Y}
    (hr : 0 < r) (hz : Feasible T r z) (hne : s ≠ x) (hzx : z x = 0) :
    (∑ i, z i*b T (dist i p/r)) - (∑ i, relocate T r z s x i*b T (dist i p/r)) ≤
      z s*(dist s x/r)/T.σ + (dist s x/r)/(10*T.R) := by
  let f : Y → ℝ := fun i => if i=s ∨ i=x then 0 else
    (z i-relocate T r z s x i)*b T (dist i p/r)
  have hf : ∀ i, 0 ≤ f i := by
    intro i; dsimp [f]; split_ifs with hi
    · rfl
    · exact mul_nonneg (sub_nonneg.mpr (relocate_le hr hz (not_or.mp hi).2).2) (b_nonneg _ _)
  have hq : 0 ≤ (dist s x/r)/(10*T.R) := div_nonneg (div_nonneg dist_nonneg hr.le)
    (by linarith [T.R_ge])
  have hbound : ∀ i, f i ≤ (dist s x/r)/(10*T.R) := by
    intro i; dsimp [f]; split_ifs with hi
    · exact hq
    · have hx := (not_or.mp hi).2
      have hs := (not_or.mp hi).1
      calc _ ≤ ((dist s x/r)/(10*T.R))*1 := mul_le_mul
             (relocate_decrease_le hr hx hs) (b_le_one _ _) (b_nonneg _ _) hq
           _ = _ := mul_one _
  have hsupport : ∀ i, 0 < f i → 0 < z i ∧ 0 < b T (dist i p/r) := by
    intro i hi
    dsimp [f] at hi
    split_ifs at hi with hix
    · exact (lt_irrefl _ hi).elim
    · have hdiff : 0 < z i-relocate T r z s x i :=
        pos_of_mul_pos_left hi (b_nonneg _ _)
      have hb : 0 < b T (dist i p/r) := pos_of_mul_pos_right hi hdiff.le
      exact ⟨by linarith [(relocate_le (s := s) hr hz (not_or.mp hix).2).1], hb⟩
  have hsum : (∑ i, f i) ≤ (dist s x/r)/(10*T.R) :=
    sum_unique_le hq hf hbound (fun i j hi hj => positive_b_support_disjoint hr hz
      (hsupport i hi).1 (hsupport j hj).1 (hsupport i hi).2 (hsupport j hj).2)
  have he : (∑ i, z i*b T (dist i p/r)) - (∑ i, relocate T r z s x i*b T (dist i p/r)) =
      z s*b T (dist s p/r) - z s*b T (dist x p/r) + ∑ i, f i := by
    rw [← sum_sub_distrib]
    have hpw : ∀ i, z i*b T (dist i p/r) - relocate T r z s x i*b T (dist i p/r) =
        (if i=s then z s*b T (dist s p/r) else 0) -
          (if i=x then z s*b T (dist x p/r) else 0) + f i := by
      intro i
      by_cases his : i=s
      · subst i; simp [f, hne, (relocate_at hne).2]
      · by_cases hix : i=x
        · subst i; simp [f, Ne.symm hne, hzx, (relocate_at hne).1]
        · simp only [f, his, hix, false_or, ite_false, sub_zero, zero_add]
          ring
    simp only [hpw, sum_add_distrib, sum_sub_distrib]
    simp
  have hb : b T (dist s p/r)-b T (dist x p/r) ≤ (dist s x/r)/T.σ :=
    (le_abs_self _).trans ((b_lipschitz T _ _).trans
      (div_le_div_of_nonneg_right (scaled_dist_lipschitz hr s x p) T.σ_pos.le))
  have hbm := mul_le_mul_of_nonneg_left hb (hz.1 s)
  rw [he]
  calc _ = z s*(b T (dist s p/r)-b T (dist x p/r)) + ∑ i, f i := by ring
       _ ≤ z s*((dist s x/r)/T.σ) + (dist s x/r)/(10*T.R) := add_le_add hbm hsum
       _ = _ := by ring

omit [Fintype Y] in
lemma moved_surcharge_loss {T : Template} {r : ℝ} {g : Y → ℝ} {s x p : Y}
    (hr : 0 < r) (hg : ∀ i, g i ∈ Set.Icc 0 1)
    (hglip : ∀ i j, |g i-g j| ≤ T.L*(dist i j/r)) :
    (1+g x)*a T (dist x p/r)-(1+g s)*a T (dist s p/r) ≤
      (4/T.σ+T.L)*(dist s x/r) := by
  have ha : |a T (dist x p/r)-a T (dist s p/r)| ≤ (2/T.σ)*(dist s x/r) := by
    have h1 := a_lipschitz (T := T) (u := dist x p/r) (v := dist s p/r) (div_nonneg dist_nonneg hr.le) (div_nonneg dist_nonneg hr.le)
    apply h1.trans
    have h2 := scaled_dist_lipschitz hr x s p
    rw [dist_comm x s] at h2
    exact mul_le_mul_of_nonneg_left h2 (div_nonneg (by norm_num) T.σ_pos.le)
  have hg' : g x-g s ≤ T.L*(dist s x/r) := by
    have := (le_abs_self (g x-g s)).trans (hglip x s)
    simpa only [dist_comm x s] using this
  have hleft := mul_le_mul_of_nonneg_left (le_abs_self (a T (dist x p/r)-a T (dist s p/r)))
    (show 0 ≤ 1+g x by linarith [(hg x).1])
  have hm := mul_le_mul (show 1+g x ≤ 2 by linarith [(hg x).2]) ha (abs_nonneg _)
    (by norm_num : (0:ℝ) ≤ 2)
  have hright : (g x-g s)*a T (dist s p/r) ≤ T.L*(dist s x/r) := by
    calc _ ≤ (T.L*(dist s x/r))*1 := mul_le_mul hg' (a_le_one _ _) (a_nonneg _ _)
           (mul_nonneg T.L_nonneg (div_nonneg dist_nonneg hr.le))
         _ = _ := mul_one _
  calc _ = (1+g x)*(a T (dist x p/r)-a T (dist s p/r)) + (g x-g s)*a T (dist s p/r) := by ring
       _ ≤ 2*((2/T.σ)*(dist s x/r)) + T.L*(dist s x/r) := add_le_add (hleft.trans hm) hright
       _ = _ := by ring

lemma relocate_shell_loss {T : Template} {r : ℝ} {g z : Y → ℝ} {s x p : Y}
    (hr : 0 < r) (hg : ∀ i, g i ∈ Set.Icc 0 1)
    (hglip : ∀ i j, |g i-g j| ≤ T.L*(dist i j/r))
    (hz : Feasible T r z) (hne : s ≠ x) (hzx : z x = 0) :
    integrand T r g (relocate T r z s x) p - integrand T r g z p ≤
      (z s*(1026/T.σ+256*T.L)+2/(10*T.R))*(dist s x/r) := by
  have hb := relocate_residual_loss (p := p) hr hz hne hzx
  have hb0 : 0 ≤ z s*(dist s x/r)/T.σ + (dist s x/r)/(10*T.R) := by
    apply add_nonneg
    · exact div_nonneg (mul_nonneg (hz.1 s) (div_nonneg dist_nonneg hr.le)) T.σ_pos.le
    · exact div_nonneg (div_nonneg dist_nonneg hr.le) (by linarith [T.R_ge])
  have hres := mul_le_mul_of_nonneg_left hb (show 0 ≤ 1+g p by linarith [(hg p).1])
  have hres2 := mul_le_mul_of_nonneg_right (show 1+g p ≤ 2 by linarith [(hg p).2]) hb0
  have hsum := sum_relocate_le hr hz hne hzx (f := fun i => (1+g i)*a T (dist i p/r))
    (fun i => mul_nonneg (by linarith [(hg i).1]) (a_nonneg _ _))
  have hm := mul_le_mul_of_nonneg_left (moved_surcharge_loss (s := s) (x := x) (p := p) hr hg hglip) (hz.1 s)
  have hsumdiff : (∑ i, relocate T r z s x i * ((1+g i)*a T (dist i p/r))) -
      (∑ i, z i*((1+g i)*a T (dist i p/r))) ≤ z s*((4/T.σ+T.L)*(dist s x/r)) := by
    linarith only [hsum, hm]
  unfold integrand
  simp only [mul_assoc]
  calc _ = (1+g p)*((∑ i, z i*b T (dist i p/r))-(∑ i, relocate T r z s x i*b T (dist i p/r))) +
      256*((∑ i, relocate T r z s x i*((1+g i)*a T (dist i p/r)))-(∑ i, z i*((1+g i)*a T (dist i p/r)))) := by ring
       _ ≤ 2*(z s*(dist s x/r)/T.σ+(dist s x/r)/(10*T.R)) +
        256*(z s*((4/T.σ+T.L)*(dist s x/r))) :=
          add_le_add (hres.trans hres2) (mul_le_mul_of_nonneg_left hsumdiff (by norm_num))
       _ = _ := by ring

lemma relocate_integrand_outside {T : Template} {r : ℝ} {g z : Y → ℝ} {s x p : Y}
    (hr : 0 < r) (hs : dist s x < T.σ*r/4) (hp : 100*T.R*r ≤ dist x p) :
    integrand T r g (relocate T r z s x) p = integrand T r g z p := by
  have hab : ∀ i, relocate T r z s x i ≠ z i →
      a T (dist i p/r) = 0 ∧ b T (dist i p/r) = 0 := by
    intro i hi
    have hxi : dist x i ≤ 50*T.R*r := by
      by_cases hix : i=x
      · subst i; simp only [dist_self]; nlinarith [T.R_ge]
      · by_cases his : i=s
        · subst i
          rw [dist_comm x s]
          have hσr : T.σ*r ≤ r := mul_le_of_le_one_left hr.le T.σ_le
          have hRr := mul_le_mul_of_nonneg_right T.R_ge hr.le
          linarith
        · by_contra hh
          exact hi (by simp [relocate, hix, his, not_lt.mpr (le_of_not_ge hh)])
    have hd : 2*T.R ≤ dist i p/r := by
      apply (le_div_iff₀ hr).mpr
      have htri := dist_triangle x i p
      have hRr : 0 ≤ T.R*r := mul_nonneg (by linarith [T.R_ge]) hr.le
      linarith
    exact ⟨a_eq_zero hd, b_eq_zero (by linarith [T.σ_le, T.R_ge])⟩
  unfold integrand
  congr 2
  · congr 1; apply sum_congr rfl; intro i _
    by_cases hi : relocate T r z s x i = z i
    · rw [hi]
    · simp [(hab i hi).2]
  · apply sum_congr rfl; intro i _
    by_cases hi : relocate T r z s x i = z i
    · rw [hi]
    · simp [(hab i hi).1]

lemma relocation_coefficient_bound (T : Template) {z : ℝ} (hz : 3/4 ≤ z) :
    z*(1026/T.σ+256*T.L)+2/(10*T.R) ≤ (256*z/T.σ^2)*(5+T.L) := by
  have hz0 : 0 ≤ z := by linarith
  have hσ2 : 0 < T.σ^2 := sq_pos_of_pos T.σ_pos
  have hσ21 : T.σ^2 ≤ 1 := by nlinarith [T.σ_pos, T.σ_le]
  have hq : 2/(10*T.R) ≤ 1 := (div_le_one (by linarith [T.R_ge])).mpr (by linarith [T.R_ge])
  have hp : 1026*T.σ+256*T.L*T.σ^2 ≤ 1026+256*T.L := by
    have := mul_le_mul_of_nonneg_left hσ21 (show 0 ≤ 256*T.L by nlinarith [T.L_nonneg])
    linarith [T.σ_le]
  have hpz := mul_le_mul_of_nonneg_left hp hz0
  have hqσ := mul_le_mul hq hσ21 hσ2.le zero_le_one
  have he : (z*(1026/T.σ+256*T.L)+2/(10*T.R))*T.σ^2 =
      z*(1026*T.σ+256*T.L*T.σ^2)+(2/(10*T.R))*T.σ^2 := by
    field_simp [T.σ_pos.ne']
  have hs : (z*(1026/T.σ+256*T.L)+2/(10*T.R))*T.σ^2 ≤ 256*z*(5+T.L) := by
    rw [he]; nlinarith
  have hf := (le_div_iff₀ hσ2).mpr hs
  calc _ ≤ 256*z*(5+T.L)/T.σ^2 := hf
       _ = _ := by ring

lemma relocate_displacement {T : Template} {r γ : ℝ} {μ g z : Y → ℝ} {s x : Y}
    (hr : 0 < r) (hγ : γ ≤ T.σ/64) (hγL : T.L*γ ≤ 1)
    (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ i, g i ∈ Set.Icc 0 1)
    (hglip : ∀ i j, |g i-g j| ≤ T.L*(dist i j/r))
    (hz : Feasible T r z)
    (hmin : IsMinOn (objective T r μ g) {w | Feasible T r w} z)
    (hs : dist s x < T.σ*r/4) (hweight : 3/4 ≤ z s)
    (hother : ∀ i, i ≠ s → dist i x ≤ T.R*r/2 → z i = 0) :
    (dist s x/r)*mass μ (ball x (γ*r)) ≤
      (5+T.L)*(mass μ (ball x (100*T.R*r) \ ball x (γ*r))+innerMoment μ x γ r) := by
  have hmoment : 0 ≤ innerMoment μ x γ r :=
    sum_nonneg (fun p _ => mul_nonneg (hμ p) (div_nonneg dist_nonneg hr.le))
  have hshell : 0 ≤ mass μ (ball x (100*T.R*r) \ ball x (γ*r)) := sum_nonneg (fun p _ => hμ p)
  by_cases hne : s=x
  · subst s; simp only [dist_self, zero_div, zero_mul]
    exact mul_nonneg (by linarith [T.L_nonneg]) (add_nonneg hshell hmoment)
  have hzX : z x = 0 := hother x (Ne.symm hne) (by simp; nlinarith [T.R_ge])
  let w : ℝ := dist s x/r
  let A : ℝ := 256*z s/T.σ^2
  let K : ℝ := z s*(1026/T.σ+256*T.L)+2/(10*T.R)
  have hw : 0 < w := div_pos (dist_pos.mpr hne) hr
  have hA : 0 < A := div_pos (by nlinarith) (sq_pos_of_pos T.σ_pos)
  have hK : K ≤ A*(5+T.L) := relocation_coefficient_bound T hweight
  have hf := relocate_feasible hr hz hne hother
  have hm := hmin hf
  change r*(∑ p, μ p*integrand T r g z p) ≤
    r*(∑ p, μ p*integrand T r g (relocate T r z s x) p) at hm
  have hcost : 0 ≤ ∑ p, μ p*(integrand T r g (relocate T r z s x) p-integrand T r g z p) := by
    simp only [mul_sub, sum_sub_distrib]
    exact sub_nonneg.mpr ((mul_le_mul_iff_right₀ hr).mp hm)
  have hpoint : ∀ p, μ p*(integrand T r g (relocate T r z s x) p-integrand T r g z p) ≤
      (if p ∈ ball x (γ*r) then μ p * (-A*(w^2-5*w*(dist x p/r))) else 0) +
      (if p ∈ ball x (100*T.R*r) \ ball x (γ*r) then μ p*K*w else 0) := by
    intro p
    by_cases hp : p ∈ ball x (γ*r)
    · rw [ite_eq_left hp, ite_eq_right (by simp [hp]), add_zero]
      apply mul_le_mul_of_nonneg_left _ (hμ p)
      have hgain := relocate_inner_gain hr hγ hγL hg hglip hz hne hs (mem_filter.mp hp).2 hother
      dsimp [w, A]; linarith
    · rw [ite_eq_right hp, zero_add]
      by_cases hout : p ∈ ball x (100*T.R*r)
      · rw [ite_eq_left (mem_sdiff.mpr ⟨hout, hp⟩)]
        have h := mul_le_mul_of_nonneg_left (relocate_shell_loss (p := p) hr hg hglip hz hne hzX) (hμ p)
        simpa only [mul_assoc] using h
      · rw [ite_eq_right (by simp [hout])]
        have he := relocate_integrand_outside (g := g) (z := z) hr hs
          (show 100*T.R*r ≤ dist x p from le_of_lt (by simpa [ball] using hout))
        rw [he, sub_self, mul_zero]
  have hsum := sum_le_sum fun p (_ : p ∈ (univ : Finset Y)) => hpoint p
  rw [sum_add_distrib] at hsum
  simp only [← sum_filter, filter_mem_eq_inter, Finset.univ_inter] at hsum
  have he1 : (∑ p ∈ ball x (γ*r), μ p*(-A*(w^2-5*w*(dist x p/r)))) =
      5*A*w*innerMoment μ x γ r - A*w^2*mass μ (ball x (γ*r)) := by
    unfold innerMoment mass
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl; intro p _; ring
  have he2 : (∑ p ∈ ball x (100*T.R*r) \ ball x (γ*r), μ p*K*w) =
      K*w*mass μ (ball x (100*T.R*r) \ ball x (γ*r)) := by
    unfold mass; rw [mul_sum]; apply sum_congr rfl; intro p _; ring
  rw [he1, he2] at hsum
  have hgain : (A*w)*(w*mass μ (ball x (γ*r))-5*innerMoment μ x γ r) ≤
      K*w*mass μ (ball x (100*T.R*r) \ ball x (γ*r)) := by nlinarith only [hcost, hsum]
  have hK' := mul_le_mul_of_nonneg_right hK (mul_nonneg hw.le hshell)
  have hgain' : (A*w)*(w*mass μ (ball x (γ*r))-5*innerMoment μ x γ r) ≤
      (A*w)*((5+T.L)*mass μ (ball x (100*T.R*r) \ ball x (γ*r))) := by
    nlinarith only [hgain, hK']
  have hlast := (mul_le_mul_iff_right₀ (mul_pos hA hw)).mp hgain'
  change w*mass μ (ball x (γ*r)) ≤ _
  nlinarith [mul_nonneg T.L_nonneg hmoment]

lemma b_sum_near {T : Template} {r : ℝ} {z : Y → ℝ} {s x p : Y}
    (hr : 0 < r) (hs : dist s x < T.σ*r/4) (hp : dist x p < T.σ*r/8)
    (hother : ∀ i, i ≠ s → dist i x ≤ T.R*r/2 → z i = 0) :
    (∑ i, z i*b T (dist i p/r)) = z s := by
  have hsp : dist s p/r ≤ T.σ := (div_le_iff₀ hr).mpr (by
    have := dist_triangle s x p; have := mul_pos T.σ_pos hr; linarith)
  conv_rhs => rw [← mul_one (z s), ← b_eq_one hsp]
  apply sum_eq_single s
  · intro i _ his
    by_cases hi : dist i x ≤ T.R*r/2
    · rw [hother i his hi, zero_mul]
    · have hip : 2*T.σ ≤ dist i p/r := by
        apply (le_div_iff₀ hr).mpr
        have htri := dist_triangle i p x
        rw [dist_comm p x] at htri
        have := mul_le_mul_of_nonneg_right T.R_ge hr.le
        have := mul_le_of_le_one_left hr.le T.σ_le
        linarith
      rw [b_eq_zero hip, mul_zero]
  · simp

lemma surcharge_diff_by_capacity {T : Template} {r : ℝ} {g z : Y → ℝ} {x y i : Y}
    (hr : 0 < r) (hg : ∀ i, g i ∈ Set.Icc 0 1) (hz : Feasible T r z)
    (hxy : dist x y < T.σ*r/8) :
    z i*(1+g i)*(a T (dist i x/r)-a T (dist i y/r)) ≤
      (4/T.σ)*(dist x y/r)*max (z i-G T (dist i x/r)) 0 := by
  have hc : 0 ≤ (4/T.σ)*(dist x y/r) :=
    mul_nonneg (div_nonneg (by norm_num) T.σ_pos.le) (div_nonneg dist_nonneg hr.le)
  have hR : 0 < T.R := by linarith [T.R_ge]
  have hσr : T.σ*r ≤ r := mul_le_of_le_one_left hr.le T.σ_le
  by_cases hi : dist i x/r ≤ 10*T.R
  · rw [G_eq_zero hi, sub_zero, max_eq_left (hz.1 i)]
    have hd : |a T (dist i x/r)-a T (dist i y/r)| ≤ (2/T.σ)*(dist x y/r) := by
      apply (a_lipschitz (T := T) (u := dist i x/r) (v := dist i y/r)
        (div_nonneg dist_nonneg hr.le) (div_nonneg dist_nonneg hr.le)).trans
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) T.σ_pos.le)
      have h := scaled_dist_lipschitz hr x y i
      simpa only [dist_comm i x, dist_comm i y] using h
    have h1 := mul_le_mul (show 1+g i ≤ 2 by linarith [(hg i).2]) hd (abs_nonneg _)
      (by norm_num : (0:ℝ) ≤ 2)
    have h2 := mul_le_mul_of_nonneg_left (le_abs_self (a T (dist i x/r)-a T (dist i y/r)))
      (show 0 ≤ 1+g i by linarith [(hg i).1])
    have h3 := mul_le_mul_of_nonneg_left (h2.trans h1) (hz.1 i)
    calc _ = z i*((1+g i)*(a T (dist i x/r)-a T (dist i y/r))) := by ring
         _ ≤ z i*(2*((2/T.σ)*(dist x y/r))) := h3
         _ = _ := by ring
  · have hix : 2*T.R ≤ dist i x/r := by linarith
    have hiy : 2*T.R ≤ dist i y/r := by
      apply (le_div_iff₀ hr).mpr
      have hi' := (lt_div_iff₀ hr).mp (lt_of_not_ge hi)
      have := dist_triangle i y x
      rw [dist_comm y x] at this
      have := mul_le_mul_of_nonneg_right T.R_ge hr.le
      nlinarith
    rw [a_eq_zero hix, a_eq_zero hiy, sub_self, mul_zero]
    exact mul_nonneg hc (le_max_right _ _)

lemma near_square_loss {T : Template} {r : ℝ} {g z : Y → ℝ} {s x y : Y}
    (hr : 0 < r) (hg : ∀ i, g i ∈ Set.Icc 0 1) (hz : Feasible T r z)
    (hs : dist s x < T.σ*r/4) (hxy : dist x y < T.σ*r/8) :
    z s*(1+g s)*(a T (dist s x/r)-a T (dist s y/r)) ≤
      (4/T.σ^2)*(dist s x/r)*(dist x y/r) := by
  have hw : 0 ≤ dist s x/r := div_nonneg dist_nonneg hr.le
  have hv : 0 ≤ dist x y/r := div_nonneg dist_nonneg hr.le
  have hsx : dist s x/r ≤ T.σ := (div_le_iff₀ hr).mpr (by nlinarith [mul_pos T.σ_pos hr])
  have hsy : dist s y/r ≤ T.σ := (div_le_iff₀ hr).mpr (by
    have := dist_triangle s x y; have := mul_pos T.σ_pos hr; linarith)
  have htri : dist s x/r-dist s y/r ≤ dist x y/r := by
    have ht := div_le_div_of_nonneg_right (dist_triangle s y x) hr.le
    rw [dist_comm y x, add_div] at ht
    linarith
  have hq : (dist s x/r)^2-(dist s y/r)^2 ≤ 2*(dist s x/r)*(dist x y/r) := by
    have := mul_le_mul_of_nonneg_left htri hw
    nlinarith [sq_nonneg (dist s x/r-dist s y/r)]
  have hcoef : z s*(1+g s) ≤ 2 := by
    have := mul_le_mul (coordinate_le_one hz s) (show 1+g s ≤ 2 by linarith [(hg s).2])
      (show 0 ≤ 1+g s by linarith [(hg s).1]) zero_le_one
    simpa using this
  have hcoef0 : 0 ≤ z s*(1+g s) := mul_nonneg (hz.1 s) (by linarith [(hg s).1])
  have h1 := mul_le_mul_of_nonneg_left hq hcoef0
  have h2 := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ 2*(dist s x/r)*(dist x y/r) by positivity)
  rw [a_eq_square hw hsx, a_eq_square (div_nonneg dist_nonneg hr.le) hsy]
  calc _ = (z s*(1+g s)*((dist s x/r)^2-(dist s y/r)^2))/T.σ^2 := by ring
       _ ≤ (2*(2*(dist s x/r)*(dist x y/r)))/T.σ^2 :=
         div_le_div_of_nonneg_right (h1.trans h2) (sq_nonneg _)
       _ = _ := by ring

lemma near_integrand_slope {T : Template} {r : ℝ} {g z : Y → ℝ} {s x y : Y}
    (hr : 0 < r) (hg : ∀ i, g i ∈ Set.Icc 0 1)
    (hglip : ∀ i j, |g i-g j| ≤ T.L*(dist i j/r))
    (hz : Feasible T r z) (hs : dist s x < T.σ*r/4) (hxy : dist x y < T.σ*r/8)
    (hother : ∀ i, i ≠ s → dist i x ≤ T.R*r/2 → z i = 0) :
    integrand T r g z x-integrand T r g z y ≤
      ((T.L+1024/T.σ)*(1-z s)+1024*(dist s x/r)/T.σ^2)*(dist x y/r) := by
  have hbx := b_sum_near hr hs (p := x) (by simp; exact mul_pos T.σ_pos hr) hother
  have hby := b_sum_near hr hs hxy hother
  have hsG : G T (dist s x/r) = 0 := G_eq_zero ((div_le_iff₀ hr).mpr (by
    have := mul_le_mul_of_nonneg_right T.R_ge hr.le
    have := mul_le_of_le_one_left hr.le T.σ_le
    linarith))
  have hcap : (∑ i ∈ univ.erase s, max (z i-G T (dist i x/r)) 0) ≤ 1-z s := by
    have h := hz.2.1 x
    rw [← sum_erase_add _ _ (mem_univ s), hsG, sub_zero, max_eq_left (hz.1 s)] at h
    linarith
  have hsum := sum_le_sum (s := univ.erase s) fun i _ =>
    surcharge_diff_by_capacity (i := i) hr hg hz hxy
  rw [← mul_sum] at hsum
  have hcap' := mul_le_mul_of_nonneg_left hcap
    (show 0 ≤ (4/T.σ)*(dist x y/r) from mul_nonneg (div_nonneg (by norm_num) T.σ_pos.le)
      (div_nonneg dist_nonneg hr.le))
  have hsum' := hsum.trans hcap'
  have hnear := near_square_loss hr hg hz hs hxy
  have hres := mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hglip x y))
    (sub_nonneg.mpr (coordinate_le_one hz s))
  have htotal : (∑ i, z i*(1+g i)*(a T (dist i x/r)-a T (dist i y/r))) ≤
      (4/T.σ)*(dist x y/r)*(1-z s)+(4/T.σ^2)*(dist s x/r)*(dist x y/r) := by
    rw [← sum_erase_add _ _ (mem_univ s)]
    exact add_le_add hsum' hnear
  have he : (∑ i, z i*(1+g i)*a T (dist i x/r)) -
      (∑ i, z i*(1+g i)*a T (dist i y/r)) =
      ∑ i, z i*(1+g i)*(a T (dist i x/r)-a T (dist i y/r)) := by
    rw [← sum_sub_distrib]; apply sum_congr rfl; intro i _; ring
  unfold integrand
  rw [hbx, hby]
  calc _ = (g x-g y)*(1-z s)+256*((∑ i, z i*(1+g i)*a T (dist i x/r)) -
      (∑ i, z i*(1+g i)*a T (dist i y/r))) := by ring
       _ = (g x-g y)*(1-z s)+256*(∑ i, z i*(1+g i)*(a T (dist i x/r)-a T (dist i y/r))) := by rw [he]
       _ ≤ (T.L*(dist x y/r))*(1-z s)+256*((4/T.σ)*(dist x y/r)*(1-z s)+
         (4/T.σ^2)*(dist s x/r)*(dist x y/r)) :=
          add_le_add hres (mul_le_mul_of_nonneg_left htotal (by norm_num))
       _ = _ := by ring

lemma localConstant_nonneg (T : Template) : 0 ≤ localConstant T := by
  unfold localConstant
  have hσ := T.σ_pos; have hL := T.L_nonneg
  positivity

lemma near_slope_mass {T : Template} {r M S J γ : ℝ} {g z : Y → ℝ} {s x y : Y}
    (hr : 0 < r) (hM : 0 ≤ M) (hS : 0 ≤ S) (hJ : 0 ≤ J)
    (hγ : γ ≤ T.σ/64) (hg : ∀ i, g i ∈ Set.Icc 0 1)
    (hglip : ∀ i j, |g i-g j| ≤ T.L*(dist i j/r))
    (hz : Feasible T r z) (hs : dist s x < T.σ*r/4) (hxy : dist x y < T.σ*r/8)
    (hother : ∀ i, i ≠ s → dist i x ≤ T.R*r/2 → z i = 0)
    (hdef : (1-z s)*M ≤ (512*γ/T.σ^2)*J+514*S)
    (hmove : (dist s x/r)*M ≤ (5+T.L)*(S+J)) :
    max (integrand T r g z x-integrand T r g z y) 0 * M ≤
      localConstant T*(S+J)*(dist x y/r) := by
  have hσ := T.σ_pos
  have hcoef : 512*γ/T.σ^2 ≤ 8/T.σ := by
    apply (div_le_iff₀ (sq_pos_of_pos hσ)).mpr
    calc 512*γ ≤ 8*T.σ := by linarith
         _ = (8/T.σ)*T.σ^2 := by field_simp
  have hdef' : (1-z s)*M ≤ (514+8/T.σ)*(S+J) := by
    have h1 := mul_le_mul_of_nonneg_right hcoef hJ
    have h2 : 0 ≤ (8/T.σ)*S := mul_nonneg (div_nonneg (by norm_num) hσ.le) hS
    nlinarith only [hdef, h1, h2, hJ]
  have h1 := mul_le_mul_of_nonneg_left hdef'
    (show 0 ≤ T.L+1024/T.σ from add_nonneg T.L_nonneg (div_nonneg (by norm_num) hσ.le))
  have h2 := mul_le_mul_of_nonneg_left hmove
    (show 0 ≤ 1024/T.σ^2 from div_nonneg (by norm_num) (sq_nonneg _))
  have hsum : ((T.L+1024/T.σ)*(1-z s)+1024*(dist s x/r)/T.σ^2)*M ≤
      localConstant T*(S+J) := by
    unfold localConstant
    calc _ = (T.L+1024/T.σ)*((1-z s)*M)+(1024/T.σ^2)*((dist s x/r)*M) := by ring
         _ ≤ (T.L+1024/T.σ)*((514+8/T.σ)*(S+J))+(1024/T.σ^2)*((5+T.L)*(S+J)) := add_le_add h1 h2
         _ = _ := by ring
  have hv : 0 ≤ dist x y/r := div_nonneg dist_nonneg hr.le
  have hslope := mul_le_mul_of_nonneg_right (near_integrand_slope hr hg hglip hz hs hxy hother) hM
  have hlast := mul_le_mul_of_nonneg_right hsum hv
  have hab : (integrand T r g z x-integrand T r g z y)*M ≤
      localConstant T*(S+J)*(dist x y/r) := by
    calc _ ≤ (((T.L+1024/T.σ)*(1-z s)+1024*(dist s x/r)/T.σ^2)*(dist x y/r))*M := hslope
         _ = (((T.L+1024/T.σ)*(1-z s)+1024*(dist s x/r)/T.σ^2)*M)*(dist x y/r) := by ring
         _ ≤ _ := hlast
  rw [max_mul_of_nonneg _ _ hM]
  apply max_le hab
  simpa only [zero_mul] using mul_nonneg (mul_nonneg (localConstant_nonneg T) (add_nonneg hS hJ)) hv

/-- The full local-optimality theorem, derived from the actual compact
minimizer, deletion, insertion and relocation competitors. -/
theorem local_structure {T : Template} {r γ δ : ℝ} {μ g z : Y → ℝ} {x : Y}
    (hr : 0 < r) (hγ0 : 0 ≤ γ) (hγ : γ ≤ T.σ/64) (hγL : T.L*γ ≤ 1)
    (hδ : δ ≤ 1/4112) (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc 0 1)
    (hglip : ∀ i j, |g i-g j| ≤ T.L*(dist i j/r))
    (hz : Feasible T r z) (hmin : IsMinOn (objective T r μ g) {w | Feasible T r w} z)
    (hM : 0 < mass μ (ball x (γ*r)))
    (hconc : mass μ (ball x (100*T.R*r) \ ball x (γ*r)) ≤ δ*mass μ (ball x (γ*r))) :
    (∀ i, T.σ*r/4 ≤ dist i x → dist i x ≤ T.R*r/2 → z i=0) ∧
    ∃ s, dist s x < T.σ*r/4 ∧ 3/4 ≤ z s ∧
      (∀ i, dist i x < T.σ*r/4 → 0 < z i → i=s) ∧
      (1-z s)*mass μ (ball x (γ*r)) ≤ 512*γ/T.σ^2*innerMoment μ x γ r +
        514*mass μ (ball x (100*T.R*r) \ ball x (γ*r)) ∧
      (dist s x/r)*mass μ (ball x (γ*r)) ≤ (5+T.L)*
        (mass μ (ball x (100*T.R*r) \ ball x (γ*r))+innerMoment μ x γ r) ∧
      ∀ y, dist x y < T.σ*r/8 →
        max (integrand T r g z x-integrand T r g z y) 0 * mass μ (ball x (γ*r)) ≤
          localConstant T*(mass μ (ball x (100*T.R*r) \ ball x (γ*r))+innerMoment μ x γ r)*(dist x y/r) := by
  have hsubset : ball x (γ*r) ⊆ ball x (100*T.R*r) := by
    intro p hp
    apply mem_filter.mpr ⟨mem_univ _, ?_⟩
    have hp' := (mem_filter.mp hp).2
    have := mul_le_mul_of_nonneg_right hγ hr.le
    have := mul_le_mul_of_nonneg_right T.R_ge hr.le
    have := mul_le_of_le_one_left hr.le T.σ_le
    nlinarith
  have hmass : mass μ (ball x (100*T.R*r)) ≤ (1+δ)*mass μ (ball x (γ*r)) := by
    have he := sum_sdiff (f := μ) hsubset
    change mass μ (ball x (100*T.R*r) \ ball x (γ*r)) + mass μ (ball x (γ*r)) =
      mass μ (ball x (100*T.R*r)) at he
    nlinarith
  have hmiddle : ∀ i, T.σ*r/4 ≤ dist i x → dist i x ≤ T.R*r/2 → z i=0 :=
    fun i hl hh => no_middle_site hr hγ hδ hμ hg hz hmin hl hh hM hmass
  obtain ⟨s, hs, hsz, he, hun⟩ := near_site_of_large hr hz
    (nearWeight_large hr hγ0 hγ hδ hμ hg hz hmin hmiddle hM hconc)
  have hs' : dist s x < T.σ*r/4 := by simpa only [dist_comm s x] using (mem_filter.mp hs).2
  have hother := near_site_others_vanish hr hz hs' (show 0 < z s by linarith) hmiddle
  have hdef : (1-z s)*mass μ (ball x (γ*r)) ≤ 512*γ/T.σ^2*innerMoment μ x γ r +
      514*mass μ (ball x (100*T.R*r) \ ball x (γ*r)) := by
    rw [← he]; exact nearWeight_deficit hr hγ hμ hg hz hmin hmiddle
  have hmove := relocate_displacement hr hγ hγL hμ hg hglip hz hmin hs' hsz hother
  refine ⟨hmiddle, s, hs', hsz, ?_, hdef, hmove, ?_⟩
  · intro i hi hip
    exact hun i (mem_filter.mpr ⟨mem_univ _, by simpa only [dist_comm x i] using hi⟩) hip
  · intro y hy
    exact near_slope_mass hr hM.le (sum_nonneg fun p _ => hμ p)
      (sum_nonneg fun p _ => mul_nonneg (hμ p) (div_nonneg dist_nonneg hr.le))
      hγ hg hglip hz hs' hy hother hdef hmove

lemma surcharge_global_by_capacity {T : Template} {r : ℝ} {g z : Y → ℝ} {x y i : Y}
    (hr : 0 < r) (hg : ∀ i, g i ∈ Set.Icc 0 1) (hz : Feasible T r z)
    (hxy : dist x y ≤ r) :
    z i*(1+g i)*(a T (dist i x/r)-a T (dist i y/r)) ≤
      (4/T.σ)*(dist x y/r)*max (z i-G T (dist i x/r)) 0 := by
  have hc : 0 ≤ (4/T.σ)*(dist x y/r) :=
    mul_nonneg (div_nonneg (by norm_num) T.σ_pos.le) (div_nonneg dist_nonneg hr.le)
  by_cases hi : dist i x/r ≤ 10*T.R
  · rw [G_eq_zero hi, sub_zero, max_eq_left (hz.1 i)]
    have hd : |a T (dist i x/r)-a T (dist i y/r)| ≤ (2/T.σ)*(dist x y/r) := by
      apply (a_lipschitz (T := T) (u := dist i x/r) (v := dist i y/r)
        (div_nonneg dist_nonneg hr.le) (div_nonneg dist_nonneg hr.le)).trans
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) T.σ_pos.le)
      have h := scaled_dist_lipschitz hr x y i
      simpa only [dist_comm i x, dist_comm i y] using h
    have h1 := mul_le_mul (show 1+g i ≤ 2 by linarith [(hg i).2]) hd (abs_nonneg _)
      (by norm_num : (0:ℝ) ≤ 2)
    have h2 := mul_le_mul_of_nonneg_left (le_abs_self (a T (dist i x/r)-a T (dist i y/r)))
      (show 0 ≤ 1+g i by linarith [(hg i).1])
    have h3 := mul_le_mul_of_nonneg_left (h2.trans h1) (hz.1 i)
    calc _ = z i*((1+g i)*(a T (dist i x/r)-a T (dist i y/r))) := by ring
         _ ≤ z i*(2*((2/T.σ)*(dist x y/r))) := h3
         _ = _ := by ring
  · have hix : 2*T.R ≤ dist i x/r := by linarith [T.R_ge]
    have hiy : 2*T.R ≤ dist i y/r := by
      apply (le_div_iff₀ hr).mpr
      have hi' := (lt_div_iff₀ hr).mp (lt_of_not_ge hi)
      have := dist_triangle i y x
      rw [dist_comm y x] at this
      have := mul_le_mul_of_nonneg_right T.R_ge hr.le
      nlinarith
    rw [a_eq_zero hix, a_eq_zero hiy, sub_self, mul_zero]
    exact mul_nonneg hc (le_max_right _ _)

lemma b_global_by_capacity {T : Template} {r : ℝ} {z : Y → ℝ} {x y i : Y}
    (hr : 0 < r) (hz : Feasible T r z) (hxy : dist x y ≤ r) :
    z i*(b T (dist i y/r)-b T (dist i x/r)) ≤
      ((dist x y/r)/T.σ)*max (z i-G T (dist i x/r)) 0 := by
  have hc : 0 ≤ (dist x y/r)/T.σ := div_nonneg (div_nonneg dist_nonneg hr.le) T.σ_pos.le
  by_cases hi : dist i x/r ≤ 10*T.R
  · rw [G_eq_zero hi, sub_zero, max_eq_left (hz.1 i)]
    have hd : |b T (dist i y/r)-b T (dist i x/r)| ≤ (dist x y/r)/T.σ := by
      apply (b_lipschitz T _ _).trans
      apply div_le_div_of_nonneg_right _ T.σ_pos.le
      have h := scaled_dist_lipschitz hr y x i
      simpa only [dist_comm i x, dist_comm i y, dist_comm y x] using h
    have h := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hd) (hz.1 i)
    simpa only [mul_comm] using h
  · have hix : 2*T.σ ≤ dist i x/r := by linarith [T.R_ge, T.σ_le]
    have hiy : 2*T.σ ≤ dist i y/r := by
      apply (le_div_iff₀ hr).mpr
      have hi' := (lt_div_iff₀ hr).mp (lt_of_not_ge hi)
      have := dist_triangle i y x
      rw [dist_comm y x] at this
      have := mul_le_mul_of_nonneg_right T.R_ge hr.le
      have := mul_le_of_le_one_left hr.le T.σ_le
      nlinarith
    rw [b_eq_zero hix, b_eq_zero hiy, sub_self, mul_zero]
    exact mul_nonneg hc (le_max_right _ _)

lemma globalConstant_ge (T : Template) : 1026 ≤ globalConstant T := by
  unfold globalConstant
  have : (1026:ℝ) ≤ 1026/T.σ := (le_div_iff₀ T.σ_pos).mpr (by nlinarith [T.σ_le])
  linarith [T.L_nonneg]

lemma integrand_diff_le {T : Template} {r : ℝ} {g z : Y → ℝ} {x y : Y}
    (hr : 0 < r) (hg : ∀ i, g i ∈ Set.Icc 0 1)
    (hglip : ∀ i j, |g i-g j| ≤ T.L*(dist i j/r)) (hz : Feasible T r z) :
    integrand T r g z x-integrand T r g z y ≤ globalConstant T*(dist x y/r) := by
  by_cases hxy : dist x y ≤ r
  · have ha := sum_le_sum (s := (univ : Finset Y)) fun i _ => surcharge_global_by_capacity (i := i) hr hg hz hxy
    rw [← mul_sum] at ha
    have ha' := ha.trans (mul_le_mul_of_nonneg_left (hz.2.1 x)
      (show 0 ≤ (4/T.σ)*(dist x y/r) from mul_nonneg (div_nonneg (by norm_num) T.σ_pos.le)
        (div_nonneg dist_nonneg hr.le)))
    rw [mul_one] at ha'
    have hb := sum_le_sum (s := (univ : Finset Y)) fun i _ => b_global_by_capacity (i := i) hr hz hxy
    rw [← mul_sum] at hb
    have hb' := hb.trans (mul_le_mul_of_nonneg_left (hz.2.1 x)
      (div_nonneg (div_nonneg dist_nonneg hr.le) T.σ_pos.le))
    rw [mul_one] at hb'
    have hby0 : 0 ≤ ∑ i, z i*b T (dist i y/r) := sum_nonneg fun i _ => mul_nonneg (hz.1 i) (b_nonneg _ _)
    have hby1 := sum_b_le_one hz y
    have hres1 : (g x-g y)*(1-∑ i, z i*b T (dist i y/r)) ≤ T.L*(dist x y/r) := by
      calc _ ≤ (T.L*(dist x y/r))*1 := mul_le_mul ((le_abs_self _).trans (hglip x y))
            (by linarith) (by linarith) (mul_nonneg T.L_nonneg (div_nonneg dist_nonneg hr.le))
           _ = _ := mul_one _
    have hres2 : (1+g x)*(∑ i, z i*(b T (dist i y/r)-b T (dist i x/r))) ≤ 2*((dist x y/r)/T.σ) := by
      calc _ ≤ (1+g x)*((dist x y/r)/T.σ) := mul_le_mul_of_nonneg_left hb' (by linarith [(hg x).1])
           _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [(hg x).2])
             (div_nonneg (div_nonneg dist_nonneg hr.le) T.σ_pos.le)
    have heb : (∑ i, z i*(b T (dist i y/r)-b T (dist i x/r))) =
        (∑ i, z i*b T (dist i y/r))-(∑ i, z i*b T (dist i x/r)) := by
      simp only [mul_sub, sum_sub_distrib]
    have hea : (∑ i, z i*(1+g i)*(a T (dist i x/r)-a T (dist i y/r))) =
        (∑ i, z i*(1+g i)*a T (dist i x/r))-(∑ i, z i*(1+g i)*a T (dist i y/r)) := by
      simp only [mul_sub, sum_sub_distrib]
    unfold integrand globalConstant
    calc _ = (g x-g y)*(1-∑ i, z i*b T (dist i y/r)) +
        (1+g x)*(∑ i, z i*(b T (dist i y/r)-b T (dist i x/r))) +
        256*(∑ i, z i*(1+g i)*(a T (dist i x/r)-a T (dist i y/r))) := by rw [heb, hea]; ring
         _ ≤ T.L*(dist x y/r)+2*((dist x y/r)/T.σ)+256*((4/T.σ)*(dist x y/r)) :=
           add_le_add (add_le_add hres1 hres2) (mul_le_mul_of_nonneg_left ha' (by norm_num))
         _ = _ := by ring
  · have hv : 1 ≤ dist x y/r := (le_div_iff₀ hr).mpr (by linarith)
    have hg0 : 0 ≤ globalConstant T := by linarith [globalConstant_ge T]
    have h := mul_le_mul_of_nonneg_left hv hg0
    linarith [(integrand_bounds hz hg x).2, (integrand_bounds hz hg y).1, globalConstant_ge T]

end KServer.Pilot


/-! Exact scale summations for pilot drift and the partition budget.
No policy or drift estimate is assumed. -/
noncomputable section
open scoped BigOperators Classical
open Finset
namespace KServer.ScaleMass

lemma capped_log {u : ℝ} (hu : 0 ≤ u) : min 1 u ≤ Real.log (1+u)/Real.log 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (le_div_iff₀ h2).mpr
  by_cases h : u ≤ 1
  · rw [min_eq_right h]
    have hc := strictConcaveOn_log_Ioi.concaveOn.2
      (show (1:ℝ) ∈ Set.Ioi 0 by norm_num) (show (2:ℝ) ∈ Set.Ioi 0 by norm_num)
      (show 0 ≤ 1-u by linarith) hu (show 1-u+u=1 by ring)
    simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at hc
    convert hc using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  · rw [min_eq_left (le_of_not_ge h), one_mul]
    exact Real.log_le_log (by norm_num) (by linarith)

/-- A p-step telescoping sum has only p boundary differences. The function is
allowed to be extended by the upper endpoint. -/
lemma shifted_sum_le (f : ℕ → ℝ) (a b : ℝ) (hf : ∀ i, f i ∈ Set.Icc a b)
    (n p : ℕ) : ∑ i ∈ range n, (f (i+p)-f i) ≤ p*(b-a) := by
  induction p with
  | zero => simp
  | succ p ih =>
    have he : (∑ i ∈ range n, (f (i+(p+1))-f i)) =
        (∑ i ∈ range n, (f (i+p)-f i)) + (f (n+p)-f p) := by
      have ht := sum_range_sub (fun i => f (i+p)) n
      simp only [zero_add, Nat.add_assoc, Nat.add_comm 1 p] at ht
      calc _ = (∑ i ∈ range n, (f (i+p)-f i)) +
          (∑ i ∈ range n, (f (i+(p+1))-f (i+p))) := by
            rw [← sum_add_distrib]; apply sum_congr rfl; intro i _; ring
           _ = _ := by rw [ht]
    rw [he, Nat.cast_add, Nat.cast_one]
    nlinarith [(hf (n+p)).2, (hf p).1]

lemma shell_log_sum {n p : ℕ} {m A : ℕ → ℝ} {k : ℝ}
    (hk : 0 < k) (hm : ∀ i, m i ∈ Set.Icc (1/2) k)
    (hA : ∀ i < n, m i ≤ A i ∧ A i ≤ m (i+p)) :
    ∑ i ∈ range n, min 1 ((A i-m i)/m i) ≤
      (p:ℝ)/Real.log 2 * Real.log (2*k) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm0 : ∀ i, 0 < m i := fun i => lt_of_lt_of_le (by norm_num) (hm i).1
  have hstep : ∀ i ∈ range n, min 1 ((A i-m i)/m i) ≤
      (Real.log (m (i+p))-Real.log (m i))/Real.log 2 := by
    intro i hi
    have hai := hA i (mem_range.mp hi)
    have h := capped_log (div_nonneg (sub_nonneg.mpr hai.1) (hm0 i).le)
    have he : 1+(A i-m i)/m i = A i/m i := by field_simp [(hm0 i).ne']; ring
    rw [he, Real.log_div (ne_of_gt ((hm0 i).trans_le hai.1)) (hm0 i).ne'] at h
    exact h.trans (div_le_div_of_nonneg_right
      (sub_le_sub_right (Real.log_le_log ((hm0 i).trans_le hai.1) hai.2) _) h2.le)
  have ht := shifted_sum_le (fun i => Real.log (m i)) (Real.log (1/2)) (Real.log k)
    (fun i => ⟨Real.log_le_log (by norm_num) (hm i).1, Real.log_le_log (hm0 i) (hm i).2⟩) n p
  have he : Real.log k-Real.log (1/2) = Real.log (2*k) := by
    rw [← Real.log_div hk.ne' (by norm_num)]; congr 1; ring
  calc _ ≤ ∑ i ∈ range n, (Real.log (m (i+p))-Real.log (m i))/Real.log 2 := sum_le_sum hstep
       _ = (∑ i ∈ range n, (Real.log (m (i+p))-Real.log (m i)))/Real.log 2 := by rw [sum_div]
       _ ≤ ((p:ℝ)*(Real.log k-Real.log (1/2)))/Real.log 2 := div_le_div_of_nonneg_right ht h2.le
       _ = _ := by rw [he]; ring

/-- Relative new mass is controlled by the logarithmic increase. -/
lemma relative_increment_le_log {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b-a)/b ≤ Real.log b-Real.log a := by
  have hb := ha.trans_le hab
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

lemma relative_increment_sum {m : ℕ → ℝ} {n : ℕ}
    (hm : ∀ i ≤ n, 0 < m i) (hmono : Monotone m) :
    1 + ∑ i ∈ range n, (m (i+1)-m i)/m (i+1) ≤
      1 + Real.log (m n/m 0) := by
  have hs := sum_le_sum (s := range n) (fun i hi =>
    relative_increment_le_log (hm i (by have := mem_range.mp hi; omega)) (hmono (by omega : i ≤ i+1)))
  rw [show (∑ i ∈ range n, (Real.log (m (i+1))-Real.log (m i))) =
    Real.log (m n)-Real.log (m 0) from sum_range_sub (fun i => Real.log (m i)) n] at hs
  rw [Real.log_div (hm n le_rfl).ne' (hm 0 (by omega)).ne']
  linarith

/-- Geometric radius sums, including every initial atom and any finite cutoff. -/
lemma geometric_weighted_sum {n : ℕ} {r : ℕ → ℝ} (hr : ∀ i < n, 0 ≤ r i)
    (hstep : ∀ i, i+1 < n → 2*r i ≤ r (i+1)) :
    ∑ i ∈ range n, r i ≤ if n=0 then 0 else 2*r (n-1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ite_eq_right (Nat.succ_ne_zero n), Nat.add_sub_cancel]
    by_cases hn : n=0
    · subst n; simp; linarith [hr 0 (by omega)]
    · have ht := ih (fun i hi => hr i (by omega)) (fun i hi => hstep i (by omega))
      rw [ite_eq_right hn] at ht
      have hd := hstep (n-1) (by omega)
      have he : n-1+1=n := by omega
      rw [he] at hd
      linarith


lemma convolution_nonneg {q : ℝ} {a : ℕ → ℝ} (hq : 0 ≤ q)
    (ha : ∀ i, 0 ≤ a i) (j : ℕ) : 0 ≤ convolution q a j :=
  sum_nonneg fun i _ => mul_nonneg (pow_nonneg hq _) (ha i)

lemma convolution_succ (q : ℝ) (a : ℕ → ℝ) (j : ℕ) :
    convolution q a (j+1) = q*convolution q a j+a (j+1) := by
  unfold convolution
  rw [sum_range_succ, mul_sum]
  simp only [Nat.sub_self, pow_zero, one_mul]
  congr 1
  apply sum_congr rfl
  intro i hi
  have he : j+1-i=(j-i)+1 := by have := mem_range.mp hi; omega
  rw [he, pow_succ]; ring

lemma convolution_sum_aux {q : ℝ} {a : ℕ → ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1/2)
    (ha : ∀ i, 0 ≤ a i) (n : ℕ) :
    (∑ j ∈ range (n+1), convolution q a j)+convolution q a n ≤
      2*∑ i ∈ range (n+1), a i := by
  induction n with
  | zero => simp [convolution]; ring_nf; exact le_rfl
  | succ n ih =>
    rw [sum_range_succ, convolution_succ, sum_range_succ (f := a)]
    have hn := convolution_nonneg hq0 ha n
    have h := mul_le_mul_of_nonneg_right hq hn
    nlinarith

lemma convolution_sum_le {q : ℝ} {a : ℕ → ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1/2)
    (ha : ∀ i, 0 ≤ a i) (n : ℕ) :
    ∑ j ∈ range n, convolution q a j ≤ 2*∑ i ∈ range n, a i := by
  cases n with
  | zero => simp
  | succ n => linarith [convolution_sum_aux hq0 hq ha n, convolution_nonneg hq0 ha n]

lemma increment_nonneg {m : ℕ → ℝ} (hm0 : 0 ≤ m 0) (hm : Monotone m) (i : ℕ) :
    0 ≤ increment m i := by
  unfold increment; split_ifs with h
  · exact hm0
  · exact sub_nonneg.mpr (hm (Nat.sub_le _ _))

lemma increment_sum_le {m : ℕ → ℝ} (hm0 : 0 < m 0) (hm : Monotone m) (n : ℕ) :
    ∑ i ∈ range (n+1), increment m i/m i ≤ 1+Real.log (m n/m 0) := by
  rw [sum_range_succ']
  simp only [increment, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
    Nat.add_sub_cancel, div_self hm0.ne']
  have h := relative_increment_sum (m := m) (n := n)
    (fun i _ => hm0.trans_le (hm (Nat.zero_le i))) hm
  linarith

/-- Exact Fubini/geometric moment estimate, encoded as a finite convolution.
The hypotheses here are the ball-layer pointwise estimate and monotone masses;
no estimate to be proved is hidden among them. -/
lemma moment_sum_le {m t : ℕ → ℝ} {q γ k : ℝ} {n : ℕ}
    (hq0 : 0 ≤ q) (hq : q ≤ 1/2) (hγ : 0 ≤ γ) (hk : 1/2 ≤ k)
    (hm0 : 1/2 ≤ m 0) (hm : Monotone m) (hmk : ∀ i < n, m i ≤ k)
    (ht : ∀ j < n, t j ≤ γ*∑ i ∈ range (j+1), q^(j-i)*increment m i/m j) :
    ∑ j ∈ range n, t j ≤ 2*γ*(1+Real.log (2*k)) := by
  have hmp : ∀ i, 0 < m i := fun i => (show (0:ℝ)<1/2 by norm_num).trans_le
    (hm0.trans (hm (Nat.zero_le i)))
  have hd : ∀ i, 0 ≤ increment m i := increment_nonneg (hmp 0).le hm
  have ha : ∀ i, 0 ≤ increment m i/m i := fun i => div_nonneg (hd i) (hmp i).le
  have hrow : ∀ j ∈ range n, t j ≤ γ*convolution q (fun i => increment m i/m i) j := by
    intro j hj
    apply (ht j (mem_range.mp hj)).trans
    apply mul_le_mul_of_nonneg_left _ hγ
    unfold convolution
    apply sum_le_sum
    intro i hi
    have hij : i ≤ j := by have := mem_range.mp hi; omega
    calc _ ≤ q^(j-i)*increment m i/m i :=
            div_le_div_of_nonneg_left (mul_nonneg (pow_nonneg hq0 _) (hd i)) (hmp i) (hm hij)
         _ = _ := by ring
  have htotal : (∑ j ∈ range n, t j) ≤ γ*(2*∑ i ∈ range n, increment m i/m i) := by
    calc _ ≤ ∑ j ∈ range n, γ*convolution q (fun i => increment m i/m i) j := sum_le_sum hrow
         _ = γ*(∑ j ∈ range n, convolution q (fun i => increment m i/m i) j) := by rw [mul_sum]
         _ ≤ _ := mul_le_mul_of_nonneg_left (convolution_sum_le hq0 hq ha n) hγ
  by_cases hn : n=0
  · subst n
    simp only [sum_range_zero]
    have hl : 0 ≤ Real.log (2*k) := Real.log_nonneg (by linarith)
    positivity
  · obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hrel := increment_sum_le (hmp 0) hm N
    have hlog : Real.log (m N/m 0) ≤ Real.log (2*k) := by
      apply Real.log_le_log (div_pos (hmp N) (hmp 0))
      apply (div_le_iff₀ (hmp 0)).mpr
      have hk' := hmk N (by omega)
      nlinarith
    have hmcoef : 0 ≤ 2*γ := by positivity
    calc _ ≤ γ*(2*∑ i ∈ range (N+1), increment m i/m i) := htotal
         _ = (2*γ)*(∑ i ∈ range (N+1), increment m i/m i) := by ring
         _ ≤ (2*γ)*(1+Real.log (2*k)) := mul_le_mul_of_nonneg_left (hrel.trans (by linarith)) hmcoef

end KServer.ScaleMass

namespace KServer.Pilot
open Finset
variable {Y : Type*} [Fintype Y] [MetricSpace Y]

lemma radius_succ (r₀ τ : ℝ) (j : ℕ) : radius r₀ τ (j+1)=τ*radius r₀ τ j := by
  unfold radius; rw [pow_succ]; ring

lemma radius_add (r₀ τ : ℝ) (i j : ℕ) : radius r₀ τ (i+j)=radius r₀ τ i*τ^j := by
  unfold radius; rw [pow_add]; ring

lemma radius_mono {r₀ τ : ℝ} (hr : 0 ≤ r₀) (hτ : 1 ≤ τ) : Monotone (radius r₀ τ) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [radius_succ]
  have hj : 0 ≤ radius r₀ τ j := mul_nonneg hr (pow_nonneg (by linarith) _)
  nlinarith

lemma ball_mono {x : Y} {r s : ℝ} (h : r ≤ s) : ball x r ⊆ ball x s := by
  intro y hy
  exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hy).2.trans h⟩

omit [Fintype Y] [MetricSpace Y] in
lemma mass_mono {μ : Y → ℝ} (hμ : ∀ y, 0 ≤ μ y) {A B : Finset Y} (h : A ⊆ B) :
    mass μ A ≤ mass μ B := sum_le_sum_of_subset_of_nonneg h (fun i _ _ => hμ i)

omit [Fintype Y] [MetricSpace Y] in
lemma mass_nonneg {μ : Y → ℝ} (hμ : ∀ y, 0 ≤ μ y) (A : Finset Y) :
    0 ≤ mass μ A := sum_nonneg fun i _ => hμ i

lemma innerMass_mono {μ : Y → ℝ} {x : Y} {γ r₀ τ : ℝ}
    (hμ : ∀ y, 0 ≤ μ y) (hγ : 0 ≤ γ) (hr : 0 ≤ r₀) (hτ : 1 ≤ τ) :
    Monotone (innerMass μ x γ r₀ τ) := by
  intro i j hij
  exact mass_mono hμ (ball_mono (mul_le_mul_of_nonneg_left (radius_mono hr hτ hij) hγ))

lemma innerMoment_step {μ : Y → ℝ} {x : Y} {γ r₀ τ : ℝ}
    (hμ : ∀ y, 0 ≤ μ y) (hγ : 0 ≤ γ) (hr : 0 < r₀) (hτ : 1 ≤ τ) (j : ℕ) :
    innerMoment μ x γ (radius r₀ τ (j+1)) ≤
      τ⁻¹*innerMoment μ x γ (radius r₀ τ j) +
        γ*(innerMass μ x γ r₀ τ (j+1)-innerMass μ x γ r₀ τ j) := by
  classical
  have hτ0 : 0 < τ := by linarith
  have hro := radius_pos hr hτ0 j
  have hrn := radius_pos hr hτ0 (j+1)
  let A := ball x (γ*radius r₀ τ j)
  let B := ball x (γ*radius r₀ τ (j+1))
  have hAB : A ⊆ B := ball_mono (mul_le_mul_of_nonneg_left (radius_mono hr.le hτ (by omega)) hγ)
  have he : innerMoment μ x γ (radius r₀ τ (j+1)) =
      (∑ p ∈ A, μ p*(dist x p/radius r₀ τ (j+1)))+
      (∑ p ∈ B\A, μ p*(dist x p/radius r₀ τ (j+1))) := by
    change (∑ p ∈ B, μ p*(dist x p/radius r₀ τ (j+1))) = _
    have hh := sum_sdiff (f := fun p => μ p*(dist x p/radius r₀ τ (j+1))) hAB
    linarith
  have hold : (∑ p ∈ A, μ p*(dist x p/radius r₀ τ (j+1))) =
      τ⁻¹*innerMoment μ x γ (radius r₀ τ j) := by
    unfold innerMoment
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    rw [radius_succ]
    field_simp
  have hnew : (∑ p ∈ B\A, μ p*(dist x p/radius r₀ τ (j+1))) ≤ γ*mass μ (B\A) := by
    unfold mass; rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hd := (mem_filter.mp (mem_sdiff.mp hp).1).2
    have hv : dist x p/radius r₀ τ (j+1) ≤ γ := (div_le_iff₀ hrn).mpr hd
    nlinarith [mul_le_mul_of_nonneg_left hv (hμ p)]
  have hm := sum_sdiff (f := μ) hAB
  change mass μ (B\A)+mass μ A=mass μ B at hm
  change _ ≤ _ + γ*(mass μ B-mass μ A)
  rw [he, hold]
  nlinarith

lemma innerMoment_convolution {μ : Y → ℝ} {x : Y} {γ r₀ τ : ℝ}
    (hμ : ∀ y, 0 ≤ μ y) (hγ : 0 ≤ γ) (hr : 0 < r₀) (hτ : 1 ≤ τ) (j : ℕ) :
    innerMoment μ x γ (radius r₀ τ j) ≤
      γ*ScaleMass.convolution τ⁻¹ (ScaleMass.increment (innerMass μ x γ r₀ τ)) j := by
  classical
  have hτ0 : 0 < τ := by linarith
  induction j with
  | zero =>
    simpa [ScaleMass.convolution, ScaleMass.increment, innerMass] using
      innerMoment_le (radius_pos hr hτ0 0) hμ (x := x) (γ := γ)
  | succ j ih =>
    calc _ ≤ τ⁻¹*innerMoment μ x γ (radius r₀ τ j)+
        γ*(innerMass μ x γ r₀ τ (j+1)-innerMass μ x γ r₀ τ j) := innerMoment_step hμ hγ hr hτ j
         _ ≤ τ⁻¹*(γ*ScaleMass.convolution τ⁻¹ (ScaleMass.increment (innerMass μ x γ r₀ τ)) j)+
        γ*(innerMass μ x γ r₀ τ (j+1)-innerMass μ x γ r₀ τ j) :=
          add_le_add (mul_le_mul_of_nonneg_left ih (inv_nonneg.mpr hτ0.le)) le_rfl
         _ = _ := by rw [ScaleMass.convolution_succ]; simp [ScaleMass.increment]; ring

/-- The moment sum for actual closed metric balls, not an interface
assuming the ball-layer estimate. It includes atoms in the first ball. -/
theorem innerMoment_scale_sum {μ : Y → ℝ} {x : Y} {γ r₀ τ k : ℝ} (n : ℕ)
    (hμ : ∀ y, 0 ≤ μ y) (hγ : 0 ≤ γ) (hr : 0 < r₀) (hτ : 2 ≤ τ)
    (hm0 : 1/2 ≤ innerMass μ x γ r₀ τ 0) (hk : ∑ y, μ y = k) :
    ∑ j ∈ range n, innerMoment μ x γ (radius r₀ τ j)/innerMass μ x γ r₀ τ j ≤
      2*γ*(1+Real.log (2*k)) := by
  have hτ0 : 0 < τ := by linarith
  have hmm := innerMass_mono (x := x) hμ hγ hr.le (show 1 ≤ τ by linarith)
  have hmp : ∀ i, 0 < innerMass μ x γ r₀ τ i := fun i =>
    (show (0:ℝ)<1/2 by norm_num).trans_le (hm0.trans (hmm (Nat.zero_le i)))
  have hmk : ∀ i, innerMass μ x γ r₀ τ i ≤ k := by
    intro i
    rw [← hk]
    exact mass_mono hμ (subset_univ _)
  apply ScaleMass.moment_sum_le (inv_nonneg.mpr hτ0.le)
    (show τ⁻¹ ≤ 1/2 by rw [inv_eq_one_div]; apply (div_le_iff₀ hτ0).mpr; linarith) hγ (hm0.trans (hmk 0)) hm0 hmm (fun i _ => hmk i)
  intro j _
  have h := div_le_div_of_nonneg_right
    (innerMoment_convolution (x := x) hμ hγ hr (show 1 ≤ τ by linarith) j) (hmp j).le
  calc _ ≤ (γ*ScaleMass.convolution τ⁻¹ (ScaleMass.increment (innerMass μ x γ r₀ τ)) j)/
      innerMass μ x γ r₀ τ j := h
       _ = _ := by unfold ScaleMass.convolution; rw [mul_div_assoc, sum_div]

/-- Shell summation for the exact closed balls. Missing coarser masses are
assigned total mass k in the telescope. -/
theorem shell_scale_sum {μ : Y → ℝ} {x : Y} {γ D r₀ τ k : ℝ} (n p : ℕ)
    (hμ : ∀ y, 0 ≤ μ y) (hγ : 0 ≤ γ) (hr : 0 < r₀) (hτ : 2 ≤ τ)
    (hD : γ ≤ D) (hp : D ≤ γ*τ^p)
    (hm0 : 1/2 ≤ innerMass μ x γ r₀ τ 0) (hk : ∑ y, μ y = k) :
    ∑ j ∈ range n, min 1 (mass μ (ball x (D*radius r₀ τ j)\
      ball x (γ*radius r₀ τ j))/innerMass μ x γ r₀ τ j) ≤
      (p:ℝ)/Real.log 2*Real.log (2*k) := by
  classical
  have hτ0 : 0 < τ := by linarith
  have hmm := innerMass_mono (x := x) hμ hγ hr.le (show 1 ≤ τ by linarith)
  have hmk : ∀ i, innerMass μ x γ r₀ τ i ≤ k := by
    intro i; rw [← hk]; exact mass_mono hμ (subset_univ _)
  have hml : ∀ i, 1/2 ≤ innerMass μ x γ r₀ τ i := fun i => hm0.trans (hmm (Nat.zero_le i))
  have hk0 : 0 < k := (show (0:ℝ)<1/2 by norm_num).trans_le (hm0.trans (hmk 0))
  let m : ℕ → ℝ := fun i => if i<n then innerMass μ x γ r₀ τ i else k
  let A : ℕ → ℝ := fun i => mass μ (ball x (D*radius r₀ τ i))
  have hm : ∀ i, m i ∈ Set.Icc (1/2) k := by
    intro i; dsimp [m]; split_ifs
    · exact ⟨hml i, hmk i⟩
    · exact ⟨hm0.trans (hmk 0), le_rfl⟩
  have hAB : ∀ i, ball x (γ*radius r₀ τ i) ⊆ ball x (D*radius r₀ τ i) :=
    fun i => ball_mono (mul_le_mul_of_nonneg_right hD (radius_pos hr hτ0 i).le)
  have hA : ∀ i < n, m i ≤ A i ∧ A i ≤ m (i+p) := by
    intro i hi
    dsimp [m, A]
    rw [ite_eq_left hi]
    refine ⟨mass_mono hμ (hAB i), ?_⟩
    split_ifs with hj
    · apply mass_mono hμ
      apply ball_mono
      rw [radius_add]
      nlinarith [mul_le_mul_of_nonneg_right hp (radius_pos hr hτ0 i).le]
    · rw [← hk]; exact mass_mono hμ (subset_univ _)
  have h := ScaleMass.shell_log_sum hk0 hm hA
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply sum_congr rfl
  intro i hi
  dsimp [m, A]
  rw [ite_eq_left (mem_range.mp hi)]
  have he := sum_sdiff (f := μ) (hAB i)
  change mass μ (ball x (D*radius r₀ τ i)\ball x (γ*radius r₀ τ i))+
    innerMass μ x γ r₀ τ i = mass μ (ball x (D*radius r₀ τ i)) at he
  have hed : mass μ (ball x (D*radius r₀ τ i)\ball x (γ*radius r₀ τ i)) =
      mass μ (ball x (D*radius r₀ τ i))-innerMass μ x γ r₀ τ i := by linarith
  rw [hed]

lemma radius_geometric {r₀ τ : ℝ} (hr : 0 ≤ r₀) (hτ : 2 ≤ τ) (j : ℕ) :
    2*radius r₀ τ j ≤ radius r₀ τ (j+1) := by
  rw [radius_succ]
  exact mul_le_mul_of_nonneg_right hτ (mul_nonneg hr (pow_nonneg (by linarith) _))

/-- Every truncated initial segment of a geometric radius sequence costs at
most twice the cutoff; there is no number-of-scales factor. -/
lemma radius_truncated_sum {r₀ τ R : ℝ} (hr : 0 ≤ r₀) (hτ : 2 ≤ τ) (hR : 0 ≤ R) (n : ℕ) :
    ∑ j ∈ range n, (if radius r₀ τ j ≤ R then radius r₀ τ j else 0) ≤ 2*R := by
  have hr0 : ∀ i, 0 ≤ radius r₀ τ i := fun i => mul_nonneg hr (pow_nonneg (by linarith) _)
  induction n with
  | zero => simp; linarith
  | succ n ih =>
    by_cases hn : radius r₀ τ n ≤ R
    · calc _ ≤ ∑ j ∈ range (n+1), radius r₀ τ j := by
            apply sum_le_sum; intro j _; split_ifs <;> simp [hr0 j]
           _ ≤ 2*radius r₀ τ n := by
            simpa using ScaleMass.geometric_weighted_sum (n := n+1) (r := radius r₀ τ)
              (fun i _ => hr0 i) (fun i _ => radius_geometric hr hτ i)
           _ ≤ _ := by linarith
    · rw [sum_range_succ, ite_eq_right hn, add_zero]; exact ih


lemma moveCost_nonneg {ν : Y → ℝ} {x : Y} (hν : ∀ y, 0 ≤ ν y) : 0 ≤ moveCost ν x :=
  sum_nonneg fun y _ => mul_nonneg (hν y) dist_nonneg

omit [MetricSpace Y] in
lemma moveMeasure_integral {μ ν F : Y → ℝ} {x : Y} (hν1 : ∑ y, ν y=1) :
    (∑ y, moveMeasure μ ν x y*F y)-(∑ y, μ y*F y) =
      ∑ y, ν y*(F x-F y) := by
  classical
  simp only [moveMeasure, add_mul, sub_mul, sum_add_distrib, sum_sub_distrib, mul_sub]
  have hδ : (∑ y, (if y=x then (1:ℝ) else 0)*F y) = F x := by
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hδ, ← sum_mul, hν1, one_mul]
  ring

lemma candidate_drift {T : Template} {r : ℝ} {μ ν g : Y → ℝ} {x : Y}
    (hν1 : ∑ y, ν y=1) :
    potential T r (moveMeasure μ ν x) g-potential T r μ g ≤
      r*∑ y, ν y*(integrand T r g (minimizer T r μ g) x-
        integrand T r g (minimizer T r μ g) y) := by
  have h := potential_le (μ := moveMeasure μ ν x) (g := g) (minimizer_spec T r μ g).1
  have he := moveMeasure_integral (F := integrand T r g (minimizer T r μ g)) (x := x) (μ := μ) hν1
  unfold objective at h
  change potential T r (moveMeasure μ ν x) g ≤ _ at h
  change _-r*(∑ y, μ y*integrand T r g (minimizer T r μ g) y) ≤ _
  calc _ ≤ r*(∑ y, moveMeasure μ ν x y*integrand T r g (minimizer T r μ g) y)-
      r*(∑ y, μ y*integrand T r g (minimizer T r μ g) y) := sub_le_sub_right h _
       _ = _ := by rw [← mul_sub, he]

lemma positive_drift_candidate {T : Template} {r : ℝ} {μ ν g : Y → ℝ} {x : Y}
    (hr : 0 ≤ r) (hν : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y=1) :
    max (potential T r (moveMeasure μ ν x) g-potential T r μ g) 0 ≤
      ∑ y, ν y*(r*max (integrand T r g (minimizer T r μ g) x-
        integrand T r g (minimizer T r μ g) y) 0) := by
  apply max_le
  · calc _ ≤ r*∑ y, ν y*(integrand T r g (minimizer T r μ g) x-
          integrand T r g (minimizer T r μ g) y) := candidate_drift hν1
         _ ≤ r*∑ y, ν y*max (integrand T r g (minimizer T r μ g) x-
          integrand T r g (minimizer T r μ g) y) 0 := by
          apply mul_le_mul_of_nonneg_left _ hr
          exact sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hν y)
         _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro y _; ring
  · exact sum_nonneg fun y _ => mul_nonneg (hν y) (mul_nonneg hr (le_max_right _ _))

lemma positive_integrand_global {T : Template} {r : ℝ} {z g : Y → ℝ}
    (hr : 0 < r) (hg : ∀ y, g y ∈ Set.Icc 0 1)
    (hglip : ∀ i j, |g i-g j| ≤ T.L*(dist i j/r)) (hz : Feasible T r z) (x y : Y) :
    r*max (integrand T r g z x-integrand T r g z y) 0 ≤ globalConstant T*dist x y := by
  have hd := integrand_diff_le (x := x) (y := y) hr hg hglip hz
  have hc0 : 0 ≤ globalConstant T := by linarith [globalConstant_ge T]
  have hb : max (integrand T r g z x-integrand T r g z y) 0 ≤ globalConstant T*(dist x y/r) :=
    max_le hd (mul_nonneg hc0 (div_nonneg dist_nonneg hr.le))
  calc _ ≤ r*(globalConstant T*(dist x y/r)) := mul_le_mul_of_nonneg_left hb hr.le
       _ = _ := by field_simp

lemma positive_integrand_bounded {T : Template} {r : ℝ} {z g : Y → ℝ}
    (hr : 0 ≤ r) (hg : ∀ y, g y ∈ Set.Icc 0 1) (hz : Feasible T r z) (x y : Y) :
    r*max (integrand T r g z x-integrand T r g z y) 0 ≤ 514*r := by
  have hb : max (integrand T r g z x-integrand T r g z y) 0 ≤ 514 :=
    max_le (by linarith [(integrand_bounds hz hg x).2, (integrand_bounds hz hg y).1]) (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hb hr]

lemma positive_integrand_local {T : Template} {r γ δ : ℝ} {μ g z : Y → ℝ} {x y : Y}
    (hr : 0 < r) (hγ0 : 0 ≤ γ) (hγ : γ ≤ T.σ/64) (hγL : T.L*γ ≤ 1)
    (hδ : δ ≤ 1/4112) (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc 0 1)
    (hglip : ∀ i j, |g i-g j| ≤ T.L*(dist i j/r))
    (hz : Feasible T r z) (hmin : IsMinOn (objective T r μ g) {w | Feasible T r w} z)
    (hM : 0 < mass μ (ball x (γ*r)))
    (hconc : mass μ (ball x (100*T.R*r)\ball x (γ*r)) ≤ δ*mass μ (ball x (γ*r)))
    (hxy : dist x y < T.σ*r/8) :
    r*max (integrand T r g z x-integrand T r g z y) 0 ≤
      localConstant T*((mass μ (ball x (100*T.R*r)\ball x (γ*r))+innerMoment μ x γ r)/
        mass μ (ball x (γ*r)))*dist x y := by
  classical
  obtain ⟨_, s, hs, hsw, hun, hdef, hdisp, hsl⟩ :=
    local_structure hr hγ0 hγ hγL hδ hμ hg hglip hz hmin hM hconc
  have h := hsl y hxy
  apply (mul_le_mul_iff_left₀ hM).mp
  calc _ = r*(max (integrand T r g z x-integrand T r g z y) 0*mass μ (ball x (γ*r))) := by ring
       _ ≤ r*(localConstant T*(mass μ (ball x (100*T.R*r)\ball x (γ*r))+
          innerMoment μ x γ r)*(dist x y/r)) := mul_le_mul_of_nonneg_left h hr.le
       _ = _ := by
          have hM' : mass μ (ball x (r*γ)) ≠ 0 := by simpa [mul_comm] using hM.ne'
          field_simp [hr.ne', hM.ne', hM']


lemma mover_innerMass_half {μ ν : Y → ℝ} {x : Y} {γ r : ℝ}
    (hν : ∀ y, 0 ≤ ν y) (hνμ : ∀ y, ν y ≤ μ y) (hν1 : ∑ y, ν y=1)
    (hγ : 0 < γ) (hr : 0 < r) (he : 2*moveCost ν x ≤ γ*r) :
    1/2 ≤ mass μ (ball x (γ*r)) := by
  classical
  have hpoint : ∀ y, (γ*r)*ν y ≤ (if y ∈ ball x (γ*r) then (γ*r)*μ y else 0)+ν y*dist x y := by
    intro y
    by_cases hy : y ∈ ball x (γ*r)
    · rw [ite_eq_left hy]
      have := mul_le_mul_of_nonneg_left (hνμ y) (mul_pos hγ hr).le
      linarith [mul_nonneg (hν y) (dist_nonneg (x := x) (y := y))]
    · rw [ite_eq_right hy, zero_add]
      have hd : γ*r ≤ dist x y := le_of_lt (by simpa [ball] using hy)
      nlinarith [mul_le_mul_of_nonneg_left hd (hν y)]
  have hs := sum_le_sum (s := univ) fun y _ => hpoint y
  rw [← mul_sum, hν1, mul_one, sum_add_distrib, ← sum_filter] at hs
  simp only [filter_mem_eq_inter, Finset.univ_inter] at hs
  rw [← mul_sum] at hs
  change γ*r ≤ (γ*r)*mass μ (ball x (γ*r))+moveCost ν x at hs
  have hp := mul_pos hγ hr
  nlinarith

lemma shellRatio_nonneg {μ : Y → ℝ} {x : Y} {γ D r : ℝ} (hμ : ∀ y, 0 ≤ μ y) :
    0 ≤ shellRatio μ x γ D r := div_nonneg (mass_nonneg hμ _) (mass_nonneg hμ _)

lemma momentRatio_nonneg {μ : Y → ℝ} {x : Y} {γ r : ℝ}
    (hμ : ∀ y, 0 ≤ μ y) (hr : 0 ≤ r) : 0 ≤ momentRatio μ x γ r :=
  div_nonneg (sum_nonneg fun p _ => mul_nonneg (hμ p) (div_nonneg dist_nonneg hr)) (mass_nonneg hμ _)

lemma slopeBudget_nonneg (T : Template) {δ h t : ℝ} (hδ : 0 ≤ δ) (hh : 0 ≤ h) (ht : 0 ≤ t) :
    0 ≤ slopeBudget T δ h t := by
  unfold slopeBudget
  have hg0 : 0 ≤ globalConstant T := by linarith [globalConstant_ge T]
  exact add_nonneg (mul_nonneg (add_nonneg (div_nonneg hg0 hδ) (localConstant_nonneg T))
    (le_min zero_le_one hh)) (mul_nonneg (localConstant_nonneg T) ht)

/-- A single estimate covers good and bad coarse radii. The exceptional far
point term is geometric and will be summed before integration. -/
lemma positive_integrand_coarse {T : Template} {r γ δ : ℝ} {μ g z : Y → ℝ} {x y : Y}
    (hr : 0 < r) (hγ0 : 0 ≤ γ) (hγ : γ ≤ T.σ/64) (hγL : T.L*γ ≤ 1)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1/4112) (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc 0 1)
    (hglip : ∀ i j, |g i-g j| ≤ T.L*(dist i j/r))
    (hz : Feasible T r z) (hmin : IsMinOn (objective T r μ g) {w | Feasible T r w} z)
    (hM : 0 < mass μ (ball x (γ*r))) :
    r*max (integrand T r g z x-integrand T r g z y) 0 ≤
      slopeBudget T δ (shellRatio μ x γ (100*T.R) r) (momentRatio μ x γ r)*dist x y +
        (if r ≤ 8*dist x y/T.σ then 514*r else 0) := by
  classical
  let h := shellRatio μ x γ (100*T.R) r
  let t := momentRatio μ x γ r
  have hh : 0 ≤ h := shellRatio_nonneg hμ
  have ht : 0 ≤ t := momentRatio_nonneg hμ hr.le
  have hF : 0 ≤ (if r ≤ 8*dist x y/T.σ then 514*r else 0) := by split_ifs <;> positivity
  have hB : 0 ≤ slopeBudget T δ h t := slopeBudget_nonneg T hδ0.le hh ht
  have hG : 0 ≤ globalConstant T := by linarith [globalConstant_ge T]
  by_cases hgood : h ≤ δ
  · have h1 : h ≤ 1 := by linarith
    have hcoeff : localConstant T*(h+t) ≤ slopeBudget T δ h t := by
      unfold slopeBudget; rw [min_eq_right h1]
      have := mul_nonneg (div_nonneg hG hδ0.le) hh
      nlinarith
    by_cases hnear : dist x y < T.σ*r/8
    · have hconc : mass μ (ball x (100*T.R*r)\ball x (γ*r)) ≤ δ*mass μ (ball x (γ*r)) := by
        exact (div_le_iff₀ hM).mp hgood
      have hl := positive_integrand_local hr hγ0 hγ hγL hδ hμ hg hglip hz hmin hM hconc hnear
      have he : (mass μ (ball x (100*T.R*r)\ball x (γ*r))+innerMoment μ x γ r)/
          mass μ (ball x (γ*r)) = h+t := by
        dsimp [h, t, shellRatio, momentRatio]; rw [add_div]
      rw [he] at hl
      exact hl.trans (le_trans (mul_le_mul_of_nonneg_right hcoeff dist_nonneg) (le_add_of_nonneg_right hF))
    · have hfar : r ≤ 8*dist x y/T.σ := (le_div_iff₀ T.σ_pos).mpr (by linarith)
      rw [ite_eq_left hfar]
      exact (positive_integrand_bounded hr.le hg hz x y).trans
        (le_add_of_nonneg_left (mul_nonneg hB dist_nonneg))
  · have hc : δ ≤ min 1 h := le_min (by linarith) (le_of_lt (lt_of_not_ge hgood))
    have hcoef : globalConstant T ≤ slopeBudget T δ h t := by
      have hbound := mul_le_mul_of_nonneg_left hc (div_nonneg hG hδ0.le)
      have he : (globalConstant T/δ)*δ=globalConstant T := by field_simp
      rw [he] at hbound
      have hmore := mul_nonneg (localConstant_nonneg T) (le_min zero_le_one hh)
      have hmoment := mul_nonneg (localConstant_nonneg T) ht
      unfold slopeBudget
      nlinarith
    exact (positive_integrand_global hr hg hglip hz x y).trans
      (le_trans (mul_le_mul_of_nonneg_right hcoef dist_nonneg) (le_add_of_nonneg_right hF))


lemma coarse_drift_sum {T : Template} {γ δ r₀ τ k : ℝ} {μ ν : Y → ℝ} {x : Y}
    (g : ℕ → Y → ℝ) (n p : ℕ)
    (hr : 0 < r₀) (hτ : 2 ≤ τ) (hγ0 : 0 < γ) (hγ : γ ≤ T.σ/64)
    (hγL : T.L*γ ≤ 1) (hδ0 : 0 < δ) (hδ : δ ≤ 1/4112)
    (hpow : 100*T.R ≤ γ*τ^p)
    (hμ : ∀ y, 0 ≤ μ y) (hν : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y=1)
    (hm0 : 1/2 ≤ innerMass μ x γ r₀ τ 0) (hk : ∑ y, μ y=k)
    (hg : ∀ j<n, ∀ y, g j y ∈ Set.Icc 0 1)
    (hgLip : ∀ j<n, ∀ y z, |g j y-g j z| ≤ T.L*(dist y z/radius r₀ τ j)) :
    ∑ j ∈ range n, max (potential T (radius r₀ τ j) (moveMeasure μ ν x) (g j)-
      potential T (radius r₀ τ j) μ (g j)) 0 ≤ coarseBudget T γ δ k p*moveCost ν x := by
  classical
  let B : ℕ → ℝ := fun j => slopeBudget T δ
    (shellRatio μ x γ (100*T.R) (radius r₀ τ j)) (momentRatio μ x γ (radius r₀ τ j))
  have hτ0 : 0 < τ := by linarith
  have hD : γ ≤ 100*T.R := by linarith [T.R_ge, T.σ_le]
  have hM : ∀ j, 0 < mass μ (ball x (γ*radius r₀ τ j)) := fun j =>
    (show (0:ℝ)<1/2 by norm_num).trans_le
      (hm0.trans (innerMass_mono (x := x) hμ hγ0.le hr.le (by linarith) (Nat.zero_le j)))
  have hB : ∑ j ∈ range n, B j ≤
      (globalConstant T/δ+localConstant T)*((p:ℝ)/Real.log 2*Real.log (2*k))+
        localConstant T*(2*γ*(1+Real.log (2*k))) := by
    simp only [B, slopeBudget, sum_add_distrib, ← mul_sum]
    exact add_le_add (mul_le_mul_of_nonneg_left
      (shell_scale_sum (x := x) n p hμ hγ0.le hr hτ hD hpow hm0 hk)
      (add_nonneg (div_nonneg (by linarith [globalConstant_ge T]) hδ0.le) (localConstant_nonneg T)))
      (mul_le_mul_of_nonneg_left (innerMoment_scale_sum (x := x) n hμ hγ0.le hr hτ hm0 hk)
        (localConstant_nonneg T))
  have hFar : ∀ y, ∑ j ∈ range n, (if radius r₀ τ j ≤ 8*dist x y/T.σ then 514*radius r₀ τ j else 0) ≤
      (8224/T.σ)*dist x y := by
    intro y
    have he : (∑ j ∈ range n, (if radius r₀ τ j ≤ 8*dist x y/T.σ then 514*radius r₀ τ j else 0)) =
        514*∑ j ∈ range n, (if radius r₀ τ j ≤ 8*dist x y/T.σ then radius r₀ τ j else 0) := by
      rw [mul_sum]; apply sum_congr rfl; intro j _; split_ifs <;> ring
    rw [he]
    calc _ ≤ 514*(2*(8*dist x y/T.σ)) := mul_le_mul_of_nonneg_left
            (radius_truncated_sum hr.le hτ (div_nonneg (mul_nonneg (by norm_num) dist_nonneg) T.σ_pos.le) n) (by norm_num)
         _ = _ := by ring
  calc _ ≤ ∑ j ∈ range n, ∑ y, ν y*(B j*dist x y+
      (if radius r₀ τ j ≤ 8*dist x y/T.σ then 514*radius r₀ τ j else 0)) := by
        apply sum_le_sum; intro j hj
        have hjn := mem_range.mp hj
        apply (positive_drift_candidate (radius_pos hr hτ0 j).le hν hν1).trans
        apply sum_le_sum; intro y _
        apply mul_le_mul_of_nonneg_left _ (hν y)
        exact positive_integrand_coarse (radius_pos hr hτ0 j) hγ0.le hγ hγL hδ0 hδ hμ
          (hg j hjn) (hgLip j hjn) (minimizer_spec T (radius r₀ τ j) μ (g j)).1
          (minimizer_spec T (radius r₀ τ j) μ (g j)).2 (hM j)
       _ = ∑ y, ν y*((∑ j ∈ range n, B j)*dist x y+
          ∑ j ∈ range n, (if radius r₀ τ j ≤ 8*dist x y/T.σ then 514*radius r₀ τ j else 0)) := by
        rw [sum_comm]; apply sum_congr rfl; intro y _
        rw [← mul_sum, sum_add_distrib, sum_mul]
       _ ≤ ∑ y, ν y*(coarseBudget T γ δ k p*dist x y) := by
        apply sum_le_sum; intro y _
        apply mul_le_mul_of_nonneg_left _ (hν y)
        calc _ ≤ ((globalConstant T/δ+localConstant T)*((p:ℝ)/Real.log 2*Real.log (2*k))+
            localConstant T*(2*γ*(1+Real.log (2*k))))*dist x y+(8224/T.σ)*dist x y :=
              add_le_add (mul_le_mul_of_nonneg_right hB dist_nonneg) (hFar y)
             _ = _ := by unfold coarseBudget; ring
       _ = _ := by unfold moveCost; rw [mul_sum]; apply sum_congr rfl; intro y _; ring

lemma radius_shift (r₀ τ : ℝ) (m j : ℕ) : radius r₀ τ (m+j)=radius (radius r₀ τ m) τ j := by
  simp only [radius, pow_add]; ring

lemma positive_drift_bounded {T : Template} {r : ℝ} {μ ν g : Y → ℝ} {x : Y}
    (hr : 0 ≤ r) (hν : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y=1)
    (hg : ∀ y, g y ∈ Set.Icc 0 1) :
    max (potential T r (moveMeasure μ ν x) g-potential T r μ g) 0 ≤ 514*r := by
  calc _ ≤ ∑ y, ν y*(r*max (integrand T r g (minimizer T r μ g) x-
        integrand T r g (minimizer T r μ g) y) 0) := positive_drift_candidate hr hν hν1
       _ ≤ ∑ y, ν y*(514*r) := sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
          (positive_integrand_bounded hr hg (minimizer_spec T r μ g).1 x y) (hν y)
       _ = _ := by rw [← sum_mul, hν1, one_mul]

/-- Full positive drift sum, with the actual minimizer at each scale. The
ascending order is just a reversal of the finite geometric scale list. -/
theorem drift_sum {T : Template} {γ δ r₀ τ k : ℝ} {μ ν : Y → ℝ} {x : Y}
    (g : ℕ → Y → ℝ) (n p : ℕ)
    (hr : 0 < r₀) (hτ : 2 ≤ τ) (hγ0 : 0 < γ) (hγ : γ ≤ T.σ/64)
    (hγL : T.L*γ ≤ 1) (hδ0 : 0 < δ) (hδ : δ ≤ 1/4112)
    (hpow : 100*T.R ≤ γ*τ^p)
    (hμ : ∀ y, 0 ≤ μ y) (hν : ∀ y, 0 ≤ ν y) (hνμ : ∀ y, ν y ≤ μ y)
    (hν1 : ∑ y, ν y=1) (hk : ∑ y, μ y=k)
    (hg : ∀ j<n, ∀ y, g j y ∈ Set.Icc 0 1)
    (hgLip : ∀ j<n, ∀ y z, |g j y-g j z| ≤ T.L*(dist y z/radius r₀ τ j)) :
    ∑ j ∈ range n, max (potential T (radius r₀ τ j) (moveMeasure μ ν x) (g j)-
      potential T (radius r₀ τ j) μ (g j)) 0 ≤
        (2056/γ+coarseBudget T γ δ k p)*moveCost ν x := by
  classical
  let e := moveCost ν x
  have he : 0 ≤ e := moveCost_nonneg hν
  have hτ0 : 0 < τ := by linarith
  let hE : ∃ m, m=n ∨ 2*e ≤ γ*radius r₀ τ m := ⟨n, Or.inl rfl⟩
  let m := Nat.find hE
  have hmn : m ≤ n := Nat.find_min' hE (Or.inl rfl)
  have hsmall : ∀ j < m, radius r₀ τ j ≤ 2*e/γ := by
    intro j hj
    have h := Nat.find_min hE hj
    have hn : ¬ 2*e ≤ γ*radius r₀ τ j := fun he => h (Or.inr he)
    apply (le_div_iff₀ hγ0).mpr
    linarith
  let Δ := fun j => max (potential T (radius r₀ τ j) (moveMeasure μ ν x) (g j)-
      potential T (radius r₀ τ j) μ (g j)) 0
  have hfine : ∑ j ∈ range m, Δ j ≤ (2056/γ)*e := by
    calc _ ≤ 514*∑ j ∈ range m, (if radius r₀ τ j ≤ 2*e/γ then radius r₀ τ j else 0) := by
          rw [mul_sum]; apply sum_le_sum; intro j hj
          rw [ite_eq_left (hsmall j (mem_range.mp hj))]
          exact positive_drift_bounded (radius_pos hr hτ0 j).le hν hν1
            (hg j ((mem_range.mp hj).trans_le hmn))
         _ ≤ 514*(2*(2*e/γ)) := mul_le_mul_of_nonneg_left
            (radius_truncated_sum hr.le hτ (div_nonneg (by linarith) hγ0.le) m) (by norm_num)
         _ = _ := by ring
  have hcoarse : ∑ j ∈ range (n-m), Δ (m+j) ≤ coarseBudget T γ δ k p*e := by
    by_cases hm : m=n
    · rw [hm, Nat.sub_self]
      simp only [range_zero, sum_empty]
      have hkhalf : 1/2 ≤ k := by
        have h := sum_le_sum (s := univ) fun y _ => hνμ y
        rw [hν1, hk] at h
        linarith
      have hlog : 0 ≤ Real.log (2*k) := Real.log_nonneg (by linarith)
      have hG : 0 ≤ globalConstant T := by linarith [globalConstant_ge T]
      have hC := localConstant_nonneg T
      have hσ := T.σ_pos
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      exact mul_nonneg (by unfold coarseBudget; positivity) he
    · have hecut : 2*e ≤ γ*radius r₀ τ m := (Nat.find_spec hE).resolve_left hm
      have hmass : 1/2 ≤ innerMass μ x γ (radius r₀ τ m) τ 0 := by
        simpa [innerMass, radius] using mover_innerMass_half hν hνμ hν1 hγ0 (radius_pos hr hτ0 m) hecut
      have h := coarse_drift_sum (x := x) (fun j => g (m+j)) (n-m) p (radius_pos hr hτ0 m)
        hτ hγ0 hγ hγL hδ0 hδ hpow hμ hν hν1 hmass hk
        (fun j hj => hg (m+j) (by omega))
        (fun j hj => by simpa [radius_shift] using hgLip (m+j) (by omega))
      simpa [Δ, e, radius_shift] using h
  have hnm : n=m+(n-m) := by omega
  change ∑ j ∈ range n, Δ j ≤ _
  conv_lhs => rw [hnm, sum_range_add]
  calc _ ≤ (2056/γ)*e+coarseBudget T γ δ k p*e := add_le_add hfine hcoarse
       _ = _ := by ring


lemma driftConstant_nonneg (T : Template) {γ δ : ℝ} (p : ℕ) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) :
    0 ≤ driftConstant T γ δ p := by
  have hG : 0 ≤ globalConstant T := by linarith [globalConstant_ge T]
  have hC := localConstant_nonneg T
  have hσ := T.σ_pos
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold driftConstant
  positivity

lemma log_k_bound {k : ℝ} (hk : 1 ≤ k) :
    0 ≤ Real.log (k+1) ∧ 1+Real.log (2*k) ≤ 2*(1+Real.log (k+1)) := by
  have hk0 : 0 < k := by linarith
  have hl := Real.log_nonneg (show 1 ≤ k+1 by linarith)
  have hlog := Real.log_le_log hk0 (show k ≤ k+1 by linarith)
  have hl2 := Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hk0.ne']
  exact ⟨hl, by linarith⟩

lemma driftBudget_le {T : Template} {γ δ k : ℝ} (p : ℕ)
    (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hk : 1 ≤ k) :
    2056/γ+coarseBudget T γ δ k p ≤ driftConstant T γ δ p*(1+Real.log (k+1)) := by
  have hG : 0 ≤ globalConstant T := by linarith [globalConstant_ge T]
  have hC := localConstant_nonneg T
  have hσ := T.σ_pos
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := log_k_bound hk
  have hbase : 2056/γ+8224/T.σ ≤ (2056/γ+8224/T.σ)*(1+Real.log (k+1)) := by
    have he : 0 ≤ 2056/γ+8224/T.σ := by positivity
    nlinarith [mul_nonneg he hlog.1]
  have hs : (globalConstant T/δ+localConstant T)*((p:ℝ)/Real.log 2*Real.log (2*k)) ≤
      ((globalConstant T/δ+localConstant T)*((p:ℝ)/Real.log 2))*(2*(1+Real.log (k+1))) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left (by linarith [hlog.2]) (by positivity)
  have ht : localConstant T*(2*γ*(1+Real.log (2*k))) ≤
      (localConstant T*(2*γ))*(2*(1+Real.log (k+1))) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left hlog.2 (by positivity)
  unfold coarseBudget driftConstant
  calc _ ≤ (2056/γ+8224/T.σ)*(1+Real.log (k+1))+
      ((globalConstant T/δ+localConstant T)*((p:ℝ)/Real.log 2))*(2*(1+Real.log (k+1)))+
        (localConstant T*(2*γ))*(2*(1+Real.log (k+1))) := by linarith
       _ = _ := by ring

/-- Section06's drift inequality with the stated dimension-free constant.
The sole scale parameter p only needs the displayed fixed geometric offset. -/
theorem pilot_drift {T : Template} {γ δ r₀ τ k : ℝ} {μ ν : Y → ℝ} {x : Y}
    (g : ℕ → Y → ℝ) (n p : ℕ)
    (hr : 0 < r₀) (hτ : 2 ≤ τ) (hγ0 : 0 < γ)
    (hγ : γ ≤ min (T.σ/64) (1/(1+T.L))) (hδ0 : 0 < δ) (hδ : δ ≤ 1/4112)
    (hpow : 100*T.R ≤ γ*(2:ℝ)^p)
    (hμ : ∀ y, 0 ≤ μ y) (hν : ∀ y, 0 ≤ ν y) (hνμ : ∀ y, ν y ≤ μ y)
    (hν1 : ∑ y, ν y=1) (hk : ∑ y, μ y=k)
    (hg : ∀ j<n, ∀ y, g j y ∈ Set.Icc 0 1)
    (hgLip : ∀ j<n, ∀ y z, |g j y-g j z| ≤ T.L*(dist y z/radius r₀ τ j)) :
    ∑ j ∈ range n, max (potential T (radius r₀ τ j) (moveMeasure μ ν x) (g j)-
      potential T (radius r₀ τ j) μ (g j)) 0 ≤
        driftConstant T γ δ p*(1+Real.log (k+1))*moveCost ν x := by
  have hk1 : 1 ≤ k := by
    have h := sum_le_sum (s := univ) fun y _ => hνμ y
    rwa [hν1, hk] at h
  have hγL : T.L*γ ≤ 1 := by
    have h := (le_div_iff₀ (show 0<1+T.L by linarith [T.L_nonneg])).mp (le_min_iff.mp hγ).2
    nlinarith
  have hpow' : 100*T.R ≤ γ*τ^p := hpow.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by norm_num) hτ p) hγ0.le)
  exact (drift_sum g n p hr hτ hγ0 (le_min_iff.mp hγ).1 hγL hδ0 hδ hpow'
    hμ hν hνμ hν1 hk hg hgLip).trans (mul_le_mul_of_nonneg_right
      (driftBudget_le p hγ0.le hδ0.le hk1) (moveCost_nonneg hν))

end KServer.Pilot

end
end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Partitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset Set

namespace KServer.Pilot
open RankTracking PosteriorRanks
variable {Ω Y : Type*} [Fintype Ω] [Fintype Y] [MetricSpace Y]

/-- Exact filtering for a profile chosen from the old observation history.
The old compact minimizer is a single admissible competitor on each old fiber. -/
lemma filtered_potential (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (H H' : Ω → ℕ) (hr : ∀ ω ν, H' ω = H' ν → H ω = H ν)
    (T : Template) (r : ℝ) (f g : Ω → Y → ℝ)
    (hg : ∀ y, Adapted H (fun ω => g ω y)) :
    avg w (fun ω => potential T r (fun y => posterior w H' (fun ν => f ν y) ω) (g ω)) ≤
      avg w (fun ω => potential T r (fun y => posterior w H (fun ν => f ν y) ω) (g ω)) := by
  let z : Ω → Y → ℝ := fun ω =>
    minimizer T r (fun y => posterior w H (fun ν => f ν y) ω) (g ω)
  have hz ω : Feasible T r (z ω) := (minimizer_spec _ _ _ _).1
  have hza : ∀ y, Adapted H (fun ω => z ω y) := by
    intro y ω ν h
    have hμ : (fun y => posterior w H (fun ν => f ν y) ω) =
        (fun y => posterior w H (fun ν => f ν y) ν) := by
      funext y
      exact posterior_adapted w H (fun ν => f ν y) ω ν h
    have hg' : g ω = g ν := funext fun y => hg y ω ν h
    simp only [z, hμ, hg']
  have hc y : Adapted H (fun ω => integrand T r (g ω) (z ω) y) := by
    intro ω ν h
    have hg' : g ω = g ν := funext fun y => hg y ω ν h
    have hz' : z ω = z ν := funext fun y => hza y ω ν h
    dsimp only
    rw [hg', hz']
  calc
    _ ≤ avg w (fun ω => objective T r
        (fun y => posterior w H' (fun ν => f ν y) ω) (g ω) (z ω)) :=
      avg_mono hw fun ω => potential_le (hz ω)
    _ = avg w (fun ω => objective T r
        (fun y => posterior w H (fun ν => f ν y) ω) (g ω) (z ω)) := by
      simp only [objective, avg, mul_sum]
      rw [sum_comm, sum_comm (f := fun ω y =>
        w ω * (r * (posterior w H (fun ν => f ν y) ω * integrand T r (g ω) (z ω) y)))]
      apply sum_congr rfl
      intro y _
      have he := (weighted_posterior hw H' (fun ν => f ν y)
        (fun ω => integrand T r (g ω) (z ω) y)
        (fun ω ν h => hc y ω ν (hr ω ν h))).trans
        (weighted_posterior hw H (fun ν => f ν y)
          (fun ω => integrand T r (g ω) (z ω) y) (hc y)).symm
      have he' := congrArg (r * ·) he
      simpa only [avg, mul_sum, mul_assoc, mul_comm, mul_left_comm] using he'
    _ = _ := rfl

end KServer.Pilot

namespace KServer.FiniteExperiment
open RankTracking PosteriorRanks Pilot
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [MetricSpace Y] [Fintype Y]
variable {k H : ℕ} [NeZero k]

omit [MetricSpace Y] in
lemma requestHistory_refines (t : ℕ) (σ ρ : Fin H → Y)
    (h : requestHistory (t+1) σ = requestHistory (t+1) ρ) :
    requestHistory t σ = requestHistory t ρ := by
  apply (requestHistory_eq_iff t σ ρ).mpr
  funext i
  have hh := congrFun ((requestHistory_eq_iff (t+1) σ ρ).mp h) i
  unfold requestPrefix at *
  by_cases hi : i.val < t
  · simpa [hi, show i.val < t+1 by omega] using hh
  · simp [hi]

/-- The precise signed filtering contribution of the actual hidden optimum. -/
lemma pilot_filtering (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (T : Pilot.Template) (r : ℝ) (t : Fin H) (g : (Fin H → Y) → Y → ℝ)
    (hg : ∀ y, Adapted (requestHistory t.val) (fun σ => g σ y)) :
    avg law.val (fun σ => potential T r (muBefore s law t σ) (g σ)) ≤
      avg law.val (fun σ => potential T r (mu s law t.val σ) (g σ)) :=
  filtered_potential law.val law.property.1 (requestHistory t.val)
    (requestHistory (t.val+1)) (requestHistory_refines t.val) T r
    (fun σ => metricCount (hidden s σ t.val)) g hg

/-- Each realized physical update obeys the literal compact-pilot drift bound. -/
lemma pilot_physical (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (T : Pilot.Template) {γ δ r₀ τ : ℝ} (t : Fin H) (σ : Fin H → Y)
    (g : ℕ → Y → ℝ) (n p : ℕ) (hσ : 0 < law.val σ)
    (hr : 0 < r₀) (hτ : 2 ≤ τ) (hγ0 : 0 < γ)
    (hγ : γ ≤ min (T.σ/64) (1/(1+T.L))) (hδ0 : 0 < δ) (hδ : δ ≤ 1/4112)
    (hpow : 100*T.R ≤ γ*(2:ℝ)^p)
    (hg : ∀ j<n, ∀ y, g j y ∈ Set.Icc 0 1)
    (hgLip : ∀ j<n, ∀ y z, |g j y-g j z| ≤ T.L*(dist y z/radius r₀ τ j)) :
    ∑ j ∈ range n, max (potential T (radius r₀ τ j) (mu s law (t.val+1) σ) (g j)-
      potential T (radius r₀ τ j) (muBefore s law t σ) (g j)) 0 ≤
        driftConstant T γ δ p*(1+Real.log ((k:ℝ)+1)) *
          ∑ y, nu s law t σ y * dist y (σ t) := by
  have he : mu s law (t.val+1) σ =
      moveMeasure (muBefore s law t σ) (nu s law t σ) (σ t) := by
    funext y
    simpa only [moveMeasure, eq_comm] using mu_move s law t σ hσ y
  rw [he]
  simpa only [moveCost, dist_comm] using pilot_drift (x := σ t) g n p hr hτ hγ0 hγ hδ0 hδ hpow
    (muBefore_nonneg s law t σ) (nu_nonneg s law t σ) (nu_le_muBefore s law t σ)
    (nu_total s law t σ hσ) (muBefore_total s law t σ hσ) hg hgLip

end KServer.FiniteExperiment

namespace KServer.FiniteExperiment
open RankTracking PosteriorRanks Pilot
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [MetricSpace Y] [Fintype Y]
variable {k H : ℕ} [NeZero k]

/-- The actual expected physical pilot increments are paid entirely by OPT. -/
theorem pilot_physical_budget (s : Configuration k Y)
    (law : FiniteDistribution (Fin H → Y)) (T : Pilot.Template)
    {γ δ r₀ τ : ℝ} (g : Fin H → (Fin H → Y) → ℕ → Y → ℝ) (n p : ℕ)
    (hr : 0 < r₀) (hτ : 2 ≤ τ) (hγ0 : 0 < γ)
    (hγ : γ ≤ min (T.σ/64) (1/(1+T.L))) (hδ0 : 0 < δ) (hδ : δ ≤ 1/4112)
    (hpow : 100*T.R ≤ γ*(2:ℝ)^p)
    (hg : ∀ t σ j, j<n → ∀ y, g t σ j y ∈ Set.Icc 0 1)
    (hgLip : ∀ t σ j, j<n → ∀ y z,
      |g t σ j y-g t σ j z| ≤ T.L*(dist y z/radius r₀ τ j)) :
    (∑ t : Fin H, avg law.val (fun σ => ∑ j ∈ range n,
      max (potential T (radius r₀ τ j) (mu s law (t.val+1) σ) (g t σ j)-
        potential T (radius r₀ τ j) (muBefore s law t σ) (g t σ j)) 0)) ≤
      driftConstant T γ δ p * (1+Real.log ((k:ℝ)+1)) *
        ∑ σ,law.val σ*optimalCost s (List.ofFn σ) := by
  calc
    _ ≤ ∑ t : Fin H, ∑ σ, law.val σ *
        (driftConstant T γ δ p * (1+Real.log ((k:ℝ)+1)) *
          ∑ y,nu s law t σ y*dist y (σ t)) := by
      apply sum_le_sum
      intro t _
      apply sum_le_sum
      intro σ _
      by_cases hσ : 0 < law.val σ
      · exact mul_le_mul_of_nonneg_left
          (pilot_physical s law T t σ (g t σ) n p hσ hr hτ hγ0 hγ hδ0 hδ hpow
            (hg t σ) (hgLip t σ)) (law.property.1 σ)
      · have hzero : law.val σ=0 := le_antisymm (le_of_not_gt hσ) (law.property.1 σ)
        simp [hzero]
    _ = _ := by
      simp only [mul_left_comm (law.val _) (driftConstant T γ δ p * (1+Real.log ((k:ℝ)+1))),
        ←mul_sum]
      rw [expected_moveCost]

/-- All-step signed filtering plus physical drift, before any decision to edit.
The edit charge is the literal difference of two achieved pilot minima. -/
theorem pilot_edit_budget (s : Configuration k Y)
    (law : FiniteDistribution (Fin H → Y)) (T : Pilot.Template)
    {γ δ r₀ τ : ℝ} (g : ℕ → (Fin H → Y) → ℕ → Y → ℝ) (n p : ℕ)
    (hr : 0 < r₀) (hτ : 2 ≤ τ) (hγ0 : 0 < γ)
    (hγ : γ ≤ min (T.σ/64) (1/(1+T.L))) (hδ0 : 0 < δ) (hδ : δ ≤ 1/4112)
    (hpow : 100*T.R ≤ γ*(2:ℝ)^p)
    (hg : ∀ t σ j, j<n → ∀ y, g t σ j y ∈ Set.Icc 0 1)
    (hgLip : ∀ t σ j, j<n → ∀ y z,
      |g t σ j y-g t σ j z| ≤ T.L*(dist y z/radius r₀ τ j))
    (hga : ∀ t j, j<n → ∀ y,
      Adapted (requestHistory t) (fun σ => g t σ j y)) :
    (∑ t : Fin H, avg law.val (fun σ => ∑ j ∈ range n,
      (potential T (radius r₀ τ j) (mu s law (t.val+1) σ) (g t.val σ j)-
        potential T (radius r₀ τ j) (mu s law (t.val+1) σ) (g (t.val+1) σ j)))) ≤
      driftConstant T γ δ p * (1+Real.log ((k:ℝ)+1)) *
        ∑ σ,law.val σ*optimalCost s (List.ofFn σ) +
          ∑ j ∈ range n,2 * radius r₀ τ j * (k:ℝ) := by
  let V : ℕ → ℝ := fun t =>
    ∑ j ∈ range n,avg law.val (fun σ => potential T (radius r₀ τ j) (mu s law t σ) (g t σ j))
  let D : Fin H → ℝ := fun t => avg law.val (fun σ => ∑ j ∈ range n,
    max (potential T (radius r₀ τ j) (mu s law (t.val+1) σ) (g t.val σ j)-
      potential T (radius r₀ τ j) (muBefore s law t σ) (g t.val σ j)) 0)
  have hstep (t : Fin H) :
      avg law.val (fun σ => ∑ j ∈ range n,
        (potential T (radius r₀ τ j) (mu s law (t.val+1) σ) (g t.val σ j)-
          potential T (radius r₀ τ j) (mu s law (t.val+1) σ) (g (t.val+1) σ j))) ≤
        V t.val-V (t.val+1)+D t := by
    have hfilter := sum_le_sum (s := range n) fun j hj =>
      pilot_filtering s law T (radius r₀ τ j) t (fun σ => g t.val σ j)
        (hga t.val j (mem_range.mp hj))
    have hpoint := avg_mono law.property.1 (fun σ =>
      sum_le_sum (s := range n) fun j _ => le_max_left
        (potential T (radius r₀ τ j) (mu s law (t.val+1) σ) (g t.val σ j)-
         potential T (radius r₀ τ j) (muBefore s law t σ) (g t.val σ j)) 0)
    have avgsum (f : ℕ → (Fin H → Y) → ℝ) :
        avg law.val (fun σ => ∑ j ∈ range n,f j σ)=∑ j ∈ range n,avg law.val (f j) := by
      unfold avg
      simp only [mul_sum]
      rw [sum_comm]
    dsimp only [V,D] at *
    simp only [avgsum, avg_sub, sum_sub_distrib] at hpoint ⊢
    linarith
  have hVnonneg : 0 ≤ V H := by
    apply sum_nonneg
    intro j hj
    exact sum_nonneg fun σ _ => mul_nonneg (law.property.1 σ)
      (potential_bounds (radius_pos hr (by linarith) j).le (mu_nonneg s law H σ)
        (hg H σ j (mem_range.mp hj))).1
  have hVupper : V 0 ≤ ∑ j ∈ range n,2 * radius r₀ τ j * (k:ℝ) := by
    apply sum_le_sum
    intro j hj
    calc
      _ ≤ avg law.val (fun _ => 2 * radius r₀ τ j * (k:ℝ)) := by
        apply sum_le_sum
        intro σ _
        by_cases hσ : 0 < law.val σ
        · exact mul_le_mul_of_nonneg_left
            (by simpa only [mu_total s law 0 σ hσ] using
              (potential_bounds (radius_pos hr (by linarith) j).le (mu_nonneg s law 0 σ)
                (hg 0 σ j (mem_range.mp hj))).2) (law.property.1 σ)
        · have hz : law.val σ=0 := le_antisymm (le_of_not_gt hσ) (law.property.1 σ)
          simp [hz]
      _ = _ := avg_const _ law.property.2 _
  have hD := pilot_physical_budget s law T (fun t σ => g t.val σ) n p
    hr hτ hγ0 hγ hδ0 hδ hpow (fun t => hg t.val) (fun t => hgLip t.val)
  have hsum := sum_le_sum (s := (univ : Finset (Fin H))) (fun t _ => hstep t)
  have htelescope : (∑ t : Fin H,(V t.val-V (t.val+1)))=V 0-V H := by
    rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => V t-V (t+1)),Finset.sum_range_sub']
  rw [sum_add_distrib,htelescope] at hsum
  dsimp only [D] at hsum
  linarith

end KServer.FiniteExperiment

end


noncomputable section
open scoped BigOperators
open Finset Set
namespace KServer.HeavyCenters
open Pilot
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [MetricSpace Y] [Fintype Y]

lemma annulus_bump_one {r : ℝ} (hr : 0 < r) {x s p : Y}
    (hs : dist s x < r/4) (hp : p∈annulus x r) :
    Pilot.a template (dist s p/r)=1 := by
  have hp' := (mem_filter.mp hp).2
  have hlo : 1 ≤ dist s p/r := by
    apply (le_div_iff₀ hr).mpr
    have ht := dist_triangle x s p
    rw [dist_comm x s] at ht
    linarith
  have hhi : dist s p/r ≤ 512 := by
    apply (div_le_iff₀ hr).mpr
    have ht := dist_triangle s x p
    linarith
  simp only [Pilot.a,template,ite_eq_left hhi,one_pow,div_one]
  exact min_eq_right (by nlinarith)

omit [Fintype Y] in
lemma profile_weight_nonneg {r : ℝ} (hr : 0 < r) (C : Finset Y) (x : Y)
    {z : Y → ℝ} (hz : ∀ i,0≤z i)
    (hmiddle : ∀ i,r/4 ≤ dist i x → dist i x ≤ 256*r → z i=0) (i : Y) :
    0 ≤ z i*(profile r C i-profile r (replace r C x) i) := by
  by_cases h : profile r (replace r C x) i ≤ profile r C i
  · exact mul_nonneg (hz i) (sub_nonneg.mpr h)
  · have hs := profile_increase_support hr C x i (lt_of_not_ge h)
    have hi : z i=0 := hmiddle i (by rw [dist_comm]; linarith)
      (by rw [dist_comm]; linarith)
    rw [hi,zero_mul]

lemma profile_residual_bound {r : ℝ} (hr : 0 < r) (C : Finset Y) (x p : Y)
    {R : ℝ} (hR : R∈Set.Icc 0 1) :
    -(if p∈annulus x r then (1:ℝ) else 0) ≤
      (profile r C p-profile r (replace r C x) p)*R := by
  by_cases hp : p∈annulus x r
  · rw [ite_eq_left hp]
    have hm := mul_nonneg
      (show 0 ≤ profile r C p-profile r (replace r C x) p+1 by
        linarith [profile_nonneg r C p,profile_le_one r (replace r C x) p]) hR.1
    nlinarith [hR.2]
  · rw [ite_eq_right hp,neg_zero]
    apply mul_nonneg _ hR.1
    by_contra hn
    have hs := profile_increase_support hr C x p (by linarith)
    apply hp
    exact mem_filter.mpr ⟨mem_univ _,hs.1,by linarith [hs.2]⟩

/-- Pointwise objective decrease from the literal center replacement. -/
lemma edit_integrand_drop {r : ℝ} (hr : 0 < r) (C : Finset Y) (x : Y)
    {z : Y → ℝ} (hz : Feasible template r z)
    (hfar : ∀ a∈C,8*r<dist a x)
    (hmiddle : ∀ i,r/4 ≤ dist i x → dist i x ≤ 256*r → z i=0)
    (hnear : ∃ s,dist s x < r/4 ∧ (1/2:ℝ) ≤ z s) (p : Y) :
    127*(if p∈annulus x r then (1:ℝ) else 0) ≤
      integrand template r (profile r C) z p-
        integrand template r (profile r (replace r C x)) z p := by
  obtain ⟨s,hs,hsz⟩ := hnear
  let R := 1-∑ i,z i*Pilot.b template (dist i p/r)
  have hR : R∈Set.Icc 0 1 := by
    constructor
    · exact sub_nonneg.mpr (sum_b_le_one hz p)
    · have hn := sum_nonneg (s := (univ : Finset Y))
        (fun i _ => mul_nonneg (hz.1 i) (Pilot.b_nonneg template (dist i p/r)))
      dsimp [R]
      linarith
  have hrb := profile_residual_bound hr C x p hR
  have he := near_profile_edit hr hfar hs
  have hsum : (∑ i,z i*(profile r C i-profile r (replace r C x) i)*
      Pilot.a template (dist i p/r)) ≥ (1/2:ℝ)*(if p∈annulus x r then (1:ℝ) else 0) := by
    by_cases hp : p∈annulus x r
    · rw [ite_eq_left hp,mul_one]
      have hb := single_le_sum (s := (univ : Finset Y))
        (fun i _ => mul_nonneg (profile_weight_nonneg hr C x hz.1 hmiddle i)
          (Pilot.a_nonneg template (dist i p/r))) (mem_univ s)
      rw [he.1,he.2,sub_zero,mul_one,annulus_bump_one hr hs hp,mul_one] at hb
      exact hsz.trans hb
    · rw [ite_eq_right hp,mul_zero]
      exact sum_nonneg fun i _ => mul_nonneg
        (profile_weight_nonneg hr C x hz.1 hmiddle i) (Pilot.a_nonneg template (dist i p/r))
  have hid : integrand template r (profile r C) z p-
      integrand template r (profile r (replace r C x)) z p =
      (profile r C p-profile r (replace r C x) p)*R+
      256*∑ i,z i*(profile r C i-profile r (replace r C x) i)*
        Pilot.a template (dist i p/r) := by
    have heq : (∑ i,z i*(1+profile r C i)*Pilot.a template (dist i p/r))-
      (∑ i,z i*(1+profile r (replace r C x) i)*Pilot.a template (dist i p/r)) =
      ∑ i,z i*(profile r C i-profile r (replace r C x) i)*Pilot.a template (dist i p/r) := by
      rw [←sum_sub_distrib]
      apply sum_congr rfl
      intro i _
      ring
    unfold integrand
    dsimp only [R]
    linear_combination 256*heq
  rw [hid]
  linarith

/-- The genuine heavy edit decrease, from compact minimizer local structure;
no pilot decrease is posed as a hypothesis. -/
theorem pilot_edit_drop {r γ δ : ℝ} (hr : 0 < r) (C : Finset Y) (x : Y)
    {μ : Y → ℝ} (hμ : ∀ y,0≤μ y) (hγ0 : 0≤γ) (hγ : γ≤1/64)
    (hδ : δ≤1/4112) (hM : 0<Pilot.mass μ (Pilot.ball x (γ*r)))
    (hheavy : Pilot.mass μ (Pilot.ball x (51200*r)) ≤
      (1+δ)*Pilot.mass μ (Pilot.ball x (γ*r)))
    (hfar : ∀ a∈C,8*r<dist a x) :
    127*r*Pilot.mass μ (annulus x r) ≤
      potential template r μ (profile r C)-potential template r μ (profile r (replace r C x)) := by
  let z := minimizer template r μ (profile r C)
  have hz := (minimizer_spec template r μ (profile r C)).1
  have hmin := (minimizer_spec template r μ (profile r C)).2
  have hbsub : Pilot.ball x (γ*r) ⊆ Pilot.ball x (51200*r) := by
    intro y hy
    apply mem_filter.mpr ⟨mem_univ _,?_⟩
    have hd := (mem_filter.mp hy).2
    nlinarith
  have hconc : Pilot.mass μ (Pilot.ball x (100*template.R*r) \ Pilot.ball x (γ*r)) ≤
      δ*Pilot.mass μ (Pilot.ball x (γ*r)) := by
    have he := sum_sdiff (f := μ) hbsub
    change Pilot.mass μ (Pilot.ball x (51200*r) \ Pilot.ball x (γ*r))+
      Pilot.mass μ (Pilot.ball x (γ*r))=Pilot.mass μ (Pilot.ball x (51200*r)) at he
    norm_num [template] at *
    linarith
  have hlocal := local_structure (T := template) hr hγ0 hγ (by dsimp [template]; linarith)
    hδ hμ (profile_bounds r C)
    (by intro i j; simpa only [template,one_mul] using profile_lipschitz hr C i j)
    hz hmin hM hconc
  have hmiddle : ∀ i,r/4 ≤ dist i x → dist i x ≤ 256*r → z i=0 := by
    simpa only [z,template,one_mul,show (512:ℝ)*r/2=256*r by ring] using hlocal.1
  obtain ⟨a,ha,haz,_⟩ := hlocal.2
  have hnear : ∃ a,dist a x < r/4 ∧ (1/2:ℝ) ≤ z a :=
    ⟨a,by simpa only [template,one_mul] using ha,by linarith⟩
  have hpoint := sum_le_sum (s := (univ : Finset Y)) fun p _ =>
    mul_le_mul_of_nonneg_left (edit_integrand_drop hr C x hz hfar hmiddle hnear p) (hμ p)
  have hobj : 127*r*Pilot.mass μ (annulus x r) ≤
      objective template r μ (profile r C) z-
        objective template r μ (profile r (replace r C x)) z := by
    have he : (∑ p,μ p*(127*(if p∈annulus x r then (1:ℝ) else 0))) =
        127*Pilot.mass μ (annulus x r) := by
      simp only [mul_ite,mul_one,mul_zero,←sum_filter]
      simp only [filter_mem_eq_inter,Finset.univ_inter]
      rw [←sum_mul]
      simp only [Pilot.mass]
      ring
    rw [he] at hpoint
    have hm := mul_le_mul_of_nonneg_left hpoint hr.le
    simp only [mul_sub,sum_sub_distrib] at hm
    unfold objective
    convert hm using 1 <;> first | rfl | ring
  have hnew := potential_le (μ := μ) (g := profile r (replace r C x)) hz
  change 127*r*Pilot.mass μ (annulus x r) ≤
    objective template r μ (profile r C) z-potential template r μ (profile r (replace r C x))
  linarith

end KServer.HeavyCenters

end


/-! The actual true-prefix heavy-center recursion of §07. All physical and
filtering steps are included in its potential budget, not only edit steps. -/
noncomputable section
open scoped BigOperators
open Finset Set
namespace KServer.HeavyCenters
open Pilot FiniteExperiment RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [MetricSpace Y] [Fintype Y]
variable {k H : ℕ} [NeZero k]

lemma step_separated (r γ δ : ℝ) (C : Finset Y) (μ : Y → ℝ) (x : Y)
    (hC : (C : Set Y).Pairwise (fun a b => 100*r<dist a b)) :
    ((step r γ δ C μ x : Finset Y) : Set Y).Pairwise (fun a b => 100*r<dist a b) := by
  unfold step
  split_ifs
  · intro a ha b hb hab
    rcases mem_insert.mp ha with rfl | ha
    · rcases mem_insert.mp hb with rfl | hb
      · exact (hab rfl).elim
      · have hd := (mem_filter.mp hb).2
        simpa only [dist_comm] using hd
    · rcases mem_insert.mp hb with rfl | hb
      · exact (mem_filter.mp ha).2
      · exact hC (mem_filter.mp ha).1 (mem_filter.mp hb).1 hab
  · exact hC

lemma centers_succ (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (r γ δ : ℝ) (σ : Fin H → Y) (t : Fin H) :
    centers s law r γ δ σ (t.val+1)=
      step r γ δ (centers s law r γ δ σ t.val) (mu s law (t.val+1) σ) (σ t) := by
  simp only [centers,t.isLt,↓reduceDIte]

lemma centers_separated (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (r γ δ : ℝ) (σ : Fin H → Y) (t : ℕ) :
    ((centers s law r γ δ σ t : Finset Y) : Set Y).Pairwise (fun a b => 100*r<dist a b) := by
  induction t with
  | zero => simp [centers]
  | succ t ih =>
    rw [centers]
    split_ifs
    · exact step_separated r γ δ _ _ _ ih
    · exact ih

lemma centers_adapted (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (r γ δ : ℝ) (t : ℕ) :
    ∀ σ ρ,requestHistory t σ=requestHistory t ρ →
      centers s law r γ δ σ t=centers s law r γ δ ρ t := by
  induction t with
  | zero => intros; rfl
  | succ t ih =>
    intro σ ρ h
    have hc := ih σ ρ (requestHistory_refines t σ ρ h)
    have hμ : mu s law (t+1) σ=mu s law (t+1) ρ :=
      funext (fun y => mu_adapted s law (t+1) y σ ρ h)
    simp only [centers]
    split_ifs with ht
    · rw [hc,hμ,request_of_history ⟨t,ht⟩ σ ρ h]
    · exact hc

lemma inner_mass_pos (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : Fin H) (σ : Fin H → Y) (hσ : 0<law.val σ) {r γ : ℝ}
    (hr : 0 < r) (hγ : 0≤γ) :
    0<Pilot.mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (γ*r)) := by
  have hx : σ t∈Pilot.ball (σ t) (γ*r) := by
    simp only [Pilot.ball,mem_filter,Finset.mem_univ,true_and,dist_self]
    exact mul_nonneg hγ hr.le
  have hm := single_le_sum (f := mu s law (t.val+1) σ)
    (fun y _ => mu_nonneg s law (t.val+1) σ y) hx
  exact lt_of_lt_of_le (by linarith [mu_served s law t σ hσ]) hm

lemma charge_le_drop (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    {r γ δ : ℝ} (hr : 0 < r) (hγ0 : 0≤γ) (hγ : γ≤1/64) (hδ : δ≤1/4112)
    (t : Fin H) (σ : Fin H → Y) (hσ : 0<law.val σ) :
    charge s law r γ δ t σ ≤
      potential template r (mu s law (t.val+1) σ) (profile r (centers s law r γ δ σ t.val))-
      potential template r (mu s law (t.val+1) σ) (profile r (centers s law r γ δ σ (t.val+1))) := by
  rw [centers_succ]
  unfold charge step
  split_ifs with ha
  · have hd := pilot_edit_drop hr (centers s law r γ δ σ t.val) (σ t)
      (mu_nonneg s law (t.val+1) σ) hγ0 hγ hδ (inner_mass_pos s law t σ hσ hr hγ0) ha.1 ha.2
    have hn := mul_nonneg hr.le (Pilot.mass_nonneg (mu_nonneg s law (t.val+1) σ) (annulus (σ t) r))
    nlinarith
  · simp

/-- The source's all-step heavy-annulus budget for the actual adaptive
construction, with a finite endpoint bound independent of law and horizon. -/
theorem annulus_budget (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    {γ δ r₀ τ : ℝ} (n p : ℕ)
    (hr : 0 < r₀) (hτ : 2≤τ) (hγ0 : 0<γ) (hγ : γ≤1/64)
    (hδ0 : 0<δ) (hδ : δ≤1/4112) (hpow : 51200≤γ*(2:ℝ)^p) :
    (∑ t : Fin H,avg law.val (fun σ => ∑ j∈range n,
      charge s law (radius r₀ τ j) γ δ t σ)) ≤
      driftConstant template γ δ p*(1+Real.log ((k:ℝ)+1))*
        ∑ σ,law.val σ*optimalCost s (List.ofFn σ)+
          ∑ j∈range n,2*radius r₀ τ j*(k:ℝ) := by
  let g := fun t σ j => profile (radius r₀ τ j) (centers s law (radius r₀ τ j) γ δ σ t)
  have hrad j : 0 < radius r₀ τ j := radius_pos hr (by linarith) j
  have hb := pilot_edit_budget s law template (g := g) n p hr hτ hγ0
    (by dsimp [template]; exact le_min hγ (by linarith)) hδ0 hδ
    (by norm_num [template]; exact hpow)
    (by intro t σ j _ y; exact profile_bounds _ _ y)
    (by intro t σ j _ y z; simpa only [template,one_mul] using
      profile_lipschitz (hrad j) (centers s law (radius r₀ τ j) γ δ σ t) y z)
    (by intro t j _ y σ ρ hh; dsimp [g]; rw [centers_adapted s law _ γ δ t σ ρ hh])
  apply le_trans _ hb
  apply sum_le_sum
  intro t _
  apply sum_le_sum
  intro σ _
  by_cases hσ : 0<law.val σ
  · apply mul_le_mul_of_nonneg_left _ (law.property.1 σ)
    exact sum_le_sum fun j _ => charge_le_drop s law (hrad j) hγ0.le hγ hδ t σ hσ
  · have hz : law.val σ=0 := le_antisymm (le_of_not_gt hσ) (law.property.1 σ)
    simp [hz]

end KServer.HeavyCenters

end


/-! Fixed labels with a cooldown are constructed by finite online coloring.
A conflict set is a deterministic collection of previously reserved records;
labels are never used as random-tape indices. This is the finite pool mechanism
of §07, not a growing historical alphabet. -/


/-! Actual finite heavy-ball label update. Intersections in the finite metric
force reuse; otherwise the new label avoids both current and previous labels.
No region, anchor or label lifetime is assumed. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavyLabels
open HeavyCenters
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y] [Fintype Y]

lemma overlap_distance {C : Finset Y} {rad : Y → ℝ} {x a : Y} {r R : ℝ}
    (hrad : ∀ a∈C,rad a≤20*r) (hR : R≤20*r) (ha : a∈overlap C rad x R) :
    dist a x≤40*r := by
  obtain ⟨ha,p,hp,hx⟩ := mem_filter.mp ha
  have ht:=dist_triangle a p x
  rw [dist_comm p x] at ht
  linarith [hrad a ha]

lemma overlap_unique {C : Finset Y} {rad : Y → ℝ} {x a b : Y} {r R : ℝ}
    (hr : 0 < r) (hC : (C:Set Y).Pairwise (fun a b=>100*r<dist a b))
    (hrad : ∀ a∈C,rad a≤20*r) (hR : R≤20*r)
    (ha : a∈overlap C rad x R) (hb : b∈overlap C rad x R) : a=b := by
  by_contra hn
  have hd:=hC (mem_filter.mp ha).1 (mem_filter.mp hb).1 hn
  have h1:=overlap_distance hrad hR ha
  have h2:=overlap_distance hrad hR hb
  have ht:=dist_triangle a x b
  rw [dist_comm x b] at ht
  linarith

omit [MetricSpace Y] in
lemma fresh_avoids (C D : Finset Y) (label prev : Y → Pool Y) :
    fresh C D label prev∉C.image label ∧ fresh C D label prev∉D.image prev :=
  (unused C D label prev).choose_spec

lemma inserted_reuses {C D : Finset Y} {rad : Y → ℝ} {label prev : Y → Pool Y} {x a : Y} {r R : ℝ}
    (hr : 0 < r) (hC : (C:Set Y).Pairwise (fun a b=>100*r<dist a b))
    (hrad : ∀ a∈C,rad a≤20*r) (hR : R≤20*r) (ha : a∈overlap C rad x R) :
    insertedLabel C D rad label prev x R=label a := by
  have h : (overlap C rad x R).Nonempty:=⟨a,ha⟩
  rw [insertedLabel,dite_eq_left h]
  rw [overlap_unique hr hC hrad hR h.choose_spec ha]

lemma existing_match {C D : Finset Y} {rad : Y → ℝ} {label prev : Y → Pool Y} {x a : Y} {R : ℝ}
    (hl : Set.InjOn label (C:Set Y)) (ha : a∈C)
    (he : insertedLabel C D rad label prev x R=label a) : a∈overlap C rad x R := by
  unfold insertedLabel at he
  split_ifs at he with h
  · have heq:=hl (mem_filter.mp h.choose_spec).1 ha he
    exact heq ▸ h.choose_spec
  · exact False.elim ((fresh_avoids C D label prev).1 (mem_image.mpr ⟨a,ha,he.symm⟩))

lemma inserted_diff_kept {C D : Finset Y} {rad : Y → ℝ} {label prev : Y → Pool Y} {x a : Y} {r R : ℝ}
    (hr : 0 < r) (hrad : ∀ a∈C,rad a≤20*r) (hR : R≤20*r)
    (hl : Set.InjOn label (C:Set Y)) (ha : a∈C) (hd : 100*r<dist a x) :
    insertedLabel C D rad label prev x R≠label a := by
  intro he
  have hh:=overlap_distance hrad hR (existing_match hl ha he)
  linarith

/-- An actual update preserves injective active heavy labels. -/
lemma update_injective {C D : Finset Y} {rad : Y → ℝ} {label prev : Y → Pool Y} {x : Y} {r R : ℝ}
    (hr : 0 < r) (hrad : ∀ a∈C,rad a≤20*r) (hR : R≤20*r)
    (hl : Set.InjOn label (C:Set Y)) :
    Set.InjOn (updatedLabel C D rad label prev x R) (replace r C x:Set Y) := by
  intro a ha b hb he
  rcases mem_insert.mp ha with hax|ha
  · subst a
    rcases mem_insert.mp hb with hbx|hb
    · exact hbx.symm
    · have hbx : b≠x := by
        intro hh; have hd:=(mem_filter.mp hb).2; simp only [hh,dist_self] at hd; linarith
      simp only [updatedLabel,Function.update_self,Function.update_of_ne hbx] at he
      exact False.elim (inserted_diff_kept hr hrad hR hl (mem_filter.mp hb).1 (mem_filter.mp hb).2 he)
  · rcases mem_insert.mp hb with hbx|hb
    · subst b
      have hax : a≠x := by
        intro hh; have hd:=(mem_filter.mp ha).2; simp only [hh,dist_self] at hd; linarith
      simp only [updatedLabel,Function.update_self,Function.update_of_ne hax] at he
      exact False.elim (inserted_diff_kept hr hrad hR hl (mem_filter.mp ha).1 (mem_filter.mp ha).2 he.symm)
    · have hax : a≠x := by
        intro hh; have hd:=(mem_filter.mp ha).2; simp only [hh,dist_self] at hd; linarith
      have hbx : b≠x := by
        intro hh; have hd:=(mem_filter.mp hb).2; simp only [hh,dist_self] at hd; linarith
      simp only [updatedLabel,Function.update_of_ne hax,Function.update_of_ne hbx] at he
      exact hl (mem_filter.mp ha).1 (mem_filter.mp hb).1 he

end KServer.HeavyLabels

end


/-! Exact truncated exponential tails and first-hit cancellation used by the
chronological finite-law partition construction, manuscript §07.  The radius
law is not replaced by a uniform/padded law: `tail` is its exact tail. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PartitionProbabilities

attribute [local instance] Classical.propDecidable Classical.decEq

lemma position_difference {r a b : ℝ} (hr : 0 < r) (hab : a ≤ b) :
    position r b-position r a ≤ (b-a)/r := by
  have hdiv : a/r ≤ b/r := div_le_div_of_nonneg_right hab hr.le
  have hd : (b-a)/r = b/r-a/r := sub_div _ _ _
  rw [hd]
  unfold position
  rcases le_total (a/r-1) 0 with ha | ha
  · rw [max_eq_right ha, min_eq_left (by norm_num : (0:ℝ) ≤ 1)]
    rcases le_total (b/r-1) 0 with hb | hb
    · rw [max_eq_right hb, min_eq_left (by norm_num : (0:ℝ) ≤ 1)]
      linarith
    · rw [max_eq_left hb]
      linarith [min_le_left (b/r-1) (1:ℝ)]
  · rw [max_eq_left ha, max_eq_left (ha.trans (sub_le_sub_right hdiv _))]
    rcases le_total (a/r-1) 1 with ha' | ha'
    · rw [min_eq_left ha']
      linarith [min_le_left (b/r-1) 1]
    · rw [min_eq_right ha', min_eq_right (ha'.trans (sub_le_sub_right hdiv _))]
      linarith

lemma position_of_ge {r a : ℝ} (hr : 0 < r) (ha : 2*r ≤ a) : position r a=1 := by
  have h : 1 ≤ a/r-1 := by have := (le_div_iff₀ hr).mpr ha; linarith
  rw [position, max_eq_left (by linarith), min_eq_right h]

lemma tail_of_ge {lam r a : ℝ} (hr : 0 < r) (ha : 2*r ≤ a) : tail lam r a=0 := by
  simp [tail,position_of_ge hr ha]

/-- Elementary exponential secant bound, including arbitrary negative inputs. -/
lemma exp_difference_le (u v : ℝ) : Real.exp u-Real.exp v ≤ (u-v)*Real.exp u := by
  have h := Real.add_one_le_exp (v-u)
  have hm := mul_le_mul_of_nonneg_right h (Real.exp_nonneg u)
  rw [← Real.exp_add] at hm
  have he : v-u+u=v := by ring
  rw [he] at hm
  nlinarith

/-- The source first-hit tail inequality, valid even if the interval crosses
one or both endpoints of the radius support. -/
theorem tail_interval_bound {lam r a b : ℝ} (hlam : 0 < lam) (hr : 0 < r) (hab : a ≤ b) :
    tail lam r a-tail lam r b ≤
      (lam*(b-a)/r)*(tail lam r a+1/(Real.exp lam-1)) := by
  let c := Real.exp lam-1
  have hc : 0 < c := sub_pos.mpr (Real.one_lt_exp_iff.mpr hlam)
  have hd := position_difference hr hab
  have hE := exp_difference_le (lam*(1-position r a)) (lam*(1-position r b))
  have hE' : Real.exp (lam*(1-position r a))-Real.exp (lam*(1-position r b)) ≤
      (lam*(b-a)/r)*Real.exp (lam*(1-position r a)) := by
    refine hE.trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    calc lam*(1-position r a)-lam*(1-position r b) = lam*(position r b-position r a) := by ring
         _ ≤ lam*((b-a)/r) := mul_le_mul_of_nonneg_left hd hlam.le
         _ = lam*(b-a)/r := by ring
  have hdiv := div_le_div_of_nonneg_right hE' hc.le
  dsimp [tail]
  dsimp [c] at hdiv hc
  convert hdiv using 1 <;> first | rfl | ring

section FiniteProduct
variable {I : Type*} [Fintype I] {Ω : I → Type*} [∀ i, Fintype (Ω i)]

lemma product_expectation (w f : ∀ i, Ω i → ℝ) :
    (∑ o, productWeight w o*∏ i, f i (o i))=∏ i, ∑ a, w i a*f i a := by
  classical
  simp only [productWeight, ← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => w i a*f i a)).symm

lemma rectangle_probability (w : ∀ i, Ω i → ℝ) (E : ∀ i, Ω i → Prop) :
    probability w (fun o => ∀ i, E i (o i))=∏ i, ∑ a, if E i a then w i a else 0 := by
  classical
  rw [probability, Fintype.prod_sum]
  apply sum_congr rfl
  intro o _
  by_cases h : ∀ i, E i (o i)
  · simp [h, productWeight]
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := not_forall.mp h
    symm
    exact prod_eq_zero (mem_univ i) (ite_eq_right hi)

lemma probability_range {w : ∀ i, Ω i → ℝ} (hw : ∀ i a, 0 ≤ w i a)
    (hsum : ∀ i, ∑ a, w i a=1) (E : (∀ i, Ω i) → Prop) :
    probability w E ∈ Set.Icc (0:ℝ) 1 := by
  classical
  refine ⟨sum_nonneg (fun o _ => ?_), ?_⟩
  · split_ifs
    · exact productWeight_nonneg hw o
    · rfl
  · calc probability w E ≤ ∑ o, productWeight w o := by
           apply sum_le_sum
           intro o _
           split_ifs
           · rfl
           · exact productWeight_nonneg hw o
         _ = 1 := productWeight_sum w hsum

omit [Fintype I] in
lemma complement_probability (w : ∀ i, Ω i → ℝ) (i : I) (E : Ω i → Prop)
    (hw : ∑ a, w i a=1) :
    (∑ a, if ¬E a then w i a else 0)=1-∑ a, if E a then w i a else 0 := by
  classical
  have he : (∑ a, if ¬E a then w i a else 0)+(∑ a, if E a then w i a else 0)=1 := by
    rw [← sum_add_distrib, ← hw]
    apply sum_congr rfl
    intro a _
    split_ifs <;> simp_all
  linarith
end FiniteProduct

section FirstSeparation
variable {n : ℕ} {Ω : Fin n → Type*} [∀ i, Fintype (Ω i)]

omit [∀ i, Fintype (Ω i)] in
lemma firstAt_unique {hit sep : ∀ i, Ω i → Prop} (hs : ∀ i a, sep i a → hit i a)
    {o : ∀ i, Ω i} {i j : Fin n} (hi : firstAt hit sep i o) (hj : firstAt hit sep j o) : i=j := by
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim (hj.2 i h (hs i (o i) hi.1))
  · exact h
  · exact False.elim (hi.2 j h (hs j (o j) hj.1))

lemma firstSeparation_probability {hit sep : ∀ i, Ω i → Prop}
    (hs : ∀ i a, sep i a → hit i a) (w : ∀ i, Ω i → ℝ) :
    probability w (firstSeparation hit sep)=∑ i, probability w (firstAt hit sep i) := by
  classical
  unfold probability
  rw [sum_comm]
  apply sum_congr rfl
  intro o _
  by_cases h : firstSeparation hit sep o
  · rw [ite_eq_left h]
    obtain ⟨i,hi⟩ := h
    change firstAt hit sep i o at hi
    symm
    rw [sum_eq_single i, ite_eq_left hi]
    · intro j _ hji
      rw [ite_eq_right (fun hj => hji (firstAt_unique hs hj hi))]
    · exact fun hnot => False.elim (hnot (mem_univ i))
  · rw [ite_eq_right h]
    symm
    apply sum_eq_zero
    intro i _
    exact ite_eq_right (fun hi => h ⟨i,hi⟩)

/-- Evaluation of one first-hit rectangle under the constructed product tape. -/
lemma firstAt_probability {hit sep : ∀ i, Ω i → Prop}
    (w : ∀ i, Ω i → ℝ) (hw : ∀ i, ∑ a, w i a=1) (i : Fin n) :
    probability w (firstAt hit sep i)=
      (∑ a, if sep i a then w i a else 0) *
        ∏ j ∈ univ.filter (fun j : Fin n => j < i), (1 - ∑ a, if hit j a then w j a else 0) := by
  classical
  let E : ∀ j, Ω j → Prop := fun j a => (j=i → sep j a) ∧ (j < i → ¬hit j a)
  have he : firstAt hit sep i=(fun o => ∀ j, E j (o j)) := by
    funext o
    apply propext
    constructor
    · intro h j
      exact ⟨fun hj => by subst j; exact h.1, h.2 j⟩
    · intro h
      exact ⟨(h i).1 rfl, fun j hj => (h j).2 hj⟩
  rw [he,rectangle_probability]
  have hfac (j : Fin n) : (∑ a, @ite ℝ (E j a) (Classical.propDecidable _) (w j a) 0)=
      (if j=i then (∑ a, if sep j a then w j a else 0) else 1)*
      (if j < i then (1-∑ a, if hit j a then w j a else 0) else 1) := by
    by_cases hji : j=i
    · subst j
      simp [E]
    · by_cases hj : j < i
      · simp only [E,hji,hj,false_implies,true_implies,true_and,ite_false,ite_true,one_mul]
        exact complement_probability w j (hit j) (hw j)
      · simp [E,hji,hj,hw]
  calc
    (∏ j, ∑ a, @ite ℝ (E j a) (Classical.propDecidable _) (w j a) 0) = ∏ j, ((if j=i then (∑ a, if sep j a then w j a else 0) else 1)*
      (if j < i then (1-∑ a, if hit j a then w j a else 0) else 1)) :=
        prod_congr rfl (fun j _ => hfac j)
    _ = _ := by
      rw [prod_mul_distrib]
      simp only [prod_ite_eq',mem_univ,ite_true]
      congr 1
      rw [prod_filter]

end FirstSeparation

end KServer.PartitionProbabilities

end


/-! Finite inverse-tail sampling for the chronological tape. It applies both
to retirement ages and to the finitely many observable radius thresholds. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.FiniteSurvival

lemma probability_living (s : ℕ → ℝ) (N a : ℕ) (ha : a ≤ N) :
    probability s (fun d : Fin N => a ≤ (d:ℕ))=s a-s N := by
  classical
  have heq : probability s (fun d : Fin N => a ≤ (d:ℕ))=
      ∑ d : Fin N, if a ≤ (d:ℕ) then s d-s (d+1) else 0 := by
    apply sum_congr rfl
    intro d _
    by_cases h : a ≤ (d:ℕ) <;> simp [h,weight]
  rw [heq,Fin.sum_univ_eq_sum_range (fun d => if a ≤ d then s d-s (d+1) else 0)]
  have hf : (range N).filter (fun d => a ≤ d)=Ico a N := by
    ext d
    simp only [mem_filter,mem_range,mem_Ico]
    omega
  rw [← sum_filter,hf]
  have h := sum_Ico_sub s ha
  have he : (∑ d ∈ Ico a N, (s d-s (d+1))) =
      -(∑ d ∈ Ico a N, (s (d+1)-s d)) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro d _
    ring
  rw [he,h]
  ring

end KServer.FiniteSurvival

end


/-! Finite discretization of the manuscript's truncated exponential radius.
All pairwise-distance decisions are included in a finite ordered grid; its
literal tail law yields a finite tape, without invoking assumed independence. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.FiniteRadius
open PartitionProbabilities FiniteSurvival
attribute [local instance] Classical.propDecidable Classical.decEq

lemma survival_fin (D : Finset ℝ) (lam r : ℝ) (a : Fin (grid D r).card) :
    survival D lam r a=tail lam r (point D r a) := by simp [survival,a.isLt]

lemma grid_tail (D : Finset ℝ) {lam r a : ℝ} (_ : 0<lam) (_ : 0 < r)
    (ha:a∈grid D r) :
    (∑ i,if a≤point D r i then weights D lam r i else 0)=tail lam r a := by
  let j:=((grid D r).orderIsoOfFin rfl).symm ⟨a,ha⟩
  have he:point D r j=a := congrArg Subtype.val (((grid D r).orderIsoOfFin rfl).apply_symm_apply _)
  have hiff (i : Fin (grid D r).card) : a≤point D r i ↔ j.val ≤ i.val := by
    rw [←he]
    exact (point_mono D r).le_iff_le
  simp_rw [hiff]
  have hh:=probability_living (survival D lam r) (grid D r).card j.val j.isLt.le
  change (∑ i,if j.val ≤ i.val then weight (survival D lam r) i else 0)=_
  unfold FiniteSurvival.probability at hh
  simp only [survival_last,sub_zero,survival_fin,he] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply sum_congr rfl
  intro i _
  by_cases hi : j.val ≤ i.val <;> simp [hi]

end KServer.FiniteRadius

end


/-! Finite realization of the uniform heavy-ball radii. The finite grid
preserves every relevant metric threshold, hence its law is exact for balls. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.FiniteUniform
open FiniteRadius FiniteSurvival
attribute [local instance] Classical.propDecidable Classical.decEq

lemma tail_of_ge {r a : ℝ} (hr : 0 < r) (ha : 2*r≤a) : tail r a=0 := by
  have hh : (2*r-a)/r≤0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hr.le
  simp [tail,min_eq_right (by linarith : (2*r-a)/r≤1),max_eq_left hh]
lemma tail_lipschitz {r a b : ℝ} (hr : 0 < r) : |tail r a-tail r b|≤|a-b|/r := by
  have h1 := abs_max_sub_max_le_max (0:ℝ) (min 1 ((2*r-a)/r)) 0 (min 1 ((2*r-b)/r))
  have h2 := abs_min_sub_min_le_max (1:ℝ) ((2*r-a)/r) 1 ((2*r-b)/r)
  simp only [sub_self,abs_zero] at h1 h2
  have h1' := h1.trans (max_le (abs_nonneg _) le_rfl)
  have h2' := h2.trans (max_le (abs_nonneg _) le_rfl)
  have he : (2*r-a)/r-(2*r-b)/r=-(a-b)/r := by ring
  simpa only [tail,he,abs_div,abs_neg,abs_of_pos hr] using h1'.trans h2'

lemma survival_fin (D : Finset ℝ) (r : ℝ) (a : Fin (grid D r).card) :
    survival D r a=tail r (point D r a) := by simp [survival,a.isLt]
lemma grid_tail (D : Finset ℝ) {r a : ℝ} (ha:a∈grid D r) :
    (∑ i,if a≤point D r i then weights D r i else 0)=tail r a := by
  let j:=((grid D r).orderIsoOfFin rfl).symm ⟨a,ha⟩
  have he:point D r j=a := congrArg Subtype.val (((grid D r).orderIsoOfFin rfl).apply_symm_apply _)
  have hiff (i : Fin (grid D r).card) : a≤point D r i ↔ j.val ≤ i.val := by
    rw [←he]
    exact (point_mono D r).le_iff_le
  simp_rw [hiff]
  have hh:=probability_living (survival D r) (grid D r).card j.val j.isLt.le
  change (∑ i,if j.val ≤ i.val then weight (survival D r) i else 0)=_
  unfold FiniteSurvival.probability at hh
  simp only [survival_last,sub_zero,survival_fin,he] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply sum_congr rfl
  intro i _
  by_cases hi : j.val ≤ i.val <;> simp [hi]
lemma query_tail (D : Finset ℝ) {r a : ℝ} (hr : 0 < r) (ha:a∈D) :
    (∑ i,if a≤point D r i then weights D r i else 0)=tail r a := by
  by_cases hlo : a < r
  · rw [tail_of_le hr hlo.le]
    convert weights_sum D hr using 1
    all_goals try with_reducible_and_instances rfl
    apply sum_congr rfl
    intro i _
    exact ite_eq_left (hlo.le.trans (point_range D hr i).1)
  · by_cases hhi : 2*r<a
    · rw [tail_of_ge hr hhi.le]
      apply sum_eq_zero
      intro i _
      exact ite_eq_right (not_le.mpr ((point_range D hr i).2.trans_lt hhi))
    · exact grid_tail D (mem_insert_of_mem (mem_insert_of_mem
        (mem_filter.mpr ⟨ha,le_of_not_gt hlo,le_of_not_gt hhi⟩)))

variable {Y : Type*} [Fintype Y] [PseudoMetricSpace Y]
lemma dist_threshold (r : ℝ) (x y : Y) : (dist x y-12*r)/4∈thresholds (Y:=Y) r :=
  mem_image.mpr ⟨(x,y),mem_univ _,rfl⟩
lemma radius_range {r : ℝ} (hr : 0 < r) (i : Outcome Y r) : radius r i∈Set.Icc (16*r) (20*r) := by
  have hh:=point_range (thresholds (Y:=Y) r) hr i
  dsimp [radius]; constructor <;> linarith [hh.1,hh.2]
lemma ball_probability {r : ℝ} (hr : 0 < r) (c x : Y) :
    (∑ i : Outcome Y r,if dist c x ≤ radius r i then law r i else 0)=tail r ((dist c x-12*r)/4) := by
  convert query_tail (thresholds (Y:=Y) r) hr (dist_threshold r c x) using 1
  all_goals try with_reducible_and_instances rfl
  apply sum_congr rfl
  intro i _
  have he : dist c x ≤ radius r i ↔ (dist c x-12*r)/4≤point (thresholds (Y:=Y) r) r i := by
    dsimp [radius]; constructor <;> intro hh <;> linarith
  simp only [he,law]

lemma separates_comm (r : ℝ) (c x y : Y) (i : Outcome Y r) :
    separates r c x y i ↔ separates r c y x i := Or.comm
lemma separation_ordered {r : ℝ} (hr : 0 < r) (c x y : Y) (hxy : dist c x≤dist c y) :
    (∑ i : Outcome Y r,if separates r c x y i then law r i else 0)=
      tail r ((dist c x-12*r)/4)-tail r ((dist c y-12*r)/4) := by
  rw [←ball_probability hr c x,←ball_probability hr c y,←sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  by_cases hy : dist c y ≤ radius r i
  · have hx:=hxy.trans hy
    simp [separates,hy,hx,not_lt_of_ge hx,not_lt_of_ge hy]
  · have hny:=lt_of_not_ge hy
    by_cases hx : dist c x ≤ radius r i <;> simp [separates,hy,hx,hny]

theorem one_ball_bound {r : ℝ} (hr : 0 < r) (c x y : Y) :
    (∑ i : Outcome Y r,if separates r c x y i then law r i else 0)≤dist x y/(4*r) := by
  wlog hxy : dist c x≤dist c y generalizing x y
  · have hb:=this y x (le_of_not_ge hxy)
    have he : (fun i : Outcome Y r=>separates r c x y i)=(fun i=>separates r c y x i) := by
      funext i; exact propext (separates_comm r c x y i)
    simpa only [he,dist_comm y x] using hb
  rw [separation_ordered hr c x y hxy]
  have hLip:=tail_lipschitz (a:=(dist c x-12*r)/4) (b:=(dist c y-12*r)/4) hr
  have he : (dist c x-12*r)/4-(dist c y-12*r)/4=(dist c x-dist c y)/4 := by ring
  rw [he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<4)] at hLip
  have hdist : |dist c x-dist c y|≤dist x y := by
    simpa only [dist_comm c x,dist_comm c y] using abs_dist_sub_le x y c
  calc _ ≤ |tail r ((dist c x-12*r)/4)-tail r ((dist c y-12*r)/4)| := le_abs_self _
    _ ≤ (|dist c x-dist c y|/4)/r := hLip
    _ = |dist c x-dist c y|/(4*r) := by ring
    _ ≤ dist x y/(4*r) := div_le_div_of_nonneg_right hdist (by positivity)
end KServer.FiniteUniform

end


/-! The literal causal heavy-ball radii/labels recursion on the constructed
finite tape. The center schedule is the actual true-prefix pilot schedule. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavySchedule
open HeavyCenters HeavyLabels FiniteExperiment
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [MetricSpace Y] [Fintype Y]
variable {k H : ℕ} [NeZero k]

lemma run_valid (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    {r : ℝ} (hr : 0 < r) (γ δ : ℝ) (σ : Fin H → Y) (tape : Fin H → FiniteUniform.Outcome Y r)
    (t : ℕ) :
    (∀ a∈centers s law r γ δ σ t,(run s law r γ δ σ tape t).rad a∈Set.Icc (16*r) (20*r)) ∧
    Set.InjOn (run s law r γ δ σ tape t).label (centers s law r γ δ σ t:Set Y) := by
  induction t with
  | zero => simp [centers,Set.InjOn]
  | succ t ih =>
    rw [run,centers]
    dsimp only
    simp only [HeavyCenters.step]
    split_ifs with ht ha
    · constructor
      · intro a haC
        rcases mem_insert.mp haC with hax|haC
        · subst a
          simpa only [Function.update_self] using FiniteUniform.radius_range hr (tape ⟨t,ht⟩)
        · have hax : a≠σ ⟨t,ht⟩ := by
            intro he
            have hd:=(mem_filter.mp haC).2
            rw [he,dist_self] at hd
            linarith
          simp only [Function.update_of_ne hax]
          exact ih.1 a (mem_filter.mp haC).1
      · have hv := update_injective (D := centers s law r γ δ σ (t-1))
          (prev := (run s law r γ δ σ tape t).previous) (x := σ ⟨t,ht⟩)
          hr (fun a ha=>(ih.1 a ha).2) (FiniteUniform.radius_range hr (tape ⟨t,ht⟩)).2 ih.2
        exact hv
    · exact ih
    · exact ih

lemma radius_birth (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y)) (r γ δ : ℝ)
    (σ : Fin H → Y) (tape : Fin H → FiniteUniform.Outcome Y r) (t : ℕ) (a : Y) :
    (run s law r γ δ σ tape t).rad a=
      match birth s law r γ δ σ t a with
      | none=>16*r
      | some i=>FiniteUniform.radius r (tape i) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run,birth]
    dsimp only
    split_ifs with ht ha
    · by_cases hx : a=σ ⟨t,ht⟩
      · subst a; simp only [Function.update_self]
      · simp only [Function.update_of_ne hx]; exact ih
    · exact ih
    · exact ih

lemma present_birth (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    {r : ℝ} (hr : 0 < r) (γ δ : ℝ) (σ : Fin H → Y) (t : ℕ) (a : Y)
    (ha : a∈centers s law r γ δ σ t) :
    ∃ i : Fin H,birth s law r γ δ σ t a=some i ∧ i.val<t ∧ σ i=a := by
  induction t with
  | zero => simp [centers] at ha
  | succ t ih =>
    rw [centers] at ha
    simp only [HeavyCenters.step] at ha
    rw [birth]
    split_ifs at * with ht hA
    · rcases mem_insert.mp ha with he|ha
      · subst a
        exact ⟨⟨t,ht⟩,Function.update_self _ _ _,by change t<t+1; omega,rfl⟩
      · have hx : a≠σ ⟨t,ht⟩ := by
          intro he
          have hd:=(mem_filter.mp ha).2
          rw [he,dist_self] at hd
          linarith
        obtain ⟨i,hi,hb,hc⟩:=ih (mem_filter.mp ha).1
        exact ⟨i,by simpa only [Function.update_of_ne hx] using hi,by omega,hc⟩
    · obtain ⟨i,hi,hb,hc⟩:=ih ha
      exact ⟨i,hi,by omega,hc⟩
    · obtain ⟨i,hi,hb,hc⟩:=ih ha
      exact ⟨i,hi,by omega,hc⟩
end KServer.HeavySchedule

end


/-! Exact finite ball laws for the metric thresholds used in §07.  Their
chronological first-hit estimate uses the constructed product law, not an
independence premise about a posterior filtration. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.FiniteBallLaw
open PartitionProbabilities FiniteRadius
attribute [local instance] Classical.propDecidable Classical.decEq

lemma query_tail (D : Finset ℝ) {lam r a : ℝ} (hlam : 0 < lam) (hr : 0 < r)
    (ha : a ∈ D) :
    (∑ i, if a ≤ point D r i then weights D lam r i else 0)=tail lam r a := by
  by_cases hlo : a < r
  · rw [tail_of_le hlam hr hlo.le]
    convert weights_sum D hlam hr using 1
    all_goals try with_reducible_and_instances rfl
    apply sum_congr rfl
    intro i _
    exact ite_eq_left (hlo.le.trans (point_range D hr i).1)
  · by_cases hhi : 2*r < a
    · rw [tail_of_ge hr hhi.le]
      apply sum_eq_zero
      intro i _
      exact ite_eq_right (not_le.mpr ((point_range D hr i).2.trans_lt hhi))
    · apply grid_tail D hlam hr
      exact mem_insert_of_mem (mem_insert_of_mem (mem_filter.mpr ⟨ha,le_of_not_gt hlo,le_of_not_gt hhi⟩))

variable {Y : Type*} [Fintype Y] [PseudoMetricSpace Y]

lemma dist_threshold (x y : Y) : dist x y ∈ thresholds (Y:=Y) :=
  mem_image.mpr ⟨(x,y),mem_univ _,rfl⟩

lemma radius_range {r : ℝ} (hr : 0 < r) (i : Outcome Y r) : radius r i ∈ Set.Icc r (2*r) :=
  point_range _ hr i

lemma separation_hit (r : ℝ) (c x y : Y) (i : Outcome Y r) : separates r c x y i → hit r c x y i := by
  rintro (h|h)
  · exact Or.inl h.1
  · exact Or.inr h.1

lemma hit_min (r : ℝ) (c x y : Y) (i : Outcome Y r) :
    hit r c x y i ↔ min (dist c x) (dist c y) ≤ radius r i := by
  exact min_le_iff.symm

lemma separation_interval (r : ℝ) (c x y : Y) (i : Outcome Y r) :
    separates r c x y i ↔ min (dist c x) (dist c y) ≤ radius r i ∧
      radius r i < max (dist c x) (dist c y) := by
  rcases le_total (dist c x) (dist c y) with h|h
  · rw [min_eq_left h,max_eq_right h]
    constructor
    · rintro (he|he)
      · exact he
      · exact False.elim ((not_lt_of_ge (h.trans he.1)) he.2)
    · exact Or.inl
  · rw [min_eq_right h,max_eq_left h]
    constructor
    · rintro (he|he)
      · exact False.elim ((not_lt_of_ge (h.trans he.1)) he.2)
      · exact he
    · exact Or.inr

lemma min_threshold (c x y : Y) : min (dist c x) (dist c y) ∈ thresholds (Y:=Y) := by
  rcases le_total (dist c x) (dist c y) with h|h
  · simpa [min_eq_left h] using dist_threshold c x
  · simpa [min_eq_right h] using dist_threshold c y

lemma max_threshold (c x y : Y) : max (dist c x) (dist c y) ∈ thresholds (Y:=Y) := by
  rcases le_total (dist c x) (dist c y) with h|h
  · simpa [max_eq_right h] using dist_threshold c y
  · simpa [max_eq_left h] using dist_threshold c x

lemma hit_probability {lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r) (c x y : Y) :
    (∑ i : Outcome Y r, if hit r c x y i then law lam r i else 0)=
      tail lam r (min (dist c x) (dist c y)) := by
  simp_rw [hit_min]
  exact query_tail _ hlam hr (min_threshold c x y)

lemma separation_probability {lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r) (c x y : Y) :
    (∑ i : Outcome Y r, if separates r c x y i then law lam r i else 0)=
      tail lam r (min (dist c x) (dist c y))-
        tail lam r (max (dist c x) (dist c y)) := by
  rw [←query_tail _ hlam hr (min_threshold c x y),←query_tail _ hlam hr (max_threshold c x y),←sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  rw [separation_interval]
  simp only [radius,law]
  by_cases h : max (dist c x) (dist c y) ≤ point (thresholds (Y:=Y)) r i
  · have hl : min (dist c x) (dist c y) ≤ point (thresholds (Y:=Y)) r i := (min_le_max).trans h
    simp [h,hl,not_lt_of_ge h]
  · have hh : point (thresholds (Y:=Y)) r i < max (dist c x) (dist c y) := lt_of_not_ge h
    simp only [hh,and_true,ite_eq_right h,sub_zero]

omit [Fintype Y] in
lemma width_distance (c x y : Y) : max (dist c x) (dist c y)-min (dist c x) (dist c y) ≤ dist x y := by
  rw [max_sub_min_eq_abs]
  simpa [dist_comm,abs_sub_comm] using abs_dist_sub_le x y c

lemma one_ball_bound {lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r) (c x y : Y) :
    (∑ i : Outcome Y r, if separates r c x y i then law lam r i else 0) ≤
      (lam*dist x y/r)*((∑ i : Outcome Y r, if hit r c x y i then law lam r i else 0)+
        1/(Real.exp lam-1)) := by
  rw [separation_probability hlam hr,hit_probability hlam hr]
  have ht := tail_interval_bound hlam hr (min_le_max (a:=dist c x) (b:=dist c y))
  refine ht.trans ?_
  apply mul_le_mul_of_nonneg_right
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (width_distance c x y) hlam.le) hr.le
  · exact add_nonneg (tail_range hlam _ _).1 (div_nonneg zero_le_one (by linarith [Real.one_lt_exp_iff.mpr hlam]))

lemma lambda_pos {K : ℕ} (hK : 1 ≤ K) : 0 < Real.log (1+(K:ℝ)^2) := by
  have hk : (1:ℝ) ≤ K := by exact_mod_cast hK
  apply Real.log_pos
  nlinarith

end KServer.FiniteBallLaw

end


/- Chronological rosters retain insertion times rather than surviving random balls. The tests are independent of the partition tape, and young records reserve slots. -/


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.Chronological

variable {Y : Type*} [MetricSpace Y]

lemma age_mono (center : ℕ → Y) {I J : Finset ℕ} {R S : ℝ} (hIJ : I ⊆ J)
    (hRS : R ≤ S) (i : ℕ) : age center I R i ≤ age center J S i := by
  classical
  apply card_le_card
  intro j hj
  obtain ⟨hj,hij,hd⟩ := mem_filter.mp hj
  exact mem_filter.mpr ⟨hIJ hj,hij,hd.trans hRS⟩

/-- Adding the next insertion increments precisely neighbouring old entries. -/
lemma age_insert (center : ℕ → Y) (I : Finset ℕ) (R : ℝ) {i t : ℕ}
    (ht : t ∉ I) (hit : i < t) :
    age center (insert t I) R i = age center I R i +
      if dist (center i) (center t) ≤ R then 1 else 0 := by
  classical
  unfold age
  rw [filter_insert]
  by_cases hd : dist (center i) (center t) ≤ R
  · rw [ite_eq_left ⟨hit, hd⟩, ite_eq_left hd,
      card_insert_of_notMem (fun hm => ht (mem_filter.mp hm).1)]
  · rw [ite_eq_right (fun h => hd h.2), ite_eq_right hd]
    simp

lemma age_new (center : ℕ → Y) (I : Finset ℕ) (R : ℝ) {t : ℕ}
    (ht : ∀ i ∈ I, i < t) : age center (insert t I) R t = 0 := by
  classical
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨hi,hti,_⟩ := mem_filter.mp hi
  rcases mem_insert.mp hi with rfl | hi
  · omega
  · have := ht i hi
    omega

lemma schedule_before (request : ℕ → Y) (r : ℝ) (K : ℕ) (qualifies : ℕ → Prop)
    (t : ℕ) : ∀ i ∈ schedule request r K qualifies t, i < t := by
  classical
  induction t with
  | zero => simp [schedule]
  | succ t ih =>
      intro i hi
      simp only [schedule] at hi
      split_ifs at hi with h
      · rcases mem_insert.mp hi with rfl | hi
        · omega
        · exact (ih i hi).trans (Nat.lt_succ_self t)
      · exact (ih i hi).trans (Nat.lt_succ_self t)

lemma qualified_coverage (request : ℕ → Y) (r : ℝ) (K : ℕ) (qualifies : ℕ → Prop)
    (t : ℕ) (hK : 0 < K) (hr : 0 ≤ r) (hq : qualifies t) :
    ∃ i ∈ schedule request r K qualifies (t+1),
      age request (schedule request r K qualifies (t+1)) (20*r) i < K ∧
      dist (request i) (request t) ≤ r/2 := by
  classical
  let I := schedule request r K qualifies t
  by_cases ht : insertTest request I r K t (qualifies t)
  · have he : schedule request r K qualifies (t+1) = insert t I := by
      simp only [schedule]
      exact ite_eq_left ht
    rw [he]
    refine ⟨t, mem_insert_self _ _, ?_, ?_⟩
    · rw [age_new request I (20*r) (schedule_before request r K qualifies t)]
      exact hK
    · simp only [dist_self]
      positivity
  · have he : schedule request r K qualifies (t+1) = I := by
      simp only [schedule]
      exact ite_eq_right ht
    rw [he]
    have hh : ∃ i ∈ I, age request I (20*r) i < K ∧ dist (request i) (request t) ≤ r/2 := by
      by_contra hn
      exact ht ⟨hq,hn⟩
    exact hh

end KServer.Chronological

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.SparseFirstHit
open PartitionProbabilities FiniteBallLaw Chronological
attribute [local instance] Classical.propDecidable Classical.decEq

/-- An error is paid only on indices that can hit a queried point.  This
permits a preallocated horizon-size tape without a horizon-size bound. -/
theorem sparse_bound {n : ℕ} {Ω : Fin n → Type*} [∀ i, Fintype (Ω i)]
    {hit sep : ∀ i, Ω i → Prop} (w : ∀ i, Ω i → ℝ)
    (hw : ∀ i a, 0 ≤ w i a) (hw1 : ∀ i, ∑ a, w i a=1)
    (hsep : ∀ i a, sep i a → hit i a) {c : ℝ} (ε : Fin n → ℝ)
    (hc : 0 ≤ c) (hε : ∀ i, 0 ≤ ε i)
    (hm : ∀ i, (∑ a, if sep i a then w i a else 0) ≤
      c*((∑ a, if hit i a then w i a else 0)+ε i)) :
    probability w (firstSeparation hit sep) ≤ c*(1+∑ i, ε i) := by
  let p : Fin n → ℝ := fun i => ∑ a, if hit i a then w i a else 0
  have hp (i : Fin n) : p i ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨sum_nonneg (fun a _ => ?_), ?_⟩
    · split_ifs
      · exact hw i a
      · rfl
    · calc p i ≤ ∑ a, w i a := by
             apply sum_le_sum
             intro a _
             split_ifs
             · rfl
             · exact hw i a
           _ = 1 := hw1 i
  let q : Fin n → ℝ := fun i => ∏ j ∈ univ.filter (fun j : Fin n => j < i), (1-p j)
  have hq (i : Fin n) : q i ∈ Set.Icc (0:ℝ) 1 := by
    exact ⟨prod_nonneg (fun j _ => sub_nonneg.mpr (hp j).2),
      prod_le_one (fun index _ => sub_nonneg.mpr (hp index).2)
        (fun index _ => by linarith [(hp index).1])⟩
  have hb (i : Fin n) : probability w (firstAt hit sep i) ≤
      c*(probability w (firstAt hit hit i)+ε i) := by
    rw [firstAt_probability w hw1,firstAt_probability w hw1]
    change (∑ a, if sep i a then w i a else 0)*q i ≤ c*(p i*q i+ε i)
    calc _ ≤ (c*(p i+ε i))*q i := mul_le_mul_of_nonneg_right (hm i) (hq i).1
         _ ≤ _ := by nlinarith only [mul_nonneg hc (mul_nonneg (hε i) (by linarith [(hq i).2] : 0 ≤ 1-q i))]
  calc probability w (firstSeparation hit sep) = ∑ i, probability w (firstAt hit sep i) :=
         firstSeparation_probability hsep w
       _ ≤ ∑ i, c*(probability w (firstAt hit hit i)+ε i) := sum_le_sum (fun i _ => hb i)
       _ = c*(probability w (firstSeparation hit hit)+∑ i, ε i) := by
         rw [← mul_sum,sum_add_distrib,← firstSeparation_probability (fun _ _ h => h) w]
       _ ≤ c*(1+∑ i, ε i) := mul_le_mul_of_nonneg_left
         (add_le_add (probability_range hw hw1 _).2 le_rfl) hc

variable {Y : Type*} [Fintype Y] [MetricSpace Y] {H : ℕ}

lemma absent_hit {r : ℝ} (hr : 0 < r) (c x y : Y) (d : Outcome Y r)
    (h : ¬min (dist c x) (dist c y) ≤ 2*r) : ¬hit r c x y d := by
  intro hh
  exact h ((hit_min _ _ _ _ _).mp hh |>.trans (radius_range hr d).2)

/-- All previous insertion ordinals, with nonpresent records literally
suppressed.  Only potential hitters contribute the truncation error. -/
theorem present_bound {lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r)
    (center : Fin H → Y) (present : Fin H → Prop) (x y : Y) :
    probability (fun _ : Fin H => law (Y:=Y) lam r)
      (firstSeparation (fun j d => present j ∧ hit r (center j) x y d)
        (fun j d => present j ∧ separates r (center j) x y d)) ≤
      (lam*dist x y/r)*(1+(1/(Real.exp lam-1))*(candidates r center present x y).card) := by
  let ε : Fin H → ℝ := fun j => if j∈candidates r center present x y then 1/(Real.exp lam-1) else 0
  have heps : ∑ j, ε j=(1/(Real.exp lam-1))*(candidates r center present x y).card := by
    simp [ε,sum_ite_mem,mul_comm]
  rw [←heps]
  apply sparse_bound
  · exact fun _ => law_nonneg hlam hr
  · exact fun _ => law_sum hlam hr
  · exact fun j d h => ⟨h.1,separation_hit _ _ _ _ _ h.2⟩
  · positivity
  · intro j
    dsimp [ε]
    split_ifs
    · exact div_nonneg zero_le_one (by linarith [Real.one_lt_exp_iff.mpr hlam])
    · rfl
  · intro j
    by_cases hp : present j
    · simp only [hp,true_and]
      by_cases hd : min (dist (center j) x) (dist (center j) y) ≤ 2*r
      · have hm : j∈candidates r center present x y := mem_filter.mpr ⟨mem_univ _,hp,hd⟩
        simpa only [ε,ite_eq_left hm] using one_ball_bound hlam hr (center j) x y
      · have hhit (d : Outcome Y r) : ¬hit r (center j) x y d := absent_hit hr _ _ _ _ hd
        have hsep (d : Outcome Y r) : ¬separates r (center j) x y d := fun h=>hhit d (separation_hit _ _ _ _ _ h)
        have hm : j∉candidates r center present x y := fun hh => hd (mem_filter.mp hh).2.2
        simp [hhit,hsep,ε,hm]
    · simp [hp,ε,candidates]

omit [Fintype Y] in
lemma close_centers {r : ℝ} (hr : 0 ≤ r) {c d x y : Y} (hxy : dist x y ≤ r)
    (hc : min (dist c x) (dist c y) ≤ 2*r) (hd : min (dist d x) (dist d y) ≤ 2*r) :
    dist c d ≤ 20*r := by
  rcases min_le_iff.mp hc with hc|hc <;> rcases min_le_iff.mp hd with hd|hd
  · have ht := dist_triangle c x d
    rw [dist_comm x d] at ht
    linarith
  · have ht := dist_triangle4 c x y d
    rw [dist_comm y d] at ht
    linarith
  · have ht := dist_triangle4 c y x d
    rw [dist_comm y x,dist_comm x d] at ht
    linarith
  · have ht := dist_triangle c y d
    rw [dist_comm y d] at ht
    linarith

omit [Fintype Y] in
lemma candidate_count {r : ℝ} (hr : 0 ≤ r) (center : ℕ → Y) (I : Finset ℕ)
    (present : Fin H → Prop) {K : ℕ}
    (hp : ∀ i, present i → (i:ℕ)∈I ∧ age center I (20*r) i<K^2)
    (x y : Y) (hxy : dist x y ≤ r) :
    (candidates r (fun i : Fin H => center i) present x y).card ≤ K^2 := by
  let S : Finset (Fin H) := candidates r (fun i : Fin H => center i) present x y
  have hinj : Function.Injective (fun i : Fin H => (i:ℕ)) := Fin.val_injective
  have he : (S.image (fun i : Fin H => (i:ℕ))).card=S.card := card_image_of_injective _ hinj
  rw [←he]
  apply local_age_count center I _ (20*r) (K^2)
  · intro j hj
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hj
    exact (hp i (mem_filter.mp hi).2.1).1
  · intro j hj
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hj
    exact (hp i (mem_filter.mp hi).2.1).2
  · intro i hi j hj
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hi
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hj
    exact close_centers hr hxy (mem_filter.mp ha).2.2 (mem_filter.mp hb).2.2

/-- Conditional on any actual presence pattern, the horizon-size radius tape
has the stated K²-independent first-hit bound, by the literal age count. -/
theorem chronological_roster_bound {K : ℕ} (hK : 1 ≤ K) {r : ℝ} (hr : 0 < r)
    (center : ℕ → Y) (I : Finset ℕ) (present : Fin H → Prop)
    (hp : ∀ i, present i → (i:ℕ)∈I ∧ age center I (20*r) i<K^2)
    (x y : Y) (hxy : dist x y ≤ r) :
    probability (fun _ : Fin H => law (Y:=Y) (Real.log (1+(K:ℝ)^2)) r)
      (firstSeparation (fun j d => present j ∧ hit r (center j) x y d)
        (fun j d => present j ∧ separates r (center j) x y d)) ≤
      2*Real.log (1+(K:ℝ)^2)*dist x y/r := by
  have hl := lambda_pos hK
  refine (present_bound hl hr (fun i : Fin H=>center i) present x y).trans ?_
  have hk : (0:ℝ) < K := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
  have hn : ((candidates r (fun i : Fin H=>center i) present x y).card:ℝ) ≤ (K:ℝ)^2 := by
    exact_mod_cast candidate_count hr.le center I present hp x y hxy
  rw [Real.exp_log (by positivity : 0 < 1+(K:ℝ)^2),add_sub_cancel_left]
  have hfrac : (1/(K:ℝ)^2)*((candidates r (fun i : Fin H=>center i) present x y).card:ℝ) ≤ 1 := by
    rw [one_div,mul_comm,←div_eq_mul_inv]
    exact (div_le_one (sq_pos_of_pos hk)).mpr hn
  have hc : 0 ≤ Real.log (1+(K:ℝ)^2)*dist x y/r := by positivity
  calc _ ≤ (Real.log (1+(K:ℝ)^2)*dist x y/r)*2 :=
      mul_le_mul_of_nonneg_left (by linarith) hc
    _ = _ := by ring

end KServer.SparseFirstHit

end


/-! The distinct actual and auxiliary lifetimes of §07.  These estimates are
uniform in the horizon and in every fixed chronological insertion schedule.
Compulsory-retirement tails are unconditional, as required by the source. -/
noncomputable section
open scoped BigOperators
namespace KServer.RosterLifetimes

lemma survive_exp {q : ℝ} (hq : q ≤ 1) (N : ℕ) :
    survive q N ≤ Real.exp (-(q*N)) := by
  calc (1-q)^N ≤ (Real.exp (-q))^N :=
        pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg q) N
       _ = Real.exp (-(q*N)) := by rw [← Real.exp_nat_mul]; congr 1; ring

lemma cubic_decay {x : ℝ} (hx : 0 ≤ x) : x^3*Real.exp (-x) ≤ 6 := by
  have h := Real.pow_div_factorial_le_exp x hx 3
  norm_num at h
  have hm := mul_le_mul_of_nonneg_right h (Real.exp_nonneg (-x))
  have he : Real.exp x*Real.exp (-x)=1 := by rw [← Real.exp_add]; simp
  rw [he] at hm
  linarith

/-- Explicit uniform version of K² exp(-(K-1))=O(1/K). -/
lemma actual_exponential_bound {x : ℝ} (hx : 2 ≤ x) :
    x^2*Real.exp (-(x-1)) ≤ 48/x := by
  have hp : 0 < x := by linarith
  rw [le_div_iff₀ hp]
  have hc := cubic_decay (x := x-1) (by linarith)
  have hpow : x^3 ≤ 8*(x-1)^3 := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ x) (by linarith : x ≤ 2*(x-1)) 3
    nlinarith only [h]
  have hm := mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg (-(x-1)))
  nlinarith only [hc,hm]

/-- Explicit uniform auxiliary tail estimate. The denominator really is √K,
not K; the two tapes are never identified. -/
lemma short_exponential_bound {x : ℝ} (hx : 2 ≤ x) :
    x*Real.exp (-((x-1)/Real.sqrt x)) ≤ 48/Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith
  have hy : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hs : (Real.sqrt x)^2=x := Real.sq_sqrt hx0
  have hd : Real.sqrt x/2 ≤ (x-1)/Real.sqrt x := by
    rw [le_div_iff₀ hy]
    nlinarith only [hs,hx]
  have he : Real.exp (-((x-1)/Real.sqrt x)) ≤ Real.exp (-(Real.sqrt x/2)) :=
    Real.exp_le_exp.mpr (neg_le_neg hd)
  have hc := cubic_decay (x := Real.sqrt x/2) (by positivity)
  have hc' : (Real.sqrt x)^3*Real.exp (-(Real.sqrt x/2)) ≤ 48 := by
    nlinarith only [hc]
  rw [le_div_iff₀ hy]
  calc x*Real.exp (-((x-1)/Real.sqrt x))*Real.sqrt x ≤
        x*Real.exp (-(Real.sqrt x/2))*Real.sqrt x := by gcongr
       _ = (Real.sqrt x)^3*Real.exp (-(Real.sqrt x/2)) := by calc
         _ = (Real.sqrt x)^2*Real.exp (-(Real.sqrt x/2))*Real.sqrt x := by rw [hs]
         _ = _ := by ring
       _ ≤ 48 := hc'

lemma short_new {K : ℕ} (hK : 0<K) : shortPresence K 0=1 := by
  simp [shortPresence,hK,survive]

/-- The source unconditional actual-first-coverer retirement estimate,
including both stochastic and compulsory terms.  The factor K² is the
geometric roster count proved from chronological ages, not the total history. -/
theorem actual_retirement_bound (K : ℕ) (hK : 2 ≤ K) :
    1/(K:ℝ)+(K:ℝ)^2*survive (1/(K:ℝ)) (K^2-K) ≤ 49/(K:ℝ) := by
  have hKr : (2:ℝ) ≤ K := by exact_mod_cast hK
  have hKp : (0:ℝ) < K := by linarith
  have hKK : K ≤ K^2 := by nlinarith
  have hcast : ((K^2-K : ℕ):ℝ)=(K:ℝ)^2-K := by rw [Nat.cast_sub hKK,Nat.cast_pow]
  have hs := survive_exp (q := 1/(K:ℝ)) ((div_le_one hKp).mpr (by linarith)) (K^2-K)
  rw [hcast] at hs
  have he : -(1/(K:ℝ)*((K:ℝ)^2-K)) = -((K:ℝ)-1) := by field_simp
  rw [he] at hs
  have hb := (mul_le_mul_of_nonneg_left hs (sq_nonneg (K:ℝ))).trans (actual_exponential_bound hKr)
  have hsum := add_le_add_left hb (1/(K:ℝ))
  convert hsum using 1 <;> first | rfl | ring

/-- The auxiliary ramp can increase by at most this amount; its complete
retirement calculation has a uniform 49/√K bound. -/
theorem short_retirement_bound (K : ℕ) (hK : 2 ≤ K) :
    1/Real.sqrt K+(K:ℝ)*survive (1/Real.sqrt K) (K-1) ≤ 49/Real.sqrt K := by
  have hKr : (2:ℝ) ≤ K := by exact_mod_cast hK
  have hKp : (0:ℝ) < K := by linarith
  have hy : 0 < Real.sqrt K := Real.sqrt_pos.mpr hKp
  have hy1 : 1 ≤ Real.sqrt K := by
    exact (Real.one_le_sqrt).mpr (by linarith)
  have hcast : ((K-1 : ℕ):ℝ)=(K:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  have hs := survive_exp (q := 1/Real.sqrt K) ((div_le_one hy).mpr hy1) (K-1)
  rw [hcast] at hs
  have he : -(1/Real.sqrt K*((K:ℝ)-1)) = -(((K:ℝ)-1)/Real.sqrt K) := by ring
  rw [he] at hs
  have hb := (mul_le_mul_of_nonneg_left hs hKp.le).trans (short_exponential_bound hKr)
  have hsum := add_le_add_left hb (1/Real.sqrt K)
  convert hsum using 1 <;> first | rfl | ring

end KServer.RosterLifetimes

end


/-! Literal actual roster lifetime tape, separate from the auxiliary short
roster.  Every construction below is finite at the prescribed horizon. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualRoster
open RosterLifetimes FiniteSurvival Chronological FiniteBallLaw PartitionProbabilities
attribute [local instance] Classical.propDecidable Classical.decEq

lemma alive_young {K a : ℕ} {d : Lifetime K} (h : alive K a d) : a<K^2 := by
  rcases h with h|h
  · have hk : K ≤ K^2 := by nlinarith [Nat.zero_le K]
    exact h.trans_le hk
  · exact h.trans_lt d.isLt

lemma alive_certain {K a : ℕ} (ha : a<K) (d : Lifetime K) : alive K a d := Or.inl ha

lemma alive_probability {K : ℕ} (hK : 1 ≤ K) (a : ℕ) :
    (∑ d : Lifetime K, if alive K a d then lifetimeLaw K d else 0)=actualPresence K a := by
  by_cases ha : a < K
  · simp only [alive,ha,true_or,ite_true,actual_guaranteed ha]
    exact lifetime_sum hK
  · by_cases hc : a ≤ K^2
    · simp only [alive,ha,false_or]
      have hv := probability_living (actualPresence K) (K^2) a hc
      rw [actual_cutoff le_rfl,sub_zero] at hv
      calc (∑ d : Lifetime K, if a≤(d:ℕ) then lifetimeLaw K d else 0)
          = FiniteSurvival.probability (actualPresence K) (fun d : Fin (K^2)=>a≤(d:ℕ)) := by
            unfold FiniteSurvival.probability
            apply sum_congr rfl
            intro d _
            by_cases hd : a≤(d:ℕ) <;> simp [hd,lifetimeLaw]
           _ = actualPresence K a := hv
    · rw [actual_cutoff (le_of_lt (lt_of_not_ge hc))]
      apply sum_eq_zero
      intro d _
      exact ite_eq_right (fun h=>hc (alive_young h).le)

lemma alive_antitone (K : ℕ) (d : Lifetime K) {a b : ℕ} (hab : a≤b) (h : alive K b d) : alive K a d := by
  rcases h with h|h
  · exact Or.inl (lt_of_le_of_lt hab h)
  · exact Or.inr (hab.trans h)

lemma death_probability {K : ℕ} (hK : 1 ≤ K) (a : ℕ) :
    (∑ d : Lifetime K, if alive K a d ∧ ¬alive K (a+1) d then lifetimeLaw K d else 0)=
      actualPresence K a-actualPresence K (a+1) := by
  rw [←alive_probability hK a,←alive_probability hK (a+1),←sum_sub_distrib]
  apply sum_congr rfl
  intro d _
  by_cases hn : alive K (a+1) d
  · have ho := alive_antitone K d (Nat.le_succ _) hn
    simp [hn,ho]
  · simp [hn]

/-- Before the compulsory age, the inverse-tail tape has exactly the source
hazard 1/K once independent trials have begun. -/
lemma ordinary_death_bound {K a : ℕ} (hK : 1 ≤ K) (ha : a+1<K^2) :
    actualPresence K a-actualPresence K (a+1) ≤ (1/(K:ℝ))*actualPresence K a := by
  by_cases hc : a+1<K
  · rw [actual_guaranteed hc,actual_guaranteed (by omega)]
    have hq := (rate_range hK).1
    simpa only [sub_self,mul_one] using hq
  · by_cases hb : a<K
    · have he : a+1=K := by omega
      rw [actual_guaranteed hb]
      simp only [actualPresence,he,lt_self_iff_false,ite_false,show K<K^2 from he ▸ ha,ite_true,
        Nat.sub_self,zero_add,survive,pow_one,mul_one]
      ring_nf
      rfl
    · have hab : a<K^2 := by omega
      have hn : ¬a+1<K := by omega
      simp only [actualPresence,ite_eq_right hb,ite_eq_left hab,ite_eq_right hn,ite_eq_left ha]
      have he : a+1-K+1=(a-K+1)+1 := by omega
      rw [he]
      simp only [survive,pow_succ]
      nlinarith

variable {Y : Type*} [MetricSpace Y] {H K : ℕ}

lemma present_young (center : ℕ → Y) (I : Finset ℕ) (r : ℝ) (tape : Fin H → Lifetime K) (i : Fin H)
    (hp : present center I r tape i) : (i:ℕ)∈I ∧ age center I (20*r) i<K^2 :=
  ⟨hp.1,alive_young hp.2⟩

lemma young_present (center : ℕ → Y) (I : Finset ℕ) (r : ℝ) (tape : Fin H → Lifetime K) (i : Fin H)
    (hi : (i:ℕ)∈I) (ha : age center I (20*r) i<K) : present center I r tape i :=
  ⟨hi,alive_certain ha _⟩

section Radius
variable [Fintype Y]

lemma first_some_iff (center : ℕ → Y) (I : Finset ℕ) (r : ℝ) (life : Fin H → Lifetime K)
    (radii : Fin H → Outcome Y r) (x : Y) (i : Fin H) :
    first center I r life radii x=some i ↔
      covered center I r life radii x i ∧ ∀ j < i,¬covered center I r life radii x j := by
  dsimp only [first]
  split_ifs with h
  · constructor
    · intro he
      have hi : (univ.filter (covered center I r life radii x)).min' h=i := Option.some.inj he
      constructor
      · rw [←hi]
        exact (mem_filter.mp (min'_mem _ _)).2
      · intro j hj hc
        have hmin := min'_le (univ.filter (covered center I r life radii x)) j (mem_filter.mpr ⟨mem_univ _,hc⟩)
        rw [hi] at hmin
        exact (not_le_of_gt hj) hmin
    · rintro ⟨hi,hbefore⟩
      congr 1
      apply le_antisymm
      · exact min'_le _ _ (mem_filter.mpr ⟨mem_univ _,hi⟩)
      · by_contra hh
        exact hbefore _ (lt_of_not_ge hh) (mem_filter.mp (min'_mem _ _)).2
  · constructor
    · simp
    · intro hi
      exact False.elim (h ⟨i,mem_filter.mpr ⟨mem_univ _,hi.1⟩⟩)

lemma first_none_iff (center : ℕ → Y) (I : Finset ℕ) (r : ℝ) (life : Fin H → Lifetime K)
    (radii : Fin H → Outcome Y r) (x : Y) :
    first center I r life radii x=none ↔ ∀ i,¬covered center I r life radii x i := by
  simp [first,Finset.not_nonempty_iff_eq_empty,Finset.filter_eq_empty_iff]

/-- Deterministic source coverage on a qualifying insertion step, including
zero-weight lifetime outcomes. -/
lemma qualified_covered (center : ℕ → Y) {r : ℝ} (hr : 0 < r) (hK : 0<K)
    (qualifies : ℕ → Prop) (t : ℕ) (ht : t<H) (hq : qualifies t)
    (life : Fin H → Lifetime K) (radii : Fin H → Outcome Y r) :
    ∃ i, covered center (schedule center r K qualifies (t+1)) r life radii (center t) i := by
  obtain ⟨i,hi,ha,hd⟩ := qualified_coverage center r K qualifies t hK hr.le hq
  have hiH : i < H := (schedule_before center r K qualifies (t+1) i hi).trans_le (by omega)
  refine ⟨⟨i,hiH⟩,young_present _ _ _ _ _ hi ha,?_⟩
  exact hd.trans ((by linarith : r/2 ≤ r).trans (radius_range hr _).1)

/-- Actual fixed-schedule first-hit probability under the complete finite
radius tape, with the independently sampled lifetime tape fixed arbitrarily. -/
theorem first_hit_estimate (center : ℕ → Y) (I : Finset ℕ) {r : ℝ} (hr : 0 < r)
    (hK : 1 ≤ K) (life : Fin H → Lifetime K) (x y : Y) (hxy : dist x y ≤ r) :
    PartitionProbabilities.probability (fun _ : Fin H => law (Y:=Y) (Real.log (1+(K:ℝ)^2)) r)
      (firstSeparation (fun j d => present center I r life j ∧ hit r (center j) x y d)
        (fun j d => present center I r life j ∧ separates r (center j) x y d)) ≤
      2*Real.log (1+(K:ℝ)^2)*dist x y/r :=
  SparseFirstHit.chronological_roster_bound hK hr center I _ (present_young center I r life) x y hxy

end Radius
end KServer.ActualRoster

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Rosters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualRoster
open Chronological FiniteBallLaw PartitionProbabilities
attribute [local instance] Classical.propDecidable Classical.decEq

lemma probability_mono {J : Type*} [Fintype J] {Ω : J → Type*} [∀ j,Fintype (Ω j)]
    {w : ∀ j, Ω j → ℝ} (hw : ∀ j a, 0 ≤ w j a) {E F : (∀ j, Ω j) → Prop}
    (hEF : ∀ o, E o → F o) : PartitionProbabilities.probability w E ≤ PartitionProbabilities.probability w F := by
  unfold PartitionProbabilities.probability
  apply sum_le_sum
  intro o _
  by_cases he : E o
  · simp [he,hEF o he]
  · simp only [ite_eq_right he]
    split_ifs
    · exact productWeight_nonneg hw o
    · rfl

variable {Y : Type*} [MetricSpace Y] [Fintype Y] {H K : ℕ}

lemma separates_iff_cover (center : ℕ → Y) (I : Finset ℕ) (r : ℝ)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (x y : Y) (i : Fin H) :
    (present center I r life i ∧ separates r (center i) x y (rad i)) ↔
      (covered center I r life rad x i ∧ ¬covered center I r life rad y i) ∨
      (covered center I r life rad y i ∧ ¬covered center I r life rad x i) := by
  simp only [covered,separates]
  constructor
  · rintro ⟨hp,he|he⟩
    · exact Or.inl ⟨⟨hp,he.1⟩,fun hh=>not_le_of_gt he.2 hh.2⟩
    · exact Or.inr ⟨⟨hp,he.1⟩,fun hh=>not_le_of_gt he.2 hh.2⟩
  · rintro (⟨⟨hp,hx⟩,hy⟩|⟨⟨hp,hy⟩,hx⟩)
    · exact ⟨hp,Or.inl ⟨hx,lt_of_not_ge (fun h=>hy ⟨hp,h⟩)⟩⟩
    · exact ⟨hp,Or.inr ⟨hy,lt_of_not_ge (fun h=>hx ⟨hp,h⟩)⟩⟩

lemma hit_iff_cover (center : ℕ → Y) (I : Finset ℕ) (r : ℝ)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (x y : Y) (i : Fin H) :
    (present center I r life i ∧ hit r (center i) x y (rad i)) ↔
      covered center I r life rad x i ∨ covered center I r life rad y i := by
  exact and_or_left

/-- The first-hit event is literally the event that the actual two chronological
keys differ, including absence on either or both sides. -/
theorem first_ne_iff (center : ℕ → Y) (I : Finset ℕ) (r : ℝ)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (x y : Y) :
    first center I r life rad x ≠ first center I r life rad y ↔
      firstSeparation (fun j d=>present center I r life j ∧ hit r (center j) x y d)
        (fun j d=>present center I r life j ∧ separates r (center j) x y d) rad := by
  constructor
  · intro hne
    cases hx : first center I r life rad x with
    | none =>
      have hnx := (first_none_iff _ _ _ _ _ _).mp hx
      cases hy : first center I r life rad y with
      | none => exact False.elim (hne (hx.trans hy.symm))
      | some i =>
        obtain ⟨hi,hbefore⟩ := (first_some_iff _ _ _ _ _ _ _).mp hy
        refine ⟨i,(separates_iff_cover _ _ _ _ _ _ _ _).mpr (Or.inr ⟨hi,hnx i⟩),?_⟩
        intro j hj hh
        rcases (hit_iff_cover _ _ _ _ _ _ _ _).mp hh with hh|hh
        · exact hnx j hh
        · exact hbefore j hj hh
    | some i =>
      obtain ⟨hi,hbefore⟩ := (first_some_iff _ _ _ _ _ _ _).mp hx
      cases hy : first center I r life rad y with
      | none =>
        have hny := (first_none_iff _ _ _ _ _ _).mp hy
        refine ⟨i,(separates_iff_cover _ _ _ _ _ _ _ _).mpr (Or.inl ⟨hi,hny i⟩),?_⟩
        intro j hj hh
        rcases (hit_iff_cover _ _ _ _ _ _ _ _).mp hh with hh|hh
        · exact hbefore j hj hh
        · exact hny j hh
      | some j =>
        obtain ⟨hj,hbeforej⟩ := (first_some_iff _ _ _ _ _ _ _).mp hy
        have hneij : i≠j := fun he=>hne (hx.trans (by rw [he,←hy]))
        rcases lt_or_gt_of_ne hneij with hij|hji
        · refine ⟨i,(separates_iff_cover _ _ _ _ _ _ _ _).mpr (Or.inl ⟨hi,hbeforej i hij⟩),?_⟩
          intro a ha hh
          rcases (hit_iff_cover _ _ _ _ _ _ _ _).mp hh with hh|hh
          · exact hbefore a ha hh
          · exact hbeforej a (ha.trans hij) hh
        · refine ⟨j,(separates_iff_cover _ _ _ _ _ _ _ _).mpr (Or.inr ⟨hj,hbefore j hji⟩),?_⟩
          intro a ha hh
          rcases (hit_iff_cover _ _ _ _ _ _ _ _).mp hh with hh|hh
          · exact hbefore a (ha.trans hji) hh
          · exact hbeforej a ha hh
  · rintro ⟨i,hsep,hbefore⟩ heq
    have hn (j : Fin H) (hj : j < i) : ¬covered center I r life rad x j ∧ ¬covered center I r life rad y j := by
      exact ⟨fun h=>hbefore j hj ((hit_iff_cover _ _ _ _ _ _ _ _).mpr (Or.inl h)),
        fun h=>hbefore j hj ((hit_iff_cover _ _ _ _ _ _ _ _).mpr (Or.inr h))⟩
    rcases (separates_iff_cover _ _ _ _ _ _ _ _).mp hsep with ⟨hx,hy⟩|⟨hy,hx⟩
    · have hfirst := (first_some_iff _ _ _ _ _ _ _).mpr ⟨hx,fun j hj=>(hn j hj).1⟩
      rw [heq] at hfirst
      exact hy ((first_some_iff _ _ _ _ _ _ _).mp hfirst).1
    · have hfirst := (first_some_iff _ _ _ _ _ _ _).mpr ⟨hy,fun j hj=>(hn j hj).2⟩
      rw [←heq] at hfirst
      exact hx ((first_some_iff _ _ _ _ _ _ _).mp hfirst).1

/-- Uniform-in-history spatial bound for the actual fixed-lifetime keys. -/
theorem spatial_bound (center : ℕ → Y) (I : Finset ℕ) {r : ℝ} (hr : 0 < r)
    (hK : 1 ≤ K) (life : Fin H → Lifetime K) (x y : Y) (hxy : dist x y ≤ r) :
    PartitionProbabilities.probability (fun _ : Fin H=>law (Y:=Y) (Real.log (1+(K:ℝ)^2)) r)
      (fun rad=>first center I r life rad x ≠ first center I r life rad y) ≤
      2*Real.log (1+(K:ℝ)^2)*dist x y/r := by
  have he : (fun rad=>first center I r life rad x ≠ first center I r life rad y)=
      firstSeparation (fun j d=>present center I r life j ∧ hit r (center j) x y d)
        (fun j d=>present center I r life j ∧ separates r (center j) x y d) := by
    funext rad
    exact propext (first_ne_iff _ _ _ _ _ _ _)
  rw [he]
  exact first_hit_estimate center I hr hK life x y hxy

end KServer.ActualRoster

end


/-! Heavy keys of the constructed finite schedule and their exact full-input
spatial estimate; label reuse does not impose or assume a probability law. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavyKeys
open HeavyCenters HeavySchedule HeavyLabels FiniteExperiment PartitionProbabilities
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y]

lemma hit_unique {r : ℝ} (hr : 0 < r) {C : Finset Y} {rad : Y → ℝ} {x a b : Y}
    (hC : (C:Set Y).Pairwise (fun a b=>100*r<dist a b))
    (hrad : ∀ a∈C,rad a≤20*r) (ha : a∈hits C rad x) (hb : b∈hits C rad x) : a=b := by
  by_contra hn
  obtain ⟨ha,hax⟩:=mem_filter.mp ha
  obtain ⟨hb,hbx⟩:=mem_filter.mp hb
  have hd:=hC ha hb hn
  have ht:=dist_triangle a x b
  rw [dist_comm x b] at ht
  linarith [hrad a ha,hrad b hb]

lemma centerKey_some {r : ℝ} (hr : 0 < r) {C : Finset Y} {rad : Y → ℝ} {x a : Y}
    (hC : (C:Set Y).Pairwise (fun a b=>100*r<dist a b))
    (hrad : ∀ a∈C,rad a≤20*r) :
    centerKey C rad x=some a ↔ a∈C ∧ dist a x ≤ rad a := by
  unfold centerKey
  split_ifs with h
  · constructor
    · intro he
      have he':=Option.some.inj he
      rw [←he']
      exact mem_filter.mp h.choose_spec
    · intro ha
      rw [hit_unique hr hC hrad h.choose_spec (mem_filter.mpr ha)]
  · simp only [false_iff,not_and]
    intro ha hx
    exact h ⟨a,mem_filter.mpr ⟨ha,hx⟩⟩

lemma centerKey_none (C : Finset Y) (rad : Y → ℝ) (x : Y) :
    centerKey C rad x=none ↔ ∀ a∈C,rad a<dist a x := by
  unfold centerKey
  split_ifs with h
  · simp only [false_iff,not_forall]
    obtain ⟨a,ha⟩:=h
    obtain ⟨ha,hax⟩:=mem_filter.mp ha
    exact ⟨a,ha,not_lt_of_ge hax⟩
  · simp only [true_iff]
    intro a ha
    exact lt_of_not_ge (fun hx=>h ⟨a,mem_filter.mpr ⟨ha,hx⟩⟩)

lemma candidate_unique {C : Finset Y} {r : ℝ} (hr : 0 < r) {x y a b : Y}
    (hxy : 4*dist x y < r) (hC : (C:Set Y).Pairwise (fun a b=>100*r<dist a b))
    (ha : a∈candidates C r x y) (hb : b∈candidates C r x y) : a=b := by
  by_contra hn
  obtain ⟨ha,hax|hay⟩:=mem_filter.mp ha <;>
    obtain ⟨hb,hbx|hby⟩:=mem_filter.mp hb
  all_goals
    have hd:=hC ha hb hn
    have h1:=dist_triangle a x b
    have h2:=dist_triangle a y b
    have h3:=dist_triangle a x y
    have h4:=dist_triangle a y x
    have h5:=dist_triangle x y b
    have h6:=dist_triangle y x b
    simp only [dist_comm x b,dist_comm y b,dist_comm y x] at h1 h2 h4 h5 h6
    linarith [dist_nonneg (x:=x) (y:=y)]

lemma ne_separates {C : Finset Y} {rad : Y → ℝ} {r : ℝ} (hr : 0 < r) {x y : Y}
    (hC : (C:Set Y).Pairwise (fun a b=>100*r<dist a b))
    (hrad : ∀ a∈C,rad a≤20*r) (hne : centerKey C rad x≠centerKey C rad y) :
    ∃ a∈candidates C r x y,
      (dist a x ≤ rad a ∧ rad a<dist a y) ∨ (dist a y ≤ rad a ∧ rad a<dist a x) := by
  cases hx : centerKey C rad x with
  | none =>
    cases hy : centerKey C rad y with
    | none => exact False.elim (hne (hx.trans hy.symm))
    | some a =>
      obtain ⟨ha,hay⟩:=(centerKey_some hr hC hrad).mp hy
      exact ⟨a,mem_filter.mpr ⟨ha,Or.inr (hay.trans (hrad a ha))⟩,
        Or.inr ⟨hay,(centerKey_none C rad x).mp hx a ha⟩⟩
  | some a =>
    obtain ⟨ha,hax⟩:=(centerKey_some hr hC hrad).mp hx
    refine ⟨a,mem_filter.mpr ⟨ha,Or.inl (hax.trans (hrad a ha))⟩,Or.inl ⟨hax,?_⟩⟩
    apply lt_of_not_ge
    intro hay
    exact hne (hx.trans ((centerKey_some hr hC hrad).mpr ⟨ha,hay⟩).symm)

lemma cylinder {I Ω : Type*} [Fintype I] [Fintype Ω] (w : I → Ω → ℝ)
    (hsum : ∀ i,∑ a,w i a=1) (i : I) (E : Ω → Prop) :
    probability w (fun o=>E (o i))=∑ a,if E a then w i a else 0 := by
  have he : (fun o : I → Ω=>E (o i))=(fun o=>∀ j,j=i → E (o j)) := by
    funext o
    exact propext ⟨fun h j hj=>by simpa only [hj] using h,fun h=>h i rfl⟩
  rw [he,rectangle_probability w (fun j a=>j=i → E a)]
  trans ∏ j, if j=i then (∑ a,if E a then w i a else 0) else 1
  · apply prod_congr rfl
    intro j _
    by_cases hj : j=i
    · subst j; simp only [true_implies,ite_eq_left]
    · simp only [hj,false_implies,ite_true,ite_false,hsum]
  · simp

variable [Fintype Y] {k H : ℕ} [NeZero k]

/-- The source's d/(4r) bound for the actual heavy key, conditioned only on
full input, with deterministic birth times and a genuine product radius tape. -/
theorem spatial_bound (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    {r : ℝ} (hr : 0 < r) (γ δ : ℝ) (σ : Fin H → Y) (t : ℕ) (x y : Y)
    (hxy : 4*dist x y < r) :
    probability (fun _ : Fin H=>FiniteUniform.law (Y:=Y) r)
      (fun tape=>key s law r γ δ σ tape t x≠key s law r γ δ σ tape t y)≤dist x y/(4*r) := by
  let C:=centers s law r γ δ σ t
  have hC:=(centers_separated s law r γ δ σ t)
  by_cases hn : (candidates C r x y).Nonempty
  · obtain ⟨a,ha⟩:=hn
    obtain ⟨i,hi,_,_⟩:=present_birth s law hr γ δ σ t a (mem_filter.mp ha).1
    have hsub := ActualRoster.probability_mono
      (fun (_ : Fin H) b=>FiniteUniform.law_nonneg hr b)
      (E:=fun tape=>key s law r γ δ σ tape t x≠key s law r γ δ σ tape t y)
      (F:=fun tape=>FiniteUniform.separates r a x y (tape i)) (by
        intro tape hne
        have hc : centerKey C (run s law r γ δ σ tape t).rad x≠
            centerKey C (run s law r γ δ σ tape t).rad y := by
          intro he; exact hne (congrArg (Option.map (run s law r γ δ σ tape t).label) he)
        obtain ⟨b,hb,hsep⟩:=ne_separates hr hC (fun b hb=>(run_valid s law hr γ δ σ tape t).1 b hb |>.2) hc
        have he:=candidate_unique hr hxy hC hb ha
        subst b
        rw [radius_birth,hi] at hsep
        exact hsep)
    have he:=cylinder (fun _ : Fin H=>FiniteUniform.law (Y:=Y) r)
      (fun _=>FiniteUniform.law_sum hr) i (FiniteUniform.separates r a x y)
    exact hsub.trans (he.le.trans (FiniteUniform.one_ball_bound hr a x y))
  · have he : ∀ tape,key s law r γ δ σ tape t x=key s law r γ δ σ tape t y := by
      intro tape
      apply congrArg (Option.map (run s law r γ δ σ tape t).label)
      by_contra hc
      obtain ⟨a,ha,_⟩:=ne_separates hr hC (fun b hb=>(run_valid s law hr γ δ σ tape t).1 b hb |>.2) hc
      exact hn ⟨a,ha⟩
    have hz : probability (fun _ : Fin H=>FiniteUniform.law (Y:=Y) r)
        (fun tape=>key s law r γ δ σ tape t x≠key s law r γ δ σ tape t y)=0 := by
      simp [probability,he]
    rw [hz]
    positivity
end KServer.HeavyKeys

end


/-! Finite independent short-lifetime expectations used only for the pilot
profile in §07. No adaptive independence is postulated: all equalities below
are identities of finite product sums. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.RosterExpectation
open PartitionProbabilities
attribute [local instance] Classical.propDecidable Classical.decEq

variable {I A B : Type*} [Fintype I] [Fintype A] [Fintype B]

lemma product_pushforward (w : I → A → ℝ) (φ : I → A → B) (f : (I → B) → ℝ) :
    (∑ o,productWeight w o*f (fun i => φ i (o i))) =
      ∑ b,productWeight (fun i b => ∑ a,if φ i a=b then w i a else 0) b*f b := by
  have he (b : I → B) : productWeight (fun i b => ∑ a,if φ i a=b then w i a else 0) b =
      ∑ o,if (fun i=>φ i (o i))=b then productWeight w o else 0 := by
    rw [productWeight,←rectangle_probability,probability]
    apply sum_congr rfl
    intro o _
    congr 1
    exact propext ⟨fun h=>funext h,fun h i=>congrFun h i⟩
  simp_rw [he,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro o _
  symm
  rw [sum_eq_single (fun i=>φ i (o i))]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

omit [Fintype B] in
lemma product_marginal (w : I → A → ℝ) (hw : ∀ i,∑ a,w i a=1)
    (i : I) (f : A → ℝ) :
    (∑ o,productWeight w o*f (o i))=∑ a,w i a*f a := by
  have he (o : I → A) : f (o i)=∏ j,if j=i then f (o j) else 1 := by simp
  simp_rw [he]
  rw [product_expectation w (fun j a => if j=i then f a else 1)]
  have hfac (j : I) : (∑ a,w j a*(if j=i then f a else 1))=
      if j=i then ∑ a,w i a*f a else 1 := by
    split_ifs with h
    · subst j; rfl
    · simpa using hw j
  simp_rw [hfac]
  simp

lemma bernoulli_sum (q : ℝ) : ∑ b,bernoulli q b=1 := by
  simp [bernoulli]
lemma bernoulli_nonneg {q : ℝ} (hq : q∈Set.Icc 0 1) (b : Bool) : 0 ≤ bernoulli q b := by
  cases b <;> simp [bernoulli] <;> linarith [hq.1,hq.2]

omit [Fintype A] [Fintype B] in
lemma bernoulli_thinning (q d : I → ℝ) (f : (I → Bool) → ℝ) :
    (∑ o : I → Bool×Bool,productWeight (fun i b=>bernoulli (q i) b.1*bernoulli (d i) b.2) o*
      f (fun i=>(o i).1 && !(o i).2))=
    ∑ b,productWeight (fun i=>bernoulli (q i*(1-d i))) b*f b := by
  rw [product_pushforward (fun i (b : Bool×Bool)=>bernoulli (q i) b.1*bernoulli (d i) b.2)
    (fun _ (b : Bool×Bool)=>b.1 && !b.2) f]
  congr 1
  funext b
  congr 1
  apply prod_congr rfl
  intro i _
  cases b i <;> simp [Fintype.sum_prod_type,bernoulli]
  ring

omit [Fintype A] [Fintype B] in
lemma paired_expectation (q d : I → ℝ) (f : (I → Bool) → (I → Bool) → ℝ) :
    (∑ o : I → Bool×Bool,productWeight (fun i b=>bernoulli (q i) b.1*bernoulli (d i) b.2) o*
      f (fun i=>(o i).1) (fun i=>(o i).2))=
    ∑ a,productWeight (fun i=>bernoulli (q i)) a*
      ∑ b,productWeight (fun i=>bernoulli (d i)) b*f a b := by
  let e : (I → Bool×Bool) ≃ (I → Bool)×(I → Bool) :=
    { toFun := fun o=>(fun i=>(o i).1,fun i=>(o i).2)
      invFun := fun ab i=>(ab.1 i,ab.2 i)
      left_inv := fun _=>rfl
      right_inv := fun ab=>by cases ab; rfl }
  rw [Fintype.sum_equiv e (fun o=>productWeight (fun i b=>bernoulli (q i) b.1*bernoulli (d i) b.2) o*
    f (fun i=>(o i).1) (fun i=>(o i).2))
    (fun ab=>productWeight (fun i=>bernoulli (q i)) ab.1*productWeight (fun i=>bernoulli (d i)) ab.2*f ab.1 ab.2)]
  · simp only [Fintype.sum_prod_type,mul_sum,mul_assoc]
  · intro o
    simp [e,productWeight,prod_mul_distrib]

lemma minimum_le_one (v : I → ℝ) (a : I → Bool) : minimum v a ≤ 1 :=
  min'_le _ _ (mem_insert_self _ _)
lemma minimum_le (v : I → ℝ) {a : I → Bool} {i : I} (hi : a i=true) : minimum v a ≤ v i :=
  min'_le _ _ (mem_insert_of_mem (mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hi⟩,rfl⟩))
lemma le_minimum {v : I → ℝ} {a : I → Bool} {u : ℝ} (hu : u ≤ 1)
    (h : ∀ i,a i=true → u ≤ v i) : u ≤ minimum v a := by
  apply le_min'
  intro z hz
  rcases mem_insert.mp hz with rfl | hz
  · exact hu
  · obtain ⟨i,hi,rfl⟩:=mem_image.mp hz
    exact h i (mem_filter.mp hi).2
lemma minimum_nonneg {v : I → ℝ} (hv : ∀ i,0 ≤ v i) (a : I → Bool) : 0 ≤ minimum v a :=
  le_minimum (by norm_num) (fun i _=>hv i)
lemma minimum_cases (v : I → ℝ) (a : I → Bool) :
    minimum v a=1 ∨ ∃ i,a i=true ∧ minimum v a=v i := by
  have hm := min'_mem (insert 1 ((univ.filter (fun i=>a i=true)).image v)) ⟨1,mem_insert_self _ _⟩
  rcases mem_insert.mp hm with h | h
  · exact Or.inl h
  · obtain ⟨i,hi,he⟩:=mem_image.mp h
    exact Or.inr ⟨i,(mem_filter.mp hi).2,he.symm⟩

lemma profile_bounds {q v : I → ℝ} (hq : ∀ i,q i∈Set.Icc 0 1)
    (hv : ∀ i,v i∈Set.Icc 0 1) : profile q v∈Set.Icc 0 1 := by
  have hw := productWeight_nonneg (fun i=>bernoulli_nonneg (hq i))
  refine ⟨sum_nonneg (fun a _=>mul_nonneg (hw a) (minimum_nonneg (fun i=>(hv i).1) a)),?_⟩
  calc profile q v  ≤  ∑ a,productWeight (fun i=>bernoulli (q i)) a*1 :=
        sum_le_sum (fun a _=>mul_le_mul_of_nonneg_left (minimum_le_one _ _) (hw a))
    _ = 1 := by simpa using productWeight_sum (fun i=>bernoulli (q i)) (fun i=>bernoulli_sum _)

/-- Continuing independent trials gives exactly the new survival marginal. -/
lemma profile_thinning (q d v : I → ℝ) :
    profile (fun i=>q i*(1-d i)) v=
      ∑ a,productWeight (fun i=>bernoulli (q i)) a*
        ∑ b,productWeight (fun i=>bernoulli (d i)) b*minimum v (fun i=>a i && !b i) := by
  rw [profile,←bernoulli_thinning]
  exact paired_expectation q d (fun a b=>minimum v (fun i=>a i && !b i))

lemma minimum_retirement {v : I → ℝ} (hv : ∀ i,0 ≤ v i) (a b : I → Bool)
    {i : I} (hai : a i=true) (hmin : minimum v a=v i) :
    minimum v (fun i=>a i && !b i)-minimum v a ≤ if b i then 1 else 0 := by
  cases hbi : b i
  · simp only [Bool.false_eq_true,ite_false]
    have hh := minimum_le v (a := fun i=>a i && !b i) (i := i) (by simp [hai,hbi])
    linarith
  · simp only [ite_true]
    linarith [minimum_le_one v (fun i=>a i && !b i),minimum_nonneg hv a]

/-- The selected old nearest survivor is tested by a fresh independent trial.
Compulsory deaths are charged without conditioning on survival. -/
lemma conditional_retirement {v d : I → ℝ} (hv : ∀ i,0 ≤ v i)
    (hd : ∀ i,d i∈Set.Icc 0 1) (a : I → Bool) {α : ℝ} (hα : 0 ≤ α)
    (C : Finset I) (hnc : ∀ i,i∉C → d i ≤ α) :
    (∑ b,productWeight (fun i=>bernoulli (d i)) b*minimum v (fun i=>a i && !b i))-
      minimum v a ≤ α+∑ i∈C,if a i then 1 else 0 := by
  have hw:=productWeight_nonneg (fun i=>bernoulli_nonneg (hd i))
  have hws:=productWeight_sum (fun i=>bernoulli (d i)) (fun i=>bernoulli_sum _)
  have hc : 0 ≤ ∑ i∈C,if a i then (1:ℝ) else 0 := sum_nonneg (fun i _=>by split_ifs <;> norm_num)
  have he : (∑ b,productWeight (fun i=>bernoulli (d i)) b*minimum v (fun i=>a i && !b i))-
      minimum v a = ∑ b,productWeight (fun i=>bernoulli (d i)) b*
        (minimum v (fun i=>a i && !b i)-minimum v a) := by
    simp_rw [mul_sub]
    rw [sum_sub_distrib,←sum_mul,hws,one_mul]
  rw [he]
  rcases minimum_cases v a with hm | ⟨i,hai,hm⟩
  · have hb : (∑ b,productWeight (fun i=>bernoulli (d i)) b*
        (minimum v (fun i=>a i && !b i)-minimum v a)) ≤ 0 := by
      apply sum_nonpos
      intro b _
      exact mul_nonpos_of_nonneg_of_nonpos (hw b) (by linarith [minimum_le_one v (fun i=>a i && !b i)])
    exact hb.trans (add_nonneg hα hc)
  · calc (∑ b,productWeight (fun i=>bernoulli (d i)) b*
          (minimum v (fun i=>a i && !b i)-minimum v a))
        ≤ ∑ b,productWeight (fun i=>bernoulli (d i)) b*(if b i then 1 else 0) :=
          sum_le_sum (fun b _=>mul_le_mul_of_nonneg_left (minimum_retirement hv a b hai hm) (hw b))
      _ = d i := by
        rw [product_marginal (fun i=>bernoulli (d i)) (fun i=>bernoulli_sum _) i (fun b=>if b then 1 else 0)]
        simp [bernoulli]
      _ ≤ α+∑ j∈C,if a j then 1 else 0 := by
        by_cases hi : i∈C
        · have hb : (1:ℝ) ≤ ∑ j∈C,if a j then 1 else 0 := by
            have hh:=single_le_sum (f := fun j=>if a j then (1:ℝ) else 0)
              (fun j _=>by split_ifs <;> norm_num) hi
            simpa [hai] using hh
          linarith [(hd i).2]
        · exact (hnc i hi).trans (le_add_of_nonneg_right hc)

lemma profile_retirement_bound {q d v : I → ℝ} (hq : ∀ i,q i∈Set.Icc 0 1)
    (hd : ∀ i,d i∈Set.Icc 0 1) (hv : ∀ i,0 ≤ v i) {α : ℝ} (hα : 0 ≤ α)
    (C : Finset I) (hnc : ∀ i,i∉C → d i ≤ α) :
    profile (fun i=>q i*(1-d i)) v-profile q v ≤ α+∑ i∈C,q i := by
  have hw:=productWeight_nonneg (fun i=>bernoulli_nonneg (hq i))
  have hws:=productWeight_sum (fun i=>bernoulli (q i)) (fun i=>bernoulli_sum _)
  rw [profile_thinning,profile,←sum_sub_distrib]
  have he : (∑ a,productWeight (fun i=>bernoulli (q i)) a*(α+∑ i∈C,if a i then 1 else 0))=
      α+∑ i∈C,q i := by
    simp_rw [mul_add,mul_sum]
    rw [sum_add_distrib,←sum_mul,hws,one_mul,sum_comm]
    congr 1
    apply sum_congr rfl
    intro i _
    rw [product_marginal (fun i=>bernoulli (q i)) (fun i=>bernoulli_sum _) i (fun b=>if b then 1 else 0)]
    simp [bernoulli]
  rw [←he]
  apply sum_le_sum
  intro a _
  rw [←mul_sub]
  exact mul_le_mul_of_nonneg_left (conditional_retirement hv hd a hα C hnc) (hw a)

lemma minimum_force_le (v : I → ℝ) (a : I → Bool) (i : I) :
    minimum v (Function.update a i true) ≤ minimum v a := by
  apply le_minimum (minimum_le_one _ _)
  intro j hj
  apply minimum_le
  by_cases hji : j=i
  · subst j; simp
  · simp [Function.update_of_ne hji,hj]

lemma forced_expectation (q : I → ℝ) (i : I) (f : (I → Bool) → ℝ) :
    (∑ a,productWeight (fun i=>bernoulli (q i)) a*f (Function.update a i true))=
      ∑ a,productWeight (fun j=>bernoulli (Function.update q i 1 j)) a*f a := by
  have he (a : I → Bool) : Function.update a i true=(fun j=>if j=i then true else a j) := by
    funext j; by_cases hj : j=i <;> simp [hj,Function.update_of_ne]
  simp_rw [he]
  rw [product_pushforward (fun i=>bernoulli (q i)) (fun j b=>if j=i then true else b) f]
  apply sum_congr rfl
  intro a _
  congr 1
  apply prod_congr rfl
  intro j _
  by_cases hji : j=i
  · subst j
    cases a i <;> simp [bernoulli]
  · cases a j <;> simp [hji,Function.update_of_ne,bernoulli]

lemma profile_insertion_le {q : I → ℝ} (hq : ∀ i,q i∈Set.Icc 0 1) (v : I → ℝ) (i : I) :
    profile (Function.update q i 1) v ≤ profile q v := by
  rw [profile,←forced_expectation]
  apply sum_le_sum
  intro a _
  exact mul_le_mul_of_nonneg_left (minimum_force_le v a i)
    (productWeight_nonneg (fun i=>bernoulli_nonneg (hq i)) a)

lemma weight_zero_at {q : I → ℝ} {a : I → Bool} {i : I} (h : bernoulli (q i) (a i)=0) :
    productWeight (fun i=>bernoulli (q i)) a=0 := prod_eq_zero (mem_univ i) h

lemma profile_one {q v : I → ℝ} (h : ∀ i,q i≠0 → 1 ≤ v i) : profile q v=1 := by
  calc profile q v=∑ a,productWeight (fun i=>bernoulli (q i)) a := by
        apply sum_congr rfl
        intro a _
        by_cases hw : productWeight (fun i=>bernoulli (q i)) a=0
        · simp [hw]
        · have hm : minimum v a=1 := by
            apply le_antisymm (minimum_le_one _ _)
            apply le_minimum le_rfl
            intro i hi
            apply h i
            intro hq
            exact hw (weight_zero_at (i := i) (by simp [bernoulli,hi,hq]))
          rw [hm,mul_one]
    _ = 1 := productWeight_sum (fun i=>bernoulli (q i)) (fun i=>bernoulli_sum _)

lemma profile_zero_of_certain {q v : I → ℝ} (hv : ∀ i,0 ≤ v i) {i : I}
    (hqi : q i=1) (hvi : v i=0) : profile q v=0 := by
  apply sum_eq_zero
  intro a _
  cases hai : a i
  · rw [weight_zero_at (i := i) (by simp [bernoulli,hai,hqi]),zero_mul]
  · have hm : minimum v a=0 := le_antisymm ((minimum_le v hai).trans_eq hvi) (minimum_nonneg hv a)
    rw [hm,mul_zero]

lemma minimum_lipschitz {v w : I → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ i,|v i-w i| ≤ L) (a : I → Bool) : |minimum v a-minimum w a| ≤ L := by
  have hdir (v w : I → ℝ) (h : ∀ i,v i-w i ≤ L) : minimum v a-minimum w a ≤ L := by
    suffices minimum v a-L ≤ minimum w a by linarith
    apply le_minimum (by linarith [minimum_le_one v a])
    intro i hi
    linarith [minimum_le v hi,h i]
  rw [abs_sub_le_iff]
  exact ⟨hdir v w (fun i=>(le_abs_self _).trans (h i)),
    hdir w v (fun i=>by linarith [(neg_le_abs (v i-w i)).trans (h i)])⟩

lemma profile_lipschitz {q v w : I → ℝ} (hq : ∀ i,q i∈Set.Icc 0 1) {L : ℝ}
    (hL : 0 ≤ L) (h : ∀ i,|v i-w i| ≤ L) : |profile q v-profile q w| ≤ L := by
  have hw:=productWeight_nonneg (fun i=>bernoulli_nonneg (hq i))
  unfold profile
  rw [←sum_sub_distrib]
  calc |∑ a,(productWeight (fun i=>bernoulli (q i)) a*minimum v a-
        productWeight (fun i=>bernoulli (q i)) a*minimum w a)|
      ≤ ∑ a,|productWeight (fun i=>bernoulli (q i)) a*minimum v a-
        productWeight (fun i=>bernoulli (q i)) a*minimum w a| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a,productWeight (fun i=>bernoulli (q i)) a*L := by
      apply sum_le_sum
      intro a _
      rw [←mul_sub,abs_mul,abs_of_nonneg (hw a)]
      exact mul_le_mul_of_nonneg_left (minimum_lipschitz hL h a) (hw a)
    _ = L := by rw [←sum_mul,productWeight_sum _ (fun i=>bernoulli_sum _),one_mul]

lemma minimum_cut {v : I → ℝ} (hv : ∀ i,v i ≤ 1) (a : I → Bool) :
    minimum v a=minimum v (fun i=>if v i<1 then a i else false) := by
  apply le_antisymm
  · apply le_minimum (minimum_le_one _ _)
    intro i hi
    split_ifs at hi with hh
    · exact minimum_le v hi
  · apply le_minimum (minimum_le_one _ _)
    intro i hi
    by_cases hh : v i<1
    · exact minimum_le v (i := i) (by simp [hh,hi])
    · exact (minimum_le_one _ _).trans_eq (le_antisymm (hv i) (le_of_not_gt hh)).symm

lemma profile_cut {q v : I → ℝ} (hv : ∀ i,v i ≤ 1) :
    profile q v=profile (fun i=>if v i<1 then q i else 0) v := by
  unfold profile
  have he (a : I → Bool) := minimum_cut hv a
  conv_lhs => arg 2; ext a; rw [he]
  rw [product_pushforward (fun i=>bernoulli (q i)) (fun i b=>if v i<1 then b else false) (minimum v)]
  apply sum_congr rfl
  intro a _
  congr 1
  apply prod_congr rfl
  intro i _
  by_cases hi : v i<1 <;> cases a i <;> simp [hi,bernoulli]

lemma profile_irrelevant {q q' v : I → ℝ} (hv : ∀ i,v i ≤ 1)
    (he : ∀ i,v i<1 → q i=q' i) : profile q v=profile q' v := by
  rw [profile_cut hv,profile_cut (q := q') hv]
  congr 1
  funext i
  by_cases hi : v i<1 <;> simp [hi,he i]

/-- Only compulsory candidates whose ramps are below one need be counted. -/
lemma profile_retirement_local {q d v : I → ℝ} (hq : ∀ i,q i∈Set.Icc 0 1)
    (hd : ∀ i,d i∈Set.Icc 0 1) (hv : ∀ i,v i∈Set.Icc 0 1) {α : ℝ} (hα : 0 ≤ α)
    (C : Finset I) (hnc : ∀ i,i∉C → v i<1 → d i ≤ α) :
    profile (fun i=>q i*(1-d i)) v-profile q v ≤ α+∑ i∈C,q i := by
  let d' : I → ℝ := fun i=>if v i<1 then d i else 0
  have he : profile (fun i=>q i*(1-d i)) v=profile (fun i=>q i*(1-d' i)) v := by
    apply profile_irrelevant (fun i=>(hv i).2)
    intro i hi
    simp [d',hi]
  rw [he]
  apply profile_retirement_bound hq (fun i=>?_) (fun i=>(hv i).1) hα C (fun i hi=>?_)
  · dsimp [d']
    split_ifs
    · exact hd i
    · exact ⟨le_rfl,zero_le_one⟩
  · dsimp [d']
    split_ifs with hh
    · exact hnc i hi hh
    · exact hα


/-- Coordinates with zero presence probability carry no information about
an expected profile. This is the exact causality fact for unused ordinals. -/
lemma profile_values_congr {q v w : I → ℝ}
    (h : ∀ i,q i≠0 → v i=w i) : profile q v=profile q w := by
  apply sum_congr rfl
  intro a _
  by_cases hw : productWeight (fun i=>bernoulli (q i)) a=0
  · simp [hw]
  · congr 1
    apply le_antisymm
    · apply le_minimum (minimum_le_one _ _)
      intro i hi
      have hq : q i≠0 := fun hz=>hw (weight_zero_at (i := i) (by simp [bernoulli,hi,hz]))
      rw [←h i hq]
      exact minimum_le v hi
    · apply le_minimum (minimum_le_one _ _)
      intro i hi
      have hq : q i≠0 := fun hz=>hw (weight_zero_at (i := i) (by simp [bernoulli,hi,hz]))
      rw [h i hq]
      exact minimum_le w hi

end KServer.RosterExpectation

end


/-! The genuine deterministic expected short-roster profile in §07, on the
finite preallocated set of insertion ordinals. The auxiliary lifetimes are
not the actual partition lifetimes. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ShortRoster
open Chronological RosterLifetimes
attribute [local instance] Classical.propDecidable Classical.decEq

lemma ramp_bounds (u : ℝ) : ramp u∈Set.Icc 0 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩
lemma ramp_zero {u : ℝ} (hu : u ≤ 1/8) : ramp u=0 := by
  simp [ramp,max_eq_left (by linarith : 8*u-1 ≤ 0)]
lemma ramp_one {u : ℝ} (hu : 1/4 ≤ u) : ramp u=1 :=
  min_eq_left ((by linarith : 1 ≤ 8*u-1).trans (le_max_right _ _))
lemma ramp_lipschitz (u v : ℝ) : |ramp u-ramp v| ≤ 8*|u-v| := by
  rw [abs_le]
  constructor <;> unfold ramp <;> simp only [min_def,max_def] <;> split_ifs <;>
    have h1:=le_abs_self (u-v) <;> have h2:=neg_le_abs (u-v) <;> linarith

lemma rate_bounds {K : ℕ} (hK : 2 ≤ K) : 1/Real.sqrt K∈Set.Icc (0:ℝ) 1 := by
  have hs : 1 ≤ Real.sqrt K := Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ K by omega))
  exact ⟨by positivity,(div_le_one (by linarith)).mpr hs⟩
lemma short_bounds {K : ℕ} (hK : 2 ≤ K) (a : ℕ) : shortPresence K a∈Set.Icc (0:ℝ) 1 := by
  unfold shortPresence
  split_ifs
  · exact survive_range (rate_bounds hK) a
  · exact ⟨le_rfl,zero_le_one⟩

variable {Y : Type*} [MetricSpace Y] {H : ℕ}

lemma probability_bounds (request : ℕ → Y) (r : ℝ) {K : ℕ} (hK : 2 ≤ K)
    (S : Finset ℕ) (i : Fin H) : probability request r K S i∈Set.Icc (0:ℝ) 1 := by
  unfold probability
  split_ifs
  · exact short_bounds hK _
  · exact ⟨le_rfl,zero_le_one⟩
lemma profile_bounds (request : ℕ → Y) (r : ℝ) {K : ℕ} (hK : 2 ≤ K)
    (S : Finset ℕ) (p : Y) : profile (H := H) request r K S p∈Set.Icc (0:ℝ) 1 :=
  RosterExpectation.profile_bounds (probability_bounds request r hK S) (fun _=>ramp_bounds _)

lemma values_lipschitz (request : ℕ → Y) {r : ℝ} (hr : 0 < r) (p q : Y) (i : Fin H) :
    |values request r p i-values request r q i| ≤ 8*dist p q/r := by
  have hl:=ramp_lipschitz (dist (request i) p/r) (dist (request i) q/r)
  have hd : |dist (request i) p-dist (request i) q| ≤ dist p q := by
    simpa only [dist_comm (request i)] using abs_dist_sub_le p q (request i)
  rw [←sub_div,abs_div,abs_of_pos hr] at hl
  exact hl.trans (by simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hd hr.le) (by norm_num : (0:ℝ) ≤ 8))

lemma profile_lipschitz (request : ℕ → Y) {r : ℝ} (hr : 0 < r) {K : ℕ} (hK : 2 ≤ K)
    (S : Finset ℕ) (p q : Y) : |profile (H := H) request r K S p-profile (H := H) request r K S q| ≤ 8*dist p q/r :=
  RosterExpectation.profile_lipschitz (probability_bounds request r hK S)
    (by positivity) (values_lipschitz request hr p q)

lemma death_bounds (request : ℕ → Y) (r : ℝ) {K : ℕ} (hK : 2 ≤ K)
    (S : Finset ℕ) (t i : Fin H) : death request r K S t i∈Set.Icc (0:ℝ) 1 := by
  unfold death
  split_ifs
  · exact rate_bounds hK
  · exact ⟨zero_le_one,le_rfl⟩
  · exact ⟨le_rfl,zero_le_one⟩

lemma probability_insert (request : ℕ → Y) (r : ℝ) {K : ℕ} (hK : 2 ≤ K)
    (S : Finset ℕ) (t : Fin H) (hbefore : ∀ i∈S,i<(t:ℕ)) :
    probability (H := H) request r K (insert (t:ℕ) S)=
      Function.update (fun i=>probability request r K S i*(1-death request r K S t i)) t 1 := by
  have ht : (t:ℕ)∉S := fun h=>Nat.lt_irrefl _ (hbefore _ h)
  funext i
  by_cases hit : i=t
  · subst i
    simp [probability,age_new request S (20*r) hbefore,short_new (show 0<K by omega)]
  · have hin : (i:ℕ)≠(t:ℕ) := fun h=>hit (Fin.ext h)
    rw [Function.update_of_ne hit]
    by_cases hi : (i:ℕ)∈S
    · have he:=age_insert request S (20*r) ht (hbefore i hi)
      by_cases hd : dist (request i) (request t) ≤ 20*r
      · rw [ite_eq_left hd] at he
        by_cases ha : age request S (20*r) i<K
        · by_cases ha' : age request S (20*r) i+1<K
          · have hh : age request (insert (t:ℕ) S) (20*r) i<K := by omega
            simp [probability,hi,hin,he,death,ha,ha',hd,shortPresence,survive,pow_succ]
          · have hh : ¬age request (insert (t:ℕ) S) (20*r) i<K := by omega
            simp [probability,hi,hin,he,death,ha,ha',hd,shortPresence,survive]
        · have hh : ¬age request S (20*r) i+1<K := by omega
          simp [probability,hi,hin,he,death,ha,hh,hd,shortPresence]
      · simp only [ite_eq_right hd,add_zero] at he
        simp [probability,hi,hin,he,death,hd]
    · simp [probability,hin,hi,death]

lemma profile_unit_drop (request : ℕ → Y) {r : ℝ} (hr : 0 < r) {K : ℕ} (hK : 2 ≤ K)
    (S : Finset ℕ) (t : Fin H) (hbefore : ∀ i∈S,i<(t:ℕ))
    (htest : ¬∃ i∈S,age request S (20*r) i<K ∧ dist (request i) (request t) ≤ r/2)
    {p : Y} (hp : dist (request t) p ≤ r/8) :
    profile (H := H) request r K S p-profile (H := H) request r K (insert (t:ℕ) S) p=1 := by
  have hold : profile (H := H) request r K S p=1 := by
    apply RosterExpectation.profile_one
    intro i hi
    have hIS : (i:ℕ)∈S := by by_contra hn; exact hi (by simp [probability,hn])
    have hage : age request S (20*r) i<K := by
      by_contra hn
      exact hi (by simp [probability,hIS,shortPresence,hn])
    have hd : r/2<dist (request i) (request t) := lt_of_not_ge (fun hd=>htest ⟨i,hIS,hage,hd⟩)
    have hdp : r/4 ≤ dist (request i) p := by
      have hd':=dist_triangle (request i) p (request t)
      rw [dist_comm p (request t)] at hd'
      linarith
    rw [values,ramp_one ((le_div_iff₀ hr).mpr (by linarith))]
  have hnew : profile (H := H) request r K (insert (t:ℕ) S) p=0 := by
    apply RosterExpectation.profile_zero_of_certain (fun i=>(ramp_bounds _).1) (i := t)
    · rw [probability_insert request r hK S t hbefore]
      simp
    · exact ramp_zero ((div_le_iff₀ hr).mpr (by linarith))
  rw [hold,hnew,sub_zero]

lemma values_lt_one (request : ℕ → Y) {r : ℝ} (hr : 0 < r) {p : Y} {i : Fin H}
    (hi : values request r p i<1) : dist (request i) p < r/4 := by
  by_contra hn
  have hh:=ramp_one ((le_div_iff₀ hr).mpr (by linarith [le_of_not_gt hn] : (1:ℝ)/4*r ≤ dist (request i) p))
  change ramp (dist (request i) p/r)<1 at hi
  rw [hh] at hi
  exact lt_irrefl _ hi

lemma compulsory_count (request : ℕ → Y) {r : ℝ} (hr : 0 < r) {K : ℕ} (hK : 2 ≤ K)
    (S : Finset ℕ) (p : Y) : (compulsory (H := H) request r K S p).card ≤ K := by
  let C:=compulsory (H := H) request r K S p
  have hinj : Function.Injective (fun i : Fin H=>(i:ℕ)) := Fin.val_injective
  have he : (C.image (fun (i : Fin H)=>(i:ℕ))).card=C.card := card_image_of_injective C hinj
  rw [←he]
  apply local_age_count request S _ (20*r) K
  · intro n hn
    obtain ⟨i,hi,he⟩:=mem_image.mp hn
    subst n
    exact (mem_filter.mp hi).2.1
  · intro n hn
    obtain ⟨i,hi,he⟩:=mem_image.mp hn
    subst n
    have hage:=(mem_filter.mp hi).2.2.1
    omega
  · intro n hn m hm
    obtain ⟨i,hi,he⟩:=mem_image.mp hn
    obtain ⟨j,hj,hf⟩:=mem_image.mp hm
    subst n
    subst m
    have hi':=(mem_filter.mp hi).2.2.2
    have hj':=(mem_filter.mp hj).2.2.2
    have hd:=dist_triangle (request i) p (request j)
    rw [dist_comm p (request j)] at hd
    linarith

lemma compulsory_mass (request : ℕ → Y) {r : ℝ} (hr : 0 < r) {K : ℕ} (hK : 2 ≤ K)
    (S : Finset ℕ) (p : Y) :
    (∑ i∈compulsory (H := H) request r K S p,probability request r K S i) ≤
      (K:ℝ)*survive (1/Real.sqrt K) (K-1) := by
  let C:=compulsory (H := H) request r K S p
  have he : (∑ i∈C,probability request r K S i)=(C.card:ℝ)*survive (1/Real.sqrt K) (K-1) := by
    calc (∑ i∈C,probability request r K S i)=∑ _i∈C,survive (1/Real.sqrt K) (K-1) := by
          apply sum_congr rfl
          intro i hi
          obtain ⟨hi,ha,_⟩:=(mem_filter.mp hi).2
          simp [probability,hi,shortPresence,ha,show K-1<K by omega]
      _ = _ := by simp
  change (∑ i∈C,probability request r K S i) ≤ _
  rw [he]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast compulsory_count (H := H) request hr hK S p)
    (survive_range (rate_bounds hK) (K-1)).1

/-- The exact short-roster retirement bound, including compulsory deaths,
is uniform in the number of chronological records and the horizon. -/
theorem profile_error (request : ℕ → Y) {r : ℝ} (hr : 0 < r) {K : ℕ} (hK : 2 ≤ K)
    (S : Finset ℕ) (t : Fin H) (hbefore : ∀ i∈S,i<(t:ℕ)) (p : Y) :
    profile (H := H) request r K (insert (t:ℕ) S) p-profile (H := H) request r K S p ≤ 49/Real.sqrt K := by
  let q:=probability (H := H) request r K S
  let d:=death request r K S t
  let v:=values (H := H) request r p
  have hq : ∀ i,q i∈Set.Icc 0 1 := probability_bounds request r hK S
  have hd : ∀ i,d i∈Set.Icc 0 1 := death_bounds request r hK S t
  have hv : ∀ i,v i∈Set.Icc 0 1 := fun i=>ramp_bounds _
  have hthin : ∀ i,q i*(1-d i)∈Set.Icc 0 1 := by
    intro i
    refine ⟨mul_nonneg (hq i).1 (by linarith [(hd i).2]),?_⟩
    exact (mul_le_mul_of_nonneg_left (by linarith [(hd i).1] : 1-d i ≤ 1) (hq i).1).trans (by simpa using (hq i).2)
  have hinst : profile (H := H) request r K (insert (t:ℕ) S) p ≤ RosterExpectation.profile (fun i=>q i*(1-d i)) v := by
    unfold profile
    rw [probability_insert request r hK S t hbefore]
    convert RosterExpectation.profile_insertion_le hthin v t using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext i
    by_cases hi : i=t <;> simp [hi,q,d]
  have hret := RosterExpectation.profile_retirement_local hq hd hv (rate_bounds hK).1
    (compulsory (H := H) request r K S p) (fun i hi hvi=>by
      dsimp [d,death]
      split_ifs with ha ha'
      · rfl
      · apply False.elim
        apply hi
        apply mem_filter.mpr
        refine ⟨mem_univ _,ha.1,?_,values_lt_one request hr hvi⟩
        omega
      · exact (rate_bounds hK).1)
  have hmass:=compulsory_mass (H := H) request hr hK S p
  have hbound:=short_retirement_bound K hK
  change RosterExpectation.profile (fun i=>q i*(1-d i)) v-
    profile (H := H) request r K S p ≤ _ at hret
  linarith

lemma profile_outside (request : ℕ → Y) {r : ℝ} (hr : 0 < r) {K : ℕ} (hK : 2 ≤ K)
    (S : Finset ℕ) (t : Fin H) (hbefore : ∀ i∈S,i<(t:ℕ)) {p : Y}
    (hp : 21*r<dist (request t) p) :
    profile (H := H) request r K S p=profile (H := H) request r K (insert (t:ℕ) S) p := by
  unfold profile
  apply RosterExpectation.profile_irrelevant (fun i=>(ramp_bounds _).2)
  intro i hi
  have hdist:=values_lt_one request hr hi
  have hit : i≠t := by intro h; subst i; linarith
  have hfar : ¬dist (request i) (request t) ≤ 20*r := by
    intro hh
    have ht:=dist_triangle (request t) (request i) p
    rw [dist_comm (request t) (request i)] at ht
    linarith
  rw [probability_insert request r hK S t hbefore,Function.update_of_ne hit]
  simp [death,hfar]

lemma profile_increase_support (request : ℕ → Y) {r : ℝ} (hr : 0 < r) {K : ℕ} (hK : 2 ≤ K)
    (S : Finset ℕ) (t : Fin H) (hbefore : ∀ i∈S,i<(t:ℕ))
    (htest : ¬∃ i∈S,age request S (20*r) i<K ∧ dist (request i) (request t) ≤ r/2)
    {p : Y} (hp : profile (H := H) request r K S p<profile (H := H) request r K (insert (t:ℕ) S) p) :
    r/8<dist (request t) p ∧ dist (request t) p ≤ 21*r := by
  constructor
  · by_contra hn
    have he:=profile_unit_drop request hr hK S t hbefore htest (le_of_not_gt hn)
    linarith
  · by_contra hn
    have he:=profile_outside request hr hK S t hbefore (lt_of_not_ge hn)
    linarith


lemma age_congr {request request' : ℕ → Y} {S : Finset ℕ} {r : ℝ} {i : ℕ}
    (hi : request i=request' i) (h : ∀ j∈S,request j=request' j) :
    age request S r i=age request' S r i := by
  unfold age
  congr 1
  apply filter_congr
  intro j hj
  rw [hi,h j hj]

lemma profile_congr {request request' : ℕ → Y} {S : Finset ℕ}
    (h : ∀ j∈S,request j=request' j) (r : ℝ) (K : ℕ) (p : Y) :
    profile (H := H) request r K S p=profile (H := H) request' r K S p := by
  have hq : probability (H := H) request r K S=probability request' r K S := by
    funext i
    unfold probability
    split_ifs with hi
    · rw [age_congr (h i hi) h]
    · rfl
  unfold profile
  rw [hq]
  apply RosterExpectation.profile_values_congr
  intro i hi
  have hIS : (i:ℕ)∈S := by by_contra hn; exact hi (by simp [probability,hn])
  simp only [values,h i hIS]

end KServer.ShortRoster

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Tiers
attribute [-instance] _root_.OAI.KServer.JointExperiment.levelTapeFintype _root_.OAI.KServer.LevelKeys.alphabetFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/- Analytic insertion gain for the second compact pilot under the profile hypotheses. -/


noncomputable section
open scoped BigOperators
open Finset Set
namespace KServer.Pilot
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [Fintype Y] [MetricSpace Y] [DecidableEq Y]

omit [DecidableEq Y] in
lemma residual_bounds {T : Template} {r : ℝ} {z : Y → ℝ}
    (hz : Feasible T r z) (p : Y) :
    1-∑ s,z s*b T (dist s p/r) ∈ Set.Icc 0 1 := by
  refine ⟨sub_nonneg.mpr (sum_b_le_one hz p),?_⟩
  have hh := sum_nonneg (s := (univ : Finset Y))
    (fun s _ => mul_nonneg (hz.1 s) (b_nonneg T (dist s p/r)))
  linarith

omit [DecidableEq Y] in
lemma profile_difference (T : Template) (r : ℝ) (g₀ g₁ z : Y → ℝ) (p : Y) :
    integrand T r g₀ z p-integrand T r g₁ z p =
      (g₀ p-g₁ p)*(1-∑ s,z s*b T (dist s p/r))+
        256*∑ s,z s*(g₀ s-g₁ s)*a T (dist s p/r) := by
  have he : (∑ s,z s*(1+g₀ s)*a T (dist s p/r))-
      (∑ s,z s*(1+g₁ s)*a T (dist s p/r)) =
      ∑ s,z s*(g₀ s-g₁ s)*a T (dist s p/r) := by
    rw [←sum_sub_distrib]
    apply sum_congr rfl
    intros
    ring
  unfold integrand
  linear_combination 256*he

omit [DecidableEq Y] in
/-- A narrow residual has deficit at most one half unless a nearby pilot
site has weight at least one half. Separation, not a new assumption about
sparsity, proves that at most one positive bump contributes. -/
lemma residual_half {T : Template} {r γ : ℝ} {z : Y → ℝ} {x p : Y}
    (hr : 0 < r) (hγ : γ<T.σ) (hz : Feasible T r z)
    (hn : ∀ s,dist s x<3*T.σ*r → z s<1/2)
    (hp : dist x p≤γ*r) : 1/2 ≤ 1-∑ s,z s*b T (dist s p/r) := by
  have hterm : ∀ s,0≤z s*b T (dist s p/r) :=
    fun s => mul_nonneg (hz.1 s) (b_nonneg T _)
  have hsingle : ∀ s,0<z s*b T (dist s p/r) → z s*b T (dist s p/r)≤1/2 := by
    intro s hs
    have hzpos : 0<z s := (mul_pos_iff.mp hs).resolve_right (by intro h; linarith [hz.1 s]) |>.1
    have hbpos : 0<b T (dist s p/r) :=
      (mul_pos_iff.mp hs).resolve_right (by intro h; linarith [hz.1 s]) |>.2
    have hd : dist s p<2*T.σ*r := (div_lt_iff₀ hr).mp (b_pos_iff.mp hbpos)
    have hnear : dist s x<3*T.σ*r := by
      have ht := dist_triangle s p x
      rw [dist_comm p x] at ht
      have hm := mul_lt_mul_of_pos_right hγ hr
      linarith
    exact (mul_le_of_le_one_right (hz.1 s) (b_le_one T _)).trans (hn s hnear).le
  have huniq : ∀ s t,0<z s*b T (dist s p/r) → 0<z t*b T (dist t p/r) → s=t := by
    intro s t hs ht
    have hs' := (mul_pos_iff.mp hs).resolve_right (by intro h; linarith [hz.1 s])
    have ht' := (mul_pos_iff.mp ht).resolve_right (by intro h; linarith [hz.1 t])
    exact positive_b_support_disjoint hr hz hs'.1 ht'.1 hs'.2 ht'.2
  have hh := sum_unique_le (f := fun s => z s*b T (dist s p/r))
    (q := (1/2:ℝ)) (by norm_num) hterm
      (fun s => by by_cases hs : 0<z s*b T (dist s p/r); exact hsingle s hs
                   exact (le_of_not_gt hs).trans (by norm_num)) huniq
  linarith

omit [DecidableEq Y] in
/-- Correcting each coefficient by epsilon uses the pilot capacity once,
not the number of sites. -/
lemma surcharge_error {T : Template} {r ε : ℝ} {z d : Y → ℝ} (hz : Feasible T r z)
    (hε : 0≤ε) (hd : ∀ s,-ε≤d s) (p : Y) :
    -ε ≤ ∑ s,z s*d s*a T (dist s p/r) := by
  have hb := sum_le_sum (s := (univ : Finset Y)) fun s _ =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hd s) (hz.1 s)) (a_nonneg T (dist s p/r))
  have he : (∑ s,z s*(-ε)*a T (dist s p/r))=
      -ε*∑ s,z s*a T (dist s p/r) := by
    rw [mul_sum]
    apply sum_congr rfl
    intros
    ring
  rw [he] at hb
  have hc := mul_le_mul_of_nonneg_left (sum_a_le_one hz p) hε
  linarith

omit [DecidableEq Y] in
lemma surcharge_gain {T : Template} {r ε : ℝ} {z d : Y → ℝ} (hz : Feasible T r z)
    (hε : 0≤ε) (hd : ∀ i,-ε≤d i) (s p : Y) (hs : d s=1) (hzs : 1/2≤z s)
    (ha : a T (dist s p/r)=1) :
    1/2-ε ≤ ∑ i,z i*d i*a T (dist i p/r) := by
  have hn i : 0≤z i*(d i+ε)*a T (dist i p/r) :=
    mul_nonneg (mul_nonneg (hz.1 i) (by linarith [hd i])) (a_nonneg T _)
  have hb := single_le_sum (s := (univ : Finset Y)) (fun i _ => hn i) (mem_univ s)
  have he : (∑ i,z i*(d i+ε)*a T (dist i p/r))=
      (∑ i,z i*d i*a T (dist i p/r))+ε*∑ i,z i*a T (dist i p/r) := by
    rw [mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intros
    ring
  rw [he,hs,ha,mul_one] at hb
  have hc := mul_le_mul_of_nonneg_left (sum_a_le_one hz p) hε
  have hzε : 1/2≤z s*(1+ε) := by nlinarith [hz.1 s]
  linarith

omit [MetricSpace Y] in
lemma indicator_sum (μ : Y → ℝ) (A : Finset Y) :
    (∑ p,μ p*(if p∈A then (1:ℝ) else 0))=mass μ A := by
  simp only [mul_ite,mul_one,mul_zero,←sum_filter,filter_mem_eq_inter,Finset.univ_inter,mass]

/-- Common signed error estimate, including exact support. -/
lemma profile_error {T : Template} {r ε : ℝ} {z g₀ g₁ : Y → ℝ}
    (hz : Feasible T r z) (hε : 0≤ε) (hd : ∀ i,-ε≤g₀ i-g₁ i) (W : Finset Y)
    (hres : ∀ p,p∉W → 0≤g₀ p-g₁ p)
    (hsur : ∀ p,p∉W → ∀ i,0≤z i*(g₀ i-g₁ i)*a T (dist i p/r)) (p : Y) :
    -257*ε*(if p∈W then (1:ℝ) else 0) ≤ integrand T r g₀ z p-integrand T r g₁ z p := by
  rw [profile_difference]
  have hR := residual_bounds hz p
  by_cases hp : p∈W
  · rw [ite_eq_left hp,mul_one]
    have hm := mul_le_mul_of_nonneg_right (hd p) hR.1
    have he := mul_le_mul_of_nonneg_left hR.2 hε
    have hs := surcharge_error hz hε hd p
    nlinarith
  · rw [ite_eq_right hp,mul_zero]
    exact add_nonneg (mul_nonneg (hres p hp) hR.1)
      (mul_nonneg (by norm_num) (sum_nonneg (fun i _ => hsur p hp i)))

/-- A residual gain is added to the common signed error, pointwise. -/
lemma profile_residual_gain {T : Template} {r ε : ℝ} {z g₀ g₁ : Y → ℝ}
    (hz : Feasible T r z) (hε : 0≤ε) (hd : ∀ i,-ε≤g₀ i-g₁ i) (W A : Finset Y)
    (hres : ∀ p,p∉W → 0≤g₀ p-g₁ p)
    (hsur : ∀ p,p∉W → ∀ i,0≤z i*(g₀ i-g₁ i)*a T (dist i p/r))
    (hgain : ∀ p∈A,g₀ p-g₁ p=1 ∧ 1/2≤1-∑ s,z s*b T (dist s p/r)) (p : Y) :
    (1/2:ℝ)*(if p∈A then 1 else 0)-257*ε*(if p∈W then (1:ℝ) else 0) ≤
      integrand T r g₀ z p-integrand T r g₁ z p := by
  by_cases hp : p∈A
  · have hg := hgain p hp
    rw [ite_eq_left hp,mul_one,profile_difference,hg.1,one_mul]
    by_cases hw : p∈W
    · rw [ite_eq_left hw,mul_one]
      have hs := surcharge_error hz hε hd p
      linarith
    · rw [ite_eq_right hw,mul_zero,sub_zero]
      have hs := sum_nonneg (s := (univ : Finset Y)) (fun i _ => hsur p hw i)
      linarith [hg.2]
  · rw [ite_eq_right hp,mul_zero,zero_sub]
    convert profile_error hz hε hd W hres hsur p using 1 <;> first | rfl | ring

/-- A known near site creates a surcharge gain, pointwise. -/
lemma profile_surcharge_gain {T : Template} {r ε : ℝ} {z g₀ g₁ : Y → ℝ}
    (hz : Feasible T r z) (hε : 0≤ε) (hd : ∀ i,-ε≤g₀ i-g₁ i) (W A : Finset Y)
    (hres : ∀ p,p∉W → 0≤g₀ p-g₁ p)
    (hsur : ∀ p,p∉W → ∀ i,0≤z i*(g₀ i-g₁ i)*a T (dist i p/r))
    (s : Y) (hs : g₀ s-g₁ s=1) (hzs : 1/2≤z s)
    (ha : ∀ p∈A,a T (dist s p/r)=1) (p : Y) :
    128*(if p∈A then (1:ℝ) else 0)-257*ε*(if p∈W then (1:ℝ) else 0) ≤
      integrand T r g₀ z p-integrand T r g₁ z p := by
  by_cases hp : p∈A
  · have hR := residual_bounds hz p
    rw [ite_eq_left hp,mul_one,profile_difference]
    by_cases hw : p∈W
    · rw [ite_eq_left hw,mul_one]
      have hsg := surcharge_gain hz hε hd s p hs hzs (ha p hp)
      have hm := mul_le_mul_of_nonneg_right (hd p) hR.1
      have he := mul_le_mul_of_nonneg_left hR.2 hε
      nlinarith
    · rw [ite_eq_right hw,mul_zero,sub_zero]
      have hsg := single_le_sum (s := (univ : Finset Y))
        (fun i _ => hsur p hw i) (mem_univ s)
      rw [hs,ha p hp,mul_one,mul_one] at hsg
      have hrn := mul_nonneg (hres p hw) hR.1
      linarith
  · rw [ite_eq_right hp,mul_zero,zero_sub]
    convert profile_error hz hε hd W hres hsur p using 1 <;> first | rfl | ring

/-- Integrating a pointwise pilot edit estimate and testing the literal old
minimizer proves a minimum decrease; no decrease assumption is needed. -/
lemma potential_profile_gain {T : Template} {r c e : ℝ} {μ g₀ g₁ : Y → ℝ}
    (hr : 0 ≤ r) (hμ : ∀ p,0≤μ p) (A W : Finset Y)
    (hpoint : ∀ p,c*(if p∈A then (1:ℝ) else 0)-e*(if p∈W then (1:ℝ) else 0) ≤
      integrand T r g₀ (minimizer T r μ g₀) p-
        integrand T r g₁ (minimizer T r μ g₀) p) :
    r*(c*mass μ A-e*mass μ W) ≤ potential T r μ g₀-potential T r μ g₁ := by
  have hb := sum_le_sum (s := (univ : Finset Y)) fun p _ =>
    mul_le_mul_of_nonneg_left (hpoint p) (hμ p)
  have he : (∑ p,μ p*(c*(if p∈A then (1:ℝ) else 0)-e*(if p∈W then (1:ℝ) else 0)))=
      c*mass μ A-e*mass μ W := by
    simp only [mul_sub,sum_sub_distrib,mul_left_comm (μ _) c,mul_left_comm (μ _) e,
      ←mul_sum,indicator_sum]
  rw [he] at hb
  have hm := mul_le_mul_of_nonneg_left hb hr
  have he' : r*∑ p,μ p*(integrand T r g₀ (minimizer T r μ g₀) p-
      integrand T r g₁ (minimizer T r μ g₀) p) =
      potential T r μ g₀-objective T r μ g₁ (minimizer T r μ g₀) := by
    simp only [mul_sub,sum_sub_distrib,mul_sub,potential,objective]
  rw [he'] at hm
  exact hm.trans (sub_le_sub_left (potential_le (minimizer_spec T r μ g₀).1) _)

omit [DecidableEq Y] in
/-- A coefficient lower bound using the actual bump supports on any two
finite regions. Used for the heavy annular version of the tier edit. -/
lemma coefficient_lower {T : Template} {r : ℝ} {μ g : Y → ℝ} (s : Y)
    (hμ : ∀ p,0≤μ p) (hg : ∀ p,g p∈Set.Icc 0 1) (A B : Finset Y)
    (ha : ∀ p∈A,a T (dist s p/r)=1)
    (hb : ∀ p,b T (dist s p/r)≠0 → p∈B) :
    256*mass μ A-2*mass μ B ≤ coefficient T r μ g s := by
  have hapos : 256*mass μ A ≤ ∑ p,μ p*(256*(1+g s)*a T (dist s p/r)) := by
    calc _ ≤ ∑ p∈A,μ p*(256*(1+g s)*a T (dist s p/r)) := by
           unfold mass
           rw [mul_sum]
           apply sum_le_sum
           intro p hp
           rw [ha p hp,mul_one]
           nlinarith [mul_nonneg (hμ p) (hg s).1]
         _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun p _ _ =>
           mul_nonneg (hμ p) (mul_nonneg (by linarith [(hg s).1]) (a_nonneg _ _)))
  have hbneg : (∑ p,μ p*((1+g p)*b T (dist s p/r))) ≤ 2*mass μ B := by
    calc _ = ∑ p∈B,μ p*((1+g p)*b T (dist s p/r)) := by
           apply (sum_subset (subset_univ _) ?_).symm
           intro p _ hnot
           have hz : b T (dist s p/r)=0 := by by_contra hn; exact hnot (hb p hn)
           simp [hz]
         _ ≤ _ := by
           unfold mass
           rw [mul_sum]
           apply sum_le_sum
           intro p _
           have hh : (1+g p)*b T (dist s p/r)≤2 := by
             nlinarith [mul_nonneg (hg p).1 (sub_nonneg.mpr (b_le_one T (dist s p/r))),
               b_nonneg T (dist s p/r),(hg p).1,(hg p).2,b_le_one T (dist s p/r)]
           nlinarith [mul_le_mul_of_nonneg_left hh (hμ p)]
  unfold coefficient
  simp only [mul_sub,sum_sub_distrib]
  linarith

lemma a_eq_one {T : Template} {v : ℝ} (hv : T.σ≤v) (hR : v≤T.R) : a T v=1 := by
  rw [a,ite_eq_left hR]
  apply min_eq_right
  apply (le_div_iff₀ (sq_pos_of_pos T.σ_pos)).mpr
  nlinarith [T.σ_pos]

end KServer.Pilot

end


noncomputable section
open scoped BigOperators
open Finset Set
namespace KServer.Pilot
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [Fintype Y] [MetricSpace Y] [DecidableEq Y]

omit [DecidableEq Y] in
lemma tier_increasing_site_zero {T : Template} {r γ δ : ℝ} {μ g z : Y → ℝ} {x s : Y}
    (hr : 0 < r) (hσ : T.σ≤1/1000) (hγ : γ≤1/100) (hδ : δ≤1)
    (hμ : ∀ p,0≤μ p) (hg : ∀ p,g p∈Set.Icc 0 1)
    (hz : Feasible T r z) (hmin : IsMinOn (objective T r μ g) {w | Feasible T r w} z)
    (hM : 0 < mass μ (ball x (γ*r)))
    (hconc : mass μ (ball x (51200*r))≤(1+δ)*mass μ (ball x (γ*r)))
    (hslo : r/8<dist s x) (hshi : dist s x≤21*r) : z s=0 := by
  apply minimizer_zero_of_coefficient_pos hr hz hmin
  have ha : ∀ p∈ball x (γ*r),a T (dist s p/r)=1 := by
    intro p hp
    have hp' := (mem_filter.mp hp).2
    apply a_eq_one
    · apply (le_div_iff₀ hr).mpr
      have ht := dist_triangle s p x
      rw [dist_comm p x] at ht
      have hg' := mul_le_mul_of_nonneg_right hγ hr.le
      have hs' := mul_le_mul_of_nonneg_right hσ hr.le
      linarith
    · apply (div_le_iff₀ hr).mpr
      have ht := dist_triangle s x p
      have hg' := mul_le_mul_of_nonneg_right hγ hr.le
      have hR' := mul_le_mul_of_nonneg_right T.R_ge hr.le
      linarith
  have hb : ∀ p,b T (dist s p/r)≠0 → p∈ball x (51200*r) := by
    intro p hp
    have hbpos : 0<b T (dist s p/r) := lt_of_le_of_ne (b_nonneg _ _) (Ne.symm hp)
    have hd := (div_lt_iff₀ hr).mp (b_pos_iff.mp hbpos)
    have ht := dist_triangle x s p
    rw [dist_comm x s] at ht
    have hs' := mul_le_mul_of_nonneg_right hσ hr.le
    apply mem_filter.mpr ⟨mem_univ _,?_⟩
    linarith
  have hc := coefficient_lower s hμ hg (ball x (γ*r)) (ball x (51200*r)) ha hb
  have hδ' := mul_le_mul_of_nonneg_right hδ hM.le
  linarith

lemma tier_near_bump {T : Template} {r γ : ℝ} {x s p : Y}
    (hr : 0 < r) (hσ : T.σ≤1/1000) (hR : 51201≤T.R) (hγ : 10*T.σ<γ)
    (hs : dist s x<3*T.σ*r)
    (hp : p∈ball x (51200*r) \ ball x (γ*r)) : a T (dist s p/r)=1 := by
  have hpout := (mem_filter.mp (mem_sdiff.mp hp).1).2
  have hpin : γ*r<dist x p := by
    have hnot := (mem_sdiff.mp hp).2
    by_contra hn
    exact hnot (mem_filter.mpr ⟨mem_univ _,le_of_not_gt hn⟩)
  apply a_eq_one
  · apply (le_div_iff₀ hr).mpr
    have ht := dist_triangle x s p
    rw [dist_comm x s] at ht
    have hg' := mul_lt_mul_of_pos_right hγ hr
    nlinarith [mul_pos T.σ_pos hr]
  · apply (div_le_iff₀ hr).mpr
    have ht := dist_triangle s x p
    have hσ' := mul_le_mul_of_nonneg_right hσ hr.le
    have hR' := mul_le_mul_of_nonneg_right hR hr.le
    linarith

omit [DecidableEq Y] in
lemma tier_outer_surcharge_nonneg {T : Template} {r : ℝ} {z d : Y → ℝ} {x p : Y}
    (hr : 0 < r) (hz : Feasible T r z)
    (hsupp : ∀ i,d i<0 → dist x i≤21*r)
    (hp : p∉ball x (100*T.R*r)) (i : Y) : 0≤z i*d i*a T (dist i p/r) := by
  by_cases hd : 0≤d i
  · exact mul_nonneg (mul_nonneg (hz.1 i) hd) (a_nonneg T _)
  · have hi := hsupp i (lt_of_not_ge hd)
    have ha : a T (dist i p/r)=0 := by
      apply a_eq_zero
      apply (le_div_iff₀ hr).mpr
      have hp' : 100*T.R*r<dist x p := by
        by_contra hn
        exact hp (mem_filter.mpr ⟨mem_univ _,le_of_not_gt hn⟩)
      have ht := dist_triangle x i p
      have hR := mul_le_mul_of_nonneg_right T.R_ge hr.le
      linarith
    simp [ha]

lemma tierRegion_subset (T : Template) {r γ δ : ℝ} (hr : 0 ≤ r)
    (μ : Y → ℝ) (x : Y) (hR : 51201≤T.R) :
    tierRegion T r γ δ μ x ⊆ ball x (100*T.R*r) := by
  unfold tierRegion
  split_ifs
  · intro p hp
    have hp' := (mem_filter.mp (mem_sdiff.mp hp).1).2
    apply mem_filter.mpr ⟨mem_univ _,?_⟩
    have hm := mul_le_mul_of_nonneg_right hR hr
    nlinarith
  · exact subset_refl _

/-- Geometry discharges the signed-error support with the annular heavy
region, rather than paying the possibly large inner heavy mass. -/
lemma tier_error_support {T : Template} {r γ δ : ℝ} {μ g₀ g₁ z : Y → ℝ} {x : Y}
    (hr : 0 < r) (hσ : T.σ≤1/1000) (hγ : γ≤1/100) (hδ : δ≤1)
    (hμ : ∀ p,0≤μ p) (hg : ∀ p,g₀ p∈Set.Icc 0 1)
    (hz : Feasible T r z) (hmin : IsMinOn (objective T r μ g₀) {w | Feasible T r w} z)
    (hM : 0 < mass μ (ball x (γ*r)))
    (hdrop : ∀ p,dist x p ≤ r/8 → g₀ p-g₁ p=1)
    (hsupp : ∀ p,g₀ p-g₁ p<0 → dist x p≤21*r) :
    (∀ p,p∉tierRegion T r γ δ μ x → 0≤g₀ p-g₁ p) ∧
    (∀ p,p∉tierRegion T r γ δ μ x → ∀ i,0≤z i*(g₀ i-g₁ i)*a T (dist i p/r)) := by
  have hlow (i : Y) (hi : g₀ i-g₁ i<0) : r/8<dist x i := by
    by_contra hn
    rw [hdrop i (le_of_not_gt hn)] at hi
    norm_num at hi
  by_cases hheavy : mass μ (ball x (51200*r))≤(1+δ)*mass μ (ball x (γ*r))
  · have hreg : tierRegion T r γ δ μ x=ball x (51200*r) \ ball x (γ*r) :=
      ite_eq_left hheavy
    constructor
    · intro p hp
      by_contra hn
      have hd := lt_of_not_ge hn
      apply hp
      rw [hreg]
      apply mem_sdiff.mpr
      constructor
      · apply mem_filter.mpr ⟨mem_univ _,?_⟩
        linarith [hsupp p hd]
      · intro hh
        have hp' := (mem_filter.mp hh).2
        have hγ' := mul_le_mul_of_nonneg_right hγ hr.le
        linarith [hlow p hd]
    · intro p _ i
      by_cases hi : 0≤g₀ i-g₁ i
      · exact mul_nonneg (mul_nonneg (hz.1 i) hi) (a_nonneg T _)
      · have he : z i=0 := tier_increasing_site_zero hr hσ hγ hδ hμ hg hz hmin hM hheavy
          (by simpa only [dist_comm i x] using hlow i (lt_of_not_ge hi))
          (by simpa only [dist_comm i x] using hsupp i (lt_of_not_ge hi))
        simp [he]
  · have hreg : tierRegion T r γ δ μ x=ball x (100*T.R*r) := ite_eq_right hheavy
    constructor
    · intro p hp
      by_contra hn
      apply hp
      rw [hreg]
      apply mem_filter.mpr ⟨mem_univ _,?_⟩
      have ht := hsupp p (lt_of_not_ge hn)
      have hR := mul_le_mul_of_nonneg_right T.R_ge hr.le
      linarith
    · intro p hp i
      rw [hreg] at hp
      exact tier_outer_surcharge_nonneg hr hz hsupp hp i

/-- Tier-pilot drop, including the heavy annular refinement. The
profile hypotheses describe the actual short-roster update; no pilot drop,
site existence, or coefficient-vanishing statement is assumed. -/
theorem tier_pilot_drop {T : Template} {r γH γL δ h ε : ℝ} {μ g₀ g₁ : Y → ℝ} {x : Y}
    (hr : 0 < r) (hσ : T.σ≤1/1000) (hR : 51201≤T.R)
    (hγH : γH≤1/100) (hσH : 10*T.σ<γH) (hγL : γL<T.σ)
    (hδ0 : 0≤δ) (hδ : δ≤1/256) (hh : 0≤h) (hε : 0≤ε)
    (hμ : ∀ p,0≤μ p) (hg : ∀ p,g₀ p∈Set.Icc 0 1)
    (hM : 0 < mass μ (ball x (γL*r)))
    (hqual : mass μ (ball x (100*T.R*r))≤Real.exp h*mass μ (ball x (γL*r)))
    (hd : ∀ p,-ε≤g₀ p-g₁ p)
    (hdrop : ∀ p,dist x p ≤ r/8 → g₀ p-g₁ p=1)
    (hsupp : ∀ p,g₀ p-g₁ p<0 → dist x p≤21*r) :
    r*mass μ (tierRegion T r γH δ μ x)*(128*δ*Real.exp (-h)-257*ε) ≤
      potential T r μ g₀-potential T r μ g₁ := by
  let z := minimizer T r μ g₀
  let W := tierRegion T r γH δ μ x
  let A := ball x (51200*r) \ ball x (γH*r)
  have hz : Feasible T r z := (minimizer_spec T r μ g₀).1
  have hmin := (minimizer_spec T r μ g₀).2
  have hLH : ball x (γL*r) ⊆ ball x (γH*r) := by
    apply ball_mono
    have hLH : γL≤γH := by linarith [T.σ_pos]
    exact mul_le_mul_of_nonneg_right hLH hr.le
  have hBH : ball x (γH*r) ⊆ ball x (51200*r) := by
    apply ball_mono
    exact mul_le_mul_of_nonneg_right (by linarith : γH≤51200) hr.le
  have hMH : 0 < mass μ (ball x (γH*r)) := hM.trans_le (mass_mono hμ hLH)
  have hsupport := tier_error_support hr hσ hγH (by linarith : δ≤1) hμ hg hz hmin hMH hdrop hsupp
  have hW0 : 0≤ mass μ W := mass_nonneg hμ W
  have hWI : Real.exp (-h)*mass μ W≤ mass μ (ball x (γL*r)) := by
    have he := mul_le_mul_of_nonneg_left
      ((mass_mono hμ (tierRegion_subset T (γ := γH) (δ := δ) hr.le μ x hR)).trans hqual) (Real.exp_nonneg (-h))
    have heq : Real.exp (-h)*(Real.exp h*mass μ (ball x (γL*r)))=mass μ (ball x (γL*r)) := by
      rw [←mul_assoc,←Real.exp_add]
      simp
    rw [heq] at he
    exact he
  by_cases hn : ∃ s,dist s x<3*T.σ*r ∧ 1/2≤z s
  · obtain ⟨s,hs,hsz⟩ := hn
    have hsdrop : g₀ s-g₁ s=1 := by
      apply hdrop
      rw [dist_comm x s]
      have hm := mul_le_mul_of_nonneg_right hσ hr.le
      linarith
    have hgain := potential_profile_gain hr.le hμ A W
      (profile_surcharge_gain hz hε hd W A hsupport.1 hsupport.2 s hsdrop hsz
        (fun p hp => tier_near_bump hr hσ hR hσH hs hp))
    have hmass : δ*Real.exp (-h)*mass μ W≤ mass μ A := by
      by_cases hheavy : mass μ (ball x (51200*r))≤(1+δ)*mass μ (ball x (γH*r))
      · have heq : W=A := ite_eq_left hheavy
        rw [heq]
        have he : Real.exp (-h)≤1 := by
          rw [Real.exp_le_one_iff]
          linarith
        have hδe : δ*Real.exp (-h)≤1 :=
          (mul_le_mul_of_nonneg_left he hδ0).trans (by linarith)
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hδe (mass_nonneg hμ A)
      · have heq := sum_sdiff (f := μ) hBH
        change mass μ A+mass μ (ball x (γH*r))=mass μ (ball x (51200*r)) at heq
        have hMI := mul_le_mul_of_nonneg_left (mass_mono hμ hLH) hδ0
        have hWI' := mul_le_mul_of_nonneg_left hWI hδ0
        have hh' := lt_of_not_ge hheavy
        nlinarith only [heq,hMI,hWI',hh']
    have hm : 128*δ*Real.exp (-h)*mass μ W≤128*mass μ A := by nlinarith only [hmass]
    have hfinal := (mul_le_mul_of_nonneg_left (sub_le_sub_right hm (257*ε*mass μ W)) hr.le).trans hgain
    convert hfinal using 1 <;> first | rfl | ring
  · have hn' : ∀ s,dist s x<3*T.σ*r → z s<1/2 := by
      intro s hs
      by_contra hh
      exact hn ⟨s,hs,le_of_not_gt hh⟩
    have hprofile : ∀ p∈ball x (γL*r),g₀ p-g₁ p=1 ∧ 1/2≤1-∑ s,z s*b T (dist s p/r) := by
      intro p hp
      have hp' := (mem_filter.mp hp).2
      constructor
      · apply hdrop
        have hγ' := mul_lt_mul_of_pos_right hγL hr
        have hσ' := mul_le_mul_of_nonneg_right hσ hr.le
        linarith
      · exact residual_half hr hγL hz hn' hp'
    have hgain := potential_profile_gain hr.le hμ (ball x (γL*r)) W
      (profile_residual_gain hz hε hd W (ball x (γL*r)) hsupport.1 hsupport.2 hprofile)
    have hmass : 128*δ*Real.exp (-h)*mass μ W≤(1/2)*mass μ (ball x (γL*r)) := by
      have he := mul_le_mul_of_nonneg_left hWI (show 0≤128*δ by positivity)
      have hc : 128*δ≤1/2 := by linarith
      have hc' := mul_le_mul_of_nonneg_right hc hM.le
      nlinarith only [he,hc']
    have hfinal := (mul_le_mul_of_nonneg_left (sub_le_sub_right hmass (257*ε*mass μ W)) hr.le).trans hgain
    convert hfinal using 1 <;> first | rfl | ring

end KServer.Pilot

end


/-! The actual adapted chronological tier process and its all-step compact
pilot payment. No conditional drift or unconstructed roster is postulated. -/
noncomputable section
open scoped BigOperators
open Finset Set
namespace KServer.TierProcess
open FiniteExperiment RankTracking PosteriorRanks Pilot Chronological
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y] [Fintype Y] [DecidableEq Y]
variable {k H : ℕ} [NeZero k]

omit [MetricSpace Y] [Fintype Y] [DecidableEq Y] in
lemma request_fin (s : Configuration k Y) (σ : Fin H → Y) (t : Fin H) :
    request s σ t=σ t := by simp [request,t.isLt]

omit [MetricSpace Y] [DecidableEq Y] in
lemma request_adapted (s : Configuration k Y) {t i : ℕ} (hi : i<t)
    (σ ρ : Fin H → Y) (hh : requestHistory t σ=requestHistory t ρ) :
    request s σ i=request s ρ i := by
  unfold request
  split_ifs with hH
  · have he:=congrFun ((requestHistory_eq_iff _ _ _).mp hh) ⟨i,hH⟩
    simpa [requestPrefix,hi] using he
  · rfl

omit [DecidableEq Y] in
lemma roster_succ (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (T : Template) (r γ h : ℝ) (K : ℕ) (σ : Fin H → Y) (t : ℕ) :
    roster s law T r γ h K σ (t+1)=
      if insertTest (request s σ) (roster s law T r γ h K σ t) r K t (qualifies s law T r γ h σ t)
      then insert t (roster s law T r γ h K σ t) else roster s law T r γ h K σ t := rfl

omit [DecidableEq Y] in
lemma roster_before (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (T : Template) (r γ h : ℝ) (K : ℕ) (σ : Fin H → Y) (t : ℕ) :
    ∀ i∈roster s law T r γ h K σ t,i<t :=
  schedule_before _ _ _ _ _

omit [DecidableEq Y] in
lemma roster_adapted (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (T : Template) (r γ h : ℝ) (K : ℕ) (t : ℕ) :
    ∀ σ ρ,requestHistory t σ=requestHistory t ρ →
      roster s law T r γ h K σ t=roster s law T r γ h K ρ t := by
  induction t with
  | zero => intros; rfl
  | succ t ih =>
    intro σ ρ hh
    have hc:=ih σ ρ (requestHistory_refines t σ ρ hh)
    have hreq : ∀ i,i<t+1 → request s σ i=request s ρ i := fun i hi=>request_adapted s hi σ ρ hh
    have hq : qualifies s law T r γ h σ t ↔ qualifies s law T r γ h ρ t := by
      have hμ : mu s law (t+1) σ=mu s law (t+1) ρ := funext (fun y=>mu_adapted s law (t+1) y σ ρ hh)
      simp only [qualifies,hμ,hreq t (by omega)]
    have ha (i : ℕ) (hi : i∈roster s law T r γ h K σ t) :
        age (request s σ) (roster s law T r γ h K σ t) (20*r) i=
        age (request s ρ) (roster s law T r γ h K σ t) (20*r) i :=
      ShortRoster.age_congr (hreq i (by have hh:=roster_before s law T r γ h K σ t i hi; omega))
        (fun j hj=>hreq j (by have hh:=roster_before s law T r γ h K σ t j hj; omega))
    have ht : insertTest (request s σ) (roster s law T r γ h K σ t) r K t (qualifies s law T r γ h σ t) ↔
        insertTest (request s ρ) (roster s law T r γ h K ρ t) r K t (qualifies s law T r γ h ρ t) := by
      unfold insertTest
      rw [←hc,hq]
      refine and_congr Iff.rfl (not_congr ?_)
      apply exists_congr
      intro i
      apply and_congr_right
      intro hi
      rw [ha i hi,hreq i (by have hh:=roster_before s law T r γ h K σ t i hi; omega),hreq t (by omega)]
    rw [roster_succ,roster_succ,ht,hc]

omit [DecidableEq Y] in
lemma profile_adapted (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (T : Template) (r γ h : ℝ) (K t : ℕ) (p : Y) :
    Adapted (requestHistory t) (fun σ=>profile s law T r γ h K σ t p) := by
  intro σ ρ hh
  change ShortRoster.profile (H := H) (request s σ) r K (roster s law T r γ h K σ t) p=
    ShortRoster.profile (H := H) (request s ρ) r K (roster s law T r γ h K ρ t) p
  rw [←roster_adapted s law T r γ h K t σ ρ hh]
  exact ShortRoster.profile_congr (fun j hj=>request_adapted s (roster_before s law T r γ h K σ t j hj) σ ρ hh) r K p

lemma charge_nonneg (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (T : Template) {r : ℝ} (hr : 0 ≤ r) (γH γL δ h : ℝ) (K : ℕ) (t : Fin H) (σ : Fin H → Y) :
    0 ≤ charge s law T r γH γL δ h K t σ := by
  unfold charge
  split_ifs
  · exact mul_nonneg hr (mass_nonneg (mu_nonneg s law (t.val+1) σ) _)
  · rfl

lemma charge_le_drop (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    {T : Template} {r γH γL δ h : ℝ} {K : ℕ}
    (hr : 0 < r) (hK : 2≤K) (hσ : T.σ≤1/1000) (hR : 51201≤T.R)
    (hγH : γH≤1/100) (hσH : 10*T.σ<γH) (hγL0 : 0≤γL) (hγL : γL<T.σ)
    (hδ0 : 0≤δ) (hδ : δ≤1/256) (hh : 0≤h) (t : Fin H) (σ : Fin H → Y) (hs : 0<law.val σ) :
    charge s law T r γH γL δ h K t σ*(128*δ*Real.exp (-h)-257*(49/Real.sqrt K)) ≤
      potential T r (mu s law (t.val+1) σ) (profile s law T r γL h K σ t)-
      potential T r (mu s law (t.val+1) σ) (profile s law T r γL h K σ (t.val+1)) := by
  let S:=roster s law T r γL h K σ t
  have hbefore : ∀ i∈S,i<(t:ℕ) := roster_before s law T r γL h K σ t
  unfold charge
  split_ifs with ht
  · have hnew : roster s law T r γL h K σ (t.val+1)=insert (t:ℕ) S := by
      rw [roster_succ,ite_eq_left ht]
    have hM:=HeavyCenters.inner_mass_pos s law t σ hs hr hγL0
    have hd:=tier_pilot_drop hr hσ hR hγH hσH hγL hδ0 hδ hh
      (by positivity : 0≤49/Real.sqrt K) (mu_nonneg s law (t.val+1) σ)
      (ShortRoster.profile_bounds (H := H) (request s σ) r hK S) hM
      (by simpa only [qualifies,request_fin] using ht.1.2)
      (fun p=>by have hh:=ShortRoster.profile_error (request s σ) hr hK S t hbefore p; linarith)
      (fun p hp=>ShortRoster.profile_unit_drop (request s σ) hr hK S t hbefore ht.2 (by simpa only [request_fin] using hp))
      (fun p hp=>by
        have he:=ShortRoster.profile_increase_support (request s σ) hr hK S t hbefore ht.2 (by linarith :
          ShortRoster.profile (H := H) (request s σ) r K S p<ShortRoster.profile (H := H) (request s σ) r K (insert (t:ℕ) S) p)
        simpa only [request_fin] using he.2)
    change _ ≤ potential T r (mu s law (t.val+1) σ) (ShortRoster.profile (H := H) (request s σ) r K S)-
      potential T r (mu s law (t.val+1) σ) (ShortRoster.profile (H := H) (request s σ) r K (roster s law T r γL h K σ (t.val+1)))
    rw [hnew]
    exact hd
  · have hnew : roster s law T r γL h K σ (t.val+1)=S := by
      rw [roster_succ,ite_eq_right ht]
    change 0*_ ≤ potential T r (mu s law (t.val+1) σ) (ShortRoster.profile (H := H) (request s σ) r K S)-
      potential T r (mu s law (t.val+1) σ) (ShortRoster.profile (H := H) (request s σ) r K (roster s law T r γL h K σ (t.val+1)))
    rw [hnew,zero_mul,sub_self]


end KServer.TierProcess

end


/-! Fixed absolute tier parameters and the weighted insertion estimate.
The roster remains the chronological finite-law
roster, not a family satisfying a hypothetical insertion bound. -/
noncomputable section
open scoped BigOperators
open Finset Set
namespace KServer.TierProcess
open FiniteExperiment RankTracking PosteriorRanks Pilot Chronological
attribute [local instance] Classical.propDecidable Classical.decEq

lemma tierK_sqrt {h : ℝ} : Real.exp (32*h)≤Real.sqrt (tierK h) := by
  apply (Real.le_sqrt (Real.exp_nonneg _) (Nat.cast_nonneg _)).mpr
  have he : Real.exp (32*h)^2=Real.exp (64*h) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [he]
  exact tierK_exp h

lemma exp_large {h : ℝ} (hh : 1≤h) : (2:ℝ)^31≤Real.exp (31*h) := by
  calc (2:ℝ)^31 ≤ (Real.exp 1)^31 := pow_le_pow_left₀ (by norm_num) exp_one_ge_two _
       _ = Real.exp 31 := by rw [← Real.exp_nat_mul]; congr 1; norm_num
       _ ≤ Real.exp (31*h) := Real.exp_le_exp.mpr (by linarith)

lemma tier_error_absorb {h : ℝ} (hh : 1≤h) :
    257*(49/Real.sqrt (tierK h))≤64*heavyDelta*Real.exp (-h) := by
  have hKpos : 0<Real.sqrt (tierK h) := lt_of_lt_of_le (Real.exp_pos _) tierK_sqrt
  have hsq := tierK_sqrt (h := h)
  have he:=exp_large hh
  have hex : Real.exp (-h)*Real.exp (32*h)=Real.exp (31*h) := by
    rw [← Real.exp_add]; congr 1; ring
  have hmul:=mul_le_mul_of_nonneg_left hsq (Real.exp_nonneg (-h))
  rw [hex] at hmul
  have hbig : (12593:ℝ)≤64*heavyDelta*(Real.exp (-h)*Real.sqrt (tierK h)) := by
    dsimp [heavyDelta]
    nlinarith
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hKpos).mpr
  norm_num only [mul_assoc] at *
  exact hbig

lemma tier_reciprocal_absorb {h : ℝ} (hh : 1≤h) :
    1/(tierK h:ℝ)≤64*heavyDelta*Real.exp (-2*h) := by
  have hK : 0<(tierK h:ℝ) := lt_of_lt_of_le (Real.exp_pos _) (tierK_exp h)
  have he:=exp_large hh
  have h62 : (128:ℝ)≤Real.exp (62*h) := by
    have hmono : Real.exp (31*h)≤Real.exp (62*h) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hex : Real.exp (-2*h)*Real.exp (64*h)=Real.exp (62*h) := by
    rw [← Real.exp_add]; congr 1; ring
  have hmul:=mul_le_mul_of_nonneg_left (tierK_exp h) (Real.exp_nonneg (-2*h))
  rw [hex] at hmul
  apply (div_le_iff₀ hK).mpr
  dsimp [heavyDelta]
  nlinarith

lemma tier_weight_sum (n : ℕ) : (∑ i∈range n, Real.exp (-(i+1:ℝ)))≤1 := by
  have hq : Real.exp (-1)≤(1/2:ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) exp_one_ge_two
  have he (i : ℕ) : Real.exp (-(i+1:ℝ))=(Real.exp (-1))^(i+1) := by
    rw [←Real.exp_nat_mul]; congr 1; push_cast; ring
  calc _ ≤ ∑ i∈range n,(1/2:ℝ)^(i+1) := by
         apply sum_le_sum
         intro i _
         rw [he]
         exact pow_le_pow_left₀ (Real.exp_nonneg _) hq _
       _ = (1/2:ℝ)*∑ i∈range n,(1/2:ℝ)^i := by
         simp only [pow_succ,←sum_mul]; ring
       _ ≤ 1 := by nlinarith [sum_geometric_two_le n]

variable {Y : Type*} [MetricSpace Y] [Fintype Y] [DecidableEq Y]
variable {k H : ℕ} [NeZero k]

lemma weighted_insertion_drop (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    {r h : ℝ} (hr : 0 < r) (hh : 1≤h) (t : Fin H) (σ : Fin H → Y) (hs : 0<law.val σ) :
    charge s law tierTemplate r heavyGamma tierGamma heavyDelta h (tierK h) t σ/(tierK h:ℝ) ≤
      Real.exp (-h)*(potential tierTemplate r (mu s law (t.val+1) σ)
        (profile s law tierTemplate r tierGamma h (tierK h) σ t)-
      potential tierTemplate r (mu s law (t.val+1) σ)
        (profile s law tierTemplate r tierGamma h (tierK h) σ (t.val+1))) := by
  have hd:=charge_le_drop s law (T := tierTemplate) (γH := heavyGamma) (γL := tierGamma) (δ := heavyDelta) hr (tierK_ge_two hh)
    (by norm_num [tierTemplate]) (by norm_num [tierTemplate])
    (by norm_num [heavyGamma]) (by norm_num [tierTemplate,heavyGamma])
    (by norm_num [tierGamma]) (by norm_num [tierGamma,tierTemplate])
    (by norm_num [heavyDelta]) (by norm_num [heavyDelta]) (by linarith : 0≤h) t σ hs
  have hc:=charge_nonneg s law tierTemplate hr.le heavyGamma tierGamma heavyDelta h (tierK h) t σ
  have herr:=tier_error_absorb hh
  have hrec:=tier_reciprocal_absorb hh
  have hex : Real.exp (-h)*Real.exp (-h)=Real.exp (-2*h) := by
    rw [← Real.exp_add]; congr 1; ring
  have hlo : 64*heavyDelta*Real.exp (-h)≤128*heavyDelta*Real.exp (-h)-257*(49/Real.sqrt (tierK h)) := by linarith
  calc _ = charge s law tierTemplate r heavyGamma tierGamma heavyDelta h (tierK h) t σ*(1/(tierK h:ℝ)) := by ring
       _ ≤ charge s law tierTemplate r heavyGamma tierGamma heavyDelta h (tierK h) t σ*(64*heavyDelta*Real.exp (-2*h)) :=
         mul_le_mul_of_nonneg_left hrec hc
       _ = Real.exp (-h)*(charge s law tierTemplate r heavyGamma tierGamma heavyDelta h (tierK h) t σ*(64*heavyDelta*Real.exp (-h))) := by rw [← hex]; ring
       _ ≤ _ := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hlo hc).trans hd) (Real.exp_nonneg _)

/-- A single real tier's actual insertion charges. The multiplier exp(-h)
will be summable, so the estimate does not pay the number of tiers. -/
theorem weighted_insertion_budget (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    {r₀ τ h : ℝ} (n : ℕ) (hr : 0 < r₀) (hτ : 2≤τ) (hh : 1≤h) :
    (∑ t : Fin H,avg law.val (fun σ=>∑ j∈range n,
      charge s law tierTemplate (radius r₀ τ j) heavyGamma tierGamma heavyDelta h (tierK h) t σ/(tierK h:ℝ))) ≤
      Real.exp (-h)*(tierDrift*(1+Real.log ((k:ℝ)+1))*
        ∑ σ,law.val σ*optimalCost s (List.ofFn σ)+ ∑ j∈range n,2*radius r₀ τ j*(k:ℝ)) := by
  let g:=fun t σ j=>profile s law tierTemplate (radius r₀ τ j) tierGamma h (tierK h) σ t
  have hrad j : 0 < radius r₀ τ j := radius_pos hr (by linarith) j
  have hb:=pilot_edit_budget s law tierTemplate (γ := tierGamma) (δ := tierDelta) (g := g) n 60 hr hτ
    (by norm_num [tierGamma]) (by norm_num [tierGamma,tierTemplate])
    (by norm_num [tierDelta]) (by norm_num [tierDelta])
    (by norm_num [tierTemplate,tierGamma])
    (by intro t σ j _ y; exact ShortRoster.profile_bounds (request s σ) _ (tierK_ge_two hh) _ y)
    (by intro t σ j _ y z; simpa only [g,profile,tierTemplate,mul_div_assoc] using ShortRoster.profile_lipschitz (H := H) (request s σ) (hrad j) (tierK_ge_two hh) (roster s law tierTemplate (radius r₀ τ j) tierGamma h (tierK h) σ t) y z)
    (by intro t j _ y; exact profile_adapted s law tierTemplate (radius r₀ τ j) tierGamma h (tierK h) t y)
  have hpoint : (∑ t : Fin H,avg law.val (fun σ=>∑ j∈range n,
      charge s law tierTemplate (radius r₀ τ j) heavyGamma tierGamma heavyDelta h (tierK h) t σ/(tierK h:ℝ))) ≤
    ∑ t : Fin H,avg law.val (fun σ=>∑ j∈range n,Real.exp (-h)*
      (potential tierTemplate (radius r₀ τ j) (mu s law (t.val+1) σ) (g t σ j)-
      potential tierTemplate (radius r₀ τ j) (mu s law (t.val+1) σ) (g (t.val+1) σ j))) := by
    apply sum_le_sum
    intro t _
    apply sum_le_sum
    intro σ _
    by_cases hs : 0<law.val σ
    · apply mul_le_mul_of_nonneg_left _ (law.property.1 σ)
      exact sum_le_sum fun j _=>weighted_insertion_drop s law (hrad j) hh t σ hs
    · have hz : law.val σ=0 := le_antisymm (le_of_not_gt hs) (law.property.1 σ)
      simp [hz]
  refine hpoint.trans ?_
  simp only [← mul_sum]
  simp only [avg,mul_left_comm (law.val _) (Real.exp (-h)),← mul_sum]
  exact mul_le_mul_of_nonneg_left hb (Real.exp_nonneg (-h))

end KServer.TierProcess

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.Chronological
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y]

lemma schedule_mem (center : ℕ → Y) (r : ℝ) (K : ℕ) (qualifies : ℕ → Prop)
    (n i : ℕ) : i∈schedule center r K qualifies n ↔
      i<n ∧ insertTest center (schedule center r K qualifies i) r K i (qualifies i) := by
  induction n with
  | zero => simp [schedule]
  | succ n ih =>
    by_cases hin : i=n
    · subst i
      have hn : n∉schedule center r K qualifies n := fun hh=>Nat.lt_irrefl _ (schedule_before _ _ _ _ _ _ hh)
      simp only [schedule]
      split_ifs with he
      · simp [he]
      · simp [he,hn]
    · simp only [schedule]
      split_ifs with h
      · rw [mem_insert,or_iff_right hin,ih]
        constructor
        · intro hh; exact ⟨by omega,hh.2⟩
        · intro hh; exact ⟨by omega,hh.2⟩
      · rw [ih]
        constructor
        · intro hh; exact ⟨by omega,hh.2⟩
        · intro hh; exact ⟨by omega,hh.2⟩

end KServer.Chronological

end


/-! Present chronological balls, permanent finite-pool labels and actual
anchors. These are literal constructed keys, not assumed partitions. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TierKeys
open Chronological ActualRoster FiniteBallLaw PartitionProbabilities
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y] [Fintype Y] {H K : ℕ}

variable [Nonempty Y]

omit [Nonempty Y] in
lemma guaranteed_coverage (center : ℕ → Y) {r : ℝ} (hr : 0 < r) (hK : 0<K)
    (q : ℕ → Prop) (t : ℕ) (ht : t<H) (hq : q t)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) :
    ∃ a,key center hr.le K q life rad (t+1) (center t)=some a := by
  obtain ⟨i,hi⟩:=qualified_covered center hr hK q t ht hq life rad
  have hn : first center (schedule center r K q (t+1)) r life rad (center t)≠none := by
    intro hh
    exact (first_none_iff _ _ _ _ _ _).mp hh i hi
  cases he : first center (schedule center r K q (t+1)) r life rad (center t) with
  | none => exact False.elim (hn he)
  | some i => exact ⟨Chronological.label center hr.le K q i,by simp only [key,he,Option.map_some]⟩

omit [Nonempty Y] in
theorem spatial_bound (center : ℕ → Y) {r : ℝ} (hr : 0 < r) (hK : 1≤K)
    (q : ℕ → Prop) (life : Fin H → Lifetime K) (t : ℕ) (x y : Y) (hxy : dist x y ≤ r) :
    probability (fun _ : Fin H=>law (Y:=Y) (Real.log (1+(K:ℝ)^2)) r)
      (fun rad=>key center hr.le K q life rad t x≠key center hr.le K q life rad t y)≤
      2*Real.log (1+(K:ℝ)^2)*dist x y/r := by
  have hl : 0<Real.log (1+(K:ℝ)^2) := Real.log_pos (by
    have hk : (1:ℝ)≤K := by exact_mod_cast hK
    nlinarith)
  exact (ActualRoster.probability_mono (fun (_ : Fin H) d=>law_nonneg hl hr d) (by
    intro rad hne he
    exact hne (congrArg (Option.map (fun i : Fin H=>Chronological.label center hr.le K q i)) he))).trans
      (ActualRoster.spatial_bound center (schedule center r K q t) hr hK life x y hxy)
end KServer.TierKeys

end


/-! Fixed finite precedence alphabets: literal selection of the first covering
structure, with singleton fallback. This is the coordinate map in §07. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PriorityKeys
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I Y : Type*} [Fintype I] [LinearOrder I] {A : I → Type*}

lemma selected_some_of_mem (key : (i:I) → Y → Option (A i)) (x : Y)
    (h:(covered key x).Nonempty) :
    ∃ a : A ((covered key x).min' h),
      key ((covered key x).min' h) x=some a ∧
      selected key x=some ⟨(covered key x).min' h,a⟩ := by
  have hn:=(mem_filter.mp (min'_mem (covered key x) h)).2
  cases he:key ((covered key x).min' h) x with
  | none => exact False.elim (hn he)
  | some a => exact ⟨a,rfl,by simp only [selected,dite_eq_left h,he,Option.map_some]⟩

lemma selected_eq_of_prefix (key : (i:I) → Y → Option (A i)) (x y : Y)
    (h : I) (hx:key h x≠none) (he:∀ i≤h,key i x=key i y) :
    selected key x=selected key y := by
  have hcx:(covered key x).Nonempty:=⟨h,mem_filter.mpr ⟨mem_univ _,hx⟩⟩
  have hy:key h y≠none:=by rw [←he h le_rfl]; exact hx
  have hcy:(covered key y).Nonempty:=⟨h,mem_filter.mpr ⟨mem_univ _,hy⟩⟩
  have hmx:(covered key x).min' hcx≤h:=min'_le (covered key x) h (mem_filter.mpr ⟨mem_univ _,hx⟩)
  have hmy:(covered key y).min' hcy≤h:=min'_le (covered key y) h (mem_filter.mpr ⟨mem_univ _,hy⟩)
  obtain ⟨a,ha,hsa⟩:=selected_some_of_mem key x hcx
  obtain ⟨b,hb,hsb⟩:=selected_some_of_mem key y hcy
  have hxy:(covered key x).min' hcx≤(covered key y).min' hcy:=by
    apply min'_le
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    rw [he _ hmy,hb]
    exact Option.some_ne_none b
  have hyx:(covered key y).min' hcy≤(covered key x).min' hcx:=by
    apply min'_le
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    rw [←he _ hmx,ha]
    exact Option.some_ne_none a
  have hh:=le_antisymm hxy hyx
  rw [selected,dite_eq_left hcx,selected,dite_eq_left hcy]
  dsimp only
  exact (congrArg (fun i => (key i x).map (fun a => (⟨i,a⟩:Sigma A))) hh).trans
    (congrArg (Option.map (fun a => (⟨(covered key y).min' hcy,a⟩:Sigma A))) (he _ hmy))

lemma key_ne_prefix (keys : (i:I) → Y → Option (A i)) (x y : Y)
    (h:I) (hx:keys h x≠none) (hne:key keys x≠key keys y) :
    ∃ i≤h,keys i x≠keys i y := by
  by_contra hn
  push Not at hn
  have he:=selected_eq_of_prefix keys x y h hx hn
  have hc:(covered keys x).Nonempty:=⟨h,mem_filter.mpr ⟨mem_univ _,hx⟩⟩
  obtain ⟨a,_,ha⟩:=selected_some_of_mem keys x hc
  exact hne (by simp only [key,←he,ha])

theorem probability_prefix_bound {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ ω,0≤w ω)
    (keys : Ω → (i:I) → Y → Option (A i)) (x y : Y) (h:I)
    (hx : ∀ ω,keys ω h x≠none) :
    (∑ ω,if key (keys ω) x≠key (keys ω) y then w ω else 0)≤
      ∑ i∈univ.filter (fun i=>i≤h),∑ ω,if keys ω i x≠keys ω i y then w ω else 0 := by
  rw [sum_comm]
  apply sum_le_sum
  intro ω _
  by_cases he:key (keys ω) x=key (keys ω) y
  · simp only [he,ne_eq,not_true_eq_false,ite_false]
    exact sum_nonneg (fun i _=>by split_ifs <;> first | exact hw ω | exact le_rfl)
  · obtain ⟨i,hi,hd⟩:=key_ne_prefix (keys ω) x y h (hx ω) he
    rw [ite_eq_left he]
    calc w ω = (if keys ω i x≠keys ω i y then w ω else 0) := (ite_eq_left hd).symm
         _ ≤ ∑ j∈univ.filter (fun i=>i≤h),if keys ω j x≠keys ω j y then w ω else 0 :=
           single_le_sum (f:=fun j=>if keys ω j x≠keys ω j y then w ω else 0)
             (s:=univ.filter (fun j=>j≤h)) (fun j _=>by split_ifs <;> first | exact hw ω | exact le_rfl)
             (mem_filter.mpr ⟨mem_univ _,hi⟩)

end KServer.PriorityKeys

end


/-! Literal dyadic tier parameters and their logarithmic expense, §07. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TierDyadic
open TierProcess

lemma index_covers (L:ℝ) : L≤(2:ℝ)^(index L) := Nat.find_spec (exists_power L)

lemma index_le {L:ℝ} {n:ℕ} (hn:L≤(2:ℝ)^n) : index L≤n := Nat.find_min' _ hn

lemma index_zero {L:ℝ} (hL:L≤1) : index L=0 := by
  apply Nat.eq_zero_of_le_zero
  exact index_le (by simpa only [pow_zero] using hL)

lemma preceding_lt (L:ℝ) {n:ℕ} (hn : n < index L) : (2:ℝ)^n<L :=
  lt_of_not_ge (Nat.find_min (exists_power L) hn)

lemma tier_sum (n:ℕ) : ∑ i∈range (n+1),(2:ℝ)^i=2*(2:ℝ)^n-1 := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [sum_range_succ,ih,pow_succ]; ring

theorem qualified_sum {L:ℝ} (hL:0≤L) :
    ∑ i∈range (index L+1),(2:ℝ)^i≤4*(1+L) := by
  by_cases hz:index L=0
  · rw [hz,tier_sum,pow_zero]; linarith
  · have hp:=preceding_lt L (Nat.sub_one_lt hz)
    have hs:(index L-1)+1=index L:=by omega
    have hh:(2:ℝ)^(index L)<2*L:=by
      rw [←hs,pow_succ]
      linarith
    rw [tier_sum]
    linarith

lemma index_mono : Monotone index := by
  intro a b hab
  exact index_le (hab.trans (index_covers b))

lemma tierK_upper {h:ℝ} (hh:1≤h) : (tierK h:ℝ)≤2*Real.exp (64*h) := by
  have he : 1≤Real.exp (64*h):=Real.one_le_exp_iff.mpr (by linarith)
  have hc : (tierK h:ℝ)<Real.exp (64*h)+1 := by
    exact Nat.ceil_lt_add_one (Real.exp_nonneg _)
  linarith

lemma exp_three_ge_five : (5:ℝ)≤Real.exp 3 := by
  have h2:=exp_one_ge_two
  have hpow : (2:ℝ)^3≤(Real.exp 1)^3:=pow_le_pow_left₀ (by norm_num) h2 _
  rw [←Real.exp_nat_mul] at hpow
  norm_num at hpow
  linarith

theorem radius_coefficient {h:ℝ} (hh:1≤h) :
    Real.log (1+(tierK h:ℝ)^2)≤131*h := by
  have hk:=tierK_upper hh
  have he : 1≤Real.exp (128*h):=Real.one_le_exp_iff.mpr (by linarith)
  have hex:(Real.exp (64*h))^2=Real.exp (128*h):=by
    rw [←Real.exp_nat_mul]; congr 1; ring
  have hb : 1+(tierK h:ℝ)^2≤5*Real.exp (128*h):=by
    nlinarith [(Nat.cast_nonneg (tierK h) : (0:ℝ)≤tierK h),Real.exp_pos (64*h)]
  have h5 : (5:ℝ)≤Real.exp (3*h):=exp_three_ge_five.trans (Real.exp_le_exp.mpr (by linarith))
  have hc : 1+(tierK h:ℝ)^2≤Real.exp (131*h):=by
    calc _ ≤ 5*Real.exp (128*h) := hb
         _ ≤ Real.exp (3*h)*Real.exp (128*h) := mul_le_mul_of_nonneg_right h5 (Real.exp_nonneg _)
         _ = Real.exp (131*h) := by rw [←Real.exp_add]; congr 1; ring
  exact (Real.log_le_iff_le_exp (by positivity)).mpr hc
end KServer.TierDyadic

end


/-! Coverage and exact tier selection for the actual posterior-driven map.
The logarithmic ratio is computed from the new true-prefix metric posterior. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LevelCoverage
open FiniteExperiment Pilot TierProcess
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y] [Fintype Y] {k H : ℕ} [NeZero k]

lemma ball_mass_mono (μ:Y→ℝ) (hμ:∀ y,0 ≤ μ y) (x:Y) {r R:ℝ} (hr:r ≤ R) :
    mass μ (ball x r) ≤ mass μ (ball x R) := by
  exact sum_le_sum_of_subset_of_nonneg
    (fun y hy=> mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hy).2.trans hr⟩)
    (fun y _ _=> hμ y)

lemma ball_mass_total (μ:Y→ℝ) (hμ:∀ y,0 ≤ μ y) (x:Y) (r:ℝ) :
    mass μ (ball x r) ≤ ∑ y,μ y :=
  sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun y _ _=> hμ y)

lemma ball_mass_served (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (σ:Fin H→Y) (hs:0 < law.val σ) (t:Fin H) {r:ℝ} (hr:0 ≤ r) :
    1 ≤ mass (mu s law (t.val+1) σ) (ball (σ t) r) := by
  apply (mu_served s law t σ hs).trans
  exact single_le_sum (fun y _=> mu_nonneg s law (t.val+1) σ y)
    (by simp only [ball,mem_filter,mem_univ,true_and,dist_self]; exact hr)

lemma logratio_bounds (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (σ:Fin H→Y) (hs:0 < law.val σ) (t:Fin H) {r:ℝ} (hr:0 ≤ r) :
    0 ≤ logratio s law σ t r ∧ logratio s law σ t r ≤ Real.log k := by
  have hi:=ball_mass_served s law σ hs t (mul_nonneg (by norm_num [tierGamma] : 0 ≤ tierGamma) hr)
  have hb:=ball_mass_mono (mu s law (t.val+1) σ) (mu_nonneg s law (t.val+1) σ)
    (σ t) (show tierGamma*r ≤ 100*tierTemplate.R*r by dsimp [tierGamma,tierTemplate]; nlinarith)
  have ht:=ball_mass_total (mu s law (t.val+1) σ) (mu_nonneg s law (t.val+1) σ)
    (σ t) (100*tierTemplate.R*r)
  rw [mu_total s law (t.val+1) σ hs] at ht
  have hip:0 < mass (mu s law (t.val+1) σ) (ball (σ t) (tierGamma*r)):=by linarith
  have hp:0 < mass (mu s law (t.val+1) σ) (ball (σ t) (100*tierTemplate.R*r)):=by linarith
  have hq:1 ≤ mass (mu s law (t.val+1) σ) (ball (σ t) (100*tierTemplate.R*r))/
      mass (mu s law (t.val+1) σ) (ball (σ t) (tierGamma*r)) := (le_div_iff₀ hip).mpr (by simpa using hb)
  refine ⟨Real.log_nonneg hq,Real.log_le_log (div_pos hp hip) ?_⟩
  apply (div_le_iff₀ hip).mpr
  exact ht.trans (le_mul_of_one_le_right (Nat.cast_nonneg _) hi)

lemma qualifies_of_log (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (σ:Fin H→Y) (hs:0 < law.val σ) (t:Fin H) {r h:ℝ} (hr:0 ≤ r)
    (hh:logratio s law σ t r ≤ h) :
    qualifies s law tierTemplate r tierGamma h σ t := by
  refine ⟨t.isLt,?_⟩
  rw [request_fin]
  have hi:=ball_mass_served s law σ hs t (mul_nonneg (by norm_num [tierGamma] : 0 ≤ tierGamma) hr)
  have hb:=ball_mass_served s law σ hs t
    (mul_nonneg (by norm_num [tierTemplate] : 0 ≤ 100*tierTemplate.R) hr : 0 ≤ 100*tierTemplate.R*r)
  have hip:0 < mass (mu s law (t.val+1) σ) (ball (σ t) (tierGamma*r)):=by linarith
  have hbp:0 < mass (mu s law (t.val+1) σ) (ball (σ t) (100*tierTemplate.R*r)):=by linarith
  exact (div_le_iff₀ hip).mp ((Real.log_le_iff_le_exp (div_pos hbp hip)).mp hh)

lemma firstTier_le (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (σ:Fin H→Y) (hs:0 < law.val σ) (t:Fin H) {r:ℝ} (hr:0 ≤ r) :
    firstTier s law σ t r ≤ TierDyadic.index (Real.log k) :=
  TierDyadic.index_mono (logratio_bounds s law σ hs t hr).2

lemma firstTier_qualifies (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (σ:Fin H→Y) (hs:0 < law.val σ) (t:Fin H) {r:ℝ} (hr:0 ≤ r) :
    qualifies s law tierTemplate r tierGamma ((2:ℝ)^(firstTier s law σ t r)) σ t :=
  qualifies_of_log s law σ hs t hr (TierDyadic.index_covers _)

lemma heavy_near_center (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (σ:Fin H→Y) (t:Fin H) {r γ δ:ℝ} (hr:0 ≤ r)
    (hh:mass (mu s law (t.val+1) σ) (ball (σ t) (51200*r)) ≤ 
      (1+δ)*mass (mu s law (t.val+1) σ) (ball (σ t) (γ*r))) :
    ∃ a∈HeavyCenters.centers s law r γ δ σ (t.val+1),dist a (σ t) ≤ 8*r := by
  rw [HeavyCenters.centers_succ,HeavyCenters.step]
  split_ifs with ha
  · exact ⟨σ t,mem_insert_self _ _,by simpa only [dist_self] using mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hr⟩
  · have hn:¬∀ a∈HeavyCenters.centers s law r γ δ σ t.val,8*r < dist a (σ t):=fun hn=> ha ⟨hh,hn⟩
    push Not at hn
    exact hn

lemma heavy_agrees (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (σ:Fin H→Y) (t:Fin H) {r γ δ:ℝ} (hr:0 < r)
    (hh:mass (mu s law (t.val+1) σ) (ball (σ t) (51200*r)) ≤ 
      (1+δ)*mass (mu s law (t.val+1) σ) (ball (σ t) (γ*r)))
    (rad:Fin H→FiniteUniform.Outcome Y r) (y:Y) (hy:4*dist (σ t) y < r) :
    ∃ a,HeavyKeys.key s law r γ δ σ rad (t.val+1) (σ t)=some a ∧
      HeavyKeys.key s law r γ δ σ rad (t.val+1) y=some a := by
  obtain ⟨a,ha,hd⟩:=heavy_near_center s law σ t hr.le hh
  have hv:=HeavySchedule.run_valid s law hr γ δ σ rad (t.val+1)
  have hC:=HeavyCenters.centers_separated s law r γ δ σ (t.val+1)
  have hx:dist a (σ t) ≤ (HeavySchedule.run s law r γ δ σ rad (t.val+1)).rad a:=by linarith [(hv.1 a ha).1]
  have hz:dist a y ≤ (HeavySchedule.run s law r γ δ σ rad (t.val+1)).rad a:=by
    linarith [dist_triangle a (σ t) y,(hv.1 a ha).1,dist_nonneg (x:=σ t) (y:=y)]
  have hkx:=(HeavyKeys.centerKey_some hr hC (fun b hb=> (hv.1 b hb).2)).mpr ⟨ha,hx⟩
  have hky:=(HeavyKeys.centerKey_some hr hC (fun b hb=> (hv.1 b hb).2)).mpr ⟨ha,hz⟩
  refine ⟨(HeavySchedule.run s law r γ δ σ rad (t.val+1)).label a,?_,?_⟩  <;> 
    simp only [HeavyKeys.key,hkx,hky,Option.map_some]
end KServer.LevelCoverage

end


/-! The actual finite complete level alphabet and map of §07: chronological
heavy balls precede the dyadic tiers, and singleton keys are the fallback. -/


/-! Explicit finite independent tapes and their exact marginal laws. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.FiniteTape
open PartitionProbabilities
attribute [local instance] Classical.propDecidable Classical.decEq

variable {I:Type*} [Fintype I] {Ω:I→Type*} [∀ i,Fintype (Ω i)]

lemma marginal (w:(i:I)→Ω i→ℝ) (hw:∀ i,∑ a,w i a=1) (j:I) (f:Ω j→ℝ) :
    (∑ o,productWeight w o*f (o j))=∑ a,w j a*f a := by
  let g:(i:I)→Ω i→ℝ:=fun i a=>if h:i=j then f (h ▸ a) else 1
  have hg (o:(i:I)→Ω i):∏ i,g i (o i)=f (o j):=by simp [g]
  have he:=product_expectation w g
  simp only [hg] at he
  rw [he]
  trans ∏ i,if i=j then (∑ a,w j a*f a) else 1
  · apply prod_congr rfl
    intro i _
    by_cases hi:i=j
    · subst i; simp [g]
    · simp [g,hi,hw]
  · simp

lemma event_marginal (w:(i:I)→Ω i→ℝ) (hw:∀ i,∑ a,w i a=1) (j:I) (E:Ω j→Prop) :
    probability w (fun o=>E (o j))=∑ a,if E a then w j a else 0 := by
  have hh:=marginal w hw j (fun a=>if E a then 1 else 0)
  simpa only [probability,mul_ite,mul_one,mul_zero] using hh

variable {A B:Type*} [Fintype A] [Fintype B]

lemma pair_left (u:A→ℝ) (v:B→ℝ) (hv:∑ b,v b=1) (f:A→ℝ) :
    (∑ p,pair u v p*f p.1)=∑ a,u a*f a := by
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  simp only [pair]
  calc (∑ b,u a*v b*f a)=(u a*f a)*∑ b,v b := by rw [mul_sum]; apply sum_congr rfl; intros; ring
       _ = _ := by rw [hv,mul_one]

lemma pair_right (u:A→ℝ) (v:B→ℝ) (hu:∑ a,u a=1) (f:B→ℝ) :
    (∑ p,pair u v p*f p.2)=∑ b,v b*f b := by
  simp only [Fintype.sum_prod_type,pair,mul_assoc,←mul_sum,←sum_mul,hu,one_mul]

lemma pair_event_left (u:A→ℝ) (v:B→ℝ) (hv:∑ b,v b=1) (E:A→Prop) :
    (∑ p,if E p.1 then pair u v p else 0)=∑ a,if E a then u a else 0 := by
  simpa only [mul_ite,mul_one,mul_zero] using pair_left u v hv (fun a=>if E a then 1 else 0)

lemma pair_event_right (u:A→ℝ) (v:B→ℝ) (hu:∑ a,u a=1) (E:B→Prop) :
    (∑ p,if E p.2 then pair u v p else 0)=∑ b,if E b then v b else 0 := by
  simpa only [mul_ite,mul_one,mul_zero] using pair_right u v hu (fun b=>if E b then 1 else 0)
end KServer.FiniteTape

end


/-! A single genuine finite independent tape for the complete level map. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LevelLaw
open LevelKeys FiniteTape PartitionProbabilities FiniteExperiment TierProcess
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ}

attribute [local instance] OAI.KServer.LevelLaw.finDecEq
lemma heavy_event {r:ℝ} (hr:0 < r) (E:(Fin H→FiniteUniform.Outcome Y r)→Prop) :
    (∑ a:Tape Y k H r,if E a.1 then weight r a else 0)=
      probability (fun _ : Fin H=>FiniteUniform.law r) E :=
  pair_event_left (heavyWeight (Y:=Y) (H:=H) r) (productWeight (tierWeight (Y:=Y) (H:=H) (k:=k) r))
    (productWeight_sum _ (tier_sum hr)) E

lemma tier_event {r:ℝ} (hr:0 < r) (i:Tier k)
    (E:((Fin H→ActualRoster.Lifetime (tierK (height i))) × (Fin H→FiniteBallLaw.Outcome Y r))→Prop) :
    (∑ a:Tape Y k H r,if E (a.2 i) then weight r a else 0)=∑ b,if E b then tierWeight r i b else 0 := by
  have he:=pair_event_right (heavyWeight (Y:=Y) (H:=H) r)
    (productWeight (tierWeight (Y:=Y) (H:=H) (k:=k) r)) (heavy_sum hr) (fun a=>E (a i))
  exact he.trans (event_marginal (tierWeight r) (tier_sum hr) i E)

variable [NeZero k]

lemma heavy_spatial (s:Configuration k Y) (law:RequestLaw Y H)
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (t:ℕ) (x y:Y) (hxy:4*dist x y < r) :
    (∑ a:Tape Y k H r,if keys s law hr.le σ a t none x≠keys s law hr.le σ a t none y then weight r a else 0)
      ≤ dist x y/(4*r) := by
  change (∑ a:Tape Y k H r,if HeavyKeys.key s law r heavyGamma heavyDelta σ a.1 t x≠
    HeavyKeys.key s law r heavyGamma heavyDelta σ a.1 t y then weight r a else 0) ≤ _
  have he:=heavy_event (k:=k) hr (fun a=>HeavyKeys.key s law r heavyGamma heavyDelta σ a t x≠
    HeavyKeys.key s law r heavyGamma heavyDelta σ a t y)
  have heq : (∑ a:Tape Y k H r,if HeavyKeys.key s law r heavyGamma heavyDelta σ a.1 t x≠
    HeavyKeys.key s law r heavyGamma heavyDelta σ a.1 t y then weight r a else 0)=
    probability (fun _ : Fin H=>FiniteUniform.law r) (fun a=>HeavyKeys.key s law r heavyGamma heavyDelta σ a t x≠
    HeavyKeys.key s law r heavyGamma heavyDelta σ a t y) := by
      refine Eq.trans ?_ he
      apply sum_congr rfl
      intro a _
      split_ifs <;> rfl
  rw [heq]
  exact HeavyKeys.spatial_bound s law hr heavyGamma heavyDelta σ t x y hxy

lemma tier_spatial (s:Configuration k Y) (law:RequestLaw Y H)
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (t:ℕ) (i:Tier k) (x y:Y) (hxy:dist x y ≤ r) :
    (∑ a:Tape Y k H r,if keys s law hr.le σ a t (some i) x≠keys s law hr.le σ a t (some i) y then weight r a else 0)
      ≤ 2*Real.log (1+(tierK (height i):ℝ)^2)*dist x y/r := by
  change (∑ a:Tape Y k H r,if TierKeys.key (request s σ) hr.le (tierK (height i))
      (tierQualifies s law r σ i) (a.2 i).1 (a.2 i).2 t x≠
      TierKeys.key (request s σ) hr.le (tierK (height i)) (tierQualifies s law r σ i)
      (a.2 i).1 (a.2 i).2 t y then weight r a else 0) ≤ _
  have he:=tier_event (H:=H) hr i (fun a=>TierKeys.key (request s σ) hr.le (tierK (height i))
      (tierQualifies s law r σ i) a.1 a.2 t x≠
      TierKeys.key (request s σ) hr.le (tierK (height i)) (tierQualifies s law r σ i) a.1 a.2 t y)
  have heq : (∑ a:Tape Y k H r,if TierKeys.key (request s σ) hr.le (tierK (height i))
      (tierQualifies s law r σ i) (a.2 i).1 (a.2 i).2 t x≠
      TierKeys.key (request s σ) hr.le (tierK (height i)) (tierQualifies s law r σ i)
      (a.2 i).1 (a.2 i).2 t y then weight r a else 0)=
      ∑ b:(Fin H→ActualRoster.Lifetime (tierK (height i))) × (Fin H→FiniteBallLaw.Outcome Y r),if TierKeys.key (request s σ) hr.le (tierK (height i)) (tierQualifies s law r σ i) b.1 b.2 t x≠
        TierKeys.key (request s σ) hr.le (tierK (height i)) (tierQualifies s law r σ i) b.1 b.2 t y
        then tierWeight r i b else 0 := by
    refine Eq.trans ?_ (he.trans ?_)
    all_goals
      apply sum_congr rfl
      intro a _
      split_ifs <;> rfl
  rw [heq]
  simp only [tierWeight,Fintype.sum_prod_type,pair]
  trans ∑ life:Fin H→ActualRoster.Lifetime (tierK (height i)),
    lifetimeWeight i life*(2*Real.log (1+(tierK (height i):ℝ)^2)*dist x y/r)
  · apply sum_le_sum
    intro life _
    simp_rw [show ∀ rad, (if TierKeys.key (request s σ) hr.le (tierK (height i))
      (tierQualifies s law r σ i) life rad t x≠TierKeys.key (request s σ) hr.le (tierK (height i))
      (tierQualifies s law r σ i) life rad t y then lifetimeWeight i life*radiusWeight r i rad else 0)=
      lifetimeWeight i life*(if TierKeys.key (request s σ) hr.le (tierK (height i))
        (tierQualifies s law r σ i) life rad t x≠TierKeys.key (request s σ) hr.le (tierK (height i))
        (tierQualifies s law r σ i) life rad t y then radiusWeight r i rad else 0) by intro rad; split_ifs <;> simp]
    rw [←mul_sum]
    apply mul_le_mul_of_nonneg_left
    · convert TierKeys.spatial_bound (request s σ) hr
        (by have hh:=tierK_ge_two (height_ge i); omega) (tierQualifies s law r σ i) life t x y hxy using 1
      all_goals try with_reducible_and_instances rfl
      all_goals first | rfl | (apply sum_congr rfl; intro a _; split_ifs <;> rfl)
    · exact lifetime_nonneg i life
  · rw [←sum_mul,lifetime_sum,one_mul]
end KServer.LevelLaw

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_RosterEdits
attribute [-instance] _root_.OAI.KServer.JointExperiment.levelTapeFintype _root_.OAI.KServer.LevelKeys.alphabetFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualRoster
open RosterLifetimes FiniteBallLaw PartitionProbabilities Chronological
attribute [local instance] Classical.propDecidable Classical.decEq

lemma final_survival {K a : ℕ} (hK : 2 ≤ K) (ha : a+1=K^2) :
    actualPresence K a=survive (1/(K:ℝ)) (K^2-K) := by
  have hkk : K+1 ≤ K^2 := by nlinarith
  have hak : ¬a<K := by omega
  have hac : a<K^2 := by omega
  have he : a-K+1=K^2-K := by omega
  simp only [actualPresence,ite_eq_right hak,ite_eq_left hac,he]

/-- Unconditional marginal death bound. The extra tail is never interpreted
as a conditional compulsory hazard. -/
lemma death_marginal {K a b : ℕ} (hK : 2 ≤ K) (hab : a ≤ b) (hba : b ≤ a+1) :
    (∑ d : Lifetime K, if alive K a d ∧ ¬alive K b d then lifetimeLaw K d else 0) ≤
      (1/(K:ℝ))*actualPresence K a+
        if a<K^2 then survive (1/(K:ℝ)) (K^2-K) else 0 := by
  have hk : 1≤K := by omega
  have hq := (rate_range hk).1
  have hs := (survival_range hk a).1
  have ht := (survive_range (rate_range hk) (K^2-K)).1
  by_cases he : b=a
  · subst b
    simp only [and_not_self,ite_false,sum_const_zero]
    exact add_nonneg (mul_nonneg hq hs) (by split_ifs <;> positivity)
  · have hb : b=a+1 := by omega
    subst b
    rw [death_probability hk]
    by_cases hac : a<K^2
    · rw [ite_eq_left hac]
      by_cases hbc : a+1<K^2
      · exact (ordinary_death_bound hk hbc).trans (le_add_of_nonneg_right ht)
      · have heq : a+1=K^2 := by omega
        rw [actual_cutoff (a:=a+1) (by omega),sub_zero,final_survival hK heq]
        exact le_add_of_nonneg_left (mul_nonneg hq ht)
    · rw [ite_eq_right hac,actual_cutoff (le_of_not_gt hac),actual_cutoff (by omega)]
      simp

/-- A literal finite lifetime-tape first-coverer estimate.  The `S` hypothesis
is only a deterministic candidate count, and is discharged by chronological
ages below. -/
theorem first_retirement_bound {H K : ℕ} (hK : 2 ≤ K)
    (a b : Fin H → ℕ) (inc : ∀ i, a i≤b i ∧ b i≤a i+1)
    (cover : Fin H → Prop) (S : Finset (Fin H))
    (hS : ∀ i, cover i → a i<K^2 → i∈S) (hcard : S.card ≤ K^2) :
    PartitionProbabilities.probability (fun _ : Fin H=>lifetimeLaw K)
      (firstSeparation (fun i d=>cover i ∧ alive K (a i) d)
        (fun i d=>cover i ∧ alive K (a i) d ∧ ¬alive K (b i) d)) ≤ 49/(K:ℝ) := by
  have hk : 1≤K := by omega
  have hkp : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  let T : ℝ := survive (1/(K:ℝ)) (K^2-K)
  have hT : 0≤T := (survive_range (rate_range hk) _).1
  let ε : Fin H → ℝ := fun i=>if i∈S then (K:ℝ)*T else 0
  have heps : ∑ i, ε i=(K:ℝ)*T*S.card := by simp [ε,sum_ite_mem,mul_comm]
  have hh := SparseFirstHit.sparse_bound (fun _ : Fin H=>lifetimeLaw K)
    (fun _=>lifetime_nonneg hk) (fun _=>lifetime_sum hk)
    (hit:=fun i d=>cover i ∧ alive K (a i) d)
    (sep:=fun i d=>cover i ∧ alive K (a i) d ∧ ¬alive K (b i) d)
    (fun _ _ h=>⟨h.1,h.2.1⟩) ε (rate_range hk).1
    (fun i=>by dsimp [ε]; split_ifs <;> positivity)
  have hm (i : Fin H) : (∑ d, if cover i ∧ alive K (a i) d ∧ ¬alive K (b i) d then lifetimeLaw K d else 0) ≤
      (1/(K:ℝ))*((∑ d, if cover i ∧ alive K (a i) d then lifetimeLaw K d else 0)+ε i) := by
    by_cases hc : cover i
    · simp only [hc,true_and]
      rw [alive_probability hk]
      have hd := death_marginal hK (inc i).1 (inc i).2
      refine hd.trans ?_
      by_cases hy : a i<K^2
      · simp only [ite_eq_left hy,ε,ite_eq_left (hS i hc hy)]
        dsimp [T]
        field_simp
        exact le_rfl
      · simp only [ite_eq_right hy,add_zero]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by dsimp [ε]; split_ifs <;> positivity)) (rate_range hk).1
    · simp only [hc,false_and,ite_false,sum_const_zero,zero_add]
      exact mul_nonneg (rate_range hk).1 (by dsimp [ε]; split_ifs <;> positivity)
  have hb := hh (fun i=>by
    convert hm i using 1
    · apply sum_congr rfl
      intro d _
      by_cases h : cover i ∧ alive K (a i) d ∧ ¬alive K (b i) d <;> simp [h]
    · apply congrArg (fun z : ℝ=>(1/(K:ℝ))*(z+ε i))
      apply sum_congr rfl
      intro d _
      by_cases h : cover i ∧ alive K (a i) d <;> simp [h])
  rw [heps] at hb
  have hc : (S.card:ℝ)≤(K:ℝ)^2 := by exact_mod_cast hcard
  have hfin : (1/(K:ℝ))*(1+(K:ℝ)*T*S.card) ≤ 1/(K:ℝ)+(K:ℝ)^2*T := by
    calc _ ≤ (1/(K:ℝ))*(1+(K:ℝ)*T*(K:ℝ)^2) := by gcongr
         _ = _ := by field_simp
  exact (hb.trans hfin).trans (actual_retirement_bound K hK)

variable {Y : Type*} [MetricSpace Y] [Fintype Y] {H K : ℕ}

/-- The unconditional first-coverer retirement estimate for an actual fixed
chronological roster and arbitrary fixed radii. Increment bounds follow from
one chronological insertion, not from the realized random presences. -/
theorem chronological_retirement_bound (center : ℕ → Y) (I : Finset ℕ)
    {r : ℝ} (hr : 0 < r) (hK : 2≤K) (rad : Fin H → Outcome Y r) (p : Y)
    (b : Fin H → ℕ) (hinc : ∀ i : Fin H, age center I (20*r) i≤b i ∧ b i≤age center I (20*r) i+1) :
    PartitionProbabilities.probability (fun _ : Fin H=>lifetimeLaw K)
      (firstSeparation
        (fun i d=>(i:ℕ)∈I ∧ dist (center i) p ≤ radius r (rad i) ∧ alive K (age center I (20*r) i) d)
        (fun i d=>(i:ℕ)∈I ∧ dist (center i) p ≤ radius r (rad i) ∧
          alive K (age center I (20*r) i) d ∧ ¬alive K (b i) d)) ≤49/(K:ℝ) := by
  let a : Fin H → ℕ := fun i=>age center I (20*r) i
  let pres : Fin H → Prop := fun i=>(i:ℕ)∈I ∧ a i<K^2
  let S := SparseFirstHit.candidates r (fun i : Fin H=>center i) pres p p
  have hb := first_retirement_bound hK a b hinc
    (fun i=>(i:ℕ)∈I ∧ dist (center i) p ≤ radius r (rad i)) S
    (fun i hi ha=>by
      simp only [S,SparseFirstHit.candidates,mem_filter,mem_univ,true_and,min_self]
      exact ⟨⟨hi.1,ha⟩,hi.2.trans (radius_range hr _).2⟩)
    (SparseFirstHit.candidate_count hr.le center I pres (fun _ h=>h) p p (by simpa using hr.le))
  simpa only [a,and_assoc] using hb

end KServer.ActualRoster

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualRoster
open Chronological FiniteBallLaw PartitionProbabilities
attribute [local instance] Classical.propDecidable Classical.decEq

variable {Y : Type*} [MetricSpace Y] [Fintype Y] {H K : ℕ}

omit [Fintype Y] in
lemma age_insert_bounds (center : ℕ → Y) (I : Finset ℕ) (R : ℝ) (t i : ℕ) :
    age center I R i ≤ age center (insert t I) R i ∧
      age center (insert t I) R i ≤ age center I R i+1 := by
  refine ⟨age_mono center (subset_insert _ _) le_rfl i,?_⟩
  unfold age
  rw [filter_insert]
  split_ifs
  · exact card_insert_le _ _
  · omega

lemma old_covered_of_new (center : ℕ → Y) (I : Finset ℕ) (r : ℝ) (t : ℕ)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (p : Y) (i : Fin H)
    (hit : (i:ℕ)≠t) (hi : covered center (insert t I) r life rad p i) :
    covered center I r life rad p i := by
  refine ⟨⟨(mem_insert.mp hi.1.1).resolve_left hit,?_⟩,hi.2⟩
  exact alive_antitone K _ (age_insert_bounds center I (20*r) t i).1 hi.1.2

lemma new_covered_of_persists (center : ℕ → Y) (I : Finset ℕ) (r : ℝ) (t : ℕ)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (p : Y) (i : Fin H)
    (hi : covered center I r life rad p i) (hp : present center (insert t I) r life i) :
    covered center (insert t I) r life rad p i := ⟨hp,hi.2⟩

/-- Chronological appending cannot supersede a surviving first coverer. -/
lemma first_persists (center : ℕ → Y) (I : Finset ℕ) (r : ℝ) (t : ℕ)
    (hI : ∀ i∈I, i<t) (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r)
    (p : Y) (i : Fin H) (hfirst : first center I r life rad p=some i)
    (hp : present center (insert t I) r life i) :
    first center (insert t I) r life rad p=some i := by
  obtain ⟨hc,hbefore⟩ := (first_some_iff _ _ _ _ _ _ _).mp hfirst
  apply (first_some_iff _ _ _ _ _ _ _).mpr
  refine ⟨new_covered_of_persists center I r t life rad p i hc hp,?_⟩
  intro j hj hnew
  have hji : (j:ℕ) < i := hj
  have hit := hI i hc.1.1
  exact hbefore j hj (old_covered_of_new center I r t life rad p j (by omega) hnew)

lemma retired_iff (center : ℕ → Y) (I J : Finset ℕ) (hIJ : I⊆J) (r : ℝ)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (p : Y) :
    retired center I J r life rad p ↔
      firstSeparation
        (fun i d=>(i:ℕ)∈I ∧ dist (center i) p ≤ radius r (rad i) ∧ alive K (age center I (20*r) i) d)
        (fun i d=>(i:ℕ)∈I ∧ dist (center i) p ≤ radius r (rad i) ∧
          alive K (age center I (20*r) i) d ∧ ¬alive K (age center J (20*r) i) d) life := by
  constructor
  · rintro ⟨i,hf,hn⟩
    obtain ⟨hi,hbef⟩ := (first_some_iff _ _ _ _ _ _ _).mp hf
    refine ⟨i,⟨hi.1.1,hi.2,hi.1.2,fun h=>hn ⟨hIJ hi.1.1,h⟩⟩,?_⟩
    rintro j hj ⟨hm,hd,ha⟩
    exact hbef j hj ⟨⟨hm,ha⟩,hd⟩
  · rintro ⟨i,⟨hm,hd,ha,hn⟩,hbef⟩
    refine ⟨i,(first_some_iff _ _ _ _ _ _ _).mpr ⟨⟨⟨hm,ha⟩,hd⟩,?_⟩,fun h=>hn h.2⟩
    intro j hj hh
    exact hbef j hj ⟨hh.1.1,hh.2,hh.1.2⟩

/-- An actual insertion's exceptional first-coverer retirement row, under the
literal lifetime tape and with every radius held fixed. -/
theorem insertion_retirement (center : ℕ → Y) (I : Finset ℕ) {r : ℝ} (hr : 0 < r)
    (hK : 2≤K) (t : ℕ) (rad : Fin H → Outcome Y r) (p : Y) :
    PartitionProbabilities.probability (fun _ : Fin H=>lifetimeLaw K)
      (fun life=>retired center I (insert t I) r life rad p) ≤49/(K:ℝ) := by
  have he : (fun life=>retired center I (insert t I) r life rad p)=
      firstSeparation
        (fun i d=>(i:ℕ)∈I ∧ dist (center i) p ≤ radius r (rad i) ∧ alive K (age center I (20*r) i) d)
        (fun i d=>(i:ℕ)∈I ∧ dist (center i) p ≤ radius r (rad i) ∧
          alive K (age center I (20*r) i) d ∧ ¬alive K (age center (insert t I) (20*r) i) d) := by
    funext life
    exact propext (retired_iff center I _ (subset_insert _ _) r life rad p)
  rw [he]
  exact chronological_retirement_bound center I hr hK rad p _ (fun i=>age_insert_bounds center I (20*r) t i)

/-- The retirement error is supported inside the 22r neighbourhood. -/
lemma retired_near (center : ℕ → Y) (I : Finset ℕ) {r : ℝ} (hr : 0 < r) (t : ℕ)
    (hI : ∀ i∈I, i<t) (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r)
    (p : Y) (h : retired center I (insert t I) r life rad p) : dist p (center t)≤22*r := by
  obtain ⟨i,hf,hn⟩ := h
  obtain ⟨hi,_⟩ := (first_some_iff _ _ _ _ _ _ _).mp hf
  have hit : (i:ℕ)<t := hI i hi.1.1
  have ht : t∉I := fun hh=>Nat.lt_irrefl _ (hI t hh)
  have hc : dist (center i) (center t)≤20*r := by
    by_contra hc
    have ha := age_insert center I (20*r) ht hit
    rw [ite_eq_right hc,add_zero] at ha
    apply hn
    exact ⟨mem_insert_of_mem hi.1.1,ha ▸ hi.1.2⟩
  have hp := hi.2.trans (radius_range hr _).2
  have htri := dist_triangle p (center i) (center t)
  rw [dist_comm p (center i)] at htri
  linarith

/-- A fresh appended ball covers every point within r, pathwise even on
zero-probability lifetime tape outcomes. -/
lemma inserted_covers (center : ℕ → Y) (I : Finset ℕ) {r : ℝ} (hr : 0 < r) (hK : 0<K)
    (t : Fin H) (hI : ∀ i∈I, i<t) (life : Fin H → Lifetime K)
    (rad : Fin H → Outcome Y r) (p : Y) (hp : dist (center t) p ≤ r) :
    covered center (insert (t:ℕ) I) r life rad p t := by
  refine ⟨⟨mem_insert_self _ _,?_⟩,hp.trans (radius_range hr _).1⟩
  rw [age_new center I (20*r) hI]
  exact alive_certain hK _

lemma indicator_nonneg (P : Prop) : 0 ≤ indicator P := by unfold indicator; split_ifs <;> norm_num at *
lemma indicator_le_one (P : Prop) : indicator P≤1 := by unfold indicator; split_ifs <;> norm_num at *

/-- Literal stationary noncoverage table. -/
theorem stationary_table (center : ℕ → Y) (I : Finset ℕ) (r : ℝ) (t : ℕ)
    (hI : ∀ i∈I, i<t) (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (p : Y) :
    indicator (first center I r life rad p≠first center (insert t I) r life rad p)+
      indicator (first center (insert t I) r life rad p=none)-
      indicator (first center I r life rad p=none) ≤
        2*indicator (retired center I (insert t I) r life rad p) := by
  cases ho : first center I r life rad p with
  | none =>
    cases hn : first center (insert t I) r life rad p with
    | none => simp only [indicator]; split_ifs <;> norm_num at *
    | some j => simp only [indicator]; split_ifs <;> norm_num at *
  | some i =>
    by_cases hr : retired center I (insert t I) r life rad p
    · rw [show indicator (retired center I (insert t I) r life rad p)=1 from ite_eq_left hr]
      cases hn : first center (insert t I) r life rad p with
      | none => unfold indicator; split_ifs <;> norm_num at *
      | some j => simp only [indicator]; split_ifs <;> norm_num at *
    · have hp : present center (insert t I) r life i := by
        by_contra hp; exact hr ⟨i,ho,hp⟩
      have hn := first_persists center I r t hI life rad p i ho hp
      simp [hn,indicator,hr]

/-- Mover row, using final guaranteed coverage instead of a stationary final
position. Its retirement coefficient is one instead of two. -/
theorem mover_table (center : ℕ → Y) (I : Finset ℕ) {r : ℝ} (hr : 0 < r) (hK : 0<K)
    (t : Fin H) (hI : ∀ i∈I, i<t) (life : Fin H → Lifetime K)
    (rad : Fin H → Outcome Y r) (p : Y) :
    indicator (first center I r life rad p≠first center (insert (t:ℕ) I) r life rad p)+
      indicator (first center (insert (t:ℕ) I) r life rad (center t)=none)-
      indicator (first center I r life rad p=none) ≤
        indicator (retired center I (insert (t:ℕ) I) r life rad p) := by
  have hc := inserted_covers center I hr hK t hI life rad (center t) (by simpa using hr.le)
  have hn : first center (insert (t:ℕ) I) r life rad (center t)≠none :=
    fun h=>(first_none_iff _ _ _ _ _ _).mp h t hc
  rw [show indicator (first center (insert (t:ℕ) I) r life rad (center t)=none)=0 from ite_eq_right hn,add_zero]
  cases ho : first center I r life rad p with
  | none =>
    unfold indicator
    split_ifs <;> norm_num at *
  | some i =>
    by_cases he : retired center I (insert (t:ℕ) I) r life rad p
    · rw [show indicator (retired center I (insert (t:ℕ) I) r life rad p)=1 from ite_eq_left he]
      unfold indicator
      split_ifs <;> norm_num at *
    · have hp : present center (insert (t:ℕ) I) r life i := by
        by_contra hp; exact he ⟨i,ho,hp⟩
      have hnew := first_persists center I r t hI life rad p i ho hp
      simp [hnew,indicator,he]

end KServer.ActualRoster

end


/-! One-structure edits of the actual priority map. These lemmas keep earlier
structures fixed; in particular a covered heavy key suppresses all tier edits. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PriorityKeys
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I Y:Type*} [Fintype I] [LinearOrder I] {A:I→Type*}

lemma selected_congr_point (q₀ q₁:(i:I)→Y→Option (A i)) (x:Y)
    (h:∀ i,q₀ i x=q₁ i x) : selected q₀ x=selected q₁ x := by
  let u₀:(i:I)→Unit→Option (A i):=fun i _=>q₀ i x
  let u₁:(i:I)→Unit→Option (A i):=fun i _=>q₁ i x
  have hu:u₀=u₁:=funext fun i=>funext fun _=>h i
  change selected u₀ ()=selected u₁ ()
  rw [hu]

lemma key_congr_point (q₀ q₁:(i:I)→Y→Option (A i)) (x:Y)
    (h:∀ i,q₀ i x=q₁ i x) : key q₀ x=key q₁ x := by
  simp only [key,selected_congr_point q₀ q₁ x h]

lemma key_ne_single (q₀ q₁:(i:I)→Y→Option (A i)) (x:Y) (j:I)
    (h:∀ i,i≠j→q₀ i x=q₁ i x) (hn:key q₀ x≠key q₁ x) : q₀ j x≠q₁ j x := by
  intro he
  apply hn
  apply key_congr_point
  intro i
  by_cases hi:i=j
  · subst i; exact he
  · exact h i hi

lemma single_indicator (q₀ q₁:(i:I)→Y→Option (A i)) (x:Y) (j:I)
    (h:∀ i,i≠j→q₀ i x=q₁ i x) :
    ActualRoster.indicator (key q₀ x≠key q₁ x) ≤ ActualRoster.indicator (q₀ j x≠q₁ j x) := by
  unfold ActualRoster.indicator
  split_ifs with hn hj hj <;> try norm_num
  exact False.elim (hj (key_ne_single q₀ q₁ x j h hn))

omit [Fintype I] in
lemma stage_at (q₀ q₁:(i:I)→Y→Option (A i)) (j:I) :
    stageBefore q₀ q₁ j j=q₀ j ∧ stageAfter q₀ q₁ j j=q₁ j := by
  simp [stageBefore,stageAfter]

omit [Fintype I] in
lemma stage_outside (q₀ q₁:(i:I)→Y→Option (A i)) (j i:I) (hi:i≠j) :
    stageBefore q₀ q₁ j i=stageAfter q₀ q₁ j i := by
  simp only [stageBefore,stageAfter,le_iff_lt_or_eq,hi,or_false]

lemma stage_charge (q₀ q₁:(i:I)→Y→Option (A i)) (j:I) (x:Y) :
    ActualRoster.indicator (key (stageBefore q₀ q₁ j) x≠key (stageAfter q₀ q₁ j) x) ≤
      ActualRoster.indicator (q₀ j x≠q₁ j x) := by
  have h:=single_indicator (stageBefore q₀ q₁ j) (stageAfter q₀ q₁ j) x j
    (fun i hi=>congrFun (stage_outside q₀ q₁ j i hi) x)
  simpa only [(stage_at q₀ q₁ j).1,(stage_at q₀ q₁ j).2] using h

variable [OrderBot I]

lemma selected_bot (q:(i:I)→Y→Option (A i)) (x:Y) (a:A ⊥) (ha:q ⊥ x=some a) :
    selected q x=some ⟨⊥,a⟩ := by
  have hc:(covered q x).Nonempty:=⟨⊥,mem_filter.mpr ⟨mem_univ _,by rw [ha]; exact Option.some_ne_none _⟩⟩
  have he:(covered q x).min' hc=⊥:=bot_unique (min'_le (covered q x) ⊥ (mem_filter.mpr ⟨mem_univ _,by rw [ha]; exact Option.some_ne_none _⟩))
  unfold selected
  rw [dite_eq_left hc]
  change (q ((covered q x).min' hc) x).map (fun b=>(⟨(covered q x).min' hc,b⟩:Sigma A))=some ⟨⊥,a⟩
  rw [he,ha]
  rfl

lemma key_bot (q:(i:I)→Y→Option (A i)) (x:Y) (a:A ⊥) (ha:q ⊥ x=some a) :
    key q x=Sum.inl ⟨⊥,a⟩ := by simp only [key,selected_bot q x a ha]

lemma bot_shadow (q₀ q₁:(i:I)→Y→Option (A i)) (x:Y) (a:A ⊥)
    (h₀:q₀ ⊥ x=some a) (h₁:q₁ ⊥ x=some a) : key q₀ x=key q₁ x :=
  (key_bot q₀ x a h₀).trans (key_bot q₁ x a h₁).symm
lemma stage_shadow (q₀ q₁:(i:I)→Y→Option (A i)) {j:I} (hj:⊥<j)
    (x:Y) (a:A ⊥) (ha:q₁ ⊥ x=some a) :
    key (stageBefore q₀ q₁ j) x=key (stageAfter q₀ q₁ j) x := by
  apply bot_shadow _ _ x a
  · simpa only [stageBefore,ite_eq_left hj] using ha
  · simpa only [stageAfter,ite_eq_left hj.le] using ha
end KServer.PriorityKeys

end


/-! Literal finite-label tier edit tables. The old/new difference is bounded
through permanent chronological labels; no resampling or independence is
assumed at an observed surviving roster. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TierEdits
open ActualRoster Chronological
attribute [local instance] Classical.propDecidable Classical.decEq

lemma indicator_mono {P Q:Prop} (h:P→Q) : indicator P≤ indicator Q := by
  unfold indicator
  split_ifs with hP hQ hQ <;> try norm_num
  exact False.elim (hQ (h hP))

lemma map_charge {A B:Type*} (f:A→B) (a b:Option A) :
    indicator (a.map f≠b.map f)≤ indicator (a≠b) :=
  indicator_mono (fun hn he=>hn (congrArg (Option.map f) he))

lemma map_none {A B:Type*} (f:A→B) (a:Option A) :
    indicator (a.map f=none)=indicator (a=none) := by
  cases a <;> simp [indicator]

variable {Y:Type*} [MetricSpace Y] [Fintype Y] {H K:ℕ}

lemma key_none (center:ℕ→Y) {r:ℝ} (hr:0 ≤ r) (q:ℕ→Prop)
    (life:Fin H→Lifetime K) (rad:Fin H→FiniteBallLaw.Outcome Y r) (t:ℕ) (p:Y) :
    indicator (TierKeys.key center hr K q life rad t p=none)=
      indicator (first center (schedule center r K q t) r life rad p=none) :=
  map_none _ _

lemma key_change (center:ℕ→Y) {r:ℝ} (hr:0 ≤ r) (q:ℕ→Prop)
    (life:Fin H→Lifetime K) (rad:Fin H→FiniteBallLaw.Outcome Y r) (t:ℕ) (p:Y) :
    indicator (TierKeys.key center hr K q life rad t p≠TierKeys.key center hr K q life rad (t+1) p)≤
      indicator (first center (schedule center r K q t) r life rad p≠
        first center (schedule center r K q (t+1)) r life rad p) :=
  map_charge _ _ _

lemma stationary (center:ℕ→Y) {r:ℝ} (hr:0 ≤ r) (q:ℕ→Prop)
    (life:Fin H→Lifetime K) (rad:Fin H→FiniteBallLaw.Outcome Y r) (t:ℕ) (p:Y)
    (hin:insertTest center (schedule center r K q t) r K t (q t)) :
    indicator (TierKeys.key center hr K q life rad t p≠TierKeys.key center hr K q life rad (t+1) p)+
      indicator (TierKeys.key center hr K q life rad (t+1) p=none)-
      indicator (TierKeys.key center hr K q life rad t p=none) ≤
        2*indicator (retired center (schedule center r K q t) (schedule center r K q (t+1)) r life rad p) := by
  have ht:=stationary_table center (schedule center r K q t) r t (schedule_before _ _ _ _ _) life rad p
  have hnew:schedule center r K q (t+1)=insert t (schedule center r K q t):=by
    simp only [schedule,ite_eq_left hin]
  have hc:=key_change center hr q life rad t p
  rw [key_none,key_none,hnew]
  rw [hnew] at hc
  linarith

lemma mover (center:ℕ→Y) {r:ℝ} (hr:0 < r) (hK:0<K) (q:ℕ→Prop)
    (life:Fin H→Lifetime K) (rad:Fin H→FiniteBallLaw.Outcome Y r) (t:Fin H) (p:Y)
    (hin:insertTest center (schedule center r K q t) r K t (q t)) :
    indicator (TierKeys.key center hr.le K q life rad t p≠TierKeys.key center hr.le K q life rad (t.val+1) p)+
      indicator (TierKeys.key center hr.le K q life rad (t.val+1) (center t)=none)-
      indicator (TierKeys.key center hr.le K q life rad t p=none) ≤
        indicator (retired center (schedule center r K q t) (schedule center r K q (t.val+1)) r life rad p) := by
  have ht:=mover_table center (schedule center r K q t) hr hK t (schedule_before _ _ _ _ _) life rad p
  have hnew:schedule center r K q (t.val+1)=insert (t:ℕ) (schedule center r K q t):=by
    simp only [schedule,ite_eq_left hin]
  have hc:=key_change center hr.le q life rad t p
  rw [key_none,key_none,hnew]
  rw [hnew] at hc
  linarith

lemma no_insert (center:ℕ→Y) {r:ℝ} (hr:0 ≤ r) (q:ℕ→Prop)
    (life:Fin H→Lifetime K) (rad:Fin H→FiniteBallLaw.Outcome Y r) (t:ℕ)
    (hin:¬insertTest center (schedule center r K q t) r K t (q t)) :
    TierKeys.key center hr K q life rad (t+1)=TierKeys.key center hr K q life rad t := by
  funext p
  simp only [TierKeys.key,schedule,ite_eq_right hin]

lemma covered_inner (center:ℕ→Y) {r:ℝ} (hr:0 < r) (hK:0<K) (q:ℕ→Prop)
    (life:Fin H→Lifetime K) (rad:Fin H→FiniteBallLaw.Outcome Y r) (t:Fin H)
    (hin:insertTest center (schedule center r K q t) r K t (q t)) (p:Y) (hp:dist (center t) p ≤ r) :
    indicator (TierKeys.key center hr.le K q life rad (t.val+1) p=none)=0 := by
  rw [key_none]
  have hnew:schedule center r K q (t.val+1)=insert (t:ℕ) (schedule center r K q t):=by
    simp only [schedule,ite_eq_left hin]
  rw [hnew]
  apply ite_eq_right
  intro hh
  exact (first_none_iff _ _ _ _ _ _).mp hh t
    (inserted_covers center _ hr hK t (schedule_before _ _ _ _ _) life rad p hp)

end KServer.TierEdits

end


/-! The literal chronological tier edits inside a complete level, including
heavy-priority shadowing. Noncoverage deliberately ignores earlier structures. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LevelTierEdits
open LevelKeys LevelCoverage LevelLaw FiniteExperiment TierProcess Pilot
open ActualRoster Chronological
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

lemma charge_nonneg (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:ℕ) (i:Tier k) (p:Y) : 0 ≤ charge s law hr σ a t i p :=
  indicator_nonneg _

lemma charge_le (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:ℕ) (i:Tier k) (p:Y) :
    charge s law hr σ a t i p ≤ indicator (keys s law hr σ a t (i:Structure k) p≠
      keys s law hr σ a (t+1) (i:Structure k) p) :=
  PriorityKeys.stage_charge _ _ _ _

lemma stationary (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:ℕ) (i:Tier k) (p:Y)
    (hin:inserted s law r σ t i) :
    charge s law hr σ a t i p+uncovered s law hr σ a (t+1) i p-
      uncovered s law hr σ a t i p ≤ 2*indicator (retirement s law r σ a t i p) := by
  have ht:=TierEdits.stationary (request s σ) hr (tierQualifies s law r σ i)
    (a.2 i).1 (a.2 i).2 t p hin
  have hc:=charge_le s law hr σ a t i p
  dsimp only [uncovered,retirement,keys] at hc ⊢
  linarith

lemma mover (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (i:Tier k) (p:Y)
    (hin:inserted s law r σ t i) :
    charge s law hr.le σ a t i p+uncovered s law hr.le σ a (t.val+1) i (σ t)-
      uncovered s law hr.le σ a t i p ≤ indicator (retirement s law r σ a t i p) := by
  have ht:=TierEdits.mover (request s σ) hr
    (by have hh:=tierK_ge_two (height_ge i); omega) (tierQualifies s law r σ i)
    (a.2 i).1 (a.2 i).2 t p hin
  rw [request_fin] at ht
  have hc:=charge_le s law hr.le σ a t i p
  dsimp only [uncovered,retirement,keys] at hc ⊢
  linarith

lemma no_insert_charge (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:ℕ) (i:Tier k) (p:Y)
    (hin:¬inserted s law r σ t i) : charge s law hr σ a t i p=0 := by
  apply le_antisymm _ (charge_nonneg s law hr σ a t i p)
  have hc:=charge_le s law hr σ a t i p
  have he:=congrFun (TierEdits.no_insert (request s σ) hr
    (tierQualifies s law r σ i) (a.2 i).1 (a.2 i).2 t hin) p
  change keys s law hr σ a (t+1) (i:Structure k) p=keys s law hr σ a t (i:Structure k) p at he
  simpa only [he,ne_self_iff_false,indicator,ite_false] using hc

lemma no_insert_stationary (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:ℕ) (i:Tier k) (p:Y)
    (hin:¬inserted s law r σ t i) :
    charge s law hr σ a t i p+uncovered s law hr σ a (t+1) i p-
      uncovered s law hr σ a t i p=0 := by
  rw [no_insert_charge s law hr σ a t i p hin,zero_add]
  have he:=congrFun (TierEdits.no_insert (request s σ) hr
    (tierQualifies s law r σ i) (a.2 i).1 (a.2 i).2 t hin) p
  change keys s law hr σ a (t+1) (i:Structure k) p=keys s law hr σ a t (i:Structure k) p at he
  change indicator (_=none)-indicator (_=none)=0
  rw [he,sub_self]

lemma covered_qualified (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (i:Tier k)
    (hq:tierQualifies s law r σ i t) : uncovered s law hr.le σ a (t.val+1) i (σ t)=0 := by
  obtain ⟨b,hb⟩:=TierKeys.guaranteed_coverage (request s σ) hr
    (by have hh:=tierK_ge_two (height_ge i); omega) (tierQualifies s law r σ i)
    t t.isLt hq (a.2 i).1 (a.2 i).2
  rw [request_fin] at hb
  change keys s law hr.le σ a (t.val+1) (i:Structure k) (σ t)=some b at hb
  change indicator (_=none)=0
  rw [hb]
  exact ite_eq_right (Option.some_ne_none _)

attribute [local instance] OAI.KServer.LevelTierEdits.finDecEq
lemma no_insert_mover (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (i:Tier k) (p:Y)
    (hin:¬inserted s law r σ t i) :
    charge s law hr.le σ a t i p+uncovered s law hr.le σ a (t.val+1) i (σ t)-
      uncovered s law hr.le σ a t i p ≤
        if tierQualifies s law r σ i t then 0 else
          indicator (keys s law hr.le σ a (t.val+1) (i:Structure k) (σ t)≠
            keys s law hr.le σ a (t.val+1) (i:Structure k) p) := by
  rw [no_insert_charge s law hr.le σ a t i p hin,zero_add]
  by_cases hq:tierQualifies s law r σ i t
  · rw [ite_eq_left hq,covered_qualified s law hr σ a t i hq]
    exact sub_nonpos.mpr (indicator_nonneg _)
  · rw [ite_eq_right hq]
    have he:=congrFun (TierEdits.no_insert (request s σ) hr.le
      (tierQualifies s law r σ i) (a.2 i).1 (a.2 i).2 t hin) p
    change keys s law hr.le σ a (t.val+1) (i:Structure k) p=keys s law hr.le σ a t (i:Structure k) p at he
    unfold uncovered
    rw [←he]
    unfold indicator
    split_ifs with hx hp hn hp hn hn <;> try norm_num
    all_goals simp_all

lemma heavy_inner_covers (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (p:Y)
    (hh:mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (51200*r)) ≤
      (1+heavyDelta)*mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (heavyGamma*r)))
    (hp:dist (σ t) p ≤ heavyGamma*r) : ∃ b,keys s law hr.le σ a (t.val+1) (⊥:Structure k) p=some b := by
  obtain ⟨c,hc,hd⟩:=heavy_near_center s law σ t hr.le hh
  have hv:=HeavySchedule.run_valid s law hr heavyGamma heavyDelta σ a.1 (t.val+1)
  have hC:=HeavyCenters.centers_separated s law r heavyGamma heavyDelta σ (t.val+1)
  have hcp:dist c p ≤ (HeavySchedule.run s law r heavyGamma heavyDelta σ a.1 (t.val+1)).rad c:=by
    have hγ:heavyGamma ≤ 1:=by norm_num [heavyGamma]
    have hm:=mul_le_mul_of_nonneg_right hγ hr.le
    linarith [dist_triangle c (σ t) p,(hv.1 c hc).1]
  have he:=(HeavyKeys.centerKey_some hr hC (fun b hb=>(hv.1 b hb).2)).mpr ⟨hc,hcp⟩
  refine ⟨(HeavySchedule.run s law r heavyGamma heavyDelta σ a.1 (t.val+1)).label c,?_⟩
  change HeavyKeys.key _ _ _ _ _ _ _ _ _=some _
  simp only [HeavyKeys.key,he,Option.map_some]

lemma heavy_inner_charge (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (i:Tier k) (p:Y)
    (hh:mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (51200*r)) ≤
      (1+heavyDelta)*mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (heavyGamma*r)))
    (hp:dist (σ t) p ≤ heavyGamma*r) : charge s law hr.le σ a t i p=0 := by
  obtain ⟨b,hb⟩:=heavy_inner_covers s law hr σ a t p hh hp
  have he:=PriorityKeys.stage_shadow (I:=Structure k) (keys s law hr.le σ a t)
    (keys s law hr.le σ a (t.val+1)) (j:=(i:Structure k)) (WithBot.bot_lt_coe i) p b hb
  exact ite_eq_right (not_not.mpr he)

lemma heavy_inner_stationary (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (i:Tier k) (p:Y)
    (hin:inserted s law r σ t i)
    (hh:mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (51200*r)) ≤
      (1+heavyDelta)*mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (heavyGamma*r)))
    (hp:dist (σ t) p ≤ heavyGamma*r) :
    charge s law hr.le σ a t i p+uncovered s law hr.le σ a (t.val+1) i p-
      uncovered s law hr.le σ a t i p ≤ 0 := by
  rw [heavy_inner_charge s law hr σ a t i p hh hp,zero_add]
  have hcov:=TierEdits.covered_inner (request s σ) hr
    (by have hh:=tierK_ge_two (height_ge i); omega) (tierQualifies s law r σ i)
    (a.2 i).1 (a.2 i).2 t hin p
    (by rw [request_fin]; exact hp.trans (mul_le_of_le_one_left hr.le (by norm_num [heavyGamma])))
  change uncovered s law hr.le σ a (t.val+1) i p=0 at hcov
  rw [hcov]
  exact sub_nonpos.mpr (indicator_nonneg _)

end KServer.LevelTierEdits

end


/-! Average actual tier retirements over the full finite partition tape, not
conditionally on surviving entries. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LevelRetirement
open LevelKeys LevelCoverage LevelLaw LevelTierEdits FiniteExperiment TierProcess Pilot
open ActualRoster Chronological FiniteTape PartitionProbabilities
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ}

attribute [local instance] OAI.KServer.LevelRetirement.finDecEq
lemma tier_lifetime_bound {r:ℝ} (hr:0 < r) (i:Tier k)
    (E:(Fin H→Lifetime (tierK (height i)))→(Fin H→FiniteBallLaw.Outcome Y r)→Prop)
    (c:ℝ) (hc:∀ rad,probability (fun _ : Fin H=>lifetimeLaw (tierK (height i)))
      (fun life=>E life rad) ≤ c) :
    (∑ a:Tape Y k H r,if E (a.2 i).1 (a.2 i).2 then weight r a else 0) ≤ c := by
  have he:=tier_event (H:=H) hr i (fun b=>E b.1 b.2)
  have heq : (∑ a:Tape Y k H r,if E (a.2 i).1 (a.2 i).2 then weight r a else 0)=
      ∑ b:(Fin H→Lifetime (tierK (height i))) × (Fin H→FiniteBallLaw.Outcome Y r),
        if E b.1 b.2 then tierWeight r i b else 0 := by
    refine Eq.trans ?_ (he.trans ?_) <;> apply sum_congr rfl <;> intro a _ <;> split_ifs <;> rfl
  rw [heq]
  simp only [Fintype.sum_prod_type,tierWeight,pair]
  rw [sum_comm]
  calc (∑ rad,∑ life,if E life rad then lifetimeWeight i life*radiusWeight r i rad else 0)=
        ∑ rad,radiusWeight r i rad*(∑ life,if E life rad then lifetimeWeight i life else 0) := by
          apply sum_congr rfl
          intro rad _
          rw [mul_sum]
          apply sum_congr rfl
          intro life _
          split_ifs <;> ring
       _ ≤ ∑ rad,radiusWeight r i rad*c := by
          apply sum_le_sum
          intro rad _
          apply mul_le_mul_of_nonneg_left _ (radius_nonneg hr i rad)
          exact hc rad
       _ = c := by rw [←sum_mul,radius_sum hr i,one_mul]

variable [NeZero k]

lemma retirement_bound (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (t:ℕ) (i:Tier k) (p:Y) (hin:inserted s law r σ t i) :
    (∑ a:Tape Y k H r,if retirement s law r σ a t i p then weight r a else 0) ≤
      49/(tierK (height i):ℝ) := by
  have hnew:schedule (request s σ) r (tierK (height i)) (tierQualifies s law r σ i) (t+1)=
      insert t (schedule (request s σ) r (tierK (height i)) (tierQualifies s law r σ i) t):=by
    change insertTest _ _ _ _ _ _ at hin
    simp only [schedule,ite_eq_left hin]
  unfold retirement
  rw [hnew]
  refine tier_lifetime_bound hr i (fun life rad => retired (request s σ)
    (schedule (request s σ) r (tierK (height i)) (tierQualifies s law r σ i) t)
    (insert t (schedule (request s σ) r (tierK (height i)) (tierQualifies s law r σ i) t))
    r life rad p) _ ?_
  intro rad
  exact insertion_retirement (request s σ) _ hr (tierK_ge_two (height_ge i)) t rad p

lemma retirement_far (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (i:Tier k) (p:Y)
    (hin:inserted s law r σ t i) (hp:22*r < dist (σ t) p) :
    ¬retirement s law r σ a t i p := by
  intro he
  have hnew:schedule (request s σ) r (tierK (height i)) (tierQualifies s law r σ i) (t.val+1)=
      insert (t:ℕ) (schedule (request s σ) r (tierK (height i)) (tierQualifies s law r σ i) t):=by
    change insertTest _ _ _ _ _ _ at hin
    simp only [schedule,ite_eq_left hin]
  unfold retirement at he
  rw [hnew] at he
  have hn:=retired_near (request s σ) _ hr t (schedule_before _ _ _ _ _) (a.2 i).1 (a.2 i).2 p he
  rw [request_fin,dist_comm] at hn
  exact not_lt_of_ge hn hp

omit [NeZero k] in
lemma mean_mono {r:ℝ} (hr:0 < r) {f g:Tape Y k H r→ℝ} (h:∀ a,f a≤g a) : mean r f ≤ mean r g :=
  sum_le_sum (fun a _=>mul_le_mul_of_nonneg_left (h a) (weight_nonneg hr a))

omit [NeZero k] in
lemma mean_const {r:ℝ} (hr:0 < r) (c:ℝ) : mean (Y:=Y) (k:=k) (H:=H) r (fun _=>c)=c := by
  unfold mean
  rw [←sum_mul,weight_sum hr,one_mul]

omit [NeZero k] in
lemma mean_indicator (r:ℝ) (E:Tape Y k H r→Prop) :
    mean r (fun a=>indicator (E a))=∑ a,if E a then weight r a else 0 := by
  unfold mean
  apply sum_congr rfl
  intro a _
  by_cases h:E a
  · simp only [indicator,ite_eq_left h,mul_one]
  · simp only [indicator,ite_eq_right h,mul_zero]

omit [NeZero k] in
lemma mean_scale (r:ℝ) (c:ℝ) (f:Tape Y k H r→ℝ) :
    mean r (fun a=>c*f a)=c*mean r f := by
  unfold mean
  rw [mul_sum]
  apply sum_congr rfl
  intro a _
  ring

lemma stationary_mean (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (t:Fin H) (i:Tier k) (p:Y) (hin:inserted s law r σ t i) :
    mean r (fun a=>LevelTierEdits.charge s law hr.le σ a t i p+
      uncovered s law hr.le σ a (t.val+1) i p-uncovered s law hr.le σ a t i p) ≤
        if dist (σ t) p≤22*r ∧ ¬(mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (51200*r)) ≤
          (1+heavyDelta)*mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (heavyGamma*r)) ∧
          dist (σ t) p≤heavyGamma*r) then 98/(tierK (height i):ℝ) else 0 := by
  by_cases hp:dist (σ t) p≤22*r
  · by_cases hh:mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (51200*r)) ≤
          (1+heavyDelta)*mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (heavyGamma*r)) ∧
          dist (σ t) p≤heavyGamma*r
    · rw [ite_eq_right (fun h=>h.2 hh)]
      exact (mean_mono hr (fun a=>heavy_inner_stationary s law hr σ a t i p hin hh.1 hh.2)).trans_eq (mean_const hr 0)
    · rw [ite_eq_left ⟨hp,hh⟩]
      have hb:=mean_mono hr (fun a=>LevelTierEdits.stationary s law hr.le σ a t i p hin)
      rw [mean_scale,mean_indicator] at hb
      have hc:=mul_le_mul_of_nonneg_left (retirement_bound s law hr σ t i p hin) (by norm_num : (0:ℝ)≤2)
      exact hb.trans (by convert hc using 1; ring)
  · rw [ite_eq_right (fun h=>hp h.1)]
    have hb:=mean_mono hr (fun a=>LevelTierEdits.stationary s law hr.le σ a t i p hin)
    have hz (a:Tape Y k H r):indicator (retirement s law r σ a t i p)=0:=
      ite_eq_right (retirement_far s law hr σ a t i p hin (lt_of_not_ge hp))
    simp only [hz,mul_zero,mean_const hr] at hb
    exact hb

lemma mover_mean (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (t:Fin H) (i:Tier k) (p:Y) (hin:inserted s law r σ t i) :
    mean r (fun a=>LevelTierEdits.charge s law hr.le σ a t i p+
      uncovered s law hr.le σ a (t.val+1) i (σ t)-uncovered s law hr.le σ a t i p) ≤
        49/(tierK (height i):ℝ) := by
  have hb:=mean_mono hr (fun a=>LevelTierEdits.mover s law hr σ a t i p hin)
  rw [mean_indicator] at hb
  exact hb.trans (retirement_bound s law hr σ t i p hin)

end KServer.LevelRetirement

end


/-! Exact scale-log sums for the true post-request metric posterior. The same
absolute shift works for the heavy test and all dyadic tier tests. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LevelScale
open FiniteExperiment Pilot LevelCoverage TierProcess
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [Fintype Y] [MetricSpace Y]

lemma log_ball_bounds (μ:Y→ℝ) (hμ:∀ y,0 ≤ μ y) (x:Y) (hx:1 ≤ μ x)
    {k r:ℝ} (hk:∑ y,μ y=k) (hr:0 ≤ r) :
    Real.log (mass μ (ball x r)) ∈ Set.Icc 0 (Real.log k) := by
  have hl:1 ≤ mass μ (ball x r):=hx.trans (single_le_sum (fun y _=>hμ y)
    (by simp only [ball,mem_filter,mem_univ,true_and,dist_self]; exact hr))
  have hu:mass μ (ball x r) ≤ k:=by simpa only [hk] using ball_mass_total μ hμ x r
  exact ⟨Real.log_nonneg hl,Real.log_le_log (by linarith) hu⟩

lemma mass_positive (μ:Y→ℝ) (hμ:∀ y,0 ≤ μ y) (x:Y) (hx:1 ≤ μ x)
    {r:ℝ} (hr:0 ≤ r) : 0 < mass μ (ball x r) := by
  have hl:1 ≤ mass μ (ball x r):=hx.trans (single_le_sum (fun y _=>hμ y)
    (by simp only [ball,mem_filter,mem_univ,true_and,dist_self]; exact hr))
  linarith

lemma logratio_sum (μ:Y→ℝ) (hμ:∀ y,0 ≤ μ y) (x:Y) (hx:1 ≤ μ x)
    {k r₀ τ γ D:ℝ} (hk:∑ y,μ y=k) (hr:0 ≤ r₀) (hτ:0 ≤ τ)
    (hγ:0 < γ) (hγD:γ ≤ D) (p n:ℕ) (hp:D ≤ γ*τ^p) :
    (∑ j∈range n,Real.log (mass μ (ball x (D*radius r₀ τ j))/
      mass μ (ball x (γ*radius r₀ τ j)))) ≤ p*Real.log k := by
  have hrad (j:ℕ):0 ≤ radius r₀ τ j:=mul_nonneg hr (pow_nonneg hτ _)
  have hm (j:ℕ):0 < mass μ (ball x (γ*radius r₀ τ j)):=
    mass_positive μ hμ x hx (mul_nonneg hγ.le (hrad j))
  have hM (j:ℕ):0 < mass μ (ball x (D*radius r₀ τ j)):=
    mass_positive μ hμ x hx (mul_nonneg (hγ.le.trans hγD) (hrad j))
  have hstep (j:ℕ):mass μ (ball x (D*radius r₀ τ j)) ≤
      mass μ (ball x (γ*radius r₀ τ (j+p))):=by
    apply ball_mass_mono μ hμ x
    rw [radius_add]
    nlinarith [mul_le_mul_of_nonneg_right hp (hrad j)]
  calc _ ≤ ∑ j∈range n,(Real.log (mass μ (ball x (γ*radius r₀ τ (j+p))))-
          Real.log (mass μ (ball x (γ*radius r₀ τ j)))) := by
        apply sum_le_sum
        intro j _
        rw [Real.log_div (hM j).ne' (hm j).ne']
        exact sub_le_sub_right (Real.log_le_log (hM j) (hstep j)) _
       _ ≤ _ := by
        simpa using ScaleMass.shifted_sum_le (fun j=>Real.log (mass μ (ball x (γ*radius r₀ τ j))))
          0 (Real.log k) (fun j=>log_ball_bounds μ hμ x hx hk (mul_nonneg hγ.le (hrad j))) n p

lemma nonheavy_count (μ:Y→ℝ) (hμ:∀ y,0 ≤ μ y) (x:Y) (hx:1 ≤ μ x)
    {k r₀ τ γ D δ:ℝ} (hk:∑ y,μ y=k) (hr:0 ≤ r₀) (hτ:0 ≤ τ)
    (hγ:0 < γ) (hγD:γ ≤ D) (hδ:0 < δ) (p n:ℕ) (hp:D ≤ γ*τ^p) :
    (∑ j∈range n,if mass μ (ball x (D*radius r₀ τ j)) ≤
      (1+δ)*mass μ (ball x (γ*radius r₀ τ j)) then (0:ℝ) else 1)
      ≤ (p*Real.log k)/Real.log (1+δ) := by
  have hlog:0 < Real.log (1+δ):=Real.log_pos (by linarith)
  apply (le_div_iff₀ hlog).mpr
  trans ∑ j∈range n,Real.log (mass μ (ball x (D*radius r₀ τ j))/
      mass μ (ball x (γ*radius r₀ τ j)))
  · rw [sum_mul]
    apply sum_le_sum
    intro j _
    have hrad:0 ≤ radius r₀ τ j:=mul_nonneg hr (pow_nonneg hτ _)
    have hm:=mass_positive μ hμ x hx (mul_nonneg hγ.le hrad)
    have hM:=mass_positive μ hμ x hx (mul_nonneg (hγ.le.trans hγD) hrad)
    have hab:=ball_mass_mono μ hμ x (mul_le_mul_of_nonneg_right hγD hrad)
    split_ifs with hh
    · rw [zero_mul]
      exact Real.log_nonneg ((le_div_iff₀ hm).mpr (by simpa using hab))
    · rw [one_mul]
      apply Real.log_le_log (by linarith : 0 < 1+δ)
      exact (le_div_iff₀ hm).mpr (le_of_lt (lt_of_not_ge hh))
  · exact logratio_sum μ hμ x hx hk hr hτ hγ hγD p n hp

lemma tier_shift {τ:ℝ} (hτ:2 ≤ τ) : 100*tierTemplate.R ≤ tierGamma*τ^60 := by
  have hp:(2:ℝ)^60 ≤ τ^60:=pow_le_pow_left₀ (by norm_num) hτ _
  have hc:100*tierTemplate.R ≤ tierGamma*(2:ℝ)^60:=by norm_num [tierTemplate,tierGamma]
  exact hc.trans (mul_le_mul_of_nonneg_left hp (by norm_num [tierGamma]))

lemma heavy_shift {τ:ℝ} (hτ:2 ≤ τ) : (51200:ℝ) ≤ heavyGamma*τ^60 := by
  have hp:(2:ℝ)^60 ≤ τ^60:=pow_le_pow_left₀ (by norm_num) hτ _
  have hc:(51200:ℝ) ≤ heavyGamma*(2:ℝ)^60:=by norm_num [heavyGamma]
  exact hc.trans (mul_le_mul_of_nonneg_left hp (by norm_num [heavyGamma]))

variable {k H:ℕ} [NeZero k]

lemma actual_logratio_sum (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (σ:Fin H→Y) (hσ:0 < law.val σ) (t:Fin H) {r₀ τ:ℝ} (hr:0 ≤ r₀) (hτ:2 ≤ τ) (n:ℕ) :
    (∑ j∈range n, logratio s law σ t (radius r₀ τ j)) ≤ 60*Real.log k := by
  exact logratio_sum (mu s law (t.val+1) σ) (mu_nonneg s law (t.val+1) σ)
    (σ t) (mu_served s law t σ hσ) (mu_total s law (t.val+1) σ hσ) hr (by linarith)
    (by norm_num [tierGamma]) (by norm_num [tierGamma,tierTemplate]) 60 n (tier_shift hτ)

lemma actual_nonheavy_count (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (σ:Fin H→Y) (hσ:0 < law.val σ) (t:Fin H) {r₀ τ:ℝ} (hr:0 ≤ r₀) (hτ:2 ≤ τ) (n:ℕ) :
    (∑ j∈range n,if mass (mu s law (t.val+1) σ) (ball (σ t) (51200*radius r₀ τ j)) ≤
      (1+heavyDelta)*mass (mu s law (t.val+1) σ) (ball (σ t) (heavyGamma*radius r₀ τ j)) then (0:ℝ) else 1)
      ≤ (60*Real.log k)/Real.log (1+heavyDelta) := by
  exact nonheavy_count (mu s law (t.val+1) σ) (mu_nonneg s law (t.val+1) σ)
    (σ t) (mu_served s law t σ hσ) (mu_total s law (t.val+1) σ hσ) hr (by linarith)
    (by norm_num [heavyGamma]) (by norm_num [heavyGamma]) (by norm_num [heavyDelta])
    60 n (heavy_shift hτ)
end KServer.LevelScale

end


/-! The complete-level first-covering probability bound, with its individual
local log ratio (not the largest tier times the number of scales). -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LevelSpatial
open LevelKeys LevelCoverage LevelLaw FiniteExperiment TierProcess Pilot
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

lemma fin_prefix_sum (f:ℕ→ℝ) {N n:ℕ} (hn:n < N) :
    (∑ i:Fin N,if i.val ≤ n then f i else 0)=∑ i∈range (n+1),f i := by
  have he:=Fin.sum_univ_eq_sum_range (fun m:ℕ=>if m ≤ n then f m else 0) N
  rw [he]
  calc (∑ i∈range N,if i ≤ n then f i else 0)=∑ i∈range (n+1),if i ≤ n then f i else 0 := by
        symm
        refine sum_subset (range_mono (by omega)) ?_
        intro i hi hni
        exact ite_eq_right (by simp only [mem_range] at hni; omega)
       _ = _ := by apply sum_congr rfl; intro i hi; exact ite_eq_left (by have := mem_range.mp hi; omega)

lemma structure_prefix_sum {k:ℕ} (p:Structure k→ℝ) (i:Tier k) :
    (∑ j∈univ.filter (fun j:Structure k=>j ≤ (i:Structure k)),p j)=
      p (⊥:Structure k)+∑ j:Tier k,if j ≤ i then p (j:Structure k) else 0 := by
  let f : Structure k → ℝ := fun j=>if j ≤ (i:Structure k) then p j else 0
  have hs : (∑ j∈univ.filter (fun j:Structure k=>j ≤ (i:Structure k)),p j)=∑ j:Structure k,f j := by
    rw [sum_filter]
  rw [hs]
  let e : Structure k ≃ Option (Tier k) := Equiv.refl _
  rw [Fintype.sum_equiv e f (fun j=>f (e.symm j)) (fun _=>rfl)]
  have he:=Fintype.sum_option (fun j:Option (Tier k)=>f (e.symm j))
  rw [he]
  have hb : f (e.symm none)=p (⊥:Structure k) := by
    change f (⊥:Structure k)=_
    simp only [f,bot_le,ite_true]
  rw [hb]
  congr 1
  apply sum_congr rfl
  intro j _
  change (if (j:Structure k) ≤ (i:Structure k) then p (j:Structure k) else 0)=_
  simp only [WithBot.coe_le_coe]

variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

attribute [local instance] OAI.KServer.LevelSpatial.finDecEq
lemma separation_le_one (s:Configuration k Y) (law:RequestLaw Y H)
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (t:ℕ) (x y:Y) : separation s law hr.le σ t x y ≤ 1 := by
  calc _ ≤ ∑ a:Tape Y k H r,weight r a := by
        apply sum_le_sum; intro a _; split_ifs <;> first | exact le_rfl | exact weight_nonneg hr a
       _ = 1 := weight_sum hr

lemma prefix_bound (s:Configuration k Y) (law:RequestLaw Y H)
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (t:ℕ) (x y:Y) (hxy:4*dist x y < r)
    (i:Tier k) (hi:∀ a:Tape Y k H r,keys s law hr.le σ a t (some i) x≠none) :
    separation s law hr.le σ t x y ≤ dist x y/(4*r)+
      (262*dist x y/r)*(∑ j∈range (i.val+1),(2:ℝ)^j) := by
  have hp:=PriorityKeys.probability_prefix_bound (I:=Structure k) (weight r) (weight_nonneg hr)
    (fun a:Tape Y k H r=>keys s law hr.le σ a t) x y (i:Structure k) hi
  have he : separation s law hr.le σ t x y =
      ∑ a:Tape Y k H r,if PriorityKeys.key (I:=Structure k) (keys s law hr.le σ a t) x ≠
        PriorityKeys.key (I:=Structure k) (keys s law hr.le σ a t) y then weight r a else 0 := by
    apply sum_congr rfl
    intro a _
    unfold LevelKeys.map
    split_ifs <;> rfl
  have hp' : separation s law hr.le σ t x y ≤
      ∑ j∈univ.filter (fun j:Structure k=>j ≤ (i:Structure k)),
        ∑ a:Tape Y k H r,if keys s law hr.le σ a t j x≠keys s law hr.le σ a t j y then weight r a else 0 := by
    rw [he]
    convert hp using 1
    · apply sum_congr rfl
      intro a _
      split_ifs <;> rfl
    · simp only [sum_filter]
      apply sum_congr rfl
      intro j _
      split_ifs <;> rfl
  rw [structure_prefix_sum] at hp'
  refine hp'.trans ?_
  apply add_le_add (heavy_spatial s law hr σ t x y hxy)
  have hs:(∑ j:Tier k,if j ≤ i then height j else 0)=∑ j∈range (i.val+1),(2:ℝ)^j := by
    exact fin_prefix_sum (fun n=>(2:ℝ)^n) i.isLt
  rw [←hs,mul_sum]
  apply sum_le_sum
  intro j _
  by_cases hj:j ≤ i
  · simp only [hj,ite_true]
    have hd:dist x y ≤ r:=by linarith [dist_nonneg (x:=x) (y:=y)]
    have hb:=tier_spatial s law hr σ t j x y hd
    have hl:Real.log (1+(tierK (height j):ℝ)^2) ≤ 131*height j:=
      TierDyadic.radius_coefficient (height_ge j)
    apply hb.trans
    have hc:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl (by norm_num : (0:ℝ) ≤ 2))
      (div_nonneg (dist_nonneg (x:=x) (y:=y)) hr.le)
    convert hc using 1 <;> ring
  · simp only [hj,ite_false,mul_zero,le_refl]

lemma request_bound (s:Configuration k Y) (law:RequestLaw Y H)
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (hσ:0 < law.val σ) (t:Fin H) (y:Y)
    (hxy:4*dist (σ t) y < r) :
    separation s law hr.le σ (t.val+1) (σ t) y ≤
      1050*(1+logratio s law σ t r)*dist (σ t) y/r := by
  let i:Tier k:=⟨firstTier s law σ t r,by have hh:=firstTier_le s law σ hσ t hr.le; omega⟩
  have hq:tierQualifies s law r σ i t:=firstTier_qualifies s law σ hσ t hr.le
  have hi (a:Tape Y k H r):keys s law hr.le σ a (t.val+1) (some i) (σ t)≠none:=by
    obtain ⟨b,hb⟩:=TierKeys.guaranteed_coverage (request s σ) hr
      (lt_of_lt_of_le (by omega : 0 < 2) (tierK_ge_two (height_ge i)))
      (tierQualifies s law r σ i) t t.isLt hq (a.2 i).1 (a.2 i).2
    change TierKeys.key (request s σ) hr.le (tierK (height i)) (tierQualifies s law r σ i)
      (a.2 i).1 (a.2 i).2 (t.val+1) (σ t)≠none
    rw [request_fin] at hb
    rw [hb]
    exact Option.some_ne_none _
  have hb:=prefix_bound s law hr σ (t.val+1) (σ t) y hxy i hi
  have hL:=logratio_bounds s law σ hσ t hr.le
  have hsum: (∑ j∈range (i.val+1),(2:ℝ)^j) ≤ 4*(1+logratio s law σ t r):=
    TierDyadic.qualified_sum hL.1
  have hmul:=mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 262*dist (σ t) y/r)
  have hc:dist (σ t) y/(4*r) ≤ 2*(1+logratio s law σ t r)*dist (σ t) y/r:=by
    apply (div_le_div_iff₀ (by positivity : 0 < 4*r) hr).mpr
    have hd:=mul_nonneg hL.1 (dist_nonneg (x:=σ t) (y:=y))
    have hdr:=mul_nonneg hd hr.le
    nlinarith [mul_nonneg (dist_nonneg (x:=σ t) (y:=y)) hr.le]
  calc _ ≤ dist (σ t) y/(4*r)+(262*dist (σ t) y/r)*(∑ j∈range (i.val+1),(2:ℝ)^j) := hb
       _ ≤ 2*(1+logratio s law σ t r)*dist (σ t) y/r+(262*dist (σ t) y/r)*(4*(1+logratio s law σ t r)) := add_le_add hc hmul
       _ = _ := by ring

lemma map_eq_of_heavy (s:Configuration k Y) (law:RequestLaw Y H)
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (t:Fin H) (y:Y) (hxy:4*dist (σ t) y < r)
    (hh:mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (51200*r)) ≤
      (1+heavyDelta)*mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (heavyGamma*r)))
    (a:Tape Y k H r) : map s law hr.le σ a (t.val+1) (σ t)=map s law hr.le σ a (t.val+1) y := by
  obtain ⟨b,hb,hby⟩:=heavy_agrees s law σ t hr hh a.1 y hxy
  by_contra hn
  obtain ⟨j,hj,hd⟩:=PriorityKeys.key_ne_prefix (keys s law hr.le σ a (t.val+1)) (σ t) y none
    (by change HeavyKeys.key s law r heavyGamma heavyDelta σ a.1 (t.val+1) (σ t)≠none
        rw [hb]; exact Option.some_ne_none _) hn
  have he:j=none:=bot_unique hj
  subst j
  exact hd (hb.trans hby.symm)

lemma heavy_zero (s:Configuration k Y) (law:RequestLaw Y H)
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (t:Fin H) (y:Y) (hxy:4*dist (σ t) y < r)
    (hh:mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (51200*r)) ≤
      (1+heavyDelta)*mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (heavyGamma*r))) :
    separation s law hr.le σ (t.val+1) (σ t) y=0 := by
  apply sum_eq_zero
  intro a _
  exact ite_eq_right (not_not.mpr (map_eq_of_heavy s law hr σ t y hxy hh a))

/-- The complete-level estimate (final-map-separation), with an explicit
absolute factor and no number-of-scales or largest-tier multiplier. -/
lemma spatial_sum (s:Configuration k Y) (law:RequestLaw Y H)
    (σ:Fin H→Y) (hσ:0 < law.val σ) (t:Fin H) (y:Y)
    {r₀ τ:ℝ} (hr:0 < r₀) (hτ:2 ≤ τ) (n:ℕ) :
    (∑ j∈range n, Pilot.radius r₀ τ j *
      separation s law (Pilot.radius_pos hr (by linarith) j).le σ (t.val+1) (σ t) y) ≤
      (8+1050*(60/Real.log (1+heavyDelta)+60)*Real.log k)*dist (σ t) y := by
  let R:=Pilot.radius r₀ τ
  let L (j:ℕ):=logratio s law σ t (R j)
  let N (j:ℕ):ℝ:=if Pilot.mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (51200*R j)) ≤
    (1+heavyDelta)*Pilot.mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (heavyGamma*R j)) then 0 else 1
  have hR (j:ℕ):0 < R j:=Pilot.radius_pos hr (by linarith) j
  have hL (j:ℕ):0 ≤ L j:=(logratio_bounds s law σ hσ t (hR j).le).1
  have hN (j:ℕ):0 ≤ N j:=by dsimp [N]; split_ifs <;> norm_num
  have hpoint (j:ℕ):R j*separation s law (hR j).le σ (t.val+1) (σ t) y ≤
      (if R j ≤ 4*dist (σ t) y then R j else 0)+1050*dist (σ t) y*(N j+L j):=by
    by_cases hsmall:R j ≤ 4*dist (σ t) y
    · rw [ite_eq_left hsmall]
      have hs:=mul_le_mul_of_nonneg_left (separation_le_one s law (hR j) σ (t.val+1) (σ t) y) (hR j).le
      have hmore:0 ≤ 1050*dist (σ t) y*(N j+L j):=mul_nonneg (by positivity) (add_nonneg (hN j) (hL j))
      linarith
    · rw [ite_eq_right hsmall]
      have hbig:4*dist (σ t) y < R j:=lt_of_not_ge hsmall
      dsimp only [N]
      split_ifs with hh
      · rw [heavy_zero s law (hR j) σ t y hbig hh,mul_zero,zero_add,zero_add]
        exact mul_nonneg (by positivity) (hL j)
      · have hs:=request_bound s law (hR j) σ hσ t y hbig
        have hm:=mul_le_mul_of_nonneg_left hs (hR j).le
        have he:R j*(1050*(1+L j)*dist (σ t) y/R j)=1050*dist (σ t) y*(1+L j):=by field_simp [(hR j).ne']
        change R j*separation s law (hR j).le σ (t.val+1) (σ t) y ≤ R j*(1050*(1+L j)*dist (σ t) y/R j) at hm
        simpa only [he,zero_add] using hm
  have hsum:=sum_le_sum (fun j (_:j∈range n)=>hpoint j)
  rw [sum_add_distrib,←mul_sum,sum_add_distrib] at hsum
  have hsmall:=Pilot.radius_truncated_sum hr.le hτ (by positivity : 0 ≤ 4*dist (σ t) y) n
  have hlogs:=LevelScale.actual_logratio_sum s law σ hσ t hr.le hτ n
  have hcount:=LevelScale.actual_nonheavy_count s law σ hσ t hr.le hτ n
  have hlarge:=mul_le_mul_of_nonneg_left (add_le_add hcount hlogs)
    (by positivity : 0 ≤ 1050*dist (σ t) y)
  have htotal:=hsum.trans (add_le_add hsmall hlarge)
  convert htotal using 1 <;> first | rfl | ring
end KServer.LevelSpatial

end


/-! Physical movement of the tier noncoverage potential on steps without an
insertion.  Unqualified dyadic heights sum against the local log ratio. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LevelNoInsert
open ActualRoster LevelKeys LevelCoverage LevelLaw LevelTierEdits LevelRetirement FiniteExperiment TierProcess Pilot
attribute [local instance] Classical.propDecidable Classical.decEq

lemma filtered_powers {L:ℝ} (hL:0 ≤ L) (n:ℕ) :
    (∑ i∈range n,if (2:ℝ)^i<L then (2:ℝ)^i else 0) ≤ 2*L := by
  induction n with
  | zero => simp only [range_zero,sum_empty]; linarith
  | succ n ih =>
    by_cases hn:(2:ℝ)^n<L
    · have he : (∑ i∈range (n+1),if (2:ℝ)^i<L then (2:ℝ)^i else 0)=
          ∑ i∈range (n+1),(2:ℝ)^i := by
        apply sum_congr rfl
        intro i hi
        exact ite_eq_left ((pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2)
          (by have hh:=mem_range.mp hi; omega)).trans_lt hn)
      rw [he,TierDyadic.tier_sum]
      linarith
    · rw [sum_range_succ,ite_eq_right hn,add_zero]
      exact ih

lemma tier_count (k:ℕ) : (Fintype.card (Tier k):ℝ) ≤ 4*(1+Real.log k) := by
  by_cases hk:k=0
  · subst k
    norm_num [Tier,TierDyadic.index_zero (show (0:ℝ) ≤ 1 by norm_num)]
  have hl:0 ≤ Real.log k:=Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk)
  have hp:=TierDyadic.qualified_sum hl
  have hi : (Fintype.card (Tier k):ℝ) ≤ ∑ i∈range (TierDyadic.index (Real.log k)+1),(2:ℝ)^i := by
    calc _ = ∑ i∈range (TierDyadic.index (Real.log k)+1),(1:ℝ) := by simp [Tier]
         _ ≤ _ := sum_le_sum (fun i _=>one_le_pow₀ (by norm_num))
  exact hi.trans hp

variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

attribute [local instance] OAI.KServer.LevelNoInsert.finDecEq
lemma unqualified_height_sum (s:Configuration k Y) (law:RequestLaw Y H)
    {r:ℝ} (hr:0 ≤ r) (σ:Fin H→Y) (hs:0 < law.val σ) (t:Fin H) :
    (∑ i:Tier k,if tierQualifies s law r σ i t then 0 else height i) ≤
      2*logratio s law σ t r := by
  trans ∑ i:Tier k,if height i<logratio s law σ t r then height i else 0
  · apply sum_le_sum
    intro i _
    by_cases hq:tierQualifies s law r σ i t
    · rw [ite_eq_left hq]; split_ifs
      · exact (show (0:ℝ) ≤ 1 by norm_num).trans (height_ge i)
      · rfl
    · have hi:height i<logratio s law σ t r:=lt_of_not_ge (fun hn=>hq (qualifies_of_log s law σ hs t hr hn))
      rw [ite_eq_right hq,ite_eq_left hi]
  · unfold height
    have he:=Fin.sum_univ_eq_sum_range (fun j:ℕ=>if (2:ℝ)^j<logratio s law σ t r then (2:ℝ)^j else 0) (TierDyadic.index (Real.log k)+1)
    rw [he]
    exact filtered_powers (logratio_bounds s law σ hs t hr).1 _

lemma error_le_one (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (t:Fin H) (i:Tier k) (p:Y) : error s law hr.le σ t i p ≤ 1 := by
  unfold error
  split_ifs with hin
  · norm_num
  · have hb:=mean_mono hr (fun a=>no_insert_mover s law hr σ a t i p hin)
    refine hb.trans ((mean_mono hr (fun a=>?_)).trans_eq (mean_const hr 1))
    split_ifs
    · norm_num
    · unfold indicator; split_ifs <;> norm_num

lemma error_spatial (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (t:Fin H) (i:Tier k) (p:Y) (hp:dist (σ t) p ≤ r) :
    error s law hr.le σ t i p ≤
      (262*dist (σ t) p/r)*(if tierQualifies s law r σ i t then 0 else height i) := by
  have hnon:0 ≤ 262*dist (σ t) p/r:=by positivity
  unfold error
  by_cases hin:inserted s law r σ t i
  · rw [ite_eq_left hin]
    exact mul_nonneg hnon (by split_ifs <;> first | rfl | exact (height_ge i).trans' (by norm_num))
  · rw [ite_eq_right hin]
    have hb:=mean_mono hr (fun a=>no_insert_mover s law hr σ a t i p hin)
    by_cases hq:tierQualifies s law r σ i t
    · simp only [ite_eq_left hq,mul_zero,mean_const hr] at hb ⊢
      exact hb
    · simp only [ite_eq_right hq] at hb ⊢
      rw [mean_indicator] at hb
      have hc:=LevelLaw.tier_spatial s law hr σ (t.val+1) i (σ t) p hp
      have hh:=mul_le_mul_of_nonneg_right (TierDyadic.radius_coefficient (height_ge i))
        (div_nonneg (dist_nonneg (x:=σ t) (y:=p)) hr.le)
      dsimp only [keys] at hb hc
      have hbound : (∑ a:Tape Y k H r,if TierKeys.key (request s σ) hr.le (tierK (height i))
          (tierQualifies s law r σ i) (a.2 i).1 (a.2 i).2 (t.val+1) (σ t) ≠
          TierKeys.key (request s σ) hr.le (tierK (height i)) (tierQualifies s law r σ i)
            (a.2 i).1 (a.2 i).2 (t.val+1) p then weight r a else 0) ≤
          (262*dist (σ t) p/r)*height i := by
        refine hc.trans ?_
        convert mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 2) using 1 <;> ring
      apply hb.trans
      convert hbound using 1 <;> first | rfl | (apply sum_congr rfl; intro a _; congr 1)

lemma level_error (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (hs:0 < law.val σ) (t:Fin H) (p:Y) :
    r*(∑ i:Tier k,error s law hr.le σ t i p) ≤
      (if r ≤ 4*dist (σ t) p then (Fintype.card (Tier k):ℝ)*r else 0)+
        524*dist (σ t) p*logratio s law σ t r := by
  by_cases hp:r ≤ 4*dist (σ t) p
  · rw [ite_eq_left hp]
    have hb:=sum_le_sum (fun i (_:i∈univ)=>error_le_one s law hr σ t i p)
    simp only [sum_const,card_univ,nsmul_eq_mul,mul_one] at hb
    have hc:=mul_le_mul_of_nonneg_left hb hr.le
    have hn:=mul_nonneg (by positivity : 0 ≤ 524*dist (σ t) p) (logratio_bounds s law σ hs t hr.le).1
    nlinarith
  · rw [ite_eq_right hp,zero_add]
    have hdist:dist (σ t) p ≤ r:=by linarith [dist_nonneg (x:=σ t) (y:=p)]
    have hb:=sum_le_sum (fun i (_:i∈univ)=>error_spatial s law hr σ t i p hdist)
    rw [←mul_sum] at hb
    have hc:=hb.trans (mul_le_mul_of_nonneg_left (unqualified_height_sum s law hr.le σ hs t) (by positivity))
    have hd:=mul_le_mul_of_nonneg_left hc hr.le
    calc _ ≤ r*((262*dist (σ t) p/r)*(2*logratio s law σ t r)) := hd
         _ = _ := by field_simp [hr.ne']; ring

lemma scales_error (s:Configuration k Y) (law:RequestLaw Y H)
    (σ:Fin H→Y) (hs:0 < law.val σ) (t:Fin H) (p:Y)
    {r₀ τ:ℝ} (hr:0 < r₀) (hτ:2 ≤ τ) (n:ℕ) :
    (∑ j∈range n,Pilot.radius r₀ τ j *
      (∑ i:Tier k,error s law (Pilot.radius_pos hr (by linarith) j).le σ t i p)) ≤
      (32*(1+Real.log k)+31440*Real.log k)*dist (σ t) p := by
  have hb:=sum_le_sum (fun j (_:j∈range n)=>level_error s law (Pilot.radius_pos hr (by linarith) j) σ hs t p)
  rw [sum_add_distrib,←mul_sum] at hb
  have he:(∑ j∈range n,if Pilot.radius r₀ τ j ≤ 4*dist (σ t) p then
      (Fintype.card (Tier k):ℝ)*Pilot.radius r₀ τ j else 0)=
      (Fintype.card (Tier k):ℝ)*∑ j∈range n,if Pilot.radius r₀ τ j ≤ 4*dist (σ t) p then Pilot.radius r₀ τ j else 0 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [he] at hb
  have hsmall:=mul_le_mul_of_nonneg_left (Pilot.radius_truncated_sum hr.le hτ
    (by positivity : 0 ≤ 4*dist (σ t) p) n) (Nat.cast_nonneg (Fintype.card (Tier k)): (0:ℝ) ≤ _)
  have hlarge:=mul_le_mul_of_nonneg_left (LevelScale.actual_logratio_sum s law σ hs t hr.le hτ n)
    (by positivity : 0 ≤ 524*dist (σ t) p)
  have hcount:=mul_le_mul_of_nonneg_right (tier_count k) (by positivity : 0 ≤ 8*dist (σ t) p)
  have ht:=hb.trans (add_le_add hsmall hlarge)
  nlinarith
end KServer.LevelNoInsert

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_PartitionBudget
attribute [-instance] _root_.OAI.KServer.JointExperiment.levelTapeFintype _root_.OAI.KServer.LevelKeys.alphabetFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal conditional averaging for the hidden optimum's stationary members.
Only conditioning on the true request prefix is used; tape averages may be
performed first without conditioning on a surviving random roster. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HiddenAverages
open FiniteExperiment PosteriorRanks RankTracking
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

omit [MetricSpace Y] [NeZero k] in
lemma counting_integral (c:Configuration k Y) (f:Y→ℝ) :
    (∑ y,metricCount c y*f y)=∑ i,f (c i) := by
  classical
  simp only [metricCount,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp

lemma expected_before_test (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (t:Fin H) (f:(Fin H→Y)→Y→ℝ)
    (hf:∀ y,Adapted (requestHistory (t.val+1)) (fun σ=>f σ y)) :
    avg law.val (fun σ=>∑ y,muBefore s law t σ y*f σ y)=
      avg law.val (fun σ=>∑ i,f σ (hidden s σ t i)) := by
  rw [avg_sum]
  have he y : avg law.val (fun σ=>muBefore s law t σ y*f σ y)=
      avg law.val (fun σ=>metricCount (hidden s σ t) y*f σ y) := by
    simpa only [muBefore,mul_comm] using weighted_posterior law.property.1 (requestHistory (t.val+1))
      (fun σ=>metricCount (hidden s σ t) y) (fun σ=>f σ y) (hf y)
  simp_rw [he]
  rw [←avg_sum]
  congr 1
  funext σ
  exact counting_integral _ _

lemma expected_mover_test (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (t:Fin H) (f:(Fin H→Y)→Y→ℝ)
    (hf:∀ y,Adapted (requestHistory (t.val+1)) (fun σ=>f σ y)) :
    avg law.val (fun σ=>∑ y,nu s law t σ y*f σ y)=
      avg law.val (fun σ=>f σ (hidden s σ t (mover s σ t))) := by
  classical
  rw [avg_sum]
  have he y : avg law.val (fun σ=>nu s law t σ y*f σ y)=
      avg law.val (fun σ=>(if hidden s σ t (mover s σ t)=y then 1 else 0)*f σ y) := by
    simpa only [nu,mul_comm] using weighted_posterior law.property.1 (requestHistory (t.val+1))
      (fun σ=>if hidden s σ t (mover s σ t)=y then (1:ℝ) else 0) (fun σ=>f σ y) (hf y)
  simp_rw [he]
  rw [←avg_sum]
  congr 1
  funext σ
  simp

lemma stationary_le (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (t:Fin H) (σ:Fin H→Y) (hs:0<law.val σ) (y:Y) : stationary s law t σ y ≤ mu s law (t.val+1) σ y := by
  rw [mu_move s law t σ hs y]
  dsimp only [stationary]
  split_ifs <;> linarith

lemma expected_stationary_test (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (t:Fin H) (f:(Fin H→Y)→Y→ℝ)
    (hf:∀ y,Adapted (requestHistory (t.val+1)) (fun σ=>f σ y)) :
    avg law.val (fun σ=>∑ y,stationary s law t σ y*f σ y)=
      avg law.val (fun σ=>∑ i∈univ.erase (mover s σ t),f σ (hidden s σ t i)) := by
  classical
  simp only [stationary,sub_mul,sum_sub_distrib,avg_sub]
  rw [expected_before_test s law t f hf,expected_mover_test s law t f hf,←avg_sub]
  congr 1
  funext σ
  exact (sum_erase_eq_sub (mem_univ (mover s σ t))).symm

end KServer.HiddenAverages

end


/-! Literal tier edit potentials along the selected hidden optimum.
Retirement averages are over the complete independent tape, before request
prefix conditioning.  All quantities below refer to constructed keys. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TierTemporal
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw LevelTierEdits
open LevelRetirement HiddenAverages RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

omit [NeZero k] in
lemma mean_add (r:ℝ) (f g:Tape Y k H r→ℝ) :
    mean r (fun a=>f a+g a)=mean r f+mean r g := by simp [mean,mul_add,sum_add_distrib]
omit [NeZero k] in
lemma mean_sub (r:ℝ) (f g:Tape Y k H r→ℝ) :
    mean r (fun a=>f a-g a)=mean r f-mean r g := by simp [mean,mul_sub,sum_sub_distrib]
omit [NeZero k] in
lemma mean_sum (r:ℝ) {I:Type*} (S:Finset I) (f:I→Tape Y k H r→ℝ) :
    mean r (fun a=>∑ i∈S,f i a)=∑ i∈S,mean r (f i) := by
  simp only [mean,mul_sum]
  exact sum_comm

lemma mover_inner (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (i:Tier k) (p:Y)
    (hin:inserted s law r σ t i)
    (hh:mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (51200*r)) ≤
      (1+heavyDelta)*mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (heavyGamma*r)))
    (hp:dist (σ t) p≤heavyGamma*r) :
    LevelTierEdits.charge s law hr.le σ a t i p+uncovered s law hr.le σ a (t.val+1) i (σ t)-
      uncovered s law hr.le σ a t i p ≤ 0 := by
  rw [heavy_inner_charge s law hr σ a t i p hh hp,zero_add,
    covered_qualified s law hr σ a t i hin.1]
  exact sub_nonpos.mpr (ActualRoster.indicator_nonneg _)

lemma mover_mean_inner (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (t:Fin H) (i:Tier k) (p:Y) (hin:inserted s law r σ t i)
    (hh:mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (51200*r)) ≤
      (1+heavyDelta)*mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (heavyGamma*r))) :
    mean r (fun a=>LevelTierEdits.charge s law hr.le σ a t i p+
      uncovered s law hr.le σ a (t.val+1) i (σ t)-uncovered s law hr.le σ a t i p) ≤
        if heavyGamma*r<dist (σ t) p then 49/(tierK (height i):ℝ) else 0 := by
  split_ifs with hp
  · exact mover_mean s law hr σ t i p hin
  · exact (mean_mono hr (fun a=>mover_inner s law hr σ a t i p hin hh (le_of_not_gt hp))).trans_eq (mean_const hr 0)

omit [MetricSpace Y] [Fintype Y] [NeZero k] in
lemma dyadic_exp_sum (k:ℕ) : (∑ i:Tier k,Real.exp (-height i))≤1 := by
  have hc (i:ℕ) : (i:ℝ)+1≤(2:ℝ)^i := by
    induction i with
    | zero => norm_num
    | succ i ih =>
      rw [pow_succ,Nat.cast_add,Nat.cast_one]
      have hi : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
      nlinarith
  calc _ ≤ ∑ i:Tier k,Real.exp (-(i.val+1:ℝ)) := by
         apply sum_le_sum
         intro i _
         exact Real.exp_le_exp.mpr (neg_le_neg (hc i.val))
       _ ≤ _ := by
         have he:=Fin.sum_univ_eq_sum_range (fun n:ℕ=>Real.exp (-(n+1:ℝ))) (TierDyadic.index (Real.log k)+1)
         rw [he]
         exact tier_weight_sum _

omit [MetricSpace Y] [Fintype Y] [NeZero k] in
lemma dyadic_reciprocal_sum (k:ℕ) : (∑ i:Tier k,1/(tierK (height i):ℝ))≤1 := by
  refine (sum_le_sum (fun i (_:i∈univ)=>?_)).trans (dyadic_exp_sum k)
  have hi:=height_ge i
  have hb:=tier_reciprocal_absorb hi
  have he:Real.exp (-2*height i)≤Real.exp (-height i):=Real.exp_le_exp.mpr (by linarith)
  have ht:64*heavyDelta≤1:=by norm_num [heavyDelta]
  exact hb.trans ((mul_le_mul_of_nonneg_left he (by norm_num [heavyDelta])).trans
    (mul_le_of_le_one_left (Real.exp_nonneg _) ht))

lemma potential_bounds (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:ℕ) (i:Tier k) :
    potential s law hr σ a t i∈Set.Icc 0 (k:ℝ) := by
  constructor
  · exact sum_nonneg (fun l _=>ActualRoster.indicator_nonneg _)
  · unfold potential uncovered
    exact (sum_le_sum (fun l (_:l∈univ)=>ActualRoster.indicator_le_one _)).trans_eq (by simp)

attribute [local instance] OAI.KServer.TierTemporal.finDecEq
lemma potential_step (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (i:Tier k) :
    editCost s law hr σ a t i+potential s law hr σ a (t.val+1) i-potential s law hr σ a t i=
      (∑ l∈univ.erase (mover s σ t),(LevelTierEdits.charge s law hr σ a t i (hidden s σ t l)+
        uncovered s law hr σ a (t.val+1) i (hidden s σ t l)-uncovered s law hr σ a t i (hidden s σ t l)))+
      (LevelTierEdits.charge s law hr σ a t i (hidden s σ t (mover s σ t))+
        uncovered s law hr σ a (t.val+1) i (σ t)-uncovered s law hr σ a t i (hidden s σ t (mover s σ t))) := by
  have he:potential s law hr σ a (t.val+1) i=
    (∑ l∈univ.erase (mover s σ t),uncovered s law hr σ a (t.val+1) i (hidden s σ t l))+
      uncovered s law hr σ a (t.val+1) i (σ t) := by
    unfold potential
    rw [←sum_erase_add _ _ (mem_univ (mover s σ t)),hidden_covers]
    congr 1
    apply sum_congr rfl
    intro l hl
    congr 1
    have he:=congrFun (hidden_step s σ t) l
    simpa [serve,(mem_erase.mp hl).1] using he
  rw [he]
  unfold editCost potential
  have hC:=sum_erase_add univ (fun l:Fin k=>LevelTierEdits.charge s law hr σ a t i (hidden s σ t l)) (mem_univ (mover s σ t))
  have hU:=sum_erase_add univ (fun l:Fin k=>uncovered s law hr σ a t i (hidden s σ t l)) (mem_univ (mover s σ t))
  simp only [sum_sub_distrib,sum_add_distrib]
  linarith

end KServer.TierTemporal

end


/-! True-prefix payment of literal tier retirement errors by the posterior
insertion mass.  No conditioning on the realized random tape is used. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TierAverages
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw LevelTierEdits
open LevelRetirement HiddenAverages RankTracking PosteriorRanks TierTemporal ActualRoster
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

lemma test_nonneg (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:Fin H) (i:Tier k) (p:Y) :
    0≤test s law r σ t i p := by unfold test; split_ifs; exact indicator_nonneg _; rfl

lemma inserted_adapted (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (t:Fin H) (i:Tier k)
    (σ ρ:Fin H→Y) (hh:requestHistory (t.val+1) σ=requestHistory (t.val+1) ρ) :
    inserted s law r σ t i ↔ inserted s law r ρ t i := by
  have hm (ω:Fin H→Y) : inserted s law r ω t i ↔
    (t:ℕ)∈roster s law tierTemplate r tierGamma (height i) (tierK (height i)) ω (t.val+1) := by
    rw [roster,Chronological.schedule_mem]
    exact (and_iff_right (Nat.lt_succ_self t.val)).symm
  rw [hm,hm,roster_adapted s law tierTemplate r tierGamma (height i) (tierK (height i)) (t.val+1) σ ρ hh]

lemma test_adapted (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (t:Fin H) (i:Tier k) (p:Y) :
    Adapted (requestHistory (t.val+1)) (fun σ=>test s law r σ t i p) := by
  intro σ ρ hh
  have hm:mu s law (t.val+1) σ=mu s law (t.val+1) ρ:=funext (fun y=>mu_adapted s law (t.val+1) y σ ρ hh)
  simp only [test,region,inserted_adapted s law r t i σ ρ hh,hm,request_of_history t σ ρ hh]

lemma retirement_region (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (t:Fin H) (p:Y)
    (hp:dist (σ t) p≤22*r)
    (hh:¬(mass (mu s law (t.val+1) σ) (ball (σ t) (51200*r))≤
      (1+heavyDelta)*mass (mu s law (t.val+1) σ) (ball (σ t) (heavyGamma*r)) ∧ dist (σ t) p≤heavyGamma*r)) :
    p∈region s law r σ t := by
  unfold region tierRegion
  split_ifs with h
  · refine mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,by nlinarith⟩,?_⟩
    intro hm
    exact hh ⟨h,(mem_filter.mp hm).2⟩
  · apply mem_filter.mpr ⟨mem_univ _,?_⟩
    norm_num [tierTemplate]
    nlinarith

lemma stationary_test_bound (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (t:Fin H) (i:Tier k) (p:Y) :
    mean r (fun a=>LevelTierEdits.charge s law hr.le σ a t i p+
      uncovered s law hr.le σ a (t.val+1) i p-uncovered s law hr.le σ a t i p) ≤
      (98/(tierK (height i):ℝ))*test s law r σ t i p := by
  by_cases hin:inserted s law r σ t i
  · have hb:=stationary_mean s law hr σ t i p hin
    refine hb.trans ?_
    rw [test,ite_eq_left hin]
    split_ifs with he
    · rw [indicator,ite_eq_left (retirement_region s law hr σ t p he.1 he.2),mul_one]
    · exact mul_nonneg (by positivity) (indicator_nonneg _)
  · rw [test,ite_eq_right hin,mul_zero]
    have he (a:Tape Y k H r):LevelTierEdits.charge s law hr.le σ a t i p+
      uncovered s law hr.le σ a (t.val+1) i p-uncovered s law hr.le σ a t i p=0:=
        no_insert_stationary s law hr.le σ a t i p hin
    simp only [he,mean_const hr,le_refl]

lemma test_mass (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:Fin H) (i:Tier k) :
    (∑ y,mu s law (t.val+1) σ y*test s law r σ t i y)=
      if inserted s law r σ t i then mass (mu s law (t.val+1) σ) (region s law r σ t) else 0 := by
  unfold test
  split_ifs with h
  · simp only [indicator,mul_ite,mul_one,mul_zero]
    rw [←sum_filter]
    congr 1
    ext y
    simp
  · simp

lemma expected_stationary_bound (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (t:Fin H) (i:Tier k) :
    avg law.val (fun σ=>∑ l∈univ.erase (mover s σ t),test s law r σ t i (hidden s σ t l)) ≤
      avg law.val (fun σ=>if inserted s law r σ t i then mass (mu s law (t.val+1) σ) (region s law r σ t) else 0) := by
  rw [←expected_stationary_test s law t (fun σ p=>test s law r σ t i p) (test_adapted s law r t i)]
  trans avg law.val (fun σ=>∑ y,mu s law (t.val+1) σ y*test s law r σ t i y)
  · apply sum_le_sum
    intro σ _
    by_cases hs:0<law.val σ
    · apply mul_le_mul_of_nonneg_left _ hs.le
      apply sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_right (stationary_le s law t σ hs y) (test_nonneg s law r σ t i y)
    · have hz:law.val σ=0:=le_antisymm (le_of_not_gt hs) (law.property.1 σ)
      simp only [hz,zero_mul,le_refl]
  · apply le_of_eq
    congr 1
    funext σ
    exact test_mass s law r σ t i

lemma nonheavy_mass (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (hs:0<law.val σ) (t:Fin H)
    (hh:¬ mass (mu s law (t.val+1) σ) (ball (σ t) (51200*r))≤
      (1+heavyDelta)*mass (mu s law (t.val+1) σ) (ball (σ t) (heavyGamma*r))) :
      1 ≤ mass (mu s law (t.val+1) σ) (region s law r σ t) := by
  unfold region tierRegion
  rw [ite_eq_right hh]
  have hm:σ t∈ball (σ t) (100*tierTemplate.R*r):=by
    simp only [ball,mem_filter,mem_univ,true_and,dist_self]
    norm_num [tierTemplate]
    positivity
  exact (mu_served s law t σ hs).trans (single_le_sum (fun y _=>mu_nonneg s law (t.val+1) σ y) hm)

end KServer.TierAverages

end


/-! Literal one-step tier cost + potential accounting at the true observation
filtration. The insertion term is the existing geometric pilot charge. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TierBudget
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw LevelTierEdits
open LevelRetirement HiddenAverages RankTracking PosteriorRanks TierTemporal TierAverages ActualRoster
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

lemma paidMass_nonneg (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:Fin H) (i:Tier k) :
    0≤paidMass s law r σ t i := by
  unfold paidMass
  split_ifs
  · exact mass_nonneg (mu_nonneg s law (t.val+1) σ) _
  · rfl

lemma paidMass_charge (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:Fin H) (i:Tier k) :
    r*paidMass s law r σ t i=TierProcess.charge s law tierTemplate r heavyGamma tierGamma heavyDelta
      (height i) (tierK (height i)) t σ := by
  unfold paidMass TierProcess.charge
  change r*(if inserted s law r σ t i then _ else 0)=(if inserted s law r σ t i then _ else 0)
  split_ifs <;> first | rfl | simp

lemma mover_bound (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (hs:0<law.val σ) (t:Fin H) (i:Tier k) (p:Y) :
    mean r (fun a=>LevelTierEdits.charge s law hr.le σ a t i p+
      uncovered s law hr.le σ a (t.val+1) i (σ t)-uncovered s law hr.le σ a t i p) ≤
      (49/(tierK (height i):ℝ))*paidMass s law r σ t i+
      (49/(tierK (height i):ℝ))*indicator (heavyGamma*r<dist (σ t) p)+
      LevelNoInsert.error s law hr.le σ t i p := by
  have hC:(0:ℝ)≤49/(tierK (height i):ℝ):=by positivity
  have hP:=mul_nonneg hC (paidMass_nonneg s law r σ t i)
  have hD:=mul_nonneg hC (indicator_nonneg (heavyGamma*r<dist (σ t) p))
  by_cases hin:inserted s law r σ t i
  · rw [LevelNoInsert.error,ite_eq_left hin,add_zero]
    by_cases hh:mass (mu s law (t.val+1) σ) (ball (σ t) (51200*r))≤
        (1+heavyDelta)*mass (mu s law (t.val+1) σ) (ball (σ t) (heavyGamma*r))
    · have hb:=mover_mean_inner s law hr σ t i p hin hh
      have he:(if heavyGamma*r<dist (σ t) p then 49/(tierK (height i):ℝ) else 0)=
          (49/(tierK (height i):ℝ))*indicator (heavyGamma*r<dist (σ t) p):=by
        unfold indicator
        split_ifs <;> ring
      rw [he] at hb
      linarith
    · have hm:=nonheavy_mass s law hr σ hs t hh
      have hp:1≤paidMass s law r σ t i:=by rw [paidMass,ite_eq_left hin]; exact hm
      have hb:=mover_mean s law hr σ t i p hin
      have hm:=mul_le_mul_of_nonneg_left hp hC
      linarith
  · rw [LevelNoInsert.error,ite_eq_right hin]
    linarith

lemma average_step (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (t:Fin H) (i:Tier k) :
    avg law.val (fun σ=>mean r (fun a=>editCost s law hr.le σ a t i+
      TierTemporal.potential s law hr.le σ a (t.val+1) i-TierTemporal.potential s law hr.le σ a t i)) ≤
      (147/(tierK (height i):ℝ))*avg law.val (fun σ=>paidMass s law r σ t i)+
      (49/(tierK (height i):ℝ))*avg law.val (fun σ=>indicator (heavyGamma*r<dist (σ t) (hidden s σ t (mover s σ t))))+
      avg law.val (fun σ=>LevelNoInsert.error s law hr.le σ t i (hidden s σ t (mover s σ t))) := by
  let stationaryTerm:=fun σ=>∑ l∈univ.erase (mover s σ t),test s law r σ t i (hidden s σ t l)
  have hpoint (σ:Fin H→Y) (hs:0<law.val σ):
      mean r (fun a=>editCost s law hr.le σ a t i+TierTemporal.potential s law hr.le σ a (t.val+1) i-
        TierTemporal.potential s law hr.le σ a t i) ≤
      (98/(tierK (height i):ℝ))*stationaryTerm σ+
        ((49/(tierK (height i):ℝ))*paidMass s law r σ t i+
        (49/(tierK (height i):ℝ))*indicator (heavyGamma*r<dist (σ t) (hidden s σ t (mover s σ t)))+
        LevelNoInsert.error s law hr.le σ t i (hidden s σ t (mover s σ t))) := by
    simp_rw [potential_step,mean_add,mean_sum]
    apply add_le_add _ (mover_bound s law hr σ hs t i _)
    have hd:TierTemporal.finDecEq k=instDecidableEqFin k:=Subsingleton.elim _ _
    rw [hd]
    exact (sum_le_sum (fun l (_:l∈univ.erase (mover s σ t))=>
      stationary_test_bound s law hr σ t i (hidden s σ t l))).trans_eq (mul_sum _ _ _).symm
  have hb:avg law.val (fun σ=>mean r (fun a=>editCost s law hr.le σ a t i+
      TierTemporal.potential s law hr.le σ a (t.val+1) i-TierTemporal.potential s law hr.le σ a t i)) ≤
        avg law.val (fun σ=>(98/(tierK (height i):ℝ))*stationaryTerm σ+
        ((49/(tierK (height i):ℝ))*paidMass s law r σ t i+
        (49/(tierK (height i):ℝ))*indicator (heavyGamma*r<dist (σ t) (hidden s σ t (mover s σ t)))+
        LevelNoInsert.error s law hr.le σ t i (hidden s σ t (mover s σ t)))) := by
    apply sum_le_sum
    intro σ _
    by_cases hs:0<law.val σ
    · exact mul_le_mul_of_nonneg_left (hpoint σ hs) hs.le
    · have hz:law.val σ=0:=le_antisymm (le_of_not_gt hs) (law.property.1 σ)
      simp only [hz,zero_mul,le_refl]
  simp only [avg_add,avg_mul] at hb
  have hs:=mul_le_mul_of_nonneg_left (expected_stationary_bound s law r t i)
    (show (0:ℝ)≤98/(tierK (height i):ℝ) by positivity)
  change (98/(tierK (height i):ℝ))*avg law.val stationaryTerm ≤
    (98/(tierK (height i):ℝ))*avg law.val (fun σ=>paidMass s law r σ t i) at hs
  have hc:(147/(tierK (height i):ℝ))=98/(tierK (height i):ℝ)+49/(tierK (height i):ℝ):=by ring
  rw [hc,add_mul]
  linarith only [hb,hs]

end KServer.TierBudget

end


/-! Horizon-independent endpoint bound for the actual dyadic-tier edits. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TierGlobal
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw LevelTierEdits
open LevelRetirement HiddenAverages RankTracking PosteriorRanks TierTemporal TierAverages ActualRoster TierBudget
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

omit [MetricSpace Y] [Fintype Y] [NeZero k] in
lemma telescope_budget (p:ℕ→ℝ) (c b:Fin H→ℝ)
    (hs:∀ t,c t+p (t.val+1)-p t≤b t) (hF:0≤p H) :
    (∑ t,c t) ≤ ∑ t,b t+p 0 := by
  have hd:(∑ t:Fin H,(p (t.val+1)-p t))=p H-p 0 := by
    calc _ = ∑ t∈range H,(p (t+1)-p t) := Fin.sum_univ_eq_sum_range (fun t:ℕ=>p (t+1)-p t) H
         _ = _ := sum_range_sub p H
  have he:=sum_le_sum (fun t (_:t∈univ)=>hs t)
  have heq:(∑ t:Fin H,(c t+p (t.val+1)-p t))=(∑ t,c t)+(p H-p 0):=by
    simp_rw [show ∀ t:Fin H,c t+p (t.val+1)-p t=c t+(p (t.val+1)-p t) by intro t; ring]
    rw [sum_add_distrib,hd]
  rw [heq] at he
  linarith

lemma potential_mean_bounds (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (t:ℕ) (i:Tier k) :
    avg law.val (fun σ=>mean r (fun a=>TierTemporal.potential s law hr.le σ a t i))∈Set.Icc 0 (k:ℝ) := by
  constructor
  · calc 0 = avg law.val (fun _=>mean (Y:=Y) (k:=k) (H:=H) r (fun _=>0)) := by
           rw [mean_const hr,avg_const _ law.property.2]
         _ ≤ _ := avg_mono law.property.1 (fun σ=>mean_mono hr
           (fun a=>(_root_.OAI.KServer.TierTemporal.potential_bounds s law hr.le σ a t i).1))
  · calc _ ≤ avg law.val (fun _=>mean (Y:=Y) (k:=k) (H:=H) r (fun _=>(k:ℝ))) :=
           avg_mono law.property.1 (fun σ=>mean_mono hr
             (fun a=>(_root_.OAI.KServer.TierTemporal.potential_bounds s law hr.le σ a t i).2))
         _ = _ := by rw [mean_const hr,avg_const _ law.property.2]

lemma tier_budget (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r) (i:Tier k) :
    (∑ t:Fin H,avg law.val (fun σ=>mean r (fun a=>editCost s law hr.le σ a t i))) ≤
      (147/(tierK (height i):ℝ))*(∑ t:Fin H,avg law.val (fun σ=>paidMass s law r σ t i))+
      (49/(tierK (height i):ℝ))*(∑ t:Fin H,avg law.val (fun σ=>indicator
        (heavyGamma*r<dist (σ t) (hidden s σ t (mover s σ t)))))+
      (∑ t:Fin H,avg law.val (fun σ=>LevelNoInsert.error s law hr.le σ t i (hidden s σ t (mover s σ t))))+k := by
  have hs:=fun t:Fin H=>average_step s law hr t i
  simp only [mean_sub,mean_add,avg_sub,avg_add] at hs
  have hb:=telescope_budget (fun t=>avg law.val (fun σ=>mean r
    (fun a=>TierTemporal.potential s law hr.le σ a t i))) _ _ hs
    (potential_mean_bounds s law hr H i).1
  simp only [sum_add_distrib,←mul_sum] at hb
  exact hb.trans (add_le_add le_rfl (potential_mean_bounds s law hr 0 i).2)

omit [Fintype Y] in
lemma actual_move_cost (s:Configuration k Y) (σ:Fin H→Y) :
    (∑ t:Fin H,dist (σ t) (hidden s σ t (mover s σ t)))=optimalCost s (List.ofFn σ) := by
  simp_rw [dist_comm (σ _),←hidden_movement]
  exact hidden_total_cost s σ

lemma far_scales {r₀ τ d:ℝ} (hr:0 < r₀) (hτ:2≤τ) (hd:0≤d) (n:ℕ) :
    (∑ j∈range n,radius r₀ τ j*indicator (heavyGamma*radius r₀ τ j<d)) ≤ 2*d/heavyGamma := by
  have hg:(0:ℝ)<heavyGamma:=by norm_num [heavyGamma]
  have hb:=radius_truncated_sum hr.le hτ (div_nonneg hd hg.le) n
  have he:2*(d/heavyGamma)=2*d/heavyGamma:=by ring
  refine (sum_le_sum (fun j (_:j∈range n)=>?_)).trans (hb.trans_eq he)
  by_cases hj:heavyGamma*radius r₀ τ j<d
  · have hle:radius r₀ τ j≤d/heavyGamma:=(le_div_iff₀ hg).mpr (by linarith)
    simp only [indicator,ite_eq_left hj,mul_one,ite_eq_left hle,le_refl]
  · simp only [indicator,ite_eq_right hj,mul_zero]
    split_ifs
    · exact (radius_pos hr (by linarith) j).le
    · rfl

end KServer.TierGlobal

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TierScaleBudget
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw LevelTierEdits
open LevelRetirement HiddenAverages RankTracking PosteriorRanks TierTemporal TierAverages ActualRoster TierBudget TierGlobal
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

omit [MetricSpace Y] [Fintype Y] [NeZero k] in
lemma avg_finset_sum {Ω I:Type*} [Fintype Ω] (w:Ω→ℝ) (S:Finset I) (f:I→Ω→ℝ) :
    avg w (fun ω=>∑ i∈S,f i ω)=∑ i∈S,avg w (f i) := by
  simp only [avg,mul_sum]
  exact sum_comm

omit [MetricSpace Y] [Fintype Y] [NeZero k] in
lemma factor_sum {I:Type*} [Fintype I] (f:I→ℝ) (c M:ℝ) :
    c*(∑ i,f i)*M=∑ i,c*f i*M := by rw [mul_sum,sum_mul]

lemma insertion_budget (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0 < r₀) (hτ:2≤τ) (n:ℕ) (i:Tier k) :
    (∑ j∈range n,radius r₀ τ j*((147/(tierK (height i):ℝ))*
      (∑ t:Fin H,avg law.val (fun σ=>paidMass s law (radius r₀ τ j) σ t i)))) ≤
      147*Real.exp (-height i)*(tierDrift*(1+Real.log ((k:ℝ)+1))*
        ∑ σ,law.val σ*optimalCost s (List.ofFn σ))+
      147*Real.exp (-height i)*(∑ j∈range n,2*radius r₀ τ j*(k:ℝ)) := by
  have hb:=weighted_insertion_budget s law n hr hτ (height_ge i)
  have he:(∑ j∈range n,radius r₀ τ j*((147/(tierK (height i):ℝ))*
      (∑ t:Fin H,avg law.val (fun σ=>paidMass s law (radius r₀ τ j) σ t i))))=
      147*(∑ t:Fin H,avg law.val (fun σ=>∑ j∈range n,
        TierProcess.charge s law tierTemplate (radius r₀ τ j) heavyGamma tierGamma heavyDelta
          (height i) (tierK (height i)) t σ/(tierK (height i):ℝ))) := by
    simp_rw [←paidMass_charge,div_eq_mul_inv,avg_finset_sum]
    rw [sum_comm]
    simp only [mul_sum,avg]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro t _
    apply sum_congr rfl
    intro σ _
    ring
  rw [he]
  exact (mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤147)).trans_eq (by ring)

lemma insertion_all (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0 < r₀) (hτ:2≤τ) (n:ℕ) :
    (∑ i:Tier k,∑ j∈range n,radius r₀ τ j*((147/(tierK (height i):ℝ))*
      (∑ t:Fin H,avg law.val (fun σ=>paidMass s law (radius r₀ τ j) σ t i)))) ≤
      147*(tierDrift*(1+Real.log ((k:ℝ)+1))*
        ∑ σ,law.val σ*optimalCost s (List.ofFn σ))+
      147*(∑ j∈range n,2*radius r₀ τ j*(k:ℝ)) := by
  let A:=tierDrift*(1+Real.log ((k:ℝ)+1))*(∑ σ,law.val σ*optimalCost s (List.ofFn σ))
  let B:=∑ j∈range n,2*radius r₀ τ j*(k:ℝ)
  have hn:0≤A:=by
    apply mul_nonneg
    · apply mul_nonneg
      · exact driftConstant_nonneg tierTemplate 60 (by norm_num [tierGamma]) (by norm_num [tierDelta])
      · have hl:0≤Real.log ((k:ℝ)+1):= Real.log_nonneg (by have hk:=Nat.cast_nonneg (α:=ℝ) k; linarith)
        linarith
    · exact sum_nonneg (fun σ _=>mul_nonneg (law.property.1 σ) (optimalCost_nonneg s (List.ofFn σ)))
  have he:0≤B:=sum_nonneg (fun j _=>by
    have hj:=(radius_pos (τ:=τ) hr (by linarith) j).le
    exact mul_nonneg (mul_nonneg (by norm_num) hj) (Nat.cast_nonneg k))
  calc _ ≤ ∑ i:Tier k,(147*Real.exp (-height i)*A+147*Real.exp (-height i)*B) :=
           sum_le_sum (fun i (_:i∈univ)=>insertion_budget s law hr hτ n i)
       _ = 147*(∑ i:Tier k,Real.exp (-height i))*(A+B) := by
           simp only [mul_add,mul_sum,sum_mul,sum_add_distrib]
       _ ≤ 147*1*(A+B) := mul_le_mul_of_nonneg_right
           (mul_le_mul_of_nonneg_left (dyadic_exp_sum k) (by norm_num)) (add_nonneg hn he)
       _ = _ := by ring

lemma far_all (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0 < r₀) (hτ:2≤τ) (n:ℕ) :
    (∑ i:Tier k,∑ j∈range n,radius r₀ τ j*((49/(tierK (height i):ℝ))*
      (∑ t:Fin H,avg law.val (fun σ=>indicator (heavyGamma*radius r₀ τ j<dist (σ t) (hidden s σ t (mover s σ t))))))) ≤
      (98/heavyGamma)*(∑ σ,law.val σ*optimalCost s (List.ofFn σ)) := by
  let M:ℝ:=∑ t:Fin H,avg law.val (fun σ=>∑ j∈range n,radius r₀ τ j*
    indicator (heavyGamma*radius r₀ τ j<dist (σ t) (hidden s σ t (mover s σ t))))
  have hM: M≤(2/heavyGamma)*(∑ σ,law.val σ*optimalCost s (List.ofFn σ)):=by
    have hb:=sum_le_sum (fun t (_:t∈univ)=>avg_mono law.property.1 (fun σ=>
      far_scales hr hτ (dist_nonneg (x:=σ t) (y:=hidden s σ t (mover s σ t))) n))
    have he:(∑ t:Fin H,avg law.val (fun σ=>2*dist (σ t) (hidden s σ t (mover s σ t))/heavyGamma))=
        (2/heavyGamma)*(∑ σ,law.val σ*optimalCost s (List.ofFn σ)):=by
      simp only [avg]
      rw [sum_comm,mul_sum]
      apply sum_congr rfl
      intro σ _
      rw [←actual_move_cost s σ]
      simp only [mul_sum]
      apply sum_congr rfl
      intro t _
      ring
    exact hb.trans_eq he
  have hn:0≤M:=by
    exact sum_nonneg (fun t _=>sum_nonneg (fun σ _=>mul_nonneg (law.property.1 σ)
      (sum_nonneg (fun j _=>mul_nonneg (radius_pos (τ:=τ) hr (by linarith) j).le (indicator_nonneg _)))))
  have he:(∑ i:Tier k,∑ j∈range n,radius r₀ τ j*((49/(tierK (height i):ℝ))*
      (∑ t:Fin H,avg law.val (fun σ=>indicator (heavyGamma*radius r₀ τ j<dist (σ t) (hidden s σ t (mover s σ t)))))))=
      49*(∑ i:Tier k,1/(tierK (height i):ℝ))*M := by
    rw [factor_sum]
    apply sum_congr rfl
    intro i _
    unfold M
    simp_rw [avg_finset_sum,avg_mul]
    rw [sum_comm]
    simp only [mul_sum]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro t _
    ring
  rw [he]
  have hsum:=mul_le_mul_of_nonneg_left (dyadic_reciprocal_sum k) (by positivity : (0:ℝ)≤49*M)
  have hbound:=mul_le_mul_of_nonneg_left hM (by norm_num : (0:ℝ)≤49)
  calc _ ≤ 49*M := by nlinarith only [hsum]
       _ ≤ _ := hbound.trans_eq (by ring)

lemma noinsert_all (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0 < r₀) (hτ:2≤τ) (n:ℕ) :
    (∑ i:Tier k,∑ j∈range n,radius r₀ τ j*(∑ t:Fin H,avg law.val (fun σ=>
      LevelNoInsert.error s law (radius_pos (τ:=τ) hr (by linarith) j).le σ t i
        (hidden s σ t (mover s σ t))))) ≤
      (32*(1+Real.log k)+31440*Real.log k)*(∑ σ,law.val σ*optimalCost s (List.ofFn σ)) := by
  have hb:=sum_le_sum (fun t (_:t∈univ)=>sum_le_sum (fun σ (_:σ∈univ)=>show
    law.val σ*(∑ j∈range n,radius r₀ τ j*(∑ i:Tier k,
      LevelNoInsert.error s law (radius_pos (τ:=τ) hr (by linarith) j).le σ t i
        (hidden s σ t (mover s σ t)))) ≤
    law.val σ*((32*(1+Real.log k)+31440*Real.log k)*
      dist (σ t) (hidden s σ t (mover s σ t))) from by
        by_cases hs:law.val σ=0
        · simp only [hs,zero_mul,le_refl]
        · exact mul_le_mul_of_nonneg_left (LevelNoInsert.scales_error s law σ
            (lt_of_le_of_ne (law.property.1 σ) (Ne.symm hs)) t _ hr hτ n) (law.property.1 σ)))
  have he:(∑ i:Tier k,∑ j∈range n,radius r₀ τ j*(∑ t:Fin H,avg law.val (fun σ=>
      LevelNoInsert.error s law (radius_pos (τ:=τ) hr (by linarith) j).le σ t i
        (hidden s σ t (mover s σ t)))))=
      ∑ t:Fin H,∑ σ,law.val σ*(∑ j∈range n,radius r₀ τ j*(∑ i:Tier k,
      LevelNoInsert.error s law (radius_pos (τ:=τ) hr (by linarith) j).le σ t i
        (hidden s σ t (mover s σ t)))) := by
    simp only [avg,mul_sum]
    calc _ = ∑ j∈range n,∑ t:Fin H,∑ σ,∑ i:Tier k,
        radius r₀ τ j*(law.val σ*LevelNoInsert.error s law
          (radius_pos (τ:=τ) hr (by linarith) j).le σ t i
          (hidden s σ t (mover s σ t))) := by
            rw [sum_comm]
            apply sum_congr rfl
            intro j _
            rw [sum_comm]
            apply sum_congr rfl
            intro t _
            rw [sum_comm]
         _ = _ := by
            rw [sum_comm]
            apply sum_congr rfl
            intro t _
            rw [sum_comm]
            apply sum_congr rfl
            intro σ _
            apply sum_congr rfl
            intro j _
            exact sum_congr rfl (fun i _=>by ring)
  rw [he]
  refine hb.trans_eq ?_
  rw [sum_comm,mul_sum]
  apply sum_congr rfl
  intro σ _
  rw [←actual_move_cost s σ]
  simp only [mul_sum]
  exact sum_congr rfl (fun t _=>by ring)

end KServer.TierScaleBudget

end


/-! Literal deterministic heavy-center schedule and its clipped distance profile,
§07 of the current manuscript. Random heavy radii do not affect this schedule. -/
noncomputable section
open scoped BigOperators
open Finset Set
namespace KServer.HeavyEdit

lemma ramp_bounds (u : ℝ) : ramp u ∈ Set.Icc 0 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩
lemma ramp_zero {u : ℝ} (hu : u ≤ 9) : ramp u=0 := by
  simp [ramp,max_eq_left (by linarith : u-9 ≤ 0)]
lemma ramp_one {u : ℝ} (hu : 10 ≤ u) : ramp u=1 := by
  exact min_eq_left ((by linarith : 1 ≤ u-9).trans (le_max_right _ _))
lemma ramp_lipschitz (u v : ℝ) : |ramp u-ramp v| ≤ |u-v| := by
  rw [abs_le]
  constructor <;> unfold ramp <;>
    simp only [min_def,max_def] <;> split_ifs <;>
    have h1 := le_abs_self (u-v) <;> have h2 := neg_le_abs (u-v) <;> linarith

attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y]

lemma profile_nonneg (r : ℝ) (C : Finset Y) (y : Y) : 0 ≤ profile r C y := by
  apply le_min'
  intro z hz
  rcases mem_insert.mp hz with rfl | hz
  · norm_num
  · obtain ⟨a,_,rfl⟩ := mem_image.mp hz
    exact (ramp_bounds _).1

lemma profile_le_one (r : ℝ) (C : Finset Y) (y : Y) : profile r C y ≤ 1 :=
  min'_le _ _ (mem_insert_self _ _)
lemma profile_le (r : ℝ) {C : Finset Y} {a : Y} (ha : a∈C) (y : Y) :
    profile r C y ≤ ramp (dist a y/r) :=
  min'_le _ _ (mem_insert_of_mem (mem_image.mpr ⟨a,ha,rfl⟩))
lemma le_profile (r : ℝ) (C : Finset Y) (y : Y) {u : ℝ} (hu : u ≤ 1)
    (h : ∀ a∈C,u ≤ ramp (dist a y/r)) : u ≤ profile r C y := by
  apply le_min'
  intro z hz
  rcases mem_insert.mp hz with rfl | hz
  · exact hu
  · obtain ⟨a,ha,rfl⟩ := mem_image.mp hz
    exact h a ha
lemma profile_eq_one {r : ℝ} (hr : 0 < r) {C : Finset Y} {y : Y}
    (h : ∀ a∈C,10*r ≤ dist a y) : profile r C y=1 := by
  apply le_antisymm (profile_le_one _ _ _)
  apply le_profile _ _ _ le_rfl
  intro a ha
  rw [ramp_one ((le_div_iff₀ hr).mpr (h a ha))]
lemma profile_eq_zero {r : ℝ} (hr : 0 < r) {C : Finset Y} {a y : Y}
    (ha : a∈C) (hay : dist a y ≤ 9*r) : profile r C y=0 := by
  apply le_antisymm _ (profile_nonneg _ _ _)
  exact (profile_le r ha y).trans_eq (ramp_zero ((div_le_iff₀ hr).mpr hay))

lemma profile_lipschitz {r : ℝ} (hr : 0 < r) (C : Finset Y) (y z : Y) :
    |profile r C y-profile r C z| ≤ dist y z/r := by
  have hdir (y z : Y) : profile r C y-profile r C z ≤ dist y z/r := by
    suffices profile r C y-dist y z/r ≤ profile r C z by linarith
    apply le_profile r C z
    · linarith [profile_le_one r C y,div_nonneg (dist_nonneg (x := y) (y := z)) hr.le]
    · intro a ha
      have hl := ramp_lipschitz (dist a y/r) (dist a z/r)
      have hm : |dist a y-dist a z| ≤ dist y z := by
        simpa only [dist_comm a] using abs_dist_sub_le y z a
      rw [←sub_div,abs_div,abs_of_pos hr] at hl
      have hb := hl.trans (div_le_div_of_nonneg_right hm hr.le)
      have hc := (le_abs_self (ramp (dist a y/r)-ramp (dist a z/r))).trans hb
      linarith [profile_le r ha y]
  rw [abs_sub_le_iff]
  exact ⟨hdir y z,by simpa only [dist_comm z y] using hdir z y⟩


open HeavyCenters HeavyLabels HeavyKeys

lemma profile_far {r:ℝ} (hr:0 < r) (C:Finset Y) {x p:Y}
    (hp:120*r<dist x p) : profile r (replace r C x) p=profile r C p := by
  apply le_antisymm
  · apply le_profile _ _ _ (profile_le_one _ _ _)
    intro a ha
    by_cases hax:100*r<dist a x
    · exact profile_le r (mem_insert_of_mem (mem_filter.mpr ⟨ha,hax⟩)) p
    · have ht:=dist_triangle x a p
      rw [dist_comm x a] at ht
      have hap:10*r≤dist a p:=by linarith
      rw [ramp_one ((le_div_iff₀ hr).mpr hap)]
      exact profile_le_one _ _ _
  · apply le_profile _ _ _ (profile_le_one _ _ _)
    intro a ha
    rcases mem_insert.mp ha with hax|ha
    · subst a
      rw [ramp_one ((le_div_iff₀ hr).mpr (by linarith))]
      exact profile_le_one _ _ _
    · exact profile_le r (mem_filter.mp ha).1 p

variable [Fintype Y]

omit [Fintype Y] in
lemma replace_separated {r:ℝ} {C:Finset Y} {x:Y}
    (hC:(C:Set Y).Pairwise (fun a b=>100*r<dist a b)) :
    (replace r C x:Set Y).Pairwise (fun a b=>100*r<dist a b) := by
  intro a ha b hb hn
  rcases mem_insert.mp ha with hax|ha
  · subst a
    have hb':=(mem_insert.mp hb).resolve_left (Ne.symm hn)
    simpa only [dist_comm] using (mem_filter.mp hb').2
  · rcases mem_insert.mp hb with hbx|hb
    · subst b; exact (mem_filter.mp ha).2
    · exact hC (mem_filter.mp ha).1 (mem_filter.mp hb).1 hn

omit [Fintype Y] in
lemma new_radius {r R:ℝ} (hr:0 < r) {C:Finset Y} {x:Y} {rad:Y→ℝ}
    (hrad:∀ a∈C,rad a≤20*r) (hR:R≤20*r) :
    ∀ a∈replace r C x,Function.update rad x R a≤20*r := by
  intro a ha
  rcases mem_insert.mp ha with hax|ha
  · subst a; simpa only [Function.update_self] using hR
  · have hn:a≠x:=by intro he; have h:=(mem_filter.mp ha).2; rw [he,dist_self] at h; linarith
    simpa only [Function.update_of_ne hn] using hrad a (mem_filter.mp ha).1

lemma inner_reuses {r R:ℝ} (hr:0 < r) {C D:Finset Y} {x p a:Y} {rad:Y→ℝ}
    {lab prev:Y→Pool Y} (hC:(C:Set Y).Pairwise (fun a b=>100*r<dist a b))
    (hrad:∀ a∈C,rad a∈Set.Icc (16*r) (20*r)) (hR:R∈Set.Icc (16*r) (20*r))
    (ha:a∈C) (hap:dist a p≤10*r) (hxp:dist x p≤3*r) :
    oldKey C rad lab p=newKey C D rad lab prev r x R p := by
  have haP:dist a p ≤ rad a:=by linarith [(hrad a ha).1]
  have hxP:dist x p≤R:=by linarith [hR.1]
  have ho:centerKey C rad p=some a:=
    (centerKey_some hr hC (fun a ha=>(hrad a ha).2)).mpr ⟨ha,haP⟩
  have hn:centerKey (replace r C x) (Function.update rad x R) p=some x:=
    (centerKey_some hr (replace_separated hC) (new_radius hr (fun a ha=>(hrad a ha).2) hR.2)).mpr
      ⟨mem_insert_self _ _,by simpa only [Function.update_self] using hxP⟩
  have hl:=inserted_reuses (D:=D) (label:=lab) (prev:=prev) hr hC
    (fun a ha=>(hrad a ha).2) hR.2 (mem_filter.mpr ⟨ha,⟨p,haP,hxP⟩⟩)
  simp only [oldKey,newKey,ho,hn,Option.map_some,updatedLabel,Function.update_self,hl]

lemma keys_far {r R:ℝ} (hr:0 < r) {C D:Finset Y} {x p:Y} {rad:Y→ℝ}
    {lab prev:Y→Pool Y} (hC:(C:Set Y).Pairwise (fun a b=>100*r<dist a b))
    (hrad:∀ a∈C,rad a≤20*r) (hR:R≤20*r) (hp:120*r<dist x p) :
    oldKey C rad lab p=newKey C D rad lab prev r x R p := by
  have hnc:¬dist x p≤R:=by linarith
  cases he:centerKey C rad p with
  | none =>
    have hn:centerKey (replace r C x) (Function.update rad x R) p=none:=by
      apply (centerKey_none _ _ _).mpr
      intro a ha
      rcases mem_insert.mp ha with hax|ha
      · subst a; simpa only [Function.update_self] using lt_of_not_ge hnc
      · have hax:a≠x:=by intro hh; have h:=(mem_filter.mp ha).2; rw [hh,dist_self] at h; linarith
        rw [Function.update_of_ne hax]
        exact (centerKey_none C rad p).mp he a (mem_filter.mp ha).1
    simp only [oldKey,newKey,he,hn,Option.map_none]
  | some a =>
    obtain ⟨ha,hap⟩:=(centerKey_some hr hC hrad).mp he
    have ht:=dist_triangle x a p
    rw [dist_comm x a] at ht
    have hax:100*r<dist a x:=by linarith [hrad a ha]
    have han:a≠x:=by intro hh; rw [hh,dist_self] at hax; linarith
    have hn:centerKey (replace r C x) (Function.update rad x R) p=some a:=by
      apply (centerKey_some hr (replace_separated hC) (new_radius hr hrad hR)).mpr
      exact ⟨mem_insert_of_mem (mem_filter.mpr ⟨ha,hax⟩),by simpa only [Function.update_of_ne han] using hap⟩
    simp only [oldKey,newKey,he,hn,Option.map_some,updatedLabel,Function.update_of_ne han]

lemma inner_paid {r R:ℝ} (hr:0 < r) {C D:Finset Y} {x p:Y} {rad:Y→ℝ}
    {lab prev:Y→Pool Y} (hC:(C:Set Y).Pairwise (fun a b=>100*r<dist a b))
    (hrad:∀ a∈C,rad a∈Set.Icc (16*r) (20*r)) (hR:R∈Set.Icc (16*r) (20*r))
    (hxp:dist x p≤3*r) :
    (if oldKey C rad lab p≠newKey C D rad lab prev r x R p then (1:ℝ) else 0) +
      profile r (replace r C x) p-profile r C p≤0 := by
  have hn:profile r (replace r C x) p=0:=profile_eq_zero hr (mem_insert_self _ _) (by linarith)
  rw [hn]
  by_cases he:∃ a∈C,dist a p≤10*r
  · obtain ⟨a,ha,hap⟩:=he
    rw [ite_eq_right (not_not.mpr (inner_reuses hr hC hrad hR ha hap hxp))]
    linarith [profile_nonneg r C p]
  · have hp:profile r C p=1:=by
      apply profile_eq_one hr
      intro a ha
      exact le_of_lt (lt_of_not_ge (fun hh=>he ⟨a,ha,hh⟩))
    rw [hp]
    split_ifs <;> norm_num

/-- Source heavy edit charge table for a stationary member. -/
theorem stationary {r R:ℝ} (hr:0 < r) {C D:Finset Y} {x p:Y} {rad:Y→ℝ}
    {lab prev:Y→Pool Y} (hC:(C:Set Y).Pairwise (fun a b=>100*r<dist a b))
    (hrad:∀ a∈C,rad a∈Set.Icc (16*r) (20*r)) (hR:R∈Set.Icc (16*r) (20*r)) :
    (if oldKey C rad lab p≠newKey C D rad lab prev r x R p then (1:ℝ) else 0) +
      profile r (replace r C x) p-profile r C p≤
        if 3*r<dist x p ∧ dist x p≤120*r then 2 else 0 := by
  by_cases hnear:dist x p≤3*r
  · rw [ite_eq_right (show ¬(3*r<dist x p ∧ dist x p≤120*r) from fun h=>not_lt_of_ge hnear h.1)]
    exact inner_paid hr hC hrad hR hnear
  · by_cases hfar:120*r<dist x p
    · rw [profile_far hr C hfar,ite_eq_right (show ¬(3*r<dist x p ∧ dist x p≤120*r) from fun h=>not_le_of_gt hfar h.2),
        ite_eq_right (not_not.mpr (keys_far (D:=D) (lab:=lab) (prev:=prev) hr hC (fun a ha=>(hrad a ha).2) hR.2 hfar))]
      ring_nf
      exact le_rfl
    · rw [ite_eq_left (show 3*r<dist x p ∧ dist x p≤120*r from ⟨lt_of_not_ge hnear,le_of_not_gt hfar⟩)]
      have ho:=profile_nonneg r C p
      have hn:=profile_le_one r (replace r C x) p
      split_ifs <;> linarith

/-- Source heavy edit charge table for the designated mover. -/
theorem mover {r R:ℝ} (hr:0 < r) {C D:Finset Y} {x p:Y} {rad:Y→ℝ}
    {lab prev:Y→Pool Y} (hC:(C:Set Y).Pairwise (fun a b=>100*r<dist a b))
    (hrad:∀ a∈C,rad a∈Set.Icc (16*r) (20*r)) (hR:R∈Set.Icc (16*r) (20*r)) :
    (if oldKey C rad lab p≠newKey C D rad lab prev r x R p then (1:ℝ) else 0) +
      profile r (replace r C x) x-profile r C p≤ if 3*r<dist x p then 1 else 0 := by
  by_cases hnear:dist x p≤3*r
  · have hh:=inner_paid (D:=D) (lab:=lab) (prev:=prev) hr hC hrad hR hnear
    have hp:profile r (replace r C x) p=0:=profile_eq_zero hr (mem_insert_self _ _) (by linarith)
    have hx:profile r (replace r C x) x=0:=profile_eq_zero hr (mem_insert_self _ _) (by simpa only [dist_self] using (mul_nonneg (by norm_num : (0:ℝ)≤9) hr.le))
    rw [ite_eq_right (not_lt_of_ge hnear),hx]
    simpa only [hp] using hh
  · rw [ite_eq_left (lt_of_not_ge hnear)]
    have hx:profile r (replace r C x) x=0:=profile_eq_zero hr (mem_insert_self _ _) (by simpa only [dist_self] using (mul_nonneg (by norm_num : (0:ℝ)≤9) hr.le))
    rw [hx]
    have ho:=profile_nonneg r C p
    split_ifs <;> linarith
end KServer.HeavyEdit

end


/-! The actual heavy-priority stage, including its deterministic clipped-ramp
potential and the true hidden trajectory. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavyTemporal
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw PriorityKeys ActualRoster
open HeavyCenters HeavySchedule HeavyLabels LevelRetirement RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

lemma charge_le (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:ℕ) (p:Y) :
    charge s law hr σ a t p ≤ indicator
      (HeavyKeys.key s law r heavyGamma heavyDelta σ a.1 t p≠
        HeavyKeys.key s law r heavyGamma heavyDelta σ a.1 (t+1) p) :=
  stage_charge _ _ _ _

lemma active_keys (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (ha:active s law r σ t) (p:Y) :
    HeavyKeys.key s law r heavyGamma heavyDelta σ a.1 (t.val+1) p=
      HeavyEdit.newKey (centers s law r heavyGamma heavyDelta σ t)
      (centers s law r heavyGamma heavyDelta σ (t.val-1))
      (run s law r heavyGamma heavyDelta σ a.1 t).rad
      (run s law r heavyGamma heavyDelta σ a.1 t).label
      (run s law r heavyGamma heavyDelta σ a.1 t).previous r (σ t)
      (FiniteUniform.radius r (a.1 t)) p := by
  simp only [HeavyKeys.key,centers_succ,HeavyCenters.step,run,t.isLt,dite_eq_left,active] at ha ⊢
  simp only [ite_eq_left ha]
  rfl

lemma inactive_keys (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (ha:¬active s law r σ t) (p:Y) :
    HeavyKeys.key s law r heavyGamma heavyDelta σ a.1 (t.val+1) p=
      HeavyKeys.key s law r heavyGamma heavyDelta σ a.1 t p := by
  simp only [HeavyKeys.key,centers_succ,HeavyCenters.step,run,t.isLt,dite_eq_left,active] at ha ⊢
  simp only [ite_eq_right ha]

lemma inactive_charge (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (ha:¬active s law r σ t) (p:Y) :
    charge s law hr σ a t p=0 := by
  have hb:=charge_le s law hr σ a t p
  rw [inactive_keys s law r σ a t ha p] at hb
  simp only [ne_self_iff_false,indicator,ite_false] at hb
  exact le_antisymm hb (indicator_nonneg _)

lemma active_profile (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ)
    (σ:Fin H→Y) (t:Fin H) (ha:active s law r σ t) (p:Y) :
    profile s law r σ (t.val+1) p=HeavyEdit.profile r
      (replace r (centers s law r heavyGamma heavyDelta σ t) (σ t)) p := by
  dsimp only [active] at ha
  simp only [profile,centers_succ,HeavyCenters.step,ite_eq_left ha]

lemma inactive_profile (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ)
    (σ:Fin H→Y) (t:Fin H) (ha:¬active s law r σ t) (p:Y) :
    profile s law r σ (t.val+1) p=profile s law r σ t p := by
  dsimp only [active] at ha
  simp only [profile,centers_succ,HeavyCenters.step,ite_eq_right ha]

lemma stationary (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (p:Y) :
    charge s law hr.le σ a t p+profile s law r σ (t.val+1) p-profile s law r σ t p ≤
      if active s law r σ t then 2*indicator (3*r<dist (σ t) p ∧ dist (σ t) p≤120*r) else 0 := by
  by_cases ha:active s law r σ t
  · rw [ite_eq_left ha,active_profile s law r σ t ha p]
    have hc:=charge_le s law hr.le σ a t p
    rw [active_keys s law r σ a t ha p] at hc
    have hb:=HeavyEdit.stationary (x:=σ t) (D:=centers s law r heavyGamma heavyDelta σ (t.val-1))
      (lab:=(run s law r heavyGamma heavyDelta σ a.1 t).label)
      (prev:=(run s law r heavyGamma heavyDelta σ a.1 t).previous) hr
      (centers_separated s law r heavyGamma heavyDelta σ t)
      (run_valid s law hr heavyGamma heavyDelta σ a.1 t).1 (FiniteUniform.radius_range hr (a.1 t))
      (p:=p)
    simp only [HeavyKeys.key] at hc
    have he:(if 3*r<dist (σ t) p ∧ dist (σ t) p≤120*r then (2:ℝ) else 0)=
        2*indicator (3*r<dist (σ t) p ∧ dist (σ t) p≤120*r):=by
      unfold indicator
      split_ifs <;> norm_num
    rw [he] at hb
    dsimp only [profile]
    simp only [HeavyEdit.oldKey] at hb
    apply (sub_le_sub (add_le_add hc (le_refl _)) (le_refl _)).trans
    convert hb using 1 <;> first | rfl | (simp only [indicator]; congr 4)
  · rw [ite_eq_right ha,inactive_charge s law hr.le σ a t ha p,inactive_profile s law r σ t ha p]
    ring_nf
    exact le_rfl


lemma mover (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (p:Y) :
    charge s law hr.le σ a t p+profile s law r σ (t.val+1) (σ t)-profile s law r σ t p ≤
      indicator (3*r<dist (σ t) p)+(if heavy s law r σ t then 0 else dist (σ t) p/r) := by
  by_cases ha:active s law r σ t
  · have hh:heavy s law r σ t:=ha.1
    rw [active_profile s law r σ t ha (σ t),ite_eq_left hh]
    have hc:=charge_le s law hr.le σ a t p
    rw [active_keys s law r σ a t ha p] at hc
    have hb:=HeavyEdit.mover (x:=σ t) (D:=centers s law r heavyGamma heavyDelta σ (t.val-1))
      (lab:=(run s law r heavyGamma heavyDelta σ a.1 t).label)
      (prev:=(run s law r heavyGamma heavyDelta σ a.1 t).previous) hr
      (centers_separated s law r heavyGamma heavyDelta σ t)
      (run_valid s law hr heavyGamma heavyDelta σ a.1 t).1 (FiniteUniform.radius_range hr (a.1 t))
      (p:=p)
    simp only [HeavyKeys.key] at hc
    simp only [HeavyEdit.oldKey] at hb
    dsimp only [profile]
    simp only [add_zero]
    apply (sub_le_sub (add_le_add hc (le_refl _)) (le_refl _)).trans
    convert hb using 1 <;> first | rfl | (simp only [indicator]; congr 4)
  · rw [inactive_charge s law hr.le σ a t ha p,inactive_profile s law r σ t ha (σ t)]
    by_cases hh:heavy s law r σ t
    · rw [ite_eq_left hh]
      have he:∃ a∈centers s law r heavyGamma heavyDelta σ t,dist a (σ t)≤8*r:=by
        by_contra hn
        push Not at hn
        exact ha ⟨hh,hn⟩
      obtain ⟨b,hb,hbd⟩:=he
      have hz:profile s law r σ t (σ t)=0:=HeavyEdit.profile_eq_zero hr hb (by linarith)
      rw [hz]
      have hp:=HeavyEdit.profile_nonneg r (centers s law r heavyGamma heavyDelta σ t) p
      have hi:=indicator_nonneg (3*r<dist (σ t) p)
      dsimp only [profile]
      linarith
    · rw [ite_eq_right hh]
      have hb:=(le_abs_self _).trans (HeavyEdit.profile_lipschitz hr
        (centers s law r heavyGamma heavyDelta σ t) (σ t) p)
      have hi:=indicator_nonneg (3*r<dist (σ t) p)
      dsimp only [profile]
      linarith

end KServer.HeavyTemporal

end


/-! True-prefix causality of the literal fixed-label complete level map.
The finite permanent colors and cooldown reservations do not read the future. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.KeysAdapted
open FiniteExperiment TierProcess Chronological ActualRoster LevelKeys LevelLaw
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

omit [MetricSpace Y] [NeZero k] in
lemma history_mono {t T:ℕ} (ht:t≤T) (σ ρ:Fin H→Y)
    (hh:requestHistory T σ=requestHistory T ρ) : requestHistory t σ=requestHistory t ρ := by
  rw [requestHistory_eq_iff] at hh ⊢
  funext i
  by_cases hi:i.val<t
  · have hiT:i.val<T:=lt_of_lt_of_le hi ht
    have he:=congrFun hh i
    simpa only [requestPrefix,ite_eq_left hi,ite_eq_left hiT] using he
  · simp only [requestPrefix,ite_eq_right hi]

end KServer.KeysAdapted

end


/-! True-prefix heavy edit accounting. The deterministic profile is telescoped
on the hidden labeled optimum; no surviving-radius conditioning is used. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavyBudget
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw PriorityKeys ActualRoster
open HeavyCenters HeavySchedule HeavyLabels LevelRetirement RankTracking PosteriorRanks
open HiddenAverages HeavyTemporal TierGlobal
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

lemma test_nonneg (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:Fin H) (p:Y) :
    0≤test s law r σ t p := by unfold test; split_ifs; exact indicator_nonneg _; rfl

lemma test_adapted (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (t:Fin H) (p:Y) :
    Adapted (requestHistory (t.val+1)) (fun σ=>test s law r σ t p) := by
  intro σ ρ hh
  have hm:mu s law (t.val+1) σ=mu s law (t.val+1) ρ:=funext (fun y=>mu_adapted s law (t.val+1) y σ ρ hh)
  have hp:requestHistory t.val σ=requestHistory t.val ρ:=by
    exact KeysAdapted.history_mono (Nat.le_succ _) σ ρ hh
  have hc:=centers_adapted s law r heavyGamma heavyDelta t.val σ ρ hp
  simp only [test,active,hm,hc,request_of_history t σ ρ hh]
  congr 4

lemma test_mass (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:Fin H) :
    (∑ y,mu s law (t.val+1) σ y*test s law r σ t y)=
      if active s law r σ t then mass (mu s law (t.val+1) σ) (HeavyCenters.annulus (σ t) r) else 0 := by
  unfold test
  split_ifs
  · simp only [indicator,mul_ite,mul_one,mul_zero]
    rw [←sum_filter]
    congr 1
  · simp

lemma stationary_bound (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (t:Fin H) :
    avg law.val (fun σ=>∑ l∈univ.erase (FiniteExperiment.mover s σ t),test s law r σ t (hidden s σ t l)) ≤
      avg law.val (fun σ=>if active s law r σ t then mass (mu s law (t.val+1) σ) (HeavyCenters.annulus (σ t) r) else 0) := by
  rw [←expected_stationary_test s law t (fun σ p=>test s law r σ t p) (test_adapted s law r t)]
  trans avg law.val (fun σ=>∑ y,mu s law (t.val+1) σ y*test s law r σ t y)
  · apply sum_le_sum
    intro σ _
    by_cases hs:0<law.val σ
    · apply mul_le_mul_of_nonneg_left _ hs.le
      apply sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_right (stationary_le s law t σ hs y) (test_nonneg s law r σ t y)
    · have hz:law.val σ=0:=le_antisymm (le_of_not_gt hs) (law.property.1 σ)
      simp only [hz,zero_mul,le_refl]
  · apply le_of_eq
    congr 1
    funext σ
    exact test_mass s law r σ t

lemma potential_bounds (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:ℕ) :
    potential s law r σ t∈Set.Icc 0 (k:ℝ) := by
  constructor
  · exact sum_nonneg (fun l _=>HeavyEdit.profile_nonneg _ _ _)
  · exact (sum_le_sum (fun l (_:l∈univ)=>HeavyEdit.profile_le_one _ _ _)).trans_eq (by simp)

lemma potential_step (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) :
    editCost s law hr σ a t+potential s law r σ (t.val+1)-potential s law r σ t=
      (∑ l∈univ.erase (FiniteExperiment.mover s σ t),(HeavyTemporal.charge s law hr σ a t (hidden s σ t l)+
        HeavyTemporal.profile s law r σ (t.val+1) (hidden s σ t l)-HeavyTemporal.profile s law r σ t (hidden s σ t l)))+
      (HeavyTemporal.charge s law hr σ a t (hidden s σ t (FiniteExperiment.mover s σ t))+
        HeavyTemporal.profile s law r σ (t.val+1) (σ t)-HeavyTemporal.profile s law r σ t (hidden s σ t (FiniteExperiment.mover s σ t))) := by
  have he:potential s law r σ (t.val+1)=
    (∑ l∈univ.erase (FiniteExperiment.mover s σ t),HeavyTemporal.profile s law r σ (t.val+1) (hidden s σ t l))+
      HeavyTemporal.profile s law r σ (t.val+1) (σ t) := by
    unfold potential
    rw [←sum_erase_add _ _ (mem_univ (FiniteExperiment.mover s σ t)),hidden_covers]
    congr 1
    apply sum_congr rfl
    intro l hl
    congr 1
    have he:=congrFun (hidden_step s σ t) l
    simpa [serve,(mem_erase.mp hl).1] using he
  rw [he]
  unfold editCost potential
  have hC:=sum_erase_add univ (fun l:Fin k=>HeavyTemporal.charge s law hr σ a t (hidden s σ t l)) (mem_univ (FiniteExperiment.mover s σ t))
  have hU:=sum_erase_add univ (fun l:Fin k=>HeavyTemporal.profile s law r σ t (hidden s σ t l)) (mem_univ (FiniteExperiment.mover s σ t))
  simp only [sum_sub_distrib,sum_add_distrib]
  linarith

lemma step_bound (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) :
    editCost s law hr.le σ a t+potential s law r σ (t.val+1)-potential s law r σ t≤
      2*(∑ l∈univ.erase (FiniteExperiment.mover s σ t),test s law r σ t (hidden s σ t l))+
      indicator (3*r<dist (σ t) (hidden s σ t (FiniteExperiment.mover s σ t)))+
      (if heavy s law r σ t then 0 else dist (σ t) (hidden s σ t (FiniteExperiment.mover s σ t))/r) := by
  rw [potential_step]
  have hs:=sum_le_sum (fun l (_:l∈univ.erase (FiniteExperiment.mover s σ t))=>HeavyTemporal.stationary s law hr σ a t (hidden s σ t l))
  have he: (∑ l∈univ.erase (FiniteExperiment.mover s σ t),(if active s law r σ t then
      2*indicator (3*r<dist (σ t) (hidden s σ t l) ∧ dist (σ t) (hidden s σ t l)≤120*r) else 0))=
      2*(∑ l∈univ.erase (FiniteExperiment.mover s σ t),test s law r σ t (hidden s σ t l)) := by
    unfold test
    split_ifs
    · rw [mul_sum]
    · simp
  rw [he] at hs
  have hm:=HeavyTemporal.mover s law hr σ a t (hidden s σ t (FiniteExperiment.mover s σ t))
  linarith

lemma average_step (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (t:Fin H) :
    avg law.val (fun σ=>mean r (fun a=>editCost s law hr.le σ a t))+
      avg law.val (fun σ=>potential s law r σ (t.val+1))-
      avg law.val (fun σ=>potential s law r σ t) ≤
    2*avg law.val (fun σ=>if active s law r σ t then mass (mu s law (t.val+1) σ) (HeavyCenters.annulus (σ t) r) else 0)+
      avg law.val (fun σ=>indicator (3*r<dist (σ t) (hidden s σ t (mover s σ t))))+
      avg law.val (fun σ=>if heavy s law r σ t then 0 else dist (σ t) (hidden s σ t (mover s σ t))/r) := by
  have hb:=avg_mono law.property.1 (fun σ=>(mean_mono hr (fun a=>step_bound s law hr σ a t)))
  simp only [TierTemporal.mean_sub,TierTemporal.mean_add,mean_const hr,avg_add,avg_sub,avg_mul] at hb
  have hs:=stationary_bound s law r t
  linarith

lemma mean_bounds (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (t:ℕ) :
    avg law.val (fun σ=>potential s law r σ t)∈Set.Icc 0 (k:ℝ) := by
  constructor
  · exact (show 0=avg law.val (fun _=>0) by rw [avg_const _ law.property.2]).le.trans
      (avg_mono law.property.1 (fun σ=>(potential_bounds s law r σ t).1))
  · calc _ ≤ avg law.val (fun _=>(k:ℝ)) := avg_mono law.property.1 (fun σ=>(potential_bounds s law r σ t).2)
         _ = _ := avg_const _ law.property.2 _

lemma heavy_budget (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r) :
    (∑ t:Fin H,avg law.val (fun σ=>mean r (fun a=>editCost s law hr.le σ a t))) ≤
    2*(∑ t:Fin H,avg law.val (fun σ=>if active s law r σ t then mass (mu s law (t.val+1) σ) (HeavyCenters.annulus (σ t) r) else 0))+
      (∑ t:Fin H,avg law.val (fun σ=>indicator (3*r<dist (σ t) (hidden s σ t (mover s σ t)))))+
      (∑ t:Fin H,avg law.val (fun σ=>if heavy s law r σ t then 0 else dist (σ t) (hidden s σ t (mover s σ t))/r))+k := by
  have hb:=telescope_budget (fun t=>avg law.val (fun σ=>potential s law r σ t)) _ _
    (average_step s law hr) (mean_bounds s law r H).1
  simp only [sum_add_distrib,←mul_sum] at hb
  exact hb.trans (add_le_add le_rfl (mean_bounds s law r 0).2)

end KServer.HeavyBudget

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_JointExperiment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The posterior counting measure is built from labeled hidden positions.
Integrating adapted metric tests is exactly conditional expectation, and
prefix quota domination is relative to this measure, not an extra premise. -/


/-! Removing null atoms preserves the literal conditional experiment. This
allows quota feasibility to be used only on positive posterior fibers. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PositiveExperiment
open RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Ω:Type} [Fintype Ω]

lemma sum_support {w:Ω→ℝ} (hw:∀ ω,0≤w ω) (f:Ω→ℝ):
    (∑ ω:Support w,weight w ω*f ω.val)=∑ ω,w ω*f ω:=by
  have hh:=Fintype.sum_subtype_add_sum_subtype (fun ω=>0<w ω) (fun ω=>w ω*f ω)
  have hz:(∑ ω:{ω:Ω // ¬0<w ω},w ω.val*f ω.val)=0:=by
    apply sum_eq_zero
    intro ω _
    have he:w ω.val=0:=le_antisymm (le_of_not_gt ω.property) (hw ω.val)
    rw [he,zero_mul]
  simpa only [hz,add_zero,weight] using hh

end KServer.PositiveExperiment

end


/-! The single positive finite joint request/tape experiment for every scale.
All maps use precisely the request history and the independent finite tapes. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointExperiment
open FiniteExperiment PartitionProbabilities RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ}

variable (law:FiniteDistribution (Fin H→Y)) {r:Fin L→ℝ} (hr:∀ d,0 < r d)

lemma raw_nonneg (ω:Raw Y k H L r):0 ≤ rawWeight law hr ω:=
  FiniteExperiment.weight_nonneg law (tapeLaw (Y:=Y) (k:=k) (H:=H) hr) ω

lemma avg_raw (f:Raw Y k H L r→ℝ):
    avg (weight (k:=k) law hr) (fun ω=>f ω.val)=avg (rawWeight law hr) f:=
  PositiveExperiment.sum_support (raw_nonneg law hr) f

variable [NeZero k] (s:Configuration k Y)

omit [NeZero k] in
lemma scale_mean (d:Fin L) (f:(Fin H→Y)→LevelKeys.Tape Y k H (r d)→ℝ):
    avg (weight (k:=k) law hr) (fun ω=>f ω.val.1 (ω.val.2 d))=
      avg law.val (fun σ=>LevelRetirement.mean (r d) (f σ)):=by
  rw [avg_raw law hr (fun ω:Raw Y k H L r=>f ω.1 (ω.2 d))]
  unfold RankTracking.avg rawWeight FiniteExperiment.weight
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro σ _
  simp only [mul_assoc,←mul_sum]
  congr 1
  unfold tapeLaw tapeWeight LevelRetirement.mean
  convert FiniteTape.marginal (fun j=>LevelLaw.weight (r j))
    (fun j=>LevelLaw.weight_sum (hr j)) d (f σ) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext x
  simp only [mem_univ]

end KServer.JointExperiment

end


/-! The dependent permanent key alphabet is genuinely finite. -/


/-! Endpoint costs on the actual schedule are charged to active size, rather
than to all inactive fixed labels. This is needed for wholesale edits. -/

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_JointBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric absorption on the same numbered tree used for metric rounding. -/


/-! All-scale, law/horizon-independent roster endpoint, aggregating the actual
chronological edit charges rather than assuming metric distortion. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.EmbeddedCost
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw LevelRetirement RankTracking
open TierGlobal TierScaleBudget
attribute [local instance] Classical.propDecidable Classical.decEq

lemma exchange {Ω T:Type*} [Fintype Ω] [Fintype T] (w:Ω→ℝ) (r:ℕ→ℝ)
    (S:Finset ℕ) (f:ℕ→T→Ω→ℝ):
    (∑ j∈S,r j*(∑ t:T,avg w (f j t)))=∑ t:T,avg w (fun σ=>∑ j∈S,r j*f j t σ):=by
  simp only [avg,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  rw [sum_comm]
  apply sum_congr rfl
  intro σ _
  exact sum_congr rfl (fun j _=>by ring)

variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

lemma tier_all (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0 < r₀) (hτ:2 ≤ τ) (n:ℕ):
    tierMove s law hr hτ n ≤ tierCoefficient k*opt s law+
      (294+Fintype.card (Tier k))*inventory k r₀ τ n:=by
  have hrad j:0 < radius r₀ τ j:=radius_pos hr (by linarith) j
  have hs:=sum_le_sum (s:=univ) (fun i _=>sum_le_sum (s:=range n) (fun j _=>
    mul_le_mul_of_nonneg_left (tier_budget s law (hrad j) i) (hrad j).le))
  simp only [mul_add,sum_add_distrib] at hs
  have hA:=insertion_all s law hr hτ n
  have hB:=far_all s law hr hτ n
  have hC:=noinsert_all s law hr hτ n
  have he:(∑ j∈range n,2*radius r₀ τ j*(k:ℝ))=2*inventory k r₀ τ n:=by
    simp only [inventory,mul_sum,mul_assoc]
  have he':(∑ i:Tier k,∑ j∈range n,radius r₀ τ j*(k:ℝ))=
      (Fintype.card (Tier k):ℝ)*inventory k r₀ τ n:=by simp [inventory]
  rw [he'] at hs
  unfold tierMove tierCoefficient opt
  rw [he] at hA
  linarith
end KServer.EmbeddedCost

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.EmbeddedCost
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw LevelRetirement RankTracking
open TierGlobal TierScaleBudget HeavyTemporal ActualRoster
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

lemma movement_average (s:Configuration k Y) (law:RequestLaw Y H) (c:ℝ):
    (∑ t:Fin H,avg law.val (fun σ=>c*dist (σ t) (hidden s σ t (mover s σ t))))=c*opt s law:=by
  simp only [avg,opt]
  rw [sum_comm,mul_sum]
  apply sum_congr rfl
  intro σ _
  rw [←actual_move_cost s σ]
  simp only [mul_sum]
  exact sum_congr rfl (fun t _=>by ring)

omit [MetricSpace Y] [Fintype Y] [NeZero k] in
lemma far_scales_general {r₀ τ d c:ℝ} (hr:0 < r₀) (hτ:2 ≤ τ) (hd:0 ≤ d) (hc:0 < c) (n:ℕ):
    (∑ j∈range n,radius r₀ τ j*indicator (c*radius r₀ τ j<d)) ≤ (2/c)*d:=by
  have hb:=radius_truncated_sum hr.le hτ (div_nonneg hd hc.le) n
  refine (sum_le_sum (s:=range n) (fun j _=>?_)).trans (hb.trans_eq (by ring))
  by_cases hj:c*radius r₀ τ j<d
  · have hle:radius r₀ τ j ≤ d/c:=(le_div_iff₀ hc).mpr (by linarith)
    simp only [indicator,ite_eq_left hj,mul_one,ite_eq_left hle,le_refl]
  · simp only [indicator,ite_eq_right hj,mul_zero]
    split_ifs
    · exact (radius_pos hr (by linarith) j).le
    · rfl

lemma nonheavy_scales (s:Configuration k Y) (law:RequestLaw Y H)
    (σ:Fin H→Y) (hσ:0<law.val σ) (t:Fin H) (y:Y)
    {r₀ τ:ℝ} (hr:0 < r₀) (hτ:2 ≤ τ) (n:ℕ):
    (∑ j∈range n,radius r₀ τ j*(if heavy s law (radius r₀ τ j) σ t then 0 else dist (σ t) y/radius r₀ τ j)) ≤
      ((60/Real.log (1+heavyDelta))*Real.log k)*dist (σ t) y:=by
  have hb:=mul_le_mul_of_nonneg_right (LevelScale.actual_nonheavy_count s law σ hσ t hr.le hτ n)
    (dist_nonneg (x:=σ t) (y:=y))
  have he:(∑ j∈range n,radius r₀ τ j*(if heavy s law (radius r₀ τ j) σ t then 0 else dist (σ t) y/radius r₀ τ j))=
      (∑ j∈range n,if heavy s law (radius r₀ τ j) σ t then (0:ℝ) else 1)*dist (σ t) y:=by
    rw [sum_mul]
    apply sum_congr rfl
    intro j _
    split_ifs
    · simp
    · field_simp [(radius_pos (τ:=τ) hr (by linarith) j).ne']
  rw [he]
  convert hb using 1 <;> first | rfl | ring

lemma heavy_far_all (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0 < r₀) (hτ:2 ≤ τ) (n:ℕ):
    (∑ j∈range n,radius r₀ τ j*(∑ t:Fin H,avg law.val (fun σ=>indicator
      (3*radius r₀ τ j<dist (σ t) (hidden s σ t (mover s σ t)))))) ≤ (2/3:ℝ)*opt s law:=by
  rw [exchange]
  refine (sum_le_sum (fun t (_:t∈univ)=>avg_mono law.property.1 (fun σ=>
    far_scales_general hr hτ dist_nonneg (by norm_num : (0:ℝ)<3) n))).trans_eq ?_
  exact movement_average s law (2/3)

lemma heavy_nonheavy_all (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0 < r₀) (hτ:2 ≤ τ) (n:ℕ):
    (∑ j∈range n,radius r₀ τ j*(∑ t:Fin H,avg law.val (fun σ=>
      if heavy s law (radius r₀ τ j) σ t then 0 else dist (σ t) (hidden s σ t (mover s σ t))/radius r₀ τ j))) ≤
      ((60/Real.log (1+heavyDelta))*Real.log k)*opt s law:=by
  rw [exchange]
  refine le_trans ?_ (movement_average s law _).le
  apply sum_le_sum
  intro t _
  apply sum_le_sum
  intro σ _
  by_cases hs:law.val σ=0
  · simp only [hs,zero_mul,le_refl]
  · exact mul_le_mul_of_nonneg_left (nonheavy_scales s law σ
      (lt_of_le_of_ne (law.property.1 σ) (Ne.symm hs)) t _ hr hτ n) (law.property.1 σ)

lemma heavy_annulus_all (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0 < r₀) (hτ:2 ≤ τ) (n:ℕ):
    (∑ j∈range n,radius r₀ τ j*(∑ t:Fin H,avg law.val (fun σ=>
      if active s law (radius r₀ τ j) σ t then
      mass (mu s law (t.val+1) σ) (HeavyCenters.annulus (σ t) (radius r₀ τ j)) else 0))) ≤
      heavyDrift*(1+Real.log ((k:ℝ)+1))*opt s law+2*inventory k r₀ τ n:=by
  rw [exchange]
  have hb:=HeavyCenters.annulus_budget s law (γ:=heavyGamma) (δ:=heavyDelta) n 26 hr hτ
    (by norm_num [heavyGamma]) (by norm_num [heavyGamma])
    (by norm_num [heavyDelta]) (by norm_num [heavyDelta])
    (by norm_num [heavyGamma])
  have he:(∑ j∈range n,2*radius r₀ τ j*(k:ℝ))=2*inventory k r₀ τ n:=by
    simp only [inventory,mul_sum,mul_assoc]
  rw [he] at hb
  have hc (t:Fin H) (σ:Fin H→Y) (j:ℕ):
      HeavyCenters.charge s law (radius r₀ τ j) heavyGamma heavyDelta t σ=
        radius r₀ τ j*(if active s law (radius r₀ τ j) σ t then
          mass (mu s law (t.val+1) σ) (HeavyCenters.annulus (σ t) (radius r₀ τ j)) else 0):=by
    unfold HeavyCenters.charge active
    split_ifs <;> ring
  simp_rw [hc] at hb
  exact hb

lemma heavy_all (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0 < r₀) (hτ:2 ≤ τ) (n:ℕ):
    heavyMove s law hr hτ n ≤ heavyCoefficient k*opt s law+5*inventory k r₀ τ n:=by
  have hrad j:0 < radius r₀ τ j:=radius_pos hr (by linarith) j
  have hs:=sum_le_sum (s:=range n) (fun j _=>
    mul_le_mul_of_nonneg_left (HeavyBudget.heavy_budget s law (hrad j)) (hrad j).le)
  have hA:=heavy_annulus_all s law hr hτ n
  have hB:=heavy_far_all s law hr hτ n
  have hC:=heavy_nonheavy_all s law hr hτ n
  simp only [mul_add,sum_add_distrib] at hs
  have he:(∑ j∈range n,radius r₀ τ j*(2*(∑ t:Fin H,avg law.val (fun σ=>
      if active s law (radius r₀ τ j) σ t then
      mass (mu s law (t.val+1) σ) (HeavyCenters.annulus (σ t) (radius r₀ τ j)) else 0))))=
      2*(∑ j∈range n,radius r₀ τ j*(∑ t:Fin H,avg law.val (fun σ=>
      if active s law (radius r₀ τ j) σ t then
      mass (mu s law (t.val+1) σ) (HeavyCenters.annulus (σ t) (radius r₀ τ j)) else 0))):=by
    rw [mul_sum]
    exact sum_congr rfl (fun j _=>by ring)
  rw [he] at hs
  change heavyMove s law hr hτ n ≤ _+inventory k r₀ τ n at hs
  unfold heavyCoefficient
  linarith
end KServer.EmbeddedCost

end


/-! The chronological triangle inequality for the literal priority stages. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PriorityKeys
attribute [local instance] Classical.propDecidable Classical.decEq
open ActualRoster

lemma indicator_triangle {B:Type*} (a b c:B):
    indicator (a≠c) ≤ indicator (a≠b)+indicator (b≠c):=by
  by_cases hab:a=b
  · subst b; simp [indicator]
  · by_cases hbc:b=c
    · subst c; simp [indicator]
    · unfold indicator
      simp only [ite_eq_left hab,ite_eq_left hbc]
      split_ifs <;> norm_num

lemma indicator_chain {B:Type*} (f:ℕ→B) (n:ℕ):
    indicator (f 0≠f n) ≤ ∑ j∈range n,indicator (f j≠f (j+1)):=by
  induction n with
  | zero=>simp [indicator]
  | succ n ih=>
    rw [sum_range_succ]
    exact (indicator_triangle (f 0) (f n) (f (n+1))).trans (add_le_add ih (le_refl _))

variable {I Y:Type*} [Fintype I] [LinearOrder I] {A:I→Type*}

lemma stages_total (q₀ q₁:(i:I)→Y→Option (A i)) (x:Y):
    indicator (key q₀ x≠key q₁ x) ≤
      ∑ j:I,indicator (key (stageBefore q₀ q₁ j) x≠key (stageAfter q₀ q₁ j) x):=by
  let m:=Fintype.card I
  let e:Fin m ≃o I:=Fintype.orderIsoFinOfCardEq I rfl
  let blend (n:ℕ):(i:I)→Y→Option (A i):=fun i=>if (e.symm i).val<n then q₁ i else q₀ i
  have hzero:blend 0=q₀:=by funext i; simp [blend]
  have hlast:blend m=q₁:=by funext i; simp [blend,(e.symm i).isLt]
  have hbefore (j:Fin m):blend j.val=stageBefore q₀ q₁ (e j):=by
    funext i
    have he:(e.symm i).val<j.val ↔ i<e j:=by
      change e.symm i<j ↔ i<e j
      constructor
      · intro h; simpa only [e.apply_symm_apply] using e.strictMono h
      · intro h; simpa only [e.symm_apply_apply] using e.symm.strictMono h
    simp only [blend,stageBefore,he]
  have hafter (j:Fin m):blend (j.val+1)=stageAfter q₀ q₁ (e j):=by
    funext i
    have he:(e.symm i).val<j.val+1 ↔ i≤e j:=by
      rw [Nat.lt_succ_iff]
      change e.symm i≤j ↔ i≤e j
      constructor
      · intro h; simpa only [e.apply_symm_apply] using e.monotone h
      · intro h; simpa only [e.symm_apply_apply] using e.symm.monotone h
    simp only [blend,stageAfter,he]
  have hb:=indicator_chain (fun n=>key (blend n) x) m
  rw [hzero,hlast,←Fin.sum_univ_eq_sum_range] at hb
  simp only [hbefore,hafter] at hb
  exact hb.trans_eq (Fintype.sum_equiv e.toEquiv _ _ (fun _=>rfl))
end KServer.PriorityKeys

end


/-! The all-step embedded motion of the selected hidden labeled optimum. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.EmbeddedCost
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw LevelRetirement RankTracking
open ActualRoster RankTracking TierTemporal
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

omit [MetricSpace Y] [Fintype Y] [NeZero k] in
lemma indicator_ne_comm {B:Type*} (a b:B):indicator (a≠b)=indicator (b≠a):=by
  simp only [ne_comm]

lemma map_edit (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:ℕ) (p:Y):
    indicator (map s law hr σ a t p≠map s law hr σ a (t+1) p) ≤
      HeavyTemporal.charge s law hr σ a t p+
        ∑ i:Tier k,LevelTierEdits.charge s law hr σ a t i p:=by
  have hb:=PriorityKeys.stages_total (keys s law hr σ a t) (keys s law hr σ a (t+1)) p
  let f (j:Structure k):ℝ:=indicator
    (PriorityKeys.key (PriorityKeys.stageBefore (keys s law hr σ a t) (keys s law hr σ a (t+1)) j) p≠
      PriorityKeys.key (PriorityKeys.stageAfter (keys s law hr σ a t) (keys s law hr σ a (t+1)) j) p)
  change _ ≤ ∑ j:Structure k,f j at hb
  let e:Structure k ≃ Option (Tier k):=Equiv.refl _
  rw [Fintype.sum_equiv e f (fun j=>f (e.symm j)) (fun _=>rfl),Fintype.sum_option] at hb
  exact hb

lemma physical_cross (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H):
    (∑ l:Fin k,indicator (map s law hr σ a (t.val+1) (hidden s σ t l)≠
      map s law hr σ a (t.val+1) (hidden s σ (t.val+1) l)))=
        indicator (map s law hr σ a (t.val+1) (σ t)≠
          map s law hr σ a (t.val+1) (hidden s σ t (mover s σ t))):=by
  rw [hidden_step]
  rw [sum_eq_single (mover s σ t)]
  · simp only [serve,Function.update_self]
    exact indicator_ne_comm _ _
  · intro l _ hl
    simp [serve,Function.update_of_ne hl,indicator]
  · simp

lemma mapped_step (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H):
    mappedCross s law hr σ a t ≤ HeavyBudget.editCost s law hr σ a t+
      (∑ i:Tier k,TierTemporal.editCost s law hr σ a t i)+
      indicator (map s law hr σ a (t.val+1) (σ t)≠
        map s law hr σ a (t.val+1) (hidden s σ t (mover s σ t))):=by
  have hs:=sum_le_sum (s:=univ) (fun l (_:l∈univ)=>
    (PriorityKeys.indicator_triangle (map s law hr σ a t (hidden s σ t l))
      (map s law hr σ a (t.val+1) (hidden s σ t l))
      (map s law hr σ a (t.val+1) (hidden s σ (t.val+1) l))).trans
        (add_le_add (map_edit s law hr σ a t (hidden s σ t l)) (le_refl _)))
  simp only [sum_add_distrib] at hs
  rw [physical_cross] at hs
  unfold mappedCross HeavyBudget.editCost TierTemporal.editCost
  exact hs.trans_eq (by rw [sum_comm (f:=fun l i=>LevelTierEdits.charge s law hr σ a t i (hidden s σ t l))])

lemma mapped_step_mean (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (t:Fin H):
    mean r (fun a=>mappedCross s law hr.le σ a t) ≤
      mean r (fun a=>HeavyBudget.editCost s law hr.le σ a t)+
      (∑ i:Tier k,mean r (fun a=>TierTemporal.editCost s law hr.le σ a t i))+
      LevelSpatial.separation s law hr.le σ (t.val+1) (σ t) (hidden s σ t (mover s σ t)):=by
  have hb:=mean_mono hr (fun a=>mapped_step s law hr.le σ a t)
  simp only [mean_add,mean_sum] at hb
  have he:mean r (fun a=>indicator (map s law hr.le σ a (t.val+1) (σ t)≠
      map s law hr.le σ a (t.val+1) (hidden s σ t (mover s σ t))))=
      LevelSpatial.separation s law hr.le σ (t.val+1) (σ t) (hidden s σ t (mover s σ t)):=by
    rw [mean_indicator]
    unfold LevelSpatial.separation
    apply sum_congr rfl
    intro a _
    split_ifs <;> rfl
  rw [he] at hb
  exact hb

end KServer.EmbeddedCost

end


/-! The finite all-scale offline embedding endpoint. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.EmbeddedCost
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw LevelRetirement RankTracking
open ActualRoster RankTracking TierTemporal
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

lemma spatial_all (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0 < r₀) (hτ:2≤τ) (n:ℕ):
    spatialMove s law hr hτ n ≤ spatialCoefficient k*opt s law:=by
  unfold spatialMove
  rw [exchange]
  refine le_trans ?_ (movement_average s law _).le
  apply sum_le_sum
  intro t _
  apply sum_le_sum
  intro σ _
  by_cases hs:law.val σ=0
  · simp only [hs,zero_mul,le_refl]
  · exact mul_le_mul_of_nonneg_left (LevelSpatial.spatial_sum s law σ
      (lt_of_le_of_ne (law.property.1 σ) (Ne.symm hs)) t _ hr hτ n) (law.property.1 σ)

lemma key_move_decompose (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0 < r₀) (hτ:2≤τ) (n:ℕ):
    keyMove s law hr hτ n ≤ heavyMove s law hr hτ n+tierMove s law hr hτ n+
      spatialMove s law hr hτ n:=by
  have hrad j:0 < radius r₀ τ j:=radius_pos hr (by linarith) j
  have hs:=sum_le_sum (s:=range n) (fun j _=>mul_le_mul_of_nonneg_left
    (sum_le_sum (s:=univ) (fun t (_:t∈univ)=>avg_mono law.property.1 (fun σ=>
      mapped_step_mean s law (hrad j) σ t))) (hrad j).le)
  simp only [avg_add,avg_sum,mul_add,sum_add_distrib] at hs
  have he:(∑ j∈range n,radius r₀ τ j*(∑ t:Fin H,∑ i:Tier k,avg law.val (fun σ=>
      mean (radius r₀ τ j) (fun a=>TierTemporal.editCost s law (hrad j).le σ a t i))))=
        tierMove s law hr hτ n:=by
    unfold tierMove
    simp_rw [sum_comm (f:=fun t i=>avg law.val (fun σ=>
      mean (radius r₀ τ _) (fun a=>TierTemporal.editCost s law (hrad _).le σ a t i)))]
    simp only [mul_sum]
    rw [sum_comm]
  rw [he] at hs
  exact hs

lemma embedding_all (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0 < r₀) (hτ:2≤τ) (n:ℕ):
    keyMove s law hr hτ n ≤
      (tierCoefficient k+heavyCoefficient k+spatialCoefficient k)*opt s law+
        (299+Fintype.card (Tier k))*inventory k r₀ τ n:=by
  have hD:=key_move_decompose s law hr hτ n
  have hA:=tier_all s law hr hτ n
  have hB:=heavy_all s law hr hτ n
  have hC:=spatial_all s law hr hτ n
  linarith

end KServer.EmbeddedCost

end


/-! The finite all-scale embedding is used with the reversed geometric list
of radii in the top-down prefix construction, not with a moved quantifier. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointEmbedding
open JointExperiment RankTracking ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0 < r d)

lemma cross_mean (d:Fin L) (t:Fin H):
    avg (weight law hr) (HierarchicalQuota.keyCross (maps law hr s) (hidden law hr s) d.val t.val)=
      avg law.val (fun σ=>LevelRetirement.mean (r d) (fun tape=>
        EmbeddedCost.mappedCross s law (hr d).le σ tape t)):=by
  have he:(HierarchicalQuota.keyCross (maps law hr s) (hidden law hr s) d.val t.val)=
      fun ω:Atom (k:=k) law hr=>EmbeddedCost.mappedCross s law (hr d).le ω.val.1 (ω.val.2 d) t:=by
    funext ω
    unfold HierarchicalQuota.keyCross EmbeddedCost.mappedCross
    simp only [JointExperiment.maps,dite_eq_left d.isLt,JointExperiment.hidden]
    apply sum_congr rfl
    intro i _
    unfold ActualRoster.indicator
    split_ifs <;> simp_all only [ne_eq,eq_comm,not_true_eq_false,not_false_eq_true]
  rw [he]
  exact scale_mean law hr d (fun σ tape=>EmbeddedCost.mappedCross s law (hr d).le σ tape t)

lemma total_key:
    total (weight law hr) H (JointBudget.stepKey s law hr)=∑ d:Fin L,r d*scaleCost s law (r d):=by
  unfold total JointBudget.stepKey
  rw [←Fin.sum_univ_eq_sum_range]
  simp only [avg_sum,avg_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  rw [←mul_sum]
  simp_rw [cross_mean s law hr d]
  rw [scaleCost,dite_eq_left (hr d)]

lemma radius_reverse {R τ:ℝ} (hτ:τ≠0) (d:Fin L):
    R/τ^(d.val+1)=Pilot.radius (R/τ^L) τ d.rev.val:=by
  unfold Pilot.radius
  have hd:d.rev.val+(d.val+1)=L:=by simp only [Fin.val_rev]; omega
  apply (div_eq_iff (pow_ne_zero _ hτ)).mpr
  rw [mul_assoc,←pow_add,hd,div_mul_cancel₀ _ (pow_ne_zero _ hτ)]

lemma key_bound_oai {R τ:ℝ} (hR:0<R) (hτ:2≤τ) (hrad:∀ d,r d=R/τ^(d.val+1)):
    total (weight law hr) H (JointBudget.stepKey s law hr)≤
      (EmbeddedCost.tierCoefficient k+EmbeddedCost.heavyCoefficient k+EmbeddedCost.spatialCoefficient k)*
        EmbeddedCost.opt s law+
      (299+Fintype.card (LevelKeys.Tier k))*EmbeddedCost.inventory k (R/τ^L) τ L:=by
  have ht:0<τ:=by linarith
  have hbase:0<R/τ^L:=div_pos hR (pow_pos ht _)
  have he:total (weight law hr) H (JointBudget.stepKey s law hr)=
      EmbeddedCost.keyMove s law hbase hτ L:=by
    rw [total_key]
    simp_rw [hrad, radius_reverse ht.ne']
    rw [Fintype.sum_equiv Fin.revPerm
      (fun d:Fin L=>Pilot.radius (R/τ^L) τ d.rev.val*scaleCost s law (Pilot.radius (R/τ^L) τ d.rev.val))
      (fun d:Fin L=>Pilot.radius (R/τ^L) τ d.val*scaleCost s law (Pilot.radius (R/τ^L) τ d.val)) (fun _=>rfl)]
    rw [Fin.sum_univ_eq_sum_range (fun j=>Pilot.radius (R/τ^L) τ j*
      scaleCost s law (Pilot.radius (R/τ^L) τ j)) L]
    unfold EmbeddedCost.keyMove
    apply sum_congr rfl
    intro d _
    rw [scaleCost,dite_eq_left (Pilot.radius_pos hbase ht d)]
  rw [he]
  exact EmbeddedCost.embedding_all s law hbase hτ L
end KServer.JointEmbedding

end

end OAI
end

theorem solution : type_of% @OAI.KServer.JointEmbedding.key_bound_oai := @OAI.KServer.JointEmbedding.key_bound_oai
